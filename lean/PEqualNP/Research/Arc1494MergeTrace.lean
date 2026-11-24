import Init

namespace SophiaResearch.Arc1494MergeTrace

abbrev Part := Fin 15
abbrev Mask := Fin 16

def partitions : List (List Nat) := [[1,2,4,8],[1,2,12],[1,4,10],[1,6,8],[2,4,9],[2,5,8],[3,4,8],[1,14],[2,13],[3,12],[4,11],[5,10],[6,9],[7,8],[15]]

def blocks (g : Part) : List Nat := partitions[g.val]!

def rank (g : Part) : Nat := 4 - (blocks g).length

def contained (g : Part) (a : Mask) : Bool :=
  a.val == 0 || (blocks g).any (fun b => (a.val &&& b) == a.val)

def inter (a b : Mask) : Mask := Fin.ofNat 16 (a.val &&& b.val)
def union (a b : Mask) : Mask := Fin.ofNat 16 (a.val ||| b.val)

def merge (g : Part) (a b : Mask) : Part :=
  if a.val == 0 || b.val == 0 then g else
    let s := (union a b).val
    let hit := (blocks g).filter fun m => (m &&& s) != 0
    let rest := (blocks g).filter fun m => (m &&& s) == 0
    let joined := hit.foldl (·|||·) 0 :: rest
    Fin.ofNat 15 (partitions.findIdx (fun p =>
      p.length == joined.length && p.all (fun m => joined.contains m)))

def event (g : Part) (a b : Mask) : Nat :=
  if rank g < rank (merge g a b) then 1 else 0

def atomic (a : Mask) : Bool := ([0,1,2,4,8] : List Nat).contains a.val

theorem zero_rank : rank (0 : Part) = 0 := by decide +kernel

theorem atomic_contained :
    ∀ a : Mask, atomic a = true → contained 0 a = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 10000000 in
theorem inter_contained :
    ∀ g : Part, ∀ a b : Mask, contained g a = true →
      contained g (inter a b) = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
set_option synthInstance.maxSize 256 in
theorem merge_local :
    ∀ g : Part, ∀ a b : Mask, contained g a = true → contained g b = true →
      (contained (merge g a b) (union a b) = true) ∧
      rank (merge g a b) ≤ rank g + event g a b ∧
      (event g a b = 1 → a.val ≠ 0 ∧ b.val ≠ 0 ∧ (a.val &&& b.val) = 0) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 100000000 in
set_option synthInstance.maxSize 256 in
theorem merge_preserve :
    ∀ g : Part, ∀ a b c : Mask, contained g a = true → contained g b = true →
      contained g c = true → contained (merge g a b) c = true := by
  decide +kernel

theorem merge_spec (g : Part) (a b : Mask)
    (ha : contained g a = true) (hb : contained g b = true) :
      (contained (merge g a b) (union a b) = true) ∧
      (∀ c : Mask, contained g c = true → contained (merge g a b) c = true) ∧
      rank (merge g a b) ≤ rank g + event g a b ∧
      (event g a b = 1 → a.val ≠ 0 ∧ b.val ≠ 0 ∧ (a.val &&& b.val) = 0) := by
  obtain ⟨hu,hr,he⟩ := merge_local g a b ha hb
  exact ⟨hu, fun c hc => merge_preserve g a b c ha hb hc, hr, he⟩

theorem full_rank :
    ∀ g : Part, contained g (15 : Mask) = true → rank g = 3 := by decide +kernel

-- A false wire's support is its singleton support restricted to four target
-- variables. False AND steps keep a subset of a false parent's support.
-- False OR steps merge the supports of their two false parents.
inductive ZeroTrace : List Mask → Part → Nat → Prop
  | start (xs : List Mask) (h : ∀ a ∈ xs, atomic a = true) :
      ZeroTrace xs 0 0
  | sub {xs g c} (h : ZeroTrace xs g c) (a b : Mask) (ha : a ∈ xs) :
      ZeroTrace (inter a b :: xs) g c
  | join {xs g c} (h : ZeroTrace xs g c) (a b : Mask)
      (ha : a ∈ xs) (hb : b ∈ xs) :
      ZeroTrace (union a b :: xs) (merge g a b) (c + event g a b)

theorem trace_invariant {xs : List Mask} {g : Part} {c : Nat}
    (h : ZeroTrace xs g c) :
    (∀ a ∈ xs, contained g a = true) ∧ rank g ≤ c := by
  induction h with
  | start xs h =>
    exact ⟨fun a ha => atomic_contained a (h a ha), by simp [zero_rank]⟩
  | @sub xs g c _ a b ha ih =>
    refine ⟨?_, ih.2⟩
    intro u hu
    rcases List.mem_cons.mp hu with he | he
    · subst u
      exact inter_contained g a b (ih.1 a ha)
    · exact ih.1 u he
  | @join xs g c _ a b ha hb ih =>
    obtain ⟨hu, hp, hr, _⟩ := merge_spec g a b (ih.1 a ha) (ih.1 b hb)
    refine ⟨?_, ?_⟩
    · intro u hx
      rcases List.mem_cons.mp hx with he | he
      · subst u
        exact hu
      · exact hp u (ih.1 u he)
    · omega

theorem trace_full_requires_three {xs : List Mask} {g : Part} {c : Nat}
    (h : ZeroTrace xs g c) (hout : (15 : Mask) ∈ xs) :
    3 ≤ c := by
  have hi := trace_invariant h
  have hr := full_rank g (hi.1 15 hout)
  omega

theorem total_gate_count (m a o dirty : Nat) (hm : m ≤ 13)
    (hcharge : 162*m ≤ 60*o)
    (hdirty1 : dirty ≤ a) (hdirty2 : dirty ≤ m)
    (hclean : 3*(m-dirty) ≤ o)
    (hremaining : 162*dirty ≤ 60*(o-3*(m-dirty))) :
    3*m ≤ a+o := by
  by_cases ha : 3 ≤ a
  · omega
  · have hd : dirty ≤ 2 := by omega
    rcases Nat.le.dest hd with ⟨e,he⟩
    omega

end SophiaResearch.Arc1494MergeTrace
