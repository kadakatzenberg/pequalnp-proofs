import Init

namespace SophiaResearch.P4PairSharedSupport

def edges : List (Nat × Nat) :=
  [(0,1), (1,2), (2,3), (4,5), (5,6), (6,7)]

def f (r : Nat) : Bool :=
  edges.any fun e => r.testBit e.1 && r.testBit e.2

def inside (s : Nat) (e : Nat × Nat) : Bool :=
  s.testBit e.1 && s.testBit e.2

def crosses (s : Nat) (e : Nat × Nat) : Bool :=
  s.testBit e.1 != s.testBit e.2

def orient (s : Nat) (e : Nat × Nat) : Nat × Nat :=
  if s.testBit e.1 then e else (e.2,e.1)

def mixedProper (s : Nat) : Bool :=
  s != 255 && s % 16 != 0 && s / 16 != 0

def subset (a s : Nat) : Bool :=
  (List.range 8).all fun i => !a.testBit i || s.testBit i

def disjoint (a s : Nat) : Bool :=
  (List.range 8).all fun i => !(a.testBit i && s.testBit i)

structure Witness where
  a : Nat
  b : Nat
  x : Nat
  ya : Nat
  yb : Nat

def witness (s : Nat) : Witness :=
  match edges.find? (inside s) with
  | some e =>
    let c := orient s ((edges.find? (crosses s)).getD (0,0))
    let y := 2 ^ e.1 + 2 ^ e.2
    ⟨0, 2 ^ c.2, 2 ^ c.1, y, y⟩
  | none =>
    let c := orient s ((edges.find? (fun e => crosses s e && decide (e.1 < 4))).getD (0,0))
    let d := orient s ((edges.find? (fun e => crosses s e && decide (4 ≤ e.1))).getD (0,0))
    ⟨2 ^ c.2, 2 ^ d.2, 2 ^ c.1, 2 ^ c.1, 2 ^ d.1⟩

def valid (s : Nat) (w : Witness) : Bool :=
  disjoint w.a s && disjoint w.b s &&
  subset w.x s && subset w.ya s && subset w.yb s &&
  !f w.a && !f w.b &&
  f (w.a + w.ya) && f (w.b + w.yb) &&
  (f (w.a + w.x) != f (w.b + w.x))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem no_proper_mixed_one_bit_support :
    ∀ s : Fin 256, mixedProper s.val = true →
      valid s.val (witness s.val) = true := by
  decide +kernel

theorem mixed_proper_count :
    ((List.range 256).filter mixedProper).length = 224 := by
  decide +kernel

def witnessProps (s : Nat) (w : Witness) : Prop :=
  disjoint w.a s = true ∧ disjoint w.b s = true ∧
  subset w.x s = true ∧ subset w.ya s = true ∧ subset w.yb s = true ∧
  f w.a = false ∧ f w.b = false ∧
  f (w.a + w.ya) = true ∧ f (w.b + w.yb) = true ∧
  f (w.a + w.x) ≠ f (w.b + w.x)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem witness_props :
    ∀ s : Fin 256, mixedProper s.val = true →
      witnessProps s.val (witness s.val) := by
  unfold witnessProps
  decide +kernel

theorem empty_subset : ∀ s : Fin 256, subset 0 s.val = true := by
  decide +kernel

theorem one_bit_slices_eq (a b : Bool → Bool) (z ya yb x : Bool)
    (ha0 : a z = false) (hb0 : b z = false)
    (ha1 : a ya = true) (hb1 : b yb = true) : a x = b x := by
  cases z <;> cases ya <;> cases yb <;> cases x <;> simp_all

theorem no_one_bit_factor (s : Fin 256) (hs : mixedProper s.val = true) :
    ¬ ∃ (h : Nat → Bool) (g : Nat → Bool → Bool),
      ∀ a x : Nat, disjoint a s.val = true → subset x s.val = true →
        f (a + x) = g a (h x) := by
  intro H
  obtain ⟨h,g,hg⟩ := H
  let w := witness s.val
  have hp : witnessProps s.val w := witness_props s hs
  obtain ⟨ha,hb,hx,hya,hyb,hfa,hfb,hfya,hfyb,hdiff⟩ := hp
  have a0 := hg w.a 0 ha (empty_subset s)
  have b0 := hg w.b 0 hb (empty_subset s)
  simp only [Nat.add_zero] at a0 b0
  have aya := hg w.a w.ya ha hya
  have byb := hg w.b w.yb hb hyb
  have ax := hg w.a w.x ha hx
  have bx := hg w.b w.x hb hx
  have same := one_bit_slices_eq (g w.a) (g w.b) (h 0) (h w.ya) (h w.yb) (h w.x)
    (a0.symm.trans hfa) (b0.symm.trans hfb)
    (aya.symm.trans hfya) (byb.symm.trans hfyb)
  exact hdiff (ax.trans (same.trans bx.symm))

end SophiaResearch.P4PairSharedSupport
