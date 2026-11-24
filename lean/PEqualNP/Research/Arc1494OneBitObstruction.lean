import Init

namespace SophiaResearch.Arc1494

abbrev V := Fin 26

def incident (p w : Nat) : Bool :=
  [0, 1, 3, 9].contains ((p + 13 - w) % 13)

def adj (a b : V) : Bool :=
  if a.val < 13 then
    if 13 ≤ b.val then incident a.val (b.val - 13) else false
  else
    if b.val < 13 then incident b.val (a.val - 13) else false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem plane_paths :
    ∀ a b : V, a ≠ b →
      adj a b = true ∨
      (∃ c : V, adj a c = true ∧ adj c b = true) ∨
      (∃ c d : V, adj a c = true ∧ adj c d = true ∧ adj d b = true) := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem separated_neighbors :
    ∀ a b : V, a ≠ b →
      ∃ t : V, adj t a = true ∧ adj t b = false := by
  decide +kernel

theorem nonisolated : ∀ v : V, ∃ z : V, adj z v = true := by
  decide +kernel

theorem symmetric : ∀ a b : V, adj a b = adj b a := by
  decide +kernel

theorem crossing (S : V → Bool) (a b : V)
    (ha : S a = true) (hb : S b = false) :
    ∃ u v : V, S u = true ∧ S v = false ∧ adj v u = true := by
  have hne : a ≠ b := by
    intro he
    subst b
    simp_all
  rcases plane_paths a b hne with h | ⟨c,hac,hcb⟩ | ⟨c,e,hac,hce,heb⟩
  · exact ⟨a,b,ha,hb,(symmetric b a).trans h⟩
  · cases hc : S c
    · exact ⟨a,c,ha,hc,(symmetric c a).trans hac⟩
    · exact ⟨c,b,hc,hb,(symmetric b c).trans hcb⟩
  · cases hc : S c
    · exact ⟨a,c,ha,hc,(symmetric c a).trans hac⟩
    · cases he : S e
      · exact ⟨c,e,hc,he,(symmetric e c).trans hce⟩
      · exact ⟨e,b,he,hb,(symmetric b e).trans heb⟩

def inside (S : V → Bool) (xs : List V) : Prop :=
  xs.all S = true

def outside (S : V → Bool) (xs : List V) : Prop :=
  xs.all (fun v => !S v) = true

theorem two_unary_maps (a b : Bool → Bool) (z ya yb x : Bool)
    (ha0 : a z = false) (hb0 : b z = false)
    (ha1 : a ya = true) (hb1 : b yb = true) : a x = b x := by
  cases z <;> cases ya <;> cases yb <;> cases x <;> simp_all

theorem slice_obstruction
    (f : List V → Bool) (S : V → Bool)
    (a b x ya yb : List V)
    (ha : outside S a) (hb : outside S b)
    (hx : inside S x) (hya : inside S ya) (hyb : inside S yb)
    (ha0 : f a = false) (hb0 : f b = false)
    (ha1 : f (a ++ ya) = true) (hb1 : f (b ++ yb) = true)
    (hne : f (a ++ x) ≠ f (b ++ x)) :
    ¬ ∃ (h : List V → Bool) (g : List V → Bool → Bool),
       ∀ a b : List V, outside S a → inside S b →
         f (a ++ b) = g a (h b) := by
  rintro ⟨h,g,hg⟩
  have hnil : inside S [] := by simp [inside]
  have a0 := hg a [] ha hnil
  have b0 := hg b [] hb hnil
  simp only [List.append_nil] at a0 b0
  have a1 := hg a ya ha hya
  have b1 := hg b yb hb hyb
  have ax := hg a x ha hx
  have bx := hg b x hb hx
  have same := two_unary_maps (g a) (g b) (h []) (h ya) (h yb) (h x)
    (a0.symm.trans ha0) (b0.symm.trans hb0)
    (a1.symm.trans ha1) (b1.symm.trans hb1)
  exact hne (ax.trans (same.trans bx.symm))

-- Only empty, singleton, pair and monotone positive triple tests are required.
-- No circuit correct on the arc promise can have a one-bit private support
-- of size at least two that is strictly smaller than all input variables.
theorem no_proper_one_bit_factor
    (f : List V → Bool)
    (hf0 : f [] = false)
    (hf1 : ∀ v : V, f [v] = false)
    (hf2 : ∀ u v : V, f [u,v] = adj u v)
    (hf3 : ∀ a u v : V, adj u v = true → f [a,u,v] = true)
    (S : V → Bool) (u v t : V)
    (hu : S u = true) (hv : S v = true) (huv : u ≠ v)
    (ht : S t = false) :
    ¬ ∃ (h : List V → Bool) (g : List V → Bool → Bool),
       ∀ a b : List V, outside S a → inside S b →
         f (a ++ b) = g a (h b) := by
  by_cases hi : ∃ p q : V, S p = true ∧ S q = true ∧ adj p q = true
  · obtain ⟨p,q,hp,hq,he⟩ := hi
    obtain ⟨s,w,hs,hw,hsw⟩ := crossing S u t hu ht
    apply slice_obstruction f S [] [w] [s] [p,q] [p,q]
    · simp [outside]
    · simp [outside,hw]
    · simp [inside,hs]
    · simp [inside,hp,hq]
    · simp [inside,hp,hq]
    · exact hf0
    · exact hf1 w
    · exact (hf2 p q).trans he
    · exact hf3 w p q he
    · change f [s] ≠ f [w,s]
      rw [hf1 s, hf2 w s, hsw]
      decide
  · obtain ⟨a, hau, hav⟩ := separated_neighbors u v huv
    obtain ⟨b, hbv⟩ := nonisolated v
    have ha : S a = false := by
      cases h : S a
      · rfl
      · exact False.elim (hi ⟨a,u,h,hu,hau⟩)
    have hb : S b = false := by
      cases h : S b
      · rfl
      · exact False.elim (hi ⟨b,v,h,hv,hbv⟩)
    apply slice_obstruction f S [a] [b] [v] [u] [v]
    · simp [outside,ha]
    · simp [outside,hb]
    · simp [inside,hv]
    · simp [inside,hu]
    · simp [inside,hv]
    · exact hf1 a
    · exact hf1 b
    · exact (hf2 a u).trans hau
    · exact (hf2 b v).trans hbv
    · change f [a,v] ≠ f [b,v]
      rw [hf2 a v, hf2 b v, hav, hbv]
      decide

end SophiaResearch.Arc1494
