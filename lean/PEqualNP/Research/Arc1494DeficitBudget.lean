import Init

namespace SophiaResearch.Arc1494DeficitBudget

-- All 13 outputs require 54 negative-arc traces apiece, each with
-- 3 merge events of weight 10 and one completion event of weight 1.
theorem deficit_budget (capacity actual deficit : Nat)
    (hcap : capacity ≤ 600 * 37)
    (hactual : 21762 ≤ actual)
    (hdef : actual + deficit ≤ capacity) :
    deficit ≤ 438 := by omega

-- A proper nonsingleton support within a line has capacity at most 540.
-- A full-line support has capacity at most 594.
-- A clean output consumes two proper support ORs and one full support OR.
theorem clean_output_cost : 126 = 2 * (600-540) + (600-594) := by decide

theorem maximum_pair_gates (pairs : Nat)
    (h : 60*pairs ≤ 438) : pairs ≤ 7 := by omega

-- c clean outputs, l dirty outputs with a chosen line-contained filter,
-- n dirty outputs whose chosen filter is noncollinear.
-- The charged gates for different lines are distinct.
theorem nonlinear_filter_requirement (c l n : Nat)
    (hpartition : c + l + n = 13)
    (hcharge : 126*c + 60*l ≤ 438) :
    c ≤ 3 ∧ 6 + c ≤ n := by omega

theorem table_c0 (l n : Nat) (hpartition : l+n=13)
    (hcharge : 60*l≤438) : 7≥l ∧ 6≤n := by omega

theorem table_c1 (l n : Nat) (hpartition : 1+l+n=13)
    (hcharge : 126+60*l≤438) : 5≥l ∧ 7≤n := by omega

theorem table_c2 (l n : Nat) (hpartition : 2+l+n=13)
    (hcharge : 252+60*l≤438) : 3≥l ∧ 8≤n := by omega

theorem table_c3 (l n : Nat) (hpartition : 3+l+n=13)
    (hcharge : 378+60*l≤438) : 1≥l ∧ 9≤n := by omega

-- A concrete counterexample to discounting every noncollinear
-- support's reciprocal-size charge by one fifth.
def lineMasks : List Nat := [523,1046,2092,4184,177,354,708,1416,2832,5664,3137,6274,4357]
def cover : List Nat := [161,1031,2817,4169]

def pop13 (a : Nat) : Nat :=
  ((List.range 13).filter fun i => a.testBit i).length

def collinear (s : Nat) : Bool :=
  lineMasks.any fun l => (s &&& l) == s

def fourArcExcludingZero (a : Nat) : Bool :=
  !a.testBit 0 && pop13 a == 4 &&
    lineMasks.all (fun l => decide (pop13 (a &&& l) ≤ 2))

theorem cover_sizes : cover.map pop13 = [3,4,4,4] := by decide +kernel
theorem cover_types : cover.map collinear = [true,false,false,false] := by decide +kernel
theorem cover_contains_zero : cover.all (fun s => s.testBit 0) = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 50000000 in
theorem cover_separates :
    (List.range 8192).all (fun a => !fourArcExcludingZero a ||
      cover.any (fun s => (s &&& a) == 0)) = true := by
  decide +kernel

-- Scale 60: ordinary charge 65/60 > 1, discounted charge 56/60 < 1.
theorem discounted_counterexample : 60/3 + 3*(48/4) < 60 := by decide
theorem ordinary_charge : 60/3 + 3*(60/4) = 65 := by decide

end SophiaResearch.Arc1494DeficitBudget
