import Init

namespace SophiaResearch.AdjacentBranchCover

def edges : List (Nat × Nat) :=
  [(0,1), (0,2), (0,3), (1,4), (1,5),
   (2,6), (3,7), (4,8), (5,9)]

def covered (E : List (Nat × Nat)) (m : Fin 1024) : Bool :=
  E.all fun e => m.val.testBit e.1 || m.val.testBit e.2

def cost (m : Fin 1024) : Nat :=
  ((List.range 10).filter fun i => m.val.testBit i).length

def del (E : List (Nat × Nat)) (S : List Nat) : List (Nat × Nat) :=
  E.filter fun e => !(S.contains e.1 || S.contains e.2)

def ofSet (S : List Nat) : Fin 1024 :=
  Fin.ofNat 1024 (S.foldl (fun n i => n + 2 ^ i) 0)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem all_cover_bounds :
    (∀ m : Fin 1024, covered edges m = true → 5 ≤ cost m) ∧
    (∀ m : Fin 1024, covered (del edges [0]) m = true → 4 ≤ cost m) ∧
    (∀ m : Fin 1024, covered (del edges [1]) m = true → 4 ≤ cost m) ∧
    (∀ m : Fin 1024, covered (del edges [0,1]) m = true → 4 ≤ cost m) := by
  decide +kernel

theorem actual_minimum_covers :
    covered edges (ofSet [0,2,3,4,5]) = true ∧
    cost (ofSet [0,2,3,4,5]) = 5 ∧
    covered (del edges [0]) (ofSet [2,3,4,5]) = true ∧
    covered (del edges [1]) (ofSet [2,3,4,5]) = true ∧
    covered (del edges [0,1]) (ofSet [2,3,4,5]) = true ∧
    cost (ofSet [2,3,4,5]) = 4 := by
  decide +kernel

theorem graph_edge_counts :
    edges.length = 9 ∧
    (del edges [0]).length = 6 ∧
    (del edges [1]).length = 6 ∧
    (del edges [0,1]).length = 4 := by
  decide

end SophiaResearch.AdjacentBranchCover
