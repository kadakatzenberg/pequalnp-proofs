import PEqualNP.Defs.MetaComplexity
/-!
A local, exact-semantics witness for the disjoint union of two four-vertex paths.
Uses the OFFICIAL PEqualNP.CircuitLowerBounds.Circuit definition.
This is an upper bound only. The eight-gate lower bound remains unproved in Lean.
-/

namespace SophiaResearch.P4Pair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 7)

/-- g0 through g3 compute the first four-vertex path on inputs 0..3;
    g4 through g7 compute the second path on inputs 4..7;
    g8 ORs the path outputs. All gate and wire indices are official. -/
def witness : Circuit :=
  ⟨[
    ⟨GateOp.or,  [0,2]⟩,    -- wire 8
    ⟨GateOp.and, [1,8]⟩,    -- wire 9
    ⟨GateOp.and, [2,3]⟩,    -- wire 10
    ⟨GateOp.or,  [9,10]⟩,   -- wire 11
    ⟨GateOp.or,  [4,6]⟩,    -- wire 12
    ⟨GateOp.and, [5,12]⟩,   -- wire 13
    ⟨GateOp.and, [6,7]⟩,    -- wire 14
    ⟨GateOp.or,  [13,14]⟩,  -- wire 15
    ⟨GateOp.or,  [11,15]⟩   -- wire 16
  ], 16⟩

theorem witness_size : witness.size = 9 := by rfl

theorem witness_fanin : FanInTwo witness := by
  simp [FanInTwo, witness]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem witness_correct : ∀ x : Fin 8 → Bool,
    witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem has_nine_gate_circuit : HasCircuitSize 8 target 9 := by
  refine ⟨witness, witness_fanin, by simp [witness_size], witness_correct⟩

end SophiaResearch.P4Pair

#print axioms SophiaResearch.P4Pair.has_nine_gate_circuit
