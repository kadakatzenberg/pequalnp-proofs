import PEqualNP.Defs.MetaComplexity

-- Research-only finite upper-bound controls, not the posted L-meta-519 theorem.

namespace SophiaResearch.Spider223

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) ||
  (x 0 && x 3) || (x 3 && x 4) ||
  (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 7)

def witness : Circuit :=
  ⟨[
    ⟨GateOp.or,  [1,3]⟩,   -- wire 8
    ⟨GateOp.or,  [8,5]⟩,   -- wire 9
    ⟨GateOp.and, [0,9]⟩,   -- wire 10
    ⟨GateOp.and, [1,2]⟩,   -- wire 11
    ⟨GateOp.and, [3,4]⟩,   -- wire 12
    ⟨GateOp.or,  [5,7]⟩,   -- wire 13
    ⟨GateOp.and, [6,13]⟩,  -- wire 14
    ⟨GateOp.or,  [10,11]⟩, -- wire 15
    ⟨GateOp.or,  [12,14]⟩, -- wire 16
    ⟨GateOp.or,  [15,16]⟩  -- wire 17
  ], 17⟩

theorem witness_size : witness.size = 10 := by rfl

theorem witness_fanin : FanInTwo witness := by
  simp [FanInTwo, witness]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem witness_correct : ∀ x : Fin 8 → Bool,
    witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem ten_gate_upper : HasCircuitSize 8 target 10 := by
  exact ⟨witness, witness_fanin, by simp [witness_size], witness_correct⟩

def targetFalse (x : Fin 8 → Bool) : Bool :=
  (x 1 && x 2) || (x 3 && x 4) ||
  (x 5 && x 6) || (x 6 && x 7)

def targetTrue (x : Fin 8 → Bool) : Bool :=
  x 1 || x 3 || x 5 || (x 6 && x 7)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem zero_restriction :
    ∀ x : Fin 8 → Bool, target (Function.update x 0 false) = targetFalse x := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem one_restriction :
    ∀ x : Fin 8 → Bool, target (Function.update x 0 true) = targetTrue x := by
  decide +kernel

def witnessFalse : Circuit :=
  ⟨[
    ⟨GateOp.and, [1,2]⟩,
    ⟨GateOp.and, [3,4]⟩,
    ⟨GateOp.or,  [5,7]⟩,
    ⟨GateOp.and, [6,10]⟩,
    ⟨GateOp.or,  [8,9]⟩,
    ⟨GateOp.or,  [12,11]⟩
  ], 13⟩

def witnessTrue : Circuit :=
  ⟨[
    ⟨GateOp.and, [6,7]⟩,
    ⟨GateOp.or,  [1,3]⟩,
    ⟨GateOp.or,  [9,5]⟩,
    ⟨GateOp.or,  [10,8]⟩
  ], 11⟩

theorem witnessFalse_size : witnessFalse.size = 6 := by rfl

theorem witnessTrue_size : witnessTrue.size = 4 := by rfl

theorem witnessFalse_fanin : FanInTwo witnessFalse := by
  simp [FanInTwo, witnessFalse]

theorem witnessTrue_fanin : FanInTwo witnessTrue := by
  simp [FanInTwo, witnessTrue]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem witnessFalse_correct :
    ∀ x : Fin 8 → Bool, witnessFalse.eval (List.ofFn x) = targetFalse x := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem witnessTrue_correct :
    ∀ x : Fin 8 → Bool, witnessTrue.eval (List.ofFn x) = targetTrue x := by
  decide +kernel

end SophiaResearch.Spider223


namespace SophiaResearch.DoubleStar

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 2) ||
  (x 0 && x 3) || (x 1 && x 4) || (x 1 && x 5)

def witness : Circuit :=
  ⟨[
    ⟨GateOp.or,  [2,3]⟩,
    ⟨GateOp.or,  [1,6]⟩,
    ⟨GateOp.and, [0,7]⟩,
    ⟨GateOp.or,  [4,5]⟩,
    ⟨GateOp.and, [1,9]⟩,
    ⟨GateOp.or,  [8,10]⟩
  ], 11⟩

theorem witness_size : witness.size = 6 := by rfl

theorem witness_fanin : FanInTwo witness := by
  simp [FanInTwo, witness]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem witness_correct :
    ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = target x := by
  decide +kernel

theorem six_gate_upper : HasCircuitSize 6 target 6 := by
  exact ⟨witness, witness_fanin, by simp [witness_size], witness_correct⟩

def restrict0False (x : Fin 6 → Bool) : Bool :=
  x 1 && (x 4 || x 5)

def restrict0True (x : Fin 6 → Bool) : Bool :=
  x 1 || x 2 || x 3

def restrict1False (x : Fin 6 → Bool) : Bool :=
  x 0 && (x 2 || x 3)

def restrict1True (x : Fin 6 → Bool) : Bool :=
  x 0 || x 4 || x 5

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem restrictions_correct :
    (∀ x : Fin 6 → Bool,
       target (Function.update x 0 false) = restrict0False x) ∧
    (∀ x : Fin 6 → Bool,
       target (Function.update x 0 true) = restrict0True x) ∧
    (∀ x : Fin 6 → Bool,
       target (Function.update x 1 false) = restrict1False x) ∧
    (∀ x : Fin 6 → Bool,
       target (Function.update x 1 true) = restrict1True x) := by
  decide +kernel

def w0False : Circuit :=
  ⟨[⟨GateOp.or, [4,5]⟩, ⟨GateOp.and, [1,6]⟩], 7⟩

def w0True : Circuit :=
  ⟨[⟨GateOp.or, [1,2]⟩, ⟨GateOp.or, [6,3]⟩], 7⟩

def w1False : Circuit :=
  ⟨[⟨GateOp.or, [2,3]⟩, ⟨GateOp.and, [0,6]⟩], 7⟩

def w1True : Circuit :=
  ⟨[⟨GateOp.or, [0,4]⟩, ⟨GateOp.or, [6,5]⟩], 7⟩

theorem restriction_gate_counts :
    w0False.size = 2 ∧ w0True.size = 2 ∧
    w1False.size = 2 ∧ w1True.size = 2 := by
  decide

theorem restriction_fanins :
    FanInTwo w0False ∧ FanInTwo w0True ∧
    FanInTwo w1False ∧ FanInTwo w1True := by
  simp [FanInTwo, w0False, w0True, w1False, w1True]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem restriction_witnesses_correct :
    (∀ x : Fin 6 → Bool, w0False.eval (List.ofFn x) = restrict0False x) ∧
    (∀ x : Fin 6 → Bool, w0True.eval (List.ofFn x) = restrict0True x) ∧
    (∀ x : Fin 6 → Bool, w1False.eval (List.ofFn x) = restrict1False x) ∧
    (∀ x : Fin 6 → Bool, w1True.eval (List.ofFn x) = restrict1True x) := by
  decide +kernel

end SophiaResearch.DoubleStar
