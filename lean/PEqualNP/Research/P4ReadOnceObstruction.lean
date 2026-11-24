import Init
/-!
Finite certificate: the P4 edge function is not computed by any full binary
AND/OR formula with four leaves, including repeated variable labels.
There are 5 full binary tree shapes, 8 binary gate-operation choices,
and 4^4 choices of input variables. Every 16-row truth table is represented
as a single BitVec 16, so no 16-deep nested evaluator is needed.
This is a local auxiliary lemma, NOT a full L-meta-519 proof.
-/
namespace SophiaResearch.ReadOnceP4

def inputMask : Fin 4 → BitVec 16
  | 0 => 0xAAAA#16
  | 1 => 0xCCCC#16
  | 2 => 0xF0F0#16
  | 3 => 0xFF00#16

def combine (op : Bool) (x y : BitVec 16) : BitVec 16 :=
  if op then x &&& y else x ||| y

def P4target : BitVec 16 :=
  (inputMask 0 &&& inputMask 1) |||
  (inputMask 1 &&& inputMask 2) |||
  (inputMask 2 &&& inputMask 3)

def eval (shape : Fin 5) (ops : Fin 8)
    (a b c d : Fin 4) : BitVec 16 :=
  let x := inputMask a
  let y := inputMask b
  let z := inputMask c
  let w := inputMask d
  let p := combine (ops.val.testBit 0)
  let q := combine (ops.val.testBit 1)
  let t := combine (ops.val.testBit 2)
  match shape.val with
  | 0 => t (q (p x y) z) w
  | 1 => t (q x (p y z)) w
  | 2 => t (p x y) (q z w)
  | 3 => t x (q (p y z) w)
  | _ => t x (q y (p z w))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 20000000 in
theorem no_four_leaf_formula :
    ∀ (shape : Fin 5) (ops : Fin 8) (a b c d : Fin 4),
      eval shape ops a b c d ≠ P4target := by
  decide +kernel

theorem input_masks_are_truth_table_columns :
    ∀ (i : Fin 4) (r : Fin 16),
      (inputMask i).getLsbD r.val = r.val.testBit i.val := by
  decide +kernel

theorem target_is_P4_edge_function :
    ∀ r : Fin 16,
      P4target.getLsbD r.val =
        ((r.val.testBit 0 && r.val.testBit 1) ||
         (r.val.testBit 1 && r.val.testBit 2) ||
         (r.val.testBit 2 && r.val.testBit 3)) := by
  decide +kernel

end SophiaResearch.ReadOnceP4

#print axioms SophiaResearch.ReadOnceP4.no_four_leaf_formula
#print axioms SophiaResearch.ReadOnceP4.input_masks_are_truth_table_columns
#print axioms SophiaResearch.ReadOnceP4.target_is_P4_edge_function
