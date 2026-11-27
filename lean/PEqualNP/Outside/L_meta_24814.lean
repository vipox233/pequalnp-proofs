import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24814

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.and, [2, 0]⟩, ⟨GateOp.or, [6, 5]⟩,
  ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.or, [0, 9]⟩,
  ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.and, [13, 12]⟩], 14⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

lemma okOp_mem (o : GateOp) (h : okOp o = true) :
    o ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by
  cases o <;> simp_all [okOp]

lemma all_ok : ∀ g ∈ circ.gates, okOp g.op = true ∧ g.inputs.length ≤ 2 := by
  decide

lemma fan : FanInTwo circ := fun g hg => ⟨okOp_mem _ (all_ok g hg).1, (all_ok g hg).2⟩

lemma size_le : circ.size ≤ 9 := by
  decide

lemma correct : ∀ i j : Fin 6,
    circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
      (2147755 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide

end PEqualNP.Outside.L_meta_24814

theorem PEqualNP.Outside.L_meta_24814 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147755 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨PEqualNP.Outside.L_meta_24814.circ, PEqualNP.Outside.L_meta_24814.fan,
    PEqualNP.Outside.L_meta_24814.size_le, PEqualNP.Outside.L_meta_24814.correct⟩
