import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21118

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circ : Circuit := ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [3, 9]⟩, ⟨GateOp.or, [2, 8]⟩, ⟨GateOp.or, [6, 11]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [13, 14]⟩, ⟨GateOp.or, [7, 12]⟩, ⟨GateOp.and, [10, 16]⟩, ⟨GateOp.or, [15, 17]⟩], 18⟩

def monoOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

lemma monoOp_mem (o : GateOp) (h : monoOp o = true) :
    o ∈ ({GateOp.and, GateOp.or} : Set GateOp) := by
  cases o <;> simp_all [monoOp]

lemma all_mono : ∀ g ∈ circ.gates, monoOp g.op = true ∧ g.inputs.length ≤ 2 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma l0 : Monotone2 circ :=
  fun g hg => ⟨monoOp_mem _ (all_mono g hg).1, (all_mono g hg).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma l1 : circ.size ≤ 10 :=
  by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma l2 : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (36057 : ℕ).testBit (5 * u.val + v.val)) circ :=
  by decide +kernel

end PEqualNP.Outside.L_meta_21118

theorem PEqualNP.Outside.L_meta_21118 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36057 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21118.circ, PEqualNP.Outside.L_meta_21118.l0, PEqualNP.Outside.L_meta_21118.l1, PEqualNP.Outside.L_meta_21118.l2⟩
