import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22690

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [11, 6]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [15, 14]⟩,
    ⟨.and, [1, 16]⟩,
    ⟨.and, [0, 14]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 19]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [21, 18]⟩,
    ⟨.or, [22, 20]⟩], 23⟩

private def monotoneOp (op : GateOp) : Bool :=
  match op with
  | .and | .or => true
  | _ => false

private theorem witness_monotone : Monotone2 witness := by
  have check : witness.gates.all (fun g => monotoneOp g.op && decide (g.inputs.length ≤ 2)) =
      true := by decide +kernel
  intro g hg
  have shape := List.all_eq_true.mp check g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at shape
  refine ⟨?_, shape.2⟩
  cases op : g.op <;> simp [op, monotoneOp] at shape ⊢

end PEqualNP.Outside.L_meta_22690

open PEqualNP.Outside.L_meta_22690 in
theorem PEqualNP.Outside.L_meta_22690 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843197 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨witness, witness_monotone, by decide, by decide +kernel⟩
