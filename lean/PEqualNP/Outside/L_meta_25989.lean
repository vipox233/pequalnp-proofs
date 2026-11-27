import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25989
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[
      ⟨.or, [2, 1]⟩,
      ⟨.and, [4, 0]⟩,
      ⟨.not, [9]⟩,
      ⟨.or, [4, 0]⟩,
      ⟨.and, [5, 8]⟩,
      ⟨.or, [11, 12]⟩,
      ⟨.and, [6, 1]⟩,
      ⟨.or, [13, 14]⟩,
      ⟨.and, [10, 15]⟩], 16⟩

def allowed (op : GateOp) : Bool :=
  match op with
  | .and | .or | .not => true
  | _ => false

theorem basis : FanInTwo circuit := by
  have h : circuit.gates.all (fun g => allowed g.op && decide (g.inputs.length ≤ 2)) = true := by decide
  intro g hg
  obtain ⟨kind, arity⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp h g hg)
  refine ⟨?_, of_decide_eq_true arity⟩
  cases op : g.op <;> rw [op] at kind <;> simp_all [allowed]


end PEqualNP.Outside.L_meta_25989

theorem PEqualNP.Outside.L_meta_25989 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 7, 3, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨PEqualNP.Outside.L_meta_25989.circuit, PEqualNP.Outside.L_meta_25989.basis, by decide, by decide, ?_⟩
  intro u v
  fin_cases u <;> fin_cases v <;> decide +kernel
