import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22874

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[
  ⟨.or, [2, 3]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [10, 11]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.or, [14, 9]⟩,
  ⟨.and, [13, 15]⟩,
  ⟨.and, [3, 6]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.and, [18, 7]⟩,
  ⟨.and, [1, 4]⟩,
  ⟨.or, [12, 16]⟩,
  ⟨.or, [21, 17]⟩,
  ⟨.or, [22, 19]⟩,
  ⟨.or, [23, 20]⟩], 24⟩

def monoB (c : Circuit) : Bool := c.gates.all fun g =>
  (match g.op with | .and | .or => true | _ => false) && (g.inputs.length ≤ 2)

private theorem mono_of (c : Circuit) (h : monoB c = true) : Monotone2 c := by
  intro g hg
  have h1 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨?_, h1.2⟩
  cases he : g.op <;> simp [he] at h1 ⊢

def A (u : Fin 4) (v : Fin 6) : Bool := (1883516 : ℕ).testBit (6 * u.val + v.val)

theorem realizes : Represents A C := by
  intro u
  fin_cases u <;> decide +kernel

end PEqualNP.Outside.L_meta_22874

open PEqualNP.Outside.L_meta_22874 in
theorem PEqualNP.Outside.L_meta_22874 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883516 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  exact ⟨C, mono_of C (by decide +kernel), by decide +kernel, realizes⟩
