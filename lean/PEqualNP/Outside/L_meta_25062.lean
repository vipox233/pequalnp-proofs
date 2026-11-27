import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25062_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_25062_aux

open PEqualNP.Outside.L_meta_25062_aux in
theorem PEqualNP.Outside.L_meta_25062 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≠ 1) ∨ (2 ≤ u.val ∧ v.val = 0))) C := by
  intro n hn
  refine ⟨⟨[⟨.or, [0, n + 1]⟩, ⟨.or, [1, n]⟩, ⟨.or, [0, n + n + 1]⟩, ⟨.and, [n + n, n + n + 1]⟩, ⟨.not, [n + n + 3]⟩, ⟨.and, [n + n + 2, n + n + 4]⟩],
    n + n + 5⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h0 : (PEqualNP.Represents.oneEach u v).getD (0) false = decide (u.val = 0) := by
      simpa [Fin.ext_iff] using gL u ⟨0, by omega⟩ v
    have h1 : (PEqualNP.Represents.oneEach u v).getD (1) false = decide (u.val = 1) := by
      simpa [Fin.ext_iff] using gL u ⟨1, by omega⟩ v
    have h2 : (PEqualNP.Represents.oneEach u v).getD (n) false = decide (v.val = 0) := by
      simpa [Fin.ext_iff] using gR u v ⟨0, by omega⟩
    have h3 : (PEqualNP.Represents.oneEach u v).getD (n + 1) false = decide (v.val = 1) := by
      simpa [Fin.ext_iff] using gR u v ⟨1, by omega⟩
    generalize PEqualNP.Represents.oneEach u v = l at hl h0 h1 h2 h3
    have i0 : 0 < l.length := by omega
    have i1 : 1 < l.length := by omega
    have i2 : n < l.length := by omega
    have i3 : n + 1 < l.length := by omega
    rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3
    rw [show n + n = l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl, List.map, List.getD_eq_getElem?_getD, List.append_assoc, List.cons_append,
      List.nil_append, List.getElem?_append_left i0, List.getElem?_append_left i1, List.getElem?_append_left i2, List.getElem?_append_left i3,
      h0, h1, h2, h3,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
    have := u.isLt; have := v.isLt
    first
      | (apply Bool.eq_iff_iff.2
         simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
           Bool.not_true, decide_eq_false_iff_not]
         constructor <;> intro h <;> omega)
      | (by_cases a0 : u.val = 0 <;> by_cases a1 : u.val = 1 <;> by_cases a2 : v.val = 0 <;> by_cases a3 : v.val = 1 <;>
           simp [a0, a1, a2, a3] <;> omega)
