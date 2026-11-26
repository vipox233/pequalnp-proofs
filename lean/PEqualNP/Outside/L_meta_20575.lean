import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20575_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_20575_aux

open PEqualNP.Outside.L_meta_20575_aux in
theorem PEqualNP.Outside.L_meta_20575 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) C := by
  intro n hn
  refine ⟨⟨[⟨.or, [n - 2, n - 1]⟩, ⟨.or, [0, n + n]⟩, ⟨.or, [n, n + 1]⟩, ⟨.and, [n + n + 1, n + 2]⟩,
    ⟨.and, [n + n, n + n + 2]⟩, ⟨.or, [n + n + 1, n + 2]⟩, ⟨.not, [n + n + 5]⟩,
    ⟨.or, [n + n + 3, n + n + 6]⟩, ⟨.or, [n + n + 7, n + n + 4]⟩],
    n + n + 8⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h0 : (PEqualNP.Represents.oneEach u v).getD 0 false = decide (u.val = 0) := by
      simpa [Fin.ext_iff] using gL u ⟨0, by omega⟩ v
    have ha : (PEqualNP.Represents.oneEach u v).getD (n - 2) false = decide (u.val + 2 = n) := by
      have := gL u ⟨n - 2, by omega⟩ v
      simp only [Fin.ext_iff] at this
      rw [this]; congr 1; apply propext; omega
    have hb : (PEqualNP.Represents.oneEach u v).getD (n - 1) false = decide (u.val + 1 = n) := by
      have := gL u ⟨n - 1, by omega⟩ v
      simp only [Fin.ext_iff] at this
      rw [this]; congr 1; apply propext; omega
    have hy0 : (PEqualNP.Represents.oneEach u v).getD n false = decide (v.val = 0) := by
      simpa [Fin.ext_iff] using gR u v ⟨0, by omega⟩
    have hy1 : (PEqualNP.Represents.oneEach u v).getD (n + 1) false = decide (v.val = 1) := by
      simpa [Fin.ext_iff] using gR u v ⟨1, by omega⟩
    have hy2 : (PEqualNP.Represents.oneEach u v).getD (n + 2) false = decide (v.val = 2) := by
      simpa [Fin.ext_iff] using gR u v ⟨2, by omega⟩
    generalize PEqualNP.Represents.oneEach u v = l at hl h0 ha hb hy0 hy1 hy2
    have i0 : 0 < l.length := by omega
    have ia : n - 2 < l.length := by omega
    have ib : n - 1 < l.length := by omega
    have j0 : n < l.length := by omega
    have j1 : n + 1 < l.length := by omega
    have j2 : n + 2 < l.length := by omega
    rw [List.getD_eq_getElem?_getD] at h0 ha hb hy0 hy1 hy2
    rw [show n + n = l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl, List.map, List.getD_eq_getElem?_getD, List.append_assoc, List.cons_append,
      List.nil_append, List.getElem?_append_left i0,
      List.getElem?_append_left j0, List.getElem?_append_left j1,
      List.getElem?_append_left j2, h0, ha, hb, hy0, hy1, hy2,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
    have := u.isLt; have := v.isLt
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true, decide_eq_false_iff_not]
    constructor <;> intro h <;> omega
