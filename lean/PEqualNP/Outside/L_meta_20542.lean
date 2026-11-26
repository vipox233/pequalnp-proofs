import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20542_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_20542_aux

open PEqualNP.Outside.L_meta_20542_aux in
theorem PEqualNP.Outside.L_meta_20542 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ 2 ≤ v.val) ∨ (u.val = 1 ∧ (v.val ≤ 1 ∨ 3 ≤ v.val)) ∨ (u.val = 2 ∧ v.val ≤ 1) ∨ (3 ≤ u.val ∧ v.val ≤ 2))) C := by
  intro n hn
  refine ⟨⟨[⟨.or, [0, n + 2]⟩, ⟨.or, [1, n + 1]⟩, ⟨.or, [n, n + n + 1]⟩, ⟨.or, [2, n + n + 2]⟩,
    ⟨.or, [n + n, n + n + 2]⟩, ⟨.and, [n + n, n + n + 3]⟩, ⟨.not, [n + n + 5]⟩,
    ⟨.and, [n + n + 4, n + n + 6]⟩], n + n + 7⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n + n := by
      simp [PEqualNP.Represents.oneEach]
    have h0 : (PEqualNP.Represents.oneEach u v).getD 0 false = decide (u.val = 0) := by
      simpa [Fin.ext_iff] using gL u ⟨0, by omega⟩ v
    have h1 : (PEqualNP.Represents.oneEach u v).getD 1 false = decide (u.val = 1) := by
      simpa [Fin.ext_iff] using gL u ⟨1, by omega⟩ v
    have h2 : (PEqualNP.Represents.oneEach u v).getD 2 false = decide (u.val = 2) := by
      simpa [Fin.ext_iff] using gL u ⟨2, by omega⟩ v
    have h3 : (PEqualNP.Represents.oneEach u v).getD n false = decide (v.val = 0) := by
      simpa [Fin.ext_iff] using gR u v ⟨0, by omega⟩
    have h4 : (PEqualNP.Represents.oneEach u v).getD (n + 1) false = decide (v.val = 1) := by
      simpa [Fin.ext_iff] using gR u v ⟨1, by omega⟩
    have h5 : (PEqualNP.Represents.oneEach u v).getD (n + 2) false = decide (v.val = 2) := by
      simpa [Fin.ext_iff] using gR u v ⟨2, by omega⟩
    generalize PEqualNP.Represents.oneEach u v = l at hl h0 h1 h2 h3 h4 h5
    have i0 : 0 < l.length := by omega
    have i1 : 1 < l.length := by omega
    have i2 : 2 < l.length := by omega
    have i3 : n < l.length := by omega
    have i4 : n + 1 < l.length := by omega
    have i5 : n + 2 < l.length := by omega
    rw [List.getD_eq_getElem?_getD] at h0 h1 h2 h3 h4 h5
    rw [show n + n = l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl, List.map, List.getD_eq_getElem?_getD, List.append_assoc, List.cons_append,
      List.nil_append, List.getElem?_append_left i0, List.getElem?_append_left i1,
      List.getElem?_append_left i2, List.getElem?_append_left i3, List.getElem?_append_left i4,
      List.getElem?_append_left i5, h0, h1, h2, h3, h4, h5,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
    have := u.isLt; have := v.isLt
    by_cases a : u.val = 0 <;> by_cases b : u.val = 1 <;> by_cases b2 : u.val = 2 <;>
      by_cases c : v.val = 0 <;> by_cases d : v.val = 1 <;> by_cases e : v.val = 2 <;>
      simp [a, b, b2, c, d, e] <;> omega
