import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25440_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

theorem mask {n : ℕ} (u v : Fin n) :
    (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3) = decide ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 0 ∧ v.val = 2) ∨ (u.val = 0 ∧ 3 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (u.val = 1 ∧ v.val = 2) ∨ (u.val = 1 ∧ 3 ≤ v.val) ∨ (u.val = 2 ∧ v.val = 0) ∨ (u.val = 2 ∧ v.val = 1) ∨ (u.val = 2 ∧ 3 ≤ v.val) ∨ (3 ≤ u.val ∧ v.val = 0) ∨ (3 ≤ u.val ∧ v.val = 1) ∨ (3 ≤ u.val ∧ v.val = 2) ∨ (3 ≤ u.val ∧ 3 ≤ v.val)) := by
  generalize u.val = a
  generalize v.val = b
  have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ 3 ≤ a := by omega
  have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ 3 ≤ b := by omega
  rcases ha with rfl | rfl | rfl | ha <;> rcases hb with rfl | rfl | rfl | hb <;>
    simp [Nat.min_eq_right, Nat.testBit, *] <;> omega

theorem core : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 0 ∧ v.val = 2) ∨ (u.val = 0 ∧ 3 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (u.val = 1 ∧ v.val = 2) ∨ (u.val = 1 ∧ 3 ≤ v.val) ∨ (u.val = 2 ∧ v.val = 0) ∨ (u.val = 2 ∧ v.val = 1) ∨ (u.val = 2 ∧ 3 ≤ v.val) ∨ (3 ≤ u.val ∧ v.val = 0) ∨ (3 ≤ u.val ∧ v.val = 1) ∨ (3 ≤ u.val ∧ v.val = 2) ∨ (3 ≤ u.val ∧ 3 ≤ v.val))) C := by
  intro n hn
  refine ⟨⟨[⟨.and, [1, n + 1]⟩, ⟨.and, [0, n]⟩, ⟨.and, [2, n + 2]⟩, ⟨.or, [n + n, n + n + 2]⟩, ⟨.or, [n + n + 1, n + n + 3]⟩, ⟨.not, [n + n + 4]⟩],
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
    have h2 : (PEqualNP.Represents.oneEach u v).getD (2) false = decide (u.val = 2) := by
      simpa [Fin.ext_iff] using gL u ⟨2, by omega⟩ v
    have h3 : (PEqualNP.Represents.oneEach u v).getD (n) false = decide (v.val = 0) := by
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
      List.nil_append, List.getElem?_append_left i0, List.getElem?_append_left i1, List.getElem?_append_left i2, List.getElem?_append_left i3, List.getElem?_append_left i4, List.getElem?_append_left i5,
      h0, h1, h2, h3, h4, h5,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      PEqualNP.CircuitLowerBounds.GateOp.eval]
    simp
    have := u.isLt; have := v.isLt
    first
      | (apply Bool.eq_iff_iff.2
         simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
           Bool.not_true, decide_eq_false_iff_not]
         constructor <;> intro h <;> omega)
      | (by_cases a0 : u.val = 0 <;> by_cases a1 : u.val = 1 <;> by_cases a2 : u.val = 2 <;> by_cases a3 : v.val = 0 <;> by_cases a4 : v.val = 1 <;> by_cases a5 : v.val = 2 <;>
           simp [a0, a1, a2, a3, a4, a5] <;> omega)

end PEqualNP.Outside.L_meta_25440_aux

open PEqualNP.Outside.L_meta_25440_aux in
theorem PEqualNP.Outside.L_meta_25440 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) C := by
  intro n hn
  have e : (fun (u : Fin n) (v : Fin n) => (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) = (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val = 1) ∨ (u.val = 0 ∧ v.val = 2) ∨ (u.val = 0 ∧ 3 ≤ v.val) ∨ (u.val = 1 ∧ v.val = 0) ∨ (u.val = 1 ∧ v.val = 2) ∨ (u.val = 1 ∧ 3 ≤ v.val) ∨ (u.val = 2 ∧ v.val = 0) ∨ (u.val = 2 ∧ v.val = 1) ∨ (u.val = 2 ∧ 3 ≤ v.val) ∨ (3 ≤ u.val ∧ v.val = 0) ∨ (3 ≤ u.val ∧ v.val = 1) ∨ (3 ≤ u.val ∧ v.val = 2) ∨ (3 ≤ u.val ∧ 3 ≤ v.val))) := by
    funext u v
    exact mask u v
  rw [e]
  exact core n hn
