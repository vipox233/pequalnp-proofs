import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25235
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C (n : ℕ) : Circuit :=
  ⟨[⟨.or, [0, n + 1]⟩, ⟨.or, [1, n]⟩, ⟨.and, [2 * n, 2 * n + 1]⟩, ⟨.not, [2 * n + 2]⟩,
    ⟨.or, [2 * n, n]⟩, ⟨.and, [2 * n + 3, 2 * n + 4]⟩], 2 * n + 5⟩

theorem gl (x : List Bool) (bs : List Bool) (i : ℕ) (h : i < x.length) :
    (x ++ bs).getD i false = x.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem gr (x : List Bool) (bs : List Bool) (k : ℕ) :
    (x ++ bs).getD (x.length + k) false = bs.getD k false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem eval_eq (n : ℕ) (hn : 2 ≤ n) (x : List Bool) (hx : x.length = 2 * n) :
    (C n).eval x =
      (!((x.getD 0 false || x.getD (n + 1) false) && (x.getD 1 false || x.getD n false)) &&
        ((x.getD 0 false || x.getD (n + 1) false) || x.getD n false)) := by
  simp only [Circuit.eval, Circuit.wires, C, List.foldl, List.map, List.append_assoc,
    List.cons_append, List.nil_append]
  simp only [gl x _ 1 (by omega), gl x _ n (by omega)]
  simp only [show 2 * n = x.length + 0 by omega, gr]
  simp [GateOp.eval, List.getD]

theorem row {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; exact hi)]
  simp [hi, Fin.ext_iff, eq_comm]

theorem col {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp [hj, Fin.ext_iff, eq_comm]

end PEqualNP.Outside.L_meta_25235

theorem PEqualNP.Outside.L_meta_25235 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val = 0) ∨ (2 ≤ u.val ∧ v.val ≤ 1))) C := by
  intro n hn
  refine ⟨PEqualNP.Outside.L_meta_25235.C n, ?_, by simp [PEqualNP.Outside.L_meta_25235.C, PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  · intro g hg
    simp [PEqualNP.Outside.L_meta_25235.C] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = 2 * n := by
      simp [PEqualNP.Represents.oneEach]; omega
    rw [PEqualNP.Outside.L_meta_25235.eval_eq n (by omega) _ hl]
    have c0 := PEqualNP.Outside.L_meta_25235.col u v 0 (by omega)
    have c1 := PEqualNP.Outside.L_meta_25235.col u v 1 (by omega)
    simp only [Nat.add_zero] at c0
    rw [PEqualNP.Outside.L_meta_25235.row u v 0 (by omega), PEqualNP.Outside.L_meta_25235.row u v 1 (by omega), c0, c1]
    obtain ⟨a, ha⟩ := u
    obtain ⟨b, hb⟩ := v
    simp only
    rcases a with _ | _ | a <;> rcases b with _ | _ | b <;> simp
