import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem getD_oneEach {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n + n) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hlen : (oneEach u v).length = n + n := by simp [oneEach]
  rw [List.getD_eq_getElem _ _ (by omega)]
  simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
  split_ifs with h
  · have hne : ¬ i = n + v.val := by omega
    simp [Fin.ext_iff, hne, eq_comm]
  · have hne : ¬ i = u.val := by omega
    have hiff : i - n = v.val ↔ i = n + v.val := by omega
    simp [Fin.ext_iff, hne, hiff]

private theorem getD_step_push (w : List Bool) (g : Gate) :
    (stepGate w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [stepGate]

private theorem getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (stepGate w g).getD i false = w.getD i false := by
  rw [stepGate, List.getD_append _ _ _ _ hi]

private def buildC (n : ℕ) : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, n]⟩,
      ⟨GateOp.and, [1, n + 1]⟩,
      ⟨GateOp.or, [2 * n, 2 * n + 1]⟩,
      ⟨GateOp.not, [2 * n + 2]⟩
    ],
    output := 2 * n + 3 }

private theorem buildC_fan (n : ℕ) : FanInTwo (buildC n) := by
  intro g hg
  simp only [buildC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

private theorem buildC_rep (n : ℕ) (hn : 2 ≤ n) :
    Represents (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) (buildC n) := by
  intro u v
  simp only [Circuit.eval, Circuit.wires, buildC]
  change (([⟨GateOp.and, [0, n]⟩, ⟨GateOp.and, [1, n + 1]⟩,
    ⟨GateOp.or, [2 * n, 2 * n + 1]⟩, ⟨GateOp.not, [2 * n + 2]⟩] : List Gate).foldl
    stepGate (oneEach u v)).getD (2 * n + 3) false = _
  simp only [List.foldl_cons, List.foldl_nil]
  set w0 := oneEach u v
  have hl0 : w0.length = 2 * n := by simp [w0, oneEach]; omega
  set s0 := stepGate w0 ⟨GateOp.and, [0, n]⟩
  have hl1 : s0.length = 2 * n + 1 := by simp [s0, stepGate, hl0]
  have hs0 : s0.getD (2 * n) false = (w0.getD 0 false && w0.getD n false) := by
    have := getD_step_push w0 ⟨GateOp.and, [0, n]⟩
    rw [hl0] at this; rw [this]; simp [GateOp.eval]
  set s1 := stepGate s0 ⟨GateOp.and, [1, n + 1]⟩
  have hl2 : s1.length = 2 * n + 2 := by simp [s1, stepGate, hl1]
  have hs1 : s1.getD (2 * n + 1) false = (w0.getD 1 false && w0.getD (n + 1) false) := by
    have := getD_step_push s0 ⟨GateOp.and, [1, n + 1]⟩
    rw [hl1] at this
    rw [this]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [getD_step_lt w0 _ 1 (by omega), getD_step_lt w0 _ (n + 1) (by omega)]
  set s2 := stepGate s1 ⟨GateOp.or, [2 * n, 2 * n + 1]⟩
  have hl3 : s2.length = 2 * n + 3 := by simp [s2, stepGate, hl2]
  have hs2 : s2.getD (2 * n + 2) false = (s0.getD (2 * n) false || s1.getD (2 * n + 1) false) := by
    have := getD_step_push s1 ⟨GateOp.or, [2 * n, 2 * n + 1]⟩
    rw [hl2] at this
    rw [this]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rw [getD_step_lt s0 _ (2 * n) (by omega)]
  have hs3 : (stepGate s2 ⟨GateOp.not, [2 * n + 2]⟩).getD (2 * n + 3) false =
      !(s2.getD (2 * n + 2) false) := by
    have := getD_step_push s2 ⟨GateOp.not, [2 * n + 2]⟩
    rw [hl3] at this; rw [this]; simp [GateOp.eval]
  rw [hs3, hs2, hs0, hs1,
    getD_oneEach u v 0 (by omega), getD_oneEach u v n (by omega),
    getD_oneEach u v 1 (by omega), getD_oneEach u v (n + 1) (by omega)]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Fin.ext_iff]
  have := u.isLt; have := v.isLt
  omega

end PEqualNP.Outside.L_meta_20545

theorem PEqualNP.Outside.L_meta_20545 : ∀ n : ℕ, 2 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) C := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_20545.buildC n,
    PEqualNP.Outside.L_meta_20545.buildC_fan n,
    by simp [PEqualNP.Outside.L_meta_20545.buildC, PEqualNP.CircuitLowerBounds.Circuit.size],
    PEqualNP.Outside.L_meta_20545.buildC_rep n hn⟩
