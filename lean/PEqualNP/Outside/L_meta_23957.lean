import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23957

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ (n : ℕ) : Circuit :=
  ⟨[ ⟨GateOp.or, [0, n]⟩,
     ⟨GateOp.and, [0, n]⟩,
     ⟨GateOp.not, [2 * n + 1]⟩,
     ⟨GateOp.and, [2 * n, 2 * n + 2]⟩,
     ⟨GateOp.and, [1, n + 1]⟩,
     ⟨GateOp.or, [2 * n + 3, 2 * n + 4]⟩ ],
   2 * n + 5⟩

theorem circ_fan (n : ℕ) : FanInTwo (circ n) := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_size (n : ℕ) : (circ n).size ≤ 6 := by
  simp [circ, Circuit.size]

theorem getD_append_left (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_append_right_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem oneEach_len {n : ℕ} (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]
  omega

theorem oneEach_getD_left {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD k false = decide (u.val = k) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [hk]), List.getElem?_ofFn]
  simp [hk, Fin.ext_iff, eq_comm]

theorem oneEach_getD_right {n : ℕ} (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD (n + k) false = decide (v.val = k) := by
  simp only [oneEach, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left,
      List.getElem?_ofFn]
  simp [hk, Fin.ext_iff, eq_comm]

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem circ_eval (n : ℕ) (hn : 3 ≤ n) (u v : Fin n) :
    (circ n).eval (oneEach u v) =
      decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≤ 1) ∨ (2 ≤ u.val ∧ v.val = 0)) := by
  let w0 := oneEach u v
  have hw0 : w0.length = 2 * n := oneEach_len u v
  have h0 : w0.getD 0 false = decide (u.val = 0) := oneEach_getD_left u v 0 (by omega)
  have h1 : w0.getD 1 false = decide (u.val = 1) := oneEach_getD_left u v 1 (by omega)
  have hn0 : w0.getD n false = decide (v.val = 0) := oneEach_getD_right u v 0 (by omega)
  have hn1 : w0.getD (n + 1) false = decide (v.val = 1) := oneEach_getD_right u v 1 (by omega)
  let g0 : Gate := ⟨GateOp.or, [0, n]⟩
  let g1 : Gate := ⟨GateOp.and, [0, n]⟩
  let g2 : Gate := ⟨GateOp.not, [2 * n + 1]⟩
  let g3 : Gate := ⟨GateOp.and, [2 * n, 2 * n + 2]⟩
  let g4 : Gate := ⟨GateOp.and, [1, n + 1]⟩
  let g5 : Gate := ⟨GateOp.or, [2 * n + 3, 2 * n + 4]⟩
  let v0 := decide (u.val = 0) || decide (v.val = 0)
  let v1 := decide (u.val = 0) && decide (v.val = 0)
  let v2 := !v1
  let v3 := v0 && v2
  let v4 := decide (u.val = 1) && decide (v.val = 1)
  let v5 := v3 || v4
  let w1 := stp w0 g0
  have ew1 : w1 = w0 ++ [v0] := by
    simp only [w1, stp, g0, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, h0, hn0, v0, id_eq]
  have hw1 : w1.length = 2 * n + 1 := by simp [ew1, hw0]
  let w2 := stp w1 g1
  have hw1_0 : w1.getD 0 false = decide (u.val = 0) := by
    rw [ew1, getD_append_left _ _ _ (by omega)]; exact h0
  have hw1_n : w1.getD n false = decide (v.val = 0) := by
    rw [ew1, getD_append_left _ _ _ (by omega)]; exact hn0
  have ew2 : w2 = w1 ++ [v1] := by
    simp only [w2, stp, g1, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, hw1_0, hw1_n, v1, id_eq]
  have hw2 : w2.length = 2 * n + 2 := by simp [ew2, hw1]
  let w3 := stp w2 g2
  have hw2_out : w2.getD (2 * n + 1) false = v1 := by
    rw [ew2, ← hw1, getD_append_right_eq]
  have ew3 : w3 = w2 ++ [v2] := by
    simp only [w3, stp, g2, GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, hw2_out, v2]
  have hw3 : w3.length = 2 * n + 3 := by simp [ew3, hw2]
  let w4 := stp w3 g3
  have hw3_2n : w3.getD (2 * n) false = v0 := by
    rw [ew3, getD_append_left _ _ _ (by omega), ew2, getD_append_left _ _ _ (by omega), ew1, ← hw0, getD_append_right_eq]
  have hw3_out : w3.getD (2 * n + 2) false = v2 := by
    rw [ew3, ← hw2, getD_append_right_eq]
  have ew4 : w4 = w3 ++ [v3] := by
    simp only [w4, stp, g3, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, hw3_2n, hw3_out, v3, id_eq]
  have hw4 : w4.length = 2 * n + 4 := by simp [ew4, hw3]
  let w5 := stp w4 g4
  have hw4_1 : w4.getD 1 false = decide (u.val = 1) := by
    rw [ew4, getD_append_left _ _ _ (by omega), ew3, getD_append_left _ _ _ (by omega),
        ew2, getD_append_left _ _ _ (by omega), ew1, getD_append_left _ _ _ (by omega)]; exact h1
  have hw4_n1 : w4.getD (n + 1) false = decide (v.val = 1) := by
    rw [ew4, getD_append_left _ _ _ (by omega), ew3, getD_append_left _ _ _ (by omega),
        ew2, getD_append_left _ _ _ (by omega), ew1, getD_append_left _ _ _ (by omega)]; exact hn1
  have ew5 : w5 = w4 ++ [v4] := by
    simp only [w5, stp, g4, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, hw4_1, hw4_n1, v4, id_eq]
  have hw5 : w5.length = 2 * n + 5 := by simp [ew5, hw4]
  let w6 := stp w5 g5
  have hw5_v3 : w5.getD (2 * n + 3) false = v3 := by
    rw [ew5, getD_append_left _ _ _ (by omega), ew4, ← hw3, getD_append_right_eq]
  have hw5_v4 : w5.getD (2 * n + 4) false = v4 := by
    rw [ew5, ← hw4, getD_append_right_eq]
  have ew6 : w6 = w5 ++ [v5] := by
    simp only [w6, stp, g5, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, hw5_v3, hw5_v4, v5, id_eq]
  have heval : (circ n).eval (oneEach u v) = v5 := by
    change w6.getD (2 * n + 5) false = v5
    rw [ew6, ← hw5, getD_append_right_eq]
  rw [heval]
  dsimp only [v5, v3, v4, v2, v0, v1]
  by_cases hu0 : u.val = 0 <;> by_cases hu1 : u.val = 1 <;>
    by_cases hv0 : v.val = 0 <;> by_cases hv1 : v.val = 1 <;>
    simp_all <;> omega

end PEqualNP.Outside.L_meta_23957

theorem PEqualNP.Outside.L_meta_23957 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≤ 1) ∨ (2 ≤ u.val ∧ v.val = 0))) C :=
  fun n hn => ⟨PEqualNP.Outside.L_meta_23957.circ n,
    PEqualNP.Outside.L_meta_23957.circ_fan n,
    PEqualNP.Outside.L_meta_23957.circ_size n,
    fun u v => PEqualNP.Outside.L_meta_23957.circ_eval n hn u v⟩
