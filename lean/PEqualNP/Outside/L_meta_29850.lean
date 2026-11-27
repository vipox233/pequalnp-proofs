import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29850

open PEqualNP.CircuitLowerBounds

lemma foldl_wires_eq (gs : List Gate) (ws1 ws2 : List Bool)
    (hlen : ws1.length = ws2.length)
    (h5len : 5 < ws1.length)
    (h5a : ws1.getD 5 false = true)
    (h5b : ws2.getD 5 false = true)
    (hinv : ∀ m, m ≠ 0 → ws1.getD m false = ws2.getD m false)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.or ∧ 5 ∈ g.inputs) ∨ 0 ∉ g.inputs) :
    ∀ m, m ≠ 0 →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ws1).getD m false =
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ws2).getD m false := by
  induction gs generalizing ws1 ws2 with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg := hgs g (by simp)
    have hbit : g.op.eval (g.inputs.map (fun i => ws1.getD i false)) =
                g.op.eval (g.inputs.map (fun i => ws2.getD i false)) := by
      rcases hg with ⟨hop, h5in⟩ | h0not
      · have hev : ∀ (w : List Bool), w.getD 5 false = true →
            GateOp.or.eval (g.inputs.map (fun i => w.getD i false)) = true := by
          intro w hw
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨5, h5in, hw⟩, rfl⟩
        rw [hop, hev ws1 h5a, hev ws2 h5b]
      · congr 1
        apply List.map_congr_left
        intro m hm
        exact hinv m (fun h0 => h0not (h0 ▸ hm))
    apply ih
    · simp [hlen]
    · simp; omega
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, h5a]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD, h5b]
    · intro m hm
      rw [hbit]
      by_cases hmlt : m < ws1.length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hmlt]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
        exact hinv m hm
      · have hle : ws1.length ≤ m := by omega
        have hle2 : ws2.length ≤ m := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hle]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hle2, hlen]
    · intro g' hg'
      exact hgs g' (by simp [hg'])

lemma foldl_wires_head (gs : List Gate) (ws : List Bool) (h0 : 0 < ws.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ws).getD 0 false =
    ws.getD 0 false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (ws ++ [g.op.eval (g.inputs.map (fun i => ws.getD i false))]) (by simp)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h0, ← List.getD_eq_getElem?_getD]

end PEqualNP.Outside.L_meta_29850

theorem PEqualNP.Outside.L_meta_29850 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 5 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true) := by
  rintro ⟨C, i, k, _, _, _, heval, _, h0only, hor, _, _, _, h5i, _, _, _⟩
  by_cases h0out : C.output = 0
  · let c : Fin 7 → Bool := ![true, false, false, false, false, false, false]
    have hc := heval c
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, h0out] at hc
    rw [PEqualNP.Outside.L_meta_29850.foldl_wires_head _ _ (by simp [c])] at hc
    simp [c] at hc
  · let a : Fin 7 → Bool := ![false, true, false, false, false, true, false]
    let b : Fin 7 → Bool := ![true, true, false, false, false, true, false]
    have ha := heval a
    have hb := heval b
    have heq : C.eval (List.ofFn a) = C.eval (List.ofFn b) := by
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
      apply PEqualNP.Outside.L_meta_29850.foldl_wires_eq C.gates (List.ofFn a) (List.ofFn b)
      · simp
      · simp
      · decide
      · decide
      · intro m hm
        rcases m with _ | _ | _ | _ | _ | _ | _ | m
        · contradiction
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · simp [List.getD_eq_getElem?_getD, a, b]
      · intro g hg
        rcases List.mem_iff_get.mp hg with ⟨j, rfl⟩
        by_cases h0in : (0 : ℕ) ∈ (C.gates.get j).inputs
        · have hj : j = i := h0only j h0in
          subst hj
          left
          exact ⟨hor, h5i⟩
        · right
          exact h0in
      · exact h0out
    rw [ha, hb] at heq
    simp [a, b] at heq
