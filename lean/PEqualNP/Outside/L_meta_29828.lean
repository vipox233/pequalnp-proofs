import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29828

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]

private theorem getD_append_lt {w : List Bool} {v : Bool} {m : ℕ} (hm : m < w.length) :
    (w ++ [v]).getD m false = w.getD m false := by
  have hm' : m < (w ++ [v]).length := by simp; omega
  rw [List.getD_eq_getElem _ _ hm', List.getD_eq_getElem _ _ hm, List.getElem_append_left hm]

private theorem getD_append_eq {w : List Bool} {v : Bool} :
    (w ++ [v]).getD w.length false = v := by
  have hm' : w.length < (w ++ [v]).length := by simp
  rw [List.getD_eq_getElem _ _ hm', List.getElem_append_right (Nat.le_refl _)]
  simp

private theorem getD_append_gt {w : List Bool} {v : Bool} {m : ℕ} (hm : w.length < m) :
    (w ++ [v]).getD m false = false := by
  have hge : (w ++ [v]).length ≤ m := by simp; omega
  exact List.getD_eq_default _ _ hge

private theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (m : ℕ) (hm : m < w.length) :
    (gs.foldl step w).getD m false = w.getD m false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hm' : m < (step w g).length := by simp [step]; omega
    rw [ih (step w g) hm', step, getD_append_lt hm]

private theorem foldl_preserves (gs : List Gate)
    (hgs : ∀ g ∈ gs, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ 2 ∈ g.inputs))
    (w1 w2 : List Bool)
    (hlen : w1.length = w2.length)
    (hge : 3 ≤ w1.length)
    (h2 : w1.getD 2 false = true)
    (hag : ∀ m, m ≠ 0 → w1.getD m false = w2.getD m false) :
    ∀ m, m ≠ 0 → (gs.foldl step w1).getD m false = (gs.foldl step w2).getD m false := by
  induction gs generalizing w1 w2 with
  | nil => exact hag
  | cons g rest ih =>
    simp only [List.foldl_cons]
    have hgv : g.op.eval (g.inputs.map fun idx => w1.getD idx false) =
               g.op.eval (g.inputs.map fun idx => w2.getD idx false) := by
      rcases hgs g (List.mem_cons_self ..) with h0 | ⟨hop, h2in⟩
      · congr 1
        apply List.map_congr_left
        intro idx hidx
        exact hag idx (fun h => h0 (h ▸ hidx))
      · have h2' : w2.getD 2 false = true := by rw [← hag 2 (by decide), h2]
        rw [hop]
        dsimp [GateOp.eval]
        have hl1 : (g.inputs.map fun idx => w1.getD idx false).any id = true :=
          List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨2, h2in, h2⟩, rfl⟩
        have hl2 : (g.inputs.map fun idx => w2.getD idx false).any id = true :=
          List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨2, h2in, h2'⟩, rfl⟩
        rw [hl1, hl2]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    · simp [step, hlen]
    · simp [step]; omega
    · simp only [step]
      rw [getD_append_lt (by omega), h2]
    · intro m hm
      simp only [step]
      rcases lt_trichotomy m w1.length with hlt | rfl | hgt
      · rw [getD_append_lt hlt, getD_append_lt (by omega), hag m hm]
      · rw [getD_append_eq, hlen, getD_append_eq, hgv]
      · rw [getD_append_gt hgt, getD_append_gt (by omega)]

end PEqualNP.Outside.L_meta_29828

theorem PEqualNP.Outside.L_meta_29828 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 4 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true)) := by
  rintro ⟨C, i, k, _, _, _, heval, _, huniq, hopi, _, _, _, h2in, _, _, _⟩
  have hout : C.output ≠ 0 := by
    intro h0
    let z : Fin 7 → Bool := ![false, true, true, false, false, false, false]
    have hz1 := heval z
    have hz2 : C.eval (List.ofFn z) = false := by
      dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
      rw [h0]
      change (C.gates.foldl PEqualNP.Outside.L_meta_29828.step (List.ofFn z)).getD 0 false = false
      rw [PEqualNP.Outside.L_meta_29828.foldl_getD_lt C.gates (List.ofFn z) 0 (by simp)]
      rfl
    rw [hz2] at hz1
    exact Bool.false_ne_true hz1
  let x : Fin 7 → Bool := ![false, false, true, false, false, false, true]
  let y : Fin 7 → Bool := ![true, false, true, false, false, false, true]
  have hgs : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ g.inputs) := by
    intro g hg
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    by_cases h0 : 0 ∈ (C.gates.get j).inputs
    · right
      have hji : j = i := huniq j h0
      subst hji
      exact ⟨hopi, h2in⟩
    · exact Or.inl h0
  have heq : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
    dsimp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires]
    apply PEqualNP.Outside.L_meta_29828.foldl_preserves C.gates hgs (List.ofFn x) (List.ofFn y)
    · simp
    · simp
    · rfl
    · intro m hm
      by_cases hlt : m < 7
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
        simp only [List.getElem_ofFn]
        rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact hout
  have hx : C.eval (List.ofFn x) = false := heval x
  have hy : C.eval (List.ofFn y) = true := heval y
  rw [hx, hy] at heq
  exact Bool.false_ne_true heq
