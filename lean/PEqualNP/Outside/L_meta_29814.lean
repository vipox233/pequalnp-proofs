import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29814_aux

theorem wires_foldl_getD_lt (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (r : ℕ) (hr : r < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w).getD r false =
    w.getD r false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hr' : r < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      rw [List.length_append]; omega
    rw [ih _ hr']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hr]

theorem foldl_agree (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hgs : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ g.inputs)
    (w1 w2 : List Bool) (hlen : w1.length = w2.length) (hge3 : 3 ≤ w1.length)
    (h21 : w1.getD 2 false = true) (h22 : w2.getD 2 false = true)
    (hagr : ∀ r, r ≠ 0 → w1.getD r false = w2.getD r false) :
    ∀ r, r ≠ 0 →
      (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w1).getD r false =
      (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w2).getD r false := by
  induction gs generalizing w1 w2 with
  | nil => exact hagr
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hgs' : ∀ g' ∈ gs, 0 ∈ g'.inputs → g'.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ g'.inputs :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem g hg')
    have hval : g.op.eval (g.inputs.map fun k => w1.getD k false) =
        g.op.eval (g.inputs.map fun k => w2.getD k false) := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨hop, h2in⟩ := hgs g (List.mem_cons_self) h0
        rw [hop]
        simp only [PEqualNP.CircuitLowerBounds.GateOp.eval]
        have ht1 : (g.inputs.map fun k => w1.getD k false).any id = true :=
          List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨2, h2in, h21⟩, rfl⟩
        have ht2 : (g.inputs.map fun k => w2.getD k false).any id = true :=
          List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨2, h2in, h22⟩, rfl⟩
        rw [ht1, ht2]
      · congr 1
        refine List.map_congr_left fun k hk => hagr k (fun h => h0 (h ▸ hk))
    refine ih hgs' _ _ (by simp [hlen]) (by simp; omega) ?_ ?_ ?_
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 2 < w1.length by omega)]
      simpa [List.getD_eq_getElem?_getD] using h21
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show 2 < w2.length by omega)]
      simpa [List.getD_eq_getElem?_getD] using h22
    · intro r hr0
      by_cases hlt : r < w1.length
      · have hlt2 : r < w2.length := hlen ▸ hlt
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_append_left hlt2]
        simpa [List.getD_eq_getElem?_getD] using hagr r hr0
      · by_cases heq : r = w1.length
        · subst heq
          rw [hval, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
          simp [hlen]
        · have hgt1 : (w1 ++ [g.op.eval (g.inputs.map fun k => w1.getD k false)]).length ≤ r := by
            simp; omega
          have hgt2 : (w2 ++ [g.op.eval (g.inputs.map fun k => w2.getD k false)]).length ≤ r := by
            simp; omega
          rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none hgt1, List.getElem?_eq_none hgt2]

end PEqualNP.Outside.L_meta_29814_aux

theorem PEqualNP.Outside.L_meta_29814 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 3 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true)) := by
  rintro ⟨C, i, k, _hi3, _hfit, _hsize, heval, _h0in, huniq, hor, _hand, _hik, _hkin, h2in, _h2ne, _h2lt, _hwit⟩
  have hout_ne0 : C.output ≠ 0 := by
    intro h0
    let x0 : Fin 7 → Bool := ![false, true, true, false, false, false, false]
    have h1 := heval x0
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval, h0, PEqualNP.CircuitLowerBounds.Circuit.wires,
      PEqualNP.Outside.L_meta_29814_aux.wires_foldl_getD_lt C.gates (List.ofFn x0) 0 (by simp)] at h1
    simp [x0] at h1
  have hgs : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ∈ g.inputs := by
    intro g hg h0
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    have hji : j = i := huniq j h0
    subst hji
    exact ⟨hor, h2in⟩
  let x1 : Fin 7 → Bool := ![false, false, true, false, false, false, true]
  let x2 : Fin 7 → Bool := ![true, false, true, false, false, false, true]
  have hagr_in : ∀ r, r ≠ 0 → (List.ofFn x1).getD r false = (List.ofFn x2).getD r false := by
    intro r hr0
    by_cases hr7 : r < 7
    · have hcases : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have hge1 : (List.ofFn x1).length ≤ r := by simp; omega
      have hge2 : (List.ofFn x2).length ≤ r := by simp; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]
  have h21 : (List.ofFn x1).getD 2 false = true := rfl
  have h22 : (List.ofFn x2).getD 2 false = true := rfl
  have heq := PEqualNP.Outside.L_meta_29814_aux.foldl_agree C.gates hgs
    (List.ofFn x1) (List.ofFn x2) (by simp) (by simp) h21 h22 hagr_in C.output hout_ne0
  have h1 := heval x1
  have h2 := heval x2
  rw [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires] at h1 h2
  rw [heq, h2] at h1
  simp [x1, x2] at h1
