import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29888_aux

open PEqualNP.CircuitLowerBounds

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x =
      run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

private lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton]
    omega

private lemma run_getD_lt (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc]
    have hlen : w < (run gs x).length := by rw [run_length]; omega
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlen,
      ← List.getD_eq_getElem _ _ hlen, ih]

private lemma run_agree_except_zero (gs : List Gate) (xF xT : List Bool)
    (hlenF : xF.length = 7) (hlenT : xT.length = 7)
    (h5F : xF.getD 5 false = true) (h5T : xT.getD 5 false = true)
    (hinit : ∀ w ≠ 0, xF.getD w false = xT.getD w false)
    (hgate : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = GateOp.or ∧ 5 ∈ g.inputs) :
    ∀ w ≠ 0, (run gs xF).getD w false = (run gs xT).getD w false := by
  induction gs using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => hgate g' (List.mem_append_left _ hg'))
    intro w hw0
    rw [run_snoc, run_snoc]
    have hlen_eq : (run gs xF).length = (run gs xT).length := by
      rw [run_length, run_length, hlenF, hlenT]
    have hval_eq :
        g.op.eval (g.inputs.map fun a => (run gs xF).getD a false) =
        g.op.eval (g.inputs.map fun a => (run gs xT).getD a false) := by
      by_cases h0 : 0 ∈ g.inputs
      · obtain ⟨hop, h5⟩ := hgate g (by simp) h0
        rw [hop]
        have hf5 : (run gs xF).getD 5 false = true := by
          rw [run_getD_lt _ _ _ (by omega)]; exact h5F
        have ht5 : (run gs xT).getD 5 false = true := by
          rw [run_getD_lt _ _ _ (by omega)]; exact h5T
        have htrueF : GateOp.or.eval (g.inputs.map fun a => (run gs xF).getD a false) = true := by
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨5, h5, hf5⟩, rfl⟩
        have htrueT : GateOp.or.eval (g.inputs.map fun a => (run gs xT).getD a false) = true := by
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨5, h5, ht5⟩, rfl⟩
        rw [htrueF, htrueT]
      · congr 1
        apply List.map_congr_left
        intro a ha
        have ha0 : a ≠ 0 := fun h => h0 (h ▸ ha)
        exact ih' a ha0
    rw [hval_eq]
    by_cases hlt : w < (run gs xF).length
    · have hltT : w < (run gs xT).length := by omega
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_append_left hlt, List.getElem_append_left hltT,
        ← List.getD_eq_getElem _ _ hlt, ← List.getD_eq_getElem _ _ hltT]
      exact ih' w hw0
    · by_cases heq : w = (run gs xF).length
      · have heqT : w = (run gs xT).length := by omega
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        simp [heq]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]

private def xF : Fin 7 → Bool := ![false, true, false, false, false, true, false]
private def xT : Fin 7 → Bool := ![true, true, false, false, false, true, false]
private def x0 : Fin 7 → Bool := ![true, false, false, false, false, false, false]

private theorem main_thm :
    ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 7 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true) := by
  rintro ⟨C, i, k, -, -, -, heval, -, huniq, hi_or, -, -, -, hi5, -⟩
  have hgate : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = GateOp.or ∧ 5 ∈ g.inputs := by
    intro g hg h0
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    have hji : j = i := huniq j h0
    subst hji
    exact ⟨hi_or, hi5⟩
  have hout0 : C.output ≠ 0 := by
    intro h0
    have h1 := heval x0
    have h2 : C.eval (List.ofFn x0) = true := by
      change (run C.gates (List.ofFn x0)).getD C.output false = true
      rw [h0, run_getD_lt _ _ _ (by simp)]
      decide
    rw [h2] at h1
    revert h1
    decide
  have hagree := run_agree_except_zero C.gates (List.ofFn xF) (List.ofFn xT)
    (by simp) (by simp) (by decide) (by decide)
    (fun w hw0 => by
      by_cases hw7 : w < 7
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
          List.getElem_ofFn, List.getElem_ofFn]
        have : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)])
    hgate C.output hout0
  have hF : C.eval (List.ofFn xF) = false := by rw [heval xF]; decide
  have hT : C.eval (List.ofFn xT) = true := by rw [heval xT]; decide
  change C.eval (List.ofFn xF) = C.eval (List.ofFn xT) at hagree
  rw [hF, hT] at hagree
  cases hagree

end PEqualNP.Outside.L_meta_29888_aux

theorem PEqualNP.Outside.L_meta_29888 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 7 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true)) :=
  PEqualNP.Outside.L_meta_29888_aux.main_thm
