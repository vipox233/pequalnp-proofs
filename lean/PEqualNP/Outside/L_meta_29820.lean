import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29820

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

private theorem input_preserved (gs : List Gate) (w : List Bool) (j : ℕ)
    (hj : j < w.length) : (gs.foldl step w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hj

-- Once wire 5 is true, every OR gate reading both wires ignores wire 0's value.
private theorem fold_agrees (gs : List Gate) (t : List Bool)
    (ht : 5 < (false :: t).length)
    (h5 : (false :: t).getD 5 false = true)
    (hg : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ 5 ∈ g.inputs) :
    ∃ u : List Bool,
      gs.foldl step (false :: t) = false :: u ∧
      gs.foldl step (true :: t) = true :: u := by
  induction gs generalizing t with
  | nil => exact ⟨t, rfl, rfl⟩
  | cons g gs ih =>
    have hgate :
        g.op.eval (g.inputs.map fun j => (false :: t).getD j false) =
          g.op.eval (g.inputs.map fun j => (true :: t).getD j false) := by
      by_cases hr : 0 ∈ g.inputs
      · obtain ⟨hop, hw⟩ := hg g (List.mem_cons_self ..) hr
        have hor (b : Bool) : g.op.eval (g.inputs.map fun j => (b :: t).getD j false) = true := by
          rw [hop, GateOp.eval]
          apply List.any_eq_true.mpr
          exact ⟨true, List.mem_map.mpr ⟨5, hw, h5⟩, rfl⟩
        rw [hor false, hor true]
      · congr 1
        apply List.map_congr_left
        intro j hj
        cases j with
        | zero => exact (hr hj).elim
        | succ j => rfl
    let bit := g.op.eval (g.inputs.map fun j => (false :: t).getD j false)
    have hstep (b : Bool) : step (b :: t) g = b :: (t ++ [bit]) := by
      cases b
      · rfl
      · change true :: (t ++ [_]) = true :: (t ++ [bit])
        rw [← hgate]
    have h5' : (false :: (t ++ [bit])).getD 5 false = true := by
      change ((false :: t) ++ [bit]).getD 5 false = true
      rw [List.getD_append _ _ _ _ ht, h5]
    obtain ⟨u, hu, hu'⟩ := ih (t ++ [bit]) (by simp at ht ⊢; omega) h5'
      (fun g h => hg g (List.mem_cons_of_mem _ h))
    exact ⟨u, by simpa only [List.foldl_cons, hstep] using hu,
      by simpa only [List.foldl_cons, hstep] using hu'⟩

private def testInput (b : Bool) : Fin 7 → Bool :=
  fun j => b && (j == 0) || (j == 1) || (j == 5)

private def singletonInput : Fin 7 → Bool := fun j => j == 0

private theorem test_list (b : Bool) :
    List.ofFn (testInput b) = [b, true, false, false, false, true, false] := by
  cases b <;> rfl

private theorem contradicts_cycle (C : Circuit)
    (heval : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
        (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)))
    (hg : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 5 ∈ g.inputs) : False := by
  have hout : C.output ≠ 0 := by
    intro h
    have hz := heval singletonInput
    change (C.gates.foldl step (List.ofFn singletonInput)).getD C.output false = false at hz
    rw [h, input_preserved C.gates _ 0 (by simp)] at hz
    exact Bool.noConfusion hz
  obtain ⟨u, hu, hu'⟩ := fold_agrees C.gates [true, false, false, false, true, false]
    (by decide) rfl hg
  have hl := heval (testInput false)
  have hr := heval (testInput true)
  change (C.gates.foldl step (List.ofFn (testInput false))).getD C.output false = false at hl
  change (C.gates.foldl step (List.ofFn (testInput true))).getD C.output false = true at hr
  rw [test_list, hu] at hl
  rw [test_list, hu'] at hr
  cases ho : C.output with
  | zero => exact hout ho
  | succ n =>
    rw [ho] at hl hr
    exact Bool.noConfusion (hl.symm.trans hr)

end PEqualNP.Outside.L_meta_29820

theorem PEqualNP.Outside.L_meta_29820 : ¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 3 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true) := by
  rintro ⟨C, i, _, _, _, _, heval, _, hunique, hop, _, _, _, h5, _⟩
  apply PEqualNP.Outside.L_meta_29820.contradicts_cycle C heval
  intro g hmem hr
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hmem
  rw [hunique j hr]
  exact ⟨hop, h5⟩
