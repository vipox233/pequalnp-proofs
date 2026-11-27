import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_29910

private def bank (bit : Bool) (tail : List Bool) : List Bool :=
  bit :: true :: false :: false :: false :: true :: false :: tail

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun u => w.getD u false)]

private theorem masked (g : Gate) (tail : List Bool)
    (h : 0 ∈ g.inputs → g.op = .or ∧ 5 ∈ g.inputs) :
    g.op.eval (g.inputs.map fun u => (bank false tail).getD u false) =
    g.op.eval (g.inputs.map fun u => (bank true tail).getD u false) := by
  by_cases reads : 0 ∈ g.inputs
  · obtain ⟨op, five⟩ := h reads
    have lit (b : Bool) :
        (g.inputs.map fun u => (bank b tail).getD u false).any id = true := by
      apply List.any_eq_true.mpr
      exact ⟨true, List.mem_map.mpr ⟨5, five, rfl⟩, rfl⟩
    rw [op]
    exact (lit false).trans (lit true).symm
  · congr 1
    apply List.map_congr_left
    intro u hu
    cases u with
    | zero => exact (reads hu).elim
    | succ u => rfl

private theorem same_tail (gs : List Gate)
    (h : ∀ g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ 5 ∈ g.inputs) (tail : List Bool) :
    ∃ finalTail, gs.foldl step (bank false tail) = bank false finalTail ∧
      gs.foldl step (bank true tail) = bank true finalTail := by
  induction gs generalizing tail with
  | nil => exact ⟨tail, rfl, rfl⟩
  | cons g gs ih =>
    have e := masked g tail (h g (by simp))
    simp only [List.foldl_cons, step]
    rw [e]
    exact ih (fun a ha => h a (by simp [ha])) _

end PEqualNP.Outside.L_meta_29910

open PEqualNP.Outside.L_meta_29910

theorem PEqualNP.Outside.L_meta_29910 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true)) := by
  rintro ⟨C, i, k, _, _, _, correct, _, onlyReader, orGate, _, _, _, five, _⟩
  have gateRule : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 5 ∈ g.inputs := by
    intro g hg reads
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have eq := onlyReader ⟨j, hj⟩ reads
    subst i
    exact ⟨orGate, five⟩
  let test (b : Bool) (j : Fin 7) : Bool :=
    ((j == 0) && b) || (j == 1) || (j == 5)
  have off := correct (test false)
  have on := correct (test true)
  change (C.gates.foldl step (bank false [])).getD C.output false = false at off
  change (C.gates.foldl step (bank true [])).getD C.output false = true at on
  obtain ⟨t, left, right⟩ := same_tail C.gates gateRule []
  rw [left] at off
  rw [right] at on
  cases ho : C.output with
  | zero =>
    let singleton (j : Fin 7) : Bool := j == 0
    have single := correct singleton
    change (C.wires (List.ofFn singleton)).getD C.output false = false at single
    rw [ho] at single
    have keep (gs : List Gate) (t : List Bool) :
        (gs.foldl step (true :: t)).getD 0 false = true := by
      induction gs generalizing t with
      | nil => rfl
      | cons g rest ih => exact ih _
    exact Bool.noConfusion ((keep C.gates _).symm.trans single)
  | succ u =>
    rw [ho] at off on
    exact Bool.noConfusion (off.symm.trans on)
