import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29804

open PEqualNP.CircuitLowerBounds

def wireBank (b : Bool) (tail : List Bool) : List Bool :=
  b :: true :: false :: true :: tail

def appendGate (bank : List Bool) (g : Gate) : List Bool :=
  bank ++ [g.op.eval (g.inputs.map fun j => bank.getD j false)]

theorem bank_nonzero (tail : List Bool) {j : Nat} (h : j ≠ 0) :
    (wireBank false tail).getD j false = (wireBank true tail).getD j false := by
  cases j with
  | zero => exact (h rfl).elim
  | succ j => rfl

theorem gate_equal (tail : List Bool) (g : Gate)
    (h : 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs) :
    g.op.eval (g.inputs.map fun j => (wireBank false tail).getD j false) =
      g.op.eval (g.inputs.map fun j => (wireBank true tail).getD j false) := by
  by_cases readsZero : 0 ∈ g.inputs
  · obtain ⟨hop, hthree⟩ := h readsZero
    have evalOr (b : Bool) :
        GateOp.or.eval (g.inputs.map fun j => (wireBank b tail).getD j false) = true := by
      exact List.any_eq_true.mpr ⟨true, List.mem_map.mpr ⟨3, hthree, rfl⟩, rfl⟩
    rw [hop, evalOr false, evalOr true]
  · congr 1
    apply List.map_congr_left
    intro j hj
    exact bank_nonzero tail (fun e => readsZero (e ▸ hj))

theorem fold_bank (gates : List Gate) (tail : List Bool)
    (h : ∀ g ∈ gates, 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs) :
    ∃ out, gates.foldl appendGate (wireBank false tail) = wireBank false out ∧
      gates.foldl appendGate (wireBank true tail) = wireBank true out := by
  induction gates generalizing tail with
  | nil => exact ⟨tail, rfl, rfl⟩
  | cons g gates ih =>
    let bit := g.op.eval (g.inputs.map fun j => (wireBank false tail).getD j false)
    have e := gate_equal tail g (h g (by simp))
    have hl : appendGate (wireBank false tail) g = wireBank false (tail ++ [bit]) := rfl
    have hr : appendGate (wireBank true tail) g = wireBank true (tail ++ [bit]) := by
      unfold appendGate
      rw [← e]
      rfl
    simp only [List.foldl_cons, hl, hr]
    exact ih _ (fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem fold_head (gates : List Gate) (b : Bool) (tail : List Bool) :
    (gates.foldl appendGate (b :: tail)).getD 0 false = b := by
  induction gates generalizing tail with
  | nil => rfl
  | cons g gates ih => exact ih _

end PEqualNP.Outside.L_meta_29804

open PEqualNP.Outside.L_meta_29804 in
theorem PEqualNP.Outside.L_meta_29804 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 2 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 3 ∈ (C.gates.get i).inputs ∧ 3 ≠ 0 ∧ 3 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 3 false = true)) := by
  rintro ⟨C, i, k, _, _, _, computes, _, onlyRead, isOr, _, _, _, hthree, _, _, _⟩
  have guarded : ∀ g ∈ C.gates, 0 ∈ g.inputs → g.op = .or ∧ 3 ∈ g.inputs := by
    intro g hg hzero
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
    rw [onlyRead j hzero]
    exact ⟨isOr, hthree⟩
  let low : Fin 7 → Bool := fun j => decide (j = 1 ∨ j = 3)
  let high : Fin 7 → Bool := fun j => decide (j = 0 ∨ j = 1 ∨ j = 3)
  have inputLow : List.ofFn low = wireBank false [false, false, false] := by decide
  have inputHigh : List.ofFn high = wireBank true [false, false, false] := by decide
  have evalLow : C.eval (List.ofFn low) = false := by simpa [low] using computes low
  have evalHigh : C.eval (List.ofFn high) = true := by simpa [high] using computes high
  have outputNonzero : C.output ≠ 0 := by
    intro hout
    let zeroOnly : Fin 7 → Bool := fun j => decide (j = 0)
    have inputZero : List.ofFn zeroOnly = [true, false, false, false, false, false, false] := by decide
    have h := computes zeroOnly
    have ez : C.eval (List.ofFn zeroOnly) = false := by simpa [zeroOnly] using h
    change (C.gates.foldl appendGate (List.ofFn zeroOnly)).getD C.output false = false at ez
    rw [inputZero, hout, fold_head] at ez
    contradiction
  obtain ⟨tail, hlow, hhigh⟩ := fold_bank C.gates [false, false, false] guarded
  have equality : C.eval (List.ofFn low) = C.eval (List.ofFn high) := by
    change (C.gates.foldl appendGate (List.ofFn low)).getD C.output false =
      (C.gates.foldl appendGate (List.ofFn high)).getD C.output false
    rw [inputLow, inputHigh, hlow, hhigh]
    exact bank_nonzero tail outputNonzero
  rw [evalLow, evalHigh] at equality
  contradiction
