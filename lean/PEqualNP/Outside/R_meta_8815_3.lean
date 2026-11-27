import PEqualNP.Defs
theorem PEqualNP.Outside.R_meta_8815_3
    (matching_split : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)),
      (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →
      x2.card = (Finset.univ.image (fun v : Fin x1 => (v, x3 v))).card +
        (x2 \ Finset.univ.image (fun v : Fin x1 => (v, x3 v))).card)
    (matching_card : ∀ (x1 : ℕ) (x3 : Equiv.Perm (Fin x1)),
      (Finset.univ.image (fun v : Fin x1 => (v, x3 v))).card = x1)
    (excess_bound : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (0 : ℕ) < x1 →
      (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →
      (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →
      PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
      (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →
      (x2 \ Finset.univ.image (fun v : Fin x1 => (v, x3 v))).card ≤
        (x4.output :: List.flatMap (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs) x4.gates).length -
          (x4.output :: List.flatMap (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs) x4.gates).toFinset.card) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (0 : ℕ) < x1 →     (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →       (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →         PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →           (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →             have x10 : List ℕ := x4.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x4.gates;             x2.card ≤ x1 + (x10.length - x10.toFinset.card) := by
  intro x1 x2 x3 x4 hpos hnc hperm hcirc hfun
  have hsplit := matching_split x1 x2 x3 hperm
  have hcard := matching_card x1 x3
  have hexc := excess_bound x1 x2 x3 x4 hpos hnc hperm hcirc hfun
  change x2.card ≤ x1 + ((x4.output :: List.flatMap (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs) x4.gates).length -
    (x4.output :: List.flatMap (fun (g : PEqualNP.CircuitLowerBounds.Gate) => g.inputs) x4.gates).toFinset.card)
  rw [hsplit, hcard]
  exact Nat.add_le_add_left hexc x1
