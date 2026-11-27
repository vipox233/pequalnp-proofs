import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18950_2
    (hWireBounds :
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → ℕ → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : ℕ) => (x3.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x4) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5))).getD x6 Bool.false;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),
        (∃ (a b : Finset (Fin (13 : ℕ))), x3 x4 a b x5 = Bool.true ∧ x3 x4 a b x6 = Bool.false) →
        (∃ (a b : Finset (Fin (13 : ℕ))), x3 x4 a b x6 = Bool.true ∧ x3 x4 a b x5 = Bool.false) →
        x5 < (26 : ℕ) + x4.size ∧ x6 < (26 : ℕ) + x4.size ∧ x5 ≠ x6)
    (hOrderedLB :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      have x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => Maximal (fun (x3 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => ∀ x4 ∈ x3.1, ∀ x6 ∈ x3.2, ¬x1 x4 x6) x2;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → ℕ → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : ℕ) => (x3.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x4) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5))).getD x6 Bool.false;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ),
        (PEqualNP.MetaComplexity.Monotone2 x4 ∧
          (26 : ℕ) ≤ x5 ∧ x5 < x6 ∧ x6 < (26 : ℕ) + x4.size ∧
          (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x3 x4 {x10} {x11} x5 = Bool.true ∧ x3 x4 {x10} {x11} x6 = Bool.true) ∧
          (∀ (x11 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x11 → x3 x4 x11.1 x11.2 x5 = Bool.false ∨ x3 x4 x11.1 x11.2 x6 = Bool.false) ∧
          (∃ (x12 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x12 ∧ x3 x4 x12.1 x12.2 x5 = Bool.true ∧ x3 x4 x12.1 x12.2 x6 = Bool.false) ∧
          (∃ (x13 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x13 ∧ x3 x4 x13.1 x13.2 x6 = Bool.true ∧ x3 x4 x13.1 x13.2 x5 = Bool.false)) →
        (63 : ℕ) ≤ x4.size) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => Maximal (fun (x3 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => ∀ x4 ∈ x3.1, ∀ x6 ∈ x3.2, ¬x1 x4 x6) x2; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → ℕ → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : ℕ) => (x3.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x4) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5))).getD x6 Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → (26 : ℕ) ≤ x5 → (26 : ℕ) ≤ x6 → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → x3 x4 {x10} {x11} x5 = Bool.true ∧ x3 x4 {x10} {x11} x6 = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x11 → x3 x4 x11.1 x11.2 x5 = Bool.false ∨ x3 x4 x11.1 x11.2 x6 = Bool.false) → (∃ (x12 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x12 ∧ x3 x4 x12.1 x12.2 x5 = Bool.true ∧ x3 x4 x12.1 x12.2 x6 = Bool.false) → (∃ (x13 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x13 ∧ x3 x4 x13.1 x13.2 x6 = Bool.true ∧ x3 x4 x13.1 x13.2 x5 = Bool.false) → (63 : ℕ) ≤ x4.size) :=
  fun x4 x5 x6 hM h5 h6 hPos hNeg hS1 hS2 =>
    have hb := hWireBounds x4 x5 x6
      (Exists.elim hS1 fun p hp => ⟨p.1, p.2, hp.2⟩)
      (Exists.elim hS2 fun p hp => ⟨p.1, p.2, hp.2⟩)
    Or.elim (Nat.lt_or_gt_of_ne hb.2.2)
      (fun hlt => hOrderedLB x4 x5 x6 ⟨hM, h5, hlt, hb.2.1, hPos, hNeg, hS1, hS2⟩)
      (fun hgt => hOrderedLB x4 x6 x5 ⟨hM, h6, hgt, hb.1,
        fun a b hab => (hPos a b hab).symm,
        fun p hp => (hNeg p hp).symm, hS2, hS1⟩)
