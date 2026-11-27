import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18948_2
    (hEvalPG23 :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      have x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) =>
        Maximal (fun (x3 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => ∀ x4 ∈ x3.1, ∀ x6 ∈ x3.2, ¬x1 x4 x6) x2;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → ℕ → Bool :=
        fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : ℕ) =>
          (x3.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) =>
            if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x4)
            else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5))).getD x6 Bool.false;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x4 →
        (26 : ℕ) ≤ x5 →
        (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → x3 x4 {x8} {x9} x5 = Bool.true) →
        (∀ (x9 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x9 → x3 x4 x9.1 x9.2 x5 = Bool.false) →
        x5 < (26 : ℕ) + x4.size ∧
        ∀ (f : Fin (26 : ℕ) → Bool),
          (x4.wires (List.ofFn f)).getD x5 Bool.false = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)), x1 p l ∧ f (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ f (Fin.natAdd (13 : ℕ) l) = Bool.true)
    (hPG23CircuitLB :
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x4 →
        (26 : ℕ) ≤ x5 →
        x5 < (26 : ℕ) + x4.size →
        (∀ (f : Fin (26 : ℕ) → Bool),
          (x4.wires (List.ofFn f)).getD x5 Bool.false = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)),
              (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              f (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
              f (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (63 : ℕ) ≤ x4.size) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => Maximal (fun (x3 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => ∀ x4 ∈ x3.1, ∀ x6 ∈ x3.2, ¬x1 x4 x6) x2; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → ℕ → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Finset (Fin (13 : ℕ))) (x6 : ℕ) => (x3.wires (List.ofFn fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x4) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5))).getD x6 Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ), PEqualNP.MetaComplexity.Monotone2 x4 → (26 : ℕ) ≤ x5 → (∀ (x8 x9 : Fin (13 : ℕ)), x1 x8 x9 → x3 x4 {x8} {x9} x5 = Bool.true) → (∀ (x9 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))), x2 x9 → x3 x4 x9.1 x9.2 x5 = Bool.false) → (63 : ℕ) ≤ x4.size) := by
  intro x1 x2 x3 x4 x5 hM h5 hPos hNeg
  exact
    let h := hEvalPG23 x4 x5 hM h5 hPos hNeg
    hPG23CircuitLB x4 x5 hM h5 h.1 h.2
