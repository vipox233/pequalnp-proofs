import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8925_2
    (hNonIncFalse :
      have s : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 →
        (∀ q ∈ PEqualNP.HeptadCover.quadrangles s,
          PEqualNP.LowMerge.wireVal x3
            ((List.ofFn fun i : Fin (13 : ℕ) => Decidable.decide (i ∈ q)) ++
             List.ofFn fun i : Fin (13 : ℕ) => Decidable.decide (i ∈ PEqualNP.HeptadCover.missLines s q))
            ((26 : ℕ) + g) = Bool.false) →
        ∀ (p l : Fin (13 : ℕ)), p ∉ s l →
          PEqualNP.LowMerge.wireVal x3 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) p l) ((26 : ℕ) + g) = Bool.false)
    (hWithNonIncFalse :
      let S : Type := Finset (Fin (13 : ℕ));
      have s : Fin (13 : ℕ) → S := PEqualNP.HeptadCover.singerLines3;
      have x1 : S → List Bool := fun q =>
        (List.ofFn fun i : Fin (13 : ℕ) => Decidable.decide (i ∈ q)) ++
        List.ofFn fun i : Fin (13 : ℕ) => Decidable.decide (i ∈ PEqualNP.HeptadCover.missLines s q);
      have x2 : Finset S := PEqualNP.HeptadCover.quadrangles s;
      ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),
        have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;
        have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;
        (PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (38 : ℕ) ≤ x3.size ∧ x3.size < (64 : ℕ) ∧
         (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 ∧
         (∀ g ∈ x3.gates, g.inputs.getD (0 : ℕ) (0 : ℕ) ≠ g.inputs.getD (1 : ℕ) (0 : ℕ)) ∧
         (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧
         (∀ i < x3.size, (x5 i).op = PEqualNP.CircuitLowerBounds.GateOp.and →
           ∀ w ∈ (x5 i).inputs, ∃ q ∈ x2, x6 (x1 q) ((26 : ℕ) + i) ≠ x6 (x1 q) w) ∧
         (∀ g ∈ x4, g < x3.size ∧ (x5 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
           (∀ q ∈ x2, x6 (x1 q) ((26 : ℕ) + g) = Bool.false) ∧
           (∀ p l : Fin (13 : ℕ), p ∉ s l → x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) p l) ((26 : ℕ) + g) = Bool.false)) ∧
         (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) ∧
         (∀ y : List Bool, y.length = (26 : ℕ) →
           (x3.eval y = Bool.true ↔ ∃ g ∈ x4, x6 y ((26 : ℕ) + g) = Bool.true))) →
        ∃ x17 : Finset (S × S),
          have cov : Finset (Fin (13 : ℕ) × Fin (13 : ℕ)) := x17.biUnion fun b => b.1 ×ˢ b.2;
          cov ⊆ PEqualNP.HeptadCover.incidences s ∧
          (∀ p l : Fin (13 : ℕ), p ∈ s l →
            (∃ g ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) p l) ((26 : ℕ) + g) = Bool.true) → (p, l) ∈ cov) ∧
          ∑ b ∈ x17, (b.1.card + b.2.card) ≤ x3.size + (1 : ℕ)) :
    (have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : Finset (Finset (Fin (13 : ℕ))) := PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Finset ℕ),   have x5 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x3;   have x6 : List Bool → ℕ → Bool := PEqualNP.LowMerge.wireVal x3;   PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → (38 : ℕ) ≤ x3.size → x3.size < (64 : ℕ) → (8 : ℕ) ≤ PEqualNP.ReadTwo.nAnd x3 ∧ (18 : ℕ) ≤ PEqualNP.ReadTwo.nOr x3 → (∀ x11 ∈ x3.gates, x11.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x11.inputs.getD (1 : ℕ) (0 : ℕ)) → (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x3 → (∀ x13 < x3.size, (x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ x16 ∈ (x5 x13).inputs, ∃ x18 ∈ x2, x6 (x1 x18) ((26 : ℕ) + x13) ≠ x6 (x1 x18) x16) → (∀ x14 ∈ x4, x14 < x3.size ∧ (x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ x16 ∈ x2, x6 (x1 x16) ((26 : ℕ) + x14) = Bool.false) → (2 : ℕ) * x4.card ≤ x3.size + (1 : ℕ) → (∀ (x16 : List Bool), x16.length = (26 : ℕ) → (x3.eval x16 = Bool.true ↔ ∃ x18 ∈ x4, x6 x16 ((26 : ℕ) + x18) = Bool.true)) → ∃ (x17 : Finset (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)))), (x17.biUnion fun (x18 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => x18.1 ×ˢ x18.2) ⊆ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 ∧ (∀ (x18 x19 : Fin (13 : ℕ)), x18 ∈ PEqualNP.HeptadCover.singerLines3 x19 → (∃ x21 ∈ x4, x6 (PEqualNP.LowMerge.pointLineInput (13 : ℕ) (13 : ℕ) x18 x19) ((26 : ℕ) + x21) = Bool.true) → (x18, x19) ∈ x17.biUnion fun (x22 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => x22.1 ×ˢ x22.2) ∧ ∑ x18 ∈ x17, (x18.1.card + x18.2.card) ≤ x3.size + (1 : ℕ)) :=
  fun x3 x4 hAO hGe38 hLt64 hAndOr hNoSelf hAP hStrict hX4 hCard hEval =>
    hWithNonIncFalse x3 x4
      ⟨hAO, hGe38, hLt64, hAndOr.1, hAndOr.2, hNoSelf, hAP, hStrict,
       fun g hg =>
         ⟨(hX4 g hg).1, (hX4 g hg).2.1, (hX4 g hg).2.2,
          hNonIncFalse x3 g hAO (hX4 g hg).2.2⟩,
       hCard, hEval⟩
