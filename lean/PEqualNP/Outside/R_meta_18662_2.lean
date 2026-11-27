import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18662_2
    (hX14One : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)),
      have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4;
      x4 x3 →
        (∀ (x6 : Finset (Fin x1)), x4 x6 → x3.card ≤ x6.card) →
          (∀ x7 ∈ x3, ∃ x9 ∉ x3, x2.Adj x7 x9) →
            (∃ x8 ∈ x3, ∃ x9 ∈ x3, x2.Adj x8 x9) →
              (∀ (x9 : Fin x1), (∃ (x10 : Fin x1), x2.Adj x9 x10) → (x2.neighborSet x9).ncard = (3 : ℕ)) →
                (∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) →
                  ∀ (x11 : (Fin x1 → Bool) → Bool),
                    (∀ (x12 : Fin x1 → Bool), x11 x12 = Bool.true ↔ ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →
                      ∀ (x13 : ℕ),
                        x13 + (1 : ℕ) + (1 : ℕ) = x2.edgeSet.ncard + x3.card →
                          PEqualNP.MetaComplexity.HasCircuitSize x1 x11 x13 →
                            ∃ x18 ∈ x3, ∃ x19 ∈ x3, x2.Adj x18 x19 ∧
                              ∃ (x20 : ℕ),
                                x20 + (1 : ℕ) + (1 : ℕ) ≤ (x2.edgeSet \ (x2.incidenceSet x18 ∪ x2.incidenceSet x19)).ncard + ((x3.erase x18).erase x19).card ∧
                                  PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x11 (Function.update (Function.update x21 x18 Bool.false) x19 Bool.false)) x20)
    (hX14Ge2 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)),
      have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4;
      x4 x3 →
        (∀ (x6 : Finset (Fin x1)), x4 x6 → x3.card ≤ x6.card) →
          (∀ x7 ∈ x3, ∃ x9 ∉ x3, x2.Adj x7 x9) →
            (∃ x8 ∈ x3, ∃ x9 ∈ x3, x2.Adj x8 x9) →
              (∀ (x9 : Fin x1), (∃ (x10 : Fin x1), x2.Adj x9 x10) → (x2.neighborSet x9).ncard = (3 : ℕ)) →
                (∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) →
                  ∀ (x11 : (Fin x1 → Bool) → Bool),
                    (∀ (x12 : Fin x1 → Bool), x11 x12 = Bool.true ↔ ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →
                      ∀ (x13 x14 : ℕ),
                        (2 : ℕ) ≤ x14 →
                          x13 + (1 : ℕ) + x14 = x2.edgeSet.ncard + x3.card →
                            PEqualNP.MetaComplexity.HasCircuitSize x1 x11 x13 →
                              ∃ x18 ∈ x3, ∃ x19 ∈ x3, x2.Adj x18 x19 ∧
                                ∃ (x20 : ℕ),
                                  x20 + (1 : ℕ) + x14 ≤ (x2.edgeSet \ (x2.incidenceSet x18 ∪ x2.incidenceSet x19)).ncard + ((x3.erase x18).erase x19).card ∧
                                    PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x11 (Function.update (Function.update x21 x18 Bool.false) x19 Bool.false)) x20) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)),   have x4 : Finset (Fin x1) → Prop := fun (x4 : Finset (Fin x1)) => ∀ (x5 x6 : Fin x1), x2.Adj x5 x6 → x5 ∈ x4 ∨ x6 ∈ x4;   x4 x3 → (∀ (x6 : Finset (Fin x1)), x4 x6 → x3.card ≤ x6.card) → (∀ x7 ∈ x3, ∃ x9 ∉ x3, x2.Adj x7 x9) → (∃ x8 ∈ x3, ∃ x9 ∈ x3, x2.Adj x8 x9) → (∀ (x9 : Fin x1), (∃ (x10 : Fin x1), x2.Adj x9 x10) → (x2.neighborSet x9).ncard = (3 : ℕ)) → (∀ (x10 : Fin x1) (x11 : x2.Walk x10 x10), x11.IsCycle → (7 : ℕ) ≤ x11.length) → ∀ (x11 : (Fin x1 → Bool) → Bool), (∀ (x12 : Fin x1 → Bool), x11 x12 = Bool.true ↔ ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) → ∀ (x13 x14 : ℕ), (0 : ℕ) < x14 → x13 + (1 : ℕ) + x14 = x2.edgeSet.ncard + x3.card → PEqualNP.MetaComplexity.HasCircuitSize x1 x11 x13 → ∃ x18 ∈ x3, ∃ x19 ∈ x3, x2.Adj x18 x19 ∧ ∃ (x20 : ℕ), x20 + (1 : ℕ) + x14 ≤ (x2.edgeSet \ (x2.incidenceSet x18 ∪ x2.incidenceSet x19)).ncard + ((x3.erase x18).erase x19).card ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x11 (Function.update (Function.update x21 x18 Bool.false) x19 Bool.false)) x20) :=
  fun x1 x2 x3 hcov hmin hnoiso hedge hdeg hgirth x11 hspec x13 x14 hpos hsum hcs =>
    Or.elim (Nat.eq_or_lt_of_le hpos)
      (fun heq => by subst heq; exact hX14One x1 x2 x3 hcov hmin hnoiso hedge hdeg hgirth x11 hspec x13 hsum hcs)
      (fun hge => hX14Ge2 x1 x2 x3 hcov hmin hnoiso hedge hdeg hgirth x11 hspec x13 x14 hge hsum hcs)
