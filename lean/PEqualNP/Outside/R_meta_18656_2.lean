import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18656_2
    (hReadersSub :
      ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin (11 : ℕ)),
        (PEqualNP.TopForm.readers (0 : ℕ) c ↑v).card ≤
        ((Finset.range c.size).filter fun (g : ℕ) =>
          ((PEqualNP.MetaComplexity.NestedCover.gateAt c g).inputs.any fun (w : ℕ) =>
            !PEqualNP.ReadTwo.wval c (fun (i : Fin (11 : ℕ)) => Decidable.decide (i ≠ v)) w) = Bool.true).card)
    (hWithReaderDeg2 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) :=
        PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
          (List.map (fun (k : ℕ) => (k / (11 : ℕ), k % (11 : ℕ)))
            [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ),
             (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]);
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        (PEqualNP.TopForm.IsLeastAO x1 x2 ∧
         PEqualNP.TopForm.TopForm x1 x2 ∧
         x2.size ≤ (21 : ℕ) ∧
         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card ∧
         (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card +
           (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card <
           (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card ∧
         (∀ (v : Fin (11 : ℕ)), ↑v < (4 : ℕ) → (PEqualNP.TopForm.readers (0 : ℕ) x2 ↑v).card ≤ (2 : ℕ)) ∧
         (∀ (v : Fin (11 : ℕ)), ↑v < (4 : ℕ) →
           ((Finset.range x2.size).filter fun (g : ℕ) =>
             ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 g).inputs.any fun (w : ℕ) =>
               !PEqualNP.ReadTwo.wval x2 (fun (i : Fin (11 : ℕ)) => Decidable.decide (i ≠ v)) w) = Bool.true).card ≤ (2 : ℕ))) →
        ∃ (x9 : Fin (11 : ℕ)),
          ↑x9 < (4 : ℕ) ∧
          let x10 : ℕ → Prop := fun (g : ℕ) =>
            ∃ w < (11 : ℕ) + g, ∀ (f : Fin (11 : ℕ) → Bool), f x9 = Bool.false →
              PEqualNP.ReadTwo.wval x2 f ((11 : ℕ) + g) = PEqualNP.ReadTwo.wval x2 f w;
          ∃ (g1 g2 g3 : ℕ), g1 < g2 ∧ g2 < g3 ∧ g3 < x2.size ∧ x10 g1 ∧ x10 g2 ∧ x10 g3) :
    (let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x1 : ℕ) => (x1 / (11 : ℕ), x1 % (11 : ℕ))) [(9 : ℕ), (10 : ℕ), (15 : ℕ), (19 : ℕ), (27 : ℕ), (32 : ℕ), (39 : ℕ), (40 : ℕ), (52 : ℕ), (54 : ℕ), (63 : ℕ), (64 : ℕ), (73 : ℕ), (76 : ℕ), (86 : ℕ), (97 : ℕ)]); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       x2.size ≤ (21 : ℕ) →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) → {x10 ∈ Finset.range x2.size | ((PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs.any fun (x11 : ℕ) => !PEqualNP.ReadTwo.wval x2 (fun (x12 : Fin (11 : ℕ)) => Decidable.decide (x12 ≠ x8)) x11) = Bool.true}.card ≤ (2 : ℕ)) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) :=
  fun x2 hL hTF hSz hJ2 hCount hDead =>
    hWithReaderDeg2 x2
      ⟨hL, hTF, hSz, hJ2, hCount,
       fun v hv => Nat.le_trans (hReadersSub x2 v) (hDead v hv),
       hDead⟩
