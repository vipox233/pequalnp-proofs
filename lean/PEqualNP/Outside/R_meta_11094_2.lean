import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_11094_2
    (hStarBound :
      ∃ (K1 : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ (u : Fin n) (v : Fin n), G.Adj u v) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).Nonempty →
        (G.edgeFinset ∩ PEqualNP.TopForm.starEdges G C).card +
          (G.edgeFinset ∩ PEqualNP.TopForm.starEdges G C).card ≤
          C.size + (1 : ℕ) + K1 * (n + (1 : ℕ)).sqrt)
    (hUstarBound :
      ∃ (K2 : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ (u : Fin n) (v : Fin n), G.Adj u v) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (PEqualNP.TopForm.junk G C).Nonempty →
        (PEqualNP.TopForm.Ustar G C).card ≤ K2 * (n + (1 : ℕ)).sqrt) :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x6 : Fin x2) (x7 : Fin x2), x3.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → x3.edgeSet.ncard + x3.edgeSet.ncard ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt) := by
  exact Exists.elim hStarBound fun K1 hK1 =>
    Exists.elim hUstarBound fun K2 hK2 =>
      ⟨K1 + (K2 + K2), fun n G inst C hedge hleast htop hjunk =>
        let hs := hK1 n G C hedge hleast htop hjunk
        let hu := hK2 n G C hedge hleast htop hjunk
        let hncard : G.edgeSet.ncard = G.edgeFinset.card :=
          Eq.trans (congrArg Set.ncard (SimpleGraph.coe_edgeFinset G).symm)
            (Set.ncard_coe_finset G.edgeFinset)
        let hpart : (G.edgeFinset ∩ PEqualNP.TopForm.starEdges G C).card +
            (PEqualNP.TopForm.Ustar G C).card = G.edgeFinset.card :=
          Finset.card_inter_add_card_sdiff G.edgeFinset (PEqualNP.TopForm.starEdges G C)
        let a := (G.edgeFinset ∩ PEqualNP.TopForm.starEdges G C).card
        let b := (PEqualNP.TopForm.Ustar G C).card
        let s := (n + (1 : ℕ)).sqrt
        have hstep1 : G.edgeSet.ncard + G.edgeSet.ncard = (a + a) + (b + b) :=
          Eq.trans (congrArg₂ HAdd.hAdd hncard hncard)
            (Eq.trans (congrArg₂ HAdd.hAdd hpart.symm hpart.symm)
              (Eq.trans (Nat.add_assoc a b (a + b))
                (Eq.trans (congrArg (a + ·)
                  (Eq.trans (Nat.add_assoc b a b).symm
                    (Eq.trans (congrArg (· + b) (Nat.add_comm b a))
                      (Nat.add_assoc a b b))))
                  (Nat.add_assoc a a (b + b)).symm)))
        have hstep2 : (a + a) + (b + b) ≤ (C.size + (1 : ℕ) + K1 * s) + (K2 * s + K2 * s) :=
          Nat.add_le_add hs (Nat.add_le_add hu hu)
        have hstep3 : (C.size + (1 : ℕ) + K1 * s) + (K2 * s + K2 * s) =
            C.size + (1 : ℕ) + (K1 + (K2 + K2)) * s :=
          Eq.trans (Nat.add_assoc (C.size + (1 : ℕ)) (K1 * s) (K2 * s + K2 * s))
            (congrArg ((C.size + (1 : ℕ)) + ·)
              (Eq.trans (congrArg (K1 * s + ·) (Nat.add_mul K2 K2 s).symm)
                (Nat.add_mul K1 (K2 + K2) s).symm))
        hstep1 ▸ hstep3 ▸ hstep2⟩
