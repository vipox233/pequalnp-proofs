import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_11094_3
    (hOneJunk :
      ∃ (K1 : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ),
        (∃ (u : Fin n) (v : Fin n), G.Adj u v) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        PEqualNP.TopForm.junk G C = {g} →
        G.edgeSet.ncard + G.edgeSet.ncard ≤ C.size + (1 : ℕ) + K1 * (n + (1 : ℕ)).sqrt)
    (hMultiJunk :
      ∃ (K2 : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        (∃ (u : Fin n) (v : Fin n), G.Adj u v) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        G.edgeSet.ncard + G.edgeSet.ncard ≤ C.size + (1 : ℕ) + K2 * (n + (1 : ℕ)).sqrt) :
    (∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∃ (x6 : Fin x2) (x7 : Fin x2), x3.Adj x6 x7) → PEqualNP.TopForm.IsLeastAO x3 x5 → PEqualNP.TopForm.TopForm x3 x5 → (PEqualNP.TopForm.junk x3 x5).Nonempty → x3.edgeSet.ncard + x3.edgeSet.ncard ≤ x5.size + (1 : ℕ) + x1 * (x2 + (1 : ℕ)).sqrt) :=
  Exists.elim hOneJunk fun K1 hK1 =>
    Exists.elim hMultiJunk fun K2 hK2 =>
      ⟨K1 + K2, fun n G inst C hedge hleast htop hjunk =>
        let s := (n + (1 : ℕ)).sqrt
        Or.elim (Nat.lt_or_ge (PEqualNP.TopForm.junk G C).card (2 : ℕ))
          (fun hlt =>
            let hc1 : (PEqualNP.TopForm.junk G C).card = (1 : ℕ) :=
              Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Finset.card_pos.mpr hjunk)
            Exists.elim (Finset.card_eq_one.mp hc1) fun g hg =>
              Nat.le_trans (hK1 n G C g hedge hleast htop hg)
                (Nat.add_le_add_left (Nat.mul_le_mul_right s (Nat.le_add_right K1 K2)) (C.size + (1 : ℕ))))
          (fun hge =>
            Nat.le_trans (hK2 n G C hedge hleast htop hge)
              (Nat.add_le_add_left (Nat.mul_le_mul_right s (Nat.le_add_left K2 K1)) (C.size + (1 : ℕ))))⟩
