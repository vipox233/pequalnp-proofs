import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18954_2
    (hPG23Char :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj],
        (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) =>
          ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) →
        (∀ (u v : Fin (26 : ℕ)), x1.Adj u v → (↑u < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑v) ∨ ((13 : ℕ) ≤ ↑u ∧ ↑v < (13 : ℕ))) ∧
        (∀ (u : Fin (26 : ℕ)), x1.degree u = (4 : ℕ)) ∧
        (∀ (u v w z : Fin (26 : ℕ)), x1.Adj u v → x1.Adj v w → x1.Adj w z → x1.Adj z u → u = w ∨ v = z))
    (hC4FreeMixedVC :
      ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        ((∀ (u v : Fin (26 : ℕ)), x1.Adj u v → (↑u < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑v) ∨ ((13 : ℕ) ≤ ↑u ∧ ↑v < (13 : ℕ))) ∧
         (∀ (u : Fin (26 : ℕ)), x1.degree u = (4 : ℕ)) ∧
         (∀ (u v w z : Fin (26 : ℕ)), x1.Adj u v → x1.Adj v w → x1.Adj w z → x1.Adj z u → u = w ∨ v = z)) →
        PEqualNP.TopForm.IsLeastAO x1 x3 →
        PEqualNP.TopForm.TopForm x1 x3 →
        x3.size ≤ (64 : ℕ) →
        PEqualNP.TopForm.junk x1 x3 ≠ ∅ →
        ∃ (x9 : Finset (Fin (26 : ℕ))),
          (∀ (x10 x11 : Fin (26 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧
          (∃ (x10 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x10 ∈ x9) ∧
          (∃ (x10 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x10 ∈ x9) ∧
          x9.card + (PEqualNP.TopForm.Ustar x1 x3).card ≤
            (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card +
            (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card +
            (PEqualNP.TopForm.junk x1 x3).card +
            (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) :
    (∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + (26 : ℕ) - ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → x3.size ≤ (64 : ℕ) → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → ∃ (x9 : Finset (Fin (26 : ℕ))), (∀ (x10 x11 : Fin (26 : ℕ)), x1.Adj x10 x11 → x10 ∈ x9 ∨ x11 ∈ x9) ∧ (∃ (x10 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x10 ∈ x9) ∧ (∃ (x10 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x10 ∈ x9) ∧ x9.card + (PEqualNP.TopForm.Ustar x1 x3).card ≤ (PEqualNP.TopForm.tops x1 x3 \ PEqualNP.TopForm.centreless x1 x3).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) := by
  intro x1 x2 x3 hG hLeast hTF hsz hJunk
  exact @hC4FreeMixedVC x1 x2 x3 (@hPG23Char x1 x2 hG) hLeast hTF hsz hJunk
