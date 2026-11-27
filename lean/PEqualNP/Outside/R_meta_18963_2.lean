import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18963_2
    (hMatchingPigeonhole :
      ∀ (U : Finset (Sym2 (Fin (26 : ℕ)))),
        have M : Fin (13 : ℕ) → Finset (Sym2 (Fin (26 : ℕ))) := fun (d : Fin (13 : ℕ)) =>
          Finset.image (fun (p : Fin (13 : ℕ)) => s(Fin.castAdd (13 : ℕ) p, Fin.natAdd (13 : ℕ) (d - p))) Finset.univ;
        (U ∩ M (0 : Fin (13 : ℕ))).card + (U ∩ M (1 : Fin (13 : ℕ))).card +
        (U ∩ M (3 : Fin (13 : ℕ))).card + (U ∩ M (9 : Fin (13 : ℕ))).card ≤ U.card)
    (hWithMatchingBound :
      let x1 : SimpleGraph (Fin (26 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) =>
        ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsLeastAO x1 x2 →
        PEqualNP.TopForm.TopForm x1 x2 →
        x2.size ≤ (63 : ℕ) →
        have x6 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;
        have x7 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;
        have x8 : ℕ := (PEqualNP.TopForm.junk x1 x2).card;
        have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x8 + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;
        have x11 : Fin (13 : ℕ) → ℕ := fun (x11 : Fin (13 : ℕ)) =>
          (x6 ∩ Finset.image (fun (x12 : Fin (13 : ℕ)) => s(Fin.castAdd (13 : ℕ) x12, Fin.natAdd (13 : ℕ) (x11 - x12))) Finset.univ).card;
        ((2 : ℕ) ≤ x8 ∧ (4 : ℕ) ≤ x9 ∧ (4 : ℕ) ≤ x6.card ∧
         (4 : ℕ) * x9 + (4 : ℕ) ≤ (5 : ℕ) * x6.card ∧
         x9 < x6.card + x11 (0 : Fin (13 : ℕ)) ∧
         x9 < x6.card + x11 (1 : Fin (13 : ℕ)) ∧
         x9 < x6.card + x11 (3 : Fin (13 : ℕ)) ∧
         x9 < x6.card + x11 (9 : Fin (13 : ℕ))) →
        (13 : ℕ) + x6.card ≤ x7 + x9) :
    (let x1 : SimpleGraph (Fin (26 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) => ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       x2.size ≤ (63 : ℕ) →         have x6 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;         have x7 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;         have x8 : ℕ := (PEqualNP.TopForm.junk x1 x2).card;         have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + x8 + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;         have x10 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x11 : Fin (13 : ℕ) → ℕ := fun (x11 : Fin (13 : ℕ)) => (x6 ∩ Finset.image (fun (x12 : Fin (13 : ℕ)) => s(Fin.castAdd (13 : ℕ) x12, Fin.natAdd (13 : ℕ) (x11 - x12))) Finset.univ).card;         (2 : ℕ) ≤ x8 → (4 : ℕ) ≤ x9 → (4 : ℕ) ≤ x6.card → (∀ x15 ∈ x10, x9 < x6.card + x11 x15) → (13 : ℕ) + x6.card ≤ x7 + x9) := by
  intro x1 x2 hL hTF hsz x6 x7 x8 x9 x10 x11 h8 h9 h6 h15
  have h0 : x9 < x6.card + x11 (0 : Fin (13 : ℕ)) :=
    h15 (0 : Fin (13 : ℕ)) (Finset.mem_insert_self _ _)
  have h1 : x9 < x6.card + x11 (1 : Fin (13 : ℕ)) :=
    h15 (1 : Fin (13 : ℕ)) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h3 : x9 < x6.card + x11 (3 : Fin (13 : ℕ)) :=
    h15 (3 : Fin (13 : ℕ)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have h9' : x9 < x6.card + x11 (9 : Fin (13 : ℕ)) :=
    h15 (9 : Fin (13 : ℕ)) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
  have hSum : x11 (0 : Fin (13 : ℕ)) + x11 (1 : Fin (13 : ℕ)) + x11 (3 : Fin (13 : ℕ)) + x11 (9 : Fin (13 : ℕ)) ≤ x6.card :=
    hMatchingPigeonhole x6
  have hRatio : (4 : ℕ) * x9 + (4 : ℕ) ≤ (5 : ℕ) * x6.card := by omega
  exact hWithMatchingBound x2 hL hTF hsz ⟨h8, h9, h6, hRatio, h0, h1, h3, h9'⟩
