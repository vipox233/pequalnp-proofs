import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_461 : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
  (∃ C : Finset (Fin n), C.card ≤ k ∧ G.IsVertexCover (C : Set (Fin n))) ↔
  ∃ D : Finset (Fin n), D.card ≤ k ∧ ∀ x : Fin n,
    ¬ Relation.TransGen (fun a b : Fin n => a ∉ D ∧ b ∉ D ∧ G.Adj a b) x x := by
  intro n k G
  constructor
  · rintro ⟨C, hcard, hcov⟩
    refine ⟨C, hcard, fun x htx => ?_⟩
    cases htx with
    | single h =>
      rcases hcov h.2.2 with h1 | h2
      · exact h.1 (Finset.mem_coe.mp h1)
      · exact h.2.1 (Finset.mem_coe.mp h2)
    | tail _ h =>
      rcases hcov h.2.2 with h1 | h2
      · exact h.1 (Finset.mem_coe.mp h1)
      · exact h.2.1 (Finset.mem_coe.mp h2)
  · rintro ⟨D, hcard, hacyc⟩
    refine ⟨D, hcard, fun v w hadj => ?_⟩
    by_cases hv : v ∈ D
    · exact Or.inl (Finset.mem_coe.mpr hv)
    · by_cases hw : w ∈ D
      · exact Or.inr (Finset.mem_coe.mpr hw)
      · exfalso
        exact hacyc v (Relation.TransGen.tail (Relation.TransGen.single ⟨hv, hw, hadj⟩) ⟨hw, hv, hadj.symm⟩)
