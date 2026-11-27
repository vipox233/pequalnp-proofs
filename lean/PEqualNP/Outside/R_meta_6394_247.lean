import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6394_247
    (smallAnd : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.size ≤ (64 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → ∃ (x7 : Finset (Fin (26 : ℕ))), (∀ (x8 x9 : Fin (26 : ℕ)), x1.Adj x8 x9 → x8 ∈ x7 ∨ x9 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x8 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x8 ∈ x7) ∧ (52 : ℕ) + x7.card ≤ x3.size + (1 : ℕ))
    (smallOther : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.size ≤ (64 : ℕ) → ¬(PEqualNP.MetaComplexity.NestedCover.gateAt x3 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → ∃ (x7 : Finset (Fin (26 : ℕ))), (∀ (x8 x9 : Fin (26 : ℕ)), x1.Adj x8 x9 → x8 ∈ x7 ∨ x9 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x8 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x8 ∈ x7) ∧ (52 : ℕ) + x7.card ≤ x3.size + (1 : ℕ)) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → ∃ (x7 : Finset (Fin (26 : ℕ))), (∀ (x8 x9 : Fin (26 : ℕ)), x1.Adj x8 x9 → x8 ∈ x7 ∨ x9 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x8 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x8 ∈ x7) ∧ (52 : ℕ) + x7.card ≤ x3.size + (1 : ℕ) := by
  intro x1 x2 x3 hspec hleast hjunk
  by_cases hs : x3.size ≤ (64 : ℕ)
  · by_cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and
    · exact @smallAnd x1 x2 x3 hs h hspec hleast hjunk
    · exact @smallOther x1 x2 x3 hs h hspec hleast hjunk
  · let K : Finset (Fin (26 : ℕ)) :=
      Finset.image (Fin.castAdd (13 : ℕ)) (Finset.univ : Finset (Fin (13 : ℕ))) ∪
        {(Fin.natAdd (13 : ℕ) (0 : Fin (13 : ℕ)) : Fin (26 : ℕ))}
    have key : ∀ x : Fin (13 : ℕ), Fin.castAdd (13 : ℕ) x ∈ K := by decide
    refine ⟨K, ?_, ?_, ?_, ?_⟩
    · intro u v huv
      rcases (hspec u v).mp huv with ⟨p, l, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact Or.inl (key p)
      · exact Or.inr (key p)
    · exact ⟨0, key (0 : Fin (13 : ℕ))⟩
    · exact ⟨0, Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)⟩
    · have hcard : K.card = 14 := by decide
      omega
