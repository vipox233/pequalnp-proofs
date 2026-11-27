import PEqualNP.Defs

-- A case split on the first gate of the circuit (gateAt reads the default OR gate past the end):
-- either gate 0 is an AND gate, or it is not (for a monotone circuit, an OR gate). Each piece is
-- the step with that one extra hypothesis.
theorem PEqualNP.Outside.R_meta_17848_64
    (firstAnd : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.MetaComplexity.Monotone2 x1 → have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3)); (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (64 : ℕ) ≤ x1.size)
    (firstOther : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op ≠ PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.MetaComplexity.Monotone2 x1 → have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3)); (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (64 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3)); (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (64 : ℕ) ≤ x1.size := by
  intro x1
  by_cases h : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and
  · exact firstAnd x1 h
  · exact firstOther x1 h
