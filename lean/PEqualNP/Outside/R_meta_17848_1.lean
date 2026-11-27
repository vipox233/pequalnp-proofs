import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-17848`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_17848_1 :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3));     (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (64 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3));     (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g) → (64 : ℕ) ≤ x1.size) →
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x1 →     have x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => x1.eval (List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide (finSumFinEquiv.symm x4 ∉ x3));     (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3, x3 (PEqualNP.HeptadCover.supp PEqualNP.HeptadCover.singerLines3 x4) = Bool.true) → (∀ x5 ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3, x3 {Sum.inl x5.1, Sum.inr x5.2} = Bool.false) → (64 : ℕ) ≤ x1.size) := by
  classical
  intro h1 h2 x1
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x1.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
