import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

/-- Cut for `L-meta-6569`: the circuit has a second gate, or it does not. -/
theorem PEqualNP.Outside.R_meta_6569_1 :
    (∀ (x1 : ℕ) (x2 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → (∀ (x5 x6 : Fin (x1 + (1 : ℕ))), x5 ≠ x6 → Function.Bijective fun (x8 : Fin (x1 * x1)) => (x2 x5 x8, x2 x6 x8)) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x1 * x1)) (x8 : Fin (x1 + (1 : ℕ))), x3.eval (PEqualNP.GenericRejection.incidenceInput {x7} {finProdFinEquiv (x8, x2 x8 x7)}) = Bool.true) → (∀ (x8 : Finset (Fin (x1 * x1))) (x9 : Finset (Fin (x1 + (1 : ℕ)) × Fin x1)), x9.card ≤ x1 → (∀ x11 ∈ x8, ∀ (x13 : Fin (x1 + (1 : ℕ))), (x13, x2 x13 x11) ∉ x9) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 (Finset.map finProdFinEquiv.toEmbedding x9)) = Bool.false) → (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x3.gates[1]? = Option.some g) → x1 ^ (2 : ℕ) * (x1 + (1 : ℕ)) ≤ (99 : ℕ) * x3.size) →
    (∀ (x1 : ℕ) (x2 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → (∀ (x5 x6 : Fin (x1 + (1 : ℕ))), x5 ≠ x6 → Function.Bijective fun (x8 : Fin (x1 * x1)) => (x2 x5 x8, x2 x6 x8)) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x1 * x1)) (x8 : Fin (x1 + (1 : ℕ))), x3.eval (PEqualNP.GenericRejection.incidenceInput {x7} {finProdFinEquiv (x8, x2 x8 x7)}) = Bool.true) → (∀ (x8 : Finset (Fin (x1 * x1))) (x9 : Finset (Fin (x1 + (1 : ℕ)) × Fin x1)), x9.card ≤ x1 → (∀ x11 ∈ x8, ∀ (x13 : Fin (x1 + (1 : ℕ))), (x13, x2 x13 x11) ∉ x9) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 (Finset.map finProdFinEquiv.toEmbedding x9)) = Bool.false) → ¬(∃ (g : PEqualNP.CircuitLowerBounds.Gate), x3.gates[1]? = Option.some g) → x1 ^ (2 : ℕ) * (x1 + (1 : ℕ)) ≤ (99 : ℕ) * x3.size) →
    (∀ (x1 : ℕ) (x2 : Fin (x1 + (1 : ℕ)) → Fin (x1 * x1) → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → (∀ (x5 x6 : Fin (x1 + (1 : ℕ))), x5 ≠ x6 → Function.Bijective fun (x8 : Fin (x1 * x1)) => (x2 x5 x8, x2 x6 x8)) → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x7 : Fin (x1 * x1)) (x8 : Fin (x1 + (1 : ℕ))), x3.eval (PEqualNP.GenericRejection.incidenceInput {x7} {finProdFinEquiv (x8, x2 x8 x7)}) = Bool.true) → (∀ (x8 : Finset (Fin (x1 * x1))) (x9 : Finset (Fin (x1 + (1 : ℕ)) × Fin x1)), x9.card ≤ x1 → (∀ x11 ∈ x8, ∀ (x13 : Fin (x1 + (1 : ℕ))), (x13, x2 x13 x11) ∉ x9) → x3.eval (PEqualNP.GenericRejection.incidenceInput x8 (Finset.map finProdFinEquiv.toEmbedding x9)) = Bool.false) → x1 ^ (2 : ℕ) * (x1 + (1 : ℕ)) ≤ (99 : ℕ) * x3.size) := by
  classical
  intro h1 h2 x1 x2 x3
  intros
  by_cases h : (∃ (g : PEqualNP.CircuitLowerBounds.Gate), x3.gates[1]? = Option.some g)
  · apply h1 <;> assumption
  · apply h2 <;> assumption
