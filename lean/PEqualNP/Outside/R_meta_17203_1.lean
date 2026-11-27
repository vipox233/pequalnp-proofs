import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17203_1
    (hMinVC :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)),
        ¬x2.Colorable (2 : ℕ) →
        ∃ (C : Finset (Fin x1)),
          (∀ (u v : Fin x1), x2.Adj u v → u ∈ C ∨ v ∈ C) ∧
          (∀ (C' : Finset (Fin x1)), (∀ (u v : Fin x1), x2.Adj u v → u ∈ C' ∨ v ∈ C') → C.card ≤ C'.card) ∧
          (∀ w ∈ C, ∃ z ∉ C, x2.Adj w z) ∧
          (∃ u ∈ C, ∃ v ∈ C, x2.Adj u v))
    (hElim :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (C : Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (u v : Fin x1), x2.Adj u v → u ∈ C ∨ v ∈ C) →
        (∀ w ∈ C, ∃ z ∉ C, x2.Adj w z) →
        (∃ u ∈ C, ∃ v ∈ C, x2.Adj u v) →
        (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) →
        (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x3 →
        (∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x3 x9 = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) →
        x3.size + (1 : ℕ) < x2.edgeSet.ncard + C.card →
        ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧
          ∃ (x12 : Finset ℕ), (7 : ℕ) ≤ x12.card ∧
            have x13 : ℕ → (Fin x1 → Bool) → Bool := fun (x13 : ℕ) (x14 : Fin x1 → Bool) => PEqualNP.LowMerge.wireVal x3 (List.ofFn (Function.update (Function.update x14 x10 Bool.false) x11 Bool.false)) x13;
            ∀ x14 ∈ x12, x14 < x3.size ∧ ((∀ (x16 : Fin x1 → Bool), x13 (x1 + x14) x16 = Bool.false) ∨ ∃ x16 < x1 + x14, x13 (x1 + x14) = x13 x16)) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∃ (x7 : Fin x1) (x8 : Fin x1), x2.Adj x7 x8) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x3 → (∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x3 x9 = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → (∃ (x10 : Finset (Fin x1)), (∀ (x11 x12 : Fin x1), x2.Adj x11 x12 → x11 ∈ x10 ∨ x12 ∈ x10) ∧ x2.edgeSet.ncard + x10.card ≤ x3.size + (1 : ℕ)) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ ∃ (x12 : Finset ℕ), (7 : ℕ) ≤ x12.card ∧ have x13 : ℕ → (Fin x1 → Bool) → Bool := fun (x13 : ℕ) (x14 : Fin x1 → Bool) => PEqualNP.LowMerge.wireVal x3 (List.ofFn (Function.update (Function.update x14 x10 Bool.false) x11 Bool.false)) x13; ∀ x14 ∈ x12, x14 < x3.size ∧ ((∀ (x16 : Fin x1 → Bool), x13 (x1 + x14) x16 = Bool.false) ∨ ∃ x16 < x1 + x14, x13 (x1 + x14) = x13 x16)) := by
  intro x1 x2 x3 hNonBip hDeg hGirth _ hMin hFun
  obtain ⟨C, hVC, _, hOut, hIn⟩ := hMinVC x1 x2 hNonBip
  by_cases hle : x2.edgeSet.ncard + C.card ≤ x3.size + 1
  · exact Or.inl ⟨C, hVC, hle⟩
  · exact Or.inr (hElim x1 x2 C x3 hVC hOut hIn hDeg hGirth hMin hFun (Nat.lt_of_not_le hle))

