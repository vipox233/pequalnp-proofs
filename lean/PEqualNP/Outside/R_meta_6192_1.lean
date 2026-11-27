import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6192_1
    (hMinCircuit :
      ∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : ℕ),
        PEqualNP.MetaComplexity.HasCircuitSize x1 x2 x3 →
        ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 ∧
          x5.size ≤ x3 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x5 = x2)
    (hFromMinimal :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Fin x1) (x4 : Set (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),
        (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (x2.neighborSet x3).ncard = (0 : ℕ) → x4.ncard = (3 : ℕ) → x3 ∉ x4 →
        (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13 ≠ x15 → ∀ (x18 : x2.Walk x13 x15), x18.IsPath → (5 : ℕ) ≤ x18.length) →
        (∀ x14 ∈ x4, (x2.neighborSet x14).ncard = (2 : ℕ)) →
        (∀ (x15 : Fin x1), x15 ≠ x3 → x15 ∉ x4 → (x2.neighborSet x15).ncard = (3 : ℕ)) →
        (∀ (x16 : Fin x1 → Bool), x5 x16 = Bool.true ↔ ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x6 →
        PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →
        x6.size + (5 : ℕ) < (2 : ℕ) * x1 →
        ∃ (x20 : Fin x1), x20 ≠ x3 ∧ x20 ∉ x4 ∧ ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ x6.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x5 (Function.update x22 x20 Bool.false)) x21) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Fin x1) (x4 : Set (Fin x1)) (x5 : (Fin x1 → Bool) → Bool), (30 : ℕ) ≤ x1 → Even x1 → x2.Colorable (2 : ℕ) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (x2.neighborSet x3).ncard = (0 : ℕ) → x4.ncard = (3 : ℕ) → x3 ∉ x4 → (∀ x13 ∈ x4, ∀ x15 ∈ x4, x13 ≠ x15 → ∀ (x18 : x2.Walk x13 x15), x18.IsPath → (5 : ℕ) ≤ x18.length) → (∀ x14 ∈ x4, (x2.neighborSet x14).ncard = (2 : ℕ)) → (∀ (x15 : Fin x1), x15 ≠ x3 → x15 ∉ x4 → (x2.neighborSet x15).ncard = (3 : ℕ)) → (∀ (x16 : Fin x1 → Bool), x5 x16 = Bool.true ↔ ∃ (x17 : Fin x1) (x18 : Fin x1), x2.Adj x17 x18 ∧ x16 x17 = Bool.true ∧ x16 x18 = Bool.true) → ∀ (x17 : ℕ), x17 + (5 : ℕ) < (2 : ℕ) * x1 → PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x17 → ∃ (x20 : Fin x1), x20 ≠ x3 ∧ x20 ∉ x4 ∧ ∃ (x21 : ℕ), x21 + (4 : ℕ) ≤ x17 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x22 : Fin x1 → Bool) => x5 (Function.update x22 x20 Bool.false)) x21 :=
  fun x1 x2 x3 x4 x5 h30 hEv hCol hGir hD3 hC4 h34 hDist hD4 hDall hFun x17 hSz hHCS =>
    Exists.elim (hMinCircuit x1 x5 x17 hHCS) fun C hC =>
      Exists.elim (hFromMinimal x1 x2 x3 x4 x5 C h30 hEv hCol hGir hD3 hC4 h34 hDist hD4 hDall hFun hC.1 hC.2.2 (Nat.lt_of_le_of_lt (Nat.add_le_add_right hC.2.1 (5 : ℕ)) hSz)) fun v hv =>
        ⟨v, hv.1, hv.2.1, Exists.elim hv.2.2 fun s hs => ⟨s, Nat.le_trans hs.1 hC.2.1, hs.2⟩⟩
