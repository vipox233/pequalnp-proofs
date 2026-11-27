import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7808_1
    (hAllCubic :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),
        Odd x6 →
        (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →
        (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →
        (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = (3 : ℕ)) →
        (7 : ℕ∞) ≤ x2.egirth →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        ∃ (x16 : Fin x6) (x17 : Fin x6),
          x2.Adj (x7 x16) (x7 x17) ∧
          ∃ (x18 : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo x18 ∧
            x18.size ≤ x5.size ∧
            PEqualNP.MetaComplexity.circuitFun x1 x18 = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧
            ∃ (x19 : Finset ℕ),
              (7 : ℕ) ≤ x19.card ∧
              ∀ x20 ∈ x19,
                x20 < x18.size ∧
                ((∃ (x22 : ℕ),
                    (x22 < x1 + x20 ∧ (x22 < x1 ∨ x22 - x1 ∉ x19) ∨ x1 + x18.size ≤ x22) ∧
                    ∀ (x23 : Fin x1 → Bool),
                      have x24 : List Bool := x18.wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));
                      x24.getD (x1 + x20) Bool.false = x24.getD x22 Bool.false) ∨
                  x18.output ≠ x1 + x20 ∧ PEqualNP.MetaComplexity.NestedCover.readsIn x18 (Finset.range x18.size \ x19) (x1 + x20) = (0 : ℕ)))
    (hHasIsolated :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),
        x4.Nonempty →
        Odd x6 →
        (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →
        (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →
        (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →
        (7 : ℕ∞) ≤ x2.egirth →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
        ∃ (x16 : Fin x6) (x17 : Fin x6),
          x2.Adj (x7 x16) (x7 x17) ∧
          ∃ (x18 : PEqualNP.CircuitLowerBounds.Circuit),
            PEqualNP.MetaComplexity.FanInTwo x18 ∧
            x18.size ≤ x5.size ∧
            PEqualNP.MetaComplexity.circuitFun x1 x18 = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧
            ∃ (x19 : Finset ℕ),
              (7 : ℕ) ≤ x19.card ∧
              ∀ x20 ∈ x19,
                x20 < x18.size ∧
                ((∃ (x22 : ℕ),
                    (x22 < x1 + x20 ∧ (x22 < x1 ∨ x22 - x1 ∉ x19) ∨ x1 + x18.size ≤ x22) ∧
                    ∀ (x23 : Fin x1 → Bool),
                      have x24 : List Bool := x18.wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));
                      x24.getD (x1 + x20) Bool.false = x24.getD x22 Bool.false) ∨
                  x18.output ≠ x1 + x20 ∧ PEqualNP.MetaComplexity.NestedCover.readsIn x18 (Finset.range x18.size \ x19) (x1 + x20) = (0 : ℕ))) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 x8 : Fin x6 ↪ Fin x1),   Odd x6 →     (∀ (x10 : Fin x6), x2.Adj (x7 x10) (x8 x10) ∧ x8 x10 ∉ Set.range ⇑x7) →       (∀ (x11 x12 : Fin x6), x2.Adj (x7 x11) (x7 x12) ↔ (↑x11 + (1 : ℕ)) % x6 = ↑x12 ∨ (↑x12 + (1 : ℕ)) % x6 = ↑x11) →         (∀ (x12 : Fin x1), (x2.neighborSet x12).ncard = if x12 ∈ x4 then (0 : ℕ) else (3 : ℕ)) →           (7 : ℕ∞) ≤ x2.egirth →             PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →                 ∃ (x16 : Fin x6) (x17 : Fin x6),                   x2.Adj (x7 x16) (x7 x17) ∧                     ∃ (x18 : PEqualNP.CircuitLowerBounds.Circuit),                       PEqualNP.MetaComplexity.FanInTwo x18 ∧                         x18.size ≤ x5.size ∧                           PEqualNP.MetaComplexity.circuitFun x1 x18 = PEqualNP.MetaComplexity.circuitFun x1 x5 ∧                             ∃ (x19 : Finset ℕ),                               (7 : ℕ) ≤ x19.card ∧                                 ∀ x20 ∈ x19,                                   x20 < x18.size ∧                                     ((∃ (x22 : ℕ),                                         (x22 < x1 + x20 ∧ (x22 < x1 ∨ x22 - x1 ∉ x19) ∨ x1 + x18.size ≤ x22) ∧                                           ∀ (x23 : Fin x1 → Bool),                                             have x24 : List Bool := x18.wires (List.ofFn (Function.update (Function.update x23 (x7 x16) Bool.false) (x7 x17) Bool.false));                                             x24.getD (x1 + x20) Bool.false = x24.getD x22 Bool.false) ∨                                       x18.output ≠ x1 + x20 ∧ PEqualNP.MetaComplexity.NestedCover.readsIn x18 (Finset.range x18.size \ x19) (x1 + x20) = (0 : ℕ)) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hOdd h10 h11 h12 hGir hMin hFun
  rcases x4.eq_empty_or_nonempty with rfl | hne
  · exact @hAllCubic x1 x2 x3 x5 x6 x7 x8 hOdd h10 h11 (fun v => by simpa using h12 v) hGir hMin hFun
  · exact @hHasIsolated x1 x2 x3 x4 x5 x6 x7 x8 hne hOdd h10 h11 h12 hGir hMin hFun
