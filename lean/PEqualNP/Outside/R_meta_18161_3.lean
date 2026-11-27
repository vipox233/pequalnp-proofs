import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18161_3
    (hSizeLt7 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C => PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ (f : Fin x1 → Bool), C.eval (List.ofFn f) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 f;
      x5.size < (7 : ℕ) →
      ¬x2.Colorable (2 : ℕ) →
      (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →
      (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
      (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →
      ok x5 →
      (∀ C, ok C → x5.size ≤ C.size) →
      (∀ (x13 : Finset (Fin x1)), (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x14 ∈ x13 ∨ x15 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeSet.ncard + x13.card) →
      ∃ (x14 : Fin x1) (x15 : Fin x1),
        x2.Adj x14 x15 ∧
        ∃ (x16 : Finset ℕ) (x17 : Finset ℕ),
          Disjoint x16 x17 ∧
          (∀ x18 ∈ x16 ∪ x17, x18 < x5.size) ∧
          (∀ x18 ∈ x16,
            ∃ (x20 : ℕ),
              (x20 < x1 + x18 ∨ x1 + x5.size ≤ x20) ∧
              (∀ x21 ∈ x17, x20 ≠ x1 + x21) ∧
              ∀ (x21 : Fin x1 → Bool),
                have x22 : List Bool := x5.wires (List.ofFn (Function.update (Function.update x21 x14 Bool.false) x15 Bool.false));
                x22.getD (x1 + x18) Bool.false = x22.getD x20 Bool.false) ∧
          (∀ x18 ∈ x17, x5.output ≠ x1 + x18 ∧ ∀ (x20 : ℕ) (x21 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x20]? = Option.some x21 → x1 + x18 ∈ x21.inputs → x20 ∈ x16 ∪ x17) ∧
          (7 : ℕ) ≤ x16.card + x17.card)
    (hSizeGe7 :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      have ok : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C => PEqualNP.MetaComplexity.FanInTwo C ∧ ∀ (f : Fin x1 → Bool), C.eval (List.ofFn f) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 f;
      (7 : ℕ) ≤ x5.size →
      ¬x2.Colorable (2 : ℕ) →
      (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →
      (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
      (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →
      ok x5 →
      (∀ C, ok C → x5.size ≤ C.size) →
      (∀ (x13 : Finset (Fin x1)), (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x14 ∈ x13 ∨ x15 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeSet.ncard + x13.card) →
      ∃ (x14 : Fin x1) (x15 : Fin x1),
        x2.Adj x14 x15 ∧
        ∃ (x16 : Finset ℕ) (x17 : Finset ℕ),
          Disjoint x16 x17 ∧
          (∀ x18 ∈ x16 ∪ x17, x18 < x5.size) ∧
          (∀ x18 ∈ x16,
            ∃ (x20 : ℕ),
              (x20 < x1 + x18 ∨ x1 + x5.size ≤ x20) ∧
              (∀ x21 ∈ x17, x20 ≠ x1 + x21) ∧
              ∀ (x21 : Fin x1 → Bool),
                have x22 : List Bool := x5.wires (List.ofFn (Function.update (Function.update x21 x14 Bool.false) x15 Bool.false));
                x22.getD (x1 + x18) Bool.false = x22.getD x20 Bool.false) ∧
          (∀ x18 ∈ x17, x5.output ≠ x1 + x18 ∧ ∀ (x20 : ℕ) (x21 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x20]? = Option.some x21 → x1 + x18 ∈ x21.inputs → x20 ∈ x16 ∪ x17) ∧
          (7 : ℕ) ≤ x16.card + x17.card) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   ¬x2.Colorable (2 : ℕ) →     (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →       (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →         (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →           PEqualNP.MetaComplexity.FanInTwo x5 →             (∀ (x11 : Fin x1 → Bool), x5.eval (List.ofFn x11) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 x11) →               (∀ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 → (∀ (x14 : Fin x1 → Bool), x12.eval (List.ofFn x14) = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 x14) → x5.size ≤ x12.size) →                 (∀ (x13 : Finset (Fin x1)), (∀ (x14 x15 : Fin x1), x2.Adj x14 x15 → x14 ∈ x13 ∨ x15 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeSet.ncard + x13.card) →                   ∃ (x14 : Fin x1) (x15 : Fin x1),                     x2.Adj x14 x15 ∧                       ∃ (x16 : Finset ℕ) (x17 : Finset ℕ),                         Disjoint x16 x17 ∧                           (∀ x18 ∈ x16 ∪ x17, x18 < x5.size) ∧                             (∀ x18 ∈ x16,                                 ∃ (x20 : ℕ),                                   (x20 < x1 + x18 ∨ x1 + x5.size ≤ x20) ∧                                     (∀ x21 ∈ x17, x20 ≠ x1 + x21) ∧                                       ∀ (x21 : Fin x1 → Bool),                                         have x22 : List Bool := x5.wires (List.ofFn (Function.update (Function.update x21 x14 Bool.false) x15 Bool.false));                                         x22.getD (x1 + x18) Bool.false = x22.getD x20 Bool.false) ∧                               (∀ x18 ∈ x17, x5.output ≠ x1 + x18 ∧ ∀ (x20 : ℕ) (x21 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x20]? = Option.some x21 → x1 + x18 ∈ x21.inputs → x20 ∈ x16 ∪ x17) ∧ (7 : ℕ) ≤ x16.card + x17.card) :=
  fun x1 x2 _ x4 x5 hNot2 hDeg hGirth hIso hFan hEval hMin hBeat =>
    Or.elim (Nat.lt_or_ge x5.size (7 : ℕ))
      (fun hLt => hSizeLt7 x1 x2 x4 x5 hLt hNot2 hDeg hGirth hIso ⟨hFan, hEval⟩ (fun C hC => hMin C hC.1 hC.2) hBeat)
      (fun hGe => hSizeGe7 x1 x2 x4 x5 hGe hNot2 hDeg hGirth hIso ⟨hFan, hEval⟩ (fun C hC => hMin C hC.1 hC.2) hBeat)
