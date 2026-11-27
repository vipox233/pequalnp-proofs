import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18932_1
    (hAndCase :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.Colorable (2 : ℕ) →
        (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →
        (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) →
        (∃ x14 ∉ x4, ∃ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) (x17 : ℕ),
          x5.gates[x15]? = Option.some x16 ∧
          List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x14) x5.gates = [x16] ∧
          x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x1 ≤ x17 ∧ x17 < x1 + x15 ∧ (x16.inputs = [↑x14, x17] ∨ x16.inputs = [x17, ↑x14])) →
        ∃ (x15 : Fin x1) (x16 : Fin x1), x15 ∉ x4 ∧ x16 ∉ x4 ∧ x15 ≠ x16 ∧ ¬x2.Adj x15 x16 ∧
          ∃ (x17 : ℕ), x17 + (8 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x18 x15 Bool.false) x16 Bool.false)) x17)
    (hOrCase :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.Colorable (2 : ℕ) →
        (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →
        (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) →
        (∃ x14 ∉ x4, ∃ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) (x17 : ℕ),
          x5.gates[x15]? = Option.some x16 ∧
          List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x14) x5.gates = [x16] ∧
          x16.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          x1 ≤ x17 ∧ x17 < x1 + x15 ∧ (x16.inputs = [↑x14, x17] ∨ x16.inputs = [x17, ↑x14])) →
        ∃ (x15 : Fin x1) (x16 : Fin x1), x15 ∉ x4 ∧ x16 ∉ x4 ∧ x15 ≠ x16 ∧ ¬x2.Adj x15 x16 ∧
          ∃ (x17 : ℕ), x17 + (8 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x18 x15 Bool.false) x16 Bool.false)) x17) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2.Colorable (2 : ℕ) → (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → (∃ x14 ∉ x4, ∃ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) (x17 : ℕ), x5.gates[x15]? = Option.some x16 ∧ List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x14) x5.gates = [x16] ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x1 ≤ x17 ∧ x17 < x1 + x15 ∧ (x16.inputs = [↑x14, x17] ∨ x16.inputs = [x17, ↑x14])) → ∃ (x15 : Fin x1) (x16 : Fin x1), x15 ∉ x4 ∧ x16 ∉ x4 ∧ x15 ≠ x16 ∧ ¬x2.Adj x15 x16 ∧ ∃ (x17 : ℕ), x17 + (8 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x18 x15 Bool.false) x16 Bool.false)) x17) :=
  fun x1 x2 _ x4 x5 hCol hDeg hGirth hNoX4 hEdge hMin hFun hSz hEx =>
    Exists.elim hEx fun x14 hx14 =>
      Exists.elim hx14.2 fun x15 hx15 =>
        Exists.elim hx15 fun x16 hx16 =>
          Exists.elim hx16 fun x17 h =>
            Or.elim h.2.2.1
              (fun hAnd => hAndCase x1 x2 x4 x5 hCol hDeg hGirth hNoX4 hEdge hMin hFun hSz ⟨x14, hx14.1, x15, x16, x17, h.1, h.2.1, hAnd, h.2.2.2⟩)
              (fun hOr => hOrCase x1 x2 x4 x5 hCol hDeg hGirth hNoX4 hEdge hMin hFun hSz ⟨x14, hx14.1, x15, x16, x17, h.1, h.2.1, hOr, h.2.2.2⟩)
