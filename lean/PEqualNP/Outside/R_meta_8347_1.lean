import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8347_1
    (hNotReaders :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
        have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;
        have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => Finset.filter (fun x10 : ℕ => x10 ≠ x9 ∧ (x7 (↑x8) (ga x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (ga x10) = Bool.true)) (Finset.range x5.gates.length);
        have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;
        (PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 ∧
          (∃ x16 ∉ x4, ∃ x17 < x5.gates.length, (x9 x16).length = (1 : ℕ) ∧ x7 (↑x16) (ga x17) = Bool.true ∧ (ga x17).op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
          ¬∃ x17 ∉ x4, ∃ x18 < x5.gates.length, x7 (↑x17) (ga x18) = Bool.true ∧ (ga x18).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x17 x18).card) →
        ∃ v ∉ x4, ∃ g < x5.gates.length,
          (x9 v).length = (1 : ℕ) ∧
          x7 (↑v) (ga g) = Bool.true ∧
          (ga g).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          (1 : ℕ) ≤ (x8 v g).card ∧ (x8 v g).card ≤ (2 : ℕ) ∧
          ∀ h ∈ x8 v g, g < h ∧ x7 (x1 + g) (ga h) = Bool.true)
    (hElimNotGate :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have ga : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5;
        have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
        have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;
        have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => Finset.filter (fun x10 : ℕ => x10 ≠ x9 ∧ (x7 (↑x8) (ga x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (ga x10) = Bool.true)) (Finset.range x5.gates.length);
        have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;
        ((∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) ∧
          (7 : ℕ∞) ≤ x2.egirth ∧
          (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) ∧
          PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 ∧
          PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 ∧
          (∀ x15 ∉ x4, (x9 x15).length ≤ (3 : ℕ) ∧ ((x9 x15).length = (3 : ℕ) → ∀ x18 ∈ x9 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) ∧
          (∃ v ∉ x4, ∃ g < x5.gates.length, (x9 v).length = (1 : ℕ) ∧ x7 (↑v) (ga g) = Bool.true ∧ (ga g).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (1 : ℕ) ≤ (x8 v g).card ∧ (x8 v g).card ≤ (2 : ℕ) ∧ ∀ h ∈ x8 v g, g < h ∧ x7 (x1 + g) (ga h) = Bool.true) ∧
          ¬∃ x17 ∉ x4, ∃ x18 < x5.gates.length, x7 (↑x17) (ga x18) = Bool.true ∧ (ga x18).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x17 x18).card) →
        ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x15 ∉ x4, (x9 x15).length ≤ (3 : ℕ) ∧ ((x9 x15).length = (3 : ℕ) → ∀ x18 ∈ x9 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, ∃ x17 < x5.gates.length, (x9 x16).length = (1 : ℕ) ∧ x7 (↑x16) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x17).op = PEqualNP.CircuitLowerBounds.GateOp.not) → (¬∃ x17 ∉ x4, ∃ x18 < x5.gates.length, x7 (↑x17) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x18) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x18).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x17 x18).card) → ∃ x18 ∉ x4, ∃ (x19 : ℕ), x19 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x20 : Fin x1 → Bool) => x6 (Function.update x20 x18 Bool.false)) x19) :=
  fun x1 x2 _ x4 x5 hDeg hGirth hAct hMin hFun hFans hNot hNo3 =>
    hElimNotGate x1 x2 x4 x5 ⟨hDeg, hGirth, hAct, hMin, hFun, hFans,
      hNotReaders x1 x2 x4 x5 ⟨hMin, hFun, hNot, hNo3⟩, hNo3⟩
