import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18459_2
    (hHasOrReader :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
        have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;
        (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
        (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
        (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
        (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        ∀ (x16 : Fin x1), x16 ∉ x4 → (x7 x16).length = (2 : ℕ) → (∀ (x17 : Fin x1), x2.Adj x16 x17 → (x7 x17).length = (2 : ℕ)) →
        (∃ x17 ∈ x7 x16, x17.op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18)
    (hNoOrReader :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
        have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;
        (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) →
        (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) →
        (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) →
        (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) →
        PEqualNP.MetaComplexity.FanInTwo x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 →
        (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) →
        (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        ∀ (x16 : Fin x1), x16 ∉ x4 → (x7 x16).length = (2 : ℕ) → (∀ (x17 : Fin x1), x2.Adj x16 x17 → (x7 x17).length = (2 : ℕ)) →
        (∀ x17 ∈ x7 x16, x17.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →
        ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x7 : Fin x1) => List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains ↑x7) x5.gates;   (∀ x8 ∉ x4, (x2.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x2.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x2.Adj x10 x11 → x10 ∉ x4) → (∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12) → PEqualNP.MetaComplexity.FanInTwo x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ (x14 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x6 x14 → x5.size ≤ x14) → (∀ x15 ∉ x4, (2 : ℕ) ≤ (x7 x15).length ∧ (x7 x15).length ≤ (3 : ℕ) ∧ ((x7 x15).length = (3 : ℕ) → ∀ x18 ∈ x7 x15, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x16 ∉ x4, (x7 x16).length = (2 : ℕ) ∧ ∀ (x17 : Fin x1), x2.Adj x16 x17 → (x7 x17).length = (2 : ℕ)) → ∃ x17 ∉ x4, ∃ (x18 : ℕ), x18 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x19 : Fin x1 → Bool) => x6 (Function.update x19 x17 Bool.false)) x18) := by
  intro x1 x2 x3 x4 x5 x6 x7 hDeg hGirth hAdjOut hHasEdge hFanIn hFun hMin hFanBound hEx
  exact hEx.elim fun x16 h16 =>
    (Classical.em (∃ g ∈ x7 x16, g.op = PEqualNP.CircuitLowerBounds.GateOp.or)).elim
      (fun hOr => @hHasOrReader x1 x2 x3 x4 x5 hDeg hGirth hAdjOut hHasEdge hFanIn hFun hMin hFanBound x16 h16.1 h16.2.1 h16.2.2 hOr)
      (fun hNoOr => @hNoOrReader x1 x2 x3 x4 x5 hDeg hGirth hAdjOut hHasEdge hFanIn hFun hMin hFanBound x16 h16.1 h16.2.1 h16.2.2 (fun g hg hEq => hNoOr ⟨g, hg, hEq⟩))
