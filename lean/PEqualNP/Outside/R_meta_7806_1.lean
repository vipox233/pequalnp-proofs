import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7806_1
    (hFanoutLeOne :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
        (∀ x12 ∉ x4,
          have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;
          x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        ∀ (x13 x14 : Fin x1), x2.Adj x13 x14 →
        (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x13) x5.gates).length ≤ (1 : ℕ) →
        ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15)
    (hBothFanoutTwo :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →
        (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →
        (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →
        (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →
        (∀ x12 ∉ x4,
          have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;
          x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        ∀ (x13 x14 : Fin x1), x2.Adj x13 x14 →
        (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x13) x5.gates).length = (2 : ℕ) →
        (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x14) x5.gates).length = (2 : ℕ) →
        ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →             PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →               (∀ x12 ∉ x4,                   have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;                   x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                 (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x13) x5.gates).length ≤ (2 : ℕ) ∧ (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x14) x5.gates).length ≤ (2 : ℕ)) → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15 := by
  intro x1 x2 x3 x4 x5 hDeg hGir hIso hEd hMin hFun hAll hEx
  rcases hEx with ⟨u, v, huv, hu, hv⟩
  rcases Nat.lt_or_ge (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑u) x5.gates).length 2 with hu1 | hu2
  · exact @hFanoutLeOne x1 x2 x3 x4 x5 hDeg hGir hIso hEd hMin hFun hAll u v huv (Nat.le_of_lt_succ hu1)
  · rcases Nat.lt_or_ge (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑v) x5.gates).length 2 with hv1 | hv2
    · exact @hFanoutLeOne x1 x2 x3 x4 x5 hDeg hGir hIso hEd hMin hFun hAll v u (x2.symm.symm u v huv) (Nat.le_of_lt_succ hv1)
    · exact @hBothFanoutTwo x1 x2 x3 x4 x5 hDeg hGir hIso hEd hMin hFun hAll u v huv (Nat.le_antisymm hu hu2) (Nat.le_antisymm hv hv2)
