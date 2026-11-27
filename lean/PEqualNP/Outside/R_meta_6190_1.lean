import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_6190_1
    (hFanoutZero :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (30 : ℕ) ≤ x1 → x2.Colorable (2 : ℕ) →
        (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 : Fin x1 → Bool), x3 x9 = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) →
        PEqualNP.MetaComplexity.circuitFun x1 x4 = x3 →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →
        x4.size + (1 : ℕ) < (2 : ℕ) * x1 →
        (∀ (x13 : Fin x1),
          have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x13) x4.gates;
          x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ (x14 : Fin x1), (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x14) x4.gates).length = (0 : ℕ)) →
        ∃ (x15 : Fin x1) (x16 : ℕ), x16 + (4 : ℕ) ≤ x4.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update x17 x15 Bool.false)) x16)
    (hFanoutOne :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (30 : ℕ) ≤ x1 → x2.Colorable (2 : ℕ) →
        (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 : Fin x1 → Bool), x3 x9 = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) →
        PEqualNP.MetaComplexity.circuitFun x1 x4 = x3 →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 →
        x4.size + (1 : ℕ) < (2 : ℕ) * x1 →
        (∀ (x13 : Fin x1),
          have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x13) x4.gates;
          x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →
        (∃ (x14 : Fin x1), (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x14) x4.gates).length = (1 : ℕ)) →
        ∃ (x15 : Fin x1) (x16 : ℕ), x16 + (4 : ℕ) ≤ x4.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update x17 x15 Bool.false)) x16) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : (Fin x1 → Bool) → Bool) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (30 : ℕ) ≤ x1 → x2.Colorable (2 : ℕ) → (∀ (x7 : Fin x1), (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 : Fin x1 → Bool), x3 x9 = Bool.true ↔ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → PEqualNP.MetaComplexity.circuitFun x1 x4 = x3 → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x4 → x4.size + (1 : ℕ) < (2 : ℕ) * x1 → (∀ (x13 : Fin x1), have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x13) x4.gates; x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ (x14 : Fin x1), (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x14) x4.gates).length ≤ (1 : ℕ)) → ∃ (x15 : Fin x1) (x16 : ℕ), x16 + (4 : ℕ) ≤ x4.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x3 (Function.update x17 x15 Bool.false)) x16 :=
  fun x1 x2 x3 x4 h30 hCol hDeg hGir hFun hCF hMin hSz hAll hEx =>
    Exists.elim hEx fun v hv =>
      Or.elim (Nat.eq_zero_or_pos (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑v) x4.gates).length)
        (fun h0 => hFanoutZero x1 x2 x3 x4 h30 hCol hDeg hGir hFun hCF hMin hSz hAll ⟨v, h0⟩)
        (fun hpos => hFanoutOne x1 x2 x3 x4 h30 hCol hDeg hGir hFun hCF hMin hSz hAll ⟨v, Nat.le_antisymm hv hpos⟩)
