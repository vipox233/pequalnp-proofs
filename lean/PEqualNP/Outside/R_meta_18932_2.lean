import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18932_2
    (hBipartiteBalanced :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)),
        x2.Colorable (2 : ℕ) →
        (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →
        (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) →
        ∃ (A B : Finset (Fin x1)),
          Disjoint A B ∧ A ∪ B = Finset.univ \ x4 ∧ A.card = B.card ∧ (3 : ℕ) ≤ A.card ∧
          ∀ (u v : Fin x1), x2.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (hFromBalanced :
      ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj]
        (x4 A B : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        Disjoint A B →
        A ∪ B = Finset.univ \ x4 →
        A.card = B.card →
        (3 : ℕ) ≤ A.card →
        (∀ (u v : Fin x1), x2.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A)) →
        (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) →
        (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →
        PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →
        PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ →
        x5.size + (1 : ℕ) < (4 : ℕ) * A.card →
        (∃ x14 ∉ x4, ∃ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) (x17 : ℕ),
          x5.gates[x15]? = Option.some x16 ∧
          List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x14) x5.gates = [x16] ∧
          (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          x1 ≤ x17 ∧ x17 < x1 + x15 ∧ (x16.inputs = [↑x14, x17] ∨ x16.inputs = [x17, ↑x14])) →
        ∃ (x15 : Fin x1) (x16 : Fin x1), x15 ∉ x4 ∧ x16 ∉ x4 ∧ x15 ≠ x16 ∧ ¬x2.Adj x15 x16 ∧
          ∃ (x17 : ℕ), x17 + (8 : ℕ) ≤ x5.size ∧
            PEqualNP.MetaComplexity.HasCircuitSize x1
              (fun (x18 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x18 x15 Bool.false) x16 Bool.false)) x17) :
    (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2.Colorable (2 : ℕ) → (∀ x7 ∉ x4, (x2.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x2.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → (∃ x14 ∉ x4, ∃ (x15 : ℕ) (x16 : PEqualNP.CircuitLowerBounds.Gate) (x17 : ℕ), x5.gates[x15]? = Option.some x16 ∧ List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x14) x5.gates = [x16] ∧ (x16.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x16.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x1 ≤ x17 ∧ x17 < x1 + x15 ∧ (x16.inputs = [↑x14, x17] ∨ x16.inputs = [x17, ↑x14])) → ∃ (x15 : Fin x1) (x16 : Fin x1), x15 ∉ x4 ∧ x16 ∉ x4 ∧ x15 ≠ x16 ∧ ¬x2.Adj x15 x16 ∧ ∃ (x17 : ℕ), x17 + (8 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x18 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x18 x15 Bool.false) x16 Bool.false)) x17) := by
  intro x1 x2 x3 x4 x5 hCol hDeg hGirth hIso hEdge hMin hFun hSz hFan1
  obtain ⟨A, B, hDisj, hUnion, hEq, hGe3, hBip⟩ := hBipartiteBalanced x1 x2 x4 hCol hDeg hGirth hIso hEdge
  have hCard : A.card + B.card = x1 - x4.card := by
    have h1 := Finset.card_union_of_disjoint hDisj
    rw [hUnion, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hSz' : x5.size + 1 < 4 * A.card := by omega
  exact hFromBalanced x1 x2 x4 A B x5 hDisj hUnion hEq hGe3 hBip hDeg hGirth hMin hFun hSz' hFan1

