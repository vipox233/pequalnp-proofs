import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17893_1
    (hVert01 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (11 : ℕ)),
        (↑x3 < (2 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (11 : ℕ) x2 ∧ (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x2 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) ∧ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x7.op) x2.gates ≤ (12 : ℕ)) →
          ∃ (x8 : Finset (Sym2 (Fin (11 : ℕ)))) (x9 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (x1.deleteEdges ↑x8) x9 ∧ x9.card + x8.card ≤ (6 : ℕ))
    (hVert23 :
      let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))];
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (11 : ℕ)),
        ((2 : ℕ) ≤ ↑x3 ∧ x3 < (4 : Fin (11 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (11 : ℕ) x2 ∧ (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x2 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) ∧ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x7.op) x2.gates ≤ (12 : ℕ)) →
          ∃ (x8 : Finset (Sym2 (Fin (11 : ℕ)))) (x9 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (x1.deleteEdges ↑x8) x9 ∧ x9.card + x8.card ≤ (6 : ℕ)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x3 < (4 : Fin (11 : ℕ)), PEqualNP.TopForm.IsAO2 (11 : ℕ) x2 → (∀ (x6 : Fin (11 : ℕ) → Bool), x6 x3 = Bool.false → PEqualNP.MetaComplexity.circuitFun (11 : ℕ) x2 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x6) → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x7.op) x2.gates ≤ (12 : ℕ) → ∃ (x8 : Finset (Sym2 (Fin (11 : ℕ)))) (x9 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (x1.deleteEdges ↑x8) x9 ∧ x9.card + x8.card ≤ (6 : ℕ) :=
  fun x2 x3 hLt4 hAO hEv hCnt =>
    (Nat.lt_or_ge (x3 : ℕ) (2 : ℕ)).elim
      (fun hLt2 => hVert01 x2 x3 ⟨hLt2, hAO, hEv, hCnt⟩)
      (fun hGe2 => hVert23 x2 x3 ⟨hGe2, hLt4, hAO, hEv, hCnt⟩)
