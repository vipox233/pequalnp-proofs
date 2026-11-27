import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17311_2
    (hSameSide :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        x2.WellFormed →
        x2.Computes x1 →
        x2.outVars = ∅ →
        (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →
        x2.size = (20 : ℕ) →
        have x8 : Fin (42 : ℕ) → Finset (Fin x2.size) := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9};
        (∀ (x9 : Fin (42 : ℕ)), (x8 x9).card ≤ (4 : ℕ)) →
        (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → (x8 x10 ∪ x8 x11).card ≤ (6 : ℕ)) →
        (∃ (g : Fin x2.size),
          ((0 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (2 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (21 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (23 : Fin (42 : ℕ)) ∈ x2.rightVars g) ∨
          ((21 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (23 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (0 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (2 : Fin (42 : ℕ)) ∈ x2.rightVars g)) →
        False)
    (hCrossSide :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        x2.WellFormed →
        x2.Computes x1 →
        x2.outVars = ∅ →
        (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →
        x2.size = (20 : ℕ) →
        have x8 : Fin (42 : ℕ) → Finset (Fin x2.size) := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9};
        (∀ (x9 : Fin (42 : ℕ)), (x8 x9).card ≤ (4 : ℕ)) →
        (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → (x8 x10 ∪ x8 x11).card ≤ (6 : ℕ)) →
        (∃ (g : Fin x2.size),
          ((0 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (23 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (21 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (2 : Fin (42 : ℕ)) ∈ x2.rightVars g) ∨
          ((21 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (2 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (0 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (23 : Fin (42 : ℕ)) ∈ x2.rightVars g)) →
        False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.WellFormed →     x2.Computes x1 →       x2.outVars = ∅ →         (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →           x2.size = (20 : ℕ) →             have x8 : Fin (42 : ℕ) → Finset (Fin x2.size) := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9};             (∀ (x9 : Fin (42 : ℕ)), (x8 x9).card ≤ (4 : ℕ)) →               (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → (x8 x10 ∪ x8 x11).card ≤ (6 : ℕ)) →                 have x11 : Fin x2.size → Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x11 : Fin x2.size) (x12 x13 : Fin (42 : ℕ)) => x12 ∈ x2.leftVars x11 ∧ x13 ∈ x2.rightVars x11 ∨ x13 ∈ x2.leftVars x11 ∧ x12 ∈ x2.rightVars x11;                 (∃ (x12 : Fin x2.size), x11 x12 (0 : Fin (42 : ℕ)) (21 : Fin (42 : ℕ)) ∧ x11 x12 (2 : Fin (42 : ℕ)) (23 : Fin (42 : ℕ))) → False) :=
  fun x2 hWF hComp hOut hDisj hSz hDeg hNonEdge hEx =>
    Exists.elim hEx fun g hg =>
      Or.elim hg.1
        (fun h0L =>
          Or.elim hg.2
            (fun h2L => hSameSide x2 hWF hComp hOut hDisj hSz hDeg hNonEdge ⟨g, Or.inl ⟨h0L.1, h2L.1, h0L.2, h2L.2⟩⟩)
            (fun h23L => hCrossSide x2 hWF hComp hOut hDisj hSz hDeg hNonEdge ⟨g, Or.inl ⟨h0L.1, h23L.1, h0L.2, h23L.2⟩⟩))
        (fun h21L =>
          Or.elim hg.2
            (fun h2L => hCrossSide x2 hWF hComp hOut hDisj hSz hDeg hNonEdge ⟨g, Or.inr ⟨h21L.1, h2L.1, h21L.2, h2L.2⟩⟩)
            (fun h23L => hSameSide x2 hWF hComp hOut hDisj hSz hDeg hNonEdge ⟨g, Or.inr ⟨h21L.1, h23L.1, h21L.2, h23L.2⟩⟩))
