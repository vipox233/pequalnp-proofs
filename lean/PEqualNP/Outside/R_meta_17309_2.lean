import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17309_2
    (hAligned :
      let x1 : SimpleGraph (Fin (42 : ℕ)) :=
        SimpleGraph.fromRel fun (a b : Fin (42 : ℕ)) =>
          ↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧ (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        (x2.WellFormed ∧
         x2.Computes x1 ∧
         x2.outVars = ∅ ∧
         (∀ (g : Fin x2.size), Disjoint (x2.leftVars g) (x2.rightVars g)) ∧
         x2.size = (20 : ℕ) ∧
         (∀ (v : Fin (42 : ℕ)),
           Fintype.card (Subtype fun (g : Fin x2.size) => v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g) ≤ (4 : ℕ)) ∧
         (∀ (u v : Fin (42 : ℕ)), ↑u < (21 : ℕ) → (21 : ℕ) ≤ ↑v → ¬x1.Adj u v →
           Fintype.card (Subtype fun (g : Fin x2.size) =>
             (u ∈ x2.leftVars g ∨ u ∈ x2.rightVars g) ∨ (v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g)) ≤ (6 : ℕ)) ∧
         (∃ (g : Fin x2.size),
           ((0 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (1 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧
            (21 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (22 : Fin (42 : ℕ)) ∈ x2.rightVars g) ∨
           ((21 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (22 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧
            (0 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (1 : Fin (42 : ℕ)) ∈ x2.rightVars g))) →
        False)
    (hCrossed :
      let x1 : SimpleGraph (Fin (42 : ℕ)) :=
        SimpleGraph.fromRel fun (a b : Fin (42 : ℕ)) =>
          ↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧ (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),
        (x2.WellFormed ∧
         x2.Computes x1 ∧
         x2.outVars = ∅ ∧
         (∀ (g : Fin x2.size), Disjoint (x2.leftVars g) (x2.rightVars g)) ∧
         x2.size = (20 : ℕ) ∧
         (∀ (v : Fin (42 : ℕ)),
           Fintype.card (Subtype fun (g : Fin x2.size) => v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g) ≤ (4 : ℕ)) ∧
         (∀ (u v : Fin (42 : ℕ)), ↑u < (21 : ℕ) → (21 : ℕ) ≤ ↑v → ¬x1.Adj u v →
           Fintype.card (Subtype fun (g : Fin x2.size) =>
             (u ∈ x2.leftVars g ∨ u ∈ x2.rightVars g) ∨ (v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g)) ≤ (6 : ℕ)) ∧
         (∃ (g : Fin x2.size),
           ((0 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (22 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧
            (21 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (1 : Fin (42 : ℕ)) ∈ x2.rightVars g) ∨
           ((21 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧ (1 : Fin (42 : ℕ)) ∈ x2.leftVars g ∧
            (0 : Fin (42 : ℕ)) ∈ x2.rightVars g ∧ (22 : Fin (42 : ℕ)) ∈ x2.rightVars g))) →
        False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.WellFormed →     x2.Computes x1 →       x2.outVars = ∅ →         (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →           x2.size = (20 : ℕ) →             have x8 : Fin (42 : ℕ) → Finset (Fin x2.size) := fun (x8 : Fin (42 : ℕ)) => {x9 : Fin x2.size | x8 ∈ x2.leftVars x9 ∨ x8 ∈ x2.rightVars x9};             (∀ (x9 : Fin (42 : ℕ)), (x8 x9).card ≤ (4 : ℕ)) →               (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → (x8 x10 ∪ x8 x11).card ≤ (6 : ℕ)) →                 have x11 : Fin x2.size → Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x11 : Fin x2.size) (x12 x13 : Fin (42 : ℕ)) => x12 ∈ x2.leftVars x11 ∧ x13 ∈ x2.rightVars x11 ∨ x13 ∈ x2.leftVars x11 ∧ x12 ∈ x2.rightVars x11;                 (∃ (x12 : Fin x2.size), x11 x12 (0 : Fin (42 : ℕ)) (21 : Fin (42 : ℕ)) ∧ x11 x12 (1 : Fin (42 : ℕ)) (22 : Fin (42 : ℕ))) → False) :=
  fun x2 hWF hComp hOut hDisj hSz hDeg hUnion hPair =>
    let hDeg' : ∀ (v : Fin (42 : ℕ)),
        Fintype.card (Subtype fun (g : Fin x2.size) => v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g) ≤ (4 : ℕ) :=
      fun v =>
        Eq.mp
          (congrArg (fun k => k ≤ (4 : ℕ))
            (Fintype.card_subtype fun g : Fin x2.size => v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g).symm)
          (hDeg v)
    let hUnion' : ∀ (u v : Fin (42 : ℕ)), ↑u < (21 : ℕ) → (21 : ℕ) ≤ ↑v →
        ¬(SimpleGraph.fromRel fun (a b : Fin (42 : ℕ)) =>
          ↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧ (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]).Adj u v →
        Fintype.card (Subtype fun (g : Fin x2.size) =>
          (u ∈ x2.leftVars g ∨ u ∈ x2.rightVars g) ∨ (v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g)) ≤ (6 : ℕ) :=
      fun u v hu hv hna =>
        Eq.mp
          (congrArg (fun k => k ≤ (6 : ℕ))
            ((Fintype.card_subtype fun g : Fin x2.size =>
                (u ∈ x2.leftVars g ∨ u ∈ x2.rightVars g) ∨ (v ∈ x2.leftVars g ∨ v ∈ x2.rightVars g)).trans
              (congrArg Finset.card (Finset.filter_or _ _ Finset.univ))).symm)
          (hUnion u v hu hv hna)
    Exists.elim hPair fun g hg =>
      Or.elim hg.1
        (fun h021 =>
          Or.elim hg.2
            (fun h122 =>
              hAligned x2 ⟨hWF, hComp, hOut, hDisj, hSz, hDeg', hUnion',
                ⟨g, Or.inl ⟨h021.1, h122.1, h021.2, h122.2⟩⟩⟩)
            (fun h221 =>
              hCrossed x2 ⟨hWF, hComp, hOut, hDisj, hSz, hDeg', hUnion',
                ⟨g, Or.inl ⟨h021.1, h221.1, h021.2, h221.2⟩⟩⟩))
        (fun h210 =>
          Or.elim hg.2
            (fun h122 =>
              hCrossed x2 ⟨hWF, hComp, hOut, hDisj, hSz, hDeg', hUnion',
                ⟨g, Or.inr ⟨h210.1, h122.1, h210.2, h122.2⟩⟩⟩)
            (fun h221 =>
              hAligned x2 ⟨hWF, hComp, hOut, hDisj, hSz, hDeg', hUnion',
                ⟨g, Or.inr ⟨h210.1, h221.1, h210.2, h221.2⟩⟩⟩))
