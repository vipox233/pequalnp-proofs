import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18101_2
    (hFirstEarlier :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      have x2 : (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x3 : Fin x2.size) (x4 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x4.1 ∈ x2.leftVars x3 ∧ x4.2 ∈ x2.rightVars x3 ∨ x4.2 ∈ x2.leftVars x3 ∧ x4.1 ∈ x2.rightVars x3;
      have x3 : (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x3.size → Prop := fun (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x4 : Fin x3.size) => ∀ x5 ∈ x3.leftVars x4, ∀ x7 ∈ x3.rightVars x4, x1.Adj x5 x7;
      ∀ (x4 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x11 x12 : Fin x4.size) (x13 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))),
        (x4.WellFormed ∧
          x4.Computes x1 ∧
          x4.outVars = ∅ ∧
          (∀ (x8 : Fin x4.size) (x9 : Fin (42 : ℕ)), x4.gateVal {x9} x8 = Bool.false) ∧
          (∀ (x9 : Fin x4.size), Disjoint (x4.leftVars x9) (x4.rightVars x9)) ∧
          x4.size ≤ (20 : ℕ) ∧
          x11 < x12 ∧
          x11 ∉ x4.outGates ∧ x12 ∉ x4.outGates ∧
          ¬x3 x4 x11 ∧ ¬x3 x4 x12 ∧
          (6 : ℕ) ≤ x13.card ∧
          ∀ x14 ∈ x13, ↑x14.1 < (21 : ℕ) ∧ x1.Adj x14.1 x14.2 ∧ x2 x4 x11 x14 ∧ ∀ (x16 : Fin x4.size), x3 x4 x16 → ¬x2 x4 x16 x14) →
        False)
    (hFirstLater :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      have x2 : (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x3 : Fin x2.size) (x4 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x4.1 ∈ x2.leftVars x3 ∧ x4.2 ∈ x2.rightVars x3 ∨ x4.2 ∈ x2.leftVars x3 ∧ x4.1 ∈ x2.rightVars x3;
      have x3 : (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x3.size → Prop := fun (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x4 : Fin x3.size) => ∀ x5 ∈ x3.leftVars x4, ∀ x7 ∈ x3.rightVars x4, x1.Adj x5 x7;
      ∀ (x4 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x11 x12 : Fin x4.size) (x13 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))),
        (x4.WellFormed ∧
          x4.Computes x1 ∧
          x4.outVars = ∅ ∧
          (∀ (x8 : Fin x4.size) (x9 : Fin (42 : ℕ)), x4.gateVal {x9} x8 = Bool.false) ∧
          (∀ (x9 : Fin x4.size), Disjoint (x4.leftVars x9) (x4.rightVars x9)) ∧
          x4.size ≤ (20 : ℕ) ∧
          x12 < x11 ∧
          x11 ∉ x4.outGates ∧ x12 ∉ x4.outGates ∧
          ¬x3 x4 x11 ∧ ¬x3 x4 x12 ∧
          (6 : ℕ) ≤ x13.card ∧
          ∀ x14 ∈ x13, ↑x14.1 < (21 : ℕ) ∧ x1.Adj x14.1 x14.2 ∧ x2 x4 x11 x14 ∧ ∀ (x16 : Fin x4.size), x3 x4 x16 → ¬x2 x4 x16 x14) →
        False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x3 : Fin x2.size) (x4 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x4.1 ∈ x2.leftVars x3 ∧ x4.2 ∈ x2.rightVars x3 ∨ x4.2 ∈ x2.leftVars x3 ∧ x4.1 ∈ x2.rightVars x3; have x3 : (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) → Fin x3.size → Prop := fun (x3 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x4 : Fin x3.size) => ∀ x5 ∈ x3.leftVars x4, ∀ x7 ∈ x3.rightVars x4, x1.Adj x5 x7; ∀ (x4 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x4.WellFormed → x4.Computes x1 → x4.outVars = ∅ → (∀ (x8 : Fin x4.size) (x9 : Fin (42 : ℕ)), x4.gateVal {x9} x8 = Bool.false) → (∀ (x9 : Fin x4.size), Disjoint (x4.leftVars x9) (x4.rightVars x9)) → x4.size ≤ (20 : ℕ) → (∃ (x11 : Fin x4.size) (x12 : Fin x4.size), x11 ≠ x12 ∧ x11 ∉ x4.outGates ∧ x12 ∉ x4.outGates ∧ ¬x3 x4 x11 ∧ ¬x3 x4 x12 ∧ ∃ (x13 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))), (6 : ℕ) ≤ x13.card ∧ ∀ x14 ∈ x13, ↑x14.1 < (21 : ℕ) ∧ x1.Adj x14.1 x14.2 ∧ x2 x4 x11 x14 ∧ ∀ (x16 : Fin x4.size), x3 x4 x16 → ¬x2 x4 x16 x14) → False) :=
  fun x4 hWF hComp hOut hSing hDisj hSz hEx =>
    Exists.elim hEx fun g1 hg1 =>
    Exists.elim hg1 fun g2 hg2 =>
    Exists.elim hg2.2.2.2.2.2 fun E hE =>
      Or.elim (lt_or_gt_of_ne hg2.1)
        (fun hLt => hFirstEarlier x4 g1 g2 E ⟨hWF, hComp, hOut, hSing, hDisj, hSz, hLt, hg2.2.1, hg2.2.2.1, hg2.2.2.2.1, hg2.2.2.2.2.1, hE.1, hE.2⟩)
        (fun hGt => hFirstLater x4 g1 g2 E ⟨hWF, hComp, hOut, hSing, hDisj, hSz, hGt, hg2.2.1, hg2.2.2.1, hg2.2.2.2.1, hg2.2.2.2.2.1, hE.1, hE.2⟩)
