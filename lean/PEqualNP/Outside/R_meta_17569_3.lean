import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17569_3
    (hSingleOutGate :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x10 : Fin x2.size) (x11 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))),
        have x9 : Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x9 : Fin x2.size) (x10 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x10.1 ∈ x2.leftVars x9 ∧ x10.2 ∈ x2.rightVars x9 ∨ x10.2 ∈ x2.leftVars x9 ∧ x10.1 ∈ x2.rightVars x9;
        (x2.outGates.card = (1 : ℕ) ∧
          x2.WellFormed ∧
          x2.outVars = ∅ ∧
          (∀ (x5 : Fin x2.size) (x6 : Fin (42 : ℕ)), x2.gateVal {x6} x5 = Bool.false) ∧
          (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) ∧
          (x2.size = (19 : ℕ) ∨ x2.size = (20 : ℕ)) ∧
          (∀ (x8 x9 : Fin (42 : ℕ)), x1.Adj x8 x9 → x2.eval {x8, x9} = Bool.true) ∧
          x10 ∉ x2.outGates ∧
          x11.card = (6 : ℕ) ∧
          ∀ x12 ∈ x11, ↑x12.1 < (21 : ℕ) ∧ x1.Adj x12.1 x12.2 ∧ x9 x10 x12 ∧ (∀ x14 ∈ x2.outGates, ¬x9 x14 x12) ∧ ∃ x14 ∈ x2.outGates, Relation.ReflTransGen (fun (x15 x16 : Fin x2.size) => (x15 ∈ x2.leftGates x16 ∨ x15 ∈ x2.rightGates x16) ∧ x2.gateVal {x12.1, x12.2} x16 = Bool.true) x10 x14) →
        ∃ (x10 : Finset (Fin (42 : ℕ))), Maximal (fun (x11 : Finset (Fin (42 : ℕ))) => ∀ x12 ∈ x11, ∀ x14 ∈ x11, ¬x1.Adj x12 x14) x10 ∧ x2.eval x10 = Bool.true)
    (hMultiOutGate :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x10 : Fin x2.size) (x11 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))),
        have x9 : Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x9 : Fin x2.size) (x10 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x10.1 ∈ x2.leftVars x9 ∧ x10.2 ∈ x2.rightVars x9 ∨ x10.2 ∈ x2.leftVars x9 ∧ x10.1 ∈ x2.rightVars x9;
        ((2 : ℕ) ≤ x2.outGates.card ∧
          x2.WellFormed ∧
          x2.outVars = ∅ ∧
          (∀ (x5 : Fin x2.size) (x6 : Fin (42 : ℕ)), x2.gateVal {x6} x5 = Bool.false) ∧
          (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) ∧
          (x2.size = (19 : ℕ) ∨ x2.size = (20 : ℕ)) ∧
          (∀ (x8 x9 : Fin (42 : ℕ)), x1.Adj x8 x9 → x2.eval {x8, x9} = Bool.true) ∧
          x10 ∉ x2.outGates ∧
          x11.card = (6 : ℕ) ∧
          ∀ x12 ∈ x11, ↑x12.1 < (21 : ℕ) ∧ x1.Adj x12.1 x12.2 ∧ x9 x10 x12 ∧ (∀ x14 ∈ x2.outGates, ¬x9 x14 x12) ∧ ∃ x14 ∈ x2.outGates, Relation.ReflTransGen (fun (x15 x16 : Fin x2.size) => (x15 ∈ x2.leftGates x16 ∨ x15 ∈ x2.rightGates x16) ∧ x2.gateVal {x12.1, x12.2} x16 = Bool.true) x10 x14) →
        ∃ (x10 : Finset (Fin (42 : ℕ))), Maximal (fun (x11 : Finset (Fin (42 : ℕ))) => ∀ x12 ∈ x11, ∀ x14 ∈ x11, ¬x1.Adj x12 x14) x10 ∧ x2.eval x10 = Bool.true) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)),   x2.WellFormed →     x2.outVars = ∅ →       (∀ (x5 : Fin x2.size) (x6 : Fin (42 : ℕ)), x2.gateVal {x6} x5 = Bool.false) →         (∀ (x6 : Fin x2.size), Disjoint (x2.leftVars x6) (x2.rightVars x6)) →           x2.size = (19 : ℕ) ∨ x2.size = (20 : ℕ) →             (∀ (x8 x9 : Fin (42 : ℕ)), x1.Adj x8 x9 → x2.eval {x8, x9} = Bool.true) →               (have x9 : Fin x2.size → Fin (42 : ℕ) × Fin (42 : ℕ) → Prop := fun (x9 : Fin x2.size) (x10 : Fin (42 : ℕ) × Fin (42 : ℕ)) => x10.1 ∈ x2.leftVars x9 ∧ x10.2 ∈ x2.rightVars x9 ∨ x10.2 ∈ x2.leftVars x9 ∧ x10.1 ∈ x2.rightVars x9;                 ∃ x10 ∉ x2.outGates, ∃ (x11 : Finset (Fin (42 : ℕ) × Fin (42 : ℕ))), x11.card = (6 : ℕ) ∧ ∀ x12 ∈ x11, ↑x12.1 < (21 : ℕ) ∧ x1.Adj x12.1 x12.2 ∧ x9 x10 x12 ∧ (∀ x14 ∈ x2.outGates, ¬x9 x14 x12) ∧ ∃ x14 ∈ x2.outGates, Relation.ReflTransGen (fun (x15 x16 : Fin x2.size) => (x15 ∈ x2.leftGates x16 ∨ x15 ∈ x2.rightGates x16) ∧ x2.gateVal {x12.1, x12.2} x16 = Bool.true) x10 x14) →                 ∃ (x10 : Finset (Fin (42 : ℕ))), Maximal (fun (x11 : Finset (Fin (42 : ℕ))) => ∀ x12 ∈ x11, ∀ x14 ∈ x11, ¬x1.Adj x12 x14) x10 ∧ x2.eval x10 = Bool.true) :=
  fun x2 hWF hOut hSing hDisj hSz hEdges hEx =>
    Exists.elim hEx fun x10 hx10 =>
    Exists.elim hx10.2 fun x11 hx11 =>
      have hNE11 : x11.Nonempty := Finset.card_pos.mp (Eq.subst (motive := fun n => (0 : ℕ) < n) hx11.1.symm (Nat.zero_lt_succ (5 : ℕ)))
      Exists.elim hNE11 fun e he =>
      Exists.elim (hx11.2 e he).2.2.2.2 fun g hg =>
        Or.elim (Nat.eq_or_lt_of_le (Finset.one_le_card.mpr ⟨g, hg.1⟩))
          (fun hEq => hSingleOutGate x2 x10 x11 ⟨hEq.symm, hWF, hOut, hSing, hDisj, hSz, hEdges, hx10.1, hx11.1, hx11.2⟩)
          (fun hLt => hMultiOutGate x2 x10 x11 ⟨hLt, hWF, hOut, hSing, hDisj, hSz, hEdges, hx10.1, hx11.1, hx11.2⟩)
