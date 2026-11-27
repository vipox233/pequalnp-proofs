import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8528_2
    (hCard4 :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x11 : Finset (Fin x2.size × Bool)),
        (x2.WellFormed ∧
          x2.Computes x1 ∧
          x2.outVars = ∅ ∧
          (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) ∧
          (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) ∧
          x2.size = (20 : ℕ) ∧
          (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) ∧
          (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) ∧
          x11.card = (4 : ℕ) ∧
          (∀ x12 ∈ x11, ∃ (x14 : Fin (42 : ℕ)) (x15 : Fin (42 : ℕ)), x1.Adj x14 x15 ∧ (if x12.2 = Bool.true then x2.leftVars x12.1 else x2.rightVars x12.1) = {x14, x15}) ∧
          ∀ x12 ∈ x11, ∀ x14 ∈ x11, x12 ≠ x14 → Disjoint (if x12.2 = Bool.true then x2.leftVars x12.1 else x2.rightVars x12.1) (if x14.2 = Bool.true then x2.leftVars x14.1 else x2.rightVars x14.1)) →
        False)
    (hCardGe5 :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x11 : Finset (Fin x2.size × Bool)),
        (x2.WellFormed ∧
          x2.Computes x1 ∧
          x2.outVars = ∅ ∧
          (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) ∧
          (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) ∧
          x2.size = (20 : ℕ) ∧
          (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) ∧
          (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) ∧
          (5 : ℕ) ≤ x11.card ∧
          (∀ x12 ∈ x11, ∃ (x14 : Fin (42 : ℕ)) (x15 : Fin (42 : ℕ)), x1.Adj x14 x15 ∧ (if x12.2 = Bool.true then x2.leftVars x12.1 else x2.rightVars x12.1) = {x14, x15}) ∧
          ∀ x12 ∈ x11, ∀ x14 ∈ x11, x12 ≠ x14 → Disjoint (if x12.2 = Bool.true then x2.leftVars x12.1 else x2.rightVars x12.1) (if x14.2 = Bool.true then x2.leftVars x14.1 else x2.rightVars x14.1)) →
        False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (20 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) → (∃ (x11 : Finset (Fin x2.size × Bool)), (4 : ℕ) ≤ x11.card ∧ (∀ x12 ∈ x11, ∃ (x14 : Fin (42 : ℕ)) (x15 : Fin (42 : ℕ)), x1.Adj x14 x15 ∧ (if x12.2 = Bool.true then x2.leftVars x12.1 else x2.rightVars x12.1) = {x14, x15}) ∧ ∀ x12 ∈ x11, ∀ x14 ∈ x11, x12 ≠ x14 → Disjoint (if x12.2 = Bool.true then x2.leftVars x12.1 else x2.rightVars x12.1) (if x14.2 = Bool.true then x2.leftVars x14.1 else x2.rightVars x14.1)) → False) :=
  fun x2 hWF hComp hOut hSing hDisj hSz hDeg hPair hEx =>
    Exists.elim hEx fun s hs =>
      Or.elim (Nat.eq_or_lt_of_le hs.1)
        (fun hEq => hCard4 x2 s ⟨hWF, hComp, hOut, hSing, hDisj, hSz, hDeg, hPair, hEq.symm, hs.2.1, hs.2.2⟩)
        (fun hLt => hCardGe5 x2 s ⟨hWF, hComp, hOut, hSing, hDisj, hSz, hDeg, hPair, hLt, hs.2.1, hs.2.2⟩)
