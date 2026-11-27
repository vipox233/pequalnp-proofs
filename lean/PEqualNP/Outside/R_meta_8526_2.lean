import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8526_2
    (hLeftPair :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x11 : Fin x2.size) (x12 x13 : Fin (42 : ℕ)),
        (x2.WellFormed ∧
          x2.Computes x1 ∧
          x2.outVars = ∅ ∧
          (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) ∧
          (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) ∧
          x2.size = (20 : ℕ) ∧
          (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) ∧
          (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) ∧
          ↑x12 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x13 ∧ ¬x1.Adj x12 x13 ∧
          x2.leftVars x11 = {x12, x13}) →
        False)
    (hRightPair :
      have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)];
      ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)) (x11 : Fin x2.size) (x12 x13 : Fin (42 : ℕ)),
        (x2.WellFormed ∧
          x2.Computes x1 ∧
          x2.outVars = ∅ ∧
          (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) ∧
          (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) ∧
          x2.size = (20 : ℕ) ∧
          (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) ∧
          (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) ∧
          ↑x12 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x13 ∧ ¬x1.Adj x12 x13 ∧
          x2.rightVars x11 = {x12, x13}) →
        False) :
    (have x1 : SimpleGraph (Fin (42 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; ∀ (x2 : PEqualNP.AndCount.AndCountCircuit (42 : ℕ)), x2.WellFormed → x2.Computes x1 → x2.outVars = ∅ → (∀ (x6 : Fin x2.size) (x7 : Fin (42 : ℕ)), x2.gateVal {x7} x6 = Bool.false) → (∀ (x7 : Fin x2.size), Disjoint (x2.leftVars x7) (x2.rightVars x7)) → x2.size = (20 : ℕ) → (∀ (x9 : Fin (42 : ℕ)), {x10 : Fin x2.size | x9 ∈ x2.leftVars x10 ∨ x9 ∈ x2.rightVars x10}.ncard ≤ (4 : ℕ)) → (∀ (x10 x11 : Fin (42 : ℕ)), ↑x10 < (21 : ℕ) → (21 : ℕ) ≤ ↑x11 → ¬x1.Adj x10 x11 → {x15 : Fin x2.size | x10 ∈ x2.leftVars x15 ∨ x10 ∈ x2.rightVars x15 ∨ x11 ∈ x2.leftVars x15 ∨ x11 ∈ x2.rightVars x15}.ncard ≤ (6 : ℕ)) → (∃ (x11 : Fin x2.size × Bool) (x12 : Fin (42 : ℕ)) (x13 : Fin (42 : ℕ)), ↑x12 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x13 ∧ ¬x1.Adj x12 x13 ∧ (if x11.2 = Bool.true then x2.leftVars x11.1 else x2.rightVars x11.1) = {x12, x13}) → False) := by
  intro x1 x2 hWF hComp hOut hSing hDisj hSz hDeg hPair hEx
  rcases hEx with ⟨⟨g, b⟩, u, v, hu, hv, hna, heq⟩
  cases b
  · exact hRightPair x2 g u v ⟨hWF, hComp, hOut, hSing, hDisj, hSz, hDeg, hPair, hu, hv, hna, by simpa using heq⟩
  · exact hLeftPair x2 g u v ⟨hWF, hComp, hOut, hSing, hDisj, hSz, hDeg, hPair, hu, hv, hna, by simpa using heq⟩
