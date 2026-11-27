import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18934_2
    (hDisjointOwnedInputs :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (j : ℕ) (p1 l1 p2 l2 : Fin (13 : ℕ)),
        (∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[i]? = Option.some g →
          (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (a b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < (26 : ℕ) + i ∧ b < (26 : ℕ) + i) →
        p1 ≠ p2 → l1 ≠ l2 →
        PEqualNP.EdgeOwnership.Owns (26 : ℕ) C j (Fin.castAdd (13 : ℕ) p1) (Fin.natAdd (13 : ℕ) l1) →
        PEqualNP.EdgeOwnership.Owns (26 : ℕ) C j (Fin.castAdd (13 : ℕ) p2) (Fin.natAdd (13 : ℕ) l2) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ (a b : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs = [a, b] ∧
          (26 : ℕ) ≤ a ∧ (26 : ℕ) ≤ b ∧ a ≠ b ∧ a < (26 : ℕ) + j ∧ b < (26 : ℕ) + j)
    (hElimNonStarAnd :
      have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) =>
        x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ));
      have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) =>
        (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 →
          (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧
        ∀ (x3 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔
          ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true;
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
        fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 x6 : Fin (13 : ℕ)) =>
          x1 x5 x6 ∧ PEqualNP.EdgeOwnership.Owns (26 : ℕ) x3 x4 (Fin.castAdd (13 : ℕ) x5) (Fin.natAdd (13 : ℕ) x6);
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) =>
        ∀ (x6 x7 x8 x9 : Fin (13 : ℕ)), x3 x4 x5 x6 x7 → x3 x4 x5 x8 x9 → x6 = x8 ∨ x7 = x9;
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x7 a b : ℕ) (p1 l1 p2 l2 : Fin (13 : ℕ)),
        (x2 x5 ∧ x7 < x5.size ∧ (∀ x9 < x7, x4 x5 x9) ∧
         x3 x5 x7 p1 l1 ∧ x3 x5 x7 p2 l2 ∧ p1 ≠ p2 ∧ l1 ≠ l2 ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
         (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x7).inputs = [a, b] ∧
         (26 : ℕ) ≤ a ∧ (26 : ℕ) ≤ b ∧ a ≠ b ∧ a < (26 : ℕ) + x7 ∧ b < (26 : ℕ) + x7) →
        ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x11.size ≤ x5.size ∧ ∀ x12 ≤ x7, x4 x11 x12) :
    (have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3) ∧ ∀ (x3 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 x6 : Fin (13 : ℕ)) => x1 x5 x6 ∧ PEqualNP.EdgeOwnership.Owns (26 : ℕ) x3 x4 (Fin.castAdd (13 : ℕ) x5) (Fin.natAdd (13 : ℕ) x6); have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) => ∀ (x6 x7 x8 x9 : Fin (13 : ℕ)), x3 x4 x5 x6 x7 → x3 x4 x5 x8 x9 → x6 = x8 ∨ x7 = x9; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → ∀ x7 < x5.size, (∀ x9 < x7, x4 x5 x9) → ¬x4 x5 x7 → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x11.size ≤ x5.size ∧ ∀ x12 ≤ x7, x4 x11 x12) := by
  intro x1 x2 x3 x4 x5 hx2 x7 hx7 hPrev hNot
  have hEx : ∃ (p1 l1 p2 l2 : Fin (13 : ℕ)), x3 x5 x7 p1 l1 ∧ x3 x5 x7 p2 l2 ∧ p1 ≠ p2 ∧ l1 ≠ l2 :=
    Classical.byContradiction fun hNo => hNot fun p1 l1 p2 l2 hA hB =>
      Classical.byContradiction fun hNotOr =>
        hNo ⟨p1, l1, p2, l2, hA, hB, fun hp => hNotOr (Or.inl hp), fun hl => hNotOr (Or.inr hl)⟩
  exact Exists.elim hEx fun p1 h1 =>
    Exists.elim h1 fun l1 h2 =>
      Exists.elim h2 fun p2 h3 =>
        Exists.elim h3 fun l2 hW =>
          let hIn := hDisjointOwnedInputs x5 x7 p1 l1 p2 l2 hx2.1 hW.2.2.1 hW.2.2.2 hW.1.2 hW.2.1.2
          Exists.elim hIn.2 fun a ha =>
            Exists.elim ha fun b hb =>
              hElimNonStarAnd x5 x7 a b p1 l1 p2 l2
                ⟨hx2, hx7, hPrev, hW.1, hW.2.1, hW.2.2.1, hW.2.2.2,
                 hIn.1, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1, hb.2.2.2.2.2⟩
