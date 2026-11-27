import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18781_2
    (hLiveAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate),
        ((42 : ℕ) ≤ x1.output ∧ PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (124 : ℕ) ∧
          (∀ (x5 : Fin (42 : ℕ) → Bool),
            x1.eval (List.ofFn x5) = Bool.true ↔
              ∃ (a b : Fin (42 : ℕ)),
                (↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧
                  (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
                x5 a = Bool.true ∧ x5 b = Bool.true) ∧
          x1.gates[x6]? = Option.some x7 ∧
          x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) =>
            Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true ∧
          ((42 : ℕ) + x6 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (42 : ℕ) x1 x6 (x1.output - (42 : ℕ)))) →
        False)
    (hDeadAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate),
        ((42 : ℕ) ≤ x1.output ∧ PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (124 : ℕ) ∧
          (∀ (x5 : Fin (42 : ℕ) → Bool),
            x1.eval (List.ofFn x5) = Bool.true ↔
              ∃ (a b : Fin (42 : ℕ)),
                (↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧
                  (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧
                x5 a = Bool.true ∧ x5 b = Bool.true) ∧
          x1.gates[x6]? = Option.some x7 ∧
          x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) =>
            Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true ∧
          (42 : ℕ) + x6 ≠ x1.output ∧ ¬PEqualNP.EdgeOwnership.InCone (42 : ℕ) x1 x6 (x1.output - (42 : ℕ))) →
        False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (22 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) :=
  fun x1 hOut hM hSz hSpec hEx =>
    hEx.elim fun x6 hx6 =>
      hx6.elim fun x7 hx7 =>
        (Classical.em ((42 : ℕ) + x6 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (42 : ℕ) x1 x6 (x1.output - (42 : ℕ)))).elim
          (fun hLive => hLiveAnd x1 x6 x7 ⟨hOut, hM, hSz, hSpec, hx7.1, hx7.2.1, hx7.2.2, hLive⟩)
          (fun hNotLive => hDeadAnd x1 x6 x7
            ⟨hOut, hM, hSz, hSpec, hx7.1, hx7.2.1, hx7.2.2,
              fun hEq => hNotLive (Or.inl hEq), fun hIn => hNotLive (Or.inr hIn)⟩)
