import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18757_2
    (hFold01 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
    (42 : ℕ) ≤ C.output → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ (124 : ℕ) →
    (∀ (x : Fin (42 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔
      ∃ (a b : Fin (42 : ℕ)), (↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧ (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x a = Bool.true ∧ x b = Bool.true) →
    (∃ (g : ℕ) (gt : PEqualNP.CircuitLowerBounds.Gate), C.gates[g]? = Option.some gt ∧ gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      (C.wires (List.ofFn fun (i : Fin (42 : ℕ)) => Decidable.decide (i = (0 : Fin (42 : ℕ)) ∨ i = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + g) Bool.false = Bool.true) →
    ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ (123 : ℕ) ∧
      ∀ (x : Fin (42 : ℕ) → Bool), x (0 : Fin (42 : ℕ)) = Bool.true → x (1 : Fin (42 : ℕ)) = Bool.true →
        (D.eval (List.ofFn x) = Bool.true ↔ ∃ (a b : Fin (42 : ℕ)), (↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧ (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x a = Bool.true ∧ x b = Bool.true))
    (hNoRestr123 : ¬∃ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ (123 : ℕ) ∧
    ∀ (x : Fin (42 : ℕ) → Bool), x (0 : Fin (42 : ℕ)) = Bool.true → x (1 : Fin (42 : ℕ)) = Bool.true →
      (D.eval (List.ofFn x) = Bool.true ↔ ∃ (a b : Fin (42 : ℕ)), (↑a < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑b ∧ (↑b + (21 : ℕ) - ↑a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x a = Bool.true ∧ x b = Bool.true)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (42 : ℕ) ≤ x1.output → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (124 : ℕ) → (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), (↑x6 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x7 ∧ (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ¬∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (x8 = (0 : Fin (42 : ℕ)) ∨ x8 = (1 : Fin (42 : ℕ))))).getD ((42 : ℕ) + x6) Bool.false = Bool.true :=
  fun C hout hM hsz hEval hEx => hNoRestr123 (hFold01 C hout hM hsz hEval hEx)
