import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18330_2
    (hDiffEquiv :
      ∀ (a b : Fin (7 : ℕ)),
        ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] ↔
          (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))))
    (hCircuitDiff :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (25 : ℕ) ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
        (∀ (x2 x3 : Fin (7 : ℕ)), ↑(x2 - x3) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧
        ∀ (x2 : Fin (7 : ℕ) → Bool), x1.eval (List.ofFn fun (x3 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x2 (fun (x4 : Fin (7 : ℕ)) => Decidable.decide (∀ (x5 : Fin (7 : ℕ)), x2 x5 = Bool.true → ¬↑(x5 - x4) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)])) x3) = Bool.false) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (25 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧ ∀ (x2 : Fin (7 : ℕ) → Bool), x1.eval (List.ofFn fun (x3 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x2 (fun (x4 : Fin (7 : ℕ)) => Decidable.decide (∀ (x5 : Fin (7 : ℕ)), x2 x5 = Bool.true → ¬(x5 = x4 ∨ x5 = x4 + (1 : Fin (7 : ℕ)) ∨ x5 = x4 + (3 : Fin (7 : ℕ))))) x3) = Bool.false) := by
  rcases hCircuitDiff with ⟨x1, hSz, hG, hPos, hNeg⟩
  refine ⟨x1, hSz, hG, fun x2 x3 h => hPos x2 x3 ((hDiffEquiv x2 x3).mpr h), fun x2 => ?_⟩
  have hfn :
      (fun (x4 : Fin (7 : ℕ)) => Decidable.decide (∀ (x5 : Fin (7 : ℕ)), x2 x5 = Bool.true → ¬(x5 = x4 ∨ x5 = x4 + (1 : Fin (7 : ℕ)) ∨ x5 = x4 + (3 : Fin (7 : ℕ))))) =
      (fun (x4 : Fin (7 : ℕ)) => Decidable.decide (∀ (x5 : Fin (7 : ℕ)), x2 x5 = Bool.true → ¬↑(x5 - x4) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)])) := by
    funext x4
    apply decide_eq_decide.mpr
    constructor <;> intro h x5 hx5 hn
    · exact h x5 hx5 ((hDiffEquiv x5 x4).mp hn)
    · exact h x5 hx5 ((hDiffEquiv x5 x4).mpr hn)
  exact congrArg (fun f => x1.eval (List.ofFn fun (x3 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x2 f x3)) hfn ▸ hNeg x2
