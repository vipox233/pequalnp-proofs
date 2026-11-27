import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17970_2
    (hLineEquiv :
      ∀ (a b : Fin (7 : ℕ)),
        (¬((1 : ℕ) ≤ ↑b ∧ ↑b ≤ (3 : ℕ)) ∧ (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ)))) ↔
          (↑b ∈ [(0 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ)] ∧ ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)]))
    (hCircuitDiff :
      let x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => ↑x2 ∈ [(0 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ)] ∧ ↑(x1 - x2) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)];
      ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
        x2.size ≤ (15 : ℕ) ∧
        (25 : ℕ) ≤ x2.output ∧
        x2.output < (25 : ℕ) + x2.size ∧
        (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (25 : ℕ) + x3 ∧ x7 < (25 : ℕ) + x3) ∧
        (∀ (x3 x4 : Fin (7 : ℕ)), x1 x3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧
        (∀ (x3 x4 x5 x6 : Bool),
          have x7 : Fin (7 : ℕ) → Bool := ![x3, Bool.true, Bool.true, Bool.true, x4, x5, x6];
          have x8 : Fin (7 : ℕ) → Bool := fun (x8 : Fin (7 : ℕ)) => !Decidable.decide (∃ (x9 : Fin (7 : ℕ)), x1 x8 x9 ∧ x7 x9 = Bool.true);
          x2.eval ((List.ofFn fun (x9 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x8 x7 x9) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧
        ∀ (x3 : Bool), ∃ (x4 : ℕ → ℕ), x4 (if x3 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x4 (if x3 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x5 < (25 : ℕ), x5 ≠ (0 : ℕ) → x5 ≠ (7 : ℕ) → x4 x5 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x4 x2.output ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 x8 : ℕ), x2.gates[x5]? = Option.some x6 → x6.inputs = [x7, x8] → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((25 : ℕ) + x5) ≤ x4 x7 + x4 x8) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((25 : ℕ) + x5) ≤ Min.min (x4 x7) (x4 x8))) :
    (let x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => ¬((1 : ℕ) ≤ ↑x2 ∧ ↑x2 ≤ (3 : ℕ)) ∧ (x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ))); ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (15 : ℕ) ∧     (25 : ℕ) ≤ x2.output ∧       x2.output < (25 : ℕ) + x2.size ∧         (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (25 : ℕ) + x3 ∧ x7 < (25 : ℕ) + x3) ∧           (∀ (x3 x4 : Fin (7 : ℕ)), x1 x3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧             (∀ (x3 x4 x5 x6 : Bool),                 have x7 : Fin (7 : ℕ) → Bool := ![x3, Bool.true, Bool.true, Bool.true, x4, x5, x6];                 have x8 : Fin (7 : ℕ) → Bool := fun (x8 : Fin (7 : ℕ)) => !Decidable.decide (∃ (x9 : Fin (7 : ℕ)), x1 x8 x9 ∧ x7 x9 = Bool.true);                 x2.eval ((List.ofFn fun (x9 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases x8 x7 x9) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧               ∀ (x3 : Bool), ∃ (x4 : ℕ → ℕ), x4 (if x3 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x4 (if x3 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x5 < (25 : ℕ), x5 ≠ (0 : ℕ) → x5 ≠ (7 : ℕ) → x4 x5 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x4 x2.output ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 x8 : ℕ), x2.gates[x5]? = Option.some x6 → x6.inputs = [x7, x8] → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and → x4 ((25 : ℕ) + x5) ≤ x4 x7 + x4 x8) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → x4 ((25 : ℕ) + x5) ≤ Min.min (x4 x7) (x4 x8))) := by
  rcases hCircuitDiff with ⟨x2, hSz, hO1, hO2, hG, hPos, hNeg, hW⟩
  refine ⟨x2, hSz, hO1, hO2, hG, fun x3 x4 hx => hPos x3 x4 ((hLineEquiv x3 x4).mp hx), fun x3 x4 x5 x6 => ?_, hW⟩
  have hfn :
      (fun (x8 : Fin (7 : ℕ)) => !Decidable.decide (∃ (x9 : Fin (7 : ℕ)), (¬((1 : ℕ) ≤ ↑x9 ∧ ↑x9 ≤ (3 : ℕ)) ∧ (x8 = x9 ∨ x8 = x9 + (1 : Fin (7 : ℕ)) ∨ x8 = x9 + (3 : Fin (7 : ℕ)))) ∧ (![x3, Bool.true, Bool.true, Bool.true, x4, x5, x6] : Fin (7 : ℕ) → Bool) x9 = Bool.true)) =
      (fun (x8 : Fin (7 : ℕ)) => !Decidable.decide (∃ (x9 : Fin (7 : ℕ)), (↑x9 ∈ [(0 : ℕ), (4 : ℕ), (5 : ℕ), (6 : ℕ)] ∧ ↑(x8 - x9) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)]) ∧ (![x3, Bool.true, Bool.true, Bool.true, x4, x5, x6] : Fin (7 : ℕ) → Bool) x9 = Bool.true)) := by
    funext x8
    congr 1
    apply decide_eq_decide.mpr
    constructor <;> rintro ⟨x9, h1, h2⟩
    · exact ⟨x9, (hLineEquiv x8 x9).mp h1, h2⟩
    · exact ⟨x9, (hLineEquiv x8 x9).mpr h1, h2⟩
  simpa only [hfn] using hNeg x3 x4 x5 x6
