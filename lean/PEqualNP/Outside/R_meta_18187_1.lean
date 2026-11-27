import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18187_1
    (hExists12 : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      x1.size ≤ (15 : ℕ) ∧
      (12 : ℕ) ≤ x1.output ∧
      x1.output < (12 : ℕ) + x1.size ∧
      (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (12 : ℕ) + x2 ∧ x6 < (12 : ℕ) + x2) ∧
      (List.foldl
        (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
          have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
          have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
          x2 ++ [bif x3.op.eval [Bool.false, Bool.true] then x4 ||| x5 else x4 &&& x5])
        [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ), (134213632 : ℕ), (105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ)] x1.gates).getD x1.output (0 : ℕ) = (4095 : ℕ) ∧
      ∀ x2 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (12 : ℕ) [(0 : ℕ), (7 : ℕ)] x2).getD x1.output Option.none).getD (2 : ℕ))
    (hLift : ∀ (init1 init2 : List ℕ) (f : ℕ → ℕ) (x1 : PEqualNP.CircuitLowerBounds.Circuit),
      have ok : ℕ → List ℕ → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun n init C =>
        C.size ≤ (15 : ℕ) ∧ n ≤ C.output ∧ C.output < n + C.size ∧
        (∀ (i : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[i]? = Option.some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (a b : ℕ), g.inputs = [a, b] ∧ a ≠ b ∧ a < n + i ∧ b < n + i) ∧
        (List.foldl
          (fun (a : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
            have v0 : ℕ := a.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
            have v1 : ℕ := a.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
            a ++ [bif g.op.eval [Bool.false, Bool.true] then v0 ||| v1 else v0 &&& v1])
          init C.gates).getD C.output (0 : ℕ) = (4095 : ℕ) ∧
        ∀ x ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults C n [(0 : ℕ), (7 : ℕ)] x).getD C.output Option.none).getD (2 : ℕ);
      init1.length = (12 : ℕ) → init2.length = (25 : ℕ) →
      f (0 : ℕ) = (0 : ℕ) → f (7 : ℕ) = (7 : ℕ) →
      (∀ i < (12 : ℕ), f i < (25 : ℕ) ∧ init2.getD (f i) (0 : ℕ) = init1.getD i (0 : ℕ)) →
      (∀ i < (12 : ℕ), ∀ j < (12 : ℕ), f i = f j → i = j) →
      ok (12 : ℕ) init1 x1 →
      ∃ (y1 : PEqualNP.CircuitLowerBounds.Circuit), ok (25 : ℕ) init2 y1) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (15 : ℕ) ∧     (25 : ℕ) ≤ x1.output ∧       x1.output < (25 : ℕ) + x1.size ∧         (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧           (List.foldl                     (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>                       have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                       have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                       x2 ++ [bif x3.op.eval [Bool.false, Bool.true] then x4 ||| x5 else x4 &&& x5])                     [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ)] x1.gates).getD                 x1.output (0 : ℕ) =               (4095 : ℕ) ∧             ∀ x2 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] x2).getD x1.output Option.none).getD (2 : ℕ)) := by
  exact Exists.elim hExists12 fun C hC =>
    hLift
      [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ), (134213632 : ℕ), (105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ)]
      [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ)]
      (fun i => if i < 9 then i else i + 2)
      C rfl rfl rfl rfl (by decide) (by decide) hC
