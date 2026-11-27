import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18187_2
    (hInitEq :
      [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ)] =
        [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ)] ++
          List.replicate (3 : ℕ) (134213632 : ℕ) ++
          [(105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ)] ++
          List.replicate (11 : ℕ) (134213632 : ℕ))
    (hCircuitCompact :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (15 : ℕ) ∧
        (25 : ℕ) ≤ x1.output ∧
        x1.output < (25 : ℕ) + x1.size ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧
        (List.foldl
          (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>
            have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);
            have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);
            x2 ++ [bif x3.op.eval [Bool.false, Bool.true] then x4 ||| x5 else x4 &&& x5])
          ([(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ)] ++
            List.replicate (3 : ℕ) (134213632 : ℕ) ++
            [(105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ)] ++
            List.replicate (11 : ℕ) (134213632 : ℕ))
          x1.gates).getD x1.output (0 : ℕ) = (4095 : ℕ) ∧
        (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] (0 : ℕ)).getD x1.output Option.none).getD (2 : ℕ) ∧
        (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] (7 : ℕ)).getD x1.output Option.none).getD (2 : ℕ)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (15 : ℕ) ∧     (25 : ℕ) ≤ x1.output ∧       x1.output < (25 : ℕ) + x1.size ∧         (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧           (List.foldl                     (fun (x2 : List ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate) =>                       have x4 : ℕ := x2.getD (x3.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ);                       have x5 : ℕ := x2.getD (x3.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ);                       x2 ++ [bif x3.op.eval [Bool.false, Bool.true] then x4 ||| x5 else x4 &&& x5])                     [(70689 : ℕ), (5263618 : ℕ), (1046528 : ℕ), (47534084 : ℕ), (28520456 : ℕ), (3158096 : ℕ), (62080 : ℕ), (86679559 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (105693240 : ℕ), (126812608 : ℕ), (133172736 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ), (134213632 : ℕ)] x1.gates).getD                 x1.output (0 : ℕ) =               (4095 : ℕ) ∧             ∀ x2 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (25 : ℕ) [(0 : ℕ), (7 : ℕ)] x2).getD x1.output Option.none).getD (2 : ℕ)) :=
  Exists.elim hCircuitCompact fun x1 hP =>
    ⟨x1, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hInitEq.symm ▸ hP.2.2.2.2.1,
      fun _ hx2 =>
        Or.elim (List.mem_cons.mp hx2)
          (fun h0 => h0.symm ▸ hP.2.2.2.2.2.1)
          (fun h1 =>
            Or.elim (List.mem_cons.mp h1)
              (fun h7 => h7.symm ▸ hP.2.2.2.2.2.2)
              (fun hnil => False.elim (List.not_mem_nil hnil)))⟩
