import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17719_2
    (hCanonWeight :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool),
        (∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate),
          x1.gates[x4]? = Option.some x5 →
          (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (x6 : ℕ) (x7 : ℕ), x5.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (25 : ℕ) + x4 ∧ x7 < (25 : ℕ) + x4) →
        (2 : ℕ) ≤
          (x1.gates.foldl
            (fun (ws : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
              ws ++
                [if g.op.eval [Bool.true, Bool.false] then
                  Min.min (ws.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ))
                    (ws.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ))
                else
                  ws.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) + ws.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)])
            (List.ofFn fun (i : Fin (25 : ℕ)) =>
              if (↑i : ℕ) = (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) then (0 : ℕ)
              else if (↑i : ℕ) = (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) then (1 : ℕ)
              else (2 : ℕ))).getD x1.output (0 : ℕ) →
        ∃ (x3 : ℕ → ℕ),
          x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧
          x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧
          (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧
          (2 : ℕ) ≤ x3 x1.output ∧
          ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ),
            x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] →
            (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧
            (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)))
    (hCircuitWitness :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate),
          x1.gates[x2]? = Option.some x3 →
          (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧
        (∀ x2 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)],
          x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧
        (∀ x2 ∈ [(1919 : ℕ), (2036 : ℕ), (3918 : ℕ), (4036 : ℕ), (5917 : ℕ), (6036 : ℕ), (7948 : ℕ), (8068 : ℕ), (10042 : ℕ), (10160 : ℕ), (12042 : ℕ), (14104 : ℕ), (14224 : ℕ), (16136 : ℕ), (16256 : ℕ)],
          x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧
        ∀ (x2 : Bool),
          (2 : ℕ) ≤
            (x1.gates.foldl
              (fun (ws : List ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) =>
                ws ++
                  [if g.op.eval [Bool.true, Bool.false] then
                    Min.min (ws.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ))
                      (ws.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ))
                  else
                    ws.getD (g.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) + ws.getD (g.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)])
              (List.ofFn fun (i : Fin (25 : ℕ)) =>
                if (↑i : ℕ) = (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) then (0 : ℕ)
                else if (↑i : ℕ) = (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) then (1 : ℕ)
                else (2 : ℕ))).getD x1.output (0 : ℕ)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ x2 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧ (∀ x2 ∈ [(1919 : ℕ), (2036 : ℕ), (3918 : ℕ), (4036 : ℕ), (5917 : ℕ), (6036 : ℕ), (7948 : ℕ), (8068 : ℕ), (10042 : ℕ), (10160 : ℕ), (12042 : ℕ), (14104 : ℕ), (14224 : ℕ), (16136 : ℕ), (16256 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7))) :=
  Exists.elim hCircuitWitness fun x1 h =>
    ⟨x1, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      fun x2 => hCanonWeight x1 x2 h.2.2.2.1 (h.2.2.2.2.2.2 x2)⟩
