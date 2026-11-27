import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17719_1
    (hPadEquiv :
      ∀ (x2 : ℕ) (b : Bool),
        ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) b) =
          List.ofFn (fun (i : Fin (25 : ℕ)) => if ↑i < (14 : ℕ) then x2.testBit ↑i else b))
    (hCircuit :
      have inp : ℕ → Bool → List Bool := fun x2 b =>
        List.ofFn (fun (i : Fin (25 : ℕ)) => if ↑i < (14 : ℕ) then x2.testBit ↑i else b);
      have oA := PEqualNP.CircuitLowerBounds.GateOp.and;
      have oO := PEqualNP.CircuitLowerBounds.GateOp.or;
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate),
          x1.gates[x2]? = Option.some x3 →
          (x3.op = oA ∨ x3.op = oO) ∧
          ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧
        (∀ x2 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)],
          x1.eval (inp x2 Bool.false) = Bool.true) ∧
        (∀ x2 ∈ [(1919 : ℕ), (2036 : ℕ), (3918 : ℕ), (4036 : ℕ), (5917 : ℕ), (6036 : ℕ), (7948 : ℕ), (8068 : ℕ), (10042 : ℕ), (10160 : ℕ), (12042 : ℕ), (14104 : ℕ), (14224 : ℕ), (16136 : ℕ), (16256 : ℕ)],
          x1.eval (inp x2 Bool.true) = Bool.false) ∧
        ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ),
          x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧
          x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧
          (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧
          (2 : ℕ) ≤ x3 x1.output ∧
          ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ),
            (x1.gates[x4]? = Option.some x5 ∧ x5.inputs = [x6, x7]) →
            (x5.op = oA → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧
            (x5.op = oO → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7))) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ x2 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.false) = Bool.true) ∧ (∀ x2 ∈ [(1919 : ℕ), (2036 : ℕ), (3918 : ℕ), (4036 : ℕ), (5917 : ℕ), (6036 : ℕ), (7948 : ℕ), (8068 : ℕ), (10042 : ℕ), (10160 : ℕ), (12042 : ℕ), (14104 : ℕ), (14224 : ℕ), (16136 : ℕ), (16256 : ℕ)], x1.eval ((List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) ++ List.replicate (11 : ℕ) Bool.true) = Bool.false) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7))) :=
  Exists.elim hCircuit fun x1 h =>
    ⟨x1, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      fun x2 hx2 => (congrArg x1.eval (hPadEquiv x2 Bool.false)).trans (h.2.2.2.2.1 x2 hx2),
      fun x2 hx2 => (congrArg x1.eval (hPadEquiv x2 Bool.true)).trans (h.2.2.2.2.2.1 x2 hx2),
      fun x2 => Exists.elim (h.2.2.2.2.2.2 x2) fun x3 hx3 =>
        ⟨x3, hx3.1, hx3.2.1, hx3.2.2.1, hx3.2.2.2.1, fun x4 x5 x6 x7 hg hi => hx3.2.2.2.2 x4 x5 x6 x7 ⟨hg, hi⟩⟩⟩
