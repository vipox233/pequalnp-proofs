import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18514_2
    (hDiffEquiv :
      ∀ (a b : Fin (7 : ℕ)),
        ↑(a - b) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] ↔
          (a = b ∨ a = b + (1 : Fin (7 : ℕ)) ∨ a = b + (3 : Fin (7 : ℕ))))
    (hCircuitDiff :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ (27 : ℕ) ∧
        (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧
        (∀ (x2 x3 : Fin (7 : ℕ)), ↑(x2 - x3) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ)] → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧
        (∀ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∀ (x4 : Fin (7 : ℕ)), x1.eval (List.ofFn fun (x5 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases (fun (x6 : Fin (7 : ℕ)) => x2.testBit ↑(x6 + x4)) (fun (x6 : Fin (7 : ℕ)) => x2.testBit ((7 : ℕ) + ↑(x6 + x4))) x5) = Bool.false) ∧
        (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (14 : ℕ) [(0 : ℕ), (7 : ℕ)] (0 : ℕ)).getD x1.output Option.none).getD (2 : ℕ) ∧
        (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (14 : ℕ) [(0 : ℕ), (7 : ℕ)] (7 : ℕ)).getD x1.output Option.none).getD (2 : ℕ)) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (27 : ℕ) ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (14 : ℕ) + x2 ∧ x6 < (14 : ℕ) + x2) ∧ (∀ (x2 x3 : Fin (7 : ℕ)), x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x5 : Fin (14 : ℕ)) => Decidable.decide (x5 = Fin.castAdd (7 : ℕ) x2 ∨ x5 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧ (∀ x2 ∈ [(127 : ℕ), (244 : ℕ), (480 : ℕ), (720 : ℕ), (1188 : ℕ), (3008 : ℕ), (16256 : ℕ)], ∀ (x4 : Fin (7 : ℕ)), x1.eval (List.ofFn fun (x5 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases (fun (x6 : Fin (7 : ℕ)) => x2.testBit ↑(x6 + x4)) (fun (x6 : Fin (7 : ℕ)) => x2.testBit ((7 : ℕ) + ↑(x6 + x4))) x5) = Bool.false) ∧ ∀ x2 ∈ [(0 : ℕ), (7 : ℕ)], (2 : ℕ) ≤ ((PEqualNP.ReadK.scalarMults x1 (14 : ℕ) [(0 : ℕ), (7 : ℕ)] x2).getD x1.output Option.none).getD (2 : ℕ)) :=
  Exists.elim hCircuitDiff fun x1 hP =>
    ⟨x1, hP.1, hP.2.1,
      fun x2 x3 h => hP.2.2.1 x2 x3 ((hDiffEquiv x2 x3).mpr h),
      hP.2.2.2.1,
      fun _ hx2 =>
        Or.elim (List.mem_cons.mp hx2)
          (fun h0 => h0.symm ▸ hP.2.2.2.2.1)
          (fun h1 =>
            Or.elim (List.mem_cons.mp h1)
              (fun h7 => h7.symm ▸ hP.2.2.2.2.2)
              (fun hnil => False.elim (List.not_mem_nil hnil)))⟩
