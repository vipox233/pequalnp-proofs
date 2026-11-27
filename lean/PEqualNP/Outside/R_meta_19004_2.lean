import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_19004_2
    (hSpecAndCount :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        ({j : ℕ | ∃ g : PEqualNP.CircuitLowerBounds.Gate, C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard =
          (C.gates.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [false] && g.op.eval [false, true, false])).length) ∧
        ((∀ (x5 x6 : Finset (Fin 13)),
            C.eval (List.ofFn fun x7 : Fin 26 =>
              if x7.1 < 13 then decide (Fin.ofNat 13 x7.1 ∈ x5) else decide (Fin.ofNat 13 x7.1 ∈ x6)) = true ↔
            ∃ x7 ∈ x5, ∃ x8 ∈ x6, (x7.1 + x8.1) % 13 ∈ [0, 1, 3, 9]) →
          ∀ (x : Fin 26 → Bool),
            C.eval (List.ofFn x) = true ↔
            ∃ (p l : Fin 13), (p.1 + l.1) % 13 ∈ [0, 1, 3, 9] ∧
              x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true))
    (hOrCount51 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        C.output + 1 = 26 + C.gates.length →
        (∃ (ins : List ℕ), C.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := ins }) →
        (∀ (x : Fin 26 → Bool),
          C.eval (List.ofFn x) = true ↔
          ∃ (p l : Fin 13), (p.1 + l.1) % 13 ∈ [0, 1, 3, 9] ∧
            x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) →
        51 ≤ (C.gates.filter (fun g : PEqualNP.CircuitLowerBounds.Gate => !g.op.eval [false] && g.op.eval [false, true, false])).length) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.output + (1 : ℕ) = (26 : ℕ) + x1.gates.length → (∃ (x4 : List ℕ), x1.gates.getLast? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := x4 : PEqualNP.CircuitLowerBounds.Gate }) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), x1.eval (List.ofFn fun (x7 : Fin (26 : ℕ)) => if ↑x7 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x7 ∈ x6)) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → (51 : ℕ) ≤ {x6 : ℕ | ∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) :=
  fun x1 hMono hOut hLast hComp =>
    let hSC := hSpecAndCount x1
    Eq.subst hSC.1.symm (hOrCount51 x1 hMono hOut hLast (hSC.2 hComp))
