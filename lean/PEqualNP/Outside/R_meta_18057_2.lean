import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18057_2
    (hCase67 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),
        have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;
        (↑x2 < (4 : ℕ) ∧
          PEqualNP.MetaComplexity.Monotone2 x1 ∧
          x1.size ≤ (124 : ℕ) ∧
          (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ (fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) x5) ∧
          x7 (148193411399 : ℕ) ∧
          x7 x6 ∧
          (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | ((Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x11.op) x1.gates[x10]?).getD Bool.false && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card) →
        ∃ (x12 : (x12 : Fin (67 : ℕ)) → Fin (x1.size - ↑x12)) (x13 : Fin (67 : ℕ) → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin (67 : ℕ)) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange (67 : ℕ))).eval (List.ofFn x14) = x1.eval (List.ofFn x14))
    (hCase72 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),
        have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;
        ((4 : ℕ) ≤ ↑x2 ∧ ↑x2 < (9 : ℕ) ∧
          PEqualNP.MetaComplexity.Monotone2 x1 ∧
          x1.size ≤ (124 : ℕ) ∧
          (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ (fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) x5) ∧
          x7 (148193411399 : ℕ) ∧
          x7 x6 ∧
          (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | ((Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x11.op) x1.gates[x10]?).getD Bool.false && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card) →
        ∃ (x12 : (x12 : Fin (72 : ℕ)) → Fin (x1.size - ↑x12)) (x13 : Fin (72 : ℕ) → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin (72 : ℕ)) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange (72 : ℕ))).eval (List.ofFn x14) = x1.eval (List.ofFn x14))
    (hCase76 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),
        have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);
        have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;
        ((9 : ℕ) ≤ ↑x2 ∧
          PEqualNP.MetaComplexity.Monotone2 x1 ∧
          x1.size ≤ (124 : ℕ) ∧
          (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ (fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) x5) ∧
          x7 (148193411399 : ℕ) ∧
          x7 x6 ∧
          (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | ((Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x11.op) x1.gates[x10]?).getD Bool.false && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card) →
        ∃ (x12 : (x12 : Fin (76 : ℕ)) → Fin (x1.size - ↑x12)) (x13 : Fin (76 : ℕ) → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin (76 : ℕ)) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange (76 : ℕ))).eval (List.ofFn x14) = x1.eval (List.ofFn x14)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (14 : ℕ)),   PEqualNP.MetaComplexity.Monotone2 x1 →     x1.size ≤ (124 : ℕ) →       (∀ (x5 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x5) = Bool.true ↔ (fun (x6 : Fin (42 : ℕ) → Bool) => ∃ (x7 : Fin (42 : ℕ)) (x8 : Fin (42 : ℕ)), (↑x7 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x8 ∧ (↑x8 + (21 : ℕ) - ↑x7) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x6 x7 = Bool.true ∧ x6 x8 = Bool.true) x5) →         have x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ);         have x7 : ℕ → Prop := fun (x7 : ℕ) => ∃ (x8 : ℕ), PEqualNP.ReadTwo.isAnd x1 x8 ∧ (PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x8 fun (x9 : Fin (42 : ℕ)) => x7.testBit ↑x9) = Bool.true;         x7 (148193411399 : ℕ) →           x7 x6 →             (33 : ℕ) ≤ {x10 ∈ Finset.range x1.size | ((Option.map (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.true Bool.false (fun (_ : ℕ) => Bool.false) Bool.false x11.op) x1.gates[x10]?).getD Bool.false && !PEqualNP.EdgeOwnership.gateVal (42 : ℕ) x1 x10 fun (x11 : Fin (42 : ℕ)) => x6.testBit ↑x11) = Bool.true}.card →               have x11 : ℕ := if ↑x2 < (4 : ℕ) then (67 : ℕ) else if ↑x2 < (9 : ℕ) then (72 : ℕ) else (76 : ℕ);               ∃ (x12 : (x12 : Fin x11) → Fin (x1.size - ↑x12)) (x13 : Fin x11 → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin x11) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange x11)).eval (List.ofFn x14) = x1.eval (List.ofFn x14)) :=
  fun x1 x2 hM hSz hComp hA1 hA2 hCard =>
    let x6 : ℕ := [(693637218693 : ℕ), (214750724172 : ℕ), (43100670213 : ℕ), (2201724715076 : ℕ), (429513539622 : ℕ), (10838245382 : ℕ), (214756769811 : ℕ), (412337856832 : ℕ), (154640061441 : ℕ), (1718003696225 : ℕ), (1387274437386 : ℕ), (3436007392450 : ℕ), (3436108316976 : ℕ), (1168315262978 : ℕ)].getD ↑x2 (0 : ℕ)
    Or.elim (Nat.lt_or_ge x2.val (4 : ℕ))
      (fun hLt4 =>
        Eq.subst
          (motive := fun m => ∃ (x12 : (x12 : Fin m) → Fin (x1.size - ↑x12)) (x13 : Fin m → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin m) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange m)).eval (List.ofFn x14) = x1.eval (List.ofFn x14))
          (ite_eq_left hLt4).symm
          (hCase67 x1 x2 ⟨hLt4, hM, hSz, hComp, hA1, hA2, hCard⟩))
      (fun hGe4 =>
        Or.elim (Nat.lt_or_ge x2.val (9 : ℕ))
          (fun hLt9 =>
            Eq.subst
              (motive := fun m => ∃ (x12 : (x12 : Fin m) → Fin (x1.size - ↑x12)) (x13 : Fin m → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin m) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange m)).eval (List.ofFn x14) = x1.eval (List.ofFn x14))
              (Eq.trans (ite_eq_right (Nat.not_lt.mpr hGe4)) (ite_eq_left hLt9)).symm
              (hCase72 x1 x2 ⟨hGe4, hLt9, hM, hSz, hComp, hA1, hA2, hCard⟩))
          (fun hGe9 =>
            Eq.subst
              (motive := fun m => ∃ (x12 : (x12 : Fin m) → Fin (x1.size - ↑x12)) (x13 : Fin m → ℕ), ∀ (x14 : Fin (42 : ℕ) → Bool), (∀ (x15 : Fin (42 : ℕ)), ((148193411399 : ℕ) ||| x6).testBit ↑x15 = Bool.true → x14 x15 = Bool.false) → (List.foldl (fun (x16 : PEqualNP.CircuitLowerBounds.Circuit) (x17 : Fin m) => PEqualNP.CircuitMoves.eraseGate (42 : ℕ) x16 (↑(x12 x17)) (x13 x17)) x1 (List.finRange m)).eval (List.ofFn x14) = x1.eval (List.ofFn x14))
              (Eq.trans (ite_eq_right (Nat.not_lt.mpr hGe4)) (ite_eq_right (Nat.not_lt.mpr hGe9))).symm
              (hCase76 x1 x2 ⟨hGe9, hM, hSz, hComp, hA1, hA2, hCard⟩)))
