import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18520_2
    (hCompileAO2 : ∀ (codes : List (Bool × ℕ × ℕ)),
      codes.length ≤ (22 : ℕ) →
        (∀ (k : ℕ), k < codes.length →
          have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
          g.2.1 ≠ g.2.2 ∧ g.2.1 < (14 : ℕ) + k ∧ g.2.2 < (14 : ℕ) + k) →
          have C : PEqualNP.CircuitLowerBounds.Circuit :=
            ⟨codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (13 : ℕ) + codes.length⟩;
          PEqualNP.TopForm.IsAO2 (14 : ℕ) C ∧ (∀ x2 ∈ C.gates, x2.inputs.Nodup))
    (hCodeWitness : ∃ (codes : List (Bool × ℕ × ℕ)),
      (1 : ℕ) ≤ codes.length ∧
        codes.length ≤ (22 : ℕ) ∧
          (∀ (k : ℕ), k < codes.length →
            have g : Bool × ℕ × ℕ := codes.getD k (Bool.false, (0 : ℕ), (0 : ℕ));
            g.2.1 ≠ g.2.2 ∧ g.2.1 < (14 : ℕ) + k ∧ g.2.2 < (14 : ℕ) + k) ∧
            have C : PEqualNP.CircuitLowerBounds.Circuit :=
              ⟨codes.map (fun (g : Bool × ℕ × ℕ) => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (13 : ℕ) + codes.length⟩;
            (∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) → x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → C.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧
              ∀ x2 ∈ [(127 : ℕ), (244 : ℕ), (361 : ℕ), (480 : ℕ), (595 : ℕ), (720 : ℕ), (833 : ℕ), (1063 : ℕ), (1188 : ℕ), (1313 : ℕ), (1539 : ℕ), (2126 : ℕ), (2244 : ℕ), (2376 : ℕ), (2626 : ℕ), (3008 : ℕ), (3078 : ℕ), (4125 : ℕ), (4244 : ℕ), (4361 : ℕ), (4625 : ℕ), (5125 : ℕ), (5889 : ℕ), (6156 : ℕ), (7300 : ℕ), (8250 : ℕ), (8368 : ℕ), (8488 : ℕ), (8722 : ℕ), (9250 : ℕ), (9632 : ℕ), (10250 : ℕ), (11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)],
                C.eval (List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) = Bool.false) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (22 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (∀ x2 ∈ x1.gates, x2.inputs.Nodup) ∧         (14 : ℕ) ≤ x1.output ∧           x1.output < (14 : ℕ) + x1.size ∧             (∀ (x2 x3 : Fin (7 : ℕ)), x3 ≠ (1 : Fin (7 : ℕ)) → x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x2 ∨ x6 = Fin.natAdd (7 : ℕ) x3)) = Bool.true) ∧               ∀                 x2 ∈                   have x3 : List ℕ :=                     have x3 : List ℕ :=                       have x3 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];                       (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x3;                     have x4 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x3;                     (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x4;                   have x4 : List ℕ :=                     have x4 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x3;                     (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x4;                   have x5 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x4;                   (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x5,                 x1.eval (List.ofFn fun (x4 : Fin (14 : ℕ)) => x2.testBit ↑x4) = Bool.false :=
  Exists.elim hCodeWitness fun codes h =>
    let C : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨codes.map (fun g => ⟨if g.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.and, [g.2.1, g.2.2]⟩), (13 : ℕ) + codes.length⟩
    let hc := hCompileAO2 codes h.2.1 h.2.2.1
    have hsz : C.size = codes.length := List.length_map _
    ⟨C, hsz ▸ h.2.1, hc.1, hc.2, Nat.add_le_add_left h.1 (13 : ℕ), hsz.symm ▸ Nat.add_lt_add_right (Nat.lt_succ_self (13 : ℕ)) codes.length, h.2.2.2.1, h.2.2.2.2⟩
