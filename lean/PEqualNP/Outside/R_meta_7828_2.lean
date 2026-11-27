import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7828_2
    (hOutVarsEmpty :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        x1.WellFormed →
        x1.size ≤ (50 : ℕ) →
        x1.outVars = ∅ →
        have x4 : ℕ → Fin (13 : ℕ) → Finset (Fin (27 : ℕ)) := fun (x4 : ℕ) (x5 : Fin (13 : ℕ)) => {x6 : Fin (27 : ℕ) | ↑x6 = (0 : ℕ) ∨ x4.testBit (((↑x6 - (1 : ℕ)) % (13 : ℕ) + (13 : ℕ) - ↑x5) % (13 : ℕ) + (13 : ℕ) * ((↑x6 - (1 : ℕ)) / (13 : ℕ))) = Bool.false};
        have x5 : Fin (52 : ℕ) → Finset (Fin (27 : ℕ)) := fun (x5 : Fin (52 : ℕ)) => x4 ([(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ)].getD (↑x5 / (13 : ℕ)) (0 : ℕ)) (Fin.ofNat (13 : ℕ) ↑x5);
        have x6 : List ℕ := [(61888 : ℕ), (92576 : ℕ), (162112 : ℕ), (177472 : ℕ), (192832 : ℕ), (208132 : ℕ), (308368 : ℕ), (339076 : ℕ), (408580 : ℕ), (470020 : ℕ), (555296 : ℕ), (570640 : ℕ), (601376 : ℕ), (616736 : ℕ), (670976 : ℕ), (686336 : ℕ), (701696 : ℕ), (732416 : ℕ), (801808 : ℕ), (832528 : ℕ), (932864 : ℕ), (1079392 : ℕ), (1194052 : ℕ), (1210432 : ℕ), (1325076 : ℕ), (1456132 : ℕ), (1603616 : ℕ), (1849360 : ℕ), (2172068 : ℕ), (2241604 : ℕ), (2274368 : ℕ), (2405504 : ℕ), (2434180 : ℕ), (2503684 : ℕ), (3289156 : ℕ), (4532356 : ℕ)];
        (∀ (x8 : Fin (52 : ℕ)), x1.eval (x5 x8) = Bool.false) →
        (∀ (x9 : Fin (36 : ℕ)) (x10 : Fin (13 : ℕ)), x1.eval (x4 (x6.getD ↑x9 (0 : ℕ)) x10) = Bool.true) →
        (∃ (x10 : Fin (4 : ℕ)) (x11 : Finset (Fin x1.size)), (∀ (x12 : Fin x1.size), x12 ∈ x11 ↔ x1.gateVal (x4 ([(7405575 : ℕ), (59244600 : ℕ), (33916544 : ℕ), (162112 : ℕ)].getD ↑x10 (0 : ℕ)) (0 : Fin (13 : ℕ))) x12 = Bool.true) ∧ (18 : ℕ) ≤ x11.card ∧ x11.card < x1.size) →
        False)
    (hOutVarsNonempty :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        x1.WellFormed →
        x1.size ≤ (50 : ℕ) →
        (∃ (v : Fin (27 : ℕ)), v ∈ x1.outVars) →
        have x4 : ℕ → Fin (13 : ℕ) → Finset (Fin (27 : ℕ)) := fun (x4 : ℕ) (x5 : Fin (13 : ℕ)) => {x6 : Fin (27 : ℕ) | ↑x6 = (0 : ℕ) ∨ x4.testBit (((↑x6 - (1 : ℕ)) % (13 : ℕ) + (13 : ℕ) - ↑x5) % (13 : ℕ) + (13 : ℕ) * ((↑x6 - (1 : ℕ)) / (13 : ℕ))) = Bool.false};
        have x5 : Fin (52 : ℕ) → Finset (Fin (27 : ℕ)) := fun (x5 : Fin (52 : ℕ)) => x4 ([(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ)].getD (↑x5 / (13 : ℕ)) (0 : ℕ)) (Fin.ofNat (13 : ℕ) ↑x5);
        (∀ (x8 : Fin (52 : ℕ)), x1.eval (x5 x8) = Bool.false) →
        False) :
    (∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),   x1.WellFormed →     x1.size ≤ (50 : ℕ) →       have x4 : ℕ → Fin (13 : ℕ) → Finset (Fin (27 : ℕ)) := fun (x4 : ℕ) (x5 : Fin (13 : ℕ)) => {x6 : Fin (27 : ℕ) | ↑x6 = (0 : ℕ) ∨ x4.testBit (((↑x6 - (1 : ℕ)) % (13 : ℕ) + (13 : ℕ) - ↑x5) % (13 : ℕ) + (13 : ℕ) * ((↑x6 - (1 : ℕ)) / (13 : ℕ))) = Bool.false};       have x5 : Fin (52 : ℕ) → Finset (Fin (27 : ℕ)) := fun (x5 : Fin (52 : ℕ)) => x4 ([(8193 : ℕ), (8194 : ℕ), (8200 : ℕ), (8704 : ℕ)].getD (↑x5 / (13 : ℕ)) (0 : ℕ)) (Fin.ofNat (13 : ℕ) ↑x5);       have x6 : List ℕ :=         have x6 : List ℕ :=           have x6 : List ℕ :=             have x6 : List ℕ := [(2405504 : ℕ), (2434180 : ℕ), (2503684 : ℕ), (3289156 : ℕ), (4532356 : ℕ)];             (1849360 : ℕ) :: (2172068 : ℕ) :: (2241604 : ℕ) :: (2274368 : ℕ) :: x6;           have x7 : List ℕ := (1194052 : ℕ) :: (1210432 : ℕ) :: (1325076 : ℕ) :: (1456132 : ℕ) :: (1603616 : ℕ) :: x6;           (801808 : ℕ) :: (832528 : ℕ) :: (932864 : ℕ) :: (1079392 : ℕ) :: x7;         have x7 : List ℕ :=           have x7 : List ℕ := (616736 : ℕ) :: (670976 : ℕ) :: (686336 : ℕ) :: (701696 : ℕ) :: (732416 : ℕ) :: x6;           (470020 : ℕ) :: (555296 : ℕ) :: (570640 : ℕ) :: (601376 : ℕ) :: x7;         have x8 : List ℕ := (192832 : ℕ) :: (208132 : ℕ) :: (308368 : ℕ) :: (339076 : ℕ) :: (408580 : ℕ) :: x7;         (61888 : ℕ) :: (92576 : ℕ) :: (162112 : ℕ) :: (177472 : ℕ) :: x8;       have x7 : List ℕ := [(7405575 : ℕ), (59244600 : ℕ), (33916544 : ℕ), (162112 : ℕ)];       (∀ (x8 : Fin (52 : ℕ)), x1.eval (x5 x8) = Bool.false) → (∀ (x9 : Fin (36 : ℕ)) (x10 : Fin (13 : ℕ)), x1.eval (x4 (x6.getD ↑x9 (0 : ℕ)) x10) = Bool.true) → (∃ (x10 : Fin (4 : ℕ)) (x11 : Finset (Fin x1.size)), (∀ (x12 : Fin x1.size), x12 ∈ x11 ↔ x1.gateVal (x4 (x7.getD ↑x10 (0 : ℕ)) (0 : Fin (13 : ℕ))) x12 = Bool.true) ∧ (18 : ℕ) ≤ x11.card ∧ x11.card < x1.size) → False) :=
  fun x1 hWF hSz hNeg hPos hEx =>
    Or.elim (Classical.em (x1.outVars = ∅))
      (fun hEm => hOutVarsEmpty x1 hWF hSz hEm hNeg hPos hEx)
      (fun hNe => hOutVarsNonempty x1 hWF hSz (Finset.nonempty_iff_ne_empty.mpr hNe) hNeg)
