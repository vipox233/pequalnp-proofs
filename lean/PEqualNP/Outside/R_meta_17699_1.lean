import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17699_1
    (hBit2 :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x2 x3 : ℕ),
        have x4 : ℕ → ℕ → Bool := fun (a b : ℕ) => PEqualNP.BlindGate.wireValue x1 (14 : ℕ) (fun (i : Fin (14 : ℕ)) => a.testBit ↑i) b;
        (x4 x5 x2 || x4 x5 (2 : ℕ) && x4 x5 x3) =
          (if x5.testBit (2 : ℕ) = Bool.true then x4 x5 x2 || x4 x5 x3 else x4 x5 x2))
    (hCircuit :
      ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),
        x1.size ≤ (24 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧ (∀ g ∈ x1.gates, g.inputs.Nodup) ∧
        x2 < (14 : ℕ) + x1.size ∧ x3 < (14 : ℕ) + x1.size ∧ x2 ≠ (2 : ℕ) ∧ x2 ≠ x3 ∧
        have x4 : ℕ → ℕ → Bool := fun (a b : ℕ) => PEqualNP.BlindGate.wireValue x1 (14 : ℕ) (fun (i : Fin (14 : ℕ)) => a.testBit ↑i) b;
        (∀ x5 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (258 : ℕ), (260 : ℕ), (272 : ℕ), (516 : ℕ), (520 : ℕ), (544 : ℕ), (1032 : ℕ), (1040 : ℕ), (1088 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)],
          (if x5.testBit (2 : ℕ) = Bool.true then x4 x5 x2 || x4 x5 x3 else x4 x5 x2) = Bool.true) ∧
        (∀ x5 ∈ [(127 : ℕ), (244 : ℕ), (361 : ℕ), (480 : ℕ), (595 : ℕ), (720 : ℕ), (833 : ℕ), (1063 : ℕ), (1188 : ℕ), (1313 : ℕ), (1539 : ℕ), (2126 : ℕ), (2244 : ℕ), (2376 : ℕ), (2626 : ℕ), (3008 : ℕ), (3078 : ℕ), (4125 : ℕ), (4244 : ℕ), (4361 : ℕ), (4625 : ℕ), (5125 : ℕ), (5889 : ℕ), (6156 : ℕ), (7300 : ℕ), (8250 : ℕ), (8368 : ℕ), (8488 : ℕ), (8722 : ℕ), (9250 : ℕ), (9632 : ℕ), (10250 : ℕ), (11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)],
          (if x5.testBit (2 : ℕ) = Bool.true then x4 x5 x2 || x4 x5 x3 else x4 x5 x2) = Bool.false) ∧
        x4 (1 : ℕ) x3 = Bool.false ∧ x4 (128 : ℕ) x3 = Bool.false) :
    (∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),   x1.size ≤ (24 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧         x2 < (14 : ℕ) + x1.size ∧           x3 < (14 : ℕ) + x1.size ∧             x2 ≠ (2 : ℕ) ∧               x2 ≠ x3 ∧                 have x4 : ℕ → ℕ → Bool := fun (x4 x5 : ℕ) => PEqualNP.BlindGate.wireValue x1 (14 : ℕ) (fun (x6 : Fin (14 : ℕ)) => x4.testBit ↑x6) x5;                 (∀ x5 ∈ [(129 : ℕ), (130 : ℕ), (136 : ℕ), (258 : ℕ), (260 : ℕ), (272 : ℕ), (516 : ℕ), (520 : ℕ), (544 : ℕ), (1032 : ℕ), (1040 : ℕ), (1088 : ℕ), (2064 : ℕ), (2080 : ℕ), (2049 : ℕ), (4128 : ℕ), (4160 : ℕ), (4098 : ℕ), (8256 : ℕ), (8193 : ℕ), (8196 : ℕ)], (x4 x5 x2 || x4 x5 (2 : ℕ) && x4 x5 x3) = Bool.true) ∧                   (∀                       x5 ∈                         have x6 : List ℕ :=                           have x6 : List ℕ :=                             have x6 : List ℕ := [(11778 : ℕ), (12312 : ℕ), (12944 : ℕ), (14600 : ℕ), (16256 : ℕ)];                             (8488 : ℕ) :: (8722 : ℕ) :: (9250 : ℕ) :: (9632 : ℕ) :: (10250 : ℕ) :: x6;                           have x7 : List ℕ := (5889 : ℕ) :: (6156 : ℕ) :: (7300 : ℕ) :: (8250 : ℕ) :: (8368 : ℕ) :: x6;                           (4244 : ℕ) :: (4361 : ℕ) :: (4625 : ℕ) :: (5125 : ℕ) :: x7;                         have x7 : List ℕ :=                           have x7 : List ℕ := (2376 : ℕ) :: (2626 : ℕ) :: (3008 : ℕ) :: (3078 : ℕ) :: (4125 : ℕ) :: x6;                           (1313 : ℕ) :: (1539 : ℕ) :: (2126 : ℕ) :: (2244 : ℕ) :: x7;                         have x8 : List ℕ := (595 : ℕ) :: (720 : ℕ) :: (833 : ℕ) :: (1063 : ℕ) :: (1188 : ℕ) :: x7;                         (127 : ℕ) :: (244 : ℕ) :: (361 : ℕ) :: (480 : ℕ) :: x8,                       (x4 x5 x2 || x4 x5 (2 : ℕ) && x4 x5 x3) = Bool.false) ∧                     x4 (1 : ℕ) x3 = Bool.false ∧ x4 (128 : ℕ) x3 = Bool.false) :=
  Exists.elim hCircuit fun x1 h1 =>
    Exists.elim h1 fun x2 h2 =>
      Exists.elim h2 fun x3 h =>
        ⟨x1, x2, x3, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
          fun x5 hx5 => (hBit2 x1 x5 x2 x3).trans (h.2.2.2.2.2.2.2.1 x5 hx5),
          fun x5 hx5 => (hBit2 x1 x5 x2 x3).trans (h.2.2.2.2.2.2.2.2.1 x5 hx5),
          h.2.2.2.2.2.2.2.2.2.1,
          h.2.2.2.2.2.2.2.2.2.2⟩
