import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18910_2
    (hFullSpec :
      have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2;
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        PEqualNP.MetaComplexity.Monotone2 C ∧
        C.size ≤ (29 : ℕ) ∧
        C.output < (17 : ℕ) + C.size ∧
        w < (17 : ℕ) + C.size ∧
        ∀ (x : Fin (17 : ℕ) → Bool),
          (C.eval (List.ofFn x) = Bool.true ↔ ∃ (u v : Fin (17 : ℕ)), x1 u v = Bool.true ∧ x u = Bool.true ∧ x v = Bool.true) ∧
          (C.eval (List.ofFn x) = Bool.false → (C.wires (List.ofFn x)).getD w Bool.false = (x (15 : Fin (17 : ℕ)) || x (16 : Fin (17 : ℕ)))))
    (hSpecToTests :
      have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
        (∀ (x : Fin (17 : ℕ) → Bool),
          (C.eval (List.ofFn x) = Bool.true ↔ ∃ (u v : Fin (17 : ℕ)), x1 u v = Bool.true ∧ x u = Bool.true ∧ x v = Bool.true) ∧
          (C.eval (List.ofFn x) = Bool.false → (C.wires (List.ofFn x)).getD w Bool.false = (x (15 : Fin (17 : ℕ)) || x (16 : Fin (17 : ℕ))))) →
        (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → C.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧
        (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (C.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD w Bool.false = Bool.true) ∧
        ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),
          (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →
          have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false;
          ∀ (x8 : Fin (17 : ℕ) → Bool),
            (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) →
            (C.wires (List.ofFn x8)).getD (if x4 = Bool.true then w else C.output) Bool.false = Bool.false) :
    (have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (29 : ℕ) ∧       x2.output < (17 : ℕ) + x2.size ∧         x3 < (17 : ℕ) + x2.size ∧           (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → x2.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧             (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (x2.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD x3 Bool.false = Bool.true) ∧               ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),                 (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →                   have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false;                   ∀ (x8 : Fin (17 : ℕ) → Bool), (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) → (x2.wires (List.ofFn x8)).getD (if x4 = Bool.true then x3 else x2.output) Bool.false = Bool.false) :=
  Exists.elim hFullSpec fun C hC =>
    Exists.elim hC fun w hw =>
      ⟨C, w, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
        (hSpecToTests C w hw.2.2.2.2).1,
        (hSpecToTests C w hw.2.2.2.2).2.1,
        (hSpecToTests C w hw.2.2.2.2).2.2⟩
