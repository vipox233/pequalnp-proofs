import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17401_2
    (hEmptyGates :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));
        have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x4 x5 : Finset (Fin (13 : ℕ))) => {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ x8 ∈ x5, x7 = Fin.natAdd (13 : ℕ) x8)) x6 = Bool.true};
        (x1.WellFormed ∧
          x1.size ≤ (50 : ℕ) ∧
          x1.outVars = ∅ ∧
          x1.outGates = ∅ ∧
          (∀ (x6 x7 : Fin (13 : ℕ)), x3 x6 x7 → x1.eval (x4 {x6} {x7}) = Bool.false) ∧
          (∀ (x7 x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∈ x7, ∀ x11 ∈ x8, ¬x3 x9 x11) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x3 x11 x10}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x3 x11 x12}.card ≤ (2 : ℕ)) → x1.eval (x4 x7 x8) = Bool.true) ∧
          (∀ (x8 : Fin x1.size) (x9 : Bool),
            ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)),
              x3 x10 x11 ∧
                have x12 : Finset (Fin (27 : ℕ)) := x4 {x10} {x11};
                PEqualNP.AndCount.AndCountCircuit.sideTrue x12 (x1.leftVars x8) (x1.leftGates x8) x8 (x1.gateVal x12) = x9 ∧ PEqualNP.AndCount.AndCountCircuit.sideTrue x12 (x1.rightVars x8) (x1.rightGates x8) x8 (x1.gateVal x12) = !x9)) →
        False)
    (hNonEmptyGates :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));
        have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x4 x5 : Finset (Fin (13 : ℕ))) => {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ x8 ∈ x5, x7 = Fin.natAdd (13 : ℕ) x8)) x6 = Bool.true};
        (x1.WellFormed ∧
          x1.size ≤ (50 : ℕ) ∧
          x1.outVars = ∅ ∧
          x1.outGates.Nonempty ∧
          (∀ (x6 x7 : Fin (13 : ℕ)), x3 x6 x7 → x1.eval (x4 {x6} {x7}) = Bool.false) ∧
          (∀ (x7 x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∈ x7, ∀ x11 ∈ x8, ¬x3 x9 x11) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x3 x11 x10}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x3 x11 x12}.card ≤ (2 : ℕ)) → x1.eval (x4 x7 x8) = Bool.true) ∧
          (∀ (x8 : Fin x1.size) (x9 : Bool),
            ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)),
              x3 x10 x11 ∧
                have x12 : Finset (Fin (27 : ℕ)) := x4 {x10} {x11};
                PEqualNP.AndCount.AndCountCircuit.sideTrue x12 (x1.leftVars x8) (x1.leftGates x8) x8 (x1.gateVal x12) = x9 ∧ PEqualNP.AndCount.AndCountCircuit.sideTrue x12 (x1.rightVars x8) (x1.rightGates x8) x8 (x1.gateVal x12) = !x9)) →
        False) :
    (∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),   x1.WellFormed →     let x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x3 x4 : Fin (13 : ℕ)) => x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ));     have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Finset (Fin (27 : ℕ)) := fun (x4 x5 : Finset (Fin (13 : ℕ))) => {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x8 ∈ x4, x7 = Fin.castAdd (13 : ℕ) x8) ∨ ∃ x8 ∈ x5, x7 = Fin.natAdd (13 : ℕ) x8)) x6 = Bool.true};     x1.outVars = ∅ →       (∀ (x6 x7 : Fin (13 : ℕ)), x3 x6 x7 → x1.eval (x4 {x6} {x7}) = Bool.false) →         (∀ (x7 x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∈ x7, ∀ x11 ∈ x8, ¬x3 x9 x11) → (∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x7 | x3 x11 x10}.card ≤ (2 : ℕ)) → (∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x8 | x3 x11 x12}.card ≤ (2 : ℕ)) → x1.eval (x4 x7 x8) = Bool.true) →           (∀ (x8 : Fin x1.size) (x9 : Bool),               ∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)),                 x3 x10 x11 ∧                   have x12 : Finset (Fin (27 : ℕ)) := x4 {x10} {x11};                   PEqualNP.AndCount.AndCountCircuit.sideTrue x12 (x1.leftVars x8) (x1.leftGates x8) x8 (x1.gateVal x12) = x9 ∧ PEqualNP.AndCount.AndCountCircuit.sideTrue x12 (x1.rightVars x8) (x1.rightGates x8) x8 (x1.gateVal x12) = !x9) →             (51 : ℕ) ≤ x1.size) :=
  fun x1 hWF hOutV hF hT hSide =>
    Or.elim (Nat.lt_or_ge x1.size (51 : ℕ))
      (fun hLt =>
        False.elim
          (Or.elim (Finset.eq_empty_or_nonempty x1.outGates)
            (fun hE => hEmptyGates x1 ⟨hWF, Nat.le_of_lt_succ hLt, hOutV, hE, hF, hT, hSide⟩)
            (fun hNE => hNonEmptyGates x1 ⟨hWF, Nat.le_of_lt_succ hLt, hOutV, hNE, hF, hT, hSide⟩)))
      id
