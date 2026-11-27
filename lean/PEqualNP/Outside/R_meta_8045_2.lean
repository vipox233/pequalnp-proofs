import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8045_2
    (hEmptyOut :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        (x1.WellFormed ∧
          x1.size ≤ (50 : ℕ) ∧
          x1.outVars = ∅ ∧
          (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → x1.eval {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) x6 = Bool.true} = Bool.false) ∧
          (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin (13 : ℕ)) => {x6, x6 + (1 : Fin (13 : ℕ)), x6 + (3 : Fin (13 : ℕ)), x6 + (9 : Fin (13 : ℕ))}) x4 x5 → PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin (13 : ℕ)) => {x7, x7 + (1 : Fin (13 : ℕ)), x7 + (3 : Fin (13 : ℕ)), x7 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x4 x5 → x1.eval {x8 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x9 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x10 ∈ x4, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ x10 ∈ x5, x9 = Fin.natAdd (13 : ℕ) x10)) x8 = Bool.true} = Bool.true)) →
        False)
    (hNonEmptyOut :
      ∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)),
        (x1.WellFormed ∧
          x1.size ≤ (50 : ℕ) ∧
          x1.outVars.Nonempty ∧
          (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → x1.eval {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) x6 = Bool.true} = Bool.false) ∧
          (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin (13 : ℕ)) => {x6, x6 + (1 : Fin (13 : ℕ)), x6 + (3 : Fin (13 : ℕ)), x6 + (9 : Fin (13 : ℕ))}) x4 x5 → PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin (13 : ℕ)) => {x7, x7 + (1 : Fin (13 : ℕ)), x7 + (3 : Fin (13 : ℕ)), x7 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x4 x5 → x1.eval {x8 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x9 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x10 ∈ x4, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ x10 ∈ x5, x9 = Fin.natAdd (13 : ℕ) x10)) x8 = Bool.true} = Bool.true)) →
        False) :
    (∀ (x1 : PEqualNP.AndCount.AndCountCircuit (27 : ℕ)), x1.WellFormed → (∀ (x3 x4 : Fin (13 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (13 : ℕ)) ∨ x3 = x4 + (3 : Fin (13 : ℕ)) ∨ x3 = x4 + (9 : Fin (13 : ℕ)) → x1.eval {x6 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x7 : Fin (26 : ℕ)) => !Decidable.decide (x7 = Fin.castAdd (13 : ℕ) x3 ∨ x7 = Fin.natAdd (13 : ℕ) x4)) x6 = Bool.true} = Bool.false) → (∀ (x4 x5 : Finset (Fin (13 : ℕ))), PEqualNP.GenericRejection.IsMaximalFalse (fun (x6 : Fin (13 : ℕ)) => {x6, x6 + (1 : Fin (13 : ℕ)), x6 + (3 : Fin (13 : ℕ)), x6 + (9 : Fin (13 : ℕ))}) x4 x5 → PEqualNP.GenericRejection.IsGeneric (fun (x7 : Fin (13 : ℕ)) => {x7, x7 + (1 : Fin (13 : ℕ)), x7 + (3 : Fin (13 : ℕ)), x7 + (9 : Fin (13 : ℕ))}) (3 : ℕ) x4 x5 → x1.eval {x8 : Fin (27 : ℕ) | Fin.cases Bool.true (fun (x9 : Fin (26 : ℕ)) => !Decidable.decide ((∃ x10 ∈ x4, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ x10 ∈ x5, x9 = Fin.natAdd (13 : ℕ) x10)) x8 = Bool.true} = Bool.true) → (51 : ℕ) ≤ x1.size) :=
  fun x1 hWF hF hT =>
    Or.elim (Nat.lt_or_ge x1.size (51 : ℕ))
      (fun hLt =>
        False.elim
          (Or.elim (Finset.eq_empty_or_nonempty x1.outVars)
            (fun hE => hEmptyOut x1 ⟨hWF, Nat.le_of_lt_succ hLt, hE, hF, hT⟩)
            (fun hNE => hNonEmptyOut x1 ⟨hWF, Nat.le_of_lt_succ hLt, hNE, hF, hT⟩)))
      id
