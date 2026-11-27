import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18156_2
    (hSingerEq :
      PEqualNP.HeptadCover.singerLines3 =
        fun (l : Fin (13 : ℕ)) => {l, l + (1 : Fin (13 : ℕ)), l + (3 : Fin (13 : ℕ)), l + (9 : Fin (13 : ℕ))})
    (hExplicit :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := fun (l : Fin (13 : ℕ)) => {l, l + (1 : Fin (13 : ℕ)), l + (3 : Fin (13 : ℕ)), l + (9 : Fin (13 : ℕ))};
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>
        have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};
        have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};
        PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ)) ∧ PEqualNP.GenericRejection.IsMaximalFalse x1 x4 x5;
      ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),
        (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧
        have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false]) (List.ofFn x6) (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false;
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 → (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧
        ∀ (x7 x8 : Fin (13 : ℕ) → Bool), x2 x7 x8 → x6 (Fin.append x7 x8) = Bool.false) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>   have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};   have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};   PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ)) ∧ PEqualNP.GenericRejection.IsMaximalFalse x1 x4 x5; ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),   (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧     have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false]) (List.ofFn x6) (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false;     (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 → (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧ ∀ (x7 x8 : Fin (13 : ℕ) → Bool), x2 x7 x8 → x6 (Fin.append x7 x8) = Bool.false) :=
  Eq.subst
    (motive := fun (x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ))) =>
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>
        have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};
        have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};
        PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ)) ∧ PEqualNP.GenericRejection.IsMaximalFalse x1 x4 x5;
      ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),
        (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧
        have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false]) (List.ofFn x6) (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false;
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 → (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧
        ∀ (x7 x8 : Fin (13 : ℕ) → Bool), x2 x7 x8 → x6 (Fin.append x7 x8) = Bool.false)
    hSingerEq.symm hExplicit
