import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7959_1
    (hCompile :
      ∀ (prog : List (Bool × ℕ × ℕ)),
        prog.length = (63 : ℕ) →
        ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),
          (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧
          ∀ (init : List Bool),
            init.length = (26 : ℕ) →
            (List.foldl
              (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) =>
                x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false])
              init (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false =
            (List.foldl
              (fun (x7 : List Bool) (x8 : Bool × ℕ × ℕ) =>
                x7 ++ [bif x8.1 then x7.getD (x8.2.1 % x7.length) Bool.false && x7.getD (x8.2.2 % x7.length) Bool.false else x7.getD (x8.2.1 % x7.length) Bool.false || x7.getD (x8.2.2 % x7.length) Bool.false])
              init prog).getD (88 : ℕ) Bool.false)
    (hProg :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>
        have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};
        have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};
        PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧
        (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧
        ∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ);
      ∃ (prog : List (Bool × ℕ × ℕ)),
        prog.length = (63 : ℕ) ∧
        have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) =>
          (List.foldl
            (fun (x7 : List Bool) (x8 : Bool × ℕ × ℕ) =>
              x7 ++ [bif x8.1 then x7.getD (x8.2.1 % x7.length) Bool.false && x7.getD (x8.2.2 % x7.length) Bool.false else x7.getD (x8.2.1 % x7.length) Bool.false || x7.getD (x8.2.2 % x7.length) Bool.false])
            (List.ofFn x6) prog).getD (88 : ℕ) Bool.false;
        (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 →
          (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧
        ∀ (x7 x8 : Fin (13 : ℕ) → Bool), x2 x7 x8 → x6 (Fin.append x7 x8) = Bool.false) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>   have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};   have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};   PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧ ∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ); ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),   (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧     have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false]) (List.ofFn x6) (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false;     (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 → (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧ ∀ (x7 x8 : Fin (13 : ℕ) → Bool), x2 x7 x8 → x6 (Fin.append x7 x8) = Bool.false) :=
  Exists.elim hProg fun prog hP =>
    Exists.elim (hCompile prog hP.1) fun x3 h1 =>
      Exists.elim h1 fun x4 h2 =>
        Exists.elim h2 fun x5 hC =>
          ⟨x3, x4, x5, hC.1,
            fun x7 x8 h => (hC.2 _ (List.length_ofFn ..)).trans (hP.2.1 x7 x8 h),
            fun x7 x8 h => (hC.2 _ (List.length_ofFn ..)).trans (hP.2.2 x7 x8 h)⟩
