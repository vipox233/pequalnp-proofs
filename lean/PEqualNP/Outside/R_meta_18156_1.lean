import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18156_1
    (hOvalSound :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      ∀ (P L : Fin (13 : ℕ) → Bool),
        have X : Finset (Fin (13 : ℕ)) := Finset.univ.filter fun p : Fin (13 : ℕ) => P p = Bool.true;
        have Y : Finset (Fin (13 : ℕ)) := Finset.univ.filter fun l : Fin (13 : ℕ) => L l = Bool.true;
        PEqualNP.GenericRejection.IsFalseInput x1 X Y →
        (∀ (l : Fin (13 : ℕ)), (Finset.filter (fun p : Fin (13 : ℕ) => P p = Bool.true) (x1 l)).card ≤ (2 : ℕ)) →
        (∀ (p : Fin (13 : ℕ)), (Finset.filter (fun l : Fin (13 : ℕ) => p ∈ x1 l) Y).card ≤ (2 : ℕ)) →
        PEqualNP.GenericRejection.IsMaximalFalse x1 X Y →
        (∀ (p l : Fin (13 : ℕ)), P p = Bool.true → L l = Bool.true → p ∉ x1 l) ∧
        X.card + Y.card = (7 : ℕ) ∧ (3 : ℕ) ≤ X.card ∧ X.card ≤ (4 : ℕ))
    (hOvalCircuit :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),
        (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧
          have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) =>
            (List.foldl (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) =>
              x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false])
              (List.ofFn x6) (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false;
          (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 →
            (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧
          ∀ (x7 x8 : Fin (13 : ℕ) → Bool),
            have X : Finset (Fin (13 : ℕ)) := Finset.univ.filter fun p : Fin (13 : ℕ) => x7 p = Bool.true;
            have Y : Finset (Fin (13 : ℕ)) := Finset.univ.filter fun l : Fin (13 : ℕ) => x8 l = Bool.true;
            (∀ (p l : Fin (13 : ℕ)), x7 p = Bool.true → x8 l = Bool.true → p ∉ x1 l) →
            X.card + Y.card = (7 : ℕ) →
            (3 : ℕ) ≤ X.card →
            X.card ≤ (4 : ℕ) →
            x6 (Fin.append x7 x8) = Bool.false) :
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → Prop := fun (x2 x3 : Fin (13 : ℕ) → Bool) =>   have x4 : Finset (Fin (13 : ℕ)) := {x4 : Fin (13 : ℕ) | x2 x4 = Bool.true};   have x5 : Finset (Fin (13 : ℕ)) := {x5 : Fin (13 : ℕ) | x3 x5 = Bool.true};   PEqualNP.GenericRejection.IsFalseInput x1 x4 x5 ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x1 x6 | x2 x7 = Bool.true}.card ≤ (2 : ℕ)) ∧ (∀ (x6 : Fin (13 : ℕ)), {x7 ∈ x5 | x6 ∈ x1 x7}.card ≤ (2 : ℕ)) ∧ PEqualNP.GenericRejection.IsMaximalFalse x1 x4 x5; ∃ (x3 : Fin (63 : ℕ) → Bool) (x4 : Fin (63 : ℕ) → Fin (89 : ℕ)) (x5 : Fin (63 : ℕ) → Fin (89 : ℕ)),   (∀ (x6 : Fin (63 : ℕ)), ↑(x4 x6) < (26 : ℕ) + ↑x6 ∧ ↑(x5 x6) < (26 : ℕ) + ↑x6 ∧ x4 x6 ≤ x5 x6) ∧     have x6 : (Fin (26 : ℕ) → Bool) → Bool := fun (x6 : Fin (26 : ℕ) → Bool) => (List.foldl (fun (x7 : List Bool) (x8 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) => x7 ++ [bif x8.1 then x7.getD (↑x8.2.1) Bool.false && x7.getD (↑x8.2.2) Bool.false else x7.getD (↑x8.2.1) Bool.false || x7.getD (↑x8.2.2) Bool.false]) (List.ofFn x6) (List.ofFn fun (x7 : Fin (63 : ℕ)) => (x3 x7, x4 x7, x5 x7))).getD (88 : ℕ) Bool.false;     (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ x1 x8 → (x6 fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8)) = Bool.true) ∧ ∀ (x7 x8 : Fin (13 : ℕ) → Bool), x2 x7 x8 → x6 (Fin.append x7 x8) = Bool.false) := by
  exact Exists.elim hOvalCircuit fun op hop =>
    Exists.elim hop fun a ha =>
      Exists.elim ha fun b hb =>
        ⟨op, a, b, hb.1, hb.2.1, fun P L hPL =>
          have hs := hOvalSound P L hPL.1 hPL.2.1 hPL.2.2.1 hPL.2.2.2
          hb.2.2 P L hs.1 hs.2.1 hs.2.2.1 hs.2.2.2⟩
