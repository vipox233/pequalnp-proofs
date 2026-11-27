import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18272_3
    (hFoldCountEquiv :
      (∀ (n : ℕ) (p : Fin n → Bool), List.countP p (List.finRange n) = (List.filter p (List.finRange n)).length) ∧
      ∀ (f : ℕ × ℕ → ℕ) (l : List (ℕ × ℕ)),
        List.foldl (fun (acc : ℕ) (p : ℕ × ℕ) => acc ||| f p) (0 : ℕ) l =
          List.foldr (fun (a b : ℕ) => a ||| b) (0 : ℕ) (List.map f l))
    (hFoldWitness :
      ∃ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 : Fin x1 → ℕ) (x4 : Fin x1 → ℕ) (x5 : ℕ → ℕ) (x6 : List (ℕ × ℕ)), (6 : ℕ) ≤ x1 ∧ x1 + (2 : ℕ) * x6.length = (22 : ℕ) ∧ (3 : ℕ) ≤ List.countP x2 (List.finRange x1) ∧ (∀ (x7 : Fin (11 : ℕ)), x5 ↑x7 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x7 (0 : ℕ)) ∧ (∀ (x7 : Fin x1), x3 x7 ≤ x4 x7 ∧ x4 x7 < (11 : ℕ) + ↑x7 ∧ (x5 ((11 : ℕ) + ↑x7) = if x2 x7 = Bool.true then x5 (x3 x7) &&& x5 (x4 x7) else x5 (x3 x7) ||| x5 (x4 x7)) ∧ (∃ (x8 : Fin (16 : ℕ)), (x5 ((11 : ℕ) + ↑x7)).testBit ↑x8 = Bool.true) ∧ (∃ (x8 : Fin (24 : ℕ)), (x5 ((11 : ℕ) + ↑x7)).testBit ((16 : ℕ) + ↑x8) = Bool.true) ∧ ((∃ x8 ∈ x6, (11 : ℕ) + ↑x7 = x8.1 ∨ (11 : ℕ) + ↑x7 = x8.2) ∨ ∃ (x8 : Fin x1), x7 < x8 ∧ ((11 : ℕ) + ↑x7 = x3 x8 ∨ (11 : ℕ) + ↑x7 = x4 x8))) ∧ (∀ x7 ∈ x6, x7.1 < (11 : ℕ) + x1 ∧ x7.2 < (11 : ℕ) + x1) ∧ List.foldl (fun (acc : ℕ) (p : ℕ × ℕ) => acc ||| (x5 p.1 &&& x5 p.2)) (0 : ℕ) x6 = (65535 : ℕ)) :
    (∃ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 : Fin x1 → ℕ) (x4 : Fin x1 → ℕ) (x5 : ℕ → ℕ) (x6 : List (ℕ × ℕ)), (6 : ℕ) ≤ x1 ∧ x1 + (2 : ℕ) * x6.length = (22 : ℕ) ∧ (3 : ℕ) ≤ (List.filter x2 (List.finRange x1)).length ∧ (∀ (x7 : Fin (11 : ℕ)), x5 ↑x7 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x7 (0 : ℕ)) ∧ (∀ (x7 : Fin x1), x3 x7 ≤ x4 x7 ∧ x4 x7 < (11 : ℕ) + ↑x7 ∧ (x5 ((11 : ℕ) + ↑x7) = if x2 x7 = Bool.true then x5 (x3 x7) &&& x5 (x4 x7) else x5 (x3 x7) ||| x5 (x4 x7)) ∧ (∃ (x8 : Fin (16 : ℕ)), (x5 ((11 : ℕ) + ↑x7)).testBit ↑x8 = Bool.true) ∧ (∃ (x8 : Fin (24 : ℕ)), (x5 ((11 : ℕ) + ↑x7)).testBit ((16 : ℕ) + ↑x8) = Bool.true) ∧ ((∃ x8 ∈ x6, (11 : ℕ) + ↑x7 = x8.1 ∨ (11 : ℕ) + ↑x7 = x8.2) ∨ ∃ (x8 : Fin x1), x7 < x8 ∧ ((11 : ℕ) + ↑x7 = x3 x8 ∨ (11 : ℕ) + ↑x7 = x4 x8))) ∧ (∀ x7 ∈ x6, x7.1 < (11 : ℕ) + x1 ∧ x7.2 < (11 : ℕ) + x1) ∧ List.foldr (fun (x7 x8 : ℕ) => x7 ||| x8) (0 : ℕ) (List.map (fun (x7 : ℕ × ℕ) => x5 x7.1 &&& x5 x7.2) x6) = (65535 : ℕ)) :=
  Exists.elim hFoldWitness fun x1 h1 =>
    Exists.elim h1 fun x2 h2 =>
      Exists.elim h2 fun x3 h3 =>
        Exists.elim h3 fun x4 h4 =>
          Exists.elim h4 fun x5 h5 =>
            Exists.elim h5 fun x6 hP =>
              ⟨x1, x2, x3, x4, x5, x6,
               hP.1, hP.2.1,
               (hFoldCountEquiv.1 x1 x2) ▸ hP.2.2.1,
               hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1,
               (hFoldCountEquiv.2 (fun p => x5 p.1 &&& x5 p.2) x6) ▸ hP.2.2.2.2.2.2⟩
