import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17549_3
    (hFoldOrCover : ∀ (f : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ) (xs : List (Fin (32 : ℕ) × Fin (32 : ℕ))),
      (∀ a ∈ xs, f a < (65536 : ℕ)) →
        (∀ (b : Fin (16 : ℕ)), (28864 : ℕ).testBit ↑b = Bool.false → ∃ a ∈ xs, (f a).testBit ↑b = Bool.true) →
          List.foldl (fun (acc : ℕ) (a : Fin (32 : ℕ) × Fin (32 : ℕ)) => acc ||| f a) (28864 : ℕ) xs = (65535 : ℕ))
    (hBitwiseWitness : ∃ (x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x2 : List (Fin (32 : ℕ) × Fin (32 : ℕ))),
      have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ), (371245215936 : ℕ), (582520731713 : ℕ), (1066477318818 : ℕ), (549755842560 : ℕ), (728266404032 : ℕ)] x1;
      have x4 : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ := fun (x4 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x3.getD ↑x4.1 (0 : ℕ) &&& x3.getD ↑x4.2 (0 : ℕ);
      x1.length + (2 : ℕ) * x2.length ≤ (15 : ℕ) ∧
        (∀ (x5 : Fin x1.length), ↑(x1.get x5).2.1 < (16 : ℕ) + ↑x5 ∧ ↑(x1.get x5).2.2 < (16 : ℕ) + ↑x5) ∧
          (List.filter (fun (x5 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5.1) x1).length = (1 : ℕ) ∧
            (∀ (x5 : Fin x1.length), (x1.get x5).1 = Bool.true → x3.getD ((16 : ℕ) + ↑x5) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ)) ∧
              (∀ x5 ∈ x2, ↑x5.1 < (16 : ℕ) + x1.length ∧ ↑x5.2 < (16 : ℕ) + x1.length ∧ x4 x5 &&& (1099511562240 : ℕ) = (0 : ℕ) ∧ x4 x5 < (65536 : ℕ)) ∧
                ∀ (b : Fin (16 : ℕ)), (28864 : ℕ).testBit ↑b = Bool.false → ∃ p ∈ x2, (x4 p).testBit ↑b = Bool.true) :
    ∃ (x1 : List (Bool × Fin (32 : ℕ) × Fin (32 : ℕ))) (x2 : List (Fin (32 : ℕ) × Fin (32 : ℕ))),   have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ), (371245215936 : ℕ), (582520731713 : ℕ), (1066477318818 : ℕ), (549755842560 : ℕ), (728266404032 : ℕ)] x1;   have x4 : Fin (32 : ℕ) × Fin (32 : ℕ) → ℕ := fun (x4 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x3.getD ↑x4.1 (0 : ℕ) &&& x3.getD ↑x4.2 (0 : ℕ);   x1.length + (2 : ℕ) * x2.length ≤ (15 : ℕ) ∧ (∀ (x5 : Fin x1.length), ↑(x1.get x5).2.1 < (16 : ℕ) + ↑x5 ∧ ↑(x1.get x5).2.2 < (16 : ℕ) + ↑x5) ∧ (List.filter (fun (x5 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x5.1) x1).length = (1 : ℕ) ∧ (∀ (x5 : Fin x1.length), (x1.get x5).1 = Bool.true → x3.getD ((16 : ℕ) + ↑x5) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ)) ∧ (∀ x5 ∈ x2, ↑x5.1 < (16 : ℕ) + x1.length ∧ ↑x5.2 < (16 : ℕ) + x1.length ∧ x4 x5 &&& (1099511562240 : ℕ) = (0 : ℕ)) ∧ List.foldl (fun (x5 : ℕ) (x6 : Fin (32 : ℕ) × Fin (32 : ℕ)) => x5 ||| x4 x6) (28864 : ℕ) x2 = (65535 : ℕ) :=
  Exists.elim hBitwiseWitness fun x1 h1 =>
  Exists.elim h1 fun x2 h =>
    ⟨x1, x2, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      fun p hp =>
        have h5 := h.2.2.2.2.1 p hp
        ⟨h5.1, h5.2.1, h5.2.2.1⟩,
      hFoldOrCover _ x2 (fun p hp => (h.2.2.2.2.1 p hp).2.2.2) h.2.2.2.2.2⟩
