import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18683_2
    (hEmbedDoubleTri :
      ∀ (z : ℕ → ℕ) (b1 b3 : ℕ) (p : Fin (24 : ℕ)),
        (∀ (j : Fin (15 : ℕ)), ∃ (i h : Fin ((9 : ℕ) + ↑j)),
          z ((9 : ℕ) + ↑j) = (z ↑i ||| z ↑h) ∨ z ((9 : ℕ) + ↑j) = (z ↑i &&& z ↑h)) →
        ∃ (w : ℕ → ℕ),
          w (0 : ℕ) = z (0 : ℕ) ∧
          w (1 : ℕ) = b1 ∧
          w (2 : ℕ) = z (1 : ℕ) ∧
          w (3 : ℕ) = b3 ∧
          (∀ (i : Fin (7 : ℕ)), w (↑i + (4 : ℕ)) = z (↑i + (2 : ℕ))) ∧
          w (31 : ℕ) = (z ↑p ||| ((b1 &&& (z (2 : ℕ) ||| z (6 : ℕ))) ||| (b3 &&& (z (4 : ℕ) ||| z (5 : ℕ))))) ∧
          ∀ (j : Fin (21 : ℕ)), ∃ (i h : Fin ((11 : ℕ) + ↑j)),
            w ((11 : ℕ) + ↑j) = (w ↑i ||| w ↑h) ∨ w ((11 : ℕ) + ↑j) = (w ↑i &&& w ↑h))
    (hPuncturedDoubleTri :
      ∃ (z : ℕ → ℕ),
        (∀ (i : Fin (9 : ℕ)), z ↑i = [(2147418115 : ℕ), (34144976944 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑i (0 : ℕ)) ∧
        (∃ (p : Fin (24 : ℕ)), z ↑p ||| (204 : ℕ) = (65535 : ℕ)) ∧
        ∀ (j : Fin (15 : ℕ)), ∃ (i h : Fin ((9 : ℕ) + ↑j)),
          z ((9 : ℕ) + ↑j) = (z ↑i ||| z ↑h) ∨ z ((9 : ℕ) + ↑j) = (z ↑i &&& z ↑h)) :
    ∃ (x1 : ℕ → ℕ), (∀ (x2 : Fin (11 : ℕ)), x1 ↑x2 = [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)].getD ↑x2 (0 : ℕ)) ∧ (∃ (x2 : Fin (32 : ℕ)), x1 ↑x2 = (65535 : ℕ)) ∧ ∀ (x2 : Fin (21 : ℕ)), ∃ (x3 : Fin ((11 : ℕ) + ↑x2)) (x4 : Fin ((11 : ℕ) + ↑x2)), x1 ((11 : ℕ) + ↑x2) = x1 ↑x3 ||| x1 ↑x4 ∨ x1 ((11 : ℕ) + ↑x2) = x1 ↑x3 &&& x1 ↑x4 := by
  rcases hPuncturedDoubleTri with ⟨z, init, ⟨p, hp⟩, hz⟩
  rcases hEmbedDoubleTri z (663661903884 : ℕ) (728266375360 : ℕ) p hz with ⟨w, h0, h1, h2, h3, hshift, hout, hrec⟩
  refine ⟨w, ?_, ⟨⟨31, by decide⟩, ?_⟩, hrec⟩
  · exact Fin.cases (Eq.trans h0 (init ⟨0, Nat.zero_lt_succ 8⟩))
      (Fin.cases h1
        (Fin.cases (Eq.trans h2 (init ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 7)⟩))
          (Fin.cases h3
            (fun k => Eq.trans (hshift k) (init ⟨k.val + 2, Nat.add_lt_add_right k.isLt 2⟩)))))
  · have hz2 : z 2 = 21653750532 := init ⟨2, Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ 6))⟩
    have hz4 : z 4 = 26322415680 := init ⟨4, Nat.lt_of_sub_ne_zero (by decide)⟩
    have hz5 : z 5 = 344922804352 := init ⟨5, Nat.lt_of_sub_ne_zero (by decide)⟩
    have hz6 : z 6 = 414195942664 := init ⟨6, Nat.lt_of_sub_ne_zero (by decide)⟩
    change w 31 = 65535
    rw [hout, hz2, hz4, hz5, hz6]
    exact hp
