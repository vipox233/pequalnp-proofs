import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18415_1
    (h1 : ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ (29 : ℕ) ∧ C.output < (17 : ℕ) + C.size ∧ w < (17 : ℕ) + C.size ∧
      ∀ (x : Fin (17 : ℕ) → Bool),
        (C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p l : Fin (17 : ℕ)),
            (([33216, 36352, 61440, 70208, 74880, 84224] : List ℕ).getD p.val 0).testBit l.val = Bool.true ∧
              x p = Bool.true ∧ x l = Bool.true) ∧
        (C.eval (List.ofFn x) = Bool.false →
          (C.wires (List.ofFn x)).getD w Bool.false = (x (15 : Fin 17) || x (16 : Fin 17))))
    (h2 : ∀ (p l : Fin (17 : ℕ)),
      (([33216, 36352, 61440, 70208, 74880, 84224] : List ℕ).getD p.val 0).testBit l.val = Bool.true ↔
        (↑p < (6 : ℕ) ∧
          (↑l = (15 : ℕ) + ↑p / (3 : ℕ) ∨
            (6 : ℕ) ≤ ↑l ∧ ↑l < (15 : ℕ) ∧
              (if ↑p < (3 : ℕ) then (↑l - (6 : ℕ)) / (3 : ℕ) else (↑l - (6 : ℕ)) % (3 : ℕ)) = ↑p % (3 : ℕ)))) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size ≤ (29 : ℕ) ∧       x1.output < (17 : ℕ) + x1.size ∧         x2 < (17 : ℕ) + x1.size ∧           ∀ (x3 : Fin (17 : ℕ) → Bool),             have x4 : Fin (17 : ℕ) → Fin (17 : ℕ) → Prop := fun (x4 x5 : Fin (17 : ℕ)) => ↑x4 < (6 : ℕ) ∧ (↑x5 = (15 : ℕ) + ↑x4 / (3 : ℕ) ∨ (6 : ℕ) ≤ ↑x5 ∧ ↑x5 < (15 : ℕ) ∧ (if ↑x4 < (3 : ℕ) then (↑x5 - (6 : ℕ)) / (3 : ℕ) else (↑x5 - (6 : ℕ)) % (3 : ℕ)) = ↑x4 % (3 : ℕ));             (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x5 : Fin (17 : ℕ)) (x6 : Fin (17 : ℕ)), x4 x5 x6 ∧ x3 x5 = Bool.true ∧ x3 x6 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (15 : Fin (17 : ℕ)) || x3 (16 : Fin (17 : ℕ)))) := by
  obtain ⟨C, w, hm, hs, ho, hw, hb⟩ := h1
  refine ⟨C, w, hm, hs, ho, hw, ?_⟩
  intro x
  dsimp only
  refine ⟨?_, ?_⟩
  · constructor
    · intro hev
      obtain ⟨p, l, he, hp, hl⟩ := (hb x).1.mp hev
      exact ⟨p, l, (h2 p l).mp he, hp, hl⟩
    · rintro ⟨p, l, hr, hp, hl⟩
      exact (hb x).1.mpr ⟨p, l, (h2 p l).mpr hr, hp, hl⟩
  · exact (hb x).2
