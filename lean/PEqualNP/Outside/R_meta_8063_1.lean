import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8063_1
    (hStepExtend :
      ∀ (x1 : ℕ) (x2 : ℕ → Bool) (x3 x4 : ℕ → ℕ) (x5 : ℕ → BitVec (60 : ℕ)) (x9 : ℕ) (x12 : Bool),
        x9 < x1 →
        have x13 : ℕ := if x12 = Bool.true then (58 : ℕ) else (59 : ℕ);
        have stepRel : ℕ → ℕ → Prop := fun (x14 x15 : ℕ) =>
          ∃ x16 < x1, x15 = (14 : ℕ) + x16 ∧
            (x14 = x3 x16 ∧ (x2 x16 || (x5 (x4 x16)).getLsbD x13) = Bool.true ∨
             x14 = x4 x16 ∧ (x2 x16 || (x5 (x3 x16)).getLsbD x13) = Bool.true);
        (Relation.ReflTransGen stepRel (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) (x3 x9) ∧
          (x2 x9 || (x5 (x4 x9)).getLsbD x13) = Bool.true) ∨
        (Relation.ReflTransGen stepRel (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) (x4 x9) ∧
          (x2 x9 || (x5 (x3 x9)).getLsbD x13) = Bool.true) →
        Relation.ReflTransGen stepRel (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) ((14 : ℕ) + x9))
    (hPrevWire :
      ∀ (x1 : ℕ) (x2 : ℕ → Bool) (x3 x4 : ℕ → ℕ) (x5 : ℕ → BitVec (60 : ℕ)),
        x1 ≤ (27 : ℕ) →
        (∀ x7 < (14 : ℕ), x5 x7 = BitVec.ofNat (60 : ℕ) ([(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD x7 (0 : ℕ))) →
        (∀ x8 < x1, x3 x8 ≠ x4 x8 ∧ x3 x8 < (14 : ℕ) + x8 ∧ x4 x8 < (14 : ℕ) + x8 ∧ (x2 x8 = Bool.false → (0 : ℕ) < x8) ∧ x5 ((14 : ℕ) + x8) = if x2 x8 = Bool.true then x5 (x3 x8) ||| x5 (x4 x8) else x5 (x3 x8) &&& x5 (x4 x8)) →
        ∀ x9 < x1,
          x5 ((14 : ℕ) + x9) = (2097151 : BitVec (60 : ℕ)) →
          ∃ (x12 : Bool),
            have x13 : ℕ := if x12 = Bool.true then (58 : ℕ) else (59 : ℕ);
            have stepRel : ℕ → ℕ → Prop := fun (x14 x15 : ℕ) =>
              ∃ x16 < x1, x15 = (14 : ℕ) + x16 ∧
                (x14 = x3 x16 ∧ (x2 x16 || (x5 (x4 x16)).getLsbD x13) = Bool.true ∨
                 x14 = x4 x16 ∧ (x2 x16 || (x5 (x3 x16)).getLsbD x13) = Bool.true);
            (Relation.ReflTransGen stepRel (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) (x3 x9) ∧
              (x2 x9 || (x5 (x4 x9)).getLsbD x13) = Bool.true) ∨
            (Relation.ReflTransGen stepRel (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) (x4 x9) ∧
              (x2 x9 || (x5 (x3 x9)).getLsbD x13) = Bool.true)) :
    (∀ (x1 : ℕ) (x2 : ℕ → Bool) (x3 x4 : ℕ → ℕ) (x5 : ℕ → BitVec (60 : ℕ)),   x1 ≤ (27 : ℕ) →     (∀ x7 < (14 : ℕ), x5 x7 = BitVec.ofNat (60 : ℕ) ([(2594090156585648135 : ℕ), (15270196031782968 : ℕ), (58150373818816 : ℕ), (94946423956573696 : ℕ), (54820275478360064 : ℕ), (3870282840506368 : ℕ), (133412159488 : ℕ), (1911954591369396745 : ℕ), (218716039641305168 : ℕ), (189725234880873600 : ℕ), (156548607028504576 : ℕ), (229736628137050114 : ℕ), (270286071509155872 : ℕ), (288160007408582916 : ℕ)].getD x7 (0 : ℕ))) →       (∀ x8 < x1, x3 x8 ≠ x4 x8 ∧ x3 x8 < (14 : ℕ) + x8 ∧ x4 x8 < (14 : ℕ) + x8 ∧ (x2 x8 = Bool.false → (0 : ℕ) < x8) ∧ x5 ((14 : ℕ) + x8) = if x2 x8 = Bool.true then x5 (x3 x8) ||| x5 (x4 x8) else x5 (x3 x8) &&& x5 (x4 x8)) →         ∀ x9 < x1,           x5 ((14 : ℕ) + x9) = (2097151 : BitVec (60 : ℕ)) →             ∃ (x12 : Bool),               have x13 : ℕ := if x12 = Bool.true then (58 : ℕ) else (59 : ℕ);               Relation.ReflTransGen (fun (x14 x15 : ℕ) => ∃ x16 < x1, x15 = (14 : ℕ) + x16 ∧ (x14 = x3 x16 ∧ (x2 x16 || (x5 (x4 x16)).getLsbD x13) = Bool.true ∨ x14 = x4 x16 ∧ (x2 x16 || (x5 (x3 x16)).getLsbD x13) = Bool.true)) (if x12 = Bool.true then (7 : ℕ) else (0 : ℕ)) ((14 : ℕ) + x9)) :=
  fun x1 x2 x3 x4 x5 h1 h2 h3 x9 hx9 hVal =>
    Exists.elim (hPrevWire x1 x2 x3 x4 x5 h1 h2 h3 x9 hx9 hVal) fun x12 hDisj =>
      ⟨x12, hStepExtend x1 x2 x3 x4 x5 x9 x12 hx9 hDisj⟩
