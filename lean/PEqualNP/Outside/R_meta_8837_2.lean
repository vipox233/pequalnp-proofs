import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8837_2
    (hDual :
      ∀ (q v : ℕ) (I : Fin v → Fin v → Prop) [DecidableRel I],
        (1 : ℕ) ≤ q →
        v = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ (l : Fin v), Fintype.card { p : Fin v // I p l } = q + (1 : ℕ)) →
        (∀ (p1 p2 : Fin v), p1 ≠ p2 → ∃! l : Fin v, I p1 l ∧ I p2 l) →
        ∀ (l1 l2 : Fin v), l1 ≠ l2 → ∃! p : Fin v, I p l1 ∧ I p l2)
    (hMain :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
        (199 : ℕ) ≤ x1 →
        x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
        (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
        (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
        (∀ (l1 l2 : Fin x2), l1 ≠ l2 → ∃! p : Fin x2, x3 p l1 ∧ x3 p l2) →
        ∀ (x9 : ℕ) (x10 : Finset ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),
          have x12 : ℕ := x2 + x2;
          have x13 : ℕ := x12 + x9 - (1 : ℕ);
          have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
          have x15 : ℕ → Prop := fun (x15 : ℕ) => ∀ (x16 x17 : Fin x2), x3 x16 x17 → (x14 x16, x14 x17) ∈ x11 x15;
          have x16 : ℕ → Prop := fun (x16 : ℕ) => ∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x11 x16;
          x12 ≤ x9 + (1 : ℕ) → x9 < x2 * (x1 / (100 : ℕ) + (1 : ℕ)) → (∀ (x19 : Fin x2), x11 ↑x19 = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.1 x19 = Bool.true} ∧ x11 (x2 + ↑x19) = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.2 x19 = Bool.true}) → (∀ x20 < x9, ∃ (x22 : ℕ) (x23 : ℕ), Max.max x22 x23 < x12 + x20 ∧ (x11 (x12 + x20) ∈ [x11 x22 ∪ x11 x23, x11 x22, ∅] ∨ x11 (x12 + x20) = x11 x22 ∩ x11 x23 ∧ (x20 ∈ x10 ∨ ∃ (x24 : Set (Fin x2 → Bool)) (x25 : Set (Fin x2 → Bool)), x11 x22 = x24 ×ˢ Set.univ ∧ x11 x23 = Set.univ ×ˢ x25))) → x15 x13 ∧ x16 x13 → (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) → (∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x13 ∧ x11 x13 = x11 x23 ∪ x11 x24 ∧ ¬x15 x23 ∧ ¬x15 x24) → (100 : ℕ) * x10.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],
      (199 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →
      ∀ (x9 : ℕ) (x10 : Finset ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),
        have x12 : ℕ := x2 + x2;
        have x13 : ℕ := x12 + x9 - (1 : ℕ);
        have x14 : Fin x2 → Fin x2 → Bool := fun (x14 x15 : Fin x2) => Decidable.decide (x15 = x14);
        have x15 : ℕ → Prop := fun (x15 : ℕ) => ∀ (x16 x17 : Fin x2), x3 x16 x17 → (x14 x16, x14 x17) ∈ x11 x15;
        have x16 : ℕ → Prop := fun (x16 : ℕ) => ∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x11 x16;
        x12 ≤ x9 + (1 : ℕ) → x9 < x2 * (x1 / (100 : ℕ) + (1 : ℕ)) → (∀ (x19 : Fin x2), x11 ↑x19 = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.1 x19 = Bool.true} ∧ x11 (x2 + ↑x19) = {x20 : (Fin x2 → Bool) × (Fin x2 → Bool) | x20.2 x19 = Bool.true}) → (∀ x20 < x9, ∃ (x22 : ℕ) (x23 : ℕ), Max.max x22 x23 < x12 + x20 ∧ (x11 (x12 + x20) ∈ [x11 x22 ∪ x11 x23, x11 x22, ∅] ∨ x11 (x12 + x20) = x11 x22 ∩ x11 x23 ∧ (x20 ∈ x10 ∨ ∃ (x24 : Set (Fin x2 → Bool)) (x25 : Set (Fin x2 → Bool)), x11 x22 = x24 ×ˢ Set.univ ∧ x11 x23 = Set.univ ×ˢ x25))) → x15 x13 ∧ x16 x13 → (∀ x22 < x13, ¬(x15 x22 ∧ x16 x22)) → (∃ (x23 : ℕ) (x24 : ℕ), Max.max x23 x24 < x13 ∧ x11 x13 = x11 x23 ∪ x11 x24 ∧ ¬x15 x23 ∧ ¬x15 x24) → (100 : ℕ) * x10.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x9 := by
  intro x1 x2 x3 x4 hx1 hx2 hLine hUniq
  have hle1 : (1 : ℕ) ≤ x1 := Nat.le_trans (show (1 : ℕ) ≤ 199 by decide) hx1
  exact @hMain x1 x2 x3 x4 hx1 hx2 hLine hUniq (@hDual x1 x2 x3 x4 hle1 hx2 hLine hUniq)
