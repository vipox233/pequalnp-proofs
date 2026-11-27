import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17257_2
    (hProjPlaneDual :
      ∀ (q v : ℕ) (inc : Fin v → Fin v → Prop) [DecidableRel inc],
        (2 : ℕ) ≤ q →
        v = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ l : Fin v, Fintype.card { p : Fin v // inc p l } = q + (1 : ℕ)) →
        (∀ p₁ p₂ : Fin v, p₁ ≠ p₂ → ∃! l : Fin v, inc p₁ l ∧ inc p₂ l) →
        (∀ p : Fin v, Fintype.card { l : Fin v // inc p l } = q + (1 : ℕ)) ∧
        (∀ l₁ l₂ : Fin v, l₁ ≠ l₂ → ∃! p : Fin v, inc p l₁ ∧ inc p l₂))
    (hEvenOrderDualLB :
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [DecidableRel x3],
        let x5 : Type := Fin x2 → Bool;
        have x6 : Fin x2 → Fin x2 → Bool := fun a b => Decidable.decide (b = a);
        ((299 : ℕ) ≤ x1 ∧ x1 % (2 : ℕ) = (0 : ℕ) ∧ x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) ∧
         (∀ l : Fin x2, Fintype.card { p : Fin x2 // x3 p l } = x1 + (1 : ℕ)) ∧
         (∀ p : Fin x2, Fintype.card { l : Fin x2 // x3 p l } = x1 + (1 : ℕ)) ∧
         (∀ p₁ p₂ : Fin x2, p₁ ≠ p₂ → ∃! l : Fin x2, x3 p₁ l ∧ x3 p₂ l) ∧
         (∀ l₁ l₂ : Fin x2, l₁ ≠ l₂ → ∃! p : Fin x2, x3 p l₁ ∧ x3 p l₂)) →
        ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),
          (x12 < x2 + x2 + x11 ∧
           (∀ i : Fin x2,
             x14 ↑i = {t : x5 × x5 | t.1 i = Bool.true} ∧
             x14 (x2 + ↑i) = {t : x5 × x5 | t.2 i = Bool.true}) ∧
           (∀ g < x11,
             ∃ u < x2 + x2 + g, ∃ w < x2 + x2 + g,
               have s : Set (x5 × x5) := x14 (x2 + x2 + g);
               s ∈ [x14 u ∪ x14 w, x14 u, ∅] ∨
               s = x14 u ∩ x14 w ∧ (g ∈ x13 ∨ ∃ (A B : Set x5), x14 u = A ×ˢ Set.univ ∧ x14 w = Set.univ ×ˢ B)) ∧
           (∀ p l : Fin x2, x3 p l → (x6 p, x6 l) ∈ x14 x12) ∧
           (∀ y : x5, Fintype.card { l : Fin x2 // y l = Bool.true } ≤ x1 →
             (fun p : Fin x2 => Decidable.decide ¬∃ l : Fin x2, x3 p l ∧ y l = Bool.true, y) ∉ x14 x12) ∧
           (100 : ℕ) * x13.card < x2 * x1) →
          x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (100 : ℕ) * x13.card < x2 * x1 → x1 % (2 : ℕ) = (0 : ℕ) → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11) :=
  fun x1 x2 x3 _ h299 hV hDeg hUnique x11 x12 x13 x14 hOut hInputs hGates hPos hNeg hCard hEven =>
    have hDual := hProjPlaneDual x1 x2 x3 (Nat.le_trans (Nat.le_add_right (2 : ℕ) (297 : ℕ)) h299) hV hDeg hUnique
    hEvenOrderDualLB x1 x2 x3
      ⟨h299, hEven, hV, hDeg, hDual.1, hUnique, hDual.2⟩
      x11 x12 x13 x14
      ⟨hOut, hInputs, hGates, hPos, hNeg, hCard⟩
