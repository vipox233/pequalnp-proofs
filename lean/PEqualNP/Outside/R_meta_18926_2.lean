import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18926_2
    (hWireBounds :
      have x1 : Fin 12 → Fin 13 → Prop := fun p l => p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9;
      have x2 : (Fin 25 → Bool) → Prop := fun x => ∃ (p : Fin 12) (l : Fin 13), x1 p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true;
      have wv : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin 25 → Bool) → Bool := fun C w x => (C.wires (List.ofFn x)).getD w false;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        (∀ x : Fin 25 → Bool, (wv C u x && wv C v x) = true ↔ x2 x) →
        (∀ i : Fin 25, wv C u (fun j => decide (j = i)) = false) →
        25 ≤ u ∧ u < 25 + C.size ∧ v < 25 + C.size)
    (hBoundedWiresLB :
      have x1 : Fin 12 → Fin 13 → Prop := fun p l => p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9;
      have x2 : (Fin 25 → Bool) → Prop := fun x => ∃ (p : Fin 12) (l : Fin 13), x1 p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true;
      have wv : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin 25 → Bool) → Bool := fun C w x => (C.wires (List.ofFn x)).getD w false;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        (PEqualNP.MetaComplexity.Monotone2 C ∧
         25 ≤ u ∧ u < 25 + C.size ∧ v < 25 + C.size ∧
         (∀ x : Fin 25 → Bool, (wv C u x && wv C v x) = true ↔ x2 x) ∧
         (∀ i : Fin 25, wv C u (fun j => decide (j = i)) = false)) →
        57 ≤ C.size) :
    (have x1 : Fin (12 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 : Fin (12 : ℕ)) (x2 : Fin (13 : ℕ)) => x1.succ = x2 ∨ x1.succ = x2 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (9 : Fin ((12 : ℕ) + (1 : ℕ))); have x2 : (Fin (25 : ℕ) → Bool) → Prop := fun (x2 : Fin (25 : ℕ) → Bool) => ∃ (x3 : Fin (12 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (12 : ℕ) x4) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → (Fin (25 : ℕ) → Bool) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Fin (25 : ℕ) → Bool) => (x3.wires (List.ofFn x5)).getD x4 Bool.false; have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Bool := fun (x4 x5 : Fin (25 : ℕ)) => Decidable.decide (x5 = x4); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin (25 : ℕ) → Bool), (x3 x5 x6 x9 && x3 x5 x7 x9) = Bool.true ↔ x2 x9) → (∀ (x10 : Fin (25 : ℕ)), x3 x5 x6 (x4 x10) = Bool.false) → (57 : ℕ) ≤ x5.size) :=
  fun x5 x6 x7 hMono hComp hZero =>
    let hb := hWireBounds x5 x6 x7 hComp hZero
    hBoundedWiresLB x5 x6 x7 ⟨hMono, hb.1, hb.2.1, hb.2.2, hComp, hZero⟩
