import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7290_2
    (hWiresValid :
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 →
        have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → ℕ → Bool := fun (x7 x8 x9 x10 : Fin (13 : ℕ)) (x11 : ℕ) =>
          (x2.wires ((List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x7 ∨ x12 = x8)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10))).getD x11 Bool.false;
        (∀ (x8 x9 x10 x11 : Fin (13 : ℕ)),
          (x7 x8 x9 x10 x11 x3 || x7 x8 x9 x10 x11 x4) =
            Decidable.decide ((x8 - x10).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (x8 - x11).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (x9 - x10).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (x9 - x11).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) →
        (∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x7 x9 x9 x10 x10 x3 = Bool.true ∧ x7 x9 x9 x10 x10 x4 = Bool.false) →
        (∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), x7 x10 x10 x11 x11 x4 = Bool.true ∧ x7 x10 x10 x11 x11 x3 = Bool.false) →
        (26 : ℕ) ≤ x3 ∧ x3 < (26 : ℕ) + x2.size ∧ (26 : ℕ) ≤ x4 ∧ x4 < (26 : ℕ) + x2.size ∧ x3 ≠ x4)
    (hOrderedLB :
      ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x2 →
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 →
        (26 : ℕ) ≤ x3 → x3 < x4 → x4 < (26 : ℕ) + x2.size →
        have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → ℕ → Bool := fun (x7 x8 x9 x10 : Fin (13 : ℕ)) (x11 : ℕ) =>
          (x2.wires ((List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x7 ∨ x12 = x8)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10))).getD x11 Bool.false;
        (∀ (x8 x9 x10 x11 : Fin (13 : ℕ)),
          (x7 x8 x9 x10 x11 x3 || x7 x8 x9 x10 x11 x4) =
            Decidable.decide ((x8 - x10).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (x8 - x11).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (x9 - x10).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (x9 - x11).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])) →
        (∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x7 x9 x9 x10 x10 x3 = Bool.true ∧ x7 x9 x9 x10 x10 x4 = Bool.false) →
        (∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), x7 x10 x10 x11 x11 x4 = Bool.true ∧ x7 x10 x10 x11 x11 x3 = Bool.false) →
        (63 : ℕ) ≤ x2.size) :
    (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 →       have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → ℕ → Bool := fun (x7 x8 x9 x10 : Fin (13 : ℕ)) (x11 : ℕ) => (x2.wires ((List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x7 ∨ x12 = x8)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10))).getD x11 Bool.false;       (∀ (x8 x9 x10 x11 : Fin (13 : ℕ)), (x7 x8 x9 x10 x11 x3 || x7 x8 x9 x10 x11 x4) = Decidable.decide (x8 - x10 ∈ x1 ∨ x8 - x11 ∈ x1 ∨ x9 - x10 ∈ x1 ∨ x9 - x11 ∈ x1)) → (∃ (x9 : Fin (13 : ℕ)) (x10 : Fin (13 : ℕ)), x7 x9 x9 x10 x10 x3 = Bool.true ∧ x7 x9 x9 x10 x10 x4 = Bool.false) → (∃ (x10 : Fin (13 : ℕ)) (x11 : Fin (13 : ℕ)), x7 x10 x10 x11 x11 x4 = Bool.true ∧ x7 x10 x10 x11 x11 x3 = Bool.false) → (63 : ℕ) ≤ x2.size) := by
  have hDecEq : ∀ (a b c d : Fin (13 : ℕ)),
      Decidable.decide (a - c ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∨ a - d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∨ b - c ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ))) ∨ b - d ∈ ({(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))} : Finset (Fin (13 : ℕ)))) =
      Decidable.decide ((a - c).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (a - d).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (b - c).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (b - d).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) := by decide
  intro x1 x2 x3 x4 hM hRB x7 hCov hW1 hW2
  have hCov' : ∀ (a b c d : Fin (13 : ℕ)),
      (x7 a b c d x3 || x7 a b c d x4) =
        Decidable.decide ((a - c).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (a - d).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (b - c).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∨ (b - d).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) :=
    fun a b c d => (hCov a b c d).trans (hDecEq a b c d)
  have hv := hWiresValid x2 x3 x4 hM hRB hCov' hW1 hW2
  exact Or.elim (Nat.lt_or_gt_of_ne hv.2.2.2.2)
    (fun hlt => hOrderedLB x2 x3 x4 hM hRB hv.1 hlt hv.2.2.2.1 hCov' hW1 hW2)
    (fun hgt => hOrderedLB x2 x4 x3 hM hRB hv.2.2.1 hgt hv.2.1
      (fun a b c d => (Bool.or_comm _ _).trans (hCov' a b c d)) hW2 hW1)
