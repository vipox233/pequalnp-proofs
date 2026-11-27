import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18910_1
    (hIndepCircuit :
      let x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2
      ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),
        PEqualNP.MetaComplexity.Monotone2 x2 ∧
        x2.size ≤ (29 : ℕ) ∧
        x2.output < (17 : ℕ) + x2.size ∧
        x3 < (17 : ℕ) + x2.size ∧
        (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → x2.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧
        (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (x2.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD x3 Bool.false = Bool.true) ∧
        ∀ (x8 : Fin (17 : ℕ) → Bool),
          (∀ (u v : Fin (17 : ℕ)), x1 u v = Bool.true → x8 u = Bool.false ∨ x8 v = Bool.false) →
          x2.eval (List.ofFn x8) = Bool.false ∧
          (x8 (15 : Fin (17 : ℕ)) = Bool.false → x8 (16 : Fin (17 : ℕ)) = Bool.false → (x2.wires (List.ofFn x8)).getD x3 Bool.false = Bool.false))
    (hClosureIsIndep :
      let x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2
      ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),
        (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →
        have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false
        ∀ (x8 : Fin (17 : ℕ) → Bool),
          (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) →
          (∀ (u v : Fin (17 : ℕ)), x1 u v = Bool.true → x8 u = Bool.false ∨ x8 v = Bool.false) ∧
          (x4 = Bool.true → x8 (15 : Fin (17 : ℕ)) = Bool.false ∧ x8 (16 : Fin (17 : ℕ)) = Bool.false)) :
    (have x1 : Fin (17 : ℕ) → Fin (17 : ℕ) → Bool := fun (x1 x2 : Fin (17 : ℕ)) => ([(33216 : ℕ), (36352 : ℕ), (61440 : ℕ), (70208 : ℕ), (74880 : ℕ), (84224 : ℕ)].getD ↑x1 (0 : ℕ)).testBit ↑x2; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     x2.size ≤ (29 : ℕ) ∧       x2.output < (17 : ℕ) + x2.size ∧         x3 < (17 : ℕ) + x2.size ∧           (∀ (x4 x5 : Fin (17 : ℕ)), x1 x4 x5 = Bool.true → x2.eval (List.ofFn fun (x7 : Fin (17 : ℕ)) => Decidable.decide (x7 = x4 ∨ x7 = x5)) = Bool.true) ∧             (∀ x4 ∈ [(15 : Fin (17 : ℕ)), (16 : Fin (17 : ℕ))], (x2.wires (List.ofFn fun (x6 : Fin (17 : ℕ)) => Decidable.decide (x6 = x4))).getD x3 Bool.false = Bool.true) ∧               ∀ (x4 : Bool) (x5 : Finset (Fin (17 : ℕ))),                 (∀ x6 ∈ x5, ↑x6 < (6 : ℕ)) →                   have x7 : Fin (17 : ℕ) → Prop := fun (x7 : Fin (17 : ℕ)) => (x4 = Bool.false ∨ ↑x7 < (15 : ℕ)) ∧ ∀ x8 ∈ x5, x1 x8 x7 = Bool.false;                   ∀ (x8 : Fin (17 : ℕ) → Bool), (∀ (x9 : Fin (17 : ℕ)), x8 x9 = Bool.true ↔ if ↑x9 < (6 : ℕ) then ∀ (x10 : Fin (17 : ℕ)), x1 x9 x10 = Bool.true → ¬x7 x10 else x7 x9) → (x2.wires (List.ofFn x8)).getD (if x4 = Bool.true then x3 else x2.output) Bool.false = Bool.false) := by
  obtain ⟨x2, x3, hM, hSz, hOut, hW, hEdges, hSing, hIndep⟩ := hIndepCircuit
  refine ⟨x2, x3, hM, hSz, hOut, hW, hEdges, hSing, fun x4 x5 hx5 x8 hx8 => ?_⟩
  have hcl := hClosureIsIndep x4 x5 hx5 x8 hx8
  by_cases hx4 : x4 = Bool.true
  · rw [hx4]
    have h1516 := hcl.2 hx4
    exact (hIndep x8 hcl.1).2 h1516.1 h1516.2
  · have hx4f : x4 = Bool.false := Bool.eq_false_iff.mpr hx4
    rw [hx4f]
    exact (hIndep x8 hcl.1).1
