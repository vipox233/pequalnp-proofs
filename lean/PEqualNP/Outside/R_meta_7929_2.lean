import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7929_2
    (hTwoWires :
      let P : Type := Fin (13 : ℕ) → Bool;
      have x1 : P → P := fun f j => f j || f (j + (1 : Fin (13 : ℕ))) || f (j + (3 : Fin (13 : ℕ))) || f (j + (9 : Fin (13 : ℕ)));
      have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun a b => a = b ∨ a = b + (1 : Fin (13 : ℕ)) ∨ a = b + (3 : Fin (13 : ℕ)) ∨ a = b + (9 : Fin (13 : ℕ));
      have x3 : P → P → List Bool := fun f g => List.ofFn fun i : Fin ((13 : ℕ) + (13 : ℕ)) => Fin.addCases f g i;
      have x4 : Fin (13 : ℕ) → P := fun a b => Decidable.decide (b = a);
      have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → List Bool → Bool := fun c a b l => (c.wires l).getD a Bool.false && (c.wires l).getD b Bool.false;
      ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ),
        have u : ℕ → List Bool := fun k => x6.wires (List.ofFn fun i : Fin (26 : ℕ) => Decidable.decide (↑i = k));
        x6.size ≤ (63 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ (∀ g ∈ x6.gates, g.inputs.Nodup) ∧
        x7 ≠ x8 ∧ x7 < (26 : ℕ) + x6.size ∧ x8 < (26 : ℕ) + x6.size ∧
        (∀ a b : Fin (13 : ℕ), x2 a b → x5 x6 x7 x8 (x3 (x4 a) (x4 b)) = Bool.true) ∧
        (∀ f : P, (∀ a : Fin (13 : ℕ), f a = Bool.false → ∃ b : Fin (13 : ℕ), x2 a b ∧ x1 f b = Bool.false) →
          x5 x6 x7 x8 (x3 f fun b => !x1 f b) = Bool.false) ∧
        (u (0 : ℕ)).getD x7 Bool.false = Bool.false ∧ (u (0 : ℕ)).getD x8 Bool.false = Bool.false ∧
        (u (13 : ℕ)).getD x7 Bool.false = Bool.false ∧ (u (13 : ℕ)).getD x8 Bool.false = Bool.false)
    (hBoolCombine :
      ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ),
        have u : ℕ → List Bool := fun k => x6.wires (List.ofFn fun i : Fin (26 : ℕ) => Decidable.decide (↑i = k));
        ((u (0 : ℕ)).getD x7 Bool.false = Bool.false ∧ (u (0 : ℕ)).getD x8 Bool.false = Bool.false ∧
         (u (13 : ℕ)).getD x7 Bool.false = Bool.false ∧ (u (13 : ℕ)).getD x8 Bool.false = Bool.false) →
        ∀ (x9 : Bool),
          have x10 : List Bool := x6.wires (List.ofFn fun i : Fin (26 : ℕ) => Decidable.decide (↑i = if x9 = Bool.true then (13 : ℕ) else (0 : ℕ)));
          x10.getD x7 Bool.false = Bool.false ∧ x10.getD x8 Bool.false = Bool.false) :
    (have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))); have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ)); have x3 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x3 x4 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x3 x4 x5; have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x4 x5 : Fin (13 : ℕ)) => Decidable.decide (x5 = x4); have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → List Bool → Bool := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ) (x8 : List Bool) => (x5.wires x8).getD x6 Bool.false && (x5.wires x8).getD x7 Bool.false; ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : ℕ) (x8 : ℕ),   x6.size ≤ (63 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧       (∀ x9 ∈ x6.gates, x9.inputs.Nodup) ∧         x7 ≠ x8 ∧           x7 < (26 : ℕ) + x6.size ∧             x8 < (26 : ℕ) + x6.size ∧               (∀ (x9 x10 : Fin (13 : ℕ)), x2 x9 x10 → x5 x6 x7 x8 (x3 (x4 x9) (x4 x10)) = Bool.true) ∧                 (∀ (x9 : Fin (13 : ℕ) → Bool), (∀ (x10 : Fin (13 : ℕ)), x9 x10 = Bool.false → ∃ (x12 : Fin (13 : ℕ)), x2 x10 x12 ∧ x1 x9 x12 = Bool.false) → x5 x6 x7 x8 (x3 x9 fun (x11 : Fin (13 : ℕ)) => !x1 x9 x11) = Bool.false) ∧                   ∀ (x9 : Bool),                     have x10 : List Bool := x6.wires (List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = if x9 = Bool.true then (13 : ℕ) else (0 : ℕ)));                     x10.getD x7 Bool.false = Bool.false ∧ x10.getD x8 Bool.false = Bool.false) :=
  Exists.elim hTwoWires fun x6 h1 =>
    Exists.elim h1 fun x7 h2 =>
      Exists.elim h2 fun x8 hP =>
        ⟨x6, x7, x8,
         hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2.1, hP.2.2.2.2.2.1,
         hP.2.2.2.2.2.2.1, hP.2.2.2.2.2.2.2.1,
         hBoolCombine x6 x7 x8 hP.2.2.2.2.2.2.2.2⟩
