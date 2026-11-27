import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18915_1
    (hFullTwoWire :
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w1 w2 : ℕ),
        C.size ≤ (63 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        w1 < (26 : ℕ) + C.size ∧
        w2 < (26 : ℕ) + C.size ∧
        w1 ≠ w2 ∧
        (∀ (a b : Fin (13 : ℕ) → Bool),
          have l : List Bool := List.ofFn fun (i : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases a b i;
          ((C.wires l).getD w1 Bool.false && (C.wires l).getD w2 Bool.false) =
            Decidable.decide (∃ (p q : Fin (13 : ℕ)),
              (p = q ∨ p = q + (1 : Fin (13 : ℕ)) ∨ p = q + (3 : Fin (13 : ℕ)) ∨ p = q + (9 : Fin (13 : ℕ))) ∧
              a p = Bool.true ∧ b q = Bool.true)) ∧
        ∀ (b : Bool),
          have l : List Bool := List.ofFn fun (i : Fin (26 : ℕ)) => Decidable.decide (↑i = if b = Bool.true then (13 : ℕ) else (0 : ℕ));
          ((C.wires l).getD w1 Bool.false || (C.wires l).getD w2 Bool.false) = Bool.false)
    (hTestsOfFull :
      ∀ (f : List Bool → Bool),
        (∀ (a b : Fin (13 : ℕ) → Bool),
          f (List.ofFn fun (i : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases a b i) =
            Decidable.decide (∃ (p q : Fin (13 : ℕ)),
              (p = q ∨ p = q + (1 : Fin (13 : ℕ)) ∨ p = q + (3 : Fin (13 : ℕ)) ∨ p = q + (9 : Fin (13 : ℕ))) ∧
              a p = Bool.true ∧ b q = Bool.true)) →
        have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))));
        have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4;
        have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
        (∀ (x9 x10 : Fin (13 : ℕ)), x1 (x3 x9) x10 = Bool.false → f (x2 (x3 x9) (x3 x10)) = Bool.true) ∧
        ∀ (x9 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x9) ≤ (3 : ℕ) →
          f (x2 x9 (x1 x9)) = Bool.false ∧
          f (x2 (fun (x11 : Fin (13 : ℕ)) => !(x9 x11 || x9 (x11 - (1 : Fin (13 : ℕ))) || x9 (x11 - (3 : Fin (13 : ℕ))) || x9 (x11 - (9 : Fin (13 : ℕ))))) x9) = Bool.false) :
    (have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ),   have x7 : List Bool → ℕ → Bool := fun (x7 : List Bool) (x8 : ℕ) => (x4.wires x7).getD x8 Bool.false;   have x8 : List Bool → Bool := fun (x8 : List Bool) => x7 x8 x5 && x7 x8 x6;   x4.size ≤ (63 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x9 ∈ x4.gates, x9.inputs.Nodup) ∧         x5 < (26 : ℕ) + x4.size ∧           x6 < (26 : ℕ) + x4.size ∧             x5 ≠ x6 ∧               (∀ (x9 x10 : Fin (13 : ℕ)), x1 (x3 x9) x10 = Bool.false → x8 (x2 (x3 x9) (x3 x10)) = Bool.true) ∧                 (∀ (x9 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x9) ≤ (3 : ℕ) → x8 (x2 x9 (x1 x9)) = Bool.false ∧ x8 (x2 (fun (x11 : Fin (13 : ℕ)) => !(x9 x11 || x9 (x11 - (1 : Fin (13 : ℕ))) || x9 (x11 - (3 : Fin (13 : ℕ))) || x9 (x11 - (9 : Fin (13 : ℕ))))) x9) = Bool.false) ∧                   ∀ (x9 : Bool),                     have x10 : List Bool := List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = if x9 = Bool.true then (13 : ℕ) else (0 : ℕ));                     (x7 x10 x5 || x7 x10 x6) = Bool.false) :=
  Exists.elim hFullTwoWire fun C hC =>
    Exists.elim hC fun w1 hw1 =>
      Exists.elim hw1 fun w2 h =>
        ⟨C, w1, w2, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
          (hTestsOfFull (fun l => (C.wires l).getD w1 Bool.false && (C.wires l).getD w2 Bool.false) h.2.2.2.2.2.2.1).1,
          (hTestsOfFull (fun l => (C.wires l).getD w1 Bool.false && (C.wires l).getD w2 Bool.false) h.2.2.2.2.2.2.1).2,
          h.2.2.2.2.2.2.2⟩
