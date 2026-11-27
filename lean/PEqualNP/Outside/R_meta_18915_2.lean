import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18915_2
    (hCondEquiv :
      ∀ (x9 x10 : Fin (13 : ℕ)),
        (!(Decidable.decide (x10 = x9) || Decidable.decide (x10 + (1 : Fin (13 : ℕ)) = x9) || Decidable.decide (x10 + (3 : Fin (13 : ℕ)) = x9) || Decidable.decide (x10 + (9 : Fin (13 : ℕ)) = x9))) = Bool.false ↔
          ↑(x9 - x10) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])
    (hTwoWire :
      have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ))));
      have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4;
      have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3);
      ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ),
        have x7 : List Bool → ℕ → Bool := fun (x7 : List Bool) (x8 : ℕ) => (x4.wires x7).getD x8 Bool.false;
        have x8 : List Bool → Bool := fun (x8 : List Bool) => x7 x8 x5 && x7 x8 x6;
        x4.size ≤ (63 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧
        (∀ x9 ∈ x4.gates, x9.inputs.Nodup) ∧
        x5 < (26 : ℕ) + x4.size ∧
        x6 < (26 : ℕ) + x4.size ∧
        x5 ≠ x6 ∧
        (∀ (x9 x10 : Fin (13 : ℕ)), ↑(x9 - x10) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] → x8 (x2 (x3 x9) (x3 x10)) = Bool.true) ∧
        (∀ (x9 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x9) ≤ (3 : ℕ) → x8 (x2 x9 (x1 x9)) = Bool.false ∧ x8 (x2 (fun (x11 : Fin (13 : ℕ)) => !(x9 x11 || x9 (x11 - (1 : Fin (13 : ℕ))) || x9 (x11 - (3 : Fin (13 : ℕ))) || x9 (x11 - (9 : Fin (13 : ℕ))))) x9) = Bool.false) ∧
        (have x10 : List Bool := List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (0 : ℕ)); (x7 x10 x5 || x7 x10 x6) = Bool.false) ∧
        (have x10 : List Bool := List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = (13 : ℕ)); (x7 x10 x5 || x7 x10 x6) = Bool.false)) :
    (have x1 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x1 : Fin (13 : ℕ) → Bool) (x2 : Fin (13 : ℕ)) => !(x1 x2 || x1 (x2 + (1 : Fin (13 : ℕ))) || x1 (x2 + (3 : Fin (13 : ℕ))) || x1 (x2 + (9 : Fin (13 : ℕ)))); have x2 : (Fin (13 : ℕ) → Bool) → (Fin (13 : ℕ) → Bool) → List Bool := fun (x2 x3 : Fin (13 : ℕ) → Bool) => List.ofFn fun (x4 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x2 x3 x4; have x3 : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun (x3 x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : ℕ),   have x7 : List Bool → ℕ → Bool := fun (x7 : List Bool) (x8 : ℕ) => (x4.wires x7).getD x8 Bool.false;   have x8 : List Bool → Bool := fun (x8 : List Bool) => x7 x8 x5 && x7 x8 x6;   x4.size ≤ (63 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x4 ∧       (∀ x9 ∈ x4.gates, x9.inputs.Nodup) ∧         x5 < (26 : ℕ) + x4.size ∧           x6 < (26 : ℕ) + x4.size ∧             x5 ≠ x6 ∧               (∀ (x9 x10 : Fin (13 : ℕ)), x1 (x3 x9) x10 = Bool.false → x8 (x2 (x3 x9) (x3 x10)) = Bool.true) ∧                 (∀ (x9 : Fin (13 : ℕ) → Bool), List.count Bool.true (List.ofFn x9) ≤ (3 : ℕ) → x8 (x2 x9 (x1 x9)) = Bool.false ∧ x8 (x2 (fun (x11 : Fin (13 : ℕ)) => !(x9 x11 || x9 (x11 - (1 : Fin (13 : ℕ))) || x9 (x11 - (3 : Fin (13 : ℕ))) || x9 (x11 - (9 : Fin (13 : ℕ))))) x9) = Bool.false) ∧                   ∀ (x9 : Bool),                     have x10 : List Bool := List.ofFn fun (x10 : Fin (26 : ℕ)) => Decidable.decide (↑x10 = if x9 = Bool.true then (13 : ℕ) else (0 : ℕ));                     (x7 x10 x5 || x7 x10 x6) = Bool.false) := by
  rcases hTwoWire with ⟨C, w1, w2, hSz, hAO, hNd, hw1, hw2, hne, hPos, hNeg, hS0, hS13⟩
  refine ⟨C, w1, w2, hSz, hAO, hNd, hw1, hw2, hne, fun x9 x10 hx => hPos x9 x10 ((hCondEquiv x9 x10).mp hx), hNeg, fun b => ?_⟩
  cases b
  · simpa using hS0
  · simpa using hS13
