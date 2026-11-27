import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18814_2
    (hGaloisLift :
      let x1 : Fin (12 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 : Fin (12 : ℕ)) (x2 : Fin (13 : ℕ)) => x1.succ = x2 ∨ x1.succ = x2 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (9 : Fin ((12 : ℕ) + (1 : ℕ)));
      have x3 : Finset (Fin (12 : ℕ)) → Fin (25 : ℕ) → Bool := fun (x3 : Finset (Fin (12 : ℕ))) (x4 : Fin (25 : ℕ)) => Fin.addCases (fun (x5 : Fin (12 : ℕ)) => Decidable.decide (x5 ∈ x3)) (fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬x1 x6 x5)) x4;
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List ℕ),
        PEqualNP.MetaComplexity.Monotone2 x4 →
        have x9 : (Fin (25 : ℕ) → Bool) → Bool := fun (x9 : Fin (25 : ℕ) → Bool) => (List.map (fun (x10 : ℕ) => (x4.wires (List.ofFn x9)).getD x10 Bool.false) x5).any id;
        (∃ (v : Fin (25 : ℕ) → Bool),
          (∀ (p : Fin (12 : ℕ)) (l : Fin (13 : ℕ)), x1 p l → v (Fin.castAdd (13 : ℕ) p) = Bool.true → v (Fin.natAdd (12 : ℕ) l) = Bool.true → False) ∧
          x9 v = Bool.true) →
        ∃ (x11 : Finset (Fin (12 : ℕ))),
          (∀ x12 ∉ x11, ∃ (x14 : Fin (13 : ℕ)), x1 x12 x14 ∧ ∀ x15 ∈ x11, ¬x1 x15 x14) ∧
          x9 (x3 x11) = Bool.true)
    (hNoExact56 :
      let x1 : Fin (12 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 : Fin (12 : ℕ)) (x2 : Fin (13 : ℕ)) => x1.succ = x2 ∨ x1.succ = x2 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (9 : Fin ((12 : ℕ) + (1 : ℕ)));
      have x2 : Fin (12 : ℕ) → Fin (13 : ℕ) → Fin (25 : ℕ) → Bool := fun (x2 : Fin (12 : ℕ)) (x3 : Fin (13 : ℕ)) (x4 : Fin (25 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (12 : ℕ) x3);
      ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List ℕ),
        PEqualNP.MetaComplexity.Monotone2 x4 →
        x4.size ≤ (56 : ℕ) →
        x5.length ≤ (2 : ℕ) →
        have x9 : (Fin (25 : ℕ) → Bool) → Bool := fun (x9 : Fin (25 : ℕ) → Bool) => (List.map (fun (x10 : ℕ) => (x4.wires (List.ofFn x9)).getD x10 Bool.false) x5).any id;
        (∀ (x10 : Fin (12 : ℕ)) (x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 (x2 x10 x11) = Bool.true) →
        ∃ (v : Fin (25 : ℕ) → Bool),
          (∀ (p : Fin (12 : ℕ)) (l : Fin (13 : ℕ)), x1 p l → v (Fin.castAdd (13 : ℕ) p) = Bool.true → v (Fin.natAdd (12 : ℕ) l) = Bool.true → False) ∧
          x9 v = Bool.true) :
    (let x1 : Fin (12 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 : Fin (12 : ℕ)) (x2 : Fin (13 : ℕ)) => x1.succ = x2 ∨ x1.succ = x2 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x1.succ = x2 + (9 : Fin ((12 : ℕ) + (1 : ℕ))); have x2 : Fin (12 : ℕ) → Fin (13 : ℕ) → Fin (25 : ℕ) → Bool := fun (x2 : Fin (12 : ℕ)) (x3 : Fin (13 : ℕ)) (x4 : Fin (25 : ℕ)) => Decidable.decide (x4 = Fin.castAdd (13 : ℕ) x2 ∨ x4 = Fin.natAdd (12 : ℕ) x3); have x3 : Finset (Fin (12 : ℕ)) → Fin (25 : ℕ) → Bool := fun (x3 : Finset (Fin (12 : ℕ))) (x4 : Fin (25 : ℕ)) => Fin.addCases (fun (x5 : Fin (12 : ℕ)) => Decidable.decide (x5 ∈ x3)) (fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬x1 x6 x5)) x4; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x4 →     x4.size ≤ (56 : ℕ) →       x5.length ≤ (2 : ℕ) →         have x9 : (Fin (25 : ℕ) → Bool) → Bool := fun (x9 : Fin (25 : ℕ) → Bool) => (List.map (fun (x10 : ℕ) => (x4.wires (List.ofFn x9)).getD x10 Bool.false) x5).any id;         (∀ (x10 : Fin (12 : ℕ)) (x11 : Fin (13 : ℕ)), x1 x10 x11 → x9 (x2 x10 x11) = Bool.true) → ∃ (x11 : Finset (Fin (12 : ℕ))), (∀ x12 ∉ x11, ∃ (x14 : Fin (13 : ℕ)), x1 x12 x14 ∧ ∀ x15 ∈ x11, ¬x1 x15 x14) ∧ x9 (x3 x11) = Bool.true) :=
  fun x4 x5 hM hSz hLen hPos =>
    hGaloisLift x4 x5 hM (hNoExact56 x4 x5 hM hSz hLen hPos)
