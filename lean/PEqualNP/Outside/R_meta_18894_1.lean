import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18894_1
    (hFullCircuit :
      have inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun p l => Decidable.decide (l.val ≠ (0 : ℕ) ∧ (p.val + (13 : ℕ) - l.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]);
      have infPt : Fin (13 : ℕ) → Bool := fun p => Decidable.decide (p.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]);
      ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (13 : ℕ) → ℕ),
        x3.size ≤ (50 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧
        (∀ x5 ∈ x3.gates, x5.inputs.Nodup) ∧
        x3.output < (26 : ℕ) + x3.size ∧
        (∀ x5 ∈ PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)), x4 x5 < (26 : ℕ) + x3.size ∧ x4 x5 ≠ ↑x5) ∧
        ∀ (v : Fin (26 : ℕ) → Bool),
          (PEqualNP.BlindGate.wireValue x3 (26 : ℕ) v x3.output = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)), infPt p = Bool.false ∧ inc p l = Bool.true ∧ v (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ v (Fin.natAdd (13 : ℕ) l) = Bool.true) ∧
          ∀ (p : Fin (13 : ℕ)), infPt p = Bool.true →
            (PEqualNP.BlindGate.wireValue x3 (26 : ℕ) v (x4 p) = Bool.true ↔
              ∃ (l : Fin (13 : ℕ)), inc p l = Bool.true ∧ v (Fin.natAdd (13 : ℕ) l) = Bool.true))
    (hSound :
      have x1 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ));
      have inc : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun p l => Decidable.decide (l.val ≠ (0 : ℕ) ∧ (p.val + (13 : ℕ) - l.val) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]);
      have infPt : Fin (13 : ℕ) → Bool := fun p => Decidable.decide (p.val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]);
      let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 x4 : Fin (13 : ℕ)) => x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ if x2 ∈ x1 then x3 = x2 else x3 ∉ x1;
      ∀ (eval : (Fin (26 : ℕ) → Bool) → ℕ → Bool) (out : ℕ) (x4 : Fin (13 : ℕ) → ℕ),
        (∀ (v : Fin (26 : ℕ) → Bool),
          (eval v out = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)), infPt p = Bool.false ∧ inc p l = Bool.true ∧ v (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ v (Fin.natAdd (13 : ℕ) l) = Bool.true) ∧
          ∀ (p : Fin (13 : ℕ)), infPt p = Bool.true →
            (eval v (x4 p) = Bool.true ↔
              ∃ (l : Fin (13 : ℕ)), inc p l = Bool.true ∧ v (Fin.natAdd (13 : ℕ) l) = Bool.true)) →
        ∀ (x5 : Fin (13 : ℕ)),
          have x6 : ℕ := if x5 ∈ x1 then x4 x5 else out;
          (∀ (x7 x8 : Fin (13 : ℕ)), x2 x5 x7 x8 → eval (fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.natAdd (13 : ℕ) x8 ∨ x5 ∉ x1 ∧ x10 = Fin.castAdd (13 : ℕ) x7)) x6 = Bool.true) ∧
          ∀ (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x7, x8 ∉ x1) → (x5 ∈ x1 → x7 = x1ᶜ) → eval (fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x7 ∨ x11 ∈ x1)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide ¬∃ (x12 : Fin (13 : ℕ)), x2 x5 x12 x11 ∧ (x12 ∈ x7 ∨ x5 ∈ x1)) x10) x6 = Bool.false) :
    (have x1 : Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3 (0 : Fin (13 : ℕ)); let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 x4 : Fin (13 : ℕ)) => x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ if x2 ∈ x1 then x3 = x2 else x3 ∉ x1; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (13 : ℕ) → ℕ),   x3.size ≤ (50 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x5 ∈ x3.gates, x5.inputs.Nodup) ∧         x3.output < (26 : ℕ) + x3.size ∧           (∀ x5 ∈ x1, x4 x5 < (26 : ℕ) + x3.size ∧ x4 x5 ≠ ↑x5) ∧             ∀ (x5 : Fin (13 : ℕ)),               have x6 : ℕ := if x5 ∈ x1 then x4 x5 else x3.output;               (∀ (x7 x8 : Fin (13 : ℕ)), x2 x5 x7 x8 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.natAdd (13 : ℕ) x8 ∨ x5 ∉ x1 ∧ x10 = Fin.castAdd (13 : ℕ) x7)) x6 = Bool.true) ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), (∀ x8 ∈ x7, x8 ∉ x1) → (x5 ∈ x1 → x7 = x1ᶜ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (fun (x10 : Fin (26 : ℕ)) => Fin.addCases (fun (x11 : Fin (13 : ℕ)) => Decidable.decide (x11 ∈ x7 ∨ x11 ∈ x1)) (fun (x11 : Fin (13 : ℕ)) => Decidable.decide ¬∃ (x12 : Fin (13 : ℕ)), x2 x5 x12 x11 ∧ (x12 ∈ x7 ∨ x5 ∈ x1)) x10) x6 = Bool.false) :=
  Exists.elim hFullCircuit fun x3 hx3 =>
    Exists.elim hx3 fun x4 hx4 =>
      ⟨x3, x4, hx4.1, hx4.2.1, hx4.2.2.1, hx4.2.2.2.1, hx4.2.2.2.2.1,
        hSound (PEqualNP.BlindGate.wireValue x3 (26 : ℕ)) x3.output x4 hx4.2.2.2.2.2⟩
