import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17960_1
    (hTableEquiv :
      ∀ (p l : Fin (13 : ℕ)),
        ([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)].getD (l : ℕ) (0 : ℕ)).testBit (p : ℕ) = Bool.true ↔
        (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ)) ∨ p = l + (9 : Fin (13 : ℕ))))
    (hCircuit :
      have E : Fin (13 : ℕ) → Fin (13 : ℕ) → Bool := fun p l =>
        ([(523 : ℕ), (1046 : ℕ), (2092 : ℕ), (4184 : ℕ), (177 : ℕ), (354 : ℕ), (708 : ℕ), (1416 : ℕ), (2832 : ℕ), (5664 : ℕ), (3137 : ℕ), (6274 : ℕ), (4357 : ℕ)].getD (l : ℕ) (0 : ℕ)).testBit (p : ℕ);
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (w1 w2 : ℕ),
        C.size ≤ (63 : ℕ) ∧
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        w1 ≠ w2 ∧
        w1 < (26 : ℕ) + C.size ∧
        w2 < (26 : ℕ) + C.size ∧
        (∀ (p l : Fin (13 : ℕ)), E p l = Bool.true →
          have inp : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) p) (Fin.natAdd (13 : ℕ) l);
          PEqualNP.BlindGate.wireValue C (26 : ℕ) inp w1 = Bool.true ∧
          PEqualNP.BlindGate.wireValue C (26 : ℕ) inp w2 = Bool.true) ∧
        ∀ (v : Fin ((13 : ℕ) + (13 : ℕ)) → Bool),
          (∀ (p l : Fin (13 : ℕ)), E p l = Bool.true → v (Fin.castAdd (13 : ℕ) p) = Bool.true → v (Fin.natAdd (13 : ℕ) l) = Bool.false) →
          PEqualNP.BlindGate.wireValue C (26 : ℕ) v (if v (13 : Fin ((13 : ℕ) + (13 : ℕ))) = Bool.true then w1 else w2) = Bool.false) :
    (let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Bool → Finset (Fin (13 : ℕ)) → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x2 : Bool) (x3 : Finset (Fin (13 : ℕ))) =>   have x4 : Fin (13 : ℕ) → Bool := fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3);   have x5 : Fin (13 : ℕ) → Bool := fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x3, ¬if x2 = Bool.true then x1 x6 x5 else x1 x5 x6);   if x2 = Bool.true then Fin.append x4 x5 else Fin.append x5 x4; ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : ℕ),   x3.size ≤ (63 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x6 ∈ x3.gates, x6.inputs.Nodup) ∧         x4 ≠ x5 ∧           x4 < (26 : ℕ) + x3.size ∧             x5 < (26 : ℕ) + x3.size ∧               (∀ (x6 x7 : Fin (13 : ℕ)),                   x1 x6 x7 →                     have x9 : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x6) (Fin.natAdd (13 : ℕ) x7);                     PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x9 x4 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x9 x5 = Bool.true) ∧                 ∀ (x6 : Bool) (x7 : Finset (Fin (13 : ℕ))), x7.card ≤ (3 : ℕ) → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) (x2 x6 x7) (if x2 x6 x7 (13 : Fin ((13 : ℕ) + (13 : ℕ))) = Bool.true then x4 else x5) = Bool.false) := by
  dsimp only
  refine Exists.elim hCircuit fun C hC => Exists.elim hC fun w1 hw1 => Exists.elim hw1 fun w2 h => ?_
  refine ⟨C, w1, w2, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    fun p l hpl => h.2.2.2.2.2.2.1 p l ((hTableEquiv p l).mpr hpl), ?_⟩
  intro b S _
  refine h.2.2.2.2.2.2.2 _ fun p l hpl hp => Bool.eq_false_iff.mpr fun hl => ?_
  cases b
  · rw [if_neg Bool.false_ne_true, Fin.append_left] at hp
    rw [if_neg Bool.false_ne_true, Fin.append_right] at hl
    exact (of_decide_eq_true hp) l (of_decide_eq_true hl) (Eq.mpr (if_neg Bool.false_ne_true) ((hTableEquiv p l).mp hpl))
  · rw [if_pos rfl, Fin.append_left] at hp
    rw [if_pos rfl, Fin.append_right] at hl
    exact (of_decide_eq_true hl) p (of_decide_eq_true hp) (Eq.mpr (if_pos rfl) ((hTableEquiv p l).mp hpl))
