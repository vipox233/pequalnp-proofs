import Mathlib.Combinatorics.SimpleGraph.Acyclic
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17451_1
    (hNonempty : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x6 : SimpleGraph (Fin (x1 + x2))),
      (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) →
      ¬x6.IsAcyclic →
      (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 ∨ x12.2 = x14.2 → x12 = x14) →
      x4 ⊆ x3 →
      ∃ e : Fin x1 × Fin x2, e ∈ x3 \ x4)
    (hMaxMatchCover : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)),
      x4 ⊆ x3 →
      (∀ x17 ∈ x3 \ x4, ∃ x19 ∈ x4, x19.1 = x17.1 ∨ x19.2 = x17.2) →
      ∃ V : Finset (Fin (x1 + x2)),
        (∀ e ∈ x3, Fin.castAdd x2 e.1 ∈ V ∨ Fin.natAdd x1 e.2 ∈ V) ∧
        V.card ≤ 2 * x4.card)
    (hEdgeShrink : ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),
      have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);
      have x8 : Prop :=
        ∃ (x8 : Fin (x1 + x2)),
          have x9 : ℕ := (x6.neighborSet x8).ncard;
          have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;
          (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);
      (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) →
      ¬x6.IsAcyclic → x7 x3 x5 →
      (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 ∨ x12.2 = x14.2 → x12 = x14) →
      x4 ⊆ x3 →
      (∀ (x14 x15 : Fin x1) (x16 x17 : Fin x2), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x3 ∧ (x14, x17) ∈ x3 ∧ (x15, x16) ∈ x3 ∧ (x15, x17) ∈ x3)) →
      (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) →
      ¬x8 →
      (∀ x17 ∈ x3 \ x4, ∃ x19 ∈ x4, x19.1 = x17.1 ∨ x19.2 = x17.2) →
      (∀ x18 ∈ x3 \ x4, ∀ (x20 : Finset (Fin (x1 + x2))), (∀ x21 ∈ x3.erase x18, Fin.castAdd x2 x21.1 ∈ x20 ∨ Fin.natAdd x1 x21.2 ∈ x20) → x5.size ≤ (x3.erase x18).card + x20.card - (1 : ℕ)) →
      (x3 \ x4).Nonempty →
      x5.size ≤ (x3.card - (1 : ℕ)) + (2 : ℕ) * x4.card - (1 : ℕ) →
      ∃ x19 ∈ x3, x19 ∉ x4 ∧ ∃ (x20 : PEqualNP.CircuitLowerBounds.Circuit), x20.size < x5.size ∧ x7 (x3.erase x19) x20) :
    (∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : SimpleGraph (Fin (x1 + x2))),   have x7 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧ ∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true);   have x8 : Prop :=     ∃ (x8 : Fin (x1 + x2)),       have x9 : ℕ := (x6.neighborSet x8).ncard;       have x10 : Finset ℕ := PEqualNP.TopForm.readers (0 : ℕ) x5 ↑x8;       (2 : ℕ) ≤ x9 ∧ (x9 < x10.card ∨ x9 = x10.card ∧ ∃ x11 ∈ x10, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.readers (x1 + x2) x5 x11 ⊆ x10);   (∀ (x9 x10 : Fin (x1 + x2)), x6.Adj x9 x10 ↔ ∃ x11 ∈ x3, x9 = Fin.castAdd x2 x11.1 ∧ x10 = Fin.natAdd x1 x11.2 ∨ x10 = Fin.castAdd x2 x11.1 ∧ x9 = Fin.natAdd x1 x11.2) → ¬x6.IsAcyclic → x7 x3 x5 → (∀ x12 ∈ x4, ∀ x14 ∈ x4, x12.1 = x14.1 ∨ x12.2 = x14.2 → x12 = x14) → x4 ⊆ x3 → (∀ (x14 x15 : Fin x1) (x16 x17 : Fin x2), x14 ≠ x15 → x16 ≠ x17 → ¬((x14, x16) ∈ x3 ∧ (x14, x17) ∈ x3 ∧ (x15, x16) ∈ x3 ∧ (x15, x17) ∈ x3)) → (∀ x15 ∈ x3, ((∀ x17 ∈ x3, x17.1 = x15.1 → x17 = x15) ∨ ∀ x17 ∈ x3, x17.2 = x15.2 → x17 = x15) → (x3.erase x15).Nonempty → x15 ∈ x4) → ¬x8 → (∀ x17 ∈ x3 \ x4, ∃ x19 ∈ x4, x19.1 = x17.1 ∨ x19.2 = x17.2) → (∀ x18 ∈ x3 \ x4, ∀ (x20 : Finset (Fin (x1 + x2))), (∀ x21 ∈ x3.erase x18, Fin.castAdd x2 x21.1 ∈ x20 ∨ Fin.natAdd x1 x21.2 ∈ x20) → x5.size ≤ (x3.erase x18).card + x20.card - (1 : ℕ)) → ∃ x19 ∈ x3, x19 ∉ x4 ∧ ∃ (x20 : PEqualNP.CircuitLowerBounds.Circuit), x20.size < x5.size ∧ x7 (x3.erase x19) x20) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 hAdj hCyc hFun hMatch hSub hC4 hDeg1 hNot8 hMax hBound
  exact Exists.elim (hNonempty x1 x2 x3 x4 x6 hAdj hCyc hMatch hSub) fun e he =>
    Exists.elim (hMaxMatchCover x1 x2 x3 x4 hSub hMax) fun V hV =>
      have he3 : e ∈ x3 := (Finset.mem_sdiff.mp he).1
      have hEraseCard : (x3.erase e).card = x3.card - 1 := Finset.card_erase_of_mem he3
      have hVcov : ∀ e' ∈ x3.erase e, Fin.castAdd x2 e'.1 ∈ V ∨ Fin.natAdd x1 e'.2 ∈ V :=
        fun e' he' => hV.1 e' (Finset.mem_of_mem_erase he')
      have hSz := hBound e he V hVcov
      have hVcard : V.card ≤ 2 * x4.card := hV.2
      hEdgeShrink x1 x2 x3 x4 x5 x6 hAdj hCyc hFun hMatch hSub hC4 hDeg1 hNot8 hMax hBound
        ⟨e, he⟩ (by omega)
