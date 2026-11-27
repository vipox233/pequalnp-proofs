import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7971_4
    (hWireBoundsAndNe :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (S : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) =>
        PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) S ∧
        S.toRight.card ≤ (3 : ℕ) ∧
        (∀ (l : Fin (13 : ℕ)), (S.toLeft ∩ x1 l).card ≤ (2 : ℕ)) ∧
        ∀ (p : Fin (13 : ℕ)), {l ∈ S.toRight | p ∈ x1 l}.card ≤ (2 : ℕ);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) (S : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) =>
        (C.wires (PEqualNP.GenericRejection.incidenceInput S.toLeft S.toRight)).getD w Bool.false;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        (∀ (p l : Fin (13 : ℕ)), p ∈ x1 l → (x3 C u {Sum.inl p, Sum.inr l} && x3 C v {Sum.inl p, Sum.inr l}) = Bool.true) →
        (∀ (S1 S2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), S1.card ≤ (2 : ℕ) → S2.card ≤ (2 : ℕ) → x2 (S1 ∪ S2) → (x3 C u S1 && x3 C v S2) = Bool.false) →
        (∃ (T : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), T.card ≤ (2 : ℕ) ∧ x2 T ∧ x3 C u T = Bool.true) →
        u < (26 : ℕ) + C.size ∧ v < (26 : ℕ) + C.size ∧ u ≠ v)
    (hOrderedLB :
      have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3;
      have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (S : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) =>
        PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) S ∧
        S.toRight.card ≤ (3 : ℕ) ∧
        (∀ (l : Fin (13 : ℕ)), (S.toLeft ∩ x1 l).card ≤ (2 : ℕ)) ∧
        ∀ (p : Fin (13 : ℕ)), {l ∈ S.toRight | p ∈ x1 l}.card ≤ (2 : ℕ);
      have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ) (S : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) =>
        (C.wires (PEqualNP.GenericRejection.incidenceInput S.toLeft S.toRight)).getD w Bool.false;
      have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        ¬∃ (a b : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          PEqualNP.EdgeOwnership.InCone (26 : ℕ) C a b;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (u v : ℕ),
        (u < v ∧ v < (26 : ℕ) + C.size ∧ PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C ∧ x4 C) →
        (∀ (p l : Fin (13 : ℕ)), p ∈ x1 l → (x3 C u {Sum.inl p, Sum.inr l} && x3 C v {Sum.inl p, Sum.inr l}) = Bool.true) →
        (∀ (S1 S2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), S1.card ≤ (2 : ℕ) ∧ S2.card ≤ (2 : ℕ) ∧ x2 (S1 ∪ S2) → (x3 C u S1 && x3 C v S2) = Bool.false) →
        (∀ w ∈ [u, v], ∃ (T : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), T.card ≤ (2 : ℕ) ∧ x2 T ∧ x3 C w T = Bool.true) →
        (63 : ℕ) ≤ C.size) :
    have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Prop := fun (x2 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => PEqualNP.HeptadCover.IsFree (PEqualNP.HeptadCover.incidences x1) x2 ∧ x2.toRight.card ≤ (3 : ℕ) ∧ (∀ (x3 : Fin (13 : ℕ)), (x2.toLeft ∩ x1 x3).card ≤ (2 : ℕ)) ∧ ∀ (x3 : Fin (13 : ℕ)), {x4 ∈ x2.toRight | x3 ∈ x1 x4}.card ≤ (2 : ℕ); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))) => (x3.wires (PEqualNP.GenericRejection.incidenceInput x5.toLeft x5.toRight)).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ¬∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x5 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 →       x4 x5 →         (∀ (x11 x12 : Fin (13 : ℕ)),             x11 ∈ x1 x12 →               have x14 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ)) := {Sum.inl x11, Sum.inr x12};               (x3 x5 x6 x14 && x3 x5 x7 x14) = Bool.true) →           (∀ (x12 x13 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x12.card ≤ (2 : ℕ) → x13.card ≤ (2 : ℕ) → x2 (x12 ∪ x13) → (x3 x5 x6 x12 && x3 x5 x7 x13) = Bool.false) → (∀ x13 ∈ [x6, x7], ∃ (x15 : Finset (Fin (13 : ℕ) ⊕ Fin (13 : ℕ))), x15.card ≤ (2 : ℕ) ∧ x2 x15 ∧ x3 x5 x13 x15 = Bool.true) → (63 : ℕ) ≤ x5.size :=
  fun x5 x6 x7 hM hRB hNoNest hPos hNeg hWit =>
    have hB := hWireBoundsAndNe x5 x6 x7 hPos hNeg (hWit x6 List.mem_cons_self)
    Or.elim (Nat.lt_or_gt_of_ne hB.2.2)
      (fun hlt => hOrderedLB x5 x6 x7 ⟨hlt, hB.2.1, hM, hRB, hNoNest⟩ hPos (fun S1 S2 h => hNeg S1 S2 h.1 h.2.1 h.2.2) hWit)
      (fun hgt => hOrderedLB x5 x7 x6 ⟨hgt, hB.1, hM, hRB, hNoNest⟩
        (fun p l hpl => Eq.trans (Bool.and_comm _ _) (hPos p l hpl))
        (fun S1 S2 h => Eq.trans (Bool.and_comm _ _) (hNeg S2 S1 h.2.1 h.1 (Finset.union_comm S1 S2 ▸ h.2.2)))
        (fun w hw => hWit w (Or.elim (List.mem_cons.mp hw)
          (fun he => List.mem_cons_of_mem x6 (List.mem_cons.mpr (Or.inl he)))
          (fun hr => List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr))))))
