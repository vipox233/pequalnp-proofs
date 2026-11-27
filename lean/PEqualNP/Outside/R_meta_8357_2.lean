import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8357_2
    (hDirectRead :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ 27 →
        x1.output + 1 = 14 + x1.size →
        PEqualNP.TopForm.IsAO2 14 x1 →
        (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
        (∀ x6 : Fin 14 → Bool,
          x1.eval (List.ofFn x6) = true ↔
            ∃ (x7 x8 : Fin 7),
              (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3) ∧
              x6 (Fin.castAdd 7 x7) = true ∧
              x6 (Fin.natAdd 7 x8) = true) →
        have w : ℕ → Fin 14 → Fin 14 → Bool := fun k a b =>
          PEqualNP.CleanedNonEdge.wireVal 14 x1 k (PEqualNP.EdgeOwnership.pairInput a b);
        have x7 : ℕ → Bool := fun k => w k 0 7;
        have x8 : ℕ → Bool := fun k => w k 0 0;
        have x9 : ℕ → Bool := fun k => w k 7 7;
        have x10 : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd x1;
        have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 14 x1;
        have x12 : ℕ → Prop := fun g =>
          (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x7 (14 + g) = true ∧ x8 (14 + g) = false ∧ x9 (14 + g) = false;
        ∀ x14 x15 x25 : ℕ, x14 < x15 → ¬x11 x14 x15 → ¬x11 x15 x14 → x11 x14 (x1.size - 1) → x11 x15 (x1.size - 1) →
          x12 x14 → x12 x15 → (∀ i : Fin 2, x8 (x10 x14 i) = false) → (∀ i : Fin 2, x9 (x10 x15 i) = false) →
          x12 x25 → (∀ i : Fin 2, x8 (x10 x25 i) = true ∨ x9 (x10 x25 i) = true) →
          x11 x25 x14 → x11 x25 x15 →
          (∃ i : Fin 2, x9 (x10 x14 i) = true) → (∃ i : Fin 2, x8 (x10 x15 i) = true) →
          (∃ i : Fin 2, 14 + x25 = x10 x14 i ∨ 14 + x25 = x10 x15 i) → False)
    (hIndirectBoth :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
        x1.size ≤ 27 →
        x1.output + 1 = 14 + x1.size →
        PEqualNP.TopForm.IsAO2 14 x1 →
        (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →
        (∀ x6 : Fin 14 → Bool,
          x1.eval (List.ofFn x6) = true ↔
            ∃ (x7 x8 : Fin 7),
              (x7 = x8 ∨ x7 = x8 + 1 ∨ x7 = x8 + 3) ∧
              x6 (Fin.castAdd 7 x7) = true ∧
              x6 (Fin.natAdd 7 x8) = true) →
        have w : ℕ → Fin 14 → Fin 14 → Bool := fun k a b =>
          PEqualNP.CleanedNonEdge.wireVal 14 x1 k (PEqualNP.EdgeOwnership.pairInput a b);
        have x7 : ℕ → Bool := fun k => w k 0 7;
        have x8 : ℕ → Bool := fun k => w k 0 0;
        have x9 : ℕ → Bool := fun k => w k 7 7;
        have x10 : ℕ → Fin 2 → ℕ := PEqualNP.TopForm.opnd x1;
        have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 14 x1;
        have x12 : ℕ → Prop := fun g =>
          (PEqualNP.MetaComplexity.NestedCover.gateAt x1 g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          x7 (14 + g) = true ∧ x8 (14 + g) = false ∧ x9 (14 + g) = false;
        ∀ x14 x15 x25 : ℕ, x14 < x15 → ¬x11 x14 x15 → ¬x11 x15 x14 → x11 x14 (x1.size - 1) → x11 x15 (x1.size - 1) →
          x12 x14 → x12 x15 → (∀ i : Fin 2, x8 (x10 x14 i) = false) → (∀ i : Fin 2, x9 (x10 x15 i) = false) →
          x12 x25 → (∀ i : Fin 2, x8 (x10 x25 i) = true ∨ x9 (x10 x25 i) = true) →
          x11 x25 x14 → x11 x25 x15 →
          (∃ i : Fin 2, x9 (x10 x14 i) = true) → (∃ i : Fin 2, x8 (x10 x15 i) = true) →
          (∀ i : Fin 2, 14 + x25 ≠ x10 x14 i ∧ 14 + x25 ≠ x10 x15 i) → False) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     x1.output + (1 : ℕ) = (14 : ℕ) + x1.size →       PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →         (∀ x5 ∈ x1.gates, x5.inputs.Nodup) →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             have x7 : ℕ → Bool := fun (x7 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x7 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));             have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x8 (PEqualNP.EdgeOwnership.pairInput (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)));             have x9 : ℕ → Bool := fun (x9 : ℕ) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x9 (PEqualNP.EdgeOwnership.pairInput (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)));             have x10 : ℕ → Fin (2 : ℕ) → ℕ := PEqualNP.TopForm.opnd x1;             have x11 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1;             have x12 : ℕ → Prop := fun (x12 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x7 ((14 : ℕ) + x12) = Bool.true ∧ x8 ((14 : ℕ) + x12) = Bool.false ∧ x9 ((14 : ℕ) + x12) = Bool.false;             have x13 : ℕ → Prop := fun (x13 : ℕ) => x12 x13 ∧ ∀ (x14 : Fin (2 : ℕ)), x8 (x10 x13 x14) = Bool.true ∨ x9 (x10 x13 x14) = Bool.true;             ∀ (x14 x15 : ℕ), x14 < x15 → ¬x11 x14 x15 → ¬x11 x15 x14 → x11 x14 (x1.size - (1 : ℕ)) → x11 x15 (x1.size - (1 : ℕ)) → x12 x14 → x12 x15 → (∀ (x23 : Fin (2 : ℕ)), x8 (x10 x14 x23) = Bool.false) → (∀ (x24 : Fin (2 : ℕ)), x9 (x10 x15 x24) = Bool.false) → (∃ (x25 : ℕ), x13 x25 ∧ x11 x25 x14 ∧ x11 x25 x15 ∧ (∃ (x26 : Fin (2 : ℕ)), x9 (x10 x14 x26) = Bool.true) ∧ ∃ (x26 : Fin (2 : ℕ)), x8 (x10 x15 x26) = Bool.true) → False) := by
  intro x1 hSz hOut hAO hNd hEv x7 x8 x9 x10 x11 x12 x13 x14 x15 hlt hni1 hni2 hc1 hc2 h12a h12b h8a h9b hEx
  exact Exists.elim hEx fun x25 hx25 =>
    Or.elim (Classical.em (∃ i : Fin (2 : ℕ), (14 : ℕ) + x25 = x10 x14 i ∨ (14 : ℕ) + x25 = x10 x15 i))
      (fun hDir => hDirectRead x1 hSz hOut hAO hNd hEv x14 x15 x25 hlt hni1 hni2 hc1 hc2 h12a h12b h8a h9b hx25.1.1 hx25.1.2 hx25.2.1 hx25.2.2.1 hx25.2.2.2.1 hx25.2.2.2.2 hDir)
      (fun hNoDir => hIndirectBoth x1 hSz hOut hAO hNd hEv x14 x15 x25 hlt hni1 hni2 hc1 hc2 h12a h12b h8a h9b hx25.1.1 hx25.1.2 hx25.2.1 hx25.2.2.1 hx25.2.2.2.1 hx25.2.2.2.2
        (fun i => And.intro (fun h => hNoDir ⟨i, Or.inl h⟩) (fun h => hNoDir ⟨i, Or.inr h⟩)))
