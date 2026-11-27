import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7788_3
    (hAppendTopOr : let pairIn : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (u v : Fin (26 : ℕ)) => List.ofFn fun (k : Fin (26 : ℕ)) => Decidable.decide (k = u ∨ k = v);
    let nestedAnd : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs, (26 : ℕ) ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and;
    ∀ (f : Fin (26 : ℕ) → Fin (26 : ℕ) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (w1 w2 : ℕ),
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) C →
      w1 < (26 : ℕ) + C.size →
      w2 < (26 : ℕ) + C.size →
      (∀ (u v : Fin (26 : ℕ)), ((C.wires (pairIn u v)).getD w1 Bool.false || (C.wires (pairIn u v)).getD w2 Bool.false) = f u v) →
      (∃ g1 ∈ Finset.range C.size, ∃ g2 ∈ Finset.range C.size, g1 ≠ g2 ∧ nestedAnd C g1 ∧ nestedAnd C g2 ∧ ∀ g ∈ Finset.range C.size, nestedAnd C g → g = g1 ∨ g = g2) →
      ∃ (D : PEqualNP.CircuitLowerBounds.Circuit),
        D.size = C.size + (1 : ℕ) ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) D ∧
        D.output = (26 : ℕ) + C.size ∧
        (∀ (u v : Fin (26 : ℕ)), D.eval (pairIn u v) = f u v) ∧
        (∃ g1 ∈ Finset.range D.size, ∃ g2 ∈ Finset.range D.size, g1 ≠ g2 ∧ nestedAnd D g1 ∧ nestedAnd D g2 ∧ ∀ g ∈ Finset.range D.size, nestedAnd D g → g = g1 ∨ g = g2))
    (hSingleOut64 : let adj : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (u v : Fin (26 : ℕ)) => ∃ (p l : Fin (13 : ℕ)), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ (u = Fin.castAdd (13 : ℕ) p ∧ v = Fin.natAdd (13 : ℕ) l ∨ v = Fin.castAdd (13 : ℕ) p ∧ u = Fin.natAdd (13 : ℕ) l);
    let pairIn : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (u v : Fin (26 : ℕ)) => List.ofFn fun (k : Fin (26 : ℕ)) => Decidable.decide (k = u ∨ k = v);
    let nestedAnd : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (g : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs, (26 : ℕ) ≤ w ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - (26 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and;
    ∀ (D : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 D →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) D →
      (∀ (u v : Fin (26 : ℕ)), D.eval (pairIn u v) = Decidable.decide (adj u v)) →
      (∃ g1 ∈ Finset.range D.size, ∃ g2 ∈ Finset.range D.size, g1 ≠ g2 ∧ nestedAnd D g1 ∧ nestedAnd D g2 ∧ ∀ g ∈ Finset.range D.size, nestedAnd D g → g = g1 ∨ g = g2) →
      (64 : ℕ) ≤ D.size) :
    let x1 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x1 x2 : Fin (26 : ℕ)) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ (x1 = Fin.castAdd (13 : ℕ) x3 ∧ x2 = Fin.natAdd (13 : ℕ) x4 ∨ x2 = Fin.castAdd (13 : ℕ) x3 ∧ x1 = Fin.natAdd (13 : ℕ) x4); have x2 : Fin (26 : ℕ) → Fin (26 : ℕ) → List Bool := fun (x2 x3 : Fin (26 : ℕ)) => List.ofFn fun (x4 : Fin (26 : ℕ)) => Decidable.decide (x4 = x2 ∨ x4 = x3); have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → List Bool → Bool := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : ℕ) (x5 : List Bool) => (x3.wires x5).getD x4 Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt; have x5 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : ℕ) =>   have x7 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;   (x4 x5 x6).op = x7 ∧ ∃ x8 ∈ (x4 x5 x6).inputs, (26 : ℕ) ≤ x8 ∧ (x4 x5 (x8 - (26 : ℕ))).op = x7; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 x8 : ℕ), PEqualNP.MetaComplexity.Monotone2 x6 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x6 → x7 < (26 : ℕ) + x6.size → x8 < (26 : ℕ) + x6.size → (∀ (x13 x14 : Fin (26 : ℕ)), (x3 x6 x7 (x2 x13 x14) || x3 x6 x8 (x2 x13 x14)) = Decidable.decide (x1 x13 x14)) → (∃ (x14 : Fin (26 : ℕ)) (x15 : Fin (26 : ℕ)), x3 x6 x7 (x2 x14 x15) = Bool.true ∧ x3 x6 x8 (x2 x14 x15) = Bool.false) → (∃ (x15 : Fin (26 : ℕ)) (x16 : Fin (26 : ℕ)), x3 x6 x8 (x2 x15 x16) = Bool.true ∧ x3 x6 x7 (x2 x15 x16) = Bool.false) → (∃ x16 ∈ Finset.range x6.size, ∃ x17 ∈ Finset.range x6.size, x16 ≠ x17 ∧ x5 x6 x16 ∧ x5 x6 x17 ∧ ∀ x18 ∈ Finset.range x6.size, x5 x6 x18 → x18 = x16 ∨ x18 = x17) → (63 : ℕ) ≤ x6.size :=
  fun x6 x7 x8 hM hR hw1 hw2 hOr _ _ hNest =>
    Exists.elim (hAppendTopOr (fun u v => Decidable.decide (∃ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 ∧ (u = Fin.castAdd (13 : ℕ) x3 ∧ v = Fin.natAdd (13 : ℕ) x4 ∨ v = Fin.castAdd (13 : ℕ) x3 ∧ u = Fin.natAdd (13 : ℕ) x4))) x6 x7 x8 hM hR hw1 hw2 hOr hNest)
      fun D hD =>
        Nat.le_of_succ_le_succ
          (Eq.subst (motive := fun n => (64 : ℕ) ≤ n) hD.1
            (hSingleOut64 D hD.2.1 hD.2.2.1 hD.2.2.2.2.1 hD.2.2.2.2.2))
