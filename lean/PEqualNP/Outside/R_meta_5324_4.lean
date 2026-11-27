import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5324_4
    (hBuildSandwich :
      ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2))
        (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)),
        PEqualNP.TopForm.IsAO2 (x1 + x2) x6 →
        x7.Nonempty →
        (∀ p ∈ x7, ∀ z : Fin (x1 + x2) → Bool,
          (x6.wires (List.ofFn z)).getD p.1 Bool.false = Bool.true →
          (x6.wires (List.ofFn z)).getD p.2 Bool.false = Bool.true →
          ∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3 ∧ z (Fin.castAdd x2 a) = Bool.true ∧ z (Fin.natAdd x1 b) = Bool.true) →
        (∀ e ∈ x4, e ∈ x3 ∧ ∃ p ∈ x7,
          (x6.wires (List.ofFn fun i : Fin (x1 + x2) => Decidable.decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x1 e.2))).getD p.1 Bool.false = Bool.true ∧
          (x6.wires (List.ofFn fun i : Fin (x1 + x2) => Decidable.decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x1 e.2))).getD p.2 Bool.false = Bool.true) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsAO2 (x1 + x2) D ∧
          D.size + (1 : ℕ) ≤ x6.size + (2 : ℕ) * x7.card ∧
          (∀ e ∈ x4, PEqualNP.MetaComplexity.circuitFun (x1 + x2) D
            (fun i : Fin (x1 + x2) => Decidable.decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x1 e.2)) = Bool.true) ∧
          (∀ z : Fin (x1 + x2) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x2) D z = Bool.true →
            ∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3 ∧ z (Fin.castAdd x2 a) = Bool.true ∧ z (Fin.natAdd x1 b) = Bool.true))
    (hSandwichCover :
      ∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (a a' : Fin x1) (b b' : Fin x2), a ≠ a' → b ≠ b' →
          ¬((a, b) ∈ x3 ∧ (a, b') ∈ x3 ∧ (a', b) ∈ x3 ∧ (a', b') ∈ x3)) →
        x4 ⊆ x3 →
        PEqualNP.TopForm.IsAO2 (x1 + x2) D →
        (∀ e ∈ x4, PEqualNP.MetaComplexity.circuitFun (x1 + x2) D
          (fun i : Fin (x1 + x2) => Decidable.decide (i = Fin.castAdd x2 e.1 ∨ i = Fin.natAdd x1 e.2)) = Bool.true) →
        (∀ z : Fin (x1 + x2) → Bool, PEqualNP.MetaComplexity.circuitFun (x1 + x2) D z = Bool.true →
          ∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3 ∧ z (Fin.castAdd x2 a) = Bool.true ∧ z (Fin.natAdd x1 b) = Bool.true) →
        ∃ (U : Finset (Fin x1)) (V : Finset (Fin x2)),
          (∀ e ∈ x4, e.1 ∈ U ∨ e.2 ∈ V) ∧
          x4.card + U.card + V.card ≤ D.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 x4 x5 : Finset (Fin x1 × Fin x2)) (x6 : PEqualNP.CircuitLowerBounds.Circuit) (x7 : Finset (ℕ × ℕ)), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x3 ∧ (x8, x11) ∈ x3 ∧ (x9, x10) ∈ x3 ∧ (x9, x11) ∈ x3)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x6 → (∀ x10 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD (x1 + x2 + x10) Bool.false = Bool.true ∧ ¬∃ (x14 : Fin x1) (x15 : Fin x2), (x14, x15) ∈ x3 ∧ x13 (Fin.castAdd x2 x14) = Bool.true ∧ x13 (Fin.natAdd x1 x15) = Bool.true) → (∀ x11 ∈ x7, ∀ (x13 : Fin (x1 + x2) → Bool), (x6.wires (List.ofFn x13)).getD x11.1 Bool.false = Bool.true → (x6.wires (List.ofFn x13)).getD x11.2 Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x2), (x16, x17) ∈ x3 ∧ x13 (Fin.castAdd x2 x16) = Bool.true ∧ x13 (Fin.natAdd x1 x17) = Bool.true) → (∀ x12 ∈ x4, x12 ∈ x3 ∧ ∃ x14 ∈ x7, (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.1 Bool.false = Bool.true ∧ (x6.wires (List.ofFn fun (x15 : Fin (x1 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x12.1 ∨ x15 = Fin.natAdd x1 x12.2))).getD x14.2 Bool.false = Bool.true) → x5 ⊆ x4 → (∀ x14 ∈ x5, ∀ x16 ∈ x5, x14.1 = x16.1 → x14 = x16) → (∀ x15 ∈ x5, ∀ x17 ∈ x5, x15.2 = x17.2 → x15 = x17) → x4.card + x5.card ≤ x6.size + (2 : ℕ) * x7.card := by
  classical
  intro n m E3 E4 E5 C P hc4 hAO _ hSafe hCov4 hSub5 hM1 hM2
  by_cases h4e : E4 = ∅
  · subst h4e
    have h5e : E5 = ∅ := Finset.subset_empty.mp hSub5
    subst h5e
    simp
  have h4ne : E4.Nonempty := Finset.nonempty_iff_ne_empty.mpr h4e
  have hPne : P.Nonempty := by
    obtain ⟨e, he⟩ := h4ne
    obtain ⟨_, p, hp, _⟩ := hCov4 e he
    exact ⟨p, hp⟩
  have h4sub3 : E4 ⊆ E3 := fun e he => (hCov4 e he).1
  obtain ⟨D, hDAO, hDsz, hDpos, hDsafe⟩ := hBuildSandwich n m E3 E4 C P hAO hPne hSafe hCov4
  obtain ⟨U, V, hUVcov, hUVbd⟩ := hSandwichCover n m E3 E4 D hc4 h4sub3 hDAO hDpos hDsafe
  let E5L : Finset (Fin n × Fin m) := E5.filter fun e => e.1 ∈ U
  let E5R : Finset (Fin n × Fin m) := E5.filter fun e => e.1 ∉ U
  have hLle : E5L.card ≤ U.card := by
    have hinj : Set.InjOn Prod.fst (E5L : Set (Fin n × Fin m)) :=
      fun a ha b hb hab => hM1 a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    rw [← Finset.card_image_of_injOn hinj]
    refine Finset.card_le_card fun a ha => ?_
    rcases Finset.mem_image.mp ha with ⟨e, he, rfl⟩
    exact (Finset.mem_filter.mp he).2
  have hRle : E5R.card ≤ V.card := by
    have hinj : Set.InjOn Prod.snd (E5R : Set (Fin n × Fin m)) :=
      fun a ha b hb hab => hM2 a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    rw [← Finset.card_image_of_injOn hinj]
    refine Finset.card_le_card fun b hb => ?_
    rcases Finset.mem_image.mp hb with ⟨e, he, rfl⟩
    have he' := Finset.mem_filter.mp he
    exact (hUVcov e (hSub5 he'.1)).resolve_left he'.2
  have h5split : E5.card = E5L.card + E5R.card := by
    have hdisj : Disjoint E5L E5R := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : E5L ∪ E5R = E5 := by
      ext e
      simp only [E5L, E5R, Finset.mem_union, Finset.mem_filter]
      by_cases h : e.1 ∈ U <;> simp [h]
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  omega
