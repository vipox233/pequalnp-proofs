import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8887_4
    (hMinUse :
      ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) →
        PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
        (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ x4.size ∧
          PEqualNP.TopForm.IsAO2 (x1 + x1) D ∧
          (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) D x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧
          ∀ w < x1 + x1 + D.size, w ∈ D.output :: List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) D.gates)
    (hSurplus :
      ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
        (0 : ℕ) < x1 →
        (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) →
        (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) →
        PEqualNP.TopForm.IsAO2 (x1 + x1) x4 →
        (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) →
        have x10 : List ℕ := x4.output :: List.flatMap (fun (x10 : PEqualNP.CircuitLowerBounds.Gate) => x10.inputs) x4.gates;
        x2.card ≤ x1 + (x10.length - x10.toFinset.card)) :
    have x1 : (x1 : ℕ) → Finset (Fin x1 × Fin x1) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x4 x5 x6 x7 : Fin x1), x4 ≠ x5 → x6 ≠ x7 → ¬((x4, x6) ∈ x2 ∧ (x4, x7) ∈ x2 ∧ (x5, x6) ∈ x2 ∧ (x5, x7) ∈ x2)) ∧ (∃ (x4 : Equiv.Perm (Fin x1)), ∀ (x5 : Fin x1), (x5, x4 x5) ∈ x2) ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x3 ∧ ∀ (x4 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x3 x4 = Decidable.decide (∃ (x5 : Fin x1) (x6 : Fin x1), (x5, x6) ∈ x2 ∧ x4 (Fin.castAdd x1 x5) = Bool.true ∧ x4 (Fin.natAdd x1 x6) = Bool.true); ∀ (x2 : ℕ) (x3 : Finset (Fin x2 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 x2 x3 x4 → (∀ (x6 : Fin x2), (3 : ℕ) ≤ {x7 ∈ x3 | x7.1 = x6}.card ∧ (3 : ℕ) ≤ {x7 ∈ x3 | x7.2 = x6}.card) → x3.card + x2 ≤ x4.size + (1 : ℕ) := by
  intro _x1 n E C hPrem _hDeg
  by_cases hn0 : n = 0
  · subst hn0
    have hE0 : E = ∅ := Finset.eq_empty_of_forall_notMem fun e _ => Fin.elim0 e.1
    rw [hE0, Finset.card_empty]
    omega
  have hnPos : (0 : ℕ) < n := by omega
  rcases hPrem with ⟨hc4, ⟨p, hmatch⟩, hAO, hfun⟩
  obtain ⟨D, hDle, hDAO, hDfun, hDuse⟩ := hMinUse n E p C hmatch hAO hfun
  let L : List ℕ := D.output :: List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) D.gates
  have hFlatLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate),
      (∀ g ∈ gs, g.inputs.length = 2) →
      (List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) gs).length = 2 * gs.length := by
    intro gs
    induction gs with
    | nil =>
      intro _
      simp
    | cons g gs ih =>
      intro hlen
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hg2 : g.inputs.length = 2 := hlen g (List.mem_cons_self ..)
      have hgs2 : (List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) gs).length = 2 * gs.length :=
        ih fun g' hg' => hlen g' (List.mem_cons_of_mem g hg')
      omega
  have hLlen : L.length = 2 * D.size + 1 := by
    change (List.flatMap (fun g : PEqualNP.CircuitLowerBounds.Gate => g.inputs) D.gates).length + 1 = 2 * D.gates.length + 1
    rw [hFlatLen D.gates hDAO.2.2]
  have hSub : Finset.range (n + n + D.size) ⊆ L.toFinset := by
    intro w hw
    rw [List.mem_toFinset]
    exact hDuse w (Finset.mem_range.mp hw)
  have hCardGe : n + n + D.size ≤ L.toFinset.card := by
    have h1 := Finset.card_le_card hSub
    rw [Finset.card_range] at h1
    exact h1
  have hCardLe : L.toFinset.card ≤ L.length := List.toFinset_card_le L
  have hSurp : E.card ≤ n + (L.length - L.toFinset.card) :=
    hSurplus n E p D hnPos hc4 hmatch hDAO hDfun
  omega
