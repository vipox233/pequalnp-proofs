import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18874_7
    (hTop : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun (a b : Fin 25) => ∃ (p : Fin 12) (l : Fin 13),
        (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
        a = Fin.castAdd 13 p ∧ b = Fin.natAdd 12 l) →
      PEqualNP.TopForm.IsLeastAO G C →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G D ∧
        PEqualNP.TopForm.TopForm G D ∧ D.size = C.size)
    (hClean : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun (a b : Fin 25) => ∃ (p : Fin 12) (l : Fin 13),
        (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
        a = Fin.castAdd 13 p ∧ b = Fin.natAdd 12 l) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = ∅ → 58 ≤ C.size)
    (hJunk : ∀ (G : SimpleGraph (Fin 25)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = SimpleGraph.fromRel (fun (a b : Fin 25) => ∃ (p : Fin 12) (l : Fin 13),
        (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
        a = Fin.castAdd 13 p ∧ b = Fin.natAdd 12 l) →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C ≠ ∅ → 58 ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (25 : ℕ) x1 → (∀ (x3 : Fin (25 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (12 : ℕ)) (x5 : Fin (13 : ℕ)), (x4.succ = x5 ∨ x4.succ = x5 + (1 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (3 : Fin ((12 : ℕ) + (1 : ℕ))) ∨ x4.succ = x5 + (9 : Fin ((12 : ℕ) + (1 : ℕ)))) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (12 : ℕ) x5) = Bool.true) → (58 : ℕ) ≤ x1.size) := by
  classical
  intro C hAO hSpec
  let G : SimpleGraph (Fin 25) := SimpleGraph.fromRel (fun (a b : Fin 25) => ∃ (p : Fin 12) (l : Fin 13),
    (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
    a = Fin.castAdd 13 p ∧ b = Fin.natAdd 12 l)
  have hG : G = SimpleGraph.fromRel (fun (a b : Fin 25) => ∃ (p : Fin 12) (l : Fin 13),
      (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
      a = Fin.castAdd 13 p ∧ b = Fin.natAdd 12 l) := rfl
  have hne : ∀ (p : Fin 12) (l : Fin 13), Fin.castAdd 13 p ≠ Fin.natAdd 12 l := by
    intro p l h
    have := congrArg Fin.val h
    simp at this
    omega
  have bridge : ∀ x : Fin 25 → Bool,
      (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ↔
      ∃ (p : Fin 12) (l : Fin 13), (p.succ = l ∨ p.succ = l + 1 ∨ p.succ = l + 3 ∨ p.succ = l + 9) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 12 l) = true := by
    intro x
    constructor
    · rintro ⟨u, v, hadj, hu, hv⟩
      rw [SimpleGraph.fromRel_adj] at hadj
      rcases hadj with ⟨_, ⟨p, l, hr, rfl, rfl⟩ | ⟨p, l, hr, rfl, rfl⟩⟩
      · exact ⟨p, l, hr, hu, hv⟩
      · exact ⟨p, l, hr, hv, hu⟩
    · rintro ⟨p, l, hr, hp, hl⟩
      refine ⟨Fin.castAdd 13 p, Fin.natAdd 12 l, ?_, hp, hl⟩
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hne p l, Or.inl ⟨p, l, hr, rfl, rfl⟩⟩
  have hfun : ∀ D : PEqualNP.CircuitLowerBounds.Circuit,
      (∀ (x3 : Fin 25 → Bool), D.eval (List.ofFn x3) = true ↔ ∃ (x4 : Fin 12) (x5 : Fin 13),
        (x4.succ = x5 ∨ x4.succ = x5 + 1 ∨ x4.succ = x5 + 3 ∨ x4.succ = x5 + 9) ∧
        x3 (Fin.castAdd 13 x4) = true ∧ x3 (Fin.natAdd 12 x5) = true) →
      PEqualNP.MetaComplexity.circuitFun 25 D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    intro D hD
    funext x
    have h1 := hD x
    have h2 := bridge x
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.MetaComplexity.NestedCover.graphFun
    have e : decide (∃ a ∈ (∅ : Finset (Fin 25)), x a = true) = false := by simp
    rw [e, Bool.false_or]
    by_cases h : D.eval (List.ofFn x) = true
    · rw [h]
      exact (decide_eq_true (h2.mpr (h1.mp h))).symm
    · rw [Bool.not_eq_true] at h
      rw [h]
      refine (decide_eq_false ?_).symm
      intro hx
      have := h1.mpr (h2.mp hx)
      rw [h] at this
      exact Bool.false_ne_true this
  let P : ℕ → Prop := fun s => ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.TopForm.IsAO2 25 D ∧
    PEqualNP.MetaComplexity.circuitFun 25 D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    D.size = s
  have hP : ∃ s, P s := ⟨C.size, C, hAO, hfun C hSpec, rfl⟩
  obtain ⟨D0, hAO0, hf0, hs0⟩ := Nat.find_spec hP
  have hleast : PEqualNP.TopForm.IsLeastAO G D0 := by
    refine ⟨hAO0, hf0, ?_⟩
    intro C' hC' hf'
    rw [hs0]
    exact Nat.find_min' hP ⟨C', hC', hf', rfl⟩
  have hle : Nat.find hP ≤ C.size := Nat.find_min' hP ⟨C, hAO, hfun C hSpec, rfl⟩
  obtain ⟨D1, hL1, hT1, hs1⟩ := hTop G D0 hG hleast
  have h58 : 58 ≤ D1.size := by
    by_cases hj : PEqualNP.TopForm.junk G D1 = ∅
    · exact hClean G D1 hG hL1 hT1 hj
    · exact hJunk G D1 hG hL1 hT1 hj
  omega
