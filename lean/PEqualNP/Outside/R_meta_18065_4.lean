import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18065_4
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hCleanTopForm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj]
        (mate : Fin (n + n) → Fin (n + n)) (M : PEqualNP.CircuitLowerBounds.Circuit),
        (0 : ℕ) < n →
        PEqualNP.TopForm.NoFourCycle G →
        (∀ a b : Fin n, ¬G.Adj (Fin.castAdd n a) (Fin.castAdd n b)) →
        (∀ a b : Fin n, ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
        Function.Involutive mate →
        (∀ u : Fin (n + n), G.Adj u (mate u)) →
        PEqualNP.TopForm.IsLeastAO G M →
        PEqualNP.TopForm.TopForm G M →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          D.size ≤ M.size ∧
          PEqualNP.TopForm.IsAO2 (n + n) D ∧
          PEqualNP.MetaComplexity.circuitFun (n + n) D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
          ∀ j < D.gates.length,
            (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
            ∀ x : Fin (n + n) → Bool,
              PEqualNP.EdgeOwnership.gateVal (n + n) D j x = Bool.true →
              ∃ u v : Fin (n + n), G.Adj u v ∧ x u = Bool.true ∧ x v = Bool.true) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → (∀ (x6 x7 x8 x9 : Fin x1), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x2 ∧ (x6, x9) ∈ x2 ∧ (x7, x8) ∈ x2 ∧ (x7, x9) ∈ x2)) → (∀ (x7 : Fin x1), (x7, x3 x7) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x9 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), (x10, x11) ∈ x2 ∧ x9 (Fin.castAdd x1 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size ≤ x4.size ∧ PEqualNP.TopForm.IsAO2 (x1 + x1) x10 ∧ (∀ (x11 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x10 x11 = PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x11) ∧ ∀ x11 < x10.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x10 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x14 : Fin (x1 + x1) → Bool), PEqualNP.EdgeOwnership.gateVal (x1 + x1) x10 x11 x14 = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x1), (x16, x17) ∈ x2 ∧ x14 (Fin.castAdd x1 x16) = Bool.true ∧ x14 (Fin.natAdd x1 x17) = Bool.true := by
  classical
  intro n E p C hnPos hc4 hmatch hAO hfun
  let left : Fin n → Fin (n + n) := Fin.castAdd n
  let right : Fin n → Fin (n + n) := Fin.natAdd n
  have hsepLR : ∀ a b : Fin n, left a ≠ right b := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [left, right, Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hleftInj : Function.Injective left := by
    intro a b h
    exact Fin.ext (by simpa [left] using congrArg Fin.val h)
  have hrightInj : Function.Injective right := by
    intro a b h
    have hv := congrArg Fin.val h
    simp only [right, Fin.val_natAdd] at hv
    exact Fin.ext (by omega)
  have hsplit : ∀ u : Fin (n + n), (∃ a : Fin n, u = left a) ∨ (∃ b : Fin n, u = right b) :=
    fun u => Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) u
  let adj : Fin (n + n) → Fin (n + n) → Prop := fun u v =>
    ∃ a b : Fin n, (a, b) ∈ E ∧ ((u = left a ∧ v = right b) ∨ (v = left a ∧ u = right b))
  let G : SimpleGraph (Fin (n + n)) :=
    { Adj := adj
      symm := ⟨by
        rintro u v ⟨a, b, he, hor⟩
        exact ⟨a, b, he, hor.symm⟩⟩
      loopless := ⟨by
        rintro u ⟨a, b, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hsepLR a b (h1.symm.trans h2)
        · exact hsepLR a b (h1.symm.trans h2)⟩ }
  have hlr : ∀ a b : Fin n, G.Adj (left a) (right b) ↔ (a, b) ∈ E := by
    intro a b
    constructor
    · rintro ⟨u, v, he, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
      · have ha : a = u := hleftInj h1
        have hb : b = v := hrightInj h2
        subst ha; subst hb
        exact he
      · exact False.elim (hsepLR u b h1.symm)
    · intro he
      exact ⟨a, b, he, Or.inl ⟨rfl, rfl⟩⟩
  have hll : ∀ a b : Fin n, ¬G.Adj (left a) (left b) := by
    rintro a b ⟨u, v, _, ⟨_, h2⟩ | ⟨_, h2⟩⟩
    · exact hsepLR b v h2
    · exact hsepLR a v h2
  have hrr : ∀ a b : Fin n, ¬G.Adj (right a) (right b) := by
    rintro a b ⟨u, v, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩
    · exact hsepLR u a h1.symm
    · exact hsepLR u b h1.symm
  have hno4 : PEqualNP.TopForm.NoFourCycle G := by
    intro u v huv
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases hsplit u with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases hsplit x with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact False.elim (hll a b hx'.1)
      · rcases hsplit y with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · exact False.elim (hll a c hy'.1)
        · rcases hsplit v with ⟨d, rfl⟩ | ⟨d, rfl⟩
          · by_contra hxy
            exact hc4 a d b c
              (fun h => huv (congrArg left h))
              (fun h => hxy (congrArg right h))
              ⟨(hlr a b).mp hx'.1, (hlr a c).mp hy'.1, (hlr d b).mp hx'.2, (hlr d c).mp hy'.2⟩
          · exact False.elim (hrr d b hx'.2)
    · rcases hsplit x with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · rcases hsplit y with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · rcases hsplit v with ⟨d, rfl⟩ | ⟨d, rfl⟩
          · exact False.elim (hll d b hx'.2)
          · by_contra hxy
            exact hc4 b c a d
              (fun h => hxy (congrArg left h))
              (fun h => huv (congrArg right h))
              ⟨(hlr b a).mp hx'.1.symm, (hlr b d).mp hx'.2.symm, (hlr c a).mp hy'.1.symm, (hlr c d).mp hy'.2.symm⟩
        · exact False.elim (hrr a c hy'.1)
      · exact False.elim (hrr a b hx'.1)
  have hGne : G.edgeFinset.Nonempty := by
    let a0 : Fin n := ⟨0, hnPos⟩
    refine ⟨s(left a0, right (p a0)), ?_⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact (hlr a0 (p a0)).mpr (hmatch a0)
  have hcfun : PEqualNP.MetaComplexity.circuitFun (n + n) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hfun z]
    change decide (∃ a b : Fin n, (a, b) ∈ E ∧ z (left a) = true ∧ z (right b) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (n + n))), z a = true) ||
       decide (∃ u v : Fin (n + n), G.Adj u v ∧ z u = true ∧ z v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, he, ha, hb⟩
      exact ⟨left a, right b, (hlr a b).mpr he, ha, hb⟩
    · rintro ⟨u, v, ⟨a, b, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨a, b, he, hu, hv⟩
      · exact ⟨a, b, he, hv, hu⟩
  let mate : Fin (n + n) → Fin (n + n) :=
    Fin.addCases (fun a => right (p a)) (fun b => left (p.symm b))
  have hmateL : ∀ a : Fin n, mate (left a) = right (p a) := Fin.addCases_left
  have hmateR : ∀ b : Fin n, mate (right b) = left (p.symm b) := Fin.addCases_right
  have hInv : Function.Involutive mate := by
    intro u
    rcases hsplit u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [hmateL, hmateR, p.symm_apply_apply]
    · rw [hmateR, hmateL, p.apply_symm_apply]
  have hAdjMate : ∀ u : Fin (n + n), G.Adj u (mate u) := by
    intro u
    rcases hsplit u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · rw [hmateL]
      exact (hlr a (p a)).mpr (hmatch a)
    · rw [hmateR]
      have h := hmatch (p.symm b)
      rw [p.apply_symm_apply] at h
      exact ((hlr (p.symm b) b).mpr h).symm
  obtain ⟨M, hLeast, hTF, hMle⟩ := hNorm (n + n) G C hGne hAO hcfun
  obtain ⟨D, hDle, hDAO, hDfun, hDclean⟩ := hCleanTopForm n G mate M hnPos hno4 hll hrr hInv hAdjMate hLeast hTF
  refine ⟨D, Nat.le_trans hDle hMle, hDAO, fun z => ?_, fun j hj hand x hgx => ?_⟩
  · exact congrFun (hDfun.trans hcfun.symm) z
  · rcases hDclean j hj hand x hgx with ⟨u, v, ⟨a, b, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
    · exact ⟨a, b, he, hu, hv⟩
    · exact ⟨a, b, he, hv, hu⟩
