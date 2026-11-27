import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5064_2
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hDeg1LeafLB :
      ∀ (n : ℕ) (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj]
        (mate : Fin (n + n) → Fin (n + n)) (D : PEqualNP.CircuitLowerBounds.Circuit),
        n < G.edgeFinset.card →
        PEqualNP.TopForm.NoFourCycle G →
        (∀ a b : Fin n, ¬G.Adj (Fin.castAdd n a) (Fin.castAdd n b)) →
        (∀ a b : Fin n, ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
        Function.Involutive mate →
        (∀ u : Fin (n + n), G.Adj u (mate u)) →
        (∃ z : Fin (n + n), ∀ w : Fin (n + n), G.Adj z w ↔ w = mate z) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        G.edgeFinset.card + n ≤ D.size + (1 : ℕ)) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → ((∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x11, x12) ∈ x2 → x12 = x3 x11) ∨ ∃ (x11 : Fin x1), ∀ (x12 : Fin x1), (x12, x11) ∈ x2 → x3 x12 = x11) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  classical
  intro n E p C hdense _hsize hc4 hmatch hAO hfun hleaf
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
  let enc : Fin n × Fin n → Sym2 (Fin (n + n)) := fun e => s(left e.1, right e.2)
  have hencInj : Function.Injective enc := by
    intro e1 e2 h
    change s(left e1.1, right e1.2) = s(left e2.1, right e2.2) at h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨hbad, _⟩
    · exact Prod.ext (hleftInj h1) (hrightInj h2)
    · exact False.elim (hsepLR e1.1 e2.2 hbad)
  have hedges : G.edgeFinset = E.image enc := by
    ext s
    induction s using Sym2.ind with
    | _ u v =>
      constructor
      · intro hs
        have hadj : G.Adj u v := by
          simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hs
        rcases hadj with ⟨a, b, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨(a, b), he, rfl⟩
        · exact Finset.mem_image.mpr ⟨(a, b), he, Sym2.eq_swap⟩
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨⟨a, b⟩, he, hsym⟩
        rw [← hsym]
        simpa only [enc, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (hlr a b).mpr he
  have hedgeCard : G.edgeFinset.card = E.card := by
    rw [hedges, Finset.card_image_of_injective _ hencInj]
  have hGdense : n < G.edgeFinset.card := by
    rw [hedgeCard]
    exact hdense
  have hGne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
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
  have hLeafG : ∃ z : Fin (n + n), ∀ w : Fin (n + n), G.Adj z w ↔ w = mate z := by
    rcases hleaf with ⟨a, ha⟩ | ⟨b, hb⟩
    · refine ⟨left a, fun w => ?_⟩
      constructor
      · intro hadj
        rcases hsplit w with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · exact False.elim (hll a c hadj)
        · rw [hmateL, ha c ((hlr a c).mp hadj)]
      · rintro rfl
        exact hAdjMate (left a)
    · refine ⟨right b, fun w => ?_⟩
      constructor
      · intro hadj
        rcases hsplit w with ⟨c, rfl⟩ | ⟨c, rfl⟩
        · have hpc : p c = b := hb c ((hlr c b).mp hadj.symm)
          rw [hmateR, ← hpc, p.symm_apply_apply]
        · exact False.elim (hrr b c hadj)
      · rintro rfl
        exact hAdjMate (right b)
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (n + n) G C hGne hAO hcfun
  have hLB := hDeg1LeafLB n G mate D hGdense hno4 hll hrr hInv hAdjMate hLeafG hLeast hTF
  omega
