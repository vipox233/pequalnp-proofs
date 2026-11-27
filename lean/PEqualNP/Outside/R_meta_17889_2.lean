import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17889_2
    (hNorm :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsAO2 n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
          PEqualNP.TopForm.IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size)
    (hDeleteTopForm :
      ∀ (n m : ℕ) (G : SimpleGraph (Fin (n + m))) [DecidableRel G.Adj] (a : Fin n) (b : Fin m)
        (D : PEqualNP.CircuitLowerBounds.Circuit),
        (∀ u v : Fin n, ¬G.Adj (Fin.castAdd m u) (Fin.castAdd m v)) →
        (∀ u v : Fin m, ¬G.Adj (Fin.natAdd n u) (Fin.natAdd n v)) →
        G.Adj (Fin.castAdd m a) (Fin.natAdd n b) →
        PEqualNP.TopForm.IsLeastAO G D →
        PEqualNP.TopForm.TopForm G D →
        ∃ E : PEqualNP.CircuitLowerBounds.Circuit,
          E.size < D.size ∧
          PEqualNP.TopForm.IsAO2 (n + m) E ∧
          PEqualNP.MetaComplexity.circuitFun (n + m) E =
            PEqualNP.MetaComplexity.NestedCover.graphFun (G.deleteEdges {s(Fin.castAdd m a, Fin.natAdd n b)}) ∅) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Fin x1 × Fin x2) (x5 : PEqualNP.CircuitLowerBounds.Circuit),
      x4 ∈ x3 →
      (fun (x7 : Finset (Fin x1 × Fin x2)) (x8 : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.TopForm.IsAO2 (x1 + x2) x8 ∧
        ∀ (x9 : Fin (x1 + x2) → Bool),
          PEqualNP.MetaComplexity.circuitFun (x1 + x2) x8 x9 =
            Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x7 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) x3 x5 →
      ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),
        x8.size < x5.size ∧
        (fun (x9 : Finset (Fin x1 × Fin x2)) (x10 : PEqualNP.CircuitLowerBounds.Circuit) =>
          PEqualNP.TopForm.IsAO2 (x1 + x2) x10 ∧
          ∀ (x11 : Fin (x1 + x2) → Bool),
            PEqualNP.MetaComplexity.circuitFun (x1 + x2) x10 x11 =
              Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x2), (x12, x13) ∈ x9 ∧ x11 (Fin.castAdd x2 x12) = Bool.true ∧ x11 (Fin.natAdd x1 x13) = Bool.true)) (x3.erase x4) x8 := by
  classical
  intro x1 x2 x3 x4 x5 hmem hcomp
  let left : Fin x1 → Fin (x1 + x2) := Fin.castAdd x2
  let right : Fin x2 → Fin (x1 + x2) := Fin.natAdd x1
  have hsepLR : ∀ (a : Fin x1) (b : Fin x2), left a ≠ right b := by
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
  let adj : Fin (x1 + x2) → Fin (x1 + x2) → Prop := fun u v =>
    ∃ e ∈ x3, (u = left e.1 ∧ v = right e.2) ∨ (v = left e.1 ∧ u = right e.2)
  let G : SimpleGraph (Fin (x1 + x2)) :=
    { Adj := adj
      symm := ⟨by
        rintro u v ⟨e, he, hor⟩
        exact ⟨e, he, hor.symm⟩⟩
      loopless := ⟨by
        rintro u ⟨e, _, hor⟩
        rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact hsepLR e.1 e.2 (h1.symm.trans h2)
        · exact hsepLR e.1 e.2 (h1.symm.trans h2)⟩ }
  have hlr : ∀ (a : Fin x1) (b : Fin x2), G.Adj (left a) (right b) ↔ (a, b) ∈ x3 := by
    intro a b
    constructor
    · rintro ⟨⟨u, v⟩, he, ⟨h1, h2⟩ | ⟨h1, _⟩⟩
      · have ha : a = u := hleftInj h1
        have hb : b = v := hrightInj h2
        subst ha; subst hb
        exact he
      · exact False.elim (hsepLR u b h1.symm)
    · intro he
      exact ⟨(a, b), he, Or.inl ⟨rfl, rfl⟩⟩
  have hll : ∀ a b : Fin x1, ¬G.Adj (left a) (left b) := by
    rintro a b ⟨⟨u, v⟩, _, ⟨_, h2⟩ | ⟨_, h2⟩⟩
    · exact hsepLR b v h2
    · exact hsepLR a v h2
  have hrr : ∀ a b : Fin x2, ¬G.Adj (right a) (right b) := by
    rintro a b ⟨⟨u, v⟩, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩
    · exact hsepLR u a h1.symm
    · exact hsepLR u b h1.symm
  have hadj4 : G.Adj (left x4.1) (right x4.2) := (hlr x4.1 x4.2).mpr hmem
  have hGne : G.edgeFinset.Nonempty := ⟨s(left x4.1, right x4.2), SimpleGraph.mem_edgeFinset.mpr hadj4⟩
  have hcfun : PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hcomp.2 z]
    change decide (∃ a : Fin x1, ∃ b : Fin x2, (a, b) ∈ x3 ∧ z (left a) = true ∧ z (right b) = true) =
      (decide (∃ a ∈ (∅ : Finset (Fin (x1 + x2))), z a = true) ||
       decide (∃ u v : Fin (x1 + x2), G.Adj u v ∧ z u = true ∧ z v = true))
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨a, b, he, ha, hb⟩
      exact ⟨left a, right b, (hlr a b).mpr he, ha, hb⟩
    · rintro ⟨u, v, ⟨⟨a, b⟩, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, hu, hv⟩
      · exact ⟨a, b, he, hu, hv⟩
      · exact ⟨a, b, he, hv, hu⟩
  obtain ⟨D, hLeast, hTF, hDle⟩ := hNorm (x1 + x2) G x5 hGne hcomp.1 hcfun
  obtain ⟨E, hElt, hEAO, hEfun⟩ := hDeleteTopForm x1 x2 G x4.1 x4.2 D hll hrr hadj4 hLeast hTF
  refine ⟨E, Nat.lt_of_lt_of_le hElt hDle, hEAO, ?_⟩
  intro z
  have hz := congrFun hEfun z
  rw [hz]
  change (decide (∃ a ∈ (∅ : Finset (Fin (x1 + x2))), z a = true) ||
    decide (∃ u v : Fin (x1 + x2), (G.deleteEdges {s(left x4.1, right x4.2)}).Adj u v ∧ z u = true ∧ z v = true)) =
    Decidable.decide (∃ (a : Fin x1) (b : Fin x2), (a, b) ∈ x3.erase x4 ∧ z (left a) = Bool.true ∧ z (right b) = Bool.true)
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rw [SimpleGraph.deleteEdges_adj] at huv
    rcases huv.1 with ⟨⟨a, b⟩, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · have hneq : (a, b) ≠ x4 := by
        intro heq
        apply huv.2
        rcases Prod.ext_iff.mp heq with ⟨ha, hb⟩
        dsimp only at ha hb
        rw [ha, hb]
        exact Set.mem_singleton _
      exact ⟨a, b, Finset.mem_erase.mpr ⟨hneq, he⟩, hu, hv⟩
    · have hneq : (a, b) ≠ x4 := by
        intro heq
        apply huv.2
        rcases Prod.ext_iff.mp heq with ⟨ha, hb⟩
        dsimp only at ha hb
        rw [ha, hb, Sym2.eq_swap]
        exact Set.mem_singleton _
      exact ⟨a, b, Finset.mem_erase.mpr ⟨hneq, he⟩, hv, hu⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases Finset.mem_erase.mp hab with ⟨hneq, he⟩
    refine ⟨left a, right b, ?_, ha, hb⟩
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨(hlr a b).mpr he, ?_⟩
    intro hsym
    rw [Set.mem_singleton_iff] at hsym
    rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨hbad, _⟩
    · exact hneq (Prod.ext (hleftInj h1) (hrightInj h2))
    · exact hsepLR a x4.2 hbad
