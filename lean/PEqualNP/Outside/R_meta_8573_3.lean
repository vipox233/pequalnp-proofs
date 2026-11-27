import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8573_3
    (hAccount :
      ∀ (m : ℕ) (G : SimpleGraph (Fin m)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        G.edgeFinset.Nonempty →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        G.edgeFinset.card +
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
          C.size + (PEqualNP.TopForm.Ustar G C).card + (1 : ℕ))
    (hCharge :
      ∀ (n : ℕ) (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj]
        (mate : Fin (n + n) → Fin (n + n)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.NoFourCycle G →
        (∀ a b : Fin n, ¬G.Adj (Fin.castAdd n a) (Fin.castAdd n b)) →
        (∀ a b : Fin n, ¬G.Adj (Fin.natAdd n a) (Fin.natAdd n b)) →
        Function.Involutive mate →
        (∀ u : Fin (n + n), G.Adj u (mate u)) →
        (∀ u : Fin (n + n), ∃ v : Fin (n + n), G.Adj u v ∧ v ≠ mate u) →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (2 : ℕ) ≤ (PEqualNP.TopForm.junk G C).card →
        (PEqualNP.TopForm.Ustar G C).card + n ≤
          (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
          (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card +
          (PEqualNP.TopForm.junk G C).card +
          (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : SimpleGraph (Fin (x1 + x1))) [x5 : DecidableRel x4.Adj] (x6 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (∀ (x8 x9 x10 x11 : Fin x1), x8 ≠ x9 → x10 ≠ x11 → ¬((x8, x10) ∈ x2 ∧ (x8, x11) ∈ x2 ∧ (x9, x10) ∈ x2 ∧ (x9, x11) ∈ x2)) → (∀ (x9 : Fin x1), (x9, x3 x9) ∈ x2) → ((∀ (x10 : Fin x1), ∃ (x11 : Fin x1), x11 ≠ x3 x10 ∧ (x10, x11) ∈ x2) ∧ ∀ (x10 : Fin x1), ∃ (x11 : Fin x1), x3 x11 ≠ x10 ∧ (x11, x10) ∈ x2) → (∀ (x11 x12 : Fin (x1 + x1)), x4.Adj x11 x12 ↔ ∃ (x13 : Fin x1) (x14 : Fin x1), (x13, x14) ∈ x2 ∧ (x11 = Fin.castAdd x1 x13 ∧ x12 = Fin.natAdd x1 x14 ∨ x12 = Fin.castAdd x1 x13 ∧ x11 = Fin.natAdd x1 x14)) → PEqualNP.TopForm.IsLeastAO x4 x6 → PEqualNP.TopForm.TopForm x4 x6 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x4 x6).card → x2.card + x1 ≤ x6.size + (1 : ℕ) := by
  classical
  intro n E p G _x5 C hdense hc4 hmatch hextra hG hLeast hTF hJunk
  rcases hextra with ⟨hexRow, hexCol⟩
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
  have hlr : ∀ a b : Fin n, G.Adj (left a) (right b) ↔ (a, b) ∈ E := by
    intro a b
    rw [hG]
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
    intro a b h
    rw [hG] at h
    rcases h with ⟨u, v, _, ⟨_, h2⟩ | ⟨_, h2⟩⟩
    · exact hsepLR b v h2
    · exact hsepLR a v h2
  have hrr : ∀ a b : Fin n, ¬G.Adj (right a) (right b) := by
    intro a b h
    rw [hG] at h
    rcases h with ⟨u, v, _, ⟨h1, _⟩ | ⟨h1, _⟩⟩
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
        rw [hG] at hadj
        rcases hadj with ⟨a, b, he, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact Finset.mem_image.mpr ⟨(a, b), he, rfl⟩
        · exact Finset.mem_image.mpr ⟨(a, b), he, Sym2.eq_swap⟩
      · intro hs
        rcases Finset.mem_image.mp hs with ⟨⟨a, b⟩, he, hsym⟩
        rw [← hsym]
        simpa only [enc, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using (hlr a b).mpr he
  have hedgeCard : G.edgeFinset.card = E.card := by
    rw [hedges, Finset.card_image_of_injective _ hencInj]
  have hGne : G.edgeFinset.Nonempty := by
    rw [← Finset.card_pos, hedgeCard]
    omega
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
  have hDeg2 : ∀ u : Fin (n + n), ∃ v : Fin (n + n), G.Adj u v ∧ v ≠ mate u := by
    intro u
    rcases hsplit u with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · obtain ⟨c, hcne, hc⟩ := hexRow a
      refine ⟨right c, (hlr a c).mpr hc, ?_⟩
      rw [hmateL]
      exact fun heq => hcne (hrightInj heq)
    · obtain ⟨a, hane, ha⟩ := hexCol b
      refine ⟨left a, ((hlr a b).mpr ha).symm, ?_⟩
      rw [hmateR]
      intro heq
      apply hane
      have ha' : a = p.symm b := hleftInj heq
      rw [ha', p.apply_symm_apply]
  have hAcc := hAccount (n + n) G C hno4 hGne hLeast hTF
  have hChg := hCharge n G mate C hno4 hll hrr hInv hAdjMate hDeg2 hLeast hTF hJunk
  omega
