import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9134_2
    (hLineInter :
      ∀ (n : ℕ) (S : Fin n → Finset (Fin n)),
        (∀ (p q : Fin n), p ≠ q → ∃! l : Fin n, p ∈ S l ∧ q ∈ S l) →
        ∀ (l1 l2 : Fin n), l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ))
    (hSetBound :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)),
        (299 : ℕ) ≤ q →
        n = q ^ (2 : ℕ) + q + (1 : ℕ) →
        (∀ (l : Fin n), (S l).card = q + (1 : ℕ)) →
        (∀ (p1 p2 : Fin n), p1 ≠ p2 → ∃! l : Fin n, p1 ∈ S l ∧ p2 ∈ S l) →
        (∀ (l1 l2 : Fin n), l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ)) →
        ∀ (m out : ℕ) (X : Finset ℕ) (F : ℕ → Set (Finset (Fin n) × Finset (Fin n))),
          out < n + n + m →
          (∀ (i : Fin n),
            F ↑i = {ab : Finset (Fin n) × Finset (Fin n) | i ∈ ab.1} ∧
            F (n + ↑i) = {ab : Finset (Fin n) × Finset (Fin n) | i ∈ ab.2}) →
          (∀ j < m,
            ∃ a < n + n + j,
            ∃ b < n + n + j,
              F (n + n + j) ∈ [F a ∪ F b, F a, ∅] ∨
              F (n + n + j) = F a ∩ F b ∧
                (j ∈ X ∨ ∃ (A : Set (Finset (Fin n))) (B : Set (Finset (Fin n))),
                  F a = A ×ˢ Set.univ ∧ F b = Set.univ ×ˢ B)) →
          (∀ (p l : Fin n), p ∈ S l → ({p}, {l}) ∈ F out) →
          (∀ (Y : Finset (Fin n)), Y.card ≤ q → (PEqualNP.GenericRejection.zeroSet S Y, Y) ∉ F out) →
          (100 : ℕ) * X.card < n * q →
          n * (q + (1 : ℕ)) ≤ (100 : ℕ) * m) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   let x5 : Type := Fin x2 → Bool;   have x6 : Fin x2 → Fin x2 → Bool := fun (x6 x7 : Fin x2) => Decidable.decide (x7 = x6);   (299 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x9 : Fin x2), Fintype.card { x10 : Fin x2 // x3 x10 x9 } = x1 + (1 : ℕ)) →         (∀ (x10 x11 : Fin x2), x10 ≠ x11 → ∃! x13 : Fin x2, x3 x10 x13 ∧ x3 x11 x13) →           ∀ (x11 x12 : ℕ) (x13 : Finset ℕ) (x14 : ℕ → Set (x5 × x5)),             x12 < x2 + x2 + x11 →               (∀ (x16 : Fin x2), x14 ↑x16 = {x17 : x5 × x5 | x17.1 x16 = Bool.true} ∧ x14 (x2 + ↑x16) = {x17 : x5 × x5 | x17.2 x16 = Bool.true}) →                 (∀ x17 < x11,                     ∃ x19 < x2 + x2 + x17,                       ∃ x20 < x2 + x2 + x17,                         have x21 : Set (x5 × x5) := x14 (x2 + x2 + x17);                         x21 ∈ [x14 x19 ∪ x14 x20, x14 x19, ∅] ∨ x21 = x14 x19 ∩ x14 x20 ∧ (x17 ∈ x13 ∨ ∃ (x22 : Set x5) (x23 : Set x5), x14 x19 = x22 ×ˢ Set.univ ∧ x14 x20 = Set.univ ×ˢ x23)) →                   (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x6 x18, x6 x19) ∈ x14 x12) → (∀ (x19 : x5), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x14 x12) → (100 : ℕ) * x13.card < x2 * x1 → x2 * (x1 + (1 : ℕ)) ≤ (100 : ℕ) * x11 := by
  intro x1 x2 x3 x4 x5 x6 hq hn hdeg huniq x11 x12 x13 x14 hout hin hstep htrue hfalse hX
  let S : Fin x2 → Finset (Fin x2) := fun l => Finset.univ.filter (fun p => x3 p l)
  have hSdeg : ∀ l : Fin x2, (S l).card = x1 + (1 : ℕ) := by
    intro l
    rw [← hdeg l, Fintype.card_subtype]
  have hSuniq : ∀ p1 p2 : Fin x2, p1 ≠ p2 → ∃! l : Fin x2, p1 ∈ S l ∧ p2 ∈ S l := by
    intro p1 p2 hp
    simpa [S] using huniq p1 p2 hp
  have hSinter : ∀ l1 l2 : Fin x2, l1 ≠ l2 → (S l1 ∩ S l2).card ≤ (1 : ℕ) :=
    hLineInter x2 S hSuniq
  let phi1 : Finset (Fin x2) → x5 := fun A i => Decidable.decide (i ∈ A)
  let phi : Finset (Fin x2) × Finset (Fin x2) → x5 × x5 := fun ab => (phi1 ab.1, phi1 ab.2)
  let F : ℕ → Set (Finset (Fin x2) × Finset (Fin x2)) := fun k => phi ⁻¹' (x14 k)
  have hFin : ∀ i : Fin x2,
      F ↑i = {ab : Finset (Fin x2) × Finset (Fin x2) | i ∈ ab.1} ∧
      F (x2 + ↑i) = {ab : Finset (Fin x2) × Finset (Fin x2) | i ∈ ab.2} := by
    intro i
    obtain ⟨h1, h2⟩ := hin i
    constructor
    · ext ⟨A, B⟩
      simp [F, phi, phi1, h1]
    · ext ⟨A, B⟩
      simp [F, phi, phi1, h2]
  have hFstep : ∀ j < x11,
      ∃ a < x2 + x2 + j,
      ∃ b < x2 + x2 + j,
        F (x2 + x2 + j) ∈ [F a ∪ F b, F a, ∅] ∨
        F (x2 + x2 + j) = F a ∩ F b ∧
          (j ∈ x13 ∨ ∃ (A : Set (Finset (Fin x2))) (B : Set (Finset (Fin x2))),
            F a = A ×ˢ Set.univ ∧ F b = Set.univ ×ˢ B) := by
    intro j hj
    rcases hstep j hj with ⟨a, ha, b, hb, hcase⟩
    dsimp only at hcase
    refine ⟨a, ha, b, hb, ?_⟩
    rcases hcase with hmem | ⟨heq, hbranch⟩
    · left
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
      rcases hmem with h1 | h2 | h3
      · left
        simp only [F, h1, Set.preimage_union]
      · right
        left
        simp only [F, h2]
      · right
        right
        simp only [F, h3, Set.preimage_empty]
    · right
      refine ⟨by simp only [F, heq, Set.preimage_inter], ?_⟩
      rcases hbranch with hjX | ⟨A0, B0, hA0, hB0⟩
      · exact Or.inl hjX
      · refine Or.inr ⟨phi1 ⁻¹' A0, phi1 ⁻¹' B0, ?_, ?_⟩
        · ext ⟨A, B⟩
          simp [F, phi, hA0]
        · ext ⟨A, B⟩
          simp [F, phi, hB0]
  have hFtrue : ∀ (p l : Fin x2), p ∈ S l → ({p}, {l}) ∈ F x12 := by
    intro p l hpl
    have h3 : x3 p l := by
      simpa [S] using hpl
    have hp : phi1 {p} = x6 p := by
      funext q
      simp [phi1, x6]
    have hl : phi1 {l} = x6 l := by
      funext q
      simp [phi1, x6]
    change (phi1 {p}, phi1 {l}) ∈ x14 x12
    rw [hp, hl]
    exact htrue p l h3
  have hFfalse : ∀ (Y : Finset (Fin x2)),
      Y.card ≤ x1 → (PEqualNP.GenericRejection.zeroSet S Y, Y) ∉ F x12 := by
    intro Y hY
    let y : x5 := phi1 Y
    have hycard : Fintype.card { x20 : Fin x2 // y x20 = Bool.true } ≤ x1 := by
      rw [Fintype.card_subtype]
      have hfilt : Finset.univ.filter (fun l : Fin x2 => y l = Bool.true) = Y := by
        ext l
        simp [y, phi1]
      rw [hfilt]
      exact hY
    have hzero :
        phi1 (PEqualNP.GenericRejection.zeroSet S Y) =
          fun (x21 : Fin x2) =>
            Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ y x22 = Bool.true := by
      funext p
      dsimp only [phi1, PEqualNP.GenericRejection.zeroSet, S, y]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_decide, not_exists, not_and]
      constructor
      · intro h l hpl hl
        exact h l (by simpa [decide_eq_true_iff] using hl) hpl
      · intro h l hl hpl
        exact h l hpl (by simpa [decide_eq_true_iff] using hl)
    change (phi1 (PEqualNP.GenericRejection.zeroSet S Y), y) ∉ x14 x12
    rw [hzero]
    exact hfalse y hycard
  exact hSetBound x1 x2 S hq hn hSdeg hSuniq hSinter x11 x12 x13 F hout hFin hFstep hFtrue hFfalse hX
