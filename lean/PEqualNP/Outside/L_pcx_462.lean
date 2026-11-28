import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_462_aux

open MvPolynomial PEqualNP.ProofComplexity

private lemma pcDerivable_sum {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial V (ZMod 2))
    (hf : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PCDerivable.add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

private lemma pcDerivable_mul_monomial_one {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    {g : MvPolynomial V (ZMod 2)} (hg : PCDerivable F B g)
    (s : V →₀ ℕ) (hdeg : s.sum (fun _ k => k) + g.totalDegree ≤ B) :
    PCDerivable F B (monomial s (1 : ZMod 2) * g) := by
  classical
  induction s using Finsupp.induction with
  | zero =>
    have h1 : monomial (0 : V →₀ ℕ) (1 : ZMod 2) = 1 := rfl
    rw [h1, one_mul]
    exact hg
  | @single_add v k s' hv hk ih =>
    have hsum_eq : (Finsupp.single v k + s').sum (fun _ m => m) = k + s'.sum (fun _ m => m) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    rw [hsum_eq] at hdeg
    have hih : PCDerivable F B (monomial s' (1 : ZMod 2) * g) := ih (by omega)
    have hmon_split : monomial (Finsupp.single v k + s') (1 : ZMod 2) * g =
        (X v) ^ k * (monomial s' (1 : ZMod 2) * g) := by
      rw [← mul_assoc]
      congr 1
      have h1 : monomial (Finsupp.single v k + s') (1 : ZMod 2) =
          monomial (Finsupp.single v k) (1 : ZMod 2) * monomial s' (1 : ZMod 2) := by
        rw [monomial_mul_monomial, one_mul]
      rw [h1]
      congr 1
      rw [X_pow_eq_monomial]
    rw [hmon_split]
    have hdeg_base : (monomial s' (1 : ZMod 2) * g).totalDegree ≤ s'.sum (fun _ m => m) + g.totalDegree := by
      calc (monomial s' (1 : ZMod 2) * g).totalDegree
          ≤ (monomial s' (1 : ZMod 2)).totalDegree + g.totalDegree := totalDegree_mul _ _
        _ ≤ s'.sum (fun _ m => m) + g.totalDegree := Nat.add_le_add_right (totalDegree_monomial_le s' (1 : ZMod 2)) _
    have hpow : ∀ m : ℕ, m ≤ k →
        PCDerivable F B ((X v) ^ m * (monomial s' (1 : ZMod 2) * g)) := by
      intro m
      induction m with
      | zero => intro _; simpa using hih
      | succ m ihm =>
        intro hm
        rw [pow_succ', mul_assoc]
        refine PCDerivable.mulX v (ihm (Nat.le_of_succ_le hm)) ?_
        have hXm : ((X v : MvPolynomial V (ZMod 2)) ^ m).totalDegree ≤ m := by
          rw [X_pow_eq_monomial]
          calc (monomial (Finsupp.single v m) (1 : ZMod 2)).totalDegree
              ≤ (Finsupp.single v m).sum (fun _ t => t) := totalDegree_monomial_le _ (1 : ZMod 2)
            _ = m := Finsupp.sum_single_index rfl
        have hX1 : (X v : MvPolynomial V (ZMod 2)).totalDegree ≤ 1 := by
          rw [totalDegree_X]
        calc (X v * ((X v) ^ m * (monomial s' (1 : ZMod 2) * g))).totalDegree
            ≤ (X v).totalDegree + ((X v) ^ m * (monomial s' (1 : ZMod 2) * g)).totalDegree := totalDegree_mul _ _
          _ ≤ 1 + (((X v) ^ m).totalDegree + (monomial s' (1 : ZMod 2) * g).totalDegree) :=
              Nat.add_le_add hX1 (totalDegree_mul _ _)
          _ ≤ 1 + (m + (s'.sum (fun _ t => t) + g.totalDegree)) :=
              Nat.add_le_add_left (Nat.add_le_add hXm hdeg_base) 1
          _ ≤ B := by omega
    exact hpow k (le_refl k)

private lemma pcDerivable_mul_left {V : Type} {F : Set (MvPolynomial V (ZMod 2))} {B : ℕ}
    {g : MvPolynomial V (ZMod 2)} (hg : PCDerivable F B g)
    (q : MvPolynomial V (ZMod 2)) (hdeg : q.totalDegree + g.totalDegree ≤ B) :
    PCDerivable F B (q * g) := by
  classical
  rw [as_sum q, Finset.sum_mul]
  refine pcDerivable_sum q.support _ (fun s hs => ?_)
  generalize hc_val : q.coeff s = c
  have hc : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with rfl | rfl
  · rw [monomial_zero, zero_mul]
    exact PCDerivable.zero
  · have hs_le : s.sum (fun _ k => k) ≤ q.totalDegree := le_totalDegree hs
    exact pcDerivable_mul_monomial_one hg s (by omega)

private lemma pcDerivable_lift_mul {V : Type} {F E : Set (MvPolynomial V (ZMod 2))} {B D : ℕ}
    (q : MvPolynomial V (ZMod 2)) (hqD : q.totalDegree + D ≤ B)
    (hE : ∀ f ∈ E, f.totalDegree ≤ D → PCDerivable F B (q * f))
    {g : MvPolynomial V (ZMod 2)} (hg : PCDerivable (F ∪ E) D g) :
    PCDerivable F B (q * g) := by
  induction hg with
  | @ax f hf hdeg =>
    rcases hf with hfF | hfE
    · exact pcDerivable_mul_left (PCDerivable.ax hfF (by omega)) q (by omega)
    · exact hE f hfE hdeg
  | zero =>
    rw [mul_zero]
    exact PCDerivable.zero
  | @add g1 g2 _ _ ih1 ih2 =>
    rw [mul_add]
    exact PCDerivable.add ih1 ih2
  | @mulX j g _ hdeg ih =>
    have hcomm : q * (X j * g) = X j * (q * g) := by ring
    rw [hcomm]
    refine PCDerivable.mulX j ih ?_
    rw [← hcomm]
    exact (totalDegree_mul q (X j * g)).trans (by omega)

private lemma totalDegree_finset_prod_le {V : Type} {ι : Type*}
    (s : Finset ι) (f : ι → MvPolynomial V (ZMod 2)) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

private lemma exists_inj_good {t B pdeg : ℕ} (D w : Fin t → ℕ)
    (hfits : ∀ T : Finset (Fin t), T.Nonempty → ∃ i ∈ T, pdeg + D i + ∑ j ∈ T.erase i, w j ≤ B) :
    ∀ k : ℕ, ∀ T : Finset (Fin t), T.card = k →
      ∃ f : Fin k → Fin t, Function.Injective f ∧ Finset.univ.image f = T ∧
        ∀ j : Fin k, pdeg + D (f j) + ∑ l ∈ Finset.univ.filter (fun l : Fin k => l < j), w (f l) ≤ B := by
  intro k
  induction k with
  | zero =>
    intro T hT
    have hTe : T = ∅ := Finset.card_eq_zero.mp hT
    subst hTe
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, by simp, fun j => Fin.elim0 j⟩
  | succ k ih =>
    intro T hT
    have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i0, hi0T, hi0_le⟩ := hfits T hTne
    have herase_card : (T.erase i0).card = k := by
      rw [Finset.card_erase_of_mem hi0T, hT]
      omega
    obtain ⟨f', hf'_inj, hf'_img, hf'_good⟩ := ih (T.erase i0) herase_card
    let f : Fin (k + 1) → Fin t := fun j =>
      if hj : j.val < k then f' ⟨j.val, hj⟩ else i0
    have hf'_ne : ∀ l : Fin k, f' l ≠ i0 := by
      intro l heq
      have hmem : f' l ∈ T.erase i0 := hf'_img ▸ Finset.mem_image_of_mem f' (Finset.mem_univ l)
      rw [heq] at hmem
      exact (Finset.mem_erase.mp hmem).1 rfl
    have hf_inj : Function.Injective f := by
      intro j1 j2 heq
      dsimp only [f] at heq
      by_cases h1 : j1.val < k <;> by_cases h2 : j2.val < k
      · simp only [h1, h2, ↓reduceDIte] at heq
        have h := hf'_inj heq
        exact Fin.ext (by simpa using congrArg Fin.val h)
      · simp only [h1, h2, ↓reduceDIte] at heq
        exact absurd heq (hf'_ne _)
      · simp only [h1, h2, ↓reduceDIte] at heq
        exact absurd heq.symm (hf'_ne _)
      · exact Fin.ext (by have := j1.isLt; have := j2.isLt; omega)
    have hf_img : Finset.univ.image f = T := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨j, rfl⟩
        dsimp only [f]
        by_cases hj : j.val < k
        · simp only [hj, ↓reduceDIte]
          have hmem : f' ⟨j.val, hj⟩ ∈ T.erase i0 :=
            hf'_img ▸ Finset.mem_image_of_mem f' (Finset.mem_univ _)
          exact Finset.erase_subset i0 T hmem
        · simp only [hj, ↓reduceDIte]; exact hi0T
      · intro hxT
        by_cases hxi : x = i0
        · subst hxi
          refine ⟨⟨k, Nat.lt_succ_self k⟩, ?_⟩
          simp [f]
        · have hx_er : x ∈ T.erase i0 := Finset.mem_erase.mpr ⟨hxi, hxT⟩
          rw [← hf'_img] at hx_er
          rcases Finset.mem_image.mp hx_er with ⟨l, _, rfl⟩
          refine ⟨⟨l.val, Nat.lt_succ_of_lt l.isLt⟩, ?_⟩
          simp [f, l.isLt]
    refine ⟨f, hf_inj, hf_img, fun j => ?_⟩
    by_cases hj : j.val < k
    · have hfj : f j = f' ⟨j.val, hj⟩ := by simp [f, hj]
      rw [hfj]
      have hsum_eq : (∑ l ∈ Finset.univ.filter (fun l : Fin (k + 1) => l < j), w (f l)) =
          ∑ l ∈ Finset.univ.filter (fun l : Fin k => l < ⟨j.val, hj⟩), w (f' l) := by
        refine Finset.sum_bij (fun l hl => ⟨l.val, lt_trans (Finset.mem_filter.mp hl).2 hj⟩) ?_ ?_ ?_ ?_
        · intro l hl
          have hlt : l < j := (Finset.mem_filter.mp hl).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        · intro l1 _ l2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
        · intro l hl
          have hlt : l.val < j.val := (Finset.mem_filter.mp hl).2
          refine ⟨⟨l.val, Nat.lt_succ_of_lt l.isLt⟩, ?_, Fin.ext rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
        · intro l hl
          have hlt : l.val < k := lt_trans (Finset.mem_filter.mp hl).2 hj
          simp [f, hlt]
      rw [hsum_eq]
      exact hf'_good ⟨j.val, hj⟩
    · have hjk : j.val = k := by have := j.isLt; omega
      have hfj : f j = i0 := by simp [f, hj]
      rw [hfj]
      have hsum_eq : (∑ l ∈ Finset.univ.filter (fun l : Fin (k + 1) => l < j), w (f l)) =
          ∑ x ∈ T.erase i0, w x := by
        rw [← hf'_img, Finset.sum_image (fun a _ b _ h => hf'_inj h)]
        refine Finset.sum_bij (fun l hl => ⟨l.val, by have : l.val < j.val := (Finset.mem_filter.mp hl).2; omega⟩)
          ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro l1 _ l2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
        · intro l _
          refine ⟨⟨l.val, Nat.lt_succ_of_lt l.isLt⟩, ?_, Fin.ext rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by show l.val < j.val; omega⟩
        · intro l hl
          have hlt : l.val < k := by have : l.val < j.val := (Finset.mem_filter.mp hl).2; omega
          simp [f, hlt]
      rw [hsum_eq]
      exact hi0_le

end PEqualNP.Outside.L_pcx_462_aux

open PEqualNP.Outside.L_pcx_462_aux MvPolynomial PEqualNP.ProofComplexity

theorem PEqualNP.Outside.L_pcx_462 :
    (∀ (V : Type) (F : Set (MvPolynomial V (ZMod 2))) (t B : ℕ),
  let I := Fin t
  let P := MvPolynomial V (ZMod 2)
  ∀ (E : I → Set P) (D w : I → ℕ) (p : P),
    let fits := ∀ T : Finset I, T.Nonempty → ∃ i ∈ T,
      p.totalDegree + D i + (∑ j ∈ T.erase i, w j) ≤ B
    let good := fun (π : Equiv.Perm I) => ∀ j : I,
      p.totalDegree + D (π j) + (∑ l ∈ Finset.univ.filter (fun l : I => l < j), w (π l)) ≤ B
    (fits ↔ ∃ π : Equiv.Perm I, good π) ∧
    ((∀ i, PEqualNP.ProofComplexity.PCRefutable (F ∪ E i) (D i)) →
     (∀ i, ∀ f ∈ E i, f.totalDegree ≤ D i → f.totalDegree ≤ w i) →
     ¬ PEqualNP.ProofComplexity.PCDerivable F B p →
     ∀ π : Equiv.Perm I, good π →
       ∃ e : I → P, (∀ i, e i ∈ E i ∧ (e i).totalDegree ≤ D i) ∧
         ∀ h : ℕ, h ≤ t →
           ¬ PEqualNP.ProofComplexity.PCDerivable F B
             (p * ∏ j ∈ Finset.univ.filter (fun j : I => j.val < h), e (π j)))) := by
  intro V F t B
  dsimp only
  intro E D w p
  constructor
  · constructor
    · intro hfits
      obtain ⟨f, hf_inj, _, hf_good⟩ := exists_inj_good D w hfits t Finset.univ (by simp)
      let π : Equiv.Perm (Fin t) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
      exact ⟨π, fun j => hf_good j⟩
    · rintro ⟨π, hgood⟩ T hT
      let S : Finset (Fin t) := T.image π.symm
      have hSne : S.Nonempty := hT.image π.symm
      let jmax : Fin t := S.max' hSne
      have hjmax_mem : jmax ∈ S := Finset.max'_mem S hSne
      have hi_mem : π jmax ∈ T := by
        rcases Finset.mem_image.mp hjmax_mem with ⟨x, hxT, hxeq⟩
        have : π jmax = x := by rw [← hxeq, Equiv.apply_symm_apply]
        rwa [this]
      refine ⟨π jmax, hi_mem, ?_⟩
      have hsum_le : (∑ x ∈ T.erase (π jmax), w x) ≤
          ∑ l ∈ Finset.univ.filter (fun l : Fin t => l < jmax), w (π l) := by
        have hsub : (T.erase (π jmax)).image π.symm ⊆ Finset.univ.filter (fun l : Fin t => l < jmax) := by
          intro l hl
          rcases Finset.mem_image.mp hl with ⟨x, hx, rfl⟩
          have hmemS : π.symm x ∈ S := Finset.mem_image_of_mem π.symm (Finset.erase_subset _ _ hx)
          have hle : π.symm x ≤ jmax := Finset.le_max' S _ hmemS
          have hne : π.symm x ≠ jmax := fun h =>
            (Finset.mem_erase.mp hx).1 (by rw [← h, Equiv.apply_symm_apply])
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_le_of_ne hle hne⟩
        have hrew : (∑ x ∈ T.erase (π jmax), w x) =
            ∑ l ∈ (T.erase (π jmax)).image π.symm, w (π l) := by
          rw [Finset.sum_image (fun a _ b _ h => π.symm.injective h)]
          refine Finset.sum_congr rfl (fun x _ => by simp)
        rw [hrew]
        exact Finset.sum_le_sum_of_subset hsub
      have hg := hgood jmax
      omega
  · intro href hw hnp π hgood
    have hstep : ∀ (h : ℕ) (hh : h ≤ t),
        ∃ f : Fin h → MvPolynomial V (ZMod 2),
          (∀ j : Fin h, f j ∈ E (π ⟨j.val, lt_of_lt_of_le j.isLt hh⟩) ∧
            (f j).totalDegree ≤ D (π ⟨j.val, lt_of_lt_of_le j.isLt hh⟩)) ∧
          ∀ m : ℕ, (hm : m ≤ h) →
            ¬ PCDerivable F B (p * ∏ j ∈ Finset.univ.filter (fun j : Fin h => j.val < m), f j) := by
      intro h
      induction h with
      | zero =>
        intro _
        refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun m hm => ?_⟩
        have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
        subst hm0
        simpa using hnp
      | succ h ih =>
        intro hh
        obtain ⟨f0, hf0_mem, hf0_nd⟩ := ih (Nat.le_of_succ_le hh)
        let Q : MvPolynomial V (ZMod 2) := p * ∏ j : Fin h, f0 j
        have hQ_nd : ¬ PCDerivable F B Q := by
          have h1 := hf0_nd h (le_refl h)
          have hfilt : (Finset.univ : Finset (Fin h)).filter (fun j => j.val < h) = Finset.univ := by
            ext j; simp
          rwa [hfilt] at h1
        have hQ_deg : Q.totalDegree ≤ p.totalDegree +
            ∑ l ∈ Finset.univ.filter (fun l : Fin t => l < ⟨h, hh⟩), w (π l) := by
          have h1 : Q.totalDegree ≤ p.totalDegree + ∑ j : Fin h, (f0 j).totalDegree :=
            (totalDegree_mul _ _).trans (Nat.add_le_add_left (totalDegree_finset_prod_le _ _) _)
          have h2 : (∑ j : Fin h, (f0 j).totalDegree) ≤
              ∑ j : Fin h, w (π ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_succ_le hh)⟩) :=
            Finset.sum_le_sum (fun j _ => hw _ _ (hf0_mem j).1 (hf0_mem j).2)
          have h3 : (∑ j : Fin h, w (π ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_succ_le hh)⟩)) =
              ∑ l ∈ Finset.univ.filter (fun l : Fin t => l < ⟨h, hh⟩), w (π l) := by
            refine Finset.sum_bij (fun j _ => ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_of_succ_le hh)⟩)
              ?_ ?_ ?_ ?_
            · intro j _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
            · intro j1 _ j2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
            · intro l hl
              have hlt : l.val < h := (Finset.mem_filter.mp hl).2
              exact ⟨⟨l.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
            · intro _ _; rfl
          omega
        have hQD : Q.totalDegree + D (π ⟨h, hh⟩) ≤ B := by
          have hg := hgood ⟨h, hh⟩
          omega
        have hex_next : ∃ g ∈ E (π ⟨h, hh⟩), g.totalDegree ≤ D (π ⟨h, hh⟩) ∧ ¬ PCDerivable F B (Q * g) := by
          by_contra hall
          push Not at hall
          have hder1 : PCDerivable F B (Q * 1) :=
            pcDerivable_lift_mul Q hQD hall (href (π ⟨h, hh⟩))
          rw [mul_one] at hder1
          exact hQ_nd hder1
        rcases hex_next with ⟨g, hgE, hgD, hg_nd⟩
        let f1 : Fin (h + 1) → MvPolynomial V (ZMod 2) := fun j =>
          if hj : j.val < h then f0 ⟨j.val, hj⟩ else g
        refine ⟨f1, ?_, ?_⟩
        · intro j
          dsimp only [f1]
          by_cases hj : j.val < h
          · simp only [hj, ↓reduceDIte]
            exact hf0_mem ⟨j.val, hj⟩
          · simp only [hj, ↓reduceDIte]
            have hjh : (⟨j.val, lt_of_lt_of_le j.isLt hh⟩ : Fin t) = ⟨h, hh⟩ :=
              Fin.ext (by dsimp only; have := j.isLt; omega)
            rw [hjh]
            exact ⟨hgE, hgD⟩
        · intro m hm
          by_cases hmh : m ≤ h
          · have hprod_eq : (∏ j ∈ Finset.univ.filter (fun j : Fin (h + 1) => j.val < m), f1 j) =
                ∏ j ∈ Finset.univ.filter (fun j : Fin h => j.val < m), f0 j := by
              refine Finset.prod_bij (fun j hj => ⟨j.val, lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hmh⟩)
                ?_ ?_ ?_ ?_
              · intro j hj; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
              · intro j1 _ j2 _ heq; exact Fin.ext (by simpa using congrArg Fin.val heq)
              · intro j hj
                refine ⟨⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, ?_, Fin.ext rfl⟩
                exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
              · intro j hj
                have hlt : j.val < h := lt_of_lt_of_le (Finset.mem_filter.mp hj).2 hmh
                simp [f1, hlt]
            rw [hprod_eq]
            exact hf0_nd m hmh
          · have hm_eq : m = h + 1 := by omega
            subst hm_eq
            have hfilt_all : (Finset.univ : Finset (Fin (h + 1))).filter (fun j => j.val < h + 1) = Finset.univ := by
              ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact j.isLt
            rw [hfilt_all, Fin.prod_univ_castSucc]
            have hcast : (∏ j : Fin h, f1 j.castSucc) = ∏ j : Fin h, f0 j := by
              refine Finset.prod_congr rfl (fun j _ => ?_)
              simp [f1]
            have hlast : f1 (Fin.last h) = g := by simp [f1]
            rw [hcast, hlast, ← mul_assoc]
            exact hg_nd
    obtain ⟨f, hf_mem, hf_nd⟩ := hstep t (le_refl t)
    let e : Fin t → MvPolynomial V (ZMod 2) := fun i => f (π.symm i)
    refine ⟨e, fun i => ?_, fun h hh => ?_⟩
    · have h1 := hf_mem (π.symm i)
      simpa [e] using h1
    · have hprod_eq : (∏ j ∈ Finset.univ.filter (fun j : Fin t => j.val < h), e (π j)) =
          ∏ j ∈ Finset.univ.filter (fun j : Fin t => j.val < h), f j := by
        refine Finset.prod_congr rfl (fun j _ => by simp [e])
      rw [hprod_eq]
      exact hf_nd h hh
