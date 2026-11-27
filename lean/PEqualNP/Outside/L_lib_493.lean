import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_493_aux

open MvPolynomial PEqualNP.ProofComplexity

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

theorem add_self_eq_zero {n : ℕ} (p : Poly n) : p + p = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero]
  exact zmod2_add_self (p.coeff d)

noncomputable def litPoly {n : ℕ} (l : Literal (Fin n)) : Poly n :=
  if l.2 = true then 1 + X l.1 else X l.1

theorem clausePoly_eq_prod {n : ℕ} (C : Clause (Fin n)) :
    clausePoly C = ∏ l ∈ C, litPoly l := rfl

theorem litPoly_pair_add {n : ℕ} (i : Fin n) :
    litPoly (i, true) + litPoly (i, false) = 1 := by
  simp only [litPoly, ite_true, Bool.false_eq_true, ite_false]
  calc (1 + X i : Poly n) + X i = 1 + (X i + X i) := add_assoc _ _ _
    _ = 1 + 0 := by rw [add_self_eq_zero]
    _ = 1 := add_zero 1

theorem totalDegree_X_le_one {n : ℕ} (j : Fin n) : (X j : Poly n).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le (Finsupp.single j 1) (1 : ZMod 2)).trans (by simp)

theorem totalDegree_litPoly_le {n : ℕ} (l : Literal (Fin n)) : (litPoly l).totalDegree ≤ 1 := by
  unfold litPoly
  cases l.2
  · simp only [Bool.false_eq_true, ite_false]
    exact totalDegree_X_le_one l.1
  · simp only [ite_true]
    exact (totalDegree_add (1 : Poly n) (X l.1)).trans
      (max_le (by simp) (totalDegree_X_le_one l.1))

theorem totalDegree_clausePoly_le {n : ℕ} (K : Clause (Fin n)) :
    (clausePoly K).totalDegree ≤ K.card := by
  classical
  induction K using Finset.induction_on with
  | empty => simp [clausePoly]
  | @insert l K hl ih =>
    rw [clausePoly_eq_prod, Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    have h1 := totalDegree_mul (litPoly l) (clausePoly K)
    have h2 := totalDegree_litPoly_le l
    rw [clausePoly_eq_prod] at h1 ih
    omega

theorem pc_sum {n : ℕ} {F : Set (Poly n)} {D : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly n)
    (hf : ∀ a ∈ s, PCDerivable F D (f a)) : PCDerivable F D (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact PCDerivable.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact PCDerivable.add (hf a (Finset.mem_insert_self a s))
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

theorem pc_mul_lit {n : ℕ} {F : Set (Poly n)} {D : ℕ} (l : Literal (Fin n)) {p : Poly n}
    (hp : PCDerivable F D p) (hd : p.totalDegree + 1 ≤ D) :
    PCDerivable F D (litPoly l * p) := by
  have hdeg : (X l.1 * p).totalDegree ≤ D := by
    have h1 := totalDegree_mul (X l.1 : Poly n) p
    have h2 := totalDegree_X_le_one l.1
    omega
  have hX : PCDerivable F D (X l.1 * p) := PCDerivable.mulX l.1 hp hdeg
  unfold litPoly
  cases l.2
  · simpa using hX
  · simp only [ite_true, add_mul, one_mul]
    exact PCDerivable.add hp hX

theorem pc_clause_superset {n : ℕ} {F : Set (Clause (Fin n))} {D : Clause (Fin n)} (hD : D ∈ F)
    (S : Clause (Fin n)) (hdisj : Disjoint D S) (hcard : (D ∪ S).card ≤ n) :
    PCDerivable (cnfSystem F) n (clausePoly (D ∪ S)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.union_empty] at hcard ⊢
    exact PCDerivable.ax (Or.inr ⟨D, hD, rfl⟩) ((totalDegree_clausePoly_le D).trans hcard)
  | @insert l S hl ih =>
    have hdisj' : Disjoint D S := (Finset.disjoint_insert_right.mp hdisj).2
    have hlD : l ∉ D := (Finset.disjoint_insert_right.mp hdisj).1
    have hlDS : l ∉ D ∪ S := by
      rw [Finset.mem_union]
      tauto
    have hU : D ∪ insert l S = insert l (D ∪ S) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hU] at hcard ⊢
    rw [Finset.card_insert_of_notMem hlDS] at hcard
    have ih' := ih hdisj' (by omega)
    have htd := totalDegree_clausePoly_le (D ∪ S)
    rw [clausePoly_eq_prod, Finset.prod_insert hlDS]
    rw [clausePoly_eq_prod] at ih' htd
    exact pc_mul_lit l ih' (by omega)

def fullClause {n : ℕ} (a : Fin n → Bool) : Clause (Fin n) :=
  Finset.univ.image (fun i : Fin n => (i, !a i))

theorem card_fullClause {n : ℕ} (a : Fin n → Bool) : (fullClause a).card = n := by
  unfold fullClause
  rw [Finset.card_image_of_injective _ (fun i j h => (Prod.mk.inj h).1),
    Finset.card_univ, Fintype.card_fin]

theorem subset_fullClause_of_not_sat {n : ℕ} (a : Fin n → Bool) (D : Clause (Fin n))
    (h : ¬ ClauseSat a D) : D ⊆ fullClause a := by
  intro l hl
  have hne : a l.1 ≠ l.2 := fun heq => h ⟨l, hl, heq⟩
  have hl2 : l.2 = !a l.1 := by
    cases ha : a l.1 <;> cases hb : l.2 <;> simp_all
  rw [fullClause, Finset.mem_image]
  refine ⟨l.1, Finset.mem_univ _, ?_⟩
  ext
  · rfl
  · exact hl2.symm

def miss {n : ℕ} (K : Clause (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => (i, true) ∉ K ∧ (i, false) ∉ K)

def Proper {n : ℕ} (K : Clause (Fin n)) : Prop :=
  ∀ i : Fin n, ¬ ((i, true) ∈ K ∧ (i, false) ∈ K)

def falsifiers {n : ℕ} (K : Clause (Fin n)) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun a : Fin n → Bool => ∀ l ∈ K, a l.1 ≠ l.2)

theorem mem_falsifiers_iff {n : ℕ} (K : Clause (Fin n)) (a : Fin n → Bool) :
    a ∈ falsifiers K ↔ ¬ ClauseSat a K := by
  simp only [falsifiers, Finset.mem_filter, Finset.mem_univ, true_and, ClauseSat]
  constructor
  · rintro h ⟨l, hl, heq⟩
    exact h l hl heq
  · intro h l hl heq
    exact h ⟨l, hl, heq⟩

theorem clausePoly_eq_sum_full {n : ℕ} :
    ∀ (k : ℕ) (K : Clause (Fin n)), Proper K → (miss K).card = k →
      clausePoly K = ∑ a ∈ falsifiers K, clausePoly (fullClause a)
  | 0, K, hprop, hcard => by
    have hmiss : miss K = ∅ := Finset.card_eq_zero.mp hcard
    have hcov : ∀ i : Fin n, (i, true) ∈ K ∨ (i, false) ∈ K := by
      intro i
      by_contra h
      have hi : i ∈ miss K := by
        rw [miss, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, not_or.mp h⟩
      rw [hmiss] at hi
      exact Finset.notMem_empty i hi
    let a0 : Fin n → Bool := fun i => decide ((i, false) ∈ K)
    have hKeq : K = fullClause a0 := by
      ext ⟨i, b⟩
      rw [fullClause, Finset.mem_image]
      constructor
      · intro hmem
        refine ⟨i, Finset.mem_univ i, ?_⟩
        ext
        · rfl
        · simp only [a0]
          cases b
          · simp [hmem]
          · have hnf : (i, false) ∉ K := fun hf => hprop i ⟨hmem, hf⟩
            simp [hnf]
      · rintro ⟨j, _, hj⟩
        have hji : j = i := (Prod.mk.inj hj).1
        have hjb : (!a0 j) = b := (Prod.mk.inj hj).2
        subst hji
        subst hjb
        simp only [a0]
        by_cases hf : (j, false) ∈ K
        · simp [hf]
        · simp only [hf, decide_false, Bool.not_false]
          exact (hcov j).resolve_right hf
    have hfilt : falsifiers K = {a0} := by
      ext a
      rw [mem_falsifiers_iff, Finset.mem_singleton]
      constructor
      · intro hns
        funext i
        by_cases hf : (i, false) ∈ K
        · have hne : a i ≠ false := fun he => hns ⟨(i, false), hf, he⟩
          simp only [a0, hf, decide_true]
          cases ha : a i <;> simp_all
        · have ht : (i, true) ∈ K := (hcov i).resolve_right hf
          have hne : a i ≠ true := fun he => hns ⟨(i, true), ht, he⟩
          simp only [a0, hf, decide_false]
          cases ha : a i <;> simp_all
      · rintro rfl ⟨⟨i, b⟩, hmem, heq⟩
        rw [hKeq, fullClause, Finset.mem_image] at hmem
        obtain ⟨j, _, hj⟩ := hmem
        have hji : j = i := (Prod.mk.inj hj).1
        have hjb : (!a0 j) = b := (Prod.mk.inj hj).2
        subst hji
        subst hjb
        cases h : a0 j <;> simp_all
    rw [hfilt, Finset.sum_singleton, hKeq]
  | k + 1, K, hprop, hcard => by
    have hne : (miss K).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hne
    have hni : (i, true) ∉ K ∧ (i, false) ∉ K := (Finset.mem_filter.mp hi).2
    let K1 : Clause (Fin n) := insert (i, true) K
    let K2 : Clause (Fin n) := insert (i, false) K
    have hprop1 : Proper K1 := by
      intro j ⟨ht, hf⟩
      rw [Finset.mem_insert] at ht hf
      rcases ht with h1 | h1 <;> rcases hf with h2 | h2
      · have := (Prod.mk.inj h1).2
        have := (Prod.mk.inj h2).2
        simp_all
      · have hji : j = i := (Prod.mk.inj h1).1
        subst hji
        exact hni.2 h2
      · have hji : j = i := (Prod.mk.inj h2).1
        subst hji
        exact hni.1 h1
      · exact hprop j ⟨h1, h2⟩
    have hprop2 : Proper K2 := by
      intro j ⟨ht, hf⟩
      rw [Finset.mem_insert] at ht hf
      rcases ht with h1 | h1 <;> rcases hf with h2 | h2
      · have := (Prod.mk.inj h1).2
        have := (Prod.mk.inj h2).2
        simp_all
      · have hji : j = i := (Prod.mk.inj h1).1
        subst hji
        exact hni.2 h2
      · have hji : j = i := (Prod.mk.inj h2).1
        subst hji
        exact hni.1 h1
      · exact hprop j ⟨h1, h2⟩
    have hm1 : miss K1 = (miss K).erase i := by
      ext j
      simp only [miss, K1, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩
        exact ⟨fun hji => h1 (by subst hji; rfl), h2, h4⟩
      · rintro ⟨hne', h1, h2⟩
        exact ⟨⟨fun h => hne' (Prod.mk.inj h).1, h1⟩, ⟨fun h => hne' (Prod.mk.inj h).1, h2⟩⟩
    have hm2 : miss K2 = (miss K).erase i := by
      ext j
      simp only [miss, K2, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_insert, not_or]
      constructor
      · rintro ⟨⟨_, h2⟩, ⟨h3, h4⟩⟩
        exact ⟨fun hji => h3 (by subst hji; rfl), h2, h4⟩
      · rintro ⟨hne', h1, h2⟩
        exact ⟨⟨fun h => hne' (Prod.mk.inj h).1, h1⟩, ⟨fun h => hne' (Prod.mk.inj h).1, h2⟩⟩
    have hc1 : (miss K1).card = k := by
      rw [hm1, Finset.card_erase_of_mem hi, hcard]
      omega
    have hc2 : (miss K2).card = k := by
      rw [hm2, Finset.card_erase_of_mem hi, hcard]
      omega
    have ih1 := clausePoly_eq_sum_full k K1 hprop1 hc1
    have ih2 := clausePoly_eq_sum_full k K2 hprop2 hc2
    have hpoly : clausePoly K = clausePoly K1 + clausePoly K2 := by
      rw [clausePoly_eq_prod, clausePoly_eq_prod, clausePoly_eq_prod]
      rw [Finset.prod_insert hni.1, Finset.prod_insert hni.2, ← add_mul, litPoly_pair_add, one_mul]
    have hdisj : Disjoint (falsifiers K1) (falsifiers K2) := by
      rw [Finset.disjoint_left]
      intro a ha1 ha2
      have h1 : ¬ ClauseSat a K1 := (mem_falsifiers_iff K1 a).mp ha1
      have h2 : ¬ ClauseSat a K2 := (mem_falsifiers_iff K2 a).mp ha2
      cases hai : a i
      · exact h2 ⟨(i, false), Finset.mem_insert_self _ _, hai⟩
      · exact h1 ⟨(i, true), Finset.mem_insert_self _ _, hai⟩
    have hunion : falsifiers K = falsifiers K1 ∪ falsifiers K2 := by
      ext a
      rw [Finset.mem_union, mem_falsifiers_iff, mem_falsifiers_iff, mem_falsifiers_iff]
      constructor
      · intro hns
        cases hai : a i
        · left
          rintro ⟨l, hl, hsat⟩
          rcases Finset.mem_insert.mp hl with rfl | hl
          · simp_all
          · exact hns ⟨l, hl, hsat⟩
        · right
          rintro ⟨l, hl, hsat⟩
          rcases Finset.mem_insert.mp hl with rfl | hl
          · simp_all
          · exact hns ⟨l, hl, hsat⟩
      · rintro (h1 | h2) ⟨l, hl, hsat⟩
        · exact h1 ⟨l, Finset.mem_insert_of_mem hl, hsat⟩
        · exact h2 ⟨l, Finset.mem_insert_of_mem hl, hsat⟩
    rw [hpoly, ih1, ih2, hunion, Finset.sum_union hdisj]

def toZ2 {n : ℕ} (a : Fin n → Bool) : Fin n → ZMod 2 :=
  fun i => if a i then 1 else 0

theorem eval_litPoly {n : ℕ} (a : Fin n → Bool) (l : Literal (Fin n)) :
    eval (toZ2 a) (litPoly l) = if a l.1 = l.2 then 0 else 1 := by
  rcases l with ⟨i, b⟩
  unfold litPoly toZ2
  cases ha : a i <;> cases b <;> simp [ha]
  decide

theorem eval_clausePoly_eq_zero_iff {n : ℕ} (a : Fin n → Bool) (C : Clause (Fin n)) :
    eval (toZ2 a) (clausePoly C) = 0 ↔ ClauseSat a C := by
  rw [clausePoly_eq_prod, map_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨l, hl, h0⟩
    rw [eval_litPoly] at h0
    by_cases heq : a l.1 = l.2
    · exact ⟨l, hl, heq⟩
    · simp [heq] at h0
  · rintro ⟨l, hl, heq⟩
    exact ⟨l, hl, by simp [eval_litPoly, heq]⟩

theorem eval_eq_zero_of_pc {n : ℕ} {F : Set (Clause (Fin n))} {D : ℕ} (a : Fin n → Bool)
    (ha : Satisfies a F) {p : Poly n} (hp : PCDerivable (cnfSystem F) D p) :
    eval (toZ2 a) p = 0 := by
  induction hp with
  | ax hmem _ =>
    rcases hmem with ⟨v, rfl⟩ | ⟨C, hCF, rfl⟩
    · simp only [map_add, map_mul, eval_X, toZ2]
      cases a v <;> decide
    · exact (eval_clausePoly_eq_zero_iff a C).mpr (ha C hCF)
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

theorem main (n : ℕ) (F : Set (Clause (Fin n))) (C : Clause (Fin n)) (hprop : Proper C) :
    (∀ a : Fin n → Bool, Satisfies a F → ClauseSat a C) ↔
      PCDerivable (cnfSystem F) n (clausePoly C) := by
  constructor
  · intro hsem
    rw [clausePoly_eq_sum_full (miss C).card C hprop rfl]
    refine pc_sum _ _ fun a ha => ?_
    have hns : ¬ ClauseSat a C := (mem_falsifiers_iff C a).mp ha
    have hnsF : ¬ Satisfies a F := fun hsat => hns (hsem a hsat)
    have hex : ∃ D ∈ F, ¬ ClauseSat a D := by
      by_contra h
      apply hnsF
      intro D hD
      by_contra hD'
      exact h ⟨D, hD, hD'⟩
    obtain ⟨D, hDF, hnsD⟩ := hex
    have hsub : D ⊆ fullClause a := subset_fullClause_of_not_sat a D hnsD
    have hU : D ∪ (fullClause a \ D) = fullClause a := Finset.union_sdiff_of_subset hsub
    rw [← hU]
    refine pc_clause_superset hDF (fullClause a \ D) disjoint_sdiff_self_right ?_
    rw [hU, card_fullClause]
  · intro hpc a hsat
    exact (eval_clausePoly_eq_zero_iff a C).mp (eval_eq_zero_of_pc a hsat hpc)

end PEqualNP.Outside.L_lib_493_aux

theorem PEqualNP.Outside.L_lib_493 : ∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (C : PEqualNP.ProofComplexity.Clause (Fin n)),
  (∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) →
  ((∀ a : Fin n → Bool, PEqualNP.ProofComplexity.Satisfies a F → PEqualNP.ProofComplexity.ClauseSat a C) ↔
    PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) n (PEqualNP.ProofComplexity.clausePoly C)) := by
  intro n F C hprop
  exact PEqualNP.Outside.L_lib_493_aux.main n F C hprop
