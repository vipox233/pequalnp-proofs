import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_467

open MvPolynomial PEqualNP.ProofComplexity

section Gen

variable {σ : Type} [Fintype σ] [DecidableEq σ]

noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]

lemma zmod2_pow (x : ZMod 2) : ∀ n : ℕ, 1 ≤ n → x ^ n = x
  | 0, h => by omega
  | 1, _ => pow_one x
  | n + 2, _ => by
    rw [pow_succ, zmod2_pow x (n + 1) (by omega)]
    revert x; decide

lemma eval_mlin (x : σ → ZMod 2) (a : σ →₀ ℕ) (c : ZMod 2) :
    eval x (monomial (mlin a) c) = eval x (monomial a c) := by
  simp only [eval_monomial]
  congr 1
  unfold mlin
  rw [Finsupp.prod_mapRange_index (fun _ => by simp)]
  apply Finsupp.prod_congr
  intro v hv
  have : a v ≠ 0 := Finsupp.mem_support_iff.mp hv
  rw [show min (a v) 1 = 1 by omega, pow_one, zmod2_pow _ _ (by omega)]

lemma sum_eq_degree (a : σ →₀ ℕ) : (a.sum fun _ e => e) = ∑ v, a v :=
  Finsupp.sum_fintype _ _ (fun _ => rfl)

lemma coeff_top_eq_zero (q : MvPolynomial σ (ZMod 2)) (D : ℕ) (hq : q.totalDegree ≤ D)
    (h0 : ∀ x : σ → ZMod 2, eval x q = 0) (m : σ →₀ ℕ) (hm1 : ∀ v, m v ≤ 1)
    (hmD : D ≤ ∑ v, m v) : q.coeff m = 0 := by
  classical
  set q' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ q.support, monomial (mlin a) (q.coeff a) with hq'
  have hq'0 : q' = 0 := by
    refine eq_zero_of_multilinear q' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      rw [hq', map_sum]
      simp_rw [eval_mlin]
      rw [← map_sum, ← q.as_sum]
      exact h0 x
  have hc : q'.coeff m = q.coeff m := by
    rw [hq', coeff_sum]
    simp only [coeff_monomial]
    have hmm : mlin m = m := by
      ext v; rw [mlin_apply]; have := hm1 v; omega
    by_cases hms : m ∈ q.support
    · rw [Finset.sum_eq_single m]
      · rw [if_pos hmm]
      · intro a ha hne
        rw [if_neg]
        intro hma
        apply hne
        have hle : ∀ v, m v ≤ a v := fun v => by rw [← hma, mlin_apply]; omega
        have hdeg : ∑ v, a v ≤ D := by
          have := le_totalDegree ha
          rw [sum_eq_degree] at this
          omega
        have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun v _ => hle v)).mp
          (le_antisymm (Finset.sum_le_sum fun v _ => hle v) (by omega))
        ext v; exact (heq v (Finset.mem_univ v)).symm
      · intro h; exact absurd hms h
    · have h0' : q.coeff m = 0 := by simpa using hms
      rw [h0']
      refine Finset.sum_eq_zero fun a ha => ?_
      split_ifs with hma
      · exfalso
        have hle : ∀ v, m v ≤ a v := fun v => by rw [← hma, mlin_apply]; omega
        have hdeg : ∑ v, a v ≤ D := by
          have := le_totalDegree ha
          rw [sum_eq_degree] at this
          omega
        have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun v _ => hle v)).mp
          (le_antisymm (Finset.sum_le_sum fun v _ => hle v) (by omega))
        have : a = m := by ext v; exact (heq v (Finset.mem_univ v)).symm
        exact hms (this ▸ ha)
      · rfl
  rw [← hc, hq'0]; rfl

end Gen


section Spec

variable (m k : ℕ)

abbrev Tup := Fin m × (Fin k → Option (Fin m))
abbrev TT := {U : Finset (Fin m) // U.Nonempty ∧ U.card ≤ k+1}
abbrev Pp := MvPolynomial (Fin m × Option (Fin k)) (ZMod 2)

noncomputable def prof (S : Finset (Fin m)) (U : TT m k) : ZMod 2 :=
  if U.val ⊆ S then 1 else 0

noncomputable def part (S : Finset (Fin m)) (j : Option (Fin k)) : Pp m k :=
  ∑ i ∈ S, X (i, j)

noncomputable def test (S : Finset (Fin m)) : Pp m k :=
  part m k S none * ∏ j : Fin k, (1 + part m k S (some j))

def supp (t : Tup m k) : Finset (Fin m) :=
  insert t.1 (Finset.univ.biUnion fun j => (t.2 j).toFinset)

noncomputable def ex (t : Tup m k) : (Fin m × Option (Fin k)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    match v.2 with
    | none => if v.1 = t.1 then 1 else 0
    | some j => if t.2 j = some v.1 then 1 else 0

lemma ex_none (t : Tup m k) (i : Fin m) : ex m k t (i, none) = if i = t.1 then 1 else 0 := by
  simp [ex]

lemma ex_some (t : Tup m k) (i : Fin m) (j : Fin k) :
    ex m k t (i, some j) = if t.2 j = some i then 1 else 0 := by
  simp [ex]

noncomputable def ey (o : Option (Fin m)) (j : Fin k) : (Fin m × Option (Fin k)) →₀ ℕ :=
  match o with
  | none => 0
  | some i => Finsupp.single (i, some j) 1

lemma ey_apply (o : Option (Fin m)) (j : Fin k) (i : Fin m) (o' : Option (Fin k)) :
    ey m k o j (i, o') = if o' = some j ∧ o = some i then 1 else 0 := by
  cases o with
  | none => simp [ey]
  | some a =>
    simp only [ey, Finsupp.single_apply, Prod.mk.injEq, Option.some.injEq]
    by_cases h1 : a = i <;> by_cases h2 : o' = some j <;> simp [h1, h2, eq_comm]

lemma ex_eq (t : Tup m k) :
    Finsupp.single (t.1, (none : Option (Fin k))) 1 + ∑ j, ey m k (t.2 j) j = ex m k t := by
  ext ⟨i, o⟩
  cases o with
  | none =>
    rw [ex_none, Finsupp.add_apply, Finsupp.finsetSum_apply]
    simp [ey_apply, Finsupp.single_apply, eq_comm]
  | some j0 =>
    rw [ex_some, Finsupp.add_apply, Finsupp.finsetSum_apply]
    simp [ey_apply, Finsupp.single_apply]
    by_cases h : t.2 j0 = some i
    · rw [if_pos h, Finset.card_eq_one]
      refine ⟨j0, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl; exact ⟨rfl, h⟩
    · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨rfl, hx⟩
      exact h hx

noncomputable def M (t : Tup m k) : Pp m k := monomial (ex m k t) 1

lemma test_exp (S : Finset (Fin m)) :
    test m k S = ∑ t : Tup m k, if supp m k t ⊆ S then M m k t else 0 := by
  classical
  have h1 : ∀ j : Fin k, (1 + part m k S (some j))
      = ∑ o ∈ S.insertNone, monomial (ey m k o j) (1 : ZMod 2) := by
    intro j
    rw [Finset.sum_insertNone]
    simp [ey, part, X]
  have h0 : part m k S none
      = ∑ i ∈ S, monomial (Finsupp.single (i, (none : Option (Fin k))) 1) (1 : ZMod 2) := rfl
  rw [test, h0, Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_univ_sum,
    Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext t
    simp [supp, Finset.insert_subset_iff, Finset.mem_insertNone, Fintype.mem_piFinset,
      Finset.biUnion_subset, Finset.subset_iff, Option.mem_toFinset, Option.mem_def]
    exact fun _ => ⟨fun h a x hx => h x a hx, fun h a x hx => h x a hx⟩
  · intro t _
    rw [← monomial_sum_one, monomial_mul_monomial, mul_one, M]
    rw [← ex_eq]

lemma ex_inj : Function.Injective (ex m k) := by
  intro t t0 h
  have hv : ∀ v, ex m k t v = ex m k t0 v := fun v => by rw [h]
  have h1 : t.1 = t0.1 := by
    have := hv (t0.1, none)
    rw [ex_none, ex_none] at this
    by_contra hne
    rw [if_neg (Ne.symm hne), if_pos rfl] at this
    exact absurd this (by norm_num)
  have h2 : t.2 = t0.2 := by
    funext j
    rcases ha : t.2 j with _ | a <;> rcases hb : t0.2 j with _ | b
    · rfl
    · have := hv (b, some j)
      rw [ex_some, ex_some, ha, hb] at this
      simp at this
    · have := hv (a, some j)
      rw [ex_some, ex_some, ha, hb] at this
      simp at this
    · have := hv (a, some j)
      rw [ex_some, ex_some, ha, hb] at this
      by_contra hne
      have : a ≠ b := fun e => hne (by rw [e])
      simp_all
  exact Prod.ext h1 h2

lemma coeff_M (t t0 : Tup m k) : (M m k t).coeff (ex m k t0) = if t = t0 then 1 else 0 := by
  rw [M, coeff_monomial]
  by_cases h : t = t0
  · subst h; simp
  · rw [if_neg (fun e => h (ex_inj m k e)), if_neg h]

lemma ex_le_one (t : Tup m k) (v : Fin m × Option (Fin k)) : ex m k t v ≤ 1 := by
  obtain ⟨i, o⟩ := v
  cases o with
  | none => rw [ex_none]; split_ifs <;> omega
  | some j => rw [ex_some]; split_ifs <;> omega

lemma deg_ex (t : Tup m k) (ht : ∀ j, t.2 j ≠ none) : ∑ v, ex m k t v = k + 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_option, ex_none, ex_some]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  have hA : ∑ i : Fin m, (if i = t.1 then 1 else 0 : ℕ) = 1 := by simp
  have hB : ∀ j : Fin k, ∑ i : Fin m, (if t.2 j = some i then 1 else 0 : ℕ) = 1 := by
    intro j
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (ht j)
    rw [ha]; simp
  rw [hA, Finset.sum_congr rfl (fun j _ => hB j)]
  simp [add_comm]

lemma supp_mem (t : Tup m k) : (supp m k t).Nonempty ∧ (supp m k t).card ≤ k + 1 := by
  refine ⟨Finset.insert_nonempty _ _, ?_⟩
  refine (Finset.card_insert_le _ _).trans ?_
  have : (Finset.univ.biUnion fun j => (t.2 j).toFinset).card ≤ k := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ j : Fin k, (t.2 j).toFinset.card ≤ ∑ _j : Fin k, 1 :=
          Finset.sum_le_sum fun j _ => by cases t.2 j <;> simp
      _ = k := by simp
  omega

lemma exists_top (U : TT m k) : ∃ t : Tup m k, supp m k t = U.val ∧ ∀ j, t.2 j ≠ none := by
  obtain ⟨i0, hi0⟩ := U.2.1
  set l := U.val.toList with hl
  have hlen : l.length ≤ k + 1 := by rw [hl, Finset.length_toList]; exact U.2.2
  let g : ℕ → Fin m := fun n => l.getD n i0
  have hg : ∀ n, g n ∈ U.val := by
    intro n
    by_cases h : n < l.length
    · show l.getD n i0 ∈ U.val
      rw [List.getD_eq_getElem _ _ h]
      exact Finset.mem_toList.mp (List.getElem_mem h)
    · show l.getD n i0 ∈ U.val
      rw [List.getD_eq_default _ _ (by omega)]
      exact hi0
  refine ⟨(g 0, fun j => some (g (j.val + 1))), ?_, fun j => by simp⟩
  apply Finset.Subset.antisymm
  · intro u hu
    simp only [supp, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Option.mem_toFinset, Option.mem_def, Option.some.injEq] at hu
    rcases hu with rfl | ⟨j, rfl⟩
    · exact hg 0
    · exact hg _
  · intro u hu
    have hu' : u ∈ l := Finset.mem_toList.mpr hu
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hu'
    simp only [supp, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Option.mem_toFinset, Option.mem_def, Option.some.injEq]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · left; subst h0; show l[0] = l.getD 0 i0; rw [List.getD_eq_getElem _ _ hn]
    · right
      refine ⟨⟨n - 1, by omega⟩, ?_⟩
      simp only [g]
      rw [show n - 1 + 1 = n by omega, List.getD_eq_getElem _ _ hn]

lemma coeff_test_top (S : Finset (Fin m)) (U : TT m k) (t : Tup m k) (ht : supp m k t = U.val) :
    (test m k S).coeff (ex m k t) = prof m k S U := by
  rw [test_exp, coeff_sum, Finset.sum_eq_single t]
  · rw [prof, ← ht]; split_ifs <;> simp [coeff_M]
  · intro b _ hb; split_ifs <;> simp [coeff_M, hb]
  · simp

lemma part_deg (S : Finset (Fin m)) (j : Option (Fin k)) : (part m k S j).totalDegree ≤ 1 :=
  (totalDegree_finsetSum _ _).trans (Finset.sup_le fun i _ => (totalDegree_X _).le)

lemma test_deg (S : Finset (Fin m)) : (test m k S).totalDegree ≤ k + 1 := by
  rw [test]
  refine (totalDegree_mul _ _).trans ?_
  have h1 := part_deg m k S none
  have h2 : (∏ j : Fin k, (1 + part m k S (some j))).totalDegree ≤ k := by
    refine (totalDegree_finsetProd _ _).trans ?_
    calc ∑ j : Fin k, (1 + part m k S (some j)).totalDegree ≤ ∑ _j : Fin k, 1 :=
          Finset.sum_le_sum fun j _ =>
            (totalDegree_add _ _).trans (max_le (by simp) (part_deg m k S _))
      _ = k := by simp
  omega

lemma comb (d : Finset (Fin m) → ZMod 2) (h : ∑ S, d S • prof m k S = 0) :
    ∑ S, d S • test m k S = 0 := by
  simp_rw [test_exp, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun t _ => ?_
  have hU := congrFun h ⟨supp m k t, supp_mem m k t⟩
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, prof, Pi.zero_apply] at hU
  have : ∀ S, d S • (if supp m k t ⊆ S then M m k t else 0)
      = (d S * if supp m k t ⊆ S then 1 else 0) • M m k t := by
    intro S; split_ifs <;> simp
  simp_rw [this]
  rw [← Finset.sum_smul, hU, zero_smul]

lemma key0 (d : Finset (Fin m) → ZMod 2) (r : Pp m k) (hr : r.totalDegree ≤ k)
    (h0 : ∀ x, eval x (∑ S, d S • test m k S + r) = 0) : ∑ S, d S • prof m k S = 0 := by
  funext U
  obtain ⟨t, ht, hfull⟩ := exists_top m k U
  have hq : (∑ S, d S • test m k S + r).totalDegree ≤ k + 1 := by
    refine (totalDegree_add _ _).trans (max_le ?_ (by omega))
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun S _ => ?_)
    exact (totalDegree_smul_le _ _).trans (test_deg m k S)
  have hc := coeff_top_eq_zero _ (k + 1) hq h0 (ex m k t) (ex_le_one m k t)
    (deg_ex m k t hfull).ge
  have hr0 : r.coeff (ex m k t) = 0 := by
    apply coeff_eq_zero_of_totalDegree_lt
    have := deg_ex m k t hfull
    have e : ∑ i ∈ (ex m k t).support, (ex m k t) i = ∑ v, ex m k t v := by
      have := sum_eq_degree (ex m k t)
      rw [← this]; rfl
    omega
  rw [MvPolynomial.coeff_add, hr0, add_zero, coeff_sum] at hc
  simp only [coeff_smul, smul_eq_mul, coeff_test_top m k _ U t ht] at hc
  simpa [Finset.sum_apply] using hc

end Spec

section Main

variable (m k : ℕ)

noncomputable def bools : Set (Pp m k) := Set.range (fun v : Fin m × Option (Fin k) => X v * X v + X v)

lemma eval_bool (x : Fin m × Option (Fin k) → ZMod 2) (v : Fin m × Option (Fin k)) :
    eval x (X v * X v + X v : Pp m k) = 0 := by
  simp only [map_add, map_mul, eval_X]
  generalize x v = c
  revert c; decide

lemma sumH {N : Type} [AddCommGroup N] [Module (ZMod 2) N] (H : Finset (Finset (Fin m)))
    (c : Finset (Fin m) → ZMod 2) (v : Finset (Fin m) → N) :
    ∑ S, (if S ∈ H then c S else 0) • v S = ∑ S ∈ H, c S • v S := by
  simp [ite_smul, Finset.sum_ite_mem]

lemma dsum {N : Type} [AddCommGroup N] [Module (ZMod 2) N] (H : Finset (Finset (Fin m)))
    (c : Finset (Fin m) → ZMod 2) (S : Finset (Fin m)) (v : Finset (Fin m) → N) :
    ∑ S', ((if S' = S then 1 else 0) - (if S' ∈ H then c S' else 0)) • v S'
      = v S - ∑ S' ∈ H, c S' • v S' := by
  simp only [sub_smul, Finset.sum_sub_distrib, sumH, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma low_vanish (H : Finset (Finset (Fin m))) (g low : Finset (Fin m) → Pp m k)
    (hg : ∀ S ∈ H, g S = test m k S + low S) (hlow : ∀ S ∈ H, (low S).totalDegree ≤ k)
    (c : Finset (Fin m) → ZMod 2) (q : Pp m k) (hq : q.totalDegree ≤ k)
    (hc : ∀ x, eval x q = ∑ S ∈ H, c S * eval x (g S)) :
    ∑ S ∈ H, c S • prof m k S = 0 := by
  rw [← sumH]
  refine key0 m k _ (∑ S ∈ H, c S • low S - q) ?_ ?_
  · refine (totalDegree_sub _ _).trans (max_le ?_ hq)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun S hS => ?_)
    exact (totalDegree_smul_le _ _).trans (hlow S hS)
  · intro y
    have e : ∀ S ∈ H, c S * eval y (g S) = c S * eval y (test m k S) + c S * eval y (low S) := by
      intro S hS; rw [hg S hS, map_add, mul_add]
    rw [sumH, map_add, map_sub, hc y, Finset.sum_congr rfl e, Finset.sum_add_distrib,
      map_sum, map_sum]
    simp only [MvPolynomial.smul_eval]
    ring

lemma inv_main (H : Finset (Finset (Fin m))) (g low : Finset (Fin m) → Pp m k)
    (hg : ∀ S ∈ H, g S = test m k S + low S) (hlow : ∀ S ∈ H, (low S).totalDegree ≤ k)
    (hkill : ∀ c : Finset (Fin m) → ZMod 2, ∑ S ∈ H, c S • prof m k S = 0 →
      ∀ x, ∑ S ∈ H, c S * eval x (g S) = 0)
    (p : Pp m k)
    (hp : PCDerivable (bools m k ∪ Set.image g (H : Set (Finset (Fin m)))) (k + 1) p) :
    ∃ c : Finset (Fin m) → ZMod 2, ∀ x, eval x p = ∑ S ∈ H, c S * eval x (g S) := by
  classical
  induction hp with
  | @ax q hq hdeg =>
    rcases hq with ⟨v, rfl⟩ | ⟨S, hS, rfl⟩
    · exact ⟨0, fun x => by rw [eval_bool]; simp⟩
    · refine ⟨fun S' => if S' = S then 1 else 0, fun x => ?_⟩
      simp only [ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq' H S, if_pos (Finset.mem_coe.mp hS)]
  | zero => exact ⟨0, fun x => by simp⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨c1, h1⟩ := ih1
    obtain ⟨c2, h2⟩ := ih2
    refine ⟨c1 + c2, fun x => ?_⟩
    rw [map_add, h1, h2, ← Finset.sum_add_distrib]
    simp [add_mul]
  | @mulX j q _ hdeg ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨0, fun x => ?_⟩
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    by_cases hq0 : q = 0
    · subst hq0; simp
    · have hqd : q.totalDegree ≤ k := by
        rw [totalDegree_mul_of_isDomain (X_ne_zero j) hq0, totalDegree_X] at hdeg; omega
      have hz := low_vanish m k H g low hg hlow c q hqd hc
      rw [map_mul, hc x, hkill c hz x, mul_zero]

lemma kill_test (H : Finset (Finset (Fin m))) (c : Finset (Fin m) → ZMod 2)
    (h : ∑ S ∈ H, c S • prof m k S = 0) : ∑ S ∈ H, c S • test m k S = 0 := by
  rw [← sumH] at h ⊢
  exact comb m k _ h

lemma der_sum {F : Set (Pp m k)} {B : ℕ} (c : Finset (Fin m) → ZMod 2)
    (v : Finset (Fin m) → Pp m k) (H : Finset (Finset (Fin m))) :
    (∀ S ∈ H, PCDerivable F B (v S)) → PCDerivable F B (∑ S ∈ H, c S • v S) := by
  classical
  refine Finset.induction_on H ?_ ?_
  · intro _; simpa using (PCDerivable.zero : PCDerivable F B 0)
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    refine .add ?_ (ih fun S hS => h S (Finset.mem_insert_of_mem hS))
    have hz : c a = 0 ∨ c a = 1 := by
      generalize c a = z; revert z; decide
    rcases hz with hz | hz
    · rw [hz, zero_smul]; exact .zero
    · rw [hz, one_smul]; exact h a (Finset.mem_insert_self a s)

theorem part1 (H : Finset (Finset (Fin m))) (S : Finset (Fin m)) :
    PCDerivable (bools m k ∪ Set.image (test m k) (H : Set (Finset (Fin m)))) (k + 1)
        (test m k S) ↔
      prof m k S ∈ Submodule.span (ZMod 2) (Set.image (prof m k) (H : Set (Finset (Fin m)))) := by
  classical
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := inv_main m k H (test m k) 0 (fun S _ => by simp) (fun S _ => by simp)
      (fun c h x => by
        have := congrArg (eval x) (kill_test m k H c h)
        rw [map_sum] at this
        simpa [MvPolynomial.smul_eval] using this) _ hd
    have hk := key0 m k (fun S' => (if S' = S then 1 else 0) - (if S' ∈ H then c S' else 0)) 0
      (by simp) (fun x => by
        rw [add_zero, dsum, map_sub, map_sum, hc x]
        simp [MvPolynomial.smul_eval])
    rw [dsum, sub_eq_zero] at hk
    rw [hk]
    refine Submodule.sum_mem _ fun S' hS' => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hS'))
  · intro hs
    have gen : ∀ w ∈ Submodule.span (ZMod 2) (Set.image (prof m k) (H : Set (Finset (Fin m)))),
        ∃ c : Finset (Fin m) → ZMod 2, w = ∑ S' ∈ H, c S' • prof m k S' := by
      intro w hs
      induction hs using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨S', hS', rfl⟩ := hv
        refine ⟨fun S'' => if S'' = S' then 1 else 0, ?_⟩
        simp only [ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq' H S', if_pos (Finset.mem_coe.mp hS')]
      | zero => exact ⟨0, by simp⟩
      | add v w _ _ ihv ihw =>
        obtain ⟨c1, h1⟩ := ihv
        obtain ⟨c2, h2⟩ := ihw
        exact ⟨c1 + c2, by rw [h1, h2, ← Finset.sum_add_distrib]; simp [add_smul]⟩
      | smul a v _ ihv =>
        obtain ⟨c1, h1⟩ := ihv
        exact ⟨a • c1, by rw [h1, Finset.smul_sum]; simp [mul_smul]⟩
    obtain ⟨c, hc⟩ := gen _ hs
    have hk : ∑ S', ((if S' = S then 1 else 0) - (if S' ∈ H then c S' else 0)) • prof m k S' = 0 := by
      rw [dsum, hc, sub_self]
    have ht := comb m k _ hk
    rw [dsum, sub_eq_zero] at ht
    rw [ht]
    refine der_sum m k c _ H fun S' hS' => ?_
    exact .ax (Or.inr ⟨S', Finset.mem_coe.mpr hS', rfl⟩) (test_deg m k S')

theorem part3 (H : Finset (Finset (Fin m))) (low : Finset (Fin m) → Pp m k)
    (hli : LinearIndependent (ZMod 2) (fun S : H => prof m k S.val))
    (hlow : ∀ S ∈ H, (low S).totalDegree ≤ k) (p : Pp m k) (hp : p.totalDegree ≤ k)
    (hd : PCDerivable (bools m k ∪ Set.image (fun S => test m k S + low S)
      (H : Set (Finset (Fin m)))) (k + 1) p) :
    ∀ x, eval x p = 0 := by
  classical
  have hkill : ∀ c : Finset (Fin m) → ZMod 2, ∑ S ∈ H, c S • prof m k S = 0 →
      ∀ S ∈ H, c S = 0 := by
    intro c hc S hS
    have h1 : ∑ i : H, c i.val • prof m k i.val = 0 := by
      rw [Finset.sum_coe_sort H (fun S => c S • prof m k S)]; exact hc
    exact (Fintype.linearIndependent_iff.mp hli) (fun S' => c S'.val) h1 ⟨S, hS⟩
  obtain ⟨c, hc⟩ := inv_main m k H (fun S => test m k S + low S) low (fun _ _ => rfl) hlow
    (fun c h x => Finset.sum_eq_zero fun S hS => by rw [hkill c h S hS, zero_mul]) p hd
  have hz := low_vanish m k H (fun S => test m k S + low S) low (fun _ _ => rfl) hlow c p hp hc
  intro x
  rw [hc x]
  exact Finset.sum_eq_zero fun S hS => by rw [hkill c hz S hS, zero_mul]

lemma single_eq (U : TT m k) :
    (fun U' : TT m k => if U = U' then (1 : ZMod 2) else 0) = ∑ S ∈ U.val.powerset, prof m k S := by
  funext U'
  rw [Finset.sum_apply]
  simp only [prof]
  rw [Finset.sum_boole]
  by_cases hsub : U'.val ⊆ U.val
  · have e : Finset.filter (fun S => U'.val ⊆ S) U.val.powerset = Finset.Icc U'.val U.val := by
      ext S; simp [Finset.mem_Icc, Finset.le_iff_subset, and_comm]
    rw [e, Finset.card_Icc_finset hsub]
    by_cases heq : U = U'
    · subst heq; simp
    · have hlt : U'.val.card < U.val.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => heq (Subtype.ext h).symm⟩)
      rw [if_neg heq]
      obtain ⟨n, hn⟩ : ∃ n, U.val.card - U'.val.card = n + 1 := ⟨U.val.card - U'.val.card - 1, by omega⟩
      rw [hn, pow_succ]
      push_cast
      rw [show (2 : ZMod 2) = 0 from rfl, mul_zero]
  · rw [if_neg (fun (h : U = U') => hsub (by rw [h]))]
    have : Finset.filter (fun S => U'.val ⊆ S) U.val.powerset = ∅ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.notMem_empty, iff_false, not_and]
      intro hS h; exact hsub (h.trans hS)
    rw [this]; simp

lemma top_of (W : Submodule (ZMod 2) (TT m k → ZMod 2)) (h : ∀ S : TT m k, prof m k S.val ∈ W) :
    W = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro v
  rw [pi_eq_sum_univ v]
  refine Submodule.sum_mem _ fun U _ => Submodule.smul_mem _ _ ?_
  rw [single_eq]
  refine Submodule.sum_mem _ fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  by_cases hne : S.Nonempty
  · exact h ⟨S, hne, (Finset.card_le_card hS).trans U.2.2⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    have : prof m k ∅ = 0 := by
      funext U'
      simp only [prof, Pi.zero_apply, Finset.subset_empty]
      rw [if_neg (U'.2.1.ne_empty)]
    rw [this]; exact W.zero_mem

lemma card_TT : Fintype.card (TT m k) = ∑ j ∈ Finset.range (k + 1), m.choose (j + 1) := by
  classical
  rw [Fintype.card_subtype]
  have e : (Finset.univ.filter fun U : Finset (Fin m) => U.Nonempty ∧ U.card ≤ k + 1)
      = (Finset.range (k + 1)).biUnion (fun j => Finset.powersetCard (j + 1) Finset.univ) := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · rintro ⟨hne, hc⟩
      have := Finset.card_pos.mpr hne
      exact ⟨U.card - 1, by omega, by omega⟩
    · rintro ⟨j, hj, hc⟩
      exact ⟨Finset.card_pos.mp (by omega), by omega⟩
  rw [e, Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun U h1 h2 => ?_
    rw [Finset.mem_powersetCard] at h1 h2
    omega

theorem part2 (b : ℕ) :
    (∃ H : Finset (Finset (Fin m)), H.card ≤ b ∧ ∀ S, PCDerivable
      (bools m k ∪ Set.image (test m k) (H : Set (Finset (Fin m)))) (k + 1) (test m k S)) ↔
    (∑ j ∈ Finset.range (k + 1), m.choose (j + 1)) ≤ b := by
  classical
  rw [← card_TT]
  constructor
  · rintro ⟨H, hb, hall⟩
    have htop := top_of m k _ fun S => (part1 m k H S.val).mp (hall S.val)
    have h1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (Set.image (prof m k) (H : Set (Finset (Fin m))))) ≤ H.card := by
      rw [← Finset.coe_image]
      exact (finrank_span_finset_le_card _).trans Finset.card_image_le
    rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at h1
    omega
  · intro hb
    refine ⟨(Finset.univ : Finset (TT m k)).image Subtype.val, ?_, fun S => ?_⟩
    · exact Finset.card_image_le.trans (by rw [Finset.card_univ]; exact hb)
    · rw [part1, top_of m k _ fun U => Submodule.subset_span
        (Set.mem_image_of_mem _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ U))))]
      exact Submodule.mem_top

end Main

end PEqualNP.Outside.L_pcx_467

theorem PEqualNP.Outside.L_pcx_467 : ∀ m k : ℕ,
  let I := Fin m
  let J := Fin k
  let K := ZMod 2
  let V := I × Option J
  let P := MvPolynomial V K
  let Mask := Finset I
  let T := {U : Mask // U.Nonempty ∧ U.card ≤ k+1}
  let profile := fun (S : Mask) (U : T) => if U.val ⊆ S then (1 : K) else 0
  let part := fun (S : Mask) (j : Option J) => ∑ i ∈ S, (MvPolynomial.X (i,j) : P)
  let test := fun S : Mask => part S none * ∏ j : J, (1 + part S (some j))
  let bools : Set P := Set.range (fun v : V => MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)
  let axioms := fun (H : Finset Mask) => bools ∪ Set.image test (H : Set Mask)
  (∀ (H : Finset Mask) (S : Mask),
    PEqualNP.ProofComplexity.PCDerivable (axioms H) (k+1) (test S) ↔
      profile S ∈ Submodule.span K (Set.image profile (H : Set Mask))) ∧
  (∀ b : ℕ, (∃ H : Finset Mask, H.card ≤ b ∧
    ∀ S, PEqualNP.ProofComplexity.PCDerivable (axioms H) (k+1) (test S)) ↔
    (∑ j ∈ Finset.range (k+1), m.choose (j+1)) ≤ b) ∧
  ∀ (H : Finset Mask) (low : Mask → P),
    LinearIndependent K (fun S : H => profile S.val) →
    (∀ S ∈ H, (low S).totalDegree ≤ k) →
    ∀ p : P, p.totalDegree ≤ k →
      PEqualNP.ProofComplexity.PCDerivable
        (bools ∪ Set.image (fun S => test S + low S) (H : Set Mask)) (k+1) p →
      ∀ x : V → K, MvPolynomial.eval x p = 0 := by
  intro m k I J K V P Mask T profile part test bools axioms
  exact ⟨fun H S => PEqualNP.Outside.L_pcx_467.part1 m k H S,
    fun b => PEqualNP.Outside.L_pcx_467.part2 m k b,
    fun H low hli hlow p hp hd x => PEqualNP.Outside.L_pcx_467.part3 m k H low hli hlow p hp hd x⟩
