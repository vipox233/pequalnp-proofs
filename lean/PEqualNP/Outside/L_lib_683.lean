import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_683_aux

private def sgn (c : Bool) : ℝ :=
  if c then (-1 : ℝ) else 1

private lemma sgn_sq (c : Bool) : (sgn c) ^ 2 = 1 := by
  cases c <;> norm_num [sgn]

private def posSet {q : ℕ} (v : Fin q → Bool) : Finset (Fin q) :=
  Finset.univ.filter (fun j => v j = false)

private def negSet {q : ℕ} (v : Fin q → Bool) : Finset (Fin q) :=
  Finset.univ.filter (fun j => v j = true)

private def majSet {q : ℕ} (v : Fin q → Bool) : Finset (Fin q) :=
  if (negSet v).card ≤ (posSet v).card then posSet v else negSet v

private lemma disjoint_pos_neg {q : ℕ} (v : Fin q → Bool) :
    Disjoint (posSet v) (negSet v) := by
  unfold posSet negSet
  rw [Finset.disjoint_filter]
  intro j _ h1 h2
  rw [h1] at h2
  cases h2

private lemma union_pos_neg {q : ℕ} (v : Fin q → Bool) :
    posSet v ∪ negSet v = Finset.univ := by
  ext j
  simp only [posSet, negSet, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  cases v j <;> simp

private lemma card_pos_add_neg {q : ℕ} (v : Fin q → Bool) :
    (posSet v).card + (negSet v).card = q := by
  rw [← Finset.card_union_of_disjoint (disjoint_pos_neg v), union_pos_neg,
    Finset.card_univ, Fintype.card_fin]

private lemma sum_posSet {q : ℕ} (v : Fin q → Bool) :
    ∑ j ∈ posSet v, sgn (v j) = ((posSet v).card : ℝ) := by
  have h1 : ∀ j ∈ posSet v, sgn (v j) = (1 : ℝ) := by
    intro j hj
    simp only [posSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [sgn, hj]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one]

private lemma sum_negSet {q : ℕ} (v : Fin q → Bool) :
    ∑ j ∈ negSet v, sgn (v j) = -((negSet v).card : ℝ) := by
  have h1 : ∀ j ∈ negSet v, sgn (v j) = (-1 : ℝ) := by
    intro j hj
    simp only [negSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp [sgn, hj]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  ring

private lemma sum_sgn_eq {q : ℕ} (v : Fin q → Bool) :
    ∑ j : Fin q, sgn (v j) = ((posSet v).card : ℝ) - ((negSet v).card : ℝ) := by
  rw [← union_pos_neg v, Finset.sum_union (disjoint_pos_neg v), sum_posSet, sum_negSet]
  ring

private lemma sum_majSet_sq {q : ℕ} (v : Fin q → Bool) :
    (∑ j ∈ majSet v, sgn (v j)) ^ 2 = ((majSet v).card : ℝ) ^ 2 := by
  unfold majSet
  split_ifs
  · rw [sum_posSet]
  · rw [sum_negSet]; ring

private lemma majSet_card_bounds {q : ℕ} (hq : 2 ≤ q) (v : Fin q → Bool) :
    q ≤ 2 * (majSet v).card ∧ (majSet v).card ≤ q ∧ 1 ≤ (majSet v).card := by
  have hsum := card_pos_add_neg v
  unfold majSet
  split_ifs <;> omega

private lemma sum_sgn_sq_eq {q : ℕ} (v : Fin q → Bool) :
    (∑ j : Fin q, sgn (v j)) ^ 2 = (2 * ((majSet v).card : ℝ) - (q : ℝ)) ^ 2 := by
  rw [sum_sgn_eq]
  have hq : (q : ℝ) = ((posSet v).card : ℝ) + ((negSet v).card : ℝ) := by
    exact_mod_cast (card_pos_add_neg v).symm
  unfold majSet
  split_ifs <;> rw [hq] <;> ring

private noncomputable def alpha (q : ℕ) : ℝ :=
  if q % 2 = 0 then (q : ℝ) / 2
  else (q : ℝ) * ((q : ℝ) + 2) / (2 * ((q : ℝ) + 1))

private noncomputable def beta (q : ℕ) : ℝ :=
  if q % 2 = 0 then 1 / 2
  else (q : ℝ) / (2 * ((q : ℝ) + 1))

private lemma alpha_nonneg (q : ℕ) : 0 ≤ alpha q := by
  unfold alpha
  split_ifs <;> positivity

private lemma beta_nonneg (q : ℕ) : 0 ≤ beta q := by
  unfold beta
  split_ifs <;> positivity

private lemma alpha_add_beta (q : ℕ) :
    alpha q + beta q = (q : ℝ) / 2 + if q % 2 = 0 then 1 / 2 else (q : ℝ) / ((q : ℝ) + 1) := by
  unfold alpha beta
  split_ifs with h
  · rfl
  · have hq1 : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hq1]
    ring

private lemma local_cert_nonneg {q : ℕ} (v : Fin q → Bool) :
    0 ≤ alpha q + beta q * ((∑ j : Fin q, sgn (v j)) ^ 2 / (q : ℝ)) := by
  have ha := alpha_nonneg q
  have hb := beta_nonneg q
  have hd : 0 ≤ (∑ j : Fin q, sgn (v j)) ^ 2 / (q : ℝ) := by positivity
  exact add_nonneg ha (mul_nonneg hb hd)

private lemma local_cert_le_maj {q : ℕ} (hq : 2 ≤ q) (v : Fin q → Bool) :
    alpha q + beta q * ((∑ j : Fin q, sgn (v j)) ^ 2 / (q : ℝ)) ≤ ((majSet v).card : ℝ) := by
  rw [sum_sgn_sq_eq v]
  obtain ⟨h2M, hMq, _⟩ := majSet_card_bounds hq v
  set M : ℕ := (majSet v).card
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hMq_r : (M : ℝ) ≤ (q : ℝ) := by exact_mod_cast hMq
  unfold alpha beta
  split_ifs with heven
  · have h2M_r : (q : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast h2M
    have hdiff :
        (M : ℝ) - ((q : ℝ) / 2 + 1 / 2 * ((2 * (M : ℝ) - (q : ℝ)) ^ 2 / (q : ℝ))) =
          (2 * (M : ℝ) - (q : ℝ)) * (2 * (q : ℝ) - 2 * (M : ℝ)) / (2 * (q : ℝ)) := by
      field_simp [hq_ne]
      ring
    have hnn : 0 ≤ (2 * (M : ℝ) - (q : ℝ)) * (2 * (q : ℝ) - 2 * (M : ℝ)) / (2 * (q : ℝ)) := by
      apply div_nonneg
      · exact mul_nonneg (by linarith) (by linarith)
      · positivity
    linarith
  · have h2M_odd : q + 1 ≤ 2 * M := by omega
    have h2M_r : (q : ℝ) + 1 ≤ 2 * (M : ℝ) := by exact_mod_cast h2M_odd
    have hq1_ne : (q : ℝ) + 1 ≠ 0 := by positivity
    have hdiff :
        (M : ℝ) -
          ((q : ℝ) * ((q : ℝ) + 2) / (2 * ((q : ℝ) + 1)) +
            (q : ℝ) / (2 * ((q : ℝ) + 1)) * ((2 * (M : ℝ) - (q : ℝ)) ^ 2 / (q : ℝ))) =
          (2 * (M : ℝ) - (q : ℝ) - 1) * (2 * (q : ℝ) - 2 * (M : ℝ)) / (2 * ((q : ℝ) + 1)) := by
      field_simp [hq_ne, hq1_ne]
      ring
    have hnn :
        0 ≤ (2 * (M : ℝ) - (q : ℝ) - 1) * (2 * (q : ℝ) - 2 * (M : ℝ)) / (2 * ((q : ℝ) + 1)) := by
      apply div_nonneg
      · exact mul_nonneg (by linarith) (by linarith)
      · positivity
    linarith

private lemma prod_ite_univ {b : ℕ} (T : Finset (Fin b)) (f : Fin b → ℝ) :
    (∏ i : Fin b, if i ∈ T then f i else 1) = ∏ i ∈ T, f i := by
  rw [← Finset.prod_filter]
  congr 1
  ext i
  simp

private lemma prod_le_prod_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hfga : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfgs : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
    exact mul_le_mul hfga (ih hfs hfgs) (Finset.prod_nonneg hfs) (le_trans hfa hfga)

private theorem main_proof :
    ∀ (q b p : ℕ), 2 ≤ q → 2 ≤ p →
  let K := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)
  ∀ (t : ℕ) (signs : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ),
    (∀ h, 0 ≤ w h) →
    (∀ B : Fin b → Finset (Fin q),
      let target := ∏ i : Fin b, ((B i).card : ℝ)
      let est := ∑ h : Fin t, w h * ∏ i : Fin b,
        (∑ j ∈ B i, if signs h i j then (-1 : ℝ) else 1)^2
      ((p : ℝ)-1)*target ≤ (p : ℝ)*est ∧ (p : ℝ)*est ≤ ((p : ℝ)+1)*target) →
    ((p : ℝ)-1)*K^b ≤ ((p : ℝ)+1) * ((Finset.univ.filter (fun h : Fin t => w h ≠ 0)).card : ℝ) := by
  intro q b p hq hp K t signs w hw hB
  let α : ℝ := alpha q
  let β : ℝ := beta q
  let d : Fin t → Fin b → ℝ := fun h i => (∑ j : Fin q, sgn (signs h i j)) ^ 2 / (q : ℝ)
  let coeff : Finset (Fin b) → ℝ := fun T => β ^ T.card * α ^ (Finset.univ \ T).card
  have hα : 0 ≤ α := alpha_nonneg q
  have hβ : 0 ≤ β := beta_nonneg q
  have hK : α + β = K := by
    simpa only [α, β, K] using alpha_add_beta q
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hp_nn : (0 : ℝ) ≤ (p : ℝ) := by positivity
  -- Step 1: Sum of binomial coefficients equals K^b
  have hcoeff_sum : ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset, coeff T = K ^ b := by
    have h1 :
        ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset, coeff T =
          ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset,
            (∏ _i ∈ T, β) * (∏ _i ∈ Finset.univ \ T, α) := by
      refine Finset.sum_congr rfl ?_
      intro T _
      simp [coeff, Finset.prod_const]
    rw [h1, ← Finset.prod_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, add_comm, hK]
  -- Step 2: Expansion of product of local certificates for each h
  have hprod_exp : ∀ h : Fin t,
      ∏ i : Fin b, (α + β * d h i) =
        ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset, coeff T * ∏ i ∈ T, d h i := by
    intro h
    have hcomm : ∏ i : Fin b, (α + β * d h i) = ∏ i ∈ Finset.univ, (β * d h i + α) := by
      refine Finset.prod_congr rfl ?_
      intro i _
      ring
    rw [hcomm, Finset.prod_add]
    refine Finset.sum_congr rfl ?_
    intro T _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const]
    simp only [coeff]
    ring
  -- Step 3: Per-subset lower bound from B_T
  have hT_bound : ∀ T : Finset (Fin b),
      ((p : ℝ) - 1) ≤ (p : ℝ) * ∑ h : Fin t, w h * ∏ i ∈ T, d h i := by
    intro T
    let j0 : Fin q := ⟨0, by omega⟩
    let BT : Fin b → Finset (Fin q) := fun i => if i ∈ T then Finset.univ else {j0}
    have hlo := (hB BT).1
    have htarget : ∏ i : Fin b, ((BT i).card : ℝ) = (q : ℝ) ^ T.card := by
      have hcard : ∀ i : Fin b, ((BT i).card : ℝ) = if i ∈ T then (q : ℝ) else 1 := by
        intro i
        by_cases hi : i ∈ T <;> simp [BT, hi]
      simp_rw [hcard]
      rw [prod_ite_univ, Finset.prod_const]
    have hest :
        (∑ h : Fin t, w h * ∏ i : Fin b, (∑ j ∈ BT i, if signs h i j then (-1 : ℝ) else 1) ^ 2) =
          (q : ℝ) ^ T.card * ∑ h : Fin t, w h * ∏ i ∈ T, d h i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro h _
      have hfactor : ∀ i : Fin b,
          (∑ j ∈ BT i, if signs h i j then (-1 : ℝ) else 1) ^ 2 =
            if i ∈ T then (q : ℝ) * d h i else 1 := by
        intro i
        by_cases hi : i ∈ T
        · simp only [BT, hi, ↓reduceIte, d, sgn]
          rw [mul_div_cancel₀ _ hq_ne]
        · simp only [BT, hi, ↓reduceIte, Finset.sum_singleton]
          exact sgn_sq (signs h i j0)
      simp_rw [hfactor]
      rw [prod_ite_univ, Finset.prod_mul_distrib, Finset.prod_const]
      ring
    rw [htarget, hest] at hlo
    have hqT_pos : (0 : ℝ) < (q : ℝ) ^ T.card := by positivity
    have hlo' :
        (q : ℝ) ^ T.card * ((p : ℝ) - 1) ≤
          (q : ℝ) ^ T.card * ((p : ℝ) * ∑ h : Fin t, w h * ∏ i ∈ T, d h i) := by
      linarith
    exact le_of_mul_le_mul_left hlo' hqT_pos
  -- Step 4: Lower bound on weighted sum of local certificate products
  have hlower :
      ((p : ℝ) - 1) * K ^ b ≤
        (p : ℝ) * ∑ h : Fin t, w h * ∏ i : Fin b, (α + β * d h i) := by
    have hsum_le :
        ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset, coeff T * ((p : ℝ) - 1) ≤
          ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset,
            coeff T * ((p : ℝ) * ∑ h : Fin t, w h * ∏ i ∈ T, d h i) := by
      refine Finset.sum_le_sum ?_
      intro T _
      have hcn : 0 ≤ coeff T := by
        dsimp only [coeff]
        positivity
      exact mul_le_mul_of_nonneg_left (hT_bound T) hcn
    have hlhs :
        ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset, coeff T * ((p : ℝ) - 1) =
          ((p : ℝ) - 1) * K ^ b := by
      rw [← Finset.sum_mul, hcoeff_sum, mul_comm]
    have hrhs :
        ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset,
            coeff T * ((p : ℝ) * ∑ h : Fin t, w h * ∏ i ∈ T, d h i) =
          (p : ℝ) * ∑ h : Fin t, w h * ∏ i : Fin b, (α + β * d h i) := by
      have h1 :
          ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset,
              coeff T * ((p : ℝ) * ∑ h : Fin t, w h * ∏ i ∈ T, d h i) =
            (p : ℝ) * ∑ T ∈ (Finset.univ : Finset (Fin b)).powerset,
              ∑ h : Fin t, w h * (coeff T * ∏ i ∈ T, d h i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro T _
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro h _
        ring
      rw [h1, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl ?_
      intro h _
      rw [← Finset.mul_sum, ← hprod_exp h]
    linarith
  -- Step 5: Per-member upper bound from B_h
  have hmember_le : ∀ h : Fin t,
      (p : ℝ) * (w h * ∏ i : Fin b, (α + β * d h i)) ≤ (p : ℝ) + 1 := by
    intro h
    let Bh : Fin b → Finset (Fin q) := fun i => majSet (signs h i)
    have hhi := (hB Bh).2
    let Pmaj : ℝ := ∏ i : Fin b, ((Bh i).card : ℝ)
    have hPmaj_pos : 0 < Pmaj := by
      apply Finset.prod_pos
      intro i _
      have h1 := (majSet_card_bounds hq (signs h i)).2.2
      exact_mod_cast h1
    have hterm_le_est :
        w h * Pmaj ^ 2 ≤
          ∑ h' : Fin t, w h' * ∏ i : Fin b,
            (∑ j ∈ Bh i, if signs h' i j then (-1 : ℝ) else 1) ^ 2 := by
      have hsingle :
          w h * ∏ i : Fin b, (∑ j ∈ Bh i, if signs h i j then (-1 : ℝ) else 1) ^ 2 ≤
            ∑ h' : Fin t, w h' * ∏ i : Fin b,
              (∑ j ∈ Bh i, if signs h' i j then (-1 : ℝ) else 1) ^ 2 := by
        exact Finset.single_le_sum
          (f := fun h' : Fin t => w h' * ∏ i : Fin b,
            (∑ j ∈ Bh i, if signs h' i j then (-1 : ℝ) else 1) ^ 2)
          (fun h' _ => mul_nonneg (hw h') (Finset.prod_nonneg (fun i _ => sq_nonneg _)))
          (Finset.mem_univ h)
      have heq :
          ∏ i : Fin b, (∑ j ∈ Bh i, if signs h i j then (-1 : ℝ) else 1) ^ 2 = Pmaj ^ 2 := by
        have hsq : ∀ i : Fin b,
            (∑ j ∈ Bh i, if signs h i j then (-1 : ℝ) else 1) ^ 2 = ((Bh i).card : ℝ) ^ 2 := by
          intro i
          exact sum_majSet_sq (signs h i)
        simp_rw [hsq]
        rw [← Finset.prod_pow]
      rwa [heq] at hsingle
    have hchain : (p : ℝ) * (w h * Pmaj ^ 2) ≤ ((p : ℝ) + 1) * Pmaj :=
      le_trans (mul_le_mul_of_nonneg_left hterm_le_est hp_nn) hhi
    have hchain' : Pmaj * ((p : ℝ) * (w h * Pmaj)) ≤ Pmaj * ((p : ℝ) + 1) := by
      nlinarith
    have hmaj_bound : (p : ℝ) * (w h * Pmaj) ≤ (p : ℝ) + 1 :=
      le_of_mul_le_mul_left hchain' hPmaj_pos
    have hprod_le : ∏ i : Fin b, (α + β * d h i) ≤ Pmaj := by
      exact prod_le_prod_nonneg Finset.univ (fun i => α + β * d h i) (fun i => ((Bh i).card : ℝ))
        (fun i _ => local_cert_nonneg (signs h i))
        (fun i _ => local_cert_le_maj hq (signs h i))
    have hwh_prod :
        (p : ℝ) * (w h * ∏ i : Fin b, (α + β * d h i)) ≤ (p : ℝ) * (w h * Pmaj) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod_le (hw h)) hp_nn
    exact le_trans hwh_prod hmaj_bound
  -- Step 6: Restrict sum to nonzero weights and sum the per-member upper bounds
  let Snz : Finset (Fin t) := Finset.univ.filter (fun h : Fin t => w h ≠ 0)
  have hupper :
      (p : ℝ) * ∑ h : Fin t, w h * ∏ i : Fin b, (α + β * d h i) ≤
        ((p : ℝ) + 1) * (Snz.card : ℝ) := by
    have hrestrict :
        ∑ h : Fin t, w h * ∏ i : Fin b, (α + β * d h i) =
          ∑ h ∈ Snz, w h * ∏ i : Fin b, (α + β * d h i) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro h _ hnot
      have hw0 : w h = 0 := by
        simp only [Snz, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnot
        exact hnot
      simp [hw0]
    rw [hrestrict, Finset.mul_sum]
    calc
      ∑ h ∈ Snz, (p : ℝ) * (w h * ∏ i : Fin b, (α + β * d h i))
          ≤ ∑ _h ∈ Snz, ((p : ℝ) + 1) :=
        Finset.sum_le_sum (fun h _ => hmember_le h)
      _ = ((p : ℝ) + 1) * (Snz.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact le_trans hlower hupper

end PEqualNP.Outside.L_lib_683_aux

theorem PEqualNP.Outside.L_lib_683 :
    ∀ (q b p : ℕ), 2 ≤ q → 2 ≤ p →
  let K := (q : ℝ)/2 + if q % 2 = 0 then 1/2 else (q : ℝ)/(q+1)
  ∀ (t : ℕ) (signs : Fin t → Fin b → Fin q → Bool) (w : Fin t → ℝ),
    (∀ h, 0 ≤ w h) →
    (∀ B : Fin b → Finset (Fin q),
      let target := ∏ i : Fin b, ((B i).card : ℝ)
      let est := ∑ h : Fin t, w h * ∏ i : Fin b,
        (∑ j ∈ B i, if signs h i j then (-1 : ℝ) else 1)^2
      ((p : ℝ)-1)*target ≤ (p : ℝ)*est ∧ (p : ℝ)*est ≤ ((p : ℝ)+1)*target) →
    ((p : ℝ)-1)*K^b ≤ ((p : ℝ)+1) * ((Finset.univ.filter (fun h : Fin t => w h ≠ 0)).card : ℝ) :=
  PEqualNP.Outside.L_lib_683_aux.main_proof
