import PEqualNP.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace PEqualNP.Outside.L_lib_477_aux

def satF {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (x : Fin n → Bool) : Prop :=
  ∀ c ∈ F, ∃ lit ∈ c, x lit.1 = lit.2

def critF {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (s : Fin n → Bool) (i : Fin n)
    (c : Finset (Fin n × Bool)) : Prop :=
  c ∈ F ∧ (i, s i) ∈ c ∧ ∀ e ∈ c, e = (i, s i) ∨ (e.1 ≠ i ∧ s e.1 ≠ e.2)

def forced {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (s : Fin n → Bool) (i : Fin n) : Prop :=
  ∃ c ∈ F, (i, s i) ∈ c ∧ ∀ e ∈ c, e = (i, s i) ∨ (π e.1 < π i ∧ s e.1 ≠ e.2)

instance {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (s : Fin n → Bool) (i : Fin n) : Decidable (forced F π s i) := by
  unfold forced
  infer_instance

def forcedSet {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (s : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => forced F π s i)

def cyl {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (s : Fin n → Bool) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun y => ∀ i, ¬ forced F π s i → y i = s i)

theorem cyl_card {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (s : Fin n → Bool) : (cyl F π s).card = 2 ^ (forcedSet F π s).card := by
  let U := forcedSet F π s
  have hbij : (cyl F π s).card = (Finset.univ : Finset (↥U → Bool)).card := by
    refine Finset.card_nbij' (fun y (i : ↥U) => y i.1)
      (fun h i => if hi : i ∈ U then h ⟨i, hi⟩ else s i) ?_ ?_ ?_ ?_
    · intro y _
      exact Finset.mem_univ _
    · intro h _
      simp only [cyl, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      have hni : i ∉ U := by
        simp only [U, forcedSet, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi
      simp [hni]
    · intro y hy
      simp only [cyl, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      funext i
      by_cases hi : i ∈ U
      · simp [hi]
      · simp only [dif_neg hi]
        have hnf : ¬ forced F π s i := by
          simp only [U, forcedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact hi
        exact (hy i hnf).symm
    · intro h _
      funext ⟨i, hi⟩
      simp [hi]
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

theorem not_forced_min {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (s₁ s₂ : Fin n → Bool) (hs₂ : satF F s₂) (i₀ : Fin n) (hne : s₁ i₀ ≠ s₂ i₀)
    (hmin : ∀ j, π j < π i₀ → s₁ j = s₂ j) : ¬ forced F π s₁ i₀ := by
  rintro ⟨c, hcF, _, hrest⟩
  obtain ⟨e, hec, hs2e⟩ := hs₂ c hcF
  rcases hrest e hec with rfl | ⟨hlt, hns1⟩
  · exact hne hs2e.symm
  · have heq := hmin e.1 hlt
    rw [heq] at hns1
    exact hns1 hs2e

theorem cyl_disjoint {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    {s₁ s₂ : Fin n → Bool} (hs₁ : satF F s₁) (hs₂ : satF F s₂) (hne : s₁ ≠ s₂) :
    Disjoint (cyl F π s₁) (cyl F π s₂) := by
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  let D := Finset.univ.filter (fun i : Fin n => s₁ i ≠ s₂ i)
  have hDne : D.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hne
    funext i
    by_contra hi
    have : i ∈ D := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
    rw [h] at this
    exact Finset.notMem_empty i this
  obtain ⟨i₀, hi₀D, hi₀min⟩ := Finset.exists_min_image D π hDne
  have hne0 : s₁ i₀ ≠ s₂ i₀ := (Finset.mem_filter.1 hi₀D).2
  have hmin : ∀ j, π j < π i₀ → s₁ j = s₂ j := by
    intro j hj
    by_contra hnej
    have hjD : j ∈ D := Finset.mem_filter.2 ⟨Finset.mem_univ j, hnej⟩
    exact (not_le_of_gt hj) (hi₀min j hjD)
  have hnf1 : ¬ forced F π s₁ i₀ := not_forced_min F π s₁ s₂ hs₂ i₀ hne0 hmin
  have hnf2 : ¬ forced F π s₂ i₀ :=
    not_forced_min F π s₂ s₁ hs₁ i₀ hne0.symm (fun j hj => (hmin j hj).symm)
  simp only [cyl, Finset.mem_filter, Finset.mem_univ, true_and] at hy₁ hy₂
  exact hne0 ((hy₁ i₀ hnf1).symm.trans (hy₂ i₀ hnf2))

theorem sum_pow_le {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (π : Equiv.Perm (Fin n))
    (S : Finset (Fin n → Bool)) (hS : ∀ s ∈ S, satF F s) :
    S.sum (fun s => (2 : ℝ) ^ (forcedSet F π s).card) ≤ (2 : ℝ) ^ n := by
  have hdisj : (S : Set (Fin n → Bool)).PairwiseDisjoint (cyl F π) := by
    intro s₁ h1 s₂ h2 hne
    exact cyl_disjoint F π (hS s₁ h1) (hS s₂ h2) hne
  have hnat : S.sum (fun s => 2 ^ (forcedSet F π s).card) ≤ 2 ^ n := by
    have h1 : S.sum (fun s => 2 ^ (forcedSet F π s).card) = S.sum (fun s => (cyl F π s).card) :=
      Finset.sum_congr rfl fun s _ => (cyl_card F π s).symm
    rw [h1, ← Finset.card_biUnion hdisj]
    calc (S.biUnion (cyl F π)).card
        ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ n := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hcast : ((S.sum (fun s => 2 ^ (forcedSet F π s).card) : ℕ) : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  push_cast at hcast
  exact hcast

def maxSet {n : ℕ} (A : Finset (Fin n)) (k : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ∀ v ∈ A, π v ≤ π k)

theorem maxSet_card_eq {n : ℕ} (A : Finset (Fin n)) {i k : Fin n} (hi : i ∈ A) (hk : k ∈ A) :
    (maxSet A k).card = (maxSet A i).card := by
  refine Finset.card_nbij' (fun π => π * Equiv.swap k i) (fun π => π * Equiv.swap k i)
    ?_ ?_ ?_ ?_
  · intro π hπ
    simp only [maxSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro v hv
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    have hsv : Equiv.swap k i v ∈ A := by
      by_cases hvk : v = k
      · rw [hvk, Equiv.swap_apply_left]; exact hi
      · by_cases hvi : v = i
        · rw [hvi, Equiv.swap_apply_right]; exact hk
        · rw [Equiv.swap_apply_of_ne_of_ne hvk hvi]; exact hv
    exact hπ (Equiv.swap k i v) hsv
  · intro π hπ
    simp only [maxSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    intro v hv
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    have hsv : Equiv.swap k i v ∈ A := by
      by_cases hvk : v = k
      · rw [hvk, Equiv.swap_apply_left]; exact hi
      · by_cases hvi : v = i
        · rw [hvi, Equiv.swap_apply_right]; exact hk
        · rw [Equiv.swap_apply_of_ne_of_ne hvk hvi]; exact hv
    exact hπ (Equiv.swap k i v) hsv
  · intro π _
    ext x
    simp
  · intro π _
    ext x
    simp

theorem maxSet_mul_card {n : ℕ} (A : Finset (Fin n)) {i : Fin n} (hi : i ∈ A) :
    A.card * (maxSet A i).card = Fintype.card (Equiv.Perm (Fin n)) := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))) = A.biUnion (maxSet A) := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_biUnion, maxSet, Finset.mem_filter, true_and, true_iff]
    obtain ⟨k, hkA, hkmax⟩ := Finset.exists_max_image A π ⟨i, hi⟩
    exact ⟨k, hkA, hkmax⟩
  have hdisj : (A : Set (Fin n)).PairwiseDisjoint (maxSet A) := by
    intro k₁ h1 k₂ h2 hne
    rw [Function.onFun, Finset.disjoint_left]
    intro π hπ1 hπ2
    simp only [maxSet, Finset.mem_filter, Finset.mem_univ, true_and] at hπ1 hπ2
    have hle1 : π k₂ ≤ π k₁ := hπ1 k₂ h2
    have hle2 : π k₁ ≤ π k₂ := hπ2 k₁ h1
    exact hne (π.injective (le_antisymm hle2 hle1))
  rw [← Finset.card_univ, huniv, Finset.card_biUnion hdisj]
  have hsum : ∑ k ∈ A, (maxSet A k).card = ∑ _k ∈ A, (maxSet A i).card :=
    Finset.sum_congr rfl fun k hk => maxSet_card_eq A hi hk
  rw [hsum, Finset.sum_const, smul_eq_mul]

theorem crit_forced_count {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (s : Fin n → Bool)
    (i : Fin n) (c : Finset (Fin n × Bool)) (hc : critF F s i c) :
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (c.card : ℝ)⁻¹ ≤
      ∑ π : Equiv.Perm (Fin n), if forced F π s i then (1 : ℝ) else 0 := by
  obtain ⟨hcF, hic, hrest⟩ := hc
  let A := c.image Prod.fst
  have hiA : i ∈ A := Finset.mem_image.2 ⟨(i, s i), hic, rfl⟩
  have hinj : Set.InjOn Prod.fst (c : Set (Fin n × Bool)) := by
    intro e₁ he₁ e₂ he₂ hf
    rcases hrest e₁ he₁ with rfl | ⟨hne1, hns1⟩ <;>
      rcases hrest e₂ he₂ with rfl | ⟨hne2, hns2⟩
    · rfl
    · exact absurd hf.symm hne2
    · exact absurd hf hne1
    · refine Prod.ext hf ?_
      rw [hf] at hns1
      cases hs : s e₂.1 <;> cases h1 : e₁.2 <;> cases h2 : e₂.2 <;> simp_all
  have hcard : A.card = c.card := Finset.card_image_of_injOn hinj
  have hsub : maxSet A i ⊆ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => forced F π s i) := by
    intro π hπ
    simp only [maxSet, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    refine ⟨c, hcF, hic, fun e he => ?_⟩
    rcases hrest e he with rfl | ⟨hnei, hnse⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨?_, hnse⟩
      have heA : e.1 ∈ A := Finset.mem_image.2 ⟨e, he, rfl⟩
      exact lt_of_le_of_ne (hπ e.1 heA) (fun h => hnei (π.injective h))
  have hcle : (maxSet A i).card ≤
      (Finset.univ.filter (fun π : Equiv.Perm (Fin n) => forced F π s i)).card :=
    Finset.card_le_card hsub
  have hmul := maxSet_mul_card A hiA
  rw [hcard] at hmul
  have hcpos : (0 : ℝ) < (c.card : ℝ) := by
    have : 0 < c.card := Finset.card_pos.mpr ⟨(i, s i), hic⟩
    exact_mod_cast this
  have hsum : (∑ π : Equiv.Perm (Fin n), if forced F π s i then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => forced F π s i)).card : ℝ) := by
    rw [Finset.sum_boole]
  rw [hsum]
  have hmulR : (c.card : ℝ) * ((maxSet A i).card : ℝ) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast hmul
  have hleR : ((maxSet A i).card : ℝ) ≤
      ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => forced F π s i)).card : ℝ) :=
    Nat.cast_le.mpr hcle
  have heq : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (c.card : ℝ)⁻¹ = ((maxSet A i).card : ℝ) := by
    rw [← hmulR]
    field_simp
  rw [heq]
  exact hleR

theorem expected_forced_ge {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (s : Fin n → Bool)
    (I : Finset (Fin n)) (witness : Fin n → Finset (Fin n × Bool))
    (hw : ∀ i ∈ I, critF F s i (witness i)) :
    I.sum (fun dir => ((witness dir).card : ℝ)⁻¹) ≤
      (∑ π : Equiv.Perm (Fin n), ((forcedSet F π s).card : ℝ)) /
        (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  have hNpos : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
    have : 0 < Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_pos
    exact_mod_cast this
  rw [le_div_iff₀ hNpos]
  rw [Finset.sum_mul]
  calc ∑ i ∈ I, ((witness i).card : ℝ)⁻¹ * (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
      = ∑ i ∈ I, (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * ((witness i).card : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ ≤ ∑ i ∈ I, ∑ π : Equiv.Perm (Fin n), if forced F π s i then (1 : ℝ) else 0 :=
          Finset.sum_le_sum fun i hi => crit_forced_count F s i (witness i) (hw i hi)
    _ = ∑ π : Equiv.Perm (Fin n), ∑ i ∈ I, if forced F π s i then (1 : ℝ) else 0 :=
          Finset.sum_comm
    _ ≤ ∑ π : Equiv.Perm (Fin n), ∑ i : Fin n, if forced F π s i then (1 : ℝ) else 0 := by
          refine Finset.sum_le_sum fun π _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ I) (fun i _ _ => by split_ifs <;> norm_num)
    _ = ∑ π : Equiv.Perm (Fin n), ((forcedSet F π s).card : ℝ) := by
          refine Finset.sum_congr rfl fun π _ => ?_
          unfold forcedSet
          rw [Finset.sum_boole]

theorem jensen_rpow2 {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    Real.rpow 2 ((∑ t : ι, x t) / (Fintype.card ι : ℝ)) ≤
      (∑ t : ι, Real.rpow 2 (x t)) / (Fintype.card ι : ℝ) := by
  set N : ℝ := (Fintype.card ι : ℝ)
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  set avg : ℝ := (∑ t : ι, x t) / N
  have hsum_zero : ∑ t : ι, (x t - avg) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmul : N * avg = ∑ t : ι, x t := mul_div_cancel₀ _ (ne_of_gt hNpos)
    linarith
  have h1 : ∀ t : ι, Real.log 2 * (x t - avg) + 1 ≤ Real.exp (Real.log 2 * (x t - avg)) :=
    fun t => Real.add_one_le_exp _
  have h2 : ∑ t : ι, (Real.log 2 * (x t - avg) + 1) ≤
      ∑ t : ι, Real.exp (Real.log 2 * (x t - avg)) :=
    Finset.sum_le_sum fun t _ => h1 t
  have hLHS : ∑ t : ι, (Real.log 2 * (x t - avg) + 1) = N := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsum_zero, mul_zero, zero_add,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hRHS : ∑ t : ι, Real.exp (Real.log 2 * (x t - avg)) =
      (∑ t : ι, Real.exp (Real.log 2 * x t)) * Real.exp (-(Real.log 2 * avg)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hLHS, hRHS] at h2
  have hexp_pos : 0 < Real.exp (Real.log 2 * avg) := Real.exp_pos _
  have h3 : N * Real.exp (Real.log 2 * avg) ≤ ∑ t : ι, Real.exp (Real.log 2 * x t) := by
    have hm := mul_le_mul_of_nonneg_right h2 (le_of_lt hexp_pos)
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at hm
    exact hm
  have h4 : Real.exp (Real.log 2 * avg) ≤ (∑ t : ι, Real.exp (Real.log 2 * x t)) / N := by
    rw [le_div_iff₀ hNpos]
    linarith
  have hr : ∀ y : ℝ, Real.rpow 2 y = Real.exp (Real.log 2 * y) :=
    fun y => Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) y
  simp only [hr]
  exact h4

end PEqualNP.Outside.L_lib_477_aux

theorem PEqualNP.Outside.L_lib_477 : ∀ n : Nat,
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  ∀ F : Finset Clause,
    let critical := fun (s : Point) (i : V) (c : Clause) =>
      c ∈ F ∧ (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨ (e.1 ≠ i ∧ s e.1 ≠ e.2)
    ∀ (S : Finset Point) (I : Point → Finset V) (witness : Point → V → Clause),
      (∀ s ∈ S, sat F s ∧ ∀ i ∈ I s, critical s i (witness s i)) →
      S.sum (fun model => Real.rpow 2 ((I model).sum (fun dir => ((witness model dir).card : ℝ)⁻¹))) ≤
        (2 : ℝ)^n := by
  intro n V Point Clause sat F critical S I witness hS
  set N : ℝ := (Fintype.card (Equiv.Perm (Fin n)) : ℝ)
  have hNpos : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hmodel : ∀ model ∈ S,
      Real.rpow 2 ((I model).sum (fun dir => ((witness model dir).card : ℝ)⁻¹)) ≤
        (∑ π : Equiv.Perm (Fin n),
          (2 : ℝ) ^ (PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card) / N := by
    intro model hm
    have h1 := PEqualNP.Outside.L_lib_477_aux.expected_forced_ge F model (I model)
      (witness model) (hS model hm).2
    have h2 : Real.rpow 2 ((I model).sum (fun dir => ((witness model dir).card : ℝ)⁻¹)) ≤
        Real.rpow 2 ((∑ π : Equiv.Perm (Fin n),
          ((PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card : ℝ)) / N) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h1
    have h3 := PEqualNP.Outside.L_lib_477_aux.jensen_rpow2
      (fun π : Equiv.Perm (Fin n) =>
        ((PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card : ℝ))
    have h4 : ∀ π : Equiv.Perm (Fin n),
        Real.rpow 2 ((PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card : ℝ) =
          (2 : ℝ) ^ (PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card :=
      fun π => Real.rpow_natCast 2 _
    simp only [h4] at h3
    exact le_trans h2 h3
  calc S.sum (fun model =>
        Real.rpow 2 ((I model).sum (fun dir => ((witness model dir).card : ℝ)⁻¹)))
      ≤ S.sum (fun model => (∑ π : Equiv.Perm (Fin n),
          (2 : ℝ) ^ (PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card) / N) :=
        Finset.sum_le_sum hmodel
    _ = (∑ π : Equiv.Perm (Fin n), S.sum (fun model =>
          (2 : ℝ) ^ (PEqualNP.Outside.L_lib_477_aux.forcedSet F π model).card)) / N := by
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        rw [Finset.sum_comm]
    _ ≤ (∑ _π : Equiv.Perm (Fin n), (2 : ℝ) ^ n) / N := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hNpos)
        exact Finset.sum_le_sum fun π _ =>
          PEqualNP.Outside.L_lib_477_aux.sum_pow_le F π S (fun s hs => (hS s hs).1)
    _ = (2 : ℝ) ^ n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_div_cancel_left₀ _ (ne_of_gt hNpos)
