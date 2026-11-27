import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_509_aux

private abbrev satFn {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (x : Fin n → Bool) : Prop :=
  ∀ c ∈ F, ∃ lit ∈ c, x lit.1 = lit.2

private def forcedFn {n : ℕ} (F : Finset (Finset (Fin n × Bool))) (s : Fin n → Bool)
    (order : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i =>
    ∃ c ∈ F, (i, s i) ∈ c ∧ ∀ e ∈ c, e = (i, s i) ∨
      ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))

private def flipPt {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

private lemma flipPt_apply_eq {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipPt x i i = !x i := by
  simp [flipPt]

private lemma flipPt_apply_ne {n : ℕ} (x : Fin n → Bool) (i j : Fin n) (h : j ≠ i) :
    flipPt x i j = x j := by
  simp [flipPt, h]

private lemma flipPt_invol {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    flipPt (flipPt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h
    simp [flipPt]
  · simp [flipPt, h]

private lemma subcube_disjoint {n : ℕ} (F : Finset (Finset (Fin n × Bool)))
    (order : Equiv.Perm (Fin n)) (g s1 s2 : Fin n → Bool)
    (hs1 : satFn F s1) (hs2 : satFn F s2)
    (hg1 : ∀ i : Fin n, i ∈ forcedFn F s1 order ∨ g i = s1 i)
    (hg2 : ∀ i : Fin n, i ∈ forcedFn F s2 order ∨ g i = s2 i) :
    s1 = s2 := by
  classical
  by_contra hne
  have hD : (Finset.univ.filter (fun i : Fin n => s1 i ≠ s2 i)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hne
    funext i
    by_contra hi
    have hmem : i ∈ Finset.univ.filter (fun i : Fin n => s1 i ≠ s2 i) := by
      simp [hi]
    rw [hemp] at hmem
    exact Finset.notMem_empty i hmem
  rcases Finset.exists_min_image _ (fun j : Fin n => (order j).val) hD with ⟨i, hiD, hmin⟩
  have hi_ne : s1 i ≠ s2 i := (Finset.mem_filter.mp hiD).2
  have hlt_eq : ∀ j : Fin n, (order j).val < (order i).val → s1 j = s2 j := by
    intro j hj
    by_contra hjne
    have hjD : j ∈ Finset.univ.filter (fun k : Fin n => s1 k ≠ s2 k) := by simp [hjne]
    have := hmin j hjD
    omega
  have hnf1 : i ∉ forcedFn F s1 order := by
    intro hmem
    simp only [forcedFn, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨c, hcF, _, hc_rest⟩
    rcases hs2 c hcF with ⟨e, hec, hse2⟩
    rcases hc_rest e hec with heq | ⟨hlt, hneq⟩
    · rw [heq] at hse2
      exact hi_ne hse2.symm
    · have := hlt_eq e.1 hlt
      rw [this] at hneq
      exact hneq hse2
  have hnf2 : i ∉ forcedFn F s2 order := by
    intro hmem
    simp only [forcedFn, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rcases hmem with ⟨c, hcF, _, hc_rest⟩
    rcases hs1 c hcF with ⟨e, hec, hse1⟩
    rcases hc_rest e hec with heq | ⟨hlt, hneq⟩
    · rw [heq] at hse1
      exact hi_ne hse1
    · have := hlt_eq e.1 hlt
      rw [← this] at hneq
      exact hneq hse1
  have hgi1 : g i = s1 i := (hg1 i).resolve_left hnf1
  have hgi2 : g i = s2 i := (hg2 i).resolve_left hnf2
  exact hi_ne (hgi1.symm.trans hgi2)

private lemma subcube_card {n : ℕ} (S : Finset (Fin n)) (s : Fin n → Bool) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun g => ∀ i : Fin n, i ∈ S ∨ g i = s i)).card =
      2 ^ S.card := by
  classical
  have hbij :
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun g => ∀ i : Fin n, i ∈ S ∨ g i = s i)).card =
        (Finset.univ : Finset ({i : Fin n // i ∈ S} → Bool)).card := by
    refine Finset.card_bij (fun g _ => fun i : {i : Fin n // i ∈ S} => g i.1) ?_ ?_ ?_
    · intro g _
      exact Finset.mem_univ _
    · intro g1 hg1 g2 hg2 heq
      have h1 := (Finset.mem_filter.mp hg1).2
      have h2 := (Finset.mem_filter.mp hg2).2
      funext i
      by_cases hi : i ∈ S
      · exact congrFun heq ⟨i, hi⟩
      · exact ((h1 i).resolve_left hi).trans ((h2 i).resolve_left hi).symm
    · intro f _
      refine ⟨fun i => if hi : i ∈ S then f ⟨i, hi⟩ else s i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i
        by_cases hi : i ∈ S
        · exact Or.inl hi
        · right
          simp [hi]
      · funext ⟨i, hi⟩
        simp [hi]
  rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

private lemma pairs_card_eq {n : ℕ} (F : Finset (Finset (Fin n × Bool))) :
    let models := (Finset.univ : Finset (Fin n → Bool)).filter (satFn F)
    let pairs := (Finset.univ : Finset (Equiv.Perm (Fin n) × (Fin n → Bool))).filter (fun og =>
      ∃ s ∈ models, ∀ i : Fin n, i ∈ forcedFn F s og.1 ∨ og.2 i = s i)
    pairs.card = ∑ order : Equiv.Perm (Fin n), ∑ s ∈ models, 2 ^ (forcedFn F s order).card := by
  classical
  intro models pairs
  have h1 : pairs.card =
      ∑ order : Equiv.Perm (Fin n), ∑ g : Fin n → Bool,
        if ∃ s ∈ models, ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i then 1 else 0 := by
    rw [Finset.card_filter]
    rw [Fintype.sum_prod_type]
  rw [h1]
  refine Finset.sum_congr rfl ?_
  intro order _
  have h2 : ∀ g : Fin n → Bool,
      (if ∃ s ∈ models, ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i then (1 : ℕ) else 0) =
        ∑ s ∈ models, if ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i then 1 else 0 := by
    intro g
    by_cases hex : ∃ s ∈ models, ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i
    · simp only [hex, ↓reduceIte]
      rcases hex with ⟨s0, hs0m, hgs0⟩
      rw [Finset.sum_eq_single s0]
      · simp [hgs0]
      · intro s hsm hsne
        by_cases hgs : ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i
        · exfalso
          apply hsne
          exact subcube_disjoint F order g s s0
            (Finset.mem_filter.mp hsm).2 (Finset.mem_filter.mp hs0m).2 hgs hgs0
        · simp [hgs]
      · intro hnot
        exact False.elim (hnot hs0m)
    · simp only [hex, ↓reduceIte]
      symm
      refine Finset.sum_eq_zero ?_
      intro s hsm
      have hneg : ¬ ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i :=
        fun h => hex ⟨s, hsm, h⟩
      simp [hneg]
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro s _
  rw [← Finset.card_filter, subcube_card]

private lemma perm_max_count {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    S.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let A : Fin n → Finset (Equiv.Perm (Fin n)) := fun m =>
    (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun π => ∀ j ∈ S, j ≠ m → (π j).val < (π m).val)
  have heq_card : ∀ m ∈ S, (A m).card = (A i).card := by
    intro m hm
    refine Finset.card_bij (fun π _ => π * Equiv.swap i m) ?_ ?_ ?_
    · intro π hπ
      have hmax := (Finset.mem_filter.mp hπ).2
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j hj hji
      have hswap_mem : Equiv.swap i m j ∈ S := by
        by_cases hjm : j = m
        · subst hjm
          simp [Equiv.swap_apply_right, hi]
        · rw [Equiv.swap_apply_of_ne_of_ne hji hjm]
          exact hj
      have hswap_ne : Equiv.swap i m j ≠ m := by
        intro hEq
        have := congrArg (Equiv.swap i m) hEq
        simp only [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
        exact hji this
      have := hmax (Equiv.swap i m j) hswap_mem hswap_ne
      simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using this
    · intro π1 _ π2 _ h
      exact mul_right_cancel h
    · intro σ hσ
      have hmax := (Finset.mem_filter.mp hσ).2
      refine ⟨σ * Equiv.swap i m, ?_, ?_⟩
      · simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j hj hjm
        have hswap_mem : Equiv.swap i m j ∈ S := by
          by_cases hji : j = i
          · subst hji
            simp [Equiv.swap_apply_left, hm]
          · rw [Equiv.swap_apply_of_ne_of_ne hji hjm]
            exact hj
        have hswap_ne : Equiv.swap i m j ≠ i := by
          intro hEq
          have := congrArg (Equiv.swap i m) hEq
          simp only [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
          exact hjm this
        have := hmax (Equiv.swap i m j) hswap_mem hswap_ne
        simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_right] using this
      · rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  have hsum_eq : ∑ m ∈ S, (A m).card = S.card * (A i).card := by
    calc
      ∑ m ∈ S, (A m).card = ∑ _m ∈ S, (A i).card := Finset.sum_congr rfl heq_card
      _ = S.card * (A i).card := by simp
  rw [← hsum_eq]
  have hpart : ∑ m ∈ S, (A m).card = ∑ π : Equiv.Perm (Fin n), (1 : ℕ) := by
    simp_rw [A, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro π _
    have hS : S.Nonempty := ⟨i, hi⟩
    rcases Finset.exists_max_image S (fun j => (π j).val) hS with ⟨m0, hm0S, hmax0⟩
    rw [Finset.sum_eq_single m0]
    · have hm0 : ∀ j ∈ S, j ≠ m0 → (π j).val < (π m0).val := by
        intro j hj hne
        have hle := hmax0 j hj
        have hne_val : (π j).val ≠ (π m0).val := fun hval => hne (π.injective (Fin.ext hval))
        omega
      rw [if_pos hm0]
    · intro m hm hne
      have hnot : ¬ ∀ j ∈ S, j ≠ m → (π j).val < (π m).val := by
        intro hgood
        have hlt := hgood m0 hm0S hne.symm
        have hle := hmax0 m hm
        omega
      rw [if_neg hnot]
    · intro hnot
      exact False.elim (hnot hm0S)
  rw [hpart]
  simp

private lemma expected_forced_ge_iso {n k : ℕ} (F : Finset (Finset (Fin n × Bool)))
    (hk : ∀ c ∈ F, c.card ≤ k) (s : Fin n → Bool) (hs : satFn F s) :
    let models := (Finset.univ : Finset (Fin n → Bool)).filter (satFn F)
    let iso := (Finset.univ : Finset (Fin n)).filter (fun i => flipPt s i ∉ models)
    Fintype.card (Equiv.Perm (Fin n)) * iso.card ≤
      k * ∑ π : Equiv.Perm (Fin n), (forcedFn F s π).card := by
  classical
  intro models iso
  have hswap :
      (∑ π : Equiv.Perm (Fin n), (forcedFn F s π).card) =
        ∑ i : Fin n, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => i ∈ forcedFn F s π)).card := by
    have hcard_eq : ∀ π : Equiv.Perm (Fin n),
        (forcedFn F s π).card = ∑ i : Fin n, if i ∈ forcedFn F s π then 1 else 0 := by
      intro π
      rw [← Finset.card_filter]
      congr 1
      ext i
      simp
    simp_rw [hcard_eq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.card_filter]
  rw [hswap]
  have hsub :
      (∑ i ∈ iso, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => i ∈ forcedFn F s π)).card) ≤
        ∑ i : Fin n, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => i ∈ forcedFn F s π)).card :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hmul_sub := Nat.mul_le_mul_left k hsub
  refine le_trans ?_ hmul_sub
  rw [Finset.mul_sum]
  have hconst : Fintype.card (Equiv.Perm (Fin n)) * iso.card =
      ∑ _i ∈ iso, Fintype.card (Equiv.Perm (Fin n)) := by
    simp [mul_comm]
  rw [hconst]
  refine Finset.sum_le_sum ?_
  intro i hi
  have hnot_sat : ¬ satFn F (flipPt s i) := by
    have hnm := (Finset.mem_filter.mp hi).2
    intro hsat
    exact hnm (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsat⟩)
  unfold satFn at hnot_sat
  push_neg at hnot_sat
  rcases hnot_sat with ⟨c, hcF, hc_false⟩
  rcases hs c hcF with ⟨lit, hlitc, hlit_sat⟩
  have hlit_i : lit.1 = i := by
    by_contra hne
    have hfl := hc_false lit hlitc
    rw [flipPt_apply_ne s i lit.1 hne] at hfl
    exact hfl hlit_sat
  have hlit_eq : lit = (i, s i) := by
    rcases lit with ⟨v, b⟩
    dsimp at hlit_i hlit_sat
    subst hlit_i
    rw [hlit_sat]
  have his_mem : (i, s i) ∈ c := hlit_eq ▸ hlitc
  let S : Finset (Fin n) := c.image Prod.fst
  have hiS : i ∈ S := Finset.mem_image.mpr ⟨(i, s i), his_mem, rfl⟩
  have hScard : S.card ≤ k := le_trans Finset.card_image_le (hk c hcF)
  have hsub_perm :
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card ≤
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun π => i ∈ forcedFn F s π)).card := by
    refine Finset.card_le_card ?_
    intro π hπ
    have hmax := (Finset.mem_filter.mp hπ).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, forcedFn]
    refine ⟨c, hcF, his_mem, ?_⟩
    intro e hec
    by_cases he1 : e.1 = i
    · left
      rcases e with ⟨v, b⟩
      dsimp at he1
      subst v
      have hfl := hc_false (i, b) hec
      rw [flipPt_apply_eq] at hfl
      have hb : b = s i := by
        cases hsi : s i <;> cases b <;> simp_all
      rw [hb]
    · right
      refine ⟨hmax e.1 (Finset.mem_image.mpr ⟨e, hec, rfl⟩) he1, ?_⟩
      have hfl := hc_false e hec
      rw [flipPt_apply_ne s i e.1 he1] at hfl
      exact hfl
  calc
    Fintype.card (Equiv.Perm (Fin n))
        = S.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card :=
          (perm_max_count S i hiS).symm
    _ ≤ k * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card :=
          Nat.mul_le_mul_right _ hScard
    _ ≤ k * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
            (fun π => i ∈ forcedFn F s π)).card :=
          Nat.mul_le_mul_left k hsub_perm

private lemma log_entropy_helper {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a * Real.log a + b * Real.log b + 2 * a * Real.log 2 ≤ (a + b) * Real.log (a + b) := by
  by_cases ha0 : a = 0
  · subst ha0
    simp
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have hbp : 0 < b := lt_of_lt_of_le hap hab
    have habp : 0 < a + b := add_pos hap hbp
    let g : ℝ → ℝ := fun t => Real.log (1 + t) + t * Real.log (1 + 1 / t)
    have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (Real.log (1 + 1 / t)) t := by
      intro t ht
      have htpos : (0 : ℝ) < t := ht
      have ht0 : t ≠ 0 := ne_of_gt htpos
      have h1t : 1 + t ≠ 0 := ne_of_gt (by linarith)
      have h1inv : 1 + 1 / t ≠ 0 := ne_of_gt (by positivity)
      have hd1 := ((hasDerivAt_id t).const_add 1).log h1t
      have hd_inv : HasDerivAt (fun x : ℝ => 1 + 1 / x) (-(1 / t ^ 2)) t := by
        have h := (hasDerivAt_inv ht0).const_add 1
        convert h using 1
        · funext x
          simp [one_div]
        · ring
      have hd_log2 := hd_inv.log h1inv
      have hd2 := (hasDerivAt_id t).mul hd_log2
      have hsum := hd1.add hd2
      convert hsum using 1
      · funext x
        simp [g, one_div]
      · dsimp [id]
        field_simp [ht0, h1t, h1inv]
        ring
    have hmono : MonotoneOn g (Set.Ici (1 : ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      · intro t ht
        have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one (Set.mem_Ici.mp ht)
        exact (hderiv t ht0).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
        exact (hderiv t ht0).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one (Set.mem_Ioi.mp ht)
        rw [(hderiv t ht0).deriv]
        have h1t : (0 : ℝ) < 1 / t := by positivity
        exact Real.log_nonneg (by linarith)
    have hx1 : (1 : ℝ) ≤ b / a := (one_le_div hap).mpr hab
    have hgx : g 1 ≤ g (b / a) := hmono (Set.mem_Ici.mpr le_rfl) hx1 hx1
    have hg1 : g 1 = 2 * Real.log 2 := by
      simp only [g]
      norm_num
      ring
    have hgba : a * g (b / a) = (a + b) * Real.log (a + b) - a * Real.log a - b * Real.log b := by
      simp only [g]
      have h1 : 1 + b / a = (a + b) / a := by field_simp [ne_of_gt hap]
      have h2 : 1 + 1 / (b / a) = (a + b) / b := by field_simp [ne_of_gt hap, ne_of_gt hbp]; ring
      rw [h1, h2, Real.log_div (ne_of_gt habp) (ne_of_gt hap),
        Real.log_div (ne_of_gt habp) (ne_of_gt hbp)]
      field_simp [ne_of_gt hap]
      ring
    have hmul : a * g 1 ≤ a * g (b / a) := mul_le_mul_of_nonneg_left hgx ha
    rw [hg1, hgba] at hmul
    linarith

private def edgeCount {n : ℕ} (M : Finset (Fin n → Bool)) : ℕ :=
  ∑ s ∈ M, ((Finset.univ : Finset (Fin n)).filter (fun i => flipPt s i ∈ M)).card

private lemma cube_edge_ineq : ∀ (n : ℕ) (M : Finset (Fin n → Bool)),
    (edgeCount M : ℝ) * Real.log 2 ≤ (M.card : ℝ) * Real.log (M.card : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro M
    have he : edgeCount M = 0 := by
      unfold edgeCount
      refine Finset.sum_eq_zero ?_
      intro s _
      simp
    rw [he, Nat.cast_zero, zero_mul]
    by_cases hM : M.card = 0
    · rw [hM, Nat.cast_zero, zero_mul]
    · have h1 : (1 : ℝ) ≤ (M.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM
      exact mul_nonneg (by positivity) (Real.log_nonneg h1)
  | succ n ih =>
    intro M
    classical
    let S0 : Finset (Fin (n + 1) → Bool) := M.filter (fun s => s 0 = false)
    let S1 : Finset (Fin (n + 1) → Bool) := M.filter (fun s => s 0 = true)
    let M0 : Finset (Fin n → Bool) := S0.image Fin.tail
    let M1 : Finset (Fin n → Bool) := S1.image Fin.tail
    have hcard_split : M.card = S0.card + S1.card := by
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]
        intro s hs0 hs1
        have h0 := (Finset.mem_filter.mp hs0).2
        have h1 := (Finset.mem_filter.mp hs1).2
        rw [h0] at h1
        exact Bool.false_ne_true h1
      have hunion : S0 ∪ S1 = M := by
        ext s
        simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          cases hs0 : s 0
          · exact Or.inl ⟨h, rfl⟩
          · exact Or.inr ⟨h, rfl⟩
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    have hM0_card : M0.card = S0.card := by
      refine Finset.card_image_of_injOn ?_
      intro a ha b hb htail
      funext i
      refine Fin.cases ?_ ?_ i
      · exact ((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2).symm
      · intro j
        exact congrFun htail j
    have hM1_card : M1.card = S1.card := by
      refine Finset.card_image_of_injOn ?_
      intro a ha b hb htail
      funext i
      refine Fin.cases ?_ ?_ i
      · exact ((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2).symm
      · intro j
        exact congrFun htail j
    have hM_card : M.card = M0.card + M1.card := by
      rw [hcard_split, hM0_card, hM1_card]
    have htail_flip : ∀ (s : Fin (n + 1) → Bool) (j : Fin n),
        Fin.tail (flipPt s j.succ) = flipPt (Fin.tail s) j := by
      intro s j
      funext k
      simp only [Fin.tail, flipPt]
      by_cases hkj : k = j
      · subst hkj
        simp
      · have hne : k.succ ≠ j.succ := fun h => hkj (Fin.succ_injective _ h)
        simp [hkj, hne, Fin.tail]
    have hflip_succ_mem0 : ∀ s ∈ S0, ∀ j : Fin n,
        flipPt s j.succ ∈ M ↔ flipPt (Fin.tail s) j ∈ M0 := by
      intro s hs j
      have hs0 : s 0 = false := (Finset.mem_filter.mp hs).2
      have hfl0 : flipPt s j.succ 0 = false := by
        rw [flipPt_apply_ne s j.succ 0 (Fin.succ_ne_zero j).symm, hs0]
      constructor
      · intro hmem
        refine Finset.mem_image.mpr ⟨flipPt s j.succ, ?_, htail_flip s j⟩
        exact Finset.mem_filter.mpr ⟨hmem, hfl0⟩
      · intro hmem
        rcases Finset.mem_image.mp hmem with ⟨t, htS0, hteq⟩
        have htM := (Finset.mem_filter.mp htS0).1
        have ht0 := (Finset.mem_filter.mp htS0).2
        have hEq : t = flipPt s j.succ := by
          funext i
          refine Fin.cases ?_ ?_ i
          · exact ht0.trans hfl0.symm
          · intro k
            have := congrFun hteq k
            have := this.trans (congrFun (htail_flip s j).symm k)
            exact this
        exact hEq ▸ htM
    have hflip_succ_mem1 : ∀ s ∈ S1, ∀ j : Fin n,
        flipPt s j.succ ∈ M ↔ flipPt (Fin.tail s) j ∈ M1 := by
      intro s hs j
      have hs1 : s 0 = true := (Finset.mem_filter.mp hs).2
      have hfl1 : flipPt s j.succ 0 = true := by
        rw [flipPt_apply_ne s j.succ 0 (Fin.succ_ne_zero j).symm, hs1]
      constructor
      · intro hmem
        refine Finset.mem_image.mpr ⟨flipPt s j.succ, ?_, htail_flip s j⟩
        exact Finset.mem_filter.mpr ⟨hmem, hfl1⟩
      · intro hmem
        rcases Finset.mem_image.mp hmem with ⟨t, htS1, hteq⟩
        have htM := (Finset.mem_filter.mp htS1).1
        have ht1 := (Finset.mem_filter.mp htS1).2
        have hEq : t = flipPt s j.succ := by
          funext i
          refine Fin.cases ?_ ?_ i
          · exact ht1.trans hfl1.symm
          · intro k
            have := congrFun hteq k
            have := this.trans (congrFun (htail_flip s j).symm k)
            exact this
        exact hEq ▸ htM
    have hdeg_split : ∀ s : Fin (n + 1) → Bool,
        ((Finset.univ : Finset (Fin (n + 1))).filter (fun i => flipPt s i ∈ M)).card =
          (if flipPt s 0 ∈ M then 1 else 0) +
            ((Finset.univ : Finset (Fin n)).filter (fun j => flipPt s j.succ ∈ M)).card := by
      intro s
      rw [Finset.card_filter, Fin.sum_univ_succ, ← Finset.card_filter]
    have hedge_split :
        edgeCount M =
          (∑ s ∈ S0, (if flipPt s 0 ∈ M then 1 else 0)) +
          (∑ s ∈ S1, (if flipPt s 0 ∈ M then 1 else 0)) +
          edgeCount M0 + edgeCount M1 := by
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]
        intro s hs0 hs1
        have h0 := (Finset.mem_filter.mp hs0).2
        have h1 := (Finset.mem_filter.mp hs1).2
        rw [h0] at h1
        exact Bool.false_ne_true h1
      have hunion : S0 ∪ S1 = M := by
        ext s
        simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h
          cases hs0 : s 0
          · exact Or.inl ⟨h, rfl⟩
          · exact Or.inr ⟨h, rfl⟩
      have hsplit_sum :
          edgeCount M =
            (∑ s ∈ S0, ((Finset.univ : Finset (Fin (n + 1))).filter (fun i => flipPt s i ∈ M)).card) +
            (∑ s ∈ S1, ((Finset.univ : Finset (Fin (n + 1))).filter (fun i => flipPt s i ∈ M)).card) := by
        unfold edgeCount
        rw [← Finset.sum_union hdisj, hunion]
      rw [hsplit_sum]
      unfold edgeCount
      simp_rw [hdeg_split]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hM0_sum :
          (∑ s ∈ S0, ((Finset.univ : Finset (Fin n)).filter (fun j => flipPt s j.succ ∈ M)).card) =
            ∑ t ∈ M0, ((Finset.univ : Finset (Fin n)).filter (fun j => flipPt t j ∈ M0)).card := by
        symm
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl ?_
          intro s hs
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hflip_succ_mem0 s hs j).symm
        · intro a ha b hb htail
          funext i
          refine Fin.cases ?_ ?_ i
          · exact ((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2).symm
          · intro j
            exact congrFun htail j
      have hM1_sum :
          (∑ s ∈ S1, ((Finset.univ : Finset (Fin n)).filter (fun j => flipPt s j.succ ∈ M)).card) =
            ∑ t ∈ M1, ((Finset.univ : Finset (Fin n)).filter (fun j => flipPt t j ∈ M1)).card := by
        symm
        rw [Finset.sum_image]
        · refine Finset.sum_congr rfl ?_
          intro s hs
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact (hflip_succ_mem1 s hs j).symm
        · intro a ha b hb htail
          funext i
          refine Fin.cases ?_ ?_ i
          · exact ((Finset.mem_filter.mp ha).2).trans ((Finset.mem_filter.mp hb).2).symm
          · intro j
            exact congrFun htail j
      rw [hM0_sum, hM1_sum]
      omega
    have hcross0_le0 : (∑ s ∈ S0, (if flipPt s 0 ∈ M then 1 else 0)) ≤ M0.card := by
      rw [← Finset.card_filter, hM0_card]
      exact Finset.card_filter_le _ _
    have hcross0_le1 : (∑ s ∈ S0, (if flipPt s 0 ∈ M then 1 else 0)) ≤ M1.card := by
      rw [← Finset.card_filter, hM1_card]
      have hinj : (S0.filter (fun s => flipPt s 0 ∈ M)).card ≤ S1.card := by
        refine Finset.card_le_card_of_injOn (fun s => flipPt s 0) ?_ ?_
        · intro s hs
          have hs0 := (Finset.mem_filter.mp hs).1
          have hfl := (Finset.mem_filter.mp hs).2
          have hs0val := (Finset.mem_filter.mp hs0).2
          refine Finset.mem_filter.mpr ⟨hfl, ?_⟩
          dsimp only
          rw [flipPt_apply_eq, hs0val]
          rfl
        · intro a _ b _ h
          have := congrArg (fun x => flipPt x 0) h
          simpa [flipPt_invol] using this
      exact hinj
    have hcross1_le1 : (∑ s ∈ S1, (if flipPt s 0 ∈ M then 1 else 0)) ≤ M1.card := by
      rw [← Finset.card_filter, hM1_card]
      exact Finset.card_filter_le _ _
    have hcross1_le0 : (∑ s ∈ S1, (if flipPt s 0 ∈ M then 1 else 0)) ≤ M0.card := by
      rw [← Finset.card_filter, hM0_card]
      have hinj : (S1.filter (fun s => flipPt s 0 ∈ M)).card ≤ S0.card := by
        refine Finset.card_le_card_of_injOn (fun s => flipPt s 0) ?_ ?_
        · intro s hs
          have hs1 := (Finset.mem_filter.mp hs).1
          have hfl := (Finset.mem_filter.mp hs).2
          have hs1val := (Finset.mem_filter.mp hs1).2
          refine Finset.mem_filter.mpr ⟨hfl, ?_⟩
          dsimp only
          rw [flipPt_apply_eq, hs1val]
          rfl
        · intro a _ b _ h
          have := congrArg (fun x => flipPt x 0) h
          simpa [flipPt_invol] using this
      exact hinj
    have hih0 := ih M0
    have hih1 := ih M1
    have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rcases le_total M0.card M1.card with hle | hle
    · have hedge_le : edgeCount M ≤ 2 * M0.card + edgeCount M0 + edgeCount M1 := by
        omega
      have hedge_real : (edgeCount M : ℝ) ≤ 2 * (M0.card : ℝ) + (edgeCount M0 : ℝ) + (edgeCount M1 : ℝ) := by
        exact_mod_cast hedge_le
      have hstep := log_entropy_helper (a := (M0.card : ℝ)) (b := (M1.card : ℝ))
        (Nat.cast_nonneg _) (by exact_mod_cast hle)
      have hM_cast : (M.card : ℝ) = (M0.card : ℝ) + (M1.card : ℝ) := by
        exact_mod_cast hM_card
      rw [hM_cast]
      nlinarith
    · have hedge_le : edgeCount M ≤ 2 * M1.card + edgeCount M0 + edgeCount M1 := by
        omega
      have hedge_real : (edgeCount M : ℝ) ≤ 2 * (M1.card : ℝ) + (edgeCount M0 : ℝ) + (edgeCount M1 : ℝ) := by
        exact_mod_cast hedge_le
      have hstep := log_entropy_helper (a := (M1.card : ℝ)) (b := (M0.card : ℝ))
        (Nat.cast_nonneg _) (by exact_mod_cast hle)
      have hM_cast : (M.card : ℝ) = (M1.card : ℝ) + (M0.card : ℝ) := by
        have : M.card = M1.card + M0.card := by omega
        exact_mod_cast this
      rw [hM_cast]
      nlinarith

private lemma sum_iso_add_edge {n : ℕ} (M : Finset (Fin n → Bool)) :
    (∑ s ∈ M, ((Finset.univ : Finset (Fin n)).filter (fun i => flipPt s i ∉ M)).card) +
      edgeCount M = M.card * n := by
  classical
  unfold edgeCount
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ s ∈ M,
      ((Finset.univ : Finset (Fin n)).filter (fun i => flipPt s i ∉ M)).card +
        ((Finset.univ : Finset (Fin n)).filter (fun i => flipPt s i ∈ M)).card = n := by
    intro s _
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i => flipPt s i ∈ M)
    rw [Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [Finset.sum_congr rfl hterm]
  simp

end PEqualNP.Outside.L_lib_509_aux

theorem PEqualNP.Outside.L_lib_509 : (∀ (n k : Nat), 0 < k →
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  let Order := Equiv.Perm V
  ∀ F : Finset Clause,
    let forced := fun (s : Point) (order : Order) =>
      (Finset.univ : Finset V).filter (fun i =>
        ∃ c ∈ F, (i,s i) ∈ c ∧ ∀ e ∈ c, e = (i,s i) ∨
          ((order e.1).val < (order i).val ∧ s e.1 ≠ e.2))
    (∀ c ∈ F, c.card ≤ k) →
    let models := (Finset.univ : Finset Point).filter (sat F)
    let pairs := (Finset.univ : Finset (Order × Point)).filter (fun og =>
      ∃ s ∈ models, ∀ i : V, i ∈ forced s og.1 ∨ og.2 i = s i)
    0 < models.card →
      pairs.card^k * 2^((k-1)*n) ≥
        ((Fintype.card Order)*2^n)^k * models.card^(k-1)) := by
  classical
  intro n k hk V Point Clause sat Order F forced hF models pairs hMpos
  have hpairs_eq :
      pairs.card = ∑ order : Order, ∑ s ∈ models, 2 ^ (forced s order).card :=
    PEqualNP.Outside.L_lib_509_aux.pairs_card_eq F
  have hOpos : 0 < Fintype.card Order := Fintype.card_pos
  let S : Finset (Order × Point) := (Finset.univ : Finset Order) ×ˢ models
  have hScard : S.card = Fintype.card Order * models.card := by
    rw [Finset.card_product, Finset.card_univ]
  have hSpos : 0 < S.card := by
    rw [hScard]
    exact Nat.mul_pos hOpos hMpos
  have hSRpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
  have hMRpos : (0 : ℝ) < (models.card : ℝ) := by exact_mod_cast hMpos
  have hORpos : (0 : ℝ) < (Fintype.card Order : ℝ) := by exact_mod_cast hOpos
  have hkRpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hjensen :
      Real.exp (∑ p ∈ S, ((S.card : ℝ)⁻¹ * (((forced p.2 p.1).card : ℝ) * Real.log 2))) ≤
        ∑ p ∈ S, (S.card : ℝ)⁻¹ * Real.exp (((forced p.2 p.1).card : ℝ) * Real.log 2) := by
    refine convexOn_exp.map_sum_le ?_ ?_ ?_
    · intro p _
      exact inv_nonneg.mpr (le_of_lt hSRpos)
    · simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hSRpos)
    · intro p _
      exact Set.mem_univ _
  have hrhs_jensen :
      (∑ p ∈ S, (S.card : ℝ)⁻¹ * Real.exp (((forced p.2 p.1).card : ℝ) * Real.log 2)) =
        (pairs.card : ℝ) / (S.card : ℝ) := by
    rw [← Finset.mul_sum, inv_mul_eq_div]
    congr 1
    rw [hpairs_eq, Nat.cast_sum]
    simp_rw [Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl ?_
    intro order _
    refine Finset.sum_congr rfl ?_
    intro s _
    dsimp only
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlhs_jensen :
      (∑ p ∈ S, ((S.card : ℝ)⁻¹ * (((forced p.2 p.1).card : ℝ) * Real.log 2))) =
        ((∑ s ∈ models, ∑ order : Order, (forced s order).card : ℕ) : ℝ) * Real.log 2 / (S.card : ℝ) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, inv_mul_eq_div]
    congr 2
    rw [Finset.sum_product, Finset.sum_comm]
    push_cast
    rfl
  rw [hlhs_jensen, hrhs_jensen] at hjensen
  have hsum_forced :
      Fintype.card Order *
          (∑ s ∈ models, ((Finset.univ : Finset V).filter
            (fun i => PEqualNP.Outside.L_lib_509_aux.flipPt s i ∉ models)).card) ≤
        k * (∑ s ∈ models, ∑ order : Order, (forced s order).card) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro s hs
    exact PEqualNP.Outside.L_lib_509_aux.expected_forced_ge_iso F hF s (Finset.mem_filter.mp hs).2
  have hiso_edge := PEqualNP.Outside.L_lib_509_aux.sum_iso_add_edge models
  have hedge_log := PEqualNP.Outside.L_lib_509_aux.cube_edge_ineq n models
  have hexp_bound :
      (n : ℝ) * Real.log 2 - Real.log (models.card : ℝ) ≤
        (k : ℝ) * (((∑ s ∈ models, ∑ order : Order, (forced s order).card : ℕ) : ℝ) *
          Real.log 2 / (S.card : ℝ)) := by
    have h1 : (Fintype.card Order : ℝ) *
        ((∑ s ∈ models, ((Finset.univ : Finset V).filter
          (fun i => PEqualNP.Outside.L_lib_509_aux.flipPt s i ∉ models)).card : ℕ) : ℝ) ≤
        (k : ℝ) * ((∑ s ∈ models, ∑ order : Order, (forced s order).card : ℕ) : ℝ) := by
      exact_mod_cast hsum_forced
    have h2 : ((∑ s ∈ models, ((Finset.univ : Finset V).filter
          (fun i => PEqualNP.Outside.L_lib_509_aux.flipPt s i ∉ models)).card : ℕ) : ℝ) +
        (PEqualNP.Outside.L_lib_509_aux.edgeCount models : ℝ) = (models.card : ℝ) * (n : ℝ) := by
      exact_mod_cast hiso_edge
    have hS_real : (S.card : ℝ) = (Fintype.card Order : ℝ) * (models.card : ℝ) := by
      exact_mod_cast hScard
    have h3 : (models.card : ℝ) * ((n : ℝ) * Real.log 2 - Real.log (models.card : ℝ)) ≤
        ((∑ s ∈ models, ((Finset.univ : Finset V).filter
          (fun i => PEqualNP.Outside.L_lib_509_aux.flipPt s i ∉ models)).card : ℕ) : ℝ) *
          Real.log 2 := by
      nlinarith
    have h4 : (S.card : ℝ) * ((n : ℝ) * Real.log 2 - Real.log (models.card : ℝ)) ≤
        (k : ℝ) * (((∑ s ∈ models, ∑ order : Order, (forced s order).card : ℕ) : ℝ) * Real.log 2) := by
      rw [hS_real]
      have hmul1 : (Fintype.card Order : ℝ) * ((models.card : ℝ) * ((n : ℝ) * Real.log 2 - Real.log (models.card : ℝ))) ≤
          (Fintype.card Order : ℝ) * (((∑ s ∈ models, ((Finset.univ : Finset V).filter
            (fun i => PEqualNP.Outside.L_lib_509_aux.flipPt s i ∉ models)).card : ℕ) : ℝ) * Real.log 2) :=
        mul_le_mul_of_nonneg_left h3 (le_of_lt hORpos)
      have hmul2 : (Fintype.card Order : ℝ) * ((∑ s ∈ models, ((Finset.univ : Finset V).filter
            (fun i => PEqualNP.Outside.L_lib_509_aux.flipPt s i ∉ models)).card : ℕ) : ℝ) * Real.log 2 ≤
          (k : ℝ) * ((∑ s ∈ models, ∑ order : Order, (forced s order).card : ℕ) : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right h1 (le_of_lt hlog2)
      linarith
    rw [mul_div_assoc', le_div_iff₀ hSRpos]
    linarith
  have hpow_jensen :
      Real.exp ((k : ℝ) * (((∑ s ∈ models, ∑ order : Order, (forced s order).card : ℕ) : ℝ) *
          Real.log 2 / (S.card : ℝ))) ≤
        ((pairs.card : ℝ) / (S.card : ℝ)) ^ k := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hjensen k
  have hmain_real :
      (2 : ℝ) ^ n / (models.card : ℝ) ≤ ((pairs.card : ℝ) / (S.card : ℝ)) ^ k := by
    have hexp_le := le_trans (Real.exp_le_exp.mpr hexp_bound) hpow_jensen
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log hMRpos] at hexp_le
    exact hexp_le
  have hfinal_real :
      (((Fintype.card Order : ℝ) * (2 : ℝ) ^ n) ^ k * (models.card : ℝ) ^ (k - 1)) ≤
        (pairs.card : ℝ) ^ k * (2 : ℝ) ^ ((k - 1) * n) := by
    rw [div_pow, div_le_div_iff₀ hMRpos (pow_pos hSRpos k)] at hmain_real
    have hS_real : (S.card : ℝ) = (Fintype.card Order : ℝ) * (models.card : ℝ) := by
      exact_mod_cast hScard
    rw [hS_real, mul_pow] at hmain_real
    have hM_split : (models.card : ℝ) ^ k = (models.card : ℝ) ^ (k - 1) * (models.card : ℝ) := by
      conv_lhs => rw [← Nat.sub_add_cancel hk]
      rw [pow_succ]
    rw [hM_split] at hmain_real
    have hcancel : (2 : ℝ) ^ n * ((Fintype.card Order : ℝ) ^ k * (models.card : ℝ) ^ (k - 1)) ≤
        (pairs.card : ℝ) ^ k := by
      have hrew : (2 : ℝ) ^ n * ((Fintype.card Order : ℝ) ^ k * (models.card : ℝ) ^ (k - 1)) *
          (models.card : ℝ) ≤ (pairs.card : ℝ) ^ k * (models.card : ℝ) := by
        linarith
      exact le_of_mul_le_mul_right hrew hMRpos
    have hmul2 := mul_le_mul_of_nonneg_right hcancel (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ((k - 1) * n))
    have h2pow : (2 : ℝ) ^ n * (2 : ℝ) ^ ((k - 1) * n) = ((2 : ℝ) ^ n) ^ k := by
      rw [← pow_add, ← pow_mul]
      congr 1
      have hk1 : 1 + (k - 1) = k := by omega
      calc
        n + (k - 1) * n = (1 + (k - 1)) * n := by ring
        _ = k * n := by rw [hk1]
        _ = n * k := Nat.mul_comm k n
    calc
      ((Fintype.card Order : ℝ) * (2 : ℝ) ^ n) ^ k * (models.card : ℝ) ^ (k - 1)
          = (Fintype.card Order : ℝ) ^ k * ((2 : ℝ) ^ n) ^ k * (models.card : ℝ) ^ (k - 1) := by
            rw [mul_pow]
      _ = (2 : ℝ) ^ n * ((Fintype.card Order : ℝ) ^ k * (models.card : ℝ) ^ (k - 1)) *
            (2 : ℝ) ^ ((k - 1) * n) := by
            rw [← h2pow]
            ring
      _ ≤ (pairs.card : ℝ) ^ k * (2 : ℝ) ^ ((k - 1) * n) := hmul2
  exact_mod_cast hfinal_real
