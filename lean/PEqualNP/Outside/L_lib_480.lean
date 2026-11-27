import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_480_aux

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

private abbrev oddFn {m : ℕ} (x : Fin m → Bool) : Prop :=
  ((Finset.univ : Finset (Fin m)).filter (fun j => x j = true)).card % 2 = 1

private lemma flipPt_odd_iff {m : ℕ} (x : Fin m → Bool) (i : Fin m) :
    oddFn (flipPt x i) ↔ ¬ oddFn x := by
  dsimp only [oddFn]
  let S : Finset (Fin m) := Finset.univ.filter (fun j => x j = true)
  let S' : Finset (Fin m) := Finset.univ.filter (fun j => flipPt x i j = true)
  change S'.card % 2 = 1 ↔ ¬ S.card % 2 = 1
  cases hxi : x i
  · have hiS : i ∉ S := by simp [S, hxi]
    have hS' : S' = insert i S := by
      ext j
      simp only [S', S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hji : j = i
      · subst hji
        simp [flipPt_apply_eq, hxi]
      · simp [flipPt_apply_ne x i j hji, hji]
    rw [hS', Finset.card_insert_of_notMem hiS]
    omega
  · have hiS : i ∈ S := by simp [S, hxi]
    have hS' : S' = S.erase i := by
      ext j
      simp only [S', S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hji : j = i
      · subst hji
        simp [flipPt_apply_eq, hxi]
      · simp [flipPt_apply_ne x i j hji, hji]
    have hpos : 1 ≤ S.card := Finset.one_le_card.mpr ⟨i, hiS⟩
    rw [hS', Finset.card_erase_of_mem hiS]
    omega

private lemma card_oddFn {m : ℕ} (hm : 0 < m) :
    ((Finset.univ : Finset (Fin m → Bool)).filter oddFn).card = 2 ^ (m - 1) := by
  classical
  let i0 : Fin m := ⟨0, hm⟩
  have hbij :
      ((Finset.univ : Finset (Fin m → Bool)).filter oddFn).card =
        ((Finset.univ : Finset (Fin m → Bool)).filter (fun x => ¬ oddFn x)).card := by
    refine Finset.card_bij (fun x _ => flipPt x i0) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (flipPt_odd_iff x i0).not.mpr (not_not.mpr hx)
    · intro a _ b _ h
      have := congrArg (fun z => flipPt z i0) h
      simpa [flipPt_invol] using this
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨flipPt y i0, ?_, flipPt_invol y i0⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (flipPt_odd_iff y i0).mpr hy
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin m → Bool))) (p := oddFn)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← hbij] at hsum
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ, mul_comm]
  omega

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
    have hmem : i ∈ Finset.univ.filter (fun i : Fin n => s1 i ≠ s2 i) := by simp [hi]
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
    · intro _ _
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
    rw [Finset.card_filter, Fintype.sum_prod_type]
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
      have hneg : ¬ ∀ i : Fin n, i ∈ forcedFn F s order ∨ g i = s i := fun h => hex ⟨s, hsm, h⟩
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
    calc ∑ m ∈ S, (A m).card = ∑ _m ∈ S, (A i).card := Finset.sum_congr rfl heq_card
      _ = S.card * (A i).card := by simp
  rw [← hsum_eq]
  have hpart : ∑ m ∈ S, (A m).card = ∑ _π : Equiv.Perm (Fin n), (1 : ℕ) := by
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
      split_ifs
      rfl
    · intro m hm hne
      have hnot : ¬ ∀ j ∈ S, j ≠ m → (π j).val < (π m).val := by
        intro hgood
        have hlt := hgood m0 hm0S hne.symm
        have hle := hmax0 m hm
        omega
      split_ifs
      rfl
    · intro hnot
      exact False.elim (hnot hm0S)
  rw [hpart, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

private lemma expected_forced_ge_all_iso {n k : ℕ} (F : Finset (Finset (Fin n × Bool)))
    (hk : ∀ c ∈ F, c.card ≤ k) (s : Fin n → Bool) (hs : satFn F s)
    (hiso : ∀ i : Fin n, ¬ satFn F (flipPt s i)) :
    Fintype.card (Equiv.Perm (Fin n)) * n ≤
      k * ∑ π : Equiv.Perm (Fin n), (forcedFn F s π).card := by
  classical
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
  rw [hswap, Finset.mul_sum]
  have hconst : Fintype.card (Equiv.Perm (Fin n)) * n =
      ∑ _i : Fin n, Fintype.card (Equiv.Perm (Fin n)) := by
    simp [mul_comm]
  rw [hconst]
  refine Finset.sum_le_sum ?_
  intro i _
  have hnot_sat : ¬ satFn F (flipPt s i) := hiso i
  unfold satFn at hnot_sat
  push Not at hnot_sat
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
  calc Fintype.card (Equiv.Perm (Fin n))
      = S.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card :=
        (perm_max_count S i hiS).symm
    _ ≤ k * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => ∀ j ∈ S, j ≠ i → (π j).val < (π i).val)).card :=
        Nat.mul_le_mul_right _ hScard
    _ ≤ k * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun π => i ∈ forcedFn F s π)).card :=
        Nat.mul_le_mul_left k hsub_perm

private lemma isolated_kcnf_bound {k blocks : ℕ} (hk : 0 < k)
    (F : Finset (Finset (Fin (k * blocks) × Bool)))
    (hF : ∀ c ∈ F, c.card ≤ k)
    (hiso : ∀ s : Fin (k * blocks) → Bool, satFn F s → ∀ i : Fin (k * blocks), ¬ satFn F (flipPt s i)) :
    ((Finset.univ : Finset (Fin (k * blocks) → Bool)).filter (satFn F)).card * 2 ^ blocks ≤
      2 ^ (k * blocks) := by
  classical
  let n := k * blocks
  let models := (Finset.univ : Finset (Fin n → Bool)).filter (satFn F)
  by_cases hM0 : models.card = 0
  · simp [models, hM0]
  · have hMpos : 0 < models.card := Nat.pos_of_ne_zero hM0
    let Order := Equiv.Perm (Fin n)
    let pairs := (Finset.univ : Finset (Order × (Fin n → Bool))).filter (fun og =>
      ∃ s ∈ models, ∀ i : Fin n, i ∈ forcedFn F s og.1 ∨ og.2 i = s i)
    have hpairs_eq :
        pairs.card = ∑ order : Order, ∑ s ∈ models, 2 ^ (forcedFn F s order).card :=
      pairs_card_eq F
    have hpairs_le : pairs.card ≤ Fintype.card Order * 2 ^ n := by
      calc pairs.card
          ≤ (Finset.univ : Finset (Order × (Fin n → Bool))).card := Finset.card_filter_le _ _
        _ = Fintype.card Order * 2 ^ n := by
            rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hOpos : 0 < Fintype.card Order := Fintype.card_pos
    let S : Finset (Order × (Fin n → Bool)) := (Finset.univ : Finset Order) ×ˢ models
    have hScard : S.card = Fintype.card Order * models.card := by
      rw [Finset.card_product, Finset.card_univ]
    have hSpos : 0 < S.card := by
      rw [hScard]
      exact Nat.mul_pos hOpos hMpos
    have hSRpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hSpos
    have hORpos : (0 : ℝ) < (Fintype.card Order : ℝ) := by exact_mod_cast hOpos
    have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hsum_forced :
        S.card * blocks ≤ ∑ s ∈ models, ∑ order : Order, (forcedFn F s order).card := by
      have hmul : k * (S.card * blocks) ≤ k * ∑ s ∈ models, ∑ order : Order, (forcedFn F s order).card := by
        rw [Finset.mul_sum]
        have hstep : ∀ s ∈ models,
            Fintype.card Order * n ≤ k * ∑ order : Order, (forcedFn F s order).card := by
          intro s hs
          have hsat : satFn F s := (Finset.mem_filter.mp hs).2
          exact expected_forced_ge_all_iso F hF s hsat (hiso s hsat)
        calc k * (S.card * blocks)
            = models.card * (Fintype.card Order * n) := by
              rw [hScard]
              dsimp only [n]
              ring
          _ = ∑ _s ∈ models, Fintype.card Order * n := by simp
          _ ≤ ∑ s ∈ models, k * ∑ order : Order, (forcedFn F s order).card :=
              Finset.sum_le_sum hstep
      exact Nat.le_of_mul_le_mul_left hmul hk
    have hjensen :
        Real.exp (∑ p ∈ S, ((S.card : ℝ)⁻¹ * (((forcedFn F p.2 p.1).card : ℝ) * Real.log 2))) ≤
          ∑ p ∈ S, (S.card : ℝ)⁻¹ * Real.exp (((forcedFn F p.2 p.1).card : ℝ) * Real.log 2) := by
      refine convexOn_exp.map_sum_le ?_ ?_ ?_
      · intro _ _
        exact inv_nonneg.mpr (le_of_lt hSRpos)
      · simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_inv_cancel₀ (ne_of_gt hSRpos)
      · intro _ _
        exact Set.mem_univ _
    have hrhs :
        (∑ p ∈ S, (S.card : ℝ)⁻¹ * Real.exp (((forcedFn F p.2 p.1).card : ℝ) * Real.log 2)) =
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
    have hlhs :
        (blocks : ℝ) * Real.log 2 ≤
          ∑ p ∈ S, ((S.card : ℝ)⁻¹ * (((forcedFn F p.2 p.1).card : ℝ) * Real.log 2)) := by
      rw [← Finset.mul_sum, ← Finset.sum_mul, inv_mul_eq_div, le_div_iff₀ hSRpos]
      have hcast : (S.card : ℝ) * (blocks : ℝ) ≤
          ∑ p ∈ S, ((forcedFn F p.2 p.1).card : ℝ) := by
        have hsum_eq : (∑ p ∈ S, ((forcedFn F p.2 p.1).card : ℝ)) =
            ((∑ s ∈ models, ∑ order : Order, (forcedFn F s order).card : ℕ) : ℝ) := by
          rw [Finset.sum_product, Finset.sum_comm]
          push_cast
          rfl
        rw [hsum_eq]
        exact_mod_cast hsum_forced
      nlinarith
    have hexp : (2 : ℝ) ^ blocks ≤ (pairs.card : ℝ) / (S.card : ℝ) := by
      calc (2 : ℝ) ^ blocks
          = Real.exp ((blocks : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ ≤ Real.exp (∑ p ∈ S, ((S.card : ℝ)⁻¹ * (((forcedFn F p.2 p.1).card : ℝ) * Real.log 2))) :=
            Real.exp_le_exp.mpr hlhs
        _ ≤ (pairs.card : ℝ) / (S.card : ℝ) := by rwa [hrhs] at hjensen
    have hreal : (models.card : ℝ) * (2 : ℝ) ^ blocks ≤ (2 : ℝ) ^ n := by
      have h1 : (S.card : ℝ) * (2 : ℝ) ^ blocks ≤ (pairs.card : ℝ) := by
        rwa [le_div_iff₀ hSRpos, mul_comm] at hexp
      have h2 : (pairs.card : ℝ) ≤ (Fintype.card Order : ℝ) * (2 : ℝ) ^ n := by
        exact_mod_cast hpairs_le
      have hSreal : (S.card : ℝ) = (Fintype.card Order : ℝ) * (models.card : ℝ) := by
        exact_mod_cast hScard
      have h3 : (Fintype.card Order : ℝ) * ((models.card : ℝ) * (2 : ℝ) ^ blocks) ≤
          (Fintype.card Order : ℝ) * (2 : ℝ) ^ n := by
        nlinarith
      exact le_of_mul_le_mul_left h3 hORpos
    exact_mod_cast hreal

private def blockParity {k : ℕ} (y : Fin k → Bool) : Bool :=
  decide (((Finset.univ : Finset (Fin k)).filter (fun j => y j = true)).card % 2 = 1)

private def forbidClause {k blocks : ℕ} (b : Fin blocks) (y : Fin k → Bool) :
    Finset (Fin (k * blocks) × Bool) :=
  (Finset.univ : Finset (Fin k)).image (fun j => (finProdFinEquiv (j, b), !(y j)))

private def blockCNF {k blocks : ℕ} (p : Fin blocks → Bool) :
    Finset (Finset (Fin (k * blocks) × Bool)) :=
  ((Finset.univ : Finset (Fin blocks × (Fin k → Bool))).filter
    (fun by_ => blockParity by_.2 ≠ p by_.1)).image (fun by_ => forbidClause by_.1 by_.2)

private lemma blockCNF_width {k blocks : ℕ} (p : Fin blocks → Bool) :
    ∀ c ∈ blockCNF (k := k) p, c.card ≤ k := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨⟨b, y⟩, _, rfl⟩
  calc (forbidClause b y).card
      ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

private lemma sat_blockCNF_iff {k blocks : ℕ} (p : Fin blocks → Bool) (x : Fin (k * blocks) → Bool) :
    satFn (blockCNF p) x ↔ ∀ b : Fin blocks, blockParity (fun j : Fin k => x (finProdFinEquiv (j, b))) = p b := by
  constructor
  · intro hsat b
    by_contra hne
    let y : Fin k → Bool := fun j => x (finProdFinEquiv (j, b))
    have hc : forbidClause b y ∈ blockCNF p := by
      refine Finset.mem_image.mpr ⟨(b, y), ?_, rfl⟩
      simp [hne, y]
    rcases hsat (forbidClause b y) hc with ⟨lit, hlit, hx⟩
    rcases Finset.mem_image.mp hlit with ⟨j, _, rfl⟩
    dsimp only [y] at hx
    cases hxj : x (finProdFinEquiv (j, b)) <;> simp [hxj] at hx
  · intro heq c hc
    rcases Finset.mem_image.mp hc with ⟨⟨b, y⟩, hmem, rfl⟩
    have hne : blockParity y ≠ p b := (Finset.mem_filter.mp hmem).2
    have hfun_ne : (fun j : Fin k => x (finProdFinEquiv (j, b))) ≠ y := by
      intro hxy
      rw [← hxy, heq b] at hne
      exact hne rfl
    have hex : ∃ j : Fin k, x (finProdFinEquiv (j, b)) ≠ y j := by
      by_contra hall
      push Not at hall
      exact hfun_ne (funext hall)
    rcases hex with ⟨j, hj⟩
    refine ⟨(finProdFinEquiv (j, b), !(y j)), Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, ?_⟩
    cases hxj : x (finProdFinEquiv (j, b)) <;> cases hyj : y j <;> simp_all

private lemma sum_mod_two {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ a ∈ s, f a) % 2 = (∑ a ∈ s, f a % 2) % 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    omega

private lemma oddFn_iff_blockParity {k blocks : ℕ} (x : Fin (k * blocks) → Bool) :
    oddFn x ↔ oddFn (fun b : Fin blocks => blockParity (fun j : Fin k => x (finProdFinEquiv (j, b)))) := by
  dsimp only [oddFn]
  have hcnt :
      ((Finset.univ : Finset (Fin (k * blocks))).filter (fun v => x v = true)).card =
        ∑ b : Fin blocks, ((Finset.univ : Finset (Fin k)).filter
          (fun j => x (finProdFinEquiv (j, b)) = true)).card := by
    rw [Finset.card_filter]
    have hre : (∑ v : Fin (k * blocks), if x v = true then 1 else 0) =
        ∑ jb : Fin k × Fin blocks, if x (finProdFinEquiv jb) = true then 1 else 0 := by
      exact (Equiv.sum_comp finProdFinEquiv (fun v => if x v = true then 1 else 0)).symm
    rw [hre, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [← Finset.card_filter]
  rw [hcnt, sum_mod_two]
  have hterm : ∀ b : Fin blocks,
      ((Finset.univ : Finset (Fin k)).filter (fun j => x (finProdFinEquiv (j, b)) = true)).card % 2 =
        if blockParity (fun j : Fin k => x (finProdFinEquiv (j, b))) = true then 1 else 0 := by
    intro b
    unfold blockParity
    split_ifs with h
    · exact of_decide_eq_true h
    · have hne : ((Finset.univ : Finset (Fin k)).filter (fun j => x (finProdFinEquiv (j, b)) = true)).card % 2 ≠ 1 := by
        intro heq
        exact h (decide_eq_true heq)
      omega
  simp_rw [hterm, ← Finset.card_filter]

end PEqualNP.Outside.L_lib_480_aux

theorem PEqualNP.Outside.L_lib_480 : ∀ (k blocks : Nat), 0 < k → 0 < blocks →
  let n := k*blocks
  let V := Fin n
  let Point := V → Bool
  let Clause := Finset (V × Bool)
  let sat := fun (formula : Finset Clause) (x : Point) =>
    ∀ c ∈ formula, ∃ lit ∈ c, x lit.1 = lit.2
  let odd := fun (x : Point) => ((Finset.univ : Finset V).filter (fun j => x j = true)).card % 2 = 1
  ∀ T : Nat, (∃ fs : Fin T → Finset Clause,
    (∀ u, ∀ c ∈ fs u, c.card ≤ k) ∧
    ∀ x : Point, (∃ u, sat (fs u) x) ↔ odd x) ↔ 2^(blocks-1) ≤ T := by
  classical
  intro k blocks hk hblocks n V Point Clause sat odd T
  have hn : 0 < n := Nat.mul_pos hk hblocks
  constructor
  · rintro ⟨fs, hwidth, hcov⟩
    have hbound : ∀ u : Fin T,
        ((Finset.univ : Finset Point).filter (sat (fs u))).card * 2 ^ blocks ≤ 2 ^ n := by
      intro u
      refine PEqualNP.Outside.L_lib_480_aux.isolated_kcnf_bound hk (fs u) (hwidth u) ?_
      intro s hs i hflip
      have hodd_s : PEqualNP.Outside.L_lib_480_aux.oddFn s := (hcov s).mp ⟨u, hs⟩
      have hodd_f : PEqualNP.Outside.L_lib_480_aux.oddFn (PEqualNP.Outside.L_lib_480_aux.flipPt s i) :=
        (hcov _).mp ⟨u, hflip⟩
      exact ((PEqualNP.Outside.L_lib_480_aux.flipPt_odd_iff s i).mp hodd_f) hodd_s
    have hsub : (Finset.univ : Finset Point).filter odd ⊆
        (Finset.univ : Finset (Fin T)).biUnion (fun u => (Finset.univ : Finset Point).filter (sat (fs u))) := by
      intro x hx
      have hodd_x : odd x := (Finset.mem_filter.mp hx).2
      rcases (hcov x).mpr hodd_x with ⟨u, hu⟩
      exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ u, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hu⟩⟩
    have hodd_card : ((Finset.univ : Finset Point).filter odd).card = 2 ^ (n - 1) :=
      PEqualNP.Outside.L_lib_480_aux.card_oddFn hn
    have hle_sum : 2 ^ (n - 1) ≤ ∑ u : Fin T, ((Finset.univ : Finset Point).filter (sat (fs u))).card := by
      calc 2 ^ (n - 1)
          = ((Finset.univ : Finset Point).filter odd).card := hodd_card.symm
        _ ≤ ((Finset.univ : Finset (Fin T)).biUnion
              (fun u => (Finset.univ : Finset Point).filter (sat (fs u)))).card := Finset.card_le_card hsub
        _ ≤ ∑ u : Fin T, ((Finset.univ : Finset Point).filter (sat (fs u))).card := Finset.card_biUnion_le
    have hmul_le : 2 ^ (n - 1) * 2 ^ blocks ≤ T * 2 ^ n := by
      calc 2 ^ (n - 1) * 2 ^ blocks
          ≤ (∑ u : Fin T, ((Finset.univ : Finset Point).filter (sat (fs u))).card) * 2 ^ blocks :=
            Nat.mul_le_mul_right _ hle_sum
        _ = ∑ u : Fin T, ((Finset.univ : Finset Point).filter (sat (fs u))).card * 2 ^ blocks :=
            Finset.sum_mul _ _ _
        _ ≤ ∑ _u : Fin T, 2 ^ n := Finset.sum_le_sum (fun u _ => hbound u)
        _ = T * 2 ^ n := by simp
    have hpow_eq : 2 ^ (n - 1) * 2 ^ blocks = 2 ^ (blocks - 1) * 2 ^ n := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [hpow_eq] at hmul_le
    exact Nat.le_of_mul_le_mul_right hmul_le (Nat.pos_of_ne_zero (by positivity))
  · intro hT
    let O : Finset (Fin blocks → Bool) :=
      (Finset.univ : Finset (Fin blocks → Bool)).filter PEqualNP.Outside.L_lib_480_aux.oddFn
    have hOcard : O.card = 2 ^ (blocks - 1) := PEqualNP.Outside.L_lib_480_aux.card_oddFn hblocks
    let e : Fin (2 ^ (blocks - 1)) ≃ {p : Fin blocks → Bool // p ∈ O} :=
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hOcard])).symm
    let fs : Fin T → Finset Clause := fun u =>
      if hu : u.val < 2 ^ (blocks - 1) then
        PEqualNP.Outside.L_lib_480_aux.blockCNF (e ⟨u.val, hu⟩).1
      else {∅}
    refine ⟨fs, ?_, ?_⟩
    · intro u c hc
      dsimp only [fs] at hc
      split_ifs at hc with hu
      · exact PEqualNP.Outside.L_lib_480_aux.blockCNF_width _ c hc
      · simp only [Finset.mem_singleton] at hc
        rw [hc]
        exact Nat.zero_le k
    · intro x
      constructor
      · rintro ⟨u, hu⟩
        dsimp only [fs] at hu
        split_ifs at hu with hlt
        · have hmatch := (PEqualNP.Outside.L_lib_480_aux.sat_blockCNF_iff (e ⟨u.val, hlt⟩).1 x).mp hu
          have hfun : (fun b : Fin blocks =>
              PEqualNP.Outside.L_lib_480_aux.blockParity (fun j : Fin k => x (finProdFinEquiv (j, b)))) =
              (e ⟨u.val, hlt⟩).1 := funext hmatch
          have hodd_p : PEqualNP.Outside.L_lib_480_aux.oddFn (e ⟨u.val, hlt⟩).1 :=
            (Finset.mem_filter.mp (e ⟨u.val, hlt⟩).2).2
          rw [← hfun] at hodd_p
          exact (PEqualNP.Outside.L_lib_480_aux.oddFn_iff_blockParity x).mpr hodd_p
        · exfalso
          rcases hu ∅ (Finset.mem_singleton_self ∅) with ⟨lit, hlit, _⟩
          exact Finset.notMem_empty lit hlit
      · intro hodd_x
        let p : Fin blocks → Bool := fun b =>
          PEqualNP.Outside.L_lib_480_aux.blockParity (fun j : Fin k => x (finProdFinEquiv (j, b)))
        have hpO : p ∈ O := by
          simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (PEqualNP.Outside.L_lib_480_aux.oddFn_iff_blockParity x).mp hodd_x
        let idx : Fin (2 ^ (blocks - 1)) := e.symm ⟨p, hpO⟩
        let u : Fin T := ⟨idx.val, lt_of_lt_of_le idx.isLt hT⟩
        refine ⟨u, ?_⟩
        dsimp only [fs]
        have hlt : u.val < 2 ^ (blocks - 1) := idx.isLt
        simp only [hlt, ↓reduceDIte]
        have heq : (e ⟨u.val, hlt⟩).1 = p := by
          have hfin : (⟨u.val, hlt⟩ : Fin (2 ^ (blocks - 1))) = idx := Fin.ext rfl
          rw [hfin]
          exact congrArg Subtype.val (e.apply_symm_apply ⟨p, hpO⟩)
        rw [heq]
        exact (PEqualNP.Outside.L_lib_480_aux.sat_blockCNF_iff p x).mpr (fun _ => rfl)
