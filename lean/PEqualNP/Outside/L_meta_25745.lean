import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25745_aux

private lemma z2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a; decide

private lemma z2_neg_eq (a : ZMod 2) : -a = a := by
  revert a; decide

private lemma z2_sub_eq (a b : ZMod 2) : a - b = a + b := by
  revert a b; decide

private lemma z2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a h; decide

private lemma z2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert a b h; decide

private lemma vec_sub_eq_add {r : ℕ} (u v : Fin r → ZMod 2) : u - v = u + v := by
  funext i
  exact z2_sub_eq (u i) (v i)

private lemma symm_zero_diag_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (M : ι → ι → ZMod 2) (hdiag : ∀ i, M i i = 0) (hsymm : ∀ i j, M i j = M j i) :
    ∑ i ∈ s, ∑ j ∈ s, M i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hinner : ∀ i ∈ s, ∑ j ∈ insert a s, M i j = M i a + ∑ j ∈ s, M i j := by
      intro i _
      rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih, hdiag a,
      zero_add, add_zero]
    have hswap : ∑ i ∈ s, M i a = ∑ j ∈ s, M a j := by
      apply Finset.sum_congr rfl
      intro i _
      exact hsymm i a
    rw [hswap]
    exact z2_add_self _

private lemma card_fin_fun_zmod2 (r : ℕ) : Fintype.card (Fin r → ZMod 2) = 2 ^ r := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

private lemma card_submodule_eq_pow {r : ℕ} (W : Submodule (ZMod 2) (Fin r → ZMod 2))
    [Fintype W] : Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
  let b := Module.finBasis (ZMod 2) W
  rw [Fintype.card_congr b.equivFun.toEquiv, Fintype.card_fun, Fintype.card_fin, ZMod.card]

private lemma sum_min_add_deficit {r c : ℕ} (y : Fin (c * 2 ^ r) → (Fin r → ZMod 2)) :
    (∑ v : Fin r → ZMod 2, min c (Finset.univ.filter (fun i => y i = v)).card) +
      (∑ v : Fin r → ZMod 2, (c - (Finset.univ.filter (fun i => y i = v)).card)) = c * 2 ^ r := by
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ v : Fin r → ZMod 2,
      min c (Finset.univ.filter (fun i => y i = v)).card +
        (c - (Finset.univ.filter (fun i => y i = v)).card) = c := by
    intro v
    omega
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ, card_fin_fun_zmod2, smul_eq_mul, mul_comm]

private lemma sum_counts_eq {r n : ℕ} (y : Fin n → (Fin r → ZMod 2)) :
    ∑ v : Fin r → ZMod 2, (Finset.univ.filter (fun i => y i = v)).card = n := by
  have h := Finset.card_eq_sum_card_fiberwise (f := y) (s := (Finset.univ : Finset (Fin n)))
    (t := (Finset.univ : Finset (Fin r → ZMod 2))) (fun _ _ => Finset.mem_univ _)
  simpa using h.symm

private lemma sum_excess_eq_deficit {r c : ℕ} (y : Fin (c * 2 ^ r) → (Fin r → ZMod 2)) :
    ∑ v : Fin r → ZMod 2, ((Finset.univ.filter (fun i => y i = v)).card - c) =
      ∑ v : Fin r → ZMod 2, (c - (Finset.univ.filter (fun i => y i = v)).card) := by
  have h1 := sum_min_add_deficit y
  have h2 := sum_counts_eq y
  have h3 : (∑ v : Fin r → ZMod 2, min c (Finset.univ.filter (fun i => y i = v)).card) +
      (∑ v : Fin r → ZMod 2, ((Finset.univ.filter (fun i => y i = v)).card - c)) =
      ∑ v : Fin r → ZMod 2, (Finset.univ.filter (fun i => y i = v)).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    omega
  omega

private lemma sum_subset_counts_le {r c : ℕ} (y : Fin (c * 2 ^ r) → (Fin r → ZMod 2))
    (S : Finset (Fin r → ZMod 2)) :
    ∑ v ∈ S, (Finset.univ.filter (fun i => y i = v)).card ≤
      c * S.card + ∑ v : Fin r → ZMod 2, (c - (Finset.univ.filter (fun i => y i = v)).card) := by
  rw [← sum_excess_eq_deficit y]
  calc ∑ v ∈ S, (Finset.univ.filter (fun i => y i = v)).card
      ≤ ∑ v ∈ S, (c + ((Finset.univ.filter (fun i => y i = v)).card - c)) := by
        apply Finset.sum_le_sum
        intro v _
        omega
    _ = ∑ _v ∈ S, c + ∑ v ∈ S, ((Finset.univ.filter (fun i => y i = v)).card - c) := by
        rw [Finset.sum_add_distrib]
    _ ≤ c * S.card + ∑ v : Fin r → ZMod 2, ((Finset.univ.filter (fun i => y i = v)).card - c) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        exact Nat.add_le_add_left
          (Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)) _

private lemma exists_perm_of_map {r n : ℕ} (x y : Fin n → (Fin r → ZMod 2))
    (f : (Fin r → ZMod 2) → (Fin r → ZMod 2))
    (hf : ∀ u v, dotProduct (u - v) (f u - f v) = 0) :
    ∃ (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)),
      (∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0) ∧
      K.card = ∑ w : Fin r → ZMod 2,
        min (Finset.univ.filter (fun i : Fin n => f (x i) = w)).card
            (Finset.univ.filter (fun j : Fin n => y j = w)).card := by
  classical
  let k : (Fin r → ZMod 2) → ℕ := fun w =>
    min (Finset.univ.filter (fun i : Fin n => f (x i) = w)).card
        (Finset.univ.filter (fun j : Fin n => y j = w)).card
  have hA_ex : ∀ w : Fin r → ZMod 2,
      ∃ A : Finset (Fin n), A ⊆ Finset.univ.filter (fun i : Fin n => f (x i) = w) ∧ A.card = k w :=
    fun w => Finset.exists_subset_card_eq (Nat.min_le_left _ _)
  have hB_ex : ∀ w : Fin r → ZMod 2,
      ∃ B : Finset (Fin n), B ⊆ Finset.univ.filter (fun j : Fin n => y j = w) ∧ B.card = k w :=
    fun w => Finset.exists_subset_card_eq (Nat.min_le_right _ _)
  choose A hA_sub hA_card using hA_ex
  choose B hB_sub hB_card using hB_ex
  have hA_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r → ZMod 2))) A := by
    intro w₁ _ w₂ _ hne
    change Disjoint (A w₁) (A w₂)
    rw [Finset.disjoint_left]
    intro i hi₁ hi₂
    have h1 := (Finset.mem_filter.mp (hA_sub w₁ hi₁)).2
    have h2 := (Finset.mem_filter.mp (hA_sub w₂ hi₂)).2
    exact hne (h1.symm.trans h2)
  have hB_disj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin r → ZMod 2))) B := by
    intro w₁ _ w₂ _ hne
    change Disjoint (B w₁) (B w₂)
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    have h1 := (Finset.mem_filter.mp (hB_sub w₁ hj₁)).2
    have h2 := (Finset.mem_filter.mp (hB_sub w₂ hj₂)).2
    exact hne (h1.symm.trans h2)
  let K : Finset (Fin n) := Finset.univ.biUnion A
  let L : Finset (Fin n) := Finset.univ.biUnion B
  have hK_card : K.card = ∑ w : Fin r → ZMod 2, k w := by
    rw [Finset.card_biUnion hA_disj]
    exact Finset.sum_congr rfl (fun w _ => hA_card w)
  have hL_card : L.card = ∑ w : Fin r → ZMod 2, k w := by
    rw [Finset.card_biUnion hB_disj]
    exact Finset.sum_congr rfl (fun w _ => hB_card w)
  have hmemA : ∀ {i : Fin n}, i ∈ K → i ∈ A (f (x i)) := by
    intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨w, _, hiw⟩
    have hfx : f (x i) = w := (Finset.mem_filter.mp (hA_sub w hiw)).2
    rwa [hfx]
  have hmemB : ∀ {j : Fin n}, j ∈ L → j ∈ B (y j) := by
    intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨w, _, hjw⟩
    have hyj : y j = w := (Finset.mem_filter.mp (hB_sub w hjw)).2
    rwa [hyj]
  have hew_ex : ∀ w : Fin r → ZMod 2, Nonempty ({i : Fin n // i ∈ A w} ≃ {j : Fin n // j ∈ B w}) := by
    intro w
    exact ⟨Fintype.equivOfCardEq (by simp [hA_card w, hB_card w])⟩
  let ew : ∀ w : Fin r → ZMod 2, {i : Fin n // i ∈ A w} ≃ {j : Fin n // j ∈ B w} :=
    fun w => Classical.choice (hew_ex w)
  have htoL : ∀ i : {i : Fin n // i ∈ K}, (ew (f (x i.1)) ⟨i.1, hmemA i.2⟩).1 ∈ L := by
    intro i
    exact Finset.mem_biUnion.mpr ⟨f (x i.1), Finset.mem_univ _, (ew (f (x i.1)) ⟨i.1, hmemA i.2⟩).2⟩
  have htoK : ∀ j : {j : Fin n // j ∈ L}, ((ew (y j.1)).symm ⟨j.1, hmemB j.2⟩).1 ∈ K := by
    intro j
    exact Finset.mem_biUnion.mpr ⟨y j.1, Finset.mem_univ _, ((ew (y j.1)).symm ⟨j.1, hmemB j.2⟩).2⟩
  have hy_ew : ∀ (w : Fin r → ZMod 2) (i : {i : Fin n // i ∈ A w}), y (ew w i).1 = w :=
    fun w i => (Finset.mem_filter.mp (hB_sub w (ew w i).2)).2
  have hfx_ew : ∀ (w : Fin r → ZMod 2) (j : {j : Fin n // j ∈ B w}), f (x ((ew w).symm j).1) = w :=
    fun w j => (Finset.mem_filter.mp (hA_sub w ((ew w).symm j).2)).2
  let eKL : {i : Fin n // i ∈ K} ≃ {j : Fin n // j ∈ L} :=
    { toFun := fun i => ⟨(ew (f (x i.1)) ⟨i.1, hmemA i.2⟩).1, htoL i⟩
      invFun := fun j => ⟨((ew (y j.1)).symm ⟨j.1, hmemB j.2⟩).1, htoK j⟩
      left_inv := by
        intro ⟨i, hi⟩
        apply Subtype.ext
        dsimp only
        have hy : y (ew (f (x i)) ⟨i, hmemA hi⟩).1 = f (x i) := hy_ew _ _
        have hstep : ∀ (w : Fin r → ZMod 2) (hw : w = f (x i))
            (hmem : (ew (f (x i)) ⟨i, hmemA hi⟩).1 ∈ B w),
            ((ew w).symm ⟨(ew (f (x i)) ⟨i, hmemA hi⟩).1, hmem⟩).1 = i := by
          intro w hw hmem
          subst hw
          have hsub : (⟨(ew (f (x i)) ⟨i, hmemA hi⟩).1, hmem⟩ : {j // j ∈ B (f (x i))}) =
              ew (f (x i)) ⟨i, hmemA hi⟩ := Subtype.ext rfl
          rw [hsub, Equiv.symm_apply_apply]
        exact hstep _ hy _
      right_inv := by
        intro ⟨j, hj⟩
        apply Subtype.ext
        dsimp only
        have hfx : f (x ((ew (y j)).symm ⟨j, hmemB hj⟩).1) = y j := hfx_ew _ _
        have hstep : ∀ (w : Fin r → ZMod 2) (hw : w = y j)
            (hmem : ((ew (y j)).symm ⟨j, hmemB hj⟩).1 ∈ A w),
            (ew w ⟨((ew (y j)).symm ⟨j, hmemB hj⟩).1, hmem⟩).1 = j := by
          intro w hw hmem
          subst hw
          have hsub : (⟨((ew (y j)).symm ⟨j, hmemB hj⟩).1, hmem⟩ : {i // i ∈ A (y j)}) =
              (ew (y j)).symm ⟨j, hmemB hj⟩ := Subtype.ext rfl
          rw [hsub, Equiv.apply_symm_apply]
        exact hstep _ hfx _ }
  have hcompl_card : Fintype.card {i : Fin n // i ∉ K} = Fintype.card {j : Fin n // j ∉ L} := by
    have hK_eq : Fintype.card {i : Fin n // i ∈ K} = K.card := Fintype.card_coe K
    have hL_eq : Fintype.card {j : Fin n // j ∈ L} = L.card := Fintype.card_coe L
    have hsumK := Fintype.card_subtype_compl (fun i : Fin n => i ∈ K)
    have hsumL := Fintype.card_subtype_compl (fun j : Fin n => j ∈ L)
    omega
  let eCompl : {i : Fin n // i ∉ K} ≃ {j : Fin n // j ∉ L} := Fintype.equivOfCardEq hcompl_card
  let π : Equiv.Perm (Fin n) :=
    ((Equiv.sumCompl (fun i : Fin n => i ∈ K)).symm.trans (Equiv.sumCongr eKL eCompl)).trans
      (Equiv.sumCompl (fun j : Fin n => j ∈ L))
  refine ⟨π, K, ?_, hK_card⟩
  have hπK : ∀ i (hi : i ∈ K), π i = (eKL ⟨i, hi⟩).1 := by
    intro i hi
    simp only [π, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hi, Equiv.sumCongr_apply,
      Sum.map_inl, Equiv.sumCompl_apply_inl]
  intro i hi j hj
  rw [hπK i hi, hπK j hj]
  have hyi : y (eKL ⟨i, hi⟩).1 = f (x i) := hy_ew _ _
  have hyj : y (eKL ⟨j, hj⟩).1 = f (x j) := hy_ew _ _
  rw [hyi, hyj]
  exact hf (x i) (x j)

private def sympSwap (r : ℕ) (heven : Even r) (v : Fin r → ZMod 2) : Fin r → ZMod 2 :=
  fun i =>
    if h : i.val % 2 = 0 then
      v ⟨i.val + 1, by
        rcases heven with ⟨m, hm⟩
        have := i.isLt
        omega⟩
    else
      v ⟨i.val - 1, by omega⟩

private lemma sympSwap_involution (r : ℕ) (heven : Even r) (v : Fin r → ZMod 2) :
    sympSwap r heven (sympSwap r heven v) = v := by
  funext i
  dsimp only [sympSwap]
  by_cases h : i.val % 2 = 0
  · have h1 : ¬ ((i.val + 1) % 2 = 0) := by omega
    simp only [h, ↓reduceDIte, h1]
    congr 1
  · have h1 : (i.val - 1) % 2 = 0 := by omega
    simp only [h, ↓reduceDIte, h1]
    congr 1
    apply Fin.ext
    dsimp only
    omega

private lemma sympSwap_sub (r : ℕ) (heven : Even r) (u v : Fin r → ZMod 2) :
    sympSwap r heven u - sympSwap r heven v = sympSwap r heven (u - v) := by
  funext i
  dsimp only [sympSwap, Pi.sub_apply]
  split_ifs <;> rfl

private lemma sympSwap_dot_zero (r : ℕ) (heven : Even r) (v : Fin r → ZMod 2) :
    dotProduct v (sympSwap r heven v) = 0 := by
  rcases heven with ⟨m, hm⟩
  subst hm
  unfold dotProduct
  have hev_mm : Even (m + m) := ⟨m, rfl⟩
  let f : Fin (m + m) → ZMod 2 := fun i => v i * sympSwap (m + m) hev_mm v i
  change ∑ i : Fin (m + m), f i = 0
  let e : Fin m × Fin 2 ≃ Fin (m + m) :=
    { toFun := fun p => ⟨2 * p.1.val + p.2.val, by omega⟩
      invFun := fun i => (⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩)
      left_inv := by
        intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      right_inv := by
        intro ⟨i, hi⟩
        apply Fin.ext
        dsimp only
        omega }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro k _
  rw [Fin.sum_univ_two]
  dsimp only [f]
  have h0 : (2 * k.val + 0) % 2 = 0 := by omega
  have h1 : ¬ ((2 * k.val + 1) % 2 = 0) := by omega
  simp only [e, Equiv.coe_fn_mk, sympSwap, Fin.val_zero, Fin.val_one, h0, h1, ↓reduceDIte]
  have heq0 : (⟨2 * k.val + 0, by omega⟩ : Fin (m + m)) = ⟨2 * k.val + 1 - 1, by omega⟩ :=
    Fin.ext (by dsimp only; omega)
  have heq1 : (⟨2 * k.val + 0 + 1, by omega⟩ : Fin (m + m)) = ⟨2 * k.val + 1, by omega⟩ :=
    Fin.ext rfl
  rw [heq0, heq1, mul_comm (v ⟨2 * k.val + 1, _⟩) (v ⟨2 * k.val + 1 - 1, _⟩)]
  exact z2_add_self _

private lemma achieve_n_sub_e {r c e : ℕ} (heven : Even r)
    (x : Fin (c * 2 ^ r) → (Fin r → ZMod 2))
    (hx : ∀ v, (Finset.univ.filter (fun i => x i = v)).card = c)
    (y : Fin (c * 2 ^ r) → (Fin r → ZMod 2))
    (hdef : ∑ v : Fin r → ZMod 2, (c - (Finset.univ.filter (fun i => y i = v)).card) = e) :
    ∃ (π : Equiv.Perm (Fin (c * 2 ^ r))) (K : Finset (Fin (c * 2 ^ r))),
      (∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0) ∧
      K.card = c * 2 ^ r - e := by
  have hf : ∀ u v : Fin r → ZMod 2,
      dotProduct (u - v) (sympSwap r heven u - sympSwap r heven v) = 0 := by
    intro u v
    rw [sympSwap_sub]
    exact sympSwap_dot_zero r heven (u - v)
  obtain ⟨π, K, hbox, hcard⟩ := exists_perm_of_map x y (sympSwap r heven) hf
  refine ⟨π, K, hbox, ?_⟩
  have hfib : ∀ w : Fin r → ZMod 2,
      (Finset.univ.filter (fun i => sympSwap r heven (x i) = w)).card = c := by
    intro w
    have hfilt : Finset.univ.filter (fun i => sympSwap r heven (x i) = w) =
        Finset.univ.filter (fun i => x i = sympSwap r heven w) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h; rw [← h, sympSwap_involution]
      · intro h; rw [h, sympSwap_involution]
    rw [hfilt, hx]
  simp_rw [hfib] at hcard
  have htot := sum_min_add_deficit y
  omega

private def radSub {r : ℕ}
    (B : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (U : Submodule (ZMod 2) (Fin r → ZMod 2)) : Submodule (ZMod 2) (Fin r → ZMod 2) :=
  { carrier := {u | u ∈ U ∧ ∀ v ∈ U, B u v = 0}, add_mem' := by
      intro a b ha hb
      refine ⟨U.add_mem ha.1 hb.1, fun v hv => ?_⟩
      rw [map_add, LinearMap.add_apply, ha.2 v hv, hb.2 v hv, add_zero]
    zero_mem' := ⟨U.zero_mem, fun _ _ => by simp⟩
    smul_mem' := by
      intro s a ha
      refine ⟨U.smul_mem s ha.1, fun v hv => ?_⟩
      rw [map_smul, LinearMap.smul_apply, ha.2 v hv, smul_zero] }

private lemma even_codim_rad {r : ℕ}
    (B : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (halt : ∀ v, B v v = 0)
    (hsymm : ∀ u v, B u v = B v u)
    (W : Submodule (ZMod 2) (Fin r → ZMod 2)) :
    Even (Module.finrank (ZMod 2) W - Module.finrank (ZMod 2) (radSub B W)) := by
  classical
  let radOf := radSub B
  have hstrong : ∀ k : ℕ, ∀ U : Submodule (ZMod 2) (Fin r → ZMod 2),
      Module.finrank (ZMod 2) U = k →
      Even (Module.finrank (ZMod 2) U - Module.finrank (ZMod 2) (radOf U)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro U hk
      by_cases htriv : ∀ u ∈ U, ∀ v ∈ U, B u v = 0
      · have heq : radOf U = U := by
          ext u
          exact ⟨fun h => h.1, fun hu => ⟨hu, htriv u hu⟩⟩
        rw [heq, Nat.sub_self]
        exact ⟨0, rfl⟩
      · push Not at htriv
        obtain ⟨u, huU, v, hvU, huv_ne⟩ := htriv
        have huv : B u v = 1 := z2_eq_one_of_ne_zero huv_ne
        have hvu : B v u = 1 := by rw [hsymm, huv]
        let φ : U →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
          { toFun := fun w => (B u w.1, B v w.1)
            map_add' := fun a b => by
              apply Prod.ext <;> simp only [Submodule.coe_add, map_add, Prod.fst_add, Prod.snd_add]
            map_smul' := fun s a => by
              apply Prod.ext <;> simp only [SetLike.val_smul, map_smul, Prod.smul_fst,
                Prod.smul_snd, RingHom.id_apply] }
        have hφ_surj : Function.Surjective φ := by
          intro ⟨a, b⟩
          refine ⟨a • ⟨v, hvU⟩ + b • ⟨u, huU⟩, ?_⟩
          apply Prod.ext
          · change B u (a • v + b • u) = a
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, huv, halt u,
              mul_one, mul_zero, add_zero]
          · change B v (a • v + b • u) = b
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hvu, halt v,
              mul_zero, mul_one, zero_add]
        have hrange_φ : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
        have hrank_φ : Module.finrank (ZMod 2) (LinearMap.range φ) = 2 := by
          rw [hrange_φ, finrank_top, Module.finrank_prod, Module.finrank_self]
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        rw [hrank_φ] at hrn
        let U' : Submodule (ZMod 2) (Fin r → ZMod 2) :=
          { carrier := {w | w ∈ U ∧ B u w = 0 ∧ B v w = 0}, add_mem' := by
              intro a b ha hb
              refine ⟨U.add_mem ha.1 hb.1, ?_, ?_⟩
              · rw [map_add, ha.2.1, hb.2.1, add_zero]
              · rw [map_add, ha.2.2, hb.2.2, add_zero]
            zero_mem' := ⟨U.zero_mem, by simp, by simp⟩
            smul_mem' := by
              intro s a ha
              refine ⟨U.smul_mem s ha.1, ?_, ?_⟩
              · rw [map_smul, ha.2.1, smul_zero]
              · rw [map_smul, ha.2.2, smul_zero] }
        let eker : LinearMap.ker φ ≃ₗ[ZMod 2] U' :=
          { toFun := fun w => ⟨w.1.1, w.1.2, by
              have hw : φ w.1 = 0 := w.2
              exact ⟨congrArg Prod.fst hw, congrArg Prod.snd hw⟩⟩
            invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
              change φ ⟨w.1, w.2.1⟩ = 0
              exact Prod.ext w.2.2.1 w.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hdimU' : Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) (LinearMap.ker φ) :=
          eker.finrank_eq.symm
        have hrad_eq : radOf U' = radOf U := by
          ext x
          constructor
          · intro hx
            refine ⟨hx.1.1, fun w hw => ?_⟩
            let w' := w + B u w • v + B v w • u
            have hw'U : w' ∈ U :=
              U.add_mem (U.add_mem hw (U.smul_mem _ hvU)) (U.smul_mem _ huU)
            have hBuw' : B u w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                huv, halt u, mul_one, mul_zero, add_zero]
              exact z2_add_self _
            have hBvw' : B v w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                hvu, halt v, mul_one, mul_zero, add_zero]
              exact z2_add_self _
            have hBxw' : B x w' = 0 := hx.2 w' ⟨hw'U, hBuw', hBvw'⟩
            have hBxu : B x u = 0 := by rw [hsymm]; exact hx.1.2.1
            have hBxv : B x v = 0 := by rw [hsymm]; exact hx.1.2.2
            dsimp only [w'] at hBxw'
            rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
              hBxv, hBxu, mul_zero, mul_zero, add_zero, add_zero] at hBxw'
            exact hBxw'
          · intro hx
            refine ⟨⟨hx.1, ?_, ?_⟩, fun w hw => hx.2 w hw.1⟩
            · rw [hsymm]; exact hx.2 u huU
            · rw [hsymm]; exact hx.2 v hvU
        have hle_rad : Module.finrank (ZMod 2) (radOf U') ≤ Module.finrank (ZMod 2) U' :=
          Submodule.finrank_mono (fun _ hx => hx.1)
        have hU'_lt : Module.finrank (ZMod 2) U' < k := by omega
        have hev' := ih (Module.finrank (ZMod 2) U') hU'_lt U' rfl
        rw [hrad_eq] at hev' hle_rad
        rcases hev' with ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        omega
  exact hstrong (Module.finrank (ZMod 2) W) W rfl

private lemma even_finrank_range_alt {r : ℕ}
    (A : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (halt : ∀ v, dotProduct v (A v) = 0) :
    Even (Module.finrank (ZMod 2) (LinearMap.range A)) := by
  have hsymm : ∀ u v, dotProduct u (A v) = dotProduct v (A u) := by
    intro u v
    have h := halt (u + v)
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, halt u, halt v,
      zero_add, add_zero] at h
    exact z2_eq_of_add_eq_zero h
  let B : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun u =>
        { toFun := fun v => dotProduct u (A v)
          map_add' := fun v₁ v₂ => by rw [map_add, dotProduct_add]
          map_smul' := fun s v => by rw [map_smul, dotProduct_smul, RingHom.id_apply] }
      map_add' := fun u₁ u₂ => by
        apply LinearMap.ext; intro v; exact add_dotProduct u₁ u₂ (A v)
      map_smul' := fun s u => by
        apply LinearMap.ext; intro v; exact smul_dotProduct s u (A v) }
  have hrad : radSub B ⊤ = LinearMap.ker A := by
    ext u
    change (u ∈ (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)) ∧
      ∀ v ∈ (⊤ : Submodule (ZMod 2) (Fin r → ZMod 2)), dotProduct u (A v) = 0) ↔ A u = 0
    constructor
    · intro h
      funext a
      have ha := h.2 (Pi.single a 1) Submodule.mem_top
      rw [hsymm, single_dotProduct, one_mul] at ha
      exact ha
    · intro h
      refine ⟨Submodule.mem_top, fun v _ => ?_⟩
      rw [hsymm, h, dotProduct_zero]
  have hev := even_codim_rad B halt hsymm ⊤
  rw [hrad, finrank_top] at hev
  have hrn := LinearMap.finrank_range_add_finrank_ker A
  have hsub : Module.finrank (ZMod 2) (Fin r → ZMod 2) - Module.finrank (ZMod 2) (LinearMap.ker A) =
      Module.finrank (ZMod 2) (LinearMap.range A) := by omega
  rwa [hsub] at hev

private lemma upper_bound_proof {r c e : ℕ} (hr : 2 ≤ r) (heven : Even r)
    (he : 4 * e ≤ 3 * (c * 2 ^ r))
    (x : Fin (c * 2 ^ r) → (Fin r → ZMod 2))
    (hx : ∀ v, (Finset.univ.filter (fun i => x i = v)).card = c)
    (y : Fin (c * 2 ^ r) → (Fin r → ZMod 2))
    (hdef : ∑ v : Fin r → ZMod 2, (c - (Finset.univ.filter (fun i => y i = v)).card) = e)
    (π : Equiv.Perm (Fin (c * 2 ^ r))) (K : Finset (Fin (c * 2 ^ r)))
    (hbox : ∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0) :
    K.card ≤ max (c * 2 ^ r - e) (c * 2 ^ r / 4 + e) := by
  classical
  let V := Fin r → ZMod 2
  let n := c * 2 ^ r
  have h2r : 2 ^ r = 4 * 2 ^ (r - 2) := by
    calc 2 ^ r = 2 ^ (2 + (r - 2)) := by congr 1; omega
      _ = 4 * 2 ^ (r - 2) := by rw [pow_add]; norm_num
  have hn4 : n = 4 * (c * 2 ^ (r - 2)) := by
    dsimp only [n]
    rw [h2r]
    ring
  have hdiv4 : n / 4 = c * 2 ^ (r - 2) := by omega
  by_cases hKempty : K = ∅
  · rw [hKempty, Finset.card_empty]
    exact Nat.zero_le _
  · obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hKempty
    let x₀ : V := x i₀
    let y₀ : V := y (π i₀)
    let u : Fin n → V := fun i => x i - x₀
    let w : Fin n → V := fun i => y (π i) - y₀
    have hdot_self : ∀ i ∈ K, dotProduct (u i) (w i) = 0 := by
      intro i hi
      exact hbox i hi i₀ hi₀
    have hdot_symm : ∀ i ∈ K, ∀ j ∈ K, dotProduct (u i) (w j) = dotProduct (u j) (w i) := by
      intro i hi j hj
      have h1 := hbox i hi j hj
      have hxu : x i - x j = u i - u j := by
        dsimp only [u]; abel
      have hyw : y (π i) - y (π j) = w i - w j := by
        dsimp only [w]; abel
      rw [hxu, hyw, vec_sub_eq_add (u i), vec_sub_eq_add (w i), add_dotProduct, dotProduct_add,
        dotProduct_add, hdot_self i hi, hdot_self j hj, zero_add, add_zero] at h1
      exact z2_eq_of_add_eq_zero h1
    let S : Set V := (K.image u : Set V)
    let U : Submodule (ZMod 2) V := Submodule.span (ZMod 2) S
    by_cases hUtop : U = ⊤
    · obtain ⟨B, hBS, hspanB, hliB⟩ := exists_linearIndependent (ZMod 2) S
      let b : Module.Basis B (ZMod 2) V :=
        Module.Basis.mk hliB (by
          rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hspanB]
          exact le_of_eq hUtop.symm)
      have hidx_ex : ∀ β : B, ∃ i ∈ K, u i = β.1 := by
        intro β
        have hmem : β.1 ∈ K.image u := hBS β.2
        exact Finset.mem_image.mp hmem
      choose idx hidxK hidx_eq using hidx_ex
      let A : V →ₗ[ZMod 2] V := b.constr (ZMod 2) (fun β => w (idx β))
      have hAb : ∀ β : B, A (b β) = w (idx β) := fun β => b.constr_basis (ZMod 2) _ β
      have hb_eq : ∀ β : B, b β = u (idx β) := by
        intro β
        rw [Module.Basis.mk_apply, hidx_eq β]
      have hAw : ∀ i ∈ K, A (u i) = w i := by
        intro i hi
        have hdot_basis : ∀ β : B, dotProduct (b β) (A (u i)) = dotProduct (b β) (w i) := by
          intro β
          have hrepr := (b.sum_repr (u i)).symm
          conv_lhs => rw [hrepr, map_sum, dotProduct_sum]
          have hterm : ∀ γ : B, dotProduct (b β) (A (b.repr (u i) γ • b γ)) =
              dotProduct (b.repr (u i) γ • b γ) (w (idx β)) := by
            intro γ
            rw [map_smul, dotProduct_smul, smul_dotProduct, hAb γ, hb_eq β, hb_eq γ,
              hdot_symm (idx β) (hidxK β) (idx γ) (hidxK γ)]
          simp_rw [hterm]
          rw [← sum_dotProduct, ← hrepr, hb_eq β, hdot_symm i hi (idx β) (hidxK β)]
        have hdot_all : ∀ v : V, dotProduct v (A (u i)) = dotProduct v (w i) := by
          intro v
          rw [← b.sum_repr v, sum_dotProduct, sum_dotProduct]
          apply Finset.sum_congr rfl
          intro β _
          rw [smul_dotProduct, smul_dotProduct, hdot_basis β]
        funext a
        have ha := hdot_all (Pi.single a 1)
        simpa [single_dotProduct] using ha
      have halt : ∀ v : V, dotProduct v (A v) = 0 := by
        intro v
        rw [← b.sum_repr v, map_sum, sum_dotProduct]
        have hinner : ∀ β : B, dotProduct (b.repr v β • b β) (∑ γ : B, A (b.repr v γ • b γ)) =
            ∑ γ : B, b.repr v β * (b.repr v γ * dotProduct (u (idx β)) (w (idx γ))) := by
          intro β
          rw [dotProduct_sum]
          apply Finset.sum_congr rfl
          intro γ _
          rw [map_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hAb γ, hb_eq β]
        simp_rw [hinner]
        let M : B → B → ZMod 2 := fun β γ =>
          b.repr v β * (b.repr v γ * dotProduct (u (idx β)) (w (idx γ)))
        change ∑ β ∈ Finset.univ, ∑ γ ∈ Finset.univ, M β γ = 0
        apply symm_zero_diag_sum
        · intro β
          dsimp only [M]
          rw [hdot_self (idx β) (hidxK β), mul_zero, mul_zero]
        · intro β γ
          dsimp only [M]
          rw [hdot_symm (idx β) (hidxK β) (idx γ) (hidxK γ)]
          ring
      let b₀ : V := y₀ - A x₀
      have hy_aff : ∀ i ∈ K, y (π i) = A (x i) + b₀ := by
        intro i hi
        have h1 : A (x i - x₀) = y (π i) - y₀ := hAw i hi
        rw [map_sub] at h1
        dsimp only [b₀]
        calc y (π i) = (y (π i) - y₀) + y₀ := by abel
          _ = (A (x i) - A x₀) + y₀ := by rw [← h1]
          _ = A (x i) + (y₀ - A x₀) := by abel
      by_cases hker : LinearMap.ker A = ⊥
      · have hA_inj : Function.Injective A := LinearMap.ker_eq_bot.mp hker
        let f : V → V := fun v => A v + b₀
        have hf_inj : Function.Injective f := by
          intro v₁ v₂ h
          exact hA_inj (add_right_cancel h)
        have hf_bij : Function.Bijective f := Finite.injective_iff_bijective.mp hf_inj
        let ef : V ≃ V := Equiv.ofBijective f hf_bij
        have hK_part : K.card = ∑ v : V, (K.filter (fun i => x i = v)).card := by
          have h := Finset.card_eq_sum_card_fiberwise (f := x) (s := K)
            (t := (Finset.univ : Finset V)) (fun _ _ => Finset.mem_univ _)
          exact h
        have hK_le : ∀ v : V, (K.filter (fun i => x i = v)).card ≤
            min c (Finset.univ.filter (fun j => y j = f v)).card := by
          intro v
          apply le_min
          · calc (K.filter (fun i => x i = v)).card
                ≤ (Finset.univ.filter (fun i => x i = v)).card :=
                  Finset.card_le_card (fun i hi => by
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                    exact hi.2)
              _ = c := hx v
          · calc (K.filter (fun i => x i = v)).card
                = ((K.filter (fun i => x i = v)).image π).card :=
                  (Finset.card_image_of_injective _ π.injective).symm
              _ ≤ (Finset.univ.filter (fun j => y j = f v)).card := by
                  apply Finset.card_le_card
                  intro j hj
                  rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                  rw [hy_aff i hi.1, hi.2]
        have hsum_le : K.card ≤ ∑ v : V, min c (Finset.univ.filter (fun j => y j = f v)).card := by
          rw [hK_part]
          exact Finset.sum_le_sum (fun v _ => hK_le v)
        have hsum_eq : ∑ v : V, min c (Finset.univ.filter (fun j => y j = f v)).card =
            ∑ v : V, min c (Finset.univ.filter (fun j => y j = v)).card :=
          Equiv.sum_comp ef (fun v => min c (Finset.univ.filter (fun j => y j = v)).card)
        have htot := sum_min_add_deficit y
        have hle_ne : K.card ≤ n - e := by
          rw [hsum_eq] at hsum_le
          dsimp only [V, n] at hsum_le ⊢
          rw [hdef] at htot
          omega
        exact le_trans hle_ne (le_max_left _ _)
      · have hev_rk := even_finrank_range_alt A halt
        have hker_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker A) := by
          have hbot : ⊥ < LinearMap.ker A := bot_lt_iff_ne_bot.mpr hker
          have hlt := Submodule.finrank_lt_finrank_of_lt hbot
          rw [finrank_bot] at hlt
          exact hlt
        have hrn := LinearMap.finrank_range_add_finrank_ker A
        have hfinV : Module.finrank (ZMod 2) V = r := Module.finrank_fin_fun (ZMod 2)
        rw [hfinV] at hrn
        have hrk_le : Module.finrank (ZMod 2) (LinearMap.range A) ≤ r - 2 := by
          dsimp only [V] at hrn hker_pos ⊢
          rcases heven with ⟨m, hm⟩
          rcases hev_rk with ⟨t, ht⟩
          omega
        let S_img : Finset V := Finset.univ.filter (fun v : V => v - b₀ ∈ LinearMap.range A)
        have hS_img_card : S_img.card ≤ 2 ^ (r - 2) := by
          have heqv : S_img.card = Fintype.card (LinearMap.range A) := by
            rw [← Fintype.card_coe S_img]
            refine Fintype.card_congr
              { toFun := fun v => ⟨v.1 - b₀, (Finset.mem_filter.mp v.2).2⟩
                invFun := fun v => ⟨v.1 + b₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                  simpa using v.2⟩⟩
                left_inv := fun v => Subtype.ext (by simp)
                right_inv := fun v => Subtype.ext (by simp) }
          rw [heqv, card_submodule_eq_pow]
          exact Nat.pow_le_pow_right (by norm_num) hrk_le
        have hK_le_sum : K.card ≤ ∑ v ∈ S_img, (Finset.univ.filter (fun j => y j = v)).card := by
          calc K.card = (K.image π).card := (Finset.card_image_of_injective K π.injective).symm
            _ = ∑ v ∈ S_img, ((K.image π).filter (fun j => y j = v)).card := by
                apply Finset.card_eq_sum_card_fiberwise
                intro j hj
                rcases Finset.mem_image.mp hj with ⟨i, hi, rfl⟩
                simp only [Finset.mem_coe, S_img, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hy_aff i hi, add_sub_cancel_right]
                exact LinearMap.mem_range_self A (x i)
            _ ≤ ∑ v ∈ S_img, (Finset.univ.filter (fun j => y j = v)).card := by
                apply Finset.sum_le_sum
                intro v _
                apply Finset.card_le_card
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                exact hj.2
        have hsum_ub := sum_subset_counts_le y S_img
        rw [hdef] at hsum_ub
        have hle_qe : K.card ≤ n / 4 + e := by
          have h1 : c * S_img.card ≤ c * 2 ^ (r - 2) := Nat.mul_le_mul_left c hS_img_card
          have h2 : K.card ≤ c * S_img.card + e := le_trans hK_le_sum hsum_ub
          omega
        exact le_trans hle_qe (le_max_right _ _)
    · have hU_lt : U < ⊤ := lt_top_iff_ne_top.mpr hUtop
      have hrank_lt : Module.finrank (ZMod 2) U < Module.finrank (ZMod 2) V := by
        simpa [finrank_top] using Submodule.finrank_lt_finrank_of_lt hU_lt
      have hfinV : Module.finrank (ZMod 2) V = r := Module.finrank_fin_fun (ZMod 2)
      rw [hfinV] at hrank_lt
      have hrank_le : Module.finrank (ZMod 2) U ≤ r - 1 := by omega
      let S_U : Finset V := Finset.univ.filter (fun v : V => v - x₀ ∈ U)
      have hSU_card : S_U.card ≤ 2 ^ (r - 1) := by
        have heqv : S_U.card = Fintype.card U := by
          rw [← Fintype.card_coe S_U]
          refine Fintype.card_congr
            { toFun := fun v => ⟨v.1 - x₀, (Finset.mem_filter.mp v.2).2⟩
              invFun := fun v => ⟨v.1 + x₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
                simpa using v.2⟩⟩
              left_inv := fun v => Subtype.ext (by simp)
              right_inv := fun v => Subtype.ext (by simp) }
        rw [heqv, card_submodule_eq_pow]
        exact Nat.pow_le_pow_right (by norm_num) hrank_le
      have hK_le_half : K.card ≤ c * 2 ^ (r - 1) := by
        calc K.card = ∑ v ∈ S_U, (K.filter (fun i => x i = v)).card := by
              apply Finset.card_eq_sum_card_fiberwise
              intro i hi
              simp only [Finset.mem_coe, S_U, Finset.mem_filter, Finset.mem_univ, true_and]
              exact Submodule.subset_span (Finset.mem_image_of_mem u hi)
          _ ≤ ∑ v ∈ S_U, (Finset.univ.filter (fun i => x i = v)).card := by
              apply Finset.sum_le_sum
              intro v _
              apply Finset.card_le_card
              intro i hi
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
              exact hi.2
          _ = ∑ _v ∈ S_U, c := Finset.sum_congr rfl (fun v _ => hx v)
          _ = c * S_U.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ c * 2 ^ (r - 1) := Nat.mul_le_mul_left c hSU_card
      have hhalf_eq : c * 2 ^ (r - 1) = 2 * (c * 2 ^ (r - 2)) := by
        have h1 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := by
          calc 2 ^ (r - 1) = 2 ^ (1 + (r - 2)) := by congr 1; omega
            _ = 2 * 2 ^ (r - 2) := by rw [pow_add, pow_one]
        rw [h1]; ring
      rw [hhalf_eq] at hK_le_half
      have hle_max : 2 * (c * 2 ^ (r - 2)) ≤ max (n - e) (n / 4 + e) := by
        by_cases heq : e ≤ 2 * (c * 2 ^ (r - 2))
        · exact le_trans (by omega) (le_max_left _ _)
        · exact le_trans (by omega) (le_max_right _ _)
      exact le_trans hK_le_half hle_max

private def degAltMap (r : ℕ) (heven : Even r) (v : Fin r → ZMod 2) : Fin r → ZMod 2 :=
  fun i =>
    if i.val < 2 then 0
    else if h : i.val % 2 = 0 then
      v ⟨i.val + 1, by
        rcases heven with ⟨m, hm⟩
        have := i.isLt
        omega⟩
    else
      v ⟨i.val - 1, by omega⟩

private lemma degAltMap_sub (r : ℕ) (heven : Even r) (u v : Fin r → ZMod 2) :
    degAltMap r heven u - degAltMap r heven v = degAltMap r heven (u - v) := by
  funext i
  dsimp only [degAltMap, Pi.sub_apply]
  split_ifs <;> simp

private lemma degAltMap_dot_zero (r : ℕ) (heven : Even r) (v : Fin r → ZMod 2) :
    dotProduct v (degAltMap r heven v) = 0 := by
  rcases heven with ⟨m, hm⟩
  subst hm
  unfold dotProduct
  have hev_mm : Even (m + m) := ⟨m, rfl⟩
  let f : Fin (m + m) → ZMod 2 := fun i => v i * degAltMap (m + m) hev_mm v i
  change ∑ i : Fin (m + m), f i = 0
  let e : Fin m × Fin 2 ≃ Fin (m + m) :=
    { toFun := fun p => ⟨2 * p.1.val + p.2.val, by omega⟩
      invFun := fun i => (⟨i.val / 2, by omega⟩, ⟨i.val % 2, by omega⟩)
      left_inv := by
        intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
        apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
      right_inv := by
        intro ⟨i, hi⟩
        apply Fin.ext
        dsimp only
        omega }
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro k _
  rw [Fin.sum_univ_two]
  dsimp only [f]
  by_cases hk0 : k.val = 0
  · have hlt0 : 2 * k.val < 2 := by omega
    have hlt1 : 2 * k.val + 1 < 2 := by omega
    simp only [e, Equiv.coe_fn_mk, degAltMap, Fin.val_zero, Fin.val_one, add_zero, hlt0, hlt1,
      ↓reduceIte, mul_zero]
  · have hlt0 : ¬ (2 * k.val + 0 < 2) := by omega
    have hlt1 : ¬ (2 * k.val + 1 < 2) := by omega
    have h0 : (2 * k.val + 0) % 2 = 0 := by omega
    have h1 : ¬ ((2 * k.val + 1) % 2 = 0) := by omega
    simp only [e, Equiv.coe_fn_mk, degAltMap, Fin.val_zero, Fin.val_one, hlt0, hlt1, h0, h1,
      ↓reduceIte, ↓reduceDIte]
    have heq0 : (⟨2 * k.val + 0, by omega⟩ : Fin (m + m)) = ⟨2 * k.val + 1 - 1, by omega⟩ :=
      Fin.ext (by dsimp only; omega)
    have heq1 : (⟨2 * k.val + 0 + 1, by omega⟩ : Fin (m + m)) = ⟨2 * k.val + 1, by omega⟩ :=
      Fin.ext rfl
    rw [heq0, heq1, mul_comm (v ⟨2 * k.val + 1, _⟩) (v ⟨2 * k.val + 1 - 1, _⟩)]
    exact z2_add_self _

private lemma sharpness_proof {r c e : ℕ} (hr : 2 ≤ r) (heven : Even r)
    (he : 4 * e ≤ 3 * (c * 2 ^ r))
    (x : Fin (c * 2 ^ r) → (Fin r → ZMod 2))
    (hx : ∀ v, (Finset.univ.filter (fun i => x i = v)).card = c) :
    ∃ (y : Fin (c * 2 ^ r) → (Fin r → ZMod 2)),
      (∑ v : Fin r → ZMod 2, (c - (Finset.univ.filter (fun i => y i = v)).card) = e) ∧
      ∃ (π : Equiv.Perm (Fin (c * 2 ^ r))) (K : Finset (Fin (c * 2 ^ r))),
        (∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0) ∧
        K.card = max (c * 2 ^ r - e) (c * 2 ^ r / 4 + e) := by
  classical
  let V := Fin r → ZMod 2
  let n := c * 2 ^ r
  let M := 2 ^ (r - 2)
  have hM_pos : 0 < M := Nat.two_pow_pos (r - 2)
  have h2r : 2 ^ r = 4 * M := by
    dsimp only [M]
    calc 2 ^ r = 2 ^ (2 + (r - 2)) := by congr 1; omega
      _ = 4 * 2 ^ (r - 2) := by rw [pow_add]; norm_num
  have hn4 : n = 4 * (c * M) := by dsimp only [n]; rw [h2r]; ring
  have hdiv4 : n / 4 = c * M := by omega
  have he_le : e ≤ 3 * c * M := by
    have : 4 * e ≤ 4 * (3 * c * M) := by
      calc 4 * e ≤ 3 * n := he
        _ = 4 * (3 * c * M) := by rw [hn4]; ring
    omega
  let i0 : Fin r := ⟨0, by omega⟩
  let i1 : Fin r := ⟨1, by omega⟩
  let W : Finset V := Finset.univ.filter (fun v : V => v i0 = 0 ∧ v i1 = 0)
  have hW_card : W.card = M := by
    let eW : {v : V // v ∈ W} ≃ (Fin (r - 2) → ZMod 2) :=
      { toFun := fun v j => v.1 ⟨j.val + 2, by omega⟩
        invFun := fun g => ⟨fun i => if h : i.val < 2 then 0 else g ⟨i.val - 2, by omega⟩, by
          simp only [W, Finset.mem_filter, Finset.mem_univ, true_and, i0, i1]
          exact ⟨by simp, by simp⟩⟩
        left_inv := by
          intro ⟨v, hv⟩
          apply Subtype.ext
          funext i
          simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          by_cases h : i.val < 2
          · simp only [h, ↓reduceDIte]
            have h01 : i = i0 ∨ i = i1 := by
              by_cases hi : i.val = 0
              · left; exact Fin.ext hi
              · right; apply Fin.ext; dsimp only [i1]; omega
            rcases h01 with rfl | rfl
            · exact hv.1.symm
            · exact hv.2.symm
          · simp only [h, ↓reduceDIte]
            congr 1; apply Fin.ext; dsimp only; omega
        right_inv := by
          intro g
          funext j
          have h : ¬ (j.val + 2 < 2) := by omega
          simp only [h, ↓reduceDIte]
          congr 1 }
    rw [← Fintype.card_coe W, Fintype.card_congr eW, card_fin_fun_zmod2]
  have hWc_card : Wᶜ.card = 3 * M := by
    have h1 : W.card + Wᶜ.card = Fintype.card V := Finset.card_add_card_compl W
    rw [hW_card, card_fin_fun_zmod2, h2r] at h1
    omega
  let enumW : {v : V // v ∈ W} ≃ Fin M :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, hW_card, Fintype.card_fin])
  let enumWc : {v : V // v ∈ Wᶜ} ≃ Fin (3 * M) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe, hWc_card, Fintype.card_fin])
  let addFun : Fin M → ℕ := fun k => e / M + if k.val < e % M then 1 else 0
  let subFun : Fin (3 * M) → ℕ := fun k => e / (3 * M) + if k.val < e % (3 * M) then 1 else 0
  have hadd_le : ∀ k : Fin M, addFun k ≤ 3 * c := by
    intro k
    dsimp only [addFun]
    by_cases hfull : e = 3 * c * M
    · rw [hfull, Nat.mul_div_cancel _ hM_pos, Nat.mul_mod_left]
      simp
    · have hlt : e < 3 * c * M := lt_of_le_of_ne he_le hfull
      have hq : e / M < 3 * c := (Nat.div_lt_iff_lt_mul hM_pos).mpr hlt
      split_ifs <;> omega
  have hsub_le : ∀ k : Fin (3 * M), subFun k ≤ c := by
    intro k
    dsimp only [subFun]
    have h3M_pos : 0 < 3 * M := by omega
    by_cases hfull : e = c * (3 * M)
    · rw [hfull, Nat.mul_div_cancel _ h3M_pos, Nat.mul_mod_left]
      simp
    · have hlt : e < c * (3 * M) := lt_of_le_of_ne (by linarith) hfull
      have hq : e / (3 * M) < c := (Nat.div_lt_iff_lt_mul h3M_pos).mpr hlt
      split_ifs <;> omega
  have hsum_add : ∑ k : Fin M, addFun k = e := by
    dsimp only [addFun]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hrem : (∑ k : Fin M, if k.val < e % M then 1 else 0) = e % M := by
      rw [← Finset.card_filter]
      have hlt : e % M ≤ M := le_of_lt (Nat.mod_lt e hM_pos)
      have heqv : (Finset.univ.filter (fun k : Fin M => k.val < e % M)).card =
          Fintype.card (Fin (e % M)) := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr
          { toFun := fun k => ⟨k.1.val, (Finset.mem_filter.mp k.2).2⟩
            invFun := fun k => ⟨⟨k.val, lt_of_lt_of_le k.isLt hlt⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩⟩
            left_inv := fun k => Subtype.ext (Fin.ext rfl)
            right_inv := fun k => Fin.ext rfl }
      rw [heqv, Fintype.card_fin]
    rw [hrem, Nat.div_add_mod]
  have hsum_sub : ∑ k : Fin (3 * M), subFun k = e := by
    dsimp only [subFun]
    have h3M_pos : 0 < 3 * M := by omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hrem : (∑ k : Fin (3 * M), if k.val < e % (3 * M) then 1 else 0) = e % (3 * M) := by
      rw [← Finset.card_filter]
      have hlt : e % (3 * M) ≤ 3 * M := le_of_lt (Nat.mod_lt e h3M_pos)
      have heqv : (Finset.univ.filter (fun k : Fin (3 * M) => k.val < e % (3 * M))).card =
          Fintype.card (Fin (e % (3 * M))) := by
        rw [← Fintype.card_coe]
        refine Fintype.card_congr
          { toFun := fun k => ⟨k.1.val, (Finset.mem_filter.mp k.2).2⟩
            invFun := fun k => ⟨⟨k.val, lt_of_lt_of_le k.isLt hlt⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩⟩
            left_inv := fun k => Subtype.ext (Fin.ext rfl)
            right_inv := fun k => Fin.ext rfl }
      rw [heqv, Fintype.card_fin]
    rw [hrem, Nat.div_add_mod]
  let cnt : V → ℕ := fun v =>
    if hv : v ∈ W then c + addFun (enumW ⟨v, hv⟩)
    else c - subFun (enumWc ⟨v, Finset.mem_compl.mpr hv⟩)
  have hsum_W : ∑ v ∈ W, cnt v = c * M + e := by
    have h1 : ∑ v ∈ W, cnt v = ∑ v : {v : V // v ∈ W}, (c + addFun (enumW v)) := by
      rw [← Finset.sum_coe_sort W]
      apply Finset.sum_congr rfl
      intro v _
      simp only [cnt, v.2, ↓reduceDIte]
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
      hW_card, smul_eq_mul, mul_comm, Equiv.sum_comp enumW addFun, hsum_add]
  have hsum_Wc : ∑ v ∈ Wᶜ, cnt v = 3 * c * M - e := by
    have h1 : ∑ v ∈ Wᶜ, cnt v = ∑ v : {v : V // v ∈ Wᶜ}, (c - subFun (enumWc v)) := by
      rw [← Finset.sum_coe_sort Wᶜ]
      apply Finset.sum_congr rfl
      intro v _
      have hv : v.1 ∉ W := Finset.mem_compl.mp v.2
      simp only [cnt, hv, ↓reduceDIte]
    rw [h1]
    have hadd_back : (∑ v : {v : V // v ∈ Wᶜ}, (c - subFun (enumWc v))) +
        (∑ v : {v : V // v ∈ Wᶜ}, subFun (enumWc v)) = 3 * c * M := by
      rw [← Finset.sum_add_distrib]
      have hterm : ∀ v : {v : V // v ∈ Wᶜ}, (c - subFun (enumWc v)) + subFun (enumWc v) = c :=
        fun v => Nat.sub_add_cancel (hsub_le (enumWc v))
      simp_rw [hterm]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, hWc_card, smul_eq_mul]
      ring
    rw [Equiv.sum_comp enumWc subFun, hsum_sub] at hadd_back
    omega
  have hsum_cnt : ∑ v : V, cnt v = n := by
    rw [← Finset.sum_add_sum_compl W cnt, hsum_W, hsum_Wc]
    have h4 : 4 * (c * M) = c * M + 3 * c * M := by ring
    omega
  have hcard_sigma : Fintype.card (Fin n) = Fintype.card (Σ v : V, Fin (cnt v)) := by
    rw [Fintype.card_fin, Fintype.card_sigma]
    simp only [Fintype.card_fin, hsum_cnt]
  let eqvY : Fin n ≃ Σ v : V, Fin (cnt v) := Fintype.equivOfCardEq hcard_sigma
  let y : Fin n → V := fun i => (eqvY i).1
  have hy_cnt : ∀ v : V, (Finset.univ.filter (fun i : Fin n => y i = v)).card = cnt v := by
    intro v
    rw [← Fintype.card_coe]
    let e1 : {i : Fin n // i ∈ Finset.univ.filter (fun i : Fin n => y i = v)} ≃
        {p : Σ w : V, Fin (cnt w) // p.1 = v} :=
      Equiv.subtypeEquiv eqvY (fun i => by simp [y])
    let e2 : {p : Σ w : V, Fin (cnt w) // p.1 = v} ≃ Fin (cnt v) :=
      { toFun := fun ⟨⟨_, k⟩, hw⟩ => hw ▸ k
        invFun := fun k => ⟨⟨v, k⟩, rfl⟩
        left_inv := fun ⟨⟨_, _⟩, hw⟩ => by subst hw; rfl
        right_inv := fun _ => rfl }
    rw [Fintype.card_congr (e1.trans e2), Fintype.card_fin]
  have hy_def : ∑ v : V, (c - (Finset.univ.filter (fun i => y i = v)).card) = e := by
    simp_rw [hy_cnt]
    rw [← Finset.sum_add_sum_compl W]
    have hW0 : ∑ v ∈ W, (c - cnt v) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [cnt, hv, ↓reduceDIte]
      omega
    have hWce : ∑ v ∈ Wᶜ, (c - cnt v) = e := by
      have h1 : ∑ v ∈ Wᶜ, (c - cnt v) = ∑ v : {v : V // v ∈ Wᶜ}, subFun (enumWc v) := by
        rw [← Finset.sum_coe_sort Wᶜ]
        apply Finset.sum_congr rfl
        intro v _
        have hv : v.1 ∉ W := Finset.mem_compl.mp v.2
        simp only [cnt, hv, ↓reduceDIte]
        have hv_eq : (⟨v.1, Finset.mem_compl.mpr hv⟩ : {w : V // w ∈ Wᶜ}) = v := Subtype.ext rfl
        rw [hv_eq]
        have hle := hsub_le (enumWc v)
        omega
      rw [h1, Equiv.sum_comp enumWc subFun, hsum_sub]
    rw [hW0, hWce, zero_add]
  refine ⟨y, hy_def, ?_⟩
  by_cases hcase : n - e ≤ n / 4 + e
  · rw [max_eq_right hcase]
    have hf : ∀ u v : V, dotProduct (u - v) (degAltMap r heven u - degAltMap r heven v) = 0 := by
      intro u v
      rw [degAltMap_sub]
      exact degAltMap_dot_zero r heven (u - v)
    obtain ⟨π, K, hbox, hcard⟩ := exists_perm_of_map x y (degAltMap r heven) hf
    refine ⟨π, K, hbox, ?_⟩
    have hdeg_fib : ∀ w : V,
        (Finset.univ.filter (fun i : Fin n => degAltMap r heven (x i) = w)).card =
          if w ∈ W then 4 * c else 0 := by
      intro w
      by_cases hw : w ∈ W
      · simp only [hw, ↓reduceIte]
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and] at hw
        let fw : V → V := fun v => degAltMap r heven v
        let fiberV : Finset V := Finset.univ.filter (fun v : V => fw v = w)
        have hfibV_card : fiberV.card = 4 := by
          let efib : {v : V // v ∈ fiberV} ≃ (ZMod 2 × ZMod 2) :=
            { toFun := fun v => (v.1 i0, v.1 i1)
              invFun := fun p => ⟨fun i =>
                  if i = i0 then p.1
                  else if i = i1 then p.2
                  else degAltMap r heven w i, by
                simp only [fiberV, Finset.mem_filter, Finset.mem_univ, true_and, fw]
                funext i
                dsimp only [degAltMap]
                by_cases hlt : i.val < 2
                · simp only [hlt, ↓reduceIte]
                  by_cases hi : i.val = 0
                  · have : i = i0 := Fin.ext hi
                    rw [this, hw.1]
                  · have : i = i1 := by apply Fin.ext; dsimp only [i1]; omega
                    rw [this, hw.2]
                · simp only [hlt, ↓reduceIte]
                  by_cases hev : i.val % 2 = 0
                  · have hne0 : (⟨i.val + 1, by rcases heven with ⟨m, hm⟩; have := i.isLt; omega⟩ : Fin r) ≠ i0 := by
                      intro h; have := congrArg Fin.val h; dsimp only [i0] at this; omega
                    have hne1 : (⟨i.val + 1, by rcases heven with ⟨m, hm⟩; have := i.isLt; omega⟩ : Fin r) ≠ i1 := by
                      intro h; have := congrArg Fin.val h; dsimp only [i1] at this; omega
                    have hlt' : ¬ (i.val + 1 < 2) := by omega
                    have hev' : ¬ ((i.val + 1) % 2 = 0) := by omega
                    simp only [hev, ↓reduceDIte, hne0, hne1, ↓reduceIte, hlt', hev']
                    congr 1
                  · have hne0 : (⟨i.val - 1, by omega⟩ : Fin r) ≠ i0 := by
                      intro h; have := congrArg Fin.val h; dsimp only [i0] at this; omega
                    have hne1 : (⟨i.val - 1, by omega⟩ : Fin r) ≠ i1 := by
                      intro h; have := congrArg Fin.val h; dsimp only [i1] at this; omega
                    have hlt' : ¬ (i.val - 1 < 2) := by omega
                    have hev' : (i.val - 1) % 2 = 0 := by omega
                    simp only [hev, ↓reduceDIte, hne0, hne1, ↓reduceIte, hlt', hev']
                    congr 1; apply Fin.ext; dsimp only; omega⟩
              left_inv := by
                intro ⟨v, hv⟩
                apply Subtype.ext
                funext i
                simp only [fiberV, Finset.mem_filter, Finset.mem_univ, true_and, fw] at hv
                by_cases h0 : i = i0
                · simp [h0]
                · by_cases h1 : i = i1
                  · have hne : i1 ≠ i0 := by
                      intro h; have := congrArg Fin.val h; dsimp only [i0, i1] at this; omega
                    simp [h1, hne]
                  · have hlt : ¬ (i.val < 2) := by
                      intro hlt
                      by_cases hi : i.val = 0
                      · exact h0 (Fin.ext hi)
                      · exact h1 (by apply Fin.ext; dsimp only [i1]; omega)
                    simp only [h0, h1, ↓reduceIte]
                    rw [← hv]
                    dsimp only [degAltMap]
                    simp only [hlt, ↓reduceIte]
                    by_cases hev : i.val % 2 = 0
                    · have hlt' : ¬ (i.val + 1 < 2) := by omega
                      have hev' : ¬ ((i.val + 1) % 2 = 0) := by omega
                      simp only [hev, ↓reduceDIte, hlt', ↓reduceIte, hev']
                      congr 1
                    · have hlt' : ¬ (i.val - 1 < 2) := by omega
                      have hev' : (i.val - 1) % 2 = 0 := by omega
                      simp only [hev, ↓reduceDIte, hlt', ↓reduceIte, hev']
                      congr 1; apply Fin.ext; dsimp only; omega
              right_inv := by
                intro ⟨a, b⟩
                have hne : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; dsimp only [i0, i1] at this; omega
                apply Prod.ext <;> simp [hne] }
          rw [← Fintype.card_coe fiberV, Fintype.card_congr efib, Fintype.card_prod, ZMod.card]
        calc (Finset.univ.filter (fun i : Fin n => degAltMap r heven (x i) = w)).card
            = ∑ v ∈ fiberV, ((Finset.univ.filter (fun i : Fin n => degAltMap r heven (x i) = w)).filter
                (fun i => x i = v)).card := by
              apply Finset.card_eq_sum_card_fiberwise
              intro i hi
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, fiberV, fw] at hi ⊢
              exact hi
          _ = ∑ v ∈ fiberV, (Finset.univ.filter (fun i : Fin n => x i = v)).card := by
              apply Finset.sum_congr rfl
              intro v hv
              congr 1
              ext i
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, fiberV, fw] at hv ⊢
              exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hv, h⟩⟩
          _ = ∑ _v ∈ fiberV, c := Finset.sum_congr rfl (fun v _ => hx v)
          _ = 4 * c := by rw [Finset.sum_const, hfibV_card, smul_eq_mul]
      · simp only [hw, ↓reduceIte]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hdeg
        apply hw
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hdeg]
        dsimp only [degAltMap, i0, i1]
        exact ⟨by simp, by simp⟩
    rw [hcard]
    dsimp only [n] at hdeg_fib hy_cnt
    simp_rw [hdeg_fib, hy_cnt]
    rw [← Finset.sum_add_sum_compl W]
    have hW_part : (∑ w ∈ W, min (if w ∈ W then 4 * c else 0) (cnt w)) = c * M + e := by
      calc (∑ w ∈ W, min (if w ∈ W then 4 * c else 0) (cnt w))
          = ∑ w ∈ W, cnt w := by
            apply Finset.sum_congr rfl
            intro w hw
            simp only [hw, ↓reduceIte]
            apply min_eq_right
            simp only [cnt, hw, ↓reduceDIte]
            have hle := hadd_le (enumW ⟨w, hw⟩)
            omega
        _ = c * M + e := hsum_W
    have hWc_part : (∑ w ∈ Wᶜ, min (if w ∈ W then 4 * c else 0) (cnt w)) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      have hnw : w ∉ W := Finset.mem_compl.mp hw
      simp only [hnw, ↓reduceIte, Nat.zero_min]
    rw [hW_part, hWc_part, add_zero, hdiv4]
  · rw [max_eq_left (le_of_not_ge hcase)]
    exact achieve_n_sub_e heven x hx y hy_def

end PEqualNP.Outside.L_meta_25745_aux

theorem PEqualNP.Outside.L_meta_25745 : (∀ (r c e : ℕ), 2 ≤ r → Even r →
  let V := Fin r → ZMod 2
  let n := c * 2^r
  4*e ≤ 3*n →
  ∀ x : Fin n → V,
    (∀ v : V, (Finset.univ.filter (fun i : Fin n => x i = v)).card = c) →
    let deficit := fun (y : Fin n → V) =>
      ∑ v : V, (c - (Finset.univ.filter (fun i : Fin n => y i = v)).card)
    let zeroBox := fun (y : Fin n → V) (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)) =>
      ∀ i ∈ K, ∀ j ∈ K, dotProduct (x i - x j) (y (π i) - y (π j)) = 0
    let upper := max (n-e) (n/4+e)
    (∀ y : Fin n → V, deficit y = e →
      (∃ (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)), zeroBox y π K ∧ K.card = n-e) ∧
      (∀ (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)), zeroBox y π K → K.card ≤ upper)) ∧
    (∃ (y : Fin n → V), deficit y = e ∧
      ∃ (π : Equiv.Perm (Fin n)) (K : Finset (Fin n)), zeroBox y π K ∧ K.card = upper)) := by
  intro r c e hr heven V n he x hx deficit zeroBox upper
  refine ⟨fun y hdef => ⟨?_, ?_⟩, ?_⟩
  · exact PEqualNP.Outside.L_meta_25745_aux.achieve_n_sub_e heven x hx y hdef
  · intro π K hbox
    exact PEqualNP.Outside.L_meta_25745_aux.upper_bound_proof hr heven he x hx y hdef π K hbox
  · exact PEqualNP.Outside.L_meta_25745_aux.sharpness_proof hr heven he x hx
