import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_lib_959
open Finset
def dlv (p q : Bool) : ℚ := if p = q then 0 else if q then 1 else -1
def dl {b : ℕ} (x : Fin (b+2) → Bool) (i : Fin (b+2)) : ℚ := dlv (x i) (x (i+1))
theorem dlv_ne_zero (p q : Bool) : dlv p q ≠ 0 ↔ p ≠ q := by
  cases p <;> cases q <;> simp [dlv]
theorem dlv_compl (p q : Bool) : dlv (!p) (!q) = - dlv p q := by
  cases p <;> cases q <;> simp [dlv]
theorem dlv_t1 (p q : Bool) (c : ℚ) (h : p ≠ q) :
    c * (-1) * (if q then 1 else -1) - c * (if p then 1 else -1) = 0 := by
  cases p <;> cases q <;> simp at h ⊢ <;> ring
theorem dlv_t2 (p q : Bool) (c : ℚ) :
    c * 1 * (if q then 1 else -1) - c * (if p then 1 else -1) = 2 * (c * dlv p q) := by
  cases p <;> cases q <;> simp [dlv] <;> ring
def dS {b : ℕ} (S : Finset (Fin (b+2))) (x : Fin (b+2) → Bool) : ℚ := ∏ i ∈ S, dl x i
def cnt {b : ℕ} (T : Finset (Fin (b+2))) (i : Fin (b+2)) : ℕ := (T.filter (fun t => t < i)).card
theorem cnt_succ {b : ℕ} (T : Finset (Fin (b+2))) (i : Fin (b+2)) (h : i ≠ Fin.last (b+1)) :
    cnt T (i+1) = cnt T i + if i ∈ T then 1 else 0 := by
  have hv : ((i+1 : Fin (b+2)) : ℕ) = (i : ℕ) + 1 :=
    Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr h)
  have e : T.filter (fun t => t < i+1) = (T.filter (fun t => t < i)) ∪ (T.filter (fun t => t = i)) := by
    ext t
    simp only [mem_filter, mem_union, Fin.lt_def, hv, Fin.ext_iff]
    by_cases ht : t ∈ T <;> simp [ht] <;> omega
  have d : Disjoint (T.filter (fun t => t < i)) (T.filter (fun t => t = i)) := by
    rw [disjoint_filter]
    intro t _ h1 h2
    rw [h2] at h1
    exact lt_irrefl _ h1
  unfold cnt
  rw [e, card_union_of_disjoint d, filter_eq']
  split_ifs <;> simp
theorem cnt_zero {b : ℕ} (T : Finset (Fin (b+2))) : cnt T 0 = 0 := by
  unfold cnt
  rw [card_eq_zero, filter_eq_empty_iff]
  intro t _ h
  exact Fin.not_lt_zero t h
theorem cnt_last {b : ℕ} (T : Finset (Fin (b+2))) :
    cnt T (Fin.last (b+1)) + (if Fin.last (b+1) ∈ T then 1 else 0) = T.card := by
  unfold cnt
  have e : T.filter (fun t => t < Fin.last (b+1)) = T.erase (Fin.last (b+1)) := by
    ext t; simp [Fin.lt_last_iff_ne_last, and_comm]
  rw [e]
  split_ifs with h
  · exact card_erase_add_one h
  · rw [erase_eq_of_notMem h]; simp
theorem exists_pt {b : ℕ} (D : Finset (Fin (b+2))) (hD : Even D.card) :
    ∃ x : Fin (b+2) → Bool, ∀ i, (x i ≠ x (i+1) ↔ i ∈ D) := by
  refine ⟨fun i => decide (Odd (cnt D i)), fun i => ?_⟩
  beta_reduce
  by_cases hi : i = Fin.last (b+1)
  · subst hi
    rw [Fin.last_add_one, cnt_zero]
    have h2 := cnt_last D
    by_cases hm : Fin.last (b+1) ∈ D
    · rw [if_pos hm] at h2
      have : Odd (cnt D (Fin.last (b+1))) := by
        rw [← h2] at hD
        exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hD)
      simp [this, hm]
    · rw [if_neg hm, add_zero] at h2
      have : ¬ Odd (cnt D (Fin.last (b+1))) := by
        rw [h2]; exact Nat.not_odd_iff_even.mpr hD
      simp [this, hm]
  · rw [cnt_succ D i hi]
    by_cases hm : i ∈ D
    · simp only [hm, ↓reduceIte, iff_true, Nat.odd_add_one]
      by_cases ho : Odd (cnt D i) <;> simp [ho]
    · simp [hm]
theorem dl_ne_zero {b : ℕ} (x : Fin (b+2) → Bool) (i : Fin (b+2)) : dl x i ≠ 0 ↔ x i ≠ x (i+1) :=
  dlv_ne_zero _ _
theorem dS_ne_zero {b : ℕ} (S : Finset (Fin (b+2))) (x : Fin (b+2) → Bool) :
    dS S x ≠ 0 ↔ ∀ i ∈ S, x i ≠ x (i+1) := by
  unfold dS; rw [prod_ne_zero_iff]; simp only [dl_ne_zero]
theorem dl_compl {b : ℕ} (x : Fin (b+2) → Bool) (i : Fin (b+2)) :
    dl (fun j => !x j) i = - dl x i :=
  dlv_compl _ _
theorem dS_compl {b : ℕ} (S : Finset (Fin (b+2))) (x : Fin (b+2) → Bool) :
    dS S (fun j => !x j) = (-1)^S.card * dS S x := by
  unfold dS
  rw [prod_congr rfl (fun i _ => dl_compl x i), prod_neg]
theorem dS_insert {b : ℕ} (T : Finset (Fin (b+2))) (i : Fin (b+2)) (hi : i ∉ T)
    (x : Fin (b+2) → Bool) : dS (insert i T) x = dl x i * dS T x := by
  unfold dS; rw [prod_insert hi]
theorem sgn_succ {b : ℕ} (T : Finset (Fin (b+2))) (hT : Even T.card) (i : Fin (b+2)) :
    ((-1:ℚ))^(cnt T (i+1)) = (-1)^(cnt T i) * (if i ∈ T then -1 else 1) := by
  by_cases hi : i = Fin.last (b+1)
  · subst hi
    rw [Fin.last_add_one, cnt_zero, pow_zero]
    have h2 := cnt_last T
    have h3 : ((-1:ℚ))^(cnt T (Fin.last (b+1)) + (if Fin.last (b+1) ∈ T then 1 else 0)) = 1 := by
      rw [h2]; exact hT.neg_one_pow
    rw [pow_add] at h3
    split_ifs at h3 ⊢ <;> simp only [pow_one, pow_zero, mul_one] at h3 ⊢ <;> linarith
  · rw [cnt_succ T i hi]; split_ifs <;> simp [pow_succ]
theorem tele {b : ℕ} (T : Finset (Fin (b+2))) (hT : Even T.card) (x : Fin (b+2) → Bool)
    (hx : ∀ t ∈ T, x t ≠ x (t+1)) :
    ∑ i ∈ univ \ T, ((-1:ℚ))^(cnt T i) * dl x i = 0 := by
  let u : Bool → ℚ := fun c => if c then 1 else -1
  let f : Fin (b+2) → ℚ := fun i => (-1)^(cnt T i) * u (x i)
  have h1 : ∑ i, (f (i+1) - f i) = 0 := by
    rw [sum_sub_distrib]
    have := Equiv.sum_comp (Equiv.addRight (1 : Fin (b+2))) f
    simp only [Equiv.coe_addRight] at this
    rw [this, sub_self]
  have h2 : ∀ i, f (i+1) - f i = if i ∈ T then 0 else 2 * ((-1)^(cnt T i) * dl x i) := by
    intro i
    simp only [f]
    rw [sgn_succ T hT i]
    by_cases hm : i ∈ T
    · have hne := hx i hm
      simp only [hm, ite_true]
      exact dlv_t1 _ _ _ hne
    · simp only [hm, ite_false]
      exact dlv_t2 _ _ _
  rw [sum_congr rfl (fun i _ => h2 i)] at h1
  rw [sum_ite, sum_const_zero, zero_add, ← mul_sum] at h1
  rw [sdiff_eq_filter]
  have h3 := (mul_eq_zero.mp h1).resolve_left two_ne_zero
  exact h3
theorem ident {b : ℕ} (T : Finset (Fin (b+2))) (hT : Even T.card) :
    ∑ i ∈ univ \ T, ((-1:ℚ))^(cnt T i) • dS (insert i T) = 0 := by
  funext x
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [sum_congr rfl (fun i hi => by rw [dS_insert T i (mem_sdiff.mp hi).2 x])]
  by_cases h : dS T x = 0
  · simp [h]
  · have hx := (dS_ne_zero T x).mp h
    simp_rw [← mul_assoc]
    rw [← sum_mul, tele T hT x hx, zero_mul]
theorem li_core {b : ℕ} (k : Fin (b+2)) (G : Finset (Fin (b+2)) → ℚ)
    (hG : ∀ S, ¬ Even S.card → k ∈ S → G S = 0)
    (h : ∀ x : Fin (b+2) → Bool, ∑ S, G S * dS S x = 0) : ∀ S, G S = 0 := by
  have hc : ∀ x, ∑ S, G S * ((-1)^S.card * dS S x) = 0 := fun x => by
    have := h (fun j => !x j); simpa only [dS_compl] using this
  have he : ∀ x, ∑ S, (if Even S.card then G S else 0) * dS S x = 0 := by
    intro x
    have e : ∀ S, (if Even S.card then G S else 0) * dS S x
        = (G S * dS S x + G S * ((-1)^S.card * dS S x)) / 2 := by
      intro S; split_ifs with hS
      · rw [hS.neg_one_pow]; ring
      · rw [(Nat.not_even_iff_odd.mp hS).neg_one_pow]; ring
    rw [sum_congr rfl (fun S _ => e S), ← sum_div, sum_add_distrib, h x, hc x]; simp
  have ho : ∀ x, ∑ S, (if Even S.card then 0 else G S) * dS S x = 0 := by
    intro x
    have e : ∀ S, (if Even S.card then 0 else G S) * dS S x
        = (G S * dS S x - G S * ((-1)^S.card * dS S x)) / 2 := by
      intro S; split_ifs with hS
      · rw [hS.neg_one_pow]; ring
      · rw [(Nat.not_even_iff_odd.mp hS).neg_one_pow]; ring
    rw [sum_congr rfl (fun S _ => e S), ← sum_div, sum_sub_distrib, h x, hc x]; simp
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hS : Even S.card
    · obtain ⟨x, hx⟩ := exists_pt S hS
      have hne : dS S x ≠ 0 := (dS_ne_zero S x).mpr (fun i hi => (hx i).mpr hi)
      have h1 := he x
      rw [sum_eq_single S] at h1
      · simp only [hS, ↓reduceIte] at h1
        exact (mul_eq_zero.mp h1).resolve_right hne
      · intro T _ hTS
        by_cases hT : dS T x = 0
        · simp [hT]
        · have hsub : T ⊆ S := fun i hi => (hx i).mp ((dS_ne_zero T x).mp hT i hi)
          simp [ih T (ssubset_of_subset_of_ne hsub hTS)]
      · simp
    · by_cases hkS : k ∈ S
      · exact hG S hS hkS
      · have hD : Even (insert k S).card := by
          rw [card_insert_of_notMem hkS]
          exact (Nat.not_even_iff_odd.mp hS).add_one
        obtain ⟨x, hx⟩ := exists_pt (insert k S) hD
        have hne : dS S x ≠ 0 :=
          (dS_ne_zero S x).mpr (fun i hi => (hx i).mpr (mem_insert_of_mem hi))
        have h1 := ho x
        rw [sum_eq_single S] at h1
        · simp only [hS, ↓reduceIte] at h1
          exact (mul_eq_zero.mp h1).resolve_right hne
        · intro T _ hTS
          by_cases hT : dS T x = 0
          · simp [hT]
          · by_cases hTe : Even T.card
            · simp [hTe]
            · have hsub : T ⊆ insert k S := fun i hi => (hx i).mp ((dS_ne_zero T x).mp hT i hi)
              by_cases hkT : k ∈ T
              · simp [hG T hTe hkT]
              · have hsub2 : T ⊆ S := by
                  intro i hi
                  rcases mem_insert.mp (hsub hi) with rfl | h2
                  · exact absurd hi hkT
                  · exact h2
                simp [ih T (ssubset_of_subset_of_ne hsub2 hTS)]
        · simp
theorem li_fam {b : ℕ} (k : Fin (b+2)) (F : Finset (Finset (Fin (b+2))))
    (hF : ∀ S ∈ F, ¬ Even S.card → k ∉ S) :
    LinearIndependent ℚ (fun S : F => (dS S.1 : (Fin (b+2) → Bool) → ℚ)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let G : Finset (Fin (b+2)) → ℚ := fun S => if h : S ∈ F then g ⟨S, h⟩ else 0
  have key : ∀ S, G S = 0 := by
    apply li_core k G
    · intro S hS hkS
      simp only [G]
      split_ifs with h
      · exact absurd hkS (hF S h hS)
      · rfl
    · intro x
      have h1 := congrFun hg x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
      have h2 : ∑ S : F, g S * dS S.1 x = ∑ S : F, G S.1 * dS S.1 x := by
        apply sum_congr rfl; intro S _; simp only [G, dif_pos S.2]
      rw [h2, sum_coe_sort F (fun S => G S * dS S x)] at h1
      rw [← h1]; symm
      apply sum_subset (subset_univ F)
      intro S _ hS; simp only [G, dif_neg hS, zero_mul]
  intro S
  have := key S.1
  simp only [G, dif_pos S.2] at this
  exact this
theorem count_full {b : ℕ} (k : Fin (b+2)) :
    (univ.filter (fun S : Finset (Fin (b+2)) => Even S.card ∨ k ∉ S)).card = 3 * 2^b := by
  have hk' : k + 1 ≠ k := by
    intro h
    have h1 : (1 : Fin (b+2)) = 0 := by
      have := congrArg (fun t => t - k) h; simpa using this
    exact absurd h1 (by simp)
  set k' := k + 1
  have e : univ.filter (fun S : Finset (Fin (b+2)) => Even S.card ∨ k ∉ S) =
      (univ.erase k).powerset ∪ univ.filter (fun S => k ∈ S ∧ Even S.card) := by
    ext S; simp [subset_erase]; tauto
  have d : Disjoint (univ.erase k).powerset
      (univ.filter (fun S : Finset (Fin (b+2)) => k ∈ S ∧ Even S.card)) := by
    rw [disjoint_left]; intro S h1 h2; simp [subset_erase] at h1 h2; exact h1 h2.1
  have c1 : (univ.erase k).powerset.card = 2^(b+1) := by
    rw [card_powerset, card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin]; rfl
  have c2 : (univ.filter (fun S : Finset (Fin (b+2)) => k ∈ S ∧ Even S.card)).card = 2^b := by
    have hc : ((univ.erase k).erase k').powerset.card = 2^b := by
      rw [card_powerset, card_erase_of_mem (by simp [k', hk']), card_erase_of_mem (mem_univ k),
        card_univ, Fintype.card_fin]; rfl
    rw [← hc]
    symm
    refine card_bij' (fun R _ => if Even R.card then insert k (insert k' R) else insert k R)
      (fun S _ => (S.erase k).erase k') ?_ ?_ ?_ ?_
    · intro R hR
      simp only [mem_powerset, subset_erase] at hR
      obtain ⟨⟨_, hkR⟩, hk'R⟩ := hR
      have hkk : k ∉ insert k' R := by
        rw [mem_insert]; push_neg; exact ⟨hk'.symm, hkR⟩
      split_ifs with he
      · simp only [mem_filter, mem_univ, true_and, mem_insert_self, true_and]
        rw [card_insert_of_notMem hkk, card_insert_of_notMem hk'R]
        rw [Nat.even_iff] at he ⊢; omega
      · simp only [mem_filter, mem_univ, true_and, mem_insert_self, true_and]
        rw [card_insert_of_notMem hkR]
        rw [Nat.even_iff] at he ⊢; omega
    · intro S _
      simp only [mem_powerset, subset_erase]
      refine ⟨⟨subset_univ _, ?_⟩, ?_⟩
      · intro h; exact (notMem_erase k S) (mem_of_mem_erase h)
      · exact notMem_erase k' _
    · intro R hR
      simp only [mem_powerset, subset_erase] at hR
      obtain ⟨⟨_, hkR⟩, hk'R⟩ := hR
      have hkk : k ∉ insert k' R := by
        rw [mem_insert]; push_neg; exact ⟨hk'.symm, hkR⟩
      split_ifs with he
      · rw [erase_insert hkk, erase_insert hk'R]
      · rw [erase_insert hkR, erase_eq_of_notMem hk'R]
    · intro S hS
      simp only [mem_filter, mem_univ, true_and] at hS
      obtain ⟨hkS, hSe⟩ := hS
      by_cases hk'S : k' ∈ S
      · have hk'S2 : k' ∈ S.erase k := mem_erase.mpr ⟨hk', hk'S⟩
        have hcard : ((S.erase k).erase k').card + 2 = S.card := by
          rw [card_erase_of_mem hk'S2, card_erase_of_mem hkS]
          have : 2 ≤ S.card := by
            have h3 : 1 ≤ (S.erase k).card := card_pos.mpr ⟨k', hk'S2⟩
            have h4 := card_erase_add_one hkS
            omega
          omega
        have he : Even ((S.erase k).erase k').card := by
          rw [Nat.even_iff] at hSe ⊢; omega
        simp only [he, ↓reduceIte]
        rw [insert_erase hk'S2, insert_erase hkS]
      · have h5 : (S.erase k).erase k' = S.erase k :=
          erase_eq_of_notMem (fun h => hk'S (mem_of_mem_erase h))
        have hcard := card_erase_add_one hkS
        have he : ¬ Even ((S.erase k).erase k').card := by
          rw [h5]; rw [Nat.even_iff] at hSe ⊢; omega
        simp only [he, ↓reduceIte]
        rw [h5, insert_erase hkS]
  rw [e, card_union_of_disjoint d, c1, c2]; ring
theorem span_full {b : ℕ} (k : Fin (b+2)) (S : Finset (Fin (b+2))) :
    dS S ∈ Submodule.span ℚ (Set.range (fun T : (univ.filter (fun S : Finset (Fin (b+2)) =>
      Even S.card ∨ k ∉ S)) => (dS T.1 : (Fin (b+2) → Bool) → ℚ))) := by
  have mem : ∀ T : Finset (Fin (b+2)), (Even T.card ∨ k ∉ T) →
      dS T ∈ Submodule.span ℚ (Set.range (fun T : (univ.filter (fun S : Finset (Fin (b+2)) =>
      Even S.card ∨ k ∉ S)) => (dS T.1 : (Fin (b+2) → Bool) → ℚ))) := by
    intro T hT
    exact Submodule.subset_span ⟨⟨T, by simp only [mem_filter, mem_univ, true_and]; exact hT⟩, rfl⟩
  by_cases hS : Even S.card ∨ k ∉ S
  · exact mem S hS
  · push_neg at hS
    obtain ⟨hSo, hkS⟩ := hS
    have hcard := card_erase_add_one hkS
    have hTe : Even (S.erase k).card := by
      rw [Nat.even_iff]; rw [Nat.odd_iff] at hSo; omega
    have hkT : k ∉ S.erase k := notMem_erase k S
    have hST : insert k (S.erase k) = S := insert_erase hkS
    have hid := ident (S.erase k) hTe
    rw [← add_sum_erase _ _ (mem_sdiff.mpr ⟨mem_univ k, hkT⟩)] at hid
    set w := ∑ i ∈ (univ \ S.erase k).erase k,
      ((-1:ℚ))^(cnt (S.erase k) i) • dS (insert i (S.erase k)) with hw
    have hmem : w ∈ Submodule.span ℚ (Set.range (fun T : (univ.filter (fun S : Finset (Fin (b+2)) =>
      Even S.card ∨ k ∉ S)) => (dS T.1 : (Fin (b+2) → Bool) → ℚ))) := by
      apply Submodule.sum_mem; intro i hi
      apply Submodule.smul_mem
      apply mem
      right
      have h6 := mem_erase.mp hi
      rw [mem_insert]; push_neg; exact ⟨h6.1.symm, hkT⟩
    set a := ((-1:ℚ))^(cnt (S.erase k) k) with ha
    have haa : a * a = 1 := by rw [ha, ← pow_add, ← two_mul, pow_mul]; simp
    have hv : dS S = (-a) • w := by
      have h7 : a • dS S = -w := by rw [← hST]; exact eq_neg_of_add_eq_zero_left hid
      calc dS S = (a * a) • dS S := by rw [haa, one_smul]
        _ = a • (a • dS S) := by rw [smul_smul]
        _ = (-a) • w := by rw [h7, smul_neg, neg_smul]
    rw [hv]; exact Submodule.smul_mem _ _ hmem
def Km {b : ℕ} (z : Fin (b+2) → ℚ) : Matrix (Fin (b+2) → Bool) (Fin (b+2) → Bool) ℚ := fun x y =>
  ∏ i : Fin (b+2), (z i)^((decide (x i ≠ y i)).toNat + (decide (x (i+1) = y i)).toNat)
def eta (c : Bool) : ℚ := if c then -1 else 1
def Hm (b : ℕ) : Matrix (Fin (b+2) → Bool) (Finset (Fin (b+2))) ℚ := fun y S => ∏ i ∈ S, eta (y i)
def Hi (b : ℕ) : Matrix (Finset (Fin (b+2))) (Fin (b+2) → Bool) ℚ :=
  fun S y => (∏ i ∈ S, eta (y i)) / 2^(b+2)
theorem eta_sq (p : Bool) : 1 + eta p * eta p = 2 := by cases p <;> norm_num [eta]
theorem eta_ne (p q : Bool) (h : p ≠ q) : 1 + eta p * eta q = 0 := by
  cases p <;> cases q <;> simp [eta] at h ⊢
theorem Hm_mul_Hi (b : ℕ) : Hm b * Hi b = 1 := by
  ext y y'
  simp only [Matrix.mul_apply, Hm, Hi, Matrix.one_apply]
  have e : ∑ S : Finset (Fin (b+2)), (∏ i ∈ S, eta (y i)) * ((∏ i ∈ S, eta (y' i)) / 2^(b+2))
      = (∏ i : Fin (b+2), (1 + eta (y i) * eta (y' i))) / 2^(b+2) := by
    rw [prod_one_add, powerset_univ, sum_div]
    apply sum_congr rfl; intro S _
    rw [prod_mul_distrib]; ring
  rw [e]
  split_ifs with h
  · subst h
    simp only [eta_sq, prod_const, card_univ, Fintype.card_fin]
    field_simp
  · have : ∃ i, y i ≠ y' i := by
      by_contra hc; push_neg at hc; exact h (funext hc)
    obtain ⟨i, hi⟩ := this
    rw [prod_eq_zero (mem_univ i) (eta_ne _ _ hi)]
    simp
def Hd {b : ℕ} (z : Fin (b+2) → ℚ) (x : Fin (b+2) → Bool) : ℚ :=
  ∏ i : Fin (b+2), (if x i = x (i+1) then 2 * z i else 1 + z i ^ 2)
def cc {b : ℕ} (z : Fin (b+2) → ℚ) (i : Fin (b+2)) : ℚ := (1 - z i ^ 2) / (1 + z i ^ 2)
def cS {b : ℕ} (z : Fin (b+2) → ℚ) (S : Finset (Fin (b+2))) : ℚ := ∏ i ∈ S, cc z i
def Ep {b : ℕ} (z : Fin (b+2) → ℚ) : Matrix (Fin (b+2) → Bool) (Finset (Fin (b+2))) ℚ :=
  fun x S => cS z S * dS S x
theorem factor (z : ℚ) (hz : 0 < z) (p q : Bool) (m : Prop) [Decidable m] :
    z ^ ((decide (p ≠ true)).toNat + (decide (q = true)).toNat) * (if m then eta true else 1) +
    z ^ ((decide (p ≠ false)).toNat + (decide (q = false)).toNat) * (if m then eta false else 1) =
    (if p = q then 2 * z else 1 + z^2) * (if m then (1 - z^2)/(1+z^2) * dlv p q else 1) := by
  have h1 : (1 + z^2) ≠ 0 := by positivity
  by_cases hm : m <;> cases p <;> cases q <;> simp [hm, eta, dlv] <;> field_simp <;> ring
theorem KH {b : ℕ} (z : Fin (b+2) → ℚ) (hz : ∀ i, 0 < z i) :
    Km z * Hm b = Matrix.diagonal (Hd z) * Ep z := by
  ext x S
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  let F : Fin (b+2) → Bool → ℚ := fun i c =>
    (z i)^((decide (x i ≠ c)).toNat + (decide (x (i+1) = c)).toNat) * (if i ∈ S then eta c else 1)
  have e1 : ∀ y : Fin (b+2) → Bool, Km z x y * Hm b y S = ∏ i, F i (y i) := by
    intro y
    simp only [Km, Hm, F]
    rw [prod_mul_distrib, Fintype.prod_ite_mem]
  have e2 : Hd z x * Ep z x S = ∏ i, (F i true + F i false) := by
    simp only [Hd, Ep, cS, dS, dl]
    rw [← prod_mul_distrib, ← Fintype.prod_ite_mem S, ← prod_mul_distrib]
    apply prod_congr rfl; intro i _
    exact (factor (z i) (hz i) (x i) (x (i+1)) (i ∈ S)).symm
  rw [sum_congr rfl (fun y _ => e1 y), e2, ← Fintype.prod_sum F]
  exact prod_congr rfl (fun i _ => Fintype.sum_bool _)
theorem rank_Km {b : ℕ} (z : Fin (b+2) → ℚ) (hz : ∀ i, 0 < z i) :
    (Km z).rank = (Ep z).rank := by
  have hdet : IsUnit (Matrix.diagonal (Hd z)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, prod_ne_zero_iff]
    intro x _
    simp only [Hd]
    rw [prod_ne_zero_iff]; intro i _
    have := hz i
    split_ifs <;> positivity
  have h1 : (Km z * Hm b).rank = (Ep z).rank := by
    rw [KH z hz, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hdet]
  apply le_antisymm
  · calc (Km z).rank = (Km z * Hm b * Hi b).rank := by rw [Matrix.mul_assoc, Hm_mul_Hi, Matrix.mul_one]
      _ ≤ (Km z * Hm b).rank := Matrix.rank_mul_le_left _ _
      _ = (Ep z).rank := h1
  · rw [← h1]; exact Matrix.rank_mul_le_left _ _
theorem range_Ep {b : ℕ} (z : Fin (b+2) → ℚ) :
    Set.range (Matrix.col (Ep z)) = Set.range (fun S => cS z S • (dS S : (Fin (b+2) → Bool) → ℚ)) := by
  congr 1
theorem cc_zero {b : ℕ} (z : Fin (b+2) → ℚ) (i : Fin (b+2)) (h : z i = 1) : cc z i = 0 := by
  simp [cc, h]
theorem cc_ne {b : ℕ} (z : Fin (b+2) → ℚ) (i : Fin (b+2)) (hz : 0 < z i) (h : z i ≠ 1) :
    cc z i ≠ 0 := by
  unfold cc
  apply div_ne_zero
  · intro h2
    have h4 : (z i - 1) * (z i + 1) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.mp h4 with h3 | h3
    · exact h (by linarith)
    · linarith
  · positivity
theorem fr_nonfull {b : ℕ} (z : Fin (b+2) → ℚ) (hz : ∀ i, 0 < z i) (k : Fin (b+2)) (hk : z k = 1) :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun S => cS z S • (dS S : (Fin (b+2) → Bool) → ℚ))))
      = 2 ^ (univ.filter (fun i => z i ≠ 1)).card := by
  set A := univ.filter (fun i => z i ≠ 1) with hA
  have hkA : k ∉ A := by simp [hA, hk]
  apply le_antisymm
  · calc Module.finrank ℚ (Submodule.span ℚ
          (Set.range (fun S => cS z S • (dS S : (Fin (b+2) → Bool) → ℚ))))
        ≤ Module.finrank ℚ (Submodule.span ℚ
          (Set.range (fun S : A.powerset => (dS S.1 : (Fin (b+2) → Bool) → ℚ)))) := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨S, rfl⟩
          by_cases hS : S ⊆ A
          · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨S, mem_powerset.mpr hS⟩, rfl⟩)
          · rw [not_subset] at hS
            obtain ⟨i, hiS, hiA⟩ := hS
            have h0 : cS z S = 0 := prod_eq_zero hiS (cc_zero z i (by simpa [hA] using hiA))
            simp only [h0, zero_smul]
            exact Submodule.zero_mem _
      _ ≤ Fintype.card A.powerset := finrank_range_le_card _
      _ = 2 ^ A.card := by rw [Fintype.card_coe, card_powerset]
  · calc 2 ^ A.card = Fintype.card A.powerset := by rw [Fintype.card_coe, card_powerset]
      _ = Module.finrank ℚ (Submodule.span ℚ
          (Set.range (fun S : A.powerset => (dS S.1 : (Fin (b+2) → Bool) → ℚ)))) :=
          (finrank_span_eq_card (li_fam k A.powerset
            (fun S hS _ hkS => hkA (mem_powerset.mp hS hkS)))).symm
      _ ≤ _ := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨⟨S, hS⟩, rfl⟩
          have hne : cS z S ≠ 0 := by
            apply prod_ne_zero_iff.mpr
            intro i hi
            have h5 := mem_powerset.mp hS hi
            exact cc_ne z i (hz i) (by simpa [hA] using h5)
          have h6 : (dS S : (Fin (b+2) → Bool) → ℚ) = (cS z S)⁻¹ • (cS z S • dS S) := by
            rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
          show (dS S : (Fin (b+2) → Bool) → ℚ) ∈ _
          rw [h6]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)
theorem fr_full {b : ℕ} (z : Fin (b+2) → ℚ) (hz : ∀ i, 0 < z i) (hA : ∀ i, z i ≠ 1) :
    Module.finrank ℚ (Submodule.span ℚ
      (Set.range (fun S => cS z S • (dS S : (Fin (b+2) → Bool) → ℚ)))) = 3 * 2 ^ b := by
  have hne : ∀ S, cS z S ≠ 0 := fun S => prod_ne_zero_iff.mpr (fun i _ => cc_ne z i (hz i) (hA i))
  set F := univ.filter (fun S : Finset (Fin (b+2)) => Even S.card ∨ (0 : Fin (b+2)) ∉ S) with hF
  apply le_antisymm
  · calc _ ≤ Module.finrank ℚ (Submodule.span ℚ
          (Set.range (fun S : F => (dS S.1 : (Fin (b+2) → Bool) → ℚ)))) := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨S, rfl⟩
          exact Submodule.smul_mem _ _ (span_full 0 S)
      _ ≤ Fintype.card F := finrank_range_le_card _
      _ = 3 * 2 ^ b := by rw [Fintype.card_coe, hF, count_full]
  · calc 3 * 2 ^ b = Fintype.card F := by rw [Fintype.card_coe, hF, count_full]
      _ = Module.finrank ℚ (Submodule.span ℚ
          (Set.range (fun S : F => (dS S.1 : (Fin (b+2) → Bool) → ℚ)))) := by
          refine (finrank_span_eq_card (li_fam 0 F ?_)).symm
          intro S hS h1
          simp only [hF, mem_filter, mem_univ, true_and] at hS
          tauto
      _ ≤ _ := by
          apply Submodule.finrank_mono
          rw [Submodule.span_le]
          rintro _ ⟨⟨S, _⟩, rfl⟩
          have h6 : (dS S : (Fin (b+2) → Bool) → ℚ) = (cS z S)⁻¹ • (cS z S • dS S) := by
            rw [smul_smul, inv_mul_cancel₀ (hne S), one_smul]
          show (dS S : (Fin (b+2) → Bool) → ℚ) ∈ _
          rw [h6]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S, rfl⟩)
end PEqualNP.Outside.L_lib_959
theorem PEqualNP.Outside.L_lib_959 : ∀ b : ℕ,
  let I := Fin (b+2)
  let X := I → Bool
  ∀ z : I → ℚ, (∀ i, 0 < z i) →
    let active := Finset.univ.filter (fun i : I => z i ≠ 1)
    let K : Matrix X X ℚ := fun x y =>
      ∏ i : I, (z i)^((decide (x i ≠ y i)).toNat + (decide (x (i+1) = y i)).toNat)
    K.rank = if active.card = b+2 then 3 * 2^b else 2^active.card := by
  intro b I X z hz active K
  show (PEqualNP.Outside.L_lib_959.Km z).rank =
    if (Finset.univ.filter (fun i : Fin (b+2) => z i ≠ 1)).card = b+2 then 3 * 2^b
    else 2^(Finset.univ.filter (fun i : Fin (b+2) => z i ≠ 1)).card
  rw [PEqualNP.Outside.L_lib_959.rank_Km z hz, Matrix.rank_eq_finrank_span_cols,
    PEqualNP.Outside.L_lib_959.range_Ep]
  split_ifs with h
  · apply PEqualNP.Outside.L_lib_959.fr_full z hz
    intro i hi
    have h2 : (Finset.univ.filter (fun i : Fin (b+2) => z i ≠ 1)) = Finset.univ := by
      apply Finset.eq_univ_of_card; rw [h, Fintype.card_fin]
    have h3 : i ∈ Finset.univ.filter (fun i : Fin (b+2) => z i ≠ 1) := by
      rw [h2]; exact Finset.mem_univ i
    exact (Finset.mem_filter.mp h3).2 hi
  · have h4 : ∃ k, z k = 1 := by
      by_contra hc
      push_neg at hc
      apply h
      have h2 : (Finset.univ.filter (fun i : Fin (b+2) => z i ≠ 1)) = Finset.univ := by
        ext i; simp [hc i]
      rw [h2, Finset.card_univ, Fintype.card_fin]
    obtain ⟨k, hk⟩ := h4
    exact PEqualNP.Outside.L_lib_959.fr_nonfull z hz k hk
