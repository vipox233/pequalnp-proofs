import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_pcx_319_aux

open scoped BigOperators

lemma pow_mul_choose_ge (N t : ℕ) (ht : t ≤ N) :
    N ^ t ≤ t ^ t * Nat.choose N t := by
  have hfac : 0 < t.factorial := Nat.factorial_pos t
  apply Nat.le_of_mul_le_mul_right _ hfac
  have h1 : N ^ t * t.factorial = ∏ i ∈ Finset.range t, (N * (t - i)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    clear ht hfac
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ']
      simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
      rw [← ih, Nat.factorial_succ, mul_comm]
  have hdesc : N.descFactorial t = ∏ i ∈ Finset.range t, (N - i) := by
    clear ht hfac h1
    induction t with
    | zero => simp
    | succ k ih =>
      rw [Nat.descFactorial_succ, Finset.prod_range_succ, ← ih, mul_comm]
  have h2 : t ^ t * Nat.choose N t * t.factorial = ∏ i ∈ Finset.range t, (t * (N - i)) := by
    rw [mul_assoc, mul_comm (Nat.choose N t), ← Nat.descFactorial_eq_factorial_mul_choose,
      hdesc, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h1, h2]
  apply Finset.prod_le_prod
  intro i hi
  have hi' : i < t := Finset.mem_range.mp hi
  have hle : i ≤ t := le_of_lt hi'
  have hleN : i ≤ N := le_trans hle ht
  zify [hle, hleN]
  nlinarith

lemma factorial_mul_choose_le_pow (M r : ℕ) :
    r.factorial * Nat.choose M r ≤ M ^ r := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow M r

lemma two_pow_pred_le_factorial : ∀ k : ℕ, 1 ≤ k → 2 ^ (k - 1) ≤ k.factorial := by
  intro k hk
  induction k with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero => simp
    | succ m' =>
      have hm : 1 ≤ m' + 1 := by omega
      have h1 := ih hm
      simp only [Nat.add_sub_cancel] at h1 ⊢
      rw [Nat.factorial_succ, pow_succ']
      have h2 : 2 ≤ m' + 2 := by omega
      exact Nat.mul_le_mul h2 h1

lemma succ_pow_le_three_mul_pow (r : ℕ) : (r + 1) ^ r ≤ 3 * r ^ r := by
  cases r with
  | zero => simp
  | succ m =>
    set r := m + 1
    have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
    apply Nat.le_of_mul_le_mul_left _ hpos
    rw [Nat.add_comm r 1, add_pow]
    simp only [one_pow, one_mul, Nat.cast_id]
    rw [Finset.mul_sum, Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.sub_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range r, 2 ^ r * (r ^ (r - (k + 1)) * Nat.choose r (k + 1)) ≤
        ∑ k ∈ Finset.range r, 2 ^ (r - k) * r ^ r := by
      apply Finset.sum_le_sum
      intro k hk
      have hkr : k < r := Finset.mem_range.mp hk
      have hfac := two_pow_pred_le_factorial (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hfac
      have hch := factorial_mul_choose_le_pow r (k + 1)
      have hstep : 2 ^ k * Nat.choose r (k + 1) ≤ r ^ (k + 1) :=
        le_trans (Nat.mul_le_mul_right _ hfac) hch
      have hpow2 : 2 ^ r = 2 ^ (r - k) * 2 ^ k := by
        rw [← pow_add, Nat.sub_add_cancel (le_of_lt hkr)]
      have hpowr : r ^ (r - (k + 1)) * r ^ (k + 1) = r ^ r := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]
      calc 2 ^ r * (r ^ (r - (k + 1)) * Nat.choose r (k + 1))
          = 2 ^ (r - k) * (r ^ (r - (k + 1)) * (2 ^ k * Nat.choose r (k + 1))) := by
            rw [hpow2]; ring
        _ ≤ 2 ^ (r - k) * (r ^ (r - (k + 1)) * r ^ (k + 1)) := by gcongr
        _ = 2 ^ (r - k) * r ^ r := by rw [hpowr]
    have hgeo : ∑ k ∈ Finset.range r, 2 ^ (r - k) ≤ 2 * 2 ^ r := by
      clear hsum hpos
      induction r with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ']
        simp only [Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
        have h1 : 2 * 2 ^ n = 2 ^ (n + 1) := by ring
        omega
    calc ∑ k ∈ Finset.range r, 2 ^ r * (r ^ (r - (k + 1)) * Nat.choose r (k + 1)) +
          2 ^ r * r ^ r
        ≤ ∑ k ∈ Finset.range r, 2 ^ (r - k) * r ^ r + 2 ^ r * r ^ r := by gcongr
      _ = (∑ k ∈ Finset.range r, 2 ^ (r - k)) * r ^ r + 2 ^ r * r ^ r := by
          rw [Finset.sum_mul]
      _ ≤ (2 * 2 ^ r) * r ^ r + 2 ^ r * r ^ r := by gcongr
      _ = 2 ^ r * (3 * r ^ r) := by ring

lemma three_pow_mul_factorial_ge_pow (r : ℕ) : r ^ r ≤ 3 ^ r * r.factorial := by
  induction r with
  | zero => simp
  | succ m ih =>
    have h1 := succ_pow_le_three_mul_pow m
    calc (m + 1) ^ (m + 1) = (m + 1) * (m + 1) ^ m := by rw [pow_succ']
      _ ≤ (m + 1) * (3 * m ^ m) := Nat.mul_le_mul_left _ h1
      _ ≤ (m + 1) * (3 * (3 ^ m * m.factorial)) := by gcongr
      _ = 3 ^ (m + 1) * (m + 1).factorial := by
          rw [pow_succ', Nat.factorial_succ]; ring

lemma choose_le_choose_succ (N k : ℕ) (hk : 2 * k + 1 ≤ N) :
    Nat.choose N k ≤ Nat.choose N (k + 1) := by
  have hf1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ N by omega)
  have hf2 := Nat.choose_mul_factorial_mul_factorial (show k + 1 ≤ N by omega)
  have hsub : N - k = (N - (k + 1)) + 1 := by omega
  have heq : (k + 1) * Nat.choose N (k + 1) * (k.factorial * (N - (k + 1)).factorial) =
      (N - k) * Nat.choose N k * (k.factorial * (N - (k + 1)).factorial) := by
    calc (k + 1) * Nat.choose N (k + 1) * (k.factorial * (N - (k + 1)).factorial)
        = Nat.choose N (k + 1) * (k + 1).factorial * (N - (k + 1)).factorial := by
          rw [Nat.factorial_succ]; ring
      _ = N.factorial := hf2
      _ = Nat.choose N k * k.factorial * (N - k).factorial := hf1.symm
      _ = (N - k) * Nat.choose N k * (k.factorial * (N - (k + 1)).factorial) := by
          rw [hsub, Nat.factorial_succ, ← hsub]; ring
  have hpos : 0 < k.factorial * (N - (k + 1)).factorial := by
    exact Nat.mul_pos (Nat.factorial_pos k) (Nat.factorial_pos (N - (k + 1)))
  have hmul : (k + 1) * Nat.choose N (k + 1) = (N - k) * Nat.choose N k :=
    Nat.eq_of_mul_eq_mul_right hpos heq
  have h1 : k + 1 ≤ N - k := by omega
  have h2 : (k + 1) * Nat.choose N k ≤ (k + 1) * Nat.choose N (k + 1) := by
    rw [hmul]; exact Nat.mul_le_mul_right _ h1
  exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos k)

lemma choose_mono_half (N t a : ℕ) (hta : t ≤ a) (ha : 2 * a ≤ N) :
    Nat.choose N t ≤ Nat.choose N a := by
  induction a with
  | zero =>
    have : t = 0 := by omega
    subst this; exact le_rfl
  | succ k ih =>
    by_cases htk : t ≤ k
    · exact le_trans (ih htk (by omega)) (choose_le_choose_succ N k (by omega))
    · have : t = k + 1 := by omega
      subst this; exact le_rfl

lemma choose_le_choose_of_mid (N t a : ℕ) (h1 : t ≤ a) (h2 : a + t ≤ N) :
    Nat.choose N t ≤ Nat.choose N a := by
  by_cases ha : 2 * a ≤ N
  · exact choose_mono_half N t a h1 ha
  · have hsym : Nat.choose N a = Nat.choose N (N - a) := by
      rw [Nat.choose_symm (by omega)]
    rw [hsym]
    exact choose_mono_half N t (N - a) (by omega) (by omega)


lemma card_filter_le_of_finset_sum {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) :
    (Finset.univ.filter (fun S : Finset α => S.card ≤ r)).card =
      ∑ k ∈ Finset.range (r + 1), Nat.choose (Fintype.card α) k := by
  have h : Finset.univ.filter (fun S : Finset α => S.card ≤ r) =
      (Finset.range (r + 1)).biUnion (fun k => Finset.powersetCard k (Finset.univ : Finset α)) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard, Finset.subset_univ]
    constructor
    · intro hS; exact ⟨S.card, by omega, rfl⟩
    · rintro ⟨k, hk, hcard⟩; omega
  rw [h, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro k _
    rw [Finset.card_powersetCard, Finset.card_univ]
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro S hi hj
    rw [Finset.mem_powersetCard] at hi hj
    exact hij (hi.2.symm.trans hj.2)

lemma sum_choose_le (M r : ℕ) (hr : 2 * r ≤ M) :
    ∑ k ∈ Finset.range (r + 1), Nat.choose M k ≤ (r + 1) * Nat.choose M r := by
  calc ∑ k ∈ Finset.range (r + 1), Nat.choose M k
      ≤ ∑ _k ∈ Finset.range (r + 1), Nat.choose M r := by
        apply Finset.sum_le_sum
        intro k hk
        exact choose_mono_half M k r (by have := Finset.mem_range.mp hk; omega) hr
    _ = (r + 1) * Nat.choose M r := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]


lemma card_perm_image_eq (N : ℕ) (S U : Finset (Fin N)) (hSU : S.card = U.card) :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card =
      S.card.factorial * (N - S.card).factorial := by
  classical
  let e1 : {p : Equiv.Perm (Fin N) // S.image p = U} ≃
      ({x : Fin N // x ∈ S} ≃ {x : Fin N // x ∈ U}) ×
      ({x : Fin N // x ∉ S} ≃ {x : Fin N // x ∉ U}) :=
    { toFun := fun ⟨p, hp⟩ =>
        (⟨fun x => ⟨p x.1, by rw [← hp]; exact Finset.mem_image_of_mem p x.2⟩,
          fun y => ⟨p.symm y.1, by
            have hy : y.1 ∈ S.image p := by rw [hp]; exact y.2
            rcases Finset.mem_image.mp hy with ⟨x, hx, hpx⟩
            have : p.symm y.1 = x := by rw [← hpx, p.symm_apply_apply]
            rwa [this]⟩,
          fun x => by ext; simp,
          fun y => by ext; simp⟩,
         ⟨fun x => ⟨p x.1, by
            intro hmem
            rw [← hp] at hmem
            rcases Finset.mem_image.mp hmem with ⟨z, hz, hpz⟩
            have : z = x.1 := p.injective hpz
            exact x.2 (this ▸ hz)⟩,
          fun y => ⟨p.symm y.1, by
            intro hmem
            have h1 : p (p.symm y.1) ∈ S.image p := Finset.mem_image_of_mem p hmem
            rw [hp, p.apply_symm_apply] at h1
            exact y.2 h1⟩,
          fun x => by ext; simp,
          fun y => by ext; simp⟩)
      invFun := fun ⟨f, g⟩ =>
        ⟨⟨fun x => if hx : x ∈ S then (f ⟨x, hx⟩).1 else (g ⟨x, hx⟩).1,
          fun y => if hy : y ∈ U then (f.symm ⟨y, hy⟩).1 else (g.symm ⟨y, hy⟩).1,
          fun x => by
            by_cases hx : x ∈ S
            · simp only [hx, ↓reduceDIte, (f ⟨x, hx⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply]
            · simp only [hx, ↓reduceDIte, (g ⟨x, hx⟩).2, Subtype.coe_eta, Equiv.symm_apply_apply],
          fun y => by
            by_cases hy : y ∈ U
            · simp only [hy, ↓reduceDIte, (f.symm ⟨y, hy⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply]
            · simp only [hy, ↓reduceDIte, (g.symm ⟨y, hy⟩).2, Subtype.coe_eta, Equiv.apply_symm_apply]⟩,
         by
           ext y
           simp only [Finset.mem_image, Equiv.coe_fn_mk]
           constructor
           · rintro ⟨x, hx, rfl⟩
             simp only [hx, ↓reduceDIte, (f ⟨x, hx⟩).2]
           · intro hy
             refine ⟨(f.symm ⟨y, hy⟩).1, (f.symm ⟨y, hy⟩).2, ?_⟩
             simp only [(f.symm ⟨y, hy⟩).2, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply]⟩
      left_inv := fun ⟨p, hp⟩ => by
        ext x
        by_cases hx : x ∈ S <;> simp [hx]
      right_inv := fun ⟨f, g⟩ => by
        ext x
        · simp [x.2]
        · simp [x.2] }
  have hc1 : (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card =
      Fintype.card {p : Equiv.Perm (Fin N) // S.image p = U} := by
    rw [Fintype.card_subtype]
  rw [hc1, Fintype.card_congr e1, Fintype.card_prod]
  have hS : Fintype.card {x : Fin N // x ∈ S} = S.card := Fintype.card_coe S
  have hU : Fintype.card {x : Fin N // x ∈ U} = U.card := Fintype.card_coe U
  have hSc : Fintype.card {x : Fin N // x ∉ S} = N - S.card := by
    have := Fintype.card_subtype_compl (fun x : Fin N => x ∈ S)
    rw [Fintype.card_fin, hS] at this
    exact this
  have hUc : Fintype.card {x : Fin N // x ∉ U} = N - U.card := by
    have := Fintype.card_subtype_compl (fun x : Fin N => x ∈ U)
    rw [Fintype.card_fin, hU] at this
    exact this
  have he1 : Fintype.card ({x : Fin N // x ∈ S} ≃ {x : Fin N // x ∈ U}) = S.card.factorial := by
    have eS : {x : Fin N // x ∈ S} ≃ Fin S.card := Fintype.equivFinOfCardEq hS
    have eU : {x : Fin N // x ∈ U} ≃ Fin S.card := Fintype.equivFinOfCardEq (hU.trans hSU.symm)
    rw [Fintype.card_congr (Equiv.equivCongr eS eU), Fintype.card_perm, Fintype.card_fin]
  have he2 : Fintype.card ({x : Fin N // x ∉ S} ≃ {x : Fin N // x ∉ U}) =
      (N - S.card).factorial := by
    have eSc : {x : Fin N // x ∉ S} ≃ Fin (N - S.card) := Fintype.equivFinOfCardEq hSc
    have eUc : {x : Fin N // x ∉ U} ≃ Fin (N - S.card) :=
      Fintype.equivFinOfCardEq (by rw [hUc, hSU])
    rw [Fintype.card_congr (Equiv.equivCongr eSc eUc), Fintype.card_perm, Fintype.card_fin]
  rw [he1, he2]

lemma card_perm_cross_le (N r : ℕ) (S T : Finset (Fin N)) (hr : 2 * r ≤ N) :
    (Finset.univ.filter (fun p : Equiv.Perm (Fin N) =>
      (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).card ≤ r)).card *
      Nat.choose N S.card ≤ N.factorial * ((r + 1) * Nat.choose N r) := by
  classical
  have hdiff : ∀ p : Equiv.Perm (Fin N),
      (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).card =
        (symmDiff (S.image p) T).card := by
    intro p
    have hbi : (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).image p =
        symmDiff (S.image p) T := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_symmDiff]
      constructor
      · rintro ⟨k, hk, rfl⟩
        by_cases h1 : k ∈ S
        · left
          refine ⟨⟨k, h1, rfl⟩, ?_⟩
          intro h2; exact hk (propext (iff_of_true h1 h2))
        · right
          have h2 : p k ∈ T := by
            by_contra h2; exact hk (propext (iff_of_false h1 h2))
          refine ⟨h2, ?_⟩
          rintro ⟨z, hz, hpz⟩
          exact h1 (p.injective hpz ▸ hz)
      · rintro (⟨⟨k, hk, rfl⟩, h2⟩ | ⟨h2, h1⟩)
        · exact ⟨k, fun h => h2 (by rw [← h]; exact hk), rfl⟩
        · refine ⟨p.symm y, ?_, p.apply_symm_apply y⟩
          intro h
          have : p.symm y ∈ S := by rw [h, p.apply_symm_apply]; exact h2
          exact h1 ⟨p.symm y, this, p.apply_symm_apply y⟩
    rw [← hbi, Finset.card_image_of_injective _ p.injective]
  let goodU : Finset (Finset (Fin N)) :=
    Finset.univ.filter (fun U : Finset (Fin N) => U.card = S.card ∧ (symmDiff U T).card ≤ r)
  have hpart : (Finset.univ.filter (fun p : Equiv.Perm (Fin N) =>
      (Finset.univ.filter (fun k : Fin N => (k ∈ S) ≠ (p k ∈ T))).card ≤ r)).card =
      ∑ U ∈ goodU, (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, goodU, hdiff]
      constructor
      · intro hp
        exact ⟨S.image p, ⟨Finset.card_image_of_injective S p.injective, hp⟩, rfl⟩
      · rintro ⟨U, ⟨_, hU⟩, rfl⟩
        exact hU
    · intro U1 _ U2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1 hp2
      exact hne (hp1.symm.trans hp2)
  have hsum : ∑ U ∈ goodU, (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card =
      goodU.card * (S.card.factorial * (N - S.card).factorial) := by
    calc ∑ U ∈ goodU, (Finset.univ.filter (fun p : Equiv.Perm (Fin N) => S.image p = U)).card
        = ∑ _U ∈ goodU, (S.card.factorial * (N - S.card).factorial) := by
          apply Finset.sum_congr rfl
          intro U hU
          simp only [goodU, Finset.mem_filter, Finset.mem_univ, true_and] at hU
          exact card_perm_image_eq N S U hU.1.symm
      _ = goodU.card * (S.card.factorial * (N - S.card).factorial) := by
          rw [Finset.sum_const, smul_eq_mul]
  have hgoodU : goodU.card ≤ (r + 1) * Nat.choose N r := by
    have hinj : Function.Injective (fun U : Finset (Fin N) => symmDiff U T) := by
      intro U1 U2 h
      have := congrArg (fun X => symmDiff X T) h
      simpa [symmDiff_symmDiff_cancel_right] using this
    have hsub : goodU.image (fun U => symmDiff U T) ⊆
        Finset.univ.filter (fun D : Finset (Fin N) => D.card ≤ r) := by
      intro D hD
      rcases Finset.mem_image.mp hD with ⟨U, hU, rfl⟩
      simp only [goodU, Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
      exact hU.2
    calc goodU.card = (goodU.image (fun U => symmDiff U T)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ (Finset.univ.filter (fun D : Finset (Fin N) => D.card ≤ r)).card :=
          Finset.card_le_card hsub
      _ = ∑ k ∈ Finset.range (r + 1), Nat.choose N k := by
          rw [card_filter_le_of_finset_sum, Fintype.card_fin]
      _ ≤ (r + 1) * Nat.choose N r := sum_choose_le N r hr
  have hS_le : S.card ≤ N := by
    simpa [Fintype.card_fin] using Finset.card_le_univ S
  have hfac : Nat.choose N S.card * (S.card.factorial * (N - S.card).factorial) = N.factorial := by
    rw [← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hS_le
  rw [hpart, hsum]
  calc goodU.card * (S.card.factorial * (N - S.card).factorial) * Nat.choose N S.card
      = goodU.card * (Nat.choose N S.card * (S.card.factorial * (N - S.card).factorial)) := by ring
    _ = goodU.card * N.factorial := by rw [hfac]
    _ ≤ ((r + 1) * Nat.choose N r) * N.factorial := Nat.mul_le_mul_right _ hgoodU
    _ = N.factorial * ((r + 1) * Nat.choose N r) := by ring


theorem p2_fixA_card {n : ℕ} (A : Finset (Fin n)) :
    (Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)).card = (n - A.card).factorial := by
  have h1 : (Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)).card
      = Fintype.card {f : Equiv.Perm (Fin n) // ∀ a, ¬ (a ∉ A) → f a = a} := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro ρ _
    simp only [not_not]
  rw [h1, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ∉ A)),
    Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
theorem p2_fix_le (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) =>
      k ≤ (Finset.univ.filter (fun i => ρ i = i)).card)).card * k.factorial ≤ n.factorial := by
  have hsub : Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) => k ≤ (Finset.univ.filter (fun i => ρ i = i)).card)
      ⊆ (Finset.powersetCard k (Finset.univ : Finset (Fin n))).biUnion
        (fun A => Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)) := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hρ.2
    rw [Finset.mem_biUnion]
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
    have := hA ha
    rw [Finset.mem_filter] at this
    exact this.2
  have h2 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h3 : ∑ A ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
      (Finset.univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)).card
      = n.choose k * (n - k).factorial := by
    rw [Finset.sum_congr rfl (fun A hA => by rw [p2_fixA_card, (Finset.mem_powersetCard.mp hA).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h3] at h2
  calc _ ≤ n.choose k * (n - k).factorial * k.factorial := Nat.mul_le_mul_right _ h2
    _ = n.factorial := by
      rw [mul_assoc, mul_comm (n-k).factorial, ← mul_assoc]
      exact Nat.choose_mul_factorial_mul_factorial hk

def Lmin (n : ℕ) : ℕ := (15 * n + 31) / 32

def Umax (n : ℕ) : ℕ := (17 * n) / 32

lemma central_iff (n D : ℕ) : 16 * Nat.dist (2 * D) n ≤ n ↔ Lmin n ≤ D ∧ D ≤ Umax n := by
  dsimp only [Lmin, Umax, Nat.dist]
  omega


def CrossSet {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (Bool × Fin n)) (j : Fin r) :
    Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))


lemma sum_sign_eq {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ∑ i ∈ s, (if P i then (1 : ℤ) else -1) = 2 * ((s.filter P).card : ℤ) - (s.card : ℤ) := by
  have h1 : ∑ i ∈ s, (if P i then (1 : ℤ) else -1) =
      ∑ i ∈ s, ((if P i then (2 : ℤ) else 0) - 1) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    by_cases h : P i <;> simp [h]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : ∑ i ∈ s, (if P i then (2 : ℤ) else 0) = 2 * ((s.filter P).card : ℤ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h2]

lemma exists_le_of_sum_le {α : Type*} [Fintype α] [Nonempty α] (f : α → ℤ) (C : ℤ)
    (h : ∑ a : α, f a ≤ C * (Fintype.card α : ℤ)) :
    ∃ a : α, f a ≤ C := by
  by_contra hcontra
  push Not at hcontra
  have hstep : ∀ a : α, C + 1 ≤ f a := fun a => Int.add_one_le_of_lt (hcontra a)
  have hsum : (Fintype.card α : ℤ) * (C + 1) ≤ ∑ a : α, f a := by
    calc (Fintype.card α : ℤ) * (C + 1)
        = ∑ _a : α, (C + 1) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ a : α, f a := Finset.sum_le_sum (fun a _ => hstep a)
  have hpos : (0 : ℤ) < (Fintype.card α : ℤ) := Int.natCast_pos.mpr Fintype.card_pos
  nlinarith

lemma bool_not_ne_iff (a b : Bool) : ((!a) ≠ b) ↔ ¬ (a ≠ b) := by
  cases a <;> cases b <;> decide

lemma exists_pinned_base (n r : ℕ) (h8192 : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hcoinc : ∀ j l : Fin r, j ≠ l →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (j0 : Fin r) (A : Finset (Fin n)) (hA : 128 * A.card ≤ n)
    (d_target : ℕ) (hd : d_target ≤ n - A.card) :
    let UA : Finset (Bool × Fin n) :=
      A.image (fun i => (false, i)) ∪ A.image (fun i => (true, M j0 i))
    ∃ w0 : (Bool × Fin n) → Bool,
      ((Finset.univ \ A).filter (fun i : Fin n => w0 (false, i) ≠ w0 (true, M j0 i))).card = d_target ∧
      ∀ (w : (Bool × Fin n) → Bool), (∀ v, v ∉ UA → w v = w0 v) →
        ∀ j : Fin r, j ≠ j0 →
          16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => w (false, i) ≠ w (true, M j i))).card) n ≤ n := by
  classical
  intro UA
  let B : Finset (Fin n) := Finset.univ \ A
  have hBA_disj : Disjoint B A := Finset.sdiff_disjoint
  have hBA_union : B ∪ A = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ A)
  have hBA_card : B.card + A.card = n := by
    have h := Finset.card_union_of_disjoint hBA_disj
    rw [hBA_union, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hdB : d_target ≤ B.card := by omega
  obtain ⟨P, hPB, hPcard⟩ := Finset.exists_subset_card_eq hdB
  let ws : (B → Bool) → (Bool × Fin n) → Bool := fun s v =>
    match v with
    | (false, i) => if hi : i ∈ B then s ⟨i, hi⟩ else false
    | (true, b) =>
        let i := (M j0).symm b
        if hi : i ∈ B then xor (s ⟨i, hi⟩) (decide (i ∈ P)) else false
  have hws_j0 : ∀ s : B → Bool,
      (B.filter (fun i : Fin n => ws s (false, i) ≠ ws s (true, M j0 i))).card = d_target := by
    intro s
    have hfeq : B.filter (fun i : Fin n => ws s (false, i) ≠ ws s (true, M j0 i)) = P := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hiB, hne⟩
        dsimp only [ws] at hne
        rw [dite_eq_left hiB, (M j0).symm_apply_apply, dite_eq_left hiB] at hne
        by_contra hiP
        simp [hiP] at hne
      · intro hiP
        have hiB : i ∈ B := hPB hiP
        refine ⟨hiB, ?_⟩
        dsimp only [ws]
        rw [dite_eq_left hiB, (M j0).symm_apply_apply, dite_eq_left hiB]
        simp [hiP]
    rw [hfeq, hPcard]
  let Gj : Fin r → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun i : Fin n => i ∈ B ∧ (M j0).symm (M j i) ∈ B ∧ M j i ≠ M j0 i)
  let Badj : Fin r → Finset (Fin n) := fun j => Finset.univ \ Gj j
  have hBad_bound : ∀ j : Fin r, j ≠ j0 → 128 * (Badj j).card ≤ 3 * n := by
    intro j hj
    have hsub : Badj j ⊆
        A ∪ A.image (fun t => (M j).symm (M j0 t)) ∪
          Finset.univ.filter (fun i : Fin n => M j i = M j0 i) := by
      intro i hi
      simp only [Badj, Gj, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and,
        not_and] at hi
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hiB : i ∈ B
      · by_cases hiB2 : (M j0).symm (M j i) ∈ B
        · right
          have hne := hi hiB hiB2
          exact not_not.mp hne
        · left
          right
          refine ⟨(M j0).symm (M j i), ?_, ?_⟩
          · simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hiB2
            exact hiB2
          · rw [(M j0).apply_symm_apply, (M j).symm_apply_apply]
      · left
        left
        simp only [B, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hiB
        exact hiB
    have h1 : (Badj j).card ≤
        (A ∪ A.image (fun t => (M j).symm (M j0 t)) ∪
          Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := Finset.card_le_card hsub
    have h2 : (A ∪ A.image (fun t => (M j).symm (M j0 t)) ∪
        Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card ≤
        A.card + (A.image (fun t => (M j).symm (M j0 t))).card +
        (Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := by
      calc _ ≤ (A ∪ A.image (fun t => (M j).symm (M j0 t))).card +
              (Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := Finset.card_union_le _ _
        _ ≤ A.card + (A.image (fun t => (M j).symm (M j0 t))).card +
              (Finset.univ.filter (fun i : Fin n => M j i = M j0 i)).card := by
            have := Finset.card_union_le A (A.image (fun t => (M j).symm (M j0 t)))
            omega
    have h3 : (A.image (fun t => (M j).symm (M j0 t))).card ≤ A.card := Finset.card_image_le
    have h4 := hcoinc j j0 hj
    omega
  let eta : Fin r → Fin n → (B → Bool) → ℤ := fun j i s =>
    if ws s (false, i) ≠ ws s (true, M j i) then 1 else -1
  have hortho : ∀ j : Fin r, ∀ i1 ∈ Gj j, ∀ i2 ∈ Gj j,
      i2 ≠ i1 → i2 ≠ (M j0).symm (M j i1) →
      ∑ s : B → Bool, eta j i1 s * eta j i2 s = 0 := by
    intro j i1 hi1 i2 hi2 hne1 hne2
    simp only [Gj, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rcases hi1 with ⟨hi1B, hi1'B, _⟩
    rcases hi2 with ⟨hi2B, hi2'B, hi2ne⟩
    let b2 : B := ⟨i2, hi2B⟩
    let flip2 : (B → Bool) ≃ (B → Bool) :=
      { toFun := fun s => Function.update s b2 (!(s b2))
        invFun := fun s => Function.update s b2 (!(s b2))
        left_inv := fun s => by
          funext x
          by_cases hx : x = b2
          · subst hx; simp
          · simp [Function.update, hx]
        right_inv := fun s => by
          funext x
          by_cases hx : x = b2
          · subst hx; simp
          · simp [Function.update, hx] }
    have hi2'ne : (M j0).symm (M j i2) ≠ i2 := by
      intro heq
      apply hi2ne
      have h := congrArg (M j0) heq
      simpa using h
    have hterm : ∀ s : B → Bool, eta j i1 (flip2 s) * eta j i2 (flip2 s) = -(eta j i1 s * eta j i2 s) := by
      intro s
      have he1 : eta j i1 (flip2 s) = eta j i1 s := by
        have hf1 : ws (flip2 s) (false, i1) = ws s (false, i1) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi1B, dite_eq_left hi1B]
          have hnb : (⟨i1, hi1B⟩ : B) ≠ b2 := fun h => hne1 (congrArg Subtype.val h).symm
          simp [Function.update, hnb]
        have ht1 : ws (flip2 s) (true, M j i1) = ws s (true, M j i1) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi1'B, dite_eq_left hi1'B]
          have hnb : (⟨(M j0).symm (M j i1), hi1'B⟩ : B) ≠ b2 :=
            fun h => hne2 (congrArg Subtype.val h).symm
          simp [Function.update, hnb]
        dsimp only [eta]
        rw [hf1, ht1]
      have he2 : eta j i2 (flip2 s) = -(eta j i2 s) := by
        have hf2 : ws (flip2 s) (false, i2) = !(ws s (false, i2)) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi2B, dite_eq_left hi2B]
          simp [b2]
        have ht2 : ws (flip2 s) (true, M j i2) = ws s (true, M j i2) := by
          dsimp only [ws, flip2]
          rw [dite_eq_left hi2'B, dite_eq_left hi2'B]
          have hnb : (⟨(M j0).symm (M j i2), hi2'B⟩ : B) ≠ b2 :=
            fun h => hi2'ne (congrArg Subtype.val h)
          simp [Function.update, hnb]
        dsimp only [eta]
        rw [hf2, ht2]
        cases ws s (false, i2) <;> cases ws s (true, M j i2) <;> rfl
      rw [he1, he2]
      ring
    have hsum_eq : ∑ s : B → Bool, eta j i1 s * eta j i2 s =
        ∑ s : B → Bool, eta j i1 (flip2 s) * eta j i2 (flip2 s) :=
      (Fintype.sum_equiv flip2 (fun s => eta j i1 (flip2 s) * eta j i2 (flip2 s))
        (fun s => eta j i1 s * eta j i2 s) (fun _ => rfl)).symm
    have hneg : ∑ s : B → Bool, eta j i1 s * eta j i2 s =
        -(∑ s : B → Bool, eta j i1 s * eta j i2 s) := by
      calc ∑ s : B → Bool, eta j i1 s * eta j i2 s
          = ∑ s : B → Bool, eta j i1 (flip2 s) * eta j i2 (flip2 s) := hsum_eq
        _ = ∑ s : B → Bool, -(eta j i1 s * eta j i2 s) := Finset.sum_congr rfl (fun s _ => hterm s)
        _ = -(∑ s : B → Bool, eta j i1 s * eta j i2 s) := by rw [Finset.sum_neg_distrib]
    omega
  have hj_bound : ∀ j : Fin r,
      ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2 ≤ (2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ) := by
    intro j
    have hexp : ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2 =
        ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s := by
      calc ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2
          = ∑ s : B → Bool, ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, eta j i1 s * eta j i2 s := by
            refine Finset.sum_congr rfl ?_
            intro s _
            rw [sq, Finset.sum_mul_sum]
        _ = ∑ i1 ∈ Gj j, ∑ s : B → Bool, ∑ i2 ∈ Gj j, eta j i1 s * eta j i2 s := Finset.sum_comm
        _ = ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s := by
            refine Finset.sum_congr rfl ?_
            intro i1 _
            exact Finset.sum_comm
    rw [hexp]
    have hinner : ∀ i1 ∈ Gj j,
        ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s ≤ 2 * (Fintype.card (B → Bool) : ℤ) := by
      intro i1 hi1
      let T : Finset (Fin n) := {i1, (M j0).symm (M j i1)}
      have hfilt : ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s =
          ∑ i2 ∈ (Gj j).filter (fun i2 => i2 ∈ T), ∑ s : B → Bool, eta j i1 s * eta j i2 s := by
        symm
        refine Finset.sum_filter_of_ne ?_
        intro i2 hi2 hne
        by_contra hnotT
        simp only [T, Finset.mem_insert, Finset.mem_singleton, not_or] at hnotT
        exact hne (hortho j i1 hi1 i2 hi2 hnotT.1 hnotT.2)
      rw [hfilt]
      have hterm_le : ∀ i2 : Fin n,
          ∑ s : B → Bool, eta j i1 s * eta j i2 s ≤ (Fintype.card (B → Bool) : ℤ) := by
        intro i2
        calc ∑ s : B → Bool, eta j i1 s * eta j i2 s
            ≤ ∑ _s : B → Bool, (1 : ℤ) := by
              refine Finset.sum_le_sum ?_
              intro s _
              dsimp only [eta]
              split_ifs <;> omega
          _ = (Fintype.card (B → Bool) : ℤ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hTcard : ((Gj j).filter (fun i2 => i2 ∈ T)).card ≤ 2 := by
        have hsubT : (Gj j).filter (fun i2 => i2 ∈ T) ⊆ T := by
          intro x hx
          exact (Finset.mem_filter.mp hx).2
        calc ((Gj j).filter (fun i2 => i2 ∈ T)).card
            ≤ T.card := Finset.card_le_card hsubT
          _ ≤ 2 := by
              dsimp only [T]
              exact le_trans (Finset.card_insert_le _ _) (by simp)
      calc ∑ i2 ∈ (Gj j).filter (fun i2 => i2 ∈ T), ∑ s : B → Bool, eta j i1 s * eta j i2 s
          ≤ ∑ _i2 ∈ (Gj j).filter (fun i2 => i2 ∈ T), (Fintype.card (B → Bool) : ℤ) :=
            Finset.sum_le_sum (fun i2 _ => hterm_le i2)
        _ = (((Gj j).filter (fun i2 => i2 ∈ T)).card : ℤ) * (Fintype.card (B → Bool) : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (Fintype.card (B → Bool) : ℤ) := by
            have hTcardZ : (((Gj j).filter (fun i2 => i2 ∈ T)).card : ℤ) ≤ 2 := by exact_mod_cast hTcard
            have hnonneg : (0 : ℤ) ≤ (Fintype.card (B → Bool) : ℤ) := Int.natCast_nonneg _
            nlinarith
    have hGcard : ((Gj j).card : ℤ) ≤ (n : ℤ) := by
      have h : (Gj j).card ≤ n := by
        simpa [Fintype.card_fin] using Finset.card_le_univ (Gj j)
      exact_mod_cast h
    have hnonneg : (0 : ℤ) ≤ (Fintype.card (B → Bool) : ℤ) := Int.natCast_nonneg _
    calc ∑ i1 ∈ Gj j, ∑ i2 ∈ Gj j, ∑ s : B → Bool, eta j i1 s * eta j i2 s
        ≤ ∑ _i1 ∈ Gj j, (2 * (Fintype.card (B → Bool) : ℤ)) :=
          Finset.sum_le_sum (fun i1 hi1 => hinner i1 hi1)
      _ = ((Gj j).card : ℤ) * (2 * (Fintype.card (B → Bool) : ℤ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℤ) * (2 * (Fintype.card (B → Bool) : ℤ)) := by nlinarith
      _ = (2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ) := by ring
  have htotal : ∑ s : B → Bool, ∑ j ∈ Finset.univ.erase j0, (∑ i ∈ Gj j, eta j i s) ^ 2 ≤
      (2 * (r : ℤ) * (n : ℤ)) * (Fintype.card (B → Bool) : ℤ) := by
    rw [Finset.sum_comm]
    have herase : ((Finset.univ.erase j0).card : ℤ) ≤ (r : ℤ) := by
      have h : (Finset.univ.erase j0).card ≤ r := by
        calc (Finset.univ.erase j0).card ≤ (Finset.univ : Finset (Fin r)).card :=
              Finset.card_le_card (Finset.erase_subset _ _)
          _ = r := by simp
      exact_mod_cast h
    have hnonneg : (0 : ℤ) ≤ (2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ) := by positivity
    calc ∑ j ∈ Finset.univ.erase j0, ∑ s : B → Bool, (∑ i ∈ Gj j, eta j i s) ^ 2
        ≤ ∑ _j ∈ Finset.univ.erase j0, ((2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ)) :=
          Finset.sum_le_sum (fun j _ => hj_bound j)
      _ = ((Finset.univ.erase j0).card : ℤ) * ((2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (r : ℤ) * ((2 * n : ℤ) * (Fintype.card (B → Bool) : ℤ)) := by nlinarith
      _ = (2 * (r : ℤ) * (n : ℤ)) * (Fintype.card (B → Bool) : ℤ) := by ring
  obtain ⟨s0, hs0⟩ := exists_le_of_sum_le
    (fun s : B → Bool => ∑ j ∈ Finset.univ.erase j0, (∑ i ∈ Gj j, eta j i s) ^ 2)
    (2 * (r : ℤ) * (n : ℤ)) htotal
  refine ⟨ws s0, hws_j0 s0, ?_⟩
  intro w hw j hj
  have hsq_le : (∑ i ∈ Gj j, eta j i s0) ^ 2 ≤ 2 * (r : ℤ) * (n : ℤ) := by
    have hmem : j ∈ Finset.univ.erase j0 := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    exact le_trans
      (Finset.single_le_sum (fun k _ => sq_nonneg (∑ i ∈ Gj k, eta k i s0)) hmem) hs0
  have h8192Z : 8192 * (r : ℤ) < (n : ℤ) := by exact_mod_cast h8192
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  have h32X : -(n : ℤ) ≤ 32 * (∑ i ∈ Gj j, eta j i s0) ∧
      32 * (∑ i ∈ Gj j, eta j i s0) ≤ (n : ℤ) := by
    have hsq32 : (32 * (∑ i ∈ Gj j, eta j i s0)) ^ 2 ≤ (n : ℤ) ^ 2 := by nlinarith
    constructor <;> nlinarith
  have hwG : ∀ i ∈ Gj j, w (false, i) = ws s0 (false, i) ∧ w (true, M j i) = ws s0 (true, M j i) := by
    intro i hi
    simp only [Gj, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hnf : (false, i) ∉ UA := by
      intro hmem
      simp only [UA, Finset.mem_union, Finset.mem_image] at hmem
      rcases hmem with ⟨a, ha, heq⟩ | ⟨a, _, heq⟩
      · have : a = i := (Prod.mk.inj heq).2
        subst this
        exact (Finset.mem_sdiff.mp hi.1).2 ha
      · exact Bool.false_ne_true (Prod.mk.inj heq).1.symm
    have hnt : (true, M j i) ∉ UA := by
      intro hmem
      simp only [UA, Finset.mem_union, Finset.mem_image] at hmem
      rcases hmem with ⟨a, _, heq⟩ | ⟨a, ha, heq⟩
      · exact Bool.false_ne_true (Prod.mk.inj heq).1
      · have hMeq : M j0 a = M j i := (Prod.mk.inj heq).2
        have hsymm : (M j0).symm (M j i) = a := by
          rw [← hMeq, (M j0).symm_apply_apply]
        have hnotA := (Finset.mem_sdiff.mp hi.2.1).2
        rw [hsymm] at hnotA
        exact hnotA ha
    exact ⟨hw (false, i) hnf, hw (true, M j i) hnt⟩
  let P : Fin n → Prop := fun i => w (false, i) ≠ w (true, M j i)
  have hG_Bad_disj : Disjoint (Gj j) (Badj j) := Finset.disjoint_sdiff
  have hG_Bad_union : Gj j ∪ Badj j = Finset.univ := by
    rw [Finset.union_comm]
    exact Finset.sdiff_union_of_subset (Finset.subset_univ (Gj j))
  have hcard_GB : (Gj j).card + (Badj j).card = n := by
    have h := Finset.card_union_of_disjoint hG_Bad_disj
    rw [hG_Bad_union, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hDsplit : (Finset.univ.filter P).card = ((Gj j).filter P).card + ((Badj j).filter P).card := by
    conv_lhs => rw [← hG_Bad_union]
    rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hG_Bad_disj)]
  have hDG_eq : ((Gj j).filter P).card =
      ((Gj j).filter (fun i => ws s0 (false, i) ≠ ws s0 (true, M j i))).card := by
    congr 1
    refine Finset.filter_congr ?_
    intro i hi
    rcases hwG i hi with ⟨hf, ht⟩
    simp [P, hf, ht]
  have hsign : ∑ i ∈ Gj j, eta j i s0 = 2 * (((Gj j).filter P).card : ℤ) - ((Gj j).card : ℤ) := by
    rw [hDG_eq]
    exact sum_sign_eq (Gj j) (fun i => ws s0 (false, i) ≠ ws s0 (true, M j i))
  have hDBad_le : ((Badj j).filter P).card ≤ (Badj j).card := Finset.card_filter_le _ _
  have hBad3 : 128 * (Badj j).card ≤ 3 * n := hBad_bound j hj
  rw [hsign] at h32X
  change 16 * Nat.dist (2 * (Finset.univ.filter P).card) n ≤ n
  dsimp only [Nat.dist]
  omega



def shiftPerm (n : ℕ) (hn : 0 < n) : Equiv.Perm (Fin n) :=
  { toFun := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩
    invFun := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn⟩
    left_inv := fun i => by
      apply Fin.ext; dsimp only
      by_cases h : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt h]
        have h1 : i.val + 1 + n - 1 = i.val + n := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      · have hi : i.val + 1 = n := by omega
        rw [hi, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
        omega
    right_inv := fun i => by
      apply Fin.ext; dsimp only
      by_cases h : i.val = 0
      · rw [h, zero_add]
        have hmod : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        have h1 : n - 1 + 1 = n := by omega
        rw [h1, Nat.mod_self]
      · have h1 : i.val + n - 1 = (i.val - 1) + n := by omega
        rw [h1, Nat.add_mod_right]
        have hmod : (i.val - 1) % n = i.val - 1 := Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        have h2 : i.val - 1 + 1 = i.val := by omega
        rw [h2, Nat.mod_eq_of_lt i.isLt] }

lemma shiftPerm_ne (n : ℕ) (hn : 2 ≤ n) (i : Fin n) :
    shiftPerm n (by omega) i ≠ i := by
  intro h
  have hv : (i.val + 1) % n = i.val := congrArg Fin.val h
  by_cases hlt : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have hi : i.val + 1 = n := by omega
    rw [hi, Nat.mod_self] at hv; omega

lemma choose_le_pow_of_ratio (M d B : ℕ) (hd : 1 ≤ d) (hM : 3 * M ≤ B * d) :
    Nat.choose M d ≤ B ^ d := by
  have hdpos : 0 < d ^ d := pow_pos (by omega) d
  apply Nat.le_of_mul_le_mul_left _ hdpos
  calc d ^ d * Nat.choose M d
      ≤ (3 ^ d * d.factorial) * Nat.choose M d :=
        Nat.mul_le_mul_right _ (three_pow_mul_factorial_ge_pow d)
    _ = 3 ^ d * (d.factorial * Nat.choose M d) := by ring
    _ ≤ 3 ^ d * M ^ d := Nat.mul_le_mul_left _ (factorial_mul_choose_le_pow M d)
    _ = (3 * M) ^ d := by rw [mul_pow]
    _ ≤ (B * d) ^ d := Nat.pow_le_pow_left hM d
    _ = d ^ d * B ^ d := by rw [mul_pow, mul_comm]

lemma two_pow_le_choose_fifth (n : ℕ) (hn : 5 ≤ n) :
    2 ^ (2 * (n / 5)) ≤ Nat.choose n (n / 5) := by
  set t := n / 5
  have htpos : 0 < t ^ t := pow_pos (by omega) t
  have h5 : 5 ^ t ≤ Nat.choose n t := by
    apply Nat.le_of_mul_le_mul_left _ htpos
    calc t ^ t * 5 ^ t = (5 * t) ^ t := by rw [mul_pow, mul_comm]
      _ ≤ n ^ t := Nat.pow_le_pow_left (by omega) t
      _ ≤ t ^ t * Nat.choose n t := pow_mul_choose_ge n t (by omega)
  calc 2 ^ (2 * t) = (2 ^ 2) ^ t := by rw [pow_mul]
    _ = 4 ^ t := by norm_num
    _ ≤ 5 ^ t := Nat.pow_le_pow_left (by omega) t
    _ ≤ Nat.choose n t := h5

lemma main_binom_ineq (n : ℕ) (hn : 262144 ≤ n) :
    let r := 3 * (n / 65536)
    10 * (2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) * ((r + 1) * Nat.choose n r)) <
      Nat.choose n (n / 5) := by
  intro r
  have hr12 : 12 ≤ r := by dsimp only [r]; omega
  have h3n : 3 * n ≤ 2 ^ 17 * r := by dsimp only [r]; omega
  have h3_2n : 3 * (2 * n) ≤ 2 ^ 17 * (2 * r) := by omega
  have hc1 : Nat.choose n r ≤ 2 ^ (17 * r) := by
    rw [pow_mul]
    exact choose_le_pow_of_ratio n r (2 ^ 17) (by omega) h3n
  have hc2 : Nat.choose (2 * n) (2 * r) ≤ 2 ^ (34 * r) := by
    have hpow : (2 ^ 17) ^ (2 * r) = 2 ^ (34 * r) := by rw [← pow_mul]; congr 1; ring
    rw [← hpow]
    exact choose_le_pow_of_ratio (2 * n) (2 * r) (2 ^ 17) (by omega) h3_2n
  have hr2 : r ≤ 2 ^ r := le_of_lt Nat.lt_two_pow_self
  have hpoly : 10 * 2 * (2 * r + 1) * (r + 1) ≤ 2 ^ (3 * r) := by
    have h1 : 10 * 2 * (2 * r + 1) * (r + 1) ≤ 2 ^ 7 * r ^ 2 := by nlinarith
    have h2 : r ^ 2 ≤ (2 ^ r) ^ 2 := Nat.pow_le_pow_left hr2 2
    have h3 : 2 ^ 7 * (2 ^ r) ^ 2 = 2 ^ (2 * r + 7) := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    have h4 : 2 ^ (2 * r + 7) ≤ 2 ^ (3 * r) := Nat.pow_le_pow_right (by omega) (by omega)
    calc 10 * 2 * (2 * r + 1) * (r + 1) ≤ 2 ^ 7 * r ^ 2 := h1
      _ ≤ 2 ^ 7 * (2 ^ r) ^ 2 := Nat.mul_le_mul_left _ h2
      _ = 2 ^ (2 * r + 7) := h3
      _ ≤ 2 ^ (3 * r) := h4
  have hexp : 54 * r < 2 * (n / 5) := by dsimp only [r]; omega
  have hlt : 2 ^ (54 * r) < 2 ^ (2 * (n / 5)) := Nat.pow_lt_pow_right (by omega) hexp
  have hlow := two_pow_le_choose_fifth n (by omega)
  calc 10 * (2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) * ((r + 1) * Nat.choose n r))
      = (10 * 2 * (2 * r + 1) * (r + 1)) * Nat.choose (2 * n) (2 * r) * Nat.choose n r := by ring
    _ ≤ 2 ^ (3 * r) * 2 ^ (34 * r) * 2 ^ (17 * r) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hpoly hc2) hc1
    _ = 2 ^ (54 * r) := by rw [← pow_add, ← pow_add]; congr 1; ring
    _ < 2 ^ (2 * (n / 5)) := hlt
    _ ≤ Nat.choose n (n / 5) := hlow

lemma goodCuts_card_le (n r : ℕ) (hn : 1 ≤ n) (hr : 2 * r ≤ n) :
    (Finset.univ.filter (fun S : Finset (Bool × Fin n) =>
      (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, i) ∈ S))).card ≤ r ∧
      (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, shiftPerm n (by omega) i) ∈ S))).card ≤ r)).card
    ≤ 2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) := by
  classical
  let sp := shiftPerm n (by omega)
  let cyc : Finset (Bool × Fin n) → Fin (2 * n) → Bool := fun S m =>
    if m.val % 2 = 0 then decide ((true, ⟨m.val / 2, by omega⟩) ∈ S)
    else decide ((false, ⟨m.val / 2, by omega⟩) ∈ S)
  let bdry : Finset (Bool × Fin n) → Finset (Fin (2 * n)) := fun S =>
    Finset.univ.filter (fun m : Fin (2 * n) =>
      cyc S m ≠ cyc S ⟨(m.val + 1) % (2 * n), Nat.mod_lt _ (by omega)⟩)
  let phi : Finset (Bool × Fin n) → Bool × Finset (Fin (2 * n)) := fun S =>
    (cyc S ⟨0, by omega⟩, bdry S)
  have hphi_inj : Function.Injective phi := by
    intro S1 S2 hEq
    have h0 : cyc S1 ⟨0, by omega⟩ = cyc S2 ⟨0, by omega⟩ := congrArg Prod.fst hEq
    have hb : bdry S1 = bdry S2 := congrArg Prod.snd hEq
    have hcyc : ∀ k : ℕ, (hk : k < 2 * n) → cyc S1 ⟨k, hk⟩ = cyc S2 ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro _; exact h0
      | succ k ih =>
        intro hk
        have hk' : k < 2 * n := by omega
        have hprev := ih hk'
        have hmem : (⟨k, hk'⟩ : Fin (2 * n)) ∈ bdry S1 ↔ (⟨k, hk'⟩ : Fin (2 * n)) ∈ bdry S2 := by
          rw [hb]
        simp only [bdry, Finset.mem_filter, Finset.mem_univ, true_and,
          Nat.mod_eq_of_lt hk] at hmem
        cases h1 : cyc S1 ⟨k, hk'⟩ <;> cases h2 : cyc S2 ⟨k, hk'⟩ <;>
          cases h3 : cyc S1 ⟨k + 1, hk⟩ <;> cases h4 : cyc S2 ⟨k + 1, hk⟩ <;>
          simp_all
    ext ⟨b, i⟩
    cases b
    · have hm : 2 * i.val + 1 < 2 * n := by omega
      have h := hcyc (2 * i.val + 1) hm
      have hmod : (2 * i.val + 1) % 2 = 1 := by omega
      have hdiv : (2 * i.val + 1) / 2 = i.val := by omega
      simp only [cyc, hmod, hdiv, Fin.eta] at h
      simpa using h
    · have hm : 2 * i.val < 2 * n := by omega
      have h := hcyc (2 * i.val) hm
      have hmod : (2 * i.val) % 2 = 0 := by omega
      have hdiv : (2 * i.val) / 2 = i.val := by omega
      simp only [cyc, hmod, hdiv, Fin.eta] at h
      simpa using h
  let GC := Finset.univ.filter (fun S : Finset (Bool × Fin n) =>
    (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, i) ∈ S))).card ≤ r ∧
    (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, sp i) ∈ S))).card ≤ r)
  have hbdry_le : ∀ S ∈ GC, (bdry S).card ≤ 2 * r := by
    intro S hS
    rcases (Finset.mem_filter.mp hS).2 with ⟨hc0, hc1⟩
    have hsplit : (bdry S).card =
        ((bdry S).filter (fun m : Fin (2 * n) => m.val % 2 = 0)).card +
        ((bdry S).filter (fun m : Fin (2 * n) => ¬(m.val % 2 = 0))).card :=
      (Finset.card_filter_add_card_filter_not (s := bdry S) (fun m : Fin (2 * n) => m.val % 2 = 0)).symm
    have heven : ((bdry S).filter (fun m : Fin (2 * n) => m.val % 2 = 0)).card ≤ r := by
      refine le_trans ?_ hc0
      refine Finset.card_le_card_of_injOn (fun m => (⟨m.val / 2, by omega⟩ : Fin n)) ?_ ?_
      · intro m hm
        simp only [Finset.mem_coe, bdry, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        rcases hm with ⟨hne, hev⟩
        have hlt : m.val + 1 < 2 * n := by omega
        have hmod1 : (m.val + 1) % (2 * n) = m.val + 1 := Nat.mod_eq_of_lt hlt
        have hodd : (m.val + 1) % 2 = 1 := by omega
        have hdiv : (m.val + 1) / 2 = m.val / 2 := by omega
        simp only [cyc, hev, ↓reduceIte, hmod1, hodd, hdiv] at hne
        intro hiff
        exact hne (by simp [hiff])
      · intro m1 hm1 m2 hm2 hEq
        have hev1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hm1)).2
        have hev2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hm2)).2
        have hv : m1.val / 2 = m2.val / 2 := congrArg Fin.val hEq
        exact Fin.ext (by omega)
    have hodd_le : ((bdry S).filter (fun m : Fin (2 * n) => ¬(m.val % 2 = 0))).card ≤ r := by
      refine le_trans ?_ hc1
      refine Finset.card_le_card_of_injOn (fun m => (⟨m.val / 2, by omega⟩ : Fin n)) ?_ ?_
      · intro m hm
        simp only [Finset.mem_coe, bdry, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
        rcases hm with ⟨hne, hodd⟩
        have hmod0 : ((m.val + 1) % (2 * n)) % 2 = 0 := by
          by_cases hlt : m.val + 1 < 2 * n
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have hm_eq : m.val + 1 = 2 * n := by omega
            rw [hm_eq, Nat.mod_self]
        have hdiv1 : ((m.val + 1) % (2 * n)) / 2 = (m.val / 2 + 1) % n := by
          by_cases hlt : m.val + 1 < 2 * n
          · rw [Nat.mod_eq_of_lt hlt]
            have hlt2 : m.val / 2 + 1 < n := by omega
            rw [Nat.mod_eq_of_lt hlt2]; omega
          · have hm_eq : m.val + 1 = 2 * n := by omega
            have hd : m.val / 2 + 1 = n := by omega
            rw [hm_eq, Nat.mod_self, hd, Nat.mod_self]
        simp only [cyc, hodd, ↓reduceIte, hmod0, hdiv1] at hne
        intro hiff
        apply hne
        have hsp : sp ⟨m.val / 2, by omega⟩ = ⟨(m.val / 2 + 1) % n, Nat.mod_lt _ (by omega)⟩ := rfl
        rw [hsp] at hiff
        simp [hiff]
      · intro m1 hm1 m2 hm2 hEq
        have hodd1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hm1)).2
        have hodd2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hm2)).2
        have hv : m1.val / 2 = m2.val / 2 := congrArg Fin.val hEq
        exact Fin.ext (by omega)
    omega
  let T : Finset (Bool × Finset (Fin (2 * n))) :=
    (Finset.univ : Finset Bool) ×ˢ (Finset.univ.filter (fun B : Finset (Fin (2 * n)) => B.card ≤ 2 * r))
  have hsub : GC.image phi ⊆ T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨S, hS, rfl⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbdry_le S hS⟩⟩
  calc GC.card = (GC.image phi).card := (Finset.card_image_of_injective _ hphi_inj).symm
    _ ≤ T.card := Finset.card_le_card hsub
    _ = 2 * (Finset.univ.filter (fun B : Finset (Fin (2 * n)) => B.card ≤ 2 * r)).card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    _ = 2 * ∑ k ∈ Finset.range (2 * r + 1), Nat.choose (2 * n) k := by
        rw [card_filter_le_of_finset_sum, Fintype.card_fin]
    _ ≤ 2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) :=
        Nat.mul_le_mul_left 2 (sum_choose_le (2 * n) (2 * r) (by omega))

lemma cut_false_balance (n r : ℕ) (hn : 20 * r ≤ n) (S : Finset (Bool × Fin n))
    (hlo : n ≤ 2 * S.card) (hhi : 2 * S.card ≤ 3 * n)
    (hc0 : (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, i) ∈ S))).card ≤ r) :
    let A := Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)
    n / 5 ≤ A.card ∧ A.card + n / 5 ≤ n := by
  classical
  intro A
  let B := Finset.univ.filter (fun i : Fin n => (true, i) ∈ S)
  have hS_eq : S.card = A.card + B.card := by
    have hsplit : S = S.filter (fun v : Bool × Fin n => v.1 = false) ∪
        S.filter (fun v : Bool × Fin n => v.1 = true) := by
      ext ⟨b, i⟩; cases b <;> simp
    have hdisj : Disjoint (S.filter (fun v : Bool × Fin n => v.1 = false))
        (S.filter (fun v : Bool × Fin n => v.1 = true)) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      rw [h1'] at h2'; exact Bool.false_ne_true h2'
    have hA : (S.filter (fun v : Bool × Fin n => v.1 = false)).card = A.card := by
      refine Finset.card_bij (fun v _ => v.2) ?_ ?_ ?_
      · intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvS, hvf⟩
        rcases v with ⟨b, i⟩; dsimp only at hvf; subst hvf
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS⟩
      · intro v1 hv1 v2 hv2 heq
        have h1 := (Finset.mem_filter.mp hv1).2
        have h2 := (Finset.mem_filter.mp hv2).2
        exact Prod.ext (h1.trans h2.symm) heq
      · intro i hi
        exact ⟨(false, i), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩, rfl⟩
    have hB : (S.filter (fun v : Bool × Fin n => v.1 = true)).card = B.card := by
      refine Finset.card_bij (fun v _ => v.2) ?_ ?_ ?_
      · intro v hv
        rcases Finset.mem_filter.mp hv with ⟨hvS, hvt⟩
        rcases v with ⟨b, i⟩; dsimp only at hvt; subst hvt
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvS⟩
      · intro v1 hv1 v2 hv2 heq
        have h1 := (Finset.mem_filter.mp hv1).2
        have h2 := (Finset.mem_filter.mp hv2).2
        exact Prod.ext (h1.trans h2.symm) heq
      · intro i hi
        exact ⟨(true, i), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩, rfl⟩
    conv_lhs => rw [hsplit]
    rw [Finset.card_union_of_disjoint hdisj, hA, hB]
  have hsd : symmDiff A B = Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, i) ∈ S)) := by
    ext i
    simp only [A, B, Finset.mem_symmDiff, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hAB : (A \ B).card + (B \ A).card ≤ r := by
    have hdisj : Disjoint (A \ B) (B \ A) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_sdiff.mp h2).1
    have hu : (A \ B) ∪ (B \ A) = symmDiff A B := rfl
    rw [← Finset.card_union_of_disjoint hdisj, hu, hsd]
    exact hc0
  have hA_split : A.card = (A ∩ B).card + (A \ B).card :=
    (Finset.card_inter_add_card_sdiff A B).symm
  have hB_split : B.card = (A ∩ B).card + (B \ A).card := by
    rw [Finset.inter_comm]
    exact (Finset.card_inter_add_card_sdiff B A).symm
  omega

lemma exists_good_M (n : ℕ) (hn : 262144 ≤ n) :
    ∃ M : Fin 3 → Equiv.Perm (Fin n),
      (∀ j l : Fin 3, j ≠ l →
        128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) ∧
      (∀ S : Finset (Bool × Fin n), n ≤ 2 * S.card → 2 * S.card ≤ 3 * n →
        ∃ j0 : Fin 3, 3 * (n / 65536) ≤ (CrossSet M S j0).card) := by
  classical
  let sp := shiftPerm n (by omega)
  let r := 3 * (n / 65536)
  let Bad0 : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun p => n < 128 * (Finset.univ.filter (fun i : Fin n => p i = i)).card)
  let Bad1 : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun p => n < 128 * (Finset.univ.filter (fun i : Fin n => p i = sp i)).card)
  let GC : Finset (Finset (Bool × Fin n)) :=
    Finset.univ.filter (fun S : Finset (Bool × Fin n) =>
      n ≤ 2 * S.card ∧ 2 * S.card ≤ 3 * n ∧
      (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, i) ∈ S))).card ≤ r ∧
      (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, sp i) ∈ S))).card ≤ r)
  let BadS : Finset (Bool × Fin n) → Finset (Equiv.Perm (Fin n)) := fun S =>
    Finset.univ.filter (fun p =>
      (Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, p i) ∈ S))).card ≤ r)
  let BadCut : Finset (Equiv.Perm (Fin n)) := GC.biUnion BadS
  have hBad0 : 10 * Bad0.card ≤ n.factorial := by
    let k := n / 128 + 1
    have hsub : Bad0 ⊆ Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
        k ≤ (Finset.univ.filter (fun i : Fin n => p i = i)).card) := by
      intro p hp
      simp only [Bad0, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      dsimp only [k]; omega
    have hle := Finset.card_le_card hsub
    have hfix := p2_fix_le n k (by dsimp only [k]; omega)
    have hk4 : 4 ≤ k := by dsimp only [k]; omega
    have hfac : 10 ≤ k.factorial := by
      have h1 : (4 : ℕ).factorial ≤ k.factorial := Nat.factorial_le hk4
      have h2 : (4 : ℕ).factorial = 24 := by decide
      omega
    calc 10 * Bad0.card ≤ k.factorial * Bad0.card := Nat.mul_le_mul_right _ hfac
      _ = Bad0.card * k.factorial := by ring
      _ ≤ (Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
            k ≤ (Finset.univ.filter (fun i : Fin n => p i = i)).card)).card * k.factorial :=
          Nat.mul_le_mul_right _ hle
      _ ≤ n.factorial := hfix
  have hBad1 : 10 * Bad1.card ≤ n.factorial := by
    have hle : Bad1.card ≤ Bad0.card := by
      refine Finset.card_le_card_of_injOn (fun p => p.trans sp.symm) ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe, Bad0, Bad1, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        have hfeq : Finset.univ.filter (fun i : Fin n => (p.trans sp.symm) i = i) =
            Finset.univ.filter (fun i : Fin n => p i = sp i) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            have h' : sp.symm (p i) = i := h
            have := congrArg sp h'
            simpa using this
          · intro h
            show sp.symm (p i) = i
            rw [h, Equiv.symm_apply_apply]
        rw [hfeq]; exact hp
      · intro p1 _ p2 _ h
        apply Equiv.ext
        intro i
        have := congrArg (fun q : Equiv.Perm (Fin n) => sp (q i)) h
        simpa [Equiv.trans_apply] using this
    exact le_trans (Nat.mul_le_mul_left 10 hle) hBad0
  have hBadCut : 10 * BadCut.card < n.factorial := by
    have hGC_card : GC.card ≤ 2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) := by
      refine le_trans (Finset.card_le_card ?_) (goodCuts_card_le n r (by omega) (by dsimp only [r]; omega))
      intro S hS
      simp only [GC, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      exact ⟨hS.2.2.1, hS.2.2.2⟩
    have hperS : ∀ S ∈ GC,
        (BadS S).card * Nat.choose n (n / 5) ≤ n.factorial * ((r + 1) * Nat.choose n r) := by
      intro S hS
      rcases (Finset.mem_filter.mp hS).2 with ⟨hlo, hhi, hc0, _⟩
      let AS := Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)
      let BS := Finset.univ.filter (fun i : Fin n => (true, i) ∈ S)
      have hbal := cut_false_balance n r (by dsimp only [r]; omega) S hlo hhi hc0
      have hch_mid : Nat.choose n (n / 5) ≤ Nat.choose n AS.card :=
        choose_le_choose_of_mid n (n / 5) AS.card hbal.1 hbal.2
      have hcross := card_perm_cross_le n r AS BS (by dsimp only [r]; omega)
      have hBadS_eq : BadS S = Finset.univ.filter (fun p : Equiv.Perm (Fin n) =>
          (Finset.univ.filter (fun i : Fin n => (i ∈ AS) ≠ (p i ∈ BS))).card ≤ r) := by
        ext p
        simp only [BadS, Finset.mem_filter, Finset.mem_univ, true_and]
        have hfc : Finset.univ.filter (fun i : Fin n => ¬((false, i) ∈ S ↔ (true, p i) ∈ S)) =
            Finset.univ.filter (fun i : Fin n => (i ∈ AS) ≠ (p i ∈ BS)) := by
          ext i
          simp only [AS, BS, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, eq_iff_iff]
        rw [hfc]
      rw [hBadS_eq]
      exact le_trans (Nat.mul_le_mul_left _ hch_mid) hcross
    have hsum : BadCut.card * Nat.choose n (n / 5) ≤
        GC.card * (n.factorial * ((r + 1) * Nat.choose n r)) := by
      calc BadCut.card * Nat.choose n (n / 5)
          ≤ (∑ S ∈ GC, (BadS S).card) * Nat.choose n (n / 5) :=
            Nat.mul_le_mul_right _ Finset.card_biUnion_le
        _ = ∑ S ∈ GC, (BadS S).card * Nat.choose n (n / 5) := Finset.sum_mul ..
        _ ≤ ∑ _S ∈ GC, (n.factorial * ((r + 1) * Nat.choose n r)) :=
            Finset.sum_le_sum hperS
        _ = GC.card * (n.factorial * ((r + 1) * Nat.choose n r)) := by
            rw [Finset.sum_const, smul_eq_mul]
    have hineq := main_binom_ineq n hn
    have hch_pos : 0 < Nat.choose n (n / 5) := Nat.choose_pos (by omega)
    have hfac_pos : 0 < n.factorial := Nat.factorial_pos n
    have hprod : 10 * BadCut.card * Nat.choose n (n / 5) < n.factorial * Nat.choose n (n / 5) := by
      calc 10 * BadCut.card * Nat.choose n (n / 5)
          = 10 * (BadCut.card * Nat.choose n (n / 5)) := by ring
        _ ≤ 10 * (GC.card * (n.factorial * ((r + 1) * Nat.choose n r))) :=
            Nat.mul_le_mul_left 10 hsum
        _ ≤ 10 * (2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) *
              (n.factorial * ((r + 1) * Nat.choose n r))) :=
            Nat.mul_le_mul_left 10 (Nat.mul_le_mul_right _ hGC_card)
        _ = n.factorial * (10 * (2 * ((2 * r + 1) * Nat.choose (2 * n) (2 * r)) *
              ((r + 1) * Nat.choose n r))) := by ring
        _ < n.factorial * Nat.choose n (n / 5) := Nat.mul_lt_mul_of_pos_left hineq hfac_pos
    exact Nat.lt_of_mul_lt_mul_right hprod
  have hunion : (Bad0 ∪ Bad1 ∪ BadCut).card < (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
    have hle : (Bad0 ∪ Bad1 ∪ BadCut).card ≤ Bad0.card + Bad1.card + BadCut.card :=
      le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hcard_univ : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    rw [hcard_univ]
    have hfac_pos : 0 < n.factorial := Nat.factorial_pos n
    omega
  obtain ⟨p, _, hp_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hunion
  have hp0 : p ∉ Bad0 := fun h => hp_not (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hp1 : p ∉ Bad1 := fun h => hp_not (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hpC : p ∉ BadCut := fun h => hp_not (Finset.mem_union_right _ h)
  let M : Fin 3 → Equiv.Perm (Fin n) := fun j =>
    match j with
    | ⟨0, _⟩ => Equiv.refl (Fin n)
    | ⟨1, _⟩ => sp
    | ⟨2, _⟩ => p
  refine ⟨M, ?_, ?_⟩
  · intro j l hjl
    have h01 : (Finset.univ.filter (fun i : Fin n => Equiv.refl (Fin n) i = sp i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      exact shiftPerm_ne n (by omega) i h.symm
    have h10 : (Finset.univ.filter (fun i : Fin n => sp i = Equiv.refl (Fin n) i)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      exact shiftPerm_ne n (by omega) i h
    have hp0' : 128 * (Finset.univ.filter (fun i : Fin n => p i = i)).card ≤ n := by
      simp only [Bad0, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp0
      exact hp0
    have hp1' : 128 * (Finset.univ.filter (fun i : Fin n => p i = sp i)).card ≤ n := by
      simp only [Bad1, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hp1
      exact hp1
    have hsym : ∀ f g : Fin n → Fin n,
        (Finset.univ.filter (fun i : Fin n => f i = g i)).card =
        (Finset.univ.filter (fun i : Fin n => g i = f i)).card := by
      intro f g; congr 1; ext i; simp [eq_comm]
    fin_cases j <;> fin_cases l
    · exact absurd rfl hjl
    · dsimp only [M]; rw [h01]; omega
    · dsimp only [M]; rw [hsym]; exact hp0'
    · dsimp only [M]; rw [h10]; omega
    · exact absurd rfl hjl
    · dsimp only [M]; rw [hsym]; exact hp1'
    · dsimp only [M]; exact hp0'
    · dsimp only [M]; exact hp1'
    · exact absurd rfl hjl
  · intro S hlo hhi
    by_contra hall
    push Not at hall
    have h0 : (CrossSet M S 0).card < r := hall 0
    have h1 : (CrossSet M S 1).card < r := hall 1
    have h2 : (CrossSet M S 2).card < r := hall 2
    have hSGC : S ∈ GC := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlo, hhi, ?_, ?_⟩
      · exact le_of_lt h0
      · exact le_of_lt h1
    have hpBadS : p ∈ BadS S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_lt h2⟩
    exact hpC (Finset.mem_biUnion.mpr ⟨S, hSGC, hpBadS⟩)

def slotLabel {q : ℕ} (r : Fin q) (c : Fin 3) (inS : Bool) : Bool ⊕ (Fin q × Bool) :=
  match c, inS with
  | ⟨0, _⟩, true  => Sum.inr (r, false)
  | ⟨0, _⟩, false => Sum.inr (r, true)
  | ⟨1, _⟩, true  => Sum.inr (r, false)
  | ⟨1, _⟩, false => Sum.inl false
  | ⟨2, _⟩, true  => Sum.inl false
  | ⟨2, _⟩, false => Sum.inr (r, false)

lemma slot_triple_sum (a b : Bool) :
    (if ((slotLabel (q := 1) 0 0 true).elim id (fun p => xor p.2 a) ≠
         (slotLabel (q := 1) 0 0 false).elim id (fun p => xor p.2 b)) then 1 else 0) +
    (if ((slotLabel (q := 1) 0 1 true).elim id (fun p => xor p.2 a) ≠
         (slotLabel (q := 1) 0 1 false).elim id (fun p => xor p.2 b)) then 1 else 0) +
    (if ((slotLabel (q := 1) 0 2 true).elim id (fun p => xor p.2 a) ≠
         (slotLabel (q := 1) 0 2 false).elim id (fun p => xor p.2 b)) then 1 else 0) =
    1 + 2 * (if a = true ∧ b = true then 1 else 0) := by
  cases a <;> cases b <;> decide

lemma slot_eval_eq {q : ℕ} (r : Fin q) (c : Fin 3) (inS : Bool) (a b : Fin q → Bool) :
    (slotLabel r c inS).elim id (fun p => xor p.2 (if inS = true then a p.1 else b p.1)) =
    (slotLabel (q := 1) 0 c inS).elim id (fun p => xor p.2 (if inS = true then a r else b r)) := by
  fin_cases c <;> cases inS <;> rfl

lemma gadget_for_cut (n : ℕ) (hn : 262144 ≤ n)
    (M : Fin 3 → Equiv.Perm (Fin n))
    (hcoinc : ∀ j l : Fin 3, j ≠ l →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (S : Finset (Bool × Fin n))
    (j0 : Fin 3) (hcross : 3 * (n / 65536) ≤ (CrossSet M S j0).card)
    (k : ℕ) (hk : k ≤ n / 65536) :
    let q := n / 65536
    ∃ label : (Bool × Fin n) → Bool ⊕ (Fin q × Bool),
      ∀ a b : Fin q → Bool,
        let x := fun v : Bool × Fin n => (label v).elim id (fun p =>
          xor p.2 (if v ∈ S then a p.1 else b p.1))
        (∀ j : Fin 3,
          16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card) n ≤ n) ↔
        (Finset.univ.filter (fun i : Fin q => a i = true ∧ b i = true)).card ≤ k := by
  classical
  intro q
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcross
  let d_target := Umax n - q - 2 * k
  have h8192 : 8192 * 3 < n := by omega
  have hA128 : 128 * A.card ≤ n := by rw [hAcard]; omega
  have hd_le : d_target ≤ n - A.card := by
    rw [hAcard]; dsimp only [d_target, Umax, q]; omega
  obtain ⟨w0, hw0_j0, hw0_other⟩ :=
    exists_pinned_base n 3 h8192 M hcoinc j0 A hA128 d_target hd_le
  have hcard_eq : Fintype.card (Fin q × Fin 3) = Fintype.card A := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, hAcard]
    ring
  let e : Fin q × Fin 3 ≃ A := Fintype.equivOfCardEq hcard_eq
  let label : (Bool × Fin n) → Bool ⊕ (Fin q × Bool) := fun v =>
    match v with
    | (false, i) =>
      if hi : i ∈ A then
        let rc := e.symm ⟨i, hi⟩
        slotLabel rc.1 rc.2 (decide ((false, i) ∈ S))
      else Sum.inl (w0 (false, i))
    | (true, y) =>
      let i := (M j0).symm y
      if hi : i ∈ A then
        let rc := e.symm ⟨i, hi⟩
        slotLabel rc.1 rc.2 (decide ((true, y) ∈ S))
      else Sum.inl (w0 (true, y))
  refine ⟨label, fun a b => ?_⟩
  intro x
  let UA : Finset (Bool × Fin n) :=
    A.image (fun i => (false, i)) ∪ A.image (fun i => (true, M j0 i))
  have hx_off : ∀ v, v ∉ UA → x v = w0 v := by
    intro ⟨b0, y⟩ hv
    cases b0
    · have hyA : y ∉ A := fun h => hv (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨y, h, rfl⟩))
      simp only [x, label, dite_eq_right hyA, Sum.elim_inl, id_eq]
    · have hyA : (M j0).symm y ∉ A := fun h =>
        hv (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(M j0).symm y, h, by simp⟩))
      simp only [x, label, dite_eq_right hyA, Sum.elim_inl, id_eq]
  have hx_other : ∀ j : Fin 3, j ≠ j0 →
      16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card) n ≤ n :=
    hw0_other x hx_off
  have hD_j0 : (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
      d_target + q + 2 * (Finset.univ.filter (fun r : Fin q => a r = true ∧ b r = true)).card := by
    have hdisj : Disjoint (Finset.univ \ A) A := Finset.sdiff_disjoint
    have hunion : (Finset.univ \ A) ∪ A = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ A)
    have hsplit : (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
        ((Finset.univ \ A).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card +
        (A.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card := by
      conv_lhs => rw [← hunion]
      rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
    have hoff_eq : ((Finset.univ \ A).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
        d_target := by
      rw [← hw0_j0]
      congr 1
      refine Finset.filter_congr (fun i hi => ?_)
      have hiA : i ∉ A := (Finset.mem_sdiff.mp hi).2
      have hf : (false, i) ∉ UA := by
        intro hm
        rcases Finset.mem_union.mp hm with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨u, hu, heq⟩
          exact hiA ((Prod.mk.inj heq).2 ▸ hu)
        · rcases Finset.mem_image.mp h2 with ⟨u, _, heq⟩
          exact Bool.false_ne_true (Prod.mk.inj heq).1.symm
      have ht : (true, M j0 i) ∉ UA := by
        intro hm
        rcases Finset.mem_union.mp hm with h1 | h2
        · rcases Finset.mem_image.mp h1 with ⟨u, _, heq⟩
          exact Bool.false_ne_true (Prod.mk.inj heq).1
        · rcases Finset.mem_image.mp h2 with ⟨u, hu, heq⟩
          have : u = i := (M j0).injective (Prod.mk.inj heq).2
          exact hiA (this ▸ hu)
      rw [hx_off _ hf, hx_off _ ht]
    have hA_eq : (A.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
        q + 2 * (Finset.univ.filter (fun r : Fin q => a r = true ∧ b r = true)).card := by
      have hcard_sum : (A.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
          ∑ i ∈ A, if x (false, i) ≠ x (true, M j0 i) then 1 else 0 := by
        rw [Finset.sum_boole, Nat.cast_id]
      rw [hcard_sum]
      have hsum_e : ∑ i ∈ A, (if x (false, i) ≠ x (true, M j0 i) then 1 else 0) =
          ∑ rc : Fin q × Fin 3,
            if x (false, (e rc).1) ≠ x (true, M j0 (e rc).1) then 1 else 0 := by
        rw [← Finset.sum_attach A (fun i => if x (false, i) ≠ x (true, M j0 i) then 1 else 0)]
        have := Fintype.sum_equiv e
          (fun rc : Fin q × Fin 3 => if x (false, (e rc).1) ≠ x (true, M j0 (e rc).1) then 1 else 0)
          (fun z : A => if x (false, z.1) ≠ x (true, M j0 z.1) then 1 else 0)
          (fun _ => rfl)
        exact this.symm
      rw [hsum_e, Fintype.sum_prod_type]
      have hpair : ∀ (r : Fin q) (c : Fin 3),
          (x (false, (e (r, c)).1) ≠ x (true, M j0 (e (r, c)).1)) ↔
          ((slotLabel (q := 1) 0 c true).elim id (fun p => xor p.2 (a r)) ≠
           (slotLabel (q := 1) 0 c false).elim id (fun p => xor p.2 (b r))) := by
        intro r c
        set i := (e (r, c)).1
        have hiA : i ∈ A := (e (r, c)).2
        have hcross_i : ¬((false, i) ∈ S ↔ (true, M j0 i) ∈ S) :=
          (Finset.mem_filter.mp (hAsub hiA)).2
        have he_symm : e.symm ⟨i, hiA⟩ = (r, c) := by
          have : (⟨i, hiA⟩ : A) = e (r, c) := Subtype.ext rfl
          rw [this, Equiv.symm_apply_apply]
        have hx_f : x (false, i) =
            (slotLabel (q := 1) 0 c (decide ((false, i) ∈ S))).elim id
              (fun p => xor p.2 (if decide ((false, i) ∈ S) = true then a r else b r)) := by
          dsimp only [x, label]
          rw [dite_eq_left hiA, he_symm]
          have hcond : (fun p : Fin q × Bool => xor p.2 (if (false, i) ∈ S then a p.1 else b p.1)) =
              (fun p : Fin q × Bool => xor p.2 (if decide ((false, i) ∈ S) = true then a p.1 else b p.1)) := by
            funext p; by_cases hs : (false, i) ∈ S <;> simp [hs]
          rw [hcond]
          exact slot_eval_eq r c (decide ((false, i) ∈ S)) a b
        have hx_t : x (true, M j0 i) =
            (slotLabel (q := 1) 0 c (decide ((true, M j0 i) ∈ S))).elim id
              (fun p => xor p.2 (if decide ((true, M j0 i) ∈ S) = true then a r else b r)) := by
          dsimp only [x, label]
          rw [(M j0).symm_apply_apply, dite_eq_left hiA, he_symm]
          have hcond : (fun p : Fin q × Bool => xor p.2 (if (true, M j0 i) ∈ S then a p.1 else b p.1)) =
              (fun p : Fin q × Bool => xor p.2 (if decide ((true, M j0 i) ∈ S) = true then a p.1 else b p.1)) := by
            funext p; by_cases hs : (true, M j0 i) ∈ S <;> simp [hs]
          rw [hcond]
          exact slot_eval_eq r c (decide ((true, M j0 i) ∈ S)) a b
        rw [hx_f, hx_t]
        by_cases hfS : (false, i) ∈ S
        · have htS : (true, M j0 i) ∉ S := fun ht => hcross_i ⟨fun _ => ht, fun _ => hfS⟩
          simp [hfS, htS]
        · have htS : (true, M j0 i) ∈ S := by
            by_contra ht; exact hcross_i ⟨fun h => absurd h hfS, fun h => absurd h ht⟩
          simp only [hfS, htS, decide_false, decide_true, Bool.false_eq_true, ↓reduceIte, ne_comm]
      have hinner : ∀ r : Fin q,
          (∑ c : Fin 3, if x (false, (e (r, c)).1) ≠ x (true, M j0 (e (r, c)).1) then 1 else 0) =
          1 + 2 * (if a r = true ∧ b r = true then 1 else 0) := by
        intro r
        rw [Fin.sum_univ_three]
        simp only [hpair r 0, hpair r 1, hpair r 2]
        exact slot_triple_sum (a r) (b r)
      calc ∑ r : Fin q, ∑ c : Fin 3,
              (if x (false, (e (r, c)).1) ≠ x (true, M j0 (e (r, c)).1) then 1 else 0)
          = ∑ r : Fin q, (1 + 2 * (if a r = true ∧ b r = true then 1 else 0)) :=
            Finset.sum_congr rfl (fun r _ => hinner r)
        _ = (∑ _r : Fin q, 1) + 2 * ∑ r : Fin q, (if a r = true ∧ b r = true then 1 else 0) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = q + 2 * (Finset.univ.filter (fun r : Fin q => a r = true ∧ b r = true)).card := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
              Finset.sum_boole, Nat.cast_id]
    rw [hsplit, hoff_eq, hA_eq]
    ring
  constructor
  · intro hacc
    have hj0 := (central_iff n _).mp (hacc j0)
    rw [hD_j0] at hj0
    have hle : (Finset.univ.filter (fun r : Fin q => a r = true ∧ b r = true)).card ≤ k := by
      dsimp only [d_target, Umax, Lmin, q] at hj0 ⊢
      omega
    exact le_of_eq_of_le (by
      apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) hle
  · intro hinter j
    by_cases hj : j = j0
    · subst hj
      rw [central_iff, hD_j0]
      have hcard_le : (Finset.univ.filter (fun r : Fin q => a r = true ∧ b r = true)).card ≤ k :=
        le_of_eq_of_le (by
          apply congrArg Finset.card; ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) hinter
      dsimp only [d_target, Umax, Lmin, q] at hcard_le ⊢
      omega
    · exact hx_other j hj


end PEqualNP.Outside.L_pcx_319_aux

theorem PEqualNP.Outside.L_pcx_319 :
∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let V := Bool × Fin n
  let q := n / 65536
  let A := Fin q → Bool
  let accepts := fun (M : Fin 3 → Equiv.Perm (Fin n)) (x : V → Bool) =>
    ∀ j : Fin 3,
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      16 * Nat.dist (2*D) n ≤ n
  ∃ M : Fin 3 → Equiv.Perm (Fin n), ∀ S : Finset V,
    n ≤ 2*S.card → 2*S.card ≤ 3*n → ∀ k : ℕ, k ≤ q →
    ∃ label : V → Bool ⊕ (Fin q × Bool),
      ∀ a b : A,
        let x := fun v : V => (label v).elim id (fun p =>
          xor p.2 (if v ∈ S then a p.1 else b p.1))
        accepts M x ↔ (Finset.univ.filter (fun i : Fin q => a i = true ∧ b i = true)).card ≤ k := by
  refine ⟨262144, fun n hn => ?_⟩
  intro V q A accepts
  obtain ⟨M, hcoinc, hcut⟩ := PEqualNP.Outside.L_pcx_319_aux.exists_good_M n hn
  refine ⟨M, fun S hlo hhi k hk => ?_⟩
  obtain ⟨j0, hcross⟩ := hcut S hlo hhi
  exact PEqualNP.Outside.L_pcx_319_aux.gadget_for_cut n hn M hcoinc S j0 hcross k hk
