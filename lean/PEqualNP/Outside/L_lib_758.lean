import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_758

lemma pow_15_16_lt_half : ((15 : ℝ) / 16) ^ 11 < 1 / 2 := by
  have h : (15 : ℕ) ^ 11 * 2 < 16 ^ 11 := by decide
  have hR : ((15 : ℝ) ^ 11) * 2 < (16 : ℝ) ^ 11 := by exact_mod_cast h
  rw [div_pow, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

lemma sum_zero_card_le {k m : ℕ} (S : Finset (Fin m)) (hS : S.Nonempty) :
    (Finset.univ.filter (fun v : Fin m → (Fin k → ZMod 2) => ∑ j ∈ S, v j = 0)).card ≤
      (2 ^ k) ^ (m - 1) := by
  obtain ⟨j0, hj0⟩ := hS
  let T := Finset.univ.filter (fun v : Fin m → (Fin k → ZMod 2) => ∑ j ∈ S, v j = 0)
  let f : T → ({j : Fin m // j ≠ j0} → (Fin k → ZMod 2)) :=
    fun v j => v.1 j.1
  have hf : Function.Injective f := by
    rintro ⟨v1, hv1⟩ ⟨v2, hv2⟩ heq
    ext j i
    by_cases hj : j = j0
    · rw [hj]
      have hv1' : ∑ x ∈ S, v1 x = 0 := (Finset.mem_filter.mp hv1).2
      have hv2' : ∑ x ∈ S, v2 x = 0 := (Finset.mem_filter.mp hv2).2
      have h1 : v1 j0 + ∑ x ∈ S.erase j0, v1 x = 0 := by
        simpa [Finset.add_sum_erase S v1 hj0] using hv1'
      have h2 : v2 j0 + ∑ x ∈ S.erase j0, v2 x = 0 := by
        simpa [Finset.add_sum_erase S v2 hj0] using hv2'
      have hsum : ∑ x ∈ S.erase j0, v1 x = ∑ x ∈ S.erase j0, v2 x := by
        apply Finset.sum_congr rfl
        intro x hx
        exact congrFun heq ⟨x, (Finset.mem_erase.mp hx).1⟩
      rw [hsum] at h1
      have hsub := congrArg (· - ∑ x ∈ S.erase j0, v2 x) h1
      have hsub2 := congrArg (· - ∑ x ∈ S.erase j0, v2 x) h2
      simp only [add_sub_cancel_right, zero_sub] at hsub hsub2
      exact congrFun (hsub.trans hsub2.symm) i
    · exact congrFun (congrFun heq ⟨j, hj⟩) i
  have hcard1 : T.card ≤ Fintype.card ({j : Fin m // j ≠ j0} → (Fin k → ZMod 2)) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective f hf
  have hcard2 : Fintype.card ({j : Fin m // j ≠ j0} → (Fin k → ZMod 2)) = (2 ^ k) ^ (m - 1) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
  exact hcard1.trans_eq hcard2

lemma small_subsets_card_le_six {m : ℕ} :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun S => 0 < S.card ∧ S.card ≤ 6)).card ≤
      m ^ 6 := by
  let U := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => 0 < S.card ∧ S.card ≤ 6)
  have hsub : U ⊆ (Finset.univ : Finset (Fin 6 → Fin m)).image (fun f => Finset.univ.image f) := by
    intro S hS
    rcases Finset.mem_filter.mp hS with ⟨_, hpos, hle⟩
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hpos
    let g : Fin S.card ≃ S := (S.equivFin).symm
    let f : Fin 6 → Fin m := fun i =>
      if hi : i.val < S.card then (g ⟨i.val, hi⟩).1 else x0
    refine Finset.mem_image.mpr ⟨f, Finset.mem_univ f, ?_⟩
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      dsimp only [f]
      split_ifs with hi
      · exact (g ⟨i.val, hi⟩).2
      · exact hx0
    · intro hy
      obtain ⟨i, hi⟩ := g.surjective ⟨y, hy⟩
      refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hle⟩, ?_⟩
      simp only [f, i.isLt, dite_true, Fin.eta]
      exact congrArg Subtype.val hi
  calc U.card
      ≤ ((Finset.univ : Finset (Fin 6 → Fin m)).image (fun f => Finset.univ.image f)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin 6 → Fin m)).card := Finset.card_image_le
    _ = m ^ 6 := by simp

lemma small_subsets_lt {k : ℕ} (hk : 128 ≤ k) :
    (((Finset.univ : Finset (Finset (Fin (256 * k)))).filter
      (fun S => 0 < S.card ∧ S.card ≤ max 6 (k / 32))).card : ℝ) < (2 : ℝ) ^ (k - 1) := by
  by_cases h192 : k < 192
  · have hmax : max 6 (k / 32) = 6 := max_eq_left (by omega)
    rw [hmax]
    have hle : ((Finset.univ : Finset (Finset (Fin (256 * k)))).filter
        (fun S => 0 < S.card ∧ S.card ≤ 6)).card ≤ (256 * k) ^ 6 :=
      small_subsets_card_le_six
    have hpow : (256 * k) ^ 6 < 2 ^ (k - 1) := by
      have h1 : 256 * k < 2 ^ 16 := by omega
      have h2 : (256 * k) ^ 6 < (2 ^ 16) ^ 6 := Nat.pow_lt_pow_left h1 (by norm_num)
      have h3 : (2 ^ 16) ^ 6 = 2 ^ 96 := by norm_num
      have h4 : 2 ^ 96 ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact_mod_cast lt_of_le_of_lt hle hpow
  · have hk192 : 192 ≤ k := le_of_not_gt h192
    have hmax : max 6 (k / 32) = k / 32 := max_eq_right (by omega)
    rw [hmax]
    let m := 256 * k
    let U := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => 0 < S.card ∧ S.card ≤ k / 32)
    have hsum : ∑ S : Finset (Fin m), (1 / 4096 : ℝ) ^ S.card = (1 + 1 / 4096 : ℝ) ^ m := by
      have h := Finset.prod_one_add (s := (Finset.univ : Finset (Fin m)))
        (f := fun _ => (1 / 4096 : ℝ))
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      rw [h]
      simp only [Finset.powerset_univ]
    have hterm : ∀ S ∈ U, (1 / 4096 : ℝ) ^ (k / 32) ≤ (1 / 4096 : ℝ) ^ S.card := by
      intro S hS
      have hle : S.card ≤ k / 32 := (Finset.mem_filter.mp hS).2.2
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
    have hmarkov : (U.card : ℝ) * (1 / 4096 : ℝ) ^ (k / 32) ≤ (1 + 1 / 4096 : ℝ) ^ m := by
      calc (U.card : ℝ) * (1 / 4096 : ℝ) ^ (k / 32)
          = ∑ _S ∈ U, (1 / 4096 : ℝ) ^ (k / 32) := by simp
        _ ≤ ∑ S ∈ U, (1 / 4096 : ℝ) ^ S.card := Finset.sum_le_sum hterm
        _ ≤ ∑ S : Finset (Fin m), (1 / 4096 : ℝ) ^ S.card :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
        _ = (1 + 1 / 4096 : ℝ) ^ m := hsum
    have hexp : (1 + 1 / 4096 : ℝ) ^ m ≤ (2 : ℝ) ^ (2 * (k / 16 + 1)) := by
      have h1 : (1 + 1 / 4096 : ℝ) ≤ Real.exp (1 / 4096) := by
        linarith [Real.add_one_le_exp (1 / 4096 : ℝ)]
      have h2 : (1 + 1 / 4096 : ℝ) ^ m ≤ (Real.exp (1 / 4096)) ^ m :=
        pow_le_pow_left₀ (by norm_num) h1 m
      have h3 : (Real.exp (1 / 4096)) ^ m = Real.exp ((m : ℝ) / 4096) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have h4 : (m : ℝ) / 4096 ≤ ((k / 16 + 1 : ℕ) : ℝ) := by
        rw [div_le_iff₀ (by norm_num)]
        have hnat : m ≤ (k / 16 + 1) * 4096 := by
          have : k < 16 * (k / 16 + 1) := Nat.lt_mul_div_succ k (by norm_num)
          dsimp [m]; omega
        exact_mod_cast hnat
      have h5 : Real.exp ((m : ℝ) / 4096) ≤ Real.exp (((k / 16 + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr h4
      have h6 : Real.exp (((k / 16 + 1 : ℕ) : ℝ)) = (Real.exp 1) ^ (k / 16 + 1) := by
        rw [← Real.exp_nat_mul]; ring_nf
      have h7 : Real.exp 1 ≤ (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h8 : (Real.exp 1) ^ (k / 16 + 1) ≤ (4 : ℝ) ^ (k / 16 + 1) :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h7 _
      have h9 : (4 : ℝ) ^ (k / 16 + 1) = (2 : ℝ) ^ (2 * (k / 16 + 1)) := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      linarith [h2, h3, h5, h6, h8, h9]
    have h4096 : (4096 : ℝ) ^ (k / 32) = (2 : ℝ) ^ (12 * (k / 32)) := by
      rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, ← pow_mul]
    have hU : (U.card : ℝ) ≤ (2 : ℝ) ^ (12 * (k / 32) + 2 * (k / 16 + 1)) := by
      have hpos : (0 : ℝ) < (1 / 4096 : ℝ) ^ (k / 32) := by positivity
      have hdiv := (le_div_iff₀ hpos).mpr hmarkov
      rw [div_eq_mul_inv] at hdiv
      simp only [one_div, inv_pow, inv_inv] at hdiv
      rw [h4096] at hdiv
      calc (U.card : ℝ) ≤ (1 + 4096⁻¹ : ℝ) ^ m * (2 : ℝ) ^ (12 * (k / 32)) := hdiv
        _ = (1 + 1 / 4096 : ℝ) ^ m * (2 : ℝ) ^ (12 * (k / 32)) := by norm_num
        _ ≤ (2 : ℝ) ^ (2 * (k / 16 + 1)) * (2 : ℝ) ^ (12 * (k / 32)) :=
            mul_le_mul_of_nonneg_right hexp (by positivity)
        _ = (2 : ℝ) ^ (12 * (k / 32) + 2 * (k / 16 + 1)) := by rw [← pow_add, add_comm]
    have hexp_lt : 12 * (k / 32) + 2 * (k / 16 + 1) < k - 1 := by
      have h32 : 32 * (k / 32) ≤ k := Nat.mul_div_le k 32
      have h16 : 16 * (k / 16) ≤ k := Nat.mul_div_le k 16
      omega
    have hpow_lt : (2 : ℝ) ^ (12 * (k / 32) + 2 * (k / 16 + 1)) < (2 : ℝ) ^ (k - 1) :=
      pow_lt_pow_right₀ (by norm_num) hexp_lt
    exact lt_of_le_of_lt hU hpow_lt

lemma fiber_card_eq {k : ℕ} (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (hA : Function.Surjective A) (t : Fin 3 → ZMod 2) :
    8 * (Finset.univ.filter (fun x => A x = t)).card = 2 ^ k := by
  have heq : ∀ s : Fin 3 → ZMod 2,
      (Finset.univ.filter (fun x => A x = s)).card =
      (Finset.univ.filter (fun x => A x = t)).card := by
    intro s
    obtain ⟨xs, hxs⟩ := hA s
    obtain ⟨xt, hxt⟩ := hA t
    refine Finset.card_bij (fun x _ => x - xs + xt) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_add, map_sub, hx, hxs, hxt, sub_self, zero_add]
    · intro x1 _ x2 _ heq
      have := congrArg (· - xt + xs) heq
      simpa using this
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨y - xt + xs, ?_, by abel⟩
      rw [map_add, map_sub, hy, hxt, hxs, sub_self, zero_add]
  have hpart : (Finset.univ : Finset (Fin k → ZMod 2)).card =
      ∑ s : Fin 3 → ZMod 2, (Finset.univ.filter (fun x => A x = s)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp
    · intro s _ s' _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      exact hne (h1.symm.trans h2)
  simp_rw [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, smul_eq_mul] at hpart
  simpa using hpart.symm

lemma sum_half_pow_fiber {k m : ℕ}
    (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (hA : Function.Surjective A) (t : Fin 3 → ZMod 2) :
    ∑ v : Fin m → (Fin k → ZMod 2),
      ((1 / 2 : ℝ) ^ ((Finset.univ.filter (fun j => A (v j) = t)).card)) =
    ((2 ^ k : ℝ) * (15 / 16 : ℝ)) ^ m := by
  let g : (Fin k → ZMod 2) → ℝ := fun x => if A x = t then 1 / 2 else 1
  have hprod : ∀ v : Fin m → (Fin k → ZMod 2),
      (1 / 2 : ℝ) ^ ((Finset.univ.filter (fun j => A (v j) = t)).card) =
      ∏ j : Fin m, g (v j) := by
    intro v
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  simp_rw [hprod]
  have hswap := (Fintype.prod_sum (fun (j : Fin m) (x : Fin k → ZMod 2) => g x)).symm
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hswap
  rw [hswap]
  congr 1
  have hfib := fiber_card_eq A hA t
  have hfibR : (8 : ℝ) * ((Finset.univ.filter (fun x => A x = t)).card : ℝ) = (2 ^ k : ℝ) := by
    exact_mod_cast hfib
  have hsumg : ∑ x : Fin k → ZMod 2, g x =
      ((Finset.univ.filter (fun x => A x = t)).card : ℝ) * (1 / 2) +
      ((Finset.univ.filter (fun x => ¬ A x = t)).card : ℝ) * 1 := by
    simp [g, Finset.sum_ite]
  have hcomp : ((Finset.univ.filter (fun x => A x = t)).card : ℝ) +
      ((Finset.univ.filter (fun x => ¬ A x = t)).card : ℝ) = (2 ^ k : ℝ) := by
    have hnat : (Finset.univ.filter (fun x => A x = t)).card +
        (Finset.univ.filter (fun x => ¬ A x = t)).card =
        (Finset.univ : Finset (Fin k → ZMod 2)).card :=
      Finset.card_filter_add_card_filter_not (fun x => A x = t)
    have hcard : (Finset.univ : Finset (Fin k → ZMod 2)).card = 2 ^ k := by
      simp [ZMod.card]
    exact_mod_cast hnat.trans hcard
  linarith

def toLin {k : ℕ} (M : Fin k → (Fin 3 → ZMod 2)) : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2) where
  toFun x := ∑ i : Fin k, x i • M i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

lemma eq_toLin {k : ℕ} (A : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    A = toLin (fun i => A (Pi.single i 1)) := by
  apply LinearMap.ext
  intro x
  have hx : x = ∑ i : Fin k, x i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp [toLin, map_smul]

set_option maxRecDepth 4096 in
lemma hbase_aux_gen (q t : ℝ) (hq : q = 15 / 16) (ht : t = 2) :
    (8 : ℝ) * (t ^ 16 * q ^ 256) < 1 / 2 := by
  have h11 : q ^ 11 < 1 / 2 := by rw [hq]; exact pow_15_16_lt_half
  have hq0 : 0 ≤ q := by rw [hq]; norm_num
  have hq1 : q ≤ 1 := by rw [hq]; norm_num
  have h253 : q ^ 253 < (1 / 2 : ℝ) ^ 23 := by
    have : q ^ 253 = (q ^ 11) ^ 23 := by rw [← pow_mul]
    rw [this]
    exact pow_lt_pow_left₀ h11 (by positivity) (by norm_num)
  have h256 : q ^ 256 ≤ q ^ 253 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have h256' : q ^ 256 < (1 / 2 : ℝ) ^ 23 := lt_of_le_of_lt h256 h253
  have ht0 : 0 < t := by rw [ht]; norm_num
  have h8 : (8 : ℝ) * (t ^ 16 * q ^ 256) < (8 : ℝ) * (t ^ 16 * (1 / 2 : ℝ) ^ 23) :=
    mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left h256' (by positivity)) (by norm_num)
  have hval : (8 : ℝ) * (t ^ 16 * (1 / 2 : ℝ) ^ 23) < 1 / 2 := by
    rw [ht]
    have hpow : (8 : ℝ) * ((2 : ℝ) ^ 16 * (1 / 2 : ℝ) ^ 23) = (1 / 2 : ℝ) ^ 4 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← mul_assoc, ← pow_add,
        one_div, inv_pow, show (23 : ℕ) = 19 + 4 by rfl, pow_add _ 19 4, mul_inv,
        ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul, inv_pow]
    rw [hpow]
    norm_num
  exact lt_trans h8 hval

set_option maxRecDepth 4096 in
lemma hbase_aux : (8 : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) < 1 / 2 :=
  hbase_aux_gen (15 / 16) 2 rfl rfl

set_option maxRecDepth 4096 in
lemma hhalf_aux_gen {k : ℕ} (hk : 128 ≤ k) (h : ℝ) (hh : h = 1 / 2) : (8 : ℝ) * h ^ k < 1 / 2 := by
  have hh0 : 0 ≤ h := by rw [hh]; norm_num
  have hh1 : h ≤ 1 := by rw [hh]; norm_num
  have hk1 : h ^ k ≤ h ^ 128 := pow_le_pow_of_le_one hh0 hh1 hk
  have hk3 : (8 : ℝ) * h ^ 128 < 1 / 2 := by
    rw [hh]
    have hpow : (8 : ℝ) * (1 / 2 : ℝ) ^ 128 = (1 / 2 : ℝ) ^ 125 := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num,
        show (2 : ℝ) ^ 3 = ((1 / 2 : ℝ) ^ 3)⁻¹ by norm_num,
        show (128 : ℕ) = 3 + 125 by rfl, pow_add, ← mul_assoc,
        inv_mul_cancel₀ (by positivity), one_mul]
    rw [hpow]
    have h125 : (1 / 2 : ℝ) ^ 125 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    linarith [h125, show (1 / 2 : ℝ) ^ 2 < 1 / 2 by norm_num]
  calc (8 : ℝ) * h ^ k ≤ 8 * h ^ 128 := mul_le_mul_of_nonneg_left hk1 (by norm_num)
    _ < 1 / 2 := hk3

set_option maxRecDepth 4096 in
lemma hhalf_aux {k : ℕ} (hk : 128 ≤ k) : (8 : ℝ) * (1 / 2 : ℝ) ^ k < 1 / 2 :=
  hhalf_aux_gen hk (1 / 2) rfl

end PEqualNP.Outside.L_lib_758

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_lib_758 : (∀ k : ℕ, 128 ≤ k →
  let F := ZMod 2
  let V := Fin k → F
  let m := 256*k
  ∃ v : Fin m ↪ V,
    (∀ S : Finset (Fin m), 0 < S.card → S.card ≤ max 6 (k/32) → (∑ j ∈ S, v j) ≠ 0) ∧
    (∀ (A : V →ₗ[F] (Fin 3 → F)), Function.Surjective A → ∀ t : Fin 3 → F,
      m ≤ 16*((Finset.univ : Finset (Fin m)).filter (fun j => A (v j) = t)).card)) := by
  classical
  intro k hk F V m
  let N : ℕ := Fintype.card (Fin m → V)
  have hN : (N : ℝ) = (2 ^ k : ℝ) ^ m := by
    dsimp [N, V, F]
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    push_cast
    rfl
  let B1 := (Finset.univ : Finset (Fin m → V)).filter (fun v =>
    ∃ S : Finset (Fin m), 0 < S.card ∧ S.card ≤ max 6 (k / 32) ∧ ∑ j ∈ S, v j = 0)
  let B2 := (Finset.univ : Finset (Fin m → V)).filter (fun v =>
    ∃ A : V →ₗ[F] (Fin 3 → F), Function.Surjective A ∧ ∃ t : Fin 3 → F,
      16 * ((Finset.univ : Finset (Fin m)).filter (fun j => A (v j) = t)).card < m)
  have hB1 : (B1.card : ℝ) < (N : ℝ) / 2 := by
    let U := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => 0 < S.card ∧ S.card ≤ max 6 (k / 32))
    have hsub : B1 ⊆ U.biUnion (fun S => Finset.univ.filter (fun v : Fin m → V => ∑ j ∈ S, v j = 0)) := by
      intro v hv
      rcases (Finset.mem_filter.mp hv).2 with ⟨S, hpos, hle, hsum⟩
      exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ S, hpos, hle⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, hsum⟩⟩
    have hcard : B1.card ≤ U.card * (2 ^ k) ^ (m - 1) := by
      calc B1.card
          ≤ (U.biUnion (fun S => Finset.univ.filter (fun v : Fin m → V => ∑ j ∈ S, v j = 0))).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ S ∈ U, (Finset.univ.filter (fun v : Fin m → V => ∑ j ∈ S, v j = 0)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _S ∈ U, (2 ^ k) ^ (m - 1) := by
            apply Finset.sum_le_sum
            intro S hS
            have hpos := (Finset.mem_filter.mp hS).2.1
            exact PEqualNP.Outside.L_lib_758.sum_zero_card_le S (Finset.card_pos.mp hpos)
        _ = U.card * (2 ^ k) ^ (m - 1) := by simp
    have hcardR : (B1.card : ℝ) ≤ (U.card : ℝ) * (2 ^ k : ℝ) ^ (m - 1) := by
      exact_mod_cast hcard
    have hU : (U.card : ℝ) < (2 : ℝ) ^ (k - 1) :=
      PEqualNP.Outside.L_lib_758.small_subsets_lt hk
    have hpos : (0 : ℝ) < (2 ^ k : ℝ) ^ (m - 1) := by positivity
    have hlt := mul_lt_mul_of_pos_right hU hpos
    have hm1 : 1 ≤ m := by dsimp [m]; omega
    have hpow : (2 : ℝ) ^ (k - 1) * (2 ^ k : ℝ) ^ (m - 1) = (N : ℝ) / 2 := by
      rw [hN, show m = (m - 1) + 1 by omega, pow_succ]
      have h2k : (2 : ℝ) ^ (k - 1) * 2 = (2 : ℝ) ^ k := by
        rw [← pow_succ, show k - 1 + 1 = k by omega]
      push_cast
      rw [← h2k]
      ring
    linarith [hcardR, hlt, hpow]
  have hB2 : (B2.card : ℝ) < (N : ℝ) / 2 := by
    let pairs := (Finset.univ : Finset ((Fin k → (Fin 3 → F)) × (Fin 3 → F))).filter
      (fun p => Function.Surjective (PEqualNP.Outside.L_lib_758.toLin p.1))
    have hsub : B2 ⊆ pairs.biUnion (fun p => Finset.univ.filter (fun v : Fin m → V =>
        16 * ((Finset.univ : Finset (Fin m)).filter (fun j =>
          PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card < m)) := by
      intro v hv
      rcases (Finset.mem_filter.mp hv).2 with ⟨A, hA, t, hlt⟩
      rw [PEqualNP.Outside.L_lib_758.eq_toLin A] at hA hlt
      exact Finset.mem_biUnion.mpr ⟨(_, t), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ v, hlt⟩⟩
    have hpair_bound : ∀ p ∈ pairs,
        ((Finset.univ.filter (fun v : Fin m → V =>
          16 * ((Finset.univ : Finset (Fin m)).filter (fun j =>
            PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card < m)).card : ℝ) ≤
        (N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k := by
      intro p hp
      have hsurj : Function.Surjective (PEqualNP.Outside.L_lib_758.toLin p.1) :=
        (Finset.mem_filter.mp hp).2
      let W := Finset.univ.filter (fun v : Fin m → V =>
        16 * ((Finset.univ : Finset (Fin m)).filter (fun j =>
          PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card < m)
      have hmark : (W.card : ℝ) * (1 / 2 : ℝ) ^ (16 * k) ≤
          ((2 ^ k : ℝ) * (15 / 16 : ℝ)) ^ m := by
        calc (W.card : ℝ) * (1 / 2 : ℝ) ^ (16 * k)
            = ∑ _v ∈ W, (1 / 2 : ℝ) ^ (16 * k) := by simp
          _ ≤ ∑ v ∈ W, (1 / 2 : ℝ) ^ ((Finset.univ.filter (fun j =>
                PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card) := by
              apply Finset.sum_le_sum
              intro v hv
              have hlt := (Finset.mem_filter.mp hv).2
              have hle : (Finset.univ.filter (fun j =>
                  PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card ≤ 16 * k := by
                change 16 * _ < 256 * k at hlt; omega
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hle
          _ ≤ ∑ v : Fin m → V, (1 / 2 : ℝ) ^ ((Finset.univ.filter (fun j =>
                PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card) :=
              Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
          _ = ((2 ^ k : ℝ) * (15 / 16 : ℝ)) ^ m :=
              PEqualNP.Outside.L_lib_758.sum_half_pow_fiber
                (PEqualNP.Outside.L_lib_758.toLin p.1) hsurj p.2
      have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (16 * k) := by positivity
      have hdiv := (le_div_iff₀ hpos).mpr hmark
      rw [div_eq_mul_inv] at hdiv
      simp only [one_div, inv_pow, inv_inv] at hdiv
      rw [mul_pow, ← hN] at hdiv
      have hpow16 : (2 : ℝ) ^ (16 * k) = ((2 : ℝ) ^ 16) ^ k := by rw [pow_mul]
      have hpow256 : ((15 : ℝ) / 16) ^ m = (((15 : ℝ) / 16) ^ 256) ^ k := by
        dsimp [m]; rw [pow_mul]
      rw [hpow16] at hdiv
      rw [hpow256] at hdiv
      calc (W.card : ℝ) ≤ (N : ℝ) * (((15 : ℝ) / 16) ^ 256) ^ k * ((2 : ℝ) ^ 16) ^ k := hdiv
        _ = (N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k := by
            rw [mul_assoc, ← mul_pow, mul_comm ((2 : ℝ) ^ 16)]
    have hpairs_card : pairs.card ≤ 8 * 8 ^ k := by
      calc pairs.card
          ≤ Fintype.card ((Fin k → (Fin 3 → F)) × (Fin 3 → F)) := Finset.card_le_univ pairs
        _ = Fintype.card (Fin k → (Fin 3 → F)) * Fintype.card (Fin 3 → F) := Fintype.card_prod _ _
        _ = 8 ^ k * 8 := by simp [F, ZMod.card]
        _ = 8 * 8 ^ k := mul_comm _ _
    have hB2_le : (B2.card : ℝ) ≤
        (pairs.card : ℝ) * ((N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k) := by
      have h1 : (B2.card : ℝ) ≤ ∑ p ∈ pairs,
          ((Finset.univ.filter (fun v : Fin m → V =>
            16 * ((Finset.univ : Finset (Fin m)).filter (fun j =>
              PEqualNP.Outside.L_lib_758.toLin p.1 (v j) = p.2)).card < m)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
      calc (B2.card : ℝ)
          ≤ ∑ _p ∈ pairs, ((N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k) :=
            h1.trans (Finset.sum_le_sum hpair_bound)
        _ = (pairs.card : ℝ) * ((N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k) := by simp
    have hpairsR : (pairs.card : ℝ) ≤ 8 * (8 : ℝ) ^ k := by exact_mod_cast hpairs_card
    have hbase : (8 : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) < 1 / 2 :=
      PEqualNP.Outside.L_lib_758.hbase_aux
    have hprod_le : (B2.card : ℝ) ≤ (N : ℝ) * (8 * (1 / 2 : ℝ) ^ k) := by
      have hmul : (8 * (8 : ℝ) ^ k) * ((N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k) =
          (N : ℝ) * (8 * ((8 : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256)) ^ k) := by
        rw [mul_pow, mul_pow, mul_pow]
        ac_rfl
      calc (B2.card : ℝ)
          ≤ (8 * (8 : ℝ) ^ k) * ((N : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256) ^ k) :=
            hB2_le.trans (mul_le_mul_of_nonneg_right hpairsR (by positivity))
        _ = (N : ℝ) * (8 * ((8 : ℝ) * ((2 : ℝ) ^ 16 * ((15 : ℝ) / 16) ^ 256)) ^ k) := hmul
        _ ≤ (N : ℝ) * (8 * (1 / 2 : ℝ) ^ k) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase.le k) (by norm_num))
              (by positivity)
    have hhalf : (8 : ℝ) * (1 / 2 : ℝ) ^ k < 1 / 2 :=
      PEqualNP.Outside.L_lib_758.hhalf_aux hk
    have hNpos : (0 : ℝ) < (N : ℝ) := by rw [hN]; positivity
    calc (B2.card : ℝ) ≤ (N : ℝ) * (8 * (1 / 2 : ℝ) ^ k) := hprod_le
      _ < (N : ℝ) * (1 / 2) := mul_lt_mul_of_pos_left hhalf hNpos
      _ = (N : ℝ) / 2 := mul_one_div (N : ℝ) 2
  have htot : (B1 ∪ B2).card < N := by
    have hR : ((B1 ∪ B2).card : ℝ) < (N : ℝ) := by
      have h1 : ((B1 ∪ B2).card : ℝ) ≤ (B1.card : ℝ) + (B2.card : ℝ) := by
        exact_mod_cast Finset.card_union_le B1 B2
      linarith [h1, hB1, hB2]
    exact_mod_cast hR
  have hne : (Finset.univ \ (B1 ∪ B2) : Finset (Fin m → V)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : (Finset.univ : Finset (Fin m → V)) ⊆ B1 ∪ B2 := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle := Finset.card_le_card hsub
    change N ≤ (B1 ∪ B2).card at hle
    omega
  obtain ⟨v, hv⟩ := hne
  have hv1 : v ∉ B1 := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left B2 h)
  have hv2 : v ∉ B2 := fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right B1 h)
  have hS : ∀ S : Finset (Fin m), 0 < S.card → S.card ≤ max 6 (k / 32) → (∑ j ∈ S, v j) ≠ 0 := by
    intro S hpos hle hsum
    exact hv1 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, S, hpos, hle, hsum⟩)
  have hinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have h0 : ∑ x ∈ ({i, j} : Finset (Fin m)), v x = 0 := by
      rw [Finset.sum_pair hne, hij]
      ext c
      exact CharTwo.add_self_eq_zero (v j c)
    have hcard : ({i, j} : Finset (Fin m)).card = 2 := Finset.card_pair hne
    exact hS {i, j} (by omega) (by omega) h0
  refine ⟨⟨v, hinj⟩, hS, ?_⟩
  intro A hA t
  by_contra hlt
  push Not at hlt
  exact hv2 (Finset.mem_filter.mpr ⟨Finset.mem_univ v, A, hA, t, hlt⟩)
