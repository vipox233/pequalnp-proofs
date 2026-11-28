import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1272_aux

open Classical

-- =========================================================================
-- Part 1: ZMod 2 inner products and linearly independent column selection
-- =========================================================================

private def toZ2 {m : ℕ} (f : Fin m → Bool) : Fin m → ZMod 2 :=
  fun i => if f i then 1 else 0

private def fromZ2 {m : ℕ} (x : Fin m → ZMod 2) : Fin m → Bool :=
  fun i => decide (x i = 1)

private lemma fromZ2_toZ2 {m : ℕ} (f : Fin m → Bool) : fromZ2 (toZ2 f) = f := by
  funext i
  cases h : f i <;> simp [fromZ2, toZ2, h]

private lemma toZ2_fromZ2 {m : ℕ} (x : Fin m → ZMod 2) : toZ2 (fromZ2 x) = x := by
  funext i
  have h01 : x i = 0 ∨ x i = 1 := by
    have hcases : (x i).val = 0 ∨ (x i).val = 1 := by have := (x i).val_lt; omega
    rcases hcases with h0 | h1
    · left; exact ZMod.val_injective 2 (by rw [h0]; rfl)
    · right; exact ZMod.val_injective 2 (by rw [h1]; rfl)
  rcases h01 with h0 | h1
  · simp [toZ2, fromZ2, h0]
  · simp [toZ2, fromZ2, h1]

private def equivZ2 (m : ℕ) : (Fin m → Bool) ≃ (Fin m → ZMod 2) :=
  { toFun := toZ2
    invFun := fromZ2
    left_inv := fromZ2_toZ2
    right_inv := toZ2_fromZ2 }

private lemma odd_iff_dotZ2 {m : ℕ} (f g : Fin m → Bool) :
    ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1 ↔
      (∑ i : Fin m, toZ2 f i * toZ2 g i) = (1 : ZMod 2) := by
  have hsum : (∑ i : Fin m, toZ2 f i * toZ2 g i) =
      (((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card : ZMod 2) := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases hf : f i <;> cases hg : g i <;> simp [toZ2, hf, hg]
  rw [hsum]
  set c := ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card
  constructor
  · intro h
    have hv : (c : ZMod 2).val = 1 := by rw [ZMod.val_natCast, h]
    exact ZMod.val_injective 2 (by rw [hv]; rfl)
  · intro h
    have hv := congrArg ZMod.val h
    rw [ZMod.val_natCast] at hv
    exact hv

private lemma exists_linIndep_Z2 {m t : ℕ} (G : Finset (Fin m → Bool))
    (hM : 2 ^ (t - 1) < G.card) :
    ∃ g : Fin t → (Fin m → Bool),
      (∀ a, g a ∈ G) ∧ LinearIndependent (ZMod 2) (fun a => toZ2 (g a)) := by
  have hstep : ∀ j ≤ t,
      ∃ g : Fin j → (Fin m → Bool),
        (∀ a, g a ∈ G) ∧ LinearIndependent (ZMod 2) (fun a => toZ2 (g a)) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨Fin.elim0, fun a => Fin.elim0 a, linearIndependent_empty_type⟩
    | succ j ih =>
      intro hjt
      rcases ih (by omega) with ⟨g, hgG, hind⟩
      let S : Finset (Fin m → ZMod 2) :=
        Finset.univ.image (fun c : Fin j → ZMod 2 => ∑ a : Fin j, c a • toZ2 (g a))
      have hScard : S.card ≤ 2 ^ (t - 1) := by
        calc S.card ≤ (Finset.univ : Finset (Fin j → ZMod 2)).card := Finset.card_image_le
          _ = 2 ^ j := by simp [ZMod.card]
          _ ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have hGimg : (G.image toZ2).card = G.card :=
        Finset.card_image_of_injective G (equivZ2 m).injective
      have hnotSub : ¬ G.image toZ2 ⊆ S := by
        intro hsub
        have := Finset.card_le_card hsub
        omega
      rcases Finset.not_subset.mp hnotSub with ⟨y, hyG, hyS⟩
      rcases Finset.mem_image.mp hyG with ⟨x, hxG, rfl⟩
      let g' : Fin (j + 1) → (Fin m → Bool) := Fin.snoc g x
      refine ⟨g', ?_, ?_⟩
      · intro a
        refine Fin.lastCases ?_ ?_ a
        · simpa [g'] using hxG
        · intro b; simpa [g'] using hgG b
      · rw [Fintype.linearIndependent_iff]
        intro c hc
        rw [Fin.sum_univ_castSucc] at hc
        have hcast : ∀ b : Fin j, g' b.castSucc = g b := fun b => by simp [g', Fin.snoc_castSucc]
        have hlast : g' (Fin.last j) = x := by simp [g', Fin.snoc_last]
        simp only [hcast, hlast] at hc
        have hclast : c (Fin.last j) = 0 := by
          by_contra hne
          have h1 : c (Fin.last j) = 1 := by
            generalize hz : c (Fin.last j) = v
            rw [hz] at hne
            fin_cases v
            · exact absurd rfl hne
            · rfl
          rw [h1, one_smul] at hc
          have hx_eq : toZ2 x = ∑ b : Fin j, (-c b.castSucc) • toZ2 (g b) := by
            have hneg := eq_neg_of_add_eq_zero_right hc
            rw [hneg, ← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro b _; exact (neg_smul (c b.castSucc) (toZ2 (g b))).symm
          exact hyS (Finset.mem_image.mpr ⟨fun b => -c b.castSucc, Finset.mem_univ _, hx_eq.symm⟩)
        rw [hclast, zero_smul, add_zero] at hc
        have hprev := Fintype.linearIndependent_iff.mp hind (fun b => c b.castSucc) hc
        intro a
        refine Fin.lastCases hclast hprev a
  exact hstep t le_rfl

private lemma parity_map_uniform {m t : ℕ} (g : Fin t → (Fin m → Bool))
    (hind : LinearIndependent (ZMod 2) (fun a => toZ2 (g a))) :
    let v : (Fin m → Bool) → (Fin t → Bool) := fun f a =>
      decide (((Finset.univ : Finset (Fin m)).filter (fun i => f i && g a i)).card % 2 = 1)
    ∃ c : ℕ, 2 ^ t * c = 2 ^ m ∧
      ∀ w : Fin t → Bool, ((Finset.univ : Finset (Fin m → Bool)).filter (fun f => v f = w)).card = c := by
  intro v
  let Gmat : Matrix (Fin t) (Fin m) (ZMod 2) := Matrix.of fun a i => toZ2 (g a) i
  have hT_inj : Function.Injective Gmat.transpose.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    funext a
    revert a
    apply Fintype.linearIndependent_iff.mp hind c
    funext i
    have hi := congrFun hc i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Gmat, Matrix.of_apply, Pi.zero_apply] at hi
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    simpa [mul_comm] using hi
  have hTrank : Gmat.transpose.rank = t := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hT_inj, Module.finrank_pi, Fintype.card_fin]
  have hGrank : Gmat.rank = t := by
    rw [← Matrix.rank_transpose, hTrank]
  have hrange : LinearMap.range Gmat.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hGrank, Module.finrank_pi, Fintype.card_fin]
  have hsurj : Function.Surjective Gmat.mulVecLin := by
    intro y
    have hy : y ∈ LinearMap.range Gmat.mulVecLin := by rw [hrange]; trivial
    exact LinearMap.mem_range.mp hy
  have hv_eq : ∀ f : Fin m → Bool, toZ2 (v f) = Gmat.mulVecLin (toZ2 f) := by
    intro f
    funext a
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Gmat, Matrix.of_apply]
    have hcomm : (∑ i : Fin m, toZ2 (g a) i * toZ2 f i) = ∑ i : Fin m, toZ2 f i * toZ2 (g a) i := by
      apply Finset.sum_congr rfl; intro i _; exact mul_comm _ _
    rw [hcomm]
    by_cases hodd : ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g a i)).card % 2 = 1
    · have hl : toZ2 (v f) a = 1 := by
        dsimp only [toZ2, v]
        simp only [decide_eq_true_eq, hodd, ite_true]
      rw [hl]
      exact ((odd_iff_dotZ2 f (g a)).mp hodd).symm
    · have hl : toZ2 (v f) a = 0 := by
        dsimp only [toZ2, v]
        simp only [decide_eq_true_eq, hodd, ite_false]
      rw [hl]
      have hne1 : (∑ i : Fin m, toZ2 f i * toZ2 (g a) i) ≠ 1 :=
        fun h1 => hodd ((odd_iff_dotZ2 f (g a)).mpr h1)
      have h01 : (∑ i : Fin m, toZ2 f i * toZ2 (g a) i) = 0 ∨
          (∑ i : Fin m, toZ2 f i * toZ2 (g a) i) = 1 := by
        set z := ∑ i : Fin m, toZ2 f i * toZ2 (g a) i
        have hv : z.val = 0 ∨ z.val = 1 := by have := z.val_lt; omega
        rcases hv with h0 | h1
        · left; exact ZMod.val_injective 2 (by rw [h0]; rfl)
        · right; exact ZMod.val_injective 2 (by rw [h1]; rfl)
      rcases h01 with h0 | h1
      · exact h0.symm
      · exact absurd h1 hne1
  let K : Finset (Fin m → ZMod 2) := Finset.univ.filter (fun x => Gmat.mulVecLin x = 0)
  have hfib : ∀ w : Fin t → Bool,
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun f => v f = w)).card = K.card := by
    intro w
    rcases hsurj (toZ2 w) with ⟨x0, hx0⟩
    refine Finset.card_bij'
      (fun f _ => toZ2 f - x0)
      (fun x _ => fromZ2 (x + x0)) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, K] at hf ⊢
      rw [map_sub, ← hv_eq f, hf, hx0, sub_self]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, K] at hx ⊢
      apply (equivZ2 t).injective
      change toZ2 (v (fromZ2 (x + x0))) = toZ2 w
      rw [hv_eq, toZ2_fromZ2, map_add, hx, hx0, zero_add]
    · intro f _
      simp only [sub_add_cancel, fromZ2_toZ2]
    · intro x _
      simp only [toZ2_fromZ2, add_sub_cancel_right]
  refine ⟨K.card, ?_, hfib⟩
  have hsum : (∑ w : Fin t → Bool,
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun f => v f = w)).card) = 2 ^ m := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have h1 : ∀ f : Fin m → Bool, (∑ w : Fin t → Bool, if v f = w then 1 else 0) = 1 := by
      intro f
      rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    rw [Finset.sum_congr rfl (fun f _ => h1 f), Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at hsum
  exact hsum

-- =========================================================================
-- Part 2: Sign-pattern Sauer-Shelah bound via matrix rank
-- =========================================================================

private lemma card_powerset_card_le {t r : ℕ} :
    ((Finset.univ : Finset (Fin t)).powerset.filter (fun S => S.card ≤ r)).card =
      (Finset.range (r + 1)).sum (fun i => Nat.choose t i) := by
  have heq : (Finset.univ : Finset (Fin t)).powerset.filter (fun S => S.card ≤ r) =
      (Finset.range (r + 1)).biUnion (fun i => (Finset.univ : Finset (Fin t)).powersetCard i) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard, Nat.lt_succ_iff]
    exact ⟨fun h => ⟨S.card, h, rfl⟩, fun ⟨i, hi, hcard⟩ => hcard ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro i _ j _ hij
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro S hSi hSj
    have hi := (Finset.mem_powersetCard.mp hSi).2
    have hj := (Finset.mem_powersetCard.mp hSj).2
    exact hij (hi.symm.trans hj)

private lemma sign_patterns_card_le {m t : ℕ}
    (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ) (hA : ∀ f u, A f u ≠ 0)
    (g : Fin t → (Fin m → Bool)) :
    let signSet : (Fin m → Bool) → Finset (Fin t) :=
      fun f => Finset.univ.filter (fun a => 0 < A f (g a))
    ((Finset.univ : Finset (Fin m → Bool)).image signSet).card ≤
      (Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i) := by
  intro signSet
  let B : Matrix (Fin m → Bool) (Fin t) ℝ := fun f a => A f (g a)
  have hB_le_A : B.rank ≤ A.rank := by
    unfold Matrix.rank
    apply Submodule.finrank_mono
    rintro _ ⟨y, rfl⟩
    let z : (Fin m → Bool) → ℝ := fun u => ∑ a : Fin t, if g a = u then y a else 0
    refine ⟨z, ?_⟩
    funext f
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, z, B]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    have h1 : (∑ u : Fin m → Bool, A f u * if g a = u then y a else 0) =
        ∑ u : Fin m → Bool, if g a = u then A f (g a) * y a else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      by_cases hgu : g a = u
      · rw [if_pos hgu, if_pos hgu, hgu]
      · rw [if_neg hgu, if_neg hgu, mul_zero]
    rw [h1, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  let V : Submodule ℝ (Fin t → ℝ) := LinearMap.range B.transpose.mulVecLin
  have hV_dim : Module.finrank ℝ V ≤ A.rank := by
    have h1 : Module.finrank ℝ V = B.transpose.rank := rfl
    rw [h1, Matrix.rank_transpose]
    exact hB_le_A
  have hrow_mem : ∀ f : Fin m → Bool, B f ∈ V := by
    intro f
    refine ⟨Pi.single f 1, ?_⟩
    funext a
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.sum_eq_single f]
    · simp
    · intro f' _ hf'; simp [Pi.single_eq_of_ne hf']
    · intro hni; exact absurd (Finset.mem_univ f) hni
  let 𝒜 : Finset (Finset (Fin t)) := Finset.univ.image signSet
  have hshat_le : ∀ S ∈ 𝒜.shatterer, S.card ≤ A.rank := by
    intro S hS
    rw [Finset.mem_shatterer] at hS
    by_contra hgt
    have hlt : A.rank < S.card := by omega
    let res : V →ₗ[ℝ] ({a : Fin t // a ∈ S} → ℝ) :=
      { toFun := fun u i => u.1 i.1
        map_add' := fun u v => rfl
        map_smul' := fun r u => rfl }
    have hres_dim : Module.finrank ℝ (LinearMap.range res) < Module.finrank ℝ ({a : Fin t // a ∈ S} → ℝ) := by
      have h1 : Module.finrank ℝ (LinearMap.range res) ≤ Module.finrank ℝ V :=
        LinearMap.finrank_range_le res
      have h2 : Module.finrank ℝ ({a : Fin t // a ∈ S} → ℝ) = S.card := by
        rw [Module.finrank_pi, Fintype.card_coe]
      omega
    have hne_top : LinearMap.range res ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top] at hres_dim
      exact lt_irrefl _ hres_dim
    rcases Submodule.exists_isCompl (LinearMap.range res) with ⟨W, hcompl⟩
    have hW_ne : W ≠ ⊥ := by
      intro hbot
      apply hne_top
      have htop := hcompl.sup_eq_top
      rw [hbot, sup_bot_eq] at htop
      exact htop
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hW_ne with ⟨w0, hw0W, hw0_ne⟩
    have hex_i0 : ∃ i0 : {a : Fin t // a ∈ S}, w0 i0 ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw0_ne (funext hall)
    rcases hex_i0 with ⟨i0, hi0⟩
    let φ : ({a : Fin t // a ∈ S} → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj i0).comp (W.subtype.comp (W.linearProjOfIsCompl (LinearMap.range res) hcompl.symm))
    have hφ_w0 : φ w0 ≠ 0 := by
      have h1 : W.linearProjOfIsCompl (LinearMap.range res) hcompl.symm w0 = ⟨w0, hw0W⟩ :=
        Submodule.linearProjOfIsCompl_apply_left hcompl.symm ⟨w0, hw0W⟩
      simp only [φ, LinearMap.comp_apply, h1, Submodule.coe_subtype, LinearMap.proj_apply]
      exact hi0
    have hφ_zero : ∀ u : V, φ (res u) = 0 := by
      intro u
      have hmem : res u ∈ LinearMap.range res := ⟨u, rfl⟩
      have h1 : W.linearProjOfIsCompl (LinearMap.range res) hcompl.symm (res u) = 0 :=
        Submodule.linearProjOfIsCompl_apply_right hcompl.symm ⟨res u, hmem⟩
      simp only [φ, LinearMap.comp_apply, h1, map_zero]
    let c : {a : Fin t // a ∈ S} → ℝ := fun i => φ (Pi.single i 1)
    have hφ_eq : ∀ y : {a : Fin t // a ∈ S} → ℝ, φ y = ∑ i : {a : Fin t // a ∈ S}, y i * c i := by
      intro y
      have hy : y = ∑ i : {a : Fin t // a ∈ S}, y i • Pi.single i (1 : ℝ) := by
        funext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hij; simp [Pi.single_eq_of_ne (Ne.symm hij)]
        · intro hni; exact absurd (Finset.mem_univ j) hni
      conv_lhs => rw [hy]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul]
    have hex_c : ∃ i1 : {a : Fin t // a ∈ S}, c i1 ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hφ_w0
      rw [hφ_eq w0]
      exact Finset.sum_eq_zero (fun i _ => by rw [hall i, mul_zero])
    rcases hex_c with ⟨i1, hi1⟩
    let T : Finset (Fin t) := S.filter (fun a => ∃ ha : a ∈ S, 0 < c ⟨a, ha⟩)
    have hTS : T ⊆ S := Finset.filter_subset _ _
    rcases hS hTS with ⟨U, hU𝒜, hSU⟩
    rcases Finset.mem_image.mp hU𝒜 with ⟨f, _, rfl⟩
    have hsign_iff : ∀ i : {a : Fin t // a ∈ S}, 0 < B f i.1 ↔ 0 < c i := by
      intro i
      have h1 : i.1 ∈ S ∩ signSet f ↔ i.1 ∈ T := by rw [hSU]
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, signSet, T] at h1
      constructor
      · intro hpos
        rcases (h1.mp ⟨i.2, hpos⟩).2 with ⟨ha, hc⟩
        exact hc
      · intro hc
        exact (h1.mpr ⟨i.2, i.2, hc⟩).2
    have hterm_nonneg : ∀ i : {a : Fin t // a ∈ S}, 0 ≤ B f i.1 * c i := by
      intro i
      rcases lt_trichotomy (c i) 0 with hneg | hzero | hpos
      · have hnot : ¬ 0 < B f i.1 := fun hp => not_lt.mpr (le_of_lt hneg) ((hsign_iff i).mp hp)
        have hBneg : B f i.1 < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hA f (g i.1))
        exact le_of_lt (mul_pos_of_neg_of_neg hBneg hneg)
      · rw [hzero, mul_zero]
      · exact le_of_lt (mul_pos ((hsign_iff i).mpr hpos) hpos)
    have hterm_pos : 0 < B f i1.1 * c i1 := by
      rcases lt_or_gt_of_ne hi1 with hneg | hpos
      · have hnot : ¬ 0 < B f i1.1 := fun hp => not_lt.mpr (le_of_lt hneg) ((hsign_iff i1).mp hp)
        have hBneg : B f i1.1 < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hA f (g i1.1))
        exact mul_pos_of_neg_of_neg hBneg hneg
      · exact mul_pos ((hsign_iff i1).mpr hpos) hpos
    have hsum_pos : 0 < ∑ i : {a : Fin t // a ∈ S}, B f i.1 * c i :=
      Finset.sum_pos' (fun i _ => hterm_nonneg i) ⟨i1, Finset.mem_univ i1, hterm_pos⟩
    have hsum_zero : (∑ i : {a : Fin t // a ∈ S}, B f i.1 * c i) = 0 := by
      have h1 : (∑ i : {a : Fin t // a ∈ S}, B f i.1 * c i) =
          ∑ i : {a : Fin t // a ∈ S}, res ⟨B f, hrow_mem f⟩ i * c i := rfl
      rw [h1, ← hφ_eq (res ⟨B f, hrow_mem f⟩)]
      exact hφ_zero ⟨B f, hrow_mem f⟩
    linarith
  have hsub : 𝒜.shatterer ⊆ (Finset.univ : Finset (Fin t)).powerset.filter (fun S => S.card ≤ A.rank) := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
    exact hshat_le S hS
  calc 𝒜.card ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ((Finset.univ : Finset (Fin t)).powerset.filter (fun S => S.card ≤ A.rank)).card :=
        Finset.card_le_card hsub
    _ = (Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i) := card_powerset_card_le

-- =========================================================================
-- Part 3: Hamming generating function and integer AM-GM
-- =========================================================================

private def hdist {t : ℕ} (W U : Finset (Fin t)) : ℕ :=
  ((Finset.univ : Finset (Fin t)).filter (fun a => ¬ (a ∈ W ↔ a ∈ U))).card

private lemma hdist_le {t : ℕ} (W U : Finset (Fin t)) : hdist W U ≤ t := by
  calc hdist W U ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_filter_le _ _
    _ = t := by simp

private lemma sum_pow_hdist {t : ℕ} (U : Finset (Fin t)) (q : ℕ) :
    (∑ W : Finset (Fin t), q ^ (t - hdist W U)) = (q + 1) ^ t := by
  have hmatch : ∀ W : Finset (Fin t),
      t - hdist W U = ((Finset.univ : Finset (Fin t)).filter (fun a => a ∈ W ↔ a ∈ U)).card := by
    intro W
    have htot : ((Finset.univ : Finset (Fin t)).filter (fun a => a ∈ W ↔ a ∈ U)).card +
        ((Finset.univ : Finset (Fin t)).filter (fun a => ¬ (a ∈ W ↔ a ∈ U))).card = t := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      have h1 : ∀ a : Fin t, (if a ∈ W ↔ a ∈ U then 1 else 0) + (if ¬ (a ∈ W ↔ a ∈ U) then 1 else 0) = 1 := by
        intro a; by_cases h : a ∈ W ↔ a ∈ U <;> simp [h]
      rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one]
    dsimp only [hdist]; omega
  rw [Finset.sum_congr rfl (fun W _ => by rw [hmatch W])]
  have hbij : (∑ W : Finset (Fin t), q ^ ((Finset.univ : Finset (Fin t)).filter (fun a => a ∈ W ↔ a ∈ U)).card) =
      ∑ S : Finset (Fin t), q ^ S.card := by
    refine Finset.sum_bij'
      (fun W _ => Finset.univ.filter (fun a => a ∈ W ↔ a ∈ U))
      (fun S _ => Finset.univ.filter (fun a => a ∈ S ↔ a ∈ U))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
    · intro W _
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hU : a ∈ U <;> simp [hU]
    · intro S _
      ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hU : a ∈ U <;> simp [hU]
  rw [hbij]
  have hgroup : (∑ S : Finset (Fin t), q ^ S.card) =
      ∑ i ∈ Finset.range (t + 1), ∑ S ∈ (Finset.univ : Finset (Fin t)).powersetCard i, q ^ S.card := by
    rw [← Finset.sum_biUnion]
    · congr 1; ext S
      simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard,
        Finset.subset_univ, true_and, true_iff]
      refine ⟨S.card, ?_, rfl⟩
      have : S.card ≤ t := by
        calc S.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_le_univ S
          _ = t := by simp
      omega
    · intro i _ j _ hij
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro S hSi hSj
      exact hij ((Finset.mem_powersetCard.mp hSi).2.symm.trans (Finset.mem_powersetCard.mp hSj).2)
  rw [hgroup]
  have hterm : ∀ i ∈ Finset.range (t + 1),
      (∑ S ∈ (Finset.univ : Finset (Fin t)).powersetCard i, q ^ S.card) =
        q ^ i * 1 ^ (t - i) * Nat.choose t i := by
    intro i _
    have h1 : ∀ S ∈ (Finset.univ : Finset (Fin t)).powersetCard i, q ^ S.card = q ^ i :=
      fun S hS => by rw [(Finset.mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_pow, mul_one, mul_comm]
  rw [Finset.sum_congr rfl hterm]
  simpa using (add_pow q 1 t).symm

private lemma nat_am_gm {ι : Type*} [Fintype ι] (hpos : 0 < Fintype.card ι) (a : ι → ℕ) :
    (Fintype.card ι) ^ (Fintype.card ι) * (∏ i : ι, a i) ≤ (∑ i : ι, a i) ^ (Fintype.card ι) := by
  set n := Fintype.card ι
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hpos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have ham := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (n : ℝ)⁻¹) (fun i => (a i : ℝ))
    (fun _ _ => inv_nonneg.mpr (le_of_lt hn_pos))
    (by simp [Finset.card_univ, n, mul_inv_cancel₀ hn_ne])
    (fun i _ => Nat.cast_nonneg (a i))
  have hlhs_nonneg : 0 ≤ ∏ i : ι, (a i : ℝ) ^ (n : ℝ)⁻¹ :=
    Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hpow := pow_le_pow_left₀ hlhs_nonneg ham n
  have hlhs_eq : (∏ i : ι, (a i : ℝ) ^ (n : ℝ)⁻¹) ^ n = ∏ i : ι, (a i : ℝ) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), inv_mul_cancel₀ hn_ne, Real.rpow_one]
  have hrhs_eq : (∑ i : ι, (n : ℝ)⁻¹ * (a i : ℝ)) ^ n =
      ((n : ℝ) ^ n)⁻¹ * (∑ i : ι, (a i : ℝ)) ^ n := by
    rw [← Finset.mul_sum, mul_pow, inv_pow]
  rw [hlhs_eq, hrhs_eq] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow (pow_nonneg (le_of_lt hn_pos) n)
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hn_ne), one_mul] at hmul
  have hcast : ((n ^ n * ∏ i : ι, a i : ℕ) : ℝ) ≤ (((∑ i : ι, a i) ^ n : ℕ) : ℝ) := by
    push_cast; exact hmul
  exact Nat.cast_le.mp hcast

-- =========================================================================
-- Part 4: Main core theorem (without local letI)
-- =========================================================================

private lemma binom_tail_12 {r : ℕ} :
    11 ^ (11 * r) * (Finset.range (r + 1)).sum (fun i => Nat.choose (12 * r) i) ≤ 12 ^ (12 * r) := by
  have hpow := add_pow 1 11 (12 * r)
  have h12 : (1 + 11 : ℕ) = 12 := rfl
  rw [h12] at hpow
  have hsub : Finset.range (r + 1) ⊆ Finset.range (12 * r + 1) :=
    Finset.range_mono (by omega)
  calc 11 ^ (11 * r) * (Finset.range (r + 1)).sum (fun i => Nat.choose (12 * r) i)
      = (Finset.range (r + 1)).sum (fun i => 11 ^ (11 * r) * Nat.choose (12 * r) i) :=
        Finset.mul_sum ..
    _ ≤ (Finset.range (r + 1)).sum (fun i => 1 ^ i * 11 ^ (12 * r - i) * Nat.choose (12 * r) i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [one_pow, one_mul]
        exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ (Finset.range (12 * r + 1)).sum (fun i => 1 ^ i * 11 ^ (12 * r - i) * Nat.choose (12 * r) i) :=
        Finset.sum_le_sum_of_subset hsub
    _ = 12 ^ (12 * r) := hpow.symm

private noncomputable def M_core (m k : ℕ) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ) : ℕ :=
  ((Finset.univ : Finset (Fin m → Bool)).filter (fun g =>
    ((Finset.univ : Finset (Fin m → Bool)).filter (fun f =>
      ¬ ((0 < A f g) ↔
        ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1))).card ≤ k)).card

private noncomputable def rankCore {m : ℕ} (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ) : ℕ :=
  A.rank

private lemma main_core (m k : ℕ) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ)
    (hA : ∀ f g, A f g ≠ 0) :
    (∀ t q : ℕ, 0 < t → 2 ^ (t - 1) < M_core m k A → 1 ≤ q →
      (2 * q) ^ (t * 2 ^ m) ≤ q ^ (t * k) *
        ((q + 1) ^ t * ((Finset.range (rankCore A + 1)).sum (fun i => Nat.choose t i))) ^ 2 ^ m) ∧
    (8 * k ≤ 2 ^ m → M_core m k A ≤ 2 ^ (12 * rankCore A - 1)) := by
  let words := (Finset.univ : Finset (Fin m → Bool))
  let odd := fun (f g : Fin m → Bool) =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
  let mistakes := fun g => (words.filter (fun f => ¬ ((0 < A f g) ↔ odd f g))).card
  let M := M_core m k A
  let N := 2 ^ m
  change (∀ t q : ℕ, 0 < t → 2 ^ (t - 1) < M → 1 ≤ q →
      (2 * q) ^ (t * N) ≤ q ^ (t * k) *
        ((q + 1) ^ t * ((Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i))) ^ N) ∧
    (8 * k ≤ N → M ≤ 2 ^ (12 * A.rank - 1))
  have hpart1 : ∀ t q : ℕ, 0 < t → 2 ^ (t - 1) < M → 1 ≤ q →
      (2 * q) ^ (t * N) ≤ q ^ (t * k) *
        ((q + 1) ^ t * ((Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i))) ^ N := by
    intro t q ht hM hq
    let G : Finset (Fin m → Bool) := words.filter (fun g => mistakes g ≤ k)
    rcases exists_linIndep_Z2 G hM with ⟨g, hgG, hind⟩
    rcases parity_map_uniform g hind with ⟨c, hc_mul, hfib⟩
    let v : (Fin m → Bool) → (Fin t → Bool) := fun f a => decide (odd f (g a))
    let toSet : (Fin t → Bool) → Finset (Fin t) := fun w => Finset.univ.filter (fun a => w a = true)
    let signSet : (Fin m → Bool) → Finset (Fin t) := fun f => Finset.univ.filter (fun a => 0 < A f (g a))
    let 𝒜 : Finset (Finset (Fin t)) := words.image signSet
    have h𝒜_ne : 𝒜.Nonempty := ⟨signSet (fun _ => false), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩
    have h𝒜_card : 𝒜.card ≤ (Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i) :=
      sign_patterns_card_le A hA g
    have hmin_ex : ∀ W : Finset (Fin t), ∃ U ∈ 𝒜, ∀ U' ∈ 𝒜, hdist W U ≤ hdist W U' :=
      fun W => Finset.exists_min_image 𝒜 (hdist W) h𝒜_ne
    let bestU : Finset (Fin t) → Finset (Fin t) := fun W => Classical.choose (hmin_ex W)
    have hbestU_mem : ∀ W, bestU W ∈ 𝒜 := fun W => (Classical.choose_spec (hmin_ex W)).1
    have hbestU_min : ∀ W, ∀ U' ∈ 𝒜, hdist W (bestU W) ≤ hdist W U' :=
      fun W => (Classical.choose_spec (hmin_ex W)).2
    let d : Finset (Fin t) → ℕ := fun W => hdist W (bestU W)
    have hd_le_t : ∀ W, d W ≤ t := fun W => hdist_le W (bestU W)
    have hsum_d_pow : (∑ W : Finset (Fin t), q ^ (t - d W)) ≤ (q + 1) ^ t * 𝒜.card := by
      have h1 : (∑ W : Finset (Fin t), q ^ (t - d W)) ≤
          ∑ W : Finset (Fin t), ∑ U ∈ 𝒜, q ^ (t - hdist W U) := by
        apply Finset.sum_le_sum
        intro W _
        exact Finset.single_le_sum (f := fun U => q ^ (t - hdist W U)) (fun _ _ => Nat.zero_le _) (hbestU_mem W)
      have h2 : (∑ W : Finset (Fin t), ∑ U ∈ 𝒜, q ^ (t - hdist W U)) = (q + 1) ^ t * 𝒜.card := by
        rw [Finset.sum_comm]
        rw [Finset.sum_congr rfl (fun U _ => sum_pow_hdist U q), Finset.sum_const, smul_eq_mul, mul_comm]
      exact le_trans h1 (le_of_eq h2)
    have ham := nat_am_gm (ι := Finset (Fin t)) (by simp [Fintype.card_finset]) (fun W => q ^ (t - d W))
    have hcard_fs : Fintype.card (Finset (Fin t)) = 2 ^ t := by simp [Fintype.card_finset]
    rw [hcard_fs] at ham
    have ham2 : (2 ^ t) ^ (2 ^ t) * (∏ W : Finset (Fin t), q ^ (t - d W)) ≤
        ((q + 1) ^ t * 𝒜.card) ^ (2 ^ t) :=
      le_trans ham (Nat.pow_le_pow_left hsum_d_pow (2 ^ t))
    have hpow_c := Nat.pow_le_pow_left ham2 c
    rw [mul_pow, ← pow_mul (2 ^ t), hc_mul, ← pow_mul ((q + 1) ^ t * 𝒜.card), hc_mul] at hpow_c
    have hprod_eq : (∏ W : Finset (Fin t), q ^ (t - d W)) ^ c =
        q ^ (∑ f ∈ words, (t - d (toSet (v f)))) := by
      rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
      congr 1
      have hfib_set : ∀ W : Finset (Fin t),
          (words.filter (fun f => toSet (v f) = W)).card = c := by
        intro W
        let wW : Fin t → Bool := fun a => decide (a ∈ W)
        have hEq : words.filter (fun f => toSet (v f) = W) = words.filter (fun f => v f = wW) := by
          ext f
          simp only [words, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h; funext a
            have ha := Finset.ext_iff.mp h a
            simp only [toSet, Finset.mem_filter, Finset.mem_univ, true_and] at ha
            dsimp only [wW]
            cases hv : v f a <;> simp [hv] at ha ⊢ <;> exact ha
          · intro h; ext a
            simp only [toSet, Finset.mem_filter, Finset.mem_univ, true_and, h, wW, decide_eq_true_eq]
        rw [hEq]
        exact hfib wW
      have hgroup : (∑ f ∈ words, (t - d (toSet (v f)))) =
          ∑ W : Finset (Fin t), ∑ f ∈ words.filter (fun f => toSet (v f) = W), (t - d (toSet (v f))) := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext f; simp
        · intro W1 _ W2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro f h1 h2
          simp only [Finset.mem_filter] at h1 h2
          exact hne (h1.2.symm.trans h2.2)
      rw [hgroup]
      have hinner : ∀ W : Finset (Fin t),
          (∑ f ∈ words.filter (fun f => toSet (v f) = W), (t - d (toSet (v f)))) =
            (t - d W) * c := by
        intro W
        rw [Finset.sum_congr rfl (fun f hf => by rw [(Finset.mem_filter.mp hf).2]),
          Finset.sum_const, hfib_set W, smul_eq_mul, mul_comm]
      rw [Finset.sum_congr rfl (fun W _ => hinner W), ← Finset.sum_mul]
    rw [hprod_eq] at hpow_c
    have hsum_add : (∑ f ∈ words, (t - d (toSet (v f)))) + (∑ f ∈ words, d (toSet (v f))) = t * N := by
      rw [← Finset.sum_add_distrib]
      have h1 : ∀ f ∈ words, (t - d (toSet (v f))) + d (toSet (v f)) = t :=
        fun f _ => Nat.sub_add_cancel (hd_le_t _)
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
        Fintype.card_bool, Fintype.card_fin, smul_eq_mul, mul_comm]
    have hmul_q := Nat.mul_le_mul_right (q ^ (∑ f ∈ words, d (toSet (v f)))) hpow_c
    have hlhs_simp : (2 ^ t) ^ N * q ^ (∑ f ∈ words, (t - d (toSet (v f)))) *
        q ^ (∑ f ∈ words, d (toSet (v f))) = (2 * q) ^ (t * N) := by
      rw [mul_assoc, ← pow_add, hsum_add, ← pow_mul, mul_pow]
    rw [hlhs_simp] at hmul_q
    have hsum_d_le : (∑ f ∈ words, d (toSet (v f))) ≤ t * k := by
      have h1 : (∑ f ∈ words, d (toSet (v f))) ≤ ∑ f ∈ words, hdist (toSet (v f)) (signSet f) := by
        apply Finset.sum_le_sum
        intro f _
        exact hbestU_min (toSet (v f)) (signSet f) (Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩)
      have h2 : (∑ f ∈ words, hdist (toSet (v f)) (signSet f)) = ∑ a : Fin t, mistakes (g a) := by
        have hrow : ∀ f ∈ words, hdist (toSet (v f)) (signSet f) =
            ((Finset.univ : Finset (Fin t)).filter (fun a => ¬ ((0 < A f (g a)) ↔ odd f (g a)))).card := by
          intro f _
          dsimp only [hdist]
          congr 1; ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, toSet, signSet, v, decide_eq_true_eq]
          exact not_congr iff_comm
        rw [Finset.sum_congr rfl hrow]
        simp only [mistakes, Finset.card_filter]
        exact Finset.sum_comm
      have h3 : (∑ a : Fin t, mistakes (g a)) ≤ t * k := by
        calc (∑ a : Fin t, mistakes (g a)) ≤ ∑ _a : Fin t, k := by
              apply Finset.sum_le_sum
              intro a _
              exact (Finset.mem_filter.mp (hgG a)).2
          _ = t * k := by simp [Finset.sum_const, smul_eq_mul]
      omega
    have hq_le : q ^ (∑ f ∈ words, d (toSet (v f))) ≤ q ^ (t * k) :=
      Nat.pow_le_pow_right hq hsum_d_le
    have hbase_le : (q + 1) ^ t * 𝒜.card ≤
        (q + 1) ^ t * (Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i) :=
      Nat.mul_le_mul_left _ h𝒜_card
    calc (2 * q) ^ (t * N)
        ≤ ((q + 1) ^ t * 𝒜.card) ^ N * q ^ (∑ f ∈ words, d (toSet (v f))) := hmul_q
      _ = q ^ (∑ f ∈ words, d (toSet (v f))) * ((q + 1) ^ t * 𝒜.card) ^ N := mul_comm _ _
      _ ≤ q ^ (t * k) * ((q + 1) ^ t * (Finset.range (A.rank + 1)).sum (fun i => Nat.choose t i)) ^ N :=
          Nat.mul_le_mul hq_le (Nat.pow_le_pow_left hbase_le N)
  refine ⟨hpart1, ?_⟩
  intro h8k
  set r := A.rank
  have hr_pos : 1 ≤ r := by
    by_contra hr0
    have hreq : A.rank = 0 := by omega
    have hbot : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hreq
    let f0 : Fin m → Bool := fun _ => false
    have hmem : A.mulVecLin (Pi.single f0 1) ∈ LinearMap.range A.mulVecLin := ⟨Pi.single f0 1, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have hval := congrFun hmem f0
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at hval
    rw [Finset.sum_eq_single f0] at hval
    · simp only [Pi.single_eq_same, mul_one] at hval
      exact hA f0 f0 hval
    · intro u _ hu; simp [Pi.single_eq_of_ne hu]
    · intro hni; exact absurd (Finset.mem_univ f0) hni
  by_contra hMgt
  have hMlt : 2 ^ (12 * r - 1) < M := by omega
  have h1 := hpart1 (12 * r) 7 (by omega) hMlt (by omega)
  set S := (Finset.range (r + 1)).sum (fun i => Nat.choose (12 * r) i)
  have hpow8 := Nat.pow_le_pow_left h1 8
  have hNpos : 0 < N := pow_pos (by omega) m
  have h7k : 7 ^ (12 * r * k * 8) ≤ 7 ^ (12 * r * N) :=
    Nat.pow_le_pow_right (by omega) (by have := Nat.mul_le_mul_left (12 * r) h8k; linarith)
  have hstep1 : ((2 * 7) ^ (12 * r * 8)) ^ N ≤ (7 ^ (12 * r) * ((7 + 1) ^ (12 * r) * S) ^ 8) ^ N := by
    have hl : ((2 * 7) ^ (12 * r * N)) ^ 8 = ((2 * 7) ^ (12 * r * 8)) ^ N := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    have hr1 : (7 ^ (12 * r * k) * ((7 + 1) ^ (12 * r) * S) ^ N) ^ 8 =
        7 ^ (12 * r * k * 8) * (((7 + 1) ^ (12 * r) * S) ^ 8) ^ N := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; congr 2; ring
    have hr2 : (7 ^ (12 * r) * ((7 + 1) ^ (12 * r) * S) ^ 8) ^ N =
        7 ^ (12 * r * N) * (((7 + 1) ^ (12 * r) * S) ^ 8) ^ N := by
      rw [mul_pow, ← pow_mul]
    rw [hl, hr1] at hpow8
    rw [hr2]
    exact le_trans hpow8 (Nat.mul_le_mul_right _ h7k)
  have hstep2 : (2 * 7) ^ (12 * r * 8) ≤ 7 ^ (12 * r) * ((7 + 1) ^ (12 * r) * S) ^ 8 := by
    by_contra hgt
    have hlt := Nat.pow_lt_pow_left (by omega : 7 ^ (12 * r) * ((7 + 1) ^ (12 * r) * S) ^ 8 < (2 * 7) ^ (12 * r * 8)) (by omega : N ≠ 0)
    omega
  have hcancel : 7 ^ (12 * r) * (7 ^ (84 * r) * 2 ^ (96 * r)) ≤
      7 ^ (12 * r) * (2 ^ (288 * r) * S ^ 8) := by
    have hl : 7 ^ (12 * r) * (7 ^ (84 * r) * 2 ^ (96 * r)) = (2 * 7) ^ (12 * r * 8) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, show 12 * r + 84 * r = 12 * r * 8 by ring,
        show 96 * r = 12 * r * 8 by ring, mul_comm]
    have hr : 7 ^ (12 * r) * (2 ^ (288 * r) * S ^ 8) =
        7 ^ (12 * r) * ((7 + 1) ^ (12 * r) * S) ^ 8 := by
      congr 1
      rw [mul_pow, ← pow_mul, show (7 + 1 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul,
        show 3 * (12 * r * 8) = 288 * r by ring]
    rw [hl, hr]; exact hstep2
  have hstep3 : 7 ^ (84 * r) * 2 ^ (96 * r) ≤ 2 ^ (288 * r) * S ^ 8 :=
    Nat.le_of_mul_le_mul_left hcancel (pow_pos (by omega) _)
  have hcancel2 : 2 ^ (96 * r) * 7 ^ (84 * r) ≤ 2 ^ (96 * r) * (2 ^ (192 * r) * S ^ 8) := by
    rw [mul_comm (2 ^ (96 * r)) (7 ^ (84 * r)), ← mul_assoc, ← pow_add,
      show 96 * r + 192 * r = 288 * r by ring]
    exact hstep3
  have hstep4 : 7 ^ (84 * r) ≤ 2 ^ (192 * r) * S ^ 8 :=
    Nat.le_of_mul_le_mul_left hcancel2 (pow_pos (by omega) _)
  have htail8 : 11 ^ (88 * r) * S ^ 8 ≤ 12 ^ (96 * r) := by
    have h8 := Nat.pow_le_pow_left (binom_tail_12 (r := r)) 8
    rw [mul_pow, ← pow_mul, ← pow_mul, show 11 * r * 8 = 88 * r by ring,
      show 12 * r * 8 = 96 * r by ring] at h8
    exact h8
  have hstep5 : 7 ^ (84 * r) * 11 ^ (88 * r) ≤ 2 ^ (192 * r) * 12 ^ (96 * r) := by
    calc 7 ^ (84 * r) * 11 ^ (88 * r)
        ≤ (2 ^ (192 * r) * S ^ 8) * 11 ^ (88 * r) := Nat.mul_le_mul_right _ hstep4
      _ = 2 ^ (192 * r) * (11 ^ (88 * r) * S ^ 8) := by ring
      _ ≤ 2 ^ (192 * r) * 12 ^ (96 * r) := Nat.mul_le_mul_left _ htail8
  have hnum : 2 ^ 48 * 12 ^ 24 < 7 ^ 21 * 11 ^ 22 := by norm_num
  have hbig : (2 ^ 48 * 12 ^ 24) ^ (4 * r) < (7 ^ 21 * 11 ^ 22) ^ (4 * r) :=
    Nat.pow_lt_pow_left hnum (by omega)
  have hl_eq : (2 ^ 48 * 12 ^ 24) ^ (4 * r) = 2 ^ (192 * r) * 12 ^ (96 * r) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, show 48 * (4 * r) = 192 * r by ring,
      show 24 * (4 * r) = 96 * r by ring]
  have hr_eq : (7 ^ 21 * 11 ^ 22) ^ (4 * r) = 7 ^ (84 * r) * 11 ^ (88 * r) := by
    rw [mul_pow, ← pow_mul, ← pow_mul, show 21 * (4 * r) = 84 * r by ring,
      show 22 * (4 * r) = 88 * r by ring]
  rw [hl_eq, hr_eq] at hbig
  omega

private lemma card_filter_univ_congr {α : Type*} {f1 f2 : Fintype α} {P Q : α → Prop}
    {d1 : DecidablePred P} {d2 : DecidablePred Q} (h : ∀ x : α, P x ↔ Q x) :
    (@Finset.filter α P d1 (@Finset.univ α f1)).card =
    (@Finset.filter α Q d2 (@Finset.univ α f2)).card := by
  have hf : f1 = f2 := Subsingleton.elim f1 f2
  subst hf
  congr 1; ext x; simp only [Finset.mem_filter]; exact and_congr_right (fun _ => h x)

private lemma le_iff_of_eq {a b k : ℕ} (h : a = b) : a ≤ k ↔ b ≤ k := h ▸ Iff.rfl

private lemma mod2_iff_of_eq {a b : ℕ} (h : a = b) : a % 2 = 1 ↔ b % 2 = 1 := h ▸ Iff.rfl

private lemma rank_congr_fintype {m : ℕ} (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ)
    {f1 f2 : Fintype (Fin m → Bool)} :
    @Matrix.rank _ _ ℝ f1 _ A = @Matrix.rank _ _ ℝ f2 _ A := by
  rw [Subsingleton.elim f1 f2]

private lemma main_aux :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m k : Nat) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ),
      (∀ f g, A f g ≠ 0) →
      let words := (Finset.univ : Finset (Fin m → Bool))
      let odd := fun (f g : Fin m → Bool) =>
        ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
      let mistakes := fun g => (words.filter (fun f => ¬ ((0 < A f g) ↔ odd f g))).card
      let M := (words.filter (fun g => mistakes g ≤ k)).card
      let N := 2^m
      (∀ t q : Nat, 0 < t → 2^(t-1) < M → 1 ≤ q →
        (2*q)^(t*N) ≤ q^(t*k) *
          ((q+1)^t * ((Finset.range (A.rank+1)).sum (fun i => Nat.choose t i)))^N) ∧
      (8*k ≤ N → M ≤ 2^(12*A.rank-1)) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro m k A hA words odd mistakes M N
  have hcore := main_core m k A hA
  have hM_eq : M = M_core m k A := by
    dsimp only [M, mistakes, odd, words, M_core]
    refine card_filter_univ_congr fun g => le_iff_of_eq ?_
    refine card_filter_univ_congr fun f => not_congr (iff_congr Iff.rfl (mod2_iff_of_eq ?_))
    exact card_filter_univ_congr fun i => Iff.rfl
  have hrank_eq : A.rank = rankCore A := rank_congr_fintype A
  dsimp only [N]
  rw [hM_eq, hrank_eq]
  exact hcore

end PEqualNP.Outside.L_lib_1272_aux

theorem PEqualNP.Outside.L_lib_1272 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m k : Nat) (A : Matrix (Fin m → Bool) (Fin m → Bool) ℝ),
      (∀ f g, A f g ≠ 0) →
      let words := (Finset.univ : Finset (Fin m → Bool))
      let odd := fun (f g : Fin m → Bool) =>
        ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
      let mistakes := fun g => (words.filter (fun f => ¬ ((0 < A f g) ↔ odd f g))).card
      let M := (words.filter (fun g => mistakes g ≤ k)).card
      let N := 2^m
      (∀ t q : Nat, 0 < t → 2^(t-1) < M → 1 ≤ q →
        (2*q)^(t*N) ≤ q^(t*k) *
          ((q+1)^t * ((Finset.range (A.rank+1)).sum (fun i => Nat.choose t i)))^N) ∧
      (8*k ≤ N → M ≤ 2^(12*A.rank-1)) := by
  exact PEqualNP.Outside.L_lib_1272_aux.main_aux
