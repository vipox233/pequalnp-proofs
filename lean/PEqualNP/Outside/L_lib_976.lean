import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_976_aux

open Classical

/-- Quadratic Boolean function on Fin k -> ZMod 2. -/
private def IsQuad {k : ℕ} (f : (Fin k → ZMod 2) → ZMod 2) : Prop :=
  ∃ (b : ZMod 2) (l : Fin k → ZMod 2) (M : Fin k → Fin k → ZMod 2),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j

private lemma zmod2_mul_self (x : ZMod 2) : x * x = x := by fin_cases x <;> rfl
private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by fin_cases x <;> rfl
private lemma zmod2_neg_eq (x : ZMod 2) : -x = x := by fin_cases x <;> rfl
private lemma zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by fin_cases x <;> fin_cases y <;> rfl
private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma isQuad_const {k : ℕ} (c : ZMod 2) : IsQuad (fun _ : Fin k → ZMod 2 => c) :=
  ⟨c, 0, fun _ _ => 0, fun _ => by simp⟩

private lemma isQuad_coord {k : ℕ} (i : Fin k) : IsQuad (fun s : Fin k → ZMod 2 => s i) := by
  refine ⟨0, Pi.single i 1, fun _ _ => 0, fun s => ?_⟩
  simp [dotProduct, Pi.single_apply]

private lemma isQuad_mul_coord {k : ℕ} (i j : Fin k) :
    IsQuad (fun s : Fin k → ZMod 2 => s i * s j) := by
  refine ⟨0, 0, fun a b => if a = i ∧ b = j then 1 else 0, fun s => ?_⟩
  simp only [zero_add, dotProduct_zero]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

private lemma isQuad_add {k : ℕ} {f g : (Fin k → ZMod 2) → ZMod 2}
    (hf : IsQuad f) (hg : IsQuad g) : IsQuad (fun s => f s + g s) := by
  rcases hf with ⟨b1, l1, M1, hf⟩
  rcases hg with ⟨b2, l2, M2, hg⟩
  refine ⟨b1 + b2, l1 + l2, fun i j => M1 i j + M2 i j, fun s => ?_⟩
  dsimp only
  rw [hf s, hg s, add_dotProduct]
  have hM : (∑ i, ∑ j, (M1 i j + M2 i j) * s i * s j) =
      (∑ i, ∑ j, M1 i j * s i * s j) + (∑ i, ∑ j, M2 i j * s i * s j) := by
    simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hM]; ring

private lemma isQuad_smul {k : ℕ} (c : ZMod 2) {f : (Fin k → ZMod 2) → ZMod 2}
    (hf : IsQuad f) : IsQuad (fun s => c * f s) := by
  rcases hf with ⟨b, l, M, hf⟩
  refine ⟨c * b, c • l, fun i j => c * M i j, fun s => ?_⟩
  dsimp only
  rw [hf s, smul_dotProduct, smul_eq_mul]
  have hM : (∑ i, ∑ j, c * M i j * s i * s j) = c * ∑ i, ∑ j, M i j * s i * s j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hM]; ring

private lemma isQuad_sum {k : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → (Fin k → ZMod 2) → ZMod 2) (hF : ∀ a ∈ s, IsQuad (F a)) :
    IsQuad (fun x => ∑ a ∈ s, F a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using isQuad_const 0
  | insert a t ha ih =>
    have h1 := hF a (Finset.mem_insert_self a t)
    have h2 := ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
    simpa [Finset.sum_insert ha] using isQuad_add h1 h2

private lemma isQuad_affine {k : ℕ} (b : ZMod 2) (l : Fin k → ZMod 2) :
    IsQuad (fun s : Fin k → ZMod 2 => b + dotProduct l s) :=
  ⟨b, l, fun _ _ => 0, fun _ => by simp⟩

private lemma isQuad_mul_affine {k : ℕ} (b1 b2 : ZMod 2) (l1 l2 : Fin k → ZMod 2) :
    IsQuad (fun s : Fin k → ZMod 2 => (b1 + dotProduct l1 s) * (b2 + dotProduct l2 s)) := by
  refine ⟨b1 * b2, b1 • l2 + b2 • l1, fun i j => l1 i * l2 j, fun s => ?_⟩
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hprod : dotProduct l1 s * dotProduct l2 s = ∑ i, ∑ j, l1 i * l2 j * s i * s j := by
    rw [dotProduct, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [← hprod]; ring

private lemma isQuad_comp_affine {k d : ℕ} (c : Fin d → ZMod 2)
    (T : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2))
    {f : (Fin d → ZMod 2) → ZMod 2} (hf : IsQuad f) :
    IsQuad (fun s => f (c + T s)) := by
  have hcoord : ∀ j : Fin d, ∃ (b0 : ZMod 2) (l0 : Fin k → ZMod 2),
      ∀ s, (c + T s) j = b0 + dotProduct l0 s := by
    intro j
    refine ⟨c j, fun i => T (Pi.single i 1) j, fun s => ?_⟩
    have hTs : T s = ∑ i : Fin k, s i • T (Pi.single i 1) := by
      have hs : s = ∑ i : Fin k, s i • Pi.single i (1 : ZMod 2) := by
        ext i; simp [Pi.single_apply]
      conv_lhs => rw [hs]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => map_smul T (s i) _
    rw [Pi.add_apply, hTs, Finset.sum_apply, dotProduct]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  rcases hf with ⟨b, l, M, hf⟩
  have hEq : (fun s => f (c + T s)) =
      fun s => b + (∑ j : Fin d, l j * (c + T s) j) +
        ∑ i : Fin d, ∑ j : Fin d, M i j * ((c + T s) i * (c + T s) j) := by
    ext s; rw [hf (c + T s), dotProduct]
    congr 1; refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hEq]
  refine isQuad_add (isQuad_add (isQuad_const b) ?_) ?_
  · refine isQuad_sum Finset.univ _ fun j _ => ?_
    rcases hcoord j with ⟨b0, l0, hj⟩
    have hfun : (fun s => l j * (c + T s) j) = fun s => l j * (b0 + dotProduct l0 s) := by
      ext s; rw [hj s]
    rw [hfun]; exact isQuad_smul (l j) (isQuad_affine b0 l0)
  · refine isQuad_sum Finset.univ _ fun i _ => isQuad_sum Finset.univ _ fun j _ => ?_
    rcases hcoord i with ⟨bi, li, hi⟩
    rcases hcoord j with ⟨bj, lj, hj⟩
    have hfun : (fun s => M i j * ((c + T s) i * (c + T s) j)) =
        fun s => M i j * ((bi + dotProduct li s) * (bj + dotProduct lj s)) := by
      ext s; rw [hi s, hj s]
    rw [hfun]; exact isQuad_smul (M i j) (isQuad_mul_affine bi bj li lj)

/-- Every injective linear map between finite vector spaces over ZMod 2 has a linear left inverse. -/
private lemma exists_left_inv_linear {d k : ℕ}
    (L : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (hL : Function.Injective L) :
    ∃ R : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2), ∀ x, R (L x) = x := by
  let e : (Fin d → ZMod 2) ≃ₗ[ZMod 2] LinearMap.range L := LinearEquiv.ofInjective L hL
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (LinearMap.range L)
  let proj : (Fin k → ZMod 2) →ₗ[ZMod 2] LinearMap.range L :=
    Submodule.linearProjOfIsCompl (LinearMap.range L) Q hQ
  refine ⟨e.symm.toLinearMap.comp proj, fun x => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  have hmem : L x ∈ LinearMap.range L := ⟨x, rfl⟩
  have hproj : proj (L x) = ⟨L x, hmem⟩ :=
    Submodule.linearProjOfIsCompl_apply_left hQ ⟨L x, hmem⟩
  rw [hproj]
  exact e.symm_apply_apply x

/-- Sum of any quadratic over all of Fin 3 -> ZMod 2 is 0. -/
private lemma sum_quad_cube (f : (Fin 3 → ZMod 2) → ZMod 2) (hf : IsQuad f) :
    ∑ x : Fin 3 → ZMod 2, f x = 0 := by
  rcases hf with ⟨b, l, M, hf⟩
  have h1 : (∑ _x : Fin 3 → ZMod 2, (1 : ZMod 2)) = 0 := by decide
  have h2 : ∀ i : Fin 3, (∑ x : Fin 3 → ZMod 2, x i) = 0 := by decide
  have h3 : ∀ i j : Fin 3, (∑ x : Fin 3 → ZMod 2, x i * x j) = 0 := by decide
  simp_rw [hf, Finset.sum_add_distrib, dotProduct]
  have s1 : (∑ _x : Fin 3 → ZMod 2, b) = 0 := by
    calc (∑ _x : Fin 3 → ZMod 2, b) = b * ∑ _x : Fin 3 → ZMod 2, (1 : ZMod 2) := by
          rw [Finset.mul_sum]; simp
      _ = 0 := by rw [h1, mul_zero]
  have s2 : (∑ x : Fin 3 → ZMod 2, ∑ i : Fin 3, l i * x i) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, h2 i, mul_zero]
  have s3 : (∑ x : Fin 3 → ZMod 2, ∑ i : Fin 3, ∑ j : Fin 3, M i j * x i * x j) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hfac : (∑ x : Fin 3 → ZMod 2, M i j * x i * x j) =
        M i j * ∑ x : Fin 3 → ZMod 2, x i * x j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
    rw [hfac, h3 i j, mul_zero]
  rw [s1, s2, s3]; simp

/-- Sum of any quadratic over the 12-point quadric x 0 * x 1 + x 2 * x 3 = 1 in (ZMod 2)^5 is 0. -/
private lemma sum_quad_twelve (f : (Fin 5 → ZMod 2) → ZMod 2) (hf : IsQuad f) :
    ∑ x ∈ (Finset.univ : Finset (Fin 5 → ZMod 2)).filter (fun x => x 0 * x 1 + x 2 * x 3 = 1),
      f x = 0 := by
  let T12 : Finset (Fin 5 → ZMod 2) :=
    Finset.univ.filter (fun x => x 0 * x 1 + x 2 * x 3 = 1)
  have h1 : (∑ _x ∈ T12, (1 : ZMod 2)) = 0 := by decide
  have h2 : ∀ i : Fin 5, (∑ x ∈ T12, x i) = 0 := by decide
  have h3 : ∀ i j : Fin 5, (∑ x ∈ T12, x i * x j) = 0 := by decide
  rcases hf with ⟨b, l, M, hf⟩
  change ∑ x ∈ T12, f x = 0
  simp_rw [hf, Finset.sum_add_distrib, dotProduct]
  have s1 : (∑ _x ∈ T12, b) = 0 := by
    calc (∑ _x ∈ T12, b) = b * ∑ _x ∈ T12, (1 : ZMod 2) := by rw [Finset.mul_sum]; simp
      _ = 0 := by rw [h1, mul_zero]
  have s2 : (∑ x ∈ T12, ∑ i : Fin 5, l i * x i) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.mul_sum, h2 i, mul_zero]
  have s3 : (∑ x ∈ T12, ∑ i : Fin 5, ∑ j : Fin 5, M i j * x i * x j) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hfac : (∑ x ∈ T12, M i j * x i * x j) = M i j * ∑ x ∈ T12, x i * x j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun x _ => by ring
    rw [hfac, h3 i j, mul_zero]
  rw [s1, s2, s3]; simp

/-- Reed-Muller Fourier/ANF expansion of the indicator of U' in (Fin d -> ZMod 2). -/
private lemma indicator_expansion {d : ℕ} (U' : Finset (Fin d → ZMod 2)) (y : Fin d → ZMod 2) :
    (if y ∈ U' then (1 : ZMod 2) else 0) =
      ∑ T : Finset (Fin d),
        (∑ x ∈ U', ∏ i ∈ T, (1 + x i)) * (∏ i ∈ Tᶜ, y i) := by
  have hdelta : ∀ x : Fin d → ZMod 2,
      (if x = y then (1 : ZMod 2) else 0) =
        ∑ T : Finset (Fin d), (∏ i ∈ T, (1 + x i)) * (∏ i ∈ Tᶜ, y i) := by
    intro x
    have hprod : ∏ i : Fin d, ((1 + x i) + y i) = if x = y then (1 : ZMod 2) else 0 := by
      by_cases hxy : x = y
      · subst hxy
        rw [if_pos rfl]
        refine Finset.prod_eq_one fun i _ => ?_
        have := zmod2_add_self (x i)
        calc (1 + x i) + x i = 1 + (x i + x i) := by ring
          _ = 1 := by rw [this, add_zero]
      · rw [if_neg hxy]
        have hex : ∃ i : Fin d, x i ≠ y i := by
          by_contra hall; push_neg at hall; exact hxy (funext hall)
        rcases hex with ⟨i0, hi0⟩
        refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
        rcases zmod2_eq_zero_or_one (x i0) with ha | ha <;>
        rcases zmod2_eq_zero_or_one (y i0) with hb | hb <;>
        rw [ha, hb] at hi0 ⊢
        · exact absurd rfl hi0
        · decide
        · decide
        · exact absurd rfl hi0
    rw [← hprod, Finset.prod_add]
    have hbij :
        ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          (∏ i ∈ T, (1 + x i)) * (∏ i ∈ Finset.univ \ T, y i) =
        ∑ T : Finset (Fin d), (∏ i ∈ T, (1 + x i)) * (∏ i ∈ Tᶜ, y i) := by
      have hpow : (Finset.univ : Finset (Fin d)).powerset = Finset.univ := by
        ext T; simp
      rw [hpow]
      refine Finset.sum_congr rfl fun T _ => ?_
      have hc : Finset.univ \ T = Tᶜ := by ext i; simp
      rw [hc]
    exact hbij
  calc (if y ∈ U' then (1 : ZMod 2) else 0)
      = ∑ x ∈ U', if x = y then (1 : ZMod 2) else 0 := by
          by_cases hy : y ∈ U'
          · rw [if_pos hy, Finset.sum_eq_single y]
            · simp
            · intro x _ hne; rw [if_neg hne]
            · intro h; exact absurd hy h
          · rw [if_neg hy]
            symm
            refine Finset.sum_eq_zero fun x hx => ?_
            rw [if_neg (fun (heq : x = y) => hy (heq ▸ hx))]
    _ = ∑ x ∈ U', ∑ T : Finset (Fin d), (∏ i ∈ T, (1 + x i)) * (∏ i ∈ Tᶜ, y i) :=
          Finset.sum_congr rfl fun x _ => hdelta x
    _ = ∑ T : Finset (Fin d), ∑ x ∈ U', (∏ i ∈ T, (1 + x i)) * (∏ i ∈ Tᶜ, y i) :=
          Finset.sum_comm
    _ = ∑ T : Finset (Fin d), (∑ x ∈ U', ∏ i ∈ T, (1 + x i)) * (∏ i ∈ Tᶜ, y i) :=
          Finset.sum_congr rfl fun T _ => (Finset.sum_mul _ _ _).symm

/-- Product of <= 2 factors (1 + x i) is quadratic. -/
private lemma isQuad_prod_one_add_le_two {d : ℕ} (T : Finset (Fin d)) (hT : T.card ≤ 2) :
    IsQuad (fun x : Fin d → ZMod 2 => ∏ i ∈ T, (1 + x i)) := by
  rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2) with h0 | h1 | h2
  · have hTe : T = ∅ := Finset.card_eq_zero.mp h0
    subst hTe; simpa using isQuad_const 1
  · rcases Finset.card_eq_one.mp h1 with ⟨i, rfl⟩
    simpa using isQuad_add (isQuad_const 1) (isQuad_coord i)
  · rcases Finset.card_eq_two.mp h2 with ⟨i, j, hij, rfl⟩
    have hfun : (fun x : Fin d → ZMod 2 => ∏ a ∈ ({i, j} : Finset (Fin d)), (1 + x a)) =
        fun x => (1 + dotProduct (Pi.single i 1) x) * (1 + dotProduct (Pi.single j 1) x) := by
      ext x
      rw [Finset.prod_pair hij]
      simp [dotProduct, Pi.single_apply]
    rw [hfun]
    exact isQuad_mul_affine 1 1 (Pi.single i 1) (Pi.single j 1)

/-- If U' subset (Fin 4 -> ZMod 2) is orthogonal to all quadratics, its indicator is affine,
    so its card is in {0, 8, 16}. -/
private lemma card_ortho_quad_dim4 (U' : Finset (Fin 4 → ZMod 2))
    (horth : ∀ g : (Fin 4 → ZMod 2) → ZMod 2, IsQuad g → (∑ x ∈ U', g x) = 0) :
    U'.card = 0 ∨ U'.card = 8 ∨ U'.card = 16 := by
  have haff : ∃ (b : ZMod 2) (l : Fin 4 → ZMod 2),
      ∀ y : Fin 4 → ZMod 2, (if y ∈ U' then (1 : ZMod 2) else 0) = b + dotProduct l y := by
    let c : Finset (Fin 4) → ZMod 2 := fun T => ∑ x ∈ U', ∏ i ∈ T, (1 + x i)
    have hc0 : ∀ T : Finset (Fin 4), T.card ≤ 2 → c T = 0 :=
      fun T hT => horth _ (isQuad_prod_one_add_le_two T hT)
    refine ⟨c Finset.univ, fun i => c ({i}ᶜ), fun y => ?_⟩
    rw [indicator_expansion U' y]
    have hsplit : ∑ T : Finset (Fin 4), c T * (∏ i ∈ Tᶜ, y i) =
        c Finset.univ * (∏ i ∈ (Finset.univ : Finset (Fin 4))ᶜ, y i) +
        ∑ i : Fin 4, c ({i}ᶜ) * (∏ j ∈ ({i}ᶜ : Finset (Fin 4))ᶜ, y j) := by
      let Sbig : Finset (Finset (Fin 4)) := insert Finset.univ (Finset.univ.image (fun i : Fin 4 => ({i}ᶜ : Finset (Fin 4))))
      have hzero : ∀ T : Finset (Fin 4), T ∉ Sbig → c T * (∏ i ∈ Tᶜ, y i) = 0 := by
        intro T hT
        have hcard : T.card ≤ 2 := by
          by_contra hgt
          have hge3 : 3 ≤ T.card := by omega
          have hle4 : T.card ≤ 4 := by
            have := Finset.card_le_univ T; simpa using this
          have hcc : Tᶜ.card = 4 - T.card := by
            rw [Finset.card_compl, Fintype.card_fin]
          rcases (by omega : Tᶜ.card = 0 ∨ Tᶜ.card = 1) with hc0' | hc1'
          · have hTe : Tᶜ = ∅ := Finset.card_eq_zero.mp hc0'
            have hTu : T = Finset.univ := by rw [← compl_compl T, hTe, Finset.compl_empty]
            exact hT (hTu ▸ Finset.mem_insert_self _ _)
          · rcases Finset.card_eq_one.mp hc1' with ⟨i, hi⟩
            have hTi : T = {i}ᶜ := by rw [← compl_compl T, hi]
            exact hT (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hTi.symm⟩))
        rw [hc0 T hcard, zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ Sbig) (fun T _ hT => hzero T hT)]
      have hnotmem : (Finset.univ : Finset (Fin 4)) ∉ Finset.univ.image (fun i : Fin 4 => ({i}ᶜ : Finset (Fin 4))) := by
        simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
        intro i hi
        have hmem : i ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ i
        rw [← hi] at hmem
        simp at hmem
      rw [Finset.sum_insert hnotmem]
      exact congrArg (c Finset.univ * (∏ i ∈ (Finset.univ : Finset (Fin 4))ᶜ, y i) + ·)
        (Finset.sum_image (fun i1 _ i2 _ heq => Finset.singleton_injective (compl_injective heq)))
    rw [hsplit]
    simp only [Finset.compl_univ, Finset.prod_empty, mul_one, compl_compl, Finset.prod_singleton,
      dotProduct]
  rcases haff with ⟨b, l, hbl⟩
  have hU_eq : U' = Finset.univ.filter (fun y : Fin 4 → ZMod 2 => b + dotProduct l y = 1) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hy := hbl y
    by_cases h : y ∈ U'
    · simp only [h, ↓reduceIte] at hy; simp [h, hy.symm]
    · simp only [h, ↓reduceIte] at hy; simp [h, ← hy]
  rw [hU_eq]
  have hdec : ∀ (b0 : ZMod 2) (l0 : Fin 4 → ZMod 2),
      let n := (Finset.univ.filter (fun y : Fin 4 → ZMod 2 => b0 + dotProduct l0 y = 1)).card
      n = 0 ∨ n = 8 ∨ n = 16 := by decide
  exact hdec b l

/-- If U' subset (Fin 5 -> ZMod 2) is orthogonal to all quadratics, its indicator is quadratic. -/
private lemma indicator_isQuad_dim5 (U' : Finset (Fin 5 → ZMod 2))
    (horth : ∀ g : (Fin 5 → ZMod 2) → ZMod 2, IsQuad g → (∑ x ∈ U', g x) = 0) :
    IsQuad (fun y : Fin 5 → ZMod 2 => if y ∈ U' then (1 : ZMod 2) else 0) := by
  let c : Finset (Fin 5) → ZMod 2 := fun T => ∑ x ∈ U', ∏ i ∈ T, (1 + x i)
  have hc0 : ∀ T : Finset (Fin 5), T.card ≤ 2 → c T = 0 :=
    fun T hT => horth _ (isQuad_prod_one_add_le_two T hT)
  have hfun : (fun y : Fin 5 → ZMod 2 => if y ∈ U' then (1 : ZMod 2) else 0) =
      fun y => ∑ T : Finset (Fin 5), c T * (∏ i ∈ Tᶜ, y i) := by
    ext y; exact indicator_expansion U' y
  rw [hfun]
  refine isQuad_sum Finset.univ _ fun T _ => ?_
  by_cases hT : T.card ≤ 2
  · simpa [hc0 T hT] using isQuad_const 0
  · have hTc : Tᶜ.card ≤ 2 := by
      have h1 : Tᶜ.card = 5 - T.card := by rw [Finset.card_compl, Fintype.card_fin]
      omega
    refine isQuad_smul (c T) ?_
    rcases (by omega : Tᶜ.card = 0 ∨ Tᶜ.card = 1 ∨ Tᶜ.card = 2) with h0 | h1 | h2
    · have he : Tᶜ = ∅ := Finset.card_eq_zero.mp h0
      rw [he]; simpa using isQuad_const 1
    · rcases Finset.card_eq_one.mp h1 with ⟨i, hi⟩
      rw [hi]; simpa using isQuad_coord i
    · rcases Finset.card_eq_two.mp h2 with ⟨i, j, hij, hij_eq⟩
      rw [hij_eq]
      have hp : (fun y : Fin 5 → ZMod 2 => ∏ a ∈ ({i, j} : Finset (Fin 5)), y a) =
          fun y => y i * y j := by
        ext y; exact Finset.prod_pair hij
      rw [hp]; exact isQuad_mul_coord i j

/-- Dickson classification for weight-12 quadratics on (Fin 5 -> ZMod 2):
    every weight-12 quadratic is affinely equivalent to x 0 * x 1 + x 2 * x 3. -/
private lemma dickson_weight12_dim5 (Q : (Fin 5 → ZMod 2) → ZMod 2) (hQ : IsQuad Q)
    (hcard : (Finset.univ.filter (fun x : Fin 5 → ZMod 2 => Q x = 1)).card = 12) :
    ∃ (b0 : Fin 5 → ZMod 2) (A : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin 5 → ZMod 2)),
      ∀ x : Fin 5 → ZMod 2, Q (b0 + A x) = x 0 * x 1 + x 2 * x 3 := by
  let V := Fin 5 → ZMod 2
  let B : V → V → ZMod 2 := fun x y => Q (x + y) + Q x + Q y + Q 0
  have hB_symm : ∀ x y : V, B x y = B y x := fun x y => by dsimp only [B]; rw [add_comm x y]; ring
  have hB_self : ∀ x : V, B x x = 0 := by
    intro x; dsimp only [B]
    have hxx : x + x = 0 := by ext i; exact zmod2_add_self (x i)
    rw [hxx]
    have h1 := zmod2_add_self (Q 0)
    have h2 := zmod2_add_self (Q x)
    calc Q 0 + Q x + Q x + Q 0 = (Q 0 + Q 0) + (Q x + Q x) := by ring
      _ = 0 := by rw [h1, h2, add_zero]
  have hB_lin_left : ∀ x y z : V, B (x + y) z = B x z + B y z := by
    rcases hQ with ⟨c0, l0, M0, hQeq⟩
    intro x y z
    dsimp only [B]
    simp only [hQeq, Pi.add_apply, dotProduct_add, dotProduct_zero, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    have hM_eq : ∀ u v : V,
        (∑ i, ∑ j, M0 i j * (u i + v i) * (u j + v j)) +
        (∑ i, ∑ j, M0 i j * u i * u j) +
        (∑ i, ∑ j, M0 i j * v i * v j) =
        ∑ i, ∑ j, M0 i j * (u i * v j + v i * u j) := by
      intro u v
      simp_rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h1 := zmod2_add_self (M0 i j * u i * u j)
      have h2 := zmod2_add_self (M0 i j * v i * v j)
      calc M0 i j * (u i + v i) * (u j + v j) + M0 i j * u i * u j + M0 i j * v i * v j
          = (M0 i j * u i * u j + M0 i j * u i * u j) +
            (M0 i j * v i * v j + M0 i j * v i * v j) +
            M0 i j * (u i * v j + v i * u j) := by ring
        _ = M0 i j * (u i * v j + v i * u j) := by rw [h1, h2, zero_add, zero_add]
    have hB_formula : ∀ u v : V,
        (c0 + dotProduct l0 (u + v) + ∑ i, ∑ j, M0 i j * (u + v) i * (u + v) j) +
        (c0 + dotProduct l0 u + ∑ i, ∑ j, M0 i j * u i * u j) +
        (c0 + dotProduct l0 v + ∑ i, ∑ j, M0 i j * v i * v j) + c0 =
        ∑ i, ∑ j, M0 i j * (u i * v j + v i * u j) := by
      intro u v
      have hdp : dotProduct l0 (u + v) = dotProduct l0 u + dotProduct l0 v := dotProduct_add l0 u v
      rw [hdp]
      have h2c : c0 + c0 = 0 := zmod2_add_self c0
      have h2u : dotProduct l0 u + dotProduct l0 u = 0 := zmod2_add_self _
      have h2v : dotProduct l0 v + dotProduct l0 v = 0 := zmod2_add_self _
      have hadd_i : ∀ i : Fin 5, (u + v) i = u i + v i := fun _ => rfl
      simp_rw [hadd_i]
      calc (c0 + (dotProduct l0 u + dotProduct l0 v) + ∑ i, ∑ j, M0 i j * (u i + v i) * (u j + v j)) +
            (c0 + dotProduct l0 u + ∑ i, ∑ j, M0 i j * u i * u j) +
            (c0 + dotProduct l0 v + ∑ i, ∑ j, M0 i j * v i * v j) + c0
          = (c0 + c0) + (c0 + c0) + (dotProduct l0 u + dotProduct l0 u) +
            (dotProduct l0 v + dotProduct l0 v) +
            ((∑ i, ∑ j, M0 i j * (u i + v i) * (u j + v j)) +
             (∑ i, ∑ j, M0 i j * u i * u j) +
             (∑ i, ∑ j, M0 i j * v i * v j)) := by ring
        _ = ∑ i, ∑ j, M0 i j * (u i * v j + v i * u j) := by
            rw [h2c, h2u, h2v, hM_eq u v]; ring
    have hf1 := hB_formula (x + y) z
    have hf2 := hB_formula x z
    have hf3 := hB_formula y z
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    rw [hf1, hf2, hf3]
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    change M0 i j * ((x i + y i) * z j + z i * (x j + y j)) = _
    ring
  have hB_lin_right : ∀ x y z : V, B x (y + z) = B x y + B x z := by
    intro x y z; rw [hB_symm, hB_lin_left, hB_symm y x, hB_symm z x]
  have hB_smul_left : ∀ (c : ZMod 2) (x y : V), B (c • x) y = c * B x y := by
    intro c x y
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp only [zero_smul, zero_mul, B, zero_add]
      have h1 := zmod2_add_self (Q y)
      have h2 := zmod2_add_self (Q 0)
      calc Q y + Q 0 + Q y + Q 0 = (Q y + Q y) + (Q 0 + Q 0) := by ring
        _ = 0 := by rw [h1, h2, add_zero]
    · simp
  have hB_smul_right : ∀ (c : ZMod 2) (x y : V), B x (c • y) = c * B x y := by
    intro c x y; rw [hB_symm, hB_smul_left, hB_symm]
  have hQ_add : ∀ x y : V, Q (x + y) = Q x + Q y + Q 0 + B x y := by
    intro x y; dsimp only [B]
    have h1 := zmod2_add_self (Q x); have h2 := zmod2_add_self (Q y); have h3 := zmod2_add_self (Q 0)
    calc Q (x + y) = Q (x + y) + (Q x + Q x) + (Q y + Q y) + (Q 0 + Q 0) := by rw [h1, h2, h3]; ring
      _ = Q x + Q y + Q 0 + (Q (x + y) + Q x + Q y + Q 0) := by ring
  have hQ_smul : ∀ (c : ZMod 2) (x : V), Q (c • x) = Q 0 + c * (Q x + Q 0) := by
    intro c x
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp
    · simp only [one_smul, one_mul]
      have h0 := zmod2_add_self (Q 0)
      calc Q x = (Q 0 + Q 0) + Q x := by rw [h0, zero_add]
        _ = Q 0 + (Q x + Q 0) := by ring
  -- Helper: check card of Q(A x) = 1 equals 12 for any linear equiv A
  have hcard_equiv : ∀ (A : V ≃ₗ[ZMod 2] V),
      (Finset.univ.filter (fun x : V => Q (A x) = 1)).card = 12 := by
    intro A
    rw [← hcard]
    refine Finset.card_bij (fun x _ => A x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x1 _ x2 _ h; exact A.injective h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨A.symm y, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using hy
  -- Helper: evaluate Q on a linear combination of 5 basis vectors
  have hQ_combo : ∀ (e : Fin 5 → V) (x : V),
      Q (∑ i : Fin 5, x i • e i) =
        Q 0 + (∑ i : Fin 5, x i * (Q (e i) + Q 0)) +
          ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => i.val < j.val),
            x i * x j * B (e i) (e j) := by
    intro e x
    have hstep : ∀ (v1 v2 v3 v4 v5 : V),
        Q (v1 + v2 + v3 + v4 + v5) =
          Q v1 + Q v2 + Q v3 + Q v4 + Q v5 +
          B v1 v2 + B v1 v3 + B v1 v4 + B v1 v5 +
          B v2 v3 + B v2 v4 + B v2 v5 +
          B v3 v4 + B v3 v5 + B v4 v5 := by
      intro v1 v2 v3 v4 v5
      have h4 := zmod2_add_self (Q 0)
      rw [hQ_add (v1 + v2 + v3 + v4) v5, hQ_add (v1 + v2 + v3) v4, hQ_add (v1 + v2) v3, hQ_add v1 v2]
      simp only [hB_lin_left]
      calc Q v1 + Q v2 + Q 0 + B v1 v2 + Q v3 + Q 0 + (B v1 v3 + B v2 v3) + Q v4 + Q 0 +
            (B v1 v4 + B v2 v4 + B v3 v4) + Q v5 + Q 0 +
            (B v1 v5 + B v2 v5 + B v3 v5 + B v4 v5)
          = (Q 0 + Q 0) + (Q 0 + Q 0) +
            (Q v1 + Q v2 + Q v3 + Q v4 + Q v5 +
             B v1 v2 + B v1 v3 + B v1 v4 + B v1 v5 +
             B v2 v3 + B v2 v4 + B v2 v5 +
             B v3 v4 + B v3 v5 + B v4 v5) := by ring
        _ = _ := by rw [h4]; ring
    have hsum5 : ∑ i : Fin 5, x i • e i =
        x 0 • e 0 + x 1 • e 1 + x 2 • e 2 + x 3 • e 3 + x 4 • e 4 := by
      rw [Fin.sum_univ_five]
    rw [hsum5, hstep]
    simp only [hQ_smul, hB_smul_left, hB_smul_right]
    have hlin5 : ∑ i : Fin 5, x i * (Q (e i) + Q 0) =
        x 0 * (Q (e 0) + Q 0) + x 1 * (Q (e 1) + Q 0) + x 2 * (Q (e 2) + Q 0) +
        x 3 * (Q (e 3) + Q 0) + x 4 * (Q (e 4) + Q 0) := by
      rw [Fin.sum_univ_five]
    have hquad5 : ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => i.val < j.val),
        x i * x j * B (e i) (e j) =
        x 0 * x 1 * B (e 0) (e 1) + x 0 * x 2 * B (e 0) (e 2) +
        x 0 * x 3 * B (e 0) (e 3) + x 0 * x 4 * B (e 0) (e 4) +
        x 1 * x 2 * B (e 1) (e 2) + x 1 * x 3 * B (e 1) (e 3) +
        x 1 * x 4 * B (e 1) (e 4) + x 2 * x 3 * B (e 2) (e 3) +
        x 2 * x 4 * B (e 2) (e 4) + x 3 * x 4 * B (e 3) (e 4) := by
      rw [Fin.sum_univ_five]
      have f0 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (0 : Fin 5).val < j.val) = {1, 2, 3, 4} := by decide
      have f1 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (1 : Fin 5).val < j.val) = {2, 3, 4} := by decide
      have f2 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (2 : Fin 5).val < j.val) = {3, 4} := by decide
      have f3 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (3 : Fin 5).val < j.val) = {4} := by decide
      have f4 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (4 : Fin 5).val < j.val) = ∅ := by decide
      rw [f0, f1, f2, f3, f4]
      simp [Finset.sum_insert, Finset.sum_singleton]
      ring
    rw [hlin5, hquad5]
    have hq0 : Q 0 + Q 0 = 0 := zmod2_add_self (Q 0)
    calc Q 0 + x 0 * (Q (e 0) + Q 0) + (Q 0 + x 1 * (Q (e 1) + Q 0)) +
          (Q 0 + x 2 * (Q (e 2) + Q 0)) + (Q 0 + x 3 * (Q (e 3) + Q 0)) +
          (Q 0 + x 4 * (Q (e 4) + Q 0)) +
          x 0 * (x 1 * B (e 0) (e 1)) + x 0 * (x 2 * B (e 0) (e 2)) +
          x 0 * (x 3 * B (e 0) (e 3)) + x 0 * (x 4 * B (e 0) (e 4)) +
          x 1 * (x 2 * B (e 1) (e 2)) + x 1 * (x 3 * B (e 1) (e 3)) +
          x 1 * (x 4 * B (e 1) (e 4)) + x 2 * (x 3 * B (e 2) (e 3)) +
          x 2 * (x 4 * B (e 2) (e 4)) + x 3 * (x 4 * B (e 3) (e 4))
        = (Q 0 + Q 0) + (Q 0 + Q 0) +
          (Q 0 + (x 0 * (Q (e 0) + Q 0) + x 1 * (Q (e 1) + Q 0) + x 2 * (Q (e 2) + Q 0) +
           x 3 * (Q (e 3) + Q 0) + x 4 * (Q (e 4) + Q 0)) +
          (x 0 * x 1 * B (e 0) (e 1) + x 0 * x 2 * B (e 0) (e 2) +
           x 0 * x 3 * B (e 0) (e 3) + x 0 * x 4 * B (e 0) (e 4) +
           x 1 * x 2 * B (e 1) (e 2) + x 1 * x 3 * B (e 1) (e 3) +
           x 1 * x 4 * B (e 1) (e 4) + x 2 * x 3 * B (e 2) (e 3) +
           x 2 * x 4 * B (e 2) (e 4) + x 3 * x 4 * B (e 3) (e 4))) := by ring
      _ = _ := by rw [hq0]; ring
  -- Case split on rank of alternating bilinear form B
  by_cases hB0 : ∀ u v : V, B u v = 0
  · exfalso
    have hQaff : ∀ x : V, Q x = Q 0 + dotProduct (fun i => Q (Pi.single i 1) + Q 0) x := by
      intro x
      have hx : x = ∑ i : Fin 5, x i • Pi.single i (1 : ZMod 2) := by
        ext i; simp [Pi.single_apply]
      conv_lhs => rw [hx]
      rw [hQ_combo (fun i => Pi.single i 1) x]
      simp [hB0, dotProduct, mul_comm]
    have hno12 : ∀ (c : ZMod 2) (a : V),
        (Finset.univ.filter (fun x : V => c + dotProduct a x = 1)).card ≠ 12 := by decide
    have h12 := hno12 (Q 0) (fun i => Q (Pi.single i 1) + Q 0)
    have hfeq : Finset.univ.filter (fun x : V => Q 0 + dotProduct (fun i => Q (Pi.single i 1) + Q 0) x = 1) =
        Finset.univ.filter (fun x : V => Q x = 1) := by
      ext x; simp [hQaff x]
    rw [hfeq, hcard] at h12
    exact h12 rfl
  · push_neg at hB0
    rcases hB0 with ⟨e0, e1, hB01_ne⟩
    have hB01 : B e0 e1 = 1 := (zmod2_eq_zero_or_one (B e0 e1)).resolve_left hB01_ne
    let φ0 : V →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun v => B e0 v, map_add' := hB_lin_right e0, map_smul' := fun c v => by simp [hB_smul_right] }
    let φ1 : V →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun v => B e1 v, map_add' := hB_lin_right e1, map_smul' := fun c v => by simp [hB_smul_right] }
    let W1 : Submodule (ZMod 2) V := LinearMap.ker φ0 ⊓ LinearMap.ker φ1
    have hW1_proj : ∀ v : V, v + B e1 v • e0 + B e0 v • e1 ∈ W1 := by
      intro v
      refine ⟨?_, ?_⟩
      · show B e0 (v + B e1 v • e0 + B e0 v • e1) = 0
        rw [hB_lin_right, hB_lin_right, hB_smul_right, hB_smul_right, hB_self, hB01, mul_zero,
          mul_one, add_zero, zmod2_add_self]
      · show B e1 (v + B e1 v • e0 + B e0 v • e1) = 0
        rw [hB_lin_right, hB_lin_right, hB_smul_right, hB_smul_right, hB_symm e1 e0, hB01,
          hB_self, mul_one, mul_zero, add_zero, zmod2_add_self]
    have hW1_finrank : Module.finrank (ZMod 2) W1 = 3 := by
      let Φ : V →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
        { toFun := fun v => ![B e0 v, B e1 v]
          map_add' := fun u v => by ext i; fin_cases i <;> simp [hB_lin_right]
          map_smul' := fun c v => by ext i; fin_cases i <;> simp [hB_smul_right] }
      have hker : LinearMap.ker Φ = W1 := by
        ext v; simp only [LinearMap.mem_ker, W1, Submodule.mem_inf, φ0, φ1, LinearMap.coe_mk,
          AddHom.coe_mk, Φ]
        constructor
        · intro h
          exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
        · rintro ⟨h0, h1⟩
          ext i; fin_cases i <;> simp [h0, h1]
      have hsurj : Function.Surjective Φ := by
        intro w
        refine ⟨w 1 • e0 + w 0 • e1, ?_⟩
        ext i; fin_cases i
        · simp [Φ, hB_lin_right, hB_smul_right, hB_self, hB01]
        · simp [Φ, hB_lin_right, hB_smul_right, hB_symm e1 e0, hB_self, hB01]
      have hrk := LinearMap.finrank_range_add_finrank_ker Φ
      rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrk
      have hfr2 : Module.finrank (ZMod 2) (Fin 2 → ZMod 2) = 2 := by simp
      have hfrV : Module.finrank (ZMod 2) V = 5 := by simp [V]
      rw [hfr2, hfrV] at hrk
      omega
    by_cases hB1 : ∀ u ∈ W1, ∀ v ∈ W1, B u v = 0
    · exfalso
      let bW1 := Module.finBasisOfFinrankEq (ZMod 2) W1 hW1_finrank
      let e : Fin 5 → V := ![e0, e1, (bW1 0).val, (bW1 1).val, (bW1 2).val]
      let L : V →ₗ[ZMod 2] V :=
        { toFun := fun x => ∑ i : Fin 5, x i • e i
          map_add' := fun x y => by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => add_smul (x i) (y i) (e i)
          map_smul' := fun c x => by
            dsimp only [RingHom.id_apply]
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => mul_smul c (x i) (e i) }
      have hL_inj : Function.Injective L := by
        rw [injective_iff_map_eq_zero]
        intro x hx
        have hsum0 : x 0 • e0 + x 1 • e1 + (x 2 • (bW1 0).val + x 3 • (bW1 1).val + x 4 • (bW1 2).val) = 0 := by
          have h1 : L x = x 0 • e0 + x 1 • e1 + (x 2 • (bW1 0).val + x 3 • (bW1 1).val + x 4 • (bW1 2).val) := by
            change ∑ i : Fin 5, x i • e i = _
            rw [Fin.sum_univ_five]; simp only [e, Matrix.cons_val_zero, Matrix.cons_val_one,
              Matrix.cons_val]; abel
          rw [← h1, hx]
        have hb0_0 : B e0 (bW1 0).val = 0 := (bW1 0).property.1
        have hb1_0 : B e0 (bW1 1).val = 0 := (bW1 1).property.1
        have hb2_0 : B e0 (bW1 2).val = 0 := (bW1 2).property.1
        have hb0_1 : B e1 (bW1 0).val = 0 := (bW1 0).property.2
        have hb1_1 : B e1 (bW1 1).val = 0 := (bW1 1).property.2
        have hb2_1 : B e1 (bW1 2).val = 0 := (bW1 2).property.2
        have hx1 : x 1 = 0 := by
          have h := congrArg (fun v => B e0 v) hsum0
          have h00 : B e0 0 = 0 := by simpa using hB_smul_right 0 e0 e0
          simp only [hB_lin_right, hB_smul_right, hB_self, hB01, hb0_0, hb1_0, hb2_0, h00,
            mul_zero, mul_one, zero_add, add_zero] at h
          exact h
        have hx0 : x 0 = 0 := by
          have h := congrArg (fun v => B e1 v) hsum0
          have h10 : B e1 0 = 0 := by simpa using hB_smul_right 0 e1 e1
          simp only [hB_lin_right, hB_smul_right, hB_symm e1 e0, hB01, hB_self, hb0_1, hb1_1, hb2_1, h10,
            mul_zero, mul_one, zero_add, add_zero] at h
          exact h
        rw [hx0, hx1, zero_smul, zero_smul, zero_add, zero_add] at hsum0
        have hw_sub : x 2 • bW1 0 + x 3 • bW1 1 + x 4 • bW1 2 = 0 := by
          apply Subtype.ext; exact hsum0
        have hlin : ∑ j : Fin 3, (![x 2, x 3, x 4] j) • bW1 j = 0 := by
          rw [Fin.sum_univ_three]; simpa using hw_sub
        have hrepr := Fintype.linearIndependent_iff.mp bW1.linearIndependent ![x 2, x 3, x 4] hlin
        ext i; fin_cases i
        · exact hx0
        · exact hx1
        · exact hrepr 0
        · exact hrepr 1
        · exact hrepr 2
      let A : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective L
        ⟨hL_inj, LinearMap.injective_iff_surjective.mp hL_inj⟩
      have hcardA := hcard_equiv A
      have hQA : ∀ x : V, Q (A x) = x 0 * x 1 + dotProduct (fun i => Q (e i) + Q 0) x + Q 0 := by
        intro x
        change Q (∑ i : Fin 5, x i • e i) = _
        rw [hQ_combo e x]
        have he02 : B (e 0) (e 2) = 0 := (bW1 0).property.1
        have he03 : B (e 0) (e 3) = 0 := (bW1 1).property.1
        have he04 : B (e 0) (e 4) = 0 := (bW1 2).property.1
        have he12 : B (e 1) (e 2) = 0 := (bW1 0).property.2
        have he13 : B (e 1) (e 3) = 0 := (bW1 1).property.2
        have he14 : B (e 1) (e 4) = 0 := (bW1 2).property.2
        have he23 : B (e 2) (e 3) = 0 := hB1 _ (bW1 0).property _ (bW1 1).property
        have he24 : B (e 2) (e 4) = 0 := hB1 _ (bW1 0).property _ (bW1 2).property
        have he34 : B (e 3) (e 4) = 0 := hB1 _ (bW1 1).property _ (bW1 2).property
        have hq : ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => i.val < j.val),
            x i * x j * B (e i) (e j) = x 0 * x 1 := by
          rw [Fin.sum_univ_five]
          have f0 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (0 : Fin 5).val < j.val) = {1, 2, 3, 4} := by decide
          have f1 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (1 : Fin 5).val < j.val) = {2, 3, 4} := by decide
          have f2 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (2 : Fin 5).val < j.val) = {3, 4} := by decide
          have f3 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (3 : Fin 5).val < j.val) = {4} := by decide
          have f4 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (4 : Fin 5).val < j.val) = ∅ := by decide
          rw [f0, f1, f2, f3, f4]
          simp [Finset.sum_insert, Finset.sum_singleton, he02, he03, he04, he12, he13, he14, he23, he24, he34]
          have h01 : B (e 0) (e 1) = 1 := hB01
          rw [h01, mul_one]
        rw [hq, dotProduct]
        have hl : ∑ i : Fin 5, (Q (e i) + Q 0) * x i = ∑ i : Fin 5, x i * (Q (e i) + Q 0) :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [hl]; ring
      have hno12 : ∀ (a : V) (c : ZMod 2),
          (Finset.univ.filter (fun x : V => x 0 * x 1 + dotProduct a x + c = 1)).card ≠ 12 := by decide
      have hbad := hno12 (fun i => Q (e i) + Q 0) (Q 0)
      have hfeq : Finset.univ.filter (fun x : V => x 0 * x 1 + dotProduct (fun i => Q (e i) + Q 0) x + Q 0 = 1) =
          Finset.univ.filter (fun x : V => Q (A x) = 1) := by
        ext x; simp [hQA x]
      rw [hfeq, hcardA] at hbad
      exact hbad rfl
    · push_neg at hB1
      rcases hB1 with ⟨e2, he2W, e3, he3W, hB23_ne⟩
      have hB02 : B e0 e2 = 0 := he2W.1
      have hB12 : B e1 e2 = 0 := he2W.2
      have hB03 : B e0 e3 = 0 := he3W.1
      have hB13 : B e1 e3 = 0 := he3W.2
      have hB23 : B e2 e3 = 1 := (zmod2_eq_zero_or_one (B e2 e3)).resolve_left hB23_ne
      let Φ4 : V →ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
        { toFun := fun v => ![B e0 v, B e1 v, B e2 v, B e3 v]
          map_add' := fun u v => by ext i; fin_cases i <;> simp [hB_lin_right]
          map_smul' := fun c v => by ext i; fin_cases i <;> simp [hB_smul_right] }
      have hker_pos : 0 < Module.finrank (ZMod 2) (LinearMap.ker Φ4) := by
        have hrk := LinearMap.finrank_range_add_finrank_ker Φ4
        have hle4 : Module.finrank (ZMod 2) (LinearMap.range Φ4) ≤ 4 := by
          calc Module.finrank (ZMod 2) (LinearMap.range Φ4)
              ≤ Module.finrank (ZMod 2) (Fin 4 → ZMod 2) := Submodule.finrank_le _
            _ = 4 := by simp
        have hfrV : Module.finrank (ZMod 2) V = 5 := by simp [V]
        rw [hfrV] at hrk
        omega
      have hne_bot : LinearMap.ker Φ4 ≠ ⊥ := by
        intro hbot; rw [hbot, finrank_bot] at hker_pos; omega
      obtain ⟨e4, he4_mem, he4_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne_bot
      have hB04 : B e0 e4 = 0 := by simpa [Φ4] using congrFun he4_mem 0
      have hB14 : B e1 e4 = 0 := by simpa [Φ4] using congrFun he4_mem 1
      have hB24 : B e2 e4 = 0 := by simpa [Φ4] using congrFun he4_mem 2
      have hB34 : B e3 e4 = 0 := by simpa [Φ4] using congrFun he4_mem 3
      let e : Fin 5 → V := ![e0, e1, e2, e3, e4]
      let L : V →ₗ[ZMod 2] V :=
        { toFun := fun x => ∑ i : Fin 5, x i • e i
          map_add' := fun x y => by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => add_smul (x i) (y i) (e i)
          map_smul' := fun c x => by
            dsimp only [RingHom.id_apply]
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun i _ => mul_smul c (x i) (e i) }
      have hL_inj : Function.Injective L := by
        rw [injective_iff_map_eq_zero]
        intro x hx
        have hsum0 : x 0 • e0 + x 1 • e1 + x 2 • e2 + x 3 • e3 + x 4 • e4 = 0 := by
          have h1 : L x = x 0 • e0 + x 1 • e1 + x 2 • e2 + x 3 • e3 + x 4 • e4 := by
            change ∑ i : Fin 5, x i • e i = _
            rw [Fin.sum_univ_five]; rfl
          rw [← h1, hx]
        have hB0_0 : B e0 0 = 0 := by simpa using hB_smul_right 0 e0 e0
        have hB1_0 : B e1 0 = 0 := by simpa using hB_smul_right 0 e1 e1
        have hB2_0 : B e2 0 = 0 := by simpa using hB_smul_right 0 e2 e2
        have hB3_0 : B e3 0 = 0 := by simpa using hB_smul_right 0 e3 e3
        have hx1 : x 1 = 0 := by
          have h := congrArg (fun v => B e0 v) hsum0
          simp only [hB_lin_right, hB_smul_right, hB_self, hB01, hB02, hB03, hB04, hB0_0,
            mul_zero, mul_one, zero_add, add_zero] at h; exact h
        have hx0 : x 0 = 0 := by
          have h := congrArg (fun v => B e1 v) hsum0
          simp only [hB_lin_right, hB_smul_right, hB_symm e1 e0, hB01, hB_self, hB12, hB13,
            hB14, hB1_0, mul_zero, mul_one, zero_add, add_zero] at h; exact h
        have hx3 : x 3 = 0 := by
          have h := congrArg (fun v => B e2 v) hsum0
          have h20 : B e2 e0 = 0 := by rw [hB_symm]; exact hB02
          have h21 : B e2 e1 = 0 := by rw [hB_symm]; exact hB12
          simp only [hB_lin_right, hB_smul_right, h20, h21, hB_self, hB23, hB24, hB2_0,
            mul_zero, mul_one, zero_add, add_zero] at h; exact h
        have hx2 : x 2 = 0 := by
          have h := congrArg (fun v => B e3 v) hsum0
          have h30 : B e3 e0 = 0 := by rw [hB_symm]; exact hB03
          have h31 : B e3 e1 = 0 := by rw [hB_symm]; exact hB13
          have h32 : B e3 e2 = 1 := by rw [hB_symm]; exact hB23
          simp only [hB_lin_right, hB_smul_right, h30, h31, h32, hB_self, hB34, hB3_0,
            mul_zero, mul_one, zero_add, add_zero] at h; exact h
        rw [hx0, hx1, hx2, hx3] at hsum0
        simp only [zero_smul, zero_add] at hsum0
        have hx4 : x 4 = 0 := by
          rcases zmod2_eq_zero_or_one (x 4) with h0 | h1
          · exact h0
          · rw [h1, one_smul] at hsum0; exact absurd hsum0 he4_ne
        ext i; fin_cases i <;> assumption
      let A : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective L
        ⟨hL_inj, LinearMap.injective_iff_surjective.mp hL_inj⟩
      have hcardA := hcard_equiv A
      let a : V := fun i => Q (e i) + Q 0
      let c : ZMod 2 := Q 0
      have hQA : ∀ x : V, Q (A x) = x 0 * x 1 + x 2 * x 3 + dotProduct a x + c := by
        intro x
        change Q (∑ i : Fin 5, x i • e i) = _
        rw [hQ_combo e x]
        have hq : ∑ i : Fin 5, ∑ j ∈ Finset.univ.filter (fun j : Fin 5 => i.val < j.val),
            x i * x j * B (e i) (e j) = x 0 * x 1 + x 2 * x 3 := by
          rw [Fin.sum_univ_five]
          have f0 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (0 : Fin 5).val < j.val) = {1, 2, 3, 4} := by decide
          have f1 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (1 : Fin 5).val < j.val) = {2, 3, 4} := by decide
          have f2 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (2 : Fin 5).val < j.val) = {3, 4} := by decide
          have f3 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (3 : Fin 5).val < j.val) = {4} := by decide
          have f4 : (Finset.univ : Finset (Fin 5)).filter (fun j : Fin 5 => (4 : Fin 5).val < j.val) = ∅ := by decide
          rw [f0, f1, f2, f3, f4]
          simp [Finset.sum_insert, Finset.sum_singleton, e, hB01, hB02, hB03, hB04,
            hB12, hB13, hB14, hB23, hB24, hB34]
        rw [hq, dotProduct]
        have hl : ∑ i : Fin 5, a i * x i = ∑ i : Fin 5, x i * (Q (e i) + Q 0) :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
        rw [hl]; dsimp only [c]; ring
      have hdec12 : ∀ (a0 : V) (c0 : ZMod 2),
          (Finset.univ.filter (fun x : V => x 0 * x 1 + x 2 * x 3 + dotProduct a0 x + c0 = 1)).card = 12 →
            a0 4 = 0 ∧ c0 = a0 0 * a0 1 + a0 2 * a0 3 := by decide
      have hfeq : Finset.univ.filter (fun x : V => x 0 * x 1 + x 2 * x 3 + dotProduct a x + c = 1) =
          Finset.univ.filter (fun x : V => Q (A x) = 1) := by
        ext x; simp [hQA x]
      obtain ⟨ha4, hc_eq⟩ := hdec12 a c (by rw [hfeq, hcardA])
      let sh : V := ![a 1, a 0, a 3, a 2, 0]
      refine ⟨A sh, A, fun x => ?_⟩
      rw [← map_add, hQA (sh + x), hc_eq, dotProduct, Fin.sum_univ_five]
      simp only [Pi.add_apply, sh, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        ha4, zero_mul, add_zero]
      have h0 := zmod2_add_self (a 0 * x 0)
      have h1 := zmod2_add_self (a 1 * x 1)
      have h2 := zmod2_add_self (a 2 * x 2)
      have h3 := zmod2_add_self (a 3 * x 3)
      have h01 := zmod2_add_self (a 0 * a 1)
      have h23 := zmod2_add_self (a 2 * a 3)
      calc (a 1 + x 0) * (a 0 + x 1) + (a 3 + x 2) * (a 2 + x 3) +
            (a 0 * (a 1 + x 0) + a 1 * (a 0 + x 1) + a 2 * (a 3 + x 2) + a 3 * (a 2 + x 3)) +
            (a 0 * a 1 + a 2 * a 3)
          = x 0 * x 1 + x 2 * x 3 +
            (a 0 * x 0 + a 0 * x 0) + (a 1 * x 1 + a 1 * x 1) +
            (a 2 * x 2 + a 2 * x 2) + (a 3 * x 3 + a 3 * x 3) +
            (a 0 * a 1 + a 0 * a 1) + (a 0 * a 1 + a 0 * a 1) +
            (a 2 * a 3 + a 2 * a 3) + (a 2 * a 3 + a 2 * a 3) := by ring
        _ = x 0 * x 1 + x 2 * x 3 := by rw [h0, h1, h2, h3, h01, h23]; ring

/-- Affine span submodule centered at any base point u0 in U. -/
private def affSpan {k : ℕ} (U : Finset (Fin k → ZMod 2)) (u0 : Fin k → ZMod 2) :
    Submodule (ZMod 2) (Fin k → ZMod 2) :=
  Submodule.span (ZMod 2) ((fun s => s - u0) '' (U : Set (Fin k → ZMod 2)))

private lemma affSpan_congr_base {k : ℕ} (U : Finset (Fin k → ZMod 2))
    {u1 u2 : Fin k → ZMod 2} (h1 : u1 ∈ U) (h2 : u2 ∈ U) :
    affSpan U u1 = affSpan U u2 := by
  have hle : ∀ a b : Fin k → ZMod 2, a ∈ U → b ∈ U → affSpan U a ≤ affSpan U b := by
    intro a b ha hb
    rw [affSpan, Submodule.span_le]
    rintro v ⟨s, hs, rfl⟩
    have hsb : s - b ∈ affSpan U b := Submodule.subset_span ⟨s, hs, rfl⟩
    have hab : a - b ∈ affSpan U b := Submodule.subset_span ⟨a, ha, rfl⟩
    have heq : s - a = (s - b) - (a - b) := by abel
    show s - a ∈ affSpan U b
    rw [heq]
    exact Submodule.sub_mem _ hsb hab
  exact le_antisymm (hle u1 u2 h1 h2) (hle u2 u1 h2 h1)

private lemma finrank_span_singleton_le_one {k : ℕ} (v : Fin k → ZMod 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({v} : Set (Fin k → ZMod 2))) ≤ 1 := by
  by_cases hv : v = 0
  · subst hv; rw [Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]; exact Nat.zero_le 1
  · rw [finrank_span_singleton hv]

private lemma finrank_span_insert_le {k : ℕ} (S : Set (Fin k → ZMod 2)) (v : Fin k → ZMod 2) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (insert v S)) ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) S) + 1 := by
  rw [Submodule.span_insert]
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {v})
    (Submodule.span (ZMod 2) S)
  have hv1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := finrank_span_singleton_le_one v
  omega

/-- Affine nullity is monotone: U subset E implies U.card + finrank(affSpan E) <= E.card + finrank(affSpan U). -/
private lemma affNull_mono {k : ℕ} {U E : Finset (Fin k → ZMod 2)} (hsub : U ⊆ E)
    {u0 : Fin k → ZMod 2} (hu0 : u0 ∈ U) :
    U.card + Module.finrank (ZMod 2) (affSpan E u0) ≤
      E.card + Module.finrank (ZMod 2) (affSpan U u0) := by
  have hstep : ∀ (n : ℕ) (A B : Finset (Fin k → ZMod 2)),
      A ⊆ B → u0 ∈ A → (B \ A).card = n →
      A.card + Module.finrank (ZMod 2) (affSpan B u0) ≤
        B.card + Module.finrank (ZMod 2) (affSpan A u0) := by
    intro n
    induction n with
    | zero =>
      intro A B hAB _ h0
      have hsd : B \ A = ∅ := Finset.card_eq_zero.mp h0
      have hBA : B ⊆ A := Finset.sdiff_eq_empty_iff_subset.mp hsd
      have heq : A = B := Finset.Subset.antisymm hAB hBA
      subst heq; omega
    | succ m ih =>
      intro A B hAB huA hm
      have hne : (B \ A).Nonempty := Finset.card_pos.mp (by omega)
      rcases hne with ⟨x, hx⟩
      rcases Finset.mem_sdiff.mp hx with ⟨hxB, hxA⟩
      let A' := insert x A
      have hA'B : A' ⊆ B := Finset.insert_subset_iff.mpr ⟨hxB, hAB⟩
      have huA' : u0 ∈ A' := Finset.mem_insert_of_mem huA
      have hsd' : (B \ A').card = m := by
        have heq : B \ A' = (B \ A).erase x := by
          ext y; simp only [A', Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
        rw [heq, Finset.card_erase_of_mem hx, hm]; omega
      have hih := ih A' B hA'B huA' hsd'
      have hcardA' : A'.card = A.card + 1 := Finset.card_insert_of_notMem hxA
      have hdim : Module.finrank (ZMod 2) (affSpan A' u0) ≤
          Module.finrank (ZMod 2) (affSpan A u0) + 1 := by
        have hsub_eq : affSpan A' u0 =
            Submodule.span (ZMod 2) (insert (x - u0) ((fun s => s - u0) '' (A : Set (Fin k → ZMod 2)))) := by
          dsimp only [affSpan, A']
          rw [Finset.coe_insert, Set.image_insert_eq]
        rw [hsub_eq]
        exact finrank_span_insert_le _ _
      omega
  exact hstep (E \ U).card U E hsub hu0 rfl

/-- Self-orthogonality lower bound: any nonempty quadratic-orthogonal U has 2*(dim(affSpan U)+1) <= U.card. -/
private lemma two_mul_affDim_add_one_le_card {k : ℕ} (U : Finset (Fin k → ZMod 2))
    {u0 : Fin k → ZMod 2} (hu0 : u0 ∈ U)
    (horth : ∀ f : (Fin k → ZMod 2) → ZMod 2, IsQuad f → (∑ s ∈ U, f s) = 0) :
    2 * (Module.finrank (ZMod 2) (affSpan U u0) + 1) ≤ U.card := by
  let WU := affSpan U u0
  let d := Module.finrank (ZMod 2) WU
  let bW := Module.finBasisOfFinrankEq (ZMod 2) WU (rfl : Module.finrank (ZMod 2) WU = d)
  let L : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := WU.subtype.comp bW.equivFun.symm.toLinearMap
  have hL_inj : Function.Injective L := Subtype.val_injective.comp bW.equivFun.symm.injective
  have hL_range : LinearMap.range L = WU := by
    ext v
    simp only [LinearMap.mem_range, L, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, rfl⟩; exact (bW.equivFun.symm x).property
    · intro hv; exact ⟨bW.equivFun ⟨v, hv⟩, by simp⟩
  let U' : Finset (Fin d → ZMod 2) := Finset.univ.filter (fun x => u0 + L x ∈ U)
  have hU'_card : U'.card = U.card := by
    refine Finset.card_bij (fun x _ => u0 + L x) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 _ x2 _ heq; exact hL_inj (add_left_cancel heq)
    · intro s hs
      have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
      rw [← hL_range] at hmem
      rcases hmem with ⟨x, hx⟩
      refine ⟨x, ?_, ?_⟩
      · simp only [U', Finset.mem_filter, Finset.mem_univ, true_and]
        have hseq : u0 + L x = s := by rw [hx]; abel
        rw [hseq]; exact hs
      · rw [hx]; abel
  have h0_mem : (0 : Fin d → ZMod 2) ∈ U' := by
    simp [U', hu0]
  have hspan_top : Submodule.span (ZMod 2) (U' : Set (Fin d → ZMod 2)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hLx : L x ∈ WU := by rw [← hL_range]; exact ⟨x, rfl⟩
    have hmap : Submodule.map L (Submodule.span (ZMod 2) (U' : Set (Fin d → ZMod 2))) = WU := by
      rw [Submodule.map_span]
      congr 1
      ext v
      simp only [Set.mem_image, Finset.mem_coe, U', Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨u0 + L y, hy, by abel⟩
      · rintro ⟨s, hs, rfl⟩
        have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
        rw [← hL_range] at hmem
        rcases hmem with ⟨y, hy⟩
        have hseq : u0 + L y = s := by rw [hy]; abel
        exact ⟨y, by rw [hseq]; exact hs, hy⟩
    rw [← hmap] at hLx
    rcases hLx with ⟨y, hy, hyx⟩
    rw [← hL_inj hyx]; exact hy
  have hU'_orth : ∀ g : (Fin d → ZMod 2) → ZMod 2, IsQuad g → (∑ x ∈ U', g x) = 0 := by
    intro g hg
    obtain ⟨R, hR⟩ := exists_left_inv_linear L hL_inj
    let f : (Fin k → ZMod 2) → ZMod 2 := fun s => g (R (s - u0))
    have hf : IsQuad f := by
      have hfeq : f = fun s => g (-(R u0) + R s) := by
        ext s; simp only [f, map_sub]; congr 1; abel
      rw [hfeq]; exact isQuad_comp_affine (-(R u0)) R hg
    have hsum_eq : ∑ x ∈ U', g x = ∑ s ∈ U, f s := by
      refine Finset.sum_bij (fun x _ => u0 + L x) ?_ ?_ ?_ ?_
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · intro x1 _ x2 _ heq; exact hL_inj (add_left_cancel heq)
      · intro s hs
        have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
        rw [← hL_range] at hmem
        rcases hmem with ⟨x, hx⟩
        have hseq : u0 + L x = s := by rw [hx]; abel
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hseq.symm ▸ hs⟩, hseq⟩
      · intro x _
        simp only [f, add_sub_cancel_left, hR]
    rw [hsum_eq]; exact horth f hf
  -- Matrix M : U' x (Unit + Fin d) with row x = (1, x)
  let M : Matrix U' (Unit ⊕ Fin d) (ZMod 2) := fun x j =>
    match j with
    | Sum.inl () => 1
    | Sum.inr i => x.val i
  have hM_inj : Function.Injective M.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hval : ∀ x ∈ U', v (Sum.inl ()) + dotProduct (fun i => v (Sum.inr i)) x = 0 := by
      intro x hx
      have h1 : M.mulVec v ⟨x, hx⟩ = 0 := congrFun hv ⟨x, hx⟩
      rw [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique] at h1
      dsimp only [M] at h1
      rw [one_mul] at h1
      simpa [dotProduct, mul_comm] using h1
    have hv0 : v (Sum.inl ()) = 0 := by
      have h0 := hval 0 h0_mem; simpa using h0
    have hvl : ∀ x ∈ U', dotProduct (fun i => v (Sum.inr i)) x = 0 := by
      intro x hx; have h := hval x hx; rw [hv0, zero_add] at h; exact h
    let φ : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => dotProduct (fun i => v (Sum.inr i)) x
        map_add' := fun a b => dotProduct_add _ a b
        map_smul' := fun c a => by simp [dotProduct_smul] }
    have hker_top : LinearMap.ker φ = ⊤ := by
      rw [eq_top_iff, ← hspan_top, Submodule.span_le]
      intro x hx; exact hvl x hx
    ext j; cases j with
    | inl u => cases u; exact hv0
    | inr i =>
      have hmem : Pi.single i (1 : ZMod 2) ∈ LinearMap.ker φ := by rw [hker_top]; trivial
      simpa [φ, dotProduct, Pi.single_apply] using hmem
  have hM_rk : M.rank = d + 1 := by
    calc M.rank
        = Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := rfl
      _ = Module.finrank (ZMod 2) (Unit ⊕ Fin d → ZMod 2) := LinearMap.finrank_range_of_inj hM_inj
      _ = Fintype.card (Unit ⊕ Fin d) := by simp
      _ = d + 1 := by simp [add_comm]
  have hMTM : M.transpose * M = 0 := by
    ext j1 j2
    rw [Matrix.mul_apply, Matrix.zero_apply]
    simp_rw [Matrix.transpose_apply]
    cases j1 with
    | inl u1 =>
      cases u1
      cases j2 with
      | inl u2 =>
        cases u2
        have h1 : ∑ x : U', M x (Sum.inl ()) * M x (Sum.inl ()) = ∑ _x ∈ U', (1 : ZMod 2) := by
          rw [← Finset.sum_attach U']; simp [M]
        rw [h1]; exact hU'_orth _ (isQuad_const 1)
      | inr i2 =>
        have h1 : ∑ x : U', M x (Sum.inl ()) * M x (Sum.inr i2) = ∑ x ∈ U', x i2 := by
          rw [← Finset.sum_attach U']; simp [M]
        rw [h1]; exact hU'_orth _ (isQuad_coord i2)
    | inr i1 =>
      cases j2 with
      | inl u2 =>
        cases u2
        have h1 : ∑ x : U', M x (Sum.inr i1) * M x (Sum.inl ()) = ∑ x ∈ U', x i1 := by
          rw [← Finset.sum_attach U']; simp [M]
        rw [h1]; exact hU'_orth _ (isQuad_coord i1)
      | inr i2 =>
        have h1 : ∑ x : U', M x (Sum.inr i1) * M x (Sum.inr i2) = ∑ x ∈ U', x i1 * x i2 := by
          rw [← Finset.sum_attach U']; simp [M]
        rw [h1]; exact hU'_orth _ (isQuad_mul_coord i1 i2)
  have hrange_le_ker : LinearMap.range M.mulVecLin ≤ LinearMap.ker M.transpose.mulVecLin := by
    rintro w ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      hMTM, Matrix.zero_mulVec]
  have hMT_rk : M.transpose.rank = d + 1 := by rw [Matrix.rank_transpose, hM_rk]
  have hrn := LinearMap.finrank_range_add_finrank_ker M.transpose.mulVecLin
  have hle_ker : d + 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) := by
    calc d + 1 = M.rank := hM_rk.symm
      _ = Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) := rfl
      _ ≤ Module.finrank (ZMod 2) (LinearMap.ker M.transpose.mulVecLin) :=
          Submodule.finrank_mono hrange_le_ker
  have hcard_dom : Module.finrank (ZMod 2) (U' → ZMod 2) = U.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hU'_card]
  have hMT_range : Module.finrank (ZMod 2) (LinearMap.range M.transpose.mulVecLin) = d + 1 := hMT_rk
  change 2 * (d + 1) ≤ U.card
  omega

/-- Classification of nonempty quadratic-orthogonal U with U.card <= finrank(affSpan U) + 7. -/
private lemma classify_rel_small_null {k : ℕ} (U : Finset (Fin k → ZMod 2))
    (hUne : U.Nonempty)
    (horth : ∀ f : (Fin k → ZMod 2) → ZMod 2, IsQuad f → (∑ s ∈ U, f s) = 0)
    (hnull : ∀ u0 ∈ U, U.card ≤ Module.finrank (ZMod 2) (affSpan U u0) + 7) :
    (∃ (b : Fin k → ZMod 2) (L : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)),
      Function.Injective L ∧ ∀ s, s ∈ U ↔ ∃ x : Fin 3 → ZMod 2, s = b + L x) ∨
    (∃ (b : Fin k → ZMod 2) (L : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)),
      Function.Injective L ∧ ∀ s, s ∈ U ↔ ∃ x : Fin 5 → ZMod 2, x 0 * x 1 + x 2 * x 3 = 1 ∧ s = b + L x) := by
  rcases hUne with ⟨u0, hu0⟩
  let WU := affSpan U u0
  let d := Module.finrank (ZMod 2) WU
  have hlb : 2 * (d + 1) ≤ U.card := two_mul_affDim_add_one_le_card U hu0 horth
  have hub : U.card ≤ d + 7 := hnull u0 hu0
  let bW := Module.finBasisOfFinrankEq (ZMod 2) WU (rfl : Module.finrank (ZMod 2) WU = d)
  let L : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) := WU.subtype.comp bW.equivFun.symm.toLinearMap
  have hL_inj : Function.Injective L := Subtype.val_injective.comp bW.equivFun.symm.injective
  have hL_range : LinearMap.range L = WU := by
    ext v
    simp only [LinearMap.mem_range, L, LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, rfl⟩; exact (bW.equivFun.symm x).property
    · intro hv; exact ⟨bW.equivFun ⟨v, hv⟩, by simp⟩
  let U' : Finset (Fin d → ZMod 2) := Finset.univ.filter (fun x => u0 + L x ∈ U)
  have hU'_card : U'.card = U.card := by
    refine Finset.card_bij (fun x _ => u0 + L x) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 _ x2 _ heq; exact hL_inj (add_left_cancel heq)
    · intro s hs
      have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
      rw [← hL_range] at hmem
      rcases hmem with ⟨x, hx⟩
      have hseq : u0 + L x = s := by rw [hx]; abel
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hseq.symm ▸ hs⟩, hseq⟩
  have hU'_le_pow : U.card ≤ 2 ^ d := by
    rw [← hU'_card]
    calc U'.card ≤ Fintype.card (Fin d → ZMod 2) := Finset.card_le_univ U'
      _ = 2 ^ d := by simp
  have hU'_orth : ∀ g : (Fin d → ZMod 2) → ZMod 2, IsQuad g → (∑ x ∈ U', g x) = 0 := by
    intro g hg
    obtain ⟨R, hR⟩ := exists_left_inv_linear L hL_inj
    let f : (Fin k → ZMod 2) → ZMod 2 := fun s => g (R (s - u0))
    have hf : IsQuad f := by
      have hfeq : f = fun s => g (-(R u0) + R s) := by ext s; simp only [f, map_sub]; congr 1; abel
      rw [hfeq]; exact isQuad_comp_affine (-(R u0)) R hg
    have hsum_eq : ∑ x ∈ U', g x = ∑ s ∈ U, f s := by
      refine Finset.sum_bij (fun x _ => u0 + L x) ?_ ?_ ?_ ?_
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · intro x1 _ x2 _ heq; exact hL_inj (add_left_cancel heq)
      · intro s hs
        have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
        rw [← hL_range] at hmem
        rcases hmem with ⟨x, hx⟩
        have hseq : u0 + L x = s := by rw [hx]; abel
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hseq.symm ▸ hs⟩, hseq⟩
      · intro x _; simp only [f, add_sub_cancel_left, hR]
    rw [hsum_eq]; exact horth f hf
  have hd_cases : d = 3 ∨ d = 4 ∨ d = 5 := by
    have hd_le5 : d ≤ 5 := by omega
    by_cases h0 : d = 0
    · rw [h0] at hlb hU'_le_pow; norm_num at hlb hU'_le_pow; omega
    · by_cases h1 : d = 1
      · rw [h1] at hlb hU'_le_pow; norm_num at hlb hU'_le_pow; omega
      · by_cases h2 : d = 2
        · rw [h2] at hlb hU'_le_pow; norm_num at hlb hU'_le_pow; omega
        · omega
  rcases hd_cases with hd3 | hd4 | hd5
  · left
    let e3 : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
      LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd3)
    refine ⟨u0, L.comp e3.toLinearMap, hL_inj.comp e3.injective, fun s => ?_⟩
    have hU'_univ : U' = Finset.univ := by
      refine Finset.eq_univ_of_card U' ?_
      rw [hU'_card]; simp only [Fintype.card_pi, ZMod.card, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [hd3] at hlb hU'_le_pow ⊢; norm_num at hlb hU'_le_pow ⊢; omega
    constructor
    · intro hs
      have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
      rw [← hL_range] at hmem
      rcases hmem with ⟨y, hy⟩
      refine ⟨e3.symm y, ?_⟩
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      rw [hy]; abel
    · rintro ⟨x, rfl⟩
      have hmem : e3 x ∈ U' := by rw [hU'_univ]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp hmem).2
  · exfalso
    let e4 : (Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
      LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd4)
    let U4 : Finset (Fin 4 → ZMod 2) := Finset.univ.filter (fun x => e4 x ∈ U')
    have hU4_card : U4.card = U.card := by
      rw [← hU'_card]
      refine Finset.card_bij (fun x _ => e4 x) ?_ ?_ ?_
      · intro x hx; exact (Finset.mem_filter.mp hx).2
      · intro x1 _ x2 _ h; exact e4.injective h
      · intro y hy; exact ⟨e4.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy⟩, by simp⟩
    have hU4_orth : ∀ g : (Fin 4 → ZMod 2) → ZMod 2, IsQuad g → (∑ x ∈ U4, g x) = 0 := by
      intro g hg
      have hg' : IsQuad (fun y => g (e4.symm y)) := by
        simpa using isQuad_comp_affine 0 e4.symm.toLinearMap hg
      have hsum : ∑ x ∈ U4, g x = ∑ y ∈ U', g (e4.symm y) := by
        refine Finset.sum_bij (fun x _ => e4 x) ?_ ?_ ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x1 _ x2 _ h; exact e4.injective h
        · intro y hy; exact ⟨e4.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy⟩, by simp⟩
        · intro x _; simp
      rw [hsum]; exact hU'_orth _ hg'
    have hcases := card_ortho_quad_dim4 U4 hU4_orth
    rw [hU4_card] at hcases
    omega
  · right
    let e5 : (Fin 5 → ZMod 2) ≃ₗ[ZMod 2] (Fin d → ZMod 2) :=
      LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd5)
    let U5 : Finset (Fin 5 → ZMod 2) := Finset.univ.filter (fun x => e5 x ∈ U')
    have hU5_card : U5.card = 12 := by
      have hc : U5.card = U.card := by
        rw [← hU'_card]
        refine Finset.card_bij (fun x _ => e5 x) ?_ ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x1 _ x2 _ h; exact e5.injective h
        · intro y hy; exact ⟨e5.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy⟩, by simp⟩
      omega
    have hU5_orth : ∀ g : (Fin 5 → ZMod 2) → ZMod 2, IsQuad g → (∑ x ∈ U5, g x) = 0 := by
      intro g hg
      have hg' : IsQuad (fun y => g (e5.symm y)) := by
        simpa using isQuad_comp_affine 0 e5.symm.toLinearMap hg
      have hsum : ∑ x ∈ U5, g x = ∑ y ∈ U', g (e5.symm y) := by
        refine Finset.sum_bij (fun x _ => e5 x) ?_ ?_ ?_ ?_
        · intro x hx; exact (Finset.mem_filter.mp hx).2
        · intro x1 _ x2 _ h; exact e5.injective h
        · intro y hy; exact ⟨e5.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hy⟩, by simp⟩
        · intro x _; simp
      rw [hsum]; exact hU'_orth _ hg'
    let Q : (Fin 5 → ZMod 2) → ZMod 2 := fun y => if y ∈ U5 then 1 else 0
    have hQ : IsQuad Q := indicator_isQuad_dim5 U5 hU5_orth
    have hQ_card : (Finset.univ.filter (fun x : Fin 5 → ZMod 2 => Q x = 1)).card = 12 := by
      have hfeq : Finset.univ.filter (fun x : Fin 5 → ZMod 2 => Q x = 1) = U5 := by
        ext x; simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : x ∈ U5 <;> simp [h]
      rw [hfeq, hU5_card]
    obtain ⟨b0, A, hQA⟩ := dickson_weight12_dim5 Q hQ hQ_card
    let L5 : (Fin 5 → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
      L.comp (e5.toLinearMap.comp A.toLinearMap)
    refine ⟨u0 + L (e5 b0), L5, hL_inj.comp (e5.injective.comp A.injective), fun s => ?_⟩
    constructor
    · intro hs
      have hmem : s - u0 ∈ WU := Submodule.subset_span ⟨s, hs, rfl⟩
      rw [← hL_range] at hmem
      rcases hmem with ⟨y, hy⟩
      let z := e5.symm y
      have hzU5 : z ∈ U5 := by
        simp only [U5, Finset.mem_filter, Finset.mem_univ, true_and, z, LinearEquiv.apply_symm_apply]
        simp only [U', Finset.mem_filter, Finset.mem_univ, true_and]
        have : u0 + L y = s := by rw [hy]; abel
        rw [this]; exact hs
      let x := A.symm (z - b0)
      have hzx : b0 + A x = z := by simp only [x, LinearEquiv.apply_symm_apply]; abel
      have hQx : Q (b0 + A x) = 1 := by rw [hzx]; simp [Q, hzU5]
      refine ⟨x, by rw [← hQA x]; exact hQx, ?_⟩
      simp only [L5, LinearMap.comp_apply, LinearEquiv.coe_coe]
      have hsum : u0 + L (e5 b0) + L (e5 (A x)) = u0 + L (e5 (b0 + A x)) := by
        rw [map_add, map_add]; abel
      rw [hsum, hzx]
      simp only [z, LinearEquiv.apply_symm_apply]
      rw [hy]; abel
    · rintro ⟨x, hx1, rfl⟩
      have hQx : Q (b0 + A x) = 1 := by rw [hQA x]; exact hx1
      have hmem5 : b0 + A x ∈ U5 := by
        by_contra hno; simp [Q, hno] at hQx
      have hmem' : e5 (b0 + A x) ∈ U' := (Finset.mem_filter.mp hmem5).2
      have hmemU : u0 + L (e5 (b0 + A x)) ∈ U := (Finset.mem_filter.mp hmem').2
      have hsum : u0 + L (e5 b0) + L5 x = u0 + L (e5 (b0 + A x)) := by
        simp only [L5, LinearMap.comp_apply, LinearEquiv.coe_coe, map_add]; abel
      rw [hsum]; exact hmemU

/-- Affine dimension upper bound for union of two subsets sharing a point or disjoint. -/
private lemma affDim_union_le_of_inter {k : ℕ} (U V : Finset (Fin k → ZMod 2))
    {w : Fin k → ZMod 2} (hwU : w ∈ U) (hwV : w ∈ V) :
    Module.finrank (ZMod 2) (affSpan (U ∪ V) w) +
      Module.finrank (ZMod 2) (affSpan (U ∩ V) w) ≤
    Module.finrank (ZMod 2) (affSpan U w) +
      Module.finrank (ZMod 2) (affSpan V w) := by
  have hunion : affSpan (U ∪ V) w = affSpan U w ⊔ affSpan V w := by
    dsimp only [affSpan]
    rw [Finset.coe_union, Set.image_union, Submodule.span_union]
  have hinter : affSpan (U ∩ V) w ≤ affSpan U w ⊓ affSpan V w := by
    refine le_inf ?_ ?_
    · exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr Finset.inter_subset_left))
    · exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr Finset.inter_subset_right))
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq (affSpan U w) (affSpan V w)
  have hle := Submodule.finrank_mono hinter
  rw [hunion]; omega

private lemma affDim_union_le_disj {k : ℕ} (U V : Finset (Fin k → ZMod 2))
    {u0 v0 : Fin k → ZMod 2} (hu0 : u0 ∈ U) (hv0 : v0 ∈ V) :
    Module.finrank (ZMod 2) (affSpan (U ∪ V) u0) ≤
      Module.finrank (ZMod 2) (affSpan U u0) +
      Module.finrank (ZMod 2) (affSpan V v0) + 1 := by
  have hle : affSpan (U ∪ V) u0 ≤
      affSpan U u0 ⊔ (affSpan V v0 ⊔ Submodule.span (ZMod 2) {v0 - u0}) := by
    rw [affSpan, Submodule.span_le]
    rintro z ⟨s, hs, rfl⟩
    rcases Finset.mem_union.mp hs with hsU | hsV
    · exact Submodule.mem_sup_left (Submodule.subset_span ⟨s, hsU, rfl⟩)
    · refine Submodule.mem_sup_right ?_
      have heq : s - u0 = (s - v0) + (v0 - u0) := by abel
      show s - u0 ∈ affSpan V v0 ⊔ Submodule.span (ZMod 2) {v0 - u0}
      rw [heq]
      exact Submodule.add_mem_sup (Submodule.subset_span ⟨s, hsV, rfl⟩)
        (Submodule.subset_span (Set.mem_singleton _))
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (affSpan U u0)
    (affSpan V v0 ⊔ Submodule.span (ZMod 2) {v0 - u0})
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (affSpan V v0)
    (Submodule.span (ZMod 2) {v0 - u0})
  have h4 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v0 - u0}) ≤ 1 :=
    finrank_span_singleton_le_one _
  omega

private lemma card_le_two_pow_affDim {k : ℕ} (S : Finset (Fin k → ZMod 2))
    {w : Fin k → ZMod 2} (hw : w ∈ S) :
    S.card ≤ 2 ^ Module.finrank (ZMod 2) (affSpan S w) := by
  have hbij : S.card ≤ Fintype.card (affSpan S w) := by
    refine Finset.card_le_card_of_injOn (fun s =>
      if hs : s ∈ S then (⟨s - w, Submodule.subset_span ⟨s, hs, rfl⟩⟩ : affSpan S w)
      else (0 : affSpan S w)) ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro s1 hs1 s2 hs2 heq
      have h1 : s1 ∈ S := hs1
      have h2 : s2 ∈ S := hs2
      dsimp only at heq
      rw [dif_pos h1, dif_pos h2] at heq
      exact sub_left_inj.mp (congrArg Subtype.val heq)
  have hcardW : Fintype.card (affSpan S w) = 2 ^ Module.finrank (ZMod 2) (affSpan S w) := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := affSpan S w)
    simpa [ZMod.card] using this
  rw [← hcardW]; exact hbij

theorem main_proof :
    ∀ k : ℕ,
      let F := ZMod 2
      let S := Fin k → F
      let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
        ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
      ∀ (E : Finset S) (a : S), a ∈ E →
        let W := Submodule.span F (Set.image (fun s : S => s-a) (↑E : Set S))
        let rel := fun (U : Finset S) => U ⊆ E ∧ ∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0
        let cube := fun (U : Finset S) =>
          ∃ (b : S) (L : (Fin 3 → F) →ₗ[F] S), Function.Injective L ∧
            ∀ s : S, s ∈ U ↔ ∃ x : Fin 3 → F, s = b+L x
        let twelve := fun (U : Finset S) =>
          ∃ (b : S) (L : (Fin 5 → F) →ₗ[F] S), Function.Injective L ∧
            ∀ s : S, s ∈ U ↔ ∃ x : Fin 5 → F, x 0*x 1+x 2*x 3 = 1 ∧ s = b+L x
        (E.card ≤ Module.finrank F W + 7 →
          (∀ U : Finset S, U ⊆ E → U.Nonempty → (rel U ↔ cube U ∨ twelve U)) ∧
          ∀ U V : Finset S, rel U → rel V → U.Nonempty → V.Nonempty → U = V) ∧
        (∀ h : S → F, (∃ f : S → F, quad f ∧ ∀ s ∈ E, h s = f s) ↔
          ∀ U : Finset S, rel U → (∑ s ∈ U, h s) = 0) ∧
        ∀ O : Finset S, rel O → O.Nonempty →
          (∀ U : Finset S, rel U → U.Nonempty → U = O) →
          ∃ i j l : Fin k, (∑ s ∈ O, s i*s j*s l) = 1 ∧
            ∀ h : S → F, ∃ f : S → F, quad f ∧
              ∀ s ∈ E, h s = f s + (∑ u ∈ O, h u) * s i*s j*s l := by
  intro k
  dsimp only
  let F := ZMod 2
  let S := Fin k → F
  let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
  intro E a haE
  let W := Submodule.span F (Set.image (fun s : S => s - a) (↑E : Set S))
  let rel := fun (U : Finset S) => U ⊆ E ∧ ∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0
  let cube := fun (U : Finset S) =>
    ∃ (b : S) (L : (Fin 3 → F) →ₗ[F] S), Function.Injective L ∧
      ∀ s : S, s ∈ U ↔ ∃ x : Fin 3 → F, s = b + L x
  let twelve := fun (U : Finset S) =>
    ∃ (b : S) (L : (Fin 5 → F) →ₗ[F] S), Function.Injective L ∧
      ∀ s : S, s ∈ U ↔ ∃ x : Fin 5 → F, x 0 * x 1 + x 2 * x 3 = 1 ∧ s = b + L x
  -- Helpers for cube/twelve -> rel and sizes/dims
  have hcube_orth : ∀ U : Finset S, cube U → ∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0 := by
    rintro U ⟨b, L, hL, hU⟩ f hf
    have hsum : ∑ s ∈ U, f s = ∑ x : Fin 3 → F, f (b + L x) := by
      symm
      refine Finset.sum_bij (fun x _ => b + L x) ?_ ?_ ?_ ?_
      · intro x _; exact (hU (b + L x)).mpr ⟨x, rfl⟩
      · intro x1 _ x2 _ heq; exact hL (add_left_cancel heq)
      · intro s hs; rcases (hU s).mp hs with ⟨x, rfl⟩; exact ⟨x, Finset.mem_univ x, rfl⟩
      · intro _ _; rfl
    rw [hsum]
    exact sum_quad_cube _ (isQuad_comp_affine b L hf)
  have htwelve_orth : ∀ U : Finset S, twelve U → ∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0 := by
    rintro U ⟨b, L, hL, hU⟩ f hf
    let T12 : Finset (Fin 5 → F) := Finset.univ.filter (fun x => x 0 * x 1 + x 2 * x 3 = 1)
    have hsum : ∑ s ∈ U, f s = ∑ x ∈ T12, f (b + L x) := by
      symm
      refine Finset.sum_bij (fun x _ => b + L x) ?_ ?_ ?_ ?_
      · intro x hx; exact (hU (b + L x)).mpr ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩
      · intro x1 _ x2 _ heq; exact hL (add_left_cancel heq)
      · intro s hs; rcases (hU s).mp hs with ⟨x, hx1, rfl⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx1⟩, rfl⟩
      · intro _ _; rfl
    rw [hsum]
    exact sum_quad_twelve _ (isQuad_comp_affine b L hf)
  have hcube_info : ∀ U : Finset S, cube U →
      U.card = 8 ∧ ∀ u0 ∈ U, Module.finrank (ZMod 2) (affSpan U u0) = 3 := by
    rintro U ⟨b, L, hL, hU⟩
    have hcard : U.card = 8 := by
      have hbij : U.card = Fintype.card (Fin 3 → F) := by
        symm
        refine Finset.card_bij (fun x _ => b + L x) ?_ ?_ ?_
        · intro x _; exact (hU (b + L x)).mpr ⟨x, rfl⟩
        · intro x1 _ x2 _ heq; exact hL (add_left_cancel heq)
        · intro s hs; rcases (hU s).mp hs with ⟨x, rfl⟩; exact ⟨x, Finset.mem_univ x, rfl⟩
      rw [hbij]; dsimp only [F]; simp
    refine ⟨hcard, fun u0 hu0 => ?_⟩
    have hbU : b ∈ U := (hU b).mpr ⟨0, by simp⟩
    rw [affSpan_congr_base U hu0 hbU]
    have hsp : affSpan U b = LinearMap.range L := by
      apply le_antisymm
      · rw [affSpan, Submodule.span_le]
        rintro v ⟨s, hs, rfl⟩
        rcases (hU s).mp hs with ⟨x, rfl⟩
        exact ⟨x, by abel⟩
      · rintro v ⟨x, rfl⟩
        exact Submodule.subset_span ⟨b + L x, (hU (b + L x)).mpr ⟨x, rfl⟩, by abel⟩
    rw [hsp, LinearMap.finrank_range_of_inj hL]; simp
  have htwelve_info : ∀ U : Finset S, twelve U →
      U.card = 12 ∧ ∀ u0 ∈ U, Module.finrank (ZMod 2) (affSpan U u0) = 5 := by
    rintro U ⟨b, L, hL, hU⟩
    let T12 : Finset (Fin 5 → F) := Finset.univ.filter (fun x => x 0 * x 1 + x 2 * x 3 = 1)
    have hT12_card : T12.card = 12 := by decide
    have hcard : U.card = 12 := by
      rw [← hT12_card]
      symm
      refine Finset.card_bij (fun x _ => b + L x) ?_ ?_ ?_
      · intro x hx; exact (hU (b + L x)).mpr ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩
      · intro x1 _ x2 _ heq; exact hL (add_left_cancel heq)
      · intro s hs; rcases (hU s).mp hs with ⟨x, hx1, rfl⟩
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx1⟩, rfl⟩
    refine ⟨hcard, fun u0 hu0 => ?_⟩
    rcases (hU u0).mp hu0 with ⟨x0, hx0, rfl⟩
    have hsp : affSpan U (b + L x0) = LinearMap.range L := by
      apply le_antisymm
      · rw [affSpan, Submodule.span_le]
        rintro v ⟨s, hs, rfl⟩
        rcases (hU s).mp hs with ⟨x, _, rfl⟩
        exact ⟨x - x0, by rw [map_sub]; abel⟩
      · rintro v ⟨y, rfl⟩
        -- Every basis vector of Fin 5 -> ZMod 2 is a difference of two elements of T12
        have hdiff_span : ∀ i : Fin 5, ∃ z1 ∈ T12, ∃ z2 ∈ T12, z1 - z2 = Pi.single i (1 : ZMod 2) := by
          decide
        have hy_mem : y ∈ Submodule.span F ((fun z : Fin 5 → F => z - x0) '' (T12 : Set (Fin 5 → F))) := by
          have hy_exp : y = ∑ i : Fin 5, y i • Pi.single i (1 : ZMod 2) := by
            ext i; simp [Pi.single_apply]
          rw [hy_exp]
          refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
          rcases hdiff_span i with ⟨z1, hz1, z2, hz2, hdz⟩
          rw [← hdz]
          have heq : z1 - z2 = (z1 - x0) - (z2 - x0) := by abel
          rw [heq]
          exact Submodule.sub_mem _
            (Submodule.subset_span ⟨z1, hz1, rfl⟩)
            (Submodule.subset_span ⟨z2, hz2, rfl⟩)
        have hmap : L y ∈ Submodule.map L (Submodule.span F ((fun z : Fin 5 → F => z - x0) '' (T12 : Set (Fin 5 → F)))) :=
          ⟨y, hy_mem, rfl⟩
        rw [Submodule.map_span] at hmap
        refine Submodule.span_mono ?_ hmap
        rintro w ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨b + L z, (hU (b + L z)).mpr ⟨z, (Finset.mem_filter.mp hz).2, rfl⟩, by rw [map_sub]; abel⟩
    rw [hsp, LinearMap.finrank_range_of_inj hL]; simp
  -- Part 2 (linear-algebra dual characterization on E): proved first so Part 3 can use it!
  have hpart2 : ∀ h : S → F, (∃ f : S → F, quad f ∧ ∀ s ∈ E, h s = f s) ↔
      ∀ U : Finset S, rel U → (∑ s ∈ U, h s) = 0 := by
    intro h
    constructor
    · rintro ⟨f, hf, hfeq⟩ U ⟨hUE, hUorth⟩
      have hcongr : ∑ s ∈ U, h s = ∑ s ∈ U, f s :=
        Finset.sum_congr rfl fun s hs => hfeq s (hUE hs)
      rw [hcongr]; exact hUorth f hf
    · intro horth_h
      let Qsub : Submodule F (E → F) :=
        Submodule.mk (AddSubmonoid.mk (AddSubsemigroup.mk
          {v | ∃ f : S → F, IsQuad f ∧ ∀ s : E, v s = f s.val}
          (by rintro v1 v2 ⟨f1, hf1, h1⟩ ⟨f2, hf2, h2⟩
              exact ⟨fun s => f1 s + f2 s, isQuad_add hf1 hf2, fun s => by simp [h1 s, h2 s]⟩))
          ⟨fun _ => 0, isQuad_const 0, fun _ => rfl⟩)
          (by rintro c v ⟨f, hf, hv⟩
              exact ⟨fun s => c * f s, isQuad_smul c hf, fun s => by simp [hv s]⟩)
      let perp (V : Submodule F (E → F)) : Submodule F (E → F) :=
        Submodule.mk (AddSubmonoid.mk (AddSubsemigroup.mk
          {u | ∀ v ∈ V, dotProduct u v = 0}
          (by intro u1 u2 h1 h2 v hv
              rw [add_dotProduct, h1 v hv, h2 v hv, add_zero]))
          (fun v _ => zero_dotProduct v))
          (by intro c u hu v hv
              rw [smul_dotProduct, hu v hv, smul_zero])
      let Qperp : Submodule F (E → F) := perp Qsub
      let Qpp : Submodule F (E → F) := perp Qperp
      -- Prove Qpp = Qsub by finrank counting
      have hQ_le_Qpp : Qsub ≤ Qpp := fun v hv u hu => by
        rw [dotProduct_comm]; exact hu v hv
      have hdim_perp : ∀ V : Submodule F (E → F),
          Module.finrank F V + Module.finrank F (perp V) = Fintype.card E := by
        intro V
        let bV := Module.finBasis F V
        let Ψ : (E → F) →ₗ[F] (Fin (Module.finrank F V) → F) :=
          { toFun := fun u i => dotProduct u (bV i).val
            map_add' := fun u1 u2 => by ext i; exact add_dotProduct u1 u2 _
            map_smul' := fun c u => by ext i; simp [smul_dotProduct] }
        have hker : LinearMap.ker Ψ = perp V := by
          ext u
          simp only [LinearMap.mem_ker, perp, Submodule.mem_mk, AddSubmonoid.mem_mk,
            AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
          constructor
          · intro hu v hv
            have hv_eq : (⟨v, hv⟩ : V) = ∑ i, bV.repr ⟨v, hv⟩ i • bV i := (bV.sum_repr ⟨v, hv⟩).symm
            have hv_val : v = ∑ i, bV.repr ⟨v, hv⟩ i • (bV i).val := by
              calc v = V.subtype ⟨v, hv⟩ := rfl
                _ = V.subtype (∑ i, bV.repr ⟨v, hv⟩ i • bV i) := congrArg V.subtype hv_eq
                _ = ∑ i, bV.repr ⟨v, hv⟩ i • (bV i).val := by
                      rw [map_sum]; rfl
            rw [hv_val, dotProduct_sum]
            refine Finset.sum_eq_zero fun i _ => ?_
            have hui : dotProduct u (bV i).val = 0 := congrFun hu i
            rw [dotProduct_smul, hui, smul_zero]
          · intro hu; ext i; exact hu (bV i).val (bV i).property
        let M : Matrix (Fin (Module.finrank F V)) E F := fun i s => (bV i).val s
        have hΨ_eq : Ψ = M.mulVecLin := by
          apply LinearMap.ext; intro u; funext i
          change dotProduct u (bV i).val = dotProduct (fun s => (bV i).val s) u
          exact dotProduct_comm u (bV i).val
        have hMT_inj : Function.Injective M.transpose.mulVecLin := by
          rw [injective_iff_map_eq_zero]
          intro c hc
          have hsum0 : ∑ i, c i • (bV i).val = 0 := by
            ext s
            have h1 := congrFun hc s
            simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
              Pi.zero_apply] at h1
            dsimp only [M] at h1
            simpa [Finset.sum_apply, mul_comm] using h1
          have hsub0 : ∑ i, c i • bV i = 0 := Subtype.ext (by simpa using hsum0)
          exact funext (Fintype.linearIndependent_iff.mp bV.linearIndependent c hsub0)
        have hrk : Module.finrank F (LinearMap.range Ψ) = Module.finrank F V := by
          rw [hΨ_eq]
          change M.rank = Module.finrank F V
          rw [← Matrix.rank_transpose]
          calc M.transpose.rank
              = Module.finrank F (LinearMap.range M.transpose.mulVecLin) := rfl
            _ = Module.finrank F (Fin (Module.finrank F V) → F) := LinearMap.finrank_range_of_inj hMT_inj
            _ = Module.finrank F V := by simp
        have hrn := LinearMap.finrank_range_add_finrank_ker Ψ
        rw [hrk, hker, Module.finrank_fintype_fun_eq_card] at hrn
        exact hrn
      have h1 := hdim_perp Qsub
      have h2 := hdim_perp Qperp
      have hQpp_eq : Qpp = Qsub := by
        have hfr : Module.finrank F Qsub = Module.finrank F Qpp := by
          change Module.finrank F Qsub + Module.finrank F Qperp = Fintype.card E at h1
          change Module.finrank F Qperp + Module.finrank F Qpp = Fintype.card E at h2
          omega
        exact (Submodule.eq_of_le_of_finrank_eq hQ_le_Qpp hfr).symm
      have hh_mem : (fun s : E => h s.val) ∈ Qpp := by
        intro u hu
        rw [dotProduct_comm]
        let U : Finset S := E.filter (fun s => if hs : s ∈ E then u ⟨s, hs⟩ = 1 else False)
        have hUE : U ⊆ E := Finset.filter_subset _ _
        have hU_rel : rel U := by
          refine ⟨hUE, fun f hf => ?_⟩
          have hdot := hu (fun s : E => f s.val) ⟨f, hf, fun _ => rfl⟩
          have hsum_eq : ∑ s ∈ U, f s = dotProduct u (fun s : E => f s.val) := by
            rw [dotProduct]
            rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset E) (fun s : E => u s = 1)]
            have h0 : ∑ s ∈ (Finset.univ : Finset E).filter (fun s : E => ¬ u s = 1), u s * f s.val = 0 := by
              refine Finset.sum_eq_zero fun s hs => ?_
              have hne := (Finset.mem_filter.mp hs).2
              have hu0 : u s = 0 := (zmod2_eq_zero_or_one (u s)).resolve_right hne
              rw [hu0, zero_mul]
            rw [h0, add_zero]
            refine Finset.sum_bij (fun s hs => (⟨s, hUE hs⟩ : E)) ?_ ?_ ?_ ?_
            · intro s hs
              have h1 := (Finset.mem_filter.mp hs).2
              rw [dif_pos (hUE hs)] at h1
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
            · intro s1 _ s2 _ heq; exact congrArg Subtype.val heq
            · intro s hs
              refine ⟨s.val, ?_, Subtype.ext rfl⟩
              exact Finset.mem_filter.mpr ⟨s.property, by rw [dif_pos s.property]; exact (Finset.mem_filter.mp hs).2⟩
            · intro s hs
              have h1 := (Finset.mem_filter.mp hs).2
              rw [dif_pos (hUE hs)] at h1
              rw [h1, one_mul]
          rw [hsum_eq, hdot]
        have hsum_h : dotProduct u (fun s : E => h s.val) = ∑ s ∈ U, h s := by
          rw [dotProduct]
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset E) (fun s : E => u s = 1)]
          have h0 : ∑ s ∈ (Finset.univ : Finset E).filter (fun s : E => ¬ u s = 1), u s * h s.val = 0 := by
            refine Finset.sum_eq_zero fun s hs => ?_
            have hne := (Finset.mem_filter.mp hs).2
            have hu0 : u s = 0 := (zmod2_eq_zero_or_one (u s)).resolve_right hne
            rw [hu0, zero_mul]
          rw [h0, add_zero]
          symm
          refine Finset.sum_bij (fun s hs => (⟨s, hUE hs⟩ : E)) ?_ ?_ ?_ ?_
          · intro s hs
            have h1 := (Finset.mem_filter.mp hs).2
            rw [dif_pos (hUE hs)] at h1
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
          · intro s1 _ s2 _ heq; exact congrArg Subtype.val heq
          · intro s hs
            refine ⟨s.val, ?_, Subtype.ext rfl⟩
            exact Finset.mem_filter.mpr ⟨s.property, by rw [dif_pos s.property]; exact (Finset.mem_filter.mp hs).2⟩
          · intro s hs
            have h1 := (Finset.mem_filter.mp hs).2
            rw [dif_pos (hUE hs)] at h1
            rw [h1, one_mul]
        rw [hsum_h]; exact horth_h U hU_rel
      rw [hQpp_eq] at hh_mem
      rcases hh_mem with ⟨f, hf, hfeq⟩
      exact ⟨f, hf, fun s hs => hfeq ⟨s, hs⟩⟩
  refine ⟨?_, hpart2, ?_⟩
  -- Part 1: Classification + Uniqueness when E.card <= finrank W + 7
  · intro hEnull
    have hnull_sub : ∀ (U : Finset S), U ⊆ E → ∀ u0 ∈ U,
        U.card ≤ Module.finrank (ZMod 2) (affSpan U u0) + 7 := by
      intro U hUE u0 hu0
      have hmono := affNull_mono hUE hu0
      have hW_eq : affSpan E a = affSpan E u0 := affSpan_congr_base E haE (hUE hu0)
      have hE_le : E.card ≤ Module.finrank (ZMod 2) (affSpan E u0) + 7 := by
        rw [← hW_eq]; exact hEnull
      omega
    have hclass : ∀ U : Finset S, U ⊆ E → U.Nonempty → (rel U ↔ cube U ∨ twelve U) := by
      intro U hUE hUne
      constructor
      · intro hrel
        exact classify_rel_small_null U hUne hrel.2 (hnull_sub U hUE)
      · rintro (hc | ht)
        · exact ⟨hUE, hcube_orth U hc⟩
        · exact ⟨hUE, htwelve_orth U ht⟩
    refine ⟨hclass, fun U V hU hV hUne hVne => ?_⟩
    by_contra hUV_ne
    let D : Finset S := symmDiff U V
    have hD_sub : D ⊆ E := by
      intro s hs
      rcases Finset.mem_symmDiff.mp hs with ⟨hsU, _⟩ | ⟨hsV, _⟩
      · exact hU.1 hsU
      · exact hV.1 hsV
    have hD_ne : D.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      exact hUV_ne (symmDiff_eq_bot.mp hempty)
    have hD_rel : rel D := by
      refine ⟨hD_sub, fun f hf => ?_⟩
      have hsum_sd : ∑ s ∈ D, f s = (∑ s ∈ U, f s) + (∑ s ∈ V, f s) := by
        have h1 : U = (U \ V) ∪ (U ∩ V) := (Finset.sdiff_union_inter U V).symm
        have h2 : V = (V \ U) ∪ (U ∩ V) := by
          rw [Finset.inter_comm]; exact (Finset.sdiff_union_inter V U).symm
        have hd1 : Disjoint (U \ V) (U ∩ V) := Finset.disjoint_sdiff_inter U V
        have hd2 : Disjoint (V \ U) (U ∩ V) := by
          rw [Finset.inter_comm]; exact Finset.disjoint_sdiff_inter V U
        have hd3 : Disjoint (U \ V) (V \ U) := by
          rw [Finset.disjoint_left]; intro s hs1 hs2
          exact (Finset.mem_sdiff.mp hs1).2 (Finset.mem_sdiff.mp hs2).1
        have hUsum : ∑ s ∈ U, f s = (∑ s ∈ U \ V, f s) + ∑ s ∈ U ∩ V, f s := by
          conv_lhs => rw [h1]
          exact Finset.sum_union hd1
        have hVsum : ∑ s ∈ V, f s = (∑ s ∈ V \ U, f s) + ∑ s ∈ U ∩ V, f s := by
          conv_lhs => rw [h2]
          exact Finset.sum_union hd2
        have hD_eq : D = (U \ V) ∪ (V \ U) := rfl
        rw [hD_eq, Finset.sum_union hd3, hUsum, hVsum]
        have hdouble : (∑ s ∈ U ∩ V, f s) + (∑ s ∈ U ∩ V, f s) = 0 := zmod2_add_self _
        calc (∑ s ∈ U \ V, f s) + ∑ s ∈ V \ U, f s
            = (∑ s ∈ U \ V, f s) + (∑ s ∈ V \ U, f s) +
              ((∑ s ∈ U ∩ V, f s) + ∑ s ∈ U ∩ V, f s) := by rw [hdouble, add_zero]
          _ = ((∑ s ∈ U \ V, f s) + ∑ s ∈ U ∩ V, f s) +
              ((∑ s ∈ V \ U, f s) + ∑ s ∈ U ∩ V, f s) := by ring
      rw [hsum_sd, hU.2 f hf, hV.2 f hf, add_zero]
    have hU_cl := (hclass U hU.1 hUne).mp hU
    have hV_cl := (hclass V hV.1 hVne).mp hV
    have hD_cl := (hclass D hD_sub hD_ne).mp hD_rel
    have hcard_dim : ∀ X : Finset S, cube X ∨ twelve X →
        (X.card = 8 ∧ ∀ x0 ∈ X, Module.finrank (ZMod 2) (affSpan X x0) = 3) ∨
        (X.card = 12 ∧ ∀ x0 ∈ X, Module.finrank (ZMod 2) (affSpan X x0) = 5) := by
      intro X hX; rcases hX with hc | ht
      · exact Or.inl (hcube_info X hc)
      · exact Or.inr (htwelve_info X ht)
    have hD_card : D.card = 8 ∨ D.card = 12 := by
      rcases hcard_dim D hD_cl with ⟨h8, _⟩ | ⟨h12, _⟩
      · exact Or.inl h8
      · exact Or.inr h12
    have hsymm_card : U.card + V.card = D.card + 2 * (U ∩ V).card := by
      have h1 : (U \ V).card + (U ∩ V).card = U.card := Finset.card_sdiff_add_card_inter U V
      have h2 : (V \ U).card + (U ∩ V).card = V.card := by
        rw [Finset.inter_comm]; exact Finset.card_sdiff_add_card_inter V U
      have hd3 : Disjoint (U \ V) (V \ U) := by
        rw [Finset.disjoint_left]; intro s hs1 hs2
        exact (Finset.mem_sdiff.mp hs1).2 (Finset.mem_sdiff.mp hs2).1
      have hDc : D.card = (U \ V).card + (V \ U).card := Finset.card_union_of_disjoint hd3
      omega
    have hunion_card : (U ∪ V).card + (U ∩ V).card = U.card + V.card := Finset.card_union_add_card_inter U V
    have hunion_sub : U ∪ V ⊆ E := Finset.union_subset hU.1 hV.1
    by_cases hinter_ne : (U ∩ V).Nonempty
    · rcases hinter_ne with ⟨w, hw⟩
      have hwU : w ∈ U := (Finset.mem_inter.mp hw).1
      have hwV : w ∈ V := (Finset.mem_inter.mp hw).2
      have hwUV : w ∈ U ∪ V := Finset.mem_union_left V hwU
      have hnull_UV := hnull_sub (U ∪ V) hunion_sub w hwUV
      have hdim_ineq := affDim_union_le_of_inter U V hwU hwV
      have hpow_inter := card_le_two_pow_affDim (U ∩ V) hw
      let dI := Module.finrank (ZMod 2) (affSpan (U ∩ V) w)
      have hdI_ge1 : 2 ≤ (U ∩ V).card → 1 ≤ dI := by
        intro h2; by_contra h0; have hd0 : dI = 0 := by omega
        dsimp only [dI] at hd0; rw [hd0] at hpow_inter; norm_num at hpow_inter; omega
      have hdI_ge2 : 4 ≤ (U ∩ V).card → 2 ≤ dI := by
        intro h4; by_contra hlt
        have : dI = 0 ∨ dI = 1 := by omega
        rcases this with h0 | h1
        · dsimp only [dI] at h0; rw [h0] at hpow_inter; norm_num at hpow_inter; omega
        · dsimp only [dI] at h1; rw [h1] at hpow_inter; norm_num at hpow_inter; omega
      have hdI_ge3 : 6 ≤ (U ∩ V).card → 3 ≤ dI := by
        intro h6; by_contra hlt
        have : dI = 0 ∨ dI = 1 ∨ dI = 2 := by omega
        rcases this with h0 | h1 | h2
        · dsimp only [dI] at h0; rw [h0] at hpow_inter; norm_num at hpow_inter; omega
        · dsimp only [dI] at h1; rw [h1] at hpow_inter; norm_num at hpow_inter; omega
        · dsimp only [dI] at h2; rw [h2] at hpow_inter; norm_num at hpow_inter; omega
      rcases hcard_dim U hU_cl with ⟨hUc, hUd⟩ | ⟨hUc, hUd⟩ <;>
      rcases hcard_dim V hV_cl with ⟨hVc, hVd⟩ | ⟨hVc, hVd⟩ <;>
      rcases hD_card with hDc | hDc
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge2 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge1 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge3 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge2 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge3 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge2 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge3 (by omega); dsimp only [dI] at this; omega
      · have := hUd w hwU; have := hVd w hwV; have := hdI_ge3 (by omega); dsimp only [dI] at this; omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hinter_ne
      have hi0 : (U ∩ V).card = 0 := by rw [hinter_ne]; rfl
      rcases hUne with ⟨u0, hu0⟩
      rcases hVne with ⟨v0, hv0⟩
      have hnull_UV := hnull_sub (U ∪ V) hunion_sub u0 (Finset.mem_union_left V hu0)
      have hdim_disj := affDim_union_le_disj U V hu0 hv0
      rcases hcard_dim U hU_cl with ⟨hUc, hUd⟩ | ⟨hUc, hUd⟩ <;>
      rcases hcard_dim V hV_cl with ⟨hVc, hVd⟩ | ⟨hVc, hVd⟩
      · have := hUd u0 hu0; have := hVd v0 hv0; omega
      · have := hUd u0 hu0; have := hVd v0 hv0; omega
      · have := hUd u0 hu0; have := hVd v0 hv0; omega
      · have := hUd u0 hu0; have := hVd v0 hv0; omega
  -- Part 3: Unique nonempty relation O yields a cubic monomial correction
  · intro O hO hOne hOuniq
    rcases hOne with ⟨u0, hu0⟩
    have hO_card_ge2 : ∃ v0 ∈ O, v0 ≠ u0 := by
      by_contra hall; push_neg at hall
      have hOeq : O = {u0} := by
        ext s; simp only [Finset.mem_singleton]
        exact ⟨fun hs => hall s hs, fun h => h ▸ hu0⟩
      have h1 := hO.2 (fun _ => 1) (isQuad_const 1)
      rw [hOeq, Finset.sum_singleton] at h1
      exact one_ne_zero h1
    rcases hO_card_ge2 with ⟨v0, hv0, hv0_ne⟩
    have hex_l : ∃ l : Fin k, u0 l ≠ v0 l := by
      by_contra hall; push_neg at hall; exact hv0_ne (funext hall).symm
    rcases hex_l with ⟨l, hl_ne⟩
    let O1 : Finset S := O.filter (fun s => s l = 1)
    have hO1_sub : O1 ⊆ O := Finset.filter_subset _ _
    have hO1_ne : O1.Nonempty := by
      rcases zmod2_eq_zero_or_one (u0 l) with hu | hu <;>
      rcases zmod2_eq_zero_or_one (v0 l) with hv | hv
      · exact absurd (hu.trans hv.symm) hl_ne
      · exact ⟨v0, Finset.mem_filter.mpr ⟨hv0, hv⟩⟩
      · exact ⟨u0, Finset.mem_filter.mpr ⟨hu0, hu⟩⟩
      · exact absurd (hu.trans hv.symm) hl_ne
    have hO1_ne_O : O1 ≠ O := by
      intro heq
      rcases zmod2_eq_zero_or_one (u0 l) with hu | hu <;>
      rcases zmod2_eq_zero_or_one (v0 l) with hv | hv
      · exact absurd (hu.trans hv.symm) hl_ne
      · have hm : u0 ∈ O1 := heq ▸ hu0
        have h1 := (Finset.mem_filter.mp hm).2
        rw [hu] at h1; exact zero_ne_one h1
      · have hm : v0 ∈ O1 := heq ▸ hv0
        have h1 := (Finset.mem_filter.mp hm).2
        rw [hv] at h1; exact zero_ne_one h1
      · exact absurd (hu.trans hv.symm) hl_ne
    have hO1_not_rel : ¬ rel O1 := fun hr => hO1_ne_O (hOuniq O1 hr hO1_ne)
    have hex_f : ∃ f : S → F, quad f ∧ (∑ s ∈ O1, f s) ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hO1_not_rel ⟨Finset.Subset.trans hO1_sub hO.1, hall⟩
    rcases hex_f with ⟨f, hf, hf_ne⟩
    have hf1 : ∑ s ∈ O1, f s = 1 := (zmod2_eq_zero_or_one _).resolve_left hf_ne
    have hsum_O1 : ∑ s ∈ O1, f s = ∑ s ∈ O, f s * s l := by
      rw [← Finset.sum_filter_add_sum_filter_not O (fun s => s l = 1)]
      have h0 : ∑ s ∈ O.filter (fun s => ¬ s l = 1), f s * s l = 0 := by
        refine Finset.sum_eq_zero fun s hs => ?_
        have hne := (Finset.mem_filter.mp hs).2
        have hsl0 : s l = 0 := (zmod2_eq_zero_or_one (s l)).resolve_right hne
        rw [hsl0, mul_zero]
      rw [h0, add_zero]
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.mp hs).2, mul_one]
    rw [hsum_O1] at hf1
    rcases hf with ⟨b, lvec, M, hfeq⟩
    have hexp : ∑ s ∈ O, f s * s l =
        ∑ i : Fin k, ∑ j : Fin k, M i j * (∑ s ∈ O, s i * s j * s l) := by
      have hterm : ∀ s : S, f s * s l =
          (b * s l + ∑ i : Fin k, lvec i * (s i * s l)) +
          ∑ i : Fin k, ∑ j : Fin k, M i j * (s i * s j * s l) := by
        intro s
        rw [hfeq s, dotProduct, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
        congr 1
        · congr 1
          refine Finset.sum_congr rfl fun i _ => by ring
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by ring
      simp_rw [hterm, Finset.sum_add_distrib]
      have hq_part : ∑ s ∈ O, (b * s l + ∑ i : Fin k, lvec i * (s i * s l)) = 0 := by
        apply hO.2
        refine isQuad_add (isQuad_smul b (isQuad_coord l)) ?_
        exact isQuad_sum Finset.univ _ fun i _ => isQuad_smul (lvec i) (isQuad_mul_coord i l)
      rw [Finset.sum_add_distrib] at hq_part
      rw [hq_part, zero_add]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
    rw [hexp] at hf1
    have hex_ij : ∃ i j : Fin k, (∑ s ∈ O, s i * s j * s l) = 1 := by
      by_contra hall; push_neg at hall
      have hzero : ∀ i j : Fin k, (∑ s ∈ O, s i * s j * s l) = 0 := fun i j =>
        (zmod2_eq_zero_or_one _).resolve_right (hall i j)
      have h0 : ∑ i : Fin k, ∑ j : Fin k, M i j * (∑ s ∈ O, s i * s j * s l) = 0 := by
        refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
        rw [hzero i j, mul_zero]
      rw [h0] at hf1; exact zero_ne_one hf1
    rcases hex_ij with ⟨i, j, hij1⟩
    refine ⟨i, j, l, hij1, fun h => ?_⟩
    let cH : F := ∑ u ∈ O, h u
    let h' : S → F := fun s => h s + cH * s i * s j * s l
    have hh'_orth : ∀ U : Finset S, rel U → (∑ s ∈ U, h' s) = 0 := by
      intro U hU
      by_cases hUne : U.Nonempty
      · have hUO : U = O := hOuniq U hU hUne
        rw [hUO]
        dsimp only [h']
        rw [Finset.sum_add_distrib]
        have hfac : ∑ s ∈ O, cH * s i * s j * s l = cH * ∑ s ∈ O, s i * s j * s l := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun s _ => by ring
        rw [hfac, hij1, mul_one]
        exact zmod2_add_self cH
      · rw [Finset.not_nonempty_iff_eq_empty] at hUne; subst hUne; simp
    obtain ⟨f, hf, hfeq⟩ := (hpart2 h').mpr hh'_orth
    refine ⟨f, hf, fun s hs => ?_⟩
    have h1 := hfeq s hs
    dsimp only [h', cH] at h1
    have h2 := zmod2_add_self ((∑ u ∈ O, h u) * s i * s j * s l)
    calc h s = (h s + (∑ u ∈ O, h u) * s i * s j * s l) + (∑ u ∈ O, h u) * s i * s j * s l := by
          rw [add_assoc, h2, add_zero]
      _ = f s + (∑ u ∈ O, h u) * s i * s j * s l := by rw [h1]

end PEqualNP.Outside.L_lib_976_aux

open PEqualNP.Outside.L_lib_976_aux in
theorem PEqualNP.Outside.L_lib_976 :
∀ k : ℕ,
  let F := ZMod 2
  let S := Fin k → F
  let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
  ∀ (E : Finset S) (a : S), a ∈ E →
    let W := Submodule.span F (Set.image (fun s : S => s-a) (↑E : Set S))
    let rel := fun (U : Finset S) => U ⊆ E ∧ ∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0
    let cube := fun (U : Finset S) =>
      ∃ (b : S) (L : (Fin 3 → F) →ₗ[F] S), Function.Injective L ∧
        ∀ s : S, s ∈ U ↔ ∃ x : Fin 3 → F, s = b+L x
    let twelve := fun (U : Finset S) =>
      ∃ (b : S) (L : (Fin 5 → F) →ₗ[F] S), Function.Injective L ∧
        ∀ s : S, s ∈ U ↔ ∃ x : Fin 5 → F, x 0*x 1+x 2*x 3 = 1 ∧ s = b+L x
    (E.card ≤ Module.finrank F W + 7 →
      (∀ U : Finset S, U ⊆ E → U.Nonempty → (rel U ↔ cube U ∨ twelve U)) ∧
      ∀ U V : Finset S, rel U → rel V → U.Nonempty → V.Nonempty → U = V) ∧
    (∀ h : S → F, (∃ f : S → F, quad f ∧ ∀ s ∈ E, h s = f s) ↔
      ∀ U : Finset S, rel U → (∑ s ∈ U, h s) = 0) ∧
    ∀ O : Finset S, rel O → O.Nonempty →
      (∀ U : Finset S, rel U → U.Nonempty → U = O) →
      ∃ i j l : Fin k, (∑ s ∈ O, s i*s j*s l) = 1 ∧
        ∀ h : S → F, ∃ f : S → F, quad f ∧
          ∀ s ∈ E, h s = f s + (∑ u ∈ O, h u) * s i*s j*s l :=
  main_proof
