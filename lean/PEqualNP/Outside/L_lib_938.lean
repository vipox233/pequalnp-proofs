import Mathlib
import PEqualNP.Defs

open scoped BigOperators Topology
open Finset Filter

namespace PEqualNP.Outside.L_lib_938

def sign (b : Bool) : ℝ := if b then -1 else 1

lemma sign_sq (b : Bool) : (sign b)^2 = 1 := by
  cases b <;> norm_num [sign]

lemma sign_abs (b : Bool) : |sign b| = 1 := by
  cases b <;> norm_num [sign]

lemma sign_xor (b c : Bool) : sign (xor b c) = sign b * sign c := by
  cases b <;> cases c <;> norm_num [sign]

lemma sign_eq (b c : Bool) : sign b * sign c = 2 * (if b = c then 1 else 0) - 1 := by
  cases b <;> cases c <;> norm_num [sign]

-- The filtered-product calculation follows L-lib-907, PR 43941.
lemma sign_parity {I : Type*} [Fintype I] (f : I → Bool) :
    sign ((univ.filter fun i => f i).card % 2 == 1) = ∏ i, sign (f i) := by
  classical
  have h : (∏ i, sign (f i)) = ∏ i ∈ univ.filter (fun i => f i), (-1 : ℝ) := by
    rw [prod_filter]
    rfl
  rw [h, prod_const, neg_one_pow_eq_ite]
  simp only [Nat.even_iff]
  by_cases h₀ : (univ.filter fun i => f i).card % 2 = 0
  · simp [h₀, sign]
  · have h₁ : (univ.filter fun i => f i).card % 2 = 1 := by omega
    simp [h₁, sign]

noncomputable def corr {X Y : Type*} [Fintype Y] (s : X → Y → ℝ) (x u : X) : ℝ :=
  𝔼 y, s x y * s u y

lemma corr_symm {X Y : Type*} [Fintype Y] (s : X → Y → ℝ) (x u : X) :
    corr s x u = corr s u x := by simp [corr, mul_comm]

lemma corr_self {X Y : Type*} [Fintype Y] [Nonempty Y] (s : X → Y → Bool) (x : X) :
    corr (fun x y => sign (s x y)) x x = 1 := by
  simp [corr, ← pow_two, sign_sq]

lemma sum_le_of_one_lt {I : Type*} [Fintype I] (g : I → ℝ) (j : I)
    (hj : g j ≤ -1) (hg : ∀ i, g i ≤ 1) :
    ∑ i, g i ≤ (Fintype.card I : ℝ) - 2 := by
  classical
  calc
    _ ≤ ∑ i, (if i = j then (-1 : ℝ) else 1) := by
      apply sum_le_sum
      intro i _
      by_cases hi : i = j
      · simpa [hi] using hj
      · simpa [hi] using hg i
    _ = _ := by
      have he : ∀ i : I, (if i = j then (-1 : ℝ) else 1) =
          1 - if i = j then 2 else 0 := by
        intro i
        split <;> norm_num
      simp [he, sum_sub_distrib]

lemma coordinate_corr {k : ℕ} (hk : 0 < k) (g h : Fin k → Bool)
    (he : ∃ j, g j = h j) (hn : ∃ j, g j ≠ h j) :
    |𝔼 j, sign (g j) * sign (h j)| ≤ 1 - 1 / (k : ℝ) := by
  classical
  obtain ⟨j, hj⟩ := he
  obtain ⟨i, hi⟩ := hn
  let c : Fin k → ℝ := fun j => sign (g j) * sign (h j)
  have h₁ := sum_le_of_one_lt c i (by simp [c, sign_eq, hi])
    (fun j => by simp only [c, sign_eq]; split <;> norm_num)
  have h₂ := sum_le_of_one_lt (fun j => -c j) j (by norm_num [c, sign_eq, hj])
    (fun j => by simp only [c, sign_eq]; split <;> norm_num)
  simp only [Fintype.card_fin] at h₁ h₂
  rw [sum_neg_distrib] at h₂
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  change |𝔼 j, c j| ≤ _
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, abs_le]
  constructor
  · apply (le_div_iff₀ hk').2
    rw [neg_mul, sub_mul, one_mul, div_mul_cancel₀ _ hk'.ne']
    linarith
  · apply (div_le_iff₀ hk').2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hk'.ne']
    linarith

lemma expect_prod_pi {m k : ℕ} (_hk : 0 < k) (g : Fin m → Fin k → ℝ) :
    (𝔼 y : Fin m → Fin k, ∏ i, g i (y i)) = ∏ i, 𝔼 j, g i j := by
  classical
  simp_rw [Fintype.expect_eq_sum_div_card, Fintype.card_pi_const, Fintype.card_fin,
    Nat.cast_pow, prod_div_distrib, prod_const, card_univ, Fintype.card_fin]
  rw [Fintype.prod_sum]

noncomputable def kernel {m q : ℕ} (t : ℝ) (x u : Fin m → Fin q) : ℝ :=
  ∏ i, if x i = u i then 1 else t

lemma kernel_nonneg {m q : ℕ} {t : ℝ} (ht : 0 ≤ t) (x u : Fin m → Fin q) :
    0 ≤ kernel t x u := by
  apply prod_nonneg
  intro i _
  split <;> positivity

lemma kernel_diag {m q : ℕ} (t : ℝ) (x : Fin m → Fin q) :
    kernel t x x = 1 := by simp [kernel]

lemma kernel_off {m q : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1)
    {x u : Fin m → Fin q} (hne : x ≠ u) : kernel t x u ≤ t := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ u j := by simpa [funext_iff] using hne
  calc
    _ ≤ ∏ i : Fin m, if i = j then t else 1 := by
      apply prod_le_prod₀
      · intro i _
        split <;> positivity
      · intro i _
        by_cases hi : i = j
        · subst i
          simp [hj]
        · simp only [hi, ite_false]
          split <;> simp [ht']
    _ = _ := by
      rw [prod_ite, prod_const_one, mul_one]
      have hfilter : (univ.filter fun i : Fin m => i = j) = {j} := by ext i; simp
      rw [hfilter, prod_singleton]

lemma kernel_pow {m q : ℕ} (t : ℝ) (p : ℕ) (x u : Fin m → Fin q) :
    (kernel t x u)^p = kernel (t^p) x u := by
  unfold kernel
  rw [← prod_pow]
  apply prod_congr rfl
  intro i _
  split <;> simp

lemma kernel_sum {m q : ℕ} (t : ℝ) (x : Fin m → Fin q) :
    ∑ u, kernel t x u = (1 + ((q : ℝ) - 1) * t)^m := by
  classical
  unfold kernel
  rw [← Fintype.prod_sum (fun i (j : Fin q) => if x i = j then (1 : ℝ) else t)]
  have h (i : Fin m) :
      (∑ j : Fin q, if x i = j then (1 : ℝ) else t) = 1 + ((q : ℝ) - 1) * t := by
    have h' : ∀ j : Fin q, (if x i = j then (1 : ℝ) else t) =
        t + if x i = j then 1 - t else 0 := by
      intro j
      split <;> simp
    simp [h', sum_add_distrib]
    ring
  simp [h]

lemma product_corr {m q k : ℕ} (hk : 0 < k)
    (f : Fin m → Fin q → Fin k → Bool)
    (hf : ∀ i u v, u ≠ v →
      (∃ j, f i u j = f i v j) ∧ (∃ j, f i u j ≠ f i v j))
    (left : (Fin m → Fin q) → Bool) (right : (Fin m → Fin k) → Bool)
    (x u : Fin m → Fin q) :
    |corr (fun x y => sign (xor (xor (left x) (right y))
       ((univ.filter fun i => f i (x i) (y i)).card % 2 == 1))) x u|
      ≤ kernel (1 - 1 / (k : ℝ)) x u := by
  classical
  let g := fun i j => sign (f i (x i) j) * sign (f i (u i) j)
  have he : ∀ y : Fin m → Fin k,
      sign (xor (xor (left x) (right y))
        ((univ.filter fun i => f i (x i) (y i)).card % 2 == 1)) *
      sign (xor (xor (left u) (right y))
        ((univ.filter fun i => f i (u i) (y i)).card % 2 == 1)) =
      (sign (left x) * sign (left u)) * ∏ i, g i (y i) := by
    intro y
    simp only [sign_xor, sign_parity, g, prod_mul_distrib]
    have hr : sign (right y)^2 = 1 := sign_sq _
    linear_combination (sign (left x) * sign (left u) *
      (∏ i, sign (f i (x i) (y i))) * (∏ i, sign (f i (u i) (y i)))) * hr
  unfold corr
  simp_rw [he]
  rw [← mul_expect, abs_mul, abs_mul, sign_abs, sign_abs, one_mul, one_mul,
    expect_prod_pi hk, abs_prod]
  apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
  intro i _
  by_cases hi : x i = u i
  · have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    simp [g, hi, ← pow_two, sign_sq]
  · simp only [hi, ite_false]
    exact coordinate_corr hk _ _ (hf _ _ _ hi).1 (hf _ _ _ hi).2

-- A pointwise charge using binary Kraft weights and integer lengths.
lemma binary_pay (l h : ℕ) : (h : ℝ) ≤ (l : ℝ) - 1 + (2 : ℝ)^h / 2^l := by
  by_cases hl : l ≤ h
  · have hh : (h - l : ℕ) + l = h := Nat.sub_add_cancel hl
    have hpow : (2 : ℝ)^h / 2^l = 2^(h-l) := by
      conv_lhs => rw [← hh, pow_add]
      exact mul_div_cancel_right₀ _ (by positivity)
    rw [hpow]
    have hsum : ((h - l : ℕ) : ℝ) + (l : ℝ) = (h : ℝ) := by exact_mod_cast hh
    have hbound : ((h - l : ℕ) : ℝ) + 1 ≤ (2 : ℝ)^(h-l) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := h-l))
    linarith
  · have hl' : h + 1 ≤ l := by omega
    have hl'' : (h : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hl'
    linarith [show 0 ≤ (2:ℝ)^h / 2^l by positivity]

lemma class_pay (L h l s : ℕ) (v : ℝ) (hs : s ≤ 2^L) (hl : 0 < l) (hs₀ : 0 < s)
    (hone : s = 1 → v ≤ L)
    (hsmall : 1 < s → s ≤ 2^h → v ≤ ((L : ℝ)-h)*s)
    (hlarge : 2^h < s → v ≤ (s : ℝ)/2) :
    v ≤ (s : ℝ) * ((l : ℝ) - 1) + (2 : ℝ)^L / 2^l := by
  have hpow : 0 < (2 : ℝ)^l := by positivity
  by_cases h₁ : s = 1
  · simpa [h₁] using (hone h₁).trans (binary_pay l L)
  by_cases h₂ : s ≤ 2^h
  · have hspos : 1 < s := by omega
    have hh₂ : (s : ℝ) ≤ (2 : ℝ)^h := by exact_mod_cast h₂
    have hLe : (L : ℝ) - h ≤ (l : ℝ) - 1 + ((2 : ℝ)^L / 2^h) / 2^l := by
      by_cases hh : h ≤ L
      · have h_eq : (2 : ℝ)^L / 2^h = 2^(L-h) := by
          conv_lhs => rw [← Nat.sub_add_cancel hh, pow_add]
          exact mul_div_cancel_right₀ _ (by positivity)
        rw [h_eq, ← Nat.cast_sub hh]
        exact binary_pay _ _
      · have h' : (L : ℝ) ≤ (h : ℝ) := by exact_mod_cast (by omega : L ≤ h)
        have hl' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
        linarith [show 0 ≤ ((2 : ℝ)^L / 2^h) / 2^l by positivity]
    calc
      _ ≤ ((L : ℝ)-h)*s := hsmall hspos h₂
      _ ≤ ((l : ℝ) - 1 + ((2 : ℝ)^L / 2^h) / 2^l) * s :=
        mul_le_mul_of_nonneg_right hLe (by positivity)
      _ = (s : ℝ) * ((l : ℝ) - 1) + ((2 : ℝ)^L / 2^l) * ((s : ℝ) / 2^h) := by ring
      _ ≤ _ := by
        apply add_le_add_right
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          ((div_le_one (by positivity)).2 hh₂) (show 0 ≤ (2:ℝ)^L / 2^l by positivity)
  · have h' := hlarge (by omega)
    by_cases hl₁ : l = 1
    · have hs' : (s : ℝ) ≤ (2 : ℝ)^L := by exact_mod_cast hs
      simpa [hl₁] using h'.trans (div_le_div_of_nonneg_right hs' (by norm_num : (0:ℝ) ≤ 2))
    · have hl' : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast (by omega : 2 ≤ l)
      have h₃ : (s : ℝ) / 2 ≤ (s : ℝ) * ((l : ℝ) - 1) := by
        have hh := mul_le_mul_of_nonneg_left (show (1/2:ℝ) ≤ (l : ℝ) - 1 by linarith)
          (Nat.cast_nonneg s)
        linarith
      exact h'.trans (h₃.trans (le_add_of_nonneg_right (by positivity)))

lemma code_prefix {X : Type*} [Fintype X] (send : X → List Bool)
    (hp : ∀ x x' tail, send x ++ tail = send x' → tail = []) :
    InformationTheory.IsPrefixFree ((univ.image send : Finset (List Bool)) : Set (List Bool)) := by
  intro c hc d hd hcd
  obtain ⟨x, _, rfl⟩ := mem_image.mp hc
  obtain ⟨x', _, rfl⟩ := mem_image.mp hd
  obtain ⟨tail, htail⟩ := hcd
  have ht := hp x x' tail (by exact htail)
  simpa [ht] using htail

lemma code_cost {X : Type*} [Fintype X] (L h : ℕ) (hsz : Fintype.card X = 2^L)
    (send : X → List Bool) (g : X → ℝ) (hp : ∀ x x' tail, send x ++ tail = send x' → tail = [])
    (hone : ∀ x, g x ≤ 1)
    (hsilent : (∀ x, send x = []) → ∑ x, g x = 0)
    (hsmall : ∀ S : Finset X, (∀ x ∈ S, ∀ y ∈ S, send x = send y) →
      1 < S.card → S.card ≤ 2^h →
        (L : ℝ) * (∑ x ∈ S, g x) ≤ ((L : ℝ)-h)*S.card)
    (hlarge : ∀ S : Finset X, (∀ x ∈ S, ∀ y ∈ S, send x = send y) →
      2^h < S.card → (L : ℝ) * (∑ x ∈ S, g x) ≤ (S.card : ℝ)/2) :
    (L : ℝ) * (∑ x, g x) ≤ ∑ x, ((send x).length : ℝ) := by
  classical
  by_cases he : ∃ x, send x = []
  · obtain ⟨x, hx⟩ := he
    have hz (y : X) : send y = [] :=
      hp x y (send y) (by simp [hx])
    simp [hsilent hz, hz]
  let C := univ.image send
  let fiber := fun c => univ.filter fun x => send x = c
  have hmaps (x) (_ : x ∈ (univ : Finset X)) : send x ∈ C := mem_image_of_mem _ (mem_univ _)
  have hdecomp (u : X → ℝ) : (∑ c ∈ C, ∑ x ∈ fiber c, u x) = ∑ x, u x :=
    sum_fiberwise_of_maps_to hmaps u
  have hkc := InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one
    (code_prefix send hp)
  have hk : ∑ c ∈ C, (2:ℝ)^L / 2^c.length ≤ 2^L := by
    simp only [Fintype.card_bool, Nat.cast_ofNat] at hkc
    simpa [C, mul_sum, div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hkc (show 0 ≤ (2:ℝ)^L by positivity)
  have hpoint (c : List Bool) (hc : c ∈ C) :
      (L : ℝ) * (∑ x ∈ fiber c, g x) ≤
        ((fiber c).card : ℝ) * ((c.length : ℝ)-1) + (2:ℝ)^L / 2^c.length := by
    obtain ⟨x, _, hx⟩ := mem_image.mp hc
    have hn : 0 < (fiber c).card := card_pos.2 ⟨x, by simp [fiber, hx]⟩
    have hl : 0 < c.length := by
      apply List.length_pos_iff.mpr
      rintro rfl
      exact he ⟨x, hx⟩
    have hcard : (fiber c).card ≤ 2^L := by
      rw [← hsz, ← card_univ]
      exact card_le_card (filter_subset _ _)
    have hcons : ∀ x ∈ fiber c, ∀ y ∈ fiber c, send x = send y := by
      intro x hx y hy
      exact ((mem_filter.mp hx).2).trans (mem_filter.mp hy).2.symm
    apply class_pay L h c.length (fiber c).card _ hcard hl hn
    · intro hcard
      have hb := sum_le_sum (s := fiber c) (fun x _ => hone x)
      simp [hcard] at hb
      simpa using mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg L)
    · exact hsmall _ hcons
    · exact hlarge _ hcons
  have hsum := sum_le_sum (s := C) hpoint
  have hcost :
      (∑ c ∈ C, ((fiber c).card : ℝ) * ((c.length : ℝ) - 1)) =
        (∑ x, ((send x).length : ℝ)) - (2 : ℝ)^L := by
    calc
      _ = ∑ c ∈ C, ∑ x ∈ fiber c, (((send x).length : ℝ)-1) := by
        apply sum_congr rfl
        intro c _
        have hf (x : X) (hx : x ∈ fiber c) : send x = c := (mem_filter.mp hx).2
        calc
          _ = ∑ _x ∈ fiber c, ((c.length : ℝ)-1) := by simp [mul_sub]
          _ = _ := sum_congr rfl fun x hx => by rw [hf x hx]
      _ = _ := by
        rw [hdecomp, sum_sub_distrib]
        simp [hsz]
  rw [← mul_sum, hdecomp, sum_add_distrib, hcost] at hsum
  linarith

noncomputable def meanAbs {X Y : Type*} [Fintype Y]
    (s : X → Y → ℝ) (C : Finset X) : ℝ :=
  𝔼 y, |𝔼 x ∈ C, s x y|

lemma meanAbs_sq {X Y : Type*} [Fintype Y] [Nonempty Y]
    (s : X → Y → ℝ) (C : Finset X) :
    (meanAbs s C)^2 ≤ 𝔼 x ∈ C, 𝔼 u ∈ C, |corr s x u| := by
  calc
    _ ≤ 𝔼 y, (𝔼 x ∈ C, s x y)^2 := by
      simpa [meanAbs, sq_abs] using
        (expect_mul_sq_le_sq_mul_sq (univ : Finset Y) (fun y => |𝔼 x ∈ C, s x y|)
          (fun _ => (1:ℝ)))
    _ = 𝔼 x ∈ C, 𝔼 u ∈ C, corr s x u := by
      simp_rw [pow_two, Finset.expect_mul_expect, corr]
      rw [expect_comm (univ : Finset Y) C]
      exact expect_congr rfl fun x _ => expect_comm _ _ _
    _ ≤ _ := expect_le_expect fun x _ => expect_le_expect fun u _ => le_abs_self _

lemma meanAbs_row {X Y : Type*} [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]
    (s : X → Y → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hrow : ∀ x, (𝔼 u, |corr s x u|) ≤ T^2) :
    meanAbs s univ ≤ T := by
  have h := (meanAbs_sq s univ).trans (expect_le_expect (fun x _ => hrow x))
  rw [Fintype.expect_const] at h
  by_contra! h'
  exact (not_lt_of_ge h) (pow_lt_pow_left₀ h' hT (by decide : 2 ≠ 0))

lemma class_mean_bound {X Y : Type*} [Fintype Y] [Nonempty Y]
    (b : X → Y → Bool) {e : ℝ} (w : X → Y → ℝ)
    (hw : ∀ x, (𝔼 y, |w x y - 1|) ≤ e) (C : Finset X) (hC : C.Nonempty) (read : Y → Bool) :
    (𝔼 x ∈ C, 𝔼 y, w x y * (sign (b x y) * sign (read y))) ≤
      meanAbs (fun x y => sign (b x y)) C + e := by
  let s := fun x y => sign (b x y)
  let D := fun y => sign (read y)
  calc
    _ = (𝔼 x ∈ C, 𝔼 y, ((s x y * D y) + (w x y - 1) * (s x y * D y))) := by
      apply expect_congr rfl
      intro x _
      apply expect_congr rfl
      intro y _
      dsimp [s, D]
      ring
    _ = (𝔼 y, (𝔼 x ∈ C, s x y) * D y) +
        (𝔼 x ∈ C, 𝔼 y, (w x y - 1) * (s x y * D y)) := by
      simp_rw [expect_add_distrib]
      rw [expect_comm C, expect_congr (s := (univ : Finset Y)) rfl]
      intro y _
      exact (expect_mul _ _ _).symm
    _ ≤ _ := by
      apply add_le_add
      · apply expect_le_expect
        intro y _
        calc
          _ ≤ |(𝔼 x ∈ C, s x y) * D y| := le_abs_self _
          _ = _ := by simp [abs_mul, s, D, sign_abs]
      · apply expect_le hC
        intro x _
        refine (expect_le_expect fun y _ => ?_).trans (hw x)
        calc
          _ ≤ |(w x y - 1) * (s x y * D y)| := le_abs_self _
          _ = _ := by simp [abs_mul, s, D, sign_abs]

lemma class_mean_small {X Y : Type*} [Fintype Y] [Nonempty Y]
    (b : X → Y → Bool) {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hoff : ∀ x u, x ≠ u → |corr (fun x y => sign (b x y)) x u| ≤ ρ)
    (C : Finset X) (hC : 1 < C.card) :
    meanAbs (fun x y => sign (b x y)) C ≤ 1 - (1 - ρ) / 4 := by
  classical
  let s := fun x y => sign (b x y)
  have h2 : (2:ℝ) ≤ C.card := by exact_mod_cast hC
  have hpos : 0 < (C.card : ℝ) := by linarith
  have hrow (x : X) (hx : x ∈ C) : (𝔼 u ∈ C, |corr s x u|) ≤ (1 + ρ) / 2 := by
    calc
      _ ≤ 𝔼 u ∈ C, (ρ + if u = x then 1 - ρ else 0) := by
        apply expect_le_expect
        intro u _
        by_cases he : u = x
        · subst u
          simp [s, corr_self]
        · simpa [he] using hoff x u (Ne.symm he)
      _ = ρ + (1 - ρ) / C.card := by
        rw [expect_add_distrib, expect_const ⟨x,hx⟩,
          expect_eq_sum_div_card]
        simp [hx]
      _ ≤ _ := by
        have h := div_le_div_of_nonneg_left (sub_nonneg.mpr hρ₁)
          (by norm_num : (0:ℝ) < 2) h2
        linarith
  have hC' : C.Nonempty := card_pos.mp (by omega)
  have hsq := (meanAbs_sq s C).trans (expect_le hC' hrow)
  have ht : 0 ≤ 1 - (1 - ρ) / 4 := by linarith
  by_contra! hn
  have hp := pow_lt_pow_left₀ hn ht (by decide : 2 ≠ 0)
  nlinarith [sq_nonneg (1 - ρ)]

lemma expect_pow_le {X : Type*} (C : Finset X) (hC : C.Nonempty) (g : X → ℝ)
    (hg : ∀ x ∈ C, 0 ≤ g x) (p : ℕ) :
    (𝔼 x ∈ C, g x)^p ≤ 𝔼 x ∈ C, (g x)^p := by
  have hn : (C.card : ℝ) ≠ 0 := by exact_mod_cast hC.card_ne_zero
  have hw : (∑ _x ∈ C, (C.card : ℝ)⁻¹) = 1 := by simp [hn]
  simpa [expect_eq_sum_div_card, ← mul_sum, div_eq_inv_mul] using
    Real.pow_arith_mean_le_arith_mean_pow C (fun _ => (C.card : ℝ)⁻¹) g
      (fun _ _ => by positivity) hw hg p

-- The symmetric pair weight is supported on disagreements.
noncomputable def pairWeight {X Y : Type*} [DecidableEq X] [Fintype Y]
    (b : X → Y → Bool) (x u : X) (y : Y) : ℝ :=
  if x = u then 0 else
    (1 - sign (b x y) * sign (b u y)) / (1 - corr (fun x y => sign (b x y)) x u)

lemma make_weights {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (b : X → Y → Bool) (hN : 1 < Fintype.card X)
    {ρ T : ℝ} (hρ : ρ < 1) (hT : 0 ≤ T) (hT₁ : T ≤ 1)
    (hoff : ∀ x u, x ≠ u → |corr (fun x y => sign (b x y)) x u| ≤ ρ)
    (hrow : ∀ x, (𝔼 u, |corr (fun x y => sign (b x y)) x u|) ≤ T^2) :
    ∃ w : X → Y → ℝ,
      (∀ x y, 0 ≤ w x y) ∧
      (∀ x, (𝔼 y, w x y) = 1) ∧
      (∀ y, (𝔼 x, w x y * sign (b x y)) = 0) ∧
      (∀ x, (𝔼 y, |w x y - 1|) ≤ 6*T) := by
  classical
  let s := fun x y => sign (b x y)
  let P := pairWeight b
  let N : ℝ := Fintype.card X
  let c : ℝ := 1 - 1/N
  have hN' : (2:ℝ) ≤ N := by
    change (2:ℝ) ≤ (Fintype.card X : ℝ)
    exact_mod_cast (show 2 ≤ Fintype.card X by omega)
  have hc : (1/2:ℝ) ≤ c := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
      (by norm_num : (0:ℝ) < 2) hN'
    dsimp [c]
    linarith
  have hc₀ : 0 < c := by linarith
  have : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hden (x u : X) (hu : x ≠ u) : 0 < 1 - corr s x u :=
    sub_pos.mpr ((le_abs_self _).trans_lt ((hoff x u hu).trans_lt hρ))
  have hP₀ (x u : X) (y : Y) : 0 ≤ P x u y := by
    by_cases hu : x = u
    · simp [P, pairWeight, hu]
    · simp only [P, pairWeight, hu, ite_false]
      apply div_nonneg _ (hden x u hu).le
      cases b x y <;> cases b u y <;> norm_num [sign]
  have hPmean (x u : X) : (𝔼 y, P x u y) = if u = x then 0 else 1 := by
    by_cases hu : x = u
    · simp [P, pairWeight, hu]
    · simp only [P, pairWeight, hu, Ne.symm hu, ite_false]
      rw [← expect_div, expect_sub_distrib, Fintype.expect_one]
      exact div_self (hden x u hu).ne'
  have hPeq (x u : X) (y : Y) :
      P x u y = (1 - s x y * s u y) + corr s x u * P x u y := by
    by_cases hu : x = u
    · subst u
      simp [P, pairWeight, s, ← pow_two, sign_sq]
    · simp only [P, pairWeight, hu, ite_false]
      change (1 - s x y * s u y) / (1 - corr s x u) =
        (1 - s x y * s u y) + corr s x u *
          ((1 - s x y * s u y) / (1 - corr s x u))
      field_simp [(hden x u hu).ne']; ring
  have hPswap (x u : X) (y : Y) : P x u y * s x y = -(P u x y * s u y) := by
    by_cases hu : x = u
    · simp [P, pairWeight, hu]
    · simp only [P, pairWeight, hu, Ne.symm hu, ite_false]
      have e : corr (fun x y => sign (b x y)) u x = corr s x u := corr_symm s u x
      rw [e]
      cases hx : b x y <;> cases hy : b u y <;> simp [s, hx, hy, sign]
  have hdiag (x : X) : (𝔼 u, (if u = x then (1:ℝ) else 0)) = 1/N := by
    rw [Fintype.expect_eq_sum_div_card]
    simp [N]
  have hoffmean (x : X) : (𝔼 u, (if u = x then (0:ℝ) else 1)) = c := by
    change _ = 1 - 1/N
    rw [← hdiag x, ← Fintype.expect_one (ι := X) (M := ℝ), ← expect_sub_distrib]
    apply expect_congr rfl
    intro u _
    split <;> norm_num
  let w := fun x y => (𝔼 u, P x u y) / c
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact div_nonneg (expect_nonneg fun u _ => hP₀ x u y) hc₀.le
  · intro x
    dsimp [w]
    rw [← expect_div, expect_comm]
    simp_rw [hPmean]
    exact div_eq_one_iff_eq (ne_of_gt hc₀) |>.2 (hoffmean x)
  · intro y
    have hn : (𝔼 x, 𝔼 u, P x u y * s x y) = 0 := by
      have hed : (𝔼 x, 𝔼 u, P x u y * s x y) =
          -(𝔼 x, 𝔼 u, P x u y * s x y) := by
        calc
          _ = 𝔼 x, 𝔼 u, -(P u x y * s u y) :=
            expect_congr rfl fun x _ => expect_congr rfl fun u _ => hPswap x u y
          _ = -(𝔼 x, 𝔼 u, P u x y * s u y) := by simp only [expect_neg_distrib]
          _ = _ := congrArg Neg.neg (expect_comm _ _ (fun x u => P u x y * s u y))
      linarith
    change (𝔼 x, (𝔼 u, P x u y) / c * s x y) = _
    calc
      _ = 𝔼 x, (𝔼 u, P x u y * s x y) / c := by
        apply expect_congr rfl
        intro x _
        rw [div_mul_eq_mul_div, expect_mul]
      _ = _ := by rw [← expect_div, hn, zero_div]
  · intro x
    have hglobal : meanAbs s univ ≤ T := meanAbs_row s hT hrow
    have hdc : 1/N ≤ T^2 := by
      rw [← hdiag x]
      refine (expect_le_expect fun u _ => ?_).trans (hrow x)
      by_cases he : u = x
      · subst u
        simp [corr_self]
      · simp [he, abs_nonneg]
    have hdiff (y : Y) : c * (w x y - 1) =
        (1/N) - s x y * (𝔼 u, s u y) + (𝔼 u, corr s x u * P x u y) := by
      have he : (𝔼 u, P x u y) =
          1 - s x y * (𝔼 u, s u y) + (𝔼 u, corr s x u * P x u y) := by
        calc
          _ = 𝔼 u, ((1 - s x y * s u y) + corr s x u * P x u y) :=
            expect_congr rfl fun u _ => hPeq x u y
          _ = _ := by rw [expect_add_distrib, expect_sub_distrib, Fintype.expect_one, mul_expect]
      change c * ((𝔼 u, P x u y) / c - 1) = _
      rw [he, mul_sub, mul_one, mul_div_cancel₀ _ hc₀.ne']
      dsimp [c]
      ring
    have hpoint (y : Y) : c * |w x y - 1| ≤
        (1/N) + |𝔼 u, s u y| + (𝔼 u, |corr s x u| * P x u y) := by
      rw [← abs_of_nonneg hc₀.le, ← abs_mul, hdiff]
      calc
        _ ≤ |(1/N) - s x y * (𝔼 u, s u y)| + |𝔼 u, corr s x u * P x u y| := abs_add_le _ _
        _ ≤ _ := by
          apply add_le_add
          · simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (show 0 ≤ 1/N by positivity),
                abs_mul, s, sign_abs, one_mul] using
              abs_sub_le (1/N) 0 (s x y * (𝔼 u, s u y))
          · refine (abs_expect_le _ _).trans (expect_le_expect fun u _ => ?_)
            rw [abs_mul, abs_of_nonneg (hP₀ x u y)]
    have hcor : (𝔼 y, 𝔼 u, |corr s x u| * P x u y) ≤ T^2 := by
      rw [expect_comm]
      refine (expect_le_expect fun u _ => ?_).trans (hrow x)
      rw [← mul_expect]
      change |corr s x u| * (𝔼 y, P x u y) ≤ |corr s x u|
      rw [hPmean]
      split <;> simp [abs_nonneg]
    have hev := expect_le_expect (s := (univ : Finset Y)) (fun y _ => hpoint y)
    rw [← mul_expect, expect_add_distrib, expect_add_distrib, Fintype.expect_const] at hev
    change c * (𝔼 y, |w x y - 1|) ≤ 1/N + meanAbs s univ +
      (𝔼 y, 𝔼 u, |corr s x u| * P x u y) at hev
    have hl : 0 ≤ 𝔼 y, |w x y - 1| := expect_nonneg fun _ _ => abs_nonneg _
    have hhalf := mul_le_mul_of_nonneg_right hc hl
    have hTsq : T^2 ≤ T := by nlinarith [mul_nonneg hT (sub_nonneg.mpr hT₁)]
    linarith

-- Fixed powers give uniform bounds as the number of coordinates grows.
lemma choose_scales (a q : ℕ) (ha : 0 < a) (hq : 1 < q)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) :
    ∃ (D p : ℕ) (b t u : ℝ),
      0 < D ∧ 0 < p ∧ 1 < b ∧ b^D = 2 ∧
      0 ≤ t ∧ t < 1 ∧ 0 ≤ u ∧ u < 1 ∧
      u^2 = (1 + ((q : ℝ) - 1)*ρ)/q ∧
      1 + ((q : ℝ) - 1)*ρ^p = b*t^(2*p) ∧
      ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
        ((m/D : ℕ) : ℝ) ≤ ((1-ρ)/8)*((a*m : ℕ) : ℝ) ∧
        6*u^m ≤ (1-ρ)/8 ∧ ((a*m : ℕ) : ℝ)*(2*t^m + 6*u^m) ≤ 1/2 := by
  let δ : ℝ := (1-ρ)/8
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨D, hD⟩ := exists_nat_gt (1/δ)
  have hDpos' : 0 < (D : ℝ) := (by positivity : 0 < 1/δ).trans hD
  have hDpos : 0 < D := by exact_mod_cast hDpos'
  have hDδ : 1 ≤ δ*(D:ℝ) := by
    have hh := (div_lt_iff₀ hδ).mp hD
    linarith
  let b : ℝ := (2:ℝ) ^ ((D:ℝ)⁻¹)
  have hb : 1 < b := Real.one_lt_rpow (by norm_num) (inv_pos.mpr hDpos')
  have hbD : b^D = 2 := by
    dsimp [b]
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
      inv_mul_cancel₀ hDpos'.ne', Real.rpow_one]
  have hQ : (1:ℝ) < q := by exact_mod_cast hq
  have hlim : Tendsto (fun n : ℕ => 1 + ((q : ℝ)-1)*ρ^n) atTop (𝓝 1) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀ hρ₁).const_mul
      ((q:ℝ)-1)).const_add 1
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hb))
  let p := max 1 p₀
  have hp : 0 < p := by dsimp [p]; omega
  have hBp : 1 + ((q:ℝ)-1)*ρ^p < b := hp₀ p (le_max_right _ _)
  let B : ℝ := 1 + ((q:ℝ)-1)*ρ^p
  have hB : 0 < B := by
    dsimp [B]
    have hh := mul_nonneg (sub_nonneg.mpr hQ.le) (pow_nonneg hρ₀ p)
    linarith
  have hbpos : 0 < b := by linarith
  have hBb₀ : 0 ≤ B/b := div_nonneg hB.le hbpos.le
  have hBb₁ : B/b < 1 := (div_lt_one hbpos).2 hBp
  let t : ℝ := (B/b) ^ (((2*p : ℕ) : ℝ)⁻¹)
  have hh : 0 < ((2*p : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2*p by omega)
  have ht₀ : 0 ≤ t := Real.rpow_nonneg hBb₀ _
  have ht₁ : t < 1 := Real.rpow_lt_one hBb₀ hBb₁ (inv_pos.mpr hh)
  have htP : t^(2*p) = B/b := by
    dsimp [t]
    rw [← Real.rpow_mul_natCast hBb₀, inv_mul_cancel₀ hh.ne', Real.rpow_one]
  have hbP : 1 + ((q : ℝ) - 1)*ρ^p = b*t^(2*p) := by
    rw [htP, mul_div_cancel₀ _ hbpos.ne']
  let R : ℝ := (1 + ((q : ℝ)-1)*ρ)/(q : ℝ)
  have hR₀ : 0 ≤ R := by
    apply div_nonneg _ (by linarith)
    linarith [mul_nonneg (sub_nonneg.mpr hQ.le) hρ₀]
  have hR₁ : R < 1 := by
    apply (div_lt_one (by linarith : 0 < (q:ℝ))).2
    linarith [mul_lt_mul_of_pos_left hρ₁ (sub_pos.mpr hQ)]
  let u := Real.sqrt R
  have hu₀ : 0 ≤ u := Real.sqrt_nonneg _
  have hu₁ : u < 1 := (Real.sqrt_lt hR₀ zero_le_one).2 (by simpa using hR₁)
  have hu2 : u^2 = R := Real.sq_sqrt hR₀
  have hE : Tendsto (fun m : ℕ => 6*u^m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hu₀ hu₁).const_mul (6:ℝ)
  have hdecay (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v < 1) :
      Tendsto (fun m : ℕ => (a:ℝ)*(m:ℝ)*v^m) atTop (𝓝 0) := by
    simpa [mul_assoc] using (tendsto_self_mul_const_pow_of_lt_one hv₀ hv₁).const_mul (a:ℝ)
  have hF : Tendsto (fun m : ℕ => ((a*m : ℕ) : ℝ)*(2*t^m + 6*u^m)) atTop (𝓝 0) := by
    have h := ((hdecay t ht₀ ht₁).const_mul (2:ℝ)).add ((hdecay u hu₀ hu₁).const_mul (6:ℝ))
    convert h using 1
    · ext m
      push_cast
      ring
    · simp
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.1 (hE.eventually (gt_mem_nhds hδ))
  obtain ⟨m₂, hm₂⟩ := eventually_atTop.1 (hF.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)))
  refine ⟨D, p, b, t, u, hDpos, hp, hb, hbD, ht₀, ht₁, hu₀, hu₁, hu2, hbP,
    max (max m₁ m₂) 1, by omega, ?_⟩
  intro m hm
  have hm₁' : m₁ ≤ m := by omega
  have hm₂' : m₂ ≤ m := by omega
  refine ⟨?_, (hm₁ _ hm₁').le, (hm₂ _ hm₂').le⟩
  have hfloor : ((m/D : ℕ) : ℝ)*(D:ℝ) ≤ (m:ℝ) := by exact_mod_cast Nat.div_mul_le_self m D
  have h_a : (1:ℝ) ≤ a := by exact_mod_cast ha
  push_cast
  calc
    ((m/D : ℕ) : ℝ) ≤ ((m/D : ℕ) : ℝ)*(δ*(D:ℝ)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hDδ (Nat.cast_nonneg _)
    _ = δ*(((m/D : ℕ) : ℝ)*(D:ℝ)) := by ring
    _ ≤ δ*(m:ℝ) := mul_le_mul_of_nonneg_left hfloor hδ.le
    _ ≤ δ*((a:ℝ)*(m:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h_a (Nat.cast_nonneg m)

lemma card_large_bound {D m n : ℕ} {b : ℝ}
    (hD : 0 < D) (hb : 1 < b) (hbD : b^D = 2) (hn : 2^(m/D) < n) :
    b^m ≤ 2*(n:ℝ) := by
  have hmd : m ≤ (m/D + 1) * D := by simpa [Nat.mul_comm] using (Nat.lt_mul_div_succ m hD).le
  have hn' : (2:ℝ)^(m/D) ≤ n := by exact_mod_cast hn.le
  calc
    _ ≤ b^((m/D+1)*D) := pow_le_pow_right₀ hb.le hmd
    _ = 2^((m/D : ℕ) + 1) := by rw [Nat.mul_comm, pow_mul, hbD]
    _ ≤ _ := by rw [pow_succ, mul_comm]; gcongr

-- A higher moment of the correlation kernel controls large classes.
lemma class_mean_large {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (s : X → Y → ℝ) (C : Finset X) (hC : C.Nonempty) (m p : ℕ) (hp : 0 < p)
    {b t : ℝ} (ht : 0 ≤ t) (hc : b^m ≤ 2*(C.card : ℝ))
    (hrow : ∀ x, (∑ u, |corr s x u|^p) ≤ (b*t^(2*p))^m) :
    meanAbs s C ≤ 2*t^m := by
  have hp' : p ≠ 0 := hp.ne'
  have hc' : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  have h2p : (2:ℝ) ≤ 2^p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hp
  have hrow' (x : X) : (𝔼 u ∈ C, |corr s x u|) ≤ 2*(t^m)^2 := by
    have h := expect_pow_le C hC (fun u => |corr s x u|) (fun _ _ => abs_nonneg _) p
    have hb : (𝔼 u ∈ C, |corr s x u|^p) ≤ (2*(t^m)^2)^p := by
      rw [expect_eq_sum_div_card]
      calc
        _ ≤ (∑ u, |corr s x u|^p)/(C.card : ℝ) :=
          div_le_div_of_nonneg_right
            (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)) hc'.le
        _ ≤ (b*t^(2*p))^m/(C.card : ℝ) := div_le_div_of_nonneg_right (hrow x) hc'.le
        _ = (b^m/(C.card : ℝ))*((t^m)^2)^p := by
          rw [mul_pow, ← div_mul_eq_mul_div]
          congr 1
          simp only [← pow_mul]
          congr 1
          ring
        _ ≤ 2*((t^m)^2)^p := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc').2 hc) (by positivity)
        _ ≤ (2*(t^m)^2)^p := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right h2p (by positivity)
    by_contra! hn
    exact (not_lt_of_ge (h.trans hb)) (pow_lt_pow_left₀ hn (by positivity) hp')
  have hsq := (meanAbs_sq s C).trans (expect_le hC fun x _ => hrow' x)
  by_contra! hn
  have hh := pow_lt_pow_left₀ hn (show 0 ≤ 2*t^m by positivity) (by decide : 2 ≠ 0)
  nlinarith [sq_nonneg (t^m)]

lemma weighted_code_cost {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (L h : ℕ) (hsz : Fintype.card X = 2^L)
    (b : X → Y → Bool) (w : X → Y → ℝ) (e : ℝ)
    (hw₀ : ∀ x y, 0 ≤ w x y)
    (hw₁ : ∀ x, (𝔼 y, w x y) = 1)
    (hwBal : ∀ y, (𝔼 x, w x y * sign (b x y)) = 0)
    (hwErr : ∀ x, (𝔼 y, |w x y - 1|) ≤ e)
    (hsmall : ∀ C : Finset X, 1 < C.card → C.card ≤ 2^h →
      (L : ℝ) * (meanAbs (fun x y => sign (b x y)) C + e) ≤ (L : ℝ) - h)
    (hlarge : ∀ C : Finset X, 2^h < C.card →
      (L : ℝ) * (meanAbs (fun x y => sign (b x y)) C + e) ≤ 1/2)
    (send : X → List Bool) (read : List Bool → Y → Bool)
    (hp : ∀ x x' tail, send x ++ tail = send x' → tail = []) :
    (L : ℝ) * (∑ x, 𝔼 y, w x y * (sign (b x y) * sign (read (send x) y))) ≤
      ∑ x, ((send x).length : ℝ) := by
  classical
  let g := fun x => 𝔼 y, w x y * (sign (b x y) * sign (read (send x) y))
  have hCscore (C : Finset X) (hC : C.Nonempty)
      (hconst : ∀ x ∈ C, ∀ y ∈ C, send x = send y) {v : ℝ}
      (hv : (L : ℝ)*(meanAbs (fun x y => sign (b x y)) C + e) ≤ v) :
      (L : ℝ) * (∑ x ∈ C, g x) ≤ v * C.card := by
    obtain ⟨x₀,hx₀⟩ := hC
    have h : (𝔼 x ∈ C, g x) =
        (𝔼 x ∈ C, 𝔼 y, w x y * (sign (b x y) * sign (read (send x₀) y))) := by
      apply expect_congr rfl
      intro x hx
      simp [g, hconst x hx x₀ hx₀]
    have hb := class_mean_bound b w hwErr C ⟨x₀,hx₀⟩ (read (send x₀))
    rw [← h] at hb
    have htot := (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg L)).trans hv
    have hc₀ : 0 < (C.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr ⟨x₀,hx₀⟩
    rw [expect_eq_sum_div_card, ← mul_div_assoc, div_le_iff₀ hc₀] at htot
    exact htot
  apply code_cost L h hsz send g hp
  · intro x
    refine (expect_le_expect fun y _ => ?_).trans_eq (hw₁ x)
    have hb : sign (b x y) * sign (read (send x) y) ≤ 1 := by
      rw [sign_eq]
      split <;> norm_num
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (hw₀ x y)
  · intro hnil
    have he : (𝔼 x, g x) = 0 := by
      simp only [g, hnil, ← mul_assoc]
      rw [expect_comm]
      apply expect_eq_zero
      intro y _
      rw [← expect_mul, hwBal, zero_mul]
    rw [Fintype.expect_eq_sum_div_card] at he
    have hn : (Fintype.card X : ℝ) ≠ 0 := by rw [hsz]; positivity
    exact (div_eq_zero_iff.mp he).resolve_right hn
  · intro C hconst hcard hsmallC
    exact hCscore C (card_pos.1 (by omega)) hconst (hsmall C hcard hsmallC)
  · intro C hconst hcard
    simpa [div_eq_mul_inv, mul_comm] using
      hCscore C (card_pos.1 ((Nat.zero_le _).trans_lt hcard)) hconst (hlarge C hcard)

lemma product_setup (a k : ℕ) (ha : 0 < a) (hk : 0 < k) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      let A := Fin (2^a)
      let B := Fin k
      let X := Fin m → A
      let Y := Fin m → B
      ∀ f : Fin m → A → B → Bool,
      (∀ i u v, u ≠ v →
        (∃ j, f i u j = f i v j) ∧ (∃ j, f i u j ≠ f i v j)) →
      ∀ (left : X → Bool) (right : Y → Bool),
        let truth := fun (x : X) (y : Y) =>
          xor (xor (left x) (right y))
            ((univ.filter (fun i => f i (x i) (y i))).card % 2 == 1)
        ∃ w : X → Y → ℝ,
          (∀ x y, 0 ≤ w x y) ∧ (∀ x, (𝔼 y, w x y) = 1) ∧
          ∀ (send : X → List Bool) (read : List Bool → Y → Bool),
            (∀ x x' tail, send x ++ tail = send x' → tail = []) →
            ((a*m : ℕ) : ℝ) *
                (∑ x, 𝔼 y, w x y * (sign (truth x y) * sign (read (send x) y))) ≤
              ∑ x, ((send x).length : ℝ) := by
  classical
  let q : ℕ := 2^a
  have hq : 1 < q := one_lt_pow₀ (by decide : 1 < (2:ℕ)) ha.ne'
  let ρ : ℝ := 1 - 1/(k:ℝ)
  have hk₀ : 0 < (k:ℝ) := by exact_mod_cast hk
  have hk₁ : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hρ₀ : 0 ≤ ρ := sub_nonneg.mpr ((div_le_one hk₀).2 hk₁)
  have hρ₁ : ρ < 1 := by dsimp [ρ]; linarith [div_pos (by norm_num : (0:ℝ) < 1) hk₀]
  obtain ⟨D, p, b, t, u, hD, hp, hb, hbD, ht₀, _, hu₀, hu₁, hu2, hBp, m₀, hm₀, hmb⟩ :=
    choose_scales a q ha hq hρ₀ hρ₁
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm A B X Y f hf left right truth
  let L := a*m
  let h := m/D
  have hpos : 0 < m := hm₀.trans_le hm
  have hszQ : Fintype.card X = q^m := by simp [X, A, q]
  have hsz : Fintype.card X = 2^L := by simp [hszQ, L, q, pow_mul]
  have hN : 1 < Fintype.card X := by
    rw [hszQ]
    exact one_lt_pow₀ hq hpos.ne'
  have : Nonempty Y := ⟨fun _ => ⟨0,hk⟩⟩
  let s := fun x y => sign (truth x y)
  have hK (x v : X) : |corr s x v| ≤ kernel ρ x v := product_corr hk f hf left right x v
  have hOff (x v : X) (hv : x ≠ v) : |corr s x v| ≤ ρ :=
    (hK x v).trans (kernel_off hρ₀ hρ₁.le hv)
  have hMoment (x : X) (j : ℕ) :
      (∑ v, |corr s x v|^j) ≤ (1 + ((q : ℝ)-1)*ρ^j)^m := by
    calc
      _ ≤ ∑ v, (kernel ρ x v)^j :=
        sum_le_sum fun v _ => pow_le_pow_left₀ (abs_nonneg _) (hK x v) _
      _ = _ := by simp_rw [kernel_pow, kernel_sum]; rfl
  have hRow (x : X) : (𝔼 v, |corr s x v|) ≤ (u^m)^2 := by
    rw [Fintype.expect_eq_sum_div_card, hszQ, Nat.cast_pow]
    have hh : (∑ v, |corr s x v|) ≤ (1+((q:ℝ)-1)*ρ)^m := by simpa using hMoment x 1
    calc
      _ ≤ (1+((q:ℝ)-1)*ρ)^m/(q:ℝ)^m := div_le_div_of_nonneg_right hh (by positivity)
      _ = _ := by rw [← div_pow, ← hu2, ← pow_mul, ← pow_mul, Nat.mul_comm]
  obtain ⟨w, hw₀, hw₁, hwBal, hwErr⟩ := make_weights truth hN hρ₁
    (pow_nonneg hu₀ m) (pow_le_one₀ hu₀ hu₁.le) hOff hRow
  obtain ⟨hh, he, hz⟩ := hmb m hm
  refine ⟨w, hw₀, hw₁, ?_⟩
  intro send read hpf
  apply weighted_code_cost L h hsz truth w (6*u^m) hw₀ hw₁ hwBal hwErr _ _ send read hpf
  · intro C hC _
    have hSmall := class_mean_small truth hρ₀ hρ₁.le hOff C hC
    calc
      _ ≤ (L : ℝ)*(1-(1-ρ)/8) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        linarith
      _ ≤ _ := by
        change (h : ℝ) ≤ ((1-ρ)/8)*(L : ℝ) at hh
        linarith
  · intro C hC
    have hCn : C.Nonempty := card_pos.1 ((Nat.zero_le _).trans_lt hC)
    have hCb : b^m ≤ 2*(C.card : ℝ) := card_large_bound hD hb hbD hC
    have hLarge := class_mean_large s C hCn m p hp ht₀ hCb (fun x => hBp ▸ hMoment x p)
    exact (mul_le_mul_of_nonneg_left (add_le_add hLarge le_rfl) (Nat.cast_nonneg _)).trans hz

lemma upperCost (a m : Nat) {Y : Type} (truth : (Fin m → Fin (2^a)) → Y → Bool)
    (β : ℚ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    let X := Fin m → Fin (2^a)
    ∃ (r : Nat) (send : Fin r → X → List Bool)
      (read : Fin r → List Bool → Y → Bool),
      0 < r ∧
      (∀ z x x' tail, send z x ++ tail = send z x' → tail = []) ∧
      (∀ x y, (1+β)*(r : ℚ) ≤ 2*(((Finset.univ : Finset (Fin r)).filter
        (fun z => read z (send z x) y = truth x y)).card : ℚ)) ∧
      β*(a*m : Nat) = ((∑ z : Fin r, ∑ x : X, (send z x).length : Nat) : ℚ) /
        ((r : ℚ)*((2^a)^m : Nat)) := by
  classical
  let X := Fin m → Fin (2^a)
  change ∃ (r : Nat) (send : Fin r → X → List Bool)
      (read : Fin r → List Bool → Y → Bool), _
  have hX : Fintype.card X = (2^a)^m := by simp [X]
  let encEquiv : X ≃ (Fin (a*m) → Bool) :=
    Fintype.equivOfCardEq (by rw [hX]; simp [pow_mul])
  let enc : X → List Bool := fun x => List.ofFn (encEquiv x)
  have enc_inj : Function.Injective enc := List.ofFn_injective.comp encEquiv.injective
  have enc_len (x : X) : (enc x).length = a*m := List.length_ofFn
  let dec : List Bool → Y → Bool :=
    fun w y => if h : ∃ x, enc x = w then truth (Classical.choose h) y else false
  have dec_ok (x : X) (y : Y) : dec (enc x) y = truth x y := by
    change (if h : ∃ x', enc x' = enc x then truth (Classical.choose h) y else false) = _
    have h : ∃ x', enc x' = enc x := ⟨x, rfl⟩
    rw [dite_eq_left h, enc_inj (Classical.choose_spec h)]
  let n := β.num.toNat
  let d := β.den
  have hd : 0 < d := Rat.den_pos _
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hnQ : (n : ℚ) = (β.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hβ0)
  have hfrac : (n : ℚ) / d = β := by rw [hnQ, Rat.num_div_den]
  have hβd : β * (d : ℚ) = n := ((div_eq_iff hdQ.ne').mp hfrac).symm
  have hnd : n ≤ d := by
    apply (Nat.cast_le (α := ℚ)).mp
    simpa using (div_le_iff₀ hdQ).mp (hfrac.trans_le hβ1)
  let S := Fin (2*n) ⊕ (Fin (d-n) × Bool)
  let e : Fin (2*d) ≃ S :=
    Fintype.equivOfCardEq (by
      simp only [S, Fintype.card_fin, Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
      omega)
  let msg : S → X → List Bool := fun z x => z.elim (fun _ => enc x) (fun _ => [])
  let out : S → List Bool → Y → Bool := fun z w y => z.elim (fun _ => dec w y) Prod.snd
  let send : Fin (2*d) → X → List Bool := fun z => msg (e z)
  let read : Fin (2*d) → List Bool → Y → Bool := fun z => out (e z)
  refine ⟨2*d, send, read, by omega, ?_, ?_, ?_⟩
  · intro z x x' tail h
    apply List.length_eq_zero_iff.mp
    have hh := congrArg List.length h
    have hs (w : S) : (msg w x).length = (msg w x').length := by
      cases w <;> simp [msg, enc_len]
    rw [List.length_append] at hh
    change (msg (e z) x).length + tail.length = (msg (e z) x').length at hh
    rw [← hs (e z)] at hh
    omega
  · intro x y
    let p : S → Prop := fun z => out z (msg z x) y = truth x y
    have htwo (b : Bool) :
        ((if b = true then 1 else 0) + if b = false then 1 else 0) = (1 : Nat) := by
      cases b <;> decide
    have hcount : (∑ z : S, if p z then 1 else 0) = 2*n + (d-n) := by
      rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp [p, out, msg, dec_ok, htwo]
    have hfilter : (Finset.univ.filter (fun z : Fin (2*d) => p (e z))).card =
        2*n + (d-n) := by
      calc
        _ = ∑ z : Fin (2*d), if p (e z) then 1 else 0 := (Finset.sum_boole _ _).symm
        _ = ∑ z : S, if p z then 1 else 0 := e.sum_comp (fun z => (if p z then 1 else 0 : Nat))
        _ = _ := hcount
    change (1+β)*((2*d : Nat) : ℚ) ≤
      2 * ((Finset.univ.filter (fun z : Fin (2*d) => p (e z))).card : ℚ)
    rw [hfilter]
    push_cast [Nat.cast_sub hnd]
    linarith only [hβd]
  · have hsum : (∑ z : Fin (2*d), ∑ x : X, (send z x).length) =
        (2*n) * (((2^a)^m) * (a*m)) := by
      calc
        _ = ∑ z : S, ∑ x : X, (msg z x).length := e.sum_comp _
        _ = _ := by rw [Fintype.sum_sum_type]; simp [msg, enc_len, hX]
    rw [hsum, ← hfrac]
    push_cast only [Nat.cast_mul, Nat.cast_ofNat]
    have hN : (0 : ℚ) < (((2^a)^m : Nat) : ℚ) := by positivity
    field_simp [hdQ.ne', hN.ne']

private lemma signedSeedCount {r : Nat} (target : Bool) (answer : Fin r → Bool)
    (β : ℚ) (h : (1+β)*(r : ℚ) ≤ 2*(((Finset.univ : Finset (Fin r)).filter
      (fun z => answer z = target)).card : ℚ)) :
    (β : ℝ) * (r : ℝ) ≤ ∑ z : Fin r,
      (if target then -1 else 1 : ℝ) * (if answer z then -1 else 1 : ℝ) := by
  classical
  have hR : (1+(β : ℝ))*(r : ℝ) ≤ 2*(((Finset.univ : Finset (Fin r)).filter
      (fun z => answer z = target)).card : ℝ) := by
    exact_mod_cast h
  have hBit (b : Bool) :
      (if target then -1 else 1 : ℝ) * (if b then -1 else 1 : ℝ) =
      2 * (if b = target then 1 else 0 : ℝ) - 1 := by
    cases target <;> cases b <;> norm_num
  simp_rw [hBit]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  linarith

lemma lowerCostOfSeedBound {X Y : Type} [Fintype X] [Fintype Y]
    {r L : Nat} (hr : 0 < r) (hX : 0 < Fintype.card X)
    (truth : X → Y → Bool) (w : X → Y → ℝ)
    (send : Fin r → X → List Bool) (read : Fin r → List Bool → Y → Bool)
    (β : ℚ) (hw0 : ∀ x y, 0 ≤ w x y) (hw1 : ∀ x, (𝔼 y, w x y) = 1)
    (hs : ∀ x y, (1+β)*(r : ℚ) ≤ 2*(((Finset.univ : Finset (Fin r)).filter
      (fun z => read z (send z x) y = truth x y)).card : ℚ))
    (hseed : ∀ z, (L : ℝ) * (∑ x : X, 𝔼 y : Y, w x y *
        ((if truth x y then -1 else 1 : ℝ) * (if read z (send z x) y then -1 else 1 : ℝ))) ≤
      ∑ x : X, ((send z x).length : ℝ)) :
    β * (L : ℚ) ≤ ((∑ z : Fin r, ∑ x : X, (send z x).length : Nat) : ℚ) /
      ((r : ℚ) * (Fintype.card X : ℚ)) := by
  classical
  let score (z : Fin r) (x : X) (y : Y) : ℝ :=
    (if truth x y then -1 else 1) * (if read z (send z x) y then -1 else 1)
  have hpoint (x : X) (y : Y) : (β : ℝ) * (r : ℝ) ≤ ∑ z, score z x y :=
    signedSeedCount (truth x y) (fun z => read z (send z x) y) β (hs x y)
  have hrow (x : X) : (β : ℝ) * (r : ℝ) ≤ 𝔼 y, w x y * ∑ z, score z x y := calc
    _ = 𝔼 y, w x y * ((β : ℝ) * (r : ℝ)) := by
      rw [← Finset.expect_mul, hw1, one_mul]
    _ ≤ _ := Finset.expect_le_expect fun y _ => mul_le_mul_of_nonneg_left (hpoint x y) (hw0 x y)
  have hswap : (∑ z : Fin r, (L : ℝ) * ∑ x : X, 𝔼 y, w x y * score z x y) =
      (L : ℝ) * ∑ x : X, 𝔼 y, w x y * ∑ z, score z x y := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum, Finset.expect_sum_comm]
  have hR : ((β : ℝ) * (L : ℝ)) * ((r : ℝ) * (Fintype.card X : ℝ)) ≤
      ∑ z : Fin r, ∑ x : X, ((send z x).length : ℝ) := calc
    _ = (L : ℝ) * (∑ _ : X, (β : ℝ) * (r : ℝ)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ (L : ℝ) * ∑ x : X, 𝔼 y, w x y * ∑ z, score z x y :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hrow x) (Nat.cast_nonneg _)
    _ = ∑ z : Fin r, (L : ℝ) * ∑ x : X, 𝔼 y, w x y * score z x y := hswap.symm
    _ ≤ _ := Finset.sum_le_sum fun z _ => hseed z
  have hden : (0 : ℚ) < (r : ℚ) * (Fintype.card X : ℚ) :=
    mul_pos (Nat.cast_pos.mpr hr) (Nat.cast_pos.mpr hX)
  apply (le_div_iff₀ hden).mpr
  have hcast : (∑ z : Fin r, ∑ x : X, ((send z x).length : ℝ)) =
      ((∑ z : Fin r, ∑ x : X, (send z x).length : Nat) : ℝ) := by
    push_cast
    rfl
  rw [hcast] at hR
  exact_mod_cast hR

end PEqualNP.Outside.L_lib_938

open PEqualNP.Outside.L_lib_938

theorem PEqualNP.Outside.L_lib_938 : ∀ (a k : Nat), 0 < a → 0 < k →
  ∃ m₀ : Nat, 0 < m₀ ∧ ∀ m : Nat, m₀ ≤ m →
    let A := Fin (2^a)
    let B := Fin k
    let X := Fin m → A
    let Y := Fin m → B
    ∀ f : Fin m → A → B → Bool,
    (∀ i u v, u ≠ v →
      (∃ j, f i u j = f i v j) ∧ (∃ j, f i u j ≠ f i v j)) →
    ∀ (left : X → Bool) (right : Y → Bool),
      let truth := fun (x : X) (y : Y) =>
        xor (xor (left x) (right y))
          (((Finset.univ : Finset (Fin m)).filter (fun i => f i (x i) (y i))).card % 2 == 1)
      ∀ β : ℚ, 0 ≤ β → β ≤ 1 →
        let costs : Set ℚ := {c | ∃ (r : Nat) (send : Fin r → X → List Bool)
          (read : Fin r → List Bool → Y → Bool),
          0 < r ∧
          (∀ z x x' tail, send z x ++ tail = send z x' → tail = []) ∧
          (∀ x y, (1+β)*(r : ℚ) ≤ 2*(((Finset.univ : Finset (Fin r)).filter
            (fun z => read z (send z x) y = truth x y)).card : ℚ)) ∧
          c = ((∑ z : Fin r, ∑ x : X, (send z x).length : Nat) : ℚ) /
            ((r : ℚ)*((2^a)^m : Nat))}
        IsLeast costs (β*(a*m : Nat)) := by
  classical
  intro a k ha hk
  obtain ⟨m₀, hm₀, hdet⟩ := product_setup a k ha hk
  refine ⟨m₀, hm₀, ?_⟩
  intro m hm A B X Y f hf left right truth β hβ₀ hβ₁ costs
  refine ⟨upperCost a m truth β hβ₀ hβ₁, ?_⟩
  intro c hc
  rcases hc with ⟨r, send, read, hr, hpf, hsucc, rfl⟩
  obtain ⟨w, hw₀, hw₁, hbound⟩ := hdet m hm f hf left right
  have hX : Fintype.card X = (2^a)^m := by simp [X, A]
  have hX₀ : 0 < Fintype.card X := by rw [hX]; positivity
  simpa only [hX] using
    lowerCostOfSeedBound (L := a*m) hr hX₀ truth w send read β hw₀ hw₁ hsucc
      (fun z => hbound (send z) (read z) (hpf z))
