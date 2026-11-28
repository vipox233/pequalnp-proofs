import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_918

open scoped BigOperators

abbrev F2 := ZMod 2

-- Basic ZMod 2 facts (avoid decide under Classical)
lemma zmod2_eq_zero_or_one (x : F2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma zmod2_add_self (x : F2) : x + x = 0 := by
  fin_cases x <;> rfl

lemma zmod2_neg_eq (x : F2) : -x = x := by
  fin_cases x <;> rfl

lemma zmod2_sub_eq_add (x y : F2) : x - y = x + y := by
  rw [sub_eq_add_neg, zmod2_neg_eq]

lemma zmod2_mul_self (x : F2) : x * x = x := by
  fin_cases x <;> rfl

lemma module_F2_add_self {X : Type*} [AddCommGroup X] [Module F2 X] (x : X) :
    x + x = 0 := by
  calc x + x = (1 : F2) • x + (1 : F2) • x := by simp
    _ = ((1 : F2) + 1) • x := (add_smul (1 : F2) (1 : F2) x).symm
    _ = (0 : F2) • x := by rw [zmod2_add_self]
    _ = 0 := zero_smul F2 x

lemma finrank_map_of_inj {V W : Type*} [AddCommGroup V] [Module F2 V]
    [AddCommGroup W] [Module F2 W]
    {f : V →ₗ[F2] W} (hf : Function.Injective f) (S : Submodule F2 V) :
    Module.finrank F2 (Submodule.map f S) = Module.finrank F2 S := by
  have hrange : LinearMap.range (f.comp S.subtype) = Submodule.map f S := by
    ext x
    simp [LinearMap.mem_range, Submodule.mem_map]
  rw [← hrange]
  exact (LinearEquiv.ofInjective (f.comp S.subtype) (hf.comp S.injective_subtype)).finrank_eq.symm

lemma sum_F2 (g : F2 → ℤ) : (∑ x : F2, g x) = g 0 + g 1 := by
  refine Fintype.sum_eq_add 0 1 (by decide) (fun x hx => ?_)
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · exact False.elim (hx.1 rfl)
  · exact False.elim (hx.2 rfl)

lemma card_F2 : Fintype.card F2 = 2 := by
  simp [F2]

lemma card_fin_F2 (n : ℕ) : Fintype.card (Fin n → F2) = 2 ^ n := by
  simp [card_F2]

lemma card_submodule_F2 {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V]
    (W : Submodule F2 V) :
    Nat.card W = 2 ^ Module.finrank F2 W := by
  letI : Finite W := Subtype.finite
  have h := Module.natCard_eq_pow_finrank (K := F2) (V := W)
  have h2 : Nat.card F2 = 2 := by
    rw [Nat.card_eq_fintype_card, card_F2]
  rw [h2] at h
  exact h

-- Character chi : F2 → ℤ
noncomputable def chi (x : F2) : ℤ :=
  if x = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := by
  simp [chi]

lemma chi_one : chi 1 = -1 := by
  simp [chi]

lemma chi_add (x y : F2) : chi (x + y) = chi x * chi y := by
  fin_cases x <;> fin_cases y <;> rfl

lemma chi_eq_ite (x y : F2) : (if x = y then (1 : ℤ) else -1) = chi (x + y) := by
  fin_cases x <;> fin_cases y <;> rfl

lemma chi_sq (x : F2) : chi x * chi x = 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> simp [chi]

lemma chi_sum_finset {ι : Type*} (s : Finset ι) (f : ι → F2) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma sum_chi_linearMap {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    (φ : V →ₗ[F2] F2) :
    (∑ x : V, chi (φ x)) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  by_cases hφ : φ = 0
  · simp [hφ, chi_zero]
  · simp only [hφ, ↓reduceIte]
    have hex : ∃ v : V, φ v = 1 := by
      by_contra hall
      push_neg at hall
      apply hφ
      apply LinearMap.ext
      intro v
      rcases zmod2_eq_zero_or_one (φ v) with h0 | h1
      · exact h0
      · exact False.elim (hall v h1)
    rcases hex with ⟨v, hv⟩
    have hshift : (∑ x : V, chi (φ (x + v))) = ∑ x : V, chi (φ x) :=
      Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)
    have hneg : (∑ x : V, chi (φ (x + v))) = -(∑ x : V, chi (φ x)) := by
      calc ∑ x : V, chi (φ (x + v))
          = ∑ x : V, chi (φ x + φ v) := by simp [map_add]
        _ = ∑ x : V, chi (φ x) * chi 1 := by simp [chi_add, hv]
        _ = ∑ x : V, -chi (φ x) := by simp [chi_one]
        _ = -(∑ x : V, chi (φ x)) := Finset.sum_neg_distrib (fun x => chi (φ x))
    linarith

open Classical in
lemma sum_chi_linearMap_sub {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    (W : Submodule F2 V) (φ : V →ₗ[F2] F2) :
    letI : Fintype W := Fintype.ofFinite W
    (∑ x : W, chi (φ x.1)) =
      if (∀ x ∈ W, φ x = 0) then (Fintype.card W : ℤ) else 0 := by
  letI : Fintype W := Fintype.ofFinite W
  have h := sum_chi_linearMap (φ.comp W.subtype)
  have hiff : (φ.comp W.subtype = 0) ↔ (∀ x ∈ W, φ x = 0) := by
    constructor
    · intro h0 x hx
      have := LinearMap.congr_fun h0 ⟨x, hx⟩
      simpa using this
    · intro h0
      apply LinearMap.ext
      intro x
      exact h0 x.1 x.2
  by_cases h0 : ∀ x ∈ W, φ x = 0
  · rw [if_pos h0]
    rw [if_pos (hiff.mpr h0)] at h
    exact h
  · rw [if_neg h0]
    rw [if_neg (fun h1 => h0 (hiff.mp h1))] at h
    exact h

-- Quadratic forms on an abstract F2-vector space: characterized by bilinear polar form
def IsQuad {V : Type*} [AddCommGroup V] [Module F2 V] (f : V → F2) : Prop :=
  ∃ B : V →ₗ[F2] V →ₗ[F2] F2,
    (∀ x : V, B x x = 0) ∧
    (∀ x y : V, f (x + y) + f x + f y + f 0 = B x y)

lemma polar_symm {V : Type*} [AddCommGroup V] [Module F2 V] {f : V → F2}
    {B : V →ₗ[F2] V →ₗ[F2] F2}
    (hB : ∀ x y : V, f (x + y) + f x + f y + f 0 = B x y)
    (x y : V) : B x y = B y x := by
  rw [← hB x y, ← hB y x, add_comm x y]
  ring

lemma sum_chi_quad_le_half_or_eq {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    {f : V → F2} (hf : IsQuad f) :
    (∀ x : V, f x = f 0) ∨
    2 * (∑ x : V, chi (f x)).natAbs ≤ Fintype.card V := by
  classical
  rcases hf with ⟨B, hBalt, hB⟩
  set S : ℤ := ∑ x : V, chi (f x)
  set R : Submodule F2 V := LinearMap.ker B
  letI : Fintype R := Fintype.ofFinite R
  have hSsq : S * S = ∑ z : V, ∑ y : V, chi (f (y + z) + f y) := by
    calc S * S
        = (∑ x : V, chi (f x)) * (∑ y : V, chi (f y)) := rfl
      _ = ∑ y : V, ∑ x : V, chi (f x) * chi (f y) := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]
      _ = ∑ y : V, ∑ z : V, chi (f (y + z)) * chi (f y) := by
          refine Finset.sum_congr rfl (fun y _ => ?_)
          exact (Fintype.sum_equiv (Equiv.addLeft y) _ _ (fun _ => rfl)).symm
      _ = ∑ z : V, ∑ y : V, chi (f (y + z) + f y) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun z _ => Finset.sum_congr rfl (fun y _ => ?_))
          rw [chi_add]
  have hinner : ∀ z : V,
      (∑ y : V, chi (f (y + z) + f y)) =
        if z ∈ R then (Fintype.card V : ℤ) * chi (f z + f 0) else 0 := by
    intro z
    have hrewrite : ∀ y : V, f (y + z) + f y = (f z + f 0) + B z y := by
      intro y
      have h1 := hB z y
      rw [add_comm z y] at h1
      have h2 := congrArg (· + f z + f 0) h1
      have h3 : f (y + z) + f z + f y + f 0 + f z + f 0 = f (y + z) + f y := by
        calc f (y + z) + f z + f y + f 0 + f z + f 0
            = f (y + z) + f y + (f z + f z) + (f 0 + f 0) := by ring
          _ = f (y + z) + f y := by rw [zmod2_add_self, zmod2_add_self]; ring
      rw [h3] at h2
      rw [h2]; ring
    calc (∑ y : V, chi (f (y + z) + f y))
        = ∑ y : V, chi ((f z + f 0) + B z y) := by simp_rw [hrewrite]
      _ = chi (f z + f 0) * ∑ y : V, chi (B z y) := by
          simp_rw [chi_add]; rw [← Finset.mul_sum]
      _ = chi (f z + f 0) * (if B z = 0 then (Fintype.card V : ℤ) else 0) := by
          rw [sum_chi_linearMap (B z)]
      _ = if z ∈ R then (Fintype.card V : ℤ) * chi (f z + f 0) else 0 := by
          by_cases hz : z ∈ R
          · have hz' : B z = 0 := hz
            rw [if_pos hz', if_pos hz]; ring
          · have hz' : B z ≠ 0 := hz
            rw [if_neg hz', if_neg hz]; ring
  have hSsq2 : S * S = (Fintype.card V : ℤ) * ∑ z : R, chi (f z.1 + f 0) := by
    rw [hSsq]
    simp_rw [hinner]
    rw [← Finset.sum_filter, Finset.mul_sum]
    have hbij : (∑ z ∈ Finset.univ.filter (fun z : V => z ∈ R),
        (Fintype.card V : ℤ) * chi (f z + f 0)) =
        ∑ z : R, (Fintype.card V : ℤ) * chi (f z.1 + f 0) := by
      refine Finset.sum_bij (fun z hz => (⟨z, (Finset.mem_filter.mp hz).2⟩ : R))
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ hab => congrArg Subtype.val hab)
        (fun r _ => ⟨r.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r.2⟩, rfl⟩)
        (fun _ _ => rfl)
    exact hbij
  -- On R, g(z) = f(z) + f(0) is a linear map R →ₗ[F2] F2
  let gR : R →ₗ[F2] F2 :=
    { toFun := fun z => f z.1 + f 0
      map_add' := fun x y => by
        have hx : B x.1 = 0 := x.2
        have hxy := hB x.1 y.1
        rw [hx, LinearMap.zero_apply] at hxy
        have h1 : f (x.1 + y.1) + f x.1 + f y.1 + f 0 = 0 := hxy
        have h2 := congrArg (· + f x.1 + f y.1) h1
        have h3 : f (x.1 + y.1) + f x.1 + f y.1 + f 0 + f x.1 + f y.1 =
            f (x.1 + y.1) + f 0 := by
          calc f (x.1 + y.1) + f x.1 + f y.1 + f 0 + f x.1 + f y.1
              = f (x.1 + y.1) + f 0 + (f x.1 + f x.1) + (f y.1 + f y.1) := by ring
            _ = f (x.1 + y.1) + f 0 := by rw [zmod2_add_self, zmod2_add_self]; ring
        rw [h3, zero_add] at h2
        rw [Submodule.coe_add, h2]
        calc f x.1 + f y.1 = f x.1 + f y.1 + (f 0 + f 0) := by rw [zmod2_add_self, add_zero]
          _ = (f x.1 + f 0) + (f y.1 + f 0) := by ring
      map_smul' := fun c x => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp [zmod2_add_self]
        · simp }
  have hgR := sum_chi_linearMap gR
  by_cases htop : R = ⊤
  · by_cases hg0 : gR = 0
    · left
      intro x
      have hxR : x ∈ R := by rw [htop]; trivial
      have h0 : gR ⟨x, hxR⟩ = 0 := by rw [hg0]; rfl
      change f x + f 0 = 0 at h0
      have h2 := congrArg (· + f 0) h0
      rw [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
      exact h2
    · right
      rw [if_neg hg0] at hgR
      have hS0 : S * S = 0 := by
        rw [hSsq2]
        change (Fintype.card V : ℤ) * (∑ z : R, chi (gR z)) = 0
        rw [hgR, mul_zero]
      have hSz : S = 0 := mul_self_eq_zero.mp hS0
      simp [hSz]
  · right
    -- R ≠ ⊤; show finrank R + 2 ≤ finrank V
    have hlt : Module.finrank F2 R < Module.finrank F2 V :=
      Submodule.finrank_lt htop
    have hne1 : Module.finrank F2 R + 1 ≠ Module.finrank F2 V := by
      intro heq
      -- Pick v ∉ R; then R ⊔ span{v} = ⊤, so B v = 0, contradicting v ∉ R
      have hex : ∃ v : V, v ∉ R := by
        by_contra hall
        push_neg at hall
        apply htop
        ext x; simp [hall x]
      rcases hex with ⟨v, hv⟩
      have hspan : Module.finrank F2 (Submodule.span F2 ({v} : Set V)) = 1 := by
        have hv0 : v ≠ 0 := fun h => hv (h ▸ R.zero_mem)
        exact finrank_span_singleton hv0
      have hinf : R ⊓ Submodule.span F2 ({v} : Set V) = ⊥ := by
        ext x
        simp only [Submodule.mem_inf, Submodule.mem_span_singleton, Submodule.mem_bot]
        constructor
        · rintro ⟨hxR, c, rfl⟩
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · simp
          · simp only [one_smul] at hxR; exact False.elim (hv hxR)
        · rintro rfl; exact ⟨R.zero_mem, 0, by simp⟩
      have hsup_fr : Module.finrank F2 ↥(R ⊔ Submodule.span F2 ({v} : Set V)) =
          Module.finrank F2 V := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq R (Submodule.span F2 ({v} : Set V))
        rw [hinf, finrank_bot, add_zero, hspan] at h
        omega
      have hsup_top : R ⊔ Submodule.span F2 ({v} : Set V) = ⊤ :=
        Submodule.eq_top_of_finrank_eq hsup_fr
      apply hv
      change B v = 0
      apply LinearMap.ext
      intro y
      have hy : y ∈ R ⊔ Submodule.span F2 ({v} : Set V) := by rw [hsup_top]; trivial
      rcases Submodule.mem_sup.mp hy with ⟨r, hr, w, hw, rfl⟩
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      rw [map_add, map_smul, hBalt v, smul_zero, add_zero]
      rw [polar_symm hB v r]
      have hr0 : B r = 0 := hr
      rw [hr0]; rfl
    have hfr2 : Module.finrank F2 R + 2 ≤ Module.finrank F2 V := by omega
    have hcardV : Fintype.card V = 2 ^ Module.finrank F2 V := by
      rw [← Nat.card_eq_fintype_card, Module.natCard_eq_pow_finrank (K := F2) (V := V)]
      rw [Nat.card_eq_fintype_card, card_F2]
    have hcardR : Fintype.card R = 2 ^ Module.finrank F2 R := by
      rw [← Nat.card_eq_fintype_card]
      exact card_submodule_F2 R
    have h4R : 4 * Fintype.card R ≤ Fintype.card V := by
      rw [hcardV, hcardR]
      calc 4 * 2 ^ Module.finrank F2 R
          = 2 ^ (Module.finrank F2 R + 2) := by ring
        _ ≤ 2 ^ Module.finrank F2 V := Nat.pow_le_pow_right (by omega) hfr2
    have hSsq_le : S * S ≤ (Fintype.card V : ℤ) * (Fintype.card R : ℤ) := by
      rw [hSsq2]
      change (Fintype.card V : ℤ) * (∑ z : R, chi (gR z)) ≤ _
      rw [hgR]
      split_ifs
      · exact le_rfl
      · positivity
    have h4S : (2 * (S.natAbs : ℤ)) ^ 2 ≤ (Fintype.card V : ℤ) ^ 2 := by
      have h1 : (S.natAbs : ℤ) ^ 2 = S * S := by
        rw [sq, Int.natAbs_mul_self']
      calc (2 * (S.natAbs : ℤ)) ^ 2
          = 4 * (S.natAbs : ℤ) ^ 2 := by ring
        _ = 4 * (S * S) := by rw [h1]
        _ ≤ 4 * ((Fintype.card V : ℤ) * (Fintype.card R : ℤ)) := by linarith
        _ = (Fintype.card V : ℤ) * (4 * (Fintype.card R : ℤ)) := by ring
        _ ≤ (Fintype.card V : ℤ) * (Fintype.card V : ℤ) := by
            have h4Rz : 4 * (Fintype.card R : ℤ) ≤ (Fintype.card V : ℤ) := by exact_mod_cast h4R
            exact mul_le_mul_of_nonneg_left h4Rz (by positivity)
        _ = (Fintype.card V : ℤ) ^ 2 := by ring
    have hnat : (2 * S.natAbs) ^ 2 ≤ (Fintype.card V) ^ 2 := by exact_mod_cast h4S
    by_contra hlt2
    push_neg at hlt2
    have hsq : (Fintype.card V) ^ 2 < (2 * S.natAbs) ^ 2 := Nat.pow_lt_pow_left hlt2 (by omega)
    omega

-- Bilinear map Phi(d1, d2) = sum_i d1 i * d2 i * A i
def Phi {k m : ℕ} (A : Fin m → (Fin k → F2)) (d1 d2 : Fin m → F2) : Fin k → F2 :=
  ∑ i : Fin m, (d1 i * d2 i) • A i

lemma dotProduct_Phi {k m : ℕ} (A : Fin m → (Fin k → F2))
    (d1 d2 : Fin m → F2) (u : Fin k → F2) :
    dotProduct (Phi A d1 d2) u = ∑ i : Fin m, dotProduct (A i) u * d1 i * d2 i := by
  simp only [Phi, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma Phi_add_left {k m : ℕ} (A : Fin m → (Fin k → F2))
    (d1 d1' d2 : Fin m → F2) :
    Phi A (d1 + d1') d2 = Phi A d1 d2 + Phi A d1' d2 := by
  ext j
  simp only [Phi, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma Phi_add_right {k m : ℕ} (A : Fin m → (Fin k → F2))
    (d1 d2 d2' : Fin m → F2) :
    Phi A d1 (d2 + d2') = Phi A d1 d2 + Phi A d1 d2' := by
  ext j
  simp only [Phi, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

lemma Phi_single_left {k m : ℕ} (A : Fin m → (Fin k → F2))
    (i : Fin m) (d2 : Fin m → F2) :
    Phi A (Pi.single i 1) d2 = d2 i • A i := by
  ext j
  simp only [Phi, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Pi.single_eq_of_ne hbi]
  · intro hi; exact False.elim (hi (Finset.mem_univ i))

lemma Phi_single_right {k m : ℕ} (A : Fin m → (Fin k → F2))
    (d1 : Fin m → F2) (i : Fin m) :
    Phi A d1 (Pi.single i 1) = d1 i • A i := by
  ext j
  simp only [Phi, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [Pi.single_eq_of_ne hbi]
  · intro hi; exact False.elim (hi (Finset.mem_univ i))

-- Count S(D1, P2, I) = #{(d1, d2) ∈ D1 × P2 : ∀ u ∈ I, dotProduct (Phi A d1 d2) u = 0}
open Classical in
noncomputable def solCount {k m : ℕ} (A : Fin m → (Fin k → F2))
    (D1 P2 : Submodule F2 (Fin m → F2)) (I : Submodule F2 (Fin k → F2)) : ℕ :=
  ((Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).filter (fun p =>
    p.1 ∈ D1 ∧ p.2 ∈ P2 ∧ ∀ u ∈ I, dotProduct (Phi A p.1 p.2) u = 0)).card

-- Existence of a hyperplane of I orthogonal to a given vector v
lemma exists_hyperplane_orth {k : ℕ} (I : Submodule F2 (Fin k → F2)) (d : ℕ)
    (hI : Module.finrank F2 I = d + 1) (v : Fin k → F2) :
    ∃ I' : Submodule F2 (Fin k → F2),
      I' ≤ I ∧ Module.finrank F2 I' = d ∧ ∀ u ∈ I', dotProduct v u = 0 := by
  classical
  let φ : I →ₗ[F2] F2 :=
    { toFun := fun u => dotProduct v u.1
      map_add' := fun x y => by simp [dotProduct_add]
      map_smul' := fun c x => by simp [dotProduct_smul] }
  by_cases hφ : φ = 0
  · -- Any hyperplane of I works
    have he : (Fin (d + 1) → F2) ≃ₗ[F2] I :=
      LinearEquiv.ofFinrankEq (Fin (d + 1) → F2) I (by rw [Module.finrank_fin_fun, hI])
    let proj0 : (Fin (d + 1) → F2) →ₗ[F2] F2 := LinearMap.proj 0
    let K0 : Submodule F2 (Fin (d + 1) → F2) := LinearMap.ker proj0
    have hsurj : Function.Surjective proj0 := by
      intro c
      exact ⟨Pi.single 0 c, by simp [proj0]⟩
    have hK0_fr : Module.finrank F2 K0 = d := by
      have h := LinearMap.finrank_range_add_finrank_ker proj0
      have hr : LinearMap.range proj0 = ⊤ := LinearMap.range_eq_top.mpr hsurj
      rw [hr, finrank_top] at h
      simp only [Module.finrank_fin_fun, Module.finrank_self] at h
      dsimp only [K0]; omega
    let I' : Submodule F2 (Fin k → F2) :=
      Submodule.map I.subtype (Submodule.map he.toLinearMap K0)
    refine ⟨I', ?_, ?_, ?_⟩
    · intro x hx
      rcases Submodule.mem_map.mp hx with ⟨y, _, rfl⟩
      exact y.2
    · have h1 : Module.finrank F2 I' = Module.finrank F2 (Submodule.map he.toLinearMap K0) :=
        finrank_map_of_inj I.injective_subtype _
      have h2 : Module.finrank F2 (Submodule.map he.toLinearMap K0) = Module.finrank F2 K0 :=
        finrank_map_of_inj he.injective _
      rw [h1, h2, hK0_fr]
    · intro u hu
      rcases Submodule.mem_map.mp hu with ⟨y, _, rfl⟩
      have := LinearMap.congr_fun hφ y
      exact this
  · -- φ is nonzero, hence surjective onto F2
    have hsurj : Function.Surjective φ := by
      have hex : ∃ y : I, φ y = 1 := by
        by_contra hall
        push_neg at hall
        apply hφ
        apply LinearMap.ext
        intro y
        rcases zmod2_eq_zero_or_one (φ y) with h0 | h1
        · exact h0
        · exact False.elim (hall y h1)
      rcases hex with ⟨y, hy⟩
      intro c
      rcases zmod2_eq_zero_or_one c with rfl | rfl
      · exact ⟨0, map_zero φ⟩
      · exact ⟨y, hy⟩
    let K : Submodule F2 I := LinearMap.ker φ
    have hK_fr : Module.finrank F2 K = d := by
      have h := LinearMap.finrank_range_add_finrank_ker φ
      have hr : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
      rw [hr, finrank_top, Module.finrank_self, hI] at h
      dsimp only [K]; omega
    let I' : Submodule F2 (Fin k → F2) := Submodule.map I.subtype K
    refine ⟨I', ?_, ?_, ?_⟩
    · intro x hx
      rcases Submodule.mem_map.mp hx with ⟨y, _, rfl⟩
      exact y.2
    · rw [finrank_map_of_inj I.injective_subtype K, hK_fr]
    · intro u hu
      rcases Submodule.mem_map.mp hu with ⟨y, hy, rfl⟩
      exact hy

-- If D1 ≠ ⊤ in Fin m → F2, some standard basis vector e_i is outside D1
lemma exists_single_not_mem {m : ℕ} (D1 : Submodule F2 (Fin m → F2))
    (hD1 : Module.finrank F2 D1 < m) :
    ∃ i : Fin m, Pi.single i (1 : F2) ∉ D1 := by
  by_contra hall
  push_neg at hall
  have htop : D1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i : Fin m, x i • Pi.single i (1 : F2) := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [Pi.single_eq_of_ne (Ne.symm hbj)]
      · intro hj; exact False.elim (hj (Finset.mem_univ j))
    rw [hx]
    exact Submodule.sum_mem D1 (fun i _ => Submodule.smul_mem D1 (x i) (hall i))
  rw [htop, finrank_top, Module.finrank_fin_fun] at hD1
  omega

lemma finrank_sup_span_single {m : ℕ} (D1 : Submodule F2 (Fin m → F2))
    (i : Fin m) (hi : Pi.single i (1 : F2) ∉ D1) :
    Module.finrank F2 ↥(D1 ⊔ Submodule.span F2 ({Pi.single i (1 : F2)} : Set (Fin m → F2))) =
      Module.finrank F2 D1 + 1 := by
  have hne0 : (Pi.single i (1 : F2) : Fin m → F2) ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp at this
  have hsp : Module.finrank F2 (Submodule.span F2 ({Pi.single i (1 : F2)} : Set (Fin m → F2))) = 1 :=
    finrank_span_singleton hne0
  have hinf : D1 ⊓ Submodule.span F2 ({Pi.single i (1 : F2)} : Set (Fin m → F2)) = ⊥ := by
    ext x
    simp only [Submodule.mem_inf, Submodule.mem_span_singleton, Submodule.mem_bot]
    constructor
    · rintro ⟨hx, c, rfl⟩
      rcases zmod2_eq_zero_or_one c with rfl | rfl
      · simp
      · simp only [one_smul] at hx; exact False.elim (hi hx)
    · rintro rfl; exact ⟨D1.zero_mem, 0, by simp⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq D1
    (Submodule.span F2 ({Pi.single i (1 : F2)} : Set (Fin m → F2)))
  rw [hinf, finrank_bot, add_zero, hsp] at h
  exact h

-- 1-step lifting on D1: increases finrank D1 by 1, decreases finrank I by 1, doubles solCount
lemma solCount_step_left {k m : ℕ} (A : Fin m → (Fin k → F2))
    (D1 P2 : Submodule F2 (Fin m → F2)) (I : Submodule F2 (Fin k → F2))
    (hD1 : Module.finrank F2 D1 < m) (d : ℕ) (hI : Module.finrank F2 I = d + 1) :
    ∃ (D1' : Submodule F2 (Fin m → F2)) (I' : Submodule F2 (Fin k → F2)),
      Module.finrank F2 D1' = Module.finrank F2 D1 + 1 ∧
      I' ≤ I ∧ Module.finrank F2 I' = d ∧
      2 * solCount A D1 P2 I ≤ solCount A D1' P2 I' := by
  classical
  rcases exists_single_not_mem D1 hD1 with ⟨i, hi⟩
  rcases exists_hyperplane_orth I d hI (A i) with ⟨I', hI'le, hI'fr, hI'orth⟩
  let e : Fin m → F2 := Pi.single i (1 : F2)
  let D1' : Submodule F2 (Fin m → F2) := D1 ⊔ Submodule.span F2 ({e} : Set (Fin m → F2))
  refine ⟨D1', I', finrank_sup_span_single D1 i hi, hI'le, hI'fr, ?_⟩
  let S0 := (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).filter (fun p =>
    p.1 ∈ D1 ∧ p.2 ∈ P2 ∧ ∀ u ∈ I, dotProduct (Phi A p.1 p.2) u = 0)
  let S1 := (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).filter (fun p =>
    p.1 ∈ D1' ∧ p.2 ∈ P2 ∧ ∀ u ∈ I', dotProduct (Phi A p.1 p.2) u = 0)
  have hS0 : solCount A D1 P2 I = S0.card := by unfold solCount; congr 1
  have hS1 : solCount A D1' P2 I' = S1.card := by unfold solCount; congr 1
  rw [hS0, hS1]
  let shift : (Fin m → F2) × (Fin m → F2) → (Fin m → F2) × (Fin m → F2) :=
    fun p => (p.1 + e, p.2)
  have hshift_inj : Function.Injective shift := by
    intro a b hab
    dsimp only [shift] at hab
    rcases Prod.mk.inj hab with ⟨h1, h2⟩
    exact Prod.ext (add_right_cancel h1) h2
  have hsub0 : S0 ⊆ S1 := by
    intro p hp
    simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨Submodule.mem_sup_left hp.1, hp.2.1, fun u hu => hp.2.2 u (hI'le hu)⟩
  have hsub1 : S0.image shift ⊆ S1 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, shift] at hp ⊢
    refine ⟨Submodule.add_mem D1' (Submodule.mem_sup_left hp.1)
        (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton e))),
      hp.2.1, ?_⟩
    intro u hu
    rw [Phi_add_left, add_dotProduct, hp.2.2 u (hI'le hu), zero_add]
    rw [Phi_single_left, smul_dotProduct, hI'orth u hu, smul_zero]
  have hdisj : Disjoint S0 (S0.image shift) := by
    rw [Finset.disjoint_left]
    intro p hp hpi
    rcases Finset.mem_image.mp hpi with ⟨q, hq, hqp⟩
    simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h1 : q.1 + e = p.1 := congrArg Prod.fst hqp
    have heD1 : e ∈ D1 := by
      have h2 : e = p.1 - q.1 := by
        rw [← h1, add_sub_cancel_left]
      rw [h2]
      exact Submodule.sub_mem D1 hp.1 hq.1
    exact hi heD1
  have hunion : S0 ∪ S0.image shift ⊆ S1 := Finset.union_subset hsub0 hsub1
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hshift_inj] at hcard
  omega

-- 1-step lifting on P2: increases finrank P2 by 1, decreases finrank I by 1, doubles solCount
lemma solCount_step_right {k m : ℕ} (A : Fin m → (Fin k → F2))
    (D1 P2 : Submodule F2 (Fin m → F2)) (I : Submodule F2 (Fin k → F2))
    (hP2 : Module.finrank F2 P2 < m) (d : ℕ) (hI : Module.finrank F2 I = d + 1) :
    ∃ (P2' : Submodule F2 (Fin m → F2)) (I' : Submodule F2 (Fin k → F2)),
      Module.finrank F2 P2' = Module.finrank F2 P2 + 1 ∧
      I' ≤ I ∧ Module.finrank F2 I' = d ∧
      2 * solCount A D1 P2 I ≤ solCount A D1 P2' I' := by
  classical
  rcases exists_single_not_mem P2 hP2 with ⟨i, hi⟩
  rcases exists_hyperplane_orth I d hI (A i) with ⟨I', hI'le, hI'fr, hI'orth⟩
  let e : Fin m → F2 := Pi.single i (1 : F2)
  let P2' : Submodule F2 (Fin m → F2) := P2 ⊔ Submodule.span F2 ({e} : Set (Fin m → F2))
  refine ⟨P2', I', finrank_sup_span_single P2 i hi, hI'le, hI'fr, ?_⟩
  let S0 := (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).filter (fun p =>
    p.1 ∈ D1 ∧ p.2 ∈ P2 ∧ ∀ u ∈ I, dotProduct (Phi A p.1 p.2) u = 0)
  let S1 := (Finset.univ : Finset ((Fin m → F2) × (Fin m → F2))).filter (fun p =>
    p.1 ∈ D1 ∧ p.2 ∈ P2' ∧ ∀ u ∈ I', dotProduct (Phi A p.1 p.2) u = 0)
  have hS0 : solCount A D1 P2 I = S0.card := by unfold solCount; congr 1
  have hS1 : solCount A D1 P2' I' = S1.card := by unfold solCount; congr 1
  rw [hS0, hS1]
  let shift : (Fin m → F2) × (Fin m → F2) → (Fin m → F2) × (Fin m → F2) :=
    fun p => (p.1, p.2 + e)
  have hshift_inj : Function.Injective shift := by
    intro a b hab
    dsimp only [shift] at hab
    rcases Prod.mk.inj hab with ⟨h1, h2⟩
    exact Prod.ext h1 (add_right_cancel h2)
  have hsub0 : S0 ⊆ S1 := by
    intro p hp
    simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, Submodule.mem_sup_left hp.2.1, fun u hu => hp.2.2 u (hI'le hu)⟩
  have hsub1 : S0.image shift ⊆ S1 := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and, shift] at hp ⊢
    refine ⟨hp.1, Submodule.add_mem P2' (Submodule.mem_sup_left hp.2.1)
        (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton e))), ?_⟩
    intro u hu
    rw [Phi_add_right, add_dotProduct, hp.2.2 u (hI'le hu), zero_add]
    rw [Phi_single_right, smul_dotProduct, hI'orth u hu, smul_zero]
  have hdisj : Disjoint S0 (S0.image shift) := by
    rw [Finset.disjoint_left]
    intro p hp hpi
    rcases Finset.mem_image.mp hpi with ⟨q, hq, hqp⟩
    simp only [S0, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have h2 : q.2 + e = p.2 := congrArg Prod.snd hqp
    have heP2 : e ∈ P2 := by
      have h3 : e = p.2 - q.2 := by rw [← h2, add_sub_cancel_left]
      rw [h3]
      exact Submodule.sub_mem P2 hp.2.1 hq.2.1
    exact hi heP2
  have hunion : S0 ∪ S0.image shift ⊆ S1 := Finset.union_subset hsub0 hsub1
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hshift_inj] at hcard
  omega

-- Full induction lifting D1 and P2 to ⊤
lemma solCount_lift_to_top {k m : ℕ} (A : Fin m → (Fin k → F2)) :
    ∀ (c : ℕ) (D1 P2 : Submodule F2 (Fin m → F2)) (I : Submodule F2 (Fin k → F2)),
      (m - Module.finrank F2 D1) + (m - Module.finrank F2 P2) = c →
      c ≤ Module.finrank F2 I →
      ∃ I' : Submodule F2 (Fin k → F2),
        I' ≤ I ∧ Module.finrank F2 I' = Module.finrank F2 I - c ∧
        2 ^ c * solCount A D1 P2 I ≤ solCount A ⊤ ⊤ I' := by
  intro c
  induction c with
  | zero =>
    intro D1 P2 I hc _
    have hD1_le : Module.finrank F2 D1 ≤ m := by
      have := Submodule.finrank_le D1
      simpa using this
    have hP2_le : Module.finrank F2 P2 ≤ m := by
      have := Submodule.finrank_le P2
      simpa using this
    have hD1 : D1 = ⊤ := Submodule.eq_top_of_finrank_eq (by simp; omega)
    have hP2 : P2 = ⊤ := Submodule.eq_top_of_finrank_eq (by simp; omega)
    refine ⟨I, le_rfl, by omega, ?_⟩
    simp [hD1, hP2]
  | succ c ih =>
    intro D1 P2 I hc hle
    have hD1_le : Module.finrank F2 D1 ≤ m := by
      have := Submodule.finrank_le D1; simpa using this
    have hP2_le : Module.finrank F2 P2 ≤ m := by
      have := Submodule.finrank_le P2; simpa using this
    have hIpos : 1 ≤ Module.finrank F2 I := by omega
    by_cases hD1 : Module.finrank F2 D1 < m
    · rcases solCount_step_left A D1 P2 I hD1 (Module.finrank F2 I - 1) (by omega) with
        ⟨D1', I1, hD1'fr, hI1le, hI1fr, hstep⟩
      rcases ih D1' P2 I1 (by omega) (by omega) with ⟨I', hI'le, hI'fr, hrec⟩
      refine ⟨I', hI'le.trans hI1le, by omega, ?_⟩
      calc 2 ^ (c + 1) * solCount A D1 P2 I
          = 2 ^ c * (2 * solCount A D1 P2 I) := by ring
        _ ≤ 2 ^ c * solCount A D1' P2 I1 := Nat.mul_le_mul_left _ hstep
        _ ≤ solCount A ⊤ ⊤ I' := hrec
    · have hP2 : Module.finrank F2 P2 < m := by omega
      rcases solCount_step_right A D1 P2 I hP2 (Module.finrank F2 I - 1) (by omega) with
        ⟨P2', I1, hP2'fr, hI1le, hI1fr, hstep⟩
      rcases ih D1 P2' I1 (by omega) (by omega) with ⟨I', hI'le, hI'fr, hrec⟩
      refine ⟨I', hI'le.trans hI1le, by omega, ?_⟩
      calc 2 ^ (c + 1) * solCount A D1 P2 I
          = 2 ^ c * (2 * solCount A D1 P2 I) := by ring
        _ ≤ 2 ^ c * solCount A D1 P2' I1 := Nat.mul_le_mul_left _ hstep
        _ ≤ solCount A ⊤ ⊤ I' := hrec

-- Mass of a subspace I <= Fin k -> F2
def wtA {k m : ℕ} (A : Fin m → (Fin k → F2)) (a : Fin k → F2) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) a ≠ 0)).card

noncomputable def subMass {k m : ℕ} (A : Fin m → (Fin k → F2))
    (I : Submodule F2 (Fin k → F2)) : ℕ :=
  letI : Fintype I := Fintype.ofFinite I
  ∑ u : I, 2 ^ (m - wtA A u.1)

-- Identity: 2^m * subMass A I = 2^(finrank I) * solCount A ⊤ ⊤ I
lemma sum_chi_bilin_single (c : F2) :
    (∑ a : F2, ∑ b : F2, chi (c * a * b)) = if c = 0 then 4 else 2 := by
  rcases zmod2_eq_zero_or_one c with rfl | rfl
  · simp [sum_F2, chi_zero]
  · simp [sum_F2, chi_zero, chi_one]

lemma sum_chi_Phi_full {k m : ℕ} (A : Fin m → (Fin k → F2)) (u : Fin k → F2) :
    (∑ d1 : Fin m → F2, ∑ d2 : Fin m → F2, chi (dotProduct (Phi A d1 d2) u)) =
      (2 ^ m * 2 ^ (m - wtA A u) : ℤ) := by
  have h1 : (∑ d1 : Fin m → F2, ∑ d2 : Fin m → F2, chi (dotProduct (Phi A d1 d2) u)) =
      ∑ p : Fin m → F2 × F2, ∏ i : Fin m, chi (dotProduct (A i) u * (p i).1 * (p i).2) := by
    let e : ((Fin m → F2) × (Fin m → F2)) ≃ (Fin m → F2 × F2) :=
      { toFun := fun q i => (q.1 i, q.2 i)
        invFun := fun p => (fun i => (p i).1, fun i => (p i).2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv e _ _ (fun q => ?_)
    rw [dotProduct_Phi, chi_sum_finset]
    rfl
  rw [h1]
  rw [← Fintype.prod_sum (fun i (x : F2 × F2) => chi (dotProduct (A i) u * x.1 * x.2))]
  have hfactor : ∀ i : Fin m,
      (∑ x : F2 × F2, chi (dotProduct (A i) u * x.1 * x.2)) =
        if dotProduct (A i) u = 0 then (4 : ℤ) else 2 := by
    intro i
    rw [Fintype.sum_prod_type]
    exact sum_chi_bilin_single (dotProduct (A i) u)
  simp_rw [hfactor]
  classical
  have hprod : (∏ i : Fin m, if dotProduct (A i) u = 0 then (4 : ℤ) else 2) =
      4 ^ ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u = 0)).card *
      2 ^ ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u ≠ 0)).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  rw [hprod]
  have hcomp : ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u = 0)).card =
      m - wtA A u := by
    have hdisj : Disjoint ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u = 0))
        ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u ≠ 0)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      exact (Finset.mem_filter.mp hi2).2 (Finset.mem_filter.mp hi1).2
    have hun : (Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u = 0) ∪
        (Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u ≠ 0) = Finset.univ := by
      ext i; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; tauto
    have hadd : ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u = 0)).card +
        wtA A u = m := by
      change ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u = 0)).card +
        ((Finset.univ : Finset (Fin m)).filter (fun i => dotProduct (A i) u ≠ 0)).card = m
      rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_univ, Fintype.card_fin]
    omega
  have hwt_le : wtA A u ≤ m := by
    calc wtA A u ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by simp
  rw [hcomp]
  change (4 : ℤ) ^ (m - wtA A u) * (2 : ℤ) ^ (wtA A u) = (2 : ℤ) ^ m * (2 : ℤ) ^ (m - wtA A u)
  have h4 : (4 : ℤ) ^ (m - wtA A u) = (2 : ℤ) ^ (m - wtA A u) * (2 : ℤ) ^ (m - wtA A u) := by
    rw [← mul_pow]; norm_num
  rw [h4, mul_assoc, mul_comm ((2 : ℤ) ^ (m - wtA A u)) ((2 : ℤ) ^ wtA A u), ← mul_assoc,
    ← pow_add, Nat.sub_add_cancel hwt_le]

lemma subMass_eq_solCount_top {k m : ℕ} (A : Fin m → (Fin k → F2))
    (I : Submodule F2 (Fin k → F2)) :
    2 ^ m * subMass A I = 2 ^ Module.finrank F2 I * solCount A ⊤ ⊤ I := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  have hcardI : Fintype.card I = 2 ^ Module.finrank F2 I := by
    rw [← Nat.card_eq_fintype_card]; exact card_submodule_F2 I
  suffices hZ : ((2 ^ m * subMass A I : ℕ) : ℤ) =
      ((2 ^ Module.finrank F2 I * solCount A ⊤ ⊤ I : ℕ) : ℤ) by
    exact_mod_cast hZ
  have hLHS : ((2 ^ m * subMass A I : ℕ) : ℤ) =
      ∑ u : I, ∑ d1 : Fin m → F2, ∑ d2 : Fin m → F2, chi (dotProduct (Phi A d1 d2) u.1) := by
    simp only [subMass, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [sum_chi_Phi_full]
  rw [hLHS]
  calc (∑ u : I, ∑ d1 : Fin m → F2, ∑ d2 : Fin m → F2, chi (dotProduct (Phi A d1 d2) u.1))
      = ∑ d1 : Fin m → F2, ∑ d2 : Fin m → F2, ∑ u : I, chi (dotProduct (Phi A d1 d2) u.1) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun d1 _ => Finset.sum_comm)
    _ = ∑ p : (Fin m → F2) × (Fin m → F2), ∑ u : I, chi (dotProduct (Phi A p.1 p.2) u.1) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : (Fin m → F2) × (Fin m → F2),
          if (∀ u ∈ I, dotProduct (Phi A p.1 p.2) u = 0) then (Fintype.card I : ℤ) else 0 := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        let φ : (Fin k → F2) →ₗ[F2] F2 :=
          { toFun := fun u => dotProduct (Phi A p.1 p.2) u
            map_add' := fun x y => by simp [dotProduct_add]
            map_smul' := fun c x => by simp [dotProduct_smul] }
        exact sum_chi_linearMap_sub I φ
    _ = (Fintype.card I : ℤ) * (solCount A ⊤ ⊤ I : ℤ) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 2
        unfold solCount
        congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, Submodule.mem_top, true_and]
    _ = ((2 ^ Module.finrank F2 I * solCount A ⊤ ⊤ I : ℕ) : ℤ) := by
        rw [hcardI]; push_cast; ring

-- 1-step hyperplane averaging for subMass
lemma exists_hyperplane_subMass {k m : ℕ} (A : Fin m → (Fin k → F2))
    (I : Submodule F2 (Fin k → F2)) (d : ℕ) (hI : Module.finrank F2 I = d + 1) :
    ∃ I' : Submodule F2 (Fin k → F2),
      I' ≤ I ∧ Module.finrank F2 I' = d ∧ subMass A I ≤ 2 * subMass A I' := by
  classical
  have he : (Fin (d + 1) → F2) ≃ₗ[F2] I :=
    LinearEquiv.ofFinrankEq (Fin (d + 1) → F2) I (by rw [Module.finrank_fin_fun, hI])
  let V := Fin (d + 1) → F2
  let f : V → ℕ := fun x => 2 ^ (m - wtA A (he x).1)
  have hf_le : ∀ x : V, f x ≤ 2 ^ m := fun x => Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
  have hf_zero : f 0 = 2 ^ m := by
    have h0 : (he 0).1 = 0 := by simp
    have hwt0 : wtA A 0 = 0 := by simp [wtA]
    simp [f, h0, hwt0]
  have hsumI : subMass A I = ∑ x : V, f x := by
    letI : Fintype I := Fintype.ofFinite I
    unfold subMass
    exact (Fintype.sum_equiv he.toEquiv f (fun u : I => 2 ^ (m - wtA A u.1)) (fun _ => rfl)).symm
  -- For each nonzero v : V, let H v = {x : V | dotProduct v x = 0}
  let nonzeros : Finset V := Finset.univ.filter (fun v : V => v ≠ 0)
  have hnz_card : nonzeros.card = 2 ^ (d + 1) - 1 := by
    have h1 : nonzeros = Finset.univ.erase (0 : V) := by
      ext v; simp [nonzeros]
    rw [h1, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_fin_F2]
  have hnz_pos : 0 < nonzeros.card := by
    rw [hnz_card]
    have : 2 ≤ 2 ^ (d + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  -- Count how many nonzero v satisfy dotProduct v x = 0
  have hcount_orth : ∀ x : V,
      (nonzeros.filter (fun v => dotProduct v x = 0)).card =
        if x = 0 then 2 ^ (d + 1) - 1 else 2 ^ d - 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx, hnz_card]
    · simp only [hx, ↓reduceIte]
      let φ : V →ₗ[F2] F2 :=
        { toFun := fun v => dotProduct v x
          map_add' := fun a b => add_dotProduct a b x
          map_smul' := fun c a => smul_dotProduct c a x }
      have hsurj : Function.Surjective φ := by
        have hex : ∃ i : Fin (d + 1), x i ≠ 0 := by
          by_contra h0; push_neg at h0; exact hx (funext h0)
        rcases hex with ⟨i, hi⟩
        have hi1 : x i = 1 := by
          rcases zmod2_eq_zero_or_one (x i) with h0 | h1
          · exact False.elim (hi h0)
          · exact h1
        intro c
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · exact ⟨0, map_zero φ⟩
        · refine ⟨Pi.single i 1, ?_⟩
          change ∑ j : Fin (d + 1), (Pi.single i (1 : F2) : Fin (d + 1) → F2) j * x j = 1
          rw [Finset.sum_eq_single i]
          · simp [hi1]
          · intro b _ hbi; simp [Pi.single_eq_of_ne hbi]
          · intro hi'; exact False.elim (hi' (Finset.mem_univ i))
      have hker_fr : Module.finrank F2 (LinearMap.ker φ) = d := by
        have h := LinearMap.finrank_range_add_finrank_ker φ
        have hr : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
        rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
        omega
      letI : Fintype (LinearMap.ker φ) := Fintype.ofFinite _
      have hker_card : ((Finset.univ : Finset V).filter (fun v => dotProduct v x = 0)).card = 2 ^ d := by
        have hbij : ((Finset.univ : Finset V).filter (fun v => dotProduct v x = 0)).card =
            Fintype.card (LinearMap.ker φ) := by
          refine Finset.card_bij (fun v hv => (⟨v, (Finset.mem_filter.mp hv).2⟩ : LinearMap.ker φ))
            (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ hab => congrArg Subtype.val hab)
            (fun y _ => ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩)
        rw [hbij, ← Nat.card_eq_fintype_card, card_submodule_F2, hker_fr]
      have herase : nonzeros.filter (fun v => dotProduct v x = 0) =
          ((Finset.univ : Finset V).filter (fun v => dotProduct v x = 0)).erase 0 := by
        ext v; simp [nonzeros, and_comm]
      rw [herase, Finset.card_erase_of_mem (by simp), hker_card]
  -- Double counting sum_{v != 0} sum_{x : dot v x = 0} f x
  have hdouble : (∑ v ∈ nonzeros, ∑ x ∈ Finset.univ.filter (fun x : V => dotProduct v x = 0), f x) =
      (2 ^ (d + 1) - 1) * 2 ^ m + (2 ^ d - 1) * (subMass A I - 2 ^ m) := by
    calc (∑ v ∈ nonzeros, ∑ x ∈ Finset.univ.filter (fun x : V => dotProduct v x = 0), f x)
        = ∑ v ∈ nonzeros, ∑ x : V, if dotProduct v x = 0 then f x else 0 := by
          refine Finset.sum_congr rfl (fun v _ => by rw [Finset.sum_filter])
      _ = ∑ x : V, ∑ v ∈ nonzeros, if dotProduct v x = 0 then f x else 0 := Finset.sum_comm
      _ = ∑ x : V, (nonzeros.filter (fun v => dotProduct v x = 0)).card * f x := by
          refine Finset.sum_congr rfl (fun x _ => by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul])
      _ = ∑ x : V, (if x = 0 then (2 ^ (d + 1) - 1) * f x else (2 ^ d - 1) * f x) := by
          refine Finset.sum_congr rfl (fun x _ => by rw [hcount_orth x]; split_ifs <;> rfl)
      _ = (2 ^ (d + 1) - 1) * f 0 + ∑ x ∈ Finset.univ.erase (0 : V), (2 ^ d - 1) * f x := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V))]
          simp only [↓reduceIte]
          congr 1
          refine Finset.sum_congr rfl (fun x hx => ?_)
          have hne : x ≠ 0 := (Finset.mem_erase.mp hx).1
          simp [hne]
      _ = (2 ^ (d + 1) - 1) * 2 ^ m + (2 ^ d - 1) * (subMass A I - 2 ^ m) := by
          rw [hf_zero, ← Finset.mul_sum]
          congr 2
          have htot : subMass A I = f 0 + ∑ x ∈ Finset.univ.erase (0 : V), f x := by
            rw [hsumI, Finset.add_sum_erase _ _ (Finset.mem_univ (0 : V))]
          rw [hf_zero] at htot
          omega
  -- Check 2 * double >= (2^(d+1) - 1) * subMass A I
  have hmass_ge : 2 ^ m ≤ subMass A I := by
    rw [hsumI]
    calc 2 ^ m = f 0 := hf_zero.symm
      _ ≤ ∑ x : V, f x := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
  have hmass_le : subMass A I ≤ 2 ^ (d + 1) * 2 ^ m := by
    rw [hsumI]
    calc ∑ x : V, f x ≤ ∑ _x : V, 2 ^ m := Finset.sum_le_sum (fun x _ => hf_le x)
      _ = Fintype.card V * 2 ^ m := by simp
      _ = 2 ^ (d + 1) * 2 ^ m := by rw [card_fin_F2]
  have h2ge : nonzeros.card * subMass A I ≤
      2 * ∑ v ∈ nonzeros, ∑ x ∈ Finset.univ.filter (fun x : V => dotProduct v x = 0), f x := by
    rw [hdouble, hnz_card]
    have hpow1 : 1 ≤ 2 ^ d := Nat.one_le_pow d 2 (by omega)
    have hpow2 : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    zify [hmass_ge, hpow1, (by omega : 1 ≤ 2 ^ (d + 1))]
    nlinarith
  -- Pigeonhole: some v ∈ nonzeros has subMass A I ≤ 2 * sum_{x : dot v x = 0} f x
  have hex_v : ∃ v ∈ nonzeros,
      subMass A I ≤ 2 * ∑ x ∈ Finset.univ.filter (fun x : V => dotProduct v x = 0), f x := by
    by_contra hall
    push_neg at hall
    have hlt : (∑ v ∈ nonzeros, 2 * ∑ x ∈ Finset.univ.filter (fun x : V => dotProduct v x = 0), f x) <
        ∑ _v ∈ nonzeros, subMass A I :=
      Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp hnz_pos) (fun v hv => hall v hv)
    rw [← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at hlt
    omega
  rcases hex_v with ⟨v, hv_nz, hv_le⟩
  have hv0 : v ≠ 0 := (Finset.mem_filter.mp hv_nz).2
  let ψ : V →ₗ[F2] F2 :=
    { toFun := fun x => dotProduct v x
      map_add' := fun a b => dotProduct_add v a b
      map_smul' := fun c a => dotProduct_smul c v a }
  have hsurj : Function.Surjective ψ := by
    have hex : ∃ i : Fin (d + 1), v i ≠ 0 := by
      by_contra h0; push_neg at h0; exact hv0 (funext h0)
    rcases hex with ⟨i, hi⟩
    have hi1 : v i = 1 := by
      rcases zmod2_eq_zero_or_one (v i) with h0 | h1
      · exact False.elim (hi h0)
      · exact h1
    intro c
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · exact ⟨0, map_zero ψ⟩
    · refine ⟨Pi.single i 1, ?_⟩
      change ∑ j : Fin (d + 1), v j * (Pi.single i (1 : F2) : Fin (d + 1) → F2) j = 1
      rw [Finset.sum_eq_single i]
      · simp [hi1]
      · intro b _ hbi; simp [Pi.single_eq_of_ne hbi]
      · intro hi'; exact False.elim (hi' (Finset.mem_univ i))
  let K : Submodule F2 V := LinearMap.ker ψ
  have hK_fr : Module.finrank F2 K = d := by
    have h := LinearMap.finrank_range_add_finrank_ker ψ
    have hr : LinearMap.range ψ = ⊤ := LinearMap.range_eq_top.mpr hsurj
    rw [hr, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at h
    dsimp only [K]; omega
  let I' : Submodule F2 (Fin k → F2) :=
    Submodule.map I.subtype (Submodule.map he.toLinearMap K)
  refine ⟨I', ?_, ?_, ?_⟩
  · intro x hx
    rcases Submodule.mem_map.mp hx with ⟨y, _, rfl⟩
    exact y.2
  · rw [finrank_map_of_inj I.injective_subtype _,
      finrank_map_of_inj he.injective _, hK_fr]
  · have hmassI' : subMass A I' =
        ∑ x ∈ Finset.univ.filter (fun x : V => dotProduct v x = 0), f x := by
      letI : Fintype I' := Fintype.ofFinite I'
      unfold subMass
      refine (Finset.sum_bij
        (fun x hx => (⟨(he x).1, by
          have hx0 : dotProduct v x = 0 :=
            (Finset.mem_filter (p := fun z => dotProduct v z = 0).mp hx).2
          have hxK : x ∈ K := hx0
          exact Submodule.mem_map.mpr ⟨he x, Submodule.mem_map.mpr ⟨x, hxK, rfl⟩, rfl⟩⟩ : I'))
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ hab => by
          have h1 : (he a).1 = (he b).1 := congrArg (fun z : I' => z.1) hab
          exact he.injective (Subtype.ext h1))
        (fun u _ => by
          rcases Submodule.mem_map.mp u.2 with ⟨y, hy, hyu⟩
          rcases Submodule.mem_map.mp hy with ⟨x, hxK, rfl⟩
          have hx0 : dotProduct v x = 0 := hxK
          exact ⟨x, Finset.mem_filter (p := fun z => dotProduct v z = 0).mpr
            ⟨Finset.mem_univ _, hx0⟩, Subtype.ext hyu⟩)
        (fun _ _ => rfl)).symm
    rw [hmassI']
    exact hv_le

-- Multi-step subMass descent from dim j + s down to dim j
lemma exists_subspace_subMass {k m : ℕ} (A : Fin m → (Fin k → F2)) :
    ∀ (s j : ℕ) (I : Submodule F2 (Fin k → F2)),
      Module.finrank F2 I = j + s →
      ∃ B : Submodule F2 (Fin k → F2),
        B ≤ I ∧ Module.finrank F2 B = j ∧ subMass A I ≤ 2 ^ s * subMass A B := by
  intro s
  induction s with
  | zero =>
    intro j I hI
    exact ⟨I, le_rfl, by omega, by simp⟩
  | succ s ih =>
    intro j I hI
    rcases exists_hyperplane_subMass A I (j + s) (by omega) with ⟨I1, hI1le, hI1fr, hstep⟩
    rcases ih j I1 hI1fr with ⟨B, hBle, hBfr, hrec⟩
    refine ⟨B, hBle.trans hI1le, hBfr, ?_⟩
    calc subMass A I ≤ 2 * subMass A I1 := hstep
      _ ≤ 2 * (2 ^ s * subMass A B) := Nat.mul_le_mul_left 2 hrec
      _ = 2 ^ (s + 1) * subMass A B := by ring

-- Helper: fiber sum of a function on K decomposed by K1 <= K
open Classical in
lemma fiber_abs_le_solCount {k m r j : ℕ}
    (A : Fin m → (Fin k → F2))
    (L : (Fin (2 * m + r + j) → F2) →ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (K : Submodule F2 (Fin (2 * m + r + j) → F2))
    (K1 : Submodule F2 (Fin (2 * m + r + j) → F2))
    (Z0 : Submodule F2 (Fin (2 * m + r + j) → F2))
    (D1 P2 : Submodule F2 (Fin m → F2))
    (hK1le : K1 ≤ K)
    (hZ0le : Z0 ≤ K1)
    (hK_S : ∀ y ∈ K, (L y).1 = 0)
    (hK1_d2 : ∀ y ∈ K1, (L y).2.2.1 = 0)
    (hK_P2 : ∀ y ∈ K, (L y).2.2.1 ∈ P2)
    (hK1_D1 : ∀ y ∈ K1, (L y).2.1 ∈ D1)
    (hfib_K : ∀ d2 ∈ P2,
      letI : Fintype K := Fintype.ofFinite K
      letI : Fintype K1 := Fintype.ofFinite K1
      ((Finset.univ : Finset K).filter (fun y => (L y.1).2.2.1 = d2)).card = Fintype.card K1)
    (hfib_K1 : ∀ d1 ∈ D1,
      letI : Fintype K1 := Fintype.ofFinite K1
      letI : Fintype Z0 := Fintype.ofFinite Z0
      ((Finset.univ : Finset K1).filter (fun y => (L y.1).2.1 = d1)).card = Fintype.card Z0)
    (u : Fin k → F2) (g : K → F2)
    (hg_polar : ∀ y y' : K,
      g (y + y') + g y + g y' + g 0 =
        ∑ i : Fin m, dotProduct (A i) u *
          ((L y.1).2.1 i * (L y'.1).2.2.1 i + (L y'.1).2.1 i * (L y.1).2.2.1 i)) :
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype Z0 := Fintype.ofFinite Z0
    ((∑ y : K, chi (g y)).natAbs : ℤ) ≤
      (Fintype.card Z0 : ℤ) *
        ∑ d1 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ D1),
        ∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
          chi (dotProduct (Phi A d1 d2) u) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K1 := Fintype.ofFinite K1
  letI : Fintype Z0 := Fintype.ofFinite Z0
  -- Bilinear form on K1 x K
  let bil : K1 → K → F2 := fun y1 y2 =>
    ∑ i : Fin m, dotProduct (A i) u * (L y1.1).2.1 i * (L y2.1).2.2.1 i
  -- For fixed y2 : K, y1 |-> g(y1 + y2) + g(y2) is affine-linear on K1!
  have hK1_polar : ∀ (y1 : K1) (y2 : K),
      g (⟨y1.1, hK1le y1.2⟩ + y2) + g ⟨y1.1, hK1le y1.2⟩ + g y2 + g 0 = bil y1 y2 := by
    intro y1 y2
    rw [hg_polar ⟨y1.1, hK1le y1.2⟩ y2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have h0 : (L y1.1).2.2.1 i = 0 := congrFun (hK1_d2 y1.1 y1.2) i
    rw [h0]; ring
  have hK1_lin0 : ∀ a b : K1,
      (g ⟨a.1 + b.1, hK1le (K1.add_mem a.2 b.2)⟩ + g 0) =
      (g ⟨a.1, hK1le a.2⟩ + g 0) + (g ⟨b.1, hK1le b.2⟩ + g 0) := by
    intro a b
    have h1 := hK1_polar a ⟨b.1, hK1le b.2⟩
    have h0 : bil a ⟨b.1, hK1le b.2⟩ = 0 := by
      simp only [bil]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have hb0 : (L b.1).2.2.1 i = 0 := congrFun (hK1_d2 b.1 b.2) i
      rw [hb0, mul_zero]
    rw [h0] at h1
    have h2 : g ⟨a.1 + b.1, hK1le (K1.add_mem a.2 b.2)⟩ + g ⟨a.1, hK1le a.2⟩ +
        g ⟨b.1, hK1le b.2⟩ + g 0 = 0 := h1
    have h3 := congrArg (· + g ⟨a.1, hK1le a.2⟩ + g ⟨b.1, hK1le b.2⟩) h2
    calc g ⟨a.1 + b.1, hK1le (K1.add_mem a.2 b.2)⟩ + g 0
        = g ⟨a.1 + b.1, hK1le (K1.add_mem a.2 b.2)⟩ + g ⟨a.1, hK1le a.2⟩ +
          g ⟨b.1, hK1le b.2⟩ + g 0 + g ⟨a.1, hK1le a.2⟩ + g ⟨b.1, hK1le b.2⟩ := by
            have := zmod2_add_self (g ⟨a.1, hK1le a.2⟩)
            have := zmod2_add_self (g ⟨b.1, hK1le b.2⟩)
            calc g ⟨a.1 + b.1, hK1le (K1.add_mem a.2 b.2)⟩ + g 0
                = g ⟨a.1 + b.1, hK1le (K1.add_mem a.2 b.2)⟩ + g 0 +
                  (g ⟨a.1, hK1le a.2⟩ + g ⟨a.1, hK1le a.2⟩) +
                  (g ⟨b.1, hK1le b.2⟩ + g ⟨b.1, hK1le b.2⟩) := by
                    rw [zmod2_add_self, zmod2_add_self]; ring
              _ = _ := by ring
      _ = 0 + g ⟨a.1, hK1le a.2⟩ + g ⟨b.1, hK1le b.2⟩ := h3
      _ = (g ⟨a.1, hK1le a.2⟩ + g 0) + (g ⟨b.1, hK1le b.2⟩ + g 0) := by
          calc 0 + g ⟨a.1, hK1le a.2⟩ + g ⟨b.1, hK1le b.2⟩
              = g ⟨a.1, hK1le a.2⟩ + g ⟨b.1, hK1le b.2⟩ + (g 0 + g 0) := by
                rw [zmod2_add_self]; ring
            _ = _ := by ring
  let lin0 : K1 →ₗ[F2] F2 :=
    { toFun := fun y1 => g ⟨y1.1, hK1le y1.2⟩ + g 0
      map_add' := fun a b => hK1_lin0 a b
      map_smul' := fun c a => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp only [zero_smul, ZeroMemClass.coe_zero, RingHom.id_apply, smul_eq_mul, zero_mul]
          exact zmod2_add_self (g 0)
        · simp }
  let bilMap : K →ₗ[F2] K1 →ₗ[F2] F2 :=
    { toFun := fun y2 =>
        { toFun := fun y1 => bil y1 y2
          map_add' := fun a b => by
            simp only [bil, Submodule.coe_add, map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
              ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl (fun i _ => by ring)
          map_smul' := fun c a => by
            rcases zmod2_eq_zero_or_one c with rfl | rfl
            · simp [bil]
            · simp [bil] }
      map_add' := fun a b => by
        apply LinearMap.ext; intro y1
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, bil, Submodule.coe_add,
          map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      map_smul' := fun c a => by
        apply LinearMap.ext; intro y1
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp [bil]
        · simp [bil] }
  -- Step 1: |K1| * |sum_{y in K} chi(g y)| <= |K1| * #{y2 in K : bilMap y2 = lin0}
  have hstep1 : (Fintype.card K1 : ℤ) * ((∑ y : K, chi (g y)).natAbs : ℤ) ≤
      (Fintype.card K1 : ℤ) *
        (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = lin0)).card : ℤ) := by
    have hshift : (Fintype.card K1 : ℤ) * (∑ y : K, chi (g y)) =
        ∑ y2 : K, ∑ y1 : K1, chi (g (⟨y1.1, hK1le y1.2⟩ + y2)) := by
      have h1 : ∀ y1 : K1, (∑ y2 : K, chi (g (⟨y1.1, hK1le y1.2⟩ + y2))) =
          ∑ y : K, chi (g y) := fun y1 =>
        Fintype.sum_equiv (Equiv.addLeft (⟨y1.1, hK1le y1.2⟩ : K)) _ _ (fun _ => rfl)
      rw [Finset.sum_comm]
      simp_rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hinner : ∀ y2 : K,
        (∑ y1 : K1, chi (g (⟨y1.1, hK1le y1.2⟩ + y2))) =
          if bilMap y2 = lin0 then (Fintype.card K1 : ℤ) * chi (g y2) else 0 := by
      intro y2
      have hrew : ∀ y1 : K1, g (⟨y1.1, hK1le y1.2⟩ + y2) = g y2 + (lin0 + bilMap y2) y1 := by
        intro y1
        have h1 := hK1_polar y1 y2
        have h2 := congrArg (· + g ⟨y1.1, hK1le y1.2⟩ + g y2 + g 0) h1
        have h3 : g (⟨y1.1, hK1le y1.2⟩ + y2) + g ⟨y1.1, hK1le y1.2⟩ + g y2 + g 0 +
            g ⟨y1.1, hK1le y1.2⟩ + g y2 + g 0 = g (⟨y1.1, hK1le y1.2⟩ + y2) := by
          calc _ = g (⟨y1.1, hK1le y1.2⟩ + y2) +
                (g ⟨y1.1, hK1le y1.2⟩ + g ⟨y1.1, hK1le y1.2⟩) +
                (g y2 + g y2) + (g 0 + g 0) := by ring
            _ = _ := by rw [zmod2_add_self, zmod2_add_self, zmod2_add_self]; ring
        rw [h3] at h2
        rw [h2]
        simp only [LinearMap.add_apply, lin0, bilMap, LinearMap.coe_mk, AddHom.coe_mk]
        ring
      simp_rw [hrew, chi_add]
      rw [← Finset.mul_sum, sum_chi_linearMap (lin0 + bilMap y2)]
      have hiff : (lin0 + bilMap y2 = 0) ↔ (bilMap y2 = lin0) := by
        constructor
        · intro h0
          apply LinearMap.ext; intro y1
          have h1 : lin0 y1 + bilMap y2 y1 = 0 := LinearMap.congr_fun h0 y1
          have h2 := congrArg (· + lin0 y1) h1
          rw [zero_add] at h2
          rw [← h2]
          calc bilMap y2 y1 = (lin0 y1 + lin0 y1) + bilMap y2 y1 := by rw [zmod2_add_self, zero_add]
            _ = lin0 y1 + bilMap y2 y1 + lin0 y1 := by ring
        · intro heq
          apply LinearMap.ext; intro y1
          simp [heq, zmod2_add_self]
      by_cases h0 : bilMap y2 = lin0
      · rw [if_pos (hiff.mpr h0), if_pos h0]; ring
      · rw [if_neg (fun h => h0 (hiff.mp h)), if_neg h0]; ring
    have habs_eq : (Fintype.card K1 : ℤ) * ((∑ y : K, chi (g y)).natAbs : ℤ) =
        |∑ y2 : K, ∑ y1 : K1, chi (g (⟨y1.1, hK1le y1.2⟩ + y2))| := by
      rw [← hshift, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), Int.natCast_natAbs]
    rw [habs_eq]
    calc |∑ y2 : K, ∑ y1 : K1, chi (g (⟨y1.1, hK1le y1.2⟩ + y2))|
        ≤ ∑ y2 : K, |∑ y1 : K1, chi (g (⟨y1.1, hK1le y1.2⟩ + y2))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y2 : K, if bilMap y2 = lin0 then (Fintype.card K1 : ℤ) else 0 := by
          refine Finset.sum_congr rfl (fun y2 _ => ?_)
          rw [hinner y2]
          split_ifs
          · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
            have hchi1 : |chi (g y2)| = 1 := by
              rcases zmod2_eq_zero_or_one (g y2) with h0 | h0 <;> simp [h0, chi]
            rw [hchi1, mul_one]
          · simp
      _ = (Fintype.card K1 : ℤ) *
            (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = lin0)).card : ℤ) := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Cancel Fintype.card K1 > 0
  have hK1_pos : (0 : ℤ) < Fintype.card K1 := by
    have : 0 < Fintype.card K1 := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this
  have hfib_le_ker : ((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = lin0)).card ≤
      ((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = 0)).card := by
    by_cases hempty : ((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = lin0)).Nonempty
    · rcases hempty with ⟨y0, hy0⟩
      have hy0' : bilMap y0 = lin0 := (Finset.mem_filter.mp hy0).2
      refine Finset.card_le_card_of_injOn (fun y2 => y2 + y0) ?_ ?_
      · intro y2 hy2
        have hy2' : bilMap y2 = lin0 := (Finset.mem_filter.mp hy2).2
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, map_add, hy2', hy0']
        apply LinearMap.ext; intro y1; exact zmod2_add_self (lin0 y1)
      · intro a _ b _ hab; exact add_right_cancel hab
    · rw [Finset.not_nonempty_iff_eq_empty.mp hempty]; simp
  have hstep2 : ((∑ y : K, chi (g y)).natAbs : ℤ) ≤
      (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = 0)).card : ℤ) := by
    have h1 : ((∑ y : K, chi (g y)).natAbs : ℤ) ≤
        (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = lin0)).card : ℤ) :=
      le_of_mul_le_mul_left hstep1 hK1_pos
    have h2 : (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = lin0)).card : ℤ) ≤
        (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = 0)).card : ℤ) := by
      exact_mod_cast hfib_le_ker
    exact h1.trans h2
  -- Express |ker bilMap| * |K1| = sum_{y1 : K1} sum_{y2 : K} chi (bil y1 y2)
  have hker_sum : (Fintype.card K1 : ℤ) *
      (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = 0)).card : ℤ) =
      ∑ y1 : K1, ∑ y2 : K, chi (bil y1 y2) := by
    rw [Finset.sum_comm]
    have h1 : ∀ y2 : K, (∑ y1 : K1, chi (bil y1 y2)) =
        if bilMap y2 = 0 then (Fintype.card K1 : ℤ) else 0 := fun y2 =>
      sum_chi_linearMap (bilMap y2)
    simp_rw [h1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- Push forward sum_{y1 : K1} sum_{y2 : K} chi(bil y1 y2) to D1 x P2
  have hpush : (∑ y1 : K1, ∑ y2 : K, chi (bil y1 y2)) =
      (Fintype.card K1 : ℤ) * ((Fintype.card Z0 : ℤ) *
        ∑ d1 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ D1),
        ∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
          chi (dotProduct (Phi A d1 d2) u)) := by
    -- Inner sum over y2 : K grouped by d2 = (L y2).2.2.1 ∈ P2
    have hinner2 : ∀ y1 : K1,
        (∑ y2 : K, chi (bil y1 y2)) =
          (Fintype.card K1 : ℤ) *
            ∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
              chi (dotProduct (Phi A (L y1.1).2.1 d2) u) := by
      intro y1
      have hgrp := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset K))
        (t := (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2))
        (g := fun y2 : K => (L y2.1).2.2.1)
        (f := fun y2 : K => chi (bil y1 y2))
        (fun y2 _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK_P2 y2.1 y2.2⟩)
      rw [← hgrp, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d2 hd2 => ?_)
      have hd2P : d2 ∈ P2 := (Finset.mem_filter.mp hd2).2
      have hconst : ∀ y2 ∈ (Finset.univ : Finset K).filter (fun y2 => (L y2.1).2.2.1 = d2),
          chi (bil y1 y2) = chi (dotProduct (Phi A (L y1.1).2.1 d2) u) := by
        intro y2 hy2
        have heq : (L y2.1).2.2.1 = d2 := (Finset.mem_filter.mp hy2).2
        rw [dotProduct_Phi]
        simp only [bil, heq]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hfib_K d2 hd2P]
    simp_rw [hinner2, ← Finset.mul_sum]
    congr 1
    -- Outer sum over y1 : K1 grouped by d1 = (L y1).2.1 ∈ D1
    have hgrp1 := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset K1))
      (t := (Finset.univ : Finset (Fin m → F2)).filter (· ∈ D1))
      (g := fun y1 : K1 => (L y1.1).2.1)
      (f := fun y1 : K1 => ∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
        chi (dotProduct (Phi A (L y1.1).2.1 d2) u))
      (fun y1 _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK1_D1 y1.1 y1.2⟩)
    rw [← hgrp1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d1 hd1 => ?_)
    have hd1D : d1 ∈ D1 := (Finset.mem_filter.mp hd1).2
    have hconst : ∀ y1 ∈ (Finset.univ : Finset K1).filter (fun y1 => (L y1.1).2.1 = d1),
        (∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
          chi (dotProduct (Phi A (L y1.1).2.1 d2) u)) =
        ∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
          chi (dotProduct (Phi A d1 d2) u) := by
      intro y1 hy1
      have heq : (L y1.1).2.1 = d1 := (Finset.mem_filter.mp hy1).2
      simp only [heq]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hfib_K1 d1 hd1D]
  have hker_eq : (((Finset.univ : Finset K).filter (fun y2 => bilMap y2 = 0)).card : ℤ) =
      (Fintype.card Z0 : ℤ) *
        ∑ d1 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ D1),
        ∑ d2 ∈ (Finset.univ : Finset (Fin m → F2)).filter (· ∈ P2),
          chi (dotProduct (Phi A d1 d2) u) := by
    have h := hker_sum.trans hpush
    exact mul_left_cancel₀ (ne_of_gt hK1_pos) h
  rw [← hker_eq]
  exact hstep2

-- Fiber cardinality lemma for a linear map f : X →ₗ[F2] Y onto range f
lemma card_linear_fiber {X Y : Type*} [AddCommGroup X] [Module F2 X] [Fintype X]
    [AddCommGroup Y] [Module F2 Y]
    (f : X →ₗ[F2] Y) (y : Y) (hy : y ∈ LinearMap.range f) :
    letI : DecidablePred (fun x : X => f x = y) := Classical.decPred _
    letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
    ((Finset.univ : Finset X).filter (fun x => f x = y)).card =
      Fintype.card (LinearMap.ker f) := by
  classical
  rcases hy with ⟨x0, hx0⟩
  letI : Fintype (LinearMap.ker f) := Fintype.ofFinite _
  refine Finset.card_bij
    (fun x hx => (⟨x + x0, by
      have hfx : f x = y := (Finset.mem_filter.mp hx).2
      change f (x + x0) = 0
      rw [map_add, hfx, hx0]
      exact module_F2_add_self y⟩ : LinearMap.ker f))
    (fun _ _ => Finset.mem_univ _)
    (fun _ _ _ _ hab => add_right_cancel (congrArg Subtype.val hab))
    (fun z _ => ⟨z.1 + x0, by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [map_add, show f z.1 = 0 from z.2, zero_add, hx0],
      Subtype.ext (by dsimp; rw [add_assoc, module_F2_add_self, add_zero])⟩)

-- Top-level bilinear polar forms on a submodule K <= Fin t -> F2
def polarQDef {t : ℕ} (M0 : Fin t → Fin t → F2) (K : Submodule F2 (Fin t → F2)) :
    K →ₗ[F2] K →ₗ[F2] F2 :=
  { toFun := fun y =>
      { toFun := fun y' => ∑ p, ∑ q', M0 p q' * (y.1 p * y'.1 q' + y'.1 p * y.1 q')
        map_add' := fun b c => by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q' _ => ?_))
          change M0 p q' * (y.1 p * (b.1 q' + c.1 q') + (b.1 p + c.1 p) * y.1 q') = _
          ring
        map_smul' := fun c b => by
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · simp only [zero_smul, ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul, mul_zero, add_zero, Finset.sum_const_zero, RingHom.id_apply, smul_eq_mul]
          · simp only [one_smul, RingHom.id_apply, smul_eq_mul, one_mul] }
    map_add' := fun a' b' => by
      apply LinearMap.ext; intro y'
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q' _ => ?_))
      change M0 p q' * ((a'.1 p + b'.1 p) * y'.1 q' + y'.1 p * (a'.1 q' + b'.1 q')) = _
      ring
    map_smul' := fun c a' => by
      apply LinearMap.ext; intro y'
      rcases zmod2_eq_zero_or_one c with rfl | rfl
      · change (∑ p, ∑ q', M0 p q' * (((0 : F2) • a').1 p * y'.1 q' + y'.1 p * ((0 : F2) • a').1 q')) =
          (0 : F2) * (∑ p, ∑ q', M0 p q' * (a'.1 p * y'.1 q' + y'.1 p * a'.1 q'))
        simp only [zero_smul, ZeroMemClass.coe_zero, Pi.zero_apply, zero_mul, mul_zero, add_zero,
          Finset.sum_const_zero]
      · change (∑ p, ∑ q', M0 p q' * (((1 : F2) • a').1 p * y'.1 q' + y'.1 p * ((1 : F2) • a').1 q')) =
          (1 : F2) * (∑ p, ∑ q', M0 p q' * (a'.1 p * y'.1 q' + y'.1 p * a'.1 q'))
        simp only [one_smul, one_mul] }

def polarValDef {k m r t : ℕ} (A : Fin m → (Fin k → F2))
    (L : (Fin t → F2) →ₗ[F2] (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (K : Submodule F2 (Fin t → F2)) (s0 : Fin k → F2) :
    K →ₗ[F2] K →ₗ[F2] F2 :=
  { toFun := fun y =>
      { toFun := fun y' =>
          ∑ i : Fin m, dotProduct (A i) s0 *
            ((L y.1).2.1 i * (L y'.1).2.2.1 i + (L y'.1).2.1 i * (L y.1).2.2.1 i)
        map_add' := fun b c => by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have h1 : (L (b + c).1).2.1 i = (L b.1).2.1 i + (L c.1).2.1 i := by
            simp [Submodule.coe_add, map_add]
          have h2 : (L (b + c).1).2.2.1 i = (L b.1).2.2.1 i + (L c.1).2.2.1 i := by
            simp [Submodule.coe_add, map_add]
          rw [h1, h2]; ring
        map_smul' := fun c b => by
          rcases zmod2_eq_zero_or_one c with rfl | rfl
          · change (∑ i : Fin m, dotProduct (A i) s0 *
                ((L y.1).2.1 i * (L ((0 : F2) • b).1).2.2.1 i +
                 (L ((0 : F2) • b).1).2.1 i * (L y.1).2.2.1 i)) =
              (0 : F2) * (∑ i : Fin m, dotProduct (A i) s0 *
                ((L y.1).2.1 i * (L b.1).2.2.1 i + (L b.1).2.1 i * (L y.1).2.2.1 i))
            simp only [zero_smul, ZeroMemClass.coe_zero, map_zero, Prod.fst_zero, Prod.snd_zero,
              Pi.zero_apply, zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
          · change (∑ i : Fin m, dotProduct (A i) s0 *
                ((L y.1).2.1 i * (L ((1 : F2) • b).1).2.2.1 i +
                 (L ((1 : F2) • b).1).2.1 i * (L y.1).2.2.1 i)) =
              (1 : F2) * (∑ i : Fin m, dotProduct (A i) s0 *
                ((L y.1).2.1 i * (L b.1).2.2.1 i + (L b.1).2.1 i * (L y.1).2.2.1 i))
            simp only [one_smul, one_mul] }
    map_add' := fun a' b' => by
      apply LinearMap.ext; intro y'
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have h1 : (L (a' + b').1).2.1 i = (L a'.1).2.1 i + (L b'.1).2.1 i := by
        simp [Submodule.coe_add, map_add]
      have h2 : (L (a' + b').1).2.2.1 i = (L a'.1).2.2.1 i + (L b'.1).2.2.1 i := by
        simp [Submodule.coe_add, map_add]
      rw [h1, h2]; ring
    map_smul' := fun c a' => by
      apply LinearMap.ext; intro y'
      rcases zmod2_eq_zero_or_one c with rfl | rfl
      · change (∑ i : Fin m, dotProduct (A i) s0 *
            ((L ((0 : F2) • a').1).2.1 i * (L y'.1).2.2.1 i +
             (L y'.1).2.1 i * (L ((0 : F2) • a').1).2.2.1 i)) =
          (0 : F2) * (∑ i : Fin m, dotProduct (A i) s0 *
            ((L a'.1).2.1 i * (L y'.1).2.2.1 i + (L y'.1).2.1 i * (L a'.1).2.2.1 i))
        simp only [zero_smul, ZeroMemClass.coe_zero, map_zero, Prod.fst_zero, Prod.snd_zero,
          Pi.zero_apply, zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
      · change (∑ i : Fin m, dotProduct (A i) s0 *
            ((L ((1 : F2) • a').1).2.1 i * (L y'.1).2.2.1 i +
             (L y'.1).2.1 i * (L ((1 : F2) • a').1).2.2.1 i)) =
          (1 : F2) * (∑ i : Fin m, dotProduct (A i) s0 *
            ((L a'.1).2.1 i * (L y'.1).2.2.1 i + (L y'.1).2.1 i * (L a'.1).2.2.1 i))
        simp only [one_smul, one_mul] }

-- Helper for Part 1: exact statement proof
lemma part1_main (k m r j : ℕ) (A : Fin m → (Fin k → F2))
    (L : (Fin (2 * m + r + j) → F2) →ₗ[F2]
      (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
    (hLinj : Function.Injective L) :
    ∃ B : (Fin j → F2) →ₗ[F2] (Fin k → F2),
      Function.Injective B ∧
      (∀ u : Fin j → F2, ∃ x : Fin (2 * m + r + j) → F2, (L x).1 = B u) ∧
      ∀ (h : (Fin k → F2) → F2)
        (a : (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
        (q : (Fin (2 * m + r + j) → F2) → F2),
        (∃ (z : F2) (l : Fin (2 * m + r + j) → F2)
           (M : Fin (2 * m + r + j) → Fin (2 * m + r + j) → F2),
          ∀ x, q x = z + dotProduct l x + ∑ u, ∑ v, M u v * x u * x v) →
        2 * 2 ^ (m + j) *
          (∑ x : Fin (2 * m + r + j) → F2,
            if h (a + L x).1 +
               ∑ i : Fin m, dotProduct (A i) (a + L x).1 * (a + L x).2.1 i * (a + L x).2.2.1 i =
               q x
            then (1 : ℤ) else -1).natAbs ≤
        2 ^ (2 * m + r + j) *
          max (2 ^ (m + j)) (2 * ∑ u : Fin j → F2, 2 ^ (m - wtA A (B u))) := by
  classical
  let E := Fin (2 * m + r + j) → F2
  let S := Fin k → F2
  let D := Fin m → F2
  let Z := Fin r → F2
  let V := S × (D × (D × Z))
  let piS : (Fin (2 * m + r + j) → F2) →ₗ[F2] (Fin k → F2) :=
    (LinearMap.fst F2 (Fin k → F2) ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))).comp L
  let K : Submodule F2 (Fin (2 * m + r + j) → F2) := LinearMap.ker piS
  let I : Submodule F2 (Fin k → F2) := LinearMap.range piS
  have hdim_KI : Module.finrank F2 I + Module.finrank F2 K = 2 * m + r + j := by
    have h := LinearMap.finrank_range_add_finrank_ker piS
    simpa [E] using h
  -- Subspaces K1 <= K (d2 = 0) and Z0 <= K1 (d1 = 0, d2 = 0)
  let piD2K : K →ₗ[F2] (Fin m → F2) :=
    { toFun := fun y => (L y.1).2.2.1
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let K1_in_K : Submodule F2 K := LinearMap.ker piD2K
  let K1 : Submodule F2 (Fin (2 * m + r + j) → F2) := Submodule.map K.subtype K1_in_K
  let P2 : Submodule F2 (Fin m → F2) := LinearMap.range piD2K
  have hK1le : K1 ≤ K := by
    intro x hx; rcases Submodule.mem_map.mp hx with ⟨y, _, rfl⟩; exact y.2
  have hdim_P2K1 : Module.finrank F2 P2 + Module.finrank F2 K1 = Module.finrank F2 K := by
    have h := LinearMap.finrank_range_add_finrank_ker piD2K
    rw [finrank_map_of_inj K.injective_subtype K1_in_K]
    exact h
  let piD1K1 : K1 →ₗ[F2] (Fin m → F2) :=
    { toFun := fun y => (L y.1).2.1
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  let Z0_in_K1 : Submodule F2 K1 := LinearMap.ker piD1K1
  let Z0 : Submodule F2 (Fin (2 * m + r + j) → F2) := Submodule.map K1.subtype Z0_in_K1
  let D1 : Submodule F2 (Fin m → F2) := LinearMap.range piD1K1
  have hZ0le : Z0 ≤ K1 := by
    intro x hx; rcases Submodule.mem_map.mp hx with ⟨y, _, rfl⟩; exact y.2
  have hdim_D1Z0 : Module.finrank F2 D1 + Module.finrank F2 Z0 = Module.finrank F2 K1 := by
    have h := LinearMap.finrank_range_add_finrank_ker piD1K1
    rw [finrank_map_of_inj K1.injective_subtype Z0_in_K1]
    exact h
  -- Z0 embeds injectively into Z (since on Z0, L has s=0, d1=0, d2=0)
  let piZZ0 : Z0 →ₗ[F2] Z :=
    { toFun := fun y => (L y.1).2.2.2
      map_add' := fun a b => by simp
      map_smul' := fun c a => by simp }
  have hpiZZ0_inj : Function.Injective piZZ0 := by
    intro a b hab
    apply Subtype.ext
    apply hLinj
    have haK1 : a.1 ∈ K1 := hZ0le a.2
    have hbK1 : b.1 ∈ K1 := hZ0le b.2
    have haK : a.1 ∈ K := hK1le haK1
    have hbK : b.1 ∈ K := hK1le hbK1
    have haS : (L a.1).1 = 0 := haK
    have hbS : (L b.1).1 = 0 := hbK
    have haD2 : (L a.1).2.2.1 = 0 := by
      rcases Submodule.mem_map.mp haK1 with ⟨y, hy, hya⟩
      rw [← hya]; exact hy
    have hbD2 : (L b.1).2.2.1 = 0 := by
      rcases Submodule.mem_map.mp hbK1 with ⟨y, hy, hyb⟩
      rw [← hyb]; exact hy
    have haD1 : (L a.1).2.1 = 0 := by
      rcases Submodule.mem_map.mp a.2 with ⟨y, hy, hya⟩
      rw [← hya]; exact hy
    have hbD1 : (L b.1).2.1 = 0 := by
      rcases Submodule.mem_map.mp b.2 with ⟨y, hy, hyb⟩
      rw [← hyb]; exact hy
    exact Prod.ext (haS.trans hbS.symm)
      (Prod.ext (haD1.trans hbD1.symm) (Prod.ext (haD2.trans hbD2.symm) hab))
  have hdim_Z0_le : Module.finrank F2 Z0 ≤ r := by
    have h := LinearMap.finrank_le_finrank_of_injective hpiZZ0_inj
    simpa [Z] using h
  have hdim_D1_le : Module.finrank F2 D1 ≤ m := by
    have := Submodule.finrank_le D1; simpa [D] using this
  have hdim_P2_le : Module.finrank F2 P2 ≤ m := by
    have := Submodule.finrank_le P2; simpa [D] using this
  -- Lift D1, P2 to ⊤ and descend I* to Bsub of finrank j
  set c : ℕ := (m - Module.finrank F2 D1) + (m - Module.finrank F2 P2)
  set s : ℕ := r - Module.finrank F2 Z0
  have hdim_I_eq : Module.finrank F2 I = j + c + s := by omega
  have hc_le : c ≤ Module.finrank F2 I := by omega
  rcases solCount_lift_to_top A c D1 P2 I rfl hc_le with ⟨Istar, hIstar_le, hIstar_fr, hsol_le⟩
  have hIstar_js : Module.finrank F2 Istar = j + s := by omega
  rcases exists_subspace_subMass A s j Istar hIstar_js with ⟨Bsub, hBsub_le, hBsub_fr, hmass_le⟩
  -- Build injective B : (Fin j → F2) →ₗ[F2] S with range B = Bsub
  have heB : (Fin j → F2) ≃ₗ[F2] Bsub :=
    LinearEquiv.ofFinrankEq (Fin j → F2) Bsub (by rw [Module.finrank_fin_fun, hBsub_fr])
  let B : (Fin j → F2) →ₗ[F2] S := Bsub.subtype.comp heB.toLinearMap
  have hBinj : Function.Injective B := Bsub.injective_subtype.comp heB.injective
  have hBmem : ∀ u : Fin j → F2, ∃ x : E, (L x).1 = B u := by
    intro u
    have h1 : B u ∈ I := hIstar_le (hBsub_le (heB u).2)
    exact h1
  have hmassB_eq : (∑ u : Fin j → F2, 2 ^ (m - wtA A (B u))) = subMass A Bsub := by
    letI : Fintype Bsub := Fintype.ofFinite Bsub
    unfold subMass
    exact Fintype.sum_equiv heB.toEquiv (fun u => 2 ^ (m - wtA A (B u)))
      (fun y : Bsub => 2 ^ (m - wtA A y.1)) (fun _ => rfl)
  refine ⟨B, hBinj, hBmem, ?_⟩
  -- Now prove the gap bound for arbitrary (h, a, q) with quad t q
  intro h a q hq
  rcases hq with ⟨z0, l0, M0, hqeq⟩
  -- Pick a complement W of K in E via LinearMap.exists_rightInverse or Submodule.exists_isCompl
  rcases Submodule.exists_isCompl K with ⟨W, hKW⟩
  -- Decompose E ≃ W × K
  let eWK : (W × K) ≃ E :=
    { toFun := fun p => p.1.1 + p.2.1
      invFun := fun x =>
        let p := (Submodule.prodEquivOfIsCompl W K hKW.symm).symm x
        (p.1, p.2)
      left_inv := fun p => by
        have h := (Submodule.prodEquivOfIsCompl W K hKW.symm).symm_apply_apply p
        exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
      right_inv := fun x =>
        (Submodule.prodEquivOfIsCompl W K hKW.symm).apply_symm_apply x }
  letI : Fintype W := Fintype.ofFinite W
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype K1 := Fintype.ofFinite K1
  letI : Fintype Z0 := Fintype.ofFinite Z0
  letI : Fintype I := Fintype.ofFinite I
  -- piS maps W bijectively onto I
  have hW_I : Function.Bijective (fun w : W => (⟨(L w.1).1, ⟨w.1, rfl⟩⟩ : I)) := by
    constructor
    · intro w1 w2 hw
      have hdiff : w1.1 - w2.1 ∈ K := by
        change piS (w1.1 - w2.1) = 0
        rw [map_sub]
        have h1 : (L w1.1).1 = (L w2.1).1 := congrArg Subtype.val hw
        exact sub_eq_zero.mpr h1
      have hWmem : w1.1 - w2.1 ∈ W := W.sub_mem w1.2 w2.2
      have hbot : w1.1 - w2.1 ∈ K ⊓ W := ⟨hdiff, hWmem⟩
      rw [hKW.inf_eq_bot, Submodule.mem_bot] at hbot
      exact Subtype.ext (sub_eq_zero.mp hbot)
    · intro u
      rcases u.2 with ⟨x, hx⟩
      have hxKW : x ∈ K ⊔ W := by rw [hKW.sup_eq_top]; trivial
      rcases Submodule.mem_sup.mp hxKW with ⟨y, hyK, w, hwW, rfl⟩
      refine ⟨⟨w, hwW⟩, Subtype.ext ?_⟩
      have hy0 : (L y).1 = 0 := hyK
      have : (L (y + w)).1 = (L w).1 := by simp [map_add, hy0]
      exact this.symm.trans hx
  let eWI : W ≃ I := Equiv.ofBijective _ hW_I
  -- Define fiber function f w y = val h (a + L(w + y)) + q(w + y)
  let valf : V → F2 := fun x =>
    h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2.1 i
  let f : W → K → F2 := fun w y => valf (a + L (w.1 + y.1)) + q (w.1 + y.1)
  -- Express gap sum via fibers over W
  have hgap_sum : (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1) =
      ∑ w : W, ∑ y : K, chi (f w y) := by
    have h1 : (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1) =
        ∑ p : W × K, chi (f p.1 p.2) := by
      refine (Fintype.sum_equiv eWK (fun p => chi (f p.1 p.2))
        (fun x => if valf (a + L x) = q x then (1 : ℤ) else -1) (fun p => ?_)).symm
      exact (chi_eq_ite _ _).symm
    rw [h1, Fintype.sum_prod_type]
  -- Polar form of f w on K
  let polarQ : K →ₗ[F2] K →ₗ[F2] F2 := polarQDef M0 K
  let polarVal : S → K →ₗ[F2] K →ₗ[F2] F2 := fun s0 => polarValDef A L K s0
  have hfw_polar : ∀ (w : W) (y y' : K),
      f w (y + y') + f w y + f w y' + f w 0 =
        polarVal (a.1 + (L w.1).1) y y' + polarQ y y' := by
    intro w y y'
    have hyS : (L y.1).1 = 0 := y.2
    have hy'S : (L y'.1).1 = 0 := y'.2
    have hq_pol : q (w.1 + (y.1 + y'.1)) + q (w.1 + y.1) + q (w.1 + y'.1) + q w.1 =
        polarQ y y' := by
      simp only [hqeq, polarQ, polarQDef, LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Pi.add_apply]
      have hlin : (z0 + ∑ x, l0 x * (w.1 x + (y.1 x + y'.1 x))) +
          (z0 + ∑ x, l0 x * (w.1 x + y.1 x)) +
          (z0 + ∑ x, l0 x * (w.1 x + y'.1 x)) +
          (z0 + ∑ x, l0 x * w.1 x) = 0 := by
        have h1 : z0 + z0 + z0 + z0 = 0 := by
          calc z0 + z0 + z0 + z0 = (z0 + z0) + (z0 + z0) := by ring
            _ = 0 := by rw [zmod2_add_self]
        have h2 : (∑ x, l0 x * (w.1 x + (y.1 x + y'.1 x))) +
            (∑ x, l0 x * (w.1 x + y.1 x)) +
            (∑ x, l0 x * (w.1 x + y'.1 x)) +
            (∑ x, l0 x * w.1 x) = 0 := by
          simp only [← Finset.sum_add_distrib]
          refine Finset.sum_eq_zero (fun x _ => ?_)
          have hw := zmod2_add_self (l0 x * w.1 x)
          have hy := zmod2_add_self (l0 x * y.1 x)
          have hy' := zmod2_add_self (l0 x * y'.1 x)
          calc l0 x * (w.1 x + (y.1 x + y'.1 x)) + l0 x * (w.1 x + y.1 x) +
                l0 x * (w.1 x + y'.1 x) + l0 x * w.1 x
              = (l0 x * w.1 x + l0 x * w.1 x) + (l0 x * w.1 x + l0 x * w.1 x) +
                (l0 x * y.1 x + l0 x * y.1 x) + (l0 x * y'.1 x + l0 x * y'.1 x) := by ring
            _ = 0 := by rw [hw, hy, hy']; ring
        calc _ = (z0 + z0 + z0 + z0) + ((∑ x, l0 x * (w.1 x + (y.1 x + y'.1 x))) +
              (∑ x, l0 x * (w.1 x + y.1 x)) +
              (∑ x, l0 x * (w.1 x + y'.1 x)) +
              (∑ x, l0 x * w.1 x)) := by ring
          _ = 0 := by rw [h1, h2, zero_add]
      have hquad : (∑ u, ∑ v, M0 u v * (w.1 u + (y.1 u + y'.1 u)) * (w.1 v + (y.1 v + y'.1 v))) +
          (∑ u, ∑ v, M0 u v * (w.1 u + y.1 u) * (w.1 v + y.1 v)) +
          (∑ u, ∑ v, M0 u v * (w.1 u + y'.1 u) * (w.1 v + y'.1 v)) +
          (∑ u, ∑ v, M0 u v * w.1 u * w.1 v) =
          ∑ u, ∑ v, M0 u v * (y.1 u * y'.1 v + y'.1 u * y.1 v) := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => ?_))
        have hww := zmod2_add_self (M0 u v * w.1 u * w.1 v)
        have hwy := zmod2_add_self (M0 u v * w.1 u * y.1 v)
        have hwy' := zmod2_add_self (M0 u v * w.1 u * y'.1 v)
        have hyw := zmod2_add_self (M0 u v * y.1 u * w.1 v)
        have hy'w := zmod2_add_self (M0 u v * y'.1 u * w.1 v)
        have hyy := zmod2_add_self (M0 u v * y.1 u * y.1 v)
        have hy'y' := zmod2_add_self (M0 u v * y'.1 u * y'.1 v)
        calc M0 u v * (w.1 u + (y.1 u + y'.1 u)) * (w.1 v + (y.1 v + y'.1 v)) +
              M0 u v * (w.1 u + y.1 u) * (w.1 v + y.1 v) +
              M0 u v * (w.1 u + y'.1 u) * (w.1 v + y'.1 v) +
              M0 u v * w.1 u * w.1 v
            = M0 u v * (y.1 u * y'.1 v + y'.1 u * y.1 v) +
              (M0 u v * w.1 u * w.1 v + M0 u v * w.1 u * w.1 v) +
              (M0 u v * w.1 u * w.1 v + M0 u v * w.1 u * w.1 v) +
              (M0 u v * w.1 u * y.1 v + M0 u v * w.1 u * y.1 v) +
              (M0 u v * w.1 u * y'.1 v + M0 u v * w.1 u * y'.1 v) +
              (M0 u v * y.1 u * w.1 v + M0 u v * y.1 u * w.1 v) +
              (M0 u v * y'.1 u * w.1 v + M0 u v * y'.1 u * w.1 v) +
              (M0 u v * y.1 u * y.1 v + M0 u v * y.1 u * y.1 v) +
              (M0 u v * y'.1 u * y'.1 v + M0 u v * y'.1 u * y'.1 v) := by ring
          _ = M0 u v * (y.1 u * y'.1 v + y'.1 u * y.1 v) := by
              rw [hww, hwy, hwy', hyw, hy'w, hyy, hy'y']; ring
      calc _ = ((z0 + ∑ x, l0 x * (w.1 x + (y.1 x + y'.1 x))) +
            (z0 + ∑ x, l0 x * (w.1 x + y.1 x)) +
            (z0 + ∑ x, l0 x * (w.1 x + y'.1 x)) +
            (z0 + ∑ x, l0 x * w.1 x)) +
            ((∑ u, ∑ v, M0 u v * (w.1 u + (y.1 u + y'.1 u)) * (w.1 v + (y.1 v + y'.1 v))) +
            (∑ u, ∑ v, M0 u v * (w.1 u + y.1 u) * (w.1 v + y.1 v)) +
            (∑ u, ∑ v, M0 u v * (w.1 u + y'.1 u) * (w.1 v + y'.1 v)) +
            (∑ u, ∑ v, M0 u v * w.1 u * w.1 v)) := by ring
        _ = _ := by rw [hlin, zero_add, hquad]
    have hval_pol : valf (a + L (w.1 + (y.1 + y'.1))) + valf (a + L (w.1 + y.1)) +
        valf (a + L (w.1 + y'.1)) + valf (a + L w.1) =
        polarVal (a.1 + (L w.1).1) y y' := by
      simp only [valf, polarVal, polarValDef, LinearMap.coe_mk, AddHom.coe_mk, map_add, Prod.fst_add,
        Prod.snd_add, hyS, hy'S, add_zero]
      set s0 := a.1 + (L w.1).1
      set p1 := a.2.1 + (L w.1).2.1
      set p2 := a.2.2.1 + (L w.1).2.2.1
      have hpa : ∀ (u v : D) (i : Fin m), (u + v) i = u i + v i := fun _ _ _ => rfl
      simp only [hpa, add_assoc]
      have hh0 : h s0 + h s0 + h s0 + h s0 = 0 := by
        calc h s0 + h s0 + h s0 + h s0 = (h s0 + h s0) + (h s0 + h s0) := by ring
          _ = 0 := by rw [zmod2_add_self]
      have hsum : (∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + ((L y.1).2.1 i + (L y'.1).2.1 i)) *
            (p2 i + ((L y.1).2.2.1 i + (L y'.1).2.2.1 i))) +
          (∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + (L y.1).2.1 i) * (p2 i + (L y.1).2.2.1 i)) +
          (∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + (L y'.1).2.1 i) * (p2 i + (L y'.1).2.2.1 i)) +
          (∑ i : Fin m, dotProduct (A i) s0 * p1 i * p2 i) =
          ∑ i : Fin m, dotProduct (A i) s0 *
            ((L y.1).2.1 i * (L y'.1).2.2.1 i + (L y'.1).2.1 i * (L y.1).2.2.1 i) := by
        simp only [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        set c := dotProduct (A i) s0
        set x1 := (L y.1).2.1 i
        set x2 := (L y.1).2.2.1 i
        set z1 := (L y'.1).2.1 i
        set z2 := (L y'.1).2.2.1 i
        have h1 := zmod2_add_self (c * p1 i * p2 i)
        have h2 := zmod2_add_self (c * p1 i * x2)
        have h3 := zmod2_add_self (c * p1 i * z2)
        have h4 := zmod2_add_self (c * x1 * p2 i)
        have h5 := zmod2_add_self (c * z1 * p2 i)
        have h6 := zmod2_add_self (c * x1 * x2)
        have h7 := zmod2_add_self (c * z1 * z2)
        calc c * (p1 i + (x1 + z1)) * (p2 i + (x2 + z2)) +
              c * (p1 i + x1) * (p2 i + x2) +
              c * (p1 i + z1) * (p2 i + z2) +
              c * p1 i * p2 i
            = c * (x1 * z2 + z1 * x2) +
              (c * p1 i * p2 i + c * p1 i * p2 i) +
              (c * p1 i * p2 i + c * p1 i * p2 i) +
              (c * p1 i * x2 + c * p1 i * x2) +
              (c * p1 i * z2 + c * p1 i * z2) +
              (c * x1 * p2 i + c * x1 * p2 i) +
              (c * z1 * p2 i + c * z1 * p2 i) +
              (c * x1 * x2 + c * x1 * x2) +
              (c * z1 * z2 + c * z1 * z2) := by ring
          _ = c * (x1 * z2 + z1 * x2) := by rw [h1, h2, h3, h4, h5, h6, h7]; ring
      have hrew : (h s0 + ∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + ((L y.1).2.1 i + (L y'.1).2.1 i)) *
            (p2 i + ((L y.1).2.2.1 i + (L y'.1).2.2.1 i))) +
          (h s0 + ∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + (L y.1).2.1 i) * (p2 i + (L y.1).2.2.1 i)) +
          (h s0 + ∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + (L y'.1).2.1 i) * (p2 i + (L y'.1).2.2.1 i)) +
          (h s0 + ∑ i : Fin m, dotProduct (A i) s0 * p1 i * p2 i) =
          (h s0 + h s0 + h s0 + h s0) +
          ((∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + ((L y.1).2.1 i + (L y'.1).2.1 i)) *
            (p2 i + ((L y.1).2.2.1 i + (L y'.1).2.2.1 i))) +
          (∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + (L y.1).2.1 i) * (p2 i + (L y.1).2.2.1 i)) +
          (∑ i : Fin m, dotProduct (A i) s0 *
            (p1 i + (L y'.1).2.1 i) * (p2 i + (L y'.1).2.2.1 i)) +
          (∑ i : Fin m, dotProduct (A i) s0 * p1 i * p2 i)) := by ring
      simpa only [p1, p2, hpa, add_assoc] using (hrew.trans (by rw [hh0, zero_add, hsum]))
    simp only [f, Submodule.coe_add, ZeroMemClass.coe_zero, add_zero]
    calc (valf (a + L (w.1 + (y.1 + y'.1))) + q (w.1 + (y.1 + y'.1))) +
          (valf (a + L (w.1 + y.1)) + q (w.1 + y.1)) +
          (valf (a + L (w.1 + y'.1)) + q (w.1 + y'.1)) +
          (valf (a + L w.1) + q w.1)
        = (valf (a + L (w.1 + (y.1 + y'.1))) + valf (a + L (w.1 + y.1)) +
            valf (a + L (w.1 + y'.1)) + valf (a + L w.1)) +
          (q (w.1 + (y.1 + y'.1)) + q (w.1 + y.1) + q (w.1 + y'.1) + q w.1) := by ring
      _ = polarVal (a.1 + (L w.1).1) y y' + polarQ y y' := by rw [hval_pol, hq_pol]
  -- Every f w is quadratic on K
  have hfw_quad : ∀ w : W, IsQuad (f w) := by
    intro w
    refine ⟨polarVal (a.1 + (L w.1).1) + polarQ, ?_, fun y y' => hfw_polar w y y'⟩
    intro y
    simp only [LinearMap.add_apply, polarVal, polarValDef, polarQ, polarQDef, LinearMap.coe_mk, AddHom.coe_mk]
    have h1 : (∑ i : Fin m, dotProduct (A i) (a.1 + (L w.1).1) *
        ((L y.1).2.1 i * (L y.1).2.2.1 i + (L y.1).2.1 i * (L y.1).2.2.1 i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [zmod2_add_self, mul_zero])
    have h2 : (∑ p, ∑ q', M0 p q' * (y.1 p * y.1 q' + y.1 p * y.1 q')) = 0 :=
      Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun q' _ => by rw [zmod2_add_self, mul_zero]))
    rw [h1, h2, zero_add]
  -- Split into Branch 1 (no w0 makes f w0 constant) and Branch 2 (some w0 makes f w0 constant)
  by_cases hex : ∃ w0 : W, ∀ y : K, f w0 y = f w0 0
  · -- Branch 2: exists w0 with f w0 constant on K
    rcases hex with ⟨w0, hw0⟩
    -- Deduce polarQ y y' = polarVal (a.1 + (L w0.1).1) y y'
    have hpolarQ_eq : ∀ y y' : K, polarQ y y' = polarVal (a.1 + (L w0.1).1) y y' := by
      intro y y'
      have h0 : f w0 (y + y') + f w0 y + f w0 y' + f w0 0 = 0 := by
        rw [hw0 (y + y'), hw0 y, hw0 y']
        calc f w0 0 + f w0 0 + f w0 0 + f w0 0
            = (f w0 0 + f w0 0) + (f w0 0 + f w0 0) := by ring
          _ = 0 := by rw [zmod2_add_self]
      rw [hfw_polar w0 y y'] at h0
      have h2 := congrArg (· + polarVal (a.1 + (L w0.1).1) y y') h0
      rw [zero_add] at h2
      rw [← h2]
      calc polarQ y y' = (polarVal (a.1 + (L w0.1).1) y y' + polarVal (a.1 + (L w0.1).1) y y') +
            polarQ y y' := by rw [zmod2_add_self, zero_add]
        _ = polarVal (a.1 + (L w0.1).1) y y' + polarQ y y' +
            polarVal (a.1 + (L w0.1).1) y y' := by ring
    -- So for every w : W, polar(f w) = polarVal ((L (w + w0)).1)
    have hfw_polar2 : ∀ (w : W) (y y' : K),
        f w (y + y') + f w y + f w y' + f w 0 =
          ∑ i : Fin m, dotProduct (A i) ((L w.1).1 + (L w0.1).1) *
            ((L y.1).2.1 i * (L y'.1).2.2.1 i + (L y'.1).2.1 i * (L y.1).2.2.1 i) := by
      intro w y y'
      rw [hfw_polar w y y', hpolarQ_eq y y']
      simp only [polarVal, polarValDef, LinearMap.coe_mk, AddHom.coe_mk, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hdot : dotProduct (A i) (a.1 + (L w.1).1) + dotProduct (A i) (a.1 + (L w0.1).1) =
          dotProduct (A i) ((L w.1).1 + (L w0.1).1) := by
        rw [← dotProduct_add]
        congr 1
        ext idx
        simp only [Pi.add_apply]
        calc a.1 idx + (L w.1).1 idx + (a.1 idx + (L w0.1).1 idx)
            = (a.1 idx + a.1 idx) + ((L w.1).1 idx + (L w0.1).1 idx) := by ring
          _ = (L w.1).1 idx + (L w0.1).1 idx := by rw [zmod2_add_self, zero_add]
      rw [← add_mul, hdot]
    -- Fiber cardinality hypotheses for fiber_abs_le_solCount
    have hK1_d2 : ∀ y ∈ K1, (L y).2.2.1 = 0 := by
      intro y hy; rcases Submodule.mem_map.mp hy with ⟨z, hz, rfl⟩; exact hz
    have hK_P2 : ∀ y ∈ K, (L y).2.2.1 ∈ P2 := fun y hy => ⟨⟨y, hy⟩, rfl⟩
    have hK1_D1 : ∀ y ∈ K1, (L y).2.1 ∈ D1 := fun y hy => ⟨⟨y, hy⟩, rfl⟩
    have hfib_K : ∀ d2 ∈ P2,
        ((Finset.univ : Finset K).filter (fun y => (L y.1).2.2.1 = d2)).card = Fintype.card K1 := by
      intro d2 hd2
      have h1 := card_linear_fiber piD2K d2 hd2
      letI : Fintype (LinearMap.ker piD2K) := Fintype.ofFinite _
      have hcard_eq : Fintype.card (LinearMap.ker piD2K) = Fintype.card K1 := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          card_submodule_F2 (LinearMap.ker piD2K), card_submodule_F2 K1,
          finrank_map_of_inj K.injective_subtype K1_in_K]
      rw [← h1.trans hcard_eq]
      congr 1; ext y; simp [piD2K]
    have hfib_K1 : ∀ d1 ∈ D1,
        ((Finset.univ : Finset K1).filter (fun y => (L y.1).2.1 = d1)).card = Fintype.card Z0 := by
      intro d1 hd1
      have h1 := card_linear_fiber piD1K1 d1 hd1
      letI : Fintype (LinearMap.ker piD1K1) := Fintype.ofFinite _
      have hcard_eq : Fintype.card (LinearMap.ker piD1K1) = Fintype.card Z0 := by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
          card_submodule_F2 (LinearMap.ker piD1K1), card_submodule_F2 Z0,
          finrank_map_of_inj K1.injective_subtype Z0_in_K1]
      rw [← h1.trans hcard_eq]
      congr 1; ext y; simp [piD1K1]
    -- Bound gap <= |Z0| * |I| * solCount A D1 P2 I
    have hgap_le_Z : ((∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs : ℤ) ≤
        (Fintype.card Z0 : ℤ) * (Fintype.card I : ℤ) * (solCount A D1 P2 I : ℤ) := by
      rw [hgap_sum, Int.natCast_natAbs]
      calc |∑ w : W, ∑ y : K, chi (f w y)|
          ≤ ∑ w : W, |∑ y : K, chi (f w y)| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ w : W, ((∑ y : K, chi (f w y)).natAbs : ℤ) := by
            refine Finset.sum_congr rfl (fun w _ => (Int.natCast_natAbs _).symm)
        _ ≤ ∑ w : W, (Fintype.card Z0 : ℤ) *
              ∑ d1 ∈ (Finset.univ : Finset D).filter (· ∈ D1),
              ∑ d2 ∈ (Finset.univ : Finset D).filter (· ∈ P2),
                chi (dotProduct (Phi A d1 d2) ((L w.1).1 + (L w0.1).1)) := by
            refine Finset.sum_le_sum (fun w _ => ?_)
            exact fiber_abs_le_solCount A L K K1 Z0 D1 P2 hK1le hZ0le
              (fun y hy => hy) hK1_d2 hK_P2 hK1_D1 hfib_K hfib_K1
              ((L w.1).1 + (L w0.1).1) (f w) (hfw_polar2 w)
        _ = (Fintype.card Z0 : ℤ) *
              ∑ u : I, ∑ d1 ∈ (Finset.univ : Finset D).filter (· ∈ D1),
              ∑ d2 ∈ (Finset.univ : Finset D).filter (· ∈ P2),
                chi (dotProduct (Phi A d1 d2) u.1) := by
            rw [← Finset.mul_sum]
            congr 1
            let eShift : W ≃ I := eWI.trans (Equiv.addRight (eWI w0))
            refine Fintype.sum_equiv eShift _ _ (fun w => rfl)
        _ = (Fintype.card Z0 : ℤ) * (Fintype.card I : ℤ) * (solCount A D1 P2 I : ℤ) := by
            rw [mul_assoc]
            congr 1
            calc (∑ u : I, ∑ d1 ∈ (Finset.univ : Finset D).filter (· ∈ D1),
                  ∑ d2 ∈ (Finset.univ : Finset D).filter (· ∈ P2),
                    chi (dotProduct (Phi A d1 d2) u.1))
                = ∑ d1 ∈ (Finset.univ : Finset D).filter (· ∈ D1),
                  ∑ d2 ∈ (Finset.univ : Finset D).filter (· ∈ P2),
                  ∑ u : I, chi (dotProduct (Phi A d1 d2) u.1) := by
                  rw [Finset.sum_comm]
                  refine Finset.sum_congr rfl (fun d1 _ => Finset.sum_comm)
              _ = ∑ p ∈ ((Finset.univ : Finset D).filter (· ∈ D1)) ×ˢ
                    ((Finset.univ : Finset D).filter (· ∈ P2)),
                  ∑ u : I, chi (dotProduct (Phi A p.1 p.2) u.1) := by
                  rw [Finset.sum_product]
              _ = ∑ p ∈ ((Finset.univ : Finset D).filter (· ∈ D1)) ×ˢ
                    ((Finset.univ : Finset D).filter (· ∈ P2)),
                  if (∀ u ∈ I, dotProduct (Phi A p.1 p.2) u = 0) then (Fintype.card I : ℤ) else 0 := by
                  refine Finset.sum_congr rfl (fun p _ => ?_)
                  let φ : (Fin k → F2) →ₗ[F2] F2 :=
                    { toFun := fun u => dotProduct (Phi A p.1 p.2) u
                      map_add' := fun x y => dotProduct_add (Phi A p.1 p.2) x y
                      map_smul' := fun c x => dotProduct_smul c (Phi A p.1 p.2) x }
                  exact sum_chi_linearMap_sub I φ
              _ = (Fintype.card I : ℤ) * (solCount A D1 P2 I : ℤ) := by
                  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
                  congr 2
                  unfold solCount
                  congr 1
                  ext p
                  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
                    and_assoc]
    have hgap_nat : (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs ≤
        2 ^ Module.finrank F2 Z0 * 2 ^ Module.finrank F2 I * solCount A D1 P2 I := by
      have hcardZ0 : Fintype.card Z0 = 2 ^ Module.finrank F2 Z0 := by
        rw [← Nat.card_eq_fintype_card]; exact card_submodule_F2 Z0
      have hcardI : Fintype.card I = 2 ^ Module.finrank F2 I := by
        rw [← Nat.card_eq_fintype_card]; exact card_submodule_F2 I
      rw [hcardZ0, hcardI] at hgap_le_Z
      exact_mod_cast hgap_le_Z
    -- Final Nat arithmetic combining hgap_nat, hsol_le, subMass_eq_solCount_top, hmass_le
    set gapN := (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs
    have h1 : 2 ^ c * 2 ^ (m + j) * gapN ≤
        2 ^ c * (2 ^ (m + r + j) * 2 ^ j * solCount A ⊤ ⊤ Istar) := by
      have hexp : Module.finrank F2 Z0 + Module.finrank F2 I + (m + j) =
          c + (m + r + j + j) := by omega
      calc 2 ^ c * 2 ^ (m + j) * gapN
          ≤ 2 ^ c * 2 ^ (m + j) *
              (2 ^ Module.finrank F2 Z0 * 2 ^ Module.finrank F2 I * solCount A D1 P2 I) :=
            Nat.mul_le_mul_left _ hgap_nat
        _ = 2 ^ (Module.finrank F2 Z0 + Module.finrank F2 I + (m + j)) *
              (2 ^ c * solCount A D1 P2 I) := by
            simp only [pow_add]; ring
        _ ≤ 2 ^ (Module.finrank F2 Z0 + Module.finrank F2 I + (m + j)) *
              solCount A ⊤ ⊤ Istar := Nat.mul_le_mul_left _ hsol_le
        _ = 2 ^ (c + (m + r + j + j)) * solCount A ⊤ ⊤ Istar := by rw [hexp]
        _ = 2 ^ c * (2 ^ (m + r + j) * 2 ^ j * solCount A ⊤ ⊤ Istar) := by
            simp only [pow_add]; ring
    have h2 : 2 ^ (m + j) * gapN ≤ 2 ^ (m + r + j) * 2 ^ j * solCount A ⊤ ⊤ Istar :=
      Nat.le_of_mul_le_mul_left (by simpa [mul_assoc] using h1) (Nat.two_pow_pos c)
    have hIstar_top := subMass_eq_solCount_top A Istar
    have hIstar_fr2 : Module.finrank F2 Istar = j + s := by omega
    rw [hIstar_fr2] at hIstar_top
    have h3 : 2 ^ s * (2 ^ (m + j) * gapN) ≤ 2 ^ s * (2 ^ (2 * m + r + j) * subMass A Bsub) := by
      calc 2 ^ s * (2 ^ (m + j) * gapN)
          ≤ 2 ^ s * (2 ^ (m + r + j) * 2 ^ j * solCount A ⊤ ⊤ Istar) :=
            Nat.mul_le_mul_left _ h2
        _ = 2 ^ (m + r + j) * (2 ^ (j + s) * solCount A ⊤ ⊤ Istar) := by
            simp only [pow_add]; ring
        _ = 2 ^ (m + r + j) * (2 ^ m * subMass A Istar) := by rw [← hIstar_top]
        _ = 2 ^ (2 * m + r + j) * subMass A Istar := by
            have : m + r + j + m = 2 * m + r + j := by omega
            rw [← mul_assoc, ← pow_add, this]
        _ ≤ 2 ^ (2 * m + r + j) * (2 ^ s * subMass A Bsub) :=
            Nat.mul_le_mul_left _ hmass_le
        _ = 2 ^ s * (2 ^ (2 * m + r + j) * subMass A Bsub) := by ring
    have h4 : 2 ^ (m + j) * gapN ≤ 2 ^ (2 * m + r + j) * subMass A Bsub :=
      Nat.le_of_mul_le_mul_left h3 (Nat.two_pow_pos s)
    rw [hmassB_eq]
    calc 2 * 2 ^ (m + j) * gapN
        = 2 * (2 ^ (m + j) * gapN) := by ring
      _ ≤ 2 * (2 ^ (2 * m + r + j) * subMass A Bsub) := Nat.mul_le_mul_left 2 h4
      _ = 2 ^ (2 * m + r + j) * (2 * subMass A Bsub) := by ring
      _ ≤ 2 ^ (2 * m + r + j) * max (2 ^ (m + j)) (2 * subMass A Bsub) :=
          Nat.mul_le_mul_left _ (le_max_right _ _)
  · -- Branch 1: no w0 makes f w0 constant on K; so every fiber has 2 * |S_w| <= |K|
    push_neg at hex
    have hfib_half : ∀ w : W, 2 * (∑ y : K, chi (f w y)).natAbs ≤ Fintype.card K := by
      intro w
      rcases sum_chi_quad_le_half_or_eq (hfw_quad w) with hconst | hle
      · rcases hex w with ⟨y, hy⟩
        exact False.elim (hy (hconst y))
      · exact hle
    have h2gap_Z : 2 * ((∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs : ℤ) ≤
        (Fintype.card W : ℤ) * (Fintype.card K : ℤ) := by
      rw [hgap_sum, Int.natCast_natAbs]
      calc 2 * |∑ w : W, ∑ y : K, chi (f w y)|
          ≤ 2 * ∑ w : W, |∑ y : K, chi (f w y)| := by
            exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
        _ = ∑ w : W, (2 * ((∑ y : K, chi (f w y)).natAbs : ℤ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun w _ => by rw [Int.natCast_natAbs])
        _ ≤ ∑ _w : W, (Fintype.card K : ℤ) := by
            refine Finset.sum_le_sum (fun w _ => ?_)
            exact_mod_cast hfib_half w
        _ = (Fintype.card W : ℤ) * (Fintype.card K : ℤ) := by simp
    have hcardWK : Fintype.card W * Fintype.card K = 2 ^ (2 * m + r + j) := by
      calc Fintype.card W * Fintype.card K
          = Fintype.card (W × K) := (Fintype.card_prod W K).symm
        _ = Fintype.card E := Fintype.card_congr eWK
        _ = 2 ^ (2 * m + r + j) := card_fin_F2 _
    have h2gap : 2 * (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs ≤
        2 ^ (2 * m + r + j) := by
      rw [← hcardWK]
      exact_mod_cast h2gap_Z
    calc 2 * 2 ^ (m + j) *
          (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs
        = 2 ^ (m + j) *
          (2 * (∑ x : E, if valf (a + L x) = q x then (1 : ℤ) else -1).natAbs) := by ring
      _ ≤ 2 ^ (m + j) * 2 ^ (2 * m + r + j) := Nat.mul_le_mul_left _ h2gap
      _ = 2 ^ (2 * m + r + j) * 2 ^ (m + j) := by ring
      _ ≤ 2 ^ (2 * m + r + j) *
          max (2 ^ (m + j)) (2 * ∑ u : Fin j → F2, 2 ^ (m - wtA A (B u))) :=
          Nat.mul_le_mul_left _ (le_max_left _ _)

-- Helper for Part 2: explicit construction of (L, q) achieving equality
lemma part2_main (k m r j : ℕ) (A : Fin m → (Fin k → F2))
    (B : (Fin j → F2) →ₗ[F2] (Fin k → F2)) (h : (Fin k → F2) → F2)
    (hBinj : Function.Injective B)
    (hquad : ∃ (z : F2) (l : Fin j → F2) (M : Fin j → Fin j → F2),
      ∀ u : Fin j → F2, h (B u) = z + dotProduct l u + ∑ p, ∑ q', M p q' * u p * u q') :
    ∃ (L : (Fin (2 * m + r + j) → F2) →ₗ[F2]
        (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2))))
      (q : (Fin (2 * m + r + j) → F2) → F2),
      Function.Injective L ∧
      (∃ (z : F2) (l : Fin (2 * m + r + j) → F2)
         (M : Fin (2 * m + r + j) → Fin (2 * m + r + j) → F2),
        ∀ x, q x = z + dotProduct l x + ∑ u, ∑ v, M u v * x u * x v) ∧
      2 ^ (m + j) *
        (∑ x : Fin (2 * m + r + j) → F2,
          if h ((0 : (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))) + L x).1 +
             ∑ i : Fin m,
               dotProduct (A i) ((0 : (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))) + L x).1 *
               ((0 : (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))) + L x).2.1 i *
               ((0 : (Fin k → F2) × ((Fin m → F2) × ((Fin m → F2) × (Fin r → F2)))) + L x).2.2.1 i =
             q x
          then (1 : ℤ) else -1).natAbs =
      2 ^ (2 * m + r + j) * ∑ u : Fin j → F2, 2 ^ (m - wtA A (B u)) := by
  classical
  let E := Fin (2 * m + r + j) → F2
  let D := Fin m → F2
  let Z := Fin r → F2
  let J := Fin j → F2
  let xD1 : E →ₗ[F2] D :=
    { toFun := fun x i => x ⟨i.1, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let xD2 : E →ₗ[F2] D :=
    { toFun := fun x i => x ⟨m + i.1, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let xZ : E →ₗ[F2] Z :=
    { toFun := fun x i => x ⟨2 * m + i.1, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let xJ : E →ₗ[F2] J :=
    { toFun := fun x i => x ⟨2 * m + r + i.1, by omega⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let L : E →ₗ[F2] (Fin k → F2) × (D × (D × Z)) :=
    { toFun := fun x => (B (xJ x), (xD1 x, (xD2 x, xZ x)))
      map_add' := fun a b => by
        simp only [map_add]; rfl
      map_smul' := fun c a => by
        simp only [map_smul]; rfl }
  let eSplit : E ≃ (D × D × Z × J) :=
    { toFun := fun x => (xD1 x, xD2 x, xZ x, xJ x)
      invFun := fun p idx =>
        if h1 : idx.1 < m then p.1 ⟨idx.1, h1⟩
        else if h2 : idx.1 < 2 * m then p.2.1 ⟨idx.1 - m, by omega⟩
        else if h3 : idx.1 < 2 * m + r then p.2.2.1 ⟨idx.1 - 2 * m, by omega⟩
        else p.2.2.2 ⟨idx.1 - (2 * m + r), by omega⟩
      left_inv := fun x => by
        ext idx
        by_cases h1 : idx.1 < m
        · simp [h1, xD1]
        · by_cases h2 : idx.1 < 2 * m
          · have : m + (idx.1 - m) = idx.1 := by omega
            simp [h1, h2, xD2, this]
          · by_cases h3 : idx.1 < 2 * m + r
            · have : 2 * m + (idx.1 - 2 * m) = idx.1 := by omega
              simp [h1, h2, h3, xZ, this]
            · have : 2 * m + r + (idx.1 - (2 * m + r)) = idx.1 := by omega
              simp [h1, h2, h3, xJ, this]
      right_inv := fun ⟨d1, d2, z, u⟩ => by
        refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
        · ext i; simp [xD1, i.2]
        · ext i
          have h1 : ¬ m + i.1 < m := by omega
          have h2 : m + i.1 < 2 * m := by omega
          have h3 : m + i.1 - m = i.1 := by omega
          simp [xD2, h1, h2, h3]
        · ext i
          have h1 : ¬ 2 * m + i.1 < m := by omega
          have h2 : ¬ 2 * m + i.1 < 2 * m := by omega
          have h3 : 2 * m + i.1 < 2 * m + r := by omega
          have h4 : 2 * m + i.1 - 2 * m = i.1 := by omega
          simp [xZ, h1, h2, h3, h4]
        · ext i
          have h1 : ¬ 2 * m + r + i.1 < m := by omega
          have h2 : ¬ 2 * m + r + i.1 < 2 * m := by omega
          have h3 : ¬ 2 * m + r + i.1 < 2 * m + r := by omega
          have h4 : 2 * m + r + i.1 - (2 * m + r) = i.1 := by omega
          simp [xJ, h1, h2, h3, h4] }
  have hLinj : Function.Injective L := by
    intro a b hab
    have hB : B (xJ a) = B (xJ b) := congrArg Prod.fst hab
    have h1 : xD1 a = xD1 b := congrArg (fun p => p.2.1) hab
    have h2 : xD2 a = xD2 b := congrArg (fun p => p.2.2.1) hab
    have h3 : xZ a = xZ b := congrArg (fun p => p.2.2.2) hab
    have h4 : xJ a = xJ b := hBinj hB
    exact eSplit.injective (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))
  let q : E → F2 := fun x => h (B (xJ x))
  rcases hquad with ⟨z0, l0, M0, hq0⟩
  have hq_quad : ∃ (z : F2) (l : E) (M : Fin (2 * m + r + j) → Fin (2 * m + r + j) → F2),
      ∀ x, q x = z + dotProduct l x + ∑ u, ∑ v, M u v * x u * x v := by
    let l1 : E := fun idx =>
      if hge : 2 * m + r ≤ idx.1 then l0 ⟨idx.1 - (2 * m + r), by omega⟩ else 0
    let M1 : Fin (2 * m + r + j) → Fin (2 * m + r + j) → F2 := fun u v =>
      if hu : 2 * m + r ≤ u.1 then
        if hv : 2 * m + r ≤ v.1 then
          M0 ⟨u.1 - (2 * m + r), by omega⟩ ⟨v.1 - (2 * m + r), by omega⟩
        else 0
      else 0
    refine ⟨z0, l1, M1, fun x => ?_⟩
    change h (B (xJ x)) = _
    rw [hq0 (xJ x)]
    congr 1
    · congr 1
      simp only [dotProduct, l1]
      symm
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image
        (fun i : Fin j => (⟨2 * m + r + i.1, by omega⟩ : Fin (2 * m + r + j)))))]
      · rw [Finset.sum_image (fun a _ b _ hab => Fin.ext (by
          have := congrArg Fin.val hab; dsimp at this; omega))]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hge : 2 * m + r ≤ 2 * m + r + i.1 := by omega
        have hsub : 2 * m + r + i.1 - (2 * m + r) = i.1 := by omega
        simp [hge, hsub, xJ]
      · intro idx _ hnot
        by_cases hge : 2 * m + r ≤ idx.1
        · exfalso; apply hnot
          refine Finset.mem_image.mpr ⟨⟨idx.1 - (2 * m + r), by omega⟩, Finset.mem_univ _, ?_⟩
          exact Fin.ext (by dsimp; omega)
        · simp [hge]
    · symm
      let emb : Fin j → Fin (2 * m + r + j) := fun i => ⟨2 * m + r + i.1, by omega⟩
      have hemb_inj : Function.Injective emb := fun a b hab =>
        Fin.ext (by have := congrArg Fin.val hab; dsimp [emb] at this; omega)
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))]
      · rw [Finset.sum_image (fun a _ b _ hab => hemb_inj hab)]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image emb))]
        · rw [Finset.sum_image (fun a _ b _ hab => hemb_inj hab)]
          refine Finset.sum_congr rfl (fun q' _ => ?_)
          have hp : 2 * m + r ≤ (emb p).1 := by dsimp [emb]; omega
          have hq' : 2 * m + r ≤ (emb q').1 := by dsimp [emb]; omega
          have hps : (emb p).1 - (2 * m + r) = p.1 := by dsimp [emb]; omega
          have hqs : (emb q').1 - (2 * m + r) = q'.1 := by dsimp [emb]; omega
          simp [M1, hp, hq', hps, hqs, emb, xJ]
        · intro v _ hnot
          by_cases hv : 2 * m + r ≤ v.1
          · exfalso; apply hnot
            refine Finset.mem_image.mpr ⟨⟨v.1 - (2 * m + r), by omega⟩, Finset.mem_univ _, ?_⟩
            exact Fin.ext (by dsimp [emb]; omega)
          · simp [M1, hv]
      · intro u _ hnot
        refine Finset.sum_eq_zero (fun v _ => ?_)
        by_cases hu : 2 * m + r ≤ u.1
        · exfalso; apply hnot
          refine Finset.mem_image.mpr ⟨⟨u.1 - (2 * m + r), by omega⟩, Finset.mem_univ _, ?_⟩
          exact Fin.ext (by dsimp [emb]; omega)
        · simp [M1, hu]
  refine ⟨L, q, hLinj, hq_quad, ?_⟩
  -- Evaluate the exact sum over E
  have hsum_val : (∑ x : E,
      if h ((0 : (Fin k → F2) × (D × (D × Z))) + L x).1 +
         ∑ i : Fin m,
           dotProduct (A i) ((0 : (Fin k → F2) × (D × (D × Z))) + L x).1 *
           ((0 : (Fin k → F2) × (D × (D × Z))) + L x).2.1 i *
           ((0 : (Fin k → F2) × (D × (D × Z))) + L x).2.2.1 i = q x
      then (1 : ℤ) else -1) =
      ((2 ^ (m + r) * ∑ u : J, 2 ^ (m - wtA A (B u)) : ℕ) : ℤ) := by
    have hterm : ∀ x : E,
        (if h ((0 : (Fin k → F2) × (D × (D × Z))) + L x).1 +
            ∑ i : Fin m,
              dotProduct (A i) ((0 : (Fin k → F2) × (D × (D × Z))) + L x).1 *
              ((0 : (Fin k → F2) × (D × (D × Z))) + L x).2.1 i *
              ((0 : (Fin k → F2) × (D × (D × Z))) + L x).2.2.1 i = q x
         then (1 : ℤ) else -1) =
        chi (dotProduct (Phi A (xD1 x) (xD2 x)) (B (xJ x))) := by
      intro x
      rw [zero_add, chi_eq_ite]
      congr 1
      simp only [L, q, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_Phi]
      calc h (B (xJ x)) + (∑ i : Fin m, dotProduct (A i) (B (xJ x)) * xD1 x i * xD2 x i) +
            h (B (xJ x))
          = (h (B (xJ x)) + h (B (xJ x))) +
            ∑ i : Fin m, dotProduct (A i) (B (xJ x)) * xD1 x i * xD2 x i := by ring
        _ = ∑ i : Fin m, dotProduct (A i) (B (xJ x)) * xD1 x i * xD2 x i := by
            rw [zmod2_add_self, zero_add]
    simp_rw [hterm]
    have hsplit : (∑ x : E, chi (dotProduct (Phi A (xD1 x) (xD2 x)) (B (xJ x)))) =
        ∑ p : D × D × Z × J, chi (dotProduct (Phi A p.1 p.2.1) (B p.2.2.2)) :=
      Fintype.sum_equiv eSplit _ _ (fun _ => rfl)
    rw [hsplit]
    calc (∑ p : D × D × Z × J, chi (dotProduct (Phi A p.1 p.2.1) (B p.2.2.2)))
        = ∑ d1 : D, ∑ d2 : D, ∑ _z : Z, ∑ u : J, chi (dotProduct (Phi A d1 d2) (B u)) := by
          simp only [Fintype.sum_prod_type]
      _ = ∑ u : J, ∑ _z : Z, ∑ d1 : D, ∑ d2 : D, chi (dotProduct (Phi A d1 d2) (B u)) := by
          trans (∑ d1 : D, ∑ u : J, ∑ _z : Z, ∑ d2 : D, chi (dotProduct (Phi A d1 d2) (B u)))
          · refine Finset.sum_congr rfl (fun d1 _ => ?_)
            rw [Finset.sum_comm]
            trans (∑ z : Z, ∑ u : J, ∑ d2 : D, chi (dotProduct (Phi A d1 d2) (B u)))
            · refine Finset.sum_congr rfl (fun z _ => Finset.sum_comm)
            · exact Finset.sum_comm
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
      _ = ∑ u : J, ∑ _z : Z, (2 ^ m * 2 ^ (m - wtA A (B u)) : ℤ) := by
          refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun _ _ =>
            sum_chi_Phi_full A (B u)))
      _ = ((2 ^ (m + r) * ∑ u : J, 2 ^ (m - wtA A (B u)) : ℕ) : ℤ) := by
          simp only [Finset.sum_const, Finset.card_univ, Z, card_fin_F2, nsmul_eq_mul,
            ← Finset.mul_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_sum]
          rw [pow_add]
          ring
  rw [hsum_val, Int.natAbs_natCast]
  rw [← mul_assoc, ← pow_add]
  congr 1
  congr 1
  omega

end PEqualNP.Outside.L_lib_918

theorem PEqualNP.Outside.L_lib_918 :
    ∀ (k m r j : ℕ),
      let F := ZMod 2
      let S := Fin k → F
      let D := Fin m → F
      let Z := Fin r → F
      let V := S × (D × (D × Z))
      let J := Fin j → F
      let base := 2*m+r
      let t := base+j
      let E := Fin t → F
      let quad := fun (d : ℕ) (q : (Fin d → F) → F) =>
        ∃ (z : F) (l : Fin d → F) (M : Fin d → Fin d → F), ∀ x,
          q x = z + dotProduct l x + ∑ u, ∑ v, M u v * x u * x v
      ∀ A : Fin m → S,
        let wt := fun (a : S) => ((Finset.univ : Finset (Fin m)).filter
          (fun i => dotProduct (A i) a ≠ 0)).card
        let mass := fun (B : J →ₗ[F] S) => ∑ u : J, 2^(m-wt (B u))
        let val := fun (h : S → F) (x : V) =>
          h x.1 + ∑ i : Fin m, dotProduct (A i) x.1 * x.2.1 i * x.2.2.1 i
        let gap := fun (h : S → F) (a : V) (L : E →ₗ[F] V) (q : E → F) =>
          (∑ x : E, if val h (a+L x) = q x then (1 : ℤ) else -1).natAbs
        (∀ L : E →ₗ[F] V, Function.Injective L →
          ∃ B : J →ₗ[F] S, Function.Injective B ∧
            (∀ u : J, ∃ x : E, (L x).1 = B u) ∧
            ∀ (h : S → F) (a : V) (q : E → F), quad t q →
              2 * 2^(m+j) * gap h a L q ≤ 2^t * max (2^(m+j)) (2*mass B)) ∧
          (∀ (B : J →ₗ[F] S) (h : S → F), Function.Injective B →
            quad j (fun u => h (B u)) →
            ∃ (L : E →ₗ[F] V) (q : E → F), Function.Injective L ∧ quad t q ∧
              2^(m+j) * gap h 0 L q = 2^t * mass B) := by
  intro k m r j F S D Z V J base t E quad A wt mass val gap
  exact ⟨fun L hL => PEqualNP.Outside.L_lib_918.part1_main k m r j A L hL,
         fun B h hB hq => PEqualNP.Outside.L_lib_918.part2_main k m r j A B h hB hq⟩
