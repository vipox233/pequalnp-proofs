import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_803

open Module

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K] [Fintype K]

open Classical

noncomputable instance instFinDual : Fintype (Module.Dual (ZMod 2) K) :=
  @Fintype.ofFinite _ (Module.finite_of_finite (ZMod 2))

theorem charTwo : CharP K 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) K).injective 2

theorem card_K : Fintype.card K = 2 ^ finrank (ZMod 2) K := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := K), ZMod.card]

theorem zmod2_sq (c : ZMod 2) : c * c = c := by fin_cases c <;> rfl

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by fin_cases a <;> rfl

def sqL : K →ₗ[ZMod 2] K where
  toFun x := x * x
  map_add' x y := by
    haveI := charTwo (K := K)
    show (x + y) * (x + y) = x * x + y * y
    rw [add_mul_self_eq, CharTwo.two_eq_zero]; ring
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, Algebra.smul_def]
    have h : algebraMap (ZMod 2) K c * algebraMap (ZMod 2) K c = algebraMap (ZMod 2) K c := by
      rw [← map_mul, zmod2_sq]
    calc _ = (algebraMap (ZMod 2) K c * algebraMap (ZMod 2) K c) * (x * x) := by ring
      _ = _ := by rw [h]

theorem sqL_apply (x : K) : sqL x = x * x := rfl

theorem T_zero (y : K) :
    ∑ i ∈ Finset.range (finrank (ZMod 2) K), (y * y + y) ^ (2 ^ i) = 0 := by
  haveI := charTwo (K := K)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ∀ i, (y * y + y) ^ (2 ^ i) = y ^ (2 ^ (i + 1)) - y ^ (2 ^ i) := by
    intro i
    rw [add_pow_char_pow, CharTwo.sub_eq_add, ← sq, ← pow_mul, pow_succ, mul_comm 2]
  simp_rw [h1]
  rw [Finset.sum_range_sub (fun i => y ^ (2 ^ i)), ← card_K, FiniteField.pow_card]
  simp

theorem T_one (hk : finrank (ZMod 2) K % 2 = 1) :
    ∑ i ∈ Finset.range (finrank (ZMod 2) K), (1 : K) ^ (2 ^ i) = 1 := by
  haveI := charTwo (K := K)
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have : finrank (ZMod 2) K = 2 * (finrank (ZMod 2) K / 2) + 1 := by omega
  rw [this]
  push_cast
  rw [CharTwo.two_eq_zero]; ring

theorem no_rel (hk : finrank (ZMod 2) K % 2 = 1) (φ : Module.Dual (ZMod 2) K) (hφ : φ ≠ 0)
    (l : K) (hl : φ (l * l) = 0) (h : ∀ x, φ (x * x) = φ (l * x)) : False := by
  haveI := charTwo (K := K)
  have h0 : ∀ x, φ (x * x + l * x) = 0 := by
    intro x; rw [map_add, h, zmod2_add_self]
  apply hφ
  by_cases hl0 : l = 0
  · subst hl0
    have hs : Function.Surjective (fun x : K => x * x) := by
      apply Finite.surjective_of_injective
      intro a b hab
      have hab' : a * a = b * b := hab
      have e : (a + b) * (a + b) = 0 := by
        rw [← sqL_apply, map_add, sqL_apply, sqL_apply, hab', CharTwo.add_self_eq_zero]
      have e2 := eq_neg_of_add_eq_zero_left (mul_self_eq_zero.mp e)
      rwa [CharTwo.neg_eq] at e2
    ext z
    obtain ⟨x, rfl⟩ := hs z
    simpa using h0 x
  · let S : K →ₗ[ZMod 2] K := sqL + LinearMap.id
    have hS : ∀ y, S y = y * y + y := fun y => rfl
    have hker : LinearMap.ker S ≤ Submodule.span (ZMod 2) {(1 : K)} := by
      intro y hy
      rw [LinearMap.mem_ker, hS] at hy
      have : y * (y + 1) = 0 := by rw [mul_add, mul_one]; exact hy
      rcases mul_eq_zero.mp this with h' | h'
      · rw [h']; exact Submodule.zero_mem _
      · have : y = 1 := by
          have := eq_neg_of_add_eq_zero_left h'; rwa [CharTwo.neg_eq] at this
        rw [this]; exact Submodule.mem_span_singleton_self 1
    have hkerd : finrank (ZMod 2) (LinearMap.ker S) ≤ 1 :=
      (Submodule.finrank_mono hker).trans (finrank_span_singleton (one_ne_zero (α := K))).le
    have hrn := LinearMap.finrank_range_add_finrank_ker S
    have h1 : (1 : K) ∉ LinearMap.range S := by
      rintro ⟨y, hy⟩
      rw [hS] at hy
      have := T_zero y
      rw [hy, T_one hk] at this
      exact one_ne_zero this
    have hlt : LinearMap.range S < LinearMap.range S ⊔ Submodule.span (ZMod 2) {(1 : K)} := by
      refine lt_of_le_of_ne le_sup_left (fun he => h1 ?_)
      rw [he]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1)
    have hfl := Submodule.finrank_lt_finrank_of_lt hlt
    have htop : LinearMap.range S ⊔ Submodule.span (ZMod 2) {(1 : K)} = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have := Submodule.finrank_le (LinearMap.range S ⊔ Submodule.span (ZMod 2) {(1 : K)})
      omega
    let ψ : Module.Dual (ZMod 2) K := φ ∘ₗ LinearMap.mulLeft (ZMod 2) (l * l)
    have hψ : LinearMap.range S ⊔ Submodule.span (ZMod 2) {(1 : K)} ≤ LinearMap.ker ψ := by
      apply sup_le
      · rintro _ ⟨y, rfl⟩
        rw [LinearMap.mem_ker, hS]
        have e : l * l * (y * y + y) = (l * y) * (l * y) + l * (l * y) := by ring
        simp only [ψ, LinearMap.comp_apply, LinearMap.mulLeft_apply, e]
        exact h0 (l * y)
      · rw [Submodule.span_le]
        rintro _ rfl
        simp [ψ, hl]
    rw [htop] at hψ
    have hll : l * l ≠ 0 := mul_ne_zero hl0 hl0
    ext z
    have := hψ (Submodule.mem_top : (l * l)⁻¹ * z ∈ ⊤)
    rw [LinearMap.mem_ker] at this
    simp only [ψ, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_inv_cancel_left₀ hll] at this
    exact this

def Phi (φ : Module.Dual (ZMod 2) K) : K →ₗ[ZMod 2] Module.Dual (ZMod 2) K where
  toFun c := φ ∘ₗ LinearMap.mulLeft (ZMod 2) c
  map_add' a b := by ext x; simp [add_mul]
  map_smul' c a := by ext x; simp

theorem Phi_apply (φ : Module.Dual (ZMod 2) K) (c x : K) : Phi φ c x = φ (c * x) := rfl

theorem Phi_inj (φ : Module.Dual (ZMod 2) K) (hφ : φ ≠ 0) : Function.Injective (Phi φ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro c hc
  by_contra hc0
  apply hφ; ext z
  have := LinearMap.congr_fun (LinearMap.mem_ker.mp hc) (c⁻¹ * z)
  rw [Phi_apply, mul_inv_cancel_left₀ hc0] at this
  simpa using this

theorem count (hk : finrank (ZMod 2) K % 2 = 1) (L : Submodule (ZMod 2) K)
    (φ : Module.Dual (ZMod 2) K) (hφ : φ ≠ 0)
    (hL : ∀ a ∈ L, ∀ b ∈ L, φ (a * b) = 0) :
    2 ^ (finrank (ZMod 2) L + 1) *
      (Finset.univ.filter (fun x : K => (∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0)).card =
      2 ^ finrank (ZMod 2) K := by
  classical
  have hinj := Phi_inj φ hφ
  have H : finrank (ZMod 2) K = finrank (ZMod 2) (Module.Dual (ZMod 2) K) :=
    (Subspace.dual_finrank_eq (K := ZMod 2) (V := K)).symm
  have hsurj : Function.Surjective (Phi φ) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Phi φ) H).mp hinj
  let e := LinearEquiv.ofBijective (Phi φ) ⟨hinj, hsurj⟩
  have he : ∀ l x, e l x = φ (l * x) := fun l x => rfl
  let W := L.map (e : K →ₗ[ZMod 2] Module.Dual (ZMod 2) K)
  let K1 := W.dualCoannihilator
  have hW : finrank (ZMod 2) W = finrank (ZMod 2) L := LinearEquiv.finrank_map_eq e L
  have hK1 : finrank (ZMod 2) W + finrank (ZMod 2) K1 = finrank (ZMod 2) K :=
    Subspace.finrank_add_finrank_dualCoannihilator_eq W
  have memK1 : ∀ x, x ∈ K1 ↔ ∀ l ∈ L, φ (x * l) = 0 := by
    intro x
    rw [Submodule.mem_dualCoannihilator]
    constructor
    · intro h l hl
      have := h (e l) (Submodule.mem_map_of_mem hl)
      rw [he, mul_comm] at this
      exact this
    · rintro h _ ⟨l, hl, rfl⟩
      have := h l hl
      rw [mul_comm] at this
      exact (he l x).trans this
  let ψ : K1 →ₗ[ZMod 2] ZMod 2 := (φ ∘ₗ sqL) ∘ₗ K1.subtype
  have hψ : ψ ≠ 0 := by
    intro h0
    have hmem : φ ∘ₗ sqL ∈ K1.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      have := LinearMap.congr_fun h0 ⟨x, hx⟩
      simpa [ψ] using this
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq, Submodule.mem_map] at hmem
    obtain ⟨l, hl, hle⟩ := hmem
    apply no_rel hk φ hφ l (hL l hl l hl)
    intro x
    have := LinearMap.congr_fun hle x
    exact (show φ (l * x) = φ (x * x) from this).symm
  have hsurjψ : Function.Surjective ψ := by
    obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hψ (LinearMap.ext hc)
    have hy1 : ψ y = 1 := by
      revert hy; generalize ψ y = t; intro hy; fin_cases t
      · exact absurd rfl hy
      · rfl
    intro c
    exact ⟨c • y, by rw [map_smul, hy1, smul_eq_mul, mul_one]⟩
  have hrange : finrank (ZMod 2) (LinearMap.range ψ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurjψ, finrank_top, Module.finrank_self]
  have hrn := LinearMap.finrank_range_add_finrank_ker ψ
  have hcard : (Finset.univ.filter (fun x : K => (∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0)).card
      = Nat.card (LinearMap.ker ψ) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    exact {
      toFun := fun x => ⟨⟨x.1, (memK1 x.1).2 x.2.1⟩, LinearMap.mem_ker.mpr x.2.2⟩
      invFun := fun y => ⟨y.1.1, (memK1 _).1 y.1.2, by
        have := y.2
        rw [LinearMap.mem_ker] at this
        exact this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [hcard, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add]
  congr 1
  omega

theorem cardN (W : Submodule (ZMod 2) K) :
    (Finset.univ.filter (fun φ : Module.Dual (ZMod 2) K => φ ≠ 0 ∧ ∀ w ∈ W, φ w = 0)).card
      = 2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) W) - 1 := by
  classical
  have h1 : Finset.univ.filter (fun φ : Module.Dual (ZMod 2) K => φ ≠ 0 ∧ ∀ w ∈ W, φ w = 0)
      = (Finset.univ.filter (fun φ : Module.Dual (ZMod 2) K => φ ∈ W.dualAnnihilator)).erase 0 := by
    ext φ; simp [Submodule.mem_dualAnnihilator]
  rw [h1, Finset.card_erase_of_mem (by simp)]
  have h2 : (Finset.univ.filter (fun φ : Module.Dual (ZMod 2) K => φ ∈ W.dualAnnihilator)).card
      = 2 ^ finrank (ZMod 2) W.dualAnnihilator := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have h3 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [h2]
  congr 2
  omega

theorem ann_sq_iff (W : Submodule (ZMod 2) K) (φ : Module.Dual (ZMod 2) K) :
    (∀ w ∈ Submodule.span (ZMod 2) (Set.range (fun ij : W × W => (ij.1 : K) * (ij.2 : K))),
      φ w = 0) ↔ ∀ a ∈ W, ∀ b ∈ W, φ (a * b) = 0 := by
  constructor
  · intro h a ha b hb
    exact h _ (Submodule.subset_span ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩)
  · intro h w hw
    have hle : Submodule.span (ZMod 2) (Set.range (fun ij : W × W => (ij.1 : K) * (ij.2 : K)))
        ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨a, b⟩, rfl⟩
      exact LinearMap.mem_ker.mpr (h _ a.2 _ b.2)
    exact LinearMap.mem_ker.mp (hle hw)

theorem ext_iff' (L : Submodule (ZMod 2) K) (x : K) (φ : Module.Dual (ZMod 2) K) :
    (∀ a ∈ L ⊔ Submodule.span (ZMod 2) {x}, ∀ b ∈ L ⊔ Submodule.span (ZMod 2) {x},
      φ (a * b) = 0) ↔
      (∀ a ∈ L, ∀ b ∈ L, φ (a * b) = 0) ∧ ((∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0) := by
  constructor
  · intro h
    have hx : x ∈ L ⊔ Submodule.span (ZMod 2) {x} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
    exact ⟨fun a ha b hb => h a (Submodule.mem_sup_left ha) b (Submodule.mem_sup_left hb),
      fun l hl => h x hx l (Submodule.mem_sup_left hl), h x hx x hx⟩
  · rintro ⟨h1, h2, h3⟩ a ha b hb
    obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨l', hl', y', hy', rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    have e : (l + c • x) * (l' + c' • x) =
        l * l' + c' • (x * l) + c • (x * l') + (c * c') • (x * x) := by
      simp only [Algebra.smul_def, map_mul]; ring
    rw [e, map_add, map_add, map_add, map_smul, map_smul, map_smul, h1 l hl l' hl', h2 l hl,
      h2 l' hl', h3]
    simp

theorem main (hk : finrank (ZMod 2) K % 2 = 1) (L : Submodule (ZMod 2) K) :
    2 ^ (finrank (ZMod 2) L + 1) * (∑ x : K, (2 ^ (finrank (ZMod 2) K - finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun ij : (L ⊔ Submodule.span (ZMod 2) {x} :
        Submodule (ZMod 2) K) × (L ⊔ Submodule.span (ZMod 2) {x} : Submodule (ZMod 2) K) =>
          (ij.1 : K) * (ij.2 : K))))) - 1 : ℕ)) =
      2 ^ finrank (ZMod 2) K * (2 ^ (finrank (ZMod 2) K - finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K))))) - 1) := by
  classical
  have hx : ∀ x : K, (2 ^ (finrank (ZMod 2) K - finrank (ZMod 2)
      (Submodule.span (ZMod 2) (Set.range (fun ij : (L ⊔ Submodule.span (ZMod 2) {x} :
        Submodule (ZMod 2) K) × (L ⊔ Submodule.span (ZMod 2) {x} : Submodule (ZMod 2) K) =>
          (ij.1 : K) * (ij.2 : K))))) - 1 : ℕ) =
      ∑ φ : Module.Dual (ZMod 2) K, if (φ ≠ 0 ∧ ∀ a ∈ L, ∀ b ∈ L, φ (a * b) = 0) ∧
        ((∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0) then 1 else 0 := by
    intro x
    rw [← cardN, Finset.card_filter]
    apply Finset.sum_congr rfl
    intro φ _
    apply if_congr _ rfl rfl
    rw [ann_sq_iff, ext_iff', and_assoc]
  rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_comm, Finset.mul_sum, ← cardN,
    Finset.card_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro φ _
  by_cases hA : φ ≠ 0 ∧ ∀ a ∈ L, ∀ b ∈ L, φ (a * b) = 0
  · have hA' : φ ≠ 0 ∧ ∀ w ∈ Submodule.span (ZMod 2)
        (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K))), φ w = 0 :=
      ⟨hA.1, (ann_sq_iff L φ).2 hA.2⟩
    rw [if_pos hA', mul_one]
    have hiff : ∀ x : K, ((φ ≠ 0 ∧ ∀ a ∈ L, ∀ b ∈ L, φ (a * b) = 0) ∧
        ((∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0)) ↔
        ((∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0) :=
      fun x => ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩
    simp_rw [hiff]
    rw [← Finset.card_filter]
    exact count hk L φ hA.1 hA.2
  · have hA' : ¬ (φ ≠ 0 ∧ ∀ w ∈ Submodule.span (ZMod 2)
        (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K))), φ w = 0) :=
      fun h => hA ⟨h.1, (ann_sq_iff L φ).1 h.2⟩
    rw [if_neg hA']
    have hno : ∀ x : K, ¬ ((φ ≠ 0 ∧ ∀ a ∈ L, ∀ b ∈ L, φ (a * b) = 0) ∧
        ((∀ l ∈ L, φ (x * l) = 0) ∧ φ (x * x) = 0)) := fun x h => hA h.1
    simp [hno]


def sqS (W : Submodule (ZMod 2) K) : Submodule (ZMod 2) K :=
  Submodule.span (ZMod 2) (Set.range (fun ij : W × W => (ij.1 : K) * (ij.2 : K)))

theorem main' (hk : finrank (ZMod 2) K % 2 = 1) (L : Submodule (ZMod 2) K) :
    2 ^ (finrank (ZMod 2) L + 1) * (∑ x : K,
      (2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ))
      = 2 ^ finrank (ZMod 2) K * (2 ^ (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) - 1) :=
  main hk L

theorem sq_mono {V W : Submodule (ZMod 2) K} (h : V ≤ W) : sqS V ≤ sqS W := by
  apply Submodule.span_mono
  rintro _ ⟨⟨a, b⟩, rfl⟩
  exact ⟨(⟨a, h a.2⟩, ⟨b, h b.2⟩), rfl⟩

theorem sq_top : sqS (⊤ : Submodule (ZMod 2) K) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  exact Submodule.subset_span ⟨(⟨1, trivial⟩, ⟨z, trivial⟩), one_mul z⟩

theorem fr_single (v : K) : finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := by
  have := finrank_span_le_card (R := ZMod 2) ({v} : Set K)
  simpa using this

theorem sq_ext_le (V : Submodule (ZMod 2) K) (x : K) :
    finrank (ZMod 2) (sqS (V ⊔ Submodule.span (ZMod 2) {x})) ≤
      finrank (ZMod 2) (sqS V) + finrank (ZMod 2) V + 1 := by
  have hle : sqS (V ⊔ Submodule.span (ZMod 2) {x}) ≤
      sqS V ⊔ V.map (LinearMap.mulLeft (ZMod 2) x) ⊔ Submodule.span (ZMod 2) {x * x} := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, b⟩, rfl⟩
    obtain ⟨l, hl, y, hy, ha⟩ := Submodule.mem_sup.mp a.2
    obtain ⟨l', hl', y', hy', hb⟩ := Submodule.mem_sup.mp b.2
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hy'
    have e : (a : K) * (b : K) =
        (l * l' + (c' • (x * l) + c • (x * l'))) + (c * c') • (x * x) := by
      rw [← ha, ← hb]
      simp only [Algebra.smul_def, map_mul]; ring
    show (a : K) * (b : K) ∈ _
    rw [e]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ?_) ?_
    · exact Submodule.subset_span ⟨(⟨l, hl⟩, ⟨l', hl'⟩), rfl⟩
    · refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
      · exact ⟨l, hl, rfl⟩
      · exact ⟨l', hl', rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank
    (sqS V ⊔ V.map (LinearMap.mulLeft (ZMod 2) x)) (Submodule.span (ZMod 2) {x * x})
  have h3 := Submodule.finrank_add_le_finrank_add_finrank (sqS V)
    (V.map (LinearMap.mulLeft (ZMod 2) x))
  have h4 := Submodule.finrank_map_le (LinearMap.mulLeft (ZMod 2) x) V
  have h5 := fr_single (x * x)
  omega

theorem ext_dim (V : Submodule (ZMod 2) K) (x : K) (hx : x ∉ V) :
    finrank (ZMod 2) ↥(V ⊔ Submodule.span (ZMod 2) {x}) = finrank (ZMod 2) V + 1 := by
  have hlt : (V : Submodule (ZMod 2) K) < V ⊔ Submodule.span (ZMod 2) {x} := by
    refine lt_of_le_of_ne le_sup_left (fun he => hx ?_)
    rw [he]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_add_le_finrank_add_finrank V (Submodule.span (ZMod 2) {x})
  have h3 := fr_single x
  omega

theorem ext_mem (V : Submodule (ZMod 2) K) (x : K) (hx : x ∈ V) :
    V ⊔ Submodule.span (ZMod 2) {x} = V :=
  sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem x V).mpr hx)

theorem part1 (hk : finrank (ZMod 2) K % 2 = 1) (L : Submodule (ZMod 2) K)
    (bad : K → Prop) [hdec : DecidablePred bad]
    (hbad : ∀ x, bad x ↔ finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) <
      min (finrank (ZMod 2) K) (finrank (ZMod 2) (sqS L) + (finrank (ZMod 2) L + 1))) :
    2 ^ (max (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) (finrank (ZMod 2) L + 1)) *
      (Finset.univ.filter bad).card ≤
      2 ^ finrank (ZMod 2) K *
        (2 ^ (min (finrank (ZMod 2) K - finrank (ZMod 2) (sqS L)) (finrank (ZMod 2) L + 1)) - 1) := by
  have H := main' hk L
  set k := finrank (ZMod 2) K with hkdef
  set s := finrank (ZMod 2) (sqS L)
  set r := finrank (ZMod 2) L
  have hs : s ≤ k := Submodule.finrank_le _
  have hd : ∀ x : K, finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) ≤ k :=
    fun x => Submodule.finrank_le _
  have hd2 : ∀ x : K, finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) ≤ s + r + 1 :=
    fun x => sq_ext_le L x
  set S := ∑ x : K,
      (2 ^ (k - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ) with hS
  rw [Finset.card_filter]
  by_cases hce : k - s ≤ r + 1
  · rw [max_eq_right hce, min_eq_left hce, ← H]
    apply Nat.mul_le_mul_left
    apply Finset.sum_le_sum
    intro x _
    split_ifs with hb
    · rw [hbad] at hb
      have : 1 ≤ k - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) := by omega
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
      simp at this
      omega
    · exact Nat.zero_le _
  · push Not at hce
    rw [max_eq_left hce.le, min_eq_right hce.le]
    set P := 2 ^ (k - s - (r + 1)) with hP
    set Q := 2 ^ (r + 1) with hQ
    have hPQ : 2 ^ (k - s) = P * Q := by rw [hP, hQ, ← pow_add]; congr 1; omega
    have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
    have hP1 : 1 ≤ P := Nat.one_le_two_pow
    have hpt : ∀ x : K, (if bad x then P else 0) + P ≤
        (2 ^ (k - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) - 1 : ℕ) + 1 := by
      intro x
      have hge : 1 ≤ 2 ^ (k - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x}))) :=
        Nat.one_le_two_pow
      rw [Nat.sub_add_cancel hge]
      split_ifs with hb
      · rw [hbad] at hb
        have : k - s - (r + 1) + 1 ≤ k - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) := by
          have := hd2 x; omega
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
        rw [pow_succ] at this
        omega
      · have : k - s - (r + 1) ≤ k - finrank (ZMod 2) (sqS (L ⊔ Submodule.span (ZMod 2) {x})) := by
          have := hd2 x; omega
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) this
        omega
    have hsum := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset K)) => hpt x)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
    rw [← hS, card_K, ← hkdef] at hsum
    have hite : (∑ x : K, if bad x then P else 0) = P * ∑ x : K, if bad x then 1 else 0 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; split_ifs <;> simp
    rw [hite] at hsum
    set B := ∑ x : K, if bad x then 1 else 0
    rw [hPQ] at H
    have hm := Nat.mul_le_mul_left Q hsum
    have hK1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    zify [hQ1, hK1, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega) : P * Q ≠ 0)] at H hm ⊢
    nlinarith [H, hm]

theorem step (hk : finrank (ZMod 2) K % 2 = 1) (V : Submodule (ZMod 2) K) :
    ∃ V' : Submodule (ZMod 2) K, V ≤ V' ∧
      finrank (ZMod 2) V' = min (finrank (ZMod 2) K) (finrank (ZMod 2) V + 1) ∧
      finrank (ZMod 2) (sqS V') =
        min (finrank (ZMod 2) K) (finrank (ZMod 2) (sqS V) + finrank (ZMod 2) V + 1) := by
  have hsk : finrank (ZMod 2) (sqS V) ≤ finrank (ZMod 2) K := Submodule.finrank_le _
  have hvk : finrank (ZMod 2) V ≤ finrank (ZMod 2) K := Submodule.finrank_le _
  by_cases hV : finrank (ZMod 2) V = finrank (ZMod 2) K
  · have htop : V = ⊤ := Submodule.eq_top_of_finrank_eq hV
    refine ⟨V, le_rfl, by omega, ?_⟩
    rw [htop, sq_top, finrank_top]
    omega
  · have hne : V ≠ ⊤ := fun h => hV (by rw [h, finrank_top])
    obtain ⟨x0, _, hx0⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
    by_cases hs : finrank (ZMod 2) (sqS V) = finrank (ZMod 2) K
    · refine ⟨V ⊔ Submodule.span (ZMod 2) {x0}, le_sup_left, ?_, ?_⟩
      · rw [ext_dim V x0 hx0]; omega
      · have h1 := Submodule.finrank_mono (sq_mono (le_sup_left :
          V ≤ V ⊔ Submodule.span (ZMod 2) {x0}))
        have h2 : finrank (ZMod 2) (sqS (V ⊔ Submodule.span (ZMod 2) {x0})) ≤
          finrank (ZMod 2) K := Submodule.finrank_le _
        omega
    · classical
      let bad : K → Prop := fun x => finrank (ZMod 2) (sqS (V ⊔ Submodule.span (ZMod 2) {x})) <
        min (finrank (ZMod 2) K) (finrank (ZMod 2) (sqS V) + (finrank (ZMod 2) V + 1))
      have hlt : (Finset.univ.filter bad).card < 2 ^ finrank (ZMod 2) K := by
        set c := finrank (ZMod 2) K - finrank (ZMod 2) (sqS V)
        set e := finrank (ZMod 2) V + 1
        have hp : 2 ^ (max c e) * (Finset.univ.filter bad).card ≤
            2 ^ finrank (ZMod 2) K * (2 ^ (min c e) - 1) := part1 hk V bad (fun x => Iff.rfl)
        have hmm : 2 ^ (min c e) ≤ 2 ^ (max c e) :=
          Nat.pow_le_pow_right (by norm_num) (min_le_max)
        have h1 : 1 ≤ 2 ^ (min c e) := Nat.one_le_two_pow
        have h2 : 2 ^ finrank (ZMod 2) K * (2 ^ (min c e) - 1) <
            2 ^ (max c e) * 2 ^ finrank (ZMod 2) K := by
          rw [mul_comm (2 ^ (max c e))]
          apply Nat.mul_lt_mul_of_pos_left _ Nat.one_le_two_pow
          omega
        by_contra hc
        push Not at hc
        have := Nat.mul_le_mul_left (2 ^ (max c e)) hc
        omega
      obtain ⟨x, hx⟩ : ∃ x, ¬ bad x := by
        by_contra hc
        push Not at hc
        have : Finset.univ.filter bad = Finset.univ := Finset.filter_true_of_mem (fun x _ => hc x)
        rw [this, Finset.card_univ, card_K] at hlt
        exact lt_irrefl _ hlt
      have hxV : x ∉ V := by
        intro hm
        apply hx
        show _ < _
        rw [ext_mem V x hm]
        omega
      refine ⟨V ⊔ Submodule.span (ZMod 2) {x}, le_sup_left, ?_, ?_⟩
      · rw [ext_dim V x hxV]; omega
      · have h1 := sq_ext_le V x
        have h2 : finrank (ZMod 2) (sqS (V ⊔ Submodule.span (ZMod 2) {x})) ≤
          finrank (ZMod 2) K := Submodule.finrank_le _
        have h3 : ¬ (finrank (ZMod 2) (sqS (V ⊔ Submodule.span (ZMod 2) {x})) <
          min (finrank (ZMod 2) K) (finrank (ZMod 2) (sqS V) + (finrank (ZMod 2) V + 1))) := hx
        omega

theorem chain (hk : finrank (ZMod 2) K % 2 = 1) (L : Submodule (ZMod 2) K) :
    ∃ V : ℕ → Submodule (ZMod 2) K, V 0 = L ∧ Monotone V ∧
      ∀ j : ℕ, finrank (ZMod 2) (V j) = min (finrank (ZMod 2) K) (finrank (ZMod 2) L + j) ∧
        finrank (ZMod 2) (sqS (V j)) = min (finrank (ZMod 2) K)
          (finrank (ZMod 2) (sqS L) + j * finrank (ZMod 2) L + j * (j + 1) / 2) := by
  choose f hf using step hk
  refine ⟨fun j => f^[j] L, rfl, ?_, ?_⟩
  · apply monotone_nat_of_le_succ
    intro j
    show f^[j] L ≤ f^[j+1] L
    rw [Function.iterate_succ_apply']
    exact (hf _).1
  · have hsk : finrank (ZMod 2) (sqS L) ≤ finrank (ZMod 2) K := Submodule.finrank_le _
    have hvk : finrank (ZMod 2) L ≤ finrank (ZMod 2) K := Submodule.finrank_le _
    intro j
    induction j with
    | zero =>
      show finrank (ZMod 2) L = _ ∧ finrank (ZMod 2) (sqS L) = _
      constructor <;> (simp only [zero_mul, add_zero, Nat.zero_div, mul_zero]; omega)
    | succ j ih =>
      show finrank (ZMod 2) (f^[j+1] L) = _ ∧ finrank (ZMod 2) (sqS (f^[j+1] L)) = _
      rw [Function.iterate_succ_apply', (hf _).2.1, (hf _).2.2, ih.1, ih.2]
      have e1 : (j + 1) * finrank (ZMod 2) L = j * finrank (ZMod 2) L + finrank (ZMod 2) L := by
        ring
      have e2 : (j + 1) * (j + 1 + 1) / 2 = j * (j + 1) / 2 + (j + 1) := by
        rw [show (j + 1) * (j + 1 + 1) = j * (j + 1) + (j + 1) * 2 by ring,
          Nat.add_mul_div_right _ _ (by norm_num)]
      rw [e1, e2]
      generalize j * finrank (ZMod 2) L = a
      generalize j * (j + 1) / 2 = b
      constructor <;> omega

end PEqualNP.Outside.L_lib_803

open PEqualNP.Outside.L_lib_803 in
theorem PEqualNP.Outside.L_lib_803 : let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
  let k := Module.finrank F K
  let dim := fun (L : Submodule F K) => Module.finrank F L
  let sq := fun (L : Submodule F K) =>
    Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (L : Submodule F K) (x : K) => L ⊔ Submodule.span F {x}
  k % 2 = 1 → ∀ L : Submodule F K,
    let c := k - dim (sq L)
    let e := dim L + 1
    let bad := fun x : K => dim (sq (extend L x)) < min k (dim (sq L) + e)
    2^(max c e) * (@Finset.filter K bad (fun x => Classical.propDecidable (bad x))
      Finset.univ).card ≤ 2^k * (2^(min c e) - 1) ∧
    ∃ V : ℕ → Submodule F K, V 0 = L ∧ Monotone V ∧
      ∀ j : ℕ, dim (V j) = min k (dim L+j) ∧
        dim (sq (V j)) = min k (dim (sq L) + j*dim L + j*(j+1)/2) := by
  intro F K _ _ _ _ k dim sq extend hk L c e bad
  exact ⟨part1 hk L bad (hdec := fun x => Classical.propDecidable (bad x)) (fun x => Iff.rfl),
    chain hk L⟩
