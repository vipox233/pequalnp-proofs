import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_802_aux

abbrev F := ZMod 2

lemma two_eq_zero_K (K : Type) [Field K] [Algebra F K] : (2 : K) = 0 := by
  have h : algebraMap F K (2 : F) = (2 : K) := map_ofNat (algebraMap F K) 2
  rw [← h]
  have h2 : (2 : F) = 0 := rfl
  rw [h2, map_zero]

lemma add_sq_K (K : Type) [Field K] [Algebra F K] (a b : K) :
    (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h2 : (2 : K) = 0 := two_eq_zero_K K
  calc (a + b) ^ 2 = a ^ 2 + 2 * (a * b) + b ^ 2 := by ring
    _ = a ^ 2 + 0 * (a * b) + b ^ 2 := by rw [h2]
    _ = a ^ 2 + b ^ 2 := by ring

lemma zmod2_sq (c : F) : c ^ 2 = c := by
  fin_cases c <;> rfl

lemma trace_one_eq_one (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (hodd : Module.finrank F K % 2 = 1) :
    Algebra.trace F K (1 : K) = 1 := by
  rw [show (1 : K) = algebraMap F K 1 from (map_one _).symm, Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one]
  change ((Module.finrank F K : ℕ) : ZMod 2) = 1
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
  exact hodd

noncomputable def frobEquiv (K : Type) [Field K] [Algebra F K] [Fintype K] : K ≃ₐ[F] K :=
  let f : K →ₐ[F] K :=
    { toFun := fun x => x ^ 2
      map_one' := one_pow 2
      map_mul' := fun a b => mul_pow a b 2
      map_zero' := zero_pow (by decide)
      map_add' := fun a b => add_sq_K K a b
      commutes' := fun c => by rw [← map_pow, zmod2_sq] }
  have hinj : Function.Injective f := by
    intro a b hab
    change a ^ 2 = b ^ 2 at hab
    have hsub : (a - b) ^ 2 = 0 := by
      calc (a - b) ^ 2 = a ^ 2 - 2 * (a * b) + b ^ 2 := by ring
        _ = a ^ 2 - 0 * (a * b) + b ^ 2 := by rw [two_eq_zero_K K]
        _ = b ^ 2 + b ^ 2 := by rw [hab]; ring
        _ = 2 * b ^ 2 := by ring
        _ = 0 := by rw [two_eq_zero_K K, zero_mul]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsub)
  AlgEquiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)

lemma trace_sq_eq (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K] (y : K) :
    Algebra.trace F K (y ^ 2) = Algebra.trace F K y := by
  let e : K ≃ₐ[F] K := frobEquiv K
  have he : e y = y ^ 2 := rfl
  rw [← he]
  have hconj : Algebra.lmul F K (e y) =
      e.toLinearEquiv.conj (Algebra.lmul F K y) := by
    ext z
    change e y * z = e (y * e.symm z)
    rw [map_mul, AlgEquiv.apply_symm_apply]
  change LinearMap.trace F K (Algebra.lmul F K (e y)) = LinearMap.trace F K (Algebra.lmul F K y)
  rw [hconj, LinearMap.trace_conj']

noncomputable def traceDual (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] :
    K →ₗ[F] (K →ₗ[F] F) where
  toFun b := (Algebra.trace F K).comp (LinearMap.mulLeft F b)
  map_add' b1 b2 := by
    ext x
    simp [LinearMap.mulLeft_apply, add_mul, map_add]
  map_smul' c b := by
    ext x
    simp [LinearMap.mulLeft_apply, map_smul]

lemma traceDual_bijective (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (hodd : Module.finrank F K % 2 = 1) :
    Function.Bijective (traceDual K) := by
  have hinj : Function.Injective (traceDual K) := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have h1 := LinearMap.congr_fun hb b⁻¹
    simp only [traceDual, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      LinearMap.mulLeft_apply, mul_inv_cancel₀ hb0, LinearMap.zero_apply] at h1
    rw [trace_one_eq_one K hodd] at h1
    exact one_ne_zero h1
  have hdim : Module.finrank F K = Module.finrank F (K →ₗ[F] F) := by
    rw [Subspace.dual_finrank_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj |>
    fun hsurj => ⟨hinj, hsurj⟩

noncomputable def ann (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] (M : Submodule F K) :
    Submodule F K :=
  { carrier := {b : K | ∀ m ∈ M, Algebra.trace F K (b * m) = 0},
    zero_mem' := fun m _ => by rw [zero_mul, map_zero], add_mem' := fun ha hb m hm => by rw [add_mul, map_add, ha m hm, hb m hm, add_zero],
    smul_mem' := fun c a ha m hm => by rw [smul_mul_assoc, map_smul, ha m hm, smul_zero] }

lemma finrank_ann (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (hodd : Module.finrank F K % 2 = 1) (M : Submodule F K) :
    Module.finrank F (ann K M) = Module.finrank F K - Module.finrank F M := by
  let e : K ≃ₗ[F] (K →ₗ[F] F) := LinearEquiv.ofBijective (traceDual K) (traceDual_bijective K hodd)
  let res : (K →ₗ[F] F) →ₗ[F] (M →ₗ[F] F) :=
    { toFun := fun f => f.comp M.subtype
      map_add' := fun f g => by ext m; simp
      map_smul' := fun c f => by ext m; simp }
  let g : K →ₗ[F] (M →ₗ[F] F) := res.comp e.toLinearMap
  have hker : LinearMap.ker g = ann K M := by
    ext b
    constructor
    · intro hb m hm
      exact LinearMap.congr_fun hb ⟨m, hm⟩
    · intro hb
      rw [LinearMap.mem_ker]
      ext ⟨m, hm⟩
      exact hb m hm
  have hsurj : Function.Surjective g := by
    intro f
    obtain ⟨C, hMC⟩ := Submodule.exists_isCompl M
    let piM : K →ₗ[F] M := Submodule.projectionOnto M C hMC
    let fext : K →ₗ[F] F := f.comp piM
    refine ⟨e.symm fext, ?_⟩
    ext m
    simp only [g, LinearMap.comp_apply, res, LinearMap.coe_mk, AddHom.coe_mk,
      LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, fext, Submodule.coe_subtype,
      piM, Submodule.projectionOnto_apply_left hMC m]
  have hrk := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Subspace.dual_finrank_eq, hker] at hrk
  omega

lemma card_submodule (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
    (M : Submodule F K) [DecidablePred (· ∈ M)] :
    (Finset.univ.filter (fun x : K => x ∈ M)).card = 2 ^ Module.finrank F M := by
  rw [← Fintype.card_subtype]
  let e : M ≃ₗ[F] (Fin (Module.finrank F M) → F) :=
    LinearEquiv.ofFinrankEq M (Fin (Module.finrank F M) → F) (by simp)
  rw [Fintype.card_congr e.toEquiv]
  simp [F]

lemma card_ann_nonzero (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K]
    [DecidableEq K] (hodd : Module.finrank F K % 2 = 1) (M : Submodule F K)
    [DecidablePred (· ∈ ann K M)] :
    (Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ ann K M)).card =
      2 ^ (Module.finrank F K - Module.finrank F M) - 1 := by
  have hcard_all : (Finset.univ.filter (fun b : K => b ∈ ann K M)).card =
      2 ^ (Module.finrank F K - Module.finrank F M) := by
    rw [← finrank_ann K hodd M, card_submodule K (ann K M)]
  have hzero : (0 : K) ∈ Finset.univ.filter (fun b : K => b ∈ ann K M) := by
    simp
  have herase : Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ ann K M) =
      (Finset.univ.filter (fun b : K => b ∈ ann K M)).erase 0 := by
    ext b
    simp
  rw [herase, Finset.card_erase_of_mem hzero, hcard_all]

lemma mem_ann_sq_extend_iff (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
    (L : Submodule F K) (x b : K) :
    b ∈ ann K (Submodule.span F (Set.range (fun ij : (L ⊔ Submodule.span F {x} : Submodule F K) ×
        (L ⊔ Submodule.span F {x} : Submodule F K) => (ij.1 : K) * (ij.2 : K)))) ↔
      b ∈ ann K (Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))) ∧
        (∀ l ∈ L, Algebra.trace F K (b * (l * x)) = 0) ∧
        Algebra.trace F K (b * (x ^ 2)) = 0 := by
  let sq := fun (M : Submodule F K) =>
    Submodule.span F (Set.range (fun ij : M × M => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (M : Submodule F K) (y : K) => M ⊔ Submodule.span F {y}
  change b ∈ ann K (sq (extend L x)) ↔
    b ∈ ann K (sq L) ∧ (∀ l ∈ L, Algebra.trace F K (b * (l * x)) = 0) ∧
      Algebra.trace F K (b * (x ^ 2)) = 0
  constructor
  · intro hb
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      apply hb m
      have hle : sq L ≤ sq (extend L x) := by
        apply Submodule.span_mono
        rintro _ ⟨⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩, rfl⟩
        exact ⟨⟨⟨l1, Submodule.mem_sup_left hl1⟩, ⟨l2, Submodule.mem_sup_left hl2⟩⟩, rfl⟩
      exact hle hm
    · intro l hl
      apply hb (l * x)
      apply Submodule.subset_span
      exact ⟨⟨⟨l, Submodule.mem_sup_left hl⟩,
        ⟨x, Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))⟩⟩, rfl⟩
    · apply hb (x ^ 2)
      rw [pow_two]
      apply Submodule.subset_span
      have hx : x ∈ extend L x := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton x))
      exact ⟨⟨⟨x, hx⟩, ⟨x, hx⟩⟩, rfl⟩
  · rintro ⟨hbL, hblx, hbx2⟩ m hm
    have hle : sq (extend L x) ≤ LinearMap.ker (traceDual K b) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change Algebra.trace F K (b * (u * v)) = 0
      obtain ⟨l1, hl1, _, hu2, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨l2, hl2, _, hv2, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨c1, rfl⟩ := Submodule.mem_span_singleton.mp hu2
      obtain ⟨c2, rfl⟩ := Submodule.mem_span_singleton.mp hv2
      have hprod : b * ((l1 + c1 • x) * (l2 + c2 • x)) =
          b * (l1 * l2) + c2 • (b * (l1 * x)) + c1 • (b * (l2 * x)) + (c1 * c2) • (b * x ^ 2) := by
        simp only [Algebra.smul_def, map_mul]
        ring
      rw [hprod, map_add, map_add, map_add, map_smul, map_smul, map_smul]
      have h12 : Algebra.trace F K (b * (l1 * l2)) = 0 :=
        hbL (l1 * l2) (Submodule.subset_span ⟨⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩, rfl⟩)
      rw [h12, hblx l1 hl1, hblx l2 hl2, hbx2]
      simp
    exact hle hm

end PEqualNP.Outside.L_lib_802_aux

open PEqualNP.Outside.L_lib_802_aux in
theorem PEqualNP.Outside.L_lib_802 : (let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
  let k := Module.finrank F K
  let dim := fun (L : Submodule F K) => Module.finrank F L
  let sq := fun (L : Submodule F K) =>
    Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (L : Submodule F K) (x : K) => L ⊔ Submodule.span F {x}
  k % 2 = 1 → ∀ L : Submodule F K,
    2^(dim L + 1) * (∑ x : K, (2^(k - dim (sq (extend L x))) - 1 : ℕ)) =
      2^k * (2^(k - dim (sq L)) - 1)) := by
  classical
  intro F K _ _ _ _ k dim sq extend hodd L
  let B : Finset K := Finset.univ.filter (fun b : K => b ≠ 0 ∧ b ∈ ann K (sq L))
  have hB_card : B.card = 2 ^ (k - dim (sq L)) - 1 := card_ann_nonzero K hodd (sq L)
  have hlhs_eq : (∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ)) =
      ∑ b ∈ B, (Finset.univ.filter (fun x : K => b ∈ ann K (sq (extend L x)))).card := by
    have h1 : ∀ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) =
        ∑ b : K, if b ≠ 0 ∧ b ∈ ann K (sq (extend L x)) then 1 else 0 := by
      intro x
      rw [← card_ann_nonzero K hodd (sq (extend L x)), Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ b : K, (∑ x : K, if b ≠ 0 ∧ b ∈ ann K (sq (extend L x)) then (1 : ℕ) else 0) =
        if b ∈ B then (Finset.univ.filter (fun x : K => b ∈ ann K (sq (extend L x)))).card else 0 := by
      intro b
      by_cases hb : b ∈ B
      · simp only [hb, ↓reduceIte, Finset.card_filter]
        apply Finset.sum_congr rfl
        intro x _
        have hb0 : b ≠ 0 := (Finset.mem_filter.mp hb).2.1
        simp [hb0]
      · simp only [hb, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro x _
        split_ifs with h
        · exfalso
          apply hb
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ b, h.1, ((mem_ann_sq_extend_iff K L x b).mp h.2).1⟩
        · rfl
    simp_rw [h2, ← Finset.sum_filter]
    congr 1
    ext b
    simp
  rw [hlhs_eq, ← hB_card]
  have hfiber : ∀ b ∈ B,
      2 ^ (dim L + 1) * (Finset.univ.filter (fun x : K => b ∈ ann K (sq (extend L x)))).card = 2 ^ k := by
    intro b hb
    have hb_mem := (Finset.mem_filter.mp hb).2
    have hb0 : b ≠ 0 := hb_mem.1
    have hbL : b ∈ ann K (sq L) := hb_mem.2
    let e := frobEquiv K
    let u : K := e.symm b
    have hu2 : u ^ 2 = b := e.apply_symm_apply b
    let bL : Submodule F K := L.map (LinearMap.mulLeft F b)
    let Mb : Submodule F K := bL ⊔ Submodule.span F {u}
    have hset : Finset.univ.filter (fun x : K => b ∈ ann K (sq (extend L x))) =
        Finset.univ.filter (fun x : K => x ∈ ann K Mb) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_ann_sq_extend_iff K L x b]
      have hiff_bL : (∀ l ∈ L, Algebra.trace F K (b * (l * x)) = 0) ↔
          (∀ m ∈ bL, Algebra.trace F K (x * m) = 0) := by
        constructor
        · rintro h m ⟨l, hl, rfl⟩
          have : x * (LinearMap.mulLeft F b l) = b * (l * x) := by
            simp only [LinearMap.mulLeft_apply]; ring
          rw [this]
          exact h l hl
        · intro h l hl
          have : b * (l * x) = x * (LinearMap.mulLeft F b l) := by
            simp only [LinearMap.mulLeft_apply]; ring
          rw [this]
          exact h _ ⟨l, hl, rfl⟩
      have hiff_u : Algebra.trace F K (b * x ^ 2) = 0 ↔ Algebra.trace F K (x * u) = 0 := by
        have h1 : b * x ^ 2 = (x * u) ^ 2 := by rw [mul_pow, hu2]; ring
        rw [h1, trace_sq_eq K (x * u)]
      have hiff_Mb : x ∈ ann K Mb ↔
          (∀ m ∈ bL, Algebra.trace F K (x * m) = 0) ∧ Algebra.trace F K (x * u) = 0 := by
        constructor
        · intro hx
          exact ⟨fun m hm => hx m (Submodule.mem_sup_left hm),
            hx u (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u)))⟩
        · rintro ⟨hx1, hx2⟩ m hm
          obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Submodule.mem_sup.mp hm
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hm2
          rw [mul_add, map_add, hx1 m1 hm1, zero_add, mul_smul_comm, map_smul, hx2, smul_zero]
      rw [hiff_Mb, ← hiff_bL, ← hiff_u]
      exact ⟨fun h => h.2, fun h => ⟨hbL, h⟩⟩
    rw [hset]
    have hcard_Mb : (Finset.univ.filter (fun x : K => x ∈ ann K Mb)).card = 2 ^ (k - dim Mb) := by
      rw [← finrank_ann K hodd Mb, card_submodule K (ann K Mb)]
    have hdim_bL : dim bL = dim L := by
      have hrange : bL = LinearMap.range ((LinearMap.mulLeft F b).comp L.subtype) := by
        ext y
        constructor
        · rintro ⟨l, hl, rfl⟩
          exact ⟨⟨l, hl⟩, rfl⟩
        · rintro ⟨⟨l, hl⟩, rfl⟩
          exact ⟨l, hl, rfl⟩
      rw [hrange]
      apply LinearMap.finrank_range_of_inj
      intro x y hxy
      apply Subtype.ext
      exact mul_left_cancel₀ hb0 hxy
    have hu_not_mem : u ∉ bL := by
      rintro ⟨l, hl, hlu⟩
      simp only [LinearMap.mulLeft_apply] at hlu
      have hsq : b = b ^ 2 * l ^ 2 := by
        calc b = u ^ 2 := hu2.symm
          _ = (b * l) ^ 2 := by rw [hlu]
          _ = b ^ 2 * l ^ 2 := mul_pow b l 2
      have h1 : 1 = b * (l * l) := by
        apply mul_left_cancel₀ hb0
        calc b * 1 = b := mul_one b
          _ = b ^ 2 * l ^ 2 := hsq
          _ = b * (b * (l * l)) := by ring
      have htr1 : Algebra.trace F K (1 : K) = 1 := trace_one_eq_one K hodd
      have htr0 : Algebra.trace F K (b * (l * l)) = 0 :=
        hbL (l * l) (Submodule.subset_span ⟨⟨⟨l, hl⟩, ⟨l, hl⟩⟩, rfl⟩)
      rw [h1, htr0] at htr1
      exact zero_ne_one htr1
    have hu0 : u ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by decide)] at hu2
      exact hb0 hu2.symm
    have hinf : bL ⊓ Submodule.span F {u} = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro z ⟨hz1, hz2⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz2
      have hc : c = 0 ∨ c = 1 := by
        fin_cases c
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hc with rfl | rfl
      · simp
      · simp only [one_smul] at hz1
        exact absurd hz1 hu_not_mem
    have hdim_Mb : dim Mb = dim L + 1 := by
      have hsum := Submodule.finrank_sup_add_finrank_inf_eq bL (Submodule.span F {u})
      dsimp only [dim, Mb] at hdim_bL ⊢
      rw [hinf, finrank_bot, add_zero, hdim_bL, finrank_span_singleton hu0] at hsum
      exact hsum
    have hMb_le : dim L + 1 ≤ k := by
      rw [← hdim_Mb]
      exact Submodule.finrank_le Mb
    rw [hcard_Mb, hdim_Mb, ← pow_add, Nat.add_sub_cancel' hMb_le]
  rw [Finset.mul_sum]
  calc ∑ b ∈ B, 2 ^ (dim L + 1) * (Finset.univ.filter (fun x : K => b ∈ ann K (sq (extend L x)))).card
      = ∑ _b ∈ B, 2 ^ k := Finset.sum_congr rfl hfiber
    _ = 2 ^ k * B.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
