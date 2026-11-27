import PEqualNP.Defs
import Mathlib.FieldTheory.Finite.Trace

namespace PEqualNP.Outside.L_lib_815_aux

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma char2_add_self {K : Type} [Field K] [Algebra (ZMod 2) K] (x : K) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h2K : (2 : K) = 0 := by simpa [map_ofNat] using congrArg (algebraMap (ZMod 2) K) h2
  calc x + x = (2 : K) * x := by ring
    _ = 0 := by rw [h2K, zero_mul]

private lemma sq_inj_char2 {K : Type} [Field K] [Algebra (ZMod 2) K] {x y : K} (h : x ^ 2 = y ^ 2) :
    x = y := by
  have h0 : (x - y) ^ 2 = 0 := by
    calc (x - y) ^ 2 = x ^ 2 - (x * y + x * y) + y ^ 2 := by ring
      _ = x ^ 2 - 0 + y ^ 2 := by rw [char2_add_self]
      _ = x ^ 2 + x ^ 2 := by rw [sub_zero, h]
      _ = 0 := char2_add_self _
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp h0)

private lemma trace_sq (K : Type) [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    [Fintype K] (y : K) : Algebra.trace (ZMod 2) K (y ^ 2) = Algebra.trace (ZMod 2) K y := by
  let frobMap : K →ₗ[ZMod 2] K :=
    { toFun := fun x => x ^ 2
      map_add' := fun x1 x2 => by
        calc (x1 + x2) ^ 2 = x1 ^ 2 + (x1 * x2 + x1 * x2) + x2 ^ 2 := by ring
          _ = x1 ^ 2 + 0 + x2 ^ 2 := by rw [char2_add_self]
          _ = x1 ^ 2 + x2 ^ 2 := by rw [add_zero]
      map_smul' := fun c x => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp }
  have hfrob_bij : Function.Bijective frobMap := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun _ _ h => sq_inj_char2 h, rfl⟩
  let frob : K ≃ₗ[ZMod 2] K := LinearEquiv.ofBijective frobMap hfrob_bij
  have hconj : Algebra.lmul (ZMod 2) K (y ^ 2) =
      frob.toLinearMap.comp ((Algebra.lmul (ZMod 2) K y).comp frob.symm.toLinearMap) := by
    ext x
    change y ^ 2 * x = (y * frob.symm x) ^ 2
    rw [mul_pow]
    have hsq : (frob.symm x) ^ 2 = x := frob.apply_symm_apply x
    rw [hsq]
  rw [Algebra.trace_apply, Algebra.trace_apply, hconj]
  change LinearMap.trace (ZMod 2) K (frob.toLinearMap * ((Algebra.lmul (ZMod 2) K y) * frob.symm.toLinearMap)) = _
  rw [LinearMap.trace_mul_comm, mul_assoc]
  have hinv : frob.symm.toLinearMap * frob.toLinearMap = 1 := by
    ext x; exact frob.symm_apply_apply x
  rw [hinv, mul_one]

private lemma trace_nondeg (K : Type) [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]
    [Fintype K] {a : K} (ha : a ≠ 0) : ∃ b : K, Algebra.trace (ZMod 2) K (a * b) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hnd := traceForm_nondegenerate (ZMod 2) K
  have hker : a ∈ LinearMap.ker (Algebra.traceForm (ZMod 2) K) := by
    rw [LinearMap.mem_ker]
    ext b
    exact hall b
  have hbot : LinearMap.ker (Algebra.traceForm (ZMod 2) K) = ⊥ :=
    LinearMap.BilinForm.Nondegenerate.ker_eq_bot hnd
  rw [hbot, Submodule.mem_bot] at hker
  exact ha hker

private lemma exists_linmap_of_linearIndependent {K : Type} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (v : ι → K) (hli : LinearIndependent (ZMod 2) v) (t : ι → ZMod 2) :
    ∃ g : K →ₗ[ZMod 2] ZMod 2, ∀ i : ι, g (v i) = t i := by
  let S : Submodule (ZMod 2) K := Submodule.span (ZMod 2) (Set.range v)
  let bS : Module.Basis ι (ZMod 2) S := Module.Basis.span hli
  obtain ⟨W, hcompl⟩ := Submodule.exists_isCompl S
  let proj : K →ₗ[ZMod 2] S := Submodule.projectionOnto S W hcompl
  let fS : S →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun s => ∑ i : ι, t i * bS.repr s i
      map_add' := fun s1 s2 => by simp [map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a s => by
        simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring) }
  refine ⟨fS.comp proj, ?_⟩
  intro i
  have hmem : v i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  have hproj : proj (v i) = ⟨v i, hmem⟩ := Submodule.projectionOnto_apply_left hcompl ⟨v i, hmem⟩
  have hbi : bS i = ⟨v i, hmem⟩ := Module.Basis.span_apply hli i
  change fS (proj (v i)) = t i
  rw [hproj, ← hbi]
  change ∑ j : ι, t j * bS.repr (bS i) j = t i
  simp only [Module.Basis.repr_self, Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma dim_extend_of_not_mem {K : Type} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (L : Submodule (ZMod 2) K) (x : K) (hx : x ∉ L) :
    Module.finrank (ZMod 2) ↥(L ⊔ Submodule.span (ZMod 2) {x}) = Module.finrank (ZMod 2) L + 1 := by
  have hdisj : L ⊓ Submodule.span (ZMod 2) {x} = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hy
    rcases hy with ⟨hyL, c, rfl⟩
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · simp
    · simp only [one_smul] at hyL
      exact absurd hyL hx
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq L (Submodule.span (ZMod 2) {x})
  rw [hdisj, finrank_bot, add_zero] at hmod
  have hx0 : x ≠ 0 := fun h => hx (h ▸ L.zero_mem)
  have hspan : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {x}) = 1 :=
    finrank_span_singleton hx0
  rw [hspan] at hmod
  exact hmod

private lemma dim_sq_extend_le {K : Type} [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] (L : Submodule (ZMod 2) K) (x : K) :
    let sq := fun (M : Submodule (ZMod 2) K) =>
      Submodule.span (ZMod 2) (Set.range (fun ij : M × M => (ij.1 : K) * (ij.2 : K)))
    Module.finrank (ZMod 2) (sq (L ⊔ Submodule.span (ZMod 2) {x})) ≤
      Module.finrank (ZMod 2) (sq L) + Module.finrank (ZMod 2) L + 1 := by
  dsimp only
  let sq := fun (M : Submodule (ZMod 2) K) =>
    Submodule.span (ZMod 2) (Set.range (fun ij : M × M => (ij.1 : K) * (ij.2 : K)))
  let T : (sq L) × L × ZMod 2 →ₗ[ZMod 2] K :=
    { toFun := fun p => (p.1 : K) + x * (p.2.1 : K) + p.2.2 • (x * x)
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, mul_add, add_smul]
        ring
      map_smul' := fun a p => by
        simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply,
          smul_add, mul_smul_comm, smul_eq_mul, mul_smul] }
  have hle_range : sq (L ⊔ Submodule.span (ZMod 2) {x}) ≤ LinearMap.range T := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨y1, y2⟩, rfl⟩
    have hy1 := y1.2
    have hy2 := y2.2
    rw [Submodule.mem_sup] at hy1 hy2
    rcases hy1 with ⟨l1, hl1, z1, hz1, h1eq⟩
    rcases hy2 with ⟨l2, hl2, z2, hz2, h2eq⟩
    rw [Submodule.mem_span_singleton] at hz1 hz2
    rcases hz1 with ⟨c1, rfl⟩
    rcases hz2 with ⟨c2, rfl⟩
    have hprod_mem : l1 * l2 ∈ sq L := Submodule.subset_span ⟨(⟨l1, hl1⟩, ⟨l2, hl2⟩), rfl⟩
    let lsum : L := c1 • ⟨l2, hl2⟩ + c2 • ⟨l1, hl1⟩
    refine ⟨(⟨l1 * l2, hprod_mem⟩, lsum, c1 * c2), ?_⟩
    dsimp only [T, LinearMap.coe_mk, AddHom.coe_mk, lsum]
    rw [← h1eq, ← h2eq]
    simp only [Submodule.coe_add, SetLike.val_smul]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, mul_smul]
    rw [mul_comm x l1, smul_comm c2 c1]
    abel
  have hle1 : Module.finrank (ZMod 2) (sq (L ⊔ Submodule.span (ZMod 2) {x})) ≤
      Module.finrank (ZMod 2) (LinearMap.range T) := Submodule.finrank_mono hle_range
  have hle2 : Module.finrank (ZMod 2) (LinearMap.range T) ≤
      Module.finrank (ZMod 2) ((sq L) × L × ZMod 2) := by
    have hrk := LinearMap.finrank_range_add_finrank_ker T
    omega
  have hprod : Module.finrank (ZMod 2) ((sq L) × L × ZMod 2) =
      Module.finrank (ZMod 2) (sq L) + Module.finrank (ZMod 2) L + 1 := by
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_self, Nat.add_assoc]
  change Module.finrank (ZMod 2) (sq (L ⊔ Submodule.span (ZMod 2) {x})) ≤
    Module.finrank (ZMod 2) (sq L) + Module.finrank (ZMod 2) L + 1
  omega

private lemma even_incidence (K : Type) [Field K] [Algebra (ZMod 2) K]
    [FiniteDimensional (ZMod 2) K] [Fintype K] (L : Submodule (ZMod 2) K) :
    let F := ZMod 2
    let k := Module.finrank F K
    let dim := fun (M : Submodule F K) => Module.finrank F M
    let sq := fun (M : Submodule F K) =>
      Submodule.span F (Set.range (fun ij : M × M => (ij.1 : K) * (ij.2 : K)))
    let extend := fun (M : Submodule F K) (x : K) => M ⊔ Submodule.span F {x}
    let W := sq L
    let c := k - dim W
    let e := dim L + 1
    let exceptional := fun a : K => a ≠ 0 ∧ a ∈ L ∧
      ∀ w ∈ W, Algebra.trace F K ((a⁻¹) ^ 2 * w) = 0
    let E := (@Finset.filter K exceptional (fun a => Classical.propDecidable (exceptional a))
      Finset.univ).card
    2 ^ e * (∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ)) =
      2 ^ k * ((2 ^ c - 1) + E) ∧
    E ≤ 2 ^ (dim L) - 1 ∧
    E ≤ 2 ^ c - 1 := by
  classical
  dsimp only
  let F := ZMod 2
  let k := Module.finrank F K
  let dim : Submodule F K → ℕ := fun M => Module.finrank F M
  let sq : Submodule F K → Submodule F K := fun M =>
    Submodule.span F (Set.range (fun ij : M × M => (ij.1 : K) * (ij.2 : K)))
  let extend : Submodule F K → K → Submodule F K := fun M x => M ⊔ Submodule.span F {x}
  let W := sq L
  let c := k - dim W
  let e := dim L + 1
  let tr : K →ₗ[F] F := Algebra.trace F K
  have hK_card : Fintype.card K = 2 ^ k := by
    have h := Module.card_eq_pow_finrank (K := F) (V := K)
    simpa [F, ZMod.card, k] using h
  have hk_pos : 0 < k := by
    have h1 : 1 < Fintype.card K := Fintype.one_lt_card
    rw [hK_card] at h1
    by_contra h0
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h0
    rw [hk0, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hpow_card : ∀ y : K, y ^ (2 ^ k) = y := by
    intro y
    by_cases hy : y = 0
    · rw [hy, zero_pow (by positivity)]
    · let u : Kˣ := Units.mk0 y hy
      have hu_card : Fintype.card Kˣ = 2 ^ k - 1 := by rw [Fintype.card_units, hK_card]
      have hu1 : u ^ (2 ^ k - 1) = 1 := by
        rw [← hu_card]
        exact pow_card_eq_one
      have hy1 : y ^ (2 ^ k - 1) = 1 := by
        have := congrArg (fun z : Kˣ => (z : K)) hu1
        simpa [u] using this
      have h2k : 2 ^ k = (2 ^ k - 1) + 1 := by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      rw [h2k, pow_succ, hy1, one_mul]
  let sqrtK : K → K := fun b => b ^ (2 ^ (k - 1))
  have hsqrt_sq : ∀ b : K, (sqrtK b) ^ 2 = b := by
    intro b
    dsimp only [sqrtK]
    rw [← pow_mul, ← pow_succ, show k - 1 + 1 = k by omega]
    exact hpow_card b
  let φ : K →ₗ[F] (K →ₗ[F] F) :=
    { toFun := fun b =>
        { toFun := fun x => tr (b * x)
          map_add' := fun x y => by rw [mul_add, map_add]
          map_smul' := fun a x => by simp [map_smul] }
      map_add' := fun b1 b2 => by
        ext x; change tr ((b1 + b2) * x) = tr (b1 * x) + tr (b2 * x)
        rw [add_mul, map_add]
      map_smul' := fun a b => by
        ext x; change tr ((a • b) * x) = a • tr (b * x)
        rw [smul_mul_assoc, map_smul] }
  have : Finite (K →ₗ[F] F) := Finite.of_injective (fun f : K →ₗ[F] F => (f : K → F)) DFunLike.coe_injective
  let : Fintype (K →ₗ[F] F) := Fintype.ofFinite (K →ₗ[F] F)
  have hφ_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, ?_⟩
    · intro b1 b2 heq
      by_contra hne
      have hsub : b1 - b2 ≠ 0 := sub_ne_zero.mpr hne
      obtain ⟨y, hy⟩ := trace_nondeg K hsub
      have h0 := congrArg (fun g : K →ₗ[F] F => g y) heq
      change tr (b1 * y) = tr (b2 * y) at h0
      have h1 : tr ((b1 - b2) * y) = 0 := by
        rw [sub_mul, map_sub, h0, sub_self]
      exact hy h1
    · have hcard_dual : Fintype.card (K →ₗ[F] F) = 2 ^ k := by
        have h := Module.card_eq_pow_finrank (K := F) (V := K →ₗ[F] F)
        rw [h, ZMod.card, Subspace.dual_finrank_eq]
      rw [hK_card, hcard_dual]
  have hann_card : ∀ M : Submodule F K,
      (Finset.univ.filter (fun b : K => b ≠ 0 ∧ ∀ w ∈ M, tr (b * w) = 0)).card =
        2 ^ (k - dim M) - 1 := by
    intro M
    let bM := Module.finBasis F M
    let evM : K →ₗ[F] (Fin (dim M) → F) :=
      { toFun := fun b i => tr (b * (bM i : K))
        map_add' := fun b1 b2 => by funext i; simp [add_mul, map_add]
        map_smul' := fun a b => by funext i; simp [map_smul] }
    have hev_surj : Function.Surjective evM := by
      intro t
      have hli : LinearIndependent F (fun i : Fin (dim M) => (bM i : K)) :=
        bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
      obtain ⟨g, hg⟩ := exists_linmap_of_linearIndependent (fun i : Fin (dim M) => (bM i : K)) hli t
      obtain ⟨b, hb⟩ := hφ_bij.2 g
      refine ⟨b, ?_⟩
      funext i
      change (φ b) (bM i : K) = t i
      rw [hb]
      exact hg i
    have hker_eq : ∀ b : K, b ∈ LinearMap.ker evM ↔ ∀ w ∈ M, tr (b * w) = 0 := by
      intro b
      constructor
      · intro hb w hw
        have hrepr := bM.sum_repr ⟨w, hw⟩
        have hval := congrArg M.subtype hrepr
        simp only [map_sum, map_smul, Submodule.coe_subtype] at hval
        rw [← hval, Finset.mul_sum, map_sum]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [mul_smul_comm, map_smul]
        have hi : tr (b * (bM i : K)) = 0 := congrFun (LinearMap.mem_ker.mp hb) i
        rw [hi, smul_zero]
      · intro hall
        rw [LinearMap.mem_ker]
        funext i
        exact hall (bM i : K) (bM i).2
    have hker_card : Fintype.card (LinearMap.ker evM) = 2 ^ (k - dim M) := by
      have hrk := LinearMap.finrank_range_add_finrank_ker evM
      have hrg : LinearMap.range evM = ⊤ := LinearMap.range_eq_top.mpr hev_surj
      rw [hrg, finrank_top, Module.finrank_pi F, Fintype.card_fin] at hrk
      have hker_rk : Module.finrank F (LinearMap.ker evM) = k - dim M := by omega
      have hcard := Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker evM)
      rw [hcard, ZMod.card, hker_rk]
    have hbij : (Finset.univ.filter (fun b : K => b ≠ 0 ∧ ∀ w ∈ M, tr (b * w) = 0)).card =
        (Finset.univ.filter (fun y : LinearMap.ker evM => y ≠ 0)).card := by
      apply Finset.card_bij (fun b hb => (⟨b, (hker_eq b).mpr (Finset.mem_filter.mp hb).2.2⟩ : LinearMap.ker evM))
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        intro h0
        exact hb.1 (congrArg Subtype.val h0)
      · intro b1 _ b2 _ heq; exact congrArg Subtype.val heq
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h0 => hy (Subtype.ext h0), (hker_eq y.1).mp y.2⟩, ?_⟩
        exact Subtype.ext rfl
    have hsplit : Fintype.card (LinearMap.ker evM) =
        (Finset.univ.filter (fun y : LinearMap.ker evM => y ≠ 0)).card + 1 := by
      have hdisj : Disjoint (Finset.univ.filter (fun y : LinearMap.ker evM => y ≠ 0)) ({0} : Finset (LinearMap.ker evM)) := by
        rw [Finset.disjoint_singleton_right]; simp
      have hunion : Finset.univ.filter (fun y : LinearMap.ker evM => y ≠ 0) ∪ ({0} : Finset (LinearMap.ker evM)) = Finset.univ := by
        ext y; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, iff_true]; exact ne_or_eq y 0
      conv_lhs => rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
    rw [hbij]
    have h1 : 1 ≤ 2 ^ (k - dim M) := Nat.one_le_two_pow
    omega
  have hsq_ext_iff : ∀ (x b : K),
      (∀ w ∈ sq (extend L x), tr (b * w) = 0) ↔
        (∀ w ∈ W, tr (b * w) = 0) ∧ (∀ l ∈ L, tr (b * (x * l)) = 0) ∧ tr (b * (x * x)) = 0 := by
    intro x b
    constructor
    · intro hall
      have hL_le : L ≤ extend L x := le_sup_left
      have hx_mem : x ∈ extend L x := (le_sup_right : Submodule.span F {x} ≤ extend L x) (Submodule.mem_span_singleton_self x)
      refine ⟨?_, ?_, ?_⟩
      · intro w hw
        have hsq_le : W ≤ sq (extend L x) := by
          rw [Submodule.span_le]
          rintro _ ⟨⟨l1, l2⟩, rfl⟩
          exact Submodule.subset_span ⟨(⟨l1.1, hL_le l1.2⟩, ⟨l2.1, hL_le l2.2⟩), rfl⟩
        exact hall w (hsq_le hw)
      · intro l hl
        exact hall (x * l) (Submodule.subset_span ⟨(⟨x, hx_mem⟩, ⟨l, hL_le hl⟩), rfl⟩)
      · exact hall (x * x) (Submodule.subset_span ⟨(⟨x, hx_mem⟩, ⟨x, hx_mem⟩), rfl⟩)
    · rintro ⟨hsqL, hxl, hxx⟩
      have hle : sq (extend L x) ≤ LinearMap.ker (φ b) := by
        rw [Submodule.span_le]
        rintro _ ⟨⟨y1, y2⟩, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        change tr (b * (y1.1 * y2.1)) = 0
        have hy1 := y1.2
        have hy2 := y2.2
        rw [Submodule.mem_sup] at hy1 hy2
        rcases hy1 with ⟨l1, hl1, z1, hz1, h1eq⟩
        rcases hy2 with ⟨l2, hl2, z2, hz2, h2eq⟩
        rw [Submodule.mem_span_singleton] at hz1 hz2
        rcases hz1 with ⟨c1, rfl⟩
        rcases hz2 with ⟨c2, rfl⟩
        rw [← h1eq, ← h2eq]
        have hexp : b * ((l1 + c1 • x) * (l2 + c2 • x)) =
            b * (l1 * l2) + c1 • (b * (x * l2)) + c2 • (b * (x * l1)) + (c1 * c2) • (b * (x * x)) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, mul_smul]
          rw [mul_comm l1 x, smul_comm c2 c1]
          abel
        rw [hexp, map_add, map_add, map_add, map_smul, map_smul, map_smul,
            hsqL (l1 * l2) (Submodule.subset_span ⟨(⟨l1, hl1⟩, ⟨l2, hl2⟩), rfl⟩),
            hxl l2 hl2, hxl l1 hl1, hxx]
        simp
      intro w hw
      exact LinearMap.mem_ker.mp (hle hw)
  let Pairs : Finset (K × K) := Finset.univ.filter (fun p =>
    p.2 ≠ 0 ∧ ∀ w ∈ sq (extend L p.1), tr (p.2 * w) = 0)
  have hPairs_left : Pairs.card = ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
    have hmaps : ∀ p ∈ Pairs, p.1 ∈ (Finset.univ : Finset K) := fun _ _ => Finset.mem_univ _
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← hann_card (sq (extend L x))]
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨⟨hb0, hall⟩, rfl⟩
      exact ⟨hb0, hall⟩
    · intro p1 hp1 p2 hp2 heq
      simp only [Finset.mem_filter] at hp1 hp2
      exact Prod.ext (hp1.2.trans hp2.2.symm) heq
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      refine ⟨(x, b), ?_, rfl⟩
      simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hb, trivial⟩
  let AnnSq : Finset K := Finset.univ.filter (fun b : K => b ≠ 0 ∧ ∀ w ∈ W, tr (b * w) = 0)
  have hAnnSq_card : AnnSq.card = 2 ^ c - 1 := hann_card W
  let exceptional : K → Prop := fun a => a ≠ 0 ∧ a ∈ L ∧ ∀ w ∈ W, tr ((a⁻¹) ^ 2 * w) = 0
  let ExcA : Finset K := @Finset.filter K exceptional (fun a => Classical.propDecidable (exceptional a)) Finset.univ
  let ExcB : Finset K := AnnSq.filter (fun b : K => ∃ a ∈ L, sqrtK b = b * a)
  have hExc_eq : ExcA.card = ExcB.card := by
    apply Finset.card_bij (fun a _ => (a⁻¹) ^ 2)
    · intro a ha
      have hex : exceptional a := by simpa only [ExcA, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      rcases hex with ⟨ha0, haL, haW⟩
      simp only [ExcB, AnnSq, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨pow_ne_zero 2 (inv_ne_zero ha0), haW⟩, a, haL, ?_⟩
      have hsq : (sqrtK ((a⁻¹) ^ 2)) ^ 2 = (a⁻¹) ^ 2 := hsqrt_sq ((a⁻¹) ^ 2)
      have hsqrt_eq : sqrtK ((a⁻¹) ^ 2) = a⁻¹ := sq_inj_char2 hsq
      rw [hsqrt_eq]
      field_simp [ha0]
    · intro a1 _ a2 _ heq
      have hinv : a1⁻¹ = a2⁻¹ := sq_inj_char2 heq
      exact inv_injective hinv
    · intro b hb
      simp only [ExcB, AnnSq, Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rcases hb with ⟨⟨hb0, hbW⟩, a, haL, hba⟩
      have hsqrt0 : sqrtK b ≠ 0 := by
        intro h0
        have := hsqrt_sq b
        rw [h0, zero_pow (by decide)] at this
        exact hb0 this.symm
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hba
        exact hsqrt0 hba
      have hb_eq : (a⁻¹) ^ 2 = b := by
        have hsq := congrArg (fun z : K => z ^ 2) hba
        rw [hsqrt_sq b, mul_pow] at hsq
        have h1 : b * a ^ 2 = 1 := by
          apply mul_left_cancel₀ hb0
          calc b * (b * a ^ 2) = b ^ 2 * a ^ 2 := by ring
            _ = b := hsq.symm
            _ = b * 1 := (mul_one b).symm
        have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
        rw [inv_pow]
        apply mul_right_cancel₀ ha2
        rw [inv_mul_cancel₀ ha2, h1]
      refine ⟨a, ?_, hb_eq⟩
      have hex : exceptional a := ⟨ha0, haL, by rw [hb_eq]; exact hbW⟩
      simpa only [ExcA, Finset.mem_filter, Finset.mem_univ, true_and] using hex
  have hExc_le_L : ExcA.card ≤ 2 ^ (dim L) - 1 := by
    have hL_card : Fintype.card L = 2 ^ (dim L) := by
      have h := Module.card_eq_pow_finrank (K := F) (V := L)
      simpa [F, ZMod.card, dim] using h
    have hnz : (Finset.univ.filter (fun y : L => y ≠ 0)).card = 2 ^ (dim L) - 1 := by
      have hdisj : Disjoint (Finset.univ.filter (fun y : L => y ≠ 0)) ({0} : Finset L) := by
        rw [Finset.disjoint_singleton_right]; simp
      have hunion : Finset.univ.filter (fun y : L => y ≠ 0) ∪ ({0} : Finset L) = Finset.univ := by
        ext y; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, iff_true]; exact ne_or_eq y 0
      have hsplit : Fintype.card L = (Finset.univ.filter (fun y : L => y ≠ 0)).card + 1 := by
        conv_lhs => rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
      have h1 : 1 ≤ 2 ^ (dim L) := Nat.one_le_two_pow
      omega
    rw [← hnz]
    apply Finset.card_le_card_of_injOn (fun a => if ha : a ∈ L then (⟨a, ha⟩ : L) else 0)
    · intro a ha
      have hex : exceptional a := by simpa only [ExcA, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using ha
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, hex.2.1, ↓reduceDIte]
      intro h0
      exact hex.1 (congrArg Subtype.val h0)
    · intro a1 ha1 a2 ha2 heq
      have hex1 : exceptional a1 := by simpa only [ExcA, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using ha1
      have hex2 : exceptional a2 := by simpa only [ExcA, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using ha2
      simp only [hex1.2.1, hex2.2.1, ↓reduceDIte] at heq
      exact congrArg Subtype.val heq
  have hExc_le_c : ExcA.card ≤ 2 ^ c - 1 := by
    rw [hExc_eq, ← hAnnSq_card]
    exact Finset.card_filter_le _ _
  have hfiber_b : ∀ b ∈ AnnSq,
      2 ^ e * (Pairs.filter (fun p => p.2 = b)).card = if b ∈ ExcB then 2 * 2 ^ k else 2 ^ k := by
    intro b hb
    simp only [AnnSq, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rcases hb with ⟨hb0, hb_ann⟩
    let bL := Module.finBasis F L
    by_cases hbe : b ∈ ExcB
    · simp only [hbe, ↓reduceIte]
      have hex : ∃ a ∈ L, sqrtK b = b * a := (Finset.mem_filter.mp hbe).2
      rcases hex with ⟨a, haL, hba⟩
      let vec0 : Fin (dim L) → K := fun i => b * (bL i : K)
      have hli0 : LinearIndependent F vec0 := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        let l : L := ∑ i : Fin (dim L), g i • bL i
        have hl_val : b * (l : K) = ∑ i : Fin (dim L), g i • vec0 i := by
          have hcoe : (l : K) = ∑ i : Fin (dim L), g i • (bL i : K) := by
            change L.subtype l = _
            dsimp only [l]
            rw [map_sum]
            refine Finset.sum_congr rfl (fun i _ => by rw [map_smul]; rfl)
          rw [hcoe, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => mul_smul_comm _ _ _)
        rw [← hl_val] at hg
        have hl0 : l = 0 := Subtype.ext ((mul_eq_zero.mp hg).resolve_left hb0)
        exact Fintype.linearIndependent_iff.mp bL.linearIndependent g hl0
      let Ψ0 : K →ₗ[F] (Fin (dim L) → F) :=
        { toFun := fun x i => tr (vec0 i * x)
          map_add' := fun x y => by funext i; simp [mul_add, map_add]
          map_smul' := fun c x => by funext i; simp [map_smul] }
      have hΨ0_surj : Function.Surjective Ψ0 := by
        intro t
        obtain ⟨g, hg⟩ := exists_linmap_of_linearIndependent vec0 hli0 t
        obtain ⟨x, hx⟩ := hφ_bij.2 g
        refine ⟨x, ?_⟩
        funext i
        have hcomm : tr (vec0 i * x) = tr (x * vec0 i) := by rw [mul_comm]
        change tr (vec0 i * x) = t i
        rw [hcomm]
        change (φ x) (vec0 i) = t i
        rw [hx]
        exact hg i
      have hker0_iff : ∀ x : K, x ∈ LinearMap.ker Ψ0 ↔
          (∀ l ∈ L, tr (b * (x * l)) = 0) ∧ tr (b * (x * x)) = 0 := by
        intro x
        rw [LinearMap.mem_ker]
        constructor
        · intro hx
          have hxl : ∀ l ∈ L, tr (b * (x * l)) = 0 := by
            intro l hl
            have hrepr := bL.sum_repr ⟨l, hl⟩
            have hval := congrArg L.subtype hrepr
            simp only [map_sum, map_smul, Submodule.coe_subtype] at hval
            rw [← hval, Finset.mul_sum, Finset.mul_sum, map_sum]
            refine Finset.sum_eq_zero (fun i _ => ?_)
            rw [mul_smul_comm, mul_smul_comm, map_smul]
            have hi : tr (vec0 i * x) = 0 := congrFun hx i
            have hmul : b * (x * (bL i : K)) = vec0 i * x := by dsimp only [vec0]; ring
            rw [hmul, hi, smul_zero]
          refine ⟨hxl, ?_⟩
          have hsq : b * (x * x) = (sqrtK b * x) ^ 2 := by rw [mul_pow, hsqrt_sq b]; ring
          have hmul : sqrtK b * x = b * (x * a) := by rw [hba]; ring
          rw [hsq, trace_sq K, hmul]
          exact hxl a haL
        · rintro ⟨hxl, _⟩
          funext i
          change tr (b * (bL i : K) * x) = 0
          have hmul : b * (bL i : K) * x = b * (x * (bL i : K)) := by ring
          rw [hmul]
          exact hxl (bL i : K) (bL i).2
      have hbij : (Pairs.filter (fun p => p.2 = b)).card = Fintype.card (LinearMap.ker Ψ0) := by
        rw [← Finset.card_univ]
        apply Finset.card_bij (fun p hp => (⟨p.1, by
          simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨⟨_, hall⟩, rfl⟩
          exact (hker0_iff p.1).mpr ((hsq_ext_iff p.1 p.2).mp hall).2⟩ : LinearMap.ker Ψ0))
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 heq
          simp only [Finset.mem_filter] at hp1 hp2
          exact Prod.ext (congrArg Subtype.val heq) (hp1.2.trans hp2.2.symm)
        · intro x _
          refine ⟨(x.1, b), ?_, Subtype.ext rfl⟩
          simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hb0, (hsq_ext_iff x.1 b).mpr ⟨hb_ann, (hker0_iff x.1).mp x.2⟩⟩, trivial⟩
      have hrk := LinearMap.finrank_range_add_finrank_ker Ψ0
      have hrg : LinearMap.range Ψ0 = ⊤ := LinearMap.range_eq_top.mpr hΨ0_surj
      rw [hrg, finrank_top, Module.finrank_pi F, Fintype.card_fin] at hrk
      have hcard_ker := Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker Ψ0)
      rw [hbij, hcard_ker, ZMod.card]
      calc 2 ^ e * 2 ^ Module.finrank F (LinearMap.ker Ψ0)
          = 2 * (2 ^ (dim L) * 2 ^ Module.finrank F (LinearMap.ker Ψ0)) := by
              dsimp only [e]; rw [pow_succ]; ring
        _ = 2 * 2 ^ k := by rw [← pow_add, hrk]
    · simp only [hbe, ↓reduceIte]
      have hnot_ex : ¬ ∃ a ∈ L, sqrtK b = b * a := fun h =>
        hbe (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb0, hb_ann⟩, h⟩)
      let vec : Option (Fin (dim L)) → K := fun o =>
        match o with
        | none => sqrtK b
        | some i => b * (bL i : K)
      have hli : LinearIndependent F vec := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hsplit : g none • sqrtK b + ∑ i : Fin (dim L), g (some i) • (b * (bL i : K)) = 0 := by
          simpa [Fintype.sum_option, vec] using hg
        let l : L := ∑ i : Fin (dim L), g (some i) • bL i
        have hl_val : b * (l : K) = ∑ i : Fin (dim L), g (some i) • (b * (bL i : K)) := by
          have hcoe : (l : K) = ∑ i : Fin (dim L), g (some i) • (bL i : K) := by
            change L.subtype l = _
            dsimp only [l]
            rw [map_sum]
            refine Finset.sum_congr rfl (fun i _ => by rw [map_smul]; rfl)
          rw [hcoe, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => mul_smul_comm _ _ _)
        rw [← hl_val] at hsplit
        have hg_none : g none = 0 := by
          rcases zmod2_eq_zero_or_one (g none) with h0 | h1
          · exact h0
          · exfalso
            rw [h1, one_smul] at hsplit
            have hsq_eq : sqrtK b = b * (l : K) := by
              have hadd := congrArg (fun z => z + b * (l : K)) hsplit
              rw [add_assoc, char2_add_self, add_zero, zero_add] at hadd
              exact hadd
            exact hnot_ex ⟨l.1, l.2, hsq_eq⟩
        rw [hg_none, zero_smul, zero_add] at hsplit
        have hl0 : l = 0 := Subtype.ext ((mul_eq_zero.mp hsplit).resolve_left hb0)
        have hgsome := Fintype.linearIndependent_iff.mp bL.linearIndependent (fun i => g (some i)) hl0
        intro o
        cases o with
        | none => exact hg_none
        | some i => exact hgsome i
      let Ψ : K →ₗ[F] (Option (Fin (dim L)) → F) :=
        { toFun := fun x o => tr (vec o * x)
          map_add' := fun x y => by funext o; simp [mul_add, map_add]
          map_smul' := fun a x => by funext o; simp [map_smul] }
      have hΨ_surj : Function.Surjective Ψ := by
        intro t
        obtain ⟨g, hg⟩ := exists_linmap_of_linearIndependent vec hli t
        obtain ⟨x, hx⟩ := hφ_bij.2 g
        refine ⟨x, ?_⟩
        funext o
        have hcomm : tr (vec o * x) = tr (x * vec o) := by rw [mul_comm]
        change tr (vec o * x) = t o
        rw [hcomm]
        change (φ x) (vec o) = t o
        rw [hx]
        exact hg o
      have hker_iff : ∀ x : K, x ∈ LinearMap.ker Ψ ↔
          (∀ l ∈ L, tr (b * (x * l)) = 0) ∧ tr (b * (x * x)) = 0 := by
        intro x
        rw [LinearMap.mem_ker]
        constructor
        · intro hx
          refine ⟨?_, ?_⟩
          · intro l hl
            have hrepr := bL.sum_repr ⟨l, hl⟩
            have hval := congrArg L.subtype hrepr
            simp only [map_sum, map_smul, Submodule.coe_subtype] at hval
            rw [← hval, Finset.mul_sum, Finset.mul_sum, map_sum]
            refine Finset.sum_eq_zero (fun i _ => ?_)
            rw [mul_smul_comm, mul_smul_comm, map_smul]
            have hi : tr (vec (some i) * x) = 0 := congrFun hx (some i)
            have hmul : b * (x * (bL i : K)) = vec (some i) * x := by dsimp only [vec]; ring
            rw [hmul, hi, smul_zero]
          · have h0 : tr (sqrtK b * x) = 0 := congrFun hx none
            have hsq : b * (x * x) = (sqrtK b * x) ^ 2 := by rw [mul_pow, hsqrt_sq b]; ring
            rw [hsq, trace_sq K, h0]
        · rintro ⟨hxl, hxx⟩
          funext o
          cases o with
          | none =>
            change tr (sqrtK b * x) = 0
            have hsq : b * (x * x) = (sqrtK b * x) ^ 2 := by rw [mul_pow, hsqrt_sq b]; ring
            rw [← trace_sq K, ← hsq]
            exact hxx
          | some i =>
            change tr (b * (bL i : K) * x) = 0
            have hmul : b * (bL i : K) * x = b * (x * (bL i : K)) := by ring
            rw [hmul]
            exact hxl (bL i : K) (bL i).2
      have hbij : (Pairs.filter (fun p => p.2 = b)).card = Fintype.card (LinearMap.ker Ψ) := by
        rw [← Finset.card_univ]
        apply Finset.card_bij (fun p hp => (⟨p.1, by
          simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and] at hp
          rcases hp with ⟨⟨_, hall⟩, rfl⟩
          exact (hker_iff p.1).mpr ((hsq_ext_iff p.1 p.2).mp hall).2⟩ : LinearMap.ker Ψ))
        · intro _ _; exact Finset.mem_univ _
        · intro p1 hp1 p2 hp2 heq
          simp only [Finset.mem_filter] at hp1 hp2
          exact Prod.ext (congrArg Subtype.val heq) (hp1.2.trans hp2.2.symm)
        · intro x _
          refine ⟨(x.1, b), ?_, Subtype.ext rfl⟩
          simp only [Pairs, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨hb0, (hsq_ext_iff x.1 b).mpr ⟨hb_ann, (hker_iff x.1).mp x.2⟩⟩, trivial⟩
      have hrk := LinearMap.finrank_range_add_finrank_ker Ψ
      have hrg : LinearMap.range Ψ = ⊤ := LinearMap.range_eq_top.mpr hΨ_surj
      rw [hrg, finrank_top, Module.finrank_pi F, Fintype.card_option, Fintype.card_fin] at hrk
      have hcard_ker := Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker Ψ)
      rw [hbij, hcard_ker, ZMod.card, ← pow_add, hrk]
  have hPairs_right : 2 ^ e * Pairs.card = 2 ^ k * (AnnSq.card + ExcB.card) := by
    have hmaps : ∀ p ∈ Pairs, p.2 ∈ AnnSq := by
      intro p hp
      simp only [Pairs, AnnSq, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, ((hsq_ext_iff p.1 p.2).mp hp.2).1⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps, Finset.mul_sum]
    have hsum_eq : ∑ b ∈ AnnSq, 2 ^ e * (Pairs.filter (fun p => p.2 = b)).card =
        ∑ b ∈ AnnSq, (2 ^ k + if b ∈ ExcB then 2 ^ k else 0) := by
      refine Finset.sum_congr rfl (fun b hb => ?_)
      rw [hfiber_b b hb]
      split_ifs <;> ring
    rw [hsum_eq, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite_mem]
    have hinter : AnnSq ∩ ExcB = ExcB := Finset.inter_eq_right.mpr (Finset.filter_subset _ _)
    rw [hinter, Finset.sum_const, smul_eq_mul]
    ring
  refine ⟨?_, hExc_le_L, hExc_le_c⟩
  rw [← hPairs_left, hPairs_right, hAnnSq_card, ← hExc_eq]

end PEqualNP.Outside.L_lib_815_aux

open PEqualNP.Outside.L_lib_815_aux

theorem PEqualNP.Outside.L_lib_815 :
    (let F := ZMod 2
∀ (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] [Fintype K],
  let k := Module.finrank F K
  let dim := fun (L : Submodule F K) => Module.finrank F L
  let sq := fun (L : Submodule F K) =>
    Submodule.span F (Set.range (fun ij : L × L => (ij.1 : K) * (ij.2 : K)))
  let extend := fun (L : Submodule F K) (x : K) => L ⊔ Submodule.span F {x}
  k % 2 = 0 → ∀ L : Submodule F K,
    let W := sq L
    let c := k - dim W
    let e := dim L + 1
    let exceptional := fun a : K => a ≠ 0 ∧ a ∈ L ∧
      ∀ w ∈ W, Algebra.trace F K ((a⁻¹)^2 * w) = 0
    let E := (@Finset.filter K exceptional (fun a => Classical.propDecidable (exceptional a))
      Finset.univ).card
    let loss := if c = e ∧ 0 < E ∧
      2^(dim L) * (2^e - 2) ≤ (E-1) * 2^(k-e) then 1 else 0
    2^e * (∑ x : K, (2^(k - dim (sq (extend L x))) - 1 : ℕ)) =
      2^k * ((2^c - 1) + E) ∧
    ∃ x : K, dim (extend L x) = min k e ∧
      min k (dim W + e) - loss ≤ dim (sq (extend L x))) := by
  classical
  dsimp only
  intro K _ _ _ _ _hk_even L
  let F := ZMod 2
  let k := Module.finrank F K
  let dim : Submodule F K → ℕ := fun M => Module.finrank F M
  let sq : Submodule F K → Submodule F K := fun M =>
    Submodule.span F (Set.range (fun ij : M × M => (ij.1 : K) * (ij.2 : K)))
  let extend : Submodule F K → K → Submodule F K := fun M x => M ⊔ Submodule.span F {x}
  let W := sq L
  let c := k - dim W
  let e := dim L + 1
  let exceptional : K → Prop := fun a => a ≠ 0 ∧ a ∈ L ∧ ∀ w ∈ W, Algebra.trace F K ((a⁻¹) ^ 2 * w) = 0
  let E := (@Finset.filter K exceptional (fun a => Classical.propDecidable (exceptional a)) Finset.univ).card
  let loss := if c = e ∧ 0 < E ∧ 2 ^ (dim L) * (2 ^ e - 2) ≤ (E - 1) * 2 ^ (k - e) then 1 else 0
  obtain ⟨hinc, hE_le_L, hE_le_c⟩ := even_incidence K L
  change 2 ^ e * (∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ)) = 2 ^ k * ((2 ^ c - 1) + E) at hinc
  change E ≤ 2 ^ (dim L) - 1 at hE_le_L
  change E ≤ 2 ^ c - 1 at hE_le_c
  refine ⟨hinc, ?_⟩
  have hK_card : Fintype.card K = 2 ^ k := by
    have h := Module.card_eq_pow_finrank (K := F) (V := K)
    simpa [F, ZMod.card, k] using h
  have hL_card : (Finset.univ.filter (fun x : K => x ∈ L)).card = 2 ^ (dim L) := by
    have h := Module.card_eq_pow_finrank (K := F) (V := L)
    rw [ZMod.card] at h
    have hbij : (Finset.univ.filter (fun x : K => x ∈ L)).card = Fintype.card L := by
      rw [← Finset.card_univ]
      apply Finset.card_bij (fun x hx => (⟨x, (Finset.mem_filter.mp hx).2⟩ : L))
      · intro _ _; exact Finset.mem_univ _
      · intro x1 _ x2 _ heq; exact congrArg Subtype.val heq
      · intro y _; exact ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, Subtype.ext rfl⟩
    rw [hbij, h]
  have hdimW_le : dim W ≤ k := Submodule.finrank_le W
  have hdimL_le : dim L ≤ k := Submodule.finrank_le L
  have hW_eq : sq L = W := rfl
  by_cases hc0 : c = 0
  · have hWk : dim W = k := by omega
    by_cases hLk : dim L < k
    · have hne_top : L ≠ ⊤ := by
        intro htop
        rw [htop] at hLk
        have : dim (⊤ : Submodule F K) = k := finrank_top F K
        omega
      have hex : ∃ x : K, x ∉ L := by
        by_contra hall
        push Not at hall
        apply hne_top
        ext x
        exact ⟨fun _ => trivial, fun _ => hall x⟩
      rcases hex with ⟨x, hx⟩
      have hdim_eq : dim (extend L x) = dim L + 1 := dim_extend_of_not_mem L x hx
      have hsq_le : W ≤ sq (extend L x) := by
        rw [Submodule.span_le]
        rintro _ ⟨⟨l1, l2⟩, rfl⟩
        exact Submodule.subset_span ⟨(⟨l1.1, (le_sup_left : L ≤ extend L x) l1.2⟩, ⟨l2.1, (le_sup_left : L ≤ extend L x) l2.2⟩), rfl⟩
      have hsq_ge : k ≤ dim (sq (extend L x)) := hWk ▸ Submodule.finrank_mono hsq_le
      refine ⟨x, ?_, ?_⟩
      · change dim (extend L x) = min k e; omega
      · change min k (dim W + e) - loss ≤ dim (sq (extend L x)); omega
    · have hLk_eq : dim L = k := by omega
      have h0L : (0 : K) ∈ L := L.zero_mem
      have hext0 : extend L 0 = L := sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h0L))
      refine ⟨0, ?_, ?_⟩
      · change dim (extend L 0) = min k e; rw [hext0]; omega
      · change min k (dim W + e) - loss ≤ dim (sq (extend L 0)); rw [hext0, hW_eq]; omega
  · have hc_pos : 0 < c := by omega
    by_cases hlt : c < e
    · have hloss0 : loss = 0 := by dsimp only [loss]; simp [show c ≠ e by omega]
      have hsum_lt : (∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ)) < 2 ^ k := by
        have h2c : 2 ^ c * 2 ≤ 2 ^ e := by
          have : c + 1 ≤ e := by omega
          calc 2 ^ c * 2 = 2 ^ (c + 1) := by rw [pow_succ]
            _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) this
        have hrhs_lt : (2 ^ c - 1) + E < 2 ^ e := by
          have h1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
          omega
        have hmul : 2 ^ e * (∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ)) < 2 ^ e * 2 ^ k := by
          rw [hinc]
          calc 2 ^ k * ((2 ^ c - 1) + E) < 2 ^ k * 2 ^ e := Nat.mul_lt_mul_of_pos_left hrhs_lt (by positivity)
            _ = 2 ^ e * 2 ^ k := Nat.mul_comm _ _
        exact Nat.lt_of_mul_lt_mul_left hmul
      have hex : ∃ x : K, k ≤ dim (sq (extend L x)) := by
        by_contra hall
        push Not at hall
        have hge : 2 ^ k ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
          calc 2 ^ k = ∑ _x : K, 1 := by rw [Finset.sum_const, Finset.card_univ, hK_card, smul_eq_mul, mul_one]
            _ ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
                  refine Finset.sum_le_sum (fun x _ => ?_)
                  have hx := hall x
                  have hge1 : 1 ≤ k - dim (sq (extend L x)) := by omega
                  have h2 : 2 ^ 1 ≤ 2 ^ (k - dim (sq (extend L x))) := Nat.pow_le_pow_right (by decide) hge1
                  omega
        omega
      rcases hex with ⟨x, hx⟩
      have hx_not : x ∉ L := by
        intro hxL
        have hext : extend L x = L := sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL))
        rw [hext, hW_eq] at hx
        omega
      have hdim_eq : dim (extend L x) = e := dim_extend_of_not_mem L x hx_not
      have he_le : e ≤ k := hdim_eq ▸ Submodule.finrank_le _
      refine ⟨x, ?_, ?_⟩
      · change dim (extend L x) = min k e; omega
      · change min k (dim W + e) - loss ≤ dim (sq (extend L x)); rw [hloss0]; omega
    · by_cases hgt : e < c
      · have hloss0 : loss = 0 := by dsimp only [loss]; simp [show c ≠ e by omega]
        have hex : ∃ x : K, dim W + e ≤ dim (sq (extend L x)) := by
          by_contra hall
          push Not at hall
          have hge : 2 ^ k * (2 ^ (c - e + 1) - 1) ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
            calc 2 ^ k * (2 ^ (c - e + 1) - 1)
                = ∑ _x : K, (2 ^ (c - e + 1) - 1) := by rw [Finset.sum_const, Finset.card_univ, hK_card, smul_eq_mul]
              _ ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
                    refine Finset.sum_le_sum (fun x _ => ?_)
                    have hx := hall x
                    have h1 : c - e + 1 ≤ k - dim (sq (extend L x)) := by omega
                    have h2 : 2 ^ (c - e + 1) ≤ 2 ^ (k - dim (sq (extend L x))) := Nat.pow_le_pow_right (by decide) h1
                    omega
          have hmul := Nat.mul_le_mul_left (2 ^ e) hge
          rw [hinc] at hmul
          have hmul_eq : 2 ^ e * (2 ^ k * (2 ^ (c - e + 1) - 1)) = 2 ^ k * (2 ^ e * (2 ^ (c - e + 1) - 1)) := by ring
          rw [hmul_eq] at hmul
          have hle_rhs : 2 ^ e * (2 ^ (c - e + 1) - 1) ≤ (2 ^ c - 1) + E :=
            Nat.le_of_mul_le_mul_left hmul (by positivity)
          have hpow_ce : 2 ^ e * 2 ^ (c - e + 1) = 2 * 2 ^ c := by
            rw [← pow_add, show e + (c - e + 1) = c + 1 by omega, pow_succ, Nat.mul_comm]
          have h2e_le : 2 * 2 ^ e ≤ 2 ^ c := by
            have : e + 1 ≤ c := by omega
            calc 2 * 2 ^ e = 2 ^ e * 2 := Nat.mul_comm _ _
              _ = 2 ^ (e + 1) := (pow_succ 2 e).symm
              _ ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) this
          have h2L : 2 ^ (dim L) * 2 = 2 ^ e := by dsimp only [e]; rw [pow_succ]
          have h1 : 1 ≤ 2 ^ (c - e + 1) := Nat.one_le_two_pow
          have h2 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
          have h3 : 1 ≤ 2 ^ (dim L) := Nat.one_le_two_pow
          zify [h1, h2, h3] at hle_rhs hpow_ce h2e_le h2L hE_le_L
          nlinarith
        rcases hex with ⟨x, hx⟩
        have hx_not : x ∉ L := by
          intro hxL
          have hext : extend L x = L := sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL))
          rw [hext, hW_eq] at hx
          omega
        have hdim_eq : dim (extend L x) = e := dim_extend_of_not_mem L x hx_not
        refine ⟨x, ?_, ?_⟩
        · change dim (extend L x) = min k e; omega
        · change min k (dim W + e) - loss ≤ dim (sq (extend L x)); rw [hloss0]; omega
      · have hce : c = e := by omega
        by_cases hcond : 0 < E ∧ 2 ^ (dim L) * (2 ^ e - 2) ≤ (E - 1) * 2 ^ (k - e)
        · have hloss1 : loss = 1 := by dsimp only [loss]; simp [hce, hcond]
          have hdimL_pos : 0 < dim L := by
            have hEpos := hcond.1
            have h1 : 1 ≤ 2 ^ (dim L) := Nat.one_le_two_pow
            by_contra h0
            have hL0 : dim L = 0 := Nat.eq_zero_of_not_pos h0
            rw [hL0, pow_zero] at hE_le_L
            omega
          have h2e_ge : 4 ≤ 2 ^ e := by
            have : 2 ≤ e := by omega
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) this
          have hex : ∃ x : K, x ∉ L ∧ k - 1 ≤ dim (sq (extend L x)) := by
            by_contra hall
            push Not at hall
            have hterm : ∀ x : K, 3 ≤ 2 ^ (k - dim (sq (extend L x))) - 1 := by
              intro x
              by_cases hxL : x ∈ L
              · have hext : extend L x = L := sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL))
                rw [hext, hW_eq, show k - dim W = e from hce]
                omega
              · have hlt_k : dim (sq (extend L x)) < k - 1 := hall x hxL
                have hge2 : 2 ≤ k - dim (sq (extend L x)) := by omega
                have h2 : 2 ^ 2 ≤ 2 ^ (k - dim (sq (extend L x))) := Nat.pow_le_pow_right (by decide) hge2
                omega
            have hsum_ge : 3 * 2 ^ k ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
              calc 3 * 2 ^ k = ∑ _x : K, 3 := by
                    rw [Finset.sum_const, Finset.card_univ, hK_card, smul_eq_mul, Nat.mul_comm]
                _ ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := Finset.sum_le_sum (fun x _ => hterm x)
            have hmul := Nat.mul_le_mul_left (2 ^ e) hsum_ge
            rw [hinc] at hmul
            have hle_rhs : 3 * 2 ^ e ≤ (2 ^ c - 1) + E := by
              have : 2 ^ k * (3 * 2 ^ e) ≤ 2 ^ k * ((2 ^ c - 1) + E) := by
                calc 2 ^ k * (3 * 2 ^ e) = 2 ^ e * (3 * 2 ^ k) := by ring
                  _ ≤ 2 ^ k * ((2 ^ c - 1) + E) := hmul
              exact Nat.le_of_mul_le_mul_left this (by positivity)
            rw [hce] at hle_rhs hE_le_c
            omega
          rcases hex with ⟨x, hx_not, hx_sq⟩
          have hdim_eq : dim (extend L x) = e := dim_extend_of_not_mem L x hx_not
          refine ⟨x, ?_, ?_⟩
          · change dim (extend L x) = min k e; omega
          · change min k (dim W + e) - loss ≤ dim (sq (extend L x)); rw [hloss1]; omega
        · have hloss0 : loss = 0 := by dsimp only [loss]; simp [hce, hcond]
          have hex : ∃ x : K, k ≤ dim (sq (extend L x)) := by
            by_contra hall
            push Not at hall
            by_cases hE0 : E = 0
            · have hsum_ge : 2 ^ k ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
                calc 2 ^ k = ∑ _x : K, 1 := by rw [Finset.sum_const, Finset.card_univ, hK_card, smul_eq_mul, mul_one]
                  _ ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
                        refine Finset.sum_le_sum (fun x _ => ?_)
                        have hx := hall x
                        have hge1 : 1 ≤ k - dim (sq (extend L x)) := by omega
                        have h2 : 2 ^ 1 ≤ 2 ^ (k - dim (sq (extend L x))) := Nat.pow_le_pow_right (by decide) hge1
                        omega
              have hmul := Nat.mul_le_mul_left (2 ^ e) hsum_ge
              rw [hinc, hE0, Nat.add_zero, hce] at hmul
              have hle_rhs : 2 ^ e ≤ 2 ^ e - 1 := by
                have : 2 ^ k * 2 ^ e ≤ 2 ^ k * (2 ^ e - 1) := by rw [Nat.mul_comm]; exact hmul
                exact Nat.le_of_mul_le_mul_left this (by positivity)
              have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
              omega
            · have hE_pos : 0 < E := by omega
              have hnot_ineq : ¬ (2 ^ (dim L) * (2 ^ e - 2) ≤ (E - 1) * 2 ^ (k - e)) := fun h => hcond ⟨hE_pos, h⟩
              have h2e_ge2 : 2 ≤ 2 ^ e := by
                have : 1 ≤ e := by omega
                calc 2 = 2 ^ 1 := by norm_num
                  _ ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) this
              have hterm : ∀ x : K,
                  1 + (if x ∈ L then 2 ^ e - 2 else 0) ≤ 2 ^ (k - dim (sq (extend L x))) - 1 := by
                intro x
                split_ifs with hxL
                · have hext : extend L x = L := sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL))
                  rw [hext, hW_eq, show k - dim W = e from hce]
                  omega
                · have hx := hall x
                  have hge1 : 1 ≤ k - dim (sq (extend L x)) := by omega
                  have h2 : 2 ^ 1 ≤ 2 ^ (k - dim (sq (extend L x))) := Nat.pow_le_pow_right (by decide) hge1
                  omega
              have hsum_ge : 2 ^ k + 2 ^ (dim L) * (2 ^ e - 2) ≤
                  ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := by
                calc 2 ^ k + 2 ^ (dim L) * (2 ^ e - 2)
                    = (∑ _x : K, 1) + (∑ x : K, if x ∈ L then 2 ^ e - 2 else 0) := by
                        rw [Finset.sum_const, Finset.card_univ, hK_card, smul_eq_mul, mul_one,
                            ← Finset.sum_filter, Finset.sum_const, hL_card, smul_eq_mul]
                  _ = ∑ x : K, (1 + if x ∈ L then 2 ^ e - 2 else 0) := by rw [← Finset.sum_add_distrib]
                  _ ≤ ∑ x : K, (2 ^ (k - dim (sq (extend L x))) - 1 : ℕ) := Finset.sum_le_sum (fun x _ => hterm x)
              have hmul := Nat.mul_le_mul_left (2 ^ e) hsum_ge
              rw [hinc, hce] at hmul
              have hpow_k : 2 ^ e * 2 ^ (k - e) = 2 ^ k := by
                rw [← pow_add, show e + (k - e) = k by omega]
              have h1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
              have h2 : 1 ≤ E := hE_pos
              have h3 : 2 ^ e * (2 ^ (dim L) * (2 ^ e - 2)) ≤ 2 ^ e * ((E - 1) * 2 ^ (k - e)) := by
                zify [h1, h2] at hmul hpow_k ⊢
                nlinarith
              have hineq : 2 ^ (dim L) * (2 ^ e - 2) ≤ (E - 1) * 2 ^ (k - e) :=
                Nat.le_of_mul_le_mul_left h3 (by positivity)
              exact hnot_ineq hineq
          rcases hex with ⟨x, hx⟩
          have hx_not : x ∉ L := by
            intro hxL
            have hext : extend L x = L := sup_eq_left.mpr (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxL))
            rw [hext, hW_eq] at hx
            omega
          have hdim_eq : dim (extend L x) = e := dim_extend_of_not_mem L x hx_not
          refine ⟨x, ?_, ?_⟩
          · change dim (extend L x) = min k e; omega
          · change min k (dim W + e) - loss ≤ dim (sq (extend L x)); rw [hloss0]; omega
