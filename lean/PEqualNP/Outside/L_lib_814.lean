import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_814_aux

abbrev F := ZMod 2

def linMapOf {m j : ℕ} (Y : Fin j → (Fin m → F)) : (Fin j → F) →ₗ[F] (Fin m → F) where
  toFun v a := ∑ b : Fin j, v b * Y b a
  map_add' u v := by
    ext a
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext a
    simp [Finset.mul_sum, mul_assoc]

lemma range_linMapOf {m j : ℕ} (Y : Fin j → (Fin m → F)) :
    LinearMap.range (linMapOf Y) = Submodule.span F (Set.range Y) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have hv : linMapOf Y v = ∑ b : Fin j, v b • Y b := by
      ext a
      simp [linMapOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hv]
    exact Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    refine ⟨Pi.single b 1, ?_⟩
    ext a
    simp [linMapOf, Pi.single_apply]

lemma exists_equiv_of_same_span {m j : ℕ} (Y Z : Fin j → (Fin m → F))
    (hspan : Submodule.span F (Set.range Y) = Submodule.span F (Set.range Z)) :
    ∃ φ : (Fin j → F) ≃ₗ[F] (Fin j → F), ∀ v, linMapOf Y (φ v) = linMapOf Z v := by
  let TY := linMapOf Y
  let TZ := linMapOf Z
  have hrange : LinearMap.range TY = LinearMap.range TZ := by
    rw [range_linMapOf, range_linMapOf, hspan]
  obtain ⟨UY, hUY⟩ := Submodule.exists_isCompl (LinearMap.ker TY)
  obtain ⟨UZ, hUZ⟩ := Submodule.exists_isCompl (LinearMap.ker TZ)
  let rY : UY →ₗ[F] LinearMap.range TY :=
    LinearMap.codRestrict (LinearMap.range TY) (TY.comp UY.subtype) (fun u => ⟨u.1, rfl⟩)
  let rZ : UZ →ₗ[F] LinearMap.range TZ :=
    LinearMap.codRestrict (LinearMap.range TZ) (TZ.comp UZ.subtype) (fun u => ⟨u.1, rfl⟩)
  have hrY_bij : Function.Bijective rY := by
    constructor
    · intro u1 u2 h12
      have h0 : TY (u1.1 - u2.1) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h12
      have hmem : u1.1 - u2.1 ∈ LinearMap.ker TY ⊓ UY :=
        ⟨h0, Submodule.sub_mem UY u1.2 u2.2⟩
      rw [hUY.inf_eq_bot, Submodule.mem_bot] at hmem
      exact Subtype.ext (sub_eq_zero.mp hmem)
    · rintro ⟨w, v, rfl⟩
      have hv : v ∈ LinearMap.ker TY ⊔ UY := by rw [hUY.sup_eq_top]; trivial
      obtain ⟨k, hk, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      change TY u = TY (k + u)
      rw [map_add, LinearMap.mem_ker.mp hk, zero_add]
  have hrZ_bij : Function.Bijective rZ := by
    constructor
    · intro u1 u2 h12
      have h0 : TZ (u1.1 - u2.1) = 0 := by
        rw [map_sub, sub_eq_zero]
        exact congrArg Subtype.val h12
      have hmem : u1.1 - u2.1 ∈ LinearMap.ker TZ ⊓ UZ :=
        ⟨h0, Submodule.sub_mem UZ u1.2 u2.2⟩
      rw [hUZ.inf_eq_bot, Submodule.mem_bot] at hmem
      exact Subtype.ext (sub_eq_zero.mp hmem)
    · rintro ⟨w, v, rfl⟩
      have hv : v ∈ LinearMap.ker TZ ⊔ UZ := by rw [hUZ.sup_eq_top]; trivial
      obtain ⟨k, hk, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
      refine ⟨⟨u, hu⟩, Subtype.ext ?_⟩
      change TZ u = TZ (k + u)
      rw [map_add, LinearMap.mem_ker.mp hk, zero_add]
  let eY : UY ≃ₗ[F] LinearMap.range TY := LinearEquiv.ofBijective rY hrY_bij
  let eZ : UZ ≃ₗ[F] LinearMap.range TZ := LinearEquiv.ofBijective rZ hrZ_bij
  let eR : LinearMap.range TZ ≃ₗ[F] LinearMap.range TY := LinearEquiv.ofEq _ _ hrange.symm
  let eU : UZ ≃ₗ[F] UY := (eZ.trans eR).trans eY.symm
  have hker_dim : Module.finrank F (LinearMap.ker TZ) = Module.finrank F (LinearMap.ker TY) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker TY
    have h2 := LinearMap.finrank_range_add_finrank_ker TZ
    rw [hrange] at h1
    omega
  let eK : LinearMap.ker TZ ≃ₗ[F] LinearMap.ker TY := LinearEquiv.ofFinrankEq _ _ hker_dim
  let dZ : (LinearMap.ker TZ × UZ) ≃ₗ[F] (Fin j → F) := Submodule.prodEquivOfIsCompl _ _ hUZ
  let dY : (LinearMap.ker TY × UY) ≃ₗ[F] (Fin j → F) := Submodule.prodEquivOfIsCompl _ _ hUY
  let φ : (Fin j → F) ≃ₗ[F] (Fin j → F) :=
    (dZ.symm.trans (eK.prodCongr eU)).trans dY
  refine ⟨φ, fun v => ?_⟩
  obtain ⟨⟨k, u⟩, rfl⟩ := dZ.surjective v
  have hφ : φ (dZ (k, u)) = (eK k : Fin j → F) + (eU u : Fin j → F) := by
    dsimp only [φ]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, dZ.symm_apply_apply]
    rfl
  have hdZ : dZ (k, u) = (k : Fin j → F) + (u : Fin j → F) := rfl
  rw [hφ, hdZ, map_add, map_add]
  have hkY : TY (eK k : Fin j → F) = 0 := (eK k).2
  have hkZ : TZ (k : Fin j → F) = 0 := k.2
  rw [hkY, hkZ, zero_add, zero_add]
  have hu : eY (eU u) = eR (eZ u) := eY.apply_symm_apply _
  have hu_val : (eY (eU u) : Fin m → F) = (eR (eZ u) : Fin m → F) := congrArg Subtype.val hu
  exact hu_val

def nextFin (n : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

noncomputable def tableDef (n m j : ℕ) (h : Fin n → (Fin m → F)) (Y : Fin j → (Fin m → F)) : ℚ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let good := (Finset.univ : Finset (Fin n → (Fin j → F))).filter (fun x =>
    (∀ i, x i = 0 ∨ x (nextFin n i) = 0 ∨ x i = x (nextFin n i)) ∧
    (∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a))
  (good.card : ℚ)

lemma tableDef_eq_of_same_span {n m j : ℕ}
    (h : Fin n → (Fin m → F)) (Y Z : Fin j → (Fin m → F))
    (hspan : Submodule.span F (Set.range Y) = Submodule.span F (Set.range Z)) :
    tableDef n m j h Y = tableDef n m j h Z := by
  classical
  dsimp only [tableDef]
  congr 1
  obtain ⟨φ, hφ⟩ := exists_equiv_of_same_span Y Z hspan
  let M : Matrix (Fin j) (Fin j) F := LinearMap.toMatrix' φ.toLinearMap
  let Minv : Matrix (Fin j) (Fin j) F := LinearMap.toMatrix' φ.symm.toLinearMap
  have hM_mul : M * Minv = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : φ.toLinearMap.comp φ.symm.toLinearMap = LinearMap.id := by
      ext v; simp
    rw [hcomp, LinearMap.toMatrix'_id]
  have hMinv_mul : Minv * M = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have hcomp : φ.symm.toLinearMap.comp φ.toLinearMap = LinearMap.id := by
      ext v; simp
    rw [hcomp, LinearMap.toMatrix'_id]
  let ψ : (Fin j → F) ≃ₗ[F] (Fin j → F) :=
    LinearEquiv.ofLinearMap (Matrix.mulVecLin M.transpose) (Matrix.mulVecLin Minv.transpose)
      (by
        ext v b
        simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec]
        rw [← Matrix.transpose_mul, hMinv_mul, Matrix.transpose_one, Matrix.one_mulVec])
      (by
        ext v b
        simp only [LinearMap.comp_apply, LinearMap.id_apply, Matrix.mulVecLin_apply,
          Matrix.mulVec_mulVec]
        rw [← Matrix.transpose_mul, hM_mul, Matrix.transpose_one, Matrix.one_mulVec])
  have hZ_eq : ∀ b' a, Z b' a = ∑ b : Fin j, M b b' * Y b a := by
    intro b' a
    have h1 := congrFun (hφ (Pi.single b' 1)) a
    have hL : linMapOf Z (Pi.single b' 1) a = Z b' a := by
      simp [linMapOf, Pi.single_apply]
    rw [hL] at h1
    rw [← h1]
    simp only [linMapOf, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro b _
    have hMb : M b b' = φ (Pi.single b' 1) b := by
      simp [M, LinearMap.toMatrix'_apply]
    rw [hMb]
  refine Finset.card_bij (fun x _ => fun i => ψ (x i)) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    refine ⟨fun i => ?_, fun b' a => ?_⟩
    · rcases hx.1 i with h0 | h1 | heq
      · left; rw [h0, map_zero]
      · right; left; rw [h1, map_zero]
      · right; right; rw [heq]
    · have hψ : ∀ i, ψ (x i) b' = ∑ b : Fin j, M b b' * x i b := by
        intro i
        change (M.transpose.mulVec (x i)) b' = _
        simp [Matrix.mulVec, dotProduct]
      simp_rw [hψ, Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [hZ_eq b' a]
      apply Finset.sum_congr rfl
      intro b _
      rw [← hx.2 b a, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
  · intro x1 _ x2 _ h12
    ext i b
    have hi : ψ (x1 i) = ψ (x2 i) := congrFun h12 i
    exact congrFun (ψ.injective hi) b
  · intro x' hx'
    refine ⟨fun i => ψ.symm (x' i), ?_, by ext i b; simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' ⊢
    refine ⟨fun i => ?_, fun b a => ?_⟩
    · rcases hx'.1 i with h0 | h1 | heq
      · left; rw [h0, map_zero]
      · right; left; rw [h1, map_zero]
      · right; right; rw [heq]
    · have hY_eq : ∀ b a, Y b a = ∑ b' : Fin j, Minv b' b * Z b' a := by
        intro b a
        have h1 := congrFun (hφ (φ.symm (Pi.single b 1))) a
        rw [φ.apply_symm_apply] at h1
        have hL : linMapOf Y (Pi.single b 1) a = Y b a := by
          simp [linMapOf, Pi.single_apply]
        rw [hL] at h1
        rw [h1]
        simp only [linMapOf, LinearMap.coe_mk, AddHom.coe_mk]
        apply Finset.sum_congr rfl
        intro b' _
        have hMb : Minv b' b = φ.symm (Pi.single b 1) b' := by
          simp [Minv, LinearMap.toMatrix'_apply]
        rw [hMb]
      have hψs : ∀ i, ψ.symm (x' i) b = ∑ b' : Fin j, Minv b' b * x' i b' := by
        intro i
        change (Minv.transpose.mulVec (x' i)) b = _
        simp [Matrix.mulVec, dotProduct]
      simp_rw [hψs, Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [hY_eq b a]
      apply Finset.sum_congr rfl
      intro b' _
      rw [← hx'.2 b' a, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

lemma finrank_colSpace_le_bound {n m j : ℕ}
    (h : Fin n → (Fin m → F)) (Y : Fin j → (Fin m → F))
    (x : Fin n → (Fin j → F))
    (hvalid : ∀ i : Fin n, x i = 0 ∨ x (nextFin n i) = 0 ∨ x i = x (nextFin n i))
    (hsyn : ∀ b : Fin j, ∀ a : Fin m, (∑ i : Fin n, h i a * x i b) = Y b a) :
    Module.finrank F (Submodule.span F (Set.range Y)) ≤ if n = 0 then 0 else max 1 (n / 2) := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    simp only [↓reduceIte]
    have hY0 : ∀ b, Y b = 0 := by
      intro b
      ext a
      have := hsyn b a
      simp at this
      exact this.symm
    have hbot : Submodule.span F (Set.range Y) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hle : Submodule.span F (Set.range Y) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        simp [hY0 b]
      exact hle hv
    rw [hbot, finrank_bot]
  · simp only [hn0, ↓reduceIte]
    have hnext_inj : Function.Injective (nextFin n) := by
      intro i1 i2 h12
      have hv : (i1.val + 1) % n = (i2.val + 1) % n := congrArg Fin.val h12
      apply Fin.ext
      by_cases h1 : i1.val + 1 < n <;> by_cases h2 : i2.val + 1 < n
      · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hv; omega
      · have heq2 : i2.val + 1 = n := by omega
        rw [Nat.mod_eq_of_lt h1, heq2, Nat.mod_self] at hv; omega
      · have heq1 : i1.val + 1 = n := by omega
        rw [heq1, Nat.mod_self, Nat.mod_eq_of_lt h2] at hv; omega
      · omega
    by_cases hall : ∀ i : Fin n, x i ≠ 0
    · have hstep : ∀ i : Fin n, x (nextFin n i) = x i := by
        intro i
        rcases hvalid i with h0 | h1 | heq
        · exact absurd h0 (hall i)
        · exact absurd h1 (hall (nextFin n i))
        · exact heq.symm
      have hconst : ∀ i : Fin n, x i = x ⟨0, Nat.pos_of_ne_zero hn0⟩ := by
        intro i
        rcases i with ⟨k, hk⟩
        induction k with
        | zero => rfl
        | succ k ih =>
          have hk' : k < n := Nat.lt_of_succ_lt hk
          have hnx : nextFin n ⟨k, hk'⟩ = ⟨k + 1, hk⟩ := by
            apply Fin.ext
            exact Nat.mod_eq_of_lt hk
          rw [← hnx, hstep, ih hk']
      let v0 : Fin m → F := fun a => ∑ i : Fin n, h i a
      have hle : Submodule.span F (Set.range Y) ≤ Submodule.span F {v0} := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_span_singleton]
        refine ⟨x ⟨0, Nat.pos_of_ne_zero hn0⟩ b, ?_⟩
        ext a
        rw [← hsyn b a]
        simp only [Pi.smul_apply, smul_eq_mul, v0, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hconst i, mul_comm]
      have h1 : Module.finrank F (Submodule.span F (Set.range Y)) ≤
          Module.finrank F (Submodule.span F {v0}) := Submodule.finrank_mono hle
      have h2 : Module.finrank F (Submodule.span F {v0}) ≤ 1 := by
        by_cases hv0 : v0 = 0
        · rw [hv0, Submodule.span_zero_singleton, finrank_bot]; omega
        · rw [finrank_span_singleton hv0]
      omega
    · have hex0 : ∃ i0 : Fin n, x i0 = 0 := by
        by_contra hnone
        apply hall
        intro i hi
        exact hnone ⟨i, hi⟩
      obtain ⟨i0, hi0⟩ := hex0
      let E : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0 ∧ x (nextFin n i) = 0)
      have hdisj : Disjoint E (E.image (nextFin n)) := by
        rw [Finset.disjoint_left]
        intro j hj1 hj2
        rw [Finset.mem_filter] at hj1
        rw [Finset.mem_image] at hj2
        obtain ⟨i, hi, rfl⟩ := hj2
        rw [Finset.mem_filter] at hi
        exact hj1.2.1 hi.2.2
      have hE_card : E.card ≤ n / 2 := by
        have hunion : (E ∪ E.image (nextFin n)).card ≤ Fintype.card (Fin n) := Finset.card_le_univ _
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective E hnext_inj,
          Fintype.card_fin] at hunion
        omega
      have hmem_R : ∀ i : Fin n, x i ≠ 0 → x i ∈ E.image x := by
        have haux : ∀ d : ℕ, ∀ i : Fin n, (i0.val + n - i.val) % n = d → x i ≠ 0 → x i ∈ E.image x := by
          intro d
          induction d with
          | zero =>
            intro i hd hxi
            have heq : i = i0 := by
              apply Fin.ext
              have h1 : i0.val + n - i.val = n ∨ i0.val + n - i.val < n ∨ i0.val + n - i.val > n := by omega
              rcases h1 with h1 | h1 | h1
              · omega
              · rw [Nat.mod_eq_of_lt h1] at hd; omega
              · have hlt : i0.val + n - i.val - n < n := by omega
                have hmod : (i0.val + n - i.val) % n = i0.val + n - i.val - n := by
                  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt]
                rw [hmod] at hd; omega
            rw [heq] at hxi
            exact absurd hi0 hxi
          | succ d ih =>
            intro i hd hxi
            by_cases hnx : x (nextFin n i) = 0
            · exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hxi, hnx⟩, rfl⟩
            · have heq : x i = x (nextFin n i) := by
                rcases hvalid i with h0 | h1 | h2
                · exact absurd h0 hxi
                · exact absurd h1 hnx
                · exact h2
              rw [heq]
              apply ih (nextFin n i) _ hnx
              have hmod : (i0.val + n - (nextFin n i).val) % n = d := by
                have hnext_val : (nextFin n i).val = if i.val + 1 < n then i.val + 1 else 0 := by
                  show (i.val + 1) % n = _
                  split_ifs with hlt
                  · exact Nat.mod_eq_of_lt hlt
                  · have : i.val + 1 = n := by omega
                    rw [this, Nat.mod_self]
                rw [hnext_val]
                split_ifs with hlt
                · have h1 : i0.val + n - i.val = (i0.val + n - (i.val + 1)) + 1 := by omega
                  rw [h1] at hd
                  have hmod_le : (i0.val + n - (i.val + 1)) % n < n :=
                    Nat.mod_lt _ (Nat.pos_of_ne_zero hn0)
                  have hadd : (i0.val + n - (i.val + 1) + 1) % n =
                      ((i0.val + n - (i.val + 1)) % n + 1) % n :=
                    (Nat.mod_modEq (i0.val + n - (i.val + 1)) n).symm.add_right 1
                  rw [hadd] at hd
                  by_cases hwrap : (i0.val + n - (i.val + 1)) % n + 1 < n
                  · rw [Nat.mod_eq_of_lt hwrap] at hd; omega
                  · have : (i0.val + n - (i.val + 1)) % n + 1 = n := by omega
                    rw [this, Nat.mod_self] at hd; omega
                · have hi_last : i.val + 1 = n := by omega
                  have h1 : i0.val + n - i.val = i0.val + 1 := by omega
                  rw [h1] at hd
                  simp only [Nat.sub_zero, Nat.add_mod_right]
                  rw [Nat.mod_eq_of_lt i0.isLt]
                  by_cases hwrap : i0.val + 1 < n
                  · rw [Nat.mod_eq_of_lt hwrap] at hd; omega
                  · have : i0.val + 1 = n := by omega
                    rw [this, Nat.mod_self] at hd; omega
              exact hmod
        intro i hxi
        exact haux _ i rfl hxi
      let R : Finset (Fin j → F) := E.image x
      let v : (Fin j → F) → (Fin m → F) := fun c a =>
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => x i = c), h i a
      have hle : Submodule.span F (Set.range Y) ≤ Submodule.span F (v '' (R : Set (Fin j → F))) := by
        rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        rw [SetLike.mem_coe]
        have hYb : Y b = ∑ c ∈ R, c b • v c := by
          ext a
          rw [← hsyn b a, Finset.sum_apply]
          simp only [Pi.smul_apply, smul_eq_mul, v, Finset.mul_sum]
          have hnz : ∑ i : Fin n, h i a * x i b =
              ∑ i ∈ Finset.univ.filter (fun i : Fin n => x i ≠ 0), h i a * x i b := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro i _ hi
            rw [Finset.mem_filter] at hi
            have h0 : x i = 0 := by
              by_contra hne
              exact hi ⟨Finset.mem_univ i, hne⟩
            simp [h0]
          rw [hnz]
          have hfiber : Finset.univ.filter (fun i : Fin n => x i ≠ 0) =
              R.biUnion (fun c => Finset.univ.filter (fun i : Fin n => x i = c)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
            constructor
            · intro hxi
              exact ⟨x i, hmem_R i hxi, rfl⟩
            · rintro ⟨c, hc, rfl⟩
              rw [Finset.mem_image] at hc
              obtain ⟨k, hk, hkx⟩ := hc
              rw [Finset.mem_filter] at hk
              rw [← hkx]
              exact hk.2.1
          rw [hfiber, Finset.sum_biUnion]
          · apply Finset.sum_congr rfl
            intro c _
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mem_filter] at hi
            rw [hi.2, mul_comm]
          · intro c1 _ c2 _ hne
            change Disjoint _ _
            rw [Finset.disjoint_left]
            intro i hi1 hi2
            rw [Finset.mem_filter] at hi1 hi2
            exact hne (hi1.2.symm.trans hi2.2)
        rw [hYb]
        exact Submodule.sum_mem _ fun c hc =>
          Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, hc, rfl⟩)
      have h1 : Module.finrank F (Submodule.span F (Set.range Y)) ≤
          Module.finrank F (Submodule.span F ((R.image v : Finset (Fin m → F)) : Set (Fin m → F))) := by
        have himg : (v '' (R : Set (Fin j → F))) = ((R.image v : Finset (Fin m → F)) : Set (Fin m → F)) := by
          simp
        rw [← himg]
        exact Submodule.finrank_mono hle
      have h2 : Module.finrank F (Submodule.span F ((R.image v : Finset (Fin m → F)) : Set (Fin m → F))) ≤
          (R.image v).card := finrank_span_finset_le_card (R.image v)
      have h3 : (R.image v).card ≤ R.card := Finset.card_image_le
      have h4 : R.card ≤ E.card := Finset.card_image_le
      omega

lemma tableDef_eq_card_filter {n m j : ℕ} (h : Fin n → (Fin m → F)) (Y : Fin j → (Fin m → F))
    [DecidablePred (fun x : Fin n → (Fin j → F) =>
      (∀ i, x i = 0 ∨ x (nextFin n i) = 0 ∨ x i = x (nextFin n i)) ∧
      (∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a))] :
    tableDef n m j h Y = (((Finset.univ : Finset (Fin n → (Fin j → F))).filter (fun x =>
      (∀ i, x i = 0 ∨ x (nextFin n i) = 0 ∨ x i = x (nextFin n i)) ∧
      (∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a))).card : ℚ) := by
  dsimp only [tableDef]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma tableDef_vanish {n m j : ℕ}
    (h : Fin n → (Fin m → F)) (Y : Fin j → (Fin m → F))
    (hlt : (if n = 0 then 0 else max 1 (n / 2)) < Module.finrank F (Submodule.span F (Set.range Y))) :
    tableDef n m j h Y = 0 := by
  classical
  rw [tableDef_eq_card_filter]
  rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hgood
  have hle := finrank_colSpace_le_bound h Y x hgood.1 hgood.2
  omega

open Classical in
lemma ind_mem_span_tableDef (n m j : ℕ) :
    let colSpace := fun Y : Fin j → (Fin m → F) => Submodule.span F (Set.range Y)
    let bound := if n = 0 then 0 else max 1 (n / 2)
    let allSpaces : Finset (Submodule F (Fin m → F)) := Finset.univ.image colSpace
    let ind : Submodule F (Fin m → F) → ((Fin j → (Fin m → F)) → ℚ) :=
      fun W Y => if colSpace Y = W then 1 else 0
    ∀ d : ℕ, d ≤ bound → ∀ W ∈ allSpaces, Module.finrank F W = d →
      ind W ∈ Submodule.span ℚ (Set.range (tableDef n m j)) := by
  intro colSpace bound allSpaces ind d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd W hW hdW
    obtain ⟨Y0, _, hY0⟩ := Finset.mem_image.mp hW
    have hd_le_j : d ≤ j := by
      rw [← hdW, ← hY0]
      have h1 : colSpace Y0 = LinearMap.range (linMapOf Y0) := (range_linMapOf Y0).symm
      rw [h1]
      calc Module.finrank F (LinearMap.range (linMapOf Y0))
          ≤ Module.finrank F (Fin j → F) := LinearMap.finrank_range_le _
        _ = j := Module.finrank_fin_fun F
    let B : Module.Basis (Fin d) F W := (Module.finBasis F W).reindex (finCongr hdW)
    let v : Fin d → (Fin m → F) := fun r => (B r : Fin m → F)
    let h : Fin n → (Fin m → F) := fun i =>
      if hi : i.val % 2 = 0 ∧ i.val / 2 < d then v ⟨i.val / 2, hi.2⟩ else 0
    let YW : Fin j → (Fin m → F) := fun b =>
      if hb : b.val < d then v ⟨b.val, hb⟩ else 0
    have hYW_span : colSpace YW = W := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        dsimp only [YW]
        split_ifs with hb
        · exact (B ⟨b.val, hb⟩).2
        · exact Submodule.zero_mem W
      · intro w hw
        have hw_eq : w = ∑ r : Fin d, B.repr ⟨w, hw⟩ r • v r := by
          have h1 := congrArg W.subtype (B.sum_repr ⟨w, hw⟩)
          rw [map_sum] at h1
          exact h1.symm
        rw [hw_eq]
        apply Submodule.sum_mem
        intro r _
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨⟨r.val, lt_of_lt_of_le r.isLt hd_le_j⟩, ?_⟩
        simp [YW, r.isLt]
    have hpos : tableDef n m j h YW ≠ 0 := by
      rw [tableDef_eq_card_filter]
      rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      let x : Fin n → (Fin j → F) := fun i =>
        if hi : i.val % 2 = 0 ∧ i.val / 2 < d then
          Pi.single ⟨i.val / 2, lt_of_lt_of_le hi.2 hd_le_j⟩ 1
        else 0
      refine ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_, ?_⟩⟩
      · intro i
        by_cases hi : i.val % 2 = 0 ∧ i.val / 2 < d
        · by_cases hn1 : n = 1
          · right; right
            have hnext_eq : nextFin n i = i := by
              apply Fin.ext
              show (i.val + 1) % n = i.val
              have hi0 : i.val = 0 := by have := i.isLt; omega
              rw [hi0, hn1]
            rw [hnext_eq]
          · right; left
            have hd_bound : 2 * d ≤ n ∨ d = 1 := by
              by_cases hd1 : d ≤ 1
              · right; omega
              · left
                have hn0 : n ≠ 0 := by
                  intro hn0
                  have hbd : bound = 0 := if_pos hn0
                  omega
                have hbd : bound = max 1 (n / 2) := if_neg hn0
                omega
            have hlt : i.val + 1 < n := by
              rcases hd_bound with h2d | hd1 <;> omega
            have hnext_val : (nextFin n i).val = i.val + 1 := Nat.mod_eq_of_lt hlt
            dsimp only [x]
            rw [dif_neg]
            omega
        · left
          dsimp only [x]
          rw [dif_neg hi]
      · intro b a
        have hsum_eq : ∑ i : Fin n, h i a * x i b =
            ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0 ∧ i.val / 2 < d),
              h i a * x i b := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro i _ hi
          rw [Finset.mem_filter] at hi
          have hnot : ¬ (i.val % 2 = 0 ∧ i.val / 2 < d) := fun h' => hi ⟨Finset.mem_univ i, h'⟩
          simp [h, hnot]
        rw [hsum_eq]
        dsimp only [YW]
        by_cases hb : b.val < d
        · rw [dif_pos hb]
          have h2b_lt : 2 * b.val < n := by
            by_cases hd1 : d ≤ 1
            · have hb0 : b.val = 0 := by omega
              have hn0 : n ≠ 0 := by
                intro hn0
                have hbd : bound = 0 := if_pos hn0
                omega
              omega
            · have hn0 : n ≠ 0 := by
                intro hn0
                have hbd : bound = 0 := if_pos hn0
                omega
              have hbd : bound = max 1 (n / 2) := if_neg hn0
              omega
          let ib : Fin n := ⟨2 * b.val, h2b_lt⟩
          have hib_mem : ib ∈ Finset.univ.filter (fun i : Fin n => i.val % 2 = 0 ∧ i.val / 2 < d) := by
            rw [Finset.mem_filter]
            refine ⟨Finset.mem_univ ib, ?_, ?_⟩ <;> dsimp only [ib] <;> omega
          rw [Finset.sum_eq_single ib]
          · have hcond : ib.val % 2 = 0 ∧ ib.val / 2 < d := by dsimp only [ib]; omega
            simp only [h, x, dif_pos hcond, Pi.single_apply]
            have hidx : (⟨ib.val / 2, lt_of_lt_of_le hcond.2 hd_le_j⟩ : Fin j) = b := by
              apply Fin.ext; dsimp only [ib]; omega
            have hidx2 : (⟨ib.val / 2, hcond.2⟩ : Fin d) = ⟨b.val, hb⟩ := by
              apply Fin.ext; dsimp only [ib]; omega
            rw [hidx, if_pos rfl, mul_one, hidx2]
          · intro i hi hne
            rw [Finset.mem_filter] at hi
            simp only [h, x, dif_pos hi.2, Pi.single_apply]
            have hne_idx : b ≠ ⟨i.val / 2, lt_of_lt_of_le hi.2.2 hd_le_j⟩ := by
              intro heq
              apply hne
              apply Fin.ext
              have hv : b.val = i.val / 2 := congrArg Fin.val heq
              dsimp only [ib]
              omega
            rw [if_neg hne_idx, mul_zero]
          · intro hnot
            exact absurd hib_mem hnot
        · rw [dif_neg hb]
          apply Finset.sum_eq_zero
          intro i hi
          rw [Finset.mem_filter] at hi
          simp only [h, x, dif_pos hi.2, Pi.single_apply]
          have hne_idx : b ≠ ⟨i.val / 2, lt_of_lt_of_le hi.2.2 hd_le_j⟩ := by
            intro heq
            have hv : b.val = i.val / 2 := congrArg Fin.val heq
            omega
          rw [if_neg hne_idx, mul_zero]
    have hsupp : ∀ Y, tableDef n m j h Y ≠ 0 → colSpace Y ≤ W := by
      intro Y hne
      rw [tableDef_eq_card_filter] at hne
      rw [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos] at hne
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_filter] at hx
      rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      rw [SetLike.mem_coe]
      have hYb : Y b = ∑ i : Fin n, x i b • h i := by
        ext a
        rw [← hx.2.2 b a, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        simp [mul_comm]
      rw [hYb]
      apply Submodule.sum_mem
      intro i _
      apply Submodule.smul_mem
      dsimp only [h]
      split_ifs with hi
      · exact (B ⟨i.val / 2, hi.2⟩).2
      · exact Submodule.zero_mem W
    let valH : Submodule F (Fin m → F) → ℚ := fun U =>
      if hU : ∃ Y, colSpace Y = U then tableDef n m j h (Classical.choose hU) else 0
    have hdecomp : tableDef n m j h = (tableDef n m j h YW) • ind W +
        ∑ U ∈ allSpaces.filter (fun U => U < W), valH U • ind U := by
      ext Y
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      by_cases hYW' : colSpace Y = W
      · have hzero : ∑ U ∈ allSpaces.filter (fun U => U < W), valH U * ind U Y = 0 := by
          apply Finset.sum_eq_zero
          intro U hU
          rw [Finset.mem_filter] at hU
          have hne : colSpace Y ≠ U := by
            rw [hYW']
            exact ne_of_gt hU.2
          simp [ind, hne]
        rw [hzero, add_zero]
        simp only [ind, if_pos hYW', mul_one]
        exact tableDef_eq_of_same_span h Y YW (hYW'.trans hYW_span.symm)
      · simp only [ind, if_neg hYW', mul_zero, zero_add]
        by_cases hleW : colSpace Y ≤ W
        · have hltW : colSpace Y < W := lt_of_le_of_ne hleW hYW'
          have hmem : colSpace Y ∈ allSpaces.filter (fun U => U < W) :=
            Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨Y, Finset.mem_univ Y, rfl⟩, hltW⟩
          rw [Finset.sum_eq_single (colSpace Y)]
          · simp only [↓reduceIte, mul_one]
            have hex : ∃ Y', colSpace Y' = colSpace Y := ⟨Y, rfl⟩
            dsimp only [valH]
            rw [dif_pos hex]
            exact tableDef_eq_of_same_span h Y (Classical.choose hex) (Classical.choose_spec hex).symm
          · intro U _ hne
            rw [if_neg (Ne.symm hne), mul_zero]
          · intro hnot
            exact absurd hmem hnot
        · have hzero_l : tableDef n m j h Y = 0 := by
            by_contra hne
            exact hleW (hsupp Y hne)
          rw [hzero_l]
          symm
          apply Finset.sum_eq_zero
          intro U hU
          rw [Finset.mem_filter] at hU
          have hne : colSpace Y ≠ U := fun heq => hleW (heq ▸ le_of_lt hU.2)
          rw [if_neg hne, mul_zero]
    have hsum_mem : (∑ U ∈ allSpaces.filter (fun U => U < W), valH U • ind U) ∈
        Submodule.span ℚ (Set.range (tableDef n m j)) := by
      apply Submodule.sum_mem
      intro U hU
      rw [Finset.mem_filter] at hU
      apply Submodule.smul_mem
      have hlt_dim : Module.finrank F U < d := by
        rw [← hdW]
        exact Submodule.finrank_lt_finrank_of_lt hU.2
      exact ih (Module.finrank F U) hlt_dim (le_trans (le_of_lt hlt_dim) hd) U hU.1 rfl
    have hth_mem : tableDef n m j h ∈ Submodule.span ℚ (Set.range (tableDef n m j)) :=
      Submodule.subset_span ⟨h, rfl⟩
    have hsmul_mem : (tableDef n m j h YW) • ind W ∈ Submodule.span ℚ (Set.range (tableDef n m j)) := by
      have heq : (tableDef n m j h YW) • ind W =
          tableDef n m j h - ∑ U ∈ allSpaces.filter (fun U => U < W), valH U • ind U := by
        calc (tableDef n m j h YW) • ind W
            = ((tableDef n m j h YW) • ind W +
                ∑ U ∈ allSpaces.filter (fun U => U < W), valH U • ind U) -
                ∑ U ∈ allSpaces.filter (fun U => U < W), valH U • ind U :=
              (add_sub_cancel_right _ _).symm
          _ = tableDef n m j h - ∑ U ∈ allSpaces.filter (fun U => U < W), valH U • ind U := by
              rw [← hdecomp]
      rw [heq]
      exact Submodule.sub_mem _ hth_mem hsum_mem
    have hind_eq : ind W = (tableDef n m j h YW)⁻¹ • ((tableDef n m j h YW) • ind W) := by
      rw [smul_smul, inv_mul_cancel₀ hpos, one_smul]
    rw [hind_eq]
    exact Submodule.smul_mem _ _ hsmul_mem

end PEqualNP.Outside.L_lib_814_aux

open PEqualNP.Outside.L_lib_814_aux in
theorem PEqualNP.Outside.L_lib_814 : (∀ (n m j : ℕ),
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let A := Fin m → F
  let C := Fin j → F
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ : Fin n)
  let table := fun (h : Fin n → A) (Y : Fin j → A) =>
    let good := (Finset.univ : Finset (Fin n → C)).filter (fun x =>
      (∀ i, x i = 0 ∨ x (next i) = 0 ∨ x i = x (next i)) ∧
      (∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a))
    (good.card : ℚ)
  let colSpace := fun Y : Fin j → A => Submodule.span F (Set.range Y)
  let bound := if n = 0 then 0 else max 1 (n / 2)
  ∀ g : (Fin j → A) → ℚ, g ∈ Submodule.span ℚ (Set.range table) ↔
    (∀ Y Z, colSpace Y = colSpace Z → g Y = g Z) ∧
    (∀ Y, bound < Module.finrank F (colSpace Y) → g Y = 0)) := by
  intro n m j F A C next table colSpace bound g
  classical
  have htable_eq : table = tableDef n m j := rfl
  have hbd_eq : bound = if n = 0 then 0 else max 1 (n / 2) := by
    dsimp only [bound]
    split_ifs <;> rfl
  rw [htable_eq]
  constructor
  · intro hg
    let S : Submodule ℚ ((Fin j → A) → ℚ) :=
      { carrier := {f | (∀ Y Z, colSpace Y = colSpace Z → f Y = f Z) ∧
          (∀ Y, bound < Module.finrank F (colSpace Y) → f Y = 0)}
        zero_mem' := ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩, add_mem' := fun {f1 f2} hf1 hf2 =>
          ⟨fun Y Z hYZ => by simp [hf1.1 Y Z hYZ, hf2.1 Y Z hYZ],
           fun Y hY => by simp [hf1.2 Y hY, hf2.2 Y hY]⟩
        smul_mem' := fun c {f} hf =>
          ⟨fun Y Z hYZ => by simp [hf.1 Y Z hYZ],
           fun Y hY => by simp [hf.2 Y hY]⟩ }
    have hle : Submodule.span ℚ (Set.range (tableDef n m j)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨h, rfl⟩
      refine ⟨fun Y Z hYZ => tableDef_eq_of_same_span h Y Z hYZ, fun Y hY => ?_⟩
      rw [hbd_eq] at hY
      exact tableDef_vanish h Y hY
    exact hle hg
  · rintro ⟨hg_inv, hg_vanish⟩
    let allSpaces : Finset (Submodule F A) := Finset.univ.image colSpace
    let ind : Submodule F A → ((Fin j → A) → ℚ) := fun W Y => if colSpace Y = W then 1 else 0
    let valG : Submodule F A → ℚ := fun U =>
      if hU : ∃ Y, colSpace Y = U then g (Classical.choose hU) else 0
    have hg_eq : g = ∑ W ∈ allSpaces.filter (fun (W : Submodule F A) => Module.finrank F W ≤ bound),
        valG W • ind W := by
      ext Y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hle : Module.finrank F (colSpace Y) ≤ bound
      · have hmem : colSpace Y ∈ allSpaces.filter (fun (W : Submodule F A) => Module.finrank F W ≤ bound) :=
          Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨Y, Finset.mem_univ Y, rfl⟩, hle⟩
        rw [Finset.sum_eq_single (colSpace Y)]
        · simp only [ind, if_pos rfl, mul_one]
          have hex : ∃ Y', colSpace Y' = colSpace Y := ⟨Y, rfl⟩
          dsimp only [valG]
          rw [dif_pos hex]
          exact hg_inv Y (Classical.choose hex) (Classical.choose_spec hex).symm
        · intro W _ hne
          simp [ind, Ne.symm hne]
        · intro hnot
          exact absurd hmem hnot
      · have hgt : bound < Module.finrank F (colSpace Y) := Nat.lt_of_not_ge hle
        rw [hg_vanish Y hgt]
        symm
        apply Finset.sum_eq_zero
        intro W hW
        rw [Finset.mem_filter] at hW
        have hne : colSpace Y ≠ W := by
          intro heq
          rw [heq] at hgt
          omega
        simp [ind, hne]
    rw [hg_eq]
    apply Submodule.sum_mem
    intro W hW
    rw [Finset.mem_filter] at hW
    apply Submodule.smul_mem
    have hW_le : Module.finrank F W ≤ if n = 0 then 0 else max 1 (n / 2) := by
      rw [← hbd_eq]
      exact hW.2
    exact ind_mem_span_tableDef n m j (Module.finrank F W) hW_le W hW.1 rfl
