import Mathlib
import PEqualNP.Defs

-- The block transfer in namespace C388 is the merged L_lib_388 proof, and the weighted segment
-- in namespace C836 is the merged L_lib_836 proof; both are copied unchanged up to the namespace
-- (C836 calls the copied L_lib_388 statement C388main), with credit to their authors.
namespace PEqualNP.Outside.L_clb_112
namespace C388

private def b2z (b : Bool) : ZMod 2 :=
  if b then 1 else 0

private def z2b (z : ZMod 2) : Bool :=
  decide (z = 1)

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma b2z_z2b (z : ZMod 2) : b2z (z2b z) = z := by
  rcases zmod2_eq_zero_or_one z with rfl | rfl <;> decide

private lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

private lemma b2z_inj : Function.Injective b2z := by
  intro a b h
  have := congrArg z2b h
  simpa [z2b_b2z] using this

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma gf_add_self {w : ℕ} (x : GaloisField 2 w) : x + x = 0 := by
  have h2 : (2 : GaloisField 2 w) = 0 := CharP.cast_eq_zero (GaloisField 2 w) 2
  calc x + x = (2 : GaloisField 2 w) * x := (two_mul x).symm
    _ = 0 * x := by rw [h2]
    _ = 0 := zero_mul x

private lemma gf_sub_eq_add {w : ℕ} (x y : GaloisField 2 w) : x - y = x + y := by
  rw [sub_eq_iff_eq_add, add_assoc, gf_add_self, add_zero]

private lemma exists_nonzero_functional (d : ℕ) :
    ∃ φ : GaloisField 2 (d + 1) →ₗ[ZMod 2] ZMod 2, φ 1 = 1 := by
  classical
  let K := GaloisField 2 (d + 1)
  let S1 : Submodule (ZMod 2) K := Submodule.span (ZMod 2) {(1 : K)}
  have h1ne : (1 : K) ≠ 0 := one_ne_zero
  have hS1_mem : ∀ x ∈ S1, x = 0 ∨ x = 1 := by
    intro x hx
    rw [Submodule.mem_span_singleton] at hx
    obtain ⟨c, rfl⟩ := hx
    rcases zmod2_eq_zero_or_one c with rfl | rfl
    · left; exact zero_smul _ _
    · right; exact one_smul _ _
  let ψ : ↥S1 →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => if x.1 = 0 then 0 else 1
      map_add' := fun x y => by
        rcases hS1_mem x.1 x.2 with hx | hx <;> rcases hS1_mem y.1 y.2 with hy | hy
        · simp [hx, hy]
        · simp [hx, hy, h1ne]
        · simp [hx, hy, h1ne]
        · have hxy : (x + y).1 = 0 := by
            change x.1 + y.1 = 0
            rw [hx, hy, gf_add_self]
          simp only [hxy, hx, hy, h1ne, ↓reduceIte]
          decide
      map_smul' := fun c x => by
        rcases zmod2_eq_zero_or_one c with rfl | rfl
        · simp
        · simp }
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl S1
  let φ : K →ₗ[ZMod 2] ZMod 2 := ψ.comp (Submodule.projectionOnto S1 W hW)
  refine ⟨φ, ?_⟩
  have h1S : (1 : K) ∈ S1 := Submodule.subset_span (Set.mem_singleton (1 : K))
  have hproj : Submodule.projectionOnto S1 W hW (1 : K) = ⟨(1 : K), h1S⟩ :=
    Submodule.projectionOnto_apply_left hW ⟨(1 : K), h1S⟩
  change ψ (Submodule.projectionOnto S1 W hW (1 : K)) = 1
  rw [hproj]
  simp [ψ, h1ne]

private lemma span_powers_eq_top (d : ℕ)
    (α : (GaloisField 2 (d + 1))ˣ)
    (hgen : ∀ u : (GaloisField 2 (d + 1))ˣ, u ∈ Subgroup.zpowers α) :
    Submodule.span (ZMod 2) (Set.range fun j : Fin (d + 1) => (α : GaloisField 2 (d + 1)) ^ j.val) = ⊤ := by
  classical
  let w := d + 1
  let K := GaloisField 2 w
  let _instF : Fintype K := Fintype.ofFinite K
  have hwne : w ≠ 0 := Nat.succ_ne_zero d
  have hrank : Module.finrank (ZMod 2) K = w := GaloisField.finrank 2 hwne
  have hpow_span : ∃ m ≤ w,
      (α : K) ^ m ∈ Submodule.span (ZMod 2) (Set.range fun j : Fin m => (α : K) ^ j.val) := by
    let ev : (Fin (w + 1) → ZMod 2) →ₗ[ZMod 2] K :=
      { toFun := fun c => ∑ j : Fin (w + 1), c j • (α : K) ^ j.val
        map_add' := fun c1 c2 => by
          simp [add_smul, Finset.sum_add_distrib]
        map_smul' := fun r c => by
          simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_smul] }
    have hnotinj : ¬ Function.Injective ev := by
      intro hinj
      have hcard : Fintype.card (Fin (w + 1) → ZMod 2) ≤ Fintype.card K :=
        Fintype.card_le_of_injective ev hinj
      have hcardK : Fintype.card K = 2 ^ w := by
        rw [← Nat.card_eq_fintype_card]
        exact GaloisField.card 2 w hwne
      have hcardF : Fintype.card (Fin (w + 1) → ZMod 2) = 2 ^ (w + 1) := by
        simp [Fintype.card_fin, ZMod.card]
      rw [hcardK, hcardF, pow_succ] at hcard
      have hpos : 0 < 2 ^ w := Nat.two_pow_pos w
      omega
    have hker : ∃ c : Fin (w + 1) → ZMod 2, c ≠ 0 ∧ ev c = 0 := by
      have hne : LinearMap.ker ev ≠ ⊥ := by
        intro hbot
        exact hnotinj (LinearMap.ker_eq_bot.1 hbot)
      obtain ⟨c, hc_ker, hc_ne⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨c, hc_ne, LinearMap.mem_ker.1 hc_ker⟩
    obtain ⟨c, hcne, hcev⟩ := hker
    let supp : Finset (Fin (w + 1)) := Finset.univ.filter (fun j => c j ≠ 0)
    have hsupp_ne : supp.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hcne
      funext j
      by_contra hcj
      have : j ∈ supp := Finset.mem_filter.2 ⟨Finset.mem_univ j, hcj⟩
      rw [hempty] at this
      exact Finset.notMem_empty _ this
    let jmax : Fin (w + 1) := supp.max' hsupp_ne
    have hjmax_mem : jmax ∈ supp := Finset.max'_mem supp hsupp_ne
    have hcjmax : c jmax = 1 := by
      have hne0 : c jmax ≠ 0 := (Finset.mem_filter.1 hjmax_mem).2
      rcases zmod2_eq_zero_or_one (c jmax) with h0 | h1
      · exact absurd h0 hne0
      · exact h1
    refine ⟨jmax.val, Nat.le_of_lt_succ jmax.isLt, ?_⟩
    have hsum_zero : (α : K) ^ jmax.val +
        ∑ j : Fin jmax.val, c ⟨j.val, Nat.lt_trans j.isLt jmax.isLt⟩ • (α : K) ^ j.val = 0 := by
      have h1 : ev c = ∑ j ∈ supp, c j • (α : K) ^ j.val := by
        change ∑ j : Fin (w + 1), c j • (α : K) ^ j.val = _
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : c j = 0 <;> simp [h]
      have h2 : ∑ j ∈ supp, c j • (α : K) ^ j.val =
          (α : K) ^ jmax.val + ∑ j ∈ supp.erase jmax, c j • (α : K) ^ j.val := by
        rw [← Finset.add_sum_erase _ _ hjmax_mem, hcjmax, one_smul]
      have h3 : ∑ j ∈ supp.erase jmax, c j • (α : K) ^ j.val =
          ∑ j : Fin jmax.val, c ⟨j.val, Nat.lt_trans j.isLt jmax.isLt⟩ • (α : K) ^ j.val := by
        symm
        have hsub : supp.erase jmax =
            (Finset.univ.filter (fun j : Fin jmax.val =>
              c ⟨j.val, Nat.lt_trans j.isLt jmax.isLt⟩ ≠ 0)).image
              (fun j : Fin jmax.val => (⟨j.val, Nat.lt_trans j.isLt jmax.isLt⟩ : Fin (w + 1))) := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_image, supp]
          constructor
          · rintro ⟨hne, hcj⟩
            have hle : j ≤ jmax := Finset.le_max' supp j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hcj⟩)
            have hlt : j.val < jmax.val := lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
            exact ⟨⟨j.val, hlt⟩, hcj, Fin.ext rfl⟩
          · rintro ⟨k, hck, rfl⟩
            exact ⟨fun h => Nat.ne_of_lt k.isLt (congrArg Fin.val h), hck⟩
        rw [hsub, Finset.sum_image]
        · rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h : c ⟨j.val, Nat.lt_trans j.isLt jmax.isLt⟩ = 0 <;> simp [h]
        · intro a _ b _ hab
          exact Fin.ext (congrArg (Fin.val : Fin (w + 1) → ℕ) hab)
      rw [← h3, ← h2, ← h1, hcev]
    have hα_eq : (α : K) ^ jmax.val =
        ∑ j : Fin jmax.val, c ⟨j.val, Nat.lt_trans j.isLt jmax.isLt⟩ • (α : K) ^ j.val := by
      have hadd := congrArg (fun x => x + (α : K) ^ jmax.val) hsum_zero
      simp only [zero_add] at hadd
      rw [add_comm ((α : K) ^ jmax.val), add_assoc, gf_add_self, add_zero] at hadd
      exact hadd.symm
    rw [hα_eq]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨m, hmw, hαm⟩ := hpow_span
  let M : Submodule (ZMod 2) K :=
    Submodule.span (ZMod 2) (Set.range fun j : Fin m => (α : K) ^ j.val)
  have hm_pos : 1 ≤ m := by
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    have hbot : Submodule.span (ZMod 2) (Set.range fun j : Fin 0 => (α : K) ^ j.val) = ⊥ := by
      have hempty : (Set.range fun j : Fin 0 => (α : K) ^ j.val) = ∅ := Set.range_eq_empty _
      rw [hempty, Submodule.span_empty]
    rw [hbot, Submodule.mem_bot, pow_zero] at hαm
    exact one_ne_zero hαm
  have hmul_closed : ∀ x ∈ M, (α : K) * x ∈ M := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩
      have hpow : (α : K) * (α : K) ^ j.val = (α : K) ^ (j.val + 1) := (pow_succ' _ _).symm
      rw [hpow]
      by_cases hj : j.val + 1 < m
      · exact Submodule.subset_span ⟨⟨j.val + 1, hj⟩, rfl⟩
      · have heq : j.val + 1 = m := by omega
        rw [heq]
        exact hαm
    · rw [mul_zero]; exact M.zero_mem
    · intro a b _ _ ha hb
      rw [mul_add]; exact M.add_mem ha hb
    · intro r a _ ha
      rw [mul_smul_comm]; exact M.smul_mem r ha
  have hall_pow : ∀ k : ℕ, (α : K) ^ k ∈ M := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero]
      exact Submodule.subset_span ⟨⟨0, hm_pos⟩, by simp⟩
    | succ k ih =>
      rw [pow_succ']
      exact hmul_closed _ ih
  have hMtop : M = ⊤ := by
    rw [eq_top_iff]
    intro x _
    by_cases hx : x = 0
    · rw [hx]; exact M.zero_mem
    · let u : Kˣ := Units.mk0 x hx
      have hu := hgen u
      rw [Subgroup.mem_zpowers_iff] at hu
      obtain ⟨z, hz⟩ := hu
      have hord : orderOf α ≠ 0 := ne_of_gt (orderOf_pos α)
      have hzpow : ∃ k : ℕ, α ^ k = u := by
        let o := orderOf α
        have ho_pos : 0 < o := orderOf_pos α
        let k : ℕ := (z % (o : ℤ)).toNat
        have hk_mod : (k : ℤ) = z % (o : ℤ) :=
          Int.toNat_of_nonneg (Int.emod_nonneg z (Int.natCast_ne_zero.2 hord))
        have h1 : α ^ k = α ^ z := by
          rw [← zpow_natCast, hk_mod]
          have hdiv := Int.emod_add_mul_ediv z (o : ℤ)
          conv_rhs => rw [← hdiv]
          rw [zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one]
        exact ⟨k, h1.trans hz⟩
      obtain ⟨k, hk⟩ := hzpow
      have hxk : x = (α : K) ^ k := by
        have := congrArg Units.val hk
        simpa [u] using this.symm
      rw [hxk]
      exact hall_pow k
  have hMle : M ≤ Submodule.span (ZMod 2) (Set.range fun j : Fin w => (α : K) ^ j.val) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨j.val, Nat.lt_of_lt_of_le j.isLt hmw⟩, rfl⟩
  rw [eq_top_iff]
  rw [hMtop] at hMle
  exact hMle

private lemma lfsr_construction (d : ℕ) :
    let w := d + 1
    let L := 2 ^ w - 1
    let D := Fin d → Bool
    let S := Fin L × (Fin (w + 1) → Bool)
    ∃ (base : S → Bool) (port : D × D → S),
      Function.Injective port ∧ (∀ e, base (port e) = false) ∧
      ∀ (allowed : Finset (D × D)) (a b : Fin w → Bool),
        let sat := fun (x : Fin (L + d + 1) → Bool) =>
          (∀ j : Fin w, x (Fin.ofNat (L + d + 1) j.val) = a j ∧
            x (Fin.ofNat (L + d + 1) (L + j.val)) = b j) ∧
          ∀ i : Fin L,
            let s : S := (i, fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val)))
            base s = true ∨ s ∈ allowed.image port
        (Finset.univ.filter sat).card =
          (if a = b then 1 else 0) +
          (if a 0 = false ∧ b 0 = true ∧
            ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed
           then 1 else 0) := by
  classical
  let w := d + 1
  let L := 2 ^ w - 1
  let D := Fin d → Bool
  let S := Fin L × (Fin (w + 1) → Bool)
  let K := GaloisField 2 w
  let _instF : Fintype K := Fintype.ofFinite K
  have hwne : w ≠ 0 := Nat.succ_ne_zero d
  have hcardK : Fintype.card K = 2 ^ w := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 w hwne
  have hcardU : Fintype.card Kˣ = L := by
    rw [Fintype.card_units, hcardK]
  have hLpos : 0 < L := by
    have h2 : 2 ≤ 2 ^ w := by
      have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      simpa using this
    omega
  obtain ⟨α, hα⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf α = L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hα, Nat.card_eq_fintype_card, hcardU]
  have hαL : (α : K) ^ L = 1 := by
    have h1 : α ^ L = 1 := by rw [← hord]; exact pow_orderOf_eq_one α
    simpa using congrArg Units.val h1
  have hα_ne : (α : K) ≠ 0 := α.ne_zero
  obtain ⟨φ, hφ1⟩ := exists_nonzero_functional d
  have hspan := span_powers_eq_top d α hα
  let enc : K →ₗ[ZMod 2] (Fin w → ZMod 2) :=
    { toFun := fun y j => φ ((α : K) ^ j.val * y)
      map_add' := fun y1 y2 => by
        funext j
        simp [mul_add, map_add]
      map_smul' := fun r y => by
        funext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [mul_smul_comm, map_smul, smul_eq_mul] }
  have henc_inj : Function.Injective enc := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    have hφall : ∀ x : K, φ x = 0 := by
      intro x
      have hx_mem : x * y⁻¹ ∈ Submodule.span (ZMod 2) (Set.range fun j : Fin w => (α : K) ^ j.val) := by
        rw [hspan]; trivial
      have hzero : ∀ z ∈ Submodule.span (ZMod 2) (Set.range fun j : Fin w => (α : K) ^ j.val),
          φ (z * y) = 0 := by
        intro z hz
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
        · rintro _ ⟨j, rfl⟩
          exact congrFun (LinearMap.mem_ker.1 hy) j
        · rw [zero_mul, map_zero]
        · intro a b _ _ ha hb
          rw [add_mul, map_add, ha, hb, add_zero]
        · intro r a _ ha
          rw [smul_mul_assoc, map_smul, ha, smul_zero]
      have h1 := hzero (x * y⁻¹) hx_mem
      rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at h1
      exact h1
    have h0 := hφall 1
    rw [hφ1] at h0
    exact absurd h0 (by decide)
  have henc_bij : Function.Bijective enc := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨henc_inj, ?_⟩
    simp [hcardK, Fintype.card_fin, ZMod.card]
  let encEquiv : K ≃ₗ[ZMod 2] (Fin w → ZMod 2) := LinearEquiv.ofBijective enc henc_bij
  have henc_shift : ∀ (y : K) (j : Fin w) (hj : j.val + 1 < w),
      encEquiv ((α : K) * y) j = encEquiv y ⟨j.val + 1, hj⟩ := by
    intro y j hj
    change φ ((α : K) ^ j.val * ((α : K) * y)) = φ ((α : K) ^ (j.val + 1) * y)
    rw [← mul_assoc, ← pow_succ]
  let nextBit : (Fin w → ZMod 2) → ZMod 2 :=
    fun v => encEquiv ((α : K) * encEquiv.symm v) ⟨d, Nat.lt_succ_self d⟩
  let δ : K := encEquiv.symm (Pi.single ⟨d, Nat.lt_succ_self d⟩ (1 : ZMod 2))
  have hδ_ne : δ ≠ 0 := by
    intro h0
    have h1 := congrArg encEquiv h0
    simp only [δ, LinearEquiv.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 ⟨d, Nat.lt_succ_self d⟩
    simp at h2
  have hwin_step : ∀ (win : Fin (w + 1) → Bool),
      let vL : Fin w → ZMod 2 := fun j => b2z (win ⟨j.val, by omega⟩)
      let vR : Fin w → ZMod 2 := fun j => b2z (win ⟨j.val + 1, by omega⟩)
      (b2z (win ⟨w, Nat.lt_succ_self w⟩) = nextBit vL →
        encEquiv.symm vR = (α : K) * encEquiv.symm vL) ∧
      (b2z (win ⟨w, Nat.lt_succ_self w⟩) ≠ nextBit vL →
        encEquiv.symm vR = (α : K) * encEquiv.symm vL + δ) := by
    intro win vL vR
    constructor
    · intro hEq
      apply encEquiv.injective
      rw [LinearEquiv.apply_symm_apply]
      funext j
      by_cases hj : j.val + 1 < w
      · rw [henc_shift _ j hj]
        simp [vL, vR]
      · have hjd : j = ⟨d, Nat.lt_succ_self d⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          have hjlt := j.isLt
          dsimp only [w] at hj hjlt
          omega
        subst hjd
        change b2z (win ⟨d + 1, _⟩) = nextBit vL
        exact hEq
    · intro hNe
      have hplus : b2z (win ⟨w, Nat.lt_succ_self w⟩) = nextBit vL + 1 := by
        rcases zmod2_eq_zero_or_one (b2z (win ⟨w, Nat.lt_succ_self w⟩)) with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (nextBit vL) with h2 | h2
        · exact absurd (h1.trans h2.symm) hNe
        · rw [h1, h2]; decide
        · rw [h1, h2]; decide
        · exact absurd (h1.trans h2.symm) hNe
      apply encEquiv.injective
      rw [LinearEquiv.apply_symm_apply, map_add]
      simp only [δ, LinearEquiv.apply_symm_apply]
      funext j
      simp only [Pi.add_apply]
      by_cases hj : j.val + 1 < w
      · have hne_d : j ≠ ⟨d, Nat.lt_succ_self d⟩ := fun h => by
          have hv := congrArg Fin.val h
          simp only [Fin.val_mk] at hv
          dsimp only [w] at hj
          omega
        rw [henc_shift _ j hj, Pi.single_eq_of_ne hne_d, add_zero]
        simp [vL, vR]
      · have hjd : j = ⟨d, Nat.lt_succ_self d⟩ := by
          apply Fin.ext
          simp only [Fin.val_mk]
          have hjlt := j.isLt
          dsimp only [w] at hj hjlt
          omega
        subst hjd
        rw [Pi.single_eq_same]
        exact hplus
  have hstep_inj : Function.Injective (fun i : Fin L => α ^ (i.val + 1)) := by
    intro i j hEq
    have hmul : α * α ^ i.val = α * α ^ j.val := by
      simpa [pow_succ'] using hEq
    have hpow : α ^ i.val = α ^ j.val := mul_left_cancel hmul
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hlt
    · have h1 : α ^ (j.val - i.val) = 1 := by
        have hmul2 : α ^ i.val * α ^ (j.val - i.val) = α ^ i.val * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt), mul_one, hpow]
        exact mul_left_cancel hmul2
      have hle := orderOf_le_of_pow_eq_one (by omega) h1
      omega
    · have h1 : α ^ (i.val - j.val) = 1 := by
        have hmul2 : α ^ j.val * α ^ (i.val - j.val) = α ^ j.val * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hlt), mul_one, hpow]
        exact mul_left_cancel hmul2
      have hle := orderOf_le_of_pow_eq_one (by omega) h1
      omega
  have hstep_bij : Function.Bijective (fun i : Fin L => α ^ (i.val + 1)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hstep_inj, by rw [Fintype.card_fin, hcardU]⟩
  let stepEquiv : Fin L ≃ Kˣ := Equiv.ofBijective _ hstep_bij
  let base : S → Bool := fun s =>
    decide (b2z (s.2 ⟨w, Nat.lt_succ_self w⟩) = nextBit (fun j : Fin w => b2z (s.2 ⟨j.val, by omega⟩)))
  let aVec : D → (Fin w → ZMod 2) := fun u j =>
    if hj : j.val = 0 then 0 else b2z (u ⟨j.val - 1, by omega⟩)
  let bVec : D → (Fin w → ZMod 2) := fun v j =>
    if hj : j.val = 0 then 1 else b2z (v ⟨j.val - 1, by omega⟩)
  let diffK : D × D → K := fun uv =>
    encEquiv.symm (bVec uv.2) + encEquiv.symm (aVec uv.1)
  have hdiff_ne : ∀ uv : D × D, diffK uv ≠ 0 := by
    intro uv h0
    have h1 : encEquiv.symm (bVec uv.2) = encEquiv.symm (aVec uv.1) := by
      have hadd := congrArg (fun x => x + encEquiv.symm (aVec uv.1)) h0
      simp only [diffK, zero_add, add_assoc] at hadd
      rw [gf_add_self, add_zero] at hadd
      exact hadd
    have h2 := congrFun (congrArg encEquiv h1) 0
    simp [aVec, bVec] at h2
  let portTime : D × D → Fin L := fun uv =>
    stepEquiv.symm (Units.mk0 (δ * (diffK uv)⁻¹) (mul_ne_zero hδ_ne (inv_ne_zero (hdiff_ne uv))))
  have hportTime_spec : ∀ uv : D × D,
      ((α : K) ^ ((portTime uv).val + 1))⁻¹ * δ = diffK uv := by
    intro uv
    have h1 : stepEquiv (portTime uv) =
        Units.mk0 (δ * (diffK uv)⁻¹) (mul_ne_zero hδ_ne (inv_ne_zero (hdiff_ne uv))) :=
      Equiv.apply_symm_apply stepEquiv _
    have h2 : (α : K) ^ ((portTime uv).val + 1) = δ * (diffK uv)⁻¹ := by
      have := congrArg Units.val h1
      simpa [stepEquiv] using this
    rw [h2, mul_inv, inv_inv, mul_comm δ⁻¹ (diffK uv), mul_assoc, inv_mul_cancel₀ hδ_ne, mul_one]
  let portPhys : D × D → (Fin w → ZMod 2) := fun uv =>
    encEquiv ((α : K) ^ (portTime uv).val * encEquiv.symm (aVec uv.1))
  let portWin : D × D → (Fin (w + 1) → Bool) := fun uv k =>
    if hk : k.val < w then z2b (portPhys uv ⟨k.val, hk⟩)
    else z2b (nextBit (portPhys uv) + 1)
  let port : D × D → S := fun uv => (portTime uv, portWin uv)
  have hbase_port : ∀ uv : D × D, base (port uv) = false := by
    intro uv
    have hL : (fun j : Fin w => b2z (portWin uv ⟨j.val, by omega⟩)) = portPhys uv := by
      funext j
      simp [portWin, j.isLt, b2z_z2b]
    have hR : b2z (portWin uv ⟨w, Nat.lt_succ_self w⟩) = nextBit (portPhys uv) + 1 := by
      simp [portWin, b2z_z2b]
    simp only [base, port, hL, hR, decide_eq_false_iff_not]
    intro hEq
    rcases zmod2_eq_zero_or_one (nextBit (portPhys uv)) with h | h <;> rw [h] at hEq <;> exact absurd hEq (by decide)
  have hport_inj : Function.Injective port := by
    intro uv1 uv2 hEq
    have htime : portTime uv1 = portTime uv2 := congrArg Prod.fst hEq
    have hwin : portWin uv1 = portWin uv2 := congrArg Prod.snd hEq
    have hphys : portPhys uv1 = portPhys uv2 := by
      funext j
      have hj := congrFun hwin ⟨j.val, by omega⟩
      simp only [portWin, j.isLt, ↓reduceDIte] at hj
      have := congrArg b2z hj
      simpa [b2z_z2b] using this
    have ha_eq : aVec uv1.1 = aVec uv2.1 := by
      have h1 : (α : K) ^ (portTime uv1).val * encEquiv.symm (aVec uv1.1) =
          (α : K) ^ (portTime uv2).val * encEquiv.symm (aVec uv2.1) :=
        encEquiv.injective hphys
      rw [htime] at h1
      exact encEquiv.symm.injective (mul_left_cancel₀ (pow_ne_zero _ hα_ne) h1)
    have hu : uv1.1 = uv2.1 := by
      funext j
      have hj := congrFun ha_eq j.succ
      simp only [aVec, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hj
      exact b2z_inj hj
    have hdiff_eq : diffK uv1 = diffK uv2 := by
      rw [← hportTime_spec uv1, ← hportTime_spec uv2, htime]
    have hb_eq : bVec uv1.2 = bVec uv2.2 := by
      simp only [diffK, hu] at hdiff_eq
      exact encEquiv.symm.injective (add_right_cancel hdiff_eq)
    have hv : uv1.2 = uv2.2 := by
      funext j
      have hj := congrFun hb_eq j.succ
      simp only [bVec, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hj
      exact b2z_inj hj
    exact Prod.ext hu hv
  refine ⟨base, port, hport_inj, hbase_port, ?_⟩
  intro allowed a b
  let sat := fun (x : Fin (L + d + 1) → Bool) =>
    (∀ j : Fin w, x (Fin.ofNat (L + d + 1) j.val) = a j ∧
      x (Fin.ofNat (L + d + 1) (L + j.val)) = b j) ∧
    ∀ i : Fin L,
      let s : S := (i, fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val)))
      base s = true ∨ s ∈ allowed.image port
  let winOf : (Fin (L + d + 1) → Bool) → Fin (L + 1) → (Fin w → ZMod 2) :=
    fun x i j => b2z (x (Fin.ofNat (L + d + 1) (i.val + j.val)))
  let logOf : (Fin (L + d + 1) → Bool) → Fin (L + 1) → K :=
    fun x i => ((α : K) ^ i.val)⁻¹ * encEquiv.symm (winOf x i)
  have hlog_ord : ∀ (x : Fin (L + d + 1) → Bool) (i : Fin L),
      base (i, fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))) = true →
      logOf x ⟨i.val + 1, by omega⟩ = logOf x ⟨i.val, by omega⟩ := by
    intro x i hbase
    let sw : Fin (w + 1) → Bool := fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))
    have hstep := (hwin_step sw).1 (of_decide_eq_true hbase)
    have hL : (fun j : Fin w => b2z (sw ⟨j.val, by omega⟩)) = winOf x ⟨i.val, by omega⟩ := rfl
    have hR : (fun j : Fin w => b2z (sw ⟨j.val + 1, by omega⟩)) = winOf x ⟨i.val + 1, by omega⟩ := by
      funext j
      simp only [sw, winOf]
      congr 2
      apply Fin.ext
      simp only [Fin.val_ofNat]
      congr 1
      omega
    rw [hL, hR] at hstep
    simp only [logOf, hstep]
    rw [pow_succ', mul_inv, mul_comm (α : K)⁻¹ _, mul_assoc, inv_mul_cancel_left₀ hα_ne]
  have hlog_port : ∀ (x : Fin (L + d + 1) → Bool) (i : Fin L) (uv : D × D),
      (i, fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))) = port uv →
      i = portTime uv ∧
      logOf x ⟨i.val, by omega⟩ = encEquiv.symm (aVec uv.1) ∧
      logOf x ⟨i.val + 1, by omega⟩ = encEquiv.symm (bVec uv.2) := by
    intro x i uv hEq
    let sw : Fin (w + 1) → Bool := fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))
    have hi : i = portTime uv := congrArg Prod.fst hEq
    have hwin : sw = portWin uv := congrArg Prod.snd hEq
    have hnotb : base (i, sw) = false := by
      rw [hEq]; exact hbase_port uv
    have hne : b2z (sw ⟨w, Nat.lt_succ_self w⟩) ≠
        nextBit (fun j : Fin w => b2z (sw ⟨j.val, by omega⟩)) :=
      of_decide_eq_false hnotb
    have hstep := (hwin_step sw).2 hne
    have hL : (fun j : Fin w => b2z (sw ⟨j.val, by omega⟩)) =
        winOf x ⟨i.val, by omega⟩ := rfl
    have hR : (fun j : Fin w => b2z (sw ⟨j.val + 1, by omega⟩)) =
        winOf x ⟨i.val + 1, by omega⟩ := by
      funext j
      simp only [sw, winOf]
      congr 2
      apply Fin.ext
      simp only [Fin.val_ofNat]
      congr 1
      omega
    rw [hL, hR] at hstep
    have hwinL_eq : winOf x ⟨i.val, by omega⟩ = portPhys uv := by
      funext j
      have hj := congrFun hwin ⟨j.val, by omega⟩
      simp only [portWin, j.isLt, ↓reduceDIte] at hj
      change b2z (sw ⟨j.val, by omega⟩) = portPhys uv j
      rw [hj, b2z_z2b]
    have hlogi : logOf x ⟨i.val, by omega⟩ = encEquiv.symm (aVec uv.1) := by
      simp only [logOf]
      rw [hwinL_eq]
      simp only [portPhys, LinearEquiv.symm_apply_apply, hi]
      rw [inv_mul_cancel_left₀ (pow_ne_zero _ hα_ne)]
    have hlogi1 : logOf x ⟨i.val + 1, by omega⟩ = encEquiv.symm (bVec uv.2) := by
      simp only [logOf, hstep, mul_add]
      have h1 : ((α : K) ^ (i.val + 1))⁻¹ * ((α : K) * encEquiv.symm (winOf x ⟨i.val, by omega⟩)) =
          encEquiv.symm (aVec uv.1) := by
        rw [pow_succ', mul_inv, mul_comm (α : K)⁻¹ _, mul_assoc, inv_mul_cancel_left₀ hα_ne]
        exact hlogi
      have h2 : ((α : K) ^ (i.val + 1))⁻¹ * δ = diffK uv := by
        rw [hi]; exact hportTime_spec uv
      rw [h1, h2]
      simp only [diffK]
      rw [add_comm (encEquiv.symm (bVec uv.2)), ← add_assoc, gf_add_self, zero_add]
    exact ⟨hi, hlogi, hlogi1⟩
  have htag_stick : ∀ (x : Fin (L + d + 1) → Bool), sat x →
      ∀ (k : ℕ) (hk : k ≤ L),
        (encEquiv (logOf x ⟨k, by omega⟩)) 0 = 1 →
        ∀ (r : ℕ) (hr : k + r ≤ L), logOf x ⟨k + r, by omega⟩ = logOf x ⟨k, by omega⟩ := by
    intro x hsat k hk hbit1 r
    induction r with
    | zero =>
      intro _
      rfl
    | succ r ih =>
      intro hr
      have hprev := ih (by omega)
      have hstep_sat := hsat.2 ⟨k + r, by omega⟩
      rcases hstep_sat with hbase | himg
      · exact (hlog_ord x ⟨k + r, by omega⟩ hbase).trans hprev
      · exfalso
        obtain ⟨uv, _, huv⟩ := Finset.mem_image.1 himg
        have hpt := hlog_port x ⟨k + r, by omega⟩ uv huv.symm
        have h0 := congrFun (congrArg encEquiv (hprev.symm.trans hpt.2.1)) 0
        rw [hbit1] at h0
        simp [aVec] at h0
  have hlog_det : ∀ (x1 x2 : Fin (L + d + 1) → Bool),
      (∀ i : Fin (L + 1), logOf x1 i = logOf x2 i) → x1 = x2 := by
    intro x1 x2 hlog
    funext idx
    by_cases hi : idx.val < L
    · have h1 := hlog ⟨idx.val, by omega⟩
      have hwin : winOf x1 ⟨idx.val, by omega⟩ = winOf x2 ⟨idx.val, by omega⟩ := by
        exact encEquiv.symm.injective (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hα_ne)) h1)
      have h0 := congrFun hwin 0
      simp only [winOf, Fin.val_zero, add_zero] at h0
      have hidx : Fin.ofNat (L + d + 1) idx.val = idx := by
        apply Fin.ext
        simp
      rw [hidx] at h0
      exact b2z_inj h0
    · have h1 := hlog ⟨L, Nat.lt_succ_self L⟩
      have hwin : winOf x1 ⟨L, Nat.lt_succ_self L⟩ = winOf x2 ⟨L, Nat.lt_succ_self L⟩ := by
        exact encEquiv.symm.injective (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ hα_ne)) h1)
      have hj := congrFun hwin ⟨idx.val - L, by omega⟩
      simp only [winOf] at hj
      have hidx : Fin.ofNat (L + d + 1) (L + (idx.val - L)) = idx := by
        apply Fin.ext
        have : L + (idx.val - L) = idx.val := by omega
        rw [Fin.val_ofNat, this, Nat.mod_eq_of_lt idx.isLt]
      rw [hidx] at hj
      exact b2z_inj hj
  have hlog_sat_start : ∀ (x : Fin (L + d + 1) → Bool), sat x →
      logOf x ⟨0, by omega⟩ = encEquiv.symm (fun j => b2z (a j)) := by
    intro x hsat
    simp only [logOf, pow_zero, inv_one, one_mul]
    congr 1
    funext j
    simp only [winOf, zero_add]
    rw [(hsat.1 j).1]
  have hlog_sat_end : ∀ (x : Fin (L + d + 1) → Bool), sat x →
      logOf x ⟨L, Nat.lt_succ_self L⟩ = encEquiv.symm (fun j => b2z (b j)) := by
    intro x hsat
    simp only [logOf, hαL, inv_one, one_mul]
    congr 1
    funext j
    simp only [winOf]
    rw [(hsat.1 j).2]
  have hord_mk : a = b → ∃ x : Fin (L + d + 1) → Bool, sat x ∧
      ∀ i : Fin (L + 1), logOf x i = encEquiv.symm (fun j => b2z (a j)) := by
    intro hab
    let y0 : K := encEquiv.symm (fun j => b2z (a j))
    let x : Fin (L + d + 1) → Bool := fun idx => z2b (φ ((α : K) ^ idx.val * y0))
    have hwin_x : ∀ i : Fin (L + 1), winOf x i = encEquiv ((α : K) ^ i.val * y0) := by
      intro i
      funext j
      simp only [winOf, x, b2z_z2b]
      have hlt : i.val + j.val < L + d + 1 := by omega
      have hval : (Fin.ofNat (L + d + 1) (i.val + j.val)).val = i.val + j.val := by
        simp [Nat.mod_eq_of_lt hlt]
      rw [hval, pow_add, mul_comm ((α : K) ^ i.val), mul_assoc]
      rfl
    have hlog_x : ∀ i : Fin (L + 1), logOf x i = y0 := by
      intro i
      simp only [logOf, hwin_x i, LinearEquiv.symm_apply_apply]
      rw [inv_mul_cancel_left₀ (pow_ne_zero _ hα_ne)]
    refine ⟨x, ⟨?_, ?_⟩, hlog_x⟩
    · intro j
      constructor
      · have h0 := congrFun (hwin_x ⟨0, by omega⟩) j
        simp only [winOf, zero_add, pow_zero, one_mul, y0, LinearEquiv.apply_symm_apply] at h0
        exact b2z_inj h0
      · have hL := congrFun (hwin_x ⟨L, Nat.lt_succ_self L⟩) j
        simp only [winOf, hαL, one_mul, y0, LinearEquiv.apply_symm_apply] at hL
        rw [← hab]
        exact b2z_inj hL
    · intro i
      left
      simp only [base, decide_eq_true_eq]
      have hL : (fun j : Fin w => b2z (x (Fin.ofNat (L + d + 1) (i.val + j.val)))) =
          encEquiv ((α : K) ^ i.val * y0) := hwin_x ⟨i.val, by omega⟩
      rw [hL]
      have hlt : i.val + w < L + d + 1 := by omega
      have hval : (Fin.ofNat (L + d + 1) (i.val + w)).val = i.val + w := by
        simp [Nat.mod_eq_of_lt hlt]
      simp only [x, hval, b2z_z2b, nextBit, LinearEquiv.symm_apply_apply]
      change φ ((α : K) ^ (i.val + (d + 1)) * y0) = φ ((α : K) ^ d * ((α : K) * ((α : K) ^ i.val * y0)))
      congr 1
      ring
  have hjump_mk : a 0 = false → b 0 = true →
      ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed →
      ∃ x : Fin (L + d + 1) → Bool, sat x ∧
        ∀ i : Fin (L + 1), logOf x i =
          if i.val ≤ (portTime ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ))).val
          then encEquiv.symm (fun j => b2z (a j))
          else encEquiv.symm (fun j => b2z (b j)) := by
    intro ha0 hb0 hall
    let u : D := fun j => a j.succ
    let v : D := fun j => b j.succ
    let uv : D × D := (u, v)
    let t0 : Fin L := portTime uv
    have ha_eq : (fun j : Fin w => b2z (a j)) = aVec u := by
      funext j
      cases j using Fin.cases with
      | zero => simp [aVec, ha0, b2z]
      | succ j => simp [aVec, u]
    have hb_eq : (fun j : Fin w => b2z (b j)) = bVec v := by
      funext j
      cases j using Fin.cases with
      | zero => simp [bVec, hb0, b2z]
      | succ j => simp [bVec, v]
    let ya : K := encEquiv.symm (aVec u)
    let yb : K := encEquiv.symm (bVec v)
    let x : Fin (L + d + 1) → Bool := fun idx =>
      if idx.val < t0.val + w then z2b (φ ((α : K) ^ idx.val * ya))
      else z2b (φ ((α : K) ^ idx.val * yb))
    have hdiff_phi : ∀ k : ℕ, k < d → φ ((α : K) ^ (t0.val + 1 + k) * diffK uv) = 0 := by
      intro k hk
      have h1 : (α : K) ^ (t0.val + 1 + k) * diffK uv = (α : K) ^ k * δ := by
        rw [pow_add, mul_assoc, ← hportTime_spec uv]
        have hne_pow : (α : K) ^ (t0.val + 1) ≠ 0 := pow_ne_zero _ hα_ne
        change (α : K) ^ (t0.val + 1) * ((α : K) ^ k * (((α : K) ^ (t0.val + 1))⁻¹ * δ)) = (α : K) ^ k * δ
        rw [mul_comm ((α : K) ^ k), ← mul_assoc, mul_inv_cancel_left₀ hne_pow, mul_comm]
      rw [h1]
      have h2 : encEquiv δ ⟨k, by omega⟩ = 0 := by
        simp only [δ, LinearEquiv.apply_symm_apply]
        have hne : (⟨k, by omega⟩ : Fin w) ≠ ⟨d, Nat.lt_succ_self d⟩ := by
          intro h
          have hv : k = d := congrArg Fin.val h
          omega
        exact Pi.single_eq_of_ne hne _
      exact h2
    have hdiff_phi_d : φ ((α : K) ^ (t0.val + w) * diffK uv) = 1 := by
      have h1 : (α : K) ^ (t0.val + w) * diffK uv = (α : K) ^ d * δ := by
        have htw : t0.val + w = d + (t0.val + 1) := by omega
        rw [htw, pow_add, mul_assoc, ← hportTime_spec uv]
        rw [mul_inv_cancel_left₀ (pow_ne_zero _ hα_ne)]
      rw [h1]
      have h2 : encEquiv δ ⟨d, Nat.lt_succ_self d⟩ = 1 := by
        simp [δ]
      exact h2
    have hagree : ∀ idx : Fin (L + d + 1), t0.val + 1 ≤ idx.val → idx.val < t0.val + w →
        φ ((α : K) ^ idx.val * ya) = φ ((α : K) ^ idx.val * yb) := by
      intro idx hlo hhi
      have hsub : φ ((α : K) ^ idx.val * yb) + φ ((α : K) ^ idx.val * ya) = 0 := by
        rw [← map_add, ← mul_add]
        have : idx.val = t0.val + 1 + (idx.val - (t0.val + 1)) := by omega
        rw [this]
        exact hdiff_phi (idx.val - (t0.val + 1)) (by omega)
      have hadd := congrArg (fun z => z + φ ((α : K) ^ idx.val * ya)) hsub
      simp only [zero_add, add_assoc, zmod2_add_self, add_zero] at hadd
      exact hadd.symm
    have hwin_le : ∀ i : Fin (L + 1), i.val ≤ t0.val →
        winOf x i = encEquiv ((α : K) ^ i.val * ya) := by
      intro i hi
      funext j
      have hlt : i.val + j.val < t0.val + w := by omega
      have hltN : i.val + j.val < L + d + 1 := by omega
      have hval : (Fin.ofNat (L + d + 1) (i.val + j.val)).val = i.val + j.val := by
        simp [Nat.mod_eq_of_lt hltN]
      simp only [winOf, x, hval, hlt, ↓reduceIte, b2z_z2b]
      rw [pow_add, mul_comm ((α : K) ^ i.val), mul_assoc]
      rfl
    have hwin_gt : ∀ i : Fin (L + 1), t0.val < i.val →
        winOf x i = encEquiv ((α : K) ^ i.val * yb) := by
      intro i hi
      funext j
      have hltN : i.val + j.val < L + d + 1 := by omega
      have hval : (Fin.ofNat (L + d + 1) (i.val + j.val)).val = i.val + j.val := by
        simp [Nat.mod_eq_of_lt hltN]
      simp only [winOf, x, hval]
      by_cases hlt : i.val + j.val < t0.val + w
      · simp only [hlt, ↓reduceIte, b2z_z2b]
        have hag := hagree (Fin.ofNat (L + d + 1) (i.val + j.val)) (by rw [hval]; omega) (by rw [hval]; exact hlt)
        rw [hval] at hag
        rw [hag, pow_add, mul_comm ((α : K) ^ i.val), mul_assoc]
        rfl
      · simp only [hlt, ↓reduceIte, b2z_z2b]
        rw [pow_add, mul_comm ((α : K) ^ i.val), mul_assoc]
        rfl
    have hlog_x : ∀ i : Fin (L + 1), logOf x i =
        if i.val ≤ t0.val then encEquiv.symm (fun j => b2z (a j))
        else encEquiv.symm (fun j => b2z (b j)) := by
      intro i
      by_cases hi : i.val ≤ t0.val
      · simp only [hi, ↓reduceIte, logOf, hwin_le i hi, LinearEquiv.symm_apply_apply, ha_eq]
        exact inv_mul_cancel_left₀ (pow_ne_zero _ hα_ne) ya
      · simp only [hi, ↓reduceIte, logOf, hwin_gt i (by omega), LinearEquiv.symm_apply_apply, hb_eq]
        exact inv_mul_cancel_left₀ (pow_ne_zero _ hα_ne) yb
    refine ⟨x, ⟨?_, ?_⟩, hlog_x⟩
    · intro j
      constructor
      · have h0 := congrFun (hwin_le ⟨0, by omega⟩ (Nat.zero_le _)) j
        simp only [winOf, zero_add, pow_zero, one_mul, ya, LinearEquiv.apply_symm_apply, ← ha_eq] at h0
        exact b2z_inj h0
      · have hL := congrFun (hwin_gt ⟨L, Nat.lt_succ_self L⟩ t0.isLt) j
        simp only [winOf, hαL, one_mul, yb, LinearEquiv.apply_symm_apply, ← hb_eq] at hL
        exact b2z_inj hL
    · intro i
      by_cases hit : i = t0
      · right
        refine Finset.mem_image.2 ⟨uv, hall, ?_⟩
        apply Prod.ext
        · exact hit.symm
        · funext k
          by_cases hk : k.val < w
          · have hlt : i.val + k.val < t0.val + w := by rw [hit]; omega
            have hltN : i.val + k.val < L + d + 1 := by omega
            have hval : (Fin.ofNat (L + d + 1) (i.val + k.val)).val = i.val + k.val := by
              simp [Nat.mod_eq_of_lt hltN]
            simp only [port, portWin, hk, ↓reduceDIte, x, hval, hlt, ↓reduceIte, portPhys]
            change z2b (φ ((α : K) ^ k.val * ((α : K) ^ t0.val * ya))) =
              z2b (φ ((α : K) ^ (i.val + k.val) * ya))
            congr 2
            rw [hit, pow_add]
            ring
          · have hkw : k.val = w := by omega
            have hnot : ¬ (i.val + k.val < t0.val + w) := by rw [hit, hkw]; omega
            have hltN : i.val + k.val < L + d + 1 := by omega
            have hval : (Fin.ofNat (L + d + 1) (i.val + k.val)).val = t0.val + w := by
              rw [hit, hkw]; simp [Nat.mod_eq_of_lt (by omega : t0.val + w < L + d + 1)]
            simp only [port, portWin, hk, ↓reduceDIte, x, hval, lt_irrefl, ↓reduceIte]
            congr 1
            have hnext : nextBit (portPhys uv) = φ ((α : K) ^ (t0.val + w) * ya) := by
              simp only [nextBit, portPhys, LinearEquiv.symm_apply_apply]
              change φ ((α : K) ^ d * ((α : K) * ((α : K) ^ t0.val * ya))) = _
              congr 1
              have htw : t0.val + w = d + 1 + t0.val := by omega
              rw [htw, pow_add, pow_add, pow_one]
              ring
            rw [hnext, ← hdiff_phi_d]
            simp only [diffK, ya, yb]
            rw [mul_add, map_add, add_comm (φ ((α : K) ^ (t0.val + w) * yb)), ← add_assoc,
              zmod2_add_self, zero_add]
      · left
        simp only [base, decide_eq_true_eq]
        by_cases hlt : i.val < t0.val
        · have hL : (fun j : Fin w => b2z (x (Fin.ofNat (L + d + 1) (i.val + j.val)))) =
              encEquiv ((α : K) ^ i.val * ya) := hwin_le ⟨i.val, by omega⟩ (le_of_lt hlt)
          rw [hL]
          have hltw : i.val + w < t0.val + w := by omega
          have hltN : i.val + w < L + d + 1 := by omega
          have hval : (Fin.ofNat (L + d + 1) (i.val + w)).val = i.val + w := by
            simp [Nat.mod_eq_of_lt hltN]
          simp only [x, hval, hltw, ↓reduceIte, b2z_z2b, nextBit, LinearEquiv.symm_apply_apply]
          change φ ((α : K) ^ (i.val + (d + 1)) * ya) = φ ((α : K) ^ d * ((α : K) * ((α : K) ^ i.val * ya)))
          congr 1
          ring
        · have hgt : t0.val < i.val := lt_of_le_of_ne (Nat.le_of_not_lt hlt)
            (fun h => hit (Fin.ext h.symm))
          have hL : (fun j : Fin w => b2z (x (Fin.ofNat (L + d + 1) (i.val + j.val)))) =
              encEquiv ((α : K) ^ i.val * yb) := hwin_gt ⟨i.val, by omega⟩ hgt
          rw [hL]
          have hnotw : ¬ (i.val + w < t0.val + w) := by omega
          have hltN : i.val + w < L + d + 1 := by omega
          have hval : (Fin.ofNat (L + d + 1) (i.val + w)).val = i.val + w := by
            simp [Nat.mod_eq_of_lt hltN]
          simp only [x, hval, hnotw, ↓reduceIte, b2z_z2b, nextBit, LinearEquiv.symm_apply_apply]
          change φ ((α : K) ^ (i.val + (d + 1)) * yb) = φ ((α : K) ^ d * ((α : K) * ((α : K) ^ i.val * yb)))
          congr 1
          ring
  have hsat_class : ∀ (x : Fin (L + d + 1) → Bool), sat x →
      (a = b ∧ ∀ i : Fin (L + 1), logOf x i = encEquiv.symm (fun j => b2z (a j))) ∨
      (a 0 = false ∧ b 0 = true ∧
        ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed ∧
        ∀ i : Fin (L + 1), logOf x i =
          if i.val ≤ (portTime ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ))).val
          then encEquiv.symm (fun j => b2z (a j))
          else encEquiv.symm (fun j => b2z (b j))) := by
    intro x hsat
    by_cases hall_base : ∀ i : Fin L,
        base (i, fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val))) = true
    · left
      have hconst : ∀ k : ℕ, (hk : k ≤ L) →
          logOf x ⟨k, by omega⟩ = encEquiv.symm (fun j => b2z (a j)) := by
        intro k
        induction k with
        | zero =>
          intro _
          exact hlog_sat_start x hsat
        | succ k ih =>
          intro hk
          exact (hlog_ord x ⟨k, by omega⟩ (hall_base ⟨k, by omega⟩)).trans (ih (by omega))
      have hab : a = b := by
        have hL := (hconst L le_rfl).symm.trans (hlog_sat_end x hsat)
        have hvec := encEquiv.symm.injective hL
        funext j
        exact b2z_inj (congrFun hvec j)
      exact ⟨hab, fun i => hconst i.val (Nat.le_of_lt_succ i.isLt)⟩
    · right
      push Not at hall_base
      have hex_nat : ∃ k : ℕ, ∃ hk : k < L,
          base (⟨k, hk⟩, fun offset => x (Fin.ofNat (L + d + 1) (k + offset.val))) ≠ true := by
        obtain ⟨i, hi⟩ := hall_base
        exact ⟨i.val, i.isLt, hi⟩
      let k0 := Nat.find hex_nat
      obtain ⟨hk0, hnotb0⟩ := Nat.find_spec hex_nat
      have hpre_base : ∀ k < k0, (hk : k < L) →
          base (⟨k, hk⟩, fun offset => x (Fin.ofNat (L + d + 1) (k + offset.val))) = true := by
        intro k hk hkL
        by_contra hne
        exact Nat.find_min hex_nat hk ⟨hkL, hne⟩
      have hpre_const : ∀ k ≤ k0, (hk : k ≤ L) →
          logOf x ⟨k, by omega⟩ = encEquiv.symm (fun j => b2z (a j)) := by
        intro k
        induction k with
        | zero =>
          intro _ _
          exact hlog_sat_start x hsat
        | succ k ih =>
          intro hkk0 hkL
          exact (hlog_ord x ⟨k, by omega⟩ (hpre_base k (by omega) (by omega))).trans
            (ih (by omega) (by omega))
      have hstep0 := hsat.2 ⟨k0, hk0⟩
      have himg0 : (⟨k0, hk0⟩, fun offset => x (Fin.ofNat (L + d + 1) (k0 + offset.val))) ∈
          allowed.image port := hstep0.resolve_left hnotb0
      obtain ⟨uv, huv_all, huv_eq⟩ := Finset.mem_image.1 himg0
      obtain ⟨htime0, hlog0, hlog1⟩ := hlog_port x ⟨k0, hk0⟩ uv huv_eq.symm
      have ha_vec : (fun j : Fin w => b2z (a j)) = aVec uv.1 := by
        exact encEquiv.symm.injective ((hpre_const k0 le_rfl (le_of_lt hk0)).symm.trans hlog0)
      have ha0 : a 0 = false := by
        have h0 := congrFun ha_vec 0
        simp only [aVec, Fin.val_zero, ↓reduceDIte] at h0
        cases h : a 0
        · rfl
        · simp [h, b2z] at h0
      have hu_eq : (fun j : Fin d => a j.succ) = uv.1 := by
        funext j
        have hj := congrFun ha_vec j.succ
        simp only [aVec, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hj
        exact b2z_inj hj
      have hbit1 : (encEquiv (logOf x ⟨k0 + 1, by omega⟩)) 0 = 1 := by
        rw [hlog1, LinearEquiv.apply_symm_apply]
        simp [bVec]
      have hpost_const : ∀ k, k0 < k → (hk : k ≤ L) →
          logOf x ⟨k, by omega⟩ = encEquiv.symm (bVec uv.2) := by
        intro k hgt hkL
        have h1 := htag_stick x hsat (k0 + 1) (by omega) hbit1 (k - (k0 + 1)) (by omega)
        have hidx : (⟨k0 + 1 + (k - (k0 + 1)), by omega⟩ : Fin (L + 1)) = ⟨k, by omega⟩ :=
          Fin.ext (by simp only [Fin.val_mk]; omega)
        rw [hidx] at h1
        exact h1.trans hlog1
      have hb_vec : (fun j : Fin w => b2z (b j)) = bVec uv.2 := by
        exact encEquiv.symm.injective ((hlog_sat_end x hsat).symm.trans
          (hpost_const L hk0 le_rfl))
      have hb0 : b 0 = true := by
        have h0 := congrFun hb_vec 0
        simp only [bVec, Fin.val_zero, ↓reduceDIte] at h0
        cases h : b 0
        · simp [h, b2z] at h0
        · rfl
      have hv_eq : (fun j : Fin d => b j.succ) = uv.2 := by
        funext j
        have hj := congrFun hb_vec j.succ
        simp only [bVec, Fin.val_succ, Nat.succ_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hj
        exact b2z_inj hj
      have huv_id : ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) = uv :=
        Prod.ext hu_eq hv_eq
      rw [huv_id]
      have hk0_eq : k0 = (portTime uv).val := congrArg Fin.val htime0
      refine ⟨ha0, hb0, huv_all, fun i => ?_⟩
      by_cases hi : i.val ≤ (portTime uv).val
      · simp only [hi, ↓reduceIte]
        have hi_le : i.val ≤ k0 := by rw [hk0_eq]; exact hi
        exact hpre_const i.val hi_le (Nat.le_of_lt_succ i.isLt)
      · simp only [hi, ↓reduceIte]
        have hi_gt : k0 < i.val := by rw [hk0_eq]; omega
        rw [hpost_const i.val hi_gt (Nat.le_of_lt_succ i.isLt), ← hb_vec]
  by_cases hab : a = b
  · have hnotj : ¬ (a 0 = false ∧ b 0 = true ∧
        ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed) := by
      rintro ⟨h0, h1, _⟩
      rw [← hab, h0] at h1
      exact Bool.noConfusion h1
    have hif1 : (if a = b then 1 else 0) = 1 := by simp [hab]
    have hif2 : (if a 0 = false ∧ b 0 = true ∧
        ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed then 1 else 0) = 0 := by
      simp [hnotj]
    rw [hif1, hif2, add_zero, Finset.card_eq_one]
    obtain ⟨x0, hx0_sat, hx0_log⟩ := hord_mk hab
    refine ⟨x0, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hsat
      rcases hsat_class x hsat with ⟨_, hlog⟩ | ⟨h0, h1, _⟩
      · exact hlog_det x x0 (fun i => (hlog i).trans (hx0_log i).symm)
      · rw [← hab, h0] at h1; exact Bool.noConfusion h1
    · rintro rfl; exact hx0_sat
  · by_cases hcond : a 0 = false ∧ b 0 = true ∧
        ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed
    · have hif1 : (if a = b then 1 else 0) = 0 := by simp [hab]
      have hif2 : (if a 0 = false ∧ b 0 = true ∧
          ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed then 1 else 0) = 1 := by
        simp [hcond]
      rw [hif1, hif2, zero_add, Finset.card_eq_one]
      obtain ⟨x0, hx0_sat, hx0_log⟩ := hjump_mk hcond.1 hcond.2.1 hcond.2.2
      refine ⟨x0, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hsat
        rcases hsat_class x hsat with ⟨heq, _⟩ | ⟨_, _, _, hlog⟩
        · exact absurd heq hab
        · exact hlog_det x x0 (fun i => (hlog i).trans (hx0_log i).symm)
      · rintro rfl; exact hx0_sat
    · have hif1 : (if a = b then 1 else 0) = 0 := by simp [hab]
      have hif2 : (if a 0 = false ∧ b 0 = true ∧
          ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed then 1 else 0) = 0 := by
        simp [hcond]
      rw [hif1, hif2, add_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have hsat := (Finset.mem_filter.1 hx).2
      rcases hsat_class x hsat with ⟨heq, _⟩ | ⟨h0, h1, h2, _⟩
      · exact hab heq
      · exact hcond ⟨h0, h1, h2⟩

end C388

theorem C388main :
  ∀ d : ℕ,
    let w := d + 1
    let L := 2 ^ w - 1
    let D := Fin d → Bool
    let S := Fin L × (Fin (w + 1) → Bool)
    ∃ (base : S → Bool) (port : D × D → S),
      Function.Injective port ∧ (∀ e, base (port e) = false) ∧
      ∀ (allowed : Finset (D × D)) (a b : Fin w → Bool),
        let sat := fun (x : Fin (L + d + 1) → Bool) =>
          (∀ j : Fin w, x (Fin.ofNat (L + d + 1) j.val) = a j ∧
            x (Fin.ofNat (L + d + 1) (L + j.val)) = b j) ∧
          ∀ i : Fin L,
            let s : S := (i, fun offset => x (Fin.ofNat (L + d + 1) (i.val + offset.val)))
            base s = true ∨ s ∈ allowed.image port
        (Finset.univ.filter sat).card =
          (if a = b then 1 else 0) +
          (if a 0 = false ∧ b 0 = true ∧
            ((fun j : Fin d => a j.succ), (fun j : Fin d => b j.succ)) ∈ allowed
           then 1 else 0) := by
  intro d
  exact C388.lfsr_construction d

namespace C836

section Walks

variable (d : ℕ)

abbrev State := Fin (d + 1) → Bool
abbrev Tab := (Fin (d + 2) → Bool) → Bool

def window (s : State d) (b : Bool) : Fin (d + 2) → Bool :=
  fun off => if h : off.val < d + 1 then s ⟨off.val, h⟩ else b

def shift (s : State d) (b : Bool) : State d :=
  fun j => if h : j.val + 1 < d + 1 then s ⟨j.val + 1, h⟩ else b

def walks : ℕ → (ℕ → Tab d) → State d → State d → ℕ
  | 0, _, s, s' => if s = s' then 1 else 0
  | L + 1, T, s, s' => ∑ b : Bool,
      if T 0 (window d s b) = true then walks L (fun i => T (i + 1)) (shift d s b) s' else 0

lemma walks_congr (L : ℕ) : ∀ (T T' : ℕ → Tab d), (∀ i < L, T i = T' i) →
    walks d L T = walks d L T' := by
  induction L with
  | zero => intro T T' _; rfl
  | succ L ih =>
    intro T T' h
    funext s s'
    simp only [walks, h 0 (Nat.succ_pos L),
      ih (fun i => T (i + 1)) (fun i => T' (i + 1)) (fun i hi => h (i + 1) (by omega))]

lemma walks_add (L₁ L₂ : ℕ) : ∀ (T : ℕ → Tab d) (s s' : State d),
    walks d (L₁ + L₂) T s s' = ∑ m, walks d L₁ T s m * walks d L₂ (fun i => T (L₁ + i)) m s' := by
  induction L₁ with
  | zero => intro T s s'; simp [walks]
  | succ L ih =>
    intro T s s'
    have hT : (fun i => T (L + 1 + i)) = (fun i => T (L + i + 1)) :=
      funext fun i => by rw [Nat.add_right_comm]
    rw [Nat.add_right_comm L 1 L₂]
    simp only [walks, ih, hT, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_irrel, Finset.sum_const_zero]

lemma app_eq {n : ℕ} (x : Fin n → Bool) {a b : ℕ} (ha : a < n) (hb : b < n) (h : a = b) :
    x ⟨a, ha⟩ = x ⟨b, hb⟩ := by
  subst h; rfl

abbrev Accepts (L : ℕ) (T : ℕ → Tab d) (s s' : State d) (x : Fin (L + (d + 1)) → Bool) : Prop :=
  (∀ j : Fin (d + 1), x ⟨j.val, by omega⟩ = s j ∧ x ⟨L + j.val, by omega⟩ = s' j) ∧
  ∀ i : Fin L, T i.val (fun off => x ⟨i.val + off.val, by omega⟩) = true

lemma card_accepts (L : ℕ) : ∀ (T : ℕ → Tab d) (s s' : State d),
    (Finset.univ.filter (Accepts d L T s s')).card = walks d L T s s' := by
  induction L with
  | zero =>
    intro T s s'
    simp only [walks]
    split_ifs with h
    · subst h
      rw [Finset.card_eq_one]
      refine ⟨fun k => s ⟨k.val, by omega⟩, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, -⟩
        funext k
        exact (h1 ⟨k.val, by omega⟩).1
      · rintro rfl
        exact ⟨fun j => ⟨rfl, congrArg s (Fin.ext (by simp))⟩, fun i => i.elim0⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨h1, -⟩
      exact h (funext fun j => (h1 j).1.symm.trans ((app_eq x _ _ (by simp)).trans (h1 j).2))
  | succ L ih =>
    intro T s s'
    simp only [walks, ← ih]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x ⟨d + 1, by omega⟩) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.filter_filter]
    split_ifs with hb
    · refine Finset.card_nbij' (fun x k => x ⟨k.val + 1, by omega⟩)
        (fun y k => if h : k.val = 0 then s 0 else y ⟨k.val - 1, by omega⟩) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx ⊢
        obtain ⟨-, ⟨h1, h2⟩, hxb⟩ := hx
        refine ⟨Finset.mem_univ _, fun j => ⟨?_, ?_⟩, fun i => ?_⟩
        · show x ⟨j.val + 1, _⟩ = shift d s b j
          unfold shift
          split_ifs with hj
          · exact (h1 ⟨j.val + 1, hj⟩).1
          · exact (app_eq x _ _ (by omega)).trans hxb
        · show x ⟨L + j.val + 1, _⟩ = s' j
          exact (app_eq x _ _ (by omega)).trans (h1 j).2
        · refine Eq.trans ?_ (h2 ⟨i.val + 1, by omega⟩)
          show T (i.val + 1) _ = T (i.val + 1) _
          congr 1
          funext off
          exact app_eq x _ _ (by dsimp only; omega)
      · intro y hy
        rw [Finset.mem_coe, Finset.mem_filter] at hy ⊢
        obtain ⟨-, h1, h2⟩ := hy
        have hy : ∀ k (hk : k < d + 2), (if h : k = 0 then s 0 else y ⟨k - 1, by omega⟩) =
            window d s b ⟨k, hk⟩ := by
          intro k hk
          unfold window
          dsimp only
          split_ifs with h0 h0'
          · exact congrArg s (Fin.ext h0.symm)
          · omega
          · refine (h1 ⟨k - 1, by omega⟩).1.trans ?_
            unfold shift
            rw [dite_eq_left (by dsimp only; omega)]
            exact congrArg s (Fin.ext (by dsimp only; omega))
          · refine (h1 ⟨k - 1, by omega⟩).1.trans ?_
            unfold shift
            rw [dite_eq_right (by dsimp only; omega)]
        refine ⟨Finset.mem_univ _, ⟨fun j => ⟨?_, ?_⟩, fun i => ?_⟩, ?_⟩
        · refine (hy j.val (by omega)).trans ?_
          unfold window
          rw [dite_eq_left j.isLt]
        · show (if h : L + 1 + j.val = 0 then s 0 else y ⟨L + 1 + j.val - 1, _⟩) = s' j
          rw [dite_eq_right (by omega)]
          exact (app_eq y _ _ (by omega)).trans (h1 j).2
        · obtain ⟨_ | i, hi⟩ := i
          · have hw : (fun off : Fin (d + 2) => (if h : 0 + off.val = 0 then s 0
                else y ⟨0 + off.val - 1, by omega⟩)) = window d s b := by
              funext off
              rw [← hy off.val off.isLt]
              simp only [zero_add]
            show T 0 (fun off => if h : 0 + off.val = 0 then s 0
                else y ⟨0 + off.val - 1, by omega⟩) = true
            rw [hw]
            exact hb
          · refine Eq.trans ?_ (h2 ⟨i, by omega⟩)
            show T (i + 1) _ = T (i + 1) _
            congr 1
            funext off
            show (if h : i + 1 + off.val = 0 then s 0 else y ⟨i + 1 + off.val - 1, _⟩) = _
            rw [dite_eq_right (by omega)]
            exact app_eq y _ _ (by dsimp only; omega)
        · show (if h : d + 1 = 0 then s 0 else y ⟨d + 1 - 1, _⟩) = b
          rw [dite_eq_right (by omega)]
          have h1d := (h1 ⟨d, Nat.lt_succ_self d⟩).1
          refine (app_eq y _ _ (by dsimp only; omega)).trans (h1d.trans ?_)
          unfold shift
          rw [dite_eq_right (by simp)]
      · intro x hx
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        obtain ⟨-, ⟨h1, -⟩, -⟩ := hx
        funext k
        show (if h : k.val = 0 then s 0 else x ⟨k.val - 1 + 1, _⟩) = x k
        split_ifs with h0
        · exact (h1 ⟨0, by omega⟩).1.symm.trans (app_eq x _ _ h0.symm)
        · exact app_eq x _ _ (by omega)
      · intro y _
        funext k
        show (if h : k.val + 1 = 0 then s 0 else y ⟨k.val + 1 - 1, _⟩) = y k
        rw [dite_eq_right (by omega)]
        exact app_eq y _ _ (by omega)
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨⟨h1, h2⟩, hxb⟩
      apply hb
      refine Eq.trans ?_ (h2 ⟨0, by omega⟩)
      show T 0 _ = T 0 _
      congr 1
      funext off
      unfold window
      split_ifs with ho
      · exact (h1 ⟨off.val, ho⟩).1.symm.trans (app_eq x _ _ (by simp))
      · exact hxb.symm.trans (app_eq x _ _ (by simp; omega))

end Walks

section Sweeps

variable (d : ℕ)

def copyTab : Tab d := fun win => decide (win (Fin.last (d + 1)) = win 0)

def rot (k : ℕ) (s : State d) : State d :=
  fun j => s ⟨(j.val + k) % (d + 1), Nat.mod_lt _ (Nat.succ_pos d)⟩

lemma rot_zero (s : State d) : rot d 0 s = s :=
  funext fun j => congrArg s (Fin.ext (by simp [Nat.mod_eq_of_lt j.isLt]))

lemma rot_full (s : State d) : rot d (d + 1) s = s :=
  funext fun j => congrArg s (Fin.ext (by simp [Nat.mod_eq_of_lt j.isLt]))

lemma shift_rot (k : ℕ) (s : State d) : shift d (rot d k s) (rot d k s 0) = rot d (k + 1) s := by
  funext j
  unfold shift rot
  split_ifs with h
  · exact congrArg s (Fin.ext (by dsimp only; congr 1; omega))
  · apply congrArg s
    apply Fin.ext
    dsimp only
    rw [show j.val + (k + 1) = k + (d + 1) by omega, Nat.add_mod_right, Fin.val_zero, zero_add]

lemma walks_copy_step (L : ℕ) (T : ℕ → Tab d) (hT : T 0 = copyTab d) (s s' : State d) :
    walks d (L + 1) T s s' = walks d L (fun i => T (i + 1)) (shift d s (s 0)) s' := by
  simp only [walks, hT, copyTab, window, Fintype.sum_bool]
  cases h : s 0 <;> simp [h]

lemma walks_copies (k : ℕ) : ∀ (T : ℕ → Tab d), (∀ i < k, T i = copyTab d) →
    ∀ (m : ℕ) (s s' : State d),
      walks d k T (rot d m s) s' = if rot d (m + k) s = s' then 1 else 0 := by
  induction k with
  | zero => intro T _ m s s'; rfl
  | succ k ih =>
    intro T hT m s s'
    rw [walks_copy_step d k T (hT 0 (by omega)), shift_rot,
      ih _ (fun i hi => hT (i + 1) (by omega)), show m + 1 + k = m + (k + 1) by omega]

end Sweeps

section Sweep

variable (e : ℕ)

def sweepTab (R : Bool → Bool → Bool → Bool) (i : ℕ) : Tab (e + 1) :=
  if i = 1 then fun win => R (win 0) (win ⟨e + 1, by omega⟩) (win (Fin.last (e + 2)))
  else copyTab (e + 1)

lemma mod_two (a n : ℕ) (h : a < 2 * n) : a % n = if a < n then a else a - n := by
  split_ifs with h'
  · exact Nat.mod_eq_of_lt h'
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma shift_rot_one (s : State (e + 1)) (b : Bool) :
    shift (e + 1) (rot (e + 1) 1 s) b = rot (e + 1) 2 (Function.update s 1 b) := by
  funext j
  unfold shift rot
  rw [Function.update_apply]
  split_ifs with h1 h2 h2
  · rw [Fin.ext_iff] at h2
    simp only [Fin.val_one] at h2
    rw [mod_two _ _ (by omega)] at h2
    split_ifs at h2 <;> omega
  · exact congrArg s (Fin.ext rfl)
  · rfl
  · rw [Fin.ext_iff] at h2
    simp only [Fin.val_one] at h2
    rw [mod_two _ _ (by omega)] at h2
    split_ifs at h2 <;> omega

lemma walks_sweep (R : Bool → Bool → Bool → Bool) (s s' : State (e + 1)) :
    walks (e + 1) (e + 2) (sweepTab e R) s s' =
      ∑ b : Bool, if R (s 1) (s 0) b = true then
        (if Function.update s 1 b = s' then 1 else 0) else 0 := by
  rw [walks_copy_step (e + 1) (e + 1) _ (by simp [sweepTab])]
  conv_lhs => rw [← rot_zero (e + 1) s, shift_rot, zero_add]
  simp only [walks]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h0 : rot (e + 1) 1 s 0 = s 1 :=
    congrArg s (Fin.ext (by simp [Nat.mod_eq_of_lt (show 1 < e + 2 by omega)]))
  have hl : rot (e + 1) 1 s ⟨e + 1, by omega⟩ = s 0 := congrArg s (Fin.ext (by simp))
  have hR : sweepTab e R (0 + 1) (window (e + 1) (rot (e + 1) 1 s) b) = R (s 1) (s 0) b := by
    simp [sweepTab, window, ← h0, ← hl]
  rw [hR, shift_rot_one, walks_copies (e + 1) e _ (fun i hi => by simp [sweepTab]),
    show 2 + e = e + 1 + 1 by omega, rot_full]

end Sweep

section Plane

variable (e : ℕ)

def pack (t : Bool) (u : Fin e → Bool) : State (e + 1) := Fin.cons t (Fin.cons false u)

lemma pack_zero (t : Bool) (u : Fin e → Bool) : pack e t u 0 = t := by simp [pack]

lemma pack_one (t : Bool) (u : Fin e → Bool) : pack e t u 1 = false := by
  rw [← Fin.succ_zero_eq_one, pack, Fin.cons_succ, Fin.cons_zero]

def flipRule (old tag new : Bool) : Bool := decide (new = old) || (tag && new)

def clearRule (old tag new : Bool) : Bool := decide (new = (!tag && old))

lemma walks_flipSweep (t : Bool) (u : Fin e → Bool) (s' : State (e + 1)) :
    walks (e + 1) (e + 2) (sweepTab e flipRule) (pack e t u) s' =
      (if pack e t u = s' then 1 else 0) +
        (if t then (if Function.update (pack e t u) 1 true = s' then 1 else 0) else 0) := by
  have hu : Function.update (pack e t u) 1 false = pack e t u :=
    Function.update_eq_self_iff.2 (pack_one e t u).symm
  rw [walks_sweep, Fintype.sum_bool]
  cases t <;> simp [flipRule, pack_zero, pack_one, hu, add_comm]

lemma walks_clearSweep (s s' : State (e + 1)) (hs : s 0 = true ∨ s 1 = false) :
    walks (e + 1) (e + 2) (sweepTab e clearRule) s s' =
      if Function.update s 1 false = s' then 1 else 0 := by
  rw [walks_sweep, Fintype.sum_bool]
  rcases hs with hs | hs <;> simp [clearRule, hs]

def planeTab (seg : ℕ → Tab (e + 1)) (r : ℕ) : Tab (e + 1) :=
  if r < e + 2 then sweepTab e flipRule r
  else if r < 2 * (e + 2) then sweepTab e clearRule (r - (e + 2)) else seg (r - 2 * (e + 2))

lemma walks_plane (L' : ℕ) (seg : ℕ → Tab (e + 1)) (t : Bool) (u : Fin e → Bool)
    (s' : State (e + 1)) :
    walks (e + 1) (2 * (e + 2) + L') (planeTab e seg) (pack e t u) s' =
      (if t then 2 else 1) * walks (e + 1) L' seg (pack e t u) s' := by
  have hG : ∀ m, walks (e + 1) (e + 2 + L') (fun i => planeTab e seg (e + 2 + i)) m s' =
      ∑ m', walks (e + 1) (e + 2) (sweepTab e clearRule) m m' * walks (e + 1) L' seg m' s' := by
    intro m
    rw [walks_add, walks_congr (e + 1) (e + 2) _ (sweepTab e clearRule) (fun i hi => by
        simp [planeTab, show e + 2 + i < 2 * (e + 2) by omega]),
      walks_congr (e + 1) L' _ seg (fun i hi => by
        simp [planeTab, show ¬ e + 2 + (e + 2 + i) < 2 * (e + 2) by omega,
          show e + 2 + (e + 2 + i) - 2 * (e + 2) = i by omega])]
  have hu : Function.update (pack e t u) 1 false = pack e t u :=
    Function.update_eq_self_iff.2 (pack_one e t u).symm
  have hp : walks (e + 1) (e + 2 + L') (fun i => planeTab e seg (e + 2 + i)) (pack e t u) s' =
      walks (e + 1) L' seg (pack e t u) s' := by
    rw [hG]
    simp [walks_clearSweep e _ _ (Or.inr (pack_one e t u)), hu]
  have hq : walks (e + 1) (e + 2 + L') (fun i => planeTab e seg (e + 2 + i))
      (Function.update (pack e true u) 1 true) s' = walks (e + 1) L' seg (pack e true u) s' := by
    have h0 : Function.update (pack e true u) 1 true 0 = true := by
      rw [Function.update_of_ne zero_ne_one, pack_zero]
    have h1 : Function.update (Function.update (pack e true u) 1 true) 1 false = pack e true u := by
      rw [Function.update_idem]
      exact Function.update_eq_self_iff.2 (pack_one e true u).symm
    rw [hG]
    simp [walks_clearSweep e _ _ (Or.inl h0), h1]
  rw [show 2 * (e + 2) + L' = e + 2 + (e + 2 + L') by omega, walks_add,
    walks_congr (e + 1) (e + 2) (planeTab e seg) (sweepTab e flipRule)
      (fun i hi => by simp [planeTab, hi])]
  simp only [walks_flipSweep, add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, hp]
  cases t <;> simp [hq, two_mul]

end Plane

section Bridge

variable (d : ℕ)

lemma app_mod {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < n) (h : k % n < n) :
    x ⟨k % n, h⟩ = x ⟨k, hk⟩ := app_eq x _ _ (Nat.mod_eq_of_lt hk)

def extTab (L : ℕ) (tab : Fin L → Tab d) (k : ℕ) : Tab d :=
  if h : k < L then tab ⟨k, h⟩ else fun _ => true

lemma card_mod (L : ℕ) (tab : Fin L → Tab d) (s s' : State d) :
    (Finset.univ.filter (fun x : Fin (L + (d + 1)) → Bool =>
      (∀ j : Fin (d + 1), x ⟨j.val % (L + (d + 1)), Nat.mod_lt _ (by omega)⟩ = s j ∧
        x ⟨(L + j.val) % (L + (d + 1)), Nat.mod_lt _ (by omega)⟩ = s' j) ∧
      ∀ i : Fin L, tab i (fun off => x ⟨(i.val + off.val) % (L + (d + 1)),
        Nat.mod_lt _ (by omega)⟩) = true)).card =
    walks d L (extTab d L tab) s s' := by
  rw [← card_accepts]
  congr 1
  apply Finset.filter_congr
  intro x _
  refine and_congr (forall_congr' fun j => ?_) (forall_congr' fun i => ?_)
  · rw [app_mod x j.val (by omega), app_mod x (L + j.val) (by omega)]
  · have hw : (fun off : Fin (d + 2) => x ⟨(i.val + off.val) % (L + (d + 1)),
        Nat.mod_lt _ (by omega)⟩) = fun off => x ⟨i.val + off.val, by omega⟩ :=
      funext fun off => app_mod x _ (by omega) _
    rw [hw, extTab, dite_eq_left i.isLt]

end Bridge

section Seg

variable (d : ℕ)

abbrev Cell := Fin (2 ^ (d + 2) - 1) × (Fin (d + 3) → Bool)
abbrev Pair := (Fin (d + 1) → Bool) × (Fin (d + 1) → Bool)

def segOf (base3 : Cell d → Bool)
    (port3 : Pair d → Cell d)
    (allowed : Finset (Pair d)) : ℕ → Tab (d + 1) :=
  extTab (d + 1) (2 ^ (d + 2) - 1) fun i win =>
    base3 (i, win) || decide ((i, win) ∈ allowed.image port3)

def Transfers (base3 : Cell d → Bool)
    (port3 : Pair d → Cell d) : Prop :=
  ∀ allowed (s s' : State (d + 1)),
    walks (d + 1) (2 ^ (d + 2) - 1) (segOf d base3 port3 allowed) s s' =
      (if s = s' then 1 else 0) + (if s 0 = false ∧ s' 0 = true ∧
        ((fun j : Fin (d + 1) => s j.succ), (fun j : Fin (d + 1) => s' j.succ)) ∈ allowed
        then 1 else 0)

lemma seg388 : ∃ (base3 : Cell d → Bool)
    (port3 : Pair d → Cell d),
    Function.Injective port3 ∧ (∀ p, base3 (port3 p) = false) ∧ Transfers d base3 port3 := by
  obtain ⟨base3, port3, hinj, hbase, hcount⟩ := C388main (d + 1)
  refine ⟨base3, port3, hinj, hbase, fun allowed s s' => ?_⟩
  rw [segOf, ← card_mod]
  refine Eq.trans ?_ (hcount allowed s s')
  congr 1
  apply Finset.filter_congr
  intro x _
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  rfl

end Seg

section Main

variable (e L' : ℕ) (seg : ℕ → ℕ → Tab (e + 1)) (dg : ℕ → (Fin e → Bool) → (Fin e → Bool) → Bool)

def globalTab (q k : ℕ) : Tab (e + 1) :=
  planeTab e (seg (q - 1 - k / (2 * (e + 2) + L'))) (k % (2 * (e + 2) + L'))

lemma pack_inj {t t' : Bool} {u u' : Fin e → Bool} :
    pack e t u = pack e t' u' ↔ t = t' ∧ u = u' := by
  simp [pack, Fin.cons_inj]

lemma main_count
    (hF : ∀ β u (G : State (e + 1) → ℕ), ∑ m, walks (e + 1) L' (seg β) (pack e false u) m * G m =
      G (pack e false u) + ∑ v, if dg β u v = true then G (pack e true v) else 0)
    (hT : ∀ β u m, walks (e + 1) L' (seg β) (pack e true u) m = if pack e true u = m then 1 else 0)
    (q : ℕ) : ∀ (a : Bool) (u : Fin e → Bool) (b : Bool) (v : Fin e → Bool),
    walks (e + 1) (q * (2 * (e + 2) + L')) (globalTab e L' seg q) (pack e a u) (pack e b v) =
      if a = b then (if u = v then (if a then 2 ^ q else 1) else 0)
      else if a then 0 else ∑ β ∈ Finset.range q, if dg β u v = true then 2 ^ β else 0 := by
  induction q with
  | zero => intro a u b v; cases a <;> cases b <;> simp [walks, pack_inj]
  | succ q ih =>
    intro a u b v
    have hshift : (fun i => globalTab e L' seg (q + 1) (2 * (e + 2) + L' + i)) =
        globalTab e L' seg q := by
      funext i
      simp only [globalTab]
      rw [show 2 * (e + 2) + L' + i = i + 1 * (2 * (e + 2) + L') by ring,
        Nat.add_mul_div_right _ _ (by omega), Nat.add_mul_mod_self_right]
      congr 2
      omega
    rw [Nat.succ_mul, Nat.add_comm (q * _), walks_add, hshift,
      walks_congr (e + 1) _ (globalTab e L' seg (q + 1)) (planeTab e (seg q)) (fun i hi => by
        simp [globalTab, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi])]
    simp only [walks_plane]
    cases a
    · have h := hF q u (fun m => walks (e + 1) (q * (2 * (e + 2) + L')) (globalTab e L' seg q) m
        (pack e b v))
      simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
      rw [h]
      simp only [ih]
      cases b
      · simp
      · have hs : (∑ x, if dg q u x = true then (if x = v then 2 ^ q else 0) else 0) =
            if dg q u v = true then 2 ^ q else 0 := by
          rw [Finset.sum_eq_single v (fun x _ hx => by simp [hx]) (by simp)]
          simp
        simp [Finset.sum_range_succ, hs]
    · simp only [↓reduceIte, hT, mul_assoc, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ih]
      cases b <;> simp [pow_succ, mul_comm]

end Main

section Final

variable (d q : ℕ)

abbrev planeLen : ℕ := 2 * (d + 2) + (2 ^ (d + 2) - 1)

lemma planeLen_eq : planeLen d = 2 * (d + 2) + (2 ^ (d + 2) - 1) := rfl

abbrev Digit := Fin q × (Fin d → Bool) × (Fin d → Bool)

def dig (digits : Finset (Digit d q)) (β : ℕ)
    (u v : Fin d → Bool) : Bool :=
  if h : β < q then decide ((⟨β, h⟩, u, v) ∈ digits) else false

def allowedOf (dg : ℕ → (Fin d → Bool) → (Fin d → Bool) → Bool) (β : ℕ) :
    Finset (Pair d) :=
  (Finset.univ.filter fun p : (Fin d → Bool) × (Fin d → Bool) => dg β p.1 p.2).image
    fun p => (Fin.cons false p.1, Fin.cons false p.2)

lemma pos_lt {A c P : ℕ} (hA : A < q) (hc : c < P) : A * P + c < q * P :=
  calc A * P + c < A * P + P := by omega
    _ = (A + 1) * P := by ring
    _ ≤ q * P := Nat.mul_le_mul_right _ hA

lemma pos_div {A c P : ℕ} (hc : c < P) : (A * P + c) / P = A := by
  rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hc, zero_add]

lemma pos_mod {A c P : ℕ} (hc : c < P) : (A * P + c) % P = c := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

variable (base3 : Cell d → Bool) (port3 : Pair d → Cell d)

abbrev Slot := Fin (q * planeLen d) × (Fin (d + 3) → Bool)

def portCell (e : Digit d q) : Cell d := port3 (Fin.cons false e.2.1, Fin.cons false e.2.2)

lemma portCell_lt (e : Digit d q) : 2 * (d + 2) + (portCell d q port3 e).1.val < planeLen d := by
  have := (portCell d q port3 e).1.isLt
  have := planeLen_eq d
  omega

def portOf (e : Digit d q) : Slot d q :=
  (⟨(q - 1 - e.1.val) * planeLen d + (2 * (d + 2) + (portCell d q port3 e).1.val),
    pos_lt q (by have := e.1.isLt; omega) (portCell_lt d q port3 e)⟩, (portCell d q port3 e).2)

def baseOf (s : Slot d q) : Bool :=
  planeTab d (extTab (d + 1) (2 ^ (d + 2) - 1) fun i win => base3 (i, win))
    (s.1.val % planeLen d) s.2

lemma portOf_div (e : Digit d q) : (portOf d q port3 e).1.val / planeLen d = q - 1 - e.1.val :=
  pos_div (portCell_lt d q port3 e)

lemma portOf_mod (e : Digit d q) :
    (portOf d q port3 e).1.val % planeLen d = 2 * (d + 2) + (portCell d q port3 e).1.val :=
  pos_mod (portCell_lt d q port3 e)

lemma portOf_injective (hinj : Function.Injective port3) :
    Function.Injective (portOf d q port3) := by
  rintro ⟨β, u, v⟩ ⟨β', u', v'⟩ h
  have hd := portOf_div d q port3 (β, u, v)
  have hm := portOf_mod d q port3 (β, u, v)
  rw [h, portOf_div] at hd
  rw [h, portOf_mod] at hm
  have h2 := congrArg Prod.snd h
  simp only [portOf, portCell] at hd hm h2
  have hβ : β = β' := Fin.ext (by have := β.isLt; have := β'.isLt; omega)
  have hp := hinj (Prod.ext (Fin.ext (by omega)) h2)
  simp only [Prod.mk.injEq] at hp
  rw [hβ, Fin.cons_right_injective _ hp.1, Fin.cons_right_injective _ hp.2]

lemma baseOf_portOf (hbase : ∀ p, base3 (port3 p) = false) (e : Digit d q) :
    baseOf d q base3 (portOf d q port3 e) = false := by
  have hr := (portCell d q port3 e).1.isLt
  rw [baseOf, portOf_mod, planeTab, ite_eq_right (by omega), ite_eq_right (by omega), extTab,
    dite_eq_left (by omega)]
  simp only [Nat.add_sub_cancel_left]
  exact hbase (Fin.cons false e.2.1, Fin.cons false e.2.2)

lemma not_mem_port (digits : Finset (Digit d q)) {k : ℕ}
    (hk : k < q * planeLen d) (h : k % planeLen d < 2 * (d + 2)) (win : Fin (d + 3) → Bool) :
    (⟨k, hk⟩, win) ∉ digits.image (portOf d q port3) := by
  intro hmem
  obtain ⟨e, -, he⟩ := Finset.mem_image.1 hmem
  have := planeLen_eq d
  have hm := portOf_mod d q port3 e
  rw [he] at hm
  dsimp only at hm
  omega

lemma mem_port (digits : Finset (Digit d q)) {k : ℕ}
    (hk : k < q * planeLen d) (h1 : 2 * (d + 2) ≤ k % planeLen d)
    (h3 : k % planeLen d - 2 * (d + 2) < 2 ^ (d + 2) - 1) (win : Fin (d + 3) → Bool) :
    (⟨k, hk⟩, win) ∈ digits.image (portOf d q port3) ↔
      (⟨k % planeLen d - 2 * (d + 2), h3⟩, win) ∈
        (allowedOf d (dig d q digits) (q - 1 - k / planeLen d)).image port3 := by
  have hP := planeLen_eq d
  have hkd : k / planeLen d < q := (Nat.div_lt_iff_lt_mul (by omega)).2 hk
  constructor
  · intro hmem
    obtain ⟨⟨β, u, v⟩, he, heq⟩ := Finset.mem_image.1 hmem
    have hm := portOf_mod d q port3 (β, u, v)
    have hd := portOf_div d q port3 (β, u, v)
    rw [heq] at hm hd
    dsimp only [portCell] at hm hd
    refine Finset.mem_image.2 ⟨(Fin.cons false u, Fin.cons false v),
      Finset.mem_image.2 ⟨(u, v), ?_, rfl⟩, Prod.ext (Fin.ext (by dsimp only; omega)) ?_⟩
    · have hβ : q - 1 - k / planeLen d = β.val := by have := β.isLt; omega
      simp [hβ, dig, he]
    · have h2 := congrArg Prod.snd heq
      simp only [portOf] at h2
      exact h2
  · intro hmem
    obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.1 hmem
    obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.1 hp
    have hβ : q - 1 - k / planeLen d < q := by
      generalize k / planeLen d = t at hkd ⊢; omega
    have huv' := (Finset.mem_filter.1 huv).2
    rw [dig, dite_eq_left hβ, decide_eq_true_iff] at huv'
    refine Finset.mem_image.2 ⟨(⟨q - 1 - k / planeLen d, hβ⟩, u, v), huv', ?_⟩
    refine Prod.ext (Fin.ext ?_) ?_
    · show (q - 1 - (q - 1 - k / planeLen d)) * planeLen d +
          (2 * (d + 2) + (port3 (Fin.cons false u, Fin.cons false v)).1.val) = k
      rw [hpeq, show q - 1 - (q - 1 - k / planeLen d) = k / planeLen d by
        generalize k / planeLen d = t at hkd ⊢; omega]
      dsimp only
      rw [show 2 * (d + 2) + (k % planeLen d - 2 * (d + 2)) = k % planeLen d by omega,
        Nat.div_add_mod']
    · show (port3 (Fin.cons false u, Fin.cons false v)).2 = win
      rw [hpeq]

lemma tab_eq (digits : Finset (Digit d q)) (k : ℕ)
    (hk : k < q * planeLen d) :
    extTab (d + 1) (q * planeLen d) (fun i win => baseOf d q base3 (i, win) ||
        decide ((i, win) ∈ digits.image (portOf d q port3))) k =
      globalTab d (2 ^ (d + 2) - 1)
        (fun β => segOf d base3 port3 (allowedOf d (dig d q digits) β)) q k := by
  funext win
  have hP := planeLen_eq d
  have hr : k % planeLen d < planeLen d := Nat.mod_lt _ (by omega)
  simp only [extTab, dite_eq_left hk, globalTab, baseOf]
  unfold planeTab
  split_ifs with h1 h2
  · simp [not_mem_port d q port3 digits hk (by omega) win]
  · simp [not_mem_port d q port3 digits hk (by omega) win]
  · have h3 : k % planeLen d - 2 * (d + 2) < 2 ^ (d + 2) - 1 := by omega
    simp only [segOf, extTab, dite_eq_left h3, mem_port d q port3 digits hk (by omega) h3]

lemma hF_of (dg : ℕ → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (h388 : Transfers d base3 port3)
    (β : ℕ) (u : Fin d → Bool) (G : State (d + 1) → ℕ) :
    ∑ m, walks (d + 1) (2 ^ (d + 2) - 1) (segOf d base3 port3 (allowedOf d dg β))
      (pack d false u) m * G m =
      G (pack d false u) + ∑ v, if dg β u v = true then G (pack d true v) else 0 := by
  unfold Transfers at h388
  simp only [h388, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  congr 1
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  have hset : Finset.univ.filter (fun m : State (d + 1) => pack d false u 0 = false ∧ m 0 = true ∧
      ((fun j : Fin (d + 1) => pack d false u j.succ), (fun j : Fin (d + 1) => m j.succ)) ∈
        allowedOf d dg β) = (Finset.univ.filter fun v => dg β u v = true).image (pack d true) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, allowedOf, pack,
      Fin.cons_zero, Fin.cons_succ, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hm0, a, b, hab, ha, hb⟩
      refine ⟨b, ?_, ?_⟩
      · rwa [← Fin.cons_right_injective _ ha]
      · rw [← Fin.cons_self_tail m, hm0]
        exact congrArg _ hb
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by simp, u, v, hv, rfl, by funext j; simp⟩
  rw [hset, Finset.sum_image fun x _ y _ h => ((pack_inj d).1 h).2]

lemma hT_of (dg : ℕ → (Fin d → Bool) → (Fin d → Bool) → Bool)
    (h388 : Transfers d base3 port3)
    (β : ℕ) (u : Fin d → Bool) (m : State (d + 1)) :
    walks (d + 1) (2 ^ (d + 2) - 1) (segOf d base3 port3 (allowedOf d dg β)) (pack d true u) m =
      if pack d true u = m then 1 else 0 := by
  unfold Transfers at h388
  simp [h388, pack_zero]

end Final

end C836

open C836 in
theorem C836main :
∀ d q : Nat,
  let w := d+2
  let plane := 2*w + (2^w-1)
  let L := q*plane
  let n := L+w
  let D := Fin d → Bool
  let E := Fin q × D × D
  let S := Fin L × (Fin (w+1) → Bool)
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.lt_of_lt_of_le (Nat.succ_pos (d+1)) (Nat.le_add_left _ _))⟩ : Fin n)
  let pack := fun (tag : Bool) (payload : D) => (Fin.cases tag (Fin.cases false payload) : Fin w → Bool)
  ∃ (base : S → Bool) (port : E → S),
    Function.Injective port ∧ (∀ e, base (port e) = false) ∧
    (∀ e, (port e).1.val / plane = q-1-e.1.val) ∧
    ∀ digits : Finset E, ∀ (a b : Bool) (u v : D),
      let weight := (Finset.univ : Finset (Fin q)).sum
        (fun bit => if (bit,u,v) ∈ digits then 2^bit.val else 0)
      (Finset.univ.filter (fun x : Fin n → Bool =>
        (∀ j : Fin w, x (loc j.val) = pack a u j ∧ x (loc (L+j.val)) = pack b v j) ∧
        ∀ i : Fin L,
          let s : S := (i, fun off => x (loc (i.val+off.val)))
          base s = true ∨ s ∈ digits.image port)).card =
        if a = b then (if u = v then (if a then 2^q else 1) else 0)
        else if a then 0 else weight := by
  intro d q
  dsimp only
  obtain ⟨base3, port3, hinj3, hbase3, h388⟩ := seg388 d
  refine ⟨baseOf d q base3, portOf d q port3, portOf_injective d q port3 hinj3,
    baseOf_portOf d q base3 port3 hbase3, portOf_div d q port3, fun digits a b u v => ?_⟩
  have hcard := card_mod (d + 1) (q * planeLen d) (fun i win => baseOf d q base3 (i, win) ||
    decide ((i, win) ∈ digits.image (portOf d q port3))) (pack d a u) (pack d b v)
  rw [walks_congr (d + 1) _ _ _ (fun k hk => tab_eq d q base3 port3 digits k hk),
    main_count d _ _ (dig d q digits) (hF_of d base3 port3 _ h388)
      (hT_of d base3 port3 _ h388)] at hcard
  refine Eq.trans ?_ (hcard.trans ?_)
  · congr 1
    apply Finset.filter_congr
    intro x _
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    rfl
  · rw [← Fin.sum_univ_eq_sum_range]
    simp [dig]

open Finset

variable {d t L q : ℕ}

theorem posLt {t K h o : ℕ} (hh : h < t) (ho : o < K) : h*K + o < t*K := by
  calc h*K + o < h*K + K := by omega
    _ = (h+1)*K := by ring
    _ ≤ t*K := Nat.mul_le_mul_right _ hh

theorem dm {K h o : ℕ} (ho : o < K) : (h*K + o) / K = h ∧ (h*K + o) % K = o := by
  have hK : 0 < K := by omega
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hK, Nat.div_eq_of_lt ho, zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ho]

theorem wrap (t K a k : ℕ) : (a*K + k) % (t*K) = ((a % t)*K + k) % (t*K) := by
  conv_lhs => rw [← Nat.mod_add_div a t]
  rw [show (a % t + t * (a / t)) * K + k = ((a % t) * K + k) + (a / t) * (t * K) by ring]
  rw [Nat.add_mul_mod_self_right]

def rd {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) (k : ℕ) : Bool := x ⟨k % n, Nat.mod_lt _ hn⟩

def tailB (first b0 b1 bl : Bool) : Bool := if first then b0 && !b1 && !bl else bl == b0

def baseAt (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool) (o : ℕ) (pat : Fin (d+2+1) → Bool) :
    Bool :=
  if h : o < L then base0 (⟨o, h⟩, pat) else
    tailB (decide (o = L)) (pat ⟨0, by omega⟩) (pat ⟨1, by omega⟩) (pat (Fin.last (d+2)))

def baseF (t : ℕ) (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (s : Fin (t*(L+(d+2))) × (Fin (d+2+1) → Bool)) : Bool :=
  baseAt base0 (s.1.val % (L+(d+2))) s.2

def portF (t : ℕ) (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (e : Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)) :
    Fin (t*(L+(d+2))) × (Fin (d+2+1) → Bool) :=
  (⟨e.1.val * (L+(d+2)) + (port0 e.2).1.val,
    posLt e.1.isLt (by have := (port0 e.2).1.isLt; omega)⟩, (port0 e.2).2)

theorem portF_inj {port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool)}
    (hinj : Function.Injective port0) : Function.Injective (portF t port0) := by
  rintro ⟨h, e⟩ ⟨h', e'⟩ he
  simp only [portF, Prod.mk.injEq, Fin.mk.injEq] at he
  obtain ⟨h1, h2⟩ := he
  have ho := (port0 e).1.isLt
  have ho' := (port0 e').1.isLt
  have a1 := dm (h := h.val) (K := L+(d+2)) (show (port0 e).1.val < L+(d+2) by omega)
  have a2 := dm (h := h'.val) (K := L+(d+2)) (show (port0 e').1.val < L+(d+2) by omega)
  rw [h1] at a1
  have hh : h = h' := Fin.ext (a1.1.symm.trans a2.1)
  have hoo : (port0 e).1 = (port0 e').1 := Fin.ext (a1.2.symm.trans a2.2)
  have h3 := hinj (Prod.ext hoo h2)
  rw [hh, h3]

theorem base_port {base0 : Fin L × (Fin (d+2+1) → Bool) → Bool}
    {port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool)}
    (hb : ∀ e, base0 (port0 e) = false) (e : Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)) :
    baseF t base0 (portF t port0 e) = false := by
  obtain ⟨h, e⟩ := e
  have ho := (port0 e).1.isLt
  have a := (dm (h := h.val) (show (port0 e).1.val < L+(d+2) by omega)).2
  show baseAt base0 ((h.val * (L+(d+2)) + (port0 e).1.val) % (L+(d+2))) (port0 e).2 = false
  rw [a]
  unfold baseAt
  rw [dif_pos ho]
  exact hb e

theorem port_blk (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (e : Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)) :
    (portF t port0 e).1.val / (L + (d+2)) = e.1.val := by
  have ho := (port0 e.2).1.isLt
  exact (dm (h := e.1.val) (K := L+(d+2)) (show (port0 e.2).1.val < L+(d+2) by omega)).1

def nx (ht : 0 < t) (h : Fin t) : Fin t := ⟨(h.val+1) % t, Nat.mod_lt _ ht⟩

theorem nx_prev (ht : 0 < t) (h : Fin t) : nx ht ⟨(h.val + t - 1) % t, Nat.mod_lt _ ht⟩ = h := by
  apply Fin.ext
  show ((h.val + t - 1) % t + 1) % t = h.val
  rw [Nat.mod_add_mod, show h.val + t - 1 + 1 = h.val + t * 1 by omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h.2]

theorem rd_wrap (hn : 0 < t*(L+(d+2))) (ht : 0 < t) (x : Fin (t*(L+(d+2))) → Bool) (h : Fin t)
    (k : ℕ) :
    rd hn x (h.val*(L+(d+2)) + (L+k) + (d+2)) = rd hn x ((nx ht h).val*(L+(d+2)) + k) := by
  unfold rd nx
  congr 1
  apply Fin.ext
  show (h.val*(L+(d+2)) + (L+k) + (d+2)) % (t*(L+(d+2))) =
    ((h.val+1) % t * (L+(d+2)) + k) % (t*(L+(d+2)))
  rw [show h.val*(L+(d+2)) + (L+k) + (d+2) = (h.val+1)*(L+(d+2)) + k by ring,
    wrap t (L+(d+2)) (h.val+1) k]

def glue (y : Fin t → Fin (L+(d+2)) → Bool) : Fin (t*(L+(d+2))) → Bool :=
  fun i => y ⟨i.val / (L+(d+2)), (Nat.div_lt_iff_lt_mul (by omega)).2 i.2⟩
    ⟨i.val % (L+(d+2)), Nat.mod_lt _ (by omega)⟩

theorem rd_glue (hn : 0 < t*(L+(d+2))) (y : Fin t → Fin (L+(d+2)) → Bool) (h : Fin t) (o : ℕ)
    (ho : o < L+(d+2)) : rd hn (glue y) (h.val*(L+(d+2)) + o) = y h ⟨o, ho⟩ := by
  have e1 : (h.val*(L+(d+2))+o) % (t*(L+(d+2))) = h.val*(L+(d+2))+o :=
    Nat.mod_eq_of_lt (posLt h.2 ho)
  unfold rd glue
  congr 1
  · apply Fin.ext
    show (h.val*(L+(d+2))+o) % (t*(L+(d+2))) / (L+(d+2)) = h.val
    rw [e1, (dm ho).1]
  · apply Fin.ext
    show (h.val*(L+(d+2))+o) % (t*(L+(d+2))) % (L+(d+2)) = o
    rw [e1, (dm ho).2]

def xb (hn : 0 < t*(L+(d+2))) (x : Fin (t*(L+(d+2))) → Bool) (h : Fin t) (y : Fin (L+(d+2))) :
    Bool :=
  rd hn x (h.val*(L+(d+2)) + y.val)

theorem modEq {K m : ℕ} (hm : m < K) (hk : m % K < K) : (⟨m % K, hk⟩ : Fin K) = ⟨m, hm⟩ :=
  Fin.ext (Nat.mod_eq_of_lt hm)

theorem rd_self (hn : 0 < t*(L+(d+2))) (x : Fin (t*(L+(d+2))) → Bool) (i : Fin (t*(L+(d+2)))) :
    x i = xb hn x ⟨i.val / (L+(d+2)), (Nat.div_lt_iff_lt_mul (by omega)).2 i.2⟩
      ⟨i.val % (L+(d+2)), Nat.mod_lt _ (by omega)⟩ := by
  unfold xb rd
  congr 1
  apply Fin.ext
  show i.val = (i.val / (L+(d+2)) * (L+(d+2)) + i.val % (L+(d+2))) % (t*(L+(d+2)))
  rw [Nat.div_add_mod', Nat.mod_eq_of_lt i.2]

abbrev Row (hn : 0 < t*(L+(d+2))) (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)))
    (x : Fin (t*(L+(d+2))) → Bool) (i : Fin (t*(L+(d+2)))) : Prop :=
  baseF t base0 (i, fun j => x ⟨(i.val + j.val) % (t*(L+(d+2))), Nat.mod_lt _ hn⟩) = true ∨
  (i, fun j => x ⟨(i.val + j.val) % (t*(L+(d+2))), Nat.mod_lt _ hn⟩) ∈ digits.image (portF t port0)

def alh (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (h : Fin t) :
    Finset (Fin q × (Fin d → Bool) × (Fin d → Bool)) :=
  univ.filter (fun e : Fin q × (Fin d → Bool) × (Fin d → Bool) => decide ((h, e) ∈ digits) = true)

def ix (h : Fin t) (o : ℕ) (ho : o < L+(d+2)) : Fin (t*(L+(d+2))) :=
  ⟨h.val*(L+(d+2))+o, posLt h.2 ho⟩

theorem memIn (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (h : Fin t) (o : ℕ)
    (ho : o < L) (pat : Fin (d+2+1) → Bool) :
    (ix h o (by omega), pat) ∈ digits.image (portF t port0) ↔
      ((⟨o, ho⟩ : Fin L), pat) ∈ (alh digits h).image port0 := by
  simp only [mem_image, alh, mem_filter, mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨h', e⟩, he, hp⟩
    simp only [portF, ix, Prod.mk.injEq, Fin.mk.injEq] at hp
    obtain ⟨h1, h2⟩ := hp
    have hl := (port0 e).1.isLt
    have a1 := dm (h := h'.val) (K := L+(d+2)) (show (port0 e).1.val < L+(d+2) by omega)
    have a2 := dm (h := h.val) (K := L+(d+2)) (show o < L+(d+2) by omega)
    rw [h1] at a1
    have hh : h' = h := Fin.ext (a1.1.symm.trans a2.1)
    subst hh
    exact ⟨e, he, Prod.ext (Fin.ext (a1.2.symm.trans a2.2)) h2⟩
  · rintro ⟨e, he, hp⟩
    refine ⟨(h, e), he, ?_⟩
    rw [Prod.ext_iff]
    constructor
    · apply Fin.ext
      simp only [portF, ix, hp]
    · simp only [portF, hp]

theorem memTail (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (h : Fin t) (o : ℕ)
    (ho1 : L ≤ o) (ho : o < L+(d+2)) (pat : Fin (d+2+1) → Bool) :
    (ix h o ho, pat) ∉ digits.image (portF t port0) := by
  simp only [mem_image, not_exists, not_and]
  rintro ⟨h', e⟩ _ hp
  simp only [portF, ix, Prod.mk.injEq, Fin.mk.injEq] at hp
  have hl := (port0 e).1.isLt
  have a1 := dm (h := h'.val) (K := L+(d+2)) (show (port0 e).1.val < L+(d+2) by omega)
  have a2 := dm (h := h.val) ho
  rw [hp.1] at a1
  omega

theorem rowIn (hn : 0 < t*(L+(d+2))) (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)))
    (x : Fin (t*(L+(d+2))) → Bool) (h : Fin t) (o : ℕ) (ho : o < L) :
    Row hn base0 port0 digits x (ix h o (by omega)) ↔
      base0 (⟨o, ho⟩, fun j => xb hn x h ⟨(o + j.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩) = true ∨
      ((⟨o, ho⟩ : Fin L), fun j => xb hn x h ⟨(o + j.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩) ∈
        (alh digits h).image port0 := by
  have hw : (fun j : Fin (d+2+1) =>
      x ⟨((ix h o (by omega) : Fin (t*(L+(d+2)))).val + j.val) % (t*(L+(d+2))), Nat.mod_lt _ hn⟩) =
      fun j => xb hn x h ⟨(o + j.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩ := by
    funext j
    have hj := j.isLt
    rw [modEq (show o + j.val < L+(d+2) by omega)]
    show x ⟨(h.val*(L+(d+2)) + o + j.val) % (t*(L+(d+2))), _⟩ =
      x ⟨(h.val*(L+(d+2)) + (o + j.val)) % (t*(L+(d+2))), _⟩
    simp only [add_assoc]
  unfold Row
  rw [hw, ← memIn port0 digits h o ho]
  have hb : baseF t base0 (ix h o (by omega),
      fun j => xb hn x h ⟨(o + j.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩) =
      base0 (⟨o, ho⟩, fun j => xb hn x h ⟨(o + j.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩) := by
    show baseAt base0 ((h.val*(L+(d+2))+o) % (L+(d+2))) _ = _
    rw [(dm (show o < L+(d+2) by omega)).2]
    unfold baseAt
    rw [dif_pos ho]
  rw [hb]

theorem rowTail (hn : 0 < t*(L+(d+2))) (ht : 0 < t) (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool)))
    (x : Fin (t*(L+(d+2))) → Bool) (h : Fin t) (k : ℕ) (hk : k < d+2) :
    Row hn base0 port0 digits x (ix h (L+k) (by omega)) ↔
      tailB (decide (k = 0)) (rd hn x (h.val*(L+(d+2)) + (L+k)))
        (rd hn x (h.val*(L+(d+2)) + (L+k) + 1))
        (rd hn x ((nx ht h).val*(L+(d+2)) + k)) = true := by
  unfold Row
  rw [or_iff_left (memTail port0 digits h (L+k) (by omega) (by omega) _)]
  show baseAt base0 ((h.val*(L+(d+2))+(L+k)) % (L+(d+2))) _ = true ↔ _
  rw [(dm (show L+k < L+(d+2) by omega)).2]
  unfold baseAt
  rw [dif_neg (by omega)]
  have e1 : decide (L + k = L) = decide (k = 0) := by simp
  rw [e1, ← rd_wrap hn ht x h k]
  rfl

abbrev pk (a : Bool) (u : Fin d → Bool) : Fin (d+2) → Bool := Fin.cases a (Fin.cases false u)

theorem pk_one (a : Bool) (u : Fin d → Bool) : pk a u 1 = false := by
  have e : (1 : Fin (d+2)) = (0 : Fin (d+1)).succ := Fin.ext (by simp)
  rw [e]
  rfl

abbrev sat836 (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (dg : Finset (Fin q × (Fin d → Bool) × (Fin d → Bool))) (a b : Fin (d+2) → Bool)
    (x : Fin (L+(d+2)) → Bool) : Prop :=
  (∀ j : Fin (d+2), x ⟨j.val % (L+(d+2)), Nat.mod_lt _ (by omega)⟩ = a j ∧
    x ⟨(L + j.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩ = b j) ∧
  ∀ i : Fin L, base0 (i, fun off => x ⟨(i.val + off.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩) = true ∨
    (i, fun off => x ⟨(i.val + off.val) % (L+(d+2)), Nat.mod_lt _ (by omega)⟩) ∈ dg.image port0

abbrev Hc (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool)) : Prop :=
  ∀ (dg : Finset (Fin q × (Fin d → Bool) × (Fin d → Bool))) (a b : Bool) (u v : Fin d → Bool),
    (univ.filter (sat836 base0 port0 dg (pk a u) (pk b v))).card =
      if a = b then (if u = v then (if a then 2^q else 1) else 0)
      else if a then 0 else ∑ bit : Fin q, if (bit, u, v) ∈ dg then 2^bit.val else 0

theorem cnt (ht : 0 < t) (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (hc : Hc base0 port0)
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) (p : Fin t → Fin d → Bool)
    (h : Fin t) :
    (univ.filter (sat836 base0 port0 (alh digits h) (pk false (p h)) (pk true (p (nx ht h))))).card =
      ∑ bit : Fin q, if (h, bit, p h, p (nx ht h)) ∈ digits then 2^bit.val else 0 := by
  rw [hc]
  simp [alh]

theorem count_main (ht : 0 < t) (hn : 0 < t*(L+(d+2))) (base0 : Fin L × (Fin (d+2+1) → Bool) → Bool)
    (port0 : Fin q × (Fin d → Bool) × (Fin d → Bool) → Fin L × (Fin (d+2+1) → Bool))
    (hc : Hc base0 port0)
    (digits : Finset (Fin t × Fin q × (Fin d → Bool) × (Fin d → Bool))) :
    (univ.filter (fun x : Fin (t*(L+(d+2))) → Bool => ∀ i : Fin (t*(L+(d+2))),
      Row hn base0 port0 digits x i)).card =
    ∑ p : Fin t → Fin d → Bool, ∏ h : Fin t,
      ∑ bit : Fin q, if (h, bit, p h, p (nx ht h)) ∈ digits then 2^bit.val else 0 := by
  have allRows : ∀ x, (∀ i, Row hn base0 port0 digits x i) ↔
      ∀ (h : Fin t) (o : ℕ) (ho : o < L+(d+2)), Row hn base0 port0 digits x (ix h o ho) := by
    intro x
    constructor
    · intro H h o ho; exact H _
    · intro H i
      have hK : 0 < L+(d+2) := by omega
      have := H ⟨i.val / (L+(d+2)), (Nat.div_lt_iff_lt_mul hK).2 i.2⟩ (i.val % (L+(d+2)))
        (Nat.mod_lt _ hK)
      have e : ix ⟨i.val / (L+(d+2)), (Nat.div_lt_iff_lt_mul hK).2 i.2⟩ (i.val % (L+(d+2)))
          (Nat.mod_lt _ hK) = i := Fin.ext (Nat.div_add_mod' _ _)
      rwa [e] at this
  let f : (Fin (t*(L+(d+2))) → Bool) → Fin t → Fin d → Bool :=
    fun x h j => rd hn x (h.val*(L+(d+2)) + (j.val + 2))
  let G : (p : Fin t → Fin d → Bool) → Finset (Fin t → Fin (L+(d+2)) → Bool) := fun p =>
    Fintype.piFinset (fun h =>
      univ.filter (sat836 base0 port0 (alh digits h) (pk false (p h)) (pk true (p (nx ht h)))))
  have tl0 : ∀ x, (∀ i, Row hn base0 port0 digits x i) → ∀ h : Fin t,
      (rd hn x (h.val*(L+(d+2)) + L) = true ∧ rd hn x (h.val*(L+(d+2)) + L + 1) = false) ∧
      rd hn x ((nx ht h).val*(L+(d+2))) = false := by
    intro x hx h
    have := (rowTail hn ht base0 port0 digits x h 0 (by omega)).1 (hx _)
    simp only [tailB, decide_true, ite_true, Bool.and_eq_true, Bool.not_eq_true'] at this
    simpa using this
  have tlS : ∀ x, (∀ i, Row hn base0 port0 digits x i) → ∀ (h : Fin t) (k : ℕ), k+1 < d+2 →
      rd hn x ((nx ht h).val*(L+(d+2)) + (k+1)) = rd hn x (h.val*(L+(d+2)) + (L+(k+1))) := by
    intro x hx h k hk
    have := (rowTail hn ht base0 port0 digits x h (k+1) hk).1 (hx _)
    simp only [tailB, Nat.add_one_ne_zero, decide_false, Bool.false_eq_true, ↓reduceIte,
      beq_iff_eq] at this
    exact this
  have dec : ∀ x, (∀ i, Row hn base0 port0 digits x i) → ∀ h : Fin t,
      sat836 base0 port0 (alh digits h) (pk false (f x h)) (pk true (f x (nx ht h))) (xb hn x h) := by
    intro x hx h
    refine ⟨fun j => ⟨?_, ?_⟩, fun i => (rowIn hn base0 port0 digits x h i.val i.isLt).1 (hx _)⟩
    · rw [modEq (show j.val < L+(d+2) by omega)]
      show rd hn x (h.val*(L+(d+2)) + j.val) = _
      refine Fin.cases ?_ (fun j' => ?_) j
      · have := (tl0 x hx ⟨(h.val + t - 1) % t, Nat.mod_lt _ ht⟩).2
        rw [nx_prev] at this
        simp only [pk, Fin.cases_zero, Fin.val_zero]
        simpa using this
      · refine Fin.cases ?_ (fun j'' => ?_) j'
        · have h1 := tlS x hx ⟨(h.val + t - 1) % t, Nat.mod_lt _ ht⟩ 0 (by omega)
          have h2 := (tl0 x hx ⟨(h.val + t - 1) % t, Nat.mod_lt _ ht⟩).1.2
          rw [nx_prev] at h1
          simp only [pk, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
          exact h1.trans h2
        · simp [f]
    · rw [modEq (show L + j.val < L+(d+2) by omega)]
      show rd hn x (h.val*(L+(d+2)) + (L + j.val)) = _
      refine Fin.cases ?_ (fun j' => ?_) j
      · simp only [pk, Fin.cases_zero, Fin.val_zero]
        simpa using (tl0 x hx h).1.1
      · refine Fin.cases ?_ (fun j'' => ?_) j'
        · simp only [pk, Fin.cases_zero, Fin.cases_succ, Fin.val_zero, Fin.val_succ]
          exact (tl0 x hx h).1.2
        · have := tlS x hx h (j''.val + 1) (by omega)
          simp only [pk, Fin.cases_succ, f, Fin.val_succ]
          exact this.symm
  have hcard : (univ.filter (fun x : Fin (t*(L+(d+2))) → Bool => ∀ i : Fin (t*(L+(d+2))),
      Row hn base0 port0 digits x i)).card = ((univ : Finset (Fin t → Fin d → Bool)).sigma G).card := by
    apply Finset.card_bij (fun x _ => (⟨f x, fun h => xb hn x h⟩ : Σ _ : Fin t → Fin d → Bool,
      Fin t → Fin (L+(d+2)) → Bool))
    · intro x hx
      have hx' := (mem_filter.1 hx).2
      refine mem_sigma.2 ⟨mem_univ _, Fintype.mem_piFinset.2 fun h => ?_⟩
      exact mem_filter.2 ⟨mem_univ _, dec x hx' h⟩
    · intro x _ x' _ hxx
      have hb : (fun h => xb hn x h) = (fun h => xb hn x' h) :=
        congrArg (fun s : (Σ _ : Fin t → Fin d → Bool, Fin t → Fin (L+(d+2)) → Bool) => s.2) hxx
      funext i
      rw [rd_self hn x i, rd_self hn x' i, congrFun hb]
    · rintro ⟨p, y⟩ hp
      have hy : ∀ h, sat836 base0 port0 (alh digits h) (pk false (p h)) (pk true (p (nx ht h))) (y h) :=
        fun h => (mem_filter.1 (Fintype.mem_piFinset.1 (mem_sigma.1 hp).2 h)).2
      have hxb : ∀ h, xb hn (glue y) h = y h := by
        intro h; funext o; exact rd_glue hn y h o.val o.isLt
      have hsat : ∀ i, Row hn base0 port0 digits (glue y) i := by
        rw [allRows]
        intro h o ho
        by_cases hoL : o < L
        · rw [rowIn hn base0 port0 digits (glue y) h o hoL, hxb h]
          exact (hy h).2 ⟨o, hoL⟩
        · obtain ⟨k, rfl⟩ : ∃ k, o = L + k := ⟨o - L, by omega⟩
          have hk : k < d+2 := by omega
          rw [rowTail hn ht base0 port0 digits (glue y) h k hk, rd_glue hn y h (L+k) ho,
            rd_glue hn y (nx ht h) k (by omega)]
          have e1 := ((hy h).1 ⟨k, hk⟩).2
          have e2 := ((hy (nx ht h)).1 ⟨k, hk⟩).1
          rw [modEq (show L + k < L+(d+2) by omega)] at e1
          rw [modEq (show k < L+(d+2) by omega)] at e2
          rw [e1, e2]
          rcases k with _ | k
          · have e3 := ((hy h).1 ⟨1, by omega⟩).2
            rw [modEq (show L + 1 < L+(d+2) by omega)] at e3
            rw [show h.val*(L+(d+2)) + (L+0) + 1 = h.val*(L+(d+2)) + (L+1) by ring,
              rd_glue hn y h (L+1) (by omega), e3]
            simp [tailB, pk_one]
          · rcases k with _ | k
            · simp [tailB, pk_one]
            · have q1 : (⟨k+1+1, hk⟩ : Fin (d+2)) = ((⟨k, by omega⟩ : Fin d).succ).succ := rfl
              rw [q1]
              simp [tailB]
      refine ⟨glue y, mem_filter.2 ⟨mem_univ _, hsat⟩, ?_⟩
      have hf : f (glue y) = p := by
        funext h j
        show rd hn (glue y) (h.val*(L+(d+2)) + (j.val + 2)) = p h j
        rw [rd_glue hn y h (j.val+2) (by omega)]
        have e := ((hy h).1 j.succ.succ).1
        rw [modEq (show j.succ.succ.val < L+(d+2) by simp; omega)] at e
        simpa using e
      exact Sigma.ext hf (heq_of_eq (funext hxb))
  rw [hcard, card_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun h _ => cnt ht base0 port0 hc digits p h

theorem ineq (d q t : ℕ) (hq : 0 < q) :
    t * (q * (2 * (d + 2) + (2 ^ (d + 2) - 1)) + (d + 2)) * 2 ^ (d + 2 + 1) ≤
      80 * t * q * (2 ^ d) ^ 2 := by
  have h1 : 2^(d+2) = 4*2^d := by ring
  have h2 : 2^(d+2+1) = 8*2^d := by ring
  have h3 : d < 2^d := Nat.lt_two_pow_self
  have hM : 0 < 2^d := by positivity
  rw [h1, h2]
  have h4 : q * (2 * (d + 2) + (4 * 2 ^ d - 1)) ≤ q * (8 * 2^d) :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 : 2^d ≤ q * 2^d := Nat.le_mul_of_pos_left _ hq
  have h6 : q * (2 * (d + 2) + (4 * 2 ^ d - 1)) + (d + 2) ≤ 10 * (q * 2^d) := by
    have : q * (8 * 2^d) = 8 * (q * 2^d) := by ring
    omega
  calc t * (q * (2 * (d + 2) + (4 * 2 ^ d - 1)) + (d + 2)) * (8 * 2 ^ d)
      ≤ t * (10 * (q * 2^d)) * (8 * 2^d) := by gcongr
    _ = 80 * t * q * (2 ^ d) ^ 2 := by ring

end PEqualNP.Outside.L_clb_112

open PEqualNP.Outside.L_clb_112 in
theorem PEqualNP.Outside.L_clb_112 :
∀ (d q t : Nat) (hq : 0 < q) (ht : 0 < t),
  let w := d+2
  let m := 2^d
  let block := q*(2*w+(2^w-1))+w
  let n := t*block
  let D := Fin d → Bool
  let E := Fin t × Fin q × D × D
  let S := Fin n × (Fin (w+1) → Bool)
  let next := fun (h : Fin t) => (⟨(h.val+1) % t, Nat.mod_lt _ ht⟩ : Fin t)
  let loc := fun k : Nat => (⟨k % n, Nat.mod_lt _ (Nat.mul_pos ht (Nat.lt_of_lt_of_le (Nat.succ_pos (d+1)) (Nat.le_add_left _ _)))⟩ : Fin n)
  n * 2^(w+1) ≤ 80 * t * q * m^2 ∧
    ∃ (base : S → Bool) (port : E → S),
      Function.Injective port ∧ (∀ e, base (port e) = false) ∧
      (∀ e, (port e).1.val / block = e.1.val) ∧
      ∀ digits : Finset E,
        let weight := fun (layer : Fin t) (u v : D) =>
          (Finset.univ : Finset (Fin q)).sum (fun bit =>
            if (layer,bit,u,v) ∈ digits then 2^bit.val else 0)
        (Finset.univ.filter (fun x : Fin n → Bool => ∀ i : Fin n,
          let s : S := (i,fun j => x (loc (i.val+j.val)))
          base s = true ∨ s ∈ digits.image port)).card =
          (Finset.univ : Finset (Fin t → D)).sum (fun p =>
            (Finset.univ : Finset (Fin t)).prod (fun layerId => weight layerId (p layerId) (p (next layerId)))) := by
  intro d q t hq ht
  dsimp only
  refine ⟨ineq d q t hq, ?_⟩
  obtain ⟨base0, port0, hinj, hb0, -, hc⟩ := C836main d q
  refine ⟨baseF t base0, portF t port0, portF_inj hinj, base_port hb0, port_blk port0,
    fun digits => ?_⟩
  exact count_main ht (Nat.mul_pos ht (by omega)) base0 port0
    (fun dg a b u v => hc dg a b u v) digits
