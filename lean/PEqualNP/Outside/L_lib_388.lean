import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_388_aux

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

end PEqualNP.Outside.L_lib_388_aux

theorem PEqualNP.Outside.L_lib_388 :
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
  exact PEqualNP.Outside.L_lib_388_aux.lfsr_construction d
