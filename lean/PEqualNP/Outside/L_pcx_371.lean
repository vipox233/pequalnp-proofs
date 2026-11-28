import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_371_aux

open scoped BigOperators

lemma add_self_eq_zero {F : Type} [Field F] [Algebra (ZMod 2) F] (x : F) : x + x = 0 := by
  have h2 : (2 : F) = 0 := by
    have h : (2 : ZMod 2) = 0 := by decide
    have hmap := congrArg (algebraMap (ZMod 2) F) h
    rw [map_ofNat, map_zero] at hmap
    exact hmap
  have hmul : x + x = (2 : F) * x := by ring
  rw [hmul, h2, zero_mul]

lemma neg_eq_self {F : Type} [Field F] [Algebra (ZMod 2) F] (x : F) : -x = x := by
  rw [neg_eq_iff_add_eq_zero]
  exact add_self_eq_zero x

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma idx_lt {d r : ℕ} (j : Fin r) (i : ℕ) (hi : i < d) : j.val * d + i < d * r := by
  have h1 : (j.val + 1) * d ≤ r * d := Nat.mul_le_mul_right d j.isLt
  rw [add_mul, one_mul] at h1
  rw [mul_comm d r]
  omega

lemma idx_div {d : ℕ} (hd : 0 < d) (j i : ℕ) (hi : i < d) : (j * d + i) / d = j := by
  rw [mul_comm j d, Nat.mul_add_div hd, Nat.div_eq_of_lt hi, add_zero]

lemma idx_mod {d : ℕ} (j i : ℕ) (hi : i < d) : (j * d + i) % d = i := by
  rw [mul_comm j d, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

lemma a_ne_zero_one {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (d : ℕ) (hd : 2 ≤ d) (hcard : Fintype.card F = 2 ^ d)
    (a : F) (hadj : Algebra.adjoin (ZMod 2) ({a} : Set F) = ⊤) :
    a ≠ 0 ∧ a ≠ 1 ∧ a + 1 ≠ 0 := by
  have hnot_bot : a ∉ (⊥ : Subalgebra (ZMod 2) F) := by
    intro ha
    have hle : Algebra.adjoin (ZMod 2) ({a} : Set F) ≤ ⊥ :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr ha)
    rw [hadj] at hle
    have hsurj : Function.Surjective (algebraMap (ZMod 2) F) := by
      intro x
      have hx : x ∈ (⊥ : Subalgebra (ZMod 2) F) := hle trivial
      exact Algebra.mem_bot.mp hx
    have hle_card : Fintype.card F ≤ Fintype.card (ZMod 2) :=
      Fintype.card_le_of_surjective _ hsurj
    rw [hcard, ZMod.card] at hle_card
    have h4 : 4 ≤ 2 ^ d := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hd)
    omega
  have ha0 : a ≠ 0 := by intro h; subst h; exact hnot_bot (zero_mem _)
  have ha1 : a ≠ 1 := by intro h; subst h; exact hnot_bot (one_mem _)
  have ha1' : a + 1 ≠ 0 := by
    intro h
    apply ha1
    have h1 := congrArg (fun z => z + 1) h
    simp only [add_assoc, add_self_eq_zero, add_zero, zero_add] at h1
    exact h1
  exact ⟨ha0, ha1, ha1'⟩

lemma adjoin_inv_add_one {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (a : F) (hadj : Algebra.adjoin (ZMod 2) ({a} : Set F) = ⊤) (ha1' : a + 1 ≠ 0) :
    Algebra.adjoin (ZMod 2) ({(a + 1)⁻¹} : Set F) = ⊤ := by
  classical
  set b : F := (a + 1)⁻¹
  have hb0 : b ≠ 0 := inv_ne_zero ha1'
  let u : Fˣ := Units.mk0 b hb0
  have hu_pow : u ^ Fintype.card Fˣ = 1 := pow_card_eq_one
  have hpos : 0 < Fintype.card Fˣ := Fintype.card_pos_iff.mpr ⟨1⟩
  have hmul : b * b ^ (Fintype.card Fˣ - 1) = 1 := by
    have h1 : (u : F) ^ Fintype.card Fˣ = 1 := by
      rw [← Units.val_pow_eq_pow_val, hu_pow, Units.val_one]
    have h2 : Fintype.card Fˣ = (Fintype.card Fˣ - 1) + 1 := by omega
    rw [h2, pow_succ'] at h1
    exact h1
  have hbinv : b⁻¹ = b ^ (Fintype.card Fˣ - 1) := by
    apply inv_eq_of_mul_eq_one_right hmul
  have hb_mem : b ∈ Algebra.adjoin (ZMod 2) ({b} : Set F) :=
    Algebra.subset_adjoin (Set.mem_singleton b)
  have hbinv_mem : b⁻¹ ∈ Algebra.adjoin (ZMod 2) ({b} : Set F) := by
    rw [hbinv]
    exact pow_mem hb_mem _
  have ha_eq : a = b⁻¹ + 1 := by
    simp only [b, inv_inv, add_assoc, add_self_eq_zero, add_zero]
  have ha_mem : a ∈ Algebra.adjoin (ZMod 2) ({b} : Set F) := by
    rw [ha_eq]
    exact add_mem hbinv_mem (one_mem _)
  have hle : Algebra.adjoin (ZMod 2) ({a} : Set F) ≤ Algebra.adjoin (ZMod 2) ({b} : Set F) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ha_mem)
  rw [hadj] at hle
  exact top_unique hle

def powEval {F : Type} [Field F] [Algebra (ZMod 2) F] (d : ℕ) (b : F) :
    (Fin d → ZMod 2) →ₗ[ZMod 2] F where
  toFun c := ∑ i : Fin d, c i • b ^ i.val
  map_add' c₁ c₂ := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' s c := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

lemma powEval_bijective {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (d : ℕ) (hcard : Fintype.card F = 2 ^ d)
    (b : F) (hadj : Algebra.adjoin (ZMod 2) ({b} : Set F) = ⊤) :
    Function.Bijective (powEval d b) := by
  have hinj : Function.Injective (powEval d b) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hne
    have hex : ∃ i : Fin d, c i ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (funext hall)
    let S : Finset (Fin d) := Finset.univ.filter (fun i => c i ≠ 0)
    have hS : S.Nonempty := by
      rcases hex with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    let k : Fin d := S.max' hS
    have hk_mem : k ∈ S := Finset.max'_mem S hS
    have hck : c k = 1 := by
      have h1 : c k ≠ 0 := (Finset.mem_filter.mp hk_mem).2
      rcases zmod2_eq_zero_or_one (c k) with h0 | h1'
      · exact (h1 h0).elim
      · exact h1'
    have hgt : ∀ i : Fin d, k < i → c i = 0 := by
      intro i hi
      by_contra hci
      have himem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hci⟩
      have hle : i ≤ k := Finset.le_max' S i himem
      exact not_lt_of_ge hle hi
    have hbk_eq : b ^ k.val = ∑ i ∈ Finset.univ.filter (fun i : Fin d => i < k), c i • b ^ i.val := by
      have hsum : (∑ i : Fin d, c i • b ^ i.val) =
          c k • b ^ k.val + ∑ i ∈ Finset.univ.filter (fun i : Fin d => i < k), c i • b ^ i.val := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
        congr 1
        symm
        refine Finset.sum_subset (fun i hi => Finset.mem_erase.mpr ⟨ne_of_lt (Finset.mem_filter.mp hi).2, Finset.mem_univ i⟩) ?_
        intro i hi hnot
        have hne_k : i ≠ k := (Finset.mem_erase.mp hi).1
        have hnotlt : ¬ (i < k) := by
          intro hlt
          exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
        have hlt_k : k < i := lt_of_le_of_ne (le_of_not_gt hnotlt) hne_k.symm
        rw [hgt i hlt_k, zero_smul]
      rw [powEval, LinearMap.coe_mk, AddHom.coe_mk] at hc
      rw [hsum, hck, one_smul] at hc
      have hadd := congrArg (fun z => z + b ^ k.val) hc
      simp only [zero_add] at hadd
      rw [← hadd, add_comm (b ^ k.val), add_assoc, add_self_eq_zero, add_zero]
    let W : Submodule (ZMod 2) F :=
      Submodule.span (ZMod 2) (Set.range (fun j : Fin k.val => b ^ j.val))
    have hpow_in_W : ∀ m : ℕ, b ^ m ∈ W := by
      intro m
      induction m with
      | zero =>
        by_cases hk0 : k.val = 0
        · exfalso
          have hemp : Finset.univ.filter (fun i : Fin d => i < k) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
            intro hlt
            have : i.val < k.val := hlt
            omega
          rw [hemp, Finset.sum_empty, hk0, pow_zero] at hbk_eq
          exact one_ne_zero hbk_eq
        · exact Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
      | succ m ih =>
        have hmul_W : ∀ x ∈ W, b * x ∈ W := by
          intro x hx
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
          · rintro _ ⟨j, rfl⟩
            have hbj : b * b ^ j.val = b ^ (j.val + 1) := by rw [pow_succ']
            rw [hbj]
            by_cases hlt : j.val + 1 < k.val
            · exact Submodule.subset_span ⟨⟨j.val + 1, hlt⟩, rfl⟩
            · have heq : j.val + 1 = k.val := by omega
              rw [heq, hbk_eq]
              refine Submodule.sum_mem W (fun i hi => ?_)
              have hilt : i.val < k.val := (Finset.mem_filter.mp hi).2
              exact Submodule.smul_mem W (c i) (Submodule.subset_span ⟨⟨i.val, hilt⟩, rfl⟩)
          · rw [mul_zero]; exact W.zero_mem
          · intro x y _ _ hx' hy'; rw [mul_add]; exact W.add_mem hx' hy'
          · intro s x _ hx'; rw [Algebra.mul_smul_comm]; exact W.smul_mem s hx'
        rw [pow_succ']
        exact hmul_W _ ih
    have hmul_closed : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W := by
      intro x hx y hy
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        have hstep : ∀ n : ℕ, ∀ z ∈ W, b ^ n * z ∈ W := by
          intro n
          induction n with
          | zero => intro z hz; simpa using hz
          | succ n ihn =>
            intro z hz
            rw [pow_succ', mul_assoc]
            have h1 : b ^ n * z ∈ W := ihn z hz
            refine Submodule.span_induction ?_ ?_ ?_ ?_ h1
            · rintro _ ⟨j', rfl⟩
              rw [← pow_succ']
              exact hpow_in_W (j'.val + 1)
            · rw [mul_zero]; exact W.zero_mem
            · intro u v _ _ hu hv; rw [mul_add]; exact W.add_mem hu hv
            · intro s u _ hu; rw [Algebra.mul_smul_comm]; exact W.smul_mem s hu
        exact hstep j.val y hy
      · rw [zero_mul]; exact W.zero_mem
      · intro u v _ _ hu hv; rw [add_mul]; exact W.add_mem hu hv
      · intro s u _ hu; rw [Algebra.smul_mul_assoc]; exact W.smul_mem s hu
    let A : Subalgebra (ZMod 2) F :=
      { carrier := W
        mul_mem' := fun hx hy => hmul_closed _ hx _ hy
        one_mem' := by simpa using hpow_in_W 0, add_mem' := W.add_mem
        zero_mem' := W.zero_mem
        algebraMap_mem' := fun s => by
          rw [Algebra.algebraMap_eq_smul_one]
          exact W.smul_mem s (by simpa using hpow_in_W 0) }
    have hb_in_A : b ∈ A := by
      change b ∈ W
      simpa using hpow_in_W 1
    have htop_le : (⊤ : Subalgebra (ZMod 2) F) ≤ A := by
      rw [← hadj]
      exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hb_in_A)
    have hW_top : ∀ x : F, x ∈ W := fun x => htop_le trivial
    have hsurj : Function.Surjective (fun f : Fin k.val → ZMod 2 => ∑ j : Fin k.val, f j • b ^ j.val) := by
      intro x
      have hx : x ∈ W := hW_top x
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        simp [Pi.single_apply]
      · exact ⟨0, by simp⟩
      · rintro u v _ _ ⟨fu, hfu⟩ ⟨fv, hfv⟩
        refine ⟨fu + fv, ?_⟩
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hfu, hfv]
      · rintro s u _ ⟨fu, hfu⟩
        refine ⟨s • fu, ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, hfu]
    have hle_card : Fintype.card F ≤ Fintype.card (Fin k.val → ZMod 2) :=
      Fintype.card_le_of_surjective _ hsurj
    rw [hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hle_card
    have hlt_pow : 2 ^ k.val < 2 ^ d := Nat.pow_lt_pow_right (by norm_num) k.isLt
    omega
  have hcard_eq : Fintype.card (Fin d → ZMod 2) = Fintype.card F := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin, hcard]
  exact (Fintype.bijective_iff_injective_and_card (powEval d b)).mpr ⟨hinj, hcard_eq⟩

lemma exists_nonzero_form {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (d : ℕ) (hd : 2 ≤ d) (hcard : Fintype.card F = 2 ^ d)
    (b : F) (hadj : Algebra.adjoin (ZMod 2) ({b} : Set F) = ⊤) :
    ∃ φ : F →ₗ[ZMod 2] ZMod 2, φ ≠ 0 := by
  have hbij := powEval_bijective d hcard b hadj
  let e : (Fin d → ZMod 2) ≃ₗ[ZMod 2] F := LinearEquiv.ofBijective (powEval d b) hbij
  let proj0 : (Fin d → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.proj (⟨0, by omega⟩ : Fin d)
  refine ⟨proj0.comp e.symm.toLinearMap, ?_⟩
  intro h0
  have h1 : (proj0.comp e.symm.toLinearMap) (e (Pi.single ⟨0, by omega⟩ 1)) = 0 := by
    rw [h0]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    proj0, LinearMap.proj_apply, Pi.single_eq_same] at h1
  exact one_ne_zero h1

lemma form_surjective {F : Type} [Field F] [Algebra (ZMod 2) F]
    (φ : F →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) :
    Function.Surjective φ := by
  have hex : ∃ x : F, φ x ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hφ (LinearMap.ext hall)
  rcases hex with ⟨x, hx⟩
  have hx1 : φ x = 1 := by
    rcases zmod2_eq_zero_or_one (φ x) with h0 | h1
    · exact (hx h0).elim
    · exact h1
  intro z
  rcases zmod2_eq_zero_or_one z with rfl | rfl
  · exact ⟨0, map_zero φ⟩
  · exact ⟨x, hx1⟩

lemma form_mul_eq_zero_imp {F : Type} [Field F] [Algebra (ZMod 2) F]
    (φ : F →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0) (u : F)
    (h : ∀ y : F, φ (u * y) = 0) : u = 0 := by
  by_contra hu
  rcases form_surjective φ hφ 1 with ⟨w, hw⟩
  have h1 := h (u⁻¹ * w)
  rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, hw] at h1
  exact one_ne_zero h1

def pairF {F : Type} [Field F] {r : ℕ} (u y : Fin r → F) : F :=
  ∑ j : Fin r, u j * y j

def pairZ {F : Type} [Field F] [Algebra (ZMod 2) F] {r : ℕ}
    (φ : F →ₗ[ZMod 2] ZMod 2) (u y : Fin r → F) : ZMod 2 :=
  φ (pairF u y)

lemma pairF_add_left {F : Type} [Field F] {r : ℕ} (u₁ u₂ y : Fin r → F) :
    pairF (u₁ + u₂) y = pairF u₁ y + pairF u₂ y := by
  simp only [pairF, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma pairF_add_right {F : Type} [Field F] {r : ℕ} (u y₁ y₂ : Fin r → F) :
    pairF u (y₁ + y₂) = pairF u y₁ + pairF u y₂ := by
  simp only [pairF, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma pairF_smul_left {F : Type} [Field F] {r : ℕ} (s : F) (u y : Fin r → F) :
    pairF (s • u) y = s * pairF u y := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

lemma pairF_smul_right {F : Type} [Field F] {r : ℕ} (s : F) (u y : Fin r → F) :
    pairF u (s • y) = s * pairF u y := by
  simp only [pairF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => by ring)

lemma pairZ_add_right {F : Type} [Field F] [Algebra (ZMod 2) F] {r : ℕ}
    (φ : F →ₗ[ZMod 2] ZMod 2) (u y₁ y₂ : Fin r → F) :
    pairZ φ u (y₁ + y₂) = pairZ φ u y₁ + pairZ φ u y₂ := by
  simp only [pairZ, pairF_add_right, map_add]

lemma repr_linear_form {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    {d r : ℕ} (hcard : Fintype.card F = 2 ^ d)
    (e : (Fin d → ZMod 2) ≃ₗ[ZMod 2] F)
    (φ : F →ₗ[ZMod 2] ZMod 2) (hφ : φ ≠ 0)
    (l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2) :
    ∃ (c : ZMod 2) (u : Fin r → F),
      ∀ (t : ZMod 2) (y : Fin r → F), l (t, y) = c * t + pairZ φ u y := by
  classical
  let dualEval : (F →ₗ[ZMod 2] ZMod 2) → (Fin d → ZMod 2) :=
    fun f i => f (e (Pi.single i 1))
  have hdual_inj : Function.Injective dualEval := by
    intro f₁ f₂ h
    ext x
    have hx : x = ∑ i : Fin d, (e.symm x i) • e (Pi.single i 1) := by
      have h1 : e.symm x = ∑ i : Fin d, (e.symm x i) • Pi.single i (1 : ZMod 2) := by
        ext i; simp [Pi.single_apply]
      calc
        x = e (e.symm x) := (e.apply_symm_apply x).symm
        _ = e (∑ i : Fin d, (e.symm x i) • Pi.single i (1 : ZMod 2)) := by rw [← h1]
        _ = ∑ i : Fin d, (e.symm x i) • e (Pi.single i 1) := by simp [map_sum, map_smul]
    rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [map_smul]
    have hi : f₁ (e (Pi.single i 1)) = f₂ (e (Pi.single i 1)) := congrFun h i
    rw [hi]
  let ψ : F → (Fin d → ZMod 2) := fun a i => φ (a * e (Pi.single i 1))
  have hψ_inj : Function.Injective ψ := by
    intro a₁ a₂ h
    have hdiff : ∀ x : F, φ ((a₁ + a₂) * x) = 0 := by
      intro x
      have hx : x = ∑ i : Fin d, (e.symm x i) • e (Pi.single i 1) := by
        have h1 : e.symm x = ∑ i : Fin d, (e.symm x i) • Pi.single i (1 : ZMod 2) := by
          ext i; simp [Pi.single_apply]
        calc
          x = e (e.symm x) := (e.apply_symm_apply x).symm
          _ = e (∑ i : Fin d, (e.symm x i) • Pi.single i (1 : ZMod 2)) := by rw [← h1]
          _ = ∑ i : Fin d, (e.symm x i) • e (Pi.single i 1) := by simp [map_sum, map_smul]
      rw [hx, Finset.mul_sum, map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Algebra.mul_smul_comm, map_smul, add_mul, map_add]
      have hi := congrFun h i
      simp only [ψ] at hi
      rw [hi, zmod2_add_self, smul_zero]
    have hsum0 : a₁ + a₂ = 0 := form_mul_eq_zero_imp φ hφ (a₁ + a₂) hdiff
    have h2 := congrArg (fun z => z + a₂) hsum0
    simp only [add_assoc, add_self_eq_zero, add_zero, zero_add] at h2
    exact h2
  have hψ_bij : Function.Bijective ψ :=
    (Fintype.bijective_iff_injective_and_card ψ).mpr
      ⟨hψ_inj, by rw [hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin]⟩
  let c : ZMod 2 := l (1, 0)
  have hu_ex : ∀ j : Fin r, ∃ uj : F, ∀ x : F, l (0, Pi.single (M := fun _ : Fin r => F) j x) = φ (uj * x) := by
    intro j
    let lj : F →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => l (0, Pi.single (M := fun _ : Fin r => F) j x)
        map_add' := fun x₁ x₂ => by
          have h : ((0 : ZMod 2), Pi.single (M := fun _ : Fin r => F) j (x₁ + x₂)) =
              ((0 : ZMod 2), Pi.single (M := fun _ : Fin r => F) j x₁) +
              ((0 : ZMod 2), Pi.single (M := fun _ : Fin r => F) j x₂) := by
            apply Prod.ext
            · simp
            · ext i; simp [Pi.single_apply]; split_ifs <;> simp
          rw [h, map_add]
        map_smul' := fun s x => by
          have h : ((0 : ZMod 2), Pi.single (M := fun _ : Fin r => F) j (s • x)) =
              s • ((0 : ZMod 2), Pi.single (M := fun _ : Fin r => F) j x) := by
            apply Prod.ext
            · simp
            · ext i; simp [Pi.single_apply]
          rw [h, map_smul]; rfl }
    rcases hψ_bij.2 (dualEval lj) with ⟨uj, huj⟩
    let gj : F →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => φ (uj * x)
        map_add' := fun x₁ x₂ => by rw [mul_add, map_add]
        map_smul' := fun s x => by simp only [RingHom.id_apply, Algebra.mul_smul_comm, map_smul] }
    have hEq : gj = lj := hdual_inj huj
    exact ⟨uj, fun x => (LinearMap.congr_fun hEq x).symm⟩
  choose u hu using hu_ex
  refine ⟨c, u, ?_⟩
  intro t y
  have hdecomp : (t, y) = t • ((1 : ZMod 2), (0 : Fin r → F)) +
      ∑ j : Fin r, ((0 : ZMod 2), Pi.single (M := fun _ : Fin r => F) j (y j)) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul, mul_one, Prod.fst_sum,
        Finset.sum_const_zero, add_zero]
    · ext i
      simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add, Prod.snd_sum,
        Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [hdecomp, map_add, map_smul, map_sum, smul_eq_mul]
  have hmul : t * l (1, 0) = c * t := mul_comm t c
  rw [hmul]
  congr 1
  simp only [pairZ, pairF, map_sum]
  refine Finset.sum_congr rfl (fun j _ => hu j (y j))

lemma exists_orth_vec {F : Type} [Field F] {r : ℕ}
    (U : Submodule F (Fin r → F)) (u : Fin r → F) (hu : u ∉ U) :
    ∃ v : Fin r → F, (∀ w ∈ U, pairF w v = 0) ∧ pairF u v = 1 := by
  let q : (Fin r → F) →ₗ[F] ((Fin r → F) ⧸ U) := U.mkQ
  have hqu : q u ≠ 0 := by
    intro h0
    exact hu ((Submodule.Quotient.mk_eq_zero U).mp h0)
  let L : Submodule F ((Fin r → F) ⧸ U) := Submodule.span F {q u}
  rcases Submodule.exists_isCompl L with ⟨W, hW⟩
  let eL : F ≃ₗ[F] L :=
    (LinearEquiv.toSpanNonzeroSingleton F ((Fin r → F) ⧸ U) (q u) hqu)
  let projL : ((Fin r → F) ⧸ U) →ₗ[F] L := Submodule.linearProjOfIsCompl L W hW
  let ψ : (Fin r → F) →ₗ[F] F := (eL.symm.toLinearMap.comp projL).comp q
  have hψ_U : ∀ w ∈ U, ψ w = 0 := by
    intro w hw
    simp only [ψ, LinearMap.comp_apply, q, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero U).mpr hw, map_zero]
  have hψ_u : ψ u = 1 := by
    have hmem : q u ∈ L := Submodule.subset_span (Set.mem_singleton (q u))
    have hproj : projL (q u) = ⟨q u, hmem⟩ := Submodule.linearProjOfIsCompl_apply_left hW ⟨q u, hmem⟩
    have heL1 : eL 1 = ⟨q u, hmem⟩ := by
      apply Subtype.ext
      change (1 : F) • q u = q u
      exact one_smul F (q u)
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, hproj, ← heL1,
      LinearEquiv.symm_apply_apply]
  let v : Fin r → F := fun j => ψ (Pi.single j 1)
  have hpair_eq : ∀ w : Fin r → F, pairF w v = ψ w := by
    intro w
    have hw : w = ∑ j : Fin r, w j • Pi.single j (1 : F) := by
      ext i
      simp [Pi.single_apply]
    conv_rhs => rw [hw]
    rw [map_sum]
    simp only [pairF, v, map_smul, smul_eq_mul]
  exact ⟨v, fun w hw => by rw [hpair_eq, hψ_U w hw], by rw [hpair_eq, hψ_u]⟩

lemma finrank_sup_span_eq_add_one {F : Type} [Field F] {r : ℕ}
    (U : Submodule F (Fin r → F)) (u : Fin r → F) (hu : u ∉ U) :
    Module.finrank F (U ⊔ Submodule.span F {u} : Submodule F (Fin r → F)) =
      Module.finrank F U + 1 := by
  have hu0 : u ≠ 0 := by intro h; subst h; exact hu U.zero_mem
  have hinf : U ⊓ Submodule.span F {u} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxU, hxS⟩
    change x ∈ Submodule.span F {u} at hxS
    rw [Submodule.mem_span_singleton] at hxS
    rcases hxS with ⟨s, rfl⟩
    by_cases hs : s = 0
    · simp [hs]
    · exfalso
      have : u ∈ U := by
        have h1 := U.smul_mem s⁻¹ hxU
        rwa [smul_smul, inv_mul_cancel₀ hs, one_smul] at h1
      exact hu this
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span F {u})
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hu0] at hmod
  exact hmod

lemma shape_prefix_mem {N J : Finset (List Bool)}
    (hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) :
    ∀ (p q : List Bool), q ∈ N → p <+: q → p ∈ N := by
  intro p q hq hpq
  rcases hpq with ⟨t, rfl⟩
  induction t using List.reverseRecOn with
  | nil => simpa using hq
  | append_singleton t b ih =>
    rw [← List.append_assoc] at hq
    have hmemJ : p ++ t ∈ J := hshape.2.2.1 (p ++ t) b hq
    exact ih (hshape.2.1 hmemJ)

lemma shape_strict_prefix_mem_J {N J : Finset (List Bool)}
    (hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    {p q : List Bool} (hq : q ∈ N) (hpq : p <+: q) (hne : p ≠ q) : p ∈ J := by
  rcases hpq with ⟨t, rfl⟩
  cases t with
  | nil => exact (hne (by simp)).elim
  | cons b rest =>
    have hpb_pref : p ++ [b] <+: p ++ (b :: rest) := ⟨rest, by simp⟩
    have hpb_mem : p ++ [b] ∈ N := shape_prefix_mem hshape (p ++ [b]) (p ++ (b :: rest)) hq hpb_pref
    exact hshape.2.2.1 p b hpb_mem

lemma shape_tree_sum_le {N J : Finset (List Bool)}
    (hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (Φ : List Bool → ℕ)
    (hstep : ∀ p ∈ J, Φ (p ++ [false]) + Φ (p ++ [true]) ≤ Φ p) :
    (∑ p ∈ N \ J, Φ p) ≤ Φ [] := by
  let M : ℕ := N.sup List.length
  have hlen_le : ∀ p ∈ N, p.length ≤ M := fun p hp => Finset.le_sup (f := List.length) hp
  have hind : ∀ m : ℕ, ∀ p ∈ N, M - p.length ≤ m →
      (∑ q ∈ (N \ J).filter (fun q => p <+: q), Φ q) ≤ Φ p := by
    intro m
    induction m with
    | zero =>
      intro p hp hm
      have hp_notJ : p ∉ J := by
        intro hpJ
        have h1 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
        have h2 : (p ++ [false]).length ≤ M := hlen_le _ h1
        simp only [List.length_append, List.length_singleton] at h2
        omega
      have hfilt : (N \ J).filter (fun q => p <+: q) = {p} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hqN, _⟩, hpq⟩
          by_contra hne
          exact hp_notJ (shape_strict_prefix_mem_J hshape hqN hpq (Ne.symm hne))
        · rintro rfl
          exact ⟨⟨hp, hp_notJ⟩, List.prefix_refl _⟩
      rw [hfilt, Finset.sum_singleton]
    | succ m ih =>
      intro p hp hm
      by_cases hpJ : p ∈ J
      · have hfN : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
        have htN : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
        have hdisj : Disjoint
            ((N \ J).filter (fun q => p ++ [false] <+: q))
            ((N \ J).filter (fun q => p ++ [true] <+: q)) := by
          rw [Finset.disjoint_left]
          intro q hqf hqt
          rcases (Finset.mem_filter.mp hqf).2 with ⟨rf, hrf⟩
          rcases (Finset.mem_filter.mp hqt).2 with ⟨rt, hrt⟩
          have h1 : p ++ (false :: rf) = p ++ (true :: rt) := by
            simpa [List.append_assoc] using hrf.trans hrt.symm
          have h2 : false :: rf = true :: rt := List.append_cancel_left h1
          exact Bool.noConfusion (List.cons.inj h2).1
        have hunion : (N \ J).filter (fun q => p <+: q) =
            (N \ J).filter (fun q => p ++ [false] <+: q) ∪
            (N \ J).filter (fun q => p ++ [true] <+: q) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨hqN, hqnotJ⟩, ⟨t, rfl⟩⟩
            cases t with
            | nil => exact (hqnotJ (by simpa using hpJ)).elim
            | cons b rest =>
              cases b
              · left; exact ⟨⟨hqN, hqnotJ⟩, ⟨rest, by simp⟩⟩
              · right; exact ⟨⟨hqN, hqnotJ⟩, ⟨rest, by simp⟩⟩
          · rintro (⟨hq, hpf⟩ | ⟨hq, hpt⟩)
            · exact ⟨hq, (List.prefix_append p [false]).trans hpf⟩
            · exact ⟨hq, (List.prefix_append p [true]).trans hpt⟩
        rw [hunion, Finset.sum_union hdisj]
        have ihf := ih (p ++ [false]) hfN (by simp; omega)
        have iht := ih (p ++ [true]) htN (by simp; omega)
        have hs := hstep p hpJ
        omega
      · have hfilt : (N \ J).filter (fun q => p <+: q) = {p} := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hqN, _⟩, hpq⟩
            by_contra hne
            exact hpJ (shape_strict_prefix_mem_J hshape hqN hpq (Ne.symm hne))
          · rintro rfl
            exact ⟨⟨hp, hpJ⟩, List.prefix_refl _⟩
        rw [hfilt, Finset.sum_singleton]
  have hroot := hind M [] hshape.1 (by simp)
  have hfilt_root : (N \ J).filter (fun q => [] <+: q) = N \ J := by
    ext q
    simp only [Finset.mem_filter, List.nil_prefix, and_true]
  rwa [hfilt_root] at hroot

lemma shape_tree_sum_eq {N J : Finset (List Bool)}
    (hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (Φ : List Bool → ℕ)
    (hstep : ∀ p ∈ J, Φ (p ++ [false]) + Φ (p ++ [true]) = Φ p) :
    (∑ p ∈ N \ J, Φ p) = Φ [] := by
  let M : ℕ := N.sup List.length
  have hlen_le : ∀ p ∈ N, p.length ≤ M := fun p hp => Finset.le_sup (f := List.length) hp
  have hind : ∀ m : ℕ, ∀ p ∈ N, M - p.length ≤ m →
      (∑ q ∈ (N \ J).filter (fun q => p <+: q), Φ q) = Φ p := by
    intro m
    induction m with
    | zero =>
      intro p hp hm
      have hp_notJ : p ∉ J := by
        intro hpJ
        have h1 : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
        have h2 : (p ++ [false]).length ≤ M := hlen_le _ h1
        simp only [List.length_append, List.length_singleton] at h2
        omega
      have hfilt : (N \ J).filter (fun q => p <+: q) = {p} := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hqN, _⟩, hpq⟩
          by_contra hne
          exact hp_notJ (shape_strict_prefix_mem_J hshape hqN hpq (Ne.symm hne))
        · rintro rfl
          exact ⟨⟨hp, hp_notJ⟩, List.prefix_refl _⟩
      rw [hfilt, Finset.sum_singleton]
    | succ m ih =>
      intro p hp hm
      by_cases hpJ : p ∈ J
      · have hfN : p ++ [false] ∈ N := (hshape.2.2.2 p hpJ).1
        have htN : p ++ [true] ∈ N := (hshape.2.2.2 p hpJ).2
        have hdisj : Disjoint
            ((N \ J).filter (fun q => p ++ [false] <+: q))
            ((N \ J).filter (fun q => p ++ [true] <+: q)) := by
          rw [Finset.disjoint_left]
          intro q hqf hqt
          rcases (Finset.mem_filter.mp hqf).2 with ⟨rf, hrf⟩
          rcases (Finset.mem_filter.mp hqt).2 with ⟨rt, hrt⟩
          have h1 : p ++ (false :: rf) = p ++ (true :: rt) := by
            simpa [List.append_assoc] using hrf.trans hrt.symm
          have h2 : false :: rf = true :: rt := List.append_cancel_left h1
          exact Bool.noConfusion (List.cons.inj h2).1
        have hunion : (N \ J).filter (fun q => p <+: q) =
            (N \ J).filter (fun q => p ++ [false] <+: q) ∪
            (N \ J).filter (fun q => p ++ [true] <+: q) := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff]
          constructor
          · rintro ⟨⟨hqN, hqnotJ⟩, ⟨t, rfl⟩⟩
            cases t with
            | nil => exact (hqnotJ (by simpa using hpJ)).elim
            | cons b rest =>
              cases b
              · left; exact ⟨⟨hqN, hqnotJ⟩, ⟨rest, by simp⟩⟩
              · right; exact ⟨⟨hqN, hqnotJ⟩, ⟨rest, by simp⟩⟩
          · rintro (⟨hq, hpf⟩ | ⟨hq, hpt⟩)
            · exact ⟨hq, (List.prefix_append p [false]).trans hpf⟩
            · exact ⟨hq, (List.prefix_append p [true]).trans hpt⟩
        rw [hunion, Finset.sum_union hdisj, ih (p ++ [false]) hfN (by simp; omega),
          ih (p ++ [true]) htN (by simp; omega), hstep p hpJ]
      · have hfilt : (N \ J).filter (fun q => p <+: q) = {p} := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton]
          constructor
          · rintro ⟨⟨hqN, _⟩, hpq⟩
            by_contra hne
            exact hpJ (shape_strict_prefix_mem_J hshape hqN hpq (Ne.symm hne))
          · rintro rfl
            exact ⟨⟨hp, hpJ⟩, List.prefix_refl _⟩
        rw [hfilt, Finset.sum_singleton]
  have hroot := hind M [] hshape.1 (by simp)
  have hfilt_root : (N \ J).filter (fun q => [] <+: q) = N \ J := by
    ext q
    simp only [Finset.mem_filter, List.nil_prefix, and_true]
  rwa [hfilt_root] at hroot

lemma lower_bound_dir {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (d r : ℕ) (hd : 2 ≤ d) (hcard : Fintype.card F = 2 ^ d)
    (a : F) (hadj : Algebra.adjoin (ZMod 2) ({a} : Set F) = ⊤)
    (N J : Finset (List Bool))
    (q : List Bool → (ZMod 2 × (Fin r → F)) → Bool)
    (out : List Bool → (Fin r → F))
    (hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N)
    (hq : ∀ p ∈ J, ∃ (l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
      q p = fun x => decide (l x = b))
    (hleaf : ∀ p ∈ N \ J, ∀ z : ZMod 2 × (Fin r → F),
      (∀ j : Fin p.length, q (p.take j.val) z = p.get j) →
      (if z.1 = 0 then z.2 = out p else z.2 = fun j => a * out p j)) :
    2 ^ (d * r + 1) ≤ (N \ J).card + 2 ^ ((d - 1) * r) := by
  classical
  rcases a_ne_zero_one d hd hcard a hadj with ⟨ha0, ha1, ha1'⟩
  have hadjb := adjoin_inv_add_one a hadj ha1'
  let eF : (Fin d → ZMod 2) ≃ₗ[ZMod 2] F :=
    LinearEquiv.ofBijective (powEval d (a + 1)⁻¹) (powEval_bijective d hcard (a + 1)⁻¹ hadjb)
  rcases exists_nonzero_form d hd hcard (a + 1)⁻¹ hadjb with ⟨φ, hφ⟩
  have hq_repr : ∀ p : List Bool, ∃ (c : ZMod 2) (u : Fin r → F) (b : ZMod 2),
      p ∈ J → ∀ (t : ZMod 2) (y : Fin r → F), q p (t, y) = decide (c * t + pairZ φ u y = b) := by
    intro p
    by_cases hp : p ∈ J
    · rcases hq p hp with ⟨l, b, hlb⟩
      rcases repr_linear_form hcard eF φ hφ l with ⟨c, u, hcu⟩
      refine ⟨c, u, b, fun _ t y => ?_⟩
      rw [hlb]
      exact congrArg (fun z => decide (z = b)) (hcu t y)
    · exact ⟨0, 0, 0, fun h => (hp h).elim⟩
  choose cQ uQ bQ hQ using hq_repr
  let reaches : List Bool → (ZMod 2 × (Fin r → F)) → Prop := fun p z =>
    ∀ j : Fin p.length, q (p.take j.val) z = p.get j
  have hreach_append : ∀ (p : List Bool) (b : Bool) (z : ZMod 2 × (Fin r → F)),
      reaches (p ++ [b]) z ↔ reaches p z ∧ q p z = b := by
    intro p b z
    constructor
    · intro h
      refine ⟨fun j => ?_, ?_⟩
      · have hj : j.val < (p ++ [b]).length := by simp
        have h1 := h ⟨j.val, hj⟩
        have htake : (p ++ [b]).take j.val = p.take j.val :=
          List.take_append_of_le_length (le_of_lt j.isLt)
        have hget : (p ++ [b]).get ⟨j.val, hj⟩ = p.get j := by
          simp [List.getElem_append_left j.isLt]
        rwa [htake, hget] at h1
      · have hlen : p.length < (p ++ [b]).length := by simp
        have h1 := h ⟨p.length, hlen⟩
        have htake : (p ++ [b]).take p.length = p := by simp
        have hget : (p ++ [b]).get ⟨p.length, hlen⟩ = b := by simp
        rwa [htake, hget] at h1
    · rintro ⟨hp, hqpb⟩ j
      by_cases hlt : j.val < p.length
      · have htake : (p ++ [b]).take j.val = p.take j.val :=
          List.take_append_of_le_length (le_of_lt hlt)
        have hget : (p ++ [b]).get j = p.get ⟨j.val, hlt⟩ := by
          simp [List.getElem_append_left hlt]
        rw [htake, hget]
        exact hp ⟨j.val, hlt⟩
      · have heq : j.val = p.length := by
          have hj := j.isLt
          simp only [List.length_append, List.length_singleton] at hj
          omega
        have htake : (p ++ [b]).take j.val = p := by rw [heq]; simp
        have hget : (p ++ [b]).get j = b := by
          have : (p ++ [b])[j.val]'j.isLt = b := by
            simp [heq]
          exact this
        rw [htake, hget]
        exact hqpb
  let z0 : (Fin r → F) → (ZMod 2 × (Fin r → F)) := fun x => (0, x)
  let z1 : (Fin r → F) → (ZMod 2 × (Fin r → F)) := fun x => (1, fun j => a * x j)
  let S0 : List Bool → Finset (Fin r → F) := fun p => Finset.univ.filter (fun x => reaches p (z0 x))
  let S1 : List Bool → Finset (Fin r → F) := fun p => Finset.univ.filter (fun x => reaches p (z1 x))
  let B : List Bool → Finset (Fin r → F) := fun p => S0 p ∩ S1 p
  have hS0_split : ∀ p ∈ J, (S0 (p ++ [false])).card + (S0 (p ++ [true])).card = (S0 p).card := by
    intro p _
    have hdisj : Disjoint (S0 (p ++ [false])) (S0 (p ++ [true])) := by
      rw [Finset.disjoint_left]
      intro x hf ht
      have h1 := ((hreach_append p false (z0 x)).mp (Finset.mem_filter.mp hf).2).2
      have h2 := ((hreach_append p true (z0 x)).mp (Finset.mem_filter.mp ht).2).2
      exact Bool.noConfusion (h1.symm.trans h2)
    have hunion : S0 (p ++ [false]) ∪ S0 (p ++ [true]) = S0 p := by
      ext x
      simp only [S0, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hreach_append]
      cases q p (z0 x) <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hS1_split : ∀ p ∈ J, (S1 (p ++ [false])).card + (S1 (p ++ [true])).card = (S1 p).card := by
    intro p _
    have hdisj : Disjoint (S1 (p ++ [false])) (S1 (p ++ [true])) := by
      rw [Finset.disjoint_left]
      intro x hf ht
      have h1 := ((hreach_append p false (z1 x)).mp (Finset.mem_filter.mp hf).2).2
      have h2 := ((hreach_append p true (z1 x)).mp (Finset.mem_filter.mp ht).2).2
      exact Bool.noConfusion (h1.symm.trans h2)
    have hunion : S1 (p ++ [false]) ∪ S1 (p ++ [true]) = S1 p := by
      ext x
      simp only [S1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hreach_append]
      cases q p (z1 x) <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hsum_S0 : (∑ p ∈ N \ J, (S0 p).card) = 2 ^ (d * r) := by
    rw [shape_tree_sum_eq hshape (fun p => (S0 p).card) hS0_split]
    have hroot : S0 [] = Finset.univ := by
      ext x
      simp [S0, reaches]
    rw [hroot, Finset.card_univ, Fintype.card_fun, hcard, Fintype.card_fin, ← pow_mul]
  have hsum_S1 : (∑ p ∈ N \ J, (S1 p).card) = 2 ^ (d * r) := by
    rw [shape_tree_sum_eq hshape (fun p => (S1 p).card) hS1_split]
    have hroot : S1 [] = Finset.univ := by
      ext x
      simp [S1, reaches]
    rw [hroot, Finset.card_univ, Fintype.card_fun, hcard, Fintype.card_fin, ← pow_mul]
  have hleaf_S : ∀ p ∈ N \ J, (S0 p).card + (S1 p).card ≤ 1 + (B p).card := by
    intro p hp
    have hunion_sub : S0 p ∪ S1 p ⊆ {out p} := by
      intro x hx
      rw [Finset.mem_singleton]
      rcases Finset.mem_union.mp hx with hx0 | hx1
      · have h1 := hleaf p hp (z0 x) (Finset.mem_filter.mp hx0).2
        simpa [z0] using h1
      · have h1 := hleaf p hp (z1 x) (Finset.mem_filter.mp hx1).2
        simp only [z1, one_ne_zero, ↓reduceIte] at h1
        ext j
        have h2 := congrFun h1 j
        exact mul_left_cancel₀ ha0 h2
    have hcard_u : (S0 p ∪ S1 p).card ≤ 1 := by
      exact le_trans (Finset.card_le_card hunion_sub) (by simp)
    have hinc := Finset.card_union_add_card_inter (S0 p) (S1 p)
    change (S0 p ∪ S1 p).card + (B p).card = (S0 p).card + (S1 p).card at hinc
    omega
  have htotal_leaves : 2 ^ (d * r + 1) ≤ (N \ J).card + ∑ p ∈ N \ J, (B p).card := by
    have h1 : (∑ p ∈ N \ J, ((S0 p).card + (S1 p).card)) ≤
        ∑ p ∈ N \ J, (1 + (B p).card) :=
      Finset.sum_le_sum (fun p hp => hleaf_S p hp)
    rw [Finset.sum_add_distrib, hsum_S0, hsum_S1, Finset.sum_add_distrib, Finset.sum_const,
      smul_eq_mul, mul_one] at h1
    have hpow : 2 ^ (d * r + 1) = 2 ^ (d * r) + 2 ^ (d * r) := by rw [pow_succ]; ring
    omega
  let U : List Bool → Submodule F (Fin r → F) := fun p =>
    Submodule.span F (Set.range (fun j : Fin p.length => uQ (p.take j.val)))
  have hU_append : ∀ (p : List Bool) (b : Bool),
      U (p ++ [b]) = U p ⊔ Submodule.span F {uQ p} := by
    intro p b
    dsimp only [U]
    rw [← Submodule.span_union]
    congr 1
    ext w
    simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hlt : j.val < p.length
      · left
        refine ⟨⟨j.val, hlt⟩, ?_⟩
        rw [List.take_append_of_le_length (le_of_lt hlt)]
      · right
        have heq : j.val = p.length := by
          have hj := j.isLt
          simp only [List.length_append, List.length_singleton] at hj
          omega
        have htake : (p ++ [b]).take p.length = p := List.take_left
        rw [heq, htake]
    · rintro (⟨j, rfl⟩ | rfl)
      · refine ⟨⟨j.val, by simp⟩, ?_⟩
        rw [List.take_append_of_le_length (le_of_lt j.isLt)]
      · refine ⟨⟨p.length, by simp⟩, ?_⟩
        have htake : (p ++ [b]).take p.length = p := by simp
        exact congrArg uQ htake
  let Φ : List Bool → ℕ := fun p => 2 ^ Module.finrank F (U p) * (B p).card
  have hΦ_step : ∀ p ∈ J, Φ (p ++ [false]) + Φ (p ++ [true]) ≤ Φ p := by
    intro p hpJ
    have hB_disj : Disjoint (B (p ++ [false])) (B (p ++ [true])) := by
      rw [Finset.disjoint_left]
      intro x hf ht
      have h1 := ((hreach_append p false (z0 x)).mp (Finset.mem_filter.mp (Finset.mem_inter.mp hf).1).2).2
      have h2 := ((hreach_append p true (z0 x)).mp (Finset.mem_filter.mp (Finset.mem_inter.mp ht).1).2).2
      exact Bool.noConfusion (h1.symm.trans h2)
    have hB_sub : B (p ++ [false]) ∪ B (p ++ [true]) ⊆ B p := by
      intro x hx
      rcases Finset.mem_union.mp hx with hf | ht
      · rcases Finset.mem_inter.mp hf with ⟨h0, h1⟩
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ x, ((hreach_append p false (z0 x)).mp (Finset.mem_filter.mp h0).2).1⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ x, ((hreach_append p false (z1 x)).mp (Finset.mem_filter.mp h1).2).1⟩⟩
      · rcases Finset.mem_inter.mp ht with ⟨h0, h1⟩
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ x, ((hreach_append p true (z0 x)).mp (Finset.mem_filter.mp h0).2).1⟩,
           Finset.mem_filter.mpr ⟨Finset.mem_univ x, ((hreach_append p true (z1 x)).mp (Finset.mem_filter.mp h1).2).1⟩⟩
    by_cases huU : uQ p ∈ U p
    · have hU_eq : ∀ b : Bool, U (p ++ [b]) = U p := by
        intro b
        rw [hU_append p b, sup_eq_left]
        exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr huU)
      dsimp only [Φ]
      rw [hU_eq false, hU_eq true, ← mul_add]
      refine Nat.mul_le_mul_left _ ?_
      rw [← Finset.card_union_of_disjoint hB_disj]
      exact Finset.card_le_card hB_sub
    · have hfr : ∀ b : Bool, Module.finrank F (U (p ++ [b])) = Module.finrank F (U p) + 1 := by
        intro b
        rw [hU_append p b]
        exact finrank_sup_span_eq_add_one (U p) (uQ p) huU
      rcases exists_orth_vec (U p) (uQ p) huU with ⟨v, hvU, hvu⟩
      rcases form_surjective φ hφ 1 with ⟨w0, hw0⟩
      let s0 : F := (a + 1)⁻¹ * w0
      have hs0 : φ ((a + 1) * s0) = 1 := by
        simp only [s0, ← mul_assoc, mul_inv_cancel₀ ha1', one_mul, hw0]
      let τ : (Fin r → F) → (Fin r → F) := fun x => x + s0 • v
      have hτ_inv : ∀ x, τ (τ x) = x := by
        intro x
        ext j
        simp only [τ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc, add_self_eq_zero, add_zero]
      have hτ_inj : Function.Injective τ := Function.LeftInverse.injective hτ_inv
      have hτ_B : ∀ x ∈ B p, τ x ∈ B p := by
        intro x hx
        rcases Finset.mem_inter.mp hx with ⟨hx0, hx1⟩
        have hr0 := (Finset.mem_filter.mp hx0).2
        have hr1 := (Finset.mem_filter.mp hx1).2
        have hprefJ : ∀ j : Fin p.length, p.take j.val ∈ J := by
          intro j
          have hmem : p.take j.val ++ [p.get j] <+: p := by
            refine ⟨p.drop (j.val + 1), ?_⟩
            have h1 : p.take (j.val + 1) = p.take j.val ++ [p.get j] := List.take_succ_eq_append_getElem j.isLt
            rw [← h1, List.take_append_drop]
          have hN : p.take j.val ++ [p.get j] ∈ N :=
            shape_prefix_mem hshape _ p (hshape.2.1 hpJ) hmem
          exact hshape.2.2.1 _ _ hN
        have h0' : reaches p (z0 (τ x)) := by
          intro j
          rw [← hr0 j, hQ (p.take j.val) (hprefJ j) 0 (τ x), hQ (p.take j.val) (hprefJ j) 0 x]
          have huj : uQ (p.take j.val) ∈ U p := Submodule.subset_span ⟨j, rfl⟩
          have hzero : pairF (uQ (p.take j.val)) (s0 • v) = 0 := by
            rw [pairF_smul_right, hvU _ huj, mul_zero]
          simp only [τ, pairZ, pairF_add_right, hzero, add_zero]
          rfl
        have h1' : reaches p (z1 (τ x)) := by
          intro j
          rw [← hr1 j, hQ (p.take j.val) (hprefJ j) 1 (fun i => a * (τ x) i),
            hQ (p.take j.val) (hprefJ j) 1 (fun i => a * x i)]
          have huj : uQ (p.take j.val) ∈ U p := Submodule.subset_span ⟨j, rfl⟩
          have heq_y : (fun i => a * (τ x) i) = (fun i => a * x i) + (a * s0) • v := by
            ext i; simp only [τ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
          have hzero : pairF (uQ (p.take j.val)) ((a * s0) • v) = 0 := by
            rw [pairF_smul_right, hvU _ huj, mul_zero]
          simp only [heq_y, pairZ, pairF_add_right, hzero, add_zero]
          rfl
        exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0'⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1'⟩⟩
      let W : Finset (Fin r → F) := B (p ++ [false]) ∪ B (p ++ [true])
      have hτ_out : ∀ x ∈ W, τ x ∈ B p \ W := by
        intro x hx
        have hxB : x ∈ B p := hB_sub hx
        refine Finset.mem_sdiff.mpr ⟨hτ_B x hxB, ?_⟩
        intro hτW
        have hsame : ∀ y ∈ W, q p (z0 y) = q p (z1 y) := by
          intro y hy
          rcases Finset.mem_union.mp hy with hf | ht
          · have h0 := ((hreach_append p false (z0 y)).mp (Finset.mem_filter.mp (Finset.mem_inter.mp hf).1).2).2
            have h1 := ((hreach_append p false (z1 y)).mp (Finset.mem_filter.mp (Finset.mem_inter.mp hf).2).2).2
            exact h0.trans h1.symm
          · have h0 := ((hreach_append p true (z0 y)).mp (Finset.mem_filter.mp (Finset.mem_inter.mp ht).1).2).2
            have h1 := ((hreach_append p true (z1 y)).mp (Finset.mem_filter.mp (Finset.mem_inter.mp ht).2).2).2
            exact h0.trans h1.symm
        have hqx : q p (z0 x) = q p (z1 x) := hsame x hx
        have hqτ : q p (z0 (τ x)) = q p (z1 (τ x)) := hsame (τ x) hτW
        have hval_diff : ∀ y : Fin r → F,
            (q p (z0 y) = q p (z1 y)) ↔
            (cQ p * 0 + pairZ φ (uQ p) y = cQ p * 1 + pairZ φ (uQ p) (fun i => a * y i)) := by
          intro y
          rw [hQ p hpJ 0 y, hQ p hpJ 1 (fun i => a * y i)]
          have hdec : ∀ (A1 A2 b0 : ZMod 2), (decide (A1 = b0) = decide (A2 = b0)) ↔ A1 = A2 := by
            intro A1 A2 b0
            rcases zmod2_eq_zero_or_one A1 with rfl | rfl <;>
            rcases zmod2_eq_zero_or_one A2 with rfl | rfl <;>
            rcases zmod2_eq_zero_or_one b0 with rfl | rfl <;> simp
          exact hdec _ _ _
        have heq1 := (hval_diff x).mp hqx
        have heq2 := (hval_diff (τ x)).mp hqτ
        have hpair0 : pairZ φ (uQ p) (τ x) = pairZ φ (uQ p) x + φ s0 := by
          simp only [τ, pairZ, pairF_add_right, pairF_smul_right, hvu, mul_one, map_add]
        have hpair1 : pairZ φ (uQ p) (fun i => a * (τ x) i) =
            pairZ φ (uQ p) (fun i => a * x i) + φ (a * s0) := by
          have heq_y : (fun i => a * (τ x) i) = (fun i => a * x i) + (a * s0) • v := by
            ext i; simp only [τ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
          simp only [heq_y, pairZ, pairF_add_right, pairF_smul_right, hvu, mul_one, map_add]
        rw [hpair0, hpair1] at heq2
        have hadd := congrArg (fun z => z + (cQ p * 0 + pairZ φ (uQ p) x)) heq2
        rw [heq1] at hadd
        have hcancel : φ s0 = φ (a * s0) := by
          set X1 := cQ p * 1 + pairZ φ (uQ p) (fun i => a * x i)
          have hL : X1 + φ s0 + X1 = φ s0 := by
            rw [add_comm X1 (φ s0), add_assoc, zmod2_add_self, add_zero]
          have hR : X1 + φ (a * s0) + X1 = φ (a * s0) := by
            rw [add_comm X1 (φ (a * s0)), add_assoc, zmod2_add_self, add_zero]
          have h1 : cQ p * 0 + pairZ φ (uQ p) x + φ s0 + X1 =
              cQ p * 1 + pairZ φ (uQ p) (fun i => a * x i) + φ (a * s0) + X1 := by
            simpa [X1, add_assoc] using hadd
          rw [heq1] at h1
          change X1 + φ s0 + X1 = X1 + φ (a * s0) + X1 at h1
          rwa [hL, hR] at h1
        have hsum0 : φ ((a + 1) * s0) = 0 := by
          rw [add_mul, one_mul, map_add, ← hcancel, zmod2_add_self]
        rw [hs0] at hsum0
        exact one_ne_zero hsum0
      have hcard_half : 2 * W.card ≤ (B p).card := by
        have hle_diff : W.card ≤ (B p \ W).card := by
          have himg : W.image τ ⊆ B p \ W := by
            intro y hy
            rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
            exact hτ_out x hx
          rw [← Finset.card_image_of_injective W hτ_inj]
          exact Finset.card_le_card himg
        have hsplit : (B p \ W).card + W.card = (B p).card := Finset.card_sdiff_add_card_eq_card hB_sub
        omega
      have hW_card : W.card = (B (p ++ [false])).card + (B (p ++ [true])).card :=
        Finset.card_union_of_disjoint hB_disj
      simp only [Φ, hfr false, hfr true, pow_succ]
      have hmul : 2 ^ Module.finrank F (U p) * 2 * (B (p ++ [false])).card +
          2 ^ Module.finrank F (U p) * 2 * (B (p ++ [true])).card =
          2 ^ Module.finrank F (U p) * (2 * W.card) := by
        rw [hW_card]; ring
      rw [hmul]
      exact Nat.mul_le_mul_left _ hcard_half
  have hΦ_root : Φ [] = 2 ^ (d * r) := by
    have hU0 : U [] = ⊥ := by
      rw [eq_bot_iff]
      refine Submodule.span_le.mpr ?_
      rintro w ⟨j, _⟩
      exact (Nat.not_lt_zero j.val j.isLt).elim
    have hB0 : B [] = Finset.univ := by
      ext x
      simp [B, S0, S1, reaches]
    dsimp only [Φ]
    rw [hU0, finrank_bot, pow_zero, one_mul, hB0, Finset.card_univ, Fintype.card_fun,
      hcard, Fintype.card_fin, ← pow_mul]
  have hleaf_Φ : ∀ p ∈ N \ J, 2 ^ r * (B p).card ≤ Φ p := by
    intro p hp
    by_cases hBe : (B p).Nonempty
    · rcases hBe with ⟨x, hx⟩
      have hU_top : U p = ⊤ := by
        by_contra hne
        have hex : ∃ u : Fin r → F, u ∉ U p := by
          by_contra hall
          push_neg at hall
          exact hne (eq_top_iff.mpr (fun u _ => hall u))
        rcases hex with ⟨u, hu⟩
        rcases exists_orth_vec (U p) u hu with ⟨v, hvU, hvu⟩
        have hv0 : v ≠ 0 := by
          intro h0; rw [h0] at hvu
          simp only [pairF, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hvu
          exact zero_ne_one hvu
        have hx0 : reaches p (z0 x) := (Finset.mem_filter.mp (Finset.mem_inter.mp hx).1).2
        have hprefJ : ∀ j : Fin p.length, p.take j.val ∈ J := by
          intro j
          have hmem : p.take j.val ++ [p.get j] <+: p := by
            refine ⟨p.drop (j.val + 1), ?_⟩
            have h1 : p.take (j.val + 1) = p.take j.val ++ [p.get j] := List.take_succ_eq_append_getElem j.isLt
            rw [← h1, List.take_append_drop]
          have hN : p.take j.val ++ [p.get j] ∈ N :=
            shape_prefix_mem hshape _ p (Finset.mem_sdiff.mp hp).1 hmem
          exact hshape.2.2.1 _ _ hN
        have hxv0 : reaches p (z0 (x + v)) := by
          intro j
          rw [← hx0 j, hQ (p.take j.val) (hprefJ j) 0 (x + v), hQ (p.take j.val) (hprefJ j) 0 x]
          have huj : uQ (p.take j.val) ∈ U p := Submodule.subset_span ⟨j, rfl⟩
          simp only [pairZ, pairF_add_right, hvU _ huj, add_zero]
          rfl
        have hout1 : x = out p := by simpa [z0] using hleaf p hp (z0 x) hx0
        have hout2 : x + v = out p := by simpa [z0] using hleaf p hp (z0 (x + v)) hxv0
        have hv_eq0 : v = 0 := by
          have h1 : x + v = x := hout2.trans hout1.symm
          have h2 := congrArg (fun z => x + z) h1
          ext i
          have h3 := congrFun h2 i
          simp only [Pi.add_apply, ← add_assoc, add_self_eq_zero, zero_add] at h3
          exact h3
        exact hv0 hv_eq0
      have hfr : Module.finrank F (U p) = r := by
        rw [hU_top, finrank_top, Module.finrank_pi, Fintype.card_fin]
      simp only [Φ, hfr, le_refl]
    · rw [Finset.not_nonempty_iff_eq_empty.mp hBe, Finset.card_empty, mul_zero]
      exact Nat.zero_le _
  have hB_bound : 2 ^ r * (∑ p ∈ N \ J, (B p).card) ≤ 2 ^ (d * r) := by
    rw [Finset.mul_sum]
    calc
      (∑ p ∈ N \ J, 2 ^ r * (B p).card) ≤ ∑ p ∈ N \ J, Φ p :=
        Finset.sum_le_sum (fun p hp => hleaf_Φ p hp)
      _ ≤ Φ [] := shape_tree_sum_le hshape Φ hΦ_step
      _ = 2 ^ (d * r) := hΦ_root
  have hpow_split : 2 ^ (d * r) = 2 ^ r * 2 ^ ((d - 1) * r) := by
    rw [← pow_add]
    congr 1
    have hd1 : d = (d - 1) + 1 := by omega
    conv_lhs => rw [hd1]
    ring
  rw [hpow_split] at hB_bound
  have hB_le : (∑ p ∈ N \ J, (B p).card) ≤ 2 ^ ((d - 1) * r) :=
    Nat.le_of_mul_le_mul_left hB_bound (by positivity)
  omega

lemma inv_coeff_sum_zero {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (d : ℕ) (hd : 2 ≤ d) (hcard : Fintype.card F = 2 ^ d)
    (a : F) (hadj : Algebra.adjoin (ZMod 2) ({a} : Set F) = ⊤)
    (c : Fin d → ZMod 2) (hc : (∑ i : Fin d, c i • ((a + 1)⁻¹ : F) ^ i.val) = a + 1) :
    (∑ i : Fin d, c i) = 0 := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rcases a_ne_zero_one (d' + 1) hd hcard a hadj with ⟨ha0, ha1, ha1'⟩
  set b : F := (a + 1)⁻¹
  have hadjb := adjoin_inv_add_one a hadj ha1'
  have hbij := powEval_bijective (d' + 1) hcard b hadjb
  have hb1 : b + 1 ≠ 0 := by
    intro h0
    have hb_eq1 : b = 1 := by
      have h1 := congrArg (fun z => z + 1) h0
      simp only [add_assoc, add_self_eq_zero, add_zero, zero_add] at h1
      exact h1
    have ha1_eq : a + 1 = 1 := by
      have h1 := congrArg Inv.inv hb_eq1
      simpa [b] using h1
    have ha_eq0 : a = 0 := by
      have h1 := congrArg (fun z => z + 1) ha1_eq
      simp only [add_assoc, add_self_eq_zero, add_zero] at h1
      exact h1
    exact ha0 ha_eq0
  have h1_eq : (1 : F) = ∑ i : Fin (d' + 1), c i • b ^ (i.val + 1) := by
    have hmul := congrArg (fun z => b * z) hc
    simp only [b, inv_mul_cancel₀ ha1', Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Algebra.mul_smul_comm, pow_succ']
  by_contra hsum_ne
  have hsum1 : (∑ i : Fin (d' + 1), c i) = 1 := by
    rcases zmod2_eq_zero_or_one (∑ i : Fin (d' + 1), c i) with h0 | h1
    · exact (hsum_ne h0).elim
    · exact h1
  let s : Fin (d' + 1) → ZMod 2 := fun k => ∑ j ∈ Finset.univ.filter (fun j : Fin (d' + 1) => k ≤ j), c j
  have hs0 : s 0 = 1 := by
    have hfilt : Finset.univ.filter (fun j : Fin (d' + 1) => (0 : Fin (d' + 1)) ≤ j) = Finset.univ := by
      ext j
      simp
    simp only [s, hfilt, hsum1]
  have hs_step : ∀ k : Fin d', s k.castSucc + s k.succ = c k.castSucc := by
    intro k
    have hfilt : Finset.univ.filter (fun j : Fin (d' + 1) => k.castSucc ≤ j) =
        insert k.castSucc (Finset.univ.filter (fun j : Fin (d' + 1) => k.succ ≤ j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.le_iff_val_le_val, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
      omega
    have hk_not : k.castSucc ∉ Finset.univ.filter (fun j : Fin (d' + 1) => k.succ ≤ j) := by
      simp [Fin.le_iff_val_le_val]
    simp only [s, hfilt, Finset.sum_insert hk_not]
    rw [add_assoc, zmod2_add_self, add_zero]
  have hs_last : s (Fin.last d') = c (Fin.last d') := by
    have hfilt : Finset.univ.filter (fun j : Fin (d' + 1) => Fin.last d' ≤ j) = {Fin.last d'} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.le_iff_val_le_val, Fin.ext_iff, Fin.val_last]
      have hj := j.isLt
      omega
    simp only [s, hfilt, Finset.sum_singleton]
  have hprod : (b + 1) * powEval (d' + 1) b s = 0 := by
    rw [add_mul, one_mul]
    simp only [powEval, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
    have hA : (∑ k : Fin (d' + 1), b * (s k • b ^ k.val)) =
        (∑ k : Fin d', s k.castSucc • b ^ (k.val + 1)) + s (Fin.last d') • b ^ (d' + 1) := by
      have h1 : (∑ k : Fin (d' + 1), b * (s k • b ^ k.val)) =
          ∑ k : Fin (d' + 1), s k • b ^ (k.val + 1) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Algebra.mul_smul_comm, pow_succ']
      rw [h1, Fin.sum_univ_castSucc]
      simp
    have hB : (∑ k : Fin (d' + 1), s k • b ^ k.val) =
        s 0 • (1 : F) + ∑ k : Fin d', s k.succ • b ^ (k.val + 1) := by
      rw [Fin.sum_univ_succ]
      simp
    rw [hA, hB, hs0, one_smul, hs_last]
    have hcombine : ((∑ k : Fin d', s k.castSucc • b ^ (k.val + 1)) + c (Fin.last d') • b ^ (d' + 1)) +
        (1 + ∑ k : Fin d', s k.succ • b ^ (k.val + 1)) =
        1 + ((∑ k : Fin d', (s k.castSucc + s k.succ) • b ^ (k.val + 1)) + c (Fin.last d') • b ^ (d' + 1)) := by
      simp only [add_smul, Finset.sum_add_distrib]
      ring
    rw [hcombine]
    have hmid : (∑ k : Fin d', (s k.castSucc + s k.succ) • b ^ (k.val + 1)) + c (Fin.last d') • b ^ (d' + 1) =
        ∑ i : Fin (d' + 1), c i • b ^ (i.val + 1) := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hs_step k]; rfl
    rw [hmid, ← h1_eq, add_self_eq_zero]
  have hs_zero : powEval (d' + 1) b s = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (hb1 h).elim
    · exact h
  have hs_eq0 : s = 0 := hbij.1 (by rw [hs_zero, map_zero])
  have h10 : (1 : ZMod 2) = 0 := by
    rw [← hs0, hs_eq0]; rfl
  exact one_ne_zero h10

lemma upper_bound_dir {F : Type} [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (d r : ℕ) (hd : 2 ≤ d) (hcard : Fintype.card F = 2 ^ d)
    (a : F) (hadj : Algebra.adjoin (ZMod 2) ({a} : Set F) = ⊤) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × (Fin r → F)) → Bool)
      (out : List Bool → (Fin r → F)),
      ([] ∈ N ∧ J ⊆ N ∧
        (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
        ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (∀ p ∈ J, ∃ (l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
        q p = fun x => decide (l x = b)) ∧
      (∀ p ∈ N \ J, ∀ z : ZMod 2 × (Fin r → F),
        (∀ j : Fin p.length, q (p.take j.val) z = p.get j) →
        (if z.1 = 0 then z.2 = out p else z.2 = fun j => a * out p j)) ∧
      (N \ J).card + 2 ^ ((d - 1) * r) = 2 ^ (d * r + 1) := by
  classical
  rcases a_ne_zero_one d hd hcard a hadj with ⟨ha0, ha1, ha1'⟩
  set b : F := (a + 1)⁻¹
  have hadjb := adjoin_inv_add_one a hadj ha1'
  have hbij := powEval_bijective d hcard b hadjb
  rcases exists_nonzero_form d hd hcard b hadjb with ⟨φ, hφ⟩
  have hba : b * a = b + 1 := by
    have h1 : b * (a + 1) = 1 := inv_mul_cancel₀ ha1'
    rw [mul_add, mul_one] at h1
    have h2 := congrArg (fun z => z + b) h1
    simp only [add_assoc, add_self_eq_zero, add_zero] at h2
    rw [add_comm 1 b] at h2
    exact h2
  have hmiracle : ∀ (i : ℕ) (y : F), φ (b ^ (i + 1) * (a * y)) = φ (b ^ (i + 1) * y) + φ (b ^ i * y) := by
    intro i y
    have h1 : b ^ (i + 1) * (a * y) = b ^ (i + 1) * y + b ^ i * y := by
      calc
        b ^ (i + 1) * (a * y) = b ^ i * (b * a) * y := by rw [pow_succ]; ring
        _ = b ^ i * (b + 1) * y := by rw [hba]
        _ = b ^ (i + 1) * y + b ^ i * y := by rw [pow_succ]; ring
    rw [h1, map_add]
  let enc0 : F → (Fin d → ZMod 2) := fun y i => φ (b ^ i.val * y)
  have henc0_lin : ∀ y₁ y₂, enc0 (y₁ + y₂) = enc0 y₁ + enc0 y₂ := by
    intro y₁ y₂; ext i; simp [enc0, mul_add]
  have henc0_inj : Function.Injective enc0 := by
    intro y₁ y₂ h
    have h0 : ∀ i : Fin d, φ (b ^ i.val * (y₁ + y₂)) = 0 := by
      intro i
      have hi := congrFun h i
      simp only [enc0] at hi
      rw [mul_add, map_add, hi, zmod2_add_self]
    have hall : ∀ w : F, φ (w * (y₁ + y₂)) = 0 := by
      intro w
      rcases hbij.2 w with ⟨c, rfl⟩
      simp only [powEval, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, map_sum]
      refine Finset.sum_eq_zero (fun i _ => ?_)
      rw [Algebra.smul_mul_assoc, map_smul, h0 i, smul_zero]
    have hsum0 : y₁ + y₂ = 0 := form_mul_eq_zero_imp φ hφ (y₁ + y₂) (fun w => by
      rw [mul_comm]; exact hall w)
    have h2 := congrArg (fun z => z + y₂) hsum0
    simp only [add_assoc, add_self_eq_zero, add_zero, zero_add] at h2
    exact h2
  have henc0_bij : Function.Bijective enc0 :=
    (Fintype.bijective_iff_injective_and_card enc0).mpr
      ⟨henc0_inj, by rw [hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin]⟩
  let enc1 : F → (Fin d → ZMod 2) := fun y i => φ (b ^ i.val * y) + φ ((a + 1) * y)
  have henc1_inj : Function.Injective enc1 := by
    intro y₁ y₂ h
    let w : F := y₁ + y₂
    let ε : ZMod 2 := φ ((a + 1) * w)
    have hε : ∀ i : Fin d, φ (b ^ i.val * w) = ε := by
      intro i
      have hi := congrFun h i
      simp only [enc1] at hi
      have h1 : φ (b ^ i.val * y₁) + φ ((a + 1) * y₁) + (φ (b ^ i.val * y₂) + φ ((a + 1) * y₂)) = 0 := by
        rw [hi, zmod2_add_self]
      have h2 : φ (b ^ i.val * w) + ε = 0 := by
        have h3 : φ (b ^ i.val * w) = φ (b ^ i.val * y₁) + φ (b ^ i.val * y₂) := by
          simp only [w, mul_add, map_add]
        have h4 : ε = φ ((a + 1) * y₁) + φ ((a + 1) * y₂) := by
          simp only [ε, w, mul_add, map_add]
        rw [h3, h4]
        convert h1 using 1
        ring
      have h3 := congrArg (fun z => z + ε) h2
      simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at h3
      exact h3
    rcases hbij.2 (a + 1) with ⟨c, hc⟩
    have hc_sum : (∑ i : Fin d, c i) = 0 := inv_coeff_sum_zero d hd hcard a hadj c hc
    have hε0 : ε = 0 := by
      have hcalc : ε = ∑ i : Fin d, c i * φ (b ^ i.val * w) := by
        simp only [ε]
        rw [← hc]
        simp only [powEval, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Algebra.smul_mul_assoc, map_smul, smul_eq_mul]
      rw [hcalc]
      have h2 : (∑ i : Fin d, c i * φ (b ^ i.val * w)) = (∑ i : Fin d, c i) * ε := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => by rw [hε i])
      rw [h2, hc_sum, zero_mul]
    have hw_eq : enc0 y₁ = enc0 y₂ := by
      ext i
      have h1 : φ (b ^ i.val * w) = 0 := by rw [hε i, hε0]
      simp only [w, mul_add, map_add] at h1
      have h2 := congrArg (fun z => z + φ (b ^ i.val * y₂)) h1
      simp only [add_assoc, zmod2_add_self, add_zero, zero_add] at h2
      exact h2
    exact henc0_inj hw_eq
  have henc1_bij : Function.Bijective enc1 :=
    (Fintype.bijective_iff_injective_and_card enc1).mpr
      ⟨henc1_inj, by rw [hcard, Fintype.card_fun, ZMod.card, Fintype.card_fin]⟩
  let e0 : F ≃ (Fin d → ZMod 2) := Equiv.ofBijective enc0 henc0_bij
  let e1 : F ≃ (Fin d → ZMod 2) := Equiv.ofBijective enc1 henc1_bij
  let b2z : Bool → ZMod 2 := fun bit => if bit then 1 else 0
  have hb2z_dec : ∀ z : ZMod 2, b2z (decide (z = 1)) = z := by
    intro z; rcases zmod2_eq_zero_or_one z with rfl | rfl <;> simp [b2z]
  let q : List Bool → (ZMod 2 × (Fin r → F)) → Bool := fun p z =>
    if hlt : p.length < d * r then
      let j : Fin r := ⟨p.length / d, Nat.div_lt_of_lt_mul hlt⟩
      let i : ℕ := p.length % d
      if i = 0 then
        decide (φ (z.2 j) = 1)
      else
        let prev : ZMod 2 := b2z (p.getD (p.length - 1) false)
        decide (prev * z.1 + φ (b ^ i * z.2 j) = 1)
    else
      decide (z.1 = 1)
  have hq_valid : ∀ p : List Bool, ∃ (l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2) (b0 : ZMod 2),
      q p = fun z => decide (l z = b0) := by
    intro p
    by_cases hlt : p.length < d * r
    · let j : Fin r := ⟨p.length / d, Nat.div_lt_of_lt_mul hlt⟩
      let i : ℕ := p.length % d
      by_cases hi : i = 0
      · let l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun z => φ (z.2 j)
            map_add' := fun z₁ z₂ => by simp
            map_smul' := fun s z => by simp }
        refine ⟨l, 1, funext (fun z => ?_)⟩
        simp only [q, dif_pos hlt, i, hi, ↓reduceIte, l, LinearMap.coe_mk, AddHom.coe_mk, j]
      · let prev : ZMod 2 := b2z (p.getD (p.length - 1) false)
        let l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2 :=
          { toFun := fun z => prev * z.1 + φ (b ^ i * z.2 j)
            map_add' := fun z₁ z₂ => by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, map_add]; ring
            map_smul' := fun s z => by
              simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
                Algebra.mul_smul_comm, map_smul]; ring }
        refine ⟨l, 1, funext (fun z => ?_)⟩
        simp only [q, dif_pos hlt, i, hi, ↓reduceIte, l, LinearMap.coe_mk, AddHom.coe_mk, j, prev]
    · let l : (ZMod 2 × (Fin r → F)) →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun z => z.1
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      refine ⟨l, 1, funext (fun z => ?_)⟩
      simp only [q, dif_neg hlt, l, LinearMap.coe_mk, AddHom.coe_mk]
  let dec0 : List Bool → (Fin r → F) := fun p j =>
    e0.symm (fun i : Fin d => b2z (p.getD (j.val * d + i.val) false))
  let dec1 : List Bool → (Fin r → F) := fun p j =>
    e1.symm (fun i : Fin d => b2z (p.getD (j.val * d + i.val) false))
  let allFull : Finset (List Bool) :=
    (Finset.univ : Finset (Fin (d * r) → Bool)).image List.ofFn
  have hallFull_len : ∀ p ∈ allFull, p.length = d * r := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨f, _, rfl⟩
    simp
  have hallFull_mem : ∀ p : List Bool, p.length = d * r → p ∈ allFull := by
    intro p hp
    refine Finset.mem_image.mpr ⟨fun k => p.get ⟨k.val, by omega⟩, Finset.mem_univ _, ?_⟩
    apply List.ext_get (by simp [hp])
    intro n h1 h2
    simp
  let goodFull : Finset (List Bool) := allFull.filter (fun p => dec0 p = dec1 p)
  let badFull : Finset (List Bool) := allFull.filter (fun p => dec0 p ≠ dec1 p)
  let prefNodes : Finset (List Bool) :=
    allFull.biUnion (fun p => (Finset.range (d * r)).image (fun k => p.take k))
  let J : Finset (List Bool) := prefNodes ∪ badFull
  let extLeaves : Finset (List Bool) :=
    badFull.image (fun p => p ++ [false]) ∪ badFull.image (fun p => p ++ [true])
  let N : Finset (List Bool) := prefNodes ∪ allFull ∪ extLeaves
  have hmem_pref : ∀ p : List Bool, p ∈ prefNodes ↔ p.length < d * r := by
    intro p
    simp only [prefNodes, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨q0, hq0, k, hk, rfl⟩
      rw [List.length_take, hallFull_len q0 hq0]
      omega
    · intro hlt
      let q0 : List Bool := p ++ List.replicate (d * r - p.length) false
      have hq0_len : q0.length = d * r := by simp [q0]; omega
      refine ⟨q0, hallFull_mem q0 hq0_len, p.length, hlt, ?_⟩
      simp [q0]
  have hmem_J : ∀ p : List Bool, p ∈ J ↔ p.length < d * r ∨ (p.length = d * r ∧ dec0 p ≠ dec1 p) := by
    intro p
    simp only [J, Finset.mem_union, hmem_pref, badFull, Finset.mem_filter]
    constructor
    · rintro (h | ⟨hp, hne⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hallFull_len p hp, hne⟩
    · rintro (h | ⟨hlen, hne⟩)
      · exact Or.inl h
      · exact Or.inr ⟨hallFull_mem p hlen, hne⟩
  have hmem_N : ∀ p : List Bool, p ∈ N ↔
      p.length ≤ d * r ∨ (∃ p0 : List Bool, p0.length = d * r ∧ dec0 p0 ≠ dec1 p0 ∧
        (p = p0 ++ [false] ∨ p = p0 ++ [true])) := by
    intro p
    simp only [N, extLeaves, Finset.mem_union, hmem_pref, Finset.mem_image, badFull, Finset.mem_filter]
    constructor
    · rintro ((h | h) | (⟨p0, ⟨hp0, hne⟩, rfl⟩ | ⟨p0, ⟨hp0, hne⟩, rfl⟩))
      · exact Or.inl (le_of_lt h)
      · exact Or.inl (le_of_eq (hallFull_len p h))
      · exact Or.inr ⟨p0, hallFull_len p0 hp0, hne, Or.inl rfl⟩
      · exact Or.inr ⟨p0, hallFull_len p0 hp0, hne, Or.inr rfl⟩
    · rintro (hle | ⟨p0, hlen, hne, rfl | rfl⟩)
      · by_cases hlt : p.length < d * r
        · exact Or.inl (Or.inl hlt)
        · exact Or.inl (Or.inr (hallFull_mem p (by omega)))
      · exact Or.inr (Or.inl ⟨p0, ⟨hallFull_mem p0 hlen, hne⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨p0, ⟨hallFull_mem p0 hlen, hne⟩, rfl⟩)
  have hshape : [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (b0 : Bool), p ++ [b0] ∈ N → p ∈ J) ∧
      ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hmem_N]; left; simp
    · intro p hp
      rw [hmem_J] at hp
      rw [hmem_N]
      rcases hp with h | ⟨h, _⟩
      · exact Or.inl (le_of_lt h)
      · exact Or.inl (le_of_eq h)
    · intro p b0 hp
      rw [hmem_N] at hp
      rw [hmem_J]
      rcases hp with hle | ⟨p0, hlen, hne, h1 | h1⟩
      · simp only [List.length_append, List.length_singleton] at hle
        exact Or.inl (by omega)
      · have hpeq : p = p0 := (List.append_inj_left' h1 rfl)
        subst hpeq; exact Or.inr ⟨hlen, hne⟩
      · have hpeq : p = p0 := (List.append_inj_left' h1 rfl)
        subst hpeq; exact Or.inr ⟨hlen, hne⟩
    · intro p hp
      rw [hmem_J] at hp
      constructor <;> rw [hmem_N]
      · rcases hp with hlt | ⟨hlen, hne⟩
        · left; simp; omega
        · right; exact ⟨p, hlen, hne, Or.inl rfl⟩
      · rcases hp with hlt | ⟨hlen, hne⟩
        · left; simp; omega
        · right; exact ⟨p, hlen, hne, Or.inr rfl⟩
  let out : List Bool → (Fin r → F) := fun p =>
    if p.length = d * r then dec0 p
    else if p.getD (d * r) false = false then dec0 (p.take (d * r))
    else dec1 (p.take (d * r))
  have hpath_rec0 : ∀ (p : List Bool) (x : Fin r → F),
      (hlen : p.length = d * r) →
      (∀ k : Fin (d * r), q (p.take k.val) (0, x) = p.get ⟨k.val, lt_of_lt_of_eq k.isLt hlen.symm⟩) →
      x = dec0 p := by
    intro p x hlen hpath
    ext j
    apply e0.injective
    simp only [dec0, Equiv.apply_symm_apply]
    ext i
    let idx : ℕ := j.val * d + i.val
    have hidx_lt : idx < d * r := idx_lt j i.val i.isLt
    have hq_idx := hpath ⟨idx, hidx_lt⟩
    have htake_len : (p.take idx).length = idx := List.length_take_of_le (by omega)
    have hdiv : idx / d = j.val := idx_div (by omega) j.val i.val i.isLt
    have hmod : idx % d = i.val := idx_mod j.val i.val i.isLt
    have hgetD : p.getD idx false = p.get ⟨idx, by omega⟩ := by
      rw [List.getD_eq_getElem _ _ (by omega)]; rfl
    rw [hgetD, ← hq_idx]
    simp only [q, htake_len, dif_pos hidx_lt, hdiv, hmod, mul_zero, zero_add]
    by_cases hi0 : i.val = 0
    · simp only [hi0, ↓reduceIte, hb2z_dec, e0, Equiv.ofBijective_apply, enc0, pow_zero, one_mul]
    · simp only [hi0, ↓reduceIte, hb2z_dec, e0, Equiv.ofBijective_apply, enc0]
  have hpath_rec1 : ∀ (p : List Bool) (x : Fin r → F),
      (hlen : p.length = d * r) →
      (∀ k : Fin (d * r), q (p.take k.val) (1, fun j => a * x j) = p.get ⟨k.val, lt_of_lt_of_eq k.isLt hlen.symm⟩) →
      x = dec1 p := by
    intro p x hlen hpath
    ext j
    apply e1.injective
    simp only [dec1, Equiv.apply_symm_apply]
    ext i
    have hind : ∀ (m : ℕ) (hm : m < d),
        b2z (p.getD (j.val * d + m) false) = φ (b ^ m * x j) + φ ((a + 1) * x j) := by
      intro m
      induction m with
      | zero =>
        intro hm
        let idx : ℕ := j.val * d + 0
        have hidx_lt : idx < d * r := idx_lt j 0 hm
        have hq_idx := hpath ⟨idx, hidx_lt⟩
        have htake_len : (p.take idx).length = idx := List.length_take_of_le (by omega)
        have hdiv : idx / d = j.val := idx_div (by omega) j.val 0 hm
        have hmod : idx % d = 0 := idx_mod j.val 0 hm
        have hgetD : p.getD idx false = p.get ⟨idx, by omega⟩ := by
          rw [List.getD_eq_getElem _ _ (by omega)]; rfl
        rw [hgetD, ← hq_idx]
        simp only [q, htake_len, dif_pos hidx_lt, hdiv, hmod, ↓reduceIte, hb2z_dec, pow_zero, one_mul, Fin.eta]
        rw [add_mul, one_mul, map_add, add_comm (φ (a * x j)), ← add_assoc, zmod2_add_self, zero_add]
      | succ m ihm =>
        intro hm
        let idx : ℕ := j.val * d + (m + 1)
        have hidx_lt : idx < d * r := idx_lt j (m + 1) hm
        have hq_idx := hpath ⟨idx, hidx_lt⟩
        have htake_len : (p.take idx).length = idx := List.length_take_of_le (by omega)
        have hdiv : idx / d = j.val := idx_div (by omega) j.val (m + 1) hm
        have hmod : idx % d = m + 1 := idx_mod j.val (m + 1) hm
        have hgetD : p.getD idx false = p.get ⟨idx, by omega⟩ := by
          rw [List.getD_eq_getElem _ _ (by omega)]; rfl
        have hprev : (p.take idx).getD (idx - 1) false = p.getD (j.val * d + m) false := by
          have hsub : idx - 1 = j.val * d + m := by simp only [idx]; omega
          rw [hsub, List.getD_eq_getElem _ _ (by rw [htake_len]; omega),
            List.getD_eq_getElem _ _ (by omega), List.getElem_take]
        rw [hgetD, ← hq_idx]
        simp only [q, htake_len, dif_pos hidx_lt, hdiv, hmod, Nat.add_eq_zero_iff, one_ne_zero,
          and_false, ↓reduceIte, mul_one, hprev, hb2z_dec]
        rw [ihm (by omega), hmiracle m (x j)]
        have hcancel : (φ (b ^ m * x j) + φ ((a + 1) * x j)) + (φ (b ^ (m + 1) * x j) + φ (b ^ m * x j)) =
            φ (b ^ (m + 1) * x j) + φ ((a + 1) * x j) := by
          have h1 : φ (b ^ m * x j) + φ (b ^ m * x j) = 0 := zmod2_add_self _
          calc
            (φ (b ^ m * x j) + φ ((a + 1) * x j)) + (φ (b ^ (m + 1) * x j) + φ (b ^ m * x j))
                = (φ (b ^ m * x j) + φ (b ^ m * x j)) + (φ (b ^ (m + 1) * x j) + φ ((a + 1) * x j)) := by ring
            _ = φ (b ^ (m + 1) * x j) + φ ((a + 1) * x j) := by rw [h1, zero_add]
        exact hcancel
    exact (hind i.val i.isLt).symm
  have hleaf_ok : ∀ p ∈ N \ J, ∀ z : ZMod 2 × (Fin r → F),
      (∀ k : Fin p.length, q (p.take k.val) z = p.get k) →
      (if z.1 = 0 then z.2 = out p else z.2 = fun j => a * out p j) := by
    intro p hp z hpath
    have hpN : p ∈ N := (Finset.mem_sdiff.mp hp).1
    have hpNotJ : p ∉ J := (Finset.mem_sdiff.mp hp).2
    rw [hmem_N] at hpN
    rw [hmem_J] at hpNotJ
    push_neg at hpNotJ
    rcases hpN with hle | ⟨p0, hlen0, hne0, rfl | rfl⟩
    · have hlen : p.length = d * r := by omega
      have heq01 : dec0 p = dec1 p := hpNotJ.2 hlen
      have hout : out p = dec0 p := by simp [out, hlen]
      rw [hout]
      rcases z with ⟨t, y⟩
      rcases zmod2_eq_zero_or_one t with rfl | rfl
      · simp only [↓reduceIte]
        exact hpath_rec0 p y hlen (fun k => by simpa using hpath ⟨k.val, by omega⟩)
      · simp only [one_ne_zero, ↓reduceIte]
        let x : Fin r → F := fun j => a⁻¹ * y j
        have hy : y = fun j => a * x j := by ext j; simp [x, mul_inv_cancel_left₀ ha0]
        rw [hy] at hpath ⊢
        have hx1 : x = dec1 p := hpath_rec1 p x hlen (fun k => by simpa using hpath ⟨k.val, by omega⟩)
        rw [hx1, heq01]
    · have hlen : (p0 ++ [false]).length = d * r + 1 := by simp [hlen0]
      have htake_p0 : (p0 ++ [false]).take (d * r) = p0 := by rw [← hlen0]; simp
      have hget_last : (p0 ++ [false]).getD (d * r) false = false := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [hlen0]
      have hout : out (p0 ++ [false]) = dec0 p0 := by
        simp only [out, hlen, Nat.add_eq_left, one_ne_zero, ↓reduceIte, hget_last, htake_p0]
      rw [hout]
      have hlast := hpath ⟨d * r, by omega⟩
      have htake_last : (p0 ++ [false]).take (d * r) = p0 := htake_p0
      have hget_last' : (p0 ++ [false]).get ⟨d * r, by omega⟩ = false := by
        change (p0 ++ [false])[d * r]'(by omega) = false
        rw [List.getElem_append_right (by omega)]
        simp [hlen0]
      rw [htake_last, hget_last'] at hlast
      simp only [q, hlen0, lt_irrefl, ↓reduceDIte] at hlast
      have hz1 : z.1 = 0 := by
        rcases zmod2_eq_zero_or_one z.1 with h0 | h1
        · exact h0
        · rw [h1] at hlast; simp at hlast
      simp only [hz1, ↓reduceIte]
      have hpath0 : ∀ k : Fin (d * r), q (p0.take k.val) (0, z.2) = p0.get ⟨k.val, by omega⟩ := by
        intro k
        have hk := hpath ⟨k.val, by omega⟩
        have ht : (p0 ++ [false]).take k.val = p0.take k.val :=
          List.take_append_of_le_length (by omega)
        have hg : (p0 ++ [false]).get ⟨k.val, by omega⟩ = p0.get ⟨k.val, by omega⟩ := by
          simp [List.getElem_append_left (by omega : k.val < p0.length)]
        rw [ht, hg] at hk
        have hz_eq : z = (0, z.2) := Prod.ext hz1 rfl
        rwa [← hz_eq]
      exact hpath_rec0 p0 z.2 hlen0 hpath0
    · have hlen : (p0 ++ [true]).length = d * r + 1 := by simp [hlen0]
      have htake_p0 : (p0 ++ [true]).take (d * r) = p0 := by rw [← hlen0]; simp
      have hget_last : (p0 ++ [true]).getD (d * r) false = true := by
        rw [List.getD_eq_getElem _ _ (by omega)]
        simp [hlen0]
      have hout : out (p0 ++ [true]) = dec1 p0 := by
        simp only [out, hlen, Nat.add_eq_left, one_ne_zero, ↓reduceIte, hget_last, Bool.true_eq_false, htake_p0]
      rw [hout]
      have hlast := hpath ⟨d * r, by omega⟩
      have htake_last : (p0 ++ [true]).take (d * r) = p0 := htake_p0
      have hget_last' : (p0 ++ [true]).get ⟨d * r, by omega⟩ = true := by
        change (p0 ++ [true])[d * r]'(by omega) = true
        rw [List.getElem_append_right (by omega)]
        simp [hlen0]
      rw [htake_last, hget_last'] at hlast
      simp only [q, hlen0, lt_irrefl, ↓reduceDIte] at hlast
      have hz1 : z.1 = 1 := by
        rcases zmod2_eq_zero_or_one z.1 with h0 | h1
        · rw [h0] at hlast; simp at hlast
        · exact h1
      simp only [hz1, one_ne_zero, ↓reduceIte]
      let x : Fin r → F := fun j => a⁻¹ * z.2 j
      have hy : z.2 = fun j => a * x j := by ext j; simp [x, mul_inv_cancel_left₀ ha0]
      have hpath1 : ∀ k : Fin (d * r), q (p0.take k.val) (1, fun j => a * x j) = p0.get ⟨k.val, by omega⟩ := by
        intro k
        have hk := hpath ⟨k.val, by omega⟩
        have ht : (p0 ++ [true]).take k.val = p0.take k.val :=
          List.take_append_of_le_length (by omega)
        have hg : (p0 ++ [true]).get ⟨k.val, by omega⟩ = p0.get ⟨k.val, by omega⟩ := by
          simp [List.getElem_append_left (by omega : k.val < p0.length)]
        rw [ht, hg] at hk
        have hz_eq : z = (1, fun j => a * x j) := Prod.ext hz1 hy
        rwa [← hz_eq]
      have hx1 : x = dec1 p0 := hpath_rec1 p0 x hlen0 hpath1
      rw [hy, hx1]
  have hleaves_eq : N \ J = goodFull ∪ extLeaves := by
    ext p
    simp only [Finset.mem_sdiff, hmem_N, hmem_J, Finset.mem_union, goodFull, extLeaves,
      Finset.mem_filter, Finset.mem_image, badFull]
    constructor
    · rintro ⟨hN, hnotJ⟩
      push_neg at hnotJ
      rcases hN with hle | ⟨p0, hlen0, hne0, rfl | rfl⟩
      · have hlen : p.length = d * r := by omega
        left
        exact ⟨hallFull_mem p hlen, hnotJ.2 hlen⟩
      · exact Or.inr (Or.inl ⟨p0, ⟨hallFull_mem p0 hlen0, hne0⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨p0, ⟨hallFull_mem p0 hlen0, hne0⟩, rfl⟩)
    · rintro (⟨hp, heq⟩ | (⟨p0, ⟨hp0, hne0⟩, rfl⟩ | ⟨p0, ⟨hp0, hne0⟩, rfl⟩))
      · have hlen := hallFull_len p hp
        refine ⟨Or.inl (le_of_eq hlen), ?_⟩
        rintro (hlt | ⟨_, hne⟩)
        · omega
        · exact hne heq
      · have hlen := hallFull_len p0 hp0
        refine ⟨Or.inr ⟨p0, hlen, hne0, Or.inl rfl⟩, ?_⟩
        rintro (hlt | ⟨heq, _⟩) <;> simp [hlen] at *
      · have hlen := hallFull_len p0 hp0
        refine ⟨Or.inr ⟨p0, hlen, hne0, Or.inr rfl⟩, ?_⟩
        rintro (hlt | ⟨heq, _⟩) <;> simp [hlen] at *
  have hdisj_ge : Disjoint goodFull extLeaves := by
    rw [Finset.disjoint_left]
    intro p hpg hpe
    have hlen1 := hallFull_len p (Finset.mem_filter.mp hpg).1
    rcases Finset.mem_union.mp hpe with h1 | h1
    · rcases Finset.mem_image.mp h1 with ⟨p0, hp0, rfl⟩
      have hlen0 := hallFull_len p0 (Finset.mem_filter.mp hp0).1
      simp [hlen0] at hlen1
    · rcases Finset.mem_image.mp h1 with ⟨p0, hp0, rfl⟩
      have hlen0 := hallFull_len p0 (Finset.mem_filter.mp hp0).1
      simp [hlen0] at hlen1
  have hdisj_ft : Disjoint (badFull.image (fun p => p ++ [false])) (badFull.image (fun p => p ++ [true])) := by
    rw [Finset.disjoint_left]
    intro p hf ht
    rcases Finset.mem_image.mp hf with ⟨p1, _, rfl⟩
    rcases Finset.mem_image.mp ht with ⟨p2, _, h⟩
    have h1 := List.append_inj_right' h rfl
    exact Bool.noConfusion (List.cons.inj h1).1
  have hext_card : extLeaves.card = 2 * badFull.card := by
    rw [Finset.card_union_of_disjoint hdisj_ft,
      Finset.card_image_of_injective _ (fun p₁ p₂ h => List.append_inj_left' h rfl),
      Finset.card_image_of_injective _ (fun p₁ p₂ h => List.append_inj_left' h rfl)]
    ring
  have hall_card : allFull.card = 2 ^ (d * r) := by
    rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hgood_bad : goodFull.card + badFull.card = 2 ^ (d * r) := by
    rw [← hall_card]
    exact Finset.card_filter_add_card_filter_not _
  have hgood_card : goodFull.card = 2 ^ ((d - 1) * r) := by
    let K0 : Finset F := Finset.univ.filter (fun y : F => φ ((a + 1) * y) = 0)
    have hK0_card : K0.card = 2 ^ (d - 1) := by
      rcases form_surjective φ hφ 1 with ⟨w0, hw0⟩
      let s0 : F := (a + 1)⁻¹ * w0
      have hs0 : φ ((a + 1) * s0) = 1 := by
        simp only [s0, ← mul_assoc, mul_inv_cancel₀ ha1', one_mul, hw0]
      let τ : F → F := fun y => y + s0
      have hτ_inv : ∀ y, τ (τ y) = y := fun y => by
        simp only [τ, add_assoc, add_self_eq_zero, add_zero]
      have hτ_inj : Function.Injective τ := Function.LeftInverse.injective hτ_inv
      have hK1 : K0.image τ = Finset.univ.filter (fun y : F => φ ((a + 1) * y) ≠ 0) := by
        ext y
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, K0]
        constructor
        · rintro ⟨x, hx, rfl⟩
          simp only [τ, mul_add, map_add, hx, zero_add, hs0]
          exact one_ne_zero
        · intro hy
          refine ⟨y + s0, ?_, by simp only [τ, add_assoc, add_self_eq_zero, add_zero]⟩
          have hy1 : φ ((a + 1) * y) = 1 := by
            rcases zmod2_eq_zero_or_one (φ ((a + 1) * y)) with h0 | h1
            · exact (hy h0).elim
            · exact h1
          simp only [mul_add, map_add, hy1, hs0, zmod2_add_self]
      have htot := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset F))
        (p := fun y : F => φ ((a + 1) * y) = 0)
      change K0.card + (Finset.univ.filter (fun y : F => φ ((a + 1) * y) ≠ 0)).card = (Finset.univ : Finset F).card at htot
      rw [← hK1, Finset.card_image_of_injective _ hτ_inj, Finset.card_univ, hcard] at htot
      have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
        have hd1 : d = (d - 1) + 1 := by omega
        conv_lhs => rw [hd1, pow_succ']
      omega
    let mkFull : (Fin r → F) → List Bool := fun x =>
      List.ofFn (fun k : Fin (d * r) =>
        decide (e0 (x ⟨k.val / d, Nat.div_lt_of_lt_mul k.isLt⟩)
          ⟨k.val % d, Nat.mod_lt _ (by omega)⟩ = 1))
    have hdec0_mk : ∀ x : Fin r → F, dec0 (mkFull x) = x := by
      intro x
      ext j
      apply e0.injective
      simp only [dec0, Equiv.apply_symm_apply]
      ext i
      let idx : ℕ := j.val * d + i.val
      have hidx_lt : idx < d * r := idx_lt j i.val i.isLt
      have hdiv : idx / d = j.val := idx_div (by omega) j.val i.val i.isLt
      have hmod : idx % d = i.val := idx_mod j.val i.val i.isLt
      have hget : (mkFull x).getD idx false =
          decide (e0 (x j) i = 1) := by
        rw [List.getD_eq_getElem _ _ (by simp [mkFull, hidx_lt])]
        simp only [mkFull, List.getElem_ofFn, hdiv, hmod, Fin.eta]
      rw [hget, hb2z_dec]
    have hmk_inj : Function.Injective mkFull := Function.LeftInverse.injective hdec0_mk
    have hgood_eq : goodFull =
        ((Finset.univ : Finset (Fin r → F)).filter (fun x => ∀ j : Fin r, x j ∈ K0)).image mkFull := by
      ext p
      simp only [goodFull, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, K0]
      constructor
      · rintro ⟨hp, heq⟩
        refine ⟨dec0 p, ?_, ?_⟩
        · intro j
          have h1 : enc1 (dec0 p j) = enc0 (dec0 p j) := by
            have h2 := congrFun heq j
            have h3 : e1 (dec0 p j) = e0 (dec0 p j) := by
              conv_lhs => rw [h2]
              simp only [dec1, dec0, Equiv.apply_symm_apply]
            exact h3
          have h0 := congrFun h1 ⟨0, by omega⟩
          simp only [enc1, enc0] at h0
          have h2 := congrArg (fun z => z + φ (b ^ 0 * dec0 p j)) h0
          have hL : φ (b ^ 0 * dec0 p j) + φ ((a + 1) * dec0 p j) + φ (b ^ 0 * dec0 p j) =
              φ ((a + 1) * dec0 p j) := by
            rw [add_comm (φ (b ^ 0 * dec0 p j)), add_assoc, zmod2_add_self, add_zero]
          have hR : φ (b ^ 0 * dec0 p j) + φ (b ^ 0 * dec0 p j) = 0 := zmod2_add_self _
          rwa [hL, hR] at h2
        · have hlen := hallFull_len p hp
          apply List.ext_get (by simp [mkFull, hlen])
          intro idx h1 h2
          simp only [mkFull, List.get_ofFn, dec0, Equiv.apply_symm_apply, Fin.val_cast]
          have hidx_eq : idx / d * d + idx % d = idx := by
            have := Nat.div_add_mod idx d
            linarith
          rw [hidx_eq, List.getD_eq_getElem _ _ (by omega)]
          change decide (b2z p[idx] = 1) = p[idx]
          cases p[idx] <;> simp [b2z]
      · rintro ⟨x, hx, rfl⟩
        refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [hdec0_mk]
        ext j
        apply e1.injective
        simp only [dec1, Equiv.apply_symm_apply]
        ext i
        have h1 : enc1 (x j) i = enc0 (x j) i := by
          simp only [enc1, enc0, hx j, add_zero]
        change enc1 (x j) i = _
        rw [h1]
        have h2 : dec0 (mkFull x) j = x j := congrFun (hdec0_mk x) j
        have h3 := congrFun (congrArg e0 h2) i
        simp only [dec0, Equiv.apply_symm_apply] at h3
        exact h3.symm
    rw [hgood_eq, Finset.card_image_of_injective _ hmk_inj]
    have hfilt_card : ((Finset.univ : Finset (Fin r → F)).filter (fun x => ∀ j : Fin r, x j ∈ K0)).card =
        K0.card ^ r := by
      have heq : (Finset.univ : Finset (Fin r → F)).filter (fun x => ∀ j : Fin r, x j ∈ K0) =
          Fintype.piFinset (fun _ : Fin r => K0) := by
        ext x
        simp [Fintype.mem_piFinset]
      rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hfilt_card, hK0_card, ← pow_mul]
  have hleaves_card : (N \ J).card + 2 ^ ((d - 1) * r) = 2 ^ (d * r + 1) := by
    rw [hleaves_eq, Finset.card_union_of_disjoint hdisj_ge, hext_card]
    have hpow : 2 ^ (d * r + 1) = 2 * 2 ^ (d * r) := by rw [pow_succ']
    omega
  exact ⟨N, J, q, out, hshape, fun p _ => hq_valid p, hleaf_ok, hleaves_card⟩

end PEqualNP.Outside.L_pcx_371_aux

theorem PEqualNP.Outside.L_pcx_371 :
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
      (d r : ℕ), 2 ≤ d → Fintype.card F = 2^d →
    ∀ a : F, Algebra.adjoin (ZMod 2) ({a} : Set F) = ⊤ →
      let X := Fin r → F
      ∀ K : ℕ,
        (∃ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × X) → Bool)
           (out : List Bool → X), cert (queries (ZMod 2 × X))
             (fun z x => if z.1 = 0 then z.2 = x else z.2 = fun j => a*x j) N J q out ∧
           (N \ J).card ≤ K) ↔ 2^(d*r+1) ≤ K + 2^((d-1)*r) := by
  intro shape queries cert F _ _ _ d r hd hcard a hadj X K
  constructor
  · rintro ⟨N, J, q, out, ⟨hshape, hq, hleaf⟩, hK⟩
    have hlb := PEqualNP.Outside.L_pcx_371_aux.lower_bound_dir d r hd hcard a hadj N J q out hshape hq hleaf
    omega
  · intro hK
    rcases PEqualNP.Outside.L_pcx_371_aux.upper_bound_dir d r hd hcard a hadj with
      ⟨N, J, q, out, hshape, hq, hleaf, hcard_eq⟩
    exact ⟨N, J, q, out, ⟨hshape, hq, hleaf⟩, by omega⟩
