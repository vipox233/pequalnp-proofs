import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_460_aux

open Classical

noncomputable section

abbrev F2 := ZMod 2
abbrev Vec (m : ℕ) := Fin m → F2
abbrev Space (m : ℕ) := Vec m × Vec m

def targetF {m : ℕ} (x : Space m) : F2 :=
  ∑ k : Fin m, x.1 k * x.2 k

def signQ (z : F2) : ℚ :=
  if z = 0 then 1 else -1

def sympB {m : ℕ} (u v : Space m) : F2 :=
  ∑ k : Fin m, (u.1 k * v.2 k + u.2 k * v.1 k)

lemma f2_cases (z : F2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (z : F2) : z + z = 0 := by
  fin_cases z <;> rfl

lemma f2_neg_eq (z : F2) : -z = z :=
  neg_eq_iff_add_eq_zero.mpr (f2_add_self z)

lemma signQ_zero : signQ 0 = 1 := by
  simp [signQ]

lemma signQ_one : signQ 1 = -1 := by
  simp [signQ]

lemma signQ_add (a b : F2) : signQ (a + b) = signQ a * signQ b := by
  rcases f2_cases a with rfl | rfl <;> rcases f2_cases b with rfl | rfl
  · norm_num [signQ]
  · norm_num [signQ]
  · norm_num [signQ]
  · rw [f2_add_self]; norm_num [signQ]

lemma signQ_sq (z : F2) : signQ z * signQ z = 1 := by
  rcases f2_cases z with rfl | rfl <;> norm_num [signQ]

lemma abs_signQ (z : F2) : |signQ z| = 1 := by
  rcases f2_cases z with rfl | rfl <;> norm_num [signQ]

lemma signQ_sum_finset {ι : Type*} (s : Finset ι) (f : ι → F2) :
    signQ (∑ i ∈ s, f i) = ∏ i ∈ s, signQ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [signQ_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, signQ_add, ih]

lemma targetF_add {m : ℕ} (u v : Space m) :
    targetF (u + v) = targetF u + targetF v + sympB u v := by
  simp only [targetF, sympB, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sympB_symm {m : ℕ} (u v : Space m) : sympB u v = sympB v u := by
  simp only [sympB]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sympB_self {m : ℕ} (u : Space m) : sympB u u = 0 := by
  simp only [sympB]
  apply Finset.sum_eq_zero
  intro k _
  have : u.1 k * u.2 k + u.2 k * u.1 k = u.1 k * u.2 k + u.1 k * u.2 k := by ring
  rw [this, f2_add_self]

lemma sympB_add_left {m : ℕ} (u₁ u₂ v : Space m) :
    sympB (u₁ + u₂) v = sympB u₁ v + sympB u₂ v := by
  simp only [sympB, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sympB_add_right {m : ℕ} (u v₁ v₂ : Space m) :
    sympB u (v₁ + v₂) = sympB u v₁ + sympB u v₂ := by
  rw [sympB_symm, sympB_add_left, sympB_symm v₁, sympB_symm v₂]

lemma sympB_smul_left {m : ℕ} (c : F2) (u v : Space m) :
    sympB (c • u) v = c * sympB u v := by
  simp only [sympB, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sympB_smul_right {m : ℕ} (c : F2) (u v : Space m) :
    sympB u (c • v) = c * sympB u v := by
  rw [sympB_symm, sympB_smul_left, sympB_symm]

def sympBlin (m : ℕ) : Space m →ₗ[F2] (Space m →ₗ[F2] F2) where
  toFun u :=
    { toFun := fun v => sympB u v
      map_add' := fun v₁ v₂ => sympB_add_right u v₁ v₂
      map_smul' := fun c v => by simp [sympB_smul_right] }
  map_add' u₁ u₂ := by apply LinearMap.ext; intro v; exact sympB_add_left u₁ u₂ v
  map_smul' c u := by apply LinearMap.ext; intro v; simp [sympB_smul_left]

lemma sympB_nondeg {m : ℕ} (u : Space m) (h : ∀ v : Space m, sympB u v = 0) : u = 0 := by
  apply Prod.ext
  · ext k
    let e : Vec m := fun i => if i = k then 1 else 0
    have h1 := h (0, e)
    simp only [sympB, e, Pi.zero_apply, mul_ite, mul_one, mul_zero, add_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h1
    exact h1
  · ext k
    let e : Vec m := fun i => if i = k then 1 else 0
    have h1 := h (e, 0)
    simp only [sympB, e, Pi.zero_apply, mul_ite, mul_one, mul_zero, zero_add, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at h1
    exact h1

lemma sympBlin_injective (m : ℕ) : Function.Injective (sympBlin m) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  apply sympB_nondeg u
  intro v
  exact congrFun (congrArg DFunLike.coe hu) v

lemma finrank_space (m : ℕ) : Module.finrank F2 (Space m) = 2 * m := by
  rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
  omega

lemma card_space (m : ℕ) : Fintype.card (Space m) = 2 ^ (2 * m) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card, ← pow_add]
  congr 1; omega

lemma natCard_space (m : ℕ) : Nat.card (Space m) = 2 ^ (2 * m) := by
  rw [Nat.card_eq_fintype_card, card_space]

lemma card_submodule {m : ℕ} (L : Submodule F2 (Space m)) :
    Fintype.card L = 2 ^ Module.finrank F2 L := by
  let b := Module.finBasis F2 L
  have hcard : Fintype.card L = Fintype.card (Fin (Module.finrank F2 L) → F2) :=
    Fintype.card_congr b.equivFun.toEquiv
  rw [hcard, Fintype.card_fun, Fintype.card_fin, ZMod.card]

lemma sympBlin_bijective (m : ℕ) : Function.Bijective (sympBlin m) := by
  refine ⟨sympBlin_injective m, ?_⟩
  have hfin : Module.finrank F2 (Space m) = Module.finrank F2 (Space m →ₗ[F2] F2) := by
    rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp (sympBlin_injective m)

def restrictB {m : ℕ} (L : Submodule F2 (Space m)) : Space m →ₗ[F2] (L →ₗ[F2] F2) where
  toFun u := (sympBlin m u).comp L.subtype
  map_add' u₁ u₂ := by ext v; simp [sympBlin, sympB_add_left]
  map_smul' c u := by ext v; simp [sympBlin, sympB_smul_left]

lemma restrictB_surjective {m : ℕ} (L : Submodule F2 (Space m)) :
    Function.Surjective (restrictB L) := by
  intro ℓ
  rcases Submodule.exists_isCompl L with ⟨L', hcompl⟩
  let P : Space m →ₗ[F2] L := L.projectionOnto L' hcompl
  let ℓ' : Space m →ₗ[F2] F2 := ℓ.comp P
  rcases (sympBlin_bijective m).2 ℓ' with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  ext ⟨v, hv⟩
  change sympB u v = ℓ ⟨v, hv⟩
  have h1 : sympB u v = ℓ' v := congrFun (congrArg DFunLike.coe hu) v
  rw [h1]
  change ℓ (L.projectionOnto L' hcompl (⟨v, hv⟩ : L).val) = ℓ ⟨v, hv⟩
  rw [Submodule.projectionOnto_apply_left]

lemma finrank_ker_restrictB {m : ℕ} (L : Submodule F2 (Space m)) :
    Module.finrank F2 L + Module.finrank F2 (LinearMap.ker (restrictB L)) = 2 * m := by
  have h := LinearMap.finrank_range_add_finrank_ker (restrictB L)
  rw [LinearMap.range_eq_top.mpr (restrictB_surjective L), finrank_top,
      Module.finrank_linearMap, Module.finrank_self, mul_one, finrank_space] at h
  exact h

def radB {m : ℕ} (K : Submodule F2 (Space m)) : Submodule F2 (Space m) :=
  K ⊓ LinearMap.ker (restrictB K)

lemma mem_radB {m : ℕ} {K : Submodule F2 (Space m)} {u : Space m} :
    u ∈ radB K ↔ u ∈ K ∧ ∀ v ∈ K, sympB u v = 0 := by
  simp only [radB, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨hu, hker⟩
    refine ⟨hu, fun v hv => ?_⟩
    exact congrFun (congrArg DFunLike.coe hker) ⟨v, hv⟩
  · rintro ⟨hu, hall⟩
    refine ⟨hu, ?_⟩
    ext ⟨v, hv⟩
    exact hall v hv

lemma even_finrank_sub_rad {m : ℕ} :
    ∀ (d : ℕ) (K : Submodule F2 (Space m)), Module.finrank F2 K = d →
      Even (Module.finrank F2 K - Module.finrank F2 (radB K)) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro K hdim
    by_cases hall : ∀ u ∈ K, ∀ v ∈ K, sympB u v = 0
    · have heq : radB K = K := by
        apply le_antisymm inf_le_left
        intro u hu
        exact mem_radB.mpr ⟨hu, hall u hu⟩
      rw [heq, Nat.sub_self]
      exact ⟨0, rfl⟩
    · push Not at hall
      rcases hall with ⟨u, huK, v, hvK, huv_ne⟩
      have huv : sympB u v = 1 := by
        rcases f2_cases (sympB u v) with h0 | h1
        · exact absurd h0 huv_ne
        · exact h1
      have hvu : sympB v u = 1 := by rw [sympB_symm, huv]
      let K₁ : Submodule F2 (Space m) :=
        { carrier := {w | w ∈ K ∧ sympB u w = 0 ∧ sympB v w = 0}, add_mem' := fun {a b} ha hb => ⟨K.add_mem ha.1 hb.1,
            by rw [sympB_add_right, ha.2.1, hb.2.1, add_zero],
            by rw [sympB_add_right, ha.2.2, hb.2.2, add_zero]⟩
          zero_mem' := ⟨K.zero_mem, by simp [sympB], by simp [sympB]⟩
          smul_mem' := fun c {a} ha => ⟨K.smul_mem c ha.1,
            by rw [sympB_smul_right, ha.2.1, mul_zero],
            by rw [sympB_smul_right, ha.2.2, mul_zero]⟩ }
      let P2 : Submodule F2 (Space m) := Submodule.span F2 ({u, v} : Set (Space m))
      have hP2_le : P2 ≤ K := by
        rw [Submodule.span_le]
        rintro w (rfl | rfl) <;> assumption
      have hK1_le : K₁ ≤ K := fun w hw => hw.1
      have hdisj : P2 ⊓ K₁ = ⊥ := by
        rw [eq_bot_iff]
        intro w ⟨hwP, hw1⟩
        rw [Submodule.mem_bot]
        have hw_span : w ∈ Submodule.span F2 ({u, v} : Set (Space m)) := hwP
        rw [Submodule.mem_span_pair] at hw_span
        rcases hw_span with ⟨c₁, c₂, rfl⟩
        have h1 : sympB u (c₁ • u + c₂ • v) = 0 := hw1.2.1
        have h2 : sympB v (c₁ • u + c₂ • v) = 0 := hw1.2.2
        rw [sympB_add_right, sympB_smul_right, sympB_smul_right, sympB_self, huv, mul_zero, zero_add, mul_one] at h1
        rw [sympB_add_right, sympB_smul_right, sympB_smul_right, sympB_self, hvu, mul_zero, add_zero, mul_one] at h2
        simp [h1, h2]
      have hsup : P2 ⊔ K₁ = K := by
        apply le_antisymm (sup_le hP2_le hK1_le)
        intro w hwK
        let w₁ := w + sympB v w • u + sympB u w • v
        have hw1_mem : w₁ ∈ K₁ := by
          refine ⟨K.add_mem (K.add_mem hwK (K.smul_mem _ huK)) (K.smul_mem _ hvK), ?_, ?_⟩
          · rw [sympB_add_right, sympB_add_right, sympB_smul_right, sympB_smul_right,
                sympB_self, huv, mul_zero, add_zero, mul_one, f2_add_self]
          · rw [sympB_add_right, sympB_add_right, sympB_smul_right, sympB_smul_right,
                sympB_self, hvu, mul_zero, add_zero, mul_one, f2_add_self]
        have hp_mem : sympB v w • u + sympB u w • v ∈ P2 := by
          rw [Submodule.mem_span_pair]
          exact ⟨sympB v w, sympB u w, rfl⟩
        have hw_eq : w = (sympB v w • u + sympB u w • v) + w₁ := by
          simp only [w₁]
          ext k
          · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have h1 := f2_add_self (sympB v w * u.1 k + sympB u w * v.1 k)
            linear_combination -h1
          · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            have h1 := f2_add_self (sympB v w * u.2 k + sympB u w * v.2 k)
            linear_combination -h1
        rw [hw_eq]
        exact Submodule.add_mem_sup hp_mem hw1_mem
      have hP2_dim : Module.finrank F2 P2 = 2 := by
        have hli : LinearIndependent F2 ![u, v] := by
          rw [Fintype.linearIndependent_iff]
          intro c hc
          have hsum : c 0 • u + c 1 • v = 0 := by
            simpa [Fin.sum_univ_two] using hc
          have h1 := congrArg (sympB u) hsum
          have h2 := congrArg (sympB v) hsum
          have hz1 : sympB u 0 = 0 := by simp [sympB]
          have hz2 : sympB v 0 = 0 := by simp [sympB]
          rw [sympB_add_right, sympB_smul_right, sympB_smul_right, sympB_self, huv, mul_zero, zero_add, mul_one, hz1] at h1
          rw [sympB_add_right, sympB_smul_right, sympB_smul_right, sympB_self, hvu, mul_zero, add_zero, mul_one, hz2] at h2
          intro i; fin_cases i
          · exact h2
          · exact h1
        have hrange : Set.range ![u, v] = ({u, v} : Set (Space m)) := by
          ext w; simp; tauto
        have hspan := finrank_span_eq_card hli
        rw [hrange, Fintype.card_fin] at hspan
        exact hspan
      have hdim_sum : Module.finrank F2 K = 2 + Module.finrank F2 K₁ := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq P2 K₁
        rw [hsup, hdisj, finrank_bot, add_zero, hP2_dim] at h
        exact h
      have hrad_eq : radB K₁ = radB K := by
        apply le_antisymm
        · intro w hw
          rw [mem_radB] at hw ⊢
          refine ⟨hw.1.1, fun z hz => ?_⟩
          have hz_sup : z ∈ P2 ⊔ K₁ := hsup.symm ▸ hz
          rcases Submodule.mem_sup.mp hz_sup with ⟨p, hp, z₁, hz₁, rfl⟩
          rw [Submodule.mem_span_pair] at hp
          rcases hp with ⟨c₁, c₂, rfl⟩
          rw [sympB_add_right, sympB_add_right, sympB_smul_right, sympB_smul_right,
              sympB_symm w u, hw.1.2.1, sympB_symm w v, hw.1.2.2, hw.2 z₁ hz₁]
          simp
        · intro w hw
          rw [mem_radB] at hw ⊢
          refine ⟨⟨hw.1, by rw [sympB_symm]; exact hw.2 u huK, by rw [sympB_symm]; exact hw.2 v hvK⟩,
            fun z hz => hw.2 z hz.1⟩
      have hih := ih (Module.finrank F2 K₁) (by omega) K₁ rfl
      rw [hrad_eq] at hih
      have hle_rad : Module.finrank F2 (radB K) ≤ Module.finrank F2 K₁ := by
        rw [← hrad_eq]
        exact Submodule.finrank_mono inf_le_left
      rcases hih with ⟨t, ht⟩
      refine ⟨t + 1, ?_⟩
      omega

lemma sum_sign_linear {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
    (ℓ : V →ₗ[F2] F2) :
    (∑ u : V, signQ (ℓ u)) = if ℓ = 0 then (Fintype.card V : ℚ) else 0 := by
  by_cases h0 : ℓ = 0
  · subst h0
    simp [signQ_zero]
  · simp only [h0, ↓reduceIte]
    have hex : ∃ v : V, ℓ v = 1 := by
      by_contra hall
      push Not at hall
      apply h0
      ext v
      rcases f2_cases (ℓ v) with h | h
      · exact h
      · exact absurd h (hall v)
    rcases hex with ⟨v, hv⟩
    have hshift : (∑ u : V, signQ (ℓ u)) = -(∑ u : V, signQ (ℓ u)) := by
      calc (∑ u : V, signQ (ℓ u))
          = ∑ u : V, signQ (ℓ (u + v)) :=
              (Fintype.sum_equiv (Equiv.addRight v) (fun u => signQ (ℓ (u + v))) (fun u => signQ (ℓ u)) (fun _ => rfl)).symm
        _ = ∑ u : V, (-signQ (ℓ u)) := by
              apply Finset.sum_congr rfl
              intro u _
              rw [map_add, hv, signQ_add, signQ_one]; ring
        _ = -(∑ u : V, signQ (ℓ u)) := by rw [Finset.sum_neg_distrib]
    linarith

lemma sum_sign_target (m : ℕ) :
    (∑ x : Space m, signQ (targetF x)) = (2 : ℚ) ^ m := by
  have h1 : ∀ x : Space m, signQ (targetF x) = ∏ k : Fin m, signQ (x.1 k * x.2 k) := fun x =>
    signQ_sum_finset Finset.univ (fun k => x.1 k * x.2 k)
  simp_rw [h1]
  let e : Space m ≃ (Fin m → F2 × F2) :=
    { toFun := fun x k => (x.1 k, x.2 k)
      invFun := fun f => (fun k => (f k).1, fun k => (f k).2)
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun _ => rfl }
  calc (∑ x : Space m, ∏ k : Fin m, signQ (x.1 k * x.2 k))
      = ∑ f : Fin m → F2 × F2, ∏ k : Fin m, signQ ((f k).1 * (f k).2) :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = ∏ k : Fin m, ∑ p : F2 × F2, signQ (p.1 * p.2) :=
          (Fintype.prod_sum (fun _ (p : F2 × F2) => signQ (p.1 * p.2))).symm
    _ = ∏ _ : Fin m, (2 : ℚ) := by
          apply Finset.prod_congr rfl
          intro _ _
          have hpair : (∑ p : F2 × F2, signQ (p.1 * p.2)) =
              ∑ a : F2, ∑ b : F2, signQ (a * b) := Fintype.sum_prod_type _
          have huniv : (Finset.univ : Finset F2) = {0, 1} := by
            ext z; rcases f2_cases z with rfl | rfl <;> simp
          rw [hpair, huniv]
          simp [signQ]
          norm_num
    _ = (2 : ℚ) ^ m := by simp

def cosetSum {m : ℕ} (K : Submodule F2 (Space m)) (a : Space m) : ℚ :=
  ∑ u : K, signQ (targetF (a + u.val))

lemma cosetSum_sq {m : ℕ} (K : Submodule F2 (Space m)) (a : Space m) :
    (cosetSum K a) ^ 2 = (Fintype.card K : ℚ) *
      ∑ w : radB K, signQ (targetF w.val + sympB a w.val) := by
  rw [sq, cosetSum, Finset.sum_mul]
  have hre : (∑ u : K, signQ (targetF (a + u.val)) * ∑ v : K, signQ (targetF (a + v.val))) =
      ∑ u : K, ∑ w : K, signQ (targetF w.val + sympB a w.val) * signQ (sympB u.val w.val) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.addLeft u)
      (fun w : K => signQ (targetF w.val + sympB a w.val) * signQ (sympB u.val w.val))
      (fun v : K => signQ (targetF (a + u.val)) * signQ (targetF (a + v.val)))
      (fun w => ?_)).symm
    symm
    change signQ (targetF (a + u.val)) * signQ (targetF (a + (u.val + w.val))) =
      signQ (targetF w.val + sympB a w.val) * signQ (sympB u.val w.val)
    rw [← signQ_add, ← signQ_add]
    congr 1
    have h1 : a + (u.val + w.val) = (a + u.val) + w.val := by abel
    rw [h1, targetF_add (a + u.val) w.val, sympB_add_left a u.val w.val]
    have h2 := f2_add_self (targetF (a + u.val))
    linear_combination h2
  rw [hre, Finset.sum_comm]
  have hinner : ∀ w : K, (∑ u : K, signQ (targetF w.val + sympB a w.val) * signQ (sympB u.val w.val)) =
      if w.val ∈ radB K then (Fintype.card K : ℚ) * signQ (targetF w.val + sympB a w.val) else 0 := by
    intro w
    rw [← Finset.mul_sum]
    let ℓ : K →ₗ[F2] F2 :=
      { toFun := fun u => sympB u.val w.val
        map_add' := fun u₁ u₂ => sympB_add_left u₁.val u₂.val w.val
        map_smul' := fun c u => by simp [sympB_smul_left] }
    have hlin := sum_sign_linear ℓ
    change signQ (targetF w.val + sympB a w.val) * (∑ u : K, signQ (ℓ u)) = _
    rw [hlin]
    have hiff : ℓ = 0 ↔ w.val ∈ radB K := by
      rw [mem_radB]
      constructor
      · intro h0
        refine ⟨w.property, fun z hz => ?_⟩
        rw [sympB_symm]
        exact congrFun (congrArg DFunLike.coe h0) ⟨z, hz⟩
      · rintro ⟨_, hall⟩
        ext ⟨z, hz⟩
        change sympB z w.val = 0
        rw [sympB_symm]
        exact hall z hz
    by_cases hw : w.val ∈ radB K
    · rw [if_pos (hiff.mpr hw), if_pos hw]; ring
    · rw [if_neg (fun h => hw (hiff.mp h)), if_neg hw, mul_zero]
  simp_rw [hinner]
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  congr 1
  refine Finset.sum_bij (fun (w : K) (hw : w ∈ Finset.univ.filter (fun w : K => w.val ∈ radB K)) =>
      (⟨w.val, (Finset.mem_filter.mp hw).2⟩ : radB K))
    (fun _ _ => Finset.mem_univ _)
    (fun w₁ _ w₂ _ h => Subtype.ext (congrArg (Subtype.val : radB K → Space m) h))
    (fun w _ => ⟨⟨w.val, (mem_radB.mp w.property).1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.property⟩, rfl⟩)
    (fun _ _ => rfl)

def targetOnRad {m : ℕ} (K : Submodule F2 (Space m)) : radB K →ₗ[F2] F2 where
  toFun w := targetF w.val
  map_add' w₁ w₂ := by
    change targetF (w₁.val + w₂.val) = targetF w₁.val + targetF w₂.val
    rw [targetF_add]
    have h0 : sympB w₁.val w₂.val = 0 :=
      (mem_radB.mp w₁.property).2 w₂.val (mem_radB.mp w₂.property).1
    rw [h0, add_zero]
  map_smul' c w := by
    rcases f2_cases c with rfl | rfl
    · simp [targetF, zero_smul]
    · simp [one_smul]

lemma cosetSum_sq_cases {m : ℕ} (K : Submodule F2 (Space m)) (a : Space m) :
    (cosetSum K a) ^ 2 =
      if restrictB (radB K) a = targetOnRad K then
        (Fintype.card K : ℚ) * (Fintype.card (radB K) : ℚ)
      else 0 := by
  rw [cosetSum_sq]
  let ℓ : radB K →ₗ[F2] F2 := targetOnRad K + restrictB (radB K) a
  have hsum : (∑ w : radB K, signQ (targetF w.val + sympB a w.val)) = ∑ w : radB K, signQ (ℓ w) := rfl
  rw [hsum, sum_sign_linear ℓ]
  have hiff : ℓ = 0 ↔ restrictB (radB K) a = targetOnRad K := by
    constructor
    · intro h0
      ext w
      have hw : targetOnRad K w + restrictB (radB K) a w = 0 := congrFun (congrArg DFunLike.coe h0) w
      have hadd := f2_add_self (targetOnRad K w)
      linear_combination hw - hadd
    · intro heq
      ext w
      change targetOnRad K w + restrictB (radB K) a w = 0
      rw [heq, f2_add_self]
  by_cases ha : restrictB (radB K) a = targetOnRad K
  · rw [if_pos (hiff.mpr ha), if_pos ha]
  · rw [if_neg (fun h => ha (hiff.mp h)), if_neg ha, mul_zero]

lemma card_fiber_restrictB {m : ℕ} (L : Submodule F2 (Space m)) (t : L →ₗ[F2] F2) :
    (Finset.univ.filter (fun a : Space m => restrictB L a = t)).card =
      2 ^ (2 * m - Module.finrank F2 L) := by
  rcases restrictB_surjective L t with ⟨a₀, ha₀⟩
  have hbij : (Finset.univ.filter (fun a : Space m => restrictB L a = t)).card =
      Fintype.card (LinearMap.ker (restrictB L)) := by
    rw [← Finset.card_univ]
    refine Finset.card_bij (fun a ha => (⟨a + a₀, by
        rw [LinearMap.mem_ker, map_add, ha₀, (Finset.mem_filter.mp ha).2]
        ext w; exact f2_add_self (t w)⟩ : LinearMap.ker (restrictB L)))
      (fun _ _ => Finset.mem_univ _)
      (fun a₁ _ a₂ _ h => by
        have h1 : a₁ + a₀ = a₂ + a₀ := congrArg Subtype.val h
        exact add_right_cancel h1)
      (fun u _ => ⟨u.val + a₀, by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [map_add, LinearMap.mem_ker.mp u.property, zero_add, ha₀], by
        apply Subtype.ext
        change (u.val + a₀) + a₀ = u.val
        rw [add_assoc]
        have : a₀ + a₀ = 0 := by
          apply Prod.ext <;> ext k <;> exact f2_add_self _
        rw [this, add_zero]⟩)
  rw [hbij, card_submodule]
  have hdim := finrank_ker_restrictB L
  congr 1; omega

lemma sum_cosetSum {m : ℕ} (K : Submodule F2 (Space m)) :
    (∑ a : Space m, cosetSum K a) = (Fintype.card K : ℚ) * (2 : ℚ) ^ m := by
  simp only [cosetSum]
  rw [Finset.sum_comm]
  have h1 : ∀ u : K, (∑ a : Space m, signQ (targetF (a + u.val))) = (2 : ℚ) ^ m := by
    intro u
    rw [← sum_sign_target m]
    exact Fintype.sum_equiv (Equiv.addRight u.val) _ _ (fun _ => rfl)
  simp [h1]

lemma exact_score_of_subspace (m j : ℕ) (hj : j ≤ 2 * m)
    (K : Submodule F2 (Space m)) (hdimK : Module.finrank F2 K = 2 * m - j) (shift : ℚ) :
    let dR := Module.finrank F2 (radB K)
    let r := (j - dR) / 2
    2 * r ≤ j ∧ j ≤ m + r ∧ dR = j - 2 * r ∧
    (∑ a : Space m, |cosetSum K a - (Fintype.card K : ℚ) * shift|) /
      ((Fintype.card K : ℚ) * (Nat.card (Space m) : ℚ)) =
    let base := (1 : ℚ) / 2 ^ m
    let amp := (1 : ℚ) / 2 ^ (m + r - j)
    let mass := (1 : ℚ) / 2 ^ (j - 2 * r)
    (1 - mass) * |shift| +
      (mass + base / amp) / 2 * |amp - shift| +
      (mass - base / amp) / 2 * |amp + shift| := by
  intro dR r
  have hdR_le_K : dR ≤ 2 * m - j := by
    rw [← hdimK]
    exact Submodule.finrank_mono inf_le_left
  have hdR_le_j : dR ≤ j := by
    have hle : radB K ≤ LinearMap.ker (restrictB K) := inf_le_right
    have h1 := Submodule.finrank_mono hle
    have h2 := finrank_ker_restrictB K
    omega
  have hev : Even (2 * m - j - dR) := by
    have h := even_finrank_sub_rad (2 * m - j) K hdimK
    rwa [hdimK] at h
  have hdR_eq : dR = j - 2 * r := by
    rcases hev with ⟨t, ht⟩
    omega
  have h2r : 2 * r ≤ j := by omega
  have hmr : j ≤ m + r := by omega
  refine ⟨h2r, hmr, hdR_eq, ?_⟩
  let base : ℚ := (1 : ℚ) / 2 ^ m
  let amp : ℚ := (1 : ℚ) / 2 ^ (m + r - j)
  let mass : ℚ := (1 : ℚ) / 2 ^ (j - 2 * r)
  let A : ℚ := (2 : ℚ) ^ (m - r)
  have hK_card : (Fintype.card K : ℚ) = (2 : ℚ) ^ (2 * m - j) := by
    rw [card_submodule, hdimK]; push_cast; rfl
  have hR_card : (Fintype.card (radB K) : ℚ) = (2 : ℚ) ^ dR := by
    rw [card_submodule]; push_cast; rfl
  have hX_card : (Nat.card (Space m) : ℚ) = (2 : ℚ) ^ (2 * m) := by
    rw [natCard_space]; push_cast; rfl
  have hA_eq : A = (Fintype.card K : ℚ) * amp := by
    simp only [A, amp, hK_card]
    have hexp : 2 * m - j = (m - r) + (m + r - j) := by omega
    rw [hexp, pow_add]
    have hne : (2 : ℚ) ^ (m + r - j) ≠ 0 := by positivity
    field_simp [hne]
  have hA_sq : A ^ 2 = (Fintype.card K : ℚ) * (Fintype.card (radB K) : ℚ) := by
    simp only [A, hK_card, hR_card, ← pow_mul, ← pow_add]
    congr 1; omega
  have hval : ∀ a : Space m,
      (restrictB (radB K) a = targetOnRad K → cosetSum K a = A ∨ cosetSum K a = -A) ∧
      (restrictB (radB K) a ≠ targetOnRad K → cosetSum K a = 0) := by
    intro a
    have hsq := cosetSum_sq_cases K a
    constructor
    · intro ha
      rw [if_pos ha, ← hA_sq] at hsq
      exact sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    · intro ha
      rw [if_neg ha] at hsq
      exact sq_eq_zero_iff.mp hsq
  let S_nz := Finset.univ.filter (fun a : Space m => restrictB (radB K) a = targetOnRad K)
  let S_pos := S_nz.filter (fun a : Space m => cosetSum K a = A)
  let S_neg := S_nz.filter (fun a : Space m => cosetSum K a = -A)
  let S_zero := Finset.univ.filter (fun a : Space m => restrictB (radB K) a ≠ targetOnRad K)
  have hA_pos : (0 : ℚ) < A := by positivity
  have hdisj_pn : Disjoint S_pos S_neg := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    have h1 := (Finset.mem_filter.mp ha1).2
    have h2 := (Finset.mem_filter.mp ha2).2
    linarith
  have hunion_pn : S_pos ∪ S_neg = S_nz := by
    ext a
    simp only [S_pos, S_neg, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases (hval a).1 (Finset.mem_filter.mp h).2 with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
  have hcard_nz : (S_nz.card : ℚ) = (2 : ℚ) ^ (2 * m - dR) := by
    rw [card_fiber_restrictB]; push_cast; rfl
  have hcard_pn : (S_pos.card : ℚ) + (S_neg.card : ℚ) = (2 : ℚ) ^ (2 * m - dR) := by
    have h1 : S_pos.card + S_neg.card = S_nz.card := by
      rw [← Finset.card_union_of_disjoint hdisj_pn, hunion_pn]
    have h2 : ((S_pos.card + S_neg.card : ℕ) : ℚ) = (S_nz.card : ℚ) := by exact_mod_cast h1
    push_cast at h2
    rw [h2, hcard_nz]
  have hcard_zero : (S_zero.card : ℚ) = (2 : ℚ) ^ (2 * m) - (2 : ℚ) ^ (2 * m - dR) := by
    have h1 : S_nz.card + S_zero.card = Fintype.card (Space m) := by
      have hdisj : Disjoint S_nz S_zero := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
      have hunion : S_nz ∪ S_zero = Finset.univ := by
        ext a; simp [S_nz, S_zero, Classical.em]
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    have h2 : ((S_nz.card + S_zero.card : ℕ) : ℚ) = (Fintype.card (Space m) : ℚ) := by exact_mod_cast h1
    push_cast at h2
    rw [hcard_nz, card_space] at h2
    push_cast at h2
    linarith
  have hsum_all : (∑ a : Space m, cosetSum K a) = ((S_pos.card : ℚ) - (S_neg.card : ℚ)) * A := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Space m => restrictB (radB K) a = targetOnRad K)]
    have h0 : (∑ a ∈ S_zero, cosetSum K a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      exact (hval a).2 (Finset.mem_filter.mp ha).2
    change (∑ a ∈ S_nz, cosetSum K a) + (∑ a ∈ S_zero, cosetSum K a) = _
    rw [h0, add_zero, ← hunion_pn, Finset.sum_union hdisj_pn]
    have hp : (∑ a ∈ S_pos, cosetSum K a) = (S_pos.card : ℚ) * A := by
      rw [Finset.sum_congr rfl (fun a ha => (Finset.mem_filter.mp ha).2), Finset.sum_const, nsmul_eq_mul]
    have hn : (∑ a ∈ S_neg, cosetSum K a) = (S_neg.card : ℚ) * (-A) := by
      rw [Finset.sum_congr rfl (fun a ha => (Finset.mem_filter.mp ha).2), Finset.sum_const, nsmul_eq_mul]
    rw [hp, hn]; ring
  have hdiff_pn : ((S_pos.card : ℚ) - (S_neg.card : ℚ)) * A = (Fintype.card K : ℚ) * (2 : ℚ) ^ m := by
    rw [← hsum_all, sum_cosetSum]
  have hsum_abs : (∑ a : Space m, |cosetSum K a - (Fintype.card K : ℚ) * shift|) =
      (S_zero.card : ℚ) * ((Fintype.card K : ℚ) * |shift|) +
      (S_pos.card : ℚ) * ((Fintype.card K : ℚ) * |amp - shift|) +
      (S_neg.card : ℚ) * ((Fintype.card K : ℚ) * |amp + shift|) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Space m => restrictB (radB K) a = targetOnRad K)]
    change (∑ a ∈ S_nz, |cosetSum K a - (Fintype.card K : ℚ) * shift|) +
      (∑ a ∈ S_zero, |cosetSum K a - (Fintype.card K : ℚ) * shift|) = _
    have hK_nn : (0 : ℚ) ≤ (Fintype.card K : ℚ) := Nat.cast_nonneg _
    have hz : (∑ a ∈ S_zero, |cosetSum K a - (Fintype.card K : ℚ) * shift|) =
        (S_zero.card : ℚ) * ((Fintype.card K : ℚ) * |shift|) := by
      have hcon : ∀ a ∈ S_zero, |cosetSum K a - (Fintype.card K : ℚ) * shift| = (Fintype.card K : ℚ) * |shift| := by
        intro a ha
        rw [(hval a).2 (Finset.mem_filter.mp ha).2, zero_sub, abs_neg, abs_mul, abs_of_nonneg hK_nn]
      rw [Finset.sum_congr rfl hcon, Finset.sum_const, nsmul_eq_mul]
    rw [hz, ← hunion_pn, Finset.sum_union hdisj_pn]
    have hp : (∑ a ∈ S_pos, |cosetSum K a - (Fintype.card K : ℚ) * shift|) =
        (S_pos.card : ℚ) * ((Fintype.card K : ℚ) * |amp - shift|) := by
      have hcon : ∀ a ∈ S_pos, |cosetSum K a - (Fintype.card K : ℚ) * shift| = (Fintype.card K : ℚ) * |amp - shift| := by
        intro a ha
        rw [(Finset.mem_filter.mp ha).2, hA_eq, ← mul_sub, abs_mul, abs_of_nonneg hK_nn]
      rw [Finset.sum_congr rfl hcon, Finset.sum_const, nsmul_eq_mul]
    have hn : (∑ a ∈ S_neg, |cosetSum K a - (Fintype.card K : ℚ) * shift|) =
        (S_neg.card : ℚ) * ((Fintype.card K : ℚ) * |amp + shift|) := by
      have hcon : ∀ a ∈ S_neg, |cosetSum K a - (Fintype.card K : ℚ) * shift| = (Fintype.card K : ℚ) * |amp + shift| := by
        intro a ha
        rw [(Finset.mem_filter.mp ha).2, hA_eq]
        have hneg : -((Fintype.card K : ℚ) * amp) - (Fintype.card K : ℚ) * shift =
            -((Fintype.card K : ℚ) * (amp + shift)) := by ring
        rw [hneg, abs_neg, abs_mul, abs_of_nonneg hK_nn]
      rw [Finset.sum_congr rfl hcon, Finset.sum_const, nsmul_eq_mul]
    rw [hp, hn]; ring
  rw [hsum_abs]
  have hK_ne : (Fintype.card K : ℚ) ≠ 0 := by rw [hK_card]; positivity
  have hX_ne : (Nat.card (Space m) : ℚ) ≠ 0 := by rw [hX_card]; positivity
  have hmass_eq : (2 : ℚ) ^ (2 * m - dR) / (2 : ℚ) ^ (2 * m) = mass := by
    simp only [mass, ← hdR_eq]
    have hexp : 2 * m = (2 * m - dR) + dR := by omega
    conv_lhs => rhs; rw [hexp, pow_add]
    have h1 : (2 : ℚ) ^ (2 * m - dR) ≠ 0 := by positivity
    have h2 : (2 : ℚ) ^ dR ≠ 0 := by positivity
    field_simp [h1, h2]
  have hratio_zero : (S_zero.card : ℚ) / (Nat.card (Space m) : ℚ) = 1 - mass := by
    rw [hcard_zero, hX_card, sub_div, div_self (by positivity), hmass_eq]
  have hratio_diff : ((S_pos.card : ℚ) - (S_neg.card : ℚ)) / (Nat.card (Space m) : ℚ) = base / amp := by
    have hamp_ne : amp ≠ 0 := by simp only [amp]; positivity
    have h1 : ((S_pos.card : ℚ) - (S_neg.card : ℚ)) * amp = (2 : ℚ) ^ m := by
      have h2 := hdiff_pn
      rw [hA_eq] at h2
      have h3 : (Fintype.card K : ℚ) * (((S_pos.card : ℚ) - (S_neg.card : ℚ)) * amp) =
          (Fintype.card K : ℚ) * (2 : ℚ) ^ m := by linarith
      exact mul_left_cancel₀ hK_ne h3
    have h2 : (2 : ℚ) ^ m / (2 : ℚ) ^ (2 * m) = base := by
      simp only [base]
      have hexp : 2 * m = m + m := by omega
      rw [hexp, pow_add]
      have hne : (2 : ℚ) ^ m ≠ 0 := by positivity
      field_simp [hne]
    rw [hX_card, ← h2]
    field_simp [hamp_ne]
    linarith
  have hratio_sum : ((S_pos.card : ℚ) + (S_neg.card : ℚ)) / (Nat.card (Space m) : ℚ) = mass := by
    rw [hcard_pn, hX_card, hmass_eq]
  have hratio_pos : (S_pos.card : ℚ) / (Nat.card (Space m) : ℚ) = (mass + base / amp) / 2 := by
    linarith [add_div (S_pos.card : ℚ) (S_neg.card : ℚ) (Nat.card (Space m) : ℚ),
              sub_div (S_pos.card : ℚ) (S_neg.card : ℚ) (Nat.card (Space m) : ℚ)]
  have hratio_neg : (S_neg.card : ℚ) / (Nat.card (Space m) : ℚ) = (mass - base / amp) / 2 := by
    linarith [add_div (S_pos.card : ℚ) (S_neg.card : ℚ) (Nat.card (Space m) : ℚ),
              sub_div (S_pos.card : ℚ) (S_neg.card : ℚ) (Nat.card (Space m) : ℚ)]
  have hsimp : ((S_zero.card : ℚ) * ((Fintype.card K : ℚ) * |shift|) +
      (S_pos.card : ℚ) * ((Fintype.card K : ℚ) * |amp - shift|) +
      (S_neg.card : ℚ) * ((Fintype.card K : ℚ) * |amp + shift|)) /
      ((Fintype.card K : ℚ) * (Nat.card (Space m) : ℚ)) =
      (S_zero.card : ℚ) / (Nat.card (Space m) : ℚ) * |shift| +
      (S_pos.card : ℚ) / (Nat.card (Space m) : ℚ) * |amp - shift| +
      (S_neg.card : ℚ) / (Nat.card (Space m) : ℚ) * |amp + shift| := by
    have hdiv : ∀ (a b c k x p q r : ℚ), k ≠ 0 → x ≠ 0 →
        (a * (k * p) + b * (k * q) + c * (k * r)) / (k * x) =
        a / x * p + b / x * q + c / x * r := by
      intro a b c k x p q r hk hx; field_simp [hk, hx]
    exact hdiv _ _ _ _ _ _ _ _ hK_ne hX_ne
  rw [hsimp, hratio_zero, hratio_pos, hratio_neg]

lemma cosetSum_add_mem {m : ℕ} (K : Submodule F2 (Space m)) (a : Space m) (v : K) :
    cosetSum K (a + v.val) = cosetSum K a := by
  simp only [cosetSum]
  refine Fintype.sum_equiv (Equiv.addLeft v) _ _ (fun u => ?_)
  change signQ (targetF ((a + v.val) + u.val)) = signQ (targetF (a + (v.val + u.val)))
  rw [add_assoc]

lemma query_score_bound {m j : ℕ} (query : Space m →ₗ[F2] (Fin j → F2))
    (out : (Fin j → F2) → F2) (shift : ℚ) :
    (∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift)) ≤
      (∑ a : Space m, |cosetSum (LinearMap.ker query) a -
        (Fintype.card (LinearMap.ker query) : ℚ) * shift|) /
      (Fintype.card (LinearMap.ker query) : ℚ) := by
  let K := LinearMap.ker query
  have hK_pos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    rw [card_submodule]; positivity
  rw [le_div_iff₀ hK_pos]
  have hfib : (Fintype.card K : ℚ) *
      (∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift)) =
      ∑ a : Space m, signQ (out (query a)) * (cosetSum K a - (Fintype.card K : ℚ) * shift) := by
    calc (Fintype.card K : ℚ) *
          (∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift))
        = ∑ u : K, ∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ u : K, ∑ a : Space m, signQ (out (query (a + u.val))) * (signQ (targetF (a + u.val)) - shift) := by
            apply Finset.sum_congr rfl
            intro u _
            exact (Fintype.sum_equiv (Equiv.addRight u.val) _ _ (fun _ => rfl)).symm
      _ = ∑ a : Space m, ∑ u : K, signQ (out (query a)) * (signQ (targetF (a + u.val)) - shift) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro u _
            rw [map_add, LinearMap.mem_ker.mp u.property, add_zero]
      _ = ∑ a : Space m, signQ (out (query a)) * (cosetSum K a - (Fintype.card K : ℚ) * shift) := by
            apply Finset.sum_congr rfl; intro a _
            rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rfl
  rw [mul_comm, hfib]
  apply Finset.sum_le_sum
  intro a _
  calc signQ (out (query a)) * (cosetSum K a - (Fintype.card K : ℚ) * shift)
      ≤ |signQ (out (query a)) * (cosetSum K a - (Fintype.card K : ℚ) * shift)| := le_abs_self _
    _ = |cosetSum K a - (Fintype.card K : ℚ) * shift| := by
        rw [abs_mul, abs_signQ, one_mul]

lemma query_score_achieve {m j : ℕ} (query : Space m →ₗ[F2] (Fin j → F2)) (shift : ℚ) :
    ∃ out : (Fin j → F2) → F2,
      (∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift)) =
        (∑ a : Space m, |cosetSum (LinearMap.ker query) a -
          (Fintype.card (LinearMap.ker query) : ℚ) * shift|) /
        (Fintype.card (LinearMap.ker query) : ℚ) := by
  let K := LinearMap.ker query
  let out : (Fin j → F2) → F2 := fun y =>
    if h : ∃ a : Space m, query a = y then
      if 0 ≤ cosetSum K (Classical.choose h) - (Fintype.card K : ℚ) * shift then 0 else 1
    else 0
  refine ⟨out, ?_⟩
  have hK_pos : (0 : ℚ) < (Fintype.card K : ℚ) := by
    rw [card_submodule]; positivity
  rw [eq_div_iff (ne_of_gt hK_pos)]
  have hfib : (Fintype.card K : ℚ) *
      (∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift)) =
      ∑ a : Space m, signQ (out (query a)) * (cosetSum K a - (Fintype.card K : ℚ) * shift) := by
    calc (Fintype.card K : ℚ) *
          (∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift))
        = ∑ u : K, ∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ u : K, ∑ a : Space m, signQ (out (query (a + u.val))) * (signQ (targetF (a + u.val)) - shift) := by
            apply Finset.sum_congr rfl
            intro u _
            exact (Fintype.sum_equiv (Equiv.addRight u.val) _ _ (fun _ => rfl)).symm
      _ = ∑ a : Space m, ∑ u : K, signQ (out (query a)) * (signQ (targetF (a + u.val)) - shift) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro u _
            rw [map_add, LinearMap.mem_ker.mp u.property, add_zero]
      _ = ∑ a : Space m, signQ (out (query a)) * (cosetSum K a - (Fintype.card K : ℚ) * shift) := by
            apply Finset.sum_congr rfl; intro a _
            rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            rfl
  rw [mul_comm, hfib]
  apply Finset.sum_congr rfl
  intro a _
  have hex : ∃ a' : Space m, query a' = query a := ⟨a, rfl⟩
  let a₀ := Classical.choose hex
  have ha₀ : query a₀ = query a := Classical.choose_spec hex
  have hdiff : a₀ + a ∈ K := by
    rw [LinearMap.mem_ker, map_add, ha₀]
    ext i; exact f2_add_self (query a i)
  have hcos_eq : cosetSum K a₀ = cosetSum K a := by
    have h1 : a₀ = a + (a₀ + a) := by
      apply Prod.ext
      · ext k
        simp only [Prod.fst_add, Pi.add_apply]
        have h2 := f2_add_self (a.1 k)
        linear_combination -h2
      · ext k
        simp only [Prod.snd_add, Pi.add_apply]
        have h3 := f2_add_self (a.2 k)
        linear_combination -h3
    conv_lhs => rw [h1]
    exact cosetSum_add_mem K a ⟨a₀ + a, hdiff⟩
  simp only [out, dif_pos hex]
  change signQ (if 0 ≤ cosetSum K a₀ - (Fintype.card K : ℚ) * shift then 0 else 1) *
    (cosetSum K a - (Fintype.card K : ℚ) * shift) = _
  rw [hcos_eq]
  by_cases hnn : 0 ≤ cosetSum K a - (Fintype.card K : ℚ) * shift
  · rw [if_pos hnn, signQ_zero, one_mul, abs_of_nonneg hnn]
  · rw [if_neg hnn, signQ_one, neg_one_mul, abs_of_neg (lt_of_not_ge hnn)]

lemma avg_abs_mono {m : ℕ} {K' K : Submodule F2 (Space m)} (hle : K' ≤ K) (shift : ℚ) :
    (∑ a : Space m, |cosetSum K a - (Fintype.card K : ℚ) * shift|) / (Fintype.card K : ℚ) ≤
    (∑ a : Space m, |cosetSum K' a - (Fintype.card K' : ℚ) * shift|) / (Fintype.card K' : ℚ) := by
  have hK_pos : (0 : ℚ) < (Fintype.card K : ℚ) := by rw [card_submodule]; positivity
  have hK'_pos : (0 : ℚ) < (Fintype.card K' : ℚ) := by rw [card_submodule]; positivity
  rw [div_le_div_iff₀ hK_pos hK'_pos]
  have hpt : ∀ a : Space m,
      (Fintype.card K' : ℚ) * |cosetSum K a - (Fintype.card K : ℚ) * shift| ≤
        ∑ v : K, |cosetSum K' (a + v.val) - (Fintype.card K' : ℚ) * shift| := by
    intro a
    have hid : (Fintype.card K' : ℚ) * (cosetSum K a - (Fintype.card K : ℚ) * shift) =
        ∑ v : K, (cosetSum K' (a + v.val) - (Fintype.card K' : ℚ) * shift) := by
      have h1 : (Fintype.card K' : ℚ) * cosetSum K a = ∑ v : K, cosetSum K' (a + v.val) := by
        simp only [cosetSum]
        calc (Fintype.card K' : ℚ) * ∑ v : K, signQ (targetF (a + v.val))
            = ∑ u : K', ∑ v : K, signQ (targetF (a + v.val)) := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = ∑ u : K', ∑ v : K, signQ (targetF (a + (v.val + u.val))) := by
                apply Finset.sum_congr rfl
                intro u _
                exact (Fintype.sum_equiv (Equiv.addRight (⟨u.val, hle u.property⟩ : K)) _ _ (fun _ => rfl)).symm
          _ = ∑ v : K, ∑ u : K', signQ (targetF ((a + v.val) + u.val)) := by
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl; intro v _
                apply Finset.sum_congr rfl; intro u _
                rw [add_assoc]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← h1]
      ring
    calc (Fintype.card K' : ℚ) * |cosetSum K a - (Fintype.card K : ℚ) * shift|
        = |(Fintype.card K' : ℚ) * (cosetSum K a - (Fintype.card K : ℚ) * shift)| := by
            rw [abs_mul, abs_of_pos hK'_pos]
      _ = |∑ v : K, (cosetSum K' (a + v.val) - (Fintype.card K' : ℚ) * shift)| := by rw [hid]
      _ ≤ ∑ v : K, |cosetSum K' (a + v.val) - (Fintype.card K' : ℚ) * shift| := Finset.abs_sum_le_sum_abs _ _
  calc (∑ a : Space m, |cosetSum K a - (Fintype.card K : ℚ) * shift|) * (Fintype.card K' : ℚ)
      = ∑ a : Space m, (Fintype.card K' : ℚ) * |cosetSum K a - (Fintype.card K : ℚ) * shift| := by
          rw [mul_comm, Finset.mul_sum]
    _ ≤ ∑ a : Space m, ∑ v : K, |cosetSum K' (a + v.val) - (Fintype.card K' : ℚ) * shift| :=
          Finset.sum_le_sum (fun a _ => hpt a)
    _ = ∑ v : K, ∑ a : Space m, |cosetSum K' (a + v.val) - (Fintype.card K' : ℚ) * shift| :=
          Finset.sum_comm
    _ = ∑ _ : K, ∑ a : Space m, |cosetSum K' a - (Fintype.card K' : ℚ) * shift| := by
          apply Finset.sum_congr rfl
          intro v _
          exact Fintype.sum_equiv (Equiv.addRight v.val) _ _ (fun _ => rfl)
    _ = (∑ a : Space m, |cosetSum K' a - (Fintype.card K' : ℚ) * shift|) * (Fintype.card K : ℚ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

lemma exists_subspace_of_finrank {m : ℕ} (K : Submodule F2 (Space m)) (t : ℕ)
    (ht : t ≤ Module.finrank F2 K) :
    ∃ K' : Submodule F2 (Space m), K' ≤ K ∧ Module.finrank F2 K' = t := by
  let b := Module.finBasis F2 K
  let f : Fin t → Space m := fun i => (b ⟨i.val, by omega⟩).val
  let K' : Submodule F2 (Space m) := Submodule.span F2 (Set.range f)
  refine ⟨K', ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b ⟨i.val, by omega⟩).property
  · have hli : LinearIndependent F2 f := by
      have h1 : LinearIndependent F2 (fun i : Fin t => b ⟨i.val, by omega⟩) :=
        b.linearIndependent.comp (fun i : Fin t => (⟨i.val, by omega⟩ : Fin (Module.finrank F2 K)))
          (fun i₁ i₂ h => Fin.ext (by simpa using congrArg Fin.val h))
      exact h1.map' K.subtype K.ker_subtype
    rw [finrank_span_eq_card hli, Fintype.card_fin]

def canonQuery (m j r : ℕ) (h2r : 2 * r ≤ j) (hmr : j ≤ m + r) :
    Space m →ₗ[F2] (Fin j → F2) where
  toFun x i :=
    if h1 : i.val < r then x.1 ⟨i.val, by omega⟩
    else if h2 : i.val < 2 * r then x.2 ⟨i.val - r, by omega⟩
    else x.1 ⟨i.val - r, by omega⟩
  map_add' x y := by
    ext i; dsimp
    split_ifs <;> rfl
  map_smul' c x := by
    ext i; dsimp
    split_ifs <;> rfl

lemma canonQuery_surjective (m j r : ℕ) (h2r : 2 * r ≤ j) (hmr : j ≤ m + r) :
    Function.Surjective (canonQuery m j r h2r hmr) := by
  intro y
  let x : Space m :=
    (fun k =>
      if h1 : k.val < r then y ⟨k.val, by omega⟩
      else if h2 : k.val < j - r then y ⟨k.val + r, by omega⟩
      else 0,
     fun k =>
      if h1 : k.val < r then y ⟨k.val + r, by omega⟩
      else 0)
  refine ⟨x, ?_⟩
  ext i
  simp only [canonQuery, LinearMap.coe_mk, AddHom.coe_mk, x]
  by_cases h1 : i.val < r
  · simp only [h1, ↓reduceDIte]
  · by_cases h2 : i.val < 2 * r
    · simp only [h1, h2, ↓reduceDIte]
      have h3 : i.val - r < r := by omega
      simp only [h3, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega
    · simp only [h1, h2, ↓reduceDIte]
      have h3 : ¬ (i.val - r < r) := by omega
      have h4 : i.val - r < j - r := by omega
      simp only [h3, h4, ↓reduceDIte]
      congr 1; apply Fin.ext; dsimp; omega

lemma canonQuery_ker_finrank (m j r : ℕ) (h2r : 2 * r ≤ j) (hmr : j ≤ m + r) :
    Module.finrank F2 (LinearMap.ker (canonQuery m j r h2r hmr)) = 2 * m - j := by
  have h := LinearMap.finrank_range_add_finrank_ker (canonQuery m j r h2r hmr)
  rw [LinearMap.range_eq_top.mpr (canonQuery_surjective m j r h2r hmr), finrank_top,
      Module.finrank_pi, Fintype.card_fin, finrank_space] at h
  omega

lemma canonQuery_rad_finrank (m j r : ℕ) (h2r : 2 * r ≤ j) (hmr : j ≤ m + r) :
    Module.finrank F2 (radB (LinearMap.ker (canonQuery m j r h2r hmr))) = j - 2 * r := by
  let K := LinearMap.ker (canonQuery m j r h2r hmr)
  have hmemK : ∀ u : Space m, u ∈ K ↔
      (∀ k : Fin m, k.val < j - r → u.1 k = 0) ∧ (∀ k : Fin m, k.val < r → u.2 k = 0) := by
    intro u
    rw [LinearMap.mem_ker]
    constructor
    · intro hu
      refine ⟨fun k hk => ?_, fun k hk => ?_⟩
      · by_cases h1 : k.val < r
        · have h := congrFun hu ⟨k.val, by omega⟩
          simpa [canonQuery, h1] using h
        · have h := congrFun hu ⟨k.val + r, by omega⟩
          have hn1 : ¬ (k.val + r < r) := by omega
          have hn2 : ¬ (k.val + r < 2 * r) := by omega
          have heq : (⟨k.val + r - r, by omega⟩ : Fin m) = k := Fin.ext (by dsimp; omega)
          simpa [canonQuery, hn1, hn2, heq] using h
      · have h := congrFun hu ⟨k.val + r, by omega⟩
        have hn1 : ¬ (k.val + r < r) := by omega
        have h2 : k.val + r < 2 * r := by omega
        have heq : (⟨k.val + r - r, by omega⟩ : Fin m) = k := Fin.ext (by dsimp; omega)
        simpa [canonQuery, hn1, h2, heq] using h
    · rintro ⟨h1, h2⟩
      ext i
      simp only [canonQuery, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
      split_ifs with c1 c2
      · exact h1 ⟨i.val, by omega⟩ (by dsimp; omega)
      · exact h2 ⟨i.val - r, by omega⟩ (by dsimp; omega)
      · exact h1 ⟨i.val - r, by omega⟩ (by dsimp; omega)
  have hmemR : ∀ u : Space m, u ∈ radB K ↔
      (∀ k : Fin m, u.1 k = 0) ∧ (∀ k : Fin m, k.val < r ∨ j - r ≤ k.val → u.2 k = 0) := by
    intro u
    rw [mem_radB]
    constructor
    · rintro ⟨huK, horth⟩
      have hu := (hmemK u).mp huK
      refine ⟨fun k => ?_, fun k hk => ?_⟩
      · by_cases h1 : k.val < j - r
        · exact hu.1 k h1
        · let v : Space m := (0, fun i => if i = k then 1 else 0)
          have hvK : v ∈ K := (hmemK v).mpr ⟨fun _ _ => rfl, fun i hi => by
            dsimp [v]; rw [if_neg (fun heq => by subst heq; omega)]⟩
          have h0 := horth v hvK
          simpa [sympB, v] using h0
      · rcases hk with h1 | h2
        · exact hu.2 k h1
        · let v : Space m := (fun i => if i = k then 1 else 0, 0)
          have hvK : v ∈ K := (hmemK v).mpr ⟨fun i hi => by
            dsimp [v]; rw [if_neg (fun heq => by subst heq; omega)], fun _ _ => rfl⟩
          have h0 := horth v hvK
          simpa [sympB, v] using h0
    · rintro ⟨h1, h2⟩
      refine ⟨(hmemK u).mpr ⟨fun k _ => h1 k, fun k hk => h2 k (Or.inl hk)⟩, fun v hvK => ?_⟩
      have hv := (hmemK v).mp hvK
      simp only [sympB]
      apply Finset.sum_eq_zero
      intro k _
      rw [h1 k, zero_mul, zero_add]
      by_cases hk : k.val < j - r
      · rw [hv.1 k hk, mul_zero]
      · rw [h2 k (Or.inr (by omega)), zero_mul]
  let φ : (Fin (j - 2 * r) → F2) →ₗ[F2] radB K :=
    { toFun := fun f =>
        ⟨(0, fun k => if h : r ≤ k.val ∧ k.val < j - r then f ⟨k.val - r, by omega⟩ else 0),
         (hmemR _).mpr ⟨fun _ => rfl, fun k hk => by
           dsimp; rw [dif_neg (by rcases hk with h | h <;> omega)]⟩⟩
      map_add' := fun f g => by
        apply Subtype.ext; apply Prod.ext
        · ext k; simp
        · ext k; dsimp; split_ifs <;> simp
      map_smul' := fun c f => by
        apply Subtype.ext; apply Prod.ext
        · ext k; simp
        · ext k; dsimp; split_ifs <;> simp }
  have hbij : Function.Bijective φ := by
    constructor
    · intro f g hfg
      ext i
      have h1 := congrFun (congrArg (fun u : radB K => u.val.2) hfg) ⟨i.val + r, by omega⟩
      have hcond : r ≤ i.val + r ∧ i.val + r < j - r := by omega
      have heq : (⟨i.val + r - r, by omega⟩ : Fin (j - 2 * r)) = i := Fin.ext (by dsimp; omega)
      simpa [φ, hcond, heq] using h1
    · rintro ⟨u, hu⟩
      have huR := (hmemR u).mp hu
      refine ⟨fun i => u.2 ⟨i.val + r, by omega⟩, ?_⟩
      apply Subtype.ext; apply Prod.ext
      · ext k; exact (huR.1 k).symm
      · ext k; dsimp [φ]
        split_ifs with hcond
        · exact congrArg u.2 (Fin.ext (by dsimp; omega))
        · exact (huR.2 k (by omega)).symm
  have hlequiv : (Fin (j - 2 * r) → F2) ≃ₗ[F2] radB K := LinearEquiv.ofBijective φ hbij
  rw [← hlequiv.finrank_eq, Module.finrank_pi, Fintype.card_fin]

lemma main_460 :
    ∀ m j : ℕ, j ≤ 2*m →
      let F := ZMod 2
      let V := Fin m → F
      let X := V × V
      let target := fun x : X => ∑ k : Fin m, x.1 k * x.2 k
      let sign := fun z : F => if z=0 then (1 : ℚ) else -1
      let base := (1 : ℚ)/2^m
      ∀ shift threshold : ℚ,
        (∃ (query : X →ₗ[F] (Fin j → F)) (out : (Fin j → F) → F),
          threshold*(Nat.card X : ℚ) ≤
            ∑ x : X, sign (out (query x)) * (sign (target x)-shift)) ↔
        ∃ r : ℕ, 2*r ≤ j ∧ j ≤ m+r ∧
          let amp := (1 : ℚ)/2^(m+r-j)
          let mass := (1 : ℚ)/2^(j-2*r)
          threshold ≤ (1-mass)*|shift| +
            (mass+base/amp)/2 * |amp-shift| +
            (mass-base/amp)/2 * |amp+shift| := by
  intro m j hj F V X target sign base shift threshold
  have hX_pos : (0 : ℚ) < (Nat.card (Space m) : ℚ) := by
    rw [natCard_space]; positivity
  constructor
  · rintro ⟨query, out, hbound⟩
    let K := LinearMap.ker query
    have hK_ge : 2 * m - j ≤ Module.finrank F2 K := by
      have h1 : Module.finrank F2 (LinearMap.range query) + Module.finrank F2 K = 2 * m := by
        have h := LinearMap.finrank_range_add_finrank_ker query
        rwa [finrank_space] at h
      have h2 : Module.finrank F2 (LinearMap.range query) ≤ j := by
        have := Submodule.finrank_le (LinearMap.range query)
        simpa [Module.finrank_pi, Fintype.card_fin] using this
      omega
    rcases exists_subspace_of_finrank K (2 * m - j) hK_ge with ⟨K', hK'_le, hK'_dim⟩
    have h1 : threshold * (Nat.card (Space m) : ℚ) ≤
        (∑ a : Space m, |cosetSum K a - (Fintype.card K : ℚ) * shift|) / (Fintype.card K : ℚ) :=
      le_trans hbound (query_score_bound query out shift)
    have h2 : (∑ a : Space m, |cosetSum K a - (Fintype.card K : ℚ) * shift|) / (Fintype.card K : ℚ) ≤
        (∑ a : Space m, |cosetSum K' a - (Fintype.card K' : ℚ) * shift|) / (Fintype.card K' : ℚ) :=
      avg_abs_mono hK'_le shift
    have h3 : threshold ≤
        (∑ a : Space m, |cosetSum K' a - (Fintype.card K' : ℚ) * shift|) /
          ((Fintype.card K' : ℚ) * (Nat.card (Space m) : ℚ)) := by
      rw [← div_div]
      exact (le_div_iff₀ hX_pos).mpr (le_trans h1 h2)
    have hexact := exact_score_of_subspace m j hj K' hK'_dim shift
    refine ⟨(j - Module.finrank F2 (radB K')) / 2, hexact.1, hexact.2.1, ?_⟩
    dsimp only
    rw [← hexact.2.2.2]
    exact h3
  · rintro ⟨r, h2r, hmr, hth⟩
    let query := canonQuery m j r h2r hmr
    have hdimK := canonQuery_ker_finrank m j r h2r hmr
    have hdimR := canonQuery_rad_finrank m j r h2r hmr
    have hexact := exact_score_of_subspace m j hj (LinearMap.ker query) hdimK shift
    rcases query_score_achieve query shift with ⟨out, hout⟩
    refine ⟨query, out, ?_⟩
    have hr_eq : (j - Module.finrank F2 (radB (LinearMap.ker query))) / 2 = r := by
      rw [hdimR]; omega
    have hscore := hexact.2.2.2
    rw [hr_eq] at hscore
    have hle : threshold ≤
        (∑ a : Space m, |cosetSum (LinearMap.ker query) a -
          (Fintype.card (LinearMap.ker query) : ℚ) * shift|) /
        ((Fintype.card (LinearMap.ker query) : ℚ) * (Nat.card (Space m) : ℚ)) := by
      rw [hscore]
      exact hth
    rw [← div_div] at hle
    have hmul := (le_div_iff₀ hX_pos).mp hle
    change threshold * (Nat.card (Space m) : ℚ) ≤
      ∑ x : Space m, signQ (out (query x)) * (signQ (targetF x) - shift)
    rw [hout]
    exact hmul

end

end PEqualNP.Outside.L_pcx_460_aux

theorem PEqualNP.Outside.L_pcx_460 :
∀ m j : ℕ, j ≤ 2*m →
  let F := ZMod 2
  let V := Fin m → F
  let X := V × V
  let target := fun x : X => ∑ k : Fin m, x.1 k * x.2 k
  let sign := fun z : F => if z=0 then (1 : ℚ) else -1
  let base := (1 : ℚ)/2^m
  ∀ shift threshold : ℚ,
    (∃ (query : X →ₗ[F] (Fin j → F)) (out : (Fin j → F) → F),
      threshold*(Nat.card X : ℚ) ≤
        ∑ x : X, sign (out (query x)) * (sign (target x)-shift)) ↔
    ∃ r : ℕ, 2*r ≤ j ∧ j ≤ m+r ∧
      let amp := (1 : ℚ)/2^(m+r-j)
      let mass := (1 : ℚ)/2^(j-2*r)
      threshold ≤ (1-mass)*|shift| +
        (mass+base/amp)/2 * |amp-shift| +
        (mass-base/amp)/2 * |amp+shift| :=
  PEqualNP.Outside.L_pcx_460_aux.main_460
