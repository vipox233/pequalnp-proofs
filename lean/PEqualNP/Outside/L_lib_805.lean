import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_805_aux

abbrev F := ZMod 2

def chi (a : F) : ℤ :=
  if a = 0 then 1 else -1

lemma chi_zero : chi 0 = 1 := rfl

lemma chi_one : chi 1 = -1 := rfl

lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma chi_sum {ι : Type*} (s : Finset ι) (f : ι → F) :
    chi (∑ i ∈ s, f i) = ∏ i ∈ s, chi (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chi_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, chi_add, ih]

lemma z2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> rfl

lemma z2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma z2_eq_one_of_ne_zero {a : F} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact False.elim (h rfl)
  · rfl

lemma chi_linear_sum {E : Type*} [AddCommGroup E] [Module F E] [Fintype E]
    (L : E →ₗ[F] F) :
    (∑ x : E, chi (L x)) = if L = 0 then (Fintype.card E : ℤ) else 0 := by
  by_cases hL : L = 0
  · subst hL
    simp [chi_zero]
  · simp only [hL, ↓reduceIte]
    have hex : ∃ x₀ : E, L x₀ ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hL
      exact LinearMap.ext hno
    obtain ⟨x₀, hx₀⟩ := hex
    have h1 : L x₀ = 1 := z2_eq_one_of_ne_zero hx₀
    have hshift : (∑ x : E, chi (L (x + x₀))) = ∑ x : E, chi (L x) :=
      Fintype.sum_equiv (Equiv.addRight x₀) _ _ (fun _ => rfl)
    have hneg : (∑ x : E, chi (L (x + x₀))) = -(∑ x : E, chi (L x)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_add, chi_add, h1, chi_one]
      ring
    omega

lemma sum_chi_dot {r : Nat} (a : Fin r → F) :
    (∑ u : Fin r → F, chi (∑ k : Fin r, u k * a k)) =
      if a = 0 then (2 : ℤ) ^ r else 0 := by
  let L : (Fin r → F) →ₗ[F] F :=
    { toFun := fun u => ∑ k : Fin r, u k * a k
      map_add' := fun u v => by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c u => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have h := chi_linear_sum L
  have hL0 : L = 0 ↔ a = 0 := by
    constructor
    · intro h0
      ext k
      have hk := LinearMap.congr_fun h0 (Pi.single k (1 : F))
      simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply, Pi.single_apply,
        Pi.zero_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte] using hk
    · intro h0
      subst h0
      refine LinearMap.ext fun u => ?_
      simp [L]
  have hcard : (Fintype.card (Fin r → F) : ℤ) = (2 : ℤ) ^ r := by
    simp [Fintype.card_pi, Fintype.card_fin, ZMod.card]
  simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, hL0, hcard] using h

lemma linear_fin_eq_dot {r : Nat} (φ : (Fin r → F) →ₗ[F] F) :
    ∃ u : Fin r → F, ∀ y : Fin r → F, φ y = ∑ k : Fin r, u k * y k := by
  refine ⟨fun k => φ (Pi.single k 1), fun y => ?_⟩
  have hy : y = ∑ k : Fin r, y k • Pi.single (M := fun _ => F) k (1 : F) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  conv_lhs => rw [hy]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => mul_comm _ _

lemma block_sum_zero {w : Nat} (hw : 2 ≤ w) (L : (Fin w → F) →ₗ[F] F) :
    (4 : ℤ) ∣ ∑ z : Fin w → F, chi (L z) := by
  rw [chi_linear_sum]
  split_ifs
  · have hcard : (Fintype.card (Fin w → F) : ℤ) = (2 : ℤ) ^ w := by
      simp [Fintype.card_pi, Fintype.card_fin, ZMod.card]
    rw [hcard]
    have hpow : (2 : ℤ) ^ w = (4 : ℤ) * (2 : ℤ) ^ (w - 2) := by
      have hw' : w = 2 + (w - 2) := by omega
      conv_lhs => rw [hw']
      rw [pow_add]
      norm_num
    exact ⟨(2 : ℤ) ^ (w - 2), hpow⟩
  · exact dvd_zero 4

lemma block_sum_one_eq {w : Nat} (L : (Fin w → F) →ₗ[F] F) (center : Fin w → F) :
    (∑ z : Fin w → F, chi (L z + (if z = center then (1 : F) else 0))) =
      (if L = 0 then (2 : ℤ) ^ w else 0) - 2 * chi (L center) := by
  have hbase : (∑ z : Fin w → F, chi (L z)) = if L = 0 then (2 : ℤ) ^ w else 0 := by
    rw [chi_linear_sum]
    have hcard : (Fintype.card (Fin w → F) : ℤ) = (2 : ℤ) ^ w := by
      simp [Fintype.card_pi, Fintype.card_fin, ZMod.card]
    rw [hcard]
  rw [← hbase]
  have hdiff :
      (∑ z : Fin w → F, (chi (L z + (if z = center then (1 : F) else 0)) - chi (L z))) =
        -2 * chi (L center) := by
    rw [Finset.sum_eq_single center]
    · simp only [↓reduceIte, chi_add, chi_one]
      ring
    · intro z _ hne
      simp [hne]
    · intro habs
      exact False.elim (habs (Finset.mem_univ center))
  rw [Finset.sum_sub_distrib] at hdiff
  omega

lemma block_sum_two_dvd {w : Nat} (hw : 2 ≤ w) (L : (Fin w → F) →ₗ[F] F)
    (center : Fin w → F) (c : F) :
    (2 : ℤ) ∣ ∑ z : Fin w → F, chi (L z + c * (if z = center then (1 : F) else 0)) := by
  rcases z2_cases c with rfl | rfl
  · have h4 := block_sum_zero hw L
    simp only [zero_mul, add_zero]
    exact dvd_trans (by norm_num : (2 : ℤ) ∣ 4) h4
  · simp only [one_mul]
    rw [block_sum_one_eq L center]
    split_ifs
    · have h2w : (2 : ℤ) ∣ (2 : ℤ) ^ w := by
        have hw' : w = 1 + (w - 1) := by omega
        conv_rhs => rw [hw']
        rw [pow_add, pow_one]
        exact dvd_mul_right 2 _
      exact dvd_sub h2w (dvd_mul_right 2 _)
    · rw [zero_sub]
      exact dvd_neg.mpr (dvd_mul_right 2 _)

lemma prod_dvd_of_all_two {m : Nat} (f : Fin m → ℤ)
    (h2 : ∀ i : Fin m, (2 : ℤ) ∣ f i) :
    (2 : ℤ) ^ m ∣ ∏ i : Fin m, f i := by
  have hprod : (∏ i : Fin m, (2 : ℤ)) ∣ ∏ i : Fin m, f i :=
    Finset.prod_dvd_prod_of_dvd (fun _ => (2 : ℤ)) f (fun i _ => h2 i)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hprod

lemma prod_dvd_extra_two {m : Nat} (f : Fin m → ℤ) (i₀ : Fin m)
    (h2 : ∀ i : Fin m, (2 : ℤ) ∣ f i) (h4 : (4 : ℤ) ∣ f i₀) :
    (2 : ℤ) ^ (m + 1) ∣ ∏ i : Fin m, f i := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i₀)]
  have herase : (∏ i ∈ Finset.univ.erase i₀, (2 : ℤ)) ∣ ∏ i ∈ Finset.univ.erase i₀, f i :=
    Finset.prod_dvd_prod_of_dvd (fun _ => (2 : ℤ)) f (fun i _ => h2 i)
  have hcard : (Finset.univ.erase i₀).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, Fintype.card_fin]
  have hm : 1 ≤ m := Nat.pos_of_ne_zero (fun h0 => Fin.elim0 (h0 ▸ i₀))
  rw [Finset.prod_const, hcard] at herase
  have hmul := mul_dvd_mul h4 herase
  have hpow : (4 : ℤ) * (2 : ℤ) ^ (m - 1) = (2 : ℤ) ^ (m + 1) := by
    have heq : m + 1 = 2 + (m - 1) := by omega
    rw [heq, pow_add]
    norm_num
  rwa [hpow] at hmul

lemma two_pow_dvd_and_not_next_of_odd_mul {k : Nat} {a : ℤ}
    (hodd : ¬ ((2 : ℤ) ∣ a)) :
    (2 : ℤ) ^ k ∣ (2 : ℤ) ^ k * a ∧ ¬ ((2 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ k * a) := by
  refine ⟨dvd_mul_right _ _, ?_⟩
  intro hdvd
  rw [pow_succ] at hdvd
  have hpos : (2 : ℤ) ^ k ≠ 0 := by positivity
  rcases hdvd with ⟨q, hq⟩
  have ha : a = 2 * q := by
    have hmul : (2 : ℤ) ^ k * a = (2 : ℤ) ^ k * (2 * q) := by linarith
    exact mul_left_cancel₀ hpos hmul
  exact hodd ⟨q, ha⟩

lemma odd_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) (h : ∀ i ∈ s, ¬ ((2 : ℤ) ∣ f i)) :
    ¬ ((2 : ℤ) ∣ ∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      omega
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro hdvd
      have hpa : ¬ ((2 : ℤ) ∣ f a) := h a (Finset.mem_insert_self a s)
      have hps : ¬ ((2 : ℤ) ∣ ∏ i ∈ s, f i) := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hprime : Prime (2 : ℤ) := Int.prime_two
      rcases hprime.dvd_or_dvd hdvd with h1 | h2
      · exact hpa h1
      · exact hps h2

lemma signed_divisibility (m r spare : Nat) (w : Fin m → Nat)
    (hm : 0 < m) (hr : 0 < r) (hw : ∀ i, 2 ≤ w i)
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) (full : (Fin r → F) →ₗ[F] F)
    (hAsurj : Function.Surjective A) (hfull : ∀ z : Fin m → F, full (A z) = ∑ i : Fin m, z i)
    (center : (i : Fin m) → Fin (w i) → F)
    (tilt : (((i : Fin m) → Fin (w i) → F) × (Fin spare → F)) →ₗ[F] (Fin r → F))
    (offset : Fin r → F) :
    let V := ((i : Fin m) → Fin (w i) → F) × (Fin spare → F)
    let answer := fun x : V => offset + tilt x +
      A (fun i => if x.1 i = center i then 1 else 0)
    let signed := fun y : Fin r → F => ∑ x : V,
      if answer x = y then (if full (tilt x) = 0 then (1 : ℤ) else -1) else 0
    let v := m + spare - r
    r ≤ m ∧ ∀ y : Fin r → F, ((2 : ℤ) ^ v ∣ signed y) ∧ ¬ ((2 : ℤ) ^ (v + 1) ∣ signed y) := by
  intro V answer signed v
  have hrle : r ≤ m := by
    have hcard : Fintype.card (Fin r → F) ≤ Fintype.card (Fin m → F) :=
      Fintype.card_le_of_surjective A hAsurj
    simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const,
      Finset.card_univ] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  refine ⟨hrle, fun y => ?_⟩
  let g : V → Fin m → F := fun x i => if x.1 i = center i then 1 else 0
  have h2r : (2 : ℤ) ^ r * signed y =
      ∑ u : Fin r → F, chi (∑ k : Fin r, u k * (y k + offset k)) *
        ∑ x : V, chi (full (tilt x) + (∑ k : Fin r, u k * tilt x k) +
          ∑ k : Fin r, u k * A (g x) k) := by
    have h1 : (2 : ℤ) ^ r * signed y =
        ∑ x : V, chi (full (tilt x)) * (if answer x + y = 0 then (2 : ℤ) ^ r else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      have heq : answer x + y = 0 ↔ answer x = y := by
        constructor
        · intro h0
          ext k
          have hk := congrFun h0 k
          simp only [Pi.add_apply, Pi.zero_apply] at hk
          have h2 := congrArg (fun t => t + y k) hk
          simpa only [add_assoc, z2_add_self, add_zero, zero_add] using h2
        · intro hxy
          rw [hxy]
          ext k
          exact z2_add_self (y k)
      simp only [heq, chi]
      split_ifs <;> ring
    rw [h1]
    have h2 : (∑ x : V, chi (full (tilt x)) * (if answer x + y = 0 then (2 : ℤ) ^ r else 0)) =
        ∑ x : V, ∑ u : Fin r → F,
          chi (full (tilt x)) * chi (∑ k : Fin r, u k * (answer x + y) k) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← sum_chi_dot (answer x + y), Finset.mul_sum]
    rw [h2, Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← chi_add, ← chi_add]
    congr 1
    have hsum_eq : (∑ k : Fin r, u k * (answer x + y) k) =
        (∑ k : Fin r, u k * (y k + offset k)) +
        (∑ k : Fin r, u k * tilt x k) +
        (∑ k : Fin r, u k * A (g x) k) := by
      simp only [answer, g, Pi.add_apply]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum_eq]
    ring
  let S : (Fin r → F) → ℤ := fun u =>
    ∑ x : V, chi (full (tilt x) + (∑ k : Fin r, u k * tilt x k) +
      ∑ k : Fin r, u k * A (g x) k)
  let inBlock : (i : Fin m) → (Fin (w i) → F) →ₗ[F] V := fun i =>
    { toFun := fun z => (fun j => if h : j = i then h ▸ z else 0, 0)
      map_add' := fun z₁ z₂ => by
        refine Prod.ext ?_ (add_zero (0 : Fin spare → F)).symm
        ext j t
        change (if h : j = i then h ▸ (z₁ + z₂) else 0) t =
          (if h : j = i then h ▸ z₁ else 0) t + (if h : j = i then h ▸ z₂ else 0) t
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      map_smul' := fun c z => by
        refine Prod.ext ?_ (smul_zero c : c • (0 : Fin spare → F) = 0).symm
        ext j t
        change (if h : j = i then h ▸ (c • z) else 0) t =
          c * (if h : j = i then h ▸ z else 0) t
        by_cases h : j = i
        · subst h; simp
        · simp [h] }
  let inSpare : (Fin spare → F) →ₗ[F] V :=
    { toFun := fun s => (0, s)
      map_add' := fun _ _ => Prod.ext (add_zero 0).symm rfl
      map_smul' := fun c _ => Prod.ext (smul_zero c).symm rfl }
  have hdecompV : ∀ x : V, x = (∑ i : Fin m, inBlock i (x.1 i)) + inSpare x.2 := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add, Prod.fst_sum]
      ext i t
      simp only [Pi.add_apply, Finset.sum_apply, inSpare, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.zero_apply, add_zero]
      rw [Finset.sum_eq_single i]
      · simp [inBlock]
      · intro j _ hji
        simp [inBlock, hji.symm]
      · intro habs
        exact False.elim (habs (Finset.mem_univ i))
    · rw [Prod.snd_add, Prod.snd_sum]
      simp [inBlock, inSpare]
  let Lu : (Fin r → F) → V →ₗ[F] F := fun u =>
    { toFun := fun x => full (tilt x) + ∑ k : Fin r, u k * tilt x k
      map_add' := fun x₁ x₂ => by
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := fun c x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => by ring }
  let cu : (Fin r → F) → Fin m → F := fun u i => ∑ k : Fin r, u k * A (Pi.single i 1) k
  have hS_factor : ∀ u : Fin r → F,
      S u = (∑ s : Fin spare → F, chi (Lu u (inSpare s))) *
        ∏ i : Fin m, ∑ z : Fin (w i) → F,
          chi (Lu u (inBlock i z) + cu u i * (if z = center i then (1 : F) else 0)) := by
    intro u
    have hexpr : ∀ x : V,
        chi (full (tilt x) + (∑ k : Fin r, u k * tilt x k) + ∑ k : Fin r, u k * A (g x) k) =
        chi (Lu u (inSpare x.2)) *
          ∏ i : Fin m, chi (Lu u (inBlock i (x.1 i)) + cu u i * g x i) := by
      intro x
      have hLu : full (tilt x) + (∑ k : Fin r, u k * tilt x k) =
          Lu u (inSpare x.2) + ∑ i : Fin m, Lu u (inBlock i (x.1 i)) := by
        change Lu u x = _
        conv_lhs => rw [hdecompV x]
        rw [map_add, map_sum, add_comm]
      have hg_decomp : g x = ∑ i : Fin m, g x i • Pi.single (M := fun _ => F) i (1 : F) := by
        ext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      have hAg : (∑ k : Fin r, u k * A (g x) k) = ∑ i : Fin m, cu u i * g x i := by
        conv_lhs => rw [hg_decomp]
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ k : Fin r, u k * ∑ i : Fin m, g x i * A (Pi.single i 1) k) =
              ∑ k : Fin r, ∑ i : Fin m, u k * (g x i * A (Pi.single i 1) k) := by
                refine Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _
          _ = ∑ i : Fin m, ∑ k : Fin r, u k * (g x i * A (Pi.single i 1) k) := Finset.sum_comm
          _ = ∑ i : Fin m, cu u i * g x i := by
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only [cu, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => by ring
      rw [hLu, hAg, add_assoc, ← Finset.sum_add_distrib, chi_add, chi_sum]
    change (∑ x : V, _) = _
    simp_rw [hexpr]
    rw [Fintype.sum_prod_type_right]
    simp_rw [← Finset.mul_sum]
    simp only [g]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    exact (Fintype.prod_sum (fun i z =>
      chi (Lu u (inBlock i z) + cu u i * (if z = center i then (1 : F) else 0)))).symm
  obtain ⟨uFull, huFull⟩ := linear_fin_eq_dot full
  have hLu_full : Lu uFull = 0 := by
    refine LinearMap.ext fun x => ?_
    change full (tilt x) + ∑ k : Fin r, uFull k * tilt x k = 0
    rw [← huFull (tilt x)]
    exact z2_add_self _
  have hcu_full : ∀ i : Fin m, cu uFull i = 1 := by
    intro i
    change ∑ k : Fin r, uFull k * A (Pi.single i 1) k = 1
    rw [← huFull (A (Pi.single i 1)), hfull (Pi.single i 1)]
    simp only [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hS_full : ∃ a : ℤ, ¬ ((2 : ℤ) ∣ a) ∧ S uFull = (2 : ℤ) ^ (m + spare) * a := by
    rw [hS_factor uFull]
    have hsp : (∑ s : Fin spare → F, chi (Lu uFull (inSpare s))) = (2 : ℤ) ^ spare := by
      simp [hLu_full, chi_zero, Fintype.card_pi, Fintype.card_fin, ZMod.card]
    have hblk : ∀ i : Fin m,
        (∑ z : Fin (w i) → F,
          chi (Lu uFull (inBlock i z) + cu uFull i * (if z = center i then (1 : F) else 0))) =
        (2 : ℤ) * ((2 : ℤ) ^ (w i - 1) - 1) := by
      intro i
      have h0 : (Lu uFull).comp (inBlock i) = 0 := by
        refine LinearMap.ext fun z => by simp [hLu_full]
      have hterm := block_sum_one_eq ((Lu uFull).comp (inBlock i)) (center i)
      simp only [h0, ↓reduceIte, LinearMap.zero_apply, chi_zero, mul_one] at hterm
      have hrewrite :
          (∑ z : Fin (w i) → F,
            chi (Lu uFull (inBlock i z) + cu uFull i * (if z = center i then (1 : F) else 0))) =
          (∑ z : Fin (w i) → F,
            chi (0 + (if z = center i then (1 : F) else 0))) := by
        refine Finset.sum_congr rfl fun z _ => by simp [hLu_full, hcu_full i]
      rw [hrewrite, hterm]
      have hwi : w i = 1 + (w i - 1) := by have := hw i; omega
      conv_lhs => rw [hwi]
      rw [pow_add, pow_one]
      ring
    rw [hsp]
    simp_rw [hblk, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine ⟨∏ i : Fin m, ((2 : ℤ) ^ (w i - 1) - 1), ?_, ?_⟩
    · refine odd_prod Finset.univ _ fun i _ => ?_
      have hwi : 1 ≤ w i - 1 := by have := hw i; omega
      have h2div : (2 : ℤ) ∣ (2 : ℤ) ^ (w i - 1) := by
        have heq : w i - 1 = 1 + (w i - 2) := by omega
        rw [heq, pow_add, pow_one]
        exact dvd_mul_right 2 _
      intro hdvd
      have h1 : (2 : ℤ) ∣ (1 : ℤ) := by
        have hsub := dvd_sub h2div hdvd
        simp only [sub_sub_cancel] at hsub
        exact hsub
      omega
    · rw [pow_add]
      ring
  have hS_other : ∀ u : Fin r → F, u ≠ uFull → (2 : ℤ) ^ (m + spare + 1) ∣ S u := by
    intro u hu
    have hex0 : ∃ i₀ : Fin m, cu u i₀ = 0 := by
      by_contra hno
      push Not at hno
      have hall1 : ∀ i : Fin m, cu u i = 1 := fun i => z2_eq_one_of_ne_zero (hno i)
      apply hu
      ext k
      obtain ⟨z, hz⟩ := hAsurj (Pi.single k (1 : F))
      have hdot_u : (∑ j : Fin r, u j * A z j) = ∑ i : Fin m, z i := by
        have hz_decomp : z = ∑ i : Fin m, z i • Pi.single (M := fun _ => F) i (1 : F) := by
          ext i
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
            mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        conv_lhs => rw [hz_decomp]
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc
          (∑ j : Fin r, u j * ∑ i : Fin m, z i * A (Pi.single i 1) j) =
              ∑ j : Fin r, ∑ i : Fin m, u j * (z i * A (Pi.single i 1) j) := by
                refine Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
          _ = ∑ i : Fin m, ∑ j : Fin r, u j * (z i * A (Pi.single i 1) j) := Finset.sum_comm
          _ = ∑ i : Fin m, z i * cu u i := by
                refine Finset.sum_congr rfl fun i _ => ?_
                simp only [cu, Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ i : Fin m, z i := by
                refine Finset.sum_congr rfl fun i _ => by rw [hall1 i, mul_one]
      have hdot_full : (∑ j : Fin r, uFull j * A z j) = ∑ i : Fin m, z i := by
        rw [← huFull (A z), hfull z]
      have huk : u k = ∑ j : Fin r, u j * A z j := by
        rw [hz]
        simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      have hfk : uFull k = ∑ j : Fin r, uFull j * A z j := by
        rw [hz]
        simp only [Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
      rw [huk, hfk, hdot_u, hdot_full]
    obtain ⟨i₀, hi₀⟩ := hex0
    rw [hS_factor u]
    have hsp_dvd : (2 : ℤ) ^ spare ∣ ∑ s : Fin spare → F, chi (Lu u (inSpare s)) := by
      have h := chi_linear_sum ((Lu u).comp inSpare)
      have hcard : (Fintype.card (Fin spare → F) : ℤ) = (2 : ℤ) ^ spare := by
        simp [Fintype.card_pi, Fintype.card_fin, ZMod.card]
      change (2 : ℤ) ^ spare ∣ ∑ s : Fin spare → F, chi (((Lu u).comp inSpare) s)
      rw [h, hcard]
      split_ifs
      · exact dvd_refl _
      · exact dvd_zero _
    have hprod_dvd : (2 : ℤ) ^ (m + 1) ∣
        ∏ i : Fin m, ∑ z : Fin (w i) → F,
          chi (Lu u (inBlock i z) + cu u i * (if z = center i then (1 : F) else 0)) := by
      refine prod_dvd_extra_two _ i₀ ?_ ?_
      · intro i
        exact block_sum_two_dvd (hw i) ((Lu u).comp (inBlock i)) (center i) (cu u i)
      · have h0 := block_sum_zero (hw i₀) ((Lu u).comp (inBlock i₀))
        simpa only [hi₀, zero_mul, add_zero, LinearMap.comp_apply] using h0
    have hmul := mul_dvd_mul hsp_dvd hprod_dvd
    have hpow : (2 : ℤ) ^ spare * (2 : ℤ) ^ (m + 1) = (2 : ℤ) ^ (m + spare + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rwa [hpow] at hmul
  obtain ⟨aOdd, haOdd, hSfull_eq⟩ := hS_full
  have hsplit : (2 : ℤ) ^ r * signed y =
      chi (∑ k : Fin r, uFull k * (y k + offset k)) * S uFull +
      ∑ u ∈ Finset.univ.erase uFull, chi (∑ k : Fin r, u k * (y k + offset k)) * S u := by
    rw [h2r]
    exact (Finset.add_sum_erase Finset.univ
      (fun u => chi (∑ k : Fin r, u k * (y k + offset k)) * S u) (Finset.mem_univ uFull)).symm
  have hrest_dvd : (2 : ℤ) ^ (m + spare + 1) ∣
      ∑ u ∈ Finset.univ.erase uFull, chi (∑ k : Fin r, u k * (y k + offset k)) * S u := by
    refine Finset.dvd_sum fun u hu => ?_
    exact dvd_mul_of_dvd_right (hS_other u (Finset.ne_of_mem_erase hu)) _
  rcases hrest_dvd with ⟨qRest, hqRest⟩
  let cSign : ℤ := chi (∑ k : Fin r, uFull k * (y k + offset k))
  have hcSign_odd : ¬ ((2 : ℤ) ∣ cSign * aOdd) := by
    have hsq : cSign = 1 ∨ cSign = -1 := by
      simp only [cSign, chi]
      split_ifs
      · left; rfl
      · right; rfl
    rcases hsq with h1 | h1 <;> rw [h1]
    · simpa using haOdd
    · simpa using haOdd
  have htot_eq : (2 : ℤ) ^ r * signed y = (2 : ℤ) ^ (m + spare) * (cSign * aOdd + 2 * qRest) := by
    rw [hsplit, hSfull_eq, hqRest, pow_succ]
    ring
  have htot_odd : ¬ ((2 : ℤ) ∣ (cSign * aOdd + 2 * qRest)) := by
    intro hdvd
    have h2q : (2 : ℤ) ∣ 2 * qRest := dvd_mul_right 2 qRest
    have := dvd_sub hdvd h2q
    simp only [add_sub_cancel_right] at this
    exact hcSign_odd this
  have hvr : m + spare = r + v := by
    change m + spare = r + (m + spare - r)
    omega
  have hsig_eq : signed y = (2 : ℤ) ^ v * (cSign * aOdd + 2 * qRest) := by
    have hpos : (2 : ℤ) ^ r ≠ 0 := by positivity
    rw [hvr, pow_add, mul_assoc] at htot_eq
    exact mul_left_cancel₀ hpos htot_eq
  rw [hsig_eq]
  exact two_pow_dvd_and_not_next_of_odd_mul htot_odd

lemma cell_sum_divisibility {E : Type*} [AddCommGroup E] [Module F E] [Fintype E]
    (D depth : Nat) (hcard : Fintype.card E = 2 ^ D)
    (ℓ : Fin depth → (E →ₗ[F] F)) (t : Fin depth → F) (φ : E →ₗ[F] F) :
    (2 : ℤ) ^ (D - depth) ∣
      ∑ x : E, if (∀ j : Fin depth, ℓ j x = t j) then chi (φ x) else 0 := by
  by_cases hle : depth ≤ D
  · have h2d : (2 : ℤ) ^ depth *
        (∑ x : E, if (∀ j : Fin depth, ℓ j x = t j) then chi (φ x) else 0) =
        ∑ u : Fin depth → F, chi (∑ j : Fin depth, u j * t j) *
          ∑ x : E, chi (φ x + ∑ j : Fin depth, u j * ℓ j x) := by
      have h1 : (2 : ℤ) ^ depth *
          (∑ x : E, if (∀ j : Fin depth, ℓ j x = t j) then chi (φ x) else 0) =
          ∑ x : E, chi (φ x) * (if (fun j : Fin depth => ℓ j x + t j) = 0 then (2 : ℤ) ^ depth else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hiff : (fun j : Fin depth => ℓ j x + t j) = 0 ↔ ∀ j : Fin depth, ℓ j x = t j := by
          constructor
          · intro h0 j
            have hj := congrFun h0 j
            have h2 := congrArg (fun a => a + t j) hj
            simpa only [Pi.zero_apply, add_assoc, z2_add_self, add_zero, zero_add] using h2
          · intro hall
            ext j
            rw [hall j]
            exact z2_add_self (t j)
        simp only [hiff]
        split_ifs <;> ring
      rw [h1]
      have h2 : (∑ x : E, chi (φ x) *
          (if (fun j : Fin depth => ℓ j x + t j) = 0 then (2 : ℤ) ^ depth else 0)) =
          ∑ x : E, ∑ u : Fin depth → F,
            chi (φ x) * chi (∑ j : Fin depth, u j * (ℓ j x + t j)) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← sum_chi_dot (fun j => ℓ j x + t j), Finset.mul_sum]
      rw [h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← chi_add, ← chi_add]
      congr 1
      have hsum : (∑ j : Fin depth, u j * (ℓ j x + t j)) =
          (∑ j : Fin depth, u j * ℓ j x) + (∑ j : Fin depth, u j * t j) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => mul_add _ _ _
      rw [hsum]
      ring
    have hD_dvd : (2 : ℤ) ^ D ∣
        ∑ u : Fin depth → F, chi (∑ j : Fin depth, u j * t j) *
          ∑ x : E, chi (φ x + ∑ j : Fin depth, u j * ℓ j x) := by
      refine Finset.dvd_sum fun u _ => dvd_mul_of_dvd_right ?_ _
      let ψ : E →ₗ[F] F :=
        { toFun := fun x => φ x + ∑ j : Fin depth, u j * ℓ j x
          map_add' := fun x y => by
            simp only [map_add, mul_add, Finset.sum_add_distrib]
            ring
          map_smul' := fun c x => by
            simp only [map_smul, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum]
            congr 1
            refine Finset.sum_congr rfl fun j _ => by ring }
      have h := chi_linear_sum ψ
      change (2 : ℤ) ^ D ∣ ∑ x : E, chi (ψ x)
      rw [h, hcard]
      split_ifs
      · simp
      · exact dvd_zero _
    rw [← h2d] at hD_dvd
    have hDeq : D = depth + (D - depth) := by omega
    rw [hDeq, pow_add] at hD_dvd
    have hpos : (2 : ℤ) ^ depth ≠ 0 := by positivity
    rcases hD_dvd with ⟨q, hq⟩
    exact ⟨q, mul_left_cancel₀ hpos (by linarith)⟩
  · have h0 : D - depth = 0 := by omega
    rw [h0, pow_zero]
    exact one_dvd _

lemma lower_bound (m r spare depth : Nat) (w : Fin m → Nat)
    (hw : ∀ i, 2 ≤ w i)
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) (full : (Fin r → F) →ₗ[F] F)
    (center : (i : Fin m) → Fin (w i) → F)
    (tilt : (((i : Fin m) → Fin (w i) → F) × (Fin spare → F)) →ₗ[F] (Fin r → F))
    (offset : Fin r → F)
    (hrle : r ≤ m)
    (hnotdiv : ¬ ((2 : ℤ) ^ ((m + spare - r) + 1) ∣
      ∑ x : ((i : Fin m) → Fin (w i) → F) × (Fin spare → F),
        if offset + tilt x + A (fun i => if x.1 i = center i then 1 else 0) = 0 then
          (if full (tilt x) = 0 then (1 : ℤ) else -1)
        else 0))
    (ask : (j : Fin depth) → (Fin j.val → F) →
      ((((i : Fin m) → Fin (w i) → F) × (Fin spare → F)) →ₗ[F] F))
    (answers : (((i : Fin m) → Fin (w i) → F) × (Fin spare → F)) → Fin depth → F)
    (decode : (Fin depth → F) → Fin r → F)
    (hans : ∀ x j, answers x j =
      ask j (fun u => answers x ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x)
    (hdec : ∀ x, decode (answers x) =
      offset + tilt x + A (fun i => if x.1 i = center i then 1 else 0)) :
    (∑ i : Fin m, (w i - 1)) + r ≤ depth := by
  let V := ((i : Fin m) → Fin (w i) → F) × (Fin spare → F)
  let D : Nat := (∑ i : Fin m, w i) + spare
  have hcardV : Fintype.card V = 2 ^ D := by
    simp only [V, D, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card,
      Finset.prod_const, Finset.card_univ, Finset.prod_pow_eq_pow_sum, pow_add]
  have hcell_iff : ∀ (t : Fin depth → F) (x : V),
      answers x = t ↔ ∀ j : Fin depth,
        ask j (fun u => t ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x = t j := by
    intro t x
    constructor
    · intro hxt j
      subst hxt
      exact (hans x j).symm
    · intro hall
      ext j
      obtain ⟨k, hk⟩ := j
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        rw [hans x ⟨k, hk⟩]
        have hpref : (fun u : Fin k => answers x ⟨u.val, Nat.lt_trans u.isLt hk⟩) =
            (fun u : Fin k => t ⟨u.val, Nat.lt_trans u.isLt hk⟩) := by
          ext u
          exact ih u.val u.isLt (Nat.lt_trans u.isLt hk)
        rw [hpref]
        exact hall ⟨k, hk⟩
  have hpart :
      (∑ x : V,
        if offset + tilt x + A (fun i => if x.1 i = center i then 1 else 0) = 0 then
          (if full (tilt x) = 0 then (1 : ℤ) else -1)
        else 0) =
      ∑ t : Fin depth → F,
        if decode t = 0 then
          ∑ x : V, if (∀ j : Fin depth,
            ask j (fun u => t ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x = t j) then
              chi (full (tilt x))
            else 0
        else 0 := by
    have hstep1 :
        (∑ t : Fin depth → F,
          if decode t = 0 then
            ∑ x : V, if (∀ j : Fin depth,
              ask j (fun u => t ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x = t j) then
                chi (full (tilt x))
              else 0
          else 0) =
        ∑ t : Fin depth → F, ∑ x : V,
          if decode t = 0 ∧ answers x = t then chi (full (tilt x)) else 0 := by
      refine Finset.sum_congr rfl fun t _ => ?_
      by_cases ht : decode t = 0
      · simp only [ht, ↓reduceIte, true_and]
        refine Finset.sum_congr rfl fun x _ => by simp only [hcell_iff t x]
      · simp [ht]
    rw [hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single (answers x)]
    · simp only [and_true, hdec x, chi]
    · intro t _ hne
      simp [hne.symm]
    · intro habs
      exact False.elim (habs (Finset.mem_univ _))
  have hdvd : (2 : ℤ) ^ (D - depth) ∣
      ∑ x : V,
        if offset + tilt x + A (fun i => if x.1 i = center i then 1 else 0) = 0 then
          (if full (tilt x) = 0 then (1 : ℤ) else -1)
        else 0 := by
    rw [hpart]
    refine Finset.dvd_sum fun t _ => ?_
    split_ifs
    · exact cell_sum_divisibility D depth hcardV
        (fun j => ask j (fun u => t ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩)) t (full.comp tilt)
    · exact dvd_zero _
  have hle_v : D - depth ≤ m + spare - r := by
    by_contra hgt
    push Not at hgt
    have h1 : (m + spare - r) + 1 ≤ D - depth := by omega
    have hpow : (2 : ℤ) ^ ((m + spare - r) + 1) ∣ (2 : ℤ) ^ (D - depth) :=
      pow_dvd_pow 2 h1
    exact hnotdiv (dvd_trans hpow hdvd)
  have hsum_w : (∑ i : Fin m, (w i - 1)) + m = ∑ i : Fin m, w i := by
    have h1 : (∑ i : Fin m, (w i - 1)) + ∑ _i : Fin m, (1 : Nat) = ∑ i : Fin m, w i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have := hw i
      omega
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using h1
  omega

lemma upper_bound (m r spare depth : Nat) (w : Fin m → Nat)
    (hw : ∀ i, 2 ≤ w i)
    (A : (Fin m → F) →ₗ[F] (Fin r → F))
    (center : (i : Fin m) → Fin (w i) → F)
    (tilt : (((i : Fin m) → Fin (w i) → F) × (Fin spare → F)) →ₗ[F] (Fin r → F))
    (offset : Fin r → F)
    (hdepth : (∑ i : Fin m, (w i - 1)) + r ≤ depth) :
    let V := ((i : Fin m) → Fin (w i) → F) × (Fin spare → F)
    let answer := fun x : V => offset + tilt x +
      A (fun i => if x.1 i = center i then 1 else 0)
    ∃ (ask : (j : Fin depth) → (Fin j.val → F) → (V →ₗ[F] F))
      (answers : V → Fin depth → F) (decode : (Fin depth → F) → Fin r → F),
      (∀ (x : V) (j : Fin depth), answers x j =
        ask j (fun u => answers x ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x) ∧
      (∀ x : V, decode (answers x) = answer x) := by
  intro V answer
  let Q1 : Nat := ∑ i : Fin m, (w i - 1)
  have hcardSig : Fintype.card (Σ i : Fin m, Fin (w i - 1)) = Q1 := by
    simp [Q1, Fintype.card_sigma, Fintype.card_fin]
  let eIdx : (Σ i : Fin m, Fin (w i - 1)) ≃ Fin Q1 := Fintype.equivFinOfCardEq hcardSig
  let projCoord : (i : Fin m) → (k : Fin (w i)) → (V →ₗ[F] F) := fun i k =>
    { toFun := fun x => x.1 i k
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let projR : Fin r → (Fin r → F) →ₗ[F] F := fun t =>
    { toFun := fun y => y t
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let matchPred : (k : Nat) → Q1 ≤ k → (Fin k → F) → Fin m → Bool :=
    fun k hk prev i =>
      decide (∀ t : Fin (w i - 1),
        prev ⟨(eIdx ⟨i, t⟩).val, Nat.lt_of_lt_of_le (eIdx ⟨i, t⟩).isLt hk⟩ =
        center i ⟨t.val, by have := hw i; omega⟩)
  let dynGuard : (k : Nat) → Q1 ≤ k → (Fin k → F) → (V →ₗ[F] (Fin m → F)) :=
    fun k hk prev =>
      { toFun := fun x i =>
          if matchPred k hk prev i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0
        map_add' := fun x y => by
          ext i
          change (if matchPred k hk prev i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ +
              y.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0) =
            (if matchPred k hk prev i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0) +
            (if matchPred k hk prev i then y.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0)
          split_ifs <;> simp
        map_smul' := fun c x => by
          ext i
          change (if matchPred k hk prev i then c * x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0) =
            c * (if matchPred k hk prev i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0)
          split_ifs <;> simp }
  let dynLin : (k : Nat) → Q1 ≤ k → (Fin k → F) → (V →ₗ[F] (Fin r → F)) :=
    fun k hk prev => tilt + A.comp (dynGuard k hk prev)
  let ask : (j : Fin depth) → (Fin j.val → F) → (V →ₗ[F] F) := fun j prev =>
    if h1 : j.val < Q1 then
      let p := eIdx.symm ⟨j.val, h1⟩
      projCoord p.1 ⟨p.2.val, by have := hw p.1; omega⟩
    else if h2 : j.val - Q1 < r then
      (projR ⟨j.val - Q1, h2⟩).comp (dynLin j.val (by omega) prev)
    else
      0
  let matchX : V → Fin m → Bool := fun x i =>
    decide (∀ t : Fin (w i - 1),
      x.1 i ⟨t.val, by have := hw i; omega⟩ = center i ⟨t.val, by have := hw i; omega⟩)
  let answers : V → Fin depth → F := fun x j =>
    if h1 : j.val < Q1 then
      let p := eIdx.symm ⟨j.val, h1⟩
      x.1 p.1 ⟨p.2.val, by have := hw p.1; omega⟩
    else if h2 : j.val - Q1 < r then
      (tilt x + A (fun i =>
        if matchX x i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0)) ⟨j.val - Q1, h2⟩
    else
      0
  have hQ1le : Q1 ≤ depth := by omega
  let decode : (Fin depth → F) → Fin r → F := fun tr =>
    offset +
      A (fun i =>
        if matchPred depth hQ1le tr i then center i ⟨w i - 1, by have := hw i; omega⟩ + 1 else 0) +
      (fun t : Fin r => tr ⟨Q1 + t.val, by omega⟩)
  have hread : ∀ (x : V) (p : Σ i : Fin m, Fin (w i - 1)),
      answers x ⟨(eIdx p).val, Nat.lt_of_lt_of_le (eIdx p).isLt hQ1le⟩ =
      x.1 p.1 ⟨p.2.val, by have := hw p.1; omega⟩ := by
    intro x p
    have hlt : (eIdx p).val < Q1 := (eIdx p).isLt
    simp only [answers, hlt, ↓reduceDIte]
    let readP : (Σ i : Fin m, Fin (w i - 1)) → F :=
      fun q => x.1 q.1 ⟨q.2.val, by have := hw q.1; omega⟩
    exact congrArg readP (eIdx.symm_apply_apply p)
  have hmatch_eq : ∀ (x : V) (k : Nat) (hk : Q1 ≤ k) (hkd : k ≤ depth) (i : Fin m),
      matchPred k hk (fun u : Fin k => answers x ⟨u.val, Nat.lt_of_lt_of_le u.isLt hkd⟩) i =
        matchX x i := by
    intro x k hk hkd i
    simp only [matchPred, matchX]
    congr 1
    refine propext (forall_congr' fun t => ?_)
    have heq := hread x ⟨i, t⟩
    rw [heq]
  refine ⟨ask, answers, decode, ?_, ?_⟩
  · intro x j
    by_cases h1 : j.val < Q1
    · simp only [answers, ask, h1, ↓reduceDIte, projCoord, LinearMap.coe_mk, AddHom.coe_mk]
    · by_cases h2 : j.val - Q1 < r
      · conv_lhs => simp only [answers, h1, h2, ↓reduceDIte]
        simp only [ask, h1, h2, ↓reduceDIte, projR, dynLin, dynGuard, LinearMap.comp_apply,
          LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
        have harg :
            (fun i : Fin m =>
              if matchPred j.val (by omega)
                (fun u => answers x ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) i then
                  x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0) =
            (fun i : Fin m =>
              if matchX x i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0) := by
          ext i
          rw [hmatch_eq x j.val (by omega) (Nat.le_of_lt j.isLt) i]
        rw [harg]
      · simp only [answers, ask, h1, h2, ↓reduceDIte, LinearMap.zero_apply]
  · intro x
    have htr : (fun t : Fin r => answers x ⟨Q1 + t.val, by omega⟩) =
        tilt x + A (fun i =>
          if matchX x i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0) := by
      ext t
      have h1 : ¬ (Q1 + t.val < Q1) := by omega
      have h2 : Q1 + t.val - Q1 < r := by omega
      simp only [answers, h1, h2, ↓reduceDIte]
      have hsub : (⟨Q1 + t.val - Q1, h2⟩ : Fin r) = t := Fin.ext (by simp)
      rw [hsub]
    have hmatch_full : ∀ i : Fin m, matchPred depth hQ1le (answers x) i = matchX x i :=
      fun i => hmatch_eq x depth hQ1le le_rfl i
    have hvec : (fun i : Fin m =>
        (if matchX x i then center i ⟨w i - 1, by have := hw i; omega⟩ + 1 else 0) +
        (if matchX x i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0)) =
        (fun i : Fin m => if x.1 i = center i then (1 : F) else 0) := by
      ext i
      by_cases hm : matchX x i = true
      · simp only [hm, ↓reduceIte]
        have hall : ∀ t : Fin (w i - 1),
            x.1 i ⟨t.val, by have := hw i; omega⟩ = center i ⟨t.val, by have := hw i; omega⟩ := by
          simpa only [matchX, decide_eq_true_eq] using hm
        have hlast_iff : x.1 i = center i ↔
            x.1 i ⟨w i - 1, by have := hw i; omega⟩ = center i ⟨w i - 1, by have := hw i; omega⟩ := by
          constructor
          · intro h; rw [h]
          · intro hlast
            ext k
            by_cases hk : k.val < w i - 1
            · exact hall ⟨k.val, hk⟩
            · have heq : k = ⟨w i - 1, by have := hw i; omega⟩ := by
                refine Fin.ext ?_
                have := k.isLt
                simp only
                omega
              rw [heq]
              exact hlast
        simp only [hlast_iff]
        have hcheck : ∀ a b : F, b + 1 + a = if a = b then 1 else 0 := by
          intro a b
          fin_cases a <;> fin_cases b <;> rfl
        exact hcheck _ _
      · have hm' : matchX x i = false := Bool.eq_false_iff.mpr hm
        simp only [hm', Bool.false_eq_true, ↓reduceIte, add_zero]
        have hne : x.1 i ≠ center i := by
          intro heq
          apply hm
          simp only [matchX, decide_eq_true_eq]
          intro t
          rw [heq]
        simp [hne]
    simp only [decode, hmatch_full, htr, answer]
    rw [← add_assoc, add_assoc offset, add_comm (A _), ← add_assoc, add_assoc (offset + tilt x),
      ← map_add]
    change offset + tilt x + A (fun i =>
      (if matchX x i then center i ⟨w i - 1, by have := hw i; omega⟩ + 1 else 0) +
      (if matchX x i then x.1 i ⟨w i - 1, by have := hw i; omega⟩ else 0)) =
      offset + tilt x + A (fun i => if x.1 i = center i then 1 else 0)
    rw [hvec]

lemma main_proof (m r spare depth : Nat) (w : Fin m → Nat)
    (hm : 0 < m) (hr : 0 < r) (hw : ∀ i, 2 ≤ w i)
    (A : (Fin m → F) →ₗ[F] (Fin r → F)) (full : (Fin r → F) →ₗ[F] F)
    (hAsurj : Function.Surjective A) (hfull : ∀ z : Fin m → F, full (A z) = ∑ i : Fin m, z i)
    (center : (i : Fin m) → Fin (w i) → F)
    (tilt : (((i : Fin m) → Fin (w i) → F) × (Fin spare → F)) →ₗ[F] (Fin r → F))
    (offset : Fin r → F) :
    let V := ((i : Fin m) → Fin (w i) → F) × (Fin spare → F)
    let answer := fun x : V => offset + tilt x +
      A (fun i => if x.1 i = center i then 1 else 0)
    let signed := fun y : Fin r → F => ∑ x : V,
      if answer x = y then (if full (tilt x) = 0 then (1 : ℤ) else -1) else 0
    let v := m + spare - r
    let queries := (∑ i : Fin m, (w i - 1)) + r
    let computes := ∃ (ask : (j : Fin depth) → (Fin j.val → F) → (V →ₗ[F] F))
        (answers : V → Fin depth → F) (decode : (Fin depth → F) → Fin r → F),
      (∀ (x : V) (j : Fin depth), answers x j =
        ask j (fun u => answers x ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x) ∧
      (∀ x : V, decode (answers x) = answer x)
    And (∀ y : Fin r → F, ((2 : ℤ) ^ v ∣ signed y) ∧ ¬ ((2 : ℤ) ^ (v + 1) ∣ signed y))
      (Iff computes (queries ≤ depth)) := by
  intro V answer signed v queries computes
  obtain ⟨hrle, hdiv⟩ := signed_divisibility m r spare w hm hr hw A full hAsurj hfull center tilt offset
  refine ⟨hdiv, ?_⟩
  constructor
  · rintro ⟨ask, answers, decode, hans, hdec⟩
    exact lower_bound m r spare depth w hw A full center tilt offset hrle
      (hdiv 0).2 ask answers decode hans hdec
  · intro hle
    exact upper_bound m r spare depth w hw A center tilt offset hle

end PEqualNP.Outside.L_lib_805_aux

theorem PEqualNP.Outside.L_lib_805 : (∀ (m r spare depth : Nat) (w : Fin m → Nat), 0 < m → 0 < r → (∀ i, 2 ≤ w i) →
  let F := ZMod 2
  let V := ((i : Fin m) → Fin (w i) → F) × (Fin spare → F)
  let G := Fin m → F
  let R := Fin r → F
  ∀ (A : G →ₗ[F] R) (full : R →ₗ[F] F), Function.Surjective A →
    (∀ z : G, full (A z) = ∑ i : Fin m, z i) →
    ∀ (center : (i : Fin m) → Fin (w i) → F) (tilt : V →ₗ[F] R) (offset : R),
    let answer := fun x : V => offset + tilt x +
      A (fun i => if x.1 i = center i then 1 else 0)
    let signed := fun y : R => ∑ x : V,
      if answer x = y then (if full (tilt x) = 0 then (1 : ℤ) else -1) else 0
    let v := m + spare - r
    let queries := (∑ i : Fin m, (w i - 1)) + r
    let computes := ∃ (ask : (j : Fin depth) → (Fin j.val → F) → (V →ₗ[F] F))
        (answers : V → Fin depth → F) (decode : (Fin depth → F) → R),
      (∀ (x : V) (j : Fin depth), answers x j =
        ask j (fun u => answers x ⟨u.val, Nat.lt_trans u.isLt j.isLt⟩) x) ∧
      (∀ x : V, decode (answers x) = answer x)
    And (∀ y : R, ((2 : ℤ)^v ∣ signed y) ∧ ¬((2 : ℤ)^(v+1) ∣ signed y))
      (Iff computes (queries ≤ depth))) := by
  intro m r spare depth w hm hr hw F V G R A full hAsurj hfull center tilt offset
  exact PEqualNP.Outside.L_lib_805_aux.main_proof m r spare depth w hm hr hw A full hAsurj hfull center tilt offset
