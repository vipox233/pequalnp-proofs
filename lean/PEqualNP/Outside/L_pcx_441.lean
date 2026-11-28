import Mathlib

namespace PEqualNP.Outside.L_pcx_441_aux

namespace Bias441

private noncomputable def core (m j : ℕ) : ℚ := (2 : ℚ) ^ ((j : ℤ) - m)

private noncomputable def masked (c : ℚ) (d : ℕ) : ℚ := min 1 ((2 : ℚ)^d*c)

private noncomputable def unmasked (c : ℚ) (extra : Bool) (d : ℕ) : ℚ :=
  min 1 (((2 : ℚ)^d + if extra then 1 else 0)*c)

private theorem core_nonneg (m j : ℕ) : 0 ≤ core m j := by
  unfold core
  positivity

private theorem core_step (m j : ℕ) : core m j = 2 * core (m+1) j := by
  unfold core
  have he : (j : ℤ) - (m : ℤ) = ((j : ℤ) - ((m+1 : ℕ) : ℤ)) + 1 := by push_cast; omega
  rw [he, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  simp [mul_comm]

private theorem masked_step (c : ℚ) (d : ℕ) : masked (2*c) d = masked c (d+1) := by
  unfold masked
  congr 1
  rw [pow_succ]
  ring

private theorem masked_unmasked (c : ℚ) (hc : 0 ≤ c) (extra : Bool) (d : ℕ) :
    masked c d ≤ unmasked c extra d := by
  unfold masked unmasked
  apply min_le_min_left
  cases extra <;> simp <;> linarith

private theorem unmasked_next (c : ℚ) (hc : 0 ≤ c) (extra : Bool) (d : ℕ) :
    unmasked c extra d ≤ masked c (d+1) := by
  unfold unmasked masked
  apply min_le_min_left
  rw [pow_succ]
  have hd : (1 : ℚ) ≤ 2^d := one_le_pow₀ (by norm_num)
  cases extra <;> simp <;> nlinarith

private theorem split_upper (c : ℚ) (extra : Bool) (d : ℕ) :
    (unmasked (2*c) extra d + masked (2*c) d)/2 ≤ unmasked c extra (d+1) := by
  unfold unmasked masked
  apply le_min
  · linarith [min_le_left (1 : ℚ) (((2 : ℚ)^d + if extra then 1 else 0)*(2*c)),
      min_le_left (1 : ℚ) ((2 : ℚ)^d*(2*c))]
  · have h₁ := min_le_right (1 : ℚ) (((2 : ℚ)^d+ if extra then 1 else 0)*(2*c))
    have h₂ := min_le_right (1 : ℚ) ((2 : ℚ)^d*(2*c))
    rw [pow_succ]
    linarith

private theorem min_core (m j : ℕ) : min 1 (core m j) = 1/(2 : ℚ)^(m-j) := by
  unfold core
  by_cases h : m ≤ j
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, div_one, min_eq_left]
    apply one_le_zpow₀ (by norm_num : (1 : ℚ) ≤ 2)
    omega
  · have he : (j : ℤ) - m = -((m-j : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, one_div, min_eq_right]
    apply inv_le_one_of_one_le₀
    exact one_le_pow₀ (by norm_num)

private theorem pow_mul_core (m j d : ℕ) : (2 : ℚ)^d * core m j = core m (j+d) := by
  unfold core
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  push_cast
  omega

private theorem masked_formula (m e d : ℕ) :
    masked (core m ((e-1)/2)) d = 1/(2 : ℚ)^((m - min d m)-(e-1)/2) := by
  rw [masked, pow_mul_core, min_core]
  congr 2
  omega

private theorem masked_mono (c : ℚ) (hc : 0 ≤ c) (d : ℕ) :
    masked c d ≤ masked c (d+1) :=
  (show masked c d = unmasked c false d by simp [masked, unmasked]) ▸
    unmasked_next c hc false d

private theorem unmasked_mono (c : ℚ) (hc : 0 ≤ c) (extra : Bool) (d : ℕ) :
    unmasked c extra d ≤ unmasked c extra (d+1) :=
  (unmasked_next c hc extra d).trans (masked_unmasked c hc extra (d+1))

private theorem core_of_le (m j : ℕ) (h : m ≤ j) : 1 ≤ core m j := by
  apply one_le_zpow₀ (by norm_num : (1 : ℚ) ≤ 2)
  omega

private theorem core_le_one (m j : ℕ) (h : j ≤ m) : core m j ≤ 1 := by
  unfold core
  apply zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℚ) ≤ 2)
  omega

private theorem pow_core_sub (m j a : ℕ) (ha : a ≤ m) :
    (2 : ℚ)^a * core m j = core (m-a) j := by
  unfold core
  rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  congr 1
  omega

private theorem unmasked_formula (m d j : ℕ) (extra : Bool) :
    let a := min d m
    let b := if extra then 1 else 0
    unmasked (core m j) extra d =
      (1/(2 : ℚ)^((m-a)-(j+b)) + ((2 : ℚ)^a-1)*(1/(2 : ℚ)^((m-a)-j)))/(2 : ℚ)^a := by
  intro a b
  have ha : a ≤ m := min_le_right _ _
  have hb : b ≤ 1 := by cases extra <;> simp [b]
  have hb' : (if extra then (1 : ℚ) else 0) = b := by cases extra <;> simp [b]
  have hc : 0 ≤ core m j := core_nonneg _ _
  have hp : (2 : ℚ)^a ≠ 0 := by positivity
  rw [← min_core, ← min_core]
  by_cases hs : m ≤ j+d
  · have hs' : m-a ≤ j := by dsimp [a]; omega
    have hm : 1 ≤ (2 : ℚ)^d * core m j := by
      rw [pow_mul_core]
      exact core_of_le _ _ hs
    have hu : 1 ≤ ((2 : ℚ)^d + b)*core m j := by
      linarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) b) hc]
    rw [unmasked, hb', min_eq_left hu, min_eq_left (core_of_le _ _ hs'),
      min_eq_left (core_of_le (m-a) (j+b) (by omega))]
    field_simp
    ring
  · have had : a = d := min_eq_left (by omega)
    have hj : j+b ≤ m-a := by omega
    rw [min_eq_right (core_le_one _ _ hj), min_eq_right (core_le_one (m-a) j (by omega))]
    have he : core (m-a) j = (2 : ℚ)^a * core m j := (pow_core_sub _ _ _ ha).symm
    have hf : core (m-a) (j+b) = (1+(b : ℚ))*core (m-a) j := by
      rw [← pow_mul_core]
      have hcases : b = 0 ∨ b = 1 := by omega
      rcases hcases with hh | hh
      · simp [hh]
      · simp [hh, two_mul]; ring
    have hg : ((2 : ℚ)^d + b)*core m j ≤ 1 := by
      have hh : ((2 : ℚ)^d + b)*core m j ≤ (1+(b : ℚ))*core (m-a) j := by
        have hpd : (1 : ℚ) ≤ 2^d := one_le_pow₀ (by norm_num)
        rw [he, had]
        have hb0 : 0 ≤ (b : ℚ) * core m j := mul_nonneg (Nat.cast_nonneg _) hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hpd) hb0]
      exact hh.trans (hf ▸ core_le_one _ _ hj)
    rw [unmasked, hb', min_eq_right hg, hf, he, had]
    field_simp
    ring

private theorem posted_formula (m d e : ℕ) (he : 0 < e) :
    let a := min d m
    let r := m-a
    unmasked (core m ((e-1)/2)) (e % 2 == 0) d =
      (1/(2 : ℚ)^(r-e/2) + ((2 : ℚ)^a-1) * (1/(2 : ℚ)^(r-(e-1)/2)))/(2 : ℚ)^a := by
  dsimp
  rw [unmasked_formula]
  have hdiv : (e-1)/2 + (if e % 2 == 0 then 1 else 0) = e/2 := by
    by_cases hb : e % 2 = 0
    · simp [hb]; omega
    · simp [hb]; omega
  rw [hdiv]

private theorem split_exact (m j d : ℕ) (extra : Bool) :
    (unmasked (core m j) extra d + masked (core m j) d)/2 =
      unmasked (core (m+1) j) extra (d+1) := by
  let c := core (m+1) j
  have hcc : core m j = 2*c := core_step _ _
  have hc : 0 ≤ core m j := core_nonneg _ _
  have hc' : 0 ≤ c := core_nonneg _ _
  have hpow : (1 : ℚ) ≤ 2^d := one_le_pow₀ (by norm_num)
  by_cases hm : m ≤ j+d
  · have hx : 1 ≤ (2 : ℚ)^d * core m j := by
      rw [pow_mul_core]
      exact core_of_le _ _ hm
    have hmask : masked (core m j) d = 1 := min_eq_left hx
    have h₁ : unmasked (core m j) extra d = 1 :=
      le_antisymm (min_le_left _ _) (hmask ▸ masked_unmasked _ hc extra d)
    have hmask' : masked c (d+1) = 1 := by rwa [← masked_step, ← hcc]
    have h₂ : unmasked c extra (d+1) = 1 :=
      le_antisymm (min_le_left _ _) (hmask' ▸ masked_unmasked _ hc' extra (d+1))
    rw [h₁, hmask, h₂]
    norm_num
  · have hx : 2*((2 : ℚ)^d * core m j) ≤ 1 := by
      have hr : 2*((2 : ℚ)^d * core m j) = (2 : ℚ)^(d+1)*core m j := by rw [pow_succ]; ring
      rw [hr, pow_mul_core]
      exact core_le_one _ _ (by omega)
    have he : (if extra then (1 : ℚ) else 0) ≤ 1 := by cases extra <;> simp
    have hy : ((2 : ℚ)^d + if extra then 1 else 0)*core m j ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (show (2 : ℚ)^d + (if extra then 1 else 0) ≤ 2*2^d by linarith) hc
      linarith
    have hz : ((2 : ℚ)^(d+1) + if extra then 1 else 0)*c ≤ 1 := by
      rw [pow_succ]
      have hnn : 0 ≤ (if extra then (1 : ℚ) else 0)*c := by cases extra <;> simp [hc']
      rw [hcc] at hy
      linarith
    have hw : (2 : ℚ)^d * core m j ≤ 1 := by linarith
    change _ = unmasked c extra (d+1)
    rw [unmasked, masked, unmasked, min_eq_right hy, min_eq_right hw, min_eq_right hz, hcc, pow_succ]
    ring

end Bias441


open scoped BigOperators

namespace Query441

private abbrev K := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module K V]

private noncomputable def score [Fintype V] (q s : V → K) : ℚ :=
  (∑ x : V, if s x = q x then (1 : ℚ) else -1) / Fintype.card V

private noncomputable def split (L : V →ₗ[K] K) (u : V) (hu : L u = 1) : V ≃ K × L.ker where
  toFun x := (L x, ⟨x - L x • u, by simp [hu]⟩)
  invFun z := z.2.val + z.1 • u
  left_inv x := sub_add_cancel _ _
  right_inv := by
    rintro ⟨t,x⟩
    have hx : L x.val = 0 := x.property
    have ht : L (x.val + t • u) = t := by simp [hx, hu]
    exact Prod.ext ht (Subtype.ext (by change (x.val + t • u) - L (x.val + t • u) • u = x.val; rw [ht]; exact add_sub_cancel_right _ _))

private theorem score_split [Fintype V] (L : V →ₗ[K] K) [Fintype L.ker]
    (u : V) (hu : L u = 1) (q s : V → K) :
    score q s = (score (fun x : L.ker => q x.val) (fun x => s x.val) +
      score (fun x : L.ker => q (x.val+u)) (fun x => s (x.val+u)))/2 := by
  classical
  unfold score
  have hCard := Fintype.card_congr (split L u hu)
  rw [Fintype.card_prod, ZMod.card] at hCard
  rw [hCard, Fintype.sum_equiv (split L u hu) _
    (fun z => if s (z.2.val + z.1 • u) = q (z.2.val + z.1 • u) then (1 : ℚ) else -1) (by
      intro x
      change (if s x = q x then (1 : ℚ) else -1) = (if s ((x - L x • u) + L x • u) = q ((x - L x • u) + L x • u) then (1 : ℚ) else -1)
      rw [sub_add_cancel]), Fintype.sum_prod_type]
  change (∑ t : Fin 2, ∑ x : L.ker,
    if s (x.val + (show K from t) • u) = q (x.val + (show K from t) • u) then (1 : ℚ) else -1) / _ = _
  rw [Fin.sum_univ_two]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  change ((∑ x : L.ker, if s (x.val + (0 : K) • u) = q (x.val + (0 : K) • u) then (1 : ℚ) else -1) +
    (∑ x : L.ker, if s (x.val + (1 : K) • u) = q (x.val + (1 : K) • u) then (1 : ℚ) else -1)) / _ = _
  simp only [zero_smul, add_zero, one_smul]
  ring

private def tail {d : ℕ} (L : V →ₗ[K] (Fin (d+1) → K)) : V →ₗ[K] (Fin d → K) where
  toFun x i := L x i.succ
  map_add' x y := congrArg (fun (f : Fin (d+1) → K) (i : Fin d) => f i.succ) (L.map_add x y)
  map_smul' c x := congrArg (fun (f : Fin (d+1) → K) (i : Fin d) => f i.succ) (L.map_smul c x)

private def head {d : ℕ} (L : V →ₗ[K] (Fin (d+1) → K)) : V →ₗ[K] K :=
  (LinearMap.proj 0).comp L

private def restrictTranscript {d : ℕ} (P : V →ₗ[K] (Fin (d+1) → K)) (u : V) (t : K)
    (a : Fin d → K) : Fin (d+1) → K := Fin.cons t (a + tail P u)

private theorem restrictTranscript_eq {d : ℕ} (P : V →ₗ[K] (Fin (d+1) → K))
    (u x : V) (h : P (x+u) 0 = P u 0) :
    restrictTranscript P u (P u 0) (tail P x) = P (x+u) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h.symm
  · rw [restrictTranscript, Fin.cons_succ, map_add]
    rfl

private theorem restrict_strategy {d e : ℕ} (P : V →ₗ[K] (Fin (d+1) → K))
    (N : (Fin (d+1) → K) → V →ₗ[K] (Fin e → K))
    (O : (Fin (d+1) → K) → (Fin e → K) → K) (u : V) (U : Submodule K V)
    (h : ∀ x : U, head P x.val = 0) :
    ∃ (P' : U →ₗ[K] (Fin d → K)) (N' : (Fin d → K) → U →ₗ[K] (Fin e → K))
      (O' : (Fin d → K) → (Fin e → K) → K), ∀ x : U,
    O' (P' x) (N' (P' x) x) = O (P (x.val+u)) (N (P (x.val+u)) (x.val+u)) := by
  let label := restrictTranscript P u (P u 0)
  refine ⟨(tail P).comp U.subtype, fun a => (N (label a)).comp U.subtype,
    fun a v => O (label a) (v + N (label a) u), ?_⟩
  intro x
  have hlab : label (tail P x.val) = P (x.val+u) := by
    apply restrictTranscript_eq
    rw [map_add]
    change head P x.val + P u 0 = P u 0
    rw [h x, zero_add]
  change O (label (tail P x.val)) (N (label (tail P x.val)) x.val + N (label (tail P x.val)) u) = _
  rw [hlab, (N (P (x.val+u))).map_add]

private def projection (L : V →ₗ[K] K) (u : V) (hu : L u = 1) : V →ₗ[K] L.ker :=
  (LinearMap.id - L.smulRight u).codRestrict _ (fun x => by
    change L (x - L x • u) = 0
    simp [hu])

private def combineFirst {d : ℕ} (L : V →ₗ[K] K) (u : V) (hu : L u = 1)
    (P : L.ker →ₗ[K] (Fin d → K)) : V →ₗ[K] (Fin (d+1) → K) where
  toFun x := Fin.cons (L x) (P (projection L u hu x))
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

private theorem combineFirst_apply {d : ℕ} (L : V →ₗ[K] K) (u : V) (hu : L u = 1)
    (P : L.ker →ₗ[K] (Fin d → K)) (t : K) (x : L.ker) :
    combineFirst L u hu P (x.val+t • u) = Fin.cons t (P x) := by
  have hx : L x.val = 0 := x.property
  have ht : L (x.val+t • u) = t := by simp [hx, hu]
  have hp : projection L u hu (x.val+t • u) = x := by
    apply Subtype.ext
    change x.val + t • u - L (x.val+t • u) • u = x.val
    rw [ht, add_sub_cancel_right]
  change Fin.cons (α := fun _ : Fin (d+1) => K) (L (x.val+t • u))
    (P (projection L u hu (x.val+t • u))) = _
  rw [ht, hp]

private theorem combine_strategy {d e : ℕ} (L : V →ₗ[K] K) (u : V) (hu : L u = 1)
    (P : L.ker →ₗ[K] (Fin d → K))
    (N : K → (Fin d → K) → L.ker →ₗ[K] (Fin e → K))
    (O : K → (Fin d → K) → (Fin e → K) → K) :
    ∃ (N' : (Fin (d+1) → K) → V →ₗ[K] (Fin e → K))
      (O' : (Fin (d+1) → K) → (Fin e → K) → K), ∀ t : K, ∀ x : L.ker,
      let y := x.val+t • u
      O' (combineFirst L u hu P y) (N' (combineFirst L u hu P y) y) = O t (P x) (N t (P x) x) := by
  refine ⟨fun a => (N (a 0) (Fin.tail a)).comp (projection L u hu),
    fun a b => O (a 0) (Fin.tail a) b, ?_⟩
  intro t x
  dsimp
  rw [combineFirst_apply]
  have hx : L x.val = 0 := x.property
  have ht : L (x.val+t • u) = t := by simp [hx, hu]
  have hp : projection L u hu (x.val+t • u) = x := by
    apply Subtype.ext
    change x.val + t • u - L (x.val+t • u) • u = x.val
    rw [ht, add_sub_cancel_right]
  simp [hp]

end Query441


/- Symplectic coordinate helpers ported from lean/PEqualNP/Outside/L_meta_29947.lean
   at 84686e3276044e3cadda1c4453d05f6445313e0f, with local namespace names. -/
namespace Phase441SymplecticStep

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def perpendicular (B : LinearMap.BilinForm K V) (e f : V) : Submodule K V :=
  LinearMap.ker (B e) ⊓ LinearMap.ker (B f)

private def remainder (B : LinearMap.BilinForm K V) (e f : V) : V →ₗ[K] V :=
  LinearMap.id - (B f).smulRight e - (B e).smulRight f

private theorem reconstructed (B : LinearMap.BilinForm K V) (e f v : V) :
    B f v • e + B e v • f + remainder B e f v = v := by
  change B f v • e + B e v • f + (v - B f v • e - B e v • f) = v
  abel

private theorem remainder_perpendicular (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) (v : V) :
    remainder B e f v ∈ perpendicular B e f := by
  change B e (v - B f v • e - B e v • f) = 0 ∧
    B f (v - B f v • e - B e v • f) = 0
  simp [map_sub, map_smul, smul_eq_mul, alt, ef, fe]

private theorem split_pair (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) (v w : V) :
    B v w =
      B f v * B e w + B e v * B f w +
        B (remainder B e f v) (remainder B e f w) := by
  have fe : B f e = 1 := (sym _ _).trans ef
  have hv := remainder_perpendicular B e f alt ef fe v
  have hw := remainder_perpendicular B e f alt ef fe w
  change B e (remainder B e f v) = 0 ∧ B f (remainder B e f v) = 0 at hv
  change B e (remainder B e f w) = 0 ∧ B f (remainder B e f w) = 0 at hw
  have he : B (remainder B e f v) e = 0 := (sym _ _).trans hv.1
  have hf : B (remainder B e f v) f = 0 := (sym _ _).trans hv.2
  calc
    B v w = B (B f v • e + B e v • f + remainder B e f v)
             (B f w • e + B e w • f + remainder B e f w) := by
               simp only [reconstructed]
    _ = _ := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, alt, ef, fe, hw.1, hw.2, he, hf] <;> ring

private def coordinates (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) :
    V ≃ₗ[K] (K × K × perpendicular B e f) where
  toFun v := ⟨B f v, B e v, ⟨remainder B e f v, remainder_perpendicular B e f alt ef fe v⟩⟩
  invFun x := x.1 • e + x.2.1 • f + x.2.2.val
  left_inv := reconstructed B e f
  right_inv := by
    rintro ⟨a,b,w⟩
    have hw := w.property
    change B e w.val = 0 ∧ B f w.val = 0 at hw
    have ha : B f (a • e + b • f + w.val) = a := by
      simp [map_add, map_smul, smul_eq_mul, alt, fe, hw.2]
    have hb : B e (a • e + b • f + w.val) = b := by
      simp [map_add, map_smul, smul_eq_mul, alt, ef, hw.1]
    refine Prod.ext ha (Prod.ext hb (Subtype.ext ?_))
    change a • e + b • f + w.val -
      B f (a • e + b • f + w.val) • e - B e (a • e + b • f + w.val) • f = w.val
    rw [ha,hb]
    abel
  map_add' x y := Prod.ext (map_add (B f) x y)
    (Prod.ext (map_add (B e) x y) (Subtype.ext (map_add (remainder B e f) x y)))
  map_smul' c x := Prod.ext (map_smul (B f) c x)
    (Prod.ext (map_smul (B e) c x) (Subtype.ext (map_smul (remainder B e f) c x)))

private theorem dimension_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) [Module.Finite K V] :
    Module.finrank K V = 2 + Module.finrank K (perpendicular B e f) := by
  rw [(coordinates B e f alt ef fe).finrank_eq, Module.finrank_prod, Module.finrank_prod]
  simp <;> omega

private def radicalEquiv (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) :
    LinearMap.ker B ≃ₗ[K] LinearMap.ker (B.restrict (perpendicular B e f)) where
  toFun w := by
    have van (z : V) : B w.val z = 0 := by
      exact congrArg (fun f : V →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have mem : w.val ∈ perpendicular B e f := by
      change B e w.val = 0 ∧ B f w.val = 0
      exact ⟨(sym _ _).trans (van e), (sym _ _).trans (van f)⟩
    refine ⟨⟨w.val,mem⟩,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    exact van z.val
  invFun w := by
    have fe := (sym f e).trans ef
    have van (z : perpendicular B e f) : B w.val.val z.val = 0 := by
      exact congrArg (fun f : perpendicular B e f →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have h := w.val.property
    change B e w.val.val = 0 ∧ B f w.val.val = 0 at h
    have fixed : remainder B e f w.val.val = w.val.val := by
      change w.val.val - B f w.val.val • e - B e w.val.val • f = w.val.val
      simp [h.1,h.2]
    refine ⟨w.val.val,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    have split := split_pair B e f alt sym ef w.val.val z
    have hz := van ⟨remainder B e f z, remainder_perpendicular B e f alt ef fe z⟩
    simpa [h.1,h.2,fixed] using split.trans (by simpa [h.1,h.2,fixed] using hz)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

private theorem rank_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1)
    [Module.Finite K V] :
    Module.finrank K (LinearMap.range B) =
      2 + Module.finrank K (LinearMap.range (B.restrict (perpendicular B e f))) := by
  have ambient := B.finrank_range_add_finrank_ker
  have residual := (B.restrict (perpendicular B e f)).finrank_range_add_finrank_ker
  have ker := (radicalEquiv B e f alt sym ef).finrank_eq
  have dim := dimension_step B e f alt ef ((sym _ _).trans ef)
  omega

end Phase441SymplecticStep

namespace Phase441SymplecticCoordinates
open Phase441SymplecticStep

universe u v
variable {K : Type u} [Field K]

private abbrev Coordinates {V : Type v} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (r : ℕ) :=
  { p : (Fin r → V →ₗ[K] K) × (Fin r → V →ₗ[K] K) //
    (∀ x y, B x y = ∑ i : Fin r, (p.1 i x * p.2 i y + p.2 i x * p.1 i y)) ∧
      Function.Surjective (fun x : V => (fun i => p.1 i x, fun i => p.2 i x)) }

variable {V : Type v} [AddCommGroup V] [Module K V] {B : LinearMap.BilinForm K V} {r : ℕ}

private abbrev Coordinates.left (D : Coordinates B r) := D.val.1
private abbrev Coordinates.right (D : Coordinates B r) := D.val.2
private theorem Coordinates.product (D : Coordinates B r) (x y : V) :
    B x y = ∑ i : Fin r, (D.left i x * D.right i y + D.right i x * D.left i y) := D.property.1 x y
private theorem Coordinates.independent (D : Coordinates B r) :
    Function.Surjective (fun x : V => (fun i => D.left i x, fun i => D.right i x)) := D.property.2

omit [AddCommGroup V] [Module K V] in

private theorem normalForm (r : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V],
      ∀ B : LinearMap.BilinForm K V,
        (∀ x, B x x = 0) → (∀ x y, B x y = B y x) →
          Module.finrank K (LinearMap.range B) = 2*r → Nonempty (Coordinates B r) := by
  induction r with
  | zero =>
    intro V _ _ _ B _ _ rank
    have zr : Module.finrank K (LinearMap.range B) = 0 := by simpa using rank
    have bottom : LinearMap.range B = ⊥ := Submodule.finrank_eq_zero.mp zr
    have van (x y : V) : B x y = 0 := by
      have mem := LinearMap.mem_range_self B x
      rw [bottom] at mem
      have eq : B x = 0 := by simpa using mem
      exact congrArg (fun f : V →ₗ[K] K => f y) eq
    refine ⟨⟨(Fin.elim0, Fin.elim0), ?_, ?_⟩⟩
    · intro x y
      simpa using van x y
    · intro z
      refine ⟨0,Prod.ext ?_ ?_⟩
      · funext i
        exact i.elim0
      · funext i
        exact i.elim0
  | succ r ih =>
    intro V _ _ _ B alt sym rank
    have nn : B ≠ 0 := by
      intro h
      have z : Module.finrank K (LinearMap.range B) = 0 :=
        Submodule.finrank_eq_zero.mpr (LinearMap.range_eq_bot.mpr h)
      omega
    obtain ⟨e,f0,notZero⟩ : ∃ e f, B e f ≠ 0 := by
      by_contra! h
      apply nn
      ext x y
      exact h x y
    let f : V := (B e f0)⁻¹ • f0
    have one : B e f = 1 := by
      simp [f, map_smul, smul_eq_mul, notZero]
    have other : B f e = 1 := (sym _ _).trans one
    let W := perpendicular B e f
    let pr : V →ₗ[K] W := (remainder B e f).codRestrict W
      (remainder_perpendicular B e f alt one other)
    have smaller : Module.finrank K (LinearMap.range (B.restrict W)) = 2*r := by
      have step := rank_step B e f alt sym one
      change Module.finrank K (LinearMap.range B) =
        2 + Module.finrank K (LinearMap.range (B.restrict W)) at step
      omega
    obtain ⟨prev⟩ := ih (B.restrict W) (fun x => alt x.val)
      (fun x y => sym x.val y.val) smaller
    refine ⟨⟨(Fin.cons (B f) (fun i => (prev.left i).comp pr),
      Fin.cons (B e) (fun i => (prev.right i).comp pr)), ?_, ?_⟩⟩
    · intro x y
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply]
      have form := split_pair B e f alt sym one x y
      change B x y = B f x * B e y + B e x * B f y + B.restrict W (pr x) (pr y) at form
      exact form.trans (congrArg (fun t => B f x * B e y + B e x * B f y + t) (prev.product (pr x) (pr y)))
    · rintro ⟨a,b⟩
      obtain ⟨w,hw⟩ := prev.independent (Fin.tail a, Fin.tail b)
      let uv := coordinates B e f alt one other
      let x := uv.symm (a 0,b 0,w)
      have h := uv.apply_symm_apply (a 0,b 0,w)
      have hxL : B f x = a 0 := congrArg Prod.fst h
      have hxR : B e x = b 0 := congrArg (fun p : K × K × W => p.2.1) h
      have hpr : pr x = w := congrArg (fun p : K × K × W => p.2.2) h
      refine ⟨x,Prod.ext ?_ ?_⟩
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxL
        · change prev.left j (pr x) = a j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.fst hw) j
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxR
        · change prev.right j (pr x) = b j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.snd hw) j

end Phase441SymplecticCoordinates

namespace Phase441QuadraticCoordinates
open Phase441SymplecticCoordinates

private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {B : LinearMap.BilinForm F V} {r : ℕ}

private def quadraticPart (D : Coordinates B r) (x : V) : F :=
  ∑ i : Fin r, D.left i x * D.right i x

private theorem crossTerm : ∀ a b c d : F,
    (a+c)*(b+d)+a*b+c*d = a*d+b*c := by
  decide +kernel

private theorem quadratic_polar (D : Coordinates B r) (x y : V) :
    quadraticPart D (x+y) + quadraticPart D x + quadraticPart D y = B x y := by
  rw [D.product]
  simp only [quadraticPart, ← Finset.sum_add_distrib, map_add]
  exact Finset.sum_congr rfl (fun i _ => crossTerm _ _ _ _)

private theorem scalarBalance : ∀ a b c z p q w d : F,
    c+a+b+z=d → w+p+q=d → c+z+w=(a+z+p)+(b+z+q) := by
  decide +kernel

private theorem cancelConstant : ∀ a b c : F, a=b+(a+b+c)+c := by
  decide +kernel

private theorem self_cancel : ∀ a : F, a+a=0 := by decide +kernel

private def affineLinear (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) : V →ₗ[F] F where
  toFun x := q x+q 0+quadraticPart D x
  map_add' x y := scalarBalance _ _ _ _ _ _ _ _ (polar x y) (quadratic_polar D x y)
  map_smul' c x := by
    have bits : ∀ c : F, c = 0 ∨ c = 1 := by decide +kernel
    rcases bits c with rfl | rfl
    · change q ((0 : F) • x) + q 0 + quadraticPart D ((0 : F) • x) =
        (0 : F) * (q x + q 0 + quadraticPart D x)
      simp [zero_smul, quadraticPart, self_cancel]
    · change q ((1 : F) • x) + q 0 + quadraticPart D ((1 : F) • x) =
        (1 : F) * (q x + q 0 + quadraticPart D x)
      rw [one_smul, one_mul]

private theorem exact_decomposition (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) (x : V) :
    q x = q 0 + affineLinear D q polar x + quadraticPart D x := by
  exact cancelConstant _ _ _

end Phase441QuadraticCoordinates

namespace Phase441

private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]

private abbrev IsPhase (q : V → F) (B : LinearMap.BilinForm F V) : Prop :=
  ∀ p u v, q (p+u+v)+q (p+u)+q (p+v)+q p = B u v

private theorem bit : ∀ a : F, a = 0 ∨ a = 1 := by decide
private theorem twice : ∀ a : F, a+a = 0 := by decide
private theorem scalarAdd : ∀ a b c d e f g : F, e+f+b+a = g →
    e+f+c+d = (b+a+c+d)+g := by decide

private def polarMap (q : V → F)
    (h : ∀ p u v, q (p+u+v)+q (p+u)+q (p+v)+q p = q (u+v)+q u+q v+q 0) :
    LinearMap.BilinForm F V := by
  let b (u v : V) := q (u+v)+q u+q v+q 0
  have bs : ∀ u v, b u v = b v u := by
    intro u v
    dsimp [b]
    rw [add_comm u v]
    abel
  have b0 (u : V) : b 0 u = 0 := by
    simp only [b, zero_add]
    rw [show q u + q 0 + q u + q 0 = (q u + q u) + (q 0 + q 0) by abel, twice, twice, zero_add]
  have ba (u w v : V) : b (u+w) v = b u v + b w v :=
    scalarAdd (q u) (q (u+v)) (q v) (q 0) (q (u+w+v)) (q (u+w)) (b w v) (h u w v)
  have bm (c : F) (u v : V) : b (c • u) v = c * b u v := by
    rcases bit c with rfl | rfl <;> simp [b0]
  exact {
    toFun := fun u => {
      toFun := b u
      map_add' := fun v w => by rw [bs u (v+w), ba, bs v u, bs w u]
      map_smul' := fun c v => by rw [bs u (c • v), bm, bs v u]; rfl }
    map_add' := fun u w => LinearMap.ext fun v => ba u w v
    map_smul' := fun c u => LinearMap.ext fun v => bm c u v }

private theorem phase_alt {q : V → F} {B : LinearMap.BilinForm F V} (h : IsPhase q B) :
    ∀ u, B u u = 0 := by
  intro u
  have huu : u + u = 0 := by
    calc
      u + u = (1 + 1 : F) • u := by rw [add_smul, one_smul]
      _ = 0 := by rw [twice, zero_smul]
  have hh := h 0 u u
  simp only [zero_add, huu] at hh
  rw [← hh, show q 0 + q u + q u + q 0 = (q 0 + q 0) + (q u + q u) by abel, twice, twice, zero_add]

private theorem phase_symm {q : V → F} {B : LinearMap.BilinForm F V} (h : IsPhase q B) :
    ∀ u v, B u v = B v u := by
  intro u v
  rw [← h 0 u v, ← h 0 v u]
  simp only [zero_add]
  rw [add_comm u v]
  abel

private theorem rank_even :
    ∀ (j : ℕ) {W : Type*} [AddCommGroup W] [Module F W] [Module.Finite F W]
      (B : LinearMap.BilinForm F W), (∀ x, B x x = 0) → (∀ x y, B x y = B y x) →
      Module.finrank F (LinearMap.range B) = j → ∃ m, j = 2*m := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro W _ _ _ B alt sym hj
    by_cases hB : B = 0
    · subst B
      have hh : LinearMap.range (0 : LinearMap.BilinForm F W) = ⊥ :=
        LinearMap.range_eq_bot.mpr rfl
      have hzero : j = 0 := by rw [hh, finrank_bot] at hj; exact hj.symm
      exact ⟨0, by simp [hzero]⟩
    · obtain ⟨e,f,hf⟩ : ∃ e f, B e f = 1 := by
        by_contra! hfalse
        apply hB
        ext x y
        exact (bit (B x y)).resolve_right (hfalse x y)
      let U := Phase441SymplecticStep.perpendicular B e f
      let C := B.restrict U
      have hs : j = 2 + Module.finrank F (LinearMap.range C) :=
        hj.symm.trans (Phase441SymplecticStep.rank_step B e f alt sym hf)
      obtain ⟨m, hm⟩ := ih _ (by omega) C (fun x => alt x.val) (fun x y => sym x.val y.val) rfl
      exact ⟨m+1, by omega⟩

end Phase441


open scoped BigOperators
open LinearMap Module

namespace BatchUpper

private abbrev F := ZMod 2

variable {V W : Type*} [AddCommGroup V] [Module F V] [Fintype V]
variable [AddCommGroup W] [Module F W]

private def sign (z : F) : ℤ := if z = 0 then 1 else -1

private theorem sign_add (x y : F) : sign (x + y) = sign x * sign y := by
  exact (by decide : ∀ x y : F, sign (x+y) = sign x * sign y) x y

private theorem sum_translate {A : Type*} [AddCommGroup A] [Fintype A]
    (g : A → ℤ) (r : A) : (∑ x, g (x+r)) = ∑ x, g x :=
  Fintype.sum_equiv (Equiv.addRight r) _ _ fun _ => rfl

private theorem zero_or_one (x : F) : x = 0 ∨ x = 1 :=
  (by decide : ∀ y : F, y = 0 ∨ y = 1) x

private theorem char_sum {A : Type*} [AddCommGroup A] [Fintype A]
    (l : A →+ F) : (∑ x, sign (l x)) = if l = 0 then (Fintype.card A : ℤ) else 0 := by
  classical
  by_cases hz : l = 0
  · simp [hz, sign]
  · obtain ⟨r, hr⟩ : ∃ r, l r ≠ 0 := by
      by_contra! h
      exact hz (AddMonoidHom.ext h)
    have h := sum_translate (fun x => sign (l x)) r
    simp only [l.map_add, sign_add, (zero_or_one (l r)).resolve_left hr,
      show sign 1 = -1 by decide, ← Finset.sum_mul] at h
    rw [ite_eq_right hz]
    linarith

private theorem rearrange (a b c d z : F) (h : a+b+c+d=z) : a+b = c+d+z := by
  exact (by decide : ∀ a b c d z : F, a+b+c+d=z → a+b=c+d+z) a b c d z h

private theorem eq_iff_add_zero (a b : F) : a = b ↔ a+b = 0 :=
  (by decide : ∀ a b : F, a=b ↔ a+b=0) a b

-- The translation and character orthogonality argument follows the pinned
-- `lean/PEqualNP/Outside/L_meta_29947.lean` (84686e3276044e3cadda1c4453d05f6445313e0f).
open Classical in
private theorem square {A H : Type*} [AddCommGroup A] [Fintype A] [Zero H]
    (q : A → F) (p : A → H) (b : H → A →+ F) (hb : ∀ h, b h = 0 ↔ h = 0)
    (hq : ∀ x r, q (x+r)+q x+q r+q 0 = b (p r) x) :
    (∑ x, sign (q x)) ^ 2 =
      (Fintype.card A : ℤ) * ∑ r, if p r = 0 then sign (q r+q 0) else 0 := by
  classical
  rw [pow_two]
  calc
    _ = ∑ x : A, ∑ y : A, sign (q x) * sign (q y) := by
      simp only [Finset.mul_sum, mul_comm]
    _ = ∑ x : A, ∑ r : A, sign (q x) * sign (q (r+x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_translate (fun y => sign (q x) * sign (q y)) x).symm
    _ = ∑ r : A, ∑ x : A, sign (q r+q 0)*sign (b (p r) x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro x _
      rw [← sign_add, ← sign_add, add_comm r x, add_comm (q x)]
      rw [rearrange _ _ _ _ _ (hq x r)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.mul_sum, char_sum]
      simp only [hb]
      split <;> ring

private theorem card_pow (A : Type*) [AddCommGroup A] [Module F A] [Fintype A] :
    Fintype.card A = 2 ^ Module.finrank F A := by
  rw [Module.card_eq_pow_finrank (K := F), ZMod.card]

-- Restricting the query to the global radical spends that much of its rank.
private theorem dim_ker_inter (B : V →ₗ[F] W) {e : ℕ} (L : V →ₗ[F] (Fin e → F)) :
    finrank F V - finrank F B.ker ≤
      finrank F L.ker - finrank F (B.domRestrict L.ker).ker +
        (e - finrank F (L.domRestrict B.ker).range) := by
  let I := (B.domRestrict L.ker).ker
  let J := (L.domRestrict B.ker).ker
  let E : I ≃ₗ[F] J :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hIJ := E.finrank_eq
  have hK := L.finrank_range_add_finrank_ker
  have hJ := (L.domRestrict B.ker).finrank_range_add_finrank_ker
  have hI := (B.domRestrict L.ker).finrank_range_add_finrank_ker
  have he := Submodule.finrank_le L.range
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at he
  dsimp [I, J] at hIJ
  omega

-- An integral square that is a power of two has an even exponent.
private theorem square_pow_lower {a : ℤ} {j d : ℕ} (h : a^2 = 2^j) (hd : 2*d ≤ j+1) :
    (2 : ℤ)^d ≤ |a| := by
  have hn : a.natAbs ^ 2 = 2^j := by
    simpa only [Int.natAbs_pow, show (2 : ℤ).natAbs = 2 by decide] using congrArg Int.natAbs h
  have hj : 2 * (a.natAbs.factorization 2) = j := by
    have he := congrArg (fun n : ℕ => n.factorization 2) hn
    rw [Nat.factorization_pow_self Nat.prime_two, Nat.factorization_pow, Finsupp.smul_apply,
      smul_eq_mul] at he
    exact he
  have hpow : (2 : ℤ)^(2*d) ≤ 2^j := pow_le_pow_right₀ (by decide) (by omega)
  apply le_of_sq_le_sq _ (abs_nonneg a)
  rwa [← pow_mul, Nat.mul_comm, sq_abs, h]

omit [Fintype V] in
private theorem derivative (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (x r : V) :
    f (x+r)+f x = f r+f 0+B r x := by
  apply rearrange
  calc
    _ = f (0+r+x)+f (0+r)+f (0+x)+f 0 := by
      simp only [zero_add]
      ac_rfl
    _ = _ := hq 0 r x

omit [Fintype V] in
private theorem period_iff (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (r : V) :
    (∀ x, f (x+r) = f x) ↔ r ∈ B.ker ∧ f r = f 0 := by
  constructor
  · intro h
    have h0 : f r = f 0 := by simpa using h 0
    refine ⟨LinearMap.mem_ker.mpr (LinearMap.ext fun x => ?_), h0⟩
    have hx := derivative f B hq x r
    rw [(eq_iff_add_zero _ _).mp (h x), (eq_iff_add_zero _ _).mp h0, zero_add] at hx
    exact hx.symm
  · rintro ⟨hB, h0⟩ x
    apply (eq_iff_add_zero _ _).mpr
    rw [derivative f B hq, (eq_iff_add_zero _ _).mp h0, zero_add,
      LinearMap.mem_ker.mp hB]
    rfl

private theorem toAddMonoidHom_eq_zero {A : Type*} [AddCommGroup A] [Module F A]
    (l : A →ₗ[F] F) : l.toAddMonoidHom = 0 ↔ l = 0 :=
  ⟨fun h => LinearMap.ext fun t => DFunLike.congr_fun h t, fun h => by subst l; rfl⟩

private theorem shift_cancel (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {e : ℕ} (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F)
    (r : B.ker) (hr : f r ≠ f 0) (hl : L r = 0) :
    (∑ x, sign (out (L x)+f x)) = 0 := by
  have hs := sum_translate (fun x => sign (out (L x)+f x)) (r : V)
  have hδ (x : V) : f (x+r) = f x+1 := by
    have hz := derivative f B hq x r
    have hbr : B r x = 0 := by
      rw [show B r = 0 from r.property]
      rfl
    rw [hbr, add_zero, (zero_or_one (f r+f 0)).resolve_left
      (fun h => hr ((eq_iff_add_zero _ _).mpr h))] at hz
    exact (by decide : ∀ a b : F, a+b=1 → a=b+1) _ _ hz
  simp only [L.map_add, hl, add_zero, hδ, ← add_assoc, sign_add, ← Finset.sum_mul,
    show sign 1 = -1 by decide] at hs
  simp only [sign_add]
  linarith

private theorem oneBatchInt (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {m w e : ℕ} (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F)
    (hr : 2*m ≤ finrank F L.ker - finrank F (B.domRestrict L.ker).ker + w) :
    (2 : ℤ)^(m-w/2) * (∑ x, sign (out (L x)+f x)) ≤ Fintype.card V := by
  classical
  let K := L.ker
  let I := (B.domRestrict K).ker
  let P : K →ₗ[F] K →ₗ[F] F :=
    { toFun := fun r => (B r).domRestrict K
      map_add' := fun r s => by ext t; simp
      map_smul' := fun c r => by ext t; simp }
  let J := P.ker
  let A (x : V) := ∑ k : K, sign (f (x+k))
  let H (x : V) := sign (out (L x)+f x)
  let C (x : V) := sign (out (L x))
  let D : ℤ := 2^(finrank F I + (m-w/2))
  have hIJ : finrank F I ≤ finrank F J := by
    apply Submodule.finrank_mono
    intro r hr
    change P r = 0
    have h : B r = 0 := hr
    ext t
    change B r t = 0
    simp [h]
  have hIK : finrank F I ≤ finrank F K := Submodule.finrank_le I
  have hsquare (x : V) : A x ^ 2 = (Fintype.card K : ℤ) *
      ∑ r : K, if P r = 0 then sign (f (x+r)+f x) else 0 := by
    change (∑ k : K, sign (f (x+k))) ^ 2 = _
    simpa only [Submodule.coe_add, Submodule.coe_zero, add_zero, ← add_assoc] using
      (square (fun k : K => f (x+k)) P LinearMap.toAddMonoidHom
        toAddMonoidHom_eq_zero
        (fun k r => by
          change f (x+(↑(k+r) : V))+f (x+k)+f (x+r)+f (x+(↑(0 : K) : V)) =
            B r k
          calc
            _ = f (x+r+k)+f (x+r)+f (x+k)+f x := by
              simp only [Submodule.coe_add, Submodule.coe_zero, add_zero]
              ac_rfl
            _ = _ := hq x r k))
  have hlocal (x : V) : A x = 0 ∨ A x ^ 2 = (2 : ℤ)^(finrank F K+finrank F J) := by
    let l : J →+ F :=
      { toFun := fun r => f (x+(r.val : V))+f x
        map_zero' := by
          change f (x+0)+f x = 0
          rw [add_zero, ← eq_iff_add_zero]
        map_add' := fun r s => by
          have hz : B (r.val : V) (s.val : V) = 0 := by
            have hh : P r.val = 0 := r.property
            exact DFunLike.congr_fun hh s.val
          have hh := hq x (r.val : V) (s.val : V)
          rw [hz] at hh
          change f (x+((r.val : V)+(s.val : V)))+f x =
            (f (x+(r.val : V))+f x)+(f (x+(s.val : V))+f x)
          rw [← add_assoc]
          exact (by decide : ∀ a b c d : F, a+b+c+d=0 → a+d=(b+d)+(c+d)) _ _ _ _ hh }
    have hx : (∑ r : K, if P r = 0 then sign (f (x+r)+f x) else 0) =
        ∑ r : J, sign (l r) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun r => by simp [J, LinearMap.mem_ker]) _
    have hy := hsquare x
    rw [hx, char_sum] at hy
    split at hy
    · right
      rw [card_pow K, card_pow J] at hy
      simpa [pow_add] using hy
    · left
      rw [mul_zero, pow_two, mul_eq_zero] at hy
      exact hy.elim id id
  have hpoint (x : V) : D * (C x * A x) ≤ A x ^ 2 := by
    rcases hlocal x with hz | hz
    · simp [hz]
    have hd : D ≤ |A x| := by
      apply square_pow_lower hz
      dsimp [I, K, J] at *
      omega
    have hC : C x * A x ≤ |A x| := by
      unfold C sign
      split
      · simpa using le_abs_self (A x)
      · simpa using neg_le_abs (A x)
    calc
      _ ≤ D * |A x| := mul_le_mul_of_nonneg_left hC (by dsimp [D]; positivity)
      _ ≤ |A x| * |A x| := mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      _ = A x ^ 2 := by rw [← pow_two, sq_abs]
  have hglob (r : K) : (∑ x : V, sign (f (x+r)+f x)) =
      if B r = 0 then (Fintype.card V : ℤ)*sign (f r+f 0) else 0 := by
    simp only [derivative f B hq, sign_add, ← Finset.mul_sum]
    change sign (f r) * sign (f 0) * (∑ x : V, sign ((B r).toAddMonoidHom x)) = _
    rw [char_sum]
    simp only [toAddMonoidHom_eq_zero]
    split <;> ring
  -- Averaging the squared fiber sums over all base points kills every
  -- derivative except those in the intersection of the two global kernels.
  have hsumsquare : (∑ x, A x ^ 2) ≤ (Fintype.card K : ℤ) *
      ((Fintype.card V : ℤ) * Fintype.card I) := by
    simp only [hsquare, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ r : K, if B r = 0 then (Fintype.card V : ℤ) else 0 := by
        apply Finset.sum_le_sum
        intro r _
        by_cases h : P r = 0
        · simp only [h, ite_true, hglob]
          split
          · unfold sign
            split <;> simp
          · rfl
        · simp only [ite_eq_right h, Finset.sum_const_zero]
          split <;> positivity
      _ = _ := by
        rw [← Finset.sum_filter]
        rw [Finset.sum_subtype (p := fun r : K => r ∈ I) (F := (inferInstance : Fintype I)) _
          (fun r : K => by change _ ↔ B r = 0; simp) _]
        simp [mul_comm]
  have hAvg : (∑ x, C x * A x) = (Fintype.card K : ℤ) * ∑ x, H x := by
    have hshift (r : K) (x : V) : sign (out (L x)) * sign (f (x+r)) = H (x+r) := by
      have hh : L (r : V) = 0 := r.property
      simp [H, sign_add, hh]
    calc
      _ = ∑ x : V, ∑ r : K, sign (out (L x)) * sign (f (x+r)) := by
        simp only [C, A, Finset.mul_sum]
      _ = ∑ r : K, ∑ x : V, H (x+r) := by rw [Finset.sum_comm]; simp only [hshift]
      _ = _ := by simp only [sum_translate H, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hmain := (Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)).trans hsumsquare
  rw [← Finset.mul_sum, hAvg, mul_left_comm D] at hmain
  have hcardK : (0 : ℤ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hmain' := le_of_mul_le_mul_left hmain hcardK
  have hcardI : (0 : ℤ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  have hD : D = (Fintype.card I : ℤ) * (2 : ℤ)^(m-w/2) := by
    rw [card_pow I]
    simp [D, pow_add]
  rw [hD, mul_assoc, mul_comm (Fintype.card V : ℤ)] at hmain'
  exact le_of_mul_le_mul_left hmain' hcardI

open Classical in
private theorem oneBatch (f : V → F) (B : V →ₗ[F] V →ₗ[F] F)
    (hq : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    {m e : ℕ} (hr : finrank F V - finrank F B.ker = 2*m)
    (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F) :
    (∑ x : V, if out (L x) = f x then (1 : ℚ) else -1) / Fintype.card V ≤
      if ∃ r : B.ker, f r ≠ f 0 then
        if e = 0 then (0 : ℚ) else 1/2^(m-(e-1)/2)
      else 1/2^(m-e/2) := by
  classical
  have hscore : (∑ x : V, if out (L x) = f x then (1 : ℚ) else -1) =
      ((∑ x : V, sign (out (L x)+f x) : ℤ) : ℚ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro x _
    simp [eq_iff_add_zero (out (L x)) (f x), sign]
  rw [hscore]
  have hcard : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdim := dim_ker_inter B L
  rw [hr] at hdim
  have upper (w : ℕ)
      (hw : 2*m ≤ finrank F L.ker - finrank F (B.domRestrict L.ker).ker+w) :
      ((∑ x : V, sign (out (L x)+f x) : ℤ) : ℚ) / Fintype.card V ≤ 1/2^(m-w/2) := by
    apply (div_le_div_iff₀ hcard (by positivity)).2
    rw [one_mul, mul_comm]
    exact_mod_cast oneBatchInt f B hq L out hw
  split
  · rename_i hmask
    obtain ⟨r, hr⟩ := hmask
    by_cases hz : L r = 0
    · rw [shift_cancel f B hq L out r hr hz]
      push_cast
      split <;> simp
    · have hpos : 0 < finrank F (L.domRestrict B.ker).range := by
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        exact ⟨⟨L r, ⟨r, rfl⟩⟩, fun hh => hz (congrArg Subtype.val hh)⟩
      have hle := Submodule.finrank_le (L.domRestrict B.ker).range
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle
      rw [ite_eq_right (by omega : e ≠ 0)]
      exact upper (e-1) (by omega)
  · exact upper e (by omega)

end BatchUpper


namespace TwoStageSplit

private abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]

private abbrev Rad (B : LinearMap.BilinForm F V) := LinearMap.ker B
private noncomputable abbrev polarRank (B : LinearMap.BilinForm F V) := Module.finrank F (LinearMap.range B)

private theorem rad_mem (B : LinearMap.BilinForm F V) (u : V) :
    u ∈ Rad B ↔ ∀ v, B u v = 0 := by
  rw [LinearMap.mem_ker]
  exact ⟨fun h v => congrArg (fun g : V →ₗ[F] F => g v) h,
    fun h => LinearMap.ext h⟩

private theorem zadd (x : F) : x + x = 0 := by
  rw [← two_mul, show (2 : F) = 0 by decide, zero_mul]

private theorem symm (B : LinearMap.BilinForm F V) (alt : ∀ u, B u u = 0)
    (u v : V) : B u v = B v u := by
  have h := alt (u + v)
  simp only [map_add, LinearMap.add_apply, alt, zero_add, add_zero] at h
  linear_combination h - zadd (B v u)

private theorem unitVector (Q : V →ₗ[F] F) (h : Q ≠ 0) : ∃ t, Q t = 1 := by
  by_contra hn
  apply h
  ext u
  have hu : Q u ≠ 1 := fun e => hn ⟨u, e⟩
  have cases : ∀ y : F, y = 0 ∨ y = 1 := by decide
  exact (cases (Q u)).resolve_right hu

private theorem subQuery (Q : V →ₗ[F] F) {t : V} (ht : Q t = 1) (x : V) :
    x - Q x • t ∈ Q.ker := by
  rw [LinearMap.mem_ker, map_sub, map_smul, ht, smul_eq_mul, mul_one, sub_self]

private theorem eval_of_ker (L Q : V →ₗ[F] F) {t : V} (ht : Q t = 1)
    (h : ∀ x : Q.ker, L x = 0) (x : V) : L x = Q x * L t := by
  have e := h ⟨x - Q x • t, subQuery Q ht x⟩
  simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using e

private theorem finrank_ker_unit [FiniteDimensional F V] (Q : V →ₗ[F] F) {t : V}
    (ht : Q t = 1) : 1 + Module.finrank F Q.ker = Module.finrank F V := by
  have htop : LinearMap.range Q = ⊤ := LinearMap.range_eq_top.mpr fun y =>
    ⟨y • t, by rw [map_smul, ht, smul_eq_mul, mul_one]⟩
  have h := Q.finrank_range_add_finrank_ker
  rwa [htop, finrank_top, Module.finrank_self] at h

private theorem query_in_range [FiniteDimensional F V] (B : LinearMap.BilinForm F V)
    (alt : ∀ u, B u u = 0) (Q : V →ₗ[F] F) (h : ∀ u : Rad B, Q u = 0) :
    ∃ b, B b = Q := by
  have le : LinearMap.range B ≤ (Rad B).dualAnnihilator := by
    rintro _ ⟨v, rfl⟩
    apply (Submodule.mem_dualAnnihilator (B v)).mpr
    intro x hx
    exact (symm B alt v x).trans ((rad_mem B x).mp hx v)
  have h₁ := B.finrank_range_add_finrank_ker
  have h₂ := Subspace.finrank_add_finrank_dualAnnihilator_eq (Rad B)
  have hfin : Module.finrank F (LinearMap.range B) = Module.finrank F (Rad B).dualAnnihilator :=
    Nat.add_right_cancel (h₁.trans ((add_comm _ _).trans h₂).symm)
  have eq := Submodule.eq_of_le_of_finrank_le le hfin.ge
  apply LinearMap.mem_range.mp
  rw [eq, Submodule.mem_dualAnnihilator]
  exact fun x hx => h ⟨x, hx⟩

private abbrev restrictedRad (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F) :=
  Rad (B.restrict Q.ker)

private theorem restricted_mem (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F)
    (u : Q.ker) : u ∈ restrictedRad B Q ↔ ∀ v : Q.ker, B u v = 0 :=
  rad_mem (B.restrict Q.ker) u

private def restrictedVal (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F) :
    restrictedRad B Q →ₗ[F] V := Q.ker.subtype.comp (restrictedRad B Q).subtype

private noncomputable def maskOn (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (W : Submodule F V) (van : ∀ u v : W, B u v = 0) (p : V) : W →ₗ[F] F where
  toFun u := f (p + u) + f p
  map_add' u v := by
    change f (p + ((u : V) + v)) + f p = (f (p + u) + f p) + (f (p + v) + f p)
    have h := polar p u v
    rw [van u v, add_assoc p] at h
    linear_combination h - zadd (f (p + u)) - zadd (f (p + v)) - zadd (f p)
  map_smul' c u := by
    have cases : ∀ y : F, y = 0 ∨ y = 1 := by decide
    rcases cases c with rfl | rfl
    · change f (p + (0 : F) • (u : V)) + f p = (0 : F) • _
      simp [zadd]
    · change f (p + (1 : F) • (u : V)) + f p = (1 : F) • _
      simp

private noncomputable def mask (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) : Rad B →ₗ[F] F :=
  maskOn B f polar (Rad B) (fun u v => (rad_mem B u).mp u.property v) 0

private theorem mask_apply (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (u : Rad B) :
    mask B f polar u = f u + f 0 := by
  change f (0 + (u : V)) + f 0 = _
  rw [zero_add]

private theorem translatedDerivative (B : LinearMap.BilinForm F V) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (p u : V) :
    f (p+u) + f p = (f u + f 0) + B p u := by
  have h := polar 0 p u
  simp only [zero_add] at h
  linear_combination h - zadd (f u) - zadd (f 0)

/-- A restriction to the coset with representative `p` has zero radical mask. -/
private def unmaskedAt (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F) (f : V → F) (p : V) : Prop :=
  ∀ u : restrictedRad B Q, f (p + (u.val : V)) + f p = 0

private theorem restrictPolar (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F) (f : V → F)
    (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) (p : V) :
    ∀ x u v : Q.ker,
      f (p + ↑(x+u+v)) + f (p + ↑(x+u)) + f (p + ↑(x+v)) + f (p + ↑x) =
        (B.restrict Q.ker) u v := by
  intro x u v
  simpa only [Submodule.coe_add, add_assoc, LinearMap.BilinForm.restrict_apply,
    LinearMap.domRestrict_apply] using
    polar (p + (x : V)) u v

private noncomputable def maskAt (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F)
    (f : V → F) (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (p : V) : restrictedRad B Q →ₗ[F] F :=
  mask (B.restrict Q.ker) (fun x => f (p + (x : V))) (restrictPolar B Q f polar p)

private theorem maskAt_apply (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F)
    (f : V → F) (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (p : V) (u : restrictedRad B Q) :
    maskAt B Q f polar p u = f (p + (u.val : V)) + f p := by
  rw [maskAt, mask_apply]
  simp

private theorem unmaskedAt_iff (B : LinearMap.BilinForm F V) (Q : V →ₗ[F] F)
    (f : V → F) (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (p : V) : unmaskedAt B Q f p ↔
      mask (B.restrict Q.ker) (fun x => f (p + (x : V))) (restrictPolar B Q f polar p) = 0 := by
  change unmaskedAt B Q f p ↔ maskAt B Q f polar p = 0
  constructor
  · intro h
    ext u
    rw [maskAt_apply, LinearMap.zero_apply]
    exact h u
  · intro h u
    rw [← maskAt_apply B Q f polar p u, h, LinearMap.zero_apply]

private theorem query_split_annihilates [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (alt : ∀ u, B u u = 0)
    (f : V → F) (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (Q : V →ₗ[F] F) {t : V} (ht : Q t = 1) (hq : Q.comp (Rad B).subtype = 0) :
    polarRank B = polarRank (B.restrict Q.ker) + 2 ∧
    ((unmaskedAt B Q f 0 ∨ unmaskedAt B Q f t) ↔ mask B f polar = 0) ∧
    ¬ (unmaskedAt B Q f 0 ∧ unmaskedAt B Q f t) := by
  let R := Rad B
  let K := restrictedRad B Q
  have hQ (u : R) : Q (u : V) = 0 :=
    congrArg (fun g : R →ₗ[F] F => g u) hq
  obtain ⟨b, hb⟩ := query_in_range B alt Q hQ
  have hbQ : Q b = 0 := by rw [← hb, alt]
  have hbt : B b t = 1 := by rw [hb, ht]
  let bK : K := ⟨⟨b, LinearMap.mem_ker.mpr hbQ⟩,
    (restricted_mem B Q _).mpr fun v => by
      change B b (v : V) = 0
      rw [hb]
      exact LinearMap.mem_ker.mp v.property⟩
  let L : K →ₗ[F] F := (B.flip t).comp (restrictedVal B Q)
  have hL (u : K) : L u = B (u.val : V) t := rfl
  have hbL : L bK = 1 := hbt
  have coeff (u : K) (v : V) : B (u.val : V) v = Q v * L u :=
    eval_of_ker (B (u.val : V)) Q ht ((restricted_mem B Q u.val).mp u.property) v
  let E : R ≃ₗ[F] L.ker := {
    toFun := fun u => ⟨⟨⟨u, LinearMap.mem_ker.mpr (hQ u)⟩,
      (restricted_mem B Q _).mpr fun v => (rad_mem B u).mp u.property v⟩,
      LinearMap.mem_ker.mpr ((rad_mem B u).mp u.property t)⟩
    invFun := fun u => ⟨(u.val.val : V), (rad_mem B _).mpr fun v => by
      rw [coeff u.val, LinearMap.mem_ker.mp u.property, mul_zero]⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext (Subtype.ext (Subtype.ext rfl))
    map_add' := fun _ _ => Subtype.ext (Subtype.ext (Subtype.ext rfl))
    map_smul' := fun _ _ => Subtype.ext (Subtype.ext (Subtype.ext rfl)) }
  have hRK : 1 + Module.finrank F R = Module.finrank F K := by
    rw [E.finrank_eq]
    exact finrank_ker_unit L hbL
  have rankV := B.finrank_range_add_finrank_ker
  have rankH := (B.restrict Q.ker).finrank_range_add_finrank_ker
  have dimH := finrank_ker_unit Q ht
  change polarRank B + Module.finrank F R = Module.finrank F V at rankV
  change polarRank (B.restrict Q.ker) + Module.finrank F K = Module.finrank F Q.ker at rankH
  refine ⟨by omega, ?_⟩
  have part (p : V) (u : R) : maskAt B Q f polar p (E u).val = mask B f polar u := by
    rw [maskAt_apply, mask_apply]
    change f (p + (u : V)) + f p = f (u : V) + f 0
    rw [translatedDerivative B f polar, symm B alt p u, (rad_mem B u).mp u.property p, add_zero]
  have char (p : V) :
      unmaskedAt B Q f p ↔ mask B f polar = 0 ∧ f (p + b) + f p = 0 := by
    constructor
    · intro hp
      refine ⟨?_, hp bK⟩
      ext u
      rw [← part p u, maskAt_apply]
      exact hp (E u).val
    · rintro ⟨hm, hb0⟩ u
      have van (v : L.ker) : maskAt B Q f polar p (v : K) = 0 := by
        have e := part p (E.symm v)
        rwa [E.apply_symm_apply, hm, LinearMap.zero_apply] at e
      rw [← maskAt_apply B Q f polar p u, eval_of_ker _ L hbL van, maskAt_apply]
      change L u * (f (p + b) + f p) = 0
      rw [hb0, mul_zero]
  have d0 : f (0 + b) + f 0 = f b + f 0 := by rw [zero_add]
  have dt : f (t + b) + f t = (f b + f 0) + 1 := by
    rw [translatedDerivative B f polar, symm B alt t b, hbt]
  have bit : ∀ x : F, (x = 0 ∨ x + 1 = 0) ∧ ¬ (x = 0 ∧ x + 1 = 0) := by decide
  rcases bit (f b + f 0) with ⟨hor, hand⟩
  rw [char, char, d0, dt]
  refine ⟨⟨fun h => h.elim And.left And.left, fun hm => ?_⟩, ?_⟩
  · exact hor.elim (fun h => Or.inl ⟨hm, h⟩) (fun h => Or.inr ⟨hm, h⟩)
  · exact fun h => hand ⟨h.1.2, h.2.2⟩

private theorem query_split_detects [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (alt : ∀ u, B u u = 0)
    (f : V → F) (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (Q : V →ₗ[F] F) (hq : Q.comp (Rad B).subtype ≠ 0) :
    polarRank B = polarRank (B.restrict Q.ker) ∧
      ∀ p, unmaskedAt B Q f p ↔ mask B f polar = 0 ∨
        mask B f polar = Q.comp (Rad B).subtype := by
  let R := Rad B
  let K := restrictedRad B Q
  let P := Q.comp R.subtype
  obtain ⟨r, hr⟩ := unitVector P hq
  have hrQ : Q (r : V) = 1 := hr
  have full (u : K) : (u.val : V) ∈ R := by
    apply (rad_mem B _).mpr
    intro v
    rw [eval_of_ker _ Q hrQ ((restricted_mem B Q u.val).mp u.property),
      symm B alt _ (r : V), (rad_mem B r).mp r.property, mul_zero]
  let E : K ≃ₗ[F] P.ker := {
    toFun := fun u => ⟨⟨(u.val : V), full u⟩, LinearMap.mem_ker.mpr
      (LinearMap.mem_ker.mp u.val.property)⟩
    invFun := fun u => ⟨⟨(u.val : V), LinearMap.mem_ker.mpr
      (LinearMap.mem_ker.mp u.property)⟩,
      (restricted_mem B Q _).mpr fun v => (rad_mem B u.val).mp u.val.property v⟩
    left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    right_inv := fun _ => Subtype.ext (Subtype.ext rfl)
    map_add' := fun _ _ => Subtype.ext (Subtype.ext rfl)
    map_smul' := fun _ _ => Subtype.ext (Subtype.ext rfl) }
  have hRK : 1 + Module.finrank F K = Module.finrank F R := by
    rw [E.finrank_eq]
    exact finrank_ker_unit P hr
  have rankV := B.finrank_range_add_finrank_ker
  have rankH := (B.restrict Q.ker).finrank_range_add_finrank_ker
  have dimH := finrank_ker_unit Q hrQ
  change polarRank B + Module.finrank F R = Module.finrank F V at rankV
  change polarRank (B.restrict Q.ker) + Module.finrank F K = Module.finrank F Q.ker at rankH
  refine ⟨by omega, ?_⟩
  intro p
  have part (u : K) : f (p + (u.val : V)) + f p = mask B f polar (E u).val := by
    rw [mask_apply, translatedDerivative B f polar, symm B alt p (u.val : V),
      (rad_mem B _).mp (full u) p, add_zero]
    rfl
  constructor
  · intro hp
    have van (u : P.ker) : mask B f polar (u : R) = 0 := by
      have e := part (E.symm u)
      rw [E.apply_symm_apply, hp (E.symm u)] at e
      exact e.symm
    have bit : ∀ x : F, x = 0 ∨ x = 1 := by decide
    rcases bit (mask B f polar r) with hz | ho
    · left
      ext u
      rw [eval_of_ker _ P hr van, hz, mul_zero, LinearMap.zero_apply]
    · right
      ext u
      rw [eval_of_ker _ P hr van, ho, mul_one]
  · intro hm u
    rw [part]
    rcases hm with h | h
    · rw [h, LinearMap.zero_apply]
    · rw [h]
      exact LinearMap.mem_ker.mp (E u).property

/-- The two restrictions by a nonzero binary linear query are represented by `0` and `t`.
Their half-rank and zero-mask classification is determined by the query on the radical. -/
private theorem query_split [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (alt : ∀ u, B u u = 0)
    (f : V → F) (polar : ∀ p u v, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v)
    (Q : V →ₗ[F] F) {t : V} (ht : Q t = 1) :
    let P := Q.comp (Rad B).subtype
    let m := mask B f polar
    (P = 0 → polarRank B / 2 = polarRank (B.restrict Q.ker) / 2 + 1 ∧
      ((unmaskedAt B Q f 0 ∨ unmaskedAt B Q f t) ↔ m = 0) ∧
      ¬ (unmaskedAt B Q f 0 ∧ unmaskedAt B Q f t)) ∧
    (P ≠ 0 → polarRank B / 2 = polarRank (B.restrict Q.ker) / 2 ∧
      ∀ p, unmaskedAt B Q f p ↔ m = 0 ∨ m = P) := by
  dsimp only
  constructor
  · intro h
    obtain ⟨hr, hm⟩ := query_split_annihilates B alt f polar Q ht h
    exact ⟨by omega, hm⟩
  · intro h
    obtain ⟨hr, hm⟩ := query_split_detects B alt f polar Q h
    exact ⟨by rw [hr], hm⟩
end TwoStageSplit


namespace Upper441
open Phase441 Query441 TwoStageSplit

private abbrev F := ZMod 2

private noncomputable def bound (e d m : ℕ) (unmasked : Prop) : ℚ :=
  open Classical in
  if unmasked then Bias441.unmasked (Bias441.core m ((e-1)/2)) (e % 2 == 0) d
  else Bias441.masked (Bias441.core m ((e-1)/2)) d

variable {V : Type*} [AddCommGroup V] [Module F V]

private theorem masked_iff (q : V → F) (B : LinearMap.BilinForm F V) (hq : IsPhase q B) :
    (∃ r : B.ker, q r.val ≠ q 0) ↔ mask B q hq ≠ 0 := by
  classical
  have bit : ∀ a b : F, a+b=0 ↔ a=b := by decide
  rw [ne_eq, ← not_iff_not]
  push_neg
  constructor
  · intro h
    ext x
    rw [mask_apply, LinearMap.zero_apply, bit]
    exact h x
  · intro h x
    apply (bit _ _).mp
    rw [← mask_apply B q hq, h, LinearMap.zero_apply]

private theorem rdim [Module.Finite F V] (B : LinearMap.BilinForm F V) :
    Module.finrank F V - Module.finrank F B.ker = polarRank B := by
  have h := B.finrank_range_add_finrank_ker
  change polarRank B + _ = _ at h
  omega

private theorem upper (e : ℕ) (he : 0 < e) :
    ∀ (d : ℕ) {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
      (q : V → F) (B : LinearMap.BilinForm F V) (hq : IsPhase q B)
      (P : V →ₗ[F] (Fin d → F)) (N : (Fin d → F) → V →ₗ[F] (Fin e → F))
      (O : (Fin d → F) → (Fin e → F) → F),
      score q (fun x => O (P x) (N (P x) x)) ≤ bound e d (polarRank B/2) (mask B q hq = 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro V _ _ _ q B hq P N O
    obtain ⟨m, hm⟩ := rank_even (polarRank B) B (phase_alt hq) (phase_symm hq) rfl
    have hr : Module.finrank F V - Module.finrank F B.ker = 2*m := (rdim B).trans hm
    have hP (x : V) : P x = 0 := Subsingleton.elim _ _
    have hd : polarRank B / 2 = m := by omega
    simp only [hP, hd]
    have h := BatchUpper.oneBatch q B hq (e := e) hr (N 0) (O 0)
    change score q (fun x => O 0 (N 0 x)) ≤ _ at h
    simp only [masked_iff q B hq] at h
    by_cases hmask : mask B q hq = 0
    · simp only [hmask, not_true_eq_false, ite_false] at h
      simpa [bound, hmask, Bias441.posted_formula m 0 e he] using h
    · simp only [hmask, not_false_eq_true, ite_true, ite_eq_right (by omega : e ≠ 0)] at h
      simpa [bound, hmask, Bias441.masked_formula] using h
  | succ d ih =>
    intro V _ _ _ q B hq P N O
    let L := head P
    let m := polarRank B / 2
    let c := Bias441.core m ((e-1)/2)
    let extra := e % 2 == 0
    let mask0 : Prop := mask B q hq = 0
    let s (x : V) := O (P x) (N (P x) x)
    have hc : 0 ≤ c := Bias441.core_nonneg _ _
    change score q s ≤ bound e (d+1) m mask0
    by_cases hL : L = 0
    · let label (a : Fin d → F) : Fin (d+1) → F := Fin.cons 0 a
      have hlabel (x : V) : label (tail P x) = P x := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have hx : L x = 0 := by rw [hL]; rfl
          exact hx.symm
        · simp [label, tail]
      have h := ih q B hq (tail P) (fun a => N (label a)) (fun a b => O (label a) b)
      simp only [hlabel] at h
      refine h.trans ?_
      by_cases H : mask0
      · simpa [bound, mask0, m, c, extra, H] using Bias441.unmasked_mono c hc extra d
      · simpa [bound, mask0, m, c, H] using Bias441.masked_mono c hc d
    · obtain ⟨u, hu⟩ := unitVector L hL
      let m' := polarRank (B.restrict L.ker)/2
      have child (p : V) : score (fun x : L.ker => q (p+x.val)) (fun x => s (p+x.val)) ≤
          bound e d m' (unmaskedAt B L q p) := by
        obtain ⟨P', N', O', H⟩ := restrict_strategy P N O p L.ker
          (fun x => LinearMap.mem_ker.mp x.property)
        have h := ih (fun x : L.ker => q (p+x.val)) (B.restrict L.ker)
          (restrictPolar B L q hq p) P' N' O'
        simp only [H] at h
        rw [unmaskedAt_iff B L q hq p]
        simpa only [s, m', add_comm p] using h
      have hS := score_split L u hu q s
      have hL0 := child 0
      simp only [zero_add] at hL0
      have hL1 := child u
      simp only [add_comm u] at hL1
      rw [hS]
      refine (div_le_div_of_nonneg_right (add_le_add hL0 hL1) (by norm_num : (0 : ℚ) ≤ 2)).trans ?_
      obtain ⟨h1, h2⟩ := query_split B (phase_alt hq) q hq L hu
      by_cases H : L.comp B.ker.subtype = 0
      · obtain ⟨hr, hm, hnot⟩ := h1 H
        have hr' : m = m'+1 := hr
        have hc' : Bias441.core m' ((e-1)/2) = 2*c := by
          change _ = 2 * Bias441.core m ((e-1)/2)
          rw [hr']
          exact Bias441.core_step _ _
        by_cases Hm : mask0
        · have hor : unmaskedAt B L q 0 ∨ unmaskedAt B L q u := hm.mpr Hm
          rcases hor with h | h
          · have h' : ¬ unmaskedAt B L q u := fun hh => hnot ⟨h,hh⟩
            simpa only [bound, h, h', Hm, ite_true, ite_false, hc', c, extra] using Bias441.split_upper c extra d
          · have h' : ¬ unmaskedAt B L q 0 := fun hh => hnot ⟨hh,h⟩
            simpa only [bound, h, h', Hm, ite_true, ite_false, hc', c, extra, add_comm] using Bias441.split_upper c extra d
        · have h0 : ¬ unmaskedAt B L q 0 := fun h => Hm (hm.mp (Or.inl h))
          have h1 : ¬ unmaskedAt B L q u := fun h => Hm (hm.mp (Or.inr h))
          simp only [bound, h0, h1, Hm, ite_false, hc']
          rw [Bias441.masked_step]
          change (_ + _) / 2 ≤ Bias441.masked c (d+1)
          linarith
      · obtain ⟨hr, hm⟩ := h2 H
        have hr' : m = m' := hr
        rw [← hr']
        by_cases Hm : mask0
        · have h0 := (hm 0).mpr (Or.inl Hm)
          have h1 := (hm u).mpr (Or.inl Hm)
          simp only [bound, h0, h1, Hm, ite_true]
          have hh := Bias441.unmasked_mono c hc extra d
          change (_ + _) / 2 ≤ Bias441.unmasked c extra (d+1)
          linarith
        · by_cases hmask : mask B q hq = L.comp B.ker.subtype
          · have h0 := (hm 0).mpr (Or.inr hmask)
            have h1 := (hm u).mpr (Or.inr hmask)
            simp only [bound, h0, h1, Hm, ite_true, ite_false]
            have hh := Bias441.unmasked_next c hc extra d
            change (_ + _) / 2 ≤ Bias441.masked c (d+1)
            linarith
          · have h0 := (hm 0).not.mpr (not_or.mpr ⟨Hm, hmask⟩)
            have h1 := (hm u).not.mpr (not_or.mpr ⟨Hm, hmask⟩)
            simp only [bound, h0, h1, Hm, ite_false]
            have hh := Bias441.masked_mono c hc d
            change (_ + _) / 2 ≤ Bias441.masked c (d+1)
            linarith

end Upper441


namespace Lower441
open Phase441 Phase441SymplecticCoordinates Phase441QuadraticCoordinates Query441 TwoStageSplit
private abbrev F := ZMod 2

/- Character and product bias helpers ported from lean/PEqualNP/Outside/L_meta_29947.lean
   at 84686e3276044e3cadda1c4453d05f6445313e0f. The fiber equivalence is generalized. -/

private def character (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

private theorem character_add (x y : ZMod 2) :
    character (x + y) = character x * character y := by
  have all : ∀ a b : ZMod 2, character (a + b) = character a * character b := by decide
  exact all x y


private theorem character_sum {I : Type*} (s : Finset I) (f : I → F) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert a rest fresh ih =>
    rw [Finset.sum_insert fresh,Finset.prod_insert fresh,character_add,ih]

private theorem one_pair : (∑ q : F × F, character (q.1 * q.2)) = 2 := by decide

private theorem subset_bias {A : Type*} [Fintype A] (r k : ℕ) (S : Finset (Fin r)) (q : A → F)
    (coords : A ≃ (Fin r → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i ∈ S, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^S.card * (∑ x, character (q x)) = 2 ^ (2*r + k) := by
  classical
  let w (i : Fin r) (z : F × F) : ℤ := if i ∈ S then character (z.1 * z.2) else 1
  let a (i : Fin r) : ℤ := if i ∈ S then 2 else 1
  have count : (∏ i, a i) = (2 : ℤ)^S.card := by
    unfold a
    rw [Finset.prod_ite_mem_eq,Finset.prod_const]
  have term (z : Fin r → F × F) : character (∑ i ∈ S, (z i).1 * (z i).2) = ∏ i, w i (z i) := by
    rw [character_sum]
    unfold w
    rw [Finset.prod_ite_mem_eq]
  have product : (∏ i, a i * ∑ z, w i z) = (4 : ℤ)^r := by
    have pointwise (i : Fin r) : a i * (∑ z, w i z) = 4 := by
      by_cases h : i ∈ S
      · simp [a,w,h,one_pair]
      · simp [a,w,h,Fintype.card_prod,ZMod.card]
    simp only [pointwise,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have selected : (2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i)) = 4^r := by
    rw [← count, ← Fintype.prod_sum w, ← Finset.prod_mul_distrib]
    exact product
  have all : (∑ x, character (q x)) =
      ∑ p : (Fin r → F × F) × (Fin k → F), ∏ i, w i (p.1 i) := by
    apply Fintype.sum_equiv coords
    intro x
    rw [form,term]
  rw [all,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have free : (Fintype.card (Fin k → F) : ℤ) = 2^k := by
    simp [Fintype.card_fun,ZMod.card]
  rw [free]
  calc
    _ = (2 : ℤ)^k * ((2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i))) := by ring
    _ = (2 : ℤ)^(2*r+k) := by rw [selected,pow_add,pow_mul]; norm_num [mul_comm]

private noncomputable def split_fibers {A T : Type*} [AddCommGroup A] [Module F A] [AddCommGroup T] [Module F T] (G : A →ₗ[F] T)
    (surj : Function.Surjective G) : A ≃ T × LinearMap.ker G where
  toFun x := (G x,⟨x - (surj (G x)).choose, by
    rw [LinearMap.mem_ker,map_sub,(surj (G x)).choose_spec,sub_self]⟩)
  invFun y := y.2.val + (surj y.1).choose
  left_inv x := sub_add_cancel _ _
  right_inv := by
    rintro ⟨y,z⟩
    have h : G (z.val + (surj y).choose) = y := by
      rw [map_add,(surj y).choose_spec,LinearMap.mem_ker.mp z.property,zero_add]
    apply Prod.ext h
    apply Subtype.ext
    change z.val + (surj y).choose -
      (surj (G (z.val + (surj y).choose))).choose = z.val
    rw [h,add_sub_cancel_right]

variable {V : Type*} [AddCommGroup V] [Module F V]

private theorem bitEq (a b : F) : a = b ↔ a+b=0 :=
  (by decide : ∀ a b : F, a=b ↔ a+b=0) a b

private theorem repack {I : Type*} [Fintype I] {e : ℕ}
    (h : Fintype.card I ≤ e) (A : I → V →ₗ[F] F) :
    ∃ (L : V →ₗ[F] (Fin e → F)) (decode : (Fin e → F) → (I → F)),
      ∀ x i, decode (L x) i = A i x := by
  classical
  obtain ⟨E⟩ : Nonempty (I ↪ Fin e) := Function.Embedding.nonempty_of_card_le (by simpa using h)
  let R (i : Fin e) : V →ₗ[F] F := if h : ∃ j, E j = i then A h.choose else 0
  refine ⟨LinearMap.pi R, fun v i => v (E i), ?_⟩
  intro x i
  have hi : ∃ j, E j = E i := ⟨i,rfl⟩
  have hh : hi.choose = i := E.injective hi.choose_spec
  change R (E i) x = _
  simp [R, hi, hh]

private def pairMap {B : LinearMap.BilinForm F V} {m : ℕ} (D : Coordinates B m) :
    V →ₗ[F] (Fin m → F × F) where
  toFun x i := (D.left i x, D.right i x)
  map_add' x y := by ext i <;> simp
  map_smul' c x := by ext i <;> simp

private theorem pairMap_surj {B : LinearMap.BilinForm F V} {m : ℕ} (D : Coordinates B m) :
    Function.Surjective (pairMap D) := by
  intro xs
  obtain ⟨x,h⟩ := D.independent (fun i => (xs i).1, fun i => (xs i).2)
  refine ⟨x,?_⟩
  funext i
  exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

private theorem remainder_score [Fintype V] {B : LinearMap.BilinForm F V} {m : ℕ}
    (D : Coordinates B m) (S : Finset (Fin m)) (q s : V → F)
    (h : ∀ x, s x + q x = ∑ i ∈ S, D.left i x * D.right i x) :
    score q s = 1/(2 : ℚ)^S.card := by
  classical
  let G := pairMap D
  let R := G.ker
  let k := Module.finrank F R
  let E := (split_fibers G (pairMap_surj D)).trans
    ((Equiv.refl _).prodCongr (Module.finBasis F R).equivFun.toEquiv)
  have hform (x : V) : s x + q x = ∑ i ∈ S, ((E x).1 i).1 * ((E x).1 i).2 := h x
  have hs := subset_bias m k S (fun x => s x+q x) E hform
  have hCard : Fintype.card V = 2^(2*m+k) := by
    have hg := Fintype.card_congr E
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card] at hg
    rw [hg, pow_add, pow_mul]
    norm_num
    rfl
  have hs' : (2 : ℚ)^S.card * (∑ x : V, if s x = q x then (1 : ℚ) else -1) = Fintype.card V := by
    rw [hCard]
    have hg := congrArg (Int.cast : ℤ → ℚ) hs
    push_cast at hg ⊢
    simpa [character, ← bitEq] using hg
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold score
  apply (div_eq_div_iff (ne_of_gt hpos) (by positivity)).2
  linarith

private theorem select_pairs [Fintype V] {B : LinearMap.BilinForm F V} {m : ℕ}
    (D : Coordinates B m) (q : V → F) (c : F) {j b e : ℕ} (hj : j ≤ m) (he : 2*j+b ≤ e)
    (A : Fin b → V →ₗ[F] F)
    (h : ∀ x, q x = c + (∑ i, A i x) + quadraticPart D x) :
    ∃ (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F),
      score q (fun x => out (L x)) = 1/(2 : ℚ)^(m-j) := by
  classical
  let incl : Fin j ↪ Fin m := Fin.castLEEmb hj
  let I := (Fin j × Bool) ⊕ Fin b
  let ask : I → V →ₗ[F] F := Sum.elim
    (fun i => if i.2 then D.left (incl i.1) else D.right (incl i.1)) A
  have hcard : Fintype.card I ≤ e := by
    simpa only [I, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      Nat.mul_comm j 2] using he
  obtain ⟨L, dec, hdec⟩ := repack hcard ask
  let S : Finset (Fin m) := Finset.univ.map incl
  let out (v : Fin e → F) : F := c + (∑ i : Fin b, dec v (Sum.inr i)) +
    ∑ i : Fin j, dec v (Sum.inl (i,true)) * dec v (Sum.inl (i,false))
  have hC : Sᶜ.card = m-j := by simp [S, Finset.card_compl]
  refine ⟨L,out, (remainder_score D Sᶜ q (fun x => out (L x)) ?_).trans ?_⟩
  · intro x
    have hx : out (L x) = c + (∑ i, A i x) + ∑ i ∈ S, D.left i x * D.right i x := by
      simp [out, hdec, ask, S]
    have hsplit : quadraticPart D x =
        (∑ i ∈ S, D.left i x * D.right i x) + ∑ i ∈ Sᶜ, D.left i x * D.right i x := by
      have hd : Disjoint S Sᶜ := Finset.disjoint_left.mpr (by simp)
      rw [quadraticPart, ← Finset.sum_union hd, Finset.union_compl]
    rw [hx, h, hsplit]
    exact (by decide : ∀ a b c : F, (a+b)+(a+(b+c))=c) _ _ _
  · rw [hC]

private theorem score_translate [Fintype V] (q s : V → F) (v : V) :
    score q s = score (fun x => q (x+v)) (fun x => s (x+v)) := by
  unfold score
  congr 1
  exact (Fintype.sum_equiv (Equiv.addRight v) _ _ (fun _ => rfl)).symm

open Classical in
private theorem batchAttain [Fintype V] (q : V → F) (B : LinearMap.BilinForm F V)
    (hq : IsPhase q B) (m e : ℕ) (hr : polarRank B = 2*m) :
    ∃ (L : V →ₗ[F] (Fin e → F)) (out : (Fin e → F) → F),
      score q (fun x => out (L x)) = if mask B q hq = 0 then 1/(2 : ℚ)^(m-e/2)
        else if e = 0 then 0 else 1/(2 : ℚ)^(m-(e-1)/2) := by
  classical
  have alt := phase_alt hq
  have sym := phase_symm hq
  obtain ⟨D⟩ := normalForm m B alt sym hr
  have pol (u v : V) : q (u+v)+q u+q v+q 0=B u v := by simpa using hq 0 u v
  let ell := affineLinear D q pol
  have hshape := exact_decomposition D q pol
  by_cases hm : mask B q hq = 0
  · rw [if_pos hm]
    have van (r : B.ker) : ell r.val = 0 := by
      have hdiff : q r.val + q 0 = 0 := by rw [← mask_apply B q hq, hm, LinearMap.zero_apply]
      have hpair : quadraticPart D r.val = 0 := by
        have H := LinearMap.mem_ker.mp r.property
        apply Finset.sum_eq_zero
        intro i _
        have hL : D.left i r.val = 0 := by
          obtain ⟨x,hx⟩ := D.independent (0, Pi.single i 1)
          have hl : (fun j => D.left j x) = 0 := congrArg Prod.fst hx
          have hh : (fun j => D.right j x) = Pi.single i 1 := congrArg Prod.snd hx
          have hz : B r.val x = 0 := DFunLike.congr_fun H x
          rw [D.product] at hz
          change (∑ j, (D.left j r.val * (fun k => D.right k x) j +
            D.right j r.val * (fun k => D.left k x) j)) = 0 at hz
          rw [hh, hl] at hz
          simpa [Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using hz
        simp [hL]
      change q r.val + q 0 + quadraticPart D r.val = 0
      rw [hdiff, hpair, zero_add]
    obtain ⟨v, hv⟩ := TwoStageSplit.query_in_range B alt ell van
    let q' (x : V) := q (x+v)
    have hq' (x : V) : q' x = q v + (∑ i : Fin 0, (0 : V →ₗ[F] F) x) + quadraticPart D x := by
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      have hB : B x v = ell x := (sym x v).trans (DFunLike.congr_fun hv x)
      have h := pol x v
      rw [hB, hshape x] at h
      change q (x+v) = _
      exact (by decide : ∀ a b c d e : F, a+(b+c+d)+e+b=c → a=e+d) _ _ _ _ _ h
    let j := min m (e/2)
    obtain ⟨L,out,hout⟩ := select_pairs D q' (q v) (j := j) (b := 0) (e := e)
      (min_le_left _ _) (by dsimp [j]; omega) (fun _ => 0) hq'
    refine ⟨L, fun y => out (y - L v), ?_⟩
    rw [score_translate q _ v]
    simp only [L.map_add, add_sub_cancel_right]
    have hj : m-j = m-(e/2) := by dsimp [j]; omega
    simpa only [hj] using hout
  · rw [if_neg hm]
    by_cases he : e = 0
    · subst e
      simp only [ite_true]
      obtain ⟨r, hr⟩ := (Upper441.masked_iff q B hq).mpr hm
      refine ⟨0, fun _ => 0, ?_⟩
      have hz := BatchUpper.shift_cancel q B hq (0 : V →ₗ[F] (Fin 0 → F)) (fun _ => 0) r hr rfl
      have hz' := congrArg (Int.cast : ℤ → ℚ) hz
      push_cast at hz'
      unfold score
      rw [show (∑ x : V, if (0 : F) = q x then (1 : ℚ) else -1) = 0 by
        simpa [BatchUpper.sign, eq_comm] using hz', zero_div]
    · rw [if_neg he]
      let j := min m ((e-1)/2)
      obtain ⟨L,out,hout⟩ := select_pairs D q (q 0) (j := j) (b := 1) (e := e)
        (min_le_left _ _) (by dsimp [j]; omega) (fun _ => ell)
        (fun x => by simpa using hshape x)
      refine ⟨L,out,?_⟩
      have hj : m-j = m-((e-1)/2) := by dsimp [j]; omega
      simpa only [hj] using hout

end Lower441


namespace Attain441
open Phase441 Query441 TwoStageSplit Upper441 Lower441
private abbrev F := ZMod 2

private theorem base_bound (e m : ℕ) (he : 0 < e) (p : Prop) :
    bound e 0 m p = open Classical in if p then 1/(2 : ℚ)^(m-e/2) else 1/2^(m-(e-1)/2) := by
  classical
  by_cases hp : p
  · simp [bound, hp, Bias441.posted_formula m 0 e he]
  · simp [bound, hp, Bias441.masked_formula]

private theorem zero_bound (e d : ℕ) (he : 0 < e) (p : Prop) : bound e d 0 p = 1 := by
  classical
  by_cases hp : p
  · simp [bound, hp, Bias441.posted_formula 0 d e he]
  · simp [bound, hp, Bias441.masked_formula]

private theorem rank_zero {V : Type*} [AddCommGroup V] [Module F V] :
    polarRank (0 : LinearMap.BilinForm F V) = 0 := by
  have hh : LinearMap.range (0 : LinearMap.BilinForm F V) = ⊥ :=
    LinearMap.range_eq_bot.mpr rfl
  change Module.finrank F (LinearMap.range (0 : LinearMap.BilinForm F V)) = 0
  rw [hh, finrank_bot]

private theorem attain (e : ℕ) (he : 0 < e) :
    ∀ (d : ℕ) {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
      (B : LinearMap.BilinForm F V) (alt : ∀ x, B x x = 0),
      ∃ (P : V →ₗ[F] (Fin d → F)), ∀ (q : V → F) (hq : IsPhase q B),
      ∃ (N : (Fin d → F) → V →ₗ[F] (Fin e → F)) (O : (Fin d → F) → (Fin e → F) → F),
      score q (fun x => O (P x) (N (P x) x)) = bound e d (polarRank B/2) (mask B q hq = 0) := by
  classical
  intro d
  induction d with
  | zero =>
    intro V _ _ _ B alt
    refine ⟨0,?_⟩
    intro q hq
    obtain ⟨m, hm⟩ := rank_even (polarRank B) B alt (phase_symm hq) rfl
    have hh : polarRank B/2 = m := by omega
    obtain ⟨L,out,hout⟩ := batchAttain q B hq m e hm
    refine ⟨fun _ => L, fun _ => out,?_⟩
    rw [hh, base_bound e m he]
    simpa [he.ne'] using hout
  | succ d ih =>
    intro V _ _ _ B alt
    by_cases hB : B = 0
    · subst B
      refine ⟨0,?_⟩
      intro q hq
      obtain ⟨L,out,hout⟩ := batchAttain q 0 hq 0 e (by simp [rank_zero])
      refine ⟨fun _ => L, fun _ => out,?_⟩
      rw [rank_zero, Nat.zero_div, zero_bound e (d+1) he]
      simpa [he.ne'] using hout
    · obtain ⟨v, hv⟩ : ∃ x, B x ≠ 0 := by
        by_contra! h
        exact hB (LinearMap.ext h)
      let L := B v
      obtain ⟨u, hu⟩ := unitVector L hv
      let C := B.restrict L.ker
      have hC (x : L.ker) : C x x = 0 := alt x.val
      obtain ⟨P, useP⟩ := ih C hC
      refine ⟨combineFirst L u hu P,?_⟩
      intro q hq
      let q' (t : F) (x : L.ker) := q ((t • u)+x.val)
      have hp (t : F) : IsPhase (q' t) C := restrictPolar B L q hq (t • u)
      have spec (t : F) := useP (q' t) (hp t)
      choose N O hNO using spec
      obtain ⟨N',O',hs⟩ := combine_strategy L u hu P N O
      refine ⟨N',O',?_⟩
      let s (x : V) := O' (combineFirst L u hu P x) (N' (combineFirst L u hu P x) x)
      have all (t : F) : score (fun x : L.ker => q (x.val+t • u)) (fun x => s (x.val+t • u)) =
          bound e d (polarRank C/2) (unmaskedAt B L q (t • u)) := by
        rw [unmaskedAt_iff B L q hq (t • u)]
        have H (x : L.ker) : s (x.val+t • u) = O t (P x) (N t (P x) x) := hs t x
        rw [show (fun x : L.ker => s (x.val+t • u)) = _ from funext H]
        simpa only [q', C, add_comm (t • u)] using hNO t
      have h0 := all 0
      have h1 := all 1
      simp only [zero_smul, add_zero] at h0
      simp only [one_smul] at h1
      change score q s = _
      rw [score_split L u hu, h0, h1]
      obtain ⟨split, _⟩ := query_split B alt q hq L hu
      have hzero : L.comp B.ker.subtype = 0 := by
        ext r
        change B v r.val = 0
        exact (phase_symm hq _ _).trans (DFunLike.congr_fun (LinearMap.mem_ker.mp r.property) v)
      obtain ⟨hr, hm, hn⟩ := split hzero
      rw [hr]
      have hc := Bias441.core_step (polarRank C/2) ((e-1)/2)
      by_cases hmask : mask B q hq = 0
      · rcases hm.mpr hmask with h | h
        · have h' : ¬ unmaskedAt B L q u := fun hh => hn ⟨h,hh⟩
          simp only [bound, h, h', hmask, ite_true, ite_false]
          exact Bias441.split_exact _ _ _ _
        · have h' : ¬ unmaskedAt B L q 0 := fun hh => hn ⟨hh,h⟩
          simp only [bound, h, h', hmask, ite_true, ite_false]
          rw [add_comm]
          exact Bias441.split_exact _ _ _ _
      · have h0 : ¬ unmaskedAt B L q 0 := fun h => hmask (hm.mp (Or.inl h))
        have h1 : ¬ unmaskedAt B L q u := fun h => hmask (hm.mp (Or.inr h))
        simp only [bound, h0, h1, hmask, ite_false]
        rw [hc, Bias441.masked_step]
        ring

end Attain441


namespace Bridge441
open Phase441 Query441 TwoStageSplit Upper441
private abbrev F := ZMod 2

private theorem count_iff {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (q s : V → F) (p : ℚ) :
    p*(Nat.card V : ℚ) ≤ (Nat.card {x : V // s x = q x} : ℚ) ↔
      p ≤ (1+score q s)/2 := by
  classical
  let H := (Finset.univ : Finset V).filter (fun x => s x = q x)
  have hc : Nat.card {x : V // s x = q x} = H.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hs : (∑ x : V, if s x = q x then (1 : ℚ) else -1) = 2*(H.card : ℚ) - Fintype.card V := by
    calc
      _ = ∑ x : V, (2*(if s x = q x then (1 : ℚ) else 0)-1) := by
        apply Finset.sum_congr rfl
        intro x _
        split <;> norm_num
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
        simp [H]
  have hp : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [Nat.card_eq_fintype_card, hc, score, hs]
  have hh : (1+(2*(H.card : ℚ)-Fintype.card V)/Fintype.card V)/2 =
      (H.card : ℚ)/Fintype.card V := by
    field_simp
    ring
  rw [hh, le_div_iff₀ hp]

private theorem polar_card {V : Type*} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) :
    Nat.card {u : V // ∀ v : V, B u v = 0} = Nat.card B.ker := by
  exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (TwoStageSplit.rad_mem B u).symm)

private theorem period_card {V : Type*} [AddCommGroup V] [Module F V] [Fintype V]
    (q : V → F) (B : LinearMap.BilinForm F V) (hq : IsPhase q B) :
    Nat.card {u : V // ∀ p : V, q (p+u)=q p} = Nat.card B.ker ↔ mask B q hq = 0 := by
  classical
  let A := {u : V // ∀ p : V, q (p+u)=q p}
  let E : A → B.ker := fun u => ⟨u.val, ((BatchUpper.period_iff q B hq u.val).mp u.property).1⟩
  have hinj : Function.Injective E :=
    fun _ _ h => Subtype.ext (congrArg (fun r : B.ker => r.val) h)
  have hsurj : Function.Surjective E ↔ mask B q hq = 0 := by
    constructor
    · intro hs
      by_contra! hm
      obtain ⟨r,hr⟩ := (masked_iff q B hq).mpr hm
      obtain ⟨a,ha⟩ := hs r
      have hv : a.val = r.val := congrArg (fun z : B.ker => z.val) ha
      exact hr (hv ▸ (by simpa using a.property 0 : q a.val = q 0))
    · intro hm r
      have hmask : q r.val = q 0 := by
        by_contra hn
        exact ((masked_iff q B hq).mp ⟨r,hn⟩) hm
      exact ⟨⟨r.val, (BatchUpper.period_iff q B hq r.val).mpr ⟨r.property,hmask⟩⟩, Subtype.ext rfl⟩
  change Nat.card A = Nat.card B.ker ↔ _
  rw [← hsurj, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact ⟨fun h => by
      by_contra hn
      exact (Fintype.card_lt_of_injective_not_surjective E hinj hn).ne h,
    fun h => Fintype.card_congr (Equiv.ofBijective E ⟨hinj,h⟩)⟩

end Bridge441


end PEqualNP.Outside.L_pcx_441_aux

open PEqualNP.Outside.L_pcx_441_aux in
open Phase441 Query441 TwoStageSplit Upper441 Bridge441 in
theorem PEqualNP.Outside.L_pcx_441 :
∀ (n : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  ∀ (f : X → F),
    let B := fun u v : X => f (u+v)+f u+f v+f 0
    (∀ p u v : X, f (p+u+v)+f (p+u)+f (p+v)+f p = B u v) →
    let U := fun (m j : ℕ) => (1 : ℚ)/2^(m-j/2)
    let M := fun (m j : ℕ) => if j=0 then (0 : ℚ) else 1/2^(m-(j-1)/2)
    let g := Nat.card {u : X // ∀ v : X, B u v = 0}
    let k := Nat.card {u : X // ∀ p : X, f (p+u) = f p}
    let m := (n-g.log2)/2
    ∀ d e : ℕ,
      let a := min d m
      let residual := m-a
      let bias := if e=0 then (if k=g then U m d else M m d)
        else if k=g then (U residual e + ((2 : ℚ)^a-1)*M residual e)/2^a
        else M residual e
      ∀ p : ℚ, (∃ (first : X →ₗ[F] (Fin d → F))
        (second : (Fin d → F) → X →ₗ[F] (Fin e → F))
        (out : (Fin d → F) → (Fin e → F) → F),
        p*(Nat.card X : ℚ) ≤ (Nat.card {x : X //
          out (first x) (second (first x) x) = f x} : ℚ)) ↔ p ≤ (1+bias)/2 := by
  classical
  intro n F X f b h U M g k m d e a residual bias p
  let B := polarMap f h
  have hq : IsPhase f B := h
  have hg : g = Nat.card B.ker := by
    change Nat.card {u : X // ∀ v : X, B u v = 0} = Nat.card B.ker
    exact polar_card B
  have hk : k = g ↔ mask B f hq = 0 := by
    rw [hg]
    exact period_card f B hq
  have hdim : Module.finrank F X = n := by simp [X]
  have hglog : g.log2 = Module.finrank F B.ker := by
    rw [hg, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F), ZMod.card, Nat.log2_two_pow]
  have hden := B.finrank_range_add_finrank_ker
  have hdiff : Module.finrank F X - Module.finrank F B.ker = polarRank B := by
    change polarRank B + Module.finrank F B.ker = Module.finrank F X at hden
    omega
  have hm : m = polarRank B/2 := by
    calc
      m = (n - g.log2)/2 := rfl
      _ = (Module.finrank F X - g.log2)/2 := congrArg (fun v => (v-g.log2)/2) hdim.symm
      _ = (Module.finrank F X - Module.finrank F B.ker)/2 :=
        congrArg (fun v => (Module.finrank F X-v)/2) hglog
      _ = polarRank B/2 := congrArg (· / 2) hdiff
  have hr : polarRank B = 2*m := by
    obtain ⟨j,hj⟩ := rank_even (polarRank B) B (phase_alt hq) (phase_symm hq) rfl
    omega
  have hrd : Module.finrank F X - Module.finrank F B.ker = 2*m := hdiff.trans hr
  have hmax : ∀ (P : X →ₗ[F] (Fin d → F)) (N : (Fin d → F) → X →ₗ[F] (Fin e → F))
      (O : (Fin d → F) → (Fin e → F) → F),
      score f (fun x => O (P x) (N (P x) x)) ≤ bias := by
    intro P N O
    by_cases he : e = 0
    · haveI : Subsingleton (Fin e → F) := by rw [he]; infer_instance
      have h0 (x : X) : N (P x) x = 0 := Subsingleton.elim _ _
      have hs := BatchUpper.oneBatch f B hq hrd P (fun y => O y 0)
      change score f (fun x => O (P x) 0) ≤ _ at hs
      simp only [masked_iff f B hq] at hs
      simpa [bias, he, hk, U, M, h0] using hs
    · have hbound : bound e d (polarRank B/2) (mask B f hq = 0) = bias := by
        rw [← hm]
        by_cases hm0 : mask B f hq = 0
        · simp [bound, bias, he, hk, hm0, U, M, a, residual, Bias441.posted_formula m d e (by omega)]
        · simp [bound, bias, he, hk, hm0, M, a, residual, Bias441.masked_formula]
      rw [← hbound]
      exact upper e (by omega) d f B hq P N O
  have hbest : ∃ (P : X →ₗ[F] (Fin d → F)) (N : (Fin d → F) → X →ₗ[F] (Fin e → F))
      (O : (Fin d → F) → (Fin e → F) → F),
      score f (fun x => O (P x) (N (P x) x)) = bias := by
    by_cases he : e = 0
    · obtain ⟨P,O,hO⟩ := Lower441.batchAttain f B hq m d hr
      refine ⟨P,fun _ => 0,fun a _ => O a,?_⟩
      simpa [bias, he, hk, U, M] using hO
    · obtain ⟨P,hP⟩ := Attain441.attain e (by omega) d B (phase_alt hq)
      obtain ⟨N,O,hO⟩ := hP f hq
      refine ⟨P,N,O,hO.trans ?_⟩
      rw [← hm]
      by_cases hm0 : mask B f hq = 0
      · simp [bound, bias, he, hk, hm0, U, M, a, residual, Bias441.posted_formula m d e (by omega)]
      · simp [bound, bias, he, hk, hm0, M, a, residual, Bias441.masked_formula]
  constructor
  · rintro ⟨P,N,O,h⟩
    have hp := (count_iff f (fun x => O (P x) (N (P x) x)) p).mp h
    linarith [hmax P N O]
  · intro hp
    obtain ⟨P,N,O,h⟩ := hbest
    refine ⟨P,N,O,(count_iff f (fun x => O (P x) (N (P x) x)) p).mpr ?_⟩
    rw [h]
    exact hp
