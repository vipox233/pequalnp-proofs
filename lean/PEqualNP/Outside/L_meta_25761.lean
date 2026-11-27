import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25761_aux

open scoped BigOperators

section Core

variable {k : ℕ} (hk : 0 < k)

private abbrev F := ZMod 2
private abbrev W (k : ℕ) := Fin k → ZMod 2

private lemma z2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma z2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

private lemma z2_sum_four (a : ZMod 2) : a + a + a + a = 0 := by
  fin_cases a <;> decide

private lemma z2_vec_add_self (u : W k) : u + u = 0 := by
  funext i; exact z2_add_self (u i)

private lemma z2_vec_eq_of_add_eq_zero {u v : W k} (h : u + v = 0) : u = v := by
  funext i
  have hi := congrFun h i
  simp only [Pi.add_apply, Pi.zero_apply] at hi
  generalize u i = a at hi
  generalize v i = b at hi
  fin_cases a <;> fin_cases b <;> first | rfl | exact absurd hi (by decide)

private lemma sub_mod_add_mod_self (hk : 0 < k) (c : ℕ) : (k - c % k + c) % k = 0 := by
  have hck : c % k < k := Nat.mod_lt c hk
  have h1 : (k - c % k + c) % k = (k - c % k + c % k) % k := by
    rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  rw [h1, show k - c % k + c % k = k by omega, Nat.mod_self]

private lemma add_mod_cancel (hk : 0 < k) (a b c : ℕ) (h : (a + c) % k = (b + c) % k) :
    a % k = b % k := by
  have h' : (a + c + (k - c % k)) % k = (b + c + (k - c % k)) % k := by
    rw [Nat.add_mod, h, ← Nat.add_mod]
  have hc : (c + (k - c % k)) % k = 0 := by
    rw [Nat.add_comm]; exact sub_mod_add_mod_self hk c
  rw [Nat.add_assoc, Nat.add_mod, hc, Nat.add_zero, Nat.mod_mod] at h'
  rw [Nat.add_assoc, Nat.add_mod, hc, Nat.add_zero, Nat.mod_mod] at h'
  exact h'

private def ix (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

private def shift (i : Fin k) (t : ℕ) : Fin k := ix hk (i.val + t)

private def bshift (i : Fin k) (t : ℕ) : Fin k := ix hk (i.val + k - t % k)

private lemma shift_zero (i : Fin k) : shift hk i 0 = i := by
  apply Fin.ext
  simp [shift, ix, Nat.mod_eq_of_lt i.isLt]

private lemma shift_add (i : Fin k) (a b : ℕ) :
    shift hk (shift hk i a) b = shift hk i (a + b) := by
  apply Fin.ext
  simp only [shift, ix]
  rw [Nat.mod_add_mod, Nat.add_assoc]

private lemma bshift_eq_shift (i : Fin k) (t : ℕ) :
    bshift hk i t = shift hk i (k - t % k) := by
  apply Fin.ext
  simp only [bshift, shift, ix]
  have hlt : t % k < k := Nat.mod_lt t hk
  congr 1; omega

private lemma shift_bshift (i : Fin k) (t : ℕ) :
    shift hk (bshift hk i t) t = i := by
  rw [bshift_eq_shift, shift_add]
  apply Fin.ext
  simp only [shift, ix]
  have hlt : t % k < k := Nat.mod_lt t hk
  have h1 : (i.val + (k - t % k + t)) % k = (i.val + (k - t % k + t % k)) % k := by
    rw [Nat.add_mod, Nat.add_mod (k - t % k) t]
    conv_rhs => rw [Nat.add_mod, Nat.add_mod (k - t % k) (t % k), Nat.mod_mod]
  rw [h1]
  have h2 : k - t % k + t % k = k := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

private lemma bshift_shift (i : Fin k) (t : ℕ) :
    bshift hk (shift hk i t) t = i := by
  rw [bshift_eq_shift, shift_add]
  apply Fin.ext
  simp only [shift, ix]
  have hlt : t % k < k := Nat.mod_lt t hk
  have h1 : (i.val + (t + (k - t % k))) % k = (i.val + (t % k + (k - t % k))) % k := by
    rw [Nat.add_mod, Nat.add_mod t (k - t % k)]
    conv_rhs => rw [Nat.add_mod, Nat.add_mod (t % k) (k - t % k), Nat.mod_mod]
  rw [h1]
  have h2 : t % k + (k - t % k) = k := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

private lemma shift_inj (i : Fin k) {a b : ℕ} (ha : a < k) (hb : b < k)
    (h : shift hk i a = shift hk i b) : a = b := by
  have hv : (i.val + a) % k = (i.val + b) % k := congrArg Fin.val h
  have h1 : (i.val + a + (k - i.val)) % k = (i.val + b + (k - i.val)) % k := by
    rw [Nat.add_mod, hv, ← Nat.add_mod]
  have hi : i.val < k := i.isLt
  have h2 : i.val + a + (k - i.val) = a + k := by omega
  have h3 : i.val + b + (k - i.val) = b + k := by omega
  rw [h2, h3, Nat.add_mod_right, Nat.add_mod_right,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact h1

private lemma shift_mod (i : Fin k) (a : ℕ) : shift hk i (a % k) = shift hk i a := by
  apply Fin.ext
  simp only [shift, ix]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma shift_eq_iff (i : Fin k) (a b : ℕ) :
    shift hk i a = shift hk i b ↔ a % k = b % k := by
  constructor
  · intro h
    rw [← shift_mod hk i a, ← shift_mod hk i b] at h
    exact shift_inj hk i (Nat.mod_lt a hk) (Nat.mod_lt b hk) h
  · intro h
    rw [← shift_mod hk i a, ← shift_mod hk i b, h]

private lemma bshift_eq_shift_sub (i : Fin k) {t : ℕ} (ht : t ≤ k) :
    bshift hk i t = shift hk i (k - t) := by
  by_cases htk : t = k
  · subst htk; rw [bshift_eq_shift]; simp [Nat.mod_self, shift, ix, Nat.mod_eq_of_lt i.isLt]
  · rw [bshift_eq_shift, Nat.mod_eq_of_lt (by omega)]

private def rot (offset : ℕ) (w : W k) (j : Fin k) : ZMod 2 :=
  w (ix hk (j.val + k - offset % k))

private def mix (d : ℕ) (word : W k) (mid : Fin k) : ZMod 2 :=
  word mid + word (ix hk (mid.val + d)) + word (ix hk (mid.val + k - d % k))

private def chi (z : W k) (dest : Fin k) : ZMod 2 :=
  z dest + (1 + z (ix hk (dest.val + 1))) * z (ix hk (dest.val + 2))

private def polar (u v : W k) (dest : Fin k) : ZMod 2 :=
  u (ix hk (dest.val + 1)) * v (ix hk (dest.val + 2)) +
  u (ix hk (dest.val + 2)) * v (ix hk (dest.val + 1))

private def unit (pos coord : Fin k) : ZMod 2 :=
  if coord = pos then 1 else 0

private def B (d : ℕ) (u v : W k) : W k :=
  polar hk (mix hk d u) (mix hk d v)

private lemma rot_add (offset : ℕ) (u v : W k) :
    rot hk offset (u + v) = rot hk offset u + rot hk offset v := by
  funext j; rfl

private lemma rot_eq_zero_iff (offset : ℕ) (u : W k) :
    rot hk offset u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    have h1 := congrFun h (shift hk i offset)
    simp only [rot, Pi.zero_apply] at h1
    change u (bshift hk (shift hk i offset) offset) = 0 at h1
    rw [bshift_shift] at h1
    exact h1
  · rintro rfl; funext j; rfl

private lemma rot_unit (offset : ℕ) (p : Fin k) :
    rot hk offset (unit p) = unit (shift hk p offset) := by
  funext j
  simp only [rot, unit]
  have hiff : bshift hk j offset = p ↔ j = shift hk p offset := by
    constructor
    · rintro rfl; exact (shift_bshift hk j offset).symm
    · rintro rfl; exact bshift_shift hk p offset
  change (if bshift hk j offset = p then (1 : ZMod 2) else 0) = _
  simp [hiff]

private lemma mix_add (d : ℕ) (u v : W k) :
    mix hk d (u + v) = mix hk d u + mix hk d v := by
  funext j; simp only [mix, Pi.add_apply]; ring

private lemma mix_smul (d : ℕ) (c : ZMod 2) (u : W k) :
    mix hk d (c • u) = c • mix hk d u := by
  funext j; simp only [mix, Pi.smul_apply, smul_eq_mul]; ring

private lemma mix_zero (d : ℕ) : mix hk d 0 = 0 := by
  funext j; simp [mix]

private lemma polar_add_left (u₁ u₂ v : W k) :
    polar hk (u₁ + u₂) v = polar hk u₁ v + polar hk u₂ v := by
  funext j; simp only [polar, Pi.add_apply]; ring

private lemma polar_add_right (u v₁ v₂ : W k) :
    polar hk u (v₁ + v₂) = polar hk u v₁ + polar hk u v₂ := by
  funext j; simp only [polar, Pi.add_apply]; ring

private lemma polar_smul_left (c : ZMod 2) (u v : W k) :
    polar hk (c • u) v = c • polar hk u v := by
  funext j; simp only [polar, Pi.smul_apply, smul_eq_mul]; ring

private lemma polar_smul_right (c : ZMod 2) (u v : W k) :
    polar hk u (c • v) = c • polar hk u v := by
  funext j; simp only [polar, Pi.smul_apply, smul_eq_mul]; ring

private lemma polar_zero_left (v : W k) : polar hk 0 v = 0 := by
  funext j; simp [polar]

private lemma B_add_left (d : ℕ) (u₁ u₂ v : W k) :
    B hk d (u₁ + u₂) v = B hk d u₁ v + B hk d u₂ v := by
  simp only [B, mix_add, polar_add_left]

private lemma B_add_right (d : ℕ) (u v₁ v₂ : W k) :
    B hk d u (v₁ + v₂) = B hk d u v₁ + B hk d u v₂ := by
  simp only [B, mix_add, polar_add_right]

private lemma B_smul_left (d : ℕ) (c : ZMod 2) (u v : W k) :
    B hk d (c • u) v = c • B hk d u v := by
  simp only [B, mix_smul, polar_smul_left]

private lemma B_smul_right (d : ℕ) (c : ZMod 2) (u v : W k) :
    B hk d u (c • v) = c • B hk d u v := by
  simp only [B, mix_smul, polar_smul_right]

private lemma B_zero_left (d : ℕ) (v : W k) : B hk d 0 v = 0 := by
  simp only [B, mix_zero, polar_zero_left]

private lemma B_sum_left {α : Type*} (d : ℕ) (S : Finset α) (f : α → W k) (v : W k) :
    B hk d (∑ a ∈ S, f a) v = ∑ a ∈ S, B hk d (f a) v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [B_zero_left]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, B_add_left, ih, Finset.sum_insert ha]

private lemma B_sum_right {α : Type*} (d : ℕ) (S : Finset α) (u : W k) (f : α → W k) :
    B hk d u (∑ a ∈ S, f a) = ∑ a ∈ S, B hk d u (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => funext j; simp [B, mix_zero, polar]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, B_add_right, ih, Finset.sum_insert ha]

private lemma chi_add (a b : W k) :
    chi hk (a + b) = chi hk a + chi hk b + polar hk a b := by
  funext j
  simp only [chi, polar, Pi.add_apply]
  ring

private lemma chi_mix_diff1 (d : ℕ) (x u : W k) :
    chi hk (mix hk d (x + u)) + chi hk (mix hk d x) =
    chi hk (mix hk d u) + B hk d x u := by
  rw [mix_add, chi_add]
  funext j
  simp only [B, Pi.add_apply]
  have h := z2_add_self (chi hk (mix hk d x) j)
  linear_combination h

private lemma chi_mix_diff2 (d : ℕ) (x u w : W k) :
    chi hk (mix hk d (x + u + w)) + chi hk (mix hk d (x + u)) +
    chi hk (mix hk d (x + w)) + chi hk (mix hk d x) = B hk d u w := by
  have h1 := chi_mix_diff1 hk d (x + u) w
  have h2 := chi_mix_diff1 hk d x w
  have hsum : (chi hk (mix hk d (x + u + w)) + chi hk (mix hk d (x + u))) +
      (chi hk (mix hk d (x + w)) + chi hk (mix hk d x)) =
      (chi hk (mix hk d w) + B hk d (x + u) w) + (chi hk (mix hk d w) + B hk d x w) := by
    rw [h1, h2]
  rw [B_add_left] at hsum
  funext j
  have hj := congrFun hsum j
  simp only [Pi.add_apply] at hj ⊢
  have h2a := z2_add_self (chi hk (mix hk d w) j)
  have h2b := z2_add_self (B hk d x w j)
  linear_combination hj + h2a + h2b

private lemma vec_eq_sum_units (u : W k) :
    u = ∑ p : Fin k, u p • unit p := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, unit, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ j u]
  simp

/-! ## Step 1: Invertibility of `mix` when `k % 3 ≠ 0` -/

private lemma mix_injective {d : ℕ} (hk3 : k % 3 ≠ 0) :
    Function.Injective (mix hk d) := by
  have hker : ∀ w : W k, mix hk d w = 0 → w = 0 := by
    intro w hw
    have hstep : ∀ i : Fin k, w (shift hk i (2 * d)) = w (shift hk i d) + w i := by
      intro i
      have h0 := congrFun hw (shift hk i d)
      simp only [mix, Pi.zero_apply] at h0
      change w (shift hk i d) + w (shift hk (shift hk i d) d) +
        w (bshift hk (shift hk i d) d) = 0 at h0
      rw [shift_add, bshift_shift] at h0
      have h2d : d + d = 2 * d := by omega
      rw [h2d] at h0
      have hadd := z2_add_self (w (shift hk i (2 * d)))
      linear_combination -h0 + hadd
    have hper3 : ∀ i : Fin k, w (shift hk i (3 * d)) = w i := by
      intro i
      have h1 : shift hk i (3 * d) = shift hk (shift hk i d) (2 * d) := by
        rw [shift_add]; congr 1; omega
      rw [h1, hstep (shift hk i d), shift_add]
      have h2d : d + d = 2 * d := by omega
      rw [h2d, hstep i]
      have hself := z2_add_self (w (shift hk i d))
      linear_combination hself
    have hper3m : ∀ m : ℕ, ∀ i : Fin k, w (shift hk i (m * (3 * d))) = w i := by
      intro m
      induction m with
      | zero => intro i; simp [shift_zero]
      | succ m ih =>
        intro i
        have h1 : (m + 1) * (3 * d) = m * (3 * d) + 3 * d := by ring
        rw [h1, ← shift_add, hper3, ih]
    have hcop : Nat.Coprime 3 k := by
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hdvd
      exact hk3 (Nat.mod_eq_zero_of_dvd hdvd)
    obtain ⟨a, ha⟩ : ∃ a : ℕ, (3 * a) % k = 1 % k := by
      use (3 : ZMod k)⁻¹.val
      have : NeZero k := ⟨Nat.ne_of_gt hk⟩
      have hu : IsUnit (3 : ZMod k) := (ZMod.isUnit_iff_coprime 3 k).mpr hcop
      have hmul : (3 : ZMod k) * (3 : ZMod k)⁻¹ = 1 := ZMod.mul_inv_of_unit 3 hu
      have hv := congrArg ZMod.val hmul
      rw [ZMod.val_mul, show (3 : ZMod k) = ((3 : ℕ) : ZMod k) from rfl,
        ← Nat.cast_one (R := ZMod k),
        ZMod.val_natCast, ZMod.val_natCast] at hv
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod] at hv
      exact hv
    have hd_eq : ∀ i : Fin k, w (shift hk i d) = w i := by
      intro i
      have hmod : (a * (3 * d)) % k = d % k := by
        have h1 : a * (3 * d) = (3 * a) * d := by ring
        rw [h1, Nat.mul_mod, ha, ← Nat.mul_mod, Nat.one_mul]
      rw [← shift_mod hk i d, ← hmod, shift_mod, hper3m a i]
    funext i
    simp only [Pi.zero_apply]
    have h0 := congrFun hw i
    simp only [mix, Pi.zero_apply] at h0
    change w i + w (shift hk i d) + w (bshift hk i d) = 0 at h0
    have hb : w (bshift hk i d) = w i := by
      have := hd_eq (bshift hk i d)
      rw [shift_bshift] at this
      exact this.symm
    rw [hd_eq i, hb] at h0
    have hself := z2_add_self (w i)
    linear_combination h0 - hself
  intro u v huv
  apply z2_vec_eq_of_add_eq_zero
  apply hker
  rw [mix_add, huv, z2_vec_add_self]

private lemma mix_surjective {d : ℕ} (hk3 : k % 3 ≠ 0) :
    Function.Surjective (mix hk d) :=
  Finite.surjective_of_injective (mix_injective hk hk3)

/-! ## Step 2: Reachability Subspaces and `P_chi(mix u, V)` Step Lemma -/

private def iterB (d : ℕ) : ∀ {r : ℕ}, W k → (Fin r → Fin k) → W k
  | 0, u₀, _ => u₀
  | r + 1, u₀, p => B hk d (iterB d u₀ (fun i => p i.castSucc)) (unit (p (Fin.last r)))

private def Reach (d : ℕ) (r : ℕ) (u₀ : W k) : Submodule (ZMod 2) (W k) :=
  Submodule.span (ZMod 2) (Set.range (iterB hk d (r := r) u₀))

private lemma self_mem_reach0 (d : ℕ) (u₀ : W k) : u₀ ∈ Reach hk d 0 u₀ := by
  apply Submodule.subset_span
  exact ⟨Fin.elim0, rfl⟩

private lemma B_unit_mem_reach_succ (d r : ℕ) (u₀ : W k) {u : W k}
    (hu : u ∈ Reach hk d r u₀) (p : Fin k) :
    B hk d u (unit p) ∈ Reach hk d (r + 1) u₀ := by
  let L : W k →ₗ[ZMod 2] W k :=
    { toFun := fun x => B hk d x (unit p)
      map_add' := fun x y => B_add_left hk d x y (unit p)
      map_smul' := fun c x => B_smul_left hk d c x (unit p) }
  change L u ∈ Reach hk d (r + 1) u₀
  have hle : Submodule.map L (Reach hk d r u₀) ≤ Reach hk d (r + 1) u₀ := by
    rw [Reach, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨ps, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨Fin.snoc (α := fun _ => Fin k) ps p, ?_⟩
    dsimp [L, iterB]
    have h1 : (fun i : Fin r => Fin.snoc (α := fun _ => Fin k) ps p i.castSucc) = ps := by
      funext i; simp
    rw [h1]
    simp
  exact hle ⟨u, hu, rfl⟩

private lemma polar_mem_reach_succ {d : ℕ} (hk3 : k % 3 ≠ 0) (r : ℕ) (u₀ : W k)
    {u : W k} (hu : u ∈ Reach hk d r u₀) (V : W k) :
    polar hk (mix hk d u) V ∈ Reach hk d (r + 1) u₀ := by
  obtain ⟨c, hc⟩ := mix_surjective hk hk3 V
  rw [← hc]
  change B hk d u c ∈ Reach hk d (r + 1) u₀
  rw [vec_eq_sum_units c, B_sum_right]
  apply Submodule.sum_mem
  intro p _
  rw [B_smul_right]
  exact Submodule.smul_mem _ _ (B_unit_mem_reach_succ hk d r u₀ hu p)

/-! ## Step 3: Finding `partner` and Isolating a Singleton `unit i₁ ∈ Reach 1 D₀` -/

private lemma mix_unit_eq (d : ℕ) (p : Fin k) (j : Fin k) :
    mix hk d (unit p) j =
      (if j = p then 1 else 0) + (if j = bshift hk p d then 1 else 0) +
      (if j = shift hk p d then 1 else 0) := by
  simp only [mix, unit]
  have h1 : shift hk j d = p ↔ j = bshift hk p d := by
    constructor
    · rintro rfl; exact (bshift_shift hk j d).symm
    · rintro rfl; exact shift_bshift hk p d
  have h2 : bshift hk j d = p ↔ j = shift hk p d := by
    constructor
    · rintro rfl; exact (shift_bshift hk j d).symm
    · rintro rfl; exact bshift_shift hk p d
  change (if j = p then (1 : ZMod 2) else 0) +
    (if shift hk j d = p then 1 else 0) + (if bshift hk j d = p then 1 else 0) = _
  simp [h1, h2]

private lemma polar_unit_right (hk11 : 11 ≤ k) (U : W k) (r : Fin k) (t : Fin k) :
    polar hk U (unit r) t =
      U (bshift hk r 1) * unit (bshift hk r 2) t +
      U (shift hk r 1) * unit (bshift hk r 1) t := by
  simp only [polar, unit]
  have h1 : shift hk t 2 = r ↔ t = bshift hk r 2 := by
    constructor
    · rintro rfl; exact (bshift_shift hk t 2).symm
    · rintro rfl; exact shift_bshift hk r 2
  have h2 : shift hk t 1 = r ↔ t = bshift hk r 1 := by
    constructor
    · rintro rfl; exact (bshift_shift hk t 1).symm
    · rintro rfl; exact shift_bshift hk r 1
  change U (shift hk t 1) * (if shift hk t 2 = r then (1 : ZMod 2) else 0) +
    U (shift hk t 2) * (if shift hk t 1 = r then 1 else 0) = _
  simp only [h1, h2]
  have hne : bshift hk r 2 ≠ bshift hk r 1 := by
    intro heq
    rw [bshift_eq_shift_sub hk r (by omega), bshift_eq_shift_sub hk r (by omega)] at heq
    have := shift_inj hk r (by omega) (by omega) heq
    omega
  by_cases ht2 : t = bshift hk r 2
  · subst ht2
    have h1eq : shift hk (bshift hk r 2) 1 = bshift hk r 1 := by
      rw [bshift_eq_shift_sub hk r (by omega), bshift_eq_shift_sub hk r (by omega), shift_add]
      congr 1; omega
    simp [hne, h1eq]
  · by_cases ht1 : t = bshift hk r 1
    · subst ht1
      have h2eq : shift hk (bshift hk r 1) 2 = shift hk r 1 := by
        rw [bshift_eq_shift_sub hk r (by omega), shift_add]
        rw [shift_eq_iff]
        have : k - 1 + 2 = k + 1 := by omega
        rw [this, Nat.add_mod_left]
      simp [ht2, h2eq]
    · simp [ht2, ht1]

private lemma exists_partner {d : ℕ} (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0) (hd : d = 1 ∨ d = 2)
    (start : ℕ) {v : W k} (hv : v ≠ 0) :
    ∃ partner : Fin k,
      let D₀ := B hk d (rot hk start v) (rot hk start (unit partner))
      D₀ ≠ 0 ∧
      ∃ a : Fin k, ∀ j : Fin k, D₀ j ≠ 0 → ∃ t < 2 * d + 2, j = shift hk a t := by
  have hrv : rot hk start v ≠ 0 := by
    intro h; exact hv ((rot_eq_zero_iff hk start v).mp h)
  have hu_ne : mix hk d (rot hk start v) ≠ 0 := by
    intro h
    have h0 : mix hk d (rot hk start v) = mix hk d 0 := by rw [h, mix_zero]
    exact hrv (mix_injective hk hk3 h0)
  have hne_exists : ∃ p : Fin k, B hk d (rot hk start v) (unit p) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hzero_all : ∀ V : W k, polar hk (mix hk d (rot hk start v)) V = 0 := by
      intro V
      obtain ⟨c, hc⟩ := mix_surjective hk hk3 V
      rw [← hc]
      change B hk d (rot hk start v) c = 0
      rw [vec_eq_sum_units c, B_sum_right]
      apply Finset.sum_eq_zero
      intro p _
      rw [B_smul_right, hall p, smul_zero]
    have ⟨j₀, hj₀⟩ : ∃ j₀ : Fin k, mix hk d (rot hk start v) j₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hu_ne (funext h)
    have h1 := congrFun (hzero_all (unit (shift hk j₀ 1))) (bshift hk j₀ 1)
    rw [polar_unit_right hk hk11] at h1
    have hs1 : bshift hk (shift hk j₀ 1) 1 = j₀ := bshift_shift hk j₀ 1
    have hs2 : bshift hk (shift hk j₀ 1) 2 = bshift hk j₀ 1 := by
      rw [bshift_eq_shift_sub hk _ (by omega), bshift_eq_shift_sub hk _ (by omega), shift_add,
        shift_eq_iff]
      have : 1 + (k - 2) = k - 1 := by omega
      rw [this]
    have hne : bshift hk j₀ 1 ≠ j₀ := by
      intro heq
      rw [bshift_eq_shift_sub hk j₀ (by omega)] at heq
      have := shift_inj hk j₀ (by omega) (by omega) (heq.trans (shift_zero hk j₀).symm)
      omega
    rw [hs1, hs2] at h1
    simp only [unit, ↓reduceIte, mul_one, hne, mul_zero, add_zero, Pi.zero_apply] at h1
    exact hj₀ h1
  obtain ⟨p, hp⟩ := hne_exists
  refine ⟨bshift hk p start, ?_, ?_⟩
  · rw [rot_unit, shift_bshift]; exact hp
  · rw [rot_unit, shift_bshift]
    refine ⟨bshift hk p (d + 2), fun j hj => ?_⟩
    have hd_lt : d < k := by omega
    simp only [B, polar] at hj
    have hmem_mix : ∀ x : Fin k, mix hk d (unit p) x ≠ 0 →
        ∃ m < 2 * d + 1, x = shift hk (bshift hk p d) m := by
      intro x hx
      rw [mix_unit_eq hk d p x] at hx
      by_cases hxp : x = p
      · refine ⟨d, by omega, ?_⟩
        rw [shift_bshift, hxp]
      · by_cases hxb : x = bshift hk p d
        · refine ⟨0, by omega, ?_⟩
          rw [shift_zero, hxb]
        · by_cases hxs : x = shift hk p d
          · refine ⟨2 * d, by omega, ?_⟩
            rw [hxs, bshift_eq_shift_sub hk p (by omega), shift_add, shift_eq_iff]
            have : k - d + 2 * d = k + d := by omega
            rw [this, Nat.add_mod_left]
          · simp [hxp, hxb, hxs] at hx
    have hcases : mix hk d (unit p) (shift hk j 2) ≠ 0 ∨
        mix hk d (unit p) (shift hk j 1) ≠ 0 := by
      by_contra h
      push Not at h
      simp only [shift] at h
      rw [h.1, h.2] at hj
      simp at hj
    rcases hcases with h2 | h1
    · obtain ⟨m, hm, hxm⟩ := hmem_mix _ h2
      refine ⟨m, by omega, ?_⟩
      have hsh : shift hk j 2 = shift hk (shift hk (bshift hk p (d + 2)) m) 2 := by
        rw [hxm, bshift_eq_shift_sub hk p (by omega), bshift_eq_shift_sub hk p (by omega),
          shift_add, shift_add, shift_add, shift_eq_iff]
        have : k - (d + 2) + (m + 2) = k - d + m := by omega
        rw [← Nat.add_assoc, Nat.add_assoc (k - (d + 2)), this]
      have := congrArg (fun z => bshift hk z 2) hsh
      simpa [bshift_shift] using this
    · obtain ⟨m, hm, hxm⟩ := hmem_mix _ h1
      refine ⟨m + 1, by omega, ?_⟩
      have hsh : shift hk j 1 = shift hk (shift hk (bshift hk p (d + 2)) (m + 1)) 1 := by
        rw [hxm, bshift_eq_shift_sub hk p (by omega), bshift_eq_shift_sub hk p (by omega),
          shift_add, shift_add, shift_add, shift_eq_iff]
        have : k - (d + 2) + (m + 1 + 1) = k - d + m := by omega
        rw [← Nat.add_assoc, Nat.add_assoc (k - (d + 2)), this]
      have := congrArg (fun z => bshift hk z 1) hsh
      simpa [bshift_shift] using this

private lemma exists_singleton_reach1 {d : ℕ} (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0) (hd : d = 1 ∨ d = 2)
    {D₀ : W k} (hD₀ : D₀ ≠ 0)
    (hsupp : ∃ a : Fin k, ∀ j : Fin k, D₀ j ≠ 0 → ∃ t < 2 * d + 2, j = shift hk a t) :
    ∃ i₁ : Fin k, unit i₁ ∈ Reach hk d 1 D₀ := by
  obtain ⟨a, ha⟩ := hsupp
  let U := mix hk d D₀
  have hU_ne : U ≠ 0 := by
    intro h
    have : mix hk d D₀ = mix hk d 0 := by rw [show mix hk d D₀ = U from rfl, h, mix_zero]
    exact hD₀ (mix_injective hk hk3 this)
  have hU_supp : ∀ j : Fin k, U j ≠ 0 → ∃ m < 4 * d + 2, j = shift hk (bshift hk a d) m := by
    intro j hj
    simp only [U, mix] at hj
    have hcases : D₀ j ≠ 0 ∨ D₀ (shift hk j d) ≠ 0 ∨ D₀ (bshift hk j d) ≠ 0 := by
      by_contra h
      push Not at h
      simp only [shift, bshift] at h
      rw [h.1, h.2.1, h.2.2] at hj
      simp at hj
    rcases hcases with h0 | h1 | h2
    · obtain ⟨t, ht, hjt⟩ := ha j h0
      refine ⟨t + d, by omega, ?_⟩
      rw [hjt, bshift_eq_shift_sub hk a (by omega), shift_add, shift_eq_iff]
      have : k - d + (t + d) = k + t := by omega
      rw [this, Nat.add_mod_left]
    · obtain ⟨t, ht, hjt⟩ := ha _ h1
      refine ⟨t, by omega, ?_⟩
      have hsh : shift hk j d = shift hk (shift hk (bshift hk a d) t) d := by
        rw [hjt, bshift_eq_shift_sub hk a (by omega), shift_add, shift_add, shift_eq_iff]
        have : k - d + (t + d) = k + t := by omega
        rw [this, Nat.add_mod_left]
      have := congrArg (fun z => bshift hk z d) hsh
      simpa [bshift_shift] using this
    · obtain ⟨t, ht, hjt⟩ := ha _ h2
      refine ⟨t + 2 * d, by omega, ?_⟩
      have hsh : bshift hk j d = bshift hk (shift hk (bshift hk a d) (t + 2 * d)) d := by
        rw [hjt, bshift_eq_shift_sub hk a (by omega), bshift_eq_shift_sub hk _ (by omega),
          shift_add, shift_add, shift_eq_iff]
        have : k - d + (t + 2 * d) + (k - d) = 2 * k + t := by omega
        rw [← Nat.add_assoc, this]
        simp [Nat.add_mod]
      have := congrArg (fun z => shift hk z d) hsh
      simpa [shift_bshift] using this
  -- U is NOT 2-periodic: ∃ r, U (bshift r 1) ≠ U (shift r 1)
  have hnot2per : ∃ r : Fin k, U (bshift hk r 1) ≠ U (shift hk r 1) := by
    by_contra hall
    push Not at hall
    have hstep2 : ∀ i : Fin k, U (shift hk i 2) = U i := by
      intro i
      have h1 := hall (shift hk i 1)
      rw [bshift_shift, shift_add] at h1
      exact h1.symm
    have hstep2m : ∀ m : ℕ, ∀ i : Fin k, U (shift hk i (2 * m)) = U i := by
      intro m
      induction m with
      | zero => intro i; simp [shift_zero]
      | succ m ih =>
        intro i
        have : 2 * (m + 1) = 2 * m + 2 := by omega
        rw [this, ← shift_add, hstep2, ih]
    let z0 := shift hk (bshift hk a d) (4 * d + 2)
    have hz0 : U z0 = 0 := by
      by_contra hne
      obtain ⟨m, hm, hzm⟩ := hU_supp z0 hne
      have := shift_inj hk (bshift hk a d) (by omega) (by omega) hzm
      omega
    have hU0 : ∀ j : Fin k, U j = 0 := by
      intro j
      obtain ⟨t, ht, rfl⟩ : ∃ t < k, j = shift hk z0 t := by
        refine ⟨(j.val + k - z0.val) % k, Nat.mod_lt _ hk, ?_⟩
        apply Fin.ext
        simp only [shift, ix]
        have hzlt : z0.val < k := z0.isLt
        have h1 : (z0.val + (j.val + k - z0.val) % k) % k =
            (z0.val + (j.val + k - z0.val)) % k := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        rw [h1]
        have h2 : z0.val + (j.val + k - z0.val) = j.val + k := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
      by_cases hteven : t % 2 = 0
      · have : t = 2 * (t / 2) := by omega
        rw [this, hstep2m, hz0]
      · by_cases hkeven : k % 2 = 0
        · -- k is even and ≥ 11, so k ≥ 12, hence 4*d + 3 < k, so U (shift z0 1) = 0 too!
          have hk12 : 12 ≤ k := by omega
          have hz1 : U (shift hk z0 1) = 0 := by
            by_contra hne
            obtain ⟨m, hm, hzm⟩ := hU_supp (shift hk z0 1) hne
            simp only [z0, shift_add] at hzm
            have := shift_inj hk (bshift hk a d) (by omega) (by omega) hzm
            omega
          have : t = 1 + 2 * (t / 2) := by omega
          rw [this, ← shift_add, hstep2m, hz1]
        · -- k is odd, so t + k is even!
          have hev : (t + k) % 2 = 0 := by omega
          have h1 : shift hk z0 t = shift hk z0 (t + k) := by
            rw [shift_eq_iff, Nat.add_mod_right]
          rw [h1]
          have : t + k = 2 * ((t + k) / 2) := by omega
          rw [this, hstep2m, hz0]
    exact hU_ne (funext hU0)
  obtain ⟨r, hr⟩ := hnot2per
  have hmem : polar hk U (unit r) ∈ Reach hk d 1 D₀ :=
    polar_mem_reach_succ hk hk3 0 D₀ (self_mem_reach0 hk d D₀) (unit r)
  have hpol : polar hk U (unit r) =
      U (bshift hk r 1) • unit (bshift hk r 2) + U (shift hk r 1) • unit (bshift hk r 1) := by
    funext t
    rw [polar_unit_right hk hk11 U r t]
    rfl
  rw [hpol] at hmem
  by_cases h1 : U (bshift hk r 1) = 0
  · have h2 : U (shift hk r 1) = 1 := z2_eq_one_of_ne_zero (fun h2 => hr (h1.trans h2.symm))
    rw [h1, h2, zero_smul, one_smul, zero_add] at hmem
    exact ⟨bshift hk r 1, hmem⟩
  · have h1' : U (bshift hk r 1) = 1 := z2_eq_one_of_ne_zero h1
    have h2 : U (shift hk r 1) = 0 := by
      by_contra h2ne
      exact hr (h1'.trans (z2_eq_one_of_ne_zero h2ne).symm)
    rw [h1', h2, zero_smul, one_smul, add_zero] at hmem
    exact ⟨bshift hk r 2, hmem⟩

/-! ## Step 4: Spanning `Fin k` in `s` Steps from `unit i₁` (`d = 1` and `d = 2`) -/

private lemma polar_mix_unit_eval {d : ℕ} (hk11 : 11 ≤ k)
    (i : Fin k) (r : Fin k) :
    polar hk (mix hk d (unit i)) (unit r) =
      mix hk d (unit i) (bshift hk r 1) • unit (bshift hk r 2) +
      mix hk d (unit i) (shift hk r 1) • unit (bshift hk r 1) := by
  funext t
  rw [polar_unit_right hk hk11]
  rfl

-- Helper: evaluate `mix hk d (unit i) (shift hk i t)` cleanly for small offsets!
private lemma mix_unit_shift {d : ℕ} (hk11 : 11 ≤ k) (hd : d = 1 ∨ d = 2) (i : Fin k)
    (t : ℕ) (ht : t < k) :
    mix hk d (unit i) (shift hk i t) =
      (if t = 0 then 1 else 0) + (if t = k - d then 1 else 0) + (if t = d then 1 else 0) := by
  rw [mix_unit_eq hk d i]
  have h0 : shift hk i t = i ↔ t = 0 := by
    conv_lhs => rhs; rw [← shift_zero hk i]
    rw [shift_eq_iff, Nat.mod_eq_of_lt ht, Nat.zero_mod]
  have h1 : shift hk i t = bshift hk i d ↔ t = k - d := by
    rw [bshift_eq_shift_sub hk i (by omega), shift_eq_iff, Nat.mod_eq_of_lt ht,
      Nat.mod_eq_of_lt (by omega)]
  have h2 : shift hk i t = shift hk i d ↔ t = d := by
    rw [shift_eq_iff, Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt (by omega)]
  simp [h0, h1, h2]

-- For d = 1: from `unit i ∈ Reach r`, get `unit (bshift i t) ∈ Reach (r + 1)` for `t ∈ {0, 1, 2, 3}`!
private lemma d1_step (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0) (r : ℕ) (u₀ : W k) (i : Fin k)
    (hi : unit i ∈ Reach hk 1 r u₀) (t : ℕ) (ht : t ≤ 3) :
    unit (bshift hk i t) ∈ Reach hk 1 (r + 1) u₀ := by
  have hpol : ∀ c : ℕ, c < k →
      mix hk 1 (unit i) (shift hk i ((c + k - 1) % k)) • unit (shift hk i ((c + k - 2) % k)) +
      mix hk 1 (unit i) (shift hk i ((c + 1) % k)) • unit (shift hk i ((c + k - 1) % k)) ∈
        Reach hk 1 (r + 1) u₀ := by
    intro c hc
    have hmem := polar_mem_reach_succ hk hk3 r u₀ hi (unit (shift hk i c))
    rw [polar_mix_unit_eval hk hk11] at hmem
    have hb1 : bshift hk (shift hk i c) 1 = shift hk i ((c + k - 1) % k) := by
      rw [bshift_eq_shift_sub hk _ (by omega), shift_add, shift_eq_iff, Nat.mod_mod]
      congr 1; omega
    have hb2 : bshift hk (shift hk i c) 2 = shift hk i ((c + k - 2) % k) := by
      rw [bshift_eq_shift_sub hk _ (by omega), shift_add, shift_eq_iff, Nat.mod_mod]
      congr 1; omega
    have hs1 : shift hk (shift hk i c) 1 = shift hk i ((c + 1) % k) := by
      rw [shift_add, shift_mod]
    rw [hb1, hb2, hs1] at hmem
    exact hmem
  interval_cases t
  · -- t = 0: c = 2 -> bshift(2,1)=1 (in mix), shift(2,1)=3 (not in mix), bshift(2,2)=0
    have h := hpol 2 (by omega)
    have h1 : (2 + k - 1) % k = 1 := by
      have : 2 + k - 1 = k + 1 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (2 + k - 2) % k = 0 := by
      have : 2 + k - 2 = k := by omega
      rw [this, Nat.mod_self]
    have h3 : (2 + 1) % k = 3 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3, mix_unit_shift hk hk11 (Or.inl rfl) i 1 (by omega),
      mix_unit_shift hk hk11 (Or.inl rfl) i 3 (by omega)] at h
    have hc1 : (if (1 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 1 = k - 1 then 1 else 0) +
        (if 1 = 1 then 1 else 0) = 1 := by simp [show (1 : ℕ) ≠ k - 1 by omega]
    have hc3 : (if (3 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 3 = k - 1 then 1 else 0) +
        (if 3 = 1 then 1 else 0) = 0 := by simp [show (3 : ℕ) ≠ k - 1 by omega]
    rw [hc1, hc3] at h
    have hb0 : bshift hk i 0 = i := by
      apply Fin.ext; simp [bshift, ix, Nat.mod_eq_of_lt i.isLt]
    rw [hb0]; simpa [shift_zero] using h
  · -- t = 1: c = 1 -> bshift(1,1)=0 (in mix), shift(1,1)=2 (not in mix), bshift(1,2)=k-1
    have h := hpol 1 (by omega)
    have h1 : (1 + k - 1) % k = 0 := by
      have : 1 + k - 1 = k := by omega
      rw [this, Nat.mod_self]
    have h2 : (1 + k - 2) % k = k - 1 := by
      have : 1 + k - 2 = k - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have h3 : (1 + 1) % k = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3, mix_unit_shift hk hk11 (Or.inl rfl) i 0 (by omega),
      mix_unit_shift hk hk11 (Or.inl rfl) i 2 (by omega)] at h
    have hc0 : (if (0 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 0 = k - 1 then 1 else 0) +
        (if 0 = 1 then 1 else 0) = 1 := by simp [show (0 : ℕ) ≠ k - 1 by omega]
    have hc2 : (if (2 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 2 = k - 1 then 1 else 0) +
        (if 2 = 1 then 1 else 0) = 0 := by simp [show (2 : ℕ) ≠ k - 1 by omega]
    rw [hc0, hc2] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; simpa using h
  · -- t = 2: c = k - 1 -> bshift(k-1,1)=k-2 (not in mix), shift(k-1,1)=0 (in mix), bshift(k-1,1)=k-2
    have h := hpol (k - 1) (by omega)
    have h1 : (k - 1 + k - 1) % k = k - 2 := by
      have : k - 1 + k - 1 = k + (k - 2) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (k - 1 + 1) % k = 0 := by
      have : k - 1 + 1 = k := by omega
      rw [this, Nat.mod_self]
    rw [h1, h3, mix_unit_shift hk hk11 (Or.inl rfl) i (k - 2) (by omega),
      mix_unit_shift hk hk11 (Or.inl rfl) i 0 (by omega)] at h
    have hc_km2 : (if k - 2 = 0 then (1 : ZMod 2) else 0) + (if k - 2 = k - 1 then 1 else 0) +
        (if k - 2 = 1 then 1 else 0) = 0 := by
      simp [show k - 2 ≠ 0 by omega, show k - 2 ≠ k - 1 by omega, show k - 2 ≠ 1 by omega]
    have hc0 : (if (0 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 0 = k - 1 then 1 else 0) +
        (if 0 = 1 then 1 else 0) = 1 := by simp [show (0 : ℕ) ≠ k - 1 by omega]
    rw [hc_km2, hc0] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; simpa using h
  · -- t = 3: c = k - 2 -> bshift(k-2,1)=k-3 (not in mix), shift(k-2,1)=k-1 (in mix), bshift(k-2,1)=k-3
    have h := hpol (k - 2) (by omega)
    have h1 : (k - 2 + k - 1) % k = k - 3 := by
      have : k - 2 + k - 1 = k + (k - 3) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (k - 2 + 1) % k = k - 1 := by
      have : k - 2 + 1 = k - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h3, mix_unit_shift hk hk11 (Or.inl rfl) i (k - 3) (by omega),
      mix_unit_shift hk hk11 (Or.inl rfl) i (k - 1) (by omega)] at h
    have hc_km3 : (if k - 3 = 0 then (1 : ZMod 2) else 0) + (if k - 3 = k - 1 then 1 else 0) +
        (if k - 3 = 1 then 1 else 0) = 0 := by
      simp [show k - 3 ≠ 0 by omega, show k - 3 ≠ k - 1 by omega, show k - 3 ≠ 1 by omega]
    have hc_km1 : (if k - 1 = 0 then (1 : ZMod 2) else 0) + (if k - 1 = k - 1 then 1 else 0) +
        (if k - 1 = 1 then 1 else 0) = 1 := by
      simp [show k - 1 ≠ 0 by omega, show k - 1 ≠ 1 by omega]
    rw [hc_km3, hc_km1] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; simpa using h

-- For d = 2: single-step helper producing all 4 vectors from `unit i ∈ Reach r`
private lemma d2_from_unit (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0) (r : ℕ) (u₀ : W k) (i : Fin k)
    (hi : unit i ∈ Reach hk 2 r u₀) :
    unit (bshift hk i 4) ∈ Reach hk 2 (r + 1) u₀ ∧
    unit (shift hk i 1) ∈ Reach hk 2 (r + 1) u₀ ∧
    (unit (bshift hk i 3) + unit (bshift hk i 2)) ∈ Reach hk 2 (r + 1) u₀ ∧
    (unit (bshift hk i 1) + unit i) ∈ Reach hk 2 (r + 1) u₀ := by
  have hpol : ∀ c : ℕ, c < k →
      mix hk 2 (unit i) (shift hk i ((c + k - 1) % k)) • unit (shift hk i ((c + k - 2) % k)) +
      mix hk 2 (unit i) (shift hk i ((c + 1) % k)) • unit (shift hk i ((c + k - 1) % k)) ∈
        Reach hk 2 (r + 1) u₀ := by
    intro c hc
    have hmem := polar_mem_reach_succ hk hk3 r u₀ hi (unit (shift hk i c))
    rw [polar_mix_unit_eval hk hk11] at hmem
    have hb1 : bshift hk (shift hk i c) 1 = shift hk i ((c + k - 1) % k) := by
      rw [bshift_eq_shift_sub hk _ (by omega), shift_add, shift_eq_iff, Nat.mod_mod]
      congr 1; omega
    have hb2 : bshift hk (shift hk i c) 2 = shift hk i ((c + k - 2) % k) := by
      rw [bshift_eq_shift_sub hk _ (by omega), shift_add, shift_eq_iff, Nat.mod_mod]
      congr 1; omega
    have hs1 : shift hk (shift hk i c) 1 = shift hk i ((c + 1) % k) := by
      rw [shift_add, shift_mod]
    rw [hb1, hb2, hs1] at hmem
    exact hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- unit (bshift i 4): c = k - 3
    have h := hpol (k - 3) (by omega)
    have h1 : (k - 3 + k - 1) % k = k - 4 := by
      have : k - 3 + k - 1 = k + (k - 4) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (k - 3 + 1) % k = k - 2 := by
      have : k - 3 + 1 = k - 2 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h3, mix_unit_shift hk hk11 (Or.inr rfl) i (k - 4) (by omega),
      mix_unit_shift hk hk11 (Or.inr rfl) i (k - 2) (by omega)] at h
    have hc1 : (if k - 4 = 0 then (1 : ZMod 2) else 0) + (if k - 4 = k - 2 then 1 else 0) +
        (if k - 4 = 2 then 1 else 0) = 0 := by
      simp [show k - 4 ≠ 0 by omega, show k - 4 ≠ k - 2 by omega, show k - 4 ≠ 2 by omega]
    have hc2 : (if k - 2 = 0 then (1 : ZMod 2) else 0) + (if k - 2 = k - 2 then 1 else 0) +
        (if k - 2 = 2 then 1 else 0) = 1 := by
      simp [show k - 2 ≠ 0 by omega, show k - 2 ≠ 2 by omega]
    rw [hc1, hc2] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; simpa using h
  · -- unit (shift i 1): c = 3
    have h := hpol 3 (by omega)
    have h1 : (3 + k - 1) % k = 2 := by
      have : 3 + k - 1 = k + 2 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (3 + k - 2) % k = 1 := by
      have : 3 + k - 2 = k + 1 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (3 + 1) % k = 4 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3, mix_unit_shift hk hk11 (Or.inr rfl) i 2 (by omega),
      mix_unit_shift hk hk11 (Or.inr rfl) i 4 (by omega)] at h
    have hc1 : (if (2 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 2 = k - 2 then 1 else 0) +
        (if 2 = 2 then 1 else 0) = 1 := by simp [show (2 : ℕ) ≠ k - 2 by omega]
    have hc2 : (if (4 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 4 = k - 2 then 1 else 0) +
        (if 4 = 2 then 1 else 0) = 0 := by simp [show (4 : ℕ) ≠ k - 2 by omega]
    rw [hc1, hc2] at h
    simpa using h
  · -- unit (bshift i 3) + unit (bshift i 2): c = k - 1
    have h := hpol (k - 1) (by omega)
    have h1 : (k - 1 + k - 1) % k = k - 2 := by
      have : k - 1 + k - 1 = k + (k - 2) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (k - 1 + k - 2) % k = k - 3 := by
      have : k - 1 + k - 2 = k + (k - 3) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (k - 1 + 1) % k = 0 := by
      have : k - 1 + 1 = k := by omega
      rw [this, Nat.mod_self]
    rw [h1, h2, h3, mix_unit_shift hk hk11 (Or.inr rfl) i (k - 2) (by omega),
      mix_unit_shift hk hk11 (Or.inr rfl) i 0 (by omega)] at h
    have hc1 : (if k - 2 = 0 then (1 : ZMod 2) else 0) + (if k - 2 = k - 2 then 1 else 0) +
        (if k - 2 = 2 then 1 else 0) = 1 := by
      simp [show k - 2 ≠ 0 by omega, show k - 2 ≠ 2 by omega]
    have hc2 : (if (0 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 0 = k - 2 then 1 else 0) +
        (if 0 = 2 then 1 else 0) = 1 := by simp [show (0 : ℕ) ≠ k - 2 by omega]
    rw [hc1, hc2] at h
    rw [bshift_eq_shift_sub hk i (by omega), bshift_eq_shift_sub hk i (by omega)]; simpa using h
  · -- unit (bshift i 1) + unit i: c = 1
    have h := hpol 1 (by omega)
    have h1 : (1 + k - 1) % k = 0 := by
      have : 1 + k - 1 = k := by omega
      rw [this, Nat.mod_self]
    have h2 : (1 + k - 2) % k = k - 1 := by
      have : 1 + k - 2 = k - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    have h3 : (1 + 1) % k = 2 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3, mix_unit_shift hk hk11 (Or.inr rfl) i 0 (by omega),
      mix_unit_shift hk hk11 (Or.inr rfl) i 2 (by omega)] at h
    have hc1 : (if (0 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 0 = k - 2 then 1 else 0) +
        (if 0 = 2 then 1 else 0) = 1 := by simp [show (0 : ℕ) ≠ k - 2 by omega]
    have hc2 : (if (2 : ℕ) = 0 then (1 : ZMod 2) else 0) + (if 2 = k - 2 then 1 else 0) +
        (if 2 = 2 then 1 else 0) = 1 := by simp [show (2 : ℕ) ≠ k - 2 by omega]
    rw [hc1, hc2] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; simpa [shift_zero] using h

-- For d = 2: from `unit i + unit (shift i 1) ∈ Reach r`, get 4 singletons!
private lemma d2_from_pair (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0) (r : ℕ) (u₀ : W k) (i : Fin k)
    (hp : unit i + unit (shift hk i 1) ∈ Reach hk 2 r u₀) :
    unit (bshift hk i 4) ∈ Reach hk 2 (r + 1) u₀ ∧
    unit (bshift hk i 3) ∈ Reach hk 2 (r + 1) u₀ ∧
    unit (shift hk i 1) ∈ Reach hk 2 (r + 1) u₀ ∧
    unit (shift hk i 2) ∈ Reach hk 2 (r + 1) u₀ := by
  have hmix : ∀ t < k,
      mix hk 2 (unit i + unit (shift hk i 1)) (shift hk i t) =
      if t = k - 2 ∨ t = k - 1 ∨ t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 then 1 else 0 := by
    intro t ht
    rw [mix_add, Pi.add_apply, mix_unit_shift hk hk11 (Or.inr rfl) i t ht]
    have hshift1 : shift hk i t = shift hk (shift hk i 1) ((t + k - 1) % k) := by
      rw [shift_add, shift_eq_iff]
      have : 1 + (t + k - 1) % k ≡ 1 + (t + k - 1) [MOD k] :=
        Nat.ModEq.add_left 1 (Nat.mod_modEq _ _)
      have h2 : (1 + (t + k - 1)) % k = t % k := by
        have : 1 + (t + k - 1) = t + k := by omega
        rw [this, Nat.add_mod_right]
      exact (Nat.ModEq.trans this h2).symm
    rw [hshift1, mix_unit_shift hk hk11 (Or.inr rfl) (shift hk i 1) ((t + k - 1) % k) (Nat.mod_lt _ hk)]
    by_cases ht0 : t = 0
    · subst ht0
      have : (0 + k - 1) % k = k - 1 := by simp only [zero_add]; exact Nat.mod_eq_of_lt (by omega)
      rw [this]; simp [show (0 : ℕ) ≠ k - 2 by omega, show k - 1 ≠ 0 by omega,
        show k - 1 ≠ k - 2 by omega, show k - 1 ≠ 2 by omega]
    · have hsub : (t + k - 1) % k = t - 1 := by
        have : t + k - 1 = k + (t - 1) := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      rw [hsub]
      by_cases h1 : t = 1
      · subst h1; simp [show (1 : ℕ) ≠ k - 2 by omega, show (0 : ℕ) ≠ k - 2 by omega]
      · by_cases h2 : t = 2
        · subst h2; simp [show (2 : ℕ) ≠ k - 2 by omega, show (1 : ℕ) ≠ k - 2 by omega]
        · by_cases h3 : t = 3
          · subst h3; simp [show (3 : ℕ) ≠ k - 2 by omega, show (2 : ℕ) ≠ k - 2 by omega]
          · by_cases hm2 : t = k - 2
            · subst hm2
              simp [show k - 2 ≠ 0 by omega, show k - 2 ≠ 2 by omega, show k - 2 - 1 ≠ 0 by omega,
                show k - 2 - 1 ≠ k - 2 by omega, show k - 2 - 1 ≠ 2 by omega]
            · by_cases hm1 : t = k - 1
              · subst hm1
                have : k - 1 - 1 = k - 2 := by omega
                rw [this]
                simp [show k - 1 ≠ 0 by omega, show k - 1 ≠ k - 2 by omega, show k - 1 ≠ 2 by omega,
                  show k - 2 ≠ 0 by omega, show k - 2 ≠ 2 by omega]
              · simp [ht0, h1, h2, h3, hm2, hm1,
                  show t - 1 ≠ 0 by omega, show t - 1 ≠ k - 2 by omega, show t - 1 ≠ 2 by omega]
  have hpol : ∀ c : ℕ, c < k →
      mix hk 2 (unit i + unit (shift hk i 1)) (shift hk i ((c + k - 1) % k)) •
        unit (shift hk i ((c + k - 2) % k)) +
      mix hk 2 (unit i + unit (shift hk i 1)) (shift hk i ((c + 1) % k)) •
        unit (shift hk i ((c + k - 1) % k)) ∈
        Reach hk 2 (r + 1) u₀ := by
    intro c hc
    have hmem := polar_mem_reach_succ hk hk3 r u₀ hp (unit (shift hk i c))
    have hpe : polar hk (mix hk 2 (unit i + unit (shift hk i 1))) (unit (shift hk i c)) =
        mix hk 2 (unit i + unit (shift hk i 1)) (bshift hk (shift hk i c) 1) •
          unit (bshift hk (shift hk i c) 2) +
        mix hk 2 (unit i + unit (shift hk i 1)) (shift hk (shift hk i c) 1) •
          unit (bshift hk (shift hk i c) 1) := by
      funext t; rw [polar_unit_right hk hk11]; rfl
    rw [hpe] at hmem
    have hb1 : bshift hk (shift hk i c) 1 = shift hk i ((c + k - 1) % k) := by
      rw [bshift_eq_shift_sub hk _ (by omega), shift_add, shift_eq_iff, Nat.mod_mod]
      congr 1; omega
    have hb2 : bshift hk (shift hk i c) 2 = shift hk i ((c + k - 2) % k) := by
      rw [bshift_eq_shift_sub hk _ (by omega), shift_add, shift_eq_iff, Nat.mod_mod]
      congr 1; omega
    have hs1 : shift hk (shift hk i c) 1 = shift hk i ((c + 1) % k) := by
      rw [shift_add, shift_mod]
    rw [hb1, hb2, hs1] at hmem
    exact hmem
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bshift i 4: c = k - 3 -> c-1 = k-4 (0), c+1 = k-2 (1), out = k-4
    have h := hpol (k - 3) (by omega)
    have h1 : (k - 3 + k - 1) % k = k - 4 := by
      have : k - 3 + k - 1 = k + (k - 4) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (k - 3 + 1) % k = k - 2 := by
      have : k - 3 + 1 = k - 2 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h3, hmix (k - 4) (by omega), hmix (k - 2) (by omega)] at h
    have hc0 : ¬ (k - 4 = k - 2 ∨ k - 4 = k - 1 ∨ k - 4 = 0 ∨ k - 4 = 1 ∨ k - 4 = 2 ∨ k - 4 = 3) := by omega
    simp only [hc0, ↓reduceIte, zero_smul, zero_add, true_or, one_smul] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; exact h
  · -- bshift i 3: c = k - 2 -> c-1 = k-3 (0), c+1 = k-1 (1), out = k-3
    have h := hpol (k - 2) (by omega)
    have h1 : (k - 2 + k - 1) % k = k - 3 := by
      have : k - 2 + k - 1 = k + (k - 3) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (k - 2 + 1) % k = k - 1 := by
      have : k - 2 + 1 = k - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    rw [h1, h3, hmix (k - 3) (by omega), hmix (k - 1) (by omega)] at h
    have hc0 : ¬ (k - 3 = k - 2 ∨ k - 3 = k - 1 ∨ k - 3 = 0 ∨ k - 3 = 1 ∨ k - 3 = 2 ∨ k - 3 = 3) := by omega
    simp only [hc0, ↓reduceIte, zero_smul, zero_add, true_or, or_true, one_smul] at h
    rw [bshift_eq_shift_sub hk i (by omega)]; exact h
  · -- shift i 1: c = 3 -> c-1 = 2 (1), c+1 = 4 (0), out = 1
    have h := hpol 3 (by omega)
    have h1 : (3 + k - 1) % k = 2 := by
      have : 3 + k - 1 = k + 2 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (3 + k - 2) % k = 1 := by
      have : 3 + k - 2 = k + 1 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (3 + 1) % k = 4 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3, hmix 2 (by omega), hmix 4 (by omega)] at h
    have hc0 : ¬ ((4 : ℕ) = k - 2 ∨ 4 = k - 1 ∨ 4 = 0 ∨ 4 = 1 ∨ 4 = 2 ∨ 4 = 3) := by omega
    simp only [hc0, ↓reduceIte, zero_smul, add_zero, true_or, or_true, one_smul] at h
    exact h
  · -- shift i 2: c = 4 -> c-1 = 3 (1), c+1 = 5 (0), out = 2
    have h := hpol 4 (by omega)
    have h1 : (4 + k - 1) % k = 3 := by
      have : 4 + k - 1 = k + 3 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h2 : (4 + k - 2) % k = 2 := by
      have : 4 + k - 2 = k + 2 := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    have h3 : (4 + 1) % k = 5 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3, hmix 3 (by omega), hmix 5 (by omega)] at h
    have hc0 : ¬ ((5 : ℕ) = k - 2 ∨ 5 = k - 1 ∨ 5 = 0 ∨ 5 = 1 ∨ 5 = 2 ∨ 5 = 3) := by omega
    simp only [hc0, ↓reduceIte, zero_smul, add_zero, or_true, one_smul] at h
    exact h

private lemma reach_all_units {d s : ℕ} (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0)
    (hd : d = 1 ∨ d = 2) (hs2 : 2 ≤ s) (hks : k ≤ (2 * d + 1) * s + 1)
    (u₀ : W k) {i₁ : Fin k} (hi₁ : unit i₁ ∈ Reach hk d 1 u₀) :
    ∀ j : Fin k, unit j ∈ Reach hk d (s + 1) u₀ := by
  rcases hd with rfl | rfl
  · -- d = 1: by induction on m, ∀ t ≤ 3*m, unit (bshift i₁ t) ∈ Reach 1 (m + 1) u₀
    have hind : ∀ m : ℕ, ∀ t ≤ 3 * m, unit (bshift hk i₁ t) ∈ Reach hk 1 (m + 1) u₀ := by
      intro m
      induction m with
      | zero =>
        intro t ht
        have ht0 : t = 0 := by omega
        subst ht0
        have : bshift hk i₁ 0 = i₁ := by
          rw [bshift_eq_shift_sub hk i₁ (by omega)]
          apply Fin.ext; simp [shift, ix, Nat.mod_eq_of_lt i₁.isLt]
        rw [this]; exact hi₁
      | succ m ih =>
        intro t ht
        by_cases hle : t ≤ 3 * m
        · have hprev := ih t hle
          have hstep := d1_step hk hk11 hk3 (m + 1) u₀ (bshift hk i₁ t) hprev 0 (by omega)
          have h0 : bshift hk (bshift hk i₁ t) 0 = bshift hk i₁ t := by
            rw [bshift_eq_shift_sub hk _ (by omega)]
            apply Fin.ext; simp [shift, ix, Nat.mod_eq_of_lt (bshift hk i₁ t).isLt]
          rw [h0] at hstep; exact hstep
        · have hprev := ih (3 * m) (le_refl _)
          have hstep := d1_step hk hk11 hk3 (m + 1) u₀ (bshift hk i₁ (3 * m)) hprev (t - 3 * m) (by omega)
          have hb : bshift hk (bshift hk i₁ (3 * m)) (t - 3 * m) = bshift hk i₁ t := by
            rw [bshift_eq_shift, bshift_eq_shift, bshift_eq_shift, shift_add, shift_eq_iff]
            have h1 : k - 3 * m % k + (k - (t - 3 * m) % k) + t ≡
                (k - 3 * m % k + 3 * m % k) + (k - (t - 3 * m) % k + (t - 3 * m) % k) [MOD k] := by
              have htm : t = 3 * m + (t - 3 * m) := by omega
              have hmod : t % k = (3 * m % k + (t - 3 * m) % k) % k := by
                conv_lhs => rw [htm, Nat.add_mod]
              have hsub1 : 3 * m % k < k := Nat.mod_lt _ hk
              have hsub2 : (t - 3 * m) % k < k := Nat.mod_lt _ hk
              change _ % k = _ % k
              rw [Nat.add_mod, hmod, ← Nat.add_mod]
              congr 1; omega
            have hsub1 : 3 * m % k < k := Nat.mod_lt _ hk
            have hsub2 : (t - 3 * m) % k < k := Nat.mod_lt _ hk
            have hsub3 : t % k < k := Nat.mod_lt _ hk
            have h2 : k - 3 * m % k + 3 * m % k + (k - (t - 3 * m) % k + (t - 3 * m) % k) = 2 * k := by omega
            have h3 : (k - 3 * m % k + (k - (t - 3 * m) % k) + t) % k = 0 := by
              change _ % k = _ % k at h1
              rw [h1, h2]; simp
            have h4 : (k - t % k + t) % k = 0 := sub_mod_add_mod_self hk t
            exact add_mod_cancel hk _ _ t (by rw [h3, h4])
          rw [hb] at hstep; exact hstep
    intro j
    obtain ⟨t, ht, rfl⟩ : ∃ t < k, j = bshift hk i₁ t := by
      refine ⟨(i₁.val + k - j.val) % k, Nat.mod_lt _ hk, ?_⟩
      apply Fin.ext
      simp only [bshift, ix]
      have hi1 : i₁.val < k := i₁.isLt
      have hj1 : j.val < k := j.isLt
      have hlt : (i₁.val + k - j.val) % k < k := Nat.mod_lt _ hk
      have hmod : ((i₁.val + k - j.val) % k) % k = (i₁.val + k - j.val) % k := Nat.mod_mod _ _
      rw [hmod]
      by_cases hle : j.val ≤ i₁.val
      · have h1 : (i₁.val + k - j.val) % k = i₁.val - j.val := by
          have : i₁.val + k - j.val = k + (i₁.val - j.val) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        have : i₁.val + k - (i₁.val - j.val) = k + j.val := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hj1]
      · have h1 : (i₁.val + k - j.val) % k = i₁.val + k - j.val := Nat.mod_eq_of_lt (by omega)
        rw [h1]
        have : i₁.val + k - (i₁.val + k - j.val) = j.val := by omega
        rw [this, Nat.mod_eq_of_lt hj1]
    exact hind s t (by omega)
  · -- d = 2: base m = 2 gives all 11 singletons `shift (bshift i₁ 8) t` for `t ≤ 10`,
    -- then each step expands by +5 (`bshift · 4` and `shift · 1`)!
    have hbase2 : ∀ t ≤ 10, unit (shift hk (bshift hk i₁ 8) t) ∈ Reach hk 2 3 u₀ := by
      have ⟨h_m4, h_p1, h_pairA, h_pairB⟩ := d2_from_unit hk hk11 hk3 1 u₀ i₁ hi₁
      have h_pairA' : unit (bshift hk i₁ 3) + unit (shift hk (bshift hk i₁ 3) 1) ∈ Reach hk 2 2 u₀ := by
        have hs : shift hk (bshift hk i₁ 3) 1 = bshift hk i₁ 2 := by
          rw [bshift_eq_shift_sub hk i₁ (by omega), bshift_eq_shift_sub hk i₁ (by omega), shift_add]
          congr 1; omega
        rw [hs]; exact h_pairA
      have h_pairB' : unit (bshift hk i₁ 1) + unit (shift hk (bshift hk i₁ 1) 1) ∈ Reach hk 2 2 u₀ := by
        have hs : shift hk (bshift hk i₁ 1) 1 = i₁ := shift_bshift hk i₁ 1
        rw [hs]; exact h_pairB
      have ⟨hm8, hm3, _, _⟩ := d2_from_unit hk hk11 hk3 2 u₀ (bshift hk i₁ 4) h_m4
      have ⟨_, hp2, _, _⟩ := d2_from_unit hk hk11 hk3 2 u₀ (shift hk i₁ 1) h_p1
      have ⟨hm7, hm6, hm2, hm1⟩ := d2_from_pair hk hk11 hk3 2 u₀ (bshift hk i₁ 3) h_pairA'
      have ⟨hm5, hm4, h0, hp1⟩ := d2_from_pair hk hk11 hk3 2 u₀ (bshift hk i₁ 1) h_pairB'
      intro t ht
      have hrew : ∀ (a b c : ℕ), a < k → b < k → c < k →
          shift hk (bshift hk i₁ a) b = shift hk i₁ ((k - a + b) % k) := by
        intro a b _ ha _ _
        rw [bshift_eq_shift_sub hk i₁ (by omega), shift_add, shift_mod]
      have hrew2 : ∀ (a b : ℕ), a + b < k →
          bshift hk (bshift hk i₁ a) b = bshift hk i₁ (a + b) := by
        intro a b hab
        rw [bshift_eq_shift_sub hk i₁ (by omega), bshift_eq_shift_sub hk _ (by omega),
          bshift_eq_shift_sub hk i₁ (by omega), shift_add, shift_eq_iff]
        have : k - a + (k - b) = k + (k - (a + b)) := by omega
        rw [this, Nat.add_mod_left]
      interval_cases t
      · -- 0 -> bshift i₁ 8
        have : shift hk (bshift hk i₁ 8) 0 = bshift hk (bshift hk i₁ 4) 4 := by
          rw [shift_zero, hrew2 4 4 (by omega)]
        rw [this]; exact hm8
      · -- 1 -> bshift i₁ 7
        have : shift hk (bshift hk i₁ 8) 1 = bshift hk (bshift hk i₁ 3) 4 := by
          rw [hrew2 3 4 (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            bshift_eq_shift_sub hk i₁ (by omega), shift_add]; congr 1; omega
        rw [this]; exact hm7
      · -- 2 -> bshift i₁ 6
        have : shift hk (bshift hk i₁ 8) 2 = bshift hk (bshift hk i₁ 3) 3 := by
          rw [hrew2 3 3 (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            bshift_eq_shift_sub hk i₁ (by omega), shift_add]; congr 1; omega
        rw [this]; exact hm6
      · -- 3 -> bshift i₁ 5
        have : shift hk (bshift hk i₁ 8) 3 = bshift hk (bshift hk i₁ 1) 4 := by
          rw [hrew2 1 4 (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            bshift_eq_shift_sub hk i₁ (by omega), shift_add]; congr 1; omega
        rw [this]; exact hm5
      · -- 4 -> bshift i₁ 4
        have : shift hk (bshift hk i₁ 8) 4 = bshift hk (bshift hk i₁ 1) 3 := by
          rw [hrew2 1 3 (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            bshift_eq_shift_sub hk i₁ (by omega), shift_add]; congr 1; omega
        rw [this]; exact hm4
      · -- 5 -> bshift i₁ 3
        have : shift hk (bshift hk i₁ 8) 5 = shift hk (bshift hk i₁ 4) 1 := by
          rw [bshift_eq_shift_sub hk i₁ (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            shift_add, shift_add]; congr 1; omega
        rw [this]; exact hm3
      · -- 6 -> bshift i₁ 2
        have : shift hk (bshift hk i₁ 8) 6 = shift hk (bshift hk i₁ 3) 1 := by
          rw [bshift_eq_shift_sub hk i₁ (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            shift_add, shift_add]; congr 1; omega
        rw [this]; exact hm2
      · -- 7 -> bshift i₁ 1
        have : shift hk (bshift hk i₁ 8) 7 = shift hk (bshift hk i₁ 3) 2 := by
          rw [bshift_eq_shift_sub hk i₁ (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            shift_add, shift_add]; congr 1; omega
        rw [this]; exact hm1
      · -- 8 -> i₁
        have : shift hk (bshift hk i₁ 8) 8 = shift hk (bshift hk i₁ 1) 1 := by
          rw [shift_bshift, shift_bshift]
        rw [this]; exact h0
      · -- 9 -> shift i₁ 1
        have : shift hk (bshift hk i₁ 8) 9 = shift hk (bshift hk i₁ 1) 2 := by
          rw [bshift_eq_shift_sub hk i₁ (by omega), bshift_eq_shift_sub hk i₁ (by omega),
            shift_add, shift_add, shift_eq_iff]
          have h1 : k - 8 + 9 = k + 1 := by omega
          have h2 : k - 1 + 2 = k + 1 := by omega
          rw [h1, h2]
        rw [this]; exact hp1
      · -- 10 -> shift i₁ 2
        have : shift hk (bshift hk i₁ 8) 10 = shift hk (shift hk i₁ 1) 1 := by
          rw [bshift_eq_shift_sub hk i₁ (by omega), shift_add, shift_add, shift_eq_iff]
          have h1 : k - 8 + 10 = k + 2 := by omega
          rw [h1, Nat.add_mod_left]
        rw [this]; exact hp2
    have hind : ∀ n : ℕ, ∀ t ≤ 5 * (n + 2),
        unit (shift hk (bshift hk i₁ (4 * (n + 2))) t) ∈ Reach hk 2 (n + 3) u₀ := by
      intro n
      induction n with
      | zero => exact hbase2
      | succ n ih =>
        intro t ht
        let base := bshift hk i₁ (4 * (n + 2))
        by_cases hle : t ≤ 5 * (n + 2)
        · have hprev := ih t hle
          have hstep := (d2_from_unit hk hk11 hk3 (n + 3) u₀ (shift hk base t) hprev).1
          have heq : bshift hk (shift hk base t) 4 = shift hk (bshift hk i₁ (4 * (n + 3))) t := by
            simp only [base, bshift_eq_shift, shift_add, shift_eq_iff]
            have h1 : 4 * (n + 2) % k < k := Nat.mod_lt _ hk
            have h2 : 4 % k < k := Nat.mod_lt _ hk
            have h3 : 4 * (n + 3) % k < k := Nat.mod_lt _ hk
            have hmod : (4 * (n + 3)) % k = (4 * (n + 2) % k + 4 % k) % k := by
              have : 4 * (n + 3) = 4 * (n + 2) + 4 := by omega
              rw [this, Nat.add_mod]
            have hsum1 : (k - 4 * (n + 2) % k + t + (k - 4 % k) + (4 * (n + 2) % k + 4 % k)) % k =
                t % k := by
              have : k - 4 * (n + 2) % k + t + (k - 4 % k) + (4 * (n + 2) % k + 4 % k) = 2 * k + t := by omega
              rw [this]; simp [Nat.add_mod]
            have hsum2 : (k - 4 * (n + 3) % k + t + (4 * (n + 2) % k + 4 % k)) % k = t % k := by
              rw [Nat.add_mod, ← hmod]
              have : ((k - 4 * (n + 3) % k + t) % k + 4 * (n + 3) % k) % k =
                  (k - 4 * (n + 3) % k + t + 4 * (n + 3) % k) % k := by
                rw [Nat.add_mod]; conv_rhs => rw [Nat.add_mod]
                simp only [Nat.mod_mod]
              rw [this, show k - 4 * (n + 3) % k + t + 4 * (n + 3) % k = k + t by omega, Nat.add_mod_left]
            have heq' : (k - 4 * (n + 2) % k + t + (k - 4 % k) + (4 * (n + 2) % k + 4 % k)) % k =
                (k - 4 * (n + 3) % k + t + (4 * (n + 2) % k + 4 % k)) % k := by
              rw [hsum1, hsum2]
            -- Subtract (4 * (n + 2) % k + 4 % k) mod k
            exact add_mod_cancel hk _ _ _ (by simpa [Nat.add_assoc] using heq')
          rw [heq] at hstep; exact hstep
        · -- t > 5 * (n + 2), so t - 5 ≤ 5 * (n + 2) and t ≥ 5! Use shift · 1!
          have hprev := ih (t - 5) (by omega)
          have hstep := (d2_from_unit hk hk11 hk3 (n + 3) u₀ (shift hk base (t - 5)) hprev).2.1
          have heq : shift hk (shift hk base (t - 5)) 1 = shift hk (bshift hk i₁ (4 * (n + 3))) t := by
            simp only [base, bshift_eq_shift, shift_add, shift_eq_iff]
            have h1 : 4 * (n + 2) % k < k := Nat.mod_lt _ hk
            have h3 : 4 * (n + 3) % k < k := Nat.mod_lt _ hk
            apply add_mod_cancel hk _ _ (4 * (n + 3))
            have hL : (k - 4 * (n + 2) % k + (t - 5) + 1 + 4 * (n + 3)) % k = t % k := by
              have h43 : 4 * (n + 3) = 4 * (n + 2) + 4 := by omega
              rw [h43]
              have hmod : (k - 4 * (n + 2) % k + (t - 5) + 1 + (4 * (n + 2) + 4)) % k =
                  (k - 4 * (n + 2) % k + (t - 5) + 1 + (4 * (n + 2) % k + 4)) % k := by
                rw [Nat.add_mod, Nat.add_mod (4 * (n + 2)) 4]
                conv_rhs => rw [Nat.add_mod, Nat.add_mod (4 * (n + 2) % k) 4, Nat.mod_mod]
              rw [hmod]
              have : k - 4 * (n + 2) % k + (t - 5) + 1 + (4 * (n + 2) % k + 4) = k + t := by omega
              rw [this, Nat.add_mod_left]
            have hR : (k - 4 * (n + 3) % k + t + 4 * (n + 3)) % k = t % k := by
              have hmod : (k - 4 * (n + 3) % k + t + 4 * (n + 3)) % k =
                  (k - 4 * (n + 3) % k + t + 4 * (n + 3) % k) % k := by
                rw [Nat.add_mod]
                conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
              rw [hmod]
              have : k - 4 * (n + 3) % k + t + 4 * (n + 3) % k = k + t := by omega
              rw [this, Nat.add_mod_left]
            rw [hL, hR]
          rw [heq] at hstep; exact hstep
    intro j
    have hs_eq : s = (s - 2) + 2 := by omega
    let baseS := bshift hk i₁ (4 * ((s - 2) + 2))
    obtain ⟨t, ht, rfl⟩ : ∃ t < k, j = shift hk baseS t := by
      refine ⟨(j.val + k - baseS.val) % k, Nat.mod_lt _ hk, ?_⟩
      apply Fin.ext
      simp only [shift, ix]
      have hb1 : baseS.val < k := baseS.isLt
      have hj1 : j.val < k := j.isLt
      have h1 : (baseS.val + (j.val + k - baseS.val) % k) % k =
          (baseS.val + (j.val + k - baseS.val)) % k := by
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [h1]
      have h2 : baseS.val + (j.val + k - baseS.val) = j.val + k := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hj1]
    have hmem := hind (s - 2) t (by omega)
    have hidx : (s - 2) + 3 = s + 1 := by omega
    rw [hidx] at hmem
    exact hmem

/-! ## Step 5: `q`-Fold Toggle Cube Sum = `dotProduct outputMask (iterB D₀ pulseSite)` -/

private def stateAt (d start : ℕ) (feed : ℕ → ℕ) (name : W k) {q : ℕ}
    (schedule : Fin q → W k) (key : W k) : ∀ (m : ℕ), m ≤ q → W k
  | 0, _ => rot hk start key + name
  | m + 1, hm =>
      chi hk (mix hk d (stateAt d start feed name schedule key m (by omega))) +
      rot hk (feed m) key + schedule ⟨m, hm⟩

private lemma foldl_finRange_take (d start : ℕ) (feed : ℕ → ℕ) (name : W k) {q : ℕ}
    (schedule : Fin q → W k) (key : W k) :
    ∀ (m : ℕ) (hm : m ≤ q),
      ((List.finRange q).take m).foldl
        (fun prev idx => chi hk (mix hk d prev) + rot hk (feed idx.val) key + schedule idx)
        (rot hk start key + name) =
      stateAt hk d start feed name schedule key m hm := by
  intro m
  induction m with
  | zero => intro _; simp [stateAt]
  | succ m ih =>
    intro hm
    have htake : (List.finRange q).take (m + 1) = (List.finRange q).take m ++ [⟨m, hm⟩] := by
      have hlen : m < (List.finRange q).length := by simp only [List.length_finRange]; omega
      rw [List.take_succ_eq_append_getElem hlen]
      simp
    rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil, ih (by omega)]
    rfl

private lemma foldl_finRange_eq (d start : ℕ) (feed : ℕ → ℕ) (name : W k) {q : ℕ}
    (schedule : Fin q → W k) (key : W k) :
    (List.finRange q).foldl
      (fun prev idx => chi hk (mix hk d prev) + rot hk (feed idx.val) key + schedule idx)
      (rot hk start key + name) =
    stateAt hk d start feed name schedule key q (le_refl q) := by
  have h1 := foldl_finRange_take hk d start feed name schedule key q (le_refl q)
  have htake : (List.finRange q).take q = List.finRange q := by
    apply List.take_of_length_le; simp
  rw [htake] at h1
  exact h1

private lemma stateAt_congr (d start : ℕ) (feed : ℕ → ℕ) (name : W k) {q : ℕ}
    (s₁ s₂ : Fin q → W k) (key : W k) (m : ℕ) (hm : m ≤ q)
    (h : ∀ j : Fin q, j.val < m → s₁ j = s₂ j) :
    stateAt hk d start feed name s₁ key m hm = stateAt hk d start feed name s₂ key m hm := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [stateAt]
    rw [ih (by omega) (fun j hj => h j (by omega)), h ⟨m, hm⟩ (Nat.lt_succ_self m)]

private lemma cube_sum_stateAt (d start : ℕ) (feed : ℕ → ℕ) (name base v : W k)
    (partner : Fin k) {q : ℕ} (pulseSite : Fin q → Fin k) (c : Fin q → W k) :
    ∀ (m : ℕ) (hm : m < q),
      let D₀ := B hk d (rot hk start v) (rot hk start (unit partner))
      let keys : Fin 4 → W k := fun a =>
        match a.val with
        | 0 => base + v + unit partner
        | 1 => base + v
        | 2 => base + unit partner
        | _ => base
      let sched := fun (bits : Fin m → Bool) (j : Fin q) =>
        c j + if h : j.val < m then (if bits ⟨j.val, h⟩ then unit (pulseSite j) else 0) else 0
      (∑ bits : Fin m → Bool, ∑ a : Fin 4,
        stateAt hk d start feed name (sched bits) (keys a) (m + 1) hm) =
      iterB hk d D₀ (fun i : Fin m => pulseSite ⟨i.val, by omega⟩) := by
  intro m
  induction m with
  | zero =>
    intro hm D₀ keys sched
    have huniq : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext f; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim f Fin.elim0
    rw [huniq, Finset.sum_singleton, Fin.sum_univ_four]
    simp only [stateAt, keys, sched, iterB, D₀, Nat.lt_irrefl, ↓reduceDIte, add_zero]
    have hrot : rot hk (feed 0) (base + v + unit partner) + rot hk (feed 0) (base + v) +
        rot hk (feed 0) (base + unit partner) + rot hk (feed 0) base = 0 := by
      simp only [rot_add]
      funext j; simp only [Pi.add_apply, Pi.zero_apply]
      have h1 := z2_sum_four (rot hk (feed 0) base j)
      have h2 := z2_add_self (rot hk (feed 0) v j)
      have h3 := z2_add_self (rot hk (feed 0) (unit partner) j)
      linear_combination h1 + h2 + h3
    have hchi : chi hk (mix hk d (rot hk start (base + v + unit partner) + name)) +
        chi hk (mix hk d (rot hk start (base + v) + name)) +
        chi hk (mix hk d (rot hk start (base + unit partner) + name)) +
        chi hk (mix hk d (rot hk start base + name)) =
        B hk d (rot hk start v) (rot hk start (unit partner)) := by
      have h1 : rot hk start (base + v + unit partner) + name =
          (rot hk start base + name) + rot hk start v + rot hk start (unit partner) := by
        simp only [rot_add]; funext j; simp only [Pi.add_apply]; ring
      have h2 : rot hk start (base + v) + name = (rot hk start base + name) + rot hk start v := by
        simp only [rot_add]; funext j; simp only [Pi.add_apply]; ring
      have h3 : rot hk start (base + unit partner) + name =
          (rot hk start base + name) + rot hk start (unit partner) := by
        simp only [rot_add]; funext j; simp only [Pi.add_apply]; ring
      rw [h1, h2, h3]
      exact chi_mix_diff2 hk d (rot hk start base + name) (rot hk start v) (rot hk start (unit partner))
    funext j
    have hj1 := congrFun hrot j
    have hj2 := congrFun hchi j
    simp only [Pi.add_apply, Pi.zero_apply] at hj1 hj2 ⊢
    have hc4 := z2_sum_four (c ⟨0, hm⟩ j)
    linear_combination hj1 + hj2 + hc4
  | succ m ih =>
    intro hm D₀ keys sched
    -- Split `bits : Fin (m + 1) → Bool` into `(bits' : Fin m → Bool, bLast : Bool)`!
    let e : (Fin (m + 1) → Bool) ≃ (Fin m → Bool) × Bool :=
      { toFun := fun f => (fun i => f i.castSucc, f (Fin.last m))
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun f => by
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp
          · intro j; simp
        right_inv := fun ⟨g, b⟩ => by
          apply Prod.ext
          · funext i; simp
          · simp }
    rw [Fintype.sum_equiv e _ (fun p => ∑ a : Fin 4,
      stateAt hk d start feed name (sched (Fin.snoc p.1 p.2)) (keys a) (m + 2) hm) (fun f => by
        dsimp [e]
        have hsnoc : Fin.snoc (fun i : Fin m => f i.castSucc) (f (Fin.last m)) = f := by
          funext i; refine Fin.lastCases ?_ ?_ i <;> simp
        rw [hsnoc])]
    rw [Fintype.sum_prod_type]
    have hbase_st : ∀ (g : Fin m → Bool) (a : Fin 4),
        let sched0 := fun (j : Fin q) =>
          c j + if h : j.val < m then (if g ⟨j.val, h⟩ then unit (pulseSite j) else 0) else 0
        stateAt hk d start feed name (sched (Fin.snoc g false)) (keys a) (m + 1) (by omega) =
          stateAt hk d start feed name sched0 (keys a) (m + 1) (by omega) ∧
        stateAt hk d start feed name (sched (Fin.snoc g true)) (keys a) (m + 1) (by omega) =
          stateAt hk d start feed name sched0 (keys a) (m + 1) (by omega) +
          unit (pulseSite ⟨m, by omega⟩) := by
      intro g a sched0
      have heq_m : ∀ (b : Bool),
          stateAt hk d start feed name (sched (Fin.snoc g b)) (keys a) m (by omega) =
          stateAt hk d start feed name sched0 (keys a) m (by omega) := by
        intro b
        apply stateAt_congr
        intro j hj
        have hjm : j.val < m + 1 := by omega
        simp only [sched, sched0, hj, hjm, ↓reduceDIte]
        have hsn : Fin.snoc (α := fun _ => Bool) g b ⟨j.val, hjm⟩ = g ⟨j.val, hj⟩ := by
          simp [Fin.snoc, hj]
        rw [hsn]
      constructor
      · simp only [stateAt, heq_m false]
        congr 1
        simp only [sched, sched0, Nat.lt_succ_self, Nat.lt_irrefl, ↓reduceDIte]
        have hlast : Fin.snoc (α := fun _ => Bool) g false ⟨m, Nat.lt_succ_self m⟩ = false := by
          change Fin.snoc (α := fun _ => Bool) g false (Fin.last m) = false
          simp
        simp [hlast]
      · simp only [stateAt, heq_m true]
        simp only [sched, sched0, Nat.lt_succ_self, Nat.lt_irrefl, ↓reduceDIte, add_zero]
        have hlast : Fin.snoc (α := fun _ => Bool) g true ⟨m, Nat.lt_succ_self m⟩ = true := by
          change Fin.snoc (α := fun _ => Bool) g true (Fin.last m) = true
          simp
        simp only [hlast, ↓reduceIte]
        funext j; simp only [Pi.add_apply]; ring
    have hinner : ∀ g : Fin m → Bool,
        let sched0 := fun (j : Fin q) =>
          c j + if h : j.val < m then (if g ⟨j.val, h⟩ then unit (pulseSite j) else 0) else 0
        (∑ b : Bool, ∑ a : Fin 4,
          stateAt hk d start feed name (sched (Fin.snoc g b)) (keys a) (m + 2) hm) =
        B hk d (∑ a : Fin 4, stateAt hk d start feed name sched0 (keys a) (m + 1) (by omega))
          (unit (pulseSite ⟨m, by omega⟩)) := by
      intro g sched0
      rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
      have hpair : ∀ a : Fin 4,
          stateAt hk d start feed name (sched (Fin.snoc g true)) (keys a) (m + 2) hm +
          stateAt hk d start feed name (sched (Fin.snoc g false)) (keys a) (m + 2) hm =
          chi hk (mix hk d (unit (pulseSite ⟨m, by omega⟩))) +
          B hk d (stateAt hk d start feed name sched0 (keys a) (m + 1) (by omega))
            (unit (pulseSite ⟨m, by omega⟩)) := by
        intro a
        have ⟨hf, ht⟩ := hbase_st g a
        change (chi hk (mix hk d (stateAt hk d start feed name (sched (Fin.snoc g true)) (keys a) (m + 1) (by omega))) +
            rot hk (feed (m + 1)) (keys a) + sched (Fin.snoc g true) ⟨m + 1, hm⟩) +
          (chi hk (mix hk d (stateAt hk d start feed name (sched (Fin.snoc g false)) (keys a) (m + 1) (by omega))) +
            rot hk (feed (m + 1)) (keys a) + sched (Fin.snoc g false) ⟨m + 1, hm⟩) = _
        rw [hf, ht]
        have hs_eq : sched (Fin.snoc g true) ⟨m + 1, hm⟩ = sched (Fin.snoc g false) ⟨m + 1, hm⟩ := by
          simp [sched]
        rw [hs_eq]
        have hdiff := chi_mix_diff1 hk d
          (stateAt hk d start feed name sched0 (keys a) (m + 1) (by omega))
          (unit (pulseSite ⟨m, by omega⟩))
        funext j
        have hj := congrFun hdiff j
        simp only [Pi.add_apply] at hj ⊢
        have hr2 := z2_add_self (rot hk (feed (m + 1)) (keys a) j)
        have hc2 := z2_add_self (sched (Fin.snoc g false) ⟨m + 1, hm⟩ j)
        linear_combination hj + hr2 + hc2
      simp_rw [hpair, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      rw [B_sum_left]
      have h4 : (4 : ℕ) • chi hk (mix hk d (unit (pulseSite ⟨m, by omega⟩))) = 0 := by
        funext j
        simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
        have : ((4 : ℕ) : ZMod 2) = 0 := by decide
        rw [this, zero_mul]
      rw [h4, zero_add]
    simp_rw [hinner]
    rw [← B_sum_left, ih (by omega)]
    rfl

private lemma cube_sum_delta (d start : ℕ) (feed : ℕ → ℕ) (name finalConst base v : W k)
    (partner : Fin k) (outputMask : W k) (other : W k → ZMod 2)
    {q : ℕ} (hq : 1 ≤ q) (pulseSite : Fin q → Fin k) (c : Fin q → W k) :
    let run := fun (schedule : Fin q → W k) (key : W k) =>
      chi hk (mix hk d ((List.finRange q).foldl
        (fun prev idx => chi hk (mix hk d prev) + rot hk (feed idx.val) key + schedule idx)
        (rot hk start key + name))) + rot hk (feed q) key + finalConst
    let obs := fun (cst : Fin q → W k) (w : W k) => dotProduct outputMask (run cst w) + other w
    let delta := fun cst : Fin q → W k =>
      obs cst (base + v + unit partner) + obs cst (base + v) +
      obs cst (base + unit partner) + obs cst base
    let D₀ := B hk d (rot hk start v) (rot hk start (unit partner))
    (∑ bits : Fin q → Bool, delta (fun j => c j + if bits j then unit (pulseSite j) else 0)) =
      dotProduct outputMask (iterB hk d D₀ pulseSite) := by
  intro run obs delta D₀
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  let keys : Fin 4 → W k := fun a =>
    match a.val with
    | 0 => base + v + unit partner
    | 1 => base + v
    | 2 => base + unit partner
    | _ => base
  let sched := fun (bits : Fin (m + 1) → Bool) (j : Fin (m + 1)) =>
    c j + if bits j then unit (pulseSite j) else 0
  have hdelta_rw : ∀ bits : Fin (m + 1) → Bool,
      delta (sched bits) =
      dotProduct outputMask (∑ a : Fin 4, run (sched bits) (keys a)) +
      (∑ a : Fin 4, other (keys a)) := by
    intro bits
    have hk0 : keys 0 = base + v + unit partner := rfl
    have hk1 : keys 1 = base + v := rfl
    have hk2 : keys 2 = base + unit partner := rfl
    have hk3 : keys 3 = base := rfl
    rw [Fin.sum_univ_four, Fin.sum_univ_four, hk0, hk1, hk2, hk3]
    dsimp only [delta, obs]
    simp only [dotProduct_add]
    ring
  change (∑ bits : Fin (m + 1) → Bool, delta (sched bits)) = _
  simp_rw [hdelta_rw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have heven : (2 ^ (m + 1) : ℕ) • (∑ a : Fin 4, other (keys a)) = 0 := by
    rw [nsmul_eq_mul, Nat.cast_pow]
    have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
    rw [h2, zero_pow (Nat.succ_ne_zero m), zero_mul]
  rw [heven, add_zero, ← dotProduct_sum]
  congr 1
  -- Now prove: ∑ bits, ∑ a, run (sched bits) (keys a) = iterB D₀ pulseSite!
  let e : (Fin (m + 1) → Bool) ≃ (Fin m → Bool) × Bool :=
    { toFun := fun f => (fun i => f i.castSucc, f (Fin.last m))
      invFun := fun p => Fin.snoc p.1 p.2
      left_inv := fun f => by funext i; refine Fin.lastCases ?_ ?_ i <;> simp
      right_inv := fun ⟨g, b⟩ => by apply Prod.ext <;> [funext i; skip] <;> simp }
  rw [Fintype.sum_equiv e _ (fun p => ∑ a : Fin 4, run (sched (Fin.snoc p.1 p.2)) (keys a))
    (fun f => by
      dsimp [e]
      have hsnoc : Fin.snoc (fun i : Fin m => f i.castSucc) (f (Fin.last m)) = f := by
        funext i; refine Fin.lastCases ?_ ?_ i <;> simp
      rw [hsnoc])]
  rw [Fintype.sum_prod_type]
  have hbase_st : ∀ (g : Fin m → Bool) (a : Fin 4),
      let sched0 := fun (j : Fin (m + 1)) =>
        c j + if h : j.val < m then (if g ⟨j.val, h⟩ then unit (pulseSite j) else 0) else 0
      stateAt hk d start feed name (sched (Fin.snoc g false)) (keys a) (m + 1) (le_refl _) =
        stateAt hk d start feed name sched0 (keys a) (m + 1) (le_refl _) ∧
      stateAt hk d start feed name (sched (Fin.snoc g true)) (keys a) (m + 1) (le_refl _) =
        stateAt hk d start feed name sched0 (keys a) (m + 1) (le_refl _) +
        unit (pulseSite (Fin.last m)) := by
    intro g a sched0
    have heq_m : ∀ (b : Bool),
        stateAt hk d start feed name (sched (Fin.snoc g b)) (keys a) m (by omega) =
        stateAt hk d start feed name sched0 (keys a) m (by omega) := by
      intro b
      apply stateAt_congr
      intro j hj
      simp only [sched, sched0, hj, ↓reduceDIte]
      have hsn : Fin.snoc (α := fun _ => Bool) g b j = g ⟨j.val, hj⟩ := by
        simp [Fin.snoc, hj]; rfl
      rw [hsn]
    constructor
    · simp only [stateAt, heq_m false]
      congr 1
      simp only [sched, sched0, Nat.lt_irrefl, ↓reduceDIte]
      have hlast : Fin.snoc (α := fun _ => Bool) g false ⟨m, Nat.lt_succ_self m⟩ = false := by
        change Fin.snoc (α := fun _ => Bool) g false (Fin.last m) = false
        simp
      simp [hlast]
    · simp only [stateAt, heq_m true]
      simp only [sched, sched0, Nat.lt_irrefl, ↓reduceDIte, add_zero]
      have hlast : Fin.snoc (α := fun _ => Bool) g true ⟨m, Nat.lt_succ_self m⟩ = true := by
        change Fin.snoc (α := fun _ => Bool) g true (Fin.last m) = true
        simp
      simp only [hlast, ↓reduceIte]
      funext j; simp only [Pi.add_apply]
      have hml : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := rfl
      rw [hml]
      ring
  have hinner : ∀ g : Fin m → Bool,
      let sched0 := fun (j : Fin (m + 1)) =>
        c j + if h : j.val < m then (if g ⟨j.val, h⟩ then unit (pulseSite j) else 0) else 0
      (∑ b : Bool, ∑ a : Fin 4, run (sched (Fin.snoc g b)) (keys a)) =
      B hk d (∑ a : Fin 4, stateAt hk d start feed name sched0 (keys a) (m + 1) (le_refl _))
        (unit (pulseSite (Fin.last m))) := by
    intro g sched0
    rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
    have hpair : ∀ a : Fin 4,
        run (sched (Fin.snoc g true)) (keys a) + run (sched (Fin.snoc g false)) (keys a) =
        chi hk (mix hk d (unit (pulseSite (Fin.last m)))) +
        B hk d (stateAt hk d start feed name sched0 (keys a) (m + 1) (le_refl _))
          (unit (pulseSite (Fin.last m))) := by
      intro a
      have ⟨hf, ht⟩ := hbase_st g a
      simp only [run, foldl_finRange_eq]
      rw [hf, ht]
      have hdiff := chi_mix_diff1 hk d
        (stateAt hk d start feed name sched0 (keys a) (m + 1) (le_refl _))
        (unit (pulseSite (Fin.last m)))
      funext j
      have hj := congrFun hdiff j
      simp only [Pi.add_apply] at hj ⊢
      have hr2 := z2_add_self (rot hk (feed (m + 1)) (keys a) j)
      have hc2 := z2_add_self (finalConst j)
      linear_combination hj + hr2 + hc2
    simp_rw [hpair, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [B_sum_left]
    have h4 : (4 : ℕ) • chi hk (mix hk d (unit (pulseSite (Fin.last m)))) = 0 := by
      funext j
      simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
      have : ((4 : ℕ) : ZMod 2) = 0 := by decide
      rw [this, zero_mul]
    rw [h4, zero_add]
  simp_rw [hinner]
  rw [← B_sum_left]
  have hprev := cube_sum_stateAt hk d start feed name base v partner pulseSite c m (Nat.lt_succ_self m)
  rw [hprev]
  rfl

/-! ## Step 6: Double Counting & Main Proof -/

private lemma double_count {q : ℕ} (pulseSite : Fin q → Fin k)
    (delta : (Fin q → W k) → ZMod 2)
    (hsum : ∀ c : Fin q → W k,
      (∑ bits : Fin q → Bool, delta (fun j => c j + if bits j then unit (pulseSite j) else 0)) = 1) :
    2 ^ (k * q) ≤ 2 ^ q * (Finset.univ.filter (fun c : Fin q → W k => delta c ≠ 0)).card := by
  have h1 : ∀ c : Fin q → W k,
      1 ≤ ∑ bits : Fin q → Bool,
        if delta (fun j => c j + if bits j then unit (pulseSite j) else 0) ≠ 0 then 1 else 0 := by
    intro c
    have hex : ∃ bits : Fin q → Bool,
        delta (fun j => c j + if bits j then unit (pulseSite j) else 0) ≠ 0 := by
      by_contra h
      push Not at h
      have hz : (∑ bits : Fin q → Bool,
          delta (fun j => c j + if bits j then unit (pulseSite j) else 0)) = 0 :=
        Finset.sum_eq_zero (fun b _ => h b)
      rw [hsum c] at hz
      exact one_ne_zero hz
    obtain ⟨b, hb⟩ := hex
    have hle := Finset.single_le_sum (f := fun bits : Fin q → Bool =>
      if delta (fun j => c j + if bits j then unit (pulseSite j) else 0) ≠ 0 then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    simpa [hb] using hle
  have htot : (∑ _c : Fin q → W k, (1 : ℕ)) ≤
      ∑ c : Fin q → W k, ∑ bits : Fin q → Bool,
        if delta (fun j => c j + if bits j then unit (pulseSite j) else 0) ≠ 0 then 1 else 0 :=
    Finset.sum_le_sum fun c _ => h1 c
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, ZMod.card, smul_eq_mul, mul_one, ← pow_mul] at htot
  rw [Finset.sum_comm] at htot
  have hinner : ∀ bits : Fin q → Bool,
      (∑ c : Fin q → W k,
        if delta (fun j => c j + if bits j then unit (pulseSite j) else 0) ≠ 0 then 1 else 0) =
      (Finset.univ.filter (fun c : Fin q → W k => delta c ≠ 0)).card := by
    intro bits
    let e : (Fin q → W k) ≃ (Fin q → W k) :=
      { toFun := fun c j => c j + if bits j then unit (pulseSite j) else 0
        invFun := fun c j => c j + if bits j then unit (pulseSite j) else 0
        left_inv := fun c => by
          funext j i
          by_cases hb : bits j <;> simp [hb, add_assoc, z2_add_self]
        right_inv := fun c => by
          funext j i
          by_cases hb : bits j <;> simp [hb, add_assoc, z2_add_self] }
    have heq := Fintype.sum_equiv e
      (fun c => if delta (fun j => c j + if bits j then unit (pulseSite j) else 0) ≠ 0 then 1 else 0)
      (fun c => if delta c ≠ 0 then 1 else 0) (fun _ => rfl)
    rw [heq, Finset.card_filter]
  simp_rw [hinner, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, smul_eq_mul] at htot
  exact htot

end Core

private lemma main_proof (k d s : ℕ) (hk : 0 < k) (hk11 : 11 ≤ k) (hk3 : k % 3 ≠ 0)
    (hd : d = 1 ∨ d = 2) (hs2 : 2 ≤ s) (hks : k ≤ (2 * d + 1) * s + 1) :
    let F := ZMod 2
    let W := Fin k → F
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (offset : ℕ) (w : W) (j : Fin k) => w (ix (j.val + k - offset % k))
    let mix := fun (word : W) (mid : Fin k) =>
      word mid + word (ix (mid.val + d)) + word (ix (mid.val + k - d % k))
    let chi := fun (z : W) (dest : Fin k) =>
      z dest + (1 + z (ix (dest.val + 1))) * z (ix (dest.val + 2))
    let q := s + 1
    ∀ (start : ℕ) (feed : ℕ → ℕ),
      let tick := fun (tickNo : ℕ) (key state : W) => chi (mix state) + rot (feed tickNo) key
      let run := fun (name finalConst : W) (schedule : Fin q → W) (key : W) =>
        tick q key ((List.finRange q).foldl
          (fun prev idx => tick idx.val key prev + schedule idx) (rot start key + name)) + finalConst
      let unit := fun (pos coord : Fin k) => if coord = pos then (1 : F) else 0
      ∀ v : W, v ≠ 0 → ∃ partner : Fin k, ∀ outputMask : W, outputMask ≠ 0 →
        ∃ pulseSite : Fin q → Fin k, ∀ (name finalConst base : W) (other : W → F),
          let obs := fun (cst : Fin q → W) (w : W) => dotProduct outputMask (run name finalConst cst w) + other w
          let delta := fun c : Fin q → W =>
            obs c (base + v + unit partner) + obs c (base + v) + obs c (base + unit partner) + obs c base
          (∀ c : Fin q → W,
            (∑ bits : Fin q → Bool, delta (fun j => c j + if bits j then unit (pulseSite j) else 0)) = 1) ∧
          2 ^ (k * q) ≤ 2 ^ q * (Finset.univ.filter (fun c : Fin q → W => delta c ≠ 0)).card := by
  intro F W ix_l rot_l mix_l chi_l q start feed tick run unit_l v hv
  obtain ⟨partner, hD₀_ne, hD₀_supp⟩ := exists_partner hk hk11 hk3 hd start hv
  refine ⟨partner, fun outputMask hmask => ?_⟩
  let D₀ := B hk d (rot hk start v) (rot hk start (unit partner))
  obtain ⟨i₁, hi₁⟩ := exists_singleton_reach1 hk hk11 hk3 hd hD₀_ne hD₀_supp
  have hall_units : ∀ j : Fin k, unit j ∈ Reach hk d q D₀ :=
    reach_all_units hk hk11 hk3 hd hs2 hks D₀ hi₁
  have hex_pulse : ∃ pulseSite : Fin q → Fin k, dotProduct outputMask (iterB hk d D₀ pulseSite) = 1 := by
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin k, outputMask j₀ ≠ 0 := by
      by_contra h; push Not at h; exact hmask (funext h)
    have h1 : dotProduct outputMask (unit j₀) = 1 := by
      simp only [dotProduct, unit, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ j₀ outputMask]
      simp [z2_eq_one_of_ne_zero hj₀]
    by_contra hnone
    push Not at hnone
    have hzero : ∀ p : Fin q → Fin k, dotProduct outputMask (iterB hk d D₀ p) = 0 := by
      intro p
      by_contra hne
      exact hnone p (z2_eq_one_of_ne_zero hne)
    let φ : L_meta_25761_aux.W k →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun x => dotProduct outputMask x
        map_add' := fun x y => dotProduct_add outputMask x y
        map_smul' := fun c x => dotProduct_smul c outputMask x }
    have hker : Reach hk d q D₀ ≤ LinearMap.ker φ := by
      rw [Reach, Submodule.span_le]
      rintro _ ⟨p, rfl⟩
      exact hzero p
    have hmem : unit j₀ ∈ LinearMap.ker φ := hker (hall_units j₀)
    change dotProduct outputMask (unit j₀) = 0 at hmem
    rw [h1] at hmem
    exact one_ne_zero hmem
  obtain ⟨pulseSite, hpulse⟩ := hex_pulse
  refine ⟨pulseSite, fun name finalConst base other => ?_⟩
  intro obs delta
  have hsum : ∀ c : Fin q → W,
      (∑ bits : Fin q → Bool, delta (fun j => c j + if bits j then unit_l (pulseSite j) else 0)) = 1 := by
    intro c
    have h := cube_sum_delta hk d start feed name finalConst base v partner outputMask other
      (by omega : 1 ≤ q) pulseSite c
    dsimp only at h
    rw [hpulse] at h
    exact h
  exact ⟨hsum, double_count pulseSite delta hsum⟩

end PEqualNP.Outside.L_meta_25761_aux

theorem PEqualNP.Outside.L_meta_25761 :
    ∀ (k d s : ℕ) (hk : 0 < k), 11 ≤ k → k % 3 ≠ 0 → (d = 1 ∨ d = 2) →
      2 ≤ s → k ≤ (2*d+1)*s+1 →
      let F := ZMod 2
      let W := Fin k → F
      let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let rot := fun (offset : ℕ) (w : W) (j : Fin k) => w (ix (j.val+k-offset % k))
      let mix := fun (word : W) (mid : Fin k) =>
        word mid + word (ix (mid.val+d)) + word (ix (mid.val+k-d % k))
      let chi := fun (z : W) (dest : Fin k) =>
        z dest + (1+z (ix (dest.val+1)))*z (ix (dest.val+2))
      let q := s+1
      ∀ (start : ℕ) (feed : ℕ → ℕ),
        let tick := fun (tickNo : ℕ) (key state : W) => chi (mix state) + rot (feed tickNo) key
        let run := fun (name finalConst : W) (schedule : Fin q → W) (key : W) =>
          tick q key ((List.finRange q).foldl
            (fun prev idx => tick idx.val key prev + schedule idx) (rot start key + name)) + finalConst
        let unit := fun (pos coord : Fin k) => if coord = pos then (1:F) else 0
        ∀ v : W, v ≠ 0 → ∃ partner : Fin k, ∀ outputMask : W, outputMask ≠ 0 →
          ∃ pulseSite : Fin q → Fin k, ∀ (name finalConst base : W) (other : W → F),
            let obs := fun (cst : Fin q → W) (w : W) => dotProduct outputMask (run name finalConst cst w) + other w
            let delta := fun c : Fin q → W =>
              obs c (base+v+unit partner) + obs c (base+v) + obs c (base+unit partner) + obs c base
            (∀ c : Fin q → W,
              (∑ bits : Fin q → Bool, delta (fun j => c j + if bits j then unit (pulseSite j) else 0)) = 1) ∧
            2^(k*q) ≤ 2^q * (Finset.univ.filter (fun c : Fin q → W => delta c ≠ 0)).card :=
  PEqualNP.Outside.L_meta_25761_aux.main_proof
