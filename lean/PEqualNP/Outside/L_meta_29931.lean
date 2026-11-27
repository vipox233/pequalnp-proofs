import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Matrix.Mul

namespace PEqualNP.Outside.L_meta_29931

def ix {k : Nat} (hk : 0 < k) (s : Nat) : Fin k :=
  ⟨s % k, Nat.mod_lt s hk⟩

def rot {k : Nat} (hk : 0 < k) (s : Nat) (v : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  v (ix hk (j.val + k - s % k))

def start (b : Bool) : Nat :=
  if b then 3 else 1

def feed (b : Bool) (t : Nat) : Nat :=
  if b then 3 * (t + 1) + 1 else 2 * t

def mix {k : Nat} (hk : 0 < k) (b : Bool) (v : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  let d := if b then 2 else 1
  v j + v (ix hk (j.val + d)) + v (ix hk (j.val + k - d % k))

def pair {k r : Nat}
    (v z : (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2)) : ZMod 2 :=
  dotProduct v.1 z.1 +
    ∑ s : Fin (r + 1), (dotProduct (v.2 false s) (z.2 false s) + dotProduct (v.2 true s) (z.2 true s))

def form {k r : Nat} (hk : 0 < k) :
    (Fin k ⊕ (Bool × Fin r × Fin k)) → Fin 3 →
      ((Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2)) → ZMod 2 :=
  Sum.elim (fun j _ z => z.1 j) (fun g e z =>
    let b := g.1
    let t := g.2.1
    let j := g.2.2
    let y := mix hk b (z.2 b t.castSucc)
    if e.val = 0 then y (ix hk (j.val + 1)) else if e.val = 1 then y (ix hk (j.val + 2))
    else z.2 b t.succ j + y j + rot hk (feed b t.val) z.1 j)

def DSub {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2)) : Type :=
  {z : (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2) //
    (∀ b, z.2 b 0 = rot hk (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}

def spanD {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (p : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool) :
    Submodule (ZMod 2) (DSub hk obs → ZMod 2) :=
  Submodule.span (ZMod 2)
    {f : DSub hk obs → ZMod 2 |
      ∃ (j : Fin k ⊕ (Bool × Fin r × Fin k)) (e : Fin 3),
        p j = true ∧ f = fun z : DSub hk obs => form hk j e z.val}

noncomputable def width {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (cut : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool) : Nat :=
  Module.finrank (ZMod 2)
    ((spanD hk obs cut ⊓ spanD hk obs (fun j => !(cut j))) :
      Submodule (ZMod 2) (DSub hk obs → ZMod 2))

def survive (k : Nat) (b : Bool) (steps : Nat) : Nat :=
  if 3 ∣ k then k - 2 * min ((if b then 2 else 1) * steps) (2 ^ (k.factorization 2)) else k

lemma width_not {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (cut : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool) :
    width hk obs (fun j => !(cut j)) = width hk obs cut := by
  unfold width
  have hnn : (fun j => !!(cut j)) = cut := funext fun j => Bool.not_not (cut j)
  rw [hnn, inf_comm]

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  revert x; decide

lemma zmod2_eq_iff_add_eq_zero (x y : ZMod 2) : x = y ↔ x + y = 0 := by
  revert x y; decide

lemma zmod2_add_cancel_right (x y : ZMod 2) : x + y + y = x := by
  revert x y; decide

lemma zmod2_add_cancel_left (x y : ZMod 2) : x + (x + y) = y := by
  revert x y; decide

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  revert x hx; decide

lemma zmod2_ne_cases {a c : ZMod 2} (h : a ≠ c) : (a = 1 ∧ c = 0) ∨ (a = 0 ∧ c = 1) := by
  revert a c h; decide

lemma zmod2_mix_sq (a b c d e : ZMod 2) :
    (a + b + c) + (b + d + a) + (c + a + e) = a + d + e := by
  calc (a + b + c) + (b + d + a) + (c + a + e)
      = (a + a) + (b + b) + (c + c) + (a + d + e) := by ac_rfl
    _ = a + d + e := by simp [zmod2_add_self]

lemma zmod2_natCast_of_odd {m : Nat} (hm : m % 2 = 1) : (m : ZMod 2) = 1 := by
  have h := (Nat.div_add_mod m 2).symm
  rw [hm] at h
  calc (m : ZMod 2) = ((2 * (m / 2) + 1 : Nat) : ZMod 2) := by conv_lhs => rw [h]
    _ = ((2 : Nat) : ZMod 2) * ((m / 2 : Nat) : ZMod 2) + 1 := by push_cast; rfl
    _ = 1 := by
      have h2 : ((2 : Nat) : ZMod 2) = 0 := by decide
      rw [h2, zero_mul, zero_add]

lemma add_mod_eq_self_iff {k a b : Nat} (ha : a < k) (hb : b < k) :
    (a + b) % k = a ↔ b = 0 := by
  constructor
  · intro h
    by_cases hab : a + b < k
    · rw [Nat.mod_eq_of_lt hab] at h; omega
    · have hlt : a + b - k < k := by omega
      have hmod : (a + b) % k = a + b - k := by
        have h1 : a + b = (a + b - k) + k * 1 := by omega
        conv_lhs => rw [h1]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
      rw [hmod] at h; omega
  · rintro rfl; rw [Nat.add_zero, Nat.mod_eq_of_lt ha]

lemma ix_of_fin {k : Nat} (hk : 0 < k) (j : Fin k) : ix hk j.val = j :=
  Fin.ext (Nat.mod_eq_of_lt j.isLt)

lemma ix_add_left {k : Nat} (hk : 0 < k) (a b : Nat) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) :=
  Fin.ext (by simp [ix, Nat.add_mod])

lemma ix_sub_left {k : Nat} (hk : 0 < k) (a d : Nat) :
    ix hk ((ix hk a).val + k - d % k) = ix hk (a + k - d % k) := by
  apply Fin.ext
  have hd : d % k ≤ k := le_of_lt (Nat.mod_lt d hk)
  simp only [ix]
  rw [Nat.add_sub_assoc hd, Nat.add_sub_assoc hd, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_sub_cancel {k : Nat} (hk : 0 < k) (j : Fin k) (d : Nat) :
    ix hk ((ix hk (j.val + d)).val + k - d % k) = j := by
  rw [ix_sub_left]
  apply Fin.ext
  simp only [ix]
  have hd : d = k * (d / k) + d % k := (Nat.div_add_mod d k).symm
  have hmul : k * (d / k + 1) = k * (d / k) + k := by rw [Nat.mul_add, Nat.mul_one]
  have h1 : j.val + d + k - d % k = j.val + k * (d / k + 1) := by omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]

lemma ix_sub_add_cancel {k : Nat} (hk : 0 < k) (j : Fin k) (d : Nat) :
    ix hk ((ix hk (j.val + k - d % k)).val + d) = j := by
  rw [ix_add_left]
  apply Fin.ext
  simp only [ix]
  have hd : d = k * (d / k) + d % k := (Nat.div_add_mod d k).symm
  have hlt : d % k < k := Nat.mod_lt d hk
  have hmul : k * (d / k + 1) = k * (d / k) + k := by rw [Nat.mul_add, Nat.mul_one]
  have h1 : j.val + k - d % k + d = j.val + k * (d / k + 1) := by omega
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]

lemma ix_sub_sub {k : Nat} (hk : 0 < k) (j : Fin k) (s : Nat) :
    ix hk ((ix hk (j.val + k - s % k)).val + k - s % k) = ix hk (j.val + k - (2 * s) % k) := by
  rw [ix_sub_left]
  apply Fin.ext
  simp only [ix]
  have hs : s % k < k := Nat.mod_lt s hk
  have h2s : (2 * s) % k = (2 * (s % k)) % k := by simp [Nat.mul_mod]
  rw [h2s]
  by_cases h : 2 * (s % k) < k
  · rw [Nat.mod_eq_of_lt h]
    have h1 : j.val + k - s % k + k - s % k = (j.val + k - 2 * (s % k)) + k * 1 := by omega
    rw [h1, Nat.add_mul_mod_self_left]
  · have hlt2 : 2 * (s % k) - k < k := by omega
    have hmod : (2 * (s % k)) % k = 2 * (s % k) - k := by
      have hsub : 2 * (s % k) = (2 * (s % k) - k) + k * 1 := by omega
      conv_lhs => rw [hsub]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
    rw [hmod]
    have h1 : j.val + k - s % k + k - s % k = j.val + k - (2 * (s % k) - k) := by omega
    rw [h1]

def mixStep {k : Nat} (hk : 0 < k) (s : Nat) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun v j := v j + v (ix hk (j.val + s)) + v (ix hk (j.val + k - s % k))
  map_add' u v := funext fun j => by
    simp only [Pi.add_apply]
    ac_rfl
  map_smul' c v := funext fun j => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add]

def mixLin {k : Nat} (hk : 0 < k) (b : Bool) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  mixStep hk (if b then 2 else 1)

lemma mixStep_comp_self {k : Nat} (hk : 0 < k) (s : Nat) :
    (mixStep hk s).comp (mixStep hk s) = mixStep hk (2 * s) := by
  ext v j
  simp only [LinearMap.comp_apply, mixStep, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ix_add_left, ix_add_sub_cancel, ix_sub_add_cancel, ix_sub_sub]
  have h2 : j.val + s + s = j.val + 2 * s := by omega
  rw [h2]
  exact zmod2_mix_sq _ _ _ _ _

lemma mixLin_pow_eq {k : Nat} (hk : 0 < k) (b : Bool) (n : Nat) :
    (mixLin hk b) ^ n = (mixStep hk 1) ^ ((if b then 2 else 1) * n) := by
  cases b
  · simp [mixLin]
  · change (mixStep hk 2) ^ n = (mixStep hk 1) ^ (2 * n)
    have h2 : mixStep hk 2 = (mixStep hk 1) ^ 2 := by
      rw [sq]
      exact (mixStep_comp_self hk 1).symm
    rw [h2, ← pow_mul]

lemma mixStep_one_pow_two_pow {k : Nat} (hk : 0 < k) (t : Nat) :
    (mixStep hk 1) ^ (2 ^ t) = mixStep hk (2 ^ t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by omega
    rw [h1, pow_add, ih]
    change (mixStep hk (2 ^ t)).comp (mixStep hk (2 ^ t)) = mixStep hk (2 ^ t + 2 ^ t)
    rw [mixStep_comp_self]
    have h2 : 2 * 2 ^ t = 2 ^ t + 2 ^ t := by omega
    rw [h2]

lemma ker_mixStep_one_rec {k : Nat} (hk : 0 < k) {v : Fin k → ZMod 2}
    (hv : mixStep hk 1 v = 0) (j : Nat) :
    v (ix hk (j + 2)) = v (ix hk j) + v (ix hk (j + 1)) := by
  have h0 := congrFun hv (ix hk (j + 1))
  simp only [mixStep, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h0
  rw [ix_add_left, ix_sub_left] at h0
  have hsub : ix hk (j + 1 + k - 1 % k) = ix hk j := by
    apply Fin.ext
    simp only [ix]
    by_cases hk1 : k = 1
    · subst hk1; simp
    · have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m]
      have ha : j + 1 + k - 1 = j + k * 1 := by omega
      rw [ha, Nat.add_mul_mod_self_left]
  rw [hsub] at h0
  have h1 : j + 1 + 1 = j + 2 := by omega
  rw [h1] at h0
  apply (zmod2_eq_iff_add_eq_zero _ _).mpr
  calc v (ix hk (j + 2)) + (v (ix hk j) + v (ix hk (j + 1)))
      = v (ix hk (j + 1)) + v (ix hk (j + 2)) + v (ix hk j) := by ac_rfl
    _ = 0 := h0

lemma ker_mixStep_one_period3 {k : Nat} (hk : 0 < k) {v : Fin k → ZMod 2}
    (hv : mixStep hk 1 v = 0) (j : Nat) :
    v (ix hk (j + 3)) = v (ix hk j) := by
  have h1 := ker_mixStep_one_rec hk hv (j + 1)
  have h2 := ker_mixStep_one_rec hk hv j
  have h3 : j + 1 + 2 = j + 3 := by omega
  have h4 : j + 1 + 1 = j + 2 := by omega
  rw [h3, h4] at h1
  rw [h1, h2]
  calc v (ix hk (j + 1)) + (v (ix hk j) + v (ix hk (j + 1)))
      = (v (ix hk (j + 1)) + v (ix hk (j + 1))) + v (ix hk j) := by ac_rfl
    _ = v (ix hk j) := by rw [zmod2_add_self, zero_add]

lemma ker_mixStep_one_mod3 {k : Nat} (hk : 0 < k) {v : Fin k → ZMod 2}
    (hv : mixStep hk 1 v = 0) (j : Nat) :
    v (ix hk j) = v (ix hk (j % 3)) := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < 3
    · rw [Nat.mod_eq_of_lt hj]
    · have hj3 : j - 3 < j := by omega
      have hstep : j - 3 + 3 = j := by omega
      have hmod : (j - 3) % 3 = j % 3 := by omega
      conv_lhs => rw [← hstep]
      rw [ker_mixStep_one_period3 hk hv, ih (j - 3) hj3, hmod]

lemma ker_mixStep_one_eq_zero_of_zero01 {k : Nat} (hk : 0 < k) {v : Fin k → ZMod 2}
    (hv : mixStep hk 1 v = 0) (h0 : v (ix hk 0) = 0) (h1 : v (ix hk 1) = 0) : v = 0 := by
  have h2 : v (ix hk 2) = 0 := by
    have hr := ker_mixStep_one_rec hk hv 0
    simpa [h0, h1] using hr
  funext j
  rw [← ix_of_fin hk j, ker_mixStep_one_mod3 hk hv j.val]
  have hm : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 := by omega
  rcases hm with h | h | h <;> rw [h]
  · exact h0
  · exact h1
  · exact h2

lemma ker_mixStep_one_eq_bot {k : Nat} (hk : 0 < k) (h3 : ¬ 3 ∣ k) :
    LinearMap.ker (mixStep hk 1) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv0 : mixStep hk 1 v = 0 := hv
  have hk0 : ix hk k = ix hk 0 := Fin.ext (by simp [ix])
  have hk1 : ix hk (k + 1) = ix hk 1 := Fin.ext (by simp [ix])
  have ha : v (ix hk 0) = v (ix hk (k % 3)) := by
    rw [← hk0, ker_mixStep_one_mod3 hk hv0 k]
  have hb : v (ix hk 1) = v (ix hk ((k + 1) % 3)) := by
    rw [← hk1, ker_mixStep_one_mod3 hk hv0 (k + 1)]
  have h2 : v (ix hk 2) = v (ix hk 0) + v (ix hk 1) := by
    simpa using ker_mixStep_one_rec hk hv0 0
  have hrem : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hrem with hr | hr
  · have hr1 : (k + 1) % 3 = 2 := by omega
    rw [hr] at ha
    rw [hr1, h2] at hb
    rw [← ha, zmod2_add_self] at hb
    have h1 : v (ix hk 1) = 0 := by rw [← ha, hb]
    exact ker_mixStep_one_eq_zero_of_zero01 hk hv0 hb h1
  · have hr1 : (k + 1) % 3 = 0 := by omega
    rw [hr, h2] at ha
    rw [hr1] at hb
    have h1 : v (ix hk 1) = 0 := by
      have h' : v (ix hk 0) + v (ix hk 1) = v (ix hk 0) := ha.symm
      calc v (ix hk 1) = v (ix hk 0) + (v (ix hk 0) + v (ix hk 1)) := (zmod2_add_cancel_left _ _).symm
        _ = v (ix hk 0) + v (ix hk 0) := by rw [h']
        _ = 0 := zmod2_add_self _
    have h0 : v (ix hk 0) = 0 := by rw [← hb, h1]
    exact ker_mixStep_one_eq_zero_of_zero01 hk hv0 h0 h1

lemma ker_pow_eq_bot_of_ker_eq_bot {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {f : Module.End (ZMod 2) V} (hf : LinearMap.ker f = ⊥) (n : Nat) :
    LinearMap.ker (f ^ n) = ⊥ := by
  induction n with
  | zero =>
    rw [pow_zero, Submodule.eq_bot_iff]
    intro v hv
    exact hv
  | succ n ih =>
    rw [pow_succ', Submodule.eq_bot_iff]
    intro v hv
    have h1 : f ((f ^ n) v) = 0 := hv
    have h2 : (f ^ n) v ∈ LinearMap.ker f := h1
    rw [hf, Submodule.mem_bot] at h2
    have h3 : v ∈ LinearMap.ker (f ^ n) := h2
    rw [ih, Submodule.mem_bot] at h3
    exact h3

lemma finrank_dual_eq {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]
    [Module.Finite K M] :
    Module.finrank K (M →ₗ[K] K) = Module.finrank K M := by
  let b := Module.finBasis K M
  let e : (M →ₗ[K] K) ≃ₗ[K] (Fin (Module.finrank K M) → K) :=
    { toFun := fun φ i => φ (b i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun c => b.constr K c
      left_inv := fun φ => b.ext fun i => by simp
      right_inv := fun c => funext fun i => by simp }
  rw [LinearEquiv.finrank_eq e, Module.finrank_pi, Fintype.card_fin]

lemma finrank_ker_comp_le {K : Type*} [Field K] {V W U : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    [AddCommGroup U] [Module K U]
    (f : W →ₗ[K] U) (g : V →ₗ[K] W) :
    Module.finrank K (LinearMap.ker (f.comp g)) ≤
      Module.finrank K (LinearMap.ker f) + Module.finrank K (LinearMap.ker g) := by
  let g' : LinearMap.ker (f.comp g) →ₗ[K] LinearMap.ker f :=
    { toFun := fun v => ⟨g v.1, v.2⟩
      map_add' := fun u v => Subtype.ext (g.map_add u.1 v.1)
      map_smul' := fun c v => Subtype.ext (g.map_smul c v.1) }
  have hrn := LinearMap.finrank_range_add_finrank_ker g'
  have hr : Module.finrank K (LinearMap.range g') ≤ Module.finrank K (LinearMap.ker f) :=
    Submodule.finrank_le _
  let j : LinearMap.ker g' →ₗ[K] LinearMap.ker g :=
    { toFun := fun v => ⟨v.1.1, by
        have h : g' v.1 = 0 := v.2
        exact congrArg Subtype.val h⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hab
    have hval : a.1.1 = b.1.1 := congrArg (Subtype.val : LinearMap.ker g → V) hab
    exact Subtype.ext (Subtype.ext hval)
  have hk : Module.finrank K (LinearMap.ker g') ≤ Module.finrank K (LinearMap.ker g) :=
    LinearMap.finrank_le_finrank_of_injective hj
  omega

lemma finrank_ker_mixStep_one_le {k : Nat} (hk : 0 < k) :
    Module.finrank (ZMod 2) (LinearMap.ker (mixStep hk 1)) ≤ 2 := by
  let ev : LinearMap.ker (mixStep hk 1) →ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
    { toFun := fun v i => v.1 (ix hk i.val)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective ev := by
    intro u v huv
    apply Subtype.ext
    have hdiff : mixStep hk 1 (u.1 - v.1) = 0 := by
      rw [map_sub]
      have hu : mixStep hk 1 u.1 = 0 := u.2
      have hv : mixStep hk 1 v.1 = 0 := v.2
      rw [hu, hv, sub_self]
    have h0 : (u.1 - v.1) (ix hk 0) = 0 := by
      have hc : u.1 (ix hk 0) = v.1 (ix hk 0) := congrFun huv ⟨0, by omega⟩
      exact sub_eq_zero.mpr hc
    have h1 : (u.1 - v.1) (ix hk 1) = 0 := by
      have hc : u.1 (ix hk 1) = v.1 (ix hk 1) := congrFun huv ⟨1, by omega⟩
      exact sub_eq_zero.mpr hc
    exact sub_eq_zero.mp (ker_mixStep_one_eq_zero_of_zero01 hk hdiff h0 h1)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi] using hle

lemma finrank_ker_mixStep_one_pow_le {k : Nat} (hk : 0 < k) (n : Nat) :
    Module.finrank (ZMod 2) (LinearMap.ker ((mixStep hk 1) ^ n)) ≤ 2 * n := by
  induction n with
  | zero =>
    rw [pow_zero]
    have hk0 : LinearMap.ker (1 : Module.End (ZMod 2) (Fin k → ZMod 2)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro v hv; exact hv
    rw [hk0, finrank_bot]
  | succ n ih =>
    rw [pow_succ']
    have h1 := finrank_ker_comp_le (mixStep hk 1) ((mixStep hk 1) ^ n)
    have h2 := finrank_ker_mixStep_one_le hk
    change Module.finrank (ZMod 2) (LinearMap.ker ((mixStep hk 1).comp ((mixStep hk 1) ^ n))) ≤ _
    omega

lemma not_three_dvd_two_pow (t : Nat) : ¬ 3 ∣ 2 ^ t := by
  induction t with
  | zero => omega
  | succ t ih =>
    intro h
    have h2 : 2 ^ (t + 1) = 2 * 2 ^ t := by omega
    rw [h2] at h
    have hcop : Nat.Coprime 3 2 := by decide
    exact ih (hcop.dvd_of_dvd_mul_left h)

lemma ker_mixStep_one_stab {k : Nat} (hk : 0 < k) (h3 : 3 ∣ k) :
    LinearMap.ker ((mixStep hk 1) ^ (2 ^ (k.factorization 2) + 1)) ≤
      LinearMap.ker ((mixStep hk 1) ^ (2 ^ (k.factorization 2))) := by
  set t := k.factorization 2
  set p := 2 ^ t
  set q := k / p
  have hp_pos : 0 < p := Nat.two_pow_pos t
  have hpq : p * q = k := Nat.ordProj_mul_ordCompl_eq_self k 2
  have hqp : q * p = k := by rw [Nat.mul_comm]; exact hpq
  have hq_not2 : ¬ 2 ∣ q := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have hq_odd : q % 2 = 1 := by omega
  have hp_not3 : ¬ 3 ∣ p := not_three_dvd_two_pow t
  have h3_cop : Nat.Coprime 3 p := (Nat.prime_three.coprime_iff_not_dvd).mpr hp_not3
  have h3_q : 3 ∣ q := h3_cop.dvd_of_dvd_mul_left (by rw [hpq]; exact h3)
  set m := q / 3
  have hqm : 3 * m = q := by omega
  have hm_odd : m % 2 = 1 := by omega
  have hq_ge3 : 3 ≤ q := by omega
  have hq_pos : 0 < q := by omega
  have hp_lt_k : p < k := by
    have : p * 1 < p * q := Nat.mul_lt_mul_of_pos_left (by omega) hp_pos
    omega
  intro u hu
  change ((mixStep hk 1) ^ p) u = 0
  set w := ((mixStep hk 1) ^ p) u
  have hMw : mixStep hk 1 w = 0 := by
    change ((mixStep hk 1) ^ (p + 1)) u = 0 at hu
    rw [pow_succ'] at hu
    exact hu
  have hw_eq : w = mixStep hk p u := by
    have hpow := mixStep_one_pow_two_pow hk t
    exact congrFun (congrArg DFunLike.coe hpow) u
  have hsum_zero : ∀ χ : Fin q → ZMod 2,
      (∀ c : Fin q, χ c + χ (ix hq_pos (c.val + 1)) + χ (ix hq_pos (c.val + q - 1)) = 0) →
      ∑ c : Fin q, χ c * w (ix hk (c.val * p)) = 0 := by
    intro χ hχ
    have hstep : ∀ c : Fin q,
        w (ix hk (c.val * p)) =
          u (ix hk (c.val * p)) +
          u (ix hk ((ix hq_pos (c.val + 1)).val * p)) +
          u (ix hk ((ix hq_pos (c.val + q - 1)).val * p)) := by
      intro c
      rw [hw_eq]
      simp only [mixStep, LinearMap.coe_mk, AddHom.coe_mk]
      have hc_lt : c.val * p < k := by
        have hlt : c.val * p < q * p := Nat.mul_lt_mul_of_pos_right c.isLt hp_pos
        omega
      have hc_val : (ix hk (c.val * p)).val = c.val * p := Nat.mod_eq_of_lt hc_lt
      have h1 : ix hk ((ix hk (c.val * p)).val + p) = ix hk ((ix hq_pos (c.val + 1)).val * p) := by
        rw [hc_val]
        apply Fin.ext
        simp only [ix]
        have hd : c.val + 1 = q * ((c.val + 1) / q) + (c.val + 1) % q :=
          (Nat.div_add_mod (c.val + 1) q).symm
        have heq : c.val * p + p = (c.val + 1) % q * p + k * ((c.val + 1) / q) := by
          have hmul : (c.val + 1) * p = (q * ((c.val + 1) / q) + (c.val + 1) % q) * p := by rw [← hd]
          calc c.val * p + p = (c.val + 1) * p := by rw [Nat.add_mul, Nat.one_mul]
            _ = q * ((c.val + 1) / q) * p + (c.val + 1) % q * p := by rw [hmul, Nat.add_mul]
            _ = (c.val + 1) % q * p + (q * p) * ((c.val + 1) / q) := by ac_rfl
            _ = (c.val + 1) % q * p + k * ((c.val + 1) / q) := by rw [hqp]
        rw [heq, Nat.add_mul_mod_self_left]
      have h2 : ix hk ((ix hk (c.val * p)).val + k - p % k) =
          ix hk ((ix hq_pos (c.val + q - 1)).val * p) := by
        rw [hc_val, Nat.mod_eq_of_lt hp_lt_k]
        apply Fin.ext
        simp only [ix]
        have hd : c.val + q - 1 = q * ((c.val + q - 1) / q) + (c.val + q - 1) % q :=
          (Nat.div_add_mod (c.val + q - 1) q).symm
        have hsub : c.val * p + k - p = (c.val + q - 1) * p := by
          have h1' : (c.val + q - 1) * p + p = (c.val + q) * p := by
            have hadd : c.val + q - 1 + 1 = c.val + q := by omega
            calc (c.val + q - 1) * p + p = (c.val + q - 1 + 1) * p := by rw [Nat.add_mul, Nat.one_mul]
              _ = (c.val + q) * p := by rw [hadd]
          have h2' : (c.val + q) * p = c.val * p + k := by rw [Nat.add_mul, hqp]
          omega
        have heq : (c.val + q - 1) * p = (c.val + q - 1) % q * p + k * ((c.val + q - 1) / q) := by
          calc (c.val + q - 1) * p
              = (q * ((c.val + q - 1) / q) + (c.val + q - 1) % q) * p := by rw [← hd]
            _ = q * ((c.val + q - 1) / q) * p + (c.val + q - 1) % q * p := by rw [Nat.add_mul]
            _ = (c.val + q - 1) % q * p + (q * p) * ((c.val + q - 1) / q) := by ac_rfl
            _ = (c.val + q - 1) % q * p + k * ((c.val + q - 1) / q) := by rw [hqp]
        rw [hsub, heq, Nat.add_mul_mod_self_left]
      rw [h1, h2]
    let nextQ : Fin q ≃ Fin q :=
      { toFun := fun c => ix hq_pos (c.val + 1)
        invFun := fun c => ix hq_pos (c.val + q - 1)
        left_inv := fun c => by
          have h := ix_add_sub_cancel hq_pos c 1
          rw [Nat.mod_eq_of_lt (by omega : 1 < q)] at h
          exact h
        right_inv := fun c => by
          have h := ix_sub_add_cancel hq_pos c 1
          rw [Nat.mod_eq_of_lt (by omega : 1 < q)] at h
          exact h }
    have hsplit : ∑ c : Fin q, χ c * w (ix hk (c.val * p)) =
        (∑ c : Fin q, χ c * u (ix hk (c.val * p))) +
        (∑ c : Fin q, χ c * u (ix hk ((nextQ c).val * p))) +
        (∑ c : Fin q, χ c * u (ix hk ((nextQ.symm c).val * p))) := by
      simp_rw [hstep, mul_add, Finset.sum_add_distrib]
      rfl
    rw [hsplit]
    have hs1 : ∑ c : Fin q, χ c * u (ix hk ((nextQ c).val * p)) =
        ∑ c : Fin q, χ (nextQ.symm c) * u (ix hk (c.val * p)) :=
      Fintype.sum_equiv nextQ _ _ (fun c => by simp)
    have hs2 : ∑ c : Fin q, χ c * u (ix hk ((nextQ.symm c).val * p)) =
        ∑ c : Fin q, χ (nextQ c) * u (ix hk (c.val * p)) :=
      Fintype.sum_equiv nextQ.symm _ _ (fun c => by simp)
    rw [hs1, hs2, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro c _
    have hcomb : χ c * u (ix hk (c.val * p)) +
        χ (nextQ.symm c) * u (ix hk (c.val * p)) +
        χ (nextQ c) * u (ix hk (c.val * p)) =
        (χ c + χ (ix hq_pos (c.val + 1)) + χ (ix hq_pos (c.val + q - 1))) * u (ix hk (c.val * p)) := by
      rw [← add_mul, ← add_mul]
      congr 1
      change χ c + χ (ix hq_pos (c.val + q - 1)) + χ (ix hq_pos (c.val + 1)) =
        χ c + χ (ix hq_pos (c.val + 1)) + χ (ix hq_pos (c.val + q - 1))
      ac_rfl
    rw [hcomb, hχ c, zero_mul]
  have hmod_next : ∀ c : Fin q, (ix hq_pos (c.val + 1)).val % 3 = (c.val + 1) % 3 := by
    intro c
    simp only [ix]
    have hd : c.val + 1 = (c.val + 1) % q + 3 * (m * ((c.val + 1) / q)) := by
      have h0 := (Nat.div_add_mod (c.val + 1) q).symm
      calc c.val + 1 = q * ((c.val + 1) / q) + (c.val + 1) % q := h0
        _ = (3 * m) * ((c.val + 1) / q) + (c.val + 1) % q := by rw [hqm]
        _ = (c.val + 1) % q + 3 * (m * ((c.val + 1) / q)) := by ac_rfl
    conv_rhs => rw [hd]
    rw [Nat.add_mul_mod_self_left]
  have hmod_prev : ∀ c : Fin q, (ix hq_pos (c.val + q - 1)).val % 3 = (c.val + 2) % 3 := by
    intro c
    simp only [ix]
    have hd : c.val + q - 1 = (c.val + q - 1) % q + 3 * (m * ((c.val + q - 1) / q)) := by
      have h0 := (Nat.div_add_mod (c.val + q - 1) q).symm
      calc c.val + q - 1 = q * ((c.val + q - 1) / q) + (c.val + q - 1) % q := h0
        _ = (3 * m) * ((c.val + q - 1) / q) + (c.val + q - 1) % q := by rw [hqm]
        _ = (c.val + q - 1) % q + 3 * (m * ((c.val + q - 1) / q)) := by ac_rfl
    have hq3 : (c.val + q - 1) % 3 = (c.val + 2) % 3 := by omega
    rw [← hq3]
    conv_rhs => rw [hd]
    rw [Nat.add_mul_mod_self_left]
  let chi1 : Fin q → ZMod 2 := fun c => if c.val % 3 = 1 then 0 else 1
  let chi2 : Fin q → ZMod 2 := fun c => if c.val % 3 = 0 then 0 else 1
  have hchi1 : ∑ c : Fin q, chi1 c * w (ix hk (c.val * p)) = 0 := by
    apply hsum_zero chi1
    intro c
    simp only [chi1, hmod_next, hmod_prev]
    have hcm : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2 := by omega
    rcases hcm with h | h | h
    · have h1 : (c.val + 1) % 3 = 1 := by omega
      have h2 : (c.val + 2) % 3 = 2 := by omega
      rw [h, h1, h2]; decide
    · have h1 : (c.val + 1) % 3 = 2 := by omega
      have h2 : (c.val + 2) % 3 = 0 := by omega
      rw [h, h1, h2]; decide
    · have h1 : (c.val + 1) % 3 = 0 := by omega
      have h2 : (c.val + 2) % 3 = 1 := by omega
      rw [h, h1, h2]; decide
  have hchi2 : ∑ c : Fin q, chi2 c * w (ix hk (c.val * p)) = 0 := by
    apply hsum_zero chi2
    intro c
    simp only [chi2, hmod_next, hmod_prev]
    have hcm : c.val % 3 = 0 ∨ c.val % 3 = 1 ∨ c.val % 3 = 2 := by omega
    rcases hcm with h | h | h
    · have h1 : (c.val + 1) % 3 = 1 := by omega
      have h2 : (c.val + 2) % 3 = 2 := by omega
      rw [h, h1, h2]; decide
    · have h1 : (c.val + 1) % 3 = 2 := by omega
      have h2 : (c.val + 2) % 3 = 0 := by omega
      rw [h, h1, h2]; decide
    · have h1 : (c.val + 1) % 3 = 0 := by omega
      have h2 : (c.val + 2) % 3 = 1 := by omega
      rw [h, h1, h2]; decide
  let eqv : Fin m × Fin 3 ≃ Fin q :=
    { toFun := fun mr => ⟨3 * mr.1.val + mr.2.val, by omega⟩
      invFun := fun c => (⟨c.val / 3, by omega⟩, ⟨c.val % 3, Nat.mod_lt _ (by omega)⟩)
      left_inv := fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => by
        ext <;> simp <;> omega
      right_inv := fun ⟨c, hc⟩ => by
        ext; simp; omega }
  have hw2p : w (ix hk (2 * p)) = w (ix hk 0) + w (ix hk p) := by
    have hrec := ker_mixStep_one_rec hk hMw 0
    simp only [Nat.zero_add] at hrec
    have hp_rem : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rw [ker_mixStep_one_mod3 hk hMw (2 * p), ker_mixStep_one_mod3 hk hMw p]
    rcases hp_rem with hpr | hpr
    · have h2r : (2 * p) % 3 = 2 := by omega
      rw [hpr, h2r]; exact hrec
    · have h2r : (2 * p) % 3 = 1 := by omega
      rw [hpr, h2r, hrec]
      exact (zmod2_add_cancel_left _ _).symm
  have hw_mr : ∀ (a : Fin m) (b : Fin 3),
      w (ix hk ((eqv (a, b)).val * p)) = w (ix hk (b.val * p)) := by
    intro a b
    rw [ker_mixStep_one_mod3 hk hMw, ker_mixStep_one_mod3 hk hMw (b.val * p)]
    congr 2
    change (3 * a.val + b.val) * p % 3 = b.val * p % 3
    have h1 : (3 * a.val + b.val) * p = b.val * p + 3 * (a.val * p) := by
      rw [Nat.add_mul]; ac_rfl
    rw [h1, Nat.add_mul_mod_self_left]
  have hsum_eval : ∀ (χ : Fin q → ZMod 2) (c0 c1 c2 : ZMod 2),
      (∀ (a : Fin m), χ (eqv (a, 0)) = c0 ∧ χ (eqv (a, 1)) = c1 ∧ χ (eqv (a, 2)) = c2) →
      ∑ c : Fin q, χ c * w (ix hk (c.val * p)) =
        c0 * w (ix hk 0) + c1 * w (ix hk p) + c2 * w (ix hk (2 * p)) := by
    intro χ c0 c1 c2 hχv
    rw [← Fintype.sum_equiv eqv (fun mr => χ (eqv mr) * w (ix hk ((eqv mr).val * p)))
        (fun c => χ c * w (ix hk (c.val * p))) (fun _ => rfl)]
    rw [Fintype.sum_prod_type]
    have hinner : ∀ a : Fin m,
        ∑ b : Fin 3, χ (eqv (a, b)) * w (ix hk ((eqv (a, b)).val * p)) =
          c0 * w (ix hk 0) + c1 * w (ix hk p) + c2 * w (ix hk (2 * p)) := by
      intro a
      rw [Fin.sum_univ_three]
      rcases hχv a with ⟨h0, h1, h2⟩
      rw [hw_mr a 0, hw_mr a 1, hw_mr a 2, h0, h1, h2]
      simp
    simp_rw [hinner]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      zmod2_natCast_of_odd hm_odd, one_mul]
  have he1 := hsum_eval chi1 1 0 1 (fun a => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [chi1, eqv, Fin.val_zero]
      have h0 : (3 * a.val + 0) % 3 = 0 := by omega
      simp [h0]
    · simp only [chi1, eqv, Fin.val_one]
      have h1 : (3 * a.val + 1) % 3 = 1 := by omega
      simp [h1]
    · simp only [chi1, eqv, Fin.val_two]
      have h2 : (3 * a.val + 2) % 3 = 2 := by omega
      simp [h2])
  have he2 := hsum_eval chi2 0 1 1 (fun a => by
    refine ⟨?_, ?_, ?_⟩
    · simp only [chi2, eqv, Fin.val_zero]
      have h0 : (3 * a.val + 0) % 3 = 0 := by omega
      simp [h0]
    · simp only [chi2, eqv, Fin.val_one]
      have h1 : (3 * a.val + 1) % 3 = 1 := by omega
      simp [h1]
    · simp only [chi2, eqv, Fin.val_two]
      have h2 : (3 * a.val + 2) % 3 = 2 := by omega
      simp [h2])
  rw [hchi1, one_mul, zero_mul, add_zero, one_mul, hw2p, zmod2_add_cancel_left] at he1
  rw [hchi2, zero_mul, one_mul, zero_add, one_mul, hw2p] at he2
  have hw0 : w (ix hk 0) = 0 := by
    have : w (ix hk p) + (w (ix hk 0) + w (ix hk p)) = w (ix hk 0) := by
      calc w (ix hk p) + (w (ix hk 0) + w (ix hk p))
          = (w (ix hk p) + w (ix hk p)) + w (ix hk 0) := by ac_rfl
        _ = w (ix hk 0) := by rw [zmod2_add_self, zero_add]
    rw [this] at he2
    exact he2.symm
  have hwp : w (ix hk p) = 0 := he1.symm
  have hw1 : w (ix hk 1) = 0 := by
    have hp_rem : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rw [ker_mixStep_one_mod3 hk hMw p] at hwp
    rcases hp_rem with hpr | hpr
    · rwa [hpr] at hwp
    · rw [hpr] at hwp
      have hrec := ker_mixStep_one_rec hk hMw 0
      simp only [hw0, zero_add] at hrec
      rw [← hrec]; exact hwp
  exact ker_mixStep_one_eq_zero_of_zero01 hk hMw hw0 hw1

lemma ker_mixStep_one_le_stab {k : Nat} (hk : 0 < k) (h3 : 3 ∣ k) (d : Nat) :
    LinearMap.ker ((mixStep hk 1) ^ (2 ^ (k.factorization 2) + d)) ≤
      LinearMap.ker ((mixStep hk 1) ^ (2 ^ (k.factorization 2))) := by
  induction d with
  | zero => exact le_refl _
  | succ d ih =>
    intro u hu
    have h1 : ((mixStep hk 1) ^ (2 ^ (k.factorization 2) + 1)) (((mixStep hk 1) ^ d) u) = 0 := by
      change (((mixStep hk 1) ^ (2 ^ (k.factorization 2) + 1) * (mixStep hk 1) ^ d) u) = 0
      rw [← pow_add]
      have heq : 2 ^ (k.factorization 2) + 1 + d = 2 ^ (k.factorization 2) + (d + 1) := by omega
      rw [heq]
      exact hu
    have h2 : ((mixStep hk 1) ^ (2 ^ (k.factorization 2))) (((mixStep hk 1) ^ d) u) = 0 :=
      ker_mixStep_one_stab hk h3 h1
    have h3' : u ∈ LinearMap.ker ((mixStep hk 1) ^ (2 ^ (k.factorization 2) + d)) := by
      change (((mixStep hk 1) ^ (2 ^ (k.factorization 2) + d)) u) = 0
      rw [pow_add]
      exact h2
    exact ih h3'

lemma survive_le_finrank_range {k : Nat} (hk : 0 < k) (b : Bool) (steps : Nat) :
    survive k b steps ≤ Module.finrank (ZMod 2) (LinearMap.range ((mixLin hk b) ^ steps)) := by
  rw [mixLin_pow_eq]
  set e := (if b then 2 else 1) * steps
  have hrn := LinearMap.finrank_range_add_finrank_ker ((mixStep hk 1) ^ e)
  have hdim : Module.finrank (ZMod 2) (Fin k → ZMod 2) = k := by
    rw [Module.finrank_pi, Fintype.card_fin]
  rw [hdim] at hrn
  unfold survive
  by_cases h3 : 3 ∣ k
  · simp only [h3, ↓reduceIte]
    change k - 2 * min e (2 ^ (k.factorization 2)) ≤ _
    have hker : Module.finrank (ZMod 2) (LinearMap.ker ((mixStep hk 1) ^ e)) ≤
        2 * min e (2 ^ (k.factorization 2)) := by
      by_cases hle : e ≤ 2 ^ (k.factorization 2)
      · rw [min_eq_left hle]
        exact finrank_ker_mixStep_one_pow_le hk e
      · rw [min_eq_right (le_of_not_ge hle)]
        have hsub : LinearMap.ker ((mixStep hk 1) ^ e) ≤
            LinearMap.ker ((mixStep hk 1) ^ (2 ^ (k.factorization 2))) := by
          have heq : e = 2 ^ (k.factorization 2) + (e - 2 ^ (k.factorization 2)) := by omega
          rw [heq]
          exact ker_mixStep_one_le_stab hk h3 _
        exact le_trans (Submodule.finrank_mono hsub)
          (finrank_ker_mixStep_one_pow_le hk (2 ^ (k.factorization 2)))
    omega
  · simp only [h3, ↓reduceIte]
    have hbot : LinearMap.ker ((mixStep hk 1) ^ e) = ⊥ :=
      ker_pow_eq_bot_of_ker_eq_bot (ker_mixStep_one_eq_bot hk h3) e
    rw [hbot, finrank_bot] at hrn
    omega

def embed {k r : Nat} (b : Bool) (w : Fin (r + 1) → Fin k → ZMod 2) :
    (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2) :=
  (0, fun b' => if b' = b then w else 0)

def seenFun {k r q : Nat}
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (b : Bool) (a m : Nat) (u : Fin q) (s : Fin (r + 1)) (x : Fin k) : ZMod 2 :=
  if a ≤ s.val ∧ s.val < a + m then (obs u).2 b s x else 0

lemma pair_embed {k r : Nat}
    (v : (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (b : Bool) (a m : Nat) (w : Fin (r + 1) → Fin k → ZMod 2)
    (hsupp : ∀ s : Fin (r + 1), ¬(a ≤ s.val ∧ s.val < a + m) → w s = 0) :
    pair v (embed b w) =
      ∑ s : Fin (r + 1), ∑ x : Fin k,
        (if a ≤ s.val ∧ s.val < a + m then v.2 b s x else 0) * w s x := by
  unfold pair embed
  simp only [dotProduct_zero, zero_add]
  apply Finset.sum_congr rfl
  intro s _
  cases b
  · simp only [↓reduceIte, Bool.true_eq_false, Pi.zero_apply, dotProduct, mul_zero,
      Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hs : a ≤ s.val ∧ s.val < a + m
    · simp [hs]
    · simp [hs, hsupp s hs]
  · simp only [Bool.false_eq_true, ↓reduceIte, Pi.zero_apply, dotProduct, mul_zero,
      Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hs : a ≤ s.val ∧ s.val < a + m
    · simp [hs]
    · simp [hs, hsupp s hs]

lemma finrank_range_le_of_dual_span
    {M Idx : Type} [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M] [Fintype Idx]
    (T : M →ₗ[ZMod 2] (Idx → ZMod 2)) :
    Module.finrank (ZMod 2) (LinearMap.range T) ≤
      Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (Set.range fun i : Idx => (LinearMap.proj i).comp T)) := by
  set WK := Submodule.span (ZMod 2) (Set.range fun i : Idx => (LinearMap.proj i).comp T)
  have _ : Module.Finite (ZMod 2) WK := Module.Finite.span_of_finite (ZMod 2) (Set.finite_range _)
  have _ : Module.Free (ZMod 2) WK := Module.Free.of_divisionRing (ZMod 2) WK
  let b := Module.finBasis (ZMod 2) WK
  let EK : M →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) WK) → ZMod 2) :=
    { toFun := fun v j => (b j).1 v
      map_add' := fun u v => funext fun j => (b j).1.map_add u v
      map_smul' := fun c v => funext fun j => (b j).1.map_smul c v }
  have hkerE_le : LinearMap.ker EK ≤ LinearMap.ker T := by
    intro v hv
    change T v = 0
    funext i
    have hi : (LinearMap.proj i).comp T ∈ WK := Submodule.subset_span ⟨i, rfl⟩
    let α : WK := ⟨(LinearMap.proj i).comp T, hi⟩
    let ev : WK →ₗ[ZMod 2] ZMod 2 :=
      { toFun := fun β => β.1 v
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have h1 : ev α = ∑ j, b.repr α j * ev (b j) := by
      conv_lhs => rw [← b.sum_repr α]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul]
    change ev α = 0
    rw [h1]
    apply Finset.sum_eq_zero
    intro j _
    have hvj : ev (b j) = 0 := congrFun hv j
    rw [hvj, mul_zero]
  have hrnT := LinearMap.finrank_range_add_finrank_ker T
  have hrnEK := LinearMap.finrank_range_add_finrank_ker EK
  have hker_le := Submodule.finrank_mono hkerE_le
  have hEK_le : Module.finrank (ZMod 2) (LinearMap.range EK) ≤ Module.finrank (ZMod 2) WK := by
    calc Module.finrank (ZMod 2) (LinearMap.range EK)
        ≤ Module.finrank (ZMod 2) (Fin (Module.finrank (ZMod 2) WK) → ZMod 2) :=
          Submodule.finrank_le _
      _ = Module.finrank (ZMod 2) WK := by rw [Module.finrank_pi, Fintype.card_fin]
  omega

lemma finrank_range_le_width_add_cost
    {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (cut : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool)
    (b : Bool) (a m : Nat) (ha : 0 < a)
    {V Idx : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    [Fintype Idx]
    (ι : V →ₗ[ZMod 2] (Fin (r + 1) → Fin k → ZMod 2))
    (hι_supp : ∀ v (s : Fin (r + 1)), ¬(a ≤ s.val ∧ s.val < a + m) → ι v s = 0)
    (T : V →ₗ[ZMod 2] (Idx → ZMod 2))
    (hforms : ∀ i : Idx, ∃ g : DSub hk obs → ZMod 2,
      g ∈ spanD hk obs cut ⊓ spanD hk obs (fun j => !(cut j)) ∧
      ∀ v (hv : (∀ b', (embed b (ι v)).2 b' 0 = rot hk (start b') (embed b (ι v)).1) ∧
          ∀ u, pair (obs u) (embed b (ι v)) = 0),
        g ⟨embed b (ι v), hv⟩ = T v i) :
    Module.finrank (ZMod 2) (LinearMap.range T) ≤
      width hk obs cut +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (seenFun obs b a m))) := by
  classical
  have _ : Finite (DSub hk obs) := Subtype.finite
  let _ : Fintype (DSub hk obs) := Fintype.ofFinite (DSub hk obs)
  set Sseen := Submodule.span (ZMod 2) (Set.range (seenFun obs b a m))
  let bS := Module.finBasis (ZMod 2) Sseen
  let Ψ : V →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) Sseen) → ZMod 2) :=
    { toFun := fun v j => ∑ s : Fin (r + 1), ∑ x : Fin k, (bS j).1 s x * ι v s x
      map_add' := fun u v => funext fun j => by
        simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => funext fun j => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        have h1 : ∀ (s : Fin (r + 1)) (x : Fin k),
            (bS j).1 s x * (c * ι v s x) = c * ((bS j).1 s x * ι v s x) :=
          fun _ _ => by ac_rfl
        simp_rw [h1, ← Finset.mul_sum] }
  set K := LinearMap.ker Ψ
  have hK_mem : ∀ v : K,
      (∀ b', (embed b (ι v.1)).2 b' 0 = rot hk (start b') (embed b (ι v.1)).1) ∧
      ∀ u, pair (obs u) (embed b (ι v.1)) = 0 := by
    intro v
    constructor
    · intro b'
      have hrot0 : rot hk (start b') (0 : Fin k → ZMod 2) = 0 := rfl
      change (if b' = b then ι v.1 else 0) 0 = rot hk (start b') 0
      rw [hrot0]
      split_ifs
      · exact hι_supp v.1 0 (by simp only [Fin.val_zero]; omega)
      · rfl
    · intro u
      rw [pair_embed (obs u) b a m (ι v.1) (hι_supp v.1)]
      have hu_mem : seenFun obs b a m u ∈ Sseen := Submodule.subset_span ⟨u, rfl⟩
      let α : Sseen := ⟨seenFun obs b a m u, hu_mem⟩
      let ev : Sseen →ₗ[ZMod 2] ZMod 2 :=
        { toFun := fun β => ∑ s : Fin (r + 1), ∑ x : Fin k, β.1 s x * ι v.1 s x
          map_add' := fun β γ => by
            simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
          map_smul' := fun c β => by
            simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc,
              ← Finset.mul_sum] }
      have h1 : ev α = ∑ j, bS.repr α j * ev (bS j) := by
        conv_lhs => rw [← bS.sum_repr α]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_smul, smul_eq_mul]
      change ev α = 0
      rw [h1]
      apply Finset.sum_eq_zero
      intro j _
      have hvj : ev (bS j) = 0 := congrFun v.2 j
      rw [hvj, mul_zero]
  let TK : K →ₗ[ZMod 2] (Idx → ZMod 2) := T.comp K.subtype
  have hstep1 : Module.finrank (ZMod 2) (LinearMap.range T) ≤
      Module.finrank (ZMod 2) (LinearMap.range TK) + Module.finrank (ZMod 2) Sseen := by
    have hrnT := LinearMap.finrank_range_add_finrank_ker T
    have hrnTK := LinearMap.finrank_range_add_finrank_ker TK
    have hrnΨ : Module.finrank (ZMod 2) (LinearMap.range Ψ) + Module.finrank (ZMod 2) K =
        Module.finrank (ZMod 2) V := LinearMap.finrank_range_add_finrank_ker Ψ
    have hΨ_le : Module.finrank (ZMod 2) (LinearMap.range Ψ) ≤ Module.finrank (ZMod 2) Sseen := by
      calc Module.finrank (ZMod 2) (LinearMap.range Ψ)
          ≤ Module.finrank (ZMod 2) (Fin (Module.finrank (ZMod 2) Sseen) → ZMod 2) :=
            Submodule.finrank_le _
        _ = Module.finrank (ZMod 2) Sseen := by rw [Module.finrank_pi, Fintype.card_fin]
    let injK : LinearMap.ker TK →ₗ[ZMod 2] LinearMap.ker T :=
      { toFun := fun v => ⟨v.1.1, v.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinjK : Function.Injective injK := fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (Subtype.val : LinearMap.ker T → V) hab))
    have hker_le : Module.finrank (ZMod 2) (LinearMap.ker TK) ≤
        Module.finrank (ZMod 2) (LinearMap.ker T) :=
      LinearMap.finrank_le_finrank_of_injective hinjK
    omega
  set Acut := spanD hk obs cut ⊓ spanD hk obs (fun j => !(cut j))
  let WK : Submodule (ZMod 2) (K →ₗ[ZMod 2] ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range fun i : Idx => (LinearMap.proj i).comp TK)
  let coeLin : (K →ₗ[ZMod 2] ZMod 2) →ₗ[ZMod 2] (K → ZMod 2) :=
    { toFun := fun φ v => φ v
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hcoe_inj : Function.Injective coeLin := fun _ _ h => LinearMap.ext (congrFun h)
  let pull : (DSub hk obs → ZMod 2) →ₗ[ZMod 2] (K → ZMod 2) :=
    { toFun := fun g v => g ⟨embed b (ι v.1), hK_mem v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hWK_map_le : WK.map coeLin ≤ Acut.map pull := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    rcases hforms i with ⟨g, hgA, hgval⟩
    exact ⟨g, hgA, funext fun v => hgval v.1 (hK_mem v)⟩
  have hWK_le_width : Module.finrank (ZMod 2) WK ≤ width hk obs cut := by
    have _ : Module.Finite (ZMod 2) WK := Module.Finite.span_of_finite (ZMod 2) (Set.finite_range _)
    calc Module.finrank (ZMod 2) WK
        = Module.finrank (ZMod 2) (WK.map coeLin) :=
          LinearEquiv.finrank_eq (Submodule.equivMapOfInjective coeLin hcoe_inj WK)
      _ ≤ Module.finrank (ZMod 2) (Acut.map pull) := Submodule.finrank_mono hWK_map_le
      _ ≤ Module.finrank (ZMod 2) Acut := Submodule.finrank_map_le pull Acut
  have hstep2 : Module.finrank (ZMod 2) (LinearMap.range TK) ≤ Module.finrank (ZMod 2) WK :=
    finrank_range_le_of_dual_span TK
  omega

lemma mix_coord_mem_spanD {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (p : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool)
    (b : Bool) (t : Fin r) (j : Fin k)
    (hp : p (Sum.inr (b, t, ix hk (j.val + k - 1 % k))) = true) :
    (fun z : DSub hk obs => mix hk b (z.val.2 b t.castSucc) j) ∈ spanD hk obs p := by
  apply Submodule.subset_span
  refine ⟨Sum.inr (b, t, ix hk (j.val + k - 1 % k)), ⟨0, by omega⟩, hp, ?_⟩
  funext z
  simp only [form, Sum.elim_inr, ↓reduceIte]
  rw [ix_sub_add_cancel hk j 1]

lemma linear_apply_eq_sum {k : Nat} (L : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (v : Fin k → ZMod 2) (j : Fin k) :
    L v j = ∑ j' : Fin k, L (Pi.single j' 1) j * v j' := by
  have hv : v = ∑ j' : Fin k, v j' • Pi.single j' (1 : ZMod 2) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j' _
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

lemma telescoping_mix {k r : Nat} (hk : 0 < k) (b : Bool)
    (z : Fin (r + 1) → Fin k → ZMod 2) (s0 δ : Nat) (hδ : 0 < δ) (hbd : s0 + δ ≤ r) :
    ∑ u : Fin δ,
      (((mixLin hk b) ^ (δ - u.val)) (z ⟨s0 + u.val + 1, by omega⟩) +
       ((mixLin hk b) ^ (δ - u.val + 1)) (z ⟨s0 + u.val, by omega⟩)) =
    mixLin hk b (z ⟨s0 + δ, by omega⟩) + ((mixLin hk b) ^ (δ + 1)) (z ⟨s0, by omega⟩) := by
  induction δ with
  | zero => omega
  | succ d ih =>
    by_cases hd : d = 0
    · subst hd
      simp
    · have hd_pos : 0 < d := by omega
      rw [Fin.sum_univ_castSucc]
      have hlast : (((mixLin hk b) ^ (d + 1 - d)) (z ⟨s0 + d + 1, by omega⟩) +
          ((mixLin hk b) ^ (d + 1 - d + 1)) (z ⟨s0 + d, by omega⟩)) =
          mixLin hk b (z ⟨s0 + (d + 1), by omega⟩) +
          ((mixLin hk b) ^ 2) (z ⟨s0 + d, by omega⟩) := by
        have h1 : d + 1 - d = 1 := by omega
        have h2 : d + 1 - d + 1 = 2 := by omega
        have h3 : s0 + d + 1 = s0 + (d + 1) := by omega
        simp only [h1, h2, h3, pow_one]
      have hpref : ∑ u : Fin d,
          (((mixLin hk b) ^ (d + 1 - u.val)) (z ⟨s0 + u.val + 1, by omega⟩) +
           ((mixLin hk b) ^ (d + 1 - u.val + 1)) (z ⟨s0 + u.val, by omega⟩)) =
          mixLin hk b (∑ u : Fin d,
            (((mixLin hk b) ^ (d - u.val)) (z ⟨s0 + u.val + 1, by omega⟩) +
             ((mixLin hk b) ^ (d - u.val + 1)) (z ⟨s0 + u.val, by omega⟩))) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro u _
        rw [map_add]
        have he1 : d + 1 - u.val = (d - u.val) + 1 := by omega
        rw [he1]
        conv_lhs => rw [pow_succ', pow_succ']
        rfl
      change (∑ u : Fin d,
          (((mixLin hk b) ^ (d + 1 - u.val)) (z ⟨s0 + u.val + 1, by omega⟩) +
           ((mixLin hk b) ^ (d + 1 - u.val + 1)) (z ⟨s0 + u.val, by omega⟩))) +
        (((mixLin hk b) ^ (d + 1 - d)) (z ⟨s0 + d + 1, by omega⟩) +
         ((mixLin hk b) ^ (d + 1 - d + 1)) (z ⟨s0 + d, by omega⟩)) = _
      rw [hpref, ih hd_pos (by omega), hlast, map_add]
      have hsq : mixLin hk b (mixLin hk b (z ⟨s0 + d, by omega⟩)) =
          ((mixLin hk b) ^ 2) (z ⟨s0 + d, by omega⟩) := by
        rw [pow_two]; rfl
      have hpow : mixLin hk b (((mixLin hk b) ^ (d + 1)) (z ⟨s0, by omega⟩)) =
          ((mixLin hk b) ^ (d + 1 + 1)) (z ⟨s0, by omega⟩) := by
        conv_rhs => rw [pow_succ']
        rfl
      rw [hsq, hpow]
      funext j
      simp only [Pi.add_apply]
      calc ((mixLin hk b) ^ 2) (z ⟨s0 + d, by omega⟩) j +
            ((mixLin hk b) ^ (d + 1 + 1)) (z ⟨s0, by omega⟩) j +
            (mixLin hk b (z ⟨s0 + (d + 1), by omega⟩) j +
              ((mixLin hk b) ^ 2) (z ⟨s0 + d, by omega⟩) j)
          = (((mixLin hk b) ^ 2) (z ⟨s0 + d, by omega⟩) j +
              ((mixLin hk b) ^ 2) (z ⟨s0 + d, by omega⟩) j) +
            (mixLin hk b (z ⟨s0 + (d + 1), by omega⟩) j +
              ((mixLin hk b) ^ (d + 1 + 1)) (z ⟨s0, by omega⟩) j) := by ac_rfl
        _ = mixLin hk b (z ⟨s0 + (d + 1), by omega⟩) j +
            ((mixLin hk b) ^ (d + 1 + 1)) (z ⟨s0, by omega⟩) j := by
              rw [zmod2_add_self, zero_add]

lemma case1_bound {k r q : Nat} (hk : 0 < k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (cut : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool)
    (b : Bool) (a m : Nat) (ha : 0 < a) (hm : 0 < m) (ham : a + m ≤ r)
    (lo hi : Fin m) (hlohi : lo.val < hi.val)
    (hlo : ∀ j : Fin k, cut (Sum.inr (b, ⟨a + lo.val, by omega⟩, j)) = true)
    (hhi : ∀ j : Fin k, cut (Sum.inr (b, ⟨a + hi.val, by omega⟩, j)) = false) :
    survive k b m ≤
      width hk obs cut +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (seenFun obs b a m))) := by
  set δ := hi.val - lo.val
  have hδ : 0 < δ := by omega
  have hbd : a + lo.val + δ ≤ r := by omega
  let coeff (e : Nat) (j j' : Fin k) : ZMod 2 := ((mixLin hk b) ^ e) (Pi.single j' 1) j
  let tu (u : Fin δ) : Fin r := ⟨a + lo.val + u.val, by omega⟩
  let partRes (p : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool) (j : Fin k)
      (z : (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2)) : ZMod 2 :=
    ∑ u : Fin δ, ∑ j' : Fin k,
      if p (Sum.inr (b, tu u, j')) = true then
        coeff (δ - u.val) j j' * form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ z
      else 0
  let partKey (p : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool) (j : Fin k)
      (z : (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2)) : ZMod 2 :=
    ∑ u : Fin δ, ∑ j' : Fin k,
      let idx := ix hk (j'.val + k - feed b (tu u).val % k)
      if p (Sum.inl idx) = true then
        coeff (δ - u.val) j j' * form hk (Sum.inl idx) ⟨0, by omega⟩ z
      else 0
  have hpartRes_mem : ∀ p j, (fun z : DSub hk obs => partRes p j z.val) ∈ spanD hk obs p := by
    intro p j
    have hfun : (fun z : DSub hk obs => partRes p j z.val) =
        ∑ u : Fin δ, ∑ j' : Fin k,
          (fun z : DSub hk obs =>
            if p (Sum.inr (b, tu u, j')) = true then
              coeff (δ - u.val) j j' * form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ z.val
            else 0) := by
      funext z; simp [partRes]
    rw [hfun]
    refine Submodule.sum_mem _ fun u _ => Submodule.sum_mem _ fun j' _ => ?_
    by_cases hp : p (Sum.inr (b, tu u, j')) = true
    · simp only [hp, ↓reduceIte]
      change coeff (δ - u.val) j j' •
          (fun z : DSub hk obs => form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ z.val) ∈ spanD hk obs p
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr (b, tu u, j'), ⟨2, by omega⟩, hp, rfl⟩)
    · simp only [hp, ↓reduceIte]
      exact Submodule.zero_mem _
  have hpartKey_mem : ∀ p j, (fun z : DSub hk obs => partKey p j z.val) ∈ spanD hk obs p := by
    intro p j
    have hfun : (fun z : DSub hk obs => partKey p j z.val) =
        ∑ u : Fin δ, ∑ j' : Fin k,
          (fun z : DSub hk obs =>
            let idx := ix hk (j'.val + k - feed b (tu u).val % k)
            if p (Sum.inl idx) = true then
              coeff (δ - u.val) j j' * form hk (Sum.inl idx) ⟨0, by omega⟩ z.val
            else 0) := by
      funext z; simp [partKey]
    rw [hfun]
    refine Submodule.sum_mem _ fun u _ => Submodule.sum_mem _ fun j' _ => ?_
    set idx := ix hk (j'.val + k - feed b (tu u).val % k)
    by_cases hp : p (Sum.inl idx) = true
    · simp only [hp, ↓reduceIte]
      change coeff (δ - u.val) j j' •
          (fun z : DSub hk obs => form hk (Sum.inl idx) ⟨0, by omega⟩ z.val) ∈ spanD hk obs p
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl idx, ⟨0, by omega⟩, hp, rfl⟩)
    · simp only [hp, ↓reduceIte]
      exact Submodule.zero_mem _
  have hpartRes_add : ∀ j z,
      partRes cut j z + partRes (fun x => !(cut x)) j z =
        ∑ u : Fin δ, ((mixLin hk b) ^ (δ - u.val))
          (fun j' => form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ z) j := by
    intro j z
    simp only [partRes, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [linear_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro j' _
    by_cases hc : cut (Sum.inr (b, tu u, j')) = true
    · simp [hc, coeff]
    · have hcf : cut (Sum.inr (b, tu u, j')) = false := by
        cases h : cut (Sum.inr (b, tu u, j'))
        · rfl
        · exact absurd h hc
      simp [hcf, coeff]
  have hpartKey_add : ∀ j z,
      partKey cut j z + partKey (fun x => !(cut x)) j z =
        ∑ u : Fin δ, ((mixLin hk b) ^ (δ - u.val)) (rot hk (feed b (tu u).val) z.1) j := by
    intro j z
    simp only [partKey, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [linear_apply_eq_sum]
    apply Finset.sum_congr rfl
    intro j' _
    set idx := ix hk (j'.val + k - feed b (tu u).val % k)
    by_cases hc : cut (Sum.inl idx) = true
    · simp [hc, coeff, form, rot, idx]
    · have hcf : cut (Sum.inl idx) = false := by
        cases h : cut (Sum.inl idx)
        · rfl
        · exact absurd h hc
      simp [hcf, coeff, form, rot, idx]
  have hident : ∀ j z,
      mix hk b (z.2 b ⟨a + hi.val, by omega⟩) j +
        partRes (fun x => !(cut x)) j z + partKey (fun x => !(cut x)) j z =
      ((mixLin hk b) ^ (δ + 1)) (z.2 b ⟨a + lo.val, by omega⟩) j +
        partRes cut j z + partKey cut j z := by
    intro j z
    apply (zmod2_eq_iff_add_eq_zero _ _).mpr
    have htele := congrFun (telescoping_mix hk b (z.2 b) (a + lo.val) δ hδ hbd) j
    have hhi_eq : (⟨a + lo.val + δ, by omega⟩ : Fin (r + 1)) = ⟨a + hi.val, by omega⟩ :=
      Fin.ext (show a + lo.val + δ = a + hi.val by omega)
    rw [hhi_eq] at htele
    have hstep : ∀ u : Fin δ,
        (fun j' => form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ z) +
          rot hk (feed b (tu u).val) z.1 =
          z.2 b ⟨a + lo.val + u.val + 1, by omega⟩ +
            mixLin hk b (z.2 b ⟨a + lo.val + u.val, by omega⟩) := by
      intro u
      funext j'
      simp only [Pi.add_apply, form, Sum.elim_inr, ↓reduceIte]
      change z.2 b ⟨a + lo.val + u.val + 1, by omega⟩ j' +
          mix hk b (z.2 b ⟨a + lo.val + u.val, by omega⟩) j' +
          rot hk (feed b (tu u).val) z.1 j' +
          rot hk (feed b (tu u).val) z.1 j' =
        z.2 b ⟨a + lo.val + u.val + 1, by omega⟩ j' +
          mix hk b (z.2 b ⟨a + lo.val + u.val, by omega⟩) j'
      exact zmod2_add_cancel_right _ _
    have hsum_rk : (partRes cut j z + partRes (fun x => !(cut x)) j z) +
        (partKey cut j z + partKey (fun x => !(cut x)) j z) =
        mix hk b (z.2 b ⟨a + hi.val, by omega⟩) j +
          ((mixLin hk b) ^ (δ + 1)) (z.2 b ⟨a + lo.val, by omega⟩) j := by
      rw [hpartRes_add, hpartKey_add, ← Finset.sum_add_distrib]
      have hterm : ∀ u : Fin δ,
          ((mixLin hk b) ^ (δ - u.val)) (fun j' => form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ z) j +
            ((mixLin hk b) ^ (δ - u.val)) (rot hk (feed b (tu u).val) z.1) j =
          (((mixLin hk b) ^ (δ - u.val)) (z.2 b ⟨a + lo.val + u.val + 1, by omega⟩) +
           ((mixLin hk b) ^ (δ - u.val + 1)) (z.2 b ⟨a + lo.val + u.val, by omega⟩)) j := by
        intro u
        rw [← Pi.add_apply, ← map_add, hstep u, map_add]
        have hp1 : ((mixLin hk b) ^ (δ - u.val)) (mixLin hk b (z.2 b ⟨a + lo.val + u.val, by omega⟩)) =
            ((mixLin hk b) ^ (δ - u.val + 1)) (z.2 b ⟨a + lo.val + u.val, by omega⟩) := by
          rw [pow_succ]; rfl
        rw [hp1]
      simp_rw [hterm, ← Finset.sum_apply]
      exact htele
    calc (mix hk b (z.2 b ⟨a + hi.val, by omega⟩) j +
            partRes (fun x => !(cut x)) j z + partKey (fun x => !(cut x)) j z) +
          (((mixLin hk b) ^ (δ + 1)) (z.2 b ⟨a + lo.val, by omega⟩) j +
            partRes cut j z + partKey cut j z)
        = (mix hk b (z.2 b ⟨a + hi.val, by omega⟩) j +
            ((mixLin hk b) ^ (δ + 1)) (z.2 b ⟨a + lo.val, by omega⟩) j) +
          ((partRes cut j z + partRes (fun x => !(cut x)) j z) +
            (partKey cut j z + partKey (fun x => !(cut x)) j z)) := by ac_rfl
      _ = (mix hk b (z.2 b ⟨a + hi.val, by omega⟩) j +
            ((mixLin hk b) ^ (δ + 1)) (z.2 b ⟨a + lo.val, by omega⟩) j) +
          (mix hk b (z.2 b ⟨a + hi.val, by omega⟩) j +
            ((mixLin hk b) ^ (δ + 1)) (z.2 b ⟨a + lo.val, by omega⟩) j) := by rw [hsum_rk]
      _ = 0 := zmod2_add_self _
  let ι : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (r + 1) → Fin k → ZMod 2) :=
    { toFun := fun w s =>
        if a + lo.val ≤ s.val ∧ s.val ≤ a + hi.val then
          ((mixLin hk b) ^ (s.val - (a + lo.val))) w
        else 0
      map_add' := fun u v => funext fun s => by
        simp only [Pi.add_apply]
        split_ifs
        · exact map_add _ u v
        · simp
      map_smul' := fun c v => funext fun s => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        split_ifs
        · exact map_smul _ c v
        · simp }
  have hι_supp : ∀ w (s : Fin (r + 1)), ¬(a ≤ s.val ∧ s.val < a + m) → ι w s = 0 := by
    intro w s hs
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs with h
    · exfalso; omega
    · rfl
  have hrank := finrank_range_le_width_add_cost hk obs cut b a m ha ι hι_supp
    ((mixLin hk b) ^ (δ + 1)) (by
      intro j
      refine ⟨fun z : DSub hk obs =>
          mix hk b (z.val.2 b ⟨a + hi.val, by omega⟩) j +
            partRes (fun x => !(cut x)) j z.val + partKey (fun x => !(cut x)) j z.val,
        ⟨?_, ?_⟩, ?_⟩
      · have heq : (fun z : DSub hk obs =>
            mix hk b (z.val.2 b ⟨a + hi.val, by omega⟩) j +
              partRes (fun x => !(cut x)) j z.val + partKey (fun x => !(cut x)) j z.val) =
            (fun z : DSub hk obs =>
              ((mixLin hk b) ^ (δ + 1)) (z.val.2 b ⟨a + lo.val, by omega⟩) j +
                partRes cut j z.val + partKey cut j z.val) :=
          funext fun z => hident j z.val
        rw [heq]
        refine Submodule.add_mem _ (Submodule.add_mem _ ?_ (hpartRes_mem cut j)) (hpartKey_mem cut j)
        have hpow_exp : (fun z : DSub hk obs =>
            ((mixLin hk b) ^ (δ + 1)) (z.val.2 b ⟨a + lo.val, by omega⟩) j) =
            ∑ j' : Fin k, coeff δ j j' •
              (fun z : DSub hk obs => mix hk b (z.val.2 b ⟨a + lo.val, by omega⟩) j') := by
          funext z
          rw [Finset.sum_apply, pow_succ]
          change ((mixLin hk b) ^ δ) (mix hk b (z.val.2 b ⟨a + lo.val, by omega⟩)) j = _
          rw [linear_apply_eq_sum]
          rfl
        rw [hpow_exp]
        refine Submodule.sum_mem _ fun j' _ => Submodule.smul_mem _ _ ?_
        exact mix_coord_mem_spanD hk obs cut b ⟨a + lo.val, by omega⟩ j' (hlo _)
      · refine Submodule.add_mem _ (Submodule.add_mem _ ?_ (hpartRes_mem _ j)) (hpartKey_mem _ j)
        have hhi' : (fun x => !(cut x)) (Sum.inr (b, ⟨a + hi.val, by omega⟩, ix hk (j.val + k - 1 % k))) = true := by
          simp [hhi]
        exact mix_coord_mem_spanD hk obs (fun x => !(cut x)) b ⟨a + hi.val, by omega⟩ j hhi'
      · intro w hv
        have hz2 : ∀ s : Fin (r + 1), (embed b (ι w)).2 b s = ι w s := fun s => by
          simp [embed]
        have hres0 : partRes (fun x => !(cut x)) j (embed b (ι w)) = 0 := by
          apply Finset.sum_eq_zero
          intro u _
          apply Finset.sum_eq_zero
          intro j' _
          split_ifs
          · have hf2 : form hk (Sum.inr (b, tu u, j')) ⟨2, by omega⟩ (embed b (ι w)) = 0 := by
              simp only [form, Sum.elim_inr, hz2]
              have hc1 : a + lo.val ≤ (tu u).succ.val ∧ (tu u).succ.val ≤ a + hi.val := by
                simp only [tu, Fin.val_succ]; omega
              have hc0 : a + lo.val ≤ (tu u).castSucc.val ∧ (tu u).castSucc.val ≤ a + hi.val := by
                simp only [tu, Fin.val_castSucc]; omega
              have hs1 : ι w (tu u).succ = ((mixLin hk b) ^ (u.val + 1)) w := by
                simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, hc1, and_self, ↓reduceIte]
                have : (tu u).succ.val - (a + lo.val) = u.val + 1 := by simp [tu]; omega
                rw [this]
              have hs0 : ι w (tu u).castSucc = ((mixLin hk b) ^ u.val) w := by
                simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, hc0, and_self, ↓reduceIte]
                have : (tu u).castSucc.val - (a + lo.val) = u.val := by simp [tu]
                rw [this]
              have hrot0 : rot hk (feed b (tu u).val) (embed b (ι w)).1 j' = 0 := rfl
              rw [hs1, hs0, hrot0, add_zero]
              change ((mixLin hk b) ^ (u.val + 1)) w j' + mixLin hk b (((mixLin hk b) ^ u.val) w) j' = 0
              have hp1 : mixLin hk b (((mixLin hk b) ^ u.val) w) = ((mixLin hk b) ^ (u.val + 1)) w := by
                conv_rhs => rw [pow_succ']
                rfl
              rw [hp1]
              exact zmod2_add_self _
            rw [hf2, mul_zero]
          · rfl
        have hkey0 : partKey (fun x => !(cut x)) j (embed b (ι w)) = 0 := by
          apply Finset.sum_eq_zero
          intro u _
          apply Finset.sum_eq_zero
          intro j' _
          dsimp only
          split_ifs
          · have hf0 : form hk (Sum.inl (ix hk (j'.val + k - feed b (tu u).val % k))) ⟨0, by omega⟩
                (embed b (ι w)) = 0 := rfl
            rw [hf0, mul_zero]
          · rfl
        dsimp only
        rw [hres0, hkey0, add_zero, add_zero, hz2]
        have hhi_in : a + lo.val ≤ a + hi.val ∧ a + hi.val ≤ a + hi.val := by omega
        have hhi_val : ι w ⟨a + hi.val, by omega⟩ = ((mixLin hk b) ^ δ) w := by
          simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, hhi_in, and_self, ↓reduceIte]
          have : a + hi.val - (a + lo.val) = δ := by omega
          rw [this]
        rw [hhi_val]
        change mixLin hk b (((mixLin hk b) ^ δ) w) j = ((mixLin hk b) ^ (δ + 1)) w j
        conv_rhs => rw [pow_succ']
        rfl)
  have hmono : LinearMap.range ((mixLin hk b) ^ m) ≤ LinearMap.range ((mixLin hk b) ^ (δ + 1)) := by
    rintro _ ⟨w, rfl⟩
    refine ⟨((mixLin hk b) ^ (m - (δ + 1))) w, ?_⟩
    change (((mixLin hk b) ^ (δ + 1) * (mixLin hk b) ^ (m - (δ + 1))) w) = _
    rw [← pow_add]
    have heq : δ + 1 + (m - (δ + 1)) = m := by omega
    rw [heq]
  exact le_trans (survive_le_finrank_range hk b m)
    (le_trans (Submodule.finrank_mono hmono) hrank)

lemma exists_color_change {k : Nat} (hk : 0 < k) (c : Fin k → Bool)
    (ht : ∃ x : Fin k, c x = true) (hf : ∃ y : Fin k, c y = false) :
    ∃ j : Fin k, c j = true ∧ c (ix hk (j.val + 1)) = false := by
  by_contra h
  push Not at h
  rcases ht with ⟨x, hx⟩
  rcases hf with ⟨y, hy⟩
  have hstep : ∀ n : Nat, c (ix hk (x.val + n)) = true := by
    intro n
    induction n with
    | zero => rwa [Nat.add_zero, ix_of_fin]
    | succ n ih =>
      have hnext := h (ix hk (x.val + n)) ih
      rw [ix_add_left] at hnext
      have ha : x.val + n + 1 = x.val + (n + 1) := by omega
      rw [ha] at hnext
      cases hval : c (ix hk (x.val + (n + 1)))
      · exact absurd hval hnext
      · rfl
  have hreach := hstep (y.val + k - x.val)
  have heq : ix hk (x.val + (y.val + k - x.val)) = y := by
    apply Fin.ext
    simp only [ix]
    have h1 : x.val + (y.val + k - x.val) = y.val + k * 1 := by omega
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
  rw [heq, hy] at hreach
  exact Bool.noConfusion hreach

lemma mix_single_diag {k : Nat} (hk : 0 < k) (b : Bool) (u : Fin k) :
    mix hk b (Pi.single u 1) u = 1 := by
  dsimp only [mix]
  set d := if b then 2 else 1
  simp only [Pi.single_eq_same]
  have hiff : ix hk (u.val + d) = u ↔ ix hk (u.val + k - d % k) = u := by
    have hdlt : d % k < k := Nat.mod_lt d hk
    have hult : u.val < k := u.isLt
    constructor
    · intro h
      have h1 : (u.val + d % k) % k = u.val := by
        have h0 := congrArg Fin.val h
        simp only [ix] at h0
        simpa [Nat.add_mod] using h0
      have hdm : d % k = 0 := (add_mod_eq_self_iff hult hdlt).mp h1
      apply Fin.ext; simp only [ix, hdm, Nat.sub_zero]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt hult]
    · intro h
      have h1 := congrArg Fin.val h
      simp only [ix] at h1
      have hdm : d % k = 0 := by
        by_cases h0 : d % k = 0
        · exact h0
        · have hksub : k - d % k < k := by omega
          have h2 : (u.val + (k - d % k)) % k = u.val := by
            rw [← Nat.add_sub_assoc (le_of_lt hdlt)]; exact h1
          have := (add_mod_eq_self_iff hult hksub).mp h2
          omega
      apply Fin.ext; simp only [ix]
      rw [Nat.add_mod, hdm, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hult]
  by_cases hp : ix hk (u.val + d) = u
  · have hm : ix hk (u.val + k - d % k) = u := hiff.mp hp
    rw [hp, hm, Pi.single_eq_same]
    decide
  · have hm : ix hk (u.val + k - d % k) ≠ u := fun h => hp (hiff.mpr h)
    rw [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hm]
    simp

lemma mix_two_rows_dist {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (b : Bool)
    (hsh : ¬(k = 3 ∨ (b = true ∧ k = 6))) {u v : Fin k} (huv : u ≠ v) :
    ∃ x : Fin k, mix hk b (Pi.single x 1) u ≠ mix hk b (Pi.single x 1) v := by
  by_contra hall
  push Not at hall
  set d := if b then 2 else 1
  have hsupp : ∀ (a x : Fin k), mix hk b (Pi.single x 1) a = 1 →
      x = a ∨ x = ix hk (a.val + d) ∨ x = ix hk (a.val + k - d % k) := by
    intro a x h1
    by_contra hne
    push Not at hne
    rcases hne with ⟨h0, h2, h3⟩
    have hz : mix hk b (Pi.single x 1) a = 0 := by
      dsimp only [mix]
      rw [Pi.single_eq_of_ne (Ne.symm h0), Pi.single_eq_of_ne (Ne.symm h2),
        Pi.single_eq_of_ne (Ne.symm h3)]
      simp
    rw [hz] at h1
    exact zero_ne_one h1
  have hMu_v : mix hk b (Pi.single v 1) u = 1 := by
    rw [hall v]; exact mix_single_diag hk b v
  have hv_in : v = ix hk (u.val + d) ∨ v = ix hk (u.val + k - d % k) := by
    rcases hsupp u v hMu_v with h | h | h
    · exact absurd h.symm huv
    · exact Or.inl h
    · exact Or.inr h
  have hd_ne : ix hk (u.val + d) ≠ ix hk (u.val + k - d % k) := by
    intro heq
    have hz : mix hk b (Pi.single v 1) u = 0 := by
      dsimp only [mix]
      rw [Pi.single_eq_of_ne huv, heq, zero_add]
      exact zmod2_add_self _
    rw [hz] at hMu_v
    exact zero_ne_one hMu_v
  have h2d_mod : (2 * d) % k ≠ 0 := by
    intro h2z
    apply hd_ne
    apply Fin.ext
    simp only [ix]
    have hdlt : d % k < k := Nat.mod_lt d hk
    have hd2 : (2 * (d % k)) % k = 0 := by
      have : (2 * (d % k)) % k = (2 * d) % k := by simp [Nat.mul_mod]
      rw [this, h2z]
    have hcases : d % k = 0 ∨ 2 * (d % k) = k := by
      by_cases hlt : 2 * (d % k) < k
      · rw [Nat.mod_eq_of_lt hlt] at hd2; omega
      · have hlt2 : 2 * (d % k) - k < k := by omega
        have hmod : (2 * (d % k)) % k = 2 * (d % k) - k := by
          have h1 : 2 * (d % k) = (2 * (d % k) - k) + k * 1 := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt2]
        rw [hmod] at hd2; omega
    rcases hcases with h0 | hhalf
    · rw [h0, Nat.sub_zero, Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod, Nat.add_mod_right]
    · have h1 : (u.val + d) % k = (u.val + d % k) % k := by simp [Nat.add_mod]
      rw [h1]
      have h2 : u.val + k - d % k = u.val + d % k := by omega
      rw [h2]
  have hd_mod : d % k ≠ 0 := by
    intro h0
    apply h2d_mod
    rw [Nat.mul_mod, h0, mul_zero, Nat.zero_mod]
  have h3d : ∀ (a c : Fin k), c = ix hk (a.val + d) →
      (∀ x, mix hk b (Pi.single x 1) a = mix hk b (Pi.single x 1) c) → (3 * d) % k = 0 := by
    intro a c hc hall_ac
    set y := ix hk (c.val + d)
    have hy_ne_c : y ≠ c := by
      intro hyc
      have h1 : (c.val + d % k) % k = c.val := by
        have h0 := congrArg Fin.val hyc
        simp only [y, ix] at h0
        simpa [Nat.add_mod] using h0
      exact hd_mod ((add_mod_eq_self_iff c.isLt (Nat.mod_lt d hk)).mp h1)
    have hy_ne_cm : y ≠ ix hk (c.val + k - d % k) := by
      intro hym
      have hstep : ix hk ((ix hk (c.val + d)).val + d) =
          ix hk ((ix hk (c.val + k - d % k)).val + d) := by rw [← hym]
      rw [ix_add_left, ix_sub_add_cancel] at hstep
      have h1 : (c.val + (2 * d) % k) % k = c.val := by
        have h0 := congrArg Fin.val hstep
        simp only [ix] at h0
        have h2 : c.val + d + d = c.val + 2 * d := by omega
        rw [h2] at h0
        simpa [Nat.add_mod] using h0
      exact h2d_mod ((add_mod_eq_self_iff c.isLt (Nat.mod_lt (2 * d) hk)).mp h1)
    have hMc_y : mix hk b (Pi.single y 1) c = 1 := by
      dsimp only [mix]
      rw [Pi.single_eq_of_ne hy_ne_c.symm, Pi.single_eq_same, Pi.single_eq_of_ne hy_ne_cm.symm]
      simp
    have hMa_y : mix hk b (Pi.single y 1) a = 1 := by rw [hall_ac y]; exact hMc_y
    have hy_a : y = ix hk (a.val + 2 * d) := by
      simp only [y, hc, ix_add_left]
      have : a.val + d + d = a.val + 2 * d := by omega
      rw [this]
    rcases hsupp a y hMa_y with h0 | h1 | h2
    · rw [hy_a] at h0
      have hv1 : (a.val + (2 * d) % k) % k = a.val := by
        have h0' := congrArg Fin.val h0
        simp only [ix] at h0'
        simpa [Nat.add_mod] using h0'
      exact absurd ((add_mod_eq_self_iff a.isLt (Nat.mod_lt (2 * d) hk)).mp hv1) h2d_mod
    · rw [hy_a] at h1
      have hv1 : ((a.val + d) % k + d % k) % k = (a.val + d) % k := by
        have h0' := congrArg Fin.val h1
        simp only [ix] at h0'
        have h2 : a.val + 2 * d = (a.val + d) + d := by omega
        rw [h2] at h0'
        simpa [Nat.add_mod] using h0'
      exact absurd ((add_mod_eq_self_iff (Nat.mod_lt (a.val + d) hk) (Nat.mod_lt d hk)).mp hv1) hd_mod
    · rw [hy_a] at h2
      have hstep : ix hk ((ix hk (a.val + 2 * d)).val + d) =
          ix hk ((ix hk (a.val + k - d % k)).val + d) := by rw [h2]
      rw [ix_add_left, ix_sub_add_cancel] at hstep
      have h1' : (a.val + (3 * d) % k) % k = a.val := by
        have h0' := congrArg Fin.val hstep
        simp only [ix] at h0'
        have h3 : a.val + 2 * d + d = a.val + 3 * d := by omega
        rw [h3] at h0'
        simpa [Nat.add_mod] using h0'
      exact (add_mod_eq_self_iff a.isLt (Nat.mod_lt (3 * d) hk)).mp h1'
  have h3d0 : (3 * d) % k = 0 := by
    rcases hv_in with h1 | h2
    · exact h3d u v h1 hall
    · have hu_eq : u = ix hk (v.val + d) := by
        rw [h2, ix_sub_add_cancel]
      exact h3d v u hu_eq (fun x => (hall x).symm)
  cases b
  · change 3 % k = 0 at h3d0
    by_cases hk3 : k ≤ 3
    · interval_cases k
      · simp at h3d0
      · exact hsh (Or.inl rfl)
    · rw [Nat.mod_eq_of_lt (by omega)] at h3d0
      omega
  · change 6 % k = 0 at h3d0
    change 4 % k ≠ 0 at h2d_mod
    by_cases hk6 : k ≤ 6
    · interval_cases k
      · simp at h2d_mod
      · exact hsh (Or.inl rfl)
      · simp at h2d_mod
      · simp at h3d0
      · exact hsh (Or.inr ⟨rfl, rfl⟩)
    · rw [Nat.mod_eq_of_lt (by omega)] at h3d0
      omega

lemma mix_two_rows_basis {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (b : Bool)
    {u v : Fin k} (huv : u ≠ v) :
    let sh := if k = 3 ∨ (b = true ∧ k = 6) then 1 else 2
    ∃ w : Fin sh → (Fin k → ZMod 2),
      ∀ e₁ e₂ : Fin sh,
        mix hk b (w e₁) (if e₂.val = 0 then u else v) = if e₁ = e₂ then 1 else 0 := by
  intro sh
  by_cases hsh : k = 3 ∨ (b = true ∧ k = 6)
  · have hsh1 : sh = 1 := by simp only [sh, hsh, ↓reduceIte]
    refine ⟨fun _ => Pi.single u 1, fun e₁ e₂ => ?_⟩
    have he1 : e₁.val = 0 := by omega
    have he2 : e₂.val = 0 := by omega
    have heq : e₁ = e₂ := Fin.ext (by omega)
    simp only [he2, heq, ↓reduceIte]
    exact mix_single_diag hk b u
  · have hsh2 : sh = 2 := by simp only [sh, hsh, ↓reduceIte]
    rcases mix_two_rows_dist hk hk2 b hsh huv with ⟨x, hx⟩
    have hmu : mix hk b (Pi.single u 1) u = 1 := mix_single_diag hk b u
    have hmv : mix hk b (Pi.single v 1) v = 1 := mix_single_diag hk b v
    have hmx_cases := zmod2_ne_cases hx
    have hpair : ∃ w0 w1 : Fin k → ZMod 2,
        mix hk b w0 u = 1 ∧ mix hk b w0 v = 0 ∧ mix hk b w1 u = 0 ∧ mix hk b w1 v = 1 := by
      rcases hmx_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨Pi.single x 1,
          if mix hk b (Pi.single v 1) u = 0 then Pi.single v 1 else Pi.single v 1 + Pi.single x 1,
          h1, h2, ?_, ?_⟩
        · split_ifs with hv0
          · exact hv0
          · change (mixLin hk b (Pi.single v 1 + Pi.single x 1)) u = 0
            rw [map_add, Pi.add_apply]
            have hv1 : mix hk b (Pi.single v 1) u = 1 := zmod2_eq_one_of_ne_zero hv0
            change mix hk b (Pi.single v 1) u + mix hk b (Pi.single x 1) u = 0
            rw [hv1, h1]; decide
        · split_ifs with hv0
          · exact hmv
          · change (mixLin hk b (Pi.single v 1 + Pi.single x 1)) v = 1
            rw [map_add, Pi.add_apply]
            change mix hk b (Pi.single v 1) v + mix hk b (Pi.single x 1) v = 1
            rw [hmv, h2, add_zero]
      · refine ⟨if mix hk b (Pi.single u 1) v = 0 then Pi.single u 1 else Pi.single u 1 + Pi.single x 1,
          Pi.single x 1, ?_, ?_, h1, h2⟩
        · split_ifs with hu0
          · exact hmu
          · change (mixLin hk b (Pi.single u 1 + Pi.single x 1)) u = 1
            rw [map_add, Pi.add_apply]
            change mix hk b (Pi.single u 1) u + mix hk b (Pi.single x 1) u = 1
            rw [hmu, h1, add_zero]
        · split_ifs with hu0
          · exact hu0
          · change (mixLin hk b (Pi.single u 1 + Pi.single x 1)) v = 0
            rw [map_add, Pi.add_apply]
            have hu1 : mix hk b (Pi.single u 1) v = 1 := zmod2_eq_one_of_ne_zero hu0
            change mix hk b (Pi.single u 1) v + mix hk b (Pi.single x 1) v = 0
            rw [hu1, h2]; decide
    rcases hpair with ⟨w0, w1, hw0u, hw0v, hw1u, hw1v⟩
    refine ⟨fun e => if e.val = 0 then w0 else w1, fun e₁ e₂ => ?_⟩
    have h1 : e₁.val = 0 ∨ e₁.val = 1 := by omega
    have h2 : e₂.val = 0 ∨ e₂.val = 1 := by omega
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have heq : e₁ = e₂ := Fin.ext (by omega)
      simp [h1, h2, heq, hw0u]
    · have hne : e₁ ≠ e₂ := fun h => by have := congrArg Fin.val h; omega
      simp [h1, h2, hne, hw0v]
    · have hne : e₁ ≠ e₂ := fun h => by have := congrArg Fin.val h; omega
      simp [h1, h2, hne, hw1u]
    · have heq : e₁ = e₂ := Fin.ext (by omega)
      simp [h1, h2, heq, hw1v]

lemma region_mixed_bound {k r q : Nat} (hk : 0 < k) (hk2 : 2 ≤ k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (R : (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool)
    (b : Bool) (a m : Nat) (ha : 0 < a) (ham : a + m ≤ r)
    (S : Finset (Fin m))
    (hS : ∀ t ∈ S,
      (∃ j : Fin k, R (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true) ∧
      (∃ j : Fin k, R (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = false)) :
    (if k = 3 ∨ (b = true ∧ k = 6) then 1 else 2) * S.card ≤
      width hk obs R +
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (seenFun obs b a m))) := by
  classical
  set sh := if k = 3 ∨ (b = true ∧ k = 6) then 1 else 2
  have hex : ∀ t : S, ∃ (u v : Fin k) (w : Fin sh → (Fin k → ZMod 2)),
      (fun z : DSub hk obs => mix hk b (z.val.2 b ⟨a + t.1.val, by omega⟩) u) ∈
        spanD hk obs R ⊓ spanD hk obs (fun j => !(R j)) ∧
      (fun z : DSub hk obs => mix hk b (z.val.2 b ⟨a + t.1.val, by omega⟩) v) ∈
        spanD hk obs R ⊓ spanD hk obs (fun j => !(R j)) ∧
      ∀ e₁ e₂ : Fin sh,
        mix hk b (w e₁) (if e₂.val = 0 then u else v) = if e₁ = e₂ then 1 else 0 := by
    intro t
    rcases hS t.1 t.2 with ⟨ht, hf⟩
    let c : Fin k → Bool := fun j => R (Sum.inr (b, ⟨a + t.1.val, by omega⟩, j))
    rcases exists_color_change hk c ht hf with ⟨j1, hj1t, hj1f⟩
    have ht' : ∃ x : Fin k, (!c x) = true := by
      rcases hf with ⟨y, hy⟩; exact ⟨y, by change (!c y) = true; simp [c, hy]⟩
    have hf' : ∃ y : Fin k, (!c y) = false := by
      rcases ht with ⟨x, hx⟩; exact ⟨x, by change (!c x) = false; simp [c, hx]⟩
    rcases exists_color_change hk (fun j => !(c j)) ht' hf' with ⟨j2, hj2f', hj2t'⟩
    have hj2f : c j2 = false := by simpa using hj2f'
    have hj2t : c (ix hk (j2.val + 1)) = true := by simpa using hj2t'
    have hjne : j1 ≠ j2 := fun h => by rw [h, hj2f] at hj1t; exact Bool.noConfusion hj1t
    set u := ix hk (j1.val + 2)
    set v := ix hk (j2.val + 2)
    have huv : u ≠ v := by
      intro heq
      have h1 : ix hk (u.val + k - 2 % k) = ix hk (v.val + k - 2 % k) :=
        congrArg (fun x : Fin k => ix hk (x.val + k - 2 % k)) heq
      simp only [u, v, ix_add_sub_cancel] at h1
      exact hjne h1
    rcases mix_two_rows_basis hk hk2 b huv with ⟨w, hw⟩
    refine ⟨u, v, w, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hw⟩
    · apply Submodule.subset_span
      refine ⟨Sum.inr (b, ⟨a + t.1.val, by omega⟩, j1), ⟨1, by omega⟩, hj1t, ?_⟩
      funext z; simp [form, u]
    · apply Submodule.subset_span
      refine ⟨Sum.inr (b, ⟨a + t.1.val, by omega⟩, ix hk (j1.val + 1)), ⟨0, by omega⟩,
        by simp [c] at hj1f; simp [hj1f], ?_⟩
      funext z
      simp only [form, Sum.elim_inr, ↓reduceIte]
      rw [ix_add_left]
      have : j1.val + 1 + 1 = j1.val + 2 := by omega
      simp [u, this]
    · apply Submodule.subset_span
      refine ⟨Sum.inr (b, ⟨a + t.1.val, by omega⟩, ix hk (j2.val + 1)), ⟨0, by omega⟩, hj2t, ?_⟩
      funext z
      simp only [form, Sum.elim_inr, ↓reduceIte]
      rw [ix_add_left]
      have : j2.val + 1 + 1 = j2.val + 2 := by omega
      simp [v, this]
    · apply Submodule.subset_span
      refine ⟨Sum.inr (b, ⟨a + t.1.val, by omega⟩, j2), ⟨1, by omega⟩,
        by simp [c] at hj2f; simp [hj2f], ?_⟩
      funext z; simp [form, v]
  let uOf (t : S) : Fin k := Classical.choose (hex t)
  let vOf (t : S) : Fin k := Classical.choose (Classical.choose_spec (hex t))
  let wOf (t : S) : Fin sh → (Fin k → ZMod 2) :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hex t)))
  have hspec (t : S) := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hex t)))
  let ι : (S → Fin k → ZMod 2) →ₗ[ZMod 2] (Fin (r + 1) → Fin k → ZMod 2) :=
    { toFun := fun f s =>
        if hs : a ≤ s.val ∧ s.val < a + m then
          let t : Fin m := ⟨s.val - a, by omega⟩
          if ht : t ∈ S then f ⟨t, ht⟩ else 0
        else 0
      map_add' := fun f g => funext fun s => by
        simp only [Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c f => funext fun s => by
        simp only [Pi.smul_apply, RingHom.id_apply]
        split_ifs <;> simp }
  have hι_supp : ∀ f (s : Fin (r + 1)), ¬(a ≤ s.val ∧ s.val < a + m) → ι f s = 0 := by
    intro f s hs
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, hs, ↓reduceDIte]
  have hι_at : ∀ f (t : S), ι f ⟨a + t.1.val, by omega⟩ = f t := by
    intro f t
    have htlt : t.1.val < m := t.1.isLt
    have hs : a ≤ a + t.1.val ∧ a + t.1.val < a + m := by omega
    simp only [ι, LinearMap.coe_mk, AddHom.coe_mk, hs]
    have hteq : (⟨a + t.1.val - a, by omega⟩ : Fin m) = t.1 := Fin.ext (show a + t.1.val - a = t.1.val by omega)
    have hmem : (⟨a + t.1.val - a, by omega⟩ : Fin m) ∈ S := by rw [hteq]; exact t.2
    simp only [hmem, ↓reduceDIte]
    exact congrArg f (Subtype.ext hteq)
  let T : (S → Fin k → ZMod 2) →ₗ[ZMod 2] (S × Fin sh → ZMod 2) :=
    { toFun := fun f te => mixLin hk b (f te.1) (if te.2.val = 0 then uOf te.1 else vOf te.1)
      map_add' := fun f g => funext fun te => by
        simp [map_add]
      map_smul' := fun c f => funext fun te => by
        simp [map_smul] }
  have hT_surj : LinearMap.range T = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    refine ⟨fun t => ∑ e : Fin sh, y (t, e) • wOf t e, ?_⟩
    funext ⟨t, e₂⟩
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    have hterm : ∀ e₁ : Fin sh,
        y (t, e₁) * (mixLin hk b (wOf t e₁)) (if e₂.val = 0 then uOf t else vOf t) =
          if e₁ = e₂ then y (t, e₁) else 0 := by
      intro e₁
      have hwb := (hspec t).2.2 e₁ e₂
      change y (t, e₁) * mix hk b (wOf t e₁) (if e₂.val = 0 then uOf t else vOf t) = _
      rw [hwb]
      split_ifs <;> simp
    simp_rw [hterm]
    simp
  have hrank := finrank_range_le_width_add_cost hk obs R b a m ha ι hι_supp T (by
    intro ⟨t, e⟩
    refine ⟨fun z : DSub hk obs =>
        mix hk b (z.val.2 b ⟨a + t.1.val, by omega⟩) (if e.val = 0 then uOf t else vOf t), ?_, ?_⟩
    · split_ifs
      · exact (hspec t).1
      · exact (hspec t).2.1
    · intro f _
      dsimp only
      have hz2 : (embed b (ι f)).2 b ⟨a + t.1.val, by omega⟩ = f t := by
        simp only [embed, ↓reduceIte]
        exact hι_at f t
      rw [hz2]
      rfl)
  have hdim : Module.finrank (ZMod 2) (LinearMap.range T) = sh * S.card := by
    rw [hT_surj, finrank_top, Module.finrank_pi, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_fin, Nat.mul_comm]
  rw [hdim] at hrank
  exact hrank

lemma main_proof (k r q : Nat) (hk : 0 < k) (hk2 : 2 ≤ k)
    (obs : Fin q → (Fin k → ZMod 2) × (Bool → Fin (r + 1) → Fin k → ZMod 2))
    (n cap : Nat) (bag : Fin n → (Fin k ⊕ (Bool × Fin r × Fin k)) → Bool)
    (htop : ∃ top : Fin n, ∀ i, bag top i = true)
    (htree : ∀ v : Fin n,
      (∃ one : Fin k ⊕ (Bool × Fin r × Fin k), ∀ j, bag v j = decide (j = one)) ∨
      ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ j, bag l j = true → bag h j = false) ∧
        ∀ j, bag v j = (bag l j || bag h j))
    (hcap : ∀ v, width hk obs (bag v) ≤ cap)
    (b : Bool) (a m : Nat) (ha : 0 < a) (hm : 0 < m) (ham : a + m ≤ r) :
    let cost := Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (seenFun obs b a m)))
    let sh := if k = 3 ∨ (b = true ∧ k = 6) then 1 else 2
    min (survive k b m) ((2 * sh * m + 2) / 3) ≤ cap + cost := by
  classical
  intro cost sh
  let hasFull (i : Nat) : Prop :=
    ∃ hi : i < n, ∃ t : Fin m, ∀ j : Fin k,
      bag ⟨i, hi⟩ (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true
  have hexFull : ∃ i, hasFull i := by
    rcases htop with ⟨top, htop⟩
    exact ⟨top.val, top.isLt, ⟨0, hm⟩, fun j => htop _⟩
  set vIdx := Nat.find hexFull
  have hv_spec : hasFull vIdx := Nat.find_spec hexFull
  have hv_min : ∀ i < vIdx, ¬ hasFull i := fun i hi => Nat.find_min hexFull hi
  rcases hv_spec with ⟨hv_lt, t1, ht1⟩
  let v : Fin n := ⟨vIdx, hv_lt⟩
  by_cases hcomp : ∃ t2 : Fin m, ∀ j : Fin k,
      bag v (Sum.inr (b, ⟨a + t2.val, by omega⟩, j)) = false
  · rcases hcomp with ⟨t2, ht2⟩
    have hne : t1 ≠ t2 := by
      intro heq
      subst heq
      have h1 := ht1 ⟨0, hk⟩
      have h2 := ht2 ⟨0, hk⟩
      change bag v (Sum.inr (b, ⟨a + t1.val, by omega⟩, ⟨0, hk⟩)) = true at h1
      rw [h1] at h2
      exact Bool.noConfusion h2
    have hsurv : survive k b m ≤ cap + cost := by
      by_cases hlt : t1.val < t2.val
      · exact le_trans (case1_bound hk obs (bag v) b a m ha hm ham t1 t2 hlt ht1 ht2)
          (Nat.add_le_add_right (hcap v) cost)
      · have hgt : t2.val < t1.val := by
          have : t1.val ≠ t2.val := fun h => hne (Fin.ext h)
          omega
        have h1' : ∀ j : Fin k, (fun x => !(bag v x)) (Sum.inr (b, ⟨a + t2.val, by omega⟩, j)) = true :=
          fun j => by simp only [ht2 j]; rfl
        have h2' : ∀ j : Fin k, (fun x => !(bag v x)) (Sum.inr (b, ⟨a + t1.val, by omega⟩, j)) = false :=
          fun j => by
            have h1j : bag v (Sum.inr (b, ⟨a + t1.val, by omega⟩, j)) = true := ht1 j
            simp only [h1j]; rfl
        have hbd := case1_bound hk obs (fun x => !(bag v x)) b a m ha hm ham t2 t1 hgt h1' h2'
        rw [width_not] at hbd
        exact le_trans hbd (Nat.add_le_add_right (hcap v) cost)
    exact le_trans (min_le_left _ _) hsurv
  · push Not at hcomp
    have hnotLeaf : ¬ ∃ one : Fin k ⊕ (Bool × Fin r × Fin k), ∀ j, bag v j = decide (j = one) := by
      rintro ⟨one, hone⟩
      have h0 : decide (Sum.inr (b, ⟨a + t1.val, by omega⟩, (⟨0, hk⟩ : Fin k)) = one) = true := by
        rw [← hone]; exact ht1 ⟨0, hk⟩
      have h1 : decide (Sum.inr (b, ⟨a + t1.val, by omega⟩, (⟨1, by omega⟩ : Fin k)) = one) = true := by
        rw [← hone]; exact ht1 ⟨1, by omega⟩
      have heq0 : Sum.inr (b, ⟨a + t1.val, by omega⟩, (⟨0, hk⟩ : Fin k)) = one := of_decide_eq_true h0
      have heq1 : Sum.inr (b, ⟨a + t1.val, by omega⟩, (⟨1, by omega⟩ : Fin k)) = one := of_decide_eq_true h1
      have heq : (⟨0, hk⟩ : Fin k) = ⟨1, by omega⟩ := by
        have h' := heq0.trans heq1.symm
        injection h' with hp
        exact congrArg (fun x => x.2.2) hp
      have hval : (0 : Nat) = 1 := congrArg Fin.val heq
      omega
    rcases (htree v).resolve_left hnotLeaf with ⟨l, h, hlv, hhv, _, hunion⟩
    have hl_nofull : ∀ t : Fin m, ∃ j : Fin k,
        bag l (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = false := by
      intro t
      by_contra hall
      push Not at hall
      have hall' : ∀ j : Fin k, bag l (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true := by
        intro j; cases hv : bag l (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
        · exact absurd hv (hall j)
        · rfl
      exact hv_min l.val hlv ⟨l.isLt, t, hall'⟩
    have hh_nofull : ∀ t : Fin m, ∃ j : Fin k,
        bag h (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = false := by
      intro t
      by_contra hall
      push Not at hall
      have hall' : ∀ j : Fin k, bag h (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true := by
        intro j; cases hv : bag h (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
        · exact absurd hv (hall j)
        · rfl
      exact hv_min h.val hhv ⟨h.isLt, t, hall'⟩
    let R0 := bag l
    let R1 := bag h
    let R2 := fun x => !(bag v x)
    let S0 : Finset (Fin m) := Finset.univ.filter fun t =>
      ∃ j : Fin k, R0 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true
    let S1 : Finset (Fin m) := Finset.univ.filter fun t =>
      ∃ j : Fin k, R1 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true
    let S2 : Finset (Fin m) := Finset.univ.filter fun t =>
      ∃ j : Fin k, R2 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true
    have hR2_nofull : ∀ t : Fin m, ∃ j : Fin k,
        R2 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = false := by
      intro t
      rcases hcomp t with ⟨j, hj⟩
      refine ⟨j, ?_⟩
      cases hbv : bag v (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
      · exact absurd hbv hj
      · simp [R2, hbv]
    have hb0 : sh * S0.card ≤ cap + cost :=
      le_trans (region_mixed_bound hk hk2 obs R0 b a m ha ham S0 (fun t ht =>
        ⟨(Finset.mem_filter.mp ht).2, hl_nofull t⟩))
        (Nat.add_le_add_right (hcap l) cost)
    have hb1 : sh * S1.card ≤ cap + cost :=
      le_trans (region_mixed_bound hk hk2 obs R1 b a m ha ham S1 (fun t ht =>
        ⟨(Finset.mem_filter.mp ht).2, hh_nofull t⟩))
        (Nat.add_le_add_right (hcap h) cost)
    have hb2 : sh * S2.card ≤ cap + cost := by
      have hbd := region_mixed_bound hk hk2 obs R2 b a m ha ham S2 (fun t ht =>
        ⟨(Finset.mem_filter.mp ht).2, hR2_nofull t⟩)
      rw [width_not] at hbd
      exact le_trans hbd (Nat.add_le_add_right (hcap v) cost)
    have hcover : ∀ t : Fin m,
        2 ≤ (if t ∈ S0 then 1 else 0) + (if t ∈ S1 then 1 else 0) + (if t ∈ S2 then 1 else 0) := by
      intro t
      have hhit : ∀ j : Fin k,
          R0 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true ∨
          R1 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true ∨
          R2 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = true := by
        intro j
        have hu := hunion (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
        cases hbv : bag v (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
        · exact Or.inr (Or.inr (by simp [R2, hbv]))
        · rw [hbv] at hu
          cases hbl : bag l (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
          · cases hbh : bag h (Sum.inr (b, ⟨a + t.val, by omega⟩, j))
            · simp [hbl, hbh] at hu
            · exact Or.inr (Or.inl hbh)
          · exact Or.inl hbl
      by_cases h0 : t ∈ S0 <;> by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2
      · simp [h0, h1, h2]
      · simp [h0, h1, h2]
      · simp [h0, h1, h2]
      · exfalso
        rcases hl_nofull t with ⟨j, hj⟩
        change R0 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = false at hj
        rcases hhit j with c0 | c1 | c2
        · rw [c0] at hj; exact Bool.noConfusion hj
        · exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨j, c1⟩⟩)
        · exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨j, c2⟩⟩)
      · simp [h0, h1, h2]
      · exfalso
        rcases hh_nofull t with ⟨j, hj⟩
        change R1 (Sum.inr (b, ⟨a + t.val, by omega⟩, j)) = false at hj
        rcases hhit j with c0 | c1 | c2
        · exact h0 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨j, c0⟩⟩)
        · rw [c1] at hj; exact Bool.noConfusion hj
        · exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨j, c2⟩⟩)
      · exfalso
        rcases hR2_nofull t with ⟨j, hj⟩
        rcases hhit j with c0 | c1 | c2
        · exact h0 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨j, c0⟩⟩)
        · exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨j, c1⟩⟩)
        · rw [c2] at hj; exact Bool.noConfusion hj
      · exfalso
        rcases hhit ⟨0, hk⟩ with c0 | c1 | c2
        · exact h0 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨⟨0, hk⟩, c0⟩⟩)
        · exact h1 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨⟨0, hk⟩, c1⟩⟩)
        · exact h2 (Finset.mem_filter.mpr ⟨Finset.mem_univ t, ⟨⟨0, hk⟩, c2⟩⟩)
    have hsum_card : 2 * m ≤ S0.card + S1.card + S2.card := by
      have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun t _ => hcover t)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at hs
      have hf0 : (Finset.univ.filter fun t : Fin m => t ∈ S0).card = S0.card := by
        congr 1; ext t; simp
      have hf1 : (Finset.univ.filter fun t : Fin m => t ∈ S1).card = S1.card := by
        congr 1; ext t; simp
      have hf2 : (Finset.univ.filter fun t : Fin m => t ∈ S2).card = S2.card := by
        congr 1; ext t; simp
      rw [hf0, hf1, hf2] at hs
      omega
    have hmul : 2 * sh * m ≤ 3 * (cap + cost) := by
      have h1 : sh * (2 * m) ≤ sh * (S0.card + S1.card + S2.card) :=
        Nat.mul_le_mul_left sh hsum_card
      have h2 : sh * (S0.card + S1.card + S2.card) =
          sh * S0.card + sh * S1.card + sh * S2.card := by
        rw [Nat.mul_add, Nat.mul_add]
      have h3 : 2 * sh * m = sh * (2 * m) := by ac_rfl
      omega
    have hdiv : (2 * sh * m + 2) / 3 ≤ cap + cost := by omega
    exact le_trans (min_le_right _ _) hdiv

end PEqualNP.Outside.L_meta_29931

theorem PEqualNP.Outside.L_meta_29931 : ∀ (k r q : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let X := W × (Bool → Fin (r+1) → W)
  let G := Bool × Fin r × Fin k
  let I := Fin k ⊕ G
  let ix := fun s : Nat => (⟨s % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (v : W) (j : Fin k) => v (ix (j.val+k-s % k))
  let start := fun (b : Bool) => if b then 3 else 1
  let feed := fun (b : Bool) (t : Nat) => if b then 3*(t+1)+1 else 2*t
  let mix := fun (b : Bool) (v : W) (j : Fin k) =>
    let d := if b then 2 else 1
    v j + v (ix (j.val+d)) + v (ix (j.val+k-d % k))
  let pair := fun (v z : X) => dotProduct v.1 z.1 +
    ∑ s : Fin (r+1), (dotProduct (v.2 false s) (z.2 false s) + dotProduct (v.2 true s) (z.2 true s))
  let form : I → Fin 3 → X → F := Sum.elim (fun j _ z => z.1 j) (fun g e z =>
    let b := g.1
    let t := g.2.1
    let j := g.2.2
    let y := mix b (z.2 b t.castSucc)
    if e.val = 0 then y (ix (j.val+1)) else if e.val = 1 then y (ix (j.val+2))
    else z.2 b t.succ j + y j + rot (feed b t.val) z.1 j)
  let width := fun (obs : Fin q → X) (cut : I → Bool) =>
    let D := {z : X // (∀ b, z.2 b 0 = rot (start b) z.1) ∧ ∀ i, pair (obs i) z = 0}
    let span := fun (p : I → Bool) => Submodule.span F
      {f : D → F | ∃ (j : I) (e : Fin 3), p j = true ∧ f = fun z : D => form j e z.val}
    Module.finrank F ((span cut ⊓ span (fun j => !(cut j))) : Submodule F (D → F))
  let survive := fun (b : Bool) (steps : Nat) =>
    if 3 ∣ k then k - 2 * min ((if b then 2 else 1)*steps) (2^(k.factorization 2)) else k
  2 ≤ k → ∀ (obs : Fin q → X) (n cap : Nat) (bag : Fin n → I → Bool),
    (∃ top : Fin n, ∀ i, bag top i = true) →
    (∀ v : Fin n, (∃ one : I, ∀ j, bag v j = decide (j = one)) ∨
      ∃ l h : Fin n, l < v ∧ h < v ∧ (∀ j, bag l j = true → bag h j = false) ∧
        ∀ j, bag v j = (bag l j || bag h j)) →
    (∀ v, width obs (bag v) ≤ cap) →
    ∀ (b : Bool) (a m : Nat), 0 < a → 0 < m → a+m ≤ r →
      let seen := fun (u : Fin q) (s : Fin (r+1)) (x : Fin k) =>
        if a ≤ s.val ∧ s.val < a+m then (obs u).2 b s x else 0
      let cost := Module.finrank F (Submodule.span F (Set.range seen))
      let shared := if k = 3 ∨ (b = true ∧ k = 6) then 1 else 2
      min (survive b m) ((2*shared*m+2)/3) ≤ cap + cost := by
  intro k r q hk F W X G I ix rot start feed mix pair form width survive hk2
    obs n cap bag htop htree hcap b a m ha hm ham
  exact PEqualNP.Outside.L_meta_29931.main_proof k r q hk hk2 obs n cap bag
    htop htree hcap b a m ha hm ham
