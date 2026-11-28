import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_29930

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


end PEqualNP.Outside.L_meta_29930

namespace PEqualNP.Outside.L_meta_29930

theorem endpoint_loss_bound {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A B E H : Submodule F V) :
    Module.finrank F ((A ⊔ E) ⊓ (B ⊔ H) : Submodule F V) ≤
      Module.finrank F (A ⊓ B : Submodule F V) + Module.finrank F E + Module.finrank F H := by
  have h₁ := (A ⊔ E).finrank_sup_add_finrank_inf_eq (B ⊔ H)
  have h₂ := A.finrank_sup_add_finrank_inf_eq B
  have h₃ := A.finrank_add_le_finrank_add_finrank E
  have h₄ := B.finrank_add_le_finrank_add_finrank H
  have h₅ := Submodule.finrank_mono (show A ⊔ B ≤ (A ⊔ E) ⊔ (B ⊔ H) from sup_le_sup le_sup_left le_sup_left)
  omega

theorem shared_form {F V U : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup U] [Module F U] (R : V →ₗ[F] U) (A B N M : Submodule F V)
    (hNA : N ≤ A) (hMB : M ≤ B) (hNK : N ≤ R.ker)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (hrel : a-b ∈ N ⊔ M) :
    R a ∈ (A ⊓ B : Submodule F V).map R := by
  obtain ⟨x,hx,y,hy,he⟩ := Submodule.mem_sup.mp hrel
  have eq : a-x = b+y := calc
    a-x = ((a-b)+b)-x := by abel
    _ = (x+y+b)-x := by rw [← he]
    _ = b+y := by abel
  exact ⟨a-x,⟨A.sub_mem ha (hNA hx),eq ▸ B.add_mem hb (hMB hy)⟩,
    by rw [map_sub,show R x=0 from hNK hx,sub_zero]⟩

theorem restriction_cost {F V U Z : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup U] [Module F U] [AddCommGroup Z] [Module F Z] [FiniteDimensional F V]
    (T : V →ₗ[F] U) (O : V →ₗ[F] Z) :
    Module.finrank F T.range ≤ Module.finrank F (T.comp O.ker.subtype).range + Module.finrank F O.range := by
  let T' := T.comp O.ker.subtype
  let inc : T'.ker →ₗ[F] T.ker :=
    { toFun := fun v => ⟨v.val.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective inc := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (Subtype.val : T.ker → V) h))
  have hl := LinearMap.finrank_le_finrank_of_injective hi
  have h₁ := T.finrank_range_add_finrank_ker
  have h₂ := T'.finrank_range_add_finrank_ker
  have h₃ := O.finrank_range_add_finrank_ker
  change Module.finrank F T.range ≤ Module.finrank F T'.range + Module.finrank F O.range
  omega

theorem diagonal_rank {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {I : Type*} [Fintype I] (t : I → V →ₗ[F] V) :
    let T : (I → V) →ₗ[F] (I → V) := LinearMap.pi (fun i => (t i).comp (LinearMap.proj i))
    (∑ i, Module.finrank F (t i).range) = Module.finrank F T.range := by
  classical
  let T : (I → V) →ₗ[F] (I → V) := LinearMap.pi (fun i => (t i).comp (LinearMap.proj i))
  let e : (∀ i, (t i).range) →ₗ[F] T.range :=
    { toFun := fun y => ⟨fun i => (y i).val,fun i => ((y i).property).choose,
        funext (fun i => ((y i).property).choose_spec)⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hi : Function.Injective e := by
    intro a b h
    exact funext (fun i => Subtype.ext (congrFun (congrArg Subtype.val h) i))
  have hs : Function.Surjective e := by
    rintro ⟨_,x,rfl⟩
    exact ⟨fun i => ⟨t i (x i),x i,rfl⟩,rfl⟩
  rw [← Module.finrank_pi_fintype]
  exact (LinearEquiv.ofBijective e ⟨hi,hs⟩).finrank_eq

end PEqualNP.Outside.L_meta_29930

namespace PEqualNP.Outside.L_meta_29930
open Finset
abbrev Bit := ZMod 2
abbrev Word (k : ℕ) := Fin k → Bit
abbrev Tape (r k : ℕ) := Bool → Fin (r+1) → Word k
abbrev Packet (r k : ℕ) := Word k × Tape r k
abbrev Gate (r k : ℕ) := Fin k ⊕ (Bool × Fin r × Fin k)

def active {n r : ℕ} (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (b : Bool) (s : Fin (r+1)) (i : Fin n) := bank i=b ∧ (lo i).val≤s.val ∧ s.val≤(hi i).val

def seed {n r k : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (x : Fin n → Word k) : Tape r k := fun b s =>
  ∑ i, if bank i=b ∧ (lo i).val≤s.val ∧ s.val≤(hi i).val
    then ((mixLin hk b)^(s.val-(lo i).val)) (x i) else 0

theorem seed_when {n r k : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (disj : ∀ i j,i≠j → bank i=bank j → hi i<lo j ∨ hi j<lo i)
    (x : Fin n → Word k) (i : Fin n) (s : Fin (r+1))
    (hl : (lo i).val≤s.val) (hh : s.val≤(hi i).val) :
    seed hk bank lo hi x (bank i) s = ((mixLin hk (bank i))^(s.val-(lo i).val)) (x i) := by
  unfold seed
  rw [Finset.sum_eq_single i]
  · simp [hl,hh]
  · intro j _ hji
    split
    next h =>
      obtain hsep | hsep := disj j i hji h.1
      · have := h.2.2
        change (hi j).val<(lo i).val at hsep
        omega
      · have := h.2.1
        change (hi i).val<(lo j).val at hsep
        omega
    next => rfl
  · simp

theorem seed_absent {n r k : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (x : Fin n → Word k) (b : Bool) (s : Fin (r+1)) (h : ¬∃ i, active bank lo hi b s i) :
    seed hk bank lo hi x b s=0 := by
  unfold seed
  apply Finset.sum_eq_zero
  intro i _
  exact if_neg (fun hh => h ⟨i,hh⟩)

def seedMap {n r k : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r) :
    (Fin n → Word k) →ₗ[Bit] Tape r k where
  toFun := seed hk bank lo hi
  map_add' x y := by
    funext b s
    simp only [seed,Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp
  map_smul' c x := by
    funext b s
    simp only [seed,Pi.smul_apply,RingHom.id_apply,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    split <;> simp

noncomputable def masked {n r k q : ℕ} (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (obs : Fin q → Packet r k) (u : Fin q) (b : Bool) (s : Fin (r+1)) (j : Fin k) : Bit :=
  if ∃ i, bank i=b ∧ (lo i).val≤s.val ∧ s.val≤(hi i).val then (obs u).2 b s j else 0

def bilinear {r k : ℕ} (v z : Tape r k) : Bit :=
  ∑ s, (dotProduct (v false s) (z false s) + dotProduct (v true s) (z true s))

theorem pair_seed {n r k q : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (obs : Fin q → Packet r k) (u : Fin q) (v : Fin n → Word k) :
    pair (obs u) (0,seed hk bank lo hi v) = bilinear (masked bank lo hi obs u) (seed hk bank lo hi v) := by
  simp only [pair,dotProduct_zero,zero_add,bilinear]
  apply Finset.sum_congr rfl
  intro s _
  have eq (b : Bool) : dotProduct ((obs u).2 b s) (seed hk bank lo hi v b s) =
      dotProduct (masked bank lo hi obs u b s) (seed hk bank lo hi v b s) := by
    by_cases h : ∃ i, bank i=b ∧ (lo i).val≤s.val ∧ s.val≤(hi i).val
    · have he : masked bank lo hi obs u b s=(obs u).2 b s := by
        funext j
        simp [masked,h]
      rw [he]
    · rw [seed_absent hk bank lo hi v b s h]
      simp
  rw [eq false,eq true]

def pairMap {r k : ℕ} : Tape r k →ₗ[Bit] (Tape r k →ₗ[Bit] Bit) where
  toFun z :=
    { toFun := fun v => bilinear v z
      map_add' v w := by simp [bilinear,add_dotProduct,Finset.sum_add_distrib,add_add_add_comm]
      map_smul' c v := by simp [bilinear,smul_dotProduct,Finset.mul_sum,mul_add,smul_eq_mul] }
  map_add' z w := by
    ext v
    simp [bilinear,dotProduct_add,Finset.sum_add_distrib,add_add_add_comm]
  map_smul' c z := by
    ext v
    simp [bilinear,dotProduct_smul,Finset.mul_sum,mul_add,smul_eq_mul]

noncomputable def seenSpace {n r k q : ℕ} (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (obs : Fin q → Packet r k) := Submodule.span Bit (Set.range (masked bank lo hi obs))

noncomputable def observer {n r k q : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (obs : Fin q → Packet r k) :
    (Fin n → Word k) →ₗ[Bit] (seenSpace bank lo hi obs →ₗ[Bit] Bit) :=
  ((LinearMap.lcomp Bit Bit (seenSpace bank lo hi obs).subtype) ∘ₗ pairMap) ∘ₗ seedMap hk bank lo hi

theorem goodSeed {n r k q : ℕ} (hk : 0<k) (bank : Fin n → Bool) (lo hi : Fin n → Fin r)
    (obs : Fin q → Packet r k) (pos : ∀ i,0<(lo i).val)
    (x : (observer hk bank lo hi obs).ker) :
    (∀ b, seed hk bank lo hi x.val b 0 = rot hk (start b) 0) ∧
      ∀ i, pair (obs i) (0,seed hk bank lo hi x.val)=0 := by
  constructor
  · intro b
    rw [seed_absent]
    · rfl
    · rintro ⟨i,_,hi,_⟩
      have := pos i
      simp at hi
      omega
  · intro u
    rw [pair_seed]
    exact DFunLike.congr_fun (show observer hk bank lo hi obs x.val=0 from x.property)
      (⟨masked bank lo hi obs u,Submodule.subset_span ⟨u,rfl⟩⟩ : seenSpace bank lo hi obs)

end PEqualNP.Outside.L_meta_29930

namespace PEqualNP.Outside.L_meta_29930
open Finset

def visible {r k : ℕ} (hk : 0<k) (cut : Gate r k → Bool) (b : Bool) (t : Fin r) (c : Bool)
    (x : Fin k) := ∃ j : Fin k, cut (.inr (b,t,j))=c ∧ (ix hk (j.val+1)=x ∨ ix hk (j.val+2)=x)

noncomputable def misses {r k : ℕ} (hk : 0<k) (cut : Gate r k → Bool) (b : Bool) (t : Fin r)
    (c : Bool) : Finset (Fin k) := by classical exact univ.filter (fun x => ¬visible hk cut b t c x)

def sideCut {r k : ℕ} (cut : Gate r k → Bool) (c : Bool) (j : Gate r k) :=
  if c then cut j else !(cut j)

theorem in_side {r k : ℕ} (cut : Gate r k → Bool) (c : Bool) (j : Gate r k) :
    sideCut cut c j=true ↔ cut j=c := by cases c <;> simp [sideCut]

def endpoint {n r : ℕ} (lo hi : Fin n → Fin r) (color : Fin n → Bool) (c : Bool) (i : Fin n) :=
  if color i=c then lo i else hi i

def mixedCoord {r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k) (b : Bool) (t : Fin r) (j : Fin k)
    (z : DSub hk obs) := mix hk b (z.val.2 b t.castSucc) j

noncomputable def extra {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r) (c : Bool) :=
  Submodule.span Bit (Set.range (fun p : Σ i : Fin n,
      {j : Fin k // j ∈ misses hk cut (bank i) (endpoint lo hi color c i) c} =>
    mixedCoord hk obs (bank p.1) (endpoint lo hi color c p.1) p.2.val))

noncomputable def sideSpace {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r) (c : Bool) :=
  spanD hk obs (sideCut cut c) ⊔ extra hk obs cut bank color lo hi c

theorem side_has {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r)
    (c : Bool) (i : Fin n) (j : Fin k) :
    mixedCoord hk obs (bank i) (endpoint lo hi color c i) j ∈ sideSpace hk obs cut bank color lo hi c := by
  classical
  let t := endpoint lo hi color c i
  by_cases hv : visible hk cut (bank i) t c j
  · obtain ⟨h,hcut,hj | hj⟩ := hv
    · apply (show spanD hk obs (sideCut cut c) ≤ sideSpace hk obs cut bank color lo hi c from le_sup_left)
      exact Submodule.subset_span ⟨.inr (bank i,t,h),0,(in_side cut c _).mpr hcut,by rw [← hj]; rfl⟩
    · apply (show spanD hk obs (sideCut cut c) ≤ sideSpace hk obs cut bank color lo hi c from le_sup_left)
      exact Submodule.subset_span ⟨.inr (bank i,t,h),1,(in_side cut c _).mpr hcut,by rw [← hj]; rfl⟩
  · apply (show extra hk obs cut bank color lo hi c ≤ sideSpace hk obs cut bank color lo hi c from le_sup_right)
    exact Submodule.subset_span ⟨⟨i,j,by simpa [misses] using hv⟩,rfl⟩

theorem extra_rank {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r)
    (c : Bool) : Module.finrank Bit (extra hk obs cut bank color lo hi c) ≤
    ∑ i, (misses hk cut (bank i) (endpoint lo hi color c i) c).card := by
  classical
  unfold extra
  apply (finrank_span_le_card _).trans
  rw [Set.toFinset_card]
  apply (Fintype.card_range_le _).trans
  simp

theorem combined_cost {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r) :
    Module.finrank Bit (sideSpace hk obs cut bank color lo hi true ⊓
      sideSpace hk obs cut bank color lo hi false : Submodule Bit _) ≤
    width hk obs cut + ∑ i, ((misses hk cut (bank i) (lo i) (color i)).card +
      (misses hk cut (bank i) (hi i) (!(color i))).card) := by
  classical
  letI : Finite (DSub hk obs) := inferInstanceAs (Finite {z : Packet r k // _})
  have h := endpoint_loss_bound (spanD hk obs (sideCut cut true)) (spanD hk obs (sideCut cut false))
    (extra hk obs cut bank color lo hi true) (extra hk obs cut bank color lo hi false)
  have h₀ := extra_rank hk obs cut bank color lo hi true
  have h₁ := extra_rank hk obs cut bank color lo hi false
  have hsum : (∑ i, (misses hk cut (bank i) (endpoint lo hi color true i) true).card) +
      (∑ i, (misses hk cut (bank i) (endpoint lo hi color false i) false).card) =
      ∑ i, ((misses hk cut (bank i) (lo i) (color i)).card + (misses hk cut (bank i) (hi i) (!(color i))).card) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases he : color i <;> simp [endpoint,he,Nat.add_comm]
  unfold sideSpace
  change _ ≤ Module.finrank Bit (spanD hk obs (sideCut cut true) ⊓ spanD hk obs (sideCut cut false) : Submodule Bit _) + _
  rw [← hsum,← Nat.add_assoc]
  exact h.trans (Nat.add_le_add (Nat.add_le_add_left h₀ _) h₁)

end PEqualNP.Outside.L_meta_29930

namespace PEqualNP.Outside.L_meta_29930
open Finset

def coord {X : Type*} {k : ℕ} (f : X → Word k) (j : Fin k) : X → Bit := fun z => f z j

theorem coord_linear {X : Type*} {k : ℕ} (N : Submodule Bit (X → Bit))
    (L : Word k →ₗ[Bit] Word k) (f : X → Word k) (h : ∀ j, coord f j ∈ N) (j : Fin k) :
    coord (fun z => L (f z)) j ∈ N := by
  classical
  have repr (v : Word k) : v= ∑ x : Fin k, v x • Pi.single x (1:Bit) := by
    funext x
    simp [Finset.sum_apply,Pi.single_apply,Pi.smul_apply,smul_eq_mul,mul_ite]
  have he : coord (fun z => L (f z)) j = ∑ l : Fin k, (L (Pi.single l 1) j) • coord f l := by
    funext z
    change L (f z) j=_
    conv_lhs => rw [repr (f z)]
    simp [Finset.sum_apply,Pi.smul_apply,coord,smul_eq_mul,mul_comm]
  rw [he]
  exact N.sum_mem (fun i _ => N.smul_mem _ (h i))

theorem interval_recurrence {X : Type*} {k r : ℕ} (N : Submodule Bit (X → Bit))
    (L : Word k →ₗ[Bit] Word k) (f : Fin (r+1) → X → Word k) (lo hi : Fin r) (hle : lo≤hi)
    (step : ∀ t : Fin r, lo≤t → t<hi → ∀ j,
      coord (fun z => f t.succ z - L (f t.castSucc z)) j ∈ N) :
    ∀ j,coord (fun z => L (f hi.castSucc z) - (L^(hi.val-lo.val)) (L (f lo.castSucc z))) j ∈ N := by
  have loop (d : ℕ) (hd : lo.val+d ≤ hi.val) (j : Fin k) :
      coord (fun z => f ⟨lo.val+d,by omega⟩ z - (L^d) (f lo.castSucc z)) j ∈ N := by
    induction d generalizing j with
    | zero =>
      convert N.zero_mem using 1
      funext z
      simp [coord]
      exact sub_self _
    | succ d ih =>
      let t : Fin r := ⟨lo.val+d,by omega⟩
      have hs := step t (by change lo.val ≤ lo.val+d; omega) (by change lo.val+d<hi.val; omega) j
      have ht := coord_linear N L (fun z => f t.castSucc z - (L^d) (f lo.castSucc z))
        (fun x => ih (by omega) x) j
      convert N.add_mem hs ht using 1
      funext z
      simp only [coord,Pi.add_apply,Pi.sub_apply,map_sub,pow_succ',Module.End.mul_apply]
      change _ = (f ⟨lo.val+(d+1),_⟩ z j - L (f t.castSucc z) j) + _
      abel
  have hsum : lo.val+(hi.val-lo.val)=hi.val := by change lo.val≤hi.val at hle; omega
  have h (j : Fin k) :
      coord (fun z => f hi.castSucc z - (L^(hi.val-lo.val)) (f lo.castSucc z)) j ∈ N := by
    convert loop (hi.val-lo.val) (by omega) j using 1
    have he : (⟨lo.val+(hi.val-lo.val),by omega⟩ : Fin (r+1))=hi.castSucc := Fin.ext hsum
    rw [he]
  intro j
  have hh := coord_linear N L _ h j
  convert hh using 1
  funext z
  simp only [coord,map_sub,Pi.sub_apply]
  have he (w : Word k) : L ((L^(hi.val-lo.val)) w) = (L^(hi.val-lo.val)) (L w) := by
    change (L * L^(hi.val-lo.val)) w = (L^(hi.val-lo.val) * L) w
    rw [← pow_succ',← pow_succ]
  rw [he]

theorem shadow_bound {K D I : Type} [AddCommGroup K] [Module Bit K] [FiniteDimensional Bit K]
    [Finite D] [Fintype I] (R : (D → Bit) →ₗ[Bit] (K → Bit)) (S : Submodule Bit (D → Bit))
    (T : K →ₗ[Bit] (I → Bit)) (h : ∀ i, (fun x : K => T x i) ∈ S.map R) :
    Module.finrank Bit T.range ≤ Module.finrank Bit S := by
  classical
  let C : (K →ₗ[Bit] Bit) →ₗ[Bit] (K → Bit) :=
    { toFun := fun g x => g x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let U := Submodule.span Bit (Set.range (fun i : I => (LinearMap.proj i).comp T))
  have hc : Function.Injective C := fun g h e => LinearMap.ext (congrFun e)
  have incl : U.map C ≤ S.map R := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i,rfl⟩
    exact h i
  calc
    _ ≤ Module.finrank Bit U := finrank_range_le_of_dual_span T
    _ = Module.finrank Bit (U.map C) := (Submodule.equivMapOfInjective C hc U).finrank_eq
    _ ≤ Module.finrank Bit (S.map R) := Submodule.finrank_mono incl
    _ ≤ _ := Submodule.finrank_map_le R S

end PEqualNP.Outside.L_meta_29930

namespace PEqualNP.Outside.L_meta_29930
open Finset

def readAt {D K : Type*} (p : K → D) : (D → Bit) →ₗ[Bit] (K → Bit) where
  toFun g := fun v => g (p v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem common_ends {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r)
    (order : ∀ i,0<(lo i).val ∧ lo i<hi i)
    (disj : ∀ i j,i≠j → bank i=bank j → hi i<lo j ∨ hi j<lo i) :
    let K := (observer hk bank lo hi obs).ker
    let p (x : K) : DSub hk obs :=
      ⟨(0,seed hk bank lo hi x.val),goodSeed hk bank lo hi obs (fun i => (order i).1) x⟩
    let R := readAt p
    let A := sideSpace hk obs cut bank color lo hi true
    let B := sideSpace hk obs cut bank color lo hi false
    ∀ (i : Fin n) (j : Fin k),
      (fun x : K => ((mixLin hk (bank i))^((hi i).val-(lo i).val+1)) (x.val i) j) ∈
        (A ⊓ B : Submodule Bit _).map R := by
  classical
  dsimp only
  let K := (observer hk bank lo hi obs).ker
  let p (x : K) : DSub hk obs :=
    ⟨(0,seed hk bank lo hi x.val),goodSeed hk bank lo hi obs (fun i => (order i).1) x⟩
  let R := readAt p
  let S := sideSpace hk obs cut bank color lo hi
  let N := ((S true ⊓ R.ker) ⊔ (S false ⊓ R.ker) : Submodule Bit _)
  have nuisance (g : Gate r k) (e : Fin 3) (zero : ∀ x : K,form hk g e (p x).val=0) :
      (fun z : DSub hk obs => form hk g e z.val) ∈ N := by
    let u := fun z : DSub hk obs => form hk g e z.val
    have hs : u ∈ S (cut g) := by
      apply (show spanD hk obs (sideCut cut (cut g)) ≤ S (cut g) from le_sup_left)
      exact Submodule.subset_span ⟨g,e,(in_side cut _ _).mpr rfl,rfl⟩
    have hk₀ : u ∈ R.ker := funext zero
    cases h : cut g
    · exact (show S false ⊓ R.ker ≤ N from le_sup_right) ⟨h ▸ hs,hk₀⟩
    · exact (show S true ⊓ R.ker ≤ N from le_sup_left) ⟨h ▸ hs,hk₀⟩
  intro i j
  let b := bank i
  let M := mixLin hk b
  let d := (hi i).val-(lo i).val
  let f (t : Fin (r+1)) (z : DSub hk obs) := z.val.2 b t
  have lt := (order i).2
  have hz (t : Fin r) (hl : lo i≤t) (ht : t<hi i) (j : Fin k) :
      ∀ x : K,form hk (.inr (b,t,j)) 2 (p x).val = 0 := by
    intro x
    change seed hk bank lo hi x.val b t.succ j + mix hk b (seed hk bank lo hi x.val b t.castSucc) j +
      rot hk (feed b t.val) 0 j = 0
    change (lo i).val≤t.val at hl
    change t.val<(hi i).val at ht
    have e₁ := seed_when hk bank lo hi disj x.val i t.succ (by change _≤t.val+1; omega)
      (by change t.val+1≤_; omega)
    have e₂ := seed_when hk bank lo hi disj x.val i t.castSucc hl ht.le
    change _ + M (seed hk bank lo hi x.val b t.castSucc) j + 0 = 0
    change seed hk bank lo hi x.val (bank i) t.succ j + M (seed hk bank lo hi x.val (bank i) t.castSucc) j + 0 = 0
    rw [e₁,e₂]
    have eq : t.succ.val-(lo i).val=(t.castSucc.val-(lo i).val)+1 := by
      simp only [Fin.val_succ,Fin.val_castSucc]; omega
    rw [eq,pow_succ']
    change _ + _ + 0 = 0
    exact (add_zero _).trans (zmod2_add_self _)
  have step (t : Fin r) (hl : lo i≤t) (ht : t<hi i) (l : Fin k) :
      coord (fun z => f t.succ z - M (f t.castSucc z)) l ∈ N := by
    have hres := nuisance (.inr (b,t,l)) 2 (hz t hl ht l)
    let idx := ix hk (l.val+k-feed b t.val % k)
    have hraw := nuisance (.inl idx) 0 (fun _ => rfl)
    convert N.sub_mem hres hraw using 1
    funext z
    change _ - _ = (f t.succ z l + M (f t.castSucc z) l + z.val.1 idx) - z.val.1 idx
    have char (a b c : Bit) : a-b=a+b+c-c := by revert a b c; decide
    exact char _ _ _
  let a := coord (fun z => M (f (hi i).castSucc z)) j
  let b₀ := coord (fun z => (M^d) (M (f (lo i).castSucc z))) j
  have rel : a-b₀ ∈ N := interval_recurrence N M f _ _ lt.le step j
  have end0 (l : Fin k) : coord (fun z => M (f (lo i).castSucc z)) l ∈ S (color i) := by
    have hh := side_has hk obs cut bank color lo hi (color i) i l
    simp only [endpoint,if_pos rfl] at hh
    exact hh
  have end1 : a ∈ S (!(color i)) := by
    have he : endpoint lo hi color (!(color i)) i=hi i := by cases h : color i <;> simp [endpoint,h]
    have hh := side_has hk obs cut bank color lo hi (!(color i)) i j
    rw [he] at hh
    exact hh
  have end2 : b₀ ∈ S (color i) := coord_linear (S (color i)) (M^d) _ end0 j
  have share : R a ∈ (S true ⊓ S false : Submodule Bit _).map R := by
    cases h : color i
    · apply shared_form R _ _ (S true ⊓ R.ker) (S false ⊓ R.ker) inf_le_left inf_le_left inf_le_right
        (b:=b₀) (by simpa [h] using end1) (by simpa [h] using end2) rel
    · have rev : a-b₀ ∈ ((S false ⊓ R.ker) ⊔ (S true ⊓ R.ker) : Submodule Bit _) := by
        rwa [sup_comm]
      have hrev := shared_form R (S false) (S true) (S false ⊓ R.ker) (S true ⊓ R.ker)
        inf_le_left inf_le_left inf_le_right (a:=a) (b:=b₀)
        (by simpa [h] using end1) (by simpa [h] using end2) rev
      rwa [inf_comm] at hrev
  have rep (x : K) : R a x = ((mixLin hk (bank i))^((hi i).val-(lo i).val+1)) (x.val i) j := by
    change M (seed hk bank lo hi x.val (bank i) (hi i).castSucc) j = _
    rw [seed_when hk bank lo hi disj x.val i (hi i).castSucc lt.le le_rfl,pow_succ']
    rfl
  rwa [show R a = _ from funext rep] at share

end PEqualNP.Outside.L_meta_29930

namespace PEqualNP.Outside.L_meta_29930
open Finset

def flatten (n k : ℕ) : (Fin n → Word k) ≃ₗ[Bit] (Fin n × Fin k → Bit) where
  toFun x := fun j => x j.1 j.2
  invFun y := fun i j => y (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem interval_bound {n r k q : ℕ} (hk : 0<k) (obs : Fin q → Packet r k)
    (cut : Gate r k → Bool) (bank color : Fin n → Bool) (lo hi : Fin n → Fin r)
    (order : ∀ i,0<(lo i).val ∧ lo i<hi i)
    (disj : ∀ i j,i≠j → bank i=bank j → hi i<lo j ∨ hi j<lo i) :
    (∑ i, survive k (bank i) ((hi i).val-(lo i).val+1)) ≤
    width hk obs cut + Module.finrank Bit (seenSpace bank lo hi obs) +
      ∑ i, ((misses hk cut (bank i) (lo i) (color i)).card +
        (misses hk cut (bank i) (hi i) (!(color i))).card) := by
  classical
  let O := observer hk bank lo hi obs
  let M (i : Fin n) := (mixLin hk (bank i))^((hi i).val-(lo i).val+1)
  let T : (Fin n → Word k) →ₗ[Bit] (Fin n → Word k) :=
    LinearMap.pi (fun i => (M i).comp (LinearMap.proj i))
  let U := (flatten n k).toLinearMap.comp T
  let K := O.ker
  let p (x : K) : DSub hk obs :=
    ⟨(0,seed hk bank lo hi x.val),goodSeed hk bank lo hi obs (fun i => (order i).1) x⟩
  let A := sideSpace hk obs cut bank color lo hi true
  let B := sideSpace hk obs cut bank color lo hi false
  letI : Finite (DSub hk obs) := inferInstanceAs (Finite {z : Packet r k // _})
  have lower : (∑ i, survive k (bank i) ((hi i).val-(lo i).val+1)) ≤ Module.finrank Bit T.range := by
    rw [← diagonal_rank M]
    exact Finset.sum_le_sum (fun i _ => survive_le_finrank_range hk _ _)
  have same : Module.finrank Bit U.range = Module.finrank Bit T.range := by
    rw [show U.range=T.range.map (flatten n k).toLinearMap from LinearMap.range_comp _ _]
    exact (flatten n k).finrank_map_eq _
  have ho : Module.finrank Bit O.range ≤ Module.finrank Bit (seenSpace bank lo hi obs) :=
    (Submodule.finrank_le O.range).trans_eq finrank_dual_eq
  have restr := restriction_cost U O
  have shared : Module.finrank Bit (U.comp O.ker.subtype).range ≤ Module.finrank Bit (A ⊓ B : Submodule Bit _) := by
    apply shadow_bound (readAt p) (A ⊓ B)
    rintro ⟨i,j⟩
    exact common_ends hk obs cut bank color lo hi order disj i j
  have bound := combined_cost hk obs cut bank color lo hi
  calc
    _ ≤ Module.finrank Bit U.range := lower.trans_eq same.symm
    _ ≤ _ := restr
    _ ≤ Module.finrank Bit (A ⊓ B : Submodule Bit _) + Module.finrank Bit (seenSpace bank lo hi obs) :=
      Nat.add_le_add shared ho
    _ ≤ _ := by
      have h := Nat.add_le_add_right bound (Module.finrank Bit (seenSpace bank lo hi obs))
      simpa only [Nat.add_right_comm (width hk obs cut)] using h

end PEqualNP.Outside.L_meta_29930

theorem PEqualNP.Outside.L_meta_29930 : (∀ (k r q : Nat) (hk : 0 < k),
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
  ∀ (obs : Fin q → X) (cut : I → Bool) (n : Nat) (bank color : Fin n → Bool)
    (first last : Fin n → Fin r),
    (∀ i, 0 < (first i).val ∧ first i < last i) →
    (∀ i j, i ≠ j → bank i = bank j → last i < first j ∨ last j < first i) →
    let seen := fun (u : Fin q) (b : Bool) (s : Fin (r+1)) (x : Fin k) =>
      if ∃ i, bank i = b ∧ (first i).val ≤ s.val ∧ s.val ≤ (last i).val
      then (obs u).2 b s x else 0
    let cost := Module.finrank F (Submodule.span F (Set.range seen))
    let missed := fun (b : Bool) (t : Fin r) (c : Bool) =>
      ((Finset.univ : Finset (Fin k)).filter (fun x => ¬ ∃ j : Fin k,
        cut (.inr (b,t,j)) = c ∧ (ix (j.val+1) = x ∨ ix (j.val+2) = x))).card
    let loss := ∑ i : Fin n, (missed (bank i) (first i) (color i) +
      missed (bank i) (last i) (!(color i)))
    (∑ i : Fin n, survive (bank i) ((last i).val-(first i).val+1)) ≤ width obs cut + cost + loss) := by
  intro k r q hk F W X G I ix rot start feed mix pair form width survive obs cut n bank color first last order disj
  have hh := PEqualNP.Outside.L_meta_29930.interval_bound hk obs cut bank color first last order disj
  convert hh using 1 <;> congr! 5 <;> ext y <;> simp [PEqualNP.Outside.L_meta_29930.misses, PEqualNP.Outside.L_meta_29930.visible, PEqualNP.Outside.L_meta_29930.ix, ix]
