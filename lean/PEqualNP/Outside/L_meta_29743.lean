import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29743_aux

abbrev F := ZMod 2
abbrev B := Fin 10 → F
abbrev Win := Fin 11 → F
abbrev Rel := Submodule F (B × B)

lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma zmod2_neg_eq (a : F) : -a = a := by
  rw [neg_eq_iff_add_eq_zero]
  exact zmod2_add_self a

def diff {W : Type*} [AddCommGroup W] (f : W → F) (u x : W) : F :=
  f (x + u) - f x

def fourth {W : Type*} [AddCommGroup W] (f : W → F) (v : Fin 4 → W) : W → F :=
  (List.ofFn v).foldl diff f

lemma fourth_eq {W : Type*} [AddCommGroup W] (f : W → F) (v : Fin 4 → W) (x : W) :
    fourth f v x = diff (diff (diff (diff f (v 0)) (v 1)) (v 2)) (v 3) x := by
  simp [fourth, List.ofFn_succ]

lemma diff_eq_add {W : Type*} [AddCommGroup W] (f : W → F) (u x : W) :
    diff f u x = f (x + u) + f x :=
  zmod2_sub_eq_add _ _

lemma diff_const {W : Type*} [AddCommGroup W] (c : F) (u x : W) :
    diff (fun _ : W => c) u x = 0 := by
  simp [diff]

lemma diff_add {W : Type*} [AddCommGroup W] (f g : W → F) (u x : W) :
    diff (fun y => f y + g y) u x = diff f u x + diff g u x := by
  simp only [diff_eq_add]; ring

lemma diff_linear {W : Type*} [AddCommGroup W] [Module F W] (L : W →ₗ[F] F) (u x : W) :
    diff L u x = L u := by
  simp [diff, map_add]

lemma diff_mul {W : Type*} [AddCommGroup W] (f g : W → F) (u x : W) :
    diff (fun y => f y * g y) u x = diff f u x * g (x + u) + f x * diff g u x := by
  simp only [diff_eq_add]
  have h : f x * g (x + u) + f x * g (x + u) = 0 := zmod2_add_self _
  calc f (x + u) * g (x + u) + f x * g x
      = f (x + u) * g (x + u) + (f x * g (x + u) + f x * g (x + u)) + f x * g x := by
        rw [h, add_zero]
    _ = (f (x + u) + f x) * g (x + u) + f x * (g (x + u) + g x) := by ring

lemma second_mul_affine {W : Type*} [AddCommGroup W] [Module F W]
    (L₁ L₂ : W →ₗ[F] F) (c₁ c₂ : F) (u w x : W) :
    diff (diff (fun y => (L₁ y + c₁) * (L₂ y + c₂)) u) w x = L₁ u * L₂ w + L₁ w * L₂ u := by
  simp only [diff_eq_add, map_add]
  have h2 : (2 : F) = 0 := by decide
  have h4 : (4 : F) = 0 := by decide
  ring_nf
  simp [h2, h4]

lemma fourth_add {W : Type*} [AddCommGroup W] (f g : W → F) (v : Fin 4 → W) (x : W) :
    fourth (fun y => f y + g y) v x = fourth f v x + fourth g v x := by
  simp only [fourth_eq]
  have h1 : diff (fun y => f y + g y) (v 0) = fun y => diff f (v 0) y + diff g (v 0) y :=
    funext (diff_add f g (v 0))
  rw [h1]
  have h2 : diff (fun y => diff f (v 0) y + diff g (v 0) y) (v 1) =
      fun y => diff (diff f (v 0)) (v 1) y + diff (diff g (v 0)) (v 1) y :=
    funext (diff_add _ _ (v 1))
  rw [h2]
  have h3 : diff (fun y => diff (diff f (v 0)) (v 1) y + diff (diff g (v 0)) (v 1) y) (v 2) =
      fun y => diff (diff (diff f (v 0)) (v 1)) (v 2) y + diff (diff (diff g (v 0)) (v 1)) (v 2) y :=
    funext (diff_add _ _ (v 2))
  rw [h3]
  exact diff_add _ _ (v 3) x

lemma fourth_const {W : Type*} [AddCommGroup W] (c : F) (v : Fin 4 → W) (x : W) :
    fourth (fun _ => c) v x = 0 := by
  simp only [fourth_eq]
  have h1 : diff (fun _ : W => c) (v 0) = fun _ => 0 := funext (diff_const c (v 0))
  rw [h1]
  have h2 : diff (fun _ : W => (0 : F)) (v 1) = fun _ => 0 := funext (diff_const 0 (v 1))
  rw [h2]
  have h3 : diff (fun _ : W => (0 : F)) (v 2) = fun _ => 0 := funext (diff_const 0 (v 2))
  rw [h3]
  exact diff_const 0 (v 3) x

lemma fourth_of_second_const {W : Type*} [AddCommGroup W] (q : W → F) (B0 : W → W → F)
    (hq : ∀ u w x, diff (diff q u) w x = B0 u w) (v : Fin 4 → W) (x : W) :
    fourth q v x = 0 := by
  simp only [fourth_eq]
  have h1 : diff (diff q (v 0)) (v 1) = fun _ => B0 (v 0) (v 1) := funext (hq (v 0) (v 1))
  rw [h1]
  have h2 : diff (fun _ : W => B0 (v 0) (v 1)) (v 2) = fun _ => 0 := funext (diff_const _ (v 2))
  rw [h2]
  exact diff_const 0 (v 3) x

lemma fourth_linear {W : Type*} [AddCommGroup W] [Module F W] (L : W →ₗ[F] F)
    (v : Fin 4 → W) (x : W) : fourth L v x = 0 :=
  fourth_of_second_const L (fun _ _ => 0) (fun u w x => by
    have : diff L u = fun _ => L u := funext (diff_linear L u)
    rw [this, diff_const]) v x

lemma quad_eval_shift {W : Type*} [AddCommGroup W] (q : W → F) (B0 : W → W → F)
    (hq : ∀ u w x, diff (diff q u) w x = B0 u w) :
    ∀ u x, q (x + u) = q x + diff q u x := by
  intro u x
  rw [diff_eq_add]
  have h := zmod2_add_self (q x)
  calc q (x + u) = q (x + u) + (q x + q x) := by rw [h, add_zero]
    _ = q x + (q (x + u) + q x) := by ring

lemma diff_quad_shift {W : Type*} [AddCommGroup W] (q : W → F) (B0 : W → W → F)
    (hq : ∀ u w x, diff (diff q u) w x = B0 u w) :
    ∀ u w x, diff q u (x + w) = diff q u x + B0 u w := by
  intro u w x
  have h := hq u w x
  rw [diff_eq_add] at h
  have hs := zmod2_add_self (diff q u x)
  calc diff q u (x + w) = (diff q u (x + w) + diff q u x) + diff q u x := by
        calc diff q u (x + w) = diff q u (x + w) + (diff q u x + diff q u x) := by rw [hs, add_zero]
          _ = (diff q u (x + w) + diff q u x) + diff q u x := by ring
    _ = B0 u w + diff q u x := by rw [h]
    _ = diff q u x + B0 u w := by ring

lemma quad_sum2 {W : Type*} [AddCommGroup W] (q : W → F) (B0 : W → W → F)
    (hq : ∀ u w x, diff (diff q u) w x = B0 u w) (u w x : W) :
    q (x + u + w) = q x + diff q u x + diff q w x + B0 u w := by
  rw [quad_eval_shift q B0 hq w (x + u), quad_eval_shift q B0 hq u x,
      diff_quad_shift q B0 hq w u x]
  have hsym : B0 w u = B0 u w := by
    have h1 := hq w u x
    have h2 := hq u w x
    simp only [diff_eq_add] at h1 h2
    rw [add_right_comm x u w] at h1
    rw [← h1, ← h2]; ring
  rw [hsym]; ring

lemma quad_sum3 {W : Type*} [AddCommGroup W] (q : W → F) (B0 : W → W → F)
    (hq : ∀ u w x, diff (diff q u) w x = B0 u w) (u w z x : W) :
    q (x + u + w + z) =
      q x + diff q u x + diff q w x + diff q z x + B0 u w + B0 u z + B0 w z := by
  rw [quad_eval_shift q B0 hq z (x + u + w), quad_sum2 q B0 hq u w x,
      diff_quad_shift q B0 hq z w (x + u), diff_quad_shift q B0 hq z u x]
  have hsym : ∀ a b, B0 b a = B0 a b := fun a b => by
    have h1 := hq b a x; have h2 := hq a b x
    simp only [diff_eq_add] at h1 h2
    rw [add_right_comm x a b] at h1; rw [← h1, ← h2]; ring
  rw [hsym u z, hsym w z]; ring

lemma quad_sum4 {W : Type*} [AddCommGroup W] (q : W → F) (B0 : W → W → F)
    (hq : ∀ u w x, diff (diff q u) w x = B0 u w) (a b c d x : W) :
    q (x + a + b + c + d) =
      q x + diff q a x + diff q b x + diff q c x + diff q d x +
      B0 a b + B0 a c + B0 a d + B0 b c + B0 b d + B0 c d := by
  rw [quad_eval_shift q B0 hq d (x + a + b + c), quad_sum3 q B0 hq a b c x,
      diff_quad_shift q B0 hq d c (x + a + b), diff_quad_shift q B0 hq d b (x + a),
      diff_quad_shift q B0 hq d a x]
  have hsym : ∀ u w, B0 w u = B0 u w := fun u w => by
    have h1 := hq w u x; have h2 := hq u w x
    simp only [diff_eq_add] at h1 h2
    rw [add_right_comm x u w] at h1; rw [← h1, ← h2]; ring
  rw [hsym a d, hsym b d, hsym c d]; ring

lemma fourth_expand {W : Type*} [AddCommGroup W] (f : W → F) (v : Fin 4 → W) (x : W) :
    fourth f v x =
      f (x + v 0 + v 1 + v 2 + v 3) +
      f (x + v 0 + v 1 + v 2) + f (x + v 0 + v 1 + v 3) +
      f (x + v 0 + v 2 + v 3) + f (x + v 1 + v 2 + v 3) +
      f (x + v 0 + v 1) + f (x + v 0 + v 2) + f (x + v 0 + v 3) +
      f (x + v 1 + v 2) + f (x + v 1 + v 3) + f (x + v 2 + v 3) +
      f (x + v 0) + f (x + v 1) + f (x + v 2) + f (x + v 3) + f x := by
  simp only [fourth_eq, diff_eq_add]
  have e1 : x + v 3 + v 2 + v 1 + v 0 = x + v 0 + v 1 + v 2 + v 3 := by abel
  have e2 : x + v 3 + v 2 + v 1 = x + v 1 + v 2 + v 3 := by abel
  have e3 : x + v 3 + v 2 + v 0 = x + v 0 + v 2 + v 3 := by abel
  have e4 : x + v 3 + v 1 + v 0 = x + v 0 + v 1 + v 3 := by abel
  have e5 : x + v 2 + v 1 + v 0 = x + v 0 + v 1 + v 2 := by abel
  have e6 : x + v 3 + v 2 = x + v 2 + v 3 := by abel
  have e7 : x + v 3 + v 1 = x + v 1 + v 3 := by abel
  have e8 : x + v 3 + v 0 = x + v 0 + v 3 := by abel
  have e9 : x + v 2 + v 1 = x + v 1 + v 2 := by abel
  have e10 : x + v 2 + v 0 = x + v 0 + v 2 := by abel
  have e11 : x + v 1 + v 0 = x + v 0 + v 1 := by abel
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  ring

lemma diff_const_mul {W : Type*} [AddCommGroup W] (c : F) (f : W → F) (u x : W) :
    diff (fun y => c * f y) u x = c * diff f u x := by
  simp only [diff_eq_add]; ring

lemma diff_mul_const {W : Type*} [AddCommGroup W] (f : W → F) (c : F) (u x : W) :
    diff (fun y => f y * c) u x = diff f u x * c := by
  simp only [diff_eq_add]; ring

lemma diff_shift {W : Type*} [AddCommGroup W] (f : W → F) (s u x : W) :
    diff (fun y => f (y + s)) u x = diff f u (x + s) := by
  simp only [diff_eq_add, add_right_comm]

lemma second_mul_quad {W : Type*} [AddCommGroup W]
    (q₁ q₂ : W → F) (B₁ B₂ : W → W → F)
    (h₁ : ∀ u w x, diff (diff q₁ u) w x = B₁ u w)
    (h₂ : ∀ u w x, diff (diff q₂ u) w x = B₂ u w) (a b x : W) :
    diff (diff (fun y => q₁ y * q₂ y) a) b x =
      B₁ a b * q₂ (x + b + a) + diff q₁ a x * diff q₂ b (x + a) +
      diff q₁ b x * diff q₂ a (x + b) + q₁ x * B₂ a b := by
  have hd1 : diff (fun y => q₁ y * q₂ y) a =
      fun y => diff q₁ a y * q₂ (y + a) + q₁ y * diff q₂ a y :=
    funext (diff_mul q₁ q₂ a)
  rw [hd1, diff_add, diff_mul, diff_mul, h₁ a b x, h₂ a b x, diff_shift q₂ a b x]
  rw [diff_quad_shift q₂ B₂ h₂ a b x]
  ring

lemma third_mul_quad {W : Type*} [AddCommGroup W]
    (q₁ q₂ : W → F) (B₁ B₂ : W → W → F)
    (h₁ : ∀ u w x, diff (diff q₁ u) w x = B₁ u w)
    (h₂ : ∀ u w x, diff (diff q₂ u) w x = B₂ u w) (a b c x : W) :
    diff (diff (diff (fun y => q₁ y * q₂ y) a) b) c x =
      B₁ a b * diff q₂ c (x + b + a) + B₁ a c * diff q₂ b (x + c + a) +
      diff q₁ a x * B₂ b c + B₁ b c * diff q₂ a (x + c + b) +
      diff q₁ b x * B₂ a c + diff q₁ c x * B₂ a b := by
  have hd2 : diff (diff (fun y => q₁ y * q₂ y) a) b =
      fun y => (B₁ a b * q₂ (y + b + a) + diff q₁ a y * diff q₂ b (y + a)) +
               (diff q₁ b y * diff q₂ a (y + b) + q₁ y * B₂ a b) := by
    funext y; rw [second_mul_quad q₁ q₂ B₁ B₂ h₁ h₂ a b y]; ring
  rw [hd2, diff_add, diff_add, diff_add, diff_const_mul, diff_mul_const]
  rw [diff_mul, diff_mul, h₁ a c x, h₁ b c x]
  have hs1 : diff (fun y => q₂ (y + b + a)) c x = diff q₂ c (x + b + a) := by
    simp only [diff_eq_add]; congr 1; congr 1; abel
  have hs2 : diff (fun y => diff q₂ b (y + a)) c x = B₂ b c := by
    rw [diff_shift, h₂ b c (x + a)]
  have hs3 : diff (fun y => diff q₂ a (y + b)) c x = B₂ a c := by
    rw [diff_shift, h₂ a c (x + b)]
  rw [hs1, hs2, hs3]
  ring

lemma fourth_mul_of_quad {W : Type*} [AddCommGroup W]
    (q₁ q₂ : W → F) (B₁ B₂ : W → W → F)
    (h₁ : ∀ u w x, diff (diff q₁ u) w x = B₁ u w)
    (h₂ : ∀ u w x, diff (diff q₂ u) w x = B₂ u w)
    (v : Fin 4 → W) (x : W) :
    fourth (fun y => q₁ y * q₂ y) v x =
      B₁ (v 0) (v 1) * B₂ (v 2) (v 3) + B₁ (v 0) (v 2) * B₂ (v 1) (v 3) +
      B₁ (v 0) (v 3) * B₂ (v 1) (v 2) + B₁ (v 1) (v 2) * B₂ (v 0) (v 3) +
      B₁ (v 1) (v 3) * B₂ (v 0) (v 2) + B₁ (v 2) (v 3) * B₂ (v 0) (v 1) := by
  rw [fourth_eq]
  have hd3 : diff (diff (diff (fun y => q₁ y * q₂ y) (v 0)) (v 1)) (v 2) =
      fun y =>
        ((B₁ (v 0) (v 1) * diff q₂ (v 2) (y + v 1 + v 0) +
          B₁ (v 0) (v 2) * diff q₂ (v 1) (y + v 2 + v 0)) +
         (diff q₁ (v 0) y * B₂ (v 1) (v 2) +
          B₁ (v 1) (v 2) * diff q₂ (v 0) (y + v 2 + v 1))) +
        (diff q₁ (v 1) y * B₂ (v 0) (v 2) + diff q₁ (v 2) y * B₂ (v 0) (v 1)) := by
    funext y; rw [third_mul_quad q₁ q₂ B₁ B₂ h₁ h₂ (v 0) (v 1) (v 2) y]; ring
  rw [hd3, diff_add, diff_add, diff_add, diff_add, diff_add]
  rw [diff_const_mul, diff_const_mul, diff_mul_const, diff_const_mul, diff_mul_const, diff_mul_const]
  have hs : ∀ p q r s : W, diff (fun y => diff q₂ p (y + q + r)) s x = B₂ p s := by
    intro p q r s
    have : (fun y => diff q₂ p (y + q + r)) = fun y => diff q₂ p (y + (q + r)) := by
      funext y; congr 1; abel
    rw [this, diff_shift, h₂ p s (x + (q + r))]
  rw [hs, hs, hs, h₁, h₁, h₁]
  ring

lemma diff_comp_affine {W : Type*} [AddCommGroup W] [Module F W]
    (f : W → F) (π : W →ₗ[F] W) (a u x : W) :
    diff (fun y => f (a + π (y - a))) u x = diff f (π u) (a + π (x - a)) := by
  simp only [diff]
  have h : a + π (x + u - a) = (a + π (x - a)) + π u := by
    have : x + u - a = (x - a) + u := by abel
    rw [this, map_add, add_assoc]
  rw [h]

lemma fourth_comp_affine {W : Type*} [AddCommGroup W] [Module F W]
    (f : W → F) (π : W →ₗ[F] W) (a : W) (v : Fin 4 → W) (x : W) :
    fourth (fun y => f (a + π (y - a))) v x =
      fourth f (fun r => π (v r)) (a + π (x - a)) := by
  simp only [fourth_eq]
  have h1 : diff (fun y => f (a + π (y - a))) (v 0) =
      fun y => diff f (π (v 0)) (a + π (y - a)) := funext (diff_comp_affine f π a (v 0))
  rw [h1]
  have h2 : diff (fun y => diff f (π (v 0)) (a + π (y - a))) (v 1) =
      fun y => diff (diff f (π (v 0))) (π (v 1)) (a + π (y - a)) :=
    funext (diff_comp_affine _ π a (v 1))
  rw [h2]
  have h3 : diff (fun y => diff (diff f (π (v 0))) (π (v 1)) (a + π (y - a))) (v 2) =
      fun y => diff (diff (diff f (π (v 0))) (π (v 1))) (π (v 2)) (a + π (y - a)) :=
    funext (diff_comp_affine _ π a (v 2))
  rw [h3]
  exact diff_comp_affine _ π a (v 3) x

def shiftIdx (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨(n + 5 * k - 5) % k, Nat.mod_lt _ hk⟩

lemma shiftIdx_add_five (k : ℕ) (hk : 0 < k) (n : ℕ) :
    shiftIdx k hk (n + 5) = ⟨n % k, Nat.mod_lt _ hk⟩ := by
  ext
  simp only [shiftIdx]
  have h5 : n + 5 + 5 * k - 5 = n + k * 5 := by omega
  rw [h5, Nat.add_mul_mod_self_left]

lemma shiftIdx_eq_ix_add_sub (k : ℕ) (hk : 0 < k) (i a s : ℕ) (hs : s ≤ 5) :
    (⟨((i + a) % k + k - s % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i + a + 5 - s) := by
  ext
  simp only [shiftIdx]
  have hsm : s % k ≤ k := le_of_lt (Nat.mod_lt s hk)
  have h1 : (i + a) % k + k - s % k + s % k = (i + a) % k + k := by omega
  have h2 : i + a + 5 - s + 5 * k - 5 + s = i + a + 5 * k := by omega

  have hmod : (((i + a) % k + k - s % k) + s) % k = (i + a) % k := by
    have hq : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
    have hmul : k * (s / k + 1) = k * (s / k) + k := by ring
    have h3 : (i + a) % k + k - s % k + s = (i + a) % k + k * (s / k + 1) := by omega
    rw [h3, Nat.add_mul_mod_self_left, Nat.mod_mod]
  have hmod2 : ((i + a + 5 - s + 5 * k - 5) + s) % k = (i + a) % k := by
    rw [h2, show 5 * k = k * 5 by ring, Nat.add_mul_mod_self_left]

  set x := (i + a) % k + k - s % k
  set y := i + a + 5 - s + 5 * k - 5
  have hxy : (x % k + s % k) % k = (y % k + s % k) % k := by
    rw [← Nat.add_mod, ← Nat.add_mod, hmod, hmod2]
  have hx : x % k < k := Nat.mod_lt x hk
  have hy : y % k < k := Nat.mod_lt y hk
  have hs' : s % k < k := Nat.mod_lt s hk
  by_cases hxs : x % k + s % k < k <;> by_cases hys : y % k + s % k < k
  · rw [Nat.mod_eq_of_lt hxs, Nat.mod_eq_of_lt hys] at hxy; omega
  · rw [Nat.mod_eq_of_lt hxs] at hxy
    have hsub : (y % k + s % k) % k = y % k + s % k - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hxy; omega
  · rw [Nat.mod_eq_of_lt hys] at hxy
    have hsub : (x % k + s % k) % k = x % k + s % k - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub] at hxy; omega
  · have hsub1 : (x % k + s % k) % k = x % k + s % k - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hsub2 : (y % k + s % k) % k = y % k + s % k - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hsub1, hsub2] at hxy; omega

def win (k : ℕ) (hk : 0 < k) (i : Fin k) : (Fin k → F) →ₗ[F] Win where
  toFun x t := x (shiftIdx k hk (i.val + t.val))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def locLFalse (m : Fin 6) (w : Win) : F :=
  w ⟨m.val + 4, by omega⟩ + w ⟨m.val + 5, by omega⟩ + w ⟨m.val + 3, by omega⟩

def locLTrue (m : Fin 7) (w : Win) : F :=
  w ⟨m.val + 2, by omega⟩ + w ⟨m.val + 4, by omega⟩ + w ⟨m.val, by omega⟩

def locStepBFalse (j : Fin 4) (u w : Win) : F :=
  locLFalse ⟨j.val + 1, by omega⟩ u * locLFalse ⟨j.val + 2, by omega⟩ w +
  locLFalse ⟨j.val + 1, by omega⟩ w * locLFalse ⟨j.val + 2, by omega⟩ u

def locStepBTrue (j : Fin 6) (u w : Win) : F :=
  locLTrue ⟨j.val, by omega⟩ u * locLTrue ⟨j.val + 1, by omega⟩ w +
  locLTrue ⟨j.val, by omega⟩ w * locLTrue ⟨j.val + 1, by omega⟩ u

def locB (b side : Bool) (u w : Win) : F :=
  match b, side with
  | false, false =>

      locStepBFalse 1 u w + locStepBFalse 2 u w + locStepBFalse 0 u w
  | false, true =>

      locStepBFalse 2 u w + locStepBFalse 3 u w + locStepBFalse 1 u w
  | true, false =>

      locStepBTrue 2 u w + locStepBTrue 4 u w + locStepBTrue 0 u w
  | true, true =>

      locStepBTrue 3 u w + locStepBTrue 5 u w + locStepBTrue 1 u w

def locQ4 (b : Bool) (v : Fin 4 → Win) : F :=
  locB b false (v 0) (v 1) * locB b true (v 2) (v 3) +
  locB b false (v 0) (v 2) * locB b true (v 1) (v 3) +
  locB b false (v 0) (v 3) * locB b true (v 1) (v 2) +
  locB b false (v 1) (v 2) * locB b true (v 0) (v 3) +
  locB b false (v 1) (v 3) * locB b true (v 0) (v 2) +
  locB b false (v 2) (v 3) * locB b true (v 0) (v 1)

def ixF (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rotF (k : ℕ) (hk : 0 < k) (s : ℕ) (x : Fin k → F) (i : Fin k) : F :=
  x (ixF k hk (i.val + k - s % k))

def mixF (k : ℕ) (hk : 0 < k) (g : ℕ) (x : Fin k → F) (i : Fin k) : F :=
  x i + x (ixF k hk (i.val + g)) + x (ixF k hk (i.val + k - g % k))

def stepF (k : ℕ) (hk : 0 < k) (x : Fin k → F) (i : Fin k) : F :=
  x i + (1 + x (ixF k hk (i.val + 1))) * x (ixF k hk (i.val + 2))

def outF (k : ℕ) (hk : 0 < k) (name c₁ c₂ : Bool → Fin k → F)
    (x : Fin k → F) (b : Bool) : Fin k → F :=
  let gap := if b then 2 else (1 : ℕ)
  let spin := if b then 3 else (1 : ℕ)
  let z := mixF k hk gap (rotF k hk spin x + name b)
  let y := stepF k hk z + rotF k hk (if b then 4 else 0) x + c₁ b
  stepF k hk (mixF k hk gap y) + rotF k hk (if b then 7 else 2) x + c₂ b

def mixRotLin (k : ℕ) (hk : 0 < k) (g s : ℕ) (j : Fin k) : (Fin k → F) →ₗ[F] F where
  toFun x := mixF k hk g (rotF k hk s x) j
  map_add' x y := by simp only [mixF, rotF, Pi.add_apply]; ring
  map_smul' c x := by simp only [mixF, rotF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def rotLin (k : ℕ) (hk : 0 < k) (s : ℕ) (j : Fin k) : (Fin k → F) →ₗ[F] F where
  toFun x := rotF k hk s x j
  map_add' x y := by simp only [rotF, Pi.add_apply]
  map_smul' c x := by simp only [rotF, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

lemma second_stepF (k : ℕ) (hk : 0 < k) (g s r : ℕ) (nm cc : Fin k → F) (j : Fin k) :
    ∀ u w x : Fin k → F,
      diff (diff (fun y : Fin k → F =>
        stepF k hk (mixF k hk g (rotF k hk s y + nm)) j + rotF k hk r y j + cc j) u) w x =
      mixRotLin k hk g s (ixF k hk (j.val + 1)) u * mixRotLin k hk g s (ixF k hk (j.val + 2)) w +
      mixRotLin k hk g s (ixF k hk (j.val + 1)) w * mixRotLin k hk g s (ixF k hk (j.val + 2)) u := by
  intro u w x
  set L0 := mixRotLin k hk g s j
  set L1 := mixRotLin k hk g s (ixF k hk (j.val + 1))
  set L2 := mixRotLin k hk g s (ixF k hk (j.val + 2))
  set Lr := rotLin k hk r j
  set d0 := mixF k hk g nm j
  set d1 := mixF k hk g nm (ixF k hk (j.val + 1))
  set d2 := mixF k hk g nm (ixF k hk (j.val + 2))
  have hfun : (fun y : Fin k → F =>
      stepF k hk (mixF k hk g (rotF k hk s y + nm)) j + rotF k hk r y j + cc j) =
      (fun y => (L0 y + Lr y + (d0 + cc j)) + (L1 y + (1 + d1)) * (L2 y + d2)) := by
    funext y
    have hm : ∀ p, mixF k hk g (rotF k hk s y + nm) p = mixRotLin k hk g s p y + mixF k hk g nm p := by
      intro p; simp only [mixF, mixRotLin, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]; ring
    simp only [stepF, hm, L0, L1, L2, Lr, d0, d1, d2]
    change (mixRotLin k hk g s j y + mixF k hk g nm j +
      (1 + (mixRotLin k hk g s (ixF k hk (j.val + 1)) y + mixF k hk g nm (ixF k hk (j.val + 1)))) *
        (mixRotLin k hk g s (ixF k hk (j.val + 2)) y + mixF k hk g nm (ixF k hk (j.val + 2)))) +
      rotF k hk r y j + cc j =
      (mixRotLin k hk g s j y + rotF k hk r y j + (mixF k hk g nm j + cc j)) +
      (mixRotLin k hk g s (ixF k hk (j.val + 1)) y + (1 + mixF k hk g nm (ixF k hk (j.val + 1)))) *
      (mixRotLin k hk g s (ixF k hk (j.val + 2)) y + mixF k hk g nm (ixF k hk (j.val + 2)))
    ring
  rw [hfun]
  have hlin : ∀ a b c : Fin k → F,
      diff (diff (fun y => L0 y + Lr y + (d0 + cc j)) a) b c = 0 := by
    intro a b c
    have h1 : diff (fun y => L0 y + Lr y + (d0 + cc j)) a = fun _ => L0 a + Lr a := by
      funext y; simp only [diff_eq_add, map_add]
      have hz := zmod2_add_self (L0 y + Lr y + (d0 + cc j))
      calc L0 y + L0 a + (Lr y + Lr a) + (d0 + cc j) + (L0 y + Lr y + (d0 + cc j))
          = (L0 a + Lr a) + ((L0 y + Lr y + (d0 + cc j)) + (L0 y + Lr y + (d0 + cc j))) := by ring
        _ = L0 a + Lr a := by rw [hz, add_zero]
    rw [h1, diff_const]
  have hadd1 : diff (fun y => (L0 y + Lr y + (d0 + cc j)) + (L1 y + (1 + d1)) * (L2 y + d2)) u =
      fun y => diff (fun y => L0 y + Lr y + (d0 + cc j)) u y +
               diff (fun y => (L1 y + (1 + d1)) * (L2 y + d2)) u y :=
    funext (diff_add _ _ u)
  rw [hadd1, diff_add, hlin u w x, zero_add]
  exact second_mul_affine L1 L2 (1 + d1) d2 u w x

lemma mod_cancel_add (k : ℕ) (hk : 0 < k) (x y s : ℕ) (h : (x + s) % k = (y + s) % k) :
    x % k = y % k := by
  have hxy : (x % k + s % k) % k = (y % k + s % k) % k := by
    rw [← Nat.add_mod, ← Nat.add_mod, h]
  have hx := Nat.mod_lt x hk
  have hy := Nat.mod_lt y hk
  have hs := Nat.mod_lt s hk
  have hmod : ∀ a b : ℕ, a < k → b < k → (a + b) % k = if a + b < k then a + b else a + b - k := by
    intro a b ha hb
    split_ifs with hab
    · exact Nat.mod_eq_of_lt hab
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hmod (x % k) (s % k) hx hs, hmod (y % k) (s % k) hy hs] at hxy
  split_ifs at hxy <;> omega

lemma mixRotLin_false_eq (k : ℕ) (hk : 0 < k) (i : Fin k) (m : Fin 6) (x : Fin k → F) :
    mixRotLin k hk 1 1 (ixF k hk (i.val + m.val)) x = locLFalse m (win k hk i x) := by
  simp only [mixRotLin, LinearMap.coe_mk, AddHom.coe_mk, mixF, rotF, locLFalse, win, ixF]
  have h1 : (⟨((i.val + m.val) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i.val + (m.val + 4)) := by
    convert shiftIdx_eq_ix_add_sub k hk i.val m.val 1 (by omega) using 2; omega
  have h2 : (⟨(((i.val + m.val) % k + 1) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i.val + (m.val + 5)) := by
    have hm : ((i.val + m.val) % k + 1) % k = (i.val + (m.val + 1)) % k := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    rw [hm]
    convert shiftIdx_eq_ix_add_sub k hk i.val (m.val + 1) 1 (by omega) using 2; omega
  have h3 : (⟨(((i.val + m.val) % k + k - 1 % k) % k + k - 1 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i.val + (m.val + 3)) := by
    have hstep := shiftIdx_eq_ix_add_sub k hk i.val m.val 1 (by omega)
    have hval : ((i.val + m.val) % k + k - 1 % k) % k = (i.val + m.val + 5 - 1 + 5 * k - 5) % k :=
      congrArg Fin.val hstep
    rw [hval]
    have hstep2 := shiftIdx_eq_ix_add_sub k hk (i.val + m.val + 5 - 1 + 5 * k - 5) 0 1 (by omega)
    simp only [add_zero] at hstep2
    rw [hstep2]; ext; simp only [shiftIdx]
    have heq : i.val + m.val + 5 - 1 + 5 * k - 5 + 5 - 1 + 5 * k - 5 =
        i.val + (m.val + 3) + 5 * k - 5 + k * 5 := by omega
    rw [heq, Nat.add_mul_mod_self_left]
  rw [h1, h2, h3]

lemma mixRotLin_true_eq (k : ℕ) (hk : 0 < k) (i : Fin k) (m : Fin 7) (x : Fin k → F) :
    mixRotLin k hk 2 3 (ixF k hk (i.val + m.val)) x = locLTrue m (win k hk i x) := by
  simp only [mixRotLin, LinearMap.coe_mk, AddHom.coe_mk, mixF, rotF, locLTrue, win, ixF]
  have h1 : (⟨((i.val + m.val) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i.val + (m.val + 2)) := by
    convert shiftIdx_eq_ix_add_sub k hk i.val m.val 3 (by omega) using 2; omega
  have h2 : (⟨(((i.val + m.val) % k + 2) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i.val + (m.val + 4)) := by
    have hm : ((i.val + m.val) % k + 2) % k = (i.val + (m.val + 2)) % k := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    rw [hm]
    convert shiftIdx_eq_ix_add_sub k hk i.val (m.val + 2) 3 (by omega) using 2; omega
  have h3 : (⟨(((i.val + m.val) % k + k - 2 % k) % k + k - 3 % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      shiftIdx k hk (i.val + m.val) := by
    have hstep := shiftIdx_eq_ix_add_sub k hk i.val m.val 2 (by omega)
    have hval : ((i.val + m.val) % k + k - 2 % k) % k = (i.val + m.val + 5 - 2 + 5 * k - 5) % k :=
      congrArg Fin.val hstep
    rw [hval]
    have hstep2 := shiftIdx_eq_ix_add_sub k hk (i.val + m.val + 5 - 2 + 5 * k - 5) 0 3 (by omega)
    simp only [add_zero] at hstep2
    rw [hstep2]; ext; simp only [shiftIdx]
    have heq : i.val + m.val + 5 - 2 + 5 * k - 5 + 5 - 3 + 5 * k - 5 =
        i.val + m.val + 5 * k - 5 + k * 5 := by omega
    rw [heq, Nat.add_mul_mod_self_left]
  rw [h1, h2, h3]

lemma ixF_add_mod (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    ixF k hk ((ixF k hk a).val + b) = ixF k hk (a + b) := by
  ext; simp [ixF, Nat.add_mod]

lemma ixF_sub_add (k : ℕ) (hk : 0 < k) (i a s b : ℕ) (hs : s ≤ a) :
    ixF k hk ((ixF k hk ((ixF k hk (i + a)).val + k - s % k)).val + b) =
      ixF k hk (i + (a - s) + b) := by
  ext
  simp only [ixF]
  have hsub : ((i + a) % k + k - s % k) % k = (i + (a - s)) % k := by
    apply mod_cancel_add k hk _ _ s
    have hsm : s % k ≤ k := le_of_lt (Nat.mod_lt s hk)
    have hq : s = k * (s / k) + s % k := (Nat.div_add_mod s k).symm
    have hmul : k * (s / k + 1) = k * (s / k) + k := by ring
    have h3 : (i + a) % k + k - s % k + s = (i + a) % k + k * (s / k + 1) := by omega
    have h4 : i + (a - s) + s = i + a := by omega
    rw [h3, h4, Nat.add_mul_mod_self_left, Nat.mod_mod]
  rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ixF_sub1_add (k : ℕ) (hk : 0 < k) (i : Fin k) (b : ℕ) (hb : 1 ≤ b) :
    ixF k hk ((ixF k hk (i.val + 1 + k - 2 % k)).val + b) = ixF k hk (i.val + (b - 1)) := by
  ext; simp only [ixF]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  apply mod_cancel_add k hk _ _ 2
  have hsm : 2 % k ≤ k := le_of_lt (Nat.mod_lt 2 hk)
  have hq : 2 = k * (2 / k) + 2 % k := (Nat.div_add_mod 2 k).symm
  have hmul : k * (2 / k + 1) = k * (2 / k) + k := by ring
  have h1 : i.val + 1 + k - 2 % k + b + 2 = (i.val + (b - 1) + 2) + k * (2 / k + 1) := by omega
  rw [h1, Nat.add_mul_mod_self_left]

lemma second_mix_y (k : ℕ) (hk : 0 < k) (name c₁ : Bool → Fin k → F) (b side : Bool) (i : Fin k) :
    let gap := if b then 2 else (1 : ℕ)
    let spin := if b then 3 else (1 : ℕ)
    let r1 := if b then 4 else 0
    let pos := ixF k hk (i.val + if side then 2 else 1)
    ∀ u w x : Fin k → F,
      diff (diff (fun y : Fin k → F =>
        mixF k hk gap (stepF k hk (mixF k hk gap (rotF k hk spin y + name b)) +
          rotF k hk r1 y + c₁ b) pos) u) w x =
      locB b side (win k hk i u) (win k hk i w) := by
  intro gap spin r1 pos u w x
  set Y : (Fin k → F) → Fin k → F := fun y =>
    stepF k hk (mixF k hk gap (rotF k hk spin y + name b)) + rotF k hk r1 y + c₁ b
  have hmix : (fun y => mixF k hk gap (Y y) pos) =
      (fun y => (Y y pos + Y y (ixF k hk (pos.val + gap))) + Y y (ixF k hk (pos.val + k - gap % k))) := rfl
  rw [hmix]
  have hadd : ∀ (f₁ f₂ f₃ : (Fin k → F) → F),
      diff (diff (fun y => (f₁ y + f₂ y) + f₃ y) u) w x =
      diff (diff f₁ u) w x + diff (diff f₂ u) w x + diff (diff f₃ u) w x := by
    intro f₁ f₂ f₃
    have ha : diff (fun y => (f₁ y + f₂ y) + f₃ y) u =
        fun y => (diff f₁ u y + diff f₂ u y) + diff f₃ u y := by
      funext y; rw [diff_add, diff_add]
    rw [ha, diff_add, diff_add]
  rw [hadd]
  have hY : ∀ j : Fin k, diff (diff (fun y => Y y j) u) w x =
      mixRotLin k hk gap spin (ixF k hk (j.val + 1)) u *
        mixRotLin k hk gap spin (ixF k hk (j.val + 2)) w +
      mixRotLin k hk gap spin (ixF k hk (j.val + 1)) w *
        mixRotLin k hk gap spin (ixF k hk (j.val + 2)) u :=
    fun j => second_stepF k hk gap spin r1 (name b) (c₁ b) j u w x
  rw [hY, hY, hY]
  cases b <;> cases side
  ·
    simp only [gap, spin, pos, Bool.false_eq_true, ↓reduceIte, locB, locStepBFalse]
    have e1 := ixF_add_mod k hk (i.val + 1) 1
    have e2 := ixF_add_mod k hk (i.val + 1) 2
    have e4 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + 1)).val + 1) = ixF k hk (i.val + 3) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e5 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + 1)).val + 2) = ixF k hk (i.val + 4) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e6 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + k - 1 % k)).val + 1) = ixF k hk (i.val + 1) := by
      simpa using ixF_sub_add k hk i.val 1 1 1 (by omega)
    have e7 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + k - 1 % k)).val + 2) = ixF k hk (i.val + 2) := by
      simpa using ixF_sub_add k hk i.val 1 1 2 (by omega)
    rw [e4, e5, e6, e7, e1, e2]
    rw [show i.val + 1 + 1 = i.val + 2 by omega, show i.val + 1 + 2 = i.val + 3 by omega]
    simp only [mixRotLin_false_eq k hk i ⟨1, by omega⟩,
               mixRotLin_false_eq k hk i ⟨2, by omega⟩,
               mixRotLin_false_eq k hk i ⟨3, by omega⟩,
               mixRotLin_false_eq k hk i ⟨4, by omega⟩]
    rfl
  ·
    simp only [gap, spin, pos, Bool.false_eq_true, ↓reduceIte, locB, locStepBFalse]
    have e1 := ixF_add_mod k hk (i.val + 2) 1
    have e2 := ixF_add_mod k hk (i.val + 2) 2
    have e4 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + 1)).val + 1) = ixF k hk (i.val + 4) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e5 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + 1)).val + 2) = ixF k hk (i.val + 5) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e6 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + k - 1 % k)).val + 1) = ixF k hk (i.val + 2) := by
      simpa using ixF_sub_add k hk i.val 2 1 1 (by omega)
    have e7 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + k - 1 % k)).val + 2) = ixF k hk (i.val + 3) := by
      simpa using ixF_sub_add k hk i.val 2 1 2 (by omega)
    rw [e4, e5, e6, e7, e1, e2]
    rw [show i.val + 2 + 1 = i.val + 3 by omega, show i.val + 2 + 2 = i.val + 4 by omega]
    simp only [mixRotLin_false_eq k hk i ⟨2, by omega⟩,
               mixRotLin_false_eq k hk i ⟨3, by omega⟩,
               mixRotLin_false_eq k hk i ⟨4, by omega⟩,
               mixRotLin_false_eq k hk i ⟨5, by omega⟩]
    rfl
  ·
    simp only [gap, spin, pos, Bool.false_eq_true, ↓reduceIte, locB, locStepBTrue]
    have e1 := ixF_add_mod k hk (i.val + 1) 1
    have e2 := ixF_add_mod k hk (i.val + 1) 2
    have e4 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + 2)).val + 1) = ixF k hk (i.val + 4) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e5 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + 2)).val + 2) = ixF k hk (i.val + 5) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have hpos_sub : (ixF k hk ((ixF k hk (i.val + 1)).val + k - 2 % k)).val =
        (i.val + 1 + k - 2 % k) % k := by
      simp only [ixF]
      apply mod_cancel_add k hk _ _ 2
      have hsm : 2 % k ≤ k := le_of_lt (Nat.mod_lt 2 hk)
      have hq : 2 = k * (2 / k) + 2 % k := (Nat.div_add_mod 2 k).symm
      have hmul : k * (2 / k + 1) = k * (2 / k) + k := by ring
      have hx : (i.val + 1) % k + k - 2 % k + 2 = (i.val + 1) % k + k * (2 / k + 1) := by omega
      have hy : i.val + 1 + k - 2 % k + 2 = (i.val + 1) + k * (2 / k + 1) := by omega
      rw [hx, hy, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_mod]
    have e6 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + k - 2 % k)).val + 1) = ixF k hk (i.val + 0) := by
      rw [hpos_sub]; exact ixF_sub1_add k hk i 1 (by omega)
    have e7 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 1)).val + k - 2 % k)).val + 2) = ixF k hk (i.val + 1) := by
      rw [hpos_sub]; exact ixF_sub1_add k hk i 2 (by omega)
    rw [e4, e5, e6, e7, e1, e2]
    rw [show i.val + 1 + 1 = i.val + 2 by omega, show i.val + 1 + 2 = i.val + 3 by omega]
    simp only [mixRotLin_true_eq k hk i ⟨0, by omega⟩,
               mixRotLin_true_eq k hk i ⟨1, by omega⟩,
               mixRotLin_true_eq k hk i ⟨2, by omega⟩,
               mixRotLin_true_eq k hk i ⟨3, by omega⟩,
               mixRotLin_true_eq k hk i ⟨4, by omega⟩,
               mixRotLin_true_eq k hk i ⟨5, by omega⟩]
    rfl
  ·
    simp only [gap, spin, pos, ↓reduceIte, locB, locStepBTrue]
    have e1 := ixF_add_mod k hk (i.val + 2) 1
    have e2 := ixF_add_mod k hk (i.val + 2) 2
    have e4 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + 2)).val + 1) = ixF k hk (i.val + 5) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e5 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + 2)).val + 2) = ixF k hk (i.val + 6) := by
      rw [ixF_add_mod, Nat.add_assoc, ixF_add_mod]
    have e6 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + k - 2 % k)).val + 1) = ixF k hk (i.val + 1) := by
      simpa using ixF_sub_add k hk i.val 2 2 1 (by omega)
    have e7 : ixF k hk ((ixF k hk ((ixF k hk (i.val + 2)).val + k - 2 % k)).val + 2) = ixF k hk (i.val + 2) := by
      simpa using ixF_sub_add k hk i.val 2 2 2 (by omega)
    rw [e4, e5, e6, e7, e1, e2]
    rw [show i.val + 2 + 1 = i.val + 3 by omega, show i.val + 2 + 2 = i.val + 4 by omega]
    simp only [mixRotLin_true_eq k hk i ⟨1, by omega⟩,
               mixRotLin_true_eq k hk i ⟨2, by omega⟩,
               mixRotLin_true_eq k hk i ⟨3, by omega⟩,
               mixRotLin_true_eq k hk i ⟨4, by omega⟩,
               mixRotLin_true_eq k hk i ⟨5, by omega⟩,
               mixRotLin_true_eq k hk i ⟨6, by omega⟩]
    rfl

lemma fourth_outF (k : ℕ) (hk : 0 < k) (name c₁ c₂ : Bool → Fin k → F)
    (b : Bool) (i : Fin k) (v : Fin 4 → (Fin k → F)) (x : Fin k → F) :
    fourth (fun y => outF k hk name c₁ c₂ y b i) v x =
      locQ4 b (fun r => win k hk i (v r)) := by
  set gap := if b then 2 else (1 : ℕ)
  set spin := if b then 3 else (1 : ℕ)
  set r1 := if b then 4 else 0
  set r2 := if b then 7 else 2
  set M : (Fin k → F) → Fin k → F := fun y =>
    mixF k hk gap (stepF k hk (mixF k hk gap (rotF k hk spin y + name b)) +
      rotF k hk r1 y + c₁ b)
  have hsplit : (fun y => outF k hk name c₁ c₂ y b i) =
      (fun y => (M y i + (rotF k hk r2 y i + c₂ b i)) +
        (1 + M y (ixF k hk (i.val + 1))) * M y (ixF k hk (i.val + 2))) := by
    funext y; simp only [outF, stepF, M, gap, spin, r1, r2, Pi.add_apply]; ring
  rw [hsplit, fourth_add]
  have hM0_quad : ∃ B0 : (Fin k → F) → (Fin k → F) → F, ∀ u w y, diff (diff (fun z => M z i) u) w y = B0 u w := by
    refine ⟨fun u w =>
        (mixRotLin k hk gap spin (ixF k hk (i.val + 1)) u * mixRotLin k hk gap spin (ixF k hk (i.val + 2)) w +
         mixRotLin k hk gap spin (ixF k hk (i.val + 1)) w * mixRotLin k hk gap spin (ixF k hk (i.val + 2)) u) +
        (mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + gap)).val + 1)) u * mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + gap)).val + 2)) w +
         mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + gap)).val + 1)) w * mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + gap)).val + 2)) u) +
        (mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + k - gap % k)).val + 1)) u * mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + k - gap % k)).val + 2)) w +
         mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + k - gap % k)).val + 1)) w * mixRotLin k hk gap spin (ixF k hk ((ixF k hk (i.val + k - gap % k)).val + 2)) u),
      fun u w y => ?_⟩
    set Y : (Fin k → F) → Fin k → F := fun z =>
      stepF k hk (mixF k hk gap (rotF k hk spin z + name b)) + rotF k hk r1 z + c₁ b
    have hm : (fun z => M z i) = fun z => (Y z i + Y z (ixF k hk (i.val + gap))) + Y z (ixF k hk (i.val + k - gap % k)) := rfl
    rw [hm]
    have ha : diff (fun z => (Y z i + Y z (ixF k hk (i.val + gap))) + Y z (ixF k hk (i.val + k - gap % k))) u =
        fun z => (diff (fun z => Y z i) u z + diff (fun z => Y z (ixF k hk (i.val + gap))) u z) +
                 diff (fun z => Y z (ixF k hk (i.val + k - gap % k))) u z := by
      funext z; rw [diff_add, diff_add]
    rw [ha, diff_add, diff_add]
    dsimp only [Y]
    simp only [Pi.add_apply]
    rw [second_stepF, second_stepF, second_stepF]
  obtain ⟨B0, hB0⟩ := hM0_quad
  have hzero1 : fourth (fun y => M y i + (rotF k hk r2 y i + c₂ b i)) v x = 0 := by
    rw [fourth_add, fourth_add, fourth_of_second_const _ B0 hB0]
    change 0 + (fourth (rotLin k hk r2 i) v x + fourth (fun _ => c₂ b i) v x) = 0
    rw [fourth_linear, fourth_const]
    simp
  rw [hzero1, zero_add]
  have h1 : ∀ u w y, diff (diff (fun z => 1 + M z (ixF k hk (i.val + 1))) u) w y =
      locB b false (win k hk i u) (win k hk i w) := by
    intro u w y
    have hadd : diff (fun z => 1 + M z (ixF k hk (i.val + 1))) u =
        diff (fun z => M z (ixF k hk (i.val + 1))) u := by
      funext z; rw [diff_add, diff_const, zero_add]
    rw [hadd]
    simpa [M, gap, spin, r1] using second_mix_y k hk name c₁ b false i u w y
  have h2 : ∀ u w y, diff (diff (fun z => M z (ixF k hk (i.val + 2))) u) w y =
      locB b true (win k hk i u) (win k hk i w) := by
    intro u w y
    simpa [M, gap, spin, r1] using second_mix_y k hk name c₁ b true i u w y
  exact fourth_mul_of_quad _ _ _ _ h1 h2 v x

def runF (k d : ℕ) (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F)) (x : Fin k → F) : ℕ :=
  (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)

lemma foldl_run_zero {k d : ℕ} (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
    (x : Fin k → F) (l : List (Fin d)) (h : ∀ j ∈ l, ask j 0 x = 0) :
    l.foldl (fun acc j => 2 * acc + (if ask j acc x = 0 then 0 else 1)) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldl_cons]
    have hj : ask j 0 x = 0 := h j List.mem_cons_self
    simp only [hj, ↓reduceIte, mul_zero, add_zero]
    exact ih (fun j' hj' => h j' (List.mem_cons_of_mem _ hj'))

lemma foldl_run_inj {k d : ℕ} (L : Fin d → ((Fin k → F) →ₗ[F] F))
    (x y : Fin k → F) (l : List (Fin d)) (a b : ℕ)
    (heq : l.foldl (fun acc j => 2 * acc + (if L j x = 0 then 0 else 1)) a =
           l.foldl (fun acc j => 2 * acc + (if L j y = 0 then 0 else 1)) b) :
    a = b ∧ ∀ j ∈ l, L j x = L j y := by
  induction l generalizing a b with
  | nil =>
    simp only [List.foldl_nil] at heq
    exact ⟨heq, fun j hj => by simp at hj⟩
  | cons j js ih =>
    simp only [List.foldl_cons] at heq
    obtain ⟨hab, hrest⟩ := ih _ _ heq
    have hbit : (if L j x = 0 then (0 : ℕ) else 1) < 2 := by split_ifs <;> omega
    have hbit2 : (if L j y = 0 then (0 : ℕ) else 1) < 2 := by split_ifs <;> omega
    have ha : a = b := by omega
    have hbi : (if L j x = 0 then (0 : ℕ) else 1) = (if L j y = 0 then 0 else 1) := by omega
    have hL : L j x = L j y := by
      have h01 : ∀ z : F, z = 0 ∨ z = 1 := fun z => by
        fin_cases z
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases h01 (L j x) with hx | hx <;> rcases h01 (L j y) with hy | hy
      · rw [hx, hy]
      · simp [hx, hy] at hbi
      · simp [hx, hy] at hbi
      · rw [hx, hy]
    refine ⟨ha, fun j' hj' => ?_⟩
    rcases List.mem_cons.mp hj' with rfl | hj'
    · exact hL
    · exact hrest j' hj'

lemma finrank_inf_ker_ge {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (U : Submodule F W) (ℓ : W →ₗ[F] F) :
    Module.finrank F U ≤ Module.finrank F (U ⊓ LinearMap.ker ℓ : Submodule F W) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (ℓ.domRestrict U)
  have hrg : Module.finrank F (LinearMap.range (ℓ.domRestrict U)) ≤ 1 := by
    calc Module.finrank F (LinearMap.range (ℓ.domRestrict U))
        ≤ Module.finrank F F := Submodule.finrank_le _
      _ = 1 := Module.finrank_self F
  have hker : Module.finrank F (LinearMap.ker (ℓ.domRestrict U)) =
      Module.finrank F (U ⊓ LinearMap.ker ℓ : Submodule F W) := by
    let e : LinearMap.ker (ℓ.domRestrict U) ≃ₗ[F] (U ⊓ LinearMap.ker ℓ : Submodule F W) :=
      { toFun := fun ⟨⟨x, hxU⟩, hxK⟩ => ⟨x, hxU, hxK⟩
        invFun := fun ⟨x, hxU, hxK⟩ => ⟨⟨x, hxU⟩, hxK⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _, _⟩ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.finrank_eq
  omega

lemma finrank_iInf_ker_ge {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W] :
    ∀ (d : ℕ) (L : Fin d → (W →ₗ[F] F)),
      Module.finrank F W ≤ d + Module.finrank F (⨅ j : Fin d, LinearMap.ker (L j) : Submodule F W)
  | 0, L => by
    have htop : (⨅ j : Fin 0, LinearMap.ker (L j) : Submodule F W) = ⊤ := by simp
    rw [htop, finrank_top, zero_add]
  | d + 1, L => by
    have ih := finrank_iInf_ker_ge d (fun j => L j.castSucc)
    have heq : (⨅ j : Fin (d + 1), LinearMap.ker (L j) : Submodule F W) =
        (⨅ j : Fin d, LinearMap.ker (L j.castSucc)) ⊓ LinearMap.ker (L (Fin.last d)) := by
      ext x
      simp only [Submodule.mem_iInf, Submodule.mem_inf]
      constructor
      · intro h; exact ⟨fun j => h j.castSucc, h (Fin.last d)⟩
      · rintro ⟨h1, h2⟩ j
        refine Fin.lastCases h2 h1 j
    rw [heq]
    have hstep := finrank_inf_ker_ge (⨅ j : Fin d, LinearMap.ker (L j.castSucc)) (L (Fin.last d))
    omega

lemma ker_projectionOnto {W : Type*} [AddCommGroup W] [Module F W]
    {U V : Submodule F W} (hcompl : IsCompl U V) :
    LinearMap.ker (Submodule.projectionOnto U V hcompl) = V := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    have hmem : x ∈ U ⊔ V := hcompl.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hmem
    have hp : Submodule.projectionOnto U V hcompl (u + v) = ⟨u, hu⟩ := by
      rw [map_add, Submodule.projectionOnto_apply_left hcompl ⟨u, hu⟩,
          Submodule.projectionOnto_apply_right hcompl ⟨v, hv⟩, add_zero]
    rw [hp] at hx
    have hu0 : u = 0 := congrArg Subtype.val hx
    simpa [hu0] using hv
  · intro hxV
    exact Submodule.projectionOnto_apply_right hcompl ⟨x, hxV⟩

lemma exists_functionals_ker_eq {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (V : Submodule F W) (d : ℕ) (hd : Module.finrank F W ≤ d + Module.finrank F V) :
    ∃ L : Fin d → (W →ₗ[F] F), (⨅ j : Fin d, LinearMap.ker (L j)) = V := by
  obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl V
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hUd : Module.finrank F U ≤ d := by omega
  let pU : W →ₗ[F] U := Submodule.projectionOnto U V hcompl.symm
  let bU := Module.finBasis F U
  let L : Fin d → (W →ₗ[F] F) := fun j =>
    if hj : j.val < Module.finrank F U then
      (bU.coord ⟨j.val, hj⟩).comp pU
    else 0
  refine ⟨L, ?_⟩
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hx
    have hp0 : pU x = 0 := by
      apply bU.ext_elem
      intro idx
      have hj : idx.val < d := lt_of_lt_of_le idx.isLt hUd
      have hLx := hx ⟨idx.val, hj⟩
      simp only [L, idx.isLt, ↓reduceDIte, LinearMap.comp_apply] at hLx
      simpa using hLx
    have hmem : x ∈ LinearMap.ker pU := hp0
    rwa [ker_projectionOnto hcompl.symm] at hmem
  · intro hxV j
    simp only [L]
    split_ifs with hj
    · simp only [LinearMap.comp_apply]
      have hp0 : pU x = 0 := by
        change x ∈ LinearMap.ker pU
        rwa [ker_projectionOnto hcompl.symm]
      simp [hp0]
    · rfl

def GoodSubspace (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool)
    (V : Submodule F (Fin k → F)) : Prop :=
  ∀ (b : Bool) (i : Fin k), (if b then (mark i).2 else (mark i).1) = true →
    ∀ v : Fin 4 → (Fin k → F), (∀ r, v r ∈ V) → locQ4 b (fun r => win k hk i (v r)) = 0

def FitsProp (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → F) : Prop :=
  ∃ (ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F))
    (readout : ℕ → Bool → Fin k → (Fin k → F) → F),
    (∀ h b i v x, fourth (readout h b i) v x = 0) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      outF k hk name c₁ c₂ x b i = readout (runF k d ask x) b i x

lemma fits_iff_exists_subspace (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → F) :
    FitsProp k hk mark d name c₁ c₂ ↔
      ∃ V : Submodule F (Fin k → F), k ≤ d + Module.finrank F V ∧ GoodSubspace k hk mark V := by
  constructor
  · rintro ⟨ask, readout, hcub, hmatch⟩
    let V : Submodule F (Fin k → F) := ⨅ j : Fin d, LinearMap.ker (ask j 0)
    refine ⟨V, ?_, ?_⟩
    · have hfr := finrank_iInf_ker_ge d (fun j => ask j 0)
      simpa [Module.finrank_pi_fintype, Fintype.card_fin] using hfr
    · intro b i hmk v hv
      have hrun : ∀ x ∈ V, runF k d ask x = 0 := fun x hx =>
        foldl_run_zero ask x (List.finRange d) (fun j _ => by
          have hmem : x ∈ ⨅ j : Fin d, LinearMap.ker (ask j 0) := hx
          rw [Submodule.mem_iInf] at hmem
          exact hmem j)
      have heqV : ∀ x ∈ V, outF k hk name c₁ c₂ x b i = readout 0 b i x := by
        intro x hx; rw [hmatch x b i hmk, hrun x hx]
      have h0 : (0 : Fin k → F) ∈ V := V.zero_mem
      have h1 : ∀ a, a ∈ V → outF k hk name c₁ c₂ a b i = readout 0 b i a := heqV
      have hm0 : v 0 ∈ V := hv 0
      have hm1 : v 1 ∈ V := hv 1
      have hm2 : v 2 ∈ V := hv 2
      have hm3 : v 3 ∈ V := hv 3
      have ha : ∀ x y, x ∈ V → y ∈ V → x + y ∈ V := fun _ _ hx hy => V.add_mem hx hy
      have hfeq : fourth (fun y => outF k hk name c₁ c₂ y b i) v 0 =
          fourth (readout 0 b i) v 0 := by
        rw [fourth_expand, fourth_expand]
        rw [h1 _ (ha _ _ (ha _ _ (ha _ _ (ha _ _ h0 hm0) hm1) hm2) hm3),
            h1 _ (ha _ _ (ha _ _ (ha _ _ h0 hm0) hm1) hm2),
            h1 _ (ha _ _ (ha _ _ (ha _ _ h0 hm0) hm1) hm3),
            h1 _ (ha _ _ (ha _ _ (ha _ _ h0 hm0) hm2) hm3),
            h1 _ (ha _ _ (ha _ _ (ha _ _ h0 hm1) hm2) hm3),
            h1 _ (ha _ _ (ha _ _ h0 hm0) hm1),
            h1 _ (ha _ _ (ha _ _ h0 hm0) hm2),
            h1 _ (ha _ _ (ha _ _ h0 hm0) hm3),
            h1 _ (ha _ _ (ha _ _ h0 hm1) hm2),
            h1 _ (ha _ _ (ha _ _ h0 hm1) hm3),
            h1 _ (ha _ _ (ha _ _ h0 hm2) hm3),
            h1 _ (ha _ _ h0 hm0),
            h1 _ (ha _ _ h0 hm1),
            h1 _ (ha _ _ h0 hm2),
            h1 _ (ha _ _ h0 hm3),
            h1 _ h0]
      rw [← fourth_outF k hk name c₁ c₂ b i v 0, hfeq, hcub]
  · rintro ⟨V, hdim, hgood⟩
    have hdimW : Module.finrank F (Fin k → F) ≤ d + Module.finrank F V := by
      simpa [Module.finrank_pi_fintype, Fintype.card_fin] using hdim
    obtain ⟨L, hL⟩ := exists_functionals_ker_eq V d hdimW
    obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl V
    let π : (Fin k → F) →ₗ[F] (Fin k → F) := V.subtype.comp (Submodule.projectionOnto V U hcompl)
    have hπ_mem : ∀ x, π x ∈ V := fun x => (Submodule.projectionOnto V U hcompl x).2
    have hπ_id : ∀ x ∈ V, π x = x := by
      intro x hx
      simp only [π, LinearMap.comp_apply, Submodule.coe_subtype]
      have := Submodule.projectionOnto_apply_left hcompl ⟨x, hx⟩
      exact congrArg Subtype.val this
    let ask : Fin d → ℕ → ((Fin k → F) →ₗ[F] F) := fun j _ => L j
    let rep : ℕ → (Fin k → F) := fun h =>
      if hex : ∃ x₀, runF k d ask x₀ = h then Classical.choose hex else 0
    let readout : ℕ → Bool → Fin k → (Fin k → F) → F := fun h b i x =>
      if (if b then (mark i).2 else (mark i).1) = true then
        outF k hk name c₁ c₂ (rep h + π (x - rep h)) b i
      else 0
    refine ⟨ask, readout, ?_, ?_⟩
    · intro h b i v x
      by_cases hmk : (if b then (mark i).2 else (mark i).1) = true
      · have hfn : readout h b i = fun y => outF k hk name c₁ c₂ (rep h + π (y - rep h)) b i := by
          funext y; simp only [readout, hmk, ↓reduceIte]
        rw [hfn, fourth_comp_affine (fun y => outF k hk name c₁ c₂ y b i) π (rep h) v x, fourth_outF]
        exact hgood b i hmk (fun r => π (v r)) (fun r => hπ_mem (v r))
      · have hfn : readout h b i = fun _ => 0 := by
          funext y; exact if_neg hmk
        rw [hfn]
        exact fourth_const 0 v x
    · intro x b i hmk
      simp only [readout, hmk, ↓reduceIte]
      have hex : ∃ x₀, runF k d ask x₀ = runF k d ask x := ⟨x, rfl⟩
      have hrep_run : runF k d ask (rep (runF k d ask x)) = runF k d ask x := by
        simp only [rep, hex, ↓reduceDIte]
        exact Classical.choose_spec hex
      have hsub : x - rep (runF k d ask x) ∈ V := by
        rw [← hL, Submodule.mem_iInf]
        intro j
        rw [LinearMap.mem_ker, map_sub]
        have hinj := (foldl_run_inj L _ _ (List.finRange d) 0 0 hrep_run).2 j (List.mem_finRange j)
        rw [hinj, sub_self]
      rw [hπ_id _ hsub, add_sub_cancel]

def first10 : Win →ₗ[F] B where
  toFun w t := w t.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def last10 : Win →ₗ[F] B where
  toFun w t := w t.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma first10_last10_inj (u : Win) (h1 : first10 u = 0) (h2 : last10 u = 0) : u = 0 := by
  funext t
  refine Fin.cases ?_ ?_ t
  · exact congrFun h1 0
  · intro s; exact congrFun h2 s

def Allowable (a : Bool × Bool) (U : Submodule F Win) : Prop :=
  (a.1 = true → ∀ v : Fin 4 → Win, (∀ r, v r ∈ U) → locQ4 false v = 0) ∧
  (a.2 = true → ∀ v : Fin 4 → Win, (∀ r, v r ∈ U) → locQ4 true v = 0)

def relPairSpace (R : Rel) (U : Submodule F Win) : Submodule F ((B × B) × Win) :=
  (R.prod U) ⊓ LinearMap.ker ((LinearMap.snd F B B).comp (LinearMap.fst F (B × B) Win) -
    first10.comp (LinearMap.snd F (B × B) Win))

def relStepMap : ((B × B) × Win) →ₗ[F] (B × B) :=
  ((LinearMap.fst F B B).comp (LinearMap.fst F (B × B) Win)).prod
    (last10.comp (LinearMap.snd F (B × B) Win))

def relStep (R : Rel) (U : Submodule F Win) : Rel :=
  Submodule.map relStepMap (relPairSpace R U)

lemma mem_relStep (R : Rel) (U : Submodule F Win) (p : B × B) :
    p ∈ relStep R U ↔ ∃ y : B, (p.1, y) ∈ R ∧ ∃ u ∈ U, first10 u = y ∧ last10 u = p.2 := by
  simp only [relStep, Submodule.mem_map, relPairSpace, Submodule.mem_inf, Submodule.mem_prod,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, relStepMap, LinearMap.prod_apply, sub_eq_zero, Prod.ext_iff]
  constructor
  · rintro ⟨⟨⟨a, y⟩, u⟩, ⟨⟨hR, hU⟩, hy⟩, h1, h2⟩
    exact ⟨y, h1 ▸ hR, u, hU, hy.symm, h2⟩
  · rintro ⟨y, hR, u, hU, h1, h2⟩
    exact ⟨⟨⟨p.1, y⟩, u⟩, ⟨⟨hR, hU⟩, h1.symm⟩, rfl, h2⟩

def midKer (R : Rel) (U : Submodule F Win) : Submodule F B :=
  (R.comap (LinearMap.inr F B B)) ⊓
    Submodule.map first10 (U ⊓ LinearMap.ker last10)

lemma mem_midKer (R : Rel) (U : Submodule F Win) (y : B) :
    y ∈ midKer R U ↔ (0, y) ∈ R ∧ ∃ u ∈ U, first10 u = y ∧ last10 u = 0 := by
  simp only [midKer, Submodule.mem_inf, Submodule.mem_comap, LinearMap.inr_apply,
    Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨hR, u, ⟨hU, hu2⟩, hu1⟩; exact ⟨hR, u, hU, hu1, hu2⟩
  · rintro ⟨hR, u, hU, hu1, hu2⟩; exact ⟨hR, u, ⟨hU, hu2⟩, hu1⟩

lemma finrank_le_ten (M : Submodule F B) : Module.finrank F M < 11 := by
  have h : Module.finrank F M ≤ Module.finrank F B := Submodule.finrank_le M
  have hB : Module.finrank F B = 10 := by
    simp [B, Fintype.card_fin]
  omega

noncomputable def rewardVal (R : Rel) (U : Submodule F Win) : Fin 11 :=
  ⟨Module.finrank F (midKer R U), finrank_le_ten _⟩

def diagMap : B →ₗ[F] (B × B) := LinearMap.id.prod LinearMap.id

def startRel : Rel := LinearMap.range diagMap

lemma mem_startRel (p : B × B) : p ∈ startRel ↔ p.1 = p.2 := by
  simp only [startRel, LinearMap.mem_range, diagMap, LinearMap.prod_apply, Prod.ext_iff]
  constructor
  · rintro ⟨b, h1, h2⟩; exact h1.symm.trans h2
  · intro h; exact ⟨p.1, rfl, h⟩

def diagKer (R : Rel) : Submodule F B := R.comap diagMap

lemma mem_diagKer (R : Rel) (b : B) : b ∈ diagKer R ↔ (b, b) ∈ R := Iff.rfl

noncomputable def finishRel (R : Rel) : Fin 11 :=
  ⟨Module.finrank F (diagKer R), finrank_le_ten _⟩

def edgeRel (a : Bool × Bool) (R R' : Rel) (r : Fin 11) : Prop :=
  ∃ U : Submodule F Win, Allowable a U ∧ R' = relStep R U ∧ r = rewardVal R U

lemma finrank_add_ker_of_surj {A B : Type*} [AddCommGroup A] [Module F A] [FiniteDimensional F A]
    [AddCommGroup B] [Module F B] [FiniteDimensional F B]
    (K : Submodule F A) (f : A → B)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (hsub : ∀ x y, f (x - y) = f x - f y)
    (hker : ∀ a, a ∈ K ↔ f a = 0)
    (hf : Function.Surjective f) :
    Module.finrank F B + Module.finrank F K = Module.finrank F A := by
  let s : B → A := Function.surjInv hf
  have hs : ∀ b, f (s b) = b := Function.surjInv_eq hf
  let eqv : A ≃ B × K :=
    { toFun := fun a => (f a, ⟨a - s (f a), (hker _).mpr (by rw [hsub, hs, sub_self])⟩)
      invFun := fun ⟨b, k⟩ => s b + k.1
      left_inv := fun a => by simp [add_sub_cancel]
      right_inv := fun ⟨b, ⟨k, hk⟩⟩ => by
        have hk0 : f k = 0 := (hker k).mp hk
        have hfb : f (s b + k) = b := by rw [hadd, hs, hk0, add_zero]
        apply Prod.ext hfb
        apply Subtype.ext
        simp [hfb] }
  have hcard : Nat.card A = Nat.card B * Nat.card K := by
    rw [Nat.card_congr eqv, Nat.card_prod]
  have hA := Module.natCard_eq_pow_finrank (K := F) (V := A)
  have hB := Module.natCard_eq_pow_finrank (K := F) (V := B)
  have hK := Module.natCard_eq_pow_finrank (K := F) (V := K)
  have hF : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  rw [hA, hB, hK, hF, ← pow_add] at hcard
  exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) hcard).symm

def ChainAmbient (m : ℕ) := B × (Fin m → Win)

def chainEndMap : (m : ℕ) → (B × (Fin m → Win)) →ₗ[F] (B × B)
  | 0 => { toFun := fun c => (c.1, c.1)
           map_add' := fun _ _ => rfl
           map_smul' := fun _ _ => rfl }
  | m + 1 => { toFun := fun c => (c.1, last10 (c.2 (Fin.last m)))
               map_add' := fun _ _ => by simp [Prod.mk_add_mk, map_add]
               map_smul' := fun _ _ => by simp [Prod.smul_mk, map_smul] }

def chainSpace : {m : ℕ} → (Fin m → Submodule F Win) → Submodule F (B × (Fin m → Win))
  | 0, _ => ⊤
  | m + 1, U =>
    { carrier := { c | (∀ i : Fin (m + 1), c.2 i ∈ U i) ∧
        first10 (c.2 0) = c.1 ∧
        ∀ i : Fin m, last10 (c.2 i.castSucc) = first10 (c.2 i.succ) }
      zero_mem' := ⟨fun i => (U i).zero_mem, by simp, fun i => by simp⟩, add_mem' := by
        rintro ⟨b1, w1⟩ ⟨b2, w2⟩ ⟨h1, hb1, hc1⟩ ⟨h2, hb2, hc2⟩
        refine ⟨fun i => (U i).add_mem (h1 i) (h2 i), ?_, ?_⟩
        · simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply, map_add, hb1, hb2]
        · intro i; simp only [Prod.snd_add, Pi.add_apply, map_add, hc1 i, hc2 i]
      smul_mem' := by
        rintro a ⟨b1, w1⟩ ⟨h1, hb1, hc1⟩
        refine ⟨fun i => (U i).smul_mem a (h1 i), ?_, ?_⟩
        · change first10 (a • w1 0) = a • b1; rw [map_smul, hb1]
        · intro i; change last10 (a • w1 i.castSucc) = first10 (a • w1 i.succ); rw [map_smul, map_smul, hc1 i] }

def chainRel : {m : ℕ} → (Fin m → Submodule F Win) → Rel
  | 0, _ => startRel
  | m + 1, U => relStep (chainRel (fun i : Fin m => U i.castSucc)) (U (Fin.last m))

noncomputable def chainRewardSum : {m : ℕ} → (Fin m → Submodule F Win) → ℕ
  | 0, _ => 0
  | m + 1, U =>
      chainRewardSum (fun i : Fin m => U i.castSucc) +
      (rewardVal (chainRel (fun i : Fin m => U i.castSucc)) (U (Fin.last m))).val

lemma chain_range_and_ker : ∀ (m : ℕ) (U : Fin m → Submodule F Win),
    LinearMap.range ((chainEndMap m).domRestrict (chainSpace U)) = chainRel U ∧
    Module.finrank F (LinearMap.ker ((chainEndMap m).domRestrict (chainSpace U))) = chainRewardSum U
  | 0, U => by
    constructor
    · ext p
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, chainEndMap, LinearMap.coe_mk,
        AddHom.coe_mk, chainRel, mem_startRel]
      constructor
      · rintro ⟨⟨⟨b, _⟩, _⟩, rfl⟩; rfl
      · intro h; refine ⟨⟨⟨p.1, Fin.elim0⟩, trivial⟩, ?_⟩; exact Prod.ext rfl h
    · haveI hsub : Subsingleton (LinearMap.ker ((chainEndMap 0).domRestrict (chainSpace U))) := by
        refine ⟨fun ⟨⟨⟨b1, w1⟩, _⟩, h1⟩ ⟨⟨⟨b2, w2⟩, _⟩, h2⟩ => ?_⟩
        simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, chainEndMap, LinearMap.coe_mk,
          AddHom.coe_mk, Prod.mk_eq_zero] at h1 h2
        apply Subtype.ext; apply Subtype.ext; apply Prod.ext
        · exact h1.1.trans h2.1.symm
        · funext i; exact Fin.elim0 i
      simpa [chainRewardSum] using
        (Module.finrank_zero_of_subsingleton (R := F)
          (M := LinearMap.ker ((chainEndMap 0).domRestrict (chainSpace U))))
  | m + 1, U => by
    let U' : Fin m → Submodule F Win := fun i => U i.castSucc
    let Um : Submodule F Win := U (Fin.last m)
    obtain ⟨ihR, ihK⟩ := chain_range_and_ker m U'

    have hsplit_end : ∀ (c : chainSpace U),
        let c' : B × (Fin m → Win) := (c.1.1, fun i => c.1.2 i.castSucc)
        c' ∈ chainSpace U' ∧ (chainEndMap m c').2 = first10 (c.1.2 (Fin.last m)) := by
      rintro ⟨⟨b, w⟩, hU, hb0, hlink⟩
      cases m with
      | zero =>
        refine ⟨trivial, ?_⟩
        simpa [chainEndMap] using hb0.symm
      | succ m' =>
        refine ⟨⟨fun i => hU i.castSucc, hb0, fun i => hlink i.castSucc⟩, ?_⟩
        simpa [chainEndMap] using hlink (Fin.last m')
    have hjoin : ∀ (c' : chainSpace U') (u : Um),
        (chainEndMap m c'.1).2 = first10 u.1 →
        ∃ c : chainSpace U,
          c.1.1 = c'.1.1 ∧ (∀ i : Fin m, c.1.2 i.castSucc = c'.1.2 i) ∧
          c.1.2 (Fin.last m) = u.1 := by
      rintro ⟨⟨b, w'⟩, hc'⟩ ⟨u, hu⟩ hconn
      let w : Fin (m + 1) → Win := Fin.snoc w' u
      have hw_cast : ∀ i : Fin m, w i.castSucc = w' i := fun i => by simp [w]
      have hw_last : w (Fin.last m) = u := by simp [w]
      have hmem : (b, w) ∈ chainSpace U := by
        refine ⟨fun i => Fin.lastCases (by simpa [hw_last] using hu)
            (fun j => by cases m with
              | zero => exact Fin.elim0 j
              | succ m' => simpa [hw_cast] using hc'.1 j) i, ?_, ?_⟩
        · cases m with
          | zero =>
            have h0 : (0 : Fin 1) = Fin.last 0 := rfl
            dsimp only; rw [h0, hw_last]; exact hconn.symm
          | succ m' =>
            have h0 : (0 : Fin (m' + 2)) = (0 : Fin (m' + 1)).castSucc := rfl
            dsimp only; rw [h0, hw_cast]; exact hc'.2.1
        · intro i
          cases m with
          | zero => exact Fin.elim0 i
          | succ m' =>
            refine Fin.lastCases ?_ ?_ i
            · dsimp only
              rw [hw_cast (Fin.last m'), show (Fin.last m').succ = Fin.last (m' + 1) from rfl, hw_last]
              exact hconn
            · intro j
              dsimp only
              rw [hw_cast j.castSucc, show j.castSucc.succ = j.succ.castSucc from rfl, hw_cast j.succ]
              exact hc'.2.2 j
      exact ⟨⟨(b, w), hmem⟩, rfl, hw_cast, hw_last⟩
    constructor
    ·
      ext p
      simp only [LinearMap.mem_range, LinearMap.domRestrict_apply, chainRel, mem_relStep]
      constructor
      · rintro ⟨c, hc⟩
        obtain ⟨hc', hconn⟩ := hsplit_end c
        refine ⟨first10 (c.1.2 (Fin.last m)), ?_, c.1.2 (Fin.last m), c.2.1 (Fin.last m), rfl, ?_⟩
        · rw [← ihR, LinearMap.mem_range]
          refine ⟨⟨(c.1.1, fun i => c.1.2 i.castSucc), hc'⟩, ?_⟩
          apply Prod.ext
          · have : p.1 = c.1.1 := (congrArg Prod.fst hc).symm
            rw [this]; cases m <;> rfl
          · exact hconn
        · exact congrArg Prod.snd hc
      · rintro ⟨y, hyR, u, huU, hu1, hu2⟩
        rw [← ihR, LinearMap.mem_range] at hyR
        obtain ⟨c', hc'⟩ := hyR
        have hconn : (chainEndMap m c'.1).2 = first10 u := by
          rw [hu1]; exact congrArg Prod.snd hc'
        obtain ⟨c, hc1, _, hclast⟩ := hjoin c' ⟨u, huU⟩ hconn
        refine ⟨c, ?_⟩
        apply Prod.ext
        · change c.1.1 = p.1
          rw [hc1]
          have hfst : (chainEndMap m c'.1).1 = p.1 := by
            simpa [LinearMap.domRestrict_apply] using congrArg Prod.fst hc'
          cases m <;> exact hfst
        · change last10 (c.1.2 (Fin.last m)) = p.2
          rw [hclast, hu2]
    ·
      let K1 := LinearMap.ker ((chainEndMap (m + 1)).domRestrict (chainSpace U))
      let K0 := LinearMap.ker ((chainEndMap m).domRestrict (chainSpace U'))
      let MK := midKer (chainRel U') Um

      let phi : K1 →ₗ[F] MK :=
        { toFun := fun c =>
            ⟨first10 (c.1.1.2 (Fin.last m)), by
              rw [mem_midKer]
              obtain ⟨hc', hconn⟩ := hsplit_end c.1
              have hker := c.2
              simp only [K1, LinearMap.mem_ker, LinearMap.domRestrict_apply, chainEndMap,
                LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero] at hker
              refine ⟨?_, c.1.1.2 (Fin.last m), c.1.2.1 (Fin.last m), rfl, hker.2⟩
              rw [← ihR, LinearMap.mem_range]
              refine ⟨⟨(c.1.1.1, fun i => c.1.1.2 i.castSucc), hc'⟩, ?_⟩
              apply Prod.ext
              · change (chainEndMap m (c.1.1.1, fun i => c.1.1.2 i.castSucc)).1 = 0
                cases m <;> exact hker.1
              · exact hconn⟩
          map_add' := fun _ _ => by apply Subtype.ext; simp [map_add]
          map_smul' := fun _ _ => by apply Subtype.ext; simp [map_smul] }
      have hphi_surj : Function.Surjective phi := by
        rintro ⟨y, hy⟩
        rw [mem_midKer] at hy
        obtain ⟨hyR, u, huU, hu1, hu2⟩ := hy
        rw [← ihR, LinearMap.mem_range] at hyR
        obtain ⟨c', hc'⟩ := hyR
        have hconn : (chainEndMap m c'.1).2 = first10 u := by
          rw [hu1]; exact congrArg Prod.snd hc'
        obtain ⟨c, hc1, _, hclast⟩ := hjoin c' ⟨u, huU⟩ hconn
        have hcK : c ∈ K1 := by
          simp only [K1, LinearMap.mem_ker, LinearMap.domRestrict_apply, chainEndMap,
            LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero]
          refine ⟨?_, ?_⟩
          · rw [hc1]
            have hfst : (chainEndMap m c'.1).1 = 0 := by
              simpa [LinearMap.domRestrict_apply] using congrArg Prod.fst hc'
            cases m <;> exact hfst
          · rw [hclast, hu2]
        refine ⟨⟨c, hcK⟩, ?_⟩
        apply Subtype.ext
        change first10 (c.1.2 (Fin.last m)) = y
        rw [hclast, hu1]

      let eKer : LinearMap.ker phi ≃ₗ[F] K0 :=
        { toFun := fun ⟨⟨c, hcK⟩, hphi0⟩ =>
            ⟨⟨(c.1.1, fun i => c.1.2 i.castSucc), (hsplit_end c).1⟩, by
              have hker := hcK
              simp only [K1, LinearMap.mem_ker, LinearMap.domRestrict_apply, chainEndMap,
                LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero] at hker
              have hf0 : first10 (c.1.2 (Fin.last m)) = 0 :=
                congrArg Subtype.val hphi0
              simp only [K0, LinearMap.mem_ker, LinearMap.domRestrict_apply]
              apply Prod.ext
              · cases m <;> exact hker.1
              · rw [(hsplit_end c).2, hf0]; rfl⟩
          invFun := fun ⟨c', hc'K⟩ => by
            have hconn : (chainEndMap m c'.1).2 = first10 (0 : Win) := by
              have := congrArg Prod.snd hc'K
              simpa [LinearMap.domRestrict_apply] using this
            let w : Fin (m + 1) → Win := Fin.snoc c'.1.2 0
            have hw_cast : ∀ i : Fin m, w i.castSucc = c'.1.2 i := fun i => by simp [w]
            have hw_last : w (Fin.last m) = 0 := by simp [w]
            have hmem : (c'.1.1, w) ∈ chainSpace U := by
              refine ⟨fun i => Fin.lastCases (by simp [hw_last])
                  (fun j => by cases m with
                    | zero => exact Fin.elim0 j
                    | succ m' => simpa [hw_cast] using c'.2.1 j) i, ?_, ?_⟩
              · cases m with
                | zero =>
                  have h0 : (0 : Fin 1) = Fin.last 0 := rfl
                  dsimp only; rw [h0, hw_last]; exact hconn.symm
                | succ m' =>
                  have h0 : (0 : Fin (m' + 2)) = (0 : Fin (m' + 1)).castSucc := rfl
                  dsimp only; rw [h0, hw_cast]; exact c'.2.2.1
              · intro i
                cases m with
                | zero => exact Fin.elim0 i
                | succ m' =>
                  refine Fin.lastCases ?_ ?_ i
                  · dsimp only
                    rw [hw_cast (Fin.last m'), show (Fin.last m').succ = Fin.last (m' + 1) from rfl, hw_last]
                    exact hconn
                  · intro j
                    dsimp only
                    rw [hw_cast j.castSucc, show j.castSucc.succ = j.succ.castSucc from rfl, hw_cast j.succ]
                    exact c'.2.2.2 j
            have hcK : (⟨(c'.1.1, w), hmem⟩ : chainSpace U) ∈ K1 := by
              simp only [K1, LinearMap.mem_ker, LinearMap.domRestrict_apply, chainEndMap,
                LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero]
              refine ⟨?_, by rw [hw_last, map_zero]⟩
              have hfst : (chainEndMap m c'.1).1 = 0 := by
                simpa [LinearMap.domRestrict_apply] using congrArg Prod.fst hc'K
              cases m <;> exact hfst
            refine ⟨⟨⟨(c'.1.1, w), hmem⟩, hcK⟩, ?_⟩
            apply Subtype.ext
            change first10 (w (Fin.last m)) = 0
            rw [hw_last, map_zero]
          left_inv := fun ⟨⟨⟨⟨b, w⟩, hc⟩, hcK⟩, hphi0⟩ => by
            have hker := hcK
            simp only [K1, LinearMap.mem_ker, LinearMap.domRestrict_apply, chainEndMap,
              LinearMap.coe_mk, AddHom.coe_mk, Prod.mk_eq_zero] at hker
            have hf0 : first10 (w (Fin.last m)) = 0 := congrArg Subtype.val hphi0
            have hwlast0 : w (Fin.last m) = 0 := first10_last10_inj _ hf0 hker.2
            apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
            dsimp only
            refine Prod.ext rfl ?_
            funext i
            refine Fin.lastCases ?_ ?_ i
            · simpa [Fin.snoc_last] using hwlast0.symm
            · intro j; simp
          right_inv := fun ⟨⟨⟨b, w'⟩, hc'⟩, hc'K⟩ => by
            apply Subtype.ext; apply Subtype.ext
            dsimp only
            refine Prod.ext rfl ?_
            funext j; simp
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hrn := finrank_add_ker_of_surj (LinearMap.ker phi) phi
        (fun x y => map_add phi x y) (fun x y => map_sub phi x y) (fun _ => Iff.rfl) hphi_surj
      rw [eKer.finrank_eq, ihK] at hrn
      dsimp only [K1, MK, U', Um] at hrn
      simp only [chainRewardSum, rewardVal]
      omega

def closedSub (k : ℕ) (hk : 0 < k) (U : Fin k → Submodule F Win) : Submodule F (Fin k → F) :=
  ⨅ i : Fin k, (U i).comap (win k hk i)

lemma mem_closedSub (k : ℕ) (hk : 0 < k) (U : Fin k → Submodule F Win) (x : Fin k → F) :
    x ∈ closedSub k hk U ↔ ∀ i : Fin k, win k hk i x ∈ U i := by
  simp [closedSub]

lemma win_last10_eq_first10 (k : ℕ) (hk : 0 < k) (x : Fin k → F) (i : Fin k) :
    last10 (win k hk i x) = first10 (win k hk ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩ x) := by
  funext t
  simp only [last10, first10, win, LinearMap.coe_mk, AddHom.coe_mk, Fin.val_succ, Fin.val_castSucc]
  congr 1
  ext
  simp only [shiftIdx]
  have h1 : ((i.val + 1) % k + t.val + 5 * k - 5) % k = (i.val + (t.val + 1) + 5 * k - 5) % k := by
    have hge : 5 ≤ 5 * k := by omega
    have hL : (i.val + 1) % k + t.val + 5 * k - 5 = (i.val + 1) % k + (t.val + (5 * k - 5)) := by omega
    have hR : i.val + (t.val + 1) + 5 * k - 5 = (i.val + 1) + (t.val + (5 * k - 5)) := by omega
    rw [hL, hR, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  exact h1.symm

lemma closed_chain_finrank (k : ℕ) (hk : 0 < k) (U : Fin k → Submodule F Win) :
    Module.finrank F (closedSub k hk U) =
      chainRewardSum U + (finishRel (chainRel U)).val := by

  let ClosedC : Submodule F (chainSpace U) :=
    LinearMap.ker (((LinearMap.fst F B B - LinearMap.snd F B B).comp (chainEndMap k)).domRestrict (chainSpace U))

  obtain ⟨hR, hK⟩ := chain_range_and_ker k U
  let psi : ClosedC →ₗ[F] diagKer (chainRel U) :=
    { toFun := fun c =>
        ⟨(chainEndMap k c.1.1).1, by
          rw [mem_diagKer, ← hR, LinearMap.mem_range]
          have heq : (chainEndMap k c.1.1).1 = (chainEndMap k c.1.1).2 := by
            have := c.2
            simp only [ClosedC, LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply,
              LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero] at this
            exact this
          exact ⟨c.1, Prod.ext rfl heq.symm⟩⟩
      map_add' := fun _ _ => by apply Subtype.ext; simp [map_add]
      map_smul' := fun _ _ => by apply Subtype.ext; simp [map_smul] }
  have hpsi_surj : Function.Surjective psi := by
    rintro ⟨b, hb⟩
    rw [mem_diagKer, ← hR, LinearMap.mem_range] at hb
    obtain ⟨c, hc⟩ := hb
    have hc' : chainEndMap k c.1 = (b, b) := by simpa [LinearMap.domRestrict_apply] using hc
    have hcC : c ∈ ClosedC := by
      simp only [ClosedC, LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply,
        LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero]
      rw [hc']
    exact ⟨⟨c, hcC⟩, Subtype.ext (congrArg Prod.fst hc')⟩
  let eKer : LinearMap.ker psi ≃ₗ[F] LinearMap.ker ((chainEndMap k).domRestrict (chainSpace U)) :=
    { toFun := fun ⟨⟨c, hcC⟩, h0⟩ =>
        ⟨c, by
          have h1 : (chainEndMap k c.1).1 = 0 := congrArg Subtype.val h0
          have heq : (chainEndMap k c.1).1 = (chainEndMap k c.1).2 := by
            simpa [ClosedC, sub_eq_zero] using hcC
          exact Prod.ext h1 (heq.symm.trans h1)⟩
      invFun := fun ⟨c, hcK⟩ =>
        ⟨⟨c, by
          have h1 := congrArg Prod.fst hcK
          have h2 := congrArg Prod.snd hcK
          simp only [ClosedC, LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply,
            LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero]
          exact h1.trans h2.symm⟩,
          Subtype.ext (congrArg Prod.fst hcK)⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdimClosedC : Module.finrank F ClosedC =
      chainRewardSum U + (finishRel (chainRel U)).val := by
    have hrn := finrank_add_ker_of_surj (LinearMap.ker psi) psi
      (fun x y => map_add psi x y) (fun x y => map_sub psi x y) (fun _ => Iff.rfl) hpsi_surj
    rw [eKer.finrank_eq, hK] at hrn
    simp only [finishRel]
    omega

  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  let fwd : closedSub (k' + 1) hk U →ₗ[F] ClosedC :=
    { toFun := fun ⟨x, hx⟩ =>
        let c : B × (Fin (k' + 1) → Win) := (first10 (win (k' + 1) hk 0 x), fun i => win (k' + 1) hk i x)
        have hc : c ∈ chainSpace U := by
          refine ⟨fun i => (mem_closedSub _ hk U x).mp hx i, rfl, fun i => ?_⟩
          have h := win_last10_eq_first10 (k' + 1) hk x i.castSucc
          have hi : (⟨(i.castSucc.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ : Fin (k' + 1)) = i.succ := by
            ext; simp [Nat.mod_eq_of_lt i.succ.isLt]
          rw [hi] at h; exact h
        have hcl : (⟨c, hc⟩ : chainSpace U) ∈ ClosedC := by
          simp only [ClosedC, LinearMap.mem_ker, LinearMap.domRestrict_apply, LinearMap.comp_apply,
            LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero, chainEndMap,
            LinearMap.coe_mk, AddHom.coe_mk, c]
          have h := win_last10_eq_first10 (k' + 1) hk x (Fin.last k')
          have hlast : (⟨((Fin.last k').val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ : Fin (k' + 1)) = 0 := by
            ext; simp
          rw [hlast] at h; exact h.symm
        ⟨⟨c, hc⟩, hcl⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

  let invFun : ClosedC → closedSub (k' + 1) hk U := fun ⟨⟨⟨b, ws⟩, hU, hb0, hlink⟩, hcl⟩ =>
    let x : Fin (k' + 1) → F := fun j => ws ⟨(j.val + 5) % (k' + 1), Nat.mod_lt _ hk⟩ 0
    have hwrap : last10 (ws (Fin.last k')) = first10 (ws 0) := by
      have h1 : b = last10 (ws (Fin.last k')) := by
        simpa [ClosedC, chainEndMap, sub_eq_zero] using hcl
      rw [← h1, hb0]
    have hstep_all : ∀ i : Fin (k' + 1),
        last10 (ws i) = first10 (ws ⟨(i.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩) := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · have h0 : (⟨((Fin.last k').val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ : Fin (k' + 1)) = 0 := by
          ext; simp
        rw [h0]; exact hwrap
      · intro j
        have hj : (⟨(j.castSucc.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ : Fin (k' + 1)) = j.succ := by
          ext; simp [Nat.mod_eq_of_lt j.succ.isLt]
        rw [hj]; exact hlink j
    have hws_eq : ∀ (t : Fin 11) (i : Fin (k' + 1)),
        ws i t = x (shiftIdx (k' + 1) hk (i.val + t.val)) := by
      intro t
      induction t using Fin.induction with
      | zero =>
        intro i
        simp only [x, Fin.val_zero, add_zero, shiftIdx]
        congr 1; ext
        have h5 : ((i.val + 5 * (k' + 1) - 5) % (k' + 1) + 5) % (k' + 1) = i.val := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : i.val + 5 * (k' + 1) - 5 + 5 = i.val + (k' + 1) * 5 := by omega
          rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
        exact h5.symm
      | succ s ih =>
        intro i
        have h1 : ws i s.succ = last10 (ws i) s := rfl
        rw [h1, hstep_all i]
        change ws ⟨(i.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ s.castSucc = _
        rw [ih]
        congr 1; ext; simp only [shiftIdx, Fin.val_castSucc, Fin.val_succ]
        have hge : 5 ≤ 5 * (k' + 1) := by omega
        have hL : (i.val + 1) % (k' + 1) + s.val + 5 * (k' + 1) - 5 =
            (i.val + 1) % (k' + 1) + (s.val + (5 * (k' + 1) - 5)) := by omega
        have hR : i.val + (s.val + 1) + 5 * (k' + 1) - 5 =
            (i.val + 1) + (s.val + (5 * (k' + 1) - 5)) := by omega
        rw [hL, hR, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hx_mem : x ∈ closedSub (k' + 1) hk U := by
      rw [mem_closedSub]
      intro i
      have heq : win (k' + 1) hk i x = ws i := funext (fun t => (hws_eq t i).symm)
      rw [heq]; exact hU i
    ⟨x, hx_mem⟩
  let eqv : closedSub (k' + 1) hk U ≃ₗ[F] ClosedC :=
    { toLinearMap := fwd
      invFun := invFun
      left_inv := fun ⟨x, hx⟩ => by
        apply Subtype.ext; funext j
        change x (shiftIdx (k' + 1) hk (((j.val + 5) % (k' + 1)) + 0)) = x j
        congr 1; ext; simp only [shiftIdx, add_zero]
        have hge : 5 ≤ 5 * (k' + 1) := by omega
        have h1 : (j.val + 5) % (k' + 1) + 5 * (k' + 1) - 5 =
            (j.val + 5) % (k' + 1) + (5 * (k' + 1) - 5) := by omega
        rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have h2 : j.val + 5 + (5 * (k' + 1) - 5) = j.val + (k' + 1) * 5 := by omega
        rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
      right_inv := fun ⟨⟨⟨b, ws⟩, hU, hb0, hlink⟩, hcl⟩ => by
        apply Subtype.ext; apply Subtype.ext
        have hwrap : last10 (ws (Fin.last k')) = first10 (ws 0) := by
          have h1 : b = last10 (ws (Fin.last k')) := by
            simpa [ClosedC, chainEndMap, sub_eq_zero] using hcl
          rw [← h1, hb0]
        have hstep_all : ∀ i : Fin (k' + 1),
            last10 (ws i) = first10 (ws ⟨(i.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩) := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · have h0 : (⟨((Fin.last k').val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ : Fin (k' + 1)) = 0 := by
              ext; simp
            rw [h0]; exact hwrap
          · intro j
            have hj : (⟨(j.castSucc.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ : Fin (k' + 1)) = j.succ := by
              ext; simp [Nat.mod_eq_of_lt j.succ.isLt]
            rw [hj]; exact hlink j
        let x : Fin (k' + 1) → F := fun j => ws ⟨(j.val + 5) % (k' + 1), Nat.mod_lt _ hk⟩ 0
        have hws_eq : ∀ (t : Fin 11) (i : Fin (k' + 1)),
            ws i t = x (shiftIdx (k' + 1) hk (i.val + t.val)) := by
          intro t
          induction t using Fin.induction with
          | zero =>
            intro i; simp only [x, Fin.val_zero, add_zero, shiftIdx]
            congr 1; ext
            have h5 : ((i.val + 5 * (k' + 1) - 5) % (k' + 1) + 5) % (k' + 1) = i.val := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
              have : i.val + 5 * (k' + 1) - 5 + 5 = i.val + (k' + 1) * 5 := by omega
              rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.isLt]
            exact h5.symm
          | succ s ih =>
            intro i
            have h1 : ws i s.succ = last10 (ws i) s := rfl
            rw [h1, hstep_all i]
            change ws ⟨(i.val + 1) % (k' + 1), Nat.mod_lt _ hk⟩ s.castSucc = _
            rw [ih]
            congr 1; ext; simp only [shiftIdx, Fin.val_castSucc, Fin.val_succ]
            have hL : (i.val + 1) % (k' + 1) + s.val + 5 * (k' + 1) - 5 =
                (i.val + 1) % (k' + 1) + (s.val + (5 * (k' + 1) - 5)) := by omega
            have hR : i.val + (s.val + 1) + 5 * (k' + 1) - 5 =
                (i.val + 1) + (s.val + (5 * (k' + 1) - 5)) := by omega
            rw [hL, hR, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hwin : ∀ i, win (k' + 1) hk i x = ws i := fun i => funext (fun t => (hws_eq t i).symm)
        apply Prod.ext
        · change first10 (win (k' + 1) hk 0 x) = b
          rw [hwin 0, hb0]
        · funext i; exact hwin i }
  rw [eqv.finrank_eq, hdimClosedC]

lemma chainRewardSum_eq_sum : ∀ (m : ℕ) (U : Fin m → Submodule F Win),
    ∃ (path : Fin (m + 1) → Rel) (rew : Fin m → Fin 11),
      path 0 = startRel ∧
      path (Fin.last m) = chainRel U ∧
      (∀ i : Fin m, path i.succ = relStep (path i.castSucc) (U i) ∧
        rew i = rewardVal (path i.castSucc) (U i)) ∧
      (∑ i : Fin m, (rew i).val) = chainRewardSum U
  | 0, U => ⟨fun _ => startRel, Fin.elim0, rfl, rfl, fun i => Fin.elim0 i, by simp [chainRewardSum]⟩
  | m + 1, U => by
    let U' : Fin m → Submodule F Win := fun i => U i.castSucc
    obtain ⟨p', r', hp0, hplast, hstep, hsum⟩ := chainRewardSum_eq_sum m U'
    let rLast : Fin 11 := rewardVal (chainRel U') (U (Fin.last m))
    let p : Fin (m + 2) → Rel := Fin.snoc p' (relStep (chainRel U') (U (Fin.last m)))
    let r : Fin (m + 1) → Fin 11 := Fin.snoc r' rLast
    refine ⟨p, r, ?_, ?_, ?_, ?_⟩
    · have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
      rw [h0]; simpa [p, Fin.snoc_castSucc] using hp0
    · simp [p, Fin.snoc_last, chainRel, U']
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [p, r, Fin.snoc_last]
        have hc' : p (Fin.last m).castSucc = p' (Fin.last m) := by
          simp [p]
        dsimp only [p] at hc'
        rw [hc', hplast, show (Fin.last m).succ = Fin.last (m + 1) from rfl, Fin.snoc_last]
        exact ⟨rfl, rfl⟩
      · intro j
        have h1 : p j.castSucc.castSucc = p' j.castSucc := by simp [p]
        have h2 : p j.castSucc.succ = p' j.succ := by
          dsimp only [p]
          rw [show j.castSucc.succ = j.succ.castSucc from rfl, Fin.snoc_castSucc]
        have h3 : r j.castSucc = r' j := by simp [r]
        rw [h1, h2, h3]
        exact hstep j
    · rw [Fin.sum_univ_castSucc]
      have h1 : ∀ j : Fin m, (r j.castSucc).val = (r' j).val := fun j => by
        simp [r, Fin.snoc_castSucc]
      simp only [h1, hsum, r, Fin.snoc_last, chainRewardSum, rLast, U']

lemma path_to_chain : ∀ (m : ℕ) (U : Fin m → Submodule F Win)
    (path : Fin (m + 1) → Rel) (rew : Fin m → Fin 11),
    path 0 = startRel →
    (∀ i : Fin m, path i.succ = relStep (path i.castSucc) (U i) ∧
      rew i = rewardVal (path i.castSucc) (U i)) →
    path (Fin.last m) = chainRel U ∧ (∑ i : Fin m, (rew i).val) = chainRewardSum U
  | 0, _, path, _, hp0, _ => ⟨hp0, by simp [chainRewardSum]⟩
  | m + 1, U, path, rew, hp0, hstep => by
    let U' : Fin m → Submodule F Win := fun i => U i.castSucc
    let p' : Fin (m + 1) → Rel := fun i => path i.castSucc
    let r' : Fin m → Fin 11 := fun i => rew i.castSucc
    have ih := path_to_chain m U' p' r' hp0 (fun j => hstep j.castSucc)
    have hlast := hstep (Fin.last m)
    constructor
    · change path (Fin.last m).succ = relStep (chainRel U') (U (Fin.last m))
      rw [hlast.1]; exact congrArg (fun R => relStep R (U (Fin.last m))) ih.1
    · rw [Fin.sum_univ_castSucc]
      change (∑ j : Fin m, (r' j).val) + (rew (Fin.last m)).val =
        chainRewardSum U' + (rewardVal (chainRel U') (U (Fin.last m))).val
      rw [ih.2, hlast.2]
      have : path (Fin.last m).castSucc = chainRel U' := ih.1
      rw [this]

lemma rel_card_le : Nat.card Rel ≤ 2 ^ 400 := by
  have hfinEnd : Finite ((B × B) →ₗ[F] (B × B)) :=
    Finite.of_injective (fun f : (B × B) →ₗ[F] (B × B) => (f : (B × B) → (B × B))) DFunLike.coe_injective
  have hsurj : Function.Surjective (LinearMap.ker : ((B × B) →ₗ[F] (B × B)) → Rel) := by
    intro R
    obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl R
    let pU : (B × B) →ₗ[F] (B × B) := U.subtype.comp (Submodule.projectionOnto U R hcompl.symm)
    refine ⟨pU, ?_⟩
    ext x
    simp only [pU, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype,
      Submodule.coe_eq_zero]
    change x ∈ LinearMap.ker (Submodule.projectionOnto U R hcompl.symm) ↔ x ∈ R
    rw [ker_projectionOnto hcompl.symm]
  have hle : Nat.card Rel ≤ Nat.card ((B × B) →ₗ[F] (B × B)) :=
    Nat.card_le_card_of_surjective _ hsurj
  have hcard : Nat.card ((B × B) →ₗ[F] (B × B)) = 2 ^ 400 := by
    have hBB : Module.finrank F (B × B) = 20 := by
      rw [Module.finrank_prod, Module.finrank_pi_fintype]
      simp [F]
    let b := Module.finBasis F (B × B)
    let eM : ((B × B) →ₗ[F] (B × B)) ≃ Matrix (Fin (Module.finrank F (B × B))) (Fin (Module.finrank F (B × B))) F :=
      (LinearMap.toMatrix b b).toEquiv
    rw [Nat.card_congr eM, Nat.card_eq_fintype_card]
    change Fintype.card (Fin (Module.finrank F (B × B)) → Fin (Module.finrank F (B × B)) → F) = 2 ^ 400
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ZMod.card, hBB, ← pow_mul]
  exact hle.trans hcard.le

theorem main_automaton :
    ∃ (s : ℕ) (start : Fin s) (edge : Bool × Bool → Fin s → Fin s → Fin 11 → Prop)
      (finish : Fin s → Fin 11),
      s ≤ 2 ^ 400 ∧
      ∀ (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ) (name c₁ c₂),
        FitsProp k hk mark d name c₁ c₂ ↔
        ∃ (path : Fin (k + 1) → Fin s) (reward : Fin k → Fin 11),
          path 0 = start ∧
          (∀ i : Fin k, edge (mark i) (path i.castSucc) (path i.succ) (reward i)) ∧
          k ≤ d + (∑ i, (reward i).val) + (finish (path (Fin.last k))).val := by
  have hfinEnd : Finite ((B × B) →ₗ[F] (B × B)) :=
    Finite.of_injective (fun f : (B × B) →ₗ[F] (B × B) => (f : (B × B) → (B × B))) DFunLike.coe_injective
  have : Finite Rel := Finite.of_surjective (LinearMap.ker : ((B × B) →ₗ[F] (B × B)) → Rel) (by
    intro R
    obtain ⟨U, hcompl⟩ := Submodule.exists_isCompl R
    refine ⟨U.subtype.comp (Submodule.projectionOnto U R hcompl.symm), ?_⟩
    ext x
    simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype, Submodule.coe_eq_zero]
    change x ∈ LinearMap.ker (Submodule.projectionOnto U R hcompl.symm) ↔ x ∈ R
    rw [ker_projectionOnto hcompl.symm])
  let s := Nat.card Rel
  let e : Rel ≃ Fin s := Finite.equivFin Rel
  refine ⟨s, e startRel, fun a x y r => edgeRel a (e.symm x) (e.symm y) r,
    fun x => finishRel (e.symm x), rel_card_le, ?_⟩
  intro k hk mark d name c₁ c₂
  rw [fits_iff_exists_subspace]
  constructor
  · rintro ⟨V, hdim, hgood⟩
    let U : Fin k → Submodule F Win := fun i => Submodule.map (win k hk i) V
    have hallow : ∀ i : Fin k, Allowable (mark i) (U i) := by
      intro i
      refine ⟨fun hm1 v hv => ?_, fun hm2 v hv => ?_⟩
      · have hpre : ∀ r : Fin 4, ∃ x ∈ V, win k hk i x = v r := fun r =>
          Submodule.mem_map.mp (hv r)
        choose x hxV hxw using hpre
        have := hgood false i hm1 x hxV
        simpa [hxw] using this
      · have hpre : ∀ r : Fin 4, ∃ x ∈ V, win k hk i x = v r := fun r =>
          Submodule.mem_map.mp (hv r)
        choose x hxV hxw using hpre
        have := hgood true i hm2 x hxV
        simpa [hxw] using this
    have hVle : V ≤ closedSub k hk U := by
      intro x hxV
      rw [mem_closedSub]
      intro i
      exact Submodule.mem_map_of_mem hxV
    have hdimle : Module.finrank F V ≤ Module.finrank F (closedSub k hk U) :=
      Submodule.finrank_mono hVle
    rw [closed_chain_finrank k hk U] at hdimle
    obtain ⟨pathR, rew, hp0, hplast, hstep, hsum⟩ := chainRewardSum_eq_sum k U
    refine ⟨fun j => e (pathR j), rew, by simp [hp0], ?_, ?_⟩
    · intro i
      simp only [Equiv.symm_apply_apply]
      exact ⟨U i, hallow i, (hstep i).1, (hstep i).2⟩
    · simp only [Equiv.symm_apply_apply, hsum, hplast]
      omega
  · rintro ⟨path, rew, hp0, hedge, hdim⟩
    have hch : ∀ i : Fin k, ∃ U : Submodule F Win,
        Allowable (mark i) U ∧
        e.symm (path i.succ) = relStep (e.symm (path i.castSucc)) U ∧
        rew i = rewardVal (e.symm (path i.castSucc)) U := hedge
    choose U hallow hstep hrew using hch
    have hp0' : e.symm (path 0) = startRel := by rw [hp0, Equiv.symm_apply_apply]
    obtain ⟨hplast, hsum⟩ := path_to_chain k U (fun j => e.symm (path j)) rew hp0'
      (fun i => ⟨hstep i, hrew i⟩)
    refine ⟨closedSub k hk U, ?_, ?_⟩
    · rw [closed_chain_finrank k hk U, ← hsum, ← hplast]
      dsimp only at hdim
      omega
    · intro b i hmk v hv
      have hvw : ∀ r, win k hk i (v r) ∈ U i := fun r => (mem_closedSub k hk U (v r)).mp (hv r) i
      cases b
      · exact (hallow i).1 hmk (fun r => win k hk i (v r)) hvw
      · exact (hallow i).2 hmk (fun r => win k hk i (v r)) hvw

end PEqualNP.Outside.L_meta_29743_aux

theorem PEqualNP.Outside.L_meta_29743 :
(
let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  let out := fun (x : W) (b : Bool) =>
    let z := mix (gap b) (rot (spin b) x + name b)
    let y := step z + rot (if b then 4 else 0) x + c₁ b
    step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun h j =>
      2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
  ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
    (∀ h b i, cubic (readout h b i)) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      out x b i = readout (run ask x) b i x
∃ (s : ℕ) (start : Fin s) (edge : Bool × Bool → Fin s → Fin s → Fin 11 → Prop)
    (finish : Fin s → Fin 11),
  s ≤ 2 ^ 400 ∧
  ∀ (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ) (name c₁ c₂),
    fits k hk mark d name c₁ c₂ ↔
    ∃ (path : Fin (k + 1) → Fin s) (reward : Fin k → Fin 11),
      path 0 = start ∧
      (∀ i : Fin k, edge (mark i) (path i.castSucc) (path i.succ) (reward i)) ∧
      k ≤ d + (∑ i, (reward i).val) + (finish (path (Fin.last k))).val
) :=
  PEqualNP.Outside.L_meta_29743_aux.main_automaton
