import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29748_aux

abbrev W (k : ℕ) := Fin k → ZMod 2

def ix (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k :=
  ⟨n % k, Nat.mod_lt _ hk⟩

def rot (k : ℕ) (hk : 0 < k) (s : ℕ) (x : W k) (i : Fin k) : ZMod 2 :=
  x (ix k hk (i.val + k - (s % k)))

def mix (k : ℕ) (hk : 0 < k) (x : W k) (i : Fin k) : ZMod 2 :=
  x i + x (ix k hk (i.val + 2)) + rot k hk 2 x i

def chi (k : ℕ) (hk : 0 < k) (y : W k) (i : Fin k) : ZMod 2 :=
  y i + (1 + y (ix k hk (i.val + 1))) * y (ix k hk (i.val + 2))

def upd (k : ℕ) (hk : 0 < k) (x : W k) (i : Fin k) : ZMod 2 :=
  chi k hk (mix k hk x) i

def run (k : ℕ) (hk : 0 < k) (key name c1 c2 : W k) : W k :=
  upd k hk (upd k hk (rot k hk 3 key + name) + rot k hk 4 key + c1) + rot k hk 7 key + c2

def sh (k : ℕ) (hk : 0 < k) (s : ℕ) (x : W k) (i : Fin k) : ZMod 2 :=
  x (ix k hk (s + i.val))

def F (k : ℕ) (hk : 0 < k) (z gm y : W k) (i : Fin k) : ZMod 2 :=
  chi k hk (mix k hk (chi k hk y) + gm) i +
    chi k hk (mix k hk (chi k hk (y + rot k hk 3 z)) + gm + rot k hk 4 z) i

lemma zmod2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val < 2 := a.isLt
  interval_cases hv : a.val
  · left; exact Fin.ext hv
  · right; exact Fin.ext hv

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma zmod2_add_cancel_left (a b : ZMod 2) : a + (a + b) = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma zmod2_add_eq_zero (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma w_add_self {k : ℕ} (x : W k) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

lemma w_add_cancel_left {k : ℕ} (x y : W k) : x + (x + y) = y := by
  funext i
  exact zmod2_add_cancel_left (x i) (y i)

lemma w_add_eq_zero {k : ℕ} (x y : W k) : x + y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : x i + y i = 0 := congrFun h i
    exact (zmod2_add_eq_zero (x i) (y i)).mp hi
  · rintro rfl
    exact w_add_self x

lemma card_W (k : ℕ) : Fintype.card (W k) = 2 ^ k := by
  simp [W, ZMod.card]

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def z2b (a : ZMod 2) : Bool := decide (a = 1)

lemma b2z_z2b (a : ZMod 2) : b2z (z2b a) = a := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma z2b_b2z (b : Bool) : z2b (b2z b) = b := by
  cases b <;> decide

lemma z2b_add (a b : ZMod 2) : z2b (a + b) = xor (z2b a) (z2b b) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma z2b_mul (a b : ZMod 2) : z2b (a * b) = (z2b a && z2b b) := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

lemma z2b_one_add (a : ZMod 2) : z2b (1 + a) = !(z2b a) := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma z2b_zero : z2b 0 = false := by
  decide

lemma z2b_eq_false (a : ZMod 2) : z2b a = false ↔ a = 0 := by
  rcases zmod2_cases a with rfl | rfl <;> decide

lemma b2z_add (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

lemma ix_val {k : ℕ} (hk : 0 < k) (i : Fin k) : ix k hk i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

lemma ix_mod {k : ℕ} (hk : 0 < k) (n : ℕ) : ix k hk (n % k) = ix k hk n := by
  apply Fin.ext
  simp [ix]

lemma ix_add_k {k : ℕ} (hk : 0 < k) (n : ℕ) : ix k hk (n + k) = ix k hk n := by
  apply Fin.ext
  simp [ix]

lemma ix_add_mul_k {k : ℕ} (hk : 0 < k) (n q : ℕ) : ix k hk (n + q * k) = ix k hk n := by
  apply Fin.ext
  simp [ix]

lemma ix_add_mod_left {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix k hk (a % k + b) = ix k hk (a + b) := by
  apply Fin.ext
  simp [ix, Nat.add_mod]

lemma ix_add_mod_right {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    ix k hk (a + b % k) = ix k hk (a + b) := by
  apply Fin.ext
  simp [ix, Nat.add_mod]

lemma rot_eq_sh {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) :
    rot k hk s x = sh k hk (k - s % k) x := by
  funext i
  simp only [rot, sh]
  have hlt : s % k < k := Nat.mod_lt s hk
  have heq : i.val + k - s % k = k - s % k + i.val := by omega
  rw [heq]

lemma rot_eq_sub2k {k : ℕ} (hk : 0 < k) {s : ℕ} (hs : s < 2 * k) (x : W k) (i : Fin k) :
    rot k hk s x i = x (ix k hk (i.val + 2 * k - s)) := by
  simp only [rot]
  by_cases hsk : s < k
  · rw [Nat.mod_eq_of_lt hsk]
    have heq : i.val + 2 * k - s = (i.val + k - s) + k := by omega
    rw [heq, ix_add_k]
  · have hmod : s % k = s - k := by
      have h1 : s = (s - k) + k := by omega
      conv_lhs => rw [h1]
      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    have heq : i.val + k - (s - k) = i.val + 2 * k - s := by omega
    rw [heq]

lemma rot_ix_sub2k {k : ℕ} (hk : 0 < k) {s : ℕ} (hs : s < 2 * k) (x : W k) (n : ℕ) :
    rot k hk s x (ix k hk n) = x (ix k hk (n + 2 * k - s)) := by
  rw [rot_eq_sub2k hk hs]
  have h1 : (ix k hk n).val + 2 * k - s = n % k + (2 * k - s) := by
    simp [ix]
    omega
  have h2 : n + 2 * k - s = n + (2 * k - s) := by omega
  rw [h1, h2, ix_add_mod_left]

lemma sh_add {k : ℕ} (hk : 0 < k) (s : ℕ) (x y : W k) :
    sh k hk s (x + y) = sh k hk s x + sh k hk s y := by
  funext i
  rfl

lemma sh_zero {k : ℕ} (hk : 0 < k) (s : ℕ) : sh k hk s 0 = 0 := by
  funext i
  rfl

lemma sh_comp {k : ℕ} (hk : 0 < k) (s1 s2 : ℕ) (x : W k) :
    sh k hk s1 (sh k hk s2 x) = sh k hk (s2 + s1) x := by
  funext i
  simp only [sh]
  change x (ix k hk (s2 + (s1 + i.val) % k)) = x (ix k hk (s2 + s1 + i.val))
  rw [ix_add_mod_right, Nat.add_assoc]

lemma sh_zero_shift {k : ℕ} (hk : 0 < k) (x : W k) : sh k hk 0 x = x := by
  funext i
  simp [sh, ix_val]

lemma sh_k {k : ℕ} (hk : 0 < k) (x : W k) : sh k hk k x = x := by
  funext i
  simp only [sh]
  rw [Nat.add_comm, ix_add_k, ix_val]

lemma sh_mod {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) :
    sh k hk (s % k) x = sh k hk s x := by
  funext i
  simp only [sh]
  rw [ix_add_mod_left]

def shEquiv (k : ℕ) (hk : 0 < k) (s : ℕ) : W k ≃ W k where
  toFun := sh k hk s
  invFun := sh k hk (k - s % k)
  left_inv x := by
    rw [sh_comp, ← sh_mod hk (s + (k - s % k))]
    have hlt : s % k < k := Nat.mod_lt s hk
    have hm : (s + (k - s % k)) % k = 0 := by
      have hd := Nat.div_add_mod s k
      have h1 : s + (k - s % k) = k * (s / k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mul_mod_right]
    rw [hm, sh_zero_shift]
  right_inv x := by
    rw [sh_comp, ← sh_mod hk (k - s % k + s)]
    have hlt : s % k < k := Nat.mod_lt s hk
    have hm : (k - s % k + s) % k = 0 := by
      have hd := Nat.div_add_mod s k
      have h1 : k - s % k + s = k * (s / k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mul_mod_right]
    rw [hm, sh_zero_shift]

lemma sh_rot {k : ℕ} (hk : 0 < k) (s r : ℕ) (x : W k) :
    sh k hk s (rot k hk r x) = rot k hk r (sh k hk s x) := by
  rw [rot_eq_sh, rot_eq_sh, sh_comp, sh_comp, Nat.add_comm]

lemma rot_add {k : ℕ} (hk : 0 < k) (r : ℕ) (x y : W k) :
    rot k hk r (x + y) = rot k hk r x + rot k hk r y := by
  rw [rot_eq_sh, rot_eq_sh, rot_eq_sh, sh_add]

lemma sh_mix {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) :
    sh k hk s (mix k hk x) = mix k hk (sh k hk s x) := by
  funext i
  simp only [sh, mix]
  have h1 : (ix k hk (s + i.val)).val + 2 = (s + i.val) % k + 2 := rfl
  have h2 : s + (ix k hk (i.val + 2)).val = s + (i.val + 2) % k := rfl
  have hix : ix k hk ((ix k hk (s + i.val)).val + 2) = ix k hk (s + (ix k hk (i.val + 2)).val) := by
    rw [h1, h2, ix_add_mod_left, ix_add_mod_right, Nat.add_assoc]
  have hrot : rot k hk 2 x (ix k hk (s + i.val)) = rot k hk 2 (sh k hk s x) i := by
    have hr := congrFun (sh_rot hk s 2 x) i
    simpa [sh] using hr
  rw [hix, hrot]

lemma sh_chi {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) :
    sh k hk s (chi k hk x) = chi k hk (sh k hk s x) := by
  funext i
  simp only [sh, chi]
  have h1 : ix k hk ((ix k hk (s + i.val)).val + 1) = ix k hk (s + (ix k hk (i.val + 1)).val) := by
    change ix k hk ((s + i.val) % k + 1) = ix k hk (s + (i.val + 1) % k)
    rw [ix_add_mod_left, ix_add_mod_right, Nat.add_assoc]
  have h2 : ix k hk ((ix k hk (s + i.val)).val + 2) = ix k hk (s + (ix k hk (i.val + 2)).val) := by
    change ix k hk ((s + i.val) % k + 2) = ix k hk (s + (i.val + 2) % k)
    rw [ix_add_mod_left, ix_add_mod_right, Nat.add_assoc]
  rw [h1, h2]

lemma mix_add {k : ℕ} (hk : 0 < k) (x y : W k) :
    mix k hk (x + y) = mix k hk x + mix k hk y := by
  funext i
  simp only [mix, Pi.add_apply, rot_add]
  ring

lemma mix_rot {k : ℕ} (hk : 0 < k) (r : ℕ) (x : W k) :
    mix k hk (rot k hk r x) = rot k hk r (mix k hk x) := by
  rw [rot_eq_sh, rot_eq_sh, sh_mix]

lemma mix_eq_zero_imp {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0)
    (x : W k) (hx : mix k hk x = 0) : x = 0 := by
  let u : ℕ → ZMod 2 := fun n => x (ix k hk n)
  have hu_k : ∀ n, u (n + k) = u n := fun n => by simp [u, ix_add_k]
  have hrec : ∀ n, u n + u (n + 2) + u (n + 4) = 0 := by
    intro n
    have h0 : mix k hk x (ix k hk (n + 2)) = 0 := congrFun hx (ix k hk (n + 2))
    simp only [mix] at h0
    rw [rot_ix_sub2k hk (by omega)] at h0
    have h1 : (ix k hk (n + 2)).val + 2 = (n + 2) % k + 2 := rfl
    rw [h1, ix_add_mod_left] at h0
    have h2 : n + 2 + 2 * k - 2 = n + 2 * k := by omega
    rw [h2, ix_add_mul_k] at h0
    have h3 : n + 2 + 2 = n + 4 := by omega
    rw [h3] at h0
    calc u n + u (n + 2) + u (n + 4)
        = u (n + 2) + u (n + 4) + u n := by ring
      _ = 0 := h0
  have hu6 : ∀ n, u (n + 6) = u n := by
    intro n
    have h1 := hrec n
    have h2 := hrec (n + 2)
    have h3 : (u n + u (n + 2) + u (n + 4)) + (u (n + 2) + u (n + 4) + u (n + 6)) = 0 := by
      rw [h1, h2]; simp
    have h4 : u n + u (n + 6) = 0 := by
      have heq : (u n + u (n + 2) + u (n + 4)) + (u (n + 2) + u (n + 4) + u (n + 6)) =
          (u n + u (n + 6)) + (u (n + 2) + u (n + 2)) + (u (n + 4) + u (n + 4)) := by ring
      rw [h3, zmod2_add_self, zmod2_add_self, add_zero, add_zero] at heq
      exact heq.symm
    exact ((zmod2_add_eq_zero (u n) (u (n + 6))).mp h4).symm
  have hu6q : ∀ q n, u (n + 6 * q) = u n := by
    intro q
    induction q with
    | zero => intro n; simp
    | succ q ih =>
      intro n
      have heq : n + 6 * (q + 1) = (n + 6 * q) + 6 := by omega
      rw [heq, hu6, ih]
  have hu_mod6 : ∀ n, u (n + k % 6) = u n := by
    intro n
    have heq : n + k = (n + k % 6) + 6 * (k / 6) := by omega
    rw [← hu6q (k / 6) (n + k % 6), ← heq, hu_k]
  have hu_step2 : ∀ n, u (n + 2) = u n := by
    have hcases : k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
    rcases hcases with h1 | h2 | h4 | h5
    · intro n
      have hu1 : ∀ m, u (m + 1) = u m := fun m => by simpa [h1] using hu_mod6 m
      rw [show n + 2 = (n + 1) + 1 by omega, hu1, hu1]
    · intro n
      simpa [h2] using hu_mod6 n
    · intro n
      have hu4 : ∀ m, u (m + 4) = u m := fun m => by simpa [h4] using hu_mod6 m
      rw [← hu4 (n + 2), show n + 2 + 4 = n + 6 by omega, hu6]
    · intro n
      have hu5 : ∀ m, u (m + 5) = u m := fun m => by simpa [h5] using hu_mod6 m
      have hu1 : ∀ m, u (m + 1) = u m := fun m => by
        rw [← hu5 (m + 1), show m + 1 + 5 = m + 6 by omega, hu6]
      rw [show n + 2 = (n + 1) + 1 by omega, hu1, hu1]
  funext i
  have h0 := hrec i.val
  have h1 : u (i.val + 2) = u i.val := hu_step2 i.val
  have h2 : u (i.val + 4) = u i.val := by
    rw [show i.val + 4 = (i.val + 2) + 2 by omega, hu_step2, hu_step2]
  rw [h1, h2] at h0
  have h3 : u i.val = 0 := by
    calc u i.val = u i.val + (u i.val + u i.val) := by rw [zmod2_add_self, add_zero]
      _ = u i.val + u i.val + u i.val := by ring
      _ = 0 := h0
  simpa [u, ix_val] using h3

lemma mix_bijective {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0) :
    Function.Bijective (mix k hk) := by
  apply Function.Injective.bijective_of_finite
  intro x y hxy
  have h0 : mix k hk (x + y) = 0 := by
    rw [mix_add, hxy, w_add_self]
  exact (w_add_eq_zero x y).mp (mix_eq_zero_imp hk hk7 hk3 (x + y) h0)

noncomputable def mixEquiv {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0) : W k ≃ W k :=
  Equiv.ofBijective (mix k hk) (mix_bijective hk hk7 hk3)

lemma sh_F {k : ℕ} (hk : 0 < k) (s : ℕ) (z gm y : W k) :
    sh k hk s (F k hk z gm y) = F k hk (sh k hk s z) (sh k hk s gm) (sh k hk s y) := by
  have hF : F k hk z gm y =
      chi k hk (mix k hk (chi k hk y) + gm) +
      chi k hk (mix k hk (chi k hk (y + rot k hk 3 z)) + gm + rot k hk 4 z) := rfl
  rw [hF, sh_add, sh_chi, sh_chi, sh_add, sh_add, sh_add, sh_mix, sh_mix, sh_chi, sh_chi,
    sh_add, sh_rot, sh_rot]
  rfl

lemma F_eq_sh_zero {k : ℕ} (hk : 0 < k) (z gm y : W k) (i : Fin k) :
    F k hk z gm y i = F k hk (sh k hk i.val z) (sh k hk i.val gm) (sh k hk i.val y) ⟨0, hk⟩ := by
  have h := congrFun (sh_F hk i.val z gm y) ⟨0, hk⟩
  simpa [sh, ix_val] using h

def chiB (a b c : Bool) : Bool :=
  xor a ((!b) && c)

def flocalB (z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 y0 y1 y2 y3 y4 y5 y6 y7 y8 : Bool) : Bool :=
  let c10 := chiB y0 y1 y2
  let c11 := chiB y1 y2 y3
  let c12 := chiB y2 y3 y4
  let c13 := chiB y3 y4 y5
  let c14 := chiB y4 y5 y6
  let c15 := chiB y5 y6 y7
  let c16 := chiB y6 y7 y8
  let c20 := chiB y0 (xor y1 z0) (xor y2 z1)
  let c21 := chiB (xor y1 z0) (xor y2 z1) (xor y3 z2)
  let c22 := chiB (xor y2 z1) (xor y3 z2) (xor y4 z3)
  let c23 := chiB (xor y3 z2) (xor y4 z3) (xor y5 z4)
  let c24 := chiB (xor y4 z3) (xor y5 z4) (xor y6 z5)
  let c25 := chiB (xor y5 z4) (xor y6 z5) (xor y7 z6)
  let c26 := chiB (xor y6 z5) (xor y7 z6) (xor y8 z7)
  let a0 := xor (xor (xor c12 c14) c10) g0
  let a1 := xor (xor (xor c13 c15) c11) g1
  let a2 := xor (xor (xor c14 c16) c12) g2
  let b0 := xor (xor (xor (xor c22 c24) c20) g0) z0
  let b1 := xor (xor (xor (xor c23 c25) c21) g1) z1
  let b2 := xor (xor (xor (xor c24 c26) c22) g2) z2
  xor (chiB a0 a1 a2) (chiB b0 b1 b2)

lemma flocalB_zero_z (g0 g1 g2 y0 y1 y2 y3 y4 y5 y6 y7 y8 : Bool) :
    flocalB false false false false false false false false g0 g1 g2 y0 y1 y2 y3 y4 y5 y6 y7 y8 = false := by
  simp [flocalB]

lemma z2b_chi_ix {k : ℕ} (hk : 0 < k) (y : W k) (n : ℕ) :
    z2b (chi k hk y (ix k hk n)) =
      chiB (z2b (y (ix k hk n))) (z2b (y (ix k hk (n + 1)))) (z2b (y (ix k hk (n + 2)))) := by
  simp only [chi, chiB, z2b_add, z2b_mul, show z2b 1 = true by decide, Bool.true_xor]
  have h1 : ix k hk ((ix k hk n).val + 1) = ix k hk (n + 1) := by
    change ix k hk (n % k + 1) = ix k hk (n + 1)
    exact ix_add_mod_left hk n 1
  have h2 : ix k hk ((ix k hk n).val + 2) = ix k hk (n + 2) := by
    change ix k hk (n % k + 2) = ix k hk (n + 2)
    exact ix_add_mod_left hk n 2
  rw [h1, h2]

lemma xor_shift_e (A0 A12 u224 u20 g0 w0 B12 e : Bool) :
    xor (xor A0 A12) (xor (xor (xor (xor u224 (xor u20 e)) g0) w0) B12) =
      xor (xor (xor A0 A12) (xor (xor (xor (xor u224 u20) g0) w0) B12)) e := by
  cases A0 <;> cases A12 <;> cases u224 <;> cases u20 <;>
    cases g0 <;> cases w0 <;> cases B12 <;> cases e <;> rfl

lemma z2b_F_eq {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (z gm y : W k) :
    let zb := fun m => z2b (z (ix k hk (2 * k - 4 + m)))
    let gb := fun u => z2b (gm (ix k hk u))
    let yb := fun t => z2b (y (ix k hk (2 * k - 2 + t)))
    z2b (F k hk z gm y ⟨0, hk⟩) =
      xor (flocalB (zb 0) (zb 1) (zb 2) (zb 3) (zb 4) (zb 5) (zb 6) (zb 7)
        (gb 0) (gb 1) (gb 2)
        (yb 0) (yb 1) (yb 2) (yb 3) (yb 4) (yb 5) (yb 6) (yb 7) (yb 8))
        (z2b (z (ix k hk (2 * k - 5)))) := by
  intro zb gb yb
  have hi0 : (⟨0, hk⟩ : Fin k) = ix k hk 0 := by apply Fin.ext; simp [ix]
  have hix_add : ∀ a b, ix k hk ((ix k hk a).val + b) = ix k hk (a + b) := fun a b =>
    ix_add_mod_left hk a b
  have hrot3 : ∀ t, rot k hk 3 z (ix k hk (2 * k - 2 + t)) =
      if t = 0 then z (ix k hk (2 * k - 5)) else z (ix k hk (2 * k - 4 + (t - 1))) := by
    intro t
    rw [rot_ix_sub2k hk (by omega)]
    split_ifs with ht
    · subst ht
      have h1 : 2 * k - 2 + 0 + 2 * k - 3 = (2 * k - 5) + 2 * k := by omega
      rw [h1, ix_add_mul_k]
    · have h1 : 2 * k - 2 + t + 2 * k - 3 = (2 * k - 4 + (t - 1)) + 2 * k := by omega
      rw [h1, ix_add_mul_k]
  have hrot4 : ∀ u, rot k hk 4 z (ix k hk u) = z (ix k hk (2 * k - 4 + u)) := by
    intro u
    rw [rot_ix_sub2k hk (by omega)]
    have h1 : u + 2 * k - 4 = 2 * k - 4 + u := by omega
    rw [h1]
  have hmix_ix : ∀ (v : W k) (u : ℕ),
      mix k hk v (ix k hk u) =
        v (ix k hk (2 * k - 2 + (u + 2))) +
        v (ix k hk (2 * k - 2 + (u + 4))) +
        v (ix k hk (2 * k - 2 + u)) := by
    intro v u
    simp only [mix]
    rw [hix_add, rot_ix_sub2k hk (by omega)]
    have h1 : 2 * k - 2 + (u + 2) = u + 2 * k := by omega
    have h2 : 2 * k - 2 + (u + 4) = (u + 2) + 2 * k := by omega
    have h3 : u + 2 * k - 2 = 2 * k - 2 + u := by omega
    rw [h1, h2, h3, ix_add_mul_k, ix_add_mul_k]
  have hc1 : ∀ r, z2b (chi k hk y (ix k hk (2 * k - 2 + r))) =
      chiB (yb r) (yb (r + 1)) (yb (r + 2)) := by
    intro r
    rw [z2b_chi_ix]
    simp only [yb, Nat.add_assoc]
  have hc20 : z2b (chi k hk (y + rot k hk 3 z) (ix k hk (2 * k - 2 + 0))) =
      xor (chiB (yb 0) (xor (yb 1) (zb 0)) (xor (yb 2) (zb 1)))
        (z2b (z (ix k hk (2 * k - 5)))) := by
    rw [z2b_chi_ix]
    simp only [Pi.add_apply, z2b_add, Nat.add_assoc]
    rw [hrot3 0, hrot3 1, hrot3 2]
    simp only [ite_true, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide, ite_false]
    simp only [yb, zb, chiB]
    cases z2b (y (ix k hk (2 * k - 2 + 0))) <;>
    cases z2b (z (ix k hk (2 * k - 5))) <;>
    cases (!(xor (z2b (y (ix k hk (2 * k - 2 + 1)))) (z2b (z (ix k hk (2 * k - 4 + 0))))) &&
      xor (z2b (y (ix k hk (2 * k - 2 + 2)))) (z2b (z (ix k hk (2 * k - 4 + 1))))) <;>
    rfl
  have hc2 : ∀ r, 1 ≤ r →
      z2b (chi k hk (y + rot k hk 3 z) (ix k hk (2 * k - 2 + r))) =
        chiB (xor (yb r) (zb (r - 1))) (xor (yb (r + 1)) (zb r)) (xor (yb (r + 2)) (zb (r + 1))) := by
    intro r hr
    rw [z2b_chi_ix]
    simp only [Pi.add_apply, z2b_add, Nat.add_assoc]
    rw [hrot3 r, hrot3 (r + 1), hrot3 (r + 2)]
    have hr0 : r ≠ 0 := by omega
    have hr1 : r + 1 ≠ 0 := by omega
    have hr2 : r + 2 ≠ 0 := by omega
    simp only [hr0, hr1, hr2, ite_false, Nat.add_sub_cancel]
    rfl
  simp only [F, hi0, z2b_add]
  rw [z2b_chi_ix, z2b_chi_ix]
  simp only [Pi.add_apply, z2b_add, hmix_ix, hrot4, Nat.reduceAdd]
  rw [hc1 0, hc1 1, hc1 2, hc1 3, hc1 4, hc1 5, hc1 6]
  rw [hc20, hc2 1 (by decide), hc2 2 (by decide), hc2 3 (by decide),
      hc2 4 (by decide), hc2 5 (by decide), hc2 6 (by decide)]
  simp only [Nat.reduceAdd, Nat.reduceSub, flocalB, chiB]
  exact xor_shift_e _ _ _ _ _ _ _ _

lemma z2b_F_add_F0 {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (z gm y : W k) :
    let zb := fun m => z2b (z (ix k hk (2 * k - 4 + m)))
    let gb := fun u => z2b (gm (ix k hk u))
    let yb := fun t => z2b (y (ix k hk (2 * k - 2 + t)))
    z2b (F k hk z gm y ⟨0, hk⟩ + F k hk z gm 0 ⟨0, hk⟩) =
      xor (flocalB (zb 0) (zb 1) (zb 2) (zb 3) (zb 4) (zb 5) (zb 6) (zb 7)
        (gb 0) (gb 1) (gb 2)
        (yb 0) (yb 1) (yb 2) (yb 3) (yb 4) (yb 5) (yb 6) (yb 7) (yb 8))
        (flocalB (zb 0) (zb 1) (zb 2) (zb 3) (zb 4) (zb 5) (zb 6) (zb 7)
          (gb 0) (gb 1) (gb 2)
          false false false false false false false false false) := by
  intro zb gb yb
  rw [z2b_add, z2b_F_eq hk hk7 z gm y, z2b_F_eq hk hk7 z gm 0]
  simp only [Pi.zero_apply, z2b_zero]
  generalize flocalB (zb 0) (zb 1) (zb 2) (zb 3) (zb 4) (zb 5) (zb 6) (zb 7)
    (gb 0) (gb 1) (gb 2) (yb 0) (yb 1) (yb 2) (yb 3) (yb 4) (yb 5) (yb 6) (yb 7) (yb 8) = a
  generalize flocalB (zb 0) (zb 1) (zb 2) (zb 3) (zb 4) (zb 5) (zb 6) (zb 7)
    (gb 0) (gb 1) (gb 2) false false false false false false false false false = b
  generalize z2b (z (ix k hk (2 * k - 5))) = e
  cases a <;> cases b <;> cases e <;> rfl

lemma F_zero_of_z8_zero {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (z gm y : W k)
    (hz : ∀ m < 8, z (ix k hk (2 * k - 4 + m)) = 0) :
    F k hk z gm y ⟨0, hk⟩ = z (ix k hk (2 * k - 5)) := by
  have h := z2b_F_eq hk hk7 z gm y
  have hzb : ∀ m < 8, z2b (z (ix k hk (2 * k - 4 + m))) = false := fun m hm => by
    rw [hz m hm, z2b_zero]
  simp only [hzb 0 (by decide), hzb 1 (by decide), hzb 2 (by decide), hzb 3 (by decide),
    hzb 4 (by decide), hzb 5 (by decide), hzb 6 (by decide), hzb 7 (by decide),
    flocalB_zero_z, Bool.false_xor] at h
  have h2 := congrArg b2z h
  simpa [b2z_z2b] using h2

lemma F_add_rot7_of_z8_zero {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (δ gm y : W k)
    (hz : ∀ m < 8, mix k hk δ (ix k hk (2 * k - 4 + m)) = 0) :
    F k hk (mix k hk δ) gm y ⟨0, hk⟩ + rot k hk 7 δ ⟨0, hk⟩ = δ (ix k hk (2 * k - 1)) := by
  rw [F_zero_of_z8_zero hk hk7 (mix k hk δ) gm y hz]
  have hi0 : (⟨0, hk⟩ : Fin k) = ix k hk 0 := by apply Fin.ext; simp [ix]
  rw [hi0, rot_ix_sub2k hk (by omega)]
  have hmix5 : mix k hk δ (ix k hk (2 * k - 5)) =
      δ (ix k hk (2 * k - 5)) + δ (ix k hk (2 * k - 3)) + δ (ix k hk (2 * k - 7)) := by
    simp only [mix]
    rw [rot_ix_sub2k hk (by omega)]
    have h1 : (ix k hk (2 * k - 5)).val + 2 = (2 * k - 5) % k + 2 := rfl
    rw [h1, ix_add_mod_left]
    have h2 : 2 * k - 5 + 2 = 2 * k - 3 := by omega
    have h3 : 2 * k - 5 + 2 * k - 2 = (2 * k - 7) + 2 * k := by omega
    rw [h2, h3, ix_add_mul_k]
  have hmix3 : mix k hk δ (ix k hk (2 * k - 3)) =
      δ (ix k hk (2 * k - 3)) + δ (ix k hk (2 * k - 1)) + δ (ix k hk (2 * k - 5)) := by
    simp only [mix]
    rw [rot_ix_sub2k hk (by omega)]
    have h1 : (ix k hk (2 * k - 3)).val + 2 = (2 * k - 3) % k + 2 := rfl
    rw [h1, ix_add_mod_left]
    have h2 : 2 * k - 3 + 2 = 2 * k - 1 := by omega
    have h3 : 2 * k - 3 + 2 * k - 2 = (2 * k - 5) + 2 * k := by omega
    rw [h2, h3, ix_add_mul_k]
  have hz1 : mix k hk δ (ix k hk (2 * k - 3)) = 0 := by
    have h := hz 1 (by decide)
    have heq : 2 * k - 4 + 1 = 2 * k - 3 := by omega
    rwa [heq] at h
  rw [hmix5, show 0 + 2 * k - 7 = 2 * k - 7 by omega]
  rw [hmix3] at hz1
  have hsum : δ (ix k hk (2 * k - 5)) + δ (ix k hk (2 * k - 3)) + δ (ix k hk (2 * k - 1)) = 0 := by
    calc δ (ix k hk (2 * k - 5)) + δ (ix k hk (2 * k - 3)) + δ (ix k hk (2 * k - 1))
        = δ (ix k hk (2 * k - 3)) + δ (ix k hk (2 * k - 1)) + δ (ix k hk (2 * k - 5)) := by ring
      _ = 0 := hz1
  have heq : δ (ix k hk (2 * k - 5)) + δ (ix k hk (2 * k - 3)) = δ (ix k hk (2 * k - 1)) :=
    (zmod2_add_eq_zero _ _).mp hsum
  calc δ (ix k hk (2 * k - 5)) + δ (ix k hk (2 * k - 3)) + δ (ix k hk (2 * k - 7)) +
        δ (ix k hk (2 * k - 7))
      = (δ (ix k hk (2 * k - 5)) + δ (ix k hk (2 * k - 3))) +
        (δ (ix k hk (2 * k - 7)) + δ (ix k hk (2 * k - 7))) := by ring
    _ = δ (ix k hk (2 * k - 1)) + 0 := by rw [heq, zmod2_add_self]
    _ = δ (ix k hk (2 * k - 1)) := by ring

def flocalBMask9 (z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 : Bool) (m : ℕ) : Bool :=
  flocalB z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2
    (m.testBit 0) (m.testBit 1) (m.testBit 2) (m.testBit 3) (m.testBit 4)
    (m.testBit 5) (m.testBit 6) (m.testBit 7) (m.testBit 8)

def flocalBMask7 (z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 : Bool) (m : ℕ) : Bool :=
  flocalB z3 z4 z5 z6 z0 z1 z2 z3 g0 g1 g2
    (m.testBit 5) (m.testBit 6) (m.testBit 0) (m.testBit 1) (m.testBit 2)
    (m.testBit 3) (m.testBit 4) (m.testBit 5) (m.testBit 6)

def flocalBMask8 (z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 : Bool) (m : ℕ) : Bool :=
  flocalB z4 z5 z6 z7 z0 z1 z2 z3 g0 g1 g2
    (m.testBit 6) (m.testBit 7) (m.testBit 0) (m.testBit 1) (m.testBit 2)
    (m.testBit 3) (m.testBit 4) (m.testBit 5) (m.testBit 6)

def allB1 (f : Bool → Bool) : Bool := f false && f true
def allB2 (f : Bool → Bool → Bool) : Bool := allB1 fun a => allB1 (f a)
def allB3 (f : Bool → Bool → Bool → Bool) : Bool := allB1 fun a => allB2 (f a)
def allB4 (f : Bool → Bool → Bool → Bool → Bool) : Bool := allB2 fun a b => allB2 (f a b)
def allB7 (f : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool) : Bool :=
  allB3 fun a b c => allB4 (f a b c)
def allB8 (f : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool) : Bool :=
  allB4 fun a b c d => allB4 (f a b c d)

lemma allB1_spec {f : Bool → Bool} (h : allB1 f = true) (a : Bool) : f a = true := by
  cases a <;> simp_all [allB1]

lemma allB2_spec {f : Bool → Bool → Bool} (h : allB2 f = true) (a b : Bool) : f a b = true :=
  allB1_spec (allB1_spec h a) b

lemma allB3_spec {f : Bool → Bool → Bool → Bool} (h : allB3 f = true) (a b c : Bool) :
    f a b c = true :=
  allB2_spec (allB1_spec h a) b c

lemma allB4_spec {f : Bool → Bool → Bool → Bool → Bool} (h : allB4 f = true) (a b c d : Bool) :
    f a b c d = true :=
  allB2_spec (allB2_spec h a b) c d

lemma allB7_spec {f : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool}
    (h : allB7 f = true) (a b c d e x y : Bool) : f a b c d e x y = true :=
  allB4_spec (allB3_spec h a b c) d e x y

lemma allB8_spec {f : Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool}
    (h : allB8 f = true) (a b c d e x y z : Bool) : f a b c d e x y z = true :=
  allB4_spec (allB4_spec h a b c d) e x y z

def checkW9 (z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 : Bool) : Bool :=
  let f0 := flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0
  if (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 318 == f0) &&
     (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 316 == f0) &&
     (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 34 == f0) &&
     (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 348 == f0) &&
     (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 20 == f0) &&
     (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 24 == f0) &&
     (flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 28 == f0)
  then !(z0 || z1 || z2 || z3 || z4 || z5 || z6 || z7)
  else true

def checkW7 (z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 : Bool) : Bool :=
  let f0 := flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0
  if (flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 79 == f0) &&
     (flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 88 == f0) &&
     (flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 25 == f0) &&
     (flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 53 == f0) &&
     (flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 94 == f0) &&
     (flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 33 == f0)
  then !(z0 || z1 || z2 || z3 || z4 || z5 || z6)
  else true

def checkW8 (z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 : Bool) : Bool :=
  let f0 := flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0
  if (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 207 == f0) &&
     (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 79 == f0) &&
     (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 12 == f0) &&
     (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 71 == f0) &&
     (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 3 == f0) &&
     (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 6 == f0) &&
     (flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 55 == f0)
  then !(z0 || z1 || z2 || z3 || z4 || z5 || z6 || z7)
  else true

set_option maxHeartbeats 800000 in
theorem checkW9_ok :
    allB8 (fun z0 z1 z2 z3 z4 z5 z6 z7 => allB3 (checkW9 z0 z1 z2 z3 z4 z5 z6 z7)) = true := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem checkW7_ok :
    allB7 (fun z0 z1 z2 z3 z4 z5 z6 => allB3 (checkW7 z0 z1 z2 z3 z4 z5 z6)) = true := by
  decide +kernel

set_option maxHeartbeats 800000 in
theorem checkW8_ok :
    allB8 (fun z0 z1 z2 z3 z4 z5 z6 z7 => allB3 (checkW8 z0 z1 z2 z3 z4 z5 z6 z7)) = true := by
  decide +kernel

theorem witness9_bool :
    ∀ z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 : Bool,
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 318 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 316 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 34 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 348 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 20 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 24 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 28 = flocalBMask9 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      z0 = false ∧ z1 = false ∧ z2 = false ∧ z3 = false ∧
      z4 = false ∧ z5 = false ∧ z6 = false ∧ z7 = false := by
  intro z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 h1 h2 h3 h4 h5 h6 h7
  have hc := allB3_spec (allB8_spec checkW9_ok z0 z1 z2 z3 z4 z5 z6 z7) g0 g1 g2
  simp only [checkW9, h1, h2, h3, h4, h5, h6, h7, beq_self_eq_true, Bool.and_self, ite_true,
    Bool.not_eq_true', Bool.or_eq_false_iff] at hc
  tauto

theorem witness7_bool :
    ∀ z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 : Bool,
      flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 79 = flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0 →
      flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 88 = flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0 →
      flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 25 = flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0 →
      flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 53 = flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0 →
      flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 94 = flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0 →
      flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 33 = flocalBMask7 z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 0 →
      z0 = false ∧ z1 = false ∧ z2 = false ∧ z3 = false ∧
      z4 = false ∧ z5 = false ∧ z6 = false := by
  intro z0 z1 z2 z3 z4 z5 z6 g0 g1 g2 h1 h2 h3 h4 h5 h6
  have hc := allB3_spec (allB7_spec checkW7_ok z0 z1 z2 z3 z4 z5 z6) g0 g1 g2
  simp only [checkW7, h1, h2, h3, h4, h5, h6, beq_self_eq_true, Bool.and_self, ite_true,
    Bool.not_eq_true', Bool.or_eq_false_iff] at hc
  tauto

theorem witness8_bool :
    ∀ z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 : Bool,
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 207 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 79 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 12 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 71 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 3 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 6 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 55 = flocalBMask8 z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 0 →
      z0 = false ∧ z1 = false ∧ z2 = false ∧ z3 = false ∧
      z4 = false ∧ z5 = false ∧ z6 = false ∧ z7 = false := by
  intro z0 z1 z2 z3 z4 z5 z6 z7 g0 g1 g2 h1 h2 h3 h4 h5 h6 h7
  have hc := allB3_spec (allB8_spec checkW8_ok z0 z1 z2 z3 z4 z5 z6 z7) g0 g1 g2
  simp only [checkW8, h1, h2, h3, h4, h5, h6, h7, beq_self_eq_true, Bool.and_self, ite_true,
    Bool.not_eq_true', Bool.or_eq_false_iff] at hc
  tauto

lemma z8_zero_of_F_const_ge9 {k : ℕ} (hk : 0 < k) (hk9 : 9 ≤ k) (z gm : W k)
    (hF : ∀ y : W k, F k hk z gm y ⟨0, hk⟩ + F k hk z gm 0 ⟨0, hk⟩ = 0) :
    ∀ m < 8, z (ix k hk (2 * k - 4 + m)) = 0 := by
  have hk7 : 7 ≤ k := by omega
  have hmask : ∀ mask : ℕ,
      flocalBMask9
        (z2b (z (ix k hk (2 * k - 4 + 0)))) (z2b (z (ix k hk (2 * k - 4 + 1))))
        (z2b (z (ix k hk (2 * k - 4 + 2)))) (z2b (z (ix k hk (2 * k - 4 + 3))))
        (z2b (z (ix k hk (2 * k - 4 + 4)))) (z2b (z (ix k hk (2 * k - 4 + 5))))
        (z2b (z (ix k hk (2 * k - 4 + 6)))) (z2b (z (ix k hk (2 * k - 4 + 7))))
        (z2b (gm (ix k hk 0))) (z2b (gm (ix k hk 1))) (z2b (gm (ix k hk 2))) mask =
      flocalBMask9
        (z2b (z (ix k hk (2 * k - 4 + 0)))) (z2b (z (ix k hk (2 * k - 4 + 1))))
        (z2b (z (ix k hk (2 * k - 4 + 2)))) (z2b (z (ix k hk (2 * k - 4 + 3))))
        (z2b (z (ix k hk (2 * k - 4 + 4)))) (z2b (z (ix k hk (2 * k - 4 + 5))))
        (z2b (z (ix k hk (2 * k - 4 + 6)))) (z2b (z (ix k hk (2 * k - 4 + 7))))
        (z2b (gm (ix k hk 0))) (z2b (gm (ix k hk 1))) (z2b (gm (ix k hk 2))) 0 := by
    intro mask
    let y : W k := fun i =>
      if i.val + 2 < k then b2z (mask.testBit (i.val + 2))
      else b2z (mask.testBit (i.val + 2 - k))
    have hy : ∀ t < 9, z2b (y (ix k hk (2 * k - 2 + t))) = mask.testBit t := by
      intro t ht
      by_cases ht2 : t < 2
      · have hval : (ix k hk (2 * k - 2 + t)).val = k - 2 + t := by
          simp only [ix]
          have h1 : 2 * k - 2 + t = (k - 2 + t) + k := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        simp only [y, hval]
        have hnot : ¬ (k - 2 + t + 2 < k) := by omega
        have hsub : k - 2 + t + 2 - k = t := by omega
        rw [if_neg hnot, hsub, z2b_b2z]
      · have hval : (ix k hk (2 * k - 2 + t)).val = t - 2 := by
          simp only [ix]
          have h1 : 2 * k - 2 + t = (t - 2) + 2 * k := by omega
          rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
        simp only [y, hval]
        have hlt : t - 2 + 2 < k := by omega
        have hadd : t - 2 + 2 = t := by omega
        rw [if_pos hlt, hadd, z2b_b2z]
    have h0 := z2b_F_add_F0 hk hk7 z gm y
    dsimp only at h0
    rw [hF y, z2b_zero] at h0
    rw [hy 0 (by decide), hy 1 (by decide), hy 2 (by decide), hy 3 (by decide),
        hy 4 (by decide), hy 5 (by decide), hy 6 (by decide), hy 7 (by decide),
        hy 8 (by decide)] at h0
    have hxor : ∀ a b : Bool, false = xor a b → a = b := by
      intro a b; cases a <;> cases b <;> decide
    simpa [flocalBMask9] using hxor _ _ h0
  have hw := witness9_bool
    (z2b (z (ix k hk (2 * k - 4 + 0)))) (z2b (z (ix k hk (2 * k - 4 + 1))))
    (z2b (z (ix k hk (2 * k - 4 + 2)))) (z2b (z (ix k hk (2 * k - 4 + 3))))
    (z2b (z (ix k hk (2 * k - 4 + 4)))) (z2b (z (ix k hk (2 * k - 4 + 5))))
    (z2b (z (ix k hk (2 * k - 4 + 6)))) (z2b (z (ix k hk (2 * k - 4 + 7))))
    (z2b (gm (ix k hk 0))) (z2b (gm (ix k hk 1))) (z2b (gm (ix k hk 2)))
    (hmask 318) (hmask 316) (hmask 34) (hmask 348) (hmask 20) (hmask 24) (hmask 28)
  intro m hm
  rcases hw with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  interval_cases m
  · exact (z2b_eq_false _).mp h0
  · exact (z2b_eq_false _).mp h1
  · exact (z2b_eq_false _).mp h2
  · exact (z2b_eq_false _).mp h3
  · exact (z2b_eq_false _).mp h4
  · exact (z2b_eq_false _).mp h5
  · exact (z2b_eq_false _).mp h6
  · exact (z2b_eq_false _).mp h7

lemma z8_zero_of_F_const_7 (hk : 0 < 7) (z gm : W 7)
    (hF : ∀ y : W 7, F 7 hk z gm y ⟨0, hk⟩ + F 7 hk z gm 0 ⟨0, hk⟩ = 0) :
    ∀ m < 8, z (ix 7 hk (2 * 7 - 4 + m)) = 0 := by
  have hmask : ∀ mask : ℕ,
      flocalBMask7
        (z2b (z ⟨0, by decide⟩)) (z2b (z ⟨1, by decide⟩)) (z2b (z ⟨2, by decide⟩))
        (z2b (z ⟨3, by decide⟩)) (z2b (z ⟨4, by decide⟩)) (z2b (z ⟨5, by decide⟩))
        (z2b (z ⟨6, by decide⟩))
        (z2b (gm ⟨0, by decide⟩)) (z2b (gm ⟨1, by decide⟩)) (z2b (gm ⟨2, by decide⟩)) mask =
      flocalBMask7
        (z2b (z ⟨0, by decide⟩)) (z2b (z ⟨1, by decide⟩)) (z2b (z ⟨2, by decide⟩))
        (z2b (z ⟨3, by decide⟩)) (z2b (z ⟨4, by decide⟩)) (z2b (z ⟨5, by decide⟩))
        (z2b (z ⟨6, by decide⟩))
        (z2b (gm ⟨0, by decide⟩)) (z2b (gm ⟨1, by decide⟩)) (z2b (gm ⟨2, by decide⟩)) 0 := by
    intro mask
    let y : W 7 := fun i => b2z (mask.testBit i.val)
    have h0 := z2b_F_add_F0 hk (by decide) z gm y
    dsimp only at h0
    rw [hF y, z2b_zero] at h0
    have hxor : ∀ a b : Bool, false = xor a b → a = b := by
      intro a b; cases a <;> cases b <;> decide
    have h1 := hxor _ _ h0
    simpa [flocalBMask7, y, ix, z2b_b2z] using h1
  have hw := witness7_bool
    (z2b (z ⟨0, by decide⟩)) (z2b (z ⟨1, by decide⟩)) (z2b (z ⟨2, by decide⟩))
    (z2b (z ⟨3, by decide⟩)) (z2b (z ⟨4, by decide⟩)) (z2b (z ⟨5, by decide⟩))
    (z2b (z ⟨6, by decide⟩))
    (z2b (gm ⟨0, by decide⟩)) (z2b (gm ⟨1, by decide⟩)) (z2b (gm ⟨2, by decide⟩))
    (hmask 79) (hmask 88) (hmask 25) (hmask 53) (hmask 94) (hmask 33)
  rcases hw with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  intro m hm
  interval_cases m <;>
    simp only [ix] <;>
    first
    | exact (z2b_eq_false _).mp h0
    | exact (z2b_eq_false _).mp h1
    | exact (z2b_eq_false _).mp h2
    | exact (z2b_eq_false _).mp h3
    | exact (z2b_eq_false _).mp h4
    | exact (z2b_eq_false _).mp h5
    | exact (z2b_eq_false _).mp h6

lemma z8_zero_of_F_const_8 (hk : 0 < 8) (z gm : W 8)
    (hF : ∀ y : W 8, F 8 hk z gm y ⟨0, hk⟩ + F 8 hk z gm 0 ⟨0, hk⟩ = 0) :
    ∀ m < 8, z (ix 8 hk (2 * 8 - 4 + m)) = 0 := by
  have hmask : ∀ mask : ℕ,
      flocalBMask8
        (z2b (z ⟨0, by decide⟩)) (z2b (z ⟨1, by decide⟩)) (z2b (z ⟨2, by decide⟩))
        (z2b (z ⟨3, by decide⟩)) (z2b (z ⟨4, by decide⟩)) (z2b (z ⟨5, by decide⟩))
        (z2b (z ⟨6, by decide⟩)) (z2b (z ⟨7, by decide⟩))
        (z2b (gm ⟨0, by decide⟩)) (z2b (gm ⟨1, by decide⟩)) (z2b (gm ⟨2, by decide⟩)) mask =
      flocalBMask8
        (z2b (z ⟨0, by decide⟩)) (z2b (z ⟨1, by decide⟩)) (z2b (z ⟨2, by decide⟩))
        (z2b (z ⟨3, by decide⟩)) (z2b (z ⟨4, by decide⟩)) (z2b (z ⟨5, by decide⟩))
        (z2b (z ⟨6, by decide⟩)) (z2b (z ⟨7, by decide⟩))
        (z2b (gm ⟨0, by decide⟩)) (z2b (gm ⟨1, by decide⟩)) (z2b (gm ⟨2, by decide⟩)) 0 := by
    intro mask
    let y : W 8 := fun i => b2z (mask.testBit i.val)
    have h0 := z2b_F_add_F0 hk (by decide) z gm y
    dsimp only at h0
    rw [hF y, z2b_zero] at h0
    have hxor : ∀ a b : Bool, false = xor a b → a = b := by
      intro a b; cases a <;> cases b <;> decide
    have h1 := hxor _ _ h0
    simpa [flocalBMask8, y, ix, z2b_b2z] using h1
  have hw := witness8_bool
    (z2b (z ⟨0, by decide⟩)) (z2b (z ⟨1, by decide⟩)) (z2b (z ⟨2, by decide⟩))
    (z2b (z ⟨3, by decide⟩)) (z2b (z ⟨4, by decide⟩)) (z2b (z ⟨5, by decide⟩))
    (z2b (z ⟨6, by decide⟩)) (z2b (z ⟨7, by decide⟩))
    (z2b (gm ⟨0, by decide⟩)) (z2b (gm ⟨1, by decide⟩)) (z2b (gm ⟨2, by decide⟩))
    (hmask 207) (hmask 79) (hmask 12) (hmask 71) (hmask 3) (hmask 6) (hmask 55)
  rcases hw with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  intro m hm
  interval_cases m <;>
    simp only [ix] <;>
    first
    | exact (z2b_eq_false _).mp h0
    | exact (z2b_eq_false _).mp h1
    | exact (z2b_eq_false _).mp h2
    | exact (z2b_eq_false _).mp h3
    | exact (z2b_eq_false _).mp h4
    | exact (z2b_eq_false _).mp h5
    | exact (z2b_eq_false _).mp h6
    | exact (z2b_eq_false _).mp h7

lemma z8_zero_of_F_const {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (z gm : W k)
    (hF : ∀ y : W k, F k hk z gm y ⟨0, hk⟩ + F k hk z gm 0 ⟨0, hk⟩ = 0) :
    ∀ m < 8, z (ix k hk (2 * k - 4 + m)) = 0 := by
  by_cases hk9 : 9 ≤ k
  · exact z8_zero_of_F_const_ge9 hk hk9 z gm hF
  · have hk78 : k = 7 ∨ k = 8 := by omega
    rcases hk78 with rfl | rfl
    · exact z8_zero_of_F_const_7 hk z gm hF
    · exact z8_zero_of_F_const_8 hk z gm hF

lemma single_site_const_iff {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (z gm : W k) (i : Fin k) :
    (∀ y : W k, F k hk z gm y i + F k hk z gm 0 i = 0) ↔
      (∀ m < 8, z (ix k hk (i.val + 2 * k - 4 + m)) = 0) := by
  constructor
  · intro hF
    have hF0 : ∀ y : W k,
        F k hk (sh k hk i.val z) (sh k hk i.val gm) y ⟨0, hk⟩ +
        F k hk (sh k hk i.val z) (sh k hk i.val gm) 0 ⟨0, hk⟩ = 0 := by
      intro y
      have h := hF ((shEquiv k hk i.val).symm y)
      rw [F_eq_sh_zero hk z gm _ i, F_eq_sh_zero hk z gm 0 i, sh_zero] at h
      have hsymm : sh k hk i.val ((shEquiv k hk i.val).symm y) = y :=
        (shEquiv k hk i.val).apply_symm_apply y
      rwa [hsymm] at h
    have hz0 := z8_zero_of_F_const hk hk7 (sh k hk i.val z) (sh k hk i.val gm) hF0
    intro m hm
    have h1 := hz0 m hm
    simp only [sh] at h1
    change z (ix k hk (i.val + (2 * k - 4 + m) % k)) = 0 at h1
    rw [ix_add_mod_right] at h1
    have heq : i.val + (2 * k - 4 + m) = i.val + 2 * k - 4 + m := by omega
    rwa [heq] at h1
  · intro hz y
    rw [F_eq_sh_zero hk z gm y i, F_eq_sh_zero hk z gm 0 i]
    have hz0 : ∀ m < 8, sh k hk i.val z (ix k hk (2 * k - 4 + m)) = 0 := by
      intro m hm
      simp only [sh]
      change z (ix k hk (i.val + (2 * k - 4 + m) % k)) = 0
      rw [ix_add_mod_right]
      have heq : i.val + (2 * k - 4 + m) = i.val + 2 * k - 4 + m := by omega
      rw [heq]
      exact hz m hm
    rw [F_zero_of_z8_zero hk hk7 _ _ _ hz0, F_zero_of_z8_zero hk hk7 _ _ _ hz0, zmod2_add_self]

lemma single_site_zero_iff {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (δ gm : W k) (i : Fin k) :
    (∀ y : W k, F k hk (mix k hk δ) gm y i + rot k hk 7 δ i = 0) ↔
      ((∀ m < 8, mix k hk δ (ix k hk (i.val + 2 * k - 4 + m)) = 0) ∧
        δ (ix k hk (i.val + 2 * k - 1)) = 0) := by
  constructor
  · intro hF
    have hconst : ∀ y : W k, F k hk (mix k hk δ) gm y i + F k hk (mix k hk δ) gm 0 i = 0 := by
      intro y
      have h1 := hF y
      have h2 := hF 0
      have heq : (F k hk (mix k hk δ) gm y i + rot k hk 7 δ i) +
          (F k hk (mix k hk δ) gm 0 i + rot k hk 7 δ i) =
          (F k hk (mix k hk δ) gm y i + F k hk (mix k hk δ) gm 0 i) +
          (rot k hk 7 δ i + rot k hk 7 δ i) := by ring
      rw [h1, h2, add_zero, zmod2_add_self, add_zero] at heq
      exact heq.symm
    have hz := (single_site_const_iff hk hk7 (mix k hk δ) gm i).mp hconst
    refine ⟨hz, ?_⟩
    have h0 := hF 0
    rw [F_eq_sh_zero hk (mix k hk δ) gm 0 i, sh_zero] at h0
    have hrot : rot k hk 7 δ i = rot k hk 7 (sh k hk i.val δ) ⟨0, hk⟩ := by
      have hr := congrFun (sh_rot hk i.val 7 δ) ⟨0, hk⟩
      simpa [sh, ix_val] using hr
    rw [hrot, sh_mix] at h0
    have hz0 : ∀ m < 8, mix k hk (sh k hk i.val δ) (ix k hk (2 * k - 4 + m)) = 0 := by
      intro m hm
      rw [← sh_mix]
      simp only [sh]
      change mix k hk δ (ix k hk (i.val + (2 * k - 4 + m) % k)) = 0
      rw [ix_add_mod_right]
      have heq : i.val + (2 * k - 4 + m) = i.val + 2 * k - 4 + m := by omega
      rw [heq]
      exact hz m hm
    rw [F_add_rot7_of_z8_zero hk hk7 (sh k hk i.val δ) (sh k hk i.val gm) 0 hz0] at h0
    simp only [sh] at h0
    change δ (ix k hk (i.val + (2 * k - 1) % k)) = 0 at h0
    rw [ix_add_mod_right] at h0
    have heq : i.val + (2 * k - 1) = i.val + 2 * k - 1 := by omega
    rwa [heq] at h0
  · rintro ⟨hz, hδ⟩ y
    rw [F_eq_sh_zero hk (mix k hk δ) gm y i]
    have hrot : rot k hk 7 δ i = rot k hk 7 (sh k hk i.val δ) ⟨0, hk⟩ := by
      have hr := congrFun (sh_rot hk i.val 7 δ) ⟨0, hk⟩
      simpa [sh, ix_val] using hr
    rw [hrot, sh_mix]
    have hz0 : ∀ m < 8, mix k hk (sh k hk i.val δ) (ix k hk (2 * k - 4 + m)) = 0 := by
      intro m hm
      rw [← sh_mix]
      simp only [sh]
      change mix k hk δ (ix k hk (i.val + (2 * k - 4 + m) % k)) = 0
      rw [ix_add_mod_right]
      have heq : i.val + (2 * k - 4 + m) = i.val + 2 * k - 4 + m := by omega
      rw [heq]
      exact hz m hm
    rw [F_add_rot7_of_z8_zero hk hk7 (sh k hk i.val δ) (sh k hk i.val gm) (sh k hk i.val y) hz0]
    simp only [sh]
    change δ (ix k hk (i.val + (2 * k - 1) % k)) = 0
    rw [ix_add_mod_right]
    have heq : i.val + (2 * k - 1) = i.val + 2 * k - 1 := by omega
    rw [heq]
    exact hδ

lemma run_add_run_nameOf {k : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0)
    (c1 c2 k1 k2 y : W k) (i : Fin k) :
    let e := mixEquiv hk hk7 hk3
    let name := e.symm y + rot k hk 3 k1
    let δ := k1 + k2
    let gm := mix k hk (rot k hk 4 k1 + c1)
    run k hk k1 name c1 c2 i + run k hk k2 name c1 c2 i =
      F k hk (mix k hk δ) gm y i + rot k hk 7 δ i := by
  intro e name δ gm
  have hk2 : k2 = k1 + δ := by
    simp only [δ, w_add_cancel_left]
  have hmix_symm : mix k hk (e.symm y) = y := e.apply_symm_apply y
  have h1 : rot k hk 3 k1 + name = e.symm y := by
    simp only [name]
    calc rot k hk 3 k1 + (e.symm y + rot k hk 3 k1)
        = (rot k hk 3 k1 + rot k hk 3 k1) + e.symm y := by ring
      _ = e.symm y := by rw [w_add_self, zero_add]
  have h2 : rot k hk 3 k2 + name = e.symm y + rot k hk 3 δ := by
    rw [hk2, rot_add]
    calc rot k hk 3 k1 + rot k hk 3 δ + name
        = (rot k hk 3 k1 + name) + rot k hk 3 δ := by ring
      _ = e.symm y + rot k hk 3 δ := by rw [h1]
  have hu1 : upd k hk (rot k hk 3 k1 + name) = chi k hk y := by
    funext t; simp only [upd, h1, hmix_symm]
  have hu2 : upd k hk (rot k hk 3 k2 + name) = chi k hk (y + rot k hk 3 (mix k hk δ)) := by
    funext t; simp only [upd, h2, mix_add, hmix_symm, mix_rot]
  have hm1 : mix k hk (upd k hk (rot k hk 3 k1 + name) + rot k hk 4 k1 + c1) =
      mix k hk (chi k hk y) + gm := by
    rw [hu1, show chi k hk y + rot k hk 4 k1 + c1 = chi k hk y + (rot k hk 4 k1 + c1) by ring,
      mix_add]
  have hm2 : mix k hk (upd k hk (rot k hk 3 k2 + name) + rot k hk 4 k2 + c1) =
      mix k hk (chi k hk (y + rot k hk 3 (mix k hk δ))) + gm + rot k hk 4 (mix k hk δ) := by
    rw [hu2, hk2, rot_add]
    have hrearr :
        chi k hk (y + rot k hk 3 (mix k hk δ)) + (rot k hk 4 k1 + rot k hk 4 δ) + c1 =
        chi k hk (y + rot k hk 3 (mix k hk δ)) + (rot k hk 4 k1 + c1) + rot k hk 4 δ := by ring
    rw [hrearr, mix_add, mix_add, mix_rot]
  simp only [run, Pi.add_apply]
  change chi k hk (mix k hk (upd k hk (rot k hk 3 k1 + name) + rot k hk 4 k1 + c1)) i +
      rot k hk 7 k1 i + c2 i +
      (chi k hk (mix k hk (upd k hk (rot k hk 3 k2 + name) + rot k hk 4 k2 + c1)) i +
      rot k hk 7 k2 i + c2 i) =
      F k hk (mix k hk δ) gm y i + rot k hk 7 δ i
  rw [hm1, hm2, hk2, rot_add]
  simp only [Pi.add_apply, F]
  have hkill : (rot k hk 7 k1 i + c2 i) + (rot k hk 7 k1 i + c2 i) = 0 := zmod2_add_self _
  calc chi k hk (mix k hk (chi k hk y) + gm) i + rot k hk 7 k1 i + c2 i +
        (chi k hk (mix k hk (chi k hk (y + rot k hk 3 (mix k hk δ))) + gm +
          rot k hk 4 (mix k hk δ)) i + (rot k hk 7 k1 i + rot k hk 7 δ i) + c2 i)
      = chi k hk (mix k hk (chi k hk y) + gm) i +
        chi k hk (mix k hk (chi k hk (y + rot k hk 3 (mix k hk δ))) + gm +
          rot k hk 4 (mix k hk δ)) i + rot k hk 7 δ i +
        ((rot k hk 7 k1 i + c2 i) + (rot k hk 7 k1 i + c2 i)) := by ring
    _ = chi k hk (mix k hk (chi k hk y) + gm) i +
        chi k hk (mix k hk (chi k hk (y + rot k hk 3 (mix k hk δ))) + gm +
          rot k hk 4 (mix k hk δ)) i + rot k hk 7 δ i := by rw [hkill, add_zero]

lemma exists_tag_iff_card {k h : ℕ} [DecidableEq (W k → Fin h → ZMod 2)]
    (obs : W k → W k → Fin h → ZMod 2)
    (allow : Bool) (N : ℕ) :
    (∃ (tag : W k → Fin N) (decode : Fin N → W k → Fin h → ZMod 2)
        (bias : W k → Fin h → ZMod 2),
      ∀ (key name : W k) (j : Fin h), obs key name j =
        (if allow then bias key j else 0) + decode (tag key) name j) ↔
      (Finset.image
        (fun (key : W k) (name : W k) (j : Fin h) =>
          obs key name j + if allow then obs key 0 j else 0)
        Finset.univ).card ≤ N := by
  classical
  let prof : W k → W k → Fin h → ZMod 2 :=
    fun key name j => obs key name j + if allow then obs key 0 j else 0
  change (∃ (tag : W k → Fin N) (decode : Fin N → W k → Fin h → ZMod 2)
        (bias : W k → Fin h → ZMod 2),
      ∀ (key name : W k) (j : Fin h), obs key name j =
        (if allow then bias key j else 0) + decode (tag key) name j) ↔
      (Finset.image prof Finset.univ).card ≤ N
  constructor
  · rintro ⟨tag, decode, bias, hspec⟩
    let decode' : Fin N → W k → Fin h → ZMod 2 :=
      fun t name j => decode t name j + if allow then decode t 0 j else 0
    have hprof : ∀ key : W k, prof key = decode' (tag key) := by
      intro key
      funext name j
      simp only [prof, decode']
      cases allow
      · simp [hspec key name j]
      · simp only [ite_true]
        rw [hspec key name j, hspec key 0 j]
        simp only [ite_true]
        calc bias key j + decode (tag key) name j + (bias key j + decode (tag key) 0 j)
            = (bias key j + bias key j) + (decode (tag key) name j + decode (tag key) 0 j) := by ring
          _ = decode (tag key) name j + decode (tag key) 0 j := by rw [zmod2_add_self, zero_add]
    have hsub : Finset.image prof Finset.univ ⊆ Finset.image decode' Finset.univ := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨key, _, rfl⟩
      rw [hprof key]
      exact Finset.mem_image_of_mem decode' (Finset.mem_univ (tag key))
    calc (Finset.image prof Finset.univ).card
        ≤ (Finset.image decode' Finset.univ).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
      _ = N := by simp
  · intro hcard
    let S : Finset (W k → Fin h → ZMod 2) := Finset.image prof Finset.univ
    have hScard : S.card ≤ N := hcard
    let e : ↥S ≃ Fin S.card := Fintype.equivFinOfCardEq (Fintype.card_coe S)
    let tag : W k → Fin N := fun key =>
      let idx := e ⟨prof key, Finset.mem_image_of_mem prof (Finset.mem_univ key)⟩
      ⟨idx.val, lt_of_lt_of_le idx.isLt hScard⟩
    let decode : Fin N → W k → Fin h → ZMod 2 := fun t =>
      if ht : t.val < S.card then (e.symm ⟨t.val, ht⟩).val else 0
    let bias : W k → Fin h → ZMod 2 := fun key => obs key 0
    refine ⟨tag, decode, bias, ?_⟩
    intro key name j
    have hdec : decode (tag key) = prof key := by
      simp only [tag, decode]
      have hlt : (e ⟨prof key, Finset.mem_image_of_mem prof (Finset.mem_univ key)⟩).val < S.card :=
        (e ⟨prof key, Finset.mem_image_of_mem prof (Finset.mem_univ key)⟩).isLt
      rw [dif_pos hlt]
      simp [Equiv.symm_apply_apply]
    rw [hdec]
    simp only [prof, bias]
    cases allow
    · simp
    · simp only [ite_true]
      calc obs key name j
          = obs key name j + (obs key 0 j + obs key 0 j) := by rw [zmod2_add_self, add_zero]
        _ = obs key 0 j + (obs key name j + obs key 0 j) := by ring

lemma card_image_eq_pow {k : ℕ} {α : Type*} [DecidableEq α]
    (prof : W k → α) (P : W k → Prop) [DecidablePred P]
    (hiff : ∀ k1 k2 : W k, prof k1 = prof k2 ↔ P (k1 + k2))
    (target : ℕ) (htarget : target ≤ k)
    (hcardP : Fintype.card {x : W k // P x} = 2 ^ (k - target)) :
    (Finset.image prof Finset.univ).card = 2 ^ target := by
  let S := Finset.image prof Finset.univ
  have hfib : ∀ p ∈ S,
      (Finset.univ.filter (fun x : W k => prof x = p)).card =
        (Finset.univ.filter P).card := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k0, _, rfl⟩
    refine Finset.card_bij (fun x _ => x + k0) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (hiff x k0).mp hx
    · intro x1 _ x2 _ h
      have h1 : x1 + k0 + k0 = x2 + k0 + k0 := congrArg (· + k0) h
      simpa [add_assoc, w_add_self] using h1
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨y + k0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hiff]
        have heq : y + k0 + k0 = y := by rw [add_assoc, w_add_self, add_zero]
        rwa [heq]
      · rw [add_assoc, w_add_self, add_zero]
  have hsum : (Finset.univ : Finset (W k)).card =
      ∑ p ∈ S, (Finset.univ.filter (fun x : W k => prof x = p)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x _
    exact Finset.mem_image_of_mem prof (Finset.mem_univ x)
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hsum
  have hcardW : (Finset.univ : Finset (W k)).card = 2 ^ k := by
    simpa using card_W k
  have hcardF : (Finset.univ.filter P).card = 2 ^ (k - target) := by
    rw [← Fintype.card_subtype, hcardP]
  rw [hcardW, hcardF] at hsum
  have hpow : 2 ^ k = 2 ^ target * 2 ^ (k - target) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le htarget]
  rw [hpow] at hsum
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by decide : 0 < 2)) hsum.symm

abbrev Good (k : ℕ) (hk : 0 < k) (h : ℕ) (w : W k) : Prop :=
  (∀ m < h + 7, w (ix k hk m) + w (ix k hk (m + 2)) + w (ix k hk (m + 4)) = 0) ∧
    (∀ j < h, w (ix k hk (5 + j)) = 0)

def rec6 (a b c d : ZMod 2) (n : ℕ) : ZMod 2 :=
  match n % 6 with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => a + c
  | _ => b + d

lemma rec6_step (a b c d : ZMod 2) (n : ℕ) :
    rec6 a b c d n + rec6 a b c d (n + 2) + rec6 a b c d (n + 4) = 0 := by
  have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
  have h2 : (n + 2) % 6 = (n % 6 + 2) % 6 := by omega
  have h4 : (n + 4) % 6 = (n % 6 + 4) % 6 := by omega
  simp only [rec6, h2, h4]
  interval_cases n % 6 <;>
    (rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      rcases zmod2_cases c with rfl | rfl <;> rcases zmod2_cases d with rfl | rfl <;> decide)

lemma good_eq_rec6 {k : ℕ} (hk : 0 < k) (h : ℕ) (w : W k)
    (hrec : ∀ m < h + 7, w (ix k hk m) + w (ix k hk (m + 2)) + w (ix k hk (m + 4)) = 0) :
    ∀ t < h + 11, w (ix k hk t) =
      rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) t := by
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases ht4 : t < 4
    · interval_cases t <;> simp [rec6]
    · let m := t - 4
      have hm : m < h + 7 := by omega
      have hstep := hrec m hm
      have hmt : m + 4 = t := by omega
      rw [hmt] at hstep
      have hm1 : w (ix k hk m) =
          rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) m :=
        ih m (by omega) (by omega)
      have hm2 : w (ix k hk (m + 2)) =
          rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) (m + 2) :=
        ih (m + 2) (by omega) (by omega)
      have hr := rec6_step (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) m
      rw [hmt] at hr
      rw [hm1, hm2] at hstep
      have hsum : (rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) m +
          rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) (m + 2) +
          w (ix k hk t)) +
          (rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) m +
          rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) (m + 2) +
          rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) t) = 0 := by
        rw [hstep, hr, add_zero]
      have heq0 : w (ix k hk t) +
          rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) t = 0 := by
        generalize rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) m = A at hsum
        generalize rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) (m + 2) = B at hsum
        have heq : (A + B + w (ix k hk t)) + (A + B +
            rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) t) =
            (w (ix k hk t) +
              rec6 (w (ix k hk 0)) (w (ix k hk 1)) (w (ix k hk 2)) (w (ix k hk 3)) t) +
            (A + A) + (B + B) := by ring
        rw [hsum, zmod2_add_self, zmod2_add_self, add_zero, add_zero] at heq
        exact heq.symm
      exact (zmod2_add_eq_zero _ _).mp heq0

lemma card_prefix_zero {k c : ℕ} (hc : c ≤ k) :
    Fintype.card {v : W k // ∀ i : Fin k, i.val < c → v i = 0} = 2 ^ (k - c) := by
  let e : {v : W k // ∀ i : Fin k, i.val < c → v i = 0} ≃ W (k - c) :=
    { toFun := fun v r => v.val ⟨c + r.val, by omega⟩
      invFun := fun u =>
        ⟨fun i => if hi : i.val < c then 0 else u ⟨i.val - c, by omega⟩,
         fun i hi => by simp [hi]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext i
        by_cases hi : i.val < c
        · simp [hi, v.property i hi]
        · simp only [hi, dite_false]
          have hfin : (⟨c + (i.val - c), by omega⟩ : Fin k) = i := by
            apply Fin.ext; dsimp; omega
          rw [hfin]
      right_inv := fun u => by
        funext r
        have hnot : ¬ (c + r.val < c) := by omega
        simp only [hnot, dite_false]
        have hfin : (⟨c + r.val - c, by omega⟩ : Fin (k - c)) = r := by
          apply Fin.ext; dsimp; omega
        rw [hfin] }
  rw [Fintype.card_congr e, card_W]

lemma card_allow_true {k h : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0)
    (start : Fin k) :
    Fintype.card {δ : W k // ∀ n < h + 7, mix k hk δ (ix k hk (start.val + 2 * k - 4 + n)) = 0} =
      2 ^ (k - min k (h + 7)) := by
  let e1 : {δ : W k // ∀ n < h + 7, mix k hk δ (ix k hk (start.val + 2 * k - 4 + n)) = 0} ≃
      {v : W k // ∀ i : Fin k, i.val < min k (h + 7) → v i = 0} :=
      { toFun := fun δ =>
          ⟨sh k hk (start.val + 2 * k - 4) (mix k hk δ.val), by
            intro i hi
            change mix k hk δ.val (ix k hk (start.val + 2 * k - 4 + i.val)) = 0
            exact δ.property i.val (lt_of_lt_of_le hi (min_le_right k (h + 7)))⟩
        invFun := fun v =>
          ⟨(mixEquiv hk hk7 hk3).symm ((shEquiv k hk (start.val + 2 * k - 4)).symm v.val), by
            intro n hn
            have hm : mix k hk ((mixEquiv hk hk7 hk3).symm
                ((shEquiv k hk (start.val + 2 * k - 4)).symm v.val)) =
                (shEquiv k hk (start.val + 2 * k - 4)).symm v.val :=
              (mixEquiv hk hk7 hk3).apply_symm_apply _
            rw [hm]
            have hs := congrFun ((shEquiv k hk (start.val + 2 * k - 4)).apply_symm_apply v.val) (ix k hk n)
            simp only [shEquiv, Equiv.coe_fn_mk, sh] at hs
            change ((shEquiv k hk (start.val + 2 * k - 4)).symm v.val)
              (ix k hk (start.val + 2 * k - 4 + n % k)) = v.val (ix k hk n) at hs
            rw [ix_add_mod_right] at hs
            rw [hs]
            apply v.property
            by_cases hle : h + 7 ≤ k
            · have hmin : min k (h + 7) = h + 7 := min_eq_right hle
              rw [hmin]
              simp only [ix]
              rw [Nat.mod_eq_of_lt (by omega)]
              exact hn
            · have hmin : min k (h + 7) = k := min_eq_left (by omega)
              rw [hmin]
              exact (ix k hk n).isLt⟩
        left_inv := fun δ => by
          apply Subtype.ext
          dsimp only
          change (mixEquiv hk hk7 hk3).symm ((shEquiv k hk (start.val + 2 * k - 4)).symm
            ((shEquiv k hk (start.val + 2 * k - 4)) (mix k hk δ.val))) = δ.val
          rw [(shEquiv k hk (start.val + 2 * k - 4)).symm_apply_apply]
          exact (mixEquiv hk hk7 hk3).symm_apply_apply δ.val
        right_inv := fun v => by
          apply Subtype.ext
          dsimp only
          have h1 : mix k hk ((mixEquiv hk hk7 hk3).symm
              ((shEquiv k hk (start.val + 2 * k - 4)).symm v.val)) =
              (shEquiv k hk (start.val + 2 * k - 4)).symm v.val :=
            (mixEquiv hk hk7 hk3).apply_symm_apply _
          rw [h1]
          exact (shEquiv k hk (start.val + 2 * k - 4)).apply_symm_apply v.val }
  rw [Fintype.card_congr e1, card_prefix_zero (min_le_left k (h + 7))]

def rec6B (a b c d : Bool) (n : ℕ) : Bool :=
  match n % 6 with
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => xor a c
  | _ => xor b d

lemma z2b_rec6 (a b c d : ZMod 2) (n : ℕ) :
    z2b (rec6 a b c d n) = rec6B (z2b a) (z2b b) (z2b c) (z2b d) n := by
  have hlt : n % 6 < 6 := Nat.mod_lt n (by decide)
  simp only [rec6, rec6B]
  interval_cases n % 6 <;> simp [z2b_add]

def pack4 (p : Fin 4 → ZMod 2) : Fin 16 :=
  ⟨(if z2b (p 0) then 1 else 0) + (if z2b (p 1) then 2 else 0) +
    (if z2b (p 2) then 4 else 0) + (if z2b (p 3) then 8 else 0), by
    cases z2b (p 0) <;> cases z2b (p 1) <;> cases z2b (p 2) <;> cases z2b (p 3) <;> decide⟩

def unpack4 (m : Fin 16) : Fin 4 → ZMod 2 :=
  fun i => b2z (m.val.testBit i.val)

lemma pack4_testBit (p : Fin 4 → ZMod 2) (r : Fin 4) :
    (pack4 p).val.testBit r.val = z2b (p r) := by
  rcases r with ⟨rv, hrv⟩
  interval_cases rv
  · change ((if z2b (p 0) then 1 else 0) + (if z2b (p 1) then 2 else 0) +
      (if z2b (p 2) then 4 else 0) + (if z2b (p 3) then 8 else 0)).testBit 0 = z2b (p 0)
    cases z2b (p 0) <;> cases z2b (p 1) <;> cases z2b (p 2) <;> cases z2b (p 3) <;> decide
  · change ((if z2b (p 0) then 1 else 0) + (if z2b (p 1) then 2 else 0) +
      (if z2b (p 2) then 4 else 0) + (if z2b (p 3) then 8 else 0)).testBit 1 = z2b (p 1)
    cases z2b (p 0) <;> cases z2b (p 1) <;> cases z2b (p 2) <;> cases z2b (p 3) <;> decide
  · change ((if z2b (p 0) then 1 else 0) + (if z2b (p 1) then 2 else 0) +
      (if z2b (p 2) then 4 else 0) + (if z2b (p 3) then 8 else 0)).testBit 2 = z2b (p 2)
    cases z2b (p 0) <;> cases z2b (p 1) <;> cases z2b (p 2) <;> cases z2b (p 3) <;> decide
  · change ((if z2b (p 0) then 1 else 0) + (if z2b (p 1) then 2 else 0) +
      (if z2b (p 2) then 4 else 0) + (if z2b (p 3) then 8 else 0)).testBit 3 = z2b (p 3)
    cases z2b (p 0) <;> cases z2b (p 1) <;> cases z2b (p 2) <;> cases z2b (p 3) <;> decide

lemma unpack4_pack4 (p : Fin 4 → ZMod 2) : unpack4 (pack4 p) = p := by
  funext r
  simp only [unpack4, pack4_testBit, b2z_z2b]

lemma pack4_unpack4 (m : Fin 16) : pack4 (unpack4 m) = m := by
  have h : ∀ n : Fin 16,
      (if n.val.testBit 0 then 1 else 0) + (if n.val.testBit 1 then 2 else 0) +
      (if n.val.testBit 2 then 4 else 0) + (if n.val.testBit 3 then 8 else 0) = n.val := by
    decide
  apply Fin.ext
  dsimp [pack4, unpack4]
  simp only [z2b_b2z]
  exact h m

def prefixRec6B (mh : ℕ) (m : Fin 16) : Bool :=
  (List.range mh).all fun j =>
    !(rec6B (m.val.testBit 0) (m.val.testBit 1) (m.val.testBit 2) (m.val.testBit 3) (5 + j))

def count16 (P : Fin 16 → Bool) : ℕ :=
  (if P 0 = true then 1 else 0) + ((if P 1 = true then 1 else 0) + ((if P 2 = true then 1 else 0) +
  ((if P 3 = true then 1 else 0) + ((if P 4 = true then 1 else 0) + ((if P 5 = true then 1 else 0) +
  ((if P 6 = true then 1 else 0) + ((if P 7 = true then 1 else 0) + ((if P 8 = true then 1 else 0) +
  ((if P 9 = true then 1 else 0) + ((if P 10 = true then 1 else 0) + ((if P 11 = true then 1 else 0) +
  ((if P 12 = true then 1 else 0) + ((if P 13 = true then 1 else 0) + ((if P 14 = true then 1 else 0) +
  ((if P 15 = true then 1 else 0) + 0)))))))))))))))

lemma card_fin16_eq_count16 (P : Fin 16 → Bool) :
    Fintype.card {m : Fin 16 // P m = true} = count16 P := by
  rw [Fintype.card_subtype, Finset.card_filter]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  rfl

lemma card_rec6_prefix (mh : ℕ) (h1 : 1 ≤ mh) (h4 : mh ≤ 4) :
    Fintype.card {p : Fin 4 → ZMod 2 // ∀ j < mh, rec6 (p 0) (p 1) (p 2) (p 3) (5 + j) = 0} =
      2 ^ (4 - mh) := by
  let P4 (p : Fin 4 → ZMod 2) : Prop := ∀ j < mh, rec6 (p 0) (p 1) (p 2) (p 3) (5 + j) = 0
  let e : {p : Fin 4 → ZMod 2 // P4 p} ≃ {m : Fin 16 // prefixRec6B mh m = true} :=
    { toFun := fun p =>
        ⟨pack4 p.val, by
          simp only [prefixRec6B, List.all_eq_true, List.mem_range, Bool.not_eq_true']
          intro j hj
          have hb0 : (pack4 p.val).val.testBit 0 = z2b (p.val 0) := pack4_testBit p.val 0
          have hb1 : (pack4 p.val).val.testBit 1 = z2b (p.val 1) := pack4_testBit p.val 1
          have hb2 : (pack4 p.val).val.testBit 2 = z2b (p.val 2) := pack4_testBit p.val 2
          have hb3 : (pack4 p.val).val.testBit 3 = z2b (p.val 3) := pack4_testBit p.val 3
          rw [hb0, hb1, hb2, hb3, ← z2b_rec6, p.property j hj, z2b_zero]⟩
      invFun := fun m =>
        ⟨unpack4 m.val, by
          intro j hj
          have hm := m.property
          simp only [prefixRec6B, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hm
          have h0 := hm j hj
          apply (z2b_eq_false _).mp
          rw [z2b_rec6]
          simpa [unpack4, z2b_b2z] using h0⟩
      left_inv := fun p => Subtype.ext (unpack4_pack4 p.val)
      right_inv := fun m => Subtype.ext (pack4_unpack4 m.val) }
  rw [Fintype.card_congr e, card_fin16_eq_count16]
  clear e P4
  interval_cases mh <;> decide +kernel

def goodRec6B (k h : ℕ) (a b c d : Bool) : Bool :=
  ((List.range (h + 7)).all fun m =>
    !(xor (xor (rec6B a b c d (m % k)) (rec6B a b c d ((m + 2) % k)))
      (rec6B a b c d ((m + 4) % k)))) &&
  ((List.range h).all fun j => !(rec6B a b c d ((5 + j) % k)))

instance instDecidableGood (k : ℕ) (hk : 0 < k) (h : ℕ) (w : W k) :
    Decidable (Good k hk h w) := by
  unfold Good
  infer_instance

lemma card_good_rec6_eq (k : ℕ) (hk : 0 < k) (h : ℕ)
    [Fintype {p : Fin 4 → ZMod 2 // Good k hk h (fun i => rec6 (p 0) (p 1) (p 2) (p 3) i.val)}] :
    Fintype.card {p : Fin 4 → ZMod 2 // Good k hk h (fun i => rec6 (p 0) (p 1) (p 2) (p 3) i.val)} =
      Fintype.card {m : Fin 16 //
        goodRec6B k h (m.val.testBit 0) (m.val.testBit 1) (m.val.testBit 2) (m.val.testBit 3) = true} := by
  let e : {p : Fin 4 → ZMod 2 // Good k hk h (fun i => rec6 (p 0) (p 1) (p 2) (p 3) i.val)} ≃
      {m : Fin 16 //
        goodRec6B k h (m.val.testBit 0) (m.val.testBit 1) (m.val.testBit 2) (m.val.testBit 3) = true} :=
    { toFun := fun p =>
        ⟨pack4 p.val, by
          have hb0 : (pack4 p.val).val.testBit 0 = z2b (p.val 0) := pack4_testBit p.val 0
          have hb1 : (pack4 p.val).val.testBit 1 = z2b (p.val 1) := pack4_testBit p.val 1
          have hb2 : (pack4 p.val).val.testBit 2 = z2b (p.val 2) := pack4_testBit p.val 2
          have hb3 : (pack4 p.val).val.testBit 3 = z2b (p.val 3) := pack4_testBit p.val 3
          simp only [goodRec6B, Bool.and_eq_true, List.all_eq_true, List.mem_range,
            Bool.not_eq_true', hb0, hb1, hb2, hb3]
          refine ⟨?_, ?_⟩
          · intro m hm
            have h1 := p.property.1 m hm
            have h2 := congrArg z2b h1
            simp only [ix, z2b_add, z2b_rec6, z2b_zero] at h2
            exact h2
          · intro j hj
            have h1 := p.property.2 j hj
            have h2 := congrArg z2b h1
            simp only [ix, z2b_rec6, z2b_zero] at h2
            exact h2⟩
      invFun := fun m =>
        ⟨unpack4 m.val, by
          have hm := m.property
          simp only [goodRec6B, Bool.and_eq_true, List.all_eq_true, List.mem_range,
            Bool.not_eq_true'] at hm
          refine ⟨?_, ?_⟩
          · intro r hr
            apply (z2b_eq_false _).mp
            simp only [ix, unpack4, z2b_add, z2b_rec6, z2b_b2z]
            exact hm.1 r hr
          · intro j hj
            apply (z2b_eq_false _).mp
            simp only [ix, unpack4, z2b_rec6, z2b_b2z]
            exact hm.2 j hj⟩
      left_inv := fun p => Subtype.ext (unpack4_pack4 p.val)
      right_inv := fun m => Subtype.ext (pack4_unpack4 m.val) }
  exact Fintype.card_congr e

lemma card_good_eq {k h : ℕ} (hk : 0 < k) (hk7 : 7 ≤ k) (hk3 : k % 3 ≠ 0)
    (hh0 : 0 < h) (hhk : h ≤ k) [Fintype {w : W k // Good k hk h w}] :
    let exception := (k = 11 ∧ h = 2) ∨ (k = 13 ∧ h = 3)
    let ordinary := min k (h + 7 + min h 4) - (if exception then 1 else 0)
    Fintype.card {w : W k // Good k hk h w} = 2 ^ (k - ordinary) := by
  intro exception ordinary
  by_cases hbig : h + 11 ≤ k
  · have hnotexc : ¬ exception := by
      simp only [exception]
      omega
    have hord : ordinary = h + 7 + min h 4 := by
      simp only [ordinary, hnotexc, ite_false, Nat.sub_zero]
      omega
    let e : {w : W k // Good k hk h w} ≃
        {p : Fin 4 → ZMod 2 // ∀ j < min h 4, rec6 (p 0) (p 1) (p 2) (p 3) (5 + j) = 0} ×
          W (k - (h + 11)) :=
      { toFun := fun w =>
          (⟨fun i => w.val ⟨i.val, by omega⟩, by
            intro j hj
            dsimp only
            have hjh : j < h := lt_of_lt_of_le hj (min_le_left h 4)
            have hrec := good_eq_rec6 hk h w.val w.property.1 (5 + j) (by omega)
            have h0 : w.val (ix k hk 0) = w.val ⟨0, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.zero_mod k))
            have h1 : w.val (ix k hk 1) = w.val ⟨1, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 1 < k)))
            have h2 : w.val (ix k hk 2) = w.val ⟨2, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 2 < k)))
            have h3 : w.val (ix k hk 3) = w.val ⟨3, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 3 < k)))
            rw [h0, h1, h2, h3] at hrec
            change rec6 (w.val ⟨0, by omega⟩) (w.val ⟨1, by omega⟩)
              (w.val ⟨2, by omega⟩) (w.val ⟨3, by omega⟩) (5 + j) = 0
            rw [← hrec]
            exact w.property.2 j hjh⟩,
           fun r => w.val ⟨h + 11 + r.val, by omega⟩)
        invFun := fun pt =>
          let p := pt.1.val
          let tail := pt.2
          ⟨fun i => if hi : i.val < h + 11 then rec6 (p 0) (p 1) (p 2) (p 3) i.val
            else tail ⟨i.val - (h + 11), by omega⟩, by
            refine ⟨?_, ?_⟩
            · intro m hm
              have hm0 : (ix k hk m).val = m := by
                simp only [ix]; exact Nat.mod_eq_of_lt (by omega)
              have hm2 : (ix k hk (m + 2)).val = m + 2 := by
                simp only [ix]; exact Nat.mod_eq_of_lt (by omega)
              have hm4 : (ix k hk (m + 4)).val = m + 4 := by
                simp only [ix]; exact Nat.mod_eq_of_lt (by omega)
              simp only [hm0, hm2, hm4, show m < h + 11 by omega, show m + 2 < h + 11 by omega,
                show m + 4 < h + 11 by omega, dite_true]
              exact rec6_step (p 0) (p 1) (p 2) (p 3) m
            · intro j hj
              have hjv : (ix k hk (5 + j)).val = 5 + j := by
                simp only [ix]; exact Nat.mod_eq_of_lt (by omega)
              simp only [hjv, show 5 + j < h + 11 by omega, dite_true]
              by_cases hj4 : j < 4
              · exact pt.1.property j (by omega)
              · have hp0 := pt.1.property 0 (by omega)
                have hp1 := pt.1.property 1 (by omega)
                have hp2 := pt.1.property 2 (by omega)
                have hp3 := pt.1.property 3 (by omega)
                simp only [rec6, Nat.reduceAdd, Nat.reduceMod] at hp0 hp1 hp2 hp3
                have hpa : p 0 = 0 := hp1
                have hpb : p 1 = 0 := hp2
                have hpc : p 2 = 0 := hp3
                have hpd : p 3 = 0 := by simpa [p, hpb] using hp0
                rw [hpa, hpb, hpc, hpd]
                have hmod : (5 + j) % 6 < 6 := Nat.mod_lt _ (by decide)
                simp only [rec6]
                interval_cases (5 + j) % 6 <;> simp⟩
        left_inv := fun w => by
          apply Subtype.ext
          funext i
          dsimp only
          by_cases hi : i.val < h + 11
          · simp only [hi, dite_true]
            have hrec := good_eq_rec6 hk h w.val w.property.1 i.val hi
            have h0 : w.val (ix k hk 0) = w.val ⟨0, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.zero_mod k))
            have h1 : w.val (ix k hk 1) = w.val ⟨1, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 1 < k)))
            have h2 : w.val (ix k hk 2) = w.val ⟨2, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 2 < k)))
            have h3 : w.val (ix k hk 3) = w.val ⟨3, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 3 < k)))
            rw [h0, h1, h2, h3, ix_val] at hrec
            change rec6 (w.val ⟨0, by omega⟩) (w.val ⟨1, by omega⟩)
              (w.val ⟨2, by omega⟩) (w.val ⟨3, by omega⟩) i.val = w.val i
            exact hrec.symm
          · simp only [hi, dite_false]
            apply congrArg w.val; apply Fin.ext; dsimp; omega
        right_inv := fun pt => by
          apply Prod.ext
          · apply Subtype.ext
            funext i
            dsimp only
            have hi : i.val < h + 11 := by omega
            simp only [hi, dite_true]
            rcases i with ⟨iv, hiv⟩
            interval_cases iv <;> rfl
          · funext r
            dsimp only
            have hnot : ¬ (h + 11 + r.val < h + 11) := by omega
            simp only [hnot, dite_false]
            apply congrArg pt.2; apply Fin.ext; dsimp; omega }
    rw [Fintype.card_congr e, Fintype.card_prod,
      card_rec6_prefix (min h 4) (by omega) (min_le_right h 4), card_W, ← Nat.pow_add]
    congr 1
    omega
  · by_cases hh4 : 4 ≤ h
    · have hnotexc : ¬ exception := by
        simp only [exception]
        omega
      have hord : ordinary = k := by
        simp only [ordinary, hnotexc, ite_false, Nat.sub_zero]
        omega
      rw [hord, Nat.sub_self, pow_zero]
      have hgood0 : Good k hk h 0 := by
        constructor <;> intro _ _ <;> simp
      have huniq : ∀ w : {w : W k // Good k hk h w}, w = ⟨0, hgood0⟩ := by
        intro ⟨w, hw⟩
        apply Subtype.ext
        have h5 : w (ix k hk 5) = 0 := hw.2 0 (by omega)
        have h6 : w (ix k hk 6) = 0 := hw.2 1 (by omega)
        have h7 : w (ix k hk 7) = 0 := hw.2 2 (by omega)
        have h8 : w (ix k hk 8) = 0 := hw.2 3 (by omega)
        have hm4 := hw.1 4 (by omega)
        have hm3 := hw.1 3 (by omega)
        have hm2 := hw.1 2 (by omega)
        have hm1 := hw.1 1 (by omega)
        have hm0 := hw.1 0 (by omega)
        have h4 : w (ix k hk 4) = 0 := by simpa [h6, h8] using hm4
        have h3 : w (ix k hk 3) = 0 := by simpa [h5, h7] using hm3
        have h2 : w (ix k hk 2) = 0 := by simpa [h4, h6] using hm2
        have h1 : w (ix k hk 1) = 0 := by simpa [h3, h5] using hm1
        have h0 : w (ix k hk 0) = 0 := by simpa [h2, h4] using hm0
        funext i
        dsimp only
        have hrec := good_eq_rec6 hk h w hw.1 i.val (by omega)
        rw [ix_val, h0, h1, h2, h3] at hrec
        rw [hrec]
        have hmod : i.val % 6 < 6 := Nat.mod_lt _ (by decide)
        simp only [rec6]
        interval_cases i.val % 6 <;> simp
      haveI : Unique {w : W k // Good k hk h w} :=
        { default := ⟨0, hgood0⟩
          uniq := huniq }
      exact Fintype.card_unique
    · let e : {w : W k // Good k hk h w} ≃
          {p : Fin 4 → ZMod 2 // Good k hk h (fun i => rec6 (p 0) (p 1) (p 2) (p 3) i.val)} :=
        { toFun := fun w =>
            ⟨fun r => w.val ⟨r.val, by omega⟩, by
              have hfun : (fun i : Fin k => rec6 (w.val ⟨0, by omega⟩) (w.val ⟨1, by omega⟩)
                  (w.val ⟨2, by omega⟩) (w.val ⟨3, by omega⟩) i.val) = w.val := by
                funext i
                have hrec := good_eq_rec6 hk h w.val w.property.1 i.val (by omega)
                have h0 : w.val (ix k hk 0) = w.val ⟨0, by omega⟩ :=
                  congrArg w.val (Fin.ext (Nat.zero_mod k))
                have h1 : w.val (ix k hk 1) = w.val ⟨1, by omega⟩ :=
                  congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 1 < k)))
                have h2 : w.val (ix k hk 2) = w.val ⟨2, by omega⟩ :=
                  congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 2 < k)))
                have h3 : w.val (ix k hk 3) = w.val ⟨3, by omega⟩ :=
                  congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 3 < k)))
                rw [h0, h1, h2, h3, ix_val] at hrec
                exact hrec.symm
              change Good k hk h (fun i : Fin k => rec6 (w.val ⟨0, by omega⟩) (w.val ⟨1, by omega⟩)
                (w.val ⟨2, by omega⟩) (w.val ⟨3, by omega⟩) i.val)
              rw [hfun]
              exact w.property⟩
          invFun := fun p => ⟨fun i => rec6 (p.val 0) (p.val 1) (p.val 2) (p.val 3) i.val, p.property⟩
          left_inv := fun w => by
            apply Subtype.ext
            funext i
            dsimp only
            have hrec := good_eq_rec6 hk h w.val w.property.1 i.val (by omega)
            have h0 : w.val (ix k hk 0) = w.val ⟨0, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.zero_mod k))
            have h1 : w.val (ix k hk 1) = w.val ⟨1, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 1 < k)))
            have h2 : w.val (ix k hk 2) = w.val ⟨2, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 2 < k)))
            have h3 : w.val (ix k hk 3) = w.val ⟨3, by omega⟩ :=
              congrArg w.val (Fin.ext (Nat.mod_eq_of_lt (by omega : 3 < k)))
            rw [h0, h1, h2, h3, ix_val] at hrec
            change rec6 (w.val ⟨0, by omega⟩) (w.val ⟨1, by omega⟩)
              (w.val ⟨2, by omega⟩) (w.val ⟨3, by omega⟩) i.val = w.val i
            exact hrec.symm
          right_inv := fun p => by
            apply Subtype.ext
            funext r
            dsimp only
            rcases r with ⟨rv, hrv⟩
            interval_cases rv <;> rfl }
      rw [Fintype.card_congr e, card_good_rec6_eq k hk h, card_fin16_eq_count16]
      dsimp only [ordinary, exception]
      clear e ordinary exception
      have hk_lt : k < 14 := by omega
      have hh_lt : h < 4 := by omega
      interval_cases k <;> interval_cases h <;> first | omega | decide +kernel

lemma main_theorem :
    ∀ (k : ℕ) (hk : 0 < k), 7 ≤ k → k % 3 ≠ 0 →
      ∀ (c1 c2 : W k) (start : Fin k) (h : ℕ), 0 < h → h ≤ k →
        let corrected := min k (h + 7)
        let exception := (k = 11 ∧ h = 2) ∨ (k = 13 ∧ h = 3)
        let ordinary := min k (h + 7 + min h 4) - (if exception then 1 else 0)
        ∀ (allow : Bool) (N : ℕ),
          Iff (∃ (tag : W k → Fin N) (decode : Fin N → W k → Fin h → ZMod 2)
              (bias : W k → Fin h → ZMod 2),
            ∀ (key name : W k) (j : Fin h), run k hk key name c1 c2 (ix k hk (start.val + j.val)) =
              (if allow then bias key j else 0) + decode (tag key) name j)
            (2 ^ (if allow then corrected else ordinary) ≤ N) := by
  classical
  intro k hk hk7 hk3 c1 c2 start h hh0 hhk corrected exception ordinary allow N
  let obs : W k → W k → Fin h → ZMod 2 :=
    fun key name j => run k hk key name c1 c2 (ix k hk (start.val + j.val))
  let prof : W k → W k → Fin h → ZMod 2 :=
    fun key name j => obs key name j + if allow then obs key 0 j else 0
  rw [exists_tag_iff_card obs allow N]
  have hnameOf_bij : ∀ k1 : W k,
      Function.Bijective (fun y : W k => (mixEquiv hk hk7 hk3).symm y + rot k hk 3 k1) := by
    intro k1
    have h1 : Function.Bijective (fun x : W k => x + rot k hk 3 k1) :=
      Function.bijective_iff_has_inverse.mpr ⟨fun x => x + rot k hk 3 k1,
        fun x => by dsimp only; rw [add_assoc, w_add_self, add_zero],
        fun x => by dsimp only; rw [add_assoc, w_add_self, add_zero]⟩
    exact h1.comp (mixEquiv hk hk7 hk3).symm.bijective
  cases allow
  · let P : W k → Prop := fun δ =>
      (∀ n < h + 7, mix k hk δ (ix k hk (start.val + 2 * k - 4 + n)) = 0) ∧
        (∀ j < h, δ (ix k hk (start.val + j + 2 * k - 1)) = 0)
    have hiff : ∀ k1 k2 : W k, prof k1 = prof k2 ↔ P (k1 + k2) := by
      intro k1 k2
      let gm := mix k hk (rot k hk 4 k1 + c1)
      let nameOf : W k → W k := fun y => (mixEquiv hk hk7 hk3).symm y + rot k hk 3 k1
      have hbij := hnameOf_bij k1
      have hstep1 : prof k1 = prof k2 ↔
          ∀ j : Fin h, ∀ y : W k,
            F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
              rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val)) = 0 := by
        constructor
        · intro hprof j y
          have hp := congrFun (congrFun hprof (nameOf y)) j
          simp only [prof, obs, Bool.false_eq_true, ite_false, add_zero] at hp
          rw [← run_add_run_nameOf hk hk7 hk3 c1 c2 k1 k2 y (ix k hk (start.val + j.val))]
          exact (zmod2_add_eq_zero _ _).mpr hp
        · intro hF
          funext name j
          rcases hbij.2 name with ⟨y, rfl⟩
          simp only [prof, obs, Bool.false_eq_true, ite_false, add_zero]
          have h1 := hF j y
          rw [← run_add_run_nameOf hk hk7 hk3 c1 c2 k1 k2 y (ix k hk (start.val + j.val))] at h1
          exact (zmod2_add_eq_zero _ _).mp h1
      rw [hstep1]
      have hstep2 : (∀ j : Fin h, ∀ y : W k,
          F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
            rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val)) = 0) ↔
          (∀ j : Fin h,
            (∀ m < 8, mix k hk (k1 + k2) (ix k hk ((ix k hk (start.val + j.val)).val + 2 * k - 4 + m)) = 0) ∧
            (k1 + k2) (ix k hk ((ix k hk (start.val + j.val)).val + 2 * k - 1)) = 0) := by
        constructor <;> intro H j
        · exact (single_site_zero_iff hk hk7 (k1 + k2) gm (ix k hk (start.val + j.val))).mp (H j)
        · exact (single_site_zero_iff hk hk7 (k1 + k2) gm (ix k hk (start.val + j.val))).mpr (H j)
      rw [hstep2]
      constructor
      · intro H
        refine ⟨?_, ?_⟩
        · intro n hn
          by_cases hnh : n < h
          · have h1 := (H ⟨n, hnh⟩).1 0 (by decide)
            have hix : ix k hk ((ix k hk (start.val + n)).val + 2 * k - 4 + 0) =
                ix k hk (start.val + 2 * k - 4 + n) := by
              change ix k hk ((start.val + n) % k + 2 * k - 4 + 0) = _
              have heq1 : (start.val + n) % k + 2 * k - 4 + 0 = (start.val + n) % k + (2 * k - 4) := by omega
              have heq2 : start.val + n + (2 * k - 4) = start.val + 2 * k - 4 + n := by omega
              rw [heq1, ix_add_mod_left, heq2]
            rwa [hix] at h1
          · have h1 := (H ⟨h - 1, by omega⟩).1 (n - (h - 1)) (by omega)
            have hix : ix k hk ((ix k hk (start.val + (h - 1))).val + 2 * k - 4 + (n - (h - 1))) =
                ix k hk (start.val + 2 * k - 4 + n) := by
              change ix k hk ((start.val + (h - 1)) % k + 2 * k - 4 + (n - (h - 1))) = _
              have heq1 : (start.val + (h - 1)) % k + 2 * k - 4 + (n - (h - 1)) =
                  (start.val + (h - 1)) % k + (2 * k - 4 + (n - (h - 1))) := by omega
              have heq2 : start.val + (h - 1) + (2 * k - 4 + (n - (h - 1))) =
                  start.val + 2 * k - 4 + n := by omega
              rw [heq1, ix_add_mod_left, heq2]
            rwa [hix] at h1
        · intro j hj
          have h1 := (H ⟨j, hj⟩).2
          have hix : ix k hk ((ix k hk (start.val + j)).val + 2 * k - 1) =
              ix k hk (start.val + j + 2 * k - 1) := by
            change ix k hk ((start.val + j) % k + 2 * k - 1) = _
            have heq1 : (start.val + j) % k + 2 * k - 1 = (start.val + j) % k + (2 * k - 1) := by omega
            have heq2 : start.val + j + (2 * k - 1) = start.val + j + 2 * k - 1 := by omega
            rw [heq1, ix_add_mod_left, heq2]
          rwa [hix] at h1
      · rintro ⟨h1, h2⟩ j
        refine ⟨?_, ?_⟩
        · intro m hm
          have hix : ix k hk ((ix k hk (start.val + j.val)).val + 2 * k - 4 + m) =
              ix k hk (start.val + 2 * k - 4 + (j.val + m)) := by
            change ix k hk ((start.val + j.val) % k + 2 * k - 4 + m) = _
            have heq1 : (start.val + j.val) % k + 2 * k - 4 + m =
                (start.val + j.val) % k + (2 * k - 4 + m) := by omega
            have heq2 : start.val + j.val + (2 * k - 4 + m) =
                start.val + 2 * k - 4 + (j.val + m) := by omega
            rw [heq1, ix_add_mod_left, heq2]
          rw [hix]
          exact h1 (j.val + m) (by omega)
        · have hix : ix k hk ((ix k hk (start.val + j.val)).val + 2 * k - 1) =
              ix k hk (start.val + j.val + 2 * k - 1) := by
            change ix k hk ((start.val + j.val) % k + 2 * k - 1) = _
            have heq1 : (start.val + j.val) % k + 2 * k - 1 =
                (start.val + j.val) % k + (2 * k - 1) := by omega
            have heq2 : start.val + j.val + (2 * k - 1) = start.val + j.val + 2 * k - 1 := by omega
            rw [heq1, ix_add_mod_left, heq2]
          rw [hix]
          exact h2 j.val j.isLt
    have hcardP : Fintype.card {δ : W k // P δ} = 2 ^ (k - ordinary) := by
      let s0 := start.val + 2 * k - 6
      let e : {δ : W k // P δ} ≃ {w : W k // Good k hk h w} :=
        { toFun := fun δ =>
            ⟨sh k hk s0 δ.val, by
              refine ⟨?_, ?_⟩
              · intro m hm
                have h1 := δ.property.1 m hm
                simp only [mix] at h1
                rw [rot_ix_sub2k hk (by omega)] at h1
                have hi1 : (ix k hk (start.val + 2 * k - 4 + m)).val + 2 =
                    (start.val + 2 * k - 4 + m) % k + 2 := rfl
                rw [hi1, ix_add_mod_left] at h1
                simp only [sh]
                have ha : ix k hk (s0 + (ix k hk m).val) =
                    ix k hk (start.val + 2 * k - 4 + m + 2 * k - 2) := by
                  change ix k hk (s0 + m % k) = _
                  rw [ix_add_mod_right]
                  have heq : start.val + 2 * k - 4 + m + 2 * k - 2 = (s0 + m) + 2 * k := by
                    dsimp [s0]; omega
                  rw [heq, ix_add_mul_k]
                have hb : ix k hk (s0 + (ix k hk (m + 2)).val) =
                    ix k hk (start.val + 2 * k - 4 + m) := by
                  change ix k hk (s0 + (m + 2) % k) = _
                  rw [ix_add_mod_right]
                  have heq : s0 + (m + 2) = start.val + 2 * k - 4 + m := by dsimp [s0]; omega
                  rw [heq]
                have hc : ix k hk (s0 + (ix k hk (m + 4)).val) =
                    ix k hk (start.val + 2 * k - 4 + m + 2) := by
                  change ix k hk (s0 + (m + 4) % k) = _
                  rw [ix_add_mod_right]
                  have heq : s0 + (m + 4) = start.val + 2 * k - 4 + m + 2 := by dsimp [s0]; omega
                  rw [heq]
                rw [ha, hb, hc]
                calc δ.val (ix k hk (start.val + 2 * k - 4 + m + 2 * k - 2)) +
                      δ.val (ix k hk (start.val + 2 * k - 4 + m)) +
                      δ.val (ix k hk (start.val + 2 * k - 4 + m + 2))
                    = δ.val (ix k hk (start.val + 2 * k - 4 + m)) +
                      δ.val (ix k hk (start.val + 2 * k - 4 + m + 2)) +
                      δ.val (ix k hk (start.val + 2 * k - 4 + m + 2 * k - 2)) := by ring
                  _ = 0 := h1
              · intro j hj
                simp only [sh]
                change δ.val (ix k hk (s0 + (5 + j) % k)) = 0
                rw [ix_add_mod_right]
                have heq : s0 + (5 + j) = start.val + j + 2 * k - 1 := by dsimp [s0]; omega
                rw [heq]
                exact δ.property.2 j hj⟩
          invFun := fun w =>
            ⟨(shEquiv k hk s0).symm w.val, by
              have hsw : sh k hk s0 ((shEquiv k hk s0).symm w.val) = w.val :=
                (shEquiv k hk s0).apply_symm_apply w.val
              have hval : ∀ n, (shEquiv k hk s0).symm w.val (ix k hk (s0 + n)) = w.val (ix k hk n) := by
                intro n
                have h1 := congrFun hsw (ix k hk n)
                simp only [sh] at h1
                change (shEquiv k hk s0).symm w.val (ix k hk (s0 + n % k)) = w.val (ix k hk n) at h1
                rwa [ix_add_mod_right] at h1
              refine ⟨?_, ?_⟩
              · intro m hm
                simp only [mix]
                rw [rot_ix_sub2k hk (by omega)]
                have hi1 : (ix k hk (start.val + 2 * k - 4 + m)).val + 2 =
                    (start.val + 2 * k - 4 + m) % k + 2 := rfl
                rw [hi1, ix_add_mod_left]
                have ha : ix k hk (start.val + 2 * k - 4 + m) = ix k hk (s0 + (m + 2)) := by
                  congr 1; dsimp [s0]; omega
                have hb : ix k hk (start.val + 2 * k - 4 + m + 2) = ix k hk (s0 + (m + 4)) := by
                  congr 1; dsimp [s0]; omega
                have hc : ix k hk (start.val + 2 * k - 4 + m + 2 * k - 2) = ix k hk (s0 + m) := by
                  have heq : start.val + 2 * k - 4 + m + 2 * k - 2 = (s0 + m) + 2 * k := by
                    dsimp [s0]; omega
                  rw [heq, ix_add_mul_k]
                rw [ha, hb, hc, hval (m + 2), hval (m + 4), hval m]
                calc w.val (ix k hk (m + 2)) + w.val (ix k hk (m + 4)) + w.val (ix k hk m)
                    = w.val (ix k hk m) + w.val (ix k hk (m + 2)) + w.val (ix k hk (m + 4)) := by ring
                  _ = 0 := w.property.1 m hm
              · intro j hj
                have heq : start.val + j + 2 * k - 1 = s0 + (5 + j) := by dsimp [s0]; omega
                rw [heq, hval (5 + j)]
                exact w.property.2 j hj⟩
          left_inv := fun δ => by
            apply Subtype.ext
            dsimp only
            exact (shEquiv k hk s0).symm_apply_apply δ.val
          right_inv := fun w => by
            apply Subtype.ext
            dsimp only
            exact (shEquiv k hk s0).apply_symm_apply w.val }
      rw [Fintype.card_congr e]
      convert card_good_eq hk hk7 hk3 hh0 hhk
    have hord_le : ordinary ≤ k := by
      dsimp [ordinary]
      omega
    conv_rhs => simp only [Bool.false_eq_true, ite_false]
    rw [card_image_eq_pow prof P hiff ordinary hord_le hcardP]
  · let P : W k → Prop := fun δ =>
      ∀ n < h + 7, mix k hk δ (ix k hk (start.val + 2 * k - 4 + n)) = 0
    have hiff : ∀ k1 k2 : W k, prof k1 = prof k2 ↔ P (k1 + k2) := by
      intro k1 k2
      let gm := mix k hk (rot k hk 4 k1 + c1)
      let nameOf : W k → W k := fun y => (mixEquiv hk hk7 hk3).symm y + rot k hk 3 k1
      have hbij := hnameOf_bij k1
      have hstep1 : prof k1 = prof k2 ↔
          ∀ j : Fin h, ∀ y : W k,
            F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
              F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val)) = 0 := by
        constructor
        · intro hprof j y
          have hp1 := congrFun (congrFun hprof (nameOf y)) j
          have hp2 := congrFun (congrFun hprof (nameOf 0)) j
          simp only [prof, obs, ite_true] at hp1 hp2
          have hdiff : (run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
              run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val))) +
              (run k hk k1 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)) +
              run k hk k2 (nameOf 0) c1 c2 (ix k hk (start.val + j.val))) = 0 := by
            have hadd := congrArg₂ (· + ·) hp1 hp2
            have heq0 :
                (run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                  run k hk k1 0 c1 c2 (ix k hk (start.val + j.val)) +
                  (run k hk k1 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)) +
                  run k hk k1 0 c1 c2 (ix k hk (start.val + j.val)))) +
                (run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                  run k hk k2 0 c1 c2 (ix k hk (start.val + j.val)) +
                  (run k hk k2 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)) +
                  run k hk k2 0 c1 c2 (ix k hk (start.val + j.val)))) = 0 :=
              (zmod2_add_eq_zero _ _).mpr hadd
            have heq : ((run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k1 0 c1 c2 (ix k hk (start.val + j.val)) +
                (run k hk k1 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k1 0 c1 c2 (ix k hk (start.val + j.val)))) +
              (run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k2 0 c1 c2 (ix k hk (start.val + j.val)) +
                (run k hk k2 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k2 0 c1 c2 (ix k hk (start.val + j.val))))) =
              ((run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val))) +
                (run k hk k1 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k2 (nameOf 0) c1 c2 (ix k hk (start.val + j.val)))) +
              (run k hk k1 0 c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k1 0 c1 c2 (ix k hk (start.val + j.val))) +
              (run k hk k2 0 c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k2 0 c1 c2 (ix k hk (start.val + j.val))) := by ring
            rw [heq0, zmod2_add_self, zmod2_add_self, add_zero, add_zero] at heq
            exact heq.symm
          rw [run_add_run_nameOf hk hk7 hk3 c1 c2 k1 k2 y,
            run_add_run_nameOf hk hk7 hk3 c1 c2 k1 k2 0] at hdiff
          have heq : (F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
              rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val))) +
            (F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val)) +
              rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val))) =
            (F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
              F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val))) +
            (rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val)) +
              rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val))) := by ring
          rw [hdiff, zmod2_add_self, add_zero] at heq
          exact heq.symm
        · intro hF
          funext name j
          rcases hbij.2 name with ⟨y, rfl⟩
          rcases hbij.2 0 with ⟨y0, hy0⟩
          simp only [prof, obs, ite_true]
          rw [← hy0]
          have h1 := hF j y
          have h2 := hF j y0
          have h12 : F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
              F k hk (mix k hk (k1 + k2)) gm y0 (ix k hk (start.val + j.val)) = 0 := by
            have heq : (F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
                F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val))) +
              (F k hk (mix k hk (k1 + k2)) gm y0 (ix k hk (start.val + j.val)) +
                F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val))) =
              (F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
                F k hk (mix k hk (k1 + k2)) gm y0 (ix k hk (start.val + j.val))) +
              (F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val)) +
                F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val))) := by ring
            rw [h1, h2, add_zero, zmod2_add_self, add_zero] at heq
            exact heq.symm
          have hr : (run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
              run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val))) +
              (run k hk k1 (nameOf y0) c1 c2 (ix k hk (start.val + j.val)) +
              run k hk k2 (nameOf y0) c1 c2 (ix k hk (start.val + j.val))) = 0 := by
            rw [run_add_run_nameOf hk hk7 hk3 c1 c2 k1 k2 y,
              run_add_run_nameOf hk hk7 hk3 c1 c2 k1 k2 y0]
            calc F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
                  rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val)) +
                  (F k hk (mix k hk (k1 + k2)) gm y0 (ix k hk (start.val + j.val)) +
                  rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val)))
                = (F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
                    F k hk (mix k hk (k1 + k2)) gm y0 (ix k hk (start.val + j.val))) +
                  (rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val)) +
                    rot k hk 7 (k1 + k2) (ix k hk (start.val + j.val))) := by ring
              _ = 0 := by rw [h12, zmod2_add_self, add_zero]
          apply (zmod2_add_eq_zero _ _).mp
          calc run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k1 (nameOf y0) c1 c2 (ix k hk (start.val + j.val)) +
                (run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                run k hk k2 (nameOf y0) c1 c2 (ix k hk (start.val + j.val)))
              = (run k hk k1 (nameOf y) c1 c2 (ix k hk (start.val + j.val)) +
                  run k hk k2 (nameOf y) c1 c2 (ix k hk (start.val + j.val))) +
                (run k hk k1 (nameOf y0) c1 c2 (ix k hk (start.val + j.val)) +
                  run k hk k2 (nameOf y0) c1 c2 (ix k hk (start.val + j.val))) := by ring
            _ = 0 := hr
      rw [hstep1]
      have hstep2 : (∀ j : Fin h, ∀ y : W k,
          F k hk (mix k hk (k1 + k2)) gm y (ix k hk (start.val + j.val)) +
            F k hk (mix k hk (k1 + k2)) gm 0 (ix k hk (start.val + j.val)) = 0) ↔
          (∀ j : Fin h, ∀ m < 8,
            mix k hk (k1 + k2) (ix k hk ((ix k hk (start.val + j.val)).val + 2 * k - 4 + m)) = 0) := by
        constructor <;> intro H j
        · exact (single_site_const_iff hk hk7 (mix k hk (k1 + k2)) gm (ix k hk (start.val + j.val))).mp (H j)
        · exact (single_site_const_iff hk hk7 (mix k hk (k1 + k2)) gm (ix k hk (start.val + j.val))).mpr (H j)
      rw [hstep2]
      constructor
      · intro H n hn
        by_cases hnh : n < h
        · have h1 := H ⟨n, hnh⟩ 0 (by decide)
          have hix : ix k hk ((ix k hk (start.val + n)).val + 2 * k - 4 + 0) =
              ix k hk (start.val + 2 * k - 4 + n) := by
            change ix k hk ((start.val + n) % k + 2 * k - 4 + 0) = _
            have heq1 : (start.val + n) % k + 2 * k - 4 + 0 = (start.val + n) % k + (2 * k - 4) := by omega
            have heq2 : start.val + n + (2 * k - 4) = start.val + 2 * k - 4 + n := by omega
            rw [heq1, ix_add_mod_left, heq2]
          rwa [hix] at h1
        · have h1 := H ⟨h - 1, by omega⟩ (n - (h - 1)) (by omega)
          have hix : ix k hk ((ix k hk (start.val + (h - 1))).val + 2 * k - 4 + (n - (h - 1))) =
              ix k hk (start.val + 2 * k - 4 + n) := by
            change ix k hk ((start.val + (h - 1)) % k + 2 * k - 4 + (n - (h - 1))) = _
            have heq1 : (start.val + (h - 1)) % k + 2 * k - 4 + (n - (h - 1)) =
                (start.val + (h - 1)) % k + (2 * k - 4 + (n - (h - 1))) := by omega
            have heq2 : start.val + (h - 1) + (2 * k - 4 + (n - (h - 1))) =
                start.val + 2 * k - 4 + n := by omega
            rw [heq1, ix_add_mod_left, heq2]
          rwa [hix] at h1
      · intro H j m hm
        have hix : ix k hk ((ix k hk (start.val + j.val)).val + 2 * k - 4 + m) =
            ix k hk (start.val + 2 * k - 4 + (j.val + m)) := by
          change ix k hk ((start.val + j.val) % k + 2 * k - 4 + m) = _
          have heq1 : (start.val + j.val) % k + 2 * k - 4 + m =
              (start.val + j.val) % k + (2 * k - 4 + m) := by omega
          have heq2 : start.val + j.val + (2 * k - 4 + m) =
              start.val + 2 * k - 4 + (j.val + m) := by omega
          rw [heq1, ix_add_mod_left, heq2]
        rw [hix]
        exact H (j.val + m) (by omega)
    have hcardP : Fintype.card {δ : W k // P δ} = 2 ^ (k - corrected) := by
      convert card_allow_true hk hk7 hk3 start
    conv_rhs => simp only [ite_true]
    rw [card_image_eq_pow prof P hiff corrected (min_le_left k (h + 7)) hcardP]

end PEqualNP.Outside.L_meta_29748_aux

theorem PEqualNP.Outside.L_meta_29748 : (∀ (k : ℕ) (hk : 0 < k), 7 ≤ k → k % 3 ≠ 0 →
  let W := Fin k → ZMod 2
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-(s % k)))
  let mix := fun (x : W) (i : Fin k) => x i + x (ix (i.val+2)) + rot 2 x i
  let upd := fun (x : W) (i : Fin k) =>
    let y := mix x
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2))
  let run := fun (key name c1 c2 : W) =>
    upd (upd (rot 3 key + name) + rot 4 key + c1) + rot 7 key + c2
  ∀ (c1 c2 : W) (start : Fin k) (h : ℕ), 0 < h → h ≤ k →
    let corrected := min k (h+7)
    let exception := (k=11 ∧ h=2) ∨ (k=13 ∧ h=3)
    let ordinary := min k (h+7+min h 4) - (if exception then 1 else 0)
    ∀ (allow : Bool) (N : ℕ),
      Iff (∃ (tag : W → Fin N) (decode : Fin N → W → Fin h → ZMod 2)
          (bias : W → Fin h → ZMod 2),
        ∀ (key name : W) (j : Fin h), run key name c1 c2 (ix (start.val+j.val)) =
          (if allow then bias key j else 0) + decode (tag key) name j)
        (2^(if allow then corrected else ordinary) ≤ N)) :=
  PEqualNP.Outside.L_meta_29748_aux.main_theorem
