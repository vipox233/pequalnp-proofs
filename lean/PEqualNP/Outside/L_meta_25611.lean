import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25611

private lemma z2two : (2 : ZMod 2) = 0 := by simpa using (ZMod.natCast_self 2)

private lemma z2addself (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, z2two, zero_mul]

private def b256 (b : Bool) : ZMod 2 := if b then 1 else 0

@[simp] private lemma b256xor (a b : Bool) : b256 (xor a b) = b256 a + b256 b := by
  cases a <;> cases b <;> decide

@[simp] private lemma b256and (a b : Bool) : b256 (a && b) = b256 a * b256 b := by
  cases a <;> cases b <;> decide

@[simp] private lemma b256not (a : Bool) : b256 (!a) = 1 + b256 a := by
  cases a <;> decide

private lemma b256inj {a b : Bool} (h : b256 a = b256 b) : a = b := by
  cases a <;> cases b <;> simp [b256] at h ⊢

private lemma b256fold (b : Bool) (l : List Bool) :
    b256 (l.foldl xor b) = b256 b + (l.map b256).sum := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih => simp [List.foldl, ih, add_assoc]

private lemma b256sumBits (k : ℕ) (w : Fin k → Bool) :
    b256 ((List.ofFn w).foldl xor false) = ∑ i : Fin k, b256 (w i) := by
  induction k with
  | zero => simp [b256]
  | succ k ih =>
      rw [List.ofFn_succ']
      simp [b256fold, ih, Fin.sum_univ_castSucc]

private def n256 (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt n hk⟩

private lemma n256add (k : ℕ) (hk : 0 < k) (i t : Fin k) :
    n256 k hk (i.val + t.val) = i + t := by
  ext
  simp [n256, Fin.add_def]

private lemma n256sub (k : ℕ) (hk : 0 < k) (d : ℕ) (i : Fin k) :
    n256 k hk (i.val + (k - d % k)) = i + (-(n256 k hk d)) := by
  ext
  simp [n256, Fin.add_def, Fin.neg_def, Nat.add_mod]

private def r256 (k : ℕ) [NeZero k] (t : Fin k) (v : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  fun i => v (i + t)

private lemma r256add (k : ℕ) [NeZero k] (t : Fin k) (u v : Fin k → ZMod 2) :
    r256 k t (fun i => u i + v i) = fun i => r256 k t u i + r256 k t v i := by
  rfl

private lemma r256comp (k : ℕ) [NeZero k] (s t : Fin k) (v : Fin k → ZMod 2) :
    r256 k s (r256 k t v) = r256 k (t + s) v := by
  ext i
  simp [r256, add_assoc, add_comm, add_left_comm]

private def p256 (k : ℕ) [NeZero k] (T : Fin k → ZMod 2) (v : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  fun i => ∑ t : Fin k, T t * v (i + t)

private lemma p256add (k : ℕ) [NeZero k] (T : Fin k → ZMod 2) (u v : Fin k → ZMod 2) :
    p256 k T (fun i => u i + v i) = fun i => p256 k T u i + p256 k T v i := by
  ext i
  simp [p256, mul_add, Finset.sum_add_distrib]

private lemma p256rot (k : ℕ) [NeZero k] (T : Fin k → ZMod 2) (s : Fin k) (v : Fin k → ZMod 2) :
    r256 k s (p256 k T v) = p256 k T (r256 k s v) := by
  ext i
  simp [r256, p256, add_assoc, add_comm, add_left_comm]

private def m256 (k : ℕ) [NeZero k] (d : Fin k) (v : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  fun i => v i + v (i + d) + v (i - d)

private lemma m256add (k : ℕ) [NeZero k] (d : Fin k) (u v : Fin k → ZMod 2) :
    m256 k d (fun i => u i + v i) = fun i => m256 k d u i + m256 k d v i := by
  ext i
  simp [m256]
  ring

private lemma m256rot (k : ℕ) [NeZero k] (d s : Fin k) (v : Fin k → ZMod 2) :
    r256 k s (m256 k d v) = m256 k d (r256 k s v) := by
  ext i
  simp only [r256, m256]
  congr 1 <;> abel

private lemma m256p256 (k : ℕ) [NeZero k] (T : Fin k → ZMod 2) (d : Fin k) (v : Fin k → ZMod 2) :
    m256 k d (p256 k T v) = p256 k T (m256 k d v) := by
  ext i
  simp only [m256, p256, mul_add, Finset.sum_add_distrib]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  abel
  apply Finset.sum_congr rfl
  intro t ht
  congr 1
  abel

private lemma n256nat (k : ℕ) (hk : 0 < k) (i : Fin k) (n : ℕ) :
    n256 k hk (i.val + n) = i + n256 k hk n := by
  ext
  simp [n256, Fin.add_def, Nat.add_mod]

private lemma n256zero (k : ℕ) (hk : 0 < k) (n : ℕ) :
    n256 k hk (k - n % k) = -(n256 k hk n) := by
  ext
  simp [n256, Fin.neg_def]

private def q256 (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2) (y : Fin k → ZMod 2) : ZMod 2 :=
  ∑ i : Fin k, M i * y (n256 k hk (i.val + 1)) * y (n256 k hk (i.val + 2))

private def c256 (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2)
    (u v : Fin k → ZMod 2) : ZMod 2 :=
  ∑ i : Fin k, M i *
    (u (n256 k hk (i.val + 1)) * v (n256 k hk (i.val + 2)) +
     v (n256 k hk (i.val + 1)) * u (n256 k hk (i.val + 2)))

private lemma q256add (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2)
    (u v : Fin k → ZMod 2) :
    q256 k hk M (fun i => u i + v i) = q256 k hk M u + q256 k hk M v + c256 k hk M u v := by
  simp [q256, c256, n256nat, mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf

private lemma c256add_left (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2)
    (u₁ u₂ v : Fin k → ZMod 2) :
    c256 k hk M (fun i => u₁ i + u₂ i) v = c256 k hk M u₁ v + c256 k hk M u₂ v := by
  simp [c256, n256nat, mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf

private lemma c256add_right (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2)
    (u v₁ v₂ : Fin k → ZMod 2) :
    c256 k hk M u (fun i => v₁ i + v₂ i) = c256 k hk M u v₁ + c256 k hk M u v₂ := by
  simp [c256, n256nat, mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf

private lemma sum_shift_coef (k : ℕ) [NeZero k] (M T : Fin k → ZMod 2)
    (hcoef : ∀ i t : Fin k, M i * T t = M (i + t) * T (-t))
    (f g : Fin k → ZMod 2) :
    (∑ i : Fin k, ∑ t : Fin k, M i * T t * f (i + t) * g i) =
      ∑ i : Fin k, ∑ t : Fin k, M i * T t * f i * g (i + t) := by
  calc
    (∑ i : Fin k, ∑ t : Fin k, M i * T t * f (i + t) * g i)
        = ∑ i : Fin k, ∑ t : Fin k, M (i + t) * T (-t) * f (i + t) * g i := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro t ht
            rw [hcoef]
    _ = ∑ t : Fin k, ∑ i : Fin k, M (i + t) * T (-t) * f (i + t) * g i := by
            rw [Finset.sum_comm]
    _ = ∑ t : Fin k, ∑ i : Fin k, M i * T (-t) * f i * g (i - t) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [← Equiv.sum_comp (Equiv.addRight (-t))
              (fun i : Fin k => M (i + t) * T (-t) * f (i + t) * g i)]
            apply Finset.sum_congr rfl
            intro i hi
            simp [sub_eq_add_neg, add_assoc]
    _ = ∑ i : Fin k, ∑ t : Fin k, M i * T t * f i * g (i + t) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Equiv.sum_comp (Equiv.neg (Fin k))
              (fun t : Fin k => M i * T (-t) * f i * g (i - t))]
            apply Finset.sum_congr rfl
            intro t ht
            simp [sub_eq_add_neg]

private lemma c256proj (k : ℕ) (hk : 0 < k) [NeZero k] (M T : Fin k → ZMod 2)
    (hcoef : ∀ i t : Fin k, M i * T t = M (i + t) * T (-t))
    (u v : Fin k → ZMod 2) :
    c256 k hk M (p256 k T u) v = c256 k hk M u (p256 k T v) := by
  have h1 := sum_shift_coef k M T hcoef (fun j : Fin k => u (j + n256 k hk 1))
    (fun j : Fin k => v (j + n256 k hk 2))
  have h2 := sum_shift_coef k M T hcoef (fun j : Fin k => v (j + n256 k hk 1))
    (fun j : Fin k => u (j + n256 k hk 2))
  simp [c256, p256, n256nat, Finset.sum_mul, Finset.mul_sum, mul_add, add_mul,
    Finset.sum_add_distrib] at h1 h2 ⊢
  have h1' :
      (∑ x : Fin k, ∑ i : Fin k, M x * (T i * u (x + n256 k hk 1 + i) * v (x + n256 k hk 2))) =
        ∑ x : Fin k, ∑ i : Fin k, M x * (u (x + n256 k hk 1) * (T i * v (x + n256 k hk 2 + i))) := by
    simpa [add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using h1
  have h2' :
      (∑ x : Fin k, ∑ i : Fin k, M x * (v (x + n256 k hk 1) * (T i * u (x + n256 k hk 2 + i)))) =
        ∑ x : Fin k, ∑ i : Fin k, M x * (T i * v (x + n256 k hk 1 + i) * u (x + n256 k hk 2)) := by
    simpa [add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using h2.symm
  rw [h1', h2']

private def lin256 (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2) (y : Fin k → ZMod 2) : ZMod 2 :=
  ∑ i : Fin k, M i * (y i + y (n256 k hk (i.val + 2)))

private lemma lin256add (k : ℕ) (hk : 0 < k) (M : Fin k → ZMod 2)
    (u v : Fin k → ZMod 2) :
    lin256 k hk M (fun i => u i + v i) = lin256 k hk M u + lin256 k hk M v := by
  simp [lin256, n256nat, mul_add, Finset.sum_add_distrib]
  ring_nf

private lemma b256proj (k : ℕ) (hk : 0 < k) [NeZero k] (tap : Fin k → Bool)
    (z : Fin k → Bool) (j : Fin k) :
    b256 ((List.ofFn (fun t : Fin k => tap t && z (n256 k hk (j.val + t.val)))).foldl xor false) =
      p256 k (fun t => b256 (tap t)) (fun i => b256 (z i)) j := by
  rw [b256sumBits]
  simp [p256, n256add]

private lemma b256mix (k : ℕ) (hk : 0 < k) [NeZero k] (d : ℕ) (w : Fin k → Bool)
    (i : Fin k) :
    b256 (xor (xor (w i) (w (n256 k hk (i.val + d))))
      (w (n256 k hk (i.val + (k - d % k))))) =
      m256 k (n256 k hk d) (fun j => b256 (w j)) i := by
  simp only [b256xor]
  rw [n256nat k hk i d]
  rw [n256sub k hk d i]
  simp [m256, sub_eq_add_neg]

private lemma b256observed (k : ℕ) (hk : 0 < k) (mask : Fin k → Bool) (y : Fin k → Bool) :
    b256 ((List.ofFn (fun bit : Fin k => mask bit &&
      xor (y bit) (!(y (n256 k hk (bit.val + 1))) && y (n256 k hk (bit.val + 2))))).foldl xor false) =
      lin256 k hk (fun i => b256 (mask i)) (fun i => b256 (y i)) +
        q256 k hk (fun i => b256 (mask i)) (fun i => b256 (y i)) := by
  rw [b256sumBits]
  simp [lin256, q256, b256and, b256xor, b256not, n256nat, mul_add, add_mul, Finset.sum_add_distrib]
  ring_nf

private def u256 (x : ZMod 2) : Bool := if x = 0 then false else true

private lemma b256u (x : ZMod 2) : b256 (u256 x) = x := by
  have hv : x.val = 0 ∨ x.val = 1 := by
    have hlt := ZMod.val_lt x
    omega
  rcases hv with hv | hv
  · have hx : x = 0 := by
      rw [← ZMod.natCast_zmod_val x, hv]
      simp
    simp [u256, hx, b256]
  · have hx : x = 1 := by
      rw [← ZMod.natCast_zmod_val x, hv]
      simp
    simp [u256, hx, b256]

private lemma c256proj_vanish (k : ℕ) (hk : 0 < k) [NeZero k]
    (M T : Fin k → ZMod 2)
    (hcoef : ∀ i t : Fin k, M i * T t = M (i + t) * T (-t))
    (hidem : ∀ v : Fin k → ZMod 2, p256 k T (p256 k T v) = p256 k T v)
    (x y : Fin k → ZMod 2) :
    c256 k hk M (p256 k T x) (fun i => y i + p256 k T y i) = 0 := by
  rw [c256add_right]
  rw [c256proj k hk M T hcoef x y]
  rw [c256proj k hk M T hcoef x (p256 k T y)]
  rw [hidem y]
  rw [z2addself]

private lemma n256third (k : ℕ) (hk : 0 < k) (d : ℕ) (i : Fin k) :
    n256 k hk (i.val + k - d % k) = i + -(n256 k hk d) := by
  have heq : i.val + k - d % k = i.val + (k - d % k) := by
    have hlt := Nat.mod_lt d hk
    omega
  rw [heq, n256sub]

private lemma z2three (x : ZMod 2) : x + x + x = x := by
  rw [z2addself x, zero_add]

private lemma z2sum_eq (a b c : ZMod 2) (h : a + b + c = 0) : c = a + b := by
  have h' := congrArg (fun x : ZMod 2 => x + c) h
  simpa [add_assoc, z2addself] using h'.symm

private lemma z2eq_of_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  have h' := congrArg (fun z : ZMod 2 => z + y) h
  simpa [add_assoc, z2addself] using h'

private lemma val_nsmul_fin (k : ℕ) [NeZero k] (a : Fin k) (n : ℕ) :
    ((n • a : Fin k).val) = (n * a.val) % k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, Fin.val_add, ih]
      simp [Nat.succ_mul, Nat.add_mod, Nat.mul_mod]

private lemma m256_zero (k : ℕ) (hk : 0 < k) (h3 : k % 3 ≠ 0) [NeZero k]
    (D : Fin k) (v : Fin k → ZMod 2) (hv : m256 k D v = 0) : v = 0 := by
  by_cases hk1 : k = 1
  · subst k
    ext i
    have hi := congrFun hv i
    have hidx1 : i + D = i := Subsingleton.elim _ _
    have hidx2 : i - D = i := Subsingleton.elim _ _
    rw [m256, hidx1, hidx2] at hi
    simpa [z2three] using hi
  · have hkgt : 1 < k := by omega
    have hcop : Nat.Coprime 3 k := by
      rw [Nat.prime_three.coprime_iff_not_dvd]
      intro hd
      exact h3 (Nat.mod_eq_zero_of_dvd hd)
    obtain ⟨m, hm_lt, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hkgt
    have hvpt : ∀ j : Fin k, v j + v (j + D) + v (j - D) = 0 := by
      intro j
      have hj := congrFun hv j
      simpa [m256] using hj
    have hD : (3 * m) • D = D := by
      ext
      rw [val_nsmul_fin]
      rw [Nat.mul_mod, hm, one_mul, Nat.mod_mod]
      exact Nat.mod_eq_of_lt D.isLt
    have hshift : ∀ i : Fin k, v (i + D) = v i := by
      intro i
      let g : ℕ → ZMod 2 := fun n => v (i + n • D)
      have hper : ∀ n, g (n + 3) = g n := by
        intro n
        have h1 := hvpt (i + (n + 1) • D)
        have h2 := hvpt (i + (n + 2) • D)
        have hi1 : (i + (n + 1) • D) + D = i + (n + 2) • D := by
          simp [succ_nsmul, add_assoc]
        have hi2 : (i + (n + 1) • D) - D = i + n • D := by
          rw [succ_nsmul]
          abel
        have hi3 : (i + (n + 2) • D) + D = i + (n + 3) • D := by
          simp [succ_nsmul, add_assoc]
        have hi4 : (i + (n + 2) • D) - D = i + (n + 1) • D := by
          rw [succ_nsmul]
          abel
        have h1' : g (n + 1) + g (n + 2) + g n = 0 := by
          simpa [g, hi1, hi2] using h1
        have h2' : g (n + 2) + g (n + 3) + g (n + 1) = 0 := by
          simpa [g, hi3, hi4] using h2
        have hh1 : g n = g (n + 1) + g (n + 2) := z2sum_eq _ _ _ h1'
        have h2'' : g (n + 2) + g (n + 1) + g (n + 3) = 0 := by
          simpa [add_assoc, add_comm, add_left_comm] using h2'
        have hh2 : g (n + 3) = g (n + 2) + g (n + 1) := z2sum_eq _ _ _ h2''
        rw [hh2, hh1]
        abel
      have hf3m_all : ∀ n, g (3 * n) = g 0 := by
        intro n
        induction n with
        | zero => simp [g]
        | succ n ih =>
            rw [Nat.mul_succ]
            rw [hper (3 * n), ih]
      have hg := hf3m_all m
      have hg' : g (3 * m) = g 1 := by simp [g, hD]
      have h10 : g 1 = g 0 := hg'.symm.trans hg
      simpa [g] using h10
    ext i
    have hiD : v (i - D) = v i := by
      have hs := hshift (i - D)
      simpa using hs.symm
    have hi0 := hvpt i
    rw [hshift i, hiD] at hi0
    simpa [z2three] using hi0

private lemma nsmul_one_eq (k : ℕ) (hk : 0 < k) [NeZero k] (n : ℕ) :
    n • n256 k hk 1 = n256 k hk n := by
  ext
  rw [val_nsmul_fin]
  change (n * (1 % k)) % k = n % k
  have h1 : 1 % k ≡ 1 [MOD k] := Nat.mod_modEq 1 k
  have heq : (n * (1 % k)) % k = (n * 1) % k := h1.mul_left n
  rw [heq, mul_one]

private lemma nsmul_two_inv (k : ℕ) (hk : 0 < k) [NeZero k] (m : ℕ)
    (hm : 2 * m % k = 1) (t : Fin k) :
    (m * t.val) • n256 k hk 2 = t := by
  ext
  rw [val_nsmul_fin]
  change (m * t.val * (2 % k)) % k = t.val
  have hm2 : 2 % k ≡ 2 [MOD k] := Nat.mod_modEq 2 k
  have heq : ((m * t.val) * (2 % k)) % k = ((m * t.val) * 2) % k := hm2.mul_left _
  rw [heq]
  rw [show m * t.val * 2 = (2 * m) * t.val by ring]
  rw [Nat.mul_mod, hm, one_mul, Nat.mod_mod]
  exact Nat.mod_eq_of_lt t.isLt

private lemma nsmul_two_even (k : ℕ) (hk : 0 < k) [NeZero k] (t : Fin k)
    (heven : t.val % 2 = 0) :
    (t.val / 2) • n256 k hk 2 = t := by
  ext
  rw [val_nsmul_fin]
  change ((t.val / 2) * (2 % k)) % k = t.val
  have hm2 : 2 % k ≡ 2 [MOD k] := Nat.mod_modEq 2 k
  have heq : ((t.val / 2) * (2 % k)) % k = ((t.val / 2) * 2) % k := hm2.mul_left _
  rw [heq]
  have ht : t.val / 2 * 2 = t.val := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero heven)
  rw [ht, Nat.mod_eq_of_lt t.isLt]

private lemma neg_val_odd (k : ℕ) [NeZero k] (hkeven : k % 2 = 0) (t : Fin k)
    (htodd : t.val % 2 = 1) : ((-t : Fin k).val) % 2 = 1 := by
  have htne : t ≠ 0 := by
    intro h
    subst t
    simp at htodd
  rw [Fin.val_neg, if_neg htne]
  omega

private lemma tap_odd_zero (k : ℕ) [NeZero k] (T : Fin k → ZMod 2)
    (hidem : ∀ j : Fin k, ∑ t : Fin k, T t * T (j - t) = T j)
    (hkeven : k % 2 = 0) (s : Fin k) (hsodd : s.val % 2 = 1) : T s = 0 := by
  classical
  let g : Fin k → Fin k := fun i => s - i
  let f : Fin k → ZMod 2 := fun i => T i * T (s - i)
  have hg2invol : ∀ i, g (g i) = i := by
    intro i
    simp [g]
  have hf_inv : ∀ i, f i + f (g i) = 0 := by
    intro i
    simpa [f, g, mul_comm] using z2addself (T i * T (s - i))
  have hnofix : ∀ i, f i ≠ 0 → g i ≠ i := by
    intro i hfi hfix
    have hs_eq : s = i + i := by
      exact (sub_eq_iff_eq_add.mp hfix)
    have hsval : s.val = (2 * i.val) % k := by
      simpa [Fin.add_def, two_mul] using congrArg Fin.val hs_eq
    have hmodeq : s.val ≡ 2 * i.val [MOD k] := by
      rw [hsval]
      exact Nat.mod_modEq _ _
    have h2dvd : 2 ∣ k := Nat.dvd_of_mod_eq_zero hkeven
    have hmodeq2 : s.val ≡ 2 * i.val [MOD 2] := hmodeq.of_dvd h2dvd
    have hs2' : s.val % 2 = (2 * i.val) % 2 := hmodeq2
    have hs2 : s.val % 2 = 0 := by simpa using hs2'
    omega
  have hsum : (∑ i : Fin k, f i) = 0 := by
    exact Finset.sum_ninvolution g hf_inv hnofix (by simp) hg2invol
  simpa [f] using (hidem s).symm.trans hsum

private def d256 (k : ℕ) [NeZero k] (p : Fin k) : Fin k → ZMod 2 :=
  fun j => if j = p then 1 else 0

private lemma p256delta (k : ℕ) [NeZero k] (T : Fin k → ZMod 2) (p j : Fin k) :
    p256 k T (d256 k p) j = T (p - j) := by
  classical
  simp only [p256]
  rw [Finset.sum_eq_single (p - j)]
  · congr 1
    simp [d256]
  · intro b hb hne
    have hbne : j + b ≠ p := by
      intro h
      apply hne
      rw [← h]
      abel
    simp [d256, hbne]
  · simp

private lemma n256two (k : ℕ) (hk : 0 < k) :
    n256 k hk 2 = n256 k hk 1 + n256 k hk 1 := by
  ext
  simp [n256, Fin.add_def]

private lemma sum_delta_shift (k : ℕ) [NeZero k] (f : Fin k → ZMod 2) (p a : Fin k) :
    (∑ x : Fin k, if x + a = p then f x else 0) = f (p - a) := by
  classical
  rw [Finset.sum_eq_single (p - a)]
  · congr 1
    simp
  · intro b hb hne
    have hbne : b + a ≠ p := by
      intro h
      apply hne
      rw [← h]
      abel
    simp [hbne]
  · simp

private lemma c256delta (k : ℕ) (hk : 0 < k) [NeZero k] (M : Fin k → ZMod 2)
    (u : Fin k → ZMod 2) (p : Fin k) :
    c256 k hk M u (d256 k p) =
      M (p - n256 k hk 2) * u (p - n256 k hk 1) +
        M (p - n256 k hk 1) * u (p + n256 k hk 1) := by
  classical
  simp [c256, d256, n256nat, mul_add, Finset.sum_add_distrib]
  rw [sum_delta_shift k (fun x => M x * u (x + n256 k hk 1)) p (n256 k hk 2)]
  rw [sum_delta_shift k (fun x => M x * u (x + n256 k hk 2)) p (n256 k hk 1)]
  congr 1
  · rw [n256two]
    abel
  · rw [n256two]
    abel

private lemma m256_zero_fun (k : ℕ) [NeZero k] (D : Fin k) :
    m256 k D (0 : Fin k → ZMod 2) = 0 := by
  ext i
  simp [m256]

private lemma p256_zero_fun (k : ℕ) [NeZero k] (T : Fin k → ZMod 2) :
    p256 k T (0 : Fin k → ZMod 2) = 0 := by
  ext i
  simp [p256]

private lemma z2twomul (x : ZMod 2) : 2 * x = 0 := by
  rw [z2two, zero_mul]

private lemma z2four : (4 : ZMod 2) = 0 := by
  change (2 : ZMod 2) * 2 = 0
  exact z2twomul 2

private lemma m256_inj (k : ℕ) (hk : 0 < k) (h3 : k % 3 ≠ 0) [NeZero k]
    (D : Fin k) : Function.Injective (m256 k D) := by
  intro u v huv
  have hz : m256 k D (fun i => u i + v i) = 0 := by
    rw [m256add, huv]
    ext i
    exact z2addself (m256 k D v i)
  have hz' := m256_zero k hk h3 D (fun i => u i + v i) hz
  ext i
  have hi := congrFun hz' i
  exact z2eq_of_add_eq_zero hi

private lemma m256_surj (k : ℕ) (hk : 0 < k) (h3 : k % 3 ≠ 0) [NeZero k]
    (D : Fin k) : Function.Surjective (m256 k D) := by
  exact Finite.injective_iff_surjective.mp (m256_inj k hk h3 D)

private lemma n256ksub (k : ℕ) (hk : 0 < k) (t : Fin k) :
    n256 k hk (k - t.val) = -t := by
  ext
  simp [n256, Fin.neg_def]

end PEqualNP.Outside.L_meta_25611

open PEqualNP.Outside.L_meta_25611

theorem PEqualNP.Outside.L_meta_25611 : (∀ (k : ℕ) (hk : 0 < k), k % 3 ≠ 0 →
  let index := fun (n : ℕ) => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : Fin k → Bool) (i : Fin k) => xor (u i) (v i)
  let sumBits := fun (word : Fin k → Bool) => (List.ofFn word).foldl xor false
  ∀ (tap : Fin k → Bool),
  let proj := fun (input : Fin k → Bool) (j : Fin k) =>
    sumBits (fun t => tap t && input (index (j.val + t.val)))
  (∀ z : Fin k → Bool, proj (proj z) = proj z) →
  ∀ (d : ℕ), (d = 1 ∨ d = 2) →
  let mix := fun (w : Fin k → Bool) (pos : Fin k) =>
    xor (xor (w pos) (w (index (pos.val + d)))) (w (index (pos.val + k - d % k)))
  ∀ (base mask : Fin k → Bool),
  let observed := fun (state : Fin k → Bool) =>
    let y := mix state
    sumBits (fun bit => mask bit &&
      xor (y bit) (!(y (index (bit.val + 1))) && y (index (bit.val + 2))))
  (∃ left right : (Fin k → Bool) → Bool,
    ∀ a b : Fin k → Bool,
      observed (add (add base (proj a)) (add b (proj b))) = xor (left a) (right b)) ↔
    ∀ i t : Fin k,
      (mask i && tap t) = (mask (index (i.val + t.val)) && tap (index (k - t.val)))) := by
  intro k hk h3
  haveI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  dsimp only
  intro tap hproj d hd base mask
  constructor
  · rintro ⟨left, right, hsep⟩
    let pr : (Fin k → Bool) → Fin k → Bool := fun input j =>
      (List.ofFn (fun t : Fin k => tap t && input (n256 k hk (j.val + t.val)))).foldl xor false
    let T : Fin k → ZMod 2 := fun t => b256 (tap t)
    let M : Fin k → ZMod 2 := fun i => b256 (mask i)
    let P : (Fin k → ZMod 2) → Fin k → ZMod 2 := p256 k T
    let D : Fin k := n256 k hk d
    let B0 : Fin k → ZMod 2 := fun i => b256 (base i)
    let Lf : (Fin k → Bool) → ZMod 2 := fun a => b256 (left a)
    let Rf : (Fin k → Bool) → ZMod 2 := fun b => b256 (right b)
    let bvec : (Fin k → Bool) → Fin k → ZMod 2 := fun a i => b256 (a i)
    let Sz : (Fin k → ZMod 2) → (Fin k → ZMod 2) → Fin k → ZMod 2 :=
      fun A B i => B0 i + P A i + (B i + P B i)
    let Yz : (Fin k → ZMod 2) → (Fin k → ZMod 2) → Fin k → ZMod 2 :=
      fun A B => m256 k D (Sz A B)
    let Qz : (Fin k → ZMod 2) → (Fin k → ZMod 2) → ZMod 2 :=
      fun A B => lin256 k hk M (Yz A B) + q256 k hk M (Yz A B)
    have hprZ : ∀ (w : Fin k → Bool) (j : Fin k), b256 (pr w j) = P (fun i => b256 (w i)) j := by
      intro w j
      simpa [pr, P, T] using b256proj k hk tap w j
    have hsepZ : ∀ a b : Fin k → Bool, Qz (bvec a) (bvec b) = Lf a + Rf b := by
      intro a b
      have hs := congrArg b256 (hsep a b)
      rw [b256xor] at hs
      let state : Fin k → Bool := fun i => xor (xor (base i) (pr a i)) (xor (b i) (pr b i))
      let yy : Fin k → Bool := fun pos =>
        xor (xor (state pos) (state (n256 k hk (pos.val + d))))
          (state (n256 k hk (pos.val + k - d % k)))
      change b256 ((List.ofFn (fun bit : Fin k => mask bit &&
        xor (yy bit) (!(yy (n256 k hk (bit.val + 1))) &&
          yy (n256 k hk (bit.val + 2))))).foldl xor false) = Lf a + Rf b at hs
      rw [b256observed] at hs
      have hyy : (fun i => b256 (yy i)) = m256 k D (fun i => b256 (state i)) := by
        ext i
        simp only [yy]
        rw [show n256 k hk (i.val + k - d % k) = i + -D by simpa [D] using n256third k hk d i]
        simpa [D, n256sub, sub_eq_add_neg] using b256mix k hk d state i
      rw [hyy] at hs
      have hstate : (fun i => b256 (state i)) =
          fun i => B0 i + P (bvec a) i + (bvec b i + P (bvec b) i) := by
        ext i
        simp [state, b256xor, B0, bvec, hprZ a i, hprZ b i]
        abel
      rw [hstate] at hs
      simpa [Qz, Yz, Sz] using hs
    have hsepZZ : ∀ A B : Fin k → ZMod 2,
        Qz A B = Lf (fun i => u256 (A i)) + Rf (fun i => u256 (B i)) := by
      intro A B
      have h := hsepZ (fun i => u256 (A i)) (fun i => u256 (B i))
      simpa [bvec, b256u] using h
    have hfour : ∀ A A' B B' : Fin k → ZMod 2,
        Qz A B + Qz A' B + Qz A B' + Qz A' B' = 0 := by
      intro A A' B B'
      rw [hsepZZ A B, hsepZZ A' B, hsepZZ A B', hsepZZ A' B']
      abel_nf
      simp [two_nsmul, z2two]
    have hpr : ∀ z : Fin k → Bool, pr (pr z) = pr z := by
      intro z
      simpa [pr, n256] using hproj z
    have hidemP : ∀ v : Fin k → ZMod 2, P (P v) = P v := by
      intro v
      ext j
      let z : Fin k → Bool := fun i => u256 (v i)
      have hz : (fun i => b256 (z i)) = v := by
        ext i
        simp [z, b256u]
      have hp := congrArg (fun w : Fin k → Bool => b256 (w j)) (hpr z)
      rw [hprZ (pr z) j, hprZ z j] at hp
      have hf : (fun i => b256 (pr z i)) = P v := by
        ext i
        rw [hprZ z i, hz]
      rw [hf, hz] at hp
      exact hp
    have hidemTap : ∀ j : Fin k, ∑ t : Fin k, T t * T (j - t) = T j := by
      intro j
      have h := congrFun (hidemP (d256 k j)) (⟨0, hk⟩ : Fin k)
      have hinner : P (d256 k j) = fun q => T (j - q) := by
        ext q
        exact p256delta k T j q
      rw [hinner] at h
      simpa [P, T, p256] using h
    let C : Fin k → ZMod 2 := m256 k D B0
    let UA : (Fin k → ZMod 2) → Fin k → ZMod 2 := fun A => P (m256 k D A)
    let VB : (Fin k → ZMod 2) → Fin k → ZMod 2 :=
      fun B => m256 k D (fun i => B i + P B i)
    have hsplit : ∀ A B : Fin k → ZMod 2,
        Yz A B = fun i => C i + UA A i + VB B i := by
      intro A B
      ext i
      simp [Yz, Sz, C, UA, VB, B0, P, m256add, m256p256]
    have hsplitA0 : ∀ A : Fin k → ZMod 2,
        Yz A 0 = fun i => C i + UA A i := by
      intro A
      ext i
      simp [Yz, Sz, C, UA, P, B0, m256add, m256p256, m256_zero_fun,
        p256_zero_fun, z2addself]
    have hsplit0B : ∀ B : Fin k → ZMod 2,
        Yz 0 B = fun i => C i + VB B i := by
      intro B
      ext i
      simp [Yz, Sz, C, VB, B0, P, m256add, m256p256, m256_zero_fun,
        p256_zero_fun, z2addself]
    have hsplit00 : Yz 0 0 = C := by
      ext i
      simp [Yz, Sz, C, B0, P, m256_zero_fun, p256_zero_fun, z2addself]
    have hiden : ∀ A B : Fin k → ZMod 2,
        Qz A B + Qz 0 B + Qz A 0 + Qz 0 0 = c256 k hk M (UA A) (VB B) := by
      intro A B
      dsimp [Qz]
      rw [hsplit A B, hsplit0B B, hsplitA0 A, hsplit00]
      simp [Qz, lin256add, q256add, c256add_left, c256add_right]
      abel_nf
      simp [z2twomul, z2four]
    have hcross : ∀ A B : Fin k → ZMod 2, c256 k hk M (UA A) (VB B) = 0 := by
      intro A B
      have hf := hfour A 0 B 0
      rw [hiden A B] at hf
      exact hf
    have hcross_all : ∀ x y : Fin k → ZMod 2,
        c256 k hk M (P x) (fun i => y i + P y i) = 0 := by
      intro x y
      obtain ⟨x0, hx0⟩ := m256_surj k hk h3 D x
      obtain ⟨y0, hy0⟩ := m256_surj k hk h3 D y
      rw [← hx0, ← hy0]
      have hy' : m256 k D (fun i => y0 i + P y0 i) =
          fun i => m256 k D y0 i + P (m256 k D y0) i := by
        rw [m256add]
        rw [show m256 k D (P y0) = P (m256 k D y0) by simpa [P] using m256p256 k T D y0]
      rw [← hy']
      simpa [UA, VB] using hcross x0 y0
    have hcomm : ∀ u v : Fin k → ZMod 2,
        c256 k hk M u v = c256 k hk M v u := by
      intro u v
      simp [c256, add_comm, mul_comm, mul_left_comm, mul_assoc]
    have hproj_eq : ∀ x y : Fin k → ZMod 2,
        c256 k hk M (P x) y = c256 k hk M x (P y) := by
      intro x y
      have h1 := hcross_all x y
      have h2 := hcross_all y x
      rw [c256add_right] at h1 h2
      have e1 := z2eq_of_add_eq_zero h1
      have e2 := z2eq_of_add_eq_zero h2
      calc
        c256 k hk M (P x) y = c256 k hk M (P x) (P y) := e1
        _ = c256 k hk M (P y) (P x) := hcomm (P x) (P y)
        _ = c256 k hk M (P y) x := e2.symm
        _ = c256 k hk M x (P y) := hcomm (P y) x
    let F : Fin k → Fin k → ZMod 2 := fun u t => M u * T t + M (u + t) * T (-t)
    have hFrec : ∀ u t : Fin k,
        F u t = F (u + n256 k hk 1) (t - n256 k hk 2) := by
      intro u t
      let p : Fin k := u + t + n256 k hk 1
      let q : Fin k := u + n256 k hk 2
      have h := hproj_eq (d256 k p) (d256 k q)
      have hp : p256 k T (d256 k p) = fun j => T (p - j) := by
        ext j
        exact p256delta k T p j
      have hq : p256 k T (d256 k q) = fun j => T (q - j) := by
        ext j
        exact p256delta k T q j
      rw [c256delta k hk M (p256 k T (d256 k p)) q] at h
      rw [hp] at h
      rw [hcomm (d256 k p) (p256 k T (d256 k q))] at h
      rw [c256delta k hk M (p256 k T (d256 k q)) p] at h
      rw [hq] at h
      dsimp [p, q] at h
      have hA : M (q - n256 k hk 2) * T (p - (q - n256 k hk 1)) = M u * T t := by
        dsimp [p, q]
        rw [n256two]
        congr 1 <;> abel
      have hB : M (q - n256 k hk 1) * T (p - (q + n256 k hk 1)) =
          M (u + n256 k hk 1) * T (t - n256 k hk 2) := by
        dsimp [p, q]
        rw [n256two]
        congr 1 <;> abel
      have hC : M (p - n256 k hk 2) * T (q - (p - n256 k hk 1)) =
          M (u + t - n256 k hk 1) * T (n256 k hk 2 - t) := by
        dsimp [p, q]
        rw [n256two]
        congr 1 <;> abel
      have hD : M (p - n256 k hk 1) * T (q - (p + n256 k hk 1)) = M (u + t) * T (-t) := by
        dsimp [p, q]
        rw [n256two]
        congr 1 <;> abel
      rw [hA, hB, hC, hD] at h
      dsimp [F]
      have hidx : u + n256 k hk 1 + (t - n256 k hk 2) = u + t - n256 k hk 1 := by
        rw [n256two]
        abel
      have hidx2 : -(t - n256 k hk 2) = n256 k hk 2 - t := by abel
      rw [hidx, hidx2]
      have h'' := congrArg (fun z : ZMod 2 =>
        z + (M (u + n256 k hk 1) * T (t - n256 k hk 2) + M (u + t) * T (-t))) h
      abel_nf at h'' ⊢
      simp [z2addself, z2twomul] at h''
      simpa [sub_eq_add_neg] using h''
    have hFiter : ∀ n : ℕ, ∀ u t : Fin k,
        F u t = F (u + n • n256 k hk 1) (t - n • n256 k hk 2) := by
      intro n
      induction n with
      | zero => intro u t; simp
      | succ n ih =>
          intro u t
          rw [ih u t]
          have h := hFrec (u + n • n256 k hk 1) (t - n • n256 k hk 2)
          convert h using 1 <;> (simp [succ_nsmul] <;> abel)
    have hFnorm : ∀ u t : Fin k, F u t = F 0 (t + u + u) := by
      intro u t
      let n : ℕ := (-u).val
      have hn1 : n • n256 k hk 1 = -u := by
        rw [nsmul_one_eq k hk]
        ext
        change n % k = (-u).val
        exact Nat.mod_eq_of_lt (Nat.mod_lt _ hk)
      have hn2 : n • n256 k hk 2 = -(u + u) := by
        rw [n256two, nsmul_add, hn1]
        abel
      have h := hFiter n u t
      rw [hn1, hn2] at h
      convert h using 1 <;> abel
    have hF0 : ∀ u : Fin k, F u 0 = 0 := by
      intro u
      simp [F, z2addself]
    have hFnorm_even : ∀ u : Fin k, F 0 (u + u) = 0 := by
      intro u
      have h := hFnorm u 0
      rw [hF0 u] at h
      simpa [add_assoc] using h.symm
    have hFall : ∀ u t : Fin k, F u t = 0 := by
      intro u t
      by_cases hkeven : k % 2 = 0
      · by_cases htodd : t.val % 2 = 0
        · let v : Fin k := n256 k hk (t.val / 2)
          have hv2 : v + v = t := by
            have htwo : (t.val / 2) • n256 k hk 2 = v + v := by
              rw [n256two, nsmul_add, nsmul_one_eq k hk]
            rw [← htwo, nsmul_two_even k hk t htodd]
          have hs : t + u + u = (u + v) + (u + v) := by
            rw [← hv2]
            abel
          have hz := hFnorm_even (u + v)
          rw [← hs] at hz
          have h := hFnorm u t
          rw [hz] at h
          exact h
        · have ht1 : t.val % 2 = 1 := by omega
          have hTt : T t = 0 := tap_odd_zero k T hidemTap hkeven t ht1
          have hneg : ((-t : Fin k).val) % 2 = 1 := neg_val_odd k hkeven t ht1
          have hTneg : T (-t) = 0 := tap_odd_zero k T hidemTap hkeven (-t) hneg
          simp [F, hTt, hTneg]
      · by_cases hk1 : k = 1
        · subst k
          have hu : u = 0 := Subsingleton.elim _ _
          have ht : t = 0 := Subsingleton.elim _ _
          subst u
          subst t
          simp [F, z2addself]
        · have hkgt : 1 < k := by omega
          have hcop2 : Nat.Coprime 2 k := by
            rw [Nat.prime_two.coprime_iff_not_dvd]
            intro hd
            exact hkeven (Nat.mod_eq_zero_of_dvd hd)
          obtain ⟨m, hm_lt, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop2 hkgt
          have hF0all : ∀ s : Fin k, F 0 s = 0 := by
            intro s
            let v : Fin k := n256 k hk (m * s.val)
            have hv2 : v + v = s := by
              have htwo : (m * s.val) • n256 k hk 2 = v + v := by
                rw [n256two, nsmul_add, nsmul_one_eq k hk]
              rw [← htwo, nsmul_two_inv k hk m hm s]
            have hz := hFnorm_even v
            rw [hv2] at hz
            exact hz
          have h := hFnorm u t
          rw [hF0all] at h
          exact h
    intro i t
    apply b256inj
    have hF := hFall i t
    dsimp [F] at hF
    have heqZ : M i * T t = M (i + t) * T (-t) := z2eq_of_add_eq_zero hF
    have hb : b256 (mask i && tap t) =
        b256 (mask (n256 k hk (i.val + t.val)) && tap (n256 k hk (k - t.val))) := by
      simpa [b256and, M, T, n256add, n256ksub] using heqZ
    simpa [n256] using hb
  · intro hcoef
    let pr : (Fin k → Bool) → Fin k → Bool := fun input j =>
      (List.ofFn (fun t : Fin k => tap t && input (n256 k hk (j.val + t.val)))).foldl xor false
    have hpr : ∀ z : Fin k → Bool, pr (pr z) = pr z := by
      intro z
      simpa [pr, n256] using hproj z
    let T : Fin k → ZMod 2 := fun t => b256 (tap t)
    let M : Fin k → ZMod 2 := fun i => b256 (mask i)
    let P : (Fin k → ZMod 2) → Fin k → ZMod 2 := p256 k T
    have hprZ : ∀ (w : Fin k → Bool) (j : Fin k), b256 (pr w j) = P (fun i => b256 (w i)) j := by
      intro w j
      simpa [pr, P, T] using b256proj k hk tap w j
    have hidem : ∀ v : Fin k → ZMod 2, P (P v) = P v := by
      intro v
      ext j
      let z : Fin k → Bool := fun i => u256 (v i)
      have hz : (fun i => b256 (z i)) = v := by
        ext i
        simp [z, b256u]
      have hp := congrArg (fun w : Fin k → Bool => b256 (w j)) (hpr z)
      rw [hprZ (pr z) j, hprZ z j] at hp
      have hf : (fun i => b256 (pr z i)) = P v := by
        ext i
        rw [hprZ z i, hz]
      rw [hf, hz] at hp
      exact hp
    have hcoefZ : ∀ i t : Fin k, M i * T t = M (i + t) * T (-t) := by
      intro i t
      have hb : (mask i && tap t) =
          (mask (n256 k hk (i.val + t.val)) && tap (n256 k hk (k - t.val))) := by
        simpa [n256] using hcoef i t
      have hz := congrArg b256 hb
      simpa [b256and, M, T, n256add, n256ksub] using hz
    let D : Fin k := n256 k hk d
    have hzero : ∀ x y : Fin k → ZMod 2,
        c256 k hk M (m256 k D (P x)) (m256 k D (fun i => y i + P y i)) = 0 := by
      intro x y
      have hy : m256 k D (fun i => y i + P y i) =
          fun i => m256 k D y i + P (m256 k D y) i := by
        rw [m256add]
        rw [show m256 k D (P y) = P (m256 k D y) by simpa [P] using m256p256 k T D y]
      rw [show m256 k D (P x) = P (m256 k D x) by simpa [P] using m256p256 k T D x, hy]
      exact c256proj_vanish k hk M T hcoefZ (by simpa [P] using hidem)
        (m256 k D x) (m256 k D y)
    let B0 : Fin k → ZMod 2 := fun i => b256 (base i)
    let YA : (Fin k → Bool) → Fin k → ZMod 2 := fun a =>
      m256 k D (fun i => B0 i + P (fun q => b256 (a q)) i)
    let YB : (Fin k → Bool) → Fin k → ZMod 2 := fun b =>
      m256 k D (fun i => b256 (b i) + P (fun q => b256 (b q)) i)
    let leftZ : (Fin k → Bool) → ZMod 2 := fun a =>
      lin256 k hk M (YA a) + q256 k hk M (YA a)
    let rightZ : (Fin k → Bool) → ZMod 2 := fun b =>
      lin256 k hk M (YB b) + q256 k hk M (YB b) +
        c256 k hk M (m256 k D B0) (YB b)
    refine ⟨fun a => u256 (leftZ a), fun b => u256 (rightZ b), ?_⟩
    intro a b
    apply b256inj
    rw [b256xor, b256u, b256u]
    let state : Fin k → Bool := fun i => xor (xor (base i) (pr a i)) (xor (b i) (pr b i))
    let yy : Fin k → Bool := fun pos =>
      xor (xor (state pos) (state (n256 k hk (pos.val + d))))
        (state (n256 k hk (pos.val + k - d % k)))
    change b256 ((List.ofFn (fun bit : Fin k => mask bit &&
      xor (yy bit) (!(yy (n256 k hk (bit.val + 1))) &&
        yy (n256 k hk (bit.val + 2))))).foldl xor false) = leftZ a + rightZ b
    rw [b256observed]
    have hyy : (fun i => b256 (yy i)) = m256 k D (fun i => b256 (state i)) := by
      ext i
      simp only [yy]
      rw [show n256 k hk (i.val + k - d % k) = i + -D by simpa [D] using n256third k hk d i]
      simpa [D, n256sub, sub_eq_add_neg] using b256mix k hk d state i
    rw [hyy]
    let A : Fin k → ZMod 2 := fun i => b256 (a i)
    let B : Fin k → ZMod 2 := fun i => b256 (b i)
    have hstate : (fun i => b256 (state i)) =
        fun i => B0 i + P A i + (B i + P B i) := by
      ext i
      simp [state, b256xor, B0, A, B, hprZ a i, hprZ b i]
      abel
    rw [hstate]
    have hsplit : m256 k D (fun i => B0 i + P A i + (B i + P B i)) =
        fun i => YA a i + YB b i := by
      ext i
      simp [m256, YA, YB, A, B, B0]
      abel
    rw [hsplit, lin256add, q256add]
    have hYA : YA a = fun i => m256 k D B0 i + m256 k D (P A) i := by
      ext i
      simp [YA, m256, B0, P, A]
      abel
    have hcross : c256 k hk M (YA a) (YB b) =
        c256 k hk M (m256 k D B0) (YB b) := by
      rw [hYA, c256add_left]
      have hz : c256 k hk M (m256 k D (P A)) (YB b) = 0 := by
        simpa [YB, B] using hzero A B
      rw [hz, add_zero]
    rw [hcross]
    simp [leftZ, rightZ]
    abel
