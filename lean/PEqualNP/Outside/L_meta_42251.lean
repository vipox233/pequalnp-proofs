import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42251

section
variable (k : Nat) (hk : 0 < k)

def ix (n : Nat) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩
def add (u v : Fin k → Bool) : Fin k → Bool := fun i => xor (u i) (v i)
def mix (w : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (w (ix k hk (i.val+k-1))) (xor (w i) (w (ix k hk (i.val+1))))
def rot (x : Fin k → Bool) : Fin k → Bool := fun i => x (ix k hk (i.val+k-1))
def chi (w : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (w i) (!(w (ix k hk (i.val+1))) && w (ix k hk (i.val+2)))
def row (u x : Fin k → Bool) : Fin k → Bool := add k (chi k hk (mix k hk (add k u (rot k hk x)))) x
def vv : Fin k → Bool := fun i => decide (i.val ≠ 1)
def diff (u x : Fin k → Bool) : Fin k → Bool := add k (row k hk u x) (row k hk (add k u (vv k)) x)

def zs (s : Fin k → Bool) (i : Fin k) : Bool :=
  if i.val = 0 ∨ i.val + 1 = k then false
  else if i.val = 1 then xor (s i) (xor (s (ix k hk (i.val+1))) (s (ix k hk (i.val+2))))
  else if i.val + 2 = k then xor (s (ix k hk (i.val+1))) (xor (s (ix k hk (i.val+2))) (s (ix k hk (i.val+3))))
  else xor (xor (s i) (s (ix k hk (i.val+3)))) (decide (i.val = 2))

theorem ix_fin (i : Fin k) : ix k hk i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem ix_mod (a b : Nat) : ix k hk ((ix k hk a).val + b) = ix k hk (a + b) := by
  apply Fin.ext; simp [ix, Nat.add_mod, Nat.mod_mod]

theorem ix_addk (a : Nat) : ix k hk (a + k) = ix k hk a := by
  apply Fin.ext; simp [ix]

theorem ix_ofeq (a b : Nat) (h : a = b) : ix k hk a = ix k hk b := by rw [h]

theorem mix_ix (w : Fin k → Bool) (n : Nat) : mix k hk w (ix k hk n) =
    xor (w (ix k hk (n+k-1))) (xor (w (ix k hk n)) (w (ix k hk (n+1)))) := by
  simp only [mix]
  rw [show (ix k hk n).val + k - 1 = (ix k hk n).val + (k-1) by omega, ix_mod, ix_mod,
    show n + (k-1) = n + k - 1 by omega]

theorem ix_s1 (i : Fin k) : ix k hk (i.val+1+k-1) = i := by
  rw [ix_ofeq k hk _ (i.val + k) (by omega), ix_addk, ix_fin]

theorem ix_s2 (i : Fin k) : ix k hk (i.val+2+k-1) = ix k hk (i.val+1) := by
  rw [ix_ofeq k hk _ (i.val + 1 + k) (by omega), ix_addk]

theorem mod_lt' (n : Nat) (h : n < k) : n % k = n := Nat.mod_eq_of_lt h
theorem mod_ge' (n : Nat) (h1 : k ≤ n) (h2 : n < k + k) : n % k = n - k := by
  rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]

theorem vv_ix (n : Nat) : vv k (ix k hk n) = decide (n % k ≠ 1) := rfl

theorem zform (h6 : 6 ≤ k) (s : Fin k → Bool) (i : Fin k) :
    xor (xor (chi k hk (mix k hk s) i) (chi k hk (mix k hk (add k s (vv k))) i)) (decide (i.val ≠ 0))
      = zs k hk s i := by
  have hi := i.isLt
  simp only [chi, mix_ix, ix_s1, ix_s2]
  simp only [mix, add, zs]
  simp only [vv_ix]
  have e0 : vv k i = decide (i.val ≠ 1) := rfl
  rw [e0]
  generalize s (ix k hk (i.val + k - 1)) = a0
  generalize s i = a1
  generalize s (ix k hk (i.val + 1)) = a2
  generalize s (ix k hk (i.val + 2)) = a3
  generalize s (ix k hk (i.val + 3)) = a4
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h <;>
  simp (disch := omega) only [mod_lt', mod_ge', decide_eq_true, decide_eq_false] <;>
  simp (disch := omega) only [if_pos, if_neg, decide_eq_true, decide_eq_false] <;>
  revert a0 a1 a2 a3 a4 <;> decide


def kap (a b : Bool) (c : Nat) : Bool := if c = 0 then a else if c = 1 then b else xor a b
def tau (e a b : Bool) : Fin k → Bool := fun i => xor (kap a b (i.val % 3)) (e && decide (i.val ≠ 0))
def sig (e a b : Bool) : Fin k → Bool := fun i => if i.val = 1 then a else xor (kap a b ((i.val + 2) % 3)) e
def dd : Fin k → Bool := fun i => decide (3 ≤ i.val)

theorem rot_tau (h6 : 6 ≤ k) (h3 : k % 3 = 0) (e a b : Bool) : rot k hk (tau k e a b) = sig k e a b := by
  funext i
  have hi := i.isLt
  simp only [rot, tau, sig, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ 2 ≤ i.val by omega) with h | h | h <;>
  rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with h' | h' | h' <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', kap, if_pos, if_neg, decide_eq_true, decide_eq_false] <;>
  revert e a b <;> decide

theorem zs_add_sig (h6 : 6 ≤ k) (h3 : k % 3 = 0) (s : Fin k → Bool) (e a b : Bool) :
    zs k hk (add k s (sig k e a b)) = zs k hk s := by
  funext i
  have hi := i.isLt
  simp only [zs, add, sig, ix]
  generalize s i = a1
  generalize s ⟨(i.val + 1) % k, _⟩ = a2
  generalize s ⟨(i.val + 2) % k, _⟩ = a3
  generalize s ⟨(i.val + 3) % k, _⟩ = a4
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h <;>
  rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with h' | h' | h' <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', kap, if_pos, if_neg, decide_eq_true, decide_eq_false] <;>
  revert e a b a1 a2 a3 a4 <;> decide

theorem mix_sig (h6 : 6 ≤ k) (h3 : k % 3 = 0) (e a b : Bool) :
    mix k hk (sig k e a b) = fun i => e && dd k i := by
  funext i
  have hi := i.isLt
  simp only [mix, sig, dd, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 1 < k) ∨ i.val + 1 = k by omega)
    with h | h | h | h | h <;>
  rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with h' | h' | h' <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', kap, if_pos, if_neg, decide_eq_true, decide_eq_false] <;>
  revert e a b <;> decide

theorem mix_vv (h6 : 6 ≤ k) : mix k hk (vv k) = dd k := by
  funext i
  have hi := i.isLt
  simp only [mix, vv, dd, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 1 < k) ∨ i.val + 1 = k by omega)
    with h | h | h | h | h <;>
  simp (disch := omega) only [mod_lt', mod_ge', decide_eq_true, decide_eq_false] <;> decide

theorem mix_add (a b : Fin k → Bool) : mix k hk (add k a b) = add k (mix k hk a) (mix k hk b) := by
  funext i; simp only [mix, add]; revert a b
  intro a b
  generalize a (ix k hk (i.val + k - 1)) = x1
  generalize a i = x2
  generalize a (ix k hk (i.val + 1)) = x3
  generalize b (ix k hk (i.val + k - 1)) = y1
  generalize b i = y2
  generalize b (ix k hk (i.val + 1)) = y3
  revert x1 x2 x3 y1 y2 y3; decide

theorem rot_add (a b : Fin k → Bool) : rot k hk (add k a b) = add k (rot k hk a) (rot k hk b) := rfl


theorem ix_val' (n : Nat) (h : n < k) : (ix k hk n).val = n := Nat.mod_eq_of_lt h

theorem zs_mid (s : Fin k → Bool) (n : Nat) (h2 : 2 ≤ n) (h3 : n + 3 ≤ k) :
    zs k hk s (ix k hk n) = xor (xor (s (ix k hk n)) (s (ix k hk (n+3)))) (decide (n = 2)) := by
  have hv := ix_val' k hk n (by omega)
  simp only [zs, hv]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem zs_one (h6 : 6 ≤ k) (s : Fin k → Bool) :
    zs k hk s (ix k hk 1) = xor (s (ix k hk 1)) (xor (s (ix k hk 2)) (s (ix k hk 3))) := by
  have hv := ix_val' k hk 1 (by omega)
  simp only [zs, hv]
  rw [if_neg (by omega), if_pos trivial]

theorem zs_km2 (h6 : 6 ≤ k) (s : Fin k → Bool) :
    zs k hk s (ix k hk (k-2)) = xor (s (ix k hk (k-1))) (xor (s (ix k hk 0)) (s (ix k hk 1))) := by
  have hv := ix_val' k hk (k-2) (by omega)
  simp only [zs, hv]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
    ix_ofeq k hk (k-2+1) (k-1) (by omega), ix_ofeq k hk (k-2+2) (0+k) (by omega),
    ix_ofeq k hk (k-2+3) (1+k) (by omega), ix_addk, ix_addk]

theorem zs_zero (s : Fin k → Bool) : zs k hk s (ix k hk 0) = false := by
  simp [zs, ix]

theorem zs_km1 (s : Fin k → Bool) : zs k hk s (ix k hk (k-1)) = false := by
  have hv := ix_val' k hk (k-1) (by omega)
  simp only [zs, hv]
  rw [if_pos (by omega)]

theorem zs_fib (h6 : 6 ≤ k) (h3 : k % 3 = 0) (s s' : Fin k → Bool) (h : zs k hk s = zs k hk s') :
    ∃ e a b, s' = add k s (sig k e a b) := by
  have hc : ∀ n, 2 ≤ n → n + 3 ≤ k → add k s s' (ix k hk n) = add k s s' (ix k hk (n+3)) := by
    intro n h2 h3'
    have := congrFun h (ix k hk n)
    rw [zs_mid k hk s n h2 h3', zs_mid k hk s' n h2 h3'] at this
    simp only [add]
    revert this
    generalize s (ix k hk n) = x1
    generalize s (ix k hk (n+3)) = x2
    generalize s' (ix k hk n) = y1
    generalize s' (ix k hk (n+3)) = y2
    generalize decide (n = 2) = t
    revert x1 x2 y1 y2 t; decide
  have h1 : add k s s' (ix k hk 1) = xor (add k s s' (ix k hk 2)) (add k s s' (ix k hk 3)) := by
    have := congrFun h (ix k hk 1)
    rw [zs_one k hk h6 s, zs_one k hk h6 s'] at this
    simp only [add]
    revert this
    generalize s (ix k hk 1) = x1
    generalize s (ix k hk 2) = x2
    generalize s (ix k hk 3) = x3
    generalize s' (ix k hk 1) = y1
    generalize s' (ix k hk 2) = y2
    generalize s' (ix k hk 3) = y3
    revert x1 x2 x3 y1 y2 y3; decide
  have chain : ∀ c, 2 ≤ c → ∀ m, c + 3*m < k → add k s s' (ix k hk (c + 3*m)) = add k s s' (ix k hk c) := by
    intro c hc2 m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [← ih (by omega), hc (c + 3*m) (by omega) (by omega)]
      congr 2
  have h0 : add k s s' (ix k hk 0) = add k s s' (ix k hk 3) := by
    have e1 := hc (k-3) (by omega) (by omega)
    rw [ix_ofeq k hk (k-3+3) (0+k) (by omega), ix_addk] at e1
    rw [← e1, ix_ofeq k hk (k-3) (3 + 3*((k-6)/3)) (by omega)]
    exact chain 3 (by omega) _ (by omega)
  refine ⟨xor (add k s s' (ix k hk 4)) (xor (add k s s' (ix k hk 3)) (add k s s' (ix k hk 2))),
    xor (add k s s' (ix k hk 3)) (add k s s' (ix k hk 2)),
    xor (add k s s' (ix k hk 2)) (xor (add k s s' (ix k hk 4)) (xor (add k s s' (ix k hk 3)) (add k s s' (ix k hk 2)))), ?_⟩
  funext i
  have key : add k s s' i = sig k (xor (add k s s' (ix k hk 4)) (xor (add k s s' (ix k hk 3)) (add k s s' (ix k hk 2))))
    (xor (add k s s' (ix k hk 3)) (add k s s' (ix k hk 2)))
    (xor (add k s s' (ix k hk 2)) (xor (add k s s' (ix k hk 4)) (xor (add k s s' (ix k hk 3)) (add k s s' (ix k hk 2))))) i := by
    have hi := i.isLt
    rw [← ix_fin k hk i]
    have hv := ix_val' k hk i.val hi
    simp only [sig, hv]
    rcases (show i.val = 0 ∨ i.val = 1 ∨ (2 ≤ i.val ∧ i.val % 3 = 0) ∨ (2 ≤ i.val ∧ i.val % 3 = 1) ∨
        (2 ≤ i.val ∧ i.val % 3 = 2) by omega) with h | h | h | h | h
    · rw [ix_ofeq k hk _ 0 h, h0]
      generalize add k s s' (ix k hk 2) = A; generalize add k s s' (ix k hk 3) = B
      generalize add k s s' (ix k hk 4) = C
      simp only [kap, h]; revert A B C; decide
    · rw [ix_ofeq k hk _ 1 h, h1]
      generalize add k s s' (ix k hk 2) = A; generalize add k s s' (ix k hk 3) = B
      generalize add k s s' (ix k hk 4) = C
      simp only [kap, h]; revert A B C; decide
    · rw [ix_ofeq k hk _ (3 + 3*((i.val-3)/3)) (by omega), chain 3 (by omega) _ (by omega)]
      generalize add k s s' (ix k hk 2) = A; generalize add k s s' (ix k hk 3) = B
      generalize add k s s' (ix k hk 4) = C
      simp (disch := omega) only [kap, if_pos, if_neg]; revert A B C; decide
    · rw [ix_ofeq k hk _ (4 + 3*((i.val-4)/3)) (by omega), chain 4 (by omega) _ (by omega)]
      generalize add k s s' (ix k hk 2) = A; generalize add k s s' (ix k hk 3) = B
      generalize add k s s' (ix k hk 4) = C
      simp (disch := omega) only [kap, if_pos, if_neg]; revert A B C; decide
    · rw [ix_ofeq k hk _ (2 + 3*((i.val-2)/3)) (by omega), chain 2 (by omega) _ (by omega)]
      generalize add k s s' (ix k hk 2) = A; generalize add k s s' (ix k hk 3) = B
      generalize add k s s' (ix k hk 4) = C
      simp (disch := omega) only [kap, if_pos, if_neg]; revert A B C; decide
  have : s' i = xor (s i) (add k s s' i) := by simp only [add]; cases s i <;> cases s' i <;> rfl
  rw [this, key]; rfl


def sx (u x : Fin k → Bool) : Fin k → Bool := add k u (rot k hk x)
def zD (D : Fin k → Bool) : Fin k → Bool := fun i => xor (D i) (decide (i.val ≠ 0))

theorem diff_eq (u x : Fin k → Bool) (i : Fin k) : diff k hk u x i =
    xor (chi k hk (mix k hk (sx k hk u x)) i) (chi k hk (mix k hk (add k (sx k hk u x) (vv k))) i) := by
  have e1 : add k (add k u (vv k)) (rot k hk x) = add k (sx k hk u x) (vv k) := by
    funext j; simp only [add, sx]
    cases u j <;> cases vv k j <;> cases rot k hk x j <;> rfl
  simp only [diff, row]
  rw [e1]
  simp only [add, sx]
  generalize chi k hk (mix k hk (add k u (rot k hk x))) i = A
  generalize chi k hk (mix k hk (add k (add k u (rot k hk x)) (vv k))) i = B
  cases A <;> cases B <;> cases x i <;> rfl

theorem zD_diff (h6 : 6 ≤ k) (u x : Fin k → Bool) : zD k (diff k hk u x) = zs k hk (sx k hk u x) := by
  funext i; simp only [zD]; rw [diff_eq]; exact zform k hk h6 _ i

theorem diff_iff (h6 : 6 ≤ k) (u x x' : Fin k → Bool) :
    diff k hk u x = diff k hk u x' ↔ zs k hk (sx k hk u x) = zs k hk (sx k hk u x') := by
  rw [← zD_diff k hk h6, ← zD_diff k hk h6]
  constructor
  · intro h; rw [h]
  · intro h; funext i
    have := congrFun h i
    simp only [zD] at this
    revert this; cases diff k hk u x i <;> cases diff k hk u x' i <;> simp

theorem sx_tau (h6 : 6 ≤ k) (h3 : k % 3 = 0) (u x : Fin k → Bool) (e a b : Bool) :
    sx k hk u (add k x (tau k e a b)) = add k (sx k hk u x) (sig k e a b) := by
  simp only [sx]; rw [rot_add, rot_tau k hk h6 h3]
  funext i; simp only [add]
  cases u i <;> cases rot k hk x i <;> cases sig k e a b i <;> rfl

theorem diff_tau (h6 : 6 ≤ k) (h3 : k % 3 = 0) (u x : Fin k → Bool) (e a b : Bool) :
    diff k hk u (add k x (tau k e a b)) = diff k hk u x := by
  rw [diff_iff k hk h6, sx_tau k hk h6 h3, zs_add_sig k hk h6 h3]

theorem rot_inj (y y' : Fin k → Bool) (h : rot k hk y = rot k hk y') : y = y' := by
  funext j
  have := congrFun h (ix k hk (j.val + 1))
  simp only [rot] at this
  rw [show (ix k hk (j.val + 1)).val + k - 1 = (ix k hk (j.val + 1)).val + (k-1) by omega, ix_mod,
    show j.val + 1 + (k-1) = j.val + 1 + k - 1 by omega, ix_s1] at this
  exact this

theorem fiber (h6 : 6 ≤ k) (h3 : k % 3 = 0) (u x x' : Fin k → Bool) (h : diff k hk u x' = diff k hk u x) :
    ∃ e a b, x' = add k x (tau k e a b) := by
  rw [diff_iff k hk h6] at h
  obtain ⟨e, a, b, hs⟩ := zs_fib k hk h6 h3 _ _ h.symm
  refine ⟨e, a, b, ?_⟩
  rw [← sx_tau k hk h6 h3] at hs
  apply rot_inj k hk
  funext i
  have := congrFun hs i
  simp only [sx, add] at this
  revert this; cases u i <;> cases rot k hk x' i <;> cases rot k hk (fun i => x i ^^ tau k e a b i) i <;> simp

theorem row_tau (h6 : 6 ≤ k) (h3 : k % 3 = 0) (u x : Fin k → Bool) (e a b : Bool) (i : Fin k) :
    row k hk u (add k x (tau k e a b)) i = xor (xor (row k hk u x i) (e && diff k hk u x i)) (tau k e a b i) := by
  have hm : mix k hk (sx k hk u (add k x (tau k e a b))) =
      cond e (mix k hk (add k (sx k hk u x) (vv k))) (mix k hk (sx k hk u x)) := by
    rw [sx_tau k hk h6 h3, mix_add, mix_sig k hk h6 h3]
    cases e
    · funext j; simp [add]
    · rw [mix_add, mix_vv k hk h6]; funext j; simp [add]
  have hr : row k hk u (add k x (tau k e a b)) i =
      xor (chi k hk (mix k hk (sx k hk u (add k x (tau k e a b)))) i) (add k x (tau k e a b) i) := rfl
  have hr0 : row k hk u x i = xor (chi k hk (mix k hk (sx k hk u x)) i) (x i) := rfl
  rw [hr, hr0, hm, diff_eq]
  cases e
  · simp only [cond, add]; cases chi k hk (mix k hk (sx k hk u x)) i <;> cases x i <;> cases tau k false a b i <;> rfl
  · simp only [cond, add]
    cases chi k hk (mix k hk (sx k hk u x)) i <;> cases chi k hk (mix k hk (add k (sx k hk u x) (vv k))) i <;>
      cases x i <;> cases tau k true a b i <;> rfl

theorem tau_zero (h6 : 6 ≤ k) (x : Fin k → Bool) (e a b : Bool) (h : add k x (tau k e a b) = x) :
    e = false ∧ a = false ∧ b = false := by
  have h1 := congrFun h ⟨1, by omega⟩
  have h2 := congrFun h ⟨2, by omega⟩
  have h3 := congrFun h ⟨3, by omega⟩
  simp only [add, tau, kap, Fin.val_mk] at h1 h2 h3
  clear h
  revert h1 h2 h3
  cases x ⟨1, by omega⟩ <;> cases x ⟨2, by omega⟩ <;> cases x ⟨3, by omega⟩ <;> cases e <;> cases a <;> cases b <;> simp

abbrev wk (c0 c1 c2 : Nat) (z0 z1 z2 : Bool) : Prop :=
  ∀ e a b : Bool, xor (e && z0) (kap a b c0) = false → xor (e && z1) (kap a b c1) = false →
    xor (e && z2) (kap a b c2) = false → e = false ∧ a = false ∧ b = false

def Gb (c0 c1 c2 : Nat) (z0 z1 z2 : Bool) : Bool :=
  if c0 ≠ c1 ∧ c0 ≠ c2 ∧ c1 ≠ c2 then xor z0 (xor z1 z2) else if c0 = c1 then xor z0 z1
  else if c0 = c2 then xor z0 z2 else xor z1 z2

theorem fin_low : ∀ c0 c1 c2 : Fin 3, ∀ z0 z1 z2 : Bool,
    Gb c0.val c1.val c2.val z0 z1 z2 = false → ¬ wk c0.val c1.val c2.val z0 z1 z2 := by decide

theorem fin_up3 : ∀ z0 z1 z2 : Bool, xor z0 (xor z1 z2) = true → ∀ c0 c1 c2 : Fin 3,
    c0 ≠ c1 → c0 ≠ c2 → c1 ≠ c2 → wk c0.val c1.val c2.val z0 z1 z2 := by decide

theorem fin_up2 : ∀ z0 z1 z2 : Bool, xor z0 z2 = true → ∀ c0 c1 c2 : Fin 3,
    c0 = c2 → c0 ≠ c1 → wk c0.val c1.val c2.val z0 z1 z2 := by decide

theorem read_tau (h6 : 6 ≤ k) (h3 : k % 3 = 0) (u x : Fin k → Bool) (e a b : Bool) (p : Fin k) :
    (row k hk u (add k x (tau k e a b)) p = row k hk u x p) ↔
      xor (e && zD k (diff k hk u x) p) (kap a b (p.val % 3)) = false := by
  rw [row_tau k hk h6 h3]
  simp only [tau, zD]
  cases row k hk u x p <;> cases diff k hk u x p <;> cases kap a b (p.val % 3) <;>
    cases decide (p.val ≠ 0) <;> cases e <;> decide


def off (t : Nat) : Nat := if t = 0 then 0 else if t = 1 then 1 else 3

def pN (r : Nat) (m : Nat) (t : Nat) : Nat :=
  if m = 0 then r % 2 + t
  else if m = 1 then k - 3 - r % 2 + t
  else if m < r / 2 + 1 then 6*(m-2) + 3 + 3*(r % 2) + off t
  else 6*(m - r/2 - 1) + 5 + off t

def testm (r : Nat) (z : Fin k → Bool) (m : Nat) : Bool :=
  xor (z (ix k hk (pN k r m 0))) (xor (if m ≤ 1 then z (ix k hk (pN k r m 1)) else false) (z (ix k hk (pN k r m 2))))

theorem pN_A (r t : Nat) : pN k r 0 t = r % 2 + t := by simp [pN]
theorem pN_B (r t : Nat) : pN k r 1 t = k - 3 - r % 2 + t := by simp [pN]
theorem pN_P0 (r j t : Nat) (hj : j + 1 < r / 2) : pN k r (j+2) t = 6*j + 3 + 3*(r % 2) + off t := by
  unfold pN; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; congr 3
theorem pN_P2 (r j t : Nat) (hj : j + 1 < r / 2) : pN k r (j + r/2 + 1) t = 6*j + 5 + off t := by
  unfold pN; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [show j + r / 2 + 1 - r / 2 - 1 = j by omega]
theorem testm_ge2 (r : Nat) (z : Fin k → Bool) (m : Nat) (hm : 2 ≤ m) :
    testm k hk r z m = xor (z (ix k hk (pN k r m 0))) (z (ix k hk (pN k r m 2))) := by
  simp only [testm]; rw [if_neg (by omega)]; simp
theorem testm_le1 (r : Nat) (z : Fin k → Bool) (m : Nat) (hm : m ≤ 1) :
    testm k hk r z m = xor (z (ix k hk (pN k r m 0))) (xor (z (ix k hk (pN k r m 1))) (z (ix k hk (pN k r m 2)))) := by
  simp only [testm]; rw [if_pos hm]
theorem off0 : off 0 = 0 := rfl
theorem off1 : off 1 = 1 := rfl
theorem off2 : off 2 = 3 := rfl

theorem chain_gen (s : Fin k → Bool) (c L : Nat) (hc : 3 ≤ c)
    (hstep : ∀ j, j < L → s (ix k hk (c + 6*j)) = s (ix k hk (c + 6*j + 6))) :
    ∀ j, j ≤ L → s (ix k hk (c + 6*j)) = s (ix k hk c) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [← ih (by omega), hstep j (by omega)]
    congr 2

theorem exists_test (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (s : Fin k → Bool) :
    ∃ m, m < 2*(r/2) ∧ testm k hk r (zs k hk s) m = true := by
  have h6 : 6 ≤ k := by omega
  by_contra hne
  push_neg at hne
  have hf : ∀ m, m < 2*(r/2) → testm k hk r (zs k hk s) m = false := by
    intro m hm; have := hne m hm; revert this; cases testm k hk r (zs k hk s) m <;> simp
  have pair_step : ∀ n, 3 ≤ n → n + 6 ≤ k → xor (zs k hk s (ix k hk n)) (zs k hk s (ix k hk (n+3))) = false →
      s (ix k hk n) = s (ix k hk (n + 6)) := by
    intro n hn hn6 h
    rw [zs_mid k hk s n (by omega) (by omega), zs_mid k hk s (n+3) (by omega) (by omega),
      decide_eq_false (by omega), decide_eq_false (by omega)] at h
    rw [show n + 3 + 3 = n + 6 by omega] at h
    revert h
    cases s (ix k hk n) <;> cases s (ix k hk (n+3)) <;> cases s (ix k hk (n+6)) <;> simp
  have c0 := chain_gen k hk s (3 + 3*(r % 2)) (r/2 - 1) (by omega) (by
    intro j hj
    have := hf (j+2) (by omega)
    rw [testm_ge2 k hk r _ _ (by omega), pN_P0 k r j 0 (by omega), pN_P0 k r j 2 (by omega), off0, off2] at this
    have e := pair_step (6 * j + 3 + 3 * (r % 2) + 0) (by omega) (by omega) this
    rw [show 6 * j + 3 + 3 * (r % 2) + 0 = 3 + 3 * (r % 2) + 6 * j by omega] at e
    exact e) (r/2 - 1) le_rfl
  have c2 := chain_gen k hk s 5 (r/2 - 1) (by omega) (by
    intro j hj
    have := hf (j + r/2 + 1) (by omega)
    rw [testm_ge2 k hk r _ _ (by omega), pN_P2 k r j 0 (by omega), pN_P2 k r j 2 (by omega), off0, off2] at this
    have e := pair_step (6 * j + 5 + 0) (by omega) (by omega) this
    rw [show 6 * j + 5 + 0 = 5 + 6 * j by omega] at e
    exact e) (r/2 - 1) le_rfl
  have hA := hf 0 (by omega)
  have hB := hf 1 (by omega)
  rw [testm_le1 k hk r _ _ (by omega), pN_A, pN_A, pN_A] at hA
  rw [testm_le1 k hk r _ _ (by omega), pN_B, pN_B, pN_B] at hB
  have ek : ix k hk (k - 3 + 3) = ix k hk 0 := by rw [ix_ofeq k hk _ (0 + k) (by omega), ix_addk]
  rcases Nat.mod_two_eq_zero_or_one r with ho | ho
  · rw [ho] at hA hB c0
    simp only [Nat.add_zero, Nat.zero_add, Nat.sub_zero] at hA hB c0
    rw [ix_ofeq k hk (3 + 3*0 + 6*(r/2-1)) (k-3) (by omega)] at c0
    rw [ix_ofeq k hk (5 + 6*(r/2-1)) (k-1) (by omega)] at c2
    rw [zs_zero, zs_one k hk h6, zs_mid k hk s 2 (by omega) (by omega)] at hA
    rw [zs_mid k hk s (k-3) (by omega) (by omega), ix_ofeq k hk (k - 3 + 1) (k-2) (by omega),
      ix_ofeq k hk (k - 3 + 2) (k-1) (by omega), zs_km2 k hk h6, zs_km1, ek] at hB
    rw [decide_eq_false (by omega)] at hB
    rw [c0, c2] at hB
    simp only [show (0:Nat) + 1 = 1 from rfl, show (0:Nat)+2 = 2 from rfl, show (2:Nat) + 3 = 5 from rfl,
      decide_true] at hA
    revert hA hB
    cases s (ix k hk 0) <;> cases s (ix k hk 1) <;> cases s (ix k hk 2) <;> cases s (ix k hk 3) <;>
      cases s (ix k hk 5) <;> simp
  · rw [ho] at hA hB c0
    rw [ix_ofeq k hk (3 + 3*1 + 6*(r/2-1)) (k-3) (by omega)] at c0
    rw [ix_ofeq k hk (5 + 6*(r/2-1)) (k-4) (by omega)] at c2
    rw [ix_ofeq k hk (1+0) 1 (by omega), ix_ofeq k hk (1+1) 2 (by omega), ix_ofeq k hk (1+2) 3 (by omega),
      zs_one k hk h6, zs_mid k hk s 2 (by omega) (by omega), zs_mid k hk s 3 (by omega) (by omega)] at hA
    rw [ix_ofeq k hk (k-3-1+0) (k-4) (by omega), ix_ofeq k hk (k-3-1+1) (k-3) (by omega),
      ix_ofeq k hk (k-3-1+2) (k-2) (by omega),
      zs_mid k hk s (k-4) (by omega) (by omega), zs_mid k hk s (k-3) (by omega) (by omega),
      ix_ofeq k hk (k - 4 + 3) (k-1) (by omega), zs_km2 k hk h6, ek] at hB
    rw [decide_eq_false (by omega), decide_eq_false (by omega)] at hB
    rw [c0, c2] at hB
    simp only [show (2:Nat) + 3 = 5 from rfl, show (3:Nat) + 3 = 6 from rfl, decide_true] at hA
    rw [decide_eq_false (by omega)] at hA
    revert hA hB
    cases s (ix k hk 0) <;> cases s (ix k hk 1) <;> cases s (ix k hk 2) <;> cases s (ix k hk 3) <;>
      cases s (ix k hk 5) <;> cases s (ix k hk 6) <;> cases s (ix k hk (k-1)) <;> simp


theorem panel_facts (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (m : Nat) (hm : m < 2*(r/2)) :
    (m ≤ 1 ∧ ∃ c, (∀ t, pN k r m t = c + t) ∧ c + 2 < k) ∨
    (2 ≤ m ∧ ∃ c, (∀ t, pN k r m t = c + off t) ∧ c + 3 < k) := by
  rcases (show m = 0 ∨ m = 1 ∨ (2 ≤ m ∧ m < r/2 + 1) ∨ r/2 + 1 ≤ m by omega) with h | h | h | h
  · left; exact ⟨by omega, r % 2, fun t => by rw [h, pN_A], by omega⟩
  · left; exact ⟨by omega, k - 3 - r % 2, fun t => by rw [h, pN_B], by omega⟩
  · right; refine ⟨h.1, 6*(m-2) + 3 + 3*(r % 2), fun t => ?_, by omega⟩
    have := pN_P0 k r (m-2) t (by omega); rw [show m - 2 + 2 = m by omega] at this; exact this
  · right; refine ⟨by omega, 6*(m - r/2 - 1) + 5, fun t => ?_, by omega⟩
    have := pN_P2 k r (m - r/2 - 1) t (by omega); rw [show m - r / 2 - 1 + r / 2 + 1 = m by omega] at this
    exact this

theorem upper (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (u : Fin k → Bool) (q : Nat) (hq : 2*(r/2) ≤ q) :
    ∃ (panel : Fin q → Fin 3 → Fin k) (pick : (Fin k → Bool) → Fin q),
      Function.Injective (fun x : Fin k → Bool =>
        (diff k hk u x, fun j : Fin 3 => row k hk u x (panel (pick (diff k hk u x)) j))) := by
  classical
  have h6 : 6 ≤ k := by omega
  have h3 : k % 3 = 0 := by omega
  have hq0 : 0 < q := by omega
  let panel : Fin q → Fin 3 → Fin k := fun m t => ix k hk (pN k r m.val t.val)
  let good : (Fin k → Bool) → Fin q → Prop := fun D m =>
    wk ((panel m 0).val % 3) ((panel m 1).val % 3) ((panel m 2).val % 3)
      (zD k D (panel m 0)) (zD k D (panel m 1)) (zD k D (panel m 2))
  let pick : (Fin k → Bool) → Fin q := fun D => if h : ∃ m, good D m then Classical.choose h else ⟨0, hq0⟩
  refine ⟨panel, pick, ?_⟩
  intro x1 x2 heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hD, hR⟩ := heq
  obtain ⟨e, a, b, hx2⟩ := fiber k hk h6 h3 u x1 x2 hD.symm
  have hex : ∃ m, good (diff k hk u x1) m := by
    obtain ⟨m, hm, ht⟩ := exists_test k hk r h2 hkr (sx k hk u x1)
    refine ⟨⟨m, by omega⟩, ?_⟩
    rw [← zD_diff k hk h6] at ht
    show wk ((ix k hk (pN k r m 0)).val % 3) ((ix k hk (pN k r m 1)).val % 3) ((ix k hk (pN k r m 2)).val % 3)
      (zD k (diff k hk u x1) (ix k hk (pN k r m 0))) (zD k (diff k hk u x1) (ix k hk (pN k r m 1)))
      (zD k (diff k hk u x1) (ix k hk (pN k r m 2)))
    rcases panel_facts k r h2 hkr m hm with ⟨hm1, c, hc, hck⟩ | ⟨hm2, c, hc, hck⟩
    · rw [testm_le1 k hk r _ _ hm1] at ht
      simp only [hc] at ht ⊢
      rw [ix_val' k hk _ (by omega), ix_val' k hk _ (by omega), ix_val' k hk _ (by omega)]
      exact fin_up3 _ _ _ ht ⟨(c + 0) % 3, Nat.mod_lt _ (by omega)⟩ ⟨(c + 1) % 3, Nat.mod_lt _ (by omega)⟩
        ⟨(c + 2) % 3, Nat.mod_lt _ (by omega)⟩ (by simp only [ne_eq, Fin.mk.injEq]; omega)
        (by simp only [ne_eq, Fin.mk.injEq]; omega) (by simp only [ne_eq, Fin.mk.injEq]; omega)
    · rw [testm_ge2 k hk r _ _ hm2] at ht
      simp only [hc, off0, off1, off2] at ht ⊢
      rw [ix_val' k hk _ (by omega), ix_val' k hk _ (by omega), ix_val' k hk _ (by omega)]
      exact fin_up2 _ _ _ ht ⟨(c + 0) % 3, Nat.mod_lt _ (by omega)⟩ ⟨(c + 1) % 3, Nat.mod_lt _ (by omega)⟩
        ⟨(c + 3) % 3, Nat.mod_lt _ (by omega)⟩ (by simp only [Fin.mk.injEq]; omega)
        (by simp only [ne_eq, Fin.mk.injEq]; omega)
  have hp : pick (diff k hk u x1) = Classical.choose hex := dif_pos hex
  have hgood := Classical.choose_spec hex
  rw [← hD, hp] at hR
  have r0 := congrFun hR 0
  have r1 := congrFun hR 1
  have r2 := congrFun hR 2
  rw [hx2] at r0 r1 r2
  rw [eq_comm, read_tau k hk h6 h3] at r0 r1 r2
  obtain ⟨he, ha, hb⟩ := hgood e a b r0 r1 r2
  rw [hx2, he, ha, hb]
  funext i; simp [add, tau, kap]


theorem z2c : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem sep {X ι : Type} [DecidableEq ι] (op : X → X → X) (g : ι → X → ZMod 2)
    (hg : ∀ j a b, g j (op a b) = g j a + g j b) (J : Finset ι) :
    ∀ h : X → ZMod 2, (∀ a b, h (op a b) = h a + h b) →
      (∃ x, (∀ j ∈ J, g j x = 0) ∧ h x = 1) ∨ (∃ S ⊆ J, ∀ x, h x = ∑ j ∈ S, g j x) := by
  induction J using Finset.induction_on with
  | empty =>
    intro h _
    by_cases hx : ∃ x, h x = 1
    · left; obtain ⟨x, hx⟩ := hx; exact ⟨x, by simp, hx⟩
    · right; refine ⟨∅, by simp, fun x => ?_⟩
      push_neg at hx
      rcases z2c (h x) with h0 | h0
      · simp [h0]
      · exact absurd h0 (hx x)
  | insert f J hf ih =>
    intro h hh
    rcases ih h hh with ⟨x1, hx1, h1⟩ | ⟨S, hS, hSx⟩
    · rcases ih (fun x => h x + g f x) (by intro a b; rw [hh, hg]; ring) with ⟨x2, hx2, h2⟩ | ⟨S', hS', hS'x⟩
      · rcases z2c (g f x1) with a1 | a1
        · left; refine ⟨x1, ?_, h1⟩
          intro j hj; rcases Finset.mem_insert.mp hj with rfl | hj
          · exact a1
          · exact hx1 j hj
        rcases z2c (g f x2) with a2 | a2
        · left; refine ⟨x2, ?_, by rw [a2, add_zero] at h2; exact h2⟩
          intro j hj; rcases Finset.mem_insert.mp hj with rfl | hj
          · exact a2
          · exact hx2 j hj
        left; refine ⟨op x1 x2, ?_, ?_⟩
        · intro j hj; rcases Finset.mem_insert.mp hj with rfl | hj
          · rw [hg, a1, a2]; decide
          · rw [hg, hx1 j hj, hx2 j hj]; simp
        · rw [hh, h1]; rw [a2] at h2
          rcases z2c (h x2) with b | b <;> rw [b] at h2 ⊢ <;> revert h2 <;> decide
      · right; refine ⟨insert f S', ?_, fun x => ?_⟩
        · intro j hj; rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (hS' hj)
        · have hfS : f ∉ S' := fun hm => hf (hS' hm)
          rw [Finset.sum_insert hfS, ← hS'x x]
          rcases z2c (g f x) with b | b <;> rw [b] <;> rcases z2c (h x) with c | c <;> rw [c] <;> decide
    · right; exact ⟨S, fun j hj => Finset.mem_insert_of_mem (hS hj), hSx⟩

def B2 (b : Bool) : ZMod 2 := if b then 1 else 0
theorem B2_xor (a b : Bool) : B2 (xor a b) = B2 a + B2 b := by cases a <;> cases b <;> decide

def ind (p i : Fin k) : ZMod 2 := if i = p then 1 else 0

def lamv (P : Fin 3 → Fin k) (i : Fin k) : ZMod 2 :=
  if (P 0).val % 3 ≠ (P 1).val % 3 ∧ (P 0).val % 3 ≠ (P 2).val % 3 ∧ (P 1).val % 3 ≠ (P 2).val % 3 then
    ind k (P 0) i + ind k (P 1) i + ind k (P 2) i
  else if (P 0).val % 3 = (P 1).val % 3 then ind k (P 0) i + ind k (P 1) i
  else if (P 0).val % 3 = (P 2).val % 3 then ind k (P 0) i + ind k (P 2) i
  else ind k (P 1) i + ind k (P 2) i

def GP (P : Fin 3 → Fin k) (z : Fin k → Bool) : Bool :=
  Gb ((P 0).val % 3) ((P 1).val % 3) ((P 2).val % 3) (z (P 0)) (z (P 1)) (z (P 2))

theorem lamv_sum (P : Fin 3 → Fin k) (z : Fin k → Bool) :
    ∑ i, lamv k P i * B2 (z i) = B2 (GP k P z) := by
  unfold lamv GP Gb
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib, ind, B2_xor, add_assoc]

theorem zs_aff (s1 s2 s3 : Fin k → Bool) (i : Fin k) :
    zs k hk (add k (add k s1 s2) s3) i = xor (xor (zs k hk s1 i) (zs k hk s2 i)) (zs k hk s3 i) := by
  simp only [zs, add]
  split_ifs <;> simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem GP_aff (P : Fin 3 → Fin k) (z1 z2 z3 : Fin k → Bool) :
    GP k P (fun i => xor (xor (z1 i) (z2 i)) (z3 i)) = xor (xor (GP k P z1) (GP k P z2)) (GP k P z3) := by
  simp only [GP, Gb]
  split_ifs <;> simp [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

theorem sx_aff (u x1 x2 x3 : Fin k → Bool) :
    sx k hk u (add k (add k x1 x2) x3) = add k (add k (sx k hk u x1) (sx k hk u x2)) (sx k hk u x3) := by
  funext i; simp only [sx, add, rot]
  cases u i <;> cases x1 (ix k hk (i.val + k - 1)) <;> cases x2 (ix k hk (i.val + k - 1)) <;>
    cases x3 (ix k hk (i.val + k - 1)) <;> rfl

def rotinv (y : Fin k → Bool) : Fin k → Bool := fun j => y (ix k hk (j.val + 1))

theorem rot_rotinv (y : Fin k → Bool) : rot k hk (rotinv k hk y) = y := by
  funext i
  simp only [rot, rotinv]
  rw [ix_mod, ix_ofeq k hk _ (i.val + k) (by omega), ix_addk, ix_fin]

theorem sx_surj (u s : Fin k → Bool) : sx k hk u (rotinv k hk (add k u s)) = s := by
  simp only [sx]; rw [rot_rotinv]; funext i; simp only [add]; cases u i <;> cases s i <;> rfl

theorem lower_reduce (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (u : Fin k → Bool) (q : Nat)
    (panel : Fin q → Fin 3 → Fin k) (pick : (Fin k → Bool) → Fin q)
    (hinj : Function.Injective (fun x : Fin k → Bool =>
        (diff k hk u x, fun j : Fin 3 => row k hk u x (panel (pick (diff k hk u x)) j)))) :
    ∃ S : Finset (Fin q), ∀ s : Fin k → Bool,
      ∑ i, (∑ j ∈ S, lamv k (panel j) i) * B2 (zs k hk s i) = 1 := by
  classical
  have h6 : 6 ≤ k := by omega
  have h3 : k % 3 = 0 := by omega
  let G : Fin q → (Fin k → Bool) → ZMod 2 := fun j x => B2 (GP k (panel j) (zs k hk (sx k hk u x)))
  have Gaff : ∀ j x1 x2 x3, G j (add k (add k x1 x2) x3) = G j x1 + G j x2 + G j x3 := by
    intro j x1 x2 x3
    simp only [G]
    rw [sx_aff]
    have : zs k hk (add k (add k (sx k hk u x1) (sx k hk u x2)) (sx k hk u x3)) =
        fun i => xor (xor (zs k hk (sx k hk u x1) i) (zs k hk (sx k hk u x2) i)) (zs k hk (sx k hk u x3) i) := by
      funext i; exact zs_aff k hk _ _ _ i
    rw [this, GP_aff, B2_xor, B2_xor]
  let z0 : Fin k → Bool := fun _ => false
  let op : (Fin k → Bool) × Bool → (Fin k → Bool) × Bool → (Fin k → Bool) × Bool :=
    fun a b => (add k a.1 b.1, xor a.2 b.2)
  let gt : Fin q → (Fin k → Bool) × Bool → ZMod 2 := fun j a => G j a.1 + G j z0 + B2 a.2 * G j z0
  have hgt : ∀ j a b, gt j (op a b) = gt j a + gt j b := by
    intro j a b
    simp only [gt, op]
    have e1 : add k a.1 b.1 = add k (add k a.1 b.1) z0 := by funext i; simp [add, z0]
    rw [e1, Gaff, B2_xor]
    rcases z2c (G j a.1) with c1 | c1 <;> rcases z2c (G j b.1) with c2 | c2 <;> rcases z2c (G j z0) with c3 | c3 <;>
      rcases z2c (B2 a.2) with c4 | c4 <;> rcases z2c (B2 b.2) with c5 | c5 <;> rw [c1, c2, c3, c4, c5] <;> decide
  have hht : ∀ a b, B2 (op a b).2 = B2 a.2 + B2 b.2 := by intro a b; exact B2_xor _ _
  rcases sep op gt hgt Finset.univ (fun a => B2 a.2) hht with ⟨⟨x, t⟩, hx, ht⟩ | ⟨S, _, hS⟩
  · exfalso
    have tt : t = true := by cases t <;> simp_all [B2]
    subst tt
    have hG : ∀ j, G j x = 0 := by
      intro j; have := hx j (Finset.mem_univ _); simp only [gt, B2, if_true, one_mul] at this
      rcases z2c (G j z0) with c | c <;> rw [c] at this <;> revert this <;>
        rcases z2c (G j x) with d | d <;> rw [d] <;> decide
    have hj := hG (pick (diff k hk u x))
    simp only [G] at hj
    have hgb : GP k (panel (pick (diff k hk u x))) (zs k hk (sx k hk u x)) = false := by
      revert hj; cases GP k (panel (pick (diff k hk u x))) (zs k hk (sx k hk u x)) <;> decide
    rw [← zD_diff k hk h6] at hgb
    have nw := fin_low ⟨_, Nat.mod_lt ((panel (pick (diff k hk u x)) 0).val) (by norm_num)⟩
      ⟨_, Nat.mod_lt ((panel (pick (diff k hk u x)) 1).val) (by norm_num)⟩
      ⟨_, Nat.mod_lt ((panel (pick (diff k hk u x)) 2).val) (by norm_num)⟩ _ _ _ hgb
    simp only [wk, not_forall] at nw
    obtain ⟨e, a, b, w0, w1, w2, hne⟩ := nw
    have heq := hinj (a₁ := add k x (tau k e a b)) (a₂ := x) (by
      simp only [Prod.mk.injEq]
      refine ⟨diff_tau k hk h6 h3 u x e a b, ?_⟩
      rw [diff_tau k hk h6 h3 u x e a b]
      funext t
      fin_cases t
      · exact (read_tau k hk h6 h3 u x e a b _).mpr w0
      · exact (read_tau k hk h6 h3 u x e a b _).mpr w1
      · exact (read_tau k hk h6 h3 u x e a b _).mpr w2)
    exact hne (tau_zero k h6 x e a b heq)
  · refine ⟨S, fun s => ?_⟩
    have := hS (rotinv k hk (add k u s), true)
    simp only [gt, B2, if_true, one_mul] at this
    have e2 : ∀ j, G j (rotinv k hk (add k u s)) + G j z0 + G j z0 = G j (rotinv k hk (add k u s)) := by
      intro j; rcases z2c (G j z0) with c | c <;> rw [c] <;> ring_nf <;> simp [CharTwo.two_eq_zero]
    simp only [e2] at this
    simp only [G, sx_surj] at this
    rw [this]
    simp only [← lamv_sum]
    rw [Finset.sum_comm]
    simp only [Finset.sum_mul]


def ee (n : Nat) : Fin k → Bool := fun i => decide (i.val = n)

theorem sum_dec (ν : Fin k → ZMod 2) (n : Nat) (hn : n < k) :
    ∑ i, ν i * B2 (ee k n i) = ν (ix k hk n) := by
  rw [Finset.sum_eq_single (ix k hk n)]
  · simp [B2, ee, ix_val' k hk n hn]
  · intro b _ hb
    have : b.val ≠ n := fun h => hb (Fin.ext (by rw [h, ix_val' k hk n hn]))
    simp [B2, ee, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem zs_e0 (h6 : 6 ≤ k) : zs k hk (fun _ => false) = ee k 2 := by
  funext i; have hi := i.isLt; simp only [zs, ee]
  split_ifs <;> simp <;> omega

theorem zs_e2 (h6 : 6 ≤ k) : zs k hk (ee k 2) = ee k 1 := by
  funext i; have hi := i.isLt; simp only [zs, ee, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h <;>
  simp (disch := omega) only [mod_lt', mod_ge', if_pos, if_neg, decide_eq_true, decide_eq_false] <;> simp

theorem zs_e3 (h6 : 6 ≤ k) : zs k hk (ee k 3) = fun i => xor (ee k 1 i) (xor (ee k 2 i) (ee k 3 i)) := by
  funext i; have hi := i.isLt; simp only [zs, ee, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (i.val = 3 ∧ i.val + 3 < k) ∨ (4 ≤ i.val ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h | h <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', if_pos, if_neg, decide_eq_true, decide_eq_false] <;> simp

theorem zs_e4 (h9 : 9 ≤ k) : zs k hk (ee k 4) = fun i => xor (ee k 2 i) (ee k 4 i) := by
  funext i; have hi := i.isLt; simp only [zs, ee, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 4 ∨ (3 ≤ i.val ∧ i.val ≠ 4 ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h | h <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', if_pos, if_neg, decide_eq_true, decide_eq_false] <;> simp

theorem zs_en (h6 : 6 ≤ k) (n : Nat) (hn5 : 5 ≤ n) (hn : n + 3 ≤ k) :
    zs k hk (ee k n) = fun i => xor (ee k 2 i) (xor (ee k n i) (ee k (n-3) i)) := by
  funext i; have hi := i.isLt; simp only [zs, ee, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h <;>
  rcases (show i.val = n ∨ i.val + 3 = n ∨ (i.val ≠ n ∧ i.val + 3 ≠ n) by omega) with h' | h' | h' <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', if_pos, if_neg, decide_eq_true, decide_eq_false] <;> simp

theorem zs_ek1 (h6 : 6 ≤ k) :
    zs k hk (ee k (k-1)) = fun i => xor (ee k 2 i) (xor (ee k (k-2) i) (ee k (k-4) i)) := by
  funext i; have hi := i.isLt; simp only [zs, ee, ix]
  rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ (3 ≤ i.val ∧ i.val + 3 < k) ∨ i.val + 3 = k ∨
      i.val + 2 = k ∨ i.val + 1 = k by omega) with h | h | h | h | h | h | h <;>
  rcases (show i.val + 4 = k ∨ i.val + 4 ≠ k by omega) with h' | h' <;>
  (first | (exfalso; omega) | skip) <;>
  simp (disch := omega) only [mod_lt', mod_ge', if_pos, if_neg, decide_eq_true, decide_eq_false] <;> simp

theorem sum3 (ν : Fin k → ZMod 2) (f g h : Fin k → Bool) :
    ∑ i, ν i * B2 (xor (f i) (xor (g i) (h i))) = ∑ i, ν i * B2 (f i) + ∑ i, ν i * B2 (g i) + ∑ i, ν i * B2 (h i) := by
  simp only [B2_xor, mul_add, Finset.sum_add_distrib, add_assoc]

theorem sum2 (ν : Fin k → ZMod 2) (f g : Fin k → Bool) :
    ∑ i, ν i * B2 (xor (f i) (g i)) = ∑ i, ν i * B2 (f i) + ∑ i, ν i * B2 (g i) := by
  simp only [B2_xor, mul_add, Finset.sum_add_distrib]

theorem nu_facts (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (ν : Fin k → ZMod 2)
    (hΦ : ∀ s, ∑ i, ν i * B2 (zs k hk s i) = 1) :
    (∀ m, 3*m + 3 + 3 ≤ k → ν (ix k hk (3*m+3)) = 1) ∧ (∀ m, 3*m + 2 + 3 ≤ k → ν (ix k hk (3*m+2)) = 1) ∧
    ν (ix k hk 1) = 1 ∧ ν (ix k hk (k-2)) = 1 ∧ (∀ m, 3*m + 4 + 5 ≤ k → ν (ix k hk (3*m+4)) = 0) := by
  have h6 : 6 ≤ k := by omega
  have n2 : ν (ix k hk 2) = 1 := by
    have := hΦ (fun _ => false); rwa [zs_e0 k hk h6, sum_dec k hk ν 2 (by omega)] at this
  have n1 : ν (ix k hk 1) = 1 := by
    have := hΦ (ee k 2); rwa [zs_e2 k hk h6, sum_dec k hk ν 1 (by omega)] at this
  have n3 : ν (ix k hk 3) = 1 := by
    have := hΦ (ee k 3)
    rw [zs_e3 k hk h6, sum3, sum_dec k hk ν 1 (by omega), sum_dec k hk ν 2 (by omega),
      sum_dec k hk ν 3 (by omega), n1, n2] at this
    rcases z2c (ν (ix k hk 3)) with c | c <;> rw [c] at this ⊢ <;> revert this <;> decide
  have nstep : ∀ n, 5 ≤ n → n + 3 ≤ k → ν (ix k hk n) = ν (ix k hk (n-3)) := by
    intro n hn5 hn
    have := hΦ (ee k n)
    rw [zs_en k hk h6 n hn5 hn, sum3, sum_dec k hk ν 2 (by omega), sum_dec k hk ν n (by omega),
      sum_dec k hk ν (n-3) (by omega), n2] at this
    rcases z2c (ν (ix k hk n)) with c | c <;> rw [c] at this ⊢ <;>
      rcases z2c (ν (ix k hk (n-3))) with d | d <;> rw [d] at this ⊢ <;> revert this <;> decide
  have c2 : ∀ m, 3*m + 2 + 3 ≤ k → ν (ix k hk (3*m+2)) = 1 := by
    intro m; induction m with
    | zero => intro _; exact n2
    | succ m ih =>
      intro hm; rw [nstep _ (by omega) (by omega), show 3*(m+1)+2-3 = 3*m+2 by omega]; exact ih (by omega)
  refine ⟨?_, c2, n1, ?_, ?_⟩
  · intro m; induction m with
    | zero => intro _; exact n3
    | succ m ih =>
      intro hm; rw [nstep _ (by omega) (by omega), show 3*(m+1)+3-3 = 3*m+3 by omega]; exact ih (by omega)
  · have e1 := hΦ (ee k (k-1))
    rw [zs_ek1 k hk h6, sum3, sum_dec k hk ν 2 (by omega), sum_dec k hk ν (k-2) (by omega),
      sum_dec k hk ν (k-4) (by omega), n2, show k - 4 = 3*(r-2)+2 by omega, c2 (r-2) (by omega)] at e1
    rcases z2c (ν (ix k hk (k-2))) with c | c <;> rw [c] at e1 ⊢ <;> revert e1 <;> decide
  · intro m; induction m with
    | zero =>
      intro hm
      have := hΦ (ee k 4)
      rw [zs_e4 k hk (by omega), sum2, sum_dec k hk ν 2 (by omega), sum_dec k hk ν 4 (by omega), n2] at this
      rcases z2c (ν (ix k hk 4)) with c | c <;> rw [c] at this ⊢ <;> revert this <;> decide
    | succ m ih =>
      intro hm; rw [nstep _ (by omega) (by omega), show 3*(m+1)+4-3 = 3*m+4 by omega]; exact ih (by omega)


theorem gb_par : ∀ c0 c1 c2 : Fin 3,
    Gb c0.val c1.val c2.val (decide (c0.val ≠ 2)) (decide (c1.val ≠ 2)) (decide (c2.val ≠ 2)) = false ∧
    Gb c0.val c1.val c2.val (decide (c0.val ≠ 0)) (decide (c1.val ≠ 0)) (decide (c2.val ≠ 0)) = false := by
  decide

theorem lam_perp (P : Fin 3 → Fin k) (c : Nat) (hc : c = 0 ∨ c = 2) :
    ∑ i, lamv k P i * B2 (decide (i.val % 3 ≠ c)) = 0 := by
  rw [lamv_sum]; simp only [GP]
  have h := gb_par ⟨_, Nat.mod_lt (P 0).val (by norm_num)⟩ ⟨_, Nat.mod_lt (P 1).val (by norm_num)⟩
    ⟨_, Nat.mod_lt (P 2).val (by norm_num)⟩
  simp only [Fin.val_mk] at h
  rcases hc with rfl | rfl
  · rw [h.2]; rfl
  · rw [h.1]; rfl

theorem sum_const_ee (hk : 0 < k) (c : ZMod 2) (n : Nat) (hn : n < k) : ∑ i, c * B2 (ee k n i) = c := by
  have := sum_dec k hk (fun _ => c) n hn; simpa using this

theorem sum_ee (hk : 0 < k) (n : Nat) (hn : n < k) : ∑ i, B2 (ee k n i) = 1 := by
  have := sum_dec k hk (fun _ => 1) n hn; simpa using this

theorem sum_boole' (p : Fin k → Prop) [DecidablePred p] :
    ∑ i, B2 (decide (p i)) = ((Finset.univ.filter p).card : ZMod 2) := by
  rw [← Finset.sum_boole]; congr 1; funext i; by_cases h : p i <;> simp [B2, h]

theorem card_cls (hk : 0 < k) (r : Nat) (hkr : k = 3*r) (h2 : 2 ≤ r) (c : Nat) (hc : c = 2 ∨ c = 3) :
    (Finset.univ.filter (fun i : Fin k => i.val % 3 = c % 3 ∧ c ≤ i.val ∧ i.val + 6 - c ≤ k)).card = r - 1 := by
  have e : Finset.univ.filter (fun i : Fin k => i.val % 3 = c % 3 ∧ c ≤ i.val ∧ i.val + 6 - c ≤ k) =
      (Finset.range (r-1)).image (fun m => ix k hk (3*m + c)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2', h3⟩
      exact ⟨(i.val - c)/3, by omega, Fin.ext (by rw [ix_val' k hk _ (by omega)]; omega)⟩
    · rintro ⟨m, hm, rfl⟩
      rw [ix_val' k hk _ (by omega)]; omega
  rw [e, Finset.card_image_of_injOn]
  · simp
  · intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have := congrArg Fin.val hab
    simp only at this
    rw [ix_val' k hk _ (by omega), ix_val' k hk _ (by omega)] at this
    omega

theorem lam_supp (P : Fin 3 → Fin k) :
    ∃ a b : Fin k, ∀ i : Fin k, i.val % 3 ≠ 1 → lamv k P i ≠ 0 → i = a ∨ i = b := by
  unfold lamv
  split_ifs with h1 h2 h3
  · rcases (show (P 0).val % 3 = 1 ∨ (P 1).val % 3 = 1 ∨ (P 2).val % 3 = 1 by omega) with c | c | c
    · refine ⟨P 1, P 2, fun i hi hl => ?_⟩
      by_contra hne; push_neg at hne
      have : i ≠ P 0 := fun e => hi (e ▸ c)
      simp [ind, hne.1, hne.2, this] at hl
    · refine ⟨P 0, P 2, fun i hi hl => ?_⟩
      by_contra hne; push_neg at hne
      have : i ≠ P 1 := fun e => hi (e ▸ c)
      simp [ind, hne.1, hne.2, this] at hl
    · refine ⟨P 0, P 1, fun i hi hl => ?_⟩
      by_contra hne; push_neg at hne
      have : i ≠ P 2 := fun e => hi (e ▸ c)
      simp [ind, hne.1, hne.2, this] at hl
  · refine ⟨P 0, P 1, fun i _ hl => ?_⟩
    by_contra hne; push_neg at hne; simp [ind, hne.1, hne.2] at hl
  · refine ⟨P 0, P 2, fun i _ hl => ?_⟩
    by_contra hne; push_neg at hne; simp [ind, hne.1, hne.2] at hl
  · refine ⟨P 1, P 2, fun i _ hl => ?_⟩
    by_contra hne; push_neg at hne; simp [ind, hne.1, hne.2] at hl

theorem lower (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (u : Fin k → Bool) (q : Nat)
    (panel : Fin q → Fin 3 → Fin k) (pick : (Fin k → Bool) → Fin q)
    (hinj : Function.Injective (fun x : Fin k → Bool =>
        (diff k hk u x, fun j : Fin 3 => row k hk u x (panel (pick (diff k hk u x)) j)))) :
    2*(r/2) ≤ q := by
  classical
  have h6 : 6 ≤ k := by omega
  obtain ⟨S, hS⟩ := lower_reduce k hk r h2 hkr u q panel pick hinj
  set ν : Fin k → ZMod 2 := fun i => ∑ j ∈ S, lamv k (panel j) i with hν
  obtain ⟨c0, c2, n1, nk2, c1⟩ := nu_facts k hk r h2 hkr ν hS
  have perp : ∀ c, c = 0 ∨ c = 2 → ∑ i, ν i * B2 (decide (i.val % 3 ≠ c)) = 0 := by
    intro c hc
    simp only [hν, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun j _ => lam_perp k (panel j) c hc)
  have hcast : r % 2 = 0 → ((r - 1 : Nat) : ZMod 2) = 1 := by
    intro hr
    rw [show r - 1 = 2*(r/2 - 1) + 1 by omega]; push_cast
    rw [show (2 : ZMod 2) = 0 from rfl]; simp
  have ev0 : r % 2 = 0 → ν (ix k hk 0) = 1 := by
    intro hr
    have hp := perp 2 (by omega)
    have pw : ∀ i : Fin k, ν i * B2 (decide (i.val % 3 ≠ 2)) =
        ν (ix k hk 0) * B2 (ee k 0 i) + B2 (ee k 1 i) + B2 (ee k (k-2) i) +
          B2 (decide (i.val % 3 = 3 % 3 ∧ 3 ≤ i.val ∧ i.val + 6 - 3 ≤ k)) := by
      intro i
      have hi := i.isLt
      have hix := ix_fin k hk i
      rcases (show i.val = 0 ∨ i.val = 1 ∨ i.val + 2 = k ∨ (2 ≤ i.val ∧ i.val + 3 ≤ k ∧ i.val % 3 = 0) ∨
          (4 ≤ i.val ∧ i.val + 5 ≤ k ∧ i.val % 3 = 1) ∨ i.val % 3 = 2 by omega) with h | h | h | h | h | h
      · have : i = ix k hk 0 := by rw [← hix, h]
        rw [← this]; simp (disch := omega) [ee, h, B2, decide_eq_true, decide_eq_false]
      · have : i = ix k hk 1 := by rw [← hix, h]
        rw [this, n1]; rw [← this]; simp (disch := omega) [ee, h, B2, decide_eq_true, decide_eq_false]
      · have : i = ix k hk (k-2) := by rw [← hix]; congr 1; omega
        rw [this, nk2]; rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false] <;> omega
      · have : i = ix k hk (3*((i.val-3)/3)+3) := by rw [← hix]; congr 1; omega
        rw [this, c0 _ (by omega)]; rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false]
      · have : i = ix k hk (3*((i.val-4)/3)+4) := by rw [← hix]; congr 1; omega
        rw [this, c1 _ (by omega)]; rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false]
      · simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false]
    simp only [pw, Finset.sum_add_distrib, sum_const_ee k hk _ 0 (by omega), sum_ee k hk 1 (by omega),
      sum_ee k hk (k-2) (by omega), sum_boole', card_cls k hk r hkr h2 3 (by omega), hcast hr] at hp
    rcases z2c (ν (ix k hk 0)) with c | c <;> rw [c] at hp ⊢ <;> revert hp <;> decide
  have evk : r % 2 = 0 → ν (ix k hk (k-1)) = 1 := by
    intro hr
    have hp := perp 0 (by omega)
    have pw : ∀ i : Fin k, ν i * B2 (decide (i.val % 3 ≠ 0)) =
        ν (ix k hk (k-1)) * B2 (ee k (k-1) i) + B2 (ee k 1 i) + B2 (ee k (k-2) i) +
          B2 (decide (i.val % 3 = 2 % 3 ∧ 2 ≤ i.val ∧ i.val + 6 - 2 ≤ k)) := by
      intro i
      have hi := i.isLt
      have hix := ix_fin k hk i
      rcases (show i.val + 1 = k ∨ i.val = 1 ∨ i.val + 2 = k ∨ (2 ≤ i.val ∧ i.val + 4 ≤ k ∧ i.val % 3 = 2) ∨
          (4 ≤ i.val ∧ i.val + 5 ≤ k ∧ i.val % 3 = 1) ∨ i.val % 3 = 0 by omega) with h | h | h | h | h | h
      · have : i = ix k hk (k-1) := by rw [← hix]; congr 1; omega
        rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false] <;> omega
      · have : i = ix k hk 1 := by rw [← hix, h]
        rw [this, n1]; rw [← this]; simp (disch := omega) [ee, h, B2, decide_eq_true, decide_eq_false]
      · have : i = ix k hk (k-2) := by rw [← hix]; congr 1; omega
        rw [this, nk2]; rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false] <;> omega
      · have : i = ix k hk (3*((i.val-2)/3)+2) := by rw [← hix]; congr 1; omega
        rw [this, c2 _ (by omega)]; rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false]
      · have : i = ix k hk (3*((i.val-4)/3)+4) := by rw [← hix]; congr 1; omega
        rw [this, c1 _ (by omega)]; rw [← this]; simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false]
      · simp (disch := omega) [ee, B2, decide_eq_true, decide_eq_false]
    simp only [pw, Finset.sum_add_distrib, sum_const_ee k hk _ (k-1) (by omega), sum_ee k hk 1 (by omega),
      sum_ee k hk (k-2) (by omega), sum_boole', card_cls k hk r hkr h2 2 (by omega), hcast hr] at hp
    rcases z2c (ν (ix k hk (k-1))) with c | c <;> rw [c] at hp ⊢ <;> revert hp <;> decide
  let f : Nat → Fin k := fun n => if n < r - 1 then ix k hk (3*n+3) else if n < 2*(r-1) then
    ix k hk (3*(n-(r-1))+2) else if n = 2*(r-1) then ix k hk 0 else ix k hk (k-1)
  let O : Finset (Fin k) := (Finset.range (4*(r/2))).image f
  have hO : ∀ i ∈ O, ν i = 1 ∧ i.val % 3 ≠ 1 := by
    intro i hi
    simp only [O, Finset.mem_image, Finset.mem_range] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    simp only [f]
    split_ifs with g1 g2 g3
    · exact ⟨c0 n (by omega), by rw [ix_val' k hk _ (by omega)]; omega⟩
    · exact ⟨c2 _ (by omega), by rw [ix_val' k hk _ (by omega)]; omega⟩
    · exact ⟨ev0 (by omega), by rw [ix_val' k hk _ (by omega)]; omega⟩
    · exact ⟨evk (by omega), by rw [ix_val' k hk _ (by omega)]; omega⟩
  have hcard : O.card = 4*(r/2) := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      have := congrArg Fin.val hab
      simp only [f] at this
      split_ifs at this <;> simp (disch := omega) only [ix, mod_lt'] at this <;> omega
  have hcov : O ⊆ S.biUnion (fun j => O.filter (fun i => lamv k (panel j) i ≠ 0)) := by
    intro i hi
    rw [Finset.mem_biUnion]
    by_contra hno
    push_neg at hno
    have : ν i = 0 := by
      simp only [hν]
      apply Finset.sum_eq_zero
      intro j hj
      have := hno j hj
      simp only [Finset.mem_filter, not_and, not_not] at this
      exact this hi
    rw [(hO i hi).1] at this
    exact absurd this (by decide)
  have hle : ∀ j, (O.filter (fun i => lamv k (panel j) i ≠ 0)).card ≤ 2 := by
    intro j
    obtain ⟨a, b, hab⟩ := lam_supp k (panel j)
    calc (O.filter (fun i => lamv k (panel j) i ≠ 0)).card ≤ ({a, b} : Finset (Fin k)).card := by
          apply Finset.card_le_card
          intro i hi
          simp only [Finset.mem_filter] at hi
          rcases hab i (hO i hi.1).2 hi.2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two
  have hSq : S.card ≤ q := by
    have := Finset.card_le_univ S; simpa using this
  have : 4*(r/2) ≤ 2 * S.card := by
    calc 4*(r/2) = O.card := hcard.symm
      _ ≤ (S.biUnion (fun j => O.filter (fun i => lamv k (panel j) i ≠ 0))).card := Finset.card_le_card hcov
      _ ≤ ∑ j ∈ S, (O.filter (fun i => lamv k (panel j) i ≠ 0)).card := Finset.card_biUnion_le
      _ ≤ ∑ j ∈ S, 2 := Finset.sum_le_sum (fun j _ => hle j)
      _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

theorem main (r : Nat) (h2 : 2 ≤ r) (hkr : k = 3*r) (u : Fin k → Bool) (q : Nat) :
    (∃ (panel : Fin q → Fin 3 → Fin k) (pick : (Fin k → Bool) → Fin q),
      Function.Injective (fun x : Fin k → Bool =>
        (diff k hk u x, fun j : Fin 3 => row k hk u x (panel (pick (diff k hk u x)) j)))) ↔ 2*(r/2) ≤ q := by
  constructor
  · rintro ⟨panel, pick, hinj⟩; exact lower k hk r h2 hkr u q panel pick hinj
  · intro hq; exact upper k hk r h2 hkr u q hq

end
end PEqualNP.Outside.L_meta_42251

theorem PEqualNP.Outside.L_meta_42251 : (∀ (r k : Nat) (hk : 0 < k), 2 ≤ r → k = 3*r →
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let mix := fun (w : W) (i : Fin k) => xor (w (ix (i.val+k-1))) (xor (w i) (w (ix (i.val+1))))
  let rot := fun (x : W) (i : Fin k) => x (ix (i.val+k-1))
  let chi := fun (w : W) (i : Fin k) => xor (w i) (!(w (ix (i.val+1))) && w (ix (i.val+2)))
  let row := fun (u x : W) => add (chi (mix (add u (rot x)))) x
  let v : W := fun i => decide (i.val ≠ 1)
  ∀ u : W,
    let base := row u
    let diff := fun x : W => add (base x) (row (add u v) x)
    ∀ q : Nat,
      (∃ (panel : Fin q → Fin 3 → Fin k) (pick : W → Fin q),
        Function.Injective (fun x : W =>
          (diff x, fun j : Fin 3 => base x (panel (pick (diff x)) j)))) ↔
      2*(r/2) ≤ q) := by
  intro r k hk h2 hkr
  intro W ix add mix rot chi row v u base diff q
  exact PEqualNP.Outside.L_meta_42251.main k hk r h2 hkr u q
