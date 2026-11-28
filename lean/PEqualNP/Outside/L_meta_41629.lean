import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41629

open Fin.CommRing

-- The cyclic kernel lemmas below (Gd, gd_zero, Ps, ps_eq) and the index casts
-- (ixN, castA, castS) are taken from our PEqualNP.Outside.L_meta_40554.
section cyc
variable {m : ℕ} [NeZero m]

abbrev Gd (v : Fin m → Bool) : Prop :=
  ∀ t : Fin m, xor (v t) (xor (v (t+1)) (v (t+1+1))) = false

theorem b3 : ∀ a b c : Bool, xor a (xor b c) = false → c = xor a b := by decide

theorem sq_step (v : Fin m → Bool) (hv : Gd v) (n : ℕ) :
    v ((n+2 : ℕ) : Fin m) = xor (v (n : Fin m)) (v ((n+1 : ℕ) : Fin m)) := by
  have h := hv (n : Fin m)
  have e1 : ((n : Fin m) + 1) = ((n+1 : ℕ) : Fin m) := by push_cast; rfl
  have e2 : ((n : Fin m) + 1 + 1) = ((n+2 : ℕ) : Fin m) := by push_cast; ring
  rw [e2, e1] at h
  exact b3 _ _ _ h

theorem s3 (v : Fin m → Bool) (hv : Gd v) (n : ℕ) :
    v ((n+3 : ℕ) : Fin m) = v (n : Fin m) := by
  have h1 := sq_step v hv (n+1)
  have h0 := sq_step v hv n
  rw [show n + 1 + 2 = n + 3 by omega, show n + 1 + 1 = n + 2 by omega, h0] at h1
  rw [h1]; cases v (n : Fin m) <;> cases v ((n+1 : ℕ) : Fin m) <;> rfl

theorem smod (v : Fin m → Bool) (hv : Gd v) (n : ℕ) :
    v (n : Fin m) = v ((n % 3 : ℕ) : Fin m) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 3
    · rw [Nat.mod_eq_of_lt hn]
    · have e : n = (n - 3) + 3 := by omega
      rw [e, s3 v hv, ih (n-3) (by omega)]
      rw [show (n - 3 + 3) % 3 = (n - 3) % 3 by omega]

theorem sper (v : Fin m → Bool) (n : ℕ) : v ((n + m : ℕ) : Fin m) = v (n : Fin m) := by
  rw [Nat.cast_add, Fin.natCast_self, add_zero]

theorem b3z : ∀ a b c : Bool, a = b → b = c → c = xor a b → a = false ∧ b = false ∧ c = false := by
  decide

theorem gd_zero (hm : ¬ 3 ∣ m) (v : Fin m → Bool) (hv : Gd v) : v = fun _ => false := by
  have key : ∀ a : ℕ, v (a : Fin m) = v (((a + m) % 3 : ℕ) : Fin m) := fun a => by
    rw [← sper v a, smod v hv]
  have h2 := sq_step v hv 0
  rw [show (0:ℕ) + 2 = 2 from rfl, show (0:ℕ) + 1 = 1 from rfl] at h2
  have hz : v ((0 : ℕ) : Fin m) = false ∧ v ((1 : ℕ) : Fin m) = false ∧
      v ((2 : ℕ) : Fin m) = false := by
    rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h | h
    · have q0 := key 0
      have q1 := key 1
      rw [show (0 + m) % 3 = 1 by omega] at q0
      rw [show (1 + m) % 3 = 2 by omega] at q1
      exact b3z _ _ _ q0 q1 h2
    · have q0 := key 0
      have q1 := key 1
      rw [show (0 + m) % 3 = 2 by omega] at q0
      rw [show (1 + m) % 3 = 0 by omega] at q1
      exact b3z _ _ _ q1.symm (q1.trans q0) h2
  funext t
  rw [← Fin.cast_val_eq_self t, smod v hv]
  have hr : t.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize t.val % 3 = r at hr ⊢
  interval_cases r
  · exact hz.1
  · exact hz.2.1
  · exact hz.2.2

def Pt (a b : Bool) (r : ℕ) : Bool := if r = 0 then a else if r = 1 then b else xor a b
def Ps (a b : Bool) (t : Fin m) : Bool := Pt a b (t.val % 3)

theorem vs (h3 : 3 ∣ m) (t : Fin m) : (t+1).val % 3 = (t.val % 3 + 1) % 3 := by
  have e : t + 1 = ((t.val + 1 : ℕ) : Fin m) := by simp
  rw [e, Fin.val_natCast, Nat.mod_mod_of_dvd _ h3]; omega

theorem ps_gd (h3 : 3 ∣ m) (a b : Bool) : Gd (Ps (m := m) a b) := by
  intro t
  simp only [Ps]
  rw [vs h3 (t+1), vs h3 t]
  have hr : t.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize t.val % 3 = r at hr ⊢
  interval_cases r <;> simp [Pt] <;> cases a <;> cases b <;> rfl

theorem ps0 (a b : Bool) : Ps (m := m) a b 0 = a := by
  simp [Ps, Pt]

theorem ps1 (h3 : 3 ∣ m) (a b : Bool) : Ps (m := m) a b 1 = b := by
  have := vs h3 (0 : Fin m)
  rw [zero_add] at this
  simp only [Ps, this, Fin.val_zero]
  simp [Pt]

theorem ps_eq (v : Fin m → Bool) (hv : Gd v) : Ps (v 0) (v 1) = v := by
  funext t
  have h2 := sq_step v hv 0
  rw [show (0:ℕ) + 2 = 2 from rfl, show (0:ℕ) + 1 = 1 from rfl, Nat.cast_zero, Nat.cast_one] at h2
  simp only [Ps]
  rw [← Fin.cast_val_eq_self t, smod v hv]
  simp only [Fin.cast_val_eq_self]
  have hr : t.val % 3 < 3 := Nat.mod_lt _ (by norm_num)
  generalize t.val % 3 = r at hr ⊢
  interval_cases r
  · simp [Pt]
  · simp [Pt]
  · simp only [Nat.cast_ofNat] at h2
    simp [Pt, h2]

end cyc

section bools

theorem bE : ∀ a0 a1 a2 b0 b1 b2 p0 p1 p2 d : Bool,
    xor (xor a0 (!a1 && a2)) (xor b0 (!b1 && b2)) = d →
    xor (xor (xor a0 p0) (!(xor a1 p1) && xor a2 p2))
      (xor (xor b0 p0) (!(xor b1 p1) && xor b2 p2)) = d →
    (xor a1 b1 && p2) = (p1 && xor a2 b2) := by decide

theorem bR : ∀ d0 d1 d2 d3 b2 b3 : Bool, b2 = xor d0 (xor d1 d2) →
    b3 = xor d1 (xor d2 d3) → d3 = xor d0 (xor b2 b3) := by decide

theorem bG : ∀ r0 r1 r2 v0 v1 v2 : Bool, xor r0 (xor r1 r2) = xor v0 (xor v1 v2) →
    xor (xor r0 v0) (xor (xor r1 v1) (xor r2 v2)) = false := by decide

theorem bxf : ∀ a b : Bool, xor a b = false → a = b := by decide
theorem bxp : ∀ a b p : Bool, xor a b = p → b = xor a p := by decide
theorem bnn : ∀ a : Bool, a = !a → False := by decide
theorem b4' : ∀ A X A' Y : Bool, xor A X = xor A' Y → xor A A' = xor X Y := by decide

theorem bLin : ∀ u0 u1 u2 v0 v1 v2 r0 r1 r2 : Bool,
    xor (xor (xor u0 v0) r0) (xor (xor (xor u1 v1) r1) (xor (xor u2 v2) r2)) =
      xor (xor (xor u0 r0) (xor (xor u1 r1) (xor u2 r2))) (xor v0 (xor v1 v2)) := by decide

theorem bBD : ∀ u0 u1 u2 x0 x1 x2 y0 y1 y2 : Bool,
    xor (xor (xor u0 x0) (xor (xor u1 x1) (xor u2 x2)))
      (xor (xor u0 y0) (xor (xor u1 y1) (xor u2 y2))) =
      xor (xor x0 y0) (xor (xor x1 y1) (xor x2 y2)) := by decide

def dCh (a0 a1 a2 p0 p1 p2 : Bool) : Bool :=
  xor (xor a0 (!a1 && a2)) (xor (xor a0 p0) (!(xor a1 p1) && xor a2 p2))

theorem bM1 : ∀ a0 a1 a2 a3 : Bool, false = dCh a0 a1 a2 true true false →
    false = dCh a1 a2 a3 true false true → False := by decide
theorem bW0 : ∀ x y z : Bool, dCh x y z true false false = true := by decide
theorem bW1 : ∀ x y z : Bool, dCh x y z false false false = false := by decide
theorem bA1 : ∀ x y z : Bool, dCh x y z false false true = true → y = false := by decide
theorem bA2 : ∀ x y z : Bool, dCh x y z false true true = true → z = !y := by decide
theorem bA3 : ∀ x y z : Bool, dCh x y z true true true = true → z = y := by decide
theorem bA4 : ∀ x y z : Bool, dCh x y z true true false = true → z = false := by decide
theorem bX : ∀ b : Bool, xor (xor b (!b)) (xor false false) = false → False := by decide

end bools

section tele

def par (g : ℕ → Bool) (r : ℕ) : ℕ → Bool
  | 0 => false
  | t + 1 => xor (par g r t) (g (r + 3 * t))

theorem parS (g : ℕ → Bool) (r t : ℕ) : par g r (t + 1) = xor (par g r t) (g (r + 3 * t)) := rfl

theorem par1 (g : ℕ → Bool) (r : ℕ) : par g r 1 = g r := by simp [par]

theorem parC (g : ℕ → Bool) (r a : ℕ) : ∀ b, a ≤ b →
    (∀ t, a ≤ t → t < b → g (r + 3 * t) = false) → par g r b = par g r a := by
  intro b
  induction b with
  | zero => intro h _; rw [Nat.le_zero.mp h]
  | succ b ih =>
    intro hab hz
    rcases Nat.eq_or_lt_of_le hab with e | e
    · rw [e]
    · rw [parS, hz b (by omega) (by omega), Bool.xor_false,
        ih (by omega) (fun t h1 h2 => hz t h1 (by omega))]

theorem tel (f g : ℕ → Bool) (K N : ℕ) (hKN : K = 3 * N) (hper : ∀ n, f (n + K) = f n)
    (hrec : ∀ j, f (j + 3) = xor (f j) (g j)) (r : ℕ) : par g r N = false := by
  have h : ∀ t, f (r + 3 * t) = xor (f r) (par g r t) := by
    intro t
    induction t with
    | zero => simp [par]
    | succ t ih =>
      rw [show r + 3 * (t + 1) = (r + 3 * t) + 3 by ring, hrec, ih, Bool.xor_assoc, parS]
  have := h N
  rw [← hKN, hper] at this
  revert this
  generalize f r = A
  generalize par g r N = B
  cases A <;> cases B <;> decide

theorem telZ (f g : ℕ → Bool) (K N : ℕ) (hKN : K = 3 * N) (hper : ∀ n, f (n + K) = f n)
    (hrec : ∀ j, f (j + 3) = xor (f j) (g j)) (r : ℕ) (hN : 2 ≤ N)
    (hz : ∀ t, 1 ≤ t → t < N - 1 → g (r + 3 * t) = false) :
    xor (g r) (g (r + 3 * (N - 1))) = false := by
  have T := tel f g K N hKN hper hrec r
  rw [show N = (N - 1) + 1 by omega, parS, parC g r 1 (N - 1) (by omega) hz, par1] at T
  exact T

theorem telZ1 (f g : ℕ → Bool) (K N : ℕ) (hKN : K = 3 * N) (hper : ∀ n, f (n + K) = f n)
    (hrec : ∀ j, f (j + 3) = xor (f j) (g j)) (r : ℕ) (hN : 1 ≤ N)
    (hz : ∀ t, 1 ≤ t → t < N → g (r + 3 * t) = false) : g r = false := by
  have T := tel f g K N hKN hper hrec r
  rw [parC g r 1 N hN hz, par1] at T
  exact T

end tele

def Mk (K : ℕ) : ℕ := 1 + (K - 1) % 3
def vN (K n : ℕ) : Bool := decide (Mk K + 1 ≤ n ∧ n + 2 ≤ K ∧ n % 3 = (Mk K + 1) % 3)

theorem Dval3 (K j : ℕ) (hm : Mk K = 3) (h1 : 1 ≤ j) (h2 : j + 2 ≤ K) :
    xor (Pt true false ((j + 1) % 3)) (vN K (j + 1)) = true := by
  have hMk : Mk K = 1 + (K - 1) % 3 := rfl
  cases h : vN K (j + 1) <;> simp only [vN, decide_eq_true_eq, decide_eq_false_iff_not] at h <;>
    rcases (by omega : (j + 1) % 3 = 0 ∨ (j + 1) % 3 = 1 ∨ (j + 1) % 3 = 2) with r | r | r <;>
    simp [Pt, r] <;> omega

theorem patG (K p n s : ℕ) (hk : 4 ≤ K) (hn : n < K)
    (hp : p = if n = 0 then K - 1 else n - 1) (hs : s = if n + 1 = K then 0 else n + 1) :
    xor (vN K p) (xor (vN K n) (vN K s)) = decide (Mk K ≤ n) := by
  have hMk : Mk K = 1 + (K - 1) % 3 := rfl
  cases e1 : vN K p <;> cases e2 : vN K n <;> cases e3 : vN K s <;>
    cases e4 : decide (Mk K ≤ n) <;>
    simp only [vN, decide_eq_true_eq, decide_eq_false_iff_not] at e1 e2 e3 e4 <;>
    first | rfl | (split_ifs at hp hs <;> omega)

section main
variable {k : ℕ} [NeZero k]

theorem ixN (n : ℕ) (h : n % k < k) : (⟨n % k, h⟩ : Fin k) = (n : Fin k) := by
  ext; simp [Fin.val_natCast]

theorem castA (q : Fin k) (s : ℕ) : ((q.val + s : ℕ) : Fin k) = q + (s : Fin k) := by
  push_cast; simp

theorem castS (q : Fin k) (s : ℕ) : ((q.val + k - s % k : ℕ) : Fin k) = q - (s : Fin k) := by
  have h1 : s % k ≤ q.val + k := by have := Nat.mod_lt s (NeZero.pos k); omega
  rw [Nat.cast_sub h1]
  have h2 : ((s % k : ℕ) : Fin k) = (s : Fin k) := by
    ext; simp [Fin.val_natCast]
  push_cast
  rw [h2]
  simp

def Mx1 (z : Fin k → Bool) (i : Fin k) : Bool := xor (z (i - 1)) (xor (z i) (z (i + 1)))
def Ch (z : Fin k → Bool) (i : Fin k) : Bool := xor (z i) (!(z (i + 1)) && z (i + 2))
def Rt (x : Fin k → Bool) (i : Fin k) : Bool := x (i - 1)
def Ad (u v : Fin k → Bool) (i : Fin k) : Bool := xor (u i) (v i)
def Row (n x : Fin k → Bool) (i : Fin k) : Bool := xor (Ch (Mx1 (Ad n (Rt x))) i) (x i)
def Vv (i : Fin k) : Bool := if k = 2 then decide (i.val = 1) else vN k i.val

theorem vp1 (i : Fin k) : (i + 1).val = if i.val + 1 = k then 0 else i.val + 1 := by
  have e : i + 1 = ((i.val + 1 : ℕ) : Fin k) := by rw [castA, Nat.cast_one]
  rw [e, Fin.val_natCast]
  have := i.isLt
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem vm1 (hk : 2 ≤ k) (i : Fin k) : (i - 1).val = if i.val = 0 then k - 1 else i.val - 1 := by
  have e : i - 1 = ((i.val + k - 1 % k : ℕ) : Fin k) := by rw [castS, Nat.cast_one]
  rw [e, Fin.val_natCast, Nat.mod_eq_of_lt (show 1 < k by omega)]
  have := i.isLt
  split_ifs with h
  · rw [h, show 0 + k - 1 = k - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
  · rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

theorem pat (hk : 4 ≤ k) (i : Fin k) : Mx1 (Vv (k := k)) i = decide (Mk k ≤ i.val) := by
  have h2 : k ≠ 2 := by omega
  simp only [Mx1, Vv, if_neg h2]
  exact patG k _ i.val _ hk i.isLt (vm1 (by omega) i) (vp1 i)

theorem q1col (n : Fin k → Bool) : Row n (fun j => n (j + 1)) = Row n (fun j => !(n (j + 1))) := by
  have h0 : Ad n (Rt (fun j => n (j + 1))) = fun _ => false := by
    funext j; simp only [Ad, Rt, sub_add_cancel]; cases n j <;> rfl
  have h1 : Ad n (Rt (fun j => !(n (j + 1)))) = fun _ => true := by
    funext j; simp only [Ad, Rt, sub_add_cancel]; cases n j <;> rfl
  funext i
  simp only [Row, h0, h1]
  simp [Ch, Mx1]

end main

section small

theorem k1b : ∀ b : Bool, ∀ i : Fin 1,
    Row ![b] (fun _ => false) i = Row ![b] (fun _ => true) i := by decide

theorem k3b : ∀ b0 b1 b2 : Bool, ∀ i : Fin 3,
    Row ![b0, b1, b2] (fun _ => false) i = Row ![b0, b1, b2] (fun _ => true) i := by decide

theorem k2b : ∀ u0 u1 x0 x1 y0 y1 : Bool,
    (∀ i : Fin 2, Row ![u0, u1] ![x0, x1] i = Row ![u0, u1] ![y0, y1] i) →
    (∀ i : Fin 2, Row (Ad ![u0, u1] Vv) ![x0, x1] i = Row (Ad ![u0, u1] Vv) ![y0, y1] i) →
    x0 = y0 ∧ x1 = y1 := by decide

theorem k2pat : ∀ i : Fin 2, Mx1 (Vv (k := 2)) i =
    if 2 = 2 then decide (i.val = 1) else decide (Mk 2 ≤ i.val) := by decide

theorem k1col (n : Fin 1 → Bool) : Row n (fun _ => false) = Row n (fun _ => true) := by
  have e : n = ![n 0] := by funext i; fin_cases i; rfl
  rw [e]; funext i; exact k1b _ i

theorem k3col (n : Fin 3 → Bool) : Row n (fun _ => false) = Row n (fun _ => true) := by
  have e : n = ![n 0, n 1, n 2] := by funext i; fin_cases i <;> rfl
  rw [e]; funext i; exact k3b _ _ _ i

theorem k2inj (u : Fin 2 → Bool) :
    Function.Injective (fun x : Fin 2 → Bool => (Row u x, Row (Ad u Vv) x)) := by
  intro x y h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e : ∀ f : Fin 2 → Bool, f = ![f 0, f 1] := fun f => by funext i; fin_cases i <;> rfl
  have h1' : Row ![u 0, u 1] ![x 0, x 1] = Row ![u 0, u 1] ![y 0, y 1] := by
    rw [← e u, ← e x, ← e y]; exact h1
  have h2' : Row (Ad ![u 0, u 1] Vv) ![x 0, x 1] = Row (Ad ![u 0, u 1] Vv) ![y 0, y 1] := by
    rw [← e u, ← e x, ← e y]; exact h2
  obtain ⟨r0, r1⟩ := k2b _ _ _ _ _ _ (fun i => congrFun h1' i) (fun i => congrFun h2' i)
  funext i
  fin_cases i
  · exact r0
  · exact r1

end small

section core
variable {k : ℕ} [NeZero k]

theorem core (h4 : 4 ≤ k) (P v a a' D z : Fin k → Bool)
    (hPv : ∀ i, Mx1 v i = P i) (hv : ∀ i : Fin k, v i = vN k i.val)
    (hPn : ∀ n, n < k → P (n : Fin k) = decide (Mk k ≤ n))
    (hza : ∀ i, a i = Mx1 z i)
    (hloc1 : ∀ i, xor (Ch a i) (Ch a' i) = D i)
    (hloc2 : ∀ i, xor (Ch (Ad a P) i) (Ch (Ad a' P) i) = D i)
    (hBD : ∀ i, Ad a a' i = Mx1 (Rt D) i) : ∀ i, D i = false := by
  have hMk : Mk k = 1 + (k - 1) % 3 := rfl
  have c1 : ∀ n : ℕ, ((n : ℕ) : Fin k) + 1 = ((n + 1 : ℕ) : Fin k) := fun n =>
    (Nat.cast_succ n).symm
  have c2 : ∀ n : ℕ, ((n : ℕ) : Fin k) + 2 = ((n + 2 : ℕ) : Fin k) := fun n => by
    rw [Nat.cast_add, Nat.cast_ofNat]
  have cs : ∀ n : ℕ, ((n + 1 : ℕ) : Fin k) - 1 = ((n : ℕ) : Fin k) := fun n => by
    rw [Nat.cast_succ, add_sub_cancel_right]
  have hvn : ∀ n, n < k → v (n : Fin k) = vN k n := fun n hn => by
    rw [hv, Fin.val_natCast, Nat.mod_eq_of_lt hn]
  have vF : ∀ n, ¬ (Mk k + 1 ≤ n ∧ n + 2 ≤ k ∧ n % 3 = (Mk k + 1) % 3) → vN k n = false :=
    fun n h => decide_eq_false h
  obtain ⟨B, hBdef⟩ : ∃ B, B = Ad a a' := ⟨_, rfl⟩
  have hBl : ∀ i : Fin k, (B (i + 1) && P (i + 2)) = (P (i + 1) && B (i + 2)) := by
    intro i; rw [hBdef]; exact bE _ _ _ _ _ _ _ _ _ _ (hloc1 i) (hloc2 i)
  have hBn : ∀ j : ℕ, (B ((j + 1 : ℕ) : Fin k) && P ((j + 2 : ℕ) : Fin k)) =
      (P ((j + 1 : ℕ) : Fin k) && B ((j + 2 : ℕ) : Fin k)) := by
    intro j; have := hBl (j : Fin k); rwa [c1, c2] at this
  have hrun : ∀ t, Mk k + t ≤ k - 1 → B ((Mk k + t : ℕ) : Fin k) = B ((Mk k : ℕ) : Fin k) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have := hBn (Mk k + t - 1)
      rw [show Mk k + t - 1 + 1 = Mk k + t by omega,
        show Mk k + t - 1 + 2 = Mk k + (t + 1) by omega,
        hPn (Mk k + t) (by omega), hPn (Mk k + (t + 1)) (by omega),
        decide_eq_true (by omega : Mk k ≤ Mk k + t),
        decide_eq_true (by omega : Mk k ≤ Mk k + (t + 1)), Bool.and_true, Bool.true_and] at this
      rw [← this, ih (by omega)]
  have hrun' : ∀ n, Mk k ≤ n → n ≤ k - 1 → B (n : Fin k) = B ((Mk k : ℕ) : Fin k) := by
    intro n h1 h2
    have := hrun (n - Mk k) (by omega)
    rwa [show Mk k + (n - Mk k) = n by omega] at this
  have hB0 : B ((0 : ℕ) : Fin k) = false := by
    have := hBn (k - 2)
    rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = 0 + k by omega, sper B, sper P,
      hPn (k - 1) (by omega), hPn 0 (by omega), decide_eq_true (by omega : Mk k ≤ k - 1),
      decide_eq_false (by omega : ¬ Mk k ≤ 0), Bool.and_false, Bool.true_and] at this
    exact this.symm
  have hBm1 : ∀ n, n + 1 = Mk k → B (n : Fin k) = false := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact hB0
    · have := hBn (n - 1)
      rw [show n - 1 + 1 = n by omega, show n - 1 + 2 = Mk k by omega, hPn n (by omega),
        hPn (Mk k) (by omega), decide_eq_false (by omega : ¬ Mk k ≤ n),
        decide_eq_true (le_refl (Mk k)), Bool.and_true, Bool.false_and] at this
      exact this
  have hBD' : ∀ i, B i = Mx1 (Rt D) i := fun i => by rw [hBdef]; exact hBD i
  have hBDn : ∀ j : ℕ, B ((j + 2 : ℕ) : Fin k) =
      xor (D (j : Fin k)) (xor (D ((j + 1 : ℕ) : Fin k)) (D ((j + 2 : ℕ) : Fin k))) := by
    intro j
    have e1 : ((j + 2 : ℕ) : Fin k) - 1 - 1 = ((j : ℕ) : Fin k) := by
      rw [← c2]; ring
    have e2 : ((j + 2 : ℕ) : Fin k) - 1 = ((j + 1 : ℕ) : Fin k) := by
      rw [← c2, ← c1]; ring
    have e3 : ((j + 2 : ℕ) : Fin k) + 1 - 1 = ((j + 2 : ℕ) : Fin k) := by ring
    rw [hBD']; simp only [Mx1, Rt]; rw [e1, e2, e3]
  have hrecD : ∀ j : ℕ, D ((j + 3 : ℕ) : Fin k) =
      xor (D (j : Fin k)) (xor (B ((j + 2 : ℕ) : Fin k)) (B ((j + 3 : ℕ) : Fin k))) := by
    intro j
    have h1 := hBDn j
    have h2 := hBDn (j + 1)
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega] at h2
    exact bR _ _ _ _ _ _ h1 h2
  have hB1 : Mk k = 3 → B ((1 : ℕ) : Fin k) = false := by
    intro hm
    have hN : k = 3 * (k / 3) := by omega
    have T := telZ (fun n => D (n : Fin k))
      (fun j => xor (B ((j + 2 : ℕ) : Fin k)) (B ((j + 3 : ℕ) : Fin k))) k (k / 3) hN
      (fun n => sper D n) hrecD 2 (by omega) (by
        intro t h1 h2
        beta_reduce
        rw [hrun' (2 + 3 * t + 2) (by omega) (by omega),
          hrun' (2 + 3 * t + 3) (by omega) (by omega), Bool.xor_self])
    rw [hrun' (2 + 2) (by omega) (by omega), hrun' (2 + 3) (by omega) (by omega), Bool.xor_self,
      show 2 + 3 * (k / 3 - 1) + 2 = 1 + k by omega, show 2 + 3 * (k / 3 - 1) + 3 = 2 + k by omega,
      sper B, sper B, hBm1 2 (by omega), Bool.false_xor, Bool.xor_false] at T
    exact T
  have hBP : ∀ i, B i = (B ((Mk k : ℕ) : Fin k) && P i) := by
    intro i
    have hi := i.isLt
    rw [← Fin.cast_val_eq_self i]
    generalize i.val = n at hi ⊢
    by_cases hn : Mk k ≤ n
    · rw [hrun' n hn (by omega), hPn n hi, decide_eq_true hn, Bool.and_true]
    · rw [hPn n hi, decide_eq_false hn, Bool.and_false]
      rcases (by omega : n = 0 ∨ n + 1 = Mk k ∨ (n = 1 ∧ Mk k = 3)) with e | e | ⟨e, hm⟩
      · rw [e]; exact hB0
      · exact hBm1 n e
      · rw [e]; exact hB1 hm
  intro i
  cases hc : B ((Mk k : ℕ) : Fin k)
  · have hae : a' = a := funext fun j => by
      have := hBP j
      rw [hc, Bool.false_and, hBdef] at this
      exact (bxf _ _ this).symm
    rw [← hloc1 i, hae, Bool.xor_self]
  exfalso
  have ha' : ∀ j, a' j = xor (a j) (P j) := fun j => by
    have := hBP j
    rw [hc, Bool.true_and, hBdef] at this
    exact bxp _ _ _ this
  have hBP' : ∀ j, B j = P j := fun j => by rw [hBP j, hc, Bool.true_and]
  have hD : ∀ i, D i = dCh (a i) (a (i + 1)) (a (i + 2)) (P i) (P (i + 1)) (P (i + 2)) := by
    intro i
    have := hloc1 i
    simp only [Ch, ha'] at this
    rw [← this]; rfl
  have hDn : ∀ j : ℕ, D (j : Fin k) = dCh (a (j : Fin k)) (a ((j + 1 : ℕ) : Fin k))
      (a ((j + 2 : ℕ) : Fin k)) (P (j : Fin k)) (P ((j + 1 : ℕ) : Fin k))
      (P ((j + 2 : ℕ) : Fin k)) := by
    intro j; rw [hD, c1, c2]
  have hGd : Gd (fun t => xor (Rt D t) (v t)) := by
    intro t
    have e := (hBD' (t + 1)).symm.trans ((hBP' (t + 1)).trans (hPv (t + 1)).symm)
    simp only [Mx1, add_sub_cancel_right] at e
    exact bG _ _ _ _ _ _ e
  by_cases h3 : Mk k = 3
  · have e0 : (0 : Fin k) - 1 = ((k - 1 : ℕ) : Fin k) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Fin.natCast_self, Nat.cast_one]
    have hw0 : xor (Rt D 0) (v 0) = true := by
      have h := hDn (k - 1)
      rw [show k - 1 + 1 = 0 + k by omega, show k - 1 + 2 = 1 + k by omega, sper a, sper a,
        sper P, sper P, hPn (k - 1) (by omega), hPn 0 (by omega), hPn 1 (by omega),
        decide_eq_true (by omega : Mk k ≤ k - 1), decide_eq_false (by omega : ¬ Mk k ≤ 0),
        decide_eq_false (by omega : ¬ Mk k ≤ 1), bW0] at h
      show xor (D (0 - 1)) (v 0) = true
      rw [e0, h, show (0 : Fin k) = ((0 : ℕ) : Fin k) from Nat.cast_zero.symm,
        hvn 0 (by omega), vF 0 (by omega)]
      all_goals rfl
    have hw1 : xor (Rt D 1) (v 1) = false := by
      have h := hDn 0
      rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl, hPn 0 (by omega),
        hPn 1 (by omega), hPn 2 (by omega), decide_eq_false (by omega : ¬ Mk k ≤ 0),
        decide_eq_false (by omega : ¬ Mk k ≤ 1), decide_eq_false (by omega : ¬ Mk k ≤ 2),
        bW1] at h
      show xor (D (1 - 1)) (v 1) = false
      rw [sub_self, show (0 : Fin k) = ((0 : ℕ) : Fin k) from Nat.cast_zero.symm, h,
        show (1 : Fin k) = ((1 : ℕ) : Fin k) from Nat.cast_one.symm, hvn 1 (by omega),
        vF 1 (by omega)]
      all_goals rfl
    have hps : Ps true false = fun t => xor (Rt D t) (v t) := by
      rw [← hw0, ← hw1]; exact ps_eq _ hGd
    have hDw : ∀ j, j + 1 < k → D (j : Fin k) = xor (Pt true false ((j + 1) % 3)) (vN k (j + 1)) := by
      intro j hj
      have h := congrFun hps ((j + 1 : ℕ) : Fin k)
      simp only [Ps, Rt, cs j, Fin.val_natCast, Nat.mod_eq_of_lt hj] at h
      rw [hvn (j + 1) hj] at h
      rw [h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
    have hDt : ∀ j, 1 ≤ j → j + 2 ≤ k → D (j : Fin k) = true := fun j h1 h2 => by
      rw [hDw j (by omega)]; exact Dval3 k j h3 h1 h2
    have ha2 : a ((2 : ℕ) : Fin k) = false := by
      have h := hDn 1
      rw [show (1 : ℕ) + 1 = 2 from rfl, show (1 : ℕ) + 2 = 3 from rfl, hDt 1 le_rfl (by omega),
        hPn 1 (by omega), hPn 2 (by omega), hPn 3 (by omega),
        decide_eq_false (by omega : ¬ Mk k ≤ 1), decide_eq_false (by omega : ¬ Mk k ≤ 2),
        decide_eq_true (by omega : Mk k ≤ 3)] at h
      exact bA1 _ _ _ h.symm
    have ha34 : a ((4 : ℕ) : Fin k) = !a ((3 : ℕ) : Fin k) := by
      have h := hDn 2
      rw [show (2 : ℕ) + 1 = 3 from rfl, show (2 : ℕ) + 2 = 4 from rfl,
        hDt 2 (by omega) (by omega), hPn 2 (by omega), hPn 3 (by omega), hPn 4 (by omega),
        decide_eq_false (by omega : ¬ Mk k ≤ 2), decide_eq_true (by omega : Mk k ≤ 3),
        decide_eq_true (by omega : Mk k ≤ 4)] at h
      exact bA2 _ _ _ h.symm
    have hstep : ∀ j, 3 ≤ j → j + 3 ≤ k →
        a ((j + 2 : ℕ) : Fin k) = a ((j + 1 : ℕ) : Fin k) := by
      intro j h1 h2
      have h := hDn j
      rw [hDt j (by omega) (by omega), hPn j (by omega), hPn (j + 1) (by omega),
        hPn (j + 2) (by omega), decide_eq_true (by omega : Mk k ≤ j),
        decide_eq_true (by omega : Mk k ≤ j + 1), decide_eq_true (by omega : Mk k ≤ j + 2)] at h
      exact bA3 _ _ _ h.symm
    have ha0 : a ((0 : ℕ) : Fin k) = false := by
      have h := hDn (k - 2)
      rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = 0 + k by omega, sper a, sper P,
        hDt (k - 2) (by omega) (by omega), hPn (k - 2) (by omega), hPn (k - 1) (by omega),
        hPn 0 (by omega), decide_eq_true (by omega : Mk k ≤ k - 2),
        decide_eq_true (by omega : Mk k ≤ k - 1), decide_eq_false (by omega : ¬ Mk k ≤ 0)] at h
      exact bA4 _ _ _ h.symm
    have arun0 : ∀ t, 4 + t ≤ k - 1 → a ((4 + t : ℕ) : Fin k) = a ((4 : ℕ) : Fin k) := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t ih =>
        intro ht
        rw [show 4 + (t + 1) = (t + 3) + 2 by omega, hstep (t + 3) (by omega) (by omega),
          show t + 3 + 1 = 4 + t by omega, ih (by omega)]
    have arun : ∀ n, 4 ≤ n → n ≤ k - 1 → a (n : Fin k) = a ((4 : ℕ) : Fin k) := by
      intro n h1 h2
      have := arun0 (n - 4) (by omega)
      rwa [show 4 + (n - 4) = n by omega] at this
    have hzn : ∀ j : ℕ, a ((j + 1 : ℕ) : Fin k) =
        xor (z (j : Fin k)) (xor (z ((j + 1 : ℕ) : Fin k)) (z ((j + 2 : ℕ) : Fin k))) := by
      intro j
      have e : ((j + 1 : ℕ) : Fin k) + 1 = ((j + 2 : ℕ) : Fin k) := by
        rw [← c2, ← c1]; ring
      rw [hza]; simp only [Mx1]; rw [cs j, e]
    have hrecZ : ∀ j : ℕ, z ((j + 3 : ℕ) : Fin k) =
        xor (z (j : Fin k)) (xor (a ((j + 1 : ℕ) : Fin k)) (a ((j + 2 : ℕ) : Fin k))) := by
      intro j
      have h1 := hzn j
      have h2 := hzn (j + 1)
      rw [show j + 1 + 1 = j + 2 by omega, show j + 1 + 2 = j + 3 by omega] at h2
      exact bR _ _ _ _ _ _ h1 h2
    have hN : k = 3 * (k / 3) := by omega
    have T3 := telZ1 (fun n => z (n : Fin k))
      (fun j => xor (a ((j + 1 : ℕ) : Fin k)) (a ((j + 2 : ℕ) : Fin k))) k (k / 3) hN
      (fun n => sper z n) hrecZ 0 (by omega) (by
        intro t h1 h2
        beta_reduce
        rw [arun (0 + 3 * t + 1) (by omega) (by omega),
          arun (0 + 3 * t + 2) (by omega) (by omega), Bool.xor_self])
    rw [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl, ha2, Bool.xor_false] at T3
    have T2 := telZ (fun n => z (n : Fin k))
      (fun j => xor (a ((j + 1 : ℕ) : Fin k)) (a ((j + 2 : ℕ) : Fin k))) k (k / 3) hN
      (fun n => sper z n) hrecZ 2 (by omega) (by
        intro t h1 h2
        beta_reduce
        rw [arun (2 + 3 * t + 1) (by omega) (by omega),
          arun (2 + 3 * t + 2) (by omega) (by omega), Bool.xor_self])
    rw [show (2 : ℕ) + 1 = 3 from rfl, show (2 : ℕ) + 2 = 4 from rfl, ha34,
      show 2 + 3 * (k / 3 - 1) + 1 = 0 + k by omega, show 2 + 3 * (k / 3 - 1) + 2 = 1 + k by omega,
      sper a, sper a, ha0, T3] at T2
    exact bX _ T2
  · have hw := gd_zero (m := k) (by omega) _ hGd
    have hDv : ∀ j : ℕ, D (j : Fin k) = v ((j + 1 : ℕ) : Fin k) := by
      intro j
      have := congrFun hw ((j + 1 : ℕ) : Fin k)
      simp only [Rt, cs j] at this
      exact bxf _ _ this
    have hv0 : v ((0 : ℕ) : Fin k) = false := by rw [hvn 0 (by omega)]; exact vF 0 (by omega)
    rcases (by omega : Mk k = 1 ∨ Mk k = 2) with hm | hm
    · have h1 := hDn (k - 2)
      have h2 := hDn (k - 1)
      rw [show k - 2 + 1 = k - 1 by omega, show k - 2 + 2 = 0 + k by omega, sper a, sper P,
        hPn (k - 2) (by omega), hPn (k - 1) (by omega), hPn 0 (by omega),
        decide_eq_true (by omega : Mk k ≤ k - 2), decide_eq_true (by omega : Mk k ≤ k - 1),
        decide_eq_false (by omega : ¬ Mk k ≤ 0), hDv, show k - 2 + 1 = k - 1 by omega,
        hvn (k - 1) (by omega), vF (k - 1) (by omega)] at h1
      rw [show k - 1 + 1 = 0 + k by omega, show k - 1 + 2 = 1 + k by omega, sper a, sper a,
        sper P, sper P, hPn (k - 1) (by omega), hPn 0 (by omega), hPn 1 (by omega),
        decide_eq_true (by omega : Mk k ≤ k - 1), decide_eq_false (by omega : ¬ Mk k ≤ 0),
        decide_eq_true (by omega : Mk k ≤ 1), hDv, show k - 1 + 1 = 0 + k by omega, sper v,
        hv0] at h2
      exact bM1 _ _ _ _ h1 h2
    · have h2 := hDn (k - 1)
      rw [show k - 1 + 1 = 0 + k by omega, show k - 1 + 2 = 1 + k by omega, sper a, sper a,
        sper P, sper P, hPn (k - 1) (by omega), hPn 0 (by omega), hPn 1 (by omega),
        decide_eq_true (by omega : Mk k ≤ k - 1), decide_eq_false (by omega : ¬ Mk k ≤ 0),
        decide_eq_false (by omega : ¬ Mk k ≤ 1), hDv, show k - 1 + 1 = 0 + k by omega, sper v,
        hv0, bW0] at h2
      exact Bool.false_ne_true h2

theorem inj4 (h4 : 4 ≤ k) (u x y : Fin k → Bool) (h1 : Row u x = Row u y)
    (h2 : Row (Ad u Vv) x = Row (Ad u Vv) y) : x = y := by
  have hlin : ∀ w, Mx1 (Ad (Ad u Vv) (Rt w)) = Ad (Mx1 (Ad u (Rt w))) (Mx1 Vv) := by
    intro w; funext i; exact bLin _ _ _ _ _ _ _ _ _
  have hc := core h4 (Mx1 Vv) Vv (Mx1 (Ad u (Rt x))) (Mx1 (Ad u (Rt y))) (Ad x y) (Ad u (Rt x))
    (fun _ => rfl) (fun i => if_neg (by omega))
    (fun n hn => by rw [pat h4, Fin.val_natCast, Nat.mod_eq_of_lt hn])
    (fun _ => rfl)
    (fun i => b4' _ _ _ _ (congrFun h1 i))
    (fun i => by
      have := congrFun h2 i
      simp only [Row, hlin] at this
      exact b4' _ _ _ _ this)
    (fun i => bBD _ _ _ _ _ _ _ _ _)
  funext i
  exact bxf _ _ (hc i)

theorem part2 (hk2 : k = 2 ∨ 4 ≤ k) :
    (∀ i : Fin k, Mx1 Vv i = if k = 2 then decide (i.val = 1) else decide (Mk k ≤ i.val)) ∧
    ∀ u, Function.Injective (fun x : Fin k → Bool => (Row u x, Row (Ad u Vv) x)) := by
  rcases hk2 with rfl | h4
  · exact ⟨k2pat, k2inj⟩
  · refine ⟨fun i => by rw [if_neg (by omega)]; exact pat h4 i, fun u x y h => ?_⟩
    simp only [Prod.mk.injEq] at h
    exact inj4 h4 u x y h.1 h.2

end core

end PEqualNP.Outside.L_meta_41629

open Fin.CommRing PEqualNP.Outside.L_meta_41629 in
theorem PEqualNP.Outside.L_meta_41629 : ∀ (k : Nat) (hk : 0 < k),
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let mix := fun (d : Nat) (x : W) (i : Fin k) =>
    xor (x (ix (i.val+k-d % k))) (xor (x i) (x (ix (i.val+d))))
  let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
  let chi := fun (r : W) (i : Fin k) => xor (r i) (!(r (ix (i.val+1))) && r (ix (i.val+2)))
  let row := fun (name x : W) => add (chi (mix 1 (add name (rot 1 x)))) x
  let m := 1 + (k-1) % 3
  (∀ q : Nat, (∃ names : Fin q → W, Function.Injective (fun x : W => fun j : Fin q => row (names j) x)) ↔
    k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q) ∧
  ((k = 2 ∨ 4 ≤ k) → ∃ v : W,
    (∀ i : Fin k, mix 1 v i = (if k = 2 then decide (i.val = 1) else decide (m ≤ i.val))) ∧
    ∀ u : W, Function.Injective (fun x : W => (row u x, row (add u v) x))) := by
  intro k hk W ix add mix rot chi row m
  have : NeZero k := ⟨hk.ne'⟩
  have hrow : ∀ n x, row n x = Row n x := by
    intro n x; funext i
    simp only [row, add, chi, mix, rot, ix, ixN, castA, castS, Row, Ch, Mx1, Rt, Ad, Nat.cast_one,
      Nat.cast_ofNat]
  have hmix : ∀ v i, mix 1 v i = Mx1 v i := by
    intro v i; simp only [mix, ix, ixN, castA, castS, Mx1, Nat.cast_one]
  refine ⟨?_, ?_⟩
  · intro q
    constructor
    · rintro ⟨names, hinj⟩
      have hcol : ∀ x y : W, (∀ j, Row (names j) x = Row (names j) y) → x = y := by
        intro x y h; apply hinj; funext j; simp only [hrow]; exact h j
      refine ⟨?_, ?_, ?_⟩
      · intro h1; subst h1
        have := hcol (fun _ => false) (fun _ => true) (fun j => k1col (names j))
        exact absurd (congrFun this 0) (by decide)
      · intro h3; subst h3
        have := hcol (fun _ => false) (fun _ => true) (fun j => k3col (names j))
        exact absurd (congrFun this 0) (by decide)
      · by_contra hq
        rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
        · have := hcol (fun _ => false) (fun _ => true) (fun j => j.elim0)
          exact absurd (congrFun this ⟨0, hk⟩) (by decide)
        · have := hcol (fun j => names 0 (j + 1)) (fun j => !(names 0 (j + 1)))
            (fun j => by rw [Fin.fin_one_eq_zero j]; exact q1col (names 0))
          exact bnn _ (congrFun this 0)
    · rintro ⟨h1, h3, hq⟩
      obtain ⟨-, hinj⟩ := part2 (k := k) (by omega)
      refine ⟨fun j => if j.val = 0 then (fun _ => false) else Ad (fun _ => false) Vv, ?_⟩
      intro x y hxy
      have e0' : row (fun _ => false) x = row (fun _ => false) y := congrFun hxy ⟨0, by omega⟩
      have e1' : row (Ad (fun _ => false) Vv) x = row (Ad (fun _ => false) Vv) y :=
        congrFun hxy ⟨1, by omega⟩
      have e0 := (hrow _ _).symm.trans (e0'.trans (hrow _ _))
      have e1 := (hrow _ _).symm.trans (e1'.trans (hrow _ _))
      exact hinj (fun _ => false) (Prod.ext e0 e1)
  · intro hk2
    obtain ⟨hpat, hinj⟩ := part2 (k := k) hk2
    refine ⟨Vv, fun i => by rw [hmix]; exact hpat i, fun u x y h => hinj u ?_⟩
    simp only [hrow] at h
    exact h
