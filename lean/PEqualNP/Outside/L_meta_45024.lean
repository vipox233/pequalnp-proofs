import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45024_aux

variable {k : ℕ}

def ix (hk : 0 < k) (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩
def ad (u v : Fin k → Bool) : Fin k → Bool := fun i => xor (u i) (v i)
def zz : Fin k → Bool := fun _ => false
def rot (hk : 0 < k) (s : ℕ) (w : Fin k → Bool) : Fin k → Bool :=
  fun i => w (ix hk (i.val+k-s % k))
def mix (hk : 0 < k) (d : ℕ) (w : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (w (ix hk (i.val+k-d % k))) (xor (w i) (w (ix hk (i.val+d))))
def rb (hk : 0 < k) (col : Bool) (u x : Fin k → Bool) (i : Fin k) : Bool :=
  let d := if col then 2 else 1
  let R := mix hk d (ad u (rot hk (if col then 3 else 1) x))
  xor (rot hk (if col then 4 else 0) x i)
    (xor (R i) (!(R (ix hk (i.val+1))) && R (ix hk (i.val+2))))
def dl (hk : 0 < k) (col : Bool) (u v x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (rb hk col u x i) (rb hk col (ad u v) x i)
def inK (hk : 0 < k) (N D : Fin k → Bool) : Prop :=
  ∀ i : Fin k, (N (ix hk (i.val+2)) && D (ix hk (i.val+1))) =
    (N (ix hk (i.val+1)) && D (ix hk (i.val+2)))
def colc (hk : 0 < k) (c : Fin k) (N T : Fin k → Bool) : Prop :=
  (N (ix hk (c.val+2)) && T (ix hk (c.val+1))) = (N (ix hk (c.val+1)) && T (ix hk (c.val+2)))
def isGap (hk : 0 < k) (N : Fin k → Bool) : Prop :=
  ∃ a : Fin k, (∀ i : Fin k, N i = decide (i ≠ a)) ∨
    (∀ i : Fin k, N i = decide (i ≠ a ∧ i ≠ ix hk (a.val+1)))

theorem ad_zz (x : Fin k → Bool) : ad x zz = x := by funext i; simp [ad, zz]
theorem ad_eq_zz (x y : Fin k → Bool) (h : ad x y = zz) : x = y := by
  funext i
  have := congrFun h i
  simpa [ad, zz] using this

theorem bkey : ∀ e f r0 r1 r2 s0 s1 s2 n0 n1 n2 : Bool,
    (xor (xor e (xor r0 (!r1 && r2))) (xor e (xor (xor r0 n0) (!(xor r1 n1) && xor r2 n2))) =
     xor (xor f (xor s0 (!s1 && s2))) (xor f (xor (xor s0 n0) (!(xor s1 n1) && xor s2 n2)))) ↔
    ((n2 && xor r1 s1) = (n1 && xor r2 s2)) := by decide

theorem b9 : ∀ u1 v1 r1 u2 v2 r2 u3 v3 r3 : Bool,
    xor (xor (xor u1 v1) r1) (xor (xor (xor u2 v2) r2) (xor (xor u3 v3) r3)) =
    xor (xor (xor u1 r1) (xor (xor u2 r2) (xor u3 r3))) (xor v1 (xor v2 v3)) := by decide

theorem b9' : ∀ u1 x1 y1 u2 x2 y2 u3 x3 y3 : Bool,
    xor (xor x1 y1) (xor (xor x2 y2) (xor x3 y3)) =
    xor (xor (xor u1 x1) (xor (xor u2 x2) (xor u3 x3)))
      (xor (xor u1 y1) (xor (xor u2 y2) (xor u3 y3))) := by decide

theorem mix_ad (hk : 0 < k) (d : ℕ) (a b : Fin k → Bool) :
    mix hk d (ad a b) = ad (mix hk d a) (mix hk d b) := by
  funext i
  show xor (xor _ _) (xor (xor _ _) (xor _ _)) = xor (xor _ (xor _ _)) (xor _ (xor _ _))
  generalize a (ix hk (i.val+k-d % k)) = a1
  generalize b (ix hk (i.val+k-d % k)) = b1
  generalize a (ix hk (i.val+d)) = a3
  generalize b (ix hk (i.val+d)) = b3
  cases a1 <;> cases b1 <;> cases a3 <;> cases b3 <;> cases a i <;> cases b i <;> rfl

theorem dl_iff (hk : 0 < k) (d s e : ℕ) (u v x y : Fin k → Bool) (i : Fin k) :
    (xor (xor (rot hk e x i) (xor (mix hk d (ad u (rot hk s x)) i)
        (!(mix hk d (ad u (rot hk s x)) (ix hk (i.val+1))) &&
          mix hk d (ad u (rot hk s x)) (ix hk (i.val+2)))))
      (xor (rot hk e x i) (xor (mix hk d (ad (ad u v) (rot hk s x)) i)
        (!(mix hk d (ad (ad u v) (rot hk s x)) (ix hk (i.val+1))) &&
          mix hk d (ad (ad u v) (rot hk s x)) (ix hk (i.val+2))))) =
     xor (xor (rot hk e y i) (xor (mix hk d (ad u (rot hk s y)) i)
        (!(mix hk d (ad u (rot hk s y)) (ix hk (i.val+1))) &&
          mix hk d (ad u (rot hk s y)) (ix hk (i.val+2)))))
      (xor (rot hk e y i) (xor (mix hk d (ad (ad u v) (rot hk s y)) i)
        (!(mix hk d (ad (ad u v) (rot hk s y)) (ix hk (i.val+1))) &&
          mix hk d (ad (ad u v) (rot hk s y)) (ix hk (i.val+2)))))) ↔
    ((mix hk d v (ix hk (i.val+2)) && mix hk d (rot hk s (ad x y)) (ix hk (i.val+1))) =
     (mix hk d v (ix hk (i.val+1)) && mix hk d (rot hk s (ad x y)) (ix hk (i.val+2)))) := by
  have h1 : ∀ x : Fin k → Bool, mix hk d (ad (ad u v) (rot hk s x)) =
      ad (mix hk d (ad u (rot hk s x))) (mix hk d v) := by
    intro x; funext j; exact b9 _ _ _ _ _ _ _ _ _
  have h2 : mix hk d (rot hk s (ad x y)) =
      ad (mix hk d (ad u (rot hk s x))) (mix hk d (ad u (rot hk s y))) := by
    funext j; exact b9' _ _ _ _ _ _ _ _ _
  rw [h1, h1, h2]
  exact bkey _ _ _ _ _ _ _ _ _ _ _

theorem good_iff (hk : 0 < k) (u v : Fin k → Bool) :
    (∃ c : Fin k, Function.Injective
      (fun x : Fin k → Bool => (dl hk false u v x, dl hk true u v x c))) ↔
    ∃ c : Fin k, ∀ t : Fin k → Bool, inK hk (mix hk 1 v) (mix hk 1 (rot hk 1 t)) →
      colc hk c (mix hk 2 v) (mix hk 2 (rot hk 3 t)) → t = zz := by
  constructor
  · rintro ⟨c, hI⟩
    refine ⟨c, fun t h1 h2 => ?_⟩
    apply hI
    refine Prod.ext ?_ ?_
    · funext i
      refine (dl_iff hk 1 1 0 u v t zz i).2 ?_
      rw [ad_zz]; exact h1 i
    · refine (dl_iff hk 2 3 4 u v t zz c).2 ?_
      rw [ad_zz]; exact h2
  · rintro ⟨c, h⟩
    refine ⟨c, fun x y hxy => ?_⟩
    simp only [Prod.mk.injEq] at hxy
    exact ad_eq_zz x y (h (ad x y)
      (fun i => (dl_iff hk 1 1 0 u v x y i).1 (congrFun hxy.1 i))
      ((dl_iff hk 2 3 4 u v x y c).1 hxy.2))

theorem ix_add (hk : 0 < k) (n m : ℕ) : ix hk ((ix hk n).val + m) = ix hk (n+m) :=
  Fin.ext (Nat.mod_add_mod n k m)
theorem ix_self (hk : 0 < k) (i : Fin k) : ix hk i.val = i := Fin.ext (Nat.mod_eq_of_lt i.2)
theorem ix_k (hk : 0 < k) (n : ℕ) : ix hk (n + k) = ix hk n := Fin.ext (Nat.add_mod_right n k)
theorem ix_pred (hk : 0 < k) (d : ℕ) (hd : d < k) (n : ℕ) :
    ix hk ((ix hk (n+d)).val + k - d % k) = ix hk n := by
  apply Fin.ext
  show ((n+d)%k + k - d%k)%k = n%k
  rw [Nat.mod_eq_of_lt hd, Nat.add_sub_assoc hd.le, Nat.mod_add_mod,
    show n + d + (k-d) = n + k by omega, Nat.add_mod_right]
theorem mix_ix (hk : 0 < k) (d : ℕ) (hd : d < k) (w : Fin k → Bool) (n : ℕ) :
    mix hk d w (ix hk (n+d)) =
      xor (w (ix hk n)) (xor (w (ix hk (n+d))) (w (ix hk (n+d+d)))) := by
  show xor (w (ix hk ((ix hk (n+d)).val + k - d%k)))
    (xor (w (ix hk (n+d))) (w (ix hk ((ix hk (n+d)).val + d)))) = _
  rw [ix_pred hk d hd, ix_add]
theorem rot_ix (hk : 0 < k) (s : ℕ) (hs : s < k) (w : Fin k → Bool) (n : ℕ) :
    rot hk s w (ix hk (n+s)) = w (ix hk n) := by
  show w (ix hk ((ix hk (n+s)).val + k - s%k)) = _
  rw [ix_pred hk s hs]
theorem ext_ix (hk : 0 < k) (c : ℕ) (f g : Fin k → Bool)
    (h : ∀ n, f (ix hk (n+c)) = g (ix hk (n+c))) : f = g := by
  funext i
  have e : ix hk (i.val + (k-1)*c + c) = i := by
    apply Fin.ext
    show (i.val + (k-1)*c + c) % k = i.val
    have : i.val + (k-1)*c + c = i.val + k*c := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt i.2]
  rw [← e]; exact h _

theorem mix1_ker (hk : 0 < k) (h7 : 7 ≤ k) (h3 : ¬ 3 ∣ k) (w : Fin k → Bool)
    (h : mix hk 1 w = zz) : w = zz := by
  have e : ∀ n, xor (w (ix hk n)) (xor (w (ix hk (n+1))) (w (ix hk (n+1+1)))) = false := by
    intro n; rw [← mix_ix hk 1 (by omega) w n, h]; rfl
  have p3 : ∀ n, w (ix hk (n+3)) = w (ix hk n) := by
    intro n
    have a := e n
    have b := e (n+1)
    show w (ix hk (n+1+1+1)) = _
    revert a b
    generalize w (ix hk n) = a0
    generalize w (ix hk (n+1)) = a1
    generalize w (ix hk (n+1+1)) = a2
    generalize w (ix hk (n+1+1+1)) = a3
    revert a0 a1 a2 a3; decide
  have pj : ∀ j n, w (ix hk (n+3*j)) = w (ix hk n) := by
    intro j
    induction j with
    | zero => intro n; rfl
    | succ j ih => intro n; rw [show n + 3*(j+1) = n+3*j+3 by ring, p3, ih]
  have p1 : ∀ n, w (ix hk (n+1)) = w (ix hk n) := by
    intro n
    have hm : k % 3 = 1 ∨ k % 3 = 2 := by
      have := Nat.dvd_iff_mod_eq_zero.not.1 h3
      omega
    have : ∃ j, 3*j = k+1 ∨ 3*j = 2*k+1 := by
      rcases hm with hm | hm
      · exact ⟨(2*k+1)/3, Or.inr (by omega)⟩
      · exact ⟨(k+1)/3, Or.inl (by omega)⟩
    obtain ⟨j, hj | hj⟩ := this
    · have := pj j n
      rw [hj, show n + (k+1) = n+1+k by omega, ix_k] at this
      exact this
    · have := pj j n
      rw [hj, show n + (2*k+1) = n+1+k+k by omega, ix_k, ix_k] at this
      exact this
  have pc : ∀ n, w (ix hk n) = w (ix hk 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [p1, ih]
  have z : w (ix hk 0) = false := by
    have := e 0
    rw [pc (0+1), pc (0+1+1)] at this
    revert this
    generalize w (ix hk 0) = a
    revert a; decide
  funext i
  rw [← ix_self hk i, pc, z]; rfl

theorem mix1_inj (hk : 0 < k) (h7 : 7 ≤ k) (h3 : ¬ 3 ∣ k) : Function.Injective (mix hk 1) := by
  intro a b h
  apply ad_eq_zz
  apply mix1_ker hk h7 h3
  rw [mix_ad, h]
  funext i; simp [ad, zz]

theorem L_surj (hk : 0 < k) (h7 : 7 ≤ k) (h3 : ¬ 3 ∣ k) (D : Fin k → Bool) :
    ∃ t, mix hk 1 (rot hk 1 t) = D := by
  obtain ⟨y, rfl⟩ := Finite.surjective_of_injective (mix1_inj hk h7 h3) D
  refine ⟨fun i => y (ix hk (i.val+1)), congrArg _ ?_⟩
  apply ext_ix hk 1
  intro n
  rw [rot_ix hk 1 (by omega)]
  show y (ix hk ((ix hk n).val + 1)) = _
  rw [ix_add]

theorem succ_mod_cases (hk : 0 < k) (n : ℕ) :
    ((n+1)%k = n%k+1 ∧ n%k+1 < k) ∨ ((n+1)%k = 0 ∧ n%k+1 = k) := by
  have h := Nat.mod_lt n hk
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge (n%k+1) k with h1 | h1
  · left
    have h2 : 1 < k := by omega
    rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h1]; exact ⟨rfl, h1⟩
  · right
    have h2 : n%k+1 = k := by omega
    rcases Nat.lt_or_ge 1 k with h3 | h3
    · rw [Nat.mod_eq_of_lt h3, h2, Nat.mod_self]; exact ⟨rfl, rfl⟩
    · have : k = 1 := by omega
      subst this; simp [Nat.mod_one]

theorem inK_iff (hk : 0 < k) (N D : Fin k → Bool) : inK hk N D ↔
    ∀ n : ℕ, (N (ix hk (n+1)) && D (ix hk n)) = (N (ix hk n) && D (ix hk (n+1))) := by
  constructor
  · intro h n
    have := h (ix hk (n + (k-1)))
    rw [ix_add, ix_add, show n + (k-1) + 2 = n+1+k by omega, show n + (k-1) + 1 = n+k by omega,
      ix_k, ix_k] at this
    exact this
  · intro h i
    exact h (i.val+1)

theorem inK_ad (hk : 0 < k) (N D1 D2 : Fin k → Bool) (h1 : inK hk N D1) (h2 : inK hk N D2) :
    inK hk N (ad D1 D2) := by
  intro i
  have a := h1 i
  have b := h2 i
  show (_ && xor _ _) = (_ && xor _ _)
  revert a b
  generalize N (ix hk (i.val+2)) = n2
  generalize N (ix hk (i.val+1)) = n1
  generalize D1 (ix hk (i.val+2)) = d2
  generalize D1 (ix hk (i.val+1)) = d1
  generalize D2 (ix hk (i.val+2)) = e2
  generalize D2 (ix hk (i.val+1)) = e1
  revert n1 n2 d1 d2 e1 e2; decide

theorem twoA (hk : 0 < k) (N A : Fin k → Bool)
    (hA : ∀ n, N (ix hk n) = true → N (ix hk (n+1)) = true → A (ix hk n) = A (ix hk (n+1)))
    (p q : Fin k) (hp : N p = true) (hq : N q = true) (hpq : A p ≠ A q) :
    ∃ D1 D2, inK hk N D1 ∧ inK hk N D2 ∧ D1 ≠ zz ∧ D2 ≠ zz ∧ D1 ≠ D2 := by
  have key : ∀ (p q : Fin k), N p = true → N q = true → A p = true → A q = false →
      ∃ D1 D2, inK hk N D1 ∧ inK hk N D2 ∧ D1 ≠ zz ∧ D2 ≠ zz ∧ D1 ≠ D2 := by
    intro p q hp hq hAp hAq
    refine ⟨fun i => N i && A i, fun i => N i && !A i, ?_, ?_, ?_, ?_, ?_⟩
    · rw [inK_iff]
      intro n
      have := hA n
      revert this
      show _ → (_ && (_ && _)) = (_ && (_ && _))
      generalize N (ix hk n) = n0
      generalize N (ix hk (n+1)) = n1
      generalize A (ix hk n) = a0
      generalize A (ix hk (n+1)) = a1
      revert n0 n1 a0 a1; decide
    · rw [inK_iff]
      intro n
      have := hA n
      revert this
      show _ → (_ && (_ && !_)) = (_ && (_ && !_))
      generalize N (ix hk n) = n0
      generalize N (ix hk (n+1)) = n1
      generalize A (ix hk n) = a0
      generalize A (ix hk (n+1)) = a1
      revert n0 n1 a0 a1; decide
    · intro h; have := congrFun h p; simp [hp, hAp, zz] at this
    · intro h; have := congrFun h q; simp [hq, hAq, zz] at this
    · intro h; have := congrFun h p; simp [hp, hAp] at this
  cases hAp : A p <;> cases hAq : A q
  · exact absurd (hAp.trans hAq.symm) hpq
  · exact key q p hq hp hAq hAp
  · exact key p q hp hq hAp hAq
  · exact absurd (hAp.trans hAq.symm) hpq

theorem interval (hk : 0 < k) (N : Fin k → Bool) (a b : Fin k) (ha : N a = false)
    (hb : N b = false) (n : ℕ) (_h1 : N (ix hk n) = true) (h2 : N (ix hk (n+1)) = true) :
    (fun i : Fin k => decide (min a.val b.val ≤ i.val ∧ i.val < max a.val b.val)) (ix hk n) =
    (fun i : Fin k => decide (min a.val b.val ≤ i.val ∧ i.val < max a.val b.val))
      (ix hk (n+1)) := by
  by_contra hne
  have hy : (n+1)%k = a.val ∨ (n+1)%k = b.val := by
    by_contra hc
    apply hne
    show decide (min a.val b.val ≤ n%k ∧ n%k < max a.val b.val) =
      decide (min a.val b.val ≤ (n+1)%k ∧ (n+1)%k < max a.val b.val)
    rw [decide_eq_decide]
    have := succ_mod_cases hk n
    have := a.2
    have := b.2
    have := Nat.mod_lt n hk
    omega
  rcases hy with hy | hy
  · have : ix hk (n+1) = a := Fin.ext hy
    rw [this, ha] at h2; exact Bool.false_ne_true h2
  · have : ix hk (n+1) = b := Fin.ext hy
    rw [this, hb] at h2; exact Bool.false_ne_true h2

theorem deep (hk : 0 < k) (N : Fin k → Bool) (m : ℕ) (h0 : N (ix hk m) = false)
    (h1 : N (ix hk (m+1)) = false) (h2 : N (ix hk (m+1+1)) = false) (q : Fin k)
    (hq : N q = true) :
    ∃ D1 D2, inK hk N D1 ∧ inK hk N D2 ∧ D1 ≠ zz ∧ D2 ≠ zz ∧ D1 ≠ D2 := by
  refine ⟨fun i => decide (i = ix hk (m+1)), N, ?_, ?_, ?_, ?_, ?_⟩
  · rw [inK_iff]
    intro n
    show (_ && decide _) = (_ && decide _)
    by_cases e1 : ix hk n = ix hk (m+1)
    · have e2 : ix hk (n+1) = ix hk (m+1+1) := by rw [← ix_add, e1, ix_add]
      rw [e1, e2, h1, h2]; rfl
    · by_cases e2 : ix hk (n+1) = ix hk (m+1)
      · have e3 : ix hk n = ix hk m :=
          Fin.ext (Nat.ModEq.add_right_cancel' 1 (Fin.ext_iff.1 e2))
        rw [e2, e3, h0, h1]; rfl
      · simp [e1, e2]
  · intro i; exact Bool.and_comm _ _
  · intro h; have := congrFun h (ix hk (m+1)); simp [zz] at this
  · intro h; have := congrFun h q; simp [hq, zz] at this
  · intro h; have := congrFun h (ix hk (m+1)); simp [h1] at this

theorem twoD (hk : 0 < k) (h7 : 7 ≤ k) (N : Fin k → Bool) (hno : ¬ ∀ i, N i = true)
    (hng : ¬ isGap hk N) :
    ∃ D1 D2, inK hk N D1 ∧ inK hk N D2 ∧ D1 ≠ zz ∧ D2 ≠ zz ∧ D1 ≠ D2 := by
  by_cases hz : ∃ q, N q = true
  swap
  · have hN : ∀ i, N i = false := fun i => by
      cases h : N i
      · rfl
      · exact absurd ⟨i, h⟩ hz
    refine ⟨fun _ => true, fun i => decide (i.val = 0), ?_, ?_, ?_, ?_, ?_⟩
    · intro i; rw [hN, hN]
    · intro i; rw [hN, hN]; rfl
    · intro h; have := congrFun h ⟨0, hk⟩; simp [zz] at this
    · intro h; have := congrFun h ⟨0, hk⟩; simp [zz] at this
    · intro h; have := congrFun h ⟨1, by omega⟩; simp at this
  obtain ⟨q, hq⟩ := hz
  have hdesc : ∃ m, N (ix hk m) = true ∧ N (ix hk (m+1)) = false := by
    by_contra hc
    apply hno
    have hall : ∀ n, N (ix hk (q.val + n)) = true := by
      intro n
      induction n with
      | zero => rw [Nat.add_zero, ix_self]; exact hq
      | succ n ih =>
        cases h : N (ix hk (q.val + (n+1)))
        · exact absurd ⟨q.val + n, ih, h⟩ hc
        · rfl
    intro i
    have := hall (i.val + k - q.val)
    rw [show q.val + (i.val + k - q.val) = i.val + k by have := q.2; omega, ix_k, ix_self] at this
    exact this
  obtain ⟨m, hm0, hm1⟩ := hdesc
  have x0 := Nat.mod_lt m hk
  have s0 := succ_mod_cases hk m
  have s1 := succ_mod_cases hk (m+1)
  have s2 := succ_mod_cases hk (m+1+1)
  have hne : ∀ (b : Fin k) (n : ℕ), N b ≠ N (ix hk n) → b.val ≠ n % k := by
    intro b n h e
    exact h (congrArg N (Fin.ext e))
  cases hm2 : N (ix hk (m+1+1))
  · cases hm3 : N (ix hk (m+1+1+1))
    · exact deep hk N (m+1) hm1 hm2 hm3 _ hm0
    · have hb : ∃ b, N b = false ∧ b ≠ ix hk (m+1) ∧ b ≠ ix hk (m+1+1) := by
        by_contra hc
        apply hng
        refine ⟨ix hk (m+1), Or.inr (fun i => ?_)⟩
        rw [ix_add]
        by_cases e1 : i = ix hk (m+1)
        · rw [e1, hm1]; simp
        · by_cases e2 : i = ix hk (m+1+1)
          · rw [e2, hm2]; simp
          · cases h : N i
            · exact absurd ⟨i, h, e1, e2⟩ hc
            · simp [e1, e2]
      obtain ⟨b, hb0, hb1, hb2⟩ := hb
      refine twoA hk N (fun i : Fin k => decide (min (ix hk (m+1)).val b.val ≤ i.val ∧ i.val < max (ix hk (m+1)).val b.val))
        (interval hk N (ix hk (m+1)) b hm1 hb0) (ix hk (m+1+1+1)) (ix hk m)
        hm3 hm0 ?_
      have b0 := hne b m (by rw [hb0, hm0]; simp)
      have b3 := hne b (m+1+1+1) (by rw [hb0, hm3]; simp)
      have b1 : b.val ≠ (m+1)%k := fun e => hb1 (Fin.ext e)
      have b2 : b.val ≠ (m+1+1)%k := fun e => hb2 (Fin.ext e)
      have := b.2
      show decide (min ((m+1)%k) b.val ≤ (m+1+1+1)%k ∧ (m+1+1+1)%k < max ((m+1)%k) b.val) ≠
        decide (min ((m+1)%k) b.val ≤ m%k ∧ m%k < max ((m+1)%k) b.val)
      rw [Ne, decide_eq_decide]
      omega
  · have hb : ∃ b, N b = false ∧ b ≠ ix hk (m+1) := by
      by_contra hc
      apply hng
      refine ⟨ix hk (m+1), Or.inl (fun i => ?_)⟩
      by_cases e1 : i = ix hk (m+1)
      · rw [e1, hm1]; simp
      · cases h : N i
        · exact absurd ⟨i, h, e1⟩ hc
        · simp [e1]
    obtain ⟨b, hb0, hb1⟩ := hb
    refine twoA hk N (fun i : Fin k => decide (min (ix hk (m+1)).val b.val ≤ i.val ∧ i.val < max (ix hk (m+1)).val b.val))
        (interval hk N (ix hk (m+1)) b hm1 hb0) (ix hk (m+1+1)) (ix hk m)
      hm2 hm0 ?_
    have b0 := hne b m (by rw [hb0, hm0]; simp)
    have b2 := hne b (m+1+1) (by rw [hb0, hm2]; simp)
    have b1 : b.val ≠ (m+1)%k := fun e => hb1 (Fin.ext e)
    have := b.2
    show decide (min ((m+1)%k) b.val ≤ (m+1+1)%k ∧ (m+1+1)%k < max ((m+1)%k) b.val) ≠
      decide (min ((m+1)%k) b.val ≤ m%k ∧ m%k < max ((m+1)%k) b.val)
    rw [Ne, decide_eq_decide]
    omega

theorem bphi : ∀ a b : Bool, (a = b) ↔ xor a b = false := by decide

theorem core_mp (hk : 0 < k) (h7 : 7 ≤ k) (h3 : ¬ 3 ∣ k) (v : Fin k → Bool)
    (h : ∃ c : Fin k, ∀ t : Fin k → Bool, inK hk (mix hk 1 v) (mix hk 1 (rot hk 1 t)) →
      colc hk c (mix hk 2 v) (mix hk 2 (rot hk 3 t)) → t = zz) : isGap hk (mix hk 1 v) := by
  obtain ⟨c, h⟩ := h
  by_contra hng
  by_cases hno : ∀ i, mix hk 1 v i = true
  · have hv : v = fun _ => true := by
      apply mix1_inj hk h7 h3
      funext i; rw [hno i]; rfl
    subst hv
    have := h (fun _ => true) (fun i => rfl) rfl
    have := congrFun this ⟨0, hk⟩
    simp [zz] at this
  · obtain ⟨D1, D2, k1, k2, n1, n2, n12⟩ := twoD hk h7 _ hno hng
    obtain ⟨t1, rfl⟩ := L_surj hk h7 h3 D1
    obtain ⟨t2, rfl⟩ := L_surj hk h7 h3 D2
    have z1 : t1 ≠ zz := by rintro rfl; exact n1 (by funext i; rfl)
    have z2 : t2 ≠ zz := by rintro rfl; exact n2 (by funext i; rfl)
    have z12 : t1 ≠ t2 := by rintro rfl; exact n12 rfl
    by_cases c1 : colc hk c (mix hk 2 v) (mix hk 2 (rot hk 3 t1))
    · exact z1 (h t1 k1 c1)
    by_cases c2 : colc hk c (mix hk 2 v) (mix hk 2 (rot hk 3 t2))
    · exact z2 (h t2 k2 c2)
    apply z12
    apply ad_eq_zz
    apply h
    · have e : mix hk 1 (rot hk 1 (ad t1 t2)) =
          ad (mix hk 1 (rot hk 1 t1)) (mix hk 1 (rot hk 1 t2)) := mix_ad hk 1 _ _
      rw [e]; exact inK_ad hk _ _ _ k1 k2
    · have e : mix hk 2 (rot hk 3 (ad t1 t2)) =
          ad (mix hk 2 (rot hk 3 t1)) (mix hk 2 (rot hk 3 t2)) := mix_ad hk 2 _ _
      unfold colc at c1 c2 ⊢
      rw [e]
      rw [bphi] at c1 c2 ⊢
      revert c1 c2
      show _ → _ → xor (_ && xor _ _) (_ && xor _ _) = false
      generalize mix hk 2 v (ix hk (c.val+2)) = n2
      generalize mix hk 2 v (ix hk (c.val+1)) = n1
      generalize mix hk 2 (rot hk 3 t1) (ix hk (c.val+1)) = a1
      generalize mix hk 2 (rot hk 3 t1) (ix hk (c.val+2)) = a2
      generalize mix hk 2 (rot hk 3 t2) (ix hk (c.val+1)) = b1
      generalize mix hk 2 (rot hk 3 t2) (ix hk (c.val+2)) = b2
      revert n1 n2 a1 a2 b1 b2; decide

theorem mm (hk : 0 < k) (h : 2 < k) (v : Fin k → Bool) (n : ℕ) :
    mix hk 2 v (ix hk (n+1+1)) = xor (mix hk 1 v (ix hk (n+1)))
      (xor (mix hk 1 v (ix hk (n+1+1))) (mix hk 1 v (ix hk (n+1+1+1)))) := by
  have e : mix hk 2 v (ix hk (n+1+1)) =
      xor (v (ix hk n)) (xor (v (ix hk (n+1+1))) (v (ix hk (n+1+1+1+1)))) := mix_ix hk 2 h v n
  rw [e, mix_ix hk 1 (by omega) v n, mix_ix hk 1 (by omega) v (n+1),
    mix_ix hk 1 (by omega) v (n+1+1)]
  generalize v (ix hk n) = a0
  generalize v (ix hk (n+1)) = a1
  generalize v (ix hk (n+1+1)) = a2
  generalize v (ix hk (n+1+1+1)) = a3
  generalize v (ix hk (n+1+1+1+1)) = a4
  revert a0 a1 a2 a3 a4; decide

theorem TT (hk : 0 < k) (h : 3 < k) (t : Fin k → Bool) (m : ℕ) :
    mix hk 2 (rot hk 3 t) (ix hk (m+1+1+1+1+1)) = mix hk 2 (rot hk 1 t) (ix hk (m+1+1+1)) := by
  have e1 : mix hk 2 (rot hk 3 t) (ix hk (m+1+1+1+1+1)) =
      xor (rot hk 3 t (ix hk (m+3))) (xor (rot hk 3 t (ix hk (m+1+1+3)))
        (rot hk 3 t (ix hk (m+1+1+1+1+3)))) := mix_ix hk 2 (by omega) _ (m+3)
  have e2 : mix hk 2 (rot hk 1 t) (ix hk (m+1+1+1)) =
      xor (rot hk 1 t (ix hk (m+1))) (xor (rot hk 1 t (ix hk (m+1+1+1)))
        (rot hk 1 t (ix hk (m+1+1+1+1+1)))) := mix_ix hk 2 (by omega) _ (m+1)
  rw [e1, e2, rot_ix hk 3 h t m, rot_ix hk 3 h t (m+1+1), rot_ix hk 3 h t (m+1+1+1+1),
    rot_ix hk 1 (by omega) t m, rot_ix hk 1 (by omega) t (m+1+1),
    rot_ix hk 1 (by omega) t (m+1+1+1+1)]

theorem colfail (hk : 0 < k) (h7 : 7 ≤ k) (v t : Fin k → Bool) (hv : rot hk 1 t = v) (m : ℕ)
    (hc : colc hk (ix hk (m+1+1+1+1)) (mix hk 2 v) (mix hk 2 (rot hk 3 t))) :
    ((xor (mix hk 1 v (ix hk (m+1+1+1+1+1))) (xor (mix hk 1 v (ix hk (m+1+1+1+1+1+1)))
        (mix hk 1 v (ix hk (m+1+1+1+1+1+1+1)))) &&
      xor (mix hk 1 v (ix hk (m+1+1))) (xor (mix hk 1 v (ix hk (m+1+1+1)))
        (mix hk 1 v (ix hk (m+1+1+1+1))))) =
     (xor (mix hk 1 v (ix hk (m+1+1+1+1))) (xor (mix hk 1 v (ix hk (m+1+1+1+1+1)))
        (mix hk 1 v (ix hk (m+1+1+1+1+1+1)))) &&
      xor (mix hk 1 v (ix hk (m+1+1+1))) (xor (mix hk 1 v (ix hk (m+1+1+1+1)))
        (mix hk 1 v (ix hk (m+1+1+1+1+1)))))) := by
  unfold colc at hc
  rw [ix_add, ix_add] at hc
  have hc' : (mix hk 2 v (ix hk (m+1+1+1+1+1+1)) &&
      mix hk 2 (rot hk 3 t) (ix hk (m+1+1+1+1+1))) =
      (mix hk 2 v (ix hk (m+1+1+1+1+1)) &&
      mix hk 2 (rot hk 3 t) (ix hk (m+1+1+1+1+1+1))) := hc
  rw [TT hk (by omega) t m, TT hk (by omega) t (m+1), hv, mm hk (by omega) v (m+1),
    mm hk (by omega) v (m+1+1), mm hk (by omega) v (m+1+1+1),
    mm hk (by omega) v (m+1+1+1+1)] at hc'
  exact hc'

theorem cover (hk : 0 < k) (A : ℕ) (hA : A < k) (i : Fin k) :
    ∃ y, y < k ∧ i = ix hk (A + y) := by
  refine ⟨(i.val + k - A) % k, Nat.mod_lt _ hk, Fin.ext ?_⟩
  show i.val = (A + (i.val + k - A) % k) % k
  rw [Nat.add_mod_mod, show A + (i.val + k - A) = i.val + k by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt i.2]

theorem rowker (hk : 0 < k) (h7 : 7 ≤ k) (N D : Fin k → Bool) (A g : ℕ) (hA : A < k)
    (hg : 1 ≤ g ∧ g ≤ 2)
    (hN : ∀ M y, (M = A + y ∨ M = A + y + k) → y < k → N (ix hk M) = decide (g ≤ y))
    (hD : inK hk N D) : D = zz ∨ D = N := by
  rw [inK_iff] at hD
  have const : ∀ n, g + n < k → D (ix hk (A+g+n)) = D (ix hk (A+g)) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro h
      have := hD (A+g+n)
      rw [hN (A+g+n+1) (g+n+1) (Or.inl (by omega)) (by omega),
        hN (A+g+n) (g+n) (Or.inl (by omega)) (by omega),
        decide_eq_true (by omega : g ≤ g+n+1), decide_eq_true (by omega : g ≤ g + n)] at this
      simp only [Bool.true_and] at this
      show D (ix hk (A+g+n+1)) = _
      rw [← this]; exact ih (by omega)
  have low : ∀ y, y < g → D (ix hk (A+y)) = false := by
    intro y hy
    rcases Nat.eq_zero_or_pos y with rfl | hy1
    · have := hD (A+(k-1))
      rw [hN (A+(k-1)+1) 0 (Or.inr (by omega)) (by omega),
        hN (A+(k-1)) (k-1) (Or.inl rfl) (by omega),
        decide_eq_true (by omega : g ≤ k-1), decide_eq_false (by omega : ¬ g ≤ 0),
        show A + (k-1) + 1 = A + k by omega, ix_k] at this
      simp only [Bool.true_and, Bool.false_and] at this
      exact this.symm
    · have y1 : y = 1 := by omega
      subst y1
      have := hD (A+1)
      rw [hN (A+1+1) 2 (Or.inl rfl) (by omega), hN (A+1) 1 (Or.inl rfl) (by omega),
        decide_eq_true (by omega : g ≤ 2), decide_eq_false (by omega : ¬ g ≤ 1)] at this
      simp only [Bool.true_and, Bool.false_and] at this
      exact this
  have val : ∀ y, y < k → D (ix hk (A+y)) = (D (ix hk (A+g)) && decide (g ≤ y)) := by
    intro y hy
    rcases Nat.lt_or_ge y g with h | h
    · rw [low y h, decide_eq_false (by omega : ¬ g ≤ y)]; simp
    · have := const (y-g) (by omega)
      rw [show A + g + (y-g) = A + y by omega] at this
      rw [this, decide_eq_true h]; simp
  cases hd : D (ix hk (A+g))
  · left
    funext i
    obtain ⟨y, hy, rfl⟩ := cover hk A hA i
    rw [val y hy, hd]; rfl
  · right
    funext i
    obtain ⟨y, hy, rfl⟩ := cover hk A hA i
    rw [val y hy, hd, hN (A+y) y (Or.inl rfl) hy]; rfl

theorem mod2 (_hk : 0 < k) (x : ℕ) (h : x < 2*k) :
    (x%k = x ∧ x < k) ∨ (x%k + k = x ∧ k ≤ x) := by
  rcases Nat.lt_or_ge x k with h1 | h1
  · exact Or.inl ⟨Nat.mod_eq_of_lt h1, h1⟩
  · right
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    exact ⟨by omega, h1⟩

theorem rot1_inj (hk : 0 < k) (h7 : 7 ≤ k) (t t' : Fin k → Bool)
    (h : rot hk 1 t = rot hk 1 t') : t = t' := by
  funext i
  rw [← ix_self hk i, ← rot_ix hk 1 (by omega) t i.val, h, rot_ix hk 1 (by omega)]

theorem core_mpr (hk : 0 < k) (h7 : 7 ≤ k) (h3 : ¬ 3 ∣ k) (v : Fin k → Bool)
    (h : isGap hk (mix hk 1 v)) :
    ∃ c : Fin k, ∀ t : Fin k → Bool, inK hk (mix hk 1 v) (mix hk 1 (rot hk 1 t)) →
      colc hk c (mix hk 2 v) (mix hk 2 (rot hk 3 t)) → t = zz := by
  have fin : ∀ t : Fin k → Bool, mix hk 1 (rot hk 1 t) = zz → t = zz := by
    intro t ht
    apply rot1_inj hk h7
    apply mix1_inj hk h7 h3
    rw [ht]; funext i; rfl
  obtain ⟨a, h | h⟩ := h
  · have hN : ∀ M y, (M = a.val + y ∨ M = a.val + y + k) → y < k →
        mix hk 1 v (ix hk M) = decide (1 ≤ y) := by
      intro M y hM hy
      have e : ix hk M = ix hk (a.val + y) := by
        rcases hM with rfl | rfl
        · rfl
        · exact ix_k hk _
      rw [e, h, decide_eq_decide, Ne, Fin.ext_iff]
      show ¬ (a.val + y) % k = a.val ↔ _
      have := mod2 hk (a.val + y) (by have := a.2; omega)
      have := a.2
      omega
    refine ⟨ix hk (a.val + (k-2) +1+1+1+1), fun t hK hc => ?_⟩
    rcases rowker hk h7 _ _ a.val 1 a.2 (by omega) hN hK with h0 | h1
    · exact fin t h0
    · have hv := mix1_inj hk h7 h3 h1
      have := colfail hk h7 v t hv (a.val + (k-2)) hc
      rw [hN (a.val + (k-2)+1+1) 0 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-2)+1+1+1) 1 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-2)+1+1+1+1) 2 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-2)+1+1+1+1+1) 3 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-2)+1+1+1+1+1+1) 4 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-2)+1+1+1+1+1+1+1) 5 (Or.inr (by omega)) (by omega)] at this
      simp at this
  · have hN : ∀ M y, (M = a.val + y ∨ M = a.val + y + k) → y < k →
        mix hk 1 v (ix hk M) = decide (2 ≤ y) := by
      intro M y hM hy
      have e : ix hk M = ix hk (a.val + y) := by
        rcases hM with rfl | rfl
        · rfl
        · exact ix_k hk _
      rw [e, h, decide_eq_decide, Ne, Ne, Fin.ext_iff, Fin.ext_iff]
      show (¬ (a.val + y) % k = a.val ∧ ¬ (a.val + y) % k = (a.val + 1) % k) ↔ _
      have := mod2 hk (a.val + y) (by have := a.2; omega)
      have := mod2 hk (a.val + 1) (by have := a.2; omega)
      have := a.2
      omega
    refine ⟨ix hk (a.val + (k-4) +1+1+1+1), fun t hK hc => ?_⟩
    rcases rowker hk h7 _ _ a.val 2 a.2 (by omega) hN hK with h0 | h1
    · exact fin t h0
    · have hv := mix1_inj hk h7 h3 h1
      have := colfail hk h7 v t hv (a.val + (k-4)) hc
      rw [hN (a.val + (k-4)+1+1) (k-2) (Or.inl (by omega)) (by omega),
        hN (a.val + (k-4)+1+1+1) (k-1) (Or.inl (by omega)) (by omega),
        hN (a.val + (k-4)+1+1+1+1) 0 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-4)+1+1+1+1+1) 1 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-4)+1+1+1+1+1+1) 2 (Or.inr (by omega)) (by omega),
        hN (a.val + (k-4)+1+1+1+1+1+1+1) 3 (Or.inr (by omega)) (by omega)] at this
      simp at this
      omega

def gf (hk : 0 < k) (x : Fin k × Bool) : Fin k → Bool :=
  fun i => decide (i ≠ x.1 ∧ (x.2 = true → i ≠ ix hk (x.1.val+1)))

theorem isGap_iff (hk : 0 < k) (N : Fin k → Bool) : isGap hk N ↔ ∃ x, gf hk x = N := by
  constructor
  · rintro ⟨a, h | h⟩
    · exact ⟨(a, false), by funext i; rw [h]; simp [gf]⟩
    · exact ⟨(a, true), by funext i; rw [h]; simp [gf]⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    cases b
    · exact ⟨a, Or.inl (fun i => by simp [gf])⟩
    · exact ⟨a, Or.inr (fun i => by simp [gf])⟩

theorem gf_inj (hk : 0 < k) (h7 : 7 ≤ k) : Function.Injective (gf hk) := by
  have zero : ∀ (a a' : Fin k) (b b' : Bool), gf hk (a, b) = gf hk (a', b') → a ≠ a' →
      a = ix hk (a'.val+1) := by
    intro a a' b b' h hne
    have l : gf hk (a, b) a = false := by simp [gf]
    have e := congrFun h a
    rw [l] at e
    have e1 : ¬ (a ≠ a' ∧ (b' = true → a ≠ ix hk (a'.val+1))) := of_decide_eq_false e.symm
    by_contra x
    exact e1 ⟨hne, fun _ => x⟩
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have ha : a = a' := by
    by_contra hne
    have p1 := Fin.ext_iff.1 (zero a a' b b' h hne)
    have p2 := Fin.ext_iff.1 (zero a' a b' b h.symm (Ne.symm hne))
    have q1 : a.val = (a'.val+1) % k := p1
    have q2 : a'.val = (a.val+1) % k := p2
    have := mod2 hk (a.val + 1) (by have := a.2; omega)
    have := mod2 hk (a'.val + 1) (by have := a'.2; omega)
    have := a.2
    have := a'.2
    omega
  subst ha
  have key : ix hk (a.val+1) ≠ a := by
    rw [Ne, Fin.ext_iff]
    show ¬ (a.val+1) % k = a.val
    have := mod2 hk (a.val + 1) (by have := a.2; omega)
    have := a.2
    omega
  have e := congrFun h (ix hk (a.val+1))
  cases b <;> cases b'
  · rfl
  · simp [gf, key] at e
  · simp [gf, key] at e
  · rfl

theorem count (hk : 0 < k) (h7 : 7 ≤ k) (h3 : ¬ 3 ∣ k) (P : (Fin k → Bool) → Prop)
    (inst : DecidablePred P) (hP : ∀ v, P v ↔ isGap hk (mix hk 1 v)) :
    (@Finset.filter _ P inst Finset.univ).card = 2 * k := by
  have hc1 : (@Finset.filter _ P inst Finset.univ).card = (Finset.univ.image (gf hk)).card := by
    refine Finset.card_bij (fun v _ => mix hk 1 v) ?_ ?_ ?_
    · intro v hv
      obtain ⟨x, hx⟩ := (isGap_iff hk _).1 ((hP v).1 (Finset.mem_filter.1 hv).2)
      exact Finset.mem_image.2 ⟨x, Finset.mem_univ _, hx⟩
    · intro v _ w _ h
      exact mix1_inj hk h7 h3 h
    · intro N hN
      obtain ⟨x, _, hx⟩ := Finset.mem_image.1 hN
      obtain ⟨v, rfl⟩ := Finite.surjective_of_injective (mix1_inj hk h7 h3) N
      exact ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, (hP v).2 ((isGap_iff hk _).2 ⟨x, hx⟩)⟩,
        rfl⟩
  rw [hc1, Finset.card_image_of_injective _ (gf_inj hk h7), Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]

end PEqualNP.Outside.L_meta_45024_aux

theorem PEqualNP.Outside.L_meta_45024 : ∀ (k : Nat) (hk : 0 < k), 7 ≤ k →
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let rot := fun (s : Nat) (w : W) (i : Fin k) => w (ix (i.val+k-s % k))
  let mix := fun (d : Nat) (w : W) (i : Fin k) =>
    xor (w (ix (i.val+k-d % k))) (xor (w i) (w (ix (i.val+d))))
  let readBit := fun (col : Bool) (u x : W) (i : Fin k) =>
    let d := if col then 2 else 1
    let R := mix d (add u (rot (if col then 3 else 1) x))
    xor (rot (if col then 4 else 0) x i)
      (xor (R i) (!(R (ix (i.val+1))) && R (ix (i.val+2))))
  ¬ 3 ∣ k →
  ∀ (u : W),
    let delta := fun (col : Bool) (v x : W) (i : Fin k) =>
      xor (readBit col u x i) (readBit col (add u v) x i)
    let good := fun v : W => ∃ c : Fin k,
      Function.Injective (fun x : W => (delta false v x, delta true v x c))
    (∀ v : W, good v ↔ ∃ a : Fin k,
      ((∀ i : Fin k, mix 1 v i = decide (i ≠ a)) ∨
       (∀ i : Fin k, mix 1 v i = decide (i ≠ a ∧ i ≠ ix (a.val+1))))) ∧
    (@Finset.filter W good (fun x => Classical.propDecidable (good x)) Finset.univ).card = 2*k := by
  intro k hk h7 W ix add rot mix readBit h3 u delta good
  have hg : ∀ v : W, good v ↔ PEqualNP.Outside.L_meta_45024_aux.isGap hk
      (PEqualNP.Outside.L_meta_45024_aux.mix hk 1 v) := fun v =>
    (PEqualNP.Outside.L_meta_45024_aux.good_iff hk u v).trans
      ⟨PEqualNP.Outside.L_meta_45024_aux.core_mp hk h7 h3 v,
       PEqualNP.Outside.L_meta_45024_aux.core_mpr hk h7 h3 v⟩
  exact ⟨hg, PEqualNP.Outside.L_meta_45024_aux.count hk h7 h3 good _ hg⟩
