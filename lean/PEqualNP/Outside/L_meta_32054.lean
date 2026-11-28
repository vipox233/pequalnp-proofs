import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_32054

section Gen

variable {V : Type*} [AddCommGroup V]

def dif (f : V → ZMod 2) (u : V) : V → ZMod 2 := fun x => f (x + u) - f x

def Van : ℕ → (V → ZMod 2) → Prop
  | 0, f => ∀ x, f x = 0
  | n + 1, f => ∀ u, Van n (dif f u)

theorem van_add : ∀ (n : ℕ) (f g : V → ZMod 2), Van n f → Van n g → Van n (fun x => f x + g x)
  | 0, f, g, hf, hg => fun x => by simp [hf x, hg x]
  | n + 1, f, g, hf, hg => fun u => by
      have h := van_add n _ _ (hf u) (hg u)
      have e : dif (fun x => f x + g x) u = fun x => dif f u x + dif g u x := by
        funext x; simp only [dif]; ring
      rw [e]; exact h

theorem van_congr {n : ℕ} {f g : V → ZMod 2} (h : ∀ x, f x = g x) (hf : Van n f) : Van n g := by
  have : f = g := funext h
  subst this; exact hf

theorem van_mono : ∀ (n : ℕ) (f : V → ZMod 2), Van n f → Van (n + 1) f
  | 0, f, hf => fun u => fun x => by simp only [dif]; rw [hf, hf]; simp
  | n + 1, f, hf => fun u => van_mono n _ (hf u)

theorem van_mono' {n m : ℕ} (h : n ≤ m) {f : V → ZMod 2} (hf : Van n f) : Van m f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact van_mono _ _ ih

theorem van_cmul : ∀ (n : ℕ) (c : ZMod 2) (f : V → ZMod 2), Van n f → Van n (fun x => c * f x)
  | 0, c, f, hf => fun x => by simp [hf x]
  | n + 1, c, f, hf => fun u => by
      have e : dif (fun x => c * f x) u = fun x => c * dif f u x := by
        funext x; simp only [dif]; ring
      rw [e]; exact van_cmul n c _ (hf u)

theorem van_shift : ∀ (n : ℕ) (a : V) (f : V → ZMod 2), Van n f → Van n (fun x => f (x + a))
  | 0, a, f, hf => fun x => hf _
  | n + 1, a, f, hf => fun u => by
      have e : dif (fun x => f (x + a)) u = fun x => dif f u (x + a) := by
        funext x; simp only [dif]; rw [add_right_comm]
      rw [e]; exact van_shift n a _ (hf u)

theorem van_one_const {f : V → ZMod 2} (hf : Van 1 f) : ∀ x, f x = f 0 := by
  intro x
  have := hf x 0
  simp only [dif, zero_add] at this
  exact sub_eq_zero.mp this

theorem van_mul : ∀ (a b : ℕ) (f g : V → ZMod 2), Van (a + 1) f → Van (b + 1) g →
    Van (a + b + 1) (fun x => f x * g x)
  | 0, b, f, g, hf, hg => by
      have hc := van_one_const hf
      simp only [zero_add]
      exact van_congr (fun x => by rw [hc x]) (van_cmul _ (f 0) g hg)
  | a + 1, 0, f, g, hf, hg => by
      have hc := van_one_const hg
      exact van_congr (fun x => by rw [hc x, mul_comm]) (van_cmul _ (g 0) f hf)
  | a + 1, b + 1, f, g, hf, hg => fun u => by
      have e : dif (fun x => f x * g x) u =
          fun x => dif f u x * g (x + u) + f x * dif g u x := by
        funext x; simp only [dif]; ring
      rw [e]
      apply van_add
      · have h1 := van_mul a (b + 1) (dif f u) (fun x => g (x + u)) (hf u)
          (van_shift _ u g hg)
        have : a + (b + 1) + 1 = a + 1 + b + 1 := by omega
        rw [this] at h1; exact h1
      · exact van_mul (a + 1) b f (dif g u) hf (hg u)

theorem van_const (c : ZMod 2) : Van 1 (fun _ : V => c) := fun u x => by simp [dif]

theorem van_lin (f : V →+ ZMod 2) : Van 2 (fun x => f x) := fun u => by
  have e : dif (fun x => f x) u = fun _ => f u := by funext x; simp [dif, map_add]
  rw [e]; exact van_const _


end Gen

section Cyc
variable (k : ℕ) (hk : 0 < k)

def ix (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩
def rot (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 := x (ix k hk (i.val + k - s % k))
def mix (g : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + x (ix k hk (i.val + g)) + x (ix k hk (i.val + k - g % k))
def stp (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + (1 + x (ix k hk (i.val + 1))) * x (ix k hk (i.val + 2))

def zf (g s : ℕ) (nm : Fin k → ZMod 2) (x : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  mix k hk g (rot k hk s x + nm)
def yq (g s : ℕ) (nm : Fin k → ZMod 2) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  (1 + zf k hk g s nm x (ix k hk (j.val + 1))) * zf k hk g s nm x (ix k hk (j.val + 2))
def Qf (g s : ℕ) (nm : Fin k → ZMod 2) (i : Fin k) (x : Fin k → ZMod 2) : ZMod 2 :=
  mix k hk g (yq k hk g s nm x) (ix k hk (i.val + 1)) *
    mix k hk g (yq k hk g s nm x) (ix k hk (i.val + 2))


abbrev W := Fin k → ZMod 2

theorem pv_coord (p : Fin k) : Van 2 (fun x : W k => x p) :=
  van_lin (Pi.evalAddMonoidHom (fun _ : Fin k => ZMod 2) p)

theorem decomp (g s r1 r2 : ℕ) (nm c1 c2 : Fin k → ZMod 2) (i : Fin k) :
    ∃ C : W k → ZMod 2, Van 4 C ∧ ∀ x : W k,
      (stp k hk (mix k hk g (stp k hk (mix k hk g (rot k hk s x + nm)) + rot k hk r1 x + c1)) +
        rot k hk r2 x + c2) i = Qf k hk g s nm i x + C x := by
  have hz : ∀ p, Van 2 (fun x : W k => zf k hk g s nm x p) := by
    intro p
    simp only [zf, mix, rot, Pi.add_apply]
    refine van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _)))
      (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _))))
      (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _)))
  have hy : ∀ j, Van 3 (fun x : W k => yq k hk g s nm x j) := by
    intro j
    simp only [yq]
    exact van_mul 1 1 _ _ (van_add _ _ _ (van_mono _ _ (van_const _)) (hz _)) (hz _)
  let l : W k → Fin k → ZMod 2 := fun x j => zf k hk g s nm x j + rot k hk r1 x j + c1 j
  have hl : ∀ j, Van 2 (fun x => l x j) := by
    intro j
    exact van_add _ _ _ (van_add _ _ _ (hz j) (pv_coord k _)) (van_mono _ _ (van_const _))
  have hw : ∀ j, Van 3 (fun x : W k => mix k hk g (yq k hk g s nm x) j) := by
    intro j; simp only [mix]
    exact van_add _ _ _ (van_add _ _ _ (hy _) (hy _)) (hy _)
  have hm : ∀ j, Van 2 (fun x : W k => mix k hk g (l x) j) := by
    intro j; simp only [mix]
    exact van_add _ _ _ (van_add _ _ _ (hl _) (hl _)) (hl _)
  let w' := fun (x : W k) => mix k hk g (yq k hk g s nm x)
  let m := fun (x : W k) => mix k hk g (l x)
  let i1 := ix k hk (i.val + 1)
  let i2 := ix k hk (i.val + 2)
  refine ⟨fun x => (w' x i + m x i) + (w' x i2 + m x i2) + w' x i1 * m x i2 + m x i1 * w' x i2
    + m x i1 * m x i2 + rot k hk r2 x i + c2 i, ?_, ?_⟩
  · have a1 : Van 4 (fun x => w' x i + m x i) :=
      van_mono _ _ (van_add _ _ _ (hw i) (van_mono _ _ (hm i)))
    have a2 : Van 4 (fun x => w' x i2 + m x i2) :=
      van_mono _ _ (van_add _ _ _ (hw i2) (van_mono _ _ (hm i2)))
    have a3 : Van 4 (fun x => w' x i1 * m x i2) := van_mul 2 1 _ _ (hw i1) (hm i2)
    have a4 : Van 4 (fun x => m x i1 * w' x i2) := by
      have := van_mul 1 2 _ _ (hm i1) (hw i2); exact this
    have a5 : Van 4 (fun x => m x i1 * m x i2) := van_mono _ _ (van_mul 1 1 _ _ (hm i1) (hm i2))
    have a6 : Van 4 (fun x : W k => rot k hk r2 x i) := van_mono' (by norm_num) (pv_coord k _)
    have a7 : Van 4 (fun _ : W k => c2 i) := van_mono' (by norm_num) (van_const _)
    exact van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (van_add _ _ _
      (van_add _ _ _ a1 a2) a3) a4) a5) a6) a7
  · intro x
    have e : ∀ j, (mix k hk g (stp k hk (mix k hk g (rot k hk s x + nm)) + rot k hk r1 x + c1)) j
        = w' x j + m x j := by
      intro j
      simp only [w', m, l, mix, stp, yq, zf, Pi.add_apply]
      ring
    simp only [stp, Pi.add_apply, Qf]
    rw [e, e, e]
    simp only [w', m, i1, i2]
    ring



end Cyc

variable {k : ℕ} [NeZero k]

abbrev V (k : ℕ) := ZMod k → ZMod 2

def R (s : ℕ) (x : V k) : V k := fun i => x (i - (s : ZMod k))
def M (g : ℕ) (x : V k) : V k := fun i => x i + x (i + (g : ZMod k)) + x (i - (g : ZMod k))
def st (x : V k) : V k := fun i => x i + (1 + x (i + 1)) * x (i + 2)
def ind (q : ZMod k) : V k := fun t => if t = q then 1 else 0

theorem z2 (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem vz2 (x : V k) : x + x = 0 := by funext i; exact z2 _

theorem M_add (g : ℕ) (x y : V k) : M g (x + y) = M g x + M g y := by
  funext i; simp only [M, Pi.add_apply]; ring

theorem M_zero (g : ℕ) : M g (0 : V k) = 0 := by
  funext i; simp [M]

theorem R_add (s : ℕ) (x y : V k) : R s (x + y) = R s x + R s y := by
  funext i; simp only [R, Pi.add_apply]

theorem M_R (g s : ℕ) (x : V k) : M g (R s x) = R s (M g x) := by
  funext i; simp only [M, R]
  rw [show i + (g : ZMod k) - s = i - s + g by ring, show i - (g : ZMod k) - s = i - s - g by ring]

theorem R_eq_zero (s : ℕ) (x : V k) (h : R s x = 0) : x = 0 := by
  funext i
  have := congrFun h (i + s)
  simpa [R] using this


theorem ker_triv (g : ℕ) (hk : ¬ 3 ∣ k) (x : V k) (hx : M g x = 0) : x = 0 := by
  have e : ∀ i, x i + x (i + g) + x (i - g) = 0 := fun i => congrFun hx i
  have p3 : ∀ i, x (i + 3 * g) = x i := by
    intro i
    have e1 := e (i + g)
    have e2 := e (i + 2 * g)
    rw [show i + (g : ZMod k) - g = i by ring, show i + (g : ZMod k) + g = i + 2 * g by ring]
      at e1
    rw [show i + 2 * (g : ZMod k) - g = i + g by ring,
      show i + 2 * (g : ZMod k) + g = i + 3 * g by ring] at e2
    linear_combination e2 - e1
  have pn : ∀ n : ℕ, ∀ i, x (i + (n : ZMod k) * (3 * g)) = x i := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [show i + ((n + 1 : ℕ) : ZMod k) * (3 * g) = (i + (n : ZMod k) * (3 * g)) + 3 * g by
        push_cast; ring, p3, ih]
  have hcop : Nat.Coprime 3 k := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]; exact hk
  set u := ZMod.unitOfCoprime 3 hcop
  have hu : (u : ZMod k) = 3 := by simp [u, ZMod.coe_unitOfCoprime]
  have hn : (((u⁻¹ : (ZMod k)ˣ) : ZMod k).val : ZMod k) * (3 * g) = g := by
    rw [ZMod.natCast_zmod_val, ← mul_assoc, ← hu, Units.inv_mul, one_mul]
  have ps : ∀ i, x (i + g) = x i := by
    intro i; have := pn (((u⁻¹ : (ZMod k)ˣ) : ZMod k).val) i; rwa [hn] at this
  funext i
  have ei := e i
  have hm := ps (i - g)
  rw [sub_add_cancel] at hm
  rw [ps i, ← hm] at ei
  simp only [Pi.zero_apply]
  linear_combination ei - z2 (x i)


theorem window (x : V k) (L : ℕ) (hL : 0 < L) (i : ZMod k)
    (hrec : ∀ t : ZMod k, (∀ n < L, x (t + n) = 0) → x (t + L) = 0)
    (hz : ∀ n < L, x (i + n) = 0) : x = 0 := by
  have key : ∀ m n : ℕ, n < L → x (i + ((m + n : ℕ) : ZMod k)) = 0 := by
    intro m
    induction m with
    | zero => intro n hn; simpa using hz n hn
    | succ m ih =>
      intro n hn
      by_cases hn1 : n + 1 < L
      · have := ih (n + 1) hn1
        rwa [show m + (n + 1) = m + 1 + n by omega] at this
      · have hnL : n = L - 1 := by omega
        have := hrec (i + m) (fun n' hn' => by
          have := ih n' hn'; push_cast at this; rwa [add_assoc])
        rw [show m + 1 + n = m + L by omega]; push_cast
        rwa [← add_assoc]
  funext j
  have := key (j - i).val 0 hL
  simpa [ZMod.natCast_zmod_val] using this


theorem split_sum (x y : V k) : y = x + (y + x) := by
  rw [add_comm y x, ← add_assoc, vz2, zero_add]


theorem per3 (g : ℕ) (x : V k) (hx : M g x = 0) : ∀ i, x (i + 3 * g) = x i := by
  have e : ∀ i, x i + x (i + g) + x (i - g) = 0 := fun i => congrFun hx i
  intro i
  have e1 := e (i + g)
  have e2 := e (i + 2 * g)
  rw [show i + (g : ZMod k) - g = i by ring, show i + (g : ZMod k) + g = i + 2 * g by ring] at e1
  rw [show i + 2 * (g : ZMod k) - g = i + g by ring,
    show i + 2 * (g : ZMod k) + g = i + 3 * g by ring] at e2
  linear_combination e2 - e1

theorem card_triv (g : ℕ) (hk : ¬ 3 ∣ k) : Nat.card {d : V k // M g d = 0} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨0, M_zero g⟩, fun y => Subtype.ext (ker_triv g hk y.1 y.2)⟩

theorem wd (P : ℕ) (hP : P ∣ k) (i : ZMod k) (c : ℕ) : (i + c).val % P = (i.val + c) % P := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hP, Nat.add_mod,
    Nat.mod_mod_of_dvd _ hP, ← Nat.add_mod]

theorem negc (g : ℕ) (hg : g ≤ k) : -((g : ℕ) : ZMod k) = ((k - g : ℕ) : ZMod k) := by
  rw [Nat.cast_sub hg, ZMod.natCast_self, zero_sub]

def f3 (a b : ZMod 2) (r : ℕ) : ZMod 2 := if r = 0 then a else if r = 1 then b else a + b
def w3 (a b : ZMod 2) : V k := fun i => f3 a b (i.val % 3)

def f6 (a b c d : ZMod 2) (r : ℕ) : ZMod 2 :=
  if r = 0 then a else if r = 1 then b else if r = 2 then c else if r = 3 then d
  else if r = 4 then a + c else b + d
def w6 (a b c d : ZMod 2) : V k := fun i => f6 a b c d (i.val % 6)

theorem w3_mem (h3 : 3 ∣ k) (hk6 : 6 ≤ k) (a b : ZMod 2) : M 1 (w3 (k := k) a b) = 0 := by
  funext i
  simp only [M, Pi.zero_apply]
  rw [sub_eq_add_neg, negc 1 (by omega)]
  simp only [w3]
  rw [wd 3 h3, wd 3 h3]
  obtain ⟨m, hm⟩ := h3
  have hr : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rw [show (i.val + 1) % 3 = (i.val % 3 + 1) % 3 by omega,
    show (i.val + (k - 1)) % 3 = (i.val % 3 + 2) % 3 by omega]
  rcases hr with hr | hr | hr <;> rw [hr] <;> (revert a b; decide)

theorem w6_mem (h6 : 6 ∣ k) (a b c d : ZMod 2) : M 2 (w6 (k := k) a b c d) = 0 := by
  have hk := NeZero.pos k
  funext i
  simp only [M, Pi.zero_apply]
  rw [sub_eq_add_neg, negc 2 (by omega)]
  simp only [w6]
  rw [wd 6 h6, wd 6 h6]
  obtain ⟨m, hm⟩ := h6
  have hr : i.val % 6 = 0 ∨ i.val % 6 = 1 ∨ i.val % 6 = 2 ∨ i.val % 6 = 3 ∨ i.val % 6 = 4 ∨
    i.val % 6 = 5 := by omega
  rw [show (i.val + 2) % 6 = (i.val % 6 + 2) % 6 by omega,
    show (i.val + (k - 2)) % 6 = (i.val % 6 + 4) % 6 by omega]
  rcases hr with hr | hr | hr | hr | hr | hr <;> rw [hr] <;> (revert a b c d; decide)

theorem inj1 (hk6 : 6 ≤ k) (z : V k) (hz : M 1 z = 0) (h0 : z 0 = 0) (h1 : z 1 = 0) :
    z = 0 := by
  apply window z 2 (by omega) 0
  · intro t ht
    have e0 := ht 0 (by omega)
    have e1 := ht 1 (by omega)
    have := congrFun hz (t + 1)
    simp only [M, Nat.cast_one, Pi.zero_apply] at this e0 e1
    rw [show t + 1 + 1 = t + ((2 : ℕ) : ZMod k) by push_cast; ring,
      show t + 1 - 1 = t by ring] at this
    simp only [Nat.cast_zero, add_zero] at e0 e1
    rw [e0, e1] at this; simpa using this
  · intro n hn
    interval_cases n <;> simpa using ‹_›

theorem inj2 (z : V k) (hz : M 2 z = 0) (h0 : z 0 = 0) (h1 : z 1 = 0) (h2 : z 2 = 0)
    (h3 : z 3 = 0) : z = 0 := by
  apply window z 4 (by omega) 0
  · intro t ht
    have e0 := ht 0 (by omega)
    have e2 := ht 2 (by omega)
    have := congrFun hz (t + 2)
    simp only [M, Nat.cast_ofNat, Pi.zero_apply] at this e0 e2
    rw [show t + 2 + 2 = t + ((4 : ℕ) : ZMod k) by push_cast; ring,
      show t + 2 - 2 = t by ring] at this
    simp only [Nat.cast_zero, add_zero] at e0 e2
    rw [e0, e2] at this; simpa using this
  · intro n hn
    interval_cases n
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa using h3

theorem valn (n : ℕ) (hn : n < k) : ((n : ℕ) : ZMod k).val = n := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn]

theorem val1 (hk : 2 ≤ k) : (1 : ZMod k).val = 1 := by
  rw [← Nat.cast_one, valn 1 (by omega)]

theorem card1 (h3 : 3 ∣ k) (hk6 : 6 ≤ k) : Nat.card {d : V k // M 1 d = 0} = 4 := by
  have v1 := val1 (k := k) (by omega)
  have e : {d : V k // M 1 d = 0} ≃ ZMod 2 × ZMod 2 :=
    { toFun := fun x => (x.1 0, x.1 1)
      invFun := fun p => ⟨w3 p.1 p.2, w3_mem h3 hk6 p.1 p.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        show w3 (x.1 0) (x.1 1) = x.1
        have hz := inj1 hk6 (w3 (x.1 0) (x.1 1) + x.1)
          (by rw [M_add, w3_mem h3 hk6, x.2, add_zero])
          (by simp only [Pi.add_apply, w3, ZMod.val_zero, Nat.zero_mod, f3]; exact z2 _)
          (by simp only [Pi.add_apply, w3, v1, f3]; norm_num; exact z2 _)
        have := split_sum x.1 (w3 (k := k) (x.1 0) (x.1 1))
        rwa [hz, add_zero] at this
      right_inv := by
        intro p
        simp only [w3, v1, ZMod.val_zero]
        simp [f3] }
  rw [Nat.card_congr e]; simp

theorem card6 (h6 : 6 ∣ k) : Nat.card {d : V k // M 2 d = 0} = 16 := by
  have hk := NeZero.pos k
  have hk6 : 6 ≤ k := Nat.le_of_dvd hk h6
  have v1 := val1 (k := k) (by omega)
  have v2 : (2 : ZMod k).val = 2 := by
    have := valn (k := k) 2 (by omega); simpa using this
  have v3 : (3 : ZMod k).val = 3 := by
    have := valn (k := k) 3 (by omega); simpa using this
  have e : {d : V k // M 2 d = 0} ≃ ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 :=
    { toFun := fun x => (x.1 0, x.1 1, x.1 2, x.1 3)
      invFun := fun p => ⟨w6 p.1 p.2.1 p.2.2.1 p.2.2.2, w6_mem h6 _ _ _ _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        show w6 (x.1 0) (x.1 1) (x.1 2) (x.1 3) = x.1
        have hz := inj2 (w6 (x.1 0) (x.1 1) (x.1 2) (x.1 3) + x.1)
          (by rw [M_add, w6_mem h6, x.2, add_zero])
          (by simp only [Pi.add_apply, w6, ZMod.val_zero, Nat.zero_mod, f6]; exact z2 _)
          (by simp only [Pi.add_apply, w6, v1, f6]; norm_num; exact z2 _)
          (by simp only [Pi.add_apply, w6, v2, f6]; norm_num; exact z2 _)
          (by simp only [Pi.add_apply, w6, v3, f6]; norm_num; exact z2 _)
        have := split_sum x.1 (w6 (k := k) (x.1 0) (x.1 1) (x.1 2) (x.1 3))
        rwa [hz, add_zero] at this
      right_inv := by
        intro p
        simp only [w6, v1, v2, v3, ZMod.val_zero]
        simp [f6] }
  rw [Nat.card_congr e]; simp

theorem K21 (h3 : 3 ∣ k) (hodd : ¬ 2 ∣ k) (z : V k) : M 2 z = 0 ↔ M 1 z = 0 := by
  have eqM : (∀ i, z (i + 3) = z i) → M 2 z = M 1 z := by
    intro hp
    funext i
    simp only [M, Nat.cast_ofNat, Nat.cast_one]
    rw [← hp (i - 1), show i - 1 + 3 = i + 2 by ring, ← hp (i - 2),
      show i - 2 + 3 = i + 1 by ring]
    ring
  constructor
  · intro hz
    have p6 := per3 2 z hz
    have pl : ∀ l : ℕ, ∀ t, z (t + 6 * (l : ZMod k)) = z t := by
      intro l
      induction l with
      | zero => intro t; simp
      | succ l ih =>
        intro t
        have := p6 (t + 6 * (l : ZMod k))
        push_cast at this ⊢
        rw [show t + 6 * ((l : ZMod k) + 1) = t + 6 * l + 3 * 2 by ring, this, ih]
    have hp : ∀ i, z (i + 3) = z i := by
      intro i
      obtain ⟨l, hl⟩ : ∃ l, k = 6 * l + 3 := ⟨k / 6, by omega⟩
      have := pl l (i + 3)
      rw [show i + 3 + 6 * (l : ZMod k) = i + ((6 * l + 3 : ℕ) : ZMod k) by push_cast; ring,
        ← hl, ZMod.natCast_self, add_zero] at this
      exact this.symm
    rw [← eqM hp]; exact hz
  · intro hz
    have hp : ∀ i, z (i + 3) = z i := by
      intro i; have := per3 1 z hz i; simpa using this
    rw [eqM hp]; exact hz

theorem card_odd (h3 : 3 ∣ k) (hodd : ¬ 2 ∣ k) (hk6 : 6 ≤ k) :
    Nat.card {d : V k // M 2 d = 0} = 4 := by
  rw [← card1 h3 hk6]
  exact Nat.card_congr (Equiv.subtypeEquivRight (K21 h3 hodd))


theorem ix_eq (n m : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1))
      (⟨((i : Fin (n + 1)).val + m) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      (i + (m : ZMod (n + 1))) := by
  refine ZMod.val_injective (n + 1) ?_
  rw [ZMod.val_add, ZMod.val_natCast]
  show ((i : Fin (n + 1)).val + m) % (n + 1) = (ZMod.val i + m % (n + 1)) % (n + 1)
  rw [Nat.add_mod_mod]

theorem ix_sub (n s : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1)) (⟨((i : Fin (n + 1)).val + (n + 1) - s % (n + 1)) % (n + 1),
      Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1)) (i - (s : ZMod (n + 1))) := by
  have hs : s % (n + 1) ≤ n + 1 := (Nat.mod_lt _ (Nat.succ_pos n)).le
  have := ix_eq n (n + 1 - s % (n + 1)) i
  rw [Nat.add_sub_assoc hs, this, Nat.cast_sub hs, ZMod.natCast_mod, ZMod.natCast_self]
  ring


theorem ix_one (n : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1))
      (⟨((i : Fin (n + 1)).val + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      (i + 1) := by
  rw [ix_eq n 1 i, Nat.cast_one]

theorem ix_two (n : ℕ) (i : ZMod (n + 1)) :
    @Eq (ZMod (n + 1))
      (⟨((i : Fin (n + 1)).val + 2) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ : Fin (n + 1))
      (i + 2) := by
  rw [ix_eq n 2 i, Nat.cast_ofNat]


abbrev FF := ZMod 2

def raw (g : ℕ) (q : ZMod k) (w : V k) (a : ℕ) : FF :=
  w (q + a) + w (q + (a + g : ℕ)) + w (q + (a + 2*g : ℕ))

def localQ (g : ℕ) (q : ZMod k) (bias : ℕ → FF) (w : V k) : FF :=
  let z := fun a => raw g q w a + bias a
  let pair := fun a => (1 + z a) * z (a+1)
  (pair 0 + pair g + pair (2*g)) * (pair 1 + pair (1+g) + pair (1+2*g))

theorem natInj {a b : ℕ} (ha : a < k) (hb : b < k) :
    ((a : ZMod k) = b) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem raw_add (g : ℕ) (q : ZMod k) (w v : V k) (a : ℕ) :
    raw g q (w+v) a = raw g q w a + raw g q v a := by
  simp only [raw, Pi.add_apply]; ring

theorem raw_ind (g : ℕ) (q : ZMod k) (a t : ℕ) (ha : a+2*g < k) (ht : t < k) :
    raw g q (ind (q+t)) a = (if a = t then 1 else 0) +
      (if a+g = t then 1 else 0) + (if a+2*g = t then 1 else 0) := by
  simp only [raw, ind, add_right_inj, natInj (a := a) (by omega) ht,
    natInj (a := a+g) (by omega) ht, natInj ha ht]

theorem localPair (g : ℕ) (hg : 0 < g) (q : ZMod k) (bias : ℕ → FF)
    (hk : 2+4*g < k) (w : V k) :
    dif (dif (localQ g q bias) (ind q)) (ind (q + ((2+4*g : ℕ) : ZMod k))) w =
      (raw g q w 1 + bias 1) * (1 + (raw g q w (1+2*g) + bias (1+2*g))) := by
  have lo (a : ℕ) (ha : a ≤ 2+2*g) : raw g q (ind q) a = if a = 0 then 1 else 0 := by
    have h := raw_ind g q a 0 (by omega) (by omega)
    simpa only [Nat.cast_zero,add_zero,if_neg (show a+g ≠ 0 by omega),if_neg (show a+2*g ≠ 0 by omega)] using h
  have hi (a : ℕ) (ha : a ≤ 2+2*g) : raw g q (ind (q+((2+4*g : ℕ) : ZMod k))) a =
        if a = 2+2*g then 1 else 0 := by
    rw [raw_ind g q a (2+4*g) (by omega) hk]
    simp only [if_neg (show a ≠ 2+4*g by omega), if_neg (show a+g ≠ 2+4*g by omega), zero_add,
      show a+2*g = 2+4*g ↔ a = 2+2*g by omega]
  simp (disch := omega) only [dif, localQ, raw_add, lo, hi, if_pos, if_neg, add_zero, zero_add,
    ite_true, show 1+2*g+1 = 2+2*g by omega]
  ring

theorem dif_swap {X : Type*} [AddCommGroup X] (f : X → FF) (u v : X) :
    dif (dif f u) v = dif (dif f v) u := by
  funext x; simp only [dif, add_right_comm x v u]; ring

def fourth {X : Type*} [AddCommGroup X] (f : X → FF) (d u v h x : X) : FF :=
  dif (dif (dif (dif f d) u) v) h x

theorem swapPair {X : Type*} [AddCommGroup X] (f : X → FF) (d u v h x : X) :
    fourth f d u v h x = dif (dif (dif (dif f u) v) d) h x := by
  unfold fourth
  rw [dif_swap f d u, dif_swap (dif f u) d v]

theorem localTop (g : ℕ) (hg : 0 < g) (q : ZMod k) (bias : ℕ → FF)
    (hk : 2+4*g < k) (d h w : V k) :
    fourth (localQ g q bias) d (ind q) (ind (q + ((2+4*g : ℕ) : ZMod k))) h w =
      raw g q d 1 * raw g q h (1+2*g) + raw g q d (1+2*g) * raw g q h 1 := by
  rw [swapPair]
  have eqn := funext (localPair g hg q bias hk)
  rw [eqn]; simp only [dif, raw_add]; ring

theorem localMiss (g : ℕ) (q p : ZMod k) (bias : ℕ → FF)
    (hm : ∀ a : ℕ, a ≤ 2+4*g → q+a ≠ p) : dif (localQ g q bias) (ind p) = 0 := by
  have hr (a : ℕ) (ha : a ≤ 2+2*g) : raw g q (ind p) a = 0 := by
    simp only [raw, ind, if_neg (hm a (by omega)), if_neg (hm (a+g) (by omega)),
      if_neg (hm (a+2*g) (by omega)), add_zero]
  funext w
  simp (disch := omega) only [dif, localQ, raw_add, hr, add_zero, sub_self, Pi.zero_apply]

theorem windowPins (g len : ℕ) (hlen : 2+4*g ≤ len) (hk : len + (2+4*g) < k)
    (q p : ZMod k) (a b : ℕ) (ha : a ≤ 2+4*g) (hb : b ≤ 2+4*g)
    (h1 : q+a = p) (h2 : q+b = p+len) : q = p ∧ 2+4*g = len := by
  have hh : (b : ZMod k) = ((a + len : ℕ) : ZMod k) := by
    rw [← h1, add_assoc] at h2
    simpa using add_left_cancel h2
  have he := (natInj (by omega) (by omega)).mp hh
  have hz : a = 0 := by omega
  exact ⟨by simpa [hz] using h1, by omega⟩

theorem localOther (g len : ℕ) (hlen : 2+4*g ≤ len) (hk : len + (2+4*g) < k)
    (q p : ZMod k) (bias : ℕ → FF) (hn : ¬ (q = p ∧ 2+4*g = len)) (d h w : V k) :
    fourth (localQ g q bias) d (ind p) (ind (p+len)) h w = 0 := by
  by_cases hit : ∃ a : ℕ, a ≤ 2+4*g ∧ q+a = p
  · obtain ⟨a,ha,h1⟩ := hit
    have hm := localMiss g q (p+len) bias (fun b hb h2 => hn (windowPins g len hlen hk q p a b ha hb h1 h2))
    rw [swapPair, dif_swap (localQ g q bias), hm]; simp [dif]
  · have hm := localMiss g q p bias (fun a ha h1 => hit ⟨a,ha,h1⟩)
    rw [swapPair, hm]; simp [dif]

def edge (g s : ℕ) (i : ZMod k) := i + 2 - 2*(g : ZMod k) - s

def biasAt (g : ℕ) (i : ZMod k) (nm : V k) (a : ℕ) := M g nm (i+2-g+a)

theorem tapForm (g s : ℕ) (i : ZMod k) (w : V k) (a : ℕ) :
    raw g (edge g s i) w a = M g (R s w) (i+2-g+a) := by
  simp only [raw, edge, M, R]; push_cast; ring_nf

theorem rotFin (n s : ℕ) : rot (n+1) (by omega) s = R (k := n+1) s := by
  funext w i; exact congrArg w (ix_sub n s i)

theorem mixFin (n g : ℕ) : mix (n+1) (by omega) g = M (k := n+1) g := by
  funext w i
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (congrArg w (ix_eq n g i))) (congrArg w (ix_sub n g i))

theorem stepFin (n : ℕ) : stp (n+1) (by omega) = st (k := n+1) := by
  funext w i
  exact congrArg₂ (· + ·) rfl (congrArg₂ (· * ·) (congrArg₂ (· + ·) rfl (congrArg w (ix_one n i))) (congrArg w (ix_two n i)))

theorem Qform (n g s : ℕ) (nm : V (n+1)) (i : ZMod (n+1)) (w : V (n+1)) :
    Qf (n+1) (by omega) g s nm i w = localQ g (edge g s i) (biasAt g i nm) w := by
  let z := M g (R s w + nm)
  have hz (a : ℕ) : raw g (edge g s i) w a + biasAt g i nm a = z (i+2-g+a) := by
    rw [tapForm]; simp [z, biasAt, M_add]
  have zeq : zf (n+1) (by omega) g s nm w = z := by unfold zf; rw [rotFin, mixFin]; rfl
  have yeq : (show V (n+1) from yq (n+1) (by omega) g s nm w) = fun j => (1+z (j+1))*z (j+2) := by
    funext j; unfold yq; rw [zeq]
    exact congrArg₂ (· * ·) (congrArg (fun p => 1+z p) (ix_one n j)) (congrArg z (ix_two n j))
  let yy : V (n+1) := fun j => (1+z (j+1))*z (j+2)
  have evalPt (p : Fin (n+1)) (j : ZMod (n+1)) (ep : @Eq (ZMod (n+1)) p j) :
      mix (n+1) (by omega) g (yq (n+1) (by omega) g s nm w) p = M g yy j := by
    rw [mixFin]; exact congrFun (congrArg (M (k := n+1) g) yeq) p |>.trans (congrArg (M g yy) ep)
  refine (congrArg₂ (· * ·) (evalPt _ _ (ix_one n i)) (evalPt _ _ (ix_two n i))).trans ?_
  simp only [M,yy,localQ,hz]
  push_cast; ring_nf

def bank (g s t l : ℕ) (nm c1 c2 : V k) (w : V k) :=
  st (M g (st (M g (R s w + nm)) + R t w + c1)) + R l w + c2

theorem fourthSum {X : Type*} [AddCommGroup X] (f g : X → FF) (d l r h x : X) :
    fourth (fun w => f w + g w) d l r h x = fourth f d l r h x + fourth g d l r h x := by
  simp only [fourth, dif]; abel

theorem bankQ (n g s t l : ℕ) (nm c1 c2 : V (n+1)) (j : ZMod (n+1)) (d a b h x : V (n+1)) :
    fourth (fun w => bank g s t l nm c1 c2 w j) d a b h x =
      fourth (localQ g (edge g s j) (biasAt g j nm)) d a b h x := by
  obtain ⟨C,hC,hE⟩ := decomp (n+1) (by omega) g s t l nm c1 c2 j
  simp only [mixFin, rotFin, stepFin] at hE
  have eqn : (fun w => bank g s t l nm c1 c2 w j) = fun w => localQ g (edge g s j) (biasAt g j nm) w + C w := by
    funext w; rw [← Qform n g s nm j w]; exact hE w
  rw [eqn, fourthSum (X := V (n+1)) (localQ g (edge g s j) (biasAt g j nm)) C, show fourth (X := V (n+1)) C d a b h x = 0 from hC d a b h x, add_zero]

def obsZ (A : ZMod k → Bool) (w : V k) : FF := ∑ i, if A i then w i else 0

theorem fourthObs (A : ZMod k → Bool) (f : V k → V k) (d l r h x : V k) :
    fourth (fun w => obsZ A (f w)) d l r h x =
      ∑ j, if A j then fourth (fun w => f w j) d l r h x else 0 := by
  simp only [fourth, dif, obsZ, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j hj; cases A j <;> simp

theorem bankTop (n g s t l : ℕ) (hg : 0 < g) (hk : 2*(2+4*g) < n+1) (A : ZMod (n+1) → Bool)
    (nm c1 c2 : V (n+1)) (i : ZMod (n+1)) (d h x : V (n+1)) :
    fourth (fun w => obsZ A (bank g s t l nm c1 c2 w)) d (ind (edge g s i))
      (ind (edge g s i + ((2+4*g : ℕ) : ZMod (n+1)))) h x =
    if A i then raw g (edge g s i) d 1 * raw g (edge g s i) h (1+2*g) +
      raw g (edge g s i) d (1+2*g) * raw g (edge g s i) h 1 else 0 := by
  rw [fourthObs, Finset.sum_eq_single i]
  · rw [bankQ, localTop g hg (edge g s i) _ (by omega)]
  · intro j _ hji; have hn : ¬ (edge g s j = edge g s i ∧ 2+4*g = 2+4*g) := by
      intro ⟨h,_⟩; exact hji (by simpa [edge] using h)
    rw [bankQ, localOther g (2+4*g) le_rfl (by omega) (edge g s j) (edge g s i) _ hn]; simp
  · simp

theorem rowShort (n : ℕ) (hk : 21 ≤ n+1) (A : ZMod (n+1) → Bool) (nm c1 c2 : V (n+1))
    (i : ZMod (n+1)) (d h x : V (n+1)) :
    fourth (fun w => obsZ A (bank 1 1 0 2 nm c1 c2 w)) d (ind (i-5)) (ind (i+5)) h x = 0 := by
  rw [fourthObs]; apply Finset.sum_eq_zero; intro j hj
  have eqn : i+5 = (i-5) + ((10 : ℕ) : ZMod (n+1)) := by push_cast; ring
  rw [eqn, bankQ, localOther 1 10 (by omega) (by omega) (edge 1 1 j) (i-5) _ (by omega)]; simp

theorem rawZeros (g : ℕ) (hg : 0 < g) (hk : 2+4*g < k) (q : ZMod k) (d : V k)
    (hz : ∀ h, raw g q d 1 * raw g q h (1+2*g) + raw g q d (1+2*g) * raw g q h 1 = 0) :
    raw g q d 1 = 0 ∧ raw g q d (1+2*g) = 0 := by
  constructor
  · have hh := hz (ind (q+((1+4*g : ℕ) : ZMod k)))
    simpa (disch := omega) only [raw_ind g q 1 (1+4*g) (by omega) (by omega), raw_ind g q (1+2*g) (1+4*g) (by omega) (by omega), if_pos, if_neg, ite_true,
      zero_add, add_zero, mul_zero, mul_one] using hh
  · have hh := hz (ind (q+((1 : ℕ) : ZMod k)))
    simpa (disch := omega) only [raw_ind g q 1 1 (by omega) (by omega), raw_ind g q (1+2*g) 1 (by omega) (by omega), if_pos, if_neg, ite_true,
      zero_add, add_zero, mul_zero, mul_one] using hh

theorem squareM (d : V k) : M 1 (M 1 d) = M 2 d := by
  funext j
  simp only [M, Nat.cast_one, Nat.cast_ofNat, add_sub_cancel_right, sub_add_cancel,
    show j+1+1 = j+2 by ring, show j-1-1 = j-2 by ring]
  linear_combination z2 (d j) + z2 (d (j+1)) + z2 (d (j-1))

theorem obsAdd (A : ZMod k → Bool) (w v : V k) : obsZ A (w+v) = obsZ A w + obsZ A v := by
  simp only [obsZ, Pi.add_apply, ← Finset.sum_add_distrib]; apply Finset.sum_congr rfl
  intro i hi; cases A i <;> simp

theorem obsOff (A : ZMod k → Bool) (hf : ¬ ∃ i, A i = true) (w : V k) : obsZ A w = 0 := by
  apply Finset.sum_eq_zero; intro i hi; exact if_neg (fun h => hf ⟨i,h⟩)

theorem bankChange (g s t l : ℕ) (nm c1 c2 d : V k) (hd : M g d = 0) (w : V k) :
    bank g s t l nm c1 c2 (w+d) = bank g s t l nm c1 c2 w + R l d := by
  have hz (a : ℕ) : M g (R a d) = 0 := by rw [M_R, hd]; rfl
  simp only [bank, M_add, hz, add_zero, R_add]; abel

theorem obsBankChange (A : ZMod k → Bool) (g s t l : ℕ) (nm c1 c2 d : V k) (hd : M g d = 0) :
    dif (fun w => obsZ A (bank g s t l nm c1 c2 w)) d = fun _ => obsZ A (R l d) := by
  funext w; simp [dif, bankChange g s t l nm c1 c2 d hd, obsAdd]

theorem zerofourth {X : Type*} [AddCommGroup X] (f : X → FF) (d : X) (c : FF)
    (hc : ∀ w, dif f d w = c) (a b h x : X) : fourth f d a b h x = 0 := by
  change dif (dif (dif (dif f d) a) b) h x = 0
  rw [show dif f d = fun _ => c from funext hc]; simp [dif]

def Joint (u v r1 r2 c1 c2 : V k) (A B : ZMod k → Bool) (w : V k) : FF :=
  obsZ A (bank 1 1 0 2 u r1 r2 w) + obsZ B (bank 2 3 4 7 v c1 c2 w)

theorem goodResponse (u v r1 r2 c1 c2 : V k) (A B : ZMod k → Bool) (d : V k)
    (hg : M 2 d = 0 ∧ ((∃ i, A i = true) → M 1 d = 0)) (w : V k) :
    dif (Joint u v r1 r2 c1 c2 A B) d w = obsZ A (R 2 d) + obsZ B (R 7 d) := by
  have hcol := congrFun (obsBankChange B 2 3 4 7 v c1 c2 d hg.1) w
  have hrow : dif (fun x => obsZ A (bank 1 1 0 2 u r1 r2 x)) d w = obsZ A (R 2 d) := by
    by_cases ha : ∃ i, A i = true
    · exact congrFun (obsBankChange A 1 1 0 2 u r1 r2 d (hg.2 ha)) w
    · simp [dif, obsOff A ha]
  simp only [dif] at hcol hrow; simp only [dif, Joint]; linear_combination hcol + hrow

def Quad {X : Type*} [AddCommGroup X] (f : X → FF) :=
  ∀ (v : Fin 3 → X) (x : X), (List.ofFn v).foldl dif f x = 0

theorem fromQuad {X : Type*} [AddCommGroup X] (f : X → FF) (d : X) (hq : Quad (dif f d))
    (l r h x : X) : fourth f d l r h x = 0 := by
  have hh := hq ![l,r,h] x
  simpa [List.ofFn_succ, fourth] using hh

theorem constQuad {X : Type*} [AddCommGroup X] (f : X → FF) (c : FF) (hc : ∀ w, f w = c) : Quad f := by
  rw [show f = fun _ => c from funext hc]; intro v x; simp [List.ofFn_succ, dif]

theorem jointTop (n : ℕ) (hk : 21 ≤ n+1) (u v r1 r2 c1 c2 : V (n+1)) (A B : ZMod (n+1) → Bool)
    (i : ZMod (n+1)) (d h x : V (n+1)) :
    fourth (Joint u v r1 r2 c1 c2 A B) d (ind (i-5)) (ind (i+5)) h x =
      if B i then M 2 (R 3 d) (i+1) * M 2 (R 3 h) (i+5) + M 2 (R 3 d) (i+5) * M 2 (R 3 h) (i+1) else 0 := by
  have hcol := bankTop n 2 3 4 7 (by omega) (by omega) B v c1 c2 i d h x
  unfold Joint; rw [fourthSum, rowShort n hk, zero_add]
  simp only [tapForm] at hcol
  simp only [edge] at hcol
  convert hcol using 1 <;> push_cast <;> ring_nf

theorem twoPin (z : V k) (hz : M 1 z = 0) (q : ZMod k) (h0 : z q = 0) (h2 : z (q+2) = 0) : z = 0 := by
  have recur (t : ZMod k) : z (t+1) + z (t+2) + z t = 0 := by
    have he := congrFun hz (t+1)
    simpa only [M, Nat.cast_one, Pi.zero_apply, add_sub_cancel_right, show t+1+1=t+2 by ring] using he
  have h1 : z (q+1) = 0 := by simpa [h0,h2] using recur q
  apply window z 2 (by omega) q
  · intro t ih
    have ht0 := ih 0 (by omega); have ht1 := ih 1 (by omega)
    simp only [Nat.cast_zero, Nat.cast_one, add_zero] at ht0 ht1
    simpa [ht0,ht1] using recur t
  · intro a ha; interval_cases a <;> simpa using ‹_›

theorem quadGood (n : ℕ) (hk : 21 ≤ n+1) (u v r1 r2 c1 c2 : V (n+1)) (A B : ZMod (n+1) → Bool)
    (cover : ∀ j, ∃ i, B i = true ∧ (i+1 = j ∨ i+5 = j)) (d : V (n+1))
    (hq : Quad (dif (Joint u v r1 r2 c1 c2 A B) d)) :
    M 2 d = 0 ∧ ((∃ i, A i = true) → M 1 d = 0) := by
  have hc (i : ZMod (n+1)) (hb : B i = true) :
      raw 2 (edge 2 3 i) d 1 = 0 ∧ raw 2 (edge 2 3 i) d (1+2*2) = 0 := by
    apply rawZeros 2 (by omega) (by omega); intro h
    have h1 := fromQuad _ d hq (ind (i-5)) (ind (i+5)) h 0
    rw [jointTop n hk, if_pos hb] at h1
    simp only [tapForm]; convert h1 using 1 <;> push_cast <;> ring_nf
  have hcol : M 2 d = 0 := by
    apply R_eq_zero 3; rw [← M_R]; funext j; obtain ⟨i,hb,hj⟩ := cover j
    obtain ⟨hp,hs⟩ := hc i hb
    simp only [tapForm] at hp hs
    rcases hj with rfl | rfl
    · convert hp using 1 <;> push_cast <;> ring_nf
    · convert hs using 1 <;> push_cast <;> ring_nf
  refine ⟨hcol, ?_⟩; rintro ⟨i,ha⟩
  have he : raw 1 (edge 1 1 i) d 1 = 0 ∧ raw 1 (edge 1 1 i) d (1+2*1) = 0 := by
    apply rawZeros 1 (by omega) (by omega); intro h
    let left := ind (edge 1 1 i)
    let right := ind (edge 1 1 i + ((2+4*1 : ℕ) : ZMod (n+1)))
    have hh := fromQuad _ d hq left right h 0
    change fourth (fun w => obsZ A (bank 1 1 0 2 u r1 r2 w) + obsZ B (bank 2 3 4 7 v c1 c2 w)) _ _ _ _ _ = _ at hh
    rw [fourthSum, zerofourth _ d _ (fun w => congrFun (obsBankChange B 2 3 4 7 v c1 c2 d hcol) w), add_zero] at hh
    dsimp only [left, right] at hh
    rwa [bankTop n 1 1 0 2 (by omega) (by omega), if_pos ha] at hh
  obtain ⟨hp,hs⟩ := he; simp only [tapForm, M_R, R] at hp hs
  apply twoPin (M 1 d) (by rwa [squareM]) (i+1)
  · convert hp using 1 <;> push_cast <;> ring_nf
  · convert hs using 1 <;> push_cast <;> ring_nf

theorem fullCard (n : ℕ) (hk : 21 ≤ n+1) (A : ZMod (n+1) → Bool) (P : V (n+1) → Prop)
    (hp : ∀ d, P d ↔ M 2 d = 0 ∧ ((∃ i, A i = true) → M 1 d = 0)) :
    Nat.card {d // P d} = (if 3 ∣ n+1 then (if (∀ i, A i = false) ∧ 2 ∣ n+1 then 16 else 4) else 1) := by
  classical
  by_cases h3 : 3 ∣ n+1
  · rw [if_pos h3]; by_cases ha : ∃ i, A i = true
    · have hno : ¬ ((∀ i, A i = false) ∧ 2 ∣ n+1) := by
        obtain ⟨i,hi⟩ := ha; intro h; have := h.1 i; simp_all
      rw [if_neg hno, ← card1 h3 (by omega)]
      apply Nat.card_congr; apply Equiv.subtypeEquivRight; intro d
      rw [hp]; exact ⟨fun h => h.2 ha, fun h => ⟨by rw [← squareM,h,M_zero],fun _ => h⟩⟩
    · have off : ∀ i, A i = false := by intro i; cases hi : A i <;> simp_all
      have ee : Nat.card {d // P d} = Nat.card {d : V (n+1) // M 2 d = 0} := by
        apply Nat.card_congr; apply Equiv.subtypeEquivRight; intro d; simp [hp d,ha]
      rw [ee]; by_cases h2 : 2 ∣ n+1
      · rw [if_pos ⟨off,h2⟩]; exact card6 (by omega)
      · rw [if_neg (fun h => h2 h.2)]; exact card_odd h3 h2 (by omega)
  · rw [if_neg h3]; refine Eq.trans ?_ (card_triv 2 h3); apply Nat.card_congr; apply Equiv.subtypeEquivRight; intro d
    rw [hp]; refine ⟨And.left,fun h => ⟨h,fun _ => ?_⟩⟩; rw [ker_triv 2 h3 d h,M_zero]

end PEqualNP.Outside.L_meta_32054

open PEqualNP.Outside.L_meta_32054

set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.L_meta_32054 : (∀ (k : ℕ) (hk : 0 < k), 21 ≤ k →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (s : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + s)) + x (ix (i.val + k - s % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let quad := fun (f : W → F) => ∀ (v : Fin 3 → W) (x : W), (List.ofFn v).foldl diff f x = 0
  let tap := fun (w : W) (j : ℕ) => mix 2 (rot 3 w) (ix j)
  ∀ (u v r₁ r₂ c₁ c₂ : W) (A B : Fin k → Bool),
    let obs := fun (a : Fin k → Bool) (w : W) => ∑ i : Fin k, if a i then w i else 0
    let f := fun w : W =>
      let row := step (mix 1 (rot 1 w + u)) + w + r₁
      let col := step (mix 2 (rot 3 w + v)) + rot 4 w + c₁
      obs A (step (mix 1 row) + rot 2 w + r₂) +
        obs B (step (mix 2 col) + rot 7 w + c₂)
    let unit := fun (i j : Fin k) => if j = i then (1 : F) else 0
    let rowOn := ∃ i : Fin k, A i = true
    let good := fun d : W => mix 2 d = 0 ∧ (rowOn → mix 1 d = 0)
    let response := fun d : W => obs A (rot 2 d) + obs B (rot 7 d)
    (∀ (i : Fin k) (d h x : W),
      diff (diff (diff (diff f d) (unit (ix (i.val+k-5)))) (unit (ix (i.val+5)))) h x =
        if B i then tap d (i.val+1)*tap h (i.val+5) + tap d (i.val+5)*tap h (i.val+1) else 0) ∧
    ((∀ j : Fin k, ∃ i : Fin k, B i = true ∧ (ix (i.val+1) = j ∨ ix (i.val+5) = j)) →
      (∀ d : W, quad (diff f d) ↔ good d) ∧
      (∀ (d : W) (a : F), (∀ w : W, diff f d w = a) ↔ good d ∧ a = response d) ∧
      Nat.card {d : W // ∃ a : F, ∀ w : W, diff f d w = a} =
        (if 3 ∣ k then (if (∀ i, A i = false) ∧ 2 ∣ k then 16 else 4) else 1))) := by
  intro k hk hk21
  obtain ⟨n,rfl⟩ : ∃ n, k = n+1 := ⟨k-1, by omega⟩
  intro F W ixL rotL mixL stepL diffL quadL tapL u v r1 r2 c1 c2 A B obsL f unit rowOn good response
  have hr (s : ℕ) : rotL s = R (k := n+1) s := rotFin n s
  have hm (g : ℕ) : mixL g = M (k := n+1) g := mixFin n g
  have hs : stepL = st (k := n+1) := stepFin n
  have hzero (w : V (n+1)) : R 0 w = w := by funext j; simp [R]
  have hf : f = Joint (k := n+1) u v r1 r2 c1 c2 A B := by
    funext w; simp only [f, Joint, bank, hr, hm, hs]; rw [hzero w]; rfl
  have hgood (d : W) : good d ↔ M (k := n+1) 2 d = 0 ∧ ((∃ i, A i = true) → M (k := n+1) 1 d = 0) := by
    simp only [good,rowOn,hm]; rfl
  have hresp (d : W) : response d = obsZ (k := n+1) A (R 2 d) + obsZ (k := n+1) B (R 7 d) := by
    simp only [response,hr]; rfl
  constructor
  · intro i d h x
    let iz : ZMod (n+1) := i
    have hminus : @Eq (ZMod (n+1)) (ixL (i.val+(n+1)-5)) (iz-5) := by
      have hh := ix_sub n 5 i
      rw [Nat.mod_eq_of_lt (show 5 < n+1 by omega)] at hh; exact hh
    have plus1 : @Eq (ZMod (n+1)) (ixL (i.val+1)) (iz+1) := ix_one n iz
    have plus5 : @Eq (ZMod (n+1)) (ixL (i.val+5)) (iz+5) := ix_eq n 5 iz
    have tap1 (w : W) : tapL w (i.val+1) = M (k := n+1) 2 (R 3 w) (iz+1) := by
      change mixL 2 (rotL 3 w) (ixL (i.val+1)) = _; rw [hm,hr]; exact congrArg (M (k := n+1) 2 (R 3 w)) plus1
    have tap5 (w : W) : tapL w (i.val+5) = M (k := n+1) 2 (R 3 w) (iz+5) := by
      change mixL 2 (rotL 3 w) (ixL (i.val+5)) = _; rw [hm,hr]; exact congrArg (M (k := n+1) 2 (R 3 w)) plus5
    rw [tap1 d,tap5 h,tap5 d,tap1 h]
    change fourth (X := V (n+1)) f d (ind _) (ind _) h x = _
    rw [hf,hminus,plus5]; exact jointTop n hk21 u v r1 r2 c1 c2 A B iz d h x
  · intro cover
    have cov : ∀ j : ZMod (n+1), ∃ i : ZMod (n+1), B i = true ∧ (i+1 = j ∨ i+5 = j) := by
      intro j; obtain ⟨i,hb,hj⟩ := cover j; refine ⟨i,hb,?_⟩
      rcases hj with h | h
      · exact Or.inl ((ix_one n i).symm.trans h)
      · exact Or.inr ((ix_eq n 5 i).symm.trans h)
    have forward (d : W) (hg : good d) (w : W) : diffL f d w = response d := by
      change dif f d w = _; rw [hf,hresp]; exact goodResponse _ _ _ _ _ _ _ _ _ ((hgood d).mp hg) w
    have reverse (d : W) (hq : quadL (diffL f d)) : good d := by
      apply (hgood d).mpr; apply quadGood n hk21 u v r1 r2 c1 c2 A B cov d
      change Quad (dif f d) at hq; rwa [hf] at hq
    have classify (d : W) (a : F) : (∀ w, diffL f d w = a) ↔ good d ∧ a = response d := by
      constructor
      · intro hh; have hg := reverse d (constQuad (dif f d) a hh)
        exact ⟨hg,(hh 0).symm.trans (forward d hg 0)⟩
      · rintro ⟨hg,rfl⟩; exact forward d hg
    refine ⟨fun d => ⟨reverse d,fun hg => constQuad (dif f d) _ (forward d hg)⟩,classify,?_⟩
    let pred : V (n+1) → Prop := fun d => ∃ a : F, ∀ w : W, diffL f d w = a
    have hp (d : V (n+1)) : pred d ↔ M 2 d = 0 ∧ ((∃ i : ZMod (n+1), A i = true) → M 1 d = 0) := by
      refine Iff.trans ?_ (hgood d)
      exact ⟨fun ⟨a,ha⟩ => ((classify d a).mp ha).1,fun hg => ⟨_,forward d hg⟩⟩
    refine (fullCard n hk21 A pred hp).trans ?_
    by_cases h3 : 3 ∣ n+1
    · rw [if_pos h3, if_pos h3]
      by_cases h : (∀ i : Fin (n+1), A i = false) ∧ 2 ∣ n+1
      · have hz : (∀ i : ZMod (n+1), A i = false) ∧ 2 ∣ n+1 := h
        rw [if_pos h]; exact if_pos hz
      · have hz : ¬ ((∀ i : ZMod (n+1), A i = false) ∧ 2 ∣ n+1) := h
        rw [if_neg h]; exact if_neg hz
    · rw [if_neg h3,if_neg h3]
