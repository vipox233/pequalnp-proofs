import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_32051_aux

abbrev F := ZMod 2

def diff {E : Type*} [Add E] (f : E → F) (u x : E) : F := f (x + u) - f x

def Vanishes {E : Type*} [Add E] : ℕ → (E → F) → Prop
  | 0, f => ∀ x, f x = 0
  | n + 1, f => ∀ u, Vanishes n (diff f u)

section Difference

variable {E : Type*} [AddCommMonoid E]

theorem zero_v (n : ℕ) : Vanishes n (fun _ : E => 0) := by
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro u
    have same : diff (fun _ : E => 0) u = fun _ => 0 := by funext x; simp [diff]
    rw [same]
    exact ih

theorem succ_v {f : E → F} {n : ℕ} (hf : Vanishes n f) : Vanishes (n + 1) f := by
  induction n generalizing f with
  | zero =>
    have same : f = fun _ => 0 := funext hf
    rw [same]
    exact zero_v 1
  | succ n ih =>
    intro u
    exact ih (hf u)

theorem le_v {f : E → F} {n m : ℕ} (hf : Vanishes n f) (h : n ≤ m) : Vanishes m f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact succ_v ih

theorem const_v (c : F) : Vanishes 1 (fun _ : E => c) := by
  intro u x
  simp [diff]

theorem plus_v {f g : E → F} {n : ℕ} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero =>
    intro x
    change f x + g x = 0
    rw [hf x, hg x, add_zero]
  | succ n ih =>
    intro u
    have same : diff (fun x => f x + g x) u = fun x => diff f u x + diff g u x := by
      funext x
      unfold diff
      ring
    rw [same]
    exact ih (hf u) (hg u)

theorem sub_v {f g : E → F} {n : ℕ} (hf : Vanishes n f) (hg : Vanishes n g) :
    Vanishes n (fun x => f x - g x) := by
  induction n generalizing f g with
  | zero =>
    intro x
    change f x - g x = 0
    rw [hf x, hg x, sub_zero]
  | succ n ih =>
    intro u
    have same : diff (fun x => f x - g x) u = fun x => diff f u x - diff g u x := by
      funext x
      unfold diff
      ring
    rw [same]
    exact ih (hf u) (hg u)

theorem shift_v {f : E → F} {n : ℕ} (hf : Vanishes n f) (a : E) :
    Vanishes n (fun x => f (x + a)) := by
  induction n generalizing f with
  | zero => intro x; exact hf (x + a)
  | succ n ih =>
    intro u
    have same : diff (fun x => f (x + a)) u = fun x => diff f u (x + a) := by
      funext x
      simp only [diff, add_right_comm]
    rw [same]
    exact ih (hf u)

theorem mul_v (m n : ℕ) {f g : E → F}
    (hf : Vanishes (m + 1) f) (hg : Vanishes (n + 1) g) :
    Vanishes (m + n + 1) (fun x => f x * g x) := by
  suffices aux : ∀ t m n : ℕ, m + n = t → ∀ f g : E → F,
      Vanishes (m + 1) f → Vanishes (n + 1) g →
      Vanishes (m + n + 1) (fun x => f x * g x) by
    exact aux (m + n) m n rfl f g hf hg
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro m n total f g hf hg u
    have rule : diff (fun x => f x * g x) u =
        (fun x => diff f u x * g (x + u) + f x * diff g u x) := by
      funext x
      unfold diff
      ring
    rw [rule]
    apply plus_v
    · cases m with
      | zero =>
        have hzero : (fun x => diff f u x * g (x + u)) = fun _ => 0 := by
          funext x
          change diff f u x * g (x + u) = 0
          rw [hf u x, zero_mul]
        rw [hzero]
        exact zero_v _
      | succ m =>
        have smaller := ih (m + n) (by omega) m n rfl _ _ (hf u) (shift_v hg u)
        simpa only [Nat.succ_add] using smaller
    · cases n with
      | zero =>
        have hzero : (fun x => f x * diff g u x) = fun _ => 0 := by
          funext x
          change f x * diff g u x = 0
          rw [hg u x, mul_zero]
        rw [hzero]
        exact zero_v _
      | succ n =>
        exact ih (m + n) (by omega) m n rfl _ _ hf (hg u)

theorem lin_v {g : E → F} (h : ∀ a b, g (a + b) = g a + g b) : Vanishes 2 g := by
  intro u
  have same : diff g u = fun _ => g u := by
    funext x
    simp only [diff, h]
    ring
  rw [same]
  exact const_v _

theorem const2_v (c : F) : Vanishes 2 (fun _ : E => c) := succ_v (const_v c)

theorem cmul_v {g : E → F} {n : ℕ} (c : F) (hg : Vanishes (n + 1) g) :
    Vanishes (n + 1) (fun x => c * g x) := by
  have h := mul_v 0 n (const_v c) hg
  simpa only [Nat.zero_add] using h

end Difference

theorem bit_cases (a : F) : a = 0 ∨ a = 1 := by
  revert a; decide

theorem self_plus_bit (a : F) : a + a = 0 := by
  revert a; decide

theorem eq_of_add_eq_zero_bit {a b : F} (h : a + b = 0) : a = b := by
  revert h; revert a b; decide

theorem quartic_identity (a b c d e : F) :
    (a*b+b*c+c*d)*(b*c+c*d+d*e) - b*d*(a+c)*(c+e) =
      a*b*c + b*c + b*c*d + c*d + c*d*e := by
  decide +revert +kernel

abbrev W (k : ℕ) := Fin k → F

section Cyclic

variable {k : ℕ} [NeZero k]

def sh (i : Fin k) (n : ℕ) : Fin k := ⟨(i.val + n) % k, Nat.mod_lt _ (NeZero.pos k)⟩

theorem sh_val (i : Fin k) (n : ℕ) : (sh i n).val = (i.val + n) % k := rfl

theorem sh_sh (i : Fin k) (a b : ℕ) : sh (sh i a) b = sh i (a + b) := by
  apply Fin.ext
  simp only [sh_val]
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem sh_zero (i : Fin k) : sh i 0 = i := by
  apply Fin.ext
  simp [sh_val, Nat.mod_eq_of_lt i.isLt]

theorem sh_congr (i : Fin k) {a b : ℕ} (h : a % k = b % k) : sh i a = sh i b := by
  apply Fin.ext
  simp only [sh_val]
  rw [Nat.add_mod, h, ← Nat.add_mod]

theorem sh_eq_iff (i : Fin k) (a b : ℕ) : sh i a = sh i b ↔ a % k = b % k := by
  constructor
  · intro h
    have h2 := congrArg Fin.val h
    simp only [sh_val] at h2
    exact Nat.ModEq.add_left_cancel' i.val h2
  · exact sh_congr i

theorem sh_add_k (i : Fin k) (n : ℕ) : sh i (k + n) = sh i n :=
  sh_congr i (by simp)

theorem sh_k (i : Fin k) : sh i k = i := by
  rw [← sh_zero i, sh_sh]
  exact sh_congr _ (by simp)

theorem sh_of (i0 i : Fin k) : sh i0 ((i.val + k - i0.val) % k) = i := by
  apply Fin.ext
  simp only [sh_val]
  have h1 := i.isLt
  have h2 := i0.isLt
  rw [Nat.add_mod_mod]
  rw [show i0.val + (i.val + k - i0.val) = i.val + k by omega]
  simp [Nat.mod_eq_of_lt h1]

theorem sh_pred (i0 : Fin k) (n : ℕ) (h1 : 1 ≤ n) : sh (sh i0 (k - 1)) n = sh i0 (n - 1) := by
  rw [sh_sh, show k - 1 + n = k + (n - 1) by have := NeZero.pos k; omega, sh_add_k]

theorem small_mod (n : ℕ) (h : n < k + k) :
    n % k = if n < k then n else n - k := by
  split
  · exact Nat.mod_eq_of_lt ‹n < k›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem single_sh (i0 : Fin k) (a b : ℕ) :
    (Pi.single (sh i0 a) (1 : F) : W k) (sh i0 b) = if b % k = a % k then 1 else 0 := by
  simp only [Pi.single_apply, sh_eq_iff]

end Cyclic

section Model

variable {k : ℕ} [NeZero k]

def shm (i : Fin k) : Fin k := ⟨(i.val + k - 1) % k, Nat.mod_lt _ (NeZero.pos k)⟩

def rotF (s : ℕ) (x : W k) : W k := fun i => x ⟨(i.val + k - s % k) % k, Nat.mod_lt _ (NeZero.pos k)⟩

def mixF (x : W k) : W k := fun i => x i + x (sh i 1) + x (shm i)

def stepF (x : W k) : W k := fun i => x i + (1 + x (sh i 1)) * x (sh i 2)

def fF (name c₁ c₂ : W k) (mark : Fin k → Bool) (w : W k) : F :=
  let first := stepF (mixF (rotF 1 w + name)) + w + c₁
  let last := stepF (mixF first) + rotF 2 w + c₂
  ∑ i : Fin k, if mark i then last i else 0

theorem shm_eq (i : Fin k) : shm i = sh i (k - 1) := by
  apply Fin.ext
  simp only [shm, sh_val]
  have := NeZero.pos k
  congr 1
  omega

theorem rot_eq (s : ℕ) (x : W k) (i : Fin k) : rotF s x i = x (sh i (k - s % k)) := by
  have h := Nat.mod_lt s (NeZero.pos k)
  simp only [rotF]
  congr 1
  apply Fin.ext
  simp only [sh_val]
  congr 1
  omega

theorem mix_add (x y : W k) : mixF (x + y) = mixF x + mixF y := by
  funext i
  simp only [mixF, Pi.add_apply]
  ring

theorem rot_add (s : ℕ) (x y : W k) : rotF s (x + y) = rotF s x + rotF s y := by
  funext i
  simp only [rotF, Pi.add_apply]

def Zf (x : W k) : W k := mixF (rotF 1 x)

theorem Zf_add (x y : W k) : Zf (x + y) = Zf x + Zf y := by
  simp only [Zf, rot_add, mix_add]

theorem Zf_add_apply (x y : W k) (j : Fin k) : Zf (x + y) j = Zf x j + Zf y j := by
  rw [Zf_add]; rfl

theorem shm_sh (i : Fin k) (a : ℕ) : shm (sh i (a + 1)) = sh i a := by
  rw [shm_eq, sh_sh, show a + 1 + (k - 1) = k + a by have := NeZero.pos k; omega, sh_add_k]

theorem shm_sh1 (i : Fin k) : shm (sh i 1) = i := by
  have h := shm_sh i 0
  rw [sh_zero] at h
  simpa using h

variable (name c₁ c₂ : W k)

def firstF (w : W k) : W k := stepF (mixF (rotF 1 w + name)) + w + c₁

def lastF (w : W k) : W k := stepF (mixF (firstF name c₁ w)) + rotF 2 w + c₂

def Aq (j : Fin k) (w : W k) : F :=
  Zf w j + mixF name j + (1 + mixF name (sh j 1)) * Zf w (sh j 2) +
    mixF name (sh j 2) * Zf w (sh j 1) + (1 + mixF name (sh j 1)) * mixF name (sh j 2) +
    w j + c₁ j

def qq (j : Fin k) (w : W k) : F := Zf w (sh j 1) * Zf w (sh j 2)

theorem first_eq (w : W k) (j : Fin k) : firstF name c₁ w j = Aq name c₁ j w + qq j w := by
  have z (i : Fin k) : mixF (rotF 1 w + name) i = Zf w i + mixF name i := by
    rw [mix_add]; rfl
  simp only [firstF, stepF, Pi.add_apply, z, Aq, qq]
  ring

theorem Zf_lin (j : Fin k) : Vanishes 2 (fun w : W k => Zf w j) := by
  apply lin_v
  intro a b
  exact Zf_add_apply a b j

theorem Aq_v (j : Fin k) : Vanishes 2 (Aq name c₁ j) := by
  unfold Aq
  apply plus_v
  · apply plus_v
    · apply plus_v
      · apply plus_v
        · apply plus_v
          · apply plus_v
            · exact Zf_lin j
            · exact const2_v _
          · exact cmul_v _ (Zf_lin _)
        · exact cmul_v _ (Zf_lin _)
      · exact const2_v _
    · apply lin_v
      intro a b
      rfl
  · exact const2_v _

theorem qq_v (j : Fin k) : Vanishes 3 (qq (k := k) j) :=
  mul_v 1 1 (Zf_lin _) (Zf_lin _)

def Bq (j : Fin k) (w : W k) : F := Aq name c₁ j w + Aq name c₁ (sh j 1) w + Aq name c₁ (shm j) w

def Qq (j : Fin k) (w : W k) : F := qq j w + qq (sh j 1) w + qq (shm j) w

theorem Bq_v (j : Fin k) : Vanishes 2 (Bq name c₁ j) :=
  plus_v (plus_v (Aq_v _ _ _) (Aq_v _ _ _)) (Aq_v _ _ _)

theorem Qq_v (j : Fin k) : Vanishes 3 (Qq (k := k) j) :=
  plus_v (plus_v (qq_v _) (qq_v _)) (qq_v _)

theorem mix_first (w : W k) (j : Fin k) :
    mixF (firstF name c₁ w) j = Bq name c₁ j w + Qq j w := by
  simp only [mixF, first_eq, Bq, Qq]
  ring

def tt (i : Fin k) (n : ℕ) (w : W k) : F := Zf w (sh i n)

theorem Qq_one (i : Fin k) (w : W k) :
    Qq (sh i 1) w = tt i 1 w * tt i 2 w + tt i 2 w * tt i 3 w + tt i 3 w * tt i 4 w := by
  simp only [Qq, qq, tt, shm_sh1, sh_sh]
  ring

theorem Qq_two (i : Fin k) (w : W k) :
    Qq (sh i 2) w = tt i 2 w * tt i 3 w + tt i 3 w * tt i 4 w + tt i 4 w * tt i 5 w := by
  have h : shm (sh i 2) = sh i 1 := shm_sh i 1
  simp only [Qq, qq, tt, h, sh_sh]
  ring

def Tq (i : Fin k) (w : W k) : F :=
  tt i 2 w * tt i 4 w * (tt i 1 w + tt i 3 w) * (tt i 3 w + tt i 5 w)

def restF (i : Fin k) (w : W k) : F :=
  ((Bq name c₁ i w + Qq i w + Bq name c₁ (sh i 2) w + Qq (sh i 2) w +
        Bq name c₁ (sh i 1) w * Bq name c₁ (sh i 2) w +
        Bq name c₁ (sh i 1) w * Qq (sh i 2) w + Qq (sh i 1) w * Bq name c₁ (sh i 2) w +
        (rotF 2 w i + c₂ i)) +
      (tt i 1 w * tt i 2 w * tt i 3 w + tt i 2 w * tt i 3 w + tt i 2 w * tt i 3 w * tt i 4 w +
        tt i 3 w * tt i 4 w + tt i 3 w * tt i 4 w * tt i 5 w))

theorem last_split (w : W k) (i : Fin k) :
    lastF name c₁ c₂ w i = Tq i w + restF name c₁ c₂ i w := by
  have hq := quartic_identity (tt i 1 w) (tt i 2 w) (tt i 3 w) (tt i 4 w) (tt i 5 w)
  rw [← Qq_one, ← Qq_two] at hq
  have e : lastF name c₁ c₂ w i = mixF (firstF name c₁ w) i +
      (1 + mixF (firstF name c₁ w) (sh i 1)) * mixF (firstF name c₁ w) (sh i 2) +
      rotF 2 w i + c₂ i := rfl
  rw [e, mix_first, mix_first, mix_first]
  unfold Tq restF
  rw [← hq]
  ring

theorem rot_lin (s : ℕ) (i : Fin k) : Vanishes 2 (fun w : W k => rotF s w i) := by
  apply lin_v
  intro a b
  rfl

theorem rest_v (i : Fin k) : Vanishes 4 (restF name c₁ c₂ i) := by
  have B2 (j : Fin k) : Vanishes 4 (Bq name c₁ j) := le_v (Bq_v _ _ j) (by omega)
  have Q3 (j : Fin k) : Vanishes 4 (Qq (k := k) j) := succ_v (Qq_v j)
  have T (n : ℕ) : Vanishes 2 (tt (k := k) i n) := Zf_lin _
  have T2 (a b : ℕ) : Vanishes 4 (fun w => tt i a w * tt i b w) := succ_v (mul_v 1 1 (T a) (T b))
  have T3 (a b c : ℕ) : Vanishes 4 (fun w => tt i a w * tt i b w * tt i c w) :=
    mul_v 2 1 (mul_v 1 1 (T a) (T b)) (T c)
  unfold restF
  apply plus_v
  · apply plus_v
    · apply plus_v
      · apply plus_v
        · apply plus_v
          · apply plus_v
            · apply plus_v
              · apply plus_v
                · exact B2 _
                · exact Q3 _
              · exact B2 _
            · exact Q3 _
          · exact succ_v (mul_v 1 1 (Bq_v _ _ _) (Bq_v _ _ _))
        · exact mul_v 1 2 (Bq_v _ _ _) (Qq_v _)
      · exact mul_v 2 1 (Qq_v _) (Bq_v _ _ _)
    · exact le_v (plus_v (rot_lin 2 i) (const2_v _)) (by omega)
  · exact plus_v (plus_v (plus_v (plus_v (T3 1 2 3) (T2 2 3)) (T3 2 3 4)) (T2 3 4)) (T3 3 4 5)

def D4 (g : W k → F) (a b c e x : W k) : F := diff (diff (diff (diff g a) b) c) e x

def perm3 (p1 p2 p3 q1 q2 q3 r1 r2 r3 : F) : F :=
  p1 * (q2 * r3 + q3 * r2) + p2 * (q1 * r3 + q3 * r1) + p3 * (q1 * r2 + q2 * r1)

def perm4 (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 e0 e1 e2 e3 : F) : F :=
  a0 * perm3 b1 b2 b3 c1 c2 c3 e1 e2 e3 + a1 * perm3 b0 b2 b3 c0 c2 c3 e0 e2 e3 +
    a2 * perm3 b0 b1 b3 c0 c1 c3 e0 e1 e3 + a3 * perm3 b0 b1 b2 c0 c1 c2 e0 e1 e2

theorem D4_add (g h : W k → F) (a b c e x : W k) :
    D4 (fun w => g w + h w) a b c e x = D4 g a b c e x + D4 h a b c e x := by
  simp only [D4, diff]
  ring

theorem diff_sum {ι : Type*} [Fintype ι] (g : ι → W k → F) (u : W k) :
    diff (fun w => ∑ i, g i w) u = fun x => ∑ i, diff (g i) u x := by
  funext x
  simp only [diff, Finset.sum_sub_distrib]

theorem D4_sum {ι : Type*} [Fintype ι] (g : ι → W k → F) (a b c e x : W k) :
    D4 (fun w => ∑ i, g i w) a b c e x = ∑ i, D4 (g i) a b c e x := by
  simp only [D4, diff_sum]

theorem D4_ite (m : Bool) (g : W k → F) (a b c e x : W k) :
    D4 (fun w => if m then g w else 0) a b c e x = if m then D4 g a b c e x else 0 := by
  cases m
  · simp [D4, diff]
  · simp

theorem D4_prod (L0 L1 L2 L3 : W k → F)
    (h0 : ∀ a b, L0 (a + b) = L0 a + L0 b) (h1 : ∀ a b, L1 (a + b) = L1 a + L1 b)
    (h2 : ∀ a b, L2 (a + b) = L2 a + L2 b) (h3 : ∀ a b, L3 (a + b) = L3 a + L3 b)
    (a b c e x : W k) :
    D4 (fun w => L0 w * L1 w * L2 w * L3 w) a b c e x =
      perm4 (L0 a) (L1 a) (L2 a) (L3 a) (L0 b) (L1 b) (L2 b) (L3 b)
        (L0 c) (L1 c) (L2 c) (L3 c) (L0 e) (L1 e) (L2 e) (L3 e) := by
  simp only [D4, diff, h0, h1, h2, h3, perm4, perm3]
  ring

def P4 (i : Fin k) (Y0 Y1 Y2 Y3 : W k) : F :=
  perm4 (Y0 (sh i 2)) (Y0 (sh i 4)) (Y0 (sh i 1) + Y0 (sh i 3)) (Y0 (sh i 3) + Y0 (sh i 5))
    (Y1 (sh i 2)) (Y1 (sh i 4)) (Y1 (sh i 1) + Y1 (sh i 3)) (Y1 (sh i 3) + Y1 (sh i 5))
    (Y2 (sh i 2)) (Y2 (sh i 4)) (Y2 (sh i 1) + Y2 (sh i 3)) (Y2 (sh i 3) + Y2 (sh i 5))
    (Y3 (sh i 2)) (Y3 (sh i 4)) (Y3 (sh i 1) + Y3 (sh i 3)) (Y3 (sh i 3) + Y3 (sh i 5))

theorem D4_last (i : Fin k) (a b c e x : W k) :
    D4 (fun w => lastF name c₁ c₂ w i) a b c e x = P4 i (Zf a) (Zf b) (Zf c) (Zf e) := by
  have split : (fun w => lastF name c₁ c₂ w i) = fun w => Tq i w + restF name c₁ c₂ i w := by
    funext w
    exact last_split name c₁ c₂ w i
  rw [split, D4_add]
  have zero := rest_v name c₁ c₂ i a b c e x
  change _ + D4 _ a b c e x = _
  unfold D4
  rw [zero, add_zero]
  have hT (n : ℕ) (u v : W k) : tt i n (u + v) = tt i n u + tt i n v := Zf_add_apply u v _
  have := D4_prod (fun w => tt i 2 w) (fun w => tt i 4 w) (fun w => tt i 1 w + tt i 3 w)
    (fun w => tt i 3 w + tt i 5 w) (hT 2) (hT 4)
    (fun u v => by simp only [hT]; ring) (fun u v => by simp only [hT]; ring) a b c e x
  unfold D4 at this
  unfold Tq
  rw [this]
  rfl

theorem D4_f (mark : Fin k → Bool) (a b c e x : W k) :
    D4 (fF name c₁ c₂ mark) a b c e x =
      ∑ i, if mark i then P4 i (Zf a) (Zf b) (Zf c) (Zf e) else 0 := by
  have hf : fF name c₁ c₂ mark = fun w => ∑ i, if mark i then lastF name c₁ c₂ w i else 0 := rfl
  rw [hf, D4_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [D4_ite, D4_last]

end Model

theorem weight_bound {k : ℕ} (h : W k → F) (h4 : Vanishes 4 h) (h3 : ¬ Vanishes 3 h) :
    2 ^ k ≤ 8 * Nat.card {w : W k // h w ≠ 0} := by
  classical
  obtain ⟨u1, u2, u3, x0, hx0⟩ : ∃ u1 u2 u3 x0, diff (diff (diff h u1) u2) u3 x0 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h3 (fun u1 u2 u3 x => hc u1 u2 u3 x)
  have step : ∀ x u, diff (diff (diff h u1) u2) u3 (x + u) = diff (diff (diff h u1) u2) u3 x := by
    intro x u
    have e := h4 u1 u2 u3 u x
    exact sub_eq_zero.mp e
  have const : ∀ x, diff (diff (diff h u1) u2) u3 x = diff (diff (diff h u1) u2) u3 x0 := by
    intro x
    have e := step x0 (x - x0)
    rwa [add_sub_cancel] at e
  let o : Fin 8 → W k := ![u3 + u2 + u1, u3 + u2, u3 + u1, u3, u2 + u1, u2, u1, 0]
  have cover : ∀ x, ∃ m : Fin 8, h (x + o m) ≠ 0 := by
    intro x
    by_contra hc
    push Not at hc
    apply hx0
    rw [← const x]
    have p0 : h (x + u3 + u2 + u1) = 0 := by simpa [o, add_assoc] using hc 0
    have p1 : h (x + u3 + u2) = 0 := by simpa [o, add_assoc] using hc 1
    have p2 : h (x + u3 + u1) = 0 := by simpa [o, add_assoc] using hc 2
    have p3 : h (x + u3) = 0 := by simpa [o, add_assoc] using hc 3
    have p4 : h (x + u2 + u1) = 0 := by simpa [o, add_assoc] using hc 4
    have p5 : h (x + u2) = 0 := by simpa [o, add_assoc] using hc 5
    have p6 : h (x + u1) = 0 := by simpa [o, add_assoc] using hc 6
    have p7 : h x = 0 := by simpa [o, add_assoc] using hc 7
    simp only [diff, p0, p1, p2, p3, p4, p5, p6, p7]
    ring
  have card_B : ∀ m, (Finset.univ.filter (fun x => h (x + o m) ≠ 0)).card =
      (Finset.univ.filter (fun w => h w ≠ 0)).card := by
    intro m
    apply Finset.card_bij (fun x _ => x + o m)
    · intro x hx
      simpa using hx
    · intro a _ b _ hab
      exact add_right_cancel hab
    · intro y hy
      refine ⟨y - o m, ?_, ?_⟩
      · simpa using hy
      · simp
  have hcov : (Finset.univ : Finset (W k)) ⊆
      Finset.univ.biUnion (fun m : Fin 8 => Finset.univ.filter (fun x => h (x + o m) ≠ 0)) := by
    intro x _
    obtain ⟨m, hm⟩ := cover x
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨m, hm⟩
  have bound := (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  simp only [card_B, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at bound
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hW : Fintype.card (W k) = 2 ^ k := by simp
  omega

section Kernel

variable {k : ℕ} [NeZero k]

theorem per3 (a b c d : F) (h1 : a + b + c = 0) (h2 : b + d + a = 0) : d = c := by
  revert a b c d; decide

theorem mix_period (y : W k) (hy : mixF y = 0) (i : Fin k) : y (sh i 3) = y i := by
  have e1 := congrFun hy (sh i 1)
  have e2 := congrFun hy (sh i 2)
  have h2 : shm (sh i 2) = sh i 1 := shm_sh i 1
  simp only [mixF, sh_sh, shm_sh1, h2, Pi.zero_apply] at e1 e2
  exact per3 _ _ _ _ e1 e2

theorem mix_period_mul (y : W k) (hy : mixF y = 0) (i : Fin k) (m : ℕ) :
    y (sh i (3 * m)) = y i := by
  induction m with
  | zero => rw [Nat.mul_zero, sh_zero]
  | succ m ih =>
    rw [show 3 * (m + 1) = 3 * m + 3 by ring, ← sh_sh, mix_period y hy, ih]

theorem sh_zero_val (j : Fin k) : sh (0 : Fin k) j.val = j := by
  apply Fin.ext
  simp [sh_val, Nat.mod_eq_of_lt j.isLt]

theorem three_bit (a : F) (h : a + a + a = 0) : a = 0 := by
  revert a h; decide

theorem mix_ker_trivial (h3 : ¬ 3 ∣ k) (y : W k) (hy : mixF y = 0) : y = 0 := by
  have hk := NeZero.pos k
  have one : ∀ i, y (sh i 1) = y i := by
    intro i
    rcases (show k % 3 = 1 ∨ k % 3 = 2 by omega) with h | h
    · have e := mix_period_mul y hy (sh i 1) ((k - 1) / 3)
      rw [show 3 * ((k - 1) / 3) = k - 1 by omega, sh_sh,
        show 1 + (k - 1) = k by omega, sh_k] at e
      exact e.symm
    · have e := mix_period_mul y hy i ((k + 1) / 3)
      rw [show 3 * ((k + 1) / 3) = k + 1 by omega, sh_add_k] at e
      exact e
  have all : ∀ i (n : ℕ), y (sh i n) = y i := by
    intro i n
    induction n with
    | zero => rw [sh_zero]
    | succ n ih => rw [← sh_sh, one, ih]
  have c0 : y 0 = 0 := by
    have e := congrFun hy 0
    simp only [mixF, Pi.zero_apply, all] at e
    rw [shm_eq, all] at e
    exact three_bit _ e
  funext j
  rw [← sh_zero_val j, all, c0]
  rfl

def pat (a b : F) (i : Fin k) : F :=
  if i.val % 3 = 0 then a else if i.val % 3 = 1 then b else a + b

theorem pat_mix (h3 : 3 ∣ k) (a b : F) : mixF (pat (k := k) a b) = 0 := by
  have hk := NeZero.pos k
  funext i
  have h1 : (sh i 1).val % 3 = (i.val + 1) % 3 := by rw [sh_val, Nat.mod_mod_of_dvd _ h3]
  have h2 : (shm i).val % 3 = (i.val + 2) % 3 := by
    simp only [shm]
    rw [Nat.mod_mod_of_dvd _ h3]
    obtain ⟨c, hc⟩ := h3
    omega
  simp only [mixF, pat, h1, h2, Pi.zero_apply]
  rcases (show i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 by omega) with h | h | h
  · rw [if_pos h, if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega)]
    revert a b; decide
  · rw [if_neg (by omega), if_pos h, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    revert a b; decide
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      if_pos (by omega)]
    revert a b; decide

theorem ker_eq_pat (h3 : 3 ∣ k) (y : W k) (hy : mixF y = 0) :
    pat (y 0) (y (sh 0 1)) = y := by
  have hk := NeZero.pos k
  have k3 : 3 ≤ k := Nat.le_of_dvd hk h3
  have y2 : y (sh 0 2) = y 0 + y (sh 0 1) := by
    have e := congrFun hy (sh 0 1)
    simp only [mixF, sh_sh, shm_sh1, Pi.zero_apply] at e
    revert e
    generalize y (sh 0 1) = a
    generalize y (sh 0 2) = b
    generalize y 0 = c
    revert a b c; decide
  funext j
  have hj : y j = y (sh 0 (j.val % 3)) := by
    conv_lhs => rw [← sh_zero_val j, ← Nat.mod_add_div j.val 3, ← sh_sh, mix_period_mul y hy]
  rw [hj]
  simp only [pat]
  rcases (show j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2 by omega) with h | h | h
  · rw [if_pos h, h, sh_zero]
  · rw [if_neg (by omega), if_pos h, h]
  · rw [if_neg (by omega), if_neg (by omega), h, y2]

theorem ker_card3 (h3 : 3 ∣ k) : Nat.card {y : W k // mixF y = 0} = 4 := by
  have hk := NeZero.pos k
  have k3 : 3 ≤ k := Nat.le_of_dvd hk h3
  have v1 : (sh (0 : Fin k) 1).val = 1 := by
    rw [sh_val]; simp [Nat.mod_eq_of_lt (show 1 < k by omega)]
  let e : {y : W k // mixF y = 0} ≃ F × F :=
    { toFun := fun y => (y.1 0, y.1 (sh 0 1))
      invFun := fun p => ⟨pat p.1 p.2, pat_mix h3 p.1 p.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        exact ker_eq_pat h3 y.1 y.2
      right_inv := by
        intro p
        simp only [pat, v1]
        simp }
  rw [Nat.card_congr e]
  simp

theorem ker_card1 (h3 : ¬ 3 ∣ k) : Nat.card {y : W k // mixF y = 0} = 1 := by
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · funext i; simp [mixF]
  · intro y
    apply Subtype.ext
    exact mix_ker_trivial h3 y.1 y.2

theorem sh_sub_eq_iff (j r : Fin k) (a : ℕ) (ha : a ≤ k) : sh j (k - a) = r ↔ j = sh r a := by
  constructor
  · rintro rfl
    rw [sh_sh, show k - a + a = k by omega, sh_k]
  · rintro rfl
    rw [sh_sh, show a + (k - a) = k by omega, sh_k]

theorem rot1_eq (hk2 : 2 ≤ k) (x : W k) (i : Fin k) : rotF 1 x i = x (sh i (k - 1)) := by
  rw [rot_eq, Nat.mod_eq_of_lt (by omega)]

theorem Zf_single (hk2 : 2 ≤ k) (r : Fin k) :
    Zf (Pi.single r (1 : F)) =
      Pi.single r 1 + Pi.single (sh r 1) 1 + Pi.single (sh r 2) 1 := by
  funext j
  have a1 : sh (sh j 1) (k - 1) = j := by
    rw [sh_sh, show 1 + (k - 1) = k by omega, sh_k]
  have a2 : sh (shm j) (k - 1) = sh j (k - 2) := by
    rw [shm_eq, sh_sh, show k - 1 + (k - 1) = k + (k - 2) by omega, sh_add_k]
  simp only [Zf, mixF, rot1_eq hk2, a1, a2, Pi.add_apply, Pi.single_apply,
    sh_sub_eq_iff j r 1 (by omega), sh_sub_eq_iff j r 2 (by omega)]
  ring

theorem bits4 (a b c d : F) : a + b + c + (b + c + d) = a + d := by
  revert a b c d; decide

theorem bits3 (a b c : F) : a + b + (b + c) = a + c := by
  revert a b c; decide

theorem Zf_zero : Zf (0 : W k) = 0 := by
  funext i; simp [Zf, mixF, rotF]

theorem Zf_pair (hk2 : 2 ≤ k) (r : Fin k) :
    Zf (Pi.single r (1 : F) + Pi.single (sh r 1) 1) = Pi.single r 1 + Pi.single (sh r 3) 1 := by
  rw [Zf_add, Zf_single hk2, Zf_single hk2, sh_sh, sh_sh]
  funext j
  simp only [Pi.add_apply]
  exact bits4 _ _ _ _

theorem pair_preimage (hk2 : 2 ≤ k) (p : Fin k) (m : ℕ) :
    ∃ v : W k, Zf v = Pi.single p 1 + Pi.single (sh p (3 * m)) 1 := by
  induction m with
  | zero =>
    refine ⟨0, ?_⟩
    rw [Zf_zero, Nat.mul_zero, sh_zero]
    funext j
    simp only [Pi.add_apply, Pi.zero_apply]
    exact (self_plus_bit _).symm
  | succ m ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨v + (Pi.single (sh p (3 * m)) 1 + Pi.single (sh (sh p (3 * m)) 1) 1), ?_⟩
    rw [Zf_add, hv, Zf_pair hk2, sh_sh, show 3 * m + 3 = 3 * (m + 1) by ring]
    funext j
    simp only [Pi.add_apply]
    exact bits3 _ _ _

theorem Zf_surj (hk2 : 2 ≤ k) (h3 : ¬ 3 ∣ k) (u : W k) : ∃ v, Zf v = u := by
  have inj : Function.Injective (Zf (k := k)) := by
    intro a b hab
    have e : Zf (a + b) = 0 := by
      rw [Zf_add, hab]
      funext j
      exact self_plus_bit _
    have r0 : rotF 1 (a + b) = 0 := mix_ker_trivial h3 _ e
    have ab : a + b = 0 := by
      funext j
      have := congrFun r0 (sh j 1)
      rwa [rot1_eq hk2, sh_sh, show 1 + (k - 1) = k by omega, sh_k] at this
    funext j
    exact eq_of_add_eq_zero_bit (congrFun ab j)
  exact Finite.injective_iff_surjective.mp inj u

end Kernel

section Tests

variable {k : ℕ} [NeZero k]

def Spot (i0 : Fin k) (U : W k) (a b : ℕ) : Prop :=
  U (sh i0 a) = 1 ∧ ∀ m, U (sh i0 m) ≠ 0 → m % k = a ∨ m % k = b

theorem spot_unit (i0 : Fin k) (a : ℕ) (ha : a < k) :
    Spot i0 (Pi.single (sh i0 a) (1 : F)) a a := by
  refine ⟨Pi.single_eq_same _ _, ?_⟩
  intro m hm
  rw [single_sh] at hm
  split_ifs at hm with h
  · left; rw [h, Nat.mod_eq_of_lt ha]
  · exact absurd rfl hm

theorem spot_pair (i0 : Fin k) (a b : ℕ) (ha : a < k) (hb : b < k) (hab : a ≠ b) :
    Spot i0 (Pi.single (sh i0 a) (1 : F) + Pi.single (sh i0 b) 1) a b := by
  refine ⟨?_, ?_⟩
  · simp [single_sh, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, hab]
  · intro m hm
    simp only [Pi.add_apply, single_sh, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm
    by_cases h1 : m % k = a
    · left; exact h1
    · by_cases h2 : m % k = b
      · right; exact h2
      · rw [if_neg h1, if_neg h2, add_zero] at hm
        exact absurd rfl hm

theorem spot_val {i0 : Fin k} {U : W k} {a b : ℕ} (hs : Spot i0 U a b) (ha : a < k)
    (hb : b = a ∨ 6 < b) (n : ℕ) (hn : n ≤ 6) (hnk : n < k) :
    U (sh i0 n) = if n = a then 1 else 0 := by
  by_cases h : n = a
  · subst h; rw [if_pos rfl]; exact hs.1
  · rw [if_neg h]
    by_contra hne
    rcases hs.2 n hne with e | e <;> rw [Nat.mod_eq_of_lt hnk] at e <;> omega

theorem spot_hit {i0 : Fin k} {U : W k} {a b : ℕ} (hs : Spot i0 U a b) (t : ℕ) (tk : t < k)
    (hk5 : 5 < k) :
    (∀ n, 1 ≤ n → n ≤ 5 → U (sh i0 (t + n)) = 0) ∨
      ∃ n, 1 ≤ n ∧ n ≤ 5 ∧ (t + n = a ∨ t + n = a + k ∨ t + n = b ∨ t + n = b + k) := by
  by_cases hall : ∀ n, 1 ≤ n → n ≤ 5 → U (sh i0 (t + n)) = 0
  · left; exact hall
  · right
    push Not at hall
    obtain ⟨n, h1, h5, hne⟩ := hall
    refine ⟨n, h1, h5, ?_⟩
    have e := hs.2 _ hne
    rw [small_mod (t + n) (by omega)] at e
    split_ifs at e <;> omega

theorem localize (mark : Fin k → Bool) (δ U1 U2 U3 : W k) (i0 : Fin k) (S : Finset (Fin k))
    (h : ∀ t, t < k → sh i0 t ∉ S →
      (∀ n, 1 ≤ n → n ≤ 5 → U1 (sh i0 (t + n)) = 0) ∨
      (∀ n, 1 ≤ n → n ≤ 5 → U2 (sh i0 (t + n)) = 0) ∨
      (∀ n, 1 ≤ n → n ≤ 5 → U3 (sh i0 (t + n)) = 0)) :
    ∑ i, (if mark i then P4 i δ U1 U2 U3 else 0) =
      ∑ i ∈ S, (if mark i then P4 i δ U1 U2 U3 else 0) := by
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro i _ hi
  have hi' : sh i0 ((i.val + k - i0.val) % k) = i := sh_of i0 i
  have tk : (i.val + k - i0.val) % k < k := Nat.mod_lt _ (NeZero.pos k)
  generalize (i.val + k - i0.val) % k = t at hi' tk
  subst hi'
  have taps : ∀ n, sh (sh i0 t) n = sh i0 (t + n) := fun n => sh_sh _ _ _
  rcases h t tk hi with z | z | z
  · simp [P4, taps, z 1 (by norm_num) (by norm_num), z 2 (by norm_num) (by norm_num),
      z 3 (by norm_num) (by norm_num), z 4 (by norm_num) (by norm_num),
      z 5 (by norm_num) (by norm_num), perm4, perm3]
  · simp [P4, taps, z 1 (by norm_num) (by norm_num), z 2 (by norm_num) (by norm_num),
      z 3 (by norm_num) (by norm_num), z 4 (by norm_num) (by norm_num),
      z 5 (by norm_num) (by norm_num), perm4, perm3]
  · simp [P4, taps, z 1 (by norm_num) (by norm_num), z 2 (by norm_num) (by norm_num),
      z 3 (by norm_num) (by norm_num), z 4 (by norm_num) (by norm_num),
      z 5 (by norm_num) (by norm_num), perm4, perm3]

theorem get_cols (hk : 10 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (i0 : Fin k) (a1 a2 a3 : ℕ)
    (h1 : a1 ≤ 5) (h2 : a2 ≤ 5) (h3' : a3 ≤ 5) :
    ∃ v1 v2 v3 : W k, ∃ b1 b2 b3 : ℕ, Spot i0 (Zf v1) a1 b1 ∧ Spot i0 (Zf v2) a2 b2 ∧
      Spot i0 (Zf v3) a3 b3 ∧
      ((b1 = a1 ∧ b2 = a2 ∧ b3 = a3) ∨ (30 ≤ k ∧ b1 = a1 + 9 ∧ b2 = a2 + 15 ∧ b3 = a3 + 21)) := by
  by_cases hd : 3 ∣ k
  · have hk30 : 30 ≤ k := by
      rcases h3 with h | h
      · exact absurd hd h
      · exact h
    obtain ⟨v1, e1⟩ := pair_preimage (by omega) (sh i0 a1) 3
    obtain ⟨v2, e2⟩ := pair_preimage (by omega) (sh i0 a2) 5
    obtain ⟨v3, e3⟩ := pair_preimage (by omega) (sh i0 a3) 7
    rw [sh_sh] at e1 e2 e3
    refine ⟨v1, v2, v3, a1 + 9, a2 + 15, a3 + 21, ?_, ?_, ?_, Or.inr ⟨hk30, rfl, rfl, rfl⟩⟩
    · rw [e1]; exact spot_pair _ _ _ (by omega) (by omega) (by omega)
    · rw [e2]; exact spot_pair _ _ _ (by omega) (by omega) (by omega)
    · rw [e3]; exact spot_pair _ _ _ (by omega) (by omega) (by omega)
  · obtain ⟨v1, e1⟩ := Zf_surj (by omega) hd (Pi.single (sh i0 a1) 1)
    obtain ⟨v2, e2⟩ := Zf_surj (by omega) hd (Pi.single (sh i0 a2) 1)
    obtain ⟨v3, e3⟩ := Zf_surj (by omega) hd (Pi.single (sh i0 a3) 1)
    refine ⟨v1, v2, v3, a1, a2, a3, ?_, ?_, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · rw [e1]; exact spot_unit _ _ (by omega)
    · rw [e2]; exact spot_unit _ _ (by omega)
    · rw [e3]; exact spot_unit _ _ (by omega)

def Hyp (mark : Fin k → Bool) (δ : W k) : Prop :=
  ∀ a b c : W k, ∑ i, (if mark i then P4 i δ (Zf a) (Zf b) (Zf c) else 0) = 0

theorem sh_km (i0 : Fin k) (n : ℕ) (h : 1 ≤ n) : sh i0 (k - 1 + n) = sh i0 (n - 1) := by
  rw [show k - 1 + n = k + (n - 1) by have := NeZero.pos k; omega, sh_add_k]

theorem P4_at (i0 : Fin k) (t : ℕ) (Y0 Y1 Y2 Y3 : W k) :
    P4 (sh i0 t) Y0 Y1 Y2 Y3 =
      perm4 (Y0 (sh i0 (t + 2))) (Y0 (sh i0 (t + 4))) (Y0 (sh i0 (t + 1)) + Y0 (sh i0 (t + 3)))
        (Y0 (sh i0 (t + 3)) + Y0 (sh i0 (t + 5)))
      (Y1 (sh i0 (t + 2))) (Y1 (sh i0 (t + 4))) (Y1 (sh i0 (t + 1)) + Y1 (sh i0 (t + 3)))
        (Y1 (sh i0 (t + 3)) + Y1 (sh i0 (t + 5)))
      (Y2 (sh i0 (t + 2))) (Y2 (sh i0 (t + 4))) (Y2 (sh i0 (t + 1)) + Y2 (sh i0 (t + 3)))
        (Y2 (sh i0 (t + 3)) + Y2 (sh i0 (t + 5)))
      (Y3 (sh i0 (t + 2))) (Y3 (sh i0 (t + 4))) (Y3 (sh i0 (t + 1)) + Y3 (sh i0 (t + 3)))
        (Y3 (sh i0 (t + 3)) + Y3 (sh i0 (t + 5))) := by
  simp only [P4, sh_sh]

theorem P4_base (i0 : Fin k) (Y0 Y1 Y2 Y3 : W k) :
    P4 i0 Y0 Y1 Y2 Y3 = P4 (sh i0 0) Y0 Y1 Y2 Y3 := by rw [sh_zero]

theorem testA (hk : 10 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (mark : Fin k → Bool) (δ : W k)
    (H : Hyp mark δ) (i0 : Fin k) (hm : mark i0 = true) : δ (sh i0 4) = 0 := by
  obtain ⟨v1, v2, v3, b1, b2, b3, s1, s2, s3, hb⟩ := get_cols hk h3 i0 1 2 5
    (by norm_num) (by norm_num) (by norm_num)
  have E := H v1 v2 v3
  rw [localize mark δ (Zf v1) (Zf v2) (Zf v3) i0 {i0} ?loc] at E
  case loc =>
    intro t tk hS
    have t0 : t ≠ 0 := by
      rintro rfl
      exact hS (by simp [sh_zero])
    rcases spot_hit s1 t tk (by omega) with z1 | ⟨n1, p1, q1, r1⟩
    · exact Or.inl z1
    rcases spot_hit s2 t tk (by omega) with z2 | ⟨n2, p2, q2, r2⟩
    · exact Or.inr (Or.inl z2)
    rcases spot_hit s3 t tk (by omega) with z3 | ⟨n3, p3, q3, r3⟩
    · exact Or.inr (Or.inr z3)
    exfalso
    omega
  rw [Finset.sum_singleton, if_pos hm, P4_base, P4_at] at E
  have hb1 : b1 = 1 ∨ 6 < b1 := by omega
  have hb2 : b2 = 2 ∨ 6 < b2 := by omega
  have hb3 : b3 = 5 ∨ 6 < b3 := by omega
  simp (disch := omega) only [spot_val s1 (by omega) hb1, spot_val s2 (by omega) hb2,
    spot_val s3 (by omega) hb3] at E
  simpa [perm4, perm3] using E

theorem testB (hk : 10 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (mark : Fin k → Bool) (δ : W k)
    (H : Hyp mark δ) (i0 : Fin k) (hm : mark i0 = true) : δ (sh i0 2) = 0 := by
  obtain ⟨v1, v2, v3, b1, b2, b3, s1, s2, s3, hb⟩ := get_cols hk h3 i0 1 4 5
    (by norm_num) (by norm_num) (by norm_num)
  have E := H v1 v2 v3
  rw [localize mark δ (Zf v1) (Zf v2) (Zf v3) i0 {i0} ?loc] at E
  case loc =>
    intro t tk hS
    have t0 : t ≠ 0 := by
      rintro rfl
      exact hS (by simp [sh_zero])
    rcases spot_hit s1 t tk (by omega) with z1 | ⟨n1, p1, q1, r1⟩
    · exact Or.inl z1
    rcases spot_hit s2 t tk (by omega) with z2 | ⟨n2, p2, q2, r2⟩
    · exact Or.inr (Or.inl z2)
    rcases spot_hit s3 t tk (by omega) with z3 | ⟨n3, p3, q3, r3⟩
    · exact Or.inr (Or.inr z3)
    exfalso
    omega
  rw [Finset.sum_singleton, if_pos hm, P4_base, P4_at] at E
  have hb1 : b1 = 1 ∨ 6 < b1 := by omega
  have hb2 : b2 = 4 ∨ 6 < b2 := by omega
  have hb3 : b3 = 5 ∨ 6 < b3 := by omega
  simp (disch := omega) only [spot_val s1 (by omega) hb1, spot_val s2 (by omega) hb2,
    spot_val s3 (by omega) hb3] at E
  simpa [perm4, perm3] using E

theorem testC (hk : 10 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (mark : Fin k → Bool) (δ : W k)
    (H : Hyp mark δ) (i0 : Fin k) (hm : mark i0 = true) :
    (if mark (sh i0 (k - 1)) then δ (sh i0 3) else 0) + (δ (sh i0 3) + δ (sh i0 5)) = 0 := by
  obtain ⟨v1, v2, v3, b1, b2, b3, s1, s2, s3, hb⟩ := get_cols hk h3 i0 1 2 4
    (by norm_num) (by norm_num) (by norm_num)
  have E := H v1 v2 v3
  rw [localize mark δ (Zf v1) (Zf v2) (Zf v3) i0 {sh i0 (k - 1), i0} ?loc] at E
  case loc =>
    intro t tk hS
    have t0 : t ≠ 0 := by
      rintro rfl
      exact hS (by simp [sh_zero])
    have t1 : t ≠ k - 1 := by
      rintro rfl
      exact hS (by simp)
    rcases spot_hit s1 t tk (by omega) with z1 | ⟨n1, p1, q1, r1⟩
    · exact Or.inl z1
    rcases spot_hit s2 t tk (by omega) with z2 | ⟨n2, p2, q2, r2⟩
    · exact Or.inr (Or.inl z2)
    rcases spot_hit s3 t tk (by omega) with z3 | ⟨n3, p3, q3, r3⟩
    · exact Or.inr (Or.inr z3)
    exfalso
    omega
  have ne : sh i0 (k - 1) ≠ i0 := by
    intro e
    rw [← sh_zero i0, sh_sh, sh_eq_iff, Nat.zero_add, Nat.zero_mod,
      Nat.mod_eq_of_lt (by omega)] at e
    omega
  rw [Finset.sum_pair ne, if_pos hm, P4_base i0, P4_at i0 0, P4_at i0 (k - 1)] at E
  simp (disch := omega) only [sh_km] at E
  have hb1 : b1 = 1 ∨ 6 < b1 := by omega
  have hb2 : b2 = 2 ∨ 6 < b2 := by omega
  have hb3 : b3 = 4 ∨ 6 < b3 := by omega
  simp (disch := omega) only [spot_val s1 (by omega) hb1, spot_val s2 (by omega) hb2,
    spot_val s3 (by omega) hb3] at E
  simp [perm4, perm3, sh_zero] at E
  split_ifs at E ⊢ <;> simp_all <;> ring_nf at E ⊢ <;> simp_all

theorem testD (hk : 10 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (mark : Fin k → Bool) (δ : W k)
    (H : Hyp mark δ) (i0 : Fin k) (hm : mark i0 = true) :
    (δ (sh i0 1) + δ (sh i0 3)) + (if mark (sh i0 1) then δ (sh i0 3) else 0) = 0 := by
  obtain ⟨v1, v2, v3, b1, b2, b3, s1, s2, s3, hb⟩ := get_cols hk h3 i0 2 4 5
    (by norm_num) (by norm_num) (by norm_num)
  have E := H v1 v2 v3
  rw [localize mark δ (Zf v1) (Zf v2) (Zf v3) i0 {i0, sh i0 1} ?loc] at E
  case loc =>
    intro t tk hS
    have t0 : t ≠ 0 := by
      rintro rfl
      exact hS (by simp [sh_zero])
    have t1 : t ≠ 1 := by
      rintro rfl
      exact hS (by simp)
    rcases spot_hit s1 t tk (by omega) with z1 | ⟨n1, p1, q1, r1⟩
    · exact Or.inl z1
    rcases spot_hit s2 t tk (by omega) with z2 | ⟨n2, p2, q2, r2⟩
    · exact Or.inr (Or.inl z2)
    rcases spot_hit s3 t tk (by omega) with z3 | ⟨n3, p3, q3, r3⟩
    · exact Or.inr (Or.inr z3)
    exfalso
    omega
  have ne : i0 ≠ sh i0 1 := by
    intro e
    rw [← sh_zero i0, sh_sh, sh_eq_iff, Nat.zero_add, Nat.zero_mod,
      Nat.mod_eq_of_lt (by omega)] at e
    omega
  rw [Finset.sum_pair ne, if_pos hm, P4_base, P4_at, P4_at] at E
  have hb1 : b1 = 2 ∨ 6 < b1 := by omega
  have hb2 : b2 = 4 ∨ 6 < b2 := by omega
  have hb3 : b3 = 5 ∨ 6 < b3 := by omega
  simp (disch := omega) only [spot_val s1 (by omega) hb1, spot_val s2 (by omega) hb2,
    spot_val s3 (by omega) hb3] at E
  simp [perm4, perm3, sh_zero] at E
  split_ifs at E ⊢ <;> simp_all <;> ring_nf at E ⊢ <;> simp_all

end Tests

section Main

variable {k : ℕ} [NeZero k]

def Quad (g : W k → F) : Prop :=
  ∀ (v : Fin 3 → W k) (x : W k), (List.ofFn v).foldl diff g x = 0

def okF (mark : Fin k → Bool) (d : W k) : Prop :=
  ∀ i : Fin k, mark i = true →
    let z := fun j : ℕ => mixF (rotF 1 d) (sh i j)
    z 2 = 0 ∧ z 4 = 0 ∧ z 1 = z 3 ∧ z 3 = z 5

theorem quad_iff (g : W k → F) : Quad g ↔ Vanishes 3 g := by
  constructor
  · intro h a b c x
    have := h ![a, b, c] x
    simpa [List.ofFn_succ] using this
  · intro h v x
    have := h (v 0) (v 1) (v 2) x
    simpa [List.ofFn_succ] using this

theorem sum_v {ι : Type*} [Fintype ι] {n : ℕ} (g : ι → W k → F) (hg : ∀ i, Vanishes n (g i)) :
    Vanishes n (fun w => ∑ i, g i w) := by
  classical
  have key : ∀ s : Finset ι, Vanishes n (fun w => ∑ i ∈ s, g i w) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · have e : (fun w => ∑ i ∈ (∅ : Finset ι), g i w) = fun _ => 0 := by
        funext w; simp
      rw [e]; exact zero_v n
    · intro a s ha ih
      have e : (fun w => ∑ i ∈ insert a s, g i w) = fun w => g a w + ∑ i ∈ s, g i w := by
        funext w; rw [Finset.sum_insert ha]
      rw [e]; exact plus_v (hg a) ih
  exact key Finset.univ

theorem ite_v {n : ℕ} (m : Bool) (g : W k → F) (hg : Vanishes n g) :
    Vanishes n (fun w => if m then g w else 0) := by
  cases m
  · simp only [Bool.false_eq_true, if_false]; exact zero_v n
  · simp only [if_true]; exact hg

variable (name c₁ c₂ : W k)

theorem Tq_v (i : Fin k) : Vanishes 5 (Tq (k := k) i) := by
  have T (n : ℕ) : Vanishes 2 (tt (k := k) i n) := Zf_lin _
  unfold Tq
  exact mul_v 3 1 (mul_v 2 1 (mul_v 1 1 (T 2) (T 4)) (plus_v (T 1) (T 3))) (plus_v (T 3) (T 5))

theorem last_v (i : Fin k) : Vanishes 5 (fun w => lastF name c₁ c₂ w i) := by
  have split : (fun w => lastF name c₁ c₂ w i) = fun w => Tq i w + restF name c₁ c₂ i w := by
    funext w
    exact last_split name c₁ c₂ w i
  rw [split]
  exact plus_v (Tq_v i) (succ_v (rest_v name c₁ c₂ i))

theorem f_v (mark : Fin k → Bool) : Vanishes 5 (fF name c₁ c₂ mark) := by
  have hf : fF name c₁ c₂ mark = fun w => ∑ i, if mark i then lastF name c₁ c₂ w i else 0 := rfl
  rw [hf]
  exact sum_v _ (fun i => ite_v _ _ (last_v name c₁ c₂ i))

theorem quad_iff_hyp (mark : Fin k → Bool) (d : W k) :
    Quad (diff (fF name c₁ c₂ mark) d) ↔ Hyp mark (Zf d) := by
  rw [quad_iff]
  constructor
  · intro h a b c
    rw [← D4_f name c₁ c₂ mark d a b c 0]
    exact h a b c 0
  · intro h a b c x
    have e := D4_f name c₁ c₂ mark d a b c x
    unfold D4 at e
    rw [e]
    exact h a b c

theorem necessity (hk : 10 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (mark : Fin k → Bool) (δ : W k)
    (H : Hyp mark δ) (i0 : Fin k) (hm : mark i0 = true) :
    δ (sh i0 2) = 0 ∧ δ (sh i0 4) = 0 ∧ δ (sh i0 1) = δ (sh i0 3) ∧
      δ (sh i0 3) = δ (sh i0 5) := by
  have A := testA hk h3 mark δ H i0 hm
  have B := testB hk h3 mark δ H i0 hm
  have C := testC hk h3 mark δ H i0 hm
  have D := testD hk h3 mark δ H i0 hm
  refine ⟨B, A, ?_, ?_⟩
  · cases hq : mark (sh i0 1)
    · simp only [hq, Bool.false_eq_true, if_false, add_zero] at D
      exact eq_of_add_eq_zero_bit D
    · simp only [hq, if_true] at D
      have A' := testA hk h3 mark δ H (sh i0 1) hq
      have B' := testB hk h3 mark δ H (sh i0 1) hq
      rw [sh_sh] at A' B'
      rw [show 1 + 2 = 3 by norm_num] at B'
      rw [B'] at D ⊢
      simpa using D
  · cases hp : mark (sh i0 (k - 1))
    · simp only [hp, Bool.false_eq_true, if_false, zero_add] at C
      exact eq_of_add_eq_zero_bit C
    · simp only [hp, if_true] at C
      have A' := testA hk h3 mark δ H (sh i0 (k - 1)) hp
      rw [sh_pred _ _ (by norm_num)] at A'
      rw [show 4 - 1 = 3 by norm_num] at A'
      rw [A'] at C ⊢
      simp at C
      exact C.symm

theorem sufficiency (mark : Fin k → Bool) (d : W k) (hok : okF mark d) : Hyp mark (Zf d) := by
  intro a b c
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · have h : Zf d (sh i 2) = 0 ∧ Zf d (sh i 4) = 0 ∧ Zf d (sh i 1) = Zf d (sh i 3) ∧
        Zf d (sh i 3) = Zf d (sh i 5) := hok i hi
    obtain ⟨z2, z4, z13, z35⟩ := h
    have r3 : Zf d (sh i 1) + Zf d (sh i 3) = 0 := by rw [z13, self_plus_bit]
    have r4 : Zf d (sh i 3) + Zf d (sh i 5) = 0 := by rw [z35, self_plus_bit]
    simp only [P4, z2, z4, r3, r4]
    simp [perm4]
  · rfl

theorem Zf_apply' (hk2 : 2 ≤ k) (x : W k) (i : Fin k) : Zf x i = mixF x (sh i (k - 1)) := by
  simp only [Zf, mixF, rot1_eq hk2, shm_eq, sh_sh]
  rw [show 1 + (k - 1) = k - 1 + 1 by omega]

theorem shift_const (hk2 : 2 ≤ k) (mark : Fin k → Bool) (d : W k) (hmd : mixF d = 0) (w : W k) :
    fF name c₁ c₂ mark (w + d) - fF name c₁ c₂ mark w =
      ∑ i, if mark i then rotF 2 d i else 0 := by
  have hZ : mixF (rotF 1 d) = 0 := by
    funext i
    have e := Zf_apply' hk2 d i
    simp only [Zf] at e
    rw [e, hmd]
    rfl
  have hfirst : firstF name c₁ (w + d) = firstF name c₁ w + d := by
    unfold firstF
    rw [rot_add, show rotF 1 w + rotF 1 d + name = (rotF 1 w + name) + rotF 1 d by abel,
      mix_add, hZ, add_zero]
    abel
  have hlast : lastF name c₁ c₂ (w + d) = lastF name c₁ c₂ w + rotF 2 d := by
    unfold lastF
    rw [hfirst, mix_add, hmd, add_zero, rot_add]
    abel
  have e1 : fF name c₁ c₂ mark (w + d) =
      ∑ i, if mark i then lastF name c₁ c₂ (w + d) i else 0 := rfl
  have e2 : fF name c₁ c₂ mark w = ∑ i, if mark i then lastF name c₁ c₂ w i else 0 := rfl
  rw [e1, e2, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hlast]
  split_ifs <;> simp

theorem mainM (h9 : 9 ≤ k) (h3 : ¬ 3 ∣ k ∨ 30 ≤ k) (mark : Fin k → Bool) :
    (∀ d : W k, Quad (diff (fF name c₁ c₂ mark) d) ↔ okF mark d) ∧
    (∀ (d : W k) (g : W k → F), ¬ okF mark d → Quad g →
      2 ^ k ≤ 8 * Nat.card {w : W k // diff (fF name c₁ c₂ mark) d w ≠ g w}) ∧
    ((∀ j : Fin k, ∃ i : Fin k, mark i = true ∧ (sh i 2 = j ∨ sh i 4 = j)) →
      (∀ (d : W k) (a : F), (∀ w : W k, diff (fF name c₁ c₂ mark) d w = a) ↔
        mixF d = 0 ∧ a = ∑ i : Fin k, if mark i then rotF 2 d i else 0) ∧
      Nat.card {d : W k // ∃ a : F, ∀ w : W k, diff (fF name c₁ c₂ mark) d w = a} =
        (if 3 ∣ k then 4 else 1)) := by
  have hk10 : 10 ≤ k := by
    rcases h3 with h | h
    · by_contra hlt
      exact h ⟨3, by omega⟩
    · omega
  have hk2 : 2 ≤ k := by omega
  have partA : ∀ d : W k, Quad (diff (fF name c₁ c₂ mark) d) ↔ okF mark d := by
    intro d
    rw [quad_iff_hyp]
    constructor
    · intro H i hi
      exact necessity hk10 h3 mark (Zf d) H i hi
    · exact sufficiency mark d
  refine ⟨partA, ?_, ?_⟩
  · intro d g hnot hg
    let h := fun w => diff (fF name c₁ c₂ mark) d w - g w
    have h4 : Vanishes 4 h := by
      apply sub_v
      · exact f_v name c₁ c₂ mark d
      · exact le_v ((quad_iff g).mp hg) (by norm_num)
    have h3' : ¬ Vanishes 3 h := by
      intro hv
      apply hnot
      rw [← partA, quad_iff]
      have e : diff (fF name c₁ c₂ mark) d = fun w => h w + g w := by
        funext w; simp [h]
      rw [e]
      exact plus_v hv ((quad_iff g).mp hg)
    have wb := weight_bound h h4 h3'
    have ce : Nat.card {w : W k // h w ≠ 0} =
        Nat.card {w : W k // diff (fF name c₁ c₂ mark) d w ≠ g w} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun w => sub_ne_zero))
    rw [ce] at wb
    exact wb
  · intro cover
    have const_imp : ∀ (d : W k) (a : F), (∀ w, diff (fF name c₁ c₂ mark) d w = a) →
        mixF d = 0 := by
      intro d a hc
      have v1 : Vanishes 1 (diff (fF name c₁ c₂ mark) d) := by
        intro u x
        change diff (fF name c₁ c₂ mark) d (x + u) - diff (fF name c₁ c₂ mark) d x = 0
        rw [hc, hc, sub_self]
      have hok := (partA d).mp ((quad_iff _).mpr (le_v v1 (by norm_num)))
      have hZ : ∀ j, Zf d j = 0 := by
        intro j
        obtain ⟨i, hi, hj⟩ := cover j
        have h : Zf d (sh i 2) = 0 ∧ Zf d (sh i 4) = 0 ∧ Zf d (sh i 1) = Zf d (sh i 3) ∧
            Zf d (sh i 3) = Zf d (sh i 5) := hok i hi
        rcases hj with rfl | rfl
        · exact h.1
        · exact h.2.1
      funext j
      have e := Zf_apply' hk2 d (sh j 1)
      rw [sh_sh, show 1 + (k - 1) = k by omega, sh_k] at e
      rw [Pi.zero_apply, ← e, hZ]
    have back : ∀ d : W k, mixF d = 0 → ∀ w,
        diff (fF name c₁ c₂ mark) d w = ∑ i : Fin k, if mark i then rotF 2 d i else 0 := by
      intro d hd w
      exact shift_const name c₁ c₂ hk2 mark d hd w
    refine ⟨?_, ?_⟩
    · intro d a
      constructor
      · intro hc
        have hd := const_imp d a hc
        refine ⟨hd, ?_⟩
        rw [← hc 0, back d hd 0]
      · rintro ⟨hd, rfl⟩
        exact back d hd
    · have ce : Nat.card {d : W k // ∃ a : F, ∀ w : W k, diff (fF name c₁ c₂ mark) d w = a} =
          Nat.card {d : W k // mixF d = 0} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun d =>
          ⟨fun ⟨a, ha⟩ => const_imp d a ha, fun hd => ⟨_, back d hd⟩⟩))
      rw [ce]
      split_ifs with hd
      · exact ker_card3 hd
      · exact ker_card1 hd

end Main

end PEqualNP.Outside.L_meta_32051_aux

theorem PEqualNP.Outside.L_meta_32051 : (∀ (k : ℕ) (hk : 0 < k), 9 ≤ k → (¬ 3 ∣ k ∨ 30 ≤ k) →
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (x : W) (i : Fin k) => x i + x (ix (i.val+1)) + x (ix (i.val+k-1))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1+x (ix (i.val+1))) * x (ix (i.val+2))
  let diff := fun (f : W → F) (v x : W) => f (x+v) - f x
  let quad := fun (f : W → F) => ∀ (v : Fin 3 → W) (x : W), (List.ofFn v).foldl diff f x = 0
  ∀ (name c₁ c₂ : W) (mark : Fin k → Bool),
    let f := fun w : W =>
      let first := step (mix (rot 1 w + name)) + w + c₁
      let last := step (mix first) + rot 2 w + c₂
      ∑ i : Fin k, if mark i then last i else 0
    let ok := fun d : W => ∀ i : Fin k, mark i = true →
      let z := fun j : ℕ => mix (rot 1 d) (ix (i.val+j))
      z 2 = 0 ∧ z 4 = 0 ∧ z 1 = z 3 ∧ z 3 = z 5
    (∀ d : W, quad (diff f d) ↔ ok d) ∧
    (∀ (d : W) (g : W → F), ¬ ok d → quad g →
      2^k ≤ 8 * Nat.card {w : W // diff f d w ≠ g w}) ∧
    ((∀ j : Fin k, ∃ i : Fin k, mark i = true ∧
        (ix (i.val+2) = j ∨ ix (i.val+4) = j)) →
      (∀ (d : W) (a : F), (∀ w : W, diff f d w = a) ↔
        mix d = 0 ∧ a = ∑ i : Fin k, if mark i then rot 2 d i else 0) ∧
      Nat.card {d : W // ∃ a : F, ∀ w : W, diff f d w = a} =
        (if 3 ∣ k then 4 else 1))) := by
  intro k hk h9 h3
  haveI : NeZero k := ⟨by omega⟩
  intro F W ix rot mix step diff quad name c₁ c₂ mark
  exact PEqualNP.Outside.L_meta_32051_aux.mainM name c₁ c₂ h9 h3 mark
