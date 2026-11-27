import Mathlib.Algebra.Module.Pi
import Mathlib.Data.List.OfFn
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_meta_29929_aux

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

theorem add_v {f g : E → F} {n : ℕ} (hf : Vanishes n f) (hg : Vanishes n g) :
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
    apply add_v
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

theorem v_iff_list (n : ℕ) (f : E → F) :
    Vanishes n f ↔ ∀ (us : List E), us.length = n → ∀ x, us.foldl diff f x = 0 := by
  induction n generalizing f with
  | zero =>
    constructor
    · intro hf us length x
      have empty : us = [] := List.length_eq_zero_iff.mp length
      simpa [empty] using hf x
    · intro hf x
      exact hf [] rfl x
  | succ n ih =>
    constructor
    · intro hf us hlen x
      cases us with
      | nil => simp at hlen
      | cons u rest =>
        exact (ih (diff f u)).mp (hf u) rest (Nat.succ.inj hlen) x
    · intro hf u
      exact (ih (diff f u)).mpr fun rest h x =>
        hf (u :: rest) (congrArg Nat.succ h) x

theorem v_iff_cubic (f : E → F) :
    Vanishes 4 f ↔ ∀ (v : Fin 4 → E) x, (List.ofFn v).foldl diff f x = 0 := by
  rw [v_iff_list]
  constructor
  · intro hf v
    exact hf (List.ofFn v) (by simp)
  · intro hf us hlen x
    let v (j : Fin 4) := us.get (Fin.cast hlen.symm j)
    have exactLength : List.ofFn v = us := by
      apply List.ext_getElem
      · simp [hlen]
      · intro j h₁ h₂
        simp only [List.getElem_ofFn]
        rfl
    rw [← exactLength]
    exact hf v x

end Difference

section Linear

variable {E G : Type*} [AddCommGroup E] [Module F E] [AddCommGroup G] [Module F G]

theorem aff_v (L : E →ₗ[F] F) (c : F) : Vanishes 2 (fun x => L x + c) := by
  intro u
  have same : diff (fun x => L x + c) u = fun _ => L u := by
    funext x
    simp only [diff, map_add]
    ring
  rw [same]
  exact const_v _

theorem lin_v (L : E →ₗ[F] F) : Vanishes 2 (fun x => L x) := by
  simpa only [add_zero] using aff_v L 0

theorem comap_v {n : ℕ} {f : G → F} (hf : Vanishes n f) (L : E →ₗ[F] G) :
    Vanishes n (fun x => f (L x)) := by
  induction n generalizing f with
  | zero => intro x; exact hf (L x)
  | succ n ih =>
    intro u
    have same : diff (fun x => f (L x)) u = fun x => diff f (L u) (L x) := by
      funext x
      simp [diff, map_add]
    rw [same]
    exact ih (hf (L u))

theorem bit_square (a : F) : a * a = a := by
  decide +revert +kernel

end Linear

abbrev W (k : ℕ) := Fin k → F
abbrev Form (k : ℕ) := W k →ₗ[F] F

def index {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def adv {k : ℕ} (hk : 0 < k) (i : Fin k) (s : ℕ) : Fin k :=
  index hk (i.val + s)

def back {k : ℕ} (hk : 0 < k) (i : Fin k) (s : ℕ) : Fin k :=
  index hk (i.val + k - s % k)

theorem adv_add {k : ℕ} (hk : 0 < k) (i : Fin k) (a b : ℕ) :
    adv hk (adv hk i a) b = adv hk i (a + b) := by
  apply Fin.ext
  change ((i.val + a) % k + b) % k = (i.val + (a + b)) % k
  rw [Nat.mod_add_mod, Nat.add_assoc]

theorem adv_zero {k : ℕ} (hk : 0 < k) (i : Fin k) : adv hk i 0 = i := by
  apply Fin.ext
  simp [adv, index, Nat.mod_eq_of_lt i.isLt]

theorem adv_width {k : ℕ} (hk : 0 < k) (i : Fin k) : adv hk i k = i := by
  apply Fin.ext
  simp [adv, index, Nat.mod_eq_of_lt i.isLt]

theorem back_one {k : ℕ} (hk : 0 < k) (large : 1 < k) (i : Fin k) :
    back hk i 1 = adv hk i (k - 1) := by
  apply Fin.ext
  simp only [back, adv, index, Nat.mod_eq_of_lt large, Nat.add_sub_assoc (Nat.le_of_lt large)]

theorem back_after_adv {k : ℕ} (hk : 0 < k) (large : 1 < k) (i : Fin k) :
    back hk (adv hk i 1) 1 = i := by
  rw [back_one hk large, adv_add, show 1 + (k - 1) = k by omega, adv_width]

theorem adv_after_back {k : ℕ} (hk : 0 < k) (large : 1 < k) (i : Fin k) :
    adv hk (back hk i 1) 1 = i := by
  rw [back_one hk large, adv_add, show k - 1 + 1 = k by omega, adv_width]

def coord {k : ℕ} (i : Fin k) : Form k := LinearMap.proj i

@[simp] theorem coord_apply {k : ℕ} (i : Fin k) (x : W k) : coord i x = x i := rfl

def rotLin {k : ℕ} (hk : 0 < k) (s : ℕ) : W k →ₗ[F] W k :=
  LinearMap.pi fun i => coord (back hk i s)

def mixLin {k : ℕ} (hk : 0 < k) (s : ℕ) : W k →ₗ[F] W k :=
  LinearMap.pi fun i => coord i + coord (adv hk i s) + coord (back hk i s)

@[simp] theorem rot_apply {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) (i : Fin k) :
    rotLin hk s x i = x (back hk i s) := rfl

@[simp] theorem mix_apply {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) (i : Fin k) :
    mixLin hk s x i = x i + x (adv hk i s) + x (back hk i s) := rfl

def localStep {k : ℕ} (hk : 0 < k) (x : W k) (i : Fin k) : F :=
  x i + (1 + x (adv hk i 1)) * x (adv hk i 2)

def cyclicOut {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → W k)
    (x : W k) (b : Bool) : W k :=
  let gap := if b then 2 else 1
  let spin := if b then 3 else 1
  let z := mixLin hk gap (rotLin hk spin x + name b)
  let y := localStep hk z + rotLin hk (if b then 4 else 0) x + c₁ b
  localStep hk (mixLin hk gap y) + rotLin hk (if b then 7 else 2) x + c₂ b

def firstMix {k : ℕ} (hk : 0 < k) : W k →ₗ[F] W k :=
  (mixLin hk 1).comp (rotLin hk 1)

def zform {k : ℕ} (hk : 0 < k) (i : Fin k) : Form k :=
  (coord i).comp (firstMix hk)

def zconst {k : ℕ} (hk : 0 < k) (name : W k) (i : Fin k) : F :=
  mixLin hk 1 name i

def ylin {k : ℕ} (hk : 0 < k) (name : W k) (i : Fin k) : Form k :=
  zform hk i + (1 + zconst hk name (adv hk i 1)) • zform hk (adv hk i 2) +
    zconst hk name (adv hk i 2) • zform hk (adv hk i 1) + coord i

def yconst {k : ℕ} (hk : 0 < k) (name c : W k) (i : Fin k) : F :=
  zconst hk name i + (1 + zconst hk name (adv hk i 1)) * zconst hk name (adv hk i 2) + c i

def yaff {k : ℕ} (hk : 0 < k) (name c : W k) (i : Fin k) (x : W k) : F :=
  ylin hk name i x + yconst hk name c i

def yquad {k : ℕ} (hk : 0 < k) (i : Fin k) (x : W k) : F :=
  zform hk (adv hk i 1) x * zform hk (adv hk i 2) x

theorem yaff_quad {k : ℕ} (hk : 0 < k) (name c x : W k) (i : Fin k) :
    (localStep hk (mixLin hk 1 (rotLin hk 1 x + name)) + rotLin hk 0 x + c) i =
      yaff hk name c i x + yquad hk i x := by
  have z (j : Fin k) : mixLin hk 1 (rotLin hk 1 x + name) j =
      zform hk j x + zconst hk name j := by rw [map_add]; rfl
  have rot0 : back hk i 0 = i := by
    apply Fin.ext
    simp [back, index, Nat.mod_eq_of_lt i.isLt]
  simp only [Pi.add_apply, localStep, z, rot_apply, rot0, yaff, ylin, yconst,
    yquad, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, coord_apply]
  ring

def maff {k : ℕ} (hk : 0 < k) (name c : W k) (i : Fin k) (x : W k) : F :=
  yaff hk name c i x + yaff hk name c (adv hk i 1) x + yaff hk name c (back hk i 1) x

def mquad {k : ℕ} (hk : 0 < k) (i : Fin k) (x : W k) : F :=
  yquad hk i x + yquad hk (adv hk i 1) x + yquad hk (back hk i 1) x

theorem mixed_y {k : ℕ} (hk : 0 < k) (name c x : W k) (i : Fin k) :
    mixLin hk 1 (localStep hk (mixLin hk 1 (rotLin hk 1 x + name)) + rotLin hk 0 x + c) i =
    maff hk name c i x + mquad hk i x := by
  simp only [mix_apply hk 1 _ i, yaff_quad, maff, mquad]
  ring

theorem maff_v {k : ℕ} (hk : 0 < k) (name c : W k) (i : Fin k) :
    Vanishes 2 (maff hk name c i) := by
  unfold maff yaff
  exact add_v (add_v (aff_v _ _) (aff_v _ _)) (aff_v _ _)

theorem yquad_v {k : ℕ} (hk : 0 < k) (i : Fin k) :
    Vanishes 3 (yquad hk i) := by
  exact mul_v 1 1 (lin_v _) (lin_v _)

theorem mquad_v {k : ℕ} (hk : 0 < k) (i : Fin k) :
    Vanishes 3 (mquad hk i) := by
  exact add_v (add_v (yquad_v _ _) (yquad_v _ _)) (yquad_v _ _)

def tap {k : ℕ} (hk : 0 < k) (i : Fin k) (j : ℕ) : Form k :=
  zform hk (adv hk i j)

def topForms {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin 4 → Form k :=
  ![tap hk i 2, tap hk i 4, tap hk i 1 + tap hk i 3, tap hk i 3 + tap hk i 5]

def prodFour {E : Type*} [AddCommGroup E] [Module F E]
    (f : Fin 4 → E →ₗ[F] F) (x : E) : F :=
  f 0 x * f 1 x * f 2 x * f 3 x

def cubicPart {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → W k) (i : Fin k)
    (x : W k) : F := cyclicOut hk name c₁ c₂ x false i - prodFour (topForms hk i) x

private theorem quartic_identity (a b c d e : F) :
    (a*b+b*c+c*d)*(b*c+c*d+d*e) - b*d*(a+c)*(c+e) =
      a*b*c + b*c + b*c*d + c*d + c*d*e := by
  decide +revert +kernel

private theorem quad_shift_one {k : ℕ} (hk : 0 < k) (large : 1 < k) (i : Fin k) (x : W k) :
    mquad hk (adv hk i 1) x =
      tap hk i 1 x * tap hk i 2 x + tap hk i 2 x * tap hk i 3 x +
        tap hk i 3 x * tap hk i 4 x := by
  simp only [mquad, yquad, tap, back_after_adv hk large, adv_add]
  ring

private theorem quad_shift_two {k : ℕ} (hk : 0 < k) (large : 1 < k) (i : Fin k) (x : W k) :
    mquad hk (adv hk i 2) x =
      tap hk i 2 x * tap hk i 3 x + tap hk i 3 x * tap hk i 4 x +
        tap hk i 4 x * tap hk i 5 x := by
  have prev : back hk (adv hk i 2) 1 = adv hk i 1 := by
    rw [show adv hk i 2 = adv hk (adv hk i 1) 1 by rw [adv_add], back_after_adv hk large]
  simp only [mquad, yquad, tap, prev, adv_add]
  ring

private theorem quartic_residual_v {k : ℕ} (hk : 0 < k) (large : 1 < k) (i : Fin k) :
    Vanishes 4 (fun x => mquad hk (adv hk i 1) x * mquad hk (adv hk i 2) x -
      prodFour (topForms hk i) x) := by
  have values : (fun x => mquad hk (adv hk i 1) x * mquad hk (adv hk i 2) x -
        prodFour (topForms hk i) x) =
      fun x => tap hk i 1 x * tap hk i 2 x * tap hk i 3 x + tap hk i 2 x * tap hk i 3 x +
        tap hk i 2 x * tap hk i 3 x * tap hk i 4 x + tap hk i 3 x * tap hk i 4 x +
        tap hk i 3 x * tap hk i 4 x * tap hk i 5 x := by
    funext x
    rw [quad_shift_one hk large, quad_shift_two hk large]
    exact quartic_identity _ _ _ _ _
  rw [values]
  have square (s t : ℕ) : Vanishes 3 (fun x => tap hk i s x * tap hk i t x) :=
    mul_v 1 1 (lin_v _) (lin_v _)
  have cube (s t u : ℕ) : Vanishes 4 (fun x => tap hk i s x * tap hk i t x * tap hk i u x) :=
    mul_v 2 1 (square s t) (lin_v _)
  exact add_v (add_v (add_v (add_v (cube 1 2 3) (succ_v (square 2 3))) (cube 2 3 4))
    (succ_v (square 3 4))) (cube 3 4 5)

theorem cubic_part_v {k : ℕ} (hk : 0 < k) (large : 1 < k)
    (name c₁ c₂ : Bool → W k) (i : Fin k) :
    Vanishes 4 (cubicPart hk name c₁ c₂ i) := by
  let L (j : Fin k) := maff hk (name false) (c₁ false) j
  let Q (j : Fin k) := mquad hk j
  let j := adv hk i 1
  let l := adv hk i 2
  let A : Form k := (coord i).comp (rotLin hk 2)
  have L_v (n : Fin k) : Vanishes 2 (L n) := maff_v hk _ _ n
  have Q_v (n : Fin k) : Vanishes 3 (Q n) := mquad_v hk n
  have rest_v : Vanishes 4
      (fun x => L i x + Q i x + L l x + Q l x + (A x + c₂ false i)) := by
    exact add_v (add_v (add_v (add_v (le_v (L_v _) (by omega)) (succ_v (Q_v _)))
      (le_v (L_v _) (by omega))) (succ_v (Q_v _))) (le_v (aff_v _ _) (by omega))
  have expansion : cubicPart hk name c₁ c₂ i = fun x =>
      (L i x + Q i x + L l x + Q l x + (A x + c₂ false i)) +
      L j x * L l x + L j x * Q l x + Q j x * L l x +
      (Q j x * Q l x - prodFour (topForms hk i) x) := by
    funext x
    unfold cubicPart cyclicOut
    simp only [Bool.false_eq_true, if_false, Pi.add_apply, localStep]
    rw [mixed_y, mixed_y, mixed_y]
    change (L i x + Q i x + (1 + (L j x + Q j x)) * (L l x + Q l x) +
        A x + c₂ false i) - prodFour (topForms hk i) x = _
    ring
  rw [expansion]
  exact add_v (add_v (add_v (add_v rest_v (succ_v (mul_v 1 1 (L_v j) (L_v l))))
    (mul_v 1 2 (L_v j) (Q_v l))) (mul_v 2 1 (Q_v j) (L_v l)))
    (quartic_residual_v hk large i)

section SparseRank

variable {I J : Type*} [Fintype I]

noncomputable def columnMap (a : I → J → F) : (I → F) →ₗ[F] (J → F) :=
  ∑ i, (LinearMap.proj i : (I → F) →ₗ[F] F).smulRight (a i)

theorem column_apply (a : I → J → F) (x : I → F) (j : J) :
    columnMap a x j = ∑ i, x i * a i j := by
  simp [columnMap, LinearMap.sum_apply, Finset.sum_apply, smul_eq_mul]

noncomputable def signature (a : I → J → F) (i : I) : (columnMap a).ker →ₗ[F] F :=
  (LinearMap.proj i).comp (LinearMap.ker (columnMap a)).subtype

theorem bit_one (x : F) (h : x ≠ 0) : x = 1 := Fin.eq_one_of_ne_zero _ h

theorem add_eq_zero_bits {x y : F} (h : x + y = 0) : x = y :=
  (add_eq_zero_iff_eq_neg.mp h).trans (ZMod.neg_eq_self_mod_two _)

noncomputable def visible (a : I → J → F) (j : J) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => a i j ≠ 0)

theorem mem_visible (a : I → J → F) (i : I) (j : J) :
    i ∈ visible a j ↔ a i j ≠ 0 := by
  classical
  simp [visible]

theorem visible_sum (a : I → J → F) (j : J) (x : (columnMap a).ker) :
    ∑ i ∈ visible a j, (x.val i) * a i j = 0 := by
  classical
  have hk : columnMap a x.val = 0 := LinearMap.mem_ker.mp x.property
  have atJ := congrFun hk j
  rw [column_apply] at atJ
  simp only [visible, Finset.sum_filter]
  convert atJ using 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : a i j = 0 <;> simp [h]

theorem signature_partner (a : I → J → F) (sparse : ∀ j, (visible a j).card ≤ 2)
    (i : I) (j : J) (present : a i j ≠ 0) (active : signature a i ≠ 0) :
    ∃ h, h ≠ i ∧ a h j ≠ 0 ∧ signature a h = signature a i := by
  classical
  let S := visible a j
  have i_mem : i ∈ S := (mem_visible a i j).mpr present
  by_cases further : ∃ h ∈ S, h ≠ i
  · obtain ⟨h, h_mem, different⟩ := further
    have both : ({i, h} : Finset I) ⊆ S := by
      intro w hw
      simp at hw
      rcases hw with eq | eq
      · exact eq ▸ i_mem
      · exact eq ▸ h_mem
    have all : ({i, h} : Finset I) = S :=
      Finset.eq_of_subset_of_card_le both (by simpa [Ne.symm different] using sparse j)
    have h_nonzero := (mem_visible a h j).mp h_mem
    refine ⟨h, different, h_nonzero, ?_⟩
    ext x
    have same := visible_sum a j x
    change ∑ w ∈ S, x.val w * a w j = 0 at same
    rw [← all, Finset.sum_pair (Ne.symm different), bit_one _ present,
      bit_one _ h_nonzero, mul_one, mul_one] at same
    exact (add_eq_zero_bits same).symm
  · have all : S = {i} := by
      apply Finset.Subset.antisymm
      · intro h h_mem
        have eq : h = i := by by_contra ne; exact further ⟨h, h_mem, ne⟩
        simpa using eq
      · simpa using i_mem
    exfalso
    apply active
    ext x
    have same := visible_sum a j x
    change ∑ w ∈ S, x.val w * a w j = 0 at same
    change x.val i = 0
    simpa only [all, Finset.sum_singleton, bit_one _ present, mul_one] using same

private theorem signature_triple [Nonempty J] (a : I → J → F)
    (sparse : ∀ j, (visible a j).card ≤ 2)
    (nonzero : ∀ i, a i ≠ 0) (distinct : Function.Injective a)
    (i : I) (active : signature a i ≠ 0) :
    ∃ h v, h ≠ i ∧ v ≠ i ∧ v ≠ h ∧
      signature a h = signature a i ∧ signature a v = signature a i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, a i j ≠ 0 := by
    by_contra none
    push Not at none
    exact nonzero i (funext none)
  obtain ⟨h, different, _, hsig⟩ := signature_partner a sparse i j hj active
  obtain ⟨t, ht⟩ : ∃ t, a i t ≠ a h t := by
    by_contra none
    push Not at none
    exact different (distinct (funext none)).symm
  by_cases hzero : a i t = 0
  · have hnz : a h t ≠ 0 := by simpa [hzero, ne_comm] using ht
    obtain ⟨v, vh, hva, vs⟩ := signature_partner a sparse h t hnz (hsig ▸ active)
    have vi : v ≠ i := fun eq => hva (eq ▸ hzero)
    exact ⟨h, v, different, vi, vh, hsig, vs.trans hsig⟩
  · have hz : a h t = 0 := by
      by_contra hnz
      exact ht ((bit_one _ hzero).trans (bit_one _ hnz).symm)
    obtain ⟨v, vi, hva, vs⟩ := signature_partner a sparse i t hzero active
    have vh : v ≠ h := fun eq => hva (eq ▸ hz)
    exact ⟨h, v, different, vi, vh, hsig, vs⟩

theorem sparse_kernel [Nonempty J] (a : I → J → F)
    (sparse : ∀ j, (visible a j).card ≤ 2)
    (nonzero : ∀ i, a i ≠ 0) (distinct : Function.Injective a) :
    3 * Module.finrank F ((columnMap a).ker) ≤ Fintype.card I := by
  classical
  let alive : Finset I := Finset.univ.filter (fun i => signature a i ≠ 0)
  let values := alive.image (signature a)
  have fiber_size (s : (columnMap a).ker →ₗ[F] F) (hs : s ∈ values) :
      3 ≤ (alive.filter (fun i => signature a i = s)).card := by
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hs
    have act : signature a i ≠ 0 := (Finset.mem_filter.mp hi).2
    obtain ⟨h,v,hi',vi,vh, hs,vs⟩ := signature_triple a sparse nonzero distinct i act
    have all : ({i,h,v} : Finset I) ⊆ alive.filter (fun j => signature a j = signature a i) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hi, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun eq => act (hs.symm.trans eq)⟩, hs⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, fun eq => act (vs.symm.trans eq)⟩, vs⟩
    simpa [Ne.symm hi', Ne.symm vi, Ne.symm vh] using Finset.card_le_card all
  have few : 3 * values.card ≤ Fintype.card I := by
    have sum := Finset.sum_le_sum (s := values) (fun s hs => fiber_size s hs)
    have partition := Finset.card_eq_sum_card_image (signature a) alive
    change alive.card = ∑ s ∈ values, (alive.filter (fun i => signature a i = s)).card at partition
    rw [← partition] at sum
    have upper : alive.card ≤ Fintype.card I := Finset.card_le_univ _
    simpa [Nat.mul_comm] using sum.trans upper
  let embedding : (columnMap a).ker →ₗ[F] (values → F) :=
    LinearMap.pi (fun s => s.val)
  have inj : Function.Injective embedding := by
    intro x y equal
    apply Subtype.ext
    funext i
    by_cases h : signature a i = 0
    · have p : x.val i = 0 := congrArg (fun l : (columnMap a).ker →ₗ[F] F => l x) h
      have q : y.val i = 0 := congrArg (fun l : (columnMap a).ker →ₗ[F] F => l y) h
      exact p.trans q.symm
    · have mem : signature a i ∈ values :=
        Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
      exact congrFun equal ⟨signature a i, mem⟩
  have dim := LinearMap.finrank_le_finrank_of_injective inj
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at dim
  exact (Nat.mul_le_mul_left 3 dim).trans few

theorem sparse_rank [Nonempty J] (a : I → J → F)
    (sparse : ∀ j, (visible a j).card ≤ 2)
    (nonzero : ∀ i, a i ≠ 0) (distinct : Function.Injective a) :
    2 * Fintype.card I ≤ 3 * Module.finrank F ((columnMap a).range) := by
  have dim := (columnMap a).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at dim
  have bound := sparse_kernel a sparse nonzero distinct
  omega

end SparseRank

def runAsk {k d : ℕ} (ask : Fin d → ℕ → Form k) (x : W k) : ℕ :=
  (List.finRange d).foldl (fun h j =>
    2 * h + (if ask j h x = 0 then 0 else 1)) 0

def Fits {k : ℕ} (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → W k) : Prop :=
  ∃ (ask : Fin d → ℕ → Form k) (readout : ℕ → Bool → Fin k → W k → F),
    (∀ h b i (v : Fin 4 → W k) x, (List.ofFn v).foldl diff (readout h b i) x = 0) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      cyclicOut hk name c₁ c₂ x b i = readout (runAsk ask x) b i x

def queryMap {k d : ℕ} (ask : Fin d → ℕ → Form k) : W k →ₗ[F] (Fin d → F) :=
  LinearMap.pi (fun j => ask j 0)

theorem zero_run {k d : ℕ} (ask : Fin d → ℕ → Form k) (x : (queryMap ask).ker) :
    runAsk ask x.val = 0 := by
  have no (j : Fin d) : ask j 0 x.val = 0 :=
    congrFun (LinearMap.mem_ker.mp x.property) j
  have fold_zero (xs : List (Fin d)) :
      xs.foldl (fun h j => 2 * h + (if ask j h x.val = 0 then 0 else 1)) 0 = 0 := by
    induction xs with
    | nil => rfl
    | cons j rest ih => simpa only [List.foldl_cons, no, ite_true, Nat.mul_zero, Nat.add_zero] using ih
  exact fold_zero _

noncomputable def coeffForm (k : ℕ) : W k →ₗ[F] Form k :=
  ∑ j : Fin k, (coord j).smulRight (coord j)

theorem coeff_eval (k : ℕ) (a x : W k) :
    coeffForm k a x = ∑ j : Fin k, a j * x j := by
  simp [coeffForm, LinearMap.sum_apply, smul_eq_mul]

@[simp] theorem coeff_single (k : ℕ) (i : Fin k) (a : F) :
    coeffForm k (Pi.single i a) = a • coord i := by
  apply LinearMap.ext
  intro x
  simp [coeff_eval, Pi.single_apply, ite_mul, smul_eq_mul]

noncomputable def pull {k : ℕ} (hk : 0 < k) : W k →ₗ[F] Form k :=
  (firstMix hk).dualMap.comp (coeffForm k)

theorem pull_eval {k : ℕ} (hk : 0 < k) (a x : W k) :
    pull hk a x = ∑ j : Fin k, a j * firstMix hk x j :=
  coeff_eval k a (firstMix hk x)

def mixedCoeff {k : ℕ} (hk : 0 < k) (i : Fin k) (p : Fin 4 → F) : W k :=
  Pi.single (adv hk i 1) (p 2) + Pi.single (adv hk i 2) (p 0) +
    Pi.single (adv hk i 3) (p 2 + p 3) + Pi.single (adv hk i 4) (p 1) +
    Pi.single (adv hk i 5) (p 3)

private theorem basis_four (v : Fin 4 → F) :
    v = v 0 • Pi.single (0 : Fin 4) (1 : F) + v 1 • Pi.single (1 : Fin 4) (1 : F) +
      v 2 • Pi.single (2 : Fin 4) (1 : F) + v 3 • Pi.single (3 : Fin 4) (1 : F) := by
  funext j
  fin_cases j <;> simp [smul_eq_mul]

def basisValues (value : (Fin 4 → F) →ₗ[F] F) (j : Fin 4) : F :=
  value (Pi.single j 1)

theorem expand_value (value : (Fin 4 → F) →ₗ[F] F) (v : Fin 4 → F) :
    value v = v 0 * basisValues value 0 + v 1 * basisValues value 1 +
      v 2 * basisValues value 2 + v 3 * basisValues value 3 := by
  conv_lhs => rw [basis_four v]
  simp only [map_add, map_smul, basisValues, smul_eq_mul]

theorem pull_mixed {k : ℕ} (hk : 0 < k) (i : Fin k)
    (value : (Fin 4 → F) →ₗ[F] F) (x : W k) :
    pull hk (mixedCoeff hk i (basisValues value)) x = value (fun j => topForms hk i j x) := by
  rw [expand_value]
  simp only [pull, LinearMap.comp_apply, mixedCoeff, map_add, coeff_single,
    LinearMap.dualMap_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    coord_apply, topForms, Matrix.cons_val_zero]
  change basisValues value 2 * tap hk i 1 x + basisValues value 0 * tap hk i 2 x +
      (basisValues value 2 + basisValues value 3) * tap hk i 3 x +
      basisValues value 1 * tap hk i 4 x + basisValues value 3 * tap hk i 5 x =
      tap hk i 2 x * basisValues value 0 + tap hk i 4 x * basisValues value 1 +
      (tap hk i 1 x + tap hk i 3 x) * basisValues value 2 +
      (tap hk i 3 x + tap hk i 5 x) * basisValues value 3
  ring

theorem not_surjective_four {E : Type*} [AddCommGroup E] [Module F E]
    (forms : Fin 4 → E →ₗ[F] F) (lo : Vanishes 4 (prodFour forms)) :
    ¬ Function.Surjective (LinearMap.pi forms) := by
  intro onto
  let e (t : Fin 4) : Fin 4 → F := Pi.single t 1
  obtain ⟨u, hu⟩ := onto (e 0)
  obtain ⟨v, hv⟩ := onto (e 1)
  obtain ⟨w, hw⟩ := onto (e 2)
  obtain ⟨z, hz⟩ := onto (e 3)
  have eval_u (j : Fin 4) : forms j u = e 0 j := congrFun hu j
  have eval_v (j : Fin 4) : forms j v = e 1 j := congrFun hv j
  have eval_w (j : Fin 4) : forms j w = e 2 j := congrFun hw j
  have eval_z (j : Fin 4) : forms j z = e 3 j := congrFun hz j
  have first : diff (prodFour forms) u = fun x => forms 1 x * forms 2 x * forms 3 x := by
    funext x
    simp [diff, prodFour, map_add, eval_u, e]
    ring
  have second : diff (fun x => forms 1 x * forms 2 x * forms 3 x) v =
      fun x => forms 2 x * forms 3 x := by
    funext x
    simp [diff, map_add, eval_v, e]
    ring
  have third : diff (fun x => forms 2 x * forms 3 x) w = fun x => forms 3 x := by
    funext x
    simp [diff, map_add, eval_w, e]
    ring
  have fourth : diff (fun x => forms 3 x) z = fun _ => 1 := by
    funext x
    simp [diff, map_add, eval_z, e]
  have empty := lo u v w z (0 : E)
  rw [first, second, third, fourth] at empty
  exact one_ne_zero empty

theorem marked_coeff {k d : ℕ} (hk : 0 < k) (large : 1 < k)
    (name c₁ c₂ : Bool → W k) (ask : Fin d → ℕ → Form k)
    (readout : ℕ → W k → F) (i : Fin k)
    (cubic : ∀ h, Vanishes 4 (readout h))
    (correct : ∀ x, cyclicOut hk name c₁ c₂ x false i = readout (runAsk ask x) x) :
    ∃ p : Fin 4 → F, p ≠ 0 ∧
      pull hk (mixedCoeff hk i p) ∈ (queryMap ask).dualMap.range := by
  let K := (queryMap ask).ker
  let forms (j : Fin 4) := (topForms hk i j).comp K.subtype
  let four := LinearMap.pi forms
  have out_eq : (fun x : K => cyclicOut hk name c₁ c₂ x.val false i) =
      fun x : K => readout 0 x.val := by
    funext x
    simpa only [zero_run ask x] using correct x.val
  have out_v : Vanishes 4 (fun x : K => cyclicOut hk name c₁ c₂ x.val false i) := by
    rw [out_eq]
    exact comap_v (cubic 0) K.subtype
  have lo : Vanishes 4 (prodFour forms) := by
    have eq : prodFour forms = fun x : K =>
        cyclicOut hk name c₁ c₂ x.val false i - cubicPart hk name c₁ c₂ i x.val := by
      funext x
      change prodFour (topForms hk i) x.val = _
      unfold cubicPart
      ring
    rw [eq]
    exact sub_v out_v (comap_v (cubic_part_v hk large name c₁ c₂ i) K.subtype)
  have notFull : four.range ≠ ⊤ := fun h =>
    not_surjective_four forms lo (LinearMap.range_eq_top.mp h)
  have hasAnnihilator : four.range.dualAnnihilator ≠ ⊥ := by
    intro trivial
    exact notFull ((Submodule.dualAnnihilator_eq_bot_iff (W := four.range)).mp trivial)
  obtain ⟨value, annihilates, nonzero⟩ :=
    (Submodule.ne_bot_iff four.range.dualAnnihilator).mp hasAnnihilator
  have coeffNe : basisValues value ≠ 0 := by
    intro h
    apply nonzero
    apply LinearMap.ext
    intro v
    rw [expand_value, h]
    simp
  refine ⟨basisValues value, coeffNe, ?_⟩
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule.mem_dualAnnihilator]
  intro x hx
  rw [pull_mixed]
  exact (Submodule.mem_dualAnnihilator value).mp annihilates (four ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩

def tapSet {k : ℕ} (hk : 0 < k) (P : Finset (Fin k)) : Finset (Fin k) :=
  P.biUnion (fun i => (Finset.range 5).image (fun j => index hk (i.val + j + 1)))

def Separated {k : ℕ} (hk : 0 < k) (P : Finset (Fin k)) : Prop :=
  ∀ i ∈ P, adv hk i 1 ∉ P ∧ adv hk i 2 ∉ P

def rowTap {k : ℕ} (hk : 0 < k) (i : Fin k) (s : Fin 5) : Fin k :=
  adv hk i (s.val + 1)

private theorem small_mod (k n : ℕ) (h : n < k + k) :
    n % k = if n < k then n else n - k := by
  split
  · exact Nat.mod_eq_of_lt ‹n < k›
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem adv_cancel_offset {k : ℕ} (hk : 0 < k) (i : Fin k) {a b : ℕ}
    (ha : a < k) (hb : b < k) (eq : adv hk i a = adv hk i b) : a = b := by
  have hi := i.isLt
  have h := congrArg Fin.val eq
  change (i.val + a) % k = (i.val + b) % k at h
  rw [small_mod k _ (by omega), small_mod k _ (by omega)] at h
  split at h <;> split at h <;> omega

theorem adv_cancel_row {k : ℕ} (hk : 0 < k) {i j : Fin k} {a : ℕ}
    (ha : a < k) (eq : adv hk i a = adv hk j a) : i = j := by
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have h := congrArg Fin.val eq
  change (i.val + a) % k = (j.val + a) % k at h
  rw [small_mod k _ (by omega), small_mod k _ (by omega)] at h
  split at h <;> split at h <;> omega

private theorem shift_between {k : ℕ} (hk : 0 < k) {i j : Fin k} {a b : ℕ}
    (ha : a < k) (ordered : a ≤ b) (eq : adv hk i a = adv hk j b) :
    i = adv hk j (b - a) := by
  apply adv_cancel_row hk ha
  rw [adv_add, show b - a + a = b by omega]
  exact eq

private theorem offset_set_gap {k : ℕ} (hk : 0 < k) {P : Finset (Fin k)}
    (separated : Separated hk P) {i j : Fin k} (hi : i ∈ P) (hj : j ∈ P) (ne : i ≠ j)
    {a b : ℕ} (ha : a < k) (hb : b < k) (eq : adv hk i a = adv hk j b) :
    a + 3 ≤ b ∨ b + 3 ≤ a := by
  have gap {u v : Fin k} (hu : u ∈ P) (hv : v ∈ P) (different : u ≠ v)
      {c e : ℕ} (hc : c < k) (order : c ≤ e) (same : adv hk u c = adv hk v e) :
      c + 3 ≤ e := by
    have move := shift_between hk hc order same
    by_contra close
    have opts : e - c = 0 ∨ e - c = 1 ∨ e - c = 2 := by omega
    rcases opts with sz | sz | sz
    · apply different
      simpa only [sz, adv_zero] using move
    · rw [sz] at move
      exact (separated v hv).1 (move ▸ hu)
    · rw [sz] at move
      exact (separated v hv).2 (move ▸ hu)
  by_cases order : a ≤ b
  · exact Or.inl (gap hi hj ne ha order eq)
  · exact Or.inr (gap hj hi (Ne.symm ne) hb (by omega) eq.symm)

theorem rowTap_inj {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) (i : Fin k) :
    Function.Injective (rowTap hk i) := by
  intro r s eq
  have rr := r.isLt
  have ss := s.isLt
  have h := adv_cancel_offset hk i (by omega : r.val + 1 < k) (by omega : s.val + 1 < k) eq
  exact Fin.ext (by omega)

private def rowSingle {k : ℕ} (hk : 0 < k) (i : Fin k) (s : Fin 5) (u : F) : W k :=
  Pi.single (rowTap hk i s) u

theorem mixed_at {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) (i : Fin k)
    (p : Fin 4 → F) (s : Fin 5) :
    mixedCoeff hk i p (rowTap hk i s) = ![p 2,p 0,p 2 + p 3,p 1,p 3] s := by
  have compare (a b : Fin 5) (u : F) :
      rowSingle hk i a u (rowTap hk i b) = if a = b then u else 0 := by
    simp only [rowSingle, Pi.single_apply, (rowTap_inj hk large i).eq_iff]
    by_cases h : a = b <;> simp [h, Ne.symm]
  change (rowSingle hk i 0 (p 2) + rowSingle hk i 1 (p 0) +
      rowSingle hk i 2 (p 2 + p 3) + rowSingle hk i 3 (p 1) +
      rowSingle hk i 4 (p 3)) (rowTap hk i s) = _
  simp only [Pi.add_apply, compare]
  fin_cases s <;> simp

theorem mixed_support {k : ℕ} (hk : 0 < k) (i : Fin k) (p : Fin 4 → F)
    {z : Fin k} (nonzero : mixedCoeff hk i p z ≠ 0) :
    ∃ s : Fin 5, rowTap hk i s = z := by
  by_contra none
  have away (r : Fin 5) : rowTap hk i r ≠ z := fun h => none ⟨r,h⟩
  apply nonzero
  change (rowSingle hk i 0 (p 2) + rowSingle hk i 1 (p 0) +
      rowSingle hk i 2 (p 2 + p 3) + rowSingle hk i 3 (p 1) +
      rowSingle hk i 4 (p 3)) z = 0
  simp [rowSingle, away, Ne.symm]

theorem mixed_supported_on_taps {k : ℕ} (hk : 0 < k) {P : Finset (Fin k)}
    {i : Fin k} (hi : i ∈ P) (p : Fin 4 → F) {z : Fin k} (outside : z ∉ tapSet hk P) :
    mixedCoeff hk i p z = 0 := by
  by_contra hn
  obtain ⟨s, hs⟩ := mixed_support hk i p hn
  exact outside (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr
    ⟨s.val, Finset.mem_range.mpr s.isLt, hs⟩⟩)

theorem mixed_nonzero {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) (i : Fin k) {p : Fin 4 → F}
    (hp : p ≠ 0) : mixedCoeff hk i p ≠ 0 := by
  intro vanished
  apply hp
  have value (s : Fin 5) : ![p 2,p 0,p 2 + p 3,p 1,p 3] s = 0 :=
    (mixed_at hk large i p s).symm.trans (congrFun vanished (rowTap hk i s))
  funext j
  fin_cases j
  · exact value 1
  · exact value 3
  · exact value 0
  · exact value 4

theorem mixed_sparsity {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) {P : Finset (Fin k)}
    (separated : Separated hk P) (p : P → Fin 4 → F) (z : Fin k) :
    (visible (fun i : P => mixedCoeff hk i.val (p i)) z).card ≤ 2 := by
  by_contra crowded
  obtain ⟨i,hi,j,hj,l,hl,ij,il,jl⟩ := Finset.two_lt_card.mp (by omega :
    2 < (visible (fun i : P => mixedCoeff hk i.val (p i)) z).card)
  have present (w : P) (hw : w ∈ visible (fun i : P => mixedCoeff hk i.val (p i)) z) :
      ∃ a : Fin 5, rowTap hk w.val a = z :=
    mixed_support hk w.val (p w) ((mem_visible (fun i : P => mixedCoeff hk i.val (p i)) w z).mp hw)
  obtain ⟨a,ha⟩ := present i hi
  obtain ⟨b,hb⟩ := present j hj
  obtain ⟨c,hc⟩ := present l hl
  have ap := a.isLt
  have bp := b.isLt
  have cp := c.isLt
  have pair {u v : P} (uv : u ≠ v) {s t : Fin 5} (same : rowTap hk u.val s = rowTap hk v.val t) :
      s.val + 3 ≤ t.val ∨ t.val + 3 ≤ s.val := by
    have sp := s.isLt
    have tp := t.isLt
    have gaps := offset_set_gap hk separated u.property v.property
      (fun eq => uv (Subtype.ext eq)) (by omega : s.val + 1 < k)
      (by omega : t.val + 1 < k) same
    omega
  have g₁ := pair ij (ha.trans hb.symm)
  have g₂ := pair il (ha.trans hc.symm)
  have g₃ := pair jl (hb.trans hc.symm)
  omega

private theorem overlap_offsets {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) {i j : Fin k}
    {d : ℕ} (hd : 3 ≤ d ∧ d ≤ 4) (ordered : j = adv hk i d) {r s : Fin 5}
    (eq : rowTap hk i r = rowTap hk j s) : r.val = d + s.val := by
  have rp := r.isLt
  have sp := s.isLt
  have hr : r.val + 1 < k := by omega
  have e : adv hk i (r.val + 1) = adv hk i (d + (s.val + 1)) := by
    simpa only [rowTap, ordered, adv_add] using eq
  by_cases short : d + (s.val + 1) < k
  · have h := adv_cancel_offset hk i hr short e
    omega
  · have atEnd : d + (s.val + 1) = k := by omega
    rw [atEnd, adv_width] at e
    have h := adv_cancel_offset hk i hr hk (e.trans (adv_zero hk i).symm)
    omega

private theorem distinct_ordered {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) {i j : Fin k}
    {d : ℕ} (hd : 3 ≤ d ∧ d ≤ 4) (ordered : j = adv hk i d) {p q : Fin 4 → F}
    (hp : p ≠ 0) : mixedCoeff hk i p ≠ mixedCoeff hk j q := by
  intro equal
  have agree (z : Fin k) := congrFun equal z
  have early (r : Fin 5) (lim : r.val < 3) : mixedCoeff hk i p (rowTap hk i r) = 0 := by
    by_contra hn
    have other : mixedCoeff hk j q (rowTap hk i r) ≠ 0 := fun h => hn ((agree _).trans h)
    obtain ⟨s, hs⟩ := mixed_support hk j q other
    have rel := overlap_offsets hk large hd ordered hs.symm
    omega
  have late (s : Fin 5) (lim : 2 ≤ s.val) : mixedCoeff hk j q (rowTap hk j s) = 0 := by
    by_contra hn
    have other : mixedCoeff hk i p (rowTap hk j s) ≠ 0 := fun h => hn ((agree _).symm.trans h)
    obtain ⟨r, hr⟩ := mixed_support hk i p other
    have rel := overlap_offsets hk large hd ordered hr
    have rp := r.isLt
    omega
  have q3 : q 3 = 0 :=
    (mixed_at hk large j q 4).symm.trans (late 4 (by decide))
  have q2q3 : q 2 + q 3 = 0 :=
    (mixed_at hk large j q 2).symm.trans (late 2 (by decide))
  have qFirst : mixedCoeff hk j q (rowTap hk j 0) = 0 := by
    have q2 : q 2 = 0 := by simpa only [q3, add_zero] using q2q3
    exact (mixed_at hk large j q 0).trans q2
  have fourth : mixedCoeff hk i p (rowTap hk i 3) = 0 := by
    by_contra hn
    have hn' : mixedCoeff hk j q (rowTap hk i 3) ≠ 0 := fun h => hn ((agree _).trans h)
    obtain ⟨s, hs⟩ := mixed_support hk j q hn'
    have rel := overlap_offsets hk large hd ordered hs.symm
    have last : s = 0 := Fin.ext (by change 3 = d + s.val at rel; omega)
    subst s
    exact hn' (hs ▸ qFirst)
  have p0 : p 0 = 0 := (mixed_at hk large i p 1).symm.trans (early 1 (by decide))
  have p1 : p 1 = 0 := (mixed_at hk large i p 3).symm.trans fourth
  have p2 : p 2 = 0 := (mixed_at hk large i p 0).symm.trans (early 0 (by decide))
  have p3 : p 3 = 0 := by
    have p23 : p 2 + p 3 = 0 := (mixed_at hk large i p 2).symm.trans (early 2 (by decide))
    simpa only [p2, zero_add] using p23
  apply hp
  funext a
  fin_cases a <;> assumption

theorem mixed_distinct {k : ℕ} (hk : 0 < k) (large : 9 ≤ k) {P : Finset (Fin k)}
    (separated : Separated hk P) (p : P → Fin 4 → F) (nonzero : ∀ i, p i ≠ 0) :
    Function.Injective (fun i : P => mixedCoeff hk i.val (p i)) := by
  intro i j eq
  change mixedCoeff hk i.val (p i) = mixedCoeff hk j.val (p j) at eq
  by_contra ne
  have support : ∃ z, mixedCoeff hk i.val (p i) z ≠ 0 := by
    by_contra none
    push Not at none
    exact mixed_nonzero hk large _ (nonzero i) (funext none)
  obtain ⟨z,nz⟩ := support
  obtain ⟨r,hr⟩ := mixed_support hk i.val (p i) nz
  have hn : mixedCoeff hk j.val (p j) z ≠ 0 := by rw [← eq]; exact nz
  obtain ⟨s,hs⟩ := mixed_support hk j.val (p j) hn
  have rl := r.isLt
  have sl := s.isLt
  have h := hr.trans hs.symm
  have g := offset_set_gap hk separated i.property j.property (fun e => ne (Subtype.ext e))
    (by omega : r.val + 1 < k) (by omega : s.val + 1 < k) h
  rcases g with rs | sr
  · have move := shift_between hk (by omega : r.val + 1 < k) (by omega :
      r.val + 1 ≤ s.val + 1) h
    exact distinct_ordered hk large (by omega : 3 ≤ (s.val + 1) - (r.val + 1) ∧
      (s.val + 1) - (r.val + 1) ≤ 4) move (nonzero j) eq.symm
  · have move := shift_between hk (by omega : s.val + 1 < k) (by omega :
      s.val + 1 ≤ r.val + 1) h.symm
    exact distinct_ordered hk large (by omega : 3 ≤ (r.val + 1) - (s.val + 1) ∧
      (r.val + 1) - (s.val + 1) ≤ 4) move (nonzero i) eq

def supported {k : ℕ} (S : Finset (Fin k)) : Submodule F (W k) := by
  refine { carrier := {v | ∀ i, i ∉ S → v i = 0}, zero_mem' := ?_, add_mem' := ?_, smul_mem' := ?_ }
  · intro a b ha hb i hi
    change a i + b i = 0
    rw [ha i hi, hb i hi, zero_add]
  · simp
  · intro c a ha i hi
    change c * a i = 0
    rw [ha i hi, mul_zero]

def missedResidues {k : ℕ} (S : Finset (Fin k)) : Finset ℕ :=
  ((Finset.univ : Finset (Fin k)) \ S).image (fun i => i.val % 3)

def mixEach {k : ℕ} (hk : 0 < k) (a : W k) (n : ℕ) : F :=
  a (index hk n)

theorem shift_index {k : ℕ} (hk : 0 < k) (n m : ℕ) :
    adv hk (index hk n) m = index hk (n + m) := by
  apply Fin.ext
  exact Nat.mod_add_mod n k m

private theorem pull_local_eq {k : ℕ} (hk : 0 < k) (large : 1 < k) (a : W k)
    (zero : pull hk a = 0) (p : Fin k) :
    a p + a (back hk p 1) + a (adv hk p 1) = 0 := by
  let e (i : Fin k) : W k := Pi.single i 1
  let x : W k := fun i => e p (adv hk i 1)
  have recover : rotLin hk 1 x = e p := by
    funext i
    simp only [rot_apply, x, adv_after_back hk large]
  have eq : ∑ j : Fin k, a j * mixLin hk 1 (e p) j = 0 := by
    have eval := congrArg (fun f : Form k => f x) zero
    simp only [pull_eval, firstMix, LinearMap.comp_apply, recover, LinearMap.zero_apply] at eval
    exact eval
  have eqNext (j : Fin k) : adv hk j 1 = p ↔ j = back hk p 1 := by
    constructor
    · intro same
      rw [← same, back_after_adv hk large]
    · intro same
      rw [same, adv_after_back hk large]
  have eqPrev (j : Fin k) : back hk j 1 = p ↔ j = adv hk p 1 := by
    constructor
    · intro same
      rw [← same, adv_after_back hk large]
    · intro same
      rw [same, back_after_adv hk large]
  have nextVal (j : Fin k) : e p (adv hk j 1) = e (back hk p 1) j := by
    simp only [e, Pi.single_apply, eqNext]
  have prevVal (j : Fin k) : e p (back hk j 1) = e (adv hk p 1) j := by
    simp only [e, Pi.single_apply, eqPrev]
  have select (r : Fin k) : (∑ j : Fin k, a j * e r j) = a r := by
    simp [e, Pi.single_apply, mul_ite]
  simp only [mix_apply, mul_add, Finset.sum_add_distrib, nextVal, prevVal, select] at eq
  exact eq

theorem pull_recurrence {k : ℕ} (hk : 0 < k) (large : 1 < k) (a : W k)
    (zero : pull hk a = 0) (n : ℕ) :
    mixEach hk a (n + 2) = mixEach hk a n + mixEach hk a (n + 1) := by
  have eq := pull_local_eq hk large a zero (index hk (n + 1))
  have prev : back hk (index hk (n + 1)) 1 = index hk n := by
    rw [← shift_index hk n 1, back_after_adv hk large]
  rw [prev, shift_index] at eq
  exact (add_eq_zero_bits eq).symm.trans (add_comm _ _)

private theorem period_mod (v : ℕ → F) (period : ∀ n, v (n + 3) = v n) (n : ℕ) :
    v n = v (n % 3) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases small : n < 3
    · simp [Nat.mod_eq_of_lt small]
    · have eq : n - 3 + 3 = n := by omega
      calc
        v n = v (n - 3) := eq ▸ period (n - 3)
        _ = v ((n - 3) % 3) := ih _ (by omega)
        _ = v (n % 3) := congrArg v (by omega)

theorem mix_period {k : ℕ} (hk : 0 < k) (large : 1 < k) (a : W k)
    (zero : pull hk a = 0) (n : ℕ) :
    mixEach hk a n = mixEach hk a (n % 3) := by
  apply period_mod
  intro i
  calc
    mixEach hk a (i + 3) = mixEach hk a (i + 1) + mixEach hk a (i + 2) :=
      pull_recurrence hk large a zero (i + 1)
    _ = mixEach hk a (i + 1) + (mixEach hk a i + mixEach hk a (i + 1)) := by
      rw [pull_recurrence hk large a zero i]
    _ = mixEach hk a i := by rw [add_left_comm, ZModModule.add_self, add_zero]

private theorem mix_cycle {k : ℕ} (hk : 0 < k) (a : W k) (n : ℕ) :
    mixEach hk a (n + k) = mixEach hk a n := by
  unfold mixEach
  apply congrArg a
  apply Fin.ext
  simp [index]

private theorem zero_from_starts {k : ℕ} (hk : 0 < k) (large : 1 < k) (a : W k)
    (zero : pull hk a = 0) (a₀ : mixEach hk a 0 = 0) (a₁ : mixEach hk a 1 = 0) :
    a = 0 := by
  have a₂ : mixEach hk a 2 = 0 := by simpa [a₀, a₁] using pull_recurrence hk large a zero 0
  funext i
  have atI : a i = mixEach hk a i.val := by
    unfold mixEach
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt i.isLt).symm
  rw [atI, mix_period hk large a zero]
  have cases : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by omega
  rcases cases with h | h | h <;> rw [h] <;> assumption

theorem pull_kernel_odd_period {k : ℕ} (hk : 0 < k) (large : 1 < k)
    (off : k % 3 ≠ 0) (a : W k) (zero : pull hk a = 0) : a = 0 := by
  let v := mixEach hk a
  have bridge (n : ℕ) : v n = v ((n + k) % 3) :=
    (mix_cycle hk a n).symm.trans (mix_period hk large a zero (n + k))
  have periodCase : k % 3 = 1 ∨ k % 3 = 2 := by omega
  have rel : v 0 = v 1 ∧ v 0 = v 2 := by
    rcases periodCase with h | h
    · have r₀ : v 0 = v 1 := by simpa only [Nat.zero_add, h] using bridge 0
      have r₁ : v 1 = v 2 := by simpa only [show (1 + k) % 3 = 2 by omega] using bridge 1
      exact ⟨r₀, r₀.trans r₁⟩
    · have r₀ : v 0 = v 2 := by simpa only [Nat.zero_add, h] using bridge 0
      have r₁ : v 1 = v 0 := by simpa only [show (1 + k) % 3 = 0 by omega] using bridge 1
      exact ⟨r₁.symm, r₀⟩
  have hsum : v 2 = v 0 + v 1 := pull_recurrence hk large a zero 0
  rw [← rel.1, ← rel.2, ZModModule.add_self] at hsum
  exact zero_from_starts hk large a zero hsum (rel.1.symm.trans hsum)

private theorem zeros_of_two {v : ℕ → F} (rel : v 2 = v 0 + v 1) {r s : ℕ}
    (hr : r < 3) (hs : s < 3) (ne : r ≠ s) (vr : v r = 0) (vs : v s = 0) :
    v 0 = 0 ∧ v 1 = 0 := by
  interval_cases r <;> interval_cases s <;> simp_all

theorem pull_kernel_loss {k : ℕ} (hk : 0 < k) (large : 1 < k)
    (S : Finset (Fin k)) (T : Submodule F (W k)) (contained : T ≤ supported S) :
    Module.finrank F ((pull hk).comp T.subtype).ker ≤
      if k % 3 = 0 then 2 - (missedResidues S).card else 0 := by
  classical
  let B := (pull hk).comp T.subtype
  let H := B.ker
  let raw : H →ₗ[F] W k := T.subtype.comp H.subtype
  let sample (n : ℕ) : H →ₗ[F] F := (coord (index hk n)).comp raw
  change Module.finrank F H ≤ _
  have kill (x : H) : pull hk (raw x) = 0 :=
    LinearMap.mem_ker.mp x.property
  have from_two (x : H) (first : sample 0 x = 0) (second : sample 1 x = 0) :
      x = 0 := by
    have orig := zero_from_starts hk large (raw x) (kill x) first second
    exact Subtype.ext (Subtype.ext orig)
  have vanish_sample (x : H) {r : ℕ} (hr : r ∈ missedResidues S) :
      sample r x = 0 := by
    obtain ⟨i, mem, eq⟩ := Finset.mem_image.mp hr
    have out : i ∉ S := (Finset.mem_sdiff.mp mem).2
    have point : raw x i = 0 := (contained x.val.property) i out
    have period := mix_period hk large (raw x) (kill x) i.val
    have atI : mixEach hk (raw x) i.val = raw x i := by
      unfold mixEach
      apply congrArg (raw x)
      exact Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [atI, eq, point] at period
    exact period.symm
  have below {r : ℕ} (hr : r ∈ missedResidues S) : r < 3 := by
    obtain ⟨i, _, eq⟩ := Finset.mem_image.mp hr
    exact eq ▸ Nat.mod_lt _ (by decide)
  have zero_dim (all : ∀ x : H, x = 0) : Module.finrank F H = 0 := by
    have bot : H = ⊥ := H.eq_bot_iff.mpr (fun x hx => congrArg Subtype.val (all ⟨x,hx⟩))
    rw [bot, finrank_bot]
  by_cases div : k % 3 = 0
  · rw [ite_eq_left div]
    by_cases empty : (missedResidues S).card = 0
    · let E : H →ₗ[F] F × F := (sample 0).prod (sample 1)
      have inject : Function.Injective E := by
        intro x y eq
        have e₀ : sample 0 x = sample 0 y := congrArg Prod.fst eq
        have e₁ : sample 1 x = sample 1 y := congrArg Prod.snd eq
        have z₀ : sample 0 (x + y) = 0 := by rw [(sample 0).map_add, e₀, ZModModule.add_self]
        have z₁ : sample 1 (x + y) = 0 := by rw [(sample 1).map_add, e₁, ZModModule.add_self]
        exact (add_eq_zero_iff_eq_neg.mp (from_two (x + y) z₀ z₁)).trans (ZModModule.neg_eq_self y)
      have rank := LinearMap.finrank_le_finrank_of_injective inject
      simpa [Module.finrank_prod, empty] using rank
    · by_cases single : (missedResidues S).card = 1
      · obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0 < (missedResidues S).card)
        let s := if r = 0 then 1 else 0
        have slt : s < 3 := by dsimp [s]; split <;> decide
        have distinct : r ≠ s := by dsimp [s]; split <;> omega
        have inject : Function.Injective (sample s) := by
          intro x y eq
          let total := x + y
          have other : sample s total = 0 := by dsimp [total]; rw [(sample s).map_add, eq, ZModModule.add_self]
          have zeros := zeros_of_two (pull_recurrence hk large (raw total) (kill total) 0)
            (below hr) slt distinct (vanish_sample total hr) other
          exact (add_eq_zero_iff_eq_neg.mp (from_two total zeros.1 zeros.2)).trans (ZModModule.neg_eq_self y)
        have rank := LinearMap.finrank_le_finrank_of_injective inject
        simpa [single] using rank
      · obtain ⟨r,hr,s,hs,distinct⟩ :=
          Finset.one_lt_card.mp (by omega : 1 < (missedResidues S).card)
        have rank := zero_dim fun x =>
          have zeros := zeros_of_two (pull_recurrence hk large (raw x) (kill x) 0)
            (below hr) (below hs) distinct (vanish_sample x hr) (vanish_sample x hs)
          from_two x zeros.1 zeros.2
        omega
  · rw [ite_eq_right div]
    have rank := zero_dim (fun x => Subtype.ext (Subtype.ext
      (pull_kernel_odd_period hk large div (raw x) (kill x))))
    omega

theorem separated_lower {k : ℕ} (hk : 0 < k) (large : 9 ≤ k)
    (mark : Fin k → Bool × Bool) (P : Finset (Fin k)) (d : ℕ)
    (name c₁ c₂ : Bool → W k) (marks : ∀ i ∈ P, (mark i).1 = true)
    (sep : Separated hk P) (fits : Fits hk mark d name c₁ c₂) :
    2 * P.card ≤ 3 * (d + if k % 3 = 0 then 2 - (missedResidues (tapSet hk P)).card else 0) := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have big : 1 < k := by omega
  obtain ⟨ask, out, cubic, correct⟩ := fits
  have exists_vector (i : P) : ∃ p : Fin 4 → F, p ≠ 0 ∧
      pull hk (mixedCoeff hk i.val p) ∈ (queryMap ask).dualMap.range := by
    apply marked_coeff hk big name c₁ c₂ ask (fun h => out h false i.val) i.val
    · intro h
      exact (v_iff_cubic _).mpr (cubic h false i.val)
    · intro x
      exact correct x false i.val (marks i.val i.property)
  choose p pnonzero pquery using exists_vector
  let a (i : P) := mixedCoeff hk i.val (p i)
  let A := columnMap a
  have col_rank : 2 * P.card ≤ 3 * Module.finrank F A.range := by
    have rank := sparse_rank a (mixed_sparsity hk large sep p)
      (fun i => mixed_nonzero hk large i.val (pnonzero i)) (mixed_distinct hk large sep p pnonzero)
    simpa only [Fintype.card_coe] using rank
  have expand (x : P → F) : A x = ∑ i : P, x i • a i := by
    funext j
    simp only [A, column_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have support : A.range ≤ supported (tapSet hk P) := by
    rintro _ ⟨x, rfl⟩ j off
    change A x j = 0
    rw [expand, Finset.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    change x i * mixedCoeff hk i.val (p i) j = 0
    rw [mixed_supported_on_taps hk i.property _ off, mul_zero]
  have querySpan : ((pull hk).comp A).range ≤ (queryMap ask).dualMap.range := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.comp_apply, expand, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact Submodule.smul_mem _ (x i) (pquery i)
  let B := (pull hk).comp A.range.subtype
  have B_range : B.range = ((pull hk).comp A).range := by
    unfold B
    rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_comp]
  have queryBound : Module.finrank F B.range ≤ d := by
    rw [B_range]
    refine (Submodule.finrank_mono querySpan).trans ?_
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range]
    have rank := (queryMap ask).range.finrank_le
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using rank
  have loss := pull_kernel_loss hk big (tapSet hk P) A.range support
  change Module.finrank F B.ker ≤ _ at loss
  have dimension := B.finrank_range_add_finrank_ker
  omega

def blockWidth (t : ℕ) : ℕ := 9 * t + 1

theorem width_pos (t : ℕ) : 0 < blockWidth t := by unfold blockWidth; omega

def blockMark (t : ℕ) (i : Fin (blockWidth t)) : Bool × Bool :=
  (decide (i.val < 9 * t ∧ i.val % 3 = 0), false)

def everyThird (t : ℕ) : Fin (3 * t) ↪ Fin (blockWidth t) where
  toFun i := ⟨3 * i.val, by
    have h := i.isLt
    unfold blockWidth
    omega⟩
  inj' := by
    intro i j h
    have hv : 3 * i.val = 3 * j.val := congrArg Fin.val h
    exact Fin.ext (by omega)

def blockSet (t : ℕ) : Finset (Fin (blockWidth t)) :=
  Finset.univ.map (everyThird t)

theorem block_card (t : ℕ) : (blockSet t).card = 3 * t := by simp [blockSet]

theorem block_mem (t : ℕ) (i : Fin (blockWidth t)) :
    i ∈ blockSet t ↔ i.val < 9 * t ∧ i.val % 3 = 0 := by
  rw [blockSet, Finset.mem_map]
  constructor
  · rintro ⟨j, _, eq⟩
    have hj := j.isLt
    have eqVal : 3 * j.val = i.val := congrArg Fin.val eq
    omega
  · intro ok
    let j : Fin (3 * t) := ⟨i.val / 3, by omega⟩
    refine ⟨j, Finset.mem_univ _, Fin.ext ?_⟩
    change 3 * (i.val / 3) = i.val
    omega

theorem block_separated (t : ℕ) : Separated (width_pos t) (blockSet t) := by
  intro i hi
  have mi := (block_mem t i).mp hi
  have miss_shift (s : ℕ) (hs : s = 1 ∨ s = 2) : adv (width_pos t) i s ∉ blockSet t := by
    intro member
    have mv := (block_mem t _).mp member
    have bound : i.val + s < blockWidth t := by unfold blockWidth; omega
    have near : (adv (width_pos t) i s).val = i.val + s :=
      Nat.mod_eq_of_lt bound
    rw [near] at mv
    omega
  exact ⟨miss_shift 1 (Or.inl rfl), miss_shift 2 (Or.inr rfl)⟩

private theorem equal_answers {k d : ℕ} (ask : Fin d → Form k) {x y : W k}
    (h : runAsk (fun j _ => ask j) x = runAsk (fun j _ => ask j) y) :
    ∀ j, ask j x = ask j y := by
  let bit (a : W k) (j : Fin d) : ℕ := if ask j a = 0 then 0 else 1
  let fold (a : W k) (js : List (Fin d)) := js.foldl (fun n j => 2 * n + bit a j) 0
  have all (js : List (Fin d)) (same : fold x js = fold y js) :
      ∀ j ∈ js, ask j x = ask j y := by
    induction js using List.reverseRecOn with
    | nil => intro j hj; simp at hj
    | append_singleton js last ih =>
      have final : 2 * fold x js + bit x last = 2 * fold y js + bit y last := by
        simpa only [fold, List.foldl_append, List.foldl_cons, List.foldl_nil] using same
      have atMost (a : W k) : bit a last ≤ 1 := by dsimp [bit]; split <;> omega
      have priorEq : fold x js = fold y js := by have := atMost x; have := atMost y; omega
      have bitEq : bit x last = bit y last := by omega
      have result : ask last x = ask last y := by
        by_cases zx : ask last x = 0 <;> by_cases zy : ask last y = 0
        · rw [zx, zy]
        · simp [bit, zx, zy] at bitEq
        · simp [bit, zx, zy] at bitEq
        · exact (bit_one _ zx).trans (bit_one _ zy).symm
      intro j mem
      rcases List.mem_append.mp mem with prior | final
      · exact ih priorEq j prior
      · have he : j = last := List.mem_singleton.mp final
        simpa only [he] using result
  exact fun j => all (List.finRange d) h j (List.mem_finRange j)

noncomputable def representative {E : Type*} [Zero E] (view : E → ℕ) (h : ℕ) : E := by
  classical
  exact if hs : ∃ x, view x = h then Classical.choose hs else 0

theorem representative_ok {E : Type*} [Zero E] (view : E → ℕ) (x : E) :
    view (representative view (view x)) = view x := by
  classical
  have existsHere : ∃ y, view y = view x := ⟨x,rfl⟩
  unfold representative
  rw [dite_eq_left existsHere]
  exact Classical.choose_spec existsHere

def pinnedForm {k : ℕ} (hk : 0 < k) (i : Fin k) : Form k :=
  if i.val % 9 = 0 then tap hk i 4 else
    if i.val % 9 = 3 then tap hk i 1 + tap hk i 5 else tap hk i 2

def reducedProduct {k : ℕ} (hk : 0 < k) (i : Fin k) (a : F) : W k → F :=
  let first := tap hk i 1 + tap hk i 3
  let second := tap hk i 3 + tap hk i 5
  if i.val % 9 = 0 then fun x => a * (tap hk i 2 x * first x * second x)
  else if i.val % 9 = 3 then fun x => (1+a) * (tap hk i 2 x * tap hk i 4 x * first x)
  else fun x => a * (tap hk i 4 x * first x * second x)

theorem reduced_v {k : ℕ} (hk : 0 < k) (i : Fin k) (a : F) :
    Vanishes 4 (reducedProduct hk i a) := by
  have cube (c : F) (U V W : Form k) :
      Vanishes 4 (fun x => c * (U x * V x * W x)) :=
    mul_v 0 3 (const_v _) (mul_v 2 1 (mul_v 1 1 (lin_v _) (lin_v _)) (lin_v _))
  by_cases first : i.val % 9 = 0
  · simpa only [reducedProduct, ite_eq_left first] using
      cube a (tap hk i 2) (tap hk i 1 + tap hk i 3) (tap hk i 3 + tap hk i 5)
  · by_cases mid : i.val % 9 = 3
    · simpa only [reducedProduct, ite_eq_right first, ite_eq_left mid] using
        cube (1+a) (tap hk i 2) (tap hk i 4) (tap hk i 1 + tap hk i 3)
    · simpa only [reducedProduct, ite_eq_right first, ite_eq_right mid] using
        cube a (tap hk i 4) (tap hk i 1 + tap hk i 3) (tap hk i 3 + tap hk i 5)

private theorem middle_identity (a b c d e : F) :
    b*d*(a+c)*(c+e) = (1+(a+e))*(b*d*(a+c)) := by
  decide +revert +kernel

theorem pinned_product {k : ℕ} (hk : 0 < k) (i : Fin k) (x : W k) :
    prodFour (topForms hk i) x = reducedProduct hk i (pinnedForm hk i x) x := by
  change tap hk i 2 x * tap hk i 4 x * (tap hk i 1 + tap hk i 3) x *
    (tap hk i 3 + tap hk i 5) x = _
  by_cases first : i.val % 9 = 0
  · simp only [pinnedForm, reducedProduct, ite_eq_left first]
    ring
  · by_cases mid : i.val % 9 = 3
    · simp only [pinnedForm, reducedProduct, ite_eq_right first, ite_eq_left mid,
        LinearMap.add_apply]
      exact middle_identity _ _ _ _ _
    · simp only [pinnedForm, reducedProduct, ite_eq_right first, ite_eq_right mid]
      ring

def scheduled {d : ℕ} (t : ℕ) (q : Fin d) : Form (blockWidth t) :=
  if q.val < 2 * t then
    zform (width_pos t) (index (width_pos t) (9 * (q.val / 2) + if q.val % 2 = 0 then 4 else 8))
  else 0

theorem pinned_answers {t d : ℕ} (enough : 2 * t ≤ d) {i : Fin (blockWidth t)}
    (mark : (blockMark t i).1 = true) {x y : W (blockWidth t)}
    (same : ∀ j : Fin d, scheduled t j x = scheduled t j y) :
    pinnedForm (width_pos t) i x = pinnedForm (width_pos t) i y := by
  have raw : i.val < 9 * t ∧ i.val % 3 = 0 := of_decide_eq_true mark
  let b := i.val / 9
  have ib : i.val = 9 * b + i.val % 9 := by dsimp [b]; omega
  have blocks : b < t := by omega
  let left : Fin d := ⟨2 * b, by omega⟩
  let right : Fin d := ⟨2 * b + 1, by omega⟩
  have chooseLeft : left.val < 2 * t := by dsimp [left]; omega
  have chooseRight : right.val < 2 * t := by dsimp [right]; omega
  have eq4 : zform (width_pos t) (index (width_pos t) (9 * b + 4)) x =
      zform (width_pos t) (index (width_pos t) (9 * b + 4)) y := by
    simpa only [scheduled, ite_eq_left chooseLeft, show left.val / 2 = b by dsimp [left]; omega,
      show left.val % 2 = 0 by dsimp [left]; omega, ite_true] using same left
  have eq8 : zform (width_pos t) (index (width_pos t) (9 * b + 8)) x =
      zform (width_pos t) (index (width_pos t) (9 * b + 8)) y := by
    simpa only [scheduled, ite_eq_left chooseRight, show right.val / 2 = b by dsimp [right]; omega,
      show ¬right.val % 2 = 0 by dsimp [right]; omega, ite_false] using same right
  have row : i.val % 9 = 0 ∨ i.val % 9 = 3 ∨ i.val % 9 = 6 := by omega
  rcases row with first | mid | last
  · simpa only [pinnedForm, ite_eq_left first, tap, adv, show i.val + 4 = 9 * b + 4 by omega] using eq4
  · have lt : i.val % 9 ≠ 0 := by omega
    simp only [pinnedForm, ite_eq_right lt, ite_eq_left mid, LinearMap.add_apply, tap, adv,
      show i.val + 1 = 9 * b + 4 by omega, show i.val + 5 = 9 * b + 8 by omega, eq4, eq8]
  · have lt : i.val % 9 ≠ 0 := by omega
    have lm : i.val % 9 ≠ 3 := by omega
    simpa only [pinnedForm, ite_eq_right lt, ite_eq_right lm, tap, adv, show i.val + 2 = 9 * b + 8 by omega]
      using eq8

theorem block_upper {t d : ℕ} (positive : 0 < t) (enough : 2 * t ≤ d)
    (name c₁ c₂ : Bool → W (blockWidth t)) :
    Fits (width_pos t) (blockMark t) d name c₁ c₂ := by
  let hk := width_pos t
  have large : 1 < blockWidth t := by unfold blockWidth; omega
  let ask (j : Fin d) (_ : ℕ) := scheduled t j
  let view (x : W (blockWidth t)) := runAsk ask x
  let value (h : ℕ) (i : Fin (blockWidth t)) := pinnedForm hk i (representative view h)
  let output (h : ℕ) (b : Bool) (i : Fin (blockWidth t)) (x : W (blockWidth t)) :=
    if b then 0 else cubicPart hk name c₁ c₂ i x + reducedProduct hk i (value h i) x
  refine ⟨ask, output, ?_, ?_⟩
  · intro h b i
    apply (v_iff_cubic _).mp
    cases b
    · exact add_v (cubic_part_v hk large name c₁ c₂ i) (reduced_v hk i (value h i))
    · exact zero_v _
  · intro x b i mark
    cases b
    · have same : ∀ j : Fin d, scheduled t j (representative view (view x)) = scheduled t j x :=
        equal_answers (scheduled t) (representative_ok view x)
      have pin : value (view x) i = pinnedForm hk i x := pinned_answers enough mark same
      change cyclicOut hk name c₁ c₂ x false i =
        cubicPart hk name c₁ c₂ i x + reducedProduct hk i (value (view x) i) x
      rw [pin, ← pinned_product]
      unfold cubicPart
      ring
    · simp [blockMark] at mark

theorem block_exact {t d : ℕ} (positive : 0 < t) (name c₁ c₂ : Bool → W (blockWidth t)) :
    Fits (width_pos t) (blockMark t) d name c₁ c₂ ↔ 2 * t ≤ d := by
  constructor
  · intro fits
    have big : 9 ≤ blockWidth t := by unfold blockWidth; omega
    have marked (i : Fin (blockWidth t)) (hi : i ∈ blockSet t) : (blockMark t i).1 = true :=
      decide_eq_true ((block_mem t i).mp hi)
    have bound := separated_lower (width_pos t) big (blockMark t) (blockSet t) d
      name c₁ c₂ marked (block_separated t) fits
    have noLoss : blockWidth t % 3 ≠ 0 := by unfold blockWidth; omega
    rw [ite_eq_right noLoss, Nat.add_zero, block_card] at bound
    omega
  · intro enough
    exact block_upper positive enough name c₁ c₂

end PEqualNP.Outside.L_meta_29929_aux

open PEqualNP.Outside.L_meta_29929_aux

theorem PEqualNP.Outside.L_meta_29929 : (
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
  (∀ (k : ℕ) (hk : 0 < k), 9 ≤ k →
    ∀ (mark : Fin k → Bool × Bool) (P : Finset (Fin k)) (d : ℕ)
      (name c₁ c₂ : Bool → Fin k → ZMod 2),
      let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
      let taps := P.biUnion (fun i =>
        (Finset.range 5).image (fun j => ix (i.val + j + 1)))
      let missed := ((Finset.univ : Finset (Fin k)) \ taps).image (fun i => i.val % 3)
      let loss := if k % 3 = 0 then 2 - missed.card else 0
      (∀ i ∈ P, (mark i).1 = true) →
      (∀ i ∈ P, ix (i.val + 1) ∉ P ∧ ix (i.val + 2) ∉ P) →
      fits k hk mark d name c₁ c₂ → 2 * P.card ≤ 3 * (d + loss)) ∧
    ∀ (t : ℕ), 0 < t →
      let k := 9 * t + 1
      let hk : 0 < k := Nat.zero_lt_succ _
      let mark := fun i : Fin k => (decide (i.val < 9 * t ∧ i.val % 3 = 0), false)
      ∀ (d : ℕ) (name c₁ c₂ : Bool → Fin k → ZMod 2),
        fits k hk mark d name c₁ c₂ ↔ 2 * t ≤ d
) := by
  change
    (∀ (k : ℕ) (hk : 0 < k), 9 ≤ k →
      ∀ (mark : Fin k → Bool × Bool) (P : Finset (Fin k)) (d : ℕ)
        (name c₁ c₂ : Bool → W k),
        (∀ i ∈ P, (mark i).1 = true) → Separated hk P →
        Fits hk mark d name c₁ c₂ →
        2 * P.card ≤ 3 * (d + if k % 3 = 0 then 2 - (missedResidues (tapSet hk P)).card else 0)) ∧
    (∀ t : ℕ, 0 < t → ∀ (d : ℕ) (name c₁ c₂ : Bool → W (blockWidth t)),
      Fits (width_pos t) (blockMark t) d name c₁ c₂ ↔ 2 * t ≤ d)
  constructor
  · intro k hk large mark P d name c₁ c₂ marks sep fits
    exact separated_lower hk large mark P d name c₁ c₂ marks sep fits
  · intro t positive d name c₁ c₂
    exact block_exact positive name c₁ c₂
