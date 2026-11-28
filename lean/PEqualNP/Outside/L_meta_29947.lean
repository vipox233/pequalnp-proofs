import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29947

namespace Quadratic29947Pair

private def orient (z : ℤ) : ℤ := if 0 ≤ z then 1 else -1

private theorem orient_mul (z : ℤ) : orient z * z = |z| := by
  by_cases h : 0 ≤ z
  · simp [orient,h,abs_of_nonneg h]
  · have neg := le_of_lt (lt_of_not_ge h)
    simp [orient,h,abs_of_nonpos neg]

private theorem oriented_bit (a z : ℤ) (ha : a = 1 ∨ a = -1) :
    orient z * a ≤ 1 := by
  rcases ha with rfl | rfl <;> unfold orient <;> split <;> norm_num

private theorem scale_le_abs (a b z : ℤ) : orient a * orient b * z ≤ |z| := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b <;>
    simp [orient,ha,hb,le_abs_self,neg_le_abs]

theorem paired_sum {X : Type*} [Fintype X] (f g : X → ℤ)
    (hf : ∀ x, f x = 1 ∨ f x = -1) (hg : ∀ x, g x = 1 ∨ g x = -1) :
    |∑ x, f x| + |∑ x, g x| ≤ (Fintype.card X : ℤ) + |∑ x, f x * g x| := by
  let a : ℤ := ∑ x, f x
  let b : ℤ := ∑ x, g x
  calc
    _ = orient a * a + orient b * b := by rw [orient_mul,orient_mul]
    _ = ∑ x, (orient a * f x + orient b * g x) := by
      simp only [a,b,Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ ∑ x, (1 + (orient a * orient b) * (f x * g x)) := by
      apply Finset.sum_le_sum
      intro x _
      have off : 0 ≤ (1 - orient a * f x) * (1 - orient b * g x) :=
        mul_nonneg (sub_nonneg.mpr (oriented_bit _ _ (hf x)))
          (sub_nonneg.mpr (oriented_bit _ _ (hg x)))
      nlinarith only [off]
    _ = (Fintype.card X : ℤ) + (orient a * orient b) * ∑ x, f x * g x := by
      simp [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := add_le_add_right (scale_le_abs _ _ _) _

end Quadratic29947Pair

namespace Quadratic29947Walsh

def character (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem character_add (x y : ZMod 2) :
    character (x + y) = character x * character y := by
  have all : ∀ a b : ZMod 2, character (a + b) = character a * character b := by decide
  exact all x y

theorem character_bound (x : ZMod 2) : character x ≤ 1 := by
  unfold character
  split <;> decide

theorem sum_twist {A : Type*} [AddCommGroup A] [Fintype A] (f : A → ℤ) (h : A) :
    (∑ x, f (x + h)) = ∑ x, f x := by
  apply Fintype.sum_equiv (Equiv.addRight h)
  intro x
  rfl

theorem hom_sum {A : Type*} [AddCommGroup A] [Fintype A] (l : A →+ ZMod 2) :
    (∑ x, character (l x)) = if l = 0 then (Fintype.card A : ℤ) else 0 := by
  classical
  by_cases zero : l = 0
  · simp [zero,character]
  · obtain ⟨t, nonzero⟩ : ∃ t, l t ≠ 0 := by
      by_contra! h
      apply zero
      ext t
      exact h t
    have either : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have one := (either (l t)).resolve_left nonzero
    have equiv := sum_twist (fun x => character (l x)) t
    simp only [l.map_add, character_add, one, show character 1 = -1 by decide,
      ← Finset.sum_mul] at equiv
    rw [if_neg zero]
    linarith

private theorem rearrange (a b c d e : ZMod 2) (h : a + b + c + d = e) :
    a + b = c + d + e := by
  have all : ∀ a b c d e : ZMod 2, a + b + c + d = e → a + b = c + d + e := by decide
  exact all a b c d e h

theorem square_identity {A : Type*} [AddCommGroup A] [Fintype A]
    (q : A → ZMod 2) (polar : A → A →+ ZMod 2)
    (hpolar : ∀ x h, q (x + h) + q x + q h + q 0 = polar h x) :
    (∑ x, character (q x)) ^ 2 =
      (Fintype.card A : ℤ) * ∑ h : A, if polar h = 0 then character (q h + q 0) else 0 := by
  classical
  rw [pow_two]
  calc
    _ = ∑ x : A, ∑ y : A, character (q x) * character (q y) := by
      simp only [Finset.sum_mul,Finset.mul_sum,mul_comm]
    _ = ∑ x : A, ∑ h : A, character (q x) * character (q (h + x)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (sum_twist (fun y => character (q x) * character (q y)) x).symm
    _ = ∑ h : A, ∑ x : A, character (q h + q 0) * character (polar h x) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro h _
      apply Finset.sum_congr rfl
      intro x _
      rw [← character_add, ← character_add, add_comm h x, add_comm (q x)]
      rw [rearrange _ _ _ _ _ (hpolar x h)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      rw [← Finset.mul_sum,hom_sum]
      split <;> ring

theorem square_bound {A : Type*} [AddCommGroup A] [Fintype A]
    (q : A → ZMod 2) (polar : A → A →+ ZMod 2)
    (hpolar : ∀ x h, q (x + h) + q x + q h + q 0 = polar h x) :
    (∑ x, character (q x)) ^ 2 ≤
      (Fintype.card A : ℤ) * (Fintype.card {h : A // polar h = 0} : ℤ) := by
  classical
  rw [square_identity _ _ hpolar]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ h : A, if polar h = 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro h _
      split <;> simp_all [character_bound]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (Fintype.card_of_subtype (Finset.univ.filter fun h : A => polar h = 0)
        (fun h => by simp)).symm

theorem scaled_bound {A : Type*} [AddCommGroup A] [Fintype A]
    (q : A → ZMod 2) (polar : A → A →+ ZMod 2) (e : ℕ)
    (hpolar : ∀ x h, q (x + h) + q x + q h + q 0 = polar h x)
    (capacity : (Fintype.card {h : A // polar h = 0} : ℤ) * 2 ^ (2 * e) ≤ Fintype.card A) :
    2 ^ e * |∑ x, character (q x)| ≤ (Fintype.card A : ℤ) := by
  have power : ((2 : ℤ) ^ e) ^ 2 = 2 ^ (2 * e) := by rw [← pow_mul,Nat.mul_comm e 2]
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow,power,sq_abs]
  calc
    _ ≤ 2 ^ (2 * e) * ((Fintype.card A : ℤ) * Fintype.card {h : A // polar h = 0}) :=
      mul_le_mul_of_nonneg_left (square_bound q polar hpolar) (by positivity)
    _ = (Fintype.card A : ℤ) * ((Fintype.card {h : A // polar h = 0} : ℤ) * 2 ^ (2 * e)) := by ring
    _ ≤ _ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left capacity (by positivity)

abbrev Inputs (n : ℕ) := Fin n → ZMod 2

theorem matrix_capacity (n e : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (polar : Inputs n → Inputs n →+ ZMod 2)
    (entry : ∀ h x, polar h x = dotProduct x (M.mulVec h))
    (rank : 2 * e ≤ M.rank) :
    (Fintype.card {h : Inputs n // polar h = 0} : ℤ) * 2 ^ (2 * e) ≤
      Fintype.card (Inputs n) := by
  classical
  have same (h : Inputs n) : polar h = 0 ↔ h ∈ LinearMap.ker M.mulVecLin := by
    rw [LinearMap.mem_ker]
    change polar h = 0 ↔ M.mulVec h = 0
    constructor
    · intro off
      funext i
      have atSingle : polar h (Pi.single i 1) = 0 := by simp [off]
      rw [entry, single_one_dotProduct] at atSingle
      exact atSingle
    · intro off
      ext x
      simp [entry,off]
  let identification : {h : Inputs n // polar h = 0} ≃ LinearMap.ker M.mulVecLin :=
    { toFun := fun x => ⟨x,(same x).mp x.property⟩
      invFun := fun x => ⟨x,(same x).mpr x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have dim := M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank + Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) =
      Module.finrank (ZMod 2) (Inputs n) at dim
  have room : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) + 2 * e ≤
      Module.finrank (ZMod 2) (Inputs n) := by omega
  have cardinal : Fintype.card {h : Inputs n // polar h = 0} =
      Fintype.card (LinearMap.ker M.mulVecLin) := Fintype.card_congr identification
  rw [cardinal, Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker M.mulVecLin),
      Module.card_eq_pow_finrank (K := ZMod 2) (V := Inputs n), ZMod.card]
  push_cast
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) room

end Quadratic29947Walsh

namespace Quadratic29947Polar
abbrev F := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F V]

def polar (q : V → F) (x y : V) : F :=
  q (x + y) + q x + q y + q 0

theorem add_polar (f g : V → F) (x y : V) :
    polar (fun v => f v + g v) x y = polar f x y + polar g x y := by
  unfold polar
  ring

theorem sum_polar {I : Type*} (s : Finset I) (f : I → V → F) (x y : V) :
    polar (fun v => ∑ i ∈ s, f i v) x y = ∑ i ∈ s, polar (f i) x y := by
  simp only [polar, Finset.sum_add_distrib]

theorem affine_polar (L : V →ₗ[F] F) (b : F) (x y : V) :
    polar (fun v => b + L v) x y = 0 := by
  have all : ∀ b a c : F, (b + (a + c)) + (b + a) + (b + c) + (b + 0) = 0 := by decide
  simpa only [polar,map_add,map_zero] using all b (L x) (L y)

theorem product_polar (L P : V →ₗ[F] F) (b c : F) (x y : V) :
    polar (fun v => (b + L v) * (c + P v)) x y = L x * P y + L y * P x := by
  have all : ∀ b c l₁ l₂ p₁ p₂ : F,
      (b + (l₁ + l₂)) * (c + (p₁ + p₂)) + (b + l₁) * (c + p₁) +
        (b + l₂) * (c + p₂) + (b + 0) * (c + 0) = l₁ * p₂ + l₂ * p₁ := by decide
  simpa only [polar,map_add,map_zero] using all b c (L x) (L y) (P x) (P y)

theorem translated_form {I : Type*} (s : Finset I) (L P : I → V →ₗ[F] F)
    (aff : V →ₗ[F] F) (constant : F) (shift x y : V) :
    polar (fun v => constant + aff (shift + v) + ∑ i ∈ s, L i (shift + v) * P i (shift + v)) x y =
      ∑ i ∈ s, (L i x * P i y + L i y * P i x) := by
  rw [add_polar,sum_polar]
  have a : polar (fun v => constant + aff (shift + v)) x y = 0 := by
    simpa only [map_add, ← add_assoc] using affine_polar aff (constant + aff shift) x y
  rw [a, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [map_add] using product_polar (L i) (P i) (L i shift) (P i shift) x y

theorem common_polar {I : Type*} (s : Finset I) (L P : I → V →ₗ[F] F)
    (b c : Bool → I → F) (A : Bool → V → F)
    (aff : ∀ t, ∃ (k : F) (T : V →ₗ[F] F), ∀ v, A t v = k + T v)
    (x y : V) :
    polar (fun v => A false v + ∑ i ∈ s, (b false i + L i v) * (c false i + P i v)) x y =
      polar (fun v => A true v + ∑ i ∈ s, (b true i + L i v) * (c true i + P i v)) x y := by
  have none (t : Bool) : polar (A t) x y = 0 := by
    obtain ⟨k,T,h⟩ := aff t
    rw [funext h]
    exact affine_polar T k x y
  rw [add_polar,add_polar,none,none,zero_add,zero_add,sum_polar,sum_polar]
  simp only [product_polar]

end Quadratic29947Polar

namespace Quadratic29947Restriction
open Quadratic29947Walsh

theorem rank_restrict (n m : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (independent : P.rank = m) :
    M.rank ≤ (P.transpose * M * P).rank + 2 * (n - m) := by
  have left := Matrix.rank_mul_ge P.transpose M
  have right := Matrix.rank_mul_ge (P.transpose * M) P
  have width := Matrix.rank_le_card_height P
  simp only [Matrix.rank_transpose,independent,Fintype.card_fin] at left right width
  omega

theorem rank_restrict_ge (n m r c : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (independent : P.rank = m)
    (rank : M.rank = 2 * r) (codimension : n - m ≤ c) :
    2 * (r - c) ≤ (P.transpose * M * P).rank := by
  have bound := rank_restrict n m M P independent
  omega

theorem one_leaf (n r c m : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (independent : P.rank = m)
    (rank : M.rank = 2 * r) (codimension : n - m ≤ c)
    (f g : Inputs m → ZMod 2) (polar : Inputs m → Inputs m →+ ZMod 2)
    (entries : ∀ h x, polar h x = dotProduct x ((P.transpose * M * P).mulVec h))
    (hpolar : ∀ x h, (f (x+h) + g (x+h)) + (f x + g x) +
      (f h + g h) + (f 0 + g 0) = polar h x) :
    2 ^ (r - c) * (|∑ x, character (f x)| + |∑ x, character (g x)|) ≤
      (2 ^ (r - c) + 1) * (Fintype.card (Inputs m) : ℤ) := by
  have restrictRank := rank_restrict_ge n m r c M P independent rank codimension
  have square := scaled_bound (fun x => f x + g x) polar (r - c) hpolar
    (matrix_capacity m (r - c) (P.transpose * M * P) polar entries restrictRank)
  have sign (a : ZMod 2) : character a = 1 ∨ character a = -1 := by
    unfold character
    split <;> simp
  have pair := Quadratic29947Pair.paired_sum (fun x => character (f x))
    (fun x => character (g x)) (fun x => sign _) (fun x => sign _)
  simp only [← character_add] at pair
  calc
    _ ≤ 2 ^ (r - c) * ((Fintype.card (Inputs m) : ℤ) + |∑ x, character (f x + g x)|) :=
      mul_le_mul_of_nonneg_left pair (by positivity)
    _ = 2 ^ (r - c) * (Fintype.card (Inputs m) : ℤ) + 2 ^ (r - c) * |∑ x, character (f x + g x)| := by ring
    _ ≤ _ := by rw [add_mul, one_mul]; gcongr

theorem combine_leaves {I : Type*} [Fintype I] (a b mass : I → ℤ) (e n : ℕ)
    (covers : (∑ i, mass i) = 2 ^ n)
    (leaf : ∀ i, 2 ^ e * (|a i| + |b i|) ≤ (2 ^ e + 1) * mass i) :
    2 ^ e * (|∑ i, a i| + |∑ i, b i|) ≤ (2 ^ e + 1) * 2 ^ n := by
  calc
    _ ≤ 2 ^ e * ((∑ i, |a i|) + (∑ i, |b i|)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ i, 2 ^ e * (|a i| + |b i|) := by
      simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib]
    _ ≤ ∑ i, (2 ^ e + 1) * mass i := Finset.sum_le_sum fun i _ => leaf i
    _ = _ := by rw [← Finset.mul_sum,covers]

end Quadratic29947Restriction

namespace Quadratic29947Transport
open Quadratic29947Polar Quadratic29947Walsh Quadratic29947Restriction

theorem compose_polar {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] (q : W → ZMod 2) (L : V →ₗ[ZMod 2] W)
    (x y : V) : polar (fun v => q (L v)) x y = polar q (L x) (L y) := by
  simp [polar,map_add,map_zero]

theorem matrix_pullback (n m : ℕ) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (P : Matrix (Fin n) (Fin m) (ZMod 2)) (x y : Inputs m) :
    dotProduct x ((P.transpose * M * P).mulVec y) =
      dotProduct (P.mulVec x) (M.mulVec (P.mulVec y)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

def asAdd (m : ℕ) (M : Matrix (Fin m) (Fin m) (ZMod 2)) (y : Inputs m) :
    Inputs m →+ ZMod 2 where
  toFun x := dotProduct x (M.mulVec y)
  map_zero' := by simp
  map_add' _ _ := add_dotProduct _ _ _

theorem transported_leaf (n r c m : ℕ)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (P : Matrix (Fin n) (Fin m) (ZMod 2))
    (independent : P.rank = m) (rank : M.rank = 2 * r) (codimension : n - m ≤ c)
    (Q : Bool → Inputs n → ZMod 2) (origin : Bool → Inputs n)
    (approx : Bool → Inputs m → ZMod 2)
    (shift : ∀ t x y, polar (fun u => Q t (origin t + u)) x y = polar (Q t) x y)
    (common : ∀ x y, polar (approx false) x y = polar (approx true) x y)
    (entries : ∀ x y, polar (fun v => Q false v + Q true v) x y = dotProduct x (M.mulVec y)) :
    let err := fun t u => Q t (origin t + P.mulVec u) + approx t u
    2 ^ (r - c) * (|∑ x, character (err false x)| + |∑ x, character (err true x)|) ≤
      (2 ^ (r - c) + 1) * (Fintype.card (Inputs m) : ℤ) := by
  dsimp only
  let err := fun t u => Q t (origin t + P.mulVec u) + approx t u
  apply one_leaf n r c m M P independent rank codimension (err false) (err true)
    (asAdd m (P.transpose * M * P)) (fun _ _ => rfl)
  intro x y
  change polar (fun u => err false u + err true u) x y =
    dotProduct x ((P.transpose * M * P).mulVec y)
  rw [add_polar]
  unfold err
  rw [add_polar,add_polar]
  have trans (t : Bool) :
      polar (fun u => Q t (origin t + P.mulVec u)) x y =
        polar (Q t) (P.mulVec x) (P.mulVec y) := by
    exact (compose_polar (fun u => Q t (origin t + u)) P.mulVecLin x y).trans
      (shift t _ _)
  rw [trans false,trans true, ← common, matrix_pullback, ← entries, add_polar]
  have cancel : ∀ a b d : ZMod 2, a + d + (b + d) = a + b := by decide
  apply cancel

end Quadratic29947Transport

namespace Quadratic29947Split

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

def split (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (offset : F) :
    V ≃ F × LinearMap.ker L where
  toFun x := (offset + L x, ⟨x - L x • u, by simp [LinearMap.mem_ker,unit]⟩)
  invFun pair := pair.2.val + (pair.1 - offset) • u
  left_inv x := by
    simp only [add_sub_cancel_left,sub_add_cancel]
  right_inv := by
    rintro ⟨s,z⟩
    have off : L z.val = 0 := z.property
    have eval : L (z.val + (s - offset) • u) = s - offset := by
      simp [off,unit]
    apply Prod.ext
    · change offset + L (z.val + (s - offset) • u) = s
      rw [eval,add_sub_cancel]
    · apply Subtype.ext
      change z.val + (s - offset) • u - L (z.val + (s - offset) • u) • u = z.val
      rw [eval,add_sub_cancel_right]

theorem fixed (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (offset desired : F)
    (z : LinearMap.ker L) : offset + L ((split L u unit offset).symm (desired,z)) = desired := by
  exact congrArg Prod.fst ((split L u unit offset).apply_symm_apply (desired,z))

theorem restricted_form (L P : V →ₗ[F] F) (u : V) (unit : L u = 1)
    (before shift desired : F) (z : LinearMap.ker L) :
    before + P ((split L u unit shift).symm (desired,z)) =
      (before + (desired - shift) * P u) + (P.comp (LinearMap.ker L).subtype) z := by
  change before + P (z.val + (desired - shift) • u) =
    (before + (desired - shift) * P u) + P z.val
  rw [map_add,map_smul]
  simp only [smul_eq_mul]
  abel

end Quadratic29947Split

namespace Quadratic29947Coordinates
open Quadratic29947Walsh
abbrev F := ZMod 2

noncomputable def kernelBasis {m : ℕ} (L : Inputs m →ₗ[F] F) :
    Inputs (Module.finrank F (LinearMap.ker L)) ≃ₗ[F] LinearMap.ker L :=
  (Module.finBasis F (LinearMap.ker L)).equivFun.symm

theorem one_dimension {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m) (unit : L u = 1) :
    Module.finrank F (LinearMap.ker L) + 1 = m := by
  have surj : Function.Surjective L := by
    intro a
    exact ⟨a • u, by simp [unit]⟩
  have rank := L.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj,finrank_top,Module.finrank_self] at rank
  simpa [Nat.add_comm] using rank

noncomputable def coordinates {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m)
    (unit : L u = 1) (offset : F) :
    Inputs m ≃ F × Inputs (Module.finrank F (LinearMap.ker L)) :=
  (Quadratic29947Split.split L u unit offset).trans
    (Equiv.prodCongr (Equiv.refl F) (kernelBasis L).symm.toEquiv)

theorem coordinates_inverse {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m)
    (unit : L u = 1) (offset a : F) (z : Inputs (Module.finrank F (LinearMap.ker L))) :
    (coordinates L u unit offset).symm (a,z) = (kernelBasis L z).val + (a - offset) • u := rfl

theorem sum_over_children {m : ℕ} (L : Inputs m →ₗ[F] F) (u : Inputs m)
    (unit : L u = 1) (offset : F) (g : Inputs m → ℤ) :
    (∑ x, g x) = ∑ a : F, ∑ z : Inputs (Module.finrank F (LinearMap.ker L)),
      g ((kernelBasis L z).val + (a - offset) • u) := by
  let equiv := coordinates L u unit offset
  have sum := Fintype.sum_equiv equiv g (fun pair => g (equiv.symm pair))
    (fun x => by rw [equiv.symm_apply_apply])
  rw [Fintype.sum_prod_type] at sum
  simpa only [equiv,coordinates_inverse] using sum

end Quadratic29947Coordinates

namespace Quadratic29947Affine
open PEqualNP.CircuitLowerBounds

abbrev F := ZMod 2

variable {V : Type*} [AddCommGroup V] [Module F V]

def paired (f : Bool → V → F) : Prop :=
  ∃ (offset : Bool → F) (linear : V →ₗ[F] F), ∀ t x, f t x = offset t + linear x

theorem constant (f : Bool → F) : paired (fun t (_ : V) => f t) :=
  ⟨f,0,by simp⟩

theorem plus {f g : Bool → V → F} (hf : paired f) (hg : paired g) :
    paired (fun t x => f t x + g t x) := by
  obtain ⟨bf,Lf,af⟩ := hf
  obtain ⟨bg,Lg,ag⟩ := hg
  refine ⟨fun t => bf t + bg t,Lf+Lg,?_⟩
  intro t x
  change f t x + g t x = bf t + bg t + (Lf + Lg) x
  rw [af,ag,LinearMap.add_apply]
  abel

theorem scale (a : F) {f : Bool → V → F} (hf : paired f) :
    paired (fun t x => a * f t x) := by
  obtain ⟨b,L,h⟩ := hf
  refine ⟨fun t => a * b t,a • L,?_⟩
  intro t x
  change a * f t x = a * b t + (a • L) x
  rw [h,LinearMap.smul_apply,smul_eq_mul,mul_add]

theorem affine_along_split
    (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F) (a : F)
    {f : Bool → V → F} (hf : paired f) :
    paired (fun t z => f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z))) := by
  obtain ⟨start,P,expr⟩ := hf
  refine ⟨fun t => start t + (a - b t) * P u,P.comp (LinearMap.ker L).subtype,?_⟩
  intro t z
  change f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z)) =
    start t + (a - b t) * P u + (P.comp (LinearMap.ker L).subtype) z
  rw [expr]
  exact Quadratic29947Split.restricted_form L P u unit _ _ _ _

theorem fixed_along_split
    (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F) (a : F) :
    ∀ t z, b t + L ((Quadratic29947Split.split L u unit (b t)).symm (a,z)) = a :=
  fun t z => Quadratic29947Split.fixed L u unit (b t) a z

def both (f g : Bool → V → F) : Prop :=
  paired (fun t x => f t x * g t x) ∧
    paired (fun t x => f t x + g t x + f t x * g t x)

private theorem nonzero_value (L : V →ₗ[F] F) (nonzero : L ≠ 0) : ∃ u, L u = 1 := by
  obtain ⟨u,hu⟩ : ∃ u, L u ≠ 0 := by
    by_contra! h
    apply nonzero
    ext u
    exact h u
  have values : ∀ a : F, a = 0 ∨ a = 1 := by decide
  exact ⟨u,(values (L u)).resolve_left hu⟩

private theorem split_product (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F)
    (f g : Bool → V → F) (form : ∀ t x, f t x = b t + L x)
    (hg : paired g) (a : F) :
    both
      (fun t z => f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z)))
      (fun t z => g t ((Quadratic29947Split.split L u unit (b t)).symm (a,z))) := by
  let onLeaf := fun t z => ((Quadratic29947Split.split L u unit (b t)).symm (a,z))
  have first : (fun t z => f t (onLeaf t z)) = fun (_ : Bool) (_ : LinearMap.ker L) => a := by
    funext t z
    exact (form t _).trans (fixed_along_split L u unit b a t z)
  have second : paired (fun t z => g t (onLeaf t z)) := affine_along_split L u unit b a hg
  change both (fun t z => f t (onLeaf t z)) (fun t z => g t (onLeaf t z))
  rw [first]
  exact ⟨scale a second,plus (plus (constant fun _ => a) second) (scale a second)⟩

private theorem both_comm (f g : Bool → V → F) : both f g ↔ both g f := by
  unfold both
  simp only [mul_comm,add_comm (f _ _) (g _ _)]

theorem binary_step (f g : Bool → V → F) (hf : paired f) (hg : paired g) :
    both f g ∨ ∃ (L : V →ₗ[F] F) (u : V) (unit : L u = 1) (b : Bool → F),
      ∀ a : F, both
        (fun t z => f t ((Quadratic29947Split.split L u unit (b t)).symm (a,z)))
        (fun t z => g t ((Quadratic29947Split.split L u unit (b t)).symm (a,z))) := by
  obtain ⟨bf,Lf,fa⟩ := hf
  obtain ⟨bg,Lg,ga⟩ := hg
  by_cases lf : Lf = 0
  · by_cases lg : Lg = 0
    · left
      have ef : f = fun t (_ : V) => bf t := by
        funext t x
        simp [fa,lf]
      have eg : g = fun t (_ : V) => bg t := by
        funext t x
        simp [ga,lg]
      rw [ef,eg]
      exact ⟨constant fun t => bf t * bg t, constant fun t => bf t + bg t + bf t * bg t⟩
    · obtain ⟨u,hu⟩ := nonzero_value Lg lg
      exact Or.inr ⟨Lg,u,hu,bg,fun a => (both_comm _ _).mp
        (split_product Lg u hu bg g f ga ⟨bf,Lf,fa⟩ a)⟩
  · obtain ⟨u,hu⟩ := nonzero_value Lf lf
    exact Or.inr ⟨Lf,u,hu,bf,split_product Lf u hu bf f g fa ⟨bg,Lg,ga⟩⟩

def scalar (b : Bool) : F := if b then 1 else 0

theorem two_gate_laws :
    (∀ a b, scalar (GateOp.eval .and [a,b]) = scalar a * scalar b) ∧
    (∀ a b, scalar (GateOp.eval .or [a,b]) =
      scalar a + scalar b + scalar a * scalar b) ∧
    (∀ a b, scalar (GateOp.eval (.mod 2) [a,b]) = 1 + scalar a + scalar b) ∧
    (∀ a, scalar (GateOp.eval .not [a]) = 1 + scalar a) ∧
    (∀ a, scalar (GateOp.eval (.mod 2) [a]) = 1 + scalar a) := by decide

end Quadratic29947Affine

namespace Quadratic29947Gate
open PEqualNP.CircuitLowerBounds Quadratic29947Affine

variable {V : Type*} [AddCommGroup V] [Module F V]

def read (stock : List (Bool → V → F)) (i : ℕ) : Bool → V → F :=
  stock.getD i (fun _ _ => 0)

def run (g : Gate) (stock : List (Bool → V → F)) (t : Bool) (x : V) : F :=
  scalar (g.op.eval (g.inputs.map fun i => decide (read stock i t x = 1)))

theorem read_affine (stock : List (Bool → V → F)) (h : ∀ f ∈ stock, paired f) (i : ℕ) :
    paired (read stock i) := by
  unfold read
  by_cases ok : i < stock.length
  · rw [List.getD_eq_getElem _ _ ok]
    exact h _ (List.getElem_mem ok)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact constant fun _ => 0

theorem encode_decide : ∀ a : F, scalar (decide (a = 1)) = a := by decide

theorem eval_binary_and (stock : List (Bool → V → F)) (a b : ℕ) (t : Bool) (x : V) :
    run ⟨.and,[a,b]⟩ stock t x = read stock a t x * read stock b t x := by
  simp only [run,List.map_cons,List.map_nil,two_gate_laws.1,encode_decide]

theorem eval_binary_or (stock : List (Bool → V → F)) (a b : ℕ) (t : Bool) (x : V) :
    run ⟨.or,[a,b]⟩ stock t x =
      read stock a t x + read stock b t x + read stock a t x * read stock b t x := by
  simp only [run,List.map_cons,List.map_nil,two_gate_laws.2.1,encode_decide]

theorem uncharged (g : Gate) (stock : List (Bool → V → F)) (h : ∀ f ∈ stock, paired f)
    (arity : g.inputs.length ≤ 2)
    (basis : g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
    (pay : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    paired (run g stock) := by
  rcases g with ⟨op, args⟩
  change op = .and ∨ op = .or ∨ op = .mod 2 ∨ (op = .not ∧ args.length = 1) at basis
  rcases args with _ | ⟨a,args⟩
  · exact constant fun _ => scalar (op.eval [])
  rcases args with _ | ⟨b, rest⟩
  · rcases basis with hw | hw | hw | ⟨hw,_⟩ <;> subst op
    · have semantic : ∀ b : Bool, scalar (GateOp.eval .and [b]) = scalar b := by decide
      unfold run
      simp only [List.map_cons,List.map_nil,semantic,encode_decide]
      exact read_affine stock h a
    · have semantic : ∀ b : Bool, scalar (GateOp.eval .or [b]) = scalar b := by decide
      unfold run
      simp only [List.map_cons,List.map_nil,semantic,encode_decide]
      exact read_affine stock h a
    · unfold run
      simp only [List.map_cons,List.map_nil,two_gate_laws.2.2.2.2,encode_decide]
      exact plus (constant fun _ => 1) (read_affine stock h a)
    · unfold run
      simp only [List.map_cons,List.map_nil,two_gate_laws.2.2.2.1,encode_decide]
      exact plus (constant fun _ => 1) (read_affine stock h a)
  have noMore : rest = [] := by
    have len : rest.length = 0 := by simpa using arity
    exact List.length_eq_zero_iff.mp len
  subst rest
  rcases basis with hw | hw | hw | ⟨hw, bad⟩ <;> subst op
  · exact False.elim (pay ⟨Or.inl rfl,rfl⟩)
  · exact False.elim (pay ⟨Or.inr rfl,rfl⟩)
  · unfold run
    simp only [List.map_cons,List.map_nil,two_gate_laws.2.2.1,encode_decide]
    exact plus (plus (constant fun _ => 1) (read_affine stock h a)) (read_affine stock h b)
  · cases bad

end Quadratic29947Gate

namespace Quadratic29947Tape
open PEqualNP.CircuitLowerBounds Quadratic29947Affine Quadratic29947Gate

variable {V : Type*}

def wires (tape : List Gate) (stock : List (Bool → V → F)) : List (Bool → V → F) :=
  tape.foldl (fun w g => w ++ [run g w]) stock

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem read_value (stock : List (Bool → V → F)) (w : List Bool)
    (t : Bool) (x : V) (agrees : stock.map (fun f => f t x) = w.map scalar) (i : ℕ) :
    Quadratic29947Gate.read stock i t x = scalar (w.getD i false) := by
  have lengths := congrArg List.length agrees
  simp only [List.length_map] at lengths
  by_cases ok : i < stock.length
  · have ok' : i < w.length := by omega
    have eq := congrArg (fun xs : List F => xs.getD i 0) agrees
    simpa only [Quadratic29947Gate.read,List.getD_eq_getElem _ _ ok,List.getD_eq_getElem _ _ ok',
      List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ok :
        i < (stock.map fun f => f t x).length),
      List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ok' :
        i < (w.map scalar).length),List.getElem_map] using eq
  · have out : stock.length ≤ i := by omega
    have out' : w.length ≤ i := by omega
    rw [Quadratic29947Gate.read,List.getD_eq_default _ _ out,List.getD_eq_default _ _ out']
    rfl

theorem exact_wire (tape : List Gate) (stock : List (Bool → V → F))
    (w : List Bool) (t : Bool) (x : V)
    (agrees : stock.map (fun f => f t x) = w.map scalar) :
    (wires tape stock).map (fun f => f t x) = (tape.foldl boolStep w).map scalar := by
  induction tape generalizing stock w with
  | nil => exact agrees
  | cons g tape ih =>
    apply ih
    have inv : ∀ b : Bool, decide (scalar b = 1) = b := by decide
    have value : run g stock t x = scalar (g.op.eval (g.inputs.map fun i => w.getD i false)) := by
      simp only [run,read_value stock w t x agrees,inv]
    simp only [boolStep,List.map_append,List.map_cons,List.map_nil,agrees,value]

theorem circuit_wires (C : Circuit) (stock : List (Bool → V → F)) (w : List Bool)
    (t : Bool) (x : V) (agrees : stock.map (fun f => f t x) = w.map scalar) :
    (wires C.gates stock).map (fun f => f t x) = (C.wires w).map scalar :=
  exact_wire C.gates stock w t x agrees

end Quadratic29947Tape

namespace Quadratic29947Chart
open Quadratic29947Walsh Quadratic29947Coordinates

structure Chart (n : ℕ) where
  dim : ℕ
  origin : Bool → Inputs n
  move : Inputs dim →ₗ[ZMod 2] Inputs n
  independent : Function.Injective move

def point {n : ℕ} (C : Chart n) (t : Bool) (x : Inputs C.dim) : Inputs n :=
  C.origin t + C.move x

def initial (n : ℕ) : Chart n :=
  ⟨n,fun _ => 0,LinearMap.id,fun _ _ h => h⟩

theorem initial_point (n : ℕ) (t : Bool) (x : Inputs n) : point (initial n) t x = x := by
  change 0 + x = x
  exact zero_add _

noncomputable def matrix {n : ℕ} (C : Chart n) : Matrix (Fin n) (Fin C.dim) (ZMod 2) :=
  LinearMap.toMatrix' C.move

theorem matrix_point {n : ℕ} (C : Chart n) (x : Inputs C.dim) :
    (matrix C).mulVec x = C.move x :=
  LinearMap.toMatrix'_mulVec _ _

theorem matrix_rank {n : ℕ} (C : Chart n) : (matrix C).rank = C.dim := by
  have same : (matrix C).mulVecLin = C.move :=
    LinearMap.ext fun x => matrix_point C x
  rw [Matrix.rank,same,LinearMap.finrank_range_of_inj C.independent]
  simp

noncomputable def child {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (b : Bool → ZMod 2) (a : ZMod 2) : Chart n where
  dim := Module.finrank (ZMod 2) (LinearMap.ker L)
  origin t := C.origin t + C.move ((a - b t) • u)
  move := C.move.comp ((LinearMap.ker L).subtype.comp (kernelBasis L).toLinearMap)
  independent := C.independent.comp (Subtype.val_injective.comp (kernelBasis L).injective)

theorem child_point {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (a : ZMod 2) (t : Bool)
    (z : Inputs (child C L u b a).dim) :
    point (child C L u b a) t z = point C t ((coordinates L u unit (b t)).symm (a,z)) := by
  change (C.origin t + C.move ((a - b t) • u)) + C.move (kernelBasis L z).val =
    C.origin t + C.move ((kernelBasis L z).val + (a - b t) • u)
  rw [map_add]
  abel

theorem child_dimension {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (a : ZMod 2) :
    (child C L u b a).dim + 1 = C.dim :=
  one_dimension L u unit

theorem child_sum {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (t : Bool) (f : Inputs n → ℤ) :
    (∑ x, f (point C t x)) =
      ∑ a : ZMod 2, ∑ z, f (point (child C L u b a) t z) := by
  refine (sum_over_children L u unit (b t) (fun x => f (point C t x))).trans ?_
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro z _
  exact congrArg f (child_point C L u unit b a t z).symm

theorem child_affine {n : ℕ} (C : Chart n) (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2)
    (u : Inputs C.dim) (unit : L u = 1) (b : Bool → ZMod 2) (a : ZMod 2) (f : Bool → Inputs n → ZMod 2)
    (form : Quadratic29947Affine.paired (fun t x => f t (point C t x))) :
    Quadratic29947Affine.paired (fun t z => f t (point (child C L u b a) t z)) := by
  have same := Quadratic29947Affine.affine_along_split L u unit b a form
  obtain ⟨q,Z,eq⟩ := same
  refine ⟨q,Z.comp (kernelBasis L).toLinearMap,?_⟩
  intro t z
  change f t (point (child C L u b a) t z) = q t + Z (kernelBasis L z)
  rw [child_point C L u unit b a t z]
  exact eq t (kernelBasis L z)

end Quadratic29947Chart

namespace Quadratic29947Refine
open PEqualNP.CircuitLowerBounds Quadratic29947Walsh Quadratic29947Coordinates
open Quadratic29947Chart Quadratic29947Affine Quadratic29947Gate

def pull {n : ℕ} (C : Chart n) (f : Bool → Inputs n → ZMod 2) :
    Bool → Inputs C.dim → ZMod 2 :=
  fun t x => f t (point C t x)

theorem pull_read {n : ℕ} (C : Chart n) (stock : List (Bool → Inputs n → ZMod 2)) (i : ℕ) :
    read (stock.map (pull C)) i = pull C (read stock i) := by
  unfold Quadratic29947Gate.read
  by_cases ok : i < stock.length
  · have ok' : i < (stock.map (pull C)).length := by simpa only [List.length_map] using ok
    rw [List.getD_eq_getElem _ _ ok',List.getElem_map,List.getD_eq_getElem _ _ ok]
  · have outside : stock.length ≤ i := by omega
    have outside' : (stock.map (pull C)).length ≤ i := by
      simpa only [List.length_map] using outside
    rw [List.getD_eq_default _ _ outside',List.getD_eq_default _ _ outside]
    rfl

theorem pull_gate {n : ℕ} (C : Chart n) (stock : List (Bool → Inputs n → ZMod 2)) (g : Gate) :
    run g (stock.map (pull C)) = pull C (run g stock) := by
  funext t x
  simp only [run,pull_read,pull]

theorem free_preserves {n : ℕ} (C : Chart n) (stock : List (Bool → Inputs n → ZMod 2)) (g : Gate)
    (stockAffine : ∀ f ∈ stock, paired (pull C f))
    (arity : g.inputs.length ≤ 2)
    (basis : g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))
    (pay : ¬ ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)) :
    paired (pull C (run g stock)) := by
  rw [← pull_gate]
  refine uncharged g _ ?_ arity basis pay
  intro f hf
  obtain ⟨original,mem,rfl⟩ := List.mem_map.mp hf
  exact stockAffine original mem

theorem binary_refines {n : ℕ} (C : Chart n) (stock : List (Bool → Inputs n → ZMod 2))
    (stockAffine : ∀ f ∈ stock, paired (pull C f)) (u v : ℕ) :
    (paired (pull C (run ⟨.and,[u,v]⟩ stock)) ∧ paired (pull C (run ⟨.or,[u,v]⟩ stock))) ∨
    ∃ (L : Inputs C.dim →ₗ[ZMod 2] ZMod 2) (p : Inputs C.dim) (unit : L p = 1) (b : Bool → ZMod 2),
      ∀ a : ZMod 2, paired (pull (child C L p b a) (run ⟨.and,[u,v]⟩ stock)) ∧
        paired (pull (child C L p b a) (run ⟨.or,[u,v]⟩ stock)) := by
  have all : ∀ f ∈ stock.map (pull C), paired f := by
    intro f hf
    obtain ⟨original,mem,rfl⟩ := List.mem_map.mp hf
    exact stockAffine original mem
  let f := pull C (read stock u)
  let g := pull C (read stock v)
  have hf : paired f := by
    unfold f
    rw [← pull_read]
    exact read_affine _ all u
  have hg : paired g := by
    unfold g
    rw [← pull_read]
    exact read_affine _ all v
  have pAnd : run ⟨.and,[u,v]⟩ stock = fun t x => read stock u t x * read stock v t x :=
    funext fun t => funext (eval_binary_and stock u v t)
  have pOr : run ⟨.or,[u,v]⟩ stock = fun t x => read stock u t x + read stock v t x +
      read stock u t x * read stock v t x :=
    funext fun t => funext (eval_binary_or stock u v t)
  rw [pAnd,pOr]
  rcases binary_step f g hf hg with onChart | ⟨L,p,unit,b,split⟩
  · exact Or.inl onChart
  right
  refine ⟨L,p,unit,b,?_⟩
  intro a
  have base := split a
  change both _ _ at base
  constructor
  · obtain ⟨bias,part,same⟩ := base.1
    refine ⟨bias,part.comp (kernelBasis L).toLinearMap,?_⟩
    intro t z
    simp only [pull,child_point C L p unit b,LinearMap.comp_apply,LinearEquiv.coe_coe]
    exact same t (kernelBasis L z)
  · obtain ⟨bias,part,same⟩ := base.2
    refine ⟨bias,part.comp (kernelBasis L).toLinearMap,?_⟩
    intro t z
    simp only [pull,child_point C L p unit b,LinearMap.comp_apply,LinearEquiv.coe_coe]
    exact same t (kernelBasis L z)

end Quadratic29947Refine

namespace Quadratic29947Partition
open PEqualNP.CircuitLowerBounds Quadratic29947Chart Quadratic29947Walsh
open Quadratic29947Gate Quadratic29947Affine Quadratic29947Refine

abbrev Stock (n : ℕ) := List (Bool → Inputs n → ZMod 2)

def AffineOn {n : ℕ} (C : Chart n) (stock : Stock n) : Prop :=
  ∀ f ∈ stock, paired (pull C f)

def Covers {n : ℕ} (C : Chart n) (leaves : List (Chart n)) : Prop :=
  ∀ (t : Bool) (weight : Inputs n → ℤ),
    (∑ x, weight (point C t x)) =
      (leaves.map fun leaf => ∑ z, weight (point leaf t z)).sum

def allowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def paid (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

noncomputable def price (gs : List Gate) : ℕ :=
  gs.countP (fun g => @decide (paid g) (Classical.propDecidable _))

private theorem append_affine {n : ℕ} (C : Chart n) (stock : Stock n) (h : AffineOn C stock)
    (f : Bool → Inputs n → ZMod 2) (hf : paired (pull C f)) : AffineOn C (stock ++ [f]) := by
  intro u hu
  rcases List.mem_append.mp hu with old | new
  · exact h u old
  · rw [List.mem_singleton] at new
    simpa [new] using hf

private theorem select_op {n : ℕ} (C : Chart n) (stock : Stock n) (g : Gate)
    (h : paid g) (u v : ℕ) (args : g.inputs = [u,v])
    (andOk : paired (pull C (run ⟨.and,[u,v]⟩ stock)))
    (orOk : paired (pull C (run ⟨.or,[u,v]⟩ stock))) :
    paired (pull C (run g stock)) := by
  rcases h.1 with andOp | orOp
  · have same : g = ⟨.and,[u,v]⟩ := by cases g; simp_all
    exact same ▸ andOk
  · have same : g = ⟨.or,[u,v]⟩ := by cases g; simp_all
    exact same ▸ orOk

theorem partition {n : ℕ} (gs : List Gate) (stock : Stock n) (C : Chart n)
    (allowedGs : ∀ g ∈ gs, allowed g) (initial : AffineOn C stock) :
    ∃ leaves : List (Chart n), Covers C leaves ∧
      ∀ D ∈ leaves, C.dim ≤ D.dim + price gs ∧
        AffineOn D (Quadratic29947Tape.wires gs stock) := by
  classical
  induction gs generalizing stock C with
  | nil =>
    refine ⟨[C],?_,?_⟩
    · intro t weight
      simp
    · intro D inD
      rw [List.mem_singleton] at inD
      subst D
      exact ⟨by simp [price], initial⟩
  | cons g tail ih =>
    have nextLegal : ∀ h ∈ tail, allowed h := fun h inTail => allowedGs h (List.mem_cons_of_mem _ inTail)
    have gLegal := allowedGs g (by simp)
    let next := stock ++ [run g stock]
    have nextStep : Quadratic29947Tape.wires (g :: tail) stock = Quadratic29947Tape.wires tail next := rfl
    rw [nextStep]
    by_cases costly : paid g
    · have bothArgs : ∃ u v, g.inputs = [u,v] := List.length_eq_two.mp costly.2
      obtain ⟨u,v,args⟩ := bothArgs
      rcases binary_refines C stock initial u v with simple | ⟨L,p,unit,b,split⟩
      · have affine : AffineOn C next :=
          append_affine C stock initial _ (select_op C stock g costly u v args simple.1 simple.2)
        obtain ⟨leaves,hcover,h⟩ := ih next C nextLegal affine
        refine ⟨leaves,hcover,?_⟩
        intro D inD
        obtain ⟨size,form⟩ := h D inD
        exact ⟨by simp [price,costly] at *; omega,form⟩
      · have childStock (a : ZMod 2) : AffineOn (child C L p b a) stock := by
          intro f hf
          exact child_affine C L p unit b a f (initial f hf)
        have childNext (a : ZMod 2) : AffineOn (child C L p b a) next := by
          exact append_affine _ _ (childStock a) _
            (select_op _ _ g costly u v args (split a).1 (split a).2)
        obtain ⟨left,hleft,hLeft⟩ := ih next (child C L p b 0) nextLegal (childNext 0)
        obtain ⟨right,hright,hRight⟩ := ih next (child C L p b 1) nextLegal (childNext 1)
        refine ⟨left ++ right,?_,?_⟩
        · intro t wt
          rw [child_sum C L p unit b t wt]
          have casesF : (Finset.univ : Finset (ZMod 2)) = {0,1} := by decide
          rw [casesF,Finset.sum_insert (by decide),Finset.sum_singleton,
            hleft t wt,hright t wt,List.map_append,List.sum_append]
        · intro D inD
          rcases List.mem_append.mp inD with inLeft | inRight
          · obtain ⟨size,form⟩ := hLeft D inLeft
            have parent := child_dimension C L p unit b 0
            exact ⟨by simp [price,costly] at *; omega,form⟩
          · obtain ⟨size,form⟩ := hRight D inRight
            have parent := child_dimension C L p unit b 1
            exact ⟨by simp [price,costly] at *; omega,form⟩
    · have affine : AffineOn C next := append_affine C stock initial _
        (free_preserves C stock g initial gLegal.1 gLegal.2 costly)
      obtain ⟨leaves,hcover,h⟩ := ih next C nextLegal affine
      refine ⟨leaves,hcover,?_⟩
      intro D inD
      obtain ⟨size,form⟩ := h D inD
      exact ⟨by simpa [price,costly] using size, form⟩

end Quadratic29947Partition

namespace Quadratic29947Literal
open Quadratic29947Polar Quadratic29947Walsh

def quad {n : ℕ} (q : Inputs n → ZMod 2) : Prop :=
  ∃ (b : ZMod 2) (a : Inputs n) (M : Fin n → Fin n → ZMod 2), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

def dotLinear {n : ℕ} (a : Inputs n) : Inputs n →ₗ[ZMod 2] ZMod 2 where
  toFun v := dotProduct a v
  map_add' _ _ := dotProduct_add _ _ _
  map_smul' _ _ := dotProduct_smul _ _ _

theorem shift_invariant {n : ℕ} (q : Inputs n → ZMod 2) (h : quad q)
    (a x y : Inputs n) : polar (fun u => q (a + u)) x y = polar q x y := by
  obtain ⟨c,b,M,rep⟩ := h
  let L : Fin n × Fin n → Inputs n →ₗ[ZMod 2] ZMod 2 :=
    fun ij => M ij.1 ij.2 • LinearMap.proj ij.1
  let P : Fin n × Fin n → Inputs n →ₗ[ZMod 2] ZMod 2 := fun ij => LinearMap.proj ij.2
  have decomp : q = fun v => c + dotLinear b v + ∑ i : Fin n × Fin n, L i v * P i v := by
    funext v
    rw [Fintype.sum_prod_type,rep]
    rfl
  rw [decomp]
  have trans := translated_form Finset.univ L P (dotLinear b) c a x y
  have zero := translated_form Finset.univ L P (dotLinear b) c 0 x y
  simpa only [zero_add] using trans.trans zero.symm

theorem equality_character : ∀ a b : ZMod 2,
    (if a = b then (1 : ℤ) else -1) = character (a + b) := by decide

end Quadratic29947Literal

namespace Quadratic29947Approx
open PEqualNP.CircuitLowerBounds Quadratic29947Walsh Quadratic29947Affine Quadratic29947Chart
open Quadratic29947Partition Quadratic29947Refine Quadratic29947Polar

def raw {n : ℕ} (t : Bool) (x : Inputs n) : Inputs (n+1) :=
  Fin.cons (if t then 1 else 0) x

def bits {n : ℕ} (t : Bool) (x : Inputs n) : List Bool :=
  List.ofFn fun i => decide (raw t x i = 1)

def base (n : ℕ) : Stock n := List.ofFn fun i t x => raw t x i

def stock {n : ℕ} (D : Circuit) : Stock n :=
  Quadratic29947Tape.wires D.gates (base n)

def approx {n : ℕ} (D : Circuit) (tap : Fin (n+1) → ℕ) (t : Bool) (x : Inputs n) : ZMod 2 :=
  Quadratic29947Gate.read (stock D) D.output t x +
    dotProduct (raw t x) (fun i => Quadratic29947Gate.read (stock D) (tap i) t x)

theorem raw_affine {n : ℕ} (C : Chart n) (i : Fin (n+1)) :
    paired (pull C (fun t x => raw t x i)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact constant fun t => if t then 1 else 0
  · exact ⟨fun t => C.origin t j,(LinearMap.proj j).comp C.move,fun _ _ => rfl⟩

theorem base_affine {n : ℕ} (C : Chart n) : AffineOn C (base n) := by
  intro f mem
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp mem
  exact raw_affine C i

theorem read_on_chart {n : ℕ} (C : Chart n) (D : Circuit) (h : AffineOn C (stock D)) (i : ℕ) :
    paired (pull C (Quadratic29947Gate.read (stock D) i)) := by
  rw [← pull_read]
  apply Quadratic29947Gate.read_affine
  intro f mem
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp mem
  exact h g hg

theorem field_read {n : ℕ} (D : Circuit) (t : Bool) (x : Inputs n) (i : ℕ) :
    Quadratic29947Gate.read (stock D) i t x = scalar ((D.wires (bits t x)).getD i false) := by
  have eqBase : (base n).map (fun f => f t x) = (bits t x).map scalar := by
    rw [base,bits,List.map_ofFn,List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    exact (Quadratic29947Gate.encode_decide (raw t x j)).symm
  exact Quadratic29947Tape.read_value (stock D) _ t x
    (Quadratic29947Tape.circuit_wires D _ _ t x eqBase) i

theorem exact_approx {n : ℕ} (D : Circuit) (tap : Fin (n+1) → ℕ) (t : Bool) (x : Inputs n) :
    approx D tap t x = scalar (D.eval (bits t x)) +
      dotProduct (raw t x) (fun i => scalar ((D.wires (bits t x)).getD (tap i) false)) := by
  simp only [approx,field_read,Circuit.eval]

theorem same_polar {n : ℕ} (C : Chart n) (D : Circuit) (tap : Fin (n+1) → ℕ)
    (affine : AffineOn C (stock D)) (x y : Inputs C.dim) :
    polar (pull C (approx D tap) false) x y = polar (pull C (approx D tap) true) x y := by
  classical
  choose b L dy using raw_affine C
  choose c P dv using fun i => read_on_chart C D affine (tap i)
  let A := pull C (Quadratic29947Gate.read (stock D) D.output)
  have off : ∀ t, ∃ (b : ZMod 2) (U : Inputs C.dim →ₗ[ZMod 2] ZMod 2),
      ∀ u, A t u = b + U u := by
    obtain ⟨start,U,eq⟩ := read_on_chart C D affine D.output
    exact fun t => ⟨start t,U,eq t⟩
  have terms (t : Bool) : pull C (approx D tap) t =
      fun u => A t u + ∑ i, (b i t + L i u) * (c i t + P i u) := by
    funext u
    change A t u + ∑ i, (pull C (fun t x => raw t x i)) t u *
        (pull C (Quadratic29947Gate.read (stock D) (tap i))) t u =
      A t u + ∑ i, (b i t + L i u) * (c i t + P i u)
    simp only [dy,dv]
  rw [terms false,terms true]
  exact common_polar Finset.univ L P (fun t i => b i t) (fun t i => c i t) A off x y

end Quadratic29947Approx

namespace Quadratic29947Upper
open PEqualNP.CircuitLowerBounds Quadratic29947Walsh Quadratic29947Literal Quadratic29947Polar
open Quadratic29947Restriction Quadratic29947Transport Quadratic29947Partition
open Quadratic29947Chart Quadratic29947Affine Quadratic29947Refine Quadratic29947Approx

private theorem index_sum {A : Type*} (xs : List A) (f : A → ℤ) :
    (∑ i : Fin xs.length, f xs[i]) = (xs.map f).sum := by
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map xs f)

def signedAgreement {n : ℕ} (Q : Bool → Inputs n → ZMod 2)
    (D : Circuit) (tap : Fin (n+1) → ℕ) (t : Bool) : ℤ :=
  ∑ u, character (Q t u + approx D tap t u)

theorem upper (n r c : ℕ) (Q : Bool → Inputs n → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (shape : ∀ t, quad (Q t))
    (rank : M.rank = 2*r)
    (polarEntries : ∀ x y, polar (fun u => Q false u + Q true u) x y = dotProduct x (M.mulVec y))
    (D : Circuit) (tap : Fin (n+1) → ℕ)
    (legal : ∀ g ∈ D.gates, allowed g) (budget : price D.gates ≤ c) :
    2 ^ (r-c) * (|signedAgreement Q D tap false| + |signedAgreement Q D tap true|) ≤
      (2 ^ (r-c) + 1) * 2 ^ n := by
  obtain ⟨leaves,cover,each⟩ := partition D.gates (base n) (initial n) legal (base_affine (initial n))
  let mass (i : Fin leaves.length) : ℤ := Fintype.card (Inputs (leaves[i]).dim)
  let part (t : Bool) (i : Fin leaves.length) : ℤ :=
    ∑ z, character (Q t (point leaves[i] t z) + approx D tap t (point leaves[i] t z))
  have total : ∑ i, mass i = 2 ^ n := by
    calc
      _ = ((leaves.map fun C => (Fintype.card (Inputs C.dim) : ℤ)).sum) := index_sum leaves _
      _ = ∑ x : Inputs n, (1 : ℤ) := by
        have h := cover false (fun _ => (1 : ℤ))
        change (∑ x : Inputs n, (1 : ℤ)) =
          (leaves.map fun C => ∑ z : Inputs C.dim, (1 : ℤ)).sum at h
        have massEq (C : Chart n) :
            (∑ z : Inputs C.dim, (1 : ℤ)) = (Fintype.card (Inputs C.dim) : ℤ) := by simp
        simp only [massEq] at h
        exact h.symm
      _ = _ := by simp [Inputs,Fintype.card_fun,ZMod.card]
  have decompose (t : Bool) : signedAgreement Q D tap t = ∑ i, part t i := by
    unfold signedAgreement
    let f := fun u => character (Q t u + approx D tap t u)
    have source : (∑ x : Inputs n, f x) = ∑ x, f (point (initial n) t x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg f (initial_point n t x).symm
    exact source.trans ((cover t f).trans (index_sum leaves _).symm)
  rw [decompose false,decompose true]
  apply combine_leaves (part false) (part true) mass (r-c) n total
  intro i
  let C := leaves[i]
  obtain ⟨codim,affine⟩ := each C (List.getElem_mem i.isLt)
  have fits : n - C.dim ≤ c := by
    change n ≤ C.dim + price D.gates at codim
    omega
  have localBound := transported_leaf n r c C.dim M (matrix C)
    (matrix_rank C) rank fits Q C.origin (pull C (approx D tap))
    (fun t => shift_invariant (Q t) (shape t) (C.origin t))
    (same_polar C D tap affine) polarEntries
  change 2 ^ (r-c) * (|part false i| + |part true i|) ≤ (2 ^ (r-c) + 1) * mass i
  simpa only [part,mass,pull,point,matrix_point,C] using localBound

theorem exact_upper (n r c : ℕ) (Q : Bool → Inputs n → ZMod 2)
    (M : Matrix (Fin n) (Fin n) (ZMod 2)) (shape : ∀ t, quad (Q t))
    (rank : M.rank = 2*r)
    (polarEntries : ∀ x y, polar (fun u => Q false u + Q true u) x y = dotProduct x (M.mulVec y))
    (D : Circuit) (tap : Fin (n+1) → ℕ)
    (legal : ∀ g ∈ D.gates, allowed g) (budget : price D.gates ≤ c) :
    let agree (t : Bool) := ∑ u : Inputs n,
      if Q t u = (if D.eval (bits t u) then 1 else 0) +
        dotProduct (raw t u) (fun i => if (D.wires (bits t u)).getD (tap i) false then 1 else 0)
      then (1 : ℤ) else -1
    2 ^ (r-c) * ((agree false).natAbs + (agree true).natAbs) ≤ (2 ^ (r-c) + 1) * 2 ^ n := by
  dsimp only
  have result := upper n r c Q M shape rank polarEntries D tap legal budget
  simp only [signedAgreement,exact_approx,scalar, ← equality_character] at result
  apply Int.ofNat_le.mp
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one,
    Int.natCast_natAbs] using result

end Quadratic29947Upper

namespace Quadratic29947NormalForm
open Quadratic29947Polar

theorem twice : ∀ a : F, a + a = 0 := by decide
private theorem field_values : ∀ a : F, a = 0 ∨ a = 1 := by decide

variable {V : Type*} [AddCommGroup V] [Module F V]

def zeroPolarLinear (q : V → F) (zeroPolar : ∀ x y, polar q x y = 0) : V →ₗ[F] F where
  toFun x := q x + q 0
  map_add' x y := by
    have relation := zeroPolar x y
    have all : ∀ a b c d : F, a+b+c+d = 0 → a+d = (b+d)+(c+d) := by decide
    exact all _ _ _ _ relation
  map_smul' a x := by
    rcases field_values a with rfl | rfl
    · simp [twice]
    · simp

theorem affine_of_zero_polar (q : V → F) (zeroPolar : ∀ x y, polar q x y = 0) :
    ∃ (a : F) (L : V →ₗ[F] F), ∀ x, q x = a + L x := by
  refine ⟨q 0,zeroPolarLinear q zeroPolar,fun x => ?_⟩
  change q x = q 0 + (q x + q 0)
  rw [add_comm (q x) (q 0), ← add_assoc, twice, zero_add]

theorem split_quadratic {r : ℕ} (q : V → F) (L P : Fin r → V →ₗ[F] F)
    (decomp : ∀ x y, polar q x y = ∑ i, (L i x * P i y + L i y * P i x)) :
    ∃ (b : F) (A : V →ₗ[F] F), ∀ x, q x = b + A x + ∑ i, L i x * P i x := by
  let products := fun x => ∑ i, L i x * P i x
  have productForm (x y : V) :
      polar products x y = ∑ i, (L i x * P i y + L i y * P i x) := by
    change polar (fun z => ∑ i, L i z * P i z) x y = _
    rw [sum_polar]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [zero_add] using product_polar (L i) (P i) 0 0 x y
  have off (x y : V) : polar (fun v => q v + products v) x y = 0 := by
    rw [add_polar,decomp,productForm,twice]
  obtain ⟨a,A,affine⟩ := affine_of_zero_polar _ off
  refine ⟨a,A,?_⟩
  intro x
  have after : q x + products x = a + A x := affine x
  rw [← after,add_assoc,twice,add_zero]

end Quadratic29947NormalForm

namespace Quadratic29947ExactBias
open Quadratic29947Walsh
abbrev F := ZMod 2

theorem character_sum {I : Type*} (s : Finset I) (f : I → F) :
    character (∑ i ∈ s, f i) = ∏ i ∈ s, character (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [character]
  | insert a rest fresh ih =>
    rw [Finset.sum_insert fresh,Finset.prod_insert fresh,character_add,ih]

theorem one_pair : (∑ q : F × F, character (q.1 * q.2)) = 2 := by decide

theorem pair_atoms (j : ℕ) :
    (∑ z : Fin j → F × F, character (∑ i, (z i).1 * (z i).2)) = 2 ^ j := by
  simp only [character_sum]
  rw [← Fintype.sum_pow (fun q : F × F => character (q.1 * q.2))]
  rw [one_pair]

theorem exact_bias {A : Type*} [Fintype A] (j k : ℕ) (q : A → F)
    (coords : A ≃ (Fin j → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^j * (∑ x, character (q x)) = 2 ^ (2 * j + k) := by
  have decomposition :
      (∑ x, character (q x)) =
        ∑ z : (Fin j → F × F) × (Fin k → F),
          character (∑ i, (z.1 i).1 * (z.1 i).2) :=
    Fintype.sum_equiv coords _ _ (fun x => congrArg character (form x))
  rw [decomposition,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,pair_atoms]
  simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ = (2 : ℤ)^j * 2^j * 2^k := by ring
    _ = (2 : ℤ)^(j + j + k) := by rw [pow_add,pow_add]
    _ = _ := by congr 1 <;> omega

theorem subset_bias {A : Type*} [Fintype A] (r k : ℕ) (S : Finset (Fin r)) (q : A → F)
    (coords : A ≃ (Fin r → F × F) × (Fin k → F))
    (form : ∀ x, q x = ∑ i ∈ S, ((coords x).1 i).1 * ((coords x).1 i).2) :
    (2 : ℤ)^S.card * (∑ x, character (q x)) = 2 ^ (2*r + k) := by
  classical
  let w (i : Fin r) (z : F × F) : ℤ := if i ∈ S then character (z.1 * z.2) else 1
  let a (i : Fin r) : ℤ := if i ∈ S then 2 else 1
  have count : (∏ i, a i) = (2 : ℤ)^S.card := by
    unfold a
    rw [Finset.prod_ite_mem_eq,Finset.prod_const]
  have term (z : Fin r → F × F) : character (∑ i ∈ S, (z i).1 * (z i).2) = ∏ i, w i (z i) := by
    rw [character_sum]
    unfold w
    rw [Finset.prod_ite_mem_eq]
  have product : (∏ i, a i * ∑ z, w i z) = (4 : ℤ)^r := by
    have pointwise (i : Fin r) : a i * (∑ z, w i z) = 4 := by
      by_cases h : i ∈ S
      · simp [a,w,h,one_pair]
      · simp [a,w,h,Fintype.card_prod,ZMod.card]
    simp only [pointwise,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have selected : (2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i)) = 4^r := by
    rw [← count, ← Fintype.prod_sum w, ← Finset.prod_mul_distrib]
    exact product
  have all : (∑ x, character (q x)) =
      ∑ p : (Fin r → F × F) × (Fin k → F), ∏ i, w i (p.1 i) := by
    apply Fintype.sum_equiv coords
    intro x
    rw [form,term]
  rw [all,Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum]
  have free : (Fintype.card (Fin k → F) : ℤ) = 2^k := by
    simp [Fintype.card_fun,ZMod.card]
  rw [free]
  calc
    _ = (2 : ℤ)^k * ((2 : ℤ)^S.card * (∑ z : Fin r → F × F, ∏ i, w i (z i))) := by ring
    _ = (2 : ℤ)^(2*r+k) := by rw [selected,pow_add,pow_mul]; norm_num [mul_comm]

end Quadratic29947ExactBias

namespace Quadratic29947Fiber
open Quadratic29947Walsh
abbrev F := ZMod 2

def bundle {n r : ℕ} (L R : Fin r → Inputs n →ₗ[F] F) : Inputs n →ₗ[F] (Fin r → F × F) where
  toFun x i := (L i x,R i x)
  map_add' x y := by
    funext i
    exact Prod.ext (map_add (L i) x y) (map_add (R i) x y)
  map_smul' a x := by
    funext i
    exact Prod.ext (map_smul (L i) a x) (map_smul (R i) a x)

theorem bundle_surjective {n r : ℕ} (L R : Fin r → Inputs n →ₗ[F] F)
    (independent : Function.Surjective (fun x : Inputs n => (fun i => L i x, fun i => R i x))) :
    Function.Surjective (bundle L R) := by
  intro xs
  obtain ⟨x,h⟩ := independent (fun i => (xs i).1, fun i => (xs i).2)
  refine ⟨x,?_⟩
  funext i
  exact Prod.ext (congrFun (congrArg Prod.fst h) i) (congrFun (congrArg Prod.snd h) i)

noncomputable def split_fibers {n r : ℕ} (G : Inputs n →ₗ[F] (Fin r → F×F))
    (surj : Function.Surjective G) : Inputs n ≃ (Fin r → F×F) × LinearMap.ker G where
  toFun x := (G x,⟨x - (surj (G x)).choose, by
    rw [LinearMap.mem_ker,map_sub,(surj (G x)).choose_spec,sub_self]⟩)
  invFun y := y.2.val + (surj y.1).choose
  left_inv x := sub_add_cancel _ _
  right_inv := by
    rintro ⟨y,z⟩
    have h : G (z.val + (surj y).choose) = y := by
      rw [map_add,(surj y).choose_spec,LinearMap.mem_ker.mp z.property,zero_add]
    apply Prod.ext h
    apply Subtype.ext
    change z.val + (surj y).choose -
      (surj (G (z.val + (surj y).choose))).choose = z.val
    rw [h,add_sub_cancel_right]

theorem coordinate_fibers {n r : ℕ} (L R : Fin r → Inputs n →ₗ[F] F)
    (independent : Function.Surjective (fun x : Inputs n => (fun i => L i x, fun i => R i x))) :
    ∃ (k : ℕ) (E : Inputs n ≃ ((Fin r → F×F) × (Fin k → F))),
      (2 : ℤ) ^ (2*r+k) = 2^n ∧ ∀ x i, (E x).1 i = (L i x,R i x) := by
  let G := bundle L R
  let K := LinearMap.ker G
  let k := Module.finrank F K
  let fibers := split_fibers G (bundle_surjective L R independent)
  let E := fibers.trans ((Equiv.refl _).prodCongr (Module.finBasis F K).equivFun.toEquiv)
  refine ⟨k,E,?_,fun x i => rfl⟩
  have card := Fintype.card_congr E
  have rate : 2^n = (4 : ℕ)^r * 2^k := by
    simpa [Inputs,Fintype.card_prod,Fintype.card_fun,ZMod.card] using card
  rw [pow_add,pow_mul]
  norm_num only
  exact_mod_cast rate.symm

end Quadratic29947Fiber

namespace Quadratic29947WitnessParts
open Quadratic29947Walsh Quadratic29947Literal
abbrev F := ZMod 2

theorem linear_coefficients {n : ℕ} (L : Inputs n →ₗ[F] F) (x : Inputs n) :
    L x = ∑ i : Fin n, L (Pi.single i (1 : F)) * x i := by
  classical
  have expansion : (∑ i : Fin n, x i • Pi.single i (1 : F)) = x := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply,eq_comm]
  conv_lhs => rw [← expansion]
  rw [map_sum]
  simp [mul_comm]

theorem added_products {n r : ℕ} (q : Inputs n → F) (shape : quad q)
    (L R : Fin r → Inputs n →ₗ[F] F) (J : Finset (Fin r)) :
    quad (fun x => q x + ∑ i ∈ J, L i x * R i x) := by
  classical
  obtain ⟨b,a,M,expression⟩ := shape
  let N : Fin n → Fin n → F := fun i j =>
    M i j + ∑ z ∈ J, L z (Pi.single i 1) * R z (Pi.single j 1)
  refine ⟨b,a,N,?_⟩
  intro x
  have term (z : Fin r) :
      L z x * R z x =
        ∑ i : Fin n, ∑ j : Fin n,
          L z (Pi.single i 1) * R z (Pi.single j 1) * x i * x j := by
    rw [linear_coefficients (L z),linear_coefficients (R z),Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have flip :
      (∑ z ∈ J, L z x * R z x) =
        ∑ i : Fin n, ∑ j : Fin n,
          (∑ z ∈ J, L z (Pi.single i 1) * R z (Pi.single j 1)) * x i * x j := by
    simp only [term,Finset.sum_mul]
    rw [Finset.sum_comm (s := J)]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  change q x + (∑ i ∈ J, L i x * R i x) =
    b + dotProduct a x + ∑ i, ∑ j, N i j * x i * x j
  rw [expression,flip]
  simp only [N,add_mul,Finset.sum_add_distrib]
  ring

theorem split_indices (r c j : ℕ) (fit : j ≤ r-c) :
    ∃ P J T : Finset (Fin r), P.card = min r c ∧ J.card = j ∧
      T.card = (r-c)-j ∧ ∀ f : Fin r → F, (∑ i, f i) = (∑ i ∈ P, f i) + (∑ i ∈ J, f i) + ∑ i ∈ T, f i := by
  classical
  have enough : min r c ≤ (Finset.univ : Finset (Fin r)).card := by simp
  obtain ⟨P, inAll, pc⟩ := Finset.exists_subset_card_eq enough
  let S := (Finset.univ : Finset (Fin r)) \ P
  have sc : S.card = r-c := by
    rw [show S.card = r - min r c by simp [S,Finset.card_sdiff,inAll,pc]]
    omega
  obtain ⟨J, inS, jc⟩ := Finset.exists_subset_card_eq (show j ≤ S.card by rwa [sc])
  let T := S \ J
  refine ⟨P,J,T,pc,jc,by simp [T,Finset.card_sdiff,inS,sc,jc],?_⟩
  intro f
  have all := Finset.sum_sdiff (f := f) inAll
  have second := Finset.sum_sdiff (f := f) inS
  change (∑ i ∈ S, f i) + (∑ i ∈ P, f i) = ∑ i, f i at all
  change (∑ i ∈ T, f i) + (∑ i ∈ J, f i) = ∑ i ∈ S, f i at second
  rw [← all,← second]
  ring

end Quadratic29947WitnessParts

namespace Quadratic29947MatrixForm
open Quadratic29947Polar Quadratic29947Walsh Quadratic29947Literal Quadratic29947NormalForm
def fromMatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) F) : LinearMap.BilinForm F (Inputs n) where
  toFun x := dotLinear (M.mulVec x)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    have mv := map_add M.mulVecLin x y
    change M.mulVec (x+y) = M.mulVec x + M.mulVec y at mv
    change dotProduct (M.mulVec (x+y)) z = dotProduct (M.mulVec x) z + dotProduct (M.mulVec y) z
    rw [mv,add_dotProduct]
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    have mv := map_smul M.mulVecLin a x
    change M.mulVec (a • x) = a • M.mulVec x at mv
    change dotProduct (M.mulVec (a • x)) z = a • dotProduct (M.mulVec x) z
    rw [mv,smul_dotProduct]

theorem matrix_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    Module.finrank F (LinearMap.range (fromMatrix M)) = M.rank := by
  classical
  have ker : LinearMap.ker (fromMatrix M) = LinearMap.ker M.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker]
    change fromMatrix M x = 0 ↔ M.mulVec x = 0
    constructor
    · intro h
      funext i
      have a : fromMatrix M x (Pi.single i 1) = 0 := by rw [h]; rfl
      change dotProduct (M.mulVec x) (Pi.single i 1) = 0 at a
      rw [dotProduct_single_one] at a
      exact a
    · intro off
      apply LinearMap.ext
      intro y
      change dotProduct (M.mulVec x) y = 0
      simp [off]
  have first := (fromMatrix M).finrank_range_add_finrank_ker
  have second := M.mulVecLin.finrank_range_add_finrank_ker
  rw [ker] at first
  exact Nat.add_right_cancel (first.trans second.symm)

theorem polar_compatible (n : ℕ) (d : Inputs n → F) (M : Matrix (Fin n) (Fin n) F)
    (entries : ∀ x y, polar d x y = dotProduct x (M.mulVec y)) :
    (∀ x y, polar d x y = fromMatrix M x y) ∧
    (∀ x, fromMatrix M x x = 0) ∧ (∀ x y, fromMatrix M x y = fromMatrix M y x) := by
  have exchanges (x y : Inputs n) : polar d x y = polar d y x := by
    unfold polar
    rw [add_comm x y]
    ring
  have agrees (x y : Inputs n) : polar d x y = fromMatrix M x y :=
    (exchanges x y).trans ((entries y x).trans (dotProduct_comm _ _))
  refine ⟨agrees,?_,?_⟩
  · intro x
    rw [← agrees,polar]
    have xx : x+x = 0 := funext fun i => twice (x i)
    rw [xx]
    have paired : ∀ a b : F, a+b+b+a=0 := by decide
    exact paired (d 0) (d x)
  · intro x y
    exact (agrees x y).symm.trans ((exchanges x y).trans (agrees y x))

end Quadratic29947MatrixForm

namespace Quadratic29947SymplecticStep

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def perpendicular (B : LinearMap.BilinForm K V) (e f : V) : Submodule K V :=
  LinearMap.ker (B e) ⊓ LinearMap.ker (B f)

def remainder (B : LinearMap.BilinForm K V) (e f : V) : V →ₗ[K] V :=
  LinearMap.id - (B f).smulRight e - (B e).smulRight f

theorem reconstructed (B : LinearMap.BilinForm K V) (e f v : V) :
    B f v • e + B e v • f + remainder B e f v = v := by
  change B f v • e + B e v • f + (v - B f v • e - B e v • f) = v
  abel

theorem remainder_perpendicular (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) (v : V) :
    remainder B e f v ∈ perpendicular B e f := by
  change B e (v - B f v • e - B e v • f) = 0 ∧
    B f (v - B f v • e - B e v • f) = 0
  simp [map_sub, map_smul, smul_eq_mul, alt, ef, fe]

theorem split_pair (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) (v w : V) :
    B v w =
      B f v * B e w + B e v * B f w +
        B (remainder B e f v) (remainder B e f w) := by
  have fe : B f e = 1 := (sym _ _).trans ef
  have hv := remainder_perpendicular B e f alt ef fe v
  have hw := remainder_perpendicular B e f alt ef fe w
  change B e (remainder B e f v) = 0 ∧ B f (remainder B e f v) = 0 at hv
  change B e (remainder B e f w) = 0 ∧ B f (remainder B e f w) = 0 at hw
  have he : B (remainder B e f v) e = 0 := (sym _ _).trans hv.1
  have hf : B (remainder B e f v) f = 0 := (sym _ _).trans hv.2
  calc
    B v w = B (B f v • e + B e v • f + remainder B e f v)
             (B f w • e + B e w • f + remainder B e f w) := by
               simp only [reconstructed]
    _ = _ := by
      simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        smul_eq_mul, alt, ef, fe, hw.1, hw.2, he, hf] <;> ring

def coordinates (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) :
    V ≃ₗ[K] (K × K × perpendicular B e f) where
  toFun v := ⟨B f v, B e v, ⟨remainder B e f v, remainder_perpendicular B e f alt ef fe v⟩⟩
  invFun x := x.1 • e + x.2.1 • f + x.2.2.val
  left_inv := reconstructed B e f
  right_inv := by
    rintro ⟨a,b,w⟩
    have hw := w.property
    change B e w.val = 0 ∧ B f w.val = 0 at hw
    have ha : B f (a • e + b • f + w.val) = a := by
      simp [map_add, map_smul, smul_eq_mul, alt, fe, hw.2]
    have hb : B e (a • e + b • f + w.val) = b := by
      simp [map_add, map_smul, smul_eq_mul, alt, ef, hw.1]
    refine Prod.ext ha (Prod.ext hb (Subtype.ext ?_))
    change a • e + b • f + w.val -
      B f (a • e + b • f + w.val) • e - B e (a • e + b • f + w.val) • f = w.val
    rw [ha,hb]
    abel
  map_add' x y := Prod.ext (map_add (B f) x y)
    (Prod.ext (map_add (B e) x y) (Subtype.ext (map_add (remainder B e f) x y)))
  map_smul' c x := Prod.ext (map_smul (B f) c x)
    (Prod.ext (map_smul (B e) c x) (Subtype.ext (map_smul (remainder B e f) c x)))

theorem dimension_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (ef : B e f = 1) (fe : B f e = 1) [Module.Finite K V] :
    Module.finrank K V = 2 + Module.finrank K (perpendicular B e f) := by
  rw [(coordinates B e f alt ef fe).finrank_eq, Module.finrank_prod, Module.finrank_prod]
  simp <;> omega

def radicalEquiv (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1) :
    LinearMap.ker B ≃ₗ[K] LinearMap.ker (B.restrict (perpendicular B e f)) where
  toFun w := by
    have van (z : V) : B w.val z = 0 := by
      exact congrArg (fun f : V →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have mem : w.val ∈ perpendicular B e f := by
      change B e w.val = 0 ∧ B f w.val = 0
      exact ⟨(sym _ _).trans (van e), (sym _ _).trans (van f)⟩
    refine ⟨⟨w.val,mem⟩,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    exact van z.val
  invFun w := by
    have fe := (sym f e).trans ef
    have van (z : perpendicular B e f) : B w.val.val z.val = 0 := by
      exact congrArg (fun f : perpendicular B e f →ₗ[K] K => f z) (LinearMap.mem_ker.mp w.property)
    have h := w.val.property
    change B e w.val.val = 0 ∧ B f w.val.val = 0 at h
    have fixed : remainder B e f w.val.val = w.val.val := by
      change w.val.val - B f w.val.val • e - B e w.val.val • f = w.val.val
      simp [h.1,h.2]
    refine ⟨w.val.val,?_⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro z
    have split := split_pair B e f alt sym ef w.val.val z
    have hz := van ⟨remainder B e f z, remainder_perpendicular B e f alt ef fe z⟩
    simpa [h.1,h.2,fixed] using split.trans (by simpa [h.1,h.2,fixed] using hz)
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_add' _ _ := Subtype.ext (Subtype.ext rfl)
  map_smul' _ _ := Subtype.ext (Subtype.ext rfl)

theorem rank_step (B : LinearMap.BilinForm K V) (e f : V)
    (alt : ∀ v, B v v = 0) (sym : ∀ v w, B v w = B w v) (ef : B e f = 1)
    [Module.Finite K V] :
    Module.finrank K (LinearMap.range B) =
      2 + Module.finrank K (LinearMap.range (B.restrict (perpendicular B e f))) := by
  have ambient := B.finrank_range_add_finrank_ker
  have residual := (B.restrict (perpendicular B e f)).finrank_range_add_finrank_ker
  have ker := (radicalEquiv B e f alt sym ef).finrank_eq
  have dim := dimension_step B e f alt ef ((sym _ _).trans ef)
  omega

end Quadratic29947SymplecticStep

namespace Quadratic29947SymplecticCoordinates
open Quadratic29947SymplecticStep

universe u v
variable {K : Type u} [Field K]

structure Coordinates {V : Type v} [AddCommGroup V] [Module K V]
    (B : LinearMap.BilinForm K V) (r : ℕ) where
  left : Fin r → V →ₗ[K] K
  right : Fin r → V →ₗ[K] K
  product : ∀ x y, B x y =
    ∑ i : Fin r, (left i x * right i y + right i x * left i y)
  independent : Function.Surjective (fun x : V => (fun i => left i x, fun i => right i x))

theorem normalForm (r : ℕ) :
    ∀ {V : Type v} [AddCommGroup V] [Module K V] [Module.Finite K V],
      ∀ B : LinearMap.BilinForm K V,
        (∀ x, B x x = 0) → (∀ x y, B x y = B y x) →
          Module.finrank K (LinearMap.range B) = 2*r → Nonempty (Coordinates B r) := by
  induction r with
  | zero =>
    intro V _ _ _ B _ _ rank
    have zr : Module.finrank K (LinearMap.range B) = 0 := by simpa using rank
    have bottom : LinearMap.range B = ⊥ := Submodule.finrank_eq_zero.mp zr
    have van (x y : V) : B x y = 0 := by
      have mem := LinearMap.mem_range_self B x
      rw [bottom] at mem
      have eq : B x = 0 := by simpa using mem
      exact congrArg (fun f : V →ₗ[K] K => f y) eq
    refine ⟨{left := Fin.elim0, right := Fin.elim0, product := ?_, independent := ?_}⟩
    · intro x y
      simpa using van x y
    · intro z
      refine ⟨0,Prod.ext ?_ ?_⟩
      · funext i
        exact i.elim0
      · funext i
        exact i.elim0
  | succ r ih =>
    intro V _ _ _ B alt sym rank
    have nn : B ≠ 0 := by
      intro h
      have z : Module.finrank K (LinearMap.range B) = 0 :=
        Submodule.finrank_eq_zero.mpr (LinearMap.range_eq_bot.mpr h)
      omega
    obtain ⟨e,f0,notZero⟩ : ∃ e f, B e f ≠ 0 := by
      by_contra! h
      apply nn
      ext x y
      exact h x y
    let f : V := (B e f0)⁻¹ • f0
    have one : B e f = 1 := by
      simp [f, map_smul, smul_eq_mul, notZero]
    have other : B f e = 1 := (sym _ _).trans one
    let W := perpendicular B e f
    let pr : V →ₗ[K] W := (remainder B e f).codRestrict W
      (remainder_perpendicular B e f alt one other)
    have smaller : Module.finrank K (LinearMap.range (B.restrict W)) = 2*r := by
      have step := rank_step B e f alt sym one
      change Module.finrank K (LinearMap.range B) =
        2 + Module.finrank K (LinearMap.range (B.restrict W)) at step
      omega
    obtain ⟨prev⟩ := ih (B.restrict W) (fun x => alt x.val)
      (fun x y => sym x.val y.val) smaller
    refine ⟨⟨Fin.cons (B f) (fun i => (prev.left i).comp pr),
      Fin.cons (B e) (fun i => (prev.right i).comp pr), ?_, ?_⟩⟩
    · intro x y
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, LinearMap.comp_apply]
      have form := split_pair B e f alt sym one x y
      change B x y = B f x * B e y + B e x * B f y + B.restrict W (pr x) (pr y) at form
      exact form.trans (congrArg (fun t => B f x * B e y + B e x * B f y + t) (prev.product (pr x) (pr y)))
    · rintro ⟨a,b⟩
      obtain ⟨w,hw⟩ := prev.independent (Fin.tail a, Fin.tail b)
      let uv := coordinates B e f alt one other
      let x := uv.symm (a 0,b 0,w)
      have h := uv.apply_symm_apply (a 0,b 0,w)
      have hxL : B f x = a 0 := congrArg Prod.fst h
      have hxR : B e x = b 0 := congrArg (fun p : K × K × W => p.2.1) h
      have hpr : pr x = w := congrArg (fun p : K × K × W => p.2.2) h
      refine ⟨x,Prod.ext ?_ ?_⟩
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxL
        · change prev.left j (pr x) = a j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.fst hw) j
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact hxR
        · change prev.right j (pr x) = b j.succ
          rw [hpr]
          exact congrFun (congrArg Prod.snd hw) j

end Quadratic29947SymplecticCoordinates

namespace Quadratic29947QuadraticCoordinates
open Quadratic29947SymplecticCoordinates

abbrev F := ZMod 2
variable {V : Type*} [AddCommGroup V] [Module F V]
variable {B : LinearMap.BilinForm F V} {r : ℕ}

def quadraticPart (D : Coordinates B r) (x : V) : F :=
  ∑ i : Fin r, D.left i x * D.right i x

private theorem crossTerm : ∀ a b c d : F,
    (a+c)*(b+d)+a*b+c*d = a*d+b*c := by
  decide +kernel

theorem quadratic_polar (D : Coordinates B r) (x y : V) :
    quadraticPart D (x+y) + quadraticPart D x + quadraticPart D y = B x y := by
  rw [D.product]
  simp only [quadraticPart, ← Finset.sum_add_distrib, map_add]
  exact Finset.sum_congr rfl (fun i _ => crossTerm _ _ _ _)

private theorem scalarBalance : ∀ a b c z p q w d : F,
    c+a+b+z=d → w+p+q=d → c+z+w=(a+z+p)+(b+z+q) := by
  decide +kernel

private theorem cancelConstant : ∀ a b c : F, a=b+(a+b+c)+c := by
  decide +kernel

private theorem self_cancel : ∀ a : F, a+a=0 := by decide +kernel

def affineLinear (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) : V →ₗ[F] F where
  toFun x := q x+q 0+quadraticPart D x
  map_add' x y := scalarBalance _ _ _ _ _ _ _ _ (polar x y) (quadratic_polar D x y)
  map_smul' c x := by
    have bits : ∀ c : F, c = 0 ∨ c = 1 := by decide +kernel
    rcases bits c with rfl | rfl
    · change q ((0 : F) • x) + q 0 + quadraticPart D ((0 : F) • x) =
        (0 : F) * (q x + q 0 + quadraticPart D x)
      simp [zero_smul, quadraticPart, self_cancel]
    · change q ((1 : F) • x) + q 0 + quadraticPart D ((1 : F) • x) =
        (1 : F) * (q x + q 0 + quadraticPart D x)
      rw [one_smul, one_mul]

theorem exact_decomposition (D : Coordinates B r) (q : V → F)
    (polar : ∀ u v, q (u+v)+q u+q v+q 0=B u v) (x : V) :
    q x = q 0 + affineLinear D q polar x + quadraticPart D x := by
  exact cancelConstant _ _ _

end Quadratic29947QuadraticCoordinates

namespace Quadratic29947SearchBuild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def allowed (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

noncomputable def charged (g : Gate) : Bool :=
  @decide ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) (Classical.propDecidable _)

structure Build (n : ℕ) where
  gates : List Gate
  legal : ∀ g ∈ gates, allowed g
  back : ∀ j (hj : j < gates.length), ∀ i ∈ gates[j].inputs, i < n + j

def Build.len {n : ℕ} (B : Build n) : ℕ := n + B.gates.length

noncomputable def Build.cost {n : ℕ} (B : Build n) : ℕ := B.gates.countP charged

def Build.wires {n : ℕ} (B : Build n) (x : Fin n → Bool) : List Bool :=
  (⟨B.gates, 0⟩ : Circuit).wires (List.ofFn x)

def Build.val {n : ℕ} (B : Build n) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (B.wires x).getD w false

private theorem fold_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp
    omega

theorem Build.wires_length {n : ℕ} (B : Build n) (x : Fin n → Bool) :
    (B.wires x).length = B.len := by
  simpa [Build.wires,Build.len,Circuit.wires] using fold_length B.gates (List.ofFn x)

def Build.empty (n : ℕ) : Build n :=
  ⟨[], by simp, by simp⟩

def Build.push {n : ℕ} (B : Build n) (g : Gate)
    (good : allowed g) (earlier : ∀ i ∈ g.inputs, i < B.len) : Build n where
  gates := B.gates ++ [g]
  legal := by
    intro g' mem
    rcases List.mem_append.mp mem with h | h
    · exact B.legal g' h
    · simpa only [List.mem_singleton.mp h] using good
  back := by
    intro j hj i hi
    by_cases old : j < B.gates.length
    · rw [List.getElem_append_left old] at hi
      exact B.back j old i hi
    · have now : j = B.gates.length := by simp at hj; omega
      subst j
      rw [List.getElem_append_right (le_refl _)] at hi
      simp only [Nat.sub_self,List.getElem_singleton] at hi
      exact earlier i hi

theorem Build.push_len {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) :
    (B.push g good earlier).len = B.len + 1 := by
  simp [Build.push,Build.len,Nat.add_assoc]

theorem Build.push_cost {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) :
    (B.push g good earlier).cost = B.cost + (if charged g then 1 else 0) := by
  simp [Build.push,Build.cost,List.countP_append,List.countP_cons]

theorem Build.push_wires {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) (x) :
    (B.push g good earlier).wires x = B.wires x ++ [g.op.eval (g.inputs.map (B.val x))] := by
  simp only [Build.push,Build.wires,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rfl

theorem Build.push_old {n : ℕ} (B : Build n) (g : Gate) (good) (earlier)
    (x) (w : ℕ) (old : w < B.len) :
    (B.push g good earlier).val x w = B.val x w := by
  rw [Build.val,Build.push_wires]
  have bound : w < (B.wires x).length := by simpa only [B.wires_length] using old
  simp only [Build.val,List.getD,List.getElem?_append_left bound]

theorem Build.push_new {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) (x) :
    (B.push g good earlier).val x B.len = g.op.eval (g.inputs.map (B.val x)) := by
  rw [Build.val,Build.push_wires]
  generalize h : B.wires x = w
  have len : w.length = B.len := h ▸ B.wires_length x
  rw [← len]
  simp [List.getD]

theorem Build.raw {n : ℕ} (B : Build n) (x : Fin n → Bool) (i : Fin n) :
    B.val x i = x i := by
  have aux (gs : List Gate) (init : List Bool) (j : ℕ) (bound : j < init.length) :
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD j false =
      init.getD j false := by
    induction gs generalizing init with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp; omega)]
      simp only [List.getD,List.getElem?_append_left bound]
  rw [Build.val,Build.wires,Circuit.wires,aux _ _ _ (by simp)]
  simp [List.getD,i.isLt]

theorem Build.readsBack {n : ℕ} (B : Build n) (out : ℕ) :
    ReadsBack n (⟨B.gates,out⟩ : Circuit) := by
  intro j hj i hi
  apply B.back j hj i
  simpa only [gateAt,List.getD_eq_getElem _ _ hj] using hi

inductive Expr (n : ℕ)
  | input (i : Fin n)
  | zero
  | neg (a : Expr n)
  | add (a b : Expr n)
  | mul (a b : Expr n)

def Expr.eval {n : ℕ} (x : Fin n → Bool) : Expr n → Bool
  | .input i => x i
  | .zero => false
  | .neg a => !(a.eval x)
  | .add a b => xor (a.eval x) (b.eval x)
  | .mul a b => (a.eval x) && (b.eval x)

def Expr.cost {n : ℕ} : Expr n → ℕ
  | .input _ | .zero => 0
  | .neg a => a.cost
  | .add a b => a.cost + b.cost
  | .mul a b => a.cost + b.cost + 1

def Extends {n : ℕ} (B C : Build n) : Prop :=
  B.len ≤ C.len ∧ ∀ x w, w < B.len → C.val x w = B.val x w

theorem extends_refl {n : ℕ} (B : Build n) : Extends B B :=
  ⟨le_rfl,fun _ _ _ => rfl⟩

theorem extends_trans {n : ℕ} {A B C : Build n} (ab : Extends A B) (bc : Extends B C) :
    Extends A C :=
  ⟨ab.1.trans bc.1, fun x w h => (bc.2 x w (h.trans_le ab.1)).trans (ab.2 x w h)⟩

theorem Build.push_extends {n : ℕ} (B : Build n) (g : Gate) (good) (earlier) :
    Extends B (B.push g good earlier) :=
  ⟨by rw [B.push_len]; omega, fun x w hw => B.push_old g good earlier x w hw⟩

private theorem or_zero (g : Gate) (l : g.inputs = []) :
    charged g = false := by
  simp [charged,l]

private theorem free_mod (i j : ℕ) : charged ⟨.mod 2,[i,j]⟩ = false := by
  simp [charged]

private theorem free_not (i : ℕ) : charged ⟨.not,[i]⟩ = false := by
  simp [charged]

private theorem paid_and (i j : ℕ) : charged ⟨.and,[i,j]⟩ = true := by
  simp [charged]

theorem compile {n : ℕ} (e : Expr n) (B : Build n) :
    ∃ (C : Build n) (w : ℕ),
      Extends B C ∧ w < C.len ∧ C.cost = B.cost + e.cost ∧
        ∀ x, C.val x w = e.eval x := by
  induction e generalizing B with
  | input i =>
    exact ⟨B,i,extends_refl B,by unfold Build.len; omega,by simp [Expr.cost],fun x => B.raw x i⟩
  | zero =>
    let g : Gate := ⟨.or,[]⟩
    have good : allowed g := by simp [g,allowed]
    have early : ∀ i ∈ g.inputs, i < B.len := by simp [g]
    let C := B.push g good early
    refine ⟨C,B.len,B.push_extends g good early,by simp [C,B.push_len],?_,?_⟩
    · dsimp only [C]; rw [B.push_cost,or_zero g rfl]; simp [Expr.cost]
    · intro x
      dsimp only [C]; rw [B.push_new]; rfl
  | neg a ha =>
    obtain ⟨A,i,ini,hi,price,eval⟩ := ha B
    let g : Gate := ⟨.not,[i]⟩
    have good : allowed g := by simp [g,allowed]
    have early : ∀ j ∈ g.inputs, j < A.len := by simpa [g]
    let C := A.push g good early
    refine ⟨C,A.len,extends_trans ini (A.push_extends g good early),by simp [C,A.push_len],?_,?_⟩
    · dsimp only [C]; rw [A.push_cost]; simp [g,free_not,price,Expr.cost]
    · intro x
      dsimp only [C]; rw [A.push_new]
      simpa [g,GateOp.eval,Expr.eval] using congrArg Bool.not (eval x)
  | add a b ha hb =>
    obtain ⟨A,i,ea,hi,pa,va⟩ := ha B
    obtain ⟨C,j,eb,hj,pb,vb⟩ := hb A
    have hci := hi.trans_le eb.1
    let modGate : Gate := ⟨.mod 2,[i,j]⟩
    have good : allowed modGate := by simp [modGate,allowed]
    have early : ∀ q ∈ modGate.inputs, q < C.len := by
      intro q h
      rcases (show q = i ∨ q = j from by simpa [modGate] using h) with rfl | rfl
      · exact hci
      · exact hj
    let D := C.push modGate good early
    let negGate : Gate := ⟨.not,[C.len]⟩
    have ngood : allowed negGate := by simp [negGate,allowed]
    have nearly : ∀ q ∈ negGate.inputs, q < D.len := by simp [negGate,D,C.push_len]
    refine ⟨D.push negGate ngood nearly,D.len,
      extends_trans (extends_trans ea eb)
        (extends_trans (C.push_extends modGate good early) (D.push_extends negGate ngood nearly)),
      by simp [D.push_len],?_,?_⟩
    · rw [D.push_cost,C.push_cost]
      simp [negGate,modGate,free_not,free_mod,pa,pb,Expr.cost,Nat.add_assoc]
    · intro x
      rw [D.push_new]
      change (!(D.val x C.len)) = _
      dsimp only [D]; rw [C.push_new]
      simp only [modGate,List.map_cons,List.map_nil,Expr.eval,eb.2 x i hi,va x,vb x]
      cases a.eval x <;> cases b.eval x <;> decide
  | mul a b ha hb =>
    obtain ⟨A,i,ea,hi,pa,va⟩ := ha B
    obtain ⟨C,j,eb,hj,pb,vb⟩ := hb A
    have hci := hi.trans_le eb.1
    let g : Gate := ⟨.and,[i,j]⟩
    have good : allowed g := by simp [g,allowed]
    have early : ∀ q ∈ g.inputs, q < C.len := by
      intro q h
      rcases (show q = i ∨ q = j from by simpa [g] using h) with rfl | rfl
      · exact hci
      · exact hj
    refine ⟨C.push g good early,C.len,extends_trans (extends_trans ea eb)
      (C.push_extends g good early),by simp [C.push_len],?_,?_⟩
    · rw [C.push_cost]
      simp [g,paid_and,pa,pb,Expr.cost,Nat.add_assoc]
    · intro x
      rw [C.push_new]
      simp [g,GateOp.eval,Expr.eval,eb.2 x i hi,va x,vb x]

end Quadratic29947SearchBuild

namespace Quadratic29947SearchBuild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev F := ZMod 2

def scalar (b : Bool) : F := if b then 1 else 0

@[simp] theorem scalar_encode (v : F) : scalar (decide (v = 1)) = v := by decide +revert

@[simp] theorem scalar_add (a b : Bool) :
    scalar (xor a b) = scalar a + scalar b := by
  cases a <;> cases b <;> decide

@[simp] theorem scalar_mul (a b : Bool) :
    scalar (a && b) = scalar a * scalar b := by
  cases a <;> cases b <;> decide

@[simp] theorem scalar_neg (b : Bool) : scalar (!b) = 1 + scalar b := by
  cases b <;> decide

def Expr.fieldEval {n : ℕ} (e : Expr n) (x : Fin n → F) : F :=
  scalar (e.eval fun i => decide (x i = 1))

@[simp] theorem Expr.field_input {n : ℕ} (i : Fin n) (x : Fin n → F) :
    (Expr.input i).fieldEval x = x i := by simp [Expr.fieldEval,Expr.eval]

@[simp] theorem Expr.field_zero {n : ℕ} (x : Fin n → F) :
    (Expr.zero : Expr n).fieldEval x = 0 := rfl

@[simp] theorem Expr.field_add {n : ℕ} (a b : Expr n) (x : Fin n → F) :
    (a.add b).fieldEval x = a.fieldEval x + b.fieldEval x := by simp [Expr.fieldEval,Expr.eval]

@[simp] theorem Expr.field_mul {n : ℕ} (a b : Expr n) (x : Fin n → F) :
    (a.mul b).fieldEval x = a.fieldEval x * b.fieldEval x := by simp [Expr.fieldEval,Expr.eval]

@[simp] theorem Expr.field_neg {n : ℕ} (a : Expr n) (x : Fin n → F) :
    a.neg.fieldEval x = 1 + a.fieldEval x := by simp [Expr.fieldEval,Expr.eval]

def Expr.const {n : ℕ} (v : F) : Expr n :=
  if v = 1 then .neg .zero else .zero

@[simp] theorem Expr.const_cost {n : ℕ} (v : F) : (Expr.const v : Expr n).cost = 0 := by
  unfold Expr.const
  split <;> rfl

@[simp] theorem Expr.const_field {n : ℕ} (v : F) (x : Fin n → F) :
    (Expr.const v).fieldEval x = v := by
  unfold Expr.const
  split
  · simp_all
  · have eq : ∀ w : F, w ≠ 1 → w = 0 := by decide
    rw [Expr.field_zero,eq v ‹_›]

def Expr.sumFin {n : ℕ} : {m : ℕ} → (Fin m → Expr n) → Expr n
  | 0, _ => .zero
  | m+1, es => .add (es 0) (sumFin (fun i : Fin m => es i.succ))

@[simp] theorem Expr.sumFin_cost {n m : ℕ} (es : Fin m → Expr n) :
    (Expr.sumFin es).cost = ∑ i, (es i).cost := by
  induction m with
  | zero => simp [Expr.sumFin,Expr.cost]
  | succ m ih => rw [Expr.sumFin,Expr.cost,Fin.sum_univ_succ,ih]

@[simp] theorem Expr.sumFin_field {n m : ℕ} (es : Fin m → Expr n) (x : Fin n → F) :
    (Expr.sumFin es).fieldEval x = ∑ i, (es i).fieldEval x := by
  induction m with
  | zero => simp [Expr.sumFin]
  | succ m ih => rw [Expr.sumFin,Expr.field_add,Fin.sum_univ_succ,ih]

def Expr.linear {n m : ℕ} (wire : Fin m → Fin n) (a : Fin m → F) : Expr n :=
  Expr.sumFin fun i => if a i = 1 then .input (wire i) else .zero

@[simp] theorem Expr.linear_cost {n m : ℕ} (wire : Fin m → Fin n) (a : Fin m → F) :
    (Expr.linear wire a).cost = 0 := by
  rw [Expr.linear,Expr.sumFin_cost]
  apply Finset.sum_eq_zero
  intro i _
  split <;> rfl

@[simp] theorem Expr.linear_field {n m : ℕ} (wire : Fin m → Fin n) (a : Fin m → F)
    (x : Fin n → F) : (Expr.linear wire a).fieldEval x = ∑ i, a i * x (wire i) := by
  rw [Expr.linear,Expr.sumFin_field]
  apply Finset.sum_congr rfl
  intro i _
  split
  · simp_all
  · have eq : ∀ w : F, w ≠ 1 → w = 0 := by decide
    simp [eq (a i) ‹_›]

theorem compile_many {n m : ℕ} (es : Fin m → Expr n) (B : Build n) :
    ∃ (C : Build n) (w : Fin m → ℕ),
      Extends B C ∧ (∀ i, w i < C.len) ∧ C.cost = B.cost + (∑ i, (es i).cost) ∧
        ∀ i x, C.val x (w i) = (es i).eval x := by
  induction m generalizing B with
  | zero =>
    exact ⟨B,Fin.elim0,extends_refl B,(fun i => Fin.elim0 i),by simp,fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨A,u,eb,hu,pa,va⟩ := compile (es 0) B
    obtain ⟨C,v,ec,hv,pc,vc⟩ := ih (fun i => es i.succ) A
    refine ⟨C,Fin.cons u v,extends_trans eb ec,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hu.trans_le ec.1
      · simpa using hv j
    · rw [pc,pa,Fin.sum_univ_succ]
      omega
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro x
        simpa only [Fin.cons_zero,ec.2 x u hu] using va x
      · simpa only [Fin.cons_succ] using vc j

theorem exists_circuit {n m : ℕ} (out : Expr n) (taps : Fin m → Expr n) :
    ∃ (C : Circuit) (tap : Fin m → ℕ), ReadsBack n C ∧
      (∀ g ∈ C.gates, allowed g) ∧
      C.gates.countP charged = out.cost + ∑ i, (taps i).cost ∧
      C.output < n + C.size ∧ (∀ i, tap i < n + C.size) ∧
      (∀ x : Fin n → F,
        scalar (C.eval (List.ofFn (fun i => decide (x i = 1)))) = out.fieldEval x ∧
        ∀ i, scalar ((C.wires (List.ofFn (fun j => decide (x j = 1)))).getD (tap i) false) =
          (taps i).fieldEval x) := by
  obtain ⟨B,w,_,hw,price,hout⟩ := compile out (Build.empty n)
  obtain ⟨E,t,eb,ht,pt,vt⟩ := compile_many taps B
  refine ⟨⟨E.gates,w⟩,t,E.readsBack w,E.legal,?_,?_,?_,?_⟩
  · change E.cost = _
    rw [pt,price]
    simp [Build.cost,Build.empty]
  · simpa [Build.len,Circuit.size] using hw.trans_le eb.1
  · simpa [Build.len,Circuit.size] using ht
  · intro x
    constructor
    · change scalar (E.val (fun i => decide (x i = 1)) w) = _
      rw [eb.2 _ w hw,hout]
      rfl
    · intro i
      change scalar (E.val (fun j => decide (x j = 1)) (t i)) = _
      rw [vt]
      rfl

end Quadratic29947SearchBuild

namespace Quadratic29947SearchBuild
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def raw {n : ℕ} (t : Bool) (x : Fin n → F) : Fin (n+1) → F :=
  Fin.cons (scalar t) x

def linearForm {n : ℕ} (L : (Fin n → F) →ₗ[F] F) : Expr (n+1) :=
  Expr.linear Fin.succ (fun i => L (Pi.single i (1 : F)))

@[simp] theorem linearForm_cost {n : ℕ} (L : (Fin n → F) →ₗ[F] F) :
    (linearForm L).cost = 0 := by simp [linearForm]

@[simp] theorem linearForm_eval {n : ℕ} (L : (Fin n → F) →ₗ[F] F)
    (t : Bool) (x : Fin n → F) :
    (linearForm L).fieldEval (raw t x) = L x := by
  have decompose : (∑ i : Fin n, x i • Pi.single i (1 : F)) = x := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  conv_rhs => rw [← decompose]
  rw [map_sum]
  simp [linearForm,raw,mul_comm]

def switchExpr {n r : ℕ} (d : F) (L : (Fin n → F) →ₗ[F] F)
    (P : Fin r → (Fin n → F) →ₗ[F] F) (Q : Fin r → (Fin n → F) →ₗ[F] F) : Expr (n+1) :=
  ((Expr.const d).add (linearForm L)).add
    (Expr.sumFin fun i => (linearForm (P i)).mul (linearForm (Q i)))

@[simp] theorem switchExpr_cost {n r : ℕ} (d : F) (L : (Fin n → F) →ₗ[F] F)
    (P : Fin r → (Fin n → F) →ₗ[F] F) (Q : Fin r → (Fin n → F) →ₗ[F] F) :
    (switchExpr d L P Q).cost = r := by
  simp [switchExpr,Expr.cost]

@[simp] theorem switchExpr_eval {n r : ℕ} (d : F) (L : (Fin n → F) →ₗ[F] F)
    (P : Fin r → (Fin n → F) →ₗ[F] F) (Q : Fin r → (Fin n → F) →ₗ[F] F)
    (t : Bool) (x : Fin n → F) :
    (switchExpr d L P Q).fieldEval (raw t x) = d + L x + ∑ i, P i x * Q i x := by
  simp [switchExpr]

def quad {n : ℕ} (b : F) (a : Fin n → F) (M : Fin n → Fin n → F) (x : Fin n → F) : F :=
  b + dotProduct a x + ∑ i, ∑ j, M i j * x i * x j

theorem build_switch {n r : ℕ} (b : F) (a : Fin n → F) (M : Fin n → Fin n → F)
    (d : F) (L : (Fin n → F) →ₗ[F] F)
    (P : Fin r → (Fin n → F) →ₗ[F] F) (Q : Fin r → (Fin n → F) →ₗ[F] F) :
    ∃ (D : Circuit) (tap : Fin (n+1) → ℕ), ReadsBack (n+1) D ∧
      (∀ g ∈ D.gates, allowed g) ∧ D.gates.countP charged = r ∧
      D.output < n+1+D.size ∧ (∀ i, tap i < n+1+D.size) ∧
      ∀ (t : Bool) (x : Fin n → F),
        let data := List.ofFn (fun i => decide (raw t x i = 1))
        scalar (D.eval data) +
          dotProduct (raw t x) (fun i => scalar ((D.wires data).getD (tap i) false)) =
        quad b a M x + scalar t * (d + L x + ∑ i, P i x * Q i x) := by
  let out : Expr (n+1) := (Expr.const b).add (Expr.linear Fin.succ a)
  let taps : Fin (n+1) → Expr (n+1) :=
    Fin.cons (switchExpr d L P Q) (fun i => Expr.linear Fin.succ (M i))
  obtain ⟨D,tap,back,legal,cost,hout,htap,ev⟩ := exists_circuit out taps
  refine ⟨D,tap,back,legal,?_,hout,htap,?_⟩
  · rw [cost,Fin.sum_univ_succ]
    simp [out,taps,Expr.cost]
  · intro t x data
    obtain ⟨evOut,evTap⟩ := ev (raw t x)
    change scalar (D.eval data) +
      dotProduct (raw t x) (fun i => scalar ((D.wires data).getD (tap i) false)) = _
    change scalar (D.eval data) = out.fieldEval (raw t x) at evOut
    change ∀ i, scalar ((D.wires data).getD (tap i) false) = (taps i).fieldEval (raw t x) at evTap
    simp only [evOut,out,Expr.field_add,Expr.const_field,Expr.linear_field,evTap,dotProduct]
    rw [Fin.sum_univ_succ]
    simp only [taps,Fin.cons_zero,Fin.cons_succ,switchExpr_eval,Expr.linear_field]
    simp only [raw,Fin.cons_zero,Fin.cons_succ]
    have eq : (∑ i, x i * ∑ j, M i j * x j) = ∑ i, ∑ j, M i j * x i * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [eq]
    unfold quad dotProduct
    ring

end Quadratic29947SearchBuild

namespace Quadratic29947Attain
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Quadratic29947Walsh Quadratic29947Polar Quadratic29947Literal Quadratic29947Fiber
open Quadratic29947WitnessParts Quadratic29947MatrixForm Quadratic29947ExactBias
open Quadratic29947SymplecticCoordinates Quadratic29947QuadraticCoordinates

abbrev Bit := ZMod 2

private theorem first_error : ∀ a b : Bit, a + (a+b) = b := by decide

private theorem last_error : ∀ (a b k l p j t : Bit),
    a+b = k+l+(p+j+t) → b+(a+j+(k+l+p)) = t := by decide

theorem attain (n r c : ℕ) (Q : Bool → Inputs n → Bit) (M : Matrix (Fin n) (Fin n) Bit)
    (shape : ∀ t, Quadratic29947Literal.quad (Q t)) (rank : M.rank = 2*r)
    (entries : ∀ x y, polar (fun u => Q false u + Q true u) x y = dotProduct x (M.mulVec y))
    (j : ℕ) (fit : j ≤ r-c) :
    ∃ (D : Circuit) (tap : Fin (n+1) → ℕ), ReadsBack (n+1) D ∧
      (∀ g ∈ D.gates, Quadratic29947Partition.allowed g) ∧ Quadratic29947Partition.price D.gates ≤ c ∧
      D.output < n+1+D.size ∧ (∀ i, tap i < n+1+D.size) ∧
      (2 : ℤ)^j * Quadratic29947Upper.signedAgreement Q D tap false = 2^n ∧
      (2 : ℤ)^((r-c)-j) * Quadratic29947Upper.signedAgreement Q D tap true = 2^n := by
  classical
  let d := fun x => Q false x + Q true x
  obtain ⟨formula,alternating,symmetric⟩ := polar_compatible n d M entries
  obtain ⟨coords⟩ := normalForm r (fromMatrix M) alternating symmetric ((matrix_rank M).trans rank)
  obtain ⟨k,E,scale,hE⟩ := coordinate_fibers coords.left coords.right coords.independent
  obtain ⟨P,J,T,pCount,jCount,tCount,parts⟩ := split_indices r c j fit
  have subsetSize : Fintype.card (↥P) = min r c := (Fintype.card_coe P).trans pCount
  let ei : Fin (min r c) ≃ ↥P := (Fintype.equivFinOfCardEq subsetSize).symm
  have pick (x : Inputs n) :
      (∑ i : Fin (min r c), coords.left (ei i).val x * coords.right (ei i).val x) =
        ∑ i ∈ P, coords.left i x * coords.right i x := by
    calc
      _ = ∑ i : ↥P, coords.left i.val x * coords.right i.val x :=
        Fintype.sum_equiv ei _ _ (fun _ => rfl)
      _ = _ := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach P (fun i : Fin r => coords.left i x * coords.right i x)
  let base := fun x => Q false x + ∑ i ∈ J, coords.left i x * coords.right i x
  obtain ⟨b,a,N,eBase⟩ := added_products (Q false) (shape false) coords.left coords.right J
  let l := affineLinear coords d formula
  obtain ⟨D,tap,back,allowed,cost,outFit,tapFit,computes⟩ :=
    Quadratic29947SearchBuild.build_switch b a N (d 0) l
      (fun i => coords.left (ei i).val) (fun i => coords.right (ei i).val)
  have paid : Quadratic29947Partition.price D.gates = min r c := cost
  have eval (t : Bool) (x : Inputs n) :
      Quadratic29947Approx.approx D tap t x = base x +
        (if t then 1 else 0) * (d 0 + l x + ∑ i ∈ P, coords.left i x * coords.right i x) := by
    rw [Quadratic29947Approx.exact_approx]
    have use := computes t x
    dsimp only [Quadratic29947SearchBuild.quad] at use
    rw [pick,← eBase x] at use
    exact use
  have errFalse (x : Inputs n) : Q false x + Quadratic29947Approx.approx D tap false x =
      ∑ i ∈ J, coords.left i x * coords.right i x := by
    rw [eval]
    simp only [Bool.false_eq_true,ite_false,zero_mul,add_zero,base]
    exact first_error _ _
  have errTrue (x : Inputs n) : Q true x + Quadratic29947Approx.approx D tap true x =
      ∑ i ∈ T, coords.left i x * coords.right i x := by
    rw [eval]
    simp only [ite_true,one_mul,base]
    apply last_error
    have form := exact_decomposition coords d formula x
    change Q false x + Q true x = d 0 + l x + ∑ i, coords.left i x * coords.right i x at form
    rw [parts] at form
    exact form
  refine ⟨D,tap,back,allowed,paid.trans_le (min_le_right _ _),outFit,tapFit,?_,?_⟩
  · have aligned (x : Inputs n) :
        Q false x + Quadratic29947Approx.approx D tap false x =
          ∑ i ∈ J, ((E x).1 i).1 * ((E x).1 i).2 := by
      simpa only [hE] using errFalse x
    have answer := subset_bias r k J (fun x => Q false x + Quadratic29947Approx.approx D tap false x) E aligned
    rw [jCount,scale] at answer
    exact answer
  · have aligned (x : Inputs n) :
        Q true x + Quadratic29947Approx.approx D tap true x =
          ∑ i ∈ T, ((E x).1 i).1 * ((E x).1 i).2 := by
      simpa only [hE] using errTrue x
    have answer := subset_bias r k T (fun x => Q true x + Quadratic29947Approx.approx D tap true x) E aligned
    rw [tCount,scale] at answer
    exact answer

end Quadratic29947Attain

end PEqualNP.Outside.L_meta_29947

theorem PEqualNP.Outside.L_meta_29947 : (∀ (n r c : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let quad := fun (q : V → F) =>
    ∃ (b : F) (a : V) (M : Fin n → Fin n → F), ∀ v,
      q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  ∀ (Q : Bool → V → F) (M : Matrix (Fin n) (Fin n) F), (∀ t, quad (Q t)) →
    let d := fun u : V => Q false u + Q true u
    M.rank = 2*r → (∀ u v, d (u+v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) →
    let k := n+1
    let legalTap := fun (D : Circ) (tap : Fin k → ℕ) =>
      legal k D ∧ cost D ≤ c ∧ D.output < k+D.size ∧ ∀ i, tap i < k+D.size
    let agree := fun (D : Circ) (tap : Fin k → ℕ) (t : Bool) =>
      ∑ u : V, let y : Fin k → F := Fin.cons (if t then 1 else 0) u
               let data := bits k y
               let v := fun i : Fin k => if (D.wires data).getD (tap i) false then (1 : F) else 0
               if Q t u = (if D.eval data then 1 else 0) + dotProduct y v then (1 : ℤ) else -1
    let e := r-c
    (∀ (D : Circ) (tap : Fin k → ℕ), legalTap D tap →
      2^e * ((agree D tap false).natAbs + (agree D tap true).natAbs) ≤ (2^e+1)*2^n) ∧
    ∀ j ≤ e, ∃ (D : Circ) (tap : Fin k → ℕ), legalTap D tap ∧
      (2 : ℤ)^j * agree D tap false = 2^n ∧
      (2 : ℤ)^(e-j) * agree D tap true = 2^n) := by
  intro n r c
  dsimp only
  intro Q M shape rank polarEntries
  constructor
  · intro D tap legal
    exact PEqualNP.Outside.L_meta_29947.Quadratic29947Upper.exact_upper n r c Q M shape rank polarEntries D tap
      legal.1.2 legal.2.1
  · intro j fit
    obtain ⟨D,tap,back,valid,cost,output,taps,left,right⟩ :=
      PEqualNP.Outside.L_meta_29947.Quadratic29947Attain.attain n r c Q M shape rank polarEntries j fit
    refine ⟨D,tap,⟨⟨back,valid⟩,cost,output,taps⟩,?_,?_⟩
    · simpa [PEqualNP.Outside.L_meta_29947.Quadratic29947Upper.signedAgreement,PEqualNP.Outside.L_meta_29947.Quadratic29947Approx.exact_approx,
        PEqualNP.Outside.L_meta_29947.Quadratic29947Affine.scalar,← PEqualNP.Outside.L_meta_29947.Quadratic29947Literal.equality_character,
        PEqualNP.Outside.L_meta_29947.Quadratic29947Approx.bits,PEqualNP.Outside.L_meta_29947.Quadratic29947Approx.raw] using left
    · simpa only [PEqualNP.Outside.L_meta_29947.Quadratic29947Upper.signedAgreement,PEqualNP.Outside.L_meta_29947.Quadratic29947Approx.exact_approx,
        PEqualNP.Outside.L_meta_29947.Quadratic29947Affine.scalar,← PEqualNP.Outside.L_meta_29947.Quadratic29947Literal.equality_character,
        PEqualNP.Outside.L_meta_29947.Quadratic29947Approx.bits,PEqualNP.Outside.L_meta_29947.Quadratic29947Approx.raw] using right
