import PEqualNP.Defs
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.OfFn

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_907

/-! Hamming distance controls pair counts. Two balls of radius at most two r
whose centers are far apart have a small intersection. A second-moment
bound then relates the density of close pairs at consecutive radii. -/
section Hamming

variable {A : Type} [DecidableEq A] {t : ℕ}

def disagreements (x y : Fin t → A) : Finset (Fin t) :=
  Finset.univ.filter (fun i => x i ≠ y i)

def sharedChanges (x y z : Fin t → A) : Finset (Fin t) :=
  Finset.univ.filter (fun i => x i = y i ∧ x i ≠ z i)

theorem card_disagreements (x y : Fin t → A) :
    (disagreements x y).card = hammingDist x y := rfl

theorem joint_distance (x y z : Fin t → A) :
    (disagreements x y).card + 2 * (sharedChanges x y z).card ≤
      hammingDist x z + hammingDist y z := by
  classical
  simp only [disagreements, sharedChanges, hammingDist, Finset.card_filter]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases a : x i = y i <;> by_cases b : x i = z i <;>
    by_cases c : y i = z i <;> simp_all

theorem small_support_count (t r : ℕ) :
    Fintype.card {s : Finset (Fin t) // s.card ≤ r} ≤ (r + 1) * (1 + t)^r := by
  classical
  let rank : {s : Finset (Fin t) // s.card ≤ r} →
      (Σ k : Fin (r + 1), {s : Finset (Fin t) // s.card = k.val}) :=
    fun s => ⟨⟨s.val.card, Nat.lt_succ_of_le s.property⟩, ⟨s.val, rfl⟩⟩
  have injectiveRank : Function.Injective rank := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z => z.2.val) h
  refine (Fintype.card_le_of_injective rank injectiveRank).trans ?_
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : Fin (r + 1), (1 + t)^r := by
      refine Finset.sum_le_sum fun k _ => ?_
      rw [Fintype.card_finset_len]
      simp only [Fintype.card_fin]
      exact (Nat.choose_le_pow t k.val).trans
        ((Nat.pow_le_pow_left (by omega) _).trans
          (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ k.isLt)))
    _ = (r + 1) * (1 + t)^r := by simp

variable [Fintype A]

theorem common_ball_bound (x y : Fin t → A) (d r : ℕ)
    (hfar : d ≤ hammingDist x y) (hrad : d ≤ 2 * r + 1)
    (hq : 1 ≤ Fintype.card A) :
    Fintype.card {z : Fin t → A // hammingDist x z ≤ d ∧ hammingDist y z ≤ d} ≤
      (r + 1) * (Fintype.card A)^(2 * d + r) * (1 + t)^r := by
  classical
  let D := disagreements x y
  by_cases hnear : D.card ≤ 2 * d
  · let S := {s : Finset (Fin t) // s.card ≤ r}
    let Z := {z : Fin t → A // hammingDist x z ≤ d ∧ hammingDist y z ≤ d}
    let code : Z → (Σ E : S, (↑(D ∪ E.val) → A)) := fun z =>
      ⟨⟨sharedChanges x y z.val, by
        have h := joint_distance x y z.val
        have h1 := z.property.1
        have h2 := z.property.2
        rw [card_disagreements] at h
        omega⟩, fun i => z.val i⟩
    let decode : (Σ E : S, (↑(D ∪ E.val) → A)) → Fin t → A :=
      fun z i => if h : i ∈ D ∪ z.1.val then z.2 ⟨i, h⟩ else x i
    have roundtrip (z : Z) : decode (code z) = z.val := by
      funext i
      change (if h : i ∈ D ∪ sharedChanges x y z.val then z.val i else x i) = z.val i
      split
      · rfl
      · rename_i no
        by_contra different
        apply no
        by_cases same : x i = y i
        · have other : y i ≠ z.val i := fun eq => different (same.trans eq)
          simp [D, disagreements, sharedChanges, same, other]
        · simp [D, disagreements, sharedChanges, same]
    have inj : Function.Injective code := by
      intro p q h
      exact Subtype.ext (by rw [← roundtrip p, ← roundtrip q, h])
    refine (Fintype.card_le_of_injective code inj).trans ?_
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _ : S, (Fintype.card A)^(2 * d + r) := by
        refine Finset.sum_le_sum fun E _ => ?_
        rw [Fintype.card_fun, Fintype.card_coe]
        apply Nat.pow_le_pow_right (by omega)
        have := Finset.card_union_le D E.val
        have := E.property
        omega
      _ = Fintype.card S * (Fintype.card A)^(2 * d + r) := by simp
      _ ≤ ((r + 1) * (1 + t)^r) * (Fintype.card A)^(2 * d + r) :=
        Nat.mul_le_mul_right _ (small_support_count t r)
      _ = _ := by ring
  · have empty : IsEmpty {z : Fin t → A // hammingDist x z ≤ d ∧ hammingDist y z ≤ d} :=
      ⟨fun z => by
        have h := joint_distance x y z.val
        have h1 := z.property.1
        have h2 := z.property.2
        change ¬(disagreements x y).card ≤ 2 * d at hnear
        omega⟩
    simp

section Count

variable {B : Type} [Fintype B]

def nearCount (p : B → Fin t → A) (d : ℕ) (x : B) : ℕ :=
  (Finset.univ.filter fun y => hammingDist (p x) (p y) ≤ d).card

def pairCount (p : B → Fin t → A) (d : ℕ) : ℕ :=
  ∑ x, nearCount p d x

def commonCount (p : B → Fin t → A) (d : ℕ) (x y : B) : ℕ :=
  (Finset.univ.filter fun z => hammingDist (p x) (p z) ≤ d ∧
    hammingDist (p y) (p z) ≤ d).card

omit [Fintype A] in
theorem common_count_sum (p : B → Fin t → A) (d : ℕ) :
    (∑ z, nearCount p d z ^ 2) = ∑ x, ∑ y, commonCount p d x y := by
  classical
  calc
    _ = ∑ z : B, ∑ x : B, ∑ y : B,
        if hammingDist (p x) (p z) ≤ d ∧ hammingDist (p y) (p z) ≤ d then (1 : ℕ) else 0 := by
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [nearCount, Finset.card_filter, pow_two, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hammingDist_comm (p z) (p x), hammingDist_comm (p z) (p y)]
      by_cases hx : hammingDist (p x) (p z) ≤ d <;>
        by_cases hy : hammingDist (p y) (p z) ≤ d <;> simp [hx, hy]
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [commonCount, Finset.card_filter]
      exact Finset.sum_comm

theorem projected_common_ball (p : B → Fin t → A) (hp : Function.Injective p)
    (x y : B) (d r : ℕ) (hd : d ≤ hammingDist (p x) (p y)) (hrad : d ≤ 2 * r + 1)
    (hq : 1 ≤ Fintype.card A) :
    commonCount p d x y ≤ (r + 1) * (Fintype.card A) ^ (5 * r + 2) * (1 + t)^r := by
  classical
  let S := (Finset.univ.filter fun z : B => hammingDist (p x) (p z) ≤ d ∧
    hammingDist (p y) (p z) ≤ d)
  let lift : S → {z : Fin t → A // hammingDist (p x) z ≤ d ∧ hammingDist (p y) z ≤ d} :=
    fun z => ⟨p z.val, (Finset.mem_filter.mp z.property).2⟩
  have hi : Function.Injective lift := by
    intro a b hab
    exact Subtype.ext (hp (congrArg Subtype.val hab))
  have entry := Fintype.card_le_of_injective lift hi
  rw [Fintype.card_coe] at entry
  refine entry.trans ((common_ball_bound (p x) (p y) d r hd hrad hq).trans ?_)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right hq (by omega)))

theorem pair_count_recurrence (p : B → Fin t → A) (hp : Function.Injective p)
    (d r : ℕ) (hrad : d + 1 ≤ 2 * r + 1) (hq : 1 ≤ Fintype.card A) :
    let n := Fintype.card B
    let M := (r + 1) * (Fintype.card A) ^ (5 * r + 2) * (1 + t)^r
    (pairCount p (d + 1)) ^ 2 ≤ n ^ 2 * pairCount p d + n ^ 3 * M := by
  classical
  dsimp only
  let n := Fintype.card B
  let M := (r + 1) * (Fintype.card A) ^ (5 * r + 2) * (1 + t)^r
  have row (x : B) :
      (∑ y, commonCount p (d + 1) x y) ≤ n * nearCount p d x + n * M := by
    calc
      _ ≤ ∑ y : B, ((if hammingDist (p x) (p y) ≤ d then n else 0) + M) := by
        refine Finset.sum_le_sum fun y _ => ?_
        split
        · exact (Finset.card_filter_le _ _).trans (by simp [n])
        · rename_i far
          rw [zero_add]
          exact projected_common_ball p hp x y (d + 1) r (by omega) hrad hq
      _ = n * nearCount p d x + n * M := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [nearCount, Finset.card_filter, Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          split <;> simp_all
        · simp [n]
  calc
    _ ≤ n * ∑ z, nearCount p (d + 1) z ^ 2 := by
      simpa [pairCount, n] using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset B))
          (f := nearCount p (d + 1)))
    _ = n * ∑ x, ∑ y, commonCount p (d + 1) x y := by rw [common_count_sum]
    _ ≤ n * ∑ x, (n * nearCount p d x + n * M) :=
      Nat.mul_le_mul_left _ (Finset.sum_le_sum fun x _ => row x)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [pairCount, n, M]
      ring

omit [Fintype A] in
theorem pair_count_zero (p : B → Fin t → A) (hp : Function.Injective p) :
    pairCount p 0 = Fintype.card B := by
  classical
  have one (x : B) : nearCount p 0 x = 1 := by
    have single : (Finset.univ.filter fun y => hammingDist (p x) (p y) ≤ 0) = {x} := by
      ext y
      simp [hp.eq_iff, eq_comm]
    rw [nearCount, single, Finset.card_singleton]
  simp [pairCount, one]

def density (p : B → Fin t → A) (d : ℕ) : ℚ :=
  (pairCount p d : ℚ) / (Fintype.card B : ℚ) ^ 2

omit [Fintype A] in
theorem density_zero [Nonempty B] (p : B → Fin t → A) (hp : Function.Injective p) :
    density p 0 = 1 / (Fintype.card B : ℚ) := by
  rw [density, pair_count_zero p hp]
  have h : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem density_recurrence [Nonempty B] (p : B → Fin t → A) (hp : Function.Injective p)
    (d r : ℕ) (hrad : d + 1 ≤ 2 * r + 1) (hq : 1 ≤ Fintype.card A) :
    let M := (r + 1) * (Fintype.card A) ^ (5 * r + 2) * (1 + t)^r
    density p (d + 1) ^ 2 ≤ density p d + (M : ℚ) / (Fintype.card B : ℚ) := by
  dsimp only
  let n := (Fintype.card B : ℚ)
  let M := (r + 1) * (Fintype.card A) ^ (5 * r + 2) * (1 + t)^r
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos (α := B))
  have checked := pair_count_recurrence p hp d r hrad hq
  have inequality :
      (pairCount p (d + 1) : ℚ) ^ 2 ≤ n ^ 2 * (pairCount p d : ℚ) + n ^ 3 * M := by
    dsimp [n, M]
    exact_mod_cast checked
  unfold density
  change ((pairCount p (d + 1) : ℚ) / n ^ 2) ^ 2 ≤
    (pairCount p d : ℚ) / n ^ 2 + (M : ℚ) / n
  rw [div_pow]
  refine (div_le_iff₀ (pow_pos (pow_pos hn _) _)).2 ?_
  refine inequality.trans_eq ?_
  field_simp

def recurrenceThreshold : ℕ → ℚ → ℚ
  | 0, δ => δ
  | s + 1, δ => recurrenceThreshold s (δ ^ 2 / 2)

theorem recurrenceThreshold_pos (s : ℕ) {δ : ℚ} (hd : 0 < δ) :
    0 < recurrenceThreshold s δ := by
  induction s generalizing δ with
  | zero => exact hd
  | succ s ih => exact ih (by positivity)

theorem half_square_le {δ : ℚ} (hd : 0 ≤ δ) (h1 : δ ≤ 1) : δ ^ 2 / 2 ≤ δ := by
  have h := mul_le_mul_of_nonneg_left h1 hd
  nlinarith

theorem recurrenceThreshold_le (s : ℕ) {δ : ℚ} (hd : 0 ≤ δ) (h1 : δ ≤ 1) :
    recurrenceThreshold s δ ≤ δ := by
  induction s generalizing δ with
  | zero => exact le_rfl
  | succ s ih =>
    have h := half_square_le hd h1
    exact (ih (by positivity) (h.trans h1)).trans h

theorem recurrence_lower (f : ℕ → ℚ) (u : ℚ) (s : ℕ) {δ : ℚ}
    (hd : 0 < δ) (h1 : δ ≤ 1) (hfinal : δ ≤ f s) (hzero : f 0 ≤ u)
    (hrec : ∀ d < s, f (d + 1) ^ 2 ≤ f d + u) : recurrenceThreshold s δ ≤ u := by
  induction s generalizing δ with
  | zero => exact hfinal.trans hzero
  | succ s ih =>
    change recurrenceThreshold s (δ ^ 2 / 2) ≤ u
    have positive : 0 < δ ^ 2 / 2 := by positivity
    have small := (half_square_le hd.le h1).trans h1
    by_cases h : δ ^ 2 / 2 ≤ u
    · exact (recurrenceThreshold_le s positive.le small).trans h
    · have squared : δ ^ 2 ≤ f (s + 1) ^ 2 := pow_le_pow_left₀ hd.le hfinal 2
      have lastBound := hrec s (Nat.lt_succ_self s)
      have previous : δ ^ 2 / 2 ≤ f s := by linarith
      exact ih positive small previous (fun d hd => hrec d (by omega))

theorem density_card_bound [Nonempty B] (p : B → Fin t → A) (hp : Function.Injective p)
    (r : ℕ) (hq : 1 ≤ Fintype.card A) {δ : ℚ} (hd : 0 < δ) (h1 : δ ≤ 1)
    (close : δ ≤ density p (2 * r + 1)) :
    recurrenceThreshold (2 * r + 1) δ * (Fintype.card B : ℚ) ≤
      (r + 1 : ℚ) * (Fintype.card A : ℚ) ^ (5 * r + 2) * (1 + t : ℚ)^r := by
  let M : ℕ := (r + 1) * (Fintype.card A) ^ (5 * r + 2) * (1 + t)^r
  let n := (Fintype.card B : ℚ)
  have positive : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos (α := B))
  have one : 1 ≤ (M : ℚ) := by
    have posQ : 0 < Fintype.card A := by omega
    have posM : 0 < M := by dsimp [M]; positivity
    exact_mod_cast (show 1 ≤ M by omega)
  have zero : density p 0 ≤ (M : ℚ) / n := by
    rw [density_zero p hp]
    exact div_le_div_of_nonneg_right one positive.le
  have recurrence d (hstep : d < 2 * r + 1) :
      density p (d + 1) ^ 2 ≤ density p d + (M : ℚ) / n := by
    exact density_recurrence p hp d r (by omega) hq
  have result := recurrence_lower (density p) ((M : ℚ) / n) (2 * r + 1)
    hd h1 close zero recurrence
  have finish := (le_div_iff₀ positive).mp result
  simpa [M, n] using finish

end Count

end Hamming

end PEqualNP.Outside.L_lib_907

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_907

def boolSign (b : Bool) : ℚ := if b then -1 else 1

theorem sign_square (b : Bool) : boolSign b ^ 2 = 1 := by cases b <;> norm_num [boolSign]

theorem sign_mul (a b : Bool) : boolSign a * boolSign b = 2 * (if a = b then 1 else 0) - 1 := by
  cases a <;> cases b <;> norm_num [boolSign]

theorem sign_of_power (n : ℕ) : (-1 : ℚ) ^ n = boolSign (n % 2 == 1) := by
  simp only [neg_one_pow_eq_ite, Nat.even_iff]
  by_cases h : n % 2 = 0
  · simp [h, boolSign]
  · have one : n % 2 = 1 := by omega
    simp [one, boolSign]

/-! On a uniform receiver input, parity of coordinate equalities has an exact
correlation kernel. Its value depends only on the Hamming distance. -/
section Correlation

variable {Q : Type} [Fintype Q] [DecidableEq Q] {m : ℕ}

def equalityParity (x y : Fin m → Q) : Bool :=
  ((Finset.univ.filter fun i => x i = y i).card % 2 == 1)

def symbolSign (x y : Q) : ℚ := boolSign (decide (x = y))

omit [Fintype Q] in
theorem sign_product (x y : Fin m → Q) :
    (∏ i, symbolSign (x i) (y i)) = boolSign (equalityParity x y) := by
  calc
    _ = ∏ i ∈ Finset.univ.filter (fun i => x i = y i), (-1 : ℚ) := by
      rw [Finset.prod_filter]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : x i = y i <;> simp [symbolSign, boolSign, h]
    _ = (-1 : ℚ) ^ (Finset.univ.filter (fun i => x i = y i)).card := by simp
    _ = _ := sign_of_power _

theorem symbol_inner (x z : Q) :
    ∑ y : Q, symbolSign x y * symbolSign z y =
      if x = z then (Fintype.card Q : ℚ) else (Fintype.card Q : ℚ) - 4 := by
  classical
  by_cases h : x = z
  · subst z
    simp [symbolSign, ← pow_two, sign_square]
  · rw [ite_eq_right h]
    calc
      _ = ∑ y : Q, ((1 : ℚ) - (if x = y then 2 else 0) - (if z = y then 2 else 0)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases a : x = y <;> by_cases b : z = y <;> simp_all [symbolSign, boolSign] <;> norm_num
      _ = _ := by
        simp [Finset.sum_sub_distrib]
        ring

def falloff (Q : Type) [Fintype Q] : ℚ := 1 - 4 / (Fintype.card Q : ℚ)

theorem parity_inner (x z : Fin m → Q) (hq : 0 < Fintype.card Q) :
    ∑ y : Fin m → Q, boolSign (equalityParity x y) * boolSign (equalityParity z y) =
      (Fintype.card Q : ℚ)^m * (falloff Q)^hammingDist x z := by
  classical
  have denom : (Fintype.card Q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  calc
    _ = ∑ y : Fin m → Q, ∏ i, (symbolSign (x i) (y i) * symbolSign (z i) (y i)) := by
      simp only [Finset.prod_mul_distrib, sign_product]
    _ = ∏ i, ∑ y : Q, symbolSign (x i) y * symbolSign (z i) y :=
      (Fintype.prod_sum (fun (i : Fin m) (y : Q) =>
        symbolSign (x i) y * symbolSign (z i) y)).symm
    _ = ∏ i, ((Fintype.card Q : ℚ) * (if x i = z i then 1 else falloff Q)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [symbol_inner]
      by_cases h : x i = z i
      · simp [h]
      · simp only [h, ite_false, falloff]
        field_simp
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      change (∏ i, if x i = z i then (1 : ℚ) else falloff Q) =
        (falloff Q) ^ (Finset.univ.filter (fun i => x i ≠ z i)).card
      rw [← Finset.prod_const, Finset.prod_filter]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases h : x i = z i <;> simp [h]

abbrev Words (m : ℕ) (Q : Type) := Fin m → Q

def score (S : Finset (Words m Q)) (read : Words m Q → Bool) : ℚ :=
  ∑ y, boolSign (read y) * ∑ x ∈ S, boolSign (equalityParity x y)

def pairWeight (S : Finset (Words m Q)) : ℚ :=
  ∑ x ∈ S, ∑ z ∈ S, (falloff Q)^hammingDist x z

theorem score_le (S : Finset (Words m Q)) (read : Words m Q → Bool) :
    score S read ≤ (S.card : ℚ) * (Fintype.card (Words m Q) : ℚ) := by
  classical
  calc
    _ = ∑ y : Words m Q, ∑ x ∈ S, boolSign (read y) * boolSign (equalityParity x y) := by
      simp [score, Finset.mul_sum]
    _ ≤ ∑ _ : Words m Q, ∑ _ ∈ S, (1 : ℚ) := by
      refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun x _ => ?_
      rw [sign_mul]
      split <;> norm_num
    _ = _ := by simp [mul_comm]

theorem score_square_le (S : Finset (Words m Q)) (read : Words m Q → Bool)
    (hq : 0 < Fintype.card Q) :
    score S read ^ 2 ≤ (Fintype.card (Words m Q) : ℚ)^2 * pairWeight S := by
  classical
  let N := (Fintype.card (Words m Q) : ℚ)
  let column (y : Words m Q) := ∑ x ∈ S, boolSign (equalityParity x y)
  have columns :
      ∑ y, column y ^ 2 = N * pairWeight S := by
    calc
      _ = ∑ y : Words m Q, ∑ x ∈ S, ∑ z ∈ S,
          boolSign (equalityParity x y) * boolSign (equalityParity z y) := by
        simp only [column, pow_two, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_congr rfl fun z _ => mul_comm _ _
      _ = ∑ x ∈ S, ∑ z ∈ S, ∑ y : Words m Q,
          boolSign (equalityParity x y) * boolSign (equalityParity z y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := by
        simp only [parity_inner _ _ hq, pairWeight, Finset.mul_sum]
        simp [N, Words]
  calc
    _ ≤ N * ∑ y, (boolSign (read y) * column y) ^ 2 := by
      simpa [score, N, column] using
        (sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Words m Q)))
          (f := fun y => boolSign (read y) * column y))
    _ = N * (N * pairWeight S) := by
      simp only [mul_pow, sign_square, one_mul, columns]
    _ = _ := by simp [N, pow_two, mul_assoc]

section Fibers

variable {M : Type} [Fintype M] [DecidableEq M]

def messageFiber (send : Words m Q → M) (z : M) : Finset (Words m Q) :=
  Finset.univ.filter (fun x => send x = z)

def correctCount (send : Words m Q → M) (read : M → Words m Q → Bool) : ℕ :=
  ((Finset.univ : Finset (Words m Q × Words m Q)).filter fun xy =>
    read (send xy.1) xy.2 = equalityParity xy.1 xy.2).card

omit [DecidableEq Q] in
theorem sum_fiber_size (send : Words m Q → M) :
    ∑ z, (messageFiber send z).card = Fintype.card (Words m Q) := by
  classical
  simpa [messageFiber] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Words m Q))
      (Finset.univ : Finset M) send

theorem sum_fiber_score_as_pairs (send : Words m Q → M) (read : M → Words m Q → Bool) :
    ∑ z, score (messageFiber send z) (read z) =
      ∑ xy : Words m Q × Words m Q,
        boolSign (read (send xy.1) xy.2) * boolSign (equalityParity xy.1 xy.2) := by
  classical
  calc
    _ = ∑ y : Words m Q, ∑ z, ∑ x ∈ messageFiber send z,
        boolSign (read z y) * boolSign (equalityParity x y) := by
      simp only [score, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ y : Words m Q, ∑ x : Words m Q,
        boolSign (read (send x) y) * boolSign (equalityParity x y) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      calc
        _ = ∑ z, ∑ x ∈ messageFiber send z,
            boolSign (read (send x) y) * boolSign (equalityParity x y) := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun x hx => ?_
          rw [(Finset.mem_filter.mp hx).2]
        _ = _ := by
          simpa [messageFiber] using
            Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset (Words m Q))
              (Finset.univ : Finset M) send
              (fun x => boolSign (read (send x) y) * boolSign (equalityParity x y))
    _ = ∑ xy : Words m Q × Words m Q,
        boolSign (read (send xy.1) xy.2) * boolSign (equalityParity xy.1 xy.2) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm

theorem sum_fiber_score (send : Words m Q → M) (read : M → Words m Q → Bool) :
    ∑ z, score (messageFiber send z) (read z) =
      2 * (correctCount send read : ℚ) - (Fintype.card (Words m Q) : ℚ)^2 := by
  classical
  rw [sum_fiber_score_as_pairs]
  simp_rw [sign_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have count : (correctCount send read : ℚ) = ∑ xy : Words m Q × Words m Q,
      (if read (send xy.1) xy.2 = equalityParity xy.1 xy.2 then 1 else 0) := by
    rw [correctCount, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun xy _ => ?_
    split <;> simp
  rw [← count]
  simp [pow_two]

theorem exists_large_score [Nonempty M] (send : Words m Q → M)
    (read : M → Words m Q → Bool) (β τ ε : ℚ) (ht : 0 ≤ τ) (he : 0 < ε)
    (hmargin : τ + ε < β) (hw : 0 < Fintype.card (Words m Q))
    (hwork : (1 + β) * (Fintype.card (Words m Q) : ℚ)^2 ≤
      2 * (correctCount send read : ℚ)) :
    ∃ z, ε * (Fintype.card (Words m Q) : ℚ) / (Fintype.card M : ℚ) ≤
      ((messageFiber send z).card : ℚ) ∧
      τ * ((messageFiber send z).card : ℚ) * (Fintype.card (Words m Q) : ℚ) <
        score (messageFiber send z) (read z) := by
  classical
  let n := (Fintype.card (Words m Q) : ℚ)
  let l := (Fintype.card M : ℚ)
  let a (z : M) := ((messageFiber send z).card : ℚ)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hw
  have hl : 0 < l := by dsimp [l]; exact_mod_cast (Fintype.card_pos (α := M))
  have mass : ∑ z, a z = n := by
    dsimp [a, n]
    exact_mod_cast sum_fiber_size send
  change ∃ z, ε * n / l ≤ a z ∧ τ * a z * n < score (messageFiber send z) (read z)
  by_contra missing
  push Not at missing
  have extra : 0 ≤ ε * n / l * n := by positivity
  have each (z : M) :
      score (messageFiber send z) (read z) ≤ τ * a z * n + ε * n / l * n := by
    by_cases big : ε * n / l ≤ a z
    · exact (missing z big).trans (by linarith)
    · have small : a z ≤ ε * n / l := le_of_lt (lt_of_not_ge big)
      have positive : 0 ≤ τ * a z * n := by dsimp [a]; positivity
      exact (score_le (messageFiber send z) (read z)).trans
        ((mul_le_mul_of_nonneg_right small hn.le).trans (by linarith))
  have weighted : ∑ z, τ * a z * n = τ * n * n := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, mass]
  have padded : ∑ _ : M, ε * n / l * n = ε * n * n := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change l * (ε * n / l * n) = ε * n * n
    field_simp
  have total : ∑ z, score (messageFiber send z) (read z) ≤ (τ + ε) * n^2 := by
    calc
      _ ≤ ∑ z, (τ * a z * n + ε * n / l * n) := Finset.sum_le_sum fun z _ => each z
      _ = _ := by rw [Finset.sum_add_distrib, weighted, padded]; ring
  have estimate : β * n^2 ≤ ∑ z, score (messageFiber send z) (read z) := by
    rw [sum_fiber_score send read]
    change (1 + β) * n^2 ≤ 2 * (correctCount send read : ℚ) at hwork
    change β * n^2 ≤ 2 * (correctCount send read : ℚ) - n^2
    linarith
  exact (not_lt_of_ge (estimate.trans total))
    (mul_lt_mul_of_pos_right hmargin (pow_pos hn _))

end Fibers

def closePairCount (S : Finset (Words m Q)) (d : ℕ) : ℕ :=
  ∑ x ∈ S, (S.filter fun z => hammingDist x z ≤ d).card

omit [Fintype Q] in
theorem cast_closePairCount (S : Finset (Words m Q)) (d : ℕ) :
    (closePairCount S d : ℚ) =
      ∑ x ∈ S, ∑ z ∈ S, if hammingDist x z ≤ d then (1 : ℚ) else 0 := by
  simp only [closePairCount, Nat.cast_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  split <;> simp

theorem pairWeight_le (S : Finset (Words m Q)) (d : ℕ)
    (h0 : 0 ≤ falloff Q) (h1 : falloff Q ≤ 1) :
    pairWeight S ≤ (closePairCount S d : ℚ) + (falloff Q)^(d + 1) * (S.card : ℚ)^2 := by
  calc
    _ ≤ ∑ x ∈ S, ∑ z ∈ S,
        ((if hammingDist x z ≤ d then (1 : ℚ) else 0) + (falloff Q) ^ (d + 1)) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => ?_
      split
      · exact (pow_le_one₀ h0 h1).trans (le_add_of_nonneg_right (pow_nonneg h0 _))
      · rename_i far
        rw [zero_add]
        exact pow_le_pow_of_le_one h0 h1 (by omega)
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [← cast_closePairCount]
      simp [nsmul_eq_mul]
      ring

theorem high_score_close (S : Finset (Words m Q)) (read : Words m Q → Bool)
    (d : ℕ) (τ : ℚ) (ht : 0 ≤ τ) (hq : 0 < Fintype.card Q)
    (h0 : 0 ≤ falloff Q) (h1 : falloff Q ≤ 1)
    (hw : 0 < Fintype.card (Words m Q))
    (high : τ * (S.card : ℚ) * (Fintype.card (Words m Q) : ℚ) < score S read) :
    (τ^2 - (falloff Q)^(d + 1)) * (S.card : ℚ)^2 ≤ (closePairCount S d : ℚ) := by
  let n := (Fintype.card (Words m Q) : ℚ)
  have hn : 0 < n := by dsimp [n]; exact_mod_cast hw
  have square :
      (τ * (S.card : ℚ) * n)^2 ≤ score S read ^ 2 :=
    pow_le_pow_left₀ (by positivity) high.le 2
  have work : τ^2 * (S.card : ℚ)^2 ≤ pairWeight S := by
    apply le_of_mul_le_mul_left _ (pow_pos hn 2)
    calc
      _ = (τ * (S.card : ℚ) * n)^2 := by ring
      _ ≤ score S read ^ 2 := square
      _ ≤ _ := score_square_le S read hq
  have pairs := pairWeight_le S d h0 h1
  calc
    _ = τ^2 * (S.card : ℚ)^2 - (falloff Q)^(d + 1) * (S.card : ℚ)^2 := by ring
    _ ≤ _ := by linarith

omit [DecidableEq Q] in
theorem close_constants (r : ℕ) (β : ℚ)
    (h0 : 0 ≤ falloff Q) (h1 : falloff Q ≤ 1)
    (hlo : (falloff Q)^(r + 1) < β) (hhi : β ≤ (falloff Q)^r) :
    ∃ τ ε δ : ℚ, 0 ≤ τ ∧ 0 < ε ∧ τ + ε < β ∧ 0 < δ ∧ δ ≤ 1 ∧
      δ = τ^2 - (falloff Q)^(2 * r + 1 + 1) := by
  let p := (falloff Q)^(r + 1)
  let τ := (β + p) / 2
  have pn : 0 ≤ p := by dsimp [p]; positivity
  have t_gt : p < τ := by dsimp [τ]; change p < β at hlo; linarith
  have t_lt : τ < β := by dsimp [τ]; change p < β at hlo; linarith
  have t_nonneg : 0 ≤ τ := pn.trans t_gt.le
  have tle : τ ≤ 1 := t_lt.le.trans (hhi.trans (pow_le_one₀ h0 h1))
  have exponent : (falloff Q)^(2 * r + 1 + 1) = p^2 := by
    dsimp [p]
    rw [← pow_mul]
    congr 1
    omega
  refine ⟨τ, (β - τ) / 2, τ^2 - p^2, t_nonneg, by linarith, by linarith, ?_, ?_, ?_⟩
  · have h := pow_lt_pow_left₀ t_gt pn (by decide : 2 ≠ 0)
    linarith
  · have h := pow_le_one₀ t_nonneg tle (n := 2)
    nlinarith [sq_nonneg p]
  · rw [exponent]

end Correlation

end PEqualNP.Outside.L_lib_907

namespace PEqualNP.Outside.L_lib_907

section Rank

variable {K I J O : Type} [Field K] [Fintype I] [Fintype J] [Fintype O]

theorem pivot_coordinates (U : Submodule K (I → K)) :
    ∃ S : Finset I, S.card ≤ Module.finrank K U ∧
      ∀ v ∈ U, (∀ i ∈ S, v i = 0) → v = 0 := by
  classical
  suffices all : ∀ d (V : Submodule K (I → K)), Module.finrank K V = d →
      ∃ S : Finset I, S.card ≤ d ∧
        ∀ v ∈ V, (∀ i ∈ S, v i = 0) → v = 0 from
    all (Module.finrank K U) U rfl
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro V dimension
    by_cases empty : V = ⊥
    · refine ⟨∅, by simp, ?_⟩
      intro v hv _
      simpa [empty] using hv
    · obtain ⟨v, hv, nonzero⟩ : ∃ v ∈ V, v ≠ 0 := by
        by_contra no
        push Not at no
        apply empty
        refine le_antisymm ?_ bot_le
        intro v hv
        rw [no v hv]
        exact Submodule.zero_mem _
      obtain ⟨i, different⟩ : ∃ i, v i ≠ 0 := by
        by_contra no
        push Not at no
        exact nonzero (funext no)
      let coordinate : (I → K) →ₗ[K] K := LinearMap.proj i
      let cut := V ⊓ coordinate.ker
      have smaller : cut < V := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro equal
        have inCut : v ∈ cut := equal ▸ hv
        exact different (LinearMap.mem_ker.mp (Submodule.mem_inf.mp inCut).2)
      have lowerDimension : Module.finrank K cut < d :=
        dimension ▸ Submodule.finrank_lt_finrank_of_lt smaller
      obtain ⟨S, cardS, pivot⟩ := ih _ lowerDimension cut rfl
      refine ⟨insert i S, (Finset.card_insert_le _ _).trans (by omega), ?_⟩
      intro w hw zero
      have hi : coordinate w = 0 := zero i (Finset.mem_insert_self i S)
      exact pivot w ⟨hw, LinearMap.mem_ker.mpr hi⟩
        (fun j hj => zero j (Finset.mem_insert_of_mem hj))

/-- Quotienting the message range by the nonlinear columns leaves a linear
constraint on raw inputs. Pivot coordinates of its kernel identify the raw
input within each message fiber. -/
theorem message_pivots (L : ((I → K) × (J → K)) →ₗ[K] (O → K)) :
    let rank := Module.finrank K L.range
    rank ≤ Fintype.card O ∧ rank ≤ Fintype.card I + Fintype.card J ∧
    ∃ S : Finset I, S.card + rank ≤ Fintype.card I + Fintype.card J ∧
      ∀ (x y : I → K) (u v : J → K), L (x, u) = L (y, v) →
        (∀ i ∈ S, x i = y i) → x = y := by
  classical
  dsimp only
  let A : (I → K) →ₗ[K] L.range :=
    L.rangeRestrict.comp (LinearMap.inl K (I → K) (J → K))
  let B : (J → K) →ₗ[K] L.range :=
    L.rangeRestrict.comp (LinearMap.inr K (I → K) (J → K))
  let F := B.range.mkQ.comp A
  have proj (x : I → K) (z : J → K) :
      F x = B.range.mkQ (L.rangeRestrict (x, z)) := by
    have sum : A x + B z = L.rangeRestrict (x, z) := by
      change L.rangeRestrict (x, 0) + L.rangeRestrict (0, z) = _
      rw [← map_add]
      simp
    have vanish : B.range.mkQ (B z) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [Submodule.ker_mkQ]
      exact ⟨z, rfl⟩
    rw [← sum, map_add, vanish, add_zero]
    rfl
  have onto : Function.Surjective F := by
    intro q
    obtain ⟨r, hr⟩ := B.range.mkQ_surjective q
    obtain ⟨⟨x, z⟩, h⟩ := L.surjective_rangeRestrict r
    exact ⟨x, (proj x z).trans (h ▸ hr)⟩
  have nullity := F.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr onto, finrank_top] at nullity
  have quotient := B.range.finrank_quotient_add_finrank
  have bsize := B.finrank_range_le
  have csize := (L.range).finrank_le
  simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] at nullity bsize csize
  obtain ⟨S, size, determines⟩ := pivot_coordinates F.ker
  refine ⟨csize, by omega, S, by omega, ?_⟩
  intro x y u v equal agreement
  have same : F x = F y := by
    rw [proj x u, proj y v]
    have e : L.rangeRestrict (x, u) = L.rangeRestrict (y, v) := Subtype.ext equal
    rw [e]
  have difference : x - y ∈ F.ker := by rw [LinearMap.mem_ker, map_sub, same, sub_self]
  exact sub_eq_zero.mp (determines (x - y) difference
    (fun i hi => sub_eq_zero.mpr (agreement i hi)))

end Rank

def toField : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := z == 1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem polynomial_absorb (r h : ℕ) (hr : 0 < r) :
    (h + 1)^r ≤ r^r * 2^h := by
  have small : h / r + 1 ≤ 2^(h / r) := by
    generalize h / r = k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      omega
  have quot := Nat.mod_add_div h r
  have remainder := Nat.mod_lt h hr
  calc
    (h + 1)^r ≤ (r * (h / r + 1))^r := by
      apply Nat.pow_le_pow_left
      rw [Nat.mul_add, Nat.mul_one]
      omega
    _ = r^r * (h / r + 1)^r := by rw [mul_pow]
    _ ≤ r^r * (2^(h / r))^r := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small _)
    _ ≤ r^r * 2^h := by
      rw [← pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.div_mul_le_self h r))

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

section Projection

variable {Q : Type} [DecidableEq Q] {m t : ℕ}

theorem distance_project (f : Fin t → Fin m) (hf : Function.Injective f)
    (x y : Words m Q) : hammingDist (x ∘ f) (y ∘ f) ≤ hammingDist x y := by
  classical
  let s := Finset.univ.filter (fun i : Fin t => x (f i) ≠ y (f i))
  let u := Finset.univ.filter (fun i : Fin m => x i ≠ y i)
  change s.card ≤ u.card
  rw [← Finset.card_image_of_injective s hf]
  refine Finset.card_le_card ?_
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩

theorem projected_pairs (S : Finset (Words m Q)) (f : Fin t → Fin m)
    (hf : Function.Injective f) (d : ℕ) :
    closePairCount S d ≤ pairCount (fun x : S => x.val ∘ f) d := by
  classical
  unfold closePairCount pairCount
  rw [← Finset.sum_coe_sort S]
  refine Finset.sum_le_sum fun x _ => ?_
  let V := S.filter (fun z => hammingDist x.val z ≤ d)
  let p (x : S) := x.val ∘ f
  let U := Finset.univ.filter (fun z : S => hammingDist (p x) (p z) ≤ d)
  let lift : V → U := fun z =>
    ⟨⟨z.val, (Finset.mem_filter.mp z.property).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (distance_project f hf x.val z.val).trans (Finset.mem_filter.mp z.property).2⟩⟩
  have inj : Function.Injective lift := by
    intro a b equal
    exact Subtype.ext (congrArg (fun q => q.val.val) equal)
  change V.card ≤ U.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective lift inj

end Projection

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

open PEqualNP.CircuitLowerBounds

section Linearize

variable {V X : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev WireForm (V : Type) [AddCommGroup V] [Module (ZMod 2) V] (k : ℕ) :=
  (((V × (Fin k → ZMod 2)) →ₗ[ZMod 2] ZMod 2) × ZMod 2)

def formValue {k : ℕ} (w : WireForm V k) (x : V) (h : Fin k → ZMod 2) : ZMod 2 :=
  w.1 (x, h) + w.2

def constForm {k : ℕ} (a : ZMod 2) : WireForm V k := (0, a)

@[simp] theorem value_const {k : ℕ} (a : ZMod 2) (x : V) (h : Fin k → ZMod 2) :
    formValue (constForm a) x h = a := by simp [constForm, formValue]

@[simp] theorem value_zero {k : ℕ} (x : V) (h : Fin k → ZMod 2) :
    formValue (0 : WireForm V k) x h = 0 := by simp [formValue]

@[simp] theorem value_add {k : ℕ} (a b : WireForm V k) (x : V) (h : Fin k → ZMod 2) :
    formValue (a + b) x h = formValue a x h + formValue b x h := by
  simp only [formValue, Prod.fst_add, Prod.snd_add, LinearMap.add_apply]
  ring

def paid (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

noncomputable def paidBool (g : Gate) : Bool := @decide (paid g) (Classical.propDecidable _)

noncomputable def paidCount (gs : List Gate) : ℕ := gs.countP paidBool

def legalOp (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧
    (g.op = .and ∨ g.op = .or ∨ g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1))

def appendWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun n => w.getD n false)]

theorem getD_map' {A B : Type} (f : A → B) (l : List A) (i : ℕ) (v : A) :
    (l.map f).getD i (f v) = f (l.getD i v) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[i]? <;> simp

theorem field_even_single (a : Bool) :
    toField (GateOp.eval (.mod 2) [a]) = 1 + toField a := by cases a <;> decide +kernel

theorem field_even_pair (a b : Bool) :
    toField (GateOp.eval (.mod 2) [a, b]) = 1 + toField a + toField b := by
  cases a <;> cases b <;> decide +kernel

theorem field_negate (a : Bool) : toField (!a) = 1 + toField a := by cases a <;> decide +kernel

@[simp] theorem field_false : toField false = 0 := by decide +kernel

@[simp] theorem field_true : toField true = 1 := by decide +kernel

theorem input_shapes {A : Type} (l : List A) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  rcases l with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨a, rfl⟩)
  · have short : tail.length + 1 + 1 ≤ 2 := by simpa only [List.length_cons] using h
    have empty : tail = [] := List.length_eq_zero_iff.mp (by omega)
    subst tail
    exact Or.inr (Or.inr ⟨a, b, rfl⟩)

def freeForm {k : ℕ} (w : List (WireForm V k)) (g : Gate) : WireForm V k :=
  let args := g.inputs.map (fun i => w.getD i 0)
  match g.op with
  | .and => args.headD (constForm 1)
  | .or => args.headD 0
  | .not => constForm 1 + args.headD 0
  | .mod _ => constForm 1 + args.sum
  | .maj => 0

theorem freeForm_value {k : ℕ} (w : List (WireForm V k)) (bits : List Bool)
    (x : V) (h : Fin k → ZMod 2) (g : Gate) (legal : legalOp g) (free : ¬ paid g)
    (inputs : ∀ i, formValue (w.getD i 0) x h = toField (bits.getD i false)) :
    formValue (freeForm w g) x h = toField (g.op.eval (g.inputs.map fun i => bits.getD i false)) := by
  rcases g with ⟨op, ins⟩
  obtain ⟨length, basis⟩ := legal
  change ins.length ≤ 2 at length
  rcases basis with h | h | h | ⟨h, unary⟩
  · change op = .and at h
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp [freeForm, GateOp.eval]
    · simp [freeForm, GateOp.eval, -List.getD_eq_getElem?_getD, inputs]
    · exact (free ⟨Or.inl rfl, rfl⟩).elim
  · change op = .or at h
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp [freeForm, GateOp.eval]
    · simp [freeForm, GateOp.eval, -List.getD_eq_getElem?_getD, inputs]
    · exact (free ⟨Or.inr rfl, rfl⟩).elim
  · change op = .mod 2 at h
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp [freeForm, GateOp.eval]
    · simp [freeForm, -List.getD_eq_getElem?_getD, inputs, field_even_single]
    · simp [freeForm, -List.getD_eq_getElem?_getD, inputs, field_even_pair, add_assoc]
  · change op = .not at h
    change ins.length = 1 at unary
    subst op
    rcases input_shapes ins length with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · simp at unary
    · simp [freeForm, GateOp.eval, -List.getD_eq_getElem?_getD, inputs, field_negate]
    · simp at unary

def forgetLast (k : ℕ) : (Fin (k + 1) → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  LinearMap.pi (fun j => LinearMap.proj j.castSucc)

def extendForm {k : ℕ} (w : WireForm V k) : WireForm V (k + 1) :=
  (w.1.comp ((LinearMap.fst _ _ _).prod ((forgetLast k).comp (LinearMap.snd _ _ _))), w.2)

def lastForm (k : ℕ) : WireForm V (k + 1) :=
  ((LinearMap.proj (Fin.last k)).comp (LinearMap.snd _ _ _), 0)

@[simp] theorem extendForm_value {k : ℕ} (w : WireForm V k) (x : V)
    (h : Fin k → ZMod 2) (v : ZMod 2) :
    formValue (extendForm w) x (Fin.snoc h v) = formValue w x h := by
  have eq : forgetLast k (Fin.snoc h v) = h := by
    funext i
    change (Fin.snoc (α := fun _ => ZMod 2) h v) i.castSucc = h i
    simp
  change w.1 (x, forgetLast k (Fin.snoc h v)) + w.2 = w.1 (x, h) + w.2
  rw [eq]

@[simp] theorem lastForm_value {k : ℕ} (x : V) (h : Fin k → ZMod 2) (v : ZMod 2) :
    formValue (lastForm k) x (Fin.snoc h v) = v := by
  simp [formValue, lastForm]

theorem affine_wires (raw : X → V) (input : X → List Bool)
    (initial : List (WireForm V 0))
    (hinit : ∀ x, initial.map (fun f => formValue f (raw x) Fin.elim0) = (input x).map toField)
    (gs : List Gate) (legal : ∀ g ∈ gs, legalOp g) :
    ∃ k, k = paidCount gs ∧ ∃ h : X → Fin k → ZMod 2, ∃ forms : List (WireForm V k),
      ∀ x, forms.map (fun f => formValue f (raw x) (h x)) =
        (gs.foldl appendWire (input x)).map toField := by
  classical
  induction gs using List.reverseRecOn with
  | nil => exact ⟨0, rfl, fun _ => Fin.elim0, initial, hinit⟩
  | append_singleton gs g ih =>
    have hg := legal g (by simp)
    obtain ⟨k, hc, h, forms, hf⟩ := ih (fun o ho => legal o (by simp [ho]))
    let bits (x : X) := gs.foldl appendWire (input x)
    let bit (x : X) := g.op.eval (g.inputs.map fun i => (bits x).getD i false)
    have after (x : X) : (gs ++ [g]).foldl appendWire (input x) = bits x ++ [bit x] := by
      simp [List.foldl_append, bits, bit, appendWire]
    by_cases hm : paid g
    · have count : paidCount (gs ++ [g]) = k + 1 := by
        simp [paidCount, List.countP_append, paidBool, hm, hc]
      let hnew (x : X) : Fin (k + 1) → ZMod 2 := Fin.snoc (h x) (toField (bit x))
      refine ⟨k + 1, count.symm, hnew, forms.map extendForm ++ [lastForm k], ?_⟩
      intro x
      rw [after, List.map_append, List.map_append, List.map_map]
      simp only [List.map_cons, List.map_nil, Function.comp_def, hnew, extendForm_value,
        lastForm_value, hf, bits]
    · have count : paidCount (gs ++ [g]) = k := by
        simp [paidCount, List.countP_append, paidBool, hm, hc]
      have inputs (x : X) (i : ℕ) :
          formValue (forms.getD i 0) (raw x) (h x) = toField ((bits x).getD i false) := by
        rw [← getD_map' (fun f => formValue f (raw x) (h x)), hf, value_zero]
        rw [← field_false, getD_map']
      refine ⟨k, count.symm, h, forms ++ [freeForm forms g], ?_⟩
      intro x
      rw [after, List.map_append, List.map_append, hf, List.map_singleton, List.map_singleton]
      rw [freeForm_value forms (bits x) _ _ g hg hm (inputs x)]

end Linearize

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

open scoped BigOperators

section Lower

variable {Q M : Type} [Fintype Q] [DecidableEq Q] [Fintype M] [Nonempty M]
variable {m t a d : ℕ}

theorem large_fiber_dimension (r : ℕ) (send : Words m Q → M)
    (read : M → Words m Q → Bool) (f : Fin t → Fin m) (hf : Function.Injective f)
    (separate : ∀ x y, send x = send y → x ∘ f = y ∘ f → x = y)
    (hq : Fintype.card Q = 2^a) (hm : Fintype.card M = 2^d) (hd : d ≤ a*m)
    (h0 : 0 ≤ falloff Q) (h1 : falloff Q ≤ 1)
    (β τ ε δ : ℚ) (ht : 0 ≤ τ) (he : 0 < ε) (margin : τ + ε < β)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδeq : δ = τ^2 - falloff Q ^ (2*r+1+1))
    (hwork : (1 + β) * (Fintype.card (Words m Q) : ℚ)^2 ≤
      2 * (correctCount send read : ℚ)) :
    ε * recurrenceThreshold (2*r+1) δ * (2 : ℚ)^(a*m-d) ≤
      (r+1 : ℚ) * (Fintype.card Q : ℚ)^(5*r+2) * (1+t : ℚ)^r := by
  classical
  have qw : 0 < Fintype.card Q := by rw [hq]; positivity
  have wn : Fintype.card (Words m Q) = 2^(a*m) := by
    change Fintype.card (Fin m → Q) = _
    rw [Fintype.card_fun, Fintype.card_fin, hq, ← pow_mul]
  have wp : 0 < Fintype.card (Words m Q) := by rw [wn]; positivity
  obtain ⟨z, mass, high⟩ := exists_large_score send read β τ ε ht he margin wp hwork
  let S := messageFiber send z
  let p (x : S) := x.val ∘ f
  have injective : Function.Injective p := by
    intro x y agree
    have hx : send x.val = z := (Finset.mem_filter.mp x.property).2
    have hy : send y.val = z := (Finset.mem_filter.mp y.property).2
    exact Subtype.ext (separate x.val y.val (hx.trans hy.symm) agree)
  have large : ε * (2 : ℚ)^(a*m-d) ≤ (S.card : ℚ) := by
    change ε * _ / _ ≤ (S.card : ℚ) at mass
    rw [wn, hm] at mass
    push_cast at mass
    have cut : a*m = (a*m-d)+d := by omega
    conv at mass => lhs; rw [cut, pow_add, ← mul_assoc]
    exact (le_of_mul_le_mul_right
      ((div_le_iff₀ (by positivity : (0 : ℚ) < 2^d)).mp mass) (by positivity))
  have spos : 0 < (S.card : ℚ) := lt_of_lt_of_le (by positivity) large
  have sn : 0 < S.card := by exact_mod_cast spos
  let : Nonempty S := (Finset.card_pos.mp sn).to_subtype
  have population : 0 < (Fintype.card S : ℚ)^2 := by
    rw [Fintype.card_coe]
    positivity
  have close : δ ≤ density p (2*r+1) := by
    apply (le_div_iff₀ population).mpr
    rw [Fintype.card_coe, hδeq]
    have hclose := high_score_close S (read z) (2*r+1) τ ht qw h0 h1 wp high
    exact hclose.trans (by
      exact_mod_cast projected_pairs S f hf (2*r+1))
  have limit := density_card_bound p injective r (by omega : 1 ≤ Fintype.card Q)
    hδ hδ1 close
  rw [Fintype.card_coe] at limit
  have theta := recurrenceThreshold_pos (2*r+1) hδ
  calc
    _ = recurrenceThreshold (2*r+1) δ * (ε * (2 : ℚ)^(a*m-d)) := by ring
    _ ≤ recurrenceThreshold (2*r+1) δ * (S.card : ℚ) :=
      mul_le_mul_of_nonneg_left large theta.le
    _ ≤ _ := limit

theorem choose_growth_bound (q r : ℕ) (ε θ : ℚ) (he : 0 < ε) (hθ : 0 < θ)
    (hr : 0 < r) : ∃ K : ℕ, 0 < K ∧ ∀ (b g t h : ℕ),
    t ≤ b + h + g →
    ε * θ * (2 : ℚ)^(b+h) ≤ (r+1 : ℚ) * (q : ℚ)^(5*r+2) * (1+t : ℚ)^r →
    2^b ≤ K*(1+b+g)^r := by
  let A : ℚ := (r+1 : ℚ) * (q : ℚ)^(5*r+2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have scale : 0 < ε*θ := mul_pos he hθ
  obtain ⟨K, hK⟩ := exists_nat_gt (A*(r : ℚ)^r / (ε*θ))
  have Kpos : 0 < K := by
    have : 0 ≤ A*(r : ℚ)^r / (ε*θ) := by positivity
    exact_mod_cast this.trans_lt hK
  have factor : A * (r : ℚ)^r ≤ (K : ℚ) * (ε*θ) := (div_lt_iff₀ scale).mp hK |>.le
  refine ⟨K, Kpos, ?_⟩
  intro b g t h ht hs
  change ε * θ * (2 : ℚ)^(b+h) ≤ A * (1+t : ℚ)^r at hs
  let C : ℚ := 1+b+g
  have cp : 0 ≤ C := by dsimp [C]; positivity
  have htq : (t : ℚ) ≤ (b : ℚ) + h + g := by exact_mod_cast ht
  have hprod : 1+(t : ℚ) ≤ C*(1+h) := by
    dsimp [C]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℚ) b) (Nat.cast_nonneg (α := ℚ) h),
      mul_nonneg (Nat.cast_nonneg (α := ℚ) g) (Nat.cast_nonneg (α := ℚ) h)]
  have absorb : (1+(h : ℚ))^r ≤ (r : ℚ)^r*(2 : ℚ)^h := by
    exact_mod_cast (show (1+h)^r ≤ r^r*2^h by simpa [Nat.add_comm] using polynomial_absorb r h hr)
  have bounded : (ε*θ) * ((2 : ℚ)^b * (2 : ℚ)^h) ≤
      ((K : ℚ) * (ε*θ)) * (C^r * (2 : ℚ)^h) := by
    calc
      _ ≤ A*(1+t : ℚ)^r := by simpa only [pow_add] using hs
      _ ≤ A*(C*(1+h))^r := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hprod _) hA
      _ = (A*C^r)*(1+h)^r := by rw [mul_pow, ← mul_assoc]
      _ ≤ (A*C^r)*((r : ℚ)^r*(2 : ℚ)^h) :=
        mul_le_mul_of_nonneg_left absorb (by positivity)
      _ = (A*(r : ℚ)^r)*(C^r*(2 : ℚ)^h) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right factor (by positivity)
  have final : (2 : ℚ)^b ≤ (K : ℚ)*C^r := by
    apply le_of_mul_le_mul_right _ (mul_pos scale (by positivity : 0 < (2 : ℚ)^h))
    convert bounded using 1 <;> ring
  dsimp [C] at final
  exact_mod_cast final

end Lower

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

open PEqualNP.CircuitLowerBounds

section CircuitLower

variable {a m c : ℕ}

abbrev RawIndex (m a : ℕ) := Fin m × Fin a

def rawBits (x : Words m (Fin a → Bool)) : RawIndex m a → ZMod 2 :=
  fun i => toField (x i.1 i.2)

theorem rawBits_injective : Function.Injective (rawBits (m := m) (a := a)) := by
  intro x y equal
  funext i j
  exact toField.injective (congrFun equal (i,j))

def inputBits (x : Words m (Fin a → Bool)) : List Bool :=
  (List.ofFn x).flatMap fun v => List.ofFn v

def inputForm (i : RawIndex m a) : WireForm (RawIndex m a → ZMod 2) 0 :=
  ((LinearMap.proj i).comp (LinearMap.fst _ _ _), 0)

def inputForms (m a : ℕ) : List (WireForm (RawIndex m a → ZMod 2) 0) :=
  (List.ofFn fun i : Fin m => List.ofFn fun j : Fin a => inputForm (i, j)).flatten

theorem inputForms_eval (x : Words m (Fin a → Bool)) :
    (inputForms m a).map (fun f => formValue f (rawBits x) Fin.elim0) =
      (inputBits x).map toField := by
  simp [inputForms, inputBits, List.flatMap_def, List.map_flatten, List.map_ofFn,
    Function.comp_def, inputForm, formValue, rawBits]

theorem affine_send (C : Circuit) (tap : Fin c → ℕ)
    (legal : ∀ g ∈ C.gates, legalOp g) :
    ∃ k, k = paidCount C.gates ∧ ∃ h : Words m (Fin a → Bool) → Fin k → ZMod 2,
      ∃ L : ((RawIndex m a → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] (Fin c → ZMod 2),
        ∃ γ : Fin c → ZMod 2, ∀ x j,
          toField ((C.wires (inputBits x)).getD (tap j) false) = L (rawBits x,h x) j + γ j := by
  obtain ⟨k, hk, h, forms, hforms⟩ := affine_wires rawBits inputBits
    (inputForms m a) inputForms_eval C.gates legal
  let tapForm j := forms.getD (tap j) 0
  refine ⟨k,hk,h,LinearMap.pi (fun j => (tapForm j).1),fun j => (tapForm j).2,?_⟩
  intro x j
  change _ = formValue (forms.getD (tap j) 0) (rawBits x) (h x)
  rw [← getD_map' (fun f => formValue f (rawBits x) (h x)), hforms, value_zero,
    ← field_false, getD_map']
  rfl

theorem coordinate_projection {k : ℕ}
    (L : ((RawIndex m a → ZMod 2) × (Fin k → ZMod 2)) →ₗ[ZMod 2] (Fin c → ZMod 2))
    (h : Words m (Fin a → Bool) → Fin k → ZMod 2) :
    let d := Module.finrank (ZMod 2) L.range
    d ≤ c ∧ d ≤ a*m+k ∧
    ∃ t, t+d ≤ a*m+k ∧
      ∃ f : Fin t → Fin m, Function.Injective f ∧
        ∀ x y, L.rangeRestrict (rawBits x, h x) = L.rangeRestrict (rawBits y, h y) →
          x ∘ f = y ∘ f → x = y := by
  classical
  obtain ⟨hc, hd, S, hs, membership⟩ := message_pivots L
  simp only [Fintype.card_fin, Fintype.card_prod, Nat.mul_comm m a] at hc hd hs
  let T := S.image Prod.fst
  let t := T.card
  let e : T ≃ Fin t := Fintype.equivFinOfCardEq (Fintype.card_coe T)
  let f (j : Fin t) : Fin m := (e.symm j).val
  have inj : Function.Injective f := fun _ _ equal => e.symm.injective (Subtype.ext equal)
  have bound : t ≤ S.card := Finset.card_image_le
  refine ⟨hc,hd,t,by omega,f,inj,?_⟩
  intro x y lin restrict
  apply rawBits_injective
  apply membership _ _ (h x) (h y) (congrArg Subtype.val lin)
  intro i hi
  let p : T := ⟨i.1, Finset.mem_image_of_mem Prod.fst hi⟩
  have hbase : f (e p) = i.1 := by simp [f, p]
  have equal := congrFun restrict (e p)
  change x (f (e p)) = y (f (e p)) at equal
  rw [hbase] at equal
  exact congrArg toField (congrFun equal i.2)

theorem alphabet_card (a : ℕ) : Fintype.card (Fin a → Bool) = 2^a := by
  simp

theorem alphabet_falloff (a : ℕ) : falloff (Fin a → Bool) = 1-4/((2^a : ℕ) : ℚ) := by
  rw [falloff, alphabet_card]

theorem alphabet_falloff_bounds (a : ℕ) (ha : 3 ≤ a) :
    0 ≤ falloff (Fin a → Bool) ∧ falloff (Fin a → Bool) ≤ 1 := by
  rw [alphabet_falloff]
  have h : 2^3 ≤ (2:ℕ)^a := Nat.pow_le_pow_right (by decide) ha
  have hq : (8:ℚ) ≤ ((2^a : ℕ) : ℚ) := by exact_mod_cast h
  have hp : (0:ℚ) < ((2^a : ℕ) : ℚ) := by positivity
  constructor
  · rw [sub_nonneg, div_le_iff₀ hp]
    linarith
  · exact sub_le_self _ (by positivity)

theorem circuit_lower (a r : ℕ) (ha : 3 ≤ a) (hr : 0 < r)
    (β : ℚ) (hlo : falloff (Fin a → Bool)^(r+1) < β)
    (hhi : β ≤ falloff (Fin a → Bool)^r) :
    ∃ K : ℕ, 0 < K ∧ ∀ (m b g : ℕ), b ≤ a*m →
      ∀ (C : Circuit) (tap : Fin (a*m-b) → ℕ)
        (read : (Fin (a*m-b) → Bool) → Words m (Fin a → Bool) → Bool),
        (∀ gate ∈ C.gates, legalOp gate) → paidCount C.gates ≤ g →
        let send (x : Words m (Fin a → Bool)) (j : Fin (a*m-b)) :=
          (C.wires (inputBits x)).getD (tap j) false
        (1+β)*(((2^a : ℕ) : ℚ)^m)^2 ≤ 2*(correctCount send read : ℚ) →
        2^b ≤ K*(1+b+g)^r := by
  classical
  obtain ⟨h0,h1⟩ := alphabet_falloff_bounds a ha
  obtain ⟨τ,ε,δ,ht,he,margin,hδ,hδ1,hδeq⟩ := close_constants r β h0 h1 hlo hhi
  let θ := recurrenceThreshold (2*r+1) δ
  have θpos : 0 < θ := recurrenceThreshold_pos _ hδ
  obtain ⟨K,hK,growth⟩ := choose_growth_bound (2^a) r ε θ he θpos hr
  refine ⟨K,hK,?_⟩
  intro m b g hb C tap read legal budget
  dsimp only
  intro success
  obtain ⟨k,hk,h,L,γ,hforms⟩ := affine_send C tap legal
  let d := Module.finrank (ZMod 2) L.range
  let c := a*m-b
  let : Fintype L.range := Fintype.ofFinite _
  let send (x : Words m (Fin a → Bool)) : L.range := L.rangeRestrict (rawBits x,h x)
  let decode (z : L.range) := read (fun j => toField.symm (z.val j + γ j))
  obtain ⟨hd,_,t,htd,f,hf,separate⟩ := coordinate_projection L h
  change d ≤ c at hd
  change t+d ≤ a*m+k at htd
  have recover (x : Words m (Fin a → Bool)) :
      decode (send x) = read (fun j => (C.wires (inputBits x)).getD (tap j) false) := by
    apply congrArg read
    funext j
    change toField.symm (L (rawBits x,h x) j + γ j) = _
    rw [← hforms, Equiv.symm_apply_apply]
  have correct : correctCount send decode =
      correctCount (fun x j => (C.wires (inputBits x)).getD (tap j) false) read := by
    unfold correctCount
    congr 1
    apply Finset.filter_congr
    intro xy _
    rw [recover]
  have wordCard : Fintype.card (Words m (Fin a → Bool)) = (2^a)^m := by
    change Fintype.card (Fin m → Fin a → Bool) = _
    rw [Fintype.card_fun, Fintype.card_fin, alphabet_card]
  have refined : (1+β)*(Fintype.card (Words m (Fin a → Bool)) : ℚ)^2 ≤
      2*(correctCount send decode : ℚ) := by
    rw [wordCard, Nat.cast_pow, correct]
    exact success
  have cardRange : Fintype.card L.range = 2^d := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have result := large_fiber_dimension r send decode f hf separate (alphabet_card a) cardRange
    (by omega : d ≤ a*m) h0 h1 β τ ε δ ht he margin hδ hδ1 hδeq refined
  have exponent : a*m-d = b+(c-d) := by omega
  rw [alphabet_card, exponent] at result
  exact growth b g t (c-d) (by omega) result

end CircuitLower

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

open PEqualNP.CircuitLowerBounds

section Build

def readsBack (n : ℕ) (gs : List Gate) : Prop :=
  ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < n+i.val

/-- A gate list with valid wire references and the required gate basis. -/
abbrev Plan (n : ℕ) :=
  {gs : List Gate // readsBack n gs ∧ ∀ g ∈ gs, legalOp g}

namespace Plan

abbrev gates {n : ℕ} (P : Plan n) : List Gate := P.val

theorem back {n : ℕ} (P : Plan n) : readsBack n P.gates := P.property.1

theorem legal {n : ℕ} (P : Plan n) : ∀ g ∈ P.gates, legalOp g := P.property.2

end Plan

def emptyPlan (n : ℕ) : Plan n := ⟨[], ⟨by simp [readsBack], by simp⟩⟩

def Evaluates {X : Type} {n : ℕ} (input : X → List Bool) (P : Plan n)
    (f : X → Bool) : Prop :=
  ∃ i, i < n+P.gates.length ∧ ∀ x, (P.gates.foldl appendWire (input x)).getD i false = f x

def adds {n : ℕ} (P D : Plan n) (k : ℕ) : Prop :=
  (∃ rest, D.gates = P.gates ++ rest) ∧ paidCount D.gates ≤ paidCount P.gates + k

theorem adds_refl {n : ℕ} (P : Plan n) : adds P P 0 :=
  ⟨⟨[],by simp⟩,by simp⟩

theorem adds_trans {n k l : ℕ} {P D E : Plan n} (h : adds P D k) (j : adds D E l) :
    adds P E (k+l) := by
  obtain ⟨⟨v,hv⟩,hk⟩ := h
  obtain ⟨⟨w,hw⟩,hl⟩ := j
  exact ⟨⟨v++w,by rw [hw,hv,List.append_assoc]⟩,by omega⟩

theorem adds_mono {n k l : ℕ} {P D : Plan n} (h : adds P D k) (le : k ≤ l) :
    adds P D l :=
  ⟨h.1,h.2.trans (Nat.add_le_add_left le _)⟩

theorem appendWire_length (gs : List Gate) (v : List Bool) :
    (gs.foldl appendWire v).length = v.length + gs.length := by
  induction gs generalizing v with
  | nil => simp
  | cons g gs ih => simp [ih, appendWire]; omega

theorem appendWire_prefix (gs : List Gate) (v : List Bool) :
    ∃ w, gs.foldl appendWire v = v ++ w := by
  induction gs generalizing v with
  | nil => exact ⟨[],by simp⟩
  | cons g gs ih =>
    obtain ⟨w,hw⟩ := ih (appendWire v g)
    refine ⟨[g.op.eval (g.inputs.map fun i => v.getD i false)] ++ w,?_⟩
    rw [List.foldl_cons, hw]
    simp [appendWire]

theorem getD_prefix (v w : List Bool) {i : ℕ} (hi : i < v.length) :
    (v++w).getD i false = v.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem evaluates_ext {X : Type} {n k : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) {P D : Plan n} {f : X → Bool}
    (h : Evaluates input P f) (extend : adds P D k) : Evaluates input D f := by
  obtain ⟨i,hi,hf⟩ := h
  obtain ⟨rest,hr⟩ := extend.1
  refine ⟨i,by rw [hr,List.length_append]; omega,?_⟩
  intro x
  rw [hr,List.foldl_append]
  obtain ⟨w,hw⟩ := appendWire_prefix rest (P.gates.foldl appendWire (input x))
  rw [hw, getD_prefix _ _ (by simpa [appendWire_length,size] using hi)]
  exact hf x

def planGate {n : ℕ} (P : Plan n) (g : Gate)
    (hprev : ∀ w ∈ g.inputs, w < n+P.gates.length) (hlegal : legalOp g) : Plan n := by
  refine ⟨P.gates ++ [g], ?_, ?_⟩
  ·
    intro i w hw
    by_cases h : i.val < P.gates.length
    · have eq : (P.gates ++ [g]).get i = P.gates.get ⟨i.val,h⟩ := by
        simp [List.get_eq_getElem, List.getElem_append_left h]
      rw [eq] at hw
      exact P.back ⟨i.val,h⟩ w hw
    · have hi : i.val = P.gates.length := by
        have := i.isLt
        simp at this
        omega
      have eq : (P.gates ++ [g]).get i = g := by
        simp [List.get_eq_getElem, hi]
      rw [eq] at hw
      simpa [hi] using hprev w hw
  · intro h hh
    rcases List.mem_append.mp hh with old | new
    · exact P.legal h old
    · have : h = g := by simpa using new
      simpa [this] using hlegal

theorem emit_gate {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (op : GateOp) (w : List ℕ)
    (old : ∀ i ∈ w, i < n + P.gates.length) (legal : legalOp ⟨op,w⟩) :
    ∃ D, adds P D (paidCount [⟨op,w⟩]) ∧ Evaluates input D
      (fun x => op.eval (w.map fun i => (P.gates.foldl appendWire (input x)).getD i false)) := by
  let g : Gate := ⟨op,w⟩
  let D := planGate P g old legal
  refine ⟨D,⟨⟨[g],rfl⟩,?_⟩,n+P.gates.length,?_,?_⟩
  · simp [D,planGate,Plan.gates,paidCount,List.countP_append,g]
  · simp [D,planGate,Plan.gates]
  · intro x
    have index := appendWire_length P.gates (input x)
    rw [size] at index
    change ((P.gates ++ [g]).foldl appendWire (input x)).getD (n+P.gates.length) false = _
    rw [List.foldl_append]
    simp [appendWire, g, ← index, List.getD_eq_getElem?_getD]

theorem emit_const {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (b : Bool) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun _ => b) := by
  cases b
  · simpa [paidCount,paidBool,paid,GateOp.eval] using
      emit_gate size P .or [] (by simp) ⟨by simp,Or.inr (Or.inl rfl)⟩
  · simpa [paidCount,paidBool,paid,GateOp.eval] using
      emit_gate size P .and [] (by simp) ⟨by simp,Or.inl rfl⟩

theorem emit_not {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f : X → Bool} (hf : Evaluates input P f) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => !(f x)) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨D,hd,out⟩ := emit_gate size P .not [i] (by simpa using hi)
    ⟨by simp,Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩))⟩
  refine ⟨D,?_,?_⟩
  · simpa [paidCount,paidBool,paid] using hd
  · simpa [GateOp.eval,-List.getD_eq_getElem?_getD,hfi] using out

theorem emit_and {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f g : X → Bool} (hf : Evaluates input P f) (hg : Evaluates input P g) :
    ∃ D, adds P D 1 ∧ Evaluates input D (fun x => f x && g x) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨j,hj,hgj⟩ := hg
  have refs : ∀ w ∈ [i,j], w < n + P.gates.length := by
    simp_all
  obtain ⟨D,hd,out⟩ := emit_gate size P .and [i,j] refs ⟨by simp,Or.inl rfl⟩
  refine ⟨D,?_,?_⟩
  · simpa [paidCount,paidBool,paid] using hd
  · simpa [GateOp.eval,-List.getD_eq_getElem?_getD,hfi,hgj] using out

theorem emit_xor {X : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n)
    {f g : X → Bool} (hf : Evaluates input P f) (hg : Evaluates input P g) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => Bool.xor (f x) (g x)) := by
  obtain ⟨i,hi,hfi⟩ := hf
  obtain ⟨j,hj,hgj⟩ := hg
  have refs : ∀ w ∈ [i,j], w < n + P.gates.length := by
    simp_all
  obtain ⟨D,hd,out⟩ := emit_gate size P (.mod 2) [i,j] refs ⟨by simp,Or.inr (Or.inr (Or.inl rfl))⟩
  have cost : adds P D 0 := by simpa [paidCount,paidBool,paid] using hd
  obtain ⟨E,he,result⟩ := emit_not size D out
  have eq (x : X) :
      (!(GateOp.eval (.mod 2) [(P.gates.foldl appendWire (input x)).getD i false,
        (P.gates.foldl appendWire (input x)).getD j false])) = Bool.xor (f x) (g x) := by
    rw [hfi,hgj]
    cases f x <;> cases g x <;> rfl
  refine ⟨E,by simpa using adds_trans cost he,?_⟩
  change Evaluates input E (fun x => !(GateOp.eval (.mod 2)
    [(P.gates.foldl appendWire (input x)).getD i false,
      (P.gates.foldl appendWire (input x)).getD j false])) at result
  rw [funext eq] at result
  exact result

theorem build_many {X I J : Type} {n : ℕ} {input : X → List Bool}
    (size : ∀ x, (input x).length = n) (P : Plan n) (k : ℕ)
    (s : Finset I) (f : I → J → X → Bool)
    (each : ∀ i ∈ s, ∀ (D : Plan n) (v : ℕ), adds P D v →
      ∃ E, adds D E k ∧ ∀ j, Evaluates input E (f i j)) :
    ∃ D, adds P D (s.card*k) ∧ ∀ i ∈ s, ∀ j, Evaluates input D (f i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨P,by simpa using adds_refl P,by simp⟩
  | @insert i s hi ih =>
    obtain ⟨D,extend,results⟩ := ih (fun j hj => each j (Finset.mem_insert_of_mem hj))
    obtain ⟨E,next,new⟩ := each i (Finset.mem_insert_self _ _) D _ extend
    refine ⟨E,by simpa [Finset.card_insert_of_notMem hi,Nat.add_mul] using adds_trans extend next,?_⟩
    intro j hj p
    rcases Finset.mem_insert.mp hj with eq | old
    · simpa [eq] using new p
    · exact evaluates_ext size (results j old p) next

end Build

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

open scoped BigOperators

section Synthesis

variable {X : Type} {n : ℕ} {input : X → List Bool}
variable (size : ∀ x, (input x).length = n)

theorem field_xor (a b : Bool) : toField (Bool.xor a b) = toField a + toField b := by
  cases a <;> cases b <;> decide +kernel

include size in
theorem emit_sum {I : Type} (P : Plan n) (S : Finset I) (f : I → X → Bool)
    (h : ∀ i ∈ S, Evaluates input P (f i)) :
    ∃ D, adds P D 0 ∧ Evaluates input D (fun x => toField.symm (∑ i ∈ S, toField (f i x))) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simpa [← field_false] using emit_const size P false
  | @insert i S hi ih =>
    obtain ⟨D,hd,prev⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have current := evaluates_ext size (h i (Finset.mem_insert_self _ _)) hd
    obtain ⟨E,he,sum⟩ := emit_xor size D current prev
    refine ⟨E,by simpa using adds_trans hd he,?_⟩
    have eq (x : X) :
        Bool.xor (f i x) (toField.symm (∑ j ∈ S, toField (f j x))) =
          toField.symm (∑ j ∈ insert i S, toField (f j x)) := by
      apply toField.injective
      simp [field_xor, Finset.sum_insert hi]
    simpa only [funext eq] using sum

include size in
theorem build_values {I : Type} (P : Plan n) (k : ℕ)
    (S : Finset I) (f : I → X → Bool)
    (each : ∀ i ∈ S, ∀ (D : Plan n) (v : ℕ), adds P D v →
      ∃ E, adds D E k ∧ Evaluates input E (f i)) :
    ∃ D, adds P D (S.card*k) ∧ ∀ i ∈ S, Evaluates input D (f i) := by
  obtain ⟨D,hd,h⟩ := build_many size P k S (fun i (_ : Unit) => f i) (by
    intro i hi D v hd
    obtain ⟨E,he,eval⟩ := each i hi D v hd
    exact ⟨E,he,fun _ => eval⟩)
  exact ⟨D,hd,fun i hi => h i hi ()⟩

abbrev Label (e : ℕ) := Fin e → Bool

def splitLabel {e : ℕ} (b : Label e) (v : Bool) : Label (e+1) :=
  Fin.snoc (α := fun _ => Bool) b v

theorem splitLabel_eq {e : ℕ} (s : Label (e+1)) (b : Label e) (v : Bool) :
    s = splitLabel b v ↔ (fun j => s j.castSucc) = b ∧ s (Fin.last e) = v := by
  constructor
  · rintro rfl
    exact ⟨by funext j; simp [splitLabel],by simp [splitLabel]⟩
  · rintro ⟨init, last⟩
    funext j
    induction j using Fin.lastCases with
    | last => simpa [splitLabel] using last
    | cast j => simpa [splitLabel] using congrFun init j

/- Split each initial-segment indicator with one AND. The other branch is the XOR
of the preceding indicator and the first branch. -/
include size in
theorem emit_indicators (e : ℕ) (P : Plan n) (s : Fin e → X → Bool)
    (hs : ∀ j, Evaluates input P (s j)) :
    ∃ D, adds P D (2^e-1) ∧ ∀ b : Label e, Evaluates input D
      (fun x => decide ((fun j => s j x) = b)) := by
  classical
  induction e generalizing P with
  | zero =>
    obtain ⟨D,hd,yes⟩ := emit_const size P true
    refine ⟨D,by simpa using hd,?_⟩
    intro b
    have : (fun x => decide ((fun j => s j x) = b)) = (fun _ => true) := by
      funext x
      exact decide_eq_true (Subsingleton.elim _ _)
    simpa only [this] using yes
  | succ e ih =>
    obtain ⟨D,hd,prev⟩ := ih P (fun j => s j.castSucc) (fun j => hs j.castSucc)
    let f (b : Label e) (v : Bool) (x : X) :=
      decide ((fun j => s j x) = splitLabel b v)
    have each (b : Label e) (E : Plan n)
        (pref : Evaluates input E (fun x => decide ((fun j => s j.castSucc x) = b)))
        (endBit : Evaluates input E (s (Fin.last e))) :
        ∃ F, adds E F 1 ∧ ∀ v, Evaluates input F (f b v) := by
      obtain ⟨F,hF,one⟩ := emit_and size E pref endBit
      obtain ⟨G,hG,zero⟩ := emit_xor size F (evaluates_ext size pref hF) one
      have eq1 (x : X) :
          (decide ((fun j => s j.castSucc x) = b) && s (Fin.last e) x) = f b true x := by
        unfold f
        simp only [splitLabel_eq]
        by_cases hp : (fun j => s j.castSucc x) = b <;> cases hb : s (Fin.last e) x <;>
          simp [hp]
      have eq0 (x : X) :
          Bool.xor (decide ((fun j => s j.castSucc x) = b))
            (decide ((fun j => s j.castSucc x) = b) && s (Fin.last e) x) = f b false x := by
        unfold f
        simp only [splitLabel_eq]
        by_cases hp : (fun j => s j.castSucc x) = b <;> cases hb : s (Fin.last e) x <;>
          simp [hp]
      refine ⟨G,by simpa using adds_trans hF hG,?_⟩
      intro v
      cases v
      · simpa only [funext eq0] using zero
      · simpa only [funext eq1] using evaluates_ext size one hG
    obtain ⟨G,hG,result⟩ := build_many size D 1 Finset.univ f (by
      intro b _ E _ ext
      exact each b E (evaluates_ext size (prev b) ext)
        (evaluates_ext size (evaluates_ext size (hs (Fin.last e)) hd) ext))
    have cost : 2^e-1+Fintype.card (Label e) = 2^(e+1)-1 := by
      have positive : 0 < (2:ℕ)^e := by positivity
      simp [Label,pow_succ]
      omega
    refine ⟨G,by simpa only [Finset.card_univ, mul_one, cost] using adds_trans hd hG,?_⟩
    intro b
    let u : Label e := fun i => b i.castSucc
    let v := b (Fin.last e)
    have eq : b = splitLabel u v := (splitLabel_eq _ _ _).mpr ⟨rfl,rfl⟩
    rw [eq]
    exact result u (Finset.mem_univ _) v

end Synthesis

end PEqualNP.Outside.L_lib_907

namespace PEqualNP.Outside.L_lib_907

open scoped BigOperators

section Coding

variable {m a r e : ℕ}

abbrev BlockMap (r e m : ℕ) := (Fin r × Label e) ↪ Fin m

noncomputable def blockMap (capacity : r*2^e ≤ m) : BlockMap r e m :=
  let E : Label e ≃ Fin (2^e) := Fintype.equivFinOfCardEq (alphabet_card e)
  ((Equiv.prodCongr (Equiv.refl (Fin r)) E).trans finProdFinEquiv).toEmbedding.trans
    ⟨Fin.castLE capacity, fun _ _ h => Fin.ext (congrArg (fun z : Fin m => z.val) h)⟩

def inputIndex (i : RawIndex m a) : Fin (m*a) := finProdFinEquiv i

theorem inputBits_eq_ofFn (x : Words m (Fin a → Bool)) :
    inputBits x = List.ofFn (fun i : Fin (m*a) =>
      let p := (finProdFinEquiv (m := m) (n := a)).symm i
      x p.1 p.2) := by
  rw [inputBits, List.flatMap_def, List.map_ofFn, List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have bound : i.val*a+j.val < m*a := calc
    _ < i.val*a+a := Nat.add_lt_add_left j.isLt _
    _ = (i.val+1)*a := by rw [Nat.add_mul,Nat.one_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ i.isLt
  have idx : (⟨i.val*a+j.val,bound⟩ : Fin (m*a)) = inputIndex (i,j) := by
    change _ = finProdFinEquiv (i,j)
    apply Fin.ext
    simp [Nat.add_comm,Nat.mul_comm]
  change x i j = x ((finProdFinEquiv (m := m) (n := a)).symm
    ⟨i.val*a+j.val,bound⟩).1 ((finProdFinEquiv (m := m) (n := a)).symm
    ⟨i.val*a+j.val,bound⟩).2
  rw [idx]
  simp [inputIndex]

theorem inputBits_length (x : Words m (Fin a → Bool)) :
    (inputBits x).length = a*m := by
  rw [inputBits_eq_ofFn, List.length_ofFn, Nat.mul_comm]

theorem evaluates_input (P : Plan (a*m)) (i : RawIndex m a) :
    Evaluates inputBits P (fun x => x i.1 i.2) := by
  have hi : (inputIndex i).val < a*m := calc
    _ < m*a := (inputIndex i).isLt
    _ = a*m := Nat.mul_comm _ _
  refine ⟨(inputIndex i).val, by omega, ?_⟩
  intro x
  obtain ⟨suffix,hs⟩ := appendWire_prefix P.gates (inputBits x)
  rw [hs, getD_prefix _ _ (by rw [inputBits_length]; exact hi), inputBits_eq_ofFn]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,(dite_eq_left (inputIndex i).isLt),Option.getD_some]
  have eta : (⟨(inputIndex i).val,(inputIndex i).isLt⟩ : Fin (m*a)) = inputIndex i := rfl
  rw [eta]
  simp only [inputIndex, Equiv.symm_apply_apply]


def basisLabel (j : Fin e) : Label e := fun k => decide (j = k)

theorem basisLabel_injective : Function.Injective (basisLabel (e := e)) := by
  intro i j h
  have atI := congrFun h i
  simpa [basisLabel, eq_comm] using atI

/-- Each block contains one symbol per label. Flip the first bit at the
syndrome label. The repaired block has zero syndrome, so its bits at unit
labels can be recovered from the other bits. -/
def syndrome (E : BlockMap r e m) (first : Fin a) (word : Words m (Fin a → Bool))
    (block : Fin r) : Label e :=
  fun j => toField.symm (∑ b ∈ Finset.univ.filter (fun b : Label e => b j = true),
    toField (word (E (block,b)) first))

noncomputable def repaired (E : BlockMap r e m) (first : Fin a)
    (x : Words m (Fin a → Bool)) : Words m (Fin a → Bool) := by
  classical
  exact fun i j => if j = first then Bool.xor (x i j)
    (decide (∃ block : Fin r, E (block,syndrome E first x block) = i)) else x i j

theorem repaired_other (E : BlockMap r e m) (first : Fin a)
    (x : Words m (Fin a → Bool)) (i : Fin m) (j : Fin a) (hj : j ≠ first) :
    repaired E first x i j = x i j := by
  simp [repaired, hj]

theorem repaired_outside (E : BlockMap r e m) (first : Fin a)
    (x : Words m (Fin a → Bool)) (i : Fin m) (outside : ∀ u : Fin r, ∀ b, E (u,b) ≠ i)
    (j : Fin a) : repaired E first x i j = x i j := by
  have no : ¬ ∃ block : Fin r, E (block,syndrome E first x block) = i := by
    rintro ⟨u,h⟩
    exact outside u _ h
  simp [repaired, no]

theorem repaired_in (E : BlockMap r e m) (first : Fin a)
    (x : Words m (Fin a → Bool)) (u : Fin r) (b : Label e) :
    repaired E first x (E (u,b)) first =
      Bool.xor (x (E (u,b)) first) (decide (syndrome E first x u = b)) := by
  have condition : (∃ block : Fin r, E (block,syndrome E first x block) = E (u,b)) ↔
      syndrome E first x u = b := by
    constructor
    · rintro ⟨v,hv⟩
      have same := E.injective hv
      have uv : v = u := congrArg (fun z : Fin r × Label e => z.1) same
      subst v
      exact congrArg Prod.snd same
    · intro h
      exact ⟨u,by rw [h]⟩
  simp [repaired]

theorem repaired_dist (E : BlockMap r e m) (first : Fin a)
    (x : Words m (Fin a → Bool)) : hammingDist x (repaired E first x) ≤ r := by
  classical
  let picked (u : Fin r) := E (u,syndrome E first x u)
  let S := Finset.univ.image picked
  change (Finset.univ.filter (fun i => x i ≠ repaired E first x i)).card ≤ r
  have sub : Finset.univ.filter (fun i => x i ≠ repaired E first x i) ⊆ S := by
    intro i hi
    by_contra notpicked
    have none : ¬ ∃ u, picked u = i := by simpa [S] using notpicked
    have same : x i = repaired E first x i := by
      funext j
      change x i j = if j = first then Bool.xor (x i j) (decide (∃ u, picked u = i)) else x i j
      simp [none]
    exact (Finset.mem_filter.mp hi).2 same
  exact (Finset.card_le_card sub).trans (by simpa [S] using
    (Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := picked)))

theorem repaired_syndrome (E : BlockMap r e m) (first : Fin a)
    (x : Words m (Fin a → Bool)) (u : Fin r) (j : Fin e) :
    syndrome E first (repaired E first x) u j = false := by
  classical
  let s := syndrome E first x u
  let T := Finset.univ.filter (fun b : Label e => b j = true)
  apply toField.injective
  simp only [syndrome, Equiv.apply_symm_apply, field_false]
  simp_rw [repaired_in, field_xor]
  rw [Finset.sum_add_distrib]
  change (∑ b ∈ T, toField (x (E (u,b)) first)) +
    (∑ b ∈ T, toField (decide (s = b))) = 0
  have fst : (∑ b ∈ T, toField (x (E (u,b)) first)) = toField (s j) :=
    (toField.apply_symm_apply _).symm
  have snd : (∑ b ∈ T, toField (decide (s = b))) = toField (s j) := by
    have asIte (b : Label e) : toField (decide (s = b)) = if b = s then 1 else 0 := by
      by_cases h : b = s <;> simp [h,field_false,field_true,eq_comm]
    simp_rw [asIte]
    rw [Finset.sum_ite_eq']
    cases hb : s j <;> simp [T,hb,field_false,field_true]
  rw [fst,snd]
  cases s j <;> decide +kernel

def basisPosition (E : BlockMap r e m) (first : Fin a) (p : Fin r × Fin e) : RawIndex m a :=
  (E (p.1,basisLabel p.2),first)

theorem basisPosition_injective (E : BlockMap r e m) (first : Fin a) :
    Function.Injective (basisPosition E first) := by
  intro p q h
  have same := E.injective (congrArg Prod.fst h)
  exact Prod.ext (congrArg (fun z : Fin r × Label e => z.1) same)
    (basisLabel_injective (congrArg (fun z : Fin r × Label e => z.2) same))

theorem codeword_separation (E : BlockMap r e m) (first : Fin a)
    (drop : Finset (RawIndex m a))
    (hd : ∀ i ∈ drop, ∃ p, basisPosition E first p = i)
    (x y : Words m (Fin a → Bool))
    (zx : ∀ u j, syndrome E first x u j = false)
    (zy : ∀ u j, syndrome E first y u j = false)
    (agree : ∀ i : RawIndex m a, i ∉ drop → x i.1 i.2 = y i.1 i.2) :
    x = y := by
  classical
  funext i j
  by_cases h : (i,j) ∈ drop
  · obtain ⟨⟨u,k⟩, hp⟩ := hd (i,j) h
    have hi : E (u,basisLabel k) = i := congrArg Prod.fst hp
    have hj : first = j := congrArg Prod.snd hp
    rw [← hi, ← hj]
    let T := Finset.univ.filter (fun b : Label e => b k = true)
    let b0 := basisLabel k
    have inT : b0 ∈ T := by simp [T,b0,basisLabel]
    have equalSums : (∑ b ∈ T, toField (x (E (u,b)) first)) =
        ∑ b ∈ T, toField (y (E (u,b)) first) := by
      apply toField.symm.injective
      exact (zx u k).trans (zy u k).symm
    have equalRest : (∑ b ∈ T.erase b0, toField (x (E (u,b)) first)) =
        ∑ b ∈ T.erase b0, toField (y (E (u,b)) first) := by
      refine Finset.sum_congr rfl fun b hb => ?_
      apply congrArg toField
      apply agree (E (u,b),first)
      intro bad
      obtain ⟨⟨v,l⟩,eq⟩ := hd (E (u,b),first) bad
      have same := E.injective (congrArg Prod.fst eq)
      have lab : basisLabel l = b := congrArg Prod.snd same
      have lk : l = k := by
        have bit : b k = true := (Finset.mem_filter.mp (Finset.mem_erase.mp hb).2).2
        simpa [← lab,basisLabel] using bit
      exact (Finset.mem_erase.mp hb).1 (by simpa [b0,lk] using lab.symm)
    rw [← Finset.sum_erase_add _ _ inT, ← Finset.sum_erase_add _ _ inT, equalRest] at equalSums
    exact toField.injective (add_left_cancel equalSums)
  · exact agree (i,j) h

end Coding

end PEqualNP.Outside.L_lib_907
namespace PEqualNP.Outside.L_lib_907

open scoped BigOperators
open PEqualNP.CircuitLowerBounds

section Upper

variable {m a r e : ℕ}

theorem compile_syndrome (E : BlockMap r e m) (first : Fin a)
    (P : Plan (a*m)) (u : Fin r) :
    ∃ D, adds P D 0 ∧ ∀ j, Evaluates inputBits D (fun x => syndrome E first x u j) := by
  classical
  obtain ⟨D,hd,outputs⟩ := build_values inputBits_length P 0 Finset.univ
    (fun j x => syndrome E first x u j) (by
      intro j _ D _ _
      exact emit_sum inputBits_length D (Finset.univ.filter fun b : Label e => b j = true)
        (fun b x => x (E (u,b)) first)
        (fun b _ => evaluates_input D (E (u,b),first)))
  exact ⟨D,by simpa using hd,fun j => outputs j (Finset.mem_univ _)⟩

theorem compile_block (E : BlockMap r e m) (first : Fin a)
    (P : Plan (a*m)) (u : Fin r) :
    ∃ D, adds P D (2^e-1) ∧ ∀ b : Label e,
      Evaluates inputBits D (fun x => decide (syndrome E first x u = b)) := by
  classical
  obtain ⟨D,hd,low⟩ := compile_syndrome E first P u
  obtain ⟨G,hg,outputs⟩ := emit_indicators inputBits_length e D
    (fun j x => syndrome E first x u j) low
  exact ⟨G,by simpa using adds_trans hd hg,outputs⟩

theorem compile_repaired (E : BlockMap r e m) (first : Fin a) :
    ∃ D : Plan (a*m), paidCount D.gates ≤ r*2^e ∧
      ∀ i : RawIndex m a, Evaluates inputBits D (fun x => repaired E first x i.1 i.2) := by
  classical
  let P := emptyPlan (a*m)
  obtain ⟨D,hd,decoded⟩ := build_many inputBits_length P (2^e-1) Finset.univ
    (fun (u : Fin r) (b : Label e) x => decide (syndrome E first x u = b)) (by
      intro u _ C _ _
      exact compile_block E first C u)
  obtain ⟨G,hg,repairedBits⟩ := build_values inputBits_length D 0 Finset.univ
    (fun i : RawIndex m a => fun x => repaired E first x i.1 i.2) (by
      rintro ⟨i,j⟩ _ C w past
      by_cases hj : j = first
      · subst j
        by_cases h : ∃ u : Fin r, ∃ b : Label e, E (u,b) = i
        · obtain ⟨u,b,rfl⟩ := h
          obtain ⟨F,hF,out⟩ := emit_xor inputBits_length C
            (evaluates_input C (E (u,b),first))
            (evaluates_ext inputBits_length (decoded u (Finset.mem_univ _) b) past)
          exact ⟨F,hF,by simpa [repaired_in] using out⟩
        · have no (u : Fin r) (b : Label e) : E (u,b) ≠ i := fun equal => h ⟨u,b,equal⟩
          refine ⟨C,adds_refl C,?_⟩
          simpa only [repaired_outside E first _ i no] using (evaluates_input C (i,first))
      · refine ⟨C,adds_refl C,?_⟩
        simpa only [repaired_other E first _ i j hj] using (evaluates_input C (i,j)))
  have cost := (adds_trans hd hg).2
  simp [paidCount, P, emptyPlan, Plan.gates] at cost
  have cost' : paidCount G.gates ≤ r * (2^e-1) := cost
  exact ⟨G,cost'.trans (Nat.mul_le_mul_left r (Nat.sub_le _ _)),
    fun i => repairedBits i (Finset.mem_univ _)⟩

theorem ceiling_cover (b r : ℕ) (hr : 0 < r) :
    b ≤ r * ((b+r-1)/r) := by
  have eq := Nat.mod_add_div (b+r-1) r
  have lt := Nat.mod_lt (b+r-1) hr
  omega

theorem exists_drop (E : BlockMap r e m) (first : Fin a) {b : ℕ} (hb : b ≤ r*e) :
    ∃ drop : Finset (RawIndex m a), drop.card = b ∧
      ∀ i ∈ drop, ∃ p, basisPosition E first p = i := by
  classical
  let p (i : Fin b) := finProdFinEquiv.symm (Fin.castLE hb i)
  have hp : Function.Injective p := by
    intro x y h
    have eq := finProdFinEquiv.symm.injective h
    exact Fin.ext (congrArg (fun z : Fin (r*e) => z.val) eq)
  let f := basisPosition E first ∘ p
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ ((basisPosition_injective E first).comp hp)]
    simp
  · intro i hi
    obtain ⟨z,_,equal⟩ := Finset.mem_image.mp hi
    exact ⟨p z,equal⟩

theorem drop_complement {b : ℕ} (drop : Finset (RawIndex m a)) (card : drop.card = b) :
    ∃ keep : Fin (a*m-b) → RawIndex m a,
      ∀ i : RawIndex m a, i ∉ drop → ∃ j, keep j = i := by
  classical
  let S := Finset.univ \ drop
  have size : Fintype.card S = a*m-b := by
    rw [Fintype.card_coe, Finset.card_sdiff_of_subset (Finset.subset_univ drop), Finset.card_univ, card]
    simp [RawIndex, Nat.mul_comm m a]
  let E := Fintype.equivFinOfCardEq size
  refine ⟨fun j => (E.symm j).val,?_⟩
  intro i hi
  let x : S := ⟨i,by simp [S,hi]⟩
  exact ⟨E x,by simp [x]⟩

theorem correct_of_repair {Q M : Type} [Fintype Q] [DecidableEq Q] [Fintype M]
    (send : Words m Q → M) (read : M → Words m Q → Bool) (repair : Words m Q → Words m Q)
    (recovers : ∀ x y, read (send x) y = equalityParity (repair x) y)
    (β : ℚ) (hq : 0 < Fintype.card Q) (h0 : 0 ≤ falloff Q) (h1 : falloff Q ≤ 1)
    (hβ : β ≤ falloff Q ^ r) (near : ∀ x, hammingDist x (repair x) ≤ r) :
    (1+β)*(Fintype.card (Words m Q) : ℚ)^2 ≤ 2*(correctCount send read : ℚ) := by
  classical
  let N := (Fintype.card (Words m Q) : ℚ)
  have power : (Fintype.card Q : ℚ)^m = N := by
    simp [N, Words]
  have each (x : Words m Q) : β*N ≤
      ∑ y : Words m Q, boolSign (read (send x) y) * boolSign (equalityParity x y) := by
    simp_rw [recovers]
    rw [parity_inner _ _ hq, power, hammingDist_comm (repair x) x]
    let dist := hammingDist x (repair x)
    have sum : r = dist+(r-dist) := by have hx := near x; change dist ≤ r at hx; omega
    have mono : falloff Q ^ r ≤ falloff Q ^ dist := by
      calc
        _ = falloff Q ^ dist * falloff Q^(r-dist) := by rw [← pow_add, ← sum]
        _ ≤ _ := by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1 (n := r-dist)) (pow_nonneg h0 dist)
    have hbound := hβ.trans mono
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ N)
  have aggregate : β*N^2 ≤ ∑ xy : Words m Q × Words m Q,
      boolSign (read (send xy.1) xy.2) * boolSign (equalityParity xy.1 xy.2) := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ x : Words m Q, β*N := by simp [N,nsmul_eq_mul,pow_two]; ring
      _ ≤ _ := Finset.sum_le_sum fun x _ => each x
  have eq := sum_fiber_score_as_pairs send read
  rw [← eq, sum_fiber_score] at aggregate
  change β*N^2 ≤ 2*(correctCount send read : ℚ) - N^2 at aggregate
  change (1+β)*N^2 ≤ _
  nlinarith

theorem circuit_upper (a r m b : ℕ) (ha : 3 ≤ a) (hr : 0 < r) (β : ℚ)
    (hβ : β ≤ falloff (Fin a → Bool)^r)
    (capacity : r*2^((b+r-1)/r) ≤ m) :
    let e := (b+r-1)/r
    let c := a*m-b
    ∃ (C : Circuit) (tap : Fin c → ℕ)
      (read : (Fin c → Bool) → Words m (Fin a → Bool) → Bool),
      readsBack (a*m) C.gates ∧ (∀ gate ∈ C.gates, legalOp gate) ∧
      paidCount C.gates ≤ r*2^e ∧ (∀ j, tap j < a*m+C.gates.length) ∧
      let send (x : Words m (Fin a → Bool)) (j : Fin c) :=
        (C.wires (inputBits x)).getD (tap j) false
      (1+β)*(((2^a : ℕ) : ℚ)^m)^2 ≤ 2*(correctCount send read : ℚ) := by
  classical
  let e := (b+r-1)/r
  let c := a*m-b
  let E : BlockMap r e m := blockMap capacity
  let first : Fin a := ⟨0,by omega⟩
  let repair := repaired E first
  obtain ⟨drop,hd,inBlock⟩ := exists_drop E first (ceiling_cover b r hr)
  obtain ⟨keep,hkeep⟩ := drop_complement drop hd
  obtain ⟨D,hcost,hD⟩ := compile_repaired E first
  let C : Circuit := ⟨D.gates,0⟩
  let tap (j : Fin c) := Classical.choose (hD (keep j))
  have ht (j : Fin c) := (Classical.choose_spec (hD (keep j))).1
  let send (x : Words m (Fin a → Bool)) (j : Fin c) :=
    (C.wires (inputBits x)).getD (tap j) false
  have sends (x : Words m (Fin a → Bool)) (j : Fin c) :
      send x j = repair x (keep j).1 (keep j).2 :=
    (Classical.choose_spec (hD (keep j))).2 x
  let read (z : Fin c → Bool) (y : Words m (Fin a → Bool)) :=
    if hz : ∃ x, send x = z then equalityParity (repair (Classical.choose hz)) y else false
  have recover (x y : Words m (Fin a → Bool)) :
      read (send x) y = equalityParity (repair x) y := by
    let hz : ∃ v, send v = send x := ⟨x,rfl⟩
    change (if h : ∃ v, send v = send x then
      equalityParity (repair (Classical.choose h)) y else false) = _
    rw [dite_eq_left hz]
    apply congrArg (fun q => equalityParity q y)
    apply codeword_separation E first drop inBlock
    · exact repaired_syndrome E first _
    · exact repaired_syndrome E first _
    · intro i hi
      obtain ⟨j,hj⟩ := hkeep i hi
      have eq := congrFun (Classical.choose_spec hz) j
      rw [sends, sends, hj] at eq
      exact eq
  obtain ⟨h0,h1⟩ := alphabet_falloff_bounds a ha
  have alph := alphabet_card a
  have qw : 0 < Fintype.card (Fin a → Bool) := by rw [alph]; positivity
  have yes := correct_of_repair send read repair recover β qw h0 h1 hβ (repaired_dist E first)
  have wordCard : Fintype.card (Words m (Fin a → Bool)) = (2^a)^m := by
    change Fintype.card (Fin m → Fin a → Bool) = _
    rw [Fintype.card_fun,Fintype.card_fin,alph]
  rw [wordCard,Nat.cast_pow] at yes
  exact ⟨C,tap,read,D.back,D.legal,hcost,ht,yes⟩

end Upper

end PEqualNP.Outside.L_lib_907
theorem PEqualNP.Outside.L_lib_907 :
  ∀ (a r : Nat), 3 ≤ a → 0 < r →
  let q := 2^a
  let ρ : ℚ := 1-4/(q : ℚ)
  ∀ β : ℚ, ρ^(r+1) < β → β ≤ ρ^r →
  ∃ K : Nat, 0 < K ∧ ∀ (m b : Nat), 0 < m → b ≤ a*m →
    let n := a*m
    let c := n-b
    let W := Fin m → Fin a → Bool
    let Circ := PEqualNP.CircuitLowerBounds.Circuit
    let legal := fun (C : Circ) =>
      (∀ i : Fin C.gates.length, ∀ w ∈ (C.gates.get i).inputs, w < n+i.val) ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
    let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
      ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
    let works := fun (g : Nat) =>
      ∃ (C : Circ) (tap : Fin c → Nat) (read : (Fin c → Bool) → W → Bool),
        legal C ∧ cost C ≤ g ∧ (∀ j, tap j < n+C.gates.length) ∧
        let send := fun (x : W) (j : Fin c) =>
          (C.wires ((List.ofFn x).flatMap (fun v => List.ofFn v))).getD (tap j) false
        let correct := ((Finset.univ : Finset (W × W)).filter (fun xy =>
          let same := ((Finset.univ : Finset (Fin m)).filter (fun i => xy.1 i = xy.2 i)).card
          read (send xy.1) xy.2 = (same % 2 == 1))).card
        (1+β)*((q : ℚ)^m)^2 ≤ 2*(correct : ℚ)
    (∀ g : Nat, works g → 2^b ≤ K*(1+b+g)^r) ∧
    (let e := (b+r-1)/r
     r*2^e ≤ m → works (r*2^e)) := by
  classical
  intro a r ha hr
  dsimp only
  intro β hlo hhi
  have rho : PEqualNP.Outside.L_lib_907.falloff (Fin a → Bool) = 1-4/(2:ℚ)^a := by
    rw [PEqualNP.Outside.L_lib_907.alphabet_falloff]
    norm_num
  rw [← rho] at hlo hhi
  obtain ⟨K,hK,lower⟩ := PEqualNP.Outside.L_lib_907.circuit_lower a r ha hr β hlo hhi
  refine ⟨K,hK,?_⟩
  intro m b _ hb
  constructor
  · intro g valid
    obtain ⟨C,tap,read,legal,budget,_,success⟩ := valid
    apply lower m b g hb C tap read legal.2 budget
    norm_num
    exact success
  · intro capacity
    obtain ⟨C,tap,read,back,legal,budget,taps,success⟩ :=
      PEqualNP.Outside.L_lib_907.circuit_upper a r m b ha hr β hhi capacity
    refine ⟨C,tap,read,⟨back,legal⟩,budget,taps,?_⟩
    norm_num at success
    exact success