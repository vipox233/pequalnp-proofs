import PEqualNP.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finset.Sort

namespace PEqualNP.Outside.L_meta_25585_aux

open Polynomial

def move (keep : Bool) (mode letter : Nat) : Nat × Nat :=
  let near := letter.testBit 0
  let far := letter.testBit 1
  let hit := letter.testBit 2
  let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
    ((mode == 3) && near)
  let diagonal := keep && !hit && (((mode == 1) && !near && !far) ||
    (mode == 2) || (mode == 3))
  (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
    hit.toNat + (aligned && hit).toNat)

def gainFrom (keep : Bool) (n mode code : Nat) : Nat :=
  ((List.range n).foldl (fun (st : Nat × Nat) j =>
    let result := move keep st.1 ((code >>> (3 * j)) % 8)
    (result.1, st.2 + result.2)) (mode, 0)).2

def gain (keep : Bool) (n code : Nat) : Nat :=
  gainFrom keep n 0 code

def price (keep : Bool) (n d : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun word =>
    2 ^ (2 * n - (gain keep n word - d)))).sum

lemma foldl_acc (step : Nat → Nat → Nat × Nat) (l : List Nat) (mode acc : Nat) :
    (l.foldl (fun (st : Nat × Nat) j =>
      let r := step st.1 j
      (r.1, st.2 + r.2)) (mode, acc)).2 =
    acc + (l.foldl (fun (st : Nat × Nat) j =>
      let r := step st.1 j
      (r.1, st.2 + r.2)) (mode, 0)).2 := by
  induction l generalizing mode acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [ih (step mode a).1 (acc + (step mode a).2), ih (step mode a).1 (0 + (step mode a).2)]
    omega

lemma shift_three_succ (code j : Nat) :
    code >>> (3 * (j + 1)) = (code / 8) >>> (3 * j) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have h1 : 3 * (j + 1) = 3 + 3 * j := by omega
  rw [h1, pow_add]
  have h2 : (2 : Nat) ^ 3 = 8 := by decide
  rw [h2, Nat.div_div_eq_div_mul]

lemma gainFrom_zero (keep : Bool) (mode code : Nat) :
    gainFrom keep 0 mode code = 0 := by
  simp [gainFrom]

lemma gainFrom_succ (keep : Bool) (n mode code : Nat) :
    gainFrom keep (n + 1) mode code =
    (move keep mode (code % 8)).2 +
    gainFrom keep n (move keep mode (code % 8)).1 (code / 8) := by
  unfold gainFrom
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : code >>> (3 * 0) = code := by simp
  rw [h0]
  have hf :
      (fun (st : Nat × Nat) (x : Nat) =>
        let result := move keep st.1 ((code >>> (3 * (x + 1))) % 8)
        (result.1, st.2 + result.2)) =
      (fun (st : Nat × Nat) (x : Nat) =>
        let result := move keep st.1 (((code / 8) >>> (3 * x)) % 8)
        (result.1, st.2 + result.2)) := by
    funext st x
    rw [shift_three_succ]
  rw [hf]
  have hacc := foldl_acc
    (fun m x => move keep m (((code / 8) >>> (3 * x)) % 8))
    (List.range n) (move keep mode (code % 8)).1 (0 + (move keep mode (code % 8)).2)
  simpa using hacc

lemma move_snd_le_two (keep : Bool) (mode letter : Nat) :
    (move keep mode letter).2 ≤ 2 := by
  unfold move
  dsimp only
  cases letter.testBit 2 <;>
    cases (((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1) || ((mode == 3) && letter.testBit 0)) <;>
    decide

lemma gainFrom_le_two_mul (keep : Bool) (n mode code : Nat) :
    gainFrom keep n mode code ≤ 2 * n := by
  induction n generalizing mode code with
  | zero => simp [gainFrom]
  | succ n ih =>
    rw [gainFrom_succ]
    have h1 := move_snd_le_two keep mode (code % 8)
    have h2 := ih (move keep mode (code % 8)).1 (code / 8)
    omega

lemma gain_le_two_mul (keep : Bool) (n code : Nat) :
    gain keep n code ≤ 2 * n :=
  gainFrom_le_two_mul keep n 0 code

lemma sum_range_eight_pow_succ {M : Type*} [AddCommMonoid M] (n : Nat) (f : Nat → M) :
    ∑ w ∈ Finset.range (8 ^ (n + 1)), f w =
    ∑ l ∈ Finset.range 8, ∑ r ∈ Finset.range (8 ^ n), f (l + 8 * r) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => p.1 + 8 * p.2) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
    rw [pow_succ']
    omega
  · intro p1 hp1 p2 hp2 heq
    simp only [Finset.mem_product, Finset.mem_range] at hp1 hp2
    ext <;> omega
  · intro w hw
    simp only [Finset.mem_range] at hw
    refine ⟨(w % 8, w / 8), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      constructor
      · omega
      · rw [pow_succ'] at hw
        omega
    · omega
  · intro p _
    rfl

lemma sum_range_eight {M : Type*} [AddCommMonoid M] (f : Nat → M) :
    ∑ l ∈ Finset.range 8, f l =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp [Finset.sum_range_succ, add_assoc]

noncomputable def W (keep : Bool) (n mode : Nat) : Polynomial Int :=
  ∑ w ∈ Finset.range (8 ^ n), (X : Polynomial Int) ^ gainFrom keep n mode w

lemma W_zero (keep : Bool) (mode : Nat) : W keep 0 mode = 1 := by
  simp [W, gainFrom]

lemma W_succ (keep : Bool) (n mode : Nat) :
    W keep (n + 1) mode =
    ∑ l ∈ Finset.range 8,
      (X : Polynomial Int) ^ (move keep mode l).2 *
      W keep n (move keep mode l).1 := by
  unfold W
  rw [sum_range_eight_pow_succ]
  refine Finset.sum_congr rfl ?_
  intro l hl
  rw [Finset.mem_range] at hl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _
  rw [gainFrom_succ]
  have hmod : (l + 8 * r) % 8 = l := by omega
  have hdiv : (l + 8 * r) / 8 = r := by omega
  rw [hmod, hdiv, pow_add]

lemma W_mode3_eq_mode2 (keep : Bool) (n : Nat) :
    W keep n 3 = W keep n 2 := by
  induction n with
  | zero => rw [W_zero, W_zero]
  | succ n ih =>
    rw [W_succ, W_succ, sum_range_eight, sum_range_eight]
    cases keep
    · simp only [
        show move false 3 0 = (1, 0) by decide,
        show move false 3 1 = (2, 0) by decide,
        show move false 3 2 = (1, 0) by decide,
        show move false 3 3 = (2, 0) by decide,
        show move false 3 4 = (1, 1) by decide,
        show move false 3 5 = (0, 2) by decide,
        show move false 3 6 = (1, 1) by decide,
        show move false 3 7 = (0, 2) by decide,
        show move false 2 0 = (1, 0) by decide,
        show move false 2 1 = (1, 0) by decide,
        show move false 2 2 = (2, 0) by decide,
        show move false 2 3 = (2, 0) by decide,
        show move false 2 4 = (1, 1) by decide,
        show move false 2 5 = (1, 1) by decide,
        show move false 2 6 = (0, 2) by decide,
        show move false 2 7 = (0, 2) by decide]
      ring
    · simp only [
        show move true 3 0 = (3, 0) by decide,
        show move true 3 1 = (2, 0) by decide,
        show move true 3 2 = (3, 0) by decide,
        show move true 3 3 = (2, 0) by decide,
        show move true 3 4 = (1, 1) by decide,
        show move true 3 5 = (0, 2) by decide,
        show move true 3 6 = (1, 1) by decide,
        show move true 3 7 = (0, 2) by decide,
        show move true 2 0 = (3, 0) by decide,
        show move true 2 1 = (3, 0) by decide,
        show move true 2 2 = (2, 0) by decide,
        show move true 2 3 = (2, 0) by decide,
        show move true 2 4 = (1, 1) by decide,
        show move true 2 5 = (1, 1) by decide,
        show move true 2 6 = (0, 2) by decide,
        show move true 2 7 = (0, 2) by decide]
      rw [ih]
      ring

lemma Wt_succ_0 (n : Nat) :
    W true (n + 1) 0 = (4 * X + 4) * W true n 1 := by
  rw [W_succ, sum_range_eight]
  simp only [
    show move true 0 0 = (1, 0) by decide,
    show move true 0 1 = (1, 0) by decide,
    show move true 0 2 = (1, 0) by decide,
    show move true 0 3 = (1, 0) by decide,
    show move true 0 4 = (1, 1) by decide,
    show move true 0 5 = (1, 1) by decide,
    show move true 0 6 = (1, 1) by decide,
    show move true 0 7 = (1, 1) by decide]
  ring

lemma Wt_succ_1 (n : Nat) :
    W true (n + 1) 1 =
    X ^ 2 * W true n 0 + (3 * X + 2) * W true n 1 + 2 * W true n 2 := by
  rw [W_succ, sum_range_eight]
  simp only [
    show move true 1 0 = (3, 0) by decide,
    show move true 1 1 = (1, 0) by decide,
    show move true 1 2 = (1, 0) by decide,
    show move true 1 3 = (2, 0) by decide,
    show move true 1 4 = (1, 1) by decide,
    show move true 1 5 = (1, 1) by decide,
    show move true 1 6 = (1, 1) by decide,
    show move true 1 7 = (0, 2) by decide]
  rw [W_mode3_eq_mode2]
  ring

lemma Wt_succ_2 (n : Nat) :
    W true (n + 1) 2 =
    2 * X ^ 2 * W true n 0 + 2 * X * W true n 1 + 4 * W true n 2 := by
  rw [W_succ, sum_range_eight]
  simp only [
    show move true 2 0 = (3, 0) by decide,
    show move true 2 1 = (3, 0) by decide,
    show move true 2 2 = (2, 0) by decide,
    show move true 2 3 = (2, 0) by decide,
    show move true 2 4 = (1, 1) by decide,
    show move true 2 5 = (1, 1) by decide,
    show move true 2 6 = (0, 2) by decide,
    show move true 2 7 = (0, 2) by decide]
  rw [W_mode3_eq_mode2]
  ring

lemma Wf_succ_0 (n : Nat) :
    W false (n + 1) 0 = (4 * X + 4) * W false n 1 := by
  rw [W_succ, sum_range_eight]
  simp only [
    show move false 0 0 = (1, 0) by decide,
    show move false 0 1 = (1, 0) by decide,
    show move false 0 2 = (1, 0) by decide,
    show move false 0 3 = (1, 0) by decide,
    show move false 0 4 = (1, 1) by decide,
    show move false 0 5 = (1, 1) by decide,
    show move false 0 6 = (1, 1) by decide,
    show move false 0 7 = (1, 1) by decide]
  ring

lemma Wf_succ_1 (n : Nat) :
    W false (n + 1) 1 =
    X ^ 2 * W false n 0 + (3 * X + 3) * W false n 1 + W false n 2 := by
  rw [W_succ, sum_range_eight]
  simp only [
    show move false 1 0 = (1, 0) by decide,
    show move false 1 1 = (1, 0) by decide,
    show move false 1 2 = (1, 0) by decide,
    show move false 1 3 = (2, 0) by decide,
    show move false 1 4 = (1, 1) by decide,
    show move false 1 5 = (1, 1) by decide,
    show move false 1 6 = (1, 1) by decide,
    show move false 1 7 = (0, 2) by decide]
  ring

lemma Wf_succ_2 (n : Nat) :
    W false (n + 1) 2 =
    2 * X ^ 2 * W false n 0 + (2 * X + 2) * W false n 1 + 2 * W false n 2 := by
  rw [W_succ, sum_range_eight]
  simp only [
    show move false 2 0 = (1, 0) by decide,
    show move false 2 1 = (1, 0) by decide,
    show move false 2 2 = (2, 0) by decide,
    show move false 2 3 = (2, 0) by decide,
    show move false 2 4 = (1, 1) by decide,
    show move false 2 5 = (1, 1) by decide,
    show move false 2 6 = (0, 2) by decide,
    show move false 2 7 = (0, 2) by decide]
  ring

noncomputable def A1 : Polynomial Int := 3 * X + 6
noncomputable def A2 : Polynomial Int := 4 * X ^ 3 + 4 * X ^ 2 - 8 * X - 8
noncomputable def B1 : Polynomial Int := 3 * X + 5
noncomputable def B2 : Polynomial Int := 4 * X ^ 3 + 4 * X ^ 2 - 4 * X - 4

noncomputable def G (n : Nat) : Polynomial Int := W true n 0
noncomputable def F (n : Nat) : Polynomial Int := W false n 0

lemma G_zero : G 0 = 1 := W_zero true 0

lemma G_one : G 1 = 4 * X + 4 := by
  unfold G
  rw [Wt_succ_0, W_zero]
  ring

lemma G_two : G 2 = 4 * X ^ 3 + 16 * X ^ 2 + 28 * X + 16 := by
  unfold G
  rw [Wt_succ_0, Wt_succ_1, W_zero, W_zero, W_zero]
  ring

lemma F_zero : F 0 = 1 := W_zero false 0

lemma F_one : F 1 = 4 * X + 4 := by
  unfold F
  rw [Wf_succ_0, W_zero]
  ring

lemma F_two : F 2 = 4 * X ^ 3 + 16 * X ^ 2 + 28 * X + 16 := by
  unfold F
  rw [Wf_succ_0, Wf_succ_1, W_zero, W_zero, W_zero]
  ring

lemma G_rec (n : Nat) : G (n + 2) = A1 * G (n + 1) + A2 * G n := by
  cases n with
  | zero =>
    rw [G_two, G_one, G_zero]
    unfold A1 A2
    ring
  | succ n =>
    unfold G A1 A2
    rw [Wt_succ_0 (n + 2), Wt_succ_1 (n + 1), Wt_succ_0 n, Wt_succ_1 n, Wt_succ_2 n]
    rw [Wt_succ_0 (n + 1), Wt_succ_1 n]
    ring

lemma F_rec (n : Nat) : F (n + 2) = B1 * F (n + 1) + B2 * F n := by
  cases n with
  | zero =>
    rw [F_two, F_one, F_zero]
    unfold B1 B2
    ring
  | succ n =>
    unfold F B1 B2
    rw [Wf_succ_0 (n + 2), Wf_succ_1 (n + 1), Wf_succ_0 n, Wf_succ_1 n, Wf_succ_2 n]
    rw [Wf_succ_0 (n + 1), Wf_succ_1 n]
    ring

lemma G_three_sub_F_three : G 3 - F 3 = 4 * X * (X ^ 2 - 1) := by
  rw [G_rec 1, F_rec 1, G_two, G_one, F_two, F_one]
  unfold A1 A2 B1 B2
  ring

noncomputable def PU : Nat → Polynomial Nat × Polynomial Nat
  | 0 => (1, 1)
  | 1 => (3 * X + 2, 3 * X + 6)
  | n + 2 =>
    let p1 := (PU (n + 1)).1
    let u1 := (PU (n + 1)).2
    let u0 := (PU n).2
    let p2 := (3 * X + 2) * p1 + 4 * (X + X ^ 2 + X ^ 3) * u0
    (p2, 4 * u1 + p2)

noncomputable def P (n : Nat) : Polynomial Nat := (PU n).1
noncomputable def U (n : Nat) : Polynomial Nat := (PU n).2

noncomputable def RV : Nat → Polynomial Nat × Polynomial Nat
  | 0 => (1, 1)
  | 1 => (3 * X + 3, 3 * X + 5)
  | n + 2 =>
    let r1 := (RV (n + 1)).1
    let v1 := (RV (n + 1)).2
    let v0 := (RV n).2
    let r2 := (3 * X + 3) * r1 + (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3) * v0
    (r2, 2 * v1 + r2)

noncomputable def R (n : Nat) : Polynomial Nat := (RV n).1
noncomputable def V (n : Nat) : Polynomial Nat := (RV n).2

lemma P_zero : P 0 = 1 := rfl
lemma U_zero : U 0 = 1 := rfl
lemma P_one : P 1 = 3 * X + 2 := rfl
lemma U_one : U 1 = 3 * X + 6 := rfl
lemma R_zero : R 0 = 1 := rfl
lemma V_zero : V 0 = 1 := rfl
lemma R_one : R 1 = 3 * X + 3 := rfl
lemma V_one : V 1 = 3 * X + 5 := rfl

lemma P_succ_succ (n : Nat) :
    P (n + 2) = (3 * X + 2) * P (n + 1) + 4 * (X + X ^ 2 + X ^ 3) * U n := rfl

lemma U_succ (n : Nat) : U (n + 1) = 4 * U n + P (n + 1) := by
  cases n with
  | zero =>
    rw [U_one, U_zero, P_one]
    ring
  | succ n => rfl

lemma R_succ_succ (n : Nat) :
    R (n + 2) = (3 * X + 3) * R (n + 1) + (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3) * V n := rfl

lemma V_succ (n : Nat) : V (n + 1) = 2 * V n + R (n + 1) := by
  cases n with
  | zero =>
    rw [V_one, V_zero, R_one]
    ring
  | succ n => rfl

noncomputable def toZ (p : Polynomial Nat) : Polynomial Int :=
  p.map (Nat.castRingHom Int)

lemma toZ_zero : toZ 0 = 0 := by simp [toZ]
lemma toZ_one : toZ 1 = 1 := by simp [toZ]
lemma toZ_X : toZ X = X := by simp [toZ]
lemma toZ_add (p q : Polynomial Nat) : toZ (p + q) = toZ p + toZ q := by simp [toZ]
lemma toZ_mul (p q : Polynomial Nat) : toZ (p * q) = toZ p * toZ q := by simp [toZ]
lemma toZ_pow (p : Polynomial Nat) (k : Nat) : toZ (p ^ k) = toZ p ^ k := by simp [toZ]
lemma toZ_ofNat (k : Nat) : toZ (k : Polynomial Nat) = (k : Polynomial Int) := by
  simp [toZ]

lemma toZ_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial Nat) :
    toZ (∑ i ∈ s, f i) = ∑ i ∈ s, toZ (f i) := by
  simp [toZ, Polynomial.map_sum]

lemma toZ_coeff (p : Polynomial Nat) (k : Nat) :
    (toZ p).coeff k = (p.coeff k : Int) := by
  simp [toZ, Polynomial.coeff_map]

lemma toZ_U_zero : toZ (U 0) = 1 := by rw [U_zero, toZ_one]
lemma toZ_U_one : toZ (U 1) = A1 := by
  rw [U_one]
  unfold A1
  simp [toZ]

lemma toZ_V_zero : toZ (V 0) = 1 := by rw [V_zero, toZ_one]
lemma toZ_V_one : toZ (V 1) = B1 := by
  rw [V_one]
  unfold B1
  simp [toZ]

lemma U_rec (n : Nat) : toZ (U (n + 2)) = A1 * toZ (U (n + 1)) + A2 * toZ (U n) := by
  have h1 : toZ (U (n + 1)) = 4 * toZ (U n) + toZ (P (n + 1)) := by
    have := congrArg toZ (U_succ n)
    simpa [toZ, Polynomial.map_add, Polynomial.map_mul] using this
  have h2 : toZ (U (n + 2)) = 4 * toZ (U (n + 1)) + toZ (P (n + 2)) := by
    have := congrArg toZ (U_succ (n + 1))
    simpa [toZ, Polynomial.map_add, Polynomial.map_mul] using this
  have h3 :
      toZ (P (n + 2)) =
      (3 * X + 2) * toZ (P (n + 1)) + 4 * (X + X ^ 2 + X ^ 3) * toZ (U n) := by
    have := congrArg toZ (P_succ_succ n)
    simpa [toZ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] using this
  have hp : toZ (P (n + 1)) = toZ (U (n + 1)) - 4 * toZ (U n) := by
    calc
      toZ (P (n + 1)) = (4 * toZ (U n) + toZ (P (n + 1))) - 4 * toZ (U n) := by ring
      _ = toZ (U (n + 1)) - 4 * toZ (U n) := by rw [← h1]
  rw [h2, h3, hp]
  unfold A1 A2
  ring

lemma V_rec (n : Nat) : toZ (V (n + 2)) = B1 * toZ (V (n + 1)) + B2 * toZ (V n) := by
  have h1 : toZ (V (n + 1)) = 2 * toZ (V n) + toZ (R (n + 1)) := by
    have := congrArg toZ (V_succ n)
    simpa [toZ, Polynomial.map_add, Polynomial.map_mul] using this
  have h2 : toZ (V (n + 2)) = 2 * toZ (V (n + 1)) + toZ (R (n + 2)) := by
    have := congrArg toZ (V_succ (n + 1))
    simpa [toZ, Polynomial.map_add, Polynomial.map_mul] using this
  have h3 :
      toZ (R (n + 2)) =
      (3 * X + 3) * toZ (R (n + 1)) +
      (2 + 2 * X + 4 * X ^ 2 + 4 * X ^ 3) * toZ (V n) := by
    have := congrArg toZ (R_succ_succ n)
    simpa [toZ, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow] using this
  have hr : toZ (R (n + 1)) = toZ (V (n + 1)) - 2 * toZ (V n) := by
    calc
      toZ (R (n + 1)) = (2 * toZ (V n) + toZ (R (n + 1))) - 2 * toZ (V n) := by ring
      _ = toZ (V (n + 1)) - 2 * toZ (V n) := by rw [← h1]
  rw [h2, h3, hr]
  unfold B1 B2
  ring

noncomputable def Q (n : Nat) : Polynomial Nat :=
  if n < 3 then 0 else 4 * X * ∑ j ∈ Finset.range (n - 2), U j * V (n - 3 - j)

noncomputable def K (n : Nat) : Polynomial Int :=
  ∑ j ∈ Finset.range (n + 1), toZ (U j) * toZ (V (n - j))

lemma toZ_Q_lt (n : Nat) (hn : n < 3) : toZ (Q n) = 0 := by
  simp [Q, hn, toZ_zero]

lemma toZ_Q_add_three (n : Nat) : toZ (Q (n + 3)) = 4 * X * K n := by
  have hnot : ¬ (n + 3 < 3) := by omega
  have hsub1 : n + 3 - 2 = n + 1 := by omega
  unfold Q K
  simp only [hnot, ↓reduceIte, hsub1, toZ_mul, toZ_X, toZ_sum]
  have h4 : toZ (4 : Polynomial Nat) = (4 : Polynomial Int) := by simp [toZ]
  rw [h4]
  congr 1

lemma K_zero : K 0 = 1 := by
  simp [K, toZ_U_zero, toZ_V_zero]

lemma K_one : K 1 = B1 + A1 := by
  unfold K
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp [toZ_U_zero, toZ_U_one, toZ_V_zero, toZ_V_one]

lemma K_rec_V (n : Nat) : K (n + 2) - B1 * K (n + 1) - B2 * K n = toZ (U (n + 2)) := by
  unfold K
  rw [Finset.sum_range_succ (n := n + 2), Finset.sum_range_succ (n := n + 1)]
  rw [Finset.sum_range_succ (n := n + 1)]
  have h00 : n + 2 - (n + 2) = 0 := by omega
  have h10 : n + 2 - (n + 1) = 1 := by omega
  have h11 : n + 1 - (n + 1) = 0 := by omega
  rw [h00, h10, h11, toZ_V_zero, toZ_V_one]
  have hsum :
      ∑ j ∈ Finset.range (n + 1), toZ (U j) * toZ (V (n + 2 - j)) =
      B1 * ∑ j ∈ Finset.range (n + 1), toZ (U j) * toZ (V (n + 1 - j)) +
      B2 * ∑ j ∈ Finset.range (n + 1), toZ (U j) * toZ (V (n - j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [Finset.mem_range] at hj
    have e2 : n + 2 - j = (n - j) + 2 := by omega
    have e1 : n + 1 - j = (n - j) + 1 := by omega
    rw [e2, e1, V_rec (n - j)]
    ring
  rw [hsum]
  ring

noncomputable def OpB (S : Nat → Polynomial Int) (n : Nat) : Polynomial Int :=
  S (n + 2) - B1 * S (n + 1) - B2 * S n

noncomputable def Op4 (S : Nat → Polynomial Int) (n : Nat) : Polynomial Int :=
  OpB S (n + 2) - A1 * OpB S (n + 1) - A2 * OpB S n

lemma OpB_toZ_Q_zero : OpB (fun m => toZ (Q m)) 0 = 0 := by
  unfold OpB
  dsimp only
  rw [toZ_Q_lt 2 (by omega), toZ_Q_lt 1 (by omega), toZ_Q_lt 0 (by omega)]
  ring

lemma OpB_toZ_Q_succ (k : Nat) :
    OpB (fun m => toZ (Q m)) (k + 1) = 4 * X * toZ (U k) := by
  cases k with
  | zero =>
    unfold OpB
    dsimp only
    rw [show 0 + 1 + 2 = 0 + 3 by omega, show 0 + 1 + 1 = 2 by omega, show 0 + 1 = 1 by omega]
    rw [toZ_Q_add_three 0, toZ_Q_lt 2 (by omega), toZ_Q_lt 1 (by omega), K_zero, toZ_U_zero]
    ring
  | succ k =>
    cases k with
    | zero =>
      unfold OpB
      dsimp only
      rw [show 0 + 1 + 1 + 2 = 1 + 3 by omega, show 0 + 1 + 1 + 1 = 0 + 3 by omega,
          show 0 + 1 + 1 = 2 by omega, show 0 + 1 = 1 by omega]
      rw [toZ_Q_add_three 1, toZ_Q_add_three 0, toZ_Q_lt 2 (by omega), K_one, K_zero, toZ_U_one]
      ring
    | succ k =>
      unfold OpB
      dsimp only
      rw [show k + 1 + 1 + 1 + 2 = (k + 2) + 3 by omega,
          show k + 1 + 1 + 1 + 1 = (k + 1) + 3 by omega,
          show k + 1 + 1 + 1 = k + 3 by omega,
          show k + 1 + 1 = k + 2 by omega]
      rw [toZ_Q_add_three (k + 2), toZ_Q_add_three (k + 1), toZ_Q_add_three k]
      have h := K_rec_V k
      calc
        4 * X * K (k + 2) - B1 * (4 * X * K (k + 1)) - B2 * (4 * X * K k)
          = 4 * X * (K (k + 2) - B1 * K (k + 1) - B2 * K k) := by ring
        _ = 4 * X * toZ (U (k + 2)) := by rw [h]

lemma Op4_toZ_Q (n : Nat) : Op4 (fun m => toZ (Q m)) n = 0 := by
  cases n with
  | zero =>
    unfold Op4
    rw [OpB_toZ_Q_succ 1, OpB_toZ_Q_succ 0, OpB_toZ_Q_zero, toZ_U_one, toZ_U_zero]
    ring
  | succ k =>
    unfold Op4
    rw [OpB_toZ_Q_succ (k + 2), OpB_toZ_Q_succ (k + 1), OpB_toZ_Q_succ k, U_rec k]
    ring

lemma Op4_G (n : Nat) : Op4 G n = 0 := by
  unfold Op4 OpB
  rw [G_rec (n + 2), G_rec (n + 1), G_rec n]
  ring

lemma Op4_F (n : Nat) : Op4 F n = 0 := by
  unfold Op4 OpB
  rw [F_rec (n + 2), F_rec (n + 1), F_rec n]
  ring

lemma Op4_sub (S T : Nat → Polynomial Int) (n : Nat) :
    Op4 (fun m => S m - T m) n = Op4 S n - Op4 T n := by
  unfold Op4 OpB
  ring

lemma Op4_mul_const (c : Polynomial Int) (S : Nat → Polynomial Int) (n : Nat) :
    Op4 (fun m => c * S m) n = c * Op4 S n := by
  unfold Op4 OpB
  ring

lemma diff_eq_Q (n : Nat) : G n - F n = (X ^ 2 - 1) * toZ (Q n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => rw [G_zero, F_zero, toZ_Q_lt 0 (by omega)]; ring
    | 1 => rw [G_one, F_one, toZ_Q_lt 1 (by omega)]; ring
    | 2 => rw [G_two, F_two, toZ_Q_lt 2 (by omega)]; ring
    | 3 =>
      rw [G_three_sub_F_three, toZ_Q_add_three 0, K_zero]
      ring
    | m + 4 =>
      have h0 := ih m (by omega)
      have h1 := ih (m + 1) (by omega)
      have h2 := ih (m + 2) (by omega)
      have h3 := ih (m + 3) (by omega)
      have hL : Op4 (fun k => G k - F k) m = 0 := by
        rw [Op4_sub, Op4_G, Op4_F, sub_self]
      have hR : Op4 (fun k => (X ^ 2 - 1) * toZ (Q k)) m = 0 := by
        rw [Op4_mul_const, Op4_toZ_Q, mul_zero]
      have hEq : Op4 (fun k => G k - F k) m = Op4 (fun k => (X ^ 2 - 1) * toZ (Q k)) m := by
        rw [hL, hR]
      unfold Op4 OpB at hEq
      dsimp only at hEq
      rw [show m + 2 + 2 = m + 4 by omega, show m + 2 + 1 = m + 3 by omega,
          show m + 1 + 2 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega] at hEq
      rw [h0, h1, h2, h3] at hEq
      have hSub :
          ((G (m + 4) - F (m + 4)) - (X ^ 2 - 1) * toZ (Q (m + 4))) =
          ((G (m + 4) - F (m + 4) - B1 * ((X ^ 2 - 1) * toZ (Q (m + 3))) -
            B2 * ((X ^ 2 - 1) * toZ (Q (m + 2)))) -
            A1 * ((X ^ 2 - 1) * toZ (Q (m + 3)) - B1 * ((X ^ 2 - 1) * toZ (Q (m + 2))) -
              B2 * ((X ^ 2 - 1) * toZ (Q (m + 1)))) -
            A2 * ((X ^ 2 - 1) * toZ (Q (m + 2)) - B1 * ((X ^ 2 - 1) * toZ (Q (m + 1))) -
              B2 * ((X ^ 2 - 1) * toZ (Q m)))) -
          (((X ^ 2 - 1) * toZ (Q (m + 4)) - B1 * ((X ^ 2 - 1) * toZ (Q (m + 3))) -
            B2 * ((X ^ 2 - 1) * toZ (Q (m + 2)))) -
            A1 * ((X ^ 2 - 1) * toZ (Q (m + 3)) - B1 * ((X ^ 2 - 1) * toZ (Q (m + 2))) -
              B2 * ((X ^ 2 - 1) * toZ (Q (m + 1)))) -
            A2 * ((X ^ 2 - 1) * toZ (Q (m + 2)) - B1 * ((X ^ 2 - 1) * toZ (Q (m + 1))) -
              B2 * ((X ^ 2 - 1) * toZ (Q m)))) := by ring
      rw [hEq, sub_self] at hSub
      exact sub_eq_zero.mp hSub

lemma coeff_X_mul_eq_zero {p : Polynomial Nat} {d k : Nat}
    (hp : ∀ m, d < m → p.coeff m = 0) (hk : d + 1 < k) :
    (X * p).coeff k = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [Polynomial.coeff_X_mul]
    exact hp k (by omega)

lemma coeff_X_pow_mul_eq_zero {p : Polynomial Nat} {r d k : Nat}
    (hp : ∀ m, d < m → p.coeff m = 0) (hk : d + r < k) :
    (X ^ r * p).coeff k = 0 := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with h
  · exact hp (k - r) (by omega)
  · rfl

lemma PU_deg_pos (n : Nat) :
    (∀ k, 3 * n / 2 < k → (P n).coeff k = 0 ∧ (U n).coeff k = 0) ∧
    0 < (U n).coeff (3 * n / 2) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 =>
      constructor
      · intro k hk
        rw [P_zero, U_zero]
        simp [Polynomial.coeff_one, (show k ≠ 0 by omega)]
      · rw [U_zero]
        simp
    | 1 =>
      constructor
      · intro k hk
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [P_one, U_one]
        have hk0 : k' ≠ 0 := by omega
        constructor
        · simp [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
            Polynomial.coeff_ofNat_succ, hk0]
        · simp [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
            Polynomial.coeff_ofNat_succ, hk0]
      · rw [U_one]
        simp [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
          Polynomial.coeff_ofNat_succ]
    | m + 2 =>
      have ih0 := ih m (by omega)
      have ih1 := ih (m + 1) (by omega)
      have hP0 : ∀ k, 3 * (m + 1) / 2 < k → (P (m + 1)).coeff k = 0 := fun k hk => (ih1.1 k hk).1
      have hU1 : ∀ k, 3 * (m + 1) / 2 < k → (U (m + 1)).coeff k = 0 := fun k hk => (ih1.1 k hk).2
      have hU0 : ∀ k, 3 * m / 2 < k → (U m).coeff k = 0 := fun k hk => (ih0.1 k hk).2
      have hP2_eq :
          P (m + 2) =
          3 * (X * P (m + 1)) + 2 * P (m + 1) +
          4 * (X ^ 1 * U m) + 4 * (X ^ 2 * U m) + 4 * (X ^ 3 * U m) := by
        rw [P_succ_succ]
        ring
      have hU2_eq : U (m + 2) = 4 * U (m + 1) + P (m + 2) := U_succ (m + 1)
      constructor
      · intro k hk
        have hp2 : (P (m + 2)).coeff k = 0 := by
          rw [hP2_eq]
          simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul]
          rw [coeff_X_mul_eq_zero hP0 (by omega),
              hP0 k (by omega),
              coeff_X_pow_mul_eq_zero hU0 (by omega),
              coeff_X_pow_mul_eq_zero hU0 (by omega),
              coeff_X_pow_mul_eq_zero hU0 (by omega)]
          simp
        refine ⟨hp2, ?_⟩
        rw [hU2_eq, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, hU1 k (by omega), hp2]
        simp
      · have hd : 3 * (m + 2) / 2 = 3 * m / 2 + 3 := by omega
        rw [hd, hU2_eq, hP2_eq]
        simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul]
        have hpos : 0 < (X ^ 3 * U m).coeff (3 * m / 2 + 3) := by
          rw [Polynomial.coeff_X_pow_mul]
          exact ih0.2
        omega

lemma RV_deg_pos (n : Nat) :
    (∀ k, 3 * n / 2 < k → (R n).coeff k = 0 ∧ (V n).coeff k = 0) ∧
    0 < (V n).coeff (3 * n / 2) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 =>
      constructor
      · intro k hk
        rw [R_zero, V_zero]
        simp [Polynomial.coeff_one, (show k ≠ 0 by omega)]
      · rw [V_zero]
        simp
    | 1 =>
      constructor
      · intro k hk
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [R_one, V_one]
        have hk0 : k' ≠ 0 := by omega
        constructor
        · simp [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
            Polynomial.coeff_ofNat_succ, hk0]
        · simp [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
            Polynomial.coeff_ofNat_succ, hk0]
      · rw [V_one]
        simp [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X,
          Polynomial.coeff_ofNat_succ]
    | m + 2 =>
      have ih0 := ih m (by omega)
      have ih1 := ih (m + 1) (by omega)
      have hR1 : ∀ k, 3 * (m + 1) / 2 < k → (R (m + 1)).coeff k = 0 := fun k hk => (ih1.1 k hk).1
      have hV1 : ∀ k, 3 * (m + 1) / 2 < k → (V (m + 1)).coeff k = 0 := fun k hk => (ih1.1 k hk).2
      have hV0 : ∀ k, 3 * m / 2 < k → (V m).coeff k = 0 := fun k hk => (ih0.1 k hk).2
      have hR2_eq :
          R (m + 2) =
          3 * (X * R (m + 1)) + 3 * R (m + 1) +
          2 * V m + 2 * (X ^ 1 * V m) + 4 * (X ^ 2 * V m) + 4 * (X ^ 3 * V m) := by
        rw [R_succ_succ]
        ring
      have hV2_eq : V (m + 2) = 2 * V (m + 1) + R (m + 2) := V_succ (m + 1)
      constructor
      · intro k hk
        have hr2 : (R (m + 2)).coeff k = 0 := by
          rw [hR2_eq]
          simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul]
          rw [coeff_X_mul_eq_zero hR1 (by omega),
              hR1 k (by omega),
              hV0 k (by omega),
              coeff_X_pow_mul_eq_zero hV0 (by omega),
              coeff_X_pow_mul_eq_zero hV0 (by omega),
              coeff_X_pow_mul_eq_zero hV0 (by omega)]
          simp
        refine ⟨hr2, ?_⟩
        rw [hV2_eq, Polynomial.coeff_add, Polynomial.coeff_ofNat_mul, hV1 k (by omega), hr2]
        simp
      · have hd : 3 * (m + 2) / 2 = 3 * m / 2 + 3 := by omega
        rw [hd, hV2_eq, hR2_eq]
        simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul]
        have hpos : 0 < (X ^ 3 * V m).coeff (3 * m / 2 + 3) := by
          rw [Polynomial.coeff_X_pow_mul]
          exact ih0.2
        omega

lemma coeff_finset_sum {R ι : Type*} [Semiring R] (s : Finset ι) (f : ι → Polynomial R) (m : Nat) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

lemma Q_coeff_eq_zero_of_lt_three {n : Nat} (hn : n < 3) (k : Nat) :
    (Q n).coeff k = 0 := by
  simp [Q, hn]

lemma Q_coeff_eq_zero_of_gt {n k : Nat} (hn : 3 ≤ n) (hk : 3 * (n - 1) / 2 - 2 < k) :
    (Q n).coeff k = 0 := by
  have hnot : ¬ (n < 3) := by omega
  unfold Q
  simp only [hnot, ↓reduceIte]
  have hmul : 4 * X * ∑ j ∈ Finset.range (n - 2), U j * V (n - 3 - j) =
      4 * (X * ∑ j ∈ Finset.range (n - 2), U j * V (n - 3 - j)) := by ring
  rw [hmul, Polynomial.coeff_ofNat_mul]
  have hinner :
      (X * ∑ j ∈ Finset.range (n - 2), U j * V (n - 3 - j)).coeff k = 0 := by
    refine coeff_X_mul_eq_zero (d := 3 * (n - 3) / 2) ?_ (by omega)
    intro m hm
    rw [coeff_finset_sum]
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Polynomial.coeff_mul]
    refine Finset.sum_eq_zero ?_
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    by_cases hx1 : 3 * j / 2 < x.1
    · rw [((PU_deg_pos j).1 x.1 hx1).2, zero_mul]
    · have hx2 : 3 * (n - 3 - j) / 2 < x.2 := by omega
      rw [((RV_deg_pos (n - 3 - j)).1 x.2 hx2).2, mul_zero]
  rw [hinner, mul_zero]

lemma Q_coeff_top_pos {n : Nat} (hn : 3 ≤ n) :
    0 < (Q n).coeff (3 * (n - 1) / 2 - 2) := by
  have hnot : ¬ (n < 3) := by omega
  unfold Q
  simp only [hnot, ↓reduceIte]
  have hmul : 4 * X * ∑ j ∈ Finset.range (n - 2), U j * V (n - 3 - j) =
      4 * (X * ∑ j ∈ Finset.range (n - 2), U j * V (n - 3 - j)) := by ring
  rw [hmul, Polynomial.coeff_ofNat_mul]
  have hd : 3 * (n - 1) / 2 - 2 = 3 * (n - 3) / 2 + 1 := by omega
  rw [hd, Polynomial.coeff_X_mul, coeff_finset_sum]
  have hmem : n - 3 ∈ Finset.range (n - 2) := by
    rw [Finset.mem_range]
    omega
  have hle :
      (U (n - 3) * V (n - 3 - (n - 3))).coeff (3 * (n - 3) / 2) ≤
      ∑ j ∈ Finset.range (n - 2), (U j * V (n - 3 - j)).coeff (3 * (n - 3) / 2) :=
    Finset.single_le_sum (f := fun j => (U j * V (n - 3 - j)).coeff (3 * (n - 3) / 2))
      (fun _ _ => Nat.zero_le _) hmem
  have hsub : n - 3 - (n - 3) = 0 := by omega
  rw [hsub, V_zero, mul_one] at hle
  have hpos := (PU_deg_pos (n - 3)).2
  omega

lemma Q_coeff_eq_zero_of_ge_two_mul (n k : Nat) (hk : 2 * n ≤ k) :
    (Q n).coeff k = 0 := by
  by_cases hn : n < 3
  · exact Q_coeff_eq_zero_of_lt_three hn k
  · exact Q_coeff_eq_zero_of_gt (by omega) (by omega)

def cnt (keep : Bool) (n m : Nat) : Nat :=
  ((Finset.range (8 ^ n)).filter (fun w => gain keep n w = m)).card

lemma cnt_eq_zero_of_gt (keep : Bool) (n m : Nat) (hm : 2 * n < m) :
    cnt keep n m = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro w _
  have h := gain_le_two_mul keep n w
  omega

lemma W_zero_coeff (keep : Bool) (n m : Nat) :
    (W keep n 0).coeff m = (cnt keep n m : Int) := by
  unfold W cnt gain
  rw [coeff_finset_sum]
  have h1 :
      ∑ w ∈ Finset.range (8 ^ n), ((X : Polynomial Int) ^ gainFrom keep n 0 w).coeff m =
      ∑ w ∈ Finset.range (8 ^ n), if gainFrom keep n 0 w = m then (1 : Int) else 0 := by
    refine Finset.sum_congr rfl ?_
    intro w _
    rw [Polynomial.coeff_X_pow]
    by_cases h : gainFrom keep n 0 w = m
    · simp [h]
    · have h' : m ≠ gainFrom keep n 0 w := fun he => h he.symm
      simp [h, h']
  rw [h1, ← Finset.sum_filter]
  simp

lemma cnt_diff (n m : Nat) :
    (cnt true n m : Int) - (cnt false n m : Int) =
    (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0) - ((Q n).coeff m : Int) := by
  have h := congrArg (fun p : Polynomial Int => p.coeff m) (diff_eq_Q n)
  unfold G F at h
  rw [Polynomial.coeff_sub, W_zero_coeff, W_zero_coeff] at h
  have hr : ((X ^ 2 - 1) * toZ (Q n)).coeff m =
      (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0) - ((Q n).coeff m : Int) := by
    have heq : (X ^ 2 - 1) * toZ (Q n) = X ^ 2 * toZ (Q n) - toZ (Q n) := by ring
    rw [heq, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul']
    simp only [toZ_coeff]
  rw [h, hr]

lemma parity_tail_sum_eq (n p k L : Nat) (hp : p < 2) :
    ∑ t ∈ Finset.Ico k (k + L),
      ((cnt true n (2 * t + p) : Int) - (cnt false n (2 * t + p) : Int)) =
    (if k = 0 then 0 else ((Q n).coeff (2 * k + p - 2) : Int)) -
    (if k + L = 0 then 0 else ((Q n).coeff (2 * (k + L) + p - 2) : Int)) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hadd : k + (L + 1) = (k + L) + 1 := by omega
    rw [hadd, Finset.sum_Ico_succ_top (by omega), ih, cnt_diff]
    have hidx : 2 * (k + L + 1) + p - 2 = 2 * (k + L) + p := by omega
    have hnz : k + L + 1 ≠ 0 := by omega
    simp only [hnz, ↓reduceIte, hidx]
    by_cases hkl : k + L = 0
    · have h2 : ¬ (2 ≤ 2 * (k + L) + p) := by omega
      simp only [h2, ↓reduceIte]
      simp only [hkl, ↓reduceIte]
      ring
    · have h2 : 2 ≤ 2 * (k + L) + p := by omega
      simp only [hkl, h2, ↓reduceIte]
      ring

lemma parity_tail_le (n p k : Nat) (hp : p < 2) (hk : k ≤ n + 2) :
    ∑ t ∈ Finset.Ico k (n + 2), cnt false n (2 * t + p) ≤
    ∑ t ∈ Finset.Ico k (n + 2), cnt true n (2 * t + p) := by
  have h := parity_tail_sum_eq n p k (n + 2 - k) hp
  have hkl : k + (n + 2 - k) = n + 2 := by omega
  rw [hkl] at h
  have hnz : n + 2 ≠ 0 := by omega
  simp only [hnz, ↓reduceIte] at h
  have hq0 : (Q n).coeff (2 * (n + 2) + p - 2) = 0 :=
    Q_coeff_eq_zero_of_ge_two_mul n _ (by omega)
  rw [hq0] at h
  have hnonneg : 0 ≤ (if k = 0 then (0 : Int) else ((Q n).coeff (2 * k + p - 2) : Int)) := by
    split_ifs <;> positivity
  rw [Finset.sum_sub_distrib] at h
  have hdiff :
      0 ≤ (∑ t ∈ Finset.Ico k (n + 2), (cnt true n (2 * t + p) : Int)) -
          (∑ t ∈ Finset.Ico k (n + 2), (cnt false n (2 * t + p) : Int)) := by
    rw [h]
    omega
  have hle :
      (∑ t ∈ Finset.Ico k (n + 2), (cnt false n (2 * t + p) : Int)) ≤
      (∑ t ∈ Finset.Ico k (n + 2), (cnt true n (2 * t + p) : Int)) := by omega
  exact_mod_cast hle

lemma parity_total_eq (n p : Nat) (hp : p < 2) :
    ∑ t ∈ Finset.Ico 0 (n + 2), cnt false n (2 * t + p) =
    ∑ t ∈ Finset.Ico 0 (n + 2), cnt true n (2 * t + p) := by
  have h := parity_tail_sum_eq n p 0 (n + 2) hp
  simp only [zero_add, ite_true] at h
  have hnz : n + 2 ≠ 0 := by omega
  simp only [hnz, ↓reduceIte] at h
  have hq0 : (Q n).coeff (2 * (n + 2) + p - 2) = 0 :=
    Q_coeff_eq_zero_of_ge_two_mul n _ (by omega)
  rw [hq0] at h
  rw [Finset.sum_sub_distrib] at h
  have heq :
      (∑ t ∈ Finset.Ico 0 (n + 2), (cnt false n (2 * t + p) : Int)) =
      (∑ t ∈ Finset.Ico 0 (n + 2), (cnt true n (2 * t + p) : Int)) := by omega
  exact_mod_cast heq

def paritySet (keep : Bool) (n p : Nat) : Finset (Fin (8 ^ n)) :=
  Finset.univ.filter (fun w => gain keep n w.val % 2 = p)

lemma card_parity_ge (keep : Bool) (n p k : Nat) (hp : p < 2) (hk : k ≤ n + 2) :
    ((paritySet keep n p).filter (fun w => 2 * k + p ≤ gain keep n w.val)).card =
    ∑ t ∈ Finset.Ico k (n + 2), cnt keep n (2 * t + p) := by
  have hfin :
      ((paritySet keep n p).filter (fun w => 2 * k + p ≤ gain keep n w.val)).card =
      ((Finset.range (8 ^ n)).filter
        (fun w => gain keep n w % 2 = p ∧ 2 * k + p ≤ gain keep n w)).card := by
    refine Finset.card_bij (fun w _ => w.val) ?_ ?_ ?_
    · intro w hw
      simp only [paritySet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hw ⊢
      exact ⟨w.isLt, hw.1, hw.2⟩
    · intro w1 _ w2 _ h
      exact Fin.ext h
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_range] at hw
      refine ⟨⟨w, hw.1⟩, ?_, rfl⟩
      simp [paritySet, hw.2.1, hw.2.2]
  rw [hfin]
  have hpart :
      ((Finset.range (8 ^ n)).filter
        (fun w => gain keep n w % 2 = p ∧ 2 * k + p ≤ gain keep n w)).card =
      ∑ t ∈ Finset.Ico k (n + 2),
        (((Finset.range (8 ^ n)).filter
          (fun w => gain keep n w % 2 = p ∧ 2 * k + p ≤ gain keep n w)).filter
          (fun w => gain keep n w / 2 = t)).card := by
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hw
    rcases hw with ⟨_, hmod, hge⟩
    rw [Finset.mem_coe, Finset.mem_Ico]
    dsimp only
    have hle := gain_le_two_mul keep n w
    omega
  rw [hpart]
  refine Finset.sum_congr rfl ?_
  intro t ht
  rw [Finset.mem_Ico] at ht
  unfold cnt
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨hw, hmod, _⟩, hdiv⟩
    exact ⟨hw, by omega⟩
  · rintro ⟨hw, heq⟩
    exact ⟨⟨hw, by omega, by omega⟩, by omega⟩

lemma card_paritySet_eq (n p : Nat) (hp : p < 2) :
    (paritySet false n p).card = (paritySet true n p).card := by
  have hF := card_parity_ge false n p 0 hp (by omega)
  have hT := card_parity_ge true n p 0 hp (by omega)
  have hf1 : (paritySet false n p).filter (fun w => 2 * 0 + p ≤ gain false n w.val) =
      paritySet false n p := by
    ext w
    simp only [paritySet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, by omega⟩
  have ht1 : (paritySet true n p).filter (fun w => 2 * 0 + p ≤ gain true n w.val) =
      paritySet true n p := by
    ext w
    simp only [paritySet, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, by omega⟩
  rw [hf1] at hF
  rw [ht1] at hT
  rw [hF, hT]
  exact parity_total_eq n p hp

def keyFn (keep : Bool) (n : Nat) (w : Fin (8 ^ n)) : Nat :=
  gain keep n w.val * 8 ^ n + w.val

lemma keyFn_inj (keep : Bool) (n : Nat) : Function.Injective (keyFn keep n) := by
  intro w1 w2 h
  unfold keyFn at h
  have hg : gain keep n w1.val = gain keep n w2.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : (gain keep n w1.val + 1) * 8 ^ n ≤ gain keep n w2.val * 8 ^ n :=
        Nat.mul_le_mul_right (8 ^ n) hlt
      have h2 : gain keep n w1.val * 8 ^ n + w1.val < (gain keep n w1.val + 1) * 8 ^ n := by
        rw [Nat.succ_mul]
        exact Nat.add_lt_add_left w1.isLt _
      omega
    · have h1 : (gain keep n w2.val + 1) * 8 ^ n ≤ gain keep n w1.val * 8 ^ n :=
        Nat.mul_le_mul_right (8 ^ n) hgt
      have h2 : gain keep n w2.val * 8 ^ n + w2.val < (gain keep n w2.val + 1) * 8 ^ n := by
        rw [Nat.succ_mul]
        exact Nat.add_lt_add_left w2.isLt _
      omega
  rw [hg] at h
  exact Fin.ext (by omega)

lemma keyFn_le_imp_gain_le (keep : Bool) (n : Nat) (w1 w2 : Fin (8 ^ n))
    (h : keyFn keep n w1 ≤ keyFn keep n w2) :
    gain keep n w1.val ≤ gain keep n w2.val := by
  by_contra hlt
  push Not at hlt
  unfold keyFn at h
  have h1 : (gain keep n w2.val + 1) * 8 ^ n ≤ gain keep n w1.val * 8 ^ n :=
    Nat.mul_le_mul_right (8 ^ n) hlt
  have h2 : gain keep n w2.val * 8 ^ n + w2.val < (gain keep n w2.val + 1) * 8 ^ n := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left w2.isLt _
  omega

lemma gain_lt_imp_keyFn_lt (keep : Bool) (n : Nat) (w1 w2 : Fin (8 ^ n))
    (h : gain keep n w1.val < gain keep n w2.val) :
    keyFn keep n w1 < keyFn keep n w2 := by
  unfold keyFn
  have h1 : (gain keep n w1.val + 1) * 8 ^ n ≤ gain keep n w2.val * 8 ^ n :=
    Nat.mul_le_mul_right (8 ^ n) h
  have h2 : gain keep n w1.val * 8 ^ n + w1.val < (gain keep n w1.val + 1) * 8 ^ n := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left w1.isLt _
  omega

noncomputable def imageEquiv {α β : Type*} [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (s : Finset α) :
    {x // x ∈ s} ≃ {y // y ∈ s.image f} :=
  Equiv.ofBijective
    (fun x => ⟨f x.val, Finset.mem_image_of_mem f x.property⟩)
    ⟨fun x1 x2 h => Subtype.ext (hf (congrArg Subtype.val h)),
     fun y => by
       rcases Finset.mem_image.mp y.property with ⟨x, hx, hfx⟩
       exact ⟨⟨x, hx⟩, Subtype.ext hfx⟩⟩

lemma card_fin_ge (c i : Nat) (hi : i ≤ c) :
    ((Finset.univ : Finset (Fin c)).filter (fun j : Fin c => i ≤ j.val)).card = c - i := by
  have hbij :
      ((Finset.univ : Finset (Fin c)).filter (fun j : Fin c => i ≤ j.val)).card =
      (Finset.Ico i c).card := by
    refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact Finset.mem_Ico.mpr ⟨hj, j.isLt⟩
    · intro j1 _ j2 _ h
      exact Fin.ext h
    · intro x hx
      rw [Finset.mem_Ico] at hx
      refine ⟨⟨x, hx.2⟩, ?_, rfl⟩
      simp [hx.1]
  rw [hbij, Nat.card_Ico]

lemma parity_bijection (n p : Nat) (hp : p < 2) :
    ∃ e : {w : Fin (8 ^ n) // w ∈ paritySet false n p} ≃
          {w : Fin (8 ^ n) // w ∈ paritySet true n p},
      ∀ w, gain false n w.val.val ≤ gain true n (e w).val.val := by
  let sF := paritySet false n p
  let sT := paritySet true n p
  let tF := sF.image (keyFn false n)
  let tT := sT.image (keyFn true n)
  let c := sF.card
  have hcF : tF.card = c := Finset.card_image_of_injective sF (keyFn_inj false n)
  have hcT : tT.card = c := by
    rw [Finset.card_image_of_injective sT (keyFn_inj true n)]
    exact (card_paritySet_eq n p hp).symm
  let eqF : {w // w ∈ sF} ≃ {y // y ∈ tF} := imageEquiv (keyFn false n) (keyFn_inj false n) sF
  let eqT : {w // w ∈ sT} ≃ {y // y ∈ tT} := imageEquiv (keyFn true n) (keyFn_inj true n) sT
  let oF : Fin c ≃o {y // y ∈ tF} := tF.orderIsoOfFin hcF
  let oT : Fin c ≃o {y // y ∈ tT} := tT.orderIsoOfFin hcT
  let e : {w // w ∈ sF} ≃ {w // w ∈ sT} :=
    eqF.trans (oF.symm.toEquiv.trans (oT.toEquiv.trans eqT.symm))
  refine ⟨e, ?_⟩
  intro w
  by_contra hlt
  push Not at hlt
  let i : Fin c := oF.symm (eqF w)
  have hiF : (oF i).val = keyFn false n w.val := by
    have h1 : oF i = eqF w := oF.apply_symm_apply (eqF w)
    exact congrArg Subtype.val h1
  have hiT : (oT i).val = keyFn true n (e w).val := by
    have h1 : eqT (e w) = oT i := by
      simp [e, i]
    exact (congrArg Subtype.val h1).symm
  let M := gain false n w.val.val
  have hMmod : M % 2 = p := by
    have hw := w.property
    simp only [sF, paritySet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact hw
  let k := M / 2
  have hM_eq : M = 2 * k + p := by omega
  have hk_le : k ≤ n + 2 := by
    have hle := gain_le_two_mul false n w.val.val
    omega
  have hcardF :
      c - i.val ≤ (sF.filter (fun u => M ≤ gain false n u.val)).card := by
    rw [← card_fin_ge c i.val (Nat.le_of_lt i.isLt)]
    refine Finset.card_le_card_of_injOn
      (fun j : Fin c => (eqF.symm (oF j)).val) ?_ ?_
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨(eqF.symm (oF j)).property, ?_⟩
      have hjle : i ≤ j := hj
      have hole : (oF i).val ≤ (oF j).val := oF.monotone hjle
      have hkeyj : keyFn false n (eqF.symm (oF j)).val = (oF j).val :=
        congrArg Subtype.val (eqF.apply_symm_apply (oF j))
      rw [hiF, ← hkeyj] at hole
      exact keyFn_le_imp_gain_le false n w.val (eqF.symm (oF j)).val hole
    · intro j1 _ j2 _ heq
      have hs : eqF.symm (oF j1) = eqF.symm (oF j2) := Subtype.ext heq
      exact oF.injective (eqF.symm.injective hs)
  have hcardT :
      (sT.filter (fun u => M ≤ gain true n u.val)).card ≤ c - (i.val + 1) := by
    rw [← card_fin_ge c (i.val + 1) i.isLt]
    refine Finset.card_le_card_of_injOn
      (fun u : Fin (8 ^ n) =>
        if hu : u ∈ sT then oT.symm (eqT ⟨u, hu⟩) else i) ?_ ?_
    · intro u hu
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      simp only [hu.1, ↓reduceDIte]
      have hgain : gain true n (e w).val.val < gain true n u.val := lt_of_lt_of_le hlt hu.2
      have hklt : keyFn true n (e w).val < keyFn true n u :=
        gain_lt_imp_keyFn_lt true n (e w).val u hgain
      have hlt_sub : oT i < eqT ⟨u, hu.1⟩ := by
        show (oT i).val < (eqT ⟨u, hu.1⟩).val
        rw [hiT]
        exact hklt
      have hilt : i < oT.symm (eqT ⟨u, hu.1⟩) := by
        rw [← oT.symm_apply_apply i]
        exact oT.symm.strictMono hlt_sub
      exact hilt
    · intro u1 hu1 u2 hu2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at hu1 hu2
      dsimp only at heq
      simp only [hu1.1, hu2.1, ↓reduceDIte] at heq
      have h1 := eqT.injective (oT.symm.injective heq)
      exact congrArg Subtype.val h1
  have htail :
      (sF.filter (fun u => M ≤ gain false n u.val)).card ≤
      (sT.filter (fun u => M ≤ gain true n u.val)).card := by
    rw [hM_eq, card_parity_ge false n p k hp hk_le, card_parity_ge true n p k hp hk_le]
    exact parity_tail_le n p k hp hk_le
  have hi_lt : i.val < c := i.isLt
  omega

def gluePerm {α : Type*} (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (e0 : {x // p x} ≃ {x // q x})
    (e1 : {x // ¬ p x} ≃ {x // ¬ q x}) : Equiv.Perm α where
  toFun x := if h : p x then (e0 ⟨x, h⟩).val else (e1 ⟨x, h⟩).val
  invFun y := if h : q y then (e0.symm ⟨y, h⟩).val else (e1.symm ⟨y, h⟩).val
  left_inv x := by
    by_cases h : p x
    · simp [h, (e0 ⟨x, h⟩).property]
    · simp [h, (e1 ⟨x, h⟩).property]
  right_inv y := by
    by_cases h : q y
    · simp [h, (e0.symm ⟨y, h⟩).property]
    · simp [h, (e1.symm ⟨y, h⟩).property]

lemma exists_parity_perm (n : Nat) :
    ∃ π : Equiv.Perm (Fin (8 ^ n)), ∀ w : Fin (8 ^ n),
      gain false n w.val ≤ gain true n (π w).val ∧
      gain false n w.val % 2 = gain true n (π w).val % 2 := by
  rcases parity_bijection n 0 (by omega) with ⟨e0, he0⟩
  rcases parity_bijection n 1 (by omega) with ⟨e1, he1⟩
  let pF : Fin (8 ^ n) → Prop := fun w => gain false n w.val % 2 = 0
  let pT : Fin (8 ^ n) → Prop := fun w => gain true n w.val % 2 = 0
  let isoF0 : {w // pF w} ≃ {w // w ∈ paritySet false n 0} :=
    Equiv.subtypeEquivRight (fun w => by simp [pF, paritySet])
  let isoT0 : {w // w ∈ paritySet true n 0} ≃ {w // pT w} :=
    Equiv.subtypeEquivRight (fun w => by simp [pT, paritySet])
  let isoF1 : {w // ¬ pF w} ≃ {w // w ∈ paritySet false n 1} :=
    Equiv.subtypeEquivRight (fun w => by simp [pF, paritySet])
  let isoT1 : {w // w ∈ paritySet true n 1} ≃ {w // ¬ pT w} :=
    Equiv.subtypeEquivRight (fun w => by simp [pT, paritySet])
  let f0 : {w // pF w} ≃ {w // pT w} := isoF0.trans (e0.trans isoT0)
  let f1 : {w // ¬ pF w} ≃ {w // ¬ pT w} := isoF1.trans (e1.trans isoT1)
  refine ⟨gluePerm pF pT f0 f1, ?_⟩
  intro w
  by_cases h : pF w
  · have hpi : gluePerm pF pT f0 f1 w = (f0 ⟨w, h⟩).val := by simp [gluePerm, h]
    rw [hpi]
    have hle := he0 (isoF0 ⟨w, h⟩)
    have hq : pT (f0 ⟨w, h⟩).val := (f0 ⟨w, h⟩).property
    refine ⟨hle, ?_⟩
    dsimp only [pF, pT] at h hq
    omega
  · have hpi : gluePerm pF pT f0 f1 w = (f1 ⟨w, h⟩).val := by simp [gluePerm, h]
    rw [hpi]
    have hle := he1 (isoF1 ⟨w, h⟩)
    have hq : ¬ pT (f1 ⟨w, h⟩).val := (f1 ⟨w, h⟩).property
    refine ⟨hle, ?_⟩
    dsimp only [pF, pT] at h hq
    omega

lemma list_range_map_sum (N : Nat) (f : Nat → Nat) :
    ((List.range N).map f).sum = ∑ w ∈ Finset.range N, f w := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

lemma price_eq_sum (keep : Bool) (n d : Nat) :
    price keep n d =
    ∑ m ∈ Finset.range (2 * n + 2), cnt keep n m * 2 ^ (2 * n - (m - d)) := by
  unfold price
  rw [list_range_map_sum]
  have hfib :
      ∑ w ∈ Finset.range (8 ^ n), 2 ^ (2 * n - (gain keep n w - d)) =
      ∑ m ∈ Finset.range (2 * n + 2),
        ∑ w ∈ (Finset.range (8 ^ n)).filter (fun w => gain keep n w = m),
          2 ^ (2 * n - (gain keep n w - d)) := by
    symm
    refine Finset.sum_fiberwise_of_maps_to ?_ _
    intro w _
    rw [Finset.mem_range]
    have hle := gain_le_two_mul keep n w
    omega
  rw [hfib]
  refine Finset.sum_congr rfl ?_
  intro m _
  have hconst :
      ∑ w ∈ (Finset.range (8 ^ n)).filter (fun w => gain keep n w = m),
        2 ^ (2 * n - (gain keep n w - d)) =
      ∑ _w ∈ (Finset.range (8 ^ n)).filter (fun w => gain keep n w = m),
        2 ^ (2 * n - (m - d)) := by
    refine Finset.sum_congr rfl ?_
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [hw.2]
  rw [hconst, Finset.sum_const, smul_eq_mul]
  rfl

def wgt (n d m : Nat) : Int :=
  (2 : Int) ^ (2 * n - (m - d))

lemma wgt_sub_nonneg (n d k : Nat) :
    0 ≤ wgt n d k - wgt n d (k + 2) := by
  have hle : 2 ^ (2 * n - (k + 2 - d)) ≤ 2 ^ (2 * n - (k - d)) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hleZ : (2 : Int) ^ (2 * n - (k + 2 - d)) ≤ (2 : Int) ^ (2 * n - (k - d)) := by
    exact_mod_cast hle
  unfold wgt
  omega

lemma sum_range_add_two {M : Type*} [AddCommMonoid M] (N : Nat) (f : Nat → M) :
    ∑ m ∈ Finset.range (N + 2), f m = f 0 + f 1 + ∑ k ∈ Finset.range N, f (k + 2) := by
  induction N with
  | zero => simp [Finset.sum_range_succ]
  | succ N ih =>
    rw [show N + 1 + 2 = (N + 2) + 1 by omega, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ac_rfl

lemma price_diff_eq (n d : Nat) :
    (price false n d : Int) - (price true n d : Int) =
    ∑ k ∈ Finset.range (2 * n),
      ((Q n).coeff k : Int) * (wgt n d k - wgt n d (k + 2)) := by
  rw [price_eq_sum false n d, price_eq_sum true n d]
  push_cast
  rw [← Finset.sum_sub_distrib]
  have h1 :
      ∑ m ∈ Finset.range (2 * n + 2),
        ((cnt false n m : Int) * wgt n d m - (cnt true n m : Int) * wgt n d m) =
      (∑ m ∈ Finset.range (2 * n + 2), ((Q n).coeff m : Int) * wgt n d m) -
      (∑ m ∈ Finset.range (2 * n + 2),
        (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0) * wgt n d m) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro m _
    have hc := cnt_diff n m
    have hcf :
        (cnt false n m : Int) - (cnt true n m : Int) =
        ((Q n).coeff m : Int) - (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0) := by
      omega
    calc
      (cnt false n m : Int) * wgt n d m - (cnt true n m : Int) * wgt n d m
        = ((cnt false n m : Int) - (cnt true n m : Int)) * wgt n d m := by ring
      _ = (((Q n).coeff m : Int) - (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0)) *
            wgt n d m := by rw [hcf]
      _ = ((Q n).coeff m : Int) * wgt n d m -
            (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0) * wgt n d m := by ring
  change ∑ m ∈ Finset.range (2 * n + 2),
      ((cnt false n m : Int) * wgt n d m - (cnt true n m : Int) * wgt n d m) = _
  rw [h1]
  have hS1 :
      ∑ m ∈ Finset.range (2 * n + 2), ((Q n).coeff m : Int) * wgt n d m =
      ∑ k ∈ Finset.range (2 * n), ((Q n).coeff k : Int) * wgt n d k := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [Q_coeff_eq_zero_of_ge_two_mul n (2 * n) (by omega),
        Q_coeff_eq_zero_of_ge_two_mul n (2 * n + 1) (by omega)]
    simp
  have hS2 :
      ∑ m ∈ Finset.range (2 * n + 2),
        (if 2 ≤ m then ((Q n).coeff (m - 2) : Int) else 0) * wgt n d m =
      ∑ k ∈ Finset.range (2 * n), ((Q n).coeff k : Int) * wgt n d (k + 2) := by
    rw [sum_range_add_two]
    simp only [show ¬ (2 ≤ 0) by omega, show ¬ (2 ≤ 1) by omega, ↓reduceIte, zero_mul, add_zero, zero_add]
    refine Finset.sum_congr rfl ?_
    intro k _
    have h2 : 2 ≤ k + 2 := by omega
    have hsub : k + 2 - 2 = k := by omega
    simp only [h2, ↓reduceIte, hsub]
  rw [hS1, hS2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

lemma price_comparison (n d : Nat) :
    price true n d ≤ price false n d ∧
    (price true n d < price false n d ↔ 3 ≤ n ∧ d < 3 * (n - 1) / 2) := by
  have hnonneg : ∀ k ∈ Finset.range (2 * n),
      0 ≤ ((Q n).coeff k : Int) * (wgt n d k - wgt n d (k + 2)) := by
    intro k _
    exact mul_nonneg (Int.natCast_nonneg _) (wgt_sub_nonneg n d k)
  have hdiff_nonneg : 0 ≤ (price false n d : Int) - (price true n d : Int) := by
    rw [price_diff_eq]
    exact Finset.sum_nonneg hnonneg
  constructor
  · omega
  · constructor
    · intro hlt
      by_contra hnot
      have hzero :
          ∑ k ∈ Finset.range (2 * n),
            ((Q n).coeff k : Int) * (wgt n d k - wgt n d (k + 2)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k _
        by_cases hn : n < 3
        · rw [Q_coeff_eq_zero_of_lt_three hn k]
          simp
        · have hn3 : 3 ≤ n := by omega
          have hd : 3 * (n - 1) / 2 ≤ d := by omega
          by_cases hk : 3 * (n - 1) / 2 - 2 < k
          · rw [Q_coeff_eq_zero_of_gt hn3 hk]
            simp
          · have hkd1 : k - d = 0 := by omega
            have hkd2 : k + 2 - d = 0 := by omega
            unfold wgt
            rw [hkd1, hkd2, sub_self, mul_zero]
      have hdiff := price_diff_eq n d
      rw [hzero] at hdiff
      omega
    · rintro ⟨hn3, hd⟩
      let D := 3 * (n - 1) / 2 - 2
      have hD_mem : D ∈ Finset.range (2 * n) := by
        rw [Finset.mem_range]
        omega
      have hQ_pos : (0 : Int) < ((Q n).coeff D : Int) := by
        exact_mod_cast Q_coeff_top_pos hn3
      have hwgt_pos : 0 < wgt n d D - wgt n d (D + 2) := by
        have hexp : 2 * n - (D + 2 - d) < 2 * n - (D - d) := by omega
        have hpow : 2 ^ (2 * n - (D + 2 - d)) < 2 ^ (2 * n - (D - d)) :=
          Nat.pow_lt_pow_right (by omega) hexp
        have hpowZ : (2 : Int) ^ (2 * n - (D + 2 - d)) < (2 : Int) ^ (2 * n - (D - d)) := by
          exact_mod_cast hpow
        unfold wgt
        omega
      have hterm_pos : 0 < ((Q n).coeff D : Int) * (wgt n d D - wgt n d (D + 2)) :=
        mul_pos hQ_pos hwgt_pos
      have hle := Finset.single_le_sum hnonneg hD_mem
      have hdiff := price_diff_eq n d
      omega

end PEqualNP.Outside.L_meta_25585_aux

theorem PEqualNP.Outside.L_meta_25585 : (let move := fun (keep : Bool) (mode letter : Nat) =>
    let near := letter.testBit 0
    let far := letter.testBit 1
    let hit := letter.testBit 2
    let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
      ((mode == 3) && near)
    let diagonal := keep && !hit && (((mode == 1) && !near && !far) ||
      (mode == 2) || (mode == 3))
    (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
      hit.toNat + (aligned && hit).toNat)
  let gain := fun (keep : Bool) (n code : Nat) =>
    ((List.range n).foldl (fun (st : Nat × Nat) j =>
      let result := move keep st.1 ((code >>> (3*j)) % 8)
      (result.1, st.2 + result.2)) (0, 0)).2
  let price := fun (keep : Bool) (n d : Nat) =>
    ((List.range (8^n)).map (fun word =>
      2 ^ (2*n - (gain keep n word - d)))).sum
  ∀ n : Nat,
    (∃ π : Equiv.Perm (Fin (8^n)), ∀ w : Fin (8^n),
      gain false n w.val ≤ gain true n (π w).val ∧
      gain false n w.val % 2 = gain true n (π w).val % 2) ∧
    ∀ d : Nat, price true n d ≤ price false n d ∧
      (price true n d < price false n d ↔ 3 ≤ n ∧ d < 3*(n-1)/2)) := by
  dsimp only
  intro n
  exact ⟨PEqualNP.Outside.L_meta_25585_aux.exists_parity_perm n,
    fun d => PEqualNP.Outside.L_meta_25585_aux.price_comparison n d⟩
