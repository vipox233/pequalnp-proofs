import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25590_aux

noncomputable section

open Polynomial

def move (keep : Bool) (mode letter : Nat) : Nat × Nat :=
  let near := letter.testBit 0
  let far := letter.testBit 1
  let hit := letter.testBit 2
  let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
    ((mode == 3) && near)
  let diagonal := (!hit && (((mode == 1) && !near && !far) ||
    (mode == 2) || (mode == 3))) || (keep && (mode == 3))
  (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
    hit.toNat + (aligned && hit).toNat)

def step (keep : Bool) (code : Nat) (st : Nat × Nat) (pos : Nat) : Nat × Nat :=
  let nxt := move keep st.1 ((code >>> (3 * pos)) % 8)
  (nxt.1, st.2 + nxt.2)

def runFrom (keep : Bool) (m s n code : Nat) : Nat × Nat :=
  (List.range n).foldl (step keep code) (m, s)

def gainFrom (keep : Bool) (m n code : Nat) : Nat :=
  (runFrom keep m 0 n code).2

def stateFrom (keep : Bool) (m n code : Nat) : Nat :=
  (runFrom keep m 0 n code).1

lemma foldl_shift (keep : Bool) (code : Nat) (l : List Nat) (m s : Nat) :
    l.foldl (step keep code) (m, s) =
      ((l.foldl (step keep code) (m, 0)).1, s + (l.foldl (step keep code) (m, 0)).2) := by
  induction l generalizing m s with
  | nil => simp
  | cons pos rest ih =>
    simp only [List.foldl_cons, step, Nat.zero_add]
    rw [ih, ih (m := (move keep m ((code >>> (3 * pos)) % 8)).1) (s := (move keep m ((code >>> (3 * pos)) % 8)).2)]
    ext
    · rfl
    · dsimp only
      omega

lemma foldl_map_succ (keep : Bool) (code : Nat) (l : List Nat) (st : Nat × Nat) :
    (l.map (· + 1)).foldl (step keep code) st = l.foldl (step keep (code / 8)) st := by
  induction l generalizing st with
  | nil => rfl
  | cons pos rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hsh : code >>> (3 * (pos + 1)) = (code / 8) >>> (3 * pos) := by
      rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      congr 1
      have h1 : 8 * 2 ^ (3 * pos) = 2 ^ 3 * 2 ^ (3 * pos) := rfl
      rw [h1, ← Nat.pow_add]
      congr 1
      omega
    simp only [step, hsh]
    exact ih _

lemma runFrom_succ (keep : Bool) (m n code : Nat) :
    runFrom keep m 0 (n + 1) code =
      (stateFrom keep (move keep m (code % 8)).1 n (code / 8),
       (move keep m (code % 8)).2 + gainFrom keep (move keep m (code % 8)).1 n (code / 8)) := by
  unfold runFrom stateFrom gainFrom
  rw [List.range_succ_eq_map, List.foldl_cons]
  simp only [step, Nat.mul_zero, Nat.shiftRight_zero, Nat.zero_add]
  rw [foldl_map_succ, foldl_shift]
  rfl

lemma gainFrom_succ (keep : Bool) (m n code : Nat) :
    gainFrom keep m (n + 1) code =
      (move keep m (code % 8)).2 + gainFrom keep (move keep m (code % 8)).1 n (code / 8) := by
  unfold gainFrom
  rw [runFrom_succ]
  rfl

lemma stateFrom_succ (keep : Bool) (m n code : Nat) :
    stateFrom keep m (n + 1) code =
      stateFrom keep (move keep m (code % 8)).1 n (code / 8) := by
  unfold stateFrom
  rw [runFrom_succ]
  rfl

lemma gainFrom_zero (keep : Bool) (m code : Nat) : gainFrom keep m 0 code = 0 := rfl

lemma stateFrom_zero (keep : Bool) (m code : Nat) : stateFrom keep m 0 code = m := rfl

lemma move_gain_le (keep : Bool) (m l : Nat) : (move keep m l).2 ≤ 2 := by
  unfold move
  dsimp only
  cases (l.testBit 2) <;> cases (((m == 1) && l.testBit 0 && l.testBit 1) || ((m == 2) && l.testBit 1) || ((m == 3) && l.testBit 0)) <;> decide

lemma gainFrom_le (keep : Bool) (m n code : Nat) : gainFrom keep m n code ≤ 2 * n := by
  induction n generalizing m code with
  | zero => simp [gainFrom_zero]
  | succ n ih =>
    rw [gainFrom_succ]
    have h1 := move_gain_le keep m (code % 8)
    have h2 := ih (move keep m (code % 8)).1 (code / 8)
    omega

lemma sum_range_eight_pow_succ {α : Type*} [AddCommMonoid α] (n : Nat) (f : Nat → α) :
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
    have h1 : p1.1 = p2.1 := by omega
    have h2 : p1.2 = p2.2 := by omega
    exact Prod.ext h1 h2
  · intro w hw
    simp only [Finset.mem_range] at hw
    refine ⟨(w % 8, w / 8), ?_, ?_⟩
    · simp only [Finset.mem_product, Finset.mem_range]
      refine ⟨Nat.mod_lt w (by omega), ?_⟩
      rw [pow_succ'] at hw
      omega
    · omega
  · intro _ _
    rfl

def F (keep : Bool) (m n : Nat) : Polynomial Nat :=
  ∑ w ∈ Finset.range (8 ^ n), X ^ gainFrom keep m n w

def W (m n : Nat) : Polynomial Nat :=
  ∑ w ∈ Finset.range (8 ^ n), if stateFrom true m n w = 3 then X ^ gainFrom true m n w else 0

lemma F_zero (keep : Bool) (m : Nat) : F keep m 0 = 1 := by
  simp [F, gainFrom_zero]

lemma W_zero (m : Nat) : W m 0 = if m = 3 then 1 else 0 := by
  simp [W, stateFrom_zero, gainFrom_zero]

lemma F_succ (keep : Bool) (m n : Nat) :
    F keep m (n + 1) =
      ∑ l ∈ Finset.range 8, X ^ (move keep m l).2 * F keep (move keep m l).1 n := by
  unfold F
  rw [sum_range_eight_pow_succ]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl8 : l < 8 := Finset.mem_range.mp hl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [gainFrom_succ]
  have hm : (l + 8 * r) % 8 = l := by omega
  have hd : (l + 8 * r) / 8 = r := by omega
  rw [hm, hd, pow_add]

lemma W_succ (m n : Nat) :
    W m (n + 1) =
      ∑ l ∈ Finset.range 8, X ^ (move true m l).2 * W (move true m l).1 n := by
  unfold W
  rw [sum_range_eight_pow_succ]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl8 : l < 8 := Finset.mem_range.mp hl
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [stateFrom_succ, gainFrom_succ]
  have hm : (l + 8 * r) % 8 = l := by omega
  have hd : (l + 8 * r) / 8 = r := by omega
  rw [hm, hd]
  split_ifs
  · rw [pow_add]
  · simp

lemma sum_range_eight_expand {α : Type*} [AddCommMonoid α] (f : Nat → α) :
    ∑ l ∈ Finset.range 8, f l =
      f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp [Finset.sum_range_succ]

lemma F_false_0_succ (n : Nat) :
    F false 0 (n + 1) = (4 + 4 * X) * F false 1 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F false 1 n + X ^ 0 * F false 1 n + X ^ 0 * F false 1 n + X ^ 0 * F false 1 n +
      X ^ 1 * F false 1 n + X ^ 1 * F false 1 n + X ^ 1 * F false 1 n + X ^ 1 * F false 1 n = _
  ring

lemma F_false_1_succ (n : Nat) :
    F false 1 (n + 1) =
      X ^ 2 * F false 0 n + (2 + 3 * X) * F false 1 n + F false 2 n + F false 3 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F false 3 n + X ^ 0 * F false 1 n + X ^ 0 * F false 1 n + X ^ 0 * F false 2 n +
      X ^ 1 * F false 1 n + X ^ 1 * F false 1 n + X ^ 1 * F false 1 n + X ^ 2 * F false 0 n = _
  ring

lemma F_false_2_succ (n : Nat) :
    F false 2 (n + 1) =
      2 * X ^ 2 * F false 0 n + 2 * X * F false 1 n + 2 * F false 2 n + 2 * F false 3 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F false 3 n + X ^ 0 * F false 3 n + X ^ 0 * F false 2 n + X ^ 0 * F false 2 n +
      X ^ 1 * F false 1 n + X ^ 1 * F false 1 n + X ^ 2 * F false 0 n + X ^ 2 * F false 0 n = _
  ring

lemma F_false_3_succ (n : Nat) :
    F false 3 (n + 1) =
      2 * X ^ 2 * F false 0 n + 2 * X * F false 1 n + 2 * F false 2 n + 2 * F false 3 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F false 3 n + X ^ 0 * F false 2 n + X ^ 0 * F false 3 n + X ^ 0 * F false 2 n +
      X ^ 1 * F false 1 n + X ^ 2 * F false 0 n + X ^ 1 * F false 1 n + X ^ 2 * F false 0 n = _
  ring

lemma F_true_0_succ (n : Nat) :
    F true 0 (n + 1) = (4 + 4 * X) * F true 1 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F true 1 n + X ^ 0 * F true 1 n + X ^ 0 * F true 1 n + X ^ 0 * F true 1 n +
      X ^ 1 * F true 1 n + X ^ 1 * F true 1 n + X ^ 1 * F true 1 n + X ^ 1 * F true 1 n = _
  ring

lemma F_true_1_succ (n : Nat) :
    F true 1 (n + 1) =
      X ^ 2 * F true 0 n + (2 + 3 * X) * F true 1 n + F true 2 n + F true 3 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F true 3 n + X ^ 0 * F true 1 n + X ^ 0 * F true 1 n + X ^ 0 * F true 2 n +
      X ^ 1 * F true 1 n + X ^ 1 * F true 1 n + X ^ 1 * F true 1 n + X ^ 2 * F true 0 n = _
  ring

lemma F_true_2_succ (n : Nat) :
    F true 2 (n + 1) =
      2 * X ^ 2 * F true 0 n + 2 * X * F true 1 n + 2 * F true 2 n + 2 * F true 3 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F true 3 n + X ^ 0 * F true 3 n + X ^ 0 * F true 2 n + X ^ 0 * F true 2 n +
      X ^ 1 * F true 1 n + X ^ 1 * F true 1 n + X ^ 2 * F true 0 n + X ^ 2 * F true 0 n = _
  ring

lemma F_true_3_succ (n : Nat) :
    F true 3 (n + 1) =
      2 * X ^ 2 * F true 0 n + 2 * F true 2 n + (2 + 2 * X) * F true 3 n := by
  rw [F_succ, sum_range_eight_expand]
  change X ^ 0 * F true 3 n + X ^ 0 * F true 2 n + X ^ 0 * F true 3 n + X ^ 0 * F true 2 n +
      X ^ 1 * F true 3 n + X ^ 2 * F true 0 n + X ^ 1 * F true 3 n + X ^ 2 * F true 0 n = _
  ring

lemma W_0_succ (n : Nat) :
    W 0 (n + 1) = (4 + 4 * X) * W 1 n := by
  rw [W_succ, sum_range_eight_expand]
  change X ^ 0 * W 1 n + X ^ 0 * W 1 n + X ^ 0 * W 1 n + X ^ 0 * W 1 n +
      X ^ 1 * W 1 n + X ^ 1 * W 1 n + X ^ 1 * W 1 n + X ^ 1 * W 1 n = _
  ring

lemma W_1_succ (n : Nat) :
    W 1 (n + 1) =
      X ^ 2 * W 0 n + (2 + 3 * X) * W 1 n + W 2 n + W 3 n := by
  rw [W_succ, sum_range_eight_expand]
  change X ^ 0 * W 3 n + X ^ 0 * W 1 n + X ^ 0 * W 1 n + X ^ 0 * W 2 n +
      X ^ 1 * W 1 n + X ^ 1 * W 1 n + X ^ 1 * W 1 n + X ^ 2 * W 0 n = _
  ring

lemma W_2_succ (n : Nat) :
    W 2 (n + 1) =
      2 * X ^ 2 * W 0 n + 2 * X * W 1 n + 2 * W 2 n + 2 * W 3 n := by
  rw [W_succ, sum_range_eight_expand]
  change X ^ 0 * W 3 n + X ^ 0 * W 3 n + X ^ 0 * W 2 n + X ^ 0 * W 2 n +
      X ^ 1 * W 1 n + X ^ 1 * W 1 n + X ^ 2 * W 0 n + X ^ 2 * W 0 n = _
  ring

lemma W_3_succ (n : Nat) :
    W 3 (n + 1) =
      2 * X ^ 2 * W 0 n + 2 * W 2 n + (2 + 2 * X) * W 3 n := by
  rw [W_succ, sum_range_eight_expand]
  change X ^ 0 * W 3 n + X ^ 0 * W 2 n + X ^ 0 * W 3 n + X ^ 0 * W 2 n +
      X ^ 1 * W 3 n + X ^ 2 * W 0 n + X ^ 1 * W 3 n + X ^ 2 * W 0 n = _
  ring

def TP : Nat → Polynomial Nat × Polynomial Nat
  | 0 => (1, 0)
  | j + 1 =>
    let p := TP j
    ((4 + 2 * X) * p.1 + (6 * X + 4 * X ^ 2) * p.2,
     X * p.1 + (2 + X) * p.2)

def Tpoly (j : Nat) : Polynomial Nat := (TP j).1
def Ppoly (j : Nat) : Polynomial Nat := (TP j).2

lemma Tpoly_zero : Tpoly 0 = 1 := rfl
lemma Ppoly_zero : Ppoly 0 = 0 := rfl

lemma Tpoly_succ (j : Nat) :
    Tpoly (j + 1) = (4 + 2 * X) * Tpoly j + (6 * X + 4 * X ^ 2) * Ppoly j := rfl

lemma Ppoly_succ (j : Nat) :
    Ppoly (j + 1) = X * Tpoly j + (2 + X) * Ppoly j := rfl

lemma F_false_eq_TP (j : Nat) :
    F false 0 j = Tpoly j + 2 * Ppoly j ∧
    F false 1 j = Tpoly j + (1 + X) * Ppoly j ∧
    F false 2 j = Tpoly j + 2 * X * Ppoly j ∧
    F false 3 j = Tpoly j + 2 * X * Ppoly j := by
  induction j with
  | zero =>
    simp [F_zero, Tpoly_zero, Ppoly_zero]
  | succ j ih =>
    rcases ih with ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [F_false_0_succ, h1, Tpoly_succ, Ppoly_succ]; ring
    · rw [F_false_1_succ, h0, h1, h2, h3, Tpoly_succ, Ppoly_succ]; ring
    · rw [F_false_2_succ, h0, h1, h2, h3, Tpoly_succ, Ppoly_succ]; ring
    · rw [F_false_3_succ, h0, h1, h2, h3, Tpoly_succ, Ppoly_succ]; ring

lemma F_false_diff_identity (j : Nat) :
    (1 + X) * F false 3 j + Ppoly j = (1 + X) * F false 1 j + X ^ 2 * Ppoly j := by
  rcases F_false_eq_TP j with ⟨_, h1, _, h3⟩
  rw [h1, h3]
  ring

def sumShift (m n : Nat) (b : Nat) : Polynomial Nat :=
  ∑ i ∈ Finset.range n, W m i * (2 * X) * F false b (n - 1 - i)

lemma sumShift_zero (m b : Nat) : sumShift m 0 b = 0 := by
  simp [sumShift]

lemma sumShift_succ (m n b : Nat) :
    sumShift m (n + 1) b =
      W m 0 * (2 * X) * F false b n +
        ∑ i ∈ Finset.range n, W m (i + 1) * (2 * X) * F false b (n - 1 - i) := by
  unfold sumShift
  rw [Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.add_sub_cancel]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : n - (i + 1) = n - 1 - i := by omega
  rw [hs]

lemma sumShift_0_succ (n b : Nat) :
    sumShift 0 (n + 1) b = (4 + 4 * X) * sumShift 1 n b := by
  rw [sumShift_succ, W_zero]
  have hne : ¬ (0 = 3) := by omega
  simp only [hne, ↓reduceIte, zero_mul, zero_add]
  unfold sumShift
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [W_0_succ]
  ring

lemma sumShift_1_succ (n b : Nat) :
    sumShift 1 (n + 1) b =
      X ^ 2 * sumShift 0 n b + (2 + 3 * X) * sumShift 1 n b +
        sumShift 2 n b + sumShift 3 n b := by
  rw [sumShift_succ, W_zero]
  have hne : ¬ (1 = 3) := by omega
  simp only [hne, ↓reduceIte, zero_mul, zero_add]
  unfold sumShift
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [W_1_succ]
  ring

lemma sumShift_2_succ (n b : Nat) :
    sumShift 2 (n + 1) b =
      2 * X ^ 2 * sumShift 0 n b + 2 * X * sumShift 1 n b +
        2 * sumShift 2 n b + 2 * sumShift 3 n b := by
  rw [sumShift_succ, W_zero]
  have hne : ¬ (2 = 3) := by omega
  simp only [hne, ↓reduceIte, zero_mul, zero_add]
  unfold sumShift
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [W_2_succ]
  ring

lemma sumShift_3_succ (n b : Nat) :
    sumShift 3 (n + 1) b =
      2 * X * F false b n + 2 * X ^ 2 * sumShift 0 n b +
        2 * sumShift 2 n b + (2 + 2 * X) * sumShift 3 n b := by
  rw [sumShift_succ, W_zero]
  simp only [↓reduceIte, one_mul]
  have hrest : ∑ i ∈ Finset.range n, W 3 (i + 1) * (2 * X) * F false b (n - 1 - i) =
      2 * X ^ 2 * sumShift 0 n b + 2 * sumShift 2 n b + (2 + 2 * X) * sumShift 3 n b := by
    unfold sumShift
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [W_3_succ]
    ring
  rw [hrest]
  ring

lemma telescope (n : Nat) :
    (F true 0 n + sumShift 0 n 1 = F false 0 n + sumShift 0 n 3) ∧
    (F true 1 n + sumShift 1 n 1 = F false 1 n + sumShift 1 n 3) ∧
    (F true 2 n + sumShift 2 n 1 = F false 2 n + sumShift 2 n 3) ∧
    (F true 3 n + sumShift 3 n 1 = F false 3 n + sumShift 3 n 3) := by
  induction n with
  | zero =>
    simp [F_zero, sumShift_zero]
  | succ n ih =>
    rcases ih with ⟨h0, h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [F_true_0_succ, F_false_0_succ, sumShift_0_succ, sumShift_0_succ]
      have := congrArg ((4 + 4 * X) * ·) h1
      calc (4 + 4 * X) * F true 1 n + (4 + 4 * X) * sumShift 1 n 1
          = (4 + 4 * X) * (F true 1 n + sumShift 1 n 1) := by ring
        _ = (4 + 4 * X) * (F false 1 n + sumShift 1 n 3) := this
        _ = (4 + 4 * X) * F false 1 n + (4 + 4 * X) * sumShift 1 n 3 := by ring
    · rw [F_true_1_succ, F_false_1_succ, sumShift_1_succ, sumShift_1_succ]
      have e0 := congrArg (X ^ 2 * ·) h0
      have e1 := congrArg ((2 + 3 * X) * ·) h1
      calc X ^ 2 * F true 0 n + (2 + 3 * X) * F true 1 n + F true 2 n + F true 3 n +
            (X ^ 2 * sumShift 0 n 1 + (2 + 3 * X) * sumShift 1 n 1 + sumShift 2 n 1 + sumShift 3 n 1)
          = X ^ 2 * (F true 0 n + sumShift 0 n 1) + (2 + 3 * X) * (F true 1 n + sumShift 1 n 1) +
            (F true 2 n + sumShift 2 n 1) + (F true 3 n + sumShift 3 n 1) := by ring
        _ = X ^ 2 * (F false 0 n + sumShift 0 n 3) + (2 + 3 * X) * (F false 1 n + sumShift 1 n 3) +
            (F false 2 n + sumShift 2 n 3) + (F false 3 n + sumShift 3 n 3) := by rw [e0, e1, h2, h3]
        _ = X ^ 2 * F false 0 n + (2 + 3 * X) * F false 1 n + F false 2 n + F false 3 n +
            (X ^ 2 * sumShift 0 n 3 + (2 + 3 * X) * sumShift 1 n 3 + sumShift 2 n 3 + sumShift 3 n 3) := by ring
    · rw [F_true_2_succ, F_false_2_succ, sumShift_2_succ, sumShift_2_succ]
      have e0 := congrArg (2 * X ^ 2 * ·) h0
      have e1 := congrArg (2 * X * ·) h1
      have e2 := congrArg (2 * ·) h2
      have e3 := congrArg (2 * ·) h3
      calc 2 * X ^ 2 * F true 0 n + 2 * X * F true 1 n + 2 * F true 2 n + 2 * F true 3 n +
            (2 * X ^ 2 * sumShift 0 n 1 + 2 * X * sumShift 1 n 1 + 2 * sumShift 2 n 1 + 2 * sumShift 3 n 1)
          = 2 * X ^ 2 * (F true 0 n + sumShift 0 n 1) + 2 * X * (F true 1 n + sumShift 1 n 1) +
            2 * (F true 2 n + sumShift 2 n 1) + 2 * (F true 3 n + sumShift 3 n 1) := by ring
        _ = 2 * X ^ 2 * (F false 0 n + sumShift 0 n 3) + 2 * X * (F false 1 n + sumShift 1 n 3) +
            2 * (F false 2 n + sumShift 2 n 3) + 2 * (F false 3 n + sumShift 3 n 3) := by rw [e0, e1, e2, e3]
        _ = 2 * X ^ 2 * F false 0 n + 2 * X * F false 1 n + 2 * F false 2 n + 2 * F false 3 n +
            (2 * X ^ 2 * sumShift 0 n 3 + 2 * X * sumShift 1 n 3 + 2 * sumShift 2 n 3 + 2 * sumShift 3 n 3) := by ring
    · rw [F_true_3_succ, F_false_3_succ, sumShift_3_succ, sumShift_3_succ]
      have e0 := congrArg (2 * X ^ 2 * ·) h0
      have e2 := congrArg (2 * ·) h2
      have e3 := congrArg ((2 + 2 * X) * ·) h3
      calc 2 * X ^ 2 * F true 0 n + 2 * F true 2 n + (2 + 2 * X) * F true 3 n +
            (2 * X * F false 1 n + 2 * X ^ 2 * sumShift 0 n 1 + 2 * sumShift 2 n 1 + (2 + 2 * X) * sumShift 3 n 1)
          = 2 * X * F false 1 n + 2 * X ^ 2 * (F true 0 n + sumShift 0 n 1) +
            2 * (F true 2 n + sumShift 2 n 1) + (2 + 2 * X) * (F true 3 n + sumShift 3 n 1) := by ring
        _ = 2 * X * F false 1 n + 2 * X ^ 2 * (F false 0 n + sumShift 0 n 3) +
            2 * (F false 2 n + sumShift 2 n 3) + (2 + 2 * X) * (F false 3 n + sumShift 3 n 3) := by rw [e0, e2, e3]
        _ = 2 * X ^ 2 * F false 0 n + 2 * X * F false 1 n + 2 * F false 2 n + 2 * F false 3 n +
            (2 * X * F false 3 n + 2 * X ^ 2 * sumShift 0 n 3 + 2 * sumShift 2 n 3 + (2 + 2 * X) * sumShift 3 n 3) := by ring

def Rpoly (n : Nat) : Polynomial Nat :=
  ∑ a ∈ Finset.range (n - 1), 8 * X * W 1 a * Ppoly (n - 2 - a)

lemma golden (n : Nat) :
    F true 0 n + Rpoly n = F false 0 n + X ^ 2 * Rpoly n := by
  cases n with
  | zero =>
    simp [F_zero, Rpoly]
  | succ k =>
    have htel := (telescope (k + 1)).1
    rw [sumShift_0_succ, sumShift_0_succ] at htel
    have hR : (4 + 4 * X) * sumShift 1 k 3 + Rpoly (k + 1) =
        (4 + 4 * X) * sumShift 1 k 1 + X ^ 2 * Rpoly (k + 1) := by
      unfold sumShift Rpoly
      simp only [Nat.add_sub_cancel, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      have hd := F_false_diff_identity (k - 1 - a)
      have hm := congrArg (8 * X * W 1 a * ·) hd
      have hs : k + 1 - 2 - a = k - 1 - a := by omega
      rw [hs]
      calc (4 + 4 * X) * (W 1 a * (2 * X) * F false 3 (k - 1 - a)) + 8 * X * W 1 a * Ppoly (k - 1 - a)
          = 8 * X * W 1 a * ((1 + X) * F false 3 (k - 1 - a) + Ppoly (k - 1 - a)) := by ring
        _ = 8 * X * W 1 a * ((1 + X) * F false 1 (k - 1 - a) + X ^ 2 * Ppoly (k - 1 - a)) := hm
        _ = (4 + 4 * X) * (W 1 a * (2 * X) * F false 1 (k - 1 - a)) +
            X ^ 2 * (8 * X * W 1 a * Ppoly (k - 1 - a)) := by ring
    have hboth : (F true 0 (k + 1) + Rpoly (k + 1)) + (4 + 4 * X) * sumShift 1 k 1 =
        (F false 0 (k + 1) + X ^ 2 * Rpoly (k + 1)) + (4 + 4 * X) * sumShift 1 k 1 := by
      calc (F true 0 (k + 1) + Rpoly (k + 1)) + (4 + 4 * X) * sumShift 1 k 1
          = (F true 0 (k + 1) + (4 + 4 * X) * sumShift 1 k 1) + Rpoly (k + 1) := by ring
        _ = (F false 0 (k + 1) + (4 + 4 * X) * sumShift 1 k 3) + Rpoly (k + 1) := by rw [htel]
        _ = F false 0 (k + 1) + ((4 + 4 * X) * sumShift 1 k 3 + Rpoly (k + 1)) := by ring
        _ = F false 0 (k + 1) + ((4 + 4 * X) * sumShift 1 k 1 + X ^ 2 * Rpoly (k + 1)) := by rw [hR]
        _ = (F false 0 (k + 1) + X ^ 2 * Rpoly (k + 1)) + (4 + 4 * X) * sumShift 1 k 1 := by ring
    exact add_right_cancel hboth

lemma coeff_finset_sum_aux {ι : Type*} (s : Finset ι) (f : ι → Polynomial Nat) (k : Nat) :
    (∑ i ∈ s, f i).coeff k = ∑ i ∈ s, (f i).coeff k := by
  rw [← Polynomial.lcoeff_apply, map_sum]
  rfl

lemma coeff_C_add_C_mul_X_zero (a b m : Nat) (hm : 1 < m) :
    (C a + C b * X : Polynomial Nat).coeff m = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul, Polynomial.coeff_X]
  have h1 : m ≠ 0 := by omega
  have h2 : ¬ (1 = m) := by omega
  simp [h1, h2]

lemma coeff_C_mul_X_add_C_mul_X2_zero (a b m : Nat) (hm : 2 < m) :
    (C a * X + C b * X ^ 2 : Polynomial Nat).coeff m = 0 := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  have h1 : ¬ (1 = m) := by omega
  have h2 : ¬ (m = 2) := by omega
  simp [h1, h2]

lemma coeff_mul_X_pow_zero {p : Polynomial Nat} {d k : Nat}
    (h : ∀ m, d < m → p.coeff m = 0) (r : Nat) (hk : d + r < k) :
    (X ^ r * p).coeff k = 0 := by
  rw [Polynomial.coeff_X_pow_mul']
  split_ifs with hr
  · exact h (k - r) (by omega)
  · rfl

lemma coeff_X_mul_zero {p : Polynomial Nat} {d k : Nat}
    (h : ∀ m, d < m → p.coeff m = 0) (hk : d + 1 < k) :
    (X * p).coeff k = 0 := by
  have := coeff_mul_X_pow_zero h 1 hk
  simpa using this

lemma coeff_mul_zero_of_bound {p q : Polynomial Nat} {dp dq k : Nat}
    (hp : ∀ m, dp < m → p.coeff m = 0)
    (hq : ∀ m, dq < m → q.coeff m = 0)
    (hk : dp + dq < k) : (p * q).coeff k = 0 := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  have hsum : x.1 + x.2 = k := by simpa using hx
  by_cases h1 : dp < x.1
  · rw [hp x.1 h1, zero_mul]
  · rw [hq x.2 (by omega), mul_zero]

lemma TP_bound : ∀ j : Nat,
    (∀ k, 3 * j / 2 < k → (Tpoly j).coeff k = 0) ∧
    (j = 0 → Ppoly j = 0) ∧
    (1 ≤ j → ∀ k, (3 * j - 1) / 2 < k → (Ppoly j).coeff k = 0) := by
  intro j
  induction j with
  | zero =>
    refine ⟨?_, fun _ => rfl, fun h => by omega⟩
    intro k hk
    rw [Tpoly_zero, Polynomial.coeff_one]
    simp [show k ≠ 0 by omega]
  | succ j ih =>
    rcases ih with ⟨hT, hP0, hP⟩
    refine ⟨?_, fun h => by omega, fun _ => ?_⟩
    · intro k hk
      rw [Tpoly_succ, Polynomial.coeff_add]
      have h1 : ((4 + 2 * X) * Tpoly j).coeff k = 0 := by
        have hlin : ∀ m, 1 < m → (4 + 2 * X : Polynomial Nat).coeff m = 0 := by
          intro m hm
          have heq : (4 + 2 * X : Polynomial Nat) = C 4 + C 2 * X := by simp
          rw [heq]
          exact coeff_C_add_C_mul_X_zero 4 2 m hm
        exact coeff_mul_zero_of_bound hlin hT (by omega)
      have h2 : ((6 * X + 4 * X ^ 2) * Ppoly j).coeff k = 0 := by
        by_cases hj : j = 0
        · rw [hP0 hj, mul_zero, Polynomial.coeff_zero]
        · have hquad : ∀ m, 2 < m → (6 * X + 4 * X ^ 2 : Polynomial Nat).coeff m = 0 := by
            intro m hm
            have heq : (6 * X + 4 * X ^ 2 : Polynomial Nat) = C 6 * X + C 4 * X ^ 2 := by simp
            rw [heq]
            exact coeff_C_mul_X_add_C_mul_X2_zero 6 4 m hm
          exact coeff_mul_zero_of_bound hquad (hP (by omega)) (by omega)
      rw [h1, h2, zero_add]
    · intro k hk
      rw [Ppoly_succ, Polynomial.coeff_add]
      have h1 : (X * Tpoly j).coeff k = 0 := coeff_X_mul_zero hT (by omega)
      have h2 : ((2 + X) * Ppoly j).coeff k = 0 := by
        by_cases hj : j = 0
        · rw [hP0 hj, mul_zero, Polynomial.coeff_zero]
        · have hlin : ∀ m, 1 < m → (2 + X : Polynomial Nat).coeff m = 0 := by
            intro m hm
            have heq : (2 + X : Polynomial Nat) = C 2 + C 1 * X := by simp
            rw [heq]
            exact coeff_C_add_C_mul_X_zero 2 1 m hm
          exact coeff_mul_zero_of_bound hlin (hP (by omega)) (by omega)
      rw [h1, h2, zero_add]

lemma TP_pos : ∀ j : Nat,
    0 < (Tpoly j).coeff (3 * j / 2) ∧
    (1 ≤ j → 0 < (Ppoly j).coeff ((3 * j - 1) / 2)) := by
  intro j
  induction j with
  | zero =>
    exact ⟨by simp [Tpoly_zero], fun h => by omega⟩
  | succ j ih =>
    rcases ih with ⟨hT, hP⟩
    refine ⟨?_, fun _ => ?_⟩
    · rw [Tpoly_succ, Polynomial.coeff_add]
      by_cases hpar : j % 2 = 0
      · have hidx : 3 * (j + 1) / 2 = 3 * j / 2 + 1 := by omega
        rw [hidx]
        have hpos : 0 < ((4 + 2 * X) * Tpoly j).coeff (3 * j / 2 + 1) := by
          have : (4 + 2 * X) * Tpoly j = 4 * Tpoly j + 2 * (X * Tpoly j) := by ring
          rw [this, Polynomial.coeff_add]
          have h2 : (2 * (X * Tpoly j)).coeff (3 * j / 2 + 1) = 2 * (Tpoly j).coeff (3 * j / 2) := by
            rw [Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_mul]
          omega
        omega
      · have hj1 : 1 ≤ j := by omega
        have hidx : 3 * (j + 1) / 2 = (3 * j - 1) / 2 + 2 := by omega
        rw [hidx]
        have hpos : 0 < ((6 * X + 4 * X ^ 2) * Ppoly j).coeff ((3 * j - 1) / 2 + 2) := by
          have : (6 * X + 4 * X ^ 2) * Ppoly j = 6 * (X * Ppoly j) + 4 * (X ^ 2 * Ppoly j) := by ring
          rw [this, Polynomial.coeff_add]
          have h4 : (4 * (X ^ 2 * Ppoly j)).coeff ((3 * j - 1) / 2 + 2) =
              4 * (Ppoly j).coeff ((3 * j - 1) / 2) := by
            rw [Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_pow_mul]
          have := hP hj1
          omega
        omega
    · rw [Ppoly_succ, Polynomial.coeff_add]
      have hidx : (3 * (j + 1) - 1) / 2 = 3 * j / 2 + 1 := by omega
      rw [hidx, Polynomial.coeff_X_mul]
      omega

lemma W_bound : ∀ a : Nat,
    (a ≤ 1 → W 0 a = 0) ∧
    (2 ≤ a → ∀ k, (3 * a - 4) / 2 < k → (W 0 a).coeff k = 0) ∧
    (a = 0 → W 1 a = 0) ∧
    (1 ≤ a → ∀ k, 3 * (a - 1) / 2 < k → (W 1 a).coeff k = 0) ∧
    (a = 0 → W 2 a = 0) ∧
    (1 ≤ a → ∀ k, 3 * (a - 1) / 2 < k → (W 2 a).coeff k = 0) ∧
    (∀ k, 3 * a / 2 < k → (W 3 a).coeff k = 0) := by
  intro a
  induction a with
  | zero =>
    refine ⟨fun _ => by simp [W_zero], fun h => by omega, fun _ => by simp [W_zero],
      fun h => by omega, fun _ => by simp [W_zero], fun h => by omega, ?_⟩
    intro k hk
    rw [W_zero]
    simp only [↓reduceIte, Polynomial.coeff_one]
    simp [show k ≠ 0 by omega]
  | succ a ih =>
    rcases ih with ⟨h0s, h0, h1s, h1, h2s, h2, h3⟩
    have hlin4 : ∀ m, 1 < m → (4 + 4 * X : Polynomial Nat).coeff m = 0 := by
      intro m hm
      have heq : (4 + 4 * X : Polynomial Nat) = C 4 + C 4 * X := by simp
      rw [heq]; exact coeff_C_add_C_mul_X_zero 4 4 m hm
    have hlin23 : ∀ m, 1 < m → (2 + 3 * X : Polynomial Nat).coeff m = 0 := by
      intro m hm
      have heq : (2 + 3 * X : Polynomial Nat) = C 2 + C 3 * X := by simp
      rw [heq]; exact coeff_C_add_C_mul_X_zero 2 3 m hm
    have hlin22 : ∀ m, 1 < m → (2 + 2 * X : Polynomial Nat).coeff m = 0 := by
      intro m hm
      have heq : (2 + 2 * X : Polynomial Nat) = C 2 + C 2 * X := by simp
      rw [heq]; exact coeff_C_add_C_mul_X_zero 2 2 m hm
    have hX2W0 : ∀ k, 3 * a / 2 < k → (X ^ 2 * W 0 a).coeff k = 0 := by
      intro k hk
      by_cases ha : a ≤ 1
      · rw [h0s ha, mul_zero, Polynomial.coeff_zero]
      · exact coeff_mul_X_pow_zero (h0 (by omega)) 2 (by omega)
    refine ⟨?_, ?_, fun h => by omega, ?_, fun h => by omega, ?_, ?_⟩
    · intro ha
      have ha0 : a = 0 := by omega
      subst ha0
      rw [W_0_succ, h1s rfl, mul_zero]
    · intro ha k hk
      rw [W_0_succ]
      exact coeff_mul_zero_of_bound hlin4 (h1 (by omega)) (by omega)
    · intro _ k hk
      rw [W_1_succ, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
      have e0 : (X ^ 2 * W 0 a).coeff k = 0 := hX2W0 k (by omega)
      have e1 : ((2 + 3 * X) * W 1 a).coeff k = 0 := by
        by_cases ha : a = 0
        · rw [h1s ha, mul_zero, Polynomial.coeff_zero]
        · exact coeff_mul_zero_of_bound hlin23 (h1 (by omega)) (by omega)
      have e2 : (W 2 a).coeff k = 0 := by
        by_cases ha : a = 0
        · rw [h2s ha, Polynomial.coeff_zero]
        · exact h2 (by omega) k (by omega)
      have e3 : (W 3 a).coeff k = 0 := h3 k (by omega)
      rw [e0, e1, e2, e3]
    · intro _ k hk
      rw [W_2_succ, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add]
      have e0 : (2 * X ^ 2 * W 0 a).coeff k = 0 := by
        rw [mul_assoc, Polynomial.coeff_ofNat_mul, hX2W0 k (by omega), mul_zero]
      have e1 : (2 * X * W 1 a).coeff k = 0 := by
        by_cases ha : a = 0
        · rw [h1s ha, mul_zero, Polynomial.coeff_zero]
        · rw [mul_assoc, Polynomial.coeff_ofNat_mul, coeff_X_mul_zero (h1 (by omega)) (by omega), mul_zero]
      have e2 : (2 * W 2 a).coeff k = 0 := by
        by_cases ha : a = 0
        · rw [h2s ha, mul_zero, Polynomial.coeff_zero]
        · rw [Polynomial.coeff_ofNat_mul, h2 (by omega) k (by omega), mul_zero]
      have e3 : (2 * W 3 a).coeff k = 0 := by
        rw [Polynomial.coeff_ofNat_mul, h3 k (by omega), mul_zero]
      rw [e0, e1, e2, e3]
    · intro k hk
      rw [W_3_succ, Polynomial.coeff_add, Polynomial.coeff_add]
      have e0 : (2 * X ^ 2 * W 0 a).coeff k = 0 := by
        rw [mul_assoc, Polynomial.coeff_ofNat_mul, hX2W0 k (by omega), mul_zero]
      have e2 : (2 * W 2 a).coeff k = 0 := by
        by_cases ha : a = 0
        · rw [h2s ha, mul_zero, Polynomial.coeff_zero]
        · rw [Polynomial.coeff_ofNat_mul, h2 (by omega) k (by omega), mul_zero]
      have e3 : ((2 + 2 * X) * W 3 a).coeff k = 0 :=
        coeff_mul_zero_of_bound hlin22 h3 (by omega)
      rw [e0, e2, e3]

lemma W_1_one : W 1 1 = 1 := by
  rw [W_1_succ, W_zero, W_zero, W_zero, W_zero]
  simp

lemma Rpoly_zero_of_lt_four {n : Nat} (hn : n < 4) : Rpoly n = 0 := by
  unfold Rpoly
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : a < n - 1 := Finset.mem_range.mp ha
  by_cases ha0 : a = 0
  · subst ha0
    rw [(W_bound 0).2.2.1 rfl]
    simp
  · have hj0 : n - 2 - a = 0 := by omega
    rw [hj0, Ppoly_zero, mul_zero]

lemma Rpoly_coeff_zero_of_gt {n k : Nat} (hn : 4 ≤ n) (hk : 3 * n / 2 - 4 < k) :
    (Rpoly n).coeff k = 0 := by
  unfold Rpoly
  rw [coeff_finset_sum_aux]
  refine Finset.sum_eq_zero fun a ha => ?_
  have ha' : a < n - 1 := Finset.mem_range.mp ha
  by_cases ha0 : a = 0
  · subst ha0
    rw [(W_bound 0).2.2.1 rfl]
    simp
  · by_cases hj0 : n - 2 - a = 0
    · rw [hj0, Ppoly_zero, mul_zero, Polynomial.coeff_zero]
    · have hW := (W_bound a).2.2.2.1 (by omega)
      have hP := (TP_bound (n - 2 - a)).2.2 (by omega)
      have h8X : ∀ m, 1 < m → (8 * X : Polynomial Nat).coeff m = 0 := by
        intro m hm
        have heq : (8 * X : Polynomial Nat) = C 0 + C 8 * X := by simp
        rw [heq]; exact coeff_C_add_C_mul_X_zero 0 8 m hm
      have h8XW : ∀ m, 1 + 3 * (a - 1) / 2 < m → (8 * X * W 1 a).coeff m = 0 :=
        fun m hm => coeff_mul_zero_of_bound h8X hW hm
      exact coeff_mul_zero_of_bound h8XW hP (by omega)

lemma Rpoly_top_pos {n : Nat} (hn : 4 ≤ n) :
    0 < (Rpoly n).coeff (3 * n / 2 - 4) := by
  unfold Rpoly
  rw [coeff_finset_sum_aux]
  have hmem : 1 ∈ Finset.range (n - 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum (f := fun a => (8 * X * W 1 a * Ppoly (n - 2 - a)).coeff (3 * n / 2 - 4))
    (fun _ _ => Nat.zero_le _) hmem
  have h1 : (8 * X * W 1 1 * Ppoly (n - 2 - 1)).coeff (3 * n / 2 - 4) =
      8 * (Ppoly (n - 3)).coeff ((3 * (n - 3) - 1) / 2) := by
    rw [W_1_one, mul_one]
    have hidx : 3 * n / 2 - 4 = (3 * (n - 3) - 1) / 2 + 1 := by omega
    have hsub : n - 2 - 1 = n - 3 := by omega
    rw [hsub, hidx, mul_assoc, Polynomial.coeff_ofNat_mul, Polynomial.coeff_X_mul]
  have hpos := (TP_pos (n - 3)).2 (by omega)
  omega

lemma Rpoly_coeff_zero_of_ge {n k : Nat} (hk : 2 * n - 1 ≤ k) :
    (Rpoly n).coeff k = 0 := by
  by_cases hn : n < 4
  · rw [Rpoly_zero_of_lt_four hn, Polynomial.coeff_zero]
  · exact Rpoly_coeff_zero_of_gt (by omega) (by omega)

lemma F_coeff_eq_card (keep : Bool) (n g : Nat) :
    (F keep 0 n).coeff g =
      (Finset.filter (fun w => gainFrom keep 0 n w = g) (Finset.range (8 ^ n))).card := by
  unfold F
  rw [coeff_finset_sum_aux, Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Polynomial.coeff_X_pow]
  by_cases h : gainFrom keep 0 n w = g
  · simp [h]
  · simp [h, Ne.symm h]

lemma F_coeff_fin_card (keep : Bool) (n g : Nat) :
    (F keep 0 n).coeff g =
      (Finset.filter (fun w : Fin (8 ^ n) => gainFrom keep 0 n w.val = g) Finset.univ).card := by
  rw [F_coeff_eq_card]
  refine Finset.card_bij (fun w hw => ⟨w, Finset.mem_range.mp (Finset.mem_filter.mp hw).1⟩) ?_ ?_ ?_
  · intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩
  · intro w1 _ w2 _ h
    exact congrArg Fin.val h
  · intro w hw
    exact ⟨w.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr w.isLt, (Finset.mem_filter.mp hw).2⟩, rfl⟩

lemma golden_coeff (n g : Nat) :
    (F true 0 n).coeff g + (Rpoly n).coeff g =
      (F false 0 n).coeff g + (if 2 ≤ g then (Rpoly n).coeff (g - 2) else 0) := by
  have h := congrArg (fun p => p.coeff g) (golden n)
  simpa only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul'] using h

lemma sum_even_step (n p k : Nat) (hp : p < 2) :
    ∑ j ∈ Finset.Ico k (n + 1), (F true 0 n).coeff (p + 2 * j) +
        (if k ≤ n then (Rpoly n).coeff (p + 2 * n) else 0) =
      ∑ j ∈ Finset.Ico k (n + 1), (F false 0 n).coeff (p + 2 * j) +
        (if k = 0 then 0 else if k ≤ n then (Rpoly n).coeff (p + 2 * (k - 1)) else 0) := by
  by_cases hkn : k ≤ n
  · have hsum :
        ∑ j ∈ Finset.Ico k (n + 1), ((F true 0 n).coeff (p + 2 * j) + (Rpoly n).coeff (p + 2 * j)) =
        ∑ j ∈ Finset.Ico k (n + 1), ((F false 0 n).coeff (p + 2 * j) +
          (if 2 ≤ p + 2 * j then (Rpoly n).coeff (p + 2 * j - 2) else 0)) := by
      refine Finset.sum_congr rfl fun j _ => golden_coeff n (p + 2 * j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hsplitL :
        ∑ j ∈ Finset.Ico k (n + 1), (Rpoly n).coeff (p + 2 * j) =
          ∑ j ∈ Finset.Ico k n, (Rpoly n).coeff (p + 2 * j) + (Rpoly n).coeff (p + 2 * n) := by
      rw [Finset.sum_Ico_succ_top hkn]
    have hsplitR :
        ∑ j ∈ Finset.Ico k (n + 1), (if 2 ≤ p + 2 * j then (Rpoly n).coeff (p + 2 * j - 2) else 0) =
          ∑ j ∈ Finset.Ico k n, (Rpoly n).coeff (p + 2 * j) +
            (if k = 0 then 0 else (Rpoly n).coeff (p + 2 * (k - 1))) := by
      cases k with
      | zero =>
        simp only [↓reduceIte, add_zero]
        rw [Finset.sum_eq_sum_Ico_succ_bot (Nat.zero_lt_succ n)]
        have hbot : (if 2 ≤ p + 2 * 0 then (Rpoly n).coeff (p + 2 * 0 - 2) else 0) = 0 := by
          split_ifs with h
          · omega
          · rfl
        rw [hbot, zero_add]
        refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        · intro j1 hj1 j2 hj2 heq
          simp only [Finset.mem_Ico] at hj1 hj2
          omega
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          have hge : 2 ≤ p + 2 * j := by omega
          have hsub : p + 2 * j - 2 = p + 2 * (j - 1) := by omega
          rw [ite_eq_left hge, hsub]
      | succ k' =>
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : k' + 1 < n + 1)]
        have hbot : (if 2 ≤ p + 2 * (k' + 1) then (Rpoly n).coeff (p + 2 * (k' + 1) - 2) else 0) =
            (Rpoly n).coeff (p + 2 * k') := by
          have hge : 2 ≤ p + 2 * (k' + 1) := by omega
          have hsub : p + 2 * (k' + 1) - 2 = p + 2 * k' := by omega
          rw [ite_eq_left hge, hsub]
        rw [hbot, add_comm]
        congr 1
        refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
        · intro j hj
          simp only [Finset.mem_Ico] at hj ⊢
          omega
        · intro j1 hj1 j2 hj2 heq
          simp only [Finset.mem_Ico] at hj1 hj2
          omega
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          exact ⟨j + 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
        · intro j hj
          simp only [Finset.mem_Ico] at hj
          have hge : 2 ≤ p + 2 * j := by omega
          have hsub : p + 2 * j - 2 = p + 2 * (j - 1) := by omega
          rw [ite_eq_left hge, hsub]
    rw [hsplitL, hsplitR] at hsum
    rw [ite_eq_left hkn]
    by_cases hk0 : k = 0
    · simp only [hk0, ↓reduceIte] at hsum ⊢
      omega
    · simp only [hk0, ↓reduceIte, ite_eq_left hkn] at hsum ⊢
      omega
  · have hemp : Finset.Ico k (n + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    simp [hemp, hkn]

lemma parity_filter_card_eq_sum (keep : Bool) (n p k : Nat) (hp : p < 2) :
    (Finset.filter (fun w : Fin (8 ^ n) =>
        gainFrom keep 0 n w.val % 2 = p ∧ p + 2 * k ≤ gainFrom keep 0 n w.val) Finset.univ).card =
      ∑ j ∈ Finset.Ico k (n + 1), (F keep 0 n).coeff (p + 2 * j) := by
  have hbij :
      (Finset.filter (fun w : Fin (8 ^ n) =>
          gainFrom keep 0 n w.val % 2 = p ∧ p + 2 * k ≤ gainFrom keep 0 n w.val) Finset.univ).card =
        ∑ j ∈ Finset.Ico k (n + 1),
          (Finset.filter (fun w : Fin (8 ^ n) => gainFrom keep 0 n w.val = p + 2 * j) Finset.univ).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_Ico]
      constructor
      · rintro ⟨hmod, hle⟩
        refine ⟨gainFrom keep 0 n w.val / 2, ⟨?_, ?_⟩, ?_⟩
        · omega
        · have := gainFrom_le keep 0 n w.val
          omega
        · omega
      · rintro ⟨j, ⟨hjk, _⟩, heq⟩
        rw [heq]
        omega
    · intro j1 _ j2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      have h1 := (Finset.mem_filter.mp hw1).2
      have h2 := (Finset.mem_filter.mp hw2).2
      omega
  rw [hbij]
  refine Finset.sum_congr rfl fun j _ => (F_coeff_fin_card keep n (p + 2 * j)).symm

lemma parity_total_eq (n p : Nat) (hp : p < 2) :
    (Finset.filter (fun w : Fin (8 ^ n) => gainFrom false 0 n w.val % 2 = p) Finset.univ).card =
      (Finset.filter (fun w : Fin (8 ^ n) => gainFrom true 0 n w.val % 2 = p) Finset.univ).card := by
  have h1 := parity_filter_card_eq_sum false n p 0 hp
  have h2 := parity_filter_card_eq_sum true n p 0 hp
  have hs := sum_even_step n p 0 hp
  have hR : (Rpoly n).coeff (p + 2 * n) = 0 := Rpoly_coeff_zero_of_ge (by omega)
  simp only [Nat.mul_zero, add_zero, ↓reduceIte, Nat.zero_le, hR] at h1 h2 hs
  have hf : ∀ (keep : Bool),
      Finset.filter (fun w : Fin (8 ^ n) => gainFrom keep 0 n w.val % 2 = p) Finset.univ =
      Finset.filter (fun w : Fin (8 ^ n) => gainFrom keep 0 n w.val % 2 = p ∧ p ≤ gainFrom keep 0 n w.val) Finset.univ := by
    intro keep
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨h, ?_⟩
      omega
    · exact And.left
  rw [hf false, hf true, h1, h2]
  exact hs.symm

lemma parity_tail_le (n p k : Nat) (hp : p < 2) :
    (Finset.filter (fun w : Fin (8 ^ n) =>
        gainFrom false 0 n w.val % 2 = p ∧ k ≤ gainFrom false 0 n w.val) Finset.univ).card ≤
      (Finset.filter (fun w : Fin (8 ^ n) =>
        gainFrom true 0 n w.val % 2 = p ∧ k ≤ gainFrom true 0 n w.val) Finset.univ).card := by
  let q := if k ≤ p then 0 else (k - p + 1) / 2
  have heq : ∀ (keep : Bool),
      Finset.filter (fun w : Fin (8 ^ n) =>
        gainFrom keep 0 n w.val % 2 = p ∧ k ≤ gainFrom keep 0 n w.val) Finset.univ =
      Finset.filter (fun w : Fin (8 ^ n) =>
        gainFrom keep 0 n w.val % 2 = p ∧ p + 2 * q ≤ gainFrom keep 0 n w.val) Finset.univ := by
    intro keep
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> rintro ⟨hm, hl⟩ <;> refine ⟨hm, ?_⟩ <;> dsimp only [q] at * <;> split_ifs at * <;> omega
  rw [heq false, heq true, parity_filter_card_eq_sum false n p q hp, parity_filter_card_eq_sum true n p q hp]
  have hs := sum_even_step n p q hp
  have hR : (Rpoly n).coeff (p + 2 * n) = 0 := Rpoly_coeff_zero_of_ge (by omega)
  simp only [hR, ite_self, add_zero] at hs
  omega

def lexRel {N : Nat} (f : Fin N → Nat) (a b : Fin N) : Prop :=
  f a < f b ∨ (f a = f b ∧ a.val ≤ b.val)

def lexRel_decidable {N : Nat} (f : Fin N → Nat) : DecidableRel (lexRel f) :=
  fun a b => inferInstanceAs (Decidable (f a < f b ∨ (f a = f b ∧ a.val ≤ b.val)))

lemma lexRel_total {N : Nat} (f : Fin N → Nat) : Std.Total (lexRel f) := by
  refine ⟨fun a b => ?_⟩
  unfold lexRel
  omega

lemma lexRel_trans {N : Nat} (f : Fin N → Nat) : IsTrans (Fin N) (lexRel f) := by
  refine ⟨fun a b c h1 h2 => ?_⟩
  unfold lexRel at h1 h2 ⊢
  omega

lemma lexRel_antisymm {N : Nat} (f : Fin N → Nat) : Std.Antisymm (lexRel f) := by
  refine ⟨fun a b h1 h2 => ?_⟩
  unfold lexRel at h1 h2
  exact Fin.ext (by omega)

lemma sorted_le_of_tail_le {N : Nat} (f g : Fin N → Nat) (Sf Sg : Finset (Fin N))
    (hcard : Sf.card = Sg.card)
    (htail : ∀ k, (Sf.filter (fun w => k ≤ f w)).card ≤ (Sg.filter (fun w => k ≤ g w)).card) :
    letI : DecidableRel (lexRel f) := lexRel_decidable f
    letI : Std.Total (lexRel f) := lexRel_total f
    letI : IsTrans (Fin N) (lexRel f) := lexRel_trans f
    letI : Std.Antisymm (lexRel f) := lexRel_antisymm f
    letI : DecidableRel (lexRel g) := lexRel_decidable g
    letI : Std.Total (lexRel g) := lexRel_total g
    letI : IsTrans (Fin N) (lexRel g) := lexRel_trans g
    letI : Std.Antisymm (lexRel g) := lexRel_antisymm g
    let Lf := Sf.sort (lexRel f)
    let Lg := Sg.sort (lexRel g)
    ∀ i (hif : i < Lf.length) (hig : i < Lg.length), f (Lf[i]) ≤ g (Lg[i]) := by
  let : DecidableRel (lexRel f) := lexRel_decidable f
  let : Std.Total (lexRel f) := lexRel_total f
  let : IsTrans (Fin N) (lexRel f) := lexRel_trans f
  let : Std.Antisymm (lexRel f) := lexRel_antisymm f
  let : DecidableRel (lexRel g) := lexRel_decidable g
  let : Std.Total (lexRel g) := lexRel_total g
  let : IsTrans (Fin N) (lexRel g) := lexRel_trans g
  let : Std.Antisymm (lexRel g) := lexRel_antisymm g
  intro Lf Lg i hif hig
  by_contra hlt
  push Not at hlt
  let k := f Lf[i]
  have hLflen : Lf.length = Sf.card := Finset.length_sort (lexRel f)
  have hLglen : Lg.length = Sg.card := Finset.length_sort (lexRel g)
  have hPairF : Lf.Pairwise (lexRel f) := Finset.pairwise_sort Sf (lexRel f)
  have hPairG : Lg.Pairwise (lexRel g) := Finset.pairwise_sort Sg (lexRel g)
  have hNodupF : Lf.Nodup := Finset.sort_nodup Sf (lexRel f)
  have hNodupG : Lg.Nodup := Finset.sort_nodup Sg (lexRel g)
  have hFge : Sf.card - i ≤ (Sf.filter (fun w => k ≤ f w)).card := by
    have hcard_ico : (Finset.Ico i Lf.length).card = Sf.card - i := by
      rw [Nat.card_Ico, hLflen]
    rw [← hcard_ico]
    refine Finset.card_le_card_of_injOn (fun j => if hj : j < Lf.length then Lf[j] else Lf[i]) ?_ ?_
    · intro j hj
      have hj' := Finset.mem_Ico.mp hj
      dsimp only
      rw [dite_eq_left hj'.2]
      refine Finset.mem_filter.mpr ⟨(Finset.mem_sort (lexRel f)).mp (List.getElem_mem hj'.2), ?_⟩
      by_cases heq : i = j
      · subst heq; exact le_rfl
      · have hrel := List.pairwise_iff_getElem.mp hPairF i j hif hj'.2 (by omega)
        unfold lexRel at hrel
        dsimp only [k]
        omega
    · intro j1 hj1 j2 hj2 heq
      have hj1' := Finset.mem_Ico.mp hj1
      have hj2' := Finset.mem_Ico.mp hj2
      dsimp only at heq
      rw [dite_eq_left hj1'.2, dite_eq_left hj2'.2] at heq
      exact (List.Nodup.getElem_inj_iff hNodupF).mp heq
  have hGlt : (Sg.filter (fun w => k ≤ g w)).card ≤ Sg.card - i - 1 := by
    have hsub : Sg.filter (fun w => k ≤ g w) ⊆
        (Finset.Ico (i + 1) Lg.length).image (fun j => if hj : j < Lg.length then Lg[j] else Lg[i]) := by
      intro w hw
      have hw' := Finset.mem_filter.mp hw
      have hmem : w ∈ Lg := (Finset.mem_sort (lexRel g)).mpr hw'.1
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
      refine Finset.mem_image.mpr ⟨j, ?_, by rw [dite_eq_left hj]⟩
      refine Finset.mem_Ico.mpr ⟨?_, hj⟩
      by_contra hle
      have hji : j ≤ i := by omega
      have hgw : g Lg[j] ≤ g Lg[i] := by
        by_cases heq : j = i
        · subst heq; exact le_rfl
        · have hrel := List.pairwise_iff_getElem.mp hPairG j i hj hig (by omega)
          unfold lexRel at hrel
          omega
      have hk := hw'.2
      omega
    have hle1 := Finset.card_le_card hsub
    have hle2 := Finset.card_image_le (s := Finset.Ico (i + 1) Lg.length)
      (f := fun j => if hj : j < Lg.length then Lg[j] else Lg[i])
    rw [Nat.card_Ico] at hle2
    omega
  have htk := htail k
  omega

lemma exists_equiv_of_same_card_sort {N : Nat} (f g : Fin N → Nat) (Sf Sg : Finset (Fin N))
    (hcard : Sf.card = Sg.card)
    (htail : ∀ k, (Sf.filter (fun w => k ≤ f w)).card ≤ (Sg.filter (fun w => k ≤ g w)).card) :
    ∃ e : {w : Fin N // w ∈ Sf} ≃ {w : Fin N // w ∈ Sg}, ∀ x, f x.val ≤ g (e x).val := by
  let : DecidableRel (lexRel f) := lexRel_decidable f
  let : Std.Total (lexRel f) := lexRel_total f
  let : IsTrans (Fin N) (lexRel f) := lexRel_trans f
  let : Std.Antisymm (lexRel f) := lexRel_antisymm f
  let : DecidableRel (lexRel g) := lexRel_decidable g
  let : Std.Total (lexRel g) := lexRel_total g
  let : IsTrans (Fin N) (lexRel g) := lexRel_trans g
  let : Std.Antisymm (lexRel g) := lexRel_antisymm g
  let Lf := Sf.sort (lexRel f)
  let Lg := Sg.sort (lexRel g)
  have hLflen : Lf.length = Sf.card := Finset.length_sort (lexRel f)
  have hLglen : Lg.length = Sg.card := Finset.length_sort (lexRel g)
  have hNodupF : Lf.Nodup := Finset.sort_nodup Sf (lexRel f)
  have hNodupG : Lg.Nodup := Finset.sort_nodup Sg (lexRel g)
  have hlenEq : Lf.length = Lg.length := by omega
  let eF : Fin Lf.length ≃ {w : Fin N // w ∈ Sf} :=
    Equiv.ofBijective
      (fun i => ⟨Lf[i.val], (Finset.mem_sort (lexRel f)).mp (List.getElem_mem i.isLt)⟩)
      ⟨fun i j h => Fin.ext ((List.Nodup.getElem_inj_iff hNodupF).mp (congrArg Subtype.val h)),
       fun ⟨w, hw⟩ => by
         obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((Finset.mem_sort (lexRel f)).mpr hw)
         exact ⟨⟨i, hi⟩, rfl⟩⟩
  let eG : Fin Lg.length ≃ {w : Fin N // w ∈ Sg} :=
    Equiv.ofBijective
      (fun i => ⟨Lg[i.val], (Finset.mem_sort (lexRel g)).mp (List.getElem_mem i.isLt)⟩)
      ⟨fun i j h => Fin.ext ((List.Nodup.getElem_inj_iff hNodupG).mp (congrArg Subtype.val h)),
       fun ⟨w, hw⟩ => by
         obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ((Finset.mem_sort (lexRel g)).mpr hw)
         exact ⟨⟨i, hi⟩, rfl⟩⟩
  let eFin : Fin Lf.length ≃ Fin Lg.length := finCongr hlenEq
  refine ⟨eF.symm.trans (eFin.trans eG), fun x => ?_⟩
  set i : Fin Lf.length := eF.symm x
  have hx : eF i = x := eF.apply_symm_apply x
  have hval : x.val = Lf[i.val] := (congrArg Subtype.val hx).symm
  have hig : i.val < Lg.length := by have := i.isLt; omega
  have hval2 : ((eF.symm.trans (eFin.trans eG)) x).val = Lg[i.val]'hig := rfl
  rw [hval, hval2]
  exact sorted_le_of_tail_le f g Sf Sg hcard htail i.val i.isLt hig

lemma exists_parity_perm_aux {N : Nat} (f g : Fin N → Nat)
    (htot0 : (Finset.univ.filter (fun w : Fin N => f w % 2 = 0)).card =
      (Finset.univ.filter (fun w : Fin N => g w % 2 = 0)).card)
    (htot1 : (Finset.univ.filter (fun w : Fin N => f w % 2 = 1)).card =
      (Finset.univ.filter (fun w : Fin N => g w % 2 = 1)).card)
    (htail0 : ∀ k, (Finset.univ.filter (fun w : Fin N => f w % 2 = 0 ∧ k ≤ f w)).card ≤
      (Finset.univ.filter (fun w : Fin N => g w % 2 = 0 ∧ k ≤ g w)).card)
    (htail1 : ∀ k, (Finset.univ.filter (fun w : Fin N => f w % 2 = 1 ∧ k ≤ f w)).card ≤
      (Finset.univ.filter (fun w : Fin N => g w % 2 = 1 ∧ k ≤ g w)).card) :
    ∃ perm : Fin N ≃ Fin N, ∀ w : Fin N, f w ≤ g (perm w) ∧ f w % 2 = g (perm w) % 2 := by
  let Sf0 := Finset.univ.filter (fun w : Fin N => f w % 2 = 0)
  let Sg0 := Finset.univ.filter (fun w : Fin N => g w % 2 = 0)
  let Sf1 := Finset.univ.filter (fun w : Fin N => f w % 2 = 1)
  let Sg1 := Finset.univ.filter (fun w : Fin N => g w % 2 = 1)
  have ht0 : ∀ k, (Sf0.filter (fun w => k ≤ f w)).card ≤ (Sg0.filter (fun w => k ≤ g w)).card := by
    intro k
    simpa only [Sf0, Sg0, Finset.filter_filter] using htail0 k
  have ht1 : ∀ k, (Sf1.filter (fun w => k ≤ f w)).card ≤ (Sg1.filter (fun w => k ≤ g w)).card := by
    intro k
    simpa only [Sf1, Sg1, Finset.filter_filter] using htail1 k
  obtain ⟨e0, he0⟩ := exists_equiv_of_same_card_sort f g Sf0 Sg0 htot0 ht0
  obtain ⟨e1, he1⟩ := exists_equiv_of_same_card_sort f g Sf1 Sg1 htot1 ht1
  let splitF : Fin N ≃ {w // w ∈ Sf0} ⊕ {w // w ∈ Sf1} :=
    { toFun := fun w => if h : f w % 2 = 0 then Sum.inl ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        else Sum.inr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
      invFun := fun s => Sum.elim Subtype.val Subtype.val s
      left_inv := fun w => by by_cases h : f w % 2 = 0 <;> simp [h]
      right_inv := fun s => by
        rcases s with ⟨w, hw⟩ | ⟨w, hw⟩
        · have h := (Finset.mem_filter.mp hw).2
          simp [h]
        · have h := (Finset.mem_filter.mp hw).2
          have hne : ¬ (f w % 2 = 0) := by omega
          simp [hne] }
  let splitG : Fin N ≃ {w // w ∈ Sg0} ⊕ {w // w ∈ Sg1} :=
    { toFun := fun w => if h : g w % 2 = 0 then Sum.inl ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        else Sum.inr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
      invFun := fun s => Sum.elim Subtype.val Subtype.val s
      left_inv := fun w => by by_cases h : g w % 2 = 0 <;> simp [h]
      right_inv := fun s => by
        rcases s with ⟨w, hw⟩ | ⟨w, hw⟩
        · have h := (Finset.mem_filter.mp hw).2
          simp [h]
        · have h := (Finset.mem_filter.mp hw).2
          have hne : ¬ (g w % 2 = 0) := by omega
          simp [hne] }
  let perm : Fin N ≃ Fin N := splitF.trans ((Equiv.sumCongr e0 e1).trans splitG.symm)
  refine ⟨perm, fun w => ?_⟩
  by_cases h : f w % 2 = 0
  · have hsf : splitF w = Sum.inl ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩ := by
      dsimp only [splitF]
      exact dite_eq_left h
    have hp : perm w = (e0 ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩).val := by
      change splitG.symm ((Equiv.sumCongr e0 e1) (splitF w)) = _
      rw [hsf]
      rfl
    rw [hp]
    refine ⟨he0 ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩, ?_⟩
    have hg0 := (Finset.mem_filter.mp (e0 ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩).2).2
    exact h.trans hg0.symm
  · have h1 : f w % 2 = 1 := by omega
    have hsf : splitF w = Sum.inr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩ := by
      dsimp only [splitF]
      exact dite_eq_right h
    have hp : perm w = (e1 ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩).val := by
      change splitG.symm ((Equiv.sumCongr e0 e1) (splitF w)) = _
      rw [hsf]
      rfl
    rw [hp]
    refine ⟨he1 ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩, ?_⟩
    have hg1 := (Finset.mem_filter.mp (e1 ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩⟩).2).2
    exact h1.trans hg1.symm

lemma exists_parity_perm (n : Nat) :
    ∃ perm : Fin (8 ^ n) ≃ Fin (8 ^ n), ∀ w : Fin (8 ^ n),
      gainFrom false 0 n w.val ≤ gainFrom true 0 n (perm w).val ∧
      gainFrom false 0 n w.val % 2 = gainFrom true 0 n (perm w).val % 2 :=
  exists_parity_perm_aux
    (fun w : Fin (8 ^ n) => gainFrom false 0 n w.val)
    (fun w : Fin (8 ^ n) => gainFrom true 0 n w.val)
    (parity_total_eq n 0 (by omega))
    (parity_total_eq n 1 (by omega))
    (fun k => parity_tail_le n 0 k (by omega))
    (fun k => parity_tail_le n 1 k (by omega))

def priceAux (keep : Bool) (n d : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun word => 2 ^ (2 * n - (gainFrom keep 0 n word - d)))).sum

lemma list_range_map_sum (M : Nat) (f : Nat → Nat) :
    ((List.range M).map f).sum = ∑ i ∈ Finset.range M, f i := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        Finset.sum_range_succ, ih]

lemma priceAux_eq_sum_coeff (keep : Bool) (n d : Nat) :
    priceAux keep n d =
      ∑ g ∈ Finset.range (2 * n + 1), (F keep 0 n).coeff g * 2 ^ (2 * n - (g - d)) := by
  unfold priceAux
  rw [list_range_map_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range (8 ^ n)) (t := Finset.range (2 * n + 1))
    (g := fun w => gainFrom keep 0 n w)]
  · refine Finset.sum_congr rfl fun g _ => ?_
    rw [F_coeff_eq_card]
    have hcongr : ∑ w ∈ Finset.filter (fun w => gainFrom keep 0 n w = g) (Finset.range (8 ^ n)),
        2 ^ (2 * n - (gainFrom keep 0 n w - d)) =
        ∑ _w ∈ Finset.filter (fun w => gainFrom keep 0 n w = g) (Finset.range (8 ^ n)),
        2 ^ (2 * n - (g - d)) := by
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [(Finset.mem_filter.mp hw).2]
    rw [hcongr, Finset.sum_const, smul_eq_mul]
  · intro w _
    exact Finset.mem_range.mpr (by have := gainFrom_le keep 0 n w; omega)

lemma price_identity (n d : Nat) :
    priceAux true n d +
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g - d)) =
      priceAux false n d +
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g + 2 - d)) := by
  rw [priceAux_eq_sum_coeff true, priceAux_eq_sum_coeff false]
  have hsum :
      ∑ g ∈ Finset.range (2 * n + 1),
        ((F true 0 n).coeff g + (Rpoly n).coeff g) * 2 ^ (2 * n - (g - d)) =
      ∑ g ∈ Finset.range (2 * n + 1),
        ((F false 0 n).coeff g + (if 2 ≤ g then (Rpoly n).coeff (g - 2) else 0)) *
          2 ^ (2 * n - (g - d)) := by
    refine Finset.sum_congr rfl fun g _ => by rw [golden_coeff n g]
  simp only [Nat.add_mul, Finset.sum_add_distrib] at hsum
  have hL :
      ∑ g ∈ Finset.range (2 * n + 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g - d)) =
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g - d)) := by
    cases n with
    | zero =>
      simp [Rpoly_zero_of_lt_four]
    | succ m =>
      have h1 : 2 * (m + 1) + 1 = (2 * (m + 1) - 1) + 2 := by omega
      rw [h1, Finset.sum_range_succ, Finset.sum_range_succ]
      have hz1 : (Rpoly (m + 1)).coeff (2 * (m + 1) - 1) = 0 := Rpoly_coeff_zero_of_ge le_rfl
      have hz2 : (Rpoly (m + 1)).coeff (2 * (m + 1) - 1 + 1) = 0 := Rpoly_coeff_zero_of_ge (by omega)
      rw [hz1, hz2]
      simp
  have hR :
      ∑ g ∈ Finset.range (2 * n + 1),
          (if 2 ≤ g then (Rpoly n).coeff (g - 2) else 0) * 2 ^ (2 * n - (g - d)) =
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g + 2 - d)) := by
    cases n with
    | zero =>
      simp [Rpoly_zero_of_lt_four]
    | succ m =>
      have h1 : 2 * (m + 1) + 1 = (2 * (m + 1) - 1) + 2 := by omega
      rw [h1, Finset.sum_range_succ', Finset.sum_range_succ']
      have h0lt : ¬ (2 ≤ 0) := by omega
      have h1lt : ¬ (2 ≤ 1) := by omega
      simp only [h0lt, h1lt, ↓reduceIte, zero_mul, add_zero]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hge : 2 ≤ g + 1 + 1 := by omega
      have hsub : g + 1 + 1 - 2 = g := by omega
      have hadd : g + 1 + 1 = g + 2 := by omega
      rw [ite_eq_left hge, hsub, hadd]
  rw [hL, hR] at hsum
  exact hsum

lemma price_le_and_lt_iff (n d : Nat) :
    priceAux true n d ≤ priceAux false n d ∧
      (priceAux true n d < priceAux false n d ↔ 4 ≤ n ∧ d + 2 < 3 * n / 2) := by
  have hid := price_identity n d
  have hterm_le : ∀ g ∈ Finset.range (2 * n - 1),
      (Rpoly n).coeff g * 2 ^ (2 * n - (g + 2 - d)) ≤
      (Rpoly n).coeff g * 2 ^ (2 * n - (g - d)) := by
    intro g _
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) ?_)
    omega
  have hsum_le := Finset.sum_le_sum hterm_le
  refine ⟨by omega, ?_⟩
  constructor
  · intro hlt
    have hsum_lt :
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g + 2 - d)) <
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g - d)) := by omega
    by_contra hnot
    have heq :
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g + 2 - d)) =
        ∑ g ∈ Finset.range (2 * n - 1), (Rpoly n).coeff g * 2 ^ (2 * n - (g - d)) := by
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hn4 : 4 ≤ n
      · have hd : 3 * n / 2 ≤ d + 2 := by omega
        by_cases hg : 3 * n / 2 - 4 < g
        · rw [Rpoly_coeff_zero_of_gt hn4 hg, zero_mul, zero_mul]
        · have hsub1 : g + 2 - d = 0 := by omega
          have hsub2 : g - d = 0 := by omega
          rw [hsub1, hsub2]
      · rw [Rpoly_zero_of_lt_four (by omega), Polynomial.coeff_zero, zero_mul, zero_mul]
    omega
  · rintro ⟨hn4, hd⟩
    let g0 := 3 * n / 2 - 4
    have hg0_mem : g0 ∈ Finset.range (2 * n - 1) := Finset.mem_range.mpr (by omega)
    have hpos : 0 < (Rpoly n).coeff g0 := Rpoly_top_pos hn4
    have hpow_lt : 2 ^ (2 * n - (g0 + 2 - d)) < 2 ^ (2 * n - (g0 - d)) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hterm_lt :
        (Rpoly n).coeff g0 * 2 ^ (2 * n - (g0 + 2 - d)) <
        (Rpoly n).coeff g0 * 2 ^ (2 * n - (g0 - d)) :=
      Nat.mul_lt_mul_of_pos_left hpow_lt hpos
    have hsum_lt := Finset.sum_lt_sum hterm_le ⟨g0, hg0_mem, hterm_lt⟩
    omega

end

end PEqualNP.Outside.L_meta_25590_aux

theorem PEqualNP.Outside.L_meta_25590 : (let move := fun (keep : Bool) (mode letter : Nat) =>
  let near := letter.testBit 0
  let far := letter.testBit 1
  let hit := letter.testBit 2
  let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
    ((mode == 3) && near)
  let diagonal := (!hit && (((mode == 1) && !near && !far) ||
    (mode == 2) || (mode == 3))) || (keep && (mode == 3))
  (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
    hit.toNat + (aligned && hit).toNat)
let gain := fun (keep : Bool) (n code : Nat) =>
  ((List.range n).foldl (fun (st : Nat × Nat) pos =>
    let nxt := move keep st.1 ((code >>> (3*pos)) % 8)
    (nxt.1, st.2 + nxt.2)) (0,0)).2
let price := fun (keep : Bool) (n d : Nat) =>
  ((List.range (8^n)).map (fun word => 2^(2*n - (gain keep n word - d)))).sum
∀ n : Nat,
  (∃ perm : Fin (8^n) ≃ Fin (8^n), ∀ w : Fin (8^n),
    gain false n w.val ≤ gain true n (perm w).val ∧
    gain false n w.val % 2 = gain true n (perm w).val % 2) ∧
  ∀ d : Nat, price true n d ≤ price false n d ∧
    (price true n d < price false n d ↔ 4 ≤ n ∧ d+2 < 3*n/2)) := by
  intro move gain price n
  exact ⟨PEqualNP.Outside.L_meta_25590_aux.exists_parity_perm n,
    fun d => PEqualNP.Outside.L_meta_25590_aux.price_le_and_lt_iff n d⟩
