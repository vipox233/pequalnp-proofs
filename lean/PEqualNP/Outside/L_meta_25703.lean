import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25703_aux

def chi (b : Bool) : ℤ := if b then -1 else 1

theorem chi_false : chi false = 1 := by simp [chi]
theorem chi_true : chi true = -1 := by simp [chi]
theorem chi_sq (b : Bool) : chi b * chi b = 1 := by cases b <;> simp [chi]
theorem chi_xor (b c : Bool) : chi (xor b c) = chi b * chi c := by
  cases b <;> cases c <;> simp [chi]

theorem two_pow_mul_fact_le (j : ℕ) : 2 ^ j * j.factorial ≤ (2 * j).factorial := by
  induction j with
  | zero => simp
  | succ j ih =>
    have e : 2 * (j + 1) = (2 * j + 1) + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
    calc 2 ^ j * 2 * ((j + 1) * j.factorial) = (2 * j + 1 + 1) * (2 ^ j * j.factorial) := by ring
      _ ≤ (2 * j + 1 + 1) * (2 * j).factorial := Nat.mul_le_mul_left _ ih
      _ ≤ (2 * j + 1 + 1) * ((2 * j + 1) * (2 * j).factorial) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))

theorem sum_even_odd (f : ℕ → ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m + 1), f i =
      ∑ j ∈ Finset.range (m + 1), f (2 * j) + ∑ j ∈ Finset.range m, f (2 * j + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ f (2 * m + 1 + 1), Finset.sum_range_succ f (2 * m + 1), ih,
      Finset.sum_range_succ (fun j => f (2 * j)) (m + 1),
      Finset.sum_range_succ (fun j => f (2 * j + 1)) m]
    have e1 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
    rw [e1]
    ring

theorem sum_even_only (f : ℕ → ℤ) (m : ℕ) (hodd : ∀ j, f (2 * j + 1) = 0) :
    ∑ i ∈ Finset.range (2 * m + 1), f i = ∑ j ∈ Finset.range (m + 1), f (2 * j) := by
  rw [sum_even_odd, Finset.sum_eq_zero (fun j _ => hodd j), add_zero]

theorem even_expand (s c : ℤ) (m : ℕ) :
    (s + c) ^ (2 * m) + (s - c) ^ (2 * m) =
      2 * ∑ j ∈ Finset.range (m + 1),
        ((2 * m).choose (2 * j) : ℤ) * s ^ (2 * m - 2 * j) * c ^ (2 * j) := by
  have h1 : (s + c) ^ (2 * m) =
      ∑ i ∈ Finset.range (2 * m + 1), c ^ i * s ^ (2 * m - i) * ((2 * m).choose i : ℤ) := by
    rw [add_comm, add_pow]
  have h2 : (s - c) ^ (2 * m) =
      ∑ i ∈ Finset.range (2 * m + 1), (-c) ^ i * s ^ (2 * m - i) * ((2 * m).choose i : ℤ) := by
    rw [sub_eq_add_neg, add_comm, add_pow]
  rw [h1, h2, ← Finset.sum_add_distrib, Finset.mul_sum]
  rw [sum_even_only (fun i => c ^ i * s ^ (2 * m - i) * ((2 * m).choose i : ℤ) +
    (-c) ^ i * s ^ (2 * m - i) * ((2 * m).choose i : ℤ)) m (by
      intro j
      rw [Odd.neg_pow ⟨j, rfl⟩]
      ring)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Even.neg_pow ⟨j, by ring⟩]
  ring

theorem khin (t : ℕ) : ∀ (m : ℕ) (c : ℕ → ℤ),
    (2 : ℤ) ^ m * (m.factorial : ℤ) *
        ∑ x ∈ Finset.range (2 ^ t), (∑ l ∈ Finset.range t, c l * chi (x.testBit l)) ^ (2 * m)
      ≤ (2 : ℤ) ^ t * ((2 * m).factorial : ℤ) * (∑ l ∈ Finset.range t, c l ^ 2) ^ m := by
  induction t with
  | zero =>
    intro m c
    cases m with
    | zero => simp
    | succ m => simp
  | succ t ih =>
    intro m c
    have hsplit : ∑ x ∈ Finset.range (2 ^ (t + 1)),
          (∑ l ∈ Finset.range (t + 1), c l * chi (x.testBit l)) ^ (2 * m)
        = ∑ y ∈ Finset.range (2 ^ t),
          ((∑ l ∈ Finset.range t, c l * chi (y.testBit l) + c t) ^ (2 * m) +
           (∑ l ∈ Finset.range t, c l * chi (y.testBit l) - c t) ^ (2 * m)) := by
      have e : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by ring
      rw [e, Finset.sum_range_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      have hy' : y < 2 ^ t := Finset.mem_range.1 hy
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have b1 : y.testBit t = false := Nat.testBit_lt_two_pow hy'
      have b2 : (2 ^ t + y).testBit t = true := by
        rw [Nat.testBit_two_pow_add_eq, b1]; rfl
      have b3 : ∀ l ∈ Finset.range t,
          c l * chi ((2 ^ t + y).testBit l) = c l * chi (y.testBit l) := by
        intro l hl
        rw [Nat.testBit_two_pow_add_gt (Finset.mem_range.1 hl)]
      rw [Finset.sum_congr rfl b3, b1, b2, chi_false, chi_true, mul_one, mul_neg, mul_one,
        ← sub_eq_add_neg]
    rw [hsplit, Finset.sum_range_succ]
    have hσ : 0 ≤ ∑ l ∈ Finset.range t, c l ^ 2 :=
      Finset.sum_nonneg (fun l _ => sq_nonneg (c l))
    have h1 : ∑ y ∈ Finset.range (2 ^ t),
          ((∑ l ∈ Finset.range t, c l * chi (y.testBit l) + c t) ^ (2 * m) +
           (∑ l ∈ Finset.range t, c l * chi (y.testBit l) - c t) ^ (2 * m))
        = 2 * ∑ j ∈ Finset.range (m + 1), ((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j) *
            ∑ y ∈ Finset.range (2 ^ t),
              (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j) := by
      calc _ = ∑ y ∈ Finset.range (2 ^ t), 2 * ∑ j ∈ Finset.range (m + 1),
              ((2 * m).choose (2 * j) : ℤ) *
                (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j) *
                c t ^ (2 * j) := Finset.sum_congr rfl (fun y _ => even_expand _ _ m)
        _ = 2 * ∑ y ∈ Finset.range (2 ^ t), ∑ j ∈ Finset.range (m + 1),
              ((2 * m).choose (2 * j) : ℤ) *
                (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j) *
                c t ^ (2 * j) := by rw [Finset.mul_sum]
        _ = 2 * ∑ j ∈ Finset.range (m + 1), ∑ y ∈ Finset.range (2 ^ t),
              ((2 * m).choose (2 * j) : ℤ) *
                (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j) *
                c t ^ (2 * j) := by rw [Finset.sum_comm]
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          ring
    have hterm : ∀ j ∈ Finset.range (m + 1),
        (2 : ℤ) ^ m * (m.factorial : ℤ) * (((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j) *
            ∑ y ∈ Finset.range (2 ^ t),
              (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j))
          ≤ (2 : ℤ) ^ t * ((2 * m).factorial : ℤ) *
            ((c t ^ 2) ^ j * (∑ l ∈ Finset.range t, c l ^ 2) ^ (m - j) * (m.choose j : ℤ)) := by
      intro j hj
      have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have e3 : 2 * m - 2 * j = 2 * (m - j) := by omega
      rw [e3]
      have IH := ih (m - j) c
      have hc : 0 ≤ c t ^ (2 * j) := Even.pow_nonneg ⟨j, by ring⟩ _
      have e1 : (2 : ℤ) ^ m = 2 ^ j * 2 ^ (m - j) := by
        rw [← pow_add]; congr 1; omega
      have e2 : (m.factorial : ℤ) =
          (m.choose j : ℤ) * (j.factorial : ℤ) * ((m - j).factorial : ℤ) := by
        exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjm).symm
      have hN : 2 ^ j * j.factorial * (2 * m).choose (2 * j) * (2 * (m - j)).factorial
          ≤ (2 * m).factorial := by
        have h2 : (2 * m).choose (2 * j) * (2 * j).factorial * (2 * m - 2 * j).factorial
            = (2 * m).factorial := Nat.choose_mul_factorial_mul_factorial (by omega)
        rw [e3] at h2
        calc 2 ^ j * j.factorial * (2 * m).choose (2 * j) * (2 * (m - j)).factorial
            ≤ (2 * j).factorial * (2 * m).choose (2 * j) * (2 * (m - j)).factorial :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (two_pow_mul_fact_le j))
          _ = (2 * m).factorial := by rw [← h2]; ring
      have hZ : (2 : ℤ) ^ j * (j.factorial : ℤ) * ((2 * m).choose (2 * j) : ℤ) *
          ((2 * (m - j)).factorial : ℤ) ≤ ((2 * m).factorial : ℤ) := by exact_mod_cast hN
      have hβ : 0 ≤ (2 : ℤ) ^ j * (m.choose j : ℤ) * (j.factorial : ℤ) *
          ((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j) := by positivity
      have hnn : 0 ≤ (2 : ℤ) ^ t * (m.choose j : ℤ) * c t ^ (2 * j) *
          (∑ l ∈ Finset.range t, c l ^ 2) ^ (m - j) := by positivity
      calc (2 : ℤ) ^ m * (m.factorial : ℤ) * (((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j) *
            ∑ y ∈ Finset.range (2 ^ t),
              (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * (m - j)))
          = ((2 : ℤ) ^ j * (m.choose j : ℤ) * (j.factorial : ℤ) *
              ((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j)) *
            ((2 : ℤ) ^ (m - j) * ((m - j).factorial : ℤ) * ∑ y ∈ Finset.range (2 ^ t),
              (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * (m - j))) := by
            rw [e1, e2]; ring
        _ ≤ ((2 : ℤ) ^ j * (m.choose j : ℤ) * (j.factorial : ℤ) *
              ((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j)) *
            ((2 : ℤ) ^ t * ((2 * (m - j)).factorial : ℤ) *
              (∑ l ∈ Finset.range t, c l ^ 2) ^ (m - j)) := mul_le_mul_of_nonneg_left IH hβ
        _ = ((2 : ℤ) ^ t * (m.choose j : ℤ) * c t ^ (2 * j) *
              (∑ l ∈ Finset.range t, c l ^ 2) ^ (m - j)) *
            ((2 : ℤ) ^ j * (j.factorial : ℤ) * ((2 * m).choose (2 * j) : ℤ) *
              ((2 * (m - j)).factorial : ℤ)) := by ring
        _ ≤ ((2 : ℤ) ^ t * (m.choose j : ℤ) * c t ^ (2 * j) *
              (∑ l ∈ Finset.range t, c l ^ 2) ^ (m - j)) * ((2 * m).factorial : ℤ) :=
            mul_le_mul_of_nonneg_left hZ hnn
        _ = _ := by rw [← pow_mul]; ring
    rw [h1]
    calc (2 : ℤ) ^ m * (m.factorial : ℤ) * (2 * ∑ j ∈ Finset.range (m + 1),
            ((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j) *
              ∑ y ∈ Finset.range (2 ^ t),
                (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j))
        = 2 * ∑ j ∈ Finset.range (m + 1), (2 : ℤ) ^ m * (m.factorial : ℤ) *
            (((2 * m).choose (2 * j) : ℤ) * c t ^ (2 * j) *
              ∑ y ∈ Finset.range (2 ^ t),
                (∑ l ∈ Finset.range t, c l * chi (y.testBit l)) ^ (2 * m - 2 * j)) := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ ≤ 2 * ∑ j ∈ Finset.range (m + 1), (2 : ℤ) ^ t * ((2 * m).factorial : ℤ) *
            ((c t ^ 2) ^ j * (∑ l ∈ Finset.range t, c l ^ 2) ^ (m - j) * (m.choose j : ℤ)) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
      _ = _ := by
          rw [← Finset.mul_sum, add_comm (∑ l ∈ Finset.range t, c l ^ 2) (c t ^ 2), add_pow]
          ring

theorem fact_add_le (a : ℕ) : ∀ b, (a + b).factorial ≤ a.factorial * (a + b) ^ b := by
  intro b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, Nat.factorial_succ, pow_succ]
    calc (a + b + 1) * (a + b).factorial
        ≤ (a + b + 1) * (a.factorial * (a + b) ^ b) := Nat.mul_le_mul_left _ ih
      _ ≤ (a + b + 1) * (a.factorial * (a + b + 1) ^ b) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) b))
      _ = a.factorial * ((a + b + 1) ^ b * (a + b + 1)) := by ring

theorem level1 (k a : ℕ) (ha : 0 < a) (hak : a ≤ k) (Kj : Finset (Fin (2 ^ k)))
    (e : Fin (2 ^ k) → ℤ) (he : ∀ x, e x * e x = 1) (hK : Kj.card ≤ 2 ^ (k - a)) :
    ∑ l ∈ Finset.range k, (∑ x ∈ Kj, e x * chi (x.val.testBit l)) ^ 2
      ≤ 2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2 := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℤ, M = fun l => ∑ x ∈ Kj, e x * chi (x.val.testBit l) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ → ℤ,
      L = fun x => ∑ l ∈ Finset.range k, M l * chi (x.testBit l) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℤ, W = ∑ l ∈ Finset.range k, M l ^ 2 := ⟨_, rfl⟩
  have hMl : ∀ l, M l = ∑ x ∈ Kj, e x * chi (x.val.testBit l) := by intro l; rw [hM]
  have hLx : ∀ x, L x = ∑ l ∈ Finset.range k, M l * chi (x.testBit l) := by intro x; rw [hL]
  have hgoal : ∑ l ∈ Finset.range k, (∑ x ∈ Kj, e x * chi (x.val.testBit l)) ^ 2 = W := by
    rw [hW]
    apply Finset.sum_congr rfl
    intro l _
    rw [hMl]
  rw [hgoal]
  have hW0 : 0 ≤ W := by rw [hW]; exact Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have h1 : W = ∑ x ∈ Kj, e x * L x.val := by
    rw [hW]
    calc ∑ l ∈ Finset.range k, M l ^ 2
        = ∑ l ∈ Finset.range k, ∑ x ∈ Kj, e x * (M l * chi (x.val.testBit l)) := by
          apply Finset.sum_congr rfl
          intro l _
          rw [sq]
          nth_rewrite 2 [hMl l]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = ∑ x ∈ Kj, ∑ l ∈ Finset.range k, e x * (M l * chi (x.val.testBit l)) :=
          Finset.sum_comm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hLx, Finset.mul_sum]
  have hLabs : W ≤ ∑ x ∈ Kj, |L x.val| := by
    rw [h1]
    apply Finset.sum_le_sum
    intro x _
    rcases mul_self_eq_one_iff.1 (he x) with h | h
    · rw [h, one_mul]; exact le_abs_self _
    · rw [h, neg_one_mul]; exact neg_le_abs _
  have h2 : W ^ (2 * a) ≤ (Kj.card : ℤ) ^ (2 * a - 1) * ∑ x ∈ Kj, L x.val ^ (2 * a) := by
    have e2a : 2 * a - 1 + 1 = 2 * a := by omega
    have hp := pow_sum_le_card_mul_sum_pow (s := Kj) (f := fun x => |L x.val|)
      (fun x _ => abs_nonneg _) (2 * a - 1)
    rw [e2a] at hp
    calc W ^ (2 * a) ≤ (∑ x ∈ Kj, |L x.val|) ^ (2 * a) := pow_le_pow_left₀ hW0 hLabs _
      _ ≤ (Kj.card : ℤ) ^ (2 * a - 1) * ∑ x ∈ Kj, |L x.val| ^ (2 * a) := hp
      _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          exact Even.pow_abs ⟨a, by ring⟩ _
  have h3 : ∑ x ∈ Kj, L x.val ^ (2 * a) ≤ ∑ x ∈ Finset.range (2 ^ k), L x ^ (2 * a) := by
    rw [← Fin.sum_univ_eq_sum_range (fun x => L x ^ (2 * a)) (2 ^ k)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun x => Even.pow_nonneg ⟨a, by ring⟩ _)
  have h4 : (2 : ℤ) ^ a * (a.factorial : ℤ) * ∑ x ∈ Finset.range (2 ^ k), L x ^ (2 * a)
      ≤ (2 : ℤ) ^ k * ((2 * a).factorial : ℤ) * W ^ a := by
    have hk := khin k a M
    rw [hW]
    simp only [hLx]
    exact hk
  have hfac : ((2 * a).factorial : ℤ) ≤ (a.factorial : ℤ) * (2 * (a : ℤ)) ^ a := by
    have hf := fact_add_le a a
    rw [← two_mul] at hf
    exact_mod_cast hf
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = (2 : ℤ) ^ (k - a) := ⟨_, rfl⟩
  rw [← hX]
  have hX0 : 0 < X := by rw [hX]; positivity
  have h2k : (2 : ℤ) ^ k = X * 2 ^ a := by rw [hX, ← pow_add]; congr 1; omega
  have hcard : (Kj.card : ℤ) ≤ X := by rw [hX]; exact_mod_cast hK
  generalize hS2def : ∑ x ∈ Finset.range (2 ^ k), L x ^ (2 * a) = S2 at h3 h4
  have hWa : 0 ≤ W ^ a := pow_nonneg hW0 a
  have hS2 : S2 ≤ X * (2 * (a : ℤ)) ^ a * W ^ a := by
    have h5 : (2 : ℤ) ^ a * (a.factorial : ℤ) * S2
        ≤ (2 : ℤ) ^ a * (a.factorial : ℤ) * (X * (2 * (a : ℤ)) ^ a * W ^ a) := by
      calc (2 : ℤ) ^ a * (a.factorial : ℤ) * S2
          ≤ (2 : ℤ) ^ k * ((2 * a).factorial : ℤ) * W ^ a := h4
        _ ≤ (2 : ℤ) ^ k * ((a.factorial : ℤ) * (2 * (a : ℤ)) ^ a) * W ^ a := by
            apply mul_le_mul_of_nonneg_right _ hWa
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
        _ = _ := by rw [h2k]; ring
    have hpos : (0 : ℤ) < (2 : ℤ) ^ a * (a.factorial : ℤ) := by positivity
    exact le_of_mul_le_mul_left h5 hpos
  have h6 : W ^ (2 * a) ≤ X ^ (2 * a) * (2 * (a : ℤ)) ^ a * W ^ a := by
    have hS1 : 0 ≤ ∑ x ∈ Kj, L x.val ^ (2 * a) :=
      Finset.sum_nonneg (fun x _ => Even.pow_nonneg ⟨a, by ring⟩ _)
    calc W ^ (2 * a) ≤ (Kj.card : ℤ) ^ (2 * a - 1) * ∑ x ∈ Kj, L x.val ^ (2 * a) := h2
      _ ≤ X ^ (2 * a - 1) * ∑ x ∈ Kj, L x.val ^ (2 * a) := by
          apply mul_le_mul_of_nonneg_right _ hS1
          exact pow_le_pow_left₀ (by positivity) hcard _
      _ ≤ X ^ (2 * a - 1) * S2 := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ X ^ (2 * a - 1) * (X * (2 * (a : ℤ)) ^ a * W ^ a) :=
          mul_le_mul_of_nonneg_left hS2 (by positivity)
      _ = _ := by
          have hx : X ^ (2 * a) = X ^ (2 * a - 1) * X := by
            rw [← pow_succ]; congr 1; omega
          rw [hx]; ring
  by_contra hcon
  have hcon' : 2 * (a : ℤ) * X ^ 2 < W := not_le.1 hcon
  have hWpos : 0 < W := lt_of_le_of_lt (by positivity) hcon'
  have h7 : (2 * (a : ℤ) * X ^ 2) ^ a < W ^ a :=
    pow_lt_pow_left₀ hcon' (by positivity) (by omega)
  have h8 : W ^ (2 * a) = W ^ a * W ^ a := by rw [← pow_add]; congr 1; omega
  rw [h8] at h6
  have h9 : W ^ a ≤ X ^ (2 * a) * (2 * (a : ℤ)) ^ a :=
    le_of_mul_le_mul_right h6 (pow_pos hWpos a)
  have h10 : X ^ (2 * a) * (2 * (a : ℤ)) ^ a = (2 * (a : ℤ) * X ^ 2) ^ a := by
    have hx2 : (X ^ 2) ^ a = X ^ (2 * a) := (pow_mul X 2 a).symm
    rw [mul_pow (2 * (a : ℤ)) (X ^ 2) a, hx2]; ring
  rw [h10] at h9
  exact absurd h7 (not_lt.2 h9)

def maskF {N : ℕ} (keep : Finset (Fin N)) (i j : Fin N) : Finset (Fin N) :=
  if i = j then (if i ∈ keep then ({i} : Finset (Fin N)) else ∅) else {i, j}

def tgt {N : ℕ} (G : Fin N → Fin N → Bool) (π : Equiv.Perm (Fin N)) (f g : Fin N → Bool)
    (z : Fin N × Fin N) : Bool :=
  xor (G z.1 (π z.2)) (xor (f z.1) (g z.2))

def errs {N : ℕ} (G : Fin N → Fin N → Bool) (π : Equiv.Perm (Fin N))
    (keep rows cols : Finset (Fin N)) (f g : Fin N → Bool)
    (decode : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun z : Fin N × Fin N =>
    decode (maskF keep z.1 z.2) (rows ∩ {z.1}) (cols ∩ {z.2}) ≠ tgt G π f g z)

theorem fiber_card (k a : ℕ) (hak : a ≤ k) (π : Equiv.Perm (Fin (2 ^ k)))
    (K : Finset (Fin (2 ^ k))) (j : ℕ) :
    (K.filter (fun x => (π x).val % 2 ^ a = j)).card ≤ 2 ^ (k - a) := by
  have h2k : 2 ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← pow_add]; congr 1; omega
  have hle := Finset.card_le_card_of_injOn (s := K.filter (fun x => (π x).val % 2 ^ a = j))
    (t := Finset.range (2 ^ (k - a))) (fun x => (π x).val / 2 ^ a)
    (by
      intro x _
      rw [Finset.mem_coe, Finset.mem_range]
      apply Nat.div_lt_of_lt_mul
      rw [← h2k]
      exact (π x).isLt)
    (by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter] at hx hy
      have hxy' : (π x).val / 2 ^ a = (π y).val / 2 ^ a := hxy
      have e1 := Nat.div_add_mod (π x).val (2 ^ a)
      have e2 := Nat.div_add_mod (π y).val (2 ^ a)
      rw [hx.2, hxy'] at e1
      rw [hy.2] at e2
      exact π.injective (Fin.ext (e1.symm.trans e2)))
  rwa [Finset.card_range] at hle

theorem part1 (k a : ℕ) (ha : 0 < a) (hk : 2 ^ a ≤ k)
    (G : Fin (2 ^ k) → Fin (2 ^ k) → Bool) (A B : Finset (Fin (2 ^ k)))
    (hG : ∀ x ∉ A, ∀ y ∉ B, G x y = x.val.testBit (y.val % 2 ^ a))
    (π : Equiv.Perm (Fin (2 ^ k)))
    (U R C : Finset (Fin (2 ^ k))) (f g : Fin (2 ^ k) → Bool)
    (D : Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k)) → Finset (Fin (2 ^ k)) → Bool) :
    2 ^ a * ((Finset.univ \ (R ∪ C)).filter (fun z => z ∉ A ∧ π z ∉ B)).card ^ 2
      ≤ 4 * 2 ^ a * (errs G π U R C f g D).card + 2 * a * (2 ^ k) ^ 2 := by
  have hak : a ≤ k := le_trans (Nat.lt_two_pow_self).le hk
  obtain ⟨K, hKdef⟩ : ∃ K : Finset (Fin (2 ^ k)),
      K = (Finset.univ \ (R ∪ C)).filter (fun z => z ∉ A ∧ π z ∉ B) := ⟨_, rfl⟩
  rw [← hKdef]
  have hKmem : ∀ z ∈ K, z ∉ R ∧ z ∉ C ∧ z ∉ A ∧ π z ∉ B := by
    intro z hz
    rw [hKdef, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_union] at hz
    tauto
  obtain ⟨E, hE⟩ : ∃ E : Finset (Fin (2 ^ k) × Fin (2 ^ k)), E = errs G π U R C f g D :=
    ⟨_, rfl⟩
  rw [← hE]
  obtain ⟨T, hT⟩ : ∃ T : Fin (2 ^ k) × Fin (2 ^ k) → Bool, T = tgt G π f g := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I : Finset (Fin (2 ^ k) × Fin (2 ^ k)),
      I = (K ×ˢ K).filter (fun z => T z ≠ T z.swap) := ⟨_, rfl⟩
  have hEmem : ∀ z : Fin (2 ^ k) × Fin (2 ^ k), z ∉ E →
      D (maskF U z.1 z.2) (R ∩ {z.1}) (C ∩ {z.2}) = T z := by
    intro z hz
    by_contra h
    apply hz
    rw [hE, errs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [← hT]; exact h⟩

  have hA : I ⊆ E ∪ E.image Prod.swap := by
    intro z hz
    rw [hI, Finset.mem_filter, Finset.mem_product] at hz
    obtain ⟨⟨h1, h2⟩, hne⟩ := hz
    have hz12 : z.1 ≠ z.2 := by
      intro h
      apply hne
      have hs : z.swap = z := Prod.ext h.symm h
      rw [hs]
    obtain ⟨r1, c1, -, -⟩ := hKmem z.1 h1
    obtain ⟨r2, c2, -, -⟩ := hKmem z.2 h2
    by_contra hnot
    rw [Finset.mem_union, not_or] at hnot
    obtain ⟨n1, n2⟩ := hnot
    have m1 := hEmem z n1
    have n2' : z.swap ∉ E := by
      intro h
      apply n2
      rw [Finset.mem_image]
      exact ⟨z.swap, h, Prod.swap_swap z⟩
    have m2 : D (maskF U z.2 z.1) (R ∩ {z.2}) (C ∩ {z.1}) = T z.swap := hEmem z.swap n2'
    have e1 : maskF U z.1 z.2 = maskF U z.2 z.1 := by
      simp only [maskF, if_neg hz12, if_neg (Ne.symm hz12)]
      exact Finset.pair_comm _ _
    have e2 : R ∩ {z.1} = R ∩ {z.2} := by
      rw [Finset.inter_singleton_of_notMem r1, Finset.inter_singleton_of_notMem r2]
    have e3 : C ∩ {z.2} = C ∩ {z.1} := by
      rw [Finset.inter_singleton_of_notMem c1, Finset.inter_singleton_of_notMem c2]
    apply hne
    rw [← m1, ← m2, e1, e2, e3]
  have hIcard : (I.card : ℤ) ≤ 2 * (E.card : ℤ) := by
    have h1 := Finset.card_le_card hA
    have h2 := Finset.card_union_le E (E.image Prod.swap)
    have h3 := Finset.card_image_le (s := E) (f := Prod.swap)
    have h4 : I.card ≤ 2 * E.card := by omega
    exact_mod_cast h4

  have hB : ∑ z ∈ K ×ˢ K, chi (xor (T z) (T z.swap)) = (K.card : ℤ) ^ 2 - 2 * (I.card : ℤ) := by
    have hpt : ∀ z : Fin (2 ^ k) × Fin (2 ^ k),
        chi (xor (T z) (T z.swap)) = 1 - 2 * (if T z ≠ T z.swap then (1 : ℤ) else 0) := by
      intro z
      cases T z <;> cases T z.swap <;> simp [chi]
    rw [Finset.sum_congr rfl (fun z _ => hpt z), Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_boole, hI]
    simp [Finset.card_product, sq]
  obtain ⟨cc, hcc⟩ : ∃ cc : Fin (2 ^ k) → ℕ, cc = fun z => (π z).val % 2 ^ a := ⟨_, rfl⟩
  have hccz : ∀ z, cc z = (π z).val % 2 ^ a := by intro z; rw [hcc]
  have hccr : ∀ z, cc z ∈ Finset.range (2 ^ a) := by
    intro z
    rw [hccz, Finset.mem_range]
    exact Nat.mod_lt _ (by positivity)
  obtain ⟨Ee, hEe⟩ : ∃ Ee : Fin (2 ^ k) → ℤ, Ee = fun x => chi (f x) * chi (g x) := ⟨_, rfl⟩
  have hEex : ∀ x, Ee x = chi (f x) * chi (g x) := by intro x; rw [hEe]
  have hEe1 : ∀ x, Ee x * Ee x = 1 := by
    intro x
    rw [hEex]
    calc chi (f x) * chi (g x) * (chi (f x) * chi (g x))
        = (chi (f x) * chi (f x)) * (chi (g x) * chi (g x)) := by ring
      _ = 1 := by rw [chi_sq, chi_sq]; ring
  obtain ⟨F, hF⟩ : ∃ F : Fin (2 ^ k) → Fin (2 ^ k) → ℤ,
      F = fun x y => (Ee x * chi (x.val.testBit (cc y))) * (Ee y * chi (y.val.testBit (cc x))) :=
    ⟨_, rfl⟩
  have hFxy : ∀ x y, F x y =
      (Ee x * chi (x.val.testBit (cc y))) * (Ee y * chi (y.val.testBit (cc x))) := by
    intro x y; rw [hF]
  have hC : ∑ z ∈ K ×ˢ K, chi (xor (T z) (T z.swap)) = ∑ x ∈ K, ∑ y ∈ K, F x y := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    obtain ⟨-, -, ax, bx⟩ := hKmem x hx
    obtain ⟨-, -, ay, bY⟩ := hKmem y hy
    have g1 : G x (π y) = x.val.testBit (cc y) := by rw [hccz]; exact hG x ax (π y) bY
    have g2 : G y (π x) = y.val.testBit (cc x) := by rw [hccz]; exact hG y ay (π x) bx
    have t1 : T (x, y) = xor (x.val.testBit (cc y)) (xor (f x) (g y)) := by
      rw [hT, ← g1]; rfl
    have t2 : T (x, y).swap = xor (y.val.testBit (cc x)) (xor (f y) (g x)) := by
      rw [hT, ← g2]; rfl
    rw [t1, t2, chi_xor, chi_xor, chi_xor, chi_xor, chi_xor, hFxy, hEex, hEex]
    ring
  obtain ⟨Mm, hMm⟩ : ∃ Mm : ℕ → ℕ → ℤ, Mm = fun j l =>
      ∑ x ∈ K.filter (fun x => cc x = j), Ee x * chi (x.val.testBit l) := ⟨_, rfl⟩
  have hMjl : ∀ j l, Mm j l =
      ∑ x ∈ K.filter (fun x => cc x = j), Ee x * chi (x.val.testBit l) := by
    intro j l; rw [hMm]
  have hD : ∑ x ∈ K, ∑ y ∈ K, F x y =
      ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l * Mm l j := by
    symm
    calc ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l * Mm l j
        = ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a),
            ∑ x ∈ K.filter (fun x => cc x = j), ∑ y ∈ K.filter (fun y => cc y = l), F x y := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro l _
          rw [hMjl j l, hMjl l j, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          rw [hFxy, (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
      _ = ∑ j ∈ Finset.range (2 ^ a), ∑ x ∈ K.filter (fun x => cc x = j),
            ∑ l ∈ Finset.range (2 ^ a), ∑ y ∈ K.filter (fun y => cc y = l), F x y := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
      _ = ∑ j ∈ Finset.range (2 ^ a), ∑ x ∈ K.filter (fun x => cc x = j), ∑ y ∈ K, F x y := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro x _
          exact Finset.sum_fiberwise_of_maps_to (fun y _ => hccr y) _
      _ = ∑ x ∈ K, ∑ y ∈ K, F x y :=
          Finset.sum_fiberwise_of_maps_to (fun x _ => hccr x) _
  have hEE : ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l * Mm l j
      ≤ ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l ^ 2 := by
    have h2 : ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm l j ^ 2
        = ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l ^ 2 := Finset.sum_comm
    have h3 : ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), 2 * (Mm j l * Mm l j)
        ≤ ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), (Mm j l ^ 2 + Mm l j ^ 2) :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => by
        nlinarith [sq_nonneg (Mm j l - Mm l j)]))
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h3
    rw [h2] at h3
    linarith
  have hFF : ∀ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l ^ 2
      ≤ 2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2 := by
    intro j _
    calc ∑ l ∈ Finset.range (2 ^ a), Mm j l ^ 2 ≤ ∑ l ∈ Finset.range k, Mm j l ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk)
            (fun l _ _ => sq_nonneg _)
      _ = ∑ l ∈ Finset.range k,
            (∑ x ∈ K.filter (fun x => cc x = j), Ee x * chi (x.val.testBit l)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro l _
          rw [hMjl]
      _ ≤ 2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2 := by
          apply level1 k a ha hak _ Ee hEe1
          have hfc := fiber_card k a hak π K j
          have hfe : K.filter (fun x => cc x = j) = K.filter (fun x => (π x).val % 2 ^ a = j) := by
            apply Finset.filter_congr
            intro x _
            rw [hccz]
          rw [hfe]
          exact hfc
  have hsum : ∑ z ∈ K ×ˢ K, chi (xor (T z) (T z.swap))
      ≤ (2 : ℤ) ^ a * (2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2) := by
    rw [hC, hD]
    calc ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l * Mm l j
        ≤ ∑ j ∈ Finset.range (2 ^ a), ∑ l ∈ Finset.range (2 ^ a), Mm j l ^ 2 := hEE
      _ ≤ ∑ _j ∈ Finset.range (2 ^ a), 2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2 :=
          Finset.sum_le_sum hFF
      _ = _ := by rw [Finset.sum_const, Finset.card_range]; simp
  have h2k : (2 : ℤ) ^ k = 2 ^ a * 2 ^ (k - a) := by rw [← pow_add]; congr 1; omega
  have hz : (2 : ℤ) ^ a * (K.card : ℤ) ^ 2
      ≤ 4 * 2 ^ a * (E.card : ℤ) + 2 * (a : ℤ) * ((2 : ℤ) ^ k) ^ 2 := by
    have hpos : (0 : ℤ) ≤ (2 : ℤ) ^ a := by positivity
    have hKK : (K.card : ℤ) ^ 2 ≤
        (2 : ℤ) ^ a * (2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2) + 2 * (2 * (E.card : ℤ)) := by
      have := hB
      linarith
    calc (2 : ℤ) ^ a * (K.card : ℤ) ^ 2
        ≤ (2 : ℤ) ^ a * ((2 : ℤ) ^ a * (2 * (a : ℤ) * ((2 : ℤ) ^ (k - a)) ^ 2)
            + 2 * (2 * (E.card : ℤ))) := mul_le_mul_of_nonneg_left hKK hpos
      _ = _ := by rw [h2k]; ring
  exact_mod_cast hz

theorem flip_ind {N : ℕ} (G : Fin N → Fin N → Bool) (π : Equiv.Perm (Fin N))
    (z : Fin N × Fin N) (hz : z.1 ≠ z.2) :
    2 * ∑ s : Fin N → Bool,
        (if tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap then 1 else 0)
      = Fintype.card (Fin N → Bool) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin N → Bool) → (Fin N → Bool),
      φ = fun s => Function.update s z.1 (!s z.1) := ⟨_, rfl⟩
  have hφs : ∀ s, φ s = Function.update s z.1 (!s z.1) := by intro s; rw [hφ]
  have hinv : Function.Involutive φ := by
    intro s
    rw [hφs, hφs]
    simp
  obtain ⟨fn, hfn⟩ : ∃ fn : (Fin N → Bool) → ℕ, fn = fun s =>
      (if tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap then 1 else 0) :=
    ⟨_, rfl⟩
  have hfns : ∀ s, fn s =
      (if tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap then 1 else 0) := by
    intro s; rw [hfn]
  have hgoal : ∑ s : Fin N → Bool,
      (if tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap then 1 else 0)
      = ∑ s : Fin N → Bool, fn s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [hfns]
  rw [hgoal]
  have hpt : ∀ s : Fin N → Bool, fn (φ s) + fn s = 1 := by
    intro s
    rw [hfns, hfns, hφs]
    have u1 : Function.update s z.1 (!s z.1) z.1 = !s z.1 := Function.update_self _ _ _
    have u2 : Function.update s z.1 (!s z.1) z.2 = s z.2 := Function.update_of_ne (Ne.symm hz) _ _
    have t1 : tgt G π (Function.update s z.1 (!s z.1)) (fun _ => false) z
        = xor (G z.1 (π z.2)) (xor (!s z.1) false) := by
      show xor (G z.1 (π z.2)) (xor (Function.update s z.1 (!s z.1) z.1) false) = _
      rw [u1]
    have t2 : tgt G π (Function.update s z.1 (!s z.1)) (fun _ => false) z.swap
        = xor (G z.2 (π z.1)) (xor (s z.2) false) := by
      show xor (G z.2 (π z.1)) (xor (Function.update s z.1 (!s z.1) z.2) false) = _
      rw [u2]
    have t3 : tgt G π s (fun _ => false) z = xor (G z.1 (π z.2)) (xor (s z.1) false) := rfl
    have t4 : tgt G π s (fun _ => false) z.swap = xor (G z.2 (π z.1)) (xor (s z.2) false) := rfl
    rw [t1, t2, t3, t4]
    cases G z.1 (π z.2) <;> cases G z.2 (π z.1) <;> cases s z.1 <;> cases s z.2 <;> simp
  have hsum : ∑ s : Fin N → Bool, fn (φ s) = ∑ s : Fin N → Bool, fn s :=
    Equiv.sum_comp hinv.toPerm fn
  have h1 : ∑ s : Fin N → Bool, (fn (φ s) + fn s) = Fintype.card (Fin N → Bool) := by
    rw [Finset.sum_congr rfl (fun s _ => hpt s)]
    simp
  rw [Finset.sum_add_distrib, hsum] at h1
  omega

theorem avg {N : ℕ} (G : Fin N → Fin N → Bool) (π : Equiv.Perm (Fin N))
    (P : Finset (Fin N × Fin N)) (hP : ∀ z ∈ P, z.1 ≠ z.2) :
    ∃ s : Fin N → Bool, 2 * (P.filter (fun z =>
      tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap)).card ≤ P.card := by
  by_contra hno
  have hall : ∀ s : Fin N → Bool, P.card < 2 * (P.filter (fun z =>
      tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap)).card := by
    intro s
    by_contra h
    exact hno ⟨s, not_lt.1 h⟩
  have hlt : ∑ _s : Fin N → Bool, P.card < ∑ s : Fin N → Bool, 2 * (P.filter (fun z =>
      tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap)).card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun s _ => hall s)
  have heq : ∑ s : Fin N → Bool, 2 * (P.filter (fun z =>
      tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap)).card
      = ∑ _s : Fin N → Bool, P.card := by
    calc ∑ s : Fin N → Bool, 2 * (P.filter (fun z =>
          tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap)).card
        = ∑ s : Fin N → Bool, ∑ z ∈ P, 2 *
            (if tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap
              then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.card_filter, Finset.mul_sum]
      _ = ∑ z ∈ P, ∑ s : Fin N → Bool, 2 *
            (if tgt G π s (fun _ => false) z ≠ tgt G π s (fun _ => false) z.swap
              then 1 else 0) := Finset.sum_comm
      _ = ∑ _z ∈ P, Fintype.card (Fin N → Bool) := by
          apply Finset.sum_congr rfl
          intro z hz
          rw [← Finset.mul_sum]
          exact flip_ind G π z (hP z hz)
      _ = ∑ _s : Fin N → Bool, P.card := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, smul_eq_mul, smul_eq_mul,
            mul_comm]
  rw [heq] at hlt
  exact lt_irrefl _ hlt

theorem part2 {N : ℕ} (G : Fin N → Fin N → Bool) (π : Equiv.Perm (Fin N)) (S : Finset (Fin N)) :
    ∃ (p q : Fin N → Bool) (out : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool),
      4 * (errs G π Finset.univ S ∅ p q out).card ≤ (N - S.card) * (N - S.card - 1) := by
  obtain ⟨P, hPdef⟩ : ∃ P : Finset (Fin N × Fin N),
      P = ((Finset.univ \ S) ×ˢ (Finset.univ \ S)).filter (fun z => z.2 < z.1) := ⟨_, rfl⟩
  have hPmem : ∀ z : Fin N × Fin N, z ∈ P ↔ z.1 ∉ S ∧ z.2 ∉ S ∧ z.2 < z.1 := by
    intro z
    rw [hPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨⟨-, h1⟩, ⟨-, h2⟩⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨⟨Finset.mem_univ _, h1⟩, ⟨Finset.mem_univ _, h2⟩⟩, h3⟩
  obtain ⟨s, hs⟩ := avg G π P (fun z hz => ((hPmem z).1 hz).2.2.ne')
  obtain ⟨T, hT⟩ : ∃ T : Fin N × Fin N → Bool, T = tgt G π s (fun _ => false) := ⟨_, rfl⟩
  rw [← hT] at hs
  have hu : ∀ i : Fin N, i ∈ (Finset.univ : Finset (Fin N)) := Finset.mem_univ

  have huniq : ∀ z z' : Fin N × Fin N, (z.1 ∈ S ∨ z.2 ∈ S ∨ z.1 ≤ z.2) →
      (z'.1 ∈ S ∨ z'.2 ∈ S ∨ z'.1 ≤ z'.2) →
      maskF Finset.univ z.1 z.2 = maskF Finset.univ z'.1 z'.2 → S ∩ {z.1} = S ∩ {z'.1} →
      z = z' := by
    intro z z' hz hz' hm hsig
    by_cases d : z.1 = z.2
    · by_cases d' : z'.1 = z'.2
      · simp only [maskF, if_pos d, if_pos d', if_pos (hu _)] at hm
        have h1 := Finset.singleton_inj.1 hm
        exact Prod.ext h1 (by rw [← d, h1, d'])
      · exfalso
        simp only [maskF, if_pos d, if_neg d', if_pos (hu _)] at hm
        have h1 : z'.1 ∈ ({z.1} : Finset (Fin N)) := by rw [hm]; simp
        have h2 : z'.2 ∈ ({z.1} : Finset (Fin N)) := by rw [hm]; simp
        rw [Finset.mem_singleton] at h1 h2
        exact d' (h1.trans h2.symm)
    · by_cases d' : z'.1 = z'.2
      · exfalso
        simp only [maskF, if_neg d, if_pos d', if_pos (hu _)] at hm
        have h1 : z.1 ∈ ({z'.1} : Finset (Fin N)) := by rw [← hm]; simp
        have h2 : z.2 ∈ ({z'.1} : Finset (Fin N)) := by rw [← hm]; simp
        rw [Finset.mem_singleton] at h1 h2
        exact d (h1.trans h2.symm)
      · simp only [maskF, if_neg d, if_neg d'] at hm
        have h1 : z.1 ∈ ({z'.1, z'.2} : Finset (Fin N)) := by rw [← hm]; simp
        have h2 : z.2 ∈ ({z'.1, z'.2} : Finset (Fin N)) := by rw [← hm]; simp
        rw [Finset.mem_insert, Finset.mem_singleton] at h1 h2
        rcases h1 with h1 | h1
        · rcases h2 with h2 | h2
          · exact absurd (h1.trans h2.symm) d
          · exact Prod.ext h1 h2
        · rcases h2 with h2 | h2
          · exfalso
            have n1 : z.1 ∉ S := by
              intro hin
              have hmem : z.1 ∈ S ∩ {z'.1} := by
                rw [← hsig, Finset.mem_inter, Finset.mem_singleton]
                exact ⟨hin, rfl⟩
              rw [Finset.mem_inter, Finset.mem_singleton] at hmem
              exact d (hmem.2.trans h2.symm)
            have n2 : z.2 ∉ S := by
              intro hin
              have hmem : z.2 ∈ S ∩ {z.1} := by
                rw [hsig, Finset.mem_inter, Finset.mem_singleton]
                exact ⟨hin, h2⟩
              rw [Finset.mem_inter, Finset.mem_singleton] at hmem
              exact d hmem.2.symm
            rcases hz with h | h | h
            · exact n1 h
            · exact n2 h
            · rcases hz' with h' | h' | h'
              · exact n2 (by rw [h2]; exact h')
              · exact n1 (by rw [h1]; exact h')
              · rw [← h2, ← h1] at h'
                exact d (le_antisymm h h')
          · exact absurd (h1.trans h2.symm) d
  obtain ⟨out, hout⟩ : ∃ out : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool,
      ∀ w : Fin N × Fin N, (w.1 ∈ S ∨ w.2 ∈ S ∨ w.1 ≤ w.2) → ∀ κ : Finset (Fin N),
        out (maskF Finset.univ w.1 w.2) (S ∩ {w.1}) κ = T w := by
    classical
    refine ⟨fun m ρ _ => if h : ∃ z : Fin N × Fin N, (z.1 ∈ S ∨ z.2 ∈ S ∨ z.1 ≤ z.2) ∧
        maskF Finset.univ z.1 z.2 = m ∧ S ∩ {z.1} = ρ then T h.choose else false, ?_⟩
    intro w hw κ
    have hex : ∃ z : Fin N × Fin N, (z.1 ∈ S ∨ z.2 ∈ S ∨ z.1 ≤ z.2) ∧
        maskF Finset.univ z.1 z.2 = maskF Finset.univ w.1 w.2 ∧ S ∩ {z.1} = S ∩ {w.1} :=
      ⟨w, hw, rfl, rfl⟩
    beta_reduce
    rw [dif_pos hex]
    obtain ⟨g1, g2, g3⟩ := hex.choose_spec
    rw [huniq _ _ g1 hw g2 g3]
  refine ⟨s, fun _ => false, out, ?_⟩
  have hsub : errs G π Finset.univ S ∅ s (fun _ => false) out
      ⊆ P.filter (fun z => T z ≠ T z.swap) := by
    intro z hz
    rw [errs, Finset.mem_filter] at hz
    have hz2 : out (maskF Finset.univ z.1 z.2) (S ∩ {z.1}) (∅ ∩ {z.2}) ≠ T z := by
      rw [hT]; exact hz.2
    by_cases hg : z.1 ∈ S ∨ z.2 ∈ S ∨ z.1 ≤ z.2
    · exact absurd (hout z hg _) hz2
    · rw [not_or, not_or, not_le] at hg
      obtain ⟨n1, n2, hlt⟩ := hg
      have hne : z.1 ≠ z.2 := hlt.ne'
      have hsw : out (maskF Finset.univ z.2 z.1) (S ∩ {z.2}) (∅ ∩ {z.2}) = T z.swap :=
        hout z.swap (Or.inr (Or.inr (le_of_lt hlt))) (∅ ∩ {z.2})
      have e1 : maskF Finset.univ z.2 z.1 = maskF Finset.univ z.1 z.2 := by
        simp only [maskF, if_neg hne, if_neg (Ne.symm hne)]
        exact Finset.pair_comm _ _
      have e2 : S ∩ {z.2} = S ∩ {z.1} := by
        rw [Finset.inter_singleton_of_notMem n1, Finset.inter_singleton_of_notMem n2]
      rw [e1, e2] at hsw
      rw [Finset.mem_filter, hPmem]
      refine ⟨⟨n1, n2, hlt⟩, ?_⟩
      intro heq
      apply hz2
      rw [hsw, heq]
  have hc1 := Finset.card_le_card hsub
  have hP2 : 2 * P.card ≤ (N - S.card) * (N - S.card - 1) := by
    have hdisj : Disjoint P (P.image Prod.swap) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      rw [Finset.mem_image] at hz'
      obtain ⟨w, hw, rfl⟩ := hz'
      have a1 : w.1 < w.2 := ((hPmem w.swap).1 hz).2.2
      have a2 : w.2 < w.1 := ((hPmem w).1 hw).2.2
      exact lt_asymm a1 a2
    have hsubO : P ∪ P.image Prod.swap ⊆ (Finset.univ \ S).offDiag := by
      intro z hz
      rw [Finset.mem_union] at hz
      rw [Finset.mem_offDiag, Finset.mem_sdiff, Finset.mem_sdiff]
      rcases hz with hz | hz
      · obtain ⟨n1, n2, hlt⟩ := (hPmem z).1 hz
        exact ⟨⟨Finset.mem_univ _, n1⟩, ⟨Finset.mem_univ _, n2⟩, hlt.ne'⟩
      · rw [Finset.mem_image] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        obtain ⟨n1, n2, hlt⟩ := (hPmem w).1 hw
        exact ⟨⟨Finset.mem_univ _, n2⟩, ⟨Finset.mem_univ _, n1⟩, hlt.ne⟩
    have hcard := Finset.card_le_card hsubO
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ Prod.swap_injective,
      Finset.offDiag_card, Finset.card_univ_diff, Fintype.card_fin] at hcard
    rw [Nat.mul_sub_one]
    omega
  exact le_trans (by omega) hP2

end PEqualNP.Outside.L_meta_25703_aux

theorem PEqualNP.Outside.L_meta_25703 : (∀ (k a : ℕ), 0 < a → 2^a ≤ k →
  let N := 2^k
  let r := 2^a
  ∀ (G : Fin N → Fin N → Bool) (A B : Finset (Fin N)),
    (∀ x ∉ A, ∀ y ∉ B, G x y = x.val.testBit (y.val % r)) →
    ∀ π : Equiv.Perm (Fin N),
      let cost := fun (keep rows cols : Finset (Fin N)) (f g : Fin N → Bool)
          (decode : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool) =>
        let mask := fun (i j : Fin N) => if i = j then
          (if i ∈ keep then ({i} : Finset (Fin N)) else ∅) else {i,j}
        (Finset.univ.filter (fun z : Fin N × Fin N =>
          decode (mask z.1 z.2) (rows ∩ {z.1}) (cols ∩ {z.2}) ≠
            xor (G z.1 (π z.2)) (xor (f z.1) (g z.2)))).card
      (∀ (U R C : Finset (Fin N)) (f g : Fin N → Bool)
          (D : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool),
        let K := (Finset.univ \ (R ∪ C)).filter (fun z => z ∉ A ∧ π z ∉ B)
        r*K.card^2 ≤ 4*r*cost U R C f g D + 2*a*N^2) ∧
      (∀ S : Finset (Fin N), ∃ (p q : Fin N → Bool)
          (out : Finset (Fin N) → Finset (Fin N) → Finset (Fin N) → Bool),
        4*cost Finset.univ S ∅ p q out ≤ (N-S.card)*(N-S.card-1))) := by
  intro k a ha hk N r G A B hG π cost
  refine ⟨?_, ?_⟩
  · intro U R C f g D K
    exact PEqualNP.Outside.L_meta_25703_aux.part1 k a ha hk G A B hG π U R C f g D
  · intro S
    exact PEqualNP.Outside.L_meta_25703_aux.part2 G π S
