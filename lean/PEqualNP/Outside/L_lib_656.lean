import Mathlib

namespace PEqualNP.Outside.L_lib_656_aux

def T (R : ℕ) : ℕ → ℕ
  | 0 => 0
  | M + 1 => 2 ^ (2 * R) * T R M + ((2 ^ R - 1) <<< R)

def G (R : ℕ) : ℕ → ℕ
  | 0 => 0
  | M + 1 => 2 ^ (2 * R) * G R M + 1

theorem a_lt (R : ℕ) : (2 ^ R - 1) <<< R < 2 ^ (2 * R) := by
  rw [Nat.shiftLeft_eq, two_mul, pow_add]
  have h : 0 < 2 ^ R := by positivity
  exact Nat.mul_lt_mul_of_pos_right (by omega) h

theorem a_bit (R l : ℕ) : ((2 ^ R - 1) <<< R).testBit l = decide (R ≤ l ∧ l < 2 * R) := by
  rw [Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  by_cases h : R ≤ l
  · simp [h]; omega
  · simp [h]

theorem low_bit (i l : ℕ) (hl : l < 2 * 2 ^ i) : l.testBit i = decide (2 ^ i ≤ l) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hR : 0 < 2 ^ i := by positivity
  have h1 : l / 2 ^ i < 2 := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hl)
  by_cases h : 2 ^ i ≤ l
  · have : l / 2 ^ i = 1 := by
      have : 1 ≤ l / 2 ^ i := (Nat.le_div_iff_mul_le hR).2 (by rw [one_mul]; exact h)
      omega
    simp [this, h]
  · have : l / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
    simp [this, h]

theorem shift_bit (i l : ℕ) : (l + 2 * 2 ^ i).testBit i = l.testBit i := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
    Nat.add_mul_div_right _ _ (by positivity)]
  have : (l / 2 ^ i + 2) % 2 = l / 2 ^ i % 2 := by omega
  rw [this]

theorem T_bit (i : ℕ) : ∀ M l, (T (2 ^ i) M).testBit l =
    decide (l < M * (2 * 2 ^ i) ∧ l.testBit i = true) := by
  intro M
  induction M with
  | zero => intro l; simp [T]
  | succ M ih =>
    intro l
    simp only [T]
    rw [Nat.testBit_two_pow_mul_add _ (a_lt _)]
    by_cases hl : l < 2 * 2 ^ i
    · rw [if_pos hl, a_bit, low_bit i l hl]
      have : l < (M + 1) * (2 * 2 ^ i) := by nlinarith
      by_cases h2 : 2 ^ i ≤ l
      · simp [h2, this, hl]
      · simp [h2]
    · rw [if_neg hl, ih]
      have e : l = (l - 2 * 2 ^ i) + 2 * 2 ^ i := by omega
      have hb : l.testBit i = (l - 2 * 2 ^ i).testBit i := by
        conv_lhs => rw [e]
        exact shift_bit i _
      rw [hb]
      have : l - 2 * 2 ^ i < M * (2 * 2 ^ i) ↔ l < (M + 1) * (2 * 2 ^ i) := by
        rw [Nat.add_mul, one_mul]; omega
      simp [this]

theorem T_eq (R : ℕ) : ∀ M, T R M = ((2 ^ R - 1) <<< R) * G R M := by
  intro M
  induction M with
  | zero => simp [T, G]
  | succ M ih => simp only [T, G, ih]; ring

theorem G_mul (R : ℕ) : ∀ M, (2 ^ (2 * R) - 1) * G R M = 2 ^ (M * (2 * R)) - 1 := by
  intro M
  induction M with
  | zero => simp [G]
  | succ M ih =>
    simp only [G]
    have h1 : 1 ≤ 2 ^ (2 * R) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (M * (2 * R)) := Nat.one_le_two_pow
    have e : 2 ^ ((M + 1) * (2 * R)) = 2 ^ (2 * R) * 2 ^ (M * (2 * R)) := by
      rw [← pow_add]; congr 1; ring
    rw [e, mul_add, mul_one, mul_left_comm, ih]
    zify [h1, h2, Nat.one_le_two_pow (n := 2 * R) |> fun h => Nat.mul_le_mul h h2]
    push_cast
    ring

theorem main (k : ℕ) (i : Fin k) (shift : Fin (2 ^ k)) (lane : ℕ) :
    (if shift.val.testBit i.val then (2 ^ (2 ^ k) - 1) ^^^
        (((2 ^ (2 ^ i.val) - 1) <<< (2 ^ i.val)) * ((2 ^ (2 ^ k) - 1) / (2 ^ (2 * 2 ^ i.val) - 1)))
      else (((2 ^ (2 ^ i.val) - 1) <<< (2 ^ i.val)) * ((2 ^ (2 ^ k) - 1) / (2 ^ (2 * 2 ^ i.val) - 1)))).testBit lane =
    (decide (lane < 2 ^ k) && (lane ^^^ shift.val).testBit i.val) := by
  have hi := i.isLt
  set M := 2 ^ (k - i.val - 1) with hM
  have hlanes : 2 ^ k = M * (2 * 2 ^ i.val) := by
    rw [hM, ← pow_succ', ← pow_add]; congr 1; omega
  have hpos : 0 < 2 ^ (2 * 2 ^ i.val) - 1 := by
    have : 2 ≤ 2 ^ (2 * 2 ^ i.val) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * 2 ^ i.val) := Nat.pow_le_pow_right (by norm_num) (by have := Nat.one_le_two_pow (n := i.val); omega)
    omega
  have hdiv : (2 ^ (2 ^ k) - 1) / (2 ^ (2 * 2 ^ i.val) - 1) = G (2 ^ i.val) M := by
    rw [hlanes, ← G_mul, Nat.mul_div_cancel_left _ hpos]
  have htile : ((2 ^ (2 ^ i.val) - 1) <<< (2 ^ i.val)) * ((2 ^ (2 ^ k) - 1) / (2 ^ (2 * 2 ^ i.val) - 1))
      = T (2 ^ i.val) M := by rw [hdiv, T_eq]
  rw [htile]
  have tb := T_bit i.val M lane
  rw [← hlanes] at tb
  split_ifs with hs
  · rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, tb, Nat.testBit_xor, hs]
    by_cases h1 : lane < 2 ^ k <;> cases lane.testBit i.val <;> simp [h1]
  · rw [tb, Nat.testBit_xor]
    simp only [Bool.not_eq_true] at hs
    rw [hs]
    by_cases h1 : lane < 2 ^ k <;> cases lane.testBit i.val <;> simp [h1]

end PEqualNP.Outside.L_lib_656_aux

theorem PEqualNP.Outside.L_lib_656 : ∀ (k : ℕ) (i : Fin k) (shift : Fin (2 ^ k)),
  let lanes := 2 ^ k
  let full := 2 ^ lanes - 1
  let run := 2 ^ i.val
  let tile := ((2 ^ run - 1) <<< run) * (full / (2 ^ (2 * run) - 1))
  let plane := if shift.val.testBit i.val then full ^^^ tile else tile
  ∀ lane : ℕ, plane.testBit lane =
    (decide (lane < lanes) && (lane ^^^ shift.val).testBit i.val) := by
  intro k i shift lanes full run tile plane lane
  exact PEqualNP.Outside.L_lib_656_aux.main k i shift lane
