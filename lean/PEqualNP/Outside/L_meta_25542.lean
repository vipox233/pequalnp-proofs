import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25542_aux

def move (mode letter : Nat) : Nat × Nat :=
  let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
    ((mode == 2) && letter.testBit 1)
  let hit := letter.testBit 2
  (if aligned then (if hit then 0 else 2) else 1,
    hit.toNat + (aligned && hit).toNat)

def summaryFrom (mode code length : Nat) : Nat × Nat :=
  (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
    let result := move st.1 ((code >>> (3 * digitPos)) % 8)
    (result.1, st.2 + result.2)) (mode, 0)

def summary (code length : Nat) : Nat × Nat :=
  summaryFrom 0 code length

def price (n depth : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun codeWord =>
    2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum

def phi : Nat → Nat
  | 0 => 0
  | 1 => 1
  | _ => 2

theorem move_mode_lt (mode letter : Nat) : (move mode letter).1 < 3 := by
  unfold move
  dsimp only
  split <;> [split <;> omega; omega]

theorem move_gain_le (mode letter : Nat) : (move mode letter).2 ≤ 2 := by
  unfold move
  cases (((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)) <;> cases letter.testBit 2 <;> decide

theorem foldl_summary_acc (code : Nat) (xs : List Nat) (mode acc : Nat) :
    xs.foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (mode, acc) =
    let s := xs.foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (mode, 0)
    (s.1, acc + s.2) := by
  induction xs generalizing mode acc with
  | nil => simp
  | cons d xs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (acc + (move mode ((code >>> (3 * d)) % 8)).2)]
    rw [ih _ (0 + (move mode ((code >>> (3 * d)) % 8)).2)]
    simp only [Nat.zero_add, Nat.add_assoc]

theorem shiftRight_three_succ (l rest k : Nat) (hl : l < 8) :
    (l + 8 * rest) >>> (3 * (k + 1)) = rest >>> (3 * k) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hp : 2 ^ (3 * (k + 1)) = 8 * 2 ^ (3 * k) := by
    rw [show 3 * (k + 1) = 3 + 3 * k by omega, Nat.pow_add]
  rw [hp, ← Nat.div_div_eq_div_mul]
  have hd : (l + 8 * rest) / 8 = rest := by omega
  rw [hd]

theorem summaryFrom_zero (mode code : Nat) : summaryFrom mode code 0 = (mode, 0) := rfl

theorem summaryFrom_succ (mode l rest n : Nat) (hl : l < 8) :
    summaryFrom mode (l + 8 * rest) (n + 1) =
      let r := move mode l
      let s := summaryFrom r.1 rest n
      (s.1, r.2 + s.2) := by
  unfold summaryFrom
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : ((l + 8 * rest) >>> (3 * 0)) % 8 = l := by
    simp only [Nat.mul_zero, Nat.shiftRight_zero]
    omega
  rw [h0]
  have hcongr : (List.range n).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 (((l + 8 * rest) >>> (3 * (digitPos + 1))) % 8)
      (result.1, st.2 + result.2)) ((move mode l).1, 0 + (move mode l).2) =
    (List.range n).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((rest >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) ((move mode l).1, (move mode l).2) := by
    simp only [Nat.zero_add]
    congr 1
    funext st digitPos
    rw [shiftRight_three_succ l rest digitPos hl]
  rw [hcongr, foldl_summary_acc]

theorem summaryFrom_gain_le (mode code n : Nat) : (summaryFrom mode code n).2 ≤ 2 * n := by
  induction n generalizing mode code with
  | zero => simp [summaryFrom_zero]
  | succ n ih =>
    have hsplit : code = code % 8 + 8 * (code / 8) := by omega
    conv_lhs => rw [hsplit]
    rw [summaryFrom_succ mode (code % 8) (code / 8) n (by omega)]
    dsimp only
    have h1 := move_gain_le mode (code % 8)
    have h2 := ih (move mode (code % 8)).1 (code / 8)
    omega

theorem list_sum_map_add {α : Type*} (xs : List α) (f g : α → Nat) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

theorem list_sum_map_mul_left {α : Type*} (c : Nat) (xs : List α) (f : α → Nat) :
    (xs.map (fun x => c * f x)).sum = c * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

theorem list_sum_map_const {α : Type*} (c : Nat) (xs : List α) :
    (xs.map (fun _ => c)).sum = xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

theorem list_sum_map_le {α : Type*} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hx := h x (List.mem_cons_self ..)
    have hxs := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    omega

theorem sum_range_mul (a b : Nat) (f : Nat → Nat) :
    ((List.range (a * b)).map f).sum =
      ((List.range a).map (fun r => ((List.range b).map (fun q => f (r + a * q))).sum)).sum := by
  induction b with
  | zero =>
    simp
  | succ b ih =>
    rw [Nat.mul_succ, List.range_add, List.map_append, List.sum_append, ih, List.map_map]
    have hstep : ((List.range a).map (fun r =>
        ((List.range (b + 1)).map (fun q => f (r + a * q))).sum)).sum =
      ((List.range a).map (fun r => ((List.range b).map (fun q => f (r + a * q))).sum)).sum +
      ((List.range a).map (fun r => f (r + a * b))).sum := by
      rw [← list_sum_map_add]
      congr 1
      apply List.map_congr_left
      intro r _
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    rw [hstep]
    congr 1
    congr 1
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_apply, Nat.add_comm]

theorem sum_range_eight_pow_succ (n : Nat) (f : Nat → Nat) :
    ((List.range (8 ^ (n + 1))).map f).sum =
      ((List.range 8).map (fun l => ((List.range (8 ^ n)).map (fun rest => f (l + 8 * rest))).sum)).sum := by
  rw [Nat.pow_succ', sum_range_mul]

def genSum (M mode n : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun w =>
    let g := (summaryFrom mode w n).2
    (M - 1) ^ g * M ^ (2 * n - g))).sum

theorem genSum_zero (M mode : Nat) : genSum M mode 0 = 1 := by
  simp [genSum, summaryFrom_zero]

theorem genSum_succ_step (M mode n : Nat) :
    genSum M mode (n + 1) =
      ((List.range 8).map (fun l =>
        let r := move mode l
        ((M - 1) ^ r.2 * M ^ (2 - r.2)) * genSum M r.1 n)).sum := by
  unfold genSum
  rw [sum_range_eight_pow_succ]
  congr 1
  apply List.map_congr_left
  intro l hl
  have hl8 : l < 8 := List.mem_range.1 hl
  rw [← list_sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro rest _
  rw [summaryFrom_succ mode l rest n hl8]
  dsimp only
  have hr2 : (move mode l).2 ≤ 2 := move_gain_le mode l
  have hs2 : (summaryFrom (move mode l).1 rest n).2 ≤ 2 * n := summaryFrom_gain_le _ rest n
  have hexp : 2 * (n + 1) - ((move mode l).2 + (summaryFrom (move mode l).1 rest n).2) =
      (2 - (move mode l).2) + (2 * n - (summaryFrom (move mode l).1 rest n).2) := by omega
  rw [hexp, Nat.pow_add, Nat.pow_add]
  ring

theorem genSum_rec_0 (M n : Nat) :
    genSum M 0 (n + 1) = (4 * M ^ 2 + 4 * (M - 1) * M) * genSum M 1 n := by
  rw [genSum_succ_step]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr8]
  have m0 : move 0 0 = (1, 0) := by decide
  have m1 : move 0 1 = (1, 0) := by decide
  have m2 : move 0 2 = (1, 0) := by decide
  have m3 : move 0 3 = (1, 0) := by decide
  have m4 : move 0 4 = (1, 1) := by decide
  have m5 : move 0 5 = (1, 1) := by decide
  have m6 : move 0 6 = (1, 1) := by decide
  have m7 : move 0 7 = (1, 1) := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    m0, m1, m2, m3, m4, m5, m6, m7]
  ring

theorem genSum_rec_1 (M n : Nat) :
    genSum M 1 (n + 1) =
      (M - 1) ^ 2 * genSum M 0 n +
      (3 * M ^ 2 + 3 * (M - 1) * M) * genSum M 1 n +
      M ^ 2 * genSum M 2 n := by
  rw [genSum_succ_step]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr8]
  have m0 : move 1 0 = (1, 0) := by decide
  have m1 : move 1 1 = (1, 0) := by decide
  have m2 : move 1 2 = (1, 0) := by decide
  have m3 : move 1 3 = (2, 0) := by decide
  have m4 : move 1 4 = (1, 1) := by decide
  have m5 : move 1 5 = (1, 1) := by decide
  have m6 : move 1 6 = (1, 1) := by decide
  have m7 : move 1 7 = (0, 2) := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    m0, m1, m2, m3, m4, m5, m6, m7]
  ring

theorem genSum_rec_2 (M n : Nat) :
    genSum M 2 (n + 1) =
      2 * (M - 1) ^ 2 * genSum M 0 n +
      (2 * M ^ 2 + 2 * (M - 1) * M) * genSum M 1 n +
      2 * M ^ 2 * genSum M 2 n := by
  rw [genSum_succ_step]
  have hr8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := by decide
  rw [hr8]
  have m0 : move 2 0 = (1, 0) := by decide
  have m1 : move 2 1 = (1, 0) := by decide
  have m2 : move 2 2 = (2, 0) := by decide
  have m3 : move 2 3 = (2, 0) := by decide
  have m4 : move 2 4 = (1, 1) := by decide
  have m5 : move 2 5 = (1, 1) := by decide
  have m6 : move 2 6 = (0, 2) := by decide
  have m7 : move 2 7 = (0, 2) := by decide
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    m0, m1, m2, m3, m4, m5, m6, m7]
  ring

theorem genSum_bound (M : Nat) (hM : 2 ≤ M) :
    ∀ n,
      (8 * M - 2) * genSum M 0 n ≤ (8 * M) * (8 * M ^ 2 - 5 * M + 2) ^ n ∧
      (8 * M - 2) * genSum M 1 n ≤ (8 * M - 1) * (8 * M ^ 2 - 5 * M + 2) ^ n ∧
      (8 * M - 2) * genSum M 2 n ≤ (8 * M - 2) * (8 * M ^ 2 - 5 * M + 2) ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  have hsub1 : m + 2 - 1 = m + 1 := by omega
  have hsub2 : 8 * (m + 2) - 2 = 8 * m + 14 := by omega
  have hsub3 : 8 * (m + 2) - 1 = 8 * m + 15 := by omega
  have hlam : 8 * (m + 2) ^ 2 - 5 * (m + 2) + 2 = 8 * m ^ 2 + 27 * m + 24 := by
    have : 8 * (m + 2) ^ 2 = 8 * m ^ 2 + 32 * m + 32 := by ring
    omega
  rw [hsub2, hsub3, hlam]
  intro n
  induction n with
  | zero =>
    simp only [genSum_zero, Nat.pow_zero, Nat.mul_one]
    omega
  | succ n ih =>
    rcases ih with ⟨ih0, ih1, ih2⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [genSum_rec_0, hsub1, Nat.pow_succ]
      calc
        (8 * m + 14) * ((4 * (m + 2) ^ 2 + 4 * (m + 1) * (m + 2)) * genSum (m + 2) 1 n)
            = (4 * (m + 2) ^ 2 + 4 * (m + 1) * (m + 2)) * ((8 * m + 14) * genSum (m + 2) 1 n) := by ring
        _ ≤ (4 * (m + 2) ^ 2 + 4 * (m + 1) * (m + 2)) * ((8 * m + 15) * (8 * m ^ 2 + 27 * m + 24) ^ n) :=
            Nat.mul_le_mul_left _ ih1
        _ = ((4 * (m + 2) ^ 2 + 4 * (m + 1) * (m + 2)) * (8 * m + 15)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by ring
        _ ≤ (8 * (m + 2) * (8 * m ^ 2 + 27 * m + 24)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by
            apply Nat.mul_le_mul_right
            nlinarith
        _ = 8 * (m + 2) * ((8 * m ^ 2 + 27 * m + 24) ^ n * (8 * m ^ 2 + 27 * m + 24)) := by ring
    · rw [genSum_rec_1, hsub1, Nat.pow_succ]
      have h0 := Nat.mul_le_mul_left ((m + 1) ^ 2) ih0
      have h1 := Nat.mul_le_mul_left (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) ih1
      have h2 := Nat.mul_le_mul_left ((m + 2) ^ 2) ih2
      have hcomb : (8 * m + 14) * ((m + 1) ^ 2 * genSum (m + 2) 0 n +
          (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) * genSum (m + 2) 1 n +
          (m + 2) ^ 2 * genSum (m + 2) 2 n) ≤
          ((m + 1) ^ 2 * (8 * (m + 2)) +
           (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) * (8 * m + 15) +
           (m + 2) ^ 2 * (8 * m + 14)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by
        calc
          (8 * m + 14) * ((m + 1) ^ 2 * genSum (m + 2) 0 n +
              (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) * genSum (m + 2) 1 n +
              (m + 2) ^ 2 * genSum (m + 2) 2 n)
              = (m + 1) ^ 2 * ((8 * m + 14) * genSum (m + 2) 0 n) +
                (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) * ((8 * m + 14) * genSum (m + 2) 1 n) +
                (m + 2) ^ 2 * ((8 * m + 14) * genSum (m + 2) 2 n) := by ring
          _ ≤ (m + 1) ^ 2 * (8 * (m + 2) * (8 * m ^ 2 + 27 * m + 24) ^ n) +
              (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) * ((8 * m + 15) * (8 * m ^ 2 + 27 * m + 24) ^ n) +
              (m + 2) ^ 2 * ((8 * m + 14) * (8 * m ^ 2 + 27 * m + 24) ^ n) :=
              Nat.add_le_add (Nat.add_le_add h0 h1) h2
          _ = ((m + 1) ^ 2 * (8 * (m + 2)) +
               (3 * (m + 2) ^ 2 + 3 * (m + 1) * (m + 2)) * (8 * m + 15) +
               (m + 2) ^ 2 * (8 * m + 14)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by ring
      calc
        _ ≤ _ := hcomb
        _ ≤ ((8 * m + 15) * (8 * m ^ 2 + 27 * m + 24)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by
            apply Nat.mul_le_mul_right
            nlinarith
        _ = (8 * m + 15) * ((8 * m ^ 2 + 27 * m + 24) ^ n * (8 * m ^ 2 + 27 * m + 24)) := by ring
    · rw [genSum_rec_2, hsub1, Nat.pow_succ]
      have h0 := Nat.mul_le_mul_left (2 * (m + 1) ^ 2) ih0
      have h1 := Nat.mul_le_mul_left (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) ih1
      have h2 := Nat.mul_le_mul_left (2 * (m + 2) ^ 2) ih2
      have hcomb : (8 * m + 14) * (2 * (m + 1) ^ 2 * genSum (m + 2) 0 n +
          (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) * genSum (m + 2) 1 n +
          2 * (m + 2) ^ 2 * genSum (m + 2) 2 n) ≤
          (2 * (m + 1) ^ 2 * (8 * (m + 2)) +
           (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) * (8 * m + 15) +
           2 * (m + 2) ^ 2 * (8 * m + 14)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by
        calc
          (8 * m + 14) * (2 * (m + 1) ^ 2 * genSum (m + 2) 0 n +
              (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) * genSum (m + 2) 1 n +
              2 * (m + 2) ^ 2 * genSum (m + 2) 2 n)
              = 2 * (m + 1) ^ 2 * ((8 * m + 14) * genSum (m + 2) 0 n) +
                (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) * ((8 * m + 14) * genSum (m + 2) 1 n) +
                2 * (m + 2) ^ 2 * ((8 * m + 14) * genSum (m + 2) 2 n) := by ring
          _ ≤ 2 * (m + 1) ^ 2 * (8 * (m + 2) * (8 * m ^ 2 + 27 * m + 24) ^ n) +
              (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) * ((8 * m + 15) * (8 * m ^ 2 + 27 * m + 24) ^ n) +
              2 * (m + 2) ^ 2 * ((8 * m + 14) * (8 * m ^ 2 + 27 * m + 24) ^ n) :=
              Nat.add_le_add (Nat.add_le_add h0 h1) h2
          _ = (2 * (m + 1) ^ 2 * (8 * (m + 2)) +
               (2 * (m + 2) ^ 2 + 2 * (m + 1) * (m + 2)) * (8 * m + 15) +
               2 * (m + 2) ^ 2 * (8 * m + 14)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by ring
      calc
        _ ≤ _ := hcomb
        _ ≤ ((8 * m + 14) * (8 * m ^ 2 + 27 * m + 24)) * (8 * m ^ 2 + 27 * m + 24) ^ n := by
            apply Nat.mul_le_mul_right
            nlinarith
        _ = (8 * m + 14) * ((8 * m ^ 2 + 27 * m + 24) ^ n * (8 * m ^ 2 + 27 * m + 24)) := by ring

theorem genSum_0_le (M : Nat) (hM : 2 ≤ M) (n : Nat) :
    genSum M 0 n ≤ 2 * (8 * M ^ 2 - 5 * M + 2) ^ n := by
  have h := (genSum_bound M hM n).1
  have hpos : 0 < 8 * M - 2 := by omega
  have h2 : 8 * M ≤ (8 * M - 2) * 2 := by omega
  have hmul : (8 * M - 2) * genSum M 0 n ≤ (8 * M - 2) * (2 * (8 * M ^ 2 - 5 * M + 2) ^ n) := by
    calc
      (8 * M - 2) * genSum M 0 n ≤ (8 * M) * (8 * M ^ 2 - 5 * M + 2) ^ n := h
      _ ≤ ((8 * M - 2) * 2) * (8 * M ^ 2 - 5 * M + 2) ^ n := Nat.mul_le_mul_right _ h2
      _ = (8 * M - 2) * (2 * (8 * M ^ 2 - 5 * M + 2) ^ n) := by ring
  exact Nat.le_of_mul_le_mul_left hmul hpos

theorem term_chernoff (M n d g : Nat) (hM : 2 ≤ M) (hg : g ≤ 2 * n) :
    2 ^ (2 * n - (g - d)) * (M - 1) ^ d * M ^ (2 * n) ≤
      2 ^ (2 * n) * M ^ d * ((M - 1) ^ g * M ^ (2 * n - g)) := by
  by_cases hgd : g ≤ d
  · have hsub : g - d = 0 := by omega
    rw [hsub, Nat.sub_zero]
    have hpow : (M - 1) ^ (d - g) ≤ M ^ (d - g) := Nat.pow_le_pow_left (by omega) _
    have hd_eq : d = g + (d - g) := by omega
    have h2n_eq : 2 * n = g + (2 * n - g) := by omega
    have hpow1 : (M - 1) ^ d = (M - 1) ^ g * (M - 1) ^ (d - g) := by
      rw [← Nat.pow_add, ← hd_eq]
    have hpow2 : M ^ (2 * n) = M ^ g * M ^ (2 * n - g) := by
      rw [← Nat.pow_add, ← h2n_eq]
    calc
      2 ^ (2 * n) * (M - 1) ^ d * M ^ (2 * n)
          = 2 ^ (2 * n) * ((M - 1) ^ g * (M - 1) ^ (d - g)) * (M ^ g * M ^ (2 * n - g)) := by
              rw [hpow1, hpow2]
      _ = (2 ^ (2 * n) * (M - 1) ^ g * M ^ g * M ^ (2 * n - g)) * (M - 1) ^ (d - g) := by ring
      _ ≤ (2 ^ (2 * n) * (M - 1) ^ g * M ^ g * M ^ (2 * n - g)) * M ^ (d - g) :=
            Nat.mul_le_mul_left _ hpow
      _ = 2 ^ (2 * n) * (M ^ g * M ^ (d - g)) * ((M - 1) ^ g * M ^ (2 * n - g)) := by ring
      _ = 2 ^ (2 * n) * M ^ d * ((M - 1) ^ g * M ^ (2 * n - g)) := by
            rw [← Nat.pow_add, ← hd_eq]
  · have hgt : d < g := by omega
    have hM2 : M ≤ 2 * (M - 1) := by omega
    have hpow : M ^ (g - d) ≤ (2 * (M - 1)) ^ (g - d) := Nat.pow_le_pow_left hM2 _
    rw [Nat.mul_pow] at hpow
    have hg_eq : g = d + (g - d) := by omega
    have h2n_eq1 : 2 * n = (2 * n - (g - d)) + (g - d) := by omega
    have h2n_eq2 : 2 * n = (g - d) + (d + (2 * n - g)) := by omega
    have hpowM : M ^ (2 * n) = M ^ (g - d) * (M ^ d * M ^ (2 * n - g)) := by
      rw [← Nat.pow_add, ← Nat.pow_add, ← h2n_eq2]
    calc
      2 ^ (2 * n - (g - d)) * (M - 1) ^ d * M ^ (2 * n)
          = 2 ^ (2 * n - (g - d)) * (M - 1) ^ d * (M ^ (g - d) * (M ^ d * M ^ (2 * n - g))) := by
              rw [hpowM]
      _ = (2 ^ (2 * n - (g - d)) * (M - 1) ^ d * M ^ d * M ^ (2 * n - g)) * M ^ (g - d) := by ring
      _ ≤ (2 ^ (2 * n - (g - d)) * (M - 1) ^ d * M ^ d * M ^ (2 * n - g)) *
            (2 ^ (g - d) * (M - 1) ^ (g - d)) := Nat.mul_le_mul_left _ hpow
      _ = (2 ^ (2 * n - (g - d)) * 2 ^ (g - d)) * M ^ d *
            (((M - 1) ^ d * (M - 1) ^ (g - d)) * M ^ (2 * n - g)) := by ring
      _ = 2 ^ (2 * n) * M ^ d * ((M - 1) ^ g * M ^ (2 * n - g)) := by
            rw [← Nat.pow_add, ← h2n_eq1, ← Nat.pow_add, ← hg_eq]

theorem price_chernoff (M n d : Nat) (hM : 2 ≤ M) :
    price n d * (M - 1) ^ d * M ^ (2 * n) ≤ 2 ^ (2 * n) * M ^ d * genSum M 0 n := by
  unfold price genSum summary
  have hl : price n d * (M - 1) ^ d * M ^ (2 * n) =
      ((List.range (8 ^ n)).map (fun w =>
        2 ^ (2 * n - ((summaryFrom 0 w n).2 - d)) * (M - 1) ^ d * M ^ (2 * n))).sum := by
    unfold price summary
    rw [Nat.mul_assoc, Nat.mul_comm (List.sum _), ← list_sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro w _
    ring
  have hr : 2 ^ (2 * n) * M ^ d * ((List.range (8 ^ n)).map (fun w =>
        (M - 1) ^ (summaryFrom 0 w n).2 * M ^ (2 * n - (summaryFrom 0 w n).2))).sum =
      ((List.range (8 ^ n)).map (fun w =>
        2 ^ (2 * n) * M ^ d * ((M - 1) ^ (summaryFrom 0 w n).2 * M ^ (2 * n - (summaryFrom 0 w n).2)))).sum := by
    rw [← list_sum_map_mul_left]
  calc
    ((List.range (8 ^ n)).map (fun codeWord =>
        2 ^ (2 * n - ((summaryFrom 0 codeWord n).2 - d)))).sum * (M - 1) ^ d * M ^ (2 * n)
        = ((List.range (8 ^ n)).map (fun w =>
            2 ^ (2 * n - ((summaryFrom 0 w n).2 - d)) * (M - 1) ^ d * M ^ (2 * n))).sum := hl
    _ ≤ ((List.range (8 ^ n)).map (fun w =>
          2 ^ (2 * n) * M ^ d * ((M - 1) ^ (summaryFrom 0 w n).2 * M ^ (2 * n - (summaryFrom 0 w n).2)))).sum := by
        apply list_sum_map_le
        intro w _
        exact term_chernoff M n d (summaryFrom 0 w n).2 hM (summaryFrom_gain_le 0 w n)
    _ = 2 ^ (2 * n) * M ^ d * ((List.range (8 ^ n)).map (fun w =>
          (M - 1) ^ (summaryFrom 0 w n).2 * M ^ (2 * n - (summaryFrom 0 w n).2))).sum := hr.symm

theorem bernoulli_sub {M : Nat} : ∀ p, p ≤ M → (M - p) * M ^ p ≤ M * (M - 1) ^ p := by
  intro p
  induction p with
  | zero => intro _; simp
  | succ p ih =>
    intro hp
    have ih' := ih (by omega)
    have hM1 : 1 ≤ M := by omega
    calc
      (M - (p + 1)) * M ^ (p + 1)
          = (M - (p + 1)) * M * M ^ p := by rw [Nat.pow_succ]; ring
      _ ≤ (M - 1) * (M - p) * M ^ p := by
          apply Nat.mul_le_mul_right
          zify [hp, hM1, (by omega : p ≤ M)]
          nlinarith
      _ = (M - 1) * ((M - p) * M ^ p) := by ring
      _ ≤ (M - 1) * (M * (M - 1) ^ p) := Nat.mul_le_mul_left _ ih'
      _ = M * (M - 1) ^ (p + 1) := by rw [Nat.pow_succ]; ring

theorem bernoulli_add (a b : Nat) : ∀ q, a ^ q * (a + q * b) ≤ a * (a + b) ^ q := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      a ^ (q + 1) * (a + (q + 1) * b)
          = a ^ q * (a * a + (q + 1) * a * b) := by rw [Nat.pow_succ]; ring
      _ ≤ a ^ q * (a * a + (q + 1) * a * b + q * b * b) := by
          apply Nat.mul_le_mul_left; omega
      _ = (a + b) * (a ^ q * (a + q * b)) := by ring
      _ ≤ (a + b) * (a * (a + b) ^ q) := Nat.mul_le_mul_left _ ih
      _ = a * (a + b) ^ (q + 1) := by rw [Nat.pow_succ]; ring

theorem pow_sub_mul_le {a b q : Nat} (ha : 0 < a) (hb : b ≤ a) :
    (a - b) ^ q * (a + q * b) ≤ a ^ (q + 1) := by
  have h1 : (a - b) * (a + b) ≤ a * a := by
    zify [hb]
    nlinarith
  have h2 : (a - b) ^ q * (a + b) ^ q ≤ (a * a) ^ q := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left h1 q
  have h3 := bernoulli_add a b q
  have hmul : a ^ q * ((a - b) ^ q * (a + q * b)) ≤ a ^ q * a ^ (q + 1) := by
    calc
      a ^ q * ((a - b) ^ q * (a + q * b))
          = (a - b) ^ q * (a ^ q * (a + q * b)) := by ring
      _ ≤ (a - b) ^ q * (a * (a + b) ^ q) := Nat.mul_le_mul_left _ h3
      _ = a * ((a - b) ^ q * (a + b) ^ q) := by ring
      _ ≤ a * (a * a) ^ q := Nat.mul_le_mul_left _ h2
      _ = a ^ q * a ^ (q + 1) := by rw [Nat.mul_pow, Nat.pow_succ]; ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos ha)

theorem two_mul_pow_le {A : Nat} (hA : 0 < A) : 2 * A ^ A ≤ (A + 1) ^ A := by
  have h := bernoulli_add A 1 A
  have hmul : A * (2 * A ^ A) ≤ A * (A + 1) ^ A := by
    calc
      A * (2 * A ^ A) = A ^ A * (A + A * 1) := by ring
      _ ≤ A * (A + 1) ^ A := h
  exact Nat.le_of_mul_le_mul_left hmul hA

theorem le_of_pow_le_pow {x y q : Nat} (hq : 0 < q) (h : x ^ q ≤ y ^ q) : x ≤ y := by
  by_contra hgt
  have hlt : y < x := by omega
  have hpow : y ^ q < x ^ q := Nat.pow_lt_pow_left hlt (by omega)
  omega

theorem succ_le_two_pow : ∀ m : Nat, m + 1 ≤ 2 ^ m
  | 0 => by decide
  | m + 1 => by
    have ih := succ_le_two_pow m
    rw [Nat.pow_succ]
    omega

def potSum (mode n : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun w =>
    let s := summaryFrom mode w n
    8 * s.2 + phi s.1)).sum

theorem pot_step_0 :
    ((List.range 8).map (fun l =>
      let r := move 0 l
      8 * r.2 + phi r.1)).sum = 40 := by decide

theorem pot_step_1 :
    ((List.range 8).map (fun l =>
      let r := move 1 l
      8 * r.2 + phi r.1)).sum = 48 := by decide

theorem pot_step_2 :
    ((List.range 8).map (fun l =>
      let r := move 2 l
      8 * r.2 + phi r.1)).sum = 56 := by decide

theorem pot_step (mode : Nat) (hm : mode < 3) :
    ((List.range 8).map (fun l =>
      let r := move mode l
      8 * r.2 + phi r.1)).sum = 8 * (5 + phi mode) := by
  match mode with
  | 0 => exact pot_step_0
  | 1 => exact pot_step_1
  | 2 => exact pot_step_2
  | n + 3 => omega

theorem potSum_eq : ∀ n mode, mode < 3 → potSum mode n = 8 ^ n * (5 * n + phi mode) := by
  intro n
  induction n with
  | zero =>
    intro mode _
    simp [potSum, summaryFrom_zero]
  | succ n ih =>
    intro mode hm
    unfold potSum
    rw [sum_range_eight_pow_succ]
    have hinner : ((List.range 8).map (fun l =>
        ((List.range (8 ^ n)).map (fun rest =>
          let s := summaryFrom mode (l + 8 * rest) (n + 1)
          8 * s.2 + phi s.1)).sum)).sum =
      ((List.range 8).map (fun l =>
        let r := move mode l
        8 ^ n * (5 * n) + 8 ^ n * (8 * r.2 + phi r.1))).sum := by
      congr 1
      apply List.map_congr_left
      intro l hl
      have hl8 : l < 8 := List.mem_range.1 hl
      have hrew : ((List.range (8 ^ n)).map (fun rest =>
          let s := summaryFrom mode (l + 8 * rest) (n + 1)
          8 * s.2 + phi s.1)).sum =
        ((List.range (8 ^ n)).map (fun _ => 8 * (move mode l).2)).sum +
        potSum (move mode l).1 n := by
        unfold potSum
        rw [← list_sum_map_add]
        congr 1
        apply List.map_congr_left
        intro rest _
        rw [summaryFrom_succ mode l rest n hl8]
        ring
      rw [hrew, list_sum_map_const, List.length_range, ih _ (move_mode_lt mode l)]
      ring
    rw [hinner, list_sum_map_add, list_sum_map_const, List.length_range,
        list_sum_map_mul_left, pot_step mode hm, Nat.pow_succ']
    ring

theorem sum_gain_le (n : Nat) :
    8 * ((List.range (8 ^ n)).map (fun w => (summary w n).2)).sum ≤ 5 * n * 8 ^ n := by
  have hpot := potSum_eq n 0 (by omega)
  simp only [phi, Nat.add_zero] at hpot
  have hle : 8 * ((List.range (8 ^ n)).map (fun w => (summary w n).2)).sum ≤ potSum 0 n := by
    unfold potSum summary
    rw [← list_sum_map_mul_left]
    apply list_sum_map_le
    intro w _
    dsimp only
    omega
  rw [hpot] at hle
  linarith

theorem list_partition_sum {α : Type*} (xs : List α) (p : α → Bool) (f : α → Nat) :
    ((xs.filter p).map f).sum + ((xs.filter (fun x => !(p x))).map f).sum = (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true, List.map_cons, List.sum_cons] <;> omega

theorem list_partition_length {α : Type*} (xs : List α) (p : α → Bool) :
    (xs.filter p).length + (xs.filter (fun x => !(p x))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp only [List.filter_cons, hp, Bool.not_false, Bool.not_true,
      ↓reduceIte, Bool.false_eq_true, List.length_cons] <;> omega

theorem price_lower_bound (n d : Nat) (hd : 5 * n ≤ 8 * d) :
    2 ^ (5 * n) ≤ (d + 1) * price n d := by
  let xs := List.range (8 ^ n)
  let isGood : Nat → Bool := fun w => decide ((summary w n).2 ≤ d)
  let good := xs.filter isGood
  let bad := xs.filter (fun w => !(isGood w))
  have hgain_sum : (xs.map (fun w => (summary w n).2)).sum ≤ d * 8 ^ n := by
    have h1 := sum_gain_le n
    have h2 : 5 * n * 8 ^ n ≤ 8 * (d * 8 ^ n) := by
      calc
        5 * n * 8 ^ n ≤ (8 * d) * 8 ^ n := Nat.mul_le_mul_right _ hd
        _ = 8 * (d * 8 ^ n) := by ring
    exact Nat.le_of_mul_le_mul_left (le_trans h1 h2) (by omega)
  have hbad_lb : (d + 1) * bad.length ≤ (bad.map (fun w => (summary w n).2)).sum := by
    have h1 : (bad.map (fun _ => d + 1)).sum ≤ (bad.map (fun w => (summary w n).2)).sum := by
      apply list_sum_map_le
      intro w hw
      have hmem := (List.mem_filter.1 hw).2
      simp only [isGood, Bool.not_eq_true', decide_eq_false_iff_not] at hmem
      omega
    rw [list_sum_map_const, Nat.mul_comm] at h1
    exact h1
  have hbad_ub : (bad.map (fun w => (summary w n).2)).sum ≤ d * 8 ^ n := by
    have hpart := list_partition_sum xs isGood (fun w => (summary w n).2)
    have hle : (bad.map (fun w => (summary w n).2)).sum ≤ (xs.map (fun w => (summary w n).2)).sum := by
      dsimp only [bad]
      rw [← hpart]
      exact Nat.le_add_left _ _
    exact le_trans hle hgain_sum
  have hbad_len : (d + 1) * bad.length ≤ d * 8 ^ n := le_trans hbad_lb hbad_ub
  have htot_len : good.length + bad.length = 8 ^ n := by
    have := list_partition_length xs isGood
    simpa [good, bad, xs] using this
  have hgood_lb : 8 ^ n ≤ (d + 1) * good.length := by
    have h1 : (d + 1) * good.length + (d + 1) * bad.length = (d + 1) * 8 ^ n := by
      rw [← Nat.mul_add, htot_len]
    nlinarith
  have hprice_lb : good.length * 2 ^ (2 * n) ≤ price n d := by
    have h1 : (good.map (fun _ => 2 ^ (2 * n))).sum =
        (good.map (fun w => 2 ^ (2 * n - ((summary w n).2 - d)))).sum := by
      congr 1
      apply List.map_congr_left
      intro w hw
      have hmem := (List.mem_filter.1 hw).2
      simp only [isGood, decide_eq_true_eq] at hmem
      have hsub : (summary w n).2 - d = 0 := by omega
      rw [hsub, Nat.sub_zero]
    have hpart := list_partition_sum xs isGood (fun w => 2 ^ (2 * n - ((summary w n).2 - d)))
    rw [list_sum_map_const] at h1
    unfold price
    change good.length * 2 ^ (2 * n) ≤ (xs.map (fun w => 2 ^ (2 * n - ((summary w n).2 - d)))).sum
    rw [h1, ← hpart]
    dsimp only [good]
    exact Nat.le_add_right _ _
  have h5n : 2 ^ (5 * n) = 8 ^ n * 2 ^ (2 * n) := by
    have h8 : 8 ^ n = 2 ^ (3 * n) := by
      rw [show (8 : Nat) = 2 ^ 3 by decide, ← Nat.pow_mul]
    rw [h8, ← Nat.pow_add, show 3 * n + 2 * n = 5 * n by omega]
  calc
    2 ^ (5 * n) = 8 ^ n * 2 ^ (2 * n) := h5n
    _ ≤ ((d + 1) * good.length) * 2 ^ (2 * n) := Nat.mul_le_mul_right _ hgood_lb
    _ = (d + 1) * (good.length * 2 ^ (2 * n)) := by ring
    _ ≤ (d + 1) * price n d := Nat.mul_le_mul_left _ hprice_lb

theorem main (p q : Nat) (hq : 0 < q) :
    ((∃ (period start : Nat), 0 < period ∧
        ∀ n : Nat, start ≤ n →
          price n (p * n / q) ≤ 2 ^ (5 * n - n / period)) ↔ 8 * p < 5 * q) := by
  constructor
  · rintro ⟨period, start, hper, hbound⟩
    by_contra hge
    have h58 : 5 * q ≤ 8 * p := by omega
    let C := p * period + 1
    let m := max start (2 * C + 2)
    let t := 2 * m
    let n := q * period * t
    have ht_ge : start ≤ t := by omega
    have hn_ge : start ≤ n := by
      have hqp : 1 ≤ q * period := Nat.mul_pos hq hper
      calc
        start ≤ t := ht_ge
        _ = 1 * t := by ring
        _ ≤ (q * period) * t := Nat.mul_le_mul_right t hqp
    have hd_eq : p * n / q = p * period * t := by
      have h1 : p * n = q * (p * period * t) := by dsimp only [n]; ring
      rw [h1, Nat.mul_div_right _ hq]
    have hper_eq : n / period = q * t := by
      have h1 : n = period * (q * t) := by dsimp only [n]; ring
      rw [h1, Nat.mul_div_right _ hper]
    have h5n_le : 5 * n ≤ 8 * (p * n / q) := by
      rw [hd_eq]
      dsimp only [n]
      calc
        5 * (q * period * t) = (5 * q) * (period * t) := by ring
        _ ≤ (8 * p) * (period * t) := Nat.mul_le_mul_right _ h58
        _ = 8 * (p * period * t) := by ring
    have hlb := price_lower_bound n (p * n / q) h5n_le
    have hub := hbound n hn_ge
    have hcomb : 2 ^ (5 * n) ≤ (p * n / q + 1) * 2 ^ (5 * n - n / period) :=
      le_trans hlb (Nat.mul_le_mul_left _ hub)
    have hdiv_le : n / period ≤ 5 * n := by
      have : n / period ≤ n := Nat.div_le_self n period
      omega
    have hsplit : 2 ^ (5 * n) = 2 ^ (n / period) * 2 ^ (5 * n - n / period) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' hdiv_le]
    rw [hsplit] at hcomb
    have hpow_le : 2 ^ (n / period) ≤ p * n / q + 1 :=
      Nat.le_of_mul_le_mul_right hcomb (Nat.two_pow_pos _)
    rw [hper_eq, hd_eq] at hpow_le
    have h2t_le : 2 ^ t ≤ 2 ^ (q * t) := by
      apply Nat.pow_le_pow_right (by omega)
      calc
        t = 1 * t := by ring
        _ ≤ q * t := Nat.mul_le_mul_right t hq
    have hpow_m : m + 1 ≤ 2 ^ m := succ_le_two_pow m
    have h2t_lb : (m + 1) * (m + 1) ≤ 2 ^ t := by
      have hsq : 2 ^ t = 2 ^ m * 2 ^ m := by
        dsimp only [t]
        rw [show 2 * m = m + m by omega, Nat.pow_add]
      rw [hsq]
      exact Nat.mul_le_mul hpow_m hpow_m
    have hlt : p * period * t + 1 < (m + 1) * (m + 1) := by
      have hmC : 2 * C + 2 ≤ m := le_max_right _ _
      have hC : p * period ≤ C := by dsimp only [C]; omega
      dsimp only [t]
      nlinarith
    omega
  · intro hlt
    let M := 2 * q + 5 * p * q + p + 2
    have hM2 : 2 ≤ M := by omega
    have hMp : p ≤ M := by omega
    let A := M ^ p * (8 * M ^ 2 - 5 * M + 2) ^ q
    let B := (M - 1) ^ p * (8 * M ^ 2) ^ q
    have hA_pos : 0 < A := by
      have h1 : 0 < M ^ p := Nat.pow_pos (by omega)
      have h2 : 0 < 8 * M ^ 2 - 5 * M + 2 := by nlinarith
      exact Nat.mul_pos h1 (Nat.pow_pos h2)
    have hAB : A < B := by
      have hbern1 : (M - p) * M ^ p ≤ M * (M - 1) ^ p := bernoulli_sub p hMp
      have h8a : 0 < 8 * M ^ 2 := by nlinarith
      have h5M_le : 5 * M ≤ 8 * M ^ 2 := by nlinarith
      have h8b : 5 * M - 2 ≤ 8 * M ^ 2 := by omega
      have hsub_eq : 8 * M ^ 2 - (5 * M - 2) = 8 * M ^ 2 - 5 * M + 2 := by
        have : 2 ≤ 5 * M := by omega
        omega
      have hbern2 := pow_sub_mul_le (q := q) h8a h8b
      rw [hsub_eq, Nat.pow_succ] at hbern2
      have hprod : A * ((M - p) * (8 * M ^ 2 + q * (5 * M - 2))) ≤ B * (8 * M ^ 3) := by
        calc
          A * ((M - p) * (8 * M ^ 2 + q * (5 * M - 2)))
              = ((M - p) * M ^ p) * ((8 * M ^ 2 - 5 * M + 2) ^ q * (8 * M ^ 2 + q * (5 * M - 2))) := by
                  dsimp only [A]; ring
          _ ≤ (M * (M - 1) ^ p) * ((8 * M ^ 2) ^ q * (8 * M ^ 2)) := Nat.mul_le_mul hbern1 hbern2
          _ = B * (8 * M ^ 3) := by dsimp only [B]; ring
      have hcoef : 8 * M ^ 3 < (M - p) * (8 * M ^ 2 + q * (5 * M - 2)) := by
        have hgap : 8 * p + 1 ≤ 5 * q := by omega
        have hMgt : 2 * q + 5 * p * q < M := by omega
        zify [hMp, (by omega : 2 ≤ 5 * M)]
        nlinarith
      have hstrict : A * (8 * M ^ 3) < B * (8 * M ^ 3) :=
        lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left hcoef hA_pos) hprod
      exact Nat.lt_of_mul_lt_mul_right hstrict
    let period := 2 * q * A
    let start := 2 * q * A
    refine ⟨period, start, by dsimp only [period]; exact Nat.mul_pos (Nat.mul_pos (by omega) hq) hA_pos, ?_⟩
    intro n hn
    let d := p * n / q
    let k := n / period
    have hk_pos : 1 ≤ k := by
      have hper_pos : 0 < period := Nat.mul_pos (Nat.mul_pos (by omega) hq) hA_pos
      exact Nat.div_pos hn hper_pos
    have hkn : period * k ≤ n := Nat.mul_div_le n period
    have hqd : q * d ≤ p * n := Nat.mul_div_le (p * n) q
    have hch := price_chernoff M n d hM2
    have hgs := genSum_0_le M hM2 n
    have hstep1 : price n d * (M - 1) ^ d * M ^ (2 * n) ≤
        2 * 2 ^ (2 * n) * M ^ d * (8 * M ^ 2 - 5 * M + 2) ^ n := by
      calc
        price n d * (M - 1) ^ d * M ^ (2 * n)
            ≤ 2 ^ (2 * n) * M ^ d * genSum M 0 n := hch
        _ ≤ 2 ^ (2 * n) * M ^ d * (2 * (8 * M ^ 2 - 5 * M + 2) ^ n) := Nat.mul_le_mul_left _ hgs
        _ = 2 * 2 ^ (2 * n) * M ^ d * (8 * M ^ 2 - 5 * M + 2) ^ n := by ring
    have h2pow_AB : (2 * 2 ^ k) ^ q * A ^ n ≤ B ^ n := by
      have hq1k : (1 + k) * q ≤ 2 * q * k := by nlinarith
      have hpow2 : (2 * 2 ^ k) ^ q ≤ 2 ^ (2 * q * k) := by
        have h1 : 2 * 2 ^ k = 2 ^ (1 + k) := by rw [Nat.pow_add, Nat.pow_one]
        rw [h1, ← Nat.pow_mul]
        exact Nat.pow_le_pow_right (by omega) hq1k
      have hBA : 2 * A ^ A ≤ B ^ A :=
        le_trans (two_mul_pow_le hA_pos) (Nat.pow_le_pow_left (by omega) A)
      have hBAk : 2 ^ (2 * q * k) * A ^ (period * k) ≤ B ^ (period * k) := by
        have h1 := Nat.pow_le_pow_left hBA (2 * q * k)
        rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at h1
        have heq : A * (2 * q * k) = period * k := by dsimp only [period]; ring
        rw [heq] at h1
        exact h1
      have hrem : A ^ (n - period * k) ≤ B ^ (n - period * k) := Nat.pow_le_pow_left (by omega) _
      have hn_eq : period * k + (n - period * k) = n := Nat.add_sub_cancel' hkn
      have hAn_eq : A ^ n = A ^ (period * k) * A ^ (n - period * k) := by
        rw [← Nat.pow_add, hn_eq]
      calc
        (2 * 2 ^ k) ^ q * A ^ n
            ≤ 2 ^ (2 * q * k) * A ^ n := Nat.mul_le_mul_right _ hpow2
        _ = (2 ^ (2 * q * k) * A ^ (period * k)) * A ^ (n - period * k) := by
            rw [hAn_eq]; ring
        _ ≤ B ^ (period * k) * B ^ (n - period * k) := Nat.mul_le_mul hBAk hrem
        _ = B ^ n := by rw [← Nat.pow_add, hn_eq]
    have hstep2 : (price n d * 2 ^ k) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n)) ≤
        (2 ^ (5 * n)) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n)) := by
      have hpow_q := Nat.pow_le_pow_left (Nat.mul_le_mul_left (2 ^ k) hstep1) q
      have hremM : (M - 1) ^ (p * n - q * d) ≤ M ^ (p * n - q * d) :=
        Nat.pow_le_pow_left (by omega) _
      have hpn_eq : q * d + (p * n - q * d) = p * n := Nat.add_sub_cancel' hqd
      have h5n_eq : (2 ^ (2 * n)) ^ q * (8 * M ^ 2) ^ (q * n) =
          (2 ^ (5 * n)) ^ q * M ^ (2 * q * n) := by
        have h8 : (8 : Nat) = 2 ^ 3 := by decide
        calc
          (2 ^ (2 * n)) ^ q * (8 * M ^ 2) ^ (q * n)
              = 2 ^ (2 * n * q) * (8 ^ (q * n) * (M ^ 2) ^ (q * n)) := by
                  rw [Nat.mul_pow, ← Nat.pow_mul]
          _ = (2 ^ (2 * n * q) * (2 ^ 3) ^ (q * n)) * (M ^ 2) ^ (q * n) := by rw [h8]; ring
          _ = 2 ^ (2 * n * q + 3 * (q * n)) * M ^ (2 * (q * n)) := by
                  rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_mul]
          _ = 2 ^ (5 * n * q) * M ^ (2 * q * n) := by
                  rw [show 2 * n * q + 3 * (q * n) = 5 * n * q by ring,
                      show 2 * (q * n) = 2 * q * n by ring]
          _ = (2 ^ (5 * n)) ^ q * M ^ (2 * q * n) := by rw [← Nat.pow_mul]
      have hlhs : (price n d * 2 ^ k) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n)) =
          (2 ^ k * (price n d * (M - 1) ^ d * M ^ (2 * n))) ^ q * (M - 1) ^ (p * n - q * d) := by
        have h1 : (M - 1) ^ (p * n) = ((M - 1) ^ d) ^ q * (M - 1) ^ (p * n - q * d) := by
          rw [← Nat.pow_mul, ← Nat.pow_add, show d * q = q * d by ring, hpn_eq]
        have h2 : M ^ (2 * q * n) = (M ^ (2 * n)) ^ q := by
          rw [← Nat.pow_mul, show 2 * n * q = 2 * q * n by ring]
        rw [h1, h2]
        simp only [Nat.mul_pow]
        ring
      have hmid : (2 ^ k * (2 * 2 ^ (2 * n) * M ^ d * (8 * M ^ 2 - 5 * M + 2) ^ n)) ^ q * M ^ (p * n - q * d) =
          (2 ^ (2 * n)) ^ q * ((2 * 2 ^ k) ^ q * A ^ n) := by
        have h1 : (M ^ d) ^ q * M ^ (p * n - q * d) = (M ^ p) ^ n := by
          rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_mul, show d * q = q * d by ring, hpn_eq]
        have h2 : ((8 * M ^ 2 - 5 * M + 2) ^ n) ^ q = ((8 * M ^ 2 - 5 * M + 2) ^ q) ^ n := by
          rw [← Nat.pow_mul, ← Nat.pow_mul, show n * q = q * n by ring]
        dsimp only [A]
        simp only [Nat.mul_pow]
        calc
          (2 ^ k) ^ q * (2 ^ q * (2 ^ (2 * n)) ^ q * (M ^ d) ^ q * ((8 * M ^ 2 - 5 * M + 2) ^ n) ^ q) * M ^ (p * n - q * d)
              = (2 ^ (2 * n)) ^ q * ((2 ^ q * (2 ^ k) ^ q) * (((M ^ d) ^ q * M ^ (p * n - q * d)) * ((8 * M ^ 2 - 5 * M + 2) ^ n) ^ q)) := by ring
          _ = (2 ^ (2 * n)) ^ q * ((2 ^ q * (2 ^ k) ^ q) * ((M ^ p) ^ n * ((8 * M ^ 2 - 5 * M + 2) ^ q) ^ n)) := by
              rw [h1, h2]
      have hrhs : (2 ^ (2 * n)) ^ q * B ^ n =
          (2 ^ (5 * n)) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n)) := by
        have hB : B ^ n = (M - 1) ^ (p * n) * (8 * M ^ 2) ^ (q * n) := by
          dsimp only [B]
          rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul]
        rw [hB]
        calc
          (2 ^ (2 * n)) ^ q * ((M - 1) ^ (p * n) * (8 * M ^ 2) ^ (q * n))
              = ((2 ^ (2 * n)) ^ q * (8 * M ^ 2) ^ (q * n)) * (M - 1) ^ (p * n) := by ring
          _ = ((2 ^ (5 * n)) ^ q * M ^ (2 * q * n)) * (M - 1) ^ (p * n) := by rw [h5n_eq]
          _ = (2 ^ (5 * n)) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n)) := by ring
      calc
        (price n d * 2 ^ k) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n))
            = (2 ^ k * (price n d * (M - 1) ^ d * M ^ (2 * n))) ^ q * (M - 1) ^ (p * n - q * d) := hlhs
        _ ≤ (2 ^ k * (2 * 2 ^ (2 * n) * M ^ d * (8 * M ^ 2 - 5 * M + 2) ^ n)) ^ q * (M - 1) ^ (p * n - q * d) :=
              Nat.mul_le_mul_right _ hpow_q
        _ ≤ (2 ^ k * (2 * 2 ^ (2 * n) * M ^ d * (8 * M ^ 2 - 5 * M + 2) ^ n)) ^ q * M ^ (p * n - q * d) :=
              Nat.mul_le_mul_left _ hremM
        _ = (2 ^ (2 * n)) ^ q * ((2 * 2 ^ k) ^ q * A ^ n) := hmid
        _ ≤ (2 ^ (2 * n)) ^ q * B ^ n := Nat.mul_le_mul_left _ h2pow_AB
        _ = (2 ^ (5 * n)) ^ q * ((M - 1) ^ (p * n) * M ^ (2 * q * n)) := hrhs
    have hposM : 0 < (M - 1) ^ (p * n) * M ^ (2 * q * n) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
    have hstep3 : (price n d * 2 ^ k) ^ q ≤ (2 ^ (5 * n)) ^ q :=
      Nat.le_of_mul_le_mul_right hstep2 hposM
    have hstep4 : price n d * 2 ^ k ≤ 2 ^ (5 * n) := le_of_pow_le_pow hq hstep3
    have hk_le : k ≤ 5 * n := by
      have : k ≤ n := Nat.div_le_self n period
      omega
    have hsplit5 : 2 ^ (5 * n) = 2 ^ (5 * n - k) * 2 ^ k := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hk_le]
    rw [hsplit5] at hstep4
    exact Nat.le_of_mul_le_mul_right hstep4 (Nat.two_pow_pos k)

end PEqualNP.Outside.L_meta_25542_aux

theorem PEqualNP.Outside.L_meta_25542 :
let move := fun (mode letter : Nat) =>
    let aligned := ((mode == 1) && letter.testBit 0 && letter.testBit 1) ||
      ((mode == 2) && letter.testBit 1)
    let hit := letter.testBit 2
    (if aligned then (if hit then 0 else 2) else 1,
      hit.toNat + (aligned && hit).toNat)
  let summary := fun (code length : Nat) =>
    (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
      let result := move st.1 ((code >>> (3 * digitPos)) % 8)
      (result.1, st.2 + result.2)) (0, 0)
  let price := fun (n depth : Nat) =>
    ((List.range (8 ^ n)).map (fun codeWord =>
      2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum
  ∀ (p q : Nat), 0 < q →
    ((∃ (period start : Nat), 0 < period ∧
        ∀ n : Nat, start ≤ n →
          price n (p * n / q) ≤ 2 ^ (5 * n - n / period)) ↔ 8 * p < 5 * q) :=
  PEqualNP.Outside.L_meta_25542_aux.main
