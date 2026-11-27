import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25581_aux

private def move (mode letter : Nat) : Nat × Nat :=
  let near := letter.testBit 0
  let far := letter.testBit 1
  let hit := letter.testBit 2
  let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
    ((mode == 3) && near)
  let diagonal := (mode == 3) ||
    (!hit && (((mode == 1) && !near && !far) || (mode == 2)))
  (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
    hit.toNat + (aligned && hit).toNat)

private def runFrom (s code length : Nat) : Nat × Nat :=
  (List.range length).foldl (fun (st : Nat × Nat) digitPos =>
    let result := move st.1 ((code >>> (3 * digitPos)) % 8)
    (result.1, st.2 + result.2)) (s, 0)

private def summary (code length : Nat) : Nat × Nat :=
  runFrom 0 code length

private def price (n depth : Nat) : Nat :=
  ((List.range (8 ^ n)).map (fun codeWord =>
    2 ^ (2 * n - ((summary codeWord n).2 - depth)))).sum

private def pot (s : Nat) : Nat :=
  match s with
  | 0 => 0
  | 1 => 3
  | 2 => 6
  | _ => 7

private lemma move_fst_lt_four (s l : Nat) : (move s l).1 < 4 := by
  simp only [move]
  split_ifs <;> omega

private lemma move_snd_le_two (s l : Nat) : (move s l).2 ≤ 2 := by
  simp only [move]
  cases l.testBit 2 <;> cases (((s == 1) && l.testBit 0 && l.testBit 1) ||
    ((s == 2) && l.testBit 1) || ((s == 3) && l.testBit 0)) <;> decide

private lemma foldl_shift (f : Nat → Nat → Nat × Nat) :
    ∀ (L : List Nat) (s acc : Nat),
      L.foldl (fun (st : Nat × Nat) d =>
        let res := f st.1 d
        (res.1, st.2 + res.2)) (s, acc) =
      ((L.foldl (fun (st : Nat × Nat) d =>
        let res := f st.1 d
        (res.1, st.2 + res.2)) (s, 0)).1,
       acc + (L.foldl (fun (st : Nat × Nat) d =>
        let res := f st.1 d
        (res.1, st.2 + res.2)) (s, 0)).2) := by
  intro L
  induction L with
  | nil =>
    intro s acc
    simp
  | cons a t ih =>
    intro s acc
    simp only [List.foldl_cons, zero_add]
    rw [ih (f s a).1 (acc + (f s a).2), ih (f s a).1 (f s a).2]
    ext
    · rfl
    · dsimp only
      omega

private lemma shift_eight_mul_add (c l d : Nat) (hl : l < 8) :
    ((8 * c + l) >>> (3 * (d + 1))) % 8 = (c >>> (3 * d)) % 8 := by
  have h1 : (8 * c + l) >>> (3 * (d + 1)) = (8 * c + l) / 2 ^ (3 * d + 3) := by
    rw [Nat.shiftRight_eq_div_pow, show 3 * (d + 1) = 3 * d + 3 by omega]
  have h2 : c >>> (3 * d) = c / 2 ^ (3 * d) := Nat.shiftRight_eq_div_pow c (3 * d)
  rw [h1, h2, pow_add, mul_comm (2 ^ (3 * d)) (2 ^ 3), ← Nat.div_div_eq_div_mul]
  have hdiv : (8 * c + l) / 2 ^ 3 = c := by
    have : 2 ^ 3 = 8 := by decide
    rw [this]
    omega
  rw [hdiv]

private lemma runFrom_succ (s c l n : Nat) (hl : l < 8) :
    runFrom s (8 * c + l) (n + 1) =
      ((runFrom (move s l).1 c n).1, (move s l).2 + (runFrom (move s l).1 c n).2) := by
  unfold runFrom
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : ((8 * c + l) >>> (3 * 0)) % 8 = l := by
    simp only [mul_zero, Nat.shiftRight_zero]
    omega
  simp only [h0, zero_add]
  have hfn : (fun (st : Nat × Nat) (d : Nat) =>
      let result := move st.1 (((8 * c + l) >>> (3 * (d + 1))) % 8)
      (result.1, st.2 + result.2)) =
      (fun (st : Nat × Nat) (d : Nat) =>
        let result := move st.1 ((c >>> (3 * d)) % 8)
        (result.1, st.2 + result.2)) := by
    funext st d
    rw [shift_eight_mul_add c l d hl]
  rw [hfn]
  exact foldl_shift (fun m d => move m ((c >>> (3 * d)) % 8)) (List.range n) (move s l).1 (move s l).2

private lemma runFrom_snd_le (s c n : Nat) : (runFrom s c n).2 ≤ 2 * n := by
  induction n generalizing s c with
  | zero =>
    simp [runFrom]
  | succ n ih =>
    have hcl : c = 8 * (c / 8) + c % 8 := by omega
    have hlt : c % 8 < 8 := Nat.mod_lt c (by omega)
    conv_lhs => rw [hcl]
    rw [runFrom_succ s (c / 8) (c % 8) n hlt]
    have h1 := move_snd_le_two s (c % 8)
    have h2 := ih (move s (c % 8)).1 (c / 8)
    dsimp only
    omega

private lemma list_range_map_sum {M : Type*} [AddCommMonoid M] (N : Nat) (f : Nat → M) :
    ((List.range N).map f).sum = ∑ x ∈ Finset.range N, f x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton,
      Finset.sum_range_succ, ih]

private lemma sum_range_eight_pow {M : Type*} [AddCommMonoid M] (n : Nat) (F : Nat → M) :
    ∑ w ∈ Finset.range (8 ^ (n + 1)), F w =
      ∑ l ∈ Finset.range 8, ∑ c ∈ Finset.range (8 ^ n), F (8 * c + l) := by
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => 8 * p.2 + p.1) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    rw [Finset.mem_range, pow_succ]
    omega
  · intro p1 h1 p2 h2 hEq
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at h1 h2
    ext <;> omega
  · intro w hw
    rw [Finset.mem_range, pow_succ] at hw
    refine ⟨(w % 8, w / 8), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨by omega, by omega⟩
    · omega
  · intro _ _
    rfl

private lemma step_pot_sum (s : Nat) (hs : s < 4) :
    ∑ l ∈ Finset.range 8, (20 * (move s l).2 + pot (move s l).1) = 8 * pot s + 104 := by
  interval_cases s <;> decide

private lemma mean_gain_pot (n : Nat) :
    ∀ s < 4,
      ∑ w ∈ Finset.range (8 ^ n), (20 * (runFrom s w n).2 + pot (runFrom s w n).1) =
        (pot s + 13 * n) * 8 ^ n := by
  induction n with
  | zero =>
    intro s _
    simp [runFrom]
  | succ n ih =>
    intro s hs
    rw [sum_range_eight_pow]
    have hinner : ∀ l ∈ Finset.range 8,
        ∑ c ∈ Finset.range (8 ^ n),
          (20 * (runFrom s (8 * c + l) (n + 1)).2 + pot (runFrom s (8 * c + l) (n + 1)).1) =
        (20 * (move s l).2 + pot (move s l).1 + 13 * n) * 8 ^ n := by
      intro l hl
      have hlt : l < 8 := Finset.mem_range.1 hl
      have h1 : ∑ c ∈ Finset.range (8 ^ n),
            (20 * (runFrom s (8 * c + l) (n + 1)).2 + pot (runFrom s (8 * c + l) (n + 1)).1) =
          ∑ c ∈ Finset.range (8 ^ n),
            (20 * (move s l).2 +
              (20 * (runFrom (move s l).1 c n).2 + pot (runFrom (move s l).1 c n).1)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [runFrom_succ s c l n hlt]
        dsimp only
        omega
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        ih (move s l).1 (move_fst_lt_four s l)]
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul, Finset.sum_add_distrib,
      step_pot_sum s hs, Finset.sum_const, Finset.card_range, smul_eq_mul, pow_succ]
    ring

private lemma forward_dir (p q : Nat) (hq : 0 < q) (hge : 13 * q ≤ 20 * p) :
    ¬ ∃ (period start : Nat), 0 < period ∧
      ∀ n : Nat, start ≤ n →
        price n (p * n / q) ≤ 2 ^ (5 * n - n / period) := by
  rintro ⟨period, start, hper, hbound⟩
  have hmean : ∀ n, ∑ w ∈ Finset.range (8 ^ n), 20 * (summary w n).2 ≤ 13 * n * 8 ^ n := by
    intro n
    have h1 := mean_gain_pot n 0 (by omega)
    have hle : ∑ w ∈ Finset.range (8 ^ n), 20 * (summary w n).2 ≤
        ∑ w ∈ Finset.range (8 ^ n), (20 * (runFrom 0 w n).2 + pot (runFrom 0 w n).1) :=
      Finset.sum_le_sum fun w _ => by simp [summary]
    rw [h1] at hle
    simpa [pot] using hle
  have hlow_price : ∀ n, 2 ^ (5 * n) ≤ 20 * (p * n / q + 1) * price n (p * n / q) := by
    intro n
    let d := p * n / q
    let S := Finset.range (8 ^ n)
    let Low := S.filter (fun w => (summary w n).2 ≤ d)
    let High := S.filter (fun w => ¬ (summary w n).2 ≤ d)
    have hcard_split : Low.card + High.card = 8 ^ n := by
      rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
    have hd_ge : 13 * n + 1 ≤ 20 * (d + 1) := by
      have hdiv : p * n < q * (d + 1) := by
        have h1 := Nat.div_add_mod (p * n) q
        have h2 := Nat.mod_lt (p * n) hq
        dsimp only [d]
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have h3 : 13 * n * q ≤ 20 * (p * n) := by
        calc 13 * n * q = (13 * q) * n := by ring
          _ ≤ (20 * p) * n := Nat.mul_le_mul_right n hge
          _ = 20 * (p * n) := by ring
      have h4 : 20 * (p * n) < 20 * (d + 1) * q := by
        calc 20 * (p * n) < 20 * (q * (d + 1)) := Nat.mul_lt_mul_of_pos_left hdiv (by omega)
          _ = 20 * (d + 1) * q := by ring
      have h5 : 13 * n * q < 20 * (d + 1) * q := lt_of_le_of_lt h3 h4
      have h6 : 13 * n < 20 * (d + 1) := Nat.lt_of_mul_lt_mul_right h5
      omega
    have hhigh_bound : 20 * (d + 1) * High.card ≤ 13 * n * 8 ^ n := by
      calc 20 * (d + 1) * High.card
          = ∑ _w ∈ High, 20 * (d + 1) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ w ∈ High, 20 * (summary w n).2 := by
              refine Finset.sum_le_sum fun w hw => ?_
              have hgt : d < (summary w n).2 := Nat.lt_of_not_ge (Finset.mem_filter.1 hw).2
              omega
        _ ≤ ∑ w ∈ S, 20 * (summary w n).2 :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ 13 * n * 8 ^ n := hmean n
    have hlow_card : 8 ^ n ≤ 20 * (d + 1) * Low.card := by
      nlinarith
    have hprice_ge : Low.card * 2 ^ (2 * n) ≤ price n d := by
      unfold price
      rw [list_range_map_sum]
      calc Low.card * 2 ^ (2 * n)
          = ∑ _w ∈ Low, 2 ^ (2 * n) := by rw [Finset.sum_const, smul_eq_mul]
        _ = ∑ w ∈ Low, 2 ^ (2 * n - ((summary w n).2 - d)) := by
              refine Finset.sum_congr rfl fun w hw => ?_
              have hle : (summary w n).2 ≤ d := (Finset.mem_filter.1 hw).2
              have hsub : (summary w n).2 - d = 0 := Nat.sub_eq_zero_of_le hle
              rw [hsub, Nat.sub_zero]
        _ ≤ ∑ w ∈ S, 2 ^ (2 * n - ((summary w n).2 - d)) :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hpow5 : 2 ^ (5 * n) = 8 ^ n * 2 ^ (2 * n) := by
      have h8 : (8 : Nat) = 2 ^ 3 := by decide
      rw [h8, ← pow_mul, ← pow_add]
      congr 1
      omega
    calc 2 ^ (5 * n)
        = 8 ^ n * 2 ^ (2 * n) := hpow5
      _ ≤ (20 * (d + 1) * Low.card) * 2 ^ (2 * n) := Nat.mul_le_mul_right _ hlow_card
      _ = 20 * (d + 1) * (Low.card * 2 ^ (2 * n)) := by ring
      _ ≤ 20 * (d + 1) * price n d := Nat.mul_le_mul_left _ hprice_ge
  let M := 20 * (p * period + 1)
  let k := max start (2 * M + 4)
  let n := period * k
  have hn_ge : start ≤ n := by
    have hk : start ≤ k := le_max_left _ _
    calc start ≤ k := hk
      _ = 1 * k := (one_mul k).symm
      _ ≤ period * k := Nat.mul_le_mul_right k hper
  have hdiv_n : n / period = k := Nat.mul_div_cancel_left k hper
  have h1 := hlow_price n
  have h2 := hbound n hn_ge
  rw [hdiv_n] at h2
  have h3 : 2 ^ (5 * n) ≤ 20 * (p * n / q + 1) * 2 ^ (5 * n - k) :=
    le_trans h1 (Nat.mul_le_mul_left _ h2)
  have hk_le : k ≤ 5 * n := by
    have : 1 * k ≤ period * k := Nat.mul_le_mul_right k hper
    omega
  have hsplit : 2 ^ (5 * n) = 2 ^ k * 2 ^ (5 * n - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at h3
  have hpow_le : 2 ^ k ≤ 20 * (p * n / q + 1) :=
    Nat.le_of_mul_le_mul_right h3 (Nat.two_pow_pos _)
  have hpn_le : p * n / q ≤ p * n := Nat.div_le_self _ _
  have hlin : 20 * (p * n / q + 1) ≤ M * k := by
    have hkpos : 1 ≤ k := by omega
    have h1 : 20 * (p * n / q + 1) ≤ 20 * (p * n + 1) := by omega
    have h2 : 20 * (p * (period * k) + 1) ≤ (20 * (p * period + 1)) * k := by nlinarith
    exact le_trans h1 h2
  have hquad : ∀ m : Nat, m * m ≤ 2 ^ (m + 4) := by
    intro m
    induction m with
    | zero => decide
    | succ m ih =>
      cases m with
      | zero => decide
      | succ m' =>
        cases m' with
        | zero => decide
        | succ m'' =>
          cases m'' with
          | zero => decide
          | succ m''' =>
            have hpow : 2 ^ (m''' + 4 + 4) = 2 * 2 ^ (m''' + 3 + 4) := by
              rw [show m''' + 4 + 4 = (m''' + 3 + 4) + 1 by omega, pow_succ, mul_comm]
            have hstep : (m''' + 4) * (m''' + 4) ≤ 2 * ((m''' + 3) * (m''' + 3)) := by nlinarith
            nlinarith
  have hbig : M * k < 2 ^ k := by
    have hkm : 2 * M + 4 ≤ k := le_max_right _ _
    have h4 : (k - 4) * (k - 4) ≤ 2 ^ k := by
      have hk4 : k - 4 + 4 = k := by omega
      have hq := hquad (k - 4)
      rwa [hk4] at hq
    have hstrict : M * k < (k - 4) * (k - 4) := by
      have hMpos : 20 ≤ M := by omega
      have hk_eq : k = (k - 4) + 4 := by omega
      set r := k - 4
      rw [hk_eq] at hkm ⊢
      nlinarith
    omega
  omega

private def moveTab (s l : Nat) : Nat × Nat :=
  match s, l with
  | 0, 0 => (1, 0) | 0, 1 => (1, 0) | 0, 2 => (1, 0) | 0, 3 => (1, 0)
  | 0, 4 => (1, 1) | 0, 5 => (1, 1) | 0, 6 => (1, 1) | 0, 7 => (1, 1)
  | 1, 0 => (3, 0) | 1, 1 => (1, 0) | 1, 2 => (1, 0) | 1, 3 => (2, 0)
  | 1, 4 => (1, 1) | 1, 5 => (1, 1) | 1, 6 => (1, 1) | 1, 7 => (0, 2)
  | 2, 0 => (3, 0) | 2, 1 => (3, 0) | 2, 2 => (2, 0) | 2, 3 => (2, 0)
  | 2, 4 => (1, 1) | 2, 5 => (1, 1) | 2, 6 => (0, 2) | 2, 7 => (0, 2)
  | 3, 0 => (3, 0) | 3, 1 => (2, 0) | 3, 2 => (3, 0) | 3, 3 => (2, 0)
  | 3, 4 => (3, 1) | 3, 5 => (0, 2) | 3, 6 => (3, 1) | 3, 7 => (0, 2)
  | _, _ => (0, 0)

private lemma move_eq_moveTab : ∀ s < 4, ∀ l < 8, move s l = moveTab s l := by
  decide

private lemma step_matrix_bound (a : ℚ) (_ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (s : Nat) (hs : s < 4) :
    ∑ l ∈ Finset.range 8,
        (1 - a) ^ (move s l).2 * (1 - a * (pot (move s l).1 : ℚ) / 20) ≤
      8 * (1 - 13 / 20 * a + a ^ 2) * (1 - a * (pot s : ℚ) / 20) := by
  have hrew : ∑ l ∈ Finset.range 8,
        (1 - a) ^ (move s l).2 * (1 - a * (pot (move s l).1 : ℚ) / 20) =
      ∑ l ∈ Finset.range 8,
        (1 - a) ^ (moveTab s l).2 * (1 - a * (pot (moveTab s l).1 : ℚ) / 20) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [move_eq_moveTab s hs l (Finset.mem_range.1 hl)]
  rw [hrew]
  have hrange : (Finset.range 8 : Finset Nat) = {0, 1, 2, 3, 4, 5, 6, 7} := by decide
  rw [hrange]
  interval_cases s <;>
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      OfNat.zero_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true, moveTab, pot] <;>
    norm_num <;>
    nlinarith

private lemma weighted_sum_bound (a : ℚ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) (n : Nat) :
    ∀ s < 4,
      ∑ w ∈ Finset.range (8 ^ n),
          (1 - a) ^ (runFrom s w n).2 * (1 - a * (pot (runFrom s w n).1 : ℚ) / 20) ≤
        (8 * (1 - 13 / 20 * a + a ^ 2)) ^ n * (1 - a * (pot s : ℚ) / 20) := by
  induction n with
  | zero =>
    intro s _
    simp [runFrom]
  | succ n ih =>
    intro s hs
    rw [sum_range_eight_pow]
    have hza : 0 ≤ 1 - a := by linarith
    have hinner : ∀ l ∈ Finset.range 8,
        ∑ c ∈ Finset.range (8 ^ n),
          (1 - a) ^ (runFrom s (8 * c + l) (n + 1)).2 *
            (1 - a * (pot (runFrom s (8 * c + l) (n + 1)).1 : ℚ) / 20) ≤
        (8 * (1 - 13 / 20 * a + a ^ 2)) ^ n *
          ((1 - a) ^ (move s l).2 * (1 - a * (pot (move s l).1 : ℚ) / 20)) := by
      intro l hl
      have hlt : l < 8 := Finset.mem_range.1 hl
      have heq : ∑ c ∈ Finset.range (8 ^ n),
            (1 - a) ^ (runFrom s (8 * c + l) (n + 1)).2 *
              (1 - a * (pot (runFrom s (8 * c + l) (n + 1)).1 : ℚ) / 20) =
          (1 - a) ^ (move s l).2 *
            ∑ c ∈ Finset.range (8 ^ n),
              (1 - a) ^ (runFrom (move s l).1 c n).2 *
                (1 - a * (pot (runFrom (move s l).1 c n).1 : ℚ) / 20) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [runFrom_succ s c l n hlt]
        dsimp only
        rw [pow_add, mul_assoc]
      rw [heq]
      have hle := mul_le_mul_of_nonneg_left (ih (move s l).1 (move_fst_lt_four s l))
        (pow_nonneg hza (move s l).2)
      linarith
    have h1 : ∑ l ∈ Finset.range 8, ∑ c ∈ Finset.range (8 ^ n),
          (1 - a) ^ (runFrom s (8 * c + l) (n + 1)).2 *
            (1 - a * (pot (runFrom s (8 * c + l) (n + 1)).1 : ℚ) / 20) ≤
        (8 * (1 - 13 / 20 * a + a ^ 2)) ^ n *
          ∑ l ∈ Finset.range 8, (1 - a) ^ (move s l).2 * (1 - a * (pot (move s l).1 : ℚ) / 20) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hinner
    have hρ : 0 ≤ 8 * (1 - 13 / 20 * a + a ^ 2) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left (step_matrix_bound a ha0 ha1 s hs) (pow_nonneg hρ n)
    calc ∑ l ∈ Finset.range 8, ∑ c ∈ Finset.range (8 ^ n),
            (1 - a) ^ (runFrom s (8 * c + l) (n + 1)).2 *
              (1 - a * (pot (runFrom s (8 * c + l) (n + 1)).1 : ℚ) / 20)
        ≤ (8 * (1 - 13 / 20 * a + a ^ 2)) ^ n *
            (8 * (1 - 13 / 20 * a + a ^ 2) * (1 - a * (pot s : ℚ) / 20)) := le_trans h1 h2
      _ = (8 * (1 - 13 / 20 * a + a ^ 2)) ^ (n + 1) * (1 - a * (pot s : ℚ) / 20) := by
            rw [pow_succ]; ring

private lemma bernoulli_sub (x : ℚ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (k : Nat) :
    1 - (k : ℚ) * x ≤ (1 - x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have h1 : (1 - (k : ℚ) * x) * (1 - x) ≤ (1 - x) ^ k * (1 - x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (k : ℚ) * x * x := by positivity
    linarith

private lemma bernoulli_add (x : ℚ) (hx0 : 0 ≤ x) (k : Nat) :
    1 + (k : ℚ) * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have h1 : (1 + (k : ℚ) * x) * (1 + x) ≤ (1 + x) ^ k * (1 + x) :=
      mul_le_mul_of_nonneg_right ih (by linarith)
    have h2 : 0 ≤ (k : ℚ) * x * x := by positivity
    linarith

private lemma backward_dir (p q : Nat) (hq : 0 < q) (hlt : 20 * p < 13 * q) :
    ∃ (period start : Nat), 0 < period ∧
      ∀ n : Nat, start ≤ n →
        price n (p * n / q) ≤ 2 ^ (5 * n - n / period) := by
  have hqpos : (0 : ℚ) < (q : ℚ) := Nat.cast_pos.2 hq
  have hltQ : (20 : ℚ) * (p : ℚ) + 1 ≤ 13 * (q : ℚ) := by
    have h1 : 20 * p + 1 ≤ 13 * q := hlt
    exact_mod_cast h1
  let B : ℚ := 40 * (q : ℚ) * ((p : ℚ) + 1)
  have hBpos : (0 : ℚ) < B := by positivity
  let a : ℚ := 1 / (2 * B)
  have ha0 : 0 < a := by positivity
  have ha_half : a ≤ 1 / 2 := by
    have hB1 : 1 ≤ B := by
      have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
      have hp0 : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      dsimp only [B]
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  let z : ℚ := 1 - a
  let ρ : ℚ := 1 - 13 / 20 * a + a ^ 2
  have hz_ge : 1 / 2 ≤ z := by linarith
  have hz_pos : 0 < z := by linarith
  have hz_le1 : z ≤ 1 := by linarith
  have hρ_nonneg : 0 ≤ ρ := by dsimp only [ρ]; nlinarith
  have hρ_lt_z : ρ ^ q < z ^ p := by
    let c : ℚ := (26 * (q : ℚ) - 1) / (40 * (q : ℚ))
    have hc_pos : 0 < c := by
      have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
      dsimp only [c]
      apply div_pos <;> linarith
    have hca_le1 : c * a ≤ 1 := by
      have hc1 : c ≤ 1 := by
        dsimp only [c]
        rw [div_le_one (by positivity)]
        linarith
      nlinarith
    have ha_le_inv40q : a ≤ 1 / (40 * (q : ℚ)) := by
      dsimp only [a, B]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hp0 : (0 : ℚ) ≤ (p : ℚ) := Nat.cast_nonneg p
      nlinarith
    have hρ_le : ρ ≤ 1 - c * a := by
      have h1 : 13 / 20 - c = 1 / (40 * (q : ℚ)) := by
        dsimp only [c]
        field_simp
        ring
      have h2 : a ^ 2 ≤ (1 / (40 * (q : ℚ))) * a := by
        nlinarith
      dsimp only [ρ]
      nlinarith
    have hpow_le : ρ ^ q ≤ (1 - c * a) ^ q :=
      pow_le_pow_left₀ hρ_nonneg hρ_le q
    have hprod_le1 : (1 - c * a) ^ q * (1 + (q : ℚ) * (c * a)) ≤ 1 := by
      have hba := bernoulli_add (c * a) (by positivity) q
      have h1ca : 0 ≤ 1 - c * a := by linarith
      calc (1 - c * a) ^ q * (1 + (q : ℚ) * (c * a))
          ≤ (1 - c * a) ^ q * (1 + c * a) ^ q :=
              mul_le_mul_of_nonneg_left hba (pow_nonneg h1ca q)
        _ = ((1 - c * a) * (1 + c * a)) ^ q := (mul_pow _ _ q).symm
        _ = (1 - (c * a) ^ 2) ^ q := by ring
        _ ≤ 1 ^ q := by
              refine pow_le_pow_left₀ ?_ (by nlinarith) q
              have hca0 : 0 ≤ c * a := by positivity
              nlinarith
        _ = 1 := one_pow q
    have hzp_ge : 1 - (p : ℚ) * a ≤ z ^ p := bernoulli_sub a (le_of_lt ha0) (by linarith) p
    have hqc : (q : ℚ) * c = 13 / 20 * (q : ℚ) - 1 / 40 := by
      dsimp only [c]
      field_simp
      ring
    have hgap : (1 : ℚ) / 40 ≤ (q : ℚ) * c - (p : ℚ) := by
      linarith
    have hstrict : 1 < (1 - (p : ℚ) * a) * (1 + (q : ℚ) * (c * a)) := by
      have hqc_le : (q : ℚ) * c ≤ (q : ℚ) := by linarith
      have hpa_bound : (p : ℚ) * ((q : ℚ) * c) * a ≤ 1 / 80 := by
        have h1 : (p : ℚ) * ((q : ℚ) * c) ≤ (p : ℚ) * (q : ℚ) := by nlinarith
        have h2 : (p : ℚ) * (q : ℚ) * a ≤ 1 / 80 := by
          dsimp only [a, B]
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        nlinarith
      have hmul : (1 - (p : ℚ) * a) * (1 + (q : ℚ) * (c * a)) =
          1 + ((q : ℚ) * c - (p : ℚ) - (p : ℚ) * ((q : ℚ) * c) * a) * a := by ring
      rw [hmul]
      nlinarith
    have hden_pos : 0 < 1 + (q : ℚ) * (c * a) := by positivity
    have hlt1 : (1 - c * a) ^ q < 1 - (p : ℚ) * a := by
      nlinarith
    linarith
  let r : ℚ := ρ ^ q / z ^ p
  have hr0 : 0 ≤ r := div_nonneg (pow_nonneg hρ_nonneg q) (pow_nonneg (le_of_lt hz_pos) p)
  have hr1 : r < 1 := (div_lt_one (pow_pos hz_pos p)).2 hρ_lt_z
  have hexP : ∃ P : Nat, 0 < P ∧ r ^ P ≤ 1 / (2 : ℚ) ^ q := by
    by_cases hr_zero : r = 0
    · refine ⟨1, by omega, ?_⟩
      rw [hr_zero, pow_one]
      positivity
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_zero)
      let δ : ℚ := (1 - r) / r
      have hδpos : 0 < δ := by positivity
      obtain ⟨P0, hP0⟩ := exists_nat_gt ((2 : ℚ) ^ q / δ)
      let P := P0 + 1
      refine ⟨P, by omega, ?_⟩
      have hPδ : (2 : ℚ) ^ q ≤ (P : ℚ) * δ := by
        have h1 : (2 : ℚ) ^ q / δ < (P : ℚ) := by
          have : (P0 : ℚ) < (P : ℚ) := by dsimp only [P]; push_cast; linarith
          linarith
        have h2 := (div_lt_iff₀ hδpos).1 h1
        linarith
      have hbern : (2 : ℚ) ^ q ≤ (1 + δ) ^ P := by
        have := bernoulli_add δ (le_of_lt hδpos) P
        linarith
      have hr_mul : r * (1 + δ) = 1 := by
        dsimp only [δ]
        field_simp
        ring
      have hprod : r ^ P * (2 : ℚ) ^ q ≤ 1 := by
        calc r ^ P * (2 : ℚ) ^ q
            ≤ r ^ P * (1 + δ) ^ P := mul_le_mul_of_nonneg_left hbern (pow_nonneg hr0 P)
          _ = (r * (1 + δ)) ^ P := (mul_pow r (1 + δ) P).symm
          _ = 1 ^ P := by rw [hr_mul]
          _ = 1 := one_pow P
      rw [le_div_iff₀ (by positivity)]
      exact hprod
  obtain ⟨P, hPpos, hrP⟩ := hexP
  refine ⟨2 * P, 2 * P, by omega, fun n hn => ?_⟩
  let d := p * n / q
  have hprice_step : (price n d : ℚ) * z ^ d ≤ 2 * (2 : ℚ) ^ (5 * n) * ρ ^ n := by
    have hsum_price : (price n d : ℚ) * z ^ d ≤
        (2 : ℚ) ^ (2 * n) * ∑ w ∈ Finset.range (8 ^ n), z ^ (summary w n).2 := by
      unfold price
      rw [list_range_map_sum, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_le_sum fun w _ => ?_
      have hg_le : (summary w n).2 ≤ 2 * n := runFrom_snd_le 0 w n
      have hsub_le : (summary w n).2 - d ≤ 2 * n := le_trans (Nat.sub_le _ _) hg_le
      have h2pow : ((2 ^ (2 * n - ((summary w n).2 - d)) : Nat) : ℚ) =
          (2 : ℚ) ^ (2 * n) * (1 / 2 : ℚ) ^ ((summary w n).2 - d) := by
        have hsplit : (2 : ℚ) ^ (2 * n) =
            (2 : ℚ) ^ (2 * n - ((summary w n).2 - d)) * (2 : ℚ) ^ ((summary w n).2 - d) := by
          rw [← pow_add]
          congr 1
          omega
        rw [Nat.cast_pow, Nat.cast_ofNat, hsplit, one_div, inv_pow, mul_assoc,
          mul_inv_cancel₀ (by positivity), mul_one]
      rw [h2pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : (1 / 2 : ℚ) ^ ((summary w n).2 - d) ≤ z ^ ((summary w n).2 - d) :=
        pow_le_pow_left₀ (by positivity) hz_ge _
      have h2 : z ^ ((summary w n).2 - d) * z ^ d ≤ z ^ (summary w n).2 := by
        by_cases hgd : d ≤ (summary w n).2
        · rw [← pow_add, Nat.sub_add_cancel hgd]
        · have hsub0 : (summary w n).2 - d = 0 := Nat.sub_eq_zero_of_le (by omega)
          rw [hsub0, pow_zero, one_mul]
          exact pow_le_pow_of_le_one (le_of_lt hz_pos) hz_le1 (by omega)
      exact le_trans (mul_le_mul_of_nonneg_right h1 (pow_nonneg (le_of_lt hz_pos) d)) h2
    have hsum_z : ∑ w ∈ Finset.range (8 ^ n), z ^ (summary w n).2 ≤
        2 * (8 * ρ) ^ n := by
      have hwt := weighted_sum_bound a (le_of_lt ha0) ha_half n 0 (by omega)
      have hv_ge : ∀ w, (1 / 2 : ℚ) ≤ 1 - a * (pot (runFrom 0 w n).1 : ℚ) / 20 := by
        intro w
        have hpot_le : (pot (runFrom 0 w n).1 : ℚ) ≤ 7 := by
          have : pot (runFrom 0 w n).1 ≤ 7 := by
            unfold pot
            split <;> omega
          exact_mod_cast this
        nlinarith
      have hle_sum : ∑ w ∈ Finset.range (8 ^ n), z ^ (summary w n).2 ≤
          2 * ∑ w ∈ Finset.range (8 ^ n),
            (1 - a) ^ (runFrom 0 w n).2 * (1 - a * (pot (runFrom 0 w n).1 : ℚ) / 20) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun w _ => ?_
        have h1 := hv_ge w
        have h2 : 0 ≤ (1 - a) ^ (runFrom 0 w n).2 := pow_nonneg (le_of_lt hz_pos) _
        change (1 - a) ^ (runFrom 0 w n).2 ≤ _
        nlinarith
      have hpot0 : (1 - a * (pot 0 : ℚ) / 20) = 1 := by simp [pot]
      rw [hpot0, mul_one] at hwt
      have h3 : 2 * ∑ w ∈ Finset.range (8 ^ n),
            (1 - a) ^ (runFrom 0 w n).2 * (1 - a * (pot (runFrom 0 w n).1 : ℚ) / 20) ≤
          2 * (8 * ρ) ^ n := by
        dsimp only [ρ]
        linarith
      exact le_trans hle_sum h3
    have hpow5 : (2 : ℚ) ^ (2 * n) * (8 : ℚ) ^ n = (2 : ℚ) ^ (5 * n) := by
      have h8 : (8 : ℚ) = 2 ^ 3 := by norm_num
      rw [h8, ← pow_mul, ← pow_add]
      congr 1
      omega
    calc (price n d : ℚ) * z ^ d
        ≤ (2 : ℚ) ^ (2 * n) * (2 * (8 * ρ) ^ n) :=
            le_trans hsum_price (mul_le_mul_of_nonneg_left hsum_z (by positivity))
      _ = 2 * ((2 : ℚ) ^ (2 * n) * (8 : ℚ) ^ n) * ρ ^ n := by rw [mul_pow]; ring
      _ = 2 * (2 : ℚ) ^ (5 * n) * ρ ^ n := by rw [hpow5]
  have hqd_le : q * d ≤ p * n := Nat.mul_div_le (p * n) q
  have hpow_q : (price n d : ℚ) ^ q * z ^ (p * n) ≤ (2 : ℚ) ^ q * (2 : ℚ) ^ (5 * n * q) * (ρ ^ q) ^ n := by
    have hz_mono : z ^ (p * n) ≤ (z ^ d) ^ q := by
      rw [← pow_mul, mul_comm d q]
      exact pow_le_pow_of_le_one (le_of_lt hz_pos) hz_le1 hqd_le
    calc (price n d : ℚ) ^ q * z ^ (p * n)
        ≤ (price n d : ℚ) ^ q * (z ^ d) ^ q :=
            mul_le_mul_of_nonneg_left hz_mono (by positivity)
      _ = ((price n d : ℚ) * z ^ d) ^ q := (mul_pow _ _ q).symm
      _ ≤ (2 * (2 : ℚ) ^ (5 * n) * ρ ^ n) ^ q :=
            pow_le_pow_left₀ (by positivity) hprice_step q
      _ = (2 : ℚ) ^ q * (2 : ℚ) ^ (5 * n * q) * (ρ ^ q) ^ n := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n q]
  have hdiv_rn : (price n d : ℚ) ^ q ≤ (2 : ℚ) ^ q * (2 : ℚ) ^ (5 * n * q) * r ^ n := by
    have hzp_pos : 0 < (z ^ p) ^ n := pow_pos (pow_pos hz_pos p) n
    have hrn : (ρ ^ q) ^ n / (z ^ p) ^ n = r ^ n := by
      rw [← div_pow]
    have hzp_eq : (z ^ p) ^ n = z ^ (p * n) := (pow_mul z p n).symm
    rw [← hzp_eq] at hpow_q
    rw [← hrn, ← mul_div_assoc, le_div_iff₀ hzp_pos]
    exact hpow_q
  let k := n / P
  let m := n / (2 * P)
  have hm_add : m + 1 ≤ k := by
    have h1 : 2 * P * m ≤ n := Nat.mul_div_le n (2 * P)
    have h2 : 1 ≤ m := Nat.div_pos hn (by omega)
    have h3 : P * (m + 1) ≤ 2 * P * m := by nlinarith
    have h4 : P * (m + 1) ≤ n := le_trans h3 h1
    exact (Nat.le_div_iff_mul_le hPpos).2 (by rw [mul_comm]; exact h4)
  have hPk_le : P * k ≤ n := Nat.mul_div_le n P
  have hrn_le : r ^ n ≤ (1 / (2 : ℚ) ^ q) ^ (m + 1) := by
    calc r ^ n
        ≤ r ^ (P * k) := pow_le_pow_of_le_one hr0 (le_of_lt hr1) hPk_le
      _ = (r ^ P) ^ k := pow_mul r P k
      _ ≤ (1 / (2 : ℚ) ^ q) ^ k := pow_le_pow_left₀ (pow_nonneg hr0 P) hrP k
      _ ≤ (1 / (2 : ℚ) ^ q) ^ (m + 1) :=
            pow_le_pow_of_le_one (by positivity)
              (by rw [div_le_one (by positivity)]; exact_mod_cast Nat.one_le_two_pow) hm_add
  have hm_le_5n : m ≤ 5 * n := by
    have : m ≤ n := Nat.div_le_self n (2 * P)
    omega
  have hfinal_q : (price n d : ℚ) ^ q ≤ ((2 ^ (5 * n - m) : Nat) : ℚ) ^ q := by
    have hcancel : (2 : ℚ) ^ q * (2 : ℚ) ^ (5 * n * q) * (1 / (2 : ℚ) ^ q) ^ (m + 1) =
        ((2 ^ (5 * n - m) : Nat) : ℚ) ^ q := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← pow_mul]
      have hsplit : (2 : ℚ) ^ (5 * n * q) = (2 : ℚ) ^ ((5 * n - m) * q) * (2 : ℚ) ^ (m * q) := by
        rw [← pow_add]
        congr 1
        have : (5 * n - m) * q + m * q = ((5 * n - m) + m) * q := (Nat.add_mul _ _ _).symm
        rw [this, Nat.sub_add_cancel hm_le_5n]
      rw [hsplit, pow_succ, one_div, inv_pow, ← pow_mul, mul_comm q m]
      have hne1 : (2 : ℚ) ^ q ≠ 0 := by positivity
      have hne2 : (2 : ℚ) ^ (m * q) ≠ 0 := by positivity
      field_simp
    calc (price n d : ℚ) ^ q
        ≤ (2 : ℚ) ^ q * (2 : ℚ) ^ (5 * n * q) * r ^ n := hdiv_rn
      _ ≤ (2 : ℚ) ^ q * (2 : ℚ) ^ (5 * n * q) * (1 / (2 : ℚ) ^ q) ^ (m + 1) :=
            mul_le_mul_of_nonneg_left hrn_le (by positivity)
      _ = ((2 ^ (5 * n - m) : Nat) : ℚ) ^ q := hcancel
  have hnat_q : price n d ^ q ≤ (2 ^ (5 * n - m)) ^ q := by
    exact_mod_cast hfinal_q
  by_contra hgt
  push Not at hgt
  have hpow_lt : (2 ^ (5 * n - m)) ^ q < price n d ^ q :=
    Nat.pow_lt_pow_left hgt (Nat.ne_of_gt hq)
  omega

end PEqualNP.Outside.L_meta_25581_aux

theorem PEqualNP.Outside.L_meta_25581 :
  (let move := fun (mode letter : Nat) =>
      let near := letter.testBit 0
      let far := letter.testBit 1
      let hit := letter.testBit 2
      let aligned := ((mode == 1) && near && far) || ((mode == 2) && far) ||
        ((mode == 3) && near)
      let diagonal := (mode == 3) ||
        (!hit && (((mode == 1) && !near && !far) || (mode == 2)))
      (if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1,
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
            price n (p * n / q) ≤ 2 ^ (5 * n - n / period)) ↔ 20 * p < 13 * q)) := by
  intro move summary price p q hq
  constructor
  · intro hex
    by_contra hge
    exact PEqualNP.Outside.L_meta_25581_aux.forward_dir p q hq (by omega) hex
  · intro hlt
    exact PEqualNP.Outside.L_meta_25581_aux.backward_dir p q hq hlt
