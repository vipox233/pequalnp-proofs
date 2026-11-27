import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_284_aux

section Bitwise

private def rotBit (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepBit (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

private def constBit (k j : ℕ) : ℕ :=
  3 ^ (k + j) % 2 ^ k

private def rowStateAt (k rowKey rowName t : ℕ) : ℕ :=
  (List.range t).foldl (fun rowState rowIndex =>
    stepBit k (rowState ^^^ rotBit k 1 rowState ^^^ rotBit k (k - 1) rowState) ^^^
      rotBit k (2 * rowIndex) rowKey ^^^ constBit k (rowIndex + 1)) (rotBit k 1 rowKey ^^^ rowName)

private def colStateAt (k r colKey colName t : ℕ) : ℕ :=
  (List.range t).foldl (fun colState colIndex =>
    stepBit k (colState ^^^ rotBit k 2 colState ^^^ rotBit k (k - 2) colState) ^^^
      rotBit k (3 * (colIndex + 1) + 1) colKey ^^^ constBit k (r + (colIndex + 1)))
    (rotBit k 3 colKey ^^^ colName)

private theorem rowStateAt_succ (k rowKey rowName t : ℕ) :
    rowStateAt k rowKey rowName (t + 1) =
      stepBit k (rowStateAt k rowKey rowName t ^^^ rotBit k 1 (rowStateAt k rowKey rowName t) ^^^
        rotBit k (k - 1) (rowStateAt k rowKey rowName t)) ^^^
      rotBit k (2 * t) rowKey ^^^ constBit k (t + 1) := by
  dsimp only [rowStateAt]
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem colStateAt_succ (k r colKey colName t : ℕ) :
    colStateAt k r colKey colName (t + 1) =
      stepBit k (colStateAt k r colKey colName t ^^^ rotBit k 2 (colStateAt k r colKey colName t) ^^^
        rotBit k (k - 2) (colStateAt k r colKey colName t)) ^^^
      rotBit k (3 * (t + 1) + 1) colKey ^^^ constBit k (r + (t + 1)) := by
  dsimp only [colStateAt]
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem testBit_eq_div_mod (x i : ℕ) :
    x.testBit i = ((x / 2 ^ i) % 2 == 1) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hm : x / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by decide)
  generalize x / 2 ^ i % 2 = r at hm
  interval_cases r <;> rfl

private theorem testBit_lt_two_pow' {x k i : ℕ} (hx : x < 2 ^ k) (hi : k ≤ i) :
    x.testBit i = false := by
  rw [testBit_eq_div_mod]
  have h2 : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
  have hdiv : x / 2 ^ i = 0 := Nat.div_eq_of_lt (lt_of_lt_of_le hx h2)
  simp [hdiv]

private theorem eq_of_lt_two_pow_testBit {k x y : ℕ} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ i, i < k → x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact h i hi
  · have hge : k ≤ i := Nat.le_of_not_lt hi
    rw [testBit_lt_two_pow' hx hge, testBit_lt_two_pow' hy hge]

private theorem testBit_rotBit {k : ℕ} (hk : 0 < k) (s w : ℕ) (hw : w < 2 ^ k)
    {i : ℕ} (hi : i < k) :
    (rotBit k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  dsimp only [rotBit]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsk : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ i
  · have hge_k : k ≤ (k - s % k) + i := by omega
    have hlow : w.testBit ((k - s % k) + i) = false := testBit_lt_two_pow' hw hge_k
    have hidx : (i + k - s % k) % k = i - s % k := by
      have heq : i + k - s % k = (i - s % k) + k := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hidx, decide_eq_true hle, hlow]
    simp
  · have hlt : i < s % k := Nat.lt_of_not_le hle
    have hidx : (i + k - s % k) % k = (k - s % k) + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hidx, decide_eq_false hle]
    simp

private theorem rotBit_lt (k s w : ℕ) : rotBit k s w < 2 ^ k := by
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

private theorem constBit_lt (k j : ℕ) : constBit k j < 2 ^ k := by
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

private theorem bool_toNat_testBit_zero (b : Bool) : b.toNat.testBit 0 = b := by
  cases b <;> decide

private theorem stepBit_fold_props (k word m : ℕ) (hm : m ≤ k) :
    let val := (List.range m).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
    val < 2 ^ m ∧
    ∀ i < m, val.testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  induction m with
  | zero =>
    intro val
    simp only [List.range_zero, List.foldl_nil, val]
    exact ⟨Nat.pow_pos (by decide), fun _ hm => absurd hm (Nat.not_lt_zero _)⟩
  | @succ m ih =>
    have hm' : m ≤ k := Nat.le_of_succ_le hm
    obtain ⟨ih_lt, ih_bit⟩ := ih hm'
    set prev := (List.range m).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
    set b := xor (word.testBit m) (!(word.testBit ((m + 1) % k)) && word.testBit ((m + 2) % k))
    have hstep_eq : (List.range (m + 1)).foldl (fun acc i =>
        acc ||| ((xor (word.testBit i)
          (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0 =
        prev ||| (b.toNat <<< m) := by
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [hstep_eq]
    have hb_lt : b.toNat <<< m < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq]
      cases b <;> simp [Nat.pow_succ]
    have hprev_lt : prev < 2 ^ (m + 1) := lt_of_lt_of_le ih_lt (Nat.pow_le_pow_right (by decide) (by omega))
    refine ⟨Nat.or_lt_two_pow hprev_lt hb_lt, ?_⟩
    intro i hi
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases him : i = m
    · subst him
      have hp : prev.testBit i = false := testBit_lt_two_pow' ih_lt le_rfl
      rw [hp, decide_eq_true le_rfl, Nat.sub_self, Bool.true_and, Bool.false_or,
        bool_toNat_testBit_zero]
    · have him_lt : i < m := by omega
      have hnot : ¬ m ≤ i := by omega
      rw [ih_bit i him_lt, decide_eq_false hnot]
      simp

private theorem stepBit_lt (k word : ℕ) : stepBit k word < 2 ^ k :=
  (stepBit_fold_props k word k le_rfl).1

private theorem testBit_stepBit {k : ℕ} (word : ℕ) {i : ℕ} (hi : i < k) :
    (stepBit k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) :=
  (stepBit_fold_props k word k le_rfl).2 i hi

private theorem sum_pow2_range_eq (n : ℕ) :
    (∑ j ∈ Finset.range n, 2 ^ j) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | @succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

private theorem sum_pow2_range_lt {k : ℕ} (f : Fin k → Bool) :
    (∑ j : Fin k, (f j).toNat * 2 ^ j.val) < 2 ^ k := by
  have hsum : (∑ j : Fin k, (f j).toNat * 2 ^ j.val) ≤ ∑ j : Fin k, 2 ^ j.val := by
    apply Finset.sum_le_sum
    intro j _
    cases f j <;> simp
  have hfin : (∑ j : Fin k, 2 ^ j.val) = ∑ j ∈ Finset.range k, 2 ^ j :=
    Fin.sum_univ_eq_sum_range (fun j => 2 ^ j) k
  have hpow := sum_pow2_range_eq k
  rw [hfin] at hsum
  omega

private theorem testBit_sum_fin {k : ℕ} (f : Fin k → Bool) {i : ℕ} (hi : i < k) :
    (∑ j : Fin k, (f j).toNat * 2 ^ j.val).testBit i = f ⟨i, hi⟩ := by
  have haux : ∀ (n : ℕ) (_hn : n ≤ k) (g : ℕ → Bool),
      let S := ∑ j ∈ Finset.range n, (g j).toNat * 2 ^ j
      S < 2 ^ n ∧ ∀ m < n, S.testBit m = g m := by
    intro n _ g
    induction n with
    | zero =>
      intro S
      simp only [Finset.range_zero, Finset.sum_empty, S]
      exact ⟨Nat.pow_pos (by decide), fun _ hm => absurd hm (Nat.not_lt_zero _)⟩
    | @succ n ih =>
      obtain ⟨ih_lt, ih_bit⟩ := ih (by omega)
      set prev := ∑ j ∈ Finset.range n, (g j).toNat * 2 ^ j
      have heq : ∑ j ∈ Finset.range (n + 1), (g j).toNat * 2 ^ j = prev + (g n).toNat * 2 ^ n :=
        Finset.sum_range_succ _ _
      rw [heq]
      have hlt' : prev + (g n).toNat * 2 ^ n < 2 ^ (n + 1) := by
        rw [pow_succ]
        cases g n <;> simp <;> omega
      refine ⟨hlt', ?_⟩
      intro m hm
      rw [testBit_eq_div_mod]
      by_cases hmn : m = n
      · subst hmn
        have hdiv0 : prev / 2 ^ m = 0 := Nat.div_eq_of_lt ih_lt
        have hdiv : (prev + (g m).toNat * 2 ^ m) / 2 ^ m = (g m).toNat := by
          rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), hdiv0, Nat.zero_add]
        rw [hdiv]
        cases g m <;> decide
      · have hmlt : m < n := by omega
        have hnk : 2 ^ n = 2 ^ m * 2 * 2 ^ (n - m - 1) := by
          have h1 : n = m + 1 + (n - m - 1) := by omega
          conv_lhs => rw [h1, pow_add, pow_add, pow_one]
        have hdiv : (prev + (g n).toNat * 2 ^ n) / 2 ^ m =
            prev / 2 ^ m + ((g n).toNat * 2 ^ (n - m - 1)) * 2 := by
          have hrw : (g n).toNat * 2 ^ n = ((g n).toNat * 2 ^ (n - m - 1) * 2) * 2 ^ m := by
            rw [hnk]; ring
          rw [hrw, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide))]
        rw [hdiv, Nat.add_mul_mod_self_right, ← testBit_eq_div_mod]
        exact ih_bit m hmlt
  let g : ℕ → Bool := fun j => if h : j < k then f ⟨j, h⟩ else false
  have hsum_eq : (∑ j : Fin k, (f j).toNat * 2 ^ j.val) =
      ∑ j ∈ Finset.range k, (g j).toNat * 2 ^ j := by
    rw [show (∑ j : Fin k, (f j).toNat * 2 ^ j.val) =
        ∑ j : Fin k, (g j.val).toNat * 2 ^ j.val by
      apply Finset.sum_congr rfl
      intro j _
      simp [g, j.isLt]]
    exact Fin.sum_univ_eq_sum_range (fun j => (g j).toNat * 2 ^ j) k
  rw [hsum_eq]
  have res := (haux k le_rfl g).2 i hi
  simpa [g, hi] using res

private theorem rowStateAt_lt {k : ℕ} (hk : 0 < k) (rowKey rowName : ℕ)
    (hname : rowName < 2 ^ k) (t : ℕ) :
    rowStateAt k rowKey rowName t < 2 ^ k := by
  induction t with
  | zero =>
    dsimp only [rowStateAt, List.range_zero, List.foldl_nil]
    exact Nat.xor_lt_two_pow (rotBit_lt k 1 rowKey) hname
  | @succ t _ =>
    rw [rowStateAt_succ]
    have _ := hk
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBit_lt _ _) (rotBit_lt _ _ _)) (constBit_lt _ _)

private theorem colStateAt_lt {k : ℕ} (hk : 0 < k) (r colKey colName : ℕ)
    (hname : colName < 2 ^ k) (t : ℕ) :
    colStateAt k r colKey colName t < 2 ^ k := by
  induction t with
  | zero =>
    dsimp only [colStateAt, List.range_zero, List.foldl_nil]
    exact Nat.xor_lt_two_pow (rotBit_lt k 3 colKey) hname
  | @succ t _ =>
    rw [colStateAt_succ]
    have _ := hk
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepBit_lt _ _) (rotBit_lt _ _ _)) (constBit_lt _ _)

private def nextIdx {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

private def prevIdx {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩

private theorem nextIdx_prevIdx {k : ℕ} (hk : 0 < k) (i : Fin k) :
    nextIdx hk (prevIdx hk i) = i := by
  apply Fin.ext
  dsimp only [nextIdx, prevIdx]
  by_cases hk1 : k = 1
  · subst hk1; have := i.isLt; omega
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hi : i.val < k := i.isLt
    by_cases hi0 : i.val = 0
    · have hlt : k - 1 < k := by omega
      rw [hi0, Nat.zero_add, Nat.mod_eq_of_lt hlt, show k - 1 + 1 = k by omega, Nat.mod_self]
    · have hlt : i.val - 1 < k := by omega
      have heq : i.val + k - 1 = (i.val - 1) + k := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt,
        show i.val - 1 + 1 = i.val by omega, Nat.mod_eq_of_lt hi]

private theorem prevIdx_nextIdx {k : ℕ} (hk : 0 < k) (i : Fin k) :
    prevIdx hk (nextIdx hk i) = i := by
  apply Fin.ext
  dsimp only [nextIdx, prevIdx]
  by_cases hk1 : k = 1
  · subst hk1; have := i.isLt; omega
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hi : i.val < k := i.isLt
    by_cases him : i.val + 1 = k
    · rw [him, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hlt : i.val + 1 < k := by omega
      rw [Nat.mod_eq_of_lt hlt, show i.val + 1 + k - 1 = i.val + k by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private def shiftBack {k : ℕ} (hk : 0 < k) (i : Fin k) : ℕ → Fin k
  | 0 => i
  | d + 1 => prevIdx hk (shiftBack hk i d)

private theorem shiftBack_mod {k : ℕ} (hk : 0 < k) (i : Fin k) (d : ℕ) :
    (shiftBack hk i d).val = (i.val + k - d % k) % k := by
  by_cases hk1 : k = 1
  · subst hk1
    have hlt := (shiftBack hk i d).isLt
    omega
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    induction d with
    | zero =>
      simp only [shiftBack, Nat.zero_mod, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    | @succ d ih =>
      dsimp only [shiftBack, prevIdx]
      rw [ih, h1]
      have hdm : d % k < k := Nat.mod_lt d hk
      have hhi : (i.val + k - d % k) % k < k := Nat.mod_lt _ hk
      have hsum : (i.val + k - d % k) % k + k - 1 = (i.val + k - d % k) % k + (k - 1) := by omega
      rw [hsum, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hsum2 : (i.val + k - d % k) + (k - 1) = (i.val + 2 * k - (d % k + 1)) := by omega
      rw [hsum2]
      by_cases hwrap : d % k + 1 < k
      · have hd1 : (d + 1) % k = d % k + 1 := by
          rw [Nat.add_mod, h1, Nat.mod_eq_of_lt hwrap]
        rw [hd1]
        have heq : i.val + 2 * k - (d % k + 1) = (i.val + k - (d % k + 1)) + k := by omega
        rw [heq, Nat.add_mod_right]
      · have hdeq : d % k + 1 = k := by omega
        have hd1 : (d + 1) % k = 0 := by
          rw [Nat.add_mod, h1, hdeq, Nat.mod_self]
        rw [hd1, Nat.sub_zero, hdeq]
        have heq : i.val + 2 * k - k = i.val + k := by omega
        rw [heq]

private theorem testBit_rotBit_shiftBack {k : ℕ} (hk : 0 < k) (s w : ℕ) (hw : w < 2 ^ k)
    (i : Fin k) :
    (rotBit k s w).testBit i.val = w.testBit (shiftBack hk i s).val := by
  rw [testBit_rotBit hk s w hw i.isLt, shiftBack_mod hk i s]

private theorem shiftBack_mod_k {k : ℕ} (hk : 0 < k) (i : Fin k) (s : ℕ) :
    shiftBack hk i (s % k) = shiftBack hk i s := by
  apply Fin.ext
  rw [shiftBack_mod hk i (s % k), shiftBack_mod hk i s, Nat.mod_mod]

private theorem nextIdx_mod {k : ℕ} (hk : 0 < k) (i : Fin k) :
    (nextIdx hk i).val = (i.val + 1) % k := rfl

private theorem nextIdx_nextIdx_mod {k : ℕ} (hk : 0 < k) (i : Fin k) :
    (nextIdx hk (nextIdx hk i)).val = (i.val + 2) % k := by
  dsimp only [nextIdx]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem rotBit_km1_testBit {k : ℕ} (hk : 0 < k) (w : ℕ) (hw : w < 2 ^ k) (i : Fin k) :
    (rotBit k (k - 1) w).testBit i.val = w.testBit (nextIdx hk i).val := by
  rw [testBit_rotBit hk (k - 1) w hw i.isLt, nextIdx_mod]
  congr 1
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have hmod : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    have heq : i.val + k - (k - 1) = i.val + 1 := by omega
    rw [heq]

private theorem rotBit_km2_testBit {k : ℕ} (hk : 0 < k) (w : ℕ) (hw : w < 2 ^ k) (i : Fin k) :
    (rotBit k (k - 2) w).testBit i.val = w.testBit (nextIdx hk (nextIdx hk i)).val := by
  rw [testBit_rotBit hk (k - 2) w hw i.isLt, nextIdx_nextIdx_mod]
  congr 1
  by_cases hk1 : k = 1
  · subst hk1; simp
  · by_cases hk2 : k = 2
    · subst hk2; simp
    · have hmod : (k - 2) % k = k - 2 := Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      have heq : i.val + k - (k - 2) = i.val + 2 := by omega
      rw [heq]

end Bitwise

section CycleDP

private abbrev W1 (r : ℕ) : ℕ := 13 * r + 2
private abbrev In5 : Type := Fin 5 → Bool

private structure State (r : ℕ) where
  key : Fin (3 * r + 3) → Bool
  rsPrev : Fin r → Bool
  rsCurr : Fin r → Bool
  l1P1 : Fin r → Bool
  l1P2 : Fin r → Bool
  csM2 : Fin r → Bool
  csM1 : Fin r → Bool
  cs0 : Fin r → Bool
  csP1 : Fin r → Bool
  l2P1 : Fin r → Bool
  l2P2 : Fin r → Bool
  deriving DecidableEq

private def equivAddFun (a b : ℕ) :
    ((Fin a → Bool) × (Fin b → Bool)) ≃ (Fin (a + b) → Bool) :=
  { toFun := fun ⟨f, g⟩ idx =>
      if h : idx.val < a then f ⟨idx.val, h⟩ else g ⟨idx.val - a, by omega⟩
    invFun := fun h =>
      (fun i => h ⟨i.val, by omega⟩, fun j => h ⟨a + j.val, by omega⟩)
    left_inv := fun ⟨f, g⟩ => by
      ext i
      · simp [i.isLt]
      · have hlt : ¬ (a + i.val < a) := by omega
        simp [hlt]
    right_inv := fun h => by
      funext idx
      by_cases hlt : idx.val < a
      · simp [hlt]
      · simp [hlt, show a + (idx.val - a) = idx.val by omega] }

private def equivStateVec (r : ℕ) : State r ≃ (Fin (W1 r + 1) → Bool) :=
  let eTuple : State r ≃
      (Fin (3 * r + 3) → Bool) ×
      ((Fin r → Bool) × ((Fin r → Bool) × ((Fin r → Bool) × ((Fin r → Bool) ×
      ((Fin r → Bool) × ((Fin r → Bool) × ((Fin r → Bool) × ((Fin r → Bool) ×
      ((Fin r → Bool) × (Fin r → Bool)))))))))) :=
    { toFun := fun s =>
        (s.key, (s.rsPrev, (s.rsCurr, (s.l1P1, (s.l1P2,
          (s.csM2, (s.csM1, (s.cs0, (s.csP1, (s.l2P1, s.l2P2))))))))))
      invFun := fun p =>
        ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1,
          p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1,
          p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩
      left_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _⟩ => rfl }
  let e10 := equivAddFun r r
  let e9 := (Equiv.refl (Fin r → Bool)).prodCongr e10 |>.trans (equivAddFun r (r + r))
  let e8 := (Equiv.refl (Fin r → Bool)).prodCongr e9 |>.trans (equivAddFun r (r + (r + r)))
  let e7 := (Equiv.refl (Fin r → Bool)).prodCongr e8 |>.trans (equivAddFun r (r + (r + (r + r))))
  let e6 := (Equiv.refl (Fin r → Bool)).prodCongr e7 |>.trans (equivAddFun r (r + (r + (r + (r + r)))))
  let e5 := (Equiv.refl (Fin r → Bool)).prodCongr e6 |>.trans (equivAddFun r (r + (r + (r + (r + (r + r))))))
  let e4 := (Equiv.refl (Fin r → Bool)).prodCongr e5 |>.trans (equivAddFun r (r + (r + (r + (r + (r + (r + r)))))))
  let e3 := (Equiv.refl (Fin r → Bool)).prodCongr e4 |>.trans (equivAddFun r (r + (r + (r + (r + (r + (r + (r + r))))))))
  let e2 := (Equiv.refl (Fin r → Bool)).prodCongr e3 |>.trans (equivAddFun r (r + (r + (r + (r + (r + (r + (r + (r + r)))))))))
  let e1 := (Equiv.refl (Fin (3 * r + 3) → Bool)).prodCongr e2 |>.trans
    (equivAddFun (3 * r + 3) (r + (r + (r + (r + (r + (r + (r + (r + (r + r))))))))))
  let eCast : (Fin (3 * r + 3 + (r + (r + (r + (r + (r + (r + (r + (r + (r + r)))))))))) → Bool) ≃
      (Fin (W1 r + 1) → Bool) :=
    Equiv.piCongrLeft (fun _ => Bool) (Fin.castOrderIso (by dsimp only [W1]; omega)).toEquiv
  eTuple.trans (e1.trans eCast)

private theorem state_ext {r : ℕ} {a b : State r}
    (h1 : a.key = b.key) (h2 : a.rsPrev = b.rsPrev) (h3 : a.rsCurr = b.rsCurr)
    (h4 : a.l1P1 = b.l1P1) (h5 : a.l1P2 = b.l1P2) (h6 : a.csM2 = b.csM2)
    (h7 : a.csM1 = b.csM1) (h8 : a.cs0 = b.cs0) (h9 : a.csP1 = b.csP1)
    (h10 : a.l2P1 = b.l2P1) (h11 : a.l2P2 = b.l2P2) : a = b := by
  cases a; cases b; simp only [State.mk.injEq]; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

private instance (r : ℕ) : Fintype (State r) := Fintype.ofEquiv _ (equivStateVec r).symm

private theorem card_State (r : ℕ) : Fintype.card (State r) = 2 ^ (W1 r + 1) := by
  rw [Fintype.card_congr (equivStateVec r), Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

private def getKeyRot (k r : ℕ) (keyi : Bool) (a : State r) (shift : ℕ) : Bool :=
  let sk := shift % k
  if sk = 0 then keyi
  else if h : sk - 1 < 3 * r + 3 then a.key ⟨sk - 1, h⟩
  else false

private def rsVal {k r : ℕ} (i : Fin k) (in5 : In5) (a b : State r) : ℕ → Bool
  | 0 => xor (getKeyRot k r (in5 2) a 1) (in5 0)
  | t + 1 =>
    if ht : t < r then
      let tf : Fin r := ⟨t, ht⟩
      xor (xor (xor (a.l1P1 tf) (!(b.l1P1 tf) && b.l1P2 tf))
        (getKeyRot k r (in5 2) a (2 * t))) ((constBit k (t + 1)).testBit i.val)
    else false

private def csVal {k r : ℕ} (i : Fin k) (in5 : In5) (a b : State r) : ℕ → Bool
  | 0 => xor (getKeyRot k r (in5 2) a 3) (in5 1)
  | t + 1 =>
    if ht : t < r then
      let tf : Fin r := ⟨t, ht⟩
      xor (xor (xor (a.l2P1 tf) (!(b.l2P1 tf) && b.l2P2 tf))
        (getKeyRot k r (in5 2) a (3 * (t + 1) + 1))) ((constBit k (r + (t + 1))).testBit i.val)
    else false

private def LeafOK {k r : ℕ} (i : Fin k) (in5 : In5) (a b : State r) : Bool :=
  (b.key ⟨0, by omega⟩ == in5 2) &&
  (decide (∀ d : Fin (3 * r + 2), b.key ⟨d.val + 1, by omega⟩ = a.key ⟨d.val, by omega⟩)) &&
  (decide (∀ t : Fin r,
    a.rsCurr t = rsVal i in5 a b t.val ∧
    b.rsPrev t = rsVal i in5 a b t.val ∧
    a.l1P1 t = xor (xor (rsVal i in5 a b t.val) (a.rsPrev t)) (b.rsCurr t) ∧
    b.l1P1 t = a.l1P2 t)) &&
  (in5 3 == rsVal i in5 a b r) &&
  (decide (∀ t : Fin r,
    a.cs0 t = csVal i in5 a b t.val ∧
    b.csM1 t = csVal i in5 a b t.val ∧
    b.csM2 t = a.csM1 t ∧
    a.csP1 t = b.cs0 t ∧
    a.l2P1 t = xor (xor (csVal i in5 a b t.val) (a.csM2 t)) (b.csP1 t) ∧
    b.l2P1 t = a.l2P2 t)) &&
  (in5 4 == csVal i in5 a b r)

private def rsFreeVal {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) : ℕ → Bool
  | 0 => xor (getKeyRot k r (in5 2) free 1) (in5 0)
  | t + 1 =>
    if ht : t < r then
      let tf : Fin r := ⟨t, ht⟩
      let cur := rsFreeVal i in5 free t
      let l1p1 := xor (xor cur (free.rsPrev tf)) (free.rsCurr tf)
      xor (xor (xor l1p1 (!(free.l1P1 tf) && free.l1P2 tf))
        (getKeyRot k r (in5 2) free (2 * t))) ((constBit k (t + 1)).testBit i.val)
    else false

private def csFreeVal {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) : ℕ → Bool
  | 0 => xor (getKeyRot k r (in5 2) free 3) (in5 1)
  | t + 1 =>
    if ht : t < r then
      let tf : Fin r := ⟨t, ht⟩
      let cur := csFreeVal i in5 free t
      let l2p1 := xor (xor cur (free.csM2 tf)) (free.csP1 tf)
      xor (xor (xor l2p1 (!(free.l2P1 tf) && free.l2P2 tf))
        (getKeyRot k r (in5 2) free (3 * (t + 1) + 1))) ((constBit k (r + (t + 1))).testBit i.val)
    else false

private def mkA {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) : State r :=
  { key := free.key
    rsPrev := free.rsPrev
    rsCurr := fun t => rsFreeVal i in5 free t.val
    l1P1 := fun t => xor (xor (rsFreeVal i in5 free t.val) (free.rsPrev t)) (free.rsCurr t)
    l1P2 := free.l1P1
    csM2 := free.csM2
    csM1 := free.csM1
    cs0 := fun t => csFreeVal i in5 free t.val
    csP1 := free.cs0
    l2P1 := fun t => xor (xor (csFreeVal i in5 free t.val) (free.csM2 t)) (free.csP1 t)
    l2P2 := free.l2P1 }

private def mkB {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) : State r :=
  { key := fun d => if hz : d.val = 0 then in5 2 else free.key ⟨d.val - 1, by omega⟩
    rsPrev := fun t => rsFreeVal i in5 free t.val
    rsCurr := free.rsCurr
    l1P1 := free.l1P1
    l1P2 := free.l1P2
    csM2 := free.csM1
    csM1 := fun t => csFreeVal i in5 free t.val
    cs0 := free.cs0
    csP1 := free.csP1
    l2P1 := free.l2P1
    l2P2 := free.l2P2 }

private def mkPair {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) :
    Option (State r × State r) :=
  if (in5 3 == rsFreeVal i in5 free r) && (in5 4 == csFreeVal i in5 free r) then
    some (mkA i in5 free, mkB i in5 free)
  else none

private theorem getKeyRot_mkA {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) (s : ℕ) :
    getKeyRot k r (in5 2) (mkA i in5 free) s = getKeyRot k r (in5 2) free s := rfl

private theorem rsVal_mkPair {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) (t : ℕ) :
    rsVal i in5 (mkA i in5 free) (mkB i in5 free) t = rsFreeVal i in5 free t := by
  induction t with
  | zero => rfl
  | @succ t _ =>
    dsimp only [rsVal, rsFreeVal]
    by_cases ht : t < r
    · simp only [ht, ↓reduceDIte]
      rfl
    · simp [ht]

private theorem csVal_mkPair {k r : ℕ} (i : Fin k) (in5 : In5) (free : State r) (t : ℕ) :
    csVal i in5 (mkA i in5 free) (mkB i in5 free) t = csFreeVal i in5 free t := by
  induction t with
  | zero => rfl
  | @succ t _ =>
    dsimp only [csVal, csFreeVal]
    by_cases ht : t < r
    · simp only [ht, ↓reduceDIte]
      rfl
    · simp [ht]

private theorem LeafOK_of_mkPair {k r : ℕ} {i : Fin k} {in5 : In5} {free : State r}
    {a b : State r} (hm : mkPair i in5 free = some (a, b)) :
    LeafOK i in5 a b = true := by
  dsimp only [mkPair] at hm
  split at hm
  · rename_i hchk
    simp only [Option.some.injEq, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    dsimp only [LeafOK]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · rfl
    · intro d; dsimp only [mkB, mkA]; simp [Nat.add_eq_zero_iff]
    · intro t
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact rsVal_mkPair i in5 free t.val |>.symm
      · exact rsVal_mkPair i in5 free t.val |>.symm
      · rw [rsVal_mkPair]; rfl
      · rfl
    · rw [rsVal_mkPair]; exact hchk.1
    · intro t
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact csVal_mkPair i in5 free t.val |>.symm
      · exact csVal_mkPair i in5 free t.val |>.symm
      · rfl
      · rfl
      · rw [csVal_mkPair]; rfl
      · rfl
    · rw [csVal_mkPair]; exact hchk.2
  · cases hm

private def extractFree {r : ℕ} (a b : State r) : State r :=
  { key := a.key
    rsPrev := a.rsPrev
    rsCurr := b.rsCurr
    l1P1 := b.l1P1
    l1P2 := b.l1P2
    csM2 := a.csM2
    csM1 := a.csM1
    cs0 := b.cs0
    csP1 := b.csP1
    l2P1 := b.l2P1
    l2P2 := b.l2P2 }

private theorem exists_mkPair_of_LeafOK {k r : ℕ} {i : Fin k} {in5 : In5} {a b : State r}
    (hok : LeafOK i in5 a b = true) :
    ∃ free : State r, mkPair i in5 free = some (a, b) := by
  dsimp only [LeafOK] at hok
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨hb0, hkey_shift⟩, hrs⟩, hout1⟩, hcs⟩, hout2⟩
  let free := extractFree a b
  have hgk : ∀ s, getKeyRot k r (in5 2) free s = getKeyRot k r (in5 2) a s := fun s => rfl
  have hrs_eq : ∀ t, rsFreeVal i in5 free t = rsVal i in5 a b t := fun t => by
    induction t with
    | zero => rfl
    | @succ t ih =>
      dsimp only [rsFreeVal, rsVal]
      by_cases ht : t < r
      · simp only [ht, ↓reduceDIte]
        have hr : a.l1P1 ⟨t, ht⟩ =
            xor (xor (rsVal i in5 a b t) (a.rsPrev ⟨t, ht⟩)) (b.rsCurr ⟨t, ht⟩) :=
          (hrs ⟨t, ht⟩).2.2.1
        have hp1 : free.rsPrev ⟨t, ht⟩ = a.rsPrev ⟨t, ht⟩ := rfl
        have hp2 : free.rsCurr ⟨t, ht⟩ = b.rsCurr ⟨t, ht⟩ := rfl
        have hp3 : free.l1P1 ⟨t, ht⟩ = b.l1P1 ⟨t, ht⟩ := rfl
        have hp4 : free.l1P2 ⟨t, ht⟩ = b.l1P2 ⟨t, ht⟩ := rfl
        rw [ih, hp1, hp2, hp3, hp4, hgk, ← hr]
      · simp [ht]
  have hcs_eq : ∀ t, csFreeVal i in5 free t = csVal i in5 a b t := fun t => by
    induction t with
    | zero => rfl
    | @succ t ih =>
      dsimp only [csFreeVal, csVal]
      by_cases ht : t < r
      · simp only [ht, ↓reduceDIte]
        have hc : a.l2P1 ⟨t, ht⟩ =
            xor (xor (csVal i in5 a b t) (a.csM2 ⟨t, ht⟩)) (b.csP1 ⟨t, ht⟩) :=
          (hcs ⟨t, ht⟩).2.2.2.2.1
        have hp1 : free.csM2 ⟨t, ht⟩ = a.csM2 ⟨t, ht⟩ := rfl
        have hp2 : free.csP1 ⟨t, ht⟩ = b.csP1 ⟨t, ht⟩ := rfl
        have hp3 : free.l2P1 ⟨t, ht⟩ = b.l2P1 ⟨t, ht⟩ := rfl
        have hp4 : free.l2P2 ⟨t, ht⟩ = b.l2P2 ⟨t, ht⟩ := rfl
        rw [ih, hp1, hp2, hp3, hp4, hgk, ← hc]
      · simp [ht]
  refine ⟨free, ?_⟩
  dsimp only [mkPair]
  have hchk : ((in5 3 == rsFreeVal i in5 free r) && (in5 4 == csFreeVal i in5 free r)) = true := by
    rw [hrs_eq r, hcs_eq r, hout1, hout2]; simp
  rw [hchk]
  simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq]
  constructor
  · refine state_ext rfl rfl
      (funext fun t => (hrs_eq t.val).trans (hrs t).1.symm)
      (funext fun t => ?_)
      (funext fun t => (hrs t).2.2.2)
      rfl rfl
      (funext fun t => (hcs_eq t.val).trans (hcs t).1.symm)
      (funext fun t => (hcs t).2.2.2.1.symm)
      (funext fun t => ?_)
      (funext fun t => (hcs t).2.2.2.2.2)
    · change xor (xor (rsFreeVal i in5 free t.val) (free.rsPrev t)) (free.rsCurr t) = a.l1P1 t
      rw [hrs_eq t.val]
      exact (hrs t).2.2.1.symm
    · change xor (xor (csFreeVal i in5 free t.val) (free.csM2 t)) (free.csP1 t) = a.l2P1 t
      rw [hcs_eq t.val]
      exact (hcs t).2.2.2.2.1.symm
  · refine state_ext ?_ (funext fun t => (hrs_eq t.val).trans (hrs t).2.1.symm) rfl rfl rfl
      (funext fun t => (hcs t).2.2.1.symm) (funext fun t => (hcs_eq t.val).trans (hcs t).2.1.symm)
      rfl rfl rfl rfl
    funext d
    dsimp only [mkB, free, extractFree]
    by_cases hz : d.val = 0
    · have hd0 : d = ⟨0, by omega⟩ := Fin.ext hz
      rw [hd0, hb0]; simp
    · have hdm : d.val - 1 < 3 * r + 2 := by omega
      have hs := hkey_shift ⟨d.val - 1, hdm⟩
      have hde : (⟨(⟨d.val - 1, hdm⟩ : Fin (3 * r + 2)).val + 1, by omega⟩ : Fin (3 * r + 3)) = d :=
        Fin.ext (by dsimp; omega)
      rw [hde] at hs
      simp [hz, hs]

private theorem LeafOK_iff_exists_mkPair {k r : ℕ} {i : Fin k} {in5 : In5} {a b : State r} :
    LeafOK i in5 a b = true ↔ ∃ free : State r, mkPair i in5 free = some (a, b) :=
  ⟨exists_mkPair_of_LeafOK, fun ⟨_, hm⟩ => LeafOK_of_mkPair hm⟩

private def wordOf (k : ℕ) (v : (Fin 5 × Fin k) → Bool) (track : Fin 5) : ℕ :=
  ∑ j : Fin k, (v (track, j)).toNat * 2 ^ j.val

private theorem wordOf_lt {k : ℕ} (v : (Fin 5 × Fin k) → Bool) (track : Fin 5) :
    wordOf k v track < 2 ^ k :=
  sum_pow2_range_lt (fun j => v (track, j))

private theorem testBit_wordOf {k : ℕ} (v : (Fin 5 × Fin k) → Bool) (track : Fin 5)
    (i : Fin k) : (wordOf k v track).testBit i.val = v (track, i) := by
  have := testBit_sum_fin (fun j => v (track, j)) i.isLt
  simpa [wordOf] using this

private theorem shiftBack_succ_nextIdx {k : ℕ} (hk : 0 < k) (i : Fin k) (d : ℕ) :
    shiftBack hk (nextIdx hk i) (d + 1) = shiftBack hk i d := by
  apply Fin.ext
  rw [shiftBack_mod, shiftBack_mod, nextIdx_mod]
  by_cases hk1 : k = 1
  · subst hk1
    have h1 := (shiftBack hk i d).isLt
    omega
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hdm : d % k < k := Nat.mod_lt d hk
    by_cases hwrap : d % k + 1 < k
    · have hd1 : (d + 1) % k = d % k + 1 := by rw [Nat.add_mod, h1, Nat.mod_eq_of_lt hwrap]
      rw [hd1]
      have hi1 : (i.val + 1) % k + k - (d % k + 1) =
          if i.val + 1 < k then i.val + k - d % k else i.val + 1 - k + k - (d % k + 1) := by
        split <;> rename_i hi
        · rw [Nat.mod_eq_of_lt hi]; omega
        · have hik : i.val + 1 = k := by have := i.isLt; omega
          rw [hik, Nat.mod_self]; omega
      split at hi1
      · rw [hi1]
      · rw [hi1]
        have hik : i.val + 1 = k := by have := i.isLt; omega
        have heq1 : i.val + 1 - k + k - (d % k + 1) = k - 1 - d % k := by omega
        have heq2 : i.val + k - d % k = (k - 1 - d % k) + k := by omega
        rw [heq1, heq2, Nat.add_mod_right]
    · have hde : d % k + 1 = k := by omega
      have hd1 : (d + 1) % k = 0 := by rw [Nat.add_mod, h1, hde, Nat.mod_self]
      rw [hd1, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
      have hdm2 : d % k = k - 1 := by omega
      rw [hdm2]
      have heq : i.val + k - (k - 1) = i.val + 1 := by omega
      rw [heq]

private theorem cycle_implies_agrees {k r : ℕ} (hk : 0 < k) (v : (Fin 5 × Fin k) → Bool)
    (states : Fin k → State r)
    (hcyc : ∀ i : Fin k, LeafOK i (fun t => v (t, i)) (states i) (states (nextIdx hk i)) = true) :
    wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
    wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r := by
  have hkey_all : ∀ (d : ℕ) (hd : d < 3 * r + 3) (i : Fin k),
      (states i).key ⟨d, hd⟩ = v (2, shiftBack hk i (d + 1)) := by
    intro d
    induction d with
    | zero =>
      intro hd i
      have hi := hcyc (prevIdx hk i)
      dsimp only [LeafOK] at hi
      simp only [Bool.and_eq_true, beq_iff_eq] at hi
      have hb := hi.1.1.1.1.1
      rw [nextIdx_prevIdx] at hb
      have hsb : shiftBack hk i 1 = prevIdx hk i := rfl
      rw [hsb]
      exact hb
    | @succ d ih =>
      intro hd i
      have hdm : d < 3 * r + 2 := by omega
      have hi := hcyc (prevIdx hk i)
      dsimp only [LeafOK] at hi
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
      have hs := hi.1.1.1.1.2 ⟨d, hdm⟩
      rw [nextIdx_prevIdx] at hs
      rw [hs, ih (by omega) (prevIdx hk i)]
      congr 2
      have heq : shiftBack hk (prevIdx hk i) (d + 1) = shiftBack hk i (d + 2) := by
        calc shiftBack hk (prevIdx hk i) (d + 1)
            = shiftBack hk (nextIdx hk (prevIdx hk i)) (d + 2) := by
              rw [shiftBack_succ_nextIdx]
          _ = shiftBack hk i (d + 2) := by
              rw [nextIdx_prevIdx]
      exact heq
  have hgk_rot : ∀ (s : ℕ) (hs : s ≤ 3 * r + 3) (i : Fin k),
      getKeyRot k r (v (2, i)) (states i) s = (rotBit k s (wordOf k v 2)).testBit i.val := by
    intro s hs i
    rw [testBit_rotBit_shiftBack hk s _ (wordOf_lt v 2) i, testBit_wordOf]
    dsimp only [getKeyRot]
    by_cases hsz : s % k = 0
    · simp only [hsz, ↓reduceIte]
      rw [← shiftBack_mod_k hk i s, hsz]
      rfl
    · simp only [hsz, ↓reduceIte]
      have hsk_le : s % k ≤ s := Nat.mod_le s k
      have hlt : s % k - 1 < 3 * r + 3 := by omega
      simp only [hlt, ↓reduceDIte]
      rw [hkey_all (s % k - 1) hlt i, show s % k - 1 + 1 = s % k by omega, shiftBack_mod_k]
  have hrs_eq : ∀ (t : ℕ) (ht : t ≤ r) (i : Fin k),
      rsVal i (fun u => v (u, i)) (states i) (states (nextIdx hk i)) t =
        (rowStateAt k (wordOf k v 2) (wordOf k v 0) t).testBit i.val := by
    intro t
    induction t with
    | zero =>
      intro _ i
      dsimp only [rsVal, rowStateAt, List.range_zero, List.foldl_nil]
      rw [Nat.testBit_xor, hgk_rot 1 (by omega) i, testBit_wordOf]
    | @succ t ih =>
      intro ht i
      have htr : t < r := by omega
      have ih_all : ∀ j : Fin k,
          rsVal j (fun u => v (u, j)) (states j) (states (nextIdx hk j)) t =
            (rowStateAt k (wordOf k v 2) (wordOf k v 0) t).testBit j.val :=
        fun j => ih (by omega) j
      have hc := fun j : Fin k => by
        have hj := hcyc j
        dsimp only [LeafOK] at hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.1.1.1.2 ⟨t, htr⟩
      have hl1_at : ∀ j : Fin k, (states j).l1P1 ⟨t, htr⟩ =
          (rowStateAt k (wordOf k v 2) (wordOf k v 0) t ^^^
            rotBit k 1 (rowStateAt k (wordOf k v 2) (wordOf k v 0) t) ^^^
            rotBit k (k - 1) (rowStateAt k (wordOf k v 2) (wordOf k v 0) t)).testBit j.val := by
        intro j
        have hlt := rowStateAt_lt hk (wordOf k v 2) (wordOf k v 0) (wordOf_lt v 0) t
        have hprev : (states j).rsPrev ⟨t, htr⟩ =
            (rowStateAt k (wordOf k v 2) (wordOf k v 0) t).testBit (prevIdx hk j).val := by
          have h1 := (hc (prevIdx hk j)).2.1
          rw [ih_all (prevIdx hk j)] at h1
          rw [nextIdx_prevIdx] at h1
          exact h1
        have hcurr : (states (nextIdx hk j)).rsCurr ⟨t, htr⟩ =
            (rowStateAt k (wordOf k v 2) (wordOf k v 0) t).testBit (nextIdx hk j).val := by
          have h1 := (hc (nextIdx hk j)).1
          rw [ih_all (nextIdx hk j)] at h1
          exact h1
        rw [(hc j).2.2.1, ih_all j, hprev, hcurr]
        rw [Nat.testBit_xor, Nat.testBit_xor,
          testBit_rotBit_shiftBack hk 1 _ hlt j, rotBit_km1_testBit hk _ hlt j]
        rfl
      have hl1_n2 : (states (nextIdx hk i)).l1P2 ⟨t, htr⟩ =
          (rowStateAt k (wordOf k v 2) (wordOf k v 0) t ^^^
            rotBit k 1 (rowStateAt k (wordOf k v 2) (wordOf k v 0) t) ^^^
            rotBit k (k - 1) (rowStateAt k (wordOf k v 2) (wordOf k v 0) t)).testBit
            (nextIdx hk (nextIdx hk i)).val := by
        rw [← (hc (nextIdx hk i)).2.2.2]
        exact hl1_at (nextIdx hk (nextIdx hk i))
      rw [rowStateAt_succ]
      dsimp only [rsVal]
      simp only [htr, ↓reduceDIte]
      rw [Nat.testBit_xor, Nat.testBit_xor,
        testBit_stepBit _ i.isLt, hgk_rot (2 * t) (by omega) i,
        hl1_at i, hl1_at (nextIdx hk i), hl1_n2, nextIdx_mod, nextIdx_nextIdx_mod]
  have hcs_eq : ∀ (t : ℕ) (ht : t ≤ r) (i : Fin k),
      csVal i (fun u => v (u, i)) (states i) (states (nextIdx hk i)) t =
        (colStateAt k r (wordOf k v 2) (wordOf k v 1) t).testBit i.val := by
    intro t
    induction t with
    | zero =>
      intro _ i
      dsimp only [csVal, colStateAt, List.range_zero, List.foldl_nil]
      rw [Nat.testBit_xor, hgk_rot 3 (by omega) i, testBit_wordOf]
    | @succ t ih =>
      intro ht i
      have htr : t < r := by omega
      have ih_all : ∀ j : Fin k,
          csVal j (fun u => v (u, j)) (states j) (states (nextIdx hk j)) t =
            (colStateAt k r (wordOf k v 2) (wordOf k v 1) t).testBit j.val :=
        fun j => ih (by omega) j
      have hc := fun j : Fin k => by
        have hj := hcyc j
        dsimp only [LeafOK] at hj
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hj
        exact hj.1.2 ⟨t, htr⟩
      have hl2_at : ∀ j : Fin k, (states j).l2P1 ⟨t, htr⟩ =
          (colStateAt k r (wordOf k v 2) (wordOf k v 1) t ^^^
            rotBit k 2 (colStateAt k r (wordOf k v 2) (wordOf k v 1) t) ^^^
            rotBit k (k - 2) (colStateAt k r (wordOf k v 2) (wordOf k v 1) t)).testBit j.val := by
        intro j
        have hlt := colStateAt_lt hk r (wordOf k v 2) (wordOf k v 1) (wordOf_lt v 1) t
        have hm2 : (states j).csM2 ⟨t, htr⟩ =
            (colStateAt k r (wordOf k v 2) (wordOf k v 1) t).testBit
              (prevIdx hk (prevIdx hk j)).val := by
          have h1 := (hc (prevIdx hk j)).2.2.1
          rw [nextIdx_prevIdx] at h1
          have h2 := (hc (prevIdx hk (prevIdx hk j))).2.1
          rw [ih_all (prevIdx hk (prevIdx hk j))] at h2
          rw [nextIdx_prevIdx] at h2
          rw [h1, h2]
        have hp1 : (states (nextIdx hk j)).csP1 ⟨t, htr⟩ =
            (colStateAt k r (wordOf k v 2) (wordOf k v 1) t).testBit
              (nextIdx hk (nextIdx hk j)).val := by
          have h1 := (hc (nextIdx hk (nextIdx hk j))).1
          rw [ih_all (nextIdx hk (nextIdx hk j))] at h1
          rw [(hc (nextIdx hk j)).2.2.2.1, h1]
        rw [(hc j).2.2.2.2.1, ih_all j, hm2, hp1]
        rw [Nat.testBit_xor, Nat.testBit_xor,
          testBit_rotBit_shiftBack hk 2 _ hlt j, rotBit_km2_testBit hk _ hlt j]
        rfl
      have hl2_n2 : (states (nextIdx hk i)).l2P2 ⟨t, htr⟩ =
          (colStateAt k r (wordOf k v 2) (wordOf k v 1) t ^^^
            rotBit k 2 (colStateAt k r (wordOf k v 2) (wordOf k v 1) t) ^^^
            rotBit k (k - 2) (colStateAt k r (wordOf k v 2) (wordOf k v 1) t)).testBit
            (nextIdx hk (nextIdx hk i)).val := by
        rw [← (hc (nextIdx hk i)).2.2.2.2.2]
        exact hl2_at (nextIdx hk (nextIdx hk i))
      rw [colStateAt_succ]
      dsimp only [csVal]
      simp only [htr, ↓reduceDIte]
      rw [Nat.testBit_xor, Nat.testBit_xor,
        testBit_stepBit _ i.isLt, hgk_rot (3 * (t + 1) + 1) (by omega) i,
        hl2_at i, hl2_at (nextIdx hk i), hl2_n2, nextIdx_mod, nextIdx_nextIdx_mod]
  constructor
  · apply eq_of_lt_two_pow_testBit (wordOf_lt v 3) (rowStateAt_lt hk _ _ (wordOf_lt v 0) r)
    intro i hi
    have hlo := hcyc ⟨i, hi⟩
    dsimp only [LeafOK] at hlo
    simp only [Bool.and_eq_true, beq_iff_eq] at hlo
    have ho1 := hlo.1.1.2
    rw [← hrs_eq r le_rfl ⟨i, hi⟩, ← ho1, testBit_wordOf v 3 ⟨i, hi⟩]
  · apply eq_of_lt_two_pow_testBit (wordOf_lt v 4) (colStateAt_lt hk r _ _ (wordOf_lt v 1) r)
    intro i hi
    have hlo := hcyc ⟨i, hi⟩
    dsimp only [LeafOK] at hlo
    simp only [Bool.and_eq_true, beq_iff_eq] at hlo
    have ho2 := hlo.2
    rw [← hcs_eq r le_rfl ⟨i, hi⟩, ← ho2, testBit_wordOf v 4 ⟨i, hi⟩]

private theorem agrees_implies_cycle {k r : ℕ} (hk : 0 < k) (v : (Fin 5 × Fin k) → Bool)
    (hag : wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
      wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r) :
    ∃ states : Fin k → State r,
      ∀ i : Fin k, LeafOK i (fun t => v (t, i)) (states i) (states (nextIdx hk i)) = true := by
  let rseq := fun t => rowStateAt k (wordOf k v 2) (wordOf k v 0) t
  let l1 := fun t => rseq t ^^^ rotBit k 1 (rseq t) ^^^ rotBit k (k - 1) (rseq t)
  let cseq := fun t => colStateAt k r (wordOf k v 2) (wordOf k v 1) t
  let l2 := fun t => cseq t ^^^ rotBit k 2 (cseq t) ^^^ rotBit k (k - 2) (cseq t)
  let states : Fin k → State r := fun i =>
    { key := fun d => v (2, shiftBack hk i (d.val + 1))
      rsPrev := fun t => (rseq t.val).testBit (prevIdx hk i).val
      rsCurr := fun t => (rseq t.val).testBit i.val
      l1P1 := fun t => (l1 t.val).testBit i.val
      l1P2 := fun t => (l1 t.val).testBit (nextIdx hk i).val
      csM2 := fun t => (cseq t.val).testBit (prevIdx hk (prevIdx hk i)).val
      csM1 := fun t => (cseq t.val).testBit (prevIdx hk i).val
      cs0 := fun t => (cseq t.val).testBit i.val
      csP1 := fun t => (cseq t.val).testBit (nextIdx hk i).val
      l2P1 := fun t => (l2 t.val).testBit i.val
      l2P2 := fun t => (l2 t.val).testBit (nextIdx hk i).val }
  have hgk : ∀ (s : ℕ) (hs : s ≤ 3 * r + 3) (i : Fin k),
      getKeyRot k r (v (2, i)) (states i) s = (rotBit k s (wordOf k v 2)).testBit i.val := by
    intro s hs i
    rw [testBit_rotBit_shiftBack hk s _ (wordOf_lt v 2) i, testBit_wordOf]
    dsimp only [getKeyRot]
    by_cases hsz : s % k = 0
    · simp only [hsz, ↓reduceIte]
      rw [← shiftBack_mod_k hk i s, hsz]
      rfl
    · simp only [hsz, ↓reduceIte]
      have hsk_le : s % k ≤ s := Nat.mod_le s k
      have hlt : s % k - 1 < 3 * r + 3 := by omega
      simp only [hlt, ↓reduceDIte]
      dsimp only [states]
      rw [show s % k - 1 + 1 = s % k by omega, shiftBack_mod_k]
  have hrs_eq : ∀ (t : ℕ) (ht : t ≤ r) (i : Fin k),
      rsVal i (fun u => v (u, i)) (states i) (states (nextIdx hk i)) t = (rseq t).testBit i.val := by
    intro t _ i
    induction t with
    | zero =>
      dsimp only [rsVal, rseq, rowStateAt, List.range_zero, List.foldl_nil]
      rw [Nat.testBit_xor, hgk 1 (by omega) i, testBit_wordOf]
    | @succ t _ =>
      by_cases htr : t < r
      · conv_rhs =>
          dsimp only [rseq]
          rw [rowStateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_stepBit _ i.isLt]
        dsimp only [rsVal]
        simp only [htr, ↓reduceDIte]
        rw [hgk (2 * t) (by omega) i]
        dsimp only [states, l1, rseq]
        rw [nextIdx_mod, nextIdx_nextIdx_mod]
      · omega
  have hcs_eq : ∀ (t : ℕ) (ht : t ≤ r) (i : Fin k),
      csVal i (fun u => v (u, i)) (states i) (states (nextIdx hk i)) t = (cseq t).testBit i.val := by
    intro t _ i
    induction t with
    | zero =>
      dsimp only [csVal, cseq, colStateAt, List.range_zero, List.foldl_nil]
      rw [Nat.testBit_xor, hgk 3 (by omega) i, testBit_wordOf]
    | @succ t _ =>
      by_cases htr : t < r
      · conv_rhs =>
          dsimp only [cseq]
          rw [colStateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_stepBit _ i.isLt]
        dsimp only [csVal]
        simp only [htr, ↓reduceDIte]
        rw [hgk (3 * (t + 1) + 1) (by omega) i]
        dsimp only [states, l2, cseq]
        rw [nextIdx_mod, nextIdx_nextIdx_mod]
      · omega
  refine ⟨states, fun i => ?_⟩
  dsimp only [LeafOK]
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · dsimp only [states]
    have hsb : shiftBack hk (nextIdx hk i) 1 = i := by
      change prevIdx hk (nextIdx hk i) = i
      exact prevIdx_nextIdx hk i
    rw [hsb]
  · intro d
    dsimp only [states]
    rw [shiftBack_succ_nextIdx]
  · intro t
    have hlt := rowStateAt_lt hk (wordOf k v 2) (wordOf k v 0) (wordOf_lt v 0) t.val
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hrs_eq t.val (by omega) i]
    · rw [hrs_eq t.val (by omega) i]; dsimp only [states]; rw [prevIdx_nextIdx]
    · rw [hrs_eq t.val (by omega) i]
      dsimp only [states, l1, rseq]
      rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotBit_shiftBack hk 1 _ hlt i,
        rotBit_km1_testBit hk _ hlt i]
      rfl
    · rfl
  · rw [hrs_eq r le_rfl i, ← testBit_wordOf v 3 i, hag.1]
  · intro t
    have hlt := colStateAt_lt hk r (wordOf k v 2) (wordOf k v 1) (wordOf_lt v 1) t.val
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcs_eq t.val (by omega) i]
    · rw [hcs_eq t.val (by omega) i]; dsimp only [states]; rw [prevIdx_nextIdx]
    · dsimp only [states]; rw [prevIdx_nextIdx]
    · rfl
    · rw [hcs_eq t.val (by omega) i]
      dsimp only [states, l2, cseq]
      rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotBit_shiftBack hk 2 _ hlt i,
        rotBit_km2_testBit hk _ hlt i]
      rfl
    · rfl
  · rw [hcs_eq r le_rfl i, ← testBit_wordOf v 4 i, hag.2]

end CycleDP

section TreeCNF

open PEqualNP.ProofComplexity
open PEqualNP.Search

private def stepUP {α : Type} (F : Set (Clause α)) (S : Set (Literal α)) : Set (Literal α) :=
  S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l → negLit other ∈ S}

private theorem subset_stepUP {α : Type} (F : Set (Clause α)) (S : Set (Literal α)) :
    S ⊆ stepUP F S := fun _ h => Or.inl h

private theorem stepUP_mono {α : Type} {F : Set (Clause α)} {S T : Set (Literal α)}
    (h : S ⊆ T) : stepUP F S ⊆ stepUP F T := by
  rintro l (hl | ⟨C, hCF, hlC, hneg⟩)
  · exact Or.inl (h hl)
  · exact Or.inr ⟨C, hCF, hlC, fun o ho hne => h (hneg o ho hne)⟩

private theorem stepUP_iterate_mono {α : Type} (F : Set (Clause α)) (S : Set (Literal α))
    {a b : ℕ} (hab : a ≤ b) : (stepUP F)^[a] S ⊆ (stepUP F)^[b] S := by
  have heq : b = (b - a) + a := by omega
  rw [heq, Function.iterate_add_apply]
  clear heq hab
  induction (b - a) with
  | zero => exact Set.Subset.rfl
  | @succ d ih =>
    intro l hl
    rw [Function.iterate_succ_apply']
    exact subset_stepUP F _ (ih hl)

private theorem mem_stepUP_succ_of_clause {α : Type} {F : Set (Clause α)} {S : Set (Literal α)}
    {n : ℕ} {C : Clause α} {l : Literal α} (hCF : C ∈ F) (hlC : l ∈ C)
    (hneg : ∀ other ∈ C, other ≠ l → negLit other ∈ (stepUP F)^[n] S) :
    l ∈ (stepUP F)^[n + 1] S := by
  rw [Function.iterate_succ_apply']
  exact Or.inr ⟨C, hCF, hlC, hneg⟩

private theorem stepUP_sound {α : Type} {assign : α → Bool} {F : Set (Clause α)}
    {S : Set (Literal α)} (hF : Satisfies assign F) (hS : ∀ l ∈ S, assign l.1 = l.2) :
    ∀ n : ℕ, ∀ l ∈ (stepUP F)^[n] S, assign l.1 = l.2 := by
  intro n
  induction n with
  | zero => exact hS
  | @succ n ih =>
    rw [Function.iterate_succ_apply']
    rintro l (hl | ⟨C, hCF, hlC, hneg⟩)
    · exact ih l hl
    · obtain ⟨w, hwC, hwa⟩ := hF C hCF
      by_cases hwe : w = l
      · rw [← hwe]; exact hwa
      · have hnw := ih _ (hneg w hwC hwe)
        dsimp only [negLit] at hnw
        rw [hwa] at hnw
        cases hw2 : w.2 <;> simp [hw2] at hnw

private def OrGate : ℕ → Type
  | 0 => Empty
  | n + 1 => Unit ⊕ (OrGate n ⊕ OrGate n)

private def decEqOrGate : (n : ℕ) → DecidableEq (OrGate n)
  | 0 => fun a => Empty.elim a
  | n + 1 => by
    letI : DecidableEq (OrGate n) := decEqOrGate n
    exact inferInstanceAs (DecidableEq (Unit ⊕ (OrGate n ⊕ OrGate n)))

private instance instDecEqOrGate (n : ℕ) : DecidableEq (OrGate n) := decEqOrGate n

private def orGateUniv : (n : ℕ) → { s : Finset (OrGate n) // ∀ x, x ∈ s }
  | 0 => ⟨∅, fun a => Empty.elim a⟩
  | n + 1 =>
    let s := (orGateUniv n).1
    ⟨insert (Sum.inl ()) (s.image (Sum.inr ∘ Sum.inl) ∪ s.image (Sum.inr ∘ Sum.inr)), by
      intro x
      rcases x with ⟨⟩ | xL | xR
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ((orGateUniv n).2 xL)))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ((orGateUniv n).2 xR)))⟩

private instance instFintypeOrGate (n : ℕ) : Fintype (OrGate n) :=
  ⟨(orGateUniv n).1, (orGateUniv n).2⟩

private theorem card_OrGate (n : ℕ) : Fintype.card (OrGate n) = 2 ^ n - 1 := by
  induction n with
  | zero => rfl
  | @succ n ih =>
    rw [Fintype.card_congr (show OrGate (n + 1) ≃ Unit ⊕ (OrGate n ⊕ OrGate n) from Equiv.refl _)]
    simp only [Fintype.card_sum, Fintype.card_unit, ih, pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
    omega

private def orOut {α : Type} {n : ℕ} (base : OrGate n → α) (leaf : (Fin n → Bool) → α) : α :=
  match n with
  | 0 => leaf Fin.elim0
  | _ + 1 => base (Sum.inl ())

private def orClauses {α : Type} [DecidableEq α] {n : ℕ}
    (base : OrGate n → α) (leaf : (Fin n → Bool) → α) : Finset (Clause α) :=
  match n with
  | 0 => ∅
  | _ + 1 =>
    let g := base (Sum.inl ())
    let baseL : OrGate _ → α := fun x => base (Sum.inr (Sum.inl x))
    let leafL : (Fin _ → Bool) → α := fun f => leaf (Fin.cons false f)
    let baseR : OrGate _ → α := fun x => base (Sum.inr (Sum.inr x))
    let leafR : (Fin _ → Bool) → α := fun f => leaf (Fin.cons true f)
    let gL := orOut baseL leafL
    let gR := orOut baseR leafR
    ({{(g, false), (gL, true), (gR, true)}, {(gL, false), (g, true)}, {(gR, false), (g, true)}} :
        Finset (Clause α)) ∪
      orClauses baseL leafL ∪ orClauses baseR leafR

private theorem card_le_three_orClauses {α : Type} [DecidableEq α] {n : ℕ}
    (base : OrGate n → α) (leaf : (Fin n → Bool) → α) :
    ∀ C ∈ orClauses base leaf, C.card ≤ 3 := by
  induction n with
  | zero => intro C hC; simp [orClauses] at hC
  | @succ n ih =>
    intro C hC
    dsimp only [orClauses] at hC
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with (((rfl | rfl | rfl) | hL) | hR)
    · exact Finset.card_le_three
    · exact le_trans Finset.card_le_two (by decide)
    · exact le_trans Finset.card_le_two (by decide)
    · exact ih _ _ C hL
    · exact ih _ _ C hR

private theorem sum_insert_le_add {β : Type} [DecidableEq β] (a : β) (s : Finset β) (f : β → ℕ) :
    (∑ x ∈ insert a s, f x) ≤ f a + ∑ x ∈ s, f x := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]; omega
  · rw [Finset.sum_insert ha]

private theorem sum_card_union_le {α : Type} [DecidableEq α] (A B : Finset (Finset α)) :
    (∑ C ∈ A ∪ B, C.card) ≤ (∑ C ∈ A, C.card) + (∑ C ∈ B, C.card) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A _ ih =>
    rw [Finset.insert_union]
    have h1 := sum_insert_le_add a (A ∪ B) Finset.card
    have h2 : a ∉ A := by assumption
    rw [Finset.sum_insert h2]
    omega

private theorem sum_card_orClauses {α : Type} [DecidableEq α] {n : ℕ}
    (base : OrGate n → α) (leaf : (Fin n → Bool) → α) :
    (∑ C ∈ orClauses base leaf, C.card) ≤ 7 * (2 ^ n - 1) := by
  induction n with
  | zero => simp [orClauses]
  | @succ n ih =>
    dsimp only [orClauses]
    set g := base (Sum.inl ())
    set baseL : OrGate n → α := fun x => base (Sum.inr (Sum.inl x))
    set leafL : (Fin n → Bool) → α := fun f => leaf (Fin.cons false f)
    set baseR : OrGate n → α := fun x => base (Sum.inr (Sum.inr x))
    set leafR : (Fin n → Bool) → α := fun f => leaf (Fin.cons true f)
    set gL := orOut baseL leafL
    set gR := orOut baseR leafR
    set c1 : Clause α := {(g, false), (gL, true), (gR, true)}
    set c2 : Clause α := {(gL, false), (g, true)}
    set c3 : Clause α := {(gR, false), (g, true)}
    have hu1 := sum_card_union_le ({c1, c2, c3} ∪ orClauses baseL leafL) (orClauses baseR leafR)
    have hu2 := sum_card_union_le ({c1, c2, c3} : Finset (Clause α)) (orClauses baseL leafL)
    have htop : (∑ C ∈ ({c1, c2, c3} : Finset (Clause α)), C.card) ≤ 7 := by
      have hs1 := sum_insert_le_add c1 ({c2, c3} : Finset (Clause α)) Finset.card
      have hs2 := sum_insert_le_add c2 ({c3} : Finset (Clause α)) Finset.card
      have hs3 : (∑ C ∈ ({c3} : Finset (Clause α)), C.card) = c3.card := Finset.sum_singleton _ _
      have h1 : c1.card ≤ 3 := Finset.card_le_three
      have h2 : c2.card ≤ 2 := Finset.card_le_two
      have h3 : c3.card ≤ 2 := Finset.card_le_two
      omega
    have ihL := ih baseL leafL
    have ihR := ih baseR leafR
    have hpos : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    have hle := Nat.add_le_add (Nat.add_le_add htop ihL) ihR
    have hsum : (∑ C ∈ ({c1, c2, c3} ∪ orClauses baseL leafL ∪ orClauses baseR leafR), C.card) ≤
        7 + 7 * (2 ^ n - 1) + 7 * (2 ^ n - 1) :=
      le_trans hu1 (le_trans (Nat.add_le_add_right hu2 _) hle)
    omega

private def orGateEval : {n : ℕ} → ((Fin n → Bool) → Bool) → OrGate n → Bool
  | 0, _, g => Empty.elim g
  | _ + 1, lval, g => match g with
    | Sum.inl () => decide (∃ f : Fin (_ + 1) → Bool, lval f = true)
    | Sum.inr (Sum.inl gL) => orGateEval (fun f => lval (Fin.cons false f)) gL
    | Sum.inr (Sum.inr gR) => orGateEval (fun f => lval (Fin.cons true f)) gR

private theorem orOut_eval {α : Type} {n : ℕ} (assign : α → Bool) (base : OrGate n → α)
    (leaf : (Fin n → Bool) → α) (lval : (Fin n → Bool) → Bool)
    (hb : ∀ g, assign (base g) = orGateEval lval g) (hl : ∀ f, assign (leaf f) = lval f) :
    assign (orOut base leaf) = decide (∃ f : Fin n → Bool, lval f = true) := by
  cases n with
  | zero =>
    dsimp only [orOut]
    rw [hl Fin.elim0]
    by_cases h : lval Fin.elim0 = true
    · rw [h, eq_comm, decide_eq_true ⟨Fin.elim0, h⟩]
    · have hf : lval Fin.elim0 = false := Bool.eq_false_iff.mpr h
      rw [hf, eq_comm, decide_eq_false_iff_not]
      rintro ⟨f, hft⟩
      have heq : f = Fin.elim0 := funext fun j => j.elim0
      rw [heq, hf] at hft
      exact Bool.false_ne_true hft
  | succ n =>
    dsimp only [orOut]
    rw [hb (Sum.inl ())]
    rfl

private theorem orGateEval_satisfies_orClauses {α : Type} [DecidableEq α] {n : ℕ}
    (assign : α → Bool) (base : OrGate n → α) (leaf : (Fin n → Bool) → α)
    (lval : (Fin n → Bool) → Bool)
    (hb : ∀ g, assign (base g) = orGateEval lval g) (hl : ∀ f, assign (leaf f) = lval f) :
    ∀ C ∈ orClauses base leaf, ClauseSat assign C := by
  induction n with
  | zero => intro C hC; simp [orClauses] at hC
  | @succ n ih =>
    intro C hC
    dsimp only [orClauses] at hC
    have hL_eval := orOut_eval assign
      (fun x => base (Sum.inr (Sum.inl x))) (fun f => leaf (Fin.cons false f))
      (fun f => lval (Fin.cons false f))
      (fun x => hb (Sum.inr (Sum.inl x))) (fun f => hl (Fin.cons false f))
    have hR_eval := orOut_eval assign
      (fun x => base (Sum.inr (Sum.inr x))) (fun f => leaf (Fin.cons true f))
      (fun f => lval (Fin.cons true f))
      (fun x => hb (Sum.inr (Sum.inr x))) (fun f => hl (Fin.cons true f))
    have hG_eval : assign (base (Sum.inl ())) = decide (∃ f : Fin (n + 1) → Bool, lval f = true) :=
      hb (Sum.inl ())
    have hiff : (∃ f : Fin (n + 1) → Bool, lval f = true) ↔
        (∃ f, lval (Fin.cons false f) = true) ∨ (∃ f, lval (Fin.cons true f) = true) := by
      constructor
      · rintro ⟨f, hf⟩
        have hcons : Fin.cons (f 0) (Fin.tail f) = f := funext (Fin.cases rfl (fun _ => rfl))
        by_cases h0 : f 0 = true
        · right; refine ⟨Fin.tail f, ?_⟩
          have hf0' : Fin.cons true (Fin.tail f) = f := by rw [← h0, hcons]
          rw [hf0']; exact hf
        · have hf0 : f 0 = false := Bool.eq_false_iff.mpr h0
          left; refine ⟨Fin.tail f, ?_⟩
          have hf0' : Fin.cons false (Fin.tail f) = f := by rw [← hf0, hcons]
          rw [hf0']; exact hf
      · rintro (⟨f, hf⟩ | ⟨f, hf⟩)
        · exact ⟨Fin.cons false f, hf⟩
        · exact ⟨Fin.cons true f, hf⟩
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with (((rfl | rfl | rfl) | hL) | hR)
    · by_cases exL : ∃ f, lval (Fin.cons false f) = true
      · exact ⟨(_, true), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by
          rw [hL_eval, decide_eq_true exL]⟩
      · by_cases exR : ∃ f, lval (Fin.cons true f) = true
        · exact ⟨(_, true), Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), by
            rw [hR_eval, decide_eq_true exR]⟩
        · exact ⟨(base (Sum.inl ()), false), Finset.mem_insert_self _ _, by
            rw [hG_eval, decide_eq_false (fun h => (hiff.mp h).elim exL exR)]⟩
    · by_cases exL : ∃ f, lval (Fin.cons false f) = true
      · exact ⟨(base (Sum.inl ()), true), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by
          rw [hG_eval, decide_eq_true (hiff.mpr (Or.inl exL))]⟩
      · exact ⟨(_, false), Finset.mem_insert_self _ _, by
          rw [hL_eval, decide_eq_false exL]⟩
    · by_cases exR : ∃ f, lval (Fin.cons true f) = true
      · exact ⟨(base (Sum.inl ()), true), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), by
          rw [hG_eval, decide_eq_true (hiff.mpr (Or.inr exR))]⟩
      · exact ⟨(_, false), Finset.mem_insert_self _ _, by
          rw [hR_eval, decide_eq_false exR]⟩
    · exact ih _ _ _ (fun x => hb (Sum.inr (Sum.inl x))) (fun f => hl (Fin.cons false f)) C hL
    · exact ih _ _ _ (fun x => hb (Sum.inr (Sum.inr x))) (fun f => hl (Fin.cons true f)) C hR

private theorem orClauses_prop_false {α : Type} [DecidableEq α] {n : ℕ}
    {F : Set (Clause α)} {S : Set (Literal α)} (base : OrGate n → α) (leaf : (Fin n → Bool) → α)
    (hF : (↑(orClauses base leaf) : Set (Clause α)) ⊆ F)
    (hS : ∀ f : Fin n → Bool, (leaf f, false) ∈ S) :
    (orOut base leaf, false) ∈ (stepUP F)^[n] S := by
  induction n with
  | zero => exact hS Fin.elim0
  | @succ n ih =>
    dsimp only [orOut]
    have hsubL : (↑(orClauses (fun x => base (Sum.inr (Sum.inl x)))
        (fun f => leaf (Fin.cons false f))) : Set (Clause α)) ⊆ F := fun C hC =>
      hF (Finset.mem_union_left _ (Finset.mem_union_right _ hC))
    have hsubR : (↑(orClauses (fun x => base (Sum.inr (Sum.inr x)))
        (fun f => leaf (Fin.cons true f))) : Set (Clause α)) ⊆ F := fun C hC =>
      hF (Finset.mem_union_right _ hC)
    have ihL := ih _ _ hsubL (fun f => hS (Fin.cons false f))
    have ihR := ih _ _ hsubR (fun f => hS (Fin.cons true f))
    set g := base (Sum.inl ())
    set gL := orOut (fun x => base (Sum.inr (Sum.inl x))) (fun f => leaf (Fin.cons false f))
    set gR := orOut (fun x => base (Sum.inr (Sum.inr x))) (fun f => leaf (Fin.cons true f))
    have hCF : ({(g, false), (gL, true), (gR, true)} : Clause α) ∈ F :=
      hF (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _)))
    refine mem_stepUP_succ_of_clause hCF (Finset.mem_insert_self _ _) ?_
    intro other hother hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hother
    rcases hother with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact ihL
    · exact ihR

private def clauseAnd2 {α : Type} [DecidableEq α] (out a b : α) : Finset (Clause α) :=
  {{(out, false), (a, true)}, {(out, false), (b, true)}, {(a, false), (b, false), (out, true)}}

private theorem clauseAnd2_card_le_three {α : Type} [DecidableEq α] (out a b : α) :
    ∀ C ∈ clauseAnd2 out a b, C.card ≤ 3 := by
  intro C hC
  simp only [clauseAnd2, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl | rfl
  · exact le_trans Finset.card_le_two (by decide)
  · exact le_trans Finset.card_le_two (by decide)
  · exact Finset.card_le_three

private theorem clauseAnd2_sum_le {α : Type} [DecidableEq α] (out a b : α) :
    (∑ C ∈ clauseAnd2 out a b, C.card) ≤ 7 := by
  dsimp only [clauseAnd2]
  set c1 : Clause α := {(out, false), (a, true)}
  set c2 : Clause α := {(out, false), (b, true)}
  set c3 : Clause α := {(a, false), (b, false), (out, true)}
  have hs1 := sum_insert_le_add c1 ({c2, c3} : Finset (Clause α)) Finset.card
  have hs2 := sum_insert_le_add c2 ({c3} : Finset (Clause α)) Finset.card
  have hs3 : (∑ C ∈ ({c3} : Finset (Clause α)), C.card) = c3.card := Finset.sum_singleton _ _
  have h1 : c1.card ≤ 2 := Finset.card_le_two
  have h2 : c2.card ≤ 2 := Finset.card_le_two
  have h3 : c3.card ≤ 3 := Finset.card_le_three
  omega

private theorem clauseAnd2_sat {α : Type} [DecidableEq α] {assign : α → Bool} {out a b : α}
    (heq : assign out = (assign a && assign b)) :
    ∀ C ∈ clauseAnd2 out a b, ClauseSat assign C := by
  intro C hC
  simp only [clauseAnd2, Finset.mem_insert, Finset.mem_singleton] at hC
  rcases hC with rfl | rfl | rfl
  · by_cases ha : assign a = true
    · exact ⟨(a, true), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ha⟩
    · have haf : assign a = false := Bool.eq_false_iff.mpr ha
      exact ⟨(out, false), Finset.mem_insert_self _ _, by simp [heq, haf]⟩
  · by_cases hb : assign b = true
    · exact ⟨(b, true), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hb⟩
    · have hbf : assign b = false := Bool.eq_false_iff.mpr hb
      exact ⟨(out, false), Finset.mem_insert_self _ _, by simp [heq, hbf]⟩
  · by_cases ha : assign a = true
    · by_cases hb : assign b = true
      · exact ⟨(out, true), Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), by
          simp [heq, ha, hb]⟩
      · have hbf : assign b = false := Bool.eq_false_iff.mpr hb
        exact ⟨(b, false), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hbf⟩
    · have haf : assign a = false := Bool.eq_false_iff.mpr ha
      exact ⟨(a, false), Finset.mem_insert_self _ _, haf⟩

private theorem clauseAnd2_prop_false_left {α : Type} [DecidableEq α] {F : Set (Clause α)}
    {S : Set (Literal α)} {out a b : α} (hF : (↑(clauseAnd2 out a b) : Set (Clause α)) ⊆ F)
    (ha : (a, false) ∈ S) : (out, false) ∈ stepUP F S := by
  refine Or.inr ⟨{(out, false), (a, true)},
    hF (Finset.mem_insert_self _ _), Finset.mem_insert_self _ _, fun other ho hne => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl
  · exact absurd rfl hne
  · exact ha

private theorem clauseAnd2_prop_false_right {α : Type} [DecidableEq α] {F : Set (Clause α)}
    {S : Set (Literal α)} {out a b : α} (hF : (↑(clauseAnd2 out a b) : Set (Clause α)) ⊆ F)
    (hb : (b, false) ∈ S) : (out, false) ∈ stepUP F S := by
  refine Or.inr ⟨{(out, false), (b, true)},
    hF (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), Finset.mem_insert_self _ _,
    fun other ho hne => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl
  · exact absurd rfl hne
  · exact hb

private abbrev In4 : Type := Fin 4 → Bool

private def ins4 (t : Fin 5) (b : Bool) (g : In4) : In5 := fun u =>
  if hu : u.val < t.val then g ⟨u.val, by omega⟩
  else if u.val = t.val then b
  else g ⟨u.val - 1, by omega⟩

private theorem ins4_at (t : Fin 5) (b : Bool) (g : In4) : ins4 t b g t = b := by
  dsimp only [ins4]
  simp

private theorem ins4_surj {in5 : In5} {t : Fin 5} {b : Bool} (ht : in5 t = b) :
    ∃ g : In4, ins4 t b g = in5 := by
  refine ⟨fun j => if j.val < t.val then in5 ⟨j.val, by omega⟩ else in5 ⟨j.val + 1, by omega⟩, ?_⟩
  funext u
  dsimp only [ins4]
  by_cases h1 : u.val < t.val
  · simp [h1]
  · by_cases h2 : u.val = t.val
    · have hue : u = t := Fin.ext h2
      simp [hue, ht]
    · have h3 : ¬ (u.val - 1 < t.val) := by omega
      have h4 : u.val - 1 + 1 = u.val := by omega
      simp [h1, h2, h3, h4]

private inductive SegTree (k : ℕ) : Type
  | leaf (i : Fin k) : SegTree k
  | node (lo : ℕ) (mid : Fin k) (hi : ℕ) (L R : SegTree k) : SegTree k

private def SegTree.depth {k : ℕ} : SegTree k → ℕ
  | .leaf _ => 0
  | .node _ _ _ L R => max L.depth R.depth + 1

private def SegTree.leafCount {k : ℕ} : SegTree k → ℕ
  | .leaf _ => 1
  | .node _ _ _ L R => L.leafCount + R.leafCount

private def SegTree.internalCount {k : ℕ} : SegTree k → ℕ
  | .leaf _ => 0
  | .node _ _ _ L R => 1 + L.internalCount + R.internalCount

private def SegTree.hasLeaf {k : ℕ} (i : Fin k) : SegTree k → Prop
  | .leaf j => i = j
  | .node _ _ _ L R => L.hasLeaf i ∨ R.hasLeaf i

private def SegTree.hasMid {k : ℕ} (lo : ℕ) (m : Fin k) (hi : ℕ) : SegTree k → Prop
  | .leaf _ => False
  | .node lo' mid hi' L R => (lo' = lo ∧ mid = m ∧ hi' = hi) ∨ L.hasMid lo m hi ∨ R.hasMid lo m hi

private def SegValid (k : ℕ) : SegTree k → ℕ → ℕ → Prop
  | .leaf i, lo, hi => lo = i.val ∧ hi = i.val + 1
  | .node lo' mid hi' L R, lo, hi =>
    lo' = lo ∧ hi' = hi ∧ lo < mid.val ∧ mid.val < hi ∧
      SegValid k L lo mid.val ∧ SegValid k R mid.val hi

private def SegCover (k : ℕ) : SegTree k → ℕ → ℕ → Prop
  | .leaf i, lo, hi => lo = i.val ∧ hi = i.val + 1
  | .node lo' mid hi' L R, lo, hi =>
    lo' = lo ∧ hi' = hi ∧ lo < mid.val ∧ mid.val < hi ∧
      SegCover k L lo mid.val ∧ SegCover k R mid.val hi ∧
      (∀ i : Fin k, lo ≤ i.val ∧ i.val < mid.val → L.hasLeaf i) ∧
      (∀ i : Fin k, mid.val ≤ i.val ∧ i.val < hi → R.hasLeaf i)

private def lookupMid {k : ℕ} : SegTree k → Fin k → ℕ × ℕ
  | .leaf _, _ => (0, k)
  | .node lo mid hi L R, m =>
    if m = mid then (lo, hi)
    else if m.val < mid.val then lookupMid L m
    else lookupMid R m

private theorem hasLeaf_bounds {k : ℕ} {t : SegTree k} {lo hi : ℕ} (hv : SegValid k t lo hi)
    {i : Fin k} (hl : t.hasLeaf i) : lo ≤ i.val ∧ i.val < hi := by
  induction t generalizing lo hi with
  | leaf j =>
    dsimp only [SegValid] at hv
    have heq : i = j := hl
    subst heq
    omega
  | node lo' mid hi' L R ihL ihR =>
    rcases hv with ⟨rfl, rfl, _, _, hvL, hvR⟩
    rcases hl with hlL | hlR
    · have := ihL hvL hlL; omega
    · have := ihR hvR hlR; omega

private theorem hasMid_bounds {k : ℕ} {t : SegTree k} {lo0 hi0 lo hi : ℕ} {m : Fin k}
    (hv : SegValid k t lo0 hi0) (hm : t.hasMid lo m hi) :
    lo0 ≤ lo ∧ lo < m.val ∧ m.val < hi ∧ hi ≤ hi0 := by
  induction t generalizing lo0 hi0 with
  | leaf _ => exact hm.elim
  | node lo' mid hi' L R ihL ihR =>
    rcases hv with ⟨rfl, rfl, hlm, hmh, hvL, hvR⟩
    rcases hm with ⟨rfl, rfl, rfl⟩ | hmL | hmR
    · exact ⟨le_rfl, hlm, hmh, le_rfl⟩
    · have := ihL hvL hmL; omega
    · have := ihR hvR hmR; omega

private theorem lookupMid_of_hasMid {k : ℕ} {t : SegTree k} {lo0 hi0 lo hi : ℕ} {m : Fin k}
    (hv : SegValid k t lo0 hi0) (hm : t.hasMid lo m hi) :
    lookupMid t m = (lo, hi) := by
  induction t generalizing lo0 hi0 with
  | leaf _ => exact hm.elim
  | node lo' mid hi' L R ihL ihR =>
    rcases hv with ⟨rfl, rfl, hlm, hmh, hvL, hvR⟩
    dsimp only [lookupMid]
    rcases hm with ⟨rfl, rfl, rfl⟩ | hmL | hmR
    · simp
    · have hm_lt := (hasMid_bounds hvL hmL).2.2.1
      have hmr := (hasMid_bounds hvL hmL).2.2.2
      have hne : m ≠ mid := fun h => by subst h; omega
      have hlt : m.val < mid.val := by omega
      simp only [hne, ↓reduceIte, hlt]
      exact ihL hvL hmL
    · have hm_gt := (hasMid_bounds hvR hmR).1
      have hml := (hasMid_bounds hvR hmR).2.1
      have hne : m ≠ mid := fun h => by subst h; omega
      have hnlt : ¬ m.val < mid.val := by omega
      simp only [hne, ↓reduceIte, hnlt]
      exact ihR hvR hmR

private def buildSeg (k lo len : ℕ) (hlen : 0 < len) (hbound : lo + len ≤ k) : SegTree k :=
  if h1 : len = 1 then
    SegTree.leaf ⟨lo, by omega⟩
  else
    let half := len / 2
    have hhalf : 0 < half := by omega
    have hrem : 0 < len - half := by omega
    have hm : lo + half < k := by omega
    SegTree.node lo ⟨lo + half, hm⟩ (lo + len)
      (buildSeg k lo half hhalf (by omega))
      (buildSeg k (lo + half) (len - half) hrem (by omega))
termination_by len
decreasing_by all_goals omega

private theorem buildSeg_valid (k lo len : ℕ) (hlen : 0 < len) (hbound : lo + len ≤ k) :
    SegValid k (buildSeg k lo len hlen hbound) lo (lo + len) := by
  induction len using Nat.strong_induction_on generalizing lo with
  | ind len ih =>
    unfold buildSeg
    by_cases h1 : len = 1
    · subst h1
      simp only [↓reduceDIte, SegValid]
      exact ⟨trivial, trivial⟩
    · simp only [h1, ↓reduceDIte, SegValid]
      have hhalf : 0 < len / 2 := by omega
      have hrem : 0 < len - len / 2 := by omega
      refine ⟨trivial, trivial, by omega, by omega, ?_, ?_⟩
      · exact ih (len / 2) (by omega) lo hhalf (by omega)
      · have heq : lo + len / 2 + (len - len / 2) = lo + len := by omega
        rw [← heq]
        exact ih (len - len / 2) (by omega) (lo + len / 2) hrem (by omega)

private theorem buildSeg_hasLeaf (k lo len : ℕ) (hlen : 0 < len) (hbound : lo + len ≤ k)
    (i : Fin k) (hi1 : lo ≤ i.val) (hi2 : i.val < lo + len) :
    (buildSeg k lo len hlen hbound).hasLeaf i := by
  induction len using Nat.strong_induction_on generalizing lo with
  | ind len ih =>
    unfold buildSeg
    by_cases h1 : len = 1
    · subst h1
      simp only [↓reduceDIte, SegTree.hasLeaf]
      exact Fin.ext (by dsimp only; omega)
    · simp only [h1, ↓reduceDIte, SegTree.hasLeaf]
      by_cases hleft : i.val < lo + len / 2
      · left; exact ih (len / 2) (by omega) lo (by omega) (by omega) hi1 hleft
      · right; exact ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega) (by omega) (by omega)

private theorem buildSeg_counts (k lo len : ℕ) (hlen : 0 < len) (hbound : lo + len ≤ k) :
    (buildSeg k lo len hlen hbound).leafCount = len ∧
    (buildSeg k lo len hlen hbound).internalCount = len - 1 := by
  induction len using Nat.strong_induction_on generalizing lo with
  | ind len ih =>
    unfold buildSeg
    by_cases h1 : len = 1
    · simp [h1, SegTree.leafCount, SegTree.internalCount]
    · simp only [h1, ↓reduceDIte, SegTree.leafCount, SegTree.internalCount]
      have ihL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have ihR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      omega

private theorem buildSeg_depth_le (k lo len : ℕ) (hlen : 0 < len) (hbound : lo + len ≤ k) :
    (buildSeg k lo len hlen hbound).depth ≤ Nat.clog 2 len := by
  induction len using Nat.strong_induction_on generalizing lo with
  | ind len ih =>
    unfold buildSeg
    by_cases h1 : len = 1
    · simp [h1, SegTree.depth]
    · simp only [h1, ↓reduceDIte, SegTree.depth]
      have h2 : 2 ≤ len := by omega
      have hpow : len ≤ 2 ^ Nat.clog 2 len := Nat.le_pow_clog (by decide) len
      have hclog_pos : 0 < Nat.clog 2 len := by
        by_contra hz
        have hcz : Nat.clog 2 len = 0 := by omega
        rw [hcz, pow_zero] at hpow
        omega
      have hpow_succ : 2 ^ Nat.clog 2 len = 2 * 2 ^ (Nat.clog 2 len - 1) := by
        conv_lhs => rw [show Nat.clog 2 len = (Nat.clog 2 len - 1) + 1 by omega, pow_succ']
      have hhalf_le : len / 2 ≤ 2 ^ (Nat.clog 2 len - 1) := by omega
      have hrem_le : len - len / 2 ≤ 2 ^ (Nat.clog 2 len - 1) := by omega
      have hcL : Nat.clog 2 (len / 2) ≤ Nat.clog 2 len - 1 :=
        (Nat.clog_le_iff_le_pow (by decide)).mpr hhalf_le
      have hcR : Nat.clog 2 (len - len / 2) ≤ Nat.clog 2 len - 1 :=
        (Nat.clog_le_iff_le_pow (by decide)).mpr hrem_le
      have ihL := ih (len / 2) (by omega) lo (by omega) (by omega)
      have ihR := ih (len - len / 2) (by omega) (lo + len / 2) (by omega) (by omega)
      omega

private inductive AuxVar (k r : ℕ) : Type
  | falseVar : AuxVar k r
  | matchVar (i : Fin k) (in5 : In5) : AuxVar k r
  | matchA01 (i : Fin k) (in5 : In5) : AuxVar k r
  | matchA23 (i : Fin k) (in5 : In5) : AuxVar k r
  | matchA0123 (i : Fin k) (in5 : In5) : AuxVar k r
  | forceGate (i : Fin k) (t : Fin 5) (sign : Bool) (g : OrGate 4) : AuxVar k r
  | inLeaf (i : Fin k) (a b : State r) (g : OrGate 5) : AuxVar k r
  | inNode (mid : Fin k) (a c : State r) (g : OrGate (W1 r + 1)) : AuxVar k r
  | triIn (mid : Fin k) (a b c : State r) : AuxVar k r
  | rootOK (g : OrGate (W1 r + 1)) : AuxVar k r
  | outRoot (a b : State r) : AuxVar k r
  | outLeft (mid : Fin k) (a b : State r) (g : OrGate (W1 r + 1)) : AuxVar k r
  | triOutL (mid : Fin k) (a b c : State r) : AuxVar k r
  | outRight (mid : Fin k) (b c : State r) (g : OrGate (W1 r + 1)) : AuxVar k r
  | triOutR (mid : Fin k) (a b c : State r) : AuxVar k r
  | bothLeaf (i : Fin k) (a b : State r) : AuxVar k r
  | matchToBoth (i : Fin k) (in5 : In5) (g : OrGate (W1 r + 1)) : AuxVar k r
  deriving DecidableEq

private def equivAuxVar (k r : ℕ) :
    AuxVar k r ≃
      ((Unit ⊕
      ((Fin k × In5) ⊕ ((Fin k × In5) ⊕ ((Fin k × In5) ⊕ ((Fin k × In5) ⊕
      ((Fin k × Fin 5 × Bool × OrGate 4) ⊕ ((Fin k × State r × State r × OrGate 5) ⊕
      ((Fin k × State r × State r × OrGate (W1 r + 1)) ⊕
      (Fin k × State r × State r × State r))))))))) ⊕
      (OrGate (W1 r + 1) ⊕ ((State r × State r) ⊕
      ((Fin k × State r × State r × OrGate (W1 r + 1)) ⊕
      ((Fin k × State r × State r × State r) ⊕
      ((Fin k × State r × State r × OrGate (W1 r + 1)) ⊕
      ((Fin k × State r × State r × State r) ⊕
      ((Fin k × State r × State r) ⊕
      (Fin k × In5 × OrGate (W1 r + 1)))))))))) :=
  { toFun := fun v => match v with
      | .falseVar => Sum.inl (Sum.inl ())
      | .matchVar i p => Sum.inl (Sum.inr (Sum.inl (i, p)))
      | .matchA01 i p => Sum.inl (Sum.inr (Sum.inr (Sum.inl (i, p))))
      | .matchA23 i p => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p)))))
      | .matchA0123 i p => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p))))))
      | .forceGate i t s g => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, t, s, g)))))))
      | .inLeaf i a b g => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, a, b, g))))))))
      | .inNode m a c g => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, c, g)))))))))
      | .triIn m a b c => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (m, a, b, c)))))))))
      | .rootOK g => Sum.inr (Sum.inl g)
      | .outRoot a b => Sum.inr (Sum.inr (Sum.inl (a, b)))
      | .outLeft m a b g => Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, b, g))))
      | .triOutL m a b c => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, b, c)))))
      | .outRight m b c g => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, b, c, g))))))
      | .triOutR m a b c => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, b, c)))))))
      | .bothLeaf i a b => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, a, b))))))))
      | .matchToBoth i p g => Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, p, g))))))))
    invFun := fun s => match s with
      | Sum.inl (Sum.inl ()) => .falseVar
      | Sum.inl (Sum.inr (Sum.inl (i, p))) => .matchVar i p
      | Sum.inl (Sum.inr (Sum.inr (Sum.inl (i, p)))) => .matchA01 i p
      | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p))))) => .matchA23 i p
      | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, p)))))) => .matchA0123 i p
      | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, t, s, g))))))) => .forceGate i t s g
      | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, a, b, g)))))))) => .inLeaf i a b g
      | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, c, g))))))))) => .inNode m a c g
      | Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (m, a, b, c))))))))) => .triIn m a b c
      | Sum.inr (Sum.inl g) => .rootOK g
      | Sum.inr (Sum.inr (Sum.inl (a, b))) => .outRoot a b
      | Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, b, g)))) => .outLeft m a b g
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, b, c))))) => .triOutL m a b c
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, b, c, g)))))) => .outRight m b c g
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (m, a, b, c))))))) => .triOutR m a b c
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, a, b)))))))) => .bothLeaf i a b
      | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (i, p, g)))))))) => .matchToBoth i p g
    left_inv := fun v => by cases v <;> rfl
    right_inv := fun s => by
      rcases s with
        ((⟨⟩ | ⟨i, p⟩ | ⟨i, p⟩ | ⟨i, p⟩ | ⟨i, p⟩ | ⟨i, t, s, g⟩ | ⟨i, a, b, g⟩ | ⟨m, a, c, g⟩ | ⟨m, a, b, c⟩) |
         (g | ⟨a, b⟩ | ⟨m, a, b, g⟩ | ⟨m, a, b, c⟩ | ⟨m, b, c, g⟩ | ⟨m, a, b, c⟩ | ⟨i, a, b⟩ | ⟨i, p, g⟩)) <;> rfl }

private instance (k r : ℕ) : Fintype (AuxVar k r) := Fintype.ofEquiv _ (equivAuxVar k r).symm

private theorem card_AuxVar_le (k r : ℕ) :
    Fintype.card (AuxVar k r) ≤ 15 * (k + 1) * (2 ^ (W1 r + 1)) ^ 3 := by
  let S := 2 ^ (W1 r + 1)
  have hcard : Fintype.card (AuxVar k r) =
      1 + (k * 32 + (k * 32 + (k * 32 + (k * 32 + (k * 5 * 2 * 15 + (k * S * S * 31 +
        (k * S * S * (S - 1) + k * S * S * S))))))) +
      ((S - 1) + (S * S + (k * S * S * (S - 1) + (k * S * S * S +
        (k * S * S * (S - 1) + (k * S * S * S + (k * S * S + k * 32 * (S - 1)))))))) := by
    rw [Fintype.card_congr (equivAuxVar k r)]
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, card_OrGate, card_State, show (Fintype.card In5) = 32 by decide]
    simp only [show (2 : ℕ) ^ 4 - 1 = 15 by decide, show (2 : ℕ) ^ 5 - 1 = 31 by decide,
      ← mul_assoc]
    rfl
  rw [hcard]
  have hS_sub : S - 1 ≤ S := Nat.sub_le _ _
  have hS8 : 8 ≤ S := by
    change 2 ^ 3 ≤ 2 ^ (W1 r + 1)
    exact Nat.pow_le_pow_right (by decide) (by dsimp only [W1]; omega)
  have h1 : S ^ 2 * 8 ≤ S ^ 3 := by
    calc S ^ 2 * 8 ≤ S ^ 2 * S := Nat.mul_le_mul_left _ hS8
      _ = S ^ 3 := by ring
  have h2 : S * 64 ≤ S ^ 3 := by
    have h64 : 64 ≤ S * S := by
      calc 64 = 8 * 8 := by decide
        _ ≤ S * S := Nat.mul_le_mul hS8 hS8
    calc S * 64 ≤ S * (S * S) := Nat.mul_le_mul_left _ h64
      _ = S ^ 3 := by ring
  have h3 : 512 ≤ S ^ 3 := by
    calc 512 = 8 ^ 3 := by decide
      _ ≤ S ^ 3 := Nat.pow_le_pow_left hS8 3
  have hm0 : k * S * S * (S - 1) ≤ k * S ^ 3 := by
    calc k * S * S * (S - 1) ≤ k * S * S * S := Nat.mul_le_mul_left _ hS_sub
      _ = k * S ^ 3 := by ring
  have hm1 : k * S * S * S = k * S ^ 3 := by ring
  have hm2 : k * S * S * 31 ≤ 4 * (k * S ^ 3) := by
    have h4 : 4 * k * S ^ 3 = 4 * (k * S ^ 3) := by ring
    calc k * S * S * 31 ≤ k * S * S * 32 := Nat.mul_le_mul_left _ (by decide)
      _ = 4 * k * (S ^ 2 * 8) := by ring
      _ ≤ 4 * k * S ^ 3 := Nat.mul_le_mul_left _ h1
      _ = 4 * (k * S ^ 3) := h4
  have hm3 : k * S * S ≤ k * S ^ 3 := by
    calc k * S * S ≤ k * S * S * 8 := Nat.le_mul_of_pos_right _ (by decide)
      _ = k * (S ^ 2 * 8) := by ring
      _ ≤ k * S ^ 3 := Nat.mul_le_mul_left _ h1
  have hm4 : k * 32 * (S - 1) ≤ k * S ^ 3 := by
    calc k * 32 * (S - 1) ≤ k * 32 * S := Nat.mul_le_mul_left _ hS_sub
      _ ≤ k * 64 * S := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by decide))
      _ = k * (S * 64) := by ring
      _ ≤ k * S ^ 3 := Nat.mul_le_mul_left _ h2
  have hm5 : S * S ≤ S ^ 3 := by
    calc S * S ≤ S * S * 8 := Nat.le_mul_of_pos_right _ (by decide)
      _ = S ^ 2 * 8 := by ring
      _ ≤ S ^ 3 := h1
  have hm6 : S ≤ S ^ 3 := le_trans (Nat.le_mul_of_pos_right _ (by decide)) h2
  have hm7 : k * 32 + (k * 32 + (k * 32 + (k * 32 + k * 5 * 2 * 15))) ≤ k * S ^ 3 := by
    have ha : k * 32 + (k * 32 + (k * 32 + (k * 32 + k * 5 * 2 * 15))) = k * 278 := by ring
    have hb : k * 278 ≤ k * 512 := Nat.mul_le_mul_left _ (by decide)
    have hc : k * 512 ≤ k * S ^ 3 := Nat.mul_le_mul_left _ h3
    omega
  have h1S : 1 + (S - 1) ≤ S ^ 3 := by
    have hle1 : 1 + (S - 1) = S := by omega
    rw [hle1]; exact hm6
  have hpart1 :
      (k * 32 + (k * 32 + (k * 32 + (k * 32 + (k * 5 * 2 * 15 + (k * S * S * 31 +
        (k * S * S * (S - 1) + k * S * S * S))))))) ≤ 7 * (k * S ^ 3) := by
    have h7 : k * S * S * 31 + (k * S * S * (S - 1) + k * S * S * S) ≤ 6 * (k * S ^ 3) := by
      rw [hm1]; omega
    omega
  have hpart2 :
      (k * S * S * (S - 1) + (k * S * S * S +
        (k * S * S * (S - 1) + (k * S * S * S + (k * S * S + k * 32 * (S - 1)))))) ≤ 6 * (k * S ^ 3) := by
    rw [hm1]; omega
  have hsum_bnd :
      1 + (k * 32 + (k * 32 + (k * 32 + (k * 32 + (k * 5 * 2 * 15 + (k * S * S * 31 +
        (k * S * S * (S - 1) + k * S * S * S))))))) +
      ((S - 1) + (S * S + (k * S * S * (S - 1) + (k * S * S * S +
        (k * S * S * (S - 1) + (k * S * S * S + (k * S * S + k * 32 * (S - 1)))))))) ≤
      13 * (k * S ^ 3) + 2 * S ^ 3 := by
    calc _ = (1 + (S - 1)) + S * S +
            (k * 32 + (k * 32 + (k * 32 + (k * 32 + (k * 5 * 2 * 15 + (k * S * S * 31 +
              (k * S * S * (S - 1) + k * S * S * S))))))) +
            (k * S * S * (S - 1) + (k * S * S * S +
              (k * S * S * (S - 1) + (k * S * S * S + (k * S * S + k * 32 * (S - 1)))))) := by ring
      _ ≤ S ^ 3 + S ^ 3 + 7 * (k * S ^ 3) + 6 * (k * S ^ 3) :=
          Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h1S hm5) hpart1) hpart2
      _ = 13 * (k * S ^ 3) + 2 * S ^ 3 := by ring
  have hfin : 13 * (k * S ^ 3) + 2 * S ^ 3 ≤ 15 * (k + 1) * S ^ 3 := by
    calc 13 * (k * S ^ 3) + 2 * S ^ 3 ≤ 15 * (k * S ^ 3) + 15 * S ^ 3 := by omega
      _ = 15 * (k + 1) * S ^ 3 := by ring
  exact le_trans hsum_bnd hfin

private abbrev VarSum (k r : ℕ) : Type := Sum (Fin 5 × Fin k) (AuxVar k r)

private def inOutVar {k r : ℕ} : SegTree k → State r → State r → VarSum k r
  | .leaf i, a, b => Sum.inr (AuxVar.inLeaf i a b (Sum.inl ()))
  | .node _ mid _ _ _, a, c => Sum.inr (AuxVar.inNode mid a c (Sum.inl ()))

private def cMatchOne {k r : ℕ} (i : Fin k) (in5 : In5) : Finset (Clause (VarSum k r)) :=
  let mv := Sum.inr (AuxVar.matchVar i in5)
  let p01 := Sum.inr (AuxVar.matchA01 i in5)
  let p23 := Sum.inr (AuxVar.matchA23 i in5)
  let p0123 := Sum.inr (AuxVar.matchA0123 i in5)
  Finset.univ.image (fun t : Fin 5 => ({(mv, false), (Sum.inl (t, i), in5 t)} : Clause (VarSum k r))) ∪
    {{(Sum.inl (0, i), !(in5 0)), (Sum.inl (1, i), !(in5 1)), (p01, true)},
     {(Sum.inl (2, i), !(in5 2)), (Sum.inl (3, i), !(in5 3)), (p23, true)},
     {(p01, false), (p23, false), (p0123, true)},
     {(p0123, false), (Sum.inl (4, i), !(in5 4)), (mv, true)}}

private def cMatch {k r : ℕ} : Finset (Clause (VarSum k r)) :=
  (Finset.univ : Finset (Fin k × In5)).biUnion (fun p => cMatchOne p.1 p.2)

private def cForce {k r : ℕ} : Finset (Clause (VarSum k r)) :=
  (Finset.univ : Finset (Fin k × Fin 5 × Bool)).biUnion (fun ⟨i, t, sign⟩ =>
    let leaf : In4 → VarSum k r := fun g => Sum.inr (AuxVar.matchVar i (ins4 t (!sign) g))
    orClauses (fun g => Sum.inr (AuxVar.forceGate i t sign g)) leaf ∪
      {{(Sum.inr (AuxVar.forceGate i t sign (Sum.inl ())), true), (Sum.inl (t, i), sign)}})

private def cInLeaf {k r : ℕ} : Finset (Clause (VarSum k r)) :=
  (Finset.univ : Finset (Fin k × State r × State r)).biUnion (fun ⟨i, a, b⟩ =>
    orClauses (fun g => Sum.inr (AuxVar.inLeaf i a b g))
      (fun in5 => if LeafOK i in5 a b then Sum.inr (AuxVar.matchVar i in5) else Sum.inr AuxVar.falseVar))

private def cInTree {k r : ℕ} : SegTree k → Finset (Clause (VarSum k r))
  | .leaf _ => ∅
  | .node _ mid _ L R =>
    let here := (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨a, c⟩ =>
      (Finset.univ : Finset (State r)).biUnion (fun b =>
        clauseAnd2 (Sum.inr (AuxVar.triIn mid a b c)) (inOutVar L a b) (inOutVar R b c)) ∪
      orClauses (fun g => Sum.inr (AuxVar.inNode mid a c g))
        (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) c)))
    here ∪ cInTree L ∪ cInTree R

private def cRootOK {k r : ℕ} (tree : SegTree k) : Finset (Clause (VarSum k r)) :=
  orClauses (fun g => Sum.inr (AuxVar.rootOK g))
    (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a) ∪
    {{(Sum.inr (AuxVar.rootOK (Sum.inl ())), true)}}

private def cOutRoot {k r : ℕ} : Finset (Clause (VarSum k r)) :=
  (Finset.univ : Finset (State r × State r)).image (fun ⟨a, b⟩ =>
    ({(Sum.inr (AuxVar.outRoot a b), decide (a = b))} : Clause (VarSum k r)))

private def cOutTree {k r : ℕ} : SegTree k → (State r → State r → AuxVar k r) →
    Finset (Clause (VarSum k r))
  | .leaf i, parentOut =>
    (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨a, b⟩ =>
      clauseAnd2 (Sum.inr (AuxVar.bothLeaf i a b)) (inOutVar (.leaf i) a b) (Sum.inr (parentOut a b)))
  | .node _ mid _ L R, parentOut =>
    let outL : State r → State r → AuxVar k r := fun a b => AuxVar.outLeft mid a b (Sum.inl ())
    let outR : State r → State r → AuxVar k r := fun b c => AuxVar.outRight mid b c (Sum.inl ())
    let hereL := (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨a, b⟩ =>
      (Finset.univ : Finset (State r)).biUnion (fun c =>
        clauseAnd2 (Sum.inr (AuxVar.triOutL mid a b c)) (Sum.inr (parentOut a c)) (inOutVar R b c)) ∪
      orClauses (fun g => Sum.inr (AuxVar.outLeft mid a b g))
        (fun f => Sum.inr (AuxVar.triOutL mid a b ((equivStateVec r).symm f))))
    let hereR := (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨b, c⟩ =>
      (Finset.univ : Finset (State r)).biUnion (fun a =>
        clauseAnd2 (Sum.inr (AuxVar.triOutR mid a b c)) (Sum.inr (parentOut a c)) (inOutVar L a b)) ∪
      orClauses (fun g => Sum.inr (AuxVar.outRight mid b c g))
        (fun f => Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) b c)))
    hereL ∪ hereR ∪ cOutTree L outL ∪ cOutTree R outR

private def cMatchToBoth {k r : ℕ} : Finset (Clause (VarSum k r)) :=
  (Finset.univ : Finset (Fin k × In5)).biUnion (fun ⟨i, in5⟩ =>
    orClauses (fun g => Sum.inr (AuxVar.matchToBoth i in5 g))
      (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
        | none => Sum.inr AuxVar.falseVar
        | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b)) ∪
    {{(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inr (AuxVar.matchToBoth i in5 (Sum.inl ())), true)}})

private def F_aux {k r : ℕ} (tree : SegTree k) : Finset (Clause (VarSum k r)) :=
  ({({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r))} : Finset (Clause (VarSum k r))) ∪
    cMatch ∪ cForce ∪ cInLeaf ∪ cInTree tree ∪ cRootOK tree ∪ cOutRoot ∪
    cOutTree tree AuxVar.outRoot ∪ cMatchToBoth

private theorem sum_biUnion_le {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (f : ι → Finset (Finset α)) (B : ℕ)
    (hB : ∀ x ∈ s, (∑ C ∈ f x, C.card) ≤ B) :
    (∑ C ∈ s.biUnion f, C.card) ≤ s.card * B := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.card_insert_of_notMem ha, Nat.succ_mul]
    have hu := sum_card_union_le (f a) (s.biUnion f)
    have haB := hB a (Finset.mem_insert_self _ _)
    have ihB := ih (fun x hx => hB x (Finset.mem_insert_of_mem hx))
    omega

private theorem sum_image_le {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (s : Finset ι) (f : ι → Finset α) (B : ℕ)
    (hB : ∀ x ∈ s, (f x).card ≤ B) :
    (∑ C ∈ s.image f, C.card) ≤ s.card * B := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.image_insert, Finset.card_insert_of_notMem ha, Nat.succ_mul]
    have hs := sum_insert_le_add (f a) (s.image f) Finset.card
    have haB := hB a (Finset.mem_insert_self _ _)
    have ihB := ih (fun x hx => hB x (Finset.mem_insert_of_mem hx))
    omega

private theorem F_aux_card_le_three {k r : ℕ} (tree : SegTree k) :
    ∀ C ∈ (F_aux tree : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
  have hMatch : ∀ C ∈ (cMatch : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro C hC
    simp only [cMatch, Finset.mem_biUnion, cMatchOne, Finset.mem_union,
      Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hC
    rcases hC with ⟨⟨i, in5⟩, _, (⟨t, _, rfl⟩ | rfl | rfl | rfl | rfl)⟩
    · exact le_trans Finset.card_le_two (by decide)
    · exact Finset.card_le_three
    · exact Finset.card_le_three
    · exact Finset.card_le_three
    · exact Finset.card_le_three
  have hForce : ∀ C ∈ (cForce : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro C hC
    simp only [cForce, Finset.mem_biUnion, Finset.mem_union, Finset.mem_singleton] at hC
    rcases hC with ⟨⟨i, t, s⟩, _, h1 | rfl⟩
    · exact card_le_three_orClauses _ _ C h1
    · exact le_trans Finset.card_le_two (by decide)
  have hInLeaf : ∀ C ∈ (cInLeaf : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro C hC
    simp only [cInLeaf, Finset.mem_biUnion] at hC
    rcases hC with ⟨⟨i, a, b⟩, _, h1⟩
    exact card_le_three_orClauses _ _ C h1
  have hInTree : ∀ (t : SegTree k), ∀ C ∈ (cInTree t : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro t
    induction t with
    | leaf _ => intro C hC; simp [cInTree] at hC
    | node _ mid _ L R ihL ihR =>
      intro C hC
      simp only [cInTree, Finset.mem_union, Finset.mem_biUnion] at hC
      rcases hC with ((⟨⟨a, c⟩, _, (⟨b, _, hb⟩ | ho)⟩ | hL) | hR)
      · exact clauseAnd2_card_le_three _ _ _ C hb
      · exact card_le_three_orClauses _ _ C ho
      · exact ihL C hL
      · exact ihR C hR
  have hRootOK : ∀ C ∈ (cRootOK tree : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro C hC
    simp only [cRootOK, Finset.mem_union, Finset.mem_singleton] at hC
    rcases hC with h1 | rfl
    · exact card_le_three_orClauses _ _ C h1
    · rw [Finset.card_singleton]; decide
  have hOutRoot : ∀ C ∈ (cOutRoot : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro C hC
    simp only [cOutRoot, Finset.mem_image] at hC
    rcases hC with ⟨⟨a, b⟩, _, rfl⟩
    rw [Finset.card_singleton]; decide
  have hOutTree : ∀ (t : SegTree k) (p : State r → State r → AuxVar k r),
      ∀ C ∈ (cOutTree t p : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro t
    induction t with
    | leaf i =>
      intro p C hC
      simp only [cOutTree, Finset.mem_biUnion] at hC
      rcases hC with ⟨⟨a, b⟩, _, h1⟩
      exact clauseAnd2_card_le_three _ _ _ C h1
    | node _ mid _ L R ihL ihR =>
      intro p C hC
      simp only [cOutTree, Finset.mem_union, Finset.mem_biUnion] at hC
      rcases hC with (((⟨⟨a, b⟩, _, ⟨c, _, hc⟩ | ho⟩ | ⟨⟨b, c⟩, _, ⟨a, _, ha⟩ | ho⟩) | hL) | hR)
      · exact clauseAnd2_card_le_three _ _ _ C hc
      · exact card_le_three_orClauses _ _ C ho
      · exact clauseAnd2_card_le_three _ _ _ C ha
      · exact card_le_three_orClauses _ _ C ho
      · exact ihL _ C hL
      · exact ihR _ C hR
  have hMatchToBoth : ∀ C ∈ (cMatchToBoth : Finset (Clause (VarSum k r))), C.card ≤ 3 := by
    intro C hC
    simp only [cMatchToBoth, Finset.mem_biUnion, Finset.mem_union, Finset.mem_singleton] at hC
    rcases hC with ⟨⟨i, in5⟩, _, h1 | rfl⟩
    · exact card_le_three_orClauses _ _ C h1
    · exact le_trans Finset.card_le_two (by decide)
  intro C hC
  simp only [F_aux, Finset.mem_union, Finset.mem_singleton] at hC
  rcases hC with ((((((((rfl | h1) | h2) | h3) | h4) | h5) | h6) | h7) | h8)
  · rw [Finset.card_singleton]; decide
  · exact hMatch C h1
  · exact hForce C h2
  · exact hInLeaf C h3
  · exact hInTree tree C h4
  · exact hRootOK C h5
  · exact hOutRoot C h6
  · exact hOutTree tree _ C h7
  · exact hMatchToBoth C h8

private theorem F_aux_size_le {k r : ℕ} (hk : 0 < k) (tree : SegTree k)
    (hcntL : tree.leafCount = k) (hcntI : tree.internalCount = k - 1) :
    Fintype.card (AuxVar k r) + (∑ C ∈ (F_aux tree : Finset (Clause (VarSum k r))), C.card) ≤
      256 * (k + 1) * 2 ^ (3 * (17 * r + 3)) := by
  let S := 2 ^ (W1 r + 1)
  have hS8 : 8 ≤ S := by
    change 2 ^ 3 ≤ 2 ^ (W1 r + 1)
    exact Nat.pow_le_pow_right (by decide) (by dsimp only [W1]; omega)
  have hS2 : S ^ 2 * 8 ≤ S ^ 3 := by nlinarith
  have hS1 : S * 64 ≤ S ^ 3 := by nlinarith
  have hS0 : 512 ≤ S ^ 3 := by nlinarith
  have hcard1 : (Finset.univ : Finset (Fin k × In5)).card = k * 32 := by
    simp [show (Fintype.card In5) = 32 by decide]
  have hcard2 : (Finset.univ : Finset (Fin k × Fin 5 × Bool)).card = k * 10 := by simp
  have hcard3 : (Finset.univ : Finset (State r)).card = S := card_State r
  have hcard4 : (Finset.univ : Finset (State r × State r)).card = S ^ 2 := by
    simp [card_State r, S, sq]
  have hcard5 : (Finset.univ : Finset (Fin k × State r × State r)).card = k * S ^ 2 := by
    simp [card_State r, S, sq]
  have hsMatch : (∑ C ∈ (cMatch : Finset (Clause (VarSum k r))), C.card) ≤ k * 32 * 22 := by
    apply le_trans (sum_biUnion_le _ _ 22 (fun ⟨i, in5⟩ _ => by
      dsimp only [cMatchOne]
      have hu := sum_card_union_le
        (Finset.univ.image (fun t : Fin 5 => ({(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inl (t, i), in5 t)} : Clause (VarSum k r))))
        ({{(Sum.inl (0, i), !(in5 0)), (Sum.inl (1, i), !(in5 1)), (Sum.inr (AuxVar.matchA01 i in5), true)},
          {(Sum.inl (2, i), !(in5 2)), (Sum.inl (3, i), !(in5 3)), (Sum.inr (AuxVar.matchA23 i in5), true)},
          {(Sum.inr (AuxVar.matchA01 i in5), false), (Sum.inr (AuxVar.matchA23 i in5), false), (Sum.inr (AuxVar.matchA0123 i in5), true)},
          {(Sum.inr (AuxVar.matchA0123 i in5), false), (Sum.inl (4, i), !(in5 4)), (Sum.inr (AuxVar.matchVar i in5), true)}} : Finset (Clause (VarSum k r)))
      have him := sum_image_le (Finset.univ : Finset (Fin 5))
        (fun t : Fin 5 => ({(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inl (t, i), in5 t)} : Clause (VarSum k r)))
        2 (fun _ _ => Finset.card_le_two)
      simp only [Finset.card_univ, Fintype.card_fin] at him
      set c1 : Clause (VarSum k r) := {(Sum.inl (0, i), !(in5 0)), (Sum.inl (1, i), !(in5 1)), (Sum.inr (AuxVar.matchA01 i in5), true)}
      set c2 : Clause (VarSum k r) := {(Sum.inl (2, i), !(in5 2)), (Sum.inl (3, i), !(in5 3)), (Sum.inr (AuxVar.matchA23 i in5), true)}
      set c3 : Clause (VarSum k r) := {(Sum.inr (AuxVar.matchA01 i in5), false), (Sum.inr (AuxVar.matchA23 i in5), false), (Sum.inr (AuxVar.matchA0123 i in5), true)}
      set c4 : Clause (VarSum k r) := {(Sum.inr (AuxVar.matchA0123 i in5), false), (Sum.inl (4, i), !(in5 4)), (Sum.inr (AuxVar.matchVar i in5), true)}
      have h4 : (∑ C ∈ ({c1, c2, c3, c4} : Finset (Clause (VarSum k r))), C.card) ≤ 12 := by
        have hs1 := sum_insert_le_add c1 ({c2, c3, c4} : Finset (Clause (VarSum k r))) Finset.card
        have hs2 := sum_insert_le_add c2 ({c3, c4} : Finset (Clause (VarSum k r))) Finset.card
        have hs3 := sum_insert_le_add c3 ({c4} : Finset (Clause (VarSum k r))) Finset.card
        have hs4 : (∑ C ∈ ({c4} : Finset (Clause (VarSum k r))), C.card) = c4.card := Finset.sum_singleton _ _
        have hc1 : c1.card ≤ 3 := Finset.card_le_three
        have hc2 : c2.card ≤ 3 := Finset.card_le_three
        have hc3 : c3.card ≤ 3 := Finset.card_le_three
        have hc4 : c4.card ≤ 3 := Finset.card_le_three
        omega
      have hle22 : 10 + 12 ≤ 22 := by decide
      exact le_trans hu (le_trans (Nat.add_le_add him h4) hle22)))
    rw [hcard1]
  have hsForce : (∑ C ∈ (cForce : Finset (Clause (VarSum k r))), C.card) ≤ k * 10 * 107 := by
    refine le_trans (sum_biUnion_le (Finset.univ : Finset (Fin k × Fin 5 × Bool)) _ 107 ?_) ?_
    · rintro ⟨i, t, sign⟩ _
      dsimp only
      have hu := sum_card_union_le
        (orClauses (fun g => (Sum.inr (AuxVar.forceGate i t sign g) : VarSum k r))
          (fun g => (Sum.inr (AuxVar.matchVar i (ins4 t (!sign) g)) : VarSum k r)))
        ({{(Sum.inr (AuxVar.forceGate i t sign (Sum.inl ())), true), (Sum.inl (t, i), sign)}} : Finset (Clause (VarSum k r)))
      have ho := sum_card_orClauses (fun g => (Sum.inr (AuxVar.forceGate i t sign g) : VarSum k r))
        (fun g => (Sum.inr (AuxVar.matchVar i (ins4 t (!sign) g)) : VarSum k r))
      have hs : (∑ C ∈ ({{(Sum.inr (AuxVar.forceGate i t sign (Sum.inl ())), true), (Sum.inl (t, i), sign)}} : Finset (Clause (VarSum k r))), C.card) ≤ 2 := by
        rw [Finset.sum_singleton]; exact Finset.card_le_two
      have hle107 : 7 * (2 ^ 4 - 1) + 2 ≤ 107 := by decide
      exact le_trans hu (le_trans (Nat.add_le_add ho hs) hle107)
    · rw [hcard2]
  have hsInLeaf : (∑ C ∈ (cInLeaf : Finset (Clause (VarSum k r))), C.card) ≤ k * S ^ 2 * 217 := by
    apply le_trans (sum_biUnion_le _ _ 217 (fun ⟨i, a, b⟩ _ =>
      sum_card_orClauses (fun g => Sum.inr (AuxVar.inLeaf i a b g))
        (fun in5 => if LeafOK i in5 a b then Sum.inr (AuxVar.matchVar i in5) else Sum.inr AuxVar.falseVar)))
    rw [hcard5]
  have hsInTree : ∀ (t : SegTree k),
      (∑ C ∈ (cInTree t : Finset (Clause (VarSum k r))), C.card) ≤ 14 * t.internalCount * S ^ 3 := by
    intro t
    induction t with
    | leaf _ => simp [cInTree, SegTree.internalCount]
    | node _ mid _ L R ihL ihR =>
      dsimp only [cInTree, SegTree.internalCount]
      set here : Finset (Clause (VarSum k r)) := (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨a, c⟩ =>
        (Finset.univ : Finset (State r)).biUnion (fun b =>
          clauseAnd2 (Sum.inr (AuxVar.triIn mid a b c)) (inOutVar L a b) (inOutVar R b c)) ∪
        orClauses (fun g => Sum.inr (AuxVar.inNode mid a c g))
          (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) c)))
      have hu1 := sum_card_union_le (here ∪ cInTree (r := r) L) (cInTree (r := r) R)
      have hu2 := sum_card_union_le here (cInTree (r := r) L)
      have hhere : (∑ C ∈ here, C.card) ≤ 14 * S ^ 3 := by
        refine le_trans (sum_biUnion_le (Finset.univ : Finset (State r × State r)) _ (14 * S) ?_) ?_
        · rintro ⟨a, c⟩ _
          dsimp only
          have hu := sum_card_union_le
            ((Finset.univ : Finset (State r)).biUnion (fun b =>
              clauseAnd2 (Sum.inr (AuxVar.triIn mid a b c)) (inOutVar L a b) (inOutVar R b c)))
            (orClauses (fun g => (Sum.inr (AuxVar.inNode mid a c g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) c)))
          have hb := sum_biUnion_le (Finset.univ : Finset (State r))
            (fun b => clauseAnd2 (Sum.inr (AuxVar.triIn mid a b c)) (inOutVar L a b) (inOutVar R b c))
            7 (fun b _ => clauseAnd2_sum_le _ _ _)
          have ho : (∑ C ∈ orClauses (fun g => (Sum.inr (AuxVar.inNode mid a c g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) c)), C.card) ≤ 7 * (S - 1) :=
            sum_card_orClauses (fun g => (Sum.inr (AuxVar.inNode mid a c g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) c))
          rw [hcard3] at hb
          have hsub : 7 * (S - 1) ≤ 7 * S := Nat.mul_le_mul_left 7 (Nat.sub_le S 1)
          have hadd := Nat.add_le_add hb ho
          have hfin : S * 7 + 7 * (S - 1) ≤ 14 * S := by omega
          exact le_trans hu (le_trans hadd hfin)
        · rw [hcard4]
          exact le_of_eq (by ring)
      have hsum : (∑ C ∈ (here ∪ cInTree (r := r) L ∪ cInTree (r := r) R), C.card) ≤
          14 * S ^ 3 + 14 * L.internalCount * S ^ 3 + 14 * R.internalCount * S ^ 3 :=
        le_trans hu1 (le_trans (Nat.add_le_add_right hu2 _) (Nat.add_le_add (Nat.add_le_add hhere ihL) ihR))
      exact le_trans hsum (le_of_eq (by ring))
  have hsRootOK : (∑ C ∈ (cRootOK tree : Finset (Clause (VarSum k r))), C.card) ≤ 7 * S + 1 := by
    have hu := sum_card_union_le
      (orClauses (fun g => Sum.inr (AuxVar.rootOK g)) (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a))
      ({{(Sum.inr (AuxVar.rootOK (Sum.inl ())), true)}} : Finset (Clause (VarSum k r)))
    have ho : (∑ C ∈ orClauses (fun g => Sum.inr (AuxVar.rootOK g))
        (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a), C.card) ≤ 7 * (S - 1) :=
      sum_card_orClauses (fun g => Sum.inr (AuxVar.rootOK g))
        (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a)
    have h1 : (∑ C ∈ ({{(Sum.inr (AuxVar.rootOK (Sum.inl ())), true)}} : Finset (Clause (VarSum k r))), C.card) = 1 := by
      simp
    have hsub : 7 * (S - 1) ≤ 7 * S := Nat.mul_le_mul_left 7 (Nat.sub_le S 1)
    exact le_trans (le_trans hu (Nat.add_le_add ho (le_of_eq h1))) (Nat.add_le_add_right hsub 1)
  have hsOutRoot : (∑ C ∈ (cOutRoot : Finset (Clause (VarSum k r))), C.card) ≤ S ^ 2 := by
    apply le_trans (sum_image_le (Finset.univ : Finset (State r × State r)) _ 1 (fun _ _ => by simp))
    rw [hcard4]; omega
  have hsOutTree : ∀ (t : SegTree k) (p : State r → State r → AuxVar k r),
      (∑ C ∈ (cOutTree t p : Finset (Clause (VarSum k r))), C.card) ≤
        (28 * t.internalCount + 7 * t.leafCount) * S ^ 3 := by
    intro t
    induction t with
    | leaf i =>
      intro p
      dsimp only [cOutTree, SegTree.internalCount, SegTree.leafCount]
      refine le_trans (sum_biUnion_le (Finset.univ : Finset (State r × State r)) _ 7 ?_) ?_
      · rintro ⟨a, b⟩ _
        exact clauseAnd2_sum_le _ _ _
      · rw [hcard4]
        calc S ^ 2 * 7 = 7 * S ^ 2 * 1 := by ring
          _ ≤ 7 * S ^ 2 * S := Nat.mul_le_mul_left _ (le_trans (by decide : 1 ≤ 8) hS8)
          _ = (28 * 0 + 7 * 1) * S ^ 3 := by ring
    | node _ mid _ L R ihL ihR =>
      intro p
      dsimp only [cOutTree, SegTree.internalCount, SegTree.leafCount]
      set hereL : Finset (Clause (VarSum k r)) :=
        (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨a, b⟩ =>
          (Finset.univ : Finset (State r)).biUnion (fun c =>
            clauseAnd2 (Sum.inr (AuxVar.triOutL mid a b c)) (Sum.inr (p a c)) (inOutVar R b c)) ∪
          orClauses (fun g => (Sum.inr (AuxVar.outLeft mid a b g) : VarSum k r))
            (fun f => Sum.inr (AuxVar.triOutL mid a b ((equivStateVec r).symm f))))
      set hereR : Finset (Clause (VarSum k r)) :=
        (Finset.univ : Finset (State r × State r)).biUnion (fun ⟨b, c⟩ =>
          (Finset.univ : Finset (State r)).biUnion (fun a =>
            clauseAnd2 (Sum.inr (AuxVar.triOutR mid a b c)) (Sum.inr (p a c)) (inOutVar L a b)) ∪
          orClauses (fun g => (Sum.inr (AuxVar.outRight mid b c g) : VarSum k r))
            (fun f => Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) b c)))
      have hu1 := sum_card_union_le
        (hereL ∪ hereR ∪ cOutTree L (fun a b => AuxVar.outLeft mid a b (Sum.inl ())))
        (cOutTree R (fun b c => AuxVar.outRight mid b c (Sum.inl ())))
      have hu2 := sum_card_union_le (hereL ∪ hereR)
        (cOutTree L (fun a b => AuxVar.outLeft mid a b (Sum.inl ())))
      have hu3 := sum_card_union_le hereL hereR
      have hL_here : (∑ C ∈ hereL, C.card) ≤ 14 * S ^ 3 := by
        refine le_trans (sum_biUnion_le (Finset.univ : Finset (State r × State r)) _ (14 * S) ?_) ?_
        · rintro ⟨a, b⟩ _
          dsimp only
          have hu := sum_card_union_le
            ((Finset.univ : Finset (State r)).biUnion (fun c =>
              clauseAnd2 (Sum.inr (AuxVar.triOutL mid a b c)) (Sum.inr (p a c)) (inOutVar R b c)))
            (orClauses (fun g => (Sum.inr (AuxVar.outLeft mid a b g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triOutL mid a b ((equivStateVec r).symm f))))
          have hb := sum_biUnion_le (Finset.univ : Finset (State r))
            (fun c => clauseAnd2 (Sum.inr (AuxVar.triOutL mid a b c)) (Sum.inr (p a c)) (inOutVar R b c))
            7 (fun c _ => clauseAnd2_sum_le _ _ _)
          have ho : (∑ C ∈ orClauses (fun g => (Sum.inr (AuxVar.outLeft mid a b g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triOutL mid a b ((equivStateVec r).symm f))), C.card) ≤ 7 * (S - 1) :=
            sum_card_orClauses (fun g => (Sum.inr (AuxVar.outLeft mid a b g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triOutL mid a b ((equivStateVec r).symm f)))
          rw [hcard3] at hb
          have hsub : 7 * (S - 1) ≤ 7 * S := Nat.mul_le_mul_left 7 (Nat.sub_le S 1)
          have hadd := Nat.add_le_add hb ho
          have hfin : S * 7 + 7 * (S - 1) ≤ 14 * S := by omega
          exact le_trans hu (le_trans hadd hfin)
        · rw [hcard4]; exact le_of_eq (by ring)
      have hR_here : (∑ C ∈ hereR, C.card) ≤ 14 * S ^ 3 := by
        refine le_trans (sum_biUnion_le (Finset.univ : Finset (State r × State r)) _ (14 * S) ?_) ?_
        · rintro ⟨b, c⟩ _
          dsimp only
          have hu := sum_card_union_le
            ((Finset.univ : Finset (State r)).biUnion (fun a =>
              clauseAnd2 (Sum.inr (AuxVar.triOutR mid a b c)) (Sum.inr (p a c)) (inOutVar L a b)))
            (orClauses (fun g => (Sum.inr (AuxVar.outRight mid b c g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) b c)))
          have hb := sum_biUnion_le (Finset.univ : Finset (State r))
            (fun a => clauseAnd2 (Sum.inr (AuxVar.triOutR mid a b c)) (Sum.inr (p a c)) (inOutVar L a b))
            7 (fun a _ => clauseAnd2_sum_le _ _ _)
          have ho : (∑ C ∈ orClauses (fun g => (Sum.inr (AuxVar.outRight mid b c g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) b c)), C.card) ≤ 7 * (S - 1) :=
            sum_card_orClauses (fun g => (Sum.inr (AuxVar.outRight mid b c g) : VarSum k r))
              (fun f => Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) b c))
          rw [hcard3] at hb
          have hsub : 7 * (S - 1) ≤ 7 * S := Nat.mul_le_mul_left 7 (Nat.sub_le S 1)
          have hadd := Nat.add_le_add hb ho
          have hfin : S * 7 + 7 * (S - 1) ≤ 14 * S := by omega
          exact le_trans hu (le_trans hadd hfin)
        · rw [hcard4]; exact le_of_eq (by ring)
      have hi1 := ihL (fun a b => AuxVar.outLeft mid a b (Sum.inl ()))
      have hi2 := ihR (fun b c => AuxVar.outRight mid b c (Sum.inl ()))
      have h1 := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hL_here hR_here) hi1) hi2
      have hsum : (∑ C ∈ (hereL ∪ hereR ∪ cOutTree L (fun a b => AuxVar.outLeft mid a b (Sum.inl ())) ∪
          cOutTree R (fun b c => AuxVar.outRight mid b c (Sum.inl ()))), C.card) ≤
          14 * S ^ 3 + 14 * S ^ 3 + (28 * L.internalCount + 7 * L.leafCount) * S ^ 3 +
            (28 * R.internalCount + 7 * R.leafCount) * S ^ 3 :=
        le_trans hu1 (le_trans (Nat.add_le_add_right hu2 _) (le_trans (Nat.add_le_add_right (Nat.add_le_add_right hu3 _) _) h1))
      exact le_trans hsum (le_of_eq (by ring))
  have hsMTB : (∑ C ∈ (cMatchToBoth : Finset (Clause (VarSum k r))), C.card) ≤ k * 32 * (7 * S + 2) := by
    refine le_trans (sum_biUnion_le (Finset.univ : Finset (Fin k × In5)) _ (7 * S + 2) ?_) ?_
    · rintro ⟨i, in5⟩ _
      dsimp only
      have hu := sum_card_union_le
        (orClauses (fun g => (Sum.inr (AuxVar.matchToBoth i in5 g) : VarSum k r))
          (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
            | none => (Sum.inr AuxVar.falseVar : VarSum k r)
            | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b)))
        ({{(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inr (AuxVar.matchToBoth i in5 (Sum.inl ())), true)}} : Finset (Clause (VarSum k r)))
      have ho : (∑ C ∈ orClauses (fun g => (Sum.inr (AuxVar.matchToBoth i in5 g) : VarSum k r))
          (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
            | none => (Sum.inr AuxVar.falseVar : VarSum k r)
            | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b)), C.card) ≤ 7 * (S - 1) :=
        sum_card_orClauses (fun g => (Sum.inr (AuxVar.matchToBoth i in5 g) : VarSum k r))
          (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
            | none => (Sum.inr AuxVar.falseVar : VarSum k r)
            | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b))
      have hs : (∑ C ∈ ({{(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inr (AuxVar.matchToBoth i in5 (Sum.inl ())), true)}} : Finset (Clause (VarSum k r))), C.card) ≤ 2 := by
        rw [Finset.sum_singleton]; exact Finset.card_le_two
      have hsub : 7 * (S - 1) ≤ 7 * S := Nat.mul_le_mul_left 7 (Nat.sub_le S 1)
      have hadd := Nat.add_le_add ho hs
      have hfin : 7 * (S - 1) + 2 ≤ 7 * S + 2 := Nat.add_le_add_right hsub 2
      exact le_trans hu (le_trans hadd hfin)
    · rw [hcard1]
  have hsF : (∑ C ∈ (F_aux tree : Finset (Clause (VarSum k r))), C.card) ≤
      1 + k * 32 * 22 + k * 10 * 107 + k * S ^ 2 * 217 + 14 * k * S ^ 3 +
        (7 * S + 1) + S ^ 2 + (28 * k + 7 * k) * S ^ 3 + k * 32 * (7 * S + 2) := by
    dsimp only [F_aux]
    set s0 : Finset (Clause (VarSum k r)) := {({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r))}
    set s1 := s0 ∪ (cMatch : Finset (Clause (VarSum k r)))
    set s2 := s1 ∪ (cForce : Finset (Clause (VarSum k r)))
    set s3 := s2 ∪ (cInLeaf : Finset (Clause (VarSum k r)))
    set s4 := s3 ∪ (cInTree (r := r) tree : Finset (Clause (VarSum k r)))
    set s5 := s4 ∪ (cRootOK (r := r) tree : Finset (Clause (VarSum k r)))
    set s6 := s5 ∪ (cOutRoot : Finset (Clause (VarSum k r)))
    set s7 := s6 ∪ (cOutTree tree (AuxVar.outRoot (r := r)) : Finset (Clause (VarSum k r)))
    have h1 := sum_card_union_le s7 (cMatchToBoth : Finset (Clause (VarSum k r)))
    have h2 := sum_card_union_le s6 (cOutTree tree (AuxVar.outRoot (r := r)) : Finset (Clause (VarSum k r)))
    have h3 := sum_card_union_le s5 (cOutRoot : Finset (Clause (VarSum k r)))
    have h4 := sum_card_union_le s4 (cRootOK (r := r) tree : Finset (Clause (VarSum k r)))
    have h5 := sum_card_union_le s3 (cInTree (r := r) tree : Finset (Clause (VarSum k r)))
    have h6 := sum_card_union_le s2 (cInLeaf : Finset (Clause (VarSum k r)))
    have h7 := sum_card_union_le s1 (cForce : Finset (Clause (VarSum k r)))
    have h8 := sum_card_union_le s0 (cMatch : Finset (Clause (VarSum k r)))
    have hs0 : (∑ C ∈ s0, C.card) = 1 := by simp [s0]
    have hit := hsInTree tree
    have hot := hsOutTree tree AuxVar.outRoot
    rw [hcntI] at hit hot
    rw [hcntL] at hot
    have hik : k - 1 ≤ k := Nat.sub_le _ _
    have hhit : 14 * (k - 1) * S ^ 3 ≤ 14 * k * S ^ 3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hik)
    have hhot : (28 * (k - 1) + 7 * k) * S ^ 3 ≤ (28 * k + 7 * k) * S ^ 3 :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul_left 28 hik) _)
    have hb1 : (∑ C ∈ s1, C.card) ≤ 1 + k * 32 * 22 :=
      le_trans h8 (Nat.add_le_add (le_of_eq hs0) hsMatch)
    have hb2 : (∑ C ∈ s2, C.card) ≤ 1 + k * 32 * 22 + k * 10 * 107 :=
      le_trans h7 (Nat.add_le_add hb1 hsForce)
    have hb3 : (∑ C ∈ s3, C.card) ≤ 1 + k * 32 * 22 + k * 10 * 107 + k * S ^ 2 * 217 :=
      le_trans h6 (Nat.add_le_add hb2 hsInLeaf)
    have hb4 : (∑ C ∈ s4, C.card) ≤ 1 + k * 32 * 22 + k * 10 * 107 + k * S ^ 2 * 217 + 14 * k * S ^ 3 :=
      le_trans h5 (Nat.add_le_add hb3 (le_trans hit hhit))
    have hb5 : (∑ C ∈ s5, C.card) ≤ 1 + k * 32 * 22 + k * 10 * 107 + k * S ^ 2 * 217 + 14 * k * S ^ 3 + (7 * S + 1) :=
      le_trans h4 (Nat.add_le_add hb4 hsRootOK)
    have hb6 : (∑ C ∈ s6, C.card) ≤ 1 + k * 32 * 22 + k * 10 * 107 + k * S ^ 2 * 217 + 14 * k * S ^ 3 + (7 * S + 1) + S ^ 2 :=
      le_trans h3 (Nat.add_le_add hb5 hsOutRoot)
    have hb7 : (∑ C ∈ s7, C.card) ≤ 1 + k * 32 * 22 + k * 10 * 107 + k * S ^ 2 * 217 + 14 * k * S ^ 3 + (7 * S + 1) + S ^ 2 + (28 * k + 7 * k) * S ^ 3 :=
      le_trans h2 (Nat.add_le_add hb6 (le_trans hot hhot))
    exact le_trans h1 (Nat.add_le_add hb7 hsMTB)
  have hvar : Fintype.card (AuxVar k r) ≤ 15 * (k + 1) * S ^ 3 := card_AuxVar_le k r
  have hle1 : k * S ^ 2 * 217 ≤ 28 * (k * S ^ 3) := by
    have h217 : 217 ≤ 224 := by decide
    calc k * S ^ 2 * 217 ≤ k * S ^ 2 * 224 := Nat.mul_le_mul_left _ h217
      _ = 28 * (k * (S ^ 2 * 8)) := by ring
      _ ≤ 28 * (k * S ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS2)
  have hle2 : k * 32 * (7 * S + 2) ≤ 4 * (k * S ^ 3) := by
    have h72 : 7 * S + 2 ≤ 8 * S := by omega
    calc k * 32 * (7 * S + 2) ≤ k * 32 * (8 * S) := Nat.mul_le_mul_left _ h72
      _ = 4 * (k * (S * 64)) := by ring
      _ ≤ 4 * (k * S ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS1)
  have hle3 : 1 + k * 32 * 22 + k * 10 * 107 ≤ 4 * (k * S ^ 3) := by
    have h1775 : 1 + k * 32 * 22 + k * 10 * 107 ≤ 2048 * k := by omega
    calc 1 + k * 32 * 22 + k * 10 * 107 ≤ 4 * (k * 512) := by omega
      _ ≤ 4 * (k * S ^ 3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS0)
  have hle4 : (7 * S + 1) + S ^ 2 ≤ 2 * S ^ 3 := by
    have h71 : 7 * S + 1 ≤ S * 64 := by omega
    have hs2 : S ^ 2 ≤ S ^ 2 * 8 := Nat.le_mul_of_pos_right _ (by decide)
    calc (7 * S + 1) + S ^ 2 ≤ S ^ 3 + S ^ 3 := Nat.add_le_add (le_trans h71 hS1) (le_trans hs2 hS2)
      _ = 2 * S ^ 3 := by ring
  have hSB : S ≤ 2 ^ (17 * r + 3) := by
    change 2 ^ (W1 r + 1) ≤ 2 ^ (17 * r + 3)
    exact Nat.pow_le_pow_right (by decide) (by dsimp only [W1]; omega)
  have hSB3 : S ^ 3 ≤ 2 ^ (3 * (17 * r + 3)) := by
    calc S ^ 3 ≤ (2 ^ (17 * r + 3)) ^ 3 := Nat.pow_le_pow_left hSB 3
      _ = 2 ^ (3 * (17 * r + 3)) := by rw [← pow_mul, Nat.mul_comm]
  have hle_S3 : Fintype.card (AuxVar k r) + (∑ C ∈ (F_aux tree : Finset (Clause (VarSum k r))), C.card) ≤
      256 * (k + 1) * S ^ 3 := by
    have hmul1 : 15 * (k + 1) * S ^ 3 = 15 * (k * S ^ 3) + 15 * S ^ 3 := by ring
    have hmul2 : 14 * k * S ^ 3 + (28 * k + 7 * k) * S ^ 3 = 49 * (k * S ^ 3) := by ring
    have hmul3 : 100 * (k * S ^ 3) + 17 * S ^ 3 ≤ 256 * (k + 1) * S ^ 3 := by
      have ha : 100 * (k * S ^ 3) + 17 * S ^ 3 = (100 * k + 17) * S ^ 3 := by ring
      have hb : 100 * k + 17 ≤ 256 * (k + 1) := by omega
      rw [ha]
      exact Nat.mul_le_mul_right _ hb
    omega
  exact le_trans hle_S3 (Nat.mul_le_mul_left _ hSB3)

private def PathExists {k r : ℕ} (avail : Fin k → In5 → Prop) (lo hi : ℕ)
    (a b : State r) : Prop :=
  ∃ s : ℕ → State r, s lo = a ∧ s hi = b ∧
    ∀ j : ℕ, lo ≤ j → j < hi → ∃ hj : j < k, ∃ in5 : In5,
      avail ⟨j, hj⟩ in5 ∧ LeafOK ⟨j, hj⟩ in5 (s j) (s (j + 1)) = true

private def OutPath {k r : ℕ} (avail : Fin k → In5 → Prop) (lo hi : ℕ)
    (a b : State r) : Prop :=
  ∃ c0 : State r, PathExists avail 0 lo c0 a ∧ PathExists avail hi k b c0

private theorem PathExists_self {k r : ℕ} (avail : Fin k → In5 → Prop) (lo : ℕ) (a b : State r) :
    PathExists avail lo lo a b ↔ a = b := by
  constructor
  · rintro ⟨s, rfl, rfl, _⟩; rfl
  · rintro rfl; exact ⟨fun _ => a, rfl, rfl, fun j h1 h2 => by omega⟩

private theorem PathExists_step {k r : ℕ} (avail : Fin k → In5 → Prop) {j : ℕ} (hj : j < k)
    (a b : State r) :
    PathExists avail j (j + 1) a b ↔
      ∃ in5 : In5, avail ⟨j, hj⟩ in5 ∧ LeafOK ⟨j, hj⟩ in5 a b = true := by
  constructor
  · rintro ⟨s, rfl, rfl, h⟩
    obtain ⟨hj', in5, hav, hok⟩ := h j le_rfl (by omega)
    exact ⟨in5, hav, hok⟩
  · rintro ⟨in5, hav, hok⟩
    refine ⟨fun n => if n = j then a else b, by simp, by simp, fun j' h1 h2 => ?_⟩
    have heq : j' = j := by omega
    subst heq
    refine ⟨hj, in5, hav, ?_⟩
    simpa [Nat.ne_of_gt (Nat.lt_succ_self j')] using hok

private theorem PathExists_split {k r : ℕ} (avail : Fin k → In5 → Prop)
    {lo mid hi : ℕ} (hlm : lo ≤ mid) (hmh : mid ≤ hi) (a c : State r) :
    PathExists avail lo hi a c ↔
      ∃ b : State r, PathExists avail lo mid a b ∧ PathExists avail mid hi b c := by
  constructor
  · rintro ⟨s, hsa, hsc, h⟩
    exact ⟨s mid,
      ⟨s, hsa, rfl, fun j h1 h2 => h j h1 (lt_of_lt_of_le h2 hmh)⟩,
      ⟨s, rfl, hsc, fun j h1 h2 => h j (le_trans hlm h1) h2⟩⟩
  · rintro ⟨b, ⟨s1, hs1a, hs1b, h1⟩, ⟨s2, hs2b, hs2c, h2⟩⟩
    refine ⟨fun n => if n < mid then s1 n else s2 n, ?_, ?_, ?_⟩
    · by_cases hlt : lo < mid
      · simp [hlt, hs1a]
      · have heq : lo = mid := by omega
        subst heq
        simp [hs1a.symm, hs1b, hs2b]
    · have hnot : ¬ hi < mid := by omega
      simp [hnot, hs2c]
    · intro j hj1 hj2
      by_cases hjm : j < mid
      · obtain ⟨hj, in5, hav, hok⟩ := h1 j hj1 hjm
        refine ⟨hj, in5, hav, ?_⟩
        by_cases hj1m : j + 1 < mid
        · simpa [hjm, hj1m] using hok
        · have heq : j + 1 = mid := by omega
          have hnot : ¬ j + 1 < mid := hj1m
          simpa [hjm, hnot, heq, hs2b, ← hs1b] using hok
      · have hge : mid ≤ j := Nat.le_of_not_lt hjm
        obtain ⟨hj, in5, hav, hok⟩ := h2 j hge hj2
        refine ⟨hj, in5, hav, ?_⟩
        have h1m : ¬ j < mid := hjm
        have h2m : ¬ j + 1 < mid := by omega
        simpa [h1m, h2m] using hok

private theorem OutPath_root {k r : ℕ} (avail : Fin k → In5 → Prop) (a b : State r) :
    OutPath avail 0 k a b ↔ a = b := by
  dsimp only [OutPath]
  simp only [PathExists_self]
  constructor
  · rintro ⟨c0, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨a, rfl, rfl⟩

private theorem OutPath_split_L {k r : ℕ} (avail : Fin k → In5 → Prop)
    {lo mid hi : ℕ} (_h0l : 0 ≤ lo) (_hlm : lo ≤ mid) (hmh : mid ≤ hi) (hhk : hi ≤ k)
    (a b : State r) :
    OutPath avail lo mid a b ↔
      ∃ c : State r, PathExists avail mid hi b c ∧ OutPath avail lo hi a c := by
  dsimp only [OutPath]
  constructor
  · rintro ⟨c0, h0, hmk⟩
    rw [PathExists_split avail hmh hhk] at hmk
    obtain ⟨c, hmh_c, hhk_c⟩ := hmk
    exact ⟨c, hmh_c, ⟨c0, h0, hhk_c⟩⟩
  · rintro ⟨c, hmh_c, ⟨c0, h0, hhk_c⟩⟩
    exact ⟨c0, h0, (PathExists_split avail hmh hhk _ _).mpr ⟨c, hmh_c, hhk_c⟩⟩

private theorem OutPath_split_R {k r : ℕ} (avail : Fin k → In5 → Prop)
    {lo mid hi : ℕ} (h0l : 0 ≤ lo) (hlm : lo ≤ mid) (_hmh : mid ≤ hi) (_hhk : hi ≤ k)
    (b c : State r) :
    OutPath avail mid hi b c ↔
      ∃ a : State r, PathExists avail lo mid a b ∧ OutPath avail lo hi a c := by
  dsimp only [OutPath]
  constructor
  · rintro ⟨c0, h0m, hhk_c⟩
    rw [PathExists_split avail h0l hlm] at h0m
    obtain ⟨a, h0a, ham⟩ := h0m
    exact ⟨a, ham, ⟨c0, h0a, hhk_c⟩⟩
  · rintro ⟨a, ham, ⟨c0, h0a, hhk_c⟩⟩
    exact ⟨c0, (PathExists_split avail h0l hlm _ _).mpr ⟨a, h0a, ham⟩, hhk_c⟩

private theorem PathExists_cycle_iff {k r : ℕ} (hk : 0 < k) (avail : Fin k → In5 → Prop) :
    (∃ a : State r, PathExists avail 0 k a a) ↔
      ∃ (s : Fin k → State r) (in5 : Fin k → In5),
        ∀ i : Fin k, avail i (in5 i) ∧ LeafOK i (in5 i) (s i) (s (nextIdx hk i)) = true := by
  constructor
  · rintro ⟨a, ⟨s, hs0, hsk, h⟩⟩
    have hstep : ∀ i : Fin k, ∃ in5 : In5,
        avail i in5 ∧ LeafOK i in5 (s i.val) (s (i.val + 1)) = true := fun i => by
      obtain ⟨hj, in5, hav, hok⟩ := h i.val (Nat.zero_le _) i.isLt
      exact ⟨in5, hav, hok⟩
    choose in5 hin5 using hstep
    refine ⟨fun i => s i.val, in5, fun i => ⟨(hin5 i).1, ?_⟩⟩
    have hnxt : s (nextIdx hk i).val = s (i.val + 1) := by
      dsimp only [nextIdx]
      by_cases hil : i.val + 1 < k
      · rw [Nat.mod_eq_of_lt hil]
      · have hik : i.val + 1 = k := by have := i.isLt; omega
        rw [hik, Nat.mod_self, hs0, hsk]
    dsimp only
    rw [hnxt]
    exact (hin5 i).2
  · rintro ⟨s, in5, h⟩
    refine ⟨s ⟨0, hk⟩, fun n => if hn : n < k then s ⟨n, hn⟩ else s ⟨0, hk⟩, ?_, ?_, ?_⟩
    · simp [hk]
    · simp
    · intro j _ hj
      refine ⟨hj, in5 ⟨j, hj⟩, (h ⟨j, hj⟩).1, ?_⟩
      have heq1 : (if hj' : j < k then s ⟨j, hj'⟩ else s ⟨0, hk⟩) = s ⟨j, hj⟩ := by simp [hj]
      have heq2 : (if hj' : j + 1 < k then s ⟨j + 1, hj'⟩ else s ⟨0, hk⟩) =
          s (nextIdx hk ⟨j, hj⟩) := by
        dsimp only [nextIdx]
        by_cases h1 : j + 1 < k
        · simp [h1, Nat.mod_eq_of_lt h1]
        · have hik : j + 1 = k := by omega
          simp [hik]
      dsimp only
      rw [heq1, heq2]
      exact (h ⟨j, hj⟩).2

private def availOfV {k : ℕ} (v : (Fin 5 × Fin k) → Bool) : Fin k → In5 → Prop :=
  fun i in5 => ∀ t : Fin 5, in5 t = v (t, i)

private def availOfRho {k : ℕ} (ρ : (Fin 5 × Fin k) → Option Bool) : Fin k → In5 → Prop :=
  fun i in5 => ∀ (t : Fin 5) (sgn : Bool), ρ (t, i) = some sgn → in5 t = sgn

private noncomputable def mkAux {k r : ℕ} (tree : SegTree k) (v : (Fin 5 × Fin k) → Bool) :
    AuxVar k r → Bool :=
  letI := Classical.propDecidable
  let av := availOfV v
  fun x => match x with
  | .falseVar => false
  | .matchVar i in5 => decide (∀ t : Fin 5, v (t, i) = in5 t)
  | .matchA01 i in5 => decide (v (0, i) = in5 0 ∧ v (1, i) = in5 1)
  | .matchA23 i in5 => decide (v (2, i) = in5 2 ∧ v (3, i) = in5 3)
  | .matchA0123 i in5 =>
    decide (v (0, i) = in5 0 ∧ v (1, i) = in5 1 ∧ v (2, i) = in5 2 ∧ v (3, i) = in5 3)
  | .forceGate i t sign g =>
    orGateEval (fun f => decide (∀ u : Fin 5, v (u, i) = ins4 t (!sign) f u)) g
  | .inLeaf i a b g =>
    orGateEval (fun in5 => LeafOK i in5 a b && decide (∀ t : Fin 5, v (t, i) = in5 t)) g
  | .inNode mid a c g =>
    let lh := lookupMid tree mid
    orGateEval (fun f =>
      let b := (equivStateVec r).symm f
      decide (PathExists av lh.1 mid.val a b ∧ PathExists av mid.val lh.2 b c)) g
  | .triIn mid a b c =>
    let lh := lookupMid tree mid
    decide (PathExists av lh.1 mid.val a b ∧ PathExists av mid.val lh.2 b c)
  | .rootOK g =>
    orGateEval (fun f =>
      let a := (equivStateVec r).symm f
      decide (PathExists av 0 k a a)) g
  | .outRoot a b => decide (a = b)
  | .outLeft mid a b g =>
    let lh := lookupMid tree mid
    orGateEval (fun f =>
      let c := (equivStateVec r).symm f
      decide (PathExists av mid.val lh.2 b c ∧ OutPath av lh.1 lh.2 a c)) g
  | .triOutL mid a b c =>
    let lh := lookupMid tree mid
    decide (PathExists av mid.val lh.2 b c ∧ OutPath av lh.1 lh.2 a c)
  | .outRight mid b c g =>
    let lh := lookupMid tree mid
    orGateEval (fun f =>
      let a := (equivStateVec r).symm f
      decide (PathExists av lh.1 mid.val a b ∧ OutPath av lh.1 lh.2 a c)) g
  | .triOutR mid a b c =>
    let lh := lookupMid tree mid
    decide (PathExists av lh.1 mid.val a b ∧ OutPath av lh.1 lh.2 a c)
  | .bothLeaf i a b =>
    decide (PathExists av i.val (i.val + 1) a b ∧ OutPath av i.val (i.val + 1) a b)
  | .matchToBoth i in5 g =>
    orGateEval (fun f =>
      match mkPair i in5 ((equivStateVec r).symm f) with
      | none => false
      | some (a, b) => decide (PathExists av i.val (i.val + 1) a b ∧ OutPath av i.val (i.val + 1) a b)) g

private theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private theorem PathExists_of_cycle_seg {k r : ℕ} (hk : 0 < k)
    (avail : Fin k → In5 → Prop) (s : Fin k → State r) (in5 : Fin k → In5)
    (hcyc : ∀ i : Fin k, avail i (in5 i) ∧ LeafOK i (in5 i) (s i) (s (nextIdx hk i)) = true)
    {lo hi : ℕ} (_hlh : lo ≤ hi) (hhk : hi ≤ k) :
    PathExists avail lo hi (if h : lo < k then s ⟨lo, h⟩ else s ⟨0, hk⟩)
      (if h : hi < k then s ⟨hi, h⟩ else s ⟨0, hk⟩) := by
  refine ⟨fun n => if hn : n < k then s ⟨n, hn⟩ else s ⟨0, hk⟩, rfl, rfl, fun j _ hj => ?_⟩
  have hjk : j < k := lt_of_lt_of_le hj hhk
  refine ⟨hjk, in5 ⟨j, hjk⟩, (hcyc ⟨j, hjk⟩).1, ?_⟩
  have heq1 : (if h : j < k then s ⟨j, h⟩ else s ⟨0, hk⟩) = s ⟨j, hjk⟩ := by simp [hjk]
  have heq2 : (if h : j + 1 < k then s ⟨j + 1, h⟩ else s ⟨0, hk⟩) = s (nextIdx hk ⟨j, hjk⟩) := by
    dsimp only [nextIdx]
    by_cases h1 : j + 1 < k
    · simp [h1, Nat.mod_eq_of_lt h1]
    · have hik : j + 1 = k := by omega
      simp [hik]
  dsimp only
  rw [heq1, heq2]
  exact (hcyc ⟨j, hjk⟩).2

private theorem decide_eq_true_any {p : Prop} {inst : Decidable p} :
    @decide p inst = true ↔ p := iff_of_eq (@decide_eq_true_eq p inst)

private theorem decide_eq_true_of_any {p : Prop} {inst : Decidable p} (h : p) :
    @decide p inst = true := @decide_eq_true p inst h

private theorem decide_eq_false_any {p : Prop} {inst : Decidable p} (h : ¬p) :
    @decide p inst = false := @decide_eq_false p inst h

private theorem mkAux_inOutVar {k r : ℕ} (tree : SegTree k) (v : (Fin 5 × Fin k) → Bool)
    (t : SegTree k) {lo hi : ℕ} (hv : SegValid k t lo hi)
    (hm : ∀ l m h, t.hasMid l m h → tree.hasMid l m h)
    (htree : SegValid k tree 0 k) (a b : State r) :
    Sum.elim v (mkAux tree v) (inOutVar t a b) = true ↔ PathExists (availOfV v) lo hi a b := by
  cases t with
  | leaf i =>
    rcases hv with ⟨rfl, rfl⟩
    dsimp only [inOutVar, Sum.elim_inr, mkAux, orGateEval]
    rw [decide_eq_true_any, PathExists_step (availOfV v) i.isLt a b]
    constructor
    · rintro ⟨in5, h⟩
      simp only [Bool.and_eq_true, decide_eq_true_any] at h
      exact ⟨in5, fun u => (h.2 u).symm, h.1⟩
    · rintro ⟨in5, hav, hok⟩
      refine ⟨in5, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_any]
      exact ⟨hok, fun u => (hav u).symm⟩
  | node lo' mid hi' _ _ =>
    rcases hv with ⟨rfl, rfl, hlm, hmh, _, _⟩
    have hm_here : tree.hasMid lo' mid hi' := hm lo' mid hi' (Or.inl ⟨rfl, rfl, rfl⟩)
    have hlook : lookupMid tree mid = (lo', hi') := lookupMid_of_hasMid htree hm_here
    dsimp only [inOutVar, Sum.elim_inr, mkAux, orGateEval]
    rw [hlook]
    dsimp only
    rw [decide_eq_true_any, PathExists_split (availOfV v) (le_of_lt hlm) (le_of_lt hmh)]
    constructor
    · rintro ⟨f, hf⟩
      rw [decide_eq_true_any] at hf
      exact ⟨(equivStateVec r).symm f, hf⟩
    · rintro ⟨m, hm1, hm2⟩
      refine ⟨equivStateVec r m, ?_⟩
      rw [decide_eq_true_any]
      simpa using And.intro hm1 hm2

private theorem mkAux_cInTree {k r : ℕ} (tree : SegTree k) (v : (Fin 5 × Fin k) → Bool)
    (htree : SegValid k tree 0 k) (t : SegTree k) {lo hi : ℕ} (hv : SegValid k t lo hi)
    (hm : ∀ l m h, t.hasMid l m h → tree.hasMid l m h) :
    ∀ C ∈ (cInTree t : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v (mkAux tree v)) C := by
  induction t generalizing lo hi with
  | leaf _ => intro C hC; simp [cInTree] at hC
  | node lo' mid hi' L R ihL ihR =>
    intro C hC
    rcases hv with ⟨rfl, rfl, _, _, hvL, hvR⟩
    have hm_here : tree.hasMid lo' mid hi' := hm lo' mid hi' (Or.inl ⟨rfl, rfl, rfl⟩)
    have hlook : lookupMid tree mid = (lo', hi') := lookupMid_of_hasMid htree hm_here
    have hmL : ∀ l m h, L.hasMid l m h → tree.hasMid l m h :=
      fun l m h hx => hm l m h (Or.inr (Or.inl hx))
    have hmR : ∀ l m h, R.hasMid l m h → tree.hasMid l m h :=
      fun l m h hx => hm l m h (Or.inr (Or.inr hx))
    simp only [cInTree, Finset.mem_union] at hC
    rcases hC with (hhere | hL) | hR
    · rw [Finset.mem_biUnion] at hhere
      rcases hhere with ⟨⟨a, c⟩, _, hmem⟩
      rw [Finset.mem_union] at hmem
      rcases hmem with htri | hor
      · rw [Finset.mem_biUnion] at htri
        rcases htri with ⟨b, _, hca⟩
        refine clauseAnd2_sat ?_ C hca
        apply bool_eq_of_iff
        rw [Bool.and_eq_true, mkAux_inOutVar tree v L hvL hmL htree a b,
          mkAux_inOutVar tree v R hvR hmR htree b c]
        change (@decide _ (Classical.propDecidable _) = true) ↔ _
        rw [hlook]
        dsimp only
        rw [decide_eq_true_any]
      · refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
          (fun g => Sum.inr (AuxVar.inNode mid a c g))
          (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) c))
          (let lh := lookupMid tree mid
           fun f => @decide (PathExists (availOfV v) lh.1 mid.val a ((equivStateVec r).symm f) ∧
             PathExists (availOfV v) mid.val lh.2 ((equivStateVec r).symm f) c) (Classical.propDecidable _))
          (fun _ => rfl) (fun _ => rfl) C hor
    · exact ihL hvL hmL C hL
    · exact ihR hvR hmR C hR

private theorem mkAux_cOutTree {k r : ℕ} (tree : SegTree k) (v : (Fin 5 × Fin k) → Bool)
    (htree : SegValid k tree 0 k) (t : SegTree k) {lo hi : ℕ} (hv : SegValid k t lo hi)
    (hhk : hi ≤ k) (hm : ∀ l m h, t.hasMid l m h → tree.hasMid l m h)
    (p : State r → State r → AuxVar k r)
    (hp : ∀ a b, Sum.elim v (mkAux tree v) (Sum.inr (p a b)) = true ↔ OutPath (availOfV v) lo hi a b) :
    ∀ C ∈ (cOutTree t p : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v (mkAux tree v)) C := by
  induction t generalizing lo hi p with
  | leaf i =>
    intro C hC
    rcases hv with ⟨rfl, rfl⟩
    rw [cOutTree, Finset.mem_biUnion] at hC
    rcases hC with ⟨⟨a, b⟩, _, hca⟩
    refine clauseAnd2_sat ?_ C hca
    apply bool_eq_of_iff
    rw [Bool.and_eq_true, mkAux_inOutVar tree v (.leaf i) ⟨rfl, rfl⟩ hm htree a b, hp a b]
    change (@decide _ (Classical.propDecidable _) = true) ↔ _
    rw [decide_eq_true_any]
  | node lo' mid hi' L R ihL ihR =>
    intro C hC
    rcases hv with ⟨rfl, rfl, hlm, hmh, hvL, hvR⟩
    have hm_here : tree.hasMid lo' mid hi' := hm lo' mid hi' (Or.inl ⟨rfl, rfl, rfl⟩)
    have hlook : lookupMid tree mid = (lo', hi') := lookupMid_of_hasMid htree hm_here
    have hmL : ∀ l m h, L.hasMid l m h → tree.hasMid l m h :=
      fun l m h hx => hm l m h (Or.inr (Or.inl hx))
    have hmR : ∀ l m h, R.hasMid l m h → tree.hasMid l m h :=
      fun l m h hx => hm l m h (Or.inr (Or.inr hx))
    simp only [cOutTree, Finset.mem_union] at hC
    rcases hC with ((hhereL | hhereR) | hL) | hR
    · rw [Finset.mem_biUnion] at hhereL
      rcases hhereL with ⟨⟨a, b⟩, _, hmem⟩
      rw [Finset.mem_union] at hmem
      rcases hmem with htri | hor
      · rw [Finset.mem_biUnion] at htri
        rcases htri with ⟨c, _, hca⟩
        refine clauseAnd2_sat ?_ C hca
        apply bool_eq_of_iff
        rw [Bool.and_eq_true, mkAux_inOutVar tree v R hvR hmR htree b c, hp a c, and_comm]
        change (@decide _ (Classical.propDecidable _) = true) ↔ _
        rw [hlook]
        dsimp only
        rw [decide_eq_true_any]
      · refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
          (fun g => Sum.inr (AuxVar.outLeft mid a b g))
          (fun f => Sum.inr (AuxVar.triOutL mid a b ((equivStateVec r).symm f)))
          (let lh := lookupMid tree mid
           fun f => @decide (PathExists (availOfV v) mid.val lh.2 b ((equivStateVec r).symm f) ∧
             OutPath (availOfV v) lh.1 lh.2 a ((equivStateVec r).symm f)) (Classical.propDecidable _))
          (fun _ => rfl) (fun _ => rfl) C hor
    · rw [Finset.mem_biUnion] at hhereR
      rcases hhereR with ⟨⟨b, c⟩, _, hmem⟩
      rw [Finset.mem_union] at hmem
      rcases hmem with htri | hor
      · rw [Finset.mem_biUnion] at htri
        rcases htri with ⟨a, _, hca⟩
        refine clauseAnd2_sat ?_ C hca
        apply bool_eq_of_iff
        rw [Bool.and_eq_true, mkAux_inOutVar tree v L hvL hmL htree a b, hp a c, and_comm]
        change (@decide _ (Classical.propDecidable _) = true) ↔ _
        rw [hlook]
        dsimp only
        rw [decide_eq_true_any]
      · refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
          (fun g => Sum.inr (AuxVar.outRight mid b c g))
          (fun f => Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) b c))
          (let lh := lookupMid tree mid
           fun f => @decide (PathExists (availOfV v) lh.1 mid.val ((equivStateVec r).symm f) b ∧
             OutPath (availOfV v) lh.1 lh.2 ((equivStateVec r).symm f) c) (Classical.propDecidable _))
          (fun _ => rfl) (fun _ => rfl) C hor
    · refine ihL hvL (le_of_lt mid.isLt) hmL (fun a b => AuxVar.outLeft mid a b (Sum.inl ())) ?_ C hL
      intro a b
      dsimp only [Sum.elim_inr, mkAux, orGateEval]
      rw [hlook]
      dsimp only
      rw [decide_eq_true_any, OutPath_split_L (availOfV v) (Nat.zero_le _) (le_of_lt hlm) (le_of_lt hmh) hhk a b]
      constructor
      · rintro ⟨f, hf⟩
        rw [decide_eq_true_any] at hf
        exact ⟨(equivStateVec r).symm f, hf⟩
      · rintro ⟨c, hc1, hc2⟩
        refine ⟨equivStateVec r c, ?_⟩
        rw [decide_eq_true_any]
        simpa using And.intro hc1 hc2
    · refine ihR hvR hhk hmR (fun b c => AuxVar.outRight mid b c (Sum.inl ())) ?_ C hR
      intro b c
      dsimp only [Sum.elim_inr, mkAux, orGateEval]
      rw [hlook]
      dsimp only
      rw [decide_eq_true_any, OutPath_split_R (availOfV v) (Nat.zero_le _) (le_of_lt hlm) (le_of_lt hmh) hhk b c]
      constructor
      · rintro ⟨f, hf⟩
        rw [decide_eq_true_any] at hf
        exact ⟨(equivStateVec r).symm f, hf⟩
      · rintro ⟨a, ha1, ha2⟩
        refine ⟨equivStateVec r a, ?_⟩
        rw [decide_eq_true_any]
        simpa using And.intro ha1 ha2

private theorem mkAux_satisfies_F_aux {k r : ℕ} (hk : 0 < k) (v : (Fin 5 × Fin k) → Bool)
    (hag : wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
      wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r) :
    let tree := buildSeg k 0 k hk (Nat.zero_add k).le
    Satisfies (Sum.elim v (mkAux (r := r) tree v))
      (↑(F_aux (r := r) tree : Finset (Clause (VarSum k r))) : Set _) := by
  intro tree
  have htree : SegValid k tree 0 k := by simpa [tree] using buildSeg_valid k 0 k hk (Nat.zero_add k).le
  obtain ⟨states, hcyc⟩ := agrees_implies_cycle hk v hag
  have hcyc_av : ∀ i : Fin k, availOfV v i (fun t => v (t, i)) ∧
      LeafOK i (fun t => v (t, i)) (states i) (states (nextIdx hk i)) = true :=
    fun i => ⟨fun _ => rfl, hcyc i⟩
  intro C hCF
  rw [Finset.mem_coe] at hCF
  simp only [F_aux, Finset.mem_union, Finset.mem_singleton] at hCF
  rcases hCF with ((((((((rfl | hMatch) | hForce) | hInLeaf) | hInTree) | hRootOK) | hOutRoot) | hOutTree) | hMTB)
  · exact ⟨(Sum.inr AuxVar.falseVar, false), Finset.mem_singleton_self _, rfl⟩
  · simp only [cMatch, Finset.mem_biUnion, Finset.mem_univ, true_and, cMatchOne, Finset.mem_union,
      Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hMatch
    rcases hMatch with ⟨⟨i, in5⟩, ⟨t, _, rfl⟩ | rfl | rfl | rfl | rfl⟩
    · by_cases h : ∀ u : Fin 5, v (u, i) = in5 u
      · exact ⟨(Sum.inl (t, i), in5 t), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h t⟩
      · refine ⟨(Sum.inr (AuxVar.matchVar i in5), false), Finset.mem_insert_self _ _, ?_⟩
        dsimp only [Sum.elim_inr, mkAux]
        exact decide_eq_false_any h
    · by_cases h0 : v (0, i) = in5 0
      · by_cases h1 : v (1, i) = in5 1
        · refine ⟨(Sum.inr (AuxVar.matchA01 i in5), true),
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
          dsimp only [Sum.elim_inr, mkAux]
          exact decide_eq_true_of_any ⟨h0, h1⟩
        · exact ⟨(Sum.inl (1, i), !(in5 1)), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by
            cases hv1 : v (1, i) <;> cases hi1 : in5 1 <;> simp_all⟩
      · exact ⟨(Sum.inl (0, i), !(in5 0)), Finset.mem_insert_self _ _, by
          cases hv0 : v (0, i) <;> cases hi0 : in5 0 <;> simp_all⟩
    · by_cases h2 : v (2, i) = in5 2
      · by_cases h3 : v (3, i) = in5 3
        · refine ⟨(Sum.inr (AuxVar.matchA23 i in5), true),
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
          dsimp only [Sum.elim_inr, mkAux]
          exact decide_eq_true_of_any ⟨h2, h3⟩
        · exact ⟨(Sum.inl (3, i), !(in5 3)), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by
            cases hv3 : v (3, i) <;> cases hi3 : in5 3 <;> simp_all⟩
      · exact ⟨(Sum.inl (2, i), !(in5 2)), Finset.mem_insert_self _ _, by
          cases hv2 : v (2, i) <;> cases hi2 : in5 2 <;> simp_all⟩
    · by_cases h01 : v (0, i) = in5 0 ∧ v (1, i) = in5 1
      · by_cases h23 : v (2, i) = in5 2 ∧ v (3, i) = in5 3
        · refine ⟨(Sum.inr (AuxVar.matchA0123 i in5), true),
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
          dsimp only [Sum.elim_inr, mkAux]
          exact decide_eq_true_of_any ⟨h01.1, h01.2, h23.1, h23.2⟩
        · refine ⟨(Sum.inr (AuxVar.matchA23 i in5), false),
            Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
          dsimp only [Sum.elim_inr, mkAux]
          exact decide_eq_false_any h23
      · refine ⟨(Sum.inr (AuxVar.matchA01 i in5), false), Finset.mem_insert_self _ _, ?_⟩
        dsimp only [Sum.elim_inr, mkAux]
        exact decide_eq_false_any h01
    · by_cases h0123 : v (0, i) = in5 0 ∧ v (1, i) = in5 1 ∧ v (2, i) = in5 2 ∧ v (3, i) = in5 3
      · by_cases h4 : v (4, i) = in5 4
        · refine ⟨(Sum.inr (AuxVar.matchVar i in5), true),
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), ?_⟩
          dsimp only [Sum.elim_inr, mkAux]
          refine decide_eq_true_of_any fun u => ?_
          fin_cases u <;> simp [h0123.1, h0123.2.1, h0123.2.2.1, h0123.2.2.2, h4]
        · exact ⟨(Sum.inl (4, i), !(in5 4)), Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), by
            cases hv4 : v (4, i) <;> cases hi4 : in5 4 <;> simp_all⟩
      · refine ⟨(Sum.inr (AuxVar.matchA0123 i in5), false), Finset.mem_insert_self _ _, ?_⟩
        dsimp only [Sum.elim_inr, mkAux]
        exact decide_eq_false_any h0123
  · simp only [cForce, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton] at hForce
    rcases hForce with ⟨⟨i, t, sign⟩, hor | rfl⟩
    · refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
        (fun g => Sum.inr (AuxVar.forceGate i t sign g))
        (fun g => Sum.inr (AuxVar.matchVar i (ins4 t (!sign) g)))
        (fun g => @decide (∀ u : Fin 5, v (u, i) = ins4 t (!sign) g u) (Classical.propDecidable _))
        (fun _ => rfl) (fun _ => rfl) C hor
    · by_cases hv : v (t, i) = sign
      · exact ⟨(Sum.inl (t, i), sign), Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hv⟩
      · have hv_neg : v (t, i) = !sign := by cases hvi : v (t, i) <;> cases sign <;> simp_all
        obtain ⟨g, hg⟩ := ins4_surj (in5 := fun u => v (u, i)) hv_neg
        refine ⟨(Sum.inr (AuxVar.forceGate i t sign (Sum.inl ())), true),
          Finset.mem_insert_self _ _, ?_⟩
        dsimp only [Sum.elim_inr, mkAux, orGateEval]
        rw [decide_eq_true_any]
        exact ⟨g, by rw [decide_eq_true_any]; intro u; exact (congrFun hg u).symm⟩
  · simp only [cInLeaf, Finset.mem_biUnion, Finset.mem_univ, true_and] at hInLeaf
    rcases hInLeaf with ⟨⟨i, a, b⟩, hor⟩
    refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
      (fun g => Sum.inr (AuxVar.inLeaf i a b g))
      (fun in5 => if LeafOK i in5 a b then Sum.inr (AuxVar.matchVar i in5) else Sum.inr AuxVar.falseVar)
      (fun in5 => LeafOK i in5 a b && @decide (∀ t : Fin 5, v (t, i) = in5 t) (Classical.propDecidable _))
      (fun _ => rfl)
      (fun in5 => by cases hok : LeafOK i in5 a b <;> simp [mkAux])
      C hor
  · exact mkAux_cInTree tree v htree tree htree (fun _ _ _ h => h) C hInTree
  · simp only [cRootOK, Finset.mem_union, Finset.mem_singleton] at hRootOK
    rcases hRootOK with hor | rfl
    · refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
        (fun g => Sum.inr (AuxVar.rootOK g))
        (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a)
        (fun f => let a := (equivStateVec r).symm f; @decide (PathExists (availOfV v) 0 k a a) (Classical.propDecidable _))
        (fun _ => rfl)
        (fun f => bool_eq_of_iff (by
          dsimp only
          rw [decide_eq_true_any]
          exact mkAux_inOutVar tree v tree htree (fun _ _ _ h => h) htree _ _))
        C hor
    · refine ⟨(Sum.inr (AuxVar.rootOK (Sum.inl ())), true), Finset.mem_singleton_self _, ?_⟩
      dsimp only [Sum.elim_inr, mkAux, orGateEval]
      rw [decide_eq_true_any]
      obtain ⟨a, ha⟩ := (PathExists_cycle_iff hk (availOfV v)).mpr ⟨states, fun i t => v (t, i), hcyc_av⟩
      refine ⟨equivStateVec r a, ?_⟩
      rw [decide_eq_true_any]
      simpa using ha
  · simp only [cOutRoot, Finset.mem_image, Finset.mem_univ, true_and] at hOutRoot
    rcases hOutRoot with ⟨⟨a, b⟩, rfl⟩
    refine ⟨(Sum.inr (AuxVar.outRoot a b), decide (a = b)), Finset.mem_singleton_self _,
      bool_eq_of_iff ?_⟩
    dsimp only [Sum.elim_inr, mkAux]
    rw [decide_eq_true_any, decide_eq_true_any]
  · refine mkAux_cOutTree tree v htree tree htree le_rfl (fun _ _ _ h => h) AuxVar.outRoot ?_ C hOutTree
    intro a b
    dsimp only [Sum.elim_inr, mkAux]
    rw [decide_eq_true_any, OutPath_root]
  · simp only [cMatchToBoth, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton] at hMTB
    rcases hMTB with ⟨⟨i, in5⟩, hor | rfl⟩
    · refine orGateEval_satisfies_orClauses (Sum.elim v (mkAux tree v))
        (fun g => Sum.inr (AuxVar.matchToBoth i in5 g))
        (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
          | none => Sum.inr AuxVar.falseVar
          | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b))
        (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
          | none => false
          | some (a, b) => @decide (PathExists (availOfV v) i.val (i.val + 1) a b ∧
              OutPath (availOfV v) i.val (i.val + 1) a b) (Classical.propDecidable _))
        (fun _ => rfl)
        (fun f => by
          cases hmp : mkPair i in5 ((equivStateVec r).symm f) with
          | none => rfl
          | some ab => rfl)
        C hor
    · by_cases hm : ∀ u : Fin 5, v (u, i) = in5 u
      · have hin5_eq : in5 = fun u => v (u, i) := funext fun u => (hm u).symm
        have hok : LeafOK i in5 (states i) (states (nextIdx hk i)) = true := by
          rw [hin5_eq]; exact hcyc i
        obtain ⟨free, hfree⟩ := exists_mkPair_of_LeafOK hok
        have hpe : PathExists (availOfV v) i.val (i.val + 1) (states i) (states (nextIdx hk i)) :=
          (PathExists_step (availOfV v) i.isLt _ _).mpr ⟨in5, fun u => (hm u).symm, hok⟩
        have hop1 : PathExists (availOfV v) 0 i.val (states ⟨0, hk⟩) (states i) := by
          have hs := PathExists_of_cycle_seg hk (availOfV v) states _ hcyc_av (Nat.zero_le _) (le_of_lt i.isLt)
          simpa [hk, i.isLt] using hs
        have hop2 : PathExists (availOfV v) (i.val + 1) k (states (nextIdx hk i)) (states ⟨0, hk⟩) := by
          have hs := PathExists_of_cycle_seg hk (availOfV v) states _ hcyc_av (Nat.succ_le_of_lt i.isLt) le_rfl
          have heq1 : (if h : i.val + 1 < k then states ⟨i.val + 1, h⟩ else states ⟨0, hk⟩) =
              states (nextIdx hk i) := by
            dsimp only [nextIdx]
            by_cases h1 : i.val + 1 < k
            · simp [h1, Nat.mod_eq_of_lt h1]
            · have hik : i.val + 1 = k := by have := i.isLt; omega
              simp [hik]
          have heq2 : (if h : k < k then states ⟨k, h⟩ else states ⟨0, hk⟩) = states ⟨0, hk⟩ := by
            simp
          rw [heq1, heq2] at hs
          exact hs
        refine ⟨(Sum.inr (AuxVar.matchToBoth i in5 (Sum.inl ())), true),
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩
        dsimp only [Sum.elim_inr, mkAux, orGateEval]
        rw [decide_eq_true_any]
        refine ⟨equivStateVec r free, ?_⟩
        rw [Equiv.symm_apply_apply, hfree]
        dsimp only
        rw [decide_eq_true_any]
        exact ⟨hpe, ⟨states ⟨0, hk⟩, hop1, hop2⟩⟩
      · refine ⟨(Sum.inr (AuxVar.matchVar i in5), false), Finset.mem_insert_self _ _, ?_⟩
        dsimp only [Sum.elim_inr, mkAux]
        exact decide_eq_false_any hm

private theorem orClauses_sound_true {α : Type} [DecidableEq α] {n : ℕ}
    {assign : α → Bool} (base : OrGate n → α) (leaf : (Fin n → Bool) → α)
    (hF : ∀ C ∈ orClauses base leaf, ClauseSat assign C)
    (hout : assign (orOut base leaf) = true) :
    ∃ f : Fin n → Bool, assign (leaf f) = true := by
  induction n with
  | zero => exact ⟨Fin.elim0, hout⟩
  | @succ n ih =>
    dsimp only [orOut] at hout
    have hcl : ClauseSat assign
        ({(base (Sum.inl ()), false),
          (orOut (fun x => base (Sum.inr (Sum.inl x))) (fun f => leaf (Fin.cons false f)), true),
          (orOut (fun x => base (Sum.inr (Sum.inr x))) (fun f => leaf (Fin.cons true f)), true)} : Clause α) :=
      hF _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _)))
    rcases hcl with ⟨l, hl, hla⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · simp [hout] at hla
    · have hF_L : ∀ C ∈ orClauses (fun x => base (Sum.inr (Sum.inl x))) (fun f => leaf (Fin.cons false f)),
          ClauseSat assign C := fun C hC => hF C (Finset.mem_union_left _ (Finset.mem_union_right _ hC))
      obtain ⟨f, hf⟩ := ih _ _ hF_L hla
      exact ⟨Fin.cons false f, hf⟩
    · have hF_R : ∀ C ∈ orClauses (fun x => base (Sum.inr (Sum.inr x))) (fun f => leaf (Fin.cons true f)),
          ClauseSat assign C := fun C hC => hF C (Finset.mem_union_right _ hC)
      obtain ⟨f, hf⟩ := ih _ _ hF_R hla
      exact ⟨Fin.cons true f, hf⟩

private theorem clauseAnd2_sound {α : Type} [DecidableEq α] {assign : α → Bool} {out a b : α}
    (hF : ∀ C ∈ clauseAnd2 out a b, ClauseSat assign C) (hout : assign out = true) :
    assign a = true ∧ assign b = true := by
  have h1 := hF _ (Finset.mem_insert_self _ _)
  have h2 := hF _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  constructor
  · rcases h1 with ⟨l, hl, hla⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hout] at hla
    · exact hla
  · rcases h2 with ⟨l, hl, hla⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp [hout] at hla
    · exact hla

private theorem matchVar_sound {k r : ℕ} {v : (Fin 5 × Fin k) → Bool} {aux : AuxVar k r → Bool}
    (hMatch : ∀ C ∈ (cMatch : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C)
    {i : Fin k} {in5 : In5} (hmv : aux (AuxVar.matchVar i in5) = true) :
    availOfV v i in5 := by
  intro t
  have hcl : ClauseSat (Sum.elim v aux)
      ({(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inl (t, i), in5 t)} : Clause (VarSum k r)) := by
    refine hMatch _ (Finset.mem_biUnion.mpr ⟨(i, in5), Finset.mem_univ _, ?_⟩)
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rcases hcl with ⟨l, hl, hla⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · dsimp only [Sum.elim_inr] at hla
    rw [hmv] at hla
    exact absurd hla (by decide)
  · exact hla.symm

private theorem inOut_sound_true {k r : ℕ} {v : (Fin 5 × Fin k) → Bool} {aux : AuxVar k r → Bool}
    (hfalse : aux AuxVar.falseVar = false)
    (hMatch : ∀ C ∈ (cMatch : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C)
    (hLeaf : ∀ C ∈ (cInLeaf : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C)
    (t : SegTree k) {lo hi : ℕ} (hv : SegValid k t lo hi)
    (hTree : ∀ C ∈ (cInTree t : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C)
    {a b : State r} (hin : Sum.elim v aux (inOutVar t a b) = true) :
    PathExists (availOfV v) lo hi a b := by
  induction t generalizing lo hi a b with
  | leaf i =>
    rcases hv with ⟨rfl, rfl⟩
    have hL : ∀ C ∈ orClauses (fun g => Sum.inr (AuxVar.inLeaf i a b g))
        (fun in5 => if LeafOK i in5 a b then Sum.inr (AuxVar.matchVar i in5) else Sum.inr AuxVar.falseVar),
        ClauseSat (Sum.elim v aux) C := fun C hC =>
      hLeaf C (Finset.mem_biUnion.mpr ⟨(i, a, b), Finset.mem_univ _, hC⟩)
    obtain ⟨in5, hin5⟩ := orClauses_sound_true _ _ hL hin
    by_cases hok : LeafOK i in5 a b = true
    · simp only [hok, ↓reduceIte, Sum.elim_inr] at hin5
      exact (PathExists_step (availOfV v) i.isLt a b).mpr
        ⟨in5, matchVar_sound hMatch hin5, hok⟩
    · have hokf : LeafOK i in5 a b = false := Bool.eq_false_iff.mpr hok
      simp only [hokf, Bool.false_eq_true, ↓reduceIte, Sum.elim_inr] at hin5
      rw [hfalse] at hin5
      exact absurd hin5 (by decide)
  | node lo' mid hi' L R ihL ihR =>
    rcases hv with ⟨rfl, rfl, hlm, hmh, hvL, hvR⟩
    have hT : ∀ C ∈ orClauses (fun g => Sum.inr (AuxVar.inNode mid a b g))
        (fun f => Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) b)),
        ClauseSat (Sum.elim v aux) C := fun C hC => by
      refine hTree C (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
      refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finset.mem_union_right _ hC⟩
    obtain ⟨f, hf⟩ := orClauses_sound_true _ _ hT hin
    set m := (equivStateVec r).symm f
    have hAnd : ∀ C ∈ clauseAnd2 (Sum.inr (AuxVar.triIn mid a m b)) (inOutVar L a m) (inOutVar R m b),
        ClauseSat (Sum.elim v aux) C := fun C hC => by
      refine hTree C (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
      refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finset.mem_union_left _ ?_⟩
      exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, hC⟩
    obtain ⟨h1, h2⟩ := clauseAnd2_sound hAnd hf
    have hTL : ∀ C ∈ (cInTree L : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
      fun C hC => hTree C (Finset.mem_union_left _ (Finset.mem_union_right _ hC))
    have hTR : ∀ C ∈ (cInTree R : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
      fun C hC => hTree C (Finset.mem_union_right _ hC)
    exact (PathExists_split (availOfV v) (le_of_lt hlm) (le_of_lt hmh) a b).mpr
      ⟨m, ihL hvL hTL h1, ihR hvR hTR h2⟩

private theorem satisfies_F_aux_implies_agrees {k r : ℕ} (hk : 0 < k)
    (v : (Fin 5 × Fin k) → Bool) (aux : AuxVar k r → Bool)
    (hsat : Satisfies (Sum.elim v aux) (↑(F_aux (r := r) (buildSeg k 0 k hk (Nat.zero_add k).le) : Finset (Clause (VarSum k r))) : Set _)) :
    wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
    wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r := by
  let tree := buildSeg k 0 k hk (Nat.zero_add k).le
  have hmem : ∀ C ∈ (F_aux tree : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
    fun C hC => hsat C (Finset.mem_coe.mpr hC)
  have hfalse : aux AuxVar.falseVar = false := by
    have hcl := hmem ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) (by simp [F_aux])
    rcases hcl with ⟨l, hl, hla⟩
    rw [Finset.mem_singleton] at hl
    subst hl
    exact hla
  have hMatch : ∀ C ∈ (cMatch : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
    fun C hC => hmem C (by simp [F_aux, hC])
  have hLeaf : ∀ C ∈ (cInLeaf : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
    fun C hC => hmem C (by simp [F_aux, hC])
  have hTree : ∀ C ∈ (cInTree tree : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
    fun C hC => hmem C (by simp [F_aux, hC])
  have hRoot : ∀ C ∈ (cRootOK tree : Finset (Clause (VarSum k r))), ClauseSat (Sum.elim v aux) C :=
    fun C hC => hmem C (by simp [F_aux, hC])
  have hunit : aux (AuxVar.rootOK (Sum.inl ())) = true := by
    have hcl := hRoot _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    rcases hcl with ⟨l, hl, hla⟩
    rw [Finset.mem_singleton] at hl
    subst hl
    exact hla
  have hRootOr : ∀ C ∈ orClauses (fun g => Sum.inr (AuxVar.rootOK g))
      (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a),
      ClauseSat (Sum.elim v aux) C := fun C hC => hRoot C (Finset.mem_union_left _ hC)
  obtain ⟨f, hf⟩ := orClauses_sound_true _ _ hRootOr hunit
  have htree : SegValid k tree 0 k := by simpa [tree] using buildSeg_valid k 0 k hk (Nat.zero_add k).le
  have hpe := inOut_sound_true hfalse hMatch hLeaf tree htree hTree hf
  obtain ⟨s, in5, hs⟩ := (PathExists_cycle_iff hk (availOfV v)).mp ⟨(equivStateVec r).symm f, hpe⟩
  refine cycle_implies_agrees hk v s fun i => ?_
  have heq : (fun t => v (t, i)) = in5 i := funext fun t => ((hs i).1 t).symm
  rw [heq]
  exact (hs i).2

private theorem satisfies_F_aux_iff {k r : ℕ} (hk : 0 < k) (v : (Fin 5 × Fin k) → Bool) :
    (wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
     wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r) ↔
    ∃ aux : AuxVar k r → Bool,
      Satisfies (Sum.elim v aux) (↑(F_aux (r := r) (buildSeg k 0 k hk (Nat.zero_add k).le) : Finset (Clause (VarSum k r))) : Set _) :=
  ⟨fun hag => ⟨mkAux (r := r) (buildSeg k 0 k hk (Nat.zero_add k).le) v, mkAux_satisfies_F_aux hk v hag⟩,
   fun ⟨aux, hsat⟩ => satisfies_F_aux_implies_agrees hk v aux hsat⟩

end TreeCNF

section UnitProp

open PEqualNP.ProofComplexity
open PEqualNP.Search

private def seedOfRho {k r : ℕ} (ρ : (Fin 5 × Fin k) → Option Bool) : Set (Literal (VarSum k r)) :=
  {l | ∃ raw : Fin 5 × Fin k, l.1 = Sum.inl raw ∧ ρ raw = some l.2}

private theorem up_falseVar {k r : ℕ} {F : Set (Clause (VarSum k r))}
    (hfalse : ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) ∈ F)
    (S : Set (Literal (VarSum k r))) :
    (Sum.inr AuxVar.falseVar, false) ∈ (stepUP F)^[1] S := by
  refine mem_stepUP_succ_of_clause hfalse (Finset.mem_singleton_self _) ?_
  intro other ho hne
  rw [Finset.mem_singleton] at ho
  exact absurd ho hne

private theorem up_matchVar_bad {k r : ℕ} {F : Set (Clause (VarSum k r))}
    (hMatch : ↑(cMatch : Finset (Clause (VarSum k r))) ⊆ F)
    (ρ : (Fin 5 × Fin k) → Option Bool) {i : Fin k} {in5 : In5}
    (hbad : ¬ availOfRho ρ i in5) :
    (Sum.inr (AuxVar.matchVar i in5), false) ∈ (stepUP F)^[1] (seedOfRho ρ) := by
  dsimp only [availOfRho] at hbad
  push Not at hbad
  obtain ⟨t, sgn, hρ, hne⟩ := hbad
  have hCF : ({(Sum.inr (AuxVar.matchVar i in5), false), (Sum.inl (t, i), in5 t)} : Clause (VarSum k r)) ∈ F := by
    refine hMatch (Finset.mem_coe.mpr ?_)
    refine Finset.mem_biUnion.mpr ⟨(i, in5), Finset.mem_univ _, ?_⟩
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  refine mem_stepUP_succ_of_clause hCF (Finset.mem_insert_self _ _) ?_
  intro other ho hne'
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl
  · exact absurd rfl hne'
  · refine ⟨(t, i), rfl, ?_⟩
    have hsgn : (!(in5 t)) = sgn := by cases h1 : in5 t <;> cases sgn <;> simp_all
    dsimp only [negLit]
    rw [hsgn]
    exact hρ

private theorem up_inLeaf {k r : ℕ} {F : Set (Clause (VarSum k r))}
    (hfalse : ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) ∈ F)
    (hMatch : ↑(cMatch : Finset (Clause (VarSum k r))) ⊆ F)
    (hLeaf : ↑(cInLeaf : Finset (Clause (VarSum k r))) ⊆ F)
    (ρ : (Fin 5 × Fin k) → Option Bool) {i : Fin k} {a b : State r}
    (hno : ¬ PathExists (availOfRho ρ) i.val (i.val + 1) a b) :
    (inOutVar (.leaf i) a b, false) ∈ (stepUP F)^[6] (seedOfRho ρ) := by
  have hsub : ↑(orClauses (fun g => (Sum.inr (AuxVar.inLeaf i a b g) : VarSum k r))
      (fun in5 => if LeafOK i in5 a b then (Sum.inr (AuxVar.matchVar i in5) : VarSum k r) else Sum.inr AuxVar.falseVar)) ⊆ F := by
    intro C hC
    rw [Finset.mem_coe] at hC
    exact hLeaf (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨(i, a, b), Finset.mem_univ _, hC⟩))
  have hleaves : ∀ in5 : In5,
      ((if LeafOK i in5 a b then Sum.inr (AuxVar.matchVar i in5) else Sum.inr AuxVar.falseVar), false) ∈
        (stepUP F)^[1] (seedOfRho ρ) := by
    intro in5
    by_cases hok : LeafOK i in5 a b = true
    · simp only [hok, ↓reduceIte]
      have hbad : ¬ availOfRho ρ i in5 := fun hav =>
        hno ((PathExists_step (availOfRho ρ) i.isLt a b).mpr ⟨in5, hav, hok⟩)
      exact up_matchVar_bad hMatch ρ hbad
    · have hokf : LeafOK i in5 a b = false := Bool.eq_false_iff.mpr hok
      simp only [hokf, Bool.false_eq_true, ↓reduceIte]
      exact up_falseVar hfalse (seedOfRho ρ)
  have hor := orClauses_prop_false _ _ hsub hleaves
  rw [← Function.iterate_add_apply] at hor
  simpa [inOutVar, orOut] using hor

private theorem up_inTree {k r : ℕ} {F : Set (Clause (VarSum k r))}
    (hfalse : ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) ∈ F)
    (hMatch : ↑(cMatch : Finset (Clause (VarSum k r))) ⊆ F)
    (hLeaf : ↑(cInLeaf : Finset (Clause (VarSum k r))) ⊆ F)
    (ρ : (Fin 5 × Fin k) → Option Bool)
    (t : SegTree k) {lo hi : ℕ} (hv : SegValid k t lo hi)
    (hTree : ↑(cInTree t : Finset (Clause (VarSum k r))) ⊆ F)
    {a b : State r} (hno : ¬ PathExists (availOfRho ρ) lo hi a b) :
    (inOutVar t a b, false) ∈ (stepUP F)^[6 + (W1 r + 2) * t.depth] (seedOfRho ρ) := by
  induction t generalizing lo hi a b with
  | leaf i =>
    rcases hv with ⟨rfl, rfl⟩
    simpa [SegTree.depth] using up_inLeaf hfalse hMatch hLeaf ρ hno
  | node lo' mid hi' L R ihL ihR =>
    rcases hv with ⟨rfl, rfl, hlm, hmh, hvL, hvR⟩
    have hTL : ↑(cInTree L : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
      hTree (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_coe.mp hC))))
    have hTR : ↑(cInTree R : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
      hTree (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hC)))
    let M := 6 + (W1 r + 2) * max L.depth R.depth
    have hleL : 6 + (W1 r + 2) * L.depth ≤ M := by
      dsimp only [M]; gcongr; exact le_max_left _ _
    have hleR : 6 + (W1 r + 2) * R.depth ≤ M := by
      dsimp only [M]; gcongr; exact le_max_right _ _
    have htri : ∀ f : Fin (W1 r + 1) → Bool,
        (Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) b), false) ∈
          (stepUP F)^[M + 1] (seedOfRho ρ) := by
      intro f
      set m := (equivStateVec r).symm f
      have hAnd : ↑(clauseAnd2 (Sum.inr (AuxVar.triIn mid a m b)) (inOutVar L a m) (inOutVar R m b)) ⊆ F := by
        intro C hC
        refine hTree (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)))
        refine Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finset.mem_union_left _ ?_⟩
        exact Finset.mem_biUnion.mpr ⟨m, Finset.mem_univ _, Finset.mem_coe.mp hC⟩
      by_cases hL_no : ¬ PathExists (availOfRho ρ) lo' mid.val a m
      · rw [Function.iterate_succ_apply']
        exact clauseAnd2_prop_false_left hAnd (stepUP_iterate_mono F _ hleL (ihL hvL hTL hL_no))
      · have hL_yes : PathExists (availOfRho ρ) lo' mid.val a m := not_not.mp hL_no
        have hR_no : ¬ PathExists (availOfRho ρ) mid.val hi' m b := fun hR_yes =>
          hno ((PathExists_split (availOfRho ρ) (le_of_lt hlm) (le_of_lt hmh) a b).mpr ⟨m, hL_yes, hR_yes⟩)
        rw [Function.iterate_succ_apply']
        exact clauseAnd2_prop_false_right hAnd (stepUP_iterate_mono F _ hleR (ihR hvR hTR hR_no))
    have hsub : ↑(orClauses (fun g => (Sum.inr (AuxVar.inNode mid a b g) : VarSum k r))
        (fun f => (Sum.inr (AuxVar.triIn mid a ((equivStateVec r).symm f) b) : VarSum k r))) ⊆ F := by
      intro C hC
      rw [Finset.mem_coe] at hC
      refine hTree (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ ?_)))
      exact Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finset.mem_union_right _ hC⟩
    have hor := orClauses_prop_false _ _ hsub htri
    rw [← Function.iterate_add_apply] at hor
    have heq : W1 r + 1 + (M + 1) = 6 + (W1 r + 2) * (SegTree.node lo' mid hi' L R).depth := by
      dsimp only [M, SegTree.depth]
      ring
    rw [heq] at hor
    exact hor

private theorem up_outTree {k r : ℕ} {F : Set (Clause (VarSum k r))}
    (hfalse : ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) ∈ F)
    (hMatch : ↑(cMatch : Finset (Clause (VarSum k r))) ⊆ F)
    (hLeaf : ↑(cInLeaf : Finset (Clause (VarSum k r))) ⊆ F)
    (ρ : (Fin 5 × Fin k) → Option Bool) (D : ℕ)
    (sub : SegTree k) {lo hi : ℕ} (hv : SegValid k sub lo hi) (hhk : hi ≤ k)
    (hdep : sub.depth ≤ D)
    (hInSub : ↑(cInTree sub : Finset (Clause (VarSum k r))) ⊆ F)
    (p : State r → State r → AuxVar k r)
    (hOutSub : ↑(cOutTree sub p : Finset (Clause (VarSum k r))) ⊆ F)
    (Rp : ℕ) (hRp : 6 + (W1 r + 2) * D ≤ Rp)
    (hp : ∀ a b, ¬ OutPath (availOfRho ρ) lo hi a b →
      (Sum.inr (p a b), false) ∈ (stepUP F)^[Rp] (seedOfRho ρ)) :
    ∀ (i : Fin k), sub.hasLeaf i → ∀ a b : State r,
      ¬ (PathExists (availOfRho ρ) i.val (i.val + 1) a b ∧ OutPath (availOfRho ρ) i.val (i.val + 1) a b) →
      (Sum.inr (AuxVar.bothLeaf i a b), false) ∈
        (stepUP F)^[Rp + (W1 r + 2) * sub.depth + 1] (seedOfRho ρ) := by
  induction sub generalizing lo hi p Rp with
  | leaf j =>
    intro i hi_leaf a b hno
    rcases hv with ⟨rfl, rfl⟩
    have hij : i = j := hi_leaf
    subst hij
    have hAnd : ↑(clauseAnd2 (Sum.inr (AuxVar.bothLeaf i a b))
        (inOutVar (.leaf i) a b) (Sum.inr (p a b))) ⊆ F := fun C hC =>
      hOutSub (Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _, Finset.mem_coe.mp hC⟩))
    have hle6 : 6 ≤ Rp := le_trans (Nat.le_add_right _ _) hRp
    simp only [SegTree.depth, mul_zero, add_zero]
    rw [Function.iterate_succ_apply']
    by_cases hpi : ¬ PathExists (availOfRho ρ) i.val (i.val + 1) a b
    · exact clauseAnd2_prop_false_left hAnd (stepUP_iterate_mono F _ hle6 (up_inLeaf hfalse hMatch hLeaf ρ hpi))
    · have hoi : ¬ OutPath (availOfRho ρ) i.val (i.val + 1) a b := fun h => hno ⟨not_not.mp hpi, h⟩
      exact clauseAnd2_prop_false_right hAnd (hp a b hoi)
  | node lo' mid hi' L R ihL ihR =>
    intro i hi_leaf a b hno
    rcases hv with ⟨rfl, rfl, hlm, hmh, hvL, hvR⟩
    have hInL : ↑(cInTree L : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
      hInSub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_coe.mp hC))))
    have hInR : ↑(cInTree R : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
      hInSub (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hC)))
    have hOutL : ↑(cOutTree L (fun a b => AuxVar.outLeft mid a b (Sum.inl ())) : Finset (Clause (VarSum k r))) ⊆ F :=
      fun C hC => hOutSub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_coe.mp hC))))
    have hOutR : ↑(cOutTree R (fun b c => AuxVar.outRight mid b c (Sum.inl ())) : Finset (Clause (VarSum k r))) ⊆ F :=
      fun C hC => hOutSub (Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hC)))
    have hdep_eq : (SegTree.node lo' mid hi' L R).depth = max L.depth R.depth + 1 := rfl
    have hdepL : L.depth ≤ D := by have := le_max_left L.depth R.depth; omega
    have hdepR : R.depth ≤ D := by have := le_max_right L.depth R.depth; omega
    have hRp1 : 6 + (W1 r + 2) * D ≤ Rp + (W1 r + 2) := by omega
    have hle_R_in : 6 + (W1 r + 2) * R.depth ≤ Rp := le_trans (by gcongr) hRp
    have hle_L_in : 6 + (W1 r + 2) * L.depth ≤ Rp := le_trans (by gcongr) hRp
    rcases hi_leaf with hL_leaf | hR_leaf
    · have hpL : ∀ x y : State r, ¬ OutPath (availOfRho ρ) lo' mid.val x y →
          (Sum.inr (AuxVar.outLeft mid x y (Sum.inl ())), false) ∈
            (stepUP F)^[Rp + (W1 r + 2)] (seedOfRho ρ) := by
        intro x y hnoL
        have htri : ∀ f : Fin (W1 r + 1) → Bool,
            (Sum.inr (AuxVar.triOutL mid x y ((equivStateVec r).symm f)), false) ∈
              (stepUP F)^[Rp + 1] (seedOfRho ρ) := by
          intro f
          set z := (equivStateVec r).symm f
          have hAnd : ↑(clauseAnd2 (Sum.inr (AuxVar.triOutL mid x y z))
              (Sum.inr (p x z)) (inOutVar R y z)) ⊆ F := by
            intro C hC
            refine hOutSub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))))
            refine Finset.mem_biUnion.mpr ⟨(x, y), Finset.mem_univ _, Finset.mem_union_left _ ?_⟩
            exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, Finset.mem_coe.mp hC⟩
          by_cases hz : ¬ PathExists (availOfRho ρ) mid.val hi' y z
          · rw [Function.iterate_succ_apply']
            exact clauseAnd2_prop_false_right hAnd
              (stepUP_iterate_mono F _ hle_R_in (up_inTree hfalse hMatch hLeaf ρ R hvR hInR hz))
          · have ho_no : ¬ OutPath (availOfRho ρ) lo' hi' x z := fun ho_yes =>
              hnoL ((OutPath_split_L (availOfRho ρ) (Nat.zero_le _) (le_of_lt hlm) (le_of_lt hmh) hhk x y).mpr
                ⟨z, not_not.mp hz, ho_yes⟩)
            rw [Function.iterate_succ_apply']
            exact clauseAnd2_prop_false_left hAnd (hp x z ho_no)
        have hsub : ↑(orClauses (fun g => (Sum.inr (AuxVar.outLeft mid x y g) : VarSum k r))
            (fun f => (Sum.inr (AuxVar.triOutL mid x y ((equivStateVec r).symm f)) : VarSum k r))) ⊆ F := by
          intro C hC
          rw [Finset.mem_coe] at hC
          refine hOutSub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))))
          exact Finset.mem_biUnion.mpr ⟨(x, y), Finset.mem_univ _, Finset.mem_union_right _ hC⟩
        have hor := orClauses_prop_false _ _ hsub htri
        rw [← Function.iterate_add_apply] at hor
        have heq : W1 r + 1 + (Rp + 1) = Rp + (W1 r + 2) := by ring
        rw [heq] at hor
        exact hor
      have hres := ihL hvL (le_of_lt mid.isLt) hdepL hInL _ hOutL (Rp + (W1 r + 2)) hRp1 hpL i hL_leaf a b hno
      have hmono : Rp + (W1 r + 2) + (W1 r + 2) * L.depth + 1 ≤
          Rp + (W1 r + 2) * (SegTree.node lo' mid hi' L R).depth + 1 := by
        rw [hdep_eq]
        have hlm' : L.depth ≤ max L.depth R.depth := le_max_left _ _
        nlinarith
      exact stepUP_iterate_mono F _ hmono hres
    · have hpR : ∀ y z : State r, ¬ OutPath (availOfRho ρ) mid.val hi' y z →
          (Sum.inr (AuxVar.outRight mid y z (Sum.inl ())), false) ∈
            (stepUP F)^[Rp + (W1 r + 2)] (seedOfRho ρ) := by
        intro y z hnoR
        have htri : ∀ f : Fin (W1 r + 1) → Bool,
            (Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) y z), false) ∈
              (stepUP F)^[Rp + 1] (seedOfRho ρ) := by
          intro f
          set x := (equivStateVec r).symm f
          have hAnd : ↑(clauseAnd2 (Sum.inr (AuxVar.triOutR mid x y z))
              (Sum.inr (p x z)) (inOutVar L x y)) ⊆ F := by
            intro C hC
            refine hOutSub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))))
            refine Finset.mem_biUnion.mpr ⟨(y, z), Finset.mem_univ _, Finset.mem_union_left _ ?_⟩
            exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_univ _, Finset.mem_coe.mp hC⟩
          by_cases hx : ¬ PathExists (availOfRho ρ) lo' mid.val x y
          · rw [Function.iterate_succ_apply']
            exact clauseAnd2_prop_false_right hAnd
              (stepUP_iterate_mono F _ hle_L_in (up_inTree hfalse hMatch hLeaf ρ L hvL hInL hx))
          · have ho_no : ¬ OutPath (availOfRho ρ) lo' hi' x z := fun ho_yes =>
              hnoR ((OutPath_split_R (availOfRho ρ) (Nat.zero_le _) (le_of_lt hlm) (le_of_lt hmh) hhk y z).mpr
                ⟨x, not_not.mp hx, ho_yes⟩)
            rw [Function.iterate_succ_apply']
            exact clauseAnd2_prop_false_left hAnd (hp x z ho_no)
        have hsub : ↑(orClauses (fun g => (Sum.inr (AuxVar.outRight mid y z g) : VarSum k r))
            (fun f => (Sum.inr (AuxVar.triOutR mid ((equivStateVec r).symm f) y z) : VarSum k r))) ⊆ F := by
          intro C hC
          rw [Finset.mem_coe] at hC
          refine hOutSub (Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))))
          exact Finset.mem_biUnion.mpr ⟨(y, z), Finset.mem_univ _, Finset.mem_union_right _ hC⟩
        have hor := orClauses_prop_false _ _ hsub htri
        rw [← Function.iterate_add_apply] at hor
        have heq : W1 r + 1 + (Rp + 1) = Rp + (W1 r + 2) := by ring
        rw [heq] at hor
        exact hor
      have hres := ihR hvR hhk hdepR hInR _ hOutR (Rp + (W1 r + 2)) hRp1 hpR i hR_leaf a b hno
      have hmono : Rp + (W1 r + 2) + (W1 r + 2) * R.depth + 1 ≤
          Rp + (W1 r + 2) * (SegTree.node lo' mid hi' L R).depth + 1 := by
        rw [hdep_eq]
        have hrm' : R.depth ≤ max L.depth R.depth := le_max_right _ _
        nlinarith
      exact stepUP_iterate_mono F _ hmono hres

private theorem no_cycle_if_unsat {k r : ℕ} (hk : 0 < k)
    (ρ : (Fin 5 × Fin k) → Option Bool)
    (hunsat : ¬ ∃ v : (Fin 5 × Fin k) → Bool,
      (wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
       wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r) ∧
      ∀ (raw : Fin 5 × Fin k) (sgn : Bool), ρ raw = some sgn → v raw = sgn) :
    ∀ a : State r, ¬ PathExists (availOfRho ρ) 0 k a a := by
  intro a hpe
  obtain ⟨s, in5, hs⟩ := (PathExists_cycle_iff hk (availOfRho ρ)).mp ⟨a, hpe⟩
  let v : (Fin 5 × Fin k) → Bool := fun (t, i) => in5 i t
  have hcyc : ∀ i : Fin k, LeafOK i (fun t => v (t, i)) (s i) (s (nextIdx hk i)) = true :=
    fun i => (hs i).2
  refine hunsat ⟨v, cycle_implies_agrees hk v s hcyc, fun ⟨t, i⟩ sgn hρ => ?_⟩
  exact (hs i).1 t sgn hρ

private theorem up_unsat_rootOK {k r : ℕ} (hk : 0 < k)
    (ρ : (Fin 5 × Fin k) → Option Bool)
    (hunsat : ¬ ∃ v : (Fin 5 × Fin k) → Bool,
      (wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
       wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r) ∧
      ∀ (raw : Fin 5 × Fin k) (sgn : Bool), ρ raw = some sgn → v raw = sgn) :
    let tree := buildSeg k 0 k hk (Nat.zero_add k).le
    let F : Set (Clause (VarSum k r)) := ↑(F_aux (r := r) tree : Finset _)
    ∃ C ∈ (F_aux (r := r) tree : Finset (Clause (VarSum k r))),
      ∀ l ∈ C, negLit l ∈ (stepUP F)^[2 * (17 * r + 4) * Nat.clog 2 k + (17 * r + 3) + 16] (seedOfRho ρ) := by
  intro tree F
  have htree : SegValid k tree 0 k := by simpa [tree] using buildSeg_valid k 0 k hk (Nat.zero_add k).le
  have hmemF : ∀ C ∈ (F_aux (r := r) tree : Finset (Clause (VarSum k r))), C ∈ F :=
    fun _ h => Finset.mem_coe.mpr h
  have hfalse : ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) ∈ F :=
    hmemF _ (by simp [F_aux])
  have hMatch : ↑(cMatch : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  have hLeaf : ↑(cInLeaf : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  have hTree : ↑(cInTree (r := r) tree : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  have hRoot : ↑(orClauses (fun g => Sum.inr (AuxVar.rootOK g))
      (fun f => let a := (equivStateVec r).symm f; inOutVar tree a a)) ⊆ F := fun C hC =>
    hmemF _ (by simp only [F_aux, Finset.mem_union]; left; left; left; right; exact Finset.mem_union_left _ (Finset.mem_coe.mp hC))
  have hno := no_cycle_if_unsat hk ρ hunsat
  have hleaves : ∀ f : Fin (W1 r + 1) → Bool,
      (let a := (equivStateVec r).symm f; inOutVar tree a a, false) ∈
        (stepUP F)^[6 + (W1 r + 2) * tree.depth] (seedOfRho ρ) := fun f =>
    up_inTree hfalse hMatch hLeaf ρ tree htree hTree (hno ((equivStateVec r).symm f))
  have hor := orClauses_prop_false _ _ hRoot hleaves
  rw [← Function.iterate_add_apply] at hor
  have hdepth : tree.depth ≤ Nat.clog 2 k := by simpa [tree] using buildSeg_depth_le k 0 k hk (Nat.zero_add k).le
  have hW1 : W1 r + 1 ≤ 17 * r + 3 := by dsimp only [W1]; omega
  have hround : W1 r + 1 + (6 + (W1 r + 2) * tree.depth) ≤
      2 * (17 * r + 4) * Nat.clog 2 k + (17 * r + 3) + 16 := by
    have hmul : (W1 r + 2) * tree.depth ≤ 2 * (17 * r + 4) * Nat.clog 2 k := by
      calc (W1 r + 2) * tree.depth ≤ (17 * r + 4) * Nat.clog 2 k := Nat.mul_le_mul (by omega) hdepth
        _ ≤ 2 * ((17 * r + 4) * Nat.clog 2 k) := Nat.le_mul_of_pos_left _ (by decide)
        _ = 2 * (17 * r + 4) * Nat.clog 2 k := by ring
    omega
  refine ⟨{(Sum.inr (AuxVar.rootOK (Sum.inl ())), true)}, ?_, fun l hl => ?_⟩
  · simp only [F_aux, Finset.mem_union]; left; left; left; right
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  · rw [Finset.mem_singleton] at hl
    subst hl
    exact stepUP_iterate_mono F _ hround hor

private theorem up_forced_lit {k r : ℕ} (hk : 0 < k)
    (ρ : (Fin 5 × Fin k) → Option Bool) (raw : Fin 5 × Fin k) (sign : Bool)
    (hforced : ∀ v : (Fin 5 × Fin k) → Bool,
      ((wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
        wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r) ∧
       ∀ (raw' : Fin 5 × Fin k) (sgn : Bool), ρ raw' = some sgn → v raw' = sgn) →
      v raw = sign) :
    let tree := buildSeg k 0 k hk (Nat.zero_add k).le
    let F : Set (Clause (VarSum k r)) := ↑(F_aux (r := r) tree : Finset _)
    (Sum.inl raw, sign) ∈
      (stepUP F)^[2 * (17 * r + 4) * Nat.clog 2 k + (17 * r + 3) + 16] (seedOfRho ρ) := by
  intro tree F
  rcases raw with ⟨t, i⟩
  have htree : SegValid k tree 0 k := by simpa [tree] using buildSeg_valid k 0 k hk (Nat.zero_add k).le
  have hmemF : ∀ C ∈ (F_aux (r := r) tree : Finset (Clause (VarSum k r))), C ∈ F :=
    fun _ h => Finset.mem_coe.mpr h
  have hfalse : ({(Sum.inr AuxVar.falseVar, false)} : Clause (VarSum k r)) ∈ F :=
    hmemF _ (by simp [F_aux])
  have hMatch : ↑(cMatch : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  have hLeaf : ↑(cInLeaf : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  have hTree : ↑(cInTree (r := r) tree : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  have hOutTree : ↑(cOutTree tree (AuxVar.outRoot (r := r)) : Finset (Clause (VarSum k r))) ⊆ F := fun C hC =>
    hmemF _ (by simp [F_aux, Finset.mem_coe.mp hC])
  let T1 := 6 + (W1 r + 2) * tree.depth
  have hp_root : ∀ a b : State r, ¬ OutPath (availOfRho ρ) 0 k a b →
      (Sum.inr (AuxVar.outRoot a b), false) ∈ (stepUP F)^[T1] (seedOfRho ρ) := by
    intro a b hno
    rw [OutPath_root] at hno
    have hCF : ({(Sum.inr (AuxVar.outRoot a b), decide (a = b))} : Clause (VarSum k r)) ∈ F := by
      refine hmemF _ ?_
      simp only [F_aux, Finset.mem_union]
      left; left; right
      exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩
    have h1 : (Sum.inr (AuxVar.outRoot a b), false) ∈ (stepUP F)^[1] (seedOfRho ρ) := by
      refine mem_stepUP_succ_of_clause hCF (by simp [decide_eq_false hno]) ?_
      intro other ho hne
      rw [Finset.mem_singleton] at ho
      rw [decide_eq_false hno] at ho
      exact absurd ho hne
    exact stepUP_iterate_mono F _ (by dsimp only [T1]; omega) h1
  have hhas : tree.hasLeaf i := by
    simpa [tree] using buildSeg_hasLeaf k 0 k hk (Nat.zero_add k).le i (Nat.zero_le _) (by omega)
  have hboth := up_outTree hfalse hMatch hLeaf ρ tree.depth tree htree le_rfl le_rfl hTree
    AuxVar.outRoot hOutTree T1 le_rfl hp_root i hhas
  let Rboth := T1 + (W1 r + 2) * tree.depth + 1
  have hbad_match : ∀ in5 : In5, in5 t = !sign →
      (Sum.inr (AuxVar.matchVar i in5), false) ∈ (stepUP F)^[Rboth + (W1 r + 1) + 1] (seedOfRho ρ) := by
    intro in5 hin5
    by_cases hav : ¬ availOfRho ρ i in5
    · exact stepUP_iterate_mono F _ (by dsimp only [Rboth, T1]; omega) (up_matchVar_bad hMatch ρ hav)
    · have hav_yes : availOfRho ρ i in5 := not_not.mp hav
      have hmtb_sub : ↑(orClauses (fun g => (Sum.inr (AuxVar.matchToBoth i in5 g) : VarSum k r))
          (fun f => match mkPair i in5 ((equivStateVec r).symm f) with
            | none => (Sum.inr AuxVar.falseVar : VarSum k r)
            | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b))) ⊆ F := fun C hC => by
        refine hmemF _ ?_
        simp only [F_aux, Finset.mem_union]
        right
        exact Finset.mem_biUnion.mpr ⟨(i, in5), Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_coe.mp hC)⟩
      have hleaves : ∀ f : Fin (W1 r + 1) → Bool,
          ((match mkPair i in5 ((equivStateVec r).symm f) with
            | none => (Sum.inr AuxVar.falseVar : VarSum k r)
            | some (a, b) => Sum.inr (AuxVar.bothLeaf i a b)), false) ∈
            (stepUP F)^[Rboth] (seedOfRho ρ) := by
        intro f
        cases hmp : mkPair i in5 ((equivStateVec r).symm f) with
        | none =>
          exact stepUP_iterate_mono F _ (by dsimp only [Rboth, T1]; omega) (up_falseVar hfalse (seedOfRho ρ))
        | some ab =>
          rcases ab with ⟨a, b⟩
          dsimp only
          apply hboth a b
          rintro ⟨_, ⟨c0, hop1, hop2⟩⟩
          let avail' : Fin k → In5 → Prop := fun j p => availOfRho ρ j p ∧ (j = i → p = in5)
          have hp1 : PathExists avail' 0 i.val c0 a := by
            rcases hop1 with ⟨s1, hs10, hs1a, hstep1⟩
            refine ⟨s1, hs10, hs1a, fun j h1 h2 => ?_⟩
            obtain ⟨hj, in5j, havj, hokj⟩ := hstep1 j h1 h2
            exact ⟨hj, in5j, ⟨havj, fun hji => by have hval := congrArg Fin.val hji; dsimp at hval; omega⟩, hokj⟩
          have hp2 : PathExists avail' i.val (i.val + 1) a b :=
            (PathExists_step avail' i.isLt a b).mpr ⟨in5, ⟨hav_yes, fun _ => rfl⟩, LeafOK_of_mkPair hmp⟩
          have hp3 : PathExists avail' (i.val + 1) k b c0 := by
            rcases hop2 with ⟨s2, hs2b, hs2k, hstep2⟩
            refine ⟨s2, hs2b, hs2k, fun j h1 h2 => ?_⟩
            obtain ⟨hj, in5j, havj, hokj⟩ := hstep2 j h1 h2
            exact ⟨hj, in5j, ⟨havj, fun hji => by have hval := congrArg Fin.val hji; dsimp at hval; omega⟩, hokj⟩
          have h0i : PathExists avail' 0 (i.val + 1) c0 b :=
            (PathExists_split avail' (Nat.zero_le _) (Nat.le_succ _) c0 b).mpr ⟨a, hp1, hp2⟩
          have h0k : PathExists avail' 0 k c0 c0 :=
            (PathExists_split avail' (Nat.zero_le _) (Nat.succ_le_of_lt i.isLt) c0 c0).mpr ⟨b, h0i, hp3⟩
          obtain ⟨states, in5', hcyc'⟩ := (PathExists_cycle_iff hk avail').mp ⟨c0, h0k⟩
          let v : (Fin 5 × Fin k) → Bool := fun (u, j) => in5' j u
          have hcyc_v : ∀ j : Fin k, LeafOK j (fun u => v (u, j)) (states j) (states (nextIdx hk j)) = true :=
            fun j => (hcyc' j).2
          have hag_v := cycle_implies_agrees hk v states hcyc_v
          have hρ_v : ∀ (raw' : Fin 5 × Fin k) (sgn : Bool), ρ raw' = some sgn → v raw' = sgn := by
            intro ⟨u, j⟩ sgn hρ
            exact (hcyc' j).1.1 u sgn hρ
          have hv_eq := hforced v ⟨hag_v, hρ_v⟩
          have heq_in5 : in5' i = in5 := (hcyc' i).1.2 rfl
          have hv_ti : v (t, i) = !sign := by change in5' i t = !sign; rw [heq_in5, hin5]
          rw [hv_eq] at hv_ti
          cases sign <;> simp at hv_ti
      have hor := orClauses_prop_false _ _ hmtb_sub hleaves
      rw [← Function.iterate_add_apply] at hor
      have hbin : ({(Sum.inr (AuxVar.matchVar i in5), false),
          (Sum.inr (AuxVar.matchToBoth i in5 (Sum.inl ())), true)} : Clause (VarSum k r)) ∈ F := by
        refine hmemF _ ?_
        simp only [F_aux, Finset.mem_union]
        right
        exact Finset.mem_biUnion.mpr ⟨(i, in5), Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
      have heq_step : W1 r + 1 + Rboth + 1 = Rboth + (W1 r + 1) + 1 := by ring
      rw [← heq_step]
      refine mem_stepUP_succ_of_clause hbin (Finset.mem_insert_self _ _) ?_
      intro other ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl
      · exact absurd rfl hne
      · exact hor
  have hforce_sub : ↑(orClauses (fun g => (Sum.inr (AuxVar.forceGate i t sign g) : VarSum k r))
      (fun g => Sum.inr (AuxVar.matchVar i (ins4 t (!sign) g)))) ⊆ F := fun C hC => by
    refine hmemF _ ?_
    simp only [F_aux, Finset.mem_union]
    left; left; left; left; left; left; right
    exact Finset.mem_biUnion.mpr ⟨(i, t, sign), Finset.mem_univ _, Finset.mem_union_left _ (Finset.mem_coe.mp hC)⟩
  have hforce_leaves : ∀ g : In4,
      (Sum.inr (AuxVar.matchVar i (ins4 t (!sign) g)), false) ∈
        (stepUP F)^[Rboth + (W1 r + 1) + 1] (seedOfRho ρ) :=
    fun g => hbad_match (ins4 t (!sign) g) (ins4_at t (!sign) g)
  have hor_force := orClauses_prop_false _ _ hforce_sub hforce_leaves
  rw [← Function.iterate_add_apply] at hor_force
  have hforce_bin : ({(Sum.inr (AuxVar.forceGate i t sign (Sum.inl ())), true),
      (Sum.inl (t, i), sign)} : Clause (VarSum k r)) ∈ F := by
    refine hmemF _ ?_
    simp only [F_aux, Finset.mem_union]
    left; left; left; left; left; left; right
    exact Finset.mem_biUnion.mpr ⟨(i, t, sign), Finset.mem_univ _, Finset.mem_union_right _ (Finset.mem_singleton_self _)⟩
  have hlast : (Sum.inl (t, i), sign) ∈
      (stepUP F)^[4 + (Rboth + (W1 r + 1) + 1) + 1] (seedOfRho ρ) := by
    refine mem_stepUP_succ_of_clause hforce_bin (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) ?_
    intro other ho hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl
    · exact hor_force
    · exact absurd rfl hne
  have hdepth : tree.depth ≤ Nat.clog 2 k := by simpa [tree] using buildSeg_depth_le k 0 k hk (Nat.zero_add k).le
  have hW1 : W1 r + 1 ≤ 17 * r + 3 := by dsimp only [W1]; omega
  have hround : 4 + (Rboth + (W1 r + 1) + 1) + 1 ≤
      2 * (17 * r + 4) * Nat.clog 2 k + (17 * r + 3) + 16 := by
    dsimp only [Rboth, T1]
    have hmul : 2 * ((W1 r + 2) * tree.depth) ≤ 2 * (17 * r + 4) * Nat.clog 2 k := by
      calc 2 * ((W1 r + 2) * tree.depth) ≤ 2 * ((17 * r + 4) * Nat.clog 2 k) :=
          Nat.mul_le_mul_left 2 (Nat.mul_le_mul (by omega) hdepth)
        _ = 2 * (17 * r + 4) * Nat.clog 2 k := by ring
    omega
  exact stepUP_iterate_mono F _ hround hlast

private def mapLit {α β : Type} (e : α ≃ β) (l : Literal α) : Literal β := (e l.1, l.2)

private theorem mapLit_inj {α β : Type} (e : α ≃ β) : Function.Injective (mapLit e) := by
  rintro ⟨x1, b1⟩ ⟨x2, b2⟩ h
  have h1 : e x1 = e x2 := congrArg Prod.fst h
  have h2 : b1 = b2 := congrArg Prod.snd h
  exact Prod.ext (e.injective h1) h2

private theorem mapLit_negLit {α β : Type} (e : α ≃ β) (l : Literal α) :
    mapLit e (negLit l) = negLit (mapLit e l) := rfl

private def mapClause {α β : Type} [DecidableEq β] (e : α ≃ β) (C : Clause α) : Clause β :=
  C.image (mapLit e)

private theorem mapClause_inj {α β : Type} [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Function.Injective (mapClause e) :=
  Finset.image_injective (mapLit_inj e)

private theorem mapClause_card {α β : Type} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (C : Clause α) : (mapClause e C).card = C.card :=
  Finset.card_image_of_injective C (mapLit_inj e)

private def mapCNF {α β : Type} [DecidableEq β] (e : α ≃ β) (F : Finset (Clause α)) :
    Finset (Clause β) :=
  F.image (mapClause e)

private theorem mapCNF_sum_card {α β : Type} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (F : Finset (Clause α)) : (∑ C ∈ mapCNF e F, C.card) = ∑ C ∈ F, C.card := by
  dsimp only [mapCNF]
  rw [Finset.sum_image (fun x _ y _ h => mapClause_inj e h)]
  refine Finset.sum_congr rfl fun C _ => mapClause_card e C

private theorem mapCNF_card_le_three {α β : Type} [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (F : Finset (Clause α)) (h3 : ∀ C ∈ F, C.card ≤ 3) :
    ∀ C' ∈ mapCNF e F, C'.card ≤ 3 := by
  intro C' hC'
  rcases Finset.mem_image.mp hC' with ⟨C, hCF, rfl⟩
  rw [mapClause_card]
  exact h3 C hCF

private theorem clauseSat_mapClause_iff {α β : Type} [DecidableEq β] (e : α ≃ β)
    {a : α → Bool} {a' : β → Bool} (ha : ∀ x : α, a' (e x) = a x) (C : Clause α) :
    ClauseSat a' (mapClause e C) ↔ ClauseSat a C := by
  constructor
  · rintro ⟨l', hl', hla'⟩
    rcases Finset.mem_image.mp hl' with ⟨l, hlC, rfl⟩
    refine ⟨l, hlC, ?_⟩
    dsimp only [mapLit] at hla'
    rw [← ha l.1]
    exact hla'
  · rintro ⟨l, hlC, hla⟩
    refine ⟨mapLit e l, Finset.mem_image_of_mem _ hlC, ?_⟩
    dsimp only [mapLit]
    rw [ha l.1]
    exact hla

private theorem satisfies_mapCNF_iff {α β V : Type} [DecidableEq V] [DecidableEq β] (eAux : α ≃ β)
    (F : Finset (Clause (Sum V α))) (v : V → Bool) :
    (∃ aux : α → Bool, Satisfies (Sum.elim v aux) (↑F : Set _)) ↔
      ∃ aux' : β → Bool, Satisfies (Sum.elim v aux') (↑(mapCNF (Equiv.sumCongr (Equiv.refl V) eAux) F) : Set _) := by
  let eVar : Sum V α ≃ Sum V β := Equiv.sumCongr (Equiv.refl V) eAux
  constructor
  · rintro ⟨aux, hsat⟩
    refine ⟨aux ∘ eAux.symm, fun C' hC' => ?_⟩
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hC') with ⟨C, hCF, rfl⟩
    refine (clauseSat_mapClause_iff (a := Sum.elim v aux) (a' := Sum.elim v (aux ∘ eAux.symm))
      eVar (fun x => by cases x <;> simp [eVar]) C).mpr ?_
    exact hsat C (Finset.mem_coe.mpr hCF)
  · rintro ⟨aux', hsat'⟩
    refine ⟨aux' ∘ eAux, fun C hC => ?_⟩
    refine (clauseSat_mapClause_iff (a := Sum.elim v (aux' ∘ eAux)) (a' := Sum.elim v aux')
      eVar (fun x => by cases x <;> rfl) C).mp ?_
    exact hsat' (mapClause eVar C) (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hC)))

private theorem mapLit_mem_stepUP_iff {k r m : ℕ} (eAux : AuxVar k r ≃ Fin m)
    (F : Finset (Clause (VarSum k r))) (ρ : (Fin 5 × Fin k) → Option Bool) :
    let eVar : VarSum k r ≃ Sum (Fin 5 × Fin k) (Fin m) := Equiv.sumCongr (Equiv.refl _) eAux
    let seed' : Set (Literal (Sum (Fin 5 × Fin k) (Fin m))) :=
      {l | ∃ raw : Fin 5 × Fin k, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
    ∀ (n : ℕ) (l : Literal (VarSum k r)),
      l ∈ (stepUP (↑F : Set _) )^[n] (seedOfRho ρ) ↔
        mapLit eVar l ∈ (stepUP (↑(mapCNF eVar F) : Set _))^[n] seed' := by
  intro eVar seed' n
  induction n with
  | zero =>
    intro l
    constructor
    · rintro ⟨raw, hraw, hρ⟩
      refine ⟨raw, ?_, hρ⟩
      dsimp only [mapLit]
      rw [hraw]
      rfl
    · rintro ⟨raw, hraw, hρ⟩
      refine ⟨raw, ?_, hρ⟩
      dsimp only [mapLit] at hraw
      cases hx : l.1 with
      | inl raw' =>
        rw [hx] at hraw
        simp only [eVar, Equiv.sumCongr_apply, Equiv.refl_apply, Sum.map_inl, Sum.inl.injEq] at hraw
        exact congrArg Sum.inl hraw
      | inr aux =>
        rw [hx] at hraw
        simp [eVar] at hraw
  | @succ n ih =>
    intro l
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    constructor
    · rintro (hl | ⟨C, hCF, hlC, hneg⟩)
      · exact Or.inl ((ih l).mp hl)
      · refine Or.inr ⟨mapClause eVar C, Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hCF)),
          Finset.mem_image_of_mem _ hlC, ?_⟩
        intro other' ho' hne'
        rcases Finset.mem_image.mp ho' with ⟨other, hoC, rfl⟩
        have hne : other ≠ l := fun h => hne' (by rw [h])
        rw [← mapLit_negLit]
        exact (ih _).mp (hneg other hoC hne)
    · rintro (hl | ⟨C', hC'F, hlC', hneg'⟩)
      · exact Or.inl ((ih l).mpr hl)
      · rcases Finset.mem_image.mp (Finset.mem_coe.mp hC'F) with ⟨C, hCF, rfl⟩
        rcases Finset.mem_image.mp hlC' with ⟨l₀, hl₀C, hl₀_eq⟩
        have hll₀ : l₀ = l := mapLit_inj eVar hl₀_eq
        subst hll₀
        refine Or.inr ⟨C, Finset.mem_coe.mpr hCF, hl₀C, ?_⟩
        intro other hoC hne
        have hne' : mapLit eVar other ≠ mapLit eVar l₀ := fun h => hne (mapLit_inj eVar h)
        exact (ih (negLit other)).mpr (hneg' (mapLit eVar other) (Finset.mem_image_of_mem _ hoC) hne')

private theorem main_aux (k r : ℕ) (hk : 0 < k) :
    let V := Fin 5 × Fin k
    let agrees := fun (v : V → Bool) =>
      wordOf k v 3 = rowStateAt k (wordOf k v 2) (wordOf k v 0) r ∧
      wordOf k v 4 = colStateAt k r (wordOf k v 2) (wordOf k v 1) r
    let B := 17 * r + 3
    let rounds := 2 * (B + 1) * (Nat.clog 2 k) + B + 16
    ∃ (m : ℕ) (F : Finset (Clause (Sum V (Fin m)))),
      m + (∑ C ∈ F, C.card) ≤ 256 * (k + 1) * 2 ^ (3 * B) ∧
      (∀ C ∈ F, C.card ≤ 3) ∧
      (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
        Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
      ∀ ρ : V → Option Bool,
        let seed : Set (Literal (Sum V (Fin m))) :=
          {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
        let advance := fun S : Set (Literal (Sum V (Fin m))) =>
          S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l → negLit other ∈ S}
        let known := (advance^[rounds]) seed
        let complete := fun v : V → Bool => agrees v ∧
          ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
        ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, negLit l ∈ known) ∧
        ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
          (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known) := by
  intro V agrees B rounds
  let tree := buildSeg k 0 k hk (Nat.zero_add k).le
  let F0 : Finset (Clause (VarSum k r)) := F_aux (r := r) tree
  let m := Fintype.card (AuxVar k r)
  let eAux : AuxVar k r ≃ Fin m := Fintype.equivFin (AuxVar k r)
  let eVar : VarSum k r ≃ Sum V (Fin m) := Equiv.sumCongr (Equiv.refl V) eAux
  let F : Finset (Clause (Sum V (Fin m))) := mapCNF eVar F0
  refine ⟨m, F, ?_, ?_, ?_, ?_⟩
  · have hcnt := buildSeg_counts k 0 k hk (Nat.zero_add k).le
    rw [mapCNF_sum_card]
    exact F_aux_size_le hk tree hcnt.1 hcnt.2
  · exact mapCNF_card_le_three eVar F0 (F_aux_card_le_three tree)
  · intro v
    exact (satisfies_F_aux_iff hk v).trans (satisfies_mapCNF_iff eAux F0 v)
  · intro ρ seed advance known complete
    have hadv : advance = stepUP (↑F : Set _) := by
      funext S
      simp only [advance, stepUP, Finset.mem_coe]
    have hknown : known = (stepUP (↑F : Set _))^[rounds] seed := by
      dsimp only [known]; rw [hadv]
    have hcomplete_iff : ∀ v : V → Bool, complete v ↔
        (∃ aux : Fin m → Bool, Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
        ∀ l ∈ seed, Sum.elim v (fun _ => false) l.1 = l.2 := by
      intro v
      constructor
      · rintro ⟨hag, hρ⟩
        refine ⟨?_, fun l hl => ?_⟩
        · exact ((satisfies_F_aux_iff hk v).trans (satisfies_mapCNF_iff eAux F0 v)).mp hag
        · rcases hl with ⟨raw, hraw, hρraw⟩
          have heq : l.1 = Sum.inl raw := hraw
          rw [heq]
          exact hρ raw l.2 hρraw
      · rintro ⟨hsat, hseed⟩
        refine ⟨((satisfies_F_aux_iff hk v).trans (satisfies_mapCNF_iff eAux F0 v)).mpr hsat,
          fun raw sign hρ => ?_⟩
        exact hseed (Sum.inl raw, sign) ⟨raw, rfl, hρ⟩
    have hsound : ∀ {v : V → Bool} {aux : Fin m → Bool},
        complete v → Satisfies (Sum.elim v aux) (↑F : Set _) →
        ∀ l ∈ known, Sum.elim v aux l.1 = l.2 := by
      intro v aux hcomp hsat l hl
      rw [hknown] at hl
      refine stepUP_sound hsat (fun l₀ hl₀ => ?_) rounds l hl
      rcases hl₀ with ⟨raw, hraw, hρ⟩
      have heq : l₀.1 = Sum.inl raw := hraw
      rw [heq]
      exact hcomp.2 raw l₀.2 hρ
    constructor
    · constructor
      · intro hunsat
        obtain ⟨C, hCF0, hneg⟩ := up_unsat_rootOK hk ρ hunsat
        refine ⟨mapClause eVar C, Finset.mem_image_of_mem _ hCF0, fun l' hl' => ?_⟩
        rcases Finset.mem_image.mp hl' with ⟨l, hlC, rfl⟩
        rw [hknown, ← mapLit_negLit]
        exact (mapLit_mem_stepUP_iff eAux F0 ρ rounds (negLit l)).mp (hneg l hlC)
      · rintro ⟨C, hCF, hneg⟩ ⟨v, hcomp⟩
        obtain ⟨aux, hsat⟩ := (hcomplete_iff v).mp hcomp |>.1
        obtain ⟨w, hwC, hwa⟩ := hsat C (Finset.mem_coe.mpr hCF)
        have hnw := hsound hcomp hsat (negLit w) (hneg w hwC)
        dsimp only [negLit] at hnw
        cases hw2 : w.2 <;> simp_all
    · rintro _ raw sign
      constructor
      · intro hforced
        have hl := up_forced_lit hk ρ raw sign hforced
        have hmap : mapLit eVar (Sum.inl raw, sign) = (Sum.inl raw, sign) := rfl
        rw [hknown, ← hmap]
        exact (mapLit_mem_stepUP_iff eAux F0 ρ rounds (Sum.inl raw, sign)).mp hl
      · intro hmem v hcomp
        obtain ⟨aux, hsat⟩ := ((hcomplete_iff v).mp hcomp).1
        exact hsound hcomp hsat (Sum.inl raw, sign) hmem

end UnitProp

end PEqualNP.Outside.L_pcx_284_aux

open PEqualNP.Outside.L_pcx_284_aux in
theorem PEqualNP.Outside.L_pcx_284 :
    ∀ (k r : ℕ), 0 < k →
      let rot := fun (s word : Nat) =>
        ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
      let step := fun (word : Nat) =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor (word.testBit i)
            (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
      let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
      let first := fun (rowKey rowName : Nat) =>
        (List.range r).foldl (fun rowState rowIndex =>
          step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
            rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
      let second := fun (colKey colName : Nat) =>
        (List.range r).foldl (fun colState colIndex =>
          step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
            rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
          (rot 3 colKey ^^^ colName)
      let V := Fin 5 × Fin k
      let word := fun (v : V → Bool) (track : Fin 5) =>
        ∑ j : Fin k, (v (track,j)).toNat * 2^j.val
      let agrees := fun (v : V → Bool) =>
        word v 3 = first (word v 2) (word v 0) ∧
        word v 4 = second (word v 2) (word v 1)
      let B := 17*r+3
      let rounds := 2*(B+1)*(Nat.clog 2 k) + B+16
      ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
        m + (∑ C ∈ F, C.card) ≤ 256*(k+1)*2^(3*B) ∧
        (∀ C ∈ F, C.card ≤ 3) ∧
        (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
          PEqualNP.ProofComplexity.Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
        ∀ ρ : V → Option Bool,
          let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
            {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
          let advance := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
            S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
              PEqualNP.Search.negLit other ∈ S}
          let known := (advance^[rounds]) seed
          let complete := fun v : V → Bool => agrees v ∧
            ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
          ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, PEqualNP.Search.negLit l ∈ known) ∧
          ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
            (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known) :=
  fun k r hk => main_aux k r hk





