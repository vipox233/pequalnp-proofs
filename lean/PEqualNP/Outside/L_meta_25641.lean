import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25641_aux

private def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

private def constFn (k roundNo : ℕ) : ℕ :=
  3 ^ (k + roundNo) % 2 ^ k

private def firstN (k rowKey rowName t : ℕ) : ℕ :=
  (List.range t).foldl (fun rowState rowIndex =>
    stepFn k (rowState ^^^ rotFn k 1 rowState ^^^ rotFn k (k - 1) rowState) ^^^
      rotFn k (2 * rowIndex) rowKey ^^^ constFn k (rowIndex + 1)) (rotFn k 1 rowKey ^^^ rowName)

private def secondN (k colKey colName r t : ℕ) : ℕ :=
  (List.range t).foldl (fun colState colIndex =>
    stepFn k (colState ^^^ rotFn k 2 colState ^^^ rotFn k (k - 2) colState) ^^^
      rotFn k (3 * (colIndex + 1) + 1) colKey ^^^ constFn k (r + (colIndex + 1)))
    (rotFn k 3 colKey ^^^ colName)

private lemma rotFn_lt (k s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

private lemma constFn_lt (k roundNo : ℕ) : constFn k roundNo < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

private lemma testBit_rotFn {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  set a := s % k
  have ha : a < k := Nat.mod_lt s hk
  by_cases hia : i < a
  · have hge : ¬ a ≤ i := by omega
    simp only [hge, decide_false, Bool.false_and, Bool.false_or]
    have hidx : (i + k - a) % k = k - a + i := by
      have h1 : k - a + i < k := by omega
      have h2 : i + k - a = k - a + i := by omega
      rw [h2, Nat.mod_eq_of_lt h1]
    rw [hidx]
  · have hge : a ≤ i := by omega
    simp only [hge, decide_true, Bool.true_and]
    have hbig : 2 ^ k ≤ 2 ^ (k - a + i) := Nat.pow_le_pow_right (by omega) (by omega)
    have hfalse : word.testBit (k - a + i) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw hbig)
    rw [hfalse, Bool.or_false]
    have hidx : (i + k - a) % k = i - a := by
      have h1 : i + k - a = (i - a) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hidx]

private lemma testBit_stepFold (k word m i : ℕ) :
    ((List.range m).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0).testBit i =
      if i < m then
        xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))
      else false := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have h1 : i < m + 1 := by omega
      have h2 : ¬ m ≤ i := by omega
      simp [him, h1, h2]
    · by_cases heq : i = m
      · subst heq
        simp only [lt_irrefl, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one, le_refl,
          decide_true, Bool.true_and, Nat.sub_self, Bool.false_or]
        cases (xor (word.testBit i)
          (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))) <;> decide
      · have h1 : ¬ i < m + 1 := by omega
        have h2 : m ≤ i := by omega
        have hpos : 1 ≤ i - m := by omega
        have hzero : (xor (word.testBit m)
            (!(word.testBit ((m + 1) % k)) && word.testBit ((m + 2) % k))).toNat.testBit (i - m) = false := by
          apply Nat.testBit_lt_two_pow
          have hlt2 : (xor (word.testBit m)
              (!(word.testBit ((m + 1) % k)) && word.testBit ((m + 2) % k))).toNat < 2 := by
            cases (xor (word.testBit m)
              (!(word.testBit ((m + 1) % k)) && word.testBit ((m + 2) % k))) <;> decide
          have hpow : 2 ≤ 2 ^ (i - m) := by
            calc 2 = 2 ^ 1 := by decide
              _ ≤ 2 ^ (i - m) := Nat.pow_le_pow_right (by omega) hpos
          omega
        simp [him, h1, h2, hzero]

private lemma testBit_stepFn {k word i : ℕ} (hi : i < k) :
    (stepFn k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  unfold stepFn
  rw [testBit_stepFold]
  simp [hi]

private lemma lt_two_pow_of_testBit_false {x m : ℕ} (h : ∀ i, m ≤ i → x.testBit i = false) :
    x < 2 ^ m := by
  have heq : x = x % 2 ^ m := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < m
    · simp [hi]
    · simp only [hi, decide_false, Bool.false_and]
      exact h i (by omega)
  rw [heq]
  exact Nat.mod_lt x (by positivity)

private lemma lt_two_pow_iff_testBit_false {k h x : ℕ} (hx : x < 2 ^ k) (_hh : h ≤ k) :
    x < 2 ^ (k - h) ↔ ∀ q : ℕ, k - h ≤ q → q < k → x.testBit q = false := by
  constructor
  · intro hlt q hlo _
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) hlo))
  · intro hall
    apply lt_two_pow_of_testBit_false
    intro q hlo
    by_cases hqk : q < k
    · exact hall q hlo hqk
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))

private lemma stepFn_lt (k word : ℕ) : stepFn k word < 2 ^ k := by
  apply lt_two_pow_of_testBit_false
  intro i hi
  unfold stepFn
  rw [testBit_stepFold]
  have hnot : ¬ i < k := by omega
  simp [hnot]

private lemma firstN_lt {k rowKey rowName : ℕ} (hname : rowName < 2 ^ k) (t : ℕ) :
    firstN k rowKey rowName t < 2 ^ k := by
  induction t with
  | zero =>
    unfold firstN
    exact Nat.xor_lt_two_pow (rotFn_lt k 1 rowKey) hname
  | succ t ih =>
    unfold firstN at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k _ _)) (constFn_lt k _)

private lemma secondN_lt {k colKey colName r : ℕ} (hname : colName < 2 ^ k) (t : ℕ) :
    secondN k colKey colName r t < 2 ^ k := by
  induction t with
  | zero =>
    unfold secondN
    exact Nat.xor_lt_two_pow (rotFn_lt k 3 colKey) hname
  | succ t ih =>
    unfold secondN at ih ⊢
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (stepFn_lt k _) (rotFn_lt k _ _)) (constFn_lt k _)

private lemma mod_sub_shift {k q s : ℕ} (hk : 0 < k) (hsq : s ≤ q) :
    ((q % k) + k - s % k) % k = (q - s) % k := by
  have h1 : (q - s) + s = q := by omega
  have h2 : ((q % k) + k - s % k) + s % k = (q % k) + k := by
    have := Nat.mod_lt s hk
    omega
  have hmod1 : (((q % k) + k - s % k) + s) % k = q % k := by
    calc (((q % k) + k - s % k) + s) % k
        = ((((q % k) + k - s % k) % k) + s % k) % k := Nat.add_mod _ _ _
      _ = ((((q % k) + k - s % k) % k) + (s % k) % k) % k := by rw [Nat.mod_mod]
      _ = (((q % k) + k - s % k) + s % k) % k := (Nat.add_mod _ _ _).symm
      _ = ((q % k) + k) % k := by rw [h2]
      _ = q % k := by rw [Nat.add_mod_right, Nat.mod_mod]
  have hmod2 : ((q - s) + s) % k = q % k := by rw [h1]
  have heq : (((q % k) + k - s % k) % k + s % k) % k = ((q - s) % k + s % k) % k := by
    rw [← Nat.add_mod, hmod1, ← hmod2, Nat.add_mod]
  set x := ((q % k) + k - s % k) % k
  set y := (q - s) % k
  set z := s % k
  have hx : x < k := Nat.mod_lt _ hk
  have hy : y < k := Nat.mod_lt _ hk
  have hz : z < k := Nat.mod_lt _ hk
  by_cases hxz : x + z < k <;> by_cases hyz : y + z < k
  · rw [Nat.mod_eq_of_lt hxz, Nat.mod_eq_of_lt hyz] at heq
    omega
  · rw [Nat.mod_eq_of_lt hxz, show y + z = (y + z - k) + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq
    omega
  · rw [Nat.mod_eq_of_lt hyz, show x + z = (x + z - k) + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at heq
    omega
  · rw [show x + z = (x + z - k) + k by omega, show y + z = (y + z - k) + k by omega,
      Nat.add_mod_right, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
    omega

private lemma mod_rot_neg {k q c : ℕ} (_hk : 0 < k) (hc : c ≤ k) :
    ((q % k) + k - (k - c) % k) % k = (q + c) % k := by
  by_cases hc0 : c = 0
  · subst hc0
    simp [Nat.mod_self]
  · have hlt : k - c < k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have heq : q % k + k - (k - c) = q % k + c := by omega
    rw [heq, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private lemma testBit_firstStep {k st key roundNo idx q : ℕ}
    (hk : 0 < k) (hst : st < 2 ^ k) (hkey : key < 2 ^ k) (hq1 : 1 ≤ q) (hqi : 2 * idx ≤ q) :
    (stepFn k (st ^^^ rotFn k 1 st ^^^ rotFn k (k - 1) st) ^^^
      rotFn k (2 * idx) key ^^^ constFn k roundNo).testBit (q % k) =
      xor (xor
        (xor
          (xor (xor (st.testBit (q % k)) (st.testBit ((q - 1) % k))) (st.testBit ((q + 1) % k)))
          (!(xor (xor (st.testBit ((q + 1) % k)) (st.testBit (q % k))) (st.testBit ((q + 2) % k))) &&
            xor (xor (st.testBit ((q + 2) % k)) (st.testBit ((q + 1) % k))) (st.testBit ((q + 3) % k))))
        (key.testBit ((q - 2 * idx) % k)))
        ((constFn k roundNo).testBit (q % k)) := by
  have hmod : q % k < k := Nat.mod_lt q hk
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_stepFn hmod,
    testBit_rotFn hk hkey hmod, mod_sub_shift hk hqi]
  have hmix : ∀ j : ℕ, 1 ≤ j →
      (st ^^^ rotFn k 1 st ^^^ rotFn k (k - 1) st).testBit (j % k) =
        xor (xor (st.testBit (j % k)) (st.testBit ((j - 1) % k))) (st.testBit ((j + 1) % k)) := by
    intro j hj
    have hjm : j % k < k := Nat.mod_lt j hk
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotFn hk hst hjm, testBit_rotFn hk hst hjm,
      mod_sub_shift hk hj, mod_rot_neg hk (by omega)]
  have h1 : (q % k + 1) % k = (q + 1) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : (q % k + 2) % k = (q + 2) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1, h2, hmix q hq1, hmix (q + 1) (by omega), hmix (q + 2) (by omega)]
  have hs1 : q + 1 - 1 = q := by omega
  have hs2 : q + 2 - 1 = q + 1 := by omega
  have ha1 : q + 1 + 1 = q + 2 := by omega
  have ha2 : q + 2 + 1 = q + 3 := by omega
  rw [hs1, hs2, ha1, ha2]

private lemma testBit_secondStep {k st key roundNo idx q : ℕ}
    (hk : 2 ≤ k) (hst : st < 2 ^ k) (hkey : key < 2 ^ k) (hq2 : 2 ≤ q) (hqi : 3 * (idx + 1) + 1 ≤ q) :
    (stepFn k (st ^^^ rotFn k 2 st ^^^ rotFn k (k - 2) st) ^^^
      rotFn k (3 * (idx + 1) + 1) key ^^^ constFn k roundNo).testBit (q % k) =
      xor (xor
        (xor
          (xor (xor (st.testBit (q % k)) (st.testBit ((q - 2) % k))) (st.testBit ((q + 2) % k)))
          (!(xor (xor (st.testBit ((q + 1) % k)) (st.testBit ((q - 1) % k))) (st.testBit ((q + 3) % k))) &&
            xor (xor (st.testBit ((q + 2) % k)) (st.testBit (q % k))) (st.testBit ((q + 4) % k))))
        (key.testBit ((q - (3 * (idx + 1) + 1)) % k)))
        ((constFn k roundNo).testBit (q % k)) := by
  have hk0 : 0 < k := by omega
  have hmod : q % k < k := Nat.mod_lt q hk0
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_stepFn hmod,
    testBit_rotFn hk0 hkey hmod, mod_sub_shift hk0 hqi]
  have hmix : ∀ j : ℕ, 2 ≤ j →
      (st ^^^ rotFn k 2 st ^^^ rotFn k (k - 2) st).testBit (j % k) =
        xor (xor (st.testBit (j % k)) (st.testBit ((j - 2) % k))) (st.testBit ((j + 2) % k)) := by
    intro j hj
    have hjm : j % k < k := Nat.mod_lt j hk0
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotFn hk0 hst hjm, testBit_rotFn hk0 hst hjm,
      mod_sub_shift hk0 hj, mod_rot_neg hk0 hk]
  have h1 : (q % k + 1) % k = (q + 1) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : (q % k + 2) % k = (q + 2) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1, h2, hmix q hq2, hmix (q + 1) (by omega), hmix (q + 2) (by omega)]
  have hs1 : q + 1 - 2 = q - 1 := by omega
  have hs2 : q + 2 - 2 = q := by omega
  have ha1 : q + 1 + 2 = q + 3 := by omega
  have ha2 : q + 2 + 2 = q + 4 := by omega
  rw [hs1, hs2, ha1, ha2]

private lemma firstN_congr {k w1 w2 u : ℕ} (hk : 0 < k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (hu : u < 2 ^ k) :
    ∀ (t q : ℕ), max (t + 1) (2 * t - 2) ≤ q →
      (∀ d : ℕ, q - max (t + 1) (2 * t - 2) ≤ d → d ≤ q + 3 * t →
        (t = 0 → d = q - 1) →
        w1.testBit (d % k) = w2.testBit (d % k)) →
      (firstN k w1 u t).testBit (q % k) = (firstN k w2 u t).testBit (q % k) := by
  intro t
  induction t with
  | zero =>
    intro q hq hagree
    unfold firstN
    simp only [List.range_zero, List.foldl_nil]
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotFn hk hw1 (Nat.mod_lt q hk),
      testBit_rotFn hk hw2 (Nat.mod_lt q hk), mod_sub_shift hk (by omega)]
    rw [hagree (q - 1) (by omega) (by omega) (fun _ => rfl)]
  | succ t ih =>
    intro q hq hagree
    have hstep1 : firstN k w1 u (t + 1) =
        stepFn k (firstN k w1 u t ^^^ rotFn k 1 (firstN k w1 u t) ^^^ rotFn k (k - 1) (firstN k w1 u t)) ^^^
          rotFn k (2 * t) w1 ^^^ constFn k (t + 1) := by
      unfold firstN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hstep2 : firstN k w2 u (t + 1) =
        stepFn k (firstN k w2 u t ^^^ rotFn k 1 (firstN k w2 u t) ^^^ rotFn k (k - 1) (firstN k w2 u t)) ^^^
          rotFn k (2 * t) w2 ^^^ constFn k (t + 1) := by
      unfold firstN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep1, hstep2,
      testBit_firstStep hk (firstN_lt hu t) hw1 (by omega) (by omega),
      testBit_firstStep hk (firstN_lt hu t) hw2 (by omega) (by omega)]
    have hst : ∀ j : ℕ, q - 1 ≤ j → j ≤ q + 3 →
        (firstN k w1 u t).testBit (j % k) = (firstN k w2 u t).testBit (j % k) := by
      intro j hj1 hj2
      apply ih j (by omega)
      intro d hd1 hd2 ht0
      apply hagree d (by omega) (by omega) (fun h => by omega)
    rw [hst q (by omega) (by omega), hst (q - 1) (by omega) (by omega),
      hst (q + 1) (by omega) (by omega), hst (q + 2) (by omega) (by omega),
      hst (q + 3) (by omega) (by omega)]
    rw [hagree (q - 2 * t) (by omega) (by omega) (fun h => by omega)]

private lemma firstN_congr_tight {k w1 w2 u : ℕ} (hk : 0 < k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (hu : u < 2 ^ k) :
    ∀ (t : ℕ), 1 ≤ t → ∀ q : ℕ, max (t + 1) (2 * t - 2) ≤ q →
      (∀ d : ℕ, q - max (t + 1) (2 * t - 2) ≤ d → d ≤ q + 3 * t - 1 →
        w1.testBit (d % k) = w2.testBit (d % k)) →
      (firstN k w1 u t).testBit (q % k) = (firstN k w2 u t).testBit (q % k) := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    intro q hq hagree
    have hstep1 : firstN k w1 u (t + 1) =
        stepFn k (firstN k w1 u t ^^^ rotFn k 1 (firstN k w1 u t) ^^^ rotFn k (k - 1) (firstN k w1 u t)) ^^^
          rotFn k (2 * t) w1 ^^^ constFn k (t + 1) := by
      unfold firstN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hstep2 : firstN k w2 u (t + 1) =
        stepFn k (firstN k w2 u t ^^^ rotFn k 1 (firstN k w2 u t) ^^^ rotFn k (k - 1) (firstN k w2 u t)) ^^^
          rotFn k (2 * t) w2 ^^^ constFn k (t + 1) := by
      unfold firstN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep1, hstep2,
      testBit_firstStep hk (firstN_lt hu t) hw1 (by omega) (by omega),
      testBit_firstStep hk (firstN_lt hu t) hw2 (by omega) (by omega)]
    have hst : ∀ j : ℕ, q - 1 ≤ j → j ≤ q + 3 →
        (firstN k w1 u t).testBit (j % k) = (firstN k w2 u t).testBit (j % k) := by
      intro j hj1 hj2
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · unfold firstN
        simp only [List.range_zero, List.foldl_nil]
        rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotFn hk hw1 (Nat.mod_lt j hk),
          testBit_rotFn hk hw2 (Nat.mod_lt j hk), mod_sub_shift hk (by omega)]
        rw [hagree (j - 1) (by omega) (by omega)]
      · apply ih htpos j (by omega)
        intro d hd1 hd2
        exact hagree d (by omega) (by omega)
    rw [hst q (by omega) (by omega), hst (q - 1) (by omega) (by omega),
      hst (q + 1) (by omega) (by omega), hst (q + 2) (by omega) (by omega),
      hst (q + 3) (by omega) (by omega)]
    rw [hagree (q - 2 * t) (by omega) (by omega)]

private lemma secondN_congr_tight {k w1 w2 v r : ℕ} (hk : 2 ≤ k) (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k)
    (hv : v < 2 ^ k) :
    ∀ (t : ℕ), 1 ≤ t → ∀ q : ℕ, max (2 * t + 3) (3 * t + 1) ≤ q →
      (∀ d : ℕ, q - max (2 * t + 3) (3 * t + 1) ≤ d → d ≤ q + 4 * t - 3 →
        w1.testBit (d % k) = w2.testBit (d % k)) →
      (secondN k w1 v r t).testBit (q % k) = (secondN k w2 v r t).testBit (q % k) := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    intro q hq hagree
    have hstep1 : secondN k w1 v r (t + 1) =
        stepFn k (secondN k w1 v r t ^^^ rotFn k 2 (secondN k w1 v r t) ^^^ rotFn k (k - 2) (secondN k w1 v r t)) ^^^
          rotFn k (3 * (t + 1) + 1) w1 ^^^ constFn k (r + (t + 1)) := by
      unfold secondN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hstep2 : secondN k w2 v r (t + 1) =
        stepFn k (secondN k w2 v r t ^^^ rotFn k 2 (secondN k w2 v r t) ^^^ rotFn k (k - 2) (secondN k w2 v r t)) ^^^
          rotFn k (3 * (t + 1) + 1) w2 ^^^ constFn k (r + (t + 1)) := by
      unfold secondN
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep1, hstep2,
      testBit_secondStep hk (secondN_lt hv t) hw1 (by omega) (by omega),
      testBit_secondStep hk (secondN_lt hv t) hw2 (by omega) (by omega)]
    have hst : ∀ j : ℕ, q - 2 ≤ j → j ≤ q + 4 →
        (secondN k w1 v r t).testBit (j % k) = (secondN k w2 v r t).testBit (j % k) := by
      intro j hj1 hj2
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · unfold secondN
        simp only [List.range_zero, List.foldl_nil]
        rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotFn (by omega) hw1 (Nat.mod_lt j (by omega)),
          testBit_rotFn (by omega) hw2 (Nat.mod_lt j (by omega)), mod_sub_shift (by omega) (by omega)]
        rw [hagree (j - 3) (by omega) (by omega)]
      · apply ih htpos j (by omega)
        intro d hd1 hd2
        exact hagree d (by omega) (by omega)
    rw [hst q (by omega) (by omega), hst (q - 2) (by omega) (by omega),
      hst (q + 2) (by omega) (by omega), hst (q + 1) (by omega) (by omega),
      hst (q - 1) (by omega) (by omega), hst (q + 3) (by omega) (by omega),
      hst (q + 4) (by omega) (by omega)]
    rw [hagree (q - (3 * (t + 1) + 1)) (by omega) (by omega)]

private lemma xor_cancel_mid {a b c d : Bool} (h : xor (xor a c) b = xor (xor a d) b) : c = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private lemma first_split_bit {k r w1 w2 u q : ℕ} (hk : 0 < k) (hr : 4 ≤ r)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hu : u < 2 ^ k) (hq : 2 * r - 2 ≤ q)
    (hagree : ∀ d : ℕ, q - (2 * r - 3) ≤ d → d ≤ q + 3 * r - 1 →
      w1.testBit (d % k) = w2.testBit (d % k))
    (heq : (firstN k w1 u r).testBit (q % k) = (firstN k w2 u r).testBit (q % k)) :
    w1.testBit ((q - (2 * r - 2)) % k) = w2.testBit ((q - (2 * r - 2)) % k) := by
  have hr1 : r = (r - 1) + 1 := by omega
  have hstep1 : firstN k w1 u r =
      stepFn k (firstN k w1 u (r - 1) ^^^ rotFn k 1 (firstN k w1 u (r - 1)) ^^^
        rotFn k (k - 1) (firstN k w1 u (r - 1))) ^^^
        rotFn k (2 * (r - 1)) w1 ^^^ constFn k r := by
    conv_lhs => rw [hr1]
    unfold firstN
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have : r - 1 + 1 = r := by omega
    rw [this]
  have hstep2 : firstN k w2 u r =
      stepFn k (firstN k w2 u (r - 1) ^^^ rotFn k 1 (firstN k w2 u (r - 1)) ^^^
        rotFn k (k - 1) (firstN k w2 u (r - 1))) ^^^
        rotFn k (2 * (r - 1)) w2 ^^^ constFn k r := by
    conv_lhs => rw [hr1]
    unfold firstN
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have : r - 1 + 1 = r := by omega
    rw [this]
  rw [hstep1, hstep2,
    testBit_firstStep hk (firstN_lt hu (r - 1)) hw1 (by omega) (by omega),
    testBit_firstStep hk (firstN_lt hu (r - 1)) hw2 (by omega) (by omega)] at heq
  have hst : ∀ j : ℕ, q - 1 ≤ j → j ≤ q + 3 →
      (firstN k w1 u (r - 1)).testBit (j % k) = (firstN k w2 u (r - 1)).testBit (j % k) := by
    intro j hj1 hj2
    apply firstN_congr_tight hk hw1 hw2 hu (r - 1) (by omega) j (by omega)
    intro d hd1 hd2
    exact hagree d (by omega) (by omega)
  rw [hst q (by omega) (by omega), hst (q - 1) (by omega) (by omega),
    hst (q + 1) (by omega) (by omega), hst (q + 2) (by omega) (by omega),
    hst (q + 3) (by omega) (by omega)] at heq
  have h2r : 2 * (r - 1) = 2 * r - 2 := by omega
  rw [h2r] at heq
  exact xor_cancel_mid heq

private lemma second_split_bit {k r w1 w2 v q : ℕ} (hk : 2 ≤ k) (hr : 4 ≤ r)
    (hw1 : w1 < 2 ^ k) (hw2 : w2 < 2 ^ k) (hv : v < 2 ^ k) (hq : 3 * r + 1 ≤ q)
    (hagree : ∀ d : ℕ, q - 3 * r ≤ d → d ≤ q + 4 * r - 3 →
      w1.testBit (d % k) = w2.testBit (d % k))
    (heq : (secondN k w1 v r r).testBit (q % k) = (secondN k w2 v r r).testBit (q % k)) :
    w1.testBit ((q - (3 * r + 1)) % k) = w2.testBit ((q - (3 * r + 1)) % k) := by
  have hstep_gen : ∀ w, secondN k w v r r =
      stepFn k (secondN k w v r (r - 1) ^^^ rotFn k 2 (secondN k w v r (r - 1)) ^^^
        rotFn k (k - 2) (secondN k w v r (r - 1))) ^^^
        rotFn k (3 * ((r - 1) + 1) + 1) w ^^^ constFn k (r + ((r - 1) + 1)) := by
    intro w
    have hr1 : secondN k w v r r = secondN k w v r ((r - 1) + 1) := by
      congr 1
      omega
    rw [hr1]
    unfold secondN
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hstep_gen w1, hstep_gen w2,
    testBit_secondStep hk (secondN_lt hv (r - 1)) hw1 (by omega) (by omega),
    testBit_secondStep hk (secondN_lt hv (r - 1)) hw2 (by omega) (by omega)] at heq
  have hst : ∀ j : ℕ, q - 2 ≤ j → j ≤ q + 4 →
      (secondN k w1 v r (r - 1)).testBit (j % k) = (secondN k w2 v r (r - 1)).testBit (j % k) := by
    intro j hj1 hj2
    apply secondN_congr_tight hk hw1 hw2 hv (r - 1) (by omega) j (by omega)
    intro d hd1 hd2
    exact hagree d (by omega) (by omega)
  rw [hst q (by omega) (by omega), hst (q - 2) (by omega) (by omega),
    hst (q + 2) (by omega) (by omega), hst (q + 1) (by omega) (by omega),
    hst (q - 1) (by omega) (by omega), hst (q + 3) (by omega) (by omega),
    hst (q + 4) (by omega) (by omega)] at heq
  have h3r : 3 * (r - 1 + 1) + 1 = 3 * r + 1 := by omega
  rw [h3r] at heq
  exact xor_cancel_mid heq

private noncomputable def bitsEquivFin (k : ℕ) : Fin (2 ^ k) ≃ (Fin k → Bool) :=
  Equiv.ofBijective (fun a i => a.val.testBit i.val) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro a b h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < k
    · exact congrFun h ⟨i, hi⟩
    · have hpow : 2 ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hpow),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hpow)])

private lemma fiber_structure {k r : ℕ} (hk : 0 < k) (hr : 4 ≤ r) (u v : Fin (2 ^ k)) :
    let h := (k + 1) / 2
    let s := min k (6 * r - 5)
    let atSeed : Fin s → ℕ := fun seedIndex => (k - (2 * r - 2) + seedIndex.val) % k
    let good : Fin (2 ^ k) → Prop := fun tested =>
      firstN k tested.val u.val r < 2 ^ (k - h) ∧ secondN k tested.val v.val r r < 2 ^ (k - h)
    let label : Fin (2 ^ k) → (Fin s → ZMod 2) := fun word site =>
      if word.val.testBit (atSeed site) then (1 : ZMod 2) else 0
    let free := (k - h - (3 * r + 1)) - (4 * r - 3)
    ∀ y : Fin s → ZMod 2,
      let fiber := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => good w ∧ label w = y)
      fiber.Nonempty →
        fiber.card = 2 ^ free ∧
        ∃! key : Fin (2 ^ k), key ∈ fiber ∧ ∀ p : Fin k,
          4 * r - 3 ≤ p.val → p.val < k - h - (3 * r + 1) → key.val.testBit p.val = false := by
  classical
  intro h s atSeed good label free y fiber hne
  have hlbl_eq : ∀ w1 w2 : Fin (2 ^ k), label w1 = label w2 ↔
      ∀ site : Fin s, w1.val.testBit (atSeed site) = w2.val.testBit (atSeed site) := by
    intro w1 w2
    constructor
    · intro heq site
      have h1 := congrFun heq site
      dsimp only [label] at h1
      cases hb1 : w1.val.testBit (atSeed site) <;> cases hb2 : w2.val.testBit (atSeed site) <;> simp_all
    · intro hall
      funext site
      simp only [label, hall site]
  by_cases hsmall : k ≤ 6 * r - 5
  · have hs_eq : s = k := Nat.min_eq_left hsmall
    have hfree0 : free = 0 := by dsimp only [free, h]; omega
    have hvac : ∀ p : Fin k, 4 * r - 3 ≤ p.val → p.val < k - h - (3 * r + 1) → False := by
      intro p h1 h2; dsimp only [h] at h2; omega
    have hinj_lbl : ∀ w1 w2 : Fin (2 ^ k), label w1 = label w2 → w1 = w2 := by
      intro w1 w2 hEq
      rw [hlbl_eq] at hEq
      apply (bitsEquivFin k).injective
      funext i
      let idxVal : ℕ := (i.val + (k - (k - (2 * r - 2)) % k)) % k
      have hidx_lt : idxVal < s := by
        rw [hs_eq]
        exact Nat.mod_lt _ hk
      have hat : atSeed ⟨idxVal, hidx_lt⟩ = i.val := by
        dsimp only [atSeed, idxVal]
        set c := k - (2 * r - 2)
        have h1 : (c + (i.val + (k - c % k)) % k) % k = (c % k + (i.val + (k - c % k))) % k := by
          calc (c + (i.val + (k - c % k)) % k) % k
              = (c % k + (i.val + (k - c % k)) % k % k) % k := Nat.add_mod _ _ _
            _ = (c % k + (i.val + (k - c % k)) % k) % k := by rw [Nat.mod_mod]
            _ = (c % k % k + (i.val + (k - c % k)) % k) % k := by rw [Nat.mod_mod]
            _ = (c % k + (i.val + (k - c % k))) % k := (Nat.add_mod _ _ _).symm
        rw [h1]
        have hcm : c % k < k := Nat.mod_lt c hk
        have h2 : c % k + (i.val + (k - c % k)) = i.val + k := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      have hb := hEq ⟨idxVal, hidx_lt⟩
      rw [hat] at hb
      exact hb
    rcases hne with ⟨w0, hw0⟩
    have hsing : fiber = {w0} := by
      ext w
      simp only [Finset.mem_singleton]
      constructor
      · intro hw
        exact hinj_lbl w w0 (((Finset.mem_filter.mp hw).2.2).trans ((Finset.mem_filter.mp hw0).2.2).symm)
      · rintro rfl
        exact hw0
    refine ⟨by rw [hsing, Finset.card_singleton, hfree0, pow_zero], w0,
      ⟨hw0, fun p h1 h2 => False.elim (hvac p h1 h2)⟩, ?_⟩
    rintro w ⟨hw, _⟩
    rw [hsing, Finset.mem_singleton] at hw
    exact hw
  · have hbig : 6 * r - 5 < k := by omega
    have hs_eq : s = 6 * r - 5 := Nat.min_eq_right (by omega)
    have hat_cov : ∀ p : ℕ, p < k → (p < 4 * r - 3 ∨ k - (2 * r - 2) ≤ p) →
        ∃ site : Fin s, atSeed site = p := by
      intro p hpk hcond
      rcases hcond with hlo | hhi
      · refine ⟨⟨(2 * r - 2) + p, by omega⟩, ?_⟩
        dsimp only [atSeed]
        have h1 : k - (2 * r - 2) + (2 * r - 2 + p) = p + k := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hpk]
      · refine ⟨⟨p - (k - (2 * r - 2)), by omega⟩, ?_⟩
        dsimp only [atSeed]
        have h1 : k - (2 * r - 2) + (p - (k - (2 * r - 2))) = p := by omega
        rw [h1, Nat.mod_eq_of_lt hpk]
    let freeSet : Finset (Fin k) :=
      (Finset.univ : Finset (Fin k)).filter (fun p => 4 * r - 3 ≤ p.val ∧ p.val < k - h - (3 * r + 1))
    have hfreeSet_card : freeSet.card = free := by
      by_cases hle : k - h - (3 * r + 1) ≤ 4 * r - 3
      · have hemp : freeSet = ∅ := by
          ext p
          simp only [freeSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false]
          omega
        rw [hemp, Finset.card_empty]
        dsimp only [free]
        omega
      · conv_rhs => rw [show free = (Finset.univ : Finset (Fin free)).card by simp]
        refine Finset.card_bij (fun (p : Fin k) hp => (⟨p.val - (4 * r - 3), by
          have h1 := (Finset.mem_filter.mp hp).2
          dsimp only [free]
          omega⟩ : Fin free)) ?_ ?_ ?_
        · intro _ _
          exact Finset.mem_univ _
        · intro a ha b hb heq
          have h1 := (Finset.mem_filter.mp ha).2
          have h2 := (Finset.mem_filter.mp hb).2
          have hv : a.val - (4 * r - 3) = b.val - (4 * r - 3) := by
            simpa using congrArg (Fin.val : Fin free → ℕ) heq
          exact Fin.ext (by omega)
        · intro j _
          refine ⟨⟨(4 * r - 3) + j.val, by have := j.isLt; dsimp only [free, h] at *; omega⟩, ?_, ?_⟩
          · simp only [freeSet, Finset.mem_filter, Finset.mem_univ, true_and]
            have := j.isLt
            dsimp only [free] at *
            omega
          · apply Fin.ext
            dsimp only
            omega
    have hfree_inv : ∀ (w1 w2 : Fin (2 ^ k)),
        (∀ p : Fin k, p ∉ freeSet → w1.val.testBit p.val = w2.val.testBit p.val) →
        (good w1 ↔ good w2) ∧ label w1 = label w2 := by
      intro w1 w2 hagree
      by_cases hemp_free : k - h - (3 * r + 1) ≤ 4 * r - 3
      · have hw_eq : w1 = w2 := by
          apply (bitsEquivFin k).injective
          funext p
          exact hagree p (fun hmem => by
            have hp := (Finset.mem_filter.mp hmem).2
            omega)
        subst hw_eq
        exact ⟨Iff.rfl, rfl⟩
      have hnot_free : ∀ t : ℕ, t < k → ¬ (4 * r - 3 ≤ t ∧ t < k - h - (3 * r + 1)) →
          w1.val.testBit t = w2.val.testBit t := by
        intro t htk hnf
        exact hagree ⟨t, htk⟩ (fun hmem => hnf (Finset.mem_filter.mp hmem).2)
      have hlbl : label w1 = label w2 := by
        rw [hlbl_eq]
        intro site
        have hat_lt : atSeed site < k := Nat.mod_lt _ hk
        have hat_nf : ¬ (4 * r - 3 ≤ atSeed site ∧ atSeed site < k - h - (3 * r + 1)) := by
          dsimp only [atSeed]
          have hsi := site.isLt
          by_cases h1 : site.val < 2 * r - 2
          · have h2 : k - (2 * r - 2) + site.val < k := by omega
            rw [Nat.mod_eq_of_lt h2]
            dsimp only [h]
            omega
          · have h2 : k - (2 * r - 2) + site.val = (site.val - (2 * r - 2)) + k := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
        exact hnot_free (atSeed site) hat_lt hat_nf
      have hgood_iff : good w1 ↔ good w2 := by
        dsimp only [good]
        rw [lt_two_pow_iff_testBit_false (firstN_lt u.isLt r) (by dsimp only [h]; omega),
          lt_two_pow_iff_testBit_false (firstN_lt u.isLt r) (by dsimp only [h]; omega),
          lt_two_pow_iff_testBit_false (secondN_lt v.isLt r) (by dsimp only [h]; omega),
          lt_two_pow_iff_testBit_false (secondN_lt v.isLt r) (by dsimp only [h]; omega)]
        have hf_eq : ∀ q : ℕ, k - h ≤ q → q < k →
            (firstN k w1.val u.val r).testBit q = (firstN k w2.val u.val r).testBit q := by
          intro q hq1 hq2
          rw [← Nat.mod_eq_of_lt hq2]
          apply firstN_congr_tight hk w1.isLt w2.isLt u.isLt r (by omega) q (by dsimp only [h] at hq1; omega)
          intro d hd1 hd2
          have hdk : d % k < k := Nat.mod_lt d hk
          apply hnot_free (d % k) hdk
          by_cases hlt : d < k
          · rw [Nat.mod_eq_of_lt hlt]
            omega
          · have h2 : d = (d - k) + k := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
        have hs_eq2 : ∀ q : ℕ, k - h ≤ q → q < k →
            (secondN k w1.val v.val r r).testBit q = (secondN k w2.val v.val r r).testBit q := by
          intro q hq1 hq2
          rw [← Nat.mod_eq_of_lt hq2]
          apply secondN_congr_tight (by omega) w1.isLt w2.isLt v.isLt r (by omega) q
            (by dsimp only [h] at hq1; omega)
          intro d hd1 hd2
          have hdk : d % k < k := Nat.mod_lt d hk
          apply hnot_free (d % k) hdk
          by_cases hlt : d < k
          · rw [Nat.mod_eq_of_lt hlt]
            omega
          · have h2 : d = (d - k) + k := by omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            omega
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨fun q a b => (hf_eq q a b).symm.trans (h1 q a b),
            fun q a b => (hs_eq2 q a b).symm.trans (h2 q a b)⟩
        · rintro ⟨h1, h2⟩
          exact ⟨fun q a b => (hf_eq q a b).trans (h1 q a b),
            fun q a b => (hs_eq2 q a b).trans (h2 q a b)⟩
      exact ⟨hgood_iff, hlbl⟩
    have huniq_nonfree : ∀ w1 w2 : Fin (2 ^ k), w1 ∈ fiber → w2 ∈ fiber →
        (∀ p : Fin k, p ∈ freeSet → w1.val.testBit p.val = w2.val.testBit p.val) → w1 = w2 := by
      intro w1 w2 hw1 hw2 hfree_eq
      have hg1 : good w1 := (Finset.mem_filter.mp hw1).2.1
      have hg2 : good w2 := (Finset.mem_filter.mp hw2).2.1
      have hl12 : label w1 = label w2 :=
        ((Finset.mem_filter.mp hw1).2.2).trans ((Finset.mem_filter.mp hw2).2.2).symm
      rw [hlbl_eq] at hl12
      have hseed : ∀ p : ℕ, p < k → (p < 4 * r - 3 ∨ k - (2 * r - 2) ≤ p) →
          w1.val.testBit p = w2.val.testBit p := by
        intro p hpk hcond
        rcases hat_cov p hpk hcond with ⟨site, hsite⟩
        have hb := hl12 site
        rwa [hsite] at hb
      have hf1 := (lt_two_pow_iff_testBit_false (firstN_lt u.isLt r) (by dsimp only [h]; omega)).mp hg1.1
      have hf2 := (lt_two_pow_iff_testBit_false (firstN_lt u.isLt r) (by dsimp only [h]; omega)).mp hg2.1
      have hs1 := (lt_two_pow_iff_testBit_false (secondN_lt v.isLt r) (by dsimp only [h]; omega)).mp hg1.2
      have hs2 := (lt_two_pow_iff_testBit_false (secondN_lt v.isLt r) (by dsimp only [h]; omega)).mp hg2.2
      have hdown : ∀ m : ℕ, m ≤ k → ∀ p : ℕ, k - m ≤ p → p < k →
          w1.val.testBit p = w2.val.testBit p := by
        intro m
        induction m with
        | zero =>
          intro _ p hp1 hp2
          omega
        | succ m ih =>
          intro hm p hp1 hp2
          by_cases hgt : k - m ≤ p
          · exact ih (by omega) p hgt hp2
          · have hpeq : p = k - (m + 1) := by omega
            by_cases hseed_c : p < 4 * r - 3 ∨ k - (2 * r - 2) ≤ p
            · exact hseed p hp2 hseed_c
            · by_cases hfree_c : p < k - h - (3 * r + 1)
              · exact hfree_eq ⟨p, hp2⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp only; omega, by dsimp only; omega⟩)
              · by_cases huse_first : k - h ≤ p + (2 * r - 2)
                · let q := p + (2 * r - 2)
                  have hqk : q < k := by dsimp only [q]; omega
                  have heq_f : (firstN k w1.val u.val r).testBit (q % k) =
                      (firstN k w2.val u.val r).testBit (q % k) := by
                    rw [Nat.mod_eq_of_lt hqk, hf1 q huse_first hqk, hf2 q huse_first hqk]
                  have hsplit := first_split_bit hk hr w1.isLt w2.isLt u.isLt (q := q) (by omega)
                    (by
                      intro d hd1 hd2
                      by_cases hdk : d < k
                      · rw [Nat.mod_eq_of_lt hdk]
                        exact ih (by omega) d (by dsimp only [q] at *; omega) hdk
                      · have hd_sub : d = (d - k) + k := by omega
                        rw [hd_sub, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q] at *; omega)]
                        exact hseed (d - k) (by dsimp only [q] at *; omega) (Or.inl (by dsimp only [q] at *; omega)))
                    heq_f
                  have hqp : (q - (2 * r - 2)) % k = p := by
                    dsimp only [q]
                    rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt hp2]
                  rwa [hqp] at hsplit
                · let q := p + (3 * r + 1)
                  have hqk : q < k := by dsimp only [q, h] at *; omega
                  have hqh : k - h ≤ q := by dsimp only [q]; omega
                  have heq_s : (secondN k w1.val v.val r r).testBit (q % k) =
                      (secondN k w2.val v.val r r).testBit (q % k) := by
                    rw [Nat.mod_eq_of_lt hqk, hs1 q hqh hqk, hs2 q hqh hqk]
                  have hsplit := second_split_bit (by omega) hr w1.isLt w2.isLt v.isLt (q := q) (by omega)
                    (by
                      intro d hd1 hd2
                      have hdk : d < k := by dsimp only [q, h] at *; omega
                      rw [Nat.mod_eq_of_lt hdk]
                      exact ih (by omega) d (by dsimp only [q] at *; omega) hdk)
                    heq_s
                  have hqp : (q - (3 * r + 1)) % k = p := by
                    dsimp only [q]
                    rw [Nat.add_sub_cancel, Nat.mod_eq_of_lt hp2]
                  rwa [hqp] at hsplit
      apply (bitsEquivFin k).injective
      funext p
      exact hdown k le_rfl p.val (by omega) p.isLt
    rcases hne with ⟨w0, hw0⟩
    have hbij : fiber.card = (Finset.univ : Finset ({p : Fin k // p ∈ freeSet} → Bool)).card := by
      refine Finset.card_bij (fun w _ => fun p : {p : Fin k // p ∈ freeSet} => w.val.testBit p.1.val) ?_ ?_ ?_
      · intro _ _
        exact Finset.mem_univ _
      · intro w1 hw1 w2 hw2 heq
        exact huniq_nonfree w1 w2 hw1 hw2 (fun p hp => congrFun heq ⟨p, hp⟩)
      · intro f _
        let w : Fin (2 ^ k) := (bitsEquivFin k).symm (fun p : Fin k =>
          if hp : p ∈ freeSet then f ⟨p, hp⟩ else w0.val.testBit p.val)
        have hw_bit : ∀ p : Fin k, w.val.testBit p.val =
            if hp : p ∈ freeSet then f ⟨p, hp⟩ else w0.val.testBit p.val := by
          intro p
          exact congrFun ((bitsEquivFin k).apply_symm_apply _) p
        have hsame := hfree_inv w w0 (fun p hp => by rw [hw_bit p]; simp [hp])
        refine ⟨w, ?_, ?_⟩
        · simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
          have hw0_p := (Finset.mem_filter.mp hw0).2
          exact ⟨hsame.1.mpr hw0_p.1, hsame.2.trans hw0_p.2⟩
        · funext ⟨p, hp⟩
          rw [hw_bit p]
          simp [hp]
    refine ⟨?_, ?_⟩
    · rw [hbij, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hfreeSet_card]
    · let key : Fin (2 ^ k) := (bitsEquivFin k).symm (fun p : Fin k =>
        if p ∈ freeSet then false else w0.val.testBit p.val)
      have hkey_bit : ∀ p : Fin k, key.val.testBit p.val =
          if p ∈ freeSet then false else w0.val.testBit p.val := by
        intro p
        exact congrFun ((bitsEquivFin k).apply_symm_apply _) p
      have hsame := hfree_inv key w0 (fun p hp => by rw [hkey_bit p]; simp [hp])
      have hkey_mem : key ∈ fiber := by
        simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and]
        have hw0_p := (Finset.mem_filter.mp hw0).2
        exact ⟨hsame.1.mpr hw0_p.1, hsame.2.trans hw0_p.2⟩
      refine ⟨key, ⟨hkey_mem, fun p h1 h2 => by
        rw [hkey_bit p]
        have hp : p ∈ freeSet := Finset.mem_filter.mpr ⟨Finset.mem_univ p, h1, h2⟩
        simp [hp]⟩, ?_⟩
      rintro w ⟨hw, hw_zero⟩
      refine huniq_nonfree w key hw hkey_mem ?_
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      rw [hw_zero p hp'.1 hp'.2, hkey_bit p]
      simp [hp]

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl h
  · rfl

private lemma zmod2_add_eq_zero_iff (a b : ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [zmod2_add_self, add_zero]
      _ = (a + b) + b := (add_assoc a b b).symm
      _ = b := by rw [h, zero_add]
  · rintro rfl
    exact zmod2_add_self a

private def colReplMat {s : ℕ} (i0 : Fin s) (d : Fin s → ZMod 2) : Matrix (Fin s) (Fin s) (ZMod 2) :=
  Matrix.of (fun r c => if c = i0 then d r else if r = c then 1 else 0)

private lemma colReplMat_mulVec {s : ℕ} (i0 : Fin s) (d v : Fin s → ZMod 2) (r : Fin s) :
    (colReplMat i0 d).mulVec v r = d r * v i0 + (if r = i0 then 0 else v r) := by
  simp only [Matrix.mulVec, dotProduct, colReplMat, Matrix.of_apply]
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i0)]
  simp only [↓reduceIte]
  congr 1
  by_cases hri : r = i0
  · subst hri
    simp only [↓reduceIte]
    refine Finset.sum_eq_zero ?_
    intro c hc
    have hne : c ≠ r := (Finset.mem_erase.mp hc).1
    simp [hne, hne.symm]
  · simp only [hri, ↓reduceIte]
    rw [Finset.sum_eq_single r]
    · simp [hri]
    · intro c hc hcr
      have hci : c ≠ i0 := (Finset.mem_erase.mp hc).1
      simp [hci, hcr.symm]
    · intro hnot
      exact absurd (Finset.mem_erase.mpr ⟨hri, Finset.mem_univ r⟩) hnot

private lemma colReplMat_invol {s : ℕ} (i0 : Fin s) (d : Fin s → ZMod 2) (hd : d i0 = 1)
    (v : Fin s → ZMod 2) :
    (colReplMat i0 d).mulVec ((colReplMat i0 d).mulVec v) = v := by
  funext r
  rw [colReplMat_mulVec, colReplMat_mulVec]
  by_cases hri : r = i0
  · subst hri
    simp [hd]
  · simp only [hri, ↓reduceIte, hd, one_mul, add_zero]
    rw [colReplMat_mulVec]
    simp only [hri, ↓reduceIte]
    rw [← add_assoc, zmod2_add_self, zero_add]

private lemma colReplMat_single {s : ℕ} (i0 : Fin s) (d : Fin s → ZMod 2) (hd : d i0 = 1) :
    (colReplMat i0 d).mulVec (Pi.single i0 (1 : ZMod 2)) = d := by
  funext r
  rw [colReplMat_mulVec]
  by_cases hri : r = i0
  · subst hri
    simp [hd]
  · simp [hri]

private def swapMat {s : ℕ} (i1 i2 : Fin s) : Matrix (Fin s) (Fin s) (ZMod 2) :=
  Matrix.of (fun r c => if c = Equiv.swap i1 i2 r then 1 else 0)

private lemma swapMat_mulVec {s : ℕ} (i1 i2 : Fin s) (v : Fin s → ZMod 2) (r : Fin s) :
    (swapMat i1 i2).mulVec v r = v (Equiv.swap i1 i2 r) := by
  simp only [Matrix.mulVec, dotProduct, swapMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (Equiv.swap i1 i2 r)]
  · simp
  · intro c _ hne
    simp [hne]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

private lemma swapMat_invol {s : ℕ} (i1 i2 : Fin s) (v : Fin s → ZMod 2) :
    (swapMat i1 i2).mulVec ((swapMat i1 i2).mulVec v) = v := by
  funext r
  rw [swapMat_mulVec, swapMat_mulVec, Equiv.swap_apply_self]

private lemma swapMat_single {s : ℕ} (i1 i2 : Fin s) :
    (swapMat i1 i2).mulVec (Pi.single i1 (1 : ZMod 2)) = Pi.single i2 (1 : ZMod 2) := by
  funext r
  rw [swapMat_mulVec]
  by_cases hr : r = i2
  · subst hr
    simp [Equiv.swap_apply_right]
  · have hne : Equiv.swap i1 i2 r ≠ i1 := by
      intro h
      have := congrArg (Equiv.swap i1 i2) h
      simp [Equiv.swap_apply_left] at this
      exact hr this
    simp [hr, hne, Pi.single_eq_of_ne]

private lemma exists_gl_map_vec {s : ℕ} (w1 w2 : Fin s → ZMod 2) (hw1 : w1 ≠ 0) (hw2 : w2 ≠ 0) :
    ∃ Q Qinv : Matrix (Fin s) (Fin s) (ZMod 2),
      Q * Qinv = 1 ∧ Qinv * Q = 1 ∧ Q.mulVec w1 = w2 := by
  have hex1 : ∃ i1 : Fin s, w1 i1 = 1 := by
    by_contra hall
    push Not at hall
    apply hw1
    funext i
    by_contra hne
    exact hall i (zmod2_eq_one_of_ne_zero hne)
  have hex2 : ∃ i2 : Fin s, w2 i2 = 1 := by
    by_contra hall
    push Not at hall
    apply hw2
    funext i
    by_contra hne
    exact hall i (zmod2_eq_one_of_ne_zero hne)
  rcases hex1 with ⟨i1, hi1⟩
  rcases hex2 with ⟨i2, hi2⟩
  let P1 := colReplMat i1 w1
  let S := swapMat i1 i2
  let P2 := colReplMat i2 w2
  let Q := P2 * S * P1
  let Qinv := P1 * S * P2
  have hP1 : P1 * P1 = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, colReplMat_invol i1 w1 hi1, Matrix.one_mulVec]
  have hP2 : P2 * P2 = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, colReplMat_invol i2 w2 hi2, Matrix.one_mulVec]
  have hS : S * S = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, swapMat_invol i1 i2, Matrix.one_mulVec]
  refine ⟨Q, Qinv, ?_, ?_, ?_⟩
  · calc Q * Qinv = P2 * (S * ((P1 * P1) * S)) * P2 := by simp [Q, Qinv, Matrix.mul_assoc]
      _ = P2 * (S * S) * P2 := by rw [hP1, Matrix.one_mul]
      _ = P2 * P2 := by rw [hS, Matrix.mul_one]
      _ = 1 := hP2
  · calc Qinv * Q = P1 * (S * ((P2 * P2) * S)) * P1 := by simp [Q, Qinv, Matrix.mul_assoc]
      _ = P1 * (S * S) * P1 := by rw [hP2, Matrix.one_mul]
      _ = P1 * P1 := by rw [hS, Matrix.mul_one]
      _ = 1 := hP1
  · have h1 : P1.mulVec w1 = Pi.single i1 (1 : ZMod 2) := by
      have h := colReplMat_invol i1 w1 hi1 (Pi.single i1 (1 : ZMod 2))
      rwa [colReplMat_single i1 w1 hi1] at h
    calc Q.mulVec w1 = P2.mulVec (S.mulVec (P1.mulVec w1)) := by
          dsimp only [Q]
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = P2.mulVec (S.mulVec (Pi.single i1 (1 : ZMod 2))) := by rw [h1]
      _ = P2.mulVec (Pi.single i2 (1 : ZMod 2)) := by rw [swapMat_single]
      _ = w2 := colReplMat_single i2 w2 hi2

private lemma card_fin_ge (s j : ℕ) (hj : j ≤ s) :
    ((Finset.univ : Finset (Fin s)).filter (fun i => j ≤ i.val)).card = s - j := by
  have hcomp : ((Finset.univ : Finset (Fin s)).filter (fun i => i.val < j)).card = j := by
    conv_rhs => rw [show j = (Finset.univ : Finset (Fin j)).card by simp]
    refine Finset.card_bij (fun (i : Fin s) hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin j)) ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro a _ b _ h
      exact Fin.ext (congrArg (Fin.val : Fin j → ℕ) h)
    · intro i _
      refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hj⟩, ?_, Fin.ext rfl⟩
      simp [i.isLt]
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin s))) (p := fun i : Fin s => i.val < j)
  rw [Finset.card_univ, Fintype.card_fin, hcomp] at hsum
  have hfilt : (Finset.univ : Finset (Fin s)).filter (fun i => ¬ i.val < j) =
      (Finset.univ : Finset (Fin s)).filter (fun i => j ≤ i.val) := by
    ext i
    simp [not_lt]
  rw [hfilt] at hsum
  omega

private lemma card_vec_prefix_eq {s : ℕ} (j : ℕ) (hj : j ≤ s) (v : Fin s → ZMod 2) :
    ((Finset.univ : Finset (Fin s → ZMod 2)).filter
      (fun x => ∀ i : Fin s, i.val < j → x i = v i)).card = 2 ^ (s - j) := by
  classical
  let F : Finset (Fin s) := (Finset.univ : Finset (Fin s)).filter (fun i => j ≤ i.val)
  have hF : F.card = s - j := card_fin_ge s j hj
  have hbij :
      ((Finset.univ : Finset (Fin s → ZMod 2)).filter
        (fun x => ∀ i : Fin s, i.val < j → x i = v i)).card =
        (Finset.univ : Finset ({i : Fin s // i ∈ F} → ZMod 2)).card := by
    refine Finset.card_bij (fun x _ => fun i : {i : Fin s // i ∈ F} => x i.1) ?_ ?_ ?_
    · intro _ _
      exact Finset.mem_univ _
    · intro x1 hx1 x2 hx2 heq
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      funext i
      by_cases hi : i.val < j
      · exact (h1 i hi).trans (h2 i hi).symm
      · have hiF : i ∈ F := by simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        exact congrFun heq ⟨i, hiF⟩
    · intro f _
      refine ⟨fun i => if hi : i ∈ F then f ⟨i, hi⟩ else v i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        have hni : i ∉ F := by simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]; omega
        simp [hni]
      · funext ⟨i, hi⟩
        simp [hi]
  rw [hbij, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_coe, hF]

private lemma cell_card_of_gl {s : ℕ} (A : Matrix (Fin s) (Fin s) (ZMod 2))
    (hA : Function.Injective A.mulVec) (b : Fin s → ZMod 2) (j : ℕ) (hj : j ≤ s) :
    ((Finset.univ : Finset (Fin s → ZMod 2)).filter
      (fun x => ∀ i : Fin s, i.val < j → A.mulVec x i = b i)).card = 2 ^ (s - j) := by
  classical
  have hbijA : Function.Bijective A.mulVec :=
    (Fintype.bijective_iff_injective_and_card A.mulVec).mpr ⟨hA, rfl⟩
  let e : (Fin s → ZMod 2) ≃ (Fin s → ZMod 2) := Equiv.ofBijective A.mulVec hbijA
  have hcard :
      ((Finset.univ : Finset (Fin s → ZMod 2)).filter
        (fun x => ∀ i : Fin s, i.val < j → A.mulVec x i = b i)).card =
        ((Finset.univ : Finset (Fin s → ZMod 2)).filter
          (fun y => ∀ i : Fin s, i.val < j → y i = b i)).card := by
    refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    · intro x1 _ x2 _ heq
      exact e.injective heq
    · intro y hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have he : A.mulVec (e.symm y) = y := e.apply_symm_apply y
      rwa [he]
  rw [hcard, card_vec_prefix_eq j hj b]

private lemma gl_prefix_zero_bound {s : ℕ} (j : ℕ) (hj : j ≤ s) (d : Fin s → ZMod 2) (hd : d ≠ 0) :
    let GLs := (Finset.univ : Finset (Matrix (Fin s) (Fin s) (ZMod 2))).filter
      (fun A => Function.Injective A.mulVec)
    2 ^ j * (GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).card ≤ GLs.card := by
  classical
  intro GLs
  let NZ : Finset (Fin s → ZMod 2) := (Finset.univ : Finset (Fin s → ZMod 2)).filter (fun w => w ≠ 0)
  have hNZ_card : NZ.card = 2 ^ s - 1 := by
    have h0 : (0 : Fin s → ZMod 2) ∈ (Finset.univ : Finset (Fin s → ZMod 2)) := Finset.mem_univ 0
    have heq : NZ = (Finset.univ : Finset (Fin s → ZMod 2)).erase 0 := by
      ext w
      simp [NZ]
    rw [heq, Finset.card_erase_of_mem h0, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hfiber_eq : ∀ w1 ∈ NZ, ∀ w2 ∈ NZ,
      (GLs.filter (fun A => A.mulVec d = w1)).card = (GLs.filter (fun A => A.mulVec d = w2)).card := by
    intro w1 hw1 w2 hw2
    rcases exists_gl_map_vec w1 w2 (Finset.mem_filter.mp hw1).2 (Finset.mem_filter.mp hw2).2 with
      ⟨Q, Qinv, hQQ, hQiQ, hQw⟩
    have hQinj : Function.Injective Q.mulVec := by
      intro x y hxy
      have := congrArg Qinv.mulVec hxy
      simpa [Matrix.mulVec_mulVec, hQiQ] using this
    have hQiinj : Function.Injective Qinv.mulVec := by
      intro x y hxy
      have := congrArg Q.mulVec hxy
      simpa [Matrix.mulVec_mulVec, hQQ] using this
    refine Finset.card_bij (fun A _ => Q * A) ?_ ?_ ?_
    · intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAGL, hAd⟩
      have hAinj := (Finset.mem_filter.mp hAGL).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro x y hxy
        apply hAinj
        apply hQinj
        simpa [← Matrix.mulVec_mulVec] using hxy
      · rw [← Matrix.mulVec_mulVec, hAd, hQw]
    · intro A1 _ A2 _ heq
      have := congrArg (fun M => Qinv * M) heq
      simpa [← Matrix.mul_assoc, hQiQ] using this
    · intro B hB
      rcases Finset.mem_filter.mp hB with ⟨hBGL, hBd⟩
      have hBinj := (Finset.mem_filter.mp hBGL).2
      refine ⟨Qinv * B, ?_, by rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · intro x y hxy
        apply hBinj
        apply hQiinj
        simpa [← Matrix.mulVec_mulVec] using hxy
      · rw [← Matrix.mulVec_mulVec, hBd]
        have := congrArg Qinv.mulVec hQw
        simpa [Matrix.mulVec_mulVec, hQiQ] using this.symm
  have hdNZ : d ∈ NZ := by simp [NZ, hd]
  let C := (GLs.filter (fun A => A.mulVec d = d)).card
  have hGL_eq : GLs.card = (2 ^ s - 1) * C := by
    have hmaps : ∀ A ∈ GLs, A.mulVec d ∈ NZ := by
      intro A hA
      have hAinj := (Finset.mem_filter.mp hA).2
      simp only [NZ, Finset.mem_filter, Finset.mem_univ, true_and]
      intro h0
      apply hd
      apply hAinj
      rw [h0, Matrix.mulVec_zero]
    have hpart := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hpart]
    have hterm : ∀ w ∈ NZ, (GLs.filter (fun A => A.mulVec d = w)).card = C :=
      fun w hw => hfiber_eq w hw d hdNZ
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hNZ_card]
  let NZ0 : Finset (Fin s → ZMod 2) := NZ.filter (fun w => ∀ i : Fin s, i.val < j → w i = 0)
  have hNZ0_card : NZ0.card = 2 ^ (s - j) - 1 := by
    have h0 : (0 : Fin s → ZMod 2) ∈
        (Finset.univ : Finset (Fin s → ZMod 2)).filter (fun w => ∀ i : Fin s, i.val < j → w i = 0) := by
      simp
    have heq : NZ0 =
        ((Finset.univ : Finset (Fin s → ZMod 2)).filter
          (fun w => ∀ i : Fin s, i.val < j → w i = 0)).erase 0 := by
      ext w
      simp only [NZ0, NZ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    have hcard0 := card_vec_prefix_eq j hj (0 : Fin s → ZMod 2)
    simp only [Pi.zero_apply] at hcard0
    rw [heq, Finset.card_erase_of_mem h0, hcard0]
  have hsub_eq : (GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).card =
      (2 ^ (s - j) - 1) * C := by
    have hmaps : ∀ A ∈ GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0),
        A.mulVec d ∈ NZ0 := by
      intro A hA
      rcases Finset.mem_filter.mp hA with ⟨hAGL, hAp⟩
      have hAinj := (Finset.mem_filter.mp hAGL).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hAp⟩
      intro h0
      apply hd
      apply hAinj
      rw [h0, Matrix.mulVec_zero]
    have hpart := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hpart]
    have hterm : ∀ w ∈ NZ0,
        ((GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).filter
          (fun A => A.mulVec d = w)).card = C := by
      intro w hw
      have hwNZ : w ∈ NZ := (Finset.mem_filter.mp hw).1
      have hw0 : ∀ i : Fin s, i.val < j → w i = 0 := (Finset.mem_filter.mp hw).2
      have hfilt : (GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).filter
          (fun A => A.mulVec d = w) = GLs.filter (fun A => A.mulVec d = w) := by
        ext A
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, fun i hi => by rw [h2]; exact hw0 i hi⟩, h2⟩
      rw [hfilt]
      exact hfiber_eq w hwNZ d hdNZ
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hNZ0_card]
  rw [hGL_eq, hsub_eq, ← mul_assoc]
  have hpow : 2 ^ j * (2 ^ (s - j) - 1) ≤ 2 ^ s - 1 := by
    have h1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (s - j) := Nat.one_le_two_pow
    have h3 : 2 ^ j * 2 ^ (s - j) = 2 ^ s := by rw [← pow_add, Nat.add_sub_of_le hj]
    rw [Nat.mul_sub_left_distrib, mul_one, h3]
    omega
  exact Nat.mul_le_mul_right C hpow

private lemma flag_isolation_bound {s : ℕ} (labels : Finset (Fin s → ZMod 2)) (hM : 0 < labels.card) :
    let V := Fin s → ZMod 2
    let Flag := Matrix (Fin s) (Fin s) (ZMod 2) × V
    let flags := (Finset.univ : Finset Flag).filter (fun g => Function.Injective g.1.mulVec)
    let cell := fun (flag : Flag) (j : ℕ) (x : V) =>
      ∀ i : Fin s, i.val < j → flag.1.mulVec x i = flag.2 i
    ∃ j : ℕ, j ≤ s ∧ (j = s ∨ 3 * labels.card ≤ 2 * 2 ^ j) ∧ 2 ^ j < 3 * labels.card ∧
      2 * flags.card ≤ 9 * (flags.filter (fun draw => (labels.filter (cell draw j)).card = 1)).card := by
  classical
  intro V Flag flags cell
  let GLs : Finset (Matrix (Fin s) (Fin s) (ZMod 2)) :=
    (Finset.univ : Finset (Matrix (Fin s) (Fin s) (ZMod 2))).filter (fun A => Function.Injective A.mulVec)
  have hflags_prod : flags = GLs ×ˢ (Finset.univ : Finset V) := by
    ext ⟨A, b⟩
    dsimp only [flags, GLs]
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_filter]
    simp
  have hflags_card : flags.card = GLs.card * 2 ^ s := by
    rw [hflags_prod, Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  have hMle : labels.card ≤ 2 ^ s := by
    calc labels.card ≤ (Finset.univ : Finset V).card := Finset.card_le_univ _
      _ = 2 ^ s := by simp [V, ZMod.card]
  have hex_j : ∃ j : ℕ, j ≤ s ∧ (j = s ∨ 3 * labels.card ≤ 2 * 2 ^ j) ∧ 2 ^ j < 3 * labels.card := by
    by_cases hcap : 2 * 2 ^ s < 3 * labels.card
    · exact ⟨s, le_rfl, Or.inl rfl, by omega⟩
    · have hle_s : 3 * labels.card ≤ 2 * 2 ^ s := by omega
      have hrec : ∀ t : ℕ, 3 * labels.card ≤ 2 * 2 ^ t →
          ∃ j : ℕ, j ≤ t ∧ 3 * labels.card ≤ 2 * 2 ^ j ∧ 2 ^ j < 3 * labels.card := by
        intro t
        induction t with
        | zero =>
          intro h0
          simp at h0
          omega
        | succ t ih =>
          intro ht
          by_cases hprev : 3 * labels.card ≤ 2 * 2 ^ t
          · rcases ih hprev with ⟨j, hj1, hj2, hj3⟩
            exact ⟨j, by omega, hj2, hj3⟩
          · refine ⟨t + 1, le_rfl, ht, ?_⟩
            rw [pow_succ, mul_comm]
            omega
      rcases hrec s hle_s with ⟨j, hj1, hj2, hj3⟩
      exact ⟨j, hj1, Or.inr hj2, hj3⟩
  rcases hex_j with ⟨j, hjs, hj_or, hj_lt⟩
  refine ⟨j, hjs, hj_or, hj_lt, ?_⟩
  have hsingle : ∀ x : V,
      2 ^ j * (flags.filter (fun g => cell g j x)).card = flags.card := by
    intro x
    have hsum : (flags.filter (fun g => cell g j x)).card =
        ∑ A ∈ GLs, ((Finset.univ : Finset V).filter (fun b => cell (A, b) j x)).card := by
      rw [hflags_prod, Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro A _
      rw [Finset.card_filter]
    have hinner : ∀ A ∈ GLs,
        ((Finset.univ : Finset V).filter (fun b => cell (A, b) j x)).card = 2 ^ (s - j) := by
      intro A _
      have heq : (Finset.univ : Finset V).filter (fun b => cell (A, b) j x) =
          (Finset.univ : Finset V).filter (fun b => ∀ i : Fin s, i.val < j → b i = A.mulVec x i) := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, cell]
        exact ⟨fun h i hi => (h i hi).symm, fun h i hi => (h i hi).symm⟩
      rw [heq, card_vec_prefix_eq j hjs (A.mulVec x)]
    rw [hsum, Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul, hflags_card]
    calc 2 ^ j * (GLs.card * 2 ^ (s - j)) = GLs.card * (2 ^ j * 2 ^ (s - j)) := by ring
      _ = GLs.card * 2 ^ s := by rw [← pow_add, Nat.add_sub_of_le hjs]
  by_cases hj_cap : j = s ∧ 2 * 2 ^ s < 3 * labels.card
  · rcases hj_cap with ⟨hjs_eq, hcap⟩
    subst j
    have hcard_eq : (flags.filter (fun draw => (labels.filter (cell draw s)).card = 1)).card =
        GLs.card * labels.card := by
      rw [hflags_prod, Finset.card_filter, Finset.sum_product]
      have hinner : ∀ A ∈ GLs,
          (∑ b : V, if (labels.filter (cell (A, b) s)).card = 1 then (1 : ℕ) else 0) = labels.card := by
        intro A hA
        have hAinj := (Finset.mem_filter.mp hA).2
        have hbijA : Function.Bijective A.mulVec :=
          (Fintype.bijective_iff_injective_and_card A.mulVec).mpr ⟨hAinj, rfl⟩
        let e : V ≃ V := Equiv.ofBijective A.mulVec hbijA
        rw [← Finset.card_filter]
        have hset : (Finset.univ : Finset V).filter (fun b => (labels.filter (cell (A, b) s)).card = 1) =
            labels.image e := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          have hcell_iff : ∀ x : V, cell (A, b) s x ↔ x = e.symm b := by
            intro x
            constructor
            · intro hc
              apply e.injective
              rw [e.apply_symm_apply]
              funext i
              exact hc i i.isLt
            · rintro rfl i _
              exact congrFun (e.apply_symm_apply b) i
          have hfilt_eq : labels.filter (cell (A, b) s) = labels.filter (fun x => x = e.symm b) := by
            ext x
            simp [hcell_iff]
          rw [hfilt_eq]
          by_cases hmem : e.symm b ∈ labels
          · have hsing : labels.filter (fun x => x = e.symm b) = {e.symm b} := by
              ext x
              simp only [Finset.mem_filter, Finset.mem_singleton]
              exact ⟨fun h => h.2, fun h => ⟨h ▸ hmem, h⟩⟩
            rw [hsing, Finset.card_singleton]
            exact ⟨fun _ => ⟨e.symm b, hmem, e.apply_symm_apply b⟩, fun _ => rfl⟩
          · have hemp : labels.filter (fun x => x = e.symm b) = ∅ := by
              ext x
              simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
              intro hx hxe
              exact hmem (hxe ▸ hx)
            rw [hemp, Finset.card_empty]
            constructor
            · intro h; omega
            · rintro ⟨x, hx, rfl⟩
              exact absurd (by simpa using hx) hmem
        rw [hset, Finset.card_image_of_injective _ e.injective]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    rw [hflags_card, hcard_eq]
    have h1 : 2 * 2 ^ s ≤ 9 * labels.card := by omega
    calc 2 * (GLs.card * 2 ^ s) = GLs.card * (2 * 2 ^ s) := by ring
      _ ≤ GLs.card * (9 * labels.card) := Nat.mul_le_mul_left _ h1
      _ = 9 * (GLs.card * labels.card) := by ring
  · have hMupper : 3 * labels.card ≤ 2 * 2 ^ j := by
      rcases hj_or with rfl | hle
      · omega
      · exact hle
    have hpair : ∀ x y : V, x ≠ y →
        2 ^ (2 * j) * (flags.filter (fun g => cell g j x ∧ cell g j y)).card ≤ flags.card := by
      intro x y hxy
      let d : V := x + y
      have hd : d ≠ 0 := by
        intro h0
        apply hxy
        funext i
        exact (zmod2_add_eq_zero_iff (x i) (y i)).mp (congrFun h0 i)
      have hiff : ∀ (A : Matrix (Fin s) (Fin s) (ZMod 2)) (b : V),
          (cell (A, b) j x ∧ cell (A, b) j y) ↔
            (∀ i : Fin s, i.val < j → A.mulVec d i = 0) ∧
            (∀ i : Fin s, i.val < j → b i = A.mulVec x i) := by
        intro A b
        have hadd : A.mulVec d = A.mulVec x + A.mulVec y := Matrix.mulVec_add A x y
        constructor
        · rintro ⟨hx, hy⟩
          refine ⟨fun i hi => ?_, fun i hi => (hx i hi).symm⟩
          rw [hadd, Pi.add_apply, hx i hi, hy i hi, zmod2_add_self]
        · rintro ⟨h0, hx⟩
          refine ⟨fun i hi => (hx i hi).symm, fun i hi => ?_⟩
          have h1 := h0 i hi
          rw [hadd, Pi.add_apply] at h1
          have hxy_i := (zmod2_add_eq_zero_iff _ _).mp h1
          rw [← hxy_i, ← hx i hi]
      have hcard_pair :
          (flags.filter (fun g => cell g j x ∧ cell g j y)).card =
            (GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).card * 2 ^ (s - j) := by
        rw [hflags_prod, Finset.card_filter, Finset.sum_product]
        have hinner : ∀ A ∈ GLs,
            (∑ b : V, if cell (A, b) j x ∧ cell (A, b) j y then (1 : ℕ) else 0) =
              if ∀ i : Fin s, i.val < j → A.mulVec d i = 0 then 2 ^ (s - j) else 0 := by
          intro A _
          simp_rw [hiff A]
          by_cases hA0 : ∀ i : Fin s, i.val < j → A.mulVec d i = 0
          · have hP : (∀ i : Fin s, i.val < j → A.mulVec d i = 0) ↔ True := iff_true_intro hA0
            simp only [hP, true_and, ↓reduceIte]
            rw [← Finset.card_filter]
            exact card_vec_prefix_eq j hjs (A.mulVec x)
          · have hP : (∀ i : Fin s, i.val < j → A.mulVec d i = 0) ↔ False := iff_false_intro hA0
            simp only [hP, false_and, ↓reduceIte, Finset.sum_const_zero]
        rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [hcard_pair, hflags_card]
      have hgl := gl_prefix_zero_bound j hjs d hd
      calc 2 ^ (2 * j) * ((GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).card * 2 ^ (s - j))
          = (2 ^ j * (GLs.filter (fun A => ∀ i : Fin s, i.val < j → A.mulVec d i = 0)).card) *
              (2 ^ j * 2 ^ (s - j)) := by
              rw [show 2 * j = j + j by omega, pow_add]
              ring
        _ ≤ GLs.card * (2 ^ j * 2 ^ (s - j)) := Nat.mul_le_mul_right _ hgl
        _ = GLs.card * 2 ^ s := by rw [← pow_add, Nat.add_sub_of_le hjs]
    let M : ℕ := labels.card
    let P : ℕ := 2 ^ j
    let N : Flag → ℕ := fun g => (labels.filter (cell g j)).card
    have hfirst : P * ∑ g ∈ flags, N g = M * flags.card := by
      have hswap : ∑ g ∈ flags, N g = ∑ x ∈ labels, (flags.filter (fun g => cell g j x)).card := by
        simp_rw [N, Finset.card_filter]
        exact Finset.sum_comm
      rw [hswap, Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun x _ => hsingle x)]
      simp [M]
    have hsecond : P ^ 2 * ∑ g ∈ flags, N g * (N g - 1) ≤ M * (M - 1) * flags.card := by
      have hpair_sum : ∀ g ∈ flags,
          N g * (N g - 1) = ∑ x ∈ labels, ∑ y ∈ labels.erase x,
            if cell g j x ∧ cell g j y then 1 else 0 := by
        intro g _
        let B := labels.filter (cell g j)
        have h1 : B.card * (B.card - 1) = ∑ x ∈ B, (B.erase x).card := by
          rw [Finset.sum_congr rfl (fun x hx => Finset.card_erase_of_mem hx)]
          simp
        have h2 : ∑ x ∈ B, (B.erase x).card =
            ∑ x ∈ labels, ∑ y ∈ labels.erase x, if cell g j x ∧ cell g j y then 1 else 0 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro x _
          by_cases hx : cell g j x
          · have hP : (∀ i : Fin s, i.val < j → g.1.mulVec x i = g.2 i) ↔ True := iff_true_intro hx
            simp only [cell, hP, true_and, ↓reduceIte]
            rw [← Finset.card_filter]
            congr 1
            ext y
            simp only [B, Finset.mem_erase, Finset.mem_filter, cell]
            tauto
          · have hP : (∀ i : Fin s, i.val < j → g.1.mulVec x i = g.2 i) ↔ False := iff_false_intro hx
            simp only [cell, hP, false_and, ↓reduceIte, Finset.sum_const_zero]
        exact h1.trans h2
      rw [Finset.sum_congr rfl hpair_sum, Finset.sum_comm]
      have hcomm : ∀ x ∈ labels,
          (∑ g ∈ flags, ∑ y ∈ labels.erase x, if cell g j x ∧ cell g j y then 1 else 0) =
            ∑ y ∈ labels.erase x, ∑ g ∈ flags, if cell g j x ∧ cell g j y then 1 else 0 :=
        fun _ _ => Finset.sum_comm
      rw [Finset.sum_congr rfl hcomm, Finset.mul_sum]
      have houter : ∀ x ∈ labels,
          P ^ 2 * (∑ y ∈ labels.erase x, ∑ g ∈ flags, if cell g j x ∧ cell g j y then 1 else 0) ≤
            (M - 1) * flags.card := by
        intro x hx
        have hinner : ∀ y ∈ labels.erase x,
            P ^ 2 * (∑ g ∈ flags, if cell g j x ∧ cell g j y then 1 else 0) ≤ flags.card := by
          intro y hy
          have hne : x ≠ y := (Finset.mem_erase.mp hy).1.symm
          rw [← Finset.card_filter]
          have hP2 : P ^ 2 = 2 ^ (2 * j) := by dsimp only [P]; rw [← pow_mul, mul_comm]
          rw [hP2]
          exact hpair x y hne
        calc P ^ 2 * (∑ y ∈ labels.erase x, ∑ g ∈ flags, if cell g j x ∧ cell g j y then 1 else 0)
            = ∑ y ∈ labels.erase x, P ^ 2 * (∑ g ∈ flags, if cell g j x ∧ cell g j y then 1 else 0) :=
              Finset.mul_sum _ _ _
          _ ≤ ∑ _y ∈ labels.erase x, flags.card := Finset.sum_le_sum hinner
          _ = (M - 1) * flags.card := by simp [Finset.card_erase_of_mem hx, M]
      calc ∑ x ∈ labels, P ^ 2 * (∑ y ∈ labels.erase x, ∑ g ∈ flags, if cell g j x ∧ cell g j y then 1 else 0)
          ≤ ∑ _x ∈ labels, (M - 1) * flags.card := Finset.sum_le_sum houter
        _ = M * (M - 1) * flags.card := by simp [M, mul_assoc]
    have hpt : ∀ g ∈ flags, N g ≤ (if N g = 1 then 1 else 0) + N g * (N g - 1) := by
      intro g _
      rcases Nat.eq_zero_or_pos (N g) with h0 | hpos
      · simp [h0]
      · by_cases h1 : N g = 1
        · simp [h1]
        · have h2 : 2 ≤ N g := by omega
          have hmul : N g ≤ N g * (N g - 1) := by
            calc N g = N g * 1 := (mul_one _).symm
              _ ≤ N g * (N g - 1) := Nat.mul_le_mul_left _ (by omega)
          omega
    have hsum_ineq :
        ∑ g ∈ flags, N g ≤
          (flags.filter (fun g => N g = 1)).card + ∑ g ∈ flags, N g * (N g - 1) := by
      have h := Finset.sum_le_sum hpt
      rw [Finset.sum_add_distrib, ← Finset.card_filter] at h
      exact h
    have hmul_ineq :
        P * (M * flags.card) ≤
          P ^ 2 * (flags.filter (fun g => N g = 1)).card + M * (M - 1) * flags.card := by
      have h := Nat.mul_le_mul_left (P ^ 2) hsum_ineq
      rw [mul_add] at h
      have hL : P ^ 2 * ∑ g ∈ flags, N g = P * (M * flags.card) := by
        calc P ^ 2 * ∑ g ∈ flags, N g = P * (P * ∑ g ∈ flags, N g) := by ring
          _ = P * (M * flags.card) := by rw [hfirst]
      rw [hL] at h
      exact le_trans h (Nat.add_le_add_left hsecond _)
    have hquad : 2 * P ^ 2 + 9 * (M * (M - 1)) ≤ 9 * (P * M) := by
      have h1 : P < 3 * M := hj_lt
      have h2 : 3 * M ≤ 2 * P := hMupper
      have hsub : M * (M - 1) ≤ M * M := Nat.mul_le_mul_left M (Nat.sub_le M 1)
      have hpoly : 2 * P ^ 2 + 9 * (M * M) ≤ 9 * (P * M) := by
        zify
        nlinarith
      omega
    have hstep1 :
        2 * P ^ 2 * flags.card + 9 * (M * (M - 1) * flags.card) ≤
          9 * (P * (M * flags.card)) := by
      have h := Nat.mul_le_mul_right flags.card hquad
      calc 2 * P ^ 2 * flags.card + 9 * (M * (M - 1) * flags.card)
          = (2 * P ^ 2 + 9 * (M * (M - 1))) * flags.card := by ring
        _ ≤ 9 * (P * M) * flags.card := h
        _ = 9 * (P * (M * flags.card)) := by ring
    have hstep2 :
        9 * (P * (M * flags.card)) ≤
          9 * (P ^ 2 * (flags.filter (fun g => N g = 1)).card) + 9 * (M * (M - 1) * flags.card) := by
      have h := Nat.mul_le_mul_left 9 hmul_ineq
      linarith
    have hstep3 : P ^ 2 * (2 * flags.card) ≤ P ^ 2 * (9 * (flags.filter (fun g => N g = 1)).card) := by
      linarith
    exact Nat.le_of_mul_le_mul_left hstep3 (by positivity)

private lemma pow_union_bound_25641 (k : ℕ) :
    (2 ^ k) * (2 ^ k) * 7 ^ (3 * (2 * k + 1)) < 9 ^ (3 * (2 * k + 1)) := by
  have hbase : 2 * 7 ^ 3 < 9 ^ 3 := by decide
  have h79 : 7 ^ 3 < 9 ^ 3 := by decide
  have h2k : 2 ^ (2 * k) * (7 ^ 3) ^ (2 * k) ≤ (9 ^ 3) ^ (2 * k) := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (le_of_lt hbase) (2 * k)
  have hpow2 : (2 ^ k) * (2 ^ k) = 2 ^ (2 * k) := by
    rw [← pow_add, show k + k = 2 * k by omega]
  rw [hpow2]
  calc 2 ^ (2 * k) * 7 ^ (3 * (2 * k + 1))
      = (2 ^ (2 * k) * (7 ^ 3) ^ (2 * k)) * 7 ^ 3 := by
        rw [mul_add, mul_one, pow_add, pow_mul 7 3 (2 * k), mul_assoc]
    _ < (9 ^ 3) ^ (2 * k) * 9 ^ 3 := by
        calc (2 ^ (2 * k) * (7 ^ 3) ^ (2 * k)) * 7 ^ 3
            ≤ (9 ^ 3) ^ (2 * k) * 7 ^ 3 := Nat.mul_le_mul_right _ h2k
          _ < (9 ^ 3) ^ (2 * k) * 9 ^ 3 := Nat.mul_lt_mul_of_pos_left h79 (by positivity)
    _ = 9 ^ (3 * (2 * k + 1)) := by
        rw [mul_add, mul_one, pow_add, pow_mul 9 3 (2 * k)]

end PEqualNP.Outside.L_meta_25641_aux

theorem PEqualNP.Outside.L_meta_25641 : ∀ (k r : ℕ), 0 < k → 4 ≤ r →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (roundNo : Nat) => 3 ^ (k + roundNo) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let h := (k + 1) / 2
  let s := min k (6 * r - 5)
  let atSeed := fun seedIndex : Fin s => (k - (2 * r - 2) + seedIndex.val) % k
  let good := fun (rowNm colNm tested : Fin (2 ^ k)) =>
    first tested.val rowNm.val < 2 ^ (k - h) ∧ second tested.val colNm.val < 2 ^ (k - h)
  let V := Fin s → ZMod 2
  let Flag := Matrix (Fin s) (Fin s) (ZMod 2) × V
  let flags := Finset.univ.filter (fun g : Flag => Function.Injective g.1.mulVec)
  let label := fun (word : Fin (2^k)) (site : Fin s) =>
    if word.val.testBit (atSeed site) then (1 : ZMod 2) else 0
  let cell := fun (flag : Flag) (j : Nat) (x : V) =>
    ∀ i : Fin s, i.val < j → flag.1.mulVec x i = flag.2 i
  let free := (k-h-(3*r+1))-(4*r-3)
  ∃ panel : Fin (3*(2*k+1)) → Flag, (∀ slot, panel slot ∈ flags) ∧
    ∀ u v : Fin (2^k),
      let raw := Finset.univ.filter (good u v)
      let labels := raw.image label
      let M := labels.card
      0 < M → ∃ j : Nat, j ≤ s ∧ (j = s ∨ 3*M ≤ 2*2^j) ∧ 2^j < 3*M ∧
        2*flags.card ≤ 9*(flags.filter (fun draw => (labels.filter (cell draw j)).card = 1)).card ∧
        ∃ trial : Fin (3*(2*k+1)),
          let chosen := panel trial
          let kept := raw.filter (fun cand => cell chosen j (label cand))
          (Finset.univ.filter (cell chosen j)).card = 2^(s-j) ∧
          (kept.image label).card = 1 ∧ kept.card = 2^free ∧
          ∃! key : Fin (2^k), key ∈ kept ∧ ∀ p : Fin k,
            4*r-3 ≤ p.val → p.val < k-h-(3*r+1) → key.val.testBit p.val = false := by
  classical
  intro k r hk hr rot step constant first second h s atSeed good V Flag flags label cell free
  let t : ℕ := 3 * (2 * k + 1)
  have hflags_ne : flags.Nonempty := by
    refine ⟨(1, 0), ?_⟩
    simp only [flags, Finset.mem_filter, Finset.mem_univ, true_and]
    intro x y hxy
    simpa [Matrix.one_mulVec] using hxy
  have hflags_pos : 0 < flags.card := Finset.card_pos.mpr hflags_ne
  have hchoose_j : ∀ uv : Fin (2 ^ k) × Fin (2 ^ k),
      ∃ j : ℕ,
        let raw := Finset.univ.filter (good uv.1 uv.2)
        let labels := raw.image label
        0 < labels.card →
          j ≤ s ∧ (j = s ∨ 3 * labels.card ≤ 2 * 2 ^ j) ∧ 2 ^ j < 3 * labels.card ∧
          2 * flags.card ≤ 9 * (flags.filter (fun draw => (labels.filter (cell draw j)).card = 1)).card := by
    intro uv
    let raw := Finset.univ.filter (good uv.1 uv.2)
    let labels := raw.image label
    by_cases hM : 0 < labels.card
    · rcases PEqualNP.Outside.L_meta_25641_aux.flag_isolation_bound labels hM with ⟨j, hj1, hj2, hj3, hj4⟩
      exact ⟨j, fun _ => ⟨hj1, hj2, hj3, hj4⟩⟩
    · exact ⟨0, fun hpos => False.elim (hM hpos)⟩
  choose J hJ using hchoose_j
  let badDraws : Fin (2 ^ k) × Fin (2 ^ k) → Finset Flag := fun uv =>
    let raw := Finset.univ.filter (good uv.1 uv.2)
    let labels := raw.image label
    if 0 < labels.card then
      flags.filter (fun draw => (labels.filter (cell draw (J uv))).card ≠ 1)
    else ∅
  have hbad_sub : ∀ uv, badDraws uv ⊆ flags := by
    intro uv
    dsimp only [badDraws]
    split_ifs
    · exact Finset.filter_subset _ _
    · exact Finset.empty_subset _
  have hbad_card : ∀ uv, 9 * (badDraws uv).card ≤ 7 * flags.card := by
    intro uv
    dsimp only [badDraws]
    split_ifs with hM
    · have hgood := (hJ uv hM).2.2.2
      have hcomp := Finset.card_filter_add_card_filter_not (s := flags)
        (p := fun draw => (((Finset.univ.filter (good uv.1 uv.2)).image label).filter (cell draw (J uv))).card = 1)
      change 9 * (flags.filter (fun draw =>
        ¬ (((Finset.univ.filter (good uv.1 uv.2)).image label).filter (cell draw (J uv))).card = 1)).card ≤
        7 * flags.card
      omega
    · simp
  let allPanels : Finset (Fin t → Flag) := Fintype.piFinset (fun _ : Fin t => flags)
  let miss : Fin (2 ^ k) × Fin (2 ^ k) → Finset (Fin t → Flag) := fun uv =>
    Fintype.piFinset (fun _ : Fin t => badDraws uv)
  have hmiss_sub : ∀ uv, miss uv ⊆ allPanels := by
    intro uv p hp
    rw [Fintype.mem_piFinset] at hp ⊢
    intro slot
    exact hbad_sub uv (hp slot)
  have hmiss_bound : ∀ uv, 9 ^ t * (miss uv).card ≤ 7 ^ t * flags.card ^ t := by
    intro uv
    have hcard : (miss uv).card = (badDraws uv).card ^ t := by
      dsimp only [miss]
      rw [Fintype.card_piFinset]
      simp
    rw [hcard, ← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left (hbad_card uv) t
  have hall_card : allPanels.card = flags.card ^ t := by
    dsimp only [allPanels]
    rw [Fintype.card_piFinset]
    simp
  have hbi_lt : (Finset.univ.biUnion miss).card < allPanels.card := by
    have h1 : 9 ^ t * (Finset.univ.biUnion miss).card ≤
        (2 ^ k) * (2 ^ k) * 7 ^ t * flags.card ^ t := by
      calc 9 ^ t * (Finset.univ.biUnion miss).card
          ≤ 9 ^ t * ∑ uv : Fin (2 ^ k) × Fin (2 ^ k), (miss uv).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ uv : Fin (2 ^ k) × Fin (2 ^ k), 9 ^ t * (miss uv).card := Finset.mul_sum _ _ _
        _ ≤ ∑ _uv : Fin (2 ^ k) × Fin (2 ^ k), 7 ^ t * flags.card ^ t :=
            Finset.sum_le_sum (fun uv _ => hmiss_bound uv)
        _ = (2 ^ k) * (2 ^ k) * 7 ^ t * flags.card ^ t := by
            simp [Fintype.card_prod, mul_assoc]
    have hfp : 0 < flags.card ^ t := Nat.pow_pos hflags_pos
    have h2 : (2 ^ k) * (2 ^ k) * 7 ^ t * flags.card ^ t < 9 ^ t * flags.card ^ t :=
      Nat.mul_lt_mul_of_pos_right (PEqualNP.Outside.L_meta_25641_aux.pow_union_bound_25641 k) hfp
    have h3 : 9 ^ t * (Finset.univ.biUnion miss).card < 9 ^ t * flags.card ^ t := lt_of_le_of_lt h1 h2
    rw [hall_card]
    exact Nat.lt_of_mul_lt_mul_left h3
  have hex_panel : ∃ panel ∈ allPanels, panel ∉ Finset.univ.biUnion miss := by
    by_contra hall
    push Not at hall
    have hsub : allPanels ⊆ Finset.univ.biUnion miss := fun p hp => hall p hp
    have hle := Finset.card_le_card hsub
    omega
  rcases hex_panel with ⟨panel, hpanel_all, hpanel_good⟩
  have hpanel_flags : ∀ slot : Fin t, panel slot ∈ flags := by
    intro slot
    exact (Fintype.mem_piFinset.mp hpanel_all) slot
  refine ⟨panel, hpanel_flags, fun u v => ?_⟩
  intro raw labels M hM
  rcases hJ (u, v) hM with ⟨hj1, hj2, hj3, hj4⟩
  refine ⟨J (u, v), hj1, hj2, hj3, hj4, ?_⟩
  have hnot_miss : panel ∉ miss (u, v) :=
    fun hm => hpanel_good (Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_univ _, hm⟩)
  dsimp only [miss] at hnot_miss
  rw [Fintype.mem_piFinset] at hnot_miss
  push Not at hnot_miss
  rcases hnot_miss with ⟨trial, htrial⟩
  have hM' : 0 < ((Finset.univ.filter (good u v)).image label).card := hM
  dsimp only [badDraws] at htrial
  simp only [hM', ↓reduceIte, Finset.mem_filter, not_and, not_not] at htrial
  have hsing_lbl : (labels.filter (cell (panel trial) (J (u, v)))).card = 1 :=
    htrial (hpanel_flags trial)
  refine ⟨trial, ?_, ?_, ?_, ?_⟩
  · have hAinj : Function.Injective (panel trial).1.mulVec :=
      (Finset.mem_filter.mp (hpanel_flags trial)).2
    exact PEqualNP.Outside.L_meta_25641_aux.cell_card_of_gl (panel trial).1 hAinj (panel trial).2 (J (u, v)) hj1
  · have himg : (raw.filter (fun cand => cell (panel trial) (J (u, v)) (label cand))).image label =
        labels.filter (cell (panel trial) (J (u, v))) := by
      ext y
      simp only [Finset.mem_image, Finset.mem_filter, labels]
      constructor
      · rintro ⟨cand, ⟨hc_raw, hc_cell⟩, rfl⟩
        exact ⟨⟨cand, hc_raw, rfl⟩, hc_cell⟩
      · rintro ⟨⟨cand, hc_raw, rfl⟩, hc_cell⟩
        exact ⟨cand, ⟨hc_raw, hc_cell⟩, rfl⟩
    rw [himg, hsing_lbl]
  · rcases Finset.card_eq_one.mp hsing_lbl with ⟨y, hy⟩
    have hkept_eq : raw.filter (fun cand => cell (panel trial) (J (u, v)) (label cand)) =
        (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
          (PEqualNP.Outside.L_meta_25641_aux.firstN k w.val u.val r < 2 ^ (k - h) ∧
           PEqualNP.Outside.L_meta_25641_aux.secondN k w.val v.val r r < 2 ^ (k - h)) ∧
          label w = y) := by
      ext w
      simp only [raw, Finset.mem_filter, Finset.mem_univ, true_and]
      have hg_eq : good u v w ↔
          (PEqualNP.Outside.L_meta_25641_aux.firstN k w.val u.val r < 2 ^ (k - h) ∧
           PEqualNP.Outside.L_meta_25641_aux.secondN k w.val v.val r r < 2 ^ (k - h)) := Iff.rfl
      rw [hg_eq]
      constructor
      · rintro ⟨hgw, hcw⟩
        refine ⟨hgw, ?_⟩
        have hmem : label w ∈ labels.filter (cell (panel trial) (J (u, v))) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w, ?_, rfl⟩, hcw⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hg_eq.mpr hgw⟩
        rw [hy, Finset.mem_singleton] at hmem
        exact hmem
      · rintro ⟨hgw, hlw⟩
        refine ⟨hgw, ?_⟩
        have hy_mem : y ∈ labels.filter (cell (panel trial) (J (u, v))) := by
          rw [hy]
          exact Finset.mem_singleton_self y
        rw [hlw]
        exact (Finset.mem_filter.mp hy_mem).2
    have hne_fib : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        (PEqualNP.Outside.L_meta_25641_aux.firstN k w.val u.val r < 2 ^ (k - h) ∧
         PEqualNP.Outside.L_meta_25641_aux.secondN k w.val v.val r r < 2 ^ (k - h)) ∧
        label w = y)).Nonempty := by
      have hy_mem : y ∈ labels.filter (cell (panel trial) (J (u, v))) := by
        rw [hy]
        exact Finset.mem_singleton_self y
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hy_mem).1 with ⟨w, hw_raw, hlw⟩
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, (Finset.mem_filter.mp hw_raw).2, hlw⟩⟩
    rw [hkept_eq]
    exact (PEqualNP.Outside.L_meta_25641_aux.fiber_structure hk hr u v y hne_fib).1
  · rcases Finset.card_eq_one.mp hsing_lbl with ⟨y, hy⟩
    have hkept_eq : raw.filter (fun cand => cell (panel trial) (J (u, v)) (label cand)) =
        (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
          (PEqualNP.Outside.L_meta_25641_aux.firstN k w.val u.val r < 2 ^ (k - h) ∧
           PEqualNP.Outside.L_meta_25641_aux.secondN k w.val v.val r r < 2 ^ (k - h)) ∧
          label w = y) := by
      ext w
      simp only [raw, Finset.mem_filter, Finset.mem_univ, true_and]
      have hg_eq : good u v w ↔
          (PEqualNP.Outside.L_meta_25641_aux.firstN k w.val u.val r < 2 ^ (k - h) ∧
           PEqualNP.Outside.L_meta_25641_aux.secondN k w.val v.val r r < 2 ^ (k - h)) := Iff.rfl
      rw [hg_eq]
      constructor
      · rintro ⟨hgw, hcw⟩
        refine ⟨hgw, ?_⟩
        have hmem : label w ∈ labels.filter (cell (panel trial) (J (u, v))) := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨w, ?_, rfl⟩, hcw⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hg_eq.mpr hgw⟩
        rw [hy, Finset.mem_singleton] at hmem
        exact hmem
      · rintro ⟨hgw, hlw⟩
        refine ⟨hgw, ?_⟩
        have hy_mem : y ∈ labels.filter (cell (panel trial) (J (u, v))) := by
          rw [hy]
          exact Finset.mem_singleton_self y
        rw [hlw]
        exact (Finset.mem_filter.mp hy_mem).2
    have hne_fib : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
        (PEqualNP.Outside.L_meta_25641_aux.firstN k w.val u.val r < 2 ^ (k - h) ∧
         PEqualNP.Outside.L_meta_25641_aux.secondN k w.val v.val r r < 2 ^ (k - h)) ∧
        label w = y)).Nonempty := by
      have hy_mem : y ∈ labels.filter (cell (panel trial) (J (u, v))) := by
        rw [hy]
        exact Finset.mem_singleton_self y
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hy_mem).1 with ⟨w, hw_raw, hlw⟩
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, (Finset.mem_filter.mp hw_raw).2, hlw⟩⟩
    rw [hkept_eq]
    exact (PEqualNP.Outside.L_meta_25641_aux.fiber_structure hk hr u v y hne_fib).2
