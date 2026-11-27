import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25496_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.Represents

def rotK (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepK (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def constK (k j : ℕ) : ℕ :=
  3 ^ (k + j) % 2 ^ k

def firstK (k rowKey rowName : ℕ) : ℕ :=
  let x := rotK k 1 rowKey ^^^ rowName
  stepK k (x ^^^ rotK k 1 x ^^^ rotK k (k - 1) x) ^^^ rotK k 0 rowKey ^^^ constK k 1

def secondK (k colKey colName : ℕ) : ℕ :=
  let z := rotK k 3 colKey ^^^ colName
  stepK k (z ^^^ rotK k 2 z ^^^ rotK k (k - 2) z) ^^^ rotK k 4 colKey ^^^ constK k 2

def halfK (k : ℕ) : ℕ := (k + 1) / 2

def remK (k : ℕ) : ℕ := k - halfK k

def slotsK (k : ℕ) : ℕ := 2 ^ remK k

lemma testBit_lt_of_lt {a m i : ℕ} (ha : a < 2 ^ m) (hi : m ≤ i) : a.testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hi)

lemma lt_two_pow_iff_high_bits_false {a m k : ℕ} (ha : a < 2 ^ k) :
    a < 2 ^ m ↔ ∀ i, m ≤ i → i < k → a.testBit i = false := by
  constructor
  · intro h i him _
    exact testBit_lt_of_lt h him
  · intro h
    have heq : a = a % 2 ^ m := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow]
      by_cases him : i < m
      · simp [him]
      · simp only [him, decide_false, Bool.false_and]
        by_cases hik : i < k
        · exact h i (by omega) hik
        · exact testBit_lt_of_lt ha (by omega)
    rw [heq]
    exact Nat.mod_lt a (Nat.two_pow_pos m)

lemma xor_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : (a ^^^ b) < 2 ^ k := by
  have heq : a ^^^ b = (a ^^^ b) % 2 ^ k := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_xor]
    by_cases hi : i < k
    · simp [hi]
    · have h1 : a.testBit i = false := testBit_lt_of_lt ha (by omega)
      have h2 : b.testBit i = false := testBit_lt_of_lt hb (by omega)
      simp [hi, h1, h2]
  rw [heq]
  exact Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotK_lt {k : ℕ} (s word : ℕ) : rotK k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotK_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotK k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotK
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsr : s % k < k := Nat.mod_lt s hk
  by_cases h0 : s % k = 0
  · rw [h0]
    have hge : word.testBit (k + i) = false := testBit_lt_of_lt hw (by omega)
    simp [hge, Nat.mod_eq_of_lt hi]
  · by_cases hir : i < s % k
    · have hge : ¬(s % k ≤ i) := by omega
      have hmod : (i + k - s % k) % k = k - s % k + i := by
        have hlt : k - s % k + i < k := by omega
        have heq : i + k - s % k = k - s % k + i := by omega
        rw [heq, Nat.mod_eq_of_lt hlt]
      simp [hge, hmod]
    · have hle : s % k ≤ i := by omega
      have hge : word.testBit (k - s % k + i) = false := testBit_lt_of_lt hw (by omega)
      have hmod : (i + k - s % k) % k = i - s % k := by
        have heq : i + k - s % k = (i - s % k) + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      simp [hle, hge, hmod]

def stepFold (f : ℕ → Bool) (m : ℕ) : ℕ :=
  (List.range m).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0

lemma stepFold_lt (f : ℕ → Bool) (m : ℕ) : stepFold f m < 2 ^ m := by
  induction m with
  | zero => simp [stepFold]
  | succ m ih =>
    unfold stepFold
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change stepFold f m ||| ((f m).toNat <<< m) < 2 ^ (m + 1)
    have hbit : ((f m).toNat <<< m) < 2 ^ (m + 1) := by
      rw [Nat.shiftLeft_eq]
      cases f m <;> simp [Nat.pow_succ]
    have hlt1 : stepFold f m < 2 ^ (m + 1) := lt_trans ih (by rw [Nat.pow_succ]; omega)
    have heq : (stepFold f m ||| ((f m).toNat <<< m)) =
        (stepFold f m ||| ((f m).toNat <<< m)) % 2 ^ (m + 1) := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_mod_two_pow, Nat.testBit_or]
      by_cases hi : i < m + 1
      · simp [hi]
      · have h1 : (stepFold f m).testBit i = false := testBit_lt_of_lt hlt1 (by omega)
        have h2 : ((f m).toNat <<< m).testBit i = false := testBit_lt_of_lt hbit (by omega)
        simp [hi, h1, h2]
    rw [heq]
    exact Nat.mod_lt _ (Nat.two_pow_pos (m + 1))

lemma stepFold_testBit (f : ℕ → Bool) (m i : ℕ) :
    (stepFold f m).testBit i = if i < m then f i else false := by
  induction m with
  | zero => simp [stepFold]
  | succ m ih =>
    unfold stepFold
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (stepFold f m ||| ((f m).toNat <<< m)).testBit i = if i < m + 1 then f i else false
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases him : i < m
    · have hnot : ¬(m ≤ i) := by omega
      have hlt : i < m + 1 := by omega
      simp [him, hnot, hlt]
    · by_cases heq : i = m
      · subst heq
        cases hfm : f i <;> simp
      · have hgt : ¬(i < m + 1) := by omega
        have htb : (f m).toNat.testBit (i - m) = false := by
          apply testBit_lt_of_lt (m := 1)
          · cases f m <;> simp
          · omega
        simp [him, hgt, htb]

lemma stepK_lt (k word : ℕ) : stepK k word < 2 ^ k :=
  stepFold_lt _ k

lemma stepK_testBit {k word i : ℕ} (hi : i < k) :
    (stepK k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  have h := stepFold_testBit
    (fun j => xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k)))
    k i
  unfold stepK
  simpa [stepFold, hi] using h

lemma constK_lt (k j : ℕ) : constK k j < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma firstK_lt (k w u : ℕ) : firstK k w u < 2 ^ k := by
  unfold firstK
  exact xor_lt_two_pow (xor_lt_two_pow (stepK_lt k _) (rotK_lt 0 w)) (constK_lt k 1)

lemma secondK_lt (k w v : ℕ) : secondK k w v < 2 ^ k := by
  unfold secondK
  exact xor_lt_two_pow (xor_lt_two_pow (stepK_lt k _) (rotK_lt 4 w)) (constK_lt k 2)

lemma testBit_add_two_pow {a k i : ℕ} (ha : a < 2 ^ k) :
    (a + 2 ^ k).testBit i = if i = k then true else a.testBit i := by
  by_cases hik : i < k
  · have hne : i ≠ k := by omega
    rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]
    simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
    have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hdiv : (a + 2 ^ k) / 2 ^ i = a / 2 ^ i + 2 ^ (k - i) := by
      rw [hpow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
    have heven : 2 ^ (k - i) % 2 = 0 := by
      have hsplit : 2 ^ (k - i) = 2 * 2 ^ (k - i - 1) := by
        conv_lhs => rw [show k - i = (k - i - 1) + 1 by omega]
        rw [Nat.pow_succ']
      rw [hsplit]
      omega
    rw [hdiv]
    have hmod : (a / 2 ^ i + 2 ^ (k - i)) % 2 = (a / 2 ^ i) % 2 := by omega
    simp [hmod]
  · by_cases heq : i = k
    · subst heq
      rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hdiv : (a + 2 ^ i) / 2 ^ i = 1 := by
        have h1 : (a + 2 ^ i) / 2 ^ i = a / 2 ^ i + 1 :=
          Nat.add_div_right a (Nat.two_pow_pos i)
        rw [h1, Nat.div_eq_of_lt ha]
      rw [hdiv]
      rfl
    · rw [ite_eq_right_iff.mpr (fun h => absurd h heq)]
      have h1 : (a + 2 ^ k).testBit i = false :=
        testBit_lt_of_lt (m := k + 1) (by rw [Nat.pow_succ]; omega) (by omega)
      have h2 : a.testBit i = false := testBit_lt_of_lt ha (by omega)
      rw [h1, h2]

lemma tableIndex_step {k : ℕ} (f : Fin (k + 1) → Bool) :
    tableIndex f = tableIndex (fun i : Fin k => f i.castSucc) +
      if f (Fin.last k) = true then 2 ^ k else 0 := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  simp

lemma tableIndex_lt {k : ℕ} (f : Fin k → Bool) : tableIndex f < 2 ^ k := by
  induction k with
  | zero => simp [tableIndex]
  | succ k ih =>
    rw [tableIndex_step]
    have h1 := ih (fun i : Fin k => f i.castSucc)
    rw [Nat.pow_succ]
    cases f (Fin.last k) <;> simp <;> omega

lemma tableIndex_testBit {k : ℕ} (f : Fin k → Bool) (i : ℕ) (hi : i < k) :
    (tableIndex f).testBit i = f ⟨i, hi⟩ := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [tableIndex_step]
    set a := tableIndex (fun j : Fin k => f j.castSucc)
    have ha : a < 2 ^ k := tableIndex_lt _
    by_cases hik : i < k
    · have hne : i ≠ k := by omega
      have hbit : (a + if f (Fin.last k) = true then 2 ^ k else 0).testBit i = a.testBit i := by
        cases f (Fin.last k)
        · simp
        · simp [testBit_add_two_pow ha, hne]
      rw [hbit, ih (fun j : Fin k => f j.castSucc) hik]
      rfl
    · have heq : i = k := by omega
      subst heq
      have ha0 : a.testBit i = false := testBit_lt_of_lt ha le_rfl
      have hlast : (⟨i, hi⟩ : Fin (i + 1)) = Fin.last i := rfl
      rw [hlast]
      cases hfl : f (Fin.last i)
      · simpa using ha0
      · simp [testBit_add_two_pow ha]

def initX (k s : ℕ) (idx : ℕ) : Bool :=
  if idx = 0 then s.testBit 0
  else if idx = 1 then s.testBit 1
  else if idx = 2 then s.testBit 2
  else if idx = k - 1 then s.testBit 3
  else if 3 ≤ idx ∧ idx < remK k - 1 then s.testBit (idx + 1)
  else false

def solveStep (k u : ℕ) (xs : ℕ → Bool) (t : ℕ) : ℕ → Bool :=
  let i := k - 1 - t
  let p := xor (xs ((i + 1) % k)) (xs ((i + 2) % k))
  let y1 := xor (xs i) p
  let y2 := xor p (xs ((i + 3) % k))
  let tb := !y1 && y2
  let nv := xor (xor (xor (xs i) tb) (u.testBit ((i + 1) % k))) ((constK k 1).testBit i)
  fun idx => if idx = k - 2 - t then nv else xs idx

def solveXIter (k s u : ℕ) : ℕ → (ℕ → Bool)
  | 0 => initX k s
  | t + 1 => solveStep k u (solveXIter k s u t) t

def solveX (k s u : ℕ) : ℕ → Bool :=
  solveXIter k s u (halfK k)

def bitsToNat (k : ℕ) (f : ℕ → Bool) : ℕ :=
  stepFold f k

lemma bitsToNat_lt (k : ℕ) (f : ℕ → Bool) : bitsToNat k f < 2 ^ k :=
  stepFold_lt f k

lemma bitsToNat_testBit (k : ℕ) (f : ℕ → Bool) (i : ℕ) (hi : i < k) :
    (bitsToNat k f).testBit i = f i := by
  simpa [bitsToNat, hi] using stepFold_testBit f k i

def keyOfSlot (k s u : ℕ) : ℕ :=
  let xf := solveX k s u
  bitsToNat k (fun j => xor (xf ((j + 1) % k)) (u.testBit ((j + 1) % k)))

lemma keyOfSlot_lt (k s u : ℕ) : keyOfSlot k s u < 2 ^ k :=
  bitsToNat_lt k _

lemma solveXIter_stable {k s u t1 t2 idx : ℕ} (hk : 8 ≤ k) (hle : t1 ≤ t2) (ht2 : t2 ≤ halfK k)
    (hidx : k - 1 - t1 ≤ idx ∨ idx < k - 1 - t2) :
    solveXIter k s u t2 idx = solveXIter k s u t1 idx := by
  have hh : halfK k = (k + 1) / 2 := rfl
  induction t2 with
  | zero =>
    have : t1 = 0 := by omega
    subst this; rfl
  | succ t2 ih =>
    by_cases heq : t1 = t2 + 1
    · subst heq; rfl
    · simp only [solveXIter, solveStep]
      have hne : idx ≠ k - 2 - t2 := by omega
      rw [ite_eq_right_iff.mpr (fun h => absurd h hne)]
      exact ih (by omega) (by omega) (by omega)

lemma mod_add_not_in_future {k t d : ℕ} (hk : 8 ≤ k) (ht : t < halfK k) (hd : 1 ≤ d ∧ d ≤ 3) :
    k - 1 - t ≤ (k - 1 - t + d) % k ∨ (k - 1 - t + d) % k < k - 1 - halfK k := by
  have hh : halfK k = (k + 1) / 2 := rfl
  by_cases hwrap : k - 1 - t + d < k
  · left
    rw [Nat.mod_eq_of_lt hwrap]
    omega
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

lemma solveX_eq_step {k s u i : ℕ} (hk : 8 ≤ k) (hi1 : remK k ≤ i) (hi2 : i < k) :
    let xf := solveX k s u
    let p := xor (xf ((i + 1) % k)) (xf ((i + 2) % k))
    let y1 := xor (xf i) p
    let y2 := xor p (xf ((i + 3) % k))
    xf (i - 1) =
      xor (xor (xor (xf i) (!y1 && y2)) (u.testBit ((i + 1) % k))) ((constK k 1).testBit i) := by
  set t := k - 1 - i
  have hh : halfK k = (k + 1) / 2 := rfl
  have hr : remK k = k - halfK k := rfl
  have ht : t < halfK k := by omega
  have hi_eq : k - 1 - t = i := by omega
  have him1_eq : k - 2 - t = i - 1 := by omega
  have hst0 : solveX k s u (i - 1) = solveXIter k s u (t + 1) (i - 1) :=
    solveXIter_stable hk (by omega) le_rfl (by left; omega)
  have hsti : solveX k s u i = solveXIter k s u t i :=
    solveXIter_stable hk (by omega) le_rfl (by left; omega)
  have hst1 : solveX k s u ((i + 1) % k) = solveXIter k s u t ((i + 1) % k) := by
    have h := mod_add_not_in_future hk ht (d := 1) (by omega)
    rw [hi_eq] at h
    exact solveXIter_stable hk (by omega) le_rfl (by omega)
  have hst2 : solveX k s u ((i + 2) % k) = solveXIter k s u t ((i + 2) % k) := by
    have h := mod_add_not_in_future hk ht (d := 2) (by omega)
    rw [hi_eq] at h
    exact solveXIter_stable hk (by omega) le_rfl (by omega)
  have hst3 : solveX k s u ((i + 3) % k) = solveXIter k s u t ((i + 3) % k) := by
    have h := mod_add_not_in_future hk ht (d := 3) (by omega)
    rw [hi_eq] at h
    exact solveXIter_stable hk (by omega) le_rfl (by omega)
  dsimp only
  rw [hst0, hsti, hst1, hst2, hst3]
  simp only [solveXIter, solveStep, hi_eq, him1_eq, ↓reduceIte]

lemma xor_step_cancel (xm1 x0 x1 x2 x3 u1 c1 : Bool) :
    xor (xor (xor (xor (xor x0 xm1) x1)
      (!(xor (xor x1 x0) x2) && xor (xor x2 x1) x3)) (xor x1 u1)) c1 =
    xor xm1 (xor (xor (xor x0
      (!(xor x0 (xor x1 x2)) && xor (xor x1 x2) x3)) u1) c1) := by
  cases xm1 <;> cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> cases u1 <;> cases c1 <;> rfl

lemma firstK_testBit_formula {k w u i : ℕ} (hk : 8 ≤ k) (hw : w < 2 ^ k) (hu : u < 2 ^ k)
    (hi : i < k) :
    let x := rotK k 1 w ^^^ u
    let p := xor (x.testBit ((i + 1) % k)) (x.testBit ((i + 2) % k))
    let y1 := xor (x.testBit i) p
    let y2 := xor p (x.testBit ((i + 3) % k))
    (firstK k w u).testBit i =
      xor (x.testBit ((i + k - 1) % k))
        (xor (xor (xor (x.testBit i) (!y1 && y2)) (u.testBit ((i + 1) % k)))
          ((constK k 1).testBit i)) := by
  have hk0 : 0 < k := by omega
  set x := rotK k 1 w ^^^ u
  have hx : x < 2 ^ k := xor_lt_two_pow (rotK_lt 1 w) hu
  set y := x ^^^ rotK k 1 x ^^^ rotK k (k - 1) x
  have hy_bit : ∀ j < k, y.testBit j =
      xor (xor (x.testBit j) (x.testBit ((j + k - 1) % k))) (x.testBit ((j + 1) % k)) := by
    intro j hj
    simp only [y, Nat.testBit_xor]
    rw [rotK_testBit hk0 hx hj, rotK_testBit hk0 hx hj]
    have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
    have h3 : (j + k - (k - 1)) % k = (j + 1) % k := by congr 1; omega
    rw [h1, h2, h3]
  have hw_bit : w.testBit i = xor (x.testBit ((i + 1) % k)) (u.testBit ((i + 1) % k)) := by
    have hi1 : (i + 1) % k < k := Nat.mod_lt _ hk0
    have hxi : x.testBit ((i + 1) % k) = xor ((rotK k 1 w).testBit ((i + 1) % k)) (u.testBit ((i + 1) % k)) := by
      simp [x, Nat.testBit_xor]
    rw [rotK_testBit hk0 hw hi1] at hxi
    have hmod : ((i + 1) % k + k - 1 % k) % k = i := by
      have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1]
      by_cases hlt : i + 1 < k
      · rw [Nat.mod_eq_of_lt hlt]
        have heq : i + 1 + k - 1 = i + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
      · have hieq : i = k - 1 := by omega
        subst hieq
        have hsum : k - 1 + 1 = k := by omega
        rw [hsum, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hxi
    rw [hxi]
    cases w.testBit i <;> cases u.testBit ((i + 1) % k) <;> rfl
  have h1mod : ((i + 1) % k + k - 1) % k = i := by
    by_cases hlt : i + 1 < k
    · rw [Nat.mod_eq_of_lt hlt]
      have heq : i + 1 + k - 1 = i + k := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · have hieq : i = k - 1 := by omega
      subst hieq
      have hsum : k - 1 + 1 = k := by omega
      rw [hsum, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  have h1p1 : ((i + 1) % k + 1) % k = (i + 2) % k := by
    rw [Nat.mod_add_mod]
  have h2p1 : ((i + 2) % k + 1) % k = (i + 3) % k := by
    rw [Nat.mod_add_mod]
  have h2mod : ((i + 2) % k + k - 1) % k = (i + 1) % k := by
    have hlt1 : (i + 1) % k < k := Nat.mod_lt _ hk0
    rw [← h1p1]
    by_cases hlt : (i + 1) % k + 1 < k
    · rw [Nat.mod_eq_of_lt hlt]
      have heq : (i + 1) % k + 1 + k - 1 = (i + 1) % k + k := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
    · have heq : (i + 1) % k = k - 1 := by omega
      rw [heq]
      have hsum : k - 1 + 1 = k := by omega
      rw [hsum, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
  have hr0 : (rotK k 0 w).testBit i = w.testBit i := by
    rw [rotK_testBit hk0 hw hi]
    simp [Nat.mod_eq_of_lt hi]
  unfold firstK
  change (stepK k y ^^^ rotK k 0 w ^^^ constK k 1).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_xor, stepK_testBit hi, hr0, hw_bit,
    hy_bit i hi, hy_bit ((i + 1) % k) (Nat.mod_lt _ hk0),
    hy_bit ((i + 2) % k) (Nat.mod_lt _ hk0), h1mod, h2mod, h1p1, h2p1]
  exact xor_step_cancel _ _ _ _ _ _ _

lemma keyOfSlot_x_testBit {k s u i : ℕ} (hk : 8 ≤ k) (hi : i < k) :
    (rotK k 1 (keyOfSlot k s u) ^^^ u).testBit i = solveX k s u i := by
  have hk0 : 0 < k := by omega
  rw [Nat.testBit_xor, rotK_testBit hk0 (keyOfSlot_lt k s u) hi]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  set j := (i + k - 1) % k
  have hj : j < k := Nat.mod_lt _ hk0
  unfold keyOfSlot
  rw [bitsToNat_testBit k _ j hj]
  have hjp1 : (j + 1) % k = i := by
    by_cases hi0 : i = 0
    · subst hi0
      have hjv : j = k - 1 := by simp [j]
      rw [hjv]
      have hsum : k - 1 + 1 = k := by omega
      rw [hsum, Nat.mod_self]
    · have hjv : j = i - 1 := by
        have heq : i + k - 1 = (i - 1) + k := by omega
        have hlt : i - 1 < k := by omega
        change (i + k - 1) % k = i - 1
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
      rw [hjv]
      have hsum : i - 1 + 1 = i := by omega
      rw [hsum, Nat.mod_eq_of_lt hi]
  rw [hjp1]
  cases solveX k s u i <;> cases u.testBit i <;> rfl

lemma keyOfSlot_first_lt {k s u : ℕ} (hk : 8 ≤ k) (hu : u < 2 ^ k) :
    firstK k (keyOfSlot k s u) u < slotsK k := by
  rw [slotsK, lt_two_pow_iff_high_bits_false (firstK_lt k _ u)]
  intro i hi1 hi2
  rw [firstK_testBit_formula hk (keyOfSlot_lt k s u) hu hi2]
  have hh : halfK k = (k + 1) / 2 := rfl
  have hr : remK k = k - halfK k := rfl
  have hmod : (i + k - 1) % k = i - 1 := by
    have heq : i + k - 1 = (i - 1) + k := by omega
    rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [hmod, keyOfSlot_x_testBit hk (by omega), keyOfSlot_x_testBit hk hi2,
    keyOfSlot_x_testBit hk (Nat.mod_lt _ (by omega)),
    keyOfSlot_x_testBit hk (Nat.mod_lt _ (by omega)),
    keyOfSlot_x_testBit hk (Nat.mod_lt _ (by omega))]
  have hstep := solveX_eq_step (s := s) (u := u) hk hi1 hi2
  dsimp only at hstep
  rw [hstep]
  exact Bool.xor_self _

def slotOfX (k x : ℕ) : ℕ :=
  stepFold (fun b =>
    if b = 0 then x.testBit 0
    else if b = 1 then x.testBit 1
    else if b = 2 then x.testBit 2
    else if b = 3 then x.testBit (k - 1)
    else x.testBit (b - 1)) (remK k)

lemma slotOfX_lt (k x : ℕ) : slotOfX k x < slotsK k :=
  stepFold_lt _ (remK k)

lemma bool_eq_of_xor_false {a b : Bool} (h : xor a b = false) : b = a := by
  cases a <;> cases b <;> simp_all

lemma exists_slot_of_first_lt {k w u : ℕ} (hk : 8 ≤ k) (hw : w < 2 ^ k) (hu : u < 2 ^ k)
    (hf : firstK k w u < slotsK k) :
    ∃ s < slotsK k, keyOfSlot k s u = w := by
  have hh : halfK k = (k + 1) / 2 := rfl
  have hr : remK k = k - halfK k := rfl
  set x := rotK k 1 w ^^^ u
  set s := slotOfX k x
  refine ⟨s, slotOfX_lt k x, ?_⟩
  have hinit : ∀ idx, (idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = k - 1 ∨ (3 ≤ idx ∧ idx < remK k - 1)) →
      initX k s idx = x.testBit idx := by
    intro idx hidx
    have hsb : ∀ b < remK k, s.testBit b =
        (if b = 0 then x.testBit 0
         else if b = 1 then x.testBit 1
         else if b = 2 then x.testBit 2
         else if b = 3 then x.testBit (k - 1)
         else x.testBit (b - 1)) := by
      intro b hb
      simpa [s, slotOfX, hb] using stepFold_testBit
        (fun j =>
          if j = 0 then x.testBit 0
          else if j = 1 then x.testBit 1
          else if j = 2 then x.testBit 2
          else if j = 3 then x.testBit (k - 1)
          else x.testBit (j - 1)) (remK k) b
    unfold initX
    rcases hidx with rfl | rfl | rfl | rfl | ⟨h3, hlt⟩
    · simp [hsb 0 (by omega)]
    · simp [hsb 1 (by omega)]
    · simp [hsb 2 (by omega)]
    · have hne0 : k - 1 ≠ 0 := by omega
      have hne1 : k - 1 ≠ 1 := by omega
      have hne2 : k - 1 ≠ 2 := by omega
      simp [hne0, hne1, hne2, hsb 3 (by omega)]
    · have hne0 : idx ≠ 0 := by omega
      have hne1 : idx ≠ 1 := by omega
      have hne2 : idx ≠ 2 := by omega
      have hnek : idx ≠ k - 1 := by omega
      have hb := hsb (idx + 1) (by omega)
      have hne3 : idx + 1 ≠ 0 ∧ idx + 1 ≠ 1 ∧ idx + 1 ≠ 2 ∧ idx + 1 ≠ 3 := by omega
      have hsub : idx + 1 - 1 = idx := by omega
      simp only [hne0, hne1, hne2, hnek, h3, hlt, and_self, ↓reduceIte]
      rw [hb]
      simp [hne0, hne3.2.2.1, hne3.2.2.2, hsub]
  have hagree : ∀ t ≤ halfK k, ∀ idx,
      (idx < remK k - 1 ∨ k - 1 - t ≤ idx) → idx < k →
      solveXIter k s u t idx = x.testBit idx := by
    intro t ht
    induction t with
    | zero =>
      intro idx hidx hik
      apply hinit idx
      omega
    | succ t ih =>
      intro idx hidx hik
      have ih' := ih (by omega)
      simp only [solveXIter, solveStep]
      by_cases heq : idx = k - 2 - t
      · rw [ite_eq_left_iff.mpr (fun h => absurd heq h)]
        set i := k - 1 - t
        have hi1 : remK k ≤ i := by omega
        have hi2 : i < k := by omega
        have htlt : t < halfK k := by omega
        have h0 : solveXIter k s u t i = x.testBit i := ih' i (by right; omega) hi2
        have h1 : solveXIter k s u t ((i + 1) % k) = x.testBit ((i + 1) % k) := by
          have hm : i ≤ (i + 1) % k ∨ (i + 1) % k < k - 1 - halfK k :=
            mod_add_not_in_future hk htlt (d := 1) (by omega)
          have hcond : (i + 1) % k < remK k - 1 ∨ k - 1 - t ≤ (i + 1) % k := by
            rcases hm with h | h
            · right; exact h
            · left; omega
          exact ih' ((i + 1) % k) hcond (Nat.mod_lt _ (by omega))
        have h2 : solveXIter k s u t ((i + 2) % k) = x.testBit ((i + 2) % k) := by
          have hm : i ≤ (i + 2) % k ∨ (i + 2) % k < k - 1 - halfK k :=
            mod_add_not_in_future hk htlt (d := 2) (by omega)
          have hcond : (i + 2) % k < remK k - 1 ∨ k - 1 - t ≤ (i + 2) % k := by
            rcases hm with h | h
            · right; exact h
            · left; omega
          exact ih' ((i + 2) % k) hcond (Nat.mod_lt _ (by omega))
        have h3 : solveXIter k s u t ((i + 3) % k) = x.testBit ((i + 3) % k) := by
          have hm : i ≤ (i + 3) % k ∨ (i + 3) % k < k - 1 - halfK k :=
            mod_add_not_in_future hk htlt (d := 3) (by omega)
          have hcond : (i + 3) % k < remK k - 1 ∨ k - 1 - t ≤ (i + 3) % k := by
            rcases hm with h | h
            · right; exact h
            · left; omega
          exact ih' ((i + 3) % k) hcond (Nat.mod_lt _ (by omega))
        rw [h0, h1, h2, h3]
        have hf0 : (firstK k w u).testBit i = false :=
          (lt_two_pow_iff_high_bits_false (firstK_lt k w u)).mp hf i hi1 hi2
        rw [firstK_testBit_formula hk hw hu hi2] at hf0
        have hmod : (i + k - 1) % k = idx := by
          have hsum : i + k - 1 = idx + k := by omega
          rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hik]
        rw [hmod] at hf0
        exact bool_eq_of_xor_false hf0
      · rw [ite_eq_right_iff.mpr (fun h => absurd h heq)]
        exact ih' idx (by omega) hik
  have hall : ∀ idx < k, solveX k s u idx = x.testBit idx := by
    intro idx hik
    exact hagree (halfK k) le_rfl idx (by omega) hik
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hjk : j < k
  · unfold keyOfSlot
    rw [bitsToNat_testBit k _ j hjk, hall ((j + 1) % k) (Nat.mod_lt _ (by omega))]
    have hjp1 : (j + 1) % k < k := Nat.mod_lt _ (by omega)
    have hxi : x.testBit ((j + 1) % k) =
        xor ((rotK k 1 w).testBit ((j + 1) % k)) (u.testBit ((j + 1) % k)) := by
      simp [x, Nat.testBit_xor]
    rw [rotK_testBit (by omega) hw hjp1] at hxi
    have hmod : ((j + 1) % k + k - 1 % k) % k = j := by
      have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1]
      by_cases hlt : j + 1 < k
      · rw [Nat.mod_eq_of_lt hlt]
        have heq : j + 1 + k - 1 = j + k := by omega
        rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt hjk]
      · have hjeq : j = k - 1 := by omega
        subst hjeq
        have hsum : k - 1 + 1 = k := by omega
        rw [hsum, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hxi
    rw [hxi]
    cases w.testBit j <;> cases u.testBit ((j + 1) % k) <;> rfl
  · rw [testBit_lt_of_lt (keyOfSlot_lt k s u) (by omega), testBit_lt_of_lt hw (by omega)]

lemma graph_iff_slots {k u v : ℕ} (hk : 8 ≤ k) (hu : u < 2 ^ k) :
    ((List.range (2 ^ k)).any (fun w =>
      decide (firstK k w u < slotsK k) && decide (secondK k w v < slotsK k))) =
    ((List.range (slotsK k)).any (fun s =>
      decide (secondK k (keyOfSlot k s u) v < slotsK k))) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, hf, hs⟩
    rcases exists_slot_of_first_lt hk hw hu hf with ⟨s, hs_lt, rfl⟩
    exact ⟨s, hs_lt, hs⟩
  · rintro ⟨s, _, hs⟩
    exact ⟨keyOfSlot k s u, keyOfSlot_lt k s u, keyOfSlot_first_lt hk hu, hs⟩

def wireStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def wireVal (gs : List Gate) (x : List Bool) (w : ℕ) : Bool :=
  (gs.foldl wireStep x).getD w false

def Valid (n : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j)

def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ d, gs2 = gs1 ++ d

lemma extends_rfl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma extends_trans {a b c : List Gate} (h1 : Extends a b) (h2 : Extends b c) : Extends a c := by
  rcases h1 with ⟨d1, rfl⟩
  rcases h2 with ⟨d2, rfl⟩
  exact ⟨d1 ++ d2, by simp [List.append_assoc]⟩

lemma extends_len {a b : List Gate} (h : Extends a b) : a.length ≤ b.length := by
  rcases h with ⟨d, rfl⟩
  simp

lemma foldl_wireStep_len (gs : List Gate) (x : List Bool) :
    (gs.foldl wireStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, wireStep, List.length_append, List.length_nil]
    omega

lemma getD_append_left {α : Type} (l r : List α) (i : ℕ) (d : α) (h : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_right {α : Type} (l r : List α) (i : ℕ) (d : α) (h : l.length ≤ i) :
    (l ++ r).getD i d = r.getD (i - l.length) d := by
  simp [List.getD, List.getElem?_append_right h]

lemma foldl_wireStep_getD_lt (gs : List Gate) (base : List Bool) (w : ℕ) (hw : w < base.length) :
    (gs.foldl wireStep base).getD w false = base.getD w false := by
  induction gs generalizing base with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (wireStep base g).length := by simp [wireStep]; omega
    rw [ih (wireStep base g) hw']
    exact getD_append_left base _ w false hw

lemma wireVal_append_left {n : ℕ} (gs1 gs2 : List Gate) (x : List Bool) (hx : x.length = n)
    (w : ℕ) (hw : w < n + gs1.length) :
    wireVal (gs1 ++ gs2) x w = wireVal gs1 x w := by
  unfold wireVal
  rw [List.foldl_append]
  have hlen : (gs1.foldl wireStep x).length = n + gs1.length := by rw [foldl_wireStep_len, hx]
  exact foldl_wireStep_getD_lt gs2 (gs1.foldl wireStep x) w (by omega)

lemma wireVal_of_extends {n : ℕ} {gs1 gs2 : List Gate} (hext : Extends gs1 gs2)
    (x : List Bool) (hx : x.length = n) (w : ℕ) (hw : w < n + gs1.length) :
    wireVal gs2 x w = wireVal gs1 x w := by
  rcases hext with ⟨d, rfl⟩
  exact wireVal_append_left gs1 d x hx w hw

lemma wireVal_input {n : ℕ} (gs : List Gate) (x : List Bool) (hx : x.length = n)
    (w : ℕ) (hw : w < n) :
    wireVal gs x w = x.getD w false := by
  have h := wireVal_append_left (n := n) [] gs x hx w (by simpa using hw)
  simpa [wireVal] using h

def addGate (n : ℕ) (gs : List Gate) (g : Gate) : List Gate × ℕ :=
  (gs ++ [g], n + gs.length)

lemma addGate_valid {n : ℕ} {gs : List Gate} {g : Gate} (hv : Valid n gs)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < n + gs.length) :
    Valid n (addGate n gs g).1 := by
  constructor
  · intro g' hg'
    simp only [addGate, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hv.1 g' h
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [addGate, List.length_append, List.length_cons, List.length_nil] at hj
    simp only [addGate] at hi
    by_cases hlt : j < gs.length
    · rw [getD_append_left gs [g] j _ hlt] at hi
      exact hv.2 j hlt i hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [getD_append_right gs [g] gs.length _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      exact hin i hi

lemma addGate_extends (n : ℕ) (gs : List Gate) (g : Gate) : Extends gs (addGate n gs g).1 :=
  ⟨[g], rfl⟩

lemma addGate_len (n : ℕ) (gs : List Gate) (g : Gate) : (addGate n gs g).1.length = gs.length + 1 := by
  simp [addGate]

lemma addGate_out_lt (n : ℕ) (gs : List Gate) (g : Gate) :
    (addGate n gs g).2 < n + (addGate n gs g).1.length := by
  simp [addGate]

lemma addGate_val {n : ℕ} (gs : List Gate) (g : Gate) (x : List Bool) (hx : x.length = n) :
    wireVal (addGate n gs g).1 x (addGate n gs g).2 =
      g.op.eval (g.inputs.map fun i => wireVal gs x i) := by
  unfold addGate wireVal
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, wireStep]
  have hlen : (gs.foldl wireStep x).length = n + gs.length := by rw [foldl_wireStep_len, hx]
  rw [getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]

def addConst0 (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  addGate n gs ⟨GateOp.or, []⟩

def addConst1 (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  addGate n gs ⟨GateOp.and, []⟩

def addNot (n : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  addGate n gs ⟨GateOp.not, [a]⟩

def addAnd (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  addGate n gs ⟨GateOp.and, [a, b]⟩

def addOr (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  addGate n gs ⟨GateOp.or, [a, b]⟩

def addXor (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := addOr n gs a b
  let r2 := addAnd n r1.1 a b
  let r3 := addNot n r2.1 r2.2
  addAnd n r3.1 r1.2 r3.2

def addXorConst (n : ℕ) (gs : List Gate) (a : ℕ) (c : Bool) : List Gate × ℕ :=
  if c then addNot n gs a else (gs, a)

def addEqConst (n : ℕ) (gs : List Gate) (a : ℕ) (c : Bool) : List Gate × ℕ :=
  if c then (gs, a) else addNot n gs a

lemma addConst0_spec {n : ℕ} {gs : List Gate} (hv : Valid n gs) :
    let r := addConst0 n gs
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = false := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by simp), addGate_extends _ _ _,
    addGate_len _ _ _, addGate_out_lt _ _ _, ?_⟩
  intro x hx
  rw [addConst0, addGate_val gs _ x hx]
  rfl

lemma addConst1_spec {n : ℕ} {gs : List Gate} (hv : Valid n gs) :
    let r := addConst1 n gs
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = true := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by simp), addGate_extends _ _ _,
    addGate_len _ _ _, addGate_out_lt _ _ _, ?_⟩
  intro x hx
  rw [addConst1, addGate_val gs _ x hx]
  rfl

lemma addNot_spec {n : ℕ} {gs : List Gate} {a : ℕ} (hv : Valid n gs) (ha : a < n + gs.length) :
    let r := addNot n gs a
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = !(wireVal gs x a) := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by intro i hi; simp at hi; subst hi; exact ha),
    addGate_extends _ _ _, addGate_len _ _ _, addGate_out_lt _ _ _, ?_⟩
  intro x hx
  rw [addNot, addGate_val gs _ x hx]
  rfl

lemma addAnd_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hv : Valid n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addAnd n gs a b
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = (wireVal gs x a && wireVal gs x b) := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by
      intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    addGate_extends _ _ _, addGate_len _ _ _, addGate_out_lt _ _ _, ?_⟩
  intro x hx
  rw [addAnd, addGate_val gs _ x hx]
  simp [GateOp.eval]

lemma addOr_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hv : Valid n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addOr n gs a b
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = (wireVal gs x a || wireVal gs x b) := by
  refine ⟨addGate_valid hv (by simp) (by simp) (by
      intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    addGate_extends _ _ _, addGate_len _ _ _, addGate_out_lt _ _ _, ?_⟩
  intro x hx
  rw [addOr, addGate_val gs _ x hx]
  simp [GateOp.eval]

lemma addXor_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hv : Valid n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addXor n gs a b
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 4 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = xor (wireVal gs x a) (wireVal gs x b) := by
  set r1 := addOr n gs a b with hr1
  have h1 := addOr_spec hv ha hb
  dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨v1, e1, l1, w1, val1⟩
  set r2 := addAnd n r1.1 a b with hr2
  have h2 := addAnd_spec (a := a) (b := b) v1 (by omega) (by omega)
  dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨v2, e2, l2, w2, val2⟩
  set r3 := addNot n r2.1 r2.2 with hr3
  have h3 := addNot_spec (a := r2.2) v2 w2
  dsimp only at h3; rw [← hr3] at h3
  rcases h3 with ⟨v3, e3, l3, w3, val3⟩
  set r4 := addAnd n r3.1 r1.2 r3.2 with hr4
  have h4 := addAnd_spec (a := r1.2) (b := r3.2) v3 (by omega) w3
  dsimp only at h4; rw [← hr4] at h4
  rcases h4 with ⟨v4, e4, l4, w4, val4⟩
  change Valid n r4.1 ∧ Extends gs r4.1 ∧ r4.1.length = gs.length + 4 ∧ r4.2 < n + r4.1.length ∧
    ∀ x : List Bool, x.length = n → wireVal r4.1 x r4.2 = xor (wireVal gs x a) (wireVal gs x b)
  refine ⟨v4, extends_trans e1 (extends_trans e2 (extends_trans e3 e4)), by omega, w4, ?_⟩
  intro x hx
  rw [val4 x hx, val3 x hx,
    wireVal_of_extends e3 x hx r1.2 (by omega),
    wireVal_of_extends e2 x hx r1.2 w1,
    val1 x hx, val2 x hx,
    wireVal_of_extends e1 x hx a ha,
    wireVal_of_extends e1 x hx b hb]
  cases wireVal gs x a <;> cases wireVal gs x b <;> rfl

lemma addXorConst_spec {n : ℕ} {gs : List Gate} {a : ℕ} (c : Bool) (hv : Valid n gs)
    (ha : a < n + gs.length) :
    let r := addXorConst n gs a c
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = xor (wireVal gs x a) c := by
  cases c
  · simp only [addXorConst, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hv, extends_rfl gs, by omega, ha, fun x _ => by simp⟩
  · simp only [addXorConst, ↓reduceIte]
    rcases addNot_spec hv ha with ⟨v1, e1, l1, w1, val1⟩
    exact ⟨v1, e1, by omega, w1, fun x hx => by
      rw [val1 x hx]; cases wireVal gs x a <;> rfl⟩

lemma addEqConst_spec {n : ℕ} {gs : List Gate} {a : ℕ} (c : Bool) (hv : Valid n gs)
    (ha : a < n + gs.length) :
    let r := addEqConst n gs a c
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ x : List Bool, x.length = n → wireVal r.1 x r.2 = !(xor (wireVal gs x a) c) := by
  cases c
  · simp only [addEqConst, Bool.false_eq_true, ↓reduceIte]
    rcases addNot_spec hv ha with ⟨v1, e1, l1, w1, val1⟩
    exact ⟨v1, e1, by omega, w1, fun x hx => by
      rw [val1 x hx]; cases wireVal gs x a <;> rfl⟩
  · simp only [addEqConst, ↓reduceIte]
    exact ⟨hv, extends_rfl gs, by omega, ha, fun x _ => by
      cases wireVal gs x a <;> rfl⟩

def initXWires (k s w0 w1 : ℕ) (idx : ℕ) : ℕ :=
  if initX k s idx then w1 else w0

def buildSolveStep (k : ℕ) (gs : List Gate) (xw : ℕ → ℕ) (t : ℕ) : List Gate × (ℕ → ℕ) :=
  let n := k + k
  let i := k - 1 - t
  let r1 := addXor n gs (xw ((i + 1) % k)) (xw ((i + 2) % k))
  let r2 := addXor n r1.1 (xw i) r1.2
  let r3 := addXor n r2.1 r1.2 (xw ((i + 3) % k))
  let r4 := addNot n r3.1 r2.2
  let r5 := addAnd n r4.1 r4.2 r3.2
  let r6 := addXor n r5.1 (xw i) r5.2
  let r7 := addXor n r6.1 r6.2 ((i + 1) % k)
  let r8 := addXorConst n r7.1 r7.2 ((constK k 1).testBit i)
  (r8.1, fun idx => if idx = k - 2 - t then r8.2 else xw idx)

def buildSolveIter (k s w0 w1 : ℕ) (gs : List Gate) : ℕ → List Gate × (ℕ → ℕ)
  | 0 => (gs, initXWires k s w0 w1)
  | t + 1 =>
    let r := buildSolveIter k s w0 w1 gs t
    buildSolveStep k r.1 r.2 t

lemma buildSolveStep_spec {k u t : ℕ} {gs : List Gate} {xw : ℕ → ℕ} {xs : ℕ → Bool}
    (hk : 8 ≤ k) (hv : Valid (k + k) gs)
    (hbd : ∀ idx < k, xw idx < k + k + gs.length)
    (hval : ∀ x : List Bool, x.length = k + k →
      (∀ j < k, x.getD j false = u.testBit j) →
      ∀ idx < k, wireVal gs x (xw idx) = xs idx) :
    let r := buildSolveStep k gs xw t
    Valid (k + k) r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 23 ∧
      (∀ idx < k, r.2 idx < k + k + r.1.length) ∧
      (∀ x : List Bool, x.length = k + k →
        (∀ j < k, x.getD j false = u.testBit j) →
        ∀ idx < k, wireVal r.1 x (r.2 idx) = solveStep k u xs t idx) := by
  set n := k + k
  set i := k - 1 - t
  have hi : i < k := by omega
  have hi1 : (i + 1) % k < k := Nat.mod_lt _ (by omega)
  have hi2 : (i + 2) % k < k := Nat.mod_lt _ (by omega)
  have hi3 : (i + 3) % k < k := Nat.mod_lt _ (by omega)
  set r1 := addXor n gs (xw ((i + 1) % k)) (xw ((i + 2) % k)) with hr1
  have h1 := addXor_spec hv (hbd _ hi1) (hbd _ hi2)
  dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨v1, e1, l1, w1, val1⟩
  set r2 := addXor n r1.1 (xw i) r1.2 with hr2
  have h2 := addXor_spec (a := xw i) (b := r1.2) v1 (by have := hbd _ hi; omega) w1
  dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨v2, e2, l2, w2, val2⟩
  set r3 := addXor n r2.1 r1.2 (xw ((i + 3) % k)) with hr3
  have h3 := addXor_spec (a := r1.2) (b := xw ((i + 3) % k)) v2 (by omega) (by have := hbd _ hi3; omega)
  dsimp only at h3; rw [← hr3] at h3
  rcases h3 with ⟨v3, e3, l3, w3, val3⟩
  set r4 := addNot n r3.1 r2.2 with hr4
  have h4 := addNot_spec (a := r2.2) v3 (by omega)
  dsimp only at h4; rw [← hr4] at h4
  rcases h4 with ⟨v4, e4, l4, w4, val4⟩
  set r5 := addAnd n r4.1 r4.2 r3.2 with hr5
  have h5 := addAnd_spec (a := r4.2) (b := r3.2) v4 w4 (by omega)
  dsimp only at h5; rw [← hr5] at h5
  rcases h5 with ⟨v5, e5, l5, w5, val5⟩
  set r6 := addXor n r5.1 (xw i) r5.2 with hr6
  have h6 := addXor_spec (a := xw i) (b := r5.2) v5 (by have := hbd _ hi; omega) w5
  dsimp only at h6; rw [← hr6] at h6
  rcases h6 with ⟨v6, e6, l6, w6, val6⟩
  set r7 := addXor n r6.1 r6.2 ((i + 1) % k) with hr7
  have h7 := addXor_spec (a := r6.2) (b := (i + 1) % k) v6 w6 (by omega : (i + 1) % k < n + r6.1.length)
  dsimp only at h7; rw [← hr7] at h7
  rcases h7 with ⟨v7, e7, l7, w7, val7⟩
  set r8 := addXorConst n r7.1 r7.2 ((constK k 1).testBit i) with hr8
  have h8 := addXorConst_spec ((constK k 1).testBit i) v7 w7
  dsimp only at h8; rw [← hr8] at h8
  rcases h8 with ⟨v8, e8, l8, w8, val8⟩
  have e02 : Extends gs r2.1 := extends_trans e1 e2
  have e05 : Extends gs r5.1 := extends_trans e02 (extends_trans e3 (extends_trans e4 e5))
  have e08 : Extends gs r8.1 := extends_trans e05 (extends_trans e6 (extends_trans e7 e8))
  change Valid n r8.1 ∧ Extends gs r8.1 ∧ r8.1.length ≤ gs.length + 23 ∧
    (∀ idx < k, (if idx = k - 2 - t then r8.2 else xw idx) < n + r8.1.length) ∧
    (∀ x : List Bool, x.length = n → (∀ j < k, x.getD j false = u.testBit j) →
      ∀ idx < k, wireVal r8.1 x (if idx = k - 2 - t then r8.2 else xw idx) = solveStep k u xs t idx)
  refine ⟨v8, e08, by omega, ?_, ?_⟩
  · intro idx hidx
    by_cases heq : idx = k - 2 - t
    · rw [ite_eq_left_iff.mpr (fun h => absurd heq h)]; exact w8
    · rw [ite_eq_right_iff.mpr (fun h => absurd h heq)]
      have hlen := extends_len e08
      have := hbd idx hidx
      omega
  · intro x hx hu idx hidx
    simp only [solveStep]
    by_cases heq : idx = k - 2 - t
    · rw [ite_eq_left_iff.mpr (fun h => absurd heq h), ite_eq_left_iff.mpr (fun h => absurd heq h)]
      have hx1 : wireVal r1.1 x r1.2 = xor (xs ((i + 1) % k)) (xs ((i + 2) % k)) := by
        rw [val1 x hx, hval x hx hu _ hi1, hval x hx hu _ hi2]
      have hx2 : wireVal r2.1 x r2.2 = xor (xs i) (xor (xs ((i + 1) % k)) (xs ((i + 2) % k))) := by
        rw [val2 x hx, wireVal_of_extends e1 x hx _ (hbd _ hi), hval x hx hu _ hi, hx1]
      have hx3 : wireVal r3.1 x r3.2 =
          xor (xor (xs ((i + 1) % k)) (xs ((i + 2) % k))) (xs ((i + 3) % k)) := by
        rw [val3 x hx, wireVal_of_extends e2 x hx r1.2 w1, hx1,
          wireVal_of_extends e02 x hx _ (hbd _ hi3), hval x hx hu _ hi3]
      have hx4 : wireVal r4.1 x r4.2 = !(xor (xs i) (xor (xs ((i + 1) % k)) (xs ((i + 2) % k)))) := by
        rw [val4 x hx, wireVal_of_extends e3 x hx r2.2 w2, hx2]
      have hx5 : wireVal r5.1 x r5.2 =
          (!(xor (xs i) (xor (xs ((i + 1) % k)) (xs ((i + 2) % k)))) &&
            xor (xor (xs ((i + 1) % k)) (xs ((i + 2) % k))) (xs ((i + 3) % k))) := by
        rw [val5 x hx, hx4, wireVal_of_extends e4 x hx r3.2 w3, hx3]
      have hx6 : wireVal r6.1 x r6.2 =
          xor (xs i) (!(xor (xs i) (xor (xs ((i + 1) % k)) (xs ((i + 2) % k)))) &&
            xor (xor (xs ((i + 1) % k)) (xs ((i + 2) % k))) (xs ((i + 3) % k))) := by
        rw [val6 x hx, wireVal_of_extends e05 x hx _ (hbd _ hi), hval x hx hu _ hi, hx5]
      have hx7 : wireVal r7.1 x r7.2 =
          xor (xor (xs i) (!(xor (xs i) (xor (xs ((i + 1) % k)) (xs ((i + 2) % k)))) &&
            xor (xor (xs ((i + 1) % k)) (xs ((i + 2) % k))) (xs ((i + 3) % k))))
            (u.testBit ((i + 1) % k)) := by
        rw [val7 x hx, hx6, wireVal_input r6.1 x hx _ (by omega), hu _ hi1]
      rw [val8 x hx, hx7]
    · rw [ite_eq_right_iff.mpr (fun h => absurd h heq),
        ite_eq_right_iff.mpr (fun h => absurd h heq),
        wireVal_of_extends e08 x hx _ (hbd idx hidx), hval x hx hu idx hidx]

lemma buildSolveIter_spec {k s w0 w1 : ℕ} {gs : List Gate} (hk : 8 ≤ k) (t : ℕ)
    (hv : Valid (k + k) gs)
    (hw0 : w0 < k + k + gs.length) (hw1 : w1 < k + k + gs.length)
    (hv0 : ∀ x : List Bool, x.length = k + k → wireVal gs x w0 = false)
    (hv1 : ∀ x : List Bool, x.length = k + k → wireVal gs x w1 = true) :
    let r := buildSolveIter k s w0 w1 gs t
    Valid (k + k) r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 23 * t ∧
      (∀ idx < k, r.2 idx < k + k + r.1.length) ∧
      (∀ u, ∀ x : List Bool, x.length = k + k →
        (∀ j < k, x.getD j false = u.testBit j) →
        ∀ idx < k, wireVal r.1 x (r.2 idx) = solveXIter k s u t idx) := by
  induction t with
  | zero =>
    refine ⟨hv, extends_rfl gs, by simp [buildSolveIter], ?_, ?_⟩
    · intro idx _
      simp only [buildSolveIter, initXWires]
      cases initX k s idx <;> simp [hw0, hw1]
    · intro u x hx _ idx _
      simp only [buildSolveIter, initXWires, solveXIter]
      cases initX k s idx <;> simp [hv0 x hx, hv1 x hx]
  | succ t ih =>
    rcases ih with ⟨v1, e1, l1, bd1, val1⟩
    set r1 := buildSolveIter k s w0 w1 gs t
    change let r2 := buildSolveStep k r1.1 r1.2 t
      Valid (k + k) r2.1 ∧ Extends gs r2.1 ∧ r2.1.length ≤ gs.length + 23 * (t + 1) ∧
        (∀ idx < k, r2.2 idx < k + k + r2.1.length) ∧
        (∀ u, ∀ x : List Bool, x.length = k + k →
          (∀ j < k, x.getD j false = u.testBit j) →
          ∀ idx < k, wireVal r2.1 x (r2.2 idx) = solveStep k u (solveXIter k s u t) t idx)
    have hstep := fun u => buildSolveStep_spec (u := u) (t := t) hk v1 bd1 (val1 u)
    rcases hstep 0 with ⟨v2, e2, l2, bd2, _⟩
    refine ⟨v2, extends_trans e1 e2, by omega, bd2, ?_⟩
    intro u x hx hu idx hidx
    exact (hstep u).2.2.2.2 x hx hu idx hidx

def buildMapXor (n : ℕ) (gs : List Gate) (f1 f2 : ℕ → ℕ) : ℕ → List Gate × (ℕ → ℕ)
  | 0 => (gs, fun _ => 0)
  | m + 1 =>
    let r1 := buildMapXor n gs f1 f2 m
    let r2 := addXor n r1.1 (f1 m) (f2 m)
    (r2.1, fun j => if j = m then r2.2 else r1.2 j)

lemma buildMapXor_spec {n m : ℕ} {gs : List Gate} {f1 f2 : ℕ → ℕ}
    (hv : Valid n gs)
    (hb1 : ∀ j < m, f1 j < n + gs.length)
    (hb2 : ∀ j < m, f2 j < n + gs.length) :
    let r := buildMapXor n gs f1 f2 m
    Valid n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 4 * m ∧
      (∀ j < m, r.2 j < n + r.1.length) ∧
      (∀ x : List Bool, x.length = n →
        ∀ j < m, wireVal r.1 x (r.2 j) = xor (wireVal gs x (f1 j)) (wireVal gs x (f2 j))) := by
  induction m with
  | zero =>
    exact ⟨hv, extends_rfl gs, by simp [buildMapXor], fun _ h => by omega, fun _ _ _ h => by omega⟩
  | succ m ih =>
    rcases ih (fun j hj => hb1 j (by omega)) (fun j hj => hb2 j (by omega)) with
      ⟨v1, e1, l1, bd1, val1⟩
    set r1 := buildMapXor n gs f1 f2 m with hr1
    have h1m : f1 m < n + r1.1.length := by have := hb1 m (by omega); omega
    have h2m : f2 m < n + r1.1.length := by have := hb2 m (by omega); omega
    set r2 := addXor n r1.1 (f1 m) (f2 m) with hr2
    have h2 := addXor_spec v1 h1m h2m
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, w2, val2⟩
    change Valid n r2.1 ∧ Extends gs r2.1 ∧ r2.1.length = gs.length + 4 * (m + 1) ∧
      (∀ j < m + 1, (if j = m then r2.2 else r1.2 j) < n + r2.1.length) ∧
      (∀ x : List Bool, x.length = n →
        ∀ j < m + 1, wireVal r2.1 x (if j = m then r2.2 else r1.2 j) =
          xor (wireVal gs x (f1 j)) (wireVal gs x (f2 j)))
    refine ⟨v2, extends_trans e1 e2, by omega, ?_, ?_⟩
    · intro j hj
      by_cases heq : j = m
      · rw [ite_eq_left_iff.mpr (fun h => absurd heq h)]; exact w2
      · rw [ite_eq_right_iff.mpr (fun h => absurd h heq)]; have := bd1 j (by omega); omega
    · intro x hx j hj
      by_cases heq : j = m
      · subst heq
        rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), val2 x hx,
          wireVal_of_extends e1 x hx (f1 j) (hb1 j hj),
          wireVal_of_extends e1 x hx (f2 j) (hb2 j hj)]
      · rw [ite_eq_right_iff.mpr (fun h => absurd h heq),
          wireVal_of_extends e2 x hx _ (bd1 j (by omega)), val1 x hx j (by omega)]

def buildColPass (k : ℕ) (gs : List Gate) (ww dw : ℕ → ℕ) (acc : ℕ) : ℕ → List Gate × ℕ
  | 0 => (gs, acc)
  | t + 1 =>
    let r1 := buildColPass k gs ww dw acc t
    let n := k + k
    let i := remK k + t
    let r2 := addNot n r1.1 (dw ((i + 1) % k))
    let r3 := addAnd n r2.1 r2.2 (dw ((i + 2) % k))
    let r4 := addXor n r3.1 (dw i) r3.2
    let r5 := addXor n r4.1 r4.2 (ww ((i + k - 4) % k))
    let r6 := addEqConst n r5.1 r5.2 ((constK k 2).testBit i)
    addAnd n r6.1 r1.2 r6.2

lemma buildColPass_spec {k : ℕ} {gs : List Gate} {ww dw : ℕ → ℕ} {acc : ℕ}
    (hk : 8 ≤ k) (t : ℕ) (ht : t ≤ halfK k)
    (hv : Valid (k + k) gs)
    (hbw : ∀ j < k, ww j < k + k + gs.length)
    (hbd : ∀ j < k, dw j < k + k + gs.length)
    (hba : acc < k + k + gs.length) :
    let r := buildColPass k gs ww dw acc t
    Valid (k + k) r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 12 * t ∧
      r.2 < k + k + r.1.length ∧
      (∀ x : List Bool, x.length = k + k →
        wireVal r.1 x r.2 =
          (wireVal gs x acc &&
            (List.range t).all (fun s =>
              let i := remK k + s
              let sd := xor (wireVal gs x (dw i))
                (!(wireVal gs x (dw ((i + 1) % k))) && wireVal gs x (dw ((i + 2) % k)))
              !(xor (xor sd (wireVal gs x (ww ((i + k - 4) % k)))) ((constK k 2).testBit i))))) := by
  have hh : halfK k = (k + 1) / 2 := rfl
  have hr : remK k = k - halfK k := rfl
  induction t with
  | zero =>
    exact ⟨hv, extends_rfl gs, by simp [buildColPass], hba, fun x _ => by simp [buildColPass]⟩
  | succ t ih =>
    rcases ih (by omega) with ⟨v1, e1, l1, wa1, val1⟩
    set n := k + k
    set i := remK k + t
    have hi : i < k := by omega
    have hi1 : (i + 1) % k < k := Nat.mod_lt _ (by omega)
    have hi2 : (i + 2) % k < k := Nat.mod_lt _ (by omega)
    have hi4 : (i + k - 4) % k < k := Nat.mod_lt _ (by omega)
    set r1 := buildColPass k gs ww dw acc t with hr1
    have hlen1 : gs.length ≤ r1.1.length := extends_len e1
    set r2 := addNot n r1.1 (dw ((i + 1) % k)) with hr2
    have h2 := addNot_spec (a := dw ((i + 1) % k)) v1 (by have := hbd _ hi1; omega)
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, w2, val2⟩
    set r3 := addAnd n r2.1 r2.2 (dw ((i + 2) % k)) with hr3
    have h3 := addAnd_spec (a := r2.2) (b := dw ((i + 2) % k)) v2 w2 (by have := hbd _ hi2; omega)
    dsimp only at h3; rw [← hr3] at h3
    rcases h3 with ⟨v3, e3, l3, w3, val3⟩
    set r4 := addXor n r3.1 (dw i) r3.2 with hr4
    have h4 := addXor_spec (a := dw i) (b := r3.2) v3 (by have := hbd _ hi; omega) w3
    dsimp only at h4; rw [← hr4] at h4
    rcases h4 with ⟨v4, e4, l4, w4, val4⟩
    set r5 := addXor n r4.1 r4.2 (ww ((i + k - 4) % k)) with hr5
    have h5 := addXor_spec (a := r4.2) (b := ww ((i + k - 4) % k)) v4 w4 (by have := hbw _ hi4; omega)
    dsimp only at h5; rw [← hr5] at h5
    rcases h5 with ⟨v5, e5, l5, w5, val5⟩
    set r6 := addEqConst n r5.1 r5.2 ((constK k 2).testBit i) with hr6
    have h6 := addEqConst_spec ((constK k 2).testBit i) v5 w5
    dsimp only at h6; rw [← hr6] at h6
    rcases h6 with ⟨v6, e6, l6, w6, val6⟩
    set r7 := addAnd n r6.1 r1.2 r6.2 with hr7
    have hlen6 : r1.1.length ≤ r6.1.length :=
      extends_len (extends_trans e2 (extends_trans e3 (extends_trans e4 (extends_trans e5 e6))))
    have h7 := addAnd_spec (a := r1.2) (b := r6.2) v6 (by omega) w6
    dsimp only at h7; rw [← hr7] at h7
    rcases h7 with ⟨v7, e7, l7, w7, val7⟩
    have e16 : Extends r1.1 r6.1 :=
      extends_trans e2 (extends_trans e3 (extends_trans e4 (extends_trans e5 e6)))
    have e07 : Extends gs r7.1 := extends_trans e1 (extends_trans e16 e7)
    change Valid n r7.1 ∧ Extends gs r7.1 ∧ r7.1.length ≤ gs.length + 12 * (t + 1) ∧
      r7.2 < n + r7.1.length ∧
      (∀ x : List Bool, x.length = n →
        wireVal r7.1 x r7.2 =
          (wireVal gs x acc &&
            (List.range (t + 1)).all (fun s =>
              let i := remK k + s
              let sd := xor (wireVal gs x (dw i))
                (!(wireVal gs x (dw ((i + 1) % k))) && wireVal gs x (dw ((i + 2) % k)))
              !(xor (xor sd (wireVal gs x (ww ((i + k - 4) % k)))) ((constK k 2).testBit i)))))
    refine ⟨v7, e07, by omega, w7, ?_⟩
    intro x hx
    rw [val7 x hx, wireVal_of_extends e16 x hx r1.2 wa1, val1 x hx,
      val6 x hx, val5 x hx, val4 x hx, val3 x hx, val2 x hx,
      wireVal_of_extends e1 x hx _ (hbd _ hi1),
      wireVal_of_extends (extends_trans e1 e2) x hx _ (hbd _ hi2),
      wireVal_of_extends (extends_trans e1 (extends_trans e2 e3)) x hx _ (hbd _ hi),
      wireVal_of_extends (extends_trans e1 (extends_trans e2 (extends_trans e3 e4))) x hx _ (hbw _ hi4),
      List.range_succ, List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_assoc]

def buildSlot (k s w0 w1 : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let n := k + k
  let r1 := buildSolveIter k s w0 w1 gs (halfK k)
  let r2 := buildMapXor n r1.1 (fun j => r1.2 ((j + 1) % k)) (fun j => (j + 1) % k) k
  let r3 := buildMapXor n r2.1 (fun j => r2.2 ((j + k - 3) % k)) (fun j => k + j) k
  let r4 := buildMapXor n r3.1 r3.2 (fun j => r3.2 ((j + k - 2) % k)) k
  let r5 := buildMapXor n r4.1 r4.2 (fun j => r3.2 ((j + 2) % k)) k
  buildColPass k r5.1 r2.2 r5.2 w1 (halfK k)

lemma buildSlot_spec {k s w0 w1 : ℕ} {gs : List Gate} (hk : 8 ≤ k)
    (hv : Valid (k + k) gs)
    (hw0 : w0 < k + k + gs.length) (hw1 : w1 < k + k + gs.length)
    (hv0 : ∀ x : List Bool, x.length = k + k → wireVal gs x w0 = false)
    (hv1 : ∀ x : List Bool, x.length = k + k → wireVal gs x w1 = true) :
    let r := buildSlot k s w0 w1 gs
    Valid (k + k) r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + (35 * halfK k + 16 * k) ∧
      r.2 < k + k + r.1.length ∧
      (∀ u v : ℕ, u < 2 ^ k → v < 2 ^ k →
        ∀ x : List Bool, x.length = k + k →
          (∀ j < k, x.getD j false = u.testBit j) →
          (∀ j < k, x.getD (k + j) false = v.testBit j) →
          wireVal r.1 x r.2 = decide (secondK k (keyOfSlot k s u) v < slotsK k)) := by
  have hk0 : 0 < k := by omega
  have hh : halfK k = (k + 1) / 2 := rfl
  have hr : remK k = k - halfK k := rfl
  set n := k + k
  set r1 := buildSolveIter k s w0 w1 gs (halfK k) with hr1
  have h1 := buildSolveIter_spec (s := s) hk (halfK k) hv hw0 hw1 hv0 hv1
  dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨v1, e1, l1, bd1, val1⟩
  set r2 := buildMapXor n r1.1 (fun j => r1.2 ((j + 1) % k)) (fun j => (j + 1) % k) k with hr2
  have h2 := buildMapXor_spec (m := k) (f1 := fun j => r1.2 ((j + 1) % k)) (f2 := fun j => (j + 1) % k)
      v1 (fun j _ => bd1 _ (Nat.mod_lt _ hk0)) (fun j _ => by have := Nat.mod_lt (j + 1) hk0; omega)
  dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨v2, e2, l2, bd2, val2⟩
  set r3 := buildMapXor n r2.1 (fun j => r2.2 ((j + k - 3) % k)) (fun j => k + j) k with hr3
  have h3 := buildMapXor_spec (m := k) (f1 := fun j => r2.2 ((j + k - 3) % k)) (f2 := fun j => k + j)
      v2 (fun j _ => bd2 _ (Nat.mod_lt _ hk0)) (fun j hj => by omega)
  dsimp only at h3; rw [← hr3] at h3
  rcases h3 with ⟨v3, e3, l3, bd3, val3⟩
  set r4 := buildMapXor n r3.1 r3.2 (fun j => r3.2 ((j + k - 2) % k)) k with hr4
  have h4 := buildMapXor_spec (m := k) (f1 := r3.2) (f2 := fun j => r3.2 ((j + k - 2) % k))
      v3 (fun j hj => bd3 j hj) (fun j _ => bd3 _ (Nat.mod_lt _ hk0))
  dsimp only at h4; rw [← hr4] at h4
  rcases h4 with ⟨v4, e4, l4, bd4, val4⟩
  set r5 := buildMapXor n r4.1 r4.2 (fun j => r3.2 ((j + 2) % k)) k with hr5
  have h5 := buildMapXor_spec (m := k) (f1 := r4.2) (f2 := fun j => r3.2 ((j + 2) % k))
      v4 (fun j hj => bd4 j hj) (fun j _ => by have := bd3 ((j + 2) % k) (Nat.mod_lt _ hk0); omega)
  dsimp only at h5; rw [← hr5] at h5
  rcases h5 with ⟨v5, e5, l5, bd5, val5⟩
  have e05 : Extends gs r5.1 :=
    extends_trans e1 (extends_trans e2 (extends_trans e3 (extends_trans e4 e5)))
  have hlen05 : gs.length ≤ r5.1.length := extends_len e05
  have e25 : Extends r2.1 r5.1 := extends_trans e3 (extends_trans e4 e5)
  have hlen25 : r2.1.length ≤ r5.1.length := extends_len e25
  set r6 := buildColPass k r5.1 r2.2 r5.2 w1 (halfK k) with hr6
  have h6 := buildColPass_spec (ww := r2.2) (dw := r5.2) (acc := w1)
      hk (halfK k) le_rfl v5 (fun j hj => by have := bd2 j hj; omega) bd5 (by omega)
  dsimp only at h6; rw [← hr6] at h6
  rcases h6 with ⟨v6, e6, l6, w6, val6⟩
  change Valid n r6.1 ∧ Extends gs r6.1 ∧ r6.1.length ≤ gs.length + (35 * halfK k + 16 * k) ∧
    r6.2 < n + r6.1.length ∧
    (∀ u v : ℕ, u < 2 ^ k → v < 2 ^ k →
      ∀ x : List Bool, x.length = n →
        (∀ j < k, x.getD j false = u.testBit j) →
        (∀ j < k, x.getD (k + j) false = v.testBit j) →
        wireVal r6.1 x r6.2 = decide (secondK k (keyOfSlot k s u) v < slotsK k))
  refine ⟨v6, extends_trans e05 e6, by omega, w6, ?_⟩
  intro u v _ hv_lt x hx hxu hxv
  rw [val6 x hx, wireVal_of_extends e05 x hx w1 hw1, hv1 x hx, Bool.true_and]
  set w := keyOfSlot k s u
  have hw_lt : w < 2 ^ k := keyOfSlot_lt k s u
  set z := rotK k 3 w ^^^ v
  have hz_lt : z < 2 ^ k := xor_lt_two_pow (rotK_lt 3 w) hv_lt
  set d := z ^^^ rotK k 2 z ^^^ rotK k (k - 2) z
  have hww2 : ∀ j < k, wireVal r2.1 x (r2.2 j) = w.testBit j := by
    intro j hj
    rw [val2 x hx j hj, val1 u x hx hxu _ (Nat.mod_lt _ hk0),
      wireVal_input r1.1 x hx _ (by have := Nat.mod_lt (j + 1) hk0; omega),
      hxu _ (Nat.mod_lt _ hk0)]
    unfold w keyOfSlot
    rw [bitsToNat_testBit k _ j hj]
    rfl
  have hww5 : ∀ j < k, wireVal r5.1 x (r2.2 j) = w.testBit j := by
    intro j hj
    rw [wireVal_of_extends e25 x hx (r2.2 j) (bd2 j hj), hww2 j hj]
  have hzw3 : ∀ j < k, wireVal r3.1 x (r3.2 j) = z.testBit j := by
    intro j hj
    rw [val3 x hx j hj, hww2 _ (Nat.mod_lt _ hk0),
      wireVal_input r2.1 x hx _ (by omega), hxv j hj]
    simp only [z, Nat.testBit_xor, rotK_testBit hk0 hw_lt hj]
    have h3 : 3 % k = 3 := Nat.mod_eq_of_lt (by omega)
    rw [h3]
  have hdw5 : ∀ j < k, wireVal r5.1 x (r5.2 j) = d.testBit j := by
    intro j hj
    rw [val5 x hx j hj, val4 x hx j hj,
      wireVal_of_extends e4 x hx (r3.2 ((j + 2) % k)) (bd3 _ (Nat.mod_lt _ hk0)),
      hzw3 j hj, hzw3 _ (Nat.mod_lt _ hk0), hzw3 _ (Nat.mod_lt _ hk0)]
    simp only [d, Nat.testBit_xor, rotK_testBit hk0 hz_lt hj]
    have h2 : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
    have hkm2 : (k - 2) % k = k - 2 := Nat.mod_eq_of_lt (by omega)
    have hadd2 : (j + k - (k - 2)) % k = (j + 2) % k := by congr 1; omega
    rw [h2, hkm2, hadd2]
  have hsec_eq : ∀ i < k, (secondK k w v).testBit i =
      xor (xor (xor (d.testBit i) (!(d.testBit ((i + 1) % k)) && d.testBit ((i + 2) % k)))
        (w.testBit ((i + k - 4) % k))) ((constK k 2).testBit i) := by
    intro i hi
    have h4 : 4 % k = 4 := Nat.mod_eq_of_lt (by omega)
    unfold secondK
    change (stepK k d ^^^ rotK k 4 w ^^^ constK k 2).testBit i = _
    rw [Nat.testBit_xor, Nat.testBit_xor, stepK_testBit hi, rotK_testBit hk0 hw_lt hi, h4]
  apply Bool.eq_iff_iff.mpr
  rw [List.all_eq_true, decide_eq_true_eq, slotsK,
    lt_two_pow_iff_high_bits_false (secondK_lt k w v)]
  constructor
  · intro hall i hi1 hi2
    have hmem : i - remK k ∈ List.range (halfK k) := List.mem_range.mpr (by omega)
    have hbi := hall (i - remK k) hmem
    have heqi : remK k + (i - remK k) = i := by omega
    simp only [heqi] at hbi
    rw [hdw5 i hi2, hdw5 _ (Nat.mod_lt _ hk0), hdw5 _ (Nat.mod_lt _ hk0),
      hww5 _ (Nat.mod_lt _ hk0)] at hbi
    rw [hsec_eq i hi2]
    simpa [Bool.not_eq_true'] using hbi
  · intro hlt t ht
    rw [List.mem_range] at ht
    set i := remK k + t
    have hi1 : remK k ≤ i := by omega
    have hi2 : i < k := by omega
    have h0 := hlt i hi1 hi2
    rw [hsec_eq i hi2] at h0
    rw [hdw5 i hi2, hdw5 _ (Nat.mod_lt _ hk0), hdw5 _ (Nat.mod_lt _ hk0),
      hww5 _ (Nat.mod_lt _ hk0), h0]
    rfl

def buildAllSlots (k w0 w1 : ℕ) (gs : List Gate) (acc : ℕ) : ℕ → List Gate × ℕ
  | 0 => (gs, acc)
  | m + 1 =>
    let r1 := buildAllSlots k w0 w1 gs acc m
    let r2 := buildSlot k m w0 w1 r1.1
    addOr (k + k) r2.1 r1.2 r2.2

lemma buildAllSlots_spec {k w0 w1 : ℕ} {gs : List Gate} {acc : ℕ} (hk : 8 ≤ k) (m : ℕ)
    (hv : Valid (k + k) gs)
    (hw0 : w0 < k + k + gs.length) (hw1 : w1 < k + k + gs.length)
    (hba : acc < k + k + gs.length)
    (hv0 : ∀ x : List Bool, x.length = k + k → wireVal gs x w0 = false)
    (hv1 : ∀ x : List Bool, x.length = k + k → wireVal gs x w1 = true) :
    let r := buildAllSlots k w0 w1 gs acc m
    Valid (k + k) r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + m * (35 * halfK k + 16 * k + 1) ∧
      r.2 < k + k + r.1.length ∧
      (∀ u v : ℕ, u < 2 ^ k → v < 2 ^ k →
        ∀ x : List Bool, x.length = k + k →
          (∀ j < k, x.getD j false = u.testBit j) →
          (∀ j < k, x.getD (k + j) false = v.testBit j) →
          wireVal r.1 x r.2 =
            (wireVal gs x acc ||
              (List.range m).any (fun s => decide (secondK k (keyOfSlot k s u) v < slotsK k)))) := by
  induction m with
  | zero =>
    exact ⟨hv, extends_rfl gs, by simp [buildAllSlots], hba,
      fun _ _ _ _ _ _ _ _ => by simp [buildAllSlots]⟩
  | succ m ih =>
    rcases ih with ⟨v1, e1, l1, wa1, val1⟩
    set r1 := buildAllSlots k w0 w1 gs acc m
    have hlen1 : gs.length ≤ r1.1.length := extends_len e1
    have hw01 : w0 < k + k + r1.1.length := by omega
    have hw11 : w1 < k + k + r1.1.length := by omega
    have hv01 : ∀ x : List Bool, x.length = k + k → wireVal r1.1 x w0 = false := fun x hx => by
      rw [wireVal_of_extends e1 x hx w0 hw0, hv0 x hx]
    have hv11 : ∀ x : List Bool, x.length = k + k → wireVal r1.1 x w1 = true := fun x hx => by
      rw [wireVal_of_extends e1 x hx w1 hw1, hv1 x hx]
    set r2 := buildSlot k m w0 w1 r1.1 with hr2
    have h2 := buildSlot_spec (s := m) hk v1 hw01 hw11 hv01 hv11
    dsimp only at h2; rw [← hr2] at h2
    rcases h2 with ⟨v2, e2, l2, ws2, val2⟩
    have hlen2 : r1.1.length ≤ r2.1.length := extends_len e2
    set r3 := addOr (k + k) r2.1 r1.2 r2.2 with hr3
    have h3 := addOr_spec (a := r1.2) (b := r2.2) v2 (by omega) ws2
    dsimp only at h3; rw [← hr3] at h3
    rcases h3 with ⟨v3, e3, l3, w3, val3⟩
    change Valid (k + k) r3.1 ∧ Extends gs r3.1 ∧
      r3.1.length ≤ gs.length + (m + 1) * (35 * halfK k + 16 * k + 1) ∧
      r3.2 < k + k + r3.1.length ∧
      (∀ u v : ℕ, u < 2 ^ k → v < 2 ^ k →
        ∀ x : List Bool, x.length = k + k →
          (∀ j < k, x.getD j false = u.testBit j) →
          (∀ j < k, x.getD (k + j) false = v.testBit j) →
          wireVal r3.1 x r3.2 =
            (wireVal gs x acc ||
              (List.range (m + 1)).any (fun s => decide (secondK k (keyOfSlot k s u) v < slotsK k))))
    refine ⟨v3, extends_trans e1 (extends_trans e2 e3), ?_, w3, ?_⟩
    · have hmul : (m + 1) * (35 * halfK k + 16 * k + 1) =
          m * (35 * halfK k + 16 * k + 1) + (35 * halfK k + 16 * k + 1) := by ring
      omega
    · intro u v hu hv_lt x hx hxu hxv
      rw [val3 x hx, wireVal_of_extends e2 x hx r1.2 wa1, val1 u v hu hv_lt x hx hxu hxv,
        val2 u v hu hv_lt x hx hxu hxv,
        List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

def buildCircuit (k : ℕ) : Circuit :=
  let n := k + k
  let r1 := addConst0 n []
  let r2 := addConst1 n r1.1
  let r3 := buildAllSlots k r1.2 r2.2 r2.1 r1.2 (slotsK k)
  ⟨r3.1, r3.2⟩

lemma size_bound (k : ℕ) (hk : 8 ≤ k) :
    2 + slotsK k * (35 * halfK k + 16 * k + 1) ≤ slotsK k * (36 * k) := by
  have hh : halfK k = (k + 1) / 2 := rfl
  have hr : remK k = k - halfK k := rfl
  have hslots : 2 ≤ slotsK k := by
    unfold slotsK
    have h4 : 4 ≤ remK k := by omega
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ remK k := Nat.pow_le_pow_right (by omega) (by omega)
  have hcoef : 35 * halfK k + 16 * k + 2 ≤ 36 * k := by omega
  calc 2 + slotsK k * (35 * halfK k + 16 * k + 1)
      ≤ slotsK k + slotsK k * (35 * halfK k + 16 * k + 1) := by omega
    _ = slotsK k * (35 * halfK k + 16 * k + 2) := by ring
    _ ≤ slotsK k * (36 * k) := Nat.mul_le_mul_left (slotsK k) hcoef

end PEqualNP.Outside.L_meta_25496_aux

theorem PEqualNP.Outside.L_meta_25496 : (∀ k : Nat, 8 ≤ k →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    let x := rot 1 rowKey ^^^ rowName
    step (x ^^^ rot 1 x ^^^ rot (k - 1) x) ^^^ rot 0 rowKey ^^^ constant 1
  let second := fun (colKey colName : Nat) =>
    let z := rot 3 colKey ^^^ colName
    step (z ^^^ rot 2 z ^^^ rot (k - 2) z) ^^^ rot 4 colKey ^^^ constant 2
  let slots := 2 ^ (k - (k + 1) / 2)
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < slots) && decide (second w col.val < slots))
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ slots * (36 * k) ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits) := by
  intro k hk
  open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
    PEqualNP.Represents PEqualNP.Outside.L_meta_25496_aux in
  have hv0 : Valid (k + k) [] := ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩
  set r1 := addConst0 (k + k) [] with hr1
  have h1 := addConst0_spec hv0
  dsimp only at h1; rw [← hr1] at h1
  rcases h1 with ⟨v1, e1, l1, w0lt, val0⟩
  set r2 := addConst1 (k + k) r1.1 with hr2
  have h2 := addConst1_spec v1
  dsimp only at h2; rw [← hr2] at h2
  rcases h2 with ⟨v2, e2, l2, w1lt, val1⟩
  have w0lt2 : r1.2 < k + k + r2.1.length := by omega
  have val02 : ∀ x : List Bool, x.length = k + k → wireVal r2.1 x r1.2 = false :=
    fun x hx => by rw [wireVal_of_extends e2 x hx r1.2 w0lt, val0 x hx]
  set r3 := buildAllSlots k r1.2 r2.2 r2.1 r1.2 (slotsK k) with hr3
  have h3 := buildAllSlots_spec hk (slotsK k) v2 w0lt2 w1lt w0lt2 val02 val1
  dsimp only at h3; rw [← hr3] at h3
  rcases h3 with ⟨v3, _, l3, _, val3⟩
  refine ⟨⟨r3.1, r3.2⟩, v3.1, v3.2, ?_, ?_⟩
  · have hsb := size_bound k hk
    change r3.1.length ≤ slotsK k * (36 * k)
    simp only [List.length_nil] at l1
    omega
  · intro bits
    set u := tableIndex (fun i : Fin k => bits (Fin.castAdd k i))
    set v := tableIndex (fun j : Fin k => bits (Fin.natAdd k j))
    have hu : u < 2 ^ k := tableIndex_lt _
    have hv_lt : v < 2 ^ k := tableIndex_lt _
    have hlen : (List.ofFn bits).length = k + k := List.length_ofFn
    have hxu : ∀ j < k, (List.ofFn bits).getD j false = u.testBit j := by
      intro j hj
      rw [tableIndex_testBit _ j hj]
      simp [List.getD, show j < k + k by omega]
    have hxv : ∀ j < k, (List.ofFn bits).getD (k + j) false = v.testBit j := by
      intro j hj
      rw [tableIndex_testBit _ j hj]
      simp only [List.getD, List.getElem?_ofFn, show k + j < k + k by omega, ↓reduceDIte,
        Option.getD_some, Fin.natAdd]
    have hev := val3 u v hu hv_lt (List.ofFn bits) hlen hxu hxv
    rw [val02 (List.ofFn bits) hlen, Bool.false_or] at hev
    change wireVal r3.1 (List.ofFn bits) r3.2 = _
    rw [hev]
    have hfu : (Fin.ofNat (2 ^ k) u).val = u := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hu]
    have hfv : (Fin.ofNat (2 ^ k) v).val = v := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt hv_lt]
    unfold adjFun
    change ((List.range (slotsK k)).any (fun s => decide (secondK k (keyOfSlot k s u) v < slotsK k))) =
      ((List.range (2 ^ k)).any (fun w =>
        decide (firstK k w (Fin.ofNat (2 ^ k) u).val < slotsK k) &&
        decide (secondK k w (Fin.ofNat (2 ^ k) v).val < slotsK k)))
    rw [hfu, hfv, ← graph_iff_slots hk hu]
