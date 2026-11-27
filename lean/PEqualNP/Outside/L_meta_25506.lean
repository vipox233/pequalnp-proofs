import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25506_aux

namespace BitBridge

private def stepBit (k word i : Nat) : Bool :=
  word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

private def wordStep (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i => if stepBit k word i then acc ||| 2 ^ i else acc) 0

private theorem testBit_foldl_set (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => if p j then a ||| 2 ^ j else a) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · cases p j <;> simp [hji, Ne.symm hji]

private theorem testBit_wordStep_all (k word i : Nat) :
    (wordStep k word).testBit i = (decide (i < k) && stepBit k word i) := by
  simp only [wordStep, testBit_foldl_set, Nat.zero_testBit, Bool.false_or, List.mem_range]

private theorem testBit_wordStep {k word i : Nat} (hi : i < k) :
    (wordStep k word).testBit i =
      (word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))) := by
  simp [testBit_wordStep_all, stepBit, hi]

private theorem wordStep_lt (k word : Nat) : wordStep k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_wordStep_all, Nat.not_lt_of_ge hi]

private theorem lt_two_pow_iff_testBit {n k a : Nat} (hn : n < 2 ^ k) :
    n < 2 ^ a ↔ ∀ i, a ≤ i → i < k → n.testBit i = false := by
  constructor
  · intro ha i hai _
    exact Nat.testBit_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hai))
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hai
    by_cases hi : i < k
    · exact h i hai hi
    · exact Nat.testBit_lt_two_pow
        (hn.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (Nat.le_of_not_gt hi)))

private def rot (k s w : Nat) : Nat :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

private theorem rot_lt {k s w : Nat} : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem bit_rot {k s w i : Nat} (wlt : w < 2 ^ k) (ilt : i < k) :
    (rot k s w).testBit i = w.testBit ((i + k - s % k) % k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  simp only [rot, Nat.testBit_mod_two_pow, ilt, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ i
  · have hz : w.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (wlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (i + k - s % k) % k = i - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega : k ≤ i + k - s % k), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (i + k - s % k) % k = k - s % k + i := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

private theorem lt_xor {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hm := Nat.pow_le_pow_right Nat.zero_lt_two hi
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hm),
    Nat.testBit_lt_two_pow (hb.trans_le hm)]

private theorem wordStep_eq (k word : Nat) :
    wordStep k word = (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0 := by
  unfold wordStep
  congr 1
  funext a j
  change (if stepBit k word j then a ||| 2 ^ j else a) =
    a ||| ((stepBit k word j).toNat <<< j)
  cases stepBit k word j <;> simp [Nat.shiftLeft_eq]

private theorem sub_cyclic {k a m : Nat} (hm : m ≤ k) (ha : m ≤ a) :
    (a % k + k - m) % k = (a - m) % k := by
  apply Nat.ModEq.add_right_cancel' m
  change ((a % k + k - m) + m) % k = ((a - m) + m) % k
  rw [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel ha, Nat.add_mod_right, Nat.mod_mod]

private theorem rbit {k w i : Nat} (h : i < k) {m : Nat} (hm : m < k)
    (hw : w < 2 ^ k) : (rot k m w).testBit i = w.testBit ((i + k - m) % k) := by
  rw [bit_rot hw h, Nat.mod_eq_of_lt hm]

end BitBridge

namespace Joint25506

open BitBridge
open PEqualNP.MetaComplexity (tableIndex)

private theorem pack_succ {n : Nat} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
        + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

private theorem pack_lt : ∀ {n : Nat} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n IH =>
    intro x
    rw [pack_succ, pow_succ]
    have := IH (fun i : Fin n => x i.castSucc)
    split <;> omega

private theorem bit_pack : ∀ {n : Nat} (x : Fin n → Bool) (i : Fin n),
    (tableIndex x).testBit i = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n IH =>
    intro x i
    have hlt := pack_lt (fun i : Fin n => x i.castSucc)
    rw [pack_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
    · change (tableIndex (fun i : Fin n => x i.castSucc) +
        (if x (Fin.last n) = true then 2 ^ n else 0)).testBit j.val = x j.castSucc
      cases x (Fin.last n) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · rw [Nat.add_zero]; exact IH _ j
      · rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]; exact IH _ j

private def constant (k t : Nat) : Nat := 3 ^ (k + t) % 2 ^ k
private def updateRound (k d e t w state : Nat) : Nat :=
  wordStep k (state ^^^ rot k d state ^^^ rot k (k - d) state) ^^^ rot k e w ^^^ constant k t

private def rowWord (k w u : Nat) : Nat → Nat
  | 0 => rot k 1 w ^^^ u
  | t + 1 => updateRound k 1 (2 * t) (t + 1) w (rowWord k w u t)

private def colWord (k r w v : Nat) : Nat → Nat
  | 0 => rot k 3 w ^^^ v
  | t + 1 => updateRound k 2 (3 * (t + 1) + 1) (r + (t + 1)) w (colWord k r w v t)

private theorem upd_lt (k d e t w state : Nat) : updateRound k d e t w state < 2 ^ k :=
  lt_xor (lt_xor (wordStep_lt _ _) rot_lt) (Nat.mod_lt _ (Nat.two_pow_pos _))

private theorem rowWord_lt {k w u : Nat} (hu : u < 2 ^ k) (t : Nat) : rowWord k w u t < 2 ^ k := by
  cases t
  · exact lt_xor rot_lt hu
  · exact upd_lt ..

private theorem colWord_lt {k r w v : Nat} (hv : v < 2 ^ k) (t : Nat) : colWord k r w v t < 2 ^ k := by
  cases t
  · exact lt_xor rot_lt hv
  · exact upd_lt ..

private theorem round_fold {α : Type*} (f : Nat → α) (op : α → Nat → α)
    (hf : ∀ j, f (j + 1) = op (f j) j) (t : Nat) :
    (List.range t).foldl op (f 0) = f t := by
  induction t with
  | zero => rfl
  | succ t IH => rw [List.range_succ, List.foldl_append, IH, List.foldl_cons, List.foldl_nil, hf]

private def AgreeCyc (k p L R : Nat) (w₁ w₂ : Nat) : Prop :=
  ∀ d : Nat, d ≤ L + R → w₁.testBit ((p + k - L + d) % k) = w₂.testBit ((p + k - L + d) % k)

private theorem agreeCyc_mono {k p L₁ R₁ L₂ R₂ w₁ w₂ : Nat}
    (hL : L₁ ≤ L₂) (hR : R₁ ≤ R₂) (hL2 : L₂ ≤ k)
    (H : AgreeCyc k p L₂ R₂ w₁ w₂) : AgreeCyc k p L₁ R₁ w₁ w₂ := by
  intro d hd
  have h1 := H (L₂ - L₁ + d) (by omega)
  have he : p + k - L₂ + (L₂ - L₁ + d) = p + k - L₁ + d := by omega
  rw [← he]
  exact h1

private theorem agreeCyc_shift {k p L R s δ w₁ w₂ : Nat}
    (hs : s ≤ k) (hL : L + s ≤ k) (hδ : δ ≤ s + 4)
    (H : AgreeCyc k p (L + s) (R + 4) w₁ w₂) :
    AgreeCyc k ((p + k - s + δ) % k) L R w₁ w₂ := by
  intro d hd
  have h1 := H (δ + d) (by omega)
  have he : ((p + k - s + δ) % k + k - L + d) % k = (p + k - (L + s) + (δ + d)) % k := by
    apply Nat.ModEq.add_right_cancel' (L + s)
    change (((p + k - s + δ) % k + k - L + d) + (L + s)) % k =
      ((p + k - (L + s) + (δ + d)) + (L + s)) % k
    have ea : (p + k - s + δ) % k + k - L + d + (L + s) =
        (p + k - s + δ) % k + (d + s) + k := by omega
    have eb : p + k - (L + s) + (δ + d) + (L + s) =
        (p + k - s + δ) + (d + s) := by omega
    rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
  rw [he]
  exact h1

private theorem agreeCyc_shift1 {k p L R δ w₁ w₂ : Nat}
    (hL : L + 1 ≤ k) (hδ : δ ≤ 4)
    (H : AgreeCyc k p (L + 1) (R + 3) w₁ w₂) :
    AgreeCyc k ((p + k - 1 + δ) % k) L R w₁ w₂ := by
  intro d hd
  have h1 := H (δ + d) (by omega)
  have he : ((p + k - 1 + δ) % k + k - L + d) % k = (p + k - (L + 1) + (δ + d)) % k := by
    apply Nat.ModEq.add_right_cancel' (L + 1)
    change (((p + k - 1 + δ) % k + k - L + d) + (L + 1)) % k =
      ((p + k - (L + 1) + (δ + d)) + (L + 1)) % k
    have ea : (p + k - 1 + δ) % k + k - L + d + (L + 1) =
        (p + k - 1 + δ) % k + (d + 1) + k := by omega
    have eb : p + k - (L + 1) + (δ + d) + (L + 1) =
        (p + k - 1 + δ) + (d + 1) := by omega
    rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
  rw [he]
  exact h1

private theorem agreeCyc_shift2 {k p L R δ w₁ w₂ : Nat}
    (hL : L + 2 ≤ k) (hδ : δ ≤ 6)
    (H : AgreeCyc k p (L + 2) (R + 4) w₁ w₂) :
    AgreeCyc k ((p + k - 2 + δ) % k) L R w₁ w₂ := by
  intro d hd
  have h1 := H (δ + d) (by omega)
  have he : ((p + k - 2 + δ) % k + k - L + d) % k = (p + k - (L + 2) + (δ + d)) % k := by
    apply Nat.ModEq.add_right_cancel' (L + 2)
    change (((p + k - 2 + δ) % k + k - L + d) + (L + 2)) % k =
      ((p + k - (L + 2) + (δ + d)) + (L + 2)) % k
    have ea : (p + k - 2 + δ) % k + k - L + d + (L + 2) =
        (p + k - 2 + δ) % k + (d + 2) + k := by omega
    have eb : p + k - (L + 2) + (δ + d) + (L + 2) =
        (p + k - 2 + δ) + (d + 2) := by omega
    rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
  rw [he]
  exact h1

private theorem step_mix1_congr {k s₁ s₂ p : Nat} (hk : 2 ≤ k)
    (hs1 : s₁ < 2 ^ k) (hs2 : s₂ < 2 ^ k) (hp : p < k)
    (H : ∀ δ ≤ 4, s₁.testBit ((p + k - 1 + δ) % k) = s₂.testBit ((p + k - 1 + δ) % k)) :
    (wordStep k (s₁ ^^^ rot k 1 s₁ ^^^ rot k (k - 1) s₁)).testBit p =
    (wordStep k (s₂ ^^^ rot k 1 s₂ ^^^ rot k (k - 1) s₂)).testBit p := by
  have hkpos : 0 < k := by omega
  have hlin (j : Nat) (hj : j ≤ 2) :
      (s₁ ^^^ rot k 1 s₁ ^^^ rot k (k - 1) s₁).testBit ((p + j) % k) =
      (s₂ ^^^ rot k 1 s₂ ^^^ rot k (k - 1) s₂).testBit ((p + j) % k) := by
    have hm := Nat.mod_lt (p + j) hkpos
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      rbit hm (by omega) hs1, rbit hm (by omega) hs1,
      rbit hm (by omega) hs2, rbit hm (by omega) hs2]
    have e0 : (p + j) % k = (p + k - 1 + (j + 1)) % k := by
      rw [show p + k - 1 + (j + 1) = (p + j) + k by omega, Nat.add_mod_right]
    have e1 : ((p + j) % k + k - 1) % k = (p + k - 1 + j) % k := by
      rw [show (p + j) % k + k - 1 = ((p + j) % k + k - 1) from rfl]
      apply Nat.ModEq.add_right_cancel' 1
      change ((p + j) % k + k - 1 + 1) % k = (p + k - 1 + j + 1) % k
      rw [show (p + j) % k + k - 1 + 1 = (p + j) % k + k by omega,
        show p + k - 1 + j + 1 = (p + j) + k by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.mod_mod]
    have e2 : ((p + j) % k + k - (k - 1)) % k = (p + k - 1 + (j + 2)) % k := by
      rw [show (p + j) % k + k - (k - 1) = (p + j) % k + 1 by omega, Nat.mod_add_mod,
        show p + k - 1 + (j + 2) = (p + j + 1) + k by omega, Nat.add_mod_right]
    rw [e1, e2, e0, H (j + 1) (by omega), H j (by omega), H (j + 2) (by omega)]
  rw [testBit_wordStep hp, testBit_wordStep hp]
  have hp0 : p = (p + 0) % k := (Nat.mod_eq_of_lt hp).symm
  conv_lhs => rw [hp0]
  conv_rhs => rw [hp0]
  rw [show ((p + 0) % k + 1) % k = (p + 1) % k by rw [Nat.mod_add_mod],
    show ((p + 0) % k + 2) % k = (p + 2) % k by rw [Nat.mod_add_mod]]
  rw [hlin 0 (by omega), hlin 1 (by omega), hlin 2 (by omega)]

private theorem step_mix2_congr {k s₁ s₂ p : Nat} (hk : 3 ≤ k)
    (hs1 : s₁ < 2 ^ k) (hs2 : s₂ < 2 ^ k) (hp : p < k)
    (H : ∀ δ ≤ 6, s₁.testBit ((p + k - 2 + δ) % k) = s₂.testBit ((p + k - 2 + δ) % k)) :
    (wordStep k (s₁ ^^^ rot k 2 s₁ ^^^ rot k (k - 2) s₁)).testBit p =
    (wordStep k (s₂ ^^^ rot k 2 s₂ ^^^ rot k (k - 2) s₂)).testBit p := by
  have hkpos : 0 < k := by omega
  have hlin (j : Nat) (hj : j ≤ 2) :
      (s₁ ^^^ rot k 2 s₁ ^^^ rot k (k - 2) s₁).testBit ((p + j) % k) =
      (s₂ ^^^ rot k 2 s₂ ^^^ rot k (k - 2) s₂).testBit ((p + j) % k) := by
    have hm := Nat.mod_lt (p + j) hkpos
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      rbit hm (by omega) hs1, rbit hm (by omega) hs1,
      rbit hm (by omega) hs2, rbit hm (by omega) hs2]
    have e0 : (p + j) % k = (p + k - 2 + (j + 2)) % k := by
      rw [show p + k - 2 + (j + 2) = (p + j) + k by omega, Nat.add_mod_right]
    have e1 : ((p + j) % k + k - 2) % k = (p + k - 2 + j) % k := by
      apply Nat.ModEq.add_right_cancel' 2
      change ((p + j) % k + k - 2 + 2) % k = (p + k - 2 + j + 2) % k
      rw [show (p + j) % k + k - 2 + 2 = (p + j) % k + k by omega,
        show p + k - 2 + j + 2 = (p + j) + k by omega,
        Nat.add_mod_right, Nat.add_mod_right, Nat.mod_mod]
    have e2 : ((p + j) % k + k - (k - 2)) % k = (p + k - 2 + (j + 4)) % k := by
      rw [show (p + j) % k + k - (k - 2) = (p + j) % k + 2 by omega, Nat.mod_add_mod,
        show p + k - 2 + (j + 4) = (p + j + 2) + k by omega, Nat.add_mod_right]
    rw [e1, e2, e0, H (j + 2) (by omega), H j (by omega), H (j + 4) (by omega)]
  rw [testBit_wordStep hp, testBit_wordStep hp]
  have hp0 : p = (p + 0) % k := (Nat.mod_eq_of_lt hp).symm
  conv_lhs => rw [hp0]
  conv_rhs => rw [hp0]
  rw [show ((p + 0) % k + 1) % k = (p + 1) % k by rw [Nat.mod_add_mod],
    show ((p + 0) % k + 2) % k = (p + 2) % k by rw [Nat.mod_add_mod]]
  rw [hlin 0 (by omega), hlin 1 (by omega), hlin 2 (by omega)]

private theorem rowWord_dep {k u w₁ w₂ : Nat} (hu : u < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k)
    (t : Nat) (ht : max (t + 1) (2 * t) < k) (p : Nat) (hp : p < k)
    (H : AgreeCyc k p (max (t + 1) (2 * t - 2)) (3 * t) w₁ w₂) :
    (rowWord k w₁ u t).testBit p = (rowWord k w₂ u t).testBit p := by
  induction t generalizing p with
  | zero =>
    simp only [rowWord, Nat.testBit_xor]
    rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
    have h0 := H 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [show max (0 + 1) (2 * 0 - 2) = 1 by decide] at h0
    rw [h0]
  | succ t IH =>
    simp only [rowWord, updateRound, Nat.testBit_xor]
    have hstep : (wordStep k (rowWord k w₁ u t ^^^ rot k 1 (rowWord k w₁ u t) ^^^ rot k (k - 1) (rowWord k w₁ u t))).testBit p =
        (wordStep k (rowWord k w₂ u t ^^^ rot k 1 (rowWord k w₂ u t) ^^^ rot k (k - 1) (rowWord k w₂ u t))).testBit p := by
      apply step_mix1_congr (by omega) (rowWord_lt hu t) (rowWord_lt hu t) hp
      intro δ hδ
      apply IH (by omega) _ (Nat.mod_lt _ (by omega))
      apply agreeCyc_shift1 (by omega) hδ
      exact agreeCyc_mono (by omega) (by omega) (by omega) H
    have hkey : (rot k (2 * t) w₁).testBit p = (rot k (2 * t) w₂).testBit p := by
      rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
      have hk1 := H (max (t + 1 + 1) (2 * (t + 1) - 2) - 2 * t) (by omega)
      have he : p + k - max (t + 1 + 1) (2 * (t + 1) - 2) + (max (t + 1 + 1) (2 * (t + 1) - 2) - 2 * t) =
          p + k - 2 * t := by omega
      rw [he] at hk1
      exact hk1
    rw [hstep, hkey]

private theorem colWord_dep {k r v w₁ w₂ : Nat} (hv : v < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k)
    (t : Nat) (ht : max (2 * t + 3) (3 * t + 4) < k) (p : Nat) (hp : p < k)
    (H : AgreeCyc k p (max (2 * t + 3) (3 * t + 1)) (4 * t - 3) w₁ w₂) :
    (colWord k r w₁ v t).testBit p = (colWord k r w₂ v t).testBit p := by
  induction t generalizing p with
  | zero =>
    simp only [colWord, Nat.testBit_xor]
    rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
    have h0 := H 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [show max (2 * 0 + 3) (3 * 0 + 1) = 3 by decide] at h0
    rw [h0]
  | succ t IH =>
    simp only [colWord, updateRound, Nat.testBit_xor]
    have hstep : (wordStep k (colWord k r w₁ v t ^^^ rot k 2 (colWord k r w₁ v t) ^^^ rot k (k - 2) (colWord k r w₁ v t))).testBit p =
        (wordStep k (colWord k r w₂ v t ^^^ rot k 2 (colWord k r w₂ v t) ^^^ rot k (k - 2) (colWord k r w₂ v t))).testBit p := by
      apply step_mix2_congr (by omega) (colWord_lt hv t) (colWord_lt hv t) hp
      intro δ hδ
      cases t with
      | zero =>
        simp only [colWord, Nat.testBit_xor]
        have hq : (p + k - 2 + δ) % k < k := Nat.mod_lt _ (by omega)
        rw [rbit hq (by omega) hw1, rbit hq (by omega) hw2]
        have h1 := H δ (by omega)
        have he : ((p + k - 2 + δ) % k + k - 3) % k =
            (p + k - max (2 * (0 + 1) + 3) (3 * (0 + 1) + 1) + δ) % k := by
          rw [show max (2 * (0 + 1) + 3) (3 * (0 + 1) + 1) = 5 by decide]
          apply Nat.ModEq.add_right_cancel' 5
          change (((p + k - 2 + δ) % k + k - 3) + 5) % k = ((p + k - 5 + δ) + 5) % k
          have ea : (p + k - 2 + δ) % k + k - 3 + 5 = (p + k - 2 + δ) % k + 2 + k := by omega
          have eb : p + k - 5 + δ + 5 = (p + k - 2 + δ) + 2 := by omega
          rw [ea, eb, Nat.add_mod_right, Nat.mod_add_mod]
        rw [he, h1]
      | succ t' =>
        apply IH (by omega) _ (Nat.mod_lt _ (by omega))
        apply agreeCyc_shift2 (by omega) hδ
        exact agreeCyc_mono (by omega) (by omega) (by omega) H
    have hkey : (rot k (3 * (t + 1) + 1) w₁).testBit p = (rot k (3 * (t + 1) + 1) w₂).testBit p := by
      rw [rbit hp (by omega) hw1, rbit hp (by omega) hw2]
      have hk1 := H (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) - (3 * (t + 1) + 1)) (by omega)
      have he : p + k - max (2 * (t + 1) + 3) (3 * (t + 1) + 1) +
          (max (2 * (t + 1) + 3) (3 * (t + 1) + 1) - (3 * (t + 1) + 1)) =
          p + k - (3 * (t + 1) + 1) := by omega
      rw [he] at hk1
      exact hk1
    rw [hstep, hkey]

private def rowCoreBit (k r w u i : Nat) : Bool :=
  let S := rowWord k w u (r - 1)
  (wordStep k (S ^^^ rot k 1 S ^^^ rot k (k - 1) S) ^^^ constant k r).testBit i

private def colCoreBit (k r w v i : Nat) : Bool :=
  let S := colWord k r w v (r - 1)
  (wordStep k (S ^^^ rot k 2 S ^^^ rot k (k - 2) S) ^^^ constant k (r + r)).testBit i

private theorem rowWord_final_xor {k r w u i : Nat} (hr : 4 ≤ r) (hk : 2 * r < k)
    (hw : w < 2 ^ k) (hi : i < k) :
    (rowWord k w u r).testBit i = xor (rowCoreBit k r w u i) (w.testBit ((i + k - (2 * r - 2)) % k)) := by
  have he : r - 1 + 1 = r := by omega
  conv_lhs => rw [← he]; unfold rowWord updateRound
  simp only [rowCoreBit, Nat.testBit_xor, he]
  rw [show 2 * (r - 1) = 2 * r - 2 by omega, rbit hi (by omega) hw]
  cases (wordStep k (rowWord k w u (r - 1) ^^^ rot k 1 (rowWord k w u (r - 1)) ^^^
    rot k (k - 1) (rowWord k w u (r - 1)))).testBit i <;>
    cases w.testBit ((i + k - (2 * r - 2)) % k) <;>
    cases (constant k r).testBit i <;> rfl

private theorem colWord_final_xor {k r w v i : Nat} (hr : 4 ≤ r) (hk : 3 * r + 2 < k)
    (hw : w < 2 ^ k) (hi : i < k) :
    (colWord k r w v r).testBit i = xor (colCoreBit k r w v i) (w.testBit ((i + k - (3 * r + 1)) % k)) := by
  have he : r - 1 + 1 = r := by omega
  conv_lhs => rw [← he]; unfold colWord updateRound
  simp only [colCoreBit, Nat.testBit_xor, he]
  rw [show 3 * r + 1 = 3 * r + 1 from rfl, rbit hi (by omega) hw]
  cases (wordStep k (colWord k r w v (r - 1) ^^^ rot k 2 (colWord k r w v (r - 1)) ^^^
    rot k (k - 2) (colWord k r w v (r - 1)))).testBit i <;>
    cases w.testBit ((i + k - (3 * r + 1)) % k) <;>
    cases (constant k (r + r)).testBit i <;> rfl

private theorem rowCoreBit_dep {k r u w₁ w₂ i : Nat} (hr : 4 ≤ r) (hk : 7 * r ≤ k)
    (hu : u < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k) (hi : i < k)
    (H : AgreeCyc k i (2 * r - 3) (3 * r) w₁ w₂) :
    rowCoreBit k r w₁ u i = rowCoreBit k r w₂ u i := by
  simp only [rowCoreBit, Nat.testBit_xor]
  congr 1
  apply step_mix1_congr (by omega) (rowWord_lt hu (r - 1)) (rowWord_lt hu (r - 1)) hi
  intro δ hδ
  apply rowWord_dep hu hw1 hw2 (r - 1) (by omega) _ (Nat.mod_lt _ (by omega))
  apply agreeCyc_shift1 (by omega) hδ
  exact agreeCyc_mono (by omega) (by omega) (by omega) H

private theorem colCoreBit_dep {k r v w₁ w₂ i : Nat} (hr : 4 ≤ r) (hk : 7 * r ≤ k)
    (hv : v < 2 ^ k) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k) (hi : i < k)
    (H : AgreeCyc k i (3 * r) (4 * r - 3) w₁ w₂) :
    colCoreBit k r w₁ v i = colCoreBit k r w₂ v i := by
  simp only [colCoreBit, Nat.testBit_xor]
  congr 1
  apply step_mix2_congr (by omega) (colWord_lt hv (r - 1)) (colWord_lt hv (r - 1)) hi
  intro δ hδ
  apply colWord_dep hv hw1 hw2 (r - 1) (by omega) _ (Nat.mod_lt _ (by omega))
  apply agreeCyc_shift2 (by omega) hδ
  exact agreeCyc_mono (by omega) (by omega) (by omega) H

private def setBit (k w p : Nat) (b : Bool) : Nat :=
  tableIndex (fun i : Fin k => if i.val = p then b else w.testBit i.val)

private theorem setBit_lt {k w p : Nat} {b : Bool} : setBit k w p b < 2 ^ k := pack_lt _

private theorem testBit_setBit {k w p i : Nat} {b : Bool} (hi : i < k) :
    (setBit k w p b).testBit i = if i = p then b else w.testBit i :=
  bit_pack (fun j : Fin k => if j.val = p then b else w.testBit j.val) ⟨i, hi⟩

private def sweepRow (k r u : Nat) : Nat → Nat → Nat
  | 0, w => w
  | t + 1, w =>
    let h := (k + 1) / 2
    let p := k - h - (2 * r - 2) + t
    let i := k - h + t
    sweepRow k r u t (setBit k w p (rowCoreBit k r w u i))

private def sweepCol (k r v : Nat) : Nat → Nat → Nat
  | 0, w => w
  | j + 1, w =>
    let h := (k + 1) / 2
    let p := k - h - (3 * r + 1) + j
    let i := k - h + j
    sweepCol k r v j (setBit k w p (colCoreBit k r w v i))

private theorem sweepRow_lt {k r u n w : Nat} (hw : w < 2 ^ k) :
    sweepRow k r u n w < 2 ^ k := by
  induction n generalizing w with
  | zero => exact hw
  | succ n IH => exact IH setBit_lt

private theorem sweepCol_lt {k r v n w : Nat} (hw : w < 2 ^ k) :
    sweepCol k r v n w < 2 ^ k := by
  induction n generalizing w with
  | zero => exact hw
  | succ n IH => exact IH setBit_lt

private theorem sweepRow_unchanged {k r u n w m : Nat} (hm : m < k)
    (hout : m < k - (k + 1) / 2 - (2 * r - 2) ∨ k - (k + 1) / 2 - (2 * r - 2) + n ≤ m) :
    (sweepRow k r u n w).testBit m = w.testBit m := by
  induction n generalizing w with
  | zero => rfl
  | succ n IH =>
    simp only [sweepRow]
    rw [IH (by omega), testBit_setBit hm, if_neg (by omega)]

private theorem sweepCol_unchanged {k r v n w m : Nat} (hm : m < k)
    (hout : m < k - (k + 1) / 2 - (3 * r + 1) ∨ k - (k + 1) / 2 - (3 * r + 1) + n ≤ m) :
    (sweepCol k r v n w).testBit m = w.testBit m := by
  induction n generalizing w with
  | zero => rfl
  | succ n IH =>
    simp only [sweepCol]
    rw [IH (by omega), testBit_setBit hm, if_neg (by omega)]

private theorem agree_above_row {k r p w₁ w₂ : Nat} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hp1 : k - (k + 1) / 2 - (2 * r - 2) ≤ p) (hp2 : p < k - (2 * r - 2))
    (H : ∀ m < k, (m < 4 * r - 3 ∨ p < m) → w₁.testBit m = w₂.testBit m) :
    AgreeCyc k (p + (2 * r - 2)) (2 * r - 3) (3 * r) w₁ w₂ := by
  intro d hd
  have hm : (p + (2 * r - 2) + k - (2 * r - 3) + d) % k < k := Nat.mod_lt _ (by omega)
  apply H _ hm
  have e : p + (2 * r - 2) + k - (2 * r - 3) + d = k + (p + 1 + d) := by omega
  rw [e]
  by_cases hlt : p + 1 + d < k
  · right
    rw [Nat.add_comm k, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    omega
  · left
    have hlt2 : p + 1 + d - k < k := by omega
    rw [show k + (p + 1 + d) = (p + 1 + d - k) + 2 * k by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
    omega

private theorem agree_above_col {k r p w₁ w₂ : Nat} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hp1 : k - (k + 1) / 2 - (3 * r + 1) ≤ p) (hp2 : p < k - (3 * r + 1))
    (H : ∀ m < k, (m < 4 * r - 3 ∨ p < m) → w₁.testBit m = w₂.testBit m) :
    AgreeCyc k (p + (3 * r + 1)) (3 * r) (4 * r - 3) w₁ w₂ := by
  intro d hd
  have hm : (p + (3 * r + 1) + k - 3 * r + d) % k < k := Nat.mod_lt _ (by omega)
  apply H _ hm
  have e : p + (3 * r + 1) + k - 3 * r + d = k + (p + 1 + d) := by omega
  rw [e]
  by_cases hlt : p + 1 + d < k
  · right
    rw [Nat.add_comm k, Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
    omega
  · left
    have hlt2 : p + 1 + d - k < k := by omega
    rw [show k + (p + 1 + d) = (p + 1 + d - k) + 2 * k by omega,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt2]
    omega

private theorem sweepRow_spec {k r u n w t : Nat} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hn : n ≤ (k + 1) / 2) (ht : t < n) :
    (rowWord k (sweepRow k r u n w) u r).testBit (k - (k + 1) / 2 + t) = false := by
  induction n generalizing w with
  | zero => omega
  | succ n IH =>
    simp only [sweepRow]
    by_cases h : t < n
    · exact IH setBit_lt (by omega) h
    · obtain rfl : t = n := by omega
      let h := (k + 1) / 2
      let p := k - h - (2 * r - 2) + t
      let i := k - h + t
      let w' := setBit k w p (rowCoreBit k r w u i)
      let wf := sweepRow k r u t w'
      have hwf : wf < 2 ^ k := sweepRow_lt setBit_lt
      have hi : i < k := by dsimp [i, h]; omega
      change (rowWord k wf u r).testBit i = false
      rw [rowWord_final_xor hr (by omega) hwf hi]
      have hidx : (i + k - (2 * r - 2)) % k = p := by
        rw [show i + k - (2 * r - 2) = p + k by dsimp [i, p, h]; omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [p, h]; omega)]
      rw [hidx]
      have hbit : wf.testBit p = rowCoreBit k r w u i := by
        dsimp [wf]
        rw [sweepRow_unchanged (by dsimp [p, h]; omega) (Or.inr (by dsimp [p, h]; omega))]
        dsimp [w']
        rw [testBit_setBit (by dsimp [p, h]; omega), if_pos rfl]
      have hcore : rowCoreBit k r wf u i = rowCoreBit k r w u i := by
        apply rowCoreBit_dep hr (by omega) hu hwf hw hi
        have ei : i = p + (2 * r - 2) := by dsimp [i, p, h]; omega
        rw [ei]
        apply agree_above_row hr hk (by dsimp [p, h]; omega) (by dsimp [p, h]; omega)
        intro m hm hm'
        dsimp [wf]
        rw [sweepRow_unchanged hm (by dsimp [p, h] at hm' ⊢; omega)]
        dsimp [w']
        rw [testBit_setBit hm, if_neg (by dsimp [p, h] at hm' ⊢; omega)]
      rw [hbit, hcore, Bool.xor_self]

private theorem sweepCol_spec {k r v n w j : Nat} (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (hv : v < 2 ^ k) (hw : w < 2 ^ k) (hn : n ≤ r + 3) (hj : j < n) :
    (colWord k r (sweepCol k r v n w) v r).testBit (k - (k + 1) / 2 + j) = false := by
  induction n generalizing w with
  | zero => omega
  | succ n IH =>
    simp only [sweepCol]
    by_cases h : j < n
    · exact IH setBit_lt (by omega) h
    · obtain rfl : j = n := by omega
      let h := (k + 1) / 2
      let p := k - h - (3 * r + 1) + j
      let i := k - h + j
      let w' := setBit k w p (colCoreBit k r w v i)
      let wf := sweepCol k r v j w'
      have hwf : wf < 2 ^ k := sweepCol_lt setBit_lt
      have hi : i < k := by dsimp [i, h]; omega
      change (colWord k r wf v r).testBit i = false
      rw [colWord_final_xor hr (by omega) hwf hi]
      have hidx : (i + k - (3 * r + 1)) % k = p := by
        rw [show i + k - (3 * r + 1) = p + k by dsimp [i, p, h]; omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp [p, h]; omega)]
      rw [hidx]
      have hbit : wf.testBit p = colCoreBit k r w v i := by
        dsimp [wf]
        rw [sweepCol_unchanged (by dsimp [p, h]; omega) (Or.inr (by dsimp [p, h]; omega))]
        dsimp [w']
        rw [testBit_setBit (by dsimp [p, h]; omega), if_pos rfl]
      have hcore : colCoreBit k r wf v i = colCoreBit k r w v i := by
        apply colCoreBit_dep hr (by omega) hv hwf hw hi
        have ei : i = p + (3 * r + 1) := by dsimp [i, p, h]; omega
        rw [ei]
        apply agree_above_col hr hk (by dsimp [p, h]; omega) (by dsimp [p, h]; omega)
        intro m hm hm'
        dsimp [wf]
        rw [sweepCol_unchanged hm (by dsimp [p, h] at hm' ⊢; omega)]
        dsimp [w']
        rw [testBit_setBit hm, if_neg (by dsimp [p, h] at hm' ⊢; omega)]
      rw [hbit, hcore, Bool.xor_self]

private def initWord (k r : Nat) (label : Fin (6 * r - 5) → Bool) : Nat :=
  tableIndex (fun i : Fin k =>
    if h1 : k - (2 * r - 2) ≤ i.val then
      label ⟨i.val - (k - (2 * r - 2)), by omega⟩
    else if h2 : i.val < 4 * r - 3 then
      label ⟨2 * r - 2 + i.val, by omega⟩
    else false)

private def decodeVal (k r u v : Nat) (label : Fin (6 * r - 5) → Bool) : Nat :=
  let h := (k + 1) / 2
  let w0 := initWord k r label
  let w1 := sweepRow k r u h w0
  sweepCol k r v (r + 3) w1

private theorem decodeVal_lt (k r u v : Nat) (label : Fin (6 * r - 5) → Bool) :
    decodeVal k r u v label < 2 ^ k :=
  sweepCol_lt (sweepRow_lt (pack_lt _))

private def decodeFin (k r u v : Nat) (label : Fin (6 * r - 5) → Bool) : Fin (2 ^ k) :=
  ⟨decodeVal k r u v label, decodeVal_lt k r u v label⟩

private theorem xor_eq_false_inj {c a b : Bool} (h1 : xor c a = false) (h2 : xor c b = false) :
    a = b := by
  cases c <;> cases a <;> cases b <;> simp_all

private theorem solve (k r : Nat) (hr : 4 ≤ r) (hk : (k + 1) / 2 + (7 * r - 2) ≤ k)
    (u v : Fin (2 ^ k)) :
    let h := (k + 1) / 2
    let s := 6 * r - 5
    let seedOf := fun (w : Fin (2 ^ k)) (j : Fin s) =>
      w.val.testBit ((k - (2 * r - 2) + j.val) % k)
    let canonical := fun (w : Fin (2 ^ k)) =>
      ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) →
        w.val.testBit i.val = false
    let selected := fun (w : Fin (2 ^ k)) =>
      rowWord k w.val u.val r < 2 ^ (k - h) ∧
        ∀ j : Fin (r + 3), (colWord k r w.val v.val r).testBit (k - h + j.val) = false
    let joint := fun (w : Fin (2 ^ k)) =>
      rowWord k w.val u.val r < 2 ^ (k - h) ∧ colWord k r w.val v.val r < 2 ^ (k - h)
    ∃ decode : (Fin s → Bool) → Fin (2 ^ k),
      (∀ (label : Fin s → Bool) (key : Fin (2 ^ k)),
        key = decode label ↔ seedOf key = label ∧ canonical key ∧ selected key) ∧
      ((∃ raw, joint raw) ↔ ∃ label, joint (decode label)) := by
  let h := (k + 1) / 2
  let s := 6 * r - 5
  let decode := decodeFin k r u.val v.val
  have hrow_preserve (w₁ w₂ : Nat) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k)
      (H : ∀ m < k, (m < 4 * r - 3 ∨ k - h - (2 * r - 2) ≤ m) → w₁.testBit m = w₂.testBit m)
      (i : Nat) (hi1 : k - h ≤ i) (hi2 : i < k) :
      (rowWord k w₁ u.val r).testBit i = (rowWord k w₂ u.val r).testBit i := by
    rw [rowWord_final_xor hr (by omega) hw1 hi2, rowWord_final_xor hr (by omega) hw2 hi2]
    have hbit : w₁.testBit ((i + k - (2 * r - 2)) % k) = w₂.testBit ((i + k - (2 * r - 2)) % k) := by
      have hm : (i + k - (2 * r - 2)) % k = i - (2 * r - 2) := by
        rw [show i + k - (2 * r - 2) = (i - (2 * r - 2)) + k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      exact H _ (by omega) (Or.inr (by omega))
    have hcore : rowCoreBit k r w₁ u.val i = rowCoreBit k r w₂ u.val i := by
      apply rowCoreBit_dep hr (by omega) u.isLt hw1 hw2 hi2
      have ei : i = (i - (2 * r - 2)) + (2 * r - 2) := by omega
      rw [ei]
      apply agree_above_row hr hk (by omega) (by omega)
      intro m hm hm'
      exact H m hm (by omega)
    rw [hcore, hbit]
  have hcol_preserve (w₁ w₂ : Nat) (hw1 : w₁ < 2 ^ k) (hw2 : w₂ < 2 ^ k)
      (H : ∀ m < k, (m < 4 * r - 3 ∨ k - h - (3 * r + 1) ≤ m) → w₁.testBit m = w₂.testBit m)
      (i : Nat) (hi1 : k - h ≤ i) (hi2 : i < k) :
      (colWord k r w₁ v.val r).testBit i = (colWord k r w₂ v.val r).testBit i := by
    rw [colWord_final_xor hr (by omega) hw1 hi2, colWord_final_xor hr (by omega) hw2 hi2]
    have hbit : w₁.testBit ((i + k - (3 * r + 1)) % k) = w₂.testBit ((i + k - (3 * r + 1)) % k) := by
      have hm : (i + k - (3 * r + 1)) % k = i - (3 * r + 1) := by
        rw [show i + k - (3 * r + 1) = (i - (3 * r + 1)) + k by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hm]
      exact H _ (by omega) (Or.inr (by omega))
    have hcore : colCoreBit k r w₁ v.val i = colCoreBit k r w₂ v.val i := by
      apply colCoreBit_dep hr (by omega) v.isLt hw1 hw2 hi2
      have ei : i = (i - (3 * r + 1)) + (3 * r + 1) := by omega
      rw [ei]
      apply agree_above_col hr hk (by omega) (by omega)
      intro m hm hm'
      exact H m hm (by omega)
    rw [hcore, hbit]
  have hdec_props (label : Fin s → Bool) :
      (fun j : Fin s => (decode label).val.testBit ((k - (2 * r - 2) + j.val) % k)) = label ∧
      (∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) →
        (decode label).val.testBit i.val = false) ∧
      (rowWord k (decode label).val u.val r < 2 ^ (k - h) ∧
        ∀ j : Fin (r + 3), (colWord k r (decode label).val v.val r).testBit (k - h + j.val) = false) := by
    let w0 := initWord k r label
    let w1 := sweepRow k r u.val h w0
    let w2 := sweepCol k r v.val (r + 3) w1
    have hw0 : w0 < 2 ^ k := pack_lt _
    have hw1 : w1 < 2 ^ k := sweepRow_lt hw0
    have hw2 : w2 < 2 ^ k := sweepCol_lt hw1
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext j
      change w2.testBit ((k - (2 * r - 2) + j.val) % k) = label j
      by_cases hj : j.val < 2 * r - 2
      · have hidx : (k - (2 * r - 2) + j.val) % k = k - (2 * r - 2) + j.val :=
          Nat.mod_eq_of_lt (by omega)
        rw [hidx]
        rw [sweepCol_unchanged (by omega) (Or.inr (by omega)),
          sweepRow_unchanged (by omega) (Or.inr (by omega))]
        dsimp [w0, initWord]
        rw [bit_pack _ ⟨k - (2 * r - 2) + j.val, by omega⟩]
        simp only [show k - (2 * r - 2) ≤ k - (2 * r - 2) + j.val by omega, ↓reduceDIte]
        congr 1; apply Fin.ext; dsimp; omega
      · have hidx : (k - (2 * r - 2) + j.val) % k = j.val - (2 * r - 2) := by
          rw [show k - (2 * r - 2) + j.val = (j.val - (2 * r - 2)) + k by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hidx]
        rw [sweepCol_unchanged (by omega) (Or.inl (by omega)),
          sweepRow_unchanged (by omega) (Or.inl (by omega))]
        dsimp [w0, initWord]
        rw [bit_pack _ ⟨j.val - (2 * r - 2), by omega⟩]
        simp only [show ¬ k - (2 * r - 2) ≤ j.val - (2 * r - 2) by omega, ↓reduceDIte,
          show j.val - (2 * r - 2) < 4 * r - 3 by omega]
        congr 1; apply Fin.ext; dsimp; omega
    · intro i hi1 hi2
      change w2.testBit i.val = false
      rw [sweepCol_unchanged i.isLt (Or.inl (by omega)),
        sweepRow_unchanged i.isLt (Or.inl (by omega))]
      dsimp [w0, initWord]
      rw [bit_pack _ i]
      simp only [show ¬ k - (2 * r - 2) ≤ i.val by omega, ↓reduceDIte,
        show ¬ i.val < 4 * r - 3 by omega]
    · rw [lt_two_pow_iff_testBit (rowWord_lt u.isLt r)]
      intro i hi1 hi2
      have heq := hrow_preserve w2 w1 hw2 hw1
        (fun m hm hm' => sweepCol_unchanged hm (by omega)) i hi1 hi2
      change (rowWord k w2 u.val r).testBit i = false
      rw [heq]
      have hsp := sweepRow_spec hr hk u.isLt hw0 (le_refl h) (t := i - (k - h)) (by omega)
      have ei : k - h + (i - (k - h)) = i := by omega
      simpa [w1, h, ei] using hsp
    · intro j
      exact sweepCol_spec hr hk v.isLt hw1 (le_refl (r + 3)) j.isLt
  have huniq (label : Fin s → Bool) (key : Fin (2 ^ k))
      (hseed : (fun j : Fin s => key.val.testBit ((k - (2 * r - 2) + j.val) % k)) = label)
      (hcan : ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) → key.val.testBit i.val = false)
      (hsel : rowWord k key.val u.val r < 2 ^ (k - h) ∧
        ∀ j : Fin (r + 3), (colWord k r key.val v.val r).testBit (k - h + j.val) = false) :
      key = decode label := by
    obtain ⟨dseed, dcan, dsel⟩ := hdec_props label
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro m
    by_cases hmk : m < k
    · have hlow (m' : Nat) (hm' : m' < 4 * r - 3) :
          key.val.testBit m' = (decode label).val.testBit m' := by
        let j : Fin s := ⟨2 * r - 2 + m', by dsimp [s]; omega⟩
        have e : (k - (2 * r - 2) + j.val) % k = m' := by
          dsimp [j]
          rw [show k - (2 * r - 2) + (2 * r - 2 + m') = m' + k by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have h1 := congrFun hseed j
        have h2 := congrFun dseed j
        simpa [e] using h1.trans h2.symm
      have hhigh (m' : Nat) (hm1 : k - (2 * r - 2) ≤ m') (hm2 : m' < k) :
          key.val.testBit m' = (decode label).val.testBit m' := by
        let j : Fin s := ⟨m' - (k - (2 * r - 2)), by dsimp [s]; omega⟩
        have e : (k - (2 * r - 2) + j.val) % k = m' := by
          dsimp [j]
          rw [show k - (2 * r - 2) + (m' - (k - (2 * r - 2))) = m' by omega,
            Nat.mod_eq_of_lt hm2]
        have h1 := congrFun hseed j
        have h2 := congrFun dseed j
        simpa [e] using h1.trans h2.symm
      let P := fun d : Nat => ∀ m' < k, k - m' = d → key.val.testBit m' = (decode label).val.testBit m'
      have hall (d : Nat) : P d := by
        induction d using Nat.strong_induction_on with
        | ind d IH =>
          intro m' hm' hmd
          by_cases h1 : k - (2 * r - 2) ≤ m'
          · exact hhigh m' h1 hm'
          · by_cases h2 : k - h - (2 * r - 2) ≤ m'
            · let i := m' + (2 * r - 2)
              have hi1 : k - h ≤ i := by dsimp [i]; omega
              have hi2 : i < k := by dsimp [i]; omega
              have hk0 : (rowWord k key.val u.val r).testBit i = false :=
                (lt_two_pow_iff_testBit (rowWord_lt u.isLt r)).mp hsel.1 i hi1 hi2
              have hd0 : (rowWord k (decode label).val u.val r).testBit i = false :=
                (lt_two_pow_iff_testBit (rowWord_lt u.isLt r)).mp dsel.1 i hi1 hi2
              rw [rowWord_final_xor hr (by omega) key.isLt hi2] at hk0
              rw [rowWord_final_xor hr (by omega) (decode label).isLt hi2] at hd0
              have hidx : (i + k - (2 * r - 2)) % k = m' := by
                rw [show i + k - (2 * r - 2) = m' + k by dsimp [i]; omega,
                  Nat.add_mod_right, Nat.mod_eq_of_lt hm']
              rw [hidx] at hk0 hd0
              have hcore : rowCoreBit k r key.val u.val i = rowCoreBit k r (decode label).val u.val i := by
                apply rowCoreBit_dep hr (by omega) u.isLt key.isLt (decode label).isLt hi2
                apply agree_above_row hr hk (by omega) (by omega)
                intro q hq hq'
                rcases hq' with hql | hqr
                · exact hlow q hql
                · exact IH (k - q) (by omega) q hq rfl
              rw [hcore] at hk0
              exact xor_eq_false_inj hk0 hd0
            · by_cases h3 : k - h - (3 * r + 1) ≤ m'
              · let i := m' + (3 * r + 1)
                have hi2 : i < k := by dsimp [i]; omega
                let j : Fin (r + 3) := ⟨i - (k - h), by dsimp [i]; omega⟩
                have ei : k - h + j.val = i := by dsimp [j, i]; omega
                have hk0 : (colWord k r key.val v.val r).testBit i = false := by
                  simpa [ei] using hsel.2 j
                have hd0 : (colWord k r (decode label).val v.val r).testBit i = false := by
                  simpa [ei] using dsel.2 j
                rw [colWord_final_xor hr (by omega) key.isLt hi2] at hk0
                rw [colWord_final_xor hr (by omega) (decode label).isLt hi2] at hd0
                have hidx : (i + k - (3 * r + 1)) % k = m' := by
                  rw [show i + k - (3 * r + 1) = m' + k by dsimp [i]; omega,
                    Nat.add_mod_right, Nat.mod_eq_of_lt hm']
                rw [hidx] at hk0 hd0
                have hcore : colCoreBit k r key.val v.val i = colCoreBit k r (decode label).val v.val i := by
                  apply colCoreBit_dep hr (by omega) v.isLt key.isLt (decode label).isLt hi2
                  apply agree_above_col hr hk (by omega) (by omega)
                  intro q hq hq'
                  rcases hq' with hql | hqr
                  · exact hlow q hql
                  · exact IH (k - q) (by omega) q hq rfl
                rw [hcore] at hk0
                exact xor_eq_false_inj hk0 hd0
              · by_cases h4 : 4 * r - 3 ≤ m'
                · rw [hcan ⟨m', hm'⟩ (by dsimp; omega) (by dsimp; omega),
                    dcan ⟨m', hm'⟩ (by dsimp; omega) (by dsimp; omega)]
                · exact hlow m' (by omega)
      exact hall (k - m) m hmk rfl
    · have hp := Nat.pow_le_pow_right Nat.zero_lt_two (by omega : k ≤ m)
      rw [Nat.testBit_lt_two_pow (key.isLt.trans_le hp),
        Nat.testBit_lt_two_pow ((decode label).isLt.trans_le hp)]
  refine ⟨decode, ?_, ?_⟩
  · intro label key
    constructor
    · rintro rfl
      exact hdec_props label
    · rintro ⟨hseed, hcan, hsel⟩
      exact huniq label key hseed hcan hsel
  · constructor
    · rintro ⟨raw, hraw1, hraw2⟩
      let wnormVal : Nat := tableIndex (fun i : Fin k =>
        if 4 * r - 3 ≤ i.val ∧ i.val < k - h - (3 * r + 1) then false else raw.val.testBit i.val)
      let wnorm : Fin (2 ^ k) := ⟨wnormVal, pack_lt _⟩
      have hagree (m : Nat) (hm : m < k) (hout : m < 4 * r - 3 ∨ k - h - (3 * r + 1) ≤ m) :
          wnorm.val.testBit m = raw.val.testBit m := by
        change (tableIndex _).testBit m = raw.val.testBit m
        rw [bit_pack _ ⟨m, hm⟩]
        simp only [show ¬ (4 * r - 3 ≤ m ∧ m < k - h - (3 * r + 1)) by omega, ↓reduceIte]
      have hwn1 : rowWord k wnorm.val u.val r < 2 ^ (k - h) := by
        rw [lt_two_pow_iff_testBit (rowWord_lt u.isLt r)]
        intro i hi1 hi2
        rw [hrow_preserve wnorm.val raw.val wnorm.isLt raw.isLt (fun m hm hm' => hagree m hm (by omega)) i hi1 hi2]
        exact (lt_two_pow_iff_testBit (rowWord_lt u.isLt r)).mp hraw1 i hi1 hi2
      have hwn2 : colWord k r wnorm.val v.val r < 2 ^ (k - h) := by
        rw [lt_two_pow_iff_testBit (colWord_lt v.isLt r)]
        intro i hi1 hi2
        rw [hcol_preserve wnorm.val raw.val wnorm.isLt raw.isLt hagree i hi1 hi2]
        exact (lt_two_pow_iff_testBit (colWord_lt v.isLt r)).mp hraw2 i hi1 hi2
      have hcan : ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) → wnorm.val.testBit i.val = false := by
        intro i hi1 hi2
        change (tableIndex _).testBit i.val = false
        rw [bit_pack _ i]
        simp [hi1, hi2]
      have hsel : rowWord k wnorm.val u.val r < 2 ^ (k - h) ∧
          ∀ j : Fin (r + 3), (colWord k r wnorm.val v.val r).testBit (k - h + j.val) = false := by
        refine ⟨hwn1, fun j => ?_⟩
        exact (lt_two_pow_iff_testBit (colWord_lt v.isLt r)).mp hwn2 (k - h + j.val) (by omega) (by omega)
      let label : Fin s → Bool := fun j => wnorm.val.testBit ((k - (2 * r - 2) + j.val) % k)
      have heq : wnorm = decode label := huniq label wnorm rfl hcan hsel
      exact ⟨label, heq ▸ hwn1, heq ▸ hwn2⟩
    · rintro ⟨label, hj⟩
      exact ⟨decode label, hj⟩

end Joint25506

end PEqualNP.Outside.L_meta_25506_aux

open PEqualNP.Outside.L_meta_25506_aux.BitBridge PEqualNP.Outside.L_meta_25506_aux.Joint25506

theorem PEqualNP.Outside.L_meta_25506 : ∀ (k r : Nat), 4 ≤ r → (k + 1) / 2 + (7 * r - 2) ≤ k →
  ∀ u v : Fin (2 ^ k),
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
  let h := (k + 1) / 2
  let s := 6 * r - 5
  let seedOf := fun (w : Fin (2 ^ k)) (j : Fin s) =>
    w.val.testBit ((k - (2 * r - 2) + j.val) % k)
  let canonical := fun (w : Fin (2 ^ k)) =>
    ∀ i : Fin k, 4 * r - 3 ≤ i.val → i.val < k - h - (3 * r + 1) →
      w.val.testBit i.val = false
  let selected := fun (w : Fin (2 ^ k)) =>
    first w.val u.val < 2 ^ (k - h) ∧
      ∀ j : Fin (r + 3), (second w.val v.val).testBit (k - h + j.val) = false
  let joint := fun (w : Fin (2 ^ k)) =>
    first w.val u.val < 2 ^ (k - h) ∧ second w.val v.val < 2 ^ (k - h)
  ∃ decode : (Fin s → Bool) → Fin (2 ^ k),
    (∀ (label : Fin s → Bool) (key : Fin (2 ^ k)),
      key = decode label ↔ seedOf key = label ∧ canonical key ∧ selected key) ∧
    ((∃ raw, joint raw) ↔ ∃ label, joint (decode label)) := by
  intro k r hr hk u v
  have rowEq (w : Nat) :
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) w ^^^ constant k (t + 1)) (rot k 1 w ^^^ u.val) = rowWord k w u.val r := by
    simp only [← wordStep_eq]
    exact round_fold (rowWord k w u.val) (fun s t => updateRound k 1 (2 * t) (t + 1) w s) (by intros; rfl) r
  have colEq (w : Nat) :
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) w ^^^ constant k (r + (t + 1))) (rot k 3 w ^^^ v.val) = colWord k r w v.val r := by
    simp only [← wordStep_eq]
    exact round_fold (colWord k r w v.val)
      (fun s t => updateRound k 2 (3 * (t + 1) + 1) (r + (t + 1)) w s) (by intros; rfl) r
  dsimp only
  have hS := solve k r hr hk u v
  dsimp only at hS
  obtain ⟨decode, h1, h2⟩ := hS
  refine ⟨decode, fun label key => ?_, ?_⟩
  · have h1' := h1 label key
    have hrk : (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) key.val ^^^ constant k (t + 1)) (rot k 1 key.val ^^^ u.val) = rowWord k key.val u.val r := rowEq key.val
    have hck : (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) key.val ^^^ constant k (r + (t + 1))) (rot k 3 key.val ^^^ v.val) = colWord k r key.val v.val r := colEq key.val
    change key = decode label ↔ _ ∧ _ ∧
      ((List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) key.val ^^^ constant k (t + 1)) (rot k 1 key.val ^^^ u.val) < 2 ^ (k - (k + 1) / 2) ∧
        ∀ j : Fin (r + 3), ((List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) key.val ^^^ constant k (r + (t + 1))) (rot k 3 key.val ^^^ v.val)).testBit (k - (k + 1) / 2 + j.val) = false)
    rw [hrk, hck]
    exact h1'
  · change (∃ raw : Fin (2 ^ k),
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) raw.val ^^^ constant k (t + 1)) (rot k 1 raw.val ^^^ u.val) < 2 ^ (k - (k + 1) / 2) ∧
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) raw.val ^^^ constant k (r + (t + 1))) (rot k 3 raw.val ^^^ v.val) < 2 ^ (k - (k + 1) / 2)) ↔
      (∃ label : Fin (6 * r - 5) → Bool,
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit i)
            (!((s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 1 s ^^^ rot k (k - 1) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (2 * t) (decode label).val ^^^ constant k (t + 1)) (rot k 1 (decode label).val ^^^ u.val) < 2 ^ (k - (k + 1) / 2) ∧
      (List.range r).foldl (fun s t =>
        (List.range k).foldl (fun acc i =>
          acc ||| ((xor ((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit i)
            (!((s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 1) % k)) &&
             (s ^^^ rot k 2 s ^^^ rot k (k - 2) s).testBit ((i + 2) % k))).toNat <<< i)) 0
          ^^^ rot k (3 * (t + 1) + 1) (decode label).val ^^^ constant k (r + (t + 1))) (rot k 3 (decode label).val ^^^ v.val) < 2 ^ (k - (k + 1) / 2))
    simp only [rowEq, colEq]
    exact h2
