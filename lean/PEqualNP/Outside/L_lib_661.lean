import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_661_aux

private lemma testBit_two_pow_sub_one_of_lt :
    ∀ (n i : Nat), i < n → (2 ^ n - 1).testBit i = true
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, 0, _ => by
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have heq : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
        rw [pow_succ]; omega
      rw [heq, Nat.testBit_zero]
      simp
  | n + 1, i + 1, hi => by
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have heq : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
        rw [pow_succ]; omega
      rw [heq, Nat.testBit_succ]
      have hdiv : (2 * (2 ^ n - 1) + 1) / 2 = 2 ^ n - 1 := by omega
      rw [hdiv]
      exact testBit_two_pow_sub_one_of_lt n i (by omega)

private lemma testBit_eq_false_of_lt_two_pow {x k m : Nat} (hx : x < 2 ^ k) (hm : k ≤ m) :
    x.testBit m = false := by
  have hle : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) hm
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx hle)

private lemma testBit_rot {k s x j : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (hj : j < k) :
    (((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k).testBit j =
      x.testBit ((j + k - s % k) % k) := by
  have hr : s % k < k := Nat.mod_lt s hk
  rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases hle : s % k ≤ j
  · have hge : k ≤ k - s % k + j := by omega
    have hright : x.testBit (k - s % k + j) = false :=
      testBit_eq_false_of_lt_two_pow hx hge
    have hmod : (j + k - s % k) % k = j - s % k := by
      have h1 : j + k - s % k = (j - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hright, Bool.or_false, hmod]
  · have hlt : j < s % k := by omega
    have hmod : (j + k - s % k) % k = k - s % k + j := by
      have h1 : j + k - s % k = k - s % k + j := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hmod]

private lemma mod_sub_mod_eq {k gap j : Nat} (hk : 0 < k) :
    ((j % k) + k - gap % k) % k = (j + k - gap % k) % k := by
  have hr : gap % k < k := Nat.mod_lt gap hk
  have hdiv := Nat.div_add_mod j k
  have heq : j + k - gap % k = (j % k + k - gap % k) + k * (j / k) := by omega
  rw [heq, Nat.add_mul_mod_self_left]

private lemma mod_sub_comp_eq {k gap j : Nat} (hk : 0 < k) (hgap : gap ≤ k) :
    (j + k - (k - gap) % k) % k = (j + gap) % k := by
  by_cases h0 : gap = 0
  · subst h0
    simp [Nat.mod_self]
  · by_cases hk' : gap = k
    · subst hk'
      simp
    · have hlt : k - gap < k := by omega
      rw [Nat.mod_eq_of_lt hlt]
      have heq : j + k - (k - gap) = j + gap := by omega
      rw [heq]

private lemma testBit_bool_toNat_shiftLeft (b : Bool) (m t : Nat) :
    (b.toNat <<< m).testBit t = (decide (t = m) && b) := by
  rw [Nat.testBit_shiftLeft]
  by_cases htm : t = m
  · subst htm
    cases b <;> simp
  · by_cases hle : m ≤ t
    · have hpos : 0 < t - m := by omega
      have hne : t - m ≠ 0 := by omega
      have hf : b.toNat.testBit (t - m) = false := by
        cases b
        · simp
        · change (1 : Nat).testBit (t - m) = false
          cases hsub : t - m with
          | zero => exact absurd hsub hne
          | succ d => simp [Nat.testBit_succ]
      simp [htm, hle, hf]
    · simp [htm, hle]

private lemma testBit_fold_step (f : Nat → Bool) :
    ∀ (m init t : Nat),
      ((List.range m).foldl (fun acc b => acc ||| ((f b).toNat <<< b)) init).testBit t =
        (init.testBit t || (decide (t < m) && f t))
  | 0, init, t => by
      simp
  | m + 1, init, t => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        Nat.testBit_or, testBit_fold_step f m init t, testBit_bool_toNat_shiftLeft]
      by_cases hlt : t < m
      · have hlt1 : t < m + 1 := by omega
        have hne : t ≠ m := by omega
        simp [hlt, hlt1, hne]
      · by_cases heq : t = m
        · subst heq
          simp
        · have hnot : ¬ (t < m + 1) := by omega
          simp [hlt, heq, hnot]

end PEqualNP.Outside.L_lib_661_aux

theorem PEqualNP.Outside.L_lib_661 :
∀ (k lanes gap : Nat) (hk : 0 < k), gap ≤ k →
  let word := Fin (2 ^ k)
  let atSite := fun j : Nat => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s x : Nat) =>
    ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k
  let step := fun (raw : Nat) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (raw.testBit b)
        (!(raw.testBit ((b + 1) % k)) && raw.testBit ((b + 2) % k))).toNat <<< b)) 0
  ∀ (state addend : Fin lanes → word) (planes additions : Fin k → Nat),
    (∀ i w, (planes i).testBit w.val = (state w).val.testBit i.val) →
    (∀ i w, (additions i).testBit w.val = (addend w).val.testBit i.val) →
    let mix := fun j : Nat =>
      planes (atSite j) ^^^ planes (atSite (j + k - gap % k)) ^^^
        planes (atSite (j + gap))
    let full := 2 ^ lanes - 1
    ∀ (i : Fin k) (w : Fin lanes),
      (mix i.val ^^^ ((full ^^^ mix (i.val + 1)) &&& mix (i.val + 2)) ^^^
        additions i).testBit w.val =
      (step ((state w).val ^^^ rot gap (state w).val ^^^ rot (k - gap) (state w).val) ^^^
        (addend w).val).testBit i.val := by
  intro k lanes gap hk hgap word atSite rot step state addend planes additions
    hplanes hadditions mix full i w
  let raw := (state w).val ^^^ rot gap (state w).val ^^^ rot (k - gap) (state w).val
  have hmix : ∀ j : Nat, (mix j).testBit w.val = raw.testBit (j % k) := by
    intro j
    have hlt : j % k < k := Nat.mod_lt j hk
    have hrot1 : (rot gap (state w).val).testBit (j % k) =
        (state w).val.testBit ((j + k - gap % k) % k) := by
      rw [PEqualNP.Outside.L_lib_661_aux.testBit_rot hk (state w).isLt hlt]
      rw [PEqualNP.Outside.L_lib_661_aux.mod_sub_mod_eq hk]
    have hrot2 : (rot (k - gap) (state w).val).testBit (j % k) =
        (state w).val.testBit ((j + gap) % k) := by
      rw [PEqualNP.Outside.L_lib_661_aux.testBit_rot hk (state w).isLt hlt]
      rw [PEqualNP.Outside.L_lib_661_aux.mod_sub_comp_eq hk hgap, Nat.mod_add_mod]
    simp only [mix, raw, Nat.testBit_xor, hplanes, atSite, hrot1, hrot2]
  have hfull : full.testBit w.val = true :=
    PEqualNP.Outside.L_lib_661_aux.testBit_two_pow_sub_one_of_lt lanes w.val w.isLt
  have hstep : (step raw).testBit i.val =
      xor (raw.testBit i.val) (!(raw.testBit ((i.val + 1) % k)) && raw.testBit ((i.val + 2) % k)) := by
    dsimp only [step]
    rw [PEqualNP.Outside.L_lib_661_aux.testBit_fold_step]
    simp [i.isLt]
  have hi_mod : i.val % k = i.val := Nat.mod_eq_of_lt i.isLt
  change (mix i.val ^^^ ((full ^^^ mix (i.val + 1)) &&& mix (i.val + 2)) ^^^
      additions i).testBit w.val =
    (step raw ^^^ (addend w).val).testBit i.val
  simp only [Nat.testBit_xor, Nat.testBit_and, hmix, hfull, hadditions, hstep, hi_mod,
    Bool.true_xor]
