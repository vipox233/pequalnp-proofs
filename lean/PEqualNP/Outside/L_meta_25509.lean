import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25509_aux

private def stepBit (k word i : ℕ) : Bool :=
  word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))

private def wordStep (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc i => if stepBit k word i then acc ||| 2 ^ i else acc) 0

private theorem testBit_foldl_set (p : ℕ → Bool) (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a j => if p j then a ||| 2 ^ j else a) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih]
    by_cases hji : j = i
    · subst j
      cases hp : p i <;> simp
    · cases hp : p j <;> simp [hji, Ne.symm hji]

private theorem testBit_wordStep_all (k word i : ℕ) :
    (wordStep k word).testBit i = (decide (i < k) && stepBit k word i) := by
  simp only [wordStep, testBit_foldl_set, Nat.zero_testBit, Bool.false_or, List.mem_range]

private theorem testBit_wordStep {k word i : ℕ} (hi : i < k) :
    (wordStep k word).testBit i =
      (word.testBit i ^^ (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))) := by
  simp [testBit_wordStep_all, stepBit, hi]

private theorem wordStep_lt (k word : ℕ) : wordStep k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_wordStep_all, Nat.not_lt_of_ge hi]

private theorem wordStep_eq (k word : ℕ) :
    wordStep k word = (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0 := by
  unfold wordStep
  congr 1
  funext a j
  change (if stepBit k word j then a ||| 2 ^ j else a) =
    a ||| ((stepBit k word j).toNat <<< j)
  cases stepBit k word j <;> simp [Nat.shiftLeft_eq]

private def rot (k s w : ℕ) : ℕ :=
  ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

private theorem rot_lt {k s w : ℕ} : rot k s w < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

private theorem lt_xor {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hm := Nat.pow_le_pow_right Nat.zero_lt_two hi
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hm),
    Nat.testBit_lt_two_pow (hb.trans_le hm)]

private theorem bit_rot {k s w i : ℕ} (wlt : w < 2 ^ k) (ilt : i < k) :
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

private def mixWord (k s : ℕ) : ℕ := s ^^^ rot k 1 s ^^^ rot k (k - 1) s

private theorem testBit_mixWord {k s p : ℕ} (hk : 2 ≤ k) (hs : s < 2 ^ k) (hp : p < k) :
    (mixWord k s).testBit p =
      (s.testBit p ^^ s.testBit ((p + k - 1) % k) ^^ s.testBit ((p + 1) % k)) := by
  unfold mixWord
  rw [Nat.testBit_xor, Nat.testBit_xor, bit_rot hs hp, bit_rot hs hp]
  have e1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have e2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [e1, e2, show p + k - (k - 1) = p + 1 by omega]

private def st (k : ℕ) (constants : ℕ → Fin (2 ^ k)) (x0 key : ℕ) : ℕ → ℕ
  | 0 => x0
  | t + 1 => wordStep k (mixWord k (st k constants x0 key t)) ^^^ rot k (2 * t) key ^^^ (constants (t + 1)).val

private theorem st_lt {k : ℕ} (constants : ℕ → Fin (2 ^ k)) {x0 key : ℕ} (hx : x0 < 2 ^ k) (t : ℕ) :
    st k constants x0 key t < 2 ^ k := by
  cases t with
  | zero => exact hx
  | succ t => exact lt_xor (lt_xor (wordStep_lt _ _) rot_lt) (constants (t + 1)).isLt

private theorem st_fold (k : ℕ) (constants : ℕ → Fin (2 ^ k)) (x0 key r : ℕ) :
    (List.range r).foldl (fun prev t =>
      wordStep k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * t) key ^^^
        (constants (t + 1)).val) x0 = st k constants x0 key r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    rfl

private def flipBit (k pos w : ℕ) : ℕ := w ^^^ (1 <<< (pos % k))

private theorem flipBit_lt {k pos w : ℕ} (hk : 0 < k) (hw : w < 2 ^ k) : flipBit k pos w < 2 ^ k := by
  unfold flipBit
  have hp : pos % k < k := Nat.mod_lt _ hk
  have h1 : 1 <<< (pos % k) < 2 ^ k := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) hp
  exact lt_xor hw h1

private theorem flipBit_invol {k pos w : ℕ} : flipBit k pos (flipBit k pos w) = w := by
  unfold flipBit
  apply Nat.eq_of_testBit_eq
  intro b
  simp [Nat.testBit_xor]

private theorem testBit_flipBit {k pos w b : ℕ} (hk : 0 < k) :
    (flipBit k pos w).testBit b = (w.testBit b ^^ decide (b = pos % k)) := by
  unfold flipBit
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  by_cases h : pos % k = b
  · subst h; simp
  · simp [h, Ne.symm h]

private theorem testBit_rot_xor_flip {k s pos w b : ℕ} (hk : 0 < k) (hw : w < 2 ^ k) (hb : b < k) :
    ((rot k s w).testBit b ^^ (rot k s (flipBit k pos w)).testBit b) =
      decide (b = (pos + s) % k) := by
  rw [bit_rot hw hb, bit_rot (flipBit_lt hk hw) hb, testBit_flipBit hk]
  have hcancel (a c : Bool) : (a ^^ (a ^^ c)) = c := by cases a <;> cases c <;> rfl
  rw [hcancel]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  have hs : s % k < k := Nat.mod_lt _ hk
  constructor
  · intro h
    have h1 : ((b + k - s % k) + s % k) % k = (pos % k + s % k) % k := by
      rw [← Nat.mod_add_mod (b + k - s % k), h, Nat.mod_add_mod]
    rw [Nat.sub_add_cancel (by omega), Nat.add_mod_right, Nat.mod_eq_of_lt hb] at h1
    rw [h1, Nat.mod_add_mod, Nat.add_mod_mod]
  · intro h
    subst h
    have h1 : ((pos + s) % k + k - s % k) % k = ((pos + s) % k + (k - s % k)) % k := by
      congr 1; omega
    have hdiv := Nat.div_add_mod s k
    rw [h1, Nat.mod_add_mod,
      show pos + s + (k - s % k) = pos + k * (s / k + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
      Nat.add_mul_mod_self_left]

private theorem mod_cancel_left {k Q u : ℕ} (hk : 0 < k) (hu : u < k) :
    ((Q + u) % k + k - Q % k) % k = u := by
  have hq := Nat.mod_lt Q hk
  have hdiv := Nat.div_add_mod Q k
  rw [show (Q + u) % k + k - Q % k = (Q + u) % k + (k - Q % k) by omega, Nat.mod_add_mod,
    show Q + u + (k - Q % k) = u + k * (Q / k + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hu]

private theorem testBit_mixWord_diff {k s₁ s₂ p : ℕ} (hk : 2 ≤ k)
    (hs₁ : s₁ < 2 ^ k) (hs₂ : s₂ < 2 ^ k) (hp : p < k) :
    ((mixWord k s₁).testBit p ^^ (mixWord k s₂).testBit p) =
      ((s₁.testBit p ^^ s₂.testBit p) ^^
        (s₁.testBit ((p + k - 1) % k) ^^ s₂.testBit ((p + k - 1) % k)) ^^
        (s₁.testBit ((p + 1) % k) ^^ s₂.testBit ((p + 1) % k))) := by
  rw [testBit_mixWord hk hs₁ hp, testBit_mixWord hk hs₂ hp]
  cases s₁.testBit p <;> cases s₂.testBit p <;>
    cases s₁.testBit ((p + k - 1) % k) <;> cases s₂.testBit ((p + k - 1) % k) <;>
    cases s₁.testBit ((p + 1) % k) <;> cases s₂.testBit ((p + 1) % k) <;> rfl

private theorem card_filter_half {α : Type*} [DecidableEq α] (S : Finset α) (τ : α → α)
    (p : α → Bool)
    (hmem : ∀ x ∈ S, τ x ∈ S)
    (hinvol : ∀ x ∈ S, τ (τ x) = x)
    (hflip : ∀ x ∈ S, p (τ x) = !(p x)) :
    2 * (S.filter (fun x => p x = false)).card = S.card := by
  let A := S.filter (fun x => p x = false)
  let B := S.filter (fun x => p x = true)
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun x _ => τ x)
    · intro x hx
      simp only [A, B, Finset.mem_filter] at hx ⊢
      exact ⟨hmem x hx.1, by rw [hflip x hx.1, hx.2]; rfl⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      simp only [A, Finset.mem_filter] at hx₁ hx₂
      have := congrArg τ heq
      rw [hinvol x₁ hx₁.1, hinvol x₂ hx₂.1] at this
      exact this
    · intro y hy
      simp only [A, B, Finset.mem_filter] at hy ⊢
      refine ⟨τ y, ⟨hmem y hy.1, by rw [hflip y hy.1, hy.2]; rfl⟩, hinvol y hy.1⟩
  have hunion : A ∪ B = S := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    cases p x <;> simp
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [A, B, Finset.mem_filter] at h1 h2
    rw [h1.2] at h2
    exact Bool.noConfusion h2.2
  change 2 * A.card = S.card
  rw [← hunion, Finset.card_union_of_disjoint hdisj, hAB]
  omega

private def rightReach (r t : ℕ) : ℕ := 3 * r + max t (2 * t - 3)
private def leftReach (r t : ℕ) : ℕ := 3 * r - 3 * t

private theorem diff_guard_iff {k r : ℕ} (hr : 4 ≤ r) (hk : k + 3 = 5 * r)
    (constants : ℕ → Fin (2 ^ k)) (i : Fin k) (row key : Fin (2 ^ k)) :
    let w := key.val
    let wf := flipBit k (i.val + 3 * r - 1) w
    let x0 := rot k 1 w ^^^ row.val
    let x0f := rot k 1 wf ^^^ row.val
    ((st k constants x0 w r).testBit i.val = (st k constants x0f wf r).testBit i.val) ↔
      (∀ t < r, (mixWord k (st k constants x0 w t)).testBit ((i.val + 3 * r - 3 * t - 2) % k) = false) := by
  intro w wf x0 x0f
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hw : w < 2 ^ k := key.isLt
  have hwf : wf < 2 ^ k := flipBit_lt hkpos hw
  have hx0 : x0 < 2 ^ k := lt_xor rot_lt row.isLt
  have hx0f : x0f < 2 ^ k := lt_xor rot_lt row.isLt
  let S (t : ℕ) := st k constants x0 w t
  let Sf (t : ℕ) := st k constants x0f wf t
  let D (t d : ℕ) : Bool := (S t).testBit ((i.val + d) % k) ^^ (Sf t).testBit ((i.val + d) % k)
  let G (t : ℕ) : Prop := ∀ s < t, (mixWord k (S s)).testBit ((i.val + 3 * r - 3 * s - 2) % k) = false
  have hmain (t : ℕ) (ht : t ≤ r - 1) :
      (∀ d < k, (d < leftReach r t ∨ rightReach r t < d) → D t d = false) ∧
      (D t (leftReach r t) = decide (G t)) := by
    induction t with
    | zero =>
      have hx0_diff (d : ℕ) (hd : d < k) : D 0 d = decide (d = 3 * r) := by
        dsimp [D, S, Sf, st, x0, x0f]
        have he1 : ((rot k 1 w ^^^ row.val).testBit ((i.val + d) % k) ^^
            (rot k 1 wf ^^^ row.val).testBit ((i.val + d) % k)) =
            ((rot k 1 w).testBit ((i.val + d) % k) ^^ (rot k 1 wf).testBit ((i.val + d) % k)) := by
          simp only [Nat.testBit_xor]
          cases (rot k 1 w).testBit ((i.val + d) % k) <;>
            cases (rot k 1 wf).testBit ((i.val + d) % k) <;>
            cases row.val.testBit ((i.val + d) % k) <;> rfl
        rw [he1, testBit_rot_xor_flip hkpos hw (Nat.mod_lt _ hkpos)]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        have he2 : (i.val + 3 * r - 1 + 1) % k = (i.val + 3 * r) % k := by congr 1; omega
        rw [he2]
        constructor
        · intro h
          have hsub : ((i.val + d) % k + k - i.val) % k = ((i.val + 3 * r) % k + k - i.val) % k := by rw [h]
          have hL : ((i.val + d) % k + k - i.val) % k = d := by
            rw [show (i.val + d) % k + k - i.val = (i.val + d) % k + (k - i.val) by omega,
              Nat.mod_add_mod, show i.val + d + (k - i.val) = d + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hd]
          have hR : ((i.val + 3 * r) % k + k - i.val) % k = 3 * r := by
            rw [show (i.val + 3 * r) % k + k - i.val = (i.val + 3 * r) % k + (k - i.val) by omega,
              Nat.mod_add_mod, show i.val + 3 * r + (k - i.val) = 3 * r + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hL, hR] at hsub
          exact hsub
        · intro h; subst h; rfl
      refine ⟨?_, ?_⟩
      · intro d hd hor
        rw [hx0_diff d hd, decide_eq_false_iff_not]
        dsimp [leftReach, rightReach] at hor
        omega
      · rw [hx0_diff (leftReach r 0) (by dsimp [leftReach]; omega)]
        simp [leftReach, G]
    | succ t ih =>
      obtain ⟨hsupp, hleft⟩ := ih (by omega)
      have hLt : 6 ≤ leftReach r t := by dsimp [leftReach]; omega
      have hRt : rightReach r t ≤ k - 3 := by dsimp [rightReach]; omega
      have hM_diff (d : ℕ) (hd : d < k) :
          ((mixWord k (S t)).testBit ((i.val + d) % k) ^^
            (mixWord k (Sf t)).testBit ((i.val + d) % k)) =
          (D t d ^^ D t ((d + k - 1) % k) ^^ D t ((d + 1) % k)) := by
        rw [testBit_mixWord_diff hk2 (st_lt constants hx0 t) (st_lt constants hx0f t) (Nat.mod_lt _ hkpos)]
        have e1 : ((i.val + d) % k + k - 1) % k = (i.val + (d + k - 1) % k) % k := by
          rw [show (i.val + d) % k + k - 1 = (i.val + d) % k + (k - 1) by omega,
            Nat.mod_add_mod, Nat.add_mod_mod]
          congr 1; omega
        have e2 : ((i.val + d) % k + 1) % k = (i.val + (d + 1) % k) % k := by
          rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
        rw [e1, e2]
      have hM_zero (d : ℕ) (hd : d < k) (hout : d < leftReach r t - 1 ∨ rightReach r t + 1 < d) :
          (mixWord k (S t)).testBit ((i.val + d) % k) = (mixWord k (Sf t)).testBit ((i.val + d) % k) := by
        have hxor : ((mixWord k (S t)).testBit ((i.val + d) % k) ^^
            (mixWord k (Sf t)).testBit ((i.val + d) % k)) = false := by
          rw [hM_diff d hd]
          have h0 : D t d = false := hsupp d hd (by omega)
          have h1 : D t ((d + k - 1) % k) = false := by
            apply hsupp _ (Nat.mod_lt _ hkpos)
            by_cases hd0 : d = 0
            · rw [hd0, show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega)]; right; omega
            · rw [show (d + k - 1) % k = d - 1 by
                rw [show d + k - 1 = (d - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
              omega
          have h2 : D t ((d + 1) % k) = false := by
            apply hsupp _ (Nat.mod_lt _ hkpos)
            by_cases hdk : d + 1 = k
            · rw [hdk, Nat.mod_self]; left; omega
            · rw [Nat.mod_eq_of_lt (by omega)]; omega
          rw [h0, h1, h2]; rfl
        cases ha : (mixWord k (S t)).testBit ((i.val + d) % k) <;>
          cases hb : (mixWord k (Sf t)).testBit ((i.val + d) % k) <;> simp [ha, hb] at hxor ⊢
      have hkey_diff (d : ℕ) (hd : d < k) :
          ((rot k (2 * t) w).testBit ((i.val + d) % k) ^^
            (rot k (2 * t) wf).testBit ((i.val + d) % k)) =
          decide (d = 3 * r - 1 + 2 * t) := by
        rw [testBit_rot_xor_flip hkpos hw (Nat.mod_lt _ hkpos)]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        have hlt_k : 3 * r - 1 + 2 * t < k := by omega
        have he2 : (i.val + 3 * r - 1 + 2 * t) % k = (i.val + (3 * r - 1 + 2 * t)) % k := by congr 1; omega
        rw [he2]
        constructor
        · intro h
          have hsub : ((i.val + d) % k + k - i.val) % k =
              ((i.val + (3 * r - 1 + 2 * t)) % k + k - i.val) % k := by rw [h]
          have hL : ((i.val + d) % k + k - i.val) % k = d := by
            rw [show (i.val + d) % k + k - i.val = (i.val + d) % k + (k - i.val) by omega,
              Nat.mod_add_mod, show i.val + d + (k - i.val) = d + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hd]
          have hR : ((i.val + (3 * r - 1 + 2 * t)) % k + k - i.val) % k = 3 * r - 1 + 2 * t := by
            rw [show (i.val + (3 * r - 1 + 2 * t)) % k + k - i.val =
                (i.val + (3 * r - 1 + 2 * t)) % k + (k - i.val) by omega,
              Nat.mod_add_mod, show i.val + (3 * r - 1 + 2 * t) + (k - i.val) = (3 * r - 1 + 2 * t) + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hlt_k]
          rw [hL, hR] at hsub
          exact hsub
        · intro h; subst h; rfl
      have hstep_diff (d : ℕ) (hd : d < k) :
          D (t + 1) d =
            (((wordStep k (mixWord k (S t))).testBit ((i.val + d) % k) ^^
              (wordStep k (mixWord k (Sf t))).testBit ((i.val + d) % k)) ^^
              decide (d = 3 * r - 1 + 2 * t)) := by
        dsimp [D, S, Sf, st]
        simp only [Nat.testBit_xor]
        have hc := hkey_diff d hd
        rw [← hc]
        cases (wordStep k (mixWord k (S t))).testBit ((i.val + d) % k) <;>
          cases (wordStep k (mixWord k (Sf t))).testBit ((i.val + d) % k) <;>
          cases (rot k (2 * t) w).testBit ((i.val + d) % k) <;>
          cases (rot k (2 * t) wf).testBit ((i.val + d) % k) <;>
          cases (constants (t + 1)).val.testBit ((i.val + d) % k) <;> rfl
      refine ⟨?_, ?_⟩
      · intro d hd hor
        rw [hstep_diff d hd]
        have hk0 : decide (d = 3 * r - 1 + 2 * t) = false := by
          rw [decide_eq_false_iff_not]
          dsimp [leftReach, rightReach] at hor
          omega
        rw [hk0, Bool.xor_false, testBit_wordStep (Nat.mod_lt _ hkpos), testBit_wordStep (Nat.mod_lt _ hkpos)]
        have e1 : ((i.val + d) % k + 1) % k = (i.val + (d + 1) % k) % k := by
          rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
        have e2 : ((i.val + d) % k + 2) % k = (i.val + (d + 2) % k) % k := by
          rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
        rw [e1, e2]
        have hm0 : (mixWord k (S t)).testBit ((i.val + d) % k) =
            (mixWord k (Sf t)).testBit ((i.val + d) % k) := by
          apply hM_zero d hd
          dsimp [leftReach, rightReach] at hor ⊢
          omega
        have hm1 : (mixWord k (S t)).testBit ((i.val + (d + 1) % k) % k) =
            (mixWord k (Sf t)).testBit ((i.val + (d + 1) % k) % k) := by
          apply hM_zero _ (Nat.mod_lt _ hkpos)
          dsimp [leftReach, rightReach] at hor ⊢
          by_cases hdk : d + 1 < k
          · rw [Nat.mod_eq_of_lt hdk]; omega
          · rw [show d + 1 = k by omega, Nat.mod_self]; left; omega
        have hm2 : (mixWord k (S t)).testBit ((i.val + (d + 2) % k) % k) =
            (mixWord k (Sf t)).testBit ((i.val + (d + 2) % k) % k) := by
          apply hM_zero _ (Nat.mod_lt _ hkpos)
          dsimp [leftReach, rightReach] at hor ⊢
          by_cases hdk : d + 2 < k
          · rw [Nat.mod_eq_of_lt hdk]; omega
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; left; omega
        rw [hm0, hm1, hm2]
        simp
      · let d := leftReach r (t + 1)
        have hd : d < k := by dsimp [d, leftReach]; omega
        rw [hstep_diff d hd]
        have hk0 : decide (d = 3 * r - 1 + 2 * t) = false := by
          rw [decide_eq_false_iff_not]; dsimp [d, leftReach]; omega
        rw [hk0, Bool.xor_false, testBit_wordStep (Nat.mod_lt _ hkpos), testBit_wordStep (Nat.mod_lt _ hkpos)]
        have e1 : ((i.val + d) % k + 1) % k = (i.val + (d + 1)) % k := by
          rw [Nat.mod_add_mod, Nat.add_assoc]
        have e2 : ((i.val + d) % k + 2) % k = (i.val + (d + 2)) % k := by
          rw [Nat.mod_add_mod, Nat.add_assoc]
        rw [e1, e2]
        have hd1 : d + 1 < k := by dsimp [d, leftReach]; omega
        have hd2 : d + 2 < k := by dsimp [d, leftReach]; omega
        have hm0 : (mixWord k (S t)).testBit ((i.val + d) % k) =
            (mixWord k (Sf t)).testBit ((i.val + d) % k) :=
          hM_zero d hd (by left; dsimp [d, leftReach]; omega)
        have hm1 : (mixWord k (S t)).testBit ((i.val + (d + 1)) % k) =
            (mixWord k (Sf t)).testBit ((i.val + (d + 1)) % k) :=
          hM_zero (d + 1) hd1 (by left; dsimp [d, leftReach]; omega)
        have hm2_diff : ((mixWord k (S t)).testBit ((i.val + (d + 2)) % k) ^^
            (mixWord k (Sf t)).testBit ((i.val + (d + 2)) % k)) = D t (leftReach r t) := by
          rw [hM_diff (d + 2) hd2]
          have ha : D t (d + 2) = false := hsupp (d + 2) hd2 (by left; dsimp [d, leftReach]; omega)
          have hb : D t ((d + 2 + k - 1) % k) = false := by
            rw [show (d + 2 + k - 1) % k = d + 1 by
              rw [show d + 2 + k - 1 = (d + 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hd1]]
            exact hsupp (d + 1) hd1 (by left; dsimp [d, leftReach]; omega)
          have hc : (d + 2 + 1) % k = leftReach r t := by
            rw [Nat.mod_eq_of_lt (by dsimp [d, leftReach]; omega)]
            dsimp [d, leftReach]; omega
          rw [ha, hb, hc]; simp
        have hstep_eq :
            (((mixWord k (S t)).testBit ((i.val + d) % k) ^^
              (!(mixWord k (S t)).testBit ((i.val + (d + 1)) % k) &&
                (mixWord k (S t)).testBit ((i.val + (d + 2)) % k))) ^^
            ((mixWord k (Sf t)).testBit ((i.val + d) % k) ^^
              (!(mixWord k (Sf t)).testBit ((i.val + (d + 1)) % k) &&
                (mixWord k (Sf t)).testBit ((i.val + (d + 2)) % k)))) =
            (!(mixWord k (S t)).testBit ((i.val + (d + 1)) % k) && D t (leftReach r t)) := by
          rw [hm0, hm1, ← hm2_diff]
          cases (mixWord k (Sf t)).testBit ((i.val + d) % k) <;>
            cases (mixWord k (Sf t)).testBit ((i.val + (d + 1)) % k) <;>
            cases (mixWord k (S t)).testBit ((i.val + (d + 2)) % k) <;>
            cases (mixWord k (Sf t)).testBit ((i.val + (d + 2)) % k) <;> rfl
        rw [hstep_eq, hleft]
        have hed : i.val + (d + 1) = i.val + 3 * r - 3 * t - 2 := by dsimp [d, leftReach]; omega
        rw [hed]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, G]
        constructor
        · rintro ⟨htg, hprev⟩ s hs
          by_cases hst : s < t
          · exact hprev s hst
          · obtain rfl : s = t := by omega
            exact htg
        · intro hall
          exact ⟨hall t (by omega), fun s hs => hall s (by omega)⟩
  obtain ⟨hsupp, hleft⟩ := hmain (r - 1) le_rfl
  have hr1 : r = (r - 1) + 1 := by omega
  have hM_diff (d : ℕ) (hd : d < k) :
      ((mixWord k (S (r - 1))).testBit ((i.val + d) % k) ^^
        (mixWord k (Sf (r - 1))).testBit ((i.val + d) % k)) =
      (D (r - 1) d ^^ D (r - 1) ((d + k - 1) % k) ^^ D (r - 1) ((d + 1) % k)) := by
    rw [testBit_mixWord_diff hk2 (st_lt constants hx0 (r - 1)) (st_lt constants hx0f (r - 1)) (Nat.mod_lt _ hkpos)]
    have e1 : ((i.val + d) % k + k - 1) % k = (i.val + (d + k - 1) % k) % k := by
      rw [show (i.val + d) % k + k - 1 = (i.val + d) % k + (k - 1) by omega,
        Nat.mod_add_mod, Nat.add_mod_mod]; congr 1; omega
    have e2 : ((i.val + d) % k + 1) % k = (i.val + (d + 1) % k) % k := by
      rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]
    rw [e1, e2]
  have hM0 : (mixWord k (S (r - 1))).testBit i.val = (mixWord k (Sf (r - 1))).testBit i.val := by
    have h0 := hM_diff 0 hkpos
    rw [Nat.add_zero, Nat.mod_eq_of_lt i.isLt] at h0
    have ha : D (r - 1) 0 = false := hsupp 0 hkpos (by left; dsimp [leftReach]; omega)
    have hb : D (r - 1) ((0 + k - 1) % k) = false := by
      have hk1 : (0 + k - 1) % k = k - 1 := by simp [Nat.mod_eq_of_lt (by omega : k - 1 < k)]
      rw [hk1]
      exact hsupp (k - 1) (by omega) (by right; dsimp [rightReach]; omega)
    have hc : D (r - 1) ((0 + 1) % k) = false := by
      rw [show (0 + 1) % k = 1 by rw [Nat.mod_eq_of_lt (by omega)]]
      exact hsupp 1 (by omega) (by left; dsimp [leftReach]; omega)
    rw [ha, hb, hc] at h0
    cases a : (mixWord k (S (r - 1))).testBit i.val <;>
      cases b : (mixWord k (Sf (r - 1))).testBit i.val <;> simp [a, b] at h0 ⊢
  have hM1 : (mixWord k (S (r - 1))).testBit ((i.val + 1) % k) =
      (mixWord k (Sf (r - 1))).testBit ((i.val + 1) % k) := by
    have h1 := hM_diff 1 (by omega)
    have ha : D (r - 1) 1 = false := hsupp 1 (by omega) (by left; dsimp [leftReach]; omega)
    have hb : D (r - 1) ((1 + k - 1) % k) = false := by
      rw [show (1 + k - 1) % k = 0 by rw [show 1 + k - 1 = k by omega, Nat.mod_self]]
      exact hsupp 0 hkpos (by left; dsimp [leftReach]; omega)
    have hc : D (r - 1) ((1 + 1) % k) = false := by
      rw [show (1 + 1) % k = 2 by rw [Nat.mod_eq_of_lt (by omega)]]
      exact hsupp 2 (by omega) (by left; dsimp [leftReach]; omega)
    rw [ha, hb, hc] at h1
    cases a : (mixWord k (S (r - 1))).testBit ((i.val + 1) % k) <;>
      cases b : (mixWord k (Sf (r - 1))).testBit ((i.val + 1) % k) <;> simp [a, b] at h1 ⊢
  have hM2 : ((mixWord k (S (r - 1))).testBit ((i.val + 2) % k) ^^
      (mixWord k (Sf (r - 1))).testBit ((i.val + 2) % k)) = D (r - 1) (leftReach r (r - 1)) := by
    have h2 := hM_diff 2 (by omega)
    have ha : D (r - 1) 2 = false := hsupp 2 (by omega) (by left; dsimp [leftReach]; omega)
    have hb : D (r - 1) ((2 + k - 1) % k) = false := by
      rw [show (2 + k - 1) % k = 1 by
        rw [show 2 + k - 1 = 1 + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
      exact hsupp 1 (by omega) (by left; dsimp [leftReach]; omega)
    have hc : (2 + 1) % k = leftReach r (r - 1) := by
      rw [Nat.mod_eq_of_lt (by omega)]; dsimp [leftReach]; omega
    rw [ha, hb, hc] at h2
    simpa using h2
  have hkey_last : ((rot k (2 * (r - 1)) w).testBit i.val ^^
      (rot k (2 * (r - 1)) wf).testBit i.val) = true := by
    rw [testBit_rot_xor_flip hkpos hw i.isLt]
    have he : (i.val + 3 * r - 1 + 2 * (r - 1)) % k = i.val := by
      rw [show i.val + 3 * r - 1 + 2 * (r - 1) = i.val + k by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
    rw [he]; simp
  have hfinal_xor : ((S r).testBit i.val ^^ (Sf r).testBit i.val) =
      !(!(mixWord k (S (r - 1))).testBit ((i.val + 1) % k) && D (r - 1) (leftReach r (r - 1))) := by
    have hSr : S r = wordStep k (mixWord k (S (r - 1))) ^^^ rot k (2 * (r - 1)) w ^^^ (constants r).val := by
      conv_lhs => rw [hr1]
      dsimp [S, st]; rw [show r - 1 + 1 = r by omega]
    have hSfr : Sf r = wordStep k (mixWord k (Sf (r - 1))) ^^^ rot k (2 * (r - 1)) wf ^^^ (constants r).val := by
      conv_lhs => rw [hr1]
      dsimp [Sf, st]; rw [show r - 1 + 1 = r by omega]
    rw [hSr, hSfr]
    simp only [Nat.testBit_xor, testBit_wordStep i.isLt]
    have hc : ((wordStep k (mixWord k (S (r - 1)))).testBit i.val ^^
        (wordStep k (mixWord k (Sf (r - 1)))).testBit i.val) =
        (!(mixWord k (S (r - 1))).testBit ((i.val + 1) % k) && D (r - 1) (leftReach r (r - 1))) := by
      rw [testBit_wordStep i.isLt, testBit_wordStep i.isLt, hM0, hM1, ← hM2]
      cases (mixWord k (Sf (r - 1))).testBit i.val <;>
        cases (mixWord k (Sf (r - 1))).testBit ((i.val + 1) % k) <;>
        cases (mixWord k (S (r - 1))).testBit ((i.val + 2) % k) <;>
        cases (mixWord k (Sf (r - 1))).testBit ((i.val + 2) % k) <;> rfl
    rw [testBit_wordStep i.isLt, testBit_wordStep i.isLt] at hc
    rw [← hc]
    have h1 := hkey_last
    cases a : ((mixWord k (S (r - 1))).testBit i.val ^^
        (!(mixWord k (S (r - 1))).testBit ((i.val + 1) % k) &&
          (mixWord k (S (r - 1))).testBit ((i.val + 2) % k))) <;>
      cases b : ((mixWord k (Sf (r - 1))).testBit i.val ^^
        (!(mixWord k (Sf (r - 1))).testBit ((i.val + 1) % k) &&
          (mixWord k (Sf (r - 1))).testBit ((i.val + 2) % k))) <;>
      cases c1 : (rot k (2 * (r - 1)) w).testBit i.val <;>
      cases c2 : (rot k (2 * (r - 1)) wf).testBit i.val <;>
      cases c3 : (constants r).val.testBit i.val <;>
      simp [a, b, c1, c2, c3] at h1 ⊢
  have heq_iff : ((S r).testBit i.val = (Sf r).testBit i.val) ↔
      ((S r).testBit i.val ^^ (Sf r).testBit i.val) = false := by
    cases (S r).testBit i.val <;> cases (Sf r).testBit i.val <;> decide
  rw [heq_iff, hfinal_xor, Bool.not_eq_false', Bool.and_eq_true, Bool.not_eq_true', hleft, decide_eq_true_eq]
  have he_last : i.val + 1 = i.val + 3 * r - 3 * (r - 1) - 2 := by omega
  rw [he_last]
  constructor
  · rintro ⟨hlast, hprev⟩ t ht
    by_cases hlt : t < r - 1
    · exact hprev t hlt
    · obtain rfl : t = r - 1 := by omega
      exact hlast
  · intro hall
    exact ⟨hall (r - 1) (by omega), fun t ht => hall t (by omega)⟩

private theorem key_flip_support_v2 {k r m : ℕ} (hr : 4 ≤ r) (hk : k + 3 = 5 * r) (hm : m ≤ r - 2)
    (constants : ℕ → Fin (2 ^ k)) (i : Fin k) (x0 : Fin (2 ^ k)) (w : Fin (2 ^ k)) :
    let Q := i.val + 3 * r + 1
    let piv := Q + (k - 5 * m - 7)
    let wf := flipBit k piv w.val
    (∀ s ≤ m, ∀ u < k, (k + 2 * s - 5 * m - 8 ≤ u ∧ u < k - 3 * s) →
      (st k constants x0.val w.val s).testBit ((Q + u) % k) =
        (st k constants x0.val wf s).testBit ((Q + u) % k)) := by
  intro Q piv wf
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hwf : wf < 2 ^ k := flipBit_lt hkpos w.isLt
  intro s hs
  induction s with
  | zero => intro u _ _; rfl
  | succ s ih =>
    intro u hu hrange
    have hkey_eq : (rot k (2 * s) w.val).testBit ((Q + u) % k) =
        (rot k (2 * s) wf).testBit ((Q + u) % k) := by
      have hx := testBit_rot_xor_flip (s := 2 * s) (pos := piv) hkpos w.isLt (Nat.mod_lt (Q + u) hkpos)
      have hne : (Q + u) % k ≠ (piv + 2 * s) % k := by
        intro heq
        have hpeq : piv + 2 * s = Q + (k - 5 * m - 7 + 2 * s) := by dsimp [piv]; omega
        rw [hpeq] at heq
        have hsub : ((Q + u) % k + k - Q % k) % k =
            ((Q + (k - 5 * m - 7 + 2 * s)) % k + k - Q % k) % k := by rw [heq]
        rw [mod_cancel_left hkpos hu, mod_cancel_left hkpos (by omega)] at hsub
        omega
      rw [decide_eq_false hne] at hx
      dsimp only [wf]
      cases a : (rot k (2 * s) w.val).testBit ((Q + u) % k) <;>
        cases b : (rot k (2 * s) (flipBit k piv w.val)).testBit ((Q + u) % k) <;> simp [a, b] at hx ⊢
    have hM_eq (v : ℕ) (hv : v < k) (hvr : k + 2 * s - 5 * m - 7 ≤ v ∧ v + 1 < k - 3 * s) :
        (mixWord k (st k constants x0.val w.val s)).testBit ((Q + v) % k) =
          (mixWord k (st k constants x0.val wf s)).testBit ((Q + v) % k) := by
      cases s with
      | zero => rfl
      | succ s' =>
        rw [testBit_mixWord hk2 (st_lt constants x0.isLt (s' + 1)) (Nat.mod_lt _ hkpos),
          testBit_mixWord hk2 (st_lt constants x0.isLt (s' + 1)) (Nat.mod_lt _ hkpos)]
        have h0 := ih (by omega) v hv (by omega)
        have e1 : ((Q + v) % k + k - 1) % k = (Q + (v - 1)) % k := by
          rw [show (Q + v) % k + k - 1 = (Q + v) % k + (k - 1) by omega, Nat.mod_add_mod,
            show Q + v + (k - 1) = (Q + (v - 1)) + k by omega, Nat.add_mod_right]
        have e2 : ((Q + v) % k + 1) % k = (Q + (v + 1)) % k := by
          rw [Nat.mod_add_mod, Nat.add_assoc]
        rw [e1, e2, ih (by omega) (v - 1) (by omega) (by omega), ih (by omega) (v + 1) (by omega) (by omega)]
        rw [h0]
    dsimp [st]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor,
      testBit_wordStep (Nat.mod_lt _ hkpos), testBit_wordStep (Nat.mod_lt _ hkpos), hkey_eq]
    have e1 : ((Q + u) % k + 1) % k = (Q + (u + 1)) % k := by rw [Nat.mod_add_mod, Nat.add_assoc]
    have e2 : ((Q + u) % k + 2) % k = (Q + (u + 2)) % k := by rw [Nat.mod_add_mod, Nat.add_assoc]
    rw [e1, e2, hM_eq u hu (by omega), hM_eq (u + 1) (by omega) (by omega),
      hM_eq (u + 2) (by omega) (by omega)]

private theorem count_keys_for_x0 {k r : ℕ} (hr : 4 ≤ r) (hk : k + 3 = 5 * r)
    (constants : ℕ → Fin (2 ^ k)) (i : Fin k) (x0 : Fin (2 ^ k)) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
      ∀ t < r - 1, (mixWord k (st k constants x0.val w.val (t + 1))).testBit
        ((i.val + 3 * r - 3 * (t + 1) - 2) % k) = false)).card = 2 ^ (k - (r - 1)) := by
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  let Q := i.val + 3 * r + 1
  let GSet (m : ℕ) : Finset (Fin (2 ^ k)) :=
    Finset.univ.filter (fun w =>
      ∀ t < m, (mixWord k (st k constants x0.val w.val (t + 1))).testBit
        ((i.val + 3 * r - 3 * (t + 1) - 2) % k) = false)
  have hcard (m : ℕ) (hm : m ≤ r - 1) : (GSet m).card * 2 ^ m = 2 ^ k := by
    induction m with
    | zero => simp [GSet]
    | succ m ih =>
      have hm2 : m ≤ r - 2 := by omega
      let piv := Q + (k - 5 * m - 7)
      let τ : Fin (2 ^ k) → Fin (2 ^ k) := fun w => ⟨flipBit k piv w.val, flipBit_lt hkpos w.isLt⟩
      let p : Fin (2 ^ k) → Bool := fun w =>
        (mixWord k (st k constants x0.val w.val (m + 1))).testBit ((i.val + 3 * r - 3 * (m + 1) - 2) % k)
      have hguard_pos (t : ℕ) (ht : t ≤ r - 2) :
          (i.val + 3 * r - 3 * (t + 1) - 2) % k = (Q + (k - 3 * t - 6)) % k := by
        rw [show Q + (k - 3 * t - 6) = (i.val + 3 * r - 3 * (t + 1) - 2) + k by dsimp [Q]; omega,
          Nat.add_mod_right]
      have hprev_eq (w : Fin (2 ^ k)) (t : ℕ) (ht : t < m) :
          (mixWord k (st k constants x0.val (τ w).val (t + 1))).testBit ((i.val + 3 * r - 3 * (t + 1) - 2) % k) =
            (mixWord k (st k constants x0.val w.val (t + 1))).testBit ((i.val + 3 * r - 3 * (t + 1) - 2) % k) := by
        rw [hguard_pos t (by omega)]
        rw [testBit_mixWord hk2 (st_lt constants x0.isLt (t + 1)) (Nat.mod_lt _ hkpos),
          testBit_mixWord hk2 (st_lt constants x0.isLt (t + 1)) (Nat.mod_lt _ hkpos)]
        have hs := key_flip_support_v2 hr hk hm2 constants i x0 w (t + 1) (by omega)
        have e1 : ((Q + (k - 3 * t - 6)) % k + k - 1) % k = (Q + (k - 3 * t - 7)) % k := by
          rw [show (Q + (k - 3 * t - 6)) % k + k - 1 = (Q + (k - 3 * t - 6)) % k + (k - 1) by omega,
            Nat.mod_add_mod, show Q + (k - 3 * t - 6) + (k - 1) = (Q + (k - 3 * t - 7)) + k by omega,
            Nat.add_mod_right]
        have e2 : ((Q + (k - 3 * t - 6)) % k + 1) % k = (Q + (k - 3 * t - 5)) % k := by
          rw [Nat.mod_add_mod]; congr 1; omega
        rw [e1, e2, hs (k - 3 * t - 6) (by omega) (by omega),
          hs (k - 3 * t - 7) (by omega) (by omega), hs (k - 3 * t - 5) (by omega) (by omega)]
      have hflip (w : Fin (2 ^ k)) : p (τ w) = !(p w) := by
        dsimp [p]
        rw [hguard_pos m hm2]
        rw [testBit_mixWord hk2 (st_lt constants x0.isLt (m + 1)) (Nat.mod_lt _ hkpos),
          testBit_mixWord hk2 (st_lt constants x0.isLt (m + 1)) (Nat.mod_lt _ hkpos)]
        have e1 : ((Q + (k - 3 * m - 6)) % k + k - 1) % k = (Q + (k - 3 * m - 7)) % k := by
          rw [show (Q + (k - 3 * m - 6)) % k + k - 1 = (Q + (k - 3 * m - 6)) % k + (k - 1) by omega,
            Nat.mod_add_mod, show Q + (k - 3 * m - 6) + (k - 1) = (Q + (k - 3 * m - 7)) + k by omega,
            Nat.add_mod_right]
        have e2 : ((Q + (k - 3 * m - 6)) % k + 1) % k = (Q + (k - 3 * m - 5)) % k := by
          rw [Nat.mod_add_mod]; congr 1; omega
        rw [e1, e2]
        have hs := key_flip_support_v2 hr hk hm2 constants i x0 w m le_rfl
        have hM_eq (v : ℕ) (hv : v < k) (hvr : k - 3 * m - 7 ≤ v ∧ v + 1 < k - 3 * m) :
            (mixWord k (st k constants x0.val (τ w).val m)).testBit ((Q + v) % k) =
              (mixWord k (st k constants x0.val w.val m)).testBit ((Q + v) % k) := by
          cases hm0 : m with
          | zero => rfl
          | succ m' =>
            subst hm0
            rw [testBit_mixWord hk2 (st_lt constants x0.isLt (m' + 1)) (Nat.mod_lt _ hkpos),
              testBit_mixWord hk2 (st_lt constants x0.isLt (m' + 1)) (Nat.mod_lt _ hkpos)]
            have f1 : ((Q + v) % k + k - 1) % k = (Q + (v - 1)) % k := by
              rw [show (Q + v) % k + k - 1 = (Q + v) % k + (k - 1) by omega, Nat.mod_add_mod,
                show Q + v + (k - 1) = (Q + (v - 1)) + k by omega, Nat.add_mod_right]
            have f2 : ((Q + v) % k + 1) % k = (Q + (v + 1)) % k := by
              rw [Nat.mod_add_mod, Nat.add_assoc]
            rw [f1, f2, (hs v hv (by omega)).symm, (hs (v - 1) (by omega) (by omega)).symm,
              (hs (v + 1) (by omega) (by omega)).symm]
        have hstep_eq (u : ℕ) (hu : u < k) (hur : k - 3 * m - 7 ≤ u ∧ u ≤ k - 3 * m - 5) :
            (wordStep k (mixWord k (st k constants x0.val (τ w).val m))).testBit ((Q + u) % k) =
              (wordStep k (mixWord k (st k constants x0.val w.val m))).testBit ((Q + u) % k) := by
          rw [testBit_wordStep (Nat.mod_lt _ hkpos), testBit_wordStep (Nat.mod_lt _ hkpos)]
          have f1 : ((Q + u) % k + 1) % k = (Q + (u + 1)) % k := by rw [Nat.mod_add_mod, Nat.add_assoc]
          have f2 : ((Q + u) % k + 2) % k = (Q + (u + 2)) % k := by rw [Nat.mod_add_mod, Nat.add_assoc]
          rw [f1, f2, hM_eq u hu (by omega), hM_eq (u + 1) (by omega) (by omega),
            hM_eq (u + 2) (by omega) (by omega)]
        have hk_hit (u : ℕ) (hu : u < k) :
            ((rot k (2 * m) w.val).testBit ((Q + u) % k) ^^
              (rot k (2 * m) (τ w).val).testBit ((Q + u) % k)) = decide (u = k - 3 * m - 7) := by
          have hx := testBit_rot_xor_flip (s := 2 * m) (pos := piv) hkpos w.isLt (Nat.mod_lt (Q + u) hkpos)
          rw [hx]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          have hpiv_eq : piv + 2 * m = Q + (k - 3 * m - 7) := by dsimp [piv]; omega
          rw [hpiv_eq]
          constructor
          · intro heq
            have hsub : ((Q + u) % k + k - Q % k) % k =
                ((Q + (k - 3 * m - 7)) % k + k - Q % k) % k := by rw [heq]
            rw [mod_cancel_left hkpos hu, mod_cancel_left hkpos (by omega)] at hsub
            exact hsub
          · intro h; subst h; rfl
        have hbit_eq (u : ℕ) (hu : u < k) (hur : k - 3 * m - 7 ≤ u ∧ u ≤ k - 3 * m - 5) :
            (st k constants x0.val (τ w).val (m + 1)).testBit ((Q + u) % k) =
              ((st k constants x0.val w.val (m + 1)).testBit ((Q + u) % k) ^^ decide (u = k - 3 * m - 7)) := by
          dsimp [st]
          simp only [Nat.testBit_xor, hstep_eq u hu hur]
          have hkh := hk_hit u hu
          cases a : (wordStep k (mixWord k (st k constants x0.val w.val m))).testBit ((Q + u) % k) <;>
            cases b1 : (rot k (2 * m) w.val).testBit ((Q + u) % k) <;>
            cases b2 : (rot k (2 * m) (τ w).val).testBit ((Q + u) % k) <;>
            cases c : (constants (m + 1)).val.testBit ((Q + u) % k) <;>
            cases d : decide (u = k - 3 * m - 7) <;> simp [b1, b2, d] at hkh ⊢
        rw [hbit_eq (k - 3 * m - 6) (by omega) (by omega),
          hbit_eq (k - 3 * m - 7) (by omega) (by omega),
          hbit_eq (k - 3 * m - 5) (by omega) (by omega)]
        have d1 : decide (k - 3 * m - 6 = k - 3 * m - 7) = false := by rw [decide_eq_false_iff_not]; omega
        have d2 : decide (k - 3 * m - 7 = k - 3 * m - 7) = true := by simp
        have d3 : decide (k - 3 * m - 5 = k - 3 * m - 7) = false := by rw [decide_eq_false_iff_not]; omega
        rw [d1, d2, d3]
        cases (st k constants x0.val w.val (m + 1)).testBit ((Q + (k - 3 * m - 6)) % k) <;>
          cases (st k constants x0.val w.val (m + 1)).testBit ((Q + (k - 3 * m - 7)) % k) <;>
          cases (st k constants x0.val w.val (m + 1)).testBit ((Q + (k - 3 * m - 5)) % k) <;> rfl
      have hGsucc : GSet (m + 1) = (GSet m).filter (fun w => p w = false) := by
        ext w
        simp only [GSet, Finset.mem_filter, Finset.mem_univ, true_and, p]
        constructor
        · intro h; exact ⟨fun t ht => h t (by omega), h m (by omega)⟩
        · rintro ⟨h1, h2⟩ t ht
          by_cases hlt : t < m
          · exact h1 t hlt
          · obtain rfl : t = m := by omega
            exact h2
      have hhalf : 2 * (GSet (m + 1)).card = (GSet m).card := by
        rw [hGsucc]
        apply card_filter_half (GSet m) τ p
        · intro w hw
          simp only [GSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          intro t ht
          rw [hprev_eq w t ht]
          exact hw t ht
        · intro w _
          exact Fin.ext flipBit_invol
        · intro w _
          exact hflip w
      have ih' := ih (by omega)
      calc
        (GSet (m + 1)).card * 2 ^ (m + 1) = (2 * (GSet (m + 1)).card) * 2 ^ m := by ring
        _ = (GSet m).card * 2 ^ m := by rw [hhalf]
        _ = 2 ^ k := ih'
  have hfinal := hcard (r - 1) le_rfl
  have hmul : 2 ^ (k - (r - 1)) * 2 ^ (r - 1) = 2 ^ k := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hpos : 0 < 2 ^ (r - 1) := Nat.two_pow_pos _
  exact Nat.eq_of_mul_eq_mul_right hpos (hfinal.trans hmul.symm)

private theorem count_x0 {k r : ℕ} (hr : 4 ≤ r) (hk : k + 3 = 5 * r) (i : Fin k) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x0 =>
      (mixWord k x0.val).testBit ((i.val + 3 * r - 2) % k) = false)).card = 2 ^ (k - 1) := by
  have hkpos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  let pos := (i.val + 3 * r - 2) % k
  let τ : Fin (2 ^ k) → Fin (2 ^ k) := fun x => ⟨flipBit k pos x.val, flipBit_lt hkpos x.isLt⟩
  let p : Fin (2 ^ k) → Bool := fun x => (mixWord k x.val).testBit pos
  have hhalf : 2 * ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => p x = false)).card = 2 ^ k := by
    have h := card_filter_half (Finset.univ : Finset (Fin (2 ^ k))) τ p
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ => Fin.ext flipBit_invol)
      (fun x _ => by
        dsimp [p, τ]
        have hpos : pos < k := Nat.mod_lt _ hkpos
        rw [testBit_mixWord hk2 (flipBit_lt hkpos x.isLt) hpos,
          testBit_mixWord hk2 x.isLt hpos,
          testBit_flipBit hkpos, testBit_flipBit hkpos, testBit_flipBit hkpos]
        have hpm : pos % k = pos := Nat.mod_eq_of_lt hpos
        have hne1 : (pos + k - 1) % k ≠ pos := by
          by_cases hp0 : pos = 0
          · rw [hp0, show 0 + k - 1 = k - 1 by omega, Nat.mod_eq_of_lt (by omega)]; omega
          · rw [show (pos + k - 1) % k = pos - 1 by
              rw [show pos + k - 1 = (pos - 1) + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
            omega
        have hne2 : (pos + 1) % k ≠ pos := by
          by_cases hpk : pos + 1 = k
          · rw [hpk, Nat.mod_self]; omega
          · rw [Nat.mod_eq_of_lt (by omega)]; omega
        rw [hpm, decide_eq_true rfl, decide_eq_false hne1, decide_eq_false hne2]
        cases x.val.testBit pos <;> cases x.val.testBit ((pos + k - 1) % k) <;>
          cases x.val.testBit ((pos + 1) % k) <;> rfl)
    simpa using h
  have hmul : 2 * 2 ^ (k - 1) = 2 ^ k := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  change ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun x => p x = false)).card = 2 ^ (k - 1)
  omega

private theorem main_count (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (i : Fin k)
    (hr : 4 ≤ r) (hk : k + 3 = 5 * r) :
    ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
      (st k constants (rot k 1 pair.2.val ^^^ pair.1.val) pair.2.val r).testBit i.val =
        (st k constants (rot k 1 (flipBit k (i.val + 3 * r - 1) pair.2.val) ^^^ pair.1.val)
          (flipBit k (i.val + 3 * r - 1) pair.2.val) r).testBit i.val)).card = 2 ^ (2 * k - r) := by
  let S_orig := (Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    (st k constants (rot k 1 pair.2.val ^^^ pair.1.val) pair.2.val r).testBit i.val =
      (st k constants (rot k 1 (flipBit k (i.val + 3 * r - 1) pair.2.val) ^^^ pair.1.val)
        (flipBit k (i.val + 3 * r - 1) pair.2.val) r).testBit i.val)
  let S_guard := (Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    ∀ t < r, (mixWord k (st k constants pair.1.val pair.2.val t)).testBit
      ((i.val + 3 * r - 3 * t - 2) % k) = false)
  have hbij : S_orig.card = S_guard.card := by
    apply Finset.card_bij (fun pair _ =>
      (⟨rot k 1 pair.2.val ^^^ pair.1.val, lt_xor rot_lt pair.1.isLt⟩, pair.2))
    · intro pair hpair
      simp only [S_orig, S_guard, Finset.mem_filter, Finset.mem_univ, true_and] at hpair ⊢
      exact (diff_guard_iff hr hk constants i pair.1 pair.2).mp hpair
    · intro p₁ _ p₂ _ heq
      rcases Prod.mk.inj heq with ⟨h1', h2⟩
      have h1v : rot k 1 p₁.2.val ^^^ p₁.1.val = rot k 1 p₂.2.val ^^^ p₂.1.val :=
        congrArg Fin.val h1'
      rw [h2] at h1v
      have h1 : p₁.1 = p₂.1 := by
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro b
        have hb := congrArg (fun n => n.testBit b) h1v
        simp only [Nat.testBit_xor] at hb
        cases h0 : (rot k 1 p₂.2.val).testBit b <;> cases ha : p₁.1.val.testBit b <;>
          cases hb' : p₂.1.val.testBit b <;> simp [h0, ha, hb'] at hb ⊢
      exact Prod.ext h1 h2
    · intro q hq
      simp only [S_orig, S_guard, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      let row : Fin (2 ^ k) := ⟨rot k 1 q.2.val ^^^ q.1.val, lt_xor rot_lt q.1.isLt⟩
      have hcancel : rot k 1 q.2.val ^^^ row.val = q.1.val := by
        apply Nat.eq_of_testBit_eq
        intro b
        dsimp [row]
        simp
      refine ⟨(row, q.2), ?_, Prod.ext (Fin.ext hcancel) rfl⟩
      exact (diff_guard_iff hr hk constants i row q.2).mpr (by rwa [hcancel])
  let X0 := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun x0 =>
    (mixWord k x0.val).testBit ((i.val + 3 * r - 2) % k) = false)
  let Wof (x0 : Fin (2 ^ k)) := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    ∀ t < r - 1, (mixWord k (st k constants x0.val w.val (t + 1))).testBit
      ((i.val + 3 * r - 3 * (t + 1) - 2) % k) = false)
  have hsigma : S_guard.card = ∑ x0 ∈ X0, (Wof x0).card := by
    rw [← Finset.card_sigma]
    apply Finset.card_bij (fun p _ => ⟨p.1, p.2⟩)
    · intro p hp
      simp only [S_guard, X0, Wof, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hp ⊢
      exact ⟨by simpa [st] using hp 0 (by omega), fun t ht => hp (t + 1) (by omega)⟩
    · intro p₁ _ p₂ _ heq
      cases p₁; cases p₂; simp at heq; exact Prod.ext heq.1 heq.2
    · intro q hq
      simp only [S_guard, X0, Wof, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hq ⊢
      refine ⟨(q.1, q.2), ?_, rfl⟩
      intro t ht
      cases t with
      | zero => simpa [st] using hq.1
      | succ t => exact hq.2 t (by omega)
  rw [hbij, hsigma]
  have hsum : ∑ x0 ∈ X0, (Wof x0).card = X0.card * 2 ^ (k - (r - 1)) := by
    have hconst : ∀ x0 ∈ X0, (Wof x0).card = 2 ^ (k - (r - 1)) := fun x0 _ =>
      count_keys_for_x0 hr hk constants i x0
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rw [hsum, count_x0 hr hk i, ← Nat.pow_add]
  congr 1
  omega

end PEqualNP.Outside.L_meta_25509_aux

theorem PEqualNP.Outside.L_meta_25509 : ∀ (k r : ℕ) (constants : ℕ → Fin (2 ^ k)) (i : Fin k),
  4 ≤ r → k + 3 = 5 * r →
  let rot := fun (s word : ℕ) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : ℕ) =>
    (List.range k).foldl (fun acc b =>
      acc ||| ((xor (word.testBit b)
        (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k))).toNat <<< b)) 0
  let state := fun (row key : ℕ) =>
    (List.range r).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (constants (t + 1)).val) (rot 1 key ^^^ row)
  let flip := fun key : ℕ => key ^^^ (1 <<< ((i.val + 3 * r - 1) % k))
  ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    (state pair.1.val pair.2.val).testBit i.val =
      (state pair.1.val (flip pair.2.val)).testBit i.val)).card = 2 ^ (2 * k - r) := by
  intro k r constants i hr hk
  dsimp only
  simp only [← PEqualNP.Outside.L_meta_25509_aux.wordStep_eq]
  have hst (row key : ℕ) :
      (List.range r).foldl (fun prev t =>
        PEqualNP.Outside.L_meta_25509_aux.wordStep k
          (prev ^^^ PEqualNP.Outside.L_meta_25509_aux.rot k 1 prev ^^^
            PEqualNP.Outside.L_meta_25509_aux.rot k (k - 1) prev) ^^^
          PEqualNP.Outside.L_meta_25509_aux.rot k (2 * t) key ^^^ (constants (t + 1)).val)
        (PEqualNP.Outside.L_meta_25509_aux.rot k 1 key ^^^ row) =
      PEqualNP.Outside.L_meta_25509_aux.st k constants
        (PEqualNP.Outside.L_meta_25509_aux.rot k 1 key ^^^ row) key r :=
    PEqualNP.Outside.L_meta_25509_aux.st_fold k constants _ key r
  change ((Finset.univ : Finset (Fin (2 ^ k) × Fin (2 ^ k))).filter (fun pair =>
    ((List.range r).foldl (fun prev t =>
      PEqualNP.Outside.L_meta_25509_aux.wordStep k
        (prev ^^^ PEqualNP.Outside.L_meta_25509_aux.rot k 1 prev ^^^
          PEqualNP.Outside.L_meta_25509_aux.rot k (k - 1) prev) ^^^
        PEqualNP.Outside.L_meta_25509_aux.rot k (2 * t) pair.2.val ^^^ (constants (t + 1)).val)
      (PEqualNP.Outside.L_meta_25509_aux.rot k 1 pair.2.val ^^^ pair.1.val)).testBit i.val =
    ((List.range r).foldl (fun prev t =>
      PEqualNP.Outside.L_meta_25509_aux.wordStep k
        (prev ^^^ PEqualNP.Outside.L_meta_25509_aux.rot k 1 prev ^^^
          PEqualNP.Outside.L_meta_25509_aux.rot k (k - 1) prev) ^^^
        PEqualNP.Outside.L_meta_25509_aux.rot k (2 * t)
          (PEqualNP.Outside.L_meta_25509_aux.flipBit k (i.val + 3 * r - 1) pair.2.val) ^^^
        (constants (t + 1)).val)
      (PEqualNP.Outside.L_meta_25509_aux.rot k 1
        (PEqualNP.Outside.L_meta_25509_aux.flipBit k (i.val + 3 * r - 1) pair.2.val) ^^^
        pair.1.val)).testBit i.val)).card = 2 ^ (2 * k - r)
  simp only [hst]
  exact PEqualNP.Outside.L_meta_25509_aux.main_count k r constants i hr hk
