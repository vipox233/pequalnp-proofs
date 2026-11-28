import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25729_aux

/-! ## Section 1: Bitwise primitives and `AgreeOn` propagation -/

private def foldOr (g : Nat → Bool) (n : Nat) : Nat :=
  (List.range n).foldl (fun acc cell => acc ||| ((g cell).toNat <<< cell)) 0

private lemma foldOr_spec (g : Nat → Bool) (n : Nat) :
    foldOr g n < 2 ^ n ∧ ∀ j : Nat, (foldOr g n).testBit j = if j < n then g j else false := by
  induction n with
  | zero =>
    exact ⟨by simp [foldOr], fun j => by simp [foldOr]⟩
  | succ n ih =>
    have hstep : foldOr g (n + 1) = foldOr g n ||| ((g n).toNat <<< n) := by
      unfold foldOr
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [hstep]
    refine ⟨?_, ?_⟩
    · apply Nat.or_lt_two_pow
      · exact lt_trans ih.1 (Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self n))
      · cases g n
        · simp
        · simp [Nat.shiftLeft_eq, Nat.pow_succ']
    · intro j
      rw [Nat.testBit_or, ih.2 j, Nat.testBit_shiftLeft]
      by_cases hjn : j < n
      · have hjle : ¬ (n ≤ j) := by omega
        have hjlt : j < n + 1 := by omega
        simp [hjn, hjle, hjlt]
      · by_cases hjeq : j = n
        · subst hjeq
          cases g j <;> simp
        · have hjlt : ¬ (j < n + 1) := by omega
          cases g n <;> simp [hjn, hjlt]
          · cases h : j - n with
            | zero => omega
            | succ r => simp [Nat.testBit_succ]

private def rotK (k offset x : Nat) : Nat :=
  ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k

private def mixK (k gap value : Nat) : Nat :=
  value ^^^ rotK k gap value ^^^ rotK k (k - gap) value

private def chiK (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0

private def stepK (k r : Nat) (constants : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) : Nat :=
  chiK k (mixK k (if col then 2 else 1) prev) ^^^
    rotK k (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
    (constants (if col then r + t else t)).val

private def stateAt (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name t : Nat) : Nat :=
  (List.range t).foldl (fun v tick => stepK k r c side key v (tick + 1))
    (rotK k (if side then 3 else 1) key ^^^ name)

private lemma rotK_lt (k offset x : Nat) : rotK k offset x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma mixK_lt {k : Nat} (gap value : Nat) (hv : value < 2 ^ k) : mixK k gap value < 2 ^ k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hv (rotK_lt k gap value)) (rotK_lt k (k - gap) value)

private lemma chiK_lt (k word : Nat) : chiK k word < 2 ^ k :=
  (foldOr_spec _ k).1

private lemma stepK_lt (k r : Nat) (c : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) :
    stepK k r c col raw prev t < 2 ^ k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (chiK_lt k _) (rotK_lt k _ raw)) (c _).isLt

private lemma stateAt_lt {k r : Nat} (c : Nat → Fin (2 ^ k)) (side : Bool)
    (key name : Nat) (hname : name < 2 ^ k) (t : Nat) :
    stateAt k r c side key name t < 2 ^ k := by
  induction t with
  | zero =>
    unfold stateAt
    simpa using Nat.xor_lt_two_pow (rotK_lt k _ key) hname
  | succ t _ =>
    have hs : stateAt k r c side key name (t + 1) =
        stepK k r c side key (stateAt k r c side key name t) (t + 1) := by
      unfold stateAt
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [hs]
    exact stepK_lt k r c side key _ _

private lemma stateAt_zero (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) :
    stateAt k r c side key name 0 = rotK k (if side then 3 else 1) key ^^^ name := rfl

private lemma stateAt_succ (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name t : Nat) :
    stateAt k r c side key name (t + 1) =
      stepK k r c side key (stateAt k r c side key name t) (t + 1) := by
  unfold stateAt
  rw [List.range_succ, List.foldl_append]
  rfl

private lemma stateAt_r_eq {k r : Nat} (hr : 0 < r) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) :
    stateAt k r c side key name r =
      stepK k r c side key (stateAt k r c side key name (r - 1)) r := by
  unfold stateAt
  have hrange : List.range r = List.range (r - 1) ++ [r - 1] := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    exact List.range_succ
  rw [hrange, List.foldl_append]
  dsimp only [List.foldl]
  rw [show r - 1 + 1 = r by omega]

private lemma xor_cancel_mid {a b1 b2 c : Bool} (h : xor (xor a b1) c = xor (xor a b2) c) : b1 = b2 := by
  cases a <;> cases b1 <;> cases b2 <;> cases c <;> simp_all

private lemma testBit_rotK {k : Nat} (hk : 0 < k) (s word : Nat) (hw : word < 2 ^ k) (pos : Nat) :
    (rotK k s word).testBit (pos % k) = word.testBit ((pos + (k - s % k)) % k) := by
  unfold rotK
  have hp : pos % k < k := Nat.mod_lt pos hk
  have hr : s % k < k := Nat.mod_lt s hk
  rw [Nat.testBit_mod_two_pow, decide_eq_true hp, Bool.true_and, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hmod_eq : (pos + (k - s % k)) % k = (pos % k + (k - s % k)) % k := by
    conv_lhs => rw [Nat.add_mod]
    conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
  rw [hmod_eq]
  by_cases hle : s % k ≤ pos % k
  · have hge : k ≤ k - s % k + pos % k := by omega
    have hhi : word.testBit (k - s % k + pos % k) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    rw [hhi, Bool.or_false, decide_eq_true hle, Bool.true_and]
    congr 1
    have : pos % k + (k - s % k) = (pos % k - s % k) + k := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : pos % k - s % k < k)]
  · rw [decide_eq_false hle, Bool.false_and, Bool.false_or]
    congr 1
    have h1 : k - s % k + pos % k = pos % k + (k - s % k) := by omega
    rw [h1, Nat.mod_eq_of_lt (by omega : pos % k + (k - s % k) < k)]

private lemma testBit_chiK {k : Nat} (hk : 0 < k) (word pos : Nat) :
    (chiK k word).testBit (pos % k) =
      xor (word.testBit (pos % k))
        (!(word.testBit ((pos + 1) % k)) && word.testBit ((pos + 2) % k)) := by
  change (foldOr _ k).testBit (pos % k) = _
  have hp : pos % k < k := Nat.mod_lt pos hk
  rw [(foldOr_spec _ k).2 (pos % k)]
  simp only [hp, ↓reduceIte]
  have h1 : (pos % k + 1) % k = (pos + 1) % k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : (pos % k + 2) % k = (pos + 2) % k := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1, h2]

private lemma testBit_mixK {k gap : Nat} (hg0 : 0 < gap) (hgk : gap < k) (v : Nat)
    (hv : v < 2 ^ k) (pos : Nat) :
    (mixK k gap v).testBit (pos % k) =
      xor (xor (v.testBit (pos % k)) (v.testBit ((pos + (k - gap)) % k)))
        (v.testBit ((pos + gap) % k)) := by
  have hk : 0 < k := by omega
  unfold mixK
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotK hk gap v hv pos,
    testBit_rotK hk (k - gap) v hv pos]
  rw [Nat.mod_eq_of_lt hgk, Nat.mod_eq_of_lt (by omega : k - gap < k),
    show k - (k - gap) = gap by omega]

private def AgreeOn (k x y L B : Nat) : Prop :=
  ∀ j : Nat, L ≤ j → j < B → x.testBit (j % k) = y.testBit (j % k)

private lemma agreeOn_mono {k x y L B L' B' : Nat} (hL : L ≤ L') (hB : B' ≤ B)
    (h : AgreeOn k x y L B) : AgreeOn k x y L' B' :=
  fun j hj1 hj2 => h j (le_trans hL hj1) (lt_of_lt_of_le hj2 hB)

private lemma agreeOn_extend_left {k x y L B : Nat}
    (h : AgreeOn k x y (L + 1) B) (hL : x.testBit (L % k) = y.testBit (L % k)) :
    AgreeOn k x y L B := by
  intro j hj1 hj2
  by_cases heq : j = L
  · subst heq; exact hL
  · exact h j (by omega) hj2

private lemma downward_agree {k B : Nat} (x y : Nat) (lo hi : Nat) (hle : lo ≤ hi)
    (hstep : ∀ idx, lo ≤ idx → idx < hi → AgreeOn k x y (idx + 1) B → AgreeOn k x y idx B)
    (hbase : AgreeOn k x y hi B) : AgreeOn k x y lo B := by
  have h : ∀ d, d ≤ hi - lo → AgreeOn k x y (hi - d) B := by
    intro d
    induction d with
    | zero => intro _; simpa using hbase
    | succ d ih =>
      intro hd
      have hp := ih (by omega)
      rw [show hi - d = (hi - (d + 1)) + 1 by omega] at hp
      exact hstep (hi - (d + 1)) (by omega) (by omega) hp
  simpa [Nat.sub_sub_self hle] using h (hi - lo) le_rfl

private lemma agreeOn_xor {k a1 a2 b1 b2 L B : Nat}
    (ha : AgreeOn k a1 a2 L B) (hb : AgreeOn k b1 b2 L B) :
    AgreeOn k (a1 ^^^ b1) (a2 ^^^ b2) L B := by
  intro j hj1 hj2
  rw [Nat.testBit_xor, Nat.testBit_xor, ha j hj1 hj2, hb j hj1 hj2]

private lemma agreeOn_xor_const {k a1 a2 c L B : Nat} (ha : AgreeOn k a1 a2 L B) :
    AgreeOn k (a1 ^^^ c) (a2 ^^^ c) L B := by
  intro j hj1 hj2
  rw [Nat.testBit_xor, Nat.testBit_xor, ha j hj1 hj2]

private lemma agreeOn_rot {k s x y L B : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : AgreeOn k x y L B) :
    AgreeOn k (rotK k s x) (rotK k s y) (L + s % k) (B + s % k) := by
  intro j hj1 hj2
  rw [testBit_rotK hk s x hx j, testBit_rotK hk s y hy j]
  have hr : s % k < k := Nat.mod_lt s hk
  have hsub : (j + (k - s % k)) % k = (j - s % k) % k := by
    have h1 : j + (k - s % k) = (j - s % k) + k := by omega
    rw [h1, Nat.add_mod_right]
  rw [hsub]
  exact h (j - s % k) (by omega) (by omega)

private lemma agreeOn_mix {k gap x y L B : Nat} (hg0 : 0 < gap) (hgk : gap < k)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) (h : AgreeOn k x y L B) :
    AgreeOn k (mixK k gap x) (mixK k gap y) (L + gap) (B - gap) := by
  intro j hj1 hj2
  rw [testBit_mixK hg0 hgk x hx j, testBit_mixK hg0 hgk y hy j]
  have hsub : (j + (k - gap)) % k = (j - gap) % k := by
    have h1 : j + (k - gap) = (j - gap) + k := by omega
    rw [h1, Nat.add_mod_right]
  rw [hsub, h j (by omega) (by omega), h (j - gap) (by omega) (by omega),
    h (j + gap) (by omega) (by omega)]

private lemma agreeOn_chi {k x y L B : Nat} (hk : 0 < k) (h : AgreeOn k x y L B) :
    AgreeOn k (chiK k x) (chiK k y) L (B - 2) := by
  intro j hj1 hj2
  rw [testBit_chiK hk x j, testBit_chiK hk y j,
    h j (by omega) (by omega), h (j + 1) (by omega) (by omega), h (j + 2) (by omega) (by omega)]

private lemma agreeOn_chi_guard {k x y L B : Nat} (hk : 0 < k) (h : AgreeOn k x y L B)
    (hB : 2 ≤ B) (hguard : x.testBit ((B - 1) % k) = true) :
    AgreeOn k (chiK k x) (chiK k y) L (B - 1) := by
  intro j hj1 hj2
  by_cases hlt : j < B - 2
  · exact agreeOn_chi hk h j hj1 hlt
  · have hjeq : j = B - 2 := by omega
    subst hjeq
    rw [testBit_chiK hk x (B - 2), testBit_chiK hk y (B - 2)]
    have h1 : B - 2 + 1 = B - 1 := by omega
    rw [h1, h (B - 2) hj1 (by omega), ← h (B - 1) (by omega) (by omega), hguard]
    simp

private lemma eq_of_agreeOn_full {k x y L B : Nat} (hk : 0 < k)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) (hwidth : k ≤ B - L) (h : AgreeOn k x y L B) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · let d := (j + (k - L % k)) % k
    have hd_lt : d < k := Nat.mod_lt _ hk
    have hmod : (L + d) % k = j := by
      dsimp only [d]
      calc (L + (j + (k - L % k)) % k) % k
          = (L % k + (j + (k - L % k)) % k) % k := by rw [Nat.add_mod, Nat.mod_mod]
        _ = (L % k + (j + (k - L % k))) % k := by
          conv_rhs => rw [Nat.add_mod, Nat.mod_mod]
        _ = j := by
          rw [show L % k + (j + (k - L % k)) = j + k by have := Nat.mod_lt L hk; omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    have heq := h (L + d) (by omega) (by omega)
    rw [hmod] at heq
    exact heq
  · have h1 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega : k ≤ j)))
    have h2 := Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) (by omega : k ≤ j)))
    rw [h1, h2]

private lemma testBit_slice_eq {x y off len : Nat}
    (h : (x >>> off) % 2 ^ len = (y >>> off) % 2 ^ len)
    {j : Nat} (hj1 : off ≤ j) (hj2 : j < off + len) :
    x.testBit j = y.testBit j := by
  have h1 := congrArg (fun n => n.testBit (j - off)) h
  have hjlt : j - off < len := by omega
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    decide_eq_true hjlt, Bool.true_and, Bool.true_and,
    Nat.testBit_shiftRight, Nat.testBit_shiftRight,
    show off + (j - off) = j by omega] at h1
  exact h1

/-! ## Section 2: `history` foldl properties -/

private def histStep (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (ref : Nat)
    (triple : Nat × Nat × Nat) (idx : Nat) : Nat × Nat × Nat :=
  let time := idx + 1
  let place := k - q + 3 * (r - time) + min (q - 1) triple.2.2
  let bit := (mixK k 1 triple.1).testBit ((place + 1) % k)
  let next := stepK k r sched false ref triple.1 time
  if time = 4 then (next, triple.2.1, triple.2.2)
  else (next, 2 * triple.2.1 + bit.toNat, triple.2.2 + bit.toNat)

private def histAt (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (rowVal ref : Nat) (t : Nat) :
    Nat × Nat × Nat :=
  (List.range t).foldl (histStep k r q sched ref) (rotK k 1 ref ^^^ rowVal, 0, 0)

private lemma histAt_succ (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (rowVal ref t : Nat) :
    histAt k r q sched rowVal ref (t + 1) =
      histStep k r q sched ref (histAt k r q sched rowVal ref t) t := by
  unfold histAt
  rw [List.range_succ, List.foldl_append]
  rfl

private lemma histAt_fst (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (rowVal ref t : Nat) :
    (histAt k r q sched rowVal ref t).1 = stateAt k r sched false ref rowVal t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [histAt_succ, stateAt_succ]
    dsimp only [histStep]
    split_ifs <;> dsimp only <;> rw [ih]

private lemma weight_two_mul_add_bit (code n : Nat) (b : Bool) :
    ((List.range (n + 1)).filter (fun jj => (2 * code + b.toNat).testBit jj)).length =
      ((List.range n).filter (fun jj => code.testBit jj)).length + b.toNat := by
  rw [List.range_succ_eq_map, List.filter_cons]
  have h0 : (2 * code + b.toNat).testBit 0 = b := by
    rw [Nat.testBit_zero]
    cases b <;> simp
  have hsucc : ∀ j : Nat, (2 * code + b.toNat).testBit (j + 1) = code.testBit j := by
    intro j
    rw [Nat.testBit_succ]
    have hdiv : (2 * code + b.toNat) / 2 = code := by
      cases b
      · simp
      · simp; omega
    rw [hdiv]
  have hmap : ((List.range n).map (· + 1)).filter (fun jj => (2 * code + b.toNat).testBit jj) =
      ((List.range n).filter (fun jj => code.testBit jj)).map (· + 1) := by
    rw [List.filter_map]
    have hf : ((fun jj => (2 * code + b.toNat).testBit jj) ∘ (· + 1)) = (fun jj => code.testBit jj) :=
      funext hsucc
    rw [hf]
  rw [h0, hmap]
  cases b <;> simp

private lemma histAt_weight (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (rowVal ref t : Nat) :
    let n := if t < 4 then t else t - 1
    ((List.range n).filter (fun jj => (histAt k r q sched rowVal ref t).2.1.testBit jj)).length =
      (histAt k r q sched rowVal ref t).2.2 := by
  induction t with
  | zero => simp [histAt]
  | succ t ih =>
    dsimp only at ih ⊢
    rw [histAt_succ]
    dsimp only [histStep]
    by_cases ht3 : t + 1 = 4
    · have h2 : t < 4 := by omega
      have ht_eq : 3 = t := by omega
      simp only [ht3, h2, ↓reduceIte] at ih ⊢
      simpa [ht_eq] using ih
    · simp only [ht3, ↓reduceIte]
      by_cases htlt : t < 4
      · have ht1lt : t + 1 < 4 := by omega
        simp only [htlt, ht1lt, ↓reduceIte] at ih ⊢
        rw [weight_two_mul_add_bit, ih]
      · have ht1ge : ¬ (t + 1 < 4) := by omega
        simp only [htlt, ht1ge, ↓reduceIte] at ih ⊢
        have hsub : t + 1 - 1 = (t - 1) + 1 := by omega
        rw [hsub, weight_two_mul_add_bit, ih]

private lemma histAt_cnt_le_add (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (rowVal ref t1 t2 : Nat)
    (hle : t1 ≤ t2) :
    (histAt k r q sched rowVal ref t2).2.2 ≤ (histAt k r q sched rowVal ref t1).2.2 + (t2 - t1) := by
  have hbit_le : ∀ b : Bool, b.toNat ≤ 1 := by intro b; cases b <;> decide
  induction t2 with
  | zero =>
    have : t1 = 0 := by omega
    subst this; simp
  | succ t2 ih =>
    by_cases heq : t1 = t2 + 1
    · subst heq; simp
    · have hprev := ih (by omega)
      rw [histAt_succ]
      dsimp only [histStep]
      split_ifs
      · dsimp only; omega
      · dsimp only
        exact le_trans (Nat.add_le_add hprev (hbit_le _)) (by omega)

private lemma histAt_cnt_mono (k r q : Nat) (sched : Nat → Fin (2 ^ k)) (rowVal ref t1 t2 : Nat)
    (hle : t1 ≤ t2) :
    (histAt k r q sched rowVal ref t1).2.2 ≤ (histAt k r q sched rowVal ref t2).2.2 := by
  induction t2 with
  | zero =>
    have : t1 = 0 := by omega
    subst this; exact le_rfl
  | succ t2 ih =>
    by_cases heq : t1 = t2 + 1
    · subst heq; exact le_rfl
    · have hprev := ih (by omega)
      rw [histAt_succ]
      dsimp only [histStep]
      split_ifs <;> dsimp only <;> omega

/-! ## Section 3: Fiber cardinality for `project` -/

private lemma card_project_fiber {k start m : Nat} (hk : 0 < k) (hstart : start < k) (hm : m ≤ k)
    (tag : Fin (2 ^ m)) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
      rotK k (k - start % k) w.val % 2 ^ m = tag.val)).card = 2 ^ (k - m) := by
  let S := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    rotK k (k - start % k) w.val % 2 ^ m = tag.val)
  let mkVec : (Fin (k - m) → Bool) → Fin (2 ^ k) := fun v =>
    ⟨foldOr (fun j =>
      let idx := (j + (k - start)) % k
      if h : idx < m then tag.val.testBit idx
      else if h2 : idx - m < k - m then v ⟨idx - m, h2⟩ else false) k, (foldOr_spec _ k).1⟩
  have hrot_bit : ∀ (w : Fin (2 ^ k)) (i : Nat), i < k →
      (rotK k (k - start % k) w.val).testBit i = w.val.testBit ((i + start) % k) := by
    intro w i hi
    have hst : start % k = start := Nat.mod_eq_of_lt hstart
    rw [hst]
    have h1 := testBit_rotK hk (k - start) w.val w.isLt i
    rw [Nat.mod_eq_of_lt hi] at h1
    by_cases hs0 : start = 0
    · rw [hs0] at h1 ⊢
      simp only [Nat.sub_zero, Nat.mod_self, Nat.add_mod_right, add_zero, Nat.mod_eq_of_lt hi] at h1 ⊢
      exact h1
    · rw [Nat.mod_eq_of_lt (by omega : k - start < k), show k - (k - start) = start by omega] at h1
      exact h1
  let e : ↥S ≃ (Fin (k - m) → Bool) :=
    { toFun := fun ⟨w, _⟩ j => w.val.testBit ((start + m + j.val) % k)
      invFun := fun v =>
        ⟨mkVec v, by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_mod_two_pow]
          by_cases him : i < m
          · rw [decide_eq_true him, Bool.true_and, hrot_bit _ i (by omega)]
            dsimp only [mkVec]
            have hlt : (i + start) % k < k := Nat.mod_lt _ hk
            rw [(foldOr_spec _ k).2 ((i + start) % k)]
            simp only [hlt, ↓reduceIte]
            have hidx : ((i + start) % k + (k - start)) % k = i := by
              rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
                show i + start + (k - start) = i + k by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            simp only [hidx, him, ↓reduceDIte]
          · rw [decide_eq_false him, Bool.false_and]
            symm
            exact Nat.testBit_lt_two_pow
              (lt_of_lt_of_le tag.isLt (Nat.pow_le_pow_right (by omega) (by omega : m ≤ i)))⟩
      left_inv := by
        rintro ⟨w, hw⟩
        have hproj : rotK k (k - start % k) w.val % 2 ^ m = tag.val := (Finset.mem_filter.mp hw).2
        apply Subtype.ext
        apply Fin.ext
        apply Nat.eq_of_testBit_eq
        intro j
        by_cases hjk : j < k
        · dsimp only [mkVec]
          rw [(foldOr_spec _ k).2 j]
          simp only [hjk, ↓reduceIte]
          set idx := (j + (k - start)) % k
          have hidx_lt : idx < k := Nat.mod_lt _ hk
          have hback : (idx + start) % k = j := by
            dsimp only [idx]
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
              show j + (k - start) + start = j + k by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hjk]
          by_cases him : idx < m
          · simp only [him, ↓reduceDIte]
            have ht := congrArg (fun n => n.testBit idx) hproj
            rw [Nat.testBit_mod_two_pow, decide_eq_true him, Bool.true_and,
              hrot_bit w idx hidx_lt, hback] at ht
            exact ht.symm
          · have h2 : idx - m < k - m := by omega
            simp only [him, h2, ↓reduceDIte]
            congr 1
            have hsum : start + m + (idx - m) = idx + start := by omega
            rw [hsum, hback]
        · dsimp only [mkVec]
          rw [(foldOr_spec _ k).2 j]
          simp only [hjk, ↓reduceIte]
          symm
          exact Nat.testBit_lt_two_pow
            (lt_of_lt_of_le w.isLt (Nat.pow_le_pow_right (by omega) (by omega : k ≤ j)))
      right_inv := by
        intro v
        funext j
        dsimp only [mkVec]
        have hlt : (start + m + j.val) % k < k := Nat.mod_lt _ hk
        rw [(foldOr_spec _ k).2 ((start + m + j.val) % k)]
        simp only [hlt, ↓reduceIte]
        have hidx : ((start + m + j.val) % k + (k - start)) % k = m + j.val := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
            show start + m + j.val + (k - start) = (m + j.val) + k by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        have hnot : ¬ (m + j.val < m) := by omega
        have h2 : m + j.val - m < k - m := by omega
        simp only [hidx, hnot, h2, ↓reduceDIte]
        congr 1
        exact Fin.ext (by dsimp only; omega) }
  have hc := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hc
  exact hc

private def colL (idx : Nat) : Nat → Nat
  | 0 => idx + 4
  | 1 => idx + 6
  | t => idx + 3 * t + 2

private lemma col_sweep_step {k r q g start a : Nat}
    (hq : 0 < q) (hqr : q + 2 ≤ r) (h7r : 7 * r + q ≤ k) (hr5 : 5 ≤ r)
    (hmid_eq : start - a = 3 * r - q - 1 + (q + g))
    (hcol_right : 7 * r + q + g ≤ k + 2) (hcol_top : 6 * r + g ≤ k)
    (sched : Nat → Fin (2 ^ k)) (col w1 w2 : Fin (2 ^ k))
    (hcol_eq : (stateAt k r sched true w1.val col.val r >>> (6 * r - q)) % 2 ^ (q + g) =
      (stateAt k r sched true w2.val col.val r >>> (6 * r - q)) % 2 ^ (q + g))
    (idx : Nat) (hidx_lo : 3 * r - q - 1 ≤ idx) (hidx_hi : idx < start - a)
    (hagree : AgreeOn k w1.val w2.val (idx + 1) (k + 3 * r - q - 1)) :
    AgreeOn k w1.val w2.val idx (k + 3 * r - q - 1) := by
  have hk_pos : 0 < k := by omega
  let Bc : Nat → Nat := fun t => k + 3 * r - q + 2 - 4 * t
  have hst : ∀ t : Nat, t ≤ r - 1 →
      AgreeOn k (stateAt k r sched true w1.val col.val t)
        (stateAt k r sched true w2.val col.val t) (colL idx t) (Bc t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [stateAt_zero, stateAt_zero]
      dsimp only [colL, Bc]
      simp only [mul_zero, Nat.sub_zero]
      have hrot := agreeOn_rot (s := 3) hk_pos w1.isLt w2.isLt hagree
      rw [Nat.mod_eq_of_lt (by omega : 3 < k)] at hrot
      exact agreeOn_xor_const (agreeOn_mono (by omega) (by omega) hrot)
    | succ t ih =>
      intro ht_le
      have hprev := ih (by omega)
      have hmix := agreeOn_mix (gap := 2) (by omega) (by omega)
        (stateAt_lt sched true w1.val col.val col.isLt t)
        (stateAt_lt sched true w2.val col.val col.isLt t) hprev
      have hchi := agreeOn_chi hk_pos hmix
      have hL_step : colL idx t + 2 ≤ colL idx (t + 1) := by
        cases t with
        | zero => simp [colL]
        | succ t' =>
          cases t' with
          | zero => simp [colL]
          | succ t'' => simp [colL]; omega
      have hB_step : Bc (t + 1) ≤ Bc t - 2 - 2 := by dsimp only [Bc]; omega
      have hchi_agree := agreeOn_mono hL_step hB_step hchi
      have hkey_L : (idx + 1) + (3 * (t + 1) + 1) % k ≤ colL idx (t + 1) := by
        rw [Nat.mod_eq_of_lt (by omega : 3 * (t + 1) + 1 < k)]
        cases t with
        | zero => simp [colL]
        | succ t' =>
          cases t' with
          | zero => simp [colL]
          | succ t'' => simp [colL]; omega
      have hkey_B : Bc (t + 1) ≤ k + 3 * r - q - 1 + (3 * (t + 1) + 1) % k := by
        rw [Nat.mod_eq_of_lt (by omega : 3 * (t + 1) + 1 < k)]
        dsimp only [Bc]; omega
      have hkey_agree : AgreeOn k (rotK k (3 * (t + 1) + 1) w1.val) (rotK k (3 * (t + 1) + 1) w2.val)
          (colL idx (t + 1)) (Bc (t + 1)) :=
        agreeOn_mono hkey_L hkey_B (agreeOn_rot hk_pos w1.isLt w2.isLt hagree)
      rw [stateAt_succ, stateAt_succ]
      unfold stepK
      simp only [↓reduceIte]
      exact agreeOn_xor_const (agreeOn_xor hchi_agree hkey_agree)
  let p := idx + (3 * r + 1)
  have hp_lo : 6 * r - q ≤ p := by dsimp only [p]; omega
  have hp_hi : p < 6 * r - q + (q + g) := by dsimp only [p]; omega
  have hp_lt_k : p < k := by omega
  have hCr_eq : (stateAt k r sched true w1.val col.val r).testBit p =
      (stateAt k r sched true w2.val col.val r).testBit p :=
    testBit_slice_eq hcol_eq hp_lo hp_hi
  have hprev := hst (r - 1) le_rfl
  have hmix := agreeOn_mix (gap := 2) (by omega) (by omega)
    (stateAt_lt sched true w1.val col.val col.isLt (r - 1))
    (stateAt_lt sched true w2.val col.val col.isLt (r - 1)) hprev
  have hchi := agreeOn_chi hk_pos hmix
  have hL_le : colL idx (r - 1) + 2 ≤ p := by
    have hr2 : r - 1 = (r - 3) + 2 := by omega
    rw [hr2]
    simp [colL, p]
    omega
  have hB_lt : p < Bc (r - 1) - 2 - 2 := by
    dsimp only [Bc, p]; omega
  have hchi_p : (chiK k (mixK k 2 (stateAt k r sched true w1.val col.val (r - 1)))).testBit p =
      (chiK k (mixK k 2 (stateAt k r sched true w2.val col.val (r - 1)))).testBit p := by
    have h := hchi p hL_le hB_lt
    rwa [Nat.mod_eq_of_lt hp_lt_k] at h
  rw [stateAt_r_eq (by omega : 0 < r), stateAt_r_eq (by omega : 0 < r)] at hCr_eq
  unfold stepK at hCr_eq
  simp only [↓reduceIte, Nat.testBit_xor] at hCr_eq
  rw [hchi_p] at hCr_eq
  have hrot_eq : (rotK k (3 * r + 1) w1.val).testBit p =
      (rotK k (3 * r + 1) w2.val).testBit p :=
    xor_cancel_mid hCr_eq
  have hp_mod : p % k = p := Nat.mod_eq_of_lt hp_lt_k
  rw [← hp_mod, testBit_rotK hk_pos (3 * r + 1) w1.val w1.isLt p,
    testBit_rotK hk_pos (3 * r + 1) w2.val w2.isLt p,
    Nat.mod_eq_of_lt (by omega : 3 * r + 1 < k)] at hrot_eq
  have hidx_mod : (p + (k - (3 * r + 1))) % k = idx % k := by
    have h1 : p + (k - (3 * r + 1)) = idx + k := by dsimp only [p]; omega
    rw [h1, Nat.add_mod_right]
  rw [hidx_mod] at hrot_eq
  exact agreeOn_extend_left hagree hrot_eq

private lemma guard_hit_agree {k r q ell : Nat}
    (hq : 0 < q) (hqr : q + 2 ≤ r) (h7r : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5ell : 5 * ell + q ≤ 5 * r + 2)
    (sched : Nat → Fin (2 ^ k)) (row w : Fin (2 ^ k)) (ref : Nat)
    (href_lt : ref < 2 ^ k)
    (hcnt_lt_q : ∀ t ≤ ell, (histAt k r q sched row.val ref t).2.2 < q)
    (hw_ref : AgreeOn k w.val ref (k - (2 * r - 2)) (k + 3 * r - q - 1)) :
    ∀ t : Nat, 1 ≤ t → t ≤ ell → t ≠ 4 →
      (histAt k r q sched row.val ref t).2.2 = (histAt k r q sched row.val ref (t - 1)).2.2 + 1 →
      (mixK k 1 (stateAt k r sched false w.val row.val (t - 1))).testBit
        ((k - q + 3 * (r - t) + (histAt k r q sched row.val ref (t - 1)).2.2 + 1) % k) = true := by
  have hk_pos : 0 < k := by omega
  have hr5 : 5 ≤ r := by omega
  let start := k - (2 * r - 2)
  let cnt : Nat → Nat := fun t => (histAt k r q sched row.val ref t).2.2
  have hcnt_le_id : ∀ m, cnt m ≤ m := by
    intro m
    have h0 := histAt_cnt_le_add k r q sched row.val ref 0 m (Nat.zero_le m)
    change cnt m ≤ 0 + (m - 0) at h0
    omega
  let Lref : Nat → Nat := fun t => if t ≤ 2 then start + t + 1 else start + 2 * t - 2
  let Bref : Nat → Nat := fun t => k - q + 3 * (r - t) + cnt t
  have hstate_agree : ∀ t : Nat, t < ell →
      AgreeOn k (stateAt k r sched false w.val row.val t)
        (stateAt k r sched false ref row.val t) (Lref t) (Bref t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [stateAt_zero, stateAt_zero]
      dsimp only [Lref, Bref, cnt, histAt]
      simp only [Nat.zero_le, ↓reduceIte, add_zero, Nat.sub_zero, List.range_zero, List.foldl_nil]
      have hrot := agreeOn_rot (s := 1) hk_pos w.isLt href_lt hw_ref
      rw [Nat.mod_eq_of_lt (by omega : 1 < k)] at hrot
      have hB : k - q + 3 * r ≤ k + 3 * r - q - 1 + 1 := by omega
      exact agreeOn_xor_const (agreeOn_mono le_rfl hB hrot)
    | succ t ih =>
      intro ht_lt
      have hprev := ih (by omega)
      have hmix := agreeOn_mix (gap := 1) (by omega) (by omega)
        (stateAt_lt sched false w.val row.val row.isLt t)
        (stateAt_lt sched false ref row.val row.isLt t) hprev
      have hL_step : Lref t + 1 ≤ Lref (t + 1) := by dsimp only [Lref]; split_ifs <;> omega
      have hkey_L : start + (2 * t) % k ≤ Lref (t + 1) := by
        have hlt2 : 2 * t < k := by omega
        rw [Nat.mod_eq_of_lt hlt2]
        dsimp only [Lref]; split_ifs <;> omega
      have hkey_B : Bref (t + 1) ≤ k + 3 * r - q - 1 + (2 * t) % k := by
        have hlt2 : 2 * t < k := by omega
        rw [Nat.mod_eq_of_lt hlt2]
        have hc_le : cnt (t + 1) ≤ t + 1 := hcnt_le_id (t + 1)
        dsimp only [Bref]; omega
      have hkey_agree : AgreeOn k (rotK k (2 * t) w.val) (rotK k (2 * t) ref)
          (Lref (t + 1)) (Bref (t + 1)) :=
        agreeOn_mono hkey_L hkey_B (agreeOn_rot hk_pos w.isLt href_lt hw_ref)
      have hchi_agree : AgreeOn k
          (chiK k (mixK k 1 (stateAt k r sched false w.val row.val t)))
          (chiK k (mixK k 1 (stateAt k r sched false ref row.val t)))
          (Lref (t + 1)) (Bref (t + 1)) := by
        have hcnt_step : cnt (t + 1) = cnt t ∨
            (t + 1 ≠ 4 ∧ cnt (t + 1) = cnt t + 1 ∧
              (mixK k 1 (stateAt k r sched false ref row.val t)).testBit
                ((k - q + 3 * (r - (t + 1)) + cnt t + 1) % k) = true) := by
          dsimp only [cnt]
          rw [histAt_succ]
          dsimp only [histStep]
          rw [histAt_fst]
          have hmin : min (q - 1) (histAt k r q sched row.val ref t).2.2 =
              (histAt k r q sched row.val ref t).2.2 := by
            have := hcnt_lt_q t (by omega)
            omega
          rw [hmin]
          by_cases h4 : t + 1 = 4
          · left; simp only [h4, ↓reduceIte]
          · simp only [h4, ↓reduceIte]
            cases hbit : (mixK k 1 (stateAt k r sched false ref row.val t)).testBit
                ((k - q + 3 * (r - (t + 1)) + (histAt k r q sched row.val ref t).2.2 + 1) % k)
            · exact Or.inl rfl
            · exact Or.inr ⟨h4, rfl, rfl⟩
        rcases hcnt_step with hsame | ⟨hnot4, hinc, href_true⟩
        · have hchi := agreeOn_chi hk_pos hmix
          have hB_le : Bref (t + 1) ≤ Bref t - 1 - 2 := by
            dsimp only [Bref]; rw [hsame]; omega
          exact agreeOn_mono hL_step hB_le hchi
        · have hplace_eq : Bref t - 1 - 1 = k - q + 3 * (r - (t + 1)) + cnt t + 1 := by
            dsimp only [Bref]; omega
          have hL_le_place1 : Lref t + 1 ≤ Bref t - 1 - 1 := by
            dsimp only [Lref, Bref, start]; split_ifs <;> omega
          have hw_true : (mixK k 1 (stateAt k r sched false w.val row.val t)).testBit
              ((Bref t - 1 - 1) % k) = true := by
            rw [hmix (Bref t - 1 - 1) hL_le_place1 (by dsimp only [Bref]; omega),
              hplace_eq, href_true]
          have hchi := agreeOn_chi_guard hk_pos hmix (by dsimp only [Bref]; omega) hw_true
          have hB_le : Bref (t + 1) ≤ Bref t - 1 - 1 := by
            dsimp only [Bref]; rw [hinc]; omega
          exact agreeOn_mono hL_step hB_le hchi
      rw [stateAt_succ, stateAt_succ]
      unfold stepK
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
      exact agreeOn_xor_const (agreeOn_xor hchi_agree hkey_agree)
  intro t ht1 htle ht4 hinc
  have hprev := hstate_agree (t - 1) (by omega)
  have hmix := agreeOn_mix (gap := 1) (by omega) (by omega)
    (stateAt_lt sched false w.val row.val row.isLt (t - 1))
    (stateAt_lt sched false ref row.val row.isLt (t - 1)) hprev
  have href_true : (mixK k 1 (stateAt k r sched false ref row.val (t - 1))).testBit
      ((k - q + 3 * (r - t) + cnt (t - 1) + 1) % k) = true := by
    have hstep : cnt t = (histStep k r q sched ref (histAt k r q sched row.val ref (t - 1)) (t - 1)).2.2 := by
      dsimp only [cnt]
      have ht_eq : t = (t - 1) + 1 := by omega
      conv_lhs => rw [ht_eq, histAt_succ]
    change cnt t = cnt (t - 1) + 1 at hinc
    rw [hstep] at hinc
    dsimp only [histStep] at hinc
    have ht_eq : t - 1 + 1 = t := by omega
    rw [ht_eq, histAt_fst] at hinc
    simp only [ht4, ↓reduceIte] at hinc
    have hmin : min (q - 1) (histAt k r q sched row.val ref (t - 1)).2.2 = cnt (t - 1) := by
      have := hcnt_lt_q (t - 1) (by omega)
      dsimp only [cnt]
      omega
    rw [hmin] at hinc
    cases hbit : (mixK k 1 (stateAt k r sched false ref row.val (t - 1))).testBit
        ((k - q + 3 * (r - t) + cnt (t - 1) + 1) % k)
    · rw [hbit] at hinc; dsimp only [cnt] at hinc; simp at hinc
    · rfl
  have hL_le : Lref (t - 1) + 1 ≤ k - q + 3 * (r - t) + cnt (t - 1) + 1 := by
    dsimp only [Lref, start]; split_ifs <;> omega
  have hB_lt : k - q + 3 * (r - t) + cnt (t - 1) + 1 < Bref (t - 1) - 1 := by
    dsimp only [Bref]; omega
  rw [hmix _ hL_le hB_lt, href_true]

private lemma row_sweep_step {k r q ell a hits missed : Nat}
    (hq : 0 < q) (hqr : q + 2 ≤ r) (h7r : 7 * r + q ≤ k)
    (hell5 : 5 ≤ ell) (hellr : ell ≤ r) (h5ell : 5 * ell + q ≤ 5 * r + 2)
    (hmissed_def : missed = q - hits) (hhits : hits < q)
    (sched : Nat → Fin (2 ^ k)) (row w1 w2 : Fin (2 ^ k)) (ref : Nat)
    (href_lt : ref < 2 ^ k)
    (hhits_eq : hits = (histAt k r q sched row.val ref ell).2.2)
    (hcnt_lt_q : ∀ t ≤ ell, (histAt k r q sched row.val ref t).2.2 < q)
    (hw1_ref : AgreeOn k w1.val ref (k - (2 * r - 2)) (k + 3 * r - q - 1))
    (hrow_eq : (stateAt k r sched false w1.val row.val r >>> (k - a)) % 2 ^ (a - missed) =
      (stateAt k r sched false w2.val row.val r >>> (k - a)) % 2 ^ (a - missed))
    (idx : Nat) (hidx_lo : k - (2 * r - 2) - a ≤ idx) (hidx_hi : idx < k - (2 * r - 2) - missed)
    (hagree : AgreeOn k w1.val w2.val (idx + 1) (k + 3 * r - q - 1)) :
    AgreeOn k w1.val w2.val idx (k + 3 * r - q - 1) := by
  have hk_pos : 0 < k := by omega
  have hr5 : 5 ≤ r := by omega
  let cnt : Nat → Nat := fun t => (histAt k r q sched row.val ref t).2.2
  have hcnt_le_id : ∀ m, cnt m ≤ m := by
    intro m
    have h0 := histAt_cnt_le_add k r q sched row.val ref 0 m (Nat.zero_le m)
    change cnt m ≤ 0 + (m - 0) at h0
    omega
  have hguard := guard_hit_agree hq hqr h7r hell5 hellr h5ell sched row w1 ref href_lt hcnt_lt_q hw1_ref
  let L : Nat → Nat := fun t => if t ≤ 2 then (idx + 1) + t + 1 else (idx + 1) + 2 * t - 2
  let B : Nat → Nat := fun t => k - q + 3 * (r - t) + (if t ≤ ell then cnt t else hits)
  have hst : ∀ t : Nat, t ≤ r - 1 →
      AgreeOn k (stateAt k r sched false w1.val row.val t)
        (stateAt k r sched false w2.val row.val t) (L t) (B t) := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [stateAt_zero, stateAt_zero]
      dsimp only [L, B, cnt, histAt]
      simp only [Nat.zero_le, ↓reduceIte, add_zero, Nat.sub_zero, List.range_zero, List.foldl_nil]
      have hrot := agreeOn_rot (s := 1) hk_pos w1.isLt w2.isLt hagree
      rw [Nat.mod_eq_of_lt (by omega : 1 < k)] at hrot
      exact agreeOn_xor_const (agreeOn_mono le_rfl (by omega) hrot)
    | succ t ih =>
      intro ht_le
      have hprev := ih (by omega)
      have hmix := agreeOn_mix (gap := 1) (by omega) (by omega)
        (stateAt_lt sched false w1.val row.val row.isLt t)
        (stateAt_lt sched false w2.val row.val row.isLt t) hprev
      have hL_step : L t + 1 ≤ L (t + 1) := by dsimp only [L]; split_ifs <;> omega
      have hkey_L : (idx + 1) + (2 * t) % k ≤ L (t + 1) := by
        have hlt2 : 2 * t < k := by omega
        rw [Nat.mod_eq_of_lt hlt2]
        dsimp only [L]; split_ifs <;> omega
      have hkey_B : B (t + 1) ≤ k + 3 * r - q - 1 + (2 * t) % k := by
        have hlt2 : 2 * t < k := by omega
        rw [Nat.mod_eq_of_lt hlt2]
        dsimp only [B]
        split_ifs with hle
        · have := hcnt_le_id (t + 1); omega
        · have := hcnt_le_id ell; rw [hhits_eq]; dsimp only [cnt] at this; omega
      have hkey_agree : AgreeOn k (rotK k (2 * t) w1.val) (rotK k (2 * t) w2.val)
          (L (t + 1)) (B (t + 1)) :=
        agreeOn_mono hkey_L hkey_B (agreeOn_rot hk_pos w1.isLt w2.isLt hagree)
      have hchi_agree : AgreeOn k
          (chiK k (mixK k 1 (stateAt k r sched false w1.val row.val t)))
          (chiK k (mixK k 1 (stateAt k r sched false w2.val row.val t)))
          (L (t + 1)) (B (t + 1)) := by
        by_cases htle : t + 1 ≤ ell
        · have ht_le' : t ≤ ell := by omega
          by_cases hhit : t + 1 ≠ 4 ∧ cnt (t + 1) = cnt t + 1
          · rcases hhit with ⟨h4, hinc⟩
            have hguard1 := hguard (t + 1) (by omega) htle h4 hinc
            have hBprev_eq : B t - 1 - 1 = k - q + 3 * (r - (t + 1)) + cnt t + 1 := by
              dsimp only [B]; simp only [ht_le', ↓reduceIte]; omega
            have hchi := agreeOn_chi_guard hk_pos hmix (by dsimp only [B]; omega)
              (by rw [hBprev_eq]; simpa using hguard1)
            have hB_le : B (t + 1) ≤ B t - 1 - 1 := by
              dsimp only [B]; simp only [htle, ht_le', ↓reduceIte]; omega
            exact agreeOn_mono hL_step hB_le hchi
          · have hsame : cnt (t + 1) = cnt t := by
              dsimp only [cnt]
              rw [histAt_succ]
              dsimp only [histStep]
              by_cases h4 : t + 1 = 4
              · simp only [h4, ↓reduceIte]
              · simp only [h4, ↓reduceIte]
                cases hbit : (mixK k 1 (histAt k r q sched row.val ref t).1).testBit _
                · rfl
                · exfalso; apply hhit; refine ⟨h4, ?_⟩
                  dsimp only [cnt]; rw [histAt_succ]; dsimp only [histStep]
                  simp only [h4, ↓reduceIte]
                  rw [hbit]; rfl
            have hchi := agreeOn_chi hk_pos hmix
            have hB_le : B (t + 1) ≤ B t - 1 - 2 := by
              dsimp only [B]; simp only [htle, ht_le', ↓reduceIte]; omega
            exact agreeOn_mono hL_step hB_le hchi
        · have hchi := agreeOn_chi hk_pos hmix
          have hB_le : B (t + 1) ≤ B t - 1 - 2 := by
            dsimp only [B]
            by_cases ht_eq : t = ell
            · subst ht_eq; simp only [htle, le_rfl, ↓reduceIte, hhits_eq]; dsimp only [cnt]; omega
            · have hnot : ¬ (t ≤ ell) := by omega
              simp only [htle, hnot, ↓reduceIte]; omega
          exact agreeOn_mono hL_step hB_le hchi
      rw [stateAt_succ, stateAt_succ]
      unfold stepK
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
      exact agreeOn_xor_const (agreeOn_xor hchi_agree hkey_agree)
  let p := idx + (2 * r - 2)
  have hp_lo : k - a ≤ p := by dsimp only [p]; omega
  have hp_hi : p < k - missed := by dsimp only [p]; omega
  have hp_lt_k : p < k := by omega
  have hSr_eq : (stateAt k r sched false w1.val row.val r).testBit p =
      (stateAt k r sched false w2.val row.val r).testBit p :=
    testBit_slice_eq hrow_eq hp_lo (by omega)
  have hprev := hst (r - 1) le_rfl
  have hmix := agreeOn_mix (gap := 1) (by omega) (by omega)
    (stateAt_lt sched false w1.val row.val row.isLt (r - 1))
    (stateAt_lt sched false w2.val row.val row.isLt (r - 1)) hprev
  have hLr1 : L (r - 1) + 1 = p := by
    dsimp only [L, p]
    have hgt2 : ¬ (r - 1 ≤ 2) := by omega
    simp only [hgt2, ↓reduceIte]
    omega
  have hchi_p : (chiK k (mixK k 1 (stateAt k r sched false w1.val row.val (r - 1)))).testBit p =
      (chiK k (mixK k 1 (stateAt k r sched false w2.val row.val (r - 1)))).testBit p := by
    by_cases hlt : p < B (r - 1) - 1 - 2
    · have h := agreeOn_chi hk_pos hmix p (by omega) hlt
      rwa [Nat.mod_eq_of_lt hp_lt_k] at h
    · have hr_eq_ell : r = ell := by
        dsimp only [B] at hlt
        by_contra hne
        have hnot : ¬ (r - 1 ≤ ell) ∨ r - 1 = ell := by omega
        rcases hnot with h1 | h2
        · simp only [h1, ↓reduceIte] at hlt; omega
        · rw [h2] at hlt; simp only [le_rfl, ↓reduceIte] at hlt
          dsimp only [cnt] at hlt; rw [← hhits_eq] at hlt; omega
      have hinc : cnt r = cnt (r - 1) + 1 := by
        have hr1_le : r - 1 ≤ ell := by omega
        dsimp only [B] at hlt
        simp only [hr1_le, ↓reduceIte] at hlt
        have hle1 := histAt_cnt_le_add k r q sched row.val ref (r - 1) r (by omega)
        rw [← hr_eq_ell] at hhits_eq
        dsimp only [cnt] at hlt ⊢
        omega
      have hguard1 := hguard r (by omega) (by omega) (by omega) hinc
      have hBprev_eq : B (r - 1) - 1 - 1 = k - q + 3 * (r - r) + cnt (r - 1) + 1 := by
        dsimp only [B]; simp only [show r - 1 ≤ ell by omega, ↓reduceIte]; omega
      have hchi := agreeOn_chi_guard hk_pos hmix (by dsimp only [B]; omega)
        (by rw [hBprev_eq]; simpa using hguard1)
      have hp_lt_guard : p < B (r - 1) - 1 - 1 := by
        dsimp only [B]; simp only [show r - 1 ≤ ell by omega, ↓reduceIte]
        dsimp only [cnt]; rw [← hr_eq_ell] at hhits_eq; omega
      have h := hchi p (by omega) hp_lt_guard
      rwa [Nat.mod_eq_of_lt hp_lt_k] at h
  rw [stateAt_r_eq (by omega : 0 < r), stateAt_r_eq (by omega : 0 < r)] at hSr_eq
  unfold stepK at hSr_eq
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.testBit_xor] at hSr_eq
  rw [hchi_p] at hSr_eq
  have hrot_eq : (rotK k (2 * (r - 1)) w1.val).testBit p = (rotK k (2 * (r - 1)) w2.val).testBit p :=
    xor_cancel_mid hSr_eq
  have hp_mod : p % k = p := Nat.mod_eq_of_lt hp_lt_k
  rw [← hp_mod, testBit_rotK hk_pos (2 * (r - 1)) w1.val w1.isLt p,
    testBit_rotK hk_pos (2 * (r - 1)) w2.val w2.isLt p,
    Nat.mod_eq_of_lt (by omega : 2 * (r - 1) < k)] at hrot_eq
  have hidx_mod : (p + (k - 2 * (r - 1))) % k = idx % k := by
    have h1 : p + (k - 2 * (r - 1)) = idx + k := by dsimp only [p]; omega
    rw [h1, Nat.add_mod_right]
  rw [hidx_mod] at hrot_eq
  exact agreeOn_extend_left hagree hrot_eq

end PEqualNP.Outside.L_meta_25729_aux

open PEqualNP.Outside.L_meta_25729_aux

theorem PEqualNP.Outside.L_meta_25729 :
    ∀ (k r q ell : Nat), 0 < q → q + 2 ≤ r → 7 * r + q ≤ k → k - (k + 1) / 2 + q ≤ 6 * r →
      5 ≤ ell → ell ≤ r → 5 * ell + q ≤ 5 * r + 2 →
      let h := (k + 1) / 2
      let z := k - h
      let u := 5 * r - 3
      let tries := ell - 1
      let rot := fun (offset x : Nat) =>
        ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k
      let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k - gap) value
      let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
        acc ||| ((xor (word.testBit site)
          (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0
      let step := fun (constants : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) =>
        chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
          (constants (if col then r + t else t)).val
      let state := fun (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) =>
        (List.range r).foldl (fun v tick => step c side key v (tick + 1))
          (rot (if side then 3 else 1) key ^^^ name)
      let start := k - (2 * r - 2)
      let a := min h (k - u)
      let g := z - u
      let project := fun (wordAt : Nat) => rot (k - (start % k)) wordAt % 2 ^ (u - q)
      let weight := fun (code : Nat) => ((List.range tries).filter (fun jj => code.testBit jj)).length
      ∀ (sched : Nat → Fin (2 ^ k)) (row col : Fin (2 ^ k)),
        let history := fun (label : Nat) =>
          let ref := rot start label
          let init : Nat × Nat × Nat := (rot 1 ref ^^^ row.val, 0, 0)
          let final := (List.range ell).foldl (fun triple idx =>
            let time := idx + 1
            let place := k - q + 3 * (r - time) + min (q - 1) triple.2.2
            let bit := (mix 1 triple.1).testBit ((place + 1) % k)
            let next := step sched false ref triple.1 time
            if time = 4 then (next, triple.2.1, triple.2.2)
            else (next, 2 * triple.2.1 + bit.toNat, triple.2.2 + bit.toNat)) init
          final.2.1
        ∀ tag : Fin (2 ^ (u - q)),
          let hits := weight (history tag.val)
          hits < q →
          let missed := q - hits
          ∀ (spare : Fin (2 ^ missed)) (rowPart : Fin (2 ^ (a - missed)))
            (columnPart : Fin (2 ^ (q + g))),
            ∃! w : Fin (2 ^ k), project w.val = tag.val ∧
              (w.val >>> (start - missed)) % 2 ^ missed = spare.val ∧
              (state sched false w.val row.val >>> (k - a)) % 2 ^ (a - missed) = rowPart.val ∧
              (state sched true w.val col.val >>> (6 * r - q)) % 2 ^ (q + g) = columnPart.val := by
  intro k r q ell hq hqr h7r h6r hell5 hellr h5ell
    h z u tries rot mix chi step state start a g project weight
    sched row col history tag hits hhits missed
  have hr5 : 5 ≤ r := by omega
  have hk_pos : 0 < k := by omega
  have hstart_lt : start < k := by dsimp only [start]; omega
  have hstart_pos : 0 < start := by dsimp only [start]; omega
  have huq_le : u - q ≤ k := by dsimp only [u]; omega
  have ha_ge : q < a := by dsimp only [a, h, u]; omega
  have hmissed_pos : 1 ≤ missed := by dsimp only [missed]; omega
  have hmissed_le_q : missed ≤ q := by dsimp only [missed]; omega
  have htotal_bits : missed + (a - missed) + (q + g) = k - (u - q) := by
    dsimp only [a, g, h, z, u]
    omega
  have hmid_eq : start - a = 3 * r - q - 1 + (q + g) := by
    dsimp only [start, a, g, h, z, u]
    omega
  have ha_le_start : a ≤ start := by dsimp only [start, a, h, u]; omega
  have hcol_right : 7 * r + q + g ≤ k + 2 := by
    dsimp only [g, z, h, u]
    omega
  have hcol_top : 6 * r + g ≤ k := by
    dsimp only [g, z, h, u]
    omega
  -- Bridge history with histAt
  let ref : Nat := rotK k start tag.val
  have href_lt : ref < 2 ^ k := rotK_lt k start tag.val
  have hhist_eq : history tag.val = (histAt k r q sched row.val ref ell).2.1 := rfl
  let cnt : Nat → Nat := fun t => (histAt k r q sched row.val ref t).2.2
  have hhits_eq : hits = cnt ell := by
    change weight (history tag.val) = cnt ell
    rw [hhist_eq]
    have hw := histAt_weight k r q sched row.val ref ell
    have hnot4 : ¬ (ell < 4) := by omega
    simp only [hnot4, ↓reduceIte] at hw
    exact hw
  have hcnt_le_id : ∀ m, cnt m ≤ m := by
    intro m
    have h0 := histAt_cnt_le_add k r q sched row.val ref 0 m (Nat.zero_le m)
    change cnt m ≤ 0 + (m - 0) at h0
    omega
  have hcnt_lt_q : ∀ t ≤ ell, cnt t < q := by
    intro t ht
    have hmono := histAt_cnt_mono k r q sched row.val ref t ell ht
    dsimp only [cnt] at hhits_eq ⊢
    omega
  -- Helper: any w with project w = tag agrees with ref on [start, k + 3*r - q - 1)
  have hproj_agree : ∀ w : Fin (2 ^ k), project w.val = tag.val →
      AgreeOn k w.val ref start (k + 3 * r - q - 1) := by
    intro w hw j hj1 hj2
    have hlen : j - start < u - q := by dsimp only [start, u] at *; omega
    have hproj_bit : (rotK k (k - start % k) w.val).testBit (j - start) = tag.val.testBit (j - start) := by
      have h1 := congrArg (fun n => n.testBit (j - start)) hw
      change ((rotK k (k - start % k) w.val) % 2 ^ (u - q)).testBit (j - start) =
        tag.val.testBit (j - start) at h1
      rw [Nat.testBit_mod_two_pow, decide_eq_true hlen, Bool.true_and] at h1
      exact h1
    have hw_rot : (rotK k (k - start % k) w.val).testBit (j - start) = w.val.testBit (j % k) := by
      have hst : start % k = start := Nat.mod_eq_of_lt hstart_lt
      rw [hst]
      have h1 := testBit_rotK hk_pos (k - start) w.val w.isLt (j - start)
      rw [Nat.mod_eq_of_lt (by omega : j - start < k),
        Nat.mod_eq_of_lt (by omega : k - start < k), show k - (k - start) = start by omega,
        show j - start + start = j by omega] at h1
      exact h1
    have href_bit : ref.testBit (j % k) = tag.val.testBit (j - start) := by
      dsimp only [ref]
      have htag_lt : tag.val < 2 ^ k :=
        lt_of_lt_of_le tag.isLt (Nat.pow_le_pow_right (by omega) huq_le)
      rw [testBit_rotK hk_pos start tag.val htag_lt j, Nat.mod_eq_of_lt hstart_lt]
      have hsub : (j + (k - start)) % k = j - start := by
        have h1 : j + (k - start) = (j - start) + k := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hsub]
    rw [← hw_rot, hproj_bit, href_bit]
  -- Combine sweeps into injectivity on the tag-fiber, then apply Pigeonhole
  let Fib : Finset (Fin (2 ^ k)) := (Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
    project w.val = tag.val)
  let Target := Fin (2 ^ missed) × Fin (2 ^ (a - missed)) × Fin (2 ^ (q + g))
  let eval : ↥Fib → Target := fun ⟨w, _⟩ =>
    (⟨(w.val >>> (start - missed)) % 2 ^ missed, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
     ⟨(state sched false w.val row.val >>> (k - a)) % 2 ^ (a - missed), Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
     ⟨(state sched true w.val col.val >>> (6 * r - q)) % 2 ^ (q + g), Nat.mod_lt _ (Nat.two_pow_pos _)⟩)
  have heval_inj : Function.Injective eval := by
    rintro ⟨w1, hw1⟩ ⟨w2, hw2⟩ heq
    apply Subtype.ext
    have hp1 : project w1.val = tag.val := (Finset.mem_filter.mp hw1).2
    have hp2 : project w2.val = tag.val := (Finset.mem_filter.mp hw2).2
    have hsp : (w1.val >>> (start - missed)) % 2 ^ missed =
        (w2.val >>> (start - missed)) % 2 ^ missed :=
      congrArg (fun x => x.1.val) heq
    have hrw : (state sched false w1.val row.val >>> (k - a)) % 2 ^ (a - missed) =
        (state sched false w2.val row.val >>> (k - a)) % 2 ^ (a - missed) :=
      congrArg (fun x => x.2.1.val) heq
    have hcl : (state sched true w1.val col.val >>> (6 * r - q)) % 2 ^ (q + g) =
        (state sched true w2.val col.val >>> (6 * r - q)) % 2 ^ (q + g) :=
      congrArg (fun x => x.2.2.val) heq
    -- Initial agreement from tag + spare on [start - missed, k + 3*r - q - 1)
    have hinit : AgreeOn k w1.val w2.val (start - missed) (k + 3 * r - q - 1) := by
      intro j hj1 hj2
      by_cases hjs : j < start
      · have hbit := testBit_slice_eq hsp hj1 (by omega)
        rwa [Nat.mod_eq_of_lt (by omega : j < k)]
      · exact (hproj_agree w1 hp1 j (by omega) hj2).trans (hproj_agree w2 hp2 j (by omega) hj2).symm
    -- Downward induction across row unknowns [start - a, start - missed)
    have hafter_row : AgreeOn k w1.val w2.val (start - a) (k + 3 * r - q - 1) :=
      downward_agree w1.val w2.val (start - a) (start - missed) (by omega)
        (row_sweep_step hq hqr h7r hell5 hellr h5ell rfl hhits sched row w1 w2 ref href_lt
          hhits_eq hcnt_lt_q (hproj_agree w1 hp1) hrw) hinit
    -- Downward induction across column unknowns [3*r - q - 1, start - a)
    have hfull : AgreeOn k w1.val w2.val (3 * r - q - 1) (k + 3 * r - q - 1) :=
      downward_agree w1.val w2.val (3 * r - q - 1) (start - a) (by omega)
        (col_sweep_step hq hqr h7r hr5 hmid_eq hcol_right hcol_top sched col w1 w2 hcl) hafter_row
    exact Fin.ext (eq_of_agreeOn_full hk_pos w1.isLt w2.isLt (by omega) hfull)
  have hcard_eq : Fintype.card ↥Fib = Fintype.card Target := by
    rw [Fintype.card_coe]
    change ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w =>
      rotK k (k - start % k) w.val % 2 ^ (u - q) = tag.val)).card = Fintype.card Target
    rw [card_project_fiber hk_pos hstart_lt huq_le tag]
    dsimp only [Target]
    simp only [Fintype.card_prod, Fintype.card_fin, ← Nat.pow_add]
    rw [← Nat.add_assoc, htotal_bits]
  have heval_bij : Function.Bijective eval :=
    (Fintype.bijective_iff_injective_and_card eval).mpr ⟨heval_inj, hcard_eq⟩
  intro spare rowPart columnPart
  obtain ⟨⟨w, hw⟩, hweq⟩ := heval_bij.2 (spare, rowPart, columnPart)
  refine ⟨w, ⟨(Finset.mem_filter.mp hw).2,
    congrArg (fun x => x.1.val) hweq,
    congrArg (fun x => x.2.1.val) hweq,
    congrArg (fun x => x.2.2.val) hweq⟩, ?_⟩
  intro w' ⟨hp', hsp', hrw', hcl'⟩
  have hw' : w' ∈ Fib := Finset.mem_filter.mpr ⟨Finset.mem_univ w', hp'⟩
  have heq : eval ⟨w', hw'⟩ = eval ⟨w, hw⟩ := by
    rw [hweq]
    exact Prod.ext (Fin.ext hsp') (Prod.ext (Fin.ext hrw') (Fin.ext hcl'))
  have hsub : (⟨w', hw'⟩ : ↥Fib) = ⟨w, hw⟩ := heval_inj heq
  exact congrArg Subtype.val hsub
