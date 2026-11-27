import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25525_aux

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepBit (k word j : Nat) : Bool :=
  xor (word.testBit j) (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

def stateAt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) : Nat :=
  (List.range rounds).foldl (fun prev t =>
    step k (mix k prev) ^^^ rot k (2 * t) key ^^^ (constant (t + 1)).val) (rot k 1 key ^^^ u.val)

theorem stateAt_zero (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (key : Nat) :
    stateAt k u constant 0 key = rot k 1 key ^^^ u.val := rfl

theorem stateAt_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (t key : Nat) :
    stateAt k u constant (t + 1) key =
      step k (mix k (stateAt k u constant t key)) ^^^ rot k (2 * t) key ^^^ (constant (t + 1)).val := by
  simp [stateAt, List.range_succ]

theorem rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

theorem xor_lt {k a b : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) : a ^^^ b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  have hpow := Nat.pow_le_pow_right Nat.zero_lt_two hj
  simp [Nat.testBit_xor, Nat.testBit_lt_two_pow (ha.trans_le hpow),
    Nat.testBit_lt_two_pow (hb.trans_le hpow)]

theorem testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
    (rot k s word).testBit b = word.testBit ((b + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hs : s % k < k := Nat.mod_lt _ hk
  simp only [rot, Nat.testBit_mod_two_pow, hb, decide_true, Bool.true_and,
    Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  by_cases h : s % k ≤ b
  · have hz : word.testBit (k - s % k + b) = false :=
      Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
    have he : (b + k - s % k) % k = b - s % k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, hz, he]
  · have he : (b + k - s % k) % k = k - s % k + b := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    simp [h, he]

theorem testBit_foldl_or (p : Nat → Bool) (xs : List Nat) (acc i : Nat) :
    (xs.foldl (fun a j => a ||| ((p j).toNat <<< j)) acc).testBit i =
      (acc.testBit i || (decide (i ∈ xs) && p i)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j xs ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft]
    by_cases hji : j = i
    · subst j
      cases p i <;> simp
    · by_cases hle : j ≤ i
      · have hsub : 1 ≤ i - j := by omega
        have hbt : (p j).toNat.testBit (i - j) = false := by
          cases p j
          · simp
          · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
        simp [hle, hbt, Ne.symm hji]
      · simp [hle, Ne.symm hji]

theorem testBit_step_all (k word b : Nat) :
    (step k word).testBit b = (decide (b < k) && stepBit k word b) := by
  unfold step stepBit
  rw [testBit_foldl_or]
  simp

theorem testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b = stepBit k word b := by
  simp [testBit_step_all, hb]

theorem step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  simp [testBit_step_all, Nat.not_lt_of_ge hb]

theorem stateAt_lt (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (rounds key : Nat) :
    stateAt k u constant rounds key < 2 ^ k := by
  cases rounds with
  | zero => exact xor_lt (rot_lt k 1 key) u.isLt
  | succ t =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (t + 1)).isLt

theorem testBit_mix {k word b : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
    (mix k word).testBit b =
      xor (xor (word.testBit b) (word.testBit ((b + k - 1) % k)))
        (word.testBit ((b + 1) % k)) := by
  unfold mix
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot hw hb, testBit_rot hw hb]
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have h3 : (b + k - (k - 1)) % k = (b + 1) % k := by congr 1; omega
  rw [h3]

theorem mod_sub_eq {k p s : Nat} (hk : 0 < k) (hsp : s ≤ p) :
    (p % k + k - s % k) % k = (p - s) % k := by
  have hdiv : p - s + s = p := Nat.sub_add_cancel hsp
  have h1 : (p % k + k - s % k + s % k) % k = p % k := by
    have hlt : s % k < k := Nat.mod_lt s hk
    have hadd : p % k + k - s % k + s % k = p % k + k := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_mod]
  have h2 : ((p - s) % k + s % k) % k = p % k := by
    rw [Nat.mod_add_mod, Nat.add_mod_mod, hdiv]
  set A := (p % k + k - s % k) % k
  set B := (p - s) % k
  set C := s % k
  have ha : A < k := Nat.mod_lt _ hk
  have hb : B < k := Nat.mod_lt _ hk
  have hs : C < k := Nat.mod_lt s hk
  have h3 : (A + C) % k = (B + C) % k := by
    rw [Nat.mod_add_mod, h1, ← h2]
  by_cases h1lt : A + C < k <;> by_cases h2lt : B + C < k
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2lt] at h3; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h3; omega

def lineStep (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (src : Nat → Bool) : Nat → Nat → Bool
  | 0, p => src p
  | s + 1, p =>
    let prev := lineStep k u constant src s
    let m0 := xor (xor (prev p) (prev (p - 1))) (prev (p + 1))
    let m1 := xor (xor (prev (p + 1)) (prev p)) (prev (p + 2))
    let m2 := xor (xor (prev (p + 2)) (prev (p + 1))) (prev (p + 3))
    let st := xor m0 (!m1 && m2)
    let inj := xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k))
    xor (xor st inj) ((constant (s + 1)).val.testBit (p % k))

theorem lineStep_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (src : Nat → Bool) (s p : Nat) :
    lineStep k u constant src (s + 1) p =
      xor (xor (xor (xor (xor (lineStep k u constant src s p) (lineStep k u constant src s (p - 1)))
          (lineStep k u constant src s (p + 1)))
        (!(xor (xor (lineStep k u constant src s (p + 1)) (lineStep k u constant src s p))
          (lineStep k u constant src s (p + 2))) &&
         (xor (xor (lineStep k u constant src s (p + 2)) (lineStep k u constant src s (p + 1)))
          (lineStep k u constant src s (p + 3)))))
        (xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k))))
        ((constant (s + 1)).val.testBit (p % k)) := rfl

theorem lineStep_eq_stateAt {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (key : Fin (2 ^ k)) :
    let src := fun pos : Nat => (rot k 1 key.val ^^^ u.val).testBit (pos % k)
    ∀ s p, 2 * s ≤ p → lineStep k u constant src s p = (stateAt k u constant s key.val).testBit (p % k) := by
  intro src s
  have hk_pos : 0 < k := by omega
  induction s with
  | zero =>
    intro p _
    rfl
  | succ s ih =>
    intro p hp
    simp only [lineStep]
    rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk_pos)]
    unfold stepBit
    have hm : ∀ d, (mix k (stateAt k u constant s key.val)).testBit ((p % k + d) % k) =
        xor (xor (lineStep k u constant src s (p + d))
                 (lineStep k u constant src s (p + d - 1)))
            (lineStep k u constant src s (p + d + 1)) := by
      intro d
      have hlt : (p % k + d) % k < k := Nat.mod_lt _ hk_pos
      rw [testBit_mix hk (stateAt_lt k u constant s key.val) hlt]
      have h0 : (p % k + d) % k = (p + d) % k := Nat.mod_add_mod p k d
      have h1 : ((p + d) % k + k - 1) % k = (p + d - 1) % k := by
        have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
        conv_lhs => rw [h1m]
        exact mod_sub_eq hk_pos (by omega)
      have h2 : ((p + d) % k + 1) % k = (p + d + 1) % k := Nat.mod_add_mod (p + d) k 1
      rw [h0, h1, h2, ih (p + d) (by omega), ih (p + d - 1) (by omega), ih (p + d + 1) (by omega)]
    have hm0 := hm 0
    simp only [Nat.add_zero, Nat.mod_mod] at hm0
    have hm1 := hm 1
    have hm2 := hm 2
    have he1 : p + 1 - 1 = p := by omega
    have he2 : p + 2 - 1 = p + 1 := by omega
    have he3 : p + 1 + 1 = p + 2 := by omega
    have he4 : p + 2 + 1 = p + 3 := by omega
    rw [he1, he3] at hm1
    rw [he2, he4] at hm2
    rw [hm0, hm1, hm2]
    have hinj : xor (src (p + 1 - 2 * s)) (u.val.testBit ((p + 1 - 2 * s) % k)) =
        (rot k (2 * s) key.val).testBit (p % k) := by
      simp only [src, Nat.testBit_xor]
      have hrot1 : (rot k 1 key.val).testBit ((p + 1 - 2 * s) % k) =
          key.val.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot key.isLt (Nat.mod_lt _ hk_pos)]
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hsub : p + 1 - 2 * s - 1 = p - 2 * s := by omega
        rw [← hsub]
        have h1' := mod_sub_eq hk_pos (p := p + 1 - 2 * s) (s := 1) (by omega)
        rw [h1m] at h1' ⊢
        exact congrArg key.val.testBit h1'
      have hrot2 : (rot k (2 * s) key.val).testBit (p % k) =
          key.val.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot key.isLt (Nat.mod_lt _ hk_pos), mod_sub_eq hk_pos (by omega)]
      rw [hrot1, hrot2]
      cases key.val.testBit ((p - 2 * s) % k) <;> cases u.val.testBit ((p + 1 - 2 * s) % k) <;> rfl
    rw [hinj]

def traceRun (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (q len key : Nat) : Nat × Nat :=
  (List.range len).foldl (fun (posCode : Nat × Nat) idx =>
    let pos := posCode.1 - 2
    let prev := stateAt k u constant (idx + 4) key
    let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
      (prev.testBit ((pos + 2) % k))
    (pos - (if hit then 0 else 1), posCode.2 ||| (hit.toNat <<< idx)))
    (q - 13, 0)

theorem traceRun_spec {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (q : Nat) (key : Fin (2 ^ k)) :
    let src := fun pos : Nat => (rot k 1 key.val ^^^ u.val).testBit (pos % k)
    let trunc := fun pos : Nat => if pos < q then src pos else false
    ∀ (len : Nat), 3 * len + 16 ≤ q →
      let tr := traceRun k u constant q len key.val
      let ones := ((List.range len).filter (fun digit => tr.2.testBit digit)).length
      tr.1 = q + ones - 3 * (len + 4) - 1 ∧
      (∀ d, len ≤ d → tr.2.testBit d = false) ∧
      (∀ p, 2 * (len + 4) ≤ p → p ≤ tr.1 →
        lineStep k u constant src (len + 4) p = lineStep k u constant trunc (len + 4) p) := by
  intro src trunc len
  induction len with
  | zero =>
    intro hq
    refine ⟨by simp [traceRun]; omega, fun d _ => by simp [traceRun], ?_⟩
    have h4 : ∀ s, s ≤ 4 → ∀ p, 2 * s ≤ p → p ≤ q - 1 - 3 * s →
        lineStep k u constant src s p = lineStep k u constant trunc s p := by
      intro s
      induction s with
      | zero =>
        intro _ p _ hp
        simp only [lineStep, trunc]
        rw [if_pos (by omega)]
      | succ s ih =>
        intro hs p hp1 hp2
        simp only [lineStep]
        have h0 := ih (by omega) (p - 1) (by omega) (by omega)
        have h1 := ih (by omega) p (by omega) (by omega)
        have h2 := ih (by omega) (p + 1) (by omega) (by omega)
        have h3 := ih (by omega) (p + 2) (by omega) (by omega)
        have h4' := ih (by omega) (p + 3) (by omega) (by omega)
        have hsrc : trunc (p + 1 - 2 * s) = src (p + 1 - 2 * s) := by
          simp only [trunc]; rw [if_pos (by omega)]
        rw [h0, h1, h2, h3, h4', hsrc]
    intro p hp1 hp2
    exact h4 4 (by omega) p hp1 (by simp only [traceRun, List.range_zero, List.foldl_nil] at hp2; omega)
  | succ len ih =>
    intro hq
    rcases ih (by omega) with ⟨hpos_prev, hhi_prev, hagree_prev⟩
    set tr0 := traceRun k u constant q len key.val with htr0
    have hstep_tr : traceRun k u constant q (len + 1) key.val =
        let pos := tr0.1 - 2
        let prev := stateAt k u constant (len + 4) key.val
        let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
          (prev.testBit ((pos + 2) % k))
        (pos - (if hit then 0 else 1), tr0.2 ||| (hit.toNat <<< len)) := by
      simp [traceRun, List.range_succ, htr0]
    let pos := tr0.1 - 2
    let prev := stateAt k u constant (len + 4) key.val
    let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
      (prev.testBit ((pos + 2) % k))
    have htr1_1 : (traceRun k u constant q (len + 1) key.val).1 = pos - (if hit then 0 else 1) := by
      rw [hstep_tr]
    have htr1_2 : (traceRun k u constant q (len + 1) key.val).2 = tr0.2 ||| (hit.toNat <<< len) := by
      rw [hstep_tr]
    have hbit_new : ∀ d, (traceRun k u constant q (len + 1) key.val).2.testBit d =
        if d = len then hit else tr0.2.testBit d := by
      intro d
      rw [htr1_2, Nat.testBit_or, Nat.testBit_shiftLeft]
      by_cases hd : d = len
      · subst hd
        rw [if_pos rfl, hhi_prev d (le_refl _)]
        cases hit <;> simp
      · rw [if_neg hd]
        by_cases hle : len ≤ d
        · have hsub : 1 ≤ d - len := by omega
          have hbt : hit.toNat.testBit (d - len) = false := by
            cases hit
            · simp
            · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
                (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
          simp [hle, hbt]
        · simp [hle]
    have hones_succ : ((List.range (len + 1)).filter
        (fun digit => (traceRun k u constant q (len + 1) key.val).2.testBit digit)).length =
        ((List.range len).filter (fun digit => tr0.2.testBit digit)).length + hit.toNat := by
      rw [List.range_succ, List.filter_append, List.length_append]
      have hflt_prev : (List.range len).filter
          (fun digit => (traceRun k u constant q (len + 1) key.val).2.testBit digit) =
          (List.range len).filter (fun digit => tr0.2.testBit digit) := by
        apply List.filter_congr
        intro d hd
        have hdlt : d < len := List.mem_range.1 hd
        rw [hbit_new d, if_neg (by omega)]
      rw [hflt_prev]
      simp only [List.filter_cons, List.filter_nil, hbit_new len, ↓reduceIte]
      cases hit <;> simp
    have hones_le : ((List.range len).filter (fun digit => tr0.2.testBit digit)).length ≤ len := by
      have := List.length_filter_le (fun digit => tr0.2.testBit digit) (List.range len)
      simpa using this
    refine ⟨?_, ?_, ?_⟩
    · rw [htr1_1, hones_succ]
      simp only [pos]
      cases hit <;> simp <;> omega
    · intro d hd
      rw [hbit_new d, if_neg (by omega)]
      exact hhi_prev d (by omega)
    · intro p hp1 hp2
      rw [htr1_1] at hp2
      have hpos_ge : 2 * (len + 4) + 2 ≤ tr0.1 := by omega
      have htr0_le_q : tr0.1 < q := by omega
      have hsrc_inj : trunc (p + 1 - 2 * (len + 4)) = src (p + 1 - 2 * (len + 4)) := by
        simp only [trunc]; rw [if_pos (by omega)]
      have hstep_eq : len + 1 + 4 = (len + 4) + 1 := by omega
      rw [hstep_eq, lineStep_succ k u constant src (len + 4) p, lineStep_succ k u constant trunc (len + 4) p]
      rw [hsrc_inj]
      by_cases hlt : p + 3 ≤ tr0.1
      · have h0 := hagree_prev (p - 1) (by omega) (by omega)
        have h1 := hagree_prev p (by omega) (by omega)
        have h2 := hagree_prev (p + 1) (by omega) (by omega)
        have h3 := hagree_prev (p + 2) (by omega) (by omega)
        have h4 := hagree_prev (p + 3) (by omega) (by omega)
        rw [h0, h1, h2, h3, h4]
      · have hhit_true : hit = true := by
          cases hh : hit
          · rw [hh] at hp2; simp only [Bool.false_eq_true, ↓reduceIte, pos] at hp2; omega
          · rfl
        have hp_eq : p = pos := by
          rw [hhit_true] at hp2; simp only [↓reduceIte, Nat.sub_zero, pos] at hp2 ⊢; omega
        have h0 := hagree_prev (p - 1) (by omega) (by omega)
        have h1 := hagree_prev p (by omega) (by omega)
        have h2 := hagree_prev (p + 1) (by omega) (by omega)
        have h3 := hagree_prev (p + 2) (by omega) (by omega)
        have hm1_true : xor (xor (lineStep k u constant src (len + 4) (p + 1))
            (lineStep k u constant src (len + 4) p))
            (lineStep k u constant src (len + 4) (p + 2)) = true := by
          rw [lineStep_eq_stateAt hk u constant key (len + 4) (p + 1) (by omega),
              lineStep_eq_stateAt hk u constant key (len + 4) p (by omega),
              lineStep_eq_stateAt hk u constant key (len + 4) (p + 2) (by omega)]
          have : hit = true := hhit_true
          simp only [hit, prev, ← hp_eq] at this
          rw [← this]
          cases (stateAt k u constant (len + 4) key.val).testBit (p % k) <;>
          cases (stateAt k u constant (len + 4) key.val).testBit ((p + 1) % k) <;>
          cases (stateAt k u constant (len + 4) key.val).testBit ((p + 2) % k) <;> rfl
        rw [h1, h2, h3] at hm1_true
        rw [h0, h1, h2, h3, hm1_true]
        simp

theorem lineStep_agree_right (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (L : Nat) (hfg : ∀ p, L < p → f p = g p) :
    ∀ s p, max (L + s + 1) (L + 2 * s - 2) ≤ p →
      lineStep k u constant f s p = lineStep k u constant g s p := by
  intro s
  induction s with
  | zero =>
    intro p hp
    simp only [lineStep]
    exact hfg p (by omega)
  | succ s ih =>
    intro p hp
    simp only [lineStep]
    have h0 := ih (p - 1) (by omega)
    have h1 := ih p (by omega)
    have h2 := ih (p + 1) (by omega)
    have h3 := ih (p + 2) (by omega)
    have h4 := ih (p + 3) (by omega)
    have hi := hfg (p + 1 - 2 * s) (by omega)
    rw [h0, h1, h2, h3, h4, hi]

theorem main (k r d i : Nat) (hr : 6 ≤ r) (hk : k + 3 + d = 5 * r)
    (hdn : d ≤ r - 5) (hik : i < k) (hind : i + (r - 5 - d) ≤ k)
    (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (len : Nat) (code : Fin (2 ^ len)) (hlen : len < r - 5)
    (hreach : d < ((List.range len).filter (fun digit => code.val.testBit digit)).length + (r - 5 - len))
    (a z : Fin (2 ^ k)) :
    let rot0 := fun (s word : Nat) =>
      ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
    let step0 := fun (word : Nat) =>
      (List.range k).foldl (fun acc j =>
        acc ||| ((xor (word.testBit j)
          (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
    let state := fun (rounds key : Nat) =>
      (List.range rounds).foldl (fun prev t =>
        step0 (prev ^^^ rot0 1 prev ^^^ rot0 (k - 1) prev) ^^^ rot0 (2 * t) key ^^^
          (constant (t + 1)).val) (rot0 1 key ^^^ u.val)
    let q := k + i + 3 * r - d
    let trace := fun (len key : Nat) =>
      ((List.range len).foldl (fun (posCode : Nat × Nat) idx =>
        let pos := posCode.1 - 2
        let prev := state (idx + 4) key
        let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
          (prev.testBit ((pos + 2) % k))
        (pos - (if hit then 0 else 1), posCode.2 ||| (hit.toNat <<< idx)))
        (q - 13, 0)).2
    let ones := ((List.range len).filter (fun digit => code.val.testBit digit)).length
    let t := len + 5
    let b := q + ones - 3 * t
    let left := b + 5 - 2 * t
    let startBit := fun (key pos : Nat) => (rot0 1 key ^^^ u.val).testBit (pos % k)
    let guard := fun (raw : Nat) =>
      let word := state (t - 1) raw
      xor (xor (word.testBit (b % k)) (word.testBit ((b + 1) % k)))
        (word.testBit ((b + 2) % k))
    trace len a.val = code.val → trace len z.val = code.val →
      (∀ idx : Nat, left < idx → idx < q → startBit a.val idx = startBit z.val idx) →
      xor (guard a.val) (guard z.val) = xor (startBit a.val left) (startBit z.val left) := by
  intro rot0 step0 state q trace ones t b left startBit guard htra htrz hag
  have hk2 : 2 ≤ k := by omega
  have hones_le : ones ≤ len := by
    have := List.length_filter_le (fun digit => code.val.testBit digit) (List.range len)
    simpa [ones] using this
  have hq_ge : 3 * len + 16 ≤ q := by omega
  have hleft_lt_q : left < q := by omega
  have hb_ge : 2 * (len + 4) + 2 ≤ b := by omega
  have hta := traceRun_spec hk2 u constant q a len hq_ge
  have htz := traceRun_spec hk2 u constant q z len hq_ge
  have htr_eq_a : (traceRun k u constant q len a.val).2 = code.val := htra
  have htr_eq_z : (traceRun k u constant q len z.val).2 = code.val := htrz
  rcases hta with ⟨hpos_a, _, hagree_a⟩
  rcases htz with ⟨hpos_z, _, hagree_z⟩
  rw [htr_eq_a] at hpos_a
  rw [htr_eq_z] at hpos_z
  have hb2_a : b + 2 = (traceRun k u constant q len a.val).1 := by
    rw [hpos_a]; simp only [b, t, ones]; omega
  have hb2_z : b + 2 = (traceRun k u constant q len z.val).1 := by
    rw [hpos_z]; simp only [b, t, ones]; omega
  let srcA := fun pos : Nat => (rot k 1 a.val ^^^ u.val).testBit (pos % k)
  let srcZ := fun pos : Nat => (rot k 1 z.val ^^^ u.val).testBit (pos % k)
  let trA := fun pos : Nat => if pos < q then srcA pos else false
  let trZ := fun pos : Nat => if pos < q then srcZ pos else false
  have htr_agree : ∀ p, left < p → trA p = trZ p := by
    intro p hp
    simp only [trA, trZ]
    by_cases hpq : p < q
    · rw [if_pos hpq, if_pos hpq]
      exact hag p hp hpq
    · rw [if_neg hpq, if_neg hpq]
  have htm1 : t - 1 = len + 4 := by omega
  have hguard_a : guard a.val =
      xor (xor (lineStep k u constant trA (len + 4) b)
               (lineStep k u constant trA (len + 4) (b + 1)))
          (lineStep k u constant trA (len + 4) (b + 2)) := by
    simp only [guard, htm1]
    change xor (xor ((stateAt k u constant (len + 4) a.val).testBit (b % k))
                    ((stateAt k u constant (len + 4) a.val).testBit ((b + 1) % k)))
               ((stateAt k u constant (len + 4) a.val).testBit ((b + 2) % k)) = _
    rw [← lineStep_eq_stateAt hk2 u constant a (len + 4) b (by omega),
        ← lineStep_eq_stateAt hk2 u constant a (len + 4) (b + 1) (by omega),
        ← lineStep_eq_stateAt hk2 u constant a (len + 4) (b + 2) (by omega),
        hagree_a b (by omega) (by omega),
        hagree_a (b + 1) (by omega) (by omega),
        hagree_a (b + 2) (by omega) (by omega)]
  have hguard_z : guard z.val =
      xor (xor (lineStep k u constant trZ (len + 4) b)
               (lineStep k u constant trZ (len + 4) (b + 1)))
          (lineStep k u constant trZ (len + 4) (b + 2)) := by
    simp only [guard, htm1]
    change xor (xor ((stateAt k u constant (len + 4) z.val).testBit (b % k))
                    ((stateAt k u constant (len + 4) z.val).testBit ((b + 1) % k)))
               ((stateAt k u constant (len + 4) z.val).testBit ((b + 2) % k)) = _
    rw [← lineStep_eq_stateAt hk2 u constant z (len + 4) b (by omega),
        ← lineStep_eq_stateAt hk2 u constant z (len + 4) (b + 1) (by omega),
        ← lineStep_eq_stateAt hk2 u constant z (len + 4) (b + 2) (by omega),
        hagree_z b (by omega) (by omega),
        hagree_z (b + 1) (by omega) (by omega),
        hagree_z (b + 2) (by omega) (by omega)]
  have hb1_eq : lineStep k u constant trA (len + 4) (b + 1) =
      lineStep k u constant trZ (len + 4) (b + 1) :=
    lineStep_agree_right k u constant trA trZ left htr_agree (len + 4) (b + 1) (by omega)
  have hb2_eq : lineStep k u constant trA (len + 4) (b + 2) =
      lineStep k u constant trZ (len + 4) (b + 2) :=
    lineStep_agree_right k u constant trA trZ left htr_agree (len + 4) (b + 2) (by omega)
  have hlen4_eq : len + 4 = (len + 3) + 1 := by omega
  have hb0_xor : xor (lineStep k u constant trA (len + 4) b)
      (lineStep k u constant trZ (len + 4) b) = xor (startBit a.val left) (startBit z.val left) := by
    rw [hlen4_eq, lineStep_succ k u constant trA (len + 3) b, lineStep_succ k u constant trZ (len + 3) b]
    have hp0 := lineStep_agree_right k u constant trA trZ left htr_agree (len + 3) (b - 1) (by omega)
    have hp1 := lineStep_agree_right k u constant trA trZ left htr_agree (len + 3) b (by omega)
    have hp2 := lineStep_agree_right k u constant trA trZ left htr_agree (len + 3) (b + 1) (by omega)
    have hp3 := lineStep_agree_right k u constant trA trZ left htr_agree (len + 3) (b + 2) (by omega)
    have hp4 := lineStep_agree_right k u constant trA trZ left htr_agree (len + 3) (b + 3) (by omega)
    have hidx : b + 1 - 2 * (len + 3) = left := by omega
    rw [hp0, hp1, hp2, hp3, hp4, hidx]
    have htrA_l : trA left = startBit a.val left := by
      simp only [trA, if_pos hleft_lt_q]; rfl
    have htrZ_l : trZ left = startBit z.val left := by
      simp only [trZ, if_pos hleft_lt_q]; rfl
    rw [htrA_l, htrZ_l]
    cases lineStep k u constant trZ (len + 3) (b - 1) <;>
    cases lineStep k u constant trZ (len + 3) b <;>
    cases lineStep k u constant trZ (len + 3) (b + 1) <;>
    cases lineStep k u constant trZ (len + 3) (b + 2) <;>
    cases lineStep k u constant trZ (len + 3) (b + 3) <;>
    cases u.val.testBit (left % k) <;>
    cases (constant (len + 3 + 1)).val.testBit (b % k) <;>
    cases startBit a.val left <;>
    cases startBit z.val left <;> rfl
  rw [hguard_a, hguard_z, hb1_eq, hb2_eq]
  rw [← hb0_xor]
  cases lineStep k u constant trA (len + 4) b <;>
  cases lineStep k u constant trZ (len + 4) b <;>
  cases lineStep k u constant trZ (len + 4) (b + 1) <;>
  cases lineStep k u constant trZ (len + 4) (b + 2) <;> rfl

end PEqualNP.Outside.L_meta_25525_aux

theorem PEqualNP.Outside.L_meta_25525 :
∀ (k r d i : Nat), 6 ≤ r → k + 3 + d = 5 * r →
  let n := r - 5
  d ≤ n → i < k → i + (n - d) ≤ k →
  ∀ (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let state := fun (rounds key : Nat) =>
    (List.range rounds).foldl (fun prev t =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * t) key ^^^
        (constant (t + 1)).val) (rot 1 key ^^^ u.val)
  let q := k + i + 3 * r - d
  let trace := fun (len key : Nat) =>
    ((List.range len).foldl (fun (posCode : Nat × Nat) idx =>
      let pos := posCode.1 - 2
      let prev := state (idx + 4) key
      let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
        (prev.testBit ((pos + 2) % k))
      (pos - (if hit then 0 else 1), posCode.2 ||| (hit.toNat <<< idx)))
      (q - 13, 0)).2
  ∀ (len : Nat) (code : Fin (2 ^ len)), len < n →
    let ones := ((List.range len).filter (fun digit => code.val.testBit digit)).length
    d < ones + (n - len) →
    let t := len + 5
    let b := q + ones - 3 * t
    let left := b + 5 - 2 * t
    let startBit := fun (key pos : Nat) => (rot 1 key ^^^ u.val).testBit (pos % k)
    let guard := fun (raw : Nat) =>
      let word := state (t - 1) raw
      xor (xor (word.testBit (b % k)) (word.testBit ((b + 1) % k)))
        (word.testBit ((b + 2) % k))
    ∀ a z : Fin (2 ^ k), trace len a.val = code.val → trace len z.val = code.val →
      (∀ idx : Nat, left < idx → idx < q → startBit a.val idx = startBit z.val idx) →
      xor (guard a.val) (guard z.val) = xor (startBit a.val left) (startBit z.val left) :=
  PEqualNP.Outside.L_meta_25525_aux.main
