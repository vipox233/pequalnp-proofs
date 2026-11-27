import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25526_aux

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

theorem guard_flip_25525 (k r d i : Nat) (hr : 6 ≤ r) (hk : k + 3 + d = 5 * r)
    (hdn : d ≤ r - 5) (hik : i < k) (hind : i + (r - 5 - d) ≤ k)
    (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (len : Nat) (code : Fin (2 ^ len)) (hlen : len < r - 5)
    (hreach : d < ((List.range len).filter (fun digit => code.val.testBit digit)).length + (r - 5 - len))
    (a z : Fin (2 ^ k)) :
    let q := k + i + 3 * r - d
    let ones := ((List.range len).filter (fun digit => code.val.testBit digit)).length
    let t := len + 5
    let b := q + ones - 3 * t
    let left := b + 5 - 2 * t
    let startBit := fun (key pos : Nat) => (rot k 1 key ^^^ u.val).testBit (pos % k)
    let guard := fun (raw : Nat) =>
      let word := stateAt k u constant (t - 1) raw
      xor (xor (word.testBit (b % k)) (word.testBit ((b + 1) % k)))
        (word.testBit ((b + 2) % k))
    (traceRun k u constant q len a.val).2 = code.val →
    (traceRun k u constant q len z.val).2 = code.val →
    (∀ idx : Nat, left < idx → idx < q → startBit a.val idx = startBit z.val idx) →
    xor (guard a.val) (guard z.val) = xor (startBit a.val left) (startBit z.val left) := by
  intro q ones t b left startBit guard htra htrz hag
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

def flipKey (k pos key : Nat) : Nat :=
  key ^^^ (1 <<< (pos % k))

theorem flipKey_lt {k pos key : Nat} (hk : 0 < k) (hkey : key < 2 ^ k) :
    flipKey k pos key < 2 ^ k := by
  unfold flipKey
  apply xor_lt hkey
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.pow_lt_pow_right (by omega) (Nat.mod_lt pos hk)

def flipFin {k : Nat} (hk : 0 < k) (pos : Nat) (key : Fin (2 ^ k)) : Fin (2 ^ k) :=
  ⟨flipKey k pos key.val, flipKey_lt hk key.isLt⟩

theorem flipFin_invol {k : Nat} (hk : 0 < k) (pos : Nat) (key : Fin (2 ^ k)) :
    flipFin hk pos (flipFin hk pos key) = key := by
  apply Fin.ext
  change (key.val ^^^ (1 <<< (pos % k))) ^^^ (1 <<< (pos % k)) = key.val
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem testBit_rot1_flipKey {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (pos0 idx : Nat) (hpos0 : 1 ≤ pos0) (h1 : pos0 ≤ idx) (h2 : idx < pos0 + k)
    (key : Fin (2 ^ k)) :
    (rot k 1 (flipKey k (pos0 - 1) key.val) ^^^ u.val).testBit (idx % k) =
      if idx = pos0 then !((rot k 1 key.val ^^^ u.val).testBit (idx % k))
      else (rot k 1 key.val ^^^ u.val).testBit (idx % k) := by
  have hk_pos : 0 < k := by omega
  have hflip_lt : flipKey k (pos0 - 1) key.val < 2 ^ k := flipKey_lt hk_pos key.isLt
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot hflip_lt (Nat.mod_lt idx hk_pos),
    testBit_rot key.isLt (Nat.mod_lt idx hk_pos)]
  have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hmod1 : (idx % k + k - 1 % k) % k = (idx - 1) % k := by
    rw [h1m]
    have := mod_sub_eq hk_pos (p := idx) (s := 1) (by omega)
    rwa [h1m] at this
  rw [hmod1]
  unfold flipKey
  rw [Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
  by_cases hidx : idx = pos0
  · subst hidx
    simp
  · have hne : (pos0 - 1) % k ≠ (idx - 1) % k := by
      intro heq
      have hsub : 0 < idx - pos0 := by omega
      have hlt : idx - pos0 < k := by omega
      have hsum : (pos0 - 1) + (idx - pos0) = idx - 1 := by omega
      have hmod : ((pos0 - 1) % k + (idx - pos0)) % k = (idx - 1) % k := by
        rw [Nat.mod_add_mod, hsum]
      rw [heq] at hmod
      have hlt2 : (idx - 1) % k < k := Nat.mod_lt _ hk_pos
      have := congrArg (· % k) hmod
      by_cases hc : (idx - 1) % k + (idx - pos0) < k
      · rw [Nat.mod_eq_of_lt hc] at hmod; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod; omega
    simp [hidx, hne]

theorem traceRun_fst_eq_of_snd {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (q len : Nat) (hq : 3 * len + 16 ≤ q)
    (key : Fin (2 ^ k)) :
    (traceRun k u constant q len key.val).1 =
      q + ((List.range len).filter (fun d => (traceRun k u constant q len key.val).2.testBit d)).length - 3 * (len + 4) - 1 :=
  (traceRun_spec hk u constant q key len hq).1

theorem traceRun_lt_two_pow {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (q len : Nat) (hq : 3 * len + 16 ≤ q)
    (key : Fin (2 ^ k)) :
    (traceRun k u constant q len key.val).2 < 2 ^ len := by
  apply Nat.lt_pow_two_of_testBit
  intro d hd
  exact (traceRun_spec hk u constant q key len hq).2.1 d hd

theorem traceRun_prefix_bit {k : Nat} (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (q len m : Nat) (hm : m ≤ len) (key : Nat) (d : Nat) (hd : d < m) :
    (traceRun k u constant q m key).2.testBit d = (traceRun k u constant q len key).2.testBit d := by
  induction len with
  | zero =>
    have : m = 0 := by omega
    subst m; rfl
  | succ len ih =>
    by_cases hml : m = len + 1
    · subst m; rfl
    · have hm' : m ≤ len := by omega
      have hih := ih hm'
      have hstep : (traceRun k u constant q (len + 1) key).2 =
          (traceRun k u constant q len key).2 |||
            ((xor (xor ((stateAt k u constant (len + 4) key).testBit (((traceRun k u constant q len key).1 - 2) % k))
              ((stateAt k u constant (len + 4) key).testBit (((traceRun k u constant q len key).1 - 2 + 1) % k)))
              ((stateAt k u constant (len + 4) key).testBit (((traceRun k u constant q len key).1 - 2 + 2) % k))).toNat <<< len) := by
        simp [traceRun, List.range_succ]
      rw [hih, hstep, Nat.testBit_or, Nat.testBit_shiftLeft]
      have hnot : ¬ len ≤ d := by omega
      simp [hnot]

theorem filter_ones_le_sub (f : Nat → Bool) (m len : Nat) (hm : m ≤ len) :
    ((List.range len).filter (fun d => f d)).length ≤
      ((List.range m).filter (fun d => f d)).length + (len - m) := by
  have hsplit : List.range len = List.range m ++ (List.range (len - m)).map (· + m) := by
    induction len with
    | zero =>
      have : m = 0 := by omega
      subst m; simp
    | succ len ih =>
      by_cases hml : m = len + 1
      · subst m; simp
      · have heq : len + 1 - m = (len - m) + 1 := by omega
        rw [List.range_succ, ih (by omega), heq, List.range_succ, List.map_append, List.map_singleton,
          ← List.append_assoc]
        congr 2
        omega
  rw [hsplit, List.filter_append, List.length_append]
  have hle := List.length_filter_le (fun d => f d) ((List.range (len - m)).map (· + m))
  rw [List.length_map, List.length_range] at hle
  omega

theorem traceRun_agree_of_flip {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (q len : Nat) (hq : 3 * len + 16 ≤ q)
    (pos0 : Nat) (hpos0_ge : q - k ≤ pos0) (hpos0_lt : pos0 < q) (hpos0_1 : 2 ≤ pos0)
    (a : Fin (2 ^ k))
    (hbound : ∀ m < len,
      let ones_m := ((List.range m).filter (fun d => (traceRun k u constant q len a.val).2.testBit d)).length
      let pos_m := q + ones_m - 3 * m - 15
      max (pos0 + (m + 4) + 1) (pos0 + 2 * (m + 4) - 2) ≤ pos_m) :
    let z := flipFin (by omega) (pos0 - 1) a
    ∀ m ≤ len, traceRun k u constant q m z.val = traceRun k u constant q m a.val := by
  intro z m
  induction m with
  | zero =>
    intro _
    simp [traceRun]
  | succ m ih =>
    intro hm
    have hml : m < len := hm
    have ih_m := ih (by omega)
    have htr_z : traceRun k u constant q (m + 1) z.val =
        let prevTr := traceRun k u constant q m z.val
        let pos := prevTr.1 - 2
        let prev := stateAt k u constant (m + 4) z.val
        let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
          (prev.testBit ((pos + 2) % k))
        (pos - (if hit then 0 else 1), prevTr.2 ||| (hit.toNat <<< m)) := by
      simp [traceRun, List.range_succ]
    have htr_a : traceRun k u constant q (m + 1) a.val =
        let prevTr := traceRun k u constant q m a.val
        let pos := prevTr.1 - 2
        let prev := stateAt k u constant (m + 4) a.val
        let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
          (prev.testBit ((pos + 2) % k))
        (pos - (if hit then 0 else 1), prevTr.2 ||| (hit.toNat <<< m)) := by
      simp [traceRun, List.range_succ]
    rw [htr_z, htr_a, ih_m]
    have hpos_m_eq : (traceRun k u constant q m a.val).1 - 2 =
        q + ((List.range m).filter (fun d => (traceRun k u constant q len a.val).2.testBit d)).length - 3 * m - 15 := by
      have hf := traceRun_fst_eq_of_snd hk u constant q m (by omega) a
      have hcongr : (List.range m).filter (fun d => (traceRun k u constant q m a.val).2.testBit d) =
          (List.range m).filter (fun d => (traceRun k u constant q len a.val).2.testBit d) := by
        apply List.filter_congr
        intro d hd
        exact traceRun_prefix_bit u constant q len m (by omega) a.val d (List.mem_range.mp hd)
      rw [hcongr] at hf
      have hones_le : ((List.range m).filter (fun d => (traceRun k u constant q len a.val).2.testBit d)).length ≤ m := by
        simpa using List.length_filter_le (fun d => (traceRun k u constant q len a.val).2.testBit d) (List.range m)
      have hb := hbound m hml
      omega
    set pos := (traceRun k u constant q m a.val).1 - 2
    have hbd := hbound m hml
    dsimp only at hbd
    rw [← hpos_m_eq] at hbd
    have hspec_a := traceRun_spec hk u constant q a m (by omega)
    have hspec_z := traceRun_spec hk u constant q z m (by omega)
    have htr1_eq : (traceRun k u constant q m z.val).1 = (traceRun k u constant q m a.val).1 :=
      congrArg Prod.fst ih_m
    have htr_a_ge : 3 ≤ (traceRun k u constant q m a.val).1 := by
      have ha1 := hspec_a.1
      omega
    have hpos_lt_tr : pos + 2 ≤ (traceRun k u constant q m a.val).1 := by omega
    have hpos_ge_2m : 2 * (m + 4) ≤ pos := by omega
    let srcA := fun p : Nat => (rot k 1 a.val ^^^ u.val).testBit (p % k)
    let srcZ := fun p : Nat => (rot k 1 z.val ^^^ u.val).testBit (p % k)
    let truncA := fun p : Nat => if p < q then srcA p else false
    let truncZ := fun p : Nat => if p < q then srcZ p else false
    have hagree_trunc : ∀ p, pos0 < p → truncZ p = truncA p := by
      intro p hp
      simp only [truncZ, truncA]
      by_cases hpq : p < q
      · simp only [hpq, ↓reduceIte]
        simp only [srcZ, srcA, z, flipFin]
        rw [testBit_rot1_flipKey hk u pos0 p (by omega) (by omega) (by omega) a]
        have hne : p ≠ pos0 := by omega
        simp only [hne, ↓reduceIte]
      · simp only [hpq, ↓reduceIte]
    have hbit_eq : ∀ d, d ≤ 2 →
        (stateAt k u constant (m + 4) z.val).testBit ((pos + d) % k) =
        (stateAt k u constant (m + 4) a.val).testBit ((pos + d) % k) := by
      intro d hd
      rw [← lineStep_eq_stateAt hk u constant z (m + 4) (pos + d) (by omega),
          ← lineStep_eq_stateAt hk u constant a (m + 4) (pos + d) (by omega)]
      rw [hspec_z.2.2 (pos + d) (by omega) (by omega),
          hspec_a.2.2 (pos + d) (by omega) (by omega)]
      exact lineStep_agree_right k u constant truncZ truncA pos0 hagree_trunc (m + 4) (pos + d) (by omega)
    have hb0 := hbit_eq 0 (by omega)
    have hb1 := hbit_eq 1 (by omega)
    have hb2 := hbit_eq 2 (by omega)
    simp only [Nat.add_zero] at hb0
    dsimp only
    rw [hb0, hb1, hb2]

theorem finset_filter_halving {N : Nat} (P Q : Fin N → Bool) (f : Fin N → Fin N)
    (hinv : ∀ x, f (f x) = x) (hP : ∀ x, P (f x) = P x) (hQ : ∀ x, Q (f x) = !(Q x))
    (b : Bool) :
    2 * (Finset.univ.filter (fun x => P x = true ∧ Q x = b)).card =
      (Finset.univ.filter (fun x => P x = true)).card := by
  classical
  let S := Finset.univ.filter (fun x => P x = true)
  let A := Finset.univ.filter (fun x => P x = true ∧ Q x = b)
  let B := Finset.univ.filter (fun x => P x = true ∧ Q x = !b)
  have hAB : A.card = B.card := by
    apply Finset.card_bij (fun x _ => f x)
    · intro x hx
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      refine ⟨(hP x).trans hx.1, ?_⟩
      rw [hQ x, hx.2]
    · intro x _ y _ hxy
      have := congrArg f hxy
      simpa only [hinv] using this
    · intro y hy
      refine ⟨f y, ?_, hinv y⟩
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      refine ⟨(hP y).trans hy.1, ?_⟩
      rw [hQ y, hy.2, Bool.not_not]
  have hdis : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hxA hxB
    rw [hxA.2] at hxB
    cases b <;> simp at hxB
  have hunion : A ∪ B = S := by
    ext x
    simp only [Finset.mem_union, A, B, S, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      cases hb : Q x <;> cases b <;> simp [h, hb]
  change 2 * A.card = S.card
  rw [← hunion, Finset.card_union_of_disjoint hdis, hAB]
  omega

theorem list_range_filter_eq_finset {N : Nat} (p : Nat → Bool) :
    ((List.range N).filter p).length = (Finset.univ.filter (fun x : Fin N => p x.val = true)).card := by
  have hr : List.range N = (List.finRange N).map Fin.val := by
    apply List.ext_getElem (by simp)
    intro i hi1 hi2
    simp
  have hlist : ((List.range N).filter p).length =
      ((List.finRange N).filter (fun x : Fin N => p x.val)).length := by
    rw [hr, List.filter_map, List.length_map]
    rfl
  rw [hlist]
  have hnodup : ((List.finRange N).filter (fun x : Fin N => p x.val)).Nodup :=
    (List.nodup_finRange N).filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  congr 1
  ext x
  simp

set_option maxHeartbeats 800000 in
theorem part1_count (k r d i : Nat) (hr : 6 ≤ r) (hk : k + 3 + d = 5 * r)
    (hdn : d ≤ r - 5) (hik : i < k) (hind : i + (r - 5 - d) ≤ k)
    (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) :
    let n := r - 5
    let q := k + i + 3 * r - d
    ∀ (len : Nat) (code : Fin (2 ^ len)), len ≤ n →
      (len = 0 ∨ d < ((List.range (len - 1)).filter (fun digit => code.val.testBit digit)).length + (n + 1 - len)) →
      ((List.range (2 ^ k)).filter (fun raw => (traceRun k u constant q len raw).2 == code.val)).length = 2 ^ (k - len) := by
  intro n q
  let state := stateAt k u constant
  let trace := fun len key => (traceRun k u constant q len key).2
  have hstate_eq : state = stateAt k u constant := rfl
  have htrace_eq : ∀ len key, trace len key = (traceRun k u constant q len key).2 := fun _ _ => rfl
  have hk2 : 2 ≤ k := by omega
  have hk_pos : 0 < k := by omega
  intro len
  induction len with
    | zero =>
      intro code _ _
      have hcode : code.val = 0 := by omega
      have hall : (List.range (2 ^ k)).filter (fun raw => (traceRun k u constant q 0 raw).2 == code.val) = List.range (2 ^ k) := by
        apply List.filter_eq_self.mpr
        intro raw _
        simp [traceRun, hcode]
      rw [hall, List.length_range, Nat.sub_zero]
    | succ len ih =>
      intro code hlen hreach
      have hlen_lt : len < n := hlen
      have hreach_succ : d < ((List.range len).filter (fun digit => code.val.testBit digit)).length + (n - len) := by
        rcases hreach with h0 | h1
        · omega
        · simpa using h1
      let code0 : Fin (2 ^ len) := ⟨code.val % 2 ^ len, Nat.mod_lt _ (Nat.two_pow_pos len)⟩
      have hcode0_bits : ∀ d', d' < len → code0.val.testBit d' = code.val.testBit d' := by
        intro d' hd'
        simp [code0, Nat.testBit_mod_two_pow, hd']
      have hwt_prev : ((List.range len).filter (fun digit => code0.val.testBit digit)).length =
          ((List.range len).filter (fun digit => code.val.testBit digit)).length := by
        apply congrArg List.length
        apply List.filter_congr
        intro d' hd'
        rw [hcode0_bits d' (List.mem_range.mp hd')]
      have hreach0 : len = 0 ∨
          d < ((List.range (len - 1)).filter (fun digit => code0.val.testBit digit)).length + (n + 1 - len) := by
        by_cases hl0 : len = 0
        · exact Or.inl hl0
        · right
          have hcongr : ((List.range (len - 1)).filter (fun digit => code0.val.testBit digit)).length =
              ((List.range (len - 1)).filter (fun digit => code.val.testBit digit)).length := by
            apply congrArg List.length
            apply List.filter_congr
            intro d' hd'
            have : d' < len - 1 := List.mem_range.mp hd'
            rw [hcode0_bits d' (by omega)]
          rw [hcongr]
          have hle := filter_ones_le_sub (fun digit => code.val.testBit digit) (len - 1) len (by omega)
          omega
      have ih_len := ih code0 (by omega) hreach0
      let ones := ((List.range len).filter (fun digit => code0.val.testBit digit)).length
      let t := len + 5
      let b := q + ones - 3 * t
      let left := b + 5 - 2 * t
      have hones_ge : ones + (n - len) > d := by simpa [ones, hwt_prev] using hreach_succ
      have hones_le : ones ≤ len := by
        simpa [ones] using List.length_filter_le (fun digit => code0.val.testBit digit) (List.range len)
      have hq_ge : 3 * len + 16 ≤ q := by omega
      have hleft_gt : q - k < left := by omega
      have hleft_lt : left < q := by omega
      have hleft_1 : 1 ≤ left := by omega
      have hleft_2 : 2 ≤ left := by omega
      let f : Fin (2 ^ k) → Fin (2 ^ k) := flipFin hk_pos (left - 1)
      let P : Fin (2 ^ k) → Bool := fun x => trace len x.val == code0.val
      let Q : Fin (2 ^ k) → Bool := fun x =>
        let word := state (t - 1) x.val
        xor (xor (word.testBit (b % k)) (word.testBit ((b + 1) % k)))
          (word.testBit ((b + 2) % k))
      have hf_inv : ∀ x, f (f x) = x := flipFin_invol hk_pos (left - 1)
      have hf_P : ∀ x, P (f x) = P x := by
        intro x
        simp only [P]
        by_cases hPx : trace len x.val = code0.val
        · have hagree : traceRun k u constant q len (f x).val = traceRun k u constant q len x.val := by
            refine traceRun_agree_of_flip hk2 u constant q len hq_ge left (by omega) hleft_lt hleft_2 x ?_ len (le_refl len)
            intro m hm
            have hcongr : ((List.range m).filter (fun digit => (traceRun k u constant q len x.val).2.testBit digit)).length =
                ((List.range m).filter (fun digit => code0.val.testBit digit)).length := by
              apply congrArg List.length
              apply List.filter_congr
              intro digit hdig
              rw [← htrace_eq, hPx]
            dsimp only
            rw [hcongr]
            have hsub := filter_ones_le_sub (fun digit => code0.val.testBit digit) m len (by omega)
            omega
          have heq2 : trace len (f x).val = trace len x.val := by
            rw [htrace_eq, htrace_eq]
            exact congrArg Prod.snd hagree
          rw [heq2]
        · have hne2 : trace len (f x).val ≠ code0.val := by
            intro hbad
            have hagree : traceRun k u constant q len (f (f x)).val = traceRun k u constant q len (f x).val := by
              refine traceRun_agree_of_flip hk2 u constant q len hq_ge left (by omega) hleft_lt hleft_2 (f x) ?_ len (le_refl len)
              intro m hm
              have hcongr : ((List.range m).filter (fun digit => (traceRun k u constant q len (f x).val).2.testBit digit)).length =
                  ((List.range m).filter (fun digit => code0.val.testBit digit)).length := by
                apply congrArg List.length
                apply List.filter_congr
                intro digit hdig
                rw [← htrace_eq, hbad]
              dsimp only
              rw [hcongr]
              have hsub := filter_ones_le_sub (fun digit => code0.val.testBit digit) m len (by omega)
              omega
            rw [hf_inv x] at hagree
            have heq2 : trace len x.val = trace len (f x).val := by
              rw [htrace_eq, htrace_eq]
              exact congrArg Prod.snd hagree
            exact hPx (heq2.trans hbad)
          simp [hPx, hne2]
      have hf_Q : ∀ x, P x = true → Q (f x) = !(Q x) := by
        intro x hPx
        have hPx' : (traceRun k u constant q len x.val).2 = code0.val := by
          rw [← htrace_eq]
          exact beq_iff_eq.mp hPx
        have hPfx' : (traceRun k u constant q len (f x).val).2 = code0.val := by
          have := hf_P x
          rw [hPx] at this
          rw [← htrace_eq]
          exact beq_iff_eq.mp (by simpa [P] using this.symm)
        have hguard := guard_flip_25525 k r d i hr hk hdn hik hind u constant len code0 hlen_lt
          (by simpa [ones] using hones_ge) x (f x) hPx' hPfx'
          (fun idx hidx1 hidx2 => by
            simp only [f, flipFin]
            rw [testBit_rot1_flipKey hk2 u left idx hleft_1 (by omega) (by omega) x, if_neg (by omega)])
        have hsb : xor ((rot k 1 x.val ^^^ u.val).testBit (left % k))
            ((rot k 1 (f x).val ^^^ u.val).testBit (left % k)) = true := by
          simp only [f, flipFin]
          rw [testBit_rot1_flipKey hk2 u left left hleft_1 (le_refl left) (by omega) x, if_pos rfl]
          cases (rot k 1 x.val ^^^ u.val).testBit (left % k) <;> rfl
        have hgd : xor (Q x) (Q (f x)) = true := by
          simpa only [Q, hstate_eq, b, t, ones] using hguard.trans hsb
        cases hq1 : Q x <;> cases hq2 : Q (f x) <;> simp_all

      have hPQ_equiv : ∀ x : Fin (2 ^ k),
          (trace (len + 1) x.val == code.val) = (P x && (Q x == code.val.testBit len)) := by
        intro x
        rw [htrace_eq]
        have hstep_tr : traceRun k u constant q (len + 1) x.val =
            let tr0 := traceRun k u constant q len x.val
            let pos := tr0.1 - 2
            let prev := stateAt k u constant (len + 4) x.val
            let hit := xor (xor (prev.testBit (pos % k)) (prev.testBit ((pos + 1) % k)))
              (prev.testBit ((pos + 2) % k))
            (pos - (if hit then 0 else 1), tr0.2 ||| (hit.toNat <<< len)) := by
          simp [traceRun, List.range_succ]
        have htm1 : t - 1 = len + 4 := by omega
        by_cases hPx : P x = true
        · have hPx' : (traceRun k u constant q len x.val).2 = code0.val := by
            rw [← htrace_eq]; exact beq_iff_eq.mp hPx
          have hpos0 : (traceRun k u constant q len x.val).1 - 2 = b := by
            have hf := traceRun_fst_eq_of_snd hk2 u constant q len hq_ge x
            rw [hPx'] at hf
            simp only [b, t, ones]
            omega
          have hhi : ∀ dd, len ≤ dd → (traceRun k u constant q len x.val).2.testBit dd = false :=
            (traceRun_spec hk2 u constant q x len hq_ge).2.1
          have hQ_eq : Q x =
              xor (xor ((stateAt k u constant (len + 4) x.val).testBit (((traceRun k u constant q len x.val).1 - 2) % k))
                ((stateAt k u constant (len + 4) x.val).testBit (((traceRun k u constant q len x.val).1 - 2 + 1) % k)))
                ((stateAt k u constant (len + 4) x.val).testBit (((traceRun k u constant q len x.val).1 - 2 + 2) % k)) := by
            simp only [Q, hstate_eq, htm1, hpos0]
          rw [hPx, Bool.true_and]
          apply Bool.eq_iff_iff.mpr
          rw [beq_iff_eq, beq_iff_eq, hstep_tr]
          dsimp only
          rw [← hQ_eq, hPx']
          constructor
          · intro hcomb
            have hbit := congrArg (fun w => w.testBit len) hcomb
            rw [Nat.testBit_or, Nat.testBit_shiftLeft] at hbit
            have h0 : code0.val.testBit len = false := Nat.testBit_lt_two_pow code0.isLt
            simp only [le_refl, decide_true, Nat.sub_self, Bool.true_and, h0, Bool.false_or] at hbit
            rw [← hbit]
            cases Q x <;> rfl
          · intro hq_bit
            apply Nat.eq_of_testBit_eq
            intro dd
            rw [Nat.testBit_or, Nat.testBit_shiftLeft]
            by_cases hdl : dd < len
            · have hnot : ¬ len ≤ dd := by omega
              simp only [hnot, decide_false, Bool.false_and, Bool.or_false]
              exact hcode0_bits dd hdl
            · by_cases hdeq : dd = len
              · subst hdeq
                have h0 : code0.val.testBit dd = false := Nat.testBit_lt_two_pow code0.isLt
                simp only [le_refl, decide_true, Nat.sub_self, Bool.true_and, h0, Bool.false_or, hq_bit]
                cases code.val.testBit dd <;> rfl
              · have hgt : len + 1 ≤ dd := by omega
                have h0 : code0.val.testBit dd = false :=
                  Nat.testBit_lt_two_pow (code0.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
                have hc0 : code.val.testBit dd = false :=
                  Nat.testBit_lt_two_pow (code.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hgt))
                have hsub : 1 ≤ dd - len := by omega
                have hbt : (Q x).toNat.testBit (dd - len) = false := by
                  cases Q x
                  · simp
                  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
                      (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
                simp [h0, hc0, hbt]
        · have hPfalse : P x = false := Bool.eq_false_iff.mpr hPx
          rw [hPfalse, Bool.false_and]
          apply Bool.eq_iff_iff.mpr
          simp only [beq_iff_eq, Bool.false_eq_true, iff_false]
          intro hbad
          have hpre : (traceRun k u constant q len x.val).2 = code0.val := by
            apply Nat.eq_of_testBit_eq
            intro dd
            by_cases hdl : dd < len
            · rw [hcode0_bits dd hdl, ← hbad]
              exact traceRun_prefix_bit u constant q (len + 1) len (by omega) x.val dd hdl
            · have h0 : code0.val.testBit dd = false :=
                Nat.testBit_lt_two_pow (code0.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
              rw [h0]
              exact (traceRun_spec hk2 u constant q x len hq_ge).2.1 dd (by omega)
          rw [← htrace_eq] at hpre
          have : P x = true := by simp [P, hpre]
          simp [hPfalse] at this
      let Q' : Fin (2 ^ k) → Bool := fun x =>
        if x.val < (f x).val then Q x else !(Q (f x))
      have hf_Q' : ∀ x, Q' (f x) = !(Q' x) := by
        intro x
        simp only [Q', hf_inv x]
        by_cases hlt : x.val < (f x).val
        · have hnot : ¬ (f x).val < x.val := by omega
          rw [if_pos hlt, if_neg hnot]
        · by_cases hgt : (f x).val < x.val
          · have hnot : ¬ x.val < (f x).val := by omega
            rw [if_pos hgt, if_neg hnot, Bool.not_not]
          · have heq : f x = x := Fin.ext (by omega)
            exfalso
            have hbit := congrArg (fun w : Fin (2 ^ k) => w.val.testBit ((left - 1) % k)) heq
            simp only [f, flipFin, flipKey, Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul,
              Nat.testBit_two_pow, ↓reduceIte] at hbit
            cases x.val.testBit ((left - 1) % k) <;> simp at hbit
      have hPQ' : ∀ x, P x = true → Q' x = Q x := by
        intro x hPx
        simp only [Q']
        by_cases hlt : x.val < (f x).val
        · rw [if_pos hlt]
        · rw [if_neg hlt, hf_Q x hPx, Bool.not_not]
      have hhalve := finset_filter_halving P Q' f hf_inv hf_P hf_Q' (code.val.testBit len)
      have hfilter_eq : Finset.univ.filter (fun x : Fin (2 ^ k) => (trace (len + 1) x.val == code.val) = true) =
          Finset.univ.filter (fun x : Fin (2 ^ k) => P x = true ∧ Q' x = code.val.testBit len) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hPQ_equiv x, Bool.and_eq_true]
        constructor
        · rintro ⟨hPx, hQx⟩
          exact ⟨hPx, by rw [hPQ' x hPx]; exact beq_iff_eq.mp hQx⟩
        · rintro ⟨hPx, hQx⟩
          exact ⟨hPx, beq_iff_eq.mpr (by rw [← hPQ' x hPx]; exact hQx)⟩
      rw [list_range_filter_eq_finset, hfilter_eq]
      rw [list_range_filter_eq_finset] at ih_len
      have hP_eq : Finset.univ.filter (fun x : Fin (2 ^ k) => P x = true) =
          Finset.univ.filter (fun x : Fin (2 ^ k) => ((traceRun k u constant q len x.val).2 == code0.val) = true) := rfl
      have hcard : 2 * (Finset.univ.filter (fun x : Fin (2 ^ k) => P x = true ∧ Q' x = code.val.testBit len)).card =
          2 ^ (k - len) := by
        rw [hhalve, hP_eq]
        exact ih_len
      have hsub_eq : k - len = (k - (len + 1)) + 1 := by omega
      have hpow2 : 2 ^ (k - len) = 2 * 2 ^ (k - (len + 1)) := by
        rw [hsub_eq, Nat.pow_succ']
      omega

set_option maxHeartbeats 800000 in
theorem part2_fiber (k r d i : Nat) (hr : 6 ≤ r) (hk : k + 3 + d = 5 * r)
    (hdn : d ≤ r - 5) (hik : i < k) (hind : i + (r - 5 - d) ≤ k)
    (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (code : Fin (2 ^ (r - 5)))
    (hwt : d < ((List.range (r - 5)).filter (fun digit => code.val.testBit digit)).length) :
    let n := r - 5
    let q := k + i + 3 * r - d
    let m := ((List.range n).filter (fun digit => code.val.testBit digit)).length - d
    ∀ target : Fin (2 ^ m),
      (((List.range (2 ^ k)).filter (fun raw => (traceRun k u constant q n raw).2 == code.val)).filter
        (fun candidate => ((stateAt k u constant r candidate >>> i) % 2 ^ m) == target.val)).length =
      2 ^ (k - n - m) := by
  intro n q m target
  let state := stateAt k u constant
  let trace := fun len key => (traceRun k u constant q len key).2
  have hstate_eq : state = stateAt k u constant := rfl
  have htrace_eq : ∀ len key, trace len key = (traceRun k u constant q len key).2 := fun _ _ => rfl
  have hk2 : 2 ≤ k := by omega
  have hk_pos : 0 < k := by omega
  have hwt' : d < ((List.range n).filter (fun digit => code.val.testBit digit)).length := hwt
  have hwt_le : ((List.range n).filter (fun digit => code.val.testBit digit)).length ≤ n := by
    simpa using List.length_filter_le (fun digit => code.val.testBit digit) (List.range n)
  have hreach_n : n = 0 ∨
      d < ((List.range (n - 1)).filter (fun digit => code.val.testBit digit)).length + (n + 1 - n) := by
    right
    have hsub := filter_ones_le_sub (fun digit => code.val.testBit digit) (n - 1) n (by omega)
    omega
  have hm_pos : 1 ≤ m := by dsimp only [m]; omega
  have hm_le : m ≤ n - d := by dsimp only [m]; omega
  have hikm : i + m ≤ k := by omega
  have hqn_ge : 3 * n + 16 ≤ q := by omega
  have hones_eq : ((List.range n).filter (fun digit => code.val.testBit digit)).length = d + m := by
    dsimp only [m]; omega
  have htr1_val : ∀ x : Fin (2 ^ k), trace n x.val = code.val →
      (traceRun k u constant q n x.val).1 = k + i + m + 2 := by
    intro x hx
    have hf := traceRun_fst_eq_of_snd hk2 u constant q n hqn_ge x
    have hcongr : ((List.range n).filter (fun digit => (traceRun k u constant q n x.val).2.testBit digit)).length =
        ((List.range n).filter (fun digit => code.val.testBit digit)).length := by
      apply congrArg List.length
      apply List.filter_congr
      intro digit hdig
      rw [← htrace_eq, hx]
    rw [hcongr, hones_eq] at hf
    omega
  have hpart2_ind : ∀ l ≤ m,
      ((List.range (2 ^ k)).filter (fun candidate =>
        (trace n candidate == code.val) &&
        (((state r candidate >>> (i + (m - l))) % 2 ^ l) == (target.val >>> (m - l))))).length =
      2 ^ (k - n - l) := by
    intro l
    induction l with
    | zero =>
      intro _
      have hall : (List.range (2 ^ k)).filter (fun candidate =>
          (trace n candidate == code.val) &&
          (((state r candidate >>> (i + (m - 0))) % 2 ^ 0) == (target.val >>> (m - 0)))) =
          (List.range (2 ^ k)).filter (fun candidate => trace n candidate == code.val) := by
        apply List.filter_congr
        intro candidate _
        have ht0 : target.val >>> m = 0 := by
          rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt target.isLt]
        simp [ht0, Nat.mod_one]
      rw [hall, Nat.sub_zero]
      exact part1_count k r d i hr hk hdn hik hind u constant n code (le_refl n) hreach_n
    | succ l ih =>
      intro hl
      have ih_l := ih (by omega)
      let j := m - 1 - l
      have hj_lt : j < m := by omega
      have hml : m - (l + 1) = j := by omega
      have hml0 : m - l = j + 1 := by omega
      let pos0 := q - k + j
      have hpos0_ge : q - k ≤ pos0 := by omega
      have hpos0_lt : pos0 < q := by omega
      have hpos0_1 : 1 ≤ pos0 := by omega
      have hpos0_2 : 2 ≤ pos0 := by omega
      let f : Fin (2 ^ k) → Fin (2 ^ k) := flipFin hk_pos (pos0 - 1)
      let P : Fin (2 ^ k) → Bool := fun x =>
        (trace n x.val == code.val) &&
        (((state r x.val >>> (i + (j + 1))) % 2 ^ l) == (target.val >>> (j + 1)))
      let Q : Fin (2 ^ k) → Bool := fun x => (state r x.val).testBit (i + j)
      have hf_inv : ∀ x, f (f x) = x := flipFin_invol hk_pos (pos0 - 1)
      have hf_trace : ∀ x : Fin (2 ^ k), trace n x.val = code.val → trace n (f x).val = code.val := by
        intro x hx
        have hagree : traceRun k u constant q n (f x).val = traceRun k u constant q n x.val := by
          refine traceRun_agree_of_flip hk2 u constant q n hqn_ge pos0 hpos0_ge hpos0_lt hpos0_2 x ?_ n (le_refl n)
          intro idx hidx
          have hcongr : ((List.range idx).filter (fun digit => (traceRun k u constant q n x.val).2.testBit digit)).length =
              ((List.range idx).filter (fun digit => code.val.testBit digit)).length := by
            apply congrArg List.length
            apply List.filter_congr
            intro digit hdig
            rw [← htrace_eq, hx]
          dsimp only
          rw [hcongr]
          have hsub := filter_ones_le_sub (fun digit => code.val.testBit digit) idx n (by omega)
          omega
        rw [htrace_eq]
        exact (congrArg Prod.snd hagree).trans (by rw [← htrace_eq]; exact hx)

      have hstate_bit : ∀ x : Fin (2 ^ k), trace n x.val = code.val →
          ∀ j', j ≤ j' → j' < m →
            (state r (f x).val).testBit (i + j') =
              if j' = j then !((state r x.val).testBit (i + j')) else (state r x.val).testBit (i + j') := by
        intro x hx j' hj'1 hj'2
        have hfx : trace n (f x).val = code.val := hf_trace x hx
        have htr_x : (traceRun k u constant q n x.val).1 = k + i + m + 2 := htr1_val x hx
        have htr_fx : (traceRun k u constant q n (f x).val).1 = k + i + m + 2 := htr1_val (f x) hfx
        have hspec_x := traceRun_spec hk2 u constant q x n hqn_ge
        have hspec_fx := traceRun_spec hk2 u constant q (f x) n hqn_ge
        have hn4 : n + 4 = r - 1 := by omega
        have hr1 : r = (r - 1) + 1 := by omega
        let p := k + i + j'
        have hij'_lt : i + j' < k := by omega
        have hp_mod : p % k = i + j' := by
          have : p = i + j' + 1 * k := by omega
          rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hij'_lt]
        have hp_ge : 2 * r ≤ p := by omega
        rw [← hp_mod]
        simp only [hstate_eq]
        rw [← lineStep_eq_stateAt hk2 u constant (f x) r p hp_ge,
            ← lineStep_eq_stateAt hk2 u constant x r p hp_ge,
            hr1, lineStep_succ k u constant _ (r - 1) p, lineStep_succ k u constant _ (r - 1) p]
        let srcX := fun pos : Nat => (rot k 1 x.val ^^^ u.val).testBit (pos % k)
        let srcFX := fun pos : Nat => (rot k 1 (f x).val ^^^ u.val).testBit (pos % k)
        let truncX := fun pos : Nat => if pos < q then srcX pos else false
        let truncFX := fun pos : Nat => if pos < q then srcFX pos else false
        have hagree_trunc : ∀ t', pos0 < t' → truncFX t' = truncX t' := by
          intro t' ht'
          simp only [truncFX, truncX]
          by_cases htq : t' < q
          · rw [if_pos htq, if_pos htq]
            simp only [srcFX, srcX, f, flipFin]
            rw [testBit_rot1_flipKey hk2 u pos0 t' hpos0_1 (by omega) (by omega) x, if_neg (by omega)]
          · rw [if_neg htq, if_neg htq]
        have hprev_eq : ∀ d', p - 1 ≤ d' → d' ≤ p + 3 →
            lineStep k u constant srcFX (r - 1) d' = lineStep k u constant srcX (r - 1) d' := by
          intro d' hd1 hd2
          have hd_tr1 : d' ≤ (traceRun k u constant q n x.val).1 := by rw [htr_x]; omega
          have hd_tr2 : d' ≤ (traceRun k u constant q n (f x).val).1 := by rw [htr_fx]; omega
          have h2n4 : 2 * (n + 4) ≤ d' := by omega
          have hsx := hspec_x.2.2 d' h2n4 hd_tr1
          have hsfx := hspec_fx.2.2 d' h2n4 hd_tr2
          rw [hn4] at hsx hsfx
          rw [hsx, hsfx]
          exact lineStep_agree_right k u constant truncFX truncX pos0 hagree_trunc (r - 1) d' (by omega)
        have h0 := hprev_eq (p - 1) (by omega) (by omega)
        have h1 := hprev_eq p (by omega) (by omega)
        have h2 := hprev_eq (p + 1) (by omega) (by omega)
        have h3 := hprev_eq (p + 2) (by omega) (by omega)
        have h4 := hprev_eq (p + 3) (by omega) (by omega)
        rw [h0, h1, h2, h3, h4]
        have hinj_pos : p + 1 - 2 * (r - 1) = q - k + j' := by omega
        rw [hinj_pos]
        have hj'_flip : (rot k 1 (f x).val ^^^ u.val).testBit ((q - k + j') % k) =
            if j' = j then !((rot k 1 x.val ^^^ u.val).testBit ((q - k + j') % k))
            else (rot k 1 x.val ^^^ u.val).testBit ((q - k + j') % k) := by
          simp only [f, flipFin]
          rw [testBit_rot1_flipKey hk2 u pos0 (q - k + j') hpos0_1 (by omega) (by omega) x]
          have : (q - k + j' = pos0) ↔ (j' = j) := by omega
          by_cases hjj : j' = j
          · rw [if_pos (this.mpr hjj), if_pos hjj]
          · rw [if_neg (fun h => hjj (this.mp h)), if_neg hjj]
        by_cases hjj : j' = j
        · rw [if_pos hjj] at hj'_flip ⊢
          dsimp only [srcFX, srcX]
          rw [hj'_flip]
          cases lineStep k u constant srcX (r - 1) p <;>
          cases lineStep k u constant srcX (r - 1) (p - 1) <;>
          cases lineStep k u constant srcX (r - 1) (p + 1) <;>
          cases lineStep k u constant srcX (r - 1) (p + 2) <;>
          cases lineStep k u constant srcX (r - 1) (p + 3) <;>
          cases (rot k 1 x.val ^^^ u.val).testBit ((q - k + j') % k) <;>
          cases u.val.testBit ((q - k + j') % k) <;>
          cases (constant (r - 1 + 1)).val.testBit (p % k) <;> rfl
        · rw [if_neg hjj] at hj'_flip ⊢
          dsimp only [srcFX, srcX]
          rw [hj'_flip]
      have hf_P : ∀ x, P (f x) = P x := by
        intro x
        simp only [P]
        by_cases hx : trace n x.val = code.val
        · have hfx : trace n (f x).val = code.val := hf_trace x hx
          have hx_eq : (trace n x.val == code.val) = true := beq_iff_eq.mpr hx
          have hfx_eq : (trace n (f x).val == code.val) = true := beq_iff_eq.mpr hfx
          rw [hx_eq, hfx_eq, Bool.true_and, Bool.true_and]
          have hmod_eq : ((state r (f x).val >>> (i + (j + 1))) % 2 ^ l) =
              ((state r x.val >>> (i + (j + 1))) % 2 ^ l) := by
            apply Nat.eq_of_testBit_eq
            intro b'
            by_cases hb' : b' < l
            · simp only [Nat.testBit_mod_two_pow, hb', decide_true, Bool.true_and,
                Nat.testBit_shiftRight]
              have hrw : i + (j + 1) + b' = i + (j + 1 + b') := by omega
              rw [hrw]
              have hbit := hstate_bit x hx (j + 1 + b') (by omega) (by omega)
              have hne : j + 1 + b' ≠ j := by omega
              rw [if_neg hne] at hbit
              exact hbit
            · simp [Nat.testBit_mod_two_pow, hb']
          rw [hmod_eq]
        · have hfx : trace n (f x).val ≠ code.val := by
            intro hbad
            have := hf_trace (f x) hbad
            rw [hf_inv x] at this
            exact hx this
          have hx_f : (trace n x.val == code.val) = false := beq_false_of_ne hx
          have hfx_f : (trace n (f x).val == code.val) = false := beq_false_of_ne hfx
          rw [hx_f, hfx_f, Bool.false_and, Bool.false_and]
      have hf_Q : ∀ x, P x = true → Q (f x) = !(Q x) := by
        intro x hPx
        have hx : trace n x.val = code.val := beq_iff_eq.mp (Bool.and_eq_true _ _ |>.mp hPx).1
        have hbit := hstate_bit x hx j (le_refl j) hj_lt
        rw [if_pos rfl] at hbit
        exact hbit
      let Q' : Fin (2 ^ k) → Bool := fun x =>
        if x.val < (f x).val then Q x else !(Q (f x))
      have hf_Q' : ∀ x, Q' (f x) = !(Q' x) := by
        intro x
        simp only [Q', hf_inv x]
        by_cases hlt : x.val < (f x).val
        · have hnot : ¬ (f x).val < x.val := by omega
          rw [if_pos hlt, if_neg hnot]
        · by_cases hgt : (f x).val < x.val
          · have hnot : ¬ x.val < (f x).val := by omega
            rw [if_pos hgt, if_neg hnot, Bool.not_not]
          · have heq : f x = x := Fin.ext (by omega)
            exfalso
            have hbit := congrArg (fun w : Fin (2 ^ k) => w.val.testBit ((pos0 - 1) % k)) heq
            simp only [f, flipFin, flipKey, Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul,
              Nat.testBit_two_pow, ↓reduceIte] at hbit
            cases x.val.testBit ((pos0 - 1) % k) <;> simp at hbit
      have hPQ' : ∀ x, P x = true → Q' x = Q x := by
        intro x hPx
        simp only [Q']
        by_cases hlt : x.val < (f x).val
        · rw [if_pos hlt]
        · rw [if_neg hlt, hf_Q x hPx, Bool.not_not]
      have hhalve := finset_filter_halving P Q' f hf_inv hf_P hf_Q' (target.val.testBit j)
      have hsplit_cond : ∀ x : Fin (2 ^ k),
          ((trace n x.val == code.val) &&
            (((state r x.val >>> (i + j)) % 2 ^ (l + 1)) == (target.val >>> j))) =
          (P x && (Q' x == target.val.testBit j)) := by
        intro x
        by_cases hPx : P x = true
        · rw [hPQ' x hPx]
          have hP1 : (trace n x.val == code.val) = true := (Bool.and_eq_true _ _ |>.mp hPx).1
          have hP2 : (((state r x.val >>> (i + (j + 1))) % 2 ^ l) == (target.val >>> (j + 1))) = true :=
            (Bool.and_eq_true _ _ |>.mp hPx).2
          have hP2' := beq_iff_eq.mp hP2
          rw [hPx, hP1, Bool.true_and, Bool.true_and]
          apply Bool.eq_iff_iff.mpr
          rw [beq_iff_eq, beq_iff_eq]
          constructor
          · intro heq
            have hb0 := congrArg (fun w => w.testBit 0) heq
            simp only [Nat.testBit_mod_two_pow, Nat.zero_lt_succ, decide_true, Bool.true_and,
              Nat.testBit_shiftRight, Nat.add_zero] at hb0
            exact hb0
          · intro hbit
            apply Nat.eq_of_testBit_eq
            intro b'
            by_cases hb' : b' < l + 1
            · simp only [Nat.testBit_mod_two_pow, hb', decide_true, Bool.true_and,
                Nat.testBit_shiftRight]
              cases b' with
              | zero => exact hbit
              | succ b'' =>
                have hb'' : b'' < l := by omega
                have h2 := congrArg (fun w => w.testBit b'') hP2'
                simp only [Nat.testBit_mod_two_pow, hb'', decide_true, Bool.true_and,
                  Nat.testBit_shiftRight] at h2
                have he1 : i + j + (b'' + 1) = i + (j + 1) + b'' := by omega
                have he2 : j + (b'' + 1) = j + 1 + b'' := by omega
                rw [he1, he2]
                exact h2
            · have hle : l + 1 ≤ b' := by omega
              have h0 : ((state r x.val >>> (i + j)) % 2 ^ (l + 1)).testBit b' = false :=
                Nat.testBit_lt_two_pow ((Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
                  (Nat.pow_le_pow_right Nat.zero_lt_two hle))
              have htar : target.val >>> j < 2 ^ (l + 1) := by
                rw [Nat.shiftRight_eq_div_pow]
                exact Nat.div_lt_of_lt_mul (by
                  rw [← Nat.pow_add]
                  have heq : j + (l + 1) = m := by omega
                  rw [heq]
                  exact target.isLt)
              have h1 : (target.val >>> j).testBit b' = false :=
                Nat.testBit_lt_two_pow (htar.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hle))
              rw [h0, h1]
        · have hPf : P x = false := Bool.eq_false_iff.mpr hPx
          rw [hPf, Bool.false_and]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.false_eq_true, iff_false, Bool.and_eq_true, beq_iff_eq]
          rintro ⟨h1, h2⟩
          have hP2 : ((state r x.val >>> (i + (j + 1))) % 2 ^ l) = (target.val >>> (j + 1)) := by
            apply Nat.eq_of_testBit_eq
            intro b'
            by_cases hb' : b' < l
            · simp only [Nat.testBit_mod_two_pow, hb', decide_true, Bool.true_and,
                Nat.testBit_shiftRight]
              have hsub := congrArg (fun w => w.testBit (b' + 1)) h2
              simp only [Nat.testBit_mod_two_pow, show b' + 1 < l + 1 by omega, decide_true,
                Bool.true_and, Nat.testBit_shiftRight] at hsub
              have he1 : i + (j + 1) + b' = i + j + (b' + 1) := by omega
              have he2 : j + 1 + b' = j + (b' + 1) := by omega
              rw [he1, he2]
              exact hsub
            · have hle : l ≤ b' := by omega
              have h0 : ((state r x.val >>> (i + (j + 1))) % 2 ^ l).testBit b' = false :=
                Nat.testBit_lt_two_pow ((Nat.mod_lt _ (Nat.two_pow_pos _)).trans_le
                  (Nat.pow_le_pow_right Nat.zero_lt_two hle))
              have htar : target.val >>> (j + 1) < 2 ^ l := by
                rw [Nat.shiftRight_eq_div_pow]
                exact Nat.div_lt_of_lt_mul (by
                  rw [← Nat.pow_add]
                  have heq : (j + 1) + l = m := by omega
                  rw [heq]
                  exact target.isLt)
              have h1 : (target.val >>> (j + 1)).testBit b' = false :=
                Nat.testBit_lt_two_pow (htar.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hle))
              rw [h0, h1]
          have : P x = true := by simp [P, h1, hP2]
          simp [hPf] at this
      rw [list_range_filter_eq_finset]
      have hfeq : Finset.univ.filter (fun x : Fin (2 ^ k) =>
            ((trace n x.val == code.val) &&
            (((state r x.val >>> (i + (m - (l + 1)))) % 2 ^ (l + 1)) == (target.val >>> (m - (l + 1))))) = true) =
          Finset.univ.filter (fun x : Fin (2 ^ k) => P x = true ∧ Q' x = target.val.testBit j) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hml]
        rw [hsplit_cond x, Bool.and_eq_true, beq_iff_eq]
      rw [hfeq]
      rw [list_range_filter_eq_finset] at ih_l
      have hP_eq : Finset.univ.filter (fun x : Fin (2 ^ k) => P x = true) = Finset.univ.filter (fun x : Fin (2 ^ k) =>
          ((trace n x.val == code.val) &&
          (((state r x.val >>> (i + (m - l))) % 2 ^ l) == (target.val >>> (m - l)))) = true) := by
        ext x
        simp [P, hml0]
      rw [← hP_eq] at ih_l
      have hpow : k - n - l = (k - n - (l + 1)) + 1 := by omega
      rw [ih_l, hpow, Nat.pow_succ'] at hhalve
      omega
  have hfinal := hpart2_ind m (le_refl m)
  rw [Nat.sub_self, Nat.add_zero, Nat.shiftRight_zero] at hfinal
  rw [← hfinal]
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro x _
  simp [state, trace, Bool.and_comm]

theorem main : (∀ (k r d i : Nat), 6 ≤ r → k + 3 + d = 5 * r →
  let n := r - 5
  d ≤ n → i < k → i + (n - d) ≤ k →
  ∀ (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)),
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
  ∀ (len : Nat) (code : Fin (2 ^ len)), len ≤ n →
    let wt := fun (count : Nat) =>
      ((List.range count).filter (fun digit => code.val.testBit digit)).length
    (len = 0 ∨ d < wt (len - 1) + (n + 1 - len)) →
    let keys := (List.range (2 ^ k)).filter (fun raw => trace len raw == code.val)
    keys.length = 2 ^ (k - len) ∧
      (len = n → d < wt len →
        let m := wt len - d
        ∀ target : Fin (2 ^ m),
          (keys.filter (fun candidate =>
            ((state r candidate >>> i) % 2 ^ m) == target.val)).length = 2 ^ (k - n - m))) := by
  intro k r d i hr hk n hdn hik hind u constant rot0 step0 state q trace len code hlen wt hreach
  refine ⟨part1_count k r d i hr hk hdn hik hind u constant len code hlen hreach, ?_⟩
  rintro rfl hwt
  intro m target
  exact part2_fiber k r d i hr hk hdn hik hind u constant code hwt target

end PEqualNP.Outside.L_meta_25526_aux

theorem PEqualNP.Outside.L_meta_25526 : (∀ (k r d i : Nat), 6 ≤ r → k + 3 + d = 5 * r →
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
  ∀ (len : Nat) (code : Fin (2 ^ len)), len ≤ n →
    let wt := fun (count : Nat) =>
      ((List.range count).filter (fun digit => code.val.testBit digit)).length
    (len = 0 ∨ d < wt (len - 1) + (n + 1 - len)) →
    let keys := (List.range (2 ^ k)).filter (fun raw => trace len raw == code.val)
    keys.length = 2 ^ (k - len) ∧
      (len = n → d < wt len →
        let m := wt len - d
        ∀ target : Fin (2 ^ m),
          (keys.filter (fun candidate =>
            ((state r candidate >>> i) % 2 ^ m) == target.val)).length = 2 ^ (k - n - m))) :=
  PEqualNP.Outside.L_meta_25526_aux.main
