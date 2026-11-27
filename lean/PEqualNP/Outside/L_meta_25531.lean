import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25531_aux

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
  (List.range rounds).foldl (fun prev tick =>
    step k (mix k prev) ^^^ rot k (2 * tick) key ^^^ (constant (tick + 1)).val) (rot k 1 key ^^^ u.val)

theorem stateAt_zero (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (key : Nat) :
    stateAt k u constant 0 key = rot k 1 key ^^^ u.val := rfl

theorem stateAt_succ (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (s key : Nat) :
    stateAt k u constant (s + 1) key =
      step k (mix k (stateAt k u constant s key)) ^^^ rot k (2 * s) key ^^^ (constant (s + 1)).val := by
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
  | succ s =>
    rw [stateAt_succ]
    exact xor_lt (xor_lt (step_lt k _) (rot_lt k _ _)) (constant (s + 1)).isLt

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
  | zero => intro p _; rfl
  | succ s ih =>
    intro p hp
    rw [lineStep_succ, stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk_pos)]
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

theorem lineStep_agree_interval (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (lo hi : Nat) (hfg : ∀ p, lo ≤ p → p ≤ hi → f p = g p) :
    ∀ s p, max (lo + s) (lo + 2 * s - 3) ≤ p → p + 3 * s ≤ hi →
      lineStep k u constant f s p = lineStep k u constant g s p := by
  intro s
  induction s with
  | zero =>
    intro p h1 h2
    exact hfg p (by omega) (by omega)
  | succ s ih =>
    intro p h1 h2
    rw [lineStep_succ k u constant f s p, lineStep_succ k u constant g s p]
    have h0 := ih (p - 1) (by omega) (by omega)
    have h1' := ih p (by omega) (by omega)
    have h2' := ih (p + 1) (by omega) (by omega)
    have h3 := ih (p + 2) (by omega) (by omega)
    have h4 := ih (p + 3) (by omega) (by omega)
    have hi' := hfg (p + 1 - 2 * s) (by omega) (by omega)
    rw [h0, h1', h2', h3, h4, hi']

theorem lineStep_xor_pivot (k : Nat) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (f g : Nat → Bool) (s p : Nat) (hs : 4 ≤ s) (hp : 2 * s ≤ p)
    (hfg : ∀ q, p + 4 - 2 * s ≤ q → q ≤ p + 3 * s → f q = g q) :
    xor (lineStep k u constant f s p) (lineStep k u constant g s p) =
      xor (f (p + 3 - 2 * s)) (g (p + 3 - 2 * s)) := by
  have hs_eq : s = (s - 1) + 1 := by omega
  conv_lhs => rw [hs_eq, lineStep_succ k u constant f (s - 1) p, lineStep_succ k u constant g (s - 1) p]
  have h0 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p - 1) (by omega) (by omega)
  have h1 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) p (by omega) (by omega)
  have h2 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 1) (by omega) (by omega)
  have h3 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 2) (by omega) (by omega)
  have h4 := lineStep_agree_interval k u constant f g (p + 4 - 2 * s) (p + 3 * s) hfg (s - 1) (p + 3) (by omega) (by omega)
  have hidx : p + 1 - 2 * (s - 1) = p + 3 - 2 * s := by omega
  rw [h0, h1, h2, h3, h4, hidx]
  cases lineStep k u constant g (s - 1) (p - 1) <;>
  cases lineStep k u constant g (s - 1) p <;>
  cases lineStep k u constant g (s - 1) (p + 1) <;>
  cases lineStep k u constant g (s - 1) (p + 2) <;>
  cases lineStep k u constant g (s - 1) (p + 3) <;>
  cases u.val.testBit ((p + 3 - 2 * s) % k) <;>
  cases (constant (s - 1 + 1)).val.testBit (p % k) <;>
  cases f (p + 3 - 2 * s) <;>
  cases g (p + 3 - 2 * s) <;> rfl

theorem bit_succ_eq {k : Nat} (hk : 2 ≤ k) (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (s key p : Nat) (hp : 1 ≤ p) :
    let bit := fun r pos => (stateAt k u constant r key).testBit (pos % k)
    let m := fun pos => xor (xor (bit s (pos - 1)) (bit s pos)) (bit s (pos + 1))
    bit (s + 1) p =
      xor (xor (m p) (!(m (p + 1)) && m (p + 2)))
        (xor ((rot k (2 * s) key).testBit (p % k)) ((constant (s + 1)).val.testBit (p % k))) := by
  intro bit m
  have hk_pos : 0 < k := by omega
  simp only [bit]
  rw [stateAt_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk_pos)]
  unfold stepBit
  have hm : ∀ d, (mix k (stateAt k u constant s key)).testBit ((p % k + d) % k) = m (p + d) := by
    intro d
    have hlt : (p % k + d) % k < k := Nat.mod_lt _ hk_pos
    rw [testBit_mix hk (stateAt_lt k u constant s key) hlt]
    have h0 : (p % k + d) % k = (p + d) % k := Nat.mod_add_mod p k d
    have h1 : ((p + d) % k + k - 1) % k = (p + d - 1) % k := by
      have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
      conv_lhs => rw [h1m]
      exact mod_sub_eq hk_pos (by omega)
    have h2 : ((p + d) % k + 1) % k = (p + d + 1) % k := Nat.mod_add_mod (p + d) k 1
    rw [h0, h1, h2]
    simp only [m, bit]
    cases (stateAt k u constant s key).testBit ((p + d) % k) <;>
    cases (stateAt k u constant s key).testBit ((p + d - 1) % k) <;>
    cases (stateAt k u constant s key).testBit ((p + d + 1) % k) <;> rfl
  have hm0 := hm 0
  simp only [Nat.add_zero, Nat.mod_mod] at hm0
  rw [hm0, hm 1, hm 2]
  cases m p <;> cases m (p + 1) <;> cases m (p + 2) <;>
  cases (rot k (2 * s) key).testBit (p % k) <;>
  cases (constant (s + 1)).val.testBit (p % k) <;> rfl

theorem length_filter_range_eq_card_fin (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x.val = true)).card := by
  have h1 : ((List.range N).filter p).length =
      ((Finset.range N).filter (fun n => p n = true)).card := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [List.range_succ, List.filter_append, List.length_append, Finset.range_add_one,
          Finset.filter_insert]
      by_cases h : p N = true
      · simp [h, ih, Finset.card_insert_of_notMem]
      · have hf : p N = false := Bool.eq_false_iff.2 h
        simp [h, hf, ih]
  rw [h1]
  refine Finset.card_bij (fun n hn => ⟨n, Finset.mem_range.1 (Finset.mem_filter.1 hn).1⟩) ?_ ?_ ?_
  · intro n hn
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hn).2⟩
  · intro n1 _ n2 _ heq
    exact congrArg Fin.val heq
  · intro x hx
    exact ⟨x.val, Finset.mem_filter.2 ⟨Finset.mem_range.2 x.isLt, (Finset.mem_filter.1 hx).2⟩, rfl⟩

def gain5 (b : Bool × Bool × Bool × Bool × Bool) : Nat :=
  let (f0, f1, f2, f3, f4) := b
  let next := if f0 then f3 else f4
  let extra := f0 && next && (!f2) && (!f1)
  f0.toNat + next.toNat + extra.toNat

theorem card_gain5 :
    ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 0)).card = 8 ∧
    ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 1)).card = 16 ∧
    ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 2)).card = 6 ∧
    ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 3)).card = 2 := by
  decide

theorem eq_of_false_eq_xor {x y : Bool} (h : false = xor x y) : x = y := by
  cases x <;> cases y <;> simp_all

theorem mod_eq_iff_lt {k a b c : Nat} (ha : a < k) (hb : b < k) :
    (c + a) % k = (c + b) % k ↔ a = b := by
  constructor
  · intro h
    have hk : 0 < k := by omega
    have hc := Nat.mod_lt c hk
    set r := c % k
    have h1 : (r + a) % k = (r + b) % k := by rwa [Nat.mod_add_mod, Nat.mod_add_mod]
    by_cases h1lt : r + a < k <;> by_cases h2lt : r + b < k
    · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at h1; omega
    · rw [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2lt] at h1; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h1; omega
  · intro h; subst h; rfl

theorem main (k t lo width : Nat) (ht : 5 ≤ t) (hk : 5 * t + 1 ≤ k) (hwidth : 8 ≤ width)
    (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) :
    let rot0 := fun (s word : Nat) =>
      ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
    let step0 := fun (word : Nat) =>
      (List.range k).foldl (fun acc j =>
        acc ||| ((xor (word.testBit j)
          (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
    let state := fun (rounds key : Nat) =>
      (List.range rounds).foldl (fun prev tick =>
        step0 (prev ^^^ rot0 1 prev ^^^ rot0 (k - 1) prev) ^^^ rot0 (2 * tick) key ^^^
          (constant (tick + 1)).val) (rot0 1 key ^^^ u.val)
    let edge := lo + width
    let injected := fun (round key pos : Nat) =>
      xor ((rot0 (2 * (round - 1)) key).testBit (pos % k))
        ((constant round).val.testBit (pos % k))
    let bit := fun (round key pos : Nat) => (state round key).testBit (pos % k)
    let guard := fun (round key stop : Nat) =>
      xor (xor (bit round key (stop - 2)) (bit round key (stop - 1))) (bit round key stop)
    let gain := fun (raw : Nat) =>
      let hit := guard (t - 1) raw edge
      let mid := edge - 3 + hit.toNat
      let next := guard t raw mid
      let extra := hit && next &&
        (bit t raw (edge - 3) == injected t raw edge) &&
        (bit t raw (edge - 2) == xor (injected t raw (edge - 1)) (injected t raw edge))
      hit.toNat + next.toNat + extra.toNat
    let unit := 2 ^ (k - 4)
    ((List.range 4).map (fun g =>
      ((List.range (2 ^ k)).filter (fun w => gain w == g)).length)) =
        [4 * unit, 8 * unit, 3 * unit, unit] ∧
    (∀ a z : Fin (2 ^ k),
      (∀ j : Nat, lo ≤ j → j ≤ edge → bit (t - 1) a.val j = bit (t - 1) z.val j) →
      (∀ j : Nat, lo + 1 ≤ j → j ≤ edge → injected t a.val j = injected t z.val j) →
      (∀ j : Nat, lo + 2 ≤ j → j ≤ edge → injected (t + 1) a.val j = injected (t + 1) z.val j) →
      gain a.val = gain z.val ∧
        ∀ pos : Nat, lo + 2 ≤ pos → pos ≤ edge - 6 + gain a.val →
          bit (t + 1) a.val pos = bit (t + 1) z.val pos) := by
  classical
  intro rot0 step0 state edge injected bit guard gain unit
  have hk_pos : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  constructor
  · let E' := edge + 5 * k
    have hE'_mod : ∀ d, d ≤ edge → (E' - d) % k = (edge - d) % k := by
      intro d hd
      have : E' - d = (edge - d) + k * 5 := by simp only [E']; omega
      rw [this, Nat.add_mul_mod_self_left]
    let src : Fin (2 ^ k) → Nat → Bool := fun w pos => (rot k 1 w.val ^^^ u.val).testBit (pos % k)
    let f0 : Fin (2 ^ k) → Bool := fun w => guard (t - 1) w.val edge
    let f1 : Fin (2 ^ k) → Bool := fun w =>
      xor (bit t w.val (edge - 2)) (xor (injected t w.val (edge - 1)) (injected t w.val edge))
    let f2 : Fin (2 ^ k) → Bool := fun w =>
      xor (bit t w.val (edge - 3)) (injected t w.val edge)
    let f3 : Fin (2 ^ k) → Bool := fun w => guard t w.val (edge - 2)
    let f4 : Fin (2 ^ k) → Bool := fun w => guard t w.val (edge - 3)
    have hgain_eq : ∀ w : Fin (2 ^ k), gain w.val = gain5 (f0 w, f1 w, f2 w, f3 w, f4 w) := by
      intro w
      simp only [gain, gain5, f0, f1, f2, f3, f4]
      have hmid_eq : (if guard (t - 1) w.val edge = true then guard t w.val (edge - 2)
          else guard t w.val (edge - 3)) =
          guard t w.val (edge - 3 + (guard (t - 1) w.val edge).toNat) := by
        cases guard (t - 1) w.val edge
        · simp
        · simp only [Bool.toNat_true, ↓reduceIte]
          congr 1; omega
      rw [hmid_eq]
      have hbeq : ∀ x y : Bool, (x == y) = !(xor x y) := by
        intro x y; cases x <;> cases y <;> rfl
      rw [hbeq (bit t w.val (edge - 3)), hbeq (bit t w.val (edge - 2))]
    let base := E' - 2 - 2 * t
    have hbase_le : base + (5 * t + 1) ≤ E' + 3 * t := by simp only [base]; omega
    let p0 : Fin k := ⟨(base + 5) % k, Nat.mod_lt _ hk_pos⟩
    let p1 : Fin k := ⟨(base + 3) % k, Nat.mod_lt _ hk_pos⟩
    let p2 : Fin k := ⟨(base + 2) % k, Nat.mod_lt _ hk_pos⟩
    let p3 : Fin k := ⟨(base + 1) % k, Nat.mod_lt _ hk_pos⟩
    let p4 : Fin k := ⟨(base + 0) % k, Nat.mod_lt _ hk_pos⟩
    have hp_ne : ∀ a b, a < 5 * t + 1 → b < 5 * t + 1 → a ≠ b → (base + a) % k ≠ (base + b) % k := by
      intro a b ha hb hab h
      exact hab ((mod_eq_iff_lt (by omega : a < k) (by omega : b < k)).1 h)
    let pivSet : Finset (Fin k) := {p0, p1, p2, p3, p4}
    have hpivSet_card : pivSet.card = 5 := by
      have hne : ∀ a b, a < 5 * t + 1 → b < 5 * t + 1 → a ≠ b →
          (⟨(base + a) % k, Nat.mod_lt _ hk_pos⟩ : Fin k) ≠ ⟨(base + b) % k, Nat.mod_lt _ hk_pos⟩ :=
        fun a b ha hb hab h => hp_ne a b ha hb hab (congrArg Fin.val h)
      have h01 : p0 ≠ p1 := hne 5 3 (by omega) (by omega) (by omega)
      have h02 : p0 ≠ p2 := hne 5 2 (by omega) (by omega) (by omega)
      have h03 : p0 ≠ p3 := hne 5 1 (by omega) (by omega) (by omega)
      have h04 : p0 ≠ p4 := hne 5 0 (by omega) (by omega) (by omega)
      have h12 : p1 ≠ p2 := hne 3 2 (by omega) (by omega) (by omega)
      have h13 : p1 ≠ p3 := hne 3 1 (by omega) (by omega) (by omega)
      have h14 : p1 ≠ p4 := hne 3 0 (by omega) (by omega) (by omega)
      have h23 : p2 ≠ p3 := hne 2 1 (by omega) (by omega) (by omega)
      have h24 : p2 ≠ p4 := hne 2 0 (by omega) (by omega) (by omega)
      have h34 : p3 ≠ p4 := hne 1 0 (by omega) (by omega) (by omega)
      rw [Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
          Finset.card_insert_of_notMem (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto),
          Finset.card_pair h34]
    let Ψ : Fin (2 ^ k) → (Bool × Bool × Bool × Bool × Bool) × ({j : Fin k // j ∉ pivSet} → Bool) :=
      fun w => ((f0 w, f1 w, f2 w, f3 w, f4 w), fun j => src w j.1.val)
    have hbit_line : ∀ w : Fin (2 ^ k), ∀ s d, s ≤ t → d ≤ 5 →
        bit s w.val (edge - d) = lineStep k u constant (src w) s (E' - d) := by
      intro w s d hs hd
      have h1 := lineStep_eq_stateAt hk2 u constant w s (E' - d) (by simp only [E']; omega)
      rw [h1, hE'_mod d (by omega)]
      rfl
    have hinj_src : ∀ w : Fin (2 ^ k), ∀ d, d ≤ 2 →
        injected t w.val (edge - d) =
          xor (xor (src w (E' - d + 3 - 2 * t)) (u.val.testBit ((E' - d + 3 - 2 * t) % k)))
            ((constant t).val.testBit ((E' - d) % k)) := by
      intro w d hd
      simp only [injected, hE'_mod d (by omega), src, Nat.testBit_xor]
      have hrot1 : (rot k 1 w.val).testBit ((E' - d + 3 - 2 * t) % k) =
          w.val.testBit ((E' - d + 2 - 2 * t) % k) := by
        rw [testBit_rot w.isLt (Nat.mod_lt _ hk_pos)]
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hsub : E' - d + 3 - 2 * t - 1 = E' - d + 2 - 2 * t := by simp only [E']; omega
        rw [← hsub]
        have h1' := mod_sub_eq hk_pos (p := E' - d + 3 - 2 * t) (s := 1) (by simp only [E']; omega)
        rw [h1m] at h1' ⊢
        exact congrArg w.val.testBit h1'
      have hrot2 : (rot0 (2 * (t - 1)) w.val).testBit ((edge - d) % k) =
          w.val.testBit ((E' - d + 2 - 2 * t) % k) := by
        change (rot k (2 * (t - 1)) w.val).testBit ((edge - d) % k) = _
        rw [← hE'_mod d (by omega), testBit_rot w.isLt (Nat.mod_lt _ hk_pos),
            mod_sub_eq hk_pos (by simp only [E']; omega)]
        congr 1; congr 1; simp only [E']; omega
      rw [hrot1, hrot2]
      cases w.val.testBit ((E' - d + 2 - 2 * t) % k) <;>
      cases u.val.testBit ((E' - d + 3 - 2 * t) % k) <;>
      cases (constant t).val.testBit ((edge - d) % k) <;> rfl
    have hΨ_inj : Function.Injective Ψ := by
      intro a z heq
      have h5 : (f0 a, f1 a, f2 a, f3 a, f4 a) = (f0 z, f1 z, f2 z, f3 z, f4 z) := congrArg Prod.fst heq
      have hf0 : f0 a = f0 z := congrArg Prod.fst h5
      have hf1 : f1 a = f1 z := congrArg (fun x => x.2.1) h5
      have hf2 : f2 a = f2 z := congrArg (fun x => x.2.2.1) h5
      have hf3 : f3 a = f3 z := congrArg (fun x => x.2.2.2.1) h5
      have hf4 : f4 a = f4 z := congrArg (fun x => x.2.2.2.2) h5
      have hnon : ∀ j : Fin k, j ∉ pivSet → src a j.val = src z j.val :=
        fun j hj => congrFun (congrArg Prod.snd heq) ⟨j, hj⟩
      have hsrc_mod : ∀ q, src a q = src z q ↔ src a (q % k) = src z (q % k) := by
        intro q; simp only [src, Nat.mod_mod]
      have hag_ge6 : ∀ q, base + 6 ≤ q → q ≤ E' + 3 * t - 2 → src a q = src z q := by
        intro q hq1 hq2
        rw [hsrc_mod]
        let j : Fin k := ⟨q % k, Nat.mod_lt _ hk_pos⟩
        have hj : j ∉ pivSet := by
          simp only [pivSet, Finset.mem_insert, Finset.mem_singleton]
          have hq_eq : q = base + (q - base) := by omega
          have hqd : q - base < 5 * t + 1 := by simp only [base, E'] at hq2 ⊢; omega
          rintro (h | h | h | h | h) <;>
          · have hv := congrArg Fin.val h; simp only [j, p0, p1, p2, p3, p4] at hv
            rw [hq_eq] at hv
            exact hp_ne (q - base) _ hqd (by omega) (by omega) hv
        exact hnon j hj
      have hp0_eq : src a (base + 5) = src z (base + 5) := by
        have h1 := lineStep_xor_pivot k u constant (src a) (src z) (t - 1) (E' - 2) (by omega)
          (by simp only [E']; omega) (fun q hq1 hq2 => hag_ge6 q (by simp only [base]; omega) (by omega))
        have h2 := lineStep_agree_interval k u constant (src a) (src z) (base + 6) (E' + 3 * t - 2) hag_ge6
          (t - 1) (E' - 1) (by simp only [base]; omega) (by omega)
        have h3 := lineStep_agree_interval k u constant (src a) (src z) (base + 6) (E' + 3 * t - 2) hag_ge6
          (t - 1) E' (by simp only [base]; omega) (by omega)
        have hidx : E' - 2 + 3 - 2 * (t - 1) = base + 5 := by simp only [base, E']; omega
        rw [hidx] at h1
        have hguard_eq : xor (f0 a) (f0 z) = xor (lineStep k u constant (src a) (t - 1) (E' - 2))
            (lineStep k u constant (src z) (t - 1) (E' - 2)) := by
          simp only [f0, guard]
          have e0a := hbit_line a (t - 1) 0 (by omega) (by omega)
          have e0z := hbit_line z (t - 1) 0 (by omega) (by omega)
          simp only [Nat.sub_zero] at e0a e0z
          rw [hbit_line a (t - 1) 2 (by omega) (by omega), hbit_line a (t - 1) 1 (by omega) (by omega), e0a,
              hbit_line z (t - 1) 2 (by omega) (by omega), hbit_line z (t - 1) 1 (by omega) (by omega), e0z,
              h2, h3]
          cases lineStep k u constant (src a) (t - 1) (E' - 2) <;>
          cases lineStep k u constant (src z) (t - 1) (E' - 2) <;>
          cases lineStep k u constant (src z) (t - 1) (E' - 1) <;>
          cases lineStep k u constant (src z) (t - 1) E' <;> rfl
        rw [hf0, Bool.xor_self, h1] at hguard_eq
        exact eq_of_false_eq_xor hguard_eq
      have hag_ge4 : ∀ q, base + 4 ≤ q → q ≤ E' + 3 * t - 2 → src a q = src z q := by
        intro q hq1 hq2
        by_cases h5' : q = base + 5
        · subst h5'; exact hp0_eq
        · by_cases h4' : q = base + 4
          · subst h4'
            rw [hsrc_mod]
            let j : Fin k := ⟨(base + 4) % k, Nat.mod_lt _ hk_pos⟩
            have hj : j ∉ pivSet := by
              simp only [pivSet, Finset.mem_insert, Finset.mem_singleton]
              rintro (h | h | h | h | h) <;>
              · have hv := congrArg Fin.val h; simp only [j, p0, p1, p2, p3, p4] at hv
                exact hp_ne 4 _ (by omega) (by omega) (by omega) hv
            exact hnon j hj
          · exact hag_ge6 q (by omega) hq2
      have hp1_eq : src a (base + 3) = src z (base + 3) := by
        have h1 := lineStep_xor_pivot k u constant (src a) (src z) t (E' - 2) (by omega)
          (by simp only [E']; omega) (fun q hq1 hq2 => hag_ge4 q (by simp only [base]; omega) (by omega))
        have hidx : E' - 2 + 3 - 2 * t = base + 3 := by simp only [base, E']; omega
        rw [hidx] at h1
        have hi0 : injected t a.val edge = injected t z.val edge := by
          have ea := hinj_src a 0 (by omega)
          have ez := hinj_src z 0 (by omega)
          simp only [Nat.sub_zero] at ea ez
          rw [ea, ez, hag_ge4 (E' + 3 - 2 * t) (by simp only [base]; omega) (by simp only [E']; omega)]
        have hi1 : injected t a.val (edge - 1) = injected t z.val (edge - 1) := by
          rw [hinj_src a 1 (by omega), hinj_src z 1 (by omega),
              hag_ge4 (E' - 1 + 3 - 2 * t) (by simp only [base]; omega) (by simp only [E']; omega)]
        have hf1_eq : xor (f1 a) (f1 z) = xor (lineStep k u constant (src a) t (E' - 2))
            (lineStep k u constant (src z) t (E' - 2)) := by
          simp only [f1, hbit_line a t 2 (le_refl _) (by omega), hbit_line z t 2 (le_refl _) (by omega), hi0, hi1]
          cases lineStep k u constant (src a) t (E' - 2) <;>
          cases lineStep k u constant (src z) t (E' - 2) <;>
          cases injected t z.val (edge - 1) <;> cases injected t z.val edge <;> rfl
        rw [hf1, Bool.xor_self, h1] at hf1_eq
        exact eq_of_false_eq_xor hf1_eq
      have hag_ge3 : ∀ q, base + 3 ≤ q → q ≤ E' + 3 * t - 2 → src a q = src z q := by
        intro q hq1 hq2
        by_cases h3' : q = base + 3
        · subst h3'; exact hp1_eq
        · exact hag_ge4 q (by omega) hq2
      have hp2_eq : src a (base + 2) = src z (base + 2) := by
        have h1 := lineStep_xor_pivot k u constant (src a) (src z) t (E' - 3) (by omega)
          (by simp only [E']; omega) (fun q hq1 hq2 => hag_ge3 q (by simp only [base]; omega) (by omega))
        have hidx : E' - 3 + 3 - 2 * t = base + 2 := by simp only [base, E']; omega
        rw [hidx] at h1
        have hi0 : injected t a.val edge = injected t z.val edge := by
          have ea := hinj_src a 0 (by omega)
          have ez := hinj_src z 0 (by omega)
          simp only [Nat.sub_zero] at ea ez
          rw [ea, ez, hag_ge3 (E' + 3 - 2 * t) (by simp only [base]; omega) (by simp only [E']; omega)]
        have hf2_eq : xor (f2 a) (f2 z) = xor (lineStep k u constant (src a) t (E' - 3))
            (lineStep k u constant (src z) t (E' - 3)) := by
          simp only [f2, hbit_line a t 3 (le_refl _) (by omega), hbit_line z t 3 (le_refl _) (by omega), hi0]
          cases lineStep k u constant (src a) t (E' - 3) <;>
          cases lineStep k u constant (src z) t (E' - 3) <;>
          cases injected t z.val edge <;> rfl
        rw [hf2, Bool.xor_self, h1] at hf2_eq
        exact eq_of_false_eq_xor hf2_eq
      have hag_ge2 : ∀ q, base + 2 ≤ q → q ≤ E' + 3 * t - 2 → src a q = src z q := by
        intro q hq1 hq2
        by_cases h2' : q = base + 2
        · subst h2'; exact hp2_eq
        · exact hag_ge3 q (by omega) hq2
      have hp3_eq : src a (base + 1) = src z (base + 1) := by
        have h1 := lineStep_xor_pivot k u constant (src a) (src z) t (E' - 4) (by omega)
          (by simp only [E']; omega) (fun q hq1 hq2 => hag_ge2 q (by simp only [base]; omega) (by omega))
        have h2 := lineStep_agree_interval k u constant (src a) (src z) (base + 2) (E' + 3 * t - 2) hag_ge2
          t (E' - 3) (by simp only [base]; omega) (by omega)
        have h3 := lineStep_agree_interval k u constant (src a) (src z) (base + 2) (E' + 3 * t - 2) hag_ge2
          t (E' - 2) (by simp only [base]; omega) (by omega)
        have hidx : E' - 4 + 3 - 2 * t = base + 1 := by simp only [base, E']; omega
        rw [hidx] at h1
        have hf3_eq : xor (f3 a) (f3 z) = xor (lineStep k u constant (src a) t (E' - 4))
            (lineStep k u constant (src z) t (E' - 4)) := by
          simp only [f3, guard]
          have e4 : edge - 2 - 2 = edge - 4 := by omega
          have e3 : edge - 2 - 1 = edge - 3 := by omega
          rw [e4, e3, hbit_line a t 4 (le_refl _) (by omega), hbit_line a t 3 (le_refl _) (by omega),
              hbit_line a t 2 (le_refl _) (by omega), hbit_line z t 4 (le_refl _) (by omega),
              hbit_line z t 3 (le_refl _) (by omega), hbit_line z t 2 (le_refl _) (by omega), h2, h3]
          cases lineStep k u constant (src a) t (E' - 4) <;>
          cases lineStep k u constant (src z) t (E' - 4) <;>
          cases lineStep k u constant (src z) t (E' - 3) <;>
          cases lineStep k u constant (src z) t (E' - 2) <;> rfl
        rw [hf3, Bool.xor_self, h1] at hf3_eq
        exact eq_of_false_eq_xor hf3_eq
      have hag_ge1 : ∀ q, base + 1 ≤ q → q ≤ E' + 3 * t - 2 → src a q = src z q := by
        intro q hq1 hq2
        by_cases h1' : q = base + 1
        · subst h1'; exact hp3_eq
        · exact hag_ge2 q (by omega) hq2
      have hp4_eq : src a (base + 0) = src z (base + 0) := by
        have h1 := lineStep_xor_pivot k u constant (src a) (src z) t (E' - 5) (by omega)
          (by simp only [E']; omega) (fun q hq1 hq2 => hag_ge1 q (by simp only [base]; omega) (by omega))
        have h2 := lineStep_agree_interval k u constant (src a) (src z) (base + 1) (E' + 3 * t - 2) hag_ge1
          t (E' - 4) (by simp only [base]; omega) (by omega)
        have h3 := lineStep_agree_interval k u constant (src a) (src z) (base + 1) (E' + 3 * t - 2) hag_ge1
          t (E' - 3) (by simp only [base]; omega) (by omega)
        have hidx : E' - 5 + 3 - 2 * t = base + 0 := by simp only [base, E']; omega
        rw [hidx] at h1
        have hf4_eq : xor (f4 a) (f4 z) = xor (lineStep k u constant (src a) t (E' - 5))
            (lineStep k u constant (src z) t (E' - 5)) := by
          simp only [f4, guard]
          have e5 : edge - 3 - 2 = edge - 5 := by omega
          have e4 : edge - 3 - 1 = edge - 4 := by omega
          rw [e5, e4, hbit_line a t 5 (le_refl _) (by omega), hbit_line a t 4 (le_refl _) (by omega),
              hbit_line a t 3 (le_refl _) (by omega), hbit_line z t 5 (le_refl _) (by omega),
              hbit_line z t 4 (le_refl _) (by omega), hbit_line z t 3 (le_refl _) (by omega), h2, h3]
          cases lineStep k u constant (src a) t (E' - 5) <;>
          cases lineStep k u constant (src z) t (E' - 5) <;>
          cases lineStep k u constant (src z) t (E' - 4) <;>
          cases lineStep k u constant (src z) t (E' - 3) <;> rfl
        rw [hf4, Bool.xor_self, h1] at hf4_eq
        exact eq_of_false_eq_xor hf4_eq
      have hall_src : ∀ j : Fin k, src a j.val = src z j.val := by
        intro j
        by_cases hj : j ∈ pivSet
        · simp only [pivSet, Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl | rfl | rfl
          · exact (hsrc_mod _).1 hp0_eq
          · exact (hsrc_mod _).1 hp1_eq
          · exact (hsrc_mod _).1 hp2_eq
          · exact (hsrc_mod _).1 hp3_eq
          · exact (hsrc_mod _).1 hp4_eq
        · exact hnon j hj
      apply Fin.ext
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b < k
      · have hs := hall_src ⟨(b + 1) % k, Nat.mod_lt _ hk_pos⟩
        simp only [src, Nat.mod_mod, Nat.testBit_xor, testBit_rot a.isLt (Nat.mod_lt _ hk_pos),
            testBit_rot z.isLt (Nat.mod_lt _ hk_pos)] at hs
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hinv : ((b + 1) % k + k - 1 % k) % k = b := by
          rw [mod_sub_eq hk_pos (by omega)]
          simp [Nat.mod_eq_of_lt hb]
        rw [hinv] at hs
        cases hA : a.val.testBit b <;> cases hZ : z.val.testBit b <;>
          cases hU : u.val.testBit ((b + 1) % k) <;>
          rw [hA, hZ, hU] at hs <;> first | rfl | exact Bool.noConfusion hs
      · rw [Nat.testBit_lt_two_pow (a.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega))),
            Nat.testBit_lt_two_pow (z.isLt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))]
    have hcard_rhs :
        Fintype.card ((Bool × Bool × Bool × Bool × Bool) × ({j : Fin k // j ∉ pivSet} → Bool)) =
          Fintype.card (Fin (2 ^ k)) := by
      have hsub : Fintype.card {j : Fin k // j ∉ pivSet} = k - 5 := by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hpivSet_card]
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, hsub]
      have h32 : 2 * (2 * (2 * (2 * 2))) = 2 ^ 5 := by decide
      rw [h32, ← pow_add]
      congr 1; omega
    let eΨ := Equiv.ofBijective Ψ ((Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨ_inj, hcard_rhs.symm⟩)
    have hcount_g : ∀ g : Nat,
        ((List.range (2 ^ k)).filter (fun w => gain w == g)).length =
          ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = g)).card *
            2 ^ (k - 5) := by
      intro g
      rw [length_filter_range_eq_card_fin]
      have hbij :
          ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => (gain w.val == g) = true)).card =
          ((Finset.univ : Finset ((Bool × Bool × Bool × Bool × Bool) ×
            ({j : Fin k // j ∉ pivSet} → Bool))).filter (fun p => gain5 p.1 = g)).card := by
        refine Finset.card_bij (fun w _ => eΨ w) ?_ ?_ ?_
        · intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq] at hw ⊢
          change gain5 (f0 w, f1 w, f2 w, f3 w, f4 w) = g
          rw [← hgain_eq w]; exact hw
        · intro w1 _ w2 _ h; exact eΨ.injective h
        · intro p hp
          refine ⟨eΨ.symm p, ?_, eΨ.apply_symm_apply p⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, beq_iff_eq] at hp ⊢
          have hfst : (eΨ (eΨ.symm p)).1 = p.1 := congrArg Prod.fst (eΨ.apply_symm_apply p)
          rw [hgain_eq]
          change gain5 (eΨ (eΨ.symm p)).1 = g
          rw [hfst]; exact hp
      rw [hbij]
      have hprod :
          ((Finset.univ : Finset ((Bool × Bool × Bool × Bool × Bool) ×
            ({j : Fin k // j ∉ pivSet} → Bool))).filter (fun p => gain5 p.1 = g)) =
          ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = g)) ×ˢ
          (Finset.univ : Finset ({j : Fin k // j ∉ pivSet} → Bool)) := by
        ext ⟨b, r⟩; simp
      rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
          Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hpivSet_card]
    have h4 : List.range 4 = [0, 1, 2, 3] := by decide
    rw [h4, List.map_cons, List.map_cons, List.map_cons, List.map_cons, List.map_nil]
    rw [hcount_g 0, hcount_g 1, hcount_g 2, hcount_g 3]
    have hc0 : ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 0)).card = 8 := by
      convert card_gain5.1
    have hc1 : ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 1)).card = 16 := by
      convert card_gain5.2.1
    have hc2 : ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 2)).card = 6 := by
      convert card_gain5.2.2.1
    have hc3 : ((Finset.univ : Finset (Bool × Bool × Bool × Bool × Bool)).filter (fun b => gain5 b = 3)).card = 2 := by
      convert card_gain5.2.2.2
    rw [hc0, hc1, hc2, hc3]
    have hunit : unit = 2 * 2 ^ (k - 5) := by
      simp only [unit]
      have hk5 : k - 4 = (k - 5) + 1 := by omega
      rw [hk5, pow_succ]; ring
    rw [hunit]
    have h1 : 8 * 2 ^ (k - 5) = 4 * (2 * 2 ^ (k - 5)) := by ring
    have h2 : 16 * 2 ^ (k - 5) = 8 * (2 * 2 ^ (k - 5)) := by ring
    have h3 : 6 * 2 ^ (k - 5) = 3 * (2 * 2 ^ (k - 5)) := by ring
    rw [h1, h2, h3]
  · intro a z htm1 hinjt hinjt1
    have htm1_succ : t = (t - 1) + 1 := by omega
    have hm_tm1_eq : ∀ p, lo + 1 ≤ p → p ≤ edge - 1 →
        xor (xor (bit (t - 1) a.val (p - 1)) (bit (t - 1) a.val p)) (bit (t - 1) a.val (p + 1)) =
        xor (xor (bit (t - 1) z.val (p - 1)) (bit (t - 1) z.val p)) (bit (t - 1) z.val (p + 1)) := by
      intro p hp1 hp2
      rw [htm1 (p - 1) (by omega) (by omega), htm1 p (by omega) (by omega), htm1 (p + 1) (by omega) (by omega)]
    have hhit_eq : guard (t - 1) a.val edge = guard (t - 1) z.val edge := by
      simp only [guard]
      rw [htm1 (edge - 2) (by omega) (by omega), htm1 (edge - 1) (by omega) (by omega), htm1 edge (by omega) (by omega)]
    have hbit_t_step : ∀ (w : Nat) (p : Nat), 1 ≤ p →
        bit t w p =
          xor (xor (xor (xor (bit (t - 1) w (p - 1)) (bit (t - 1) w p)) (bit (t - 1) w (p + 1)))
            (!(xor (xor (bit (t - 1) w p) (bit (t - 1) w (p + 1))) (bit (t - 1) w (p + 2))) &&
             (xor (xor (bit (t - 1) w (p + 1)) (bit (t - 1) w (p + 2))) (bit (t - 1) w (p + 3)))))
            (injected t w p) := by
      intro w p hp
      have h1 := bit_succ_eq hk2 u constant (t - 1) w p hp
      rw [← htm1_succ] at h1
      have hp1 : p + 1 - 1 = p := by omega
      have hp2 : p + 2 - 1 = p + 1 := by omega
      have hp3 : p + 1 + 1 = p + 2 := by omega
      have hp4 : p + 2 + 1 = p + 3 := by omega
      dsimp only at h1
      rw [hp1, hp2, hp3, hp4] at h1
      exact h1
    have hbit_t_eq : ∀ p, lo + 1 ≤ p → p ≤ edge - 3 + (guard (t - 1) a.val edge).toNat →
        bit t a.val p = bit t z.val p := by
      intro p hp1 hp2
      have hhit_le : (guard (t - 1) a.val edge).toNat ≤ 1 := Bool.toNat_le _
      rw [hbit_t_step a.val p (by omega), hbit_t_step z.val p (by omega),
          hinjt p hp1 (by omega)]
      by_cases hlt : p ≤ edge - 3
      · rw [htm1 (p - 1) (by omega) (by omega),
            htm1 p (by omega) (by omega),
            htm1 (p + 1) (by omega) (by omega),
            htm1 (p + 2) (by omega) (by omega),
            htm1 (p + 3) (by omega) (by omega)]
      · have hhit_true : guard (t - 1) a.val edge = true := by
          cases hh : guard (t - 1) a.val edge
          · rw [hh] at hp2; simp at hp2; omega
          · rfl
        have hp_eq : p = edge - 2 := by
          rw [hhit_true] at hp2; simp at hp2; omega
        subst hp_eq
        have he1 : edge - 2 + 1 = edge - 1 := by omega
        have he2 : edge - 2 + 2 = edge := by omega
        rw [hm_tm1_eq (edge - 2) (by omega) (by omega)]
        have ha_hit : xor (xor (bit (t - 1) a.val (edge - 2)) (bit (t - 1) a.val (edge - 2 + 1)))
            (bit (t - 1) a.val (edge - 2 + 2)) = true := by
          rw [he1, he2]; exact hhit_true
        have hz_hit : xor (xor (bit (t - 1) z.val (edge - 2)) (bit (t - 1) z.val (edge - 2 + 1)))
            (bit (t - 1) z.val (edge - 2 + 2)) = true := by
          rw [he1, he2]; exact hhit_eq.symm.trans hhit_true
        rw [ha_hit, hz_hit]
        simp
    let mid := edge - 3 + (guard (t - 1) a.val edge).toNat
    have hnext_eq : guard t a.val mid = guard t z.val mid := by
      simp only [guard]
      rw [hbit_t_eq (mid - 2) (by simp only [mid]; omega) (by simp only [mid]; omega),
          hbit_t_eq (mid - 1) (by simp only [mid]; omega) (by simp only [mid]; omega),
          hbit_t_eq mid (by simp only [mid]; omega) (le_refl _)]
    have hgain_az : gain a.val = gain z.val := by
      simp only [gain]
      rw [← hhit_eq]
      change (guard (t - 1) a.val edge).toNat + (guard t a.val mid).toNat + _ =
        (guard (t - 1) a.val edge).toNat + (guard t z.val mid).toNat + _
      rw [hnext_eq]
      by_cases hhit : guard (t - 1) a.val edge = true
      · rw [hbit_t_eq (edge - 3) (by omega) (by omega),
            hbit_t_eq (edge - 2) (by omega) (by rw [hhit]; simp; omega),
            hinjt edge (by omega) (le_refl _), hinjt (edge - 1) (by omega) (by omega)]
      · have hhf : guard (t - 1) a.val edge = false := Bool.eq_false_iff.2 hhit
        simp [hhf]
    refine ⟨hgain_az, ?_⟩
    intro pos hpos1 hpos2
    have hbit_t1_step : ∀ (w : Nat) (p : Nat), 1 ≤ p →
        bit (t + 1) w p =
          xor (xor (xor (xor (bit t w (p - 1)) (bit t w p)) (bit t w (p + 1)))
            (!(xor (xor (bit t w p) (bit t w (p + 1))) (bit t w (p + 2))) &&
             (xor (xor (bit t w (p + 1)) (bit t w (p + 2))) (bit t w (p + 3)))))
            (injected (t + 1) w p) := by
      intro w p hp
      have h1 := bit_succ_eq hk2 u constant t w p hp
      have hp1 : p + 1 - 1 = p := by omega
      have hp2 : p + 2 - 1 = p + 1 := by omega
      have hp3 : p + 1 + 1 = p + 2 := by omega
      have hp4 : p + 2 + 1 = p + 3 := by omega
      dsimp only at h1
      rw [hp1, hp2, hp3, hp4] at h1
      exact h1
    have hmt_eq : ∀ p, lo + 2 ≤ p → p ≤ mid - 1 →
        xor (xor (bit t a.val (p - 1)) (bit t a.val p)) (bit t a.val (p + 1)) =
        xor (xor (bit t z.val (p - 1)) (bit t z.val p)) (bit t z.val (p + 1)) := by
      intro p hp1 hp2
      rw [hbit_t_eq (p - 1) (by omega) (by omega), hbit_t_eq p (by omega) (by omega),
          hbit_t_eq (p + 1) (by omega) (by omega)]
    have hgain_le3 : gain a.val ≤ 3 := by
      simp only [gain]
      have := Bool.toNat_le (guard (t - 1) a.val edge)
      have := Bool.toNat_le (guard t a.val (edge - 3 + (guard (t - 1) a.val edge).toNat))
      have := Bool.toNat_le (guard (t - 1) a.val edge &&
        guard t a.val (edge - 3 + (guard (t - 1) a.val edge).toNat) &&
        (bit t a.val (edge - 3) == injected t a.val edge) &&
        (bit t a.val (edge - 2) == xor (injected t a.val (edge - 1)) (injected t a.val edge)))
      omega
    rw [hbit_t1_step a.val pos (by omega), hbit_t1_step z.val pos (by omega),
        hinjt1 pos hpos1 (by omega)]
    by_cases hlt1 : pos ≤ mid - 3
    · rw [hbit_t_eq (pos - 1) (by omega) (by simp only [mid] at hlt1; omega),
          hbit_t_eq pos (by omega) (by simp only [mid] at hlt1; omega),
          hbit_t_eq (pos + 1) (by omega) (by simp only [mid] at hlt1; omega),
          hbit_t_eq (pos + 2) (by omega) (by simp only [mid] at hlt1; omega),
          hbit_t_eq (pos + 3) (by omega) (by simp only [mid] at hlt1; omega)]
    · by_cases hlt2 : pos ≤ mid - 2
      · have hpos_eq : pos = mid - 2 := by omega
        subst hpos_eq
        have hnext_true : guard t a.val mid = true := by
          cases hn : guard t a.val mid
          · simp only [gain, mid] at hpos2
            have hn' : guard t a.val (edge - 3 + (guard (t - 1) a.val edge).toNat) = false := hn
            rw [hn'] at hpos2
            simp only [Bool.and_false, Bool.false_and, Bool.toNat_false, Nat.add_zero] at hpos2
            omega
          · rfl
        have hm1 : mid - 2 + 1 = mid - 1 := by simp only [mid]; omega
        have hm2 : mid - 2 + 2 = mid := by simp only [mid]; omega
        rw [hmt_eq (mid - 2) hpos1 (by simp only [mid]; omega)]
        have ha_n : xor (xor (bit t a.val (mid - 2)) (bit t a.val (mid - 2 + 1)))
            (bit t a.val (mid - 2 + 2)) = true := by
          rw [hm1, hm2]; exact hnext_true
        have hz_n : xor (xor (bit t z.val (mid - 2)) (bit t z.val (mid - 2 + 1)))
            (bit t z.val (mid - 2 + 2)) = true := by
          rw [hm1, hm2]; exact hnext_eq.symm.trans hnext_true
        rw [ha_n, hz_n]
        simp
      · have hextra_true :
            (guard (t - 1) a.val edge && guard t a.val mid &&
              (bit t a.val (edge - 3) == injected t a.val edge) &&
              (bit t a.val (edge - 2) == xor (injected t a.val (edge - 1)) (injected t a.val edge))) = true := by
          by_contra hne
          have hf : (guard (t - 1) a.val edge && guard t a.val mid &&
              (bit t a.val (edge - 3) == injected t a.val edge) &&
              (bit t a.val (edge - 2) == xor (injected t a.val (edge - 1)) (injected t a.val edge))) = false :=
            Bool.eq_false_iff.2 hne
          simp only [gain] at hpos2
          change pos ≤ edge - 6 + ((guard (t - 1) a.val edge).toNat + (guard t a.val mid).toNat +
            (guard (t - 1) a.val edge && guard t a.val mid &&
              (bit t a.val (edge - 3) == injected t a.val edge) &&
              (bit t a.val (edge - 2) == xor (injected t a.val (edge - 1)) (injected t a.val edge))).toNat) at hpos2
          rw [hf] at hpos2
          have := Bool.toNat_le (guard t a.val mid)
          simp only [Bool.toNat_false, Nat.add_zero] at hpos2
          simp only [mid] at hlt2
          omega
        simp only [Bool.and_eq_true, beq_iff_eq] at hextra_true
        rcases hextra_true with ⟨⟨⟨hhit_t, hnext_t⟩, halign1_a⟩, halign2_a⟩
        have hmid_e2 : mid = edge - 2 := by simp only [mid, hhit_t, Bool.toNat_true]; omega
        have hpos_e3 : pos = edge - 3 := by
          rw [hmid_e2] at hlt2
          omega
        subst hpos_e3
        rw [hmt_eq (edge - 3) hpos1 (by rw [hmid_e2]; omega)]
        have hnl_false : ∀ (w : Fin (2 ^ k)),
            guard (t - 1) w.val edge = true →
            bit t w.val (edge - 3) = injected t w.val edge →
            bit t w.val (edge - 2) = xor (injected t w.val (edge - 1)) (injected t w.val edge) →
            (!(xor (xor (bit t w.val (edge - 3)) (bit t w.val (edge - 3 + 1))) (bit t w.val (edge - 3 + 2))) &&
             (xor (xor (bit t w.val (edge - 3 + 1)) (bit t w.val (edge - 3 + 2))) (bit t w.val (edge - 3 + 3)))) = false := by
          intro w hw_hit hw_a1 hw_a2
          have e1 : edge - 3 + 1 = edge - 2 := by omega
          have e2 : edge - 3 + 2 = edge - 1 := by omega
          have e3 : edge - 3 + 3 = edge := by omega
          rw [e1, e2, e3, hw_a1, hw_a2]
          rw [hbit_t_step w.val (edge - 1) (by omega), hbit_t_step w.val edge (by omega)]
          have f1 : edge - 1 - 1 = edge - 2 := by omega
          have f2 : edge - 1 + 1 = edge := by omega
          have f3 : edge - 1 + 2 = edge + 1 := by omega
          have f4 : edge - 1 + 3 = edge + 2 := by omega
          rw [f1, f2, f3, f4]
          have hhit_w : xor (xor (bit (t - 1) w.val (edge - 2)) (bit (t - 1) w.val (edge - 1)))
              (bit (t - 1) w.val edge) = true := hw_hit
          rw [hhit_w]
          set α := xor (xor (bit (t - 1) w.val (edge - 1)) (bit (t - 1) w.val edge)) (bit (t - 1) w.val (edge + 1))
          set β := xor (xor (bit (t - 1) w.val edge) (bit (t - 1) w.val (edge + 1))) (bit (t - 1) w.val (edge + 2))
          set γ := xor (xor (bit (t - 1) w.val (edge + 1)) (bit (t - 1) w.val (edge + 2))) (bit (t - 1) w.val (edge + 3))
          cases α <;> cases β <;> cases γ <;>
          cases injected t w.val (edge - 1) <;> cases injected t w.val edge <;> rfl
        have halign1_z : bit t z.val (edge - 3) = injected t z.val edge := by
          rw [← hbit_t_eq (edge - 3) (by omega) (by omega),
              ← hinjt edge (by omega) (le_refl _)]
          exact halign1_a
        have halign2_z : bit t z.val (edge - 2) = xor (injected t z.val (edge - 1)) (injected t z.val edge) := by
          rw [← hbit_t_eq (edge - 2) (by omega) (by rw [hhit_t]; simp; omega),
              ← hinjt (edge - 1) (by omega) (by omega), ← hinjt edge (by omega) (le_refl _)]
          exact halign2_a
        rw [hnl_false a hhit_t halign1_a halign2_a,
            hnl_false z (hhit_eq.symm.trans hhit_t) halign1_z halign2_z]

end PEqualNP.Outside.L_meta_25531_aux

theorem PEqualNP.Outside.L_meta_25531 :
∀ (k t lo width : Nat), 5 ≤ t → 5 * t + 1 ≤ k → 8 ≤ width →
  ∀ (u : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let state := fun (rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ u.val)
  let edge := lo + width
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (round key pos : Nat) => (state round key).testBit (pos % k)
  let guard := fun (round key stop : Nat) =>
    xor (xor (bit round key (stop - 2)) (bit round key (stop - 1))) (bit round key stop)
  let gain := fun (raw : Nat) =>
    let hit := guard (t - 1) raw edge
    let mid := edge - 3 + hit.toNat
    let next := guard t raw mid
    let extra := hit && next &&
      (bit t raw (edge - 3) == injected t raw edge) &&
      (bit t raw (edge - 2) == xor (injected t raw (edge - 1)) (injected t raw edge))
    hit.toNat + next.toNat + extra.toNat
  let unit := 2 ^ (k - 4)
  ((List.range 4).map (fun g =>
    ((List.range (2 ^ k)).filter (fun w => gain w == g)).length)) =
      [4 * unit, 8 * unit, 3 * unit, unit] ∧
  (∀ a z : Fin (2 ^ k),
    (∀ j : Nat, lo ≤ j → j ≤ edge → bit (t - 1) a.val j = bit (t - 1) z.val j) →
    (∀ j : Nat, lo + 1 ≤ j → j ≤ edge → injected t a.val j = injected t z.val j) →
    (∀ j : Nat, lo + 2 ≤ j → j ≤ edge → injected (t + 1) a.val j = injected (t + 1) z.val j) →
    gain a.val = gain z.val ∧
      ∀ pos : Nat, lo + 2 ≤ pos → pos ≤ edge - 6 + gain a.val →
        bit (t + 1) a.val pos = bit (t + 1) z.val pos) :=
  PEqualNP.Outside.L_meta_25531_aux.main
