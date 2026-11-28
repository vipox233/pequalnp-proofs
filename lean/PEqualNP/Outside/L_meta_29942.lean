import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29942_aux

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

theorem src_inj_eq {k : Nat} (hk : 2 ≤ k) (u key : Fin (2 ^ k)) (s p : Nat) (hp : 2 * s ≤ p) :
    xor ((rot k 1 key.val ^^^ u.val).testBit ((p + 1 - 2 * s) % k))
      (u.val.testBit ((p + 1 - 2 * s) % k)) =
      (rot k (2 * s) key.val).testBit (p % k) := by
  have hk_pos : 0 < k := by omega
  simp only [Nat.testBit_xor]
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
    rw [hm0, hm1, hm2, src_inj_eq hk u key s p (by omega)]


def round2Expr (o6 o8 a b d c2 : Bool) (sym : Fin 3 → Bool) : Bool :=
  let y4 := b
  let y5 := xor b (!a)
  let y6 := xor a (xor o6 (sym 0))
  let y7 := xor (!(xor o6 (sym 0)) && xor (xor (sym 0) o8) (sym 1)) b
  let y8 := xor (!(xor (xor (sym 0) o8) (sym 1)) && xor (xor (sym 1) (sym 0)) (sym 2)) d
  let m0 := xor (xor y5 y4) y6
  let m1 := xor (xor y6 y5) y7
  let m2 := xor (xor y7 y6) y8
  xor (xor m0 (!m1 && m2)) c2

theorem guarded_row_eval {k : Nat} (hk : 2 ≤ k) (constant : Nat → Fin (2 ^ k))
    (row ref key : Fin (2 ^ k)) (p : Nat)
    (hagree : ∀ j : Fin 9,
      (stateAt k row constant 0 key.val).testBit ((p + j.val) % k) =
        (stateAt k row constant 0 ref.val).testBit ((p + j.val) % k))
    (hgood :
      let old := fun j : Nat => (stateAt k row constant 0 ref.val).testBit ((p + j) % k)
      let first := fun j : Nat => (stateAt k row constant 1 ref.val).testBit ((p + j) % k)
      let tau := xor (xor (old 6) (old 7)) (old 8)
      let al := xor (xor (xor (old 5) (old 6)) (old 7))
        (xor ((rot k (2 * (1 - 1)) ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
      let be := xor tau
        (xor ((rot k (2 * (1 - 1)) ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
      tau = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
        xor (first 4) (first 5) = !al ∧ first 4 = be) :
    let old := fun j : Nat => (stateAt k row constant 0 ref.val).testBit ((p + j) % k)
    let al := xor (xor (xor (old 5) (old 6)) (old 7))
      (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
    let be := xor (xor (xor (old 6) (old 7)) (old 8))
      (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
    let de := xor (xor (old 6) (row.val.testBit ((p + 9) % k))) ((constant 1).val.testBit ((p + 8) % k))
    let c2 := xor (xor (old 4) (row.val.testBit ((p + 4) % k))) ((constant 2).val.testBit ((p + 5) % k))
    let sym : Fin 3 → Bool := fun v => (stateAt k row constant 0 key.val).testBit ((p + 9 + v.val) % k)
    (stateAt k row constant 2 key.val).testBit ((p + 5) % k) =
      round2Expr (old 6) (old 8) al be de c2 sym := by
  dsimp only at hgood ⊢
  rcases hgood with ⟨htau, _, hf45, hf4⟩
  set srcK : Nat → Bool := fun pos => (rot k 1 key.val ^^^ row.val).testBit (pos % k)
  set srcR : Nat → Bool := fun pos => (rot k 1 ref.val ^^^ row.val).testBit (pos % k)
  have hsrc : ∀ j : Nat, j < 9 → srcK (p + j) = srcR (p + j) := fun j hj => hagree ⟨j, hj⟩
  have hlsK := lineStep_eq_stateAt hk row constant key
  have hlsR := lineStep_eq_stateAt hk row constant ref
  have hout : (stateAt k row constant 2 key.val).testBit ((p + 5) % k) =
      lineStep k row constant srcK 2 (p + 5) := (hlsK 2 (p + 5) (by omega)).symm
  rw [hout, lineStep_succ]
  have h5m1 : p + 5 - 1 = p + 4 := by omega
  have h5p1 : p + 5 + 1 = p + 6 := by omega
  have h5p2 : p + 5 + 2 = p + 7 := by omega
  have h5p3 : p + 5 + 3 = p + 8 := by omega
  have h5i : p + 5 + 1 - 2 * 1 = p + 4 := by omega
  rw [h5m1, h5p1, h5p2, h5p3, h5i, hsrc 4 (by omega)]
  have hy4 : lineStep k row constant srcK 1 (p + 4) =
      xor (xor (xor (srcR (p + 6)) (srcR (p + 7))) (srcR (p + 8)))
        (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k))) := by
    have heq : lineStep k row constant srcK 1 (p + 4) = lineStep k row constant srcR 1 (p + 4) := by
      rw [lineStep_succ, lineStep_succ]
      simp only [lineStep]
      have ha : p + 4 - 1 = p + 3 := by omega
      have hb : p + 4 + 1 = p + 5 := by omega
      have hc : p + 4 + 2 = p + 6 := by omega
      have hd : p + 4 + 3 = p + 7 := by omega
      have he : p + 4 + 1 - 2 * 0 = p + 5 := by omega
      rw [ha, hb, hc, hd, he, hsrc 3 (by omega), hsrc 4 (by omega), hsrc 5 (by omega),
        hsrc 6 (by omega), hsrc 7 (by omega)]
    rw [heq, hlsR 1 (p + 4) (by omega)]
    exact hf4
  have hy5 : lineStep k row constant srcK 1 (p + 5) =
      xor (xor (xor (xor (srcR (p + 6)) (srcR (p + 7))) (srcR (p + 8)))
        (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k))))
        (!(xor (xor (xor (srcR (p + 5)) (srcR (p + 6))) (srcR (p + 7)))
          (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))))) := by
    have heq : lineStep k row constant srcK 1 (p + 5) = lineStep k row constant srcR 1 (p + 5) := by
      rw [lineStep_succ, lineStep_succ]
      simp only [lineStep]
      have ha : p + 5 - 1 = p + 4 := by omega
      have hb : p + 5 + 1 = p + 6 := by omega
      have hc : p + 5 + 2 = p + 7 := by omega
      have hd : p + 5 + 3 = p + 8 := by omega
      have he : p + 5 + 1 - 2 * 0 = p + 6 := by omega
      rw [ha, hb, hc, hd, he, hsrc 4 (by omega), hsrc 5 (by omega), hsrc 6 (by omega),
        hsrc 7 (by omega), hsrc 8 (by omega)]
    rw [heq, hlsR 1 (p + 5) (by omega)]
    rw [hf4] at hf45
    have hbool : ∀ f5 bv av : Bool, xor bv f5 = !av → f5 = xor bv (!av) := by decide
    exact hbool _ _ _ hf45
  have hinj6 : xor (srcR (p + 7)) (row.val.testBit ((p + 7) % k)) =
      (rot k 0 ref.val).testBit ((p + 6) % k) := by
    have h := src_inj_eq hk row ref 0 (p + 6) (by omega)
    simpa [srcR] using h
  have hinj7 : xor (srcR (p + 8)) (row.val.testBit ((p + 8) % k)) =
      (rot k 0 ref.val).testBit ((p + 7) % k) := by
    have h := src_inj_eq hk row ref 0 (p + 7) (by omega)
    simpa [srcR] using h
  have hy6 : lineStep k row constant srcK 1 (p + 6) =
      xor (xor (xor (xor (srcR (p + 5)) (srcR (p + 6))) (srcR (p + 7)))
        (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))))
        (xor (srcR (p + 6)) (srcK (p + 9))) := by
    rw [lineStep_succ]
    simp only [lineStep]
    have ha : p + 6 - 1 = p + 5 := by omega
    have hb : p + 6 + 1 = p + 7 := by omega
    have hc : p + 6 + 2 = p + 8 := by omega
    have hd : p + 6 + 3 = p + 9 := by omega
    have he : p + 6 + 1 - 2 * 0 = p + 7 := by omega
    rw [ha, hb, hc, hd, he, hsrc 5 (by omega), hsrc 6 (by omega), hsrc 7 (by omega),
      hsrc 8 (by omega), hinj6]
    have hbool : ∀ o5 o6 o7 o8 x0 r6 c6 : Bool,
        xor (xor o6 o7) o8 = false →
        xor (xor (xor (xor (xor o6 o5) o7) (!(xor (xor o7 o6) o8) && xor (xor o8 o7) x0)) r6) c6 =
          xor (xor (xor (xor o5 o6) o7) (xor r6 c6)) (xor o6 x0) := by decide
    exact hbool _ _ _ _ _ _ _ htau
  have hy7 : lineStep k row constant srcK 1 (p + 7) =
      xor (!(xor (srcR (p + 6)) (srcK (p + 9))) && xor (xor (srcK (p + 9)) (srcR (p + 8))) (srcK (p + 10)))
        (xor (xor (xor (srcR (p + 6)) (srcR (p + 7))) (srcR (p + 8)))
          (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))) := by
    rw [lineStep_succ]
    simp only [lineStep]
    have ha : p + 7 - 1 = p + 6 := by omega
    have hb : p + 7 + 1 = p + 8 := by omega
    have hc : p + 7 + 2 = p + 9 := by omega
    have hd : p + 7 + 3 = p + 10 := by omega
    have he : p + 7 + 1 - 2 * 0 = p + 8 := by omega
    rw [ha, hb, hc, hd, he, hsrc 6 (by omega), hsrc 7 (by omega), hsrc 8 (by omega), hinj7]
    have hbool : ∀ o6 o7 o8 x0 x1 r7 c7 : Bool,
        xor (xor o6 o7) o8 = false →
        xor (xor (xor (xor (xor o7 o6) o8) (!(xor (xor o8 o7) x0) && xor (xor x0 o8) x1)) r7) c7 =
          xor (!(xor o6 x0) && xor (xor x0 o8) x1) (xor (xor (xor o6 o7) o8) (xor r7 c7)) := by decide
    exact hbool _ _ _ _ _ _ _ htau
  have hy8 : lineStep k row constant srcK 1 (p + 8) =
      xor (!(xor (xor (srcK (p + 9)) (srcR (p + 8))) (srcK (p + 10))) &&
          xor (xor (srcK (p + 10)) (srcK (p + 9))) (srcK (p + 11)))
        (xor (xor (srcR (p + 6)) (row.val.testBit ((p + 9) % k))) ((constant 1).val.testBit ((p + 8) % k))) := by
    rw [lineStep_succ]
    simp only [lineStep]
    have ha : p + 8 - 1 = p + 7 := by omega
    have hb : p + 8 + 1 = p + 9 := by omega
    have hc : p + 8 + 2 = p + 10 := by omega
    have hd : p + 8 + 3 = p + 11 := by omega
    have he : p + 8 + 1 - 2 * 0 = p + 9 := by omega
    rw [ha, hb, hc, hd, he, hsrc 7 (by omega), hsrc 8 (by omega)]
    have h78 : xor (srcR (p + 8)) (srcR (p + 7)) = srcR (p + 6) := by
      have hb1 : ∀ o6 o7 o8 : Bool, xor (xor o6 o7) o8 = false → xor o8 o7 = o6 := by decide
      exact hb1 _ _ _ htau
    rw [h78]
    have hb2 : ∀ t o6 x0 r9 c8 : Bool,
        xor (xor (xor (xor o6 x0) t) (xor x0 r9)) c8 = xor t (xor (xor o6 r9) c8) := by decide
    exact hb2 _ _ _ _ _
  rw [hy4, hy5, hy6, hy7, hy8]
  exact Bool.xor_assoc _ _ _


open Finset

noncomputable section

abbrev Sym := Fin 3 → Bool

def sxor (a b : Sym) : Sym := fun v => xor (a v) (b v)

def uxor {m : Nat} (u w : Fin m → Sym) : Fin m → Sym := fun i => sxor (u i) (w i)

def sgn (b : Bool) : ℝ := if b then -1 else 1

theorem sgn_mul_self (b : Bool) : sgn b * sgn b = 1 := by
  cases b <;> simp [sgn]

theorem sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> simp [sgn]

theorem abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

theorem sgn_par_add (a b : Nat) :
    sgn ((a + b) % 2 == 1) = sgn (a % 2 == 1) * sgn (b % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
  simp [sgn, Nat.add_mod, ha, hb]

theorem sgn_sum_par {ι : Type*} (s : Finset ι) (f : ι → Bool) :
    sgn ((∑ i ∈ s, (f i).toNat) % 2 == 1) = ∏ i ∈ s, sgn (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sgn]
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha, sgn_par_add, ih]
    cases f a <;> simp [sgn]

def truthC {m : Nat} (g : Fin m → Sym → Bool) (u v : Fin m → Sym) : Bool :=
  (∑ i : Fin m, (g i (sxor (u i) (v i))).toNat) % 2 == 1

theorem sgn_truthC {m : Nat} (g : Fin m → Sym → Bool) (u v : Fin m → Sym) :
    sgn (truthC g u v) = ∏ i, sgn (g i (sxor (u i) (v i))) := sgn_sum_par _ _

def gam (G : Sym → Bool) (a a' : Sym) : ℝ :=
  ∑ w : Sym, sgn (G (sxor a w)) * sgn (G (sxor a' w))

def GoodG (G : Sym → Bool) : Prop := ∀ a a' : Sym, a ≠ a' → |gam G a a'| = 4

theorem card_sym : Fintype.card Sym = 8 := by
  simp [Fintype.card_fun]

theorem card_core (m : Nat) : Fintype.card (Fin m → Sym) = 8 ^ m := by
  rw [Fintype.card_fun, card_sym, Fintype.card_fin]

theorem gam_self (G : Sym → Bool) (a : Sym) : gam G a a = 8 := by
  simp only [gam, sgn_mul_self, sum_const, card_univ, card_sym]
  norm_num

theorem corr_prod {m : Nat} (g : Fin m → Sym → Bool) (u u' : Fin m → Sym) :
    ∑ v : Fin m → Sym, sgn (truthC g u v) * sgn (truthC g u' v) =
      ∏ i, gam (g i) (u i) (u' i) := by
  simp only [sgn_truthC, ← prod_mul_distrib, gam]
  rw [Fintype.prod_sum]

theorem abs_corr_le {m : Nat} (g : Fin m → Sym → Bool) (hg : ∀ i, GoodG (g i))
    (u u' : Fin m → Sym) :
    |∑ v : Fin m → Sym, sgn (truthC g u v) * sgn (truthC g u' v)| ≤
      (8:ℝ)^m * (1/4 + 3/4 * (if u = u' then 1 else 0) +
        1/4 * ∑ i : Fin m, (if (u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) then 1 else 0)) := by
  rw [corr_prod, Finset.abs_prod]
  have h1 : ∀ i, |gam (g i) (u i) (u' i)| = 8 * (if u i = u' i then 1 else 1/2) := by
    intro i
    by_cases h : u i = u' i
    · rw [if_pos h, h, gam_self]; norm_num
    · rw [if_neg h, hg i _ _ h]; norm_num
  simp only [h1, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  rw [prod_ite]
  simp only [prod_const_one, one_mul, prod_const]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsum0 : 0 ≤ ∑ i : Fin m, (if (u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) then (1:ℝ) else 0) :=
    sum_nonneg (fun i _ => by split_ifs <;> norm_num)
  by_cases huu : u = u'
  · subst huu
    have hD : (univ.filter (fun i => ¬ u i = u i)) = ∅ := by
      ext i; simp
    rw [hD, if_pos rfl]
    have hs : ∑ i : Fin m, (if (u ≠ u ∧ ∀ j, j ≠ i → u j = u j) then (1:ℝ) else 0) = 0 := by
      apply sum_eq_zero; intro i _; simp
    rw [hs]; norm_num
  · rw [if_neg huu]
    have hDne : (univ.filter (fun i => ¬ u i = u' i)).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      apply huu
      funext i
      by_contra hi
      have : i ∈ (univ.filter (fun i => ¬ u i = u' i)) := by simp [hi]
      rw [hne] at this; simp at this
    rcases Nat.lt_or_ge (univ.filter (fun i => ¬ u i = u' i)).card 2 with hlt | hge
    · have h1 : (univ.filter (fun i => ¬ u i = u' i)).card = 1 := by
        have := hDne.card_pos; omega
      rcases Finset.card_eq_one.mp h1 with ⟨i0, hi0⟩
      have hterm : (if (u' ≠ u ∧ ∀ j, j ≠ i0 → u' j = u j) then (1:ℝ) else 0) = 1 := by
        rw [if_pos]
        refine ⟨Ne.symm huu, fun j hj => ?_⟩
        by_contra hne
        have : j ∈ (univ.filter (fun i => ¬ u i = u' i)) := by
          simp only [mem_filter, mem_univ, true_and]; exact fun h => hne h.symm
        rw [hi0] at this
        simp at this
        exact hj this
      have hle : (1:ℝ) ≤ ∑ i : Fin m, (if (u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) then (1:ℝ) else 0) := by
        have hs1 := single_le_sum
          (f := fun i => (if (u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) then (1:ℝ) else 0))
          (fun i _ => by split_ifs <;> norm_num) (mem_univ i0)
        try simp only at hs1
        rw [hterm] at hs1
        exact hs1
      rw [h1]; linarith
    · have : ((1:ℝ)/2)^(univ.filter (fun i => ¬ u i = u' i)).card ≤ (1/2)^2 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hge
      nlinarith

def fib {m : Nat} (C : Finset (Fin m → Sym)) (i : Fin m) (u : Fin m → Sym) :
    Finset (Fin m → Sym) :=
  C.filter (fun u' => ∀ j, j ≠ i → u' j = u j)

theorem mem_fib_self {m : Nat} {C : Finset (Fin m → Sym)} {u : Fin m → Sym} (hu : u ∈ C)
    (i : Fin m) : u ∈ fib C i u := by
  simp [fib, hu]

theorem fib_card_le {m : Nat} (C : Finset (Fin m → Sym)) (i : Fin m) (u : Fin m → Sym) :
    (fib C i u).card ≤ 8 := by
  have h := card_le_card_of_injOn (s := fib C i u) (t := (univ : Finset Sym)) (fun u' => u' i)
    (by intro x _; simp) (by
      intro x hx y hy hxy
      simp only [fib, coe_filter, Set.mem_setOf_eq] at hx hy
      funext j
      by_cases hj : j = i
      · subst hj; exact hxy
      · rw [hx.2 j hj, hy.2 j hj])
  rw [card_univ, card_sym] at h
  exact h

theorem log_amgm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 < x i)
    (hsum : ∑ i ∈ s, x i ≤ (s.card : ℝ)^2) :
    ∑ i ∈ s, Real.log (x i) ≤ s.card * Real.log s.card := by
  rcases Nat.eq_zero_or_pos s.card with h0 | hpos
  · rw [Finset.card_eq_zero.mp h0]; simp
  · have hn : (0:ℝ) < s.card := by exact_mod_cast hpos
    have key : ∀ i ∈ s, Real.log (x i) ≤ Real.log s.card + (x i / s.card - 1) := by
      intro i hi
      have h1 : Real.log (x i) = Real.log s.card + Real.log (x i / s.card) := by
        rw [Real.log_div (hx i hi).ne' hn.ne']; ring
      rw [h1]
      have := Real.log_le_sub_one_of_pos (div_pos (hx i hi) hn)
      linarith
    have hdiv : (∑ i ∈ s, x i) / s.card ≤ s.card := by
      rw [div_le_iff₀ hn]; nlinarith
    calc ∑ i ∈ s, Real.log (x i) ≤ ∑ i ∈ s, (Real.log s.card + (x i / s.card - 1)) :=
          sum_le_sum key
      _ = s.card * Real.log s.card + (∑ i ∈ s, x i) / s.card - s.card := by
          rw [sum_add_distrib, sum_sub_distrib, sum_const, sum_const, ← sum_div,
            nsmul_eq_mul, nsmul_eq_mul]
          ring
      _ ≤ s.card * Real.log s.card := by linarith

theorem han {m : Nat} (J : Finset (Fin m)) : ∀ C : Finset (Fin m → Sym),
    (∀ u ∈ C, ∀ u' ∈ C, ∀ i, i ∉ J → u i = u' i) →
    ∑ u ∈ C, ∑ i ∈ J, Real.log (fib C i u).card ≤ C.card * Real.log C.card := by
  induction J using Finset.induction_on with
  | empty =>
    intro C _
    simp only [sum_empty, sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  | insert j J hj ih =>
    intro C hC
    let Ca : Sym → Finset (Fin m → Sym) := fun a => C.filter (fun u => u j = a)
    have hCa : ∀ a, ∀ u ∈ Ca a, ∀ u' ∈ Ca a, ∀ i, i ∉ J → u i = u' i := by
      intro a u hu u' hu' i hi
      simp only [Ca, mem_filter] at hu hu'
      by_cases hij : i = j
      · subst hij; rw [hu.2, hu'.2]
      · exact hC u hu.1 u' hu'.1 i (by simp [hij, hi])
    have hfib : ∀ u ∈ C, ∀ i ∈ J, fib (Ca (u j)) i u = fib C i u := by
      intro u hu i hi
      have hij : j ≠ i := fun h => hj (h ▸ hi)
      ext u'
      simp only [fib, Ca, mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 j hij⟩, h3⟩
    have hsplit : ∑ u ∈ C, ∑ i ∈ J, Real.log (fib C i u).card ≤
        ∑ u ∈ C, Real.log (Ca (u j)).card := by
      calc ∑ u ∈ C, ∑ i ∈ J, Real.log (fib C i u).card
          = ∑ a : Sym, ∑ u ∈ Ca a, ∑ i ∈ J, Real.log (fib (Ca a) i u).card := by
            rw [← sum_fiberwise C (fun u => u j)]
            apply sum_congr rfl
            intro a _
            apply sum_congr rfl
            intro u hu
            have hu' := mem_filter.mp hu
            apply sum_congr rfl
            intro i hi
            have hua : u j = a := hu'.2
            rw [← hua, hfib u hu'.1 i hi]
        _ ≤ ∑ a : Sym, ((Ca a).card * Real.log (Ca a).card) :=
            sum_le_sum (fun a _ => ih (Ca a) (hCa a))
        _ = ∑ u ∈ C, Real.log (Ca (u j)).card := by
            rw [← sum_fiberwise C (fun u => u j) (fun u => Real.log (Ca (u j)).card)]
            apply sum_congr rfl
            intro a _
            rw [sum_congr rfl (g := fun _ => Real.log (Ca a).card)]
            · rw [sum_const, nsmul_eq_mul]
            · intro u hu
              have hua : u j = a := (mem_filter.mp hu).2
              rw [hua]
    have hcount : ∑ u ∈ C, (fib C j u).card * (Ca (u j)).card ≤ C.card ^ 2 := by
      have e1 : ∑ u ∈ C, (fib C j u).card * (Ca (u j)).card =
          (C.sigma (fun u => fib C j u ×ˢ Ca (u j))).card := by
        rw [card_sigma]; simp [card_product]
      rw [e1, sq, ← card_product]
      apply card_le_card_of_injOn (fun p => p.2)
      · intro p hp
        rw [mem_coe, mem_sigma, mem_product] at hp
        rw [mem_coe, mem_product]
        exact ⟨(mem_filter.mp hp.2.1).1, (mem_filter.mp hp.2.2).1⟩
      · intro p hp q hq hpq
        rw [mem_coe, mem_sigma, mem_product] at hp hq
        obtain ⟨u, x⟩ := p
        obtain ⟨w, y⟩ := q
        simp only at hpq hp hq
        subst hpq
        have huw : u = w := by
          funext i
          have h1 := (mem_filter.mp hp.2.1).2
          have h2 := (mem_filter.mp hp.2.2).2
          have h3 := (mem_filter.mp hq.2.1).2
          have h4 := (mem_filter.mp hq.2.2).2
          by_cases hij : i = j
          · subst hij; rw [← h2, h4]
          · rw [← h1 i hij, h3 i hij]
        subst huw
        rfl
    have hpos : ∀ u ∈ C, (0:ℝ) < ((fib C j u).card : ℝ) * (Ca (u j)).card := by
      intro u hu
      have h1 : 0 < (fib C j u).card := card_pos.mpr ⟨u, mem_fib_self hu j⟩
      have h2 : 0 < (Ca (u j)).card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩
      positivity
    have hamgm := log_amgm C (fun u => ((fib C j u).card : ℝ) * (Ca (u j)).card) hpos
      (by exact_mod_cast hcount)
    have hlog : ∑ u ∈ C, Real.log (((fib C j u).card : ℝ) * (Ca (u j)).card) =
        ∑ u ∈ C, Real.log (fib C j u).card + ∑ u ∈ C, Real.log (Ca (u j)).card := by
      rw [← sum_add_distrib]
      apply sum_congr rfl; intro u hu
      have h1 : 0 < (fib C j u).card := card_pos.mpr ⟨u, mem_fib_self hu j⟩
      have h2 : 0 < (Ca (u j)).card := card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩
      rw [Real.log_mul (by positivity) (by positivity)]
    rw [sum_congr rfl (fun u _ => sum_insert hj), sum_add_distrib]
    linarith

theorem deg_bound (n : Nat) (h1 : 1 ≤ n) (h8 : n ≤ 8) :
    ((n:ℝ) - 1) * (3 * Real.log 2) ≤ 7 * Real.log n := by
  have hnat : 2^(3*(n-1)) ≤ n^7 := by interval_cases n <;> norm_num
  have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := Real.log_le_log (by positivity)
    (show ((2:ℝ)^(3*(n-1))) ≤ (n:ℝ)^7 by exact_mod_cast hnat)
  rw [Real.log_pow, Real.log_pow] at h
  have hc : ((3*(n-1) : Nat) : ℝ) = 3 * ((n:ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub h1]; simp
  rw [hc] at h
  push_cast at h
  linarith

theorem edge_bound {m : Nat} (C : Finset (Fin m → Sym)) :
    (3 * Real.log 2) * ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1) ≤
      7 * (C.card * Real.log C.card) := by
  have hH := han (univ : Finset (Fin m)) C (fun u _ u' _ i hi => absurd (mem_univ i) hi)
  have hle : ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1) * (3 * Real.log 2) ≤
      ∑ u ∈ C, ∑ i : Fin m, 7 * Real.log (fib C i u).card := by
    apply sum_le_sum; intro u hu; apply sum_le_sum; intro i _
    exact deg_bound _ (card_pos.mpr ⟨u, mem_fib_self hu i⟩) (fib_card_le C i u)
  have e1 : (3 * Real.log 2) * ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1) =
      ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1) * (3 * Real.log 2) := by
    rw [mul_comm, sum_mul]; apply sum_congr rfl; intro u _; rw [sum_mul]
  have e2 : ∑ u ∈ C, ∑ i : Fin m, 7 * Real.log (fib C i u).card =
      7 * ∑ u ∈ C, ∑ i : Fin m, Real.log (fib C i u).card := by
    rw [mul_sum]; apply sum_congr rfl; intro u _; rw [mul_sum]
  rw [e1]; rw [e2] at hle
  linarith

theorem nb_count {m : Nat} (C : Finset (Fin m → Sym)) (u : Fin m → Sym) (hu : u ∈ C)
    (i : Fin m) :
    ∑ u' ∈ C, (if (u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) then (1:ℝ) else 0) =
      ((fib C i u).card : ℝ) - 1 := by
  rw [sum_boole]
  have e : C.filter (fun u' => u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) = (fib C i u).erase u := by
    ext u'; simp only [fib, mem_erase, mem_filter]; tauto
  rw [e, card_erase_of_mem (mem_fib_self hu i),
    Nat.cast_sub (card_pos.mpr ⟨u, mem_fib_self hu i⟩)]
  simp

theorem class_sq {m : Nat} (g : Fin m → Sym → Bool) (hg : ∀ i, GoodG (g i))
    (C : Finset (Fin m → Sym)) :
    ∑ v : Fin m → Sym, (∑ u ∈ C, sgn (truthC g u v))^2 ≤
      (8:ℝ)^m * ((C.card:ℝ)^2/4 + 3/4 * C.card +
        1/4 * ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1)) := by
  have e : ∀ v : Fin m → Sym, (∑ u ∈ C, sgn (truthC g u v))^2 =
      ∑ u ∈ C, ∑ u' ∈ C, sgn (truthC g u v) * sgn (truthC g u' v) := by
    intro v; rw [sq, sum_mul_sum]
  simp only [e]
  rw [sum_comm]
  calc ∑ u ∈ C, ∑ v, ∑ u' ∈ C, sgn (truthC g u v) * sgn (truthC g u' v)
      = ∑ u ∈ C, ∑ u' ∈ C, ∑ v, sgn (truthC g u v) * sgn (truthC g u' v) := by
        apply sum_congr rfl; intro u _; rw [sum_comm]
    _ ≤ ∑ u ∈ C, ∑ u' ∈ C, (8:ℝ)^m * (1/4 + 3/4 * (if u = u' then 1 else 0) +
        1/4 * ∑ i : Fin m, (if (u' ≠ u ∧ ∀ j, j ≠ i → u' j = u j) then 1 else 0)) := by
        apply sum_le_sum; intro u _; apply sum_le_sum; intro u' _
        exact le_trans (le_abs_self _) (abs_corr_le g hg u u')
    _ = ∑ u ∈ C, (8:ℝ)^m * ((C.card:ℝ)/4 + 3/4 +
          1/4 * ∑ i : Fin m, (((fib C i u).card : ℝ) - 1)) := by
        apply sum_congr rfl; intro u hu
        rw [← mul_sum]; congr 1
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_ite_eq, if_pos hu,
          sum_comm]
        simp only [nb_count C u hu, sum_const, nsmul_eq_mul]
        ring
    _ = _ := by
        rw [← mul_sum]; congr 1
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, sum_const, sum_const, nsmul_eq_mul,
          nsmul_eq_mul]
        ring

theorem class_bound {m : Nat} (g : Fin m → Sym → Bool) (hg : ∀ i, GoodG (g i))
    (C : Finset (Fin m → Sym)) :
    (∑ v : Fin m → Sym, |∑ u ∈ C, sgn (truthC g u v)|)^2 ≤
      ((8:ℝ)^m)^2 * ((C.card:ℝ)^2/4 + 3/4 * C.card +
        7 / (12 * Real.log 2) * (C.card * Real.log C.card)) := by
  have hCS := sum_mul_sq_le_sq_mul_sq (univ : Finset (Fin m → Sym)) (fun _ => (1:ℝ))
    (fun v => |∑ u ∈ C, sgn (truthC g u v)|)
  simp only [one_mul, one_pow, sum_const, card_univ, card_core, sq_abs, nsmul_eq_mul,
    mul_one] at hCS
  have hcl := class_sq g hg C
  have hed := edge_bound C
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hX : 1/4 * ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1) ≤
      7 / (12 * Real.log 2) * (C.card * Real.log C.card) := by
    have e : 7 / (12 * Real.log 2) * (C.card * Real.log C.card) =
        (7 * (C.card * Real.log C.card)) / (12 * Real.log 2) := by ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  have hN : (0:ℝ) ≤ (8:ℝ)^m := by positivity
  calc (∑ v : Fin m → Sym, |∑ u ∈ C, sgn (truthC g u v)|)^2
      ≤ (((8^m : Nat) : ℝ)) * ∑ v : Fin m → Sym, (∑ u ∈ C, sgn (truthC g u v))^2 := hCS
    _ ≤ (8:ℝ)^m * ((8:ℝ)^m * ((C.card:ℝ)^2/4 + 3/4 * C.card +
        1/4 * ∑ u ∈ C, ∑ i : Fin m, (((fib C i u).card : ℝ) - 1))) := by
        push_cast
        exact mul_le_mul_of_nonneg_left hcl hN
    _ ≤ (8:ℝ)^m * ((8:ℝ)^m * ((C.card:ℝ)^2/4 + 3/4 * C.card +
        7 / (12 * Real.log 2) * (C.card * Real.log C.card))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hN) hN
    _ = _ := by ring

theorem core_lower {m : Nat} (g : Fin m → Sym → Bool) (hg : ∀ i, GoodG (g i))
    (b K : Nat) (hb1 : 1 ≤ b) (hK : (K:ℝ) * 2^b = 8^m)
    (c : (Fin m → Sym) → Fin K) (h : Fin K → (Fin m → Sym) → Bool) :
    12 * 2^b * ((∑ u, ∑ v, sgn (h (c u) v) * sgn (truthC g u v)) / ((8:ℝ)^m)^2)^2 ≤
      3 * 2^b + 9 + 7 * b := by
  classical
  have hN : (0:ℝ) < (8:ℝ)^m := by positivity
  have hb2 : (0:ℝ) < 2^b := by positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let Cl : Fin K → Finset (Fin m → Sym) := fun j => univ.filter (fun u => c u = j)
  let a : Fin K → ℝ := fun j => ∑ v, |∑ u ∈ Cl j, sgn (truthC g u v)|
  have hA1 : ∑ u, ∑ v, sgn (h (c u) v) * sgn (truthC g u v) =
      ∑ j, ∑ v, ∑ u ∈ Cl j, sgn (h j v) * sgn (truthC g u v) := by
    rw [← sum_fiberwise univ c]
    apply sum_congr rfl; intro j _
    rw [sum_comm]
    apply sum_congr rfl; intro v _
    apply sum_congr rfl; intro u hu
    rw [(mem_filter.mp hu).2]
  have hA2 : |∑ u, ∑ v, sgn (h (c u) v) * sgn (truthC g u v)| ≤ ∑ j, a j := by
    rw [hA1]
    refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun j _ => ?_)
    refine le_trans (abs_sum_le_sum_abs _ _) (sum_le_sum fun v _ => ?_)
    rw [← mul_sum, abs_mul, abs_sgn, one_mul]
  set J := univ.filter (fun j : Fin K => 0 < (Cl j).card) with hJdef
  have hsumA : ∑ j, a j = ∑ j ∈ J, a j := by
    rw [hJdef, sum_filter]; apply sum_congr rfl; intro j _
    by_cases hj : 0 < (Cl j).card
    · rw [if_pos hj]
    · rw [if_neg hj]
      have hCl : Cl j = ∅ := card_eq_zero.mp (by omega)
      show ∑ v, |∑ u ∈ Cl j, sgn (truthC g u v)| = 0
      rw [hCl]; simp
  have hsumN : ∑ j ∈ J, ((Cl j).card : ℝ) = (8:ℝ)^m := by
    rw [hJdef, sum_filter]
    have e1 : ∑ j, (if 0 < (Cl j).card then ((Cl j).card : ℝ) else 0) =
        ∑ j, ((Cl j).card : ℝ) := by
      apply sum_congr rfl; intro j _; split_ifs with hj
      · rfl
      · have : (Cl j).card = 0 := by omega
        rw [this]; simp
    rw [e1, ← Nat.cast_sum]
    have hc := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin m → Sym)))
      (t := (univ : Finset (Fin K))) (f := c) (fun _ _ => mem_univ _)
    rw [← hc, card_univ, card_core]; simp
  have hsed := sq_sum_div_le_sum_sq_div J a (g := fun j => ((Cl j).card : ℝ)) (by
    intro j hj; have := (mem_filter.mp hj).2; exact_mod_cast this)
  rw [hsumN] at hsed
  set c7 : ℝ := 7 / (12 * Real.log 2) with hc7def
  have hc7 : 0 < c7 := by positivity
  have hper : ∀ j ∈ J, a j ^ 2 / ((Cl j).card : ℝ) ≤
      ((8:ℝ)^m)^2 * (((Cl j).card : ℝ)/4 + 3/4 + c7 * Real.log (Cl j).card) := by
    intro j hj
    have hpos : (0:ℝ) < (Cl j).card := by exact_mod_cast (mem_filter.mp hj).2
    have hb := class_bound g hg (Cl j)
    rw [div_le_iff₀ hpos]
    calc a j ^ 2 ≤ _ := hb
      _ = _ := by ring
  have hlogj : ∀ j ∈ J, c7 * Real.log (Cl j).card ≤
      7 * b / 12 + c7 * (((Cl j).card : ℝ) / 2^b - 1) := by
    intro j hj
    have hpos : (0:ℝ) < (Cl j).card := by exact_mod_cast (mem_filter.mp hj).2
    have h1 : Real.log (Cl j).card = b * Real.log 2 + Real.log (((Cl j).card : ℝ) / 2^b) := by
      rw [Real.log_div hpos.ne' hb2.ne', Real.log_pow]; ring
    have h2 := Real.log_le_sub_one_of_pos (div_pos hpos hb2)
    have hc7l : c7 * (b * Real.log 2) = 7 * b / 12 := by
      rw [hc7def]; field_simp
    rw [h1, mul_add, hc7l]
    have := mul_le_mul_of_nonneg_left h2 hc7.le
    linarith
  have hJK : (J.card : ℝ) ≤ K := by
    have : J.card ≤ K := le_trans (card_filter_le _ _) (by simp)
    exact_mod_cast this
  have hcoef : 0 ≤ 3/4 + 7*(b:ℝ)/12 - c7 := by
    have hb' : (1:ℝ) ≤ b := by exact_mod_cast hb1
    have hl := Real.log_two_gt_d9
    have : c7 ≤ 4/3 := by
      rw [hc7def, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hNK : c7 * (8:ℝ)^m / 2^b = c7 * K := by rw [← hK]; field_simp
  have hsumE : ∑ j ∈ J, (((Cl j).card : ℝ)/4 + 3/4 + c7 * Real.log (Cl j).card) ≤
      (8:ℝ)^m/4 + K * (3/4 + 7*b/12) := by
    have h1 : ∑ j ∈ J, (((Cl j).card : ℝ)/4 + 3/4 + c7 * Real.log (Cl j).card) ≤
        ∑ j ∈ J, (((Cl j).card : ℝ) * (1/4 + c7/2^b) + (3/4 + 7*b/12 - c7)) :=
      sum_le_sum (fun j hj => by
        have := hlogj j hj
        have e : ((Cl j).card : ℝ) * (1/4 + c7/2^b) + (3/4 + 7*b/12 - c7) =
            ((Cl j).card : ℝ)/4 + 3/4 + (7 * b / 12 + c7 * (((Cl j).card : ℝ) / 2^b - 1)) := by
          ring
        rw [e]; linarith)
    have e3 : ∑ j ∈ J, (((Cl j).card : ℝ) * (1/4 + c7/2^b) + (3/4 + 7*b/12 - c7)) =
        (8:ℝ)^m/4 + c7 * (8:ℝ)^m / 2^b + J.card * (3/4 + 7*b/12 - c7) := by
      rw [sum_add_distrib, ← sum_mul, hsumN, sum_const, nsmul_eq_mul]; ring
    rw [e3, hNK] at h1
    have h4 := mul_le_mul_of_nonneg_right hJK hcoef
    nlinarith
  have hsq : (∑ j, a j)^2 ≤ (8:ℝ)^m * (((8:ℝ)^m)^2 * ((8:ℝ)^m/4 + K * (3/4 + 7*b/12))) := by
    rw [hsumA]
    rw [div_le_iff₀ hN] at hsed
    have h2 : ∑ j ∈ J, a j^2 / ((Cl j).card : ℝ) ≤
        ((8:ℝ)^m)^2 * ∑ j ∈ J, (((Cl j).card : ℝ)/4 + 3/4 + c7 * Real.log (Cl j).card) := by
      rw [mul_sum]; exact sum_le_sum hper
    have h3 : ((8:ℝ)^m)^2 * ∑ j ∈ J, (((Cl j).card : ℝ)/4 + 3/4 + c7 * Real.log (Cl j).card) ≤
        ((8:ℝ)^m)^2 * ((8:ℝ)^m/4 + K * (3/4 + 7*b/12)) :=
      mul_le_mul_of_nonneg_left hsumE (by positivity)
    calc (∑ j ∈ J, a j)^2 ≤ (∑ j ∈ J, a j^2 / ((Cl j).card : ℝ)) * (8:ℝ)^m := hsed
      _ ≤ (((8:ℝ)^m)^2 * ((8:ℝ)^m/4 + K * (3/4 + 7*b/12))) * (8:ℝ)^m :=
          mul_le_mul_of_nonneg_right (le_trans h2 h3) hN.le
      _ = _ := by ring
  set A := ∑ u, ∑ v, sgn (h (c u) v) * sgn (truthC g u v) with hAdef
  have hAsq : A^2 ≤ (8:ℝ)^m * (((8:ℝ)^m)^2 * ((8:ℝ)^m/4 + K * (3/4 + 7*b/12))) := by
    have h0 : 0 ≤ |A| := abs_nonneg A
    have : |A|^2 ≤ (∑ j, a j)^2 := pow_le_pow_left₀ h0 hA2 2
    rw [sq_abs] at this
    linarith
  have key : (A / ((8:ℝ)^m)^2)^2 ≤ ((8:ℝ)^m/4 + K * (3/4 + 7*b/12)) / (8:ℝ)^m := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hN]
    calc A^2 * (8:ℝ)^m ≤ ((8:ℝ)^m * (((8:ℝ)^m)^2 * ((8:ℝ)^m/4 + K * (3/4 + 7*b/12)))) *
          (8:ℝ)^m := mul_le_mul_of_nonneg_right hAsq hN.le
      _ = _ := by ring
  have hfin : 12 * 2^b * (((8:ℝ)^m/4 + K * (3/4 + 7*b/12)) / (8:ℝ)^m) =
      3 * 2^b + 9 + 7 * b := by
    rw [← hK]
    have hK0 : (K:ℝ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hK; exact absurd hK (ne_of_lt hN)
    field_simp
    ring
  calc 12 * 2^b * (A / ((8:ℝ)^m)^2)^2
      ≤ 12 * 2^b * (((8:ℝ)^m/4 + K * (3/4 + 7*b/12)) / (8:ℝ)^m) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = _ := hfin

def ue {m : Nat} (i0 : Fin m) (v0 : Fin 3) : Fin m → Sym := fun i v => decide (i = i0 ∧ v = v0)

def syn {m t : Nat} (H : Fin m × Fin 3 → (Fin t → ZMod 2)) (u : Fin m → Sym) :
    Fin t → ZMod 2 :=
  ∑ c : Fin m × Fin 3, (if u c.1 c.2 then H c else 0)

theorem zmod2_add_self : ∀ x : ZMod 2, x + x = 0 := by decide

theorem fun_add_self {t : Nat} (x : Fin t → ZMod 2) : x + x = 0 := by
  funext r; simp [zmod2_add_self]

theorem syn_uxor {m t : Nat} (H : Fin m × Fin 3 → (Fin t → ZMod 2)) (u w : Fin m → Sym) :
    syn H (uxor u w) = syn H u + syn H w := by
  simp only [syn, ← sum_add_distrib]
  apply sum_congr rfl; intro c _
  show (if xor (u c.1 c.2) (w c.1 c.2) then H c else 0) = _
  have hz := fun_add_self (H c)
  cases u c.1 c.2 <;> cases w c.1 c.2 <;> simp [hz]

theorem syn_ue {m t : Nat} (H : Fin m × Fin 3 → (Fin t → ZMod 2)) (c : Fin m × Fin 3) :
    syn H (ue c.1 c.2) = H c := by
  simp only [syn, ue]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' _ hc
    have : ¬ (c'.1 = c.1 ∧ c'.2 = c.2) := fun h => hc (Prod.ext h.1 h.2)
    simp [this]
  · simp

theorem uxor_uxor {m : Nat} (u w : Fin m → Sym) : uxor (uxor u w) w = u := by
  funext i v; simp [uxor, sxor]

theorem ker_count {m t : Nat} (H : Fin m × Fin 3 → (Fin t → ZMod 2))
    (pick : (Fin t → ZMod 2) → Fin m × Fin 3) (hpick : ∀ s, s ≠ 0 → H (pick s) = s) :
    (univ.filter (fun u : Fin m → Sym => syn H u = 0)).card * 2^t = 8^m := by
  classical
  have hfib : ∀ s : Fin t → ZMod 2, (univ.filter (fun u : Fin m → Sym => syn H u = s)).card =
      (univ.filter (fun u : Fin m → Sym => syn H u = 0)).card := by
    intro s
    by_cases hs : s = 0
    · rw [hs]
    · have hc := hpick s hs
      symm
      apply Finset.card_nbij' (fun u => uxor u (ue (pick s).1 (pick s).2))
        (fun u => uxor u (ue (pick s).1 (pick s).2))
      · intro u hu
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hu ⊢
        rw [syn_uxor, syn_ue, hu, zero_add]; exact hc
      · intro u hu
        simp only [mem_coe, mem_filter, mem_univ, true_and] at hu ⊢
        rw [syn_uxor, syn_ue, hu, hc, fun_add_self]
      · intro u _; exact uxor_uxor u _
      · intro u _; exact uxor_uxor u _
  have htot := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin m → Sym)))
    (t := (univ : Finset (Fin t → ZMod 2))) (f := syn H) (fun _ _ => mem_univ _)
  rw [card_univ, card_core] at htot
  rw [htot, sum_congr rfl (fun s _ => hfib s), sum_const, card_univ, smul_eq_mul]
  simp [Fintype.card_fun, ZMod.card, mul_comm]

theorem core_upper {m t : Nat} (hm : 0 < m) (g : Fin m → Sym → Bool) (hg : ∀ i, GoodG (g i))
    (H : Fin m × Fin 3 → (Fin t → ZMod 2)) (pick : (Fin t → ZMod 2) → Fin m × Fin 3)
    (hpick : ∀ s, s ≠ 0 → H (pick s) = s)
    (corr : (Fin m → Sym) → (Fin m → Sym))
    (hcorr : ∀ u, corr u = if syn H u = 0 then u else uxor u (ue (pick (syn H u)).1 (pick (syn H u)).2))
    (beta : (Fin m → Sym) → Bool)
    (hbeta : ∀ u, beta u = if syn H u = 0 then false else
        decide (gam (g (pick (syn H u)).1) (corr u (pick (syn H u)).1) (u (pick (syn H u)).1) < 0)) :
    (∀ u, syn H (corr u) = 0) ∧
    ∑ u, ∑ v, sgn (xor (truthC g (corr u) v) (beta u)) * sgn (truthC g u v) =
      (8:ℝ)^m * (univ.filter (fun u : Fin m → Sym => syn H u = 0)).card +
        (8:ℝ)^m / 2 * ((8:ℝ)^m - (univ.filter (fun u : Fin m → Sym => syn H u = 0)).card) := by
  classical
  refine ⟨fun u => ?_, ?_⟩
  · rw [hcorr]
    split_ifs with h
    · exact h
    · rw [syn_uxor, syn_ue, hpick _ h, fun_add_self]
  have hrow : ∀ u, ∑ v, sgn (xor (truthC g (corr u) v) (beta u)) * sgn (truthC g u v) =
      if syn H u = 0 then (8:ℝ)^m else (8:ℝ)^m / 2 := by
    intro u
    by_cases h : syn H u = 0
    · rw [if_pos h, hbeta, if_pos h, hcorr, if_pos h]
      simp only [Bool.xor_false, sgn_mul_self, sum_const, card_univ, card_core, nsmul_eq_mul,
        mul_one]
      push_cast; ring
    · rw [if_neg h, hbeta, if_neg h]
      set c := pick (syn H u) with hcdef
      have hcu : corr u = uxor u (ue c.1 c.2) := by rw [hcorr, if_neg h]
      have e1 : ∀ v, sgn (xor (truthC g (corr u) v)
          (decide (gam (g c.1) (corr u c.1) (u c.1) < 0))) * sgn (truthC g u v) =
          sgn (decide (gam (g c.1) (corr u c.1) (u c.1) < 0)) *
            (sgn (truthC g (corr u) v) * sgn (truthC g u v)) := by
        intro v; rw [sgn_xor]; ring
      rw [sum_congr rfl (fun v _ => e1 v), ← mul_sum, corr_prod]
      have hoff : ∀ i, i ≠ c.1 → corr u i = u i := by
        intro i hi; rw [hcu]; funext v; simp [uxor, sxor, ue, hi]
      have hon : corr u c.1 ≠ u c.1 := by
        intro heq
        have := congrFun heq c.2
        rw [hcu] at this
        simp [uxor, sxor, ue] at this
      rw [← mul_prod_erase univ _ (mem_univ c.1)]
      have hrest : ∏ i ∈ univ.erase c.1, gam (g i) (corr u i) (u i) = (8:ℝ)^(m-1) := by
        rw [prod_congr rfl (fun i hi => by rw [hoff i (ne_of_mem_erase hi), gam_self]),
          prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      rw [hrest]
      have habs := hg c.1 _ _ hon
      have hsg : sgn (decide (gam (g c.1) (corr u c.1) (u c.1) < 0)) *
          gam (g c.1) (corr u c.1) (u c.1) = 4 := by
        by_cases hneg : gam (g c.1) (corr u c.1) (u c.1) < 0
        · rw [decide_eq_true hneg, abs_of_neg hneg] at *
          simp only [sgn, if_true]; linarith
        · rw [decide_eq_false hneg]
          rw [abs_of_nonneg (not_lt.mp hneg)] at habs
          simp only [sgn, Bool.false_eq_true, if_false]; linarith
      have h8 : (8:ℝ)^m = 8 * 8^(m-1) := by
        rw [← pow_succ']; congr 1; omega
      rw [← mul_assoc, hsg, h8]; ring
  rw [sum_congr rfl (fun u _ => hrow u), sum_ite, sum_const, sum_const, nsmul_eq_mul,
    nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin m → Sym)))
    (fun u => syn H u = 0)
  rw [card_univ, card_core] at hcard
  have : ((univ.filter (fun u : Fin m → Sym => ¬ syn H u = 0)).card : ℝ) =
      (8:ℝ)^m - (univ.filter (fun u : Fin m → Sym => syn H u = 0)).card := by
    have h2 : (((univ.filter (fun u : Fin m → Sym => syn H u = 0)).card +
        (univ.filter (fun u : Fin m → Sym => ¬ syn H u = 0)).card : Nat) : ℝ) = ((8^m : Nat) : ℝ) := by
      rw [hcard]
    push_cast at h2
    linarith
  rw [this]; ring

theorem count_eq_sgn {K : Type*} [DecidableEq K] (fiber : Finset K) (P Q : K → K → Bool) :
    ((((fiber.product fiber).filter (fun z => P z.1 z.2 = Q z.1 z.2)).card : Nat) : ℝ) =
      ∑ x ∈ fiber, ∑ y ∈ fiber, (1 + sgn (P x y) * sgn (Q x y)) / 2 := by
  rw [card_filter, Finset.product_eq_sprod, sum_product]
  push_cast
  apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _
  cases P x y <;> cases Q x y <;> simp [sgn] <;> norm_num

theorem sgn_sum_slices {K : Type*} [DecidableEq K] {m : Nat} (g : Fin m → Sym → Bool)
    (fiber : Finset K) (σ : K → Fin m → Sym) (truth : K → K → Bool)
    (htruth : ∀ x ∈ fiber, ∀ y ∈ fiber, truth x y = truthC g (σ x) (σ y))
    (T : Finset K) (ι : K → (Fin m → Sym) → K)
    (hsum : ∀ f : K → ℝ, ∑ x ∈ fiber, f x = ∑ t ∈ T, ∑ u, f (ι t u))
    (hsig : ∀ t ∈ T, ∀ u, σ (ι t u) = u) (hmem : ∀ t ∈ T, ∀ u, ι t u ∈ fiber)
    (P : K → K → Bool) :
    ∑ x ∈ fiber, ∑ y ∈ fiber, sgn (P x y) * sgn (truth x y) =
      ∑ p ∈ T ×ˢ T, ∑ u, ∑ v, sgn (P (ι p.1 u) (ι p.2 v)) * sgn (truthC g u v) := by
  rw [hsum, sum_product]
  apply sum_congr rfl; intro t ht
  rw [sum_congr rfl (fun u _ => hsum (fun y => sgn (P (ι t u) y) * sgn (truth (ι t u) y)))]
  rw [sum_comm]
  apply sum_congr rfl; intro t' ht'
  apply sum_congr rfl; intro u _
  apply sum_congr rfl; intro v _
  rw [htruth _ (hmem t ht u) _ (hmem t' ht' v), hsig t ht u, hsig t' ht' v]

theorem card_fiber_slices {K : Type*} {m : Nat} (fiber : Finset K)
    (T : Finset K) (ι : K → (Fin m → Sym) → K)
    (hsum : ∀ f : K → ℝ, ∑ x ∈ fiber, f x = ∑ t ∈ T, ∑ u, f (ι t u)) :
    (fiber.card : ℝ) = T.card * (8:ℝ)^m := by
  have := hsum (fun _ => 1)
  simp only [sum_const, card_univ, card_core, nsmul_eq_mul, mul_one] at this
  rw [this]; push_cast; ring

theorem rate_identity {K : Type*} [DecidableEq K] {m : Nat} (g : Fin m → Sym → Bool)
    (fiber : Finset K) (σ : K → Fin m → Sym) (truth : K → K → Bool)
    (htruth : ∀ x ∈ fiber, ∀ y ∈ fiber, truth x y = truthC g (σ x) (σ y))
    (T : Finset K) (ι : K → (Fin m → Sym) → K)
    (hsum : ∀ f : K → ℝ, ∑ x ∈ fiber, f x = ∑ t ∈ T, ∑ u, f (ι t u))
    (hsig : ∀ t ∈ T, ∀ u, σ (ι t u) = u) (hmem : ∀ t ∈ T, ∀ u, ι t u ∈ fiber)
    (hT : T.Nonempty) (P : K → K → Bool) :
    (((2 * ((((fiber.product fiber).filter (fun z => P z.1 z.2 = truth z.1 z.2)).card : ℚ) /
      ((fiber.product fiber).card : ℚ)) - 1 : ℚ)) : ℝ) =
      (∑ p ∈ T ×ˢ T, ∑ u, ∑ v, sgn (P (ι p.1 u) (ι p.2 v)) * sgn (truthC g u v)) /
        ((T ×ˢ T).card * ((8:ℝ)^m)^2) := by
  have hc := count_eq_sgn fiber P truth
  have hs := sgn_sum_slices g fiber σ truth htruth T ι hsum hsig hmem P
  have hf := card_fiber_slices fiber T ι hsum
  have hTpos : (0:ℝ) < T.card := by exact_mod_cast hT.card_pos
  have hM : (((fiber.product fiber).card : ℕ) : ℝ) = (T ×ˢ T).card * ((8:ℝ)^m)^2 := by
    rw [Finset.product_eq_sprod, card_product, card_product]; push_cast; rw [hf]; ring
  push_cast
  rw [hc, hM]
  have e : ∑ x ∈ fiber, ∑ y ∈ fiber, (1 + sgn (P x y) * sgn (truth x y)) / 2 =
      ((fiber.card : ℝ) * fiber.card + ∑ x ∈ fiber, ∑ y ∈ fiber, sgn (P x y) * sgn (truth x y)) / 2 := by
    simp only [add_div, sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_div]
    ring
  rw [e, hs, hf, card_product]
  have hN : (0:ℝ) < (8:ℝ)^m := by positivity
  push_cast
  field_simp
  ring

theorem fiber_lower {K : Type*} [DecidableEq K] {m : Nat} (g : Fin m → Sym → Bool)
    (hg : ∀ i, GoodG (g i))
    (fiber : Finset K) (σ : K → Fin m → Sym) (truth : K → K → Bool)
    (htruth : ∀ x ∈ fiber, ∀ y ∈ fiber, truth x y = truthC g (σ x) (σ y))
    (T : Finset K) (ι : K → (Fin m → Sym) → K)
    (hsum : ∀ f : K → ℝ, ∑ x ∈ fiber, f x = ∑ t ∈ T, ∑ u, f (ι t u))
    (hsig : ∀ t ∈ T, ∀ u, σ (ι t u) = u) (hmem : ∀ t ∈ T, ∀ u, ι t u ∈ fiber)
    (hT : T.Nonempty)
    (b c : Nat) (hb1 : 1 ≤ b) (hK : ((2^c : Nat) : ℝ) * 2^b = 8^m)
    (send : K → Fin (2^c)) (read : Fin (2^c) → K → Bool) :
    12 * (2:ℚ)^b * (2 * ((((fiber.product fiber).filter
      (fun z => read (send z.1) z.2 = truth z.1 z.2)).card : ℚ) /
        ((fiber.product fiber).card : ℚ)) - 1)^2 ≤ 3 * (2:ℚ)^b + 9 + 7 * (b:ℚ) := by
  have hr := rate_identity g fiber σ truth htruth T ι hsum hsig hmem hT
    (fun x y => read (send x) y)
  set X := (2 * ((((fiber.product fiber).filter
      (fun z => read (send z.1) z.2 = truth z.1 z.2)).card : ℚ) /
        ((fiber.product fiber).card : ℚ)) - 1 : ℚ) with hXdef
  have hP : (0:ℝ) < (T ×ˢ T).card := by exact_mod_cast (hT.product hT).card_pos
  have hN : (0:ℝ) < (8:ℝ)^m := by positivity
  let x : K × K → ℝ := fun p =>
    (∑ u, ∑ v, sgn (read (send (ι p.1 u)) (ι p.2 v)) * sgn (truthC g u v)) / ((8:ℝ)^m)^2
  have hxp : ∀ p ∈ T ×ˢ T, 12 * 2^b * (x p)^2 ≤ 3 * 2^b + 9 + 7 * (b:ℝ) := by
    intro p _
    exact core_lower g hg b (2^c) hb1 hK (fun u => send (ι p.1 u))
      (fun j v => read j (ι p.2 v))
  have hXr : (X : ℝ) = (∑ p ∈ T ×ˢ T, x p) / (T ×ˢ T).card := by
    rw [hr]
    simp only [x, ← sum_div]
    field_simp
  have hCS := sum_mul_sq_le_sq_mul_sq (T ×ˢ T) (fun _ => (1:ℝ)) x
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hCS
  have hsumx : ∑ p ∈ T ×ˢ T, 12 * 2^b * (x p)^2 ≤ (T ×ˢ T).card * (3 * 2^b + 9 + 7 * (b:ℝ)) := by
    have := sum_le_sum hxp
    rw [sum_const, nsmul_eq_mul] at this
    exact this
  rw [← mul_sum] at hsumx
  have hreal : 12 * 2^b * ((X:ℝ))^2 ≤ 3 * 2^b + 9 + 7 * (b:ℝ) := by
    rw [hXr, div_pow]
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    have h2b : (0:ℝ) ≤ 12 * 2^b := by positivity
    calc 12 * 2^b * (∑ p ∈ T ×ˢ T, x p)^2
        ≤ 12 * 2^b * ((T ×ˢ T).card * ∑ p ∈ T ×ˢ T, x p ^ 2) :=
          mul_le_mul_of_nonneg_left hCS h2b
      _ = (T ×ˢ T).card * (12 * 2^b * ∑ p ∈ T ×ˢ T, x p ^ 2) := by ring
      _ ≤ (T ×ˢ T).card * ((T ×ˢ T).card * (3 * 2^b + 9 + 7 * (b:ℝ))) :=
          mul_le_mul_of_nonneg_left hsumx hP.le
      _ = _ := by ring
  have : ((12 * (2:ℚ)^b * X^2 : ℚ) : ℝ) ≤ ((3 * (2:ℚ)^b + 9 + 7 * (b:ℚ) : ℚ) : ℝ) := by
    push_cast; exact hreal
  exact_mod_cast this

theorem fiber_upper {K : Type*} [DecidableEq K] {m : Nat} (g : Fin m → Sym → Bool)
    (fiber : Finset K) (σ : K → Fin m → Sym) (truth : K → K → Bool)
    (htruth : ∀ x ∈ fiber, ∀ y ∈ fiber, truth x y = truthC g (σ x) (σ y))
    (T : Finset K) (ι : K → (Fin m → Sym) → K)
    (hsum : ∀ f : K → ℝ, ∑ x ∈ fiber, f x = ∑ t ∈ T, ∑ u, f (ι t u))
    (hsig : ∀ t ∈ T, ∀ u, σ (ι t u) = u) (hmem : ∀ t ∈ T, ∀ u, ι t u ∈ fiber)
    (hT : T.Nonempty) (G : (Fin m → Sym) → (Fin m → Sym) → Bool) (t : Nat)
    (hG : ∑ u, ∑ v, sgn (G u v) * sgn (truthC g u v) =
      ((8:ℝ)^m)^2 * (1/2 + 1/2^(t+1)))
    {n : Nat} (send : K → Fin n) (read : Fin n → K → Bool)
    (hsr : ∀ x ∈ fiber, ∀ y ∈ fiber, read (send x) y = G (σ x) (σ y)) :
    3 * (2:ℚ)^t + 1 ≤ 4 * (2:ℚ)^t * ((((fiber.product fiber).filter
      (fun z => read (send z.1) z.2 = truth z.1 z.2)).card : ℚ) /
        ((fiber.product fiber).card : ℚ)) := by
  have hr := rate_identity g fiber σ truth htruth T ι hsum hsig hmem hT
    (fun x y => read (send x) y)
  have hP : (0:ℝ) < (T ×ˢ T).card := by exact_mod_cast (hT.product hT).card_pos
  have hN : (0:ℝ) < (8:ℝ)^m := by positivity
  have hinner : ∀ p ∈ T ×ˢ T, ∑ u, ∑ v, sgn (read (send (ι p.1 u)) (ι p.2 v)) * sgn (truthC g u v) =
      ((8:ℝ)^m)^2 * (1/2 + 1/2^(t+1)) := by
    intro p hp
    rw [mem_product] at hp
    rw [← hG]
    apply sum_congr rfl; intro u _; apply sum_congr rfl; intro v _
    rw [hsr _ (hmem _ hp.1 u) _ (hmem _ hp.2 v), hsig _ hp.1 u, hsig _ hp.2 v]
  rw [sum_congr rfl hinner, sum_const, nsmul_eq_mul] at hr
  set R := ((((fiber.product fiber).filter
      (fun z => read (send z.1) z.2 = truth z.1 z.2)).card : ℚ) /
        ((fiber.product fiber).card : ℚ)) with hRdef
  have hR : ((2 * R - 1 : ℚ) : ℝ) = 1/2 + 1/2^(t+1) := by
    rw [hr]; field_simp
  have hR2 : ((R : ℚ) : ℝ) = 3/4 + 1/2^(t+2) := by
    push_cast at hR
    have : (2:ℝ)^(t+2) = 2 * 2^(t+1) := by rw [pow_succ]; ring
    rw [this]
    field_simp at hR ⊢
    linarith
  have : ((3 * (2:ℚ)^t + 1 : ℚ) : ℝ) ≤ ((4 * (2:ℚ)^t * R : ℚ) : ℝ) := by
    push_cast
    rw [hR2]
    have : (2:ℝ)^(t+2) = 4 * 2^t := by rw [pow_add]; ring
    rw [this]
    field_simp
    ring_nf
    rfl
  exact_mod_cast this


def mkSym (b0 b1 b2 : Bool) : Sym :=
  fun i => match i.1 with | 0 => b0 | 1 => b1 | _ => b2

theorem sym_eq_mkSym (s : Sym) : s = mkSym (s 0) (s 1) (s 2) := by
  funext i
  fin_cases i <;> rfl

def symEquiv : Bool × Bool × Bool ≃ Sym where
  toFun t := mkSym t.1 t.2.1 t.2.2
  invFun s := (s 0, s 1, s 2)
  left_inv t := by rcases t with ⟨a, b, c⟩; rfl
  right_inv s := (sym_eq_mkSym s).symm

theorem sum_sym (f : Sym → ℝ) : ∑ w, f w =
    f (mkSym false false false) + f (mkSym false false true) + f (mkSym false true false) +
    f (mkSym false true true) + f (mkSym true false false) + f (mkSym true false true) +
    f (mkSym true true false) + f (mkSym true true true) := by
  rw [← Fintype.sum_equiv symEquiv (fun t => f (symEquiv t)) f (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [symEquiv, Equiv.coe_fn_mk]
  ring

theorem sxor_cancel (a w : Sym) : sxor a (sxor a w) = w := by
  funext v; simp only [sxor]; cases a v <;> cases w v <;> rfl

theorem sxor_shift (a a' w : Sym) : sxor (sxor a a') (sxor a w) = sxor a' w := by
  funext v; simp only [sxor]; cases a v <;> cases a' v <;> cases w v <;> rfl

theorem sxor_assoc' (a w r : Sym) : sxor (sxor a w) r = sxor a (sxor w r) := by
  funext v; simp only [sxor]; cases a v <;> cases w v <;> cases r v <;> rfl

def shiftEquiv (a : Sym) : Sym ≃ Sym where
  toFun w := sxor a w
  invFun w := sxor a w
  left_inv w := sxor_cancel a w
  right_inv w := sxor_cancel a w

def shiftREquiv (r : Sym) : Sym ≃ Sym where
  toFun w := sxor w r
  invFun w := sxor w r
  left_inv w := by funext v; simp only [sxor]; cases w v <;> cases r v <;> rfl
  right_inv w := by funext v; simp only [sxor]; cases w v <;> cases r v <;> rfl

theorem gam_reindex (G : Sym → Bool) (a a' : Sym) :
    gam G a a' = ∑ w, sgn (G w) * sgn (G (sxor (sxor a a') w)) := by
  unfold gam
  apply Fintype.sum_equiv (shiftEquiv a)
  intro w
  show _ = sgn (G (sxor a w)) * sgn (G (sxor (sxor a a') (sxor a w)))
  rw [sxor_shift]

theorem sgn_mul_ne (x y : Bool) : sgn x * sgn y = 1 - 2 * ((x != y).toNat : ℝ) := by
  cases x <;> cases y <;> simp [sgn] <;> norm_num

def cnt8 (G : Sym → Bool) (d : Sym) : Nat :=
  (G (mkSym false false false) != G (sxor d (mkSym false false false))).toNat +
  (G (mkSym false false true) != G (sxor d (mkSym false false true))).toNat +
  (G (mkSym false true false) != G (sxor d (mkSym false true false))).toNat +
  (G (mkSym false true true) != G (sxor d (mkSym false true true))).toNat +
  (G (mkSym true false false) != G (sxor d (mkSym true false false))).toNat +
  (G (mkSym true false true) != G (sxor d (mkSym true false true))).toNat +
  (G (mkSym true true false) != G (sxor d (mkSym true true false))).toNat +
  (G (mkSym true true true) != G (sxor d (mkSym true true true))).toNat

theorem gam_cnt (G : Sym → Bool) (d : Sym) :
    ∑ w, sgn (G w) * sgn (G (sxor d w)) = 8 - 2 * (cnt8 G d : ℝ) := by
  rw [sum_sym]
  simp only [sgn_mul_ne, cnt8]
  push_cast
  ring

theorem r2_cnt : ∀ o6 o8 a b d c2 d0 d1 d2 : Bool, (d0 || d1 || d2) = true →
    cnt8 (round2Expr o6 o8 a b d c2) (mkSym d0 d1 d2) = 2 ∨
      cnt8 (round2Expr o6 o8 a b d c2) (mkSym d0 d1 d2) = 6 := by
  decide

theorem r2_good (o6 o8 a b d c2 : Bool) : GoodG (round2Expr o6 o8 a b d c2) := by
  intro x y hxy
  rw [gam_reindex]
  have hd : ((sxor x y) 0 || (sxor x y) 1 || (sxor x y) 2) = true := by
    by_contra hc
    apply hxy
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    funext v
    have h0 := hc.1.1
    have h1 := hc.1.2
    have h2 := hc.2
    have hv3 : ∀ w : Fin 3, w = 0 ∨ w = 1 ∨ w = 2 := by decide
    have hv : sxor x y v = false := by
      rcases hv3 v with h | h | h <;> subst h <;> assumption
    simp only [sxor] at hv
    revert hv; cases x v <;> cases y v <;> simp
  rw [sym_eq_mkSym (sxor x y), gam_cnt]
  rcases r2_cnt o6 o8 a b d c2 _ _ _ hd with h | h <;> rw [h] <;> norm_num

theorem good_shift (G : Sym → Bool) (hG : GoodG G) (r : Sym) :
    GoodG (fun w => G (sxor w r)) := by
  intro a a' h
  have e : gam (fun w => G (sxor w r)) a a' = gam G a a' := by
    unfold gam
    apply Fintype.sum_equiv (shiftREquiv r)
    intro w
    show sgn (G (sxor (sxor a w) r)) * sgn (G (sxor (sxor a' w) r)) =
      sgn (G (sxor a (sxor w r))) * sgn (G (sxor a' (sxor w r)))
    rw [sxor_assoc', sxor_assoc']
  rw [e]; exact hG a a' h

def oldF (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (ref : Fin (2 ^ k))
    (p j : Nat) : Bool :=
  (stateAt k row constant 0 ref.val).testBit ((p + j) % k)

def gFun (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (ref : Fin (2 ^ k))
    (p : Nat) (sym : Sym) : Bool :=
  round2Expr (oldF k row constant ref p 6) (oldF k row constant ref p 8)
    (xor (xor (xor (oldF k row constant ref p 5) (oldF k row constant ref p 6))
      (oldF k row constant ref p 7))
      (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k))))
    (xor (xor (xor (oldF k row constant ref p 6) (oldF k row constant ref p 7))
      (oldF k row constant ref p 8))
      (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k))))
    (xor (xor (oldF k row constant ref p 6) (row.val.testBit ((p + 9) % k)))
      ((constant 1).val.testBit ((p + 8) % k)))
    (xor (xor (oldF k row constant ref p 4) (row.val.testBit ((p + 4) % k)))
      ((constant 2).val.testBit ((p + 5) % k)))
    sym

theorem gFun_good (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (ref : Fin (2 ^ k)) (p : Nat) : GoodG (gFun k row constant ref p) := by
  unfold gFun
  exact r2_good _ _ _ _ _ _

theorem s0_xor {k : Nat} (row : Fin (2^k)) (constant : Nat → Fin (2^k)) (l r f : Fin (2^k))
    (q : Nat) (hq : q < k) :
    (stateAt k row constant 0 ((l.val ^^^ r.val ^^^ f.val) % 2^k)).testBit q =
      xor (xor ((stateAt k row constant 0 l.val).testBit q)
        ((stateAt k row constant 0 r.val).testBit q))
        ((stateAt k row constant 0 f.val).testBit q) := by
  have hlt : l.val ^^^ r.val ^^^ f.val < 2^k := xor_lt (xor_lt l.isLt r.isLt) f.isLt
  rw [Nat.mod_eq_of_lt hlt]
  simp only [stateAt_zero, Nat.testBit_xor, testBit_rot hlt hq, testBit_rot l.isLt hq,
    testBit_rot r.isLt hq, testBit_rot f.isLt hq]
  have hb : ∀ a b c w : Bool,
      xor (xor (xor a b) c) w = xor (xor (xor a w) (xor b w)) (xor c w) := by decide
  exact hb _ _ _ _

theorem s0_flip {k : Nat} (row : Fin (2^k)) (constant : Nat → Fin (2^k)) (x : Fin (2^k))
    (M : Nat) (hM : M < 2^k) (q : Nat) (hq : q < k) :
    (stateAt k row constant 0 (x.val ^^^ M)).testBit q =
      xor ((stateAt k row constant 0 x.val).testBit q) (M.testBit ((q + k - 1 % k) % k)) := by
  have hlt : x.val ^^^ M < 2^k := xor_lt x.isLt hM
  simp only [stateAt_zero, Nat.testBit_xor, testBit_rot hlt hq, testBit_rot x.isLt hq]
  have hb : ∀ a m w : Bool, xor (xor a m) w = xor (xor a w) m := by decide
  exact hb _ _ _

def maskBits (k : Nat) (pm : Nat → Bool) : Nat :=
  (List.range k).foldl (fun acc j => acc ||| ((pm j).toNat <<< j)) 0

theorem testBit_maskBits (k : Nat) (pm : Nat → Bool) (j : Nat) :
    (maskBits k pm).testBit j = (decide (j < k) && pm j) := by
  unfold maskBits
  rw [testBit_foldl_or]
  simp

theorem maskBits_lt (k : Nat) (pm : Nat → Bool) : maskBits k pm < 2^k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_maskBits]
  have : ¬ j < k := by omega
  simp [this]

theorem predmod_eq {k x : Nat} (hk : 2 ≤ k) (hx : x < k) :
    (x + k - 1 % k) % k = if x = 0 then k - 1 else x - 1 := by
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1]
  split_ifs with hx0
  · subst hx0
    rw [Nat.mod_eq_of_lt (show 0 + k - 1 < k by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (show k ≤ x + k - 1 by omega),
      Nat.mod_eq_of_lt (show x + k - 1 - k < k by omega)]
    omega

theorem predmod_inj {k x y : Nat} (hk : 2 ≤ k) (hx : x < k) (hy : y < k)
    (h : (x + k - 1 % k) % k = (y + k - 1 % k) % k) : x = y := by
  rw [predmod_eq hk hx, predmod_eq hk hy] at h
  split_ifs at h <;> omega

theorem main_proof : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  let agree := fun (guess : K → K → Bool) =>
    (((pairs.filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) / (pairs.card : ℚ))
  let rate := fun (c : Nat) (send : K → Fin (2^c)) (read : Fin (2^c) → K → Bool) =>
    agree (fun left right => read (send left) right)
  (∀ b : Nat, b ≤ 3*m →
    ∀ (send : K → Fin (2^(3*m-b))) (read : Fin (2^(3*m-b)) → K → Bool),
      12*(2 : ℚ)^b*(2*rate (3*m-b) send read-1)^2 ≤ 3*(2 : ℚ)^b+9+7*(b : ℚ)) ∧
  (∀ t : Nat, 2^t ≤ 3*m+1 →
    ∃ (send : K → Fin (2^(3*m-t+1))) (read : Fin (2^(3*m-t+1)) → K → Bool),
      3*(2 : ℚ)^t+1 ≤ 4*(2 : ℚ)^t*rate (3*m-t+1) send read) := by
  intro k hk constant
  dsimp only
  intro m starts hm hInj row ref hgood pin hpin_in hpin_disj
  classical
  have hk12 : 12 ≤ k := by
    let i0 : Fin m := ⟨0, hm⟩
    let f : Fin 12 → Fin k := fun j => ⟨(starts i0 + j.val) % k, Nat.mod_lt _ hk⟩
    have hf : Function.Injective f := by
      intro j1 j2 h12
      have hv : (starts i0 + j1.val) % k = (starts i0 + j2.val) % k := congrArg Fin.val h12
      have hp : (i0, j1) = (i0, j2) := hInj hv
      exact congrArg Prod.snd hp
    simpa using Fintype.card_le_of_injective f hf
  have hk2 : 2 ≤ k := by omega
  have hInj3 : ∀ (iv1 iv2 : Fin m × Fin 3),
      (starts iv1.1 + 9 + iv1.2.val) % k = (starts iv2.1 + 9 + iv2.2.val) % k → iv1 = iv2 := by
    intro iv1 iv2 heq
    have h12 : (iv1.1, (⟨9 + iv1.2.val, by omega⟩ : Fin 12)) =
        (iv2.1, (⟨9 + iv2.2.val, by omega⟩ : Fin 12)) := by
      apply hInj
      simpa [Nat.add_assoc] using heq
    refine Prod.ext (congrArg (fun z : Fin m × Fin 12 => z.1) h12) (Fin.ext ?_)
    have h2 := congrArg (fun z : Fin m × Fin 12 => z.2.val) h12
    dsimp only at h2
    omega
  let sig : Fin (2^k) → Fin m → Sym := fun x i v =>
    (stateAt k row constant 0 x.val).testBit ((starts i + 9 + v.val) % k)
  let g : Fin m → Sym → Bool := fun i w => gFun k row constant ref (starts i) (sxor w (sig ref i))
  have hg : ∀ i, GoodG (g i) := fun i =>
    good_shift _ (gFun_good k row constant ref (starts i)) (sig ref i)
  let fiberF : Finset (Fin (2^k)) := univ.filter (fun keyWord => ∀ z ∈ pin,
    (stateAt k row constant 0 keyWord.val).testBit (z.val % k) =
      (stateAt k row constant 0 ref.val).testBit (z.val % k))
  let truthF : Fin (2^k) → Fin (2^k) → Bool := fun left right =>
    (∑ i : Fin m, ((stateAt k row constant 2 ((left.val ^^^ right.val ^^^ ref.val) % 2^k)).testBit
      ((starts i + 5) % k)).toNat) % 2 == 1
  have htruth : ∀ x ∈ fiberF, ∀ y ∈ fiberF, truthF x y = truthC g (sig x) (sig y) := by
    intro x hx y hy
    have hxf := (mem_filter.mp hx).2
    have hyf := (mem_filter.mp hy).2
    have hterm : ∀ i : Fin m,
        (stateAt k row constant 2 ((x.val ^^^ y.val ^^^ ref.val) % 2^k)).testBit
          ((starts i + 5) % k) = g i (sxor (sig x i) (sig y i)) := by
      intro i
      let keyF : Fin (2^k) :=
        ⟨(x.val ^^^ y.val ^^^ ref.val) % 2^k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
      have hs0 : ∀ q, q < k → (stateAt k row constant 0 keyF.val).testBit q =
          xor (xor ((stateAt k row constant 0 x.val).testBit q)
            ((stateAt k row constant 0 y.val).testBit q))
            ((stateAt k row constant 0 ref.val).testBit q) :=
        fun q hq => s0_xor row constant x y ref q hq
      have hag : ∀ j : Fin 9,
          (stateAt k row constant 0 keyF.val).testBit ((starts i + j.val) % k) =
            (stateAt k row constant 0 ref.val).testBit ((starts i + j.val) % k) := by
        intro j
        rcases hpin_in i j with ⟨z, hzpin, hzeq⟩
        rw [← hzeq, hs0 _ z.isLt]
        have h1 := hxf z hzpin
        have h2 := hyf z hzpin
        rw [Nat.mod_eq_of_lt z.isLt] at h1 h2
        rw [h1, h2]
        cases (stateAt k row constant 0 ref.val).testBit z.val <;> rfl
      have hev : (stateAt k row constant 2 keyF.val).testBit ((starts i + 5) % k) =
          gFun k row constant ref (starts i)
            (fun v => (stateAt k row constant 0 keyF.val).testBit ((starts i + 9 + v.val) % k)) :=
        guarded_row_eval hk2 constant row ref keyF (starts i) hag (hgood i)
      have hsym : (fun v : Fin 3 =>
          (stateAt k row constant 0 keyF.val).testBit ((starts i + 9 + v.val) % k)) =
          sxor (sxor (sig x i) (sig y i)) (sig ref i) := by
        funext v
        exact hs0 _ (Nat.mod_lt _ (by omega))
      rw [hsym] at hev
      exact hev
    show ((∑ i : Fin m, ((stateAt k row constant 2 ((x.val ^^^ y.val ^^^ ref.val) % 2^k)).testBit
      ((starts i + 5) % k)).toNat) % 2 == 1) =
        ((∑ i : Fin m, (g i (sxor (sig x i) (sig y i))).toNat) % 2 == 1)
    simp only [hterm]
  let pmF : (Fin m → Sym) → Nat → Bool := fun d j =>
    decide (∃ i : Fin m, ∃ v : Fin 3, d i v = true ∧
      ((starts i + 9 + v.val) % k + k - 1 % k) % k = j)
  let flipF : (Fin m → Sym) → Fin (2^k) → Fin (2^k) := fun d x =>
    ⟨x.val ^^^ maskBits k (pmF d), xor_lt x.isLt (maskBits_lt k _)⟩
  have hs0flip : ∀ d x q, q < k → (stateAt k row constant 0 (flipF d x).val).testBit q =
      xor ((stateAt k row constant 0 x.val).testBit q) (pmF d ((q + k - 1 % k) % k)) := by
    intro d x q hq
    show (stateAt k row constant 0 (x.val ^^^ maskBits k (pmF d))).testBit q = _
    rw [s0_flip row constant x _ (maskBits_lt k _) q hq, testBit_maskBits]
    have : (q + k - 1 % k) % k < k := Nat.mod_lt _ (by omega)
    simp [this]
  have hpm_pin : ∀ d, ∀ z ∈ pin, pmF d ((z.val + k - 1 % k) % k) = false := by
    intro d z hz
    simp only [pmF, decide_eq_false_iff_not, not_exists, not_and]
    intro i v _ heq
    have := predmod_inj hk2 (Nat.mod_lt _ (by omega)) z.isLt heq
    exact hpin_disj i v z hz this.symm
  have hpm_core : ∀ d (i : Fin m) (v : Fin 3),
      pmF d (((starts i + 9 + v.val) % k + k - 1 % k) % k) = d i v := by
    intro d i v
    by_cases hd : d i v = true
    · rw [hd]; simp only [pmF, decide_eq_true_iff]; exact ⟨i, v, hd, rfl⟩
    · have hd' : d i v = false := by simpa using hd
      rw [hd']; simp only [pmF, decide_eq_false_iff_not, not_exists, not_and]
      intro i' v' hd2 heq
      have h1 := predmod_inj hk2 (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
      have h2 := hInj3 (i', v') (i, v) h1
      simp only [Prod.mk.injEq] at h2
      rw [h2.1, h2.2] at hd2; exact hd hd2
  have hsigflip : ∀ d x, sig (flipF d x) = uxor (sig x) d := by
    intro d x; funext i v
    show (stateAt k row constant 0 (flipF d x).val).testBit ((starts i + 9 + v.val) % k) =
      xor ((stateAt k row constant 0 x.val).testBit ((starts i + 9 + v.val) % k)) (d i v)
    rw [hs0flip d x _ (Nat.mod_lt _ (by omega)), hpm_core]
  have hflip_mem : ∀ d x, x ∈ fiberF → flipF d x ∈ fiberF := by
    intro d x hx
    have hx' := (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨mem_univ _, fun z hz => ?_⟩
    have hz' := hx' z hz
    rw [Nat.mod_eq_of_lt z.isLt] at hz' ⊢
    rw [hs0flip d x z.val z.isLt, hpm_pin d z hz, Bool.xor_false]
    exact hz'
  have hflip_flip : ∀ d x, flipF d (flipF d x) = x := by
    intro d x; apply Fin.ext
    show (x.val ^^^ maskBits k (pmF d)) ^^^ maskBits k (pmF d) = x.val
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  let zero : Fin m → Sym := fun _ _ => false
  let T := fiberF.filter (fun x => sig x = zero)
  have huxor_self : ∀ u : Fin m → Sym, uxor u u = zero := by
    intro u; funext i v; simp [uxor, sxor, zero]
  have huxor_zero : ∀ u : Fin m → Sym, uxor zero u = u := by
    intro u; funext i v; simp [uxor, sxor, zero]
  have hsig : ∀ t ∈ T, ∀ u, sig ((fun t u => flipF u t) t u) = u := by
    intro t ht u; show sig (flipF u t) = u
    rw [hsigflip, (mem_filter.mp ht).2, huxor_zero]
  have hmem : ∀ t ∈ T, ∀ u, (fun t u => flipF u t) t u ∈ fiberF :=
    fun t ht u => hflip_mem u t (mem_filter.mp ht).1
  have hsum : ∀ f : Fin (2^k) → ℝ, ∑ x ∈ fiberF, f x = ∑ t ∈ T, ∑ u, f ((fun t u => flipF u t) t u) := by
    intro f
    show ∑ x ∈ fiberF, f x = ∑ t ∈ T, ∑ u, f (flipF u t)
    rw [← sum_product' (s := T) (t := univ) (f := fun t u => f (flipF u t))]
    symm
    apply sum_nbij' (fun p => flipF p.2 p.1) (fun x => (flipF (sig x) x, sig x))
    · intro p hp; rw [mem_product] at hp; exact hflip_mem _ _ (mem_filter.mp hp.1).1
    · intro x hx
      rw [mem_product]
      refine ⟨mem_filter.mpr ⟨hflip_mem _ _ hx, ?_⟩, mem_univ _⟩
      rw [hsigflip, huxor_self]
    · intro p hp
      rw [mem_product] at hp
      have h1 : sig (flipF p.2 p.1) = p.2 := by
        rw [hsigflip, (mem_filter.mp hp.1).2, huxor_zero]
      rw [h1, hflip_flip]
    · intro x _; exact hflip_flip _ _
    · intro p _; rfl
  have href : ref ∈ fiberF := mem_filter.mpr ⟨mem_univ _, fun _ _ => rfl⟩
  have hT : T.Nonempty :=
    ⟨flipF (sig ref) ref, mem_filter.mpr ⟨hflip_mem _ _ href, by rw [hsigflip, huxor_self]⟩⟩
  refine ⟨fun b hb send read => ?_, fun t ht => ?_⟩
  · rcases Nat.eq_zero_or_pos b with hb0 | hb1
    · subst hb0
      have key : ∀ r : ℚ, 0 ≤ r → r ≤ 1 →
          12 * (2:ℚ)^0 * (2*r - 1)^2 ≤ 3 * (2:ℚ)^0 + 9 + 7 * ((0:ℕ):ℚ) := by
        intro r h0 h1
        simp only [pow_zero, Nat.cast_zero]
        nlinarith
      refine key _ ?_ ?_
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      · exact div_le_one_of_le₀ (by exact_mod_cast card_filter_le _ _) (Nat.cast_nonneg _)
    · have hKpow : ((2^(3*m-b) : ℕ) : ℝ) * 2^b = 8^m := by
        push_cast
        rw [← pow_add, Nat.sub_add_cancel hb, pow_mul]; norm_num
      exact fiber_lower g hg fiberF sig truthF htruth T (fun t u => flipF u t) hsum hsig hmem hT
        b (3*m-b) hb1 hKpow send read
  · have htm : t ≤ 3*m := by
      by_contra hcon
      have h1 : 2^(3*m+1) ≤ 2^t := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 3*m+1 < 2^(3*m+1) := Nat.lt_two_pow_self
      omega
    have hcard : Fintype.card {s : Fin t → ZMod 2 // s ≠ 0} ≤ Fintype.card (Fin m × Fin 3) := by
      rw [Fintype.card_subtype, filter_ne', card_erase_of_mem (mem_univ _), card_univ,
        Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_fin]
      omega
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
    let pick : (Fin t → ZMod 2) → Fin m × Fin 3 := fun s =>
      if h : s ≠ 0 then emb ⟨s, h⟩ else (⟨0, hm⟩, 0)
    let H : Fin m × Fin 3 → (Fin t → ZMod 2) := fun c =>
      if h : ∃ s, emb s = c then (Classical.choose h).val else 0
    have hpick : ∀ s, s ≠ 0 → H (pick s) = s := by
      intro s hs
      have e1 : pick s = emb ⟨s, hs⟩ := dif_pos hs
      have hex : ∃ s', emb s' = pick s := ⟨⟨s, hs⟩, e1.symm⟩
      show (if h : ∃ s', emb s' = pick s then (Classical.choose h).val else 0) = s
      rw [dif_pos hex]
      have hspec := Classical.choose_spec hex
      rw [emb.injective (hspec.trans e1)]
    let corr : (Fin m → Sym) → (Fin m → Sym) := fun u =>
      if syn H u = 0 then u else uxor u (ue (pick (syn H u)).1 (pick (syn H u)).2)
    let beta : (Fin m → Sym) → Bool := fun u =>
      if syn H u = 0 then false else
        decide (gam (g (pick (syn H u)).1) (corr u (pick (syn H u)).1) (u (pick (syn H u)).1) < 0)
    obtain ⟨hsyn, hA⟩ := core_upper hm g hg H pick hpick corr (fun u => rfl) beta (fun u => rfl)
    have hkc := ker_count H pick hpick
    have hkc2 : (univ.filter (fun u : Fin m → Sym => syn H u = 0)).card = 2^(3*m-t) := by
      have h8 : (8:ℕ)^m = 2^(3*m-t) * 2^t := by
        rw [← pow_add, Nat.sub_add_cancel htm, pow_mul]; norm_num
      rw [h8] at hkc
      exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos t) hkc
    have hMsg : Fintype.card ({u : Fin m → Sym // syn H u = 0} × Bool) = 2^(3*m-t+1) := by
      rw [Fintype.card_prod, Fintype.card_subtype, Fintype.card_bool, hkc2, pow_succ]
    let eqv : ({u : Fin m → Sym // syn H u = 0} × Bool) ≃ Fin (2^(3*m-t+1)) :=
      (Fintype.equivFin _).trans (finCongr hMsg)
    let sendF : Fin (2^k) → Fin (2^(3*m-t+1)) := fun x =>
      eqv (⟨corr (sig x), hsyn (sig x)⟩, beta (sig x))
    let readF : Fin (2^(3*m-t+1)) → Fin (2^k) → Bool := fun n y =>
      xor (truthC g (eqv.symm n).1.val (sig y)) (eqv.symm n).2
    have hG : ∑ u, ∑ v, sgn ((fun u v => xor (truthC g (corr u) v) (beta u)) u v) *
        sgn (truthC g u v) = ((8:ℝ)^m)^2 * (1/2 + 1/2^(t+1)) := by
      show ∑ u, ∑ v, sgn (xor (truthC g (corr u) v) (beta u)) * sgn (truthC g u v) = _
      rw [hA]
      have hk1 : ((univ.filter (fun u : Fin m → Sym => syn H u = 0)).card : ℝ) =
          (8:ℝ)^m / 2^t := by
        rw [eq_div_iff (by positivity)]
        exact_mod_cast hkc
      rw [hk1, pow_succ]
      field_simp
      ring
    have hsr : ∀ x ∈ fiberF, ∀ y ∈ fiberF, readF (sendF x) y =
        (fun u v => xor (truthC g (corr u) v) (beta u)) (sig x) (sig y) := by
      intro x _ y _
      simp only [readF, sendF, Equiv.symm_apply_apply]
    exact ⟨sendF, readF, fiber_upper g fiberF sig truthF htruth T (fun t u => flipF u t) hsum
      hsig hmem hT (fun u v => xor (truthC g (corr u) v) (beta u)) t hG sendF readF hsr⟩

end

end PEqualNP.Outside.L_meta_29942_aux

theorem PEqualNP.Outside.L_meta_29942 : ∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc cell =>
      acc ||| ((xor (word.testBit cell)
        (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0
  let state := fun (row rounds key : Nat) =>
    (List.range rounds).foldl (fun prev tick =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * tick) key ^^^
        (constant (tick + 1)).val) (rot 1 key ^^^ row)
  let injected := fun (round key pos : Nat) =>
    xor ((rot (2 * (round - 1)) key).testBit (pos % k))
      ((constant round).val.testBit (pos % k))
  let bit := fun (row round key pos : Nat) => (state row round key).testBit (pos % k)
  ∀ (m : Nat) (starts : Fin m → Nat),
  0 < m → Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val) % k) →
  let good := fun (row ref : Fin (2^k)) (p : Nat) =>
    let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
    let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
    let τ := xor (xor (old 6) (old 7)) (old 8)
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (injected 1 ref.val (p+6))
    let β := xor τ (injected 1 ref.val (p+7))
    τ = false ∧ xor (xor (first 3) (first 4)) (first 5) = true ∧
      xor (first 4) (first 5) = !α ∧ first 4 = β
  ∀ (row ref : Fin (2^k)), (∀ i, good row ref (starts i)) →
  ∀ pin : Finset (Fin k),
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val) % k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val) % k) →
  let K := Fin (2^k)
  let fiber := (Finset.univ : Finset K).filter (fun key =>
    ∀ z ∈ pin, bit row.val 0 key.val z.val = bit row.val 0 ref.val z.val)
  let pairs := fiber.product fiber
  let truth := fun (left right : K) =>
    let key := (left.val ^^^ right.val ^^^ ref.val) % 2^k
    (∑ i : Fin m, (bit row.val 2 key (starts i+5)).toNat) % 2 == 1
  let agree := fun (guess : K → K → Bool) =>
    (((pairs.filter (fun z => guess z.1 z.2 = truth z.1 z.2)).card : ℚ) / (pairs.card : ℚ))
  let rate := fun (c : Nat) (send : K → Fin (2^c)) (read : Fin (2^c) → K → Bool) =>
    agree (fun left right => read (send left) right)
  (∀ b : Nat, b ≤ 3*m →
    ∀ (send : K → Fin (2^(3*m-b))) (read : Fin (2^(3*m-b)) → K → Bool),
      12*(2 : ℚ)^b*(2*rate (3*m-b) send read-1)^2 ≤ 3*(2 : ℚ)^b+9+7*(b : ℚ)) ∧
  (∀ t : Nat, 2^t ≤ 3*m+1 →
    ∃ (send : K → Fin (2^(3*m-t+1))) (read : Fin (2^(3*m-t+1)) → K → Bool),
      3*(2 : ℚ)^t+1 ≤ 4*(2 : ℚ)^t*rate (3*m-t+1) send read) :=
  PEqualNP.Outside.L_meta_29942_aux.main_proof
