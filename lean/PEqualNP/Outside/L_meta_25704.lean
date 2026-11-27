import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25704_aux

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

def par (n : Nat) : Bool := n % 2 == 1

def monEval {α : Type} (m : Finset α) (x : α → Bool) : Bool :=
  decide (∀ j ∈ m, x j = true)

def evalPoly {α : Type} (T : Finset (Finset α)) (x : α → Bool) : Bool :=
  par ((T.filter (fun m => ∀ j ∈ m, x j = true)).card)

def degPoly {α : Type} (u : Nat) (f : (α → Bool) → Bool) : Prop :=
  ∃ T : Finset (Finset α), (∀ m ∈ T, m.card ≤ u) ∧ ∀ x, f x = evalPoly T x

def toggleMem {α : Type} [DecidableEq α] (T : Finset (Finset α)) (m : Finset α) :
    Finset (Finset α) :=
  if m ∈ T then T.erase m else insert m T

theorem par_succ (n : Nat) : par (n + 1) = xor (par n) true := by
  unfold par
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h1 : (n + 1) % 2 = 1 := by omega
    simp [h, h1]
  · have h1 : (n + 1) % 2 = 0 := by omega
    simp [h, h1]

theorem par_sub_one {n : Nat} (hn : 1 ≤ n) : par (n - 1) = xor (par n) true := by
  have h := par_succ (n - 1)
  rw [Nat.sub_add_cancel hn] at h
  rw [h]
  cases par (n - 1) <;> rfl

theorem evalPoly_empty {α : Type} (x : α → Bool) :
    evalPoly (∅ : Finset (Finset α)) x = false := by
  simp [evalPoly, par]

theorem evalPoly_singleton {α : Type} (m : Finset α) (x : α → Bool) :
    evalPoly {m} x = monEval m x := by
  unfold evalPoly monEval par
  by_cases h : ∀ j ∈ m, x j = true
  · rw [Finset.filter_singleton, if_pos h, decide_eq_true h]
    simp
  · rw [Finset.filter_singleton, if_neg h, decide_eq_false h]
    simp

theorem evalPoly_toggleMem {α : Type} [DecidableEq α] (T : Finset (Finset α))
    (m : Finset α) (x : α → Bool) :
    evalPoly (toggleMem T m) x = xor (evalPoly T x) (monEval m x) := by
  unfold toggleMem evalPoly monEval
  by_cases hm : ∀ j ∈ m, x j = true
  · rw [decide_eq_true hm]
    by_cases hmem : m ∈ T
    · simp only [hmem, ite_true]
      have hfilt : (T.erase m).filter (fun s => ∀ j ∈ s, x j = true) =
          (T.filter (fun s => ∀ j ∈ s, x j = true)).erase m := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      have hmin : m ∈ T.filter (fun s => ∀ j ∈ s, x j = true) :=
        Finset.mem_filter.mpr ⟨hmem, hm⟩
      rw [hfilt, Finset.card_erase_of_mem hmin]
      exact par_sub_one (Finset.card_pos.mpr ⟨m, hmin⟩)
    · simp only [hmem, ite_false]
      have hfilt : (insert m T).filter (fun s => ∀ j ∈ s, x j = true) =
          insert m (T.filter (fun s => ∀ j ∈ s, x j = true)) := by
        ext s
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | hs, hxs⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨hs, hxs⟩
        · rintro (rfl | ⟨hs, hxs⟩)
          · exact ⟨Or.inl rfl, hm⟩
          · exact ⟨Or.inr hs, hxs⟩
      have hnin : m ∉ T.filter (fun s => ∀ j ∈ s, x j = true) := by
        intro h
        exact hmem (Finset.mem_filter.mp h).1
      rw [hfilt, Finset.card_insert_of_notMem hnin]
      exact par_succ _
  · rw [decide_eq_false hm, Bool.xor_false]
    by_cases hmem : m ∈ T
    · simp only [hmem, ite_true]
      congr 2
      ext s
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨⟨_, hs⟩, hxs⟩
        exact ⟨hs, hxs⟩
      · rintro ⟨hs, hxs⟩
        refine ⟨⟨?_, hs⟩, hxs⟩
        intro hsm
        subst hsm
        exact hm hxs
    · simp only [hmem, ite_false]
      congr 2
      ext s
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hs, hxs⟩
        · exact absurd hxs hm
        · exact ⟨hs, hxs⟩
      · rintro ⟨hs, hxs⟩
        exact ⟨Or.inr hs, hxs⟩

theorem evalPoly_insert {α : Type} [DecidableEq α] {T : Finset (Finset α)} {m : Finset α}
    (hm : m ∉ T) (x : α → Bool) :
    evalPoly (insert m T) x = xor (evalPoly T x) (monEval m x) := by
  have h := evalPoly_toggleMem T m x
  simp [toggleMem, hm] at h
  exact h

theorem toggleMem_card_le {α : Type} [DecidableEq α] {T : Finset (Finset α)} {m : Finset α}
    {u : Nat} (hT : ∀ s ∈ T, s.card ≤ u) (hm : m.card ≤ u) :
    ∀ s ∈ toggleMem T m, s.card ≤ u := by
  intro s hs
  unfold toggleMem at hs
  by_cases hmem : m ∈ T
  · simp only [hmem, ite_true, Finset.mem_erase] at hs
    exact hT s hs.2
  · simp only [hmem, ite_false, Finset.mem_insert] at hs
    rcases hs with rfl | hs
    · exact hm
    · exact hT s hs

theorem degPoly_mono {α : Type} {u v : Nat} {f : (α → Bool) → Bool} (huv : u ≤ v)
    (hf : degPoly u f) : degPoly v f := by
  rcases hf with ⟨T, hT, he⟩
  exact ⟨T, fun m hm => (hT m hm).trans huv, he⟩

theorem degPoly_const {α : Type} (u : Nat) (c : Bool) : degPoly (α := α) u (fun _ => c) := by
  cases c
  · exact ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), fun x => (evalPoly_empty x).symm⟩
  · refine ⟨{∅}, fun m hm => ?_, fun x => ?_⟩
    · simp only [Finset.mem_singleton] at hm
      subst hm
      simp
    · rw [evalPoly_singleton]
      simp [monEval]

theorem degPoly_var {α : Type} [DecidableEq α] (a : α) : degPoly 1 (fun x : α → Bool => x a) := by
  refine ⟨{{a}}, fun m hm => ?_, fun x => ?_⟩
  · simp only [Finset.mem_singleton] at hm
    subst hm
    simp
  · rw [evalPoly_singleton]
    simp [monEval]

theorem degPoly_xor {α : Type} [DecidableEq α] {u : Nat} {f g : (α → Bool) → Bool}
    (hf : degPoly u f) (hg : degPoly u g) : degPoly u (fun x => xor (f x) (g x)) := by
  rcases hf with ⟨T1, hT1, he1⟩
  rcases hg with ⟨T2, hT2, he2⟩
  suffices h : ∀ S : Finset (Finset α), (∀ m ∈ S, m.card ≤ u) →
      ∀ R : Finset (Finset α), (∀ m ∈ R, m.card ≤ u) →
      ∃ T : Finset (Finset α), (∀ m ∈ T, m.card ≤ u) ∧
        ∀ x, evalPoly T x = xor (evalPoly R x) (evalPoly S x) by
    rcases h T2 hT2 T1 hT1 with ⟨T, hT, he⟩
    exact ⟨T, hT, fun x => by dsimp only; rw [he1 x, he2 x, ← he x]⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _ R hR
    exact ⟨R, hR, fun x => by simp [evalPoly_empty]⟩
  | @insert m S hm ih =>
    intro hS R hR
    have hm_le : m.card ≤ u := hS m (Finset.mem_insert_self m S)
    have hS' : ∀ s ∈ S, s.card ≤ u := fun s hs => hS s (Finset.mem_insert_of_mem hs)
    rcases ih hS' (toggleMem R m) (toggleMem_card_le hR hm_le) with ⟨T, hT, he⟩
    refine ⟨T, hT, fun x => ?_⟩
    rw [he x, evalPoly_toggleMem, evalPoly_insert hm]
    cases evalPoly R x <;> cases monEval m x <;> cases evalPoly S x <;> rfl

theorem degPoly_not {α : Type} [DecidableEq α] {u : Nat} {f : (α → Bool) → Bool}
    (hf : degPoly u f) : degPoly u (fun x => !(f x)) := by
  have h := degPoly_xor hf (degPoly_const u true)
  rcases h with ⟨T, hT, he⟩
  exact ⟨T, hT, fun x => by dsimp only; rw [← he x]; dsimp only; cases f x <;> rfl⟩

theorem monEval_union {α : Type} [DecidableEq α] (m1 m2 : Finset α) (x : α → Bool) :
    (monEval m1 x && monEval m2 x) = monEval (m1 ∪ m2) x := by
  unfold monEval
  by_cases h1 : ∀ j ∈ m1, x j = true <;> by_cases h2 : ∀ j ∈ m2, x j = true
  · have h12 : ∀ j ∈ m1 ∪ m2, x j = true := by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact h1 j hj
      · exact h2 j hj
    rw [decide_eq_true h1, decide_eq_true h2, decide_eq_true h12]
    rfl
  · have h12 : ¬ (∀ j ∈ m1 ∪ m2, x j = true) := fun h => h2 (fun j hj => h j (Finset.mem_union_right m1 hj))
    rw [decide_eq_true h1, decide_eq_false h2, decide_eq_false h12]
    rfl
  · have h12 : ¬ (∀ j ∈ m1 ∪ m2, x j = true) := fun h => h1 (fun j hj => h j (Finset.mem_union_left m2 hj))
    rw [decide_eq_false h1, decide_eq_true h2, decide_eq_false h12]
    rfl
  · have h12 : ¬ (∀ j ∈ m1 ∪ m2, x j = true) := fun h => h1 (fun j hj => h j (Finset.mem_union_left m2 hj))
    rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h12]
    rfl

theorem degPoly_mon_mul {α : Type} [DecidableEq α] {u v : Nat} (m1 : Finset α) (hm1 : m1.card ≤ u)
    (T2 : Finset (Finset α)) (hT2 : ∀ m ∈ T2, m.card ≤ v) :
    degPoly (u + v) (fun x => monEval m1 x && evalPoly T2 x) := by
  induction T2 using Finset.induction_on with
  | empty =>
    refine ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), fun x => ?_⟩
    simp [evalPoly_empty]
  | @insert m2 T2 hm2 ih =>
    have hm2_le : m2.card ≤ v := hT2 m2 (Finset.mem_insert_self m2 T2)
    have hT2' : ∀ m ∈ T2, m.card ≤ v := fun m hm => hT2 m (Finset.mem_insert_of_mem hm)
    have h1 := ih hT2'
    have h2 : degPoly (u + v) (fun x => monEval (m1 ∪ m2) x) := by
      refine ⟨{m1 ∪ m2}, fun m hm => ?_, fun x => ?_⟩
      · simp only [Finset.mem_singleton] at hm
        subst hm
        exact (Finset.card_union_le m1 m2).trans (Nat.add_le_add hm1 hm2_le)
      · exact (evalPoly_singleton (m1 ∪ m2) x).symm
    rcases degPoly_xor h1 h2 with ⟨T, hT, he⟩
    refine ⟨T, hT, fun x => ?_⟩
    dsimp only
    rw [← he x]
    dsimp only
    rw [evalPoly_insert hm2, ← monEval_union]
    cases monEval m1 x <;> cases evalPoly T2 x <;> cases monEval m2 x <;> rfl

theorem degPoly_mul {α : Type} [DecidableEq α] {u v : Nat} {f g : (α → Bool) → Bool}
    (hf : degPoly u f) (hg : degPoly v g) : degPoly (u + v) (fun x => f x && g x) := by
  rcases hf with ⟨T1, hT1, he1⟩
  rcases hg with ⟨T2, hT2, he2⟩
  suffices h : ∀ S : Finset (Finset α), (∀ m ∈ S, m.card ≤ u) →
      degPoly (u + v) (fun x => evalPoly S x && evalPoly T2 x) by
    rcases h T1 hT1 with ⟨T, hT, he⟩
    exact ⟨T, hT, fun x => by dsimp only; rw [he1 x, he2 x, ← he x]⟩
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), fun x => by simp [evalPoly_empty]⟩
  | @insert m1 S hm1 ih =>
    intro hS
    have hm1_le : m1.card ≤ u := hS m1 (Finset.mem_insert_self m1 S)
    have hS' : ∀ m ∈ S, m.card ≤ u := fun m hm => hS m (Finset.mem_insert_of_mem hm)
    rcases degPoly_xor (ih hS') (degPoly_mon_mul m1 hm1_le T2 hT2) with ⟨T, hT, he⟩
    refine ⟨T, hT, fun x => ?_⟩
    dsimp only
    rw [← he x]
    dsimp only
    rw [evalPoly_insert hm1]
    cases evalPoly S x <;> cases monEval m1 x <;> cases evalPoly T2 x <;> rfl

def mkSym (b0 b1 b2 : Bool) : Fin 3 → Bool :=
  fun i => match i.1 with | 0 => b0 | 1 => b1 | _ => b2

theorem sym_eq_mkSym (s : Fin 3 → Bool) : s = mkSym (s 0) (s 1) (s 2) := by
  funext i
  fin_cases i <;> rfl

def xor8 (g : (Fin 3 → Bool) → Bool) : Bool :=
  xor (xor (xor (g (mkSym false false false)) (g (mkSym false false true)))
           (xor (g (mkSym false true false)) (g (mkSym false true true))))
      (xor (xor (g (mkSym true false false)) (g (mkSym true false true)))
           (xor (g (mkSym true true false)) (g (mkSym true true true))))

theorem xor_swap4 (a b c d : Bool) :
    xor (xor a b) (xor c d) = xor (xor a c) (xor b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem xor8_xor (f g : (Fin 3 → Bool) → Bool) :
    xor8 (fun s => xor (f s) (g s)) = xor (xor8 f) (xor8 g) := by
  unfold xor8
  rw [xor_swap4 (f (mkSym false false false)) (g (mkSym false false false))
        (f (mkSym false false true)) (g (mkSym false false true))]
  rw [xor_swap4 (f (mkSym false true false)) (g (mkSym false true false))
        (f (mkSym false true true)) (g (mkSym false true true))]
  rw [xor_swap4 (f (mkSym true false false)) (g (mkSym true false false))
        (f (mkSym true false true)) (g (mkSym true false true))]
  rw [xor_swap4 (f (mkSym true true false)) (g (mkSym true true false))
        (f (mkSym true true true)) (g (mkSym true true true))]
  rw [xor_swap4 (xor (f (mkSym false false false)) (f (mkSym false false true)))
        (xor (g (mkSym false false false)) (g (mkSym false false true)))
        (xor (f (mkSym false true false)) (f (mkSym false true true)))
        (xor (g (mkSym false true false)) (g (mkSym false true true)))]
  rw [xor_swap4 (xor (f (mkSym true false false)) (f (mkSym true false true)))
        (xor (g (mkSym true false false)) (g (mkSym true false true)))
        (xor (f (mkSym true true false)) (f (mkSym true true true)))
        (xor (g (mkSym true true false)) (g (mkSym true true true)))]
  exact xor_swap4 _ _ _ _

theorem xor8_monEval_le_two :
    ∀ mon : Finset (Fin 3), mon.card ≤ 2 → xor8 (monEval mon) = false := by
  decide

def toggleIf (b : Bool) (m : Finset (Fin 3)) (T : Finset (Finset (Fin 3))) :
    Finset (Finset (Fin 3)) :=
  if b then toggleMem T m else T

theorem evalPoly_toggleIf (b : Bool) (m : Finset (Fin 3)) (T : Finset (Finset (Fin 3)))
    (s : Fin 3 → Bool) :
    evalPoly (toggleIf b m T) s = xor (evalPoly T s) (b && monEval m s) := by
  cases b
  · simp [toggleIf]
  · simp [toggleIf, evalPoly_toggleMem]

theorem toggleIf_card_le (b : Bool) (m : Finset (Fin 3)) (T : Finset (Finset (Fin 3)))
    (hm : m.card ≤ 2) (hT : ∀ x ∈ T, x.card ≤ 2) :
    ∀ x ∈ toggleIf b m T, x.card ≤ 2 := by
  cases b
  · exact hT
  · exact toggleMem_card_le hT hm

theorem low_iff_xor8 (g : (Fin 3 → Bool) → Bool) :
    degPoly 2 g ↔ xor8 g = false := by
  constructor
  · rintro ⟨T, hT, he⟩
    have hfun : g = evalPoly T := funext he
    rw [hfun]
    clear he hfun g
    induction T using Finset.induction_on with
    | empty => rfl
    | @insert m T hm ih =>
      have hcard : m.card ≤ 2 := hT m (Finset.mem_insert_self m T)
      have hT' : ∀ s ∈ T, s.card ≤ 2 := fun s hs => hT s (Finset.mem_insert_of_mem hs)
      have hfun2 : evalPoly (insert m T) = fun s => xor (evalPoly T s) (monEval m s) :=
        funext (evalPoly_insert hm)
      rw [hfun2, xor8_xor, ih hT', xor8_monEval_le_two m hcard]
      rfl
  · intro hx
    set g000 := g (mkSym false false false)
    set g001 := g (mkSym false false true)
    set g010 := g (mkSym false true false)
    set g011 := g (mkSym false true true)
    set g100 := g (mkSym true false false)
    set g101 := g (mkSym true false true)
    set g110 := g (mkSym true true false)
    set g111 := g (mkSym true true true)
    set c0 := g000
    set c1 := xor g000 g100
    set c2 := xor g000 g010
    set c3 := xor g000 g001
    set c12 := xor (xor (xor g000 g100) g010) g110
    set c13 := xor (xor (xor g000 g100) g001) g101
    set c23 := xor (xor (xor g000 g010) g001) g011
    let T0 : Finset (Finset (Fin 3)) := ∅
    let T1 := toggleIf c0 ∅ T0
    let T2 := toggleIf c1 {0} T1
    let T3 := toggleIf c2 {1} T2
    let T4 := toggleIf c3 {2} T3
    let T5 := toggleIf c12 {0, 1} T4
    let T6 := toggleIf c13 {0, 2} T5
    let T7 := toggleIf c23 {1, 2} T6
    refine ⟨T7, ?_, ?_⟩
    · apply toggleIf_card_le _ _ _ (by decide)
      apply toggleIf_card_le _ _ _ (by decide)
      apply toggleIf_card_le _ _ _ (by decide)
      apply toggleIf_card_le _ _ _ (by decide)
      apply toggleIf_card_le _ _ _ (by decide)
      apply toggleIf_card_le _ _ _ (by decide)
      apply toggleIf_card_le _ _ _ (by decide)
      intro _ h
      exact absurd h (Finset.notMem_empty _)
    · intro s
      rw [sym_eq_mkSym s]
      simp only [T7, T6, T5, T4, T3, T2, T1, T0, evalPoly_toggleIf, evalPoly_empty]
      have hx' : xor (xor (xor g000 g001) (xor g010 g011))
          (xor (xor g100 g101) (xor g110 g111)) = false := hx
      cases s 0 <;> cases s 1 <;> cases s 2
      · change g000 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym false false false) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym false false false) = false := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym false false false) = false := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym false false false) = false := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym false false false) = false := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym false false false) = false := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym false false false) = false := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
      · change g001 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym false false true) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym false false true) = false := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym false false true) = false := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym false false true) = true := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym false false true) = false := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym false false true) = false := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym false false true) = false := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
        cases g000 <;> cases g001 <;> rfl
      · change g010 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym false true false) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym false true false) = false := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym false true false) = true := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym false true false) = false := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym false true false) = false := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym false true false) = false := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym false true false) = false := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
        cases g000 <;> cases g010 <;> rfl
      · change g011 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym false true true) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym false true true) = false := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym false true true) = true := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym false true true) = true := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym false true true) = false := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym false true true) = false := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym false true true) = true := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
        cases g000 <;> cases g001 <;> cases g010 <;> cases g011 <;> rfl
      · change g100 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym true false false) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym true false false) = true := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym true false false) = false := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym true false false) = false := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym true false false) = false := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym true false false) = false := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym true false false) = false := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
        cases g000 <;> cases g100 <;> rfl
      · change g101 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym true false true) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym true false true) = true := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym true false true) = false := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym true false true) = true := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym true false true) = false := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym true false true) = true := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym true false true) = false := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
        cases g000 <;> cases g001 <;> cases g100 <;> cases g101 <;> rfl
      · change g110 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym true true false) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym true true false) = true := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym true true false) = true := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym true true false) = false := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym true true false) = true := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym true true false) = false := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym true true false) = false := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        simp only [c0, c1, c2, c3, c12, c13, c23, Bool.and_false, Bool.and_true, Bool.xor_false, Bool.false_xor]
        cases g000 <;> cases g010 <;> cases g100 <;> cases g110 <;> rfl
      · change g111 = _
        have hm0 : monEval (∅ : Finset (Fin 3)) (mkSym true true true) = true := by decide
        have hm1 : monEval ({0} : Finset (Fin 3)) (mkSym true true true) = true := by decide
        have hm2 : monEval ({1} : Finset (Fin 3)) (mkSym true true true) = true := by decide
        have hm3 : monEval ({2} : Finset (Fin 3)) (mkSym true true true) = true := by decide
        have hm12 : monEval ({0, 1} : Finset (Fin 3)) (mkSym true true true) = true := by decide
        have hm13 : monEval ({0, 2} : Finset (Fin 3)) (mkSym true true true) = true := by decide
        have hm23 : monEval ({1, 2} : Finset (Fin 3)) (mkSym true true true) = true := by decide
        rw [hm0, hm1, hm2, hm3, hm12, hm13, hm23]
        have hlast : ∀ a0 a1 a2 a3 a4 a5 a6 a7 : Bool,
            xor (xor (xor a0 a1) (xor a2 a3)) (xor (xor a4 a5) (xor a6 a7)) = false →
            a7 = xor (xor (xor (xor (xor (xor (xor false (a0 && true))
              (xor a0 a4 && true)) (xor a0 a2 && true)) (xor a0 a1 && true))
              (xor (xor (xor a0 a4) a2) a6 && true))
              (xor (xor (xor a0 a4) a1) a5 && true))
              (xor (xor (xor a0 a2) a1) a3 && true) := by decide
        exact hlast g000 g001 g010 g011 g100 g101 g110 g111 hx'

theorem xor8_cubic : xor8 (fun s : Fin 3 → Bool => s 0 && s 1 && s 2) = true := rfl

theorem xor8_point (b : Fin 3 → Bool) : xor8 (fun s : Fin 3 → Bool => decide (s = b)) = true := by
  rw [sym_eq_mkSym b]
  generalize b 0 = b0
  generalize b 1 = b1
  generalize b 2 = b2
  cases b0 <;> cases b1 <;> cases b2 <;> decide

theorem exists_ne_cubic_xor {Q L : (Fin 3 → Bool) → Bool} (hQ : degPoly 2 Q) (hL : degPoly 2 L) :
    ∃ s : Fin 3 → Bool, L s ≠ xor (s 0 && s 1 && s 2) (Q s) := by
  by_contra h
  push Not at h
  have heq : L = fun s => xor (s 0 && s 1 && s 2) (Q s) := funext h
  have h1 : xor8 L = false := (low_iff_xor8 L).mp hL
  have h2 : xor8 Q = false := (low_iff_xor8 Q).mp hQ
  rw [heq, xor8_xor, xor8_cubic, h2] at h1
  exact Bool.noConfusion h1

theorem low_point_flip {Q : (Fin 3 → Bool) → Bool} (hQ : degPoly 2 Q) (b : Fin 3 → Bool) :
    degPoly 2 (fun s => xor (xor (s 0 && s 1 && s 2) (Q s)) (decide (s = b))) := by
  rw [low_iff_xor8, xor8_xor, xor8_xor, xor8_cubic, (low_iff_xor8 Q).mp hQ, xor8_point b]
  rfl

theorem low_known_bit0 {Q : (Fin 3 → Bool) → Bool} (hQ : degPoly 2 Q) (b0 : Bool) :
    degPoly 2 (fun s => xor (if b0 then (s 1 && s 2) else false) (Q s)) := by
  rw [low_iff_xor8, xor8_xor, (low_iff_xor8 Q).mp hQ]
  cases b0 <;> rfl

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

theorem xor8_round2Expr (o6 o8 a b d c2 : Bool) :
    xor8 (fun sym => xor (sym 0 && sym 1 && sym 2) (round2Expr o6 o8 a b d c2 sym)) = false := by
  cases o6 <;> cases o8 <;> cases a <;> cases b <;> cases d <;> cases c2 <;> rfl

theorem low_round2Q (o6 o8 a b d c2 : Bool) :
    degPoly 2 (fun sym => xor (sym 0 && sym 1 && sym 2) (round2Expr o6 o8 a b d c2 sym)) :=
  (low_iff_xor8 _).mpr (xor8_round2Expr o6 o8 a b d c2)

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

def runFn {K : Type} (steps : Nat) (ask : Nat → Nat → K → Bool) (x : K) : Nat :=
  (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0

theorem runFn_zero {K : Type} (ask : Nat → Nat → K → Bool) (x : K) :
    runFn 0 ask x = 0 := rfl

theorem runFn_succ {K : Type} (t : Nat) (ask : Nat → Nat → K → Bool) (x : K) :
    runFn (t + 1) ask x = runFn t ask x + ((ask t (runFn t ask x) x).toNat <<< t) := by
  simp [runFn, List.range_succ]

theorem runFn_lt {K : Type} (t : Nat) (ask : Nat → Nat → K → Bool) (x : K) :
    runFn t ask x < 2 ^ t := by
  induction t with
  | zero => simp [runFn]
  | succ t ih =>
    rw [runFn_succ, Nat.shiftLeft_eq, Nat.pow_succ]
    cases ask t (runFn t ask x) x <;> simp <;> omega

theorem runFn_add_exists {K : Type} (t r : Nat) (ask : Nat → Nat → K → Bool) (x : K) :
    ∃ q < 2 ^ r, runFn (t + r) ask x = runFn t ask x + q * 2 ^ t := by
  induction r with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ r ih =>
    rcases ih with ⟨q, hq, heq⟩
    refine ⟨q + (ask (t + r) (runFn (t + r) ask x) x).toNat * 2 ^ r, ?_, ?_⟩
    · rw [Nat.pow_succ]
      cases ask (t + r) (runFn (t + r) ask x) x <;> simp <;> omega
    · rw [← Nat.add_assoc, runFn_succ, heq, Nat.shiftLeft_eq, Nat.pow_add]
      ring

theorem runFn_testBit {K : Type} {t steps : Nat} (ht : t < steps)
    (ask : Nat → Nat → K → Bool) (x : K) :
    (runFn steps ask x).testBit t = ask t (runFn t ask x) x := by
  have hsplit : steps = (t + 1) + (steps - (t + 1)) := by omega
  rcases runFn_add_exists (t + 1) (steps - (t + 1)) ask x with ⟨q, _, heq⟩
  rw [← hsplit] at heq
  rw [heq, runFn_succ, Nat.shiftLeft_eq, Nat.pow_succ]
  have hlt : runFn t ask x < 2 ^ t := runFn_lt t ask x
  have hform : runFn t ask x + (ask t (runFn t ask x) x).toNat * 2 ^ t + q * (2 ^ t * 2) =
      runFn t ask x + ((ask t (runFn t ask x) x).toNat + 2 * q) * 2 ^ t := by ring
  rw [hform]
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos t),
    Nat.div_eq_of_lt hlt, Nat.zero_add, Nat.and_comm, Nat.and_one_is_mod]
  cases ask t (runFn t ask x) x
  · have hm : (0 + 2 * q) % 2 = 0 := by omega
    simp [hm]
  · have hm : (1 + 2 * q) % 2 = 1 := by omega
    simp [hm]

theorem runFn_div_pow_mod {K : Type} (n s g : Nat) (hg : g < 2 ^ s)
    (ask : Nat → Nat → K → Bool) (x : K)
    (hask : ∀ r < s, ask (n + r) (runFn (n + r) ask x) x = g.testBit r) :
    (runFn (n + s) ask x / 2 ^ n) % 2 ^ s = g := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow]
  by_cases hj : j < s
  · simp only [hj, decide_true, Bool.true_and]
    rw [← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    exact (runFn_testBit (by omega : n + j < n + s) ask x).trans (hask j hj)
  · simp only [hj, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (hg.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))).symm

theorem sum_mod_two_eq_zero {α : Type} [DecidableEq α] (S : Finset α) (f : α → Nat)
    (hf : ∀ x ∈ S, f x % 2 = 0) : (∑ x ∈ S, f x) % 2 = 0 := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a S)
    have h2 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    omega

theorem exists_patch_evalPoly_true {α : Type} [DecidableEq α]
    (T : Finset (Finset α)) (D : Nat) (hT : ∀ f ∈ T, f.card ≤ D)
    (w0 : α → Bool) (hw0 : evalPoly T w0 = true) :
    ∃ U ∈ T, U.card ≤ D ∧ ∀ w : α → Bool, ∃ A ∈ U.powerset,
      evalPoly T (fun v => if v ∈ U then decide (v ∈ A) else w v) = true := by
  have hTne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    rw [evalPoly_empty] at hw0
    exact Bool.noConfusion hw0
  rcases Finset.exists_max_image T Finset.card hTne with ⟨U, hU, hUmax⟩
  refine ⟨U, hU, hT U hU, ?_⟩
  intro w
  let patch : Finset α → α → Bool := fun A v => if v ∈ U then decide (v ∈ A) else w v
  by_contra hnone
  push Not at hnone
  have hzero : ∀ A ∈ U.powerset, (T.filter (fun f => ∀ v ∈ f, patch A v = true)).card % 2 = 0 := by
    intro A hA
    have hne := hnone A hA
    have hfalse : evalPoly T (patch A) = false := by
      cases hval : evalPoly T (patch A)
      · rfl
      · exact absurd hval hne
    unfold evalPoly par at hfalse
    rcases Nat.mod_two_eq_zero_or_one (T.filter (fun f => ∀ v ∈ f, patch A v = true)).card with h0 | h1
    · exact h0
    · simp [h1] at hfalse
  have hS0 : (∑ A ∈ U.powerset, (T.filter (fun f => ∀ v ∈ f, patch A v = true)).card) % 2 = 0 :=
    sum_mod_two_eq_zero U.powerset _ hzero
  have hswap : (∑ A ∈ U.powerset, (T.filter (fun f => ∀ v ∈ f, patch A v = true)).card) =
      ∑ f ∈ T, (U.powerset.filter (fun A => ∀ v ∈ f, patch A v = true)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap, ← Finset.add_sum_erase T _ hU] at hS0
  have hUterm : (U.powerset.filter (fun A => ∀ v ∈ U, patch A v = true)).card = 1 := by
    have hset : U.powerset.filter (fun A => ∀ v ∈ U, patch A v = true) = {U} := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hAU, hall⟩
        apply Finset.Subset.antisymm hAU
        intro v hv
        have h1 := hall v hv
        simp only [patch, hv, ite_true, decide_eq_true_eq] at h1
        exact h1
      · rintro rfl
        refine ⟨Finset.Subset.refl _, fun v hv => ?_⟩
        simp [patch, hv]
    rw [hset, Finset.card_singleton]
  have hrest : (∑ f ∈ T.erase U, (U.powerset.filter (fun A => ∀ v ∈ f, patch A v = true)).card) % 2 = 0 := by
    apply sum_mod_two_eq_zero
    intro f hf
    rcases Finset.mem_erase.mp hf with ⟨hfne, hfT⟩
    have hnsub : ¬ U ⊆ f := by
      intro hsub
      exact hfne (Finset.eq_of_subset_of_card_le hsub (hUmax f hfT)).symm
    rcases Finset.not_subset.mp hnsub with ⟨u0, hu0U, hu0f⟩
    set G := U.powerset.filter (fun A => ∀ v ∈ f, patch A v = true)
    have hpart := Finset.card_filter_add_card_filter_not (s := G) (fun A => u0 ∈ A)
    have hbij : (G.filter (fun A => u0 ∉ A)).card = (G.filter (fun A => u0 ∈ A)).card := by
      apply Finset.card_bij (fun A _ => insert u0 A)
      · intro A hA
        rcases Finset.mem_filter.mp hA with ⟨hAG, hu0nA⟩
        rcases Finset.mem_filter.mp hAG with ⟨hApow, hApatch⟩
        have hAU : A ⊆ U := Finset.mem_powerset.mp hApow
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, Finset.mem_insert_self u0 A⟩
        · exact Finset.insert_subset_iff.mpr ⟨hu0U, hAU⟩
        · intro v hvf
          have hvu0 : v ≠ u0 := fun heq => hu0f (heq ▸ hvf)
          have hp := hApatch v hvf
          simp only [patch] at hp ⊢
          by_cases hvU : v ∈ U
          · simp only [hvU, ite_true, Finset.mem_insert, hvu0, false_or] at hp ⊢
            exact hp
          · simp only [hvU, ite_false] at hp ⊢
            exact hp
      · intro A hA B hB hab
        have hAn : u0 ∉ A := (Finset.mem_filter.mp hA).2
        have hBn : u0 ∉ B := (Finset.mem_filter.mp hB).2
        have h1 := congrArg (fun X => X.erase u0) hab
        simpa [Finset.erase_insert hAn, Finset.erase_insert hBn] using h1
      · intro B hB
        rcases Finset.mem_filter.mp hB with ⟨hBG, hu0B⟩
        rcases Finset.mem_filter.mp hBG with ⟨hBpow, hBpatch⟩
        have hBU : B ⊆ U := Finset.mem_powerset.mp hBpow
        refine ⟨B.erase u0, ?_, Finset.insert_erase hu0B⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩, Finset.notMem_erase u0 B⟩
        · exact (Finset.erase_subset u0 B).trans hBU
        · intro v hvf
          have hvu0 : v ≠ u0 := fun heq => hu0f (heq ▸ hvf)
          have hp := hBpatch v hvf
          simp only [patch] at hp ⊢
          by_cases hvU : v ∈ U
          · simp only [hvU, ite_true, Finset.mem_erase, hvu0, ne_eq, not_false_eq_true, true_and] at hp ⊢
            exact hp
          · simp only [hvU, ite_false] at hp ⊢
            exact hp
    omega
  rw [hUterm] at hS0
  omega

theorem degPoly_forall_fin {α : Type} [DecidableEq α] {n : Nat}
    (cost : Nat → Nat) (g : Fin n → (α → Bool) → Bool)
    (hg : ∀ t : Fin n, degPoly (cost t.val) (g t)) :
    degPoly (∑ t : Fin n, cost t.val) (fun x => decide (∀ t : Fin n, g t x = true)) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    have hfun : (fun x : α → Bool => decide (∀ t : Fin 0, g t x = true)) = (fun _ => true) := by
      funext x
      simp
    rw [hfun]
    exact degPoly_const 0 true
  | succ n ih =>
    have hprev := ih (fun t => g t.castSucc) (fun t => hg t.castSucc)
    have hlast := hg (Fin.last n)
    have hmul := degPoly_mul hprev hlast
    rw [Fin.sum_univ_castSucc]
    rcases hmul with ⟨T, hT, he⟩
    refine ⟨T, hT, fun x => ?_⟩
    dsimp only
    rw [← he x]
    dsimp only
    by_cases h1 : ∀ t : Fin n, g t.castSucc x = true <;> by_cases h2 : g (Fin.last n) x = true
    · have hall : ∀ t : Fin (n + 1), g t x = true := fun t => Fin.lastCases h2 h1 t
      rw [decide_eq_true hall, decide_eq_true h1, h2]
      rfl
    · have hall : ¬ ∀ t : Fin (n + 1), g t x = true := fun h => h2 (h (Fin.last n))
      have h2f : g (Fin.last n) x = false := Bool.eq_false_iff.mpr h2
      rw [decide_eq_false hall, decide_eq_true h1, h2f]
      rfl
    · have hall : ¬ ∀ t : Fin (n + 1), g t x = true := fun h => h1 (fun t => h t.castSucc)
      rw [decide_eq_false hall, decide_eq_false h1, h2]
      rfl
    · have hall : ¬ ∀ t : Fin (n + 1), g t x = true := fun h => h2 (h (Fin.last n))
      have h2f : g (Fin.last n) x = false := Bool.eq_false_iff.mpr h2
      rw [decide_eq_false hall, decide_eq_false h1, h2f]
      rfl

theorem degPoly_comp_affine {k : Nat} {α : Type} [DecidableEq α] {u : Nat}
    (liftBit : (α → Bool) → Fin k → Bool)
    (hlift : ∀ j : Fin k, degPoly 1 (fun w => liftBit w j))
    (T : Finset (Finset (Fin k))) (hT : ∀ m ∈ T, m.card ≤ u) :
    degPoly u (fun w => evalPoly T (liftBit w)) := by
  induction T using Finset.induction_on with
  | empty =>
    have h := degPoly_const (α := α) u false
    rcases h with ⟨R, hR, he⟩
    exact ⟨R, hR, fun w => by dsimp only; rw [evalPoly_empty, ← he w]⟩
  | @insert m T hm ih =>
    have hm_le : m.card ≤ u := hT m (Finset.mem_insert_self m T)
    have hT' : ∀ s ∈ T, s.card ≤ u := fun s hs => hT s (Finset.mem_insert_of_mem hs)
    have h1 := ih hT'
    have hmon : degPoly m.card (fun w => monEval m (liftBit w)) := by
      clear hm hm_le hT hT' h1 ih T
      induction m using Finset.induction_on with
      | empty =>
        have h := degPoly_const (α := α) 0 true
        rcases h with ⟨R, hR, he⟩
        exact ⟨R, hR, fun w => by dsimp only; rw [← he w]; simp [monEval]⟩
      | @insert j m hjm ihm =>
        have hprod := degPoly_mul (hlift j) ihm
        rw [Finset.card_insert_of_notMem hjm, Nat.add_comm]
        rcases hprod with ⟨R, hR, he⟩
        refine ⟨R, hR, fun w => ?_⟩
        dsimp only
        rw [← he w]
        dsimp only
        unfold monEval
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_insert, forall_eq_or_imp]
    rcases degPoly_xor h1 (degPoly_mono hm_le hmon) with ⟨R, hR, he⟩
    exact ⟨R, hR, fun w => by dsimp only; rw [evalPoly_insert hm, ← he w]⟩

theorem deg_bit_xor_const {k : Nat} (idx : Fin k) (c : Bool) :
    ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ 1) ∧
      ∀ key : Fin (2 ^ k), xor (key.val.testBit idx.val) c =
        evalPoly terms (fun j : Fin k => key.val.testBit j.val) := by
  have h := degPoly_xor (degPoly_var idx) (degPoly_const 1 c)
  rcases h with ⟨terms, hterms, he⟩
  exact ⟨terms, hterms, fun key => he (fun j : Fin k => key.val.testBit j.val)⟩

theorem evalPoly_congr_filter {α : Type} (T : Finset (Finset α)) (x : α → Bool)
    (dp : DecidablePred (fun m : Finset α => ∀ j ∈ m, x j = true)) :
    ((@Finset.filter _ _ dp T).card % 2 == 1) = evalPoly T x :=
  congrArg (fun S : Finset (Finset α) => S.card % 2 == 1) (by ext m; simp only [Finset.mem_filter])

end PEqualNP.Outside.L_meta_25704_aux

open PEqualNP.Outside.L_meta_25704_aux in
theorem PEqualNP.Outside.L_meta_25704 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  Function.Injective (fun z : Fin m × Fin 12 => (starts z.1+z.2.val)%k) →
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
  (∀ i (j : Fin 9), ∃ z ∈ pin, z.val = (starts i+j.val)%k) →
  (∀ i (j : Fin 3), ∀ z ∈ pin, z.val ≠ (starts i+9+j.val)%k) →
  let K := Fin (2^k)
  let bitOf := fun (q : K) (i : Fin k) => q.val.testBit i.val
  let par := fun (n : Nat) => n % 2 == 1
  let fiber := (Finset.univ : Finset K).filter (fun keyWord =>
    ∀ z ∈ pin, bit row.val 0 keyWord.val z.val = bit row.val 0 ref.val z.val)
  let deg := fun (u : Nat) (f : K → Bool) =>
    ∃ terms : Finset (Finset (Fin k)), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ key, f key = par ((terms.filter (fun mon => ∀ j ∈ mon, bitOf key j = true)).card)
  let run := fun (steps : Nat) (ask : Nat → Nat → K → Bool) (x : K) =>
    (List.range steps).foldl (fun past levelId => past + ((ask levelId past x).toNat <<< levelId)) 0
  let out := fun (input : K) (i : Fin m) => bit row.val 2 input.val (starts i+5)
  let Symbol := Fin 3 → Bool
  let triple := fun (raw : K) (idx : Fin m) (v : Fin 3) =>
    bit row.val 0 raw.val (starts idx+9+v.val)
  let low := fun (f : Symbol → Bool) => ∃ monomials : Finset (Finset (Fin 3)),
    (∀ mon ∈ monomials, mon.card ≤ 2) ∧ ∀ symbol,
      f symbol = par ((monomials.filter (fun mon => ∀ coord ∈ mon, symbol coord = true)).card)
  ∀ (D s L : Nat),
    let possible := ∃ (n : Nat) (ask : Nat → Nat → K → Bool) (cost : Nat → Nat → Nat)
        (leaf : Nat → Fin L → Fin m → Symbol → Bool),
      (∀ path a i, low (leaf path a i)) ∧
      (∀ input ∈ fiber, ∀ u : Fin n, deg (cost u.val (run u.val ask input))
        (ask u.val (run u.val ask input))) ∧
      (∀ raw ∈ fiber, (∑ t : Fin n, cost t.val (run t.val ask raw)) ≤ D) ∧
      ∀ key ∈ fiber, ∃ a, ∀ i, leaf (run (n+s) ask key) a i (triple key i) = out key i
    possible ↔ ∃ bad : Fin (2^s*L) → Fin (m-D) → Symbol,
      ∀ w : Fin (m-D) → Symbol, ∃ a, ∀ i, w i ≠ bad a i) := by
  intro k hk constant
  dsimp only
  intro m starts hInj row ref hgood pin hpin_in hpin_disj D s L
  let K := Fin (2 ^ k)
  let fiber : Finset K := (Finset.univ : Finset K).filter (fun keyWord =>
    ∀ z ∈ pin, (stateAt k row constant 0 keyWord.val).testBit (z.val % k) =
      (stateAt k row constant 0 ref.val).testBit (z.val % k))
  have href_mem : ref ∈ fiber := Finset.mem_filter.mpr ⟨Finset.mem_univ ref, fun _ _ => rfl⟩
  by_cases hL0 : L = 0
  · subst hL0
    constructor
    · rintro ⟨_, _, _, _, _, _, _, hacc⟩
      rcases hacc ref href_mem with ⟨a, _⟩
      exact Fin.elim0 a
    · rintro ⟨bad, hbad⟩
      rcases hbad (fun _ _ => false) with ⟨a, _⟩
      have ha : a.val < 0 := by simpa using a.isLt
      omega
  have hL : 0 < L := by omega
  by_cases hm0 : m = 0
  · constructor
    · intro _
      refine ⟨fun _ i => False.elim (by have := i.isLt; omega), fun _ => ?_⟩
      exact ⟨⟨0, Nat.mul_pos (Nat.two_pow_pos s) hL⟩, fun i => False.elim (by have := i.isLt; omega)⟩
    · intro _
      refine ⟨0, fun _ _ _ => false, fun _ _ => 0, fun _ _ _ _ => false, ?_, ?_, ?_, ?_⟩
      · intro _ _ _
        exact ⟨∅, fun _ h => absurd h (Finset.notMem_empty _), fun _ => rfl⟩
      · intro _ _ u
        exact Fin.elim0 u
      · intro _ _
        simp
      · intro _ _
        exact ⟨⟨0, hL⟩, fun i => False.elim (by have := i.isLt; omega)⟩
  have hm : 0 < m := by omega
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
  let outFn : Fin m → (Fin 3 → Bool) → Bool := fun i =>
    let p := starts i
    let old := fun j : Nat => (stateAt k row constant 0 ref.val).testBit ((p + j) % k)
    let al := xor (xor (xor (old 5) (old 6)) (old 7))
      (xor ((rot k 0 ref.val).testBit ((p + 6) % k)) ((constant 1).val.testBit ((p + 6) % k)))
    let be := xor (xor (xor (old 6) (old 7)) (old 8))
      (xor ((rot k 0 ref.val).testBit ((p + 7) % k)) ((constant 1).val.testBit ((p + 7) % k)))
    let de := xor (xor (old 6) (row.val.testBit ((p + 9) % k))) ((constant 1).val.testBit ((p + 8) % k))
    let c2 := xor (xor (old 4) (row.val.testBit ((p + 4) % k))) ((constant 2).val.testBit ((p + 5) % k))
    round2Expr (old 6) (old 8) al be de c2
  let QFn : Fin m → (Fin 3 → Bool) → Bool := fun i sym =>
    xor (sym 0 && sym 1 && sym 2) (outFn i sym)
  have hQ_low : ∀ i : Fin m, degPoly 2 (QFn i) := fun i => low_round2Q _ _ _ _ _ _
  have hout_eq : ∀ key ∈ fiber, ∀ i : Fin m,
      (stateAt k row constant 2 key.val).testBit ((starts i + 5) % k) =
        outFn i (fun v : Fin 3 => (stateAt k row constant 0 key.val).testBit ((starts i + 9 + v.val) % k)) := by
    intro key hkey i
    have hkf := (Finset.mem_filter.mp hkey).2
    apply guarded_row_eval hk2 constant row ref key (starts i) _ (hgood i)
    intro j
    rcases hpin_in i j with ⟨z, hzpin, hzeq⟩
    have hzmod : z.val % k = (starts i + j.val) % k := by
      rw [Nat.mod_eq_of_lt z.isLt, hzeq]
    have hzk := hkf z hzpin
    rw [hzmod] at hzk
    exact hzk
  have hout_decomp : ∀ i sym, outFn i sym = xor (sym 0 && sym 1 && sym 2) (QFn i sym) := by
    intro i sym
    dsimp only [QFn]
    cases (sym 0 && sym 1 && sym 2) <;> cases outFn i sym <;> rfl
  classical
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
  let wantS0 : (Fin m × Fin 3 → Bool) → Fin k → Bool := fun w pos =>
    if h : ∃ iv : Fin m × Fin 3, (starts iv.1 + 9 + iv.2.val) % k = pos.val
    then w (Classical.choose h)
    else (stateAt k row constant 0 ref.val).testBit (pos.val % k)
  let keyBit : (Fin m × Fin 3 → Bool) → Fin k → Bool := fun w j =>
    xor (wantS0 w ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) (row.val.testBit ((j.val + 1) % k))
  let liftVal : (Fin m × Fin 3 → Bool) → Nat := fun w =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((if h : j < k then keyBit w ⟨j, h⟩ else false).toNat <<< j)) 0
  have hliftVal_bit : ∀ w j, (liftVal w).testBit j = if h : j < k then keyBit w ⟨j, h⟩ else false := by
    intro w j
    dsimp only [liftVal]
    rw [testBit_foldl_or]
    by_cases hj : j < k <;> simp [hj]
  have hliftVal_lt : ∀ w, liftVal w < 2 ^ k := by
    intro w
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [hliftVal_bit]
    have : ¬ j < k := by omega
    simp [this]
  let lift : (Fin m × Fin 3 → Bool) → K := fun w => ⟨liftVal w, hliftVal_lt w⟩
  have hlift_bit : ∀ w (j : Fin k), (lift w).val.testBit j.val = keyBit w j := by
    intro w j
    dsimp only [lift]
    rw [hliftVal_bit]
    simp [j.isLt]
  have hlift_s0 : ∀ w (q : Nat),
      (stateAt k row constant 0 (lift w).val).testBit (q % k) =
        wantS0 w ⟨q % k, Nat.mod_lt _ hk⟩ := by
    intro w q
    rw [stateAt_zero, Nat.testBit_xor, testBit_rot (lift w).isLt (Nat.mod_lt _ hk)]
    have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1m]
    let j : Fin k := ⟨(q % k + k - 1) % k, Nat.mod_lt _ hk⟩
    change xor ((lift w).val.testBit j.val) (row.val.testBit (q % k)) = _
    rw [hlift_bit]
    have hj1 : (j.val + 1) % k = q % k := by
      dsimp only [j]
      rw [Nat.mod_add_mod]
      have hqlt : q % k < k := Nat.mod_lt q hk
      have hsub : q % k + k - 1 + 1 = q % k + k := by omega
      rw [hsub, Nat.add_mod_right, Nat.mod_mod]
    dsimp only [keyBit]
    have hjfin : (⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨q % k, Nat.mod_lt _ hk⟩ :=
      Fin.ext hj1
    rw [hjfin, hj1]
    cases wantS0 w ⟨q % k, Nat.mod_lt _ hk⟩ <;> cases row.val.testBit (q % k) <;> rfl
  have hlift_fiber : ∀ w, lift w ∈ fiber := by
    intro w
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun z hzpin => ?_⟩
    rw [hlift_s0]
    have hno : ¬ ∃ iv : Fin m × Fin 3, (starts iv.1 + 9 + iv.2.val) % k = (⟨z.val % k, Nat.mod_lt _ hk⟩ : Fin k).val := by
      rintro ⟨⟨i, v⟩, heq⟩
      dsimp only at heq
      rw [Nat.mod_eq_of_lt z.isLt] at heq
      exact hpin_disj i v z hzpin heq.symm
    dsimp only [wantS0]
    rw [dif_neg hno]
    simp [Nat.mod_mod]
  have hlift_triple : ∀ w (i : Fin m) (v : Fin 3),
      (stateAt k row constant 0 (lift w).val).testBit ((starts i + 9 + v.val) % k) = w (i, v) := by
    intro w i v
    rw [hlift_s0]
    have hex : ∃ iv : Fin m × Fin 3,
        (starts iv.1 + 9 + iv.2.val) % k = (⟨(starts i + 9 + v.val) % k, Nat.mod_lt _ hk⟩ : Fin k).val :=
      ⟨(i, v), rfl⟩
    dsimp only [wantS0]
    rw [dif_pos hex]
    have hch : Classical.choose hex = (i, v) := hInj3 _ _ (Classical.choose_spec hex)
    rw [hch]
  have hlift_deg : ∀ j : Fin k, degPoly 1 (fun w : Fin m × Fin 3 → Bool => (lift w).val.testBit j.val) := by
    intro j
    have hfun : (fun w => (lift w).val.testBit j.val) = fun w => keyBit w j :=
      funext (fun w => hlift_bit w j)
    rw [hfun]
    dsimp only [keyBit, wantS0]
    by_cases h : ∃ iv : Fin m × Fin 3, (starts iv.1 + 9 + iv.2.val) % k = (⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val
    · simp only [dif_pos h]
      exact degPoly_xor (degPoly_var (Classical.choose h)) (degPoly_const 1 _)
    · simp only [dif_neg h]
      exact degPoly_const 1 _
  constructor
  · rintro ⟨n, ask, cost, leaf, hlow, hdeg, hcost, hacc⟩
    let w0 : Fin m × Fin 3 → Bool := fun _ => false
    let anchor : K := lift w0
    have hanchor : anchor ∈ fiber := hlift_fiber w0
    let path0 : Nat := runFn n ask anchor
    let gt : Fin n → (Fin m × Fin 3 → Bool) → Bool := fun t w =>
      !(xor (ask t.val (runFn t.val ask anchor) (lift w))
            (ask t.val (runFn t.val ask anchor) anchor))
    have hgt_deg : ∀ t : Fin n, degPoly (cost t.val (runFn t.val ask anchor)) (gt t) := by
      intro t
      rcases hdeg anchor hanchor t with ⟨terms, hterms, he⟩
      have hcomp : degPoly (cost t.val (runFn t.val ask anchor))
          (fun w => ask t.val (runFn t.val ask anchor) (lift w)) := by
        have h1 := degPoly_comp_affine (fun w j => (lift w).val.testBit j.val) hlift_deg terms hterms
        rcases h1 with ⟨R, hR, hRe⟩
        exact ⟨R, hR, fun w =>
          ((he (lift w)).trans (evalPoly_congr_filter terms (fun j : Fin k => (lift w).val.testBit j.val) _)).trans (hRe w)⟩
      exact degPoly_not (degPoly_xor hcomp (degPoly_const _ _))
    have hG_deg := degPoly_forall_fin (fun t => cost t (runFn t ask anchor)) gt hgt_deg
    have hG_degD : degPoly D (fun w => decide (∀ t : Fin n, gt t w = true)) :=
      degPoly_mono (hcost anchor hanchor) hG_deg
    rcases hG_degD with ⟨T, hTD, hTe⟩
    have hTw0 : evalPoly T w0 = true := by
      rw [← hTe w0]
      dsimp only
      simp only [decide_eq_true_eq]
      intro t
      dsimp only [gt, anchor]
      cases ask t.val (runFn t.val ask (lift w0)) (lift w0) <;> rfl
    rcases exists_patch_evalPoly_true T D hTD w0 hTw0 with ⟨U, _, hUD, hpatch⟩
    let gone : Finset (Fin m) := U.image Prod.fst
    have hgone_le : gone.card ≤ D := (Finset.card_image_le).trans hUD
    let rem : Finset (Fin m) := Finset.univ \ gone
    have hrem_ge : m - D ≤ rem.card := by
      have h1 : (Finset.univ : Finset (Fin m)).card - gone.card ≤ rem.card :=
        Finset.le_card_sdiff gone Finset.univ
      rw [Finset.card_univ, Fintype.card_fin] at h1
      omega
    let eRem : rem ≃ Fin rem.card := Fintype.equivFinOfCardEq (Fintype.card_coe rem)
    let emb : Fin (m - D) → Fin m := fun j => (eRem.symm ⟨j.val, lt_of_lt_of_le j.isLt hrem_ge⟩).val
    have hemb_inj : Function.Injective emb := by
      intro j1 j2 heq
      have hsub : eRem.symm ⟨j1.val, lt_of_lt_of_le j1.isLt hrem_ge⟩ =
          eRem.symm ⟨j2.val, lt_of_lt_of_le j2.isLt hrem_ge⟩ := Subtype.ext heq
      have hfin := eRem.symm.injective hsub
      exact Fin.ext (congrArg (fun x : Fin rem.card => x.val) hfin)
    have hemb_not_gone : ∀ j : Fin (m - D), emb j ∉ gone := by
      intro j
      have hmem := (eRem.symm ⟨j.val, lt_of_lt_of_le j.isLt hrem_ge⟩).property
      exact (Finset.mem_sdiff.mp hmem).2
    have hbad_ex : ∀ (idx : Fin (2 ^ s * L)) (j : Fin (m - D)),
        ∃ sym : Fin 3 → Bool,
          leaf (path0 + (idx.val / L) * 2 ^ n) ⟨idx.val % L, Nat.mod_lt _ hL⟩ (emb j) sym ≠
            outFn (emb j) sym := by
      intro idx j
      rcases hlow (path0 + (idx.val / L) * 2 ^ n) ⟨idx.val % L, Nat.mod_lt _ hL⟩ (emb j) with ⟨M, hM, hMe⟩
      have hLlow : degPoly 2 (leaf (path0 + (idx.val / L) * 2 ^ n) ⟨idx.val % L, Nat.mod_lt _ hL⟩ (emb j)) :=
        ⟨M, hM, fun sym => (hMe sym).trans (evalPoly_congr_filter M sym _)⟩
      rcases exists_ne_cubic_xor (hQ_low (emb j)) hLlow with ⟨sym, hne⟩
      exact ⟨sym, by rw [hout_decomp]; exact hne⟩
    let bad : Fin (2 ^ s * L) → Fin (m - D) → (Fin 3 → Bool) :=
      fun idx j => Classical.choose (hbad_ex idx j)
    refine ⟨bad, ?_⟩
    intro w_sub
    let w : Fin m × Fin 3 → Bool := fun p =>
      if h : ∃ j : Fin (m - D), emb j = p.1
      then w_sub (Classical.choose h) p.2
      else false
    have hw_emb : ∀ (j : Fin (m - D)) (v : Fin 3), w (emb j, v) = w_sub j v := by
      intro j v
      have hex : ∃ j' : Fin (m - D), emb j' = emb j := ⟨j, rfl⟩
      dsimp only [w]
      rw [dif_pos hex]
      have hch : Classical.choose hex = j := hemb_inj (Classical.choose_spec hex)
      rw [hch]
    rcases hpatch w with ⟨A, _, hTA⟩
    let w' : Fin m × Fin 3 → Bool := fun v => if v ∈ U then decide (v ∈ A) else w v
    let key : K := lift w'
    have hkey_fib : key ∈ fiber := hlift_fiber w'
    have hkey_run : runFn n ask key = path0 := by
      have hall : ∀ t : Fin n, gt t w' = true := by
        have h1 := (hTe w').trans hTA
        exact of_decide_eq_true h1
      have hprefix : ∀ r, r ≤ n → runFn r ask key = runFn r ask anchor := by
        intro r
        induction r with
        | zero => intro _; rfl
        | succ r ihr =>
          intro hr
          have hprev := ihr (by omega)
          rw [runFn_succ, runFn_succ, hprev]
          have hgt := hall ⟨r, by omega⟩
          dsimp only [gt] at hgt
          have heq_ask : ask r (runFn r ask anchor) key = ask r (runFn r ask anchor) anchor := by
            have hbool : ∀ a b : Bool, !(xor a b) = true → a = b := by decide
            exact hbool _ _ hgt
          rw [heq_ask]
      exact hprefix n (le_refl n)
    rcases runFn_add_exists n s ask key with ⟨q, hq, hrun_ns⟩
    rw [hkey_run] at hrun_ns
    rcases hacc key hkey_fib with ⟨a, ha⟩
    have hidx_lt : q * L + a.val < 2 ^ s * L := by
      have h1 : q * L + a.val < q * L + L := Nat.add_lt_add_left a.isLt (q * L)
      have h2 : q * L + L = (q + 1) * L := by ring
      have h3 : (q + 1) * L ≤ 2 ^ s * L := Nat.mul_le_mul_right L (by omega)
      omega
    let idx : Fin (2 ^ s * L) := ⟨q * L + a.val, hidx_lt⟩
    refine ⟨idx, ?_⟩
    intro j hcontra
    have hdiv : idx.val / L = q := by
      dsimp only [idx]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hL, Nat.div_eq_of_lt a.isLt, Nat.zero_add]
    have hmod : (⟨idx.val % L, Nat.mod_lt _ hL⟩ : Fin L) = a := by
      apply Fin.ext
      dsimp only [idx]
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt a.isLt]
    have htr : (fun v : Fin 3 => (stateAt k row constant 0 key.val).testBit ((starts (emb j) + 9 + v.val) % k)) = w_sub j := by
      funext v
      rw [hlift_triple]
      have hnotU : (emb j, v) ∉ U := by
        intro hmem
        exact hemb_not_gone j (Finset.mem_image.mpr ⟨(emb j, v), hmem, rfl⟩)
      dsimp only [w']
      rw [if_neg hnotU]
      exact hw_emb j v
    have hmatch := ha (emb j)
    have hrun_eq : (List.range (n + s)).foldl (fun past levelId => past + ((ask levelId past key).toNat <<< levelId)) 0 =
        path0 + q * 2 ^ n := hrun_ns
    rw [hrun_eq] at hmatch
    have hout_j := hout_eq key hkey_fib (emb j)
    change leaf (path0 + q * 2 ^ n) a (emb j)
        (fun v : Fin 3 => (stateAt k row constant 0 key.val).testBit ((starts (emb j) + 9 + v.val) % k)) =
      (stateAt k row constant 2 key.val).testBit ((starts (emb j) + 5) % k) at hmatch
    rw [hout_j, htr, hcontra] at hmatch
    set b0 := bad idx j
    have hne : leaf (path0 + (idx.val / L) * 2 ^ n) ⟨idx.val % L, Nat.mod_lt _ hL⟩ (emb j) b0 ≠
        outFn (emb j) b0 := Classical.choose_spec (hbad_ex idx j)
    rw [hdiv, hmod] at hne
    exact hne hmatch
  · rintro ⟨bad, hbad⟩
    let n : Nat := min D m
    let w_res : K → Fin (m - D) → (Fin 3 → Bool) := fun key j v =>
      (stateAt k row constant 0 key.val).testBit ((starts ⟨n + j.val, by have := j.isLt; omega⟩ + 9 + v.val) % k)
    let idx_key : K → Fin (2 ^ s * L) := fun key => Classical.choose (hbad (w_res key))
    have hidx_spec : ∀ key j, w_res key j ≠ bad (idx_key key) j :=
      fun key => Classical.choose_spec (hbad (w_res key))
    let grp : K → Nat := fun key => (idx_key key).val / L
    have hgrp_lt : ∀ key, grp key < 2 ^ s := fun key =>
      Nat.div_lt_of_lt_mul ((idx_key key).isLt.trans_eq (Nat.mul_comm (2 ^ s) L))
    let slt : K → Fin L := fun key => ⟨(idx_key key).val % L, Nat.mod_lt _ hL⟩
    let ask : Nat → Nat → K → Bool := fun u _ key =>
      if hu : u < n
      then (stateAt k row constant 0 key.val).testBit ((starts ⟨u, by omega⟩ + 9) % k)
      else (grp key).testBit (u - n)
    let cost : Nat → Nat → Nat := fun _ _ => 1
    let leaf : Nat → Fin L → Fin m → (Fin 3 → Bool) → Bool := fun path a i sym =>
      if hi : i.val < n
      then xor (if path.testBit i.val then (sym 1 && sym 2) else false) (QFn i sym)
      else
        let j : Fin (m - D) := ⟨i.val - D, by have := i.isLt; omega⟩
        let g := (path / 2 ^ n) % 2 ^ s
        have hg : g < 2 ^ s := Nat.mod_lt _ (Nat.two_pow_pos s)
        have hidx : g * L + a.val < 2 ^ s * L := by
          have h1 : g * L + a.val < g * L + L := Nat.add_lt_add_left a.isLt (g * L)
          have h2 : g * L + L = (g + 1) * L := by ring
          have h3 : (g + 1) * L ≤ 2 ^ s * L := Nat.mul_le_mul_right L (by omega)
          omega
        xor (xor (sym 0 && sym 1 && sym 2) (QFn i sym)) (decide (sym = bad ⟨g * L + a.val, hidx⟩ j))
    refine ⟨n, ask, cost, leaf, ?_, ?_, ?_, ?_⟩
    · intro path a i
      have hlow2 : degPoly 2 (leaf path a i) := by
        by_cases hi : i.val < n
        · simp only [leaf, hi, dite_true]
          exact low_known_bit0 (hQ_low i) (path.testBit i.val)
        · simp only [leaf, hi, dite_false]
          exact low_point_flip (hQ_low i) _
      rcases hlow2 with ⟨M, hM, hMe⟩
      exact ⟨M, hM, fun sym => (hMe sym).trans (evalPoly_congr_filter M sym _).symm⟩
    · intro input _ u
      let p0 : Nat := (starts ⟨u.val, by have := u.isLt; omega⟩ + 9) % k
      have hp0 : p0 < k := Nat.mod_lt _ hk
      let idx0 : Fin k := ⟨(p0 + k - 1) % k, Nat.mod_lt _ hk⟩
      rcases deg_bit_xor_const idx0 (row.val.testBit p0) with ⟨terms, hterms, he⟩
      refine ⟨terms, hterms, fun key => ?_⟩
      dsimp only [ask]
      rw [dif_pos u.isLt, stateAt_zero, Nat.testBit_xor, testBit_rot key.isLt hp0]
      have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m]
      exact (he key).trans (evalPoly_congr_filter terms (fun j : Fin k => key.val.testBit j.val) _).symm
    · intro _ _
      simp only [cost, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
      exact Nat.min_le_left D m
    · intro key hkey
      refine ⟨slt key, fun i => ?_⟩
      change leaf (runFn (n + s) ask key) (slt key) i
          (fun v : Fin 3 => (stateAt k row constant 0 key.val).testBit ((starts i + 9 + v.val) % k)) =
        (stateAt k row constant 2 key.val).testBit ((starts i + 5) % k)
      rw [hout_eq key hkey i, hout_decomp]
      dsimp only [leaf]
      by_cases hi : i.val < n
      · rw [dif_pos hi]
        have htb := runFn_testBit (by omega : i.val < n + s) ask key
        dsimp only [ask] at htb
        rw [dif_pos hi] at htb
        have hi_eq : (⟨i.val, by have := i.isLt; omega⟩ : Fin m) = i := Fin.ext rfl
        rw [hi_eq] at htb
        rw [htb]
        simp only [Fin.val_zero, Nat.add_zero]
        cases (stateAt k row constant 0 key.val).testBit ((starts i + 9) % k) <;> rfl
      · rw [dif_neg hi]
        have hdiv : (runFn (n + s) ask key / 2 ^ n) % 2 ^ s = grp key := by
          apply runFn_div_pow_mod n s (grp key) (hgrp_lt key) ask key
          intro r hr
          dsimp only [ask]
          have hnot : ¬ n + r < n := by omega
          rw [dif_neg hnot, Nat.add_sub_cancel_left]
        have hidx_eq : ∀ hproof, (⟨((runFn (n + s) ask key / 2 ^ n) % 2 ^ s) * L + (slt key).val,
            hproof⟩ : Fin (2 ^ s * L)) = idx_key key := by
          intro hproof
          apply Fin.ext
          dsimp only
          rw [hdiv]
          dsimp only [slt, grp]
          rw [Nat.mul_comm]
          exact Nat.div_add_mod (idx_key key).val L
        have hj_eq : (⟨n + (⟨i.val - D, by have := i.isLt; omega⟩ : Fin (m - D)).val, by have := i.isLt; omega⟩ : Fin m) = i := by
          apply Fin.ext
          dsimp only
          omega
        have hne : (fun v : Fin 3 => (stateAt k row constant 0 key.val).testBit ((starts i + 9 + v.val) % k)) ≠
            bad (idx_key key) ⟨i.val - D, by have := i.isLt; omega⟩ := by
          have h := hidx_spec key ⟨i.val - D, by have := i.isLt; omega⟩
          dsimp only [w_res] at h
          rw [hj_eq] at h
          exact h
        rw [hidx_eq]
        rw [decide_eq_false hne, Bool.xor_false]
