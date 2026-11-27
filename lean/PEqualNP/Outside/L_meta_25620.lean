import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25620_aux

private def rotFn (k s word : ℕ) : ℕ :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

private def stepFn (k word : ℕ) : ℕ :=
  (List.range k).foldl (fun acc cell =>
    acc ||| ((xor (word.testBit cell)
      (!(word.testBit ((cell + 1) % k)) && word.testBit ((cell + 2) % k))).toNat <<< cell)) 0

private def stateFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row rounds key : ℕ) : ℕ :=
  (List.range rounds).foldl (fun prev tick =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * tick) key ^^^
      (constant (tick + 1)).val) (rotFn k 1 key ^^^ row)

private def injectedFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (round key pos : ℕ) : Bool :=
  xor ((rotFn k (2 * (round - 1)) key).testBit (pos % k))
    ((constant round).val.testBit (pos % k))

private def bitFn (k : ℕ) (constant : ℕ → Fin (2 ^ k)) (row round key pos : ℕ) : Bool :=
  (stateFn k constant row round key).testBit (pos % k)

private lemma rotFn_lt {k : ℕ} (s word : ℕ) : rotFn k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma rotFn_testBit {k s word i : ℕ} (hk : 0 < k) (hw : word < 2 ^ k) (hi : i < k) :
    (rotFn k s word).testBit i = word.testBit ((i + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsm : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have hhi : word.testBit (k - s % k + i) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have h1 : i + k - s % k = (i - s % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hhi, Bool.or_false, decide_eq_true hle, Bool.true_and, hmod]
  · have hlt : i < s % k := by omega
    have hdec : decide (s % k ≤ i) = false := decide_eq_false (by omega)
    have hmod : (i + k - s % k) % k = i + (k - s % k) := by
      have h1 : i + k - s % k = i + (k - s % k) := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [hdec, Bool.false_and, Bool.false_or, hmod, Nat.add_comm (k - s % k) i]

private lemma foldl_or_bits (f : ℕ → Bool) :
    ∀ (n i : ℕ),
      ((List.range n).foldl (fun acc cell => acc ||| ((f cell).toNat <<< cell)) 0).testBit i =
        if i < n then f i else false
  | 0, i => by simp
  | n + 1, i => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [Nat.testBit_or, foldl_or_bits f n i, Nat.testBit_shiftLeft]
      by_cases hi : i < n
      · have hne : decide (n ≤ i) = false := decide_eq_false (by omega)
        have hi' : i < n + 1 := by omega
        simp [hi, hi', hne]
      · by_cases heq : i = n
        · subst heq
          have hge : decide (i ≤ i) = true := decide_eq_true (le_refl _)
          have hsub : i - i = 0 := Nat.sub_self i
          have hlt : i < i + 1 := by omega
          have hnlt : ¬ i < i := by omega
          simp only [hnlt, ↓reduceIte, Bool.false_or, hge, Bool.true_and, hsub, hlt]
          cases f i <;> rfl
        · have hgt : n < i := by omega
          have hsub : 1 ≤ i - n := by omega
          have hbit : (f n).toNat.testBit (i - n) = false := by
            have hlt2 : (f n).toNat < 2 ^ (i - n) := by
              have h2 : 2 ≤ 2 ^ (i - n) := by
                have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hsub
                simpa using this
              cases f n
              · simp
              · simp; omega
            exact Nat.testBit_lt_two_pow hlt2
          have hn1 : ¬ i < n + 1 := by omega
          simp [hi, hn1, hbit]

private lemma stepFn_testBit {k word i : ℕ} (hi : i < k) :
    (stepFn k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  unfold stepFn
  rw [foldl_or_bits]
  simp [hi]

private lemma stepFn_lt {k word : ℕ} : stepFn k word < 2 ^ k := by
  have hzero : ∀ i ≥ k, (stepFn k word).testBit i = false := by
    intro i hi
    unfold stepFn
    rw [foldl_or_bits]
    have : ¬ i < k := by omega
    simp [this]
  have hmod : stepFn k word % 2 ^ k = stepFn k word := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < k
    · simp [hi]
    · simp [hi, hzero i (by omega)]
  rw [← hmod]
  exact Nat.mod_lt _ (Nat.two_pow_pos k)

private lemma stateFn_lt {k : ℕ} (constant : ℕ → Fin (2 ^ k)) {row key : ℕ}
    (hrow : row < 2 ^ k) (_hkey : key < 2 ^ k) :
    ∀ rounds : ℕ, stateFn k constant row rounds key < 2 ^ k
  | 0 => by
      unfold stateFn
      simp only [List.range_zero, List.foldl_nil]
      exact Nat.xor_lt_two_pow (rotFn_lt 1 key) hrow
  | rounds + 1 => by
      unfold stateFn at *
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow stepFn_lt (rotFn_lt _ key)) (constant _).isLt

private lemma mod_sub_one {k n : ℕ} (hk : 1 ≤ k) :
    (n % k + k - 1 % k) % k = (n + k - 1) % k := by
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hlt : n % k < k := Nat.mod_lt n (by omega)
    have hrew : n % k + k - 1 = n % k + (k - 1) := by omega
    have hrew2 : n + k - 1 = n + (k - 1) := by omega
    rw [hrew, hrew2, Nat.mod_add_mod]

private lemma mod_sub_two {k n : ℕ} (hk : 2 < k) :
    (n % k + k - 2 % k) % k = (n + k - 2) % k := by
  have h2 : 2 % k = 2 := Nat.mod_eq_of_lt hk
  rw [h2]
  have hrew : n % k + k - 2 = n % k + (k - 2) := by omega
  have hrew2 : n + k - 2 = n + (k - 2) := by omega
  rw [hrew, hrew2, Nat.mod_add_mod]

private lemma mod_add_one {k n : ℕ} (hk : 2 ≤ k) :
    (n % k + k - (k - 1) % k) % k = (n + 1) % k := by
  have hkm1 : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hkm1]
  have hrew : n % k + k - (k - 1) = n % k + 1 := by omega
  rw [hrew, Nat.mod_add_mod]

private lemma bitFn_zero {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    bitFn k constant row 0 key pos =
      xor (key.testBit ((pos + k - 1) % k)) (row.testBit (pos % k)) := by
  unfold bitFn stateFn
  simp only [List.range_zero, List.foldl_nil, Nat.testBit_xor]
  rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega)), mod_sub_one (by omega)]

private lemma key_testBit_from_bit0 {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    key.testBit (pos % k) =
      xor (bitFn k constant row 0 key (pos + 1)) (row.testBit ((pos + 1) % k)) := by
  have h0 := bitFn_zero hk constant (row := row) hkey (pos + 1)
  have hmod : (pos + 1 + k - 1) % k = pos % k := by
    have : pos + 1 + k - 1 = pos + k := by omega
    rw [this, Nat.add_mod_right]
  rw [hmod] at h0
  rw [h0]
  cases key.testBit (pos % k) <;> cases row.testBit ((pos + 1) % k) <;> rfl

private lemma injectedFn_one {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) :
    injectedFn k constant 1 key pos =
      xor (xor (bitFn k constant row 0 key (pos + 1)) (row.testBit ((pos + 1) % k)))
          ((constant 1).val.testBit (pos % k)) := by
  unfold injectedFn
  have hrot0 : (rotFn k (2 * (1 - 1)) key).testBit (pos % k) = key.testBit (pos % k) := by
    rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega))]
    have h0 : 2 * (1 - 1) % k = 0 := by simp
    rw [h0, Nat.sub_zero, Nat.add_mod_right, Nat.mod_mod]
  rw [hrot0, key_testBit_from_bit0 hk constant hkey pos]

private lemma injectedFn_two {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hkey : key < 2 ^ k) (pos : ℕ) (hpos : 1 ≤ pos) :
    injectedFn k constant 2 key pos =
      xor (xor (bitFn k constant row 0 key (pos - 1)) (row.testBit ((pos - 1) % k)))
          ((constant 2).val.testBit (pos % k)) := by
  unfold injectedFn
  have hrot2 : (rotFn k (2 * (2 - 1)) key).testBit (pos % k) =
      key.testBit ((pos + k - 2) % k) := by
    rw [rotFn_testBit (by omega) hkey (Nat.mod_lt pos (by omega))]
    have h2 : 2 * (2 - 1) = 2 := by omega
    rw [h2, mod_sub_two (by omega)]
  have h0 := bitFn_zero hk constant (row := row) hkey (pos - 1)
  have hmod2 : (pos - 1 + k - 1) % k = (pos + k - 2) % k := by congr 1; omega
  rw [hmod2] at h0
  rw [hrot2]
  have hkey_eq : key.testBit ((pos + k - 2) % k) =
      xor (bitFn k constant row 0 key (pos - 1)) (row.testBit ((pos - 1) % k)) := by
    rw [h0]
    cases key.testBit ((pos + k - 2) % k) <;> cases row.testBit ((pos - 1) % k) <;> rfl
  rw [hkey_eq]

private lemma mix_testBit {k word pos : ℕ} (hk : 12 ≤ k) (hw : word < 2 ^ k) (hpos : 1 ≤ pos) :
    (word ^^^ rotFn k 1 word ^^^ rotFn k (k - 1) word).testBit (pos % k) =
      xor (xor (word.testBit ((pos - 1) % k)) (word.testBit (pos % k)))
          (word.testBit ((pos + 1) % k)) := by
  simp only [Nat.testBit_xor]
  rw [rotFn_testBit (by omega) hw (Nat.mod_lt pos (by omega)), mod_sub_one (by omega)]
  rw [rotFn_testBit (by omega) hw (Nat.mod_lt pos (by omega)), mod_add_one (by omega)]
  have hsub : (pos + k - 1) % k = (pos - 1) % k := by
    have : pos + k - 1 = (pos - 1) + k := by omega
    rw [this, Nat.add_mod_right]
  rw [hsub]
  cases word.testBit ((pos - 1) % k) <;> cases word.testBit (pos % k) <;>
    cases word.testBit ((pos + 1) % k) <;> rfl

private lemma bitFn_succ {k : ℕ} (hk : 12 ≤ k) (constant : ℕ → Fin (2 ^ k))
    {row key : ℕ} (hrow : row < 2 ^ k) (hkey : key < 2 ^ k) (r pos : ℕ) (hpos : 1 ≤ pos) :
    let m := fun h =>
      xor (xor (bitFn k constant row r key (h - 1)) (bitFn k constant row r key h))
          (bitFn k constant row r key (h + 1))
    bitFn k constant row (r + 1) key pos =
      xor (xor (m pos) (!(m (pos + 1)) && m (pos + 2)))
          (injectedFn k constant (r + 1) key pos) := by
  intro m
  set prev := stateFn k constant row r key
  have hprev_lt : prev < 2 ^ k := stateFn_lt constant hrow hkey r
  set mixed := prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev
  have hstate : stateFn k constant row (r + 1) key =
      stepFn k mixed ^^^ rotFn k (2 * r) key ^^^ (constant (r + 1)).val := by
    unfold stateFn
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  unfold bitFn
  rw [hstate]
  simp only [Nat.testBit_xor]
  rw [stepFn_testBit (Nat.mod_lt pos (by omega))]
  have hm0 : mixed.testBit (pos % k) = m pos := by
    simpa [m, bitFn, prev, mixed] using mix_testBit hk hprev_lt hpos
  have hm1 : mixed.testBit ((pos % k + 1) % k) = m (pos + 1) := by
    rw [Nat.mod_add_mod]
    simpa [m, bitFn, prev, mixed] using mix_testBit hk hprev_lt (by omega : 1 ≤ pos + 1)
  have hm2 : mixed.testBit ((pos % k + 2) % k) = m (pos + 2) := by
    rw [Nat.mod_add_mod]
    simpa [m, bitFn, prev, mixed] using mix_testBit hk hprev_lt (by omega : 1 ≤ pos + 2)
  rw [hm0, hm1, hm2]
  unfold injectedFn
  simp only [Nat.add_sub_cancel]
  cases m pos <;> cases m (pos + 1) <;> cases m (pos + 2) <;>
    cases (rotFn k (2 * r) key).testBit (pos % k) <;>
    cases (constant (r + 1)).val.testBit (pos % k) <;> rfl

private lemma card_bits_fixed {k : ℕ} (S : Finset (Fin k)) (t : Fin k → Bool) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun y =>
      ∀ i ∈ S, y.val.testBit i.val = t i)).card = 2 ^ (k - S.card) := by
  let toBits : Fin (2 ^ k) → (Fin k → Bool) := fun y i => y.val.testBit i.val
  let fromBits : (Fin k → Bool) → Fin (2 ^ k) := fun f =>
    ⟨Finset.univ.sum (fun i : Fin k => if f i then 2 ^ i.val else 0), by
      have hlt : ∀ (n : ℕ) (g : Fin n → Bool),
          (∑ i : Fin n, if g i then 2 ^ i.val else 0) < 2 ^ n := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro g
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.val_castSucc, Fin.val_last]
          have h1 := ih (fun i => g i.castSucc)
          have h2 : (if g (Fin.last n) then 2 ^ n else 0) ≤ 2 ^ n := by
            split_ifs <;> simp
          have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
          omega
      exact hlt k f⟩
  have htb_fb : ∀ (n : ℕ) (g : Fin n → Bool) (i : Fin n),
      (∑ j : Fin n, if g j then 2 ^ j.val else 0).testBit i.val = g i := by
    intro n
    induction n with
    | zero => intro _ i; exact Fin.elim0 i
    | succ n ih =>
      intro g i
      rw [Fin.sum_univ_castSucc]
      have hlt : (∑ j : Fin n, if g j.castSucc then 2 ^ j.castSucc.val else 0) < 2 ^ n := by
        have hlt0 : ∀ (m : ℕ) (h : Fin m → Bool),
            (∑ j : Fin m, if h j then 2 ^ j.val else 0) < 2 ^ m := by
          intro m
          induction m with
          | zero => intro _; simp
          | succ m ihm =>
            intro h
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            have h1 := ihm (fun j => h j.castSucc)
            have h2 : (if h (Fin.last m) then 2 ^ m else 0) ≤ 2 ^ m := by
              split_ifs <;> simp
            have hpow : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
            omega
        simpa [Fin.val_castSucc] using hlt0 n (fun j => g j.castSucc)
      set A := ∑ j : Fin n, if g j.castSucc then 2 ^ j.castSucc.val else 0
      have hval : A + (if g (Fin.last n) then 2 ^ n else 0) =
          A + 2 ^ n * (if g (Fin.last n) then 1 else 0) := by split_ifs <;> simp
      rw [Fin.val_last, hval]
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.val_last]
        rw [Nat.testBit_eq_decide_div_mod_eq, Nat.add_mul_div_left _ _ (Nat.two_pow_pos n),
            Nat.div_eq_of_lt hlt, zero_add]
        cases g (Fin.last n) <;> simp
      · intro j
        simp only [Fin.val_castSucc]
        rw [Nat.testBit_eq_decide_div_mod_eq]
        have hpow : 2 ^ n = 2 ^ j.val * 2 ^ (n - j.val) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le (le_of_lt j.isLt)]
        rw [hpow, mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos j.val)]
        have heven : 2 ∣ 2 ^ (n - j.val) * (if g (Fin.last n) then 1 else 0) :=
          dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (by omega : 1 ≤ n - j.val)) _
        rcases heven with ⟨q, hq⟩
        rw [hq, Nat.add_mul_mod_self_left, ← Nat.testBit_eq_decide_div_mod_eq]
        exact ih (fun r => g r.castSucc) j
  have hbij : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun y =>
      ∀ i ∈ S, y.val.testBit i.val = t i)).card =
      (Finset.univ : Finset ({i : Fin k // i ∉ S} → Bool)).card := by
    refine Finset.card_bij (fun y _ i => y.val.testBit i.val.val) ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro y₁ hy₁ y₂ hy₂ heq
      have h1 := (Finset.mem_filter.mp hy₁).2
      have h2 := (Finset.mem_filter.mp hy₂).2
      ext
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < k
      · by_cases hS : (⟨i, hi⟩ : Fin k) ∈ S
        · rw [h1 ⟨i, hi⟩ hS, h2 ⟨i, hi⟩ hS]
        · exact congrFun heq ⟨⟨i, hi⟩, hS⟩
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le y₁.isLt (Nat.pow_le_pow_right (by omega) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le y₂.isLt (Nat.pow_le_pow_right (by omega) (by omega)))]
    · intro f _
      let g : Fin k → Bool := fun i => if h : i ∈ S then t i else f ⟨i, h⟩
      refine ⟨fromBits g, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        have htb := htb_fb k g i
        simpa [fromBits, g, hi] using htb
      · funext ⟨i, hi⟩
        have htb := htb_fb k g i
        simpa [fromBits, g, hi] using htb
  rw [hbij, Finset.card_univ, Fintype.card_pi]
  simp only [Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

private lemma hidden_bool_part1 (f1 f2 α β δ j2 j3 j4 : Bool) (a b c : Bool) :
    let m : ℕ → Bool := fun j =>
      if j = 1 then f1
      else if j = 2 then f2
      else if j = 3 then α
      else if j = 4 then β
      else if j = 5 then xor β (!α)
      else if j = 6 then xor α a
      else if j = 7 then xor β ((!a) && b)
      else if j = 8 then xor δ ((a == b) && c)
      else false
    let mix : ℕ → Bool := fun h => xor (xor (m (h - 1)) (m h)) (m (h + 1))
    let nb : ℕ → Bool → Bool := fun j inj => xor (xor (mix j) (!(mix (j + 1)) && mix (j + 2))) inj
    nb 2 j2 = xor (xor (xor (xor f1 f2) α) (!(xor (xor f2 α) β) && true)) j2 ∧
    nb 3 j3 = xor (xor (xor f2 α) β) j3 ∧
    nb 4 j4 = xor true j4 := by
  cases f1 <;> cases f2 <;> cases α <;> cases β <;> cases δ <;>
    cases j2 <;> cases j3 <;> cases j4 <;> cases a <;> cases b <;> cases c <;> decide

private lemma hidden_bool_count5 (α β δ : Bool) :
    let m : Fin 8 → ℕ → Bool := fun s j =>
      let a := s.val.testBit 0
      let b := s.val.testBit 1
      let c := s.val.testBit 2
      if j = 4 then β
      else if j = 5 then xor β (!α)
      else if j = 6 then xor α a
      else if j = 7 then xor β ((!a) && b)
      else if j = 8 then xor δ ((a == b) && c)
      else false
    let mix : Fin 8 → ℕ → Bool := fun s h => xor (xor (m s (h - 1)) (m s h)) (m s (h + 1))
    ((Finset.univ : Finset (Fin 8)).filter (fun s =>
      xor (mix s 5) (!(mix s 6) && mix s 7) = true)).card = 5 := by
  cases α <;> cases β <;> cases δ <;> decide

private lemma prove_25620 (k : ℕ) (hk0 : 0 < k) (constant : ℕ → Fin (2 ^ k))
    (hk : 12 ≤ k) (row ref : Fin (2 ^ k)) (p : ℕ) :
    let old := fun (j : ℕ) => bitFn k constant row.val 0 ref.val (p + j)
    let first := fun (j : ℕ) => bitFn k constant row.val 1 ref.val (p + j)
    let j₁ := fun (j : ℕ) => injectedFn k constant 1 ref.val (p + j)
    let j₂ := fun (j : ℕ) => injectedFn k constant 2 ref.val (p + j)
    let pair := xor (old 7) (old 8)
    let τ := xor (old 6) pair
    let α := xor (xor (xor (old 5) (old 6)) (old 7)) (j₁ 6)
    let β := xor τ (j₁ 7)
    let δ := xor (xor pair (row.val.testBit ((p + 9) % k))) ((constant 1).val.testBit ((p + 8) % k))
    let keys := (Finset.univ : Finset (Fin (2 ^ k))).filter
      (fun q => (List.range 9).all (fun j => bitFn k constant row.val 0 q.val (p + j) == old j))
    let code := fun (q : Fin (2 ^ k)) =>
      let a := xor (bitFn k constant row.val 0 q.val (p + 9)) pair
      let b := xor (bitFn k constant row.val 0 q.val (p + 10)) (old 7)
      let c := xor (bitFn k constant row.val 0 q.val (p + 11)) (old 8)
      a.toNat + 2 * b.toNat + 4 * c.toNat
    let model := fun (s j : ℕ) =>
      let a := s.testBit 0
      let b := s.testBit 1
      let c := s.testBit 2
      if j = 6 then xor α ((!τ) && a)
      else if j = 7 then xor β ((!a) && b)
      else if j = 8 then xor δ ((a == b) && c)
      else first j
    let nextBit := fun (s j : ℕ) =>
      let mix := fun (h : ℕ) => xor (xor (model s (h - 1)) (model s h)) (model s (h + 1))
      xor (xor (mix j) (!(mix (j + 1)) && mix (j + 2))) (j₂ j)
    let guard := xor (xor (first 3) (first 4)) (first 5)
    let hidden := (xor (first 4) (first 5) == !α) && (first 4 == β)
    (∀ q ∈ keys, (∀ j : Fin 8, bitFn k constant row.val 1 q.val (p + 1 + j.val) = model (code q) (1 + j.val)) ∧
      ∀ j : Fin 4, bitFn k constant row.val 2 q.val (p + 2 + j.val) = nextBit (code q) (2 + j.val)) ∧
    (∀ s : Fin 8, (keys.filter (fun q => code q = s.val)).card = 2 ^ (k - 12)) ∧
    (τ = false → guard = true → hidden = true →
      (∀ q ∈ keys, ∀ j : Fin 3, bitFn k constant row.val 2 q.val (p + 2 + j.val) =
        bitFn k constant row.val 2 ref.val (p + 2 + j.val)) ∧
      (keys.filter (fun q => bitFn k constant row.val 2 q.val (p + 5) != j₂ 5)).card = 5 * 2 ^ (k - 12)) := by
  intro old first j₁ j₂ pair τ α β δ keys code model nextBit guard hidden
  have hcode_bits : ∀ (q : Fin (2 ^ k)),
      (code q).testBit 0 = xor (bitFn k constant row.val 0 q.val (p + 9)) pair ∧
      (code q).testBit 1 = xor (bitFn k constant row.val 0 q.val (p + 10)) (old 7) ∧
      (code q).testBit 2 = xor (bitFn k constant row.val 0 q.val (p + 11)) (old 8) ∧
      code q < 8 := by
    intro q
    dsimp only [code]
    cases xor (bitFn k constant row.val 0 q.val (p + 9)) pair <;>
    cases xor (bitFn k constant row.val 0 q.val (p + 10)) (old 7) <;>
    cases xor (bitFn k constant row.val 0 q.val (p + 11)) (old 8) <;>
    decide
  have hmem_keys : ∀ q : Fin (2 ^ k), q ∈ keys ↔
      ∀ j : ℕ, j < 9 → bitFn k constant row.val 0 q.val (p + j) = old j := by
    intro q
    simp only [keys, Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true,
      List.mem_range, beq_iff_eq]
  have hpart1 : ∀ q ∈ keys,
      (∀ j : Fin 8, bitFn k constant row.val 1 q.val (p + 1 + j.val) = model (code q) (1 + j.val)) ∧
      ∀ j : Fin 4, bitFn k constant row.val 2 q.val (p + 2 + j.val) = nextBit (code q) (2 + j.val) := by
    intro q hq
    have hq0 := (hmem_keys q).mp hq
    have hq_inj1 : ∀ i : ℕ, 1 ≤ i → i ≤ 7 →
        injectedFn k constant 1 q.val (p + i) = j₁ i := by
      intro i hi1 hi7
      dsimp only [j₁]
      rw [injectedFn_one hk constant (row := row.val) q.isLt (p + i),
          injectedFn_one hk constant (row := row.val) ref.isLt (p + i)]
      have harg : p + i + 1 = p + (i + 1) := by omega
      rw [harg, hq0 (i + 1) (by omega)]
    have hq_inj2 : ∀ i : ℕ, 2 ≤ i → i ≤ 5 →
        injectedFn k constant 2 q.val (p + i) = j₂ i := by
      intro i hi2 hi5
      dsimp only [j₂]
      rw [injectedFn_two hk constant (row := row.val) q.isLt (p + i) (by omega),
          injectedFn_two hk constant (row := row.val) ref.isLt (p + i) (by omega)]
      have harg : p + i - 1 = p + (i - 1) := by omega
      rw [harg, hq0 (i - 1) (by omega)]
    have hq1 : ∀ j : Fin 8, bitFn k constant row.val 1 q.val (p + 1 + j.val) =
        model (code q) (1 + j.val) := by
      intro j
      have hpos : 1 ≤ p + 1 + j.val := by omega
      have hb1 := bitFn_succ hk constant row.isLt q.isLt 0 (p + 1 + j.val) hpos
      have href1 := bitFn_succ hk constant row.isLt ref.isLt 0 (p + 1 + j.val) hpos
      have hcb := hcode_bits q
      set a := (code q).testBit 0
      set b := (code q).testBit 1
      set c := (code q).testBit 2
      have hX9 : bitFn k constant row.val 0 q.val (p + 9) = xor a pair := by
        rw [hcb.1]; cases bitFn k constant row.val 0 q.val (p + 9) <;> cases pair <;> rfl
      have hX10 : bitFn k constant row.val 0 q.val (p + 10) = xor b (old 7) := by
        rw [hcb.2.1]; cases bitFn k constant row.val 0 q.val (p + 10) <;> cases old 7 <;> rfl
      have hX11 : bitFn k constant row.val 0 q.val (p + 11) = xor c (old 8) := by
        rw [hcb.2.2.1]; cases bitFn k constant row.val 0 q.val (p + 11) <;> cases old 8 <;> rfl
      fin_cases j
      ·
        dsimp only [Fin.zero_eta, Fin.val_zero]
        have hmod_eq : model (code q) 1 = first 1 := rfl
        rw [hmod_eq]
        dsimp only [first]
        have hpeq : p + 1 + 0 = p + 1 := by omega
        rw [hpeq] at hb1 href1 ⊢
        rw [hb1, href1]
        have hsub : p + 1 - 1 = p + 0 := by omega
        have ha1 : p + 1 + 1 = p + 2 := by omega
        have ha2 : p + 1 + 2 = p + 3 := by omega
        have ha3 : p + 1 + 3 = p + 4 := by omega
        have ha4 : p + 1 + 2 - 1 = p + 2 := by omega
        have ha5 : p + 1 + 1 - 1 = p + 1 := by omega
        have ha6 : p + 1 + 1 + 1 = p + 3 := by omega
        have ha7 : p + 1 + 2 + 1 = p + 4 := by omega
        simp only [hsub, ha5, ha6, ha4, ha7, ha1, ha2, hq0 0 (by omega), hq0 1 (by omega),
          hq0 2 (by omega), hq0 3 (by omega), hq0 4 (by omega), hq_inj1 1 (by omega) (by omega)]
        rfl
      ·
        dsimp only [Fin.mk_one, Fin.val_one]
        have hmod_eq : model (code q) 2 = first 2 := rfl
        rw [hmod_eq]
        dsimp only [first]
        have hpeq : p + 1 + 1 = p + 2 := by omega
        rw [hpeq] at hb1 href1 ⊢
        rw [hb1, href1]
        have s1 : p + 2 - 1 = p + 1 := by omega
        have s2 : p + 2 + 1 = p + 3 := by omega
        have s3 : p + 2 + 2 = p + 4 := by omega
        have s4 : p + 2 + 1 - 1 = p + 2 := by omega
        have s5 : p + 2 + 1 + 1 = p + 4 := by omega
        have s6 : p + 2 + 2 - 1 = p + 3 := by omega
        have s7 : p + 2 + 2 + 1 = p + 5 := by omega
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 1 (by omega), hq0 2 (by omega),
          hq0 3 (by omega), hq0 4 (by omega), hq0 5 (by omega), hq_inj1 2 (by omega) (by omega)]
        rfl
      ·
        change bitFn k constant row.val 1 q.val (p + 1 + 2) = model (code q) 3
        have hmod_eq : model (code q) 3 = first 3 := rfl
        rw [hmod_eq]; dsimp only [first]
        have hpeq : p + 1 + 2 = p + 3 := by omega
        rw [hpeq] at hb1 href1 ⊢
        rw [hb1, href1]
        have s1 : p + 3 - 1 = p + 2 := by omega
        have s2 : p + 3 + 1 = p + 4 := by omega
        have s3 : p + 3 + 2 = p + 5 := by omega
        have s4 : p + 3 + 1 - 1 = p + 3 := by omega
        have s5 : p + 3 + 1 + 1 = p + 5 := by omega
        have s6 : p + 3 + 2 - 1 = p + 4 := by omega
        have s7 : p + 3 + 2 + 1 = p + 6 := by omega
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 2 (by omega), hq0 3 (by omega),
          hq0 4 (by omega), hq0 5 (by omega), hq0 6 (by omega), hq_inj1 3 (by omega) (by omega)]
        rfl
      ·
        change bitFn k constant row.val 1 q.val (p + 1 + 3) = model (code q) 4
        have hmod_eq : model (code q) 4 = first 4 := rfl
        rw [hmod_eq]; dsimp only [first]
        have hpeq : p + 1 + 3 = p + 4 := by omega
        rw [hpeq] at hb1 href1 ⊢
        rw [hb1, href1]
        have s1 : p + 4 - 1 = p + 3 := by omega
        have s2 : p + 4 + 1 = p + 5 := by omega
        have s3 : p + 4 + 2 = p + 6 := by omega
        have s4 : p + 4 + 1 - 1 = p + 4 := by omega
        have s5 : p + 4 + 1 + 1 = p + 6 := by omega
        have s6 : p + 4 + 2 - 1 = p + 5 := by omega
        have s7 : p + 4 + 2 + 1 = p + 7 := by omega
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 3 (by omega), hq0 4 (by omega),
          hq0 5 (by omega), hq0 6 (by omega), hq0 7 (by omega), hq_inj1 4 (by omega) (by omega)]
        rfl
      ·
        change bitFn k constant row.val 1 q.val (p + 1 + 4) = model (code q) 5
        have hmod_eq : model (code q) 5 = first 5 := rfl
        rw [hmod_eq]; dsimp only [first]
        have hpeq : p + 1 + 4 = p + 5 := by omega
        rw [hpeq] at hb1 href1 ⊢
        rw [hb1, href1]
        have s1 : p + 5 - 1 = p + 4 := by omega
        have s2 : p + 5 + 1 = p + 6 := by omega
        have s3 : p + 5 + 2 = p + 7 := by omega
        have s4 : p + 5 + 1 - 1 = p + 5 := by omega
        have s5 : p + 5 + 1 + 1 = p + 7 := by omega
        have s6 : p + 5 + 2 - 1 = p + 6 := by omega
        have s7 : p + 5 + 2 + 1 = p + 8 := by omega
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 4 (by omega), hq0 5 (by omega),
          hq0 6 (by omega), hq0 7 (by omega), hq0 8 (by omega), hq_inj1 5 (by omega) (by omega)]
        rfl
      ·
        change bitFn k constant row.val 1 q.val (p + 1 + 5) = model (code q) 6
        have hmod6 : model (code q) 6 = xor α ((!τ) && a) := by simp [model, a]
        rw [hmod6]
        have hpeq : p + 1 + 5 = p + 6 := by omega
        rw [hpeq] at hb1 ⊢
        rw [hb1]
        have s1 : p + 6 - 1 = p + 5 := by omega
        have s2 : p + 6 + 1 = p + 7 := by omega
        have s3 : p + 6 + 2 = p + 8 := by omega
        have s4 : p + 6 + 1 - 1 = p + 6 := by omega
        have s5 : p + 6 + 1 + 1 = p + 8 := by omega
        have s6 : p + 6 + 2 - 1 = p + 7 := by omega
        have s7 : p + 6 + 2 + 1 = p + 9 := by omega
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 5 (by omega), hq0 6 (by omega),
          hq0 7 (by omega), hq0 8 (by omega), hX9, hq_inj1 6 (by omega) (by omega)]
        dsimp only [α, τ, pair]
        generalize old 5 = x5; generalize old 6 = x6; generalize old 7 = x7
        generalize old 8 = x8; generalize j₁ 6 = k6; generalize a = va
        cases x5 <;> cases x6 <;> cases x7 <;> cases x8 <;> cases k6 <;> cases va <;> rfl
      ·
        change bitFn k constant row.val 1 q.val (p + 1 + 6) = model (code q) 7
        have hmod7 : model (code q) 7 = xor β ((!a) && b) := by simp [model, a, b]
        rw [hmod7]
        have hpeq : p + 1 + 6 = p + 7 := by omega
        rw [hpeq] at hb1 ⊢
        rw [hb1]
        have s1 : p + 7 - 1 = p + 6 := by omega
        have s2 : p + 7 + 1 = p + 8 := by omega
        have s3 : p + 7 + 2 = p + 9 := by omega
        have s4 : p + 7 + 1 - 1 = p + 7 := by omega
        have s5 : p + 7 + 1 + 1 = p + 9 := by omega
        have s6 : p + 7 + 2 - 1 = p + 8 := by omega
        have s7 : p + 7 + 2 + 1 = p + 10 := by omega
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 6 (by omega),
          hq0 7 (by omega), hq0 8 (by omega), hX9, hX10, hq_inj1 7 (by omega) (by omega)]
        dsimp only [β, τ, pair]
        generalize old 6 = x6; generalize old 7 = x7; generalize old 8 = x8
        generalize j₁ 7 = k7; generalize a = va; generalize b = vb
        cases x6 <;> cases x7 <;> cases x8 <;> cases k7 <;> cases va <;> cases vb <;> rfl
      ·
        change bitFn k constant row.val 1 q.val (p + 1 + 7) = model (code q) 8
        have hmod8 : model (code q) 8 = xor δ ((a == b) && c) := by simp [model, a, b, c]
        rw [hmod8]
        have hpeq : p + 1 + 7 = p + 8 := by omega
        rw [hpeq] at hb1 ⊢
        rw [hb1]
        have s1 : p + 8 - 1 = p + 7 := by omega
        have s2 : p + 8 + 1 = p + 9 := by omega
        have s3 : p + 8 + 2 = p + 10 := by omega
        have s4 : p + 8 + 1 - 1 = p + 8 := by omega
        have s5 : p + 8 + 1 + 1 = p + 10 := by omega
        have s6 : p + 8 + 2 - 1 = p + 9 := by omega
        have s7 : p + 8 + 2 + 1 = p + 11 := by omega
        rw [injectedFn_one hk constant (row := row.val) q.isLt (p + 8)]
        simp only [s1, s4, s5, s6, s7, s2, s3, hq0 7 (by omega), hq0 8 (by omega), hX9, hX10, hX11]
        dsimp only [δ, pair]
        generalize old 7 = x7; generalize old 8 = x8
        generalize row.val.testBit ((p + 9) % k) = r9
        generalize (constant 1).val.testBit ((p + 8) % k) = c8
        generalize a = va; generalize b = vb; generalize c = vc
        cases x7 <;> cases x8 <;> cases r9 <;> cases c8 <;> cases va <;> cases vb <;> cases vc <;> rfl
    refine ⟨hq1, fun j => ?_⟩
    have hpos : 1 ≤ p + 2 + j.val := by omega
    have hb2 := bitFn_succ hk constant row.isLt q.isLt 1 (p + 2 + j.val) hpos
    have harg : p + 2 + j.val = p + (2 + j.val) := by omega
    have hinj2 : injectedFn k constant (1 + 1) q.val (p + 2 + j.val) = j₂ (2 + j.val) := by
      rw [harg]; exact hq_inj2 (2 + j.val) (by omega) (by omega)
    rw [hb2, hinj2]
    have hmod_at : ∀ i : ℕ, 1 ≤ i → i ≤ 8 →
        bitFn k constant row.val 1 q.val (p + i) = model (code q) i := by
      intro i hi1 hi8
      have h1 := hq1 ⟨i - 1, by omega⟩
      have heq1 : p + 1 + (i - 1) = p + i := by omega
      have heq2 : 1 + (i - 1) = i := by omega
      simpa [heq1, heq2] using h1
    have hbm : ∀ h : ℕ, 2 ≤ h → h ≤ 7 →
        xor (xor (bitFn k constant row.val 1 q.val (p + h - 1)) (bitFn k constant row.val 1 q.val (p + h)))
            (bitFn k constant row.val 1 q.val (p + h + 1)) =
        xor (xor (model (code q) (h - 1)) (model (code q) h)) (model (code q) (h + 1)) := by
      intro h hh2 hh7
      have hs1 : p + h - 1 = p + (h - 1) := by omega
      have hs2 : p + h + 1 = p + (h + 1) := by omega
      rw [hs1, hs2, hmod_at (h - 1) (by omega) (by omega), hmod_at h (by omega) (by omega),
          hmod_at (h + 1) (by omega) (by omega)]
    dsimp only [nextBit]
    have ha0 : p + 2 + j.val = p + (2 + j.val) := by omega
    have ha1 : p + (2 + j.val) + 1 = p + (2 + j.val + 1) := by omega
    have ha2 : p + (2 + j.val) + 2 = p + (2 + j.val + 2) := by omega
    have hjlt := j.isLt
    rw [ha0, hbm (2 + j.val) (by omega) (by omega),
        ha1, hbm (2 + j.val + 1) (by omega) (by omega),
        ha2, hbm (2 + j.val + 2) (by omega) (by omega)]
  have hpart2 : ∀ s : Fin 8, (keys.filter (fun q => code q = s.val)).card = 2 ^ (k - 12) := by
    intro s
    let toY : Fin (2 ^ k) → Fin (2 ^ k) := fun q =>
      ⟨rotFn k 1 q.val ^^^ row.val, Nat.xor_lt_two_pow (rotFn_lt 1 q.val) row.isLt⟩
    let fromY : Fin (2 ^ k) → Fin (2 ^ k) := fun y =>
      ⟨rotFn k (k - 1) (y.val ^^^ row.val), rotFn_lt (k - 1) _⟩
    have htoY_bit : ∀ (q : Fin (2 ^ k)) (pos : ℕ),
        (toY q).val.testBit (pos % k) = bitFn k constant row.val 0 q.val pos := by
      intro q pos
      rfl
    have hfrom_to : ∀ q : Fin (2 ^ k), fromY (toY q) = q := by
      intro q
      ext
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < k
      · dsimp only [fromY, toY]
        have hxor_lt : (rotFn k 1 q.val ^^^ row.val) ^^^ row.val < 2 ^ k :=
          Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (rotFn_lt 1 q.val) row.isLt) row.isLt
        rw [rotFn_testBit (by omega) hxor_lt hi]
        have hmod : (i + k - (k - 1) % k) % k = (i + 1) % k := by
          have : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
          rw [this]
          have h1 : i + k - (k - 1) = i + 1 := by omega
          rw [h1]
        rw [hmod, Nat.testBit_xor, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
        rw [rotFn_testBit (by omega) q.isLt (Nat.mod_lt (i + 1) (by omega)), mod_sub_one (by omega)]
        have hback : (i + 1 + k - 1) % k = i := by
          have : i + 1 + k - 1 = i + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
        rw [hback]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (fromY (toY q)).isLt
              (Nat.pow_le_pow_right (by omega) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le q.isLt
              (Nat.pow_le_pow_right (by omega) (by omega)))]
    have hto_from : ∀ y : Fin (2 ^ k), toY (fromY y) = y := by
      intro y
      ext
      apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < k
      · dsimp only [toY, fromY]
        rw [Nat.testBit_xor, rotFn_testBit (by omega) (rotFn_lt (k - 1) _) hi]
        have h1 : (i + k - 1 % k) % k = (i + k - 1) % k := by
          have : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
          rw [this]
        rw [h1]
        have hxor_lt : y.val ^^^ row.val < 2 ^ k := Nat.xor_lt_two_pow y.isLt row.isLt
        rw [rotFn_testBit (by omega) hxor_lt (Nat.mod_lt _ (by omega)), mod_add_one (by omega)]
        have hback : (i + k - 1 + 1) % k = i := by
          have : i + k - 1 + 1 = i + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
        rw [hback, Nat.testBit_xor, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (toY (fromY y)).isLt
              (Nat.pow_le_pow_right (by omega) (by omega))),
            Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt
              (Nat.pow_le_pow_right (by omega) (by omega)))]
    let posOf : Fin 12 → Fin k := fun j => ⟨(p + j.val) % k, Nat.mod_lt _ (by omega)⟩
    have hpos_inj : Function.Injective posOf := by
      intro j₁ j₂ heq
      have hm : (p + j₁.val) % k = (p + j₂.val) % k := congrArg Fin.val heq
      have hr : p % k < k := Nat.mod_lt p (by omega)
      have h1 : (p % k + j₁.val) % k = (p % k + j₂.val) % k := by
        rwa [Nat.mod_add_mod, Nat.mod_add_mod]
      have hmod_lt2 : ∀ x : ℕ, x < 2 * k → x % k = if x < k then x else x - k := fun x hx => by
        by_cases hx1 : x < k
        · simp [hx1, Nat.mod_eq_of_lt hx1]
        · simp only [hx1, ↓reduceIte]
          have hx2 : x = (x - k) + k := by omega
          conv_lhs => rw [hx2]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod_lt2 (p % k + j₁.val) (by omega), hmod_lt2 (p % k + j₂.val) (by omega)] at h1
      apply Fin.ext
      split_ifs at h1 <;> omega
    let S : Finset (Fin k) := Finset.univ.image posOf
    have hS_card : S.card = 12 := by
      rw [Finset.card_image_of_injective _ hpos_inj, Finset.card_univ, Fintype.card_fin]
    let targJ : Fin 12 → Bool := fun j =>
      if j.val < 9 then old j.val
      else if j.val = 9 then xor (s.val.testBit 0) pair
      else if j.val = 10 then xor (s.val.testBit 1) (old 7)
      else xor (s.val.testBit 2) (old 8)
    let targ : Fin k → Bool := fun i =>
      if h : ∃ j : Fin 12, posOf j = i then targJ (Classical.choose h) else false
    have htarg_at : ∀ j : Fin 12, targ (posOf j) = targJ j := by
      intro j
      have hex : ∃ j' : Fin 12, posOf j' = posOf j := ⟨j, rfl⟩
      simp only [targ, hex, ↓reduceDIte]
      have hspec : posOf (Classical.choose hex) = posOf j := Classical.choose_spec hex
      rw [hpos_inj hspec]
    have hcode_iff : ∀ q : Fin (2 ^ k),
        (q ∈ keys ∧ code q = s.val) ↔ ∀ i ∈ S, (toY q).val.testBit i.val = targ i := by
      intro q
      constructor
      · rintro ⟨hq, hcq⟩ i hi
        rcases Finset.mem_image.mp hi with ⟨j, _, rfl⟩
        rw [htarg_at j]
        have hq0 := (hmem_keys q).mp hq
        have hcb := hcode_bits q
        rw [hcq] at hcb
        dsimp only [targJ, posOf]
        rw [htoY_bit q (p + j.val)]
        by_cases h9 : j.val < 9
        · simp only [h9, ↓reduceIte]; exact hq0 j.val h9
        · by_cases he9 : j.val = 9
          · rw [he9]
            simp only [Nat.lt_irrefl, ↓reduceIte]
            have h1 := hcb.1
            generalize bitFn k constant row.val 0 q.val (p + 9) = x at h1 ⊢
            generalize pair = vp at h1 ⊢
            generalize s.val.testBit 0 = s0 at h1 ⊢
            cases x <;> cases vp <;> cases s0 <;> simp at h1 ⊢
          · by_cases he10 : j.val = 10
            · rw [he10]
              simp only [show ¬(10 < 9) by omega, show (10 : ℕ) ≠ 9 by omega, ↓reduceIte]
              have h1 := hcb.2.1
              generalize bitFn k constant row.val 0 q.val (p + 10) = x at h1 ⊢
              generalize old 7 = o7 at h1 ⊢
              generalize s.val.testBit 1 = s1 at h1 ⊢
              cases x <;> cases o7 <;> cases s1 <;> simp at h1 ⊢
            · have he11 : j.val = 11 := by omega
              rw [he11]
              simp only [show ¬(11 < 9) by omega, show (11 : ℕ) ≠ 9 by omega,
                show (11 : ℕ) ≠ 10 by omega, ↓reduceIte]
              have h1 := hcb.2.2.1
              generalize bitFn k constant row.val 0 q.val (p + 11) = x at h1 ⊢
              generalize old 8 = o8 at h1 ⊢
              generalize s.val.testBit 2 = s2 at h1 ⊢
              cases x <;> cases o8 <;> cases s2 <;> simp at h1 ⊢
      · intro hall
        have hat : ∀ j : Fin 12, bitFn k constant row.val 0 q.val (p + j.val) = targJ j := by
          intro j
          have h1 := hall (posOf j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
          rw [htarg_at j] at h1
          simpa [posOf, htoY_bit] using h1
        refine ⟨(hmem_keys q).mpr fun j hj => ?_, ?_⟩
        · have h1 := hat ⟨j, by omega⟩
          simpa [targJ, hj] using h1
        · have h9 : bitFn k constant row.val 0 q.val (p + 9) = xor (s.val.testBit 0) pair := by
            simpa [targJ] using hat ⟨9, by omega⟩
          have h10 : bitFn k constant row.val 0 q.val (p + 10) = xor (s.val.testBit 1) (old 7) := by
            simpa [targJ] using hat ⟨10, by omega⟩
          have h11 : bitFn k constant row.val 0 q.val (p + 11) = xor (s.val.testBit 2) (old 8) := by
            simpa [targJ] using hat ⟨11, by omega⟩
          have hcb := hcode_bits q
          have hb0 : (code q).testBit 0 = s.val.testBit 0 := by
            rw [hcb.1, h9]; cases s.val.testBit 0 <;> cases pair <;> rfl
          have hb1 : (code q).testBit 1 = s.val.testBit 1 := by
            rw [hcb.2.1, h10]; cases s.val.testBit 1 <;> cases old 7 <;> rfl
          have hb2 : (code q).testBit 2 = s.val.testBit 2 := by
            rw [hcb.2.2.1, h11]; cases s.val.testBit 2 <;> cases old 8 <;> rfl
          apply Nat.eq_of_testBit_eq
          intro i
          by_cases hi : i < 3
          · interval_cases i
            · exact hb0
            · exact hb1
            · exact hb2
          · have hlt1 : code q < 2 ^ i := lt_of_lt_of_le hcb.2.2.2
              (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 3 ≤ i); simpa using this)
            have hlt2 : s.val < 2 ^ i := lt_of_lt_of_le s.isLt
              (by have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 3 ≤ i); simpa using this)
            rw [Nat.testBit_lt_two_pow hlt1, Nat.testBit_lt_two_pow hlt2]
    have hbij : (keys.filter (fun q => code q = s.val)).card =
        ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun y =>
          ∀ i ∈ S, y.val.testBit i.val = targ i)).card := by
      refine Finset.card_bij (fun q _ => toY q) ?_ ?_ ?_
      · intro q hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        exact (hcode_iff q).mp hq
      · intro q₁ _ q₂ _ heq
        have := congrArg fromY heq
        rwa [hfrom_to, hfrom_to] at this
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨fromY y, ?_, hto_from y⟩
        rw [Finset.mem_filter, hcode_iff, hto_from y]
        exact hy
    rw [hbij, card_bits_fixed S targ, hS_card]
  refine ⟨hpart1, hpart2, fun hτ hguard hhidden => ?_⟩
  have href_mem : ref ∈ keys := (hmem_keys ref).mpr fun _ _ => rfl
  have hhid_parts : xor (first 4) (first 5) = !α ∧ first 4 = β := by
    dsimp only [hidden] at hhidden
    simpa [Bool.and_eq_true, beq_iff_eq] using hhidden
  have hf4 : first 4 = β := hhid_parts.2
  have hf5 : first 5 = xor β (!α) := by
    have h1 := hhid_parts.1
    rw [hf4] at h1
    generalize β = vb at h1 ⊢
    generalize first 5 = vf5 at h1 ⊢
    generalize α = va at h1 ⊢
    cases vb <;> cases vf5 <;> cases va <;> simp at h1 ⊢
  have hf3 : first 3 = α := by
    have h1 : xor (xor (first 3) (first 4)) (first 5) = true := hguard
    rw [hf4, hf5] at h1
    generalize first 3 = vf3 at h1 ⊢
    generalize α = va at h1 ⊢
    generalize β = vb at h1 ⊢
    cases vf3 <;> cases va <;> cases vb <;> simp at h1 ⊢
  have hmodel_eq : ∀ (s : ℕ) (j : ℕ), 1 ≤ j → j ≤ 8 →
      model s j =
        (if j = 1 then first 1
         else if j = 2 then first 2
         else if j = 3 then α
         else if j = 4 then β
         else if j = 5 then xor β (!α)
         else if j = 6 then xor α (s.testBit 0)
         else if j = 7 then xor β ((!(s.testBit 0)) && s.testBit 1)
         else if j = 8 then xor δ ((s.testBit 0 == s.testBit 1) && s.testBit 2)
         else false) := by
    intro s j hj1 hj8
    interval_cases j <;> simp [model, hτ, hf3, hf4, hf5]
  constructor
  · intro q hq j
    have hq2 := (hpart1 q hq).2 ⟨j.val, by omega⟩
    have hr2 := (hpart1 ref href_mem).2 ⟨j.val, by omega⟩
    rw [hq2, hr2]
    have hbp1 := hidden_bool_part1 (first 1) (first 2) α β δ (j₂ 2) (j₂ 3) (j₂ 4)
      ((code q).testBit 0) ((code q).testBit 1) ((code q).testBit 2)
    have hbp2 := hidden_bool_part1 (first 1) (first 2) α β δ (j₂ 2) (j₂ 3) (j₂ 4)
      ((code ref).testBit 0) ((code ref).testBit 1) ((code ref).testBit 2)
    fin_cases j
    · dsimp only [Fin.zero_eta, Fin.val_zero, nextBit]
      have h1 : model (code q) 1 = first 1 := hmodel_eq (code q) 1 (by omega) (by omega)
      have h2 : model (code q) 2 = first 2 := hmodel_eq (code q) 2 (by omega) (by omega)
      have h3 : model (code q) 3 = α := hmodel_eq (code q) 3 (by omega) (by omega)
      have h4 : model (code q) 4 = β := hmodel_eq (code q) 4 (by omega) (by omega)
      have h5 : model (code q) 5 = xor β (!α) := hmodel_eq (code q) 5 (by omega) (by omega)
      have r1 : model (code ref) 1 = first 1 := hmodel_eq (code ref) 1 (by omega) (by omega)
      have r2 : model (code ref) 2 = first 2 := hmodel_eq (code ref) 2 (by omega) (by omega)
      have r3 : model (code ref) 3 = α := hmodel_eq (code ref) 3 (by omega) (by omega)
      have r4 : model (code ref) 4 = β := hmodel_eq (code ref) 4 (by omega) (by omega)
      have r5 : model (code ref) 5 = xor β (!α) := hmodel_eq (code ref) 5 (by omega) (by omega)
      simp only [Nat.add_zero, h1, h2, h3, h4, h5, r1, r2, r3, r4, r5]
    · dsimp only [Fin.mk_one, Fin.val_one, nextBit]
      have hl : nextBit (code q) 3 = xor (xor (xor (first 2) α) β) (j₂ 3) := by
        dsimp only [nextBit]
        rw [hmodel_eq (code q) 2 (by omega) (by omega),
            hmodel_eq (code q) 3 (by omega) (by omega),
            hmodel_eq (code q) 4 (by omega) (by omega),
            hmodel_eq (code q) 5 (by omega) (by omega),
            hmodel_eq (code q) 6 (by omega) (by omega)]
        exact hbp1.2.1
      have hr : nextBit (code ref) 3 = xor (xor (xor (first 2) α) β) (j₂ 3) := by
        dsimp only [nextBit]
        rw [hmodel_eq (code ref) 2 (by omega) (by omega),
            hmodel_eq (code ref) 3 (by omega) (by omega),
            hmodel_eq (code ref) 4 (by omega) (by omega),
            hmodel_eq (code ref) 5 (by omega) (by omega),
            hmodel_eq (code ref) 6 (by omega) (by omega)]
        exact hbp2.2.1
      exact hl.trans hr.symm
    · change nextBit (code q) 4 = nextBit (code ref) 4
      have hl : nextBit (code q) 4 = xor true (j₂ 4) := by
        dsimp only [nextBit]
        rw [hmodel_eq (code q) 3 (by omega) (by omega),
            hmodel_eq (code q) 4 (by omega) (by omega),
            hmodel_eq (code q) 5 (by omega) (by omega),
            hmodel_eq (code q) 6 (by omega) (by omega),
            hmodel_eq (code q) 7 (by omega) (by omega)]
        exact hbp1.2.2
      have hr : nextBit (code ref) 4 = xor true (j₂ 4) := by
        dsimp only [nextBit]
        rw [hmodel_eq (code ref) 3 (by omega) (by omega),
            hmodel_eq (code ref) 4 (by omega) (by omega),
            hmodel_eq (code ref) 5 (by omega) (by omega),
            hmodel_eq (code ref) 6 (by omega) (by omega),
            hmodel_eq (code ref) 7 (by omega) (by omega)]
        exact hbp2.2.2
      exact hl.trans hr.symm
  · let goodS : Finset (Fin 8) :=
      Finset.univ.filter (fun s => (nextBit s.val 5 != j₂ 5) = true)
    have hgoodS_card : goodS.card = 5 := by
      have heq_filter : goodS = (Finset.univ : Finset (Fin 8)).filter (fun s =>
          let m : ℕ → Bool := fun j =>
            if j = 4 then β
            else if j = 5 then xor β (!α)
            else if j = 6 then xor α (s.val.testBit 0)
            else if j = 7 then xor β ((!(s.val.testBit 0)) && s.val.testBit 1)
            else if j = 8 then xor δ ((s.val.testBit 0 == s.val.testBit 1) && s.val.testBit 2)
            else false
          let mix : ℕ → Bool := fun h => xor (xor (m (h - 1)) (m h)) (m (h + 1))
          xor (mix 5) (!(mix 6) && mix 7) = true) := by
        have hxor_ne : ∀ x y : Bool, ¬(xor x y = y) ↔ x = true := by decide
        ext s
        simp only [goodS, Finset.mem_filter, Finset.mem_univ, true_and, bne_iff_ne, ne_eq]
        dsimp only [nextBit]
        rw [hmodel_eq s.val 4 (by omega) (by omega),
            hmodel_eq s.val 5 (by omega) (by omega),
            hmodel_eq s.val 6 (by omega) (by omega),
            hmodel_eq s.val 7 (by omega) (by omega),
            hmodel_eq s.val 8 (by omega) (by omega)]
        rw [hxor_ne]
        simp only [show (4 : ℕ) ≠ 1 by omega, show (4 : ℕ) ≠ 2 by omega, show (4 : ℕ) ≠ 3 by omega,
          show (5 : ℕ) ≠ 1 by omega, show (5 : ℕ) ≠ 2 by omega, show (5 : ℕ) ≠ 3 by omega,
          show (5 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 1 by omega, show (6 : ℕ) ≠ 2 by omega,
          show (6 : ℕ) ≠ 3 by omega, show (6 : ℕ) ≠ 4 by omega, show (6 : ℕ) ≠ 5 by omega,
          show (7 : ℕ) ≠ 1 by omega, show (7 : ℕ) ≠ 2 by omega, show (7 : ℕ) ≠ 3 by omega,
          show (7 : ℕ) ≠ 4 by omega, show (7 : ℕ) ≠ 5 by omega, show (7 : ℕ) ≠ 6 by omega,
          show (8 : ℕ) ≠ 1 by omega, show (8 : ℕ) ≠ 2 by omega, show (8 : ℕ) ≠ 3 by omega,
          show (8 : ℕ) ≠ 4 by omega, show (8 : ℕ) ≠ 5 by omega, show (8 : ℕ) ≠ 6 by omega,
          show (8 : ℕ) ≠ 7 by omega, ↓reduceIte]
        exact (by decide : ∀ x y : Bool, (xor x y = true) ↔ ¬(x = y)) _ _
      rw [heq_filter]
      exact hidden_bool_count5 α β δ
    have hpart_eq : keys.filter (fun q => (bitFn k constant row.val 2 q.val (p + 5) != j₂ 5) = true) =
        goodS.biUnion (fun s => keys.filter (fun q => code q = s.val)) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_biUnion, goodS, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hq, hne⟩
        have hq5 : bitFn k constant row.val 2 q.val (p + 5) = nextBit (code q) 5 := by
          have h := (hpart1 q hq).2 ⟨3, by omega⟩
          have hpeq : p + 2 + 3 = p + 5 := by omega
          simpa [hpeq] using h
        have hlt8 := (hcode_bits q).2.2.2
        refine ⟨⟨code q, hlt8⟩, ?_, hq, rfl⟩
        dsimp only
        rw [← hq5]; exact hne
      · rintro ⟨s, hs, hq, hcq⟩
        refine ⟨hq, ?_⟩
        have hq5 : bitFn k constant row.val 2 q.val (p + 5) = nextBit (code q) 5 := by
          have h := (hpart1 q hq).2 ⟨3, by omega⟩
          have hpeq : p + 2 + 3 = p + 5 := by omega
          simpa [hpeq] using h
        rw [hq5, hcq]
        exact hs
    rw [hpart_eq, Finset.card_biUnion]
    · simp_rw [hpart2]
      rw [Finset.sum_const, smul_eq_mul, hgoodS_card]
    · intro s₁ _ s₂ _ hne
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      simp only [Finset.mem_filter] at hq₁ hq₂
      exact hne (Fin.ext (hq₁.2.symm.trans hq₂.2))

end PEqualNP.Outside.L_meta_25620_aux

theorem PEqualNP.Outside.L_meta_25620 : (∀ (k : Nat), 0 < k → ∀ constant : Nat → Fin (2 ^ k),
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
  12 ≤ k → ∀ (row ref : Fin (2^k)) (p : Nat),
  let old := fun (j : Nat) => bit row.val 0 ref.val (p+j)
  let first := fun (j : Nat) => bit row.val 1 ref.val (p+j)
  let j₁ := fun (j : Nat) => injected 1 ref.val (p+j)
  let j₂ := fun (j : Nat) => injected 2 ref.val (p+j)
  let pair := xor (old 7) (old 8)
  let τ := xor (old 6) pair
  let α := xor (xor (xor (old 5) (old 6)) (old 7)) (j₁ 6)
  let β := xor τ (j₁ 7)
  let δ := xor (xor pair (row.val.testBit ((p+9)%k))) ((constant 1).val.testBit ((p+8)%k))
  let keys := (Finset.univ : Finset (Fin (2^k))).filter
    (fun q => (List.range 9).all (fun j => bit row.val 0 q.val (p+j) == old j))
  let code := fun (q : Fin (2^k)) =>
    let a := xor (bit row.val 0 q.val (p+9)) pair
    let b := xor (bit row.val 0 q.val (p+10)) (old 7)
    let c := xor (bit row.val 0 q.val (p+11)) (old 8)
    a.toNat + 2*b.toNat + 4*c.toNat
  let model := fun (s j : Nat) =>
    let a := s.testBit 0
    let b := s.testBit 1
    let c := s.testBit 2
    if j = 6 then xor α ((!τ) && a)
    else if j = 7 then xor β ((!a) && b)
    else if j = 8 then xor δ ((a == b) && c)
    else first j
  let nextBit := fun (s j : Nat) =>
    let mix := fun (h : Nat) => xor (xor (model s (h-1)) (model s h)) (model s (h+1))
    xor (xor (mix j) (!(mix (j+1)) && mix (j+2))) (j₂ j)
  let guard := xor (xor (first 3) (first 4)) (first 5)
  let hidden := (xor (first 4) (first 5) == !α) && (first 4 == β)
  (∀ q ∈ keys, (∀ j : Fin 8, bit row.val 1 q.val (p+1+j.val) = model (code q) (1+j.val)) ∧
    ∀ j : Fin 4, bit row.val 2 q.val (p+2+j.val) = nextBit (code q) (2+j.val)) ∧
  (∀ s : Fin 8, (keys.filter (fun q => code q = s.val)).card = 2^(k-12)) ∧
  (τ = false → guard = true → hidden = true →
    (∀ q ∈ keys, ∀ j : Fin 3, bit row.val 2 q.val (p+2+j.val) =
      bit row.val 2 ref.val (p+2+j.val)) ∧
    (keys.filter (fun q => bit row.val 2 q.val (p+5) != j₂ 5)).card = 5*2^(k-12))) := by
  intro k hk0 constant
  dsimp only
  intro hk row ref p
  exact PEqualNP.Outside.L_meta_25620_aux.prove_25620 k hk0 constant hk row ref p
