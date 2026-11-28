import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33603_aux

def ofBits (bit : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ofBits bit n + if bit n then 2 ^ n else 0

lemma ofBits_lt (bit : ℕ → Bool) : ∀ n, ofBits bit n < 2 ^ n
  | 0 => by simp [ofBits]
  | n + 1 => by
    have ih := ofBits_lt bit n
    simp only [ofBits, Nat.pow_succ]
    split_ifs <;> omega

lemma testBit_ofBits (bit : ℕ → Bool) : ∀ n i,
    (ofBits bit n).testBit i = (decide (i < n) && bit i)
  | 0, i => by simp [ofBits]
  | n + 1, i => by
    have ih := testBit_ofBits bit n i
    have hlt := ofBits_lt bit n
    simp only [ofBits]
    by_cases hbn : bit n = true
    · simp only [hbn, ↓reduceIte]
      by_cases hi : i < n
      · have hi1 : i < n + 1 := by omega
        simp only [hi, hi1, decide_true, Bool.true_and] at ih ⊢
        rw [← ih, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
        have hdiv : (ofBits bit n + 2 ^ n) / 2 ^ i = ofBits bit n / 2 ^ i + 2 ^ (n - i) := by
          have hpow : 2 ^ n = 2 ^ (n - i) * 2 ^ i := by
            rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
          rw [hpow, Nat.add_mul_div_right _ _ (Nat.two_pow_pos i)]
        have heven : 2 ^ (n - i) % 2 = 0 := by
          obtain ⟨m, hm⟩ : ∃ m, n - i = m + 1 := ⟨n - i - 1, by omega⟩
          rw [hm, Nat.pow_succ]
          omega
        rw [hdiv]
        have hmod : (ofBits bit n / 2 ^ i + 2 ^ (n - i)) % 2 = (ofBits bit n / 2 ^ i) % 2 := by
          omega
        rw [hmod]
      · by_cases heq : i = n
        · subst heq
          simp only [lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and, hbn]
          rw [Nat.testBit_eq_decide_div_mod_eq]
          have hdiv : (ofBits bit i + 2 ^ i) / 2 ^ i = 1 := by
            rw [Nat.add_div_right _ (Nat.two_pow_pos i), Nat.div_eq_of_lt hlt]
          rw [hdiv]
          rfl
        · have hgt : n + 1 ≤ i := by omega
          have hnot : ¬ i < n + 1 := by omega
          simp only [hnot, decide_false, Bool.false_and]
          apply Nat.testBit_eq_false_of_lt
          have h1 : ofBits bit n + 2 ^ n < 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) hgt)
    · have hbnf : bit n = false := by cases h : bit n <;> simp_all
      simp only [hbnf, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      by_cases hi : i < n
      · have hi1 : i < n + 1 := by omega
        simp only [hi, hi1, decide_true, Bool.true_and] at ih ⊢
        exact ih
      · by_cases heq : i = n
        · subst heq
          simp only [lt_add_iff_pos_right, zero_lt_one, decide_true, Bool.true_and, hbnf]
          exact Nat.testBit_eq_false_of_lt hlt
        · have hnot : ¬ i < n + 1 := by omega
          simp only [hnot, decide_false, Bool.false_and]
          exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega)))

def rotW (k s z : ℕ) : ℕ :=
  ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2 ^ k

def mixW (k d z : ℕ) : ℕ :=
  z ^^^ rotW k d z ^^^ rotW k (k - d) z

lemma rotW_lt (k s z : ℕ) : rotW k s z < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_rotW {k s z i : ℕ} (hk : 0 < k) (hz : z < 2 ^ k) (hi : i < k) :
    (rotW k s z).testBit i = z.testBit ((i + k - s % k) % k) := by
  unfold rotW
  have hr : s % k < k := Nat.mod_lt s hk
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.true_and]
  by_cases hri : s % k ≤ i
  · have hge : k ≤ k - s % k + i := by omega
    have h0 : z.testBit (k - s % k + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by omega) hge))
    have hmod : (i + k - s % k) % k = i - s % k := by
      have : i + k - s % k = (i - s % k) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    simp [hri, h0, hmod]
  · have hmod : (i + k - s % k) % k = k - s % k + i := by
      have : i + k - s % k = k - s % k + i := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    simp [hri, hmod]

lemma rotW_xor {k s z₁ z₂ : ℕ} (hk : 0 < k) (h1 : z₁ < 2 ^ k) (h2 : z₂ < 2 ^ k) :
    rotW k s (z₁ ^^^ z₂) = rotW k s z₁ ^^^ rotW k s z₂ := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [testBit_rotW hk (Nat.xor_lt_two_pow h1 h2) hi, Nat.testBit_xor, Nat.testBit_xor,
      testBit_rotW hk h1 hi, testBit_rotW hk h2 hi]
  · have hlt1 : rotW k s (z₁ ^^^ z₂) < 2 ^ k := rotW_lt k s _
    have hlt2 : rotW k s z₁ ^^^ rotW k s z₂ < 2 ^ k := Nat.xor_lt_two_pow (rotW_lt k s z₁) (rotW_lt k s z₂)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt2 (Nat.pow_le_pow_right (by omega) (by omega)))]

lemma mixW_xor {k d z₁ z₂ : ℕ} (hk : 0 < k) (h1 : z₁ < 2 ^ k) (h2 : z₂ < 2 ^ k) :
    mixW k d (z₁ ^^^ z₂) = mixW k d z₁ ^^^ mixW k d z₂ := by
  unfold mixW
  rw [rotW_xor hk h1 h2, rotW_xor hk h1 h2]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_xor]
  cases z₁.testBit i <;> cases z₂.testBit i <;>
    cases (rotW k d z₁).testBit i <;> cases (rotW k d z₂).testBit i <;>
    cases (rotW k (k - d) z₁).testBit i <;> cases (rotW k (k - d) z₂).testBit i <;> rfl

lemma testBit_mixW {k d z i : ℕ} (hd : 0 < d) (hdk : d < k) (hz : z < 2 ^ k) (hi : i < k) :
    (mixW k d z).testBit i =
    xor (xor (z.testBit i) (z.testBit ((i + k - d) % k))) (z.testBit ((i + d) % k)) := by
  have hk : 0 < k := by omega
  unfold mixW
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rotW hk hz hi, testBit_rotW hk hz hi]
  have h1 : d % k = d := Nat.mod_eq_of_lt hdk
  have h2 : (k - d) % k = k - d := Nat.mod_eq_of_lt (by omega)
  have h3 : i + k - (k - d) = i + d := by omega
  rw [h1, h2, h3]

lemma rotW_surj {k s w : ℕ} (hk : 0 < k) (hw : w < 2 ^ k) :
    ∃ x < 2 ^ k, rotW k s x = w := by
  refine ⟨rotW k (k - s % k) w, rotW_lt k _ w, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · rw [testBit_rotW hk (rotW_lt k _ w) hi, testBit_rotW hk hw (Nat.mod_lt _ hk)]
    congr 1
    have hr : s % k < k := Nat.mod_lt s hk
    by_cases h0 : s % k = 0
    · simp [h0, Nat.mod_eq_of_lt hi]
    · have hkr : (k - s % k) % k = k - s % k := Nat.mod_eq_of_lt (by omega)
      rw [hkr]
      by_cases hri : s % k ≤ i
      · have h1 : (i + k - s % k) % k = i - s % k := by
          have : i + k - s % k = (i - s % k) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [h1]
        have h2 : i - s % k + k - (k - s % k) = i := by omega
        rw [h2, Nat.mod_eq_of_lt hi]
      · have h1 : (i + k - s % k) % k = i + k - s % k := Nat.mod_eq_of_lt (by omega)
        rw [h1]
        have h2 : i + k - s % k + k - (k - s % k) = i + k := by omega
        rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (rotW_lt k s _) (Nat.pow_le_pow_right (by omega) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega) (by omega)))]

def solveG (d : ℕ) (hd : 0 < d) (f : ℕ → Bool) : ℕ → Bool
  | j =>
    xor (f j) (xor (if h1 : d ≤ j then solveG d hd f (j - d) else false)
      (if h2 : 2 * d ≤ j then solveG d hd f (j - 2 * d) else false))
termination_by j => j
decreasing_by
  · omega
  · omega

lemma solveG_eq (d : ℕ) (hd : 0 < d) (f : ℕ → Bool) (j : ℕ) :
    solveG d hd f j =
    xor (f j) (xor (if d ≤ j then solveG d hd f (j - d) else false)
      (if 2 * d ≤ j then solveG d hd f (j - 2 * d) else false)) := by
  rw [solveG]
  simp only [dite_eq_ite]

lemma mixW_strip_surj {k d a start : ℕ} (hd : 0 < d) (hle : a + 2 + 2 * d ≤ k)
    (f : ℕ → Bool) :
    ∃ z < 2 ^ k, ∀ j < a + 2, (mixW k d z).testBit ((start + j) % k) = f j := by
  have hk : 0 < k := by omega
  have hdk : d < k := by omega
  let g := solveG d hd f
  let bit : ℕ → Bool := fun m =>
    let off := (m + k - start % k) % k
    if d ≤ off ∧ off < a + 2 + d then g (off - d) else false
  let z := ofBits bit k
  refine ⟨z, ofBits_lt bit k, fun j hj => ?_⟩
  rw [testBit_mixW hd hdk (ofBits_lt bit k) (Nat.mod_lt _ hk)]
  have hbit_off : ∀ t < k, z.testBit ((start + t) % k) =
      if d ≤ t ∧ t < a + 2 + d then g (t - d) else false := by
    intro t ht
    have hm : (start + t) % k < k := Nat.mod_lt _ hk
    rw [testBit_ofBits]
    simp only [hm, decide_true, Bool.true_and, bit]
    have hoff : ((start + t) % k + k - start % k) % k = t := by
      have h1 : (start + t) % k = (start % k + t) % k := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt ht]
      rw [h1]
      have hs : start % k < k := Nat.mod_lt start hk
      by_cases hlt : start % k + t < k
      · rw [Nat.mod_eq_of_lt hlt]
        have : start % k + t + k - start % k = t + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
      · have hmod : (start % k + t) % k = start % k + t - k := by
          have hsub : start % k + t = (start % k + t - k) + k := by omega
          conv_lhs => rw [hsub]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod]
        have : start % k + t - k + k - start % k = t := by omega
        rw [this, Nat.mod_eq_of_lt ht]
    rw [hoff]
  have h0 : z.testBit ((start + j) % k) = if d ≤ j then g (j - d) else false := by
    rw [hbit_off j (by omega)]
    have hjlt : j < a + 2 + d := by omega
    simp [hjlt]
  have hplus : z.testBit (((start + j) % k + d) % k) = g j := by
    have heq : ((start + j) % k + d) % k = (start + (j + d)) % k := by
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
    rw [heq, hbit_off (j + d) (by omega)]
    have h1 : d ≤ j + d := by omega
    have h2 : j + d < a + 2 + d := by omega
    simp [h1, h2]
  have hminus : z.testBit (((start + j) % k + k - d) % k) = if 2 * d ≤ j then g (j - 2 * d) else false := by
    have hshift_back : ∀ m : ℕ, ((start + m) % k + d) % k = (start + j) % k →
        ((start + j) % k + k - d) % k = (start + m) % k := by
      intro m h3
      have hlt1 : (start + m) % k < k := Nat.mod_lt _ hk
      by_cases hlt2 : (start + m) % k + d < k
      · rw [Nat.mod_eq_of_lt hlt2] at h3
        rw [← h3]
        have : (start + m) % k + d + k - d = (start + m) % k + k := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
      · have hmod : ((start + m) % k + d) % k = (start + m) % k + d - k := by
          have hsub : (start + m) % k + d = ((start + m) % k + d - k) + k := by omega
          conv_lhs => rw [hsub]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hmod] at h3
        rw [← h3]
        have : (start + m) % k + d - k + k - d = (start + m) % k := by omega
        rw [this, Nat.mod_eq_of_lt hlt1]
    by_cases h2d : 2 * d ≤ j
    · have heq : ((start + j) % k + k - d) % k = (start + (j - d)) % k :=
        hshift_back (j - d) (by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
          have : start + (j - d) + d = start + j := by omega
          rw [this])
      rw [heq, hbit_off (j - d) (by omega)]
      have hc1 : d ≤ j - d := by omega
      have hc2 : j - d < a + 2 + d := by omega
      have hsub : j - d - d = j - 2 * d := by omega
      simp [h2d, hc1, hc2, hsub]
    · by_cases hd1 : d ≤ j
      · have heq : ((start + j) % k + k - d) % k = (start + (j - d)) % k :=
          hshift_back (j - d) (by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have : start + (j - d) + d = start + j := by omega
            rw [this])
        rw [heq, hbit_off (j - d) (by omega)]
        have hnot : ¬ d ≤ j - d := by omega
        simp [h2d, hnot]
      · have heq : ((start + j) % k + k - d) % k = (start + (j + k - d)) % k :=
          hshift_back (j + k - d) (by
            rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have : start + (j + k - d) + d = (start + j) + k := by omega
            rw [this, Nat.add_mod_right])
        rw [heq, hbit_off (j + k - d) (by omega)]
        have hnot : ¬ j + k - d < a + 2 + d := by omega
        simp [h2d, hnot]
  rw [h0, hminus, hplus]
  dsimp only [g]
  rw [solveG_eq d hd f j]
  cases f j <;> cases (if d ≤ j then solveG d hd f (j - d) else false) <;>
    cases (if 2 * d ≤ j then solveG d hd f (j - 2 * d) else false) <;> rfl

def chi (s : ℕ → Bool) (j : ℕ) : Bool :=
  xor (s j) (!(s (j + 1)) && s (j + 2))

lemma chi_diff_step (p q dp dq : Bool) :
    xor (xor (!(xor p dp) && xor q dq) (!p && q)) false =
    if dp then (if dq then xor p q else q) else (if dq then !p else false) := by
  cases p <;> cases q <;> cases dp <;> cases dq <;> rfl

lemma chi_xor_eq_iff (y δ : ℕ → Bool) (j : ℕ) :
    chi (fun m => xor (y m) (δ m)) j = chi y j ↔
    (if δ (j + 1) then (if δ (j + 2) then xor (y (j + 1)) (y (j + 2)) else y (j + 2))
     else (if δ (j + 2) then !(y (j + 1)) else false)) = δ j := by
  unfold chi
  dsimp only
  cases y j <;> cases y (j + 1) <;> cases y (j + 2) <;>
    cases δ j <;> cases δ (j + 1) <;> cases δ (j + 2) <;> decide

lemma recover_even (u0 u1 u2 v0 v1 v2 : Bool)
    (e0 : xor u0 (!u1 && u2) = xor v0 (!v1 && v2))
    (e1 : xor u0 (u1 && u2) = xor v0 (v1 && v2))
    (e2 : xor (!u0) (!u1 && !u2) = xor (!v0) (!v1 && !v2)) :
    u0 = v0 ∧ u1 = v1 ∧ u2 = v2 := by
  cases u0 <;> cases u1 <;> cases u2 <;> cases v0 <;> cases v1 <;> cases v2 <;> simp_all

lemma recover_odd (u0 u1 u2 v0 v1 v2 : Bool)
    (e0 : xor u0 (!u1 && u2) = xor v0 (!v1 && v2))
    (e1 : xor (!u0) (!u1 && !u2) = xor (!v0) (!v1 && !v2))
    (e2 : xor u0 (u1 && u2) = xor v0 (v1 && v2)) :
    u0 = v0 ∧ u1 = v1 ∧ u2 = v2 := by
  cases u0 <;> cases u1 <;> cases u2 <;> cases v0 <;> cases v1 <;> cases v2 <;> simp_all

lemma chi_shift_invariant (p q hp hq dp dq : Bool)
    (hpol : (dp && hq) = (dq && hp)) :
    (if dp then (if dq then xor (xor p hp) (xor q hq) else xor q hq)
     else (if dq then !(xor p hp) else false)) =
    (if dp then (if dq then xor p q else q) else (if dq then !p else false)) := by
  cases p <;> cases q <;> cases hp <;> cases hq <;> cases dp <;> cases dq <;> simp_all

def findL (h : ℕ → Bool) : ℕ → ℕ
  | 0 => 1
  | m + 1 => if m = 0 then 1 else if h m then findL h m else m + 1

lemma findL_bounds (h : ℕ → Bool) : ∀ m, 1 ≤ m → 1 ≤ findL h m ∧ findL h m ≤ m
  | 0, hm => by omega
  | m + 1, _ => by
    simp only [findL]
    split_ifs with h0 hm'
    · omega
    · have ih := findL_bounds h m (by omega)
      omega
    · omega

lemma findL_all_true (h : ℕ → Bool) : ∀ m, 1 ≤ m → h m = true →
    ∀ j, findL h m ≤ j → j ≤ m → h j = true
  | 0, hm, _ => by omega
  | m + 1, _, hm1 => by
    simp only [findL]
    split_ifs with h0 hm'
    · intro j hj1 hj2
      have : j = 1 := by omega
      subst this; simpa [h0] using hm1
    · intro j hj1 hj2
      by_cases hjm : j ≤ m
      · exact findL_all_true h m (by omega) hm' j hj1 hjm
      · have : j = m + 1 := by omega
        subst this; exact hm1
    · intro j hj1 hj2
      have : j = m + 1 := by omega
      subst this; exact hm1

lemma findL_left_boundary (h : ℕ → Bool) : ∀ m, 1 ≤ m →
    findL h m = 1 ∨ h (findL h m - 1) = false
  | 0, hm => by omega
  | m + 1, _ => by
    simp only [findL]
    split_ifs with h0 hm'
    · exact Or.inl rfl
    · exact findL_left_boundary h m (by omega)
    · right
      have hbf : h m = false := by cases hx : h m <;> simp_all
      simpa using hbf

end PEqualNP.Outside.L_meta_33603_aux

theorem PEqualNP.Outside.L_meta_33603 :
  ∀ (k d a start init last c : Nat), 0 < d → 0 < a → a + 2 + 2*d ≤ k →
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let site := fun j : Nat => (start+j) % k
  let label := fun (u x j : Nat) =>
    let y := mix (rot init x ^^^ u)
    xor (xor (y.testBit (site j))
      (!(y.testBit (site (j+1))) && y.testBit (site (j+2))))
      (xor ((rot last x).testBit (site j)) (c.testBit (site j)))
  let agree := fun (Q : Finset Nat) (u v : Nat) =>
    ∀ x ∈ Q, ∀ j < a, label u x j = label v x j
  let identifies := fun (Q : Finset Nat) =>
    ∀ u ∈ words, ∀ v ∈ words, agree Q u v → agree words u v
  ∀ q : Nat, (∃ Q : Finset Nat, Q ⊆ words ∧ Q.card ≤ q ∧ identifies Q) ↔ 3 ≤ q := by
  intro k d a start init last c hd ha hle words rot mix site label agree identifies q
  have hk : 0 < k := by omega
  have hlabel_iff : ∀ u v x : ℕ, u < 2 ^ k → v < 2 ^ k → x < 2 ^ k → ∀ j < a,
      (label u x j = label v x j ↔
        PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor ((mix (rot init x)).testBit (site m)) ((mix u).testBit (site m))) j =
        PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor ((mix (rot init x)).testBit (site m)) ((mix v).testBit (site m))) j) := by
    intro u v x hu hv hx j _
    have hrx : rot init x < 2 ^ k := PEqualNP.Outside.L_meta_33603_aux.rotW_lt k init x
    have hmu : mix (rot init x ^^^ u) = mix (rot init x) ^^^ mix u :=
      PEqualNP.Outside.L_meta_33603_aux.mixW_xor hk hrx hu
    have hmv : mix (rot init x ^^^ v) = mix (rot init x) ^^^ mix v :=
      PEqualNP.Outside.L_meta_33603_aux.mixW_xor hk hrx hv
    simp only [label, hmu, hmv, Nat.testBit_xor, PEqualNP.Outside.L_meta_33603_aux.chi]
    cases (xor (xor ((mix (rot init x)).testBit (site j)) ((mix u).testBit (site j)))
        (!(xor ((mix (rot init x)).testBit (site (j + 1))) ((mix u).testBit (site (j + 1)))) &&
          xor ((mix (rot init x)).testBit (site (j + 2))) ((mix u).testBit (site (j + 2))))) <;>
      cases (xor (xor ((mix (rot init x)).testBit (site j)) ((mix v).testBit (site j)))
        (!(xor ((mix (rot init x)).testBit (site (j + 1))) ((mix v).testBit (site (j + 1)))) &&
          xor ((mix (rot init x)).testBit (site (j + 2))) ((mix v).testBit (site (j + 2))))) <;>
      cases (xor ((rot last x).testBit (site j)) (c.testBit (site j))) <;> decide
  have hprobe_surj : ∀ f : ℕ → Bool, ∃ x ∈ words,
      ∀ j < a + 2, (mix (rot init x)).testBit (site j) = f j := by
    intro f
    rcases PEqualNP.Outside.L_meta_33603_aux.mixW_strip_surj hd hle f with ⟨z, hz, hzf⟩
    rcases PEqualNP.Outside.L_meta_33603_aux.rotW_surj hk hz with ⟨x, hx, hxz⟩
    refine ⟨x, Finset.mem_range.mpr hx, fun j hj => ?_⟩
    change (PEqualNP.Outside.L_meta_33603_aux.mixW k d (PEqualNP.Outside.L_meta_33603_aux.rotW k init x)).testBit ((start + j) % k) = f j
    rw [hxz]
    exact hzf j hj
  constructor
  · rintro ⟨Q, hQsub, hQcard, hQid⟩
    by_contra hq3
    have hcard2 : Q.card ≤ 2 := by omega
    have hex2 : ∃ x₀ x₁ : ℕ, x₀ < 2 ^ k ∧ x₁ < 2 ^ k ∧ ∀ x ∈ Q, x = x₀ ∨ x = x₁ := by
      have h0lt : 0 < 2 ^ k := Nat.two_pow_pos k
      rcases Q.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
      · exact ⟨0, 0, h0lt, h0lt, by simp⟩
      · have hx₀lt : x₀ < 2 ^ k := Finset.mem_range.mp (hQsub hx₀)
        rcases (Q.erase x₀).eq_empty_or_nonempty with hemp | ⟨x₁, hx₁⟩
        · refine ⟨x₀, x₀, hx₀lt, hx₀lt, fun x hx => Or.inl ?_⟩
          by_contra hne
          have : x ∈ Q.erase x₀ := Finset.mem_erase.mpr ⟨hne, hx⟩
          rw [hemp] at this; exact Finset.notMem_empty _ this
        · have hx₁mem : x₁ ∈ Q := (Finset.mem_erase.mp hx₁).2
          have hx₁ne : x₁ ≠ x₀ := (Finset.mem_erase.mp hx₁).1
          have hx₁lt : x₁ < 2 ^ k := Finset.mem_range.mp (hQsub hx₁mem)
          refine ⟨x₀, x₁, hx₀lt, hx₁lt, fun x hx => ?_⟩
          by_contra hneither
          push Not at hneither
          have hsub3 : ({x₀, x₁, x} : Finset ℕ) ⊆ Q := by
            intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl | rfl <;> assumption
          have hcard3 : ({x₀, x₁, x} : Finset ℕ).card = 3 := by
            rw [Finset.card_insert_of_notMem (by simp [hx₁ne.symm, hneither.1.symm]),
              Finset.card_insert_of_notMem (by simp [hneither.2.symm]), Finset.card_singleton]
          have := Finset.card_le_card hsub3
          omega
    rcases hex2 with ⟨x₀, x₁, hx₀lt, hx₁lt, hQ2⟩
    let X₀ : ℕ → Bool := fun m => (mix (rot init x₀)).testBit (site m)
    let X₁ : ℕ → Bool := fun m => (mix (rot init x₁)).testBit (site m)
    let h : ℕ → Bool := fun m => xor (X₀ m) (X₁ m)
    have hbuild : ∀ (y δ : ℕ → Bool),
        (∀ j < a,
          (if δ (j + 1) then (if δ (j + 2) then xor (y (j + 1)) (y (j + 2)) else y (j + 2))
           else (if δ (j + 2) then !(y (j + 1)) else false)) = δ j) →
        (∀ j < a, (δ (j + 1) && h (j + 2)) = (δ (j + 2) && h (j + 1))) →
        (∃ (y' : ℕ → Bool) (j0 : ℕ), j0 < a ∧
          (if δ (j0 + 1) then (if δ (j0 + 2) then xor (y' (j0 + 1)) (y' (j0 + 2)) else y' (j0 + 2))
           else (if δ (j0 + 2) then !(y' (j0 + 1)) else false)) ≠ δ j0) →
        False := by
      intro y δ hcond hpol ⟨y', j0, hj0, hdis⟩
      let U : ℕ → Bool := fun m => xor (X₀ m) (y m)
      let V : ℕ → Bool := fun m => xor (U m) (δ m)
      rcases PEqualNP.Outside.L_meta_33603_aux.mixW_strip_surj (start := start) hd hle U with ⟨u, hult, huU⟩
      rcases PEqualNP.Outside.L_meta_33603_aux.mixW_strip_surj (start := start) hd hle V with ⟨v, hvlt, hvV⟩
      have huU' : ∀ m < a + 2, (mix u).testBit (site m) = U m := huU
      have hvV' : ∀ m < a + 2, (mix v).testBit (site m) = V m := hvV
      have hagreeQ : agree Q u v := by
        intro x hx j hj
        have hxor_u : ∀ m < a + 2, xor (X₀ m) ((mix u).testBit (site m)) = y m := fun m hm => by
          rw [huU' m hm]; simp [U]
        have hxor_v : ∀ m < a + 2, xor (X₀ m) ((mix v).testBit (site m)) = xor (y m) (δ m) := fun m hm => by
          rw [hvV' m hm]; simp [V, U]
        rcases hQ2 x hx with hx0 | hx1
        · rw [hx0, hlabel_iff u v x₀ hult hvlt hx₀lt j hj]
          have h1 : PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (X₀ m) ((mix u).testBit (site m))) j =
              PEqualNP.Outside.L_meta_33603_aux.chi y j := by
            simp only [PEqualNP.Outside.L_meta_33603_aux.chi, hxor_u j (by omega),
              hxor_u (j + 1) (by omega), hxor_u (j + 2) (by omega)]
          have h2 : PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (X₀ m) ((mix v).testBit (site m))) j =
              PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (y m) (δ m)) j := by
            simp only [PEqualNP.Outside.L_meta_33603_aux.chi, hxor_v j (by omega),
              hxor_v (j + 1) (by omega), hxor_v (j + 2) (by omega)]
          rw [h1, h2]
          exact ((PEqualNP.Outside.L_meta_33603_aux.chi_xor_eq_iff y δ j).mpr (hcond j hj)).symm
        · rw [hx1, hlabel_iff u v x₁ hult hvlt hx₁lt j hj]
          have hX1 : ∀ m, X₁ m = xor (X₀ m) (h m) := fun m => by simp [h]
          have h1 : PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (X₁ m) ((mix u).testBit (site m))) j =
              PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (y m) (h m)) j := by
            simp only [PEqualNP.Outside.L_meta_33603_aux.chi]
            have hm0 : xor (X₁ j) ((mix u).testBit (site j)) = xor (y j) (h j) := by
              rw [hX1 j, huU' j (by omega)]; simp only [U]
              cases X₀ j <;> cases h j <;> cases y j <;> rfl
            have hm1 : xor (X₁ (j + 1)) ((mix u).testBit (site (j + 1))) = xor (y (j + 1)) (h (j + 1)) := by
              rw [hX1 (j + 1), huU' (j + 1) (by omega)]; simp only [U]
              cases X₀ (j + 1) <;> cases h (j + 1) <;> cases y (j + 1) <;> rfl
            have hm2 : xor (X₁ (j + 2)) ((mix u).testBit (site (j + 2))) = xor (y (j + 2)) (h (j + 2)) := by
              rw [hX1 (j + 2), huU' (j + 2) (by omega)]; simp only [U]
              cases X₀ (j + 2) <;> cases h (j + 2) <;> cases y (j + 2) <;> rfl
            rw [hm0, hm1, hm2]
          have h2 : PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (X₁ m) ((mix v).testBit (site m))) j =
              PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (xor (y m) (h m)) (δ m)) j := by
            simp only [PEqualNP.Outside.L_meta_33603_aux.chi]
            have hm0 : xor (X₁ j) ((mix v).testBit (site j)) = xor (xor (y j) (h j)) (δ j) := by
              rw [hX1 j, hvV' j (by omega)]; simp only [V, U]
              cases X₀ j <;> cases h j <;> cases y j <;> cases δ j <;> rfl
            have hm1 : xor (X₁ (j + 1)) ((mix v).testBit (site (j + 1))) = xor (xor (y (j + 1)) (h (j + 1))) (δ (j + 1)) := by
              rw [hX1 (j + 1), hvV' (j + 1) (by omega)]; simp only [V, U]
              cases X₀ (j + 1) <;> cases h (j + 1) <;> cases y (j + 1) <;> cases δ (j + 1) <;> rfl
            have hm2 : xor (X₁ (j + 2)) ((mix v).testBit (site (j + 2))) = xor (xor (y (j + 2)) (h (j + 2))) (δ (j + 2)) := by
              rw [hX1 (j + 2), hvV' (j + 2) (by omega)]; simp only [V, U]
              cases X₀ (j + 2) <;> cases h (j + 2) <;> cases y (j + 2) <;> cases δ (j + 2) <;> rfl
            rw [hm0, hm1, hm2]
          rw [h1, h2]
          have hcond1 :
              (if δ (j + 1) then (if δ (j + 2) then xor (xor (y (j + 1)) (h (j + 1))) (xor (y (j + 2)) (h (j + 2)))
                else xor (y (j + 2)) (h (j + 2)))
               else (if δ (j + 2) then !(xor (y (j + 1)) (h (j + 1))) else false)) = δ j := by
            rw [PEqualNP.Outside.L_meta_33603_aux.chi_shift_invariant _ _ _ _ _ _ (hpol j hj)]
            exact hcond j hj
          exact ((PEqualNP.Outside.L_meta_33603_aux.chi_xor_eq_iff (fun m => xor (y m) (h m)) δ j).mpr hcond1).symm
      have hagreeAll := hQid u (Finset.mem_range.mpr hult) v (Finset.mem_range.mpr hvlt) hagreeQ
      rcases hprobe_surj (fun m => xor (U m) (y' m)) with ⟨xw, hxw, hxw_strip⟩
      have heq := hagreeAll xw hxw j0 hj0
      rw [hlabel_iff u v xw hult hvlt (Finset.mem_range.mp hxw) j0 hj0] at heq
      have h1 : PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor ((mix (rot init xw)).testBit (site m)) ((mix u).testBit (site m))) j0 =
          PEqualNP.Outside.L_meta_33603_aux.chi y' j0 := by
        simp only [PEqualNP.Outside.L_meta_33603_aux.chi]
        have hm0 : xor ((mix (rot init xw)).testBit (site j0)) ((mix u).testBit (site j0)) = y' j0 := by
          rw [hxw_strip j0 (by omega), huU' j0 (by omega)]; cases U j0 <;> cases y' j0 <;> rfl
        have hm1 : xor ((mix (rot init xw)).testBit (site (j0 + 1))) ((mix u).testBit (site (j0 + 1))) = y' (j0 + 1) := by
          rw [hxw_strip (j0 + 1) (by omega), huU' (j0 + 1) (by omega)]; cases U (j0 + 1) <;> cases y' (j0 + 1) <;> rfl
        have hm2 : xor ((mix (rot init xw)).testBit (site (j0 + 2))) ((mix u).testBit (site (j0 + 2))) = y' (j0 + 2) := by
          rw [hxw_strip (j0 + 2) (by omega), huU' (j0 + 2) (by omega)]; cases U (j0 + 2) <;> cases y' (j0 + 2) <;> rfl
        rw [hm0, hm1, hm2]
      have h2 : PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor ((mix (rot init xw)).testBit (site m)) ((mix v).testBit (site m))) j0 =
          PEqualNP.Outside.L_meta_33603_aux.chi (fun m => xor (y' m) (δ m)) j0 := by
        simp only [PEqualNP.Outside.L_meta_33603_aux.chi]
        have hm0 : xor ((mix (rot init xw)).testBit (site j0)) ((mix v).testBit (site j0)) = xor (y' j0) (δ j0) := by
          rw [hxw_strip j0 (by omega), hvV' j0 (by omega)]; simp only [V]
          cases U j0 <;> cases y' j0 <;> cases δ j0 <;> rfl
        have hm1 : xor ((mix (rot init xw)).testBit (site (j0 + 1))) ((mix v).testBit (site (j0 + 1))) = xor (y' (j0 + 1)) (δ (j0 + 1)) := by
          rw [hxw_strip (j0 + 1) (by omega), hvV' (j0 + 1) (by omega)]; simp only [V]
          cases U (j0 + 1) <;> cases y' (j0 + 1) <;> cases δ (j0 + 1) <;> rfl
        have hm2 : xor ((mix (rot init xw)).testBit (site (j0 + 2))) ((mix v).testBit (site (j0 + 2))) = xor (y' (j0 + 2)) (δ (j0 + 2)) := by
          rw [hxw_strip (j0 + 2) (by omega), hvV' (j0 + 2) (by omega)]; simp only [V]
          cases U (j0 + 2) <;> cases y' (j0 + 2) <;> cases δ (j0 + 2) <;> rfl
        rw [hm0, hm1, hm2]
      rw [h1, h2] at heq
      exact hdis ((PEqualNP.Outside.L_meta_33603_aux.chi_xor_eq_iff y' δ j0).mp heq.symm)
    by_cases hha : h a = false
    · apply hbuild (fun m => decide (m = a)) (fun m => decide (m = a + 1))
      · intro j hj
        by_cases hja : j + 1 = a
        · have hj2 : j + 2 = a + 1 := by omega
          have hjn : j ≠ a + 1 := by omega
          simp [hja, hj2, hjn]
        · have h1 : j + 1 ≠ a + 1 := by omega
          have h2 : j + 2 ≠ a + 1 := by omega
          have h3 : j ≠ a + 1 := by omega
          simp only [h1, h2, h3, decide_false, Bool.false_eq_true, ↓reduceIte]
      · intro j hj
        by_cases hja : j + 1 = a
        · have hj2 : j + 2 = a + 1 := by omega
          simp [hja, hj2, hha]
        · have h1 : j + 1 ≠ a + 1 := by omega
          have h2 : j + 2 ≠ a + 1 := by omega
          simp only [h1, h2, decide_false, Bool.false_and]
      · refine ⟨fun _ => false, a - 1, by omega, ?_⟩
        have h1 : a - 1 + 1 = a := by omega
        have h2 : a - 1 + 2 = a + 1 := by omega
        have h3 : a - 1 ≠ a + 1 := by omega
        simp [h1, h2, h3]
    · have hhat : h a = true := by cases hx : h a <;> simp_all
      let L := PEqualNP.Outside.L_meta_33603_aux.findL h a
      have hLb := PEqualNP.Outside.L_meta_33603_aux.findL_bounds h a ha
      have hLtrue := PEqualNP.Outside.L_meta_33603_aux.findL_all_true h a ha hhat
      have hLbd := PEqualNP.Outside.L_meta_33603_aux.findL_left_boundary h a ha
      let R := if h (a + 1) then a + 1 else a
      have hLR : L ≤ R := by dsimp only [R]; split_ifs <;> omega
      have hRa : a ≤ R := by dsimp only [R]; split_ifs <;> omega
      have hRtrue : ∀ m, L ≤ m → m ≤ R → h m = true := by
        intro m hm1 hm2
        dsimp only [R] at hm2
        split_ifs at hm2 with ha1
        · by_cases hma : m ≤ a
          · exact hLtrue m hm1 hma
          · have : m = a + 1 := by omega
            subst this; exact ha1
        · exact hLtrue m hm1 hm2
      let δ : ℕ → Bool := fun m => decide (L ≤ m ∧ m ≤ R)
      let y : ℕ → Bool := fun m =>
        if m < L then true
        else if m ≤ R then (if m = L then false else decide ((m - L - 1) % 2 = 1))
        else decide (L < R)
      apply hbuild y δ
      · intro j hj
        by_cases h1 : j + 2 < L
        · have d0 : δ j = false := by simp [δ]; omega
          have d1 : δ (j + 1) = false := by simp [δ]; omega
          have d2 : δ (j + 2) = false := by simp [δ]; omega
          simp only [d0, d1, d2, Bool.false_eq_true, ↓reduceIte]
        · by_cases h2 : j + 2 = L
          · have d0 : δ j = false := by simp [δ]; omega
            have d1 : δ (j + 1) = false := by simp [δ]; omega
            have d2 : δ (j + 2) = true := by simp [δ]; omega
            have hy1 : y (j + 1) = true := by simp [y]; omega
            simp only [d0, d1, d2, hy1, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
          · by_cases h3 : j + 1 = L
            · have d0 : δ j = false := by simp [δ]; omega
              have d1 : δ (j + 1) = true := by simp [δ]; omega
              by_cases hLR' : L = R
              · have d2 : δ (j + 2) = false := by simp [δ]; omega
                have hy2 : y (j + 2) = false := by
                  simp only [y, show ¬ j + 2 < L by omega, show ¬ j + 2 ≤ R by omega,
                    show ¬ L < R by omega, ↓reduceIte, decide_false]
                simp only [d0, d1, d2, hy2, Bool.false_eq_true, ↓reduceIte]
              · have d2 : δ (j + 2) = true := by simp [δ]; omega
                have hy1 : y (j + 1) = false := by
                  simp only [y, h3, lt_irrefl, hLR, ↓reduceIte]
                have hy2 : y (j + 2) = false := by
                  simp only [y, show ¬ j + 2 < L by omega, show j + 2 ≤ R by omega,
                    show j + 2 ≠ L by omega, show (j + 2 - L - 1) % 2 = 0 by omega,
                    zero_ne_one, decide_false, ↓reduceIte]
                simp only [d0, d1, d2, hy1, hy2, ↓reduceIte, Bool.xor_self]
            · by_cases h4 : j + 2 ≤ R
              · have d0 : δ j = true := by simp [δ]; omega
                have d1 : δ (j + 1) = true := by simp [δ]; omega
                have d2 : δ (j + 2) = true := by simp [δ]; omega
                have hy1a : ¬ j + 1 < L := by omega
                have hy1b : j + 1 ≤ R := by omega
                have hy1ne : j + 1 ≠ L := by omega
                have hy2a : ¬ j + 2 < L := by omega
                have hy2b : j + 2 ≤ R := by omega
                have hy2ne : j + 2 ≠ L := by omega
                simp only [d0, d1, d2, y, hy1a, hy1b, hy1ne, hy2a, hy2b, hy2ne, ↓reduceIte]
                have hstep : j + 2 - L - 1 = (j + 1 - L - 1) + 1 := by omega
                rw [hstep]
                rcases Nat.mod_two_eq_zero_or_one (j + 1 - L - 1) with hm | hm
                · have hm1 : (j + 1 - L - 1 + 1) % 2 = 1 := by omega
                  simp [hm, hm1]
                · have hm1 : (j + 1 - L - 1 + 1) % 2 = 0 := by omega
                  simp [hm, hm1]
              · have d0 : δ j = true := by simp [δ]; omega
                have d1 : δ (j + 1) = true := by simp [δ]; omega
                have d2 : δ (j + 2) = false := by simp [δ]; omega
                have hy2 : y (j + 2) = true := by
                  simp only [y, show ¬ j + 2 < L by omega, show ¬ j + 2 ≤ R by omega,
                    show L < R by omega, ↓reduceIte, decide_true]
                simp only [d0, d1, d2, hy2, Bool.false_eq_true, ↓reduceIte]
      · intro j hj
        by_cases h1 : j + 2 < L
        · have d1 : δ (j + 1) = false := by simp [δ]; omega
          have d2 : δ (j + 2) = false := by simp [δ]; omega
          simp only [d1, d2, Bool.false_and]
        · by_cases h2 : j + 2 = L
          · have d1 : δ (j + 1) = false := by simp [δ]; omega
            have d2 : δ (j + 2) = true := by simp [δ]; omega
            have hne1 : L ≠ 1 := by omega
            have hbf : h (j + 1) = false := by
              have : j + 1 = L - 1 := by omega
              rw [this]
              exact hLbd.resolve_left hne1
            simp only [d1, d2, hbf, Bool.false_and, Bool.and_false]
          · by_cases h3 : j + 2 ≤ R
            · have d1 : δ (j + 1) = true := by simp [δ]; omega
              have d2 : δ (j + 2) = true := by simp [δ]; omega
              have ht1 : h (j + 1) = true := hRtrue (j + 1) (by omega) (by omega)
              have ht2 : h (j + 2) = true := hRtrue (j + 2) (by omega) (by omega)
              simp only [d1, d2, ht1, ht2, Bool.and_true]
            · have d1 : δ (j + 1) = true := by simp [δ]; omega
              have d2 : δ (j + 2) = false := by simp [δ]; omega
              have hja1 : j + 2 = a + 1 := by omega
              have ha1f : h (a + 1) = false := by
                by_contra hnt
                have hat : h (a + 1) = true := by cases hx : h (a + 1) <;> simp_all
                have : R = a + 1 := by simp [R, hat]
                omega
              rw [hja1] at d2
              simp only [d1, d2, hja1, ha1f, Bool.and_false, Bool.false_and]
      · refine ⟨fun m => if L < R then decide (m = L) else true, L - 1, by omega, ?_⟩
        have h1 : L - 1 + 1 = L := by omega
        have h2 : L - 1 + 2 = L + 1 := by omega
        have d0 : δ (L - 1) = false := by simp [δ]; omega
        have d1 : δ L = true := by simp [δ]; omega
        by_cases hlt : L < R
        · have d2 : δ (L + 1) = true := by simp [δ]; omega
          have hne : L + 1 ≠ L := by omega
          simp only [h1, h2, d0, d1, d2, hlt, hne, decide_true, decide_false, ↓reduceIte,
            Bool.xor_false]
          decide
        · have d2 : δ (L + 1) = false := by simp [δ]; omega
          simp only [h1, h2, d0, d1, d2, hlt, Bool.false_eq_true, ↓reduceIte]
          decide
  · intro hq3
    rcases hprobe_surj (fun _ => false) with ⟨x₀, hx₀, hX₀⟩
    rcases hprobe_surj (fun j => decide (j % 2 = 1)) with ⟨x₁, hx₁, hX₁⟩
    rcases hprobe_surj (fun j => decide (j % 2 = 0)) with ⟨x₂, hx₂, hX₂⟩
    refine ⟨{x₀, x₁, x₂}, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    · calc
        ({x₀, x₁, x₂} : Finset ℕ).card ≤ ({x₁, x₂} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({x₂} : Finset ℕ).card + 1 + 1 := Nat.add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp
        _ ≤ q := hq3
    · intro u hu v hv hag
      have hult : u < 2 ^ k := Finset.mem_range.mp hu
      have hvlt : v < 2 ^ k := Finset.mem_range.mp hv
      have hstrip_eq : ∀ m < a + 2, (mix u).testBit (site m) = (mix v).testBit (site m) := by
        have hstep : ∀ j < a,
            (mix u).testBit (site j) = (mix v).testBit (site j) ∧
            (mix u).testBit (site (j + 1)) = (mix v).testBit (site (j + 1)) ∧
            (mix u).testBit (site (j + 2)) = (mix v).testBit (site (j + 2)) := by
          intro j hj
          have e0 := hag x₀ (by simp) j hj
          have e1 := hag x₁ (by simp) j hj
          have e2 := hag x₂ (by simp) j hj
          rw [hlabel_iff u v x₀ hult hvlt (Finset.mem_range.mp hx₀) j hj] at e0
          rw [hlabel_iff u v x₁ hult hvlt (Finset.mem_range.mp hx₁) j hj] at e1
          rw [hlabel_iff u v x₂ hult hvlt (Finset.mem_range.mp hx₂) j hj] at e2
          simp only [PEqualNP.Outside.L_meta_33603_aux.chi,
            hX₀ j (by omega), hX₀ (j + 1) (by omega), hX₀ (j + 2) (by omega),
            hX₁ j (by omega), hX₁ (j + 1) (by omega), hX₁ (j + 2) (by omega),
            hX₂ j (by omega), hX₂ (j + 1) (by omega), hX₂ (j + 2) (by omega),
            Bool.false_xor] at e0 e1 e2
          rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
          · have h1 : (j + 1) % 2 = 1 := by omega
            have h2 : (j + 2) % 2 = 0 := by omega
            simp only [hj0, h1, h2, zero_ne_one, one_ne_zero, decide_false, decide_true,
              Bool.false_xor, Bool.true_xor, Bool.not_not] at e1 e2
            exact PEqualNP.Outside.L_meta_33603_aux.recover_even _ _ _ _ _ _ e0 e1 e2
          · have h1 : (j + 1) % 2 = 0 := by omega
            have h2 : (j + 2) % 2 = 1 := by omega
            simp only [hj1, h1, h2, zero_ne_one, one_ne_zero, decide_false, decide_true,
              Bool.false_xor, Bool.true_xor, Bool.not_not] at e1 e2
            exact PEqualNP.Outside.L_meta_33603_aux.recover_odd _ _ _ _ _ _ e0 e1 e2
        intro m hm
        by_cases hma : m < a
        · exact (hstep m hma).1
        · by_cases hmeq : m = a
          · rw [hmeq]
            have := (hstep (a - 1) (by omega)).2.1
            simpa [show a - 1 + 1 = a by omega] using this
          · have hmeq2 : m = a + 1 := by omega
            rw [hmeq2]
            have := (hstep (a - 1) (by omega)).2.2
            simpa [show a - 1 + 2 = a + 1 by omega] using this
      intro x hx j hj
      rw [hlabel_iff u v x hult hvlt (Finset.mem_range.mp hx) j hj]
      simp only [PEqualNP.Outside.L_meta_33603_aux.chi,
        hstrip_eq j (by omega), hstrip_eq (j + 1) (by omega), hstrip_eq (j + 2) (by omega)]
