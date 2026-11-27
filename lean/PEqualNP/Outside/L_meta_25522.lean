import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25522

def Bounded (k x : Nat) : Prop :=
  ∀ m, k ≤ m → x.testBit m = false

def rotOp (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def stepOp (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc j =>
    acc ||| ((xor (word.testBit j)
      (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0

def off (k i n : Nat) : Nat :=
  (i + k - 4 + n) % k

def Indep (F : Bool → Bool → Bool) : Prop :=
  ∀ va vb, F va vb = F false false

def DepB (F : Bool → Bool → Bool) : Prop :=
  ∀ va vb, F va vb = xor vb (F false false)

def NoA (F : Bool → Bool → Bool) : Prop :=
  ∀ va vb, F va vb = F false vb

def CoeffA (F : Bool → Bool → Bool) (G : Bool → Bool) : Prop :=
  ∀ va vb, F va vb = xor (va && G vb) (F false vb)

lemma bounded_of_lt (k x : Nat) (hx : x < 2 ^ k) : Bounded k x := by
  intro m hm
  have hpow : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  exact Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx hpow)

lemma bounded_mod_two_pow (k x : Nat) : Bounded k (x % 2 ^ k) := by
  apply bounded_of_lt
  exact Nat.mod_lt x (Nat.two_pow_pos k)

lemma bounded_rotOp (k s word : Nat) : Bounded k (rotOp k s word) :=
  bounded_mod_two_pow k _

lemma bounded_xor (k x y : Nat) (hx : Bounded k x) (hy : Bounded k y) :
    Bounded k (x ^^^ y) := by
  intro m hm
  rw [Nat.testBit_xor, hx m hm, hy m hm]
  rfl

lemma bounded_two_pow (k d : Nat) (hd : d < k) : Bounded k (2 ^ d) := by
  apply bounded_of_lt
  exact Nat.pow_lt_pow_right (by omega) hd

lemma testBit_toNat_shiftLeft (b : Bool) (j m : Nat) :
    (b.toNat <<< j).testBit m = (decide (m = j) && b) := by
  cases b with
  | false =>
    simp
  | true =>
    rw [Bool.toNat_true, Nat.testBit_shiftLeft]
    by_cases hmj : m = j
    · subst hmj
      simp
    · by_cases hle : j ≤ m
      · have hpos : m - j = (m - j - 1) + 1 := by omega
        rw [hpos, Nat.testBit_succ]
        have hzero : (1 : Nat) / 2 = 0 := by omega
        rw [hzero, Nat.zero_testBit]
        simp [hmj]
      · simp [hmj, hle]

lemma testBit_foldl_bits (f : Nat → Bool) : ∀ (n m : Nat),
    ((List.range n).foldl (fun acc j => acc ||| ((f j).toNat <<< j)) 0).testBit m =
      (decide (m < n) && f m)
  | 0, m => by
    simp
  | n + 1, m => by
    rw [List.range_succ, List.foldl_concat, Nat.testBit_or, testBit_foldl_bits f n m,
      testBit_toNat_shiftLeft]
    by_cases hlt : m < n
    · have hne : m ≠ n := by omega
      have hlt1 : m < n + 1 := by omega
      simp [hlt, hne, hlt1]
    · by_cases heq : m = n
      · subst heq
        simp
      · have hlt1 : ¬ (m < n + 1) := by omega
        simp [hlt, heq, hlt1]

lemma bounded_stepOp (k word : Nat) : Bounded k (stepOp k word) := by
  intro m hm
  unfold stepOp
  rw [testBit_foldl_bits]
  have hlt : ¬ (m < k) := by omega
  simp [hlt]

lemma testBit_stepOp (k word j : Nat) (hj : j < k) :
    (stepOp k word).testBit j =
      xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k)) := by
  unfold stepOp
  rw [testBit_foldl_bits]
  simp [hj]

lemma testBit_rotOp (k s word j : Nat) (hw : Bounded k word) (hj : j < k) :
    (rotOp k s word).testBit j = word.testBit ((j + k - s % k) % k) := by
  have hk : 0 < k := by omega
  have hr : s % k < k := Nat.mod_lt s hk
  unfold rotOp
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hdec : decide (j < k) = true := decide_eq_true hj
  rw [hdec, Bool.true_and]
  by_cases hr0 : s % k = 0
  · rw [hr0]
    have hhi : word.testBit (k - 0 + j) = false := hw (k - 0 + j) (by omega)
    rw [hhi]
    have hmod : (j + k - 0) % k = j := by
      have h1 : j + k - 0 = j + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    rw [hmod]
    simp
  · by_cases hle : s % k ≤ j
    · have hhi : word.testBit (k - s % k + j) = false := hw (k - s % k + j) (by omega)
      rw [hhi]
      have hmod : (j + k - s % k) % k = j - s % k := by
        have h1 : j + k - s % k = (j - s % k) + k := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      simp [hle]
    · have hmod : (j + k - s % k) % k = k - s % k + j := by
        have h1 : j + k - s % k = k - s % k + j := by omega
        rw [h1, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      simp [hle]

lemma off_lt (k i n : Nat) (hk : 13 ≤ k) : off k i n < k :=
  Nat.mod_lt _ (by omega)

lemma off_add (k i n s : Nat) : (off k i n + s) % k = off k i (n + s) := by
  unfold off
  rw [Nat.mod_add_mod]
  congr 1
  omega

lemma off_sub (k i n s : Nat) (hk : 13 ≤ k) (hsn : s ≤ n) (hsk : s < k) :
    (off k i n + k - s % k) % k = off k i (n - s) := by
  rw [Nat.mod_eq_of_lt hsk]
  unfold off
  have h1 : (i + k - 4 + n) % k + k - s = (i + k - 4 + n) % k + (k - s) := by omega
  rw [h1, Nat.mod_add_mod]
  have h2 : i + k - 4 + n + (k - s) = (i + k - 4 + (n - s)) + k := by omega
  rw [h2, Nat.add_mod_right]

lemma off_km1 (k i n : Nat) (hk : 13 ≤ k) :
    (off k i n + k - (k - 1) % k) % k = off k i (n + 1) := by
  rw [Nat.mod_eq_of_lt (by omega : k - 1 < k)]
  have h1 : off k i n + k - (k - 1) = off k i n + 1 := by omega
  rw [h1]
  exact off_add k i n 1

lemma off_1 (k i : Nat) (hk : 13 ≤ k) : off k i 1 = (i + k - 3) % k := by
  unfold off
  congr 1
  omega

lemma off_2 (k i : Nat) (hk : 13 ≤ k) : off k i 2 = (i + k - 2) % k := by
  unfold off
  congr 1
  omega

lemma off_4 (k i : Nat) (hk : 13 ≤ k) (hi : i < k) : off k i 4 = i := by
  unfold off
  have h1 : i + k - 4 + 4 = i + k := by omega
  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma off_ne (k i n1 n2 : Nat) (hk : 13 ≤ k) (h12 : n1 < n2) (hd : n2 - n1 < k) :
    off k i n1 ≠ off k i n2 := by
  have hadd : off k i n2 = (off k i n1 + (n2 - n1)) % k := by
    have h := off_add k i n1 (n2 - n1)
    have heq : n1 + (n2 - n1) = n2 := by omega
    rw [heq] at h
    exact h.symm
  rw [hadd]
  have hlt : off k i n1 < k := off_lt k i n1 hk
  by_cases hsum : off k i n1 + (n2 - n1) < k
  · rw [Nat.mod_eq_of_lt hsum]
    omega
  · have hsub : (off k i n1 + (n2 - n1)) % k = off k i n1 + (n2 - n1) - k := by
      rw [Nat.mod_eq_sub_mod (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    omega

lemma testBit_rot0_off (k i n w : Nat) (hk : 13 ≤ k) (hw : Bounded k w) :
    (rotOp k 0 w).testBit (off k i n) = w.testBit (off k i n) := by
  rw [testBit_rotOp k 0 w (off k i n) hw (off_lt k i n hk)]
  have h := off_sub k i n 0 hk (by omega) (by omega)
  simpa using congrArg w.testBit h

lemma testBit_rot1_off (k i n w : Nat) (hk : 13 ≤ k) (hw : Bounded k w) (hn : 1 ≤ n) :
    (rotOp k 1 w).testBit (off k i n) = w.testBit (off k i (n - 1)) := by
  rw [testBit_rotOp k 1 w (off k i n) hw (off_lt k i n hk), off_sub k i n 1 hk hn (by omega)]

lemma testBit_rot2_off (k i n w : Nat) (hk : 13 ≤ k) (hw : Bounded k w) (hn : 2 ≤ n) :
    (rotOp k 2 w).testBit (off k i n) = w.testBit (off k i (n - 2)) := by
  rw [testBit_rotOp k 2 w (off k i n) hw (off_lt k i n hk), off_sub k i n 2 hk hn (by omega)]

lemma testBit_rot4_off (k i n w : Nat) (hk : 13 ≤ k) (hw : Bounded k w) (hn : 4 ≤ n) :
    (rotOp k 4 w).testBit (off k i n) = w.testBit (off k i (n - 4)) := by
  rw [testBit_rotOp k 4 w (off k i n) hw (off_lt k i n hk), off_sub k i n 4 hk hn (by omega)]

lemma testBit_rotkm1_off (k i n w : Nat) (hk : 13 ≤ k) (hw : Bounded k w) :
    (rotOp k (k - 1) w).testBit (off k i n) = w.testBit (off k i (n + 1)) := by
  rw [testBit_rotOp k (k - 1) w (off k i n) hw (off_lt k i n hk), off_km1 k i n hk]

lemma testBit_lin_off (k i n w : Nat) (hk : 13 ≤ k) (hw : Bounded k w) (hn : 1 ≤ n) :
    (w ^^^ rotOp k 1 w ^^^ rotOp k (k - 1) w).testBit (off k i n) =
      xor (xor (w.testBit (off k i n)) (w.testBit (off k i (n - 1))))
        (w.testBit (off k i (n + 1))) := by
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot1_off k i n w hk hw hn,
    testBit_rotkm1_off k i n w hk hw]

lemma testBit_step_off (k i n w : Nat) (hk : 13 ≤ k) :
    (stepOp k w).testBit (off k i n) =
      xor (w.testBit (off k i n))
        (!(w.testBit (off k i (n + 1))) && w.testBit (off k i (n + 2))) := by
  rw [testBit_stepOp k w (off k i n) (off_lt k i n hk), off_add k i n 1, off_add k i n 2]

lemma indep_noA {F : Bool → Bool → Bool} (h : Indep F) : NoA F := by
  intro va vb
  rw [h va vb, h false vb]

lemma depB_noA {F : Bool → Bool → Bool} (h : DepB F) : NoA F := by
  intro va vb
  rw [h va vb, h false vb]

lemma noA_coeffA {F : Bool → Bool → Bool} (h : NoA F) : CoeffA F (fun _ => false) := by
  intro va vb
  rw [h va vb]
  simp

lemma const_indep (c : Bool) : Indep (fun _ _ => c) := by
  intro _ _
  rfl

lemma indep_xor {F1 F2 : Bool → Bool → Bool} (h1 : Indep F1) (h2 : Indep F2) :
    Indep (fun va vb => xor (F1 va vb) (F2 va vb)) := by
  intro va vb
  dsimp only
  rw [h1 va vb, h2 va vb]

lemma indep_chi {F0 F1 F2 : Bool → Bool → Bool} (h0 : Indep F0) (h1 : Indep F1) (h2 : Indep F2) :
    Indep (fun va vb => xor (F0 va vb) (!(F1 va vb) && F2 va vb)) := by
  intro va vb
  dsimp only
  rw [h0 va vb, h1 va vb, h2 va vb]

lemma depB_xor_indep {F1 F2 : Bool → Bool → Bool} (h1 : DepB F1) (h2 : Indep F2) :
    DepB (fun va vb => xor (F1 va vb) (F2 va vb)) := by
  intro va vb
  dsimp only
  rw [h1 va vb, h2 va vb]
  cases vb <;> cases F1 false false <;> cases F2 false false <;> rfl

lemma indep_xor_depB {F1 F2 : Bool → Bool → Bool} (h1 : Indep F1) (h2 : DepB F2) :
    DepB (fun va vb => xor (F1 va vb) (F2 va vb)) := by
  intro va vb
  dsimp only
  rw [h1 va vb, h2 va vb]
  cases vb <;> cases F1 false false <;> cases F2 false false <;> rfl

lemma depB_chi {F0 F1 F2 : Bool → Bool → Bool} (h0 : DepB F0) (h1 : Indep F1) (h2 : Indep F2) :
    DepB (fun va vb => xor (F0 va vb) (!(F1 va vb) && F2 va vb)) := by
  intro va vb
  dsimp only
  rw [h0 va vb, h1 va vb, h2 va vb]
  cases vb <;> cases F0 false false <;> cases F1 false false <;> cases F2 false false <;> rfl

lemma coeffA_xor {F1 F2 : Bool → Bool → Bool} {G1 G2 : Bool → Bool}
    (h1 : CoeffA F1 G1) (h2 : CoeffA F2 G2) :
    CoeffA (fun va vb => xor (F1 va vb) (F2 va vb)) (fun vb => xor (G1 vb) (G2 vb)) := by
  intro va vb
  dsimp only
  rw [h1 va vb, h2 va vb]
  cases va <;> cases G1 vb <;> cases G2 vb <;> cases F1 false vb <;> cases F2 false vb <;> rfl

lemma coeffA_chi_aff {F0 F1 F2 : Bool → Bool → Bool} {G0 : Bool → Bool}
    (h0 : CoeffA F0 G0) (h1 : CoeffA F1 (fun _ => true)) (h2 : NoA F2) :
    CoeffA (fun va vb => xor (F0 va vb) (!(F1 va vb) && F2 va vb))
      (fun vb => xor (G0 vb) (F2 false vb)) := by
  intro va vb
  dsimp only
  rw [h0 va vb, h1 va vb, h2 va vb]
  cases va <;> cases G0 vb <;> cases F0 false vb <;> cases F1 false vb <;> cases F2 false vb <;> rfl

lemma coeffA_chi_noA {F0 F1 F2 : Bool → Bool → Bool} {G0 : Bool → Bool}
    (h0 : CoeffA F0 G0) (h1 : NoA F1) (h2 : NoA F2) :
    CoeffA (fun va vb => xor (F0 va vb) (!(F1 va vb) && F2 va vb)) G0 := by
  intro va vb
  dsimp only
  rw [h0 va vb, h1 va vb, h2 va vb]
  cases va <;> cases G0 vb <;> cases F0 false vb <;> cases F1 false vb <;> cases F2 false vb <;> rfl

lemma coeffA_congr {F F' : Bool → Bool → Bool} {G G' : Bool → Bool}
    (h : CoeffA F G) (hF : ∀ va vb, F' va vb = F va vb) (hG : ∀ vb, G vb = G' vb) :
    CoeffA F' G' := by
  intro va vb
  rw [hF va vb, hF false vb, h va vb, hG vb]

lemma indep_congr {F F' : Bool → Bool → Bool}
    (h : Indep F) (hF : ∀ va vb, F' va vb = F va vb) : Indep F' := by
  intro va vb
  rw [hF va vb, hF false false, h va vb]

lemma depB_congr {F F' : Bool → Bool → Bool}
    (h : DepB F) (hF : ∀ va vb, F' va vb = F va vb) : DepB F' := by
  intro va vb
  rw [hF va vb, hF false false, h va vb]

lemma parity_of_coeffA_depB3 {F M0 M1 M2 : Bool → Bool → Bool}
    (hF : CoeffA F (fun vb => xor (xor (M0 false vb) (M1 false vb)) (M2 false vb)))
    (h0 : DepB M0) (h1 : DepB M1) (h2 : DepB M2) :
    xor (xor (F false false) (F true false)) (xor (F false true) (F true true)) = true := by
  have hf10 := hF true false
  have hf11 := hF true true
  have hm0 := h0 false true
  have hm1 := h1 false true
  have hm2 := h2 false true
  rw [hf10, hf11]
  dsimp only
  rw [hm0, hm1, hm2]
  cases F false false <;> cases F false true <;>
    cases M0 false false <;> cases M1 false false <;> cases M2 false false <;> rfl

lemma main (k : Nat) (hk : 13 ≤ k) (c : Nat → Fin (2 ^ k))
    (row key : Fin (2 ^ k)) (i : Fin k) :
    let rot := fun (s word : Nat) =>
      ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
    let step := fun (word : Nat) =>
      (List.range k).foldl (fun acc j =>
        acc ||| ((xor (word.testBit j)
          (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
    let start := fun (u w : Nat) => rot 1 w ^^^ u
    let first := fun (u w : Nat) =>
      (List.range 3).foldl (fun prev roundIndex =>
        step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) w ^^^ (c (roundIndex + 1)).val)
        (start u w)
    let a := 2 ^ ((i.val + k - 3) % k)
    let b := 2 ^ ((i.val + k - 2) % k)
    let value := fun testKey => (first row.val testKey).testBit i.val
    xor (xor (value key.val) (value (key.val ^^^ a)))
      (xor (value (key.val ^^^ b)) (value (key.val ^^^ a ^^^ b))) = true := by
  dsimp only
  let a : Nat := 2 ^ ((i.val + k - 3) % k)
  let b : Nat := 2 ^ ((i.val + k - 2) % k)
  let W : Bool → Bool → Nat := fun va vb =>
    key.val ^^^ (if va then a else 0) ^^^ (if vb then b else 0)
  let S0 : Bool → Bool → Nat := fun va vb => rotOp k 1 (W va vb) ^^^ row.val
  let M0 : Bool → Bool → Nat := fun va vb =>
    S0 va vb ^^^ rotOp k 1 (S0 va vb) ^^^ rotOp k (k - 1) (S0 va vb)
  let S1 : Bool → Bool → Nat := fun va vb =>
    stepOp k (M0 va vb) ^^^ rotOp k 0 (W va vb) ^^^ (c 1).val
  let M1 : Bool → Bool → Nat := fun va vb =>
    S1 va vb ^^^ rotOp k 1 (S1 va vb) ^^^ rotOp k (k - 1) (S1 va vb)
  let S2 : Bool → Bool → Nat := fun va vb =>
    stepOp k (M1 va vb) ^^^ rotOp k 2 (W va vb) ^^^ (c 2).val
  let M2 : Bool → Bool → Nat := fun va vb =>
    S2 va vb ^^^ rotOp k 1 (S2 va vb) ^^^ rotOp k (k - 1) (S2 va vb)
  let S3 : Bool → Bool → Nat := fun va vb =>
    stepOp k (M2 va vb) ^^^ rotOp k 4 (W va vb) ^^^ (c 3).val
  have ha_eq : a = 2 ^ off k i.val 1 := by
    dsimp only [a]
    rw [off_1 k i.val hk]
  have hb_eq : b = 2 ^ off k i.val 2 := by
    dsimp only [b]
    rw [off_2 k i.val hk]
  have hba : Bounded k a := by
    rw [ha_eq]
    exact bounded_two_pow k _ (off_lt k i.val 1 hk)
  have hbb : Bounded k b := by
    rw [hb_eq]
    exact bounded_two_pow k _ (off_lt k i.val 2 hk)
  have hb0 : Bounded k 0 := by
    intro m _
    exact Nat.zero_testBit m
  have hbW : ∀ va vb, Bounded k (W va vb) := by
    intro va vb
    apply bounded_xor
    · apply bounded_xor
      · exact bounded_of_lt k key.val key.isLt
      · cases va <;> simpa using (by assumption)
    · cases vb <;> simpa using (by assumption)
  have hbS0 : ∀ va vb, Bounded k (S0 va vb) := fun va vb =>
    bounded_xor k _ _ (bounded_rotOp k 1 _) (bounded_of_lt k row.val row.isLt)
  have hbS1 : ∀ va vb, Bounded k (S1 va vb) := fun va vb =>
    bounded_xor k _ _ (bounded_xor k _ _ (bounded_stepOp k _) (bounded_rotOp k 0 _))
      (bounded_of_lt k (c 1).val (c 1).isLt)
  have hbS2 : ∀ va vb, Bounded k (S2 va vb) := fun va vb =>
    bounded_xor k _ _ (bounded_xor k _ _ (bounded_stepOp k _) (bounded_rotOp k 2 _))
      (bounded_of_lt k (c 2).val (c 2).isLt)
  let bit : (Bool → Bool → Nat) → Nat → Bool → Bool → Bool :=
    fun F n va vb => (F va vb).testBit (off k i.val n)
  have hW_test : ∀ n va vb, bit W n va vb =
      xor (xor (key.val.testBit (off k i.val n))
        (if va then decide (off k i.val 1 = off k i.val n) else false))
        (if vb then decide (off k i.val 2 = off k i.val n) else false) := by
    intro n va vb
    dsimp only [bit, W]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    cases va <;> cases vb <;> simp [ha_eq, hb_eq, Nat.testBit_two_pow]
  have hW_indep : ∀ n, (n = 0 ∨ (3 ≤ n ∧ n ≤ 12)) → Indep (bit W n) := by
    intro n hn va vb
    rw [hW_test n va vb, hW_test n false false]
    have h1 : off k i.val 1 ≠ off k i.val n := by
      rcases hn with rfl | ⟨h3, h12⟩
      · exact (off_ne k i.val 0 1 hk (by omega) (by omega)).symm
      · exact off_ne k i.val 1 n hk (by omega) (by omega)
    have h2 : off k i.val 2 ≠ off k i.val n := by
      rcases hn with rfl | ⟨h3, h12⟩
      · exact (off_ne k i.val 0 2 hk (by omega) (by omega)).symm
      · exact off_ne k i.val 2 n hk (by omega) (by omega)
    cases va <;> cases vb <;> simp [h1, h2]
  have hW1 : CoeffA (bit W 1) (fun _ => true) := by
    intro va vb
    rw [hW_test 1 va vb, hW_test 1 false vb]
    have h21 : off k i.val 2 ≠ off k i.val 1 :=
      (off_ne k i.val 1 2 hk (by omega) (by omega)).symm
    cases va <;> cases vb <;> simp [h21]
  have hW2 : DepB (bit W 2) := by
    intro va vb
    rw [hW_test 2 va vb, hW_test 2 false false]
    have h12 : off k i.val 1 ≠ off k i.val 2 :=
      off_ne k i.val 1 2 hk (by omega) (by omega)
    cases va <;> cases vb <;> cases key.val.testBit (off k i.val 2) <;> simp [h12]
  have hS0_eq : ∀ n (hn : 1 ≤ n) va vb,
      bit S0 n va vb = xor (bit W (n - 1) va vb) (row.val.testBit (off k i.val n)) := by
    intro n hn va vb
    dsimp only [bit, S0]
    rw [Nat.testBit_xor, testBit_rot1_off k i.val n (W va vb) hk (hbW va vb) hn]
  have hS0_1 : Indep (bit S0 1) :=
    indep_congr (indep_xor (hW_indep 0 (Or.inl rfl)) (const_indep _)) (hS0_eq 1 (by omega))
  have hS0_2 : CoeffA (bit S0 2) (fun _ => true) :=
    coeffA_congr (coeffA_xor hW1 (noA_coeffA (indep_noA (const_indep _))))
      (hS0_eq 2 (by omega)) (fun _ => rfl)
  have hS0_3 : DepB (bit S0 3) :=
    depB_congr (depB_xor_indep hW2 (const_indep _)) (hS0_eq 3 (by omega))
  have hS0_hi : ∀ n, 4 ≤ n → n ≤ 13 → Indep (bit S0 n) := by
    intro n h4 h13
    exact indep_congr
      (indep_xor (hW_indep (n - 1) (Or.inr ⟨by omega, by omega⟩)) (const_indep _))
      (hS0_eq n (by omega))
  have hM0_eq : ∀ n (hn : 1 ≤ n) va vb,
      bit M0 n va vb =
        xor (xor (bit S0 n va vb) (bit S0 (n - 1) va vb)) (bit S0 (n + 1) va vb) := by
    intro n hn va vb
    dsimp only [bit, M0]
    exact testBit_lin_off k i.val n (S0 va vb) hk (hbS0 va vb) hn
  have hM0_2 : CoeffA (bit M0 2) (fun _ => true) :=
    coeffA_congr
      (coeffA_xor (coeffA_xor hS0_2 (noA_coeffA (indep_noA hS0_1))) (noA_coeffA (depB_noA hS0_3)))
      (hM0_eq 2 (by omega)) (fun _ => rfl)
  have hM0_3 : CoeffA (bit M0 3) (fun _ => true) :=
    coeffA_congr
      (coeffA_xor (coeffA_xor (noA_coeffA (depB_noA hS0_3)) hS0_2)
        (noA_coeffA (indep_noA (hS0_hi 4 (by omega) (by omega)))))
      (hM0_eq 3 (by omega)) (fun _ => rfl)
  have hM0_4 : DepB (bit M0 4) :=
    depB_congr
      (depB_xor_indep (indep_xor_depB (hS0_hi 4 (by omega) (by omega)) hS0_3)
        (hS0_hi 5 (by omega) (by omega)))
      (hM0_eq 4 (by omega))
  have hM0_hi : ∀ n, 5 ≤ n → n ≤ 12 → Indep (bit M0 n) := by
    intro n h5 h12
    exact indep_congr
      (indep_xor
        (indep_xor (hS0_hi n (by omega) (by omega)) (hS0_hi (n - 1) (by omega) (by omega)))
        (hS0_hi (n + 1) (by omega) (by omega)))
      (hM0_eq n (by omega))
  have hS1_eq : ∀ n va vb,
      bit S1 n va vb =
        xor (xor (xor (bit M0 n va vb) (!(bit M0 (n + 1) va vb) && bit M0 (n + 2) va vb))
          (bit W n va vb)) ((c 1).val.testBit (off k i.val n)) := by
    intro n va vb
    dsimp only [bit, S1]
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_step_off k i.val n (M0 va vb) hk,
      testBit_rot0_off k i.val n (W va vb) hk (hbW va vb)]
  have hS1_2 : CoeffA (bit S1 2) (fun vb => xor true (bit M0 4 false vb)) :=
    coeffA_congr
      (coeffA_xor
        (coeffA_xor (coeffA_chi_aff hM0_2 hM0_3 (depB_noA hM0_4)) (noA_coeffA (depB_noA hW2)))
        (noA_coeffA (indep_noA (const_indep _))))
      (hS1_eq 2) (fun vb => by cases bit M0 4 false vb <;> rfl)
  have hS1_3 : CoeffA (bit S1 3) (fun _ => true) :=
    coeffA_congr
      (coeffA_xor
        (coeffA_xor
          (coeffA_chi_noA hM0_3 (depB_noA hM0_4) (indep_noA (hM0_hi 5 (by omega) (by omega))))
          (noA_coeffA (indep_noA (hW_indep 3 (Or.inr ⟨by omega, by omega⟩)))))
        (noA_coeffA (indep_noA (const_indep _))))
      (hS1_eq 3) (fun _ => rfl)
  have hS1_4 : DepB (bit S1 4) :=
    depB_congr
      (depB_xor_indep
        (depB_xor_indep
          (depB_chi hM0_4 (hM0_hi 5 (by omega) (by omega)) (hM0_hi 6 (by omega) (by omega)))
          (hW_indep 4 (Or.inr ⟨by omega, by omega⟩)))
        (const_indep _))
      (hS1_eq 4)
  have hS1_hi : ∀ n, 5 ≤ n → n ≤ 10 → Indep (bit S1 n) := by
    intro n h5 h10
    exact indep_congr
      (indep_xor
        (indep_xor
          (indep_chi (hM0_hi n (by omega) (by omega)) (hM0_hi (n + 1) (by omega) (by omega))
            (hM0_hi (n + 2) (by omega) (by omega)))
          (hW_indep n (Or.inr ⟨by omega, by omega⟩)))
        (const_indep _))
      (hS1_eq n)
  have hM1_eq : ∀ n (hn : 1 ≤ n) va vb,
      bit M1 n va vb =
        xor (xor (bit S1 n va vb) (bit S1 (n - 1) va vb)) (bit S1 (n + 1) va vb) := by
    intro n hn va vb
    dsimp only [bit, M1]
    exact testBit_lin_off k i.val n (S1 va vb) hk (hbS1 va vb) hn
  have hM1_3 : CoeffA (bit M1 3) (fun vb => bit M0 4 false vb) :=
    coeffA_congr
      (coeffA_xor (coeffA_xor hS1_3 hS1_2) (noA_coeffA (depB_noA hS1_4)))
      (hM1_eq 3 (by omega)) (fun vb => by cases bit M0 4 false vb <;> rfl)
  have hM1_4 : CoeffA (bit M1 4) (fun _ => true) :=
    coeffA_congr
      (coeffA_xor (coeffA_xor (noA_coeffA (depB_noA hS1_4)) hS1_3)
        (noA_coeffA (indep_noA (hS1_hi 5 (by omega) (by omega)))))
      (hM1_eq 4 (by omega)) (fun _ => rfl)
  have hM1_5 : DepB (bit M1 5) :=
    depB_congr
      (depB_xor_indep (indep_xor_depB (hS1_hi 5 (by omega) (by omega)) hS1_4)
        (hS1_hi 6 (by omega) (by omega)))
      (hM1_eq 5 (by omega))
  have hM1_hi : ∀ n, 6 ≤ n → n ≤ 9 → Indep (bit M1 n) := by
    intro n h6 h9
    exact indep_congr
      (indep_xor
        (indep_xor (hS1_hi n (by omega) (by omega)) (hS1_hi (n - 1) (by omega) (by omega)))
        (hS1_hi (n + 1) (by omega) (by omega)))
      (hM1_eq n (by omega))
  have hS2_eq : ∀ n (hn : 2 ≤ n) va vb,
      bit S2 n va vb =
        xor (xor (xor (bit M1 n va vb) (!(bit M1 (n + 1) va vb) && bit M1 (n + 2) va vb))
          (bit W (n - 2) va vb)) ((c 2).val.testBit (off k i.val n)) := by
    intro n hn va vb
    dsimp only [bit, S2]
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_step_off k i.val n (M1 va vb) hk,
      testBit_rot2_off k i.val n (W va vb) hk (hbW va vb) hn]
  have hS2_3 : CoeffA (bit S2 3)
      (fun vb => xor (xor (bit M0 4 false vb) (bit M1 5 false vb)) true) :=
    coeffA_congr
      (coeffA_xor
        (coeffA_xor (coeffA_chi_aff hM1_3 hM1_4 (depB_noA hM1_5)) hW1)
        (noA_coeffA (indep_noA (const_indep _))))
      (hS2_eq 3 (by omega))
      (fun vb => by cases bit M0 4 false vb <;> cases bit M1 5 false vb <;> rfl)
  have hS2_4 : CoeffA (bit S2 4) (fun _ => true) :=
    coeffA_congr
      (coeffA_xor
        (coeffA_xor
          (coeffA_chi_noA hM1_4 (depB_noA hM1_5) (indep_noA (hM1_hi 6 (by omega) (by omega))))
          (noA_coeffA (depB_noA hW2)))
        (noA_coeffA (indep_noA (const_indep _))))
      (hS2_eq 4 (by omega)) (fun _ => rfl)
  have hS2_5 : DepB (bit S2 5) :=
    depB_congr
      (depB_xor_indep
        (depB_xor_indep
          (depB_chi hM1_5 (hM1_hi 6 (by omega) (by omega)) (hM1_hi 7 (by omega) (by omega)))
          (hW_indep 3 (Or.inr ⟨by omega, by omega⟩)))
        (const_indep _))
      (hS2_eq 5 (by omega))
  have hS2_hi : ∀ n, 6 ≤ n → n ≤ 7 → Indep (bit S2 n) := by
    intro n h6 h7
    exact indep_congr
      (indep_xor
        (indep_xor
          (indep_chi (hM1_hi n (by omega) (by omega)) (hM1_hi (n + 1) (by omega) (by omega))
            (hM1_hi (n + 2) (by omega) (by omega)))
          (hW_indep (n - 2) (Or.inr ⟨by omega, by omega⟩)))
        (const_indep _))
      (hS2_eq n (by omega))
  have hM2_eq : ∀ n (hn : 1 ≤ n) va vb,
      bit M2 n va vb =
        xor (xor (bit S2 n va vb) (bit S2 (n - 1) va vb)) (bit S2 (n + 1) va vb) := by
    intro n hn va vb
    dsimp only [bit, M2]
    exact testBit_lin_off k i.val n (S2 va vb) hk (hbS2 va vb) hn
  have hM2_4 : CoeffA (bit M2 4) (fun vb => xor (bit M0 4 false vb) (bit M1 5 false vb)) :=
    coeffA_congr
      (coeffA_xor (coeffA_xor hS2_4 hS2_3) (noA_coeffA (depB_noA hS2_5)))
      (hM2_eq 4 (by omega))
      (fun vb => by cases bit M0 4 false vb <;> cases bit M1 5 false vb <;> rfl)
  have hM2_5 : CoeffA (bit M2 5) (fun _ => true) :=
    coeffA_congr
      (coeffA_xor (coeffA_xor (noA_coeffA (depB_noA hS2_5)) hS2_4)
        (noA_coeffA (indep_noA (hS2_hi 6 (by omega) (by omega)))))
      (hM2_eq 5 (by omega)) (fun _ => rfl)
  have hM2_6 : DepB (bit M2 6) :=
    depB_congr
      (depB_xor_indep (indep_xor_depB (hS2_hi 6 (by omega) (by omega)) hS2_5)
        (hS2_hi 7 (by omega) (by omega)))
      (hM2_eq 6 (by omega))
  have hS3_eq : ∀ va vb,
      bit S3 4 va vb =
        xor (xor (xor (bit M2 4 va vb) (!(bit M2 5 va vb) && bit M2 6 va vb))
          (bit W 0 va vb)) ((c 3).val.testBit (off k i.val 4)) := by
    intro va vb
    dsimp only [bit, S3]
    rw [Nat.testBit_xor, Nat.testBit_xor, testBit_step_off k i.val 4 (M2 va vb) hk,
      testBit_rot4_off k i.val 4 (W va vb) hk (hbW va vb) (by omega)]
  have hS3_4 : CoeffA (bit S3 4)
      (fun vb => xor (xor (bit M0 4 false vb) (bit M1 5 false vb)) (bit M2 6 false vb)) :=
    coeffA_congr
      (coeffA_xor
        (coeffA_xor (coeffA_chi_aff hM2_4 hM2_5 (depB_noA hM2_6))
          (noA_coeffA (indep_noA (hW_indep 0 (Or.inl rfl)))))
        (noA_coeffA (indep_noA (const_indep _))))
      hS3_eq
      (fun vb => by
        cases bit M0 4 false vb <;> cases bit M1 5 false vb <;> cases bit M2 6 false vb <;> rfl)
  have hpar := parity_of_coeffA_depB3 hS3_4 hM0_4 hM1_5 hM2_6
  have hW00 : W false false = key.val := by
    dsimp only [W]
    simp
  have hW10 : W true false = key.val ^^^ a := by
    dsimp only [W]
    simp
  have hW01 : W false true = key.val ^^^ b := by
    dsimp only [W]
    simp
  have hW11 : W true true = key.val ^^^ a ^^^ b := by
    dsimp only [W]
    simp
  have hbit_eq : ∀ va vb,
      bit S3 4 va vb =
        ((List.range 3).foldl (fun prev roundIndex =>
          stepOp k (prev ^^^ rotOp k 1 prev ^^^ rotOp k (k - 1) prev) ^^^
            rotOp k (2 * roundIndex) (W va vb) ^^^ (c (roundIndex + 1)).val)
          (rotOp k 1 (W va vb) ^^^ row.val)).testBit i.val := by
    intro va vb
    dsimp only [bit, S3, M2, S2, M1, S1, M0, S0]
    rw [off_4 k i.val hk i.isLt]
    rfl
  rw [hbit_eq false false, hbit_eq true false, hbit_eq false true, hbit_eq true true,
    hW00, hW10, hW01, hW11] at hpar
  exact hpar

end PEqualNP.Outside.L_meta_25522

theorem PEqualNP.Outside.L_meta_25522 : ∀ (k : Nat), 13 ≤ k → ∀ (c : Nat → Fin (2 ^ k))
    (row key : Fin (2 ^ k)) (i : Fin k),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let start := fun (u w : Nat) => rot 1 w ^^^ u
  let first := fun (u w : Nat) =>
    (List.range 3).foldl (fun prev roundIndex =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) w ^^^ (c (roundIndex + 1)).val)
      (start u w)
  let a := 2 ^ ((i.val + k - 3) % k)
  let b := 2 ^ ((i.val + k - 2) % k)
  let value := fun testKey => (first row.val testKey).testBit i.val
  xor (xor (value key.val) (value (key.val ^^^ a)))
    (xor (value (key.val ^^^ b)) (value (key.val ^^^ a ^^^ b))) = true := by
  exact PEqualNP.Outside.L_meta_25522.main
