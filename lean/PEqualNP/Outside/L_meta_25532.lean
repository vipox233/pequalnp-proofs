import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25532

private theorem testBit_false_of_ge {a k j : Nat} (ha : a < 2 ^ k) (hj : k ≤ j) :
    a.testBit j = false := by
  have hpow : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  have hlt : a < 2 ^ j := Nat.lt_of_lt_of_le ha hpow
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt hlt]
  rfl

private theorem lt_two_pow_of_testBit_false {a k : Nat}
    (h : ∀ j, k ≤ j → a.testBit j = false) : a < 2 ^ k := by
  have hmod : a % 2 ^ k < 2 ^ k := Nat.mod_lt a (Nat.two_pow_pos k)
  suffices heq : a = a % 2 ^ k by omega
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow]
  by_cases hlt : j < k
  · simp [hlt]
  · simp [hlt, h j (by omega)]

private theorem xor_lt_two_pow' {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    (a ^^^ b) < 2 ^ k := by
  apply lt_two_pow_of_testBit_false
  intro j hj
  rw [Nat.testBit_xor, testBit_false_of_ge ha hj, testBit_false_of_ge hb hj]
  rfl

private theorem and_lt_two_pow' {a b k : Nat} (ha : a < 2 ^ k) :
    (a &&& b) < 2 ^ k := by
  apply lt_two_pow_of_testBit_false
  intro j hj
  rw [Nat.testBit_and, testBit_false_of_ge ha hj]
  rfl

private theorem testBit_one_shiftLeft (p j : Nat) :
    (1 <<< p).testBit j = decide (j = p) := by
  rw [Nat.testBit_shiftLeft]
  by_cases hle : p ≤ j
  · simp only [decide_eq_true hle, Bool.true_and]
    by_cases heq : j = p
    · subst heq
      simp
    · simp only [decide_eq_false heq]
      exact testBit_false_of_ge (k := 1) (by omega) (by omega)
  · have hne : j ≠ p := by omega
    simp [hle, hne]

private theorem one_shiftLeft_lt_two_pow {p k : Nat} (hp : p < k) :
    (1 <<< p) < 2 ^ k := by
  apply lt_two_pow_of_testBit_false
  intro j hj
  rw [testBit_one_shiftLeft]
  have hne : j ≠ p := by omega
  simp [hne]

private theorem testBit_bool_shiftLeft (b : Bool) (p j : Nat) :
    (b.toNat <<< p).testBit j = (decide (j = p) && b) := by
  cases b
  · simp
  · simp only [Bool.toNat_true, Bool.and_true]
    exact testBit_one_shiftLeft p j

private theorem mod_sub_eq {k x s : Nat} (hk : 0 < k) (hsx : s ≤ x) :
    (x % k + k - s % k) % k = (x - s) % k := by
  set d := x - s
  have hx : x = d + s := by omega
  rw [hx, Nat.add_mod]
  have hd : d % k < k := Nat.mod_lt d hk
  have hs : s % k < k := Nat.mod_lt s hk
  by_cases hlt : d % k + s % k < k
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : d % k + s % k + k - s % k = d % k + k := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_mod]
  · have hsub_lt : d % k + s % k - k < k := by omega
    have hmod1 : (d % k + s % k) % k = d % k + s % k - k := by
      calc (d % k + s % k) % k
          = ((d % k + s % k - k) + k) % k := by congr 1; omega
        _ = (d % k + s % k - k) % k := Nat.add_mod_right _ _
        _ = d % k + s % k - k := Nat.mod_eq_of_lt hsub_lt
    rw [hmod1]
    have h2 : d % k + s % k - k + k - s % k = d % k := by omega
    rw [h2, Nat.mod_mod]

private theorem mod_add_mod_eq (k x c : Nat) :
    ((x % k) + c) % k = (x + c) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

private theorem mod_ne_of_lt_add {k a b : Nat} (h1 : a < b) (h2 : b < a + k) :
    a % k ≠ b % k := by
  intro heq
  have ha := Nat.div_add_mod a k
  have hb := Nat.div_add_mod b k
  by_cases hdiv : a / k < b / k
  · have hmul : k * (a / k) + k ≤ k * (b / k) := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left k hdiv
    omega
  · have hmul : k * (b / k) ≤ k * (a / k) := Nat.mul_le_mul_left k (by omega)
    omega

private theorem bool_xor_cancel (a0 rv c0 z1 z2 p1 p2 : Bool) :
    xor (xor (xor (xor (xor a0 (xor p1 rv)) c0) z1) z2) p1 =
    xor (xor (xor (xor (xor a0 (xor p2 rv)) c0) z1) z2) p2 := by
  have h : ∀ p, xor (xor (xor (xor (xor a0 (xor p rv)) c0) z1) z2) p =
      xor (xor (xor (xor a0 rv) c0) z1) z2 := by
    intro p
    cases a0 <;> cases rv <;> cases c0 <;> cases z1 <;> cases z2 <;> cases p <;> rfl
  rw [h p1, h p2]

-- Core definitions matching the theorem's let bindings definitionally

private def rotFn (k s bits : Nat) : Nat :=
  ((bits <<< (s % k)) ||| (bits >>> (k - s % k))) % 2 ^ k

private def stepFold (k mixed n : Nat) : Nat :=
  (List.range n).foldl (fun acc place =>
    acc ||| ((xor (mixed.testBit place)
      (!(mixed.testBit ((place + 1) % k)) && mixed.testBit ((place + 2) % k))).toNat <<< place)) 0

private def stepFn (k mixed : Nat) : Nat :=
  stepFold k mixed k

private def zFn (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (n start : Nat) : Nat :=
  let key := rotFn k (k - 1) (start ^^^ row.val)
  (List.range n).foldl (fun prev roundNo =>
    stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^ rotFn k (2 * roundNo) key ^^^
      (constant (roundNo + 1)).val) start

private def posFn (k r i : Nat) (d : Nat → Nat) (roundIdx : Nat) : Nat :=
  k + i + 3 * (r - roundIdx) - d roundIdx

private def pivotFn (k r i : Nat) (d : Nat → Nat) (recordTime : Nat) : Nat :=
  (posFn k r i d recordTime + 5 - 2 * recordTime) % k

private def guardFn (k r i : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (d : Nat → Nat) (guardTime start : Nat) : Bool :=
  let z := zFn k row constant (guardTime - 1) start
  let b := posFn k r i d guardTime
  xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
    (z.testBit ((b + 2) % k))

private def recPred (cut : Nat) (d : Nat → Nat) (time : Nat) : Bool :=
  decide (cut < time) && (List.range time).all (fun prior =>
    decide (prior < cut ∨ prior + d prior < time + d time))

private def hiddenFn (k r i : Nat) (d : Nat → Nat) (recs : List Nat) : Nat :=
  recs.foldl (fun mask entry => mask ||| (1 <<< pivotFn k r i d entry)) 0

private def decodeStep (k r i : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (d : Nat → Nat) (trial visit : Nat) : Nat :=
  if guardFn k r i row constant d visit trial then trial ^^^ (1 <<< pivotFn k r i d visit) else trial

private def decodeFn (k r i : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (d : Nat → Nat) (recs : List Nat) (input : Nat) : Nat :=
  recs.foldl (decodeStep k r i row constant d) (input ^^^ (input &&& hiddenFn k r i d recs))

-- Properties of rotFn, stepFn, zFn

private theorem rotFn_lt (k s bits : Nat) : rotFn k s bits < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

private theorem rotFn_testBit {k s bits u : Nat} (hk : 0 < k) (hbits : bits < 2 ^ k) (hu : u < k) :
    (rotFn k s bits).testBit u = bits.testBit ((u + k - s % k) % k) := by
  unfold rotFn
  rw [Nat.testBit_mod_two_pow, decide_eq_true hu, Bool.true_and,
      Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hsk : s % k < k := Nat.mod_lt s hk
  by_cases hle : s % k ≤ u
  · simp only [decide_eq_true hle, Bool.true_and]
    have hzero : bits.testBit (k - s % k + u) = false := testBit_false_of_ge hbits (by omega)
    rw [hzero, Bool.or_false]
    congr 1
    have hidx : u + k - s % k = (u - s % k) + k := by omega
    have hlt_sub : u - s % k < k := by omega
    rw [hidx, Nat.add_mod_right, Nat.mod_eq_of_lt hlt_sub]
  · simp only [decide_eq_false hle, Bool.false_and, Bool.false_or]
    congr 1
    have hlt : u + k - s % k < k := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega

private theorem rotFn_testBit_sub {k s bits x : Nat} (hk : 0 < k) (hbits : bits < 2 ^ k) (hsx : s ≤ x) :
    (rotFn k s bits).testBit (x % k) = bits.testBit ((x - s) % k) := by
  rw [rotFn_testBit hk hbits (Nat.mod_lt x hk), mod_sub_eq hk hsx]

private theorem rotFn_k_sub_1_testBit {k bits x : Nat} (hk : 2 ≤ k) (hbits : bits < 2 ^ k) :
    (rotFn k (k - 1) bits).testBit (x % k) = bits.testBit ((x + 1) % k) := by
  have hk0 : 0 < k := by omega
  have hkm : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  rw [rotFn_testBit hk0 hbits (Nat.mod_lt x hk0), hkm]
  congr 1
  have h1 : x % k + k - (k - 1) = x % k + 1 := by omega
  rw [h1, mod_add_mod_eq]

private theorem stepFold_testBit (k mixed n j : Nat) :
    (stepFold k mixed n).testBit j =
      if j < n then
        xor (mixed.testBit j) (!(mixed.testBit ((j + 1) % k)) && mixed.testBit ((j + 2) % k))
      else false := by
  induction n with
  | zero =>
    simp [stepFold]
  | succ n ih =>
    unfold stepFold at ih ⊢
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih, testBit_bool_shiftLeft]
    by_cases hlt : j < n
    · have hne : j ≠ n := by omega
      have hlt2 : j < n + 1 := by omega
      simp [hlt, hne, hlt2]
    · by_cases heq : j = n
      · subst heq
        simp
      · have hlt2 : ¬ j < n + 1 := by omega
        simp [hlt, heq, hlt2]

private theorem stepFn_testBit {k mixed j : Nat} (hj : j < k) :
    (stepFn k mixed).testBit j =
      xor (mixed.testBit j) (!(mixed.testBit ((j + 1) % k)) && mixed.testBit ((j + 2) % k)) := by
  unfold stepFn
  rw [stepFold_testBit]
  simp only [hj, ↓reduceIte]

private theorem stepFn_lt (k mixed : Nat) : stepFn k mixed < 2 ^ k := by
  apply lt_two_pow_of_testBit_false
  intro j hj
  unfold stepFn
  rw [stepFold_testBit]
  have hnot : ¬ j < k := by omega
  simp only [hnot, ↓reduceIte]

private theorem zFn_zero (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k)) (start : Nat) :
    zFn k row constant 0 start = start := by
  simp [zFn]

private theorem zFn_succ (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (n start : Nat) :
    zFn k row constant (n + 1) start =
      let prev := zFn k row constant n start
      let key := rotFn k (k - 1) (start ^^^ row.val)
      stepFn k (prev ^^^ rotFn k 1 prev ^^^ rotFn k (k - 1) prev) ^^^
        rotFn k (2 * n) key ^^^ (constant (n + 1)).val := by
  unfold zFn
  rw [List.range_succ, List.foldl_append]
  rfl

private theorem zFn_lt (k : Nat) (row : Fin (2 ^ k)) (constant : Nat → Fin (2 ^ k))
    (n start : Nat) (hstart : start < 2 ^ k) :
    zFn k row constant n start < 2 ^ k := by
  induction n with
  | zero =>
    simpa [zFn_zero] using hstart
  | succ n _ =>
    rw [zFn_succ]
    exact xor_lt_two_pow' (xor_lt_two_pow' (stepFn_lt k _) (rotFn_lt k _ _)) (constant (n + 1)).isLt

private theorem stepMixed_testBit_eq {k p1 p2 x : Nat} (hk : 2 ≤ k)
    (hp1 : p1 < 2 ^ k) (hp2 : p2 < 2 ^ k) (hx : 1 ≤ x)
    (hagree : ∀ y, x - 1 ≤ y → y ≤ x + 3 → p1.testBit (y % k) = p2.testBit (y % k)) :
    (stepFn k (p1 ^^^ rotFn k 1 p1 ^^^ rotFn k (k - 1) p1)).testBit (x % k) =
    (stepFn k (p2 ^^^ rotFn k 1 p2 ^^^ rotFn k (k - 1) p2)).testBit (x % k) := by
  have hk0 : 0 < k := by omega
  have hmix : ∀ y, x ≤ y → y ≤ x + 2 →
      (p1 ^^^ rotFn k 1 p1 ^^^ rotFn k (k - 1) p1).testBit (y % k) =
      (p2 ^^^ rotFn k 1 p2 ^^^ rotFn k (k - 1) p2).testBit (y % k) := by
    intro y hy1 hy2
    simp only [Nat.testBit_xor]
    rw [rotFn_testBit_sub hk0 hp1 (by omega), rotFn_testBit_sub hk0 hp2 (by omega),
        rotFn_k_sub_1_testBit hk hp1, rotFn_k_sub_1_testBit hk hp2,
        hagree y (by omega) (by omega), hagree (y - 1) (by omega) (by omega),
        hagree (y + 1) (by omega) (by omega)]
  rw [stepFn_testBit (Nat.mod_lt x hk0), stepFn_testBit (Nat.mod_lt x hk0),
      mod_add_mod_eq, mod_add_mod_eq,
      hmix x (by omega) (by omega), hmix (x + 1) (by omega) (by omega),
      hmix (x + 2) (by omega) (by omega)]

private def leftShift (n : Nat) : Nat :=
  if n ≤ 3 then n else 2 * n - 3

private theorem zFn_testBit_eq_of_agree {k : Nat} {row : Fin (2 ^ k)}
    {constant : Nat → Fin (2 ^ k)} (hk : 2 ≤ k) {s1 s2 : Nat}
    (hs1 : s1 < 2 ^ k) (hs2 : s2 < 2 ^ k) (n : Nat) :
    ∀ x, 2 * n ≤ x →
      (∀ u, x - leftShift n ≤ u → u ≤ x + 3 * n → s1.testBit (u % k) = s2.testBit (u % k)) →
      (zFn k row constant n s1).testBit (x % k) = (zFn k row constant n s2).testBit (x % k) := by
  have hk0 : 0 < k := by omega
  induction n with
  | zero =>
    intro x _ hagree
    rw [zFn_zero, zFn_zero]
    exact hagree x (by simp [leftShift]) (by omega)
  | succ n ih =>
    intro x hx hagree
    rw [zFn_succ, zFn_succ]
    simp only [Nat.testBit_xor]
    have hstep :
        (stepFn k (zFn k row constant n s1 ^^^ rotFn k 1 (zFn k row constant n s1) ^^^
          rotFn k (k - 1) (zFn k row constant n s1))).testBit (x % k) =
        (stepFn k (zFn k row constant n s2 ^^^ rotFn k 1 (zFn k row constant n s2) ^^^
          rotFn k (k - 1) (zFn k row constant n s2))).testBit (x % k) := by
      apply stepMixed_testBit_eq hk (zFn_lt k row constant n s1 hs1) (zFn_lt k row constant n s2 hs2) (by omega)
      intro y hy1 hy2
      apply ih y (by omega)
      intro u hu1 hu2
      apply hagree u
      · unfold leftShift at hu1 ⊢
        split at hu1 <;> split <;> omega
      · omega
    have hkey :
        (rotFn k (2 * n) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit (x % k) =
        (rotFn k (2 * n) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit (x % k) := by
      rw [rotFn_testBit_sub hk0 (rotFn_lt k _ _) (by omega),
          rotFn_testBit_sub hk0 (rotFn_lt k _ _) (by omega),
          rotFn_k_sub_1_testBit hk (xor_lt_two_pow' hs1 row.isLt),
          rotFn_k_sub_1_testBit hk (xor_lt_two_pow' hs2 row.isLt),
          Nat.testBit_xor, Nat.testBit_xor]
      have hu : s1.testBit ((x - 2 * n + 1) % k) = s2.testBit ((x - 2 * n + 1) % k) := by
        apply hagree (x - 2 * n + 1)
        · unfold leftShift
          split <;> omega
        · omega
      rw [hu]
    rw [hstep, hkey]

-- Record count and ordering lemmas

private def maxF (cut : Nat) (d : Nat → Nat) : Nat → Nat
  | 0 => cut + d cut
  | n + 1 => if n + 1 ≤ cut then cut + d cut else max (maxF cut d n) ((n + 1) + d (n + 1))

private theorem maxF_ge {cut : Nat} {d : Nat → Nat} (hcut : 0 < cut) :
    ∀ n s, cut ≤ s → s ≤ n → s + d s ≤ maxF cut d n := by
  intro n
  induction n with
  | zero =>
    intro s hs1 hs2
    omega
  | succ n ih =>
    intro s hs1 hs2
    unfold maxF
    by_cases hle : n + 1 ≤ cut
    · have hs : s = cut := by omega
      subst hs
      simp [hle]
    · simp only [hle, ↓reduceIte]
      by_cases hsn : s ≤ n
      · exact Nat.le_trans (ih s hs1 hsn) (Nat.le_max_left _ _)
      · have hs : s = n + 1 := by omega
        subst hs
        exact Nat.le_max_right _ _

private theorem maxF_le_count {cut r : Nat} {d : Nat → Nat}
    (hcut : 0 < cut)
    (hd_mono : ∀ t, cut < t → t ≤ r → d t ≤ d (t - 1)) :
    ∀ n, n ≤ r →
      maxF cut d n ≤ cut + d cut + ((List.range (n + 1)).filter (recPred cut d)).length := by
  intro n
  induction n with
  | zero =>
    intro _
    simp [maxF]
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hfilter :
        ((List.range (n + 2)).filter (recPred cut d)).length =
        ((List.range (n + 1)).filter (recPred cut d)).length +
          if recPred cut d (n + 1) then 1 else 0 := by
      rw [List.range_succ, List.filter_append, List.length_append]
      cases h : recPred cut d (n + 1) <;> simp [h]
    rw [hfilter]
    unfold maxF
    by_cases hle : n + 1 ≤ cut
    · simp only [hle, ↓reduceIte]
      omega
    · simp only [hle, ↓reduceIte]
      have hdm : d (n + 1) ≤ d n := by
        simpa using hd_mono (n + 1) (by omega) (by omega)
      have hn_le : n + d n ≤ maxF cut d n := maxF_ge hcut n n (by omega) (by omega)
      cases hpred : recPred cut d (n + 1)
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        unfold recPred at hpred
        have hgt : decide (cut < n + 1) = true := decide_eq_true (by omega)
        rw [hgt, Bool.true_and] at hpred
        have hex : ∃ prior ∈ List.range (n + 1),
            !(decide (prior < cut ∨ prior + d prior < (n + 1) + d (n + 1))) = true := by
          by_contra hno
          have hall : (List.range (n + 1)).all
              (fun prior => decide (prior < cut ∨ prior + d prior < (n + 1) + d (n + 1))) = true := by
            rw [List.all_eq_true]
            intro p hp
            cases hdp : decide (p < cut ∨ p + d p < (n + 1) + d (n + 1))
            · exfalso; exact hno ⟨p, hp, by simp [hdp]⟩
            · rfl
          rw [hall] at hpred
          cases hpred
        rcases hex with ⟨prior, hprior_mem, hprior_bad⟩
        have hprior_lt : prior < n + 1 := List.mem_range.mp hprior_mem
        have hprior_not : ¬(prior < cut ∨ prior + d prior < (n + 1) + d (n + 1)) := by
          intro hgood
          simp [hgood] at hprior_bad
        have hprior_le : prior + d prior ≤ maxF cut d n :=
          maxF_ge hcut n prior (by omega) (by omega)
        have hstep_le : (n + 1) + d (n + 1) ≤ maxF cut d n := by omega
        omega
      · simp only [↓reduceIte]
        omega

-- Hidden bitmask helper

private theorem hidden_foldl_testBit (k r i : Nat) (d : Nat → Nat)
    (l : List Nat) (init j : Nat) :
    (l.foldl (fun mask entry => mask ||| (1 <<< pivotFn k r i d entry)) init).testBit j =
      (init.testBit j || decide (j ∈ l.map (pivotFn k r i d))) := by
  induction l generalizing init with
  | nil =>
    simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.map_cons, List.mem_cons]
    rw [ih, Nat.testBit_or, testBit_one_shiftLeft]
    by_cases h1 : j = pivotFn k r i d a <;>
    by_cases h2 : j ∈ as.map (pivotFn k r i d) <;>
    cases init.testBit j <;> simp [h1, h2]

private theorem hiddenFn_testBit (k r i : Nat) (d : Nat → Nat) (recs : List Nat) (j : Nat) :
    (hiddenFn k r i d recs).testBit j = decide (j ∈ recs.map (pivotFn k r i d)) := by
  unfold hiddenFn
  rw [hidden_foldl_testBit]
  simp

-- Main proof packaged inside namespace

private theorem main_thm
    (k r e q i : Nat) (row : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (d : Nat → Nat)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hker : k + e + 3 = 5 * r) (hi : i < k)
    (hd_bound : ∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t))
    (hd_mono : ∀ t, e + q + 3 < t → t ≤ r → d t ≤ d (t - 1)) :
    let cut := e + q + 3
    let m := r - (3 * e + 2 * q + 2)
    let records := ((List.range (r - e + 1)).filter (recPred cut d)).take m
    records.length = m ∧ (records.map (pivotFn k r i d)).Nodup ∧
    ∀ seed target : Nat, seed < 2 ^ k →
      (decodeFn k r i row constant d records seed = target ↔ target < 2 ^ k ∧
        (∀ j : Fin k, j.val ∉ records.map (pivotFn k r i d) →
          seed.testBit j.val = target.testBit j.val) ∧
        ∀ t ∈ records, guardFn k r i row constant d t target = false) := by
  intro cut m records
  have hk2 : 2 ≤ k := by omega
  have hk0 : 0 < k := by omega
  have hcut0 : 0 < cut := by omega
  -- Basic facts about allRecs and records
  let allRecs := (List.range (r - e + 1)).filter (recPred cut d)
  have hrecs_def : records = allRecs.take m := rfl
  have hall_len : m ≤ allRecs.length := by
    have h1 : (r - e) + d (r - e) ≤ maxF cut d (r - e) :=
      maxF_ge hcut0 (r - e) (r - e) (by omega) (by omega)
    have h2 : maxF cut d (r - e) ≤ cut + d cut + allRecs.length :=
      maxF_le_count hcut0 hd_mono (r - e) (by omega)
    have h3 := (hd_bound cut (by omega) (by omega)).1
    omega
  have hlen : records.length = m := by
    rw [hrecs_def, List.length_take]
    omega
  have hpair_all : allRecs.Pairwise (· < ·) :=
    List.Pairwise.filter _ List.pairwise_lt_range
  have hpair_recs : records.Pairwise (· < ·) := by
    rw [hrecs_def]
    exact hpair_all.take
  -- Membership properties of records
  have hmem_rec : ∀ t ∈ records,
      cut < t ∧ t ≤ r - e ∧ ∀ prior, cut ≤ prior → prior < t → prior + d prior < t + d t := by
    intro t ht
    have ht_all : t ∈ allRecs := List.mem_of_mem_take ht
    have ⟨ht_rng, ht_pred⟩ := List.mem_filter.mp ht_all
    have ht_le : t ≤ r - e := by
      have := List.mem_range.mp ht_rng
      omega
    unfold recPred at ht_pred
    have ⟨hgt_b, hall_b⟩ := Bool.and_eq_true_iff.mp ht_pred
    have hgt : cut < t := of_decide_eq_true hgt_b
    refine ⟨hgt, ht_le, ?_⟩
    intro prior hp1 hp2
    have hmem_p : prior ∈ List.range t := List.mem_range.mpr hp2
    have hdec := List.all_eq_true.mp hall_b prior hmem_p
    have hor := of_decide_eq_true hdec
    omega
  -- Geometric bounds on P and J
  let P := k + i + 3 * r
  let J := fun t => posFn k r i d t + 5 - 2 * t
  have hJ_bounds : ∀ t ∈ records,
      posFn k r i d t + d t = k + i + 3 * (r - t) ∧
      2 * t + 12 ≤ posFn k r i d t ∧
      P - k + 2 ≤ J t ∧ J t + 2 ≤ P - 1 ∧
      J t + 5 * t + d t = P + 5 := by
    intro t ht
    rcases hmem_rec t ht with ⟨hgt, hle, _⟩
    have hdb := hd_bound t (by omega) (by omega)
    have hpos_def : posFn k r i d t = k + i + 3 * (r - t) - d t := rfl
    have hJ_def : J t = posFn k r i d t + 5 - 2 * t := rfl
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  have hJ_anti : ∀ t1 ∈ records, ∀ t2 ∈ records, t1 < t2 → J t2 < J t1 := by
    intro t1 ht1 t2 ht2 hlt
    have h1 := (hJ_bounds t1 ht1).2.2.2.2
    have h2 := (hJ_bounds t2 ht2).2.2.2.2
    rcases hmem_rec t1 ht1 with ⟨hgt1, _, _⟩
    rcases hmem_rec t2 ht2 with ⟨_, _, hprior2⟩
    have hinc := hprior2 t1 (by omega) hlt
    omega
  have hpivot_eq_J : ∀ t, pivotFn k r i d t = J t % k := fun _ => rfl
  have hpivot_lt : ∀ t, pivotFn k r i d t < k := fun t => Nat.mod_lt _ hk0
  have hnodup : (records.map (pivotFn k r i d)).Nodup := by
    rw [List.nodup_map_iff_inj_on hpair_recs.nodup]
    intro t1 ht1 t2 ht2 heq
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hJa := hJ_anti t1 ht1 t2 ht2 hlt
      have hb1 := hJ_bounds t1 ht1
      have hb2 := hJ_bounds t2 ht2
      exact mod_ne_of_lt_add hJa (by omega) heq.symm
    · have hJa := hJ_anti t2 ht2 t1 ht1 hgt
      have hb1 := hJ_bounds t1 ht1
      have hb2 := hJ_bounds t2 ht2
      exact mod_ne_of_lt_add hJa (by omega) heq
  -- Key causal-cone / XOR-linearity lemma for guardFn
  have hguard_xor : ∀ t ∈ records, ∀ s1 s2 : Nat, s1 < 2 ^ k → s2 < 2 ^ k →
      (∀ u, J t + 1 ≤ u → u ≤ P - 1 → s1.testBit (u % k) = s2.testBit (u % k)) →
      xor (guardFn k r i row constant d t s1) (s1.testBit (pivotFn k r i d t)) =
      xor (guardFn k r i row constant d t s2) (s2.testBit (pivotFn k r i d t)) := by
    intro t ht s1 s2 hs1 hs2 hagree
    rcases hmem_rec t ht with ⟨hgt, hle, _⟩
    have hb := hJ_bounds t ht
    set b := posFn k r i d t
    set m0 := t - 2
    have hm0_ge : 3 ≤ m0 := by omega
    have ht1 : t - 1 = m0 + 1 := by omega
    have hstep_eq : ∀ δ, δ ≤ 2 →
        (stepFn k (zFn k row constant m0 s1 ^^^ rotFn k 1 (zFn k row constant m0 s1) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s1))).testBit ((b + δ) % k) =
        (stepFn k (zFn k row constant m0 s2 ^^^ rotFn k 1 (zFn k row constant m0 s2) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s2))).testBit ((b + δ) % k) := by
      intro δ hδ
      apply stepMixed_testBit_eq hk2
        (zFn_lt k row constant m0 s1 hs1) (zFn_lt k row constant m0 s2 hs2) (by omega)
      intro y hy1 hy2
      apply zFn_testBit_eq_of_agree hk2 hs1 hs2 m0 y (by omega)
      intro u hu1 hu2
      have hls : leftShift m0 = 2 * m0 - 3 := by
        unfold leftShift
        by_cases h3 : m0 ≤ 3
        · have : m0 = 3 := by omega
          simp [this]
        · simp [h3]
      rw [hls] at hu1
      apply hagree u (by omega) (by omega)
    have hrk_bit : ∀ s, s < 2 ^ k → ∀ δ,
        (rotFn k (2 * m0) (rotFn k (k - 1) (s ^^^ row.val))).testBit ((b + δ) % k) =
        xor (s.testBit ((J t + δ) % k)) (row.val.testBit ((J t + δ) % k)) := by
      intro s hs δ
      rw [rotFn_testBit_sub hk0 (rotFn_lt k _ _) (by omega),
          rotFn_k_sub_1_testBit hk2 (xor_lt_two_pow' hs row.isLt),
          Nat.testBit_xor]
      have hidx : b + δ - 2 * m0 + 1 = J t + δ := by omega
      rw [hidx]
    have hstep0 :
        (stepFn k (zFn k row constant m0 s1 ^^^ rotFn k 1 (zFn k row constant m0 s1) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s1))).testBit (b % k) =
        (stepFn k (zFn k row constant m0 s2 ^^^ rotFn k 1 (zFn k row constant m0 s2) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s2))).testBit (b % k) := by
      simpa using hstep_eq 0 (by omega)
    have hrk1 :
        (rotFn k (2 * m0) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit ((b + 1) % k) =
        (rotFn k (2 * m0) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit ((b + 1) % k) := by
      rw [hrk_bit s1 hs1 1, hrk_bit s2 hs2 1, hagree (J t + 1) (by omega) (by omega)]
    have hrk2 :
        (rotFn k (2 * m0) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit ((b + 2) % k) =
        (rotFn k (2 * m0) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit ((b + 2) % k) := by
      rw [hrk_bit s1 hs1 2, hrk_bit s2 hs2 2, hagree (J t + 2) (by omega) (by omega)]
    have hrk0_1 :
        (rotFn k (2 * m0) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit (b % k) =
        xor (s1.testBit (pivotFn k r i d t)) (row.val.testBit (pivotFn k r i d t)) := by
      simpa [hpivot_eq_J] using hrk_bit s1 hs1 0
    have hrk0_2 :
        (rotFn k (2 * m0) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit (b % k) =
        xor (s2.testBit (pivotFn k r i d t)) (row.val.testBit (pivotFn k r i d t)) := by
      simpa [hpivot_eq_J] using hrk_bit s2 hs2 0
    unfold guardFn
    dsimp only
    rw [ht1, zFn_succ, zFn_succ]
    dsimp only
    simp only [Nat.testBit_xor]
    change xor (xor (xor (xor (xor
      ((stepFn k (zFn k row constant m0 s1 ^^^ rotFn k 1 (zFn k row constant m0 s1) ^^^
        rotFn k (k - 1) (zFn k row constant m0 s1))).testBit (b % k))
      ((rotFn k (2 * m0) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit (b % k)))
      ((constant (m0 + 1)).val.testBit (b % k)))
      (xor (xor
        ((stepFn k (zFn k row constant m0 s1 ^^^ rotFn k 1 (zFn k row constant m0 s1) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s1))).testBit ((b + 1) % k))
        ((rotFn k (2 * m0) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit ((b + 1) % k)))
        ((constant (m0 + 1)).val.testBit ((b + 1) % k))))
      (xor (xor
        ((stepFn k (zFn k row constant m0 s1 ^^^ rotFn k 1 (zFn k row constant m0 s1) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s1))).testBit ((b + 2) % k))
        ((rotFn k (2 * m0) (rotFn k (k - 1) (s1 ^^^ row.val))).testBit ((b + 2) % k)))
        ((constant (m0 + 1)).val.testBit ((b + 2) % k))))
      (s1.testBit (pivotFn k r i d t)) =
      xor (xor (xor (xor (xor
      ((stepFn k (zFn k row constant m0 s2 ^^^ rotFn k 1 (zFn k row constant m0 s2) ^^^
        rotFn k (k - 1) (zFn k row constant m0 s2))).testBit (b % k))
      ((rotFn k (2 * m0) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit (b % k)))
      ((constant (m0 + 1)).val.testBit (b % k)))
      (xor (xor
        ((stepFn k (zFn k row constant m0 s2 ^^^ rotFn k 1 (zFn k row constant m0 s2) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s2))).testBit ((b + 1) % k))
        ((rotFn k (2 * m0) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit ((b + 1) % k)))
        ((constant (m0 + 1)).val.testBit ((b + 1) % k))))
      (xor (xor
        ((stepFn k (zFn k row constant m0 s2 ^^^ rotFn k 1 (zFn k row constant m0 s2) ^^^
          rotFn k (k - 1) (zFn k row constant m0 s2))).testBit ((b + 2) % k))
        ((rotFn k (2 * m0) (rotFn k (k - 1) (s2 ^^^ row.val))).testBit ((b + 2) % k)))
        ((constant (m0 + 1)).val.testBit ((b + 2) % k))))
      (s2.testBit (pivotFn k r i d t))
    rw [hstep0, hstep_eq 1 (by omega), hstep_eq 2 (by omega),
        hrk1, hrk2, hrk0_1, hrk0_2]
    exact bool_xor_cancel _ _ _ _ _ _ _
  -- Consequences of hguard_xor: flip on pivot toggle, invariance on non-aliasing interval
  have hguard_toggle : ∀ t ∈ records, ∀ s : Nat, s < 2 ^ k →
      guardFn k r i row constant d t (s ^^^ (1 <<< pivotFn k r i d t)) =
      !(guardFn k r i row constant d t s) := by
    intro t ht s hs
    have hs' : s ^^^ (1 <<< pivotFn k r i d t) < 2 ^ k :=
      xor_lt_two_pow' hs (one_shiftLeft_lt_two_pow (hpivot_lt t))
    have hb := hJ_bounds t ht
    have hxor := hguard_xor t ht s (s ^^^ (1 <<< pivotFn k r i d t)) hs hs' (by
      intro u hu1 hu2
      rw [Nat.testBit_xor, testBit_one_shiftLeft]
      have hne : u % k ≠ pivotFn k r i d t := by
        rw [hpivot_eq_J]
        exact (mod_ne_of_lt_add (by omega) (by omega)).symm
      simp [hne])
    rw [Nat.testBit_xor, testBit_one_shiftLeft] at hxor
    simp only [decide_true, Bool.xor_true] at hxor
    cases hg1 : guardFn k r i row constant d t s <;>
    cases hg2 : guardFn k r i row constant d t (s ^^^ (1 <<< pivotFn k r i d t)) <;>
    cases hb0 : s.testBit (pivotFn k r i d t) <;>
    simp [hg1, hg2, hb0] at hxor ⊢
  have hguard_eq_of_ge : ∀ t ∈ records, ∀ s1 s2 : Nat, s1 < 2 ^ k → s2 < 2 ^ k →
      (∀ u, J t ≤ u → u ≤ P - 1 → s1.testBit (u % k) = s2.testBit (u % k)) →
      guardFn k r i row constant d t s1 = guardFn k r i row constant d t s2 := by
    intro t ht s1 s2 hs1 hs2 hagree
    have hb := hJ_bounds t ht
    have hxor := hguard_xor t ht s1 s2 hs1 hs2 (fun u hu1 hu2 => hagree u (by omega) hu2)
    have hp : s1.testBit (pivotFn k r i d t) = s2.testBit (pivotFn k r i d t) :=
      hagree (J t) (by omega) (by omega)
    rw [hp] at hxor
    cases hg1 : guardFn k r i row constant d t s1 <;>
    cases hg2 : guardFn k r i row constant d t s2 <;>
    cases hb0 : s2.testBit (pivotFn k r i d t) <;>
    simp [hg1, hg2, hb0] at hxor ⊢
  -- Forward fold induction on any increasing sublist of records
  have hfold_fwd : ∀ xs : List Nat, xs.Pairwise (· < ·) → (∀ t ∈ xs, t ∈ records) →
      ∀ init : Nat, init < 2 ^ k →
        let res := xs.foldl (decodeStep k r i row constant d) init
        res < 2 ^ k ∧
        (∀ j, j ∉ xs.map (pivotFn k r i d) → res.testBit j = init.testBit j) ∧
        (∀ t ∈ xs, guardFn k r i row constant d t res = false) := by
    intro xs
    induction xs with
    | nil =>
      intro _ _ init hinit
      exact ⟨hinit, fun _ _ => rfl, fun _ h => by cases h⟩
    | cons t rest ih =>
      intro hpair hsub init hinit
      rw [List.pairwise_cons] at hpair
      rcases hpair with ⟨hlt_rest, hpair_rest⟩
      have ht : t ∈ records := hsub t (List.mem_cons_self ..)
      have hsub_rest : ∀ t' ∈ rest, t' ∈ records := fun t' ht' => hsub t' (List.mem_cons_of_mem _ ht')
      let mid := decodeStep k r i row constant d init t
      have hmid_lt : mid < 2 ^ k := by
        unfold mid decodeStep
        split
        · exact xor_lt_two_pow' hinit (one_shiftLeft_lt_two_pow (hpivot_lt t))
        · exact hinit
      have hmid_bit : ∀ j, j ≠ pivotFn k r i d t → mid.testBit j = init.testBit j := by
        intro j hj
        unfold mid decodeStep
        split
        · rw [Nat.testBit_xor, testBit_one_shiftLeft, decide_eq_false hj, Bool.xor_false]
        · rfl
      have hmid_guard : guardFn k r i row constant d t mid = false := by
        unfold mid decodeStep
        cases hg : guardFn k r i row constant d t init
        · simp [hg]
        · simp [hg, hguard_toggle t ht init hinit]
      rcases ih hpair_rest hsub_rest mid hmid_lt with ⟨hres_lt, hres_bit, hres_guard⟩
      refine ⟨hres_lt, ?_, ?_⟩
      · intro j hj
        have hj1 : j ≠ pivotFn k r i d t := by
          intro heq
          exact hj (by simp [heq])
        have hj2 : j ∉ rest.map (pivotFn k r i d) := by
          intro hmem
          exact hj (by simp [hmem])
        exact (hres_bit j hj2).trans (hmid_bit j hj1)
      · intro t' ht'
        rcases List.mem_cons.mp ht' with h_eq | ht_rest
        · subst t'
          rw [← hmid_guard]
          apply hguard_eq_of_ge t ht _ mid hres_lt hmid_lt
          intro u hu1 hu2
          apply hres_bit (u % k)
          intro hmem
          rcases List.mem_map.mp hmem with ⟨t2, ht2_rest, hpiv_eq⟩
          have ht2 : t2 ∈ records := hsub_rest t2 ht2_rest
          have hJlt : J t2 < J t := hJ_anti t ht t2 ht2 (hlt_rest t2 ht2_rest)
          have hb2 := hJ_bounds t2 ht2
          exact mod_ne_of_lt_add (by omega) (by omega) hpiv_eq
        · exact hres_guard t' ht_rest
  -- Backward fold induction (uniqueness)
  have hfold_bwd : ∀ xs : List Nat, xs.Pairwise (· < ·) → (∀ t ∈ xs, t ∈ records) →
      ∀ init target : Nat, init < 2 ^ k → target < 2 ^ k →
        (∀ j, j < k → j ∉ xs.map (pivotFn k r i d) → init.testBit j = target.testBit j) →
        (∀ t ∈ xs, guardFn k r i row constant d t target = false) →
        xs.foldl (decodeStep k r i row constant d) init = target := by
    intro xs
    induction xs with
    | nil =>
      intro _ _ init target hinit htarget hbits _
      simp only [List.foldl_nil]
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hjk : j < k
      · exact hbits j hjk (by simp)
      · rw [testBit_false_of_ge hinit (by omega), testBit_false_of_ge htarget (by omega)]
    | cons t rest ih =>
      intro hpair hsub init target hinit htarget hbits hguards
      rw [List.pairwise_cons] at hpair
      rcases hpair with ⟨hlt_rest, hpair_rest⟩
      have ht : t ∈ records := hsub t (List.mem_cons_self ..)
      have hsub_rest : ∀ t' ∈ rest, t' ∈ records := fun t' ht' => hsub t' (List.mem_cons_of_mem _ ht')
      let mid := decodeStep k r i row constant d init t
      have hmid_lt : mid < 2 ^ k := by
        unfold mid decodeStep
        split
        · exact xor_lt_two_pow' hinit (one_shiftLeft_lt_two_pow (hpivot_lt t))
        · exact hinit
      apply ih hpair_rest hsub_rest mid target hmid_lt htarget
      · intro j hjk hj_rest
        by_cases hjp : j = pivotFn k r i d t
        · subst hjp
          have hagree_right : ∀ u, J t + 1 ≤ u → u ≤ P - 1 →
              init.testBit (u % k) = target.testBit (u % k) := by
            intro u hu1 hu2
            apply hbits (u % k) (Nat.mod_lt u hk0)
            intro hmem
            rcases List.mem_map.mp hmem with ⟨t2, ht2_mem, hpiv_eq⟩
            rcases List.mem_cons.mp ht2_mem with h_eq | ht2_rest
            · subst t2
              have hb := hJ_bounds t ht
              exact mod_ne_of_lt_add (by omega) (by omega) hpiv_eq
            · have ht2 : t2 ∈ records := hsub_rest t2 ht2_rest
              have hJlt : J t2 < J t := hJ_anti t ht t2 ht2 (hlt_rest t2 ht2_rest)
              have hb2 := hJ_bounds t2 ht2
              exact mod_ne_of_lt_add (by omega) (by omega) hpiv_eq
          have hxor := hguard_xor t ht init target hinit htarget hagree_right
          have hgt_false : guardFn k r i row constant d t target = false :=
            hguards t (List.mem_cons_self ..)
          rw [hgt_false, Bool.false_xor] at hxor
          unfold mid decodeStep
          cases hg : guardFn k r i row constant d t init
          · simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hg, Bool.false_xor] at hxor
            exact hxor
          · simp only [↓reduceIte, Nat.testBit_xor, testBit_one_shiftLeft, decide_true, Bool.xor_true]
            rw [hg, Bool.true_xor] at hxor
            exact hxor
        · have hj_all : j ∉ (t :: rest).map (pivotFn k r i d) := by
            simp [hjp, hj_rest]
          have hmid_eq : mid.testBit j = init.testBit j := by
            unfold mid decodeStep
            split
            · rw [Nat.testBit_xor, testBit_one_shiftLeft, decide_eq_false hjp, Bool.xor_false]
            · rfl
          rw [hmid_eq]
          exact hbits j hjk hj_all
      · intro t' ht'
        exact hguards t' (List.mem_cons_of_mem _ ht')
  -- Assemble the three conjuncts
  refine ⟨hlen, hnodup, ?_⟩
  intro seed target hseed
  let init := seed ^^^ (seed &&& hiddenFn k r i d records)
  have hinit_lt : init < 2 ^ k := xor_lt_two_pow' hseed (and_lt_two_pow' hseed)
  have hinit_bit : ∀ j, j ∉ records.map (pivotFn k r i d) → init.testBit j = seed.testBit j := by
    intro j hj
    unfold init
    rw [Nat.testBit_xor, Nat.testBit_and, hiddenFn_testBit, decide_eq_false hj,
        Bool.and_false, Bool.xor_false]
  constructor
  · intro heq
    subst heq
    rcases hfold_fwd records hpair_recs (fun _ h => h) init hinit_lt with ⟨hlt, hbits, hguards⟩
    refine ⟨hlt, ?_, hguards⟩
    intro j hj
    exact ((hbits j.val hj).trans (hinit_bit j.val hj)).symm
  · rintro ⟨htarget, hbits, hguards⟩
    apply hfold_bwd records hpair_recs (fun _ h => h) init target hinit_lt htarget
    · intro j hjk hj
      rw [hinit_bit j hj]
      exact hbits ⟨j, hjk⟩ hj
    · exact hguards

end PEqualNP.Outside.L_meta_25532

theorem PEqualNP.Outside.L_meta_25532 : ∀ (k r e q i : Nat) (row : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (d : Nat → Nat),
  0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r → i < k →
  let cut := e + q + 3
  (∀ t, cut ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) →
  (∀ t, cut < t → t ≤ r → d t ≤ d (t - 1)) →
  let m := r - (3 * e + 2 * q + 2)
  let records := ((List.range (r - e + 1)).filter (fun time =>
    decide (cut < time) && (List.range time).all (fun prior =>
      decide (prior < cut ∨ prior + d prior < time + d time)))).take m
  let pos := fun roundIdx => k + i + 3 * (r - roundIdx) - d roundIdx
  let pivot := fun recordTime => (pos recordTime + 5 - 2 * recordTime) % k
  let rot := fun (s bits : Nat) =>
    ((bits <<< (s % k)) ||| (bits >>> (k - s % k))) % 2 ^ k
  let step := fun (mixed : Nat) =>
    (List.range k).foldl (fun acc place =>
      acc ||| ((xor (mixed.testBit place)
        (!(mixed.testBit ((place + 1) % k)) && mixed.testBit ((place + 2) % k))).toNat <<< place)) 0
  let guard := fun (guardTime start : Nat) =>
    let key := rot (k - 1) (start ^^^ row.val)
    let z := (List.range (guardTime - 1)).foldl (fun prev roundNo =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundNo) key ^^^
        (constant (roundNo + 1)).val) start
    let b := pos guardTime
    xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
      (z.testBit ((b + 2) % k))
  let hidden := records.foldl (fun mask entry => mask ||| (1 <<< pivot entry)) 0
  let decode := fun input => records.foldl (fun trial visit =>
    if guard visit trial then trial ^^^ (1 <<< pivot visit) else trial)
    (input ^^^ (input &&& hidden))
  records.length = m ∧ (records.map pivot).Nodup ∧
  ∀ seed target : Nat, seed < 2 ^ k →
    (decode seed = target ↔ target < 2 ^ k ∧
      (∀ j : Fin k, j.val ∉ records.map pivot →
        seed.testBit j.val = target.testBit j.val) ∧
      ∀ t ∈ records, guard t target = false) :=
  PEqualNP.Outside.L_meta_25532.main_thm
