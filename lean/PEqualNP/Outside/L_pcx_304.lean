import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_304_aux
open PEqualNP.ProofComplexity PEqualNP.Search
def toNat {k : ℕ} (x : Fin k -> Bool) : ℕ :=
  ∑ j : Fin k, (x j).toNat * 2 ^ j.val
def ofNat (k w : ℕ) : Fin k -> Bool :=
  fun j => w.testBit j.val
theorem toNat_lt {k : ℕ} (x : Fin k -> Bool) : toNat x < 2 ^ k := by
  unfold toNat
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have hlt := ih (fun j => x j.castSucc)
    have hle : (x (Fin.last k)).toNat <= 1 := by cases x (Fin.last k) <;> simp
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith [Nat.one_le_pow k 2 (by omega)]
theorem testBit_toNat_aux (k : ℕ) (x : Fin k -> Bool) (i : ℕ) :
    (toNat x).testBit i = if h : i < k then x ⟨i, h⟩ else false := by
  induction k generalizing i with
  | zero =>
    simp [toNat]
  | succ k ih =>
    unfold toNat
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    set lo := ∑ j : Fin k, (x j.castSucc).toNat * 2 ^ j.val
    have hlo : lo < 2 ^ k := toNat_lt (fun j => x j.castSucc)
    have hlo_eq : lo = toNat (fun j : Fin k => x j.castSucc) := rfl
    have hpow2 : ∀ (n m : ℕ), n.testBit m = decide ((n / 2 ^ m) % 2 = 1) := by
      intro n m
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ m) with h | h <;> simp [h]
    by_cases hik : i < k
    · have hlt : i < k + 1 := by omega
      simp only [hlt, ↓reduceDIte]
      have hdiv : (lo + (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ i =
          lo / 2 ^ i + (x (Fin.last k)).toNat * 2 ^ (k - i) := by
        have hk_eq : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
          rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hik)]
        rw [hk_eq, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega))]
      have heven : 2 ∣ (x (Fin.last k)).toNat * 2 ^ (k - i) := by
        have hk2 : 2 ^ (k - i) = 2 ^ (k - i - 1) * 2 := by
          have : k - i = (k - i - 1) + 1 := by omega
          conv_lhs => rw [this, Nat.pow_succ]
        rw [hk2, ← Nat.mul_assoc]; exact dvd_mul_left 2 _
      have hbit_eq : (lo + (x (Fin.last k)).toNat * 2 ^ k).testBit i = lo.testBit i := by
        rw [hpow2, hpow2, hdiv]
        obtain ⟨t, ht⟩ := heven
        rw [ht, Nat.add_mul_mod_self_left]
      rw [hbit_eq, hlo_eq, ih _ i, dite_eq_left hik]
      rfl
    · have hki : k <= i := Nat.not_lt.mp hik
      have hdivk : (lo + (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ k = (x (Fin.last k)).toNat := by
        rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hlo, Nat.zero_add]
      have hdivi : (lo + (x (Fin.last k)).toNat * 2 ^ k) / 2 ^ i =
          (x (Fin.last k)).toNat / 2 ^ (i - k) := by
        have hi_eq : 2 ^ i = 2 ^ k * 2 ^ (i - k) := by
          rw [← Nat.pow_add, Nat.add_sub_of_le hki]
        rw [hi_eq, ← Nat.div_div_eq_div_mul, hdivk]
      have hbit_eq : (lo + (x (Fin.last k)).toNat * 2 ^ k).testBit i =
          ((x (Fin.last k)).toNat).testBit (i - k) := by
        rw [hpow2, hpow2, hdivi]
      rw [hbit_eq]
      by_cases hik1 : i = k
      · subst hik1
        simp only [Nat.lt_succ_self, ↓reduceDIte, Nat.sub_self]
        rw [show (⟨i, Nat.lt_succ_self i⟩ : Fin (i + 1)) = Fin.last i from rfl]
        cases x (Fin.last i) <;> rfl
      · have hnot1 : ¬ i < k + 1 := by omega
        simp only [hnot1, ↓reduceDIte]
        have hpos : 0 < i - k := by omega
        cases x (Fin.last k)
        · simp
        · change (1 : ℕ).testBit (i - k) = false
          cases hd : i - k with
          | zero => omega
          | succ d =>
            rw [hpow2, Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero d))]
            rfl
theorem z43 {k : ℕ} (x : Fin k -> Bool) (i : ℕ) :
    (toNat x).testBit i = if h : i < k then x ⟨i, h⟩ else false :=
  testBit_toNat_aux k x i
theorem z102 {k : ℕ} (x : Fin k -> Bool) (i : Fin k) :
    (toNat x).testBit i.val = x i := by
  rw [z43]; simp [i.isLt]
theorem ofNat_toNat {k : ℕ} (x : Fin k -> Bool) : ofNat k (toNat x) = x := by
  ext i
  exact z102 x i
theorem toNat_inj {k : ℕ} {x y : Fin k -> Bool} (h : toNat x = toNat y) : x = y := by
  have := congrArg (ofNat k) h
  simpa [ofNat_toNat] using this
theorem toNat_ofNat {k w : ℕ} (hw : w < 2 ^ k) : toNat (ofNat k w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [z43]
  by_cases hi : i < k
  · simp [hi, ofNat]
  · simp only [hi, ↓reduceDIte]
    symm
    apply Nat.testBit_lt_two_pow
    calc w < 2 ^ k := hw
      _ <= 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)
theorem mod_two_pow_testBit (w k i : ℕ) :
    (w % 2 ^ k).testBit i = if i < k then w.testBit i else false := by
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < k <;> simp [hi]
theorem testBit_xor_apply (a b : ℕ) (i : ℕ) :
    (a ^^^ b).testBit i = xor (a.testBit i) (b.testBit i) :=
  Nat.testBit_xor a b i
theorem xor_toNat {k : ℕ} (x y : Fin k -> Bool) :
    toNat (fun i => xor (x i) (y i)) = toNat x ^^^ toNat y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [z43, Nat.testBit_xor, z43, z43]
  split <;> simp
theorem testBit_one_ne {p : ℕ} (hp : p ≠ 0) : (1 : ℕ).testBit p = false := by
  cases p with
  | zero => contradiction
  | succ p =>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero p))]
def rotB {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k -> Bool) : Fin k -> Bool :=
  fun i => x ⟨(i.val + k - s % k) % k, Nat.mod_lt _ hk⟩
theorem rot_toNat {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k -> Bool) :
    ((toNat x <<< (s % k)) ||| (toNat x >>> (k - s % k))) % 2 ^ k =
      toNat (rotB hk s x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mod_two_pow_testBit, z43]
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte, ↓reduceDIte, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight]
    set r := s % k
    have hr : r < k := Nat.mod_lt s hk
    by_cases hri : r <= i
    · have hb1 : decide (r <= i) = true := decide_eq_true hri
      have hb2 : (toNat x).testBit (k - r + i) = false := by
        rw [z43]; simp [show ¬ k - r + i < k by omega]
      simp only [hb1, Bool.true_and, hb2, Bool.or_false]
      rw [z43]; simp only [show i - r < k by omega, ↓reduceDIte]
      congr 1; rw [Fin.ext_iff]; dsimp [rotB]
      have : (i + k - r) = k + (i - r) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · have hi_lt : i < r := Nat.not_le.mp hri
      have hb1 : decide (r <= i) = false := decide_eq_false hri
      simp only [hb1, Bool.false_and, Bool.false_or]
      rw [z43]; simp only [show k - r + i < k by omega, ↓reduceDIte]
      congr 1; rw [Fin.ext_iff]; dsimp [rotB]
      have hsub : i + k - r < k := by omega
      rw [Nat.mod_eq_of_lt hsub]; omega
  · simp [hi]
def stepB {k : ℕ} (hk : 0 < k) (x : Fin k -> Bool) : Fin k -> Bool :=
  fun i => xor (x i)
    (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)
theorem step_toNat_aux {k : ℕ} (hk : 0 < k) (x : Fin k -> Bool) (m : ℕ) (hm : m <= k) :
    ((List.range m).foldl (fun acc i =>
      acc ||| ((xor ((toNat x).testBit i)
        (!((toNat x).testBit ((i + 1) % k)) && (toNat x).testBit ((i + 2) % k))).toNat <<< i)) 0) =
    toNat (fun j : Fin k => if j.val < m then stepB hk x j else false) := by
  induction m with
  | zero =>
    simp [toNat]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (by omega)]
    set lhs_prev := toNat (fun j : Fin k => if j.val < m then stepB hk x j else false)
    have hbit : ∀ i,
        (lhs_prev ||| ((xor ((toNat x).testBit m)
          (!((toNat x).testBit ((m + 1) % k)) && (toNat x).testBit ((m + 2) % k))).toNat <<< m)).testBit i =
        (toNat (fun j : Fin k => if j.val < m + 1 then stepB hk x j else false)).testBit i := by
      intro i
      rw [Nat.testBit_or, Nat.testBit_shiftLeft]
      rw [show (toNat x).testBit m = x ⟨m, by omega⟩ from by rw [z43]; simp [show m < k by omega]]
      rw [show (toNat x).testBit ((m + 1) % k) = x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩ from by
        rw [z43]; simp [Nat.mod_lt _ hk]]
      rw [show (toNat x).testBit ((m + 2) % k) = x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩ from by
        rw [z43]; simp [Nat.mod_lt _ hk]]
      by_cases hik : i < k
      · rw [z43, z43]; simp only [hik, ↓reduceDIte]
        by_cases him : i < m
        · have hnm : ¬ m <= i := by omega
          have him1 : i < m + 1 := by omega
          simp [him, him1, hnm]
        · by_cases heq : i = m
          · subst heq
            have hnm : ¬ i < i := Nat.lt_irrefl i
            have hi1 : i < i + 1 := Nat.lt_succ_self i
            simp only [hnm, ↓reduceIte, Bool.false_or, le_refl, decide_true, Bool.true_and,
              Nat.sub_self, hi1]
            change (xor (x ⟨i, hik⟩) (!(x ⟨(i + 1) % k, Nat.mod_lt _ hk⟩) &&
              x ⟨(i + 2) % k, Nat.mod_lt _ hk⟩)).toNat.testBit 0 = stepB hk x ⟨i, hik⟩
            dsimp [stepB]
            cases x ⟨i, hik⟩ <;> cases x ⟨(i + 1) % k, Nat.mod_lt _ hk⟩ <;>
              cases x ⟨(i + 2) % k, Nat.mod_lt _ hk⟩ <;> rfl
          · have hlt : m < i := by omega
            have hnm1 : ¬ i < m + 1 := by omega
            have hmi : m <= i := by omega
            have hpos : i - m ≠ 0 := by omega
            simp only [him, hnm1, ↓reduceIte, Bool.false_or, hmi, decide_true, Bool.true_and]
            cases xor (x ⟨m, by omega⟩) (!(x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩)
            · simp
            · change (1 : ℕ).testBit (i - m) = false; exact testBit_one_ne hpos
      · have hmi : m <= i := by omega
        have hlt_pow : lhs_prev < 2 ^ i := by
          calc lhs_prev < 2 ^ k := toNat_lt _
            _ <= 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hik)
        rw [Nat.testBit_lt_two_pow hlt_pow, z43]; simp only [hik, ↓reduceDIte]
        simp only [Bool.false_or, hmi, decide_true, Bool.true_and]
        have hpos : i - m ≠ 0 := by omega
        cases xor (x ⟨m, by omega⟩) (!(x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩)
        · simp
        · change (1 : ℕ).testBit (i - m) = false; exact testBit_one_ne hpos
    exact Nat.eq_of_testBit_eq hbit
theorem step_toNat {k : ℕ} (hk : 0 < k) (x : Fin k -> Bool) :
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor ((toNat x).testBit i)
        (!((toNat x).testBit ((i + 1) % k)) && (toNat x).testBit ((i + 2) % k))).toNat <<< i)) 0 =
    toNat (stepB hk x) := by
  rw [step_toNat_aux hk x k (le_refl k)]
  congr 1; ext j; simp [j.isLt]
def mixB {k : ℕ} (hk : 0 < k) (δ : ℕ) (x : Fin k -> Bool) : Fin k -> Bool :=
  fun i => xor (xor (x i) (rotB hk δ x i)) (rotB hk (k - δ % k) x i)
theorem mixB_toNat {k : ℕ} (hk : 0 < k) (δ : ℕ) (x : Fin k -> Bool) :
    toNat x ^^^ ((toNat x <<< (δ % k)) ||| (toNat x >>> (k - δ % k))) % 2 ^ k ^^^
      ((toNat x <<< ((k - δ % k) % k)) ||| (toNat x >>> (k - (k - δ % k) % k))) % 2 ^ k =
    toNat (mixB hk δ x) := by
  rw [rot_toNat hk δ x, rot_toNat hk (k - δ % k) x, ← xor_toNat, ← xor_toNat]
  rfl
def affId : Bool × Bool := (true, false)
def affComp (f g : Bool × Bool) : Bool × Bool :=
  (f.1 && g.1, xor f.2 (f.1 && g.2))
theorem z106 (f g h : Bool × Bool) :
    affComp (affComp f g) h = affComp f (affComp g h) := by
  rcases f with ⟨a1, b1⟩; rcases g with ⟨a2, b2⟩; rcases h with ⟨a3, b3⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl
theorem z56 (f : Bool × Bool) : affComp affId f = f := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> rfl
theorem z111 (f : Bool × Bool) : affComp f affId = f := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> rfl
def affEval (f : Bool × Bool) (t : Bool) : Bool :=
  xor f.2 (f.1 && t)
theorem affEval_comp (f g : Bool × Bool) (t : Bool) :
    affEval (affComp f g) t = affEval f (affEval g t) := by
  rcases f with ⟨a1, b1⟩; rcases g with ⟨a2, b2⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases t <;> rfl
def z21 (k p : ℕ) (hk : 0 < k) : Fin k :=
  ⟨(2 * p) % k, Nat.mod_lt _ hk⟩
theorem odd_div_two_mul (_hk : 0 < k) (hk_odd : k % 2 = 1) (p : ℕ) :
    (2 * ((p * ((k + 1) / 2)) % k)) % k = p % k := by
  have h2k : 2 * ((k + 1) / 2) = k + 1 := Nat.mul_div_cancel' (by omega : 2 ∣ k + 1)
  calc (2 * ((p * ((k + 1) / 2)) % k)) % k
      = (2 * (p * ((k + 1) / 2))) % k := Nat.mul_mod_mod 2 (p * ((k + 1) / 2)) k
    _ = (p * (2 * ((k + 1) / 2))) % k := by ring_nf
    _ = (p * (k + 1)) % k := by rw [h2k]
    _ = (p * k + p) % k := by ring_nf
    _ = p % k := by rw [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
def z19 (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val * ((k + 1) / 2)) % k, Nat.mod_lt _ hk⟩
theorem stride2_right_inv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (i : Fin k) :
    z21 k (z19 k hk i).val hk = i := by
  ext; dsimp [z21, z19]
  rw [odd_div_two_mul hk hk_odd i.val, Nat.mod_eq_of_lt i.isLt]
theorem stride2_left_inv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (p : Fin k) :
    z19 k hk (z21 k p.val hk) = p := by
  ext; dsimp [z21, z19]
  have h1 : ((2 * p.val) % k * ((k + 1) / 2)) % k = (p.val * (2 * ((k + 1) / 2))) % k := by
    rw [Nat.mod_mul_mod]; ring_nf
  have h2k : 2 * ((k + 1) / 2) = k + 1 := by omega
  rw [h1, h2k, show p.val * (k + 1) = p.val * k + p.val by ring, Nat.add_mod, Nat.mul_mod_left,
    Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt p.isLt]
def chiMapAt {k : ℕ} (hk : 0 < k) (y : Fin k -> Bool) (p : Fin k) : Bool × Bool :=
  let i := z21 k p.val hk
  (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩), y i)
def chiList {k : ℕ} (hk : 0 < k) (y : Fin k -> Bool) : List (Bool × Bool) :=
  List.ofFn (chiMapAt hk y)
def invChiAt {k : ℕ} (hk : 0 < k) (y : Fin k -> Bool) (p : Fin k) : Bool :=
  let hs := chiList hk y
  let pref := (hs.take p.val).foldl affComp affId
  let suf := (hs.drop p.val).foldr affComp affId
  (affComp suf pref).2
def invChiB {k : ℕ} (hk : 0 < k) (y : Fin k -> Bool) : Fin k -> Bool :=
  fun i => invChiAt hk y (z19 k hk i)
theorem foldr_affComp_drop (l : List (Bool × Bool)) (p : ℕ) (hp : p < l.length) :
    (l.drop p).foldr affComp affId = affComp l[p] ((l.drop (p + 1)).foldr affComp affId) := by
  rw [List.drop_eq_getElem_cons hp, List.foldr_cons]
theorem foldl_affComp_take_succ (l : List (Bool × Bool)) (p : ℕ) (hp : p < l.length) :
    (l.take (p + 1)).foldl affComp affId = affComp ((l.take p).foldl affComp affId) l[p] := by
  rw [List.take_succ_eq_append_getElem hp, List.foldl_append, List.foldl_cons, List.foldl_nil]
theorem z118 (l : List (Bool × Bool)) (init : Bool × Bool) :
    l.foldl affComp init = affComp init (l.foldr affComp affId) := by
  induction l generalizing init with
  | nil => simp [z111]
  | cons a t ih =>
    simp only [List.foldl_cons, List.foldr_cons]
    rw [ih (affComp init a), z106]
theorem z152 (l : List (Bool × Bool)) (p : ℕ) :
    affComp ((l.take p).foldl affComp affId) ((l.drop p).foldr affComp affId) =
      l.foldr affComp affId := by
  rw [z118, z56]
  induction p generalizing l with
  | zero => simp [z56]
  | succ p ih =>
    cases l with
    | nil => simp [z56]
    | cons a t =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.foldr_cons]
      rw [z106, ih t]
theorem affComp_fst_eq_all (l : List (Bool × Bool)) :
    (l.foldr affComp affId).1 = l.all (fun x => x.1) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons, affComp, List.all_cons, ih]
theorem step_stepB_key (x y : Fin k -> Bool) (hk : 0 < k) (hy : y = stepB hk x) (i : Fin k) :
    (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) =
    (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) := by
  subst hy
  set i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
  set i2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
  have h12 : (⟨(i1.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = i2 := by
    rw [Fin.ext_iff]; dsimp [i1, i2]; rw [Nat.mod_add_mod]
  change (!(x i1) && x i2) = (!(stepB hk x i1) && x i2)
  dsimp [stepB]
  rw [h12]
  cases x i1 <;> cases x i2 <;> cases x ⟨(i1.val + 2) % k, Nat.mod_lt _ hk⟩ <;> rfl
theorem stepB_zero_eq {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (x : Fin k -> Bool)
    (h : stepB hk x = fun _ => false) : x = fun _ => false := by
  have hrel : ∀ i : Fin k, x i = (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
      x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) := by
    intro i
    have hi := congrFun h i
    dsimp [stepB] at hi
    cases hx : x i <;> cases hb : (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
      x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)
    · rfl
    · rw [hx, hb] at hi; exact absurd hi (by decide)
    · rw [hx, hb] at hi; exact absurd hi (by decide)
    · rfl
  by_contra hne
  have hex : ∃ i, x i = true := by
    by_contra hall
    apply hne; ext i; cases hx : x i with
    | false => rfl
    | true => exact False.elim (hall ⟨i, hx⟩)
  obtain ⟨i0, hi0⟩ := hex
  have haltern : ∀ n : ℕ,
      x ⟨(i0.val + 2 * n) % k, Nat.mod_lt _ hk⟩ = true /\
      x ⟨(i0.val + 2 * n + 1) % k, Nat.mod_lt _ hk⟩ = false := by
    intro n
    induction n with
    | zero =>
      have hi0' : x ⟨i0.val % k, Nat.mod_lt _ hk⟩ = true := by
        have hfin : (⟨i0.val % k, Nat.mod_lt _ hk⟩ : Fin k) = i0 := Fin.ext (Nat.mod_eq_of_lt i0.isLt)
        rw [hfin]; exact hi0
      have hr := hrel ⟨i0.val % k, Nat.mod_lt _ hk⟩
      rw [hi0'] at hr
      have hfin1 : (⟨((i0.val % k) + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩ := by rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]
      change true = (!(x ⟨((i0.val % k) + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨((i0.val % k) + 2) % k, Nat.mod_lt _ hk⟩) at hr
      rw [hfin1] at hr
      have hfalse : x ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩ = false := by
        cases hc : x ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩ with
        | false => rfl
        | true => rw [hc] at hr; simp at hr
      exact ⟨by simpa using hi0', hfalse⟩
    | succ n ih =>
      obtain ⟨ht, hf⟩ := ih
      have hr := hrel ⟨(i0.val + 2 * n) % k, Nat.mod_lt _ hk⟩
      rw [ht] at hr
      have h2n1 : (⟨((i0.val + 2 * n) % k + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 2 * n + 1) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]
      have h2n2 : (⟨((i0.val + 2 * n) % k + 2) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]; ring_nf
      change true = (!(x ⟨((i0.val + 2 * n) % k + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨((i0.val + 2 * n) % k + 2) % k, Nat.mod_lt _ hk⟩) at hr
      rw [h2n1, h2n2, hf] at hr
      have h2 : x ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩ = true := by
        cases hc : x ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩ with
        | true => rfl
        | false => rw [hc] at hr; simp at hr
      have hr2 := hrel ⟨(i0.val + 2 * (n + 1)) % k, Nat.mod_lt _ hk⟩
      rw [h2] at hr2
      have hmod2 : (⟨((i0.val + 2 * (n + 1)) % k + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(i0.val + 2 * (n + 1) + 1) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]
      change true = (!(x ⟨((i0.val + 2 * (n + 1)) % k + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨((i0.val + 2 * (n + 1)) % k + 2) % k, Nat.mod_lt _ hk⟩) at hr2
      rw [hmod2] at hr2
      have hf2 : x ⟨(i0.val + 2 * (n + 1) + 1) % k, Nat.mod_lt _ hk⟩ = false := by
        cases hc : x ⟨(i0.val + 2 * (n + 1) + 1) % k, Nat.mod_lt _ hk⟩ with
        | false => rfl
        | true => rw [hc] at hr2; simp at hr2
      exact ⟨h2, hf2⟩
  have hk2 := haltern ((k - 1) / 2)
  have heq_idx : (⟨(i0.val + 2 * ((k - 1) / 2) + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = i0 := by
    rw [Fin.ext_iff]; dsimp
    have : 2 * ((k - 1) / 2) + 1 = k := by omega
    rw [Nat.add_assoc, this, Nat.add_mod_right, Nat.mod_eq_of_lt i0.isLt]
  rw [heq_idx, hi0] at hk2
  exact absurd hk2.2 (by decide)
theorem invChiB_zero {k : ℕ} (hk : 0 < k) (y : Fin k -> Bool) (hy : ∀ q : Fin k, y q = false) :
    invChiB hk y = fun _ => false := by
  ext i
  dsimp [invChiB, invChiAt]
  have hs_snd : ∀ g ∈ chiList hk y, g.2 = false := by
    intro g hg
    simp only [chiList, List.mem_ofFn] at hg
    obtain ⟨p, rfl⟩ := hg
    exact hy _
  have htake : ∀ n (l : List (Bool × Bool)), (∀ g ∈ l, g.2 = false) ->
      ((l.take n).foldl affComp affId).2 = false := by
    intro n l hl
    have hfold : ∀ (ll : List (Bool × Bool)) (init : Bool × Bool),
        init.2 = false -> (∀ g ∈ ll, g.2 = false) -> (ll.foldl affComp init).2 = false := by
      intro ll
      induction ll with
      | nil => intro init h _; exact h
      | cons a t ih =>
        intro init h1 h2
        apply ih
        · dsimp [affComp]; simp [h1, h2 a List.mem_cons_self]
        · intro g hg; exact h2 g (List.mem_cons_of_mem _ hg)
    exact hfold _ _ rfl (fun g hg => hl g (List.mem_of_mem_take hg))
  have hdrop : ∀ n (l : List (Bool × Bool)), (∀ g ∈ l, g.2 = false) ->
      ((l.drop n).foldr affComp affId).2 = false := by
    intro n l hl
    have hfold : ∀ (ll : List (Bool × Bool)),
        (∀ g ∈ ll, g.2 = false) -> (ll.foldr affComp affId).2 = false := by
      intro ll
      induction ll with
      | nil => intro _; rfl
      | cons a t ih =>
        intro h2
        dsimp [affComp]
        simp [h2 a List.mem_cons_self, ih (fun g hg => h2 g (List.mem_cons_of_mem _ hg))]
    exact hfold _ (fun g hg => hl g (List.mem_of_mem_drop hg))
  dsimp [affComp]
  rw [hdrop _ _ hs_snd, htake _ _ hs_snd]
  simp
theorem foldr_affComp_append (l1 l2 : List (Bool × Bool)) :
    (l1 ++ l2).foldr affComp affId =
      affComp (l1.foldr affComp affId) (l2.foldr affComp affId) := by
  induction l1 with
  | nil => simp [z56]
  | cons a t ih =>
    simp only [List.cons_append, List.foldr_cons, ih, z106]
theorem z144 {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (x : Fin k -> Bool) :
    invChiB hk (stepB hk x) = x := by
  by_cases hy : ∃ q : Fin k, stepB hk x q = true
  · set y := stepB hk x
    have hstep_rec : ∀ p : Fin k, x (z21 k p.val hk) =
        affEval (chiMapAt hk y p) (x (z21 k (⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk)) := by
      intro p
      set i := z21 k p.val hk
      have hi2 : z21 k (⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk =
          ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp [z21, i]
        rw [Nat.mul_mod_mod, show 2 * (p.val + 1) = 2 * p.val + 2 by ring,
          Nat.add_mod (2 * p.val % k), Nat.mod_mod, ← Nat.add_mod]
      rw [hi2]
      dsimp [affEval, chiMapAt]
      have hk_key := step_stepB_key x y hk rfl i
      have hb_eq : (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
          x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) =
          (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
          x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) := hk_key.symm
      change x i = xor (y i) (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)
      rw [hb_eq]
      dsimp [y, stepB]
      cases x i <;> cases (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) &&
        x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) <;> rfl
    have hiter : ∀ (n : ℕ) (p : Fin k),
        x (z21 k p.val hk) =
        affEval (((List.range n).map (fun d =>
          chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩)).foldr affComp affId)
          (x (z21 k (⟨(p.val + n) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk)) := by
      intro n
      induction n with
      | zero =>
        intro p
        have hp0 : (⟨(p.val + 0) % k, Nat.mod_lt _ hk⟩ : Fin k) = p := by
          rw [Fin.ext_iff]; dsimp; exact Nat.mod_eq_of_lt p.isLt
        rw [hp0, List.range_zero, List.map_nil, List.foldr_nil]
        simp [affEval, affId]
      | succ n ih =>
        intro p
        rw [hstep_rec p, ih ⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩]
        have hmod : (⟨((p.val + 1) % k + n) % k, Nat.mod_lt _ hk⟩ : Fin k) =
            ⟨(p.val + (n + 1)) % k, Nat.mod_lt _ hk⟩ := by
          rw [Fin.ext_iff]; dsimp; rw [Nat.mod_add_mod]; ring_nf
        rw [hmod, List.range_succ_eq_map, List.map_cons, List.map_map, List.foldr_cons, affEval_comp]
        congr 2
        · simp [Nat.mod_eq_of_lt p.isLt]
        · congr 1
          apply List.map_congr_left
          intro d _
          congr 1; rw [Fin.ext_iff]; dsimp [Function.comp]
          rw [Nat.mod_add_mod, Nat.add_assoc, Nat.add_comm 1 d]
    ext i
    set p := z19 k hk i
    have hi_eq : z21 k p.val hk = i := stride2_right_inv hk hk_odd i
    have hk_eq := hiter k p
    have hwrap : (⟨(p.val + k) % k, Nat.mod_lt _ hk⟩ : Fin k) = p := by
      rw [Fin.ext_iff]; dsimp; rw [Nat.add_mod_right, Nat.mod_eq_of_lt p.isLt]
    rw [hwrap, hi_eq] at hk_eq
    set hs := chiList hk y
    have hlen : hs.length = k := List.length_ofFn
    have hcyc_list : (List.range k).map (fun d =>
        chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩) =
        hs.drop p.val ++ hs.take p.val := by
      apply List.ext_getElem
      · simp [hlen]
      · intro d hd1 hd2
        simp only [List.getElem_map, List.getElem_range]
        by_cases hdk : d < k - p.val
        · have hd_drop : d < (hs.drop p.val).length := by simp [hlen]; omega
          rw [List.getElem_append_left hd_drop, List.getElem_drop]
          have hpd : p.val + d < k := by omega
          have hpd_len : p.val + d < hs.length := by rw [hlen]; exact hpd
          have hget : hs[p.val + d]'hpd_len = chiMapAt hk y ⟨p.val + d, hpd⟩ := by
            simp [hs, chiList]
          rw [hget]
          congr 1; rw [Fin.ext_iff]; dsimp; exact Nat.mod_eq_of_lt hpd
        · have hd_drop : ¬ d < (hs.drop p.val).length := by simp [hlen]; omega
          rw [List.getElem_append_right (Nat.not_lt.mp hd_drop), List.getElem_take]
          have hlen_drop : (hs.drop p.val).length = k - p.val := by simp [hlen]
          have hidx : d - (k - p.val) < k := by simp at hd1; omega
          have hidx' : d - (hs.drop p.val).length < k := by rw [hlen_drop]; exact hidx
          have hidx_len : d - (hs.drop p.val).length < hs.length := by rw [hlen]; exact hidx'
          have hget : hs[d - (hs.drop p.val).length]'hidx_len =
              chiMapAt hk y ⟨d - (hs.drop p.val).length, hidx'⟩ := by
            simp [hs, chiList]
          rw [hget]
          congr 1; rw [Fin.ext_iff]; dsimp
          rw [hlen_drop]
          have : p.val + d = k + (d - (k - p.val)) := by omega
          rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hidx]
    have hcyc : ((List.range k).map (fun d =>
        chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩)).foldr affComp affId =
        affComp ((hs.drop p.val).foldr affComp affId) ((hs.take p.val).foldl affComp affId) := by
      rw [hcyc_list, foldr_affComp_append]
      congr 1
      rw [z118, z56]
    set M_p := affComp ((hs.drop p.val).foldr affComp affId) ((hs.take p.val).foldl affComp affId)
    have hMp_fst : M_p.1 = false := by
      have h1 : M_p.1 = (((hs.take p.val).foldl affComp affId).1 &&
          ((hs.drop p.val).foldr affComp affId).1) :=
        Bool.and_comm _ _
      have heq := congrArg Prod.fst (z152 hs p.val)
      have hall : (hs.foldr affComp affId).1 = false := by
        rw [affComp_fst_eq_all]
        obtain ⟨q, hq⟩ := hy
        let q1 : Fin k := ⟨(q.val + k - 1) % k, Nat.mod_lt _ hk⟩
        let r := z19 k hk q1
        have hr : (chiMapAt hk y r).1 = false := by
          dsimp [chiMapAt, r]
          have hst : (z21 k (z19 k hk q1).val hk).val = q1.val :=
            congrArg Fin.val (stride2_right_inv hk hk_odd q1)
          have hmod : (q1.val + 1) % k = q.val := by
            dsimp [q1]; rw [Nat.mod_add_mod]
            have : q.val + k - 1 + 1 = q.val + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]
          have hfin : (⟨((z21 k (z19 k hk q1).val hk).val + 1) % k,
              Nat.mod_lt _ hk⟩ : Fin k) = q := by
            rw [Fin.ext_iff]; dsimp; rw [hst, hmod]
          rw [hfin, hq]; rfl
        cases htrue : hs.all (fun x => x.1) with
        | false => rfl
        | true =>
          have hmem : chiMapAt hk y r ∈ hs := by
            simp only [hs, chiList, List.mem_ofFn]; exact ⟨r, rfl⟩
          have := List.all_eq_true.mp htrue _ hmem
          rw [hr] at this; exact absurd this (by decide)
      rw [h1]
      exact heq.trans hall
    rw [hcyc] at hk_eq
    have hev : affEval M_p (x i) = M_p.2 := by
      dsimp [affEval]; rw [hMp_fst]; simp
    rw [hk_eq, hev]
    rfl
  · have hy0 : ∀ q : Fin k, stepB hk x q = false := by
      intro q; cases hq : stepB hk x q with
      | false => rfl
      | true => exact False.elim (hy ⟨q, hq⟩)
    have hx0 := stepB_zero_eq hk hk_odd x (funext hy0)
    rw [invChiB_zero hk _ hy0, hx0]
theorem stepB_invChiB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (y : Fin k -> Bool) :
    stepB hk (invChiB hk y) = y := by
  have hinj : Function.Injective (stepB hk) :=
    Function.LeftInverse.injective (z144 hk hk_odd)
  have hsurj : Function.Surjective (stepB hk) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj y
  rw [z144 hk hk_odd]
def inv3Pos (k : ℕ) : ℕ :=
  if k % 6 = 1 then 4 * (k / 6) + 1 else 2 * (k / 6) + 2
def z109 (k δ : ℕ) : ℕ :=
  if δ = 1 then inv3Pos k else (inv3Pos k * ((k + 1) / 2)) % k
theorem inv3dConst_spec {k δ : ℕ} (hk6 : k % 6 = 1 \/ k % 6 = 5) (hk5 : 5 <= k)
    (hδ : δ = 1 \/ δ = 2) :
    (3 * δ * z109 k δ) % k = 1 := by
  have hpos : (3 * inv3Pos k) % k = 1 := by
    dsimp [inv3Pos]
    rcases hk6 with h1 | h5
    · simp only [h1, ↓reduceIte]
      have hq : k = 6 * (k / 6) + 1 := by omega
      have : 3 * (4 * (k / 6) + 1) = 2 * k + 1 := by omega
      rw [this, Nat.add_mod, show 2 * k % k = 0 from Nat.mul_mod_left 2 k, Nat.zero_add,
        Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
    · have hne1 : k % 6 ≠ 1 := by omega
      rw [if_neg hne1]
      have hq : k = 6 * (k / 6) + 5 := by omega
      have : 3 * (2 * (k / 6) + 2) = k + 1 := by omega
      rw [this, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  rcases hδ with rfl | rfl
  · simpa [z109] using hpos
  · simp only [z109, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
    have h2 : 2 * ((k + 1) / 2) = k + 1 := Nat.mul_div_cancel' (by omega : 2 ∣ k + 1)
    calc (3 * 2 * ((inv3Pos k * ((k + 1) / 2)) % k)) % k
        = (3 * 2 * (inv3Pos k * ((k + 1) / 2))) % k := Nat.mul_mod_mod _ _ k
      _ = ((3 * inv3Pos k) * (2 * ((k + 1) / 2))) % k := by ring_nf
      _ = ((3 * inv3Pos k) * (k + 1)) % k := by rw [h2]
      _ = (((3 * inv3Pos k) % k) * ((k + 1) % k)) % k := Nat.mul_mod _ _ k
      _ = (1 * (1 % k)) % k := by
        rw [hpos]
        have hk1 : (k + 1) % k = 1 % k := by rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod]
        rw [hk1]
      _ = 1 := by rw [Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
def m3dIdx (k δ p : ℕ) (hk : 0 < k) : Fin k :=
  ⟨(3 * δ * p) % k, Nat.mod_lt _ hk⟩
def m3dInv (k δ : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val * z109 k δ) % k, Nat.mod_lt _ hk⟩
theorem m3d_right_inv {k δ : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 \/ k % 6 = 5) (hk5 : 5 <= k)
    (hδ : δ = 1 \/ δ = 2) (i : Fin k) :
    m3dIdx k δ (m3dInv k δ hk i).val hk = i := by
  ext; dsimp [m3dIdx, m3dInv]
  calc (3 * δ * ((i.val * z109 k δ) % k)) % k
      = (3 * δ * (i.val * z109 k δ)) % k := Nat.mul_mod_mod _ _ k
    _ = (i.val * (3 * δ * z109 k δ)) % k := by ring_nf
    _ = ((i.val % k) * ((3 * δ * z109 k δ) % k)) % k := Nat.mul_mod _ _ k
    _ = (i.val % k * 1) % k := by rw [inv3dConst_spec hk6 hk5 hδ]
    _ = i.val := by rw [Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]
def mixDiffAt {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (p : Fin k) : Bool :=
  xor (y ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩)
      (y ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩)
def mixPref {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (p : ℕ) : Bool :=
  ((List.range p).map (fun j => mixDiffAt hk δ y ⟨j % k, Nat.mod_lt _ hk⟩)).foldl xor false
def invMixB {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) : Fin k -> Bool :=
  if k < 5 then y
  else
    let pPos : ℕ := inv3Pos k % k
    let pNeg : ℕ := (k - pPos) % k
    let x0 : Bool := xor (xor (y ⟨0, hk⟩) (mixPref hk δ y pPos)) (mixPref hk δ y pNeg)
    fun i => xor x0 (mixPref hk δ y (m3dInv k δ hk i).val)
theorem mixPref_succ {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (p : ℕ) :
    mixPref hk δ y (p + 1) = xor (mixPref hk δ y p) (mixDiffAt hk δ y ⟨p % k, Nat.mod_lt _ hk⟩) := by
  dsimp [mixPref]
  rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
theorem mixB_one {k : ℕ} (hk : 0 < k) (hk1 : k = 1) (δ : ℕ) (x : Fin k -> Bool) :
    mixB hk δ x = x := by
  subst hk1
  ext i
  have hi : i = ⟨0, hk⟩ := Fin.ext (by omega)
  subst hi
  dsimp [mixB, rotB]
  have h0 : ∀ a : ℕ, (⟨a % 1, Nat.mod_lt _ hk⟩ : Fin 1) = ⟨0, hk⟩ := fun a => Fin.ext (Nat.mod_one a)
  rw [h0, h0]
  cases h : x ⟨0, hk⟩ <;> simp [h]
theorem invMixB_mixB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 \/ k % 6 = 5)
    (δ : ℕ) (hδ : δ = 1 \/ δ = 2) (x : Fin k -> Bool) :
    invMixB hk δ (mixB hk δ x) = x := by
  by_cases hk5 : k < 5
  · have hk1 : k = 1 := by omega
    dsimp [invMixB]
    simp only [hk5, ↓reduceIte]
    exact mixB_one hk hk1 δ x
  · have h5 : 5 <= k := Nat.not_lt.mp hk5
    have hδk : δ % k = δ := Nat.mod_eq_of_lt (by omega)
    have hdiff : ∀ p : ℕ, mixDiffAt hk δ (mixB hk δ x) ⟨p % k, Nat.mod_lt _ hk⟩ =
        xor (x (m3dIdx k δ p hk)) (x (m3dIdx k δ (p + 1) hk)) := by
      intro p
      dsimp [mixDiffAt, mixB, rotB, m3dIdx]
      have hmod_p : (3 * δ * (p % k)) % k = (3 * δ * p) % k := Nat.mul_mod_mod _ _ k
      have h0 : ∀ s t : ℕ, ((s % k) + k - t % k) % k = (s + k - t % k) % k := by
        intro s t
        have htm : t % k < k := Nat.mod_lt t hk
        rw [Nat.add_sub_assoc (by omega), Nat.mod_add_mod, ← Nat.add_sub_assoc (by omega)]
      have hkmd : (k - δ) % k = k - δ := Nat.mod_eq_of_lt (by omega)
      have h_i1 : (⟨((3 * δ * (p % k) + δ) % k + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk]
        rw [show 3 * δ * (p % k) + δ + k - δ = 3 * δ * (p % k) + k by omega]
        rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]; exact hmod_p
      have h_i2 : (⟨((3 * δ * (p % k) + δ) % k + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk, hkmd]
        have : 3 * δ * (p % k) + δ + k - (k - δ) = (3 * δ * (p % k) + 2 * δ) := by omega
        rw [this, Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_i3 : (⟨((3 * δ * (p % k) + 2 * δ) % k + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk]
        have : 3 * δ * (p % k) + 2 * δ + k - δ = k + (3 * δ * (p % k) + δ) := by omega
        rw [this, Nat.add_mod_left, Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_i4 : (⟨((3 * δ * (p % k) + 2 * δ) % k + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * (p + 1)) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [h0, hδk, hkmd]
        have : 3 * δ * (p % k) + 2 * δ + k - (k - δ) = 3 * δ * (p % k) + 3 * δ := by omega
        rw [this, show 3 * δ * (p % k) + 3 * δ = 3 * δ * ((p % k) + 1) by ring,
          show 3 * δ * (p + 1) = 3 * δ * p + 3 * δ by ring]
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_j1 : (⟨(3 * δ * (p % k) + δ) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      have h_j2 : (⟨(3 * δ * (p % k) + 2 * δ) % k, Nat.mod_lt _ hk⟩ : Fin k) =
          ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.add_mod, Nat.mul_mod_mod, ← Nat.add_mod]
      rw [h_i1, h_i2, h_i3, h_i4, h_j1, h_j2]
      cases x ⟨(3 * δ * p) % k, Nat.mod_lt _ hk⟩ <;>
        cases x ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩ <;>
        cases x ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩ <;>
        cases x ⟨(3 * δ * (p + 1)) % k, Nat.mod_lt _ hk⟩ <;> rfl
    have hpref : ∀ p : ℕ, mixPref hk δ (mixB hk δ x) p =
        xor (x ⟨0, hk⟩) (x (m3dIdx k δ p hk)) := by
      intro p
      induction p with
      | zero =>
        simp [mixPref, m3dIdx]
      | succ p ih =>
        rw [mixPref_succ, ih, hdiff p]
        cases x ⟨0, hk⟩ <;> cases x (m3dIdx k δ p hk) <;> cases x (m3dIdx k δ (p + 1) hk) <;> rfl
    have hpPos : (3 * δ * (inv3Pos k % k)) % k = δ := by
      have h3p : (3 * inv3Pos k) % k = 1 := by
        have := inv3dConst_spec hk6 h5 (Or.inl rfl)
        simpa [z109] using this
      calc (3 * δ * (inv3Pos k % k)) % k
          = (3 * δ * inv3Pos k) % k := Nat.mul_mod_mod _ _ k
        _ = (δ * (3 * inv3Pos k)) % k := by ring_nf
        _ = ((δ % k) * ((3 * inv3Pos k) % k)) % k := Nat.mul_mod _ _ k
        _ = δ := by rw [h3p, hδk, Nat.mul_one, Nat.mod_eq_of_lt (by omega)]
    have hpNeg : (3 * δ * ((k - inv3Pos k % k) % k)) % k = k - δ := by
      have hp_lt : inv3Pos k % k < k := Nat.mod_lt _ hk
      have hp_pos_ne : 0 < inv3Pos k % k := by
        by_contra hle
        have h0 : inv3Pos k % k = 0 := by omega
        have hp := hpPos
        rw [h0, Nat.mul_zero, Nat.zero_mod] at hp
        omega
      have h1 : 3 * δ * (inv3Pos k % k) + 3 * δ * (k - inv3Pos k % k) = (3 * δ) * k := by
        rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.le_of_lt hp_lt)]
      have hsum : ((3 * δ * (inv3Pos k % k)) % k + (3 * δ * (k - inv3Pos k % k)) % k) % k = 0 := by
        rw [← Nat.add_mod, h1, Nat.mul_mod_left]
      rw [hpPos] at hsum
      rw [Nat.mul_mod_mod]
      have hlt : (3 * δ * (k - inv3Pos k % k)) % k < k := Nat.mod_lt _ hk
      have hnz : (3 * δ * (k - inv3Pos k % k)) % k ≠ 0 := by
        intro hz
        rw [hz, Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hsum
        omega
      obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hsum
      have hm0 : m ≠ 0 := by
        intro hz; rw [hz, Nat.mul_zero] at hm; omega
      have hm2 : m < 2 := by
        by_contra h2
        have hge : 2 <= m := by omega
        have hkm : 2 * k <= k * m := by linarith [Nat.mul_le_mul_left k hge]
        omega
      have hm1 : m = 1 := by omega
      rw [hm1, Nat.mul_one] at hm
      omega
    dsimp [invMixB]
    simp only [hk5, ↓reduceIte]
    ext i
    rw [hpref, hpref, hpref, m3d_right_inv hk hk6 h5 hδ i]
    have hm_pos : m3dIdx k δ (inv3Pos k % k) hk = ⟨δ, by omega⟩ := Fin.ext hpPos
    have hm_neg : m3dIdx k δ ((k - inv3Pos k % k) % k) hk = ⟨k - δ, by omega⟩ := Fin.ext hpNeg
    have hm_0 : mixB hk δ x ⟨0, hk⟩ =
        xor (xor (x ⟨0, hk⟩) (x ⟨k - δ, by omega⟩)) (x ⟨δ, by omega⟩) := by
      dsimp [mixB, rotB]
      have hkmd : (k - δ) % k = k - δ := Nat.mod_eq_of_lt (by omega)
      have hr1 : (⟨(0 + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨k - δ, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.zero_add, hδk, hkmd]
      have hr2 : (⟨(0 + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨δ, by omega⟩ := by
        rw [Fin.ext_iff]; dsimp; rw [Nat.zero_add, hδk, hkmd]
        rw [show k - (k - δ) = δ by omega, hδk]
      rw [hr1, hr2]
    rw [hm_pos, hm_neg, hm_0]
    cases x ⟨0, hk⟩ <;> cases x ⟨k - δ, by omega⟩ <;> cases x ⟨δ, by omega⟩ <;> cases x i <;> rfl
theorem mixB_invMixB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 \/ k % 6 = 5)
    (δ : ℕ) (hδ : δ = 1 \/ δ = 2) (y : Fin k -> Bool) :
    mixB hk δ (invMixB hk δ y) = y := by
  have hinj : Function.Injective (mixB hk δ) :=
    Function.LeftInverse.injective (invMixB_mixB hk hk6 δ hδ)
  have hsurj : Function.Surjective (mixB hk δ) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj y
  rw [invMixB_mixB hk hk6 δ hδ]
def constBit (k j : ℕ) (i : Fin k) : Bool :=
  (3 ^ (k + j) % 2 ^ k).testBit i.val
theorem toNat_constBit {k j : ℕ} :
    toNat (constBit k j) = 3 ^ (k + j) % 2 ^ k := by
  unfold constBit
  exact toNat_ofNat (Nat.mod_lt _ (Nat.pow_pos (by omega)))
def firstB {k : ℕ} (hk : 0 < k) (r : ℕ) (rowKey rowName : Fin k -> Bool) : Fin k -> Bool :=
  (List.range r).foldl
    (fun rowState rowIndex =>
      fun i =>
        xor (xor (stepB hk (mixB hk 1 rowState) i) (rotB hk (2 * rowIndex) rowKey i))
          (constBit k (rowIndex + 1) i))
    (fun i => xor (rotB hk 1 rowKey i) (rowName i))
def secondB {k : ℕ} (hk : 0 < k) (r : ℕ) (colKey colName : Fin k -> Bool) : Fin k -> Bool :=
  (List.range r).foldl
    (fun colState colIndex =>
      fun i =>
        xor (xor (stepB hk (mixB hk 2 colState) i) (rotB hk (3 * (colIndex + 1) + 1) colKey i))
          (constBit k (r + (colIndex + 1)) i))
    (fun i => xor (rotB hk 3 colKey i) (colName i))
theorem foldl_range_toNat {k : ℕ} (r : ℕ)
    (fn : ℕ -> ℕ -> ℕ) (fb : (Fin k -> Bool) -> ℕ -> (Fin k -> Bool))
    (init : Fin k -> Bool)
    (hstep : ∀ (x : Fin k -> Bool) (idx : ℕ), fn (toNat x) idx = toNat (fb x idx)) :
    (List.range r).foldl fn (toNat init) = toNat ((List.range r).foldl fb init) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, ih, hstep]
theorem firstB_toNat {k : ℕ} (hk : 0 < k) (r : ℕ) (rowKey rowName : Fin k -> Bool) :
    (List.range r).foldl (fun rowState rowIndex =>
      ((List.range k).foldl (fun acc i =>
        acc ||| ((xor ((rowState ^^^ ((rowState <<< (1 % k)) ||| (rowState >>> (k - 1 % k))) % 2 ^ k ^^^
            ((rowState <<< ((k - 1) % k)) ||| (rowState >>> (k - (k - 1) % k))) % 2 ^ k).testBit i)
          (!((rowState ^^^ ((rowState <<< (1 % k)) ||| (rowState >>> (k - 1 % k))) % 2 ^ k ^^^
            ((rowState <<< ((k - 1) % k)) ||| (rowState >>> (k - (k - 1) % k))) % 2 ^ k).testBit ((i + 1) % k)) &&
            (rowState ^^^ ((rowState <<< (1 % k)) ||| (rowState >>> (k - 1 % k))) % 2 ^ k ^^^
            ((rowState <<< ((k - 1) % k)) ||| (rowState >>> (k - (k - 1) % k))) % 2 ^ k).testBit ((i + 2) % k))).toNat <<< i)) 0) ^^^
        ((toNat rowKey <<< (2 * rowIndex % k)) ||| (toNat rowKey >>> (k - 2 * rowIndex % k))) % 2 ^ k ^^^
        3 ^ (k + (rowIndex + 1)) % 2 ^ k)
      ((((toNat rowKey <<< (1 % k)) ||| (toNat rowKey >>> (k - 1 % k))) % 2 ^ k) ^^^ toNat rowName) =
    toNat (firstB hk r rowKey rowName) := by
  have hinit : (((toNat rowKey <<< (1 % k)) ||| (toNat rowKey >>> (k - 1 % k))) % 2 ^ k) ^^^ toNat rowName =
      toNat (fun i => xor (rotB hk 1 rowKey i) (rowName i)) := by
    rw [rot_toNat hk 1 rowKey, ← xor_toNat]
  rw [hinit]
  apply foldl_range_toNat
  intro x idx
  have hm : toNat (mixB hk 1 x) =
      toNat x ^^^ ((toNat x <<< (1 % k)) ||| (toNat x >>> (k - 1 % k))) % 2 ^ k ^^^
      ((toNat x <<< ((k - 1) % k)) ||| (toNat x >>> (k - (k - 1) % k))) % 2 ^ k := by
    rw [rot_toNat hk 1 x, rot_toNat hk (k - 1) x, ← xor_toNat, ← xor_toNat]
    congr 1; ext i; dsimp [mixB, rotB]
    have hmod : (k - 1 % k) % k = (k - 1) % k := by
      by_cases hk1 : k = 1
      · subst hk1; rfl
      · rw [Nat.mod_eq_of_lt (by omega : 1 < k)]
    congr 1; exact congrArg x (Fin.ext (by dsimp; rw [hmod]))
  rw [← hm, step_toNat hk (mixB hk 1 x), rot_toNat hk (2 * idx) rowKey, ← toNat_constBit (k := k) (j := idx + 1),
    ← xor_toNat, ← xor_toNat]
theorem secondB_toNat {k : ℕ} (hk : 0 < k) (r : ℕ) (colKey colName : Fin k -> Bool) :
    (List.range r).foldl (fun colState colIndex =>
      ((List.range k).foldl (fun acc i =>
        acc ||| ((xor ((colState ^^^ ((colState <<< (2 % k)) ||| (colState >>> (k - 2 % k))) % 2 ^ k ^^^
            ((colState <<< ((k - 2) % k)) ||| (colState >>> (k - (k - 2) % k))) % 2 ^ k).testBit i)
          (!((colState ^^^ ((colState <<< (2 % k)) ||| (colState >>> (k - 2 % k))) % 2 ^ k ^^^
            ((colState <<< ((k - 2) % k)) ||| (colState >>> (k - (k - 2) % k))) % 2 ^ k).testBit ((i + 1) % k)) &&
            (colState ^^^ ((colState <<< (2 % k)) ||| (colState >>> (k - 2 % k))) % 2 ^ k ^^^
            ((colState <<< ((k - 2) % k)) ||| (colState >>> (k - (k - 2) % k))) % 2 ^ k).testBit ((i + 2) % k))).toNat <<< i)) 0) ^^^
        ((toNat colKey <<< ((3 * (colIndex + 1) + 1) % k)) |||
          (toNat colKey >>> (k - (3 * (colIndex + 1) + 1) % k))) % 2 ^ k ^^^
        3 ^ (k + (r + (colIndex + 1))) % 2 ^ k)
      ((((toNat colKey <<< (3 % k)) ||| (toNat colKey >>> (k - 3 % k))) % 2 ^ k) ^^^ toNat colName) =
    toNat (secondB hk r colKey colName) := by
  have hinit : (((toNat colKey <<< (3 % k)) ||| (toNat colKey >>> (k - 3 % k))) % 2 ^ k) ^^^ toNat colName =
      toNat (fun i => xor (rotB hk 3 colKey i) (colName i)) := by
    rw [rot_toNat hk 3 colKey, ← xor_toNat]
  rw [hinit]
  apply foldl_range_toNat
  intro x idx
  have hm : toNat (mixB hk 2 x) =
      toNat x ^^^ ((toNat x <<< (2 % k)) ||| (toNat x >>> (k - 2 % k))) % 2 ^ k ^^^
      ((toNat x <<< ((k - 2) % k)) ||| (toNat x >>> (k - (k - 2) % k))) % 2 ^ k := by
    rw [rot_toNat hk 2 x, rot_toNat hk (k - 2) x, ← xor_toNat, ← xor_toNat]
    congr 1; ext i; dsimp [mixB, rotB]
    have hmod : (k - 2 % k) % k = (k - 2) % k := by
      rcases (by omega : k = 1 \/ k = 2 \/ 3 <= k) with rfl | rfl | hk3
      · rfl
      · rfl
      · rw [Nat.mod_eq_of_lt (by omega : 2 < k)]
    congr 1; exact congrArg x (Fin.ext (by dsimp; rw [hmod]))
  rw [← hm, step_toNat hk (mixB hk 2 x), rot_toNat hk (3 * (idx + 1) + 1) colKey,
    ← toNat_constBit (k := k) (j := r + (idx + 1)), ← xor_toNat, ← xor_toNat]
def xorList : List Bool -> Bool
  | [] => false
  | a :: l => xor a (xorList l)
@[simp] theorem xorList_nil : xorList [] = false := rfl
@[simp] theorem xorList_cons (a : Bool) (l : List Bool) : xorList (a :: l) = xor a (xorList l) := rfl
theorem xorList_append (l1 l2 : List Bool) : xorList (l1 ++ l2) = xor (xorList l1) (xorList l2) := by
  induction l1 with
  | nil => simp
  | cons a l1 ih => simp [ih, Bool.xor_assoc]
theorem xorList_map_xor {α : Type} (l : List α) (f g : α -> Bool) :
    xorList (l.map (fun x => xor (f x) (g x))) = xor (xorList (l.map f)) (xorList (l.map g)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, xorList_cons, ih]
    cases f a <;> cases g a <;> cases xorList (l.map f) <;> cases xorList (l.map g) <;> rfl
theorem xorList_map_and_left {α : Type} (l : List α) (c : Bool) (f : α -> Bool) :
    xorList (l.map (fun x => c && f x)) = (c && xorList (l.map f)) := by
  cases c
  · induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, Bool.false_and, xorList_cons, Bool.false_xor] at ih ⊢; exact ih
  · simp
theorem xorList_map_and_right {α : Type} (l : List α) (f : α -> Bool) (c : Bool) :
    xorList (l.map (fun x => f x && c)) = (xorList (l.map f) && c) := by
  cases c
  · induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, Bool.and_false, xorList_cons, Bool.false_xor] at ih ⊢; exact ih
  · simp
theorem xorList_map_false {α : Type} (l : List α) : xorList (l.map (fun _ => false)) = false := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, xorList_cons, Bool.false_xor]; exact ih
theorem xorList_swap {α β : Type} (l1 : List α) (l2 : List β) (g : α -> β -> Bool) :
    xorList (l1.map (fun a => xorList (l2.map (fun b => g a b)))) =
    xorList (l2.map (fun b => xorList (l1.map (fun a => g a b)))) := by
  induction l1 with
  | nil => simp only [List.map_nil, xorList_nil, xorList_map_false]
  | cons a l1 ih =>
    simp only [List.map_cons, xorList_cons, ih, ← xorList_map_xor]
theorem z157 (n : ℕ) (f : ℕ -> Bool) :
    xorList ((List.range (n + 1)).map f) = xor (xorList ((List.range n).map f)) (f n) := by
  rw [List.range_succ, List.map_append, List.map_singleton, xorList_append]
  simp
def xorFin {n : ℕ} (f : Fin n -> Bool) : Bool := xorList (List.ofFn f)
theorem xorFin_zero (f : Fin 0 -> Bool) : xorFin f = false := rfl
theorem z57 {n : ℕ} (f : Fin (n + 1) -> Bool) :
    xorFin f = xor (f 0) (xorFin (fun i => f i.succ)) := by
  simp [xorFin, List.ofFn_succ]
theorem z121 {n : ℕ} (f : Fin (n + 1) -> Bool) :
    xorFin f = xor (xorFin (fun i : Fin n => f i.castSucc)) (f (Fin.last n)) := by
  induction n with
  | zero =>
    simp [xorFin, List.ofFn_succ]
  | succ n ih =>
    rw [z57, ih (fun i => f i.succ), z57]
    simp [Bool.xor_assoc]
theorem xorFin_eq_range {n : ℕ} (f : Fin n -> Bool) (g : ℕ -> Bool)
    (h : ∀ i : Fin n, f i = g i.val) :
    xorFin f = xorList ((List.range n).map g) := by
  induction n with
  | zero => simp [xorFin]
  | succ n ih =>
    rw [z121, z157]
    congr 1
    · exact ih (fun i => f i.castSucc) (fun i => h i.castSucc)
    · exact h (Fin.last n)
theorem xorFin_xor {n : ℕ} (f g : Fin n -> Bool) :
    xorFin (fun i => xor (f i) (g i)) = xor (xorFin f) (xorFin g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [z57, z57, z57, ih]
    cases f 0 <;> cases g 0 <;> cases xorFin (fun i => f i.succ) <;>
      cases xorFin (fun i => g i.succ) <;> rfl
theorem xorFin_and_left {n : ℕ} (c : Bool) (f : Fin n -> Bool) :
    xorFin (fun i => c && f i) = (c && xorFin f) := by
  cases c
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Bool.false_and, z57, Bool.false_xor] at ih ⊢
      exact ih (fun i => f i.succ)
  · simp
theorem xorFin_and_right {n : ℕ} (f : Fin n -> Bool) (c : Bool) :
    xorFin (fun i => f i && c) = (xorFin f && c) := by
  cases c
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Bool.and_false, z57, Bool.false_xor] at ih ⊢
      exact ih (fun i => f i.succ)
  · simp
theorem z116 {n : ℕ} : xorFin (fun _ : Fin n => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [z57, ih]
theorem xorFin_swap {m n : ℕ} (g : Fin m -> Fin n -> Bool) :
    xorFin (fun i => xorFin (fun j => g i j)) = xorFin (fun j => xorFin (fun i => g i j)) := by
  induction m with
  | zero => simp [xorFin_zero, z116]
  | succ m ih =>
    rw [z57, ih]
    conv_rhs => rw [show (fun j => xorFin (fun i : Fin (m + 1) => g i j)) =
      (fun j => xor (g 0 j) (xorFin (fun i : Fin m => g i.succ j))) from funext fun j => z57 _]
    rw [xorFin_xor]
theorem xorFin_single {n : ℕ} (i : Fin n) (b : Bool) :
    xorFin (fun j : Fin n => if j = i then b else false) = b := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rw [z57]
    refine Fin.cases ?_ ?_ i
    · have h0 : xorFin (fun j : Fin n => if j.succ = (0 : Fin (n + 1)) then b else false) = false := by
        have hfun : (fun j : Fin n => if j.succ = (0 : Fin (n + 1)) then b else false) = fun _ => false := by
          ext j; simp [Fin.succ_ne_zero]
        rw [hfun]; exact z116
      rw [if_pos rfl, h0, Bool.xor_false]
    · intro i'
      have hne : (0 : Fin (n + 1)) ≠ i'.succ := (Fin.succ_ne_zero i').symm
      rw [if_neg hne, Bool.false_xor]
      have hfun : (fun j : Fin n => if j.succ = i'.succ then b else false) =
          (fun j : Fin n => if j = i' then b else false) := by
        ext j; simp [Fin.succ_inj]
      rw [hfun]; exact ih i'
theorem z58 {n : ℕ} {f g : Fin n -> Bool} (h : ∀ i, f i = g i) : xorFin f = xorFin g := by
  congr 1; funext i; exact h i
def invD (k δ : ℕ) : ℕ := if δ = 1 then 1 else (k + 1) / 2
def sIdx {k : ℕ} (hk : 0 < k) (δ p : ℕ) : Fin k := ⟨(δ * p) % k, Nat.mod_lt _ hk⟩
def sInv {k : ℕ} (hk : 0 < k) (δ : ℕ) (i : Fin k) : Fin k :=
  ⟨(i.val * invD k δ) % k, Nat.mod_lt _ hk⟩
theorem mul_invD_mod {k δ : ℕ} (hk_odd : k % 2 = 1) (hδ : δ = 1 \/ δ = 2) :
    (δ * invD k δ) % k = 1 % k := by
  rcases hδ with rfl | rfl
  · simp [invD]
  · simp only [invD, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
    have h2 : 2 * ((k + 1) / 2) = k + 1 := by omega
    rw [h2, Nat.add_mod_left]
theorem sIdx_sInv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (δ : ℕ)
    (hδ : δ = 1 \/ δ = 2) (i : Fin k) :
    sIdx hk δ (sInv hk δ i).val = i := by
  ext; dsimp [sIdx, sInv]
  calc (δ * ((i.val * invD k δ) % k)) % k
      = (δ * (i.val * invD k δ)) % k := Nat.mul_mod_mod _ _ k
    _ = (i.val * (δ * invD k δ)) % k := by ring_nf
    _ = ((i.val % k) * ((δ * invD k δ) % k)) % k := Nat.mul_mod _ _ k
    _ = ((i.val % k) * (1 % k)) % k := by rw [mul_invD_mod hk_odd hδ]
    _ = (i.val * 1) % k := (Nat.mul_mod _ _ k).symm
    _ = i.val := by rw [Nat.mul_one, Nat.mod_eq_of_lt i.isLt]
theorem sInv_sIdx {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (δ : ℕ)
    (hδ : δ = 1 \/ δ = 2) (p : ℕ) :
    (sInv hk δ (sIdx hk δ p)).val = p % k := by
  dsimp [sInv, sIdx]
  calc ((δ * p) % k * invD k δ) % k
      = (δ * p * invD k δ) % k := Nat.mod_mul_mod _ _ k
    _ = (p * (δ * invD k δ)) % k := by ring_nf
    _ = ((p % k) * ((δ * invD k δ) % k)) % k := Nat.mul_mod _ _ k
    _ = ((p % k) * (1 % k)) % k := by rw [mul_invD_mod hk_odd hδ]
    _ = (p * 1) % k := (Nat.mul_mod _ _ k).symm
    _ = p % k := by rw [Nat.mul_one]
theorem sIdx_mod {k : ℕ} (hk : 0 < k) (δ p : ℕ) :
    sIdx hk δ (p % k) = sIdx hk δ p := by
  ext; dsimp [sIdx]; exact Nat.mul_mod_mod _ _ k
theorem sIdx_add_k {k : ℕ} (hk : 0 < k) (δ p : ℕ) :
    sIdx hk δ (p + k) = sIdx hk δ p := by
  ext; dsimp [sIdx]; rw [Nat.mul_add, Nat.add_mul_mod_self_right]
theorem mixB_at_sIdx {k : ℕ} (hk : 0 < k) (hk3 : 3 <= k) (δ : ℕ)
    (hδ : δ = 1 \/ δ = 2) (x : Fin k -> Bool) (p : ℕ) :
    mixB hk δ x (sIdx hk δ (p + 1)) =
      xor (xor (x (sIdx hk δ (p + 1))) (x (sIdx hk δ p))) (x (sIdx hk δ (p + 2))) := by
  have hδk : δ % k = δ := Nat.mod_eq_of_lt (by omega)
  have hkmd : (k - δ) % k = k - δ := Nat.mod_eq_of_lt (by omega)
  have h0 : ∀ s t : ℕ, ((s % k) + k - t % k) % k = (s + k - t % k) % k := by
    intro s t
    have htm : t % k < k := Nat.mod_lt t hk
    rw [Nat.add_sub_assoc (by omega), Nat.mod_add_mod, ← Nat.add_sub_assoc (by omega)]
  dsimp [mixB, rotB, sIdx]
  have h1 : (⟨((δ * (p + 1)) % k + k - δ % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ⟨(δ * p) % k, Nat.mod_lt _ hk⟩ := by
    ext; dsimp; rw [h0, hδk]
    have : δ * (p + 1) + k - δ = δ * p + k := by rw [Nat.mul_add, Nat.mul_one]; omega
    rw [this, Nat.add_mod_right]
  have h2 : (⟨((δ * (p + 1)) % k + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ : Fin k) =
      ⟨(δ * (p + 2)) % k, Nat.mod_lt _ hk⟩ := by
    ext; dsimp; rw [h0, hδk, hkmd]
    have : δ * (p + 1) + k - (k - δ) = δ * (p + 2) := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    rw [this]
  rw [h1, h2]
def singDiff {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (t j : ℕ) : Bool :=
  xor (y (sIdx hk δ (3 * j + t + 1))) (y (sIdx hk δ (3 * j + t + 2)))
def singPref {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (t q : ℕ) : Bool :=
  xorList ((List.range q).map (singDiff hk δ y t))
def wrapOkB {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) : Bool :=
  !(singPref hk δ y 0 (k / 3)) && !(singPref hk δ y 1 (k / 3))
def z4 {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (b0 b1 : Bool) (p : ℕ) : Bool :=
  let t := p % 3
  let q := p / 3
  let x0 := if t = 0 then b0 else if t = 1 then b1 else xor (xor (y (sIdx hk δ 1)) b0) b1
  xor x0 (singPref hk δ y t q)
def z87 {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (b0 b1 : Bool) : Fin k -> Bool :=
  fun i => z4 hk δ y b0 b1 (sInv hk δ i).val
theorem singPref_succ {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (t q : ℕ) :
    singPref hk δ y t (q + 1) = xor (singPref hk δ y t q) (singDiff hk δ y t q) := by
  dsimp [singPref]; exact z157 q (singDiff hk δ y t)
theorem invMixSingVal_add3 {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (b0 b1 : Bool) (p : ℕ) :
    z4 hk δ y b0 b1 (p + 3) =
      xor (z4 hk δ y b0 b1 p) (xor (y (sIdx hk δ (p + 1))) (y (sIdx hk δ (p + 2)))) := by
  dsimp [z4]
  have hmod : (p + 3) % 3 = p % 3 := by omega
  have hdiv : (p + 3) / 3 = p / 3 + 1 := by omega
  have hrec : 3 * (p / 3) + p % 3 = p := by omega
  rw [hmod, hdiv, singPref_succ, ← Bool.xor_assoc]
  dsimp [singDiff]
  rw [show 3 * (p / 3) + p % 3 + 1 = p + 1 by omega, show 3 * (p / 3) + p % 3 + 2 = p + 2 by omega]
theorem z94 {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k -> Bool) (b0 b1 : Bool) (p : ℕ) :
    xor (xor (z4 hk δ y b0 b1 (p + 1)) (z4 hk δ y b0 b1 p))
        (z4 hk δ y b0 b1 (p + 2)) = y (sIdx hk δ (p + 1)) := by
  induction p with
  | zero =>
    dsimp [z4, singPref]
    cases b0 <;> cases b1 <;> cases y (sIdx hk δ 1) <;> rfl
  | succ p ih =>
    rw [show p + 1 + 2 = p + 3 by omega, invMixSingVal_add3]
    generalize z4 hk δ y b0 b1 p = a at ih ⊢
    generalize z4 hk δ y b0 b1 (p + 1) = b at ih ⊢
    generalize z4 hk δ y b0 b1 (p + 2) = c at ih ⊢
    generalize y (sIdx hk δ (p + 1)) = y1 at ih ⊢
    generalize y (sIdx hk δ (p + 2)) = y2 at ⊢
    cases a <;> cases b <;> cases c <;> cases y1 <;> cases y2 <;> simp_all
theorem invMixSingVal_periodic {k : ℕ} (hk : 0 < k) (hk3d : k % 3 = 0) (δ : ℕ)
    (y : Fin k -> Bool) (b0 b1 : Bool) (hw : wrapOkB hk δ y = true) :
    ∀ p : ℕ, z4 hk δ y b0 b1 (p + k) = z4 hk δ y b0 b1 p := by
  have hs0 : singPref hk δ y 0 (k / 3) = false := by
    dsimp [wrapOkB] at hw
    cases h0 : singPref hk δ y 0 (k / 3) <;> simp [h0] at hw ⊢
  have hs1 : singPref hk δ y 1 (k / 3) = false := by
    dsimp [wrapOkB] at hw
    cases h1 : singPref hk δ y 1 (k / 3) <;> simp [h1] at hw ⊢
  have hk0 : z4 hk δ y b0 b1 k = z4 hk δ y b0 b1 0 := by
    dsimp [z4]
    rw [hk3d]; simp only [Nat.zero_mod, Nat.zero_div, ↓reduceIte, hs0]; rfl
  have hk1 : z4 hk δ y b0 b1 (1 + k) = z4 hk δ y b0 b1 1 := by
    dsimp [z4]
    have h1m : (1 + k) % 3 = 1 := by omega
    have h1d : (1 + k) / 3 = k / 3 := by omega
    rw [h1m, h1d]; simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte, hs1]; rfl
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    match p with
    | 0 => simpa using hk0
    | 1 => exact hk1
    | q + 2 =>
      have hA := z94 hk δ y b0 b1 (q + k)
      have hB := z94 hk δ y b0 b1 q
      have ih0 := ih q (by omega)
      have ih1 := ih (q + 1) (by omega)
      have hq1 : q + k + 1 = q + 1 + k := by omega
      have hq2 : q + k + 2 = q + 2 + k := by omega
      rw [hq1, hq2, ih0, ih1] at hA
      have hy : y (sIdx hk δ (q + 1 + k)) = y (sIdx hk δ (q + 1)) := by rw [sIdx_add_k]
      rw [hy] at hA
      generalize z4 hk δ y b0 b1 (q + 2 + k) = u at hA ⊢
      generalize z4 hk δ y b0 b1 (q + 2) = v at hB ⊢
      generalize z4 hk δ y b0 b1 (q + 1) = a at hA hB
      generalize z4 hk δ y b0 b1 q = b at hA hB
      generalize y (sIdx hk δ (q + 1)) = c at hA hB
      cases u <;> cases v <;> cases a <;> cases b <;> cases c <;> simp_all
theorem invMixSingVal_mod {k : ℕ} (hk : 0 < k) (hk3d : k % 3 = 0) (δ : ℕ)
    (y : Fin k -> Bool) (b0 b1 : Bool) (hw : wrapOkB hk δ y = true) (p : ℕ) :
    z4 hk δ y b0 b1 (p % k) = z4 hk δ y b0 b1 p := by
  have hper := invMixSingVal_periodic hk hk3d δ y b0 b1 hw
  have hmul : ∀ q : ℕ, z4 hk δ y b0 b1 (p % k + k * q) = z4 hk δ y b0 b1 (p % k) := by
    intro q; induction q with
    | zero => simp
    | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hdiv : p % k + k * (p / k) = p := by
    have := Nat.div_add_mod p k; omega
  rw [← hmul (p / k), hdiv]
theorem mixB_invMixSingB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (hk3d : k % 3 = 0)
    (δ : ℕ) (hδ : δ = 1 \/ δ = 2) (y : Fin k -> Bool) (b0 b1 : Bool)
    (hw : wrapOkB hk δ y = true) :
    mixB hk δ (z87 hk δ y b0 b1) = y := by
  have hk3 : 3 <= k := by omega
  ext i
  let q := (sInv hk δ i).val
  have hi : sIdx hk δ (q + k - 1 + 1) = i := by
    rw [show q + k - 1 + 1 = q + k by omega, sIdx_add_k]
    exact sIdx_sInv hk hk_odd δ hδ i
  rw [← hi, mixB_at_sIdx hk hk3 δ hδ]
  simp only [z87, sInv_sIdx hk hk_odd δ hδ, invMixSingVal_mod hk hk3d δ y b0 b1 hw]
  exact z94 hk δ y b0 b1 (q + k - 1)
theorem invMixSingB_mixB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (hk3d : k % 3 = 0)
    (δ : ℕ) (hδ : δ = 1 \/ δ = 2) (x : Fin k -> Bool) :
    wrapOkB hk δ (mixB hk δ x) = true /\
    x = z87 hk δ (mixB hk δ x) (x (sIdx hk δ 0)) (x (sIdx hk δ 1)) := by
  have hk3 : 3 <= k := by omega
  set y := mixB hk δ x
  set b0 := x (sIdx hk δ 0)
  set b1 := x (sIdx hk δ 1)
  have hmatch : ∀ p : ℕ, x (sIdx hk δ p) = z4 hk δ y b0 b1 p := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      match p with
      | 0 => simp [z4, singPref, b0]
      | 1 => simp [z4, singPref, b1]
      | q + 2 =>
        have hA : y (sIdx hk δ (q + 1)) =
            xor (xor (x (sIdx hk δ (q + 1))) (x (sIdx hk δ q))) (x (sIdx hk δ (q + 2))) :=
          mixB_at_sIdx hk hk3 δ hδ x q
        have hB := z94 hk δ y b0 b1 q
        have ih0 := ih q (by omega)
        have ih1 := ih (q + 1) (by omega)
        rw [ih0, ih1] at hA
        generalize x (sIdx hk δ (q + 2)) = u at hA ⊢
        generalize z4 hk δ y b0 b1 (q + 2) = v at hB ⊢
        generalize z4 hk δ y b0 b1 (q + 1) = a at hA hB
        generalize z4 hk δ y b0 b1 q = b at hA hB
        generalize y (sIdx hk δ (q + 1)) = c at hA hB
        cases u <;> cases v <;> cases a <;> cases b <;> cases c <;> simp_all
  have hs0 : singPref hk δ y 0 (k / 3) = false := by
    have hk0 := hmatch k
    rw [show sIdx hk δ k = sIdx hk δ 0 from by simpa using sIdx_add_k hk δ 0] at hk0
    dsimp [z4] at hk0
    rw [hk3d] at hk0
    simp only [↓reduceIte] at hk0
    change b0 = xor b0 (singPref hk δ y 0 (k / 3)) at hk0
    cases h : singPref hk δ y 0 (k / 3) with
    | false => rfl
    | true => rw [h] at hk0; cases b0 <;> simp at hk0
  have hs1 : singPref hk δ y 1 (k / 3) = false := by
    have hk1 := hmatch (1 + k)
    rw [sIdx_add_k] at hk1
    dsimp [z4] at hk1
    have h1m : (1 + k) % 3 = 1 := by omega
    have h1d : (1 + k) / 3 = k / 3 := by omega
    rw [h1m, h1d] at hk1
    simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at hk1
    change b1 = xor b1 (singPref hk δ y 1 (k / 3)) at hk1
    cases h : singPref hk δ y 1 (k / 3) with
    | false => rfl
    | true => rw [h] at hk1; cases b1 <;> simp at hk1
  constructor
  · simp [wrapOkB, hs0, hs1]
  · ext i
    have hi := hmatch (sInv hk δ i).val
    rw [sIdx_sInv hk hk_odd δ hδ i] at hi
    exact hi
def z2 (k r : ℕ) : ℕ := if k % 3 = 0 then 4 ^ r else 1
theorem z127 (k r : ℕ) : 0 < z2 k r := by
  dsimp [z2]; split_ifs <;> positivity
def initRot (isCol : Bool) : ℕ := if isCol then 3 else 1
def mixStride (isCol : Bool) : ℕ := if isCol then 2 else 1
def z16 (isCol : Bool) (idx : ℕ) : ℕ := if isCol then 3 * (idx + 1) + 1 else 2 * idx
def z10 (isCol : Bool) (r idx : ℕ) : ℕ := if isCol then r + (idx + 1) else idx + 1
theorem z123 (isCol : Bool) : mixStride isCol = 1 \/ mixStride isCol = 2 := by
  cases isCol <;> simp [mixStride]
def fwdRoundB {k : ℕ} (hk : 0 < k) (isCol : Bool) (r idx : ℕ)
    (key st : Fin k -> Bool) : Fin k -> Bool :=
  fun i => xor (xor (stepB hk (mixB hk (mixStride isCol) st) i)
    (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
def fwdIterB {k : ℕ} (hk : 0 < k) (isCol : Bool) (r : ℕ)
    (key init : Fin k -> Bool) : ℕ -> Fin k -> Bool
  | 0 => init
  | t + 1 => fwdRoundB hk isCol r t key (fwdIterB hk isCol r key init t)
theorem fwdIterB_eq_foldl {k : ℕ} (hk : 0 < k) (isCol : Bool) (r : ℕ)
    (key init : Fin k -> Bool) (t : ℕ) :
    fwdIterB hk isCol r key init t =
      (List.range t).foldl (fun st idx => fwdRoundB hk isCol r idx key st) init := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [fwdIterB, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
def z42 {k : ℕ} (hk : 0 < k) (r : ℕ) (isCol : Bool) (key inp : Fin k -> Bool) : Fin k -> Bool :=
  fwdIterB hk isCol r key (fun i => xor (rotB hk (initRot isCol) key i) (inp i)) r
theorem z61 {k : ℕ} (hk : 0 < k) (r : ℕ) (key inp : Fin k -> Bool) :
    z42 hk r false key inp = firstB hk r key inp := by
  rw [z42, fwdIterB_eq_foldl]; rfl
theorem z71 {k : ℕ} (hk : 0 < k) (r : ℕ) (key inp : Fin k -> Bool) :
    z42 hk r true key inp = secondB hk r key inp := by
  rw [z42, fwdIterB_eq_foldl]; rfl
def revRoundB {k : ℕ} (hk : 0 < k) (isCol : Bool) (r idx : ℕ)
    (key st : Fin k -> Bool) (b0 b1 : Bool) : (Fin k -> Bool) × Bool :=
  let u : Fin k -> Bool := fun i =>
    xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
  let w := invChiB hk u
  if k % 3 = 0 then (z87 hk (mixStride isCol) w b0 b1, wrapOkB hk (mixStride isCol) w)
  else (invMixB hk (mixStride isCol) w, true)
theorem revRoundB_sound {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (isCol : Bool) (r idx : ℕ)
    (key st : Fin k -> Bool) (b0 b1 : Bool)
    (hok : (revRoundB hk isCol r idx key st b0 b1).2 = true) :
    fwdRoundB hk isCol r idx key (revRoundB hk isCol r idx key st b0 b1).1 = st := by
  dsimp [revRoundB] at hok ⊢
  set u : Fin k -> Bool := fun i =>
    xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
  have hmix : mixB hk (mixStride isCol)
      (if k % 3 = 0 then z87 hk (mixStride isCol) (invChiB hk u) b0 b1
       else invMixB hk (mixStride isCol) (invChiB hk u)) = invChiB hk u := by
    split_ifs with h3
    · simp only [h3, ↓reduceIte] at hok
      exact mixB_invMixSingB hk hk_odd h3 (mixStride isCol) (z123 isCol) _ b0 b1 hok
    · have hk6 : k % 6 = 1 \/ k % 6 = 5 := by omega
      exact mixB_invMixB hk hk6 (mixStride isCol) (z123 isCol) _
  split_ifs with h3
  · have hm' : mixB hk (mixStride isCol) (z87 hk (mixStride isCol) (invChiB hk u) b0 b1) = invChiB hk u := by
      simpa [h3] using hmix
    change fwdRoundB hk isCol r idx key (z87 hk (mixStride isCol) (invChiB hk u) b0 b1) = st
    unfold fwdRoundB
    rw [hm', stepB_invChiB hk hk_odd u]
    ext i; dsimp [u]
    cases st i <;> cases rotB hk (z16 isCol idx) key i <;>
      cases constBit k (z10 isCol r idx) i <;> rfl
  · have hm' : mixB hk (mixStride isCol) (invMixB hk (mixStride isCol) (invChiB hk u)) = invChiB hk u := by
      simpa [h3] using hmix
    change fwdRoundB hk isCol r idx key (invMixB hk (mixStride isCol) (invChiB hk u)) = st
    unfold fwdRoundB
    rw [hm', stepB_invChiB hk hk_odd u]
    ext i; dsimp [u]
    cases st i <;> cases rotB hk (z16 isCol idx) key i <;>
      cases constBit k (z10 isCol r idx) i <;> rfl
theorem revRoundB_complete {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (isCol : Bool) (r idx : ℕ)
    (key x : Fin k -> Bool) :
    ∃ b0 b1 : Bool, revRoundB hk isCol r idx key (fwdRoundB hk isCol r idx key x) b0 b1 = (x, true) := by
  have hu : (fun i => xor (xor (fwdRoundB hk isCol r idx key x i)
      (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)) =
      stepB hk (mixB hk (mixStride isCol) x) := by
    ext i; dsimp [fwdRoundB]
    cases stepB hk (mixB hk (mixStride isCol) x) i <;>
      cases rotB hk (z16 isCol idx) key i <;>
      cases constBit k (z10 isCol r idx) i <;> rfl
  by_cases h3 : k % 3 = 0
  · refine ⟨x (sIdx hk (mixStride isCol) 0), x (sIdx hk (mixStride isCol) 1), ?_⟩
    dsimp [revRoundB]
    rw [hu, z144 hk hk_odd]
    simp only [h3, ↓reduceIte]
    have ⟨hw, hx⟩ := invMixSingB_mixB hk hk_odd h3 (mixStride isCol) (z123 isCol) x
    exact Prod.ext hx.symm hw
  · refine ⟨false, false, ?_⟩
    dsimp [revRoundB]
    rw [hu, z144 hk hk_odd]
    simp only [h3, ↓reduceIte]
    have hk6 : k % 6 = 1 \/ k % 6 = 5 := by omega
    exact Prod.ext (invMixB_mixB hk hk6 (mixStride isCol) (z123 isCol) x) rfl
def revIterB {k : ℕ} (hk : 0 < k) (isCol : Bool) (r : ℕ) (key : Fin k -> Bool)
    (leaf : ℕ) : ℕ -> (Fin k -> Bool) -> (Fin k -> Bool) × Bool
  | 0, st => (st, true)
  | t + 1, st =>
    let res1 := revRoundB hk isCol r t key st (leaf.testBit (2 * t)) (leaf.testBit (2 * t + 1))
    let res2 := revIterB hk isCol r key leaf t res1.1
    (res2.1, res1.2 && res2.2)
def z108 {k : ℕ} (hk : 0 < k) (r : ℕ) (isCol : Bool) (key : Fin k -> Bool)
    (leaf : ℕ) (out : Fin k -> Bool) : (Fin k -> Bool) × Bool :=
  let res := revIterB hk isCol r key leaf r out
  (fun i => xor (rotB hk (initRot isCol) key i) (res.1 i), res.2)
theorem revIterB_sound {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (isCol : Bool) (r : ℕ)
    (key : Fin k -> Bool) (leaf : ℕ) :
    ∀ (t : ℕ) (st : Fin k -> Bool),
      (revIterB hk isCol r key leaf t st).2 = true ->
      fwdIterB hk isCol r key (revIterB hk isCol r key leaf t st).1 t = st
  | 0, st, _ => rfl
  | t + 1, st, hok => by
    simp only [revIterB, Bool.and_eq_true] at hok ⊢
    rw [fwdIterB, revIterB_sound hk hk_odd isCol r key leaf t _ hok.2]
    exact revRoundB_sound hk hk_odd isCol r t key st _ _ hok.1
theorem revBranchB_sound {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (r : ℕ) (isCol : Bool)
    (key out : Fin k -> Bool) (leaf : ℕ)
    (hok : (z108 hk r isCol key leaf out).2 = true) :
    z42 hk r isCol key (z108 hk r isCol key leaf out).1 = out := by
  dsimp [z108, z42] at hok ⊢
  have hcancel : (fun i => xor (rotB hk (initRot isCol) key i)
      (xor (rotB hk (initRot isCol) key i) ((revIterB hk isCol r key leaf r out).1 i))) =
      (revIterB hk isCol r key leaf r out).1 := by
    ext i; cases rotB hk (initRot isCol) key i <;>
      cases (revIterB hk isCol r key leaf r out).1 i <;> rfl
  rw [hcancel]
  exact revIterB_sound hk hk_odd isCol r key leaf r out hok
theorem z146 {k : ℕ} (hk : 0 < k) (isCol : Bool) (r : ℕ) (key : Fin k -> Bool)
    (l1 l2 : ℕ) :
    ∀ (t : ℕ) (st : Fin k -> Bool),
      (∀ j < 2 * t, l1.testBit j = l2.testBit j) ->
      revIterB hk isCol r key l1 t st = revIterB hk isCol r key l2 t st
  | 0, _, _ => rfl
  | t + 1, st, hbits => by
    dsimp [revIterB]
    have hb0 : l1.testBit (2 * t) = l2.testBit (2 * t) := hbits (2 * t) (by omega)
    have hb1 : l1.testBit (2 * t + 1) = l2.testBit (2 * t + 1) := hbits (2 * t + 1) (by omega)
    rw [hb0, hb1]
    have ih := z146 hk isCol r key l1 l2 t
      (revRoundB hk isCol r t key st (l2.testBit (2 * t)) (l2.testBit (2 * t + 1))).1
      (fun j hj => hbits j (by omega))
    rw [ih]
theorem revIterB_complete {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (isCol : Bool) (r : ℕ)
    (key init : Fin k -> Bool) :
    ∀ t : ℕ, ∃ leaf : ℕ, leaf < z2 k t /\
      revIterB hk isCol r key leaf t (fwdIterB hk isCol r key init t) = (init, true)
  | 0 => ⟨0, z127 k 0, rfl⟩
  | t + 1 => by
    obtain ⟨l0, hl0, hih⟩ := revIterB_complete hk hk_odd isCol r key init t
    obtain ⟨b0, b1, hstep⟩ := revRoundB_complete hk hk_odd isCol r t key (fwdIterB hk isCol r key init t)
    by_cases h3 : k % 3 = 0
    · have hl0' : l0 < 4 ^ t := by simpa [z2, h3] using hl0
      let leaf := l0 + (b0.toNat + 2 * b1.toNat) * 2 ^ (2 * t)
      have hpow4 : 4 ^ t = 2 ^ (2 * t) := by rw [pow_mul]; rfl
      have hlt : leaf < z2 k (t + 1) := by
        simp only [z2, h3, ↓reduceIte, pow_succ]
        have hb : b0.toNat + 2 * b1.toNat <= 3 := by cases b0 <;> cases b1 <;> decide
        have : l0 + (b0.toNat + 2 * b1.toNat) * 4 ^ t < 4 ^ t * 4 := by nlinarith
        simpa [leaf, hpow4] using this
      have htb_lo : ∀ j < 2 * t, leaf.testBit j = l0.testBit j := by
        intro j hj
        have hlo2 : l0 < 2 ^ (2 * t) := by rwa [← hpow4]
        have hdiv : leaf / 2 ^ j = l0 / 2 ^ j + (b0.toNat + 2 * b1.toNat) * 2 ^ (2 * t - j) := by
          have hpow : 2 ^ (2 * t) = 2 ^ (2 * t - j) * 2 ^ j := by
            rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
          dsimp [leaf]
          rw [hpow, ← Nat.mul_assoc, Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega))]
        have heven : 2 ∣ (b0.toNat + 2 * b1.toNat) * 2 ^ (2 * t - j) := by
          have h1 : 2 ^ (2 * t - j) = 2 ^ (2 * t - j - 1) * 2 := by
            have : 2 * t - j = (2 * t - j - 1) + 1 := by omega
            conv_lhs => rw [this, Nat.pow_succ]
          rw [h1, ← Nat.mul_assoc]; exact dvd_mul_left 2 _
        have htb_mod : ∀ n : ℕ, n.testBit j = decide ((n / 2 ^ j) % 2 = 1) := fun n => by
          simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
          rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h]
        rw [htb_mod, htb_mod, hdiv]
        obtain ⟨c, hc⟩ := heven
        rw [hc, Nat.add_mul_mod_self_left]
      have htb_b0 : leaf.testBit (2 * t) = b0 := by
        have hlo2 : l0 < 2 ^ (2 * t) := by rwa [← hpow4]
        have hdiv : leaf / 2 ^ (2 * t) = b0.toNat + 2 * b1.toNat := by
          dsimp [leaf]
          rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hlo2, Nat.zero_add]
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
        cases b0 <;> cases b1 <;> rfl
      have htb_b1 : leaf.testBit (2 * t + 1) = b1 := by
        have hlo2 : l0 < 2 ^ (2 * t) := by rwa [← hpow4]
        have hdiv1 : leaf / 2 ^ (2 * t) = b0.toNat + 2 * b1.toNat := by
          dsimp [leaf]
          rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by omega)), Nat.div_eq_of_lt hlo2, Nat.zero_add]
        have hdiv2 : leaf / 2 ^ (2 * t + 1) = (b0.toNat + 2 * b1.toNat) / 2 := by
          rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, hdiv1]
        simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv2]
        cases b0 <;> cases b1 <;> rfl
      refine ⟨leaf, hlt, ?_⟩
      dsimp [revIterB]
      rw [htb_b0, htb_b1, fwdIterB, hstep]
      dsimp only
      rw [z146 hk isCol r key leaf l0 t _ htb_lo, hih]
      rfl
    · refine ⟨0, by simp [z2, h3], ?_⟩
      dsimp [revIterB]
      have hzero : ∀ a b, revRoundB hk isCol r t key (fwdRoundB hk isCol r t key (fwdIterB hk isCol r key init t)) a b =
          (fwdIterB hk isCol r key init t, true) := by
        intro a b
        have := hstep
        simp only [revRoundB, h3, ↓reduceIte] at this ⊢
        exact this
      rw [fwdIterB, hzero]
      dsimp only
      have hl0z : l0 = 0 := by simp only [z2, h3, ↓reduceIte] at hl0; omega
      subst hl0z
      rw [hih]; rfl
def z13 {k : ℕ} (hk : 0 < k) (r : ℕ) (isCol rev : Bool)
    (leaf : Fin (z2 k r)) (key drv : Fin k -> Bool) : (Fin k -> Bool) × Bool :=
  if rev then z108 hk r isCol key leaf.val drv
  else (z42 hk r isCol key drv, true)
theorem evalBranch_sound {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (r : ℕ) (isCol rev : Bool)
    (leaf : Fin (z2 k r)) (key drv : Fin k -> Bool)
    (hok : (z13 hk r isCol rev leaf key drv).2 = true) :
    let cand := (z13 hk r isCol rev leaf key drv).1
    if rev then z42 hk r isCol key cand = drv else cand = z42 hk r isCol key drv := by
  cases rev
  · rfl
  · exact revBranchB_sound hk hk_odd r isCol key drv leaf.val hok
theorem z148 {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (r : ℕ) (isCol rev : Bool)
    (key inp : Fin k -> Bool) :
    ∃ leaf : Fin (z2 k r),
      z13 hk r isCol rev leaf key (if rev then z42 hk r isCol key inp else inp) =
        (if rev then inp else z42 hk r isCol key inp, true) := by
  cases rev
  · exact ⟨⟨0, z127 k r⟩, rfl⟩
  · obtain ⟨l, hl, hiter⟩ := revIterB_complete hk hk_odd isCol r key
      (fun i => xor (rotB hk (initRot isCol) key i) (inp i)) r
    refine ⟨⟨l, hl⟩, ?_⟩
    simp only [z13, ↓reduceIte, z108, z42]
    rw [hiter]
    apply Prod.ext
    · ext i; dsimp only; cases rotB hk (initRot isCol) key i <;> cases inp i <;> rfl
    · rfl
abbrev BMat (h' n : ℕ) := Fin h' -> Fin n -> Bool
def colApply {h' k : ℕ} (A : Fin k -> Fin h' -> Bool) (x : Fin k -> Bool) (q : Fin h') : Bool :=
  xorFin (fun j : Fin k => A j q && x j)
def GoodMatB {h' n : ℕ} (U : Finset (Fin n)) (M : BMat h' n) : Prop :=
  ∀ x : Fin n -> Bool, (∀ i, i ∉ U -> x i = false) ->
    (∀ q : Fin h', xorFin (fun i : Fin n => M q i && x i) = false) ->
    x = fun _ => false
theorem goodMatB_mono {h' n : ℕ} {U' U : Finset (Fin n)} {M : BMat h' n}
    (hsub : U' ⊆ U) (hgood : GoodMatB U M) : GoodMatB U' M :=
  fun x hx => hgood x (fun i hi => hx i (fun h => hi (hsub h)))
theorem colApply_xor {h' k : ℕ} (A : Fin k -> Fin h' -> Bool) (x y : Fin k -> Bool) :
    colApply A (fun j => xor (x j) (y j)) = fun q => xor (colApply A x q) (colApply A y q) := by
  ext q; dsimp [colApply]
  rw [← xorFin_xor]
  exact z58 fun j => by cases A j q <;> cases x j <;> cases y j <;> rfl
theorem colApply_zero {h' k : ℕ} (A : Fin k -> Fin h' -> Bool) :
    colApply A (fun _ => false) = fun _ => false := by
  ext q; dsimp [colApply]; simp [z116]
theorem z62 {h' k : ℕ} (A : Fin k -> Fin h' -> Bool) :
    Function.Injective (colApply A) ↔
      (∀ x : Fin k -> Bool, colApply A x = (fun _ => false) -> x = fun _ => false) := by
  constructor
  · intro hinj x hx
    exact hinj (hx.trans (colApply_zero A).symm)
  · intro hker x y hxy
    have h0 : colApply A (fun j => xor (x j) (y j)) = fun _ => false := by
      rw [colApply_xor, hxy]; ext q; simp
    have hz := hker _ h0
    ext j
    have hj := congrFun hz j
    cases hx : x j <;> cases hy : y j <;> simp_all
theorem goodMatB_dual {h' n : ℕ} {U' U : Finset (Fin n)} {M : BMat h' n}
    (hsub : U' ⊆ U) (hcard : U.card = h') (hgood : GoodMatB U M) :
    ∀ i ∈ U', ∃ c : Fin h' -> Bool, ∀ j ∈ U',
      xorFin (fun q : Fin h' => c q && M q j) = decide (j = i) := by
  classical
  let eU : Fin h' ≃ U := (Fintype.equivFinOfCardEq (by simpa [Fintype.card_coe] using hcard)).symm
  let A : Fin h' -> Fin h' -> Bool := fun j q => M q (eU j).1
  have hinjA : Function.Injective (colApply A) := by
    rw [z62]
    intro a ha
    let x : Fin n -> Bool := fun idx => if h : idx ∈ U then a (eU.symm ⟨idx, h⟩) else false
    have hxU : ∀ idx, idx ∉ U -> x idx = false := fun idx h => dif_neg h
    have hxM : ∀ q : Fin h', xorFin (fun idx : Fin n => M q idx && x idx) = false := by
      intro q
      have hq : colApply A a q = false := congrFun ha q
      rw [← hq]; dsimp [colApply, A]
      have hsplit : ∀ (S : Finset (Fin n)) (g : Fin n -> Bool),
          (∀ idx, idx ∉ S -> g idx = false) ->
          ∀ (m : ℕ) (e : Fin m ≃ S), xorFin g = xorFin (fun j : Fin m => g (e j).1) := by
        intro S g hg m e
        have hstep : ∀ (r : ℕ) (T : Finset (Fin n)), T.card = r ->
            ∀ (f : Fin n -> Bool), (∀ idx, idx ∉ T -> f idx = false) ->
            ∀ (eT : Fin r ≃ T), xorFin f = xorFin (fun j : Fin r => f (eT j).1) := by
          intro r
          induction r with
          | zero =>
            intro T hTc f hf eT
            have hT : T = ∅ := Finset.card_eq_zero.mp hTc
            subst hT
            have hf0 : f = fun _ => false := funext fun z => hf z (by simp)
            rw [hf0, z116, xorFin_zero]
          | succ r ih =>
            intro T hTc f hf eT
            let a0 : Fin n := (eT 0).1
            have ha0 : a0 ∈ T := (eT 0).2
            let T' := T.erase a0
            have hT'c : T'.card = r := by rw [Finset.card_erase_of_mem ha0, hTc]; omega
            let f' : Fin n -> Bool := fun z => if z = a0 then false else f z
            have hf' : ∀ z, z ∉ T' -> f' z = false := by
              intro z hz; by_cases hza : z = a0
              · simp [f', hza]
              · simp [f', hza, hf z (fun h => hz (Finset.mem_erase.mpr ⟨hza, h⟩))]
            let eT' : Fin r ≃ T' :=
              { toFun := fun j => ⟨(eT j.succ).1, Finset.mem_erase.mpr
                  ⟨fun heq => Fin.succ_ne_zero j (eT.injective (Subtype.ext heq)), (eT j.succ).2⟩⟩
                invFun := fun y =>
                  have hne : eT.symm ⟨y.1, Finset.mem_of_mem_erase y.2⟩ ≠ 0 := by
                    intro h0
                    have : (⟨y.1, Finset.mem_of_mem_erase y.2⟩ : T) = eT 0 := by
                      simpa [h0] using (eT.apply_symm_apply ⟨y.1, Finset.mem_of_mem_erase y.2⟩).symm
                    exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val this)
                  (eT.symm ⟨y.1, Finset.mem_of_mem_erase y.2⟩).pred hne
                left_inv := fun j => by
                  apply Fin.ext; dsimp only; rw [Fin.val_pred]
                  have hsub : eT.symm ⟨(eT j.succ).1, Finset.mem_of_mem_erase (Finset.mem_erase.mpr
                      ⟨fun heq => by
                        have h0 : eT j.succ = eT 0 := Subtype.ext heq
                        exact Fin.succ_ne_zero j (eT.injective h0), (eT j.succ).2⟩)⟩ = j.succ :=
                    eT.symm_apply_apply j.succ
                  rw [hsub]; simp
                right_inv := fun y => by
                  apply Subtype.ext
                  dsimp only
                  have hne : eT.symm ⟨y.1, Finset.mem_of_mem_erase y.2⟩ ≠ 0 := by
                    intro h0
                    have : (⟨y.1, Finset.mem_of_mem_erase y.2⟩ : T) = eT 0 := by
                      simpa [h0] using (eT.apply_symm_apply ⟨y.1, Finset.mem_of_mem_erase y.2⟩).symm
                    exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val this)
                  rw [Fin.succ_pred _ hne]
                  exact congrArg Subtype.val (eT.apply_symm_apply ⟨y.1, Finset.mem_of_mem_erase y.2⟩) }
            have hf_eq : f = fun z => xor (if z = a0 then f a0 else false) (f' z) := by
              ext z; by_cases hza : z = a0 <;> simp [f', hza]
            conv_lhs => rw [hf_eq]
            rw [xorFin_xor, xorFin_single, ih T' hT'c f' hf' eT', z57]
            congr 1
            exact z58 fun j => by
              have hne : (eT j.succ).1 ≠ a0 := fun heq => Fin.succ_ne_zero j (eT.injective (Subtype.ext heq))
              simp [f', eT', hne]
        exact hstep m S (by simpa [Fintype.card_coe] using (Fintype.card_congr e).symm) g hg e
      rw [hsplit U (fun idx => M q idx && x idx) (fun idx h => by simp [hxU idx h]) h' eU]
      exact z58 fun j => by simp [x, (eU j).2]
    have hx0 := hgood x hxU hxM
    ext j
    have hj := congrFun hx0 (eU j).1
    simpa [x, (eU j).2] using hj
  have hsurjA : Function.Surjective (colApply A) := Finite.injective_iff_surjective.mp hinjA
  let AT : Fin h' -> Fin h' -> Bool := fun q j => A j q
  have hinjAT : Function.Injective (colApply AT) := by
    rw [z62]
    intro c hc
    ext q
    obtain ⟨a, ha⟩ := hsurjA (fun p => decide (p = q))
    have hdot : xorFin (fun p => c p && colApply A a p) = xorFin (fun j => colApply AT c j && a j) := by
      dsimp [colApply, AT]
      conv_lhs =>
        rw [show (fun p => c p && xorFin (fun j => A j p && a j)) =
          (fun p => xorFin (fun j => c p && (A j p && a j))) from funext fun p => (xorFin_and_left _ _).symm]
      rw [xorFin_swap]
      refine z58 fun j => ?_
      rw [← xorFin_and_right]
      exact z58 fun p => by cases c p <;> cases A j p <;> cases a j <;> rfl
    rw [ha, hc] at hdot
    have hlhs : xorFin (fun p => c p && decide (p = q)) = c q := by
      rw [show (fun p => c p && decide (p = q)) = (fun p => if p = q then c q else false) from by
        ext p; by_cases hpq : p = q <;> simp [hpq]]
      exact xorFin_single q (c q)
    have hrhs : xorFin (fun j : Fin h' => false && a j) = false := by
      simp [z116]
    rw [hlhs, hrhs] at hdot
    exact hdot
  have hsurjAT : Function.Surjective (colApply AT) := Finite.injective_iff_surjective.mp hinjAT
  intro i hi
  let iIdx : Fin h' := eU.symm ⟨i, hsub hi⟩
  obtain ⟨c, hc⟩ := hsurjAT (fun j => decide (j = iIdx))
  refine ⟨c, fun j hj => ?_⟩
  let jIdx : Fin h' := eU.symm ⟨j, hsub hj⟩
  have hcj := congrFun hc jIdx
  have heq : (eU jIdx).1 = j := congrArg Subtype.val (eU.apply_symm_apply ⟨j, hsub hj⟩)
  have hval : xorFin (fun q : Fin h' => c q && M q j) = colApply AT c jIdx := by
    dsimp [colApply, AT, A]; rw [heq]
    exact z58 fun q => Bool.and_comm _ _
  rw [hval, hcj]
  by_cases hji : j = i
  · subst hji; simp [jIdx, iIdx]
  · have hne : jIdx ≠ iIdx := fun h => hji (by
      have := congrArg (fun z => (eU z).1) h
      simpa [jIdx, iIdx] using this)
    simp [hji, hne]
theorem card_colInj_fin (h' : ℕ) : ∀ k : ℕ,
    (Finset.univ.filter (fun A : Fin k -> Fin h' -> Bool => Function.Injective (colApply A))).card =
      ∏ j ∈ Finset.range k, (2 ^ h' - 2 ^ j)
  | 0 => by
    have : (Finset.univ.filter (fun A : Fin 0 -> Fin h' -> Bool => Function.Injective (colApply A))) =
        Finset.univ := by
      ext A; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro x y _; ext i; exact Fin.elim0 i
    rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; simp
  | k + 1 => by
    classical
    let split : (Fin (k + 1) -> Fin h' -> Bool) ≃ (Fin k -> Fin h' -> Bool) × (Fin h' -> Bool) :=
      { toFun := fun A => (fun j => A j.castSucc, A (Fin.last k))
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun A => by
          ext j q; refine Fin.lastCases ?_ ?_ j
          · simp [Fin.snoc_last]
          · intro i; simp [Fin.snoc_castSucc]
        right_inv := fun ⟨A, v⟩ => by
          ext j q
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last] }
    have hiff : ∀ (A : Fin k -> Fin h' -> Bool) (v : Fin h' -> Bool),
        Function.Injective (colApply (Fin.snoc (α := fun _ => Fin h' -> Bool) A v)) ↔
          Function.Injective (colApply A) /\ v ∉ Finset.univ.image (colApply A) := by
      intro A v
      rw [z62, z62]
      have hsnoc : ∀ (x : Fin (k + 1) -> Bool),
          colApply (Fin.snoc (α := fun _ => Fin h' -> Bool) A v) x =
            fun q => xor (colApply A (fun j => x j.castSucc) q) (v q && x (Fin.last k)) := by
        intro x; ext q; dsimp [colApply]
        rw [z121]; simp [Fin.snoc_castSucc, Fin.snoc_last]
      constructor
      · intro hker
        refine ⟨fun x hx => ?_, fun hv => ?_⟩
        · have hx' : colApply (Fin.snoc (α := fun _ => Fin h' -> Bool) A v) (Fin.snoc x false) = fun _ => false := by
            rw [hsnoc]; ext q; simp [Fin.snoc_castSucc, Fin.snoc_last, congrFun hx q]
          have hz := hker _ hx'
          ext j; simpa [Fin.snoc_castSucc] using congrFun hz j.castSucc
        · rcases Finset.mem_image.mp hv with ⟨x, _, hxv⟩
          have hx' : colApply (Fin.snoc (α := fun _ => Fin h' -> Bool) A v) (Fin.snoc x true) = fun _ => false := by
            rw [hsnoc]; ext q; simp [Fin.snoc_castSucc, Fin.snoc_last, congrFun hxv q]
          have hz := congrFun (hker _ hx') (Fin.last k)
          simp [Fin.snoc_last] at hz
      · rintro ⟨hkerA, hv⟩ x hx
        rw [hsnoc] at hx
        cases hlast : x (Fin.last k)
        · have hxA : colApply A (fun j => x j.castSucc) = fun _ => false := by
            ext q; simpa [hlast] using congrFun hx q
          have hz := hkerA _ hxA
          ext j; refine Fin.lastCases hlast (fun i => congrFun hz i) j
        · exfalso; apply hv; rw [Finset.mem_image]
          refine ⟨fun j => x j.castSucc, Finset.mem_univ _, ?_⟩
          ext q
          have hq := congrFun hx q
          simp only [hlast, Bool.and_true] at hq
          cases h1 : colApply A (fun j => x j.castSucc) q <;> cases h2 : v q <;> simp_all
    let Sgood := Finset.univ.filter (fun A : Fin k -> Fin h' -> Bool => Function.Injective (colApply A))
    let Tgood := Finset.univ.filter (fun p : (Fin k -> Fin h' -> Bool) × (Fin h' -> Bool) =>
      Function.Injective (colApply p.1) /\ p.2 ∉ Finset.univ.image (colApply p.1))
    have hcard1 : (Finset.univ.filter (fun A : Fin (k + 1) -> Fin h' -> Bool => Function.Injective (colApply A))).card =
        Tgood.card := by
      rw [← Fintype.card_subtype, ← Fintype.card_subtype]
      refine Fintype.card_congr
        { toFun := fun ⟨A, hA⟩ => ⟨split A, (hiff (split A).1 (split A).2).mp (by
            have hEq : Fin.snoc (α := fun _ => Fin h' -> Bool) (split A).1 (split A).2 = A := split.left_inv A
            rwa [hEq])⟩
          invFun := fun ⟨p, hp⟩ => ⟨split.symm p, (hiff p.1 p.2).mpr hp⟩
          left_inv := fun ⟨A, _⟩ => Subtype.ext (split.left_inv A)
          right_inv := fun ⟨p, _⟩ => Subtype.ext (split.right_inv p) }
    have hT : Tgood = Sgood.biUnion (fun A => (Finset.univ.filter (fun v : Fin h' -> Bool =>
        v ∉ Finset.univ.image (colApply A))).map ⟨fun v => (A, v), fun _ _ h => (Prod.mk.inj h).2⟩) := by
      ext ⟨A, v⟩
      simp only [Tgood, Sgood, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
      constructor
      · intro h; exact ⟨A, h.1, v, h.2, rfl⟩
      · rintro ⟨A', hA', v', hv', hEq⟩
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact ⟨hA', hv'⟩
    rw [hcard1, hT, Finset.card_biUnion]
    · have hfib : ∀ A ∈ Sgood,
          ((Finset.univ.filter (fun v : Fin h' -> Bool => v ∉ Finset.univ.image (colApply A))).map
            ⟨fun v => (A, v), fun _ _ h => (Prod.mk.inj h).2⟩).card = 2 ^ h' - 2 ^ k := by
        intro A hA
        rw [Finset.card_map]
        have hinj : Function.Injective (colApply A) := (Finset.mem_filter.mp hA).2
        have himg : (Finset.univ.image (colApply A)).card = 2 ^ k := by
          rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin]
        have htot : (Finset.univ : Finset (Fin h' -> Bool)).card = 2 ^ h' := by
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        have hcomp := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin h' -> Bool)))
          (p := fun v => v ∈ Finset.univ.image (colApply A))
        have hmem : (Finset.univ.filter (fun v => v ∈ Finset.univ.image (colApply A))).card = 2 ^ k := by
          simpa [Finset.filter_mem_eq_inter] using himg
        omega
      rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
        Finset.prod_range_succ, card_colInj_fin h' k]
    · intro A1 _ A2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp1 hp2
      rcases hp1 with ⟨_, _, rfl⟩
      rcases hp2 with ⟨_, _, h2⟩
      exact hne (Prod.mk.inj h2).1.symm
theorem prod_pow_sub_lower (h' : ℕ) :
    2 ^ (h' * h') <= 4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j) := by
  by_cases h0 : h' = 0
  · subst h0; simp
  have h1 : 1 <= h' := by omega
  have hind : ∀ m : ℕ, 1 <= m ->
      (2 ^ m + 2) * (∏ j ∈ Finset.range m, 2 ^ (j + 1)) <=
        4 * 2 ^ m * (∏ j ∈ Finset.range m, (2 ^ (j + 1) - 1)) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have ih' := ih (by omega)
        rw [Finset.prod_range_succ, Finset.prod_range_succ]
        have h2m : 2 <= 2 ^ m := by
          calc 2 = 2 ^ 1 := rfl
            _ <= 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
        have hstep : (2 ^ (m + 1) + 2) * 2 ^ (m + 1) <= 2 * (2 ^ m + 2) * (2 ^ (m + 1) - 1) := by
          have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ, mul_comm]
          rw [hp]
          have hsub : 1 <= 2 * 2 ^ m := by omega
          have h2z : (2 : ℤ) <= (2 ^ m : ℕ) := by exact_mod_cast h2m
          zify [hsub]; nlinarith
        calc (2 ^ (m + 1) + 2) * ((∏ j ∈ Finset.range m, 2 ^ (j + 1)) * 2 ^ (m + 1))
            = (∏ j ∈ Finset.range m, 2 ^ (j + 1)) * ((2 ^ (m + 1) + 2) * 2 ^ (m + 1)) := by ring
          _ <= (∏ j ∈ Finset.range m, 2 ^ (j + 1)) * (2 * (2 ^ m + 2) * (2 ^ (m + 1) - 1)) :=
              Nat.mul_le_mul_left _ hstep
          _ = 2 * ((2 ^ m + 2) * (∏ j ∈ Finset.range m, 2 ^ (j + 1))) * (2 ^ (m + 1) - 1) := by ring
          _ <= 2 * (4 * 2 ^ m * (∏ j ∈ Finset.range m, (2 ^ (j + 1) - 1))) * (2 ^ (m + 1) - 1) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 ih')
          _ = 4 * 2 ^ (m + 1) * ((∏ j ∈ Finset.range m, (2 ^ (j + 1) - 1)) * (2 ^ (m + 1) - 1)) := by
              rw [pow_succ]; ring
  have hmain := hind h' h1
  have hmul : ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j) =
      (∏ j ∈ Finset.range h', 2 ^ j) * (∏ j ∈ Finset.range h', (2 ^ (j + 1) - 1)) := by
    have hrev : ∏ j ∈ Finset.range h', (2 ^ (h' - j) - 1) =
        ∏ j ∈ Finset.range h', (2 ^ (j + 1) - 1) := by
      have := Finset.prod_range_reflect (fun j => 2 ^ (j + 1) - 1) h'
      rw [← this]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      congr 2; omega
    rw [← hrev, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_of_le (by omega)]
  have hden : (∏ j ∈ Finset.range h', 2 ^ j) * (∏ j ∈ Finset.range h', 2 ^ (j + 1)) =
      2 ^ (h' * h') := by
    have hrev : ∏ j ∈ Finset.range h', 2 ^ (h' - j) = ∏ j ∈ Finset.range h', 2 ^ (j + 1) := by
      have := Finset.prod_range_reflect (fun j => 2 ^ (j + 1)) h'
      rw [← this]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      congr 1; omega
    rw [← hrev, ← Finset.prod_mul_distrib]
    have hconst : ∀ j ∈ Finset.range h', 2 ^ j * 2 ^ (h' - j) = 2 ^ h' := fun j hj => by
      rw [Finset.mem_range] at hj
      rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
    rw [Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range, ← Nat.pow_mul]
  have hpos : 0 < 2 ^ h' := Nat.pow_pos (by omega)
  have hstep2 : 2 ^ h' * 2 ^ (h' * h') <= 2 ^ h' * (4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j)) := by
    calc 2 ^ h' * 2 ^ (h' * h')
        = (∏ j ∈ Finset.range h', 2 ^ j) * (2 ^ h' * (∏ j ∈ Finset.range h', 2 ^ (j + 1))) := by
          rw [← hden]; ring
      _ <= (∏ j ∈ Finset.range h', 2 ^ j) * ((2 ^ h' + 2) * (∏ j ∈ Finset.range h', 2 ^ (j + 1))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ <= (∏ j ∈ Finset.range h', 2 ^ j) * (4 * 2 ^ h' * (∏ j ∈ Finset.range h', (2 ^ (j + 1) - 1))) :=
          Nat.mul_le_mul_left _ hmain
      _ = 2 ^ h' * (4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j)) := by rw [hmul]; ring
  exact Nat.le_of_mul_le_mul_left hstep2 hpos
open Classical in
open Classical in
theorem card_goodMatB {h' n : ℕ} {U : Finset (Fin n)} (hU : U.card = h') :
    2 ^ (h' * n) <= 4 * (Finset.univ.filter (fun M : BMat h' n => GoodMatB U M)).card := by
  classical
  let eU : Fin h' ≃ U := (Fintype.equivFinOfCardEq (by simpa [Fintype.card_coe] using hU)).symm
  let eMat : BMat h' n ≃ (Fin h' -> Fin h' -> Bool) × ({ j : Fin n // j ∉ U } -> Fin h' -> Bool) :=
    { toFun := fun M => (fun j q => M q (eU j).1, fun j q => M q j.1)
      invFun := fun p q i =>
        if hi : i ∈ U then p.1 (eU.symm ⟨i, hi⟩) q else p.2 ⟨i, hi⟩ q
      left_inv := fun M => by
        ext q i; by_cases hi : i ∈ U
        · simp [hi, congrArg Subtype.val (eU.apply_symm_apply ⟨i, hi⟩)]
        · simp [hi]
      right_inv := fun ⟨A, B⟩ => by
        ext j q
        · simp [(eU j).2]
        · simp [j.2] }
  have hgood_iff : ∀ M : BMat h' n, GoodMatB U M ↔ Function.Injective (colApply (eMat M).1) := by
    intro M
    rw [z62]
    have hsplit : ∀ (f : Fin n -> Bool), (∀ i, i ∉ U -> f i = false) ->
        xorFin f = xorFin (fun j : Fin h' => f (eU j).1) := by
      intro f hf
      have hstep : ∀ (r : ℕ) (T : Finset (Fin n)), T.card = r ->
          ∀ (g : Fin n -> Bool), (∀ idx, idx ∉ T -> g idx = false) ->
          ∀ (eT : Fin r ≃ T), xorFin g = xorFin (fun j : Fin r => g (eT j).1) := by
        intro r
        induction r with
        | zero =>
          intro T hTc g hg eT
          have hT : T = ∅ := Finset.card_eq_zero.mp hTc
          subst hT
          have hg0 : g = fun _ => false := funext fun z => hg z (by simp)
          rw [hg0, z116, xorFin_zero]
        | succ r ih =>
          intro T hTc g hg eT
          let a0 : Fin n := (eT 0).1
          have ha0 : a0 ∈ T := (eT 0).2
          let T' := T.erase a0
          have hT'c : T'.card = r := by rw [Finset.card_erase_of_mem ha0, hTc]; omega
          let g' : Fin n -> Bool := fun z => if z = a0 then false else g z
          have hg' : ∀ z, z ∉ T' -> g' z = false := by
            intro z hz; by_cases hza : z = a0
            · simp [g', hza]
            · simp [g', hza, hg z (fun h => hz (Finset.mem_erase.mpr ⟨hza, h⟩))]
          let eT' : Fin r ≃ T' :=
            { toFun := fun j => ⟨(eT j.succ).1, Finset.mem_erase.mpr
                ⟨fun heq => Fin.succ_ne_zero j (eT.injective (Subtype.ext heq)), (eT j.succ).2⟩⟩
              invFun := fun y =>
                have hne : eT.symm ⟨y.1, Finset.mem_of_mem_erase y.2⟩ ≠ 0 := by
                  intro h0
                  have : (⟨y.1, Finset.mem_of_mem_erase y.2⟩ : T) = eT 0 := by
                    simpa [h0] using (eT.apply_symm_apply ⟨y.1, Finset.mem_of_mem_erase y.2⟩).symm
                  exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val this)
                (eT.symm ⟨y.1, Finset.mem_of_mem_erase y.2⟩).pred hne
              left_inv := fun j => by
                apply Fin.ext; dsimp only; rw [Fin.val_pred]
                have hsub : eT.symm ⟨(eT j.succ).1, Finset.mem_of_mem_erase (Finset.mem_erase.mpr
                    ⟨fun heq => by
                      have h0 : eT j.succ = eT 0 := Subtype.ext heq
                      exact Fin.succ_ne_zero j (eT.injective h0), (eT j.succ).2⟩)⟩ = j.succ :=
                  eT.symm_apply_apply j.succ
                rw [hsub]; simp
              right_inv := fun y => by
                apply Subtype.ext; dsimp only
                have hne : eT.symm ⟨y.1, Finset.mem_of_mem_erase y.2⟩ ≠ 0 := by
                  intro h0
                  have : (⟨y.1, Finset.mem_of_mem_erase y.2⟩ : T) = eT 0 := by
                    simpa [h0] using (eT.apply_symm_apply ⟨y.1, Finset.mem_of_mem_erase y.2⟩).symm
                  exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val this)
                rw [Fin.succ_pred _ hne]
                exact congrArg Subtype.val (eT.apply_symm_apply ⟨y.1, Finset.mem_of_mem_erase y.2⟩) }
          have hg_eq : g = fun z => xor (if z = a0 then g a0 else false) (g' z) := by
            ext z; by_cases hza : z = a0 <;> simp [g', hza]
          conv_lhs => rw [hg_eq]
          rw [xorFin_xor, xorFin_single, ih T' hT'c g' hg' eT', z57]
          congr 1
          exact z58 fun j => by
            have hne : (eT j.succ).1 ≠ a0 := fun heq => Fin.succ_ne_zero j (eT.injective (Subtype.ext heq))
            simp [g', eT', hne]
      exact hstep h' U hU f hf eU
    constructor
    · intro hgood a ha
      let x : Fin n -> Bool := fun i => if hi : i ∈ U then a (eU.symm ⟨i, hi⟩) else false
      have hxU : ∀ i, i ∉ U -> x i = false := fun i h => dif_neg h
      have hxM : ∀ q : Fin h', xorFin (fun i : Fin n => M q i && x i) = false := by
        intro q
        rw [hsplit (fun i => M q i && x i) (fun i h => by simp [hxU i h])]
        simpa [colApply, eMat, x, (eU _).2] using congrFun ha q
      have hx0 := hgood x hxU hxM
      ext j; simpa [x, (eU j).2] using congrFun hx0 (eU j).1
    · intro hker x hxU hxM
      let a : Fin h' -> Bool := fun j => x (eU j).1
      have ha : colApply (eMat M).1 a = fun _ => false := by
        ext q
        have hq := hxM q
        rw [hsplit (fun i => M q i && x i) (fun i h => by simp [hxU i h])] at hq
        simpa [colApply, eMat, a] using hq
      have ha0 := hker a ha
      ext i; by_cases hi : i ∈ U
      · have hj := congrFun ha0 (eU.symm ⟨i, hi⟩)
        simpa [a, congrArg Subtype.val (eU.apply_symm_apply ⟨i, hi⟩)] using hj
      · exact hxU i hi
  have hcard_eq : (Finset.univ.filter (fun M : BMat h' n => GoodMatB U M)).card =
      (Finset.univ.filter (fun A : Fin h' -> Fin h' -> Bool => Function.Injective (colApply A))).card *
        2 ^ (h' * (n - h')) := by
    have h1 : (Finset.univ.filter (fun M : BMat h' n => GoodMatB U M)).card =
        Fintype.card { M : BMat h' n // GoodMatB U M } := (Fintype.card_subtype _).symm
    have h2 : Fintype.card { M : BMat h' n // GoodMatB U M } =
        Fintype.card ({ A : Fin h' -> Fin h' -> Bool // Function.Injective (colApply A) } ×
          ({ j : Fin n // j ∉ U } -> Fin h' -> Bool)) := by
      refine Fintype.card_congr
        { toFun := fun ⟨M, hM⟩ => (⟨(eMat M).1, (hgood_iff M).mp hM⟩, (eMat M).2)
          invFun := fun ⟨⟨A, hA⟩, B⟩ => ⟨eMat.symm (A, B), (hgood_iff _).mpr (by simpa using hA)⟩
          left_inv := fun ⟨M, _⟩ => Subtype.ext (eMat.left_inv M)
          right_inv := fun ⟨⟨A, _⟩, B⟩ => by
            ext1
            · apply Subtype.ext; simp [eMat.right_inv (A, B)]
            · simp [eMat.right_inv (A, B)] }
    rw [h1, h2, Fintype.card_prod, Fintype.card_subtype, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    have hcomp : Fintype.card { j : Fin n // j ∉ U } = n - h' := by
      rw [Fintype.card_subtype]
      have hadd := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
        (p := fun j => j ∈ U)
      have hU' : (Finset.univ.filter (fun j : Fin n => j ∈ U)).card = h' := by
        simpa [Finset.filter_mem_eq_inter] using hU
      have htot : (Finset.univ : Finset (Fin n)).card = n := Finset.card_fin n
      omega
    rw [hcomp, ← pow_mul]
  rw [hcard_eq, card_colInj_fin h' h']
  have hle : h' <= n := by
    have := Finset.card_le_univ U; simp only [Fintype.card_fin] at this; omega
  have hexp : 2 ^ (h' * n) = 2 ^ (h' * h') * 2 ^ (h' * (n - h')) := by
    rw [← pow_add, ← mul_add, Nat.add_sub_of_le hle]
  rw [hexp]
  calc 2 ^ (h' * h') * 2 ^ (h' * (n - h'))
      <= (4 * ∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j)) * 2 ^ (h' * (n - h')) :=
        Nat.mul_le_mul_right _ (prod_pow_sub_lower h')
    _ = 4 * ((∏ j ∈ Finset.range h', (2 ^ h' - 2 ^ j)) * 2 ^ (h' * (n - h'))) := by ring
open Classical in
open Classical in
theorem greedy_cover_stepB {h' n : ℕ} (S : Finset (Finset (Fin n))) (hS : S.Nonempty)
    (hcard : ∀ U ∈ S, U.card = h') :
    ∃ M : BMat h' n, 4 * (S.filter (fun U => ¬ GoodMatB U M)).card <= 3 * S.card := by
  classical
  let allM : Finset (BMat h' n) := Finset.univ
  have hallM_card : allM.card = 2 ^ (h' * n) := by
    simp [allM, Fintype.card_bool, ← pow_mul, mul_comm]
  have hsum : S.card * 2 ^ (h' * n) <=
      4 * ∑ M ∈ allM, (S.filter (fun U => GoodMatB U M)).card := by
    have h1 : ∑ M ∈ allM, (S.filter (fun U => GoodMatB U M)).card =
        ∑ U ∈ S, (allM.filter (fun M => GoodMatB U M)).card := by
      simp_rw [Finset.card_filter]; exact Finset.sum_comm
    rw [h1, Finset.mul_sum]
    have h2 : S.card * 2 ^ (h' * n) = ∑ _U ∈ S, 2 ^ (h' * n) := by simp [Finset.sum_const]
    rw [h2]
    exact Finset.sum_le_sum fun U hU => card_goodMatB (hcard U hU)
  by_contra hnone
  push_neg at hnone
  have hbad : ∀ M ∈ allM, 4 * (S.filter (fun U => GoodMatB U M)).card < S.card := by
    intro M _
    have hgt := hnone M
    have hsplit := Finset.card_filter_add_card_filter_not (s := S) (p := fun U => GoodMatB U M)
    omega
  have hsumlt : 4 * ∑ M ∈ allM, (S.filter (fun U => GoodMatB U M)).card < allM.card * S.card := by
    rw [Finset.mul_sum]
    have h2 : allM.card * S.card = ∑ _M ∈ allM, S.card := by simp [Finset.sum_const]
    rw [h2]
    exact Finset.sum_lt_sum (fun M hM => le_of_lt (hbad M hM))
      ⟨fun _ _ => false, Finset.mem_univ _, hbad _ (Finset.mem_univ _)⟩
  rw [hallM_card, mul_comm (2 ^ (h' * n)) S.card] at hsumlt
  omega
def rowMask {h' n : ℕ} (M : BMat h' n) (c : Fin (2 ^ h')) (j : Fin n) : Bool :=
  xorFin (fun q : Fin h' => c.val.testBit q.val && M q j)
def dotBool (h' a b : ℕ) : Bool :=
  xorFin (fun q : Fin h' => a.testBit q.val && b.testBit q.val)
def synOf {h' n : ℕ} (M : BMat h' n) (x : Fin n -> Bool) : Fin (2 ^ h') :=
  ⟨toNat (fun q : Fin h' => xorFin (fun j : Fin n => M q j && x j)), toNat_lt _⟩
theorem synOf_testBit {h' n : ℕ} (M : BMat h' n) (x : Fin n -> Bool) (q : Fin h') :
    (synOf M x).val.testBit q.val = xorFin (fun j : Fin n => M q j && x j) :=
  z102 _ q
theorem rowMask_dot_eq {h' n : ℕ} (M : BMat h' n) (c : Fin (2 ^ h')) (x : Fin n -> Bool) :
    xorFin (fun j : Fin n => rowMask M c j && x j) = dotBool h' c.val (synOf M x).val := by
  dsimp [rowMask, dotBool]
  simp_rw [synOf_testBit]
  conv_lhs =>
    rw [show (fun j : Fin n => xorFin (fun q : Fin h' => c.val.testBit q.val && M q j) && x j) =
      (fun j : Fin n => xorFin (fun q : Fin h' => (c.val.testBit q.val && M q j) && x j)) from
      funext fun j => (xorFin_and_right _ _).symm]
  rw [xorFin_swap]
  refine z58 fun q => ?_
  rw [← xorFin_and_left]
  exact z58 fun j => by cases c.val.testBit q.val <;> cases M q j <;> cases x j <;> rfl
theorem exists_mat_family_any (n h' : ℕ) (hhn : h' <= n) :
    ∃ (R : ℕ) (H : Fin R -> BMat h' n),
      1 <= R /\ R <= 3 * (h' + 1) * (Nat.clog 2 (n + 1) + 1) /\
      ∀ U : Finset (Fin n), U.card <= h' ->
        ∃ r : Fin R, ∀ i ∈ U, ∃ c : Fin (2 ^ h'), ∀ j ∈ U,
          rowMask (H r) c j = decide (j = i) := by
  classical
  by_cases hh0 : h' = 0
  · subst hh0
    refine ⟨1, fun _ q => Fin.elim0 q, le_refl 1, by nlinarith, fun U hU => ?_⟩
    have hUe : U = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hUe
    exact ⟨0, fun i hi => by simp at hi⟩
  · have hh1 : 1 <= h' := by omega
    let L := Nat.clog 2 (n + 1)
    have hL1 : 1 <= L := by
      have : Nat.clog 2 2 <= L := Nat.clog_mono_right 2 (by omega)
      have h2 : Nat.clog 2 2 = 1 := by decide
      omega
    have hn_lt : n < 2 ^ L := by
      have := (Nat.clog_le_iff_le_pow (by omega)).mp (le_rfl : L <= L)
      omega
    let R := 3 * (h' * L) + 1
    have hR1 : 1 <= R := by omega
    have hRbd : R <= 3 * (h' + 1) * (L + 1) := by dsimp [R]; nlinarith
    have hstep : ∀ (t : ℕ) (S : Finset (Finset (Fin n))), (∀ U ∈ S, U.card = h') ->
        ∃ Ms : Fin t -> BMat h' n,
          4 ^ t * (S.filter (fun U => ∀ r : Fin t, ¬ GoodMatB U (Ms r))).card <= 3 ^ t * S.card := by
      intro t
      induction t with
      | zero => intro S _; exact ⟨Fin.elim0, by simp⟩
      | succ t ih =>
        intro S hSc
        obtain ⟨Ms, hMs⟩ := ih S hSc
        let Srem := S.filter (fun U => ∀ r : Fin t, ¬ GoodMatB U (Ms r))
        by_cases hne : Srem.Nonempty
        · obtain ⟨Mnew, hMnew⟩ := greedy_cover_stepB Srem hne (fun U hU => hSc U (Finset.mem_filter.mp hU).1)
          refine ⟨Fin.snoc (α := fun _ => BMat h' n) Ms Mnew, ?_⟩
          have hsub : S.filter (fun U => ∀ r : Fin (t + 1), ¬ GoodMatB U (Fin.snoc (α := fun _ => BMat h' n) Ms Mnew r)) =
              Srem.filter (fun U => ¬ GoodMatB U Mnew) := by
            ext U; simp only [Srem, Finset.mem_filter]
            constructor
            · rintro ⟨hUS, hall⟩
              exact ⟨⟨hUS, fun r => by simpa [Fin.snoc_castSucc] using hall r.castSucc⟩,
                by simpa [Fin.snoc_last] using hall (Fin.last t)⟩
            · rintro ⟨⟨hUS, hall⟩, hlast⟩
              refine ⟨hUS, fun r => Fin.lastCases (by simpa [Fin.snoc_last] using hlast)
                (fun r' => by simpa [Fin.snoc_castSucc] using hall r') r⟩
          rw [hsub]
          calc 4 ^ (t + 1) * (Srem.filter (fun U => ¬ GoodMatB U Mnew)).card
              = 4 ^ t * (4 * (Srem.filter (fun U => ¬ GoodMatB U Mnew)).card) := by ring
            _ <= 4 ^ t * (3 * Srem.card) := Nat.mul_le_mul_left _ hMnew
            _ = 3 * (4 ^ t * Srem.card) := by ring
            _ <= 3 * (3 ^ t * S.card) := Nat.mul_le_mul_left _ hMs
            _ = 3 ^ (t + 1) * S.card := by ring
        · rw [Finset.not_nonempty_iff_eq_empty] at hne
          refine ⟨Fin.snoc (α := fun _ => BMat h' n) Ms (fun _ _ => false), ?_⟩
          have hsub : S.filter (fun U => ∀ r : Fin (t + 1),
              ¬ GoodMatB U (Fin.snoc (α := fun _ => BMat h' n) Ms (fun _ _ => false) r)) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro U hU
            rw [Finset.mem_filter] at hU
            have hrem : U ∈ Srem := Finset.mem_filter.mpr
              ⟨hU.1, fun r => by simpa [Fin.snoc_castSucc] using hU.2 r.castSucc⟩
            rw [hne] at hrem; simp at hrem
          rw [hsub, Finset.card_empty, mul_zero]; exact Nat.zero_le _
    let S0 : Finset (Finset (Fin n)) := Finset.univ.filter (fun U : Finset (Fin n) => U.card = h')
    obtain ⟨Ms, hMs⟩ := hstep R S0 (fun U hU => (Finset.mem_filter.mp hU).2)
    have hS0_lt : S0.card < 2 ^ (h' * L) := by
      have hS0_eq : S0 = Finset.powersetCard h' (Finset.univ : Finset (Fin n)) := by
        ext U; simp [S0, Finset.mem_powersetCard]
      have h1 : S0.card = n.choose h' := by
        rw [hS0_eq, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      have h2 : n.choose h' <= n ^ h' := Nat.choose_le_pow n h'
      have h3 : n ^ h' < (2 ^ L) ^ h' := Nat.pow_lt_pow_left hn_lt (by omega)
      rw [h1]; exact lt_of_le_of_lt h2 (by simpa [← pow_mul, mul_comm] using h3)
    have hrem_zero : (S0.filter (fun U => ∀ r : Fin R, ¬ GoodMatB U (Ms r))).card = 0 := by
      set rem := (S0.filter (fun U => ∀ r : Fin R, ¬ GoodMatB U (Ms r))).card
      have hpow_mul : 2 ^ (h' * L) * 3 ^ R <= 4 ^ R := by
        have h3 : 3 ^ R = 3 * 3 ^ (3 * (h' * L)) := by simp [R, pow_succ']
        have h4 : 4 ^ R = 4 * 4 ^ (3 * (h' * L)) := by simp [R, pow_succ']
        have h27 : 3 ^ (3 * (h' * L)) = 27 ^ (h' * L) := by rw [pow_mul]; rfl
        have h64 : 4 ^ (3 * (h' * L)) = 64 ^ (h' * L) := by rw [pow_mul]; rfl
        have h264 : 2 ^ (h' * L) * 27 ^ (h' * L) <= 64 ^ (h' * L) := by
          rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
        rw [h3, h4, h27, h64]
        calc 2 ^ (h' * L) * (3 * 27 ^ (h' * L))
            = 3 * (2 ^ (h' * L) * 27 ^ (h' * L)) := by ring
          _ <= 3 * 64 ^ (h' * L) := Nat.mul_le_mul_left 3 h264
          _ <= 4 * 64 ^ (h' * L) := Nat.mul_le_mul_right _ (by omega)
      by_contra hnz
      have hrem1 : 1 <= rem := by omega
      have hlt : 3 ^ R * S0.card < 4 ^ R := by
        calc 3 ^ R * S0.card < 3 ^ R * 2 ^ (h' * L) :=
              Nat.mul_lt_mul_of_pos_left hS0_lt (Nat.pow_pos (by omega))
          _ = 2 ^ (h' * L) * 3 ^ R := mul_comm _ _
          _ <= 4 ^ R := hpow_mul
      have hle : 4 ^ R <= 4 ^ R * rem := Nat.le_mul_of_pos_right _ (by omega)
      omega
    refine ⟨R, Ms, hR1, hRbd, fun U' hU' => ?_⟩
    obtain ⟨U, hsub, hUcard⟩ := Finset.exists_superset_card_eq hU'
      (by simpa [Fintype.card_fin] using hhn)
    have hUmem : U ∈ S0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hUcard⟩
    have hexr : ∃ r : Fin R, GoodMatB U (Ms r) := by
      by_contra hno
      push_neg at hno
      have hmem : U ∈ S0.filter (fun U => ∀ r : Fin R, ¬ GoodMatB U (Ms r)) :=
        Finset.mem_filter.mpr ⟨hUmem, hno⟩
      have hpos := Finset.card_pos.mpr ⟨U, hmem⟩
      omega
    obtain ⟨r, hr⟩ := hexr
    refine ⟨r, fun i hi => ?_⟩
    obtain ⟨cFun, hcFun⟩ := goodMatB_dual hsub hUcard hr i hi
    refine ⟨⟨toNat cFun, toNat_lt cFun⟩, fun j hj => ?_⟩
    dsimp [rowMask]
    rw [← hcFun j hj]
    exact z58 fun q => by rw [z102]
abbrev Lit (W : Type) := PEqualNP.ProofComplexity.Literal W
abbrev Cl (W : Type) := PEqualNP.ProofComplexity.Clause W
def negL {W : Type} (l : Lit W) : Lit W := PEqualNP.Search.negLit l
def lEv {W : Type} (α : W -> Bool) (l : Lit W) : Bool := (α l.1 == l.2)
def upS {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : Set (Lit W) :=
  S ∪ {l | ∃ D ∈ F, l ∈ D /\ ∀ other ∈ D, other ≠ l -> negL other ∈ S}
def seedOf {V M : Type} (ρ : V -> Option Bool) : Set (Lit (Sum V M)) :=
  {l | ∃ raw : V, l.1 = Sum.inl raw /\ ρ raw = some l.2}
@[simp] theorem negL_negL {W : Type} (l : Lit W) : negL (negL l) = l := by
  rcases l with ⟨v, b⟩; cases b <;> rfl
theorem lEv_eq_true {W : Type} (α : W -> Bool) (l : Lit W) :
    lEv α l = true ↔ α l.1 = l.2 := by
  rcases l with ⟨v, b⟩; dsimp [lEv]; cases α v <;> cases b <;> simp
theorem lEv_negL {W : Type} (α : W -> Bool) (l : Lit W) :
    lEv α (negL l) = !(lEv α l) := by
  rcases l with ⟨v, b⟩; dsimp [lEv, negL, PEqualNP.Search.negLit]; cases α v <;> cases b <;> rfl
theorem clauseSat_iff {W : Type} (α : W -> Bool) (C : Cl W) :
    ClauseSat α C ↔ ∃ l ∈ C, lEv α l = true := by
  simp [ClauseSat, lEv_eq_true]
theorem z136 {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : S ⊆ upS F S :=
  Set.subset_union_left
theorem upS_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
    (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : upS F1 S1 ⊆ upS F2 S2 := by
  intro l hl
  rcases hl with hl | ⟨D, hD, hlD, ho⟩
  · exact Or.inl (hS hl)
  · exact Or.inr ⟨D, hF hD, hlD, fun o h1 h2 => hS (ho o h1 h2)⟩
theorem z5 {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) {t1 t2 : ℕ}
    (h : t1 <= t2) : (upS F)^[t1] S ⊆ (upS F)^[t2] S := by
  induction h with
  | refl => exact Set.Subset.rfl
  | @step m _ ih =>
    rw [Function.iterate_succ_apply']
    exact Set.Subset.trans ih (z136 F _)
theorem upS_sound {W : Type} {F : Finset (Cl W)} {α : W -> Bool}
    (hF : Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
    (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ l ∈ upS F S, α l.1 = l.2 := by
  intro l hl
  rcases hl with hl | ⟨D, hD, hlD, ho⟩
  · exact hS l hl
  · obtain ⟨u, huD, hu⟩ := hF D hD
    by_cases heq : u = l
    · simpa [heq] using hu
    · have hn := hS (negL u) (ho u huD heq)
      simp only [negL, PEqualNP.Search.negLit] at hn
      rw [hu] at hn; cases u.2 <;> simp at hn
theorem z163 {W : Type} {F : Finset (Cl W)} {α : W -> Bool}
    (hF : Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
    (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ t : ℕ, ∀ l ∈ (upS F)^[t] S, α l.1 = l.2
  | 0 => hS
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    exact upS_sound hF (z163 hF hS t)
theorem upS_unit1 {W : Type} {F : Finset (Cl W)} {S : Set (Lit W)} {a : Lit W}
    (hC : ({a} : Cl W) ∈ F) : a ∈ upS F S := by
  refine Or.inr ⟨{a}, hC, Finset.mem_singleton_self a, fun o ho hne => ?_⟩
  rw [Finset.mem_singleton] at ho; exact absurd ho hne
theorem upS_unit2 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)} {a b : Lit W}
    (hC : ({a, b} : Cl W) ∈ F) (ha : negL a ∈ S) : b ∈ upS F S := by
  refine Or.inr ⟨{a, b}, hC, by simp, fun o ho hne => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl
  · exact ha
  · exact absurd rfl hne
theorem upS_unit3 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)} {a b c : Lit W}
    (hC : ({a, b, c} : Cl W) ∈ F) (ha : negL a ∈ S) (hb : negL b ∈ S) : c ∈ upS F S := by
  refine Or.inr ⟨{a, b, c}, hC, by simp, fun o ho hne => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact absurd rfl hne
def cl1 {W : Type} (a : Lit W) : Cl W := {a}
def imp1 {W : Type} [DecidableEq W] (a b : Lit W) : Cl W := {negL a, b}
def imp2 {W : Type} [DecidableEq W] (a b c : Lit W) : Cl W := {negL a, negL b, c}
theorem cl1_card {W : Type} (a : Lit W) : (cl1 a).card <= 3 := by simp [cl1]
theorem imp1_card {W : Type} [DecidableEq W] (a b : Lit W) : (imp1 a b).card <= 3 := by
  have := Finset.card_insert_le (negL a) ({b} : Cl W); simp at this; dsimp [imp1]; omega
theorem imp2_card {W : Type} [DecidableEq W] (a b c : Lit W) : (imp2 a b c).card <= 3 := by
  have h1 := Finset.card_insert_le (negL a) ({negL b, c} : Cl W)
  have h2 := Finset.card_insert_le (negL b) ({c} : Cl W)
  simp at h2; dsimp [imp2]; omega
theorem clauseSat_cl1 {W : Type} (α : W -> Bool) (a : Lit W) :
    ClauseSat α (cl1 a) ↔ lEv α a = true := by
  simp [clauseSat_iff, cl1]
theorem z6 {W : Type} [DecidableEq W] (α : W -> Bool) (a b : Lit W) :
    ClauseSat α (imp1 a b) ↔ (lEv α a = true -> lEv α b = true) := by
  simp only [clauseSat_iff, imp1, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, lEv_negL]
  cases lEv α a <;> cases lEv α b <;> simp
theorem z45 {W : Type} [DecidableEq W] (α : W -> Bool) (a b c : Lit W) :
    ClauseSat α (imp2 a b c) ↔ (lEv α a = true -> lEv α b = true -> lEv α c = true) := by
  simp only [clauseSat_iff, imp2, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
    exists_eq_left, lEv_negL]
  cases lEv α a <;> cases lEv α b <;> cases lEv α c <;> simp
theorem upS_imp1 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)} {a b : Lit W}
    (hC : imp1 a b ∈ F) (ha : a ∈ S) : b ∈ upS F S :=
  upS_unit2 hC (by rwa [negL_negL])
theorem upS_imp2 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)} {a b c : Lit W}
    (hC : imp2 a b c ∈ F) (ha : a ∈ S) (hb : b ∈ S) : c ∈ upS F S :=
  upS_unit3 hC (by rwa [negL_negL]) (by rwa [negL_negL])
def mapVar {V A B : Type} (e : A ≃ B) : Sum V A -> Sum V B
  | Sum.inl v => Sum.inl v
  | Sum.inr a => Sum.inr (e a)
def mapLit {V A B : Type} (e : A ≃ B) (l : Lit (Sum V A)) : Lit (Sum V B) :=
  (mapVar e l.1, l.2)
def mapCl {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (C : Cl (Sum V A)) : Cl (Sum V B) :=
  C.image (mapLit e)
theorem mapVar_inj {V A B : Type} (e : A ≃ B) : Function.Injective (mapVar (V := V) e) := by
  intro x y h; cases x <;> cases y <;> simp [mapVar] at h
  · exact congrArg Sum.inl h
  · exact congrArg Sum.inr h
theorem mapLit_inj {V A B : Type} (e : A ≃ B) : Function.Injective (mapLit (V := V) e) := by
  intro ⟨x1, b1⟩ ⟨x2, b2⟩ h
  simp only [mapLit, Prod.mk.injEq] at h
  exact Prod.ext (mapVar_inj e h.1) h.2
theorem mapLit_negL {V A B : Type} (e : A ≃ B) (l : Lit (Sum V A)) :
    mapLit e (negL l) = negL (mapLit e l) := rfl
theorem mapCl_card {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (C : Cl (Sum V A)) : (mapCl e C).card = C.card :=
  Finset.card_image_of_injective C (mapLit_inj e)
theorem mapCl_sum_card_le {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (F : Finset (Cl (Sum V A))) :
    ∑ C ∈ F.image (mapCl e), C.card <= ∑ C ∈ F, C.card := by
  calc ∑ C ∈ F.image (mapCl e), C.card
      <= ∑ C ∈ F, (mapCl e C).card := Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = ∑ C ∈ F, C.card := Finset.sum_congr rfl fun C _ => mapCl_card e C
theorem mapCl_sat_iff {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (v : V -> Bool) (aux : A -> Bool) (C : Cl (Sum V A)) :
    ClauseSat (Sum.elim v aux) C ↔ ClauseSat (Sum.elim v (aux ∘ e.symm)) (mapCl e C) := by
  constructor
  · rintro ⟨⟨x, b⟩, hx, hsat⟩
    refine ⟨mapLit e (x, b), Finset.mem_image_of_mem _ hx, ?_⟩
    cases x <;> simpa [mapLit, mapVar] using hsat
  · rintro ⟨l', hl', hsat⟩
    rcases Finset.mem_image.mp hl' with ⟨⟨x, b⟩, hx, rfl⟩
    refine ⟨(x, b), hx, ?_⟩
    cases x <;> simpa [mapLit, mapVar] using hsat
theorem mapF_sat_iff {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (v : V -> Bool) (F : Finset (Cl (Sum V A))) :
    (∃ aux : A -> Bool, Satisfies (Sum.elim v aux) (↑F : Set _)) ↔
    (∃ aux' : B -> Bool, Satisfies (Sum.elim v aux') (↑(F.image (mapCl e)) : Set _)) := by
  constructor
  · rintro ⟨aux, haux⟩
    refine ⟨aux ∘ e.symm, fun C' hC' => ?_⟩
    rcases Finset.mem_image.mp hC' with ⟨C, hC, rfl⟩
    exact (mapCl_sat_iff e v aux C).mp (haux C hC)
  · rintro ⟨aux', haux'⟩
    refine ⟨aux' ∘ e, fun C hC => ?_⟩
    have h1 := haux' (mapCl e C) (Finset.mem_image_of_mem _ hC)
    have h2 : (aux' ∘ e) ∘ e.symm = aux' := by ext b; simp
    rw [← h2] at h1
    exact (mapCl_sat_iff e v (aux' ∘ e) C).mpr h1
theorem z125 {V A B : Type} [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (F : Finset (Cl (Sum V A))) (ρ : V -> Option Bool) :
    ∀ (t : ℕ) (l : Lit (Sum V A)),
      l ∈ (upS F)^[t] (seedOf ρ) -> mapLit e l ∈ (upS (F.image (mapCl e)))^[t] (seedOf ρ)
  | 0, l, hl => by
    rcases hl with ⟨raw, hv, hρ⟩
    refine ⟨raw, ?_, hρ⟩
    dsimp [mapLit]; rw [hv]; rfl
  | t + 1, l, hl => by
    rw [Function.iterate_succ_apply'] at hl ⊢
    rcases hl with hl | ⟨D, hD, hlD, ho⟩
    · exact Or.inl (z125 e F ρ t l hl)
    · refine Or.inr ⟨mapCl e D, Finset.mem_image_of_mem _ hD, Finset.mem_image_of_mem _ hlD, ?_⟩
      intro o' ho' hne
      rcases Finset.mem_image.mp ho' with ⟨o, hoD, rfl⟩
      have hneo : o ≠ l := fun h => hne (congrArg (mapLit e) h)
      rw [← mapLit_negL]
      exact z125 e F ρ t (negL o) (ho o hoD hneo)
theorem sum_toFinset_card_le {W : Type} [DecidableEq W] (L : List (Cl W))
    (h3 : ∀ C ∈ L, C.card <= 3) :
    ∑ C ∈ L.toFinset, C.card <= 3 * L.length := by
  calc ∑ C ∈ L.toFinset, C.card
      <= ∑ _C ∈ L.toFinset, 3 := Finset.sum_le_sum fun C hC => h3 C (List.mem_toFinset.mp hC)
    _ = L.toFinset.card * 3 := by simp
    _ <= L.length * 3 := Nat.mul_le_mul_right 3 (List.toFinset_card_le L)
    _ = 3 * L.length := mul_comm _ _
def tsEq {W : Type} [DecidableEq W] (a b : Lit W) : List (Cl W) := [imp1 a b, imp1 b a]
def tsXor {W : Type} [DecidableEq W] (a b out : Lit W) : List (Cl W) :=
  [imp2 a b (negL out), imp2 (negL a) (negL b) (negL out),
   imp2 a (negL b) out, imp2 (negL a) b out]
def tsAnd {W : Type} [DecidableEq W] (a b out : Lit W) : List (Cl W) :=
  [imp1 out a, imp1 out b, imp2 a b out]
theorem tsEq_card {W : Type} [DecidableEq W] (a b : Lit W) :
    ∀ C ∈ tsEq a b, C.card <= 3 := by
  intro C hC; simp only [tsEq, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl <;> exact imp1_card _ _
theorem tsXor_card {W : Type} [DecidableEq W] (a b out : Lit W) :
    ∀ C ∈ tsXor a b out, C.card <= 3 := by
  intro C hC; simp only [tsXor, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> exact imp2_card _ _ _
theorem tsAnd_card {W : Type} [DecidableEq W] (a b out : Lit W) :
    ∀ C ∈ tsAnd a b out, C.card <= 3 := by
  intro C hC; simp only [tsAnd, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl
  · exact imp1_card _ _
  · exact imp1_card _ _
  · exact imp2_card _ _ _
theorem tsEq_sat_iff {W : Type} [DecidableEq W] (α : W -> Bool) (a b : Lit W) :
    (∀ C ∈ tsEq a b, ClauseSat α C) ↔ lEv α a = lEv α b := by
  simp only [tsEq, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    z6]
  cases lEv α a <;> cases lEv α b <;> simp
theorem z59 {W : Type} [DecidableEq W] (α : W -> Bool) (a b out : Lit W) :
    (∀ C ∈ tsXor a b out, ClauseSat α C) ↔ lEv α out = xor (lEv α a) (lEv α b) := by
  simp only [tsXor, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    z45, lEv_negL]
  cases lEv α a <;> cases lEv α b <;> cases lEv α out <;> simp
theorem tsAnd_sat_iff {W : Type} [DecidableEq W] (α : W -> Bool) (a b out : Lit W) :
    (∀ C ∈ tsAnd a b out, ClauseSat α C) ↔ lEv α out = (lEv α a && lEv α b) := by
  simp only [tsAnd, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    z6, z45]
  cases lEv α a <;> cases lEv α b <;> cases lEv α out <;> simp
abbrev DualLit (W : Type) := Lit W × Lit W
def drFlip {W : Type} (w : DualLit W) (b : Bool) : Lit W := if b then w.2 else w.1
def drNot {W : Type} (w : DualLit W) : DualLit W := (w.2, w.1)
def z34 {W : Type} (c : Bool) (w : DualLit W) : DualLit W := if c then drNot w else w
def DRMode {W : Type} (α : W -> Bool) (dead : Bool) (w : DualLit W) (val : Bool) : Prop :=
  if dead then lEv α w.1 = true /\ lEv α w.2 = true
  else lEv α w.1 = !val /\ lEv α w.2 = val
theorem z154 {W : Type} {α : W -> Bool} {dead : Bool} {w : DualLit W} {val : Bool}
    (h : DRMode α dead w val) : DRMode α dead (drNot w) (!val) := by
  cases dead <;> cases val <;> simp only [DRMode, drNot, Bool.not_false, Bool.not_true, ↓reduceIte] at h ⊢ <;> exact ⟨h.2, h.1⟩
theorem z100 {W : Type} {α : W -> Bool} {dead : Bool} {w : DualLit W} {val : Bool}
    (c : Bool) (h : DRMode α dead w val) : DRMode α dead (z34 c w) (xor c val) := by
  cases c
  · simpa [z34] using h
  · simpa [z34] using z154 h
theorem drFlip_not {W : Type} (w : DualLit W) (b : Bool) :
    drFlip (drNot w) (!b) = drFlip w b := by cases b <;> rfl
theorem z101 {W : Type} (c : Bool) (w : DualLit W) (b : Bool) :
    drFlip (z34 c w) (xor c b) = drFlip w b := by cases c <;> cases b <;> rfl
def drEq {W : Type} [DecidableEq W] (a b : DualLit W) : List (Cl W) :=
  [imp1 a.1 b.1, imp1 a.2 b.2]
def drXor {W : Type} [DecidableEq W] (a b out : DualLit W) : List (Cl W) :=
  [imp2 a.1 b.1 out.1, imp2 a.2 b.2 out.1, imp2 a.1 b.2 out.2, imp2 a.2 b.1 out.2]
def drAnd {W : Type} [DecidableEq W] (a b out : DualLit W) : List (Cl W) :=
  [imp2 a.1 b.1 out.1, imp2 a.1 b.2 out.1, imp2 a.2 b.1 out.1, imp2 a.2 b.2 out.2]
theorem drEq_card {W : Type} [DecidableEq W] (a b : DualLit W) :
    ∀ C ∈ drEq a b, C.card <= 3 := by
  intro C hC; simp only [drEq, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl <;> exact imp1_card _ _
theorem z52 {W : Type} [DecidableEq W] (a b out : DualLit W) :
    ∀ C ∈ drXor a b out, C.card <= 3 := by
  intro C hC; simp only [drXor, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> exact imp2_card _ _ _
theorem z138 {W : Type} [DecidableEq W] (a b out : DualLit W) :
    ∀ C ∈ drAnd a b out, C.card <= 3 := by
  intro C hC; simp only [drAnd, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl <;> exact imp2_card _ _ _
theorem drEq_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    {a b : DualLit W} {v : Bool}
    (ha : dead = false -> lEv α a.1 = !v /\ lEv α a.2 = v)
    (hb : DRMode α dead b v) :
    ∀ C ∈ drEq a b, ClauseSat α C := by
  intro C hC
  simp only [drEq, List.mem_cons, List.not_mem_nil, or_false] at hC
  cases dead
  · obtain ⟨ha1, ha2⟩ := ha rfl
    obtain ⟨hb1, hb2⟩ := hb
    rcases hC with rfl | rfl <;> rw [z6] <;> cases v <;> simp [ha1, ha2, hb1, hb2]
  · obtain ⟨hb1, hb2⟩ := hb
    rcases hC with rfl | rfl <;> rw [z6] <;> simp [hb1, hb2]
theorem drXor_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    {a b out : DualLit W} {va vb : Bool}
    (ha : dead = false -> lEv α a.1 = !va /\ lEv α a.2 = va)
    (hb : dead = false -> lEv α b.1 = !vb /\ lEv α b.2 = vb)
    (ho : DRMode α dead out (xor va vb)) :
    ∀ C ∈ drXor a b out, ClauseSat α C := by
  intro C hC
  simp only [drXor, List.mem_cons, List.not_mem_nil, or_false] at hC
  cases dead
  · obtain ⟨ha1, ha2⟩ := ha rfl
    obtain ⟨hb1, hb2⟩ := hb rfl
    obtain ⟨ho1, ho2⟩ := ho
    rcases hC with rfl | rfl | rfl | rfl <;> rw [z45] <;>
      cases va <;> cases vb <;> simp [ha1, ha2, hb1, hb2, ho1, ho2]
  · obtain ⟨ho1, ho2⟩ := ho
    rcases hC with rfl | rfl | rfl | rfl <;> rw [z45] <;> simp [ho1, ho2]
theorem drAnd_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    {a b out : DualLit W} {va vb : Bool}
    (ha : dead = false -> lEv α a.1 = !va /\ lEv α a.2 = va)
    (hb : dead = false -> lEv α b.1 = !vb /\ lEv α b.2 = vb)
    (ho : DRMode α dead out (va && vb)) :
    ∀ C ∈ drAnd a b out, ClauseSat α C := by
  intro C hC
  simp only [drAnd, List.mem_cons, List.not_mem_nil, or_false] at hC
  cases dead
  · obtain ⟨ha1, ha2⟩ := ha rfl
    obtain ⟨hb1, hb2⟩ := hb rfl
    obtain ⟨ho1, ho2⟩ := ho
    rcases hC with rfl | rfl | rfl | rfl <;> rw [z45] <;>
      cases va <;> cases vb <;> simp [ha1, ha2, hb1, hb2, ho1, ho2]
  · obtain ⟨ho1, ho2⟩ := ho
    rcases hC with rfl | rfl | rfl | rfl <;> rw [z45] <;> simp [ho1, ho2]
theorem drEq_up {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    {a b : DualLit W} {v : Bool}
    (hF : ∀ C ∈ drEq a b, C ∈ F) (ha : drFlip a v ∈ S) : drFlip b v ∈ upS F S := by
  cases v <;> dsimp [drFlip] at ha ⊢
  · exact upS_imp1 (hF _ (by simp [drEq])) ha
  · exact upS_imp1 (hF _ (by simp [drEq])) ha
theorem drXor_up {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    {a b out : DualLit W} {va vb : Bool}
    (hF : ∀ C ∈ drXor a b out, C ∈ F) (ha : drFlip a va ∈ S) (hb : drFlip b vb ∈ S) :
    drFlip out (xor va vb) ∈ upS F S := by
  cases va <;> cases vb <;> dsimp [drFlip] at ha hb ⊢
  · exact upS_imp2 (hF _ (by simp [drXor])) ha hb
  · exact upS_imp2 (hF _ (by simp [drXor])) ha hb
  · exact upS_imp2 (hF _ (by simp [drXor])) ha hb
  · exact upS_imp2 (hF _ (by simp [drXor])) ha hb
theorem drAnd_up {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    {a b out : DualLit W} {va vb : Bool}
    (hF : ∀ C ∈ drAnd a b out, C ∈ F) (ha : drFlip a va ∈ S) (hb : drFlip b vb ∈ S) :
    drFlip out (va && vb) ∈ upS F S := by
  cases va <;> cases vb <;> dsimp [drFlip] at ha hb ⊢
  · exact upS_imp2 (hF _ (by simp [drAnd])) ha hb
  · exact upS_imp2 (hF _ (by simp [drAnd])) ha hb
  · exact upS_imp2 (hF _ (by simp [drAnd])) ha hb
  · exact upS_imp2 (hF _ (by simp [drAnd])) ha hb
def hIdx (d lvl pos : ℕ) : ℕ := 2 ^ (d - lvl) + pos
theorem hIdx_pos (d lvl pos : ℕ) : 1 <= hIdx d lvl pos := by
  dsimp [hIdx]; have := Nat.one_le_pow (d - lvl) 2 (by omega); omega
theorem hIdx_lt {d lvl pos : ℕ} (hlvl : lvl <= d) (hpos : pos < 2 ^ (d - lvl)) :
    hIdx d lvl pos < 2 ^ (d + 1) := by
  dsimp [hIdx]
  have h1 : 2 ^ (d - lvl) <= 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
  omega
theorem z54 {d lvl pos : ℕ} (hlvl : lvl + 1 <= d) (hpos : pos < 2 ^ (d - (lvl + 1))) :
    hIdx d (lvl + 1) pos < 2 ^ d := by
  dsimp [hIdx]
  have h1 : 2 ^ (d - (lvl + 1)) + 2 ^ (d - (lvl + 1)) = 2 ^ (d - lvl) := by
    have : d - lvl = (d - (lvl + 1)) + 1 := by omega
    rw [this, pow_succ]; ring
  have h2 : 2 ^ (d - lvl) <= 2 ^ d := Nat.pow_le_pow_right (by omega) (by omega)
  omega
theorem z44 {d lvl pos : ℕ} (hlvl : lvl + 1 <= d) :
    2 * hIdx d (lvl + 1) pos = hIdx d lvl (2 * pos) /\
    2 * hIdx d (lvl + 1) pos + 1 = hIdx d lvl (2 * pos + 1) := by
  dsimp [hIdx]
  have h1 : d - lvl = (d - (lvl + 1)) + 1 := by omega
  have h2 : 2 * 2 ^ (d - (lvl + 1)) = 2 ^ (d - lvl) := by rw [h1, pow_succ, mul_comm]
  constructor <;> omega
def heapUpVal {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d : ℕ) (u : ℕ) : α :=
  if h1 : u = 0 then e
  else if h2 : u < 2 ^ d then
    op (heapUpVal op e f d (2 * u)) (heapUpVal op e f d (2 * u + 1))
  else if u < 2 ^ (d + 1) then f (u - 2 ^ d)
  else e
termination_by 2 ^ (d + 1) - u
decreasing_by
  · have : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
    omega
  · have : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ, mul_comm]
    omega
theorem z30 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d j : ℕ) (hj : j < 2 ^ d) :
    heapUpVal op e f d (2 ^ d + j) = f j := by
  rw [heapUpVal]
  have hp : 2 ^ d + j ≠ 0 := by have := Nat.one_le_pow d 2 (by omega); omega
  have hge : ¬ (2 ^ d + j < 2 ^ d) := by omega
  have hlt : 2 ^ d + j < 2 ^ (d + 1) := by rw [pow_succ]; omega
  simp [hp, hge, hlt]
theorem z79 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d u : ℕ)
    (hu1 : 1 <= u) (hu2 : u < 2 ^ d) :
    heapUpVal op e f d u = op (heapUpVal op e f d (2 * u)) (heapUpVal op e f d (2 * u + 1)) := by
  rw [heapUpVal]
  have hne : u ≠ 0 := by omega
  simp [hne, hu2]
def z17 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d : ℕ) (u : ℕ) : α :=
  if h : u <= 1 then e
  else if u % 2 = 0 then z17 op e f d (u / 2)
  else op (z17 op e f d (u / 2)) (heapUpVal op e f d (u - 1))
termination_by u
theorem z60 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d : ℕ) :
    z17 op e f d 1 = e := by rw [z17]; simp
theorem z76 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d u : ℕ) (hu : 1 <= u) :
    z17 op e f d (2 * u) = z17 op e f d u := by
  rw [z17]; have h1 : ¬ (2 * u <= 1) := by omega
  have h2 : (2 * u) % 2 = 0 := by omega
  have h3 : (2 * u) / 2 = u := by omega
  simp [h1, h2, h3]
theorem z85 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d u : ℕ) (hu : 1 <= u) :
    z17 op e f d (2 * u + 1) = op (z17 op e f d u) (heapUpVal op e f d (2 * u)) := by
  rw [z17]; have h1 : ¬ (2 * u + 1 <= 1) := by omega
  have h2 : (2 * u + 1) % 2 ≠ 0 := by omega
  have h3 : (2 * u + 1) / 2 = u := by omega
  simp [h1, h2, h3]
def z33 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d : ℕ) (u : ℕ) : α :=
  if h : u <= 1 then e
  else if u % 2 = 1 then z33 op e f d (u / 2)
  else op (heapUpVal op e f d (u + 1)) (z33 op e f d (u / 2))
termination_by u
theorem z126 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d : ℕ) :
    z33 op e f d 1 = e := by rw [z33]; simp
theorem z150 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d u : ℕ) (hu : 1 <= u) :
    z33 op e f d (2 * u) = op (heapUpVal op e f d (2 * u + 1)) (z33 op e f d u) := by
  rw [z33]; have h1 : ¬ (2 * u <= 1) := by omega
  have h2 : (2 * u) % 2 ≠ 1 := by omega
  have h3 : (2 * u) / 2 = u := by omega
  simp [h1, h2, h3]
theorem z110 {α : Type} (op : α -> α -> α) (e : α) (f : ℕ -> α) (d u : ℕ) (hu : 1 <= u) :
    z33 op e f d (2 * u + 1) = z33 op e f d u := by
  rw [z33]; have h1 : ¬ (2 * u + 1 <= 1) := by omega
  have h2 : (2 * u + 1) % 2 = 1 := by omega
  have h3 : (2 * u + 1) / 2 = u := by omega
  simp [h1, h2, h3]
def z23 (f : ℕ -> Bool) (d : ℕ) (u : ℕ) : Bool :=
  if h : u <= 1 then false
  else if u % 2 = 0 then xor (z23 f d (u / 2)) (heapUpVal xor false f d (u + 1))
  else xor (z23 f d (u / 2)) (heapUpVal xor false f d (u - 1))
termination_by u
theorem z139 (f : ℕ -> Bool) (d : ℕ) : z23 f d 1 = false := by
  rw [z23]; simp
theorem z140 (f : ℕ -> Bool) (d u : ℕ) (hu : 1 <= u) :
    z23 f d (2 * u) = xor (z23 f d u) (heapUpVal xor false f d (2 * u + 1)) := by
  rw [z23]; have h1 : ¬ (2 * u <= 1) := by omega
  have h2 : (2 * u) % 2 = 0 := by omega
  have h3 : (2 * u) / 2 = u := by omega
  simp [h1, h2, h3]
theorem z131 (f : ℕ -> Bool) (d u : ℕ) (hu : 1 <= u) :
    z23 f d (2 * u + 1) = xor (z23 f d u) (heapUpVal xor false f d (2 * u)) := by
  rw [z23]; have h1 : ¬ (2 * u + 1 <= 1) := by omega
  have h2 : (2 * u + 1) % 2 ≠ 0 := by omega
  have h3 : (2 * u + 1) / 2 = u := by omega
  simp [h1, h2, h3]
theorem z65 {α : Type} (op : α -> α -> α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a)
    (l1 l2 : List α) :
    (l1 ++ l2).foldr op e = op (l1.foldr op e) (l2.foldr op e) := by
  induction l1 with
  | nil => simp [hidl]
  | cons a l1 ih => simp [ih, hassoc]
theorem z143 {α : Type} (f : ℕ -> α) (a b : ℕ) :
    (List.range (a + b)).map f = (List.range a).map f ++ (List.range b).map (fun t => f (a + t)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.map_singleton, ih,
      List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
theorem z77 {α : Type} (op : α -> α -> α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a)
    (f : ℕ -> α) (d : ℕ) :
    ∀ (lvl pos : ℕ), lvl <= d -> pos < 2 ^ (d - lvl) ->
      heapUpVal op e f d (hIdx d lvl pos) =
        ((List.range (2 ^ lvl)).map (fun t => f (pos * 2 ^ lvl + t))).foldr op e
  | 0, pos, _, hpos => by
    have h0 : hIdx d 0 pos = 2 ^ d + pos := by simp [hIdx]
    rw [h0, z30 op e f d pos (by simpa using hpos)]
    simp [hidr]
  | lvl + 1, pos, hlvl, hpos => by
    have hu1 := hIdx_pos d (lvl + 1) pos
    have hu2 := z54 hlvl hpos
    rw [z79 op e f d _ hu1 hu2]
    obtain ⟨hl, hr⟩ := z44 hlvl (pos := pos)
    rw [hr, hl]
    have h2pos : 2 * pos < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have h2pos1 : 2 * pos + 1 < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    rw [z77 op e hassoc hidl hidr f d lvl (2 * pos) (by omega) h2pos,
        z77 op e hassoc hidl hidr f d lvl (2 * pos + 1) (by omega) h2pos1,
        ← z65 op e hassoc hidl hidr]
    have hpow : 2 ^ (lvl + 1) = 2 ^ lvl + 2 ^ lvl := by rw [pow_succ]; ring
    rw [hpow, z143]
    congr 1; congr 1
    · refine List.map_congr_left fun t _ => congrArg f (by ring)
    · refine List.map_congr_left fun t _ => congrArg f (by ring)
theorem z84 {α : Type} (op : α -> α -> α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a)
    (f : ℕ -> α) (d : ℕ) :
    heapUpVal op e f d 1 = ((List.range (2 ^ d)).map f).foldr op e := by
  have h := z77 op e hassoc hidl hidr f d d 0 (le_refl d) (by simp)
  simpa [hIdx] using h
theorem z99 {α : Type} (op : α -> α -> α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a)
    (f : ℕ -> α) {n m : ℕ} (hnm : n <= m) (hpad : ∀ j, n <= j -> f j = e) :
    ((List.range m).map f).foldr op e = ((List.range n).map f).foldr op e := by
  have hm : m = n + (m - n) := by omega
  rw [hm, z143, z65 op e hassoc hidl hidr]
  have hz : ∀ k : ℕ, ((List.range k).map (fun t => f (n + t))).foldr op e = e := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.map_singleton,
        z65 op e hassoc hidl hidr, ih, hpad (n + k) (by omega)]
      simp [hidr]
  rw [hz, hidr]
theorem z82 {α : Type} (op : α -> α -> α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a)
    (f : ℕ -> α) (d : ℕ) :
    ∀ (k : ℕ) (pos : ℕ), k <= d -> pos < 2 ^ k ->
      z17 op e f d (hIdx d (d - k) pos) =
        ((List.range (pos * 2 ^ (d - k))).map f).foldr op e
  | 0, pos, _, hpos => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    rw [this, z60]; simp
  | k + 1, pos, hk, hpos => by
    have hpar : pos / 2 < 2 ^ k := by rw [pow_succ] at hpos; omega
    have ih := z82 op e hassoc hidl hidr f d k (pos / 2) (by omega) hpar
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := pos / 2) (by omega)
    rw [hlvl] at hl hr
    have hu1 := hIdx_pos d (d - k) (pos / 2)
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hqdiv : pos / 2 = q := by omega
      rw [hqdiv] at ih hl hr hu1
      rw [hq, ← hl, z76 op e f d _ hu1, ih]
      congr 2; rw [← hlvl, pow_succ]; ring
    · have hqdiv : pos / 2 = q := by omega
      rw [hqdiv] at ih hl hr hu1
      rw [hq, ← hr, z85 op e f d _ hu1, ih, hl]
      have hup := z77 op e hassoc hidl hidr f d (d - (k + 1)) (2 * q) (by omega)
        (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)
      rw [hup, ← z65 op e hassoc hidl hidr,
        show (2 * q + 1) * 2 ^ (d - (k + 1)) = q * 2 ^ (d - k) + 2 ^ (d - (k + 1)) by
          rw [← hlvl, pow_succ]; ring, z143]
      congr 2; ext t; congr 1; rw [← hlvl, pow_succ]; ring
theorem z147 {α : Type} (op : α -> α -> α) (e : α)
    (hassoc : ∀ a b c, op (op a b) c = op a (op b c))
    (hidl : ∀ a, op e a = a) (hidr : ∀ a, op a e = a)
    (f : ℕ -> α) (d : ℕ) :
    ∀ (k : ℕ) (pos : ℕ), k <= d -> pos < 2 ^ k ->
      z33 op e f d (hIdx d (d - k) pos) =
        ((List.range (2 ^ d - (pos + 1) * 2 ^ (d - k))).map
          (fun t => f ((pos + 1) * 2 ^ (d - k) + t))).foldr op e
  | 0, pos, _, hpos => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    rw [this, z126]; simp
  | k + 1, pos, hk, hpos => by
    have hpar : pos / 2 < 2 ^ k := by rw [pow_succ] at hpos; omega
    have ih := z147 op e hassoc hidl hidr f d k (pos / 2) (by omega) hpar
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := pos / 2) (by omega)
    rw [hlvl] at hl hr
    have hu1 := hIdx_pos d (d - k) (pos / 2)
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hqdiv : pos / 2 = q := by omega
      rw [hqdiv] at ih hl hr hu1
      rw [hq, ← hl, z150 op e f d _ hu1, ih, hr]
      have hup := z77 op e hassoc hidl hidr f d (d - (k + 1)) (2 * q + 1) (by omega)
        (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)
      rw [hup, ← z65 op e hassoc hidl hidr]
      have hle1 : (q + 1) * 2 ^ (d - k) <= 2 ^ d := by
        have h1 : q + 1 <= 2 ^ k := by omega
        have h2 : 2 ^ k * 2 ^ (d - k) = 2 ^ d := by rw [← Nat.pow_add, Nat.add_sub_of_le (by omega)]
        calc (q + 1) * 2 ^ (d - k) <= 2 ^ k * 2 ^ (d - k) := Nat.mul_le_mul_right _ h1
          _ = 2 ^ d := h2
      have hgap : (q + 1) * 2 ^ (d - k) = (2 * q + 1) * 2 ^ (d - (k + 1)) + 2 ^ (d - (k + 1)) := by
        rw [← hlvl, pow_succ]; ring
      have hlen : 2 ^ d - (2 * q + 1) * 2 ^ (d - (k + 1)) =
          2 ^ (d - (k + 1)) + (2 ^ d - (q + 1) * 2 ^ (d - k)) := by
        have hsum : (2 * q + 1) * 2 ^ (d - (k + 1)) +
            (2 ^ (d - (k + 1)) + (2 ^ d - (q + 1) * 2 ^ (d - k))) = 2 ^ d := by
          rw [← Nat.add_assoc, ← hgap, Nat.add_sub_of_le hle1]
        exact (Nat.eq_sub_of_add_eq' hsum).symm
      rw [hlen, z143]
      congr 2; refine List.map_congr_left fun t _ => congrArg f (by
        rw [← Nat.add_assoc, ← hgap])
    · have hqdiv : pos / 2 = q := by omega
      rw [hqdiv] at ih hl hr hu1
      rw [hq, ← hr, z110 op e f d _ hu1, ih]
      have hmul : (2 * q + 1 + 1) * 2 ^ (d - (k + 1)) = (q + 1) * 2 ^ (d - k) := by
        rw [← hlvl, pow_succ]; ring
      rw [hmul]
theorem z105 (f : ℕ -> Bool) (d : ℕ) :
    ∀ (k : ℕ) (pos : ℕ), k <= d -> pos < 2 ^ k ->
      xor (heapUpVal xor false f d (hIdx d (d - k) pos))
          (z23 f d (hIdx d (d - k) pos)) = heapUpVal xor false f d 1
  | 0, pos, _, hpos => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    rw [this, z139, Bool.xor_false]
  | k + 1, pos, hk, hpos => by
    have hpar : pos / 2 < 2 ^ k := by rw [pow_succ] at hpos; omega
    have ih := z105 f d k (pos / 2) (by omega) hpar
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := pos / 2) (by omega)
    rw [hlvl] at hl hr
    have hu1 := hIdx_pos d (d - k) (pos / 2)
    have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := pos / 2) (by omega)
      (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
    rw [hlvl] at hu2
    have hnode := z79 xor false f d _ hu1 hu2
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hqdiv : pos / 2 = q := by omega
      rw [hqdiv] at ih hl hr hu1 hnode
      rw [hq, ← hl, z140 f d _ hu1, ← ih, hnode]
      cases heapUpVal xor false f d (2 * hIdx d (d - k) q) <;>
        cases heapUpVal xor false f d (2 * hIdx d (d - k) q + 1) <;>
        cases z23 f d (hIdx d (d - k) q) <;> rfl
    · have hqdiv : pos / 2 = q := by omega
      rw [hqdiv] at ih hl hr hu1 hnode
      rw [hq, ← hr, z131 f d _ hu1, ← ih, hnode]
      cases heapUpVal xor false f d (2 * hIdx d (d - k) q) <;>
        cases heapUpVal xor false f d (2 * hIdx d (d - k) q + 1) <;>
        cases z23 f d (hIdx d (d - k) q) <;> rfl
def z14 {W : Type} [DecidableEq W] (d : ℕ)
    (up : Fin (2 ^ (d + 1)) -> DualLit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      drXor (up ⟨2 * u, h2u⟩) (up ⟨2 * u + 1, h2u1⟩) (up ⟨u, hu⟩)
    else []
theorem z72 {W : Type} [DecidableEq W] (d : ℕ)
    (up : Fin (2 ^ (d + 1)) -> DualLit W) :
    ∀ C ∈ z14 d up, C.card <= 3 := by
  intro C hC
  rw [z14, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩
  split_ifs at hCu with h
  · exact z52 _ _ _ C hCu
  · simp at hCu
theorem z63 {W : Type} [DecidableEq W] (d : ℕ)
    (up : Fin (2 ^ (d + 1)) -> DualLit W) :
    (z14 d up).length <= 4 * 2 ^ d := by
  dsimp [z14]
  have hlen : ∀ (L : List ℕ) (f : ℕ -> List (Cl W)), (∀ x ∈ L, (f x).length <= 4) ->
      (L.flatMap f).length <= 4 * L.length := by
    intro L f hf; induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := hf a (List.mem_cons_self ..)
      have h2 := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
      omega
  refine le_trans (hlen (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
  split_ifs <;> simp [drXor]
theorem z81 {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    (d : ℕ) (f : ℕ -> Bool) (up : Fin (2 ^ (d + 1)) -> DualLit W)
    (hup : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> DRMode α dead (up u) (heapUpVal xor false f d u.val)) :
    ∀ C ∈ z14 d up, ClauseSat α C := by
  intro C hC
  rw [z14, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩
  split_ifs at hCu with h
  · have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have ho := hup ⟨u, hu⟩ h.1
    rw [z79 xor false f d u h.1 h.2] at ho
    exact drXor_sat
      (fun hd => by simpa [DRMode, hd] using hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega))
      (fun hd => by simpa [DRMode, hd] using hup ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega))
      ho C hCu
  · simp at hCu
theorem z55 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (f : ℕ -> Bool) (up : Fin (2 ^ (d + 1)) -> DualLit W)
    (hF : ∀ C ∈ z14 d up, C ∈ F)
    (bad : ℕ -> Prop) (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d), ¬ bad j ->
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩) (f j) ∈ (upS F)^[t0] S) :
    ∀ (lvl pos : ℕ) (hlvl : lvl <= d) (hpos : pos < 2 ^ (d - lvl)),
      (∀ j, pos * 2 ^ lvl <= j -> j < (pos + 1) * 2 ^ lvl -> ¬ bad j) ->
      drFlip (up ⟨hIdx d lvl pos, hIdx_lt hlvl hpos⟩)
        (heapUpVal xor false f d (hIdx d lvl pos)) ∈ (upS F)^[t0 + lvl] S
  | 0, pos, hlvl, hpos, hok => by
    have h0 : hIdx d 0 pos = 2 ^ d + pos := by simp [hIdx]
    have hpos' : pos < 2 ^ d := by simpa using hpos
    simp only [Nat.add_zero]
    have hnb : ¬ bad pos := hok pos (by simp) (by simp)
    have hl := hleaf pos hpos' hnb
    have hEq : (⟨hIdx d 0 pos, hIdx_lt hlvl hpos⟩ : Fin (2 ^ (d + 1))) =
        ⟨2 ^ d + pos, by rw [pow_succ]; omega⟩ := Fin.ext h0
    rw [hEq, h0, z30 xor false f d pos hpos']
    exact hl
  | lvl + 1, pos, hlvl, hpos, hok => by
    have hu1 := hIdx_pos d (lvl + 1) pos
    have hu2 := z54 hlvl hpos
    obtain ⟨hl, hr⟩ := z44 hlvl (pos := pos)
    have h2p : 2 * pos < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have h2p1 : 2 * pos + 1 < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have ihL := z55 d f up hF bad t0 hleaf lvl (2 * pos) (by omega) h2p
      (fun j hj1 hj2 => hok j (by rw [pow_succ]; nlinarith) (by rw [pow_succ]; nlinarith))
    have ihR := z55 d f up hF bad t0 hleaf lvl (2 * pos + 1) (by omega) h2p1
      (fun j hj1 hj2 => hok j (by rw [pow_succ]; nlinarith) (by rw [pow_succ]; nlinarith))
    rw [show t0 + (lvl + 1) = (t0 + lvl) + 1 by omega, Function.iterate_succ_apply',
      z79 xor false f d _ hu1 hu2]
    have hCsub : ∀ C ∈ drXor (up ⟨2 * hIdx d (lvl + 1) pos, by rw [pow_succ]; omega⟩)
        (up ⟨2 * hIdx d (lvl + 1) pos + 1, by rw [pow_succ]; omega⟩)
        (up ⟨hIdx d (lvl + 1) pos, hIdx_lt hlvl hpos⟩), C ∈ F := by
      intro C hC
      apply hF
      rw [z14, List.mem_flatMap]
      refine ⟨hIdx d (lvl + 1) pos, List.mem_range.mpr hu2, ?_⟩
      simp [hu1, hu2, hC]
    have hL' : drFlip (up ⟨2 * hIdx d (lvl + 1) pos, by rw [pow_succ]; omega⟩)
        (heapUpVal xor false f d (2 * hIdx d (lvl + 1) pos)) ∈ (upS F)^[t0 + lvl] S := by
      simpa [hl] using ihL
    have hR' : drFlip (up ⟨2 * hIdx d (lvl + 1) pos + 1, by rw [pow_succ]; omega⟩)
        (heapUpVal xor false f d (2 * hIdx d (lvl + 1) pos + 1)) ∈ (upS F)^[t0 + lvl] S := by
      simpa [hr] using ihR
    exact drXor_up hCsub hL' hR'
def z27 {W : Type} [DecidableEq W] (d : ℕ)
    (up dn : Fin (2 ^ (d + 1)) -> DualLit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      drXor (dn ⟨u, hu⟩) (up ⟨2 * u + 1, h2u1⟩) (dn ⟨2 * u, h2u⟩) ++
      drXor (dn ⟨u, hu⟩) (up ⟨2 * u, h2u⟩) (dn ⟨2 * u + 1, h2u1⟩)
    else []
theorem heapXorCompClauses_card {W : Type} [DecidableEq W] (d : ℕ)
    (up dn : Fin (2 ^ (d + 1)) -> DualLit W) :
    ∀ C ∈ z27 d up dn, C.card <= 3 := by
  intro C hC
  rw [z27, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩
  split_ifs at hCu with h
  · rw [List.mem_append] at hCu
    rcases hCu with h1 | h2
    · exact z52 _ _ _ C h1
    · exact z52 _ _ _ C h2
  · simp at hCu
theorem z160 {W : Type} [DecidableEq W] (d : ℕ)
    (up dn : Fin (2 ^ (d + 1)) -> DualLit W) :
    (z27 d up dn).length <= 8 * 2 ^ d := by
  dsimp [z27]
  have hlen : ∀ (L : List ℕ) (f : ℕ -> List (Cl W)), (∀ x ∈ L, (f x).length <= 8) ->
      (L.flatMap f).length <= 8 * L.length := by
    intro L f hf; induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := hf a (List.mem_cons_self ..)
      have h2 := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
      omega
  refine le_trans (hlen (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
  split_ifs <;> simp [drXor]
theorem heapXorCompClauses_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    (d : ℕ) (f : ℕ -> Bool) (up dn : Fin (2 ^ (d + 1)) -> DualLit W)
    (hup : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> DRMode α dead (up u) (heapUpVal xor false f d u.val))
    (hdn : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> DRMode α dead (dn u) (z23 f d u.val)) :
    ∀ C ∈ z27 d up dn, ClauseSat α C := by
  intro C hC
  rw [z27, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩
  split_ifs at hCu with h
  · have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    rw [List.mem_append] at hCu
    rcases hCu with h1 | h2
    · have ho := hdn ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)
      rw [z140 f d u h.1] at ho
      exact drXor_sat
        (fun hd => by simpa [DRMode, hd] using hdn ⟨u, hu⟩ h.1)
        (fun hd => by simpa [DRMode, hd] using hup ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega))
        ho C h1
    · have ho := hdn ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)
      rw [z131 f d u h.1] at ho
      exact drXor_sat
        (fun hd => by simpa [DRMode, hd] using hdn ⟨u, hu⟩ h.1)
        (fun hd => by simpa [DRMode, hd] using hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega))
        ho C h2
  · simp at hCu
theorem z134 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (f : ℕ -> Bool) (up dn : Fin (2 ^ (d + 1)) -> DualLit W)
    (hFup : ∀ C ∈ z14 d up, C ∈ F)
    (hFdn : ∀ C ∈ z27 d up dn, C ∈ F)
    (i0 : ℕ) (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d), j ≠ i0 ->
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩) (f j) ∈ (upS F)^[t0] S)
    (hroot : drFlip (dn ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩) false ∈
      (upS F)^[t0 + d] S) :
    ∀ (k : ℕ) (hk : k <= d) (pos : ℕ) (hpos : pos < 2 ^ k),
      pos * 2 ^ (d - k) <= i0 -> i0 < (pos + 1) * 2 ^ (d - k) ->
      drFlip (dn ⟨hIdx d (d - k) pos, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpos)⟩)
        (z23 f d (hIdx d (d - k) pos)) ∈ (upS F)^[t0 + d + k] S
  | 0, hk, pos, hpos, _, _ => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have h1 : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    simp only [Nat.add_zero]
    have hEq : (⟨hIdx d (d - 0) 0, hIdx_lt (by omega) (by simp)⟩ : Fin (2 ^ (d + 1))) =
        ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩ := Fin.ext h1
    rw [hEq, h1, z139]; exact hroot
  | k + 1, hk, pos, hpos, hi1, hi2 => by
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    rw [show t0 + d + (k + 1) = (t0 + d + k) + 1 by omega, Function.iterate_succ_apply']
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := z134 d f up dn hFup hFdn i0 t0 hleaf hroot k (by omega) q hpar
        (by rw [← hlvl, pow_succ]; nlinarith)
        (by rw [← hlvl, pow_succ]; nlinarith)
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hRsib : drFlip (up ⟨hIdx d (d - (k + 1)) (2 * q + 1),
          hIdx_lt (by omega) (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)⟩)
          (heapUpVal xor false f d (hIdx d (d - (k + 1)) (2 * q + 1))) ∈
          (upS F)^[t0 + (d - (k + 1))] S :=
        z55 d f up hFup (· = i0) t0 hleaf (d - (k + 1)) (2 * q + 1) (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)
          (fun j hj1 _ => by rw [hq] at hi2; omega)
      have hRsib' := z5 F S (by omega : t0 + (d - (k + 1)) <= t0 + d + k) hRsib
      have hCsub : ∀ C ∈ drXor
          (dn ⟨hIdx d (d - k) q, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpar)⟩)
          (up ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩)
          (dn ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply hFdn
        rw [z27, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hres := drXor_up hCsub ih (by simpa [hr] using hRsib')
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hl])
      rw [hEq, hq, ← hl, z140 f d _ hu1]
      simpa [hr] using hres
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := z134 d f up dn hFup hFdn i0 t0 hleaf hroot k (by omega) q hpar
        (by rw [← hlvl, pow_succ]; nlinarith)
        (by rw [← hlvl, pow_succ]; nlinarith)
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hLsib : drFlip (up ⟨hIdx d (d - (k + 1)) (2 * q),
          hIdx_lt (by omega) (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)⟩)
          (heapUpVal xor false f d (hIdx d (d - (k + 1)) (2 * q))) ∈
          (upS F)^[t0 + (d - (k + 1))] S :=
        z55 d f up hFup (· = i0) t0 hleaf (d - (k + 1)) (2 * q) (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)
          (fun j _ hj2 => by rw [hq] at hi1; omega)
      have hLsib' := z5 F S (by omega : t0 + (d - (k + 1)) <= t0 + d + k) hLsib
      have hCsub : ∀ C ∈ drXor
          (dn ⟨hIdx d (d - k) q, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpar)⟩)
          (up ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩)
          (dn ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply hFdn
        rw [z27, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hres := drXor_up hCsub ih (by simpa [hl] using hLsib')
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hr])
      rw [hEq, hq, ← hr, z131 f d _ hu1]
      simpa [hl] using hres
def z18 {W : Type} [DecidableEq W] (d : ℕ)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      drEq (pr ⟨u, hu⟩) (pr ⟨2 * u, h2u⟩) ++
      drXor (pr ⟨u, hu⟩) (up ⟨2 * u, h2u⟩) (pr ⟨2 * u + 1, h2u1⟩)
    else []
theorem z114 {W : Type} [DecidableEq W] (d : ℕ)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W) :
    ∀ C ∈ z18 d up pr, C.card <= 3 := by
  intro C hC
  rw [z18, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩
  split_ifs at hCu with h
  · rw [List.mem_append] at hCu
    rcases hCu with h1 | h2
    · exact drEq_card _ _ C h1
    · exact z52 _ _ _ C h2
  · simp at hCu
theorem z107 {W : Type} [DecidableEq W] (d : ℕ)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W) :
    (z18 d up pr).length <= 6 * 2 ^ d := by
  dsimp [z18]
  have hlen : ∀ (L : List ℕ) (f : ℕ -> List (Cl W)), (∀ x ∈ L, (f x).length <= 6) ->
      (L.flatMap f).length <= 6 * L.length := by
    intro L f hf; induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := hf a (List.mem_cons_self ..)
      have h2 := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
      omega
  refine le_trans (hlen (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
  split_ifs <;> simp [drEq, drXor]
theorem z129 {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    (d : ℕ) (f : ℕ -> Bool) (up pr : Fin (2 ^ (d + 1)) -> DualLit W)
    (hup : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> DRMode α dead (up u) (heapUpVal xor false f d u.val))
    (hpr : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> DRMode α dead (pr u) (z17 xor false f d u.val)) :
    ∀ C ∈ z18 d up pr, ClauseSat α C := by
  intro C hC
  rw [z18, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩
  split_ifs at hCu with h
  · have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    rw [List.mem_append] at hCu
    rcases hCu with h1 | h2
    · have ho := hpr ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)
      rw [z76 xor false f d u h.1] at ho
      exact drEq_sat (fun hd => by simpa [DRMode, hd] using hpr ⟨u, hu⟩ h.1) ho C h1
    · have ho := hpr ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)
      rw [z85 xor false f d u h.1] at ho
      exact drXor_sat
        (fun hd => by simpa [DRMode, hd] using hpr ⟨u, hu⟩ h.1)
        (fun hd => by simpa [DRMode, hd] using hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega))
        ho C h2
  · simp at hCu
theorem z133 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (f : ℕ -> Bool) (up pr : Fin (2 ^ (d + 1)) -> DualLit W)
    (hFup : ∀ C ∈ z14 d up, C ∈ F)
    (hFpr : ∀ C ∈ z18 d up pr, C ∈ F)
    (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d),
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩) (f j) ∈ (upS F)^[t0] S)
    (hroot : drFlip (pr ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩) false ∈
      (upS F)^[t0 + d] S) :
    ∀ (k : ℕ) (hk : k <= d) (pos : ℕ) (hpos : pos < 2 ^ k),
      drFlip (pr ⟨hIdx d (d - k) pos, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpos)⟩)
        (z17 xor false f d (hIdx d (d - k) pos)) ∈ (upS F)^[t0 + d + k] S
  | 0, hk, pos, hpos => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have h1 : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    simp only [Nat.add_zero]
    have hEq : (⟨hIdx d (d - 0) 0, hIdx_lt (by omega) (by simp)⟩ : Fin (2 ^ (d + 1))) =
        ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩ := Fin.ext h1
    rw [hEq, h1, z60]; exact hroot
  | k + 1, hk, pos, hpos => by
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    rw [show t0 + d + (k + 1) = (t0 + d + k) + 1 by omega, Function.iterate_succ_apply']
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := z133 d f up pr hFup hFpr t0 hleaf hroot k (by omega) q hpar
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hCsub : ∀ C ∈ drEq
          (pr ⟨hIdx d (d - k) q, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpar)⟩)
          (pr ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply hFpr
        rw [z18, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hres := drEq_up hCsub ih
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hl])
      rw [hEq, hq, ← hl, z76 xor false f d _ hu1]
      exact hres
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := z133 d f up pr hFup hFpr t0 hleaf hroot k (by omega) q hpar
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hLsib : drFlip (up ⟨hIdx d (d - (k + 1)) (2 * q),
          hIdx_lt (by omega) (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)⟩)
          (heapUpVal xor false f d (hIdx d (d - (k + 1)) (2 * q))) ∈
          (upS F)^[t0 + (d - (k + 1))] S :=
        z55 d f up hFup (fun _ => False) t0 (fun j hj _ => hleaf j hj)
          (d - (k + 1)) (2 * q) (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega) (fun _ _ _ h => h)
      have hLsib' := z5 F S (by omega : t0 + (d - (k + 1)) <= t0 + d + k) hLsib
      have hCsub : ∀ C ∈ drXor
          (pr ⟨hIdx d (d - k) q, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpar)⟩)
          (up ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩)
          (pr ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply hFpr
        rw [z18, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hres := drXor_up hCsub ih (by simpa [hl] using hLsib')
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hr])
      rw [hEq, hq, ← hr, z85 xor false f d _ hu1]
      simpa [hl] using hres
def drAffComp {W : Type} [DecidableEq W]
    (x y out : DualLit W × DualLit W) (tmp : DualLit W) : List (Cl W) :=
  drAnd x.1 y.1 out.1 ++ drAnd x.1 y.2 tmp ++ drXor x.2 tmp out.2
theorem z135 {W : Type} [DecidableEq W]
    (x y out : DualLit W × DualLit W) (tmp : DualLit W) :
    ∀ C ∈ drAffComp x y out tmp, C.card <= 3 := by
  intro C hC
  simp only [drAffComp, List.mem_append] at hC
  rcases hC with (h1 | h2) | h3
  · exact z138 _ _ _ C h1
  · exact z138 _ _ _ C h2
  · exact z52 _ _ _ C h3
theorem z145 {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    {x y out : DualLit W × DualLit W} {tmp : DualLit W} {vx vy : Bool × Bool}
    (hx1 : dead = false -> lEv α x.1.1 = !vx.1 /\ lEv α x.1.2 = vx.1)
    (hx2 : dead = false -> lEv α x.2.1 = !vx.2 /\ lEv α x.2.2 = vx.2)
    (hy1 : dead = false -> lEv α y.1.1 = !vy.1 /\ lEv α y.1.2 = vy.1)
    (hy2 : dead = false -> lEv α y.2.1 = !vy.2 /\ lEv α y.2.2 = vy.2)
    (htmp : DRMode α dead tmp (vx.1 && vy.2))
    (ho1 : DRMode α dead out.1 (affComp vx vy).1)
    (ho2 : DRMode α dead out.2 (affComp vx vy).2) :
    ∀ C ∈ drAffComp x y out tmp, ClauseSat α C := by
  intro C hC
  simp only [drAffComp, List.mem_append] at hC
  rcases hC with (h1 | h2) | h3
  · exact drAnd_sat hx1 hy1 ho1 C h1
  · exact drAnd_sat hx1 hy2 htmp C h2
  · exact drXor_sat hx2 (fun hd => by simpa [DRMode, hd] using htmp) ho2 C h3
theorem z162 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    {x y out : DualLit W × DualLit W} {tmp : DualLit W} {vx vy : Bool × Bool}
    (hF : ∀ C ∈ drAffComp x y out tmp, C ∈ F)
    (hx1 : drFlip x.1 vx.1 ∈ S) (hx2 : drFlip x.2 vx.2 ∈ S)
    (hy1 : drFlip y.1 vy.1 ∈ S) (hy2 : drFlip y.2 vy.2 ∈ S) :
    drFlip out.1 (affComp vx vy).1 ∈ (upS F)^[2] S /\
    drFlip out.2 (affComp vx vy).2 ∈ (upS F)^[2] S := by
  have h1 : drFlip out.1 (vx.1 && vy.1) ∈ upS F S :=
    drAnd_up (fun C hC => hF C (by simp [drAffComp, hC])) hx1 hy1
  have htmp : drFlip tmp (vx.1 && vy.2) ∈ upS F S :=
    drAnd_up (fun C hC => hF C (by simp [drAffComp, hC])) hx1 hy2
  have hx2' : drFlip x.2 vx.2 ∈ upS F S := z136 F S hx2
  have h2 : drFlip out.2 (xor vx.2 (vx.1 && vy.2)) ∈ upS F (upS F S) :=
    drXor_up (fun C hC => hF C (by simp [drAffComp, hC])) hx2' htmp
  exact ⟨z136 F _ h1, h2⟩
def z39 {W : Type} [DecidableEq W] (d : ℕ)
    (up : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tmp : Fin (2 ^ (d + 1)) -> DualLit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      drAffComp (up ⟨2 * u, h2u⟩) (up ⟨2 * u + 1, h2u1⟩) (up ⟨u, hu⟩) (tmp ⟨u, hu⟩)
    else []
def z28 {W : Type} [DecidableEq W] (d : ℕ)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tmp : Fin (2 ^ (d + 1)) -> DualLit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      drEq (pr ⟨u, hu⟩).1 (pr ⟨2 * u, h2u⟩).1 ++
      drEq (pr ⟨u, hu⟩).2 (pr ⟨2 * u, h2u⟩).2 ++
      drAffComp (pr ⟨u, hu⟩) (up ⟨2 * u, h2u⟩) (pr ⟨2 * u + 1, h2u1⟩) (tmp ⟨2 * u + 1, h2u1⟩)
    else []
def z36 {W : Type} [DecidableEq W] (d : ℕ)
    (up sf : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tmp : Fin (2 ^ (d + 1)) -> DualLit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      drAffComp (up ⟨2 * u + 1, h2u1⟩) (sf ⟨u, hu⟩) (sf ⟨2 * u, h2u⟩) (tmp ⟨2 * u, h2u⟩) ++
      drEq (sf ⟨u, hu⟩).1 (sf ⟨2 * u + 1, h2u1⟩).1 ++
      drEq (sf ⟨u, hu⟩).2 (sf ⟨2 * u + 1, h2u1⟩).2
    else []
theorem heapAffUpClauses_card {W : Type} [DecidableEq W] (d : ℕ)
    (up : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W) (tmp : Fin (2 ^ (d + 1)) -> DualLit W) :
    ∀ C ∈ z39 d up tmp, C.card <= 3 := by
  intro C hC; rw [z39, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · exact z135 _ _ _ _ C hCu
  · simp at hCu
theorem heapAffPrefClauses_card {W : Type} [DecidableEq W] (d : ℕ)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W) (tmp : Fin (2 ^ (d + 1)) -> DualLit W) :
    ∀ C ∈ z28 d up pr tmp, C.card <= 3 := by
  intro C hC; rw [z28, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · simp only [List.mem_append] at hCu
    rcases hCu with (h1 | h2) | h3
    · exact drEq_card _ _ C h1
    · exact drEq_card _ _ C h2
    · exact z135 _ _ _ _ C h3
  · simp at hCu
theorem heapAffSufClauses_card {W : Type} [DecidableEq W] (d : ℕ)
    (up sf : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W) (tmp : Fin (2 ^ (d + 1)) -> DualLit W) :
    ∀ C ∈ z36 d up sf tmp, C.card <= 3 := by
  intro C hC; rw [z36, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · simp only [List.mem_append] at hCu
    rcases hCu with (h1 | h2) | h3
    · exact z135 _ _ _ _ C h1
    · exact drEq_card _ _ C h2
    · exact drEq_card _ _ C h3
  · simp at hCu
theorem heapAff_lengths {W : Type} [DecidableEq W] (d : ℕ)
    (up pr sf : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tu tp ts : Fin (2 ^ (d + 1)) -> DualLit W) :
    (z39 d up tu).length <= 12 * 2 ^ d /\
    (z28 d up pr tp).length <= 16 * 2 ^ d /\
    (z36 d up sf ts).length <= 16 * 2 ^ d := by
  have hlen : ∀ (c : ℕ) (L : List ℕ) (f : ℕ -> List (Cl W)), (∀ x ∈ L, (f x).length <= c) ->
      (L.flatMap f).length <= c * L.length := by
    intro c L f hf; induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := hf a (List.mem_cons_self ..)
      have h2 := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
      nlinarith
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans (hlen 12 (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
    dsimp only; split_ifs <;> simp [drAffComp, drAnd, drXor]
  · refine le_trans (hlen 16 (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
    dsimp only; split_ifs <;> simp [drAffComp, drEq, drAnd, drXor]
  · refine le_trans (hlen 16 (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
    dsimp only; split_ifs <;> simp [drAffComp, drEq, drAnd, drXor]
theorem heapAffUpClauses_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    (d : ℕ) (f : ℕ -> Bool × Bool)
    (up : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tu : Fin (2 ^ (d + 1)) -> DualLit W)
    (hup : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val ->
      DRMode α dead (up u).1 (heapUpVal affComp affId f d u.val).1 /\
      DRMode α dead (up u).2 (heapUpVal affComp affId f d u.val).2)
    (htu : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> u.val < 2 ^ d ->
      DRMode α dead (tu u) ((heapUpVal affComp affId f d (2 * u.val)).1 &&
        (heapUpVal affComp affId f d (2 * u.val + 1)).2)) :
    ∀ C ∈ z39 d up tu, ClauseSat α C := by
  intro C hC; rw [z39, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have ho := hup ⟨u, hu⟩ h.1
    rw [z79 affComp affId f d u h.1 h.2] at ho
    exact z145
      (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)).1)
      (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)).2)
      (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)).1)
      (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)).2)
      (htu ⟨u, hu⟩ h.1 h.2) ho.1 ho.2 C hCu
  · simp at hCu
theorem heapAffPrefClauses_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    (d : ℕ) (f : ℕ -> Bool × Bool)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tp : Fin (2 ^ (d + 1)) -> DualLit W)
    (hup : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val ->
      DRMode α dead (up u).1 (heapUpVal affComp affId f d u.val).1 /\
      DRMode α dead (up u).2 (heapUpVal affComp affId f d u.val).2)
    (hpr : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val ->
      DRMode α dead (pr u).1 (z17 affComp affId f d u.val).1 /\
      DRMode α dead (pr u).2 (z17 affComp affId f d u.val).2)
    (htp : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> (hu2 : u.val < 2 ^ d) ->
      DRMode α dead (tp ⟨2 * u.val + 1, by have := pow_succ 2 d; omega⟩)
        ((z17 affComp affId f d u.val).1 && (heapUpVal affComp affId f d (2 * u.val)).2)) :
    ∀ C ∈ z28 d up pr tp, ClauseSat α C := by
  intro C hC; rw [z28, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    simp only [List.mem_append] at hCu
    rcases hCu with (h1 | h2) | h3
    · have ho := (hpr ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)).1
      rw [z76 affComp affId f d u h.1] at ho
      exact drEq_sat (fun hd => by simpa [DRMode, hd] using (hpr ⟨u, hu⟩ h.1).1) ho C h1
    · have ho := (hpr ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)).2
      rw [z76 affComp affId f d u h.1] at ho
      exact drEq_sat (fun hd => by simpa [DRMode, hd] using (hpr ⟨u, hu⟩ h.1).2) ho C h2
    · have ho := hpr ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)
      rw [z85 affComp affId f d u h.1] at ho
      exact z145
        (fun hd => by simpa [DRMode, hd] using (hpr ⟨u, hu⟩ h.1).1)
        (fun hd => by simpa [DRMode, hd] using (hpr ⟨u, hu⟩ h.1).2)
        (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)).1)
        (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)).2)
        (htp ⟨u, hu⟩ h.1 h.2) ho.1 ho.2 C h3
  · simp at hCu
theorem heapAffSufClauses_sat {W : Type} [DecidableEq W] {α : W -> Bool} {dead : Bool}
    (d : ℕ) (f : ℕ -> Bool × Bool)
    (up sf : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (ts : Fin (2 ^ (d + 1)) -> DualLit W)
    (hup : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val ->
      DRMode α dead (up u).1 (heapUpVal affComp affId f d u.val).1 /\
      DRMode α dead (up u).2 (heapUpVal affComp affId f d u.val).2)
    (hsf : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val ->
      DRMode α dead (sf u).1 (z33 affComp affId f d u.val).1 /\
      DRMode α dead (sf u).2 (z33 affComp affId f d u.val).2)
    (hts : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val -> (hu2 : u.val < 2 ^ d) ->
      DRMode α dead (ts ⟨2 * u.val, by have := pow_succ 2 d; omega⟩)
        ((heapUpVal affComp affId f d (2 * u.val + 1)).1 && (z33 affComp affId f d u.val).2)) :
    ∀ C ∈ z36 d up sf ts, ClauseSat α C := by
  intro C hC; rw [z36, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    simp only [List.mem_append] at hCu
    rcases hCu with (h1 | h2) | h3
    · have ho := hsf ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega)
      rw [z150 affComp affId f d u h.1] at ho
      exact z145
        (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)).1)
        (fun hd => by simpa [DRMode, hd] using (hup ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)).2)
        (fun hd => by simpa [DRMode, hd] using (hsf ⟨u, hu⟩ h.1).1)
        (fun hd => by simpa [DRMode, hd] using (hsf ⟨u, hu⟩ h.1).2)
        (hts ⟨u, hu⟩ h.1 h.2) ho.1 ho.2 C h1
    · have ho := (hsf ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)).1
      rw [z110 affComp affId f d u h.1] at ho
      exact drEq_sat (fun hd => by simpa [DRMode, hd] using (hsf ⟨u, hu⟩ h.1).1) ho C h2
    · have ho := (hsf ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega)).2
      rw [z110 affComp affId f d u h.1] at ho
      exact drEq_sat (fun hd => by simpa [DRMode, hd] using (hsf ⟨u, hu⟩ h.1).2) ho C h3
  · simp at hCu
theorem z161 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (f : ℕ -> Bool × Bool)
    (up : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tu : Fin (2 ^ (d + 1)) -> DualLit W)
    (hF : ∀ C ∈ z39 d up tu, C ∈ F) (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d),
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩).1 (f j).1 ∈ (upS F)^[t0] S /\
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩).2 (f j).2 ∈ (upS F)^[t0] S) :
    ∀ (lvl pos : ℕ) (hlvl : lvl <= d) (hpos : pos < 2 ^ (d - lvl)),
      drFlip (up ⟨hIdx d lvl pos, hIdx_lt hlvl hpos⟩).1
        (heapUpVal affComp affId f d (hIdx d lvl pos)).1 ∈ (upS F)^[t0 + 2 * lvl] S /\
      drFlip (up ⟨hIdx d lvl pos, hIdx_lt hlvl hpos⟩).2
        (heapUpVal affComp affId f d (hIdx d lvl pos)).2 ∈ (upS F)^[t0 + 2 * lvl] S
  | 0, pos, hlvl, hpos => by
    have h0 : hIdx d 0 pos = 2 ^ d + pos := by simp [hIdx]
    have hpos' : pos < 2 ^ d := by simpa using hpos
    have hEq : (⟨hIdx d 0 pos, hIdx_lt hlvl hpos⟩ : Fin (2 ^ (d + 1))) =
        ⟨2 ^ d + pos, by rw [pow_succ]; omega⟩ := Fin.ext h0
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [hEq, h0, z30 affComp affId f d pos hpos']
    exact hleaf pos hpos'
  | lvl + 1, pos, hlvl, hpos => by
    have hu1 := hIdx_pos d (lvl + 1) pos
    have hu2 := z54 hlvl hpos
    obtain ⟨hl, hr⟩ := z44 hlvl (pos := pos)
    have h2p : 2 * pos < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have h2p1 : 2 * pos + 1 < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have ihL := z161 d f up tu hF t0 hleaf lvl (2 * pos) (by omega) h2p
    have ihR := z161 d f up tu hF t0 hleaf lvl (2 * pos + 1) (by omega) h2p1
    rw [show t0 + 2 * (lvl + 1) = 2 + (t0 + 2 * lvl) by omega, Function.iterate_add_apply,
      z79 affComp affId f d _ hu1 hu2]
    have hCsub : ∀ C ∈ drAffComp
        (up ⟨2 * hIdx d (lvl + 1) pos, by rw [pow_succ]; omega⟩)
        (up ⟨2 * hIdx d (lvl + 1) pos + 1, by rw [pow_succ]; omega⟩)
        (up ⟨hIdx d (lvl + 1) pos, hIdx_lt hlvl hpos⟩)
        (tu ⟨hIdx d (lvl + 1) pos, hIdx_lt hlvl hpos⟩), C ∈ F := by
      intro C hC; apply hF
      rw [z39, List.mem_flatMap]
      refine ⟨hIdx d (lvl + 1) pos, List.mem_range.mpr hu2, ?_⟩
      simp [hu1, hu2, hC]
    exact z162 hCsub (by simpa [hl] using ihL.1) (by simpa [hl] using ihL.2)
      (by simpa [hr] using ihR.1) (by simpa [hr] using ihR.2)
theorem z165 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (f : ℕ -> Bool × Bool)
    (up pr : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tu tp : Fin (2 ^ (d + 1)) -> DualLit W)
    (hFup : ∀ C ∈ z39 d up tu, C ∈ F)
    (hFpr : ∀ C ∈ z28 d up pr tp, C ∈ F) (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d),
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩).1 (f j).1 ∈ (upS F)^[t0] S /\
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩).2 (f j).2 ∈ (upS F)^[t0] S)
    (hroot : drFlip (pr ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩).1 true ∈
        (upS F)^[t0 + 2 * d] S /\
      drFlip (pr ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩).2 false ∈
        (upS F)^[t0 + 2 * d] S) :
    ∀ (k : ℕ) (hk : k <= d) (pos : ℕ) (hpos : pos < 2 ^ k),
      drFlip (pr ⟨hIdx d (d - k) pos, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpos)⟩).1
        (z17 affComp affId f d (hIdx d (d - k) pos)).1 ∈ (upS F)^[t0 + 2 * d + 2 * k] S /\
      drFlip (pr ⟨hIdx d (d - k) pos, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpos)⟩).2
        (z17 affComp affId f d (hIdx d (d - k) pos)).2 ∈ (upS F)^[t0 + 2 * d + 2 * k] S
  | 0, hk, pos, hpos => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have h1 : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    have hEq : (⟨hIdx d (d - 0) 0, hIdx_lt (by omega) (by simp)⟩ : Fin (2 ^ (d + 1))) =
        ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩ := Fin.ext h1
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [hEq, h1, z60]; exact hroot
  | k + 1, hk, pos, hpos => by
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    rw [show t0 + 2 * d + 2 * (k + 1) = 2 + (t0 + 2 * d + 2 * k) by omega, Function.iterate_add_apply]
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := z165 d f up pr tu tp hFup hFpr t0 hleaf hroot k (by omega) q hpar
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hC1 : ∀ C ∈ drEq (pr ⟨hIdx d (d - k) q, hIdx_lt (by omega)
          (by rw [show d - (d - k) = k by omega]; exact hpar)⟩).1
          (pr ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩).1, C ∈ F := by
        intro C hC; apply hFpr
        rw [z28, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hC2 : ∀ C ∈ drEq (pr ⟨hIdx d (d - k) q, hIdx_lt (by omega)
          (by rw [show d - (d - k) = k by omega]; exact hpar)⟩).2
          (pr ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩).2, C ∈ F := by
        intro C hC; apply hFpr
        rw [z28, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hl])
      rw [hEq, hq, ← hl, z76 affComp affId f d _ hu1]
      exact ⟨z136 F _ (drEq_up hC1 ih.1), z136 F _ (drEq_up hC2 ih.2)⟩
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := z165 d f up pr tu tp hFup hFpr t0 hleaf hroot k (by omega) q hpar
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hLsib := z161 d f up tu hFup t0 hleaf (d - (k + 1)) (2 * q) (by omega)
        (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)
      have hLsib1 := z5 F S (by omega : t0 + 2 * (d - (k + 1)) <= t0 + 2 * d + 2 * k) hLsib.1
      have hLsib2 := z5 F S (by omega : t0 + 2 * (d - (k + 1)) <= t0 + 2 * d + 2 * k) hLsib.2
      have hCsub : ∀ C ∈ drAffComp
          (pr ⟨hIdx d (d - k) q, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpar)⟩)
          (up ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩)
          (pr ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩)
          (tp ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply hFpr
        rw [z28, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hr])
      rw [hEq, hq, ← hr, z85 affComp affId f d _ hu1]
      exact z162 hCsub ih.1 ih.2 (by simpa [hl] using hLsib1) (by simpa [hl] using hLsib2)
theorem heapAffSuf_up {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (f : ℕ -> Bool × Bool)
    (up sf : Fin (2 ^ (d + 1)) -> DualLit W × DualLit W)
    (tu ts : Fin (2 ^ (d + 1)) -> DualLit W)
    (hFup : ∀ C ∈ z39 d up tu, C ∈ F)
    (hFsf : ∀ C ∈ z36 d up sf ts, C ∈ F) (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d),
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩).1 (f j).1 ∈ (upS F)^[t0] S /\
      drFlip (up ⟨2 ^ d + j, by rw [pow_succ]; omega⟩).2 (f j).2 ∈ (upS F)^[t0] S)
    (hroot : drFlip (sf ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩).1 true ∈
        (upS F)^[t0 + 2 * d] S /\
      drFlip (sf ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩).2 false ∈
        (upS F)^[t0 + 2 * d] S) :
    ∀ (k : ℕ) (hk : k <= d) (pos : ℕ) (hpos : pos < 2 ^ k),
      drFlip (sf ⟨hIdx d (d - k) pos, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpos)⟩).1
        (z33 affComp affId f d (hIdx d (d - k) pos)).1 ∈ (upS F)^[t0 + 2 * d + 2 * k] S /\
      drFlip (sf ⟨hIdx d (d - k) pos, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpos)⟩).2
        (z33 affComp affId f d (hIdx d (d - k) pos)).2 ∈ (upS F)^[t0 + 2 * d + 2 * k] S
  | 0, hk, pos, hpos => by
    have hp0 : pos = 0 := by simp at hpos; omega
    subst hp0
    have h1 : hIdx d (d - 0) 0 = 1 := by simp [hIdx]
    have hEq : (⟨hIdx d (d - 0) 0, hIdx_lt (by omega) (by simp)⟩ : Fin (2 ^ (d + 1))) =
        ⟨1, by have := Nat.one_le_pow d 2 (by omega); rw [pow_succ]; omega⟩ := Fin.ext h1
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [hEq, h1, z126]; exact hroot
  | k + 1, hk, pos, hpos => by
    have hlvl : (d - (k + 1)) + 1 = d - k := by omega
    rw [show t0 + 2 * d + 2 * (k + 1) = 2 + (t0 + 2 * d + 2 * k) by omega, Function.iterate_add_apply]
    rcases Nat.even_or_odd' pos with ⟨q, hq | hq⟩
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := heapAffSuf_up d f up sf tu ts hFup hFsf t0 hleaf hroot k (by omega) q hpar
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hRsib := z161 d f up tu hFup t0 hleaf (d - (k + 1)) (2 * q + 1) (by omega)
        (by rw [show d - (d - (k + 1)) = k + 1 by omega]; omega)
      have hRsib1 := z5 F S (by omega : t0 + 2 * (d - (k + 1)) <= t0 + 2 * d + 2 * k) hRsib.1
      have hRsib2 := z5 F S (by omega : t0 + 2 * (d - (k + 1)) <= t0 + 2 * d + 2 * k) hRsib.2
      have hCsub : ∀ C ∈ drAffComp
          (up ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩)
          (sf ⟨hIdx d (d - k) q, hIdx_lt (by omega) (by rw [show d - (d - k) = k by omega]; exact hpar)⟩)
          (sf ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩)
          (ts ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply hFsf
        rw [z36, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hl])
      rw [hEq, hq, ← hl, z150 affComp affId f d _ hu1]
      exact z162 hCsub (by simpa [hr] using hRsib1) (by simpa [hr] using hRsib2) ih.1 ih.2
    · have hpar : q < 2 ^ k := by rw [pow_succ] at hpos; omega
      have ih := heapAffSuf_up d f up sf tu ts hFup hFsf t0 hleaf hroot k (by omega) q hpar
      obtain ⟨hl, hr⟩ := z44 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
      rw [hlvl] at hl hr
      have hu1 := hIdx_pos d (d - k) q
      have hu2 := z54 (d := d) (lvl := d - (k + 1)) (pos := q) (by omega)
        (by rw [show d - (d - (k + 1) + 1) = k by omega]; exact hpar)
      rw [hlvl] at hu2
      have hC1 : ∀ C ∈ drEq (sf ⟨hIdx d (d - k) q, hIdx_lt (by omega)
          (by rw [show d - (d - k) = k by omega]; exact hpar)⟩).1
          (sf ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩).1, C ∈ F := by
        intro C hC; apply hFsf
        rw [z36, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hC2 : ∀ C ∈ drEq (sf ⟨hIdx d (d - k) q, hIdx_lt (by omega)
          (by rw [show d - (d - k) = k by omega]; exact hpar)⟩).2
          (sf ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩).2, C ∈ F := by
        intro C hC; apply hFsf
        rw [z36, List.mem_flatMap]
        refine ⟨hIdx d (d - k) q, List.mem_range.mpr hu2, ?_⟩
        simp [hu1, hu2, List.mem_append, hC]
      have hEq : (⟨hIdx d (d - (k + 1)) pos, hIdx_lt (by omega)
          (by rw [show d - (d - (k + 1)) = k + 1 by omega]; exact hpos)⟩ : Fin (2 ^ (d + 1))) =
          ⟨2 * hIdx d (d - k) q + 1, by rw [pow_succ]; omega⟩ := Fin.ext (by dsimp only; rw [hq, ← hr])
      rw [hEq, hq, ← hr, z110 affComp affId f d _ hu1]
      exact ⟨z136 F _ (drEq_up hC1 ih.1), z136 F _ (drEq_up hC2 ih.2)⟩
def z24 {W : Type} [DecidableEq W] (d : ℕ)
    (node : Fin (2 ^ (d + 1)) -> Lit W) : List (Cl W) :=
  (List.range (2 ^ d)).flatMap fun u =>
    if h : 1 <= u /\ u < 2 ^ d then
      have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
      have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
      [imp2 (node ⟨2 * u, h2u⟩) (node ⟨2 * u + 1, h2u1⟩) (node ⟨u, hu⟩)]
    else []
theorem z88 {W : Type} [DecidableEq W] (d : ℕ)
    (node : Fin (2 ^ (d + 1)) -> Lit W) :
    ∀ C ∈ z24 d node, C.card <= 3 := by
  intro C hC; rw [z24, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · simp only [List.mem_singleton] at hCu; rw [hCu]; exact imp2_card _ _ _
  · simp at hCu
theorem z73 {W : Type} [DecidableEq W] (d : ℕ)
    (node : Fin (2 ^ (d + 1)) -> Lit W) :
    (z24 d node).length <= 2 ^ d := by
  dsimp [z24]
  have hlen : ∀ (L : List ℕ) (f : ℕ -> List (Cl W)), (∀ x ∈ L, (f x).length <= 1) ->
      (L.flatMap f).length <= L.length := by
    intro L f hf; induction L with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have h1 := hf a (List.mem_cons_self ..)
      have h2 := ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
      omega
  refine le_trans (hlen (List.range (2 ^ d)) _ fun u _ => ?_) (by simp [List.length_range])
  split_ifs <;> simp
theorem z95 {W : Type} [DecidableEq W] {α : W -> Bool}
    (d : ℕ) (f : ℕ -> Bool) (node : Fin (2 ^ (d + 1)) -> Lit W)
    (hnode : ∀ u : Fin (2 ^ (d + 1)), 1 <= u.val ->
      lEv α (node u) = heapUpVal and true f d u.val) :
    ∀ C ∈ z24 d node, ClauseSat α C := by
  intro C hC; rw [z24, List.mem_flatMap] at hC
  rcases hC with ⟨u, _, hCu⟩; split_ifs at hCu with h
  · simp only [List.mem_singleton] at hCu; rw [hCu, z45]
    have hu : u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u : 2 * u < 2 ^ (d + 1) := by rw [pow_succ]; omega
    have h2u1 : 2 * u + 1 < 2 ^ (d + 1) := by rw [pow_succ]; omega
    rw [hnode ⟨u, hu⟩ h.1, hnode ⟨2 * u, h2u⟩ (by change 1 <= 2 * u; omega), hnode ⟨2 * u + 1, h2u1⟩ (by change 1 <= 2 * u + 1; omega),
      z79 and true f d u h.1 h.2]
    intro h1 h2; rw [h1, h2]; rfl
  · simp at hCu
theorem z153 {W : Type} [DecidableEq W] {F : Finset (Cl W)} {S : Set (Lit W)}
    (d : ℕ) (node : Fin (2 ^ (d + 1)) -> Lit W)
    (hF : ∀ C ∈ z24 d node, C ∈ F) (t0 : ℕ)
    (hleaf : ∀ j (hj : j < 2 ^ d),
      node ⟨2 ^ d + j, by rw [pow_succ]; omega⟩ ∈ (upS F)^[t0] S) :
    ∀ (lvl pos : ℕ) (hlvl : lvl <= d) (hpos : pos < 2 ^ (d - lvl)),
      node ⟨hIdx d lvl pos, hIdx_lt hlvl hpos⟩ ∈ (upS F)^[t0 + lvl] S
  | 0, pos, hlvl, hpos => by
    have h0 : hIdx d 0 pos = 2 ^ d + pos := by simp [hIdx]
    have hpos' : pos < 2 ^ d := by simpa using hpos
    have hEq : (⟨hIdx d 0 pos, hIdx_lt hlvl hpos⟩ : Fin (2 ^ (d + 1))) =
        ⟨2 ^ d + pos, by rw [pow_succ]; omega⟩ := Fin.ext h0
    simp only [Nat.add_zero]; rw [hEq]; exact hleaf pos hpos'
  | lvl + 1, pos, hlvl, hpos => by
    have hu1 := hIdx_pos d (lvl + 1) pos
    have hu2 := z54 hlvl hpos
    obtain ⟨hl, hr⟩ := z44 hlvl (pos := pos)
    have h2p : 2 * pos < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have h2p1 : 2 * pos + 1 < 2 ^ (d - lvl) := by
      have : d - lvl = (d - (lvl + 1)) + 1 := by omega
      rw [this, pow_succ]; omega
    have ihL := z153 d node hF t0 hleaf lvl (2 * pos) (by omega) h2p
    have ihR := z153 d node hF t0 hleaf lvl (2 * pos + 1) (by omega) h2p1
    rw [show t0 + (lvl + 1) = (t0 + lvl) + 1 by omega, Function.iterate_succ_apply']
    have hC : imp2 (node ⟨2 * hIdx d (lvl + 1) pos, by rw [pow_succ]; omega⟩)
        (node ⟨2 * hIdx d (lvl + 1) pos + 1, by rw [pow_succ]; omega⟩)
        (node ⟨hIdx d (lvl + 1) pos, hIdx_lt hlvl hpos⟩) ∈ F := by
      apply hF; rw [z24, List.mem_flatMap]
      refine ⟨hIdx d (lvl + 1) pos, List.mem_range.mpr hu2, ?_⟩
      simp [hu1, hu2]
    exact upS_imp2 hC (by simpa [hl] using ihL) (by simpa [hr] using ihR)
theorem z66 {f : ℕ -> Bool} {d : ℕ} {j : ℕ} (hj : j < 2 ^ d) (hf : f j = false) :
    heapUpVal and true f d 1 = false := by
  rw [z84 and true Bool.and_assoc Bool.true_and Bool.and_true]
  have hmem : false ∈ (List.range (2 ^ d)).map f := by
    rw [List.mem_map]; exact ⟨j, List.mem_range.mpr hj, hf⟩
  generalize (List.range (2 ^ d)).map f = L at hmem ⊢
  induction L with
  | nil => simp at hmem
  | cons a t ih =>
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | ht
    · simp
    · simp [ih ht]
abbrev V5 (k : ℕ) := Fin 5 × Fin k
def dTrack (ori : Bool × Bool) : Fin 3 -> Fin 5
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => if ori.1 then 3 else 0
  | ⟨2, _⟩ => if ori.2 then 4 else 1
def drvPos {k : ℕ} (hk : 0 < k) (ori : Bool × Bool) (idx : Fin (3 * k)) : V5 k :=
  (dTrack ori ⟨idx.val / k, by have := idx.isLt; exact Nat.div_lt_of_lt_mul (by omega)⟩,
   ⟨idx.val % k, Nat.mod_lt _ hk⟩)
def drvIdx {k : ℕ} (t : Fin 3) (j : Fin k) : Fin (3 * k) :=
  ⟨t.val * k + j.val, by have ht := t.isLt; have hj := j.isLt; nlinarith⟩
theorem z49 {k : ℕ} (hk : 0 < k) (ori : Bool × Bool) (t : Fin 3) (j : Fin k) :
    drvPos hk ori (drvIdx t j) = (dTrack ori t, j) := by
  apply Prod.ext
  · dsimp [drvPos, drvIdx]
    have hdiv : (t.val * k + j.val) / k = t.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
    congr 1; exact Fin.ext hdiv
  · apply Fin.ext; dsimp [drvPos, drvIdx]
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt]
theorem dTrack_inj (ori : Bool × Bool) : Function.Injective (dTrack ori) := by
  intro a b hab
  rcases ori with ⟨rR, cR⟩
  fin_cases a <;> fin_cases b <;> cases rR <;> cases cR <;> simp_all [dTrack]
theorem drvPos_inj {k : ℕ} (hk : 0 < k) (ori : Bool × Bool) :
    Function.Injective (drvPos hk ori) := by
  intro i1 i2 h
  have h1 : (drvPos hk ori i1).1 = (drvPos hk ori i2).1 := congrArg Prod.fst h
  have h2 : (drvPos hk ori i1).2 = (drvPos hk ori i2).2 := congrArg Prod.snd h
  have ht := congrArg Fin.val (dTrack_inj ori h1)
  have hj := congrArg Fin.val h2
  dsimp [drvPos] at ht hj
  apply Fin.ext
  have hd1 := Nat.div_add_mod i1.val k
  have hd2 := Nat.div_add_mod i2.val k
  rw [← hd1, ← hd2, ht, hj]
def z15 (ori : Bool × Bool) (isCol : Bool) : Fin 5 :=
  if isCol then (if ori.2 then 1 else 4) else (if ori.1 then 0 else 3)
def z8 (isCol : Bool) : Fin 3 := if isCol then 2 else 1
def branchRev (ori : Bool × Bool) (isCol : Bool) : Bool := if isCol then ori.2 else ori.1
theorem z122 (ori : Bool × Bool) (tr : Fin 5) :
    (∃ t : Fin 3, tr = dTrack ori t) \/ tr = z15 ori false \/ tr = z15 ori true := by
  rcases ori with ⟨rR, cR⟩
  fin_cases tr <;> cases rR <;> cases cR
  all_goals first
    | exact Or.inl ⟨0, rfl⟩
    | exact Or.inl ⟨1, rfl⟩
    | exact Or.inl ⟨2, rfl⟩
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
theorem z166 {k : ℕ} (hk : 0 < k) (ori : Bool × Bool) (p : V5 k) :
    (p.1 = 2 \/ p.1 = (if ori.1 then 3 else 0) \/ p.1 = (if ori.2 then 4 else 1)) ↔
      ∃ idx : Fin (3 * k), drvPos hk ori idx = p := by
  rcases p with ⟨tr, j⟩
  constructor
  · rintro (h | h | h)
    · exact ⟨drvIdx ⟨0, by omega⟩ j, by rw [z49]; exact Prod.ext h.symm rfl⟩
    · exact ⟨drvIdx ⟨1, by omega⟩ j, by rw [z49]; exact Prod.ext h.symm rfl⟩
    · exact ⟨drvIdx ⟨2, by omega⟩ j, by rw [z49]; exact Prod.ext h.symm rfl⟩
  · rintro ⟨idx, h⟩
    have h1 := congrArg Prod.fst h
    dsimp [drvPos] at h1
    rw [← h1]
    have ht : idx.val / k = 0 \/ idx.val / k = 1 \/ idx.val / k = 2 := by
      have hlt3 : idx.val / k < 3 := Nat.div_lt_of_lt_mul (by have := idx.isLt; omega)
      match hdiv : idx.val / k with
      | 0 => exact Or.inl rfl
      | 1 => exact Or.inr (Or.inl rfl)
      | 2 => exact Or.inr (Or.inr rfl)
      | _ + 3 => exact absurd (hdiv ▸ hlt3) (by omega)
    rcases ht with h0 | h1' | h2'
    · exact Or.inl (by rw [show (⟨idx.val / k, _⟩ : Fin 3) = ⟨0, by omega⟩ from Fin.ext h0]; rfl)
    · exact Or.inr (Or.inl (by rw [show (⟨idx.val / k, _⟩ : Fin 3) = ⟨1, by omega⟩ from Fin.ext h1']; rfl))
    · exact Or.inr (Or.inr (by rw [show (⟨idx.val / k, _⟩ : Fin 3) = ⟨2, by omega⟩ from Fin.ext h2']; rfl))
def dBOf (k r : ℕ) : ℕ := if k % 3 = 0 then 2 * r else 0
theorem z67 (k r : ℕ) : 2 ^ dBOf k r = z2 k r := by
  dsimp [dBOf, z2]
  split_ifs
  · rw [pow_mul]; rfl
  · rfl
abbrev AuxConst := Bool
abbrev AuxBase (k r : ℕ) := Bool × Fin (r + 1) × Fin k × Fin 5
abbrev AuxUpDown (k h' : ℕ) := Fin (2 ^ h') × Bool × Fin (2 ^ (Nat.clog 2 (3 * k) + 1)) × Bool
abbrev AuxWalsh (k h' : ℕ) := Fin (3 * k) × Fin (h' + 1) × Fin (2 ^ h') × Bool
abbrev AuxLeafWord (k r : ℕ) := Fin (r + 1) × Fin k × Fin 9 × Bool
abbrev AuxLeafChi (k r : ℕ) := Fin r × Fin 9 × Fin (2 ^ (Nat.clog 2 k + 1)) × Bool
abbrev AuxLeafMix (k r : ℕ) := Fin r × Fin 3 × Bool × Fin (2 ^ (Nat.clog 2 k + 1)) × Bool
abbrev AuxLeafWrap (r : ℕ) := Fin (r + 1) × Bool × Bool
abbrev AuxLeafMeta (k : ℕ) := Unit ⊕ (Fin k × Bool)
abbrev AuxLeaf (k r : ℕ) :=
  AuxLeafWord k r ⊕ AuxLeafChi k r ⊕ AuxLeafMix k r ⊕ AuxLeafWrap r ⊕ AuxLeafMeta k
abbrev z155 (k h' : ℕ) :=
  (Fin (3 * k) × Bool) ⊕
  (Fin h' × Fin (2 ^ (Nat.clog 2 (3 * k) + 1)) × Bool) ⊕
  Bool
abbrev AuxSynAgg (k r : ℕ) :=
  (Bool × Fin (2 ^ (dBOf k r + 1))) ⊕
  (Bool × Fin k × Bool × Fin (2 ^ (dBOf k r + 1))) ⊕
  (Fin 5 × Fin k × Bool)
abbrev AuxSyn (k r h' : ℕ) :=
  z155 k h' ⊕ (Bool × Fin (z2 k r) × AuxLeaf k r) ⊕ AuxSynAgg k r
abbrev AuxMatAgg (k h' : ℕ) :=
  Fin (2 ^ (h' + 1)) ⊕ (Fin 5 × Fin k × Bool × Fin (2 ^ (h' + 1)))
abbrev AuxMatrix (k r h' : ℕ) :=
  AuxUpDown k h' ⊕ AuxWalsh k h' ⊕ (Fin (2 ^ h') × AuxSyn k r h') ⊕ AuxMatAgg k h'
abbrev AuxAll (k r h' R : ℕ) :=
  AuxConst ⊕ AuxBase k r ⊕ (Bool × Bool × Fin R × AuxMatrix k r h')
abbrev VarAll (k r h' R : ℕ) := Sum (V5 k) (AuxAll k r h' R)
set_option synthInstance.maxSize 4096 in
def decEqAuxLeaf (k r : ℕ) : DecidableEq (AuxLeaf k r) := inferInstance
set_option synthInstance.maxSize 4096 in
def decEqAuxSynCore (k h' : ℕ) : DecidableEq (z155 k h') := inferInstance
set_option synthInstance.maxSize 4096 in
def decEqAuxSynAgg (k r : ℕ) : DecidableEq (AuxSynAgg k r) := inferInstance
def decEqAuxSyn (k r h' : ℕ) : DecidableEq (AuxSyn k r h') :=
  @instDecidableEqSum _ _ (decEqAuxSynCore k h')
    (@instDecidableEqSum _ _
      (@instDecidableEqProd _ _ inferInstance
        (@instDecidableEqProd _ _ inferInstance (decEqAuxLeaf k r)))
      (decEqAuxSynAgg k r))
set_option synthInstance.maxSize 4096 in
def decEqAuxMatAgg (k h' : ℕ) : DecidableEq (AuxMatAgg k h') := inferInstance
def decEqAuxMatrix (k r h' : ℕ) : DecidableEq (AuxMatrix k r h') :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance
      (@instDecidableEqSum _ _
        (@instDecidableEqProd _ _ inferInstance (decEqAuxSyn k r h'))
        (decEqAuxMatAgg k h')))
def decEqAuxAll (k r h' R : ℕ) : DecidableEq (AuxAll k r h' R) :=
  @instDecidableEqSum _ _ inferInstance
    (@instDecidableEqSum _ _ inferInstance
      (@instDecidableEqProd _ _ inferInstance
        (@instDecidableEqProd _ _ inferInstance
          (@instDecidableEqProd _ _ inferInstance (decEqAuxMatrix k r h')))))
instance (priority := 2000) instDecEqAuxAll {k r h' R : ℕ} : DecidableEq (AuxAll k r h' R) :=
  decEqAuxAll k r h' R
instance (priority := 2000) instDecEqVarAll {k r h' R : ℕ} : DecidableEq (VarAll k r h' R) :=
  @instDecidableEqSum _ _ inferInstance (decEqAuxAll k r h' R)
section Builders
variable {k r h' R : ℕ}
def vRaw (p : V5 k) (b : Bool) : Lit (VarAll k r h' R) := (Sum.inl p, b)
def vRawDR (p : V5 k) : DualLit (VarAll k r h' R) := ((Sum.inl p, false), (Sum.inl p, true))
def vAux (a : AuxAll k r h' R) (b : Bool := true) : Lit (VarAll k r h' R) := (Sum.inr a, b)
def vConstTrue : Lit (VarAll k r h' R) := vAux (Sum.inl true)
def vConstFalse : Lit (VarAll k r h' R) := vAux (Sum.inl false)
def z26 : DualLit (VarAll k r h' R) := (vConstFalse, vConstTrue)
def z3 : DualLit (VarAll k r h' R) := (vConstTrue, vConstFalse)
def drConst (b : Bool) : DualLit (VarAll k r h' R) := if b then z26 else z3
def vBase (isCol : Bool) (t : Fin (r + 1)) (j : Fin k) (slot : Fin 5) : Lit (VarAll k r h' R) :=
  vAux (Sum.inr (Sum.inl (isCol, t, j, slot)))
def vMat (ori : Bool × Bool) (m : Fin R) (x : AuxMatrix k r h') : Lit (VarAll k r h' R) :=
  vAux (Sum.inr (Sum.inr (ori.1, ori.2, m, x)))
def drUpDown (ori : Bool × Bool) (m : Fin R) (c : Fin (2 ^ h')) (isDown : Bool)
    (u : Fin (2 ^ (Nat.clog 2 (3 * k) + 1))) : DualLit (VarAll k r h' R) :=
  (vMat ori m (Sum.inl (c, isDown, u, false)), vMat ori m (Sum.inl (c, isDown, u, true)))
def vWalsh (ori : Bool × Bool) (m : Fin R) (i : Fin (3 * k))
    (t : Fin (h' + 1)) (p : Fin (2 ^ h')) (b : Bool) : Lit (VarAll k r h' R) :=
  vMat ori m (Sum.inr (Sum.inl (i, t, p, b)))
def vSyn (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (x : AuxSyn k r h') : Lit (VarAll k r h' R) :=
  vMat ori m (Sum.inr (Sum.inr (Sum.inl (s, x))))
def drXDual (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) (i : Fin (3 * k)) :
    DualLit (VarAll k r h' R) :=
  (vSyn ori m s (Sum.inl (Sum.inl (i, false))), vSyn ori m s (Sum.inl (Sum.inl (i, true))))
def drPar (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) (q : Fin h')
    (u : Fin (2 ^ (Nat.clog 2 (3 * k) + 1))) : DualLit (VarAll k r h' R) :=
  (vSyn ori m s (Sum.inl (Sum.inr (Sum.inl (q, u, false)))),
   vSyn ori m s (Sum.inl (Sum.inr (Sum.inl (q, u, true)))))
def vExcl (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) : Lit (VarAll k r h' R) :=
  vSyn ori m s (Sum.inl (Sum.inr (Sum.inr false)))
def vSynDead (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) : Lit (VarAll k r h' R) :=
  vSyn ori m s (Sum.inl (Sum.inr (Sum.inr true)))
def vLeaf (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) (x : AuxLeaf k r) : Lit (VarAll k r h' R) :=
  vSyn ori m s (Sum.inr (Sum.inl (isCol, leaf, x)))
def z91 (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r))
    (t : Fin (r + 1)) (j : Fin k) (slot : Fin 9) : DualLit (VarAll k r h' R) :=
  (vLeaf ori m s isCol leaf (Sum.inl (t, j, slot, false)),
   vLeaf ori m s isCol leaf (Sum.inl (t, j, slot, true)))
def drLeafChi (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r))
    (t : Fin r) (slot : Fin 9) (u : Fin (2 ^ (Nat.clog 2 k + 1))) : DualLit (VarAll k r h' R) :=
  (vLeaf ori m s isCol leaf (Sum.inr (Sum.inl (t, slot, u, false))),
   vLeaf ori m s isCol leaf (Sum.inr (Sum.inl (t, slot, u, true))))
def drLeafMix (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r))
    (t : Fin r) (rc : Fin 3) (isPref : Bool) (u : Fin (2 ^ (Nat.clog 2 k + 1))) :
    DualLit (VarAll k r h' R) :=
  (vLeaf ori m s isCol leaf (Sum.inr (Sum.inr (Sum.inl (t, rc, isPref, u, false)))),
   vLeaf ori m s isCol leaf (Sum.inr (Sum.inr (Sum.inl (t, rc, isPref, u, true)))))
def z137 (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r))
    (t : Fin (r + 1)) (isAcc : Bool) : DualLit (VarAll k r h' R) :=
  (vLeaf ori m s isCol leaf (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, isAcc, false))))),
   vLeaf ori m s isCol leaf (Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, isAcc, true))))))
def vLeafDead (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) : Lit (VarAll k r h' R) :=
  vLeaf ori m s isCol leaf (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))))
def z90 (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) (j : Fin k) (b : Bool) : Lit (VarAll k r h' R) :=
  vLeaf ori m s isCol leaf (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, b))))))
def z69 (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (u : Fin (2 ^ (dBOf k r + 1))) : Lit (VarAll k r h' R) :=
  vSyn ori m s (Sum.inr (Sum.inr (Sum.inl (isCol, u))))
def z68 (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (j : Fin k) (b : Bool) (u : Fin (2 ^ (dBOf k r + 1))) : Lit (VarAll k r h' R) :=
  vSyn ori m s (Sum.inr (Sum.inr (Sum.inr (Sum.inl (isCol, j, b, u)))))
def vKillLit (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (p : V5 k) (b : Bool) : Lit (VarAll k r h' R) :=
  vSyn ori m s (Sum.inr (Sum.inr (Sum.inr (Sum.inr (p.1, p.2, b)))))
def z156 (ori : Bool × Bool) (m : Fin R) (u : Fin (2 ^ (h' + 1))) : Lit (VarAll k r h' R) :=
  vMat ori m (Sum.inr (Sum.inr (Sum.inr (Sum.inl u))))
def vAllKilled (ori : Bool × Bool) (m : Fin R) (p : V5 k) (b : Bool)
    (u : Fin (2 ^ (h' + 1))) : Lit (VarAll k r h' R) :=
  vMat ori m (Sum.inr (Sum.inr (Sum.inr (Sum.inr (p.1, p.2, b, u)))))
theorem flatMap_card_le {α β : Type} (L : List α) (f : α -> List β) (P : β -> Prop)
    (h : ∀ a ∈ L, ∀ b ∈ f a, P b) : ∀ b ∈ L.flatMap f, P b := by
  intro b hb; rw [List.mem_flatMap] at hb; rcases hb with ⟨a, ha, hba⟩; exact h a ha b hba
theorem z0 {α β : Type} (L : List α) (f : α -> List β) (c : ℕ)
    (h : ∀ a ∈ L, (f a).length <= c) : (L.flatMap f).length <= L.length * c := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    nlinarith
def z92 : List (Cl (VarAll k r h' R)) :=
  [cl1 vConstTrue, cl1 (negL vConstFalse)]
def z64 (hk : 0 < k) : List (Cl (VarAll k r h' R)) :=
  ([false, true] : List Bool).flatMap fun isCol =>
    let inpTr : Fin 5 := if isCol then 1 else 0
    let outTr : Fin 5 := if isCol then 4 else 3
    let initCl := (List.finRange k).flatMap fun j =>
      let kj : Fin k := ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩
      tsXor (vRaw (2, kj) true) (vRaw (inpTr, j) true) (vBase isCol ⟨0, Nat.zero_lt_succ r⟩ j 0)
    let roundCl := (List.finRange r).flatMap fun t =>
      let t0 : Fin (r + 1) := ⟨t.val, by omega⟩
      let t1 : Fin (r + 1) := ⟨t.val + 1, by omega⟩
      let δ := mixStride isCol
      (List.finRange k).flatMap fun j =>
        let j1 : Fin k := ⟨(j.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
        let j2 : Fin k := ⟨(j.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
        let jc1 : Fin k := ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
        let jc2 : Fin k := ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩
        let kj : Fin k := ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩
        let cb : Bool := constBit k (z10 isCol r t.val) j
        let keyLit := if cb then negL (vRaw (2, kj) true) else vRaw (2, kj) true
        tsXor (vBase isCol t0 j 0) (vBase isCol t0 j1 0) (vBase isCol t0 j 1) ++
        tsXor (vBase isCol t0 j 1) (vBase isCol t0 j2 0) (vBase isCol t0 j 2) ++
        tsAnd (negL (vBase isCol t0 jc1 2)) (vBase isCol t0 jc2 2) (vBase isCol t0 j 3) ++
        tsXor (vBase isCol t0 j 2) (vBase isCol t0 j 3) (vBase isCol t0 j 4) ++
        tsXor (vBase isCol t0 j 4) keyLit (vBase isCol t1 j 0)
    let outCl := (List.finRange k).flatMap fun j =>
      tsEq (vBase isCol ⟨r, Nat.lt_succ_self r⟩ j 0) (vRaw (outTr, j) true)
    initCl ++ roundCl ++ outCl
def z40 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) : List (Cl (VarAll k r h' R)) :=
  let dN := Nat.clog 2 (3 * k)
  (List.finRange (2 ^ h')).flatMap fun c =>
    let up := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c false
    let dn := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c true
    let leafCl := (List.finRange (2 ^ dN)).flatMap fun j =>
      let u : Fin (2 ^ (dN + 1)) := ⟨2 ^ dN + j.val, by rw [pow_succ]; omega⟩
      if hj : j.val < 3 * k then
        let idx : Fin (3 * k) := ⟨j.val, hj⟩
        if rowMask (H m) c idx then
          drEq (vRawDR (drvPos hk ori idx)) (up u)
        else
          drEq z3 (up u)
      else
        drEq z3 (up u)
    let rootCl := drEq z3 (dn ⟨1, by have h1 : 1 <= 2 ^ dN := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
    leafCl ++ rootCl ++ z14 dN up ++ z27 dN up dn
def z75 (p t : ℕ) : ℕ :=
  if p.testBit t then p - 2 ^ t else p
def setBitNat (p t : ℕ) : ℕ :=
  if p.testBit t then p else p + 2 ^ t
theorem z80 {h' p t : ℕ} (hp : p < 2 ^ h') : z75 p t < 2 ^ h' := by
  dsimp [z75]
  split_ifs
  · exact lt_of_le_of_lt (Nat.sub_le p _) hp
  · exact hp
theorem z104 {h' p t : ℕ} (hp : p < 2 ^ h') (ht : t < h') : setBitNat p t < 2 ^ h' := by
  dsimp [setBitNat]
  split_ifs with hb
  · exact hp
  · have htb : (p / 2 ^ t) % 2 = 0 := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb
      rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ t) with h | h
      · exact h
      · simp [h] at hb
    have hpow : 2 ^ h' = 2 ^ (h' - t) * 2 ^ t := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hqlt : p / 2 ^ t < 2 ^ (h' - t) := by
      have : p < 2 ^ (h' - t) * 2 ^ t := by rwa [← hpow]
      exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr this
    have heven_pow : 2 ∣ 2 ^ (h' - t) := by
      have : h' - t = (h' - t - 1) + 1 := by omega
      rw [this, pow_succ]; exact dvd_mul_left 2 _
    have hq_le : p / 2 ^ t + 1 < 2 ^ (h' - t) := by
      obtain ⟨c, hc⟩ := heven_pow; omega
    have hmod : p % 2 ^ t < 2 ^ t := Nat.mod_lt p (Nat.pow_pos (by omega))
    have hdiv := Nat.div_add_mod p (2 ^ t)
    nlinarith
private theorem z149 (p t j : ℕ) (hbt : p.testBit t = false) :
    (p + 2 ^ t).testBit j = if j = t then true else p.testBit j := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hbt ⊢
  have hbt0 : (p / 2 ^ t) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ t) with h | h
    · exact h
    · simp [h] at hbt
  by_cases hjt : j = t
  · subst hjt
    have hpos : 0 < 2 ^ j := Nat.pow_pos (by omega)
    rw [Nat.add_div_right p hpos]
    simp [if_pos rfl, Nat.add_mod, hbt0]
  · simp only [if_neg hjt]
    by_cases hlt : j < t
    · have hpow : 2 ^ t = 2 ^ (t - j) * 2 ^ j := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have hpos : 0 < 2 ^ j := Nat.pow_pos (by omega)
      have hdiv : (p + 2 ^ t) / 2 ^ j = p / 2 ^ j + 2 ^ (t - j) := by
        rw [hpow, Nat.add_mul_div_right _ _ hpos]
      have heven : 2 ^ (t - j) % 2 = 0 := by
        have : t - j = (t - j - 1) + 1 := by omega
        rw [this, pow_succ]; omega
      rw [hdiv]
      have hmod : (p / 2 ^ j + 2 ^ (t - j)) % 2 = (p / 2 ^ j) % 2 := by omega
      simp [hmod]
    · have hgt : t < j := by omega
      have hpow : 2 ^ j = 2 ^ (j - t) * 2 ^ t := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
      have hpt : 0 < 2 ^ t := Nat.pow_pos (by omega)
      have hpj : 0 < 2 ^ j := Nat.pow_pos (by omega)
      have heven_pow : 2 ∣ 2 ^ (j - t) := by
        have : j - t = (j - t - 1) + 1 := by omega
        rw [this, pow_succ]; exact dvd_mul_left 2 _
      have hr_mod : ((p % 2 ^ j) / 2 ^ t) % 2 = 0 := by
        have hdecomp : p / 2 ^ t = (p / 2 ^ j) * 2 ^ (j - t) + (p % 2 ^ j) / 2 ^ t := by
          have hd := Nat.div_add_mod p (2 ^ j)
          conv_lhs => rw [← hd, hpow]
          rw [show 2 ^ (j - t) * 2 ^ t * (p / (2 ^ (j - t) * 2 ^ t)) =
                2 ^ t * (p / (2 ^ (j - t) * 2 ^ t) * 2 ^ (j - t)) by ring]
          rw [Nat.mul_add_div hpt, ← hpow]
        obtain ⟨c, hc⟩ := heven_pow
        rw [hdecomp, hc] at hbt0
        have hm2 : (p / 2 ^ j * (2 * c) + p % 2 ^ j / 2 ^ t) % 2 = (p % 2 ^ j / 2 ^ t) % 2 := by
          rw [show p / 2 ^ j * (2 * c) = 2 * (p / 2 ^ j * c) by ring, Nat.mul_add_mod]
        omega
      have hr_lt : p % 2 ^ j < 2 ^ j := Nat.mod_lt p hpj
      have hq_lt : (p % 2 ^ j) / 2 ^ t < 2 ^ (j - t) := by
        have hdm := Nat.div_mul_le_self (p % 2 ^ j) (2 ^ t)
        have hr_lt' : p % 2 ^ j < 2 ^ (j - t) * 2 ^ t := hpow ▸ hr_lt
        have : (p % 2 ^ j) / 2 ^ t * 2 ^ t < 2 ^ (j - t) * 2 ^ t := lt_of_le_of_lt hdm hr_lt'
        exact Nat.lt_of_mul_lt_mul_right this
      have hq1_lt : (p % 2 ^ j) / 2 ^ t + 1 < 2 ^ (j - t) := by
        obtain ⟨c, hc⟩ := heven_pow; omega
      have hr_add_lt : p % 2 ^ j + 2 ^ t < 2 ^ j := by
        have hdm := Nat.div_add_mod (p % 2 ^ j) (2 ^ t)
        have hrm := Nat.mod_lt (p % 2 ^ j) hpt
        calc p % 2 ^ j + 2 ^ t
            = 2 ^ t * ((p % 2 ^ j) / 2 ^ t) + (p % 2 ^ j) % 2 ^ t + 2 ^ t := by rw [hdm]
          _ < 2 ^ t * ((p % 2 ^ j) / 2 ^ t) + 2 ^ t + 2 ^ t := by omega
          _ = ((p % 2 ^ j) / 2 ^ t + 2) * 2 ^ t := by ring
          _ <= 2 ^ (j - t) * 2 ^ t := Nat.mul_le_mul_right _ (by omega)
          _ = 2 ^ j := hpow.symm
      have hdiv : (p + 2 ^ t) / 2 ^ j = p / 2 ^ j := by
        have hd := Nat.div_add_mod p (2 ^ j)
        conv_lhs => rw [← hd]
        rw [Nat.add_assoc, Nat.mul_add_div hpj, Nat.div_eq_of_lt hr_add_lt, Nat.add_zero]
      rw [hdiv]
theorem z89 (p t j : ℕ) :
    (z75 p t).testBit j = if j = t then false else p.testBit j := by
  dsimp [z75]
  by_cases hbt : p.testBit t
  · simp only [hbt, ↓reduceIte]
    have hge : 2 ^ t <= p := by
      by_contra hlt
      have : p.testBit t = false := Nat.testBit_lt_two_pow (by omega)
      rw [this] at hbt; exact Bool.false_ne_true hbt
    have hqt : (p - 2 ^ t).testBit t = false := by
      simp only [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hbt ⊢
      have hpos : 0 < 2 ^ t := Nat.pow_pos (by omega)
      have hdiv : ((p - 2 ^ t) + 2 ^ t) / 2 ^ t = (p - 2 ^ t) / 2 ^ t + 1 :=
        Nat.add_div_right _ hpos
      rw [Nat.sub_add_cancel hge] at hdiv
      have hp1 : (p / 2 ^ t) % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one (p / 2 ^ t) with h | h
        · simp [h] at hbt
        · exact h
      have hq0 : ((p - 2 ^ t) / 2 ^ t) % 2 = 0 := by omega
      simp [hq0]
    have hstep := z149 (p - 2 ^ t) t j hqt
    rw [Nat.sub_add_cancel hge] at hstep
    by_cases hjt : j = t
    · subst hjt; simp [hqt]
    · simp only [if_neg hjt] at hstep ⊢; exact hstep.symm
  · have hbtf : p.testBit t = false := Bool.eq_false_iff.mpr hbt
    simp only [hbtf, Bool.false_eq_true, ↓reduceIte]
    by_cases hjt : j = t
    · subst hjt; simp [hbtf]
    · simp [hjt]
theorem z103 (p t j : ℕ) :
    (setBitNat p t).testBit j = if j = t then true else p.testBit j := by
  dsimp [setBitNat]
  by_cases hbt : p.testBit t
  · simp only [hbt, ↓reduceIte]
    by_cases hjt : j = t
    · subst hjt; simp [hbt]
    · simp [hjt]
  · have hbtf : p.testBit t = false := Bool.eq_false_iff.mpr hbt
    simp only [hbtf, Bool.false_eq_true, ↓reduceIte]
    exact z149 p t j hbtf
def z53 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) : List (Cl (VarAll k r h' R)) :=
  let dN := Nat.clog 2 (3 * k)
  have hNle : 3 * k <= 2 ^ dN := Nat.le_pow_clog (by omega) (3 * k)
  (List.finRange (3 * k)).flatMap fun i =>
    let uLeaf : Fin (2 ^ (dN + 1)) := ⟨2 ^ dN + i.val, by rw [pow_succ]; omega⟩
    let initCl := (List.finRange (2 ^ h')).flatMap fun c =>
      if rowMask (H m) c i then
        let dn := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c true uLeaf
        [imp1 dn.1 (vWalsh ori m i ⟨0, Nat.zero_lt_succ h'⟩ c false),
         imp1 dn.2 (vWalsh ori m i ⟨0, Nat.zero_lt_succ h'⟩ c true)]
      else []
    let stepCl := (List.finRange h').flatMap fun t =>
      let t0 : Fin (h' + 1) := ⟨t.val, by omega⟩
      let t1 : Fin (h' + 1) := ⟨t.val + 1, by omega⟩
      (List.finRange (2 ^ h')).flatMap fun p =>
        let p0 : Fin (2 ^ h') := ⟨z75 p.val t.val, z80 p.isLt⟩
        let p1 : Fin (2 ^ h') := ⟨setBitNat p.val t.val, z104 p.isLt t.isLt⟩
        let st : Bool := p.val.testBit t.val
        ([false, true] : List Bool).flatMap fun b =>
          [imp1 (vWalsh ori m i t0 p0 b) (vWalsh ori m i t1 p b),
           imp1 (vWalsh ori m i t0 p1 (xor b st)) (vWalsh ori m i t1 p b)]
    initCl ++ stepCl
def z12 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) : List (Cl (VarAll k r h' R)) :=
  let dN := Nat.clog 2 (3 * k)
  let xCl := (List.finRange (3 * k)).flatMap fun i =>
    let xd := drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i
    let raw := drvPos hk ori i
    [imp1 (vRaw raw false) xd.1,
     imp1 (vRaw raw true) xd.2,
     imp1 (vWalsh ori m i ⟨h', Nat.lt_succ_self h'⟩ s false) xd.1,
     imp1 (vWalsh ori m i ⟨h', Nat.lt_succ_self h'⟩ s true) xd.2,
     imp2 xd.1 xd.2 (vExcl ori m s)]
  let parCl := (List.finRange h').flatMap fun q =>
    let up := drPar (k := k) (r := r) (h' := h') (R := R) ori m s q
    let leafCl := (List.finRange (2 ^ dN)).flatMap fun j =>
      let u : Fin (2 ^ (dN + 1)) := ⟨2 ^ dN + j.val, by rw [pow_succ]; omega⟩
      if hj : j.val < 3 * k then
        if H m q ⟨j.val, hj⟩ then
          drEq (drXDual ori m s ⟨j.val, hj⟩) (up u)
        else
          drEq z3 (up u)
      else
        drEq z3 (up u)
    let root : Fin (2 ^ (dN + 1)) := ⟨1, by have := Nat.one_le_pow dN 2 (by omega); rw [pow_succ]; omega⟩
    let badBit := !(s.val.testBit q.val)
    leafCl ++ z14 dN up ++ [imp1 (drFlip (up root) badBit) (vExcl ori m s)]
  xCl ++ parCl
def z9 (hk : 0 < k) (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) : List (Cl (VarAll k r h' R)) :=
  let dk := Nat.clog 2 k
  let rev := branchRev ori isCol
  let drvSlot := z8 isCol
  let keyW : Fin k -> DualLit (VarAll k r h' R) := fun j => drXDual ori m s (drvIdx 0 j)
  let drvW : Fin k -> DualLit (VarAll k r h' R) := fun j => drXDual ori m s (drvIdx drvSlot j)
  let W := z91 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  let C := drLeafChi (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  let M := drLeafMix (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  let P := z137 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  let target := z15 ori isCol
  let tZero : Fin (r + 1) := ⟨0, Nat.zero_lt_succ r⟩
  let tLast : Fin (r + 1) := ⟨r, Nat.lt_succ_self r⟩
  let coreCl :=
    if !rev then
      let initCl := (List.finRange k).flatMap fun j =>
        let kj : Fin k := ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩
        drXor (keyW kj) (drvW j) (W tZero j 0)
      let roundCl := (List.finRange r).flatMap fun t =>
        let t0 : Fin (r + 1) := ⟨t.val, by omega⟩
        let t1 : Fin (r + 1) := ⟨t.val + 1, by omega⟩
        let δ := mixStride isCol
        (List.finRange k).flatMap fun j =>
          let j1 : Fin k := ⟨(j.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
          let j2 : Fin k := ⟨(j.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
          let jc1 : Fin k := ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
          let jc2 : Fin k := ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩
          let kj : Fin k := ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩
          let cb := constBit k (z10 isCol r t.val) j
          drXor (W t0 j 0) (W t0 j1 0) (W t0 j 1) ++
          drXor (W t0 j 1) (W t0 j2 0) (W t0 j 2) ++
          drAnd (drNot (W t0 jc1 2)) (W t0 jc2 2) (W t0 j 3) ++
          drXor (W t0 j 2) (W t0 j 3) (W t0 j 4) ++
          drXor (W t0 j 4) (z34 cb (keyW kj)) (W t1 j 0)
      let finCl := (List.finRange k).flatMap fun j => drEq (W tLast j 0) (W tZero j 8)
      let wrapCl := drEq z26 (P tLast true)
      initCl ++ roundCl ++ finCl ++ wrapCl
    else
      let initCl := (List.finRange k).flatMap fun j => drEq (drvW j) (W tZero j 0)
      let wrapInit := drEq z26 (P tZero true)
      let roundCl := (List.finRange r).flatMap fun t =>
        let t0 : Fin (r + 1) := ⟨t.val, by omega⟩
        let t1 : Fin (r + 1) := ⟨t.val + 1, by omega⟩
        let idx := r - 1 - t.val
        let δ := mixStride isCol
        let uCl := (List.finRange k).flatMap fun j =>
          let kj : Fin k := ⟨(j.val + k - z16 isCol idx % k) % k, Nat.mod_lt _ hk⟩
          let cb := constBit k (z10 isCol r idx) j
          drXor (W t0 j 0) (z34 cb (keyW kj)) (W t0 j 1)
        let upA : Fin (2 ^ (dk + 1)) -> DualLit (VarAll k r h' R) × DualLit (VarAll k r h' R) :=
          fun u => (C t 0 u, C t 1 u)
        let prA : Fin (2 ^ (dk + 1)) -> DualLit (VarAll k r h' R) × DualLit (VarAll k r h' R) :=
          fun u => (C t 2 u, C t 3 u)
        let sfA : Fin (2 ^ (dk + 1)) -> DualLit (VarAll k r h' R) × DualLit (VarAll k r h' R) :=
          fun u => (C t 4 u, C t 5 u)
        let tuA := C t 6
        let tpA := C t 7
        let tsA := C t 8
        let rootK : Fin (2 ^ (dk + 1)) := ⟨1, by have := Nat.one_le_pow dk 2 (by omega); rw [pow_succ]; omega⟩
        let chiLeafCl := (List.finRange (2 ^ dk)).flatMap fun p =>
          let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by rw [pow_succ]; omega⟩
          if hp : p.val < k then
            let i0 := z21 k p.val hk
            let i1 : Fin k := ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩
            drEq (drNot (W t0 i1 1)) (upA u).1 ++ drEq (W t0 i0 1) (upA u).2
          else
            drEq z26 (upA u).1 ++ drEq z3 (upA u).2
        let chiRootCl :=
          drEq z26 (prA rootK).1 ++ drEq z3 (prA rootK).2 ++
          drEq z26 (sfA rootK).1 ++ drEq z3 (sfA rootK).2
        let chiOutCl := (List.finRange k).flatMap fun (p : Fin k) =>
          have hp_pow : p.val < 2 ^ dk := lt_of_lt_of_le p.isLt (Nat.le_pow_clog (by omega) k)
          let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by rw [pow_succ]; omega⟩
          let i0 := z21 k p.val hk
          let i1 : Fin k := ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩
          drAffComp (drNot (W t0 i1 1), W t0 i0 1) (sfA u) (W t0 p 2, W t0 p 3) (W t0 p 4) ++
          drAnd (W t0 p 2) (prA u).2 (W t0 p 5) ++
          drXor (W t0 p 3) (W t0 p 5) (W t0 p 6)
        let wBit : Fin k -> DualLit (VarAll k r h' R) := fun i => W t0 (z19 k hk i) 6
        let mixCl :=
          if k % 3 = 0 then
            let m3 := k / 3
            let b0 := leaf.val.testBit (2 * idx)
            let b1 := leaf.val.testBit (2 * idx + 1)
            let treeCl := (List.finRange 3).flatMap fun rc =>
              let upM := M t rc false
              let prM := M t rc true
              let lfCl := (List.finRange (2 ^ dk)).flatMap fun q =>
                let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + q.val, by rw [pow_succ]; omega⟩
                if q.val < m3 then
                  drXor (wBit (sIdx hk δ (3 * q.val + rc.val + 1)))
                    (wBit (sIdx hk δ (3 * q.val + rc.val + 2))) (upM u)
                else
                  drEq z3 (upM u)
              lfCl ++ drEq z3 (prM rootK) ++
              z14 dk upM ++ z18 dk upM prM
            let outMixCl := (List.finRange k).flatMap fun (i : Fin k) =>
              let pv := (sInv hk δ i).val
              let rc : Fin 3 := ⟨pv % 3, Nat.mod_lt _ (by omega)⟩
              let qv := pv / 3
              have hq_pow : qv < 2 ^ dk := lt_of_lt_of_le (by have := (sInv hk δ i).isLt; omega)
                (Nat.le_pow_clog (by omega) k)
              let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + qv, by rw [pow_succ]; omega⟩
              let prefW := M t rc true u
              if rc.val = 0 then
                drEq (z34 b0 prefW) (W t1 i 0)
              else if rc.val = 1 then
                drEq (z34 b1 prefW) (W t1 i 0)
              else
                drXor (z34 (xor b0 b1) (wBit (sIdx hk δ 1))) prefW (W t1 i 0)
            let stepWrapCl :=
              drAnd (drNot (M t 0 false rootK)) (drNot (M t 1 false rootK)) (P t0 false) ++
              drAnd (P t0 true) (P t0 false) (P t1 true)
            treeCl ++ outMixCl ++ stepWrapCl
          else if k < 5 then
            let copyCl := (List.finRange k).flatMap fun i => drEq (wBit i) (W t1 i 0)
            let stepWrapCl :=
              drEq z26 (P t0 false) ++
              drAnd (P t0 true) (P t0 false) (P t1 true)
            copyCl ++ stepWrapCl
          else
            let upM := M t 0 false
            let prM := M t 0 true
            let lfCl := (List.finRange (2 ^ dk)).flatMap fun p =>
              let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by rw [pow_succ]; omega⟩
              if p.val < k then
                let a1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
                let a2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
                drXor (wBit a1) (wBit a2) (upM u)
              else
                drEq z3 (upM u)
            let pPos := inv3Pos k % k
            let pNeg := (k - pPos) % k
            have hpPos_lt : pPos < 2 ^ dk := lt_of_lt_of_le (Nat.mod_lt _ hk) (Nat.le_pow_clog (by omega) k)
            have hpNeg_lt : pNeg < 2 ^ dk := lt_of_lt_of_le (Nat.mod_lt _ hk) (Nat.le_pow_clog (by omega) k)
            let uPos : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + pPos, by rw [pow_succ]; omega⟩
            let uNeg : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + pNeg, by rw [pow_succ]; omega⟩
            let j0 : Fin k := ⟨0, hk⟩
            let j1 : Fin k := ⟨1 % k, Nat.mod_lt _ hk⟩
            let x0Cl :=
              drXor (wBit j0) (prM uPos) (W t0 j0 7) ++
              drXor (W t0 j0 7) (prM uNeg) (W t0 j1 7)
            let outMixCl := (List.finRange k).flatMap fun (i : Fin k) =>
              let mv := (m3dInv k δ hk i).val
              have hmv : mv < 2 ^ dk := lt_of_lt_of_le (m3dInv k δ hk i).isLt (Nat.le_pow_clog (by omega) k)
              let uM : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + mv, by rw [pow_succ]; omega⟩
              drXor (W t0 j1 7) (prM uM) (W t1 i 0)
            let stepWrapCl :=
              drEq z26 (P t0 false) ++
              drAnd (P t0 true) (P t0 false) (P t1 true)
            lfCl ++ drEq z3 (prM rootK) ++
              z14 dk upM ++ z18 dk upM prM ++
              x0Cl ++ outMixCl ++ stepWrapCl
        uCl ++ chiLeafCl ++ chiRootCl ++
          z39 dk upA tuA ++
          z28 dk upA prA tpA ++
          z36 dk upA sfA tsA ++
          chiOutCl ++ mixCl
      let finCl := (List.finRange k).flatMap fun j =>
        let kj : Fin k := ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩
        drXor (keyW kj) (W tLast j 0) (W tZero j 8)
      initCl ++ wrapInit ++ roundCl ++ finCl
  let deadCl :=
    [imp1 (vExcl ori m s) (vLeafDead ori m s isCol leaf),
     imp1 (P tLast true).1 (vLeafDead ori m s isCol leaf)] ++
    (List.finRange k).flatMap fun j =>
      [imp2 (vRaw (target, j) true) (W tZero j 8).1 (vLeafDead ori m s isCol leaf),
       imp2 (vRaw (target, j) false) (W tZero j 8).2 (vLeafDead ori m s isCol leaf)]
  let killCl := (List.finRange k).flatMap fun j =>
    ([false, true] : List Bool).flatMap fun b =>
      [imp1 (vLeafDead ori m s isCol leaf) (z90 ori m s isCol leaf j b),
       imp1 (drFlip (W tZero j 8) (!b)) (z90 ori m s isCol leaf j b)]
  coreCl ++ deadCl ++ killCl
def z35 (hk : 0 < k) (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) :
    List (Cl (VarAll k r h' R)) :=
  let dB := dBOf k r
  let rootB : Fin (2 ^ (dB + 1)) := ⟨1, by have := Nat.one_le_pow dB 2 (by omega); rw [pow_succ]; omega⟩
  let deadTrees := ([false, true] : List Bool).flatMap fun isCol =>
    let nd := z69 (k := k) (r := r) (h' := h') (R := R) ori m s isCol
    let lfCl := (List.finRange (2 ^ dB)).flatMap fun l =>
      let lf : Fin (z2 k r) := ⟨l.val, by rw [← z67]; exact l.isLt⟩
      let u : Fin (2 ^ (dB + 1)) := ⟨2 ^ dB + l.val, by rw [pow_succ]; omega⟩
      [imp1 (vLeafDead ori m s isCol lf) (nd u)]
    lfCl ++ z24 dB nd ++ [imp1 (nd rootB) (vSynDead ori m s)]
  let synDeadBase := [imp1 (vExcl ori m s) (vSynDead ori m s)]
  let killTrees := ([false, true] : List Bool).flatMap fun isCol =>
    (List.finRange k).flatMap fun j =>
      ([false, true] : List Bool).flatMap fun b =>
        let nd := z68 (k := k) (r := r) (h' := h') (R := R) ori m s isCol j b
        let lfCl := (List.finRange (2 ^ dB)).flatMap fun l =>
          let lf : Fin (z2 k r) := ⟨l.val, by rw [← z67]; exact l.isLt⟩
          let u : Fin (2 ^ (dB + 1)) := ⟨2 ^ dB + l.val, by rw [pow_succ]; omega⟩
          [imp1 (z90 ori m s isCol lf j b) (nd u)]
        let target := z15 ori isCol
        lfCl ++ z24 dB nd ++ [imp1 (nd rootB) (vKillLit ori m s (target, j) b)]
  let killLitCl := (List.finRange 5).flatMap fun tr =>
    (List.finRange k).flatMap fun j =>
      ([false, true] : List Bool).flatMap fun b =>
        [imp1 (vSynDead ori m s) (vKillLit ori m s (tr, j) b)]
  let drvKillCl := (List.finRange 3).flatMap fun slot =>
    (List.finRange k).flatMap fun j =>
      ([false, true] : List Bool).flatMap fun b =>
        [imp1 (drFlip (drXDual ori m s (drvIdx slot j)) (!b))
          (vKillLit ori m s (dTrack ori slot, j) b)]
  deadTrees ++ synDeadBase ++ killTrees ++ killLitCl ++ drvKillCl
def z48 (ori : Bool × Bool) (m : Fin R) : List (Cl (VarAll k r h' R)) :=
  let rootH : Fin (2 ^ (h' + 1)) := ⟨1, by have := Nat.one_le_pow h' 2 (by omega); rw [pow_succ]; omega⟩
  let deadNd := z156 (k := k) (r := r) (h' := h') (R := R) ori m
  let deadLeaf := (List.finRange (2 ^ h')).flatMap fun s =>
    let u : Fin (2 ^ (h' + 1)) := ⟨2 ^ h' + s.val, by rw [pow_succ]; omega⟩
    [imp1 (vSynDead ori m s) (deadNd u)]
  let deadCl := deadLeaf ++ z24 h' deadNd ++ [cl1 (negL (deadNd rootH))]
  let litCl := (List.finRange 5).flatMap fun tr =>
    (List.finRange k).flatMap fun j =>
      ([false, true] : List Bool).flatMap fun b =>
        let nd := vAllKilled (k := k) (r := r) (h' := h') (R := R) ori m (tr, j) b
        let lf := (List.finRange (2 ^ h')).flatMap fun s =>
          let u : Fin (2 ^ (h' + 1)) := ⟨2 ^ h' + s.val, by rw [pow_succ]; omega⟩
          [imp1 (vKillLit ori m s (tr, j) b) (nd u)]
        lf ++ z24 h' nd ++ [imp1 (nd rootH) (vRaw (tr, j) (!b))]
  deadCl ++ litCl
def z47 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) : List (Cl (VarAll k r h' R)) :=
  z40 hk H ori m ++
  z53 hk H ori m ++
  ((List.finRange (2 ^ h')).flatMap fun s =>
    z12 hk H ori m s ++
    (([false, true] : List Bool).flatMap fun isCol =>
      (List.finRange (z2 k r)).flatMap fun leaf =>
        z9 hk ori m s isCol leaf) ++
    z35 hk ori m s) ++
  z48 ori m
def z7 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) : List (Cl (VarAll k r h' R)) :=
  z92 ++
  z64 hk ++
  (([false, true] : List Bool).flatMap fun rR =>
    ([false, true] : List Bool).flatMap fun cR =>
      (List.finRange R).flatMap fun m =>
        z47 hk H (rR, cR) m)
end Builders
section SatAndSize
variable {k r h' R : ℕ}
theorem constClauses_card : ∀ C ∈ (z92 (k := k) (r := r) (h' := h') (R := R)), C.card <= 3 := by
  intro C hC; simp only [z92, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl <;> exact cl1_card _
theorem baseClauses_card (hk : 0 < k) :
    ∀ C ∈ (z64 (k := k) (r := r) (h' := h') (R := R) hk), C.card <= 3 := by
  intro C hC; dsimp only [z64] at hC
  rw [List.mem_flatMap] at hC; rcases hC with ⟨isCol, _, h1⟩
  simp only [List.mem_append] at h1
  rcases h1 with (hinit | hround) | hout
  · rw [List.mem_flatMap] at hinit; rcases hinit with ⟨j, _, hj⟩
    exact tsXor_card _ _ _ C hj
  · rw [List.mem_flatMap] at hround; rcases hround with ⟨t, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
    simp only [List.mem_append] at hj
    rcases hj with (((h1 | h2) | h3) | h4) | h5
    · exact tsXor_card _ _ _ C h1
    · exact tsXor_card _ _ _ C h2
    · exact tsAnd_card _ _ _ C h3
    · exact tsXor_card _ _ _ C h4
    · exact tsXor_card _ _ _ C h5
  · rw [List.mem_flatMap] at hout; rcases hout with ⟨j, _, hj⟩
    exact tsEq_card _ _ C hj
theorem upDownClauses_card (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ (z40 (k := k) (r := r) (h' := h') (R := R) hk H ori m), C.card <= 3 := by
  intro C hC; dsimp only [z40] at hC
  rw [List.mem_flatMap] at hC; rcases hC with ⟨c, _, hc⟩
  simp only [List.mem_append] at hc
  rcases hc with ((h1 | h2) | h3) | h4
  · rw [List.mem_flatMap] at h1; rcases h1 with ⟨j, _, hj⟩
    split_ifs at hj <;> exact drEq_card _ _ C hj
  · exact drEq_card _ _ C h2
  · exact z72 _ _ C h3
  · exact heapXorCompClauses_card _ _ _ C h4
theorem walshClauses_card (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ (z53 (k := k) (r := r) (h' := h') (R := R) hk H ori m), C.card <= 3 := by
  intro C hC; dsimp only [z53] at hC
  rw [List.mem_flatMap] at hC; rcases hC with ⟨i, _, hi⟩
  rw [List.mem_append] at hi
  rcases hi with h1 | h2
  · rw [List.mem_flatMap] at h1; rcases h1 with ⟨c, _, hc⟩
    split_ifs at hc
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact imp1_card _ _
    · simp at hc
  · rw [List.mem_flatMap] at h2; rcases h2 with ⟨t, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨p, _, hp⟩
    rw [List.mem_flatMap] at hp; rcases hp with ⟨b, _, hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact imp1_card _ _
theorem z151 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) :
    ∀ C ∈ (z12 (k := k) (r := r) (h' := h') (R := R) hk H ori m s), C.card <= 3 := by
  intro C hC; dsimp only [z12] at hC
  rw [List.mem_append] at hC
  rcases hC with h1 | h2
  · rw [List.mem_flatMap] at h1; rcases h1 with ⟨i, _, hi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact imp1_card _ _
    · exact imp1_card _ _
    · exact imp1_card _ _
    · exact imp1_card _ _
    · exact imp2_card _ _ _
  · rw [List.mem_flatMap] at h2; rcases h2 with ⟨q, _, hq⟩
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hlf | hup) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨j, _, hj⟩
      split_ifs at hj <;> exact drEq_card _ _ C hj
    · exact z72 _ _ C hup
    · exact imp1_card _ _
theorem leafCircuitClauses_card (hk : 0 < k) (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) :
    ∀ C ∈ (z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf), C.card <= 3 := by
  intro C hC; dsimp only [z9] at hC
  simp only [List.mem_append] at hC
  rcases hC with (hcore | hdead) | hkill
  · by_cases hrev : (!branchRev ori isCol) = true
    on_goal 1 => simp only [hrev, ↓reduceIte] at hcore
    on_goal 2 =>
      have hrevF : (!branchRev ori isCol) = false := Bool.eq_false_iff.mpr hrev
      simp only [hrevF, Bool.false_eq_true, ↓reduceIte] at hcore
    · simp only [List.mem_append] at hcore
      rcases hcore with ((h1 | h2) | h3) | h4
      · rw [List.mem_flatMap] at h1; rcases h1 with ⟨j, _, hj⟩; exact z52 _ _ _ C hj
      · rw [List.mem_flatMap] at h2; rcases h2 with ⟨t, _, ht⟩
        rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
        simp only [List.mem_append] at hj
        rcases hj with (((a | b) | c) | d) | e
        · exact z52 _ _ _ C a
        · exact z52 _ _ _ C b
        · exact z138 _ _ _ C c
        · exact z52 _ _ _ C d
        · exact z52 _ _ _ C e
      · rw [List.mem_flatMap] at h3; rcases h3 with ⟨j, _, hj⟩; exact drEq_card _ _ C hj
      · exact drEq_card _ _ C h4
    · simp only [List.mem_append] at hcore
      rcases hcore with ((h1 | h2) | h3) | h4
      · rw [List.mem_flatMap] at h1; rcases h1 with ⟨j, _, hj⟩; exact drEq_card _ _ C hj
      · exact drEq_card _ _ C h2
      · rw [List.mem_flatMap] at h3; rcases h3 with ⟨t, _, ht⟩
        simp only [List.mem_append] at ht
        rcases ht with ((((((hu | hcl) | hcr) | ha1) | ha2) | ha3) | hco) | hmix
        · rw [List.mem_flatMap] at hu; rcases hu with ⟨j, _, hj⟩; exact z52 _ _ _ C hj
        · rw [List.mem_flatMap] at hcl; rcases hcl with ⟨p, _, hp⟩
          split_ifs at hp <;> rw [List.mem_append] at hp <;> rcases hp with a | b <;> exact drEq_card _ _ C ‹_›
        · rcases hcr with ((a | b) | c) | d <;> exact drEq_card _ _ C ‹_›
        · exact heapAffUpClauses_card _ _ _ C ha1
        · exact heapAffPrefClauses_card _ _ _ _ C ha2
        · exact heapAffSufClauses_card _ _ _ _ C ha3
        · rw [List.mem_flatMap] at hco; rcases hco with ⟨p, _, hp⟩
          simp only [List.mem_append] at hp
          rcases hp with (a | b) | c
          · exact z135 _ _ _ _ C a
          · exact z138 _ _ _ C b
          · exact z52 _ _ _ C c
        · split_ifs at hmix
          · simp only [List.mem_append] at hmix
            rcases hmix with (htr | hout) | hsw
            · rw [List.mem_flatMap] at htr; rcases htr with ⟨rc, _, hrc⟩
              simp only [List.mem_append] at hrc
              rcases hrc with ((hlf | hrt) | hup) | hpr
              · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨q, _, hq⟩
                split_ifs at hq
                · exact z52 _ _ _ C hq
                · exact drEq_card _ _ C hq
              · exact drEq_card _ _ C hrt
              · exact z72 _ _ C hup
              · exact z114 _ _ _ C hpr
            · rw [List.mem_flatMap] at hout; rcases hout with ⟨i, _, hi⟩
              split_ifs at hi
              · exact drEq_card _ _ C hi
              · exact drEq_card _ _ C hi
              · exact z52 _ _ _ C hi
            · rcases hsw with a | b <;> exact z138 _ _ _ C ‹_›
          · simp only [List.mem_append] at hmix
            rcases hmix with hcp | (a | b)
            · rw [List.mem_flatMap] at hcp; rcases hcp with ⟨i, _, hi⟩; exact drEq_card _ _ C hi
            · exact drEq_card _ _ C a
            · exact z138 _ _ _ C b
          · simp only [List.mem_append] at hmix
            rcases hmix with (((((hlf | hrt) | hup) | hpr) | hx0) | hout) | hsw
            · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨p, _, hp⟩
              split_ifs at hp
              · exact z52 _ _ _ C hp
              · exact drEq_card _ _ C hp
            · exact drEq_card _ _ C hrt
            · exact z72 _ _ C hup
            · exact z114 _ _ _ C hpr
            · rcases hx0 with a | b <;> exact z52 _ _ _ C ‹_›
            · rw [List.mem_flatMap] at hout; rcases hout with ⟨i, _, hi⟩; exact z52 _ _ _ C hi
            · rcases hsw with a | b
              · exact drEq_card _ _ C a
              · exact z138 _ _ _ C b
      · rw [List.mem_flatMap] at h4; rcases h4 with ⟨j, _, hj⟩; exact z52 _ _ _ C hj
  · rcases hdead with h1 | h2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl <;> exact imp1_card _ _
    · rw [List.mem_flatMap] at h2; rcases h2 with ⟨j, _, hj⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> exact imp2_card _ _ _
  · rw [List.mem_flatMap] at hkill; rcases hkill with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact imp1_card _ _
theorem synAggClauses_card (hk : 0 < k) (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) :
    ∀ C ∈ (z35 (k := k) (r := r) (h' := h') (R := R) hk ori m s), C.card <= 3 := by
  intro C hC; dsimp only [z35] at hC
  simp only [List.mem_append] at hC
  rcases hC with (((h1 | h2) | h3) | h4) | h5
  · rw [List.mem_flatMap] at h1; rcases h1 with ⟨isCol, _, hi⟩
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with (hlf | ha) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨l, _, hl⟩
      simp only [List.mem_singleton] at hl; rw [hl]; exact imp1_card _ _
    · exact z88 _ _ C ha
    · exact imp1_card _ _
  · simp only [List.mem_singleton] at h2; rw [h2]; exact imp1_card _ _
  · rw [List.mem_flatMap] at h3; rcases h3 with ⟨isCol, _, hi⟩
    rw [List.mem_flatMap] at hi; rcases hi with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (hlf | ha) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨l, _, hl⟩
      simp only [List.mem_singleton] at hl; rw [hl]; exact imp1_card _ _
    · exact z88 _ _ C ha
    · exact imp1_card _ _
  · rw [List.mem_flatMap] at h4; rcases h4 with ⟨tr, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    simp only [List.mem_singleton] at hb; rw [hb]; exact imp1_card _ _
  · rw [List.mem_flatMap] at h5; rcases h5 with ⟨slot, _, hs⟩
    rw [List.mem_flatMap] at hs; rcases hs with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    simp only [List.mem_singleton] at hb; rw [hb]; exact imp1_card _ _
theorem matAggClauses_card (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ (z48 (k := k) (r := r) (h' := h') (R := R) ori m), C.card <= 3 := by
  intro C hC; dsimp only [z48] at hC
  rw [List.mem_append] at hC
  rcases hC with h1 | h2
  · simp only [List.mem_append, List.mem_singleton] at h1
    rcases h1 with (hlf | ha) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨s, _, hs⟩
      simp only [List.mem_singleton] at hs; rw [hs]; exact imp1_card _ _
    · exact z88 _ _ C ha
    · exact cl1_card _
  · rw [List.mem_flatMap] at h2; rcases h2 with ⟨tr, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (hlf | ha) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨s, _, hs⟩
      simp only [List.mem_singleton] at hs; rw [hs]; exact imp1_card _ _
    · exact z88 _ _ C ha
    · exact imp1_card _ _
theorem z141 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) :
    ∀ C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H), C.card <= 3 := by
  intro C hC; dsimp only [z7] at hC
  simp only [List.mem_append] at hC
  rcases hC with (h1 | h2) | h3
  · exact constClauses_card C h1
  · exact baseClauses_card hk C h2
  · rw [List.mem_flatMap] at h3; rcases h3 with ⟨rR, _, h3⟩
    rw [List.mem_flatMap] at h3; rcases h3 with ⟨cR, _, h3⟩
    rw [List.mem_flatMap] at h3; rcases h3 with ⟨m, _, hm⟩
    dsimp only [z47] at hm
    simp only [List.mem_append] at hm
    rcases hm with ((ha | hb) | hc) | hd
    · exact upDownClauses_card hk H (rR, cR) m C ha
    · exact walshClauses_card hk H (rR, cR) m C hb
    · rw [List.mem_flatMap] at hc; rcases hc with ⟨s, _, hs⟩
      simp only [List.mem_append] at hs
      rcases hs with (hsi | hsl) | hsa
      · exact z151 hk H (rR, cR) m s C hsi
      · rw [List.mem_flatMap] at hsl; rcases hsl with ⟨isCol, _, hi⟩
        rw [List.mem_flatMap] at hi; rcases hi with ⟨leaf, _, hl⟩
        exact leafCircuitClauses_card hk (rR, cR) m s isCol leaf C hl
      · exact synAggClauses_card hk (rR, cR) m s C hsa
    · exact matAggClauses_card (rR, cR) m C hd
theorem baseClauses_sound (hk : 0 < k) (v : V5 k -> Bool) (aux : AuxAll k r h' R -> Bool)
    (hsat : ∀ C ∈ (z64 (k := k) (r := r) (h' := h') (R := R) hk), ClauseSat (Sum.elim v aux) C) :
    (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) /\
    (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j)) := by
  let α := Sum.elim v aux
  have hbranch : ∀ isCol : Bool,
      (fun j => v (if isCol then 4 else 3, j)) =
        z42 hk r isCol (fun j => v (2, j)) (fun j => v (if isCol then 1 else 0, j)) := by
    intro isCol
    let key : Fin k -> Bool := fun j => v (2, j)
    let inp : Fin k -> Bool := fun j => v (if isCol then 1 else 0, j)
    let init : Fin k -> Bool := fun j => xor (rotB hk (initRot isCol) key j) (inp j)
    have hmem_isCol : isCol ∈ ([false, true] : List Bool) := by cases isCol <;> simp
    have hind : ∀ (t : ℕ) (ht : t <= r) (j : Fin k),
        lEv α (vBase (k := k) (r := r) (h' := h') (R := R) isCol ⟨t, by omega⟩ j 0) =
          fwdIterB hk isCol r key init t j := by
      intro t
      induction t with
      | zero =>
        intro _ j
        have hC : ∀ C ∈ tsXor (vRaw (2, ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩) true)
            (vRaw (if isCol then 1 else 0, j) true)
            (vBase (k := k) (r := r) (h' := h') (R := R) isCol ⟨0, Nat.zero_lt_succ r⟩ j 0),
            ClauseSat α C := by
          intro C hC; apply hsat; dsimp only [z64]
          rw [List.mem_flatMap]; refine ⟨isCol, hmem_isCol, ?_⟩
          simp only [List.mem_append]; left; left
          rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hC⟩
        have heq := (z59 α _ _ _).mp hC
        simpa [α, lEv, vRaw, init, rotB, key, inp, fwdIterB] using heq
      | succ t ih =>
        intro ht j
        have ht_lt : t < r := by omega
        let tf : Fin r := ⟨t, ht_lt⟩
        let t0 : Fin (r + 1) := ⟨t, by omega⟩
        let t1 : Fin (r + 1) := ⟨t + 1, by omega⟩
        have hsat_r : ∀ (j' : Fin k),
            let δ := mixStride isCol
            let j1 : Fin k := ⟨(j'.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
            let j2 : Fin k := ⟨(j'.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
            let jc1 : Fin k := ⟨(j'.val + 1) % k, Nat.mod_lt _ hk⟩
            let jc2 : Fin k := ⟨(j'.val + 2) % k, Nat.mod_lt _ hk⟩
            let kj : Fin k := ⟨(j'.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩
            let cb := constBit k (z10 isCol r t) j'
            let keyLit := if cb then negL (vRaw (2, kj) true) else vRaw (2, kj) true
            lEv α (vBase (k := k) (r := r) (h' := h') (R := R) isCol t0 j' 1) =
              xor (lEv α (vBase isCol t0 j' 0)) (lEv α (vBase isCol t0 j1 0)) /\
            lEv α (vBase isCol t0 j' 2) =
              xor (lEv α (vBase isCol t0 j' 1)) (lEv α (vBase isCol t0 j2 0)) /\
            lEv α (vBase isCol t0 j' 3) =
              (!(lEv α (vBase isCol t0 jc1 2)) && lEv α (vBase isCol t0 jc2 2)) /\
            lEv α (vBase isCol t0 j' 4) =
              xor (lEv α (vBase isCol t0 j' 2)) (lEv α (vBase isCol t0 j' 3)) /\
            lEv α (vBase isCol t1 j' 0) =
              xor (lEv α (vBase isCol t0 j' 4)) (lEv α keyLit) := by
          intro j'
          have hall : ∀ C ∈
              (let δ := mixStride isCol
               let j1 : Fin k := ⟨(j'.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
               let j2 : Fin k := ⟨(j'.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
               let jc1 : Fin k := ⟨(j'.val + 1) % k, Nat.mod_lt _ hk⟩
               let jc2 : Fin k := ⟨(j'.val + 2) % k, Nat.mod_lt _ hk⟩
               let kj : Fin k := ⟨(j'.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩
               let cb := constBit k (z10 isCol r t) j'
               let keyLit := if cb then negL (vRaw (2, kj) true) else vRaw (2, kj) true
               tsXor (vBase (k := k) (r := r) (h' := h') (R := R) isCol t0 j' 0) (vBase isCol t0 j1 0) (vBase isCol t0 j' 1) ++
               tsXor (vBase isCol t0 j' 1) (vBase isCol t0 j2 0) (vBase isCol t0 j' 2) ++
               tsAnd (negL (vBase isCol t0 jc1 2)) (vBase isCol t0 jc2 2) (vBase isCol t0 j' 3) ++
               tsXor (vBase isCol t0 j' 2) (vBase isCol t0 j' 3) (vBase isCol t0 j' 4) ++
               tsXor (vBase isCol t0 j' 4) keyLit (vBase isCol t1 j' 0)), ClauseSat α C := by
            intro C hC; apply hsat; dsimp only [z64]
            rw [List.mem_flatMap]; refine ⟨isCol, hmem_isCol, ?_⟩
            simp only [List.mem_append]; left; right
            rw [List.mem_flatMap]; refine ⟨tf, List.mem_finRange tf, ?_⟩
            rw [List.mem_flatMap]; exact ⟨j', List.mem_finRange j', hC⟩
          refine ⟨(z59 α _ _ _).mp (fun C hC => hall C (by simp [hC])),
                  (z59 α _ _ _).mp (fun C hC => hall C (by simp [hC])),
                  by rw [← lEv_negL]; exact (tsAnd_sat_iff α _ _ _).mp (fun C hC => hall C (by simp [hC])),
                  (z59 α _ _ _).mp (fun C hC => hall C (by simp [hC])),
                  (z59 α _ _ _).mp (fun C hC => hall C (by simp [hC]))⟩
        have hmix : ∀ j' : Fin k, lEv α (vBase (k := k) (r := r) (h' := h') (R := R) isCol t0 j' 2) =
            mixB hk (mixStride isCol) (fwdIterB hk isCol r key init t) j' := by
          intro j'
          obtain ⟨h1, h2, _, _, _⟩ := hsat_r j'
          rw [h2, h1, ih (by omega), ih (by omega), ih (by omega)]
          rfl
        obtain ⟨_, _, h3, h4, h5⟩ := hsat_r j
        rw [h5, h4, h3, hmix, hmix, hmix]
        dsimp only [fwdIterB, fwdRoundB, stepB]
        have hkl : lEv α (if constBit k (z10 isCol r t) j then
            negL (vRaw (2, ⟨(j.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩) true)
            else vRaw (2, ⟨(j.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩) true) =
            xor (rotB hk (z16 isCol t) key j) (constBit k (z10 isCol r t) j) := by
          cases constBit k (z10 isCol r t) j
          · simp [α, lEv, vRaw, rotB, key]
          · simp only [↓reduceIte, lEv_negL]; simp [α, lEv, vRaw, rotB, key]
        rw [hkl]
        cases mixB hk (mixStride isCol) (fwdIterB hk isCol r key init t) j <;>
          cases mixB hk (mixStride isCol) (fwdIterB hk isCol r key init t) ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ <;>
          cases mixB hk (mixStride isCol) (fwdIterB hk isCol r key init t) ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ <;>
          cases rotB hk (z16 isCol t) key j <;>
          cases constBit k (z10 isCol r t) j <;> rfl
    ext j
    have hout : ∀ C ∈ tsEq (vBase (k := k) (r := r) (h' := h') (R := R) isCol ⟨r, Nat.lt_succ_self r⟩ j 0)
        (vRaw (if isCol then 4 else 3, j) true), ClauseSat α C := by
      intro C hC; apply hsat; dsimp only [z64]
      rw [List.mem_flatMap]; refine ⟨isCol, hmem_isCol, ?_⟩
      simp only [List.mem_append]; right
      rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hC⟩
    have heq := (tsEq_sat_iff α _ _).mp hout
    rw [hind r (le_refl r) j] at heq
    simpa [α, lEv, vRaw, z42, key, inp, init] using heq.symm
  exact ⟨by rw [← z61]; exact hbranch false,
         by rw [← z71]; exact hbranch true⟩
def z74 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) (ori : Bool × Bool) (m : Fin R)
    (v : V5 k -> Bool) (i : Fin (3 * k)) : ℕ -> Fin (2 ^ h') -> Bool -> Bool
  | 0, c, b =>
    let dN := Nat.clog 2 (3 * k)
    let fMask : ℕ -> Bool := fun j =>
      if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && v (drvPos hk ori ⟨j, hj⟩) else false
    rowMask (H m) c i && (z23 fMask dN (2 ^ dN + i.val) == b)
  | t + 1, p, b =>
    if ht : t < h' then
      let p0 : Fin (2 ^ h') := ⟨z75 p.val t, z80 p.isLt⟩
      let p1 : Fin (2 ^ h') := ⟨setBitNat p.val t, z104 p.isLt ht⟩
      z74 hk H ori m v i t p0 b ||
        z74 hk H ori m v i t p1 (xor b (p.val.testBit t))
    else false
theorem z130 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) (ori : Bool × Bool) (m : Fin R)
    (v : V5 k -> Bool) (i : Fin (3 * k)) :
    ∀ (t : ℕ) (ht : t <= h') (p : Fin (2 ^ h')) (b : Bool),
      z74 hk H ori m v i t p b = true ->
      ∃ c : Fin (2 ^ h'),
        (∀ q, t <= q -> c.val.testBit q = p.val.testBit q) /\
        rowMask (H m) c i = true /\
        xor (z23 (fun j =>
              if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && v (drvPos hk ori ⟨j, hj⟩) else false)
              (Nat.clog 2 (3 * k)) (2 ^ (Nat.clog 2 (3 * k)) + i.val))
            (xorFin (fun q : Fin t => c.val.testBit q.val && p.val.testBit q.val)) = b
  | 0, _, c, b, h => by
    simp only [z74, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨c, fun _ _ => rfl, h.1, ?_⟩
    rw [xorFin_zero, Bool.xor_false]; exact h.2
  | t + 1, ht, p, b, h => by
    have ht' : t < h' := by omega
    simp only [z74, ht', ↓reduceDIte, Bool.or_eq_true] at h
    rcases h with h0 | h1
    · obtain ⟨c, hbits, hrm, hval⟩ := z130 hk H ori m v i t (by omega)
        ⟨z75 p.val t, z80 p.isLt⟩ b h0
      have hct : c.val.testBit t = false := by
        rw [hbits t (le_refl t)]; dsimp; rw [z89]; simp
      refine ⟨c, fun q hq => ?_, hrm, ?_⟩
      · rw [hbits q (by omega)]; dsimp; rw [z89]
        have hne : q ≠ t := by omega
        simp [hne]
      · rw [z121]; simp only [Fin.val_last, hct, Bool.false_and, Bool.xor_false]
        rw [← hval]; congr 1
        refine z58 fun q => ?_
        dsimp; rw [z89]
        have hne : q.val ≠ t := by omega
        simp [hne]
    · obtain ⟨c, hbits, hrm, hval⟩ := z130 hk H ori m v i t (by omega)
        ⟨setBitNat p.val t, z104 p.isLt ht'⟩ (xor b (p.val.testBit t)) h1
      have hct : c.val.testBit t = true := by
        rw [hbits t (le_refl t)]; dsimp; rw [z103]; simp
      refine ⟨c, fun q hq => ?_, hrm, ?_⟩
      · rw [hbits q (by omega)]; dsimp; rw [z103]
        have hne : q ≠ t := by omega
        simp [hne]
      · rw [z121]; simp only [Fin.val_last, hct, Bool.true_and]
        have hcongr : xorFin (fun q : Fin t => c.val.testBit q.val && p.val.testBit q.val) =
            xorFin (fun q : Fin t => c.val.testBit q.val && (setBitNat p.val t).testBit q.val) := by
          refine z58 fun q => ?_
          rw [z103]
          have hne : q.val ≠ t := by omega
          simp [hne]
        simp only [Fin.val_castSucc]
        rw [hcongr, ← Bool.xor_assoc]
        dsimp at hval
        rw [hval]
        cases b <;> cases p.val.testBit t <;> rfl
theorem z132 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) (ori : Bool × Bool) (m : Fin R)
    (v : V5 k -> Bool) (i : Fin (3 * k)) (b : Bool)
    (h : z74 hk H ori m v i h' (synOf (H m) (fun idx => v (drvPos hk ori idx))) b = true) :
    b = v (drvPos hk ori i) := by
  obtain ⟨c, _, hrm, hval⟩ := z130 hk H ori m v i h' (le_refl h') _ b h
  set dN := Nat.clog 2 (3 * k)
  set fMask : ℕ -> Bool := fun j =>
    if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && v (drvPos hk ori ⟨j, hj⟩) else false
  have hNle : 3 * k <= 2 ^ dN := Nat.le_pow_clog (by omega) (3 * k)
  have hi_lt : i.val < 2 ^ dN := lt_of_lt_of_le i.isLt hNle
  have hcomp := z105 fMask dN dN i.val (le_refl dN) hi_lt
  have hidx0 : hIdx dN (dN - dN) i.val = 2 ^ dN + i.val := by simp [hIdx]
  rw [hidx0, z30 xor false fMask dN i.val hi_lt] at hcomp
  have hroot : heapUpVal xor false fMask dN 1 =
      dotBool h' c.val (synOf (H m) (fun idx => v (drvPos hk ori idx))).val := by
    rw [z84 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false,
      z99 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false fMask hNle
        (fun j hj => by simp [fMask, show ¬ j < 3 * k by omega])]
    rw [← rowMask_dot_eq, xorFin_eq_range _ fMask (fun j => by simp [fMask, j.isLt])]
    have hfx : ∀ L : List Bool, L.foldr xor false = xorList L := fun L => by
      induction L with
      | nil => rfl
      | cons a t ih => simp [ih]
    exact hfx _
  have hfi : fMask i.val = v (drvPos hk ori i) := by simp [fMask, i.isLt, hrm]
  rw [hfi, hroot] at hcomp
  have hdot : xorFin (fun q : Fin h' => c.val.testBit q.val &&
      (synOf (H m) (fun idx => v (drvPos hk ori idx))).val.testBit q.val) =
      dotBool h' c.val (synOf (H m) (fun idx => v (drvPos hk ori idx))).val := rfl
  rw [hdot] at hval
  rw [← hval]
  generalize z23 fMask dN (2 ^ dN + i.val) = a at hcomp ⊢
  generalize dotBool h' c.val (synOf (H m) (fun idx => v (drvPos hk ori idx))).val = d at hcomp ⊢
  generalize v (drvPos hk ori i) = x at hcomp ⊢
  cases a <;> cases d <;> cases x <;> simp_all
def z11 (hk : 0 < k) (isCol : Bool) (r : ℕ) (key drv : Fin k -> Bool)
    (leaf : ℕ) : ℕ -> (Fin k -> Bool) × Bool
  | 0 => (drv, true)
  | t + 1 =>
    let prev := z11 hk isCol r key drv leaf t
    let idx := r - 1 - t
    let res := revRoundB hk isCol r idx key prev.1 (leaf.testBit (2 * idx)) (leaf.testBit (2 * idx + 1))
    (res.1, prev.2 && res.2)
theorem z112 (hk : 0 < k) (isCol : Bool) (r : ℕ) (key : Fin k -> Bool)
    (leaf : ℕ) :
    ∀ (t : ℕ) (ht : t <= r) (st : Fin k -> Bool),
      let mid := z11 hk isCol r key st leaf t
      let fin := revIterB hk isCol r key leaf (r - t) mid.1
      (fin.1, mid.2 && fin.2) = revIterB hk isCol r key leaf r st
  | 0, _, st => by simp [z11]
  | t + 1, ht, st => by
    have ih := z112 hk isCol r key leaf t (by omega) st
    dsimp only at ih ⊢
    set mid := z11 hk isCol r key st leaf t
    have hr : r - t = (r - (t + 1)) + 1 := by omega
    have hidx : r - 1 - t = r - (t + 1) := by omega
    rw [hr] at ih
    dsimp only [revIterB] at ih
    dsimp only [z11]
    rw [hidx]
    rw [← ih]
    apply Prod.ext
    · rfl
    · dsimp only [mid]; simp [Bool.and_assoc]
theorem z164 (hk : 0 < k) (isCol : Bool) (r : ℕ) (key drv : Fin k -> Bool) (leaf : ℕ) :
    z11 hk isCol r key drv leaf r = revIterB hk isCol r key leaf r drv := by
  have h := z112 hk isCol r key leaf r (le_refl r) drv
  simpa [Nat.sub_self, revIterB] using h
def z1 (hk : 0 < k) (ori : Bool × Bool) (isCol : Bool) (leaf : Fin (z2 k r))
    (key drv : Fin k -> Bool) (t : Fin (r + 1)) (j : Fin k) (slot : Fin 9) : Bool :=
  let rev := branchRev ori isCol
  let dk := Nat.clog 2 k
  let δ := mixStride isCol
  if !rev then
    let init : Fin k -> Bool := fun i => xor (rotB hk (initRot isCol) key i) (drv i)
    let st := fwdIterB hk isCol r key init t.val
    match slot.val with
    | 0 => st j
    | 1 => xor (st j) (rotB hk δ st j)
    | 2 => mixB hk δ st j
    | 3 => !(mixB hk δ st ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) &&
             mixB hk δ st ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩
    | 4 => stepB hk (mixB hk δ st) j
    | 8 => z42 hk r isCol key drv j
    | _ => false
  else
    let st := (z11 hk isCol r key drv leaf.val t.val).1
    let idx := r - 1 - t.val
    let u : Fin k -> Bool := fun i =>
      xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
    let fChi : ℕ -> Bool × Bool := fun p =>
      if hp : p < k then chiMapAt hk u ⟨p, hp⟩ else affId
    let sufS := z33 affComp affId fChi dk (2 ^ dk + j.val)
    let prS := z17 affComp affId fChi dk (2 ^ dk + j.val)
    let cm := chiMapAt hk u j
    let fullSuf := affComp cm sufS
    let w := invChiB hk u
    match slot.val with
    | 0 => st j
    | 1 => u j
    | 2 => fullSuf.1
    | 3 => fullSuf.2
    | 4 => cm.1 && sufS.2
    | 5 => fullSuf.1 && prS.2
    | 6 => xor fullSuf.2 (fullSuf.1 && prS.2)
    | 7 =>
      let pPos := inv3Pos k % k
      let pNeg := (k - pPos) % k
      if j.val = 0 then xor (w ⟨0, hk⟩) (mixPref hk δ w pPos)
      else xor (xor (w ⟨0, hk⟩) (mixPref hk δ w pPos)) (mixPref hk δ w pNeg)
    | 8 => (z108 hk r isCol key leaf.val drv).1 j
    | _ => false
def z41 (hk : 0 < k) (ori : Bool × Bool) (isCol : Bool) (leaf : Fin (z2 k r))
    (key drv : Fin k -> Bool) (t : Fin r) (slot : Fin 9) (u : Fin (2 ^ (Nat.clog 2 k + 1))) : Bool :=
  let dk := Nat.clog 2 k
  let st := (z11 hk isCol r key drv leaf.val t.val).1
  let idx := r - 1 - t.val
  let uW : Fin k -> Bool := fun i =>
    xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
  let fChi : ℕ -> Bool × Bool := fun p =>
    if hp : p < k then chiMapAt hk uW ⟨p, hp⟩ else affId
  match slot.val with
  | 0 => (heapUpVal affComp affId fChi dk u.val).1
  | 1 => (heapUpVal affComp affId fChi dk u.val).2
  | 2 => (z17 affComp affId fChi dk u.val).1
  | 3 => (z17 affComp affId fChi dk u.val).2
  | 4 => (z33 affComp affId fChi dk u.val).1
  | 5 => (z33 affComp affId fChi dk u.val).2
  | 6 => (heapUpVal affComp affId fChi dk (2 * u.val)).1 &&
          (heapUpVal affComp affId fChi dk (2 * u.val + 1)).2
  | 7 => (z17 affComp affId fChi dk (u.val / 2)).1 &&
          (heapUpVal affComp affId fChi dk (u.val - 1)).2
  | 8 => (heapUpVal affComp affId fChi dk (u.val + 1)).1 &&
          (z33 affComp affId fChi dk (u.val / 2)).2
  | _ => false
def z83 (hk : 0 < k) (ori : Bool × Bool) (isCol : Bool) (leaf : Fin (z2 k r))
    (key drv : Fin k -> Bool) (t : Fin r) (rc : Fin 3) (isPref : Bool)
    (u : Fin (2 ^ (Nat.clog 2 k + 1))) : Bool :=
  let dk := Nat.clog 2 k
  let δ := mixStride isCol
  let st := (z11 hk isCol r key drv leaf.val t.val).1
  let idx := r - 1 - t.val
  let uW : Fin k -> Bool := fun i =>
    xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
  let w := invChiB hk uW
  let fMix : ℕ -> Bool :=
    if k % 3 = 0 then fun q => if q < k / 3 then singDiff hk δ w rc.val q else false
    else fun p => if hp : p < k then mixDiffAt hk δ w ⟨p, hp⟩ else false
  if isPref then z17 xor false fMix dk u.val
  else heapUpVal xor false fMix dk u.val
def z22 (hk : 0 < k) (ori : Bool × Bool) (isCol : Bool) (leaf : Fin (z2 k r))
    (key drv : Fin k -> Bool) (t : Fin (r + 1)) (isAcc : Bool) : Bool :=
  if !(branchRev ori isCol) then true
  else if isAcc then (z11 hk isCol r key drv leaf.val t.val).2
  else
    let st := (z11 hk isCol r key drv leaf.val t.val).1
    let idx := r - 1 - t.val
    let uW : Fin k -> Bool := fun i =>
      xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
    let w := invChiB hk uW
    if k % 3 = 0 then wrapOkB hk (mixStride isCol) w else true
def z86 (hk : 0 < k) (ori : Bool × Bool) (isCol : Bool) (leaf : Fin (z2 k r))
    (v : V5 k -> Bool) : Bool :=
  let key : Fin k -> Bool := fun j => v (2, j)
  let drv : Fin k -> Bool := fun j => v (dTrack ori (z8 isCol), j)
  let target := z15 ori isCol
  let res := z13 hk r isCol (branchRev ori isCol) leaf key drv
  !(res.2 && decide (res.1 = fun j => v (target, j)))
def z117 (hk : 0 < k) (ori : Bool × Bool) (isCol : Bool) (leaf : Fin (z2 k r))
    (v : V5 k -> Bool) (j : Fin k) (b : Bool) : Bool :=
  let key : Fin k -> Bool := fun i => v (2, i)
  let drv : Fin k -> Bool := fun i => v (dTrack ori (z8 isCol), i)
  let res := z13 hk r isCol (branchRev ori isCol) leaf key drv
  z86 hk ori isCol leaf v || (res.1 j != b)
def auxVal (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) (v : V5 k -> Bool) :
    AuxAll k r h' R -> Bool
  | Sum.inl b => b
  | Sum.inr (Sum.inl (isCol, t, j, slot)) =>
    let key : Fin k -> Bool := fun i => v (2, i)
    let inp : Fin k -> Bool := fun i => v (if isCol then 1 else 0, i)
    let init : Fin k -> Bool := fun i => xor (rotB hk (initRot isCol) key i) (inp i)
    let st := fwdIterB hk isCol r key init t.val
    let δ := mixStride isCol
    match slot.val with
    | 0 => st j
    | 1 => xor (st j) (rotB hk δ st j)
    | 2 => mixB hk δ st j
    | 3 => !(mixB hk δ st ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) &&
             mixB hk δ st ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩
    | _ => stepB hk (mixB hk δ st) j
  | Sum.inr (Sum.inr (rR, cR, m, mx)) =>
    let ori := (rR, cR)
    let xDrv : Fin (3 * k) -> Bool := fun idx => v (drvPos hk ori idx)
    let sTrue := synOf (H m) xDrv
    let dN := Nat.clog 2 (3 * k)
    match mx with
    | Sum.inl (c, isDown, u, sign) =>
      let fMask : ℕ -> Bool := fun j =>
        if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && xDrv ⟨j, hj⟩ else false
      let val := if isDown then z23 fMask dN u.val else heapUpVal xor false fMask dN u.val
      (sign == val)
    | Sum.inr (Sum.inl (i, t, p, b)) =>
      z74 hk H ori m v i t.val p b
    | Sum.inr (Sum.inr (Sum.inl (s, sx))) =>
      if s ≠ sTrue then true
      else
        match sx with
        | Sum.inl (Sum.inl (i, sign)) => (sign == xDrv i)
        | Sum.inl (Sum.inr (Sum.inl (q, u, sign))) =>
          let fPar : ℕ -> Bool := fun j =>
            if hj : j < 3 * k then H m q ⟨j, hj⟩ && xDrv ⟨j, hj⟩ else false
          (sign == heapUpVal xor false fPar dN u.val)
        | Sum.inl (Sum.inr (Sum.inr _)) => false
        | Sum.inr (Sum.inl (isCol, leaf, lx)) =>
          let key : Fin k -> Bool := fun i => v (2, i)
          let drv : Fin k -> Bool := fun i => v (dTrack ori (z8 isCol), i)
          match lx with
          | Sum.inl (t, j, slot, sign) => (sign == z1 hk ori isCol leaf key drv t j slot)
          | Sum.inr (Sum.inl (t, slot, u, sign)) => (sign == z41 hk ori isCol leaf key drv t slot u)
          | Sum.inr (Sum.inr (Sum.inl (t, rc, isPref, u, sign))) =>
            (sign == z83 hk ori isCol leaf key drv t rc isPref u)
          | Sum.inr (Sum.inr (Sum.inr (Sum.inl (t, isAcc, sign)))) =>
            (sign == z22 hk ori isCol leaf key drv t isAcc)
          | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))) => z86 hk ori isCol leaf v
          | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, b))))) => z117 hk ori isCol leaf v j b
        | Sum.inr (Sum.inr (Sum.inl (isCol, u))) =>
          let fD : ℕ -> Bool := fun l =>
            if hl : l < z2 k r then z86 hk ori isCol ⟨l, hl⟩ v else true
          heapUpVal and true fD (dBOf k r) u.val
        | Sum.inr (Sum.inr (Sum.inr (Sum.inl (isCol, j, b, u)))) =>
          let fK : ℕ -> Bool := fun l =>
            if hl : l < z2 k r then z117 hk ori isCol ⟨l, hl⟩ v j b else true
          heapUpVal and true fK (dBOf k r) u.val
        | Sum.inr (Sum.inr (Sum.inr (Sum.inr (tr, j, b)))) =>
          (v (tr, j) != b)
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl u))) =>
      heapUpVal and true (fun s => decide (s ≠ sTrue.val)) h' u.val
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (tr, j, b, u)))) =>
      heapUpVal and true (fun s => if s = sTrue.val then (v (tr, j) != b) else true) h' u.val
theorem z142 (hk : 0 < k) (u : Fin k -> Bool) (p : Fin k) :
    let dk := Nat.clog 2 k
    let fChi : ℕ -> Bool × Bool := fun q => if hq : q < k then chiMapAt hk u ⟨q, hq⟩ else affId
    let sufS := z33 affComp affId fChi dk (2 ^ dk + p.val)
    let prS := z17 affComp affId fChi dk (2 ^ dk + p.val)
    let fullSuf := affComp (chiMapAt hk u p) sufS
    xor fullSuf.2 (fullSuf.1 && prS.2) = invChiAt hk u p := by
  dsimp only
  set dk := Nat.clog 2 k
  set fChi : ℕ -> Bool × Bool := fun q => if hq : q < k then chiMapAt hk u ⟨q, hq⟩ else affId
  have hkle : k <= 2 ^ dk := Nat.le_pow_clog (by omega) k
  have hp_lt : p.val < 2 ^ dk := lt_of_lt_of_le p.isLt hkle
  have hidx : hIdx dk (dk - dk) p.val = 2 ^ dk + p.val := by simp [hIdx]
  have hpref : z17 affComp affId fChi dk (2 ^ dk + p.val) =
      ((chiList hk u).take p.val).foldl affComp affId := by
    rw [← hidx, z82 affComp affId z106 z56 z111
      fChi dk dk p.val (le_refl dk) hp_lt]
    rw [z118, z56]
    congr 1
    apply List.ext_getElem
    · simp [chiList, Nat.min_eq_left (Nat.le_of_lt p.isLt)]
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range, List.getElem_take, chiList, List.getElem_ofFn]
      have hjk : j < k := by simp at hj1; omega
      simp [fChi, hjk]
  have hsuf : affComp (chiMapAt hk u p) (z33 affComp affId fChi dk (2 ^ dk + p.val)) =
      ((chiList hk u).drop p.val).foldr affComp affId := by
    rw [← hidx, z147 affComp affId z106 z56 z111
      fChi dk dk p.val (le_refl dk) hp_lt]
    have h1 : (p.val + 1) * 2 ^ (dk - dk) = p.val + 1 := by simp
    rw [h1]
    have hdrop : (chiList hk u).drop p.val = chiMapAt hk u p :: (chiList hk u).drop (p.val + 1) := by
      rw [List.drop_eq_getElem_cons (by simp [chiList, p.isLt])]
      simp [chiList]
    rw [hdrop, List.foldr_cons]
    congr 1
    have hpad : ((List.range (2 ^ dk - (p.val + 1))).map (fun t => fChi (p.val + 1 + t))).foldr affComp affId =
        ((List.range (k - (p.val + 1))).map (fun t => fChi (p.val + 1 + t))).foldr affComp affId :=
      z99 affComp affId z106 z56 z111
        (fun t => fChi (p.val + 1 + t)) (by omega) (fun t ht => by
          simp [fChi, show ¬ p.val + 1 + t < k by omega])
    rw [hpad]
    congr 1
    apply List.ext_getElem
    · simp [chiList]
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range, List.getElem_drop, chiList, List.getElem_ofFn]
      have hjk : p.val + 1 + j < k := by simp at hj1; omega
      simp [fChi, hjk]
  rw [hsuf, hpref]
  rfl
theorem z124 (hk : 0 < k) (δ : ℕ) (w : Fin k -> Bool) (p : ℕ) (hp : p < k) :
    let dk := Nat.clog 2 k
    let fMix : ℕ -> Bool := fun q => if hq : q < k then mixDiffAt hk δ w ⟨q, hq⟩ else false
    z17 xor false fMix dk (2 ^ dk + p) = mixPref hk δ w p := by
  dsimp only
  set dk := Nat.clog 2 k
  set fMix : ℕ -> Bool := fun q => if hq : q < k then mixDiffAt hk δ w ⟨q, hq⟩ else false
  have hkle : k <= 2 ^ dk := Nat.le_pow_clog (by omega) k
  have hp_lt : p < 2 ^ dk := lt_of_lt_of_le hp hkle
  have hidx : hIdx dk (dk - dk) p = 2 ^ dk + p := by simp [hIdx]
  rw [← hidx, z82 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false
    fMix dk dk p (le_refl dk) hp_lt]
  have hfold : ∀ L : List Bool, L.foldr xor false = L.foldl xor false := by
    intro L
    have hgen : ∀ acc : Bool, L.foldl xor acc = xor acc (L.foldr xor false) := by
      induction L with
      | nil => intro acc; simp
      | cons a t ih => intro acc; simp only [List.foldl_cons, List.foldr_cons, ih, Bool.xor_assoc]
    rw [hgen false, Bool.false_xor]
  rw [hfold]; dsimp [mixPref]
  congr 1; simp only [Nat.sub_self, pow_zero, Nat.mul_one]
  refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj
  have hjk : j < k := by omega
  simp [fMix, hjk, Nat.mod_eq_of_lt hjk]
theorem z93 (hk : 0 < k) (δ : ℕ) (w : Fin k -> Bool) (rc q : ℕ) (hq : q <= k / 3) :
    let dk := Nat.clog 2 k
    let fMix : ℕ -> Bool := fun j => if j < k / 3 then singDiff hk δ w rc j else false
    (q < k / 3 -> z17 xor false fMix dk (2 ^ dk + q) = singPref hk δ w rc q) /\
    heapUpVal xor false fMix dk 1 = singPref hk δ w rc (k / 3) := by
  dsimp only
  set dk := Nat.clog 2 k
  set fMix : ℕ -> Bool := fun j => if j < k / 3 then singDiff hk δ w rc j else false
  have hkle : k <= 2 ^ dk := Nat.le_pow_clog (by omega) k
  have hmle : k / 3 <= 2 ^ dk := le_trans (Nat.div_le_self k 3) hkle
  have hfoldr_eq : ∀ L : List Bool, L.foldr xor false = xorList L := fun L => by
    induction L with
    | nil => rfl
    | cons a t ih => simp [ih]
  constructor
  · intro hqlt
    have hq2 : q < 2 ^ dk := lt_of_lt_of_le hqlt hmle
    have hidx : hIdx dk (dk - dk) q = 2 ^ dk + q := by simp [hIdx]
    rw [← hidx, z82 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false
      fMix dk dk q (le_refl dk) hq2, hfoldr_eq]
    dsimp [singPref]; simp only [Nat.sub_self, pow_zero, Nat.mul_one]
    congr 1; refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj; simp [fMix, show j < k / 3 by omega]
  · rw [z84 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false,
      z99 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false fMix hmle
        (fun j hj => by simp [fMix, show ¬ j < k / 3 by omega]), hfoldr_eq]
    dsimp [singPref]; congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [List.mem_range] at hj; simp [fMix, hj]
theorem drMode_aux_eq {k r h' R : ℕ} {α : VarAll k r h' R -> Bool}
    {w : DualLit (VarAll k r h' R)} {val : Bool}
    (h1 : lEv α w.1 = !val) (h2 : lEv α w.2 = val) :
    DRMode α false w val := ⟨h1, h2⟩
theorem drMode_aux_dead {k r h' R : ℕ} {α : VarAll k r h' R -> Bool}
    {w : DualLit (VarAll k r h' R)} (val : Bool)
    (h1 : lEv α w.1 = true) (h2 : lEv α w.2 = true) :
    DRMode α true w val := ⟨h1, h2⟩
theorem constClauses_sat (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) (v : V5 k -> Bool) :
    ∀ C ∈ (z92 (k := k) (r := r) (h' := h') (R := R)),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  intro C hC; simp only [z92, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl
  · rw [clauseSat_cl1]; rfl
  · rw [clauseSat_cl1]; rfl
theorem baseClauses_sat (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) (v : V5 k -> Bool)
    (hag : (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) /\
           (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j))) :
    ∀ C ∈ (z64 (k := k) (r := r) (h' := h') (R := R) hk),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  intro C hC; change ClauseSat α C; dsimp only [z64] at hC
  rw [List.mem_flatMap] at hC; rcases hC with ⟨isCol, _, h1⟩
  simp only [List.mem_append] at h1
  rcases h1 with (hinit | hround) | hout
  · rw [List.mem_flatMap] at hinit; rcases hinit with ⟨j, _, hj⟩
    refine ((z59 α _ _ _).mpr ?_) C hj
    simp [α, lEv, vRaw, vBase, vAux, auxVal, fwdIterB, rotB]
  · rw [List.mem_flatMap] at hround; rcases hround with ⟨t, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
    simp only [List.mem_append] at hj
    rcases hj with (((a | b) | c) | d) | e
    · refine ((z59 α _ _ _).mpr ?_) C a
      simp [α, lEv, vBase, vAux, auxVal, rotB]
    · refine ((z59 α _ _ _).mpr ?_) C b
      simp [α, lEv, vBase, vAux, auxVal, mixB, rotB]
    · refine ((tsAnd_sat_iff α _ _ _).mpr ?_) C c
      rw [lEv_negL]; simp [α, lEv, vBase, vAux, auxVal]
    · refine ((z59 α _ _ _).mpr ?_) C d
      simp [α, lEv, vBase, vAux, auxVal, stepB]
    · refine ((z59 α _ _ _).mpr ?_) C e
      have hkl : lEv α (if constBit k (z10 isCol r t.val) j then
          negL (vRaw (2, ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩) true)
          else vRaw (2, ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩) true) =
          xor (rotB hk (z16 isCol t.val) (fun i => v (2, i)) j)
            (constBit k (z10 isCol r t.val) j) := by
        cases constBit k (z10 isCol r t.val) j
        · simp [α, lEv, vRaw, rotB]
        · simp only [↓reduceIte, lEv_negL]; simp [α, lEv, vRaw, rotB]
      rw [hkl]
      simp [α, lEv, vBase, vAux, auxVal, fwdIterB, fwdRoundB, Bool.xor_assoc]
  · rw [List.mem_flatMap] at hout; rcases hout with ⟨j, _, hj⟩
    refine ((tsEq_sat_iff α _ _).mpr ?_) C hj
    cases isCol
    · have h3 := congrFun hag.1 j
      simpa [α, lEv, vBase, vAux, vRaw, auxVal, ← z61, z42] using h3.symm
    · have h4 := congrFun hag.2 j
      simpa [α, lEv, vBase, vAux, vRaw, auxVal, ← z71, z42] using h4.symm
theorem upDownClauses_sat (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (v : V5 k -> Bool) :
    ∀ C ∈ (z40 (k := k) (r := r) (h' := h') (R := R) hk H ori m),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  rcases ori with ⟨rR, cR⟩
  let ori : Bool × Bool := (rR, cR)
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  let dN := Nat.clog 2 (3 * k)
  let xDrv : Fin (3 * k) -> Bool := fun idx => v (drvPos hk ori idx)
  intro C hC; change ClauseSat α C; dsimp only [z40] at hC
  rw [List.mem_flatMap] at hC; rcases hC with ⟨c, _, hc⟩
  let fMask : ℕ -> Bool := fun j =>
    if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && xDrv ⟨j, hj⟩ else false
  have hup_mode : ∀ u : Fin (2 ^ (dN + 1)), 1 <= u.val ->
      DRMode α false (drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c false u)
        (heapUpVal xor false fMask dN u.val) := by
    intro u _; constructor <;> (dsimp [α, ori, lEv, drUpDown, vMat, vAux, auxVal, dN, xDrv, fMask]; cases heapUpVal xor false fMask dN u.val <;> rfl)
  have hdn_mode : ∀ u : Fin (2 ^ (dN + 1)), 1 <= u.val ->
      DRMode α false (drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c true u)
        (z23 fMask dN u.val) := by
    intro u _; constructor <;> (dsimp [α, ori, lEv, drUpDown, vMat, vAux, auxVal, dN, xDrv, fMask]; cases z23 fMask dN u.val <;> rfl)
  simp only [List.mem_append] at hc
  rcases hc with ((hlf | hrt) | hup) | hdn
  · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨j, _, hj⟩
    have hjlt : j.val < 2 ^ dN := j.isLt
    let u : Fin (2 ^ (dN + 1)) := ⟨2 ^ dN + j.val, by change 2 ^ dN + j.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩
    have hu1 : 1 <= u.val := by have := Nat.one_le_pow dN 2 (by omega); dsimp [u]; omega
    have ho := hup_mode u hu1
    rw [show u.val = 2 ^ dN + j.val from rfl, z30 xor false fMask dN j.val j.isLt] at ho
    split_ifs at hj with hjk hrm
    · have hfv : fMask j.val = xDrv ⟨j.val, hjk⟩ := by simp [fMask, hjk, hrm]
      rw [hfv] at ho
      exact drEq_sat (fun _ => by
        constructor <;> (dsimp [α, ori, lEv, vRawDR, xDrv]; cases v (drvPos hk ori ⟨j.val, hjk⟩) <;> rfl)) ho C hj
    · have hfv : fMask j.val = false := by simp [fMask, hjk, hrm]
      rw [hfv] at ho
      exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hj
    · have hfv : fMask j.val = false := by simp [fMask, hjk]
      rw [hfv] at ho
      exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hj
  · have ho := hdn_mode ⟨1, by have := Nat.one_le_pow dN 2 (by omega); rw [pow_succ]; omega⟩ (le_refl 1)
    rw [show (⟨1, _⟩ : Fin (2 ^ (dN + 1))).val = 1 from rfl, z139] at ho
    exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hrt
  · exact z81 dN fMask _ hup_mode C hup
  · exact heapXorCompClauses_sat dN fMask _ _ hup_mode hdn_mode C hdn
theorem walshClauses_sat (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (v : V5 k -> Bool) :
    ∀ C ∈ (z53 (k := k) (r := r) (h' := h') (R := R) hk H ori m),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  rcases ori with ⟨rR, cR⟩
  let ori : Bool × Bool := (rR, cR)
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  intro C hC; change ClauseSat α C; dsimp only [z53] at hC
  rw [List.mem_flatMap] at hC; rcases hC with ⟨i, _, hi⟩
  rw [List.mem_append] at hi
  rcases hi with hinit | hstep
  · rw [List.mem_flatMap] at hinit; rcases hinit with ⟨c, _, hc⟩
    split_ifs at hc with hrm
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> rw [z6] <;>
        (intro h; simp only [α, ori, lEv, drUpDown, vWalsh, vMat, vAux, auxVal, z74, Sum.elim_inr, hrm, Bool.true_and, beq_true] at h ⊢; cases hval : z23 _ _ _ <;> simp_all)
    · simp at hc
  · rw [List.mem_flatMap] at hstep; rcases hstep with ⟨t, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨p, _, hp⟩
    rw [List.mem_flatMap] at hp; rcases hp with ⟨b, _, hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> rw [z6] <;>
      (intro h; simp only [α, ori, lEv, vWalsh, vMat, vAux, auxVal, z74, Sum.elim_inr, t.isLt, ↓reduceDIte, beq_true, Bool.or_eq_true] at h ⊢)
    · exact Or.inl h
    · exact Or.inr h
theorem z159 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) (v : V5 k -> Bool) :
    ∀ C ∈ (z12 (k := k) (r := r) (h' := h') (R := R) hk H ori m s),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  rcases ori with ⟨rR, cR⟩
  let ori : Bool × Bool := (rR, cR)
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  let xDrv : Fin (3 * k) -> Bool := fun idx => v (drvPos hk ori idx)
  let sTrue := synOf (H m) xDrv
  let dN := Nat.clog 2 (3 * k)
  let dead : Bool := decide (s ≠ sTrue)
  have hxMode : ∀ i : Fin (3 * k),
      DRMode α dead (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) (xDrv i) := by
    intro i; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte]; cases v (drvPos hk (rR, cR) i) <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  intro C hC; change ClauseSat α C; dsimp only [z12] at hC
  rw [List.mem_append] at hC
  rcases hC with hx | hpar
  · rw [List.mem_flatMap] at hx; rcases hx with ⟨i, _, hi⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    by_cases hs : s = sTrue
    · rcases hi with rfl | rfl | rfl | rfl | rfl
      · rw [z6]; intro h
        dsimp [α, ori, lEv, vRaw, drXDual, vSyn, vMat, vAux, auxVal] at h ⊢
        simp [hs, sTrue, xDrv, ori, beq_iff_eq] at h ⊢; exact h
      · rw [z6]; intro h
        dsimp [α, ori, lEv, vRaw, drXDual, vSyn, vMat, vAux, auxVal] at h ⊢
        simp [hs, sTrue, xDrv, ori, beq_iff_eq] at h ⊢; exact h
      · rw [z6]; intro h
        dsimp [α, ori, lEv, vWalsh, drXDual, vSyn, vMat, vAux, auxVal] at h ⊢
        have hw : z74 hk H ori m v i h' sTrue false = true := by
          simpa [hs, beq_true] using h
        have hb := z132 hk H ori m v i false hw
        simp [hs, sTrue, xDrv, ori, xDrv, hb.symm]
      · rw [z6]; intro h
        dsimp [α, ori, lEv, vWalsh, drXDual, vSyn, vMat, vAux, auxVal] at h ⊢
        have hw : z74 hk H ori m v i h' sTrue true = true := by
          simpa [hs, beq_true] using h
        have hb := z132 hk H ori m v i true hw
        simp [hs, sTrue, xDrv, ori, xDrv, hb.symm]
      · rw [z45]; intro h1 h2
        dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal] at h1 h2
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true] at h1 h2
        cases hxi : xDrv i <;> simp_all
    · rcases hi with rfl | rfl | rfl | rfl | rfl
      · rw [z6]; intro _; dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
      · rw [z6]; intro _; dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
      · rw [z6]; intro _; dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
      · rw [z6]; intro _; dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
      · rw [z45]; intro _ _; dsimp [α, ori, lEv, vExcl, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
  · rw [List.mem_flatMap] at hpar; rcases hpar with ⟨q, _, hq⟩
    let fPar : ℕ -> Bool := fun j => if hj : j < 3 * k then H m q ⟨j, hj⟩ && xDrv ⟨j, hj⟩ else false
    have hparMode : ∀ u : Fin (2 ^ (dN + 1)), 1 <= u.val ->
        DRMode α dead (drPar (k := k) (r := r) (h' := h') (R := R) ori m s q u)
          (heapUpVal xor false fPar dN u.val) := by
      intro u _; by_cases hs : s = sTrue
      · have hd : dead = false := by simp [dead, hs]
        rw [hd]; constructor <;> (dsimp [α, ori, lEv, drPar, vSyn, vMat, vAux, auxVal, sTrue, xDrv, fPar, dN]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte]; cases heapUpVal xor false fPar dN u.val <;> rfl)
      · have hd : dead = true := by simp [dead, hs]
        rw [hd]; constructor <;> (dsimp [α, ori, lEv, drPar, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
    simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with (hlf | hup) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨j, _, hj⟩
      have hjlt : j.val < 2 ^ dN := j.isLt
      let u : Fin (2 ^ (dN + 1)) := ⟨2 ^ dN + j.val, by change 2 ^ dN + j.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩
      have hu1 : 1 <= u.val := by have := Nat.one_le_pow dN 2 (by omega); dsimp [u]; omega
      have ho := hparMode u hu1
      rw [show u.val = 2 ^ dN + j.val from rfl, z30 xor false fPar dN j.val j.isLt] at ho
      split_ifs at hj with hjk hmq
      · have hfv : fPar j.val = xDrv ⟨j.val, hjk⟩ := by simp [fPar, hjk, hmq]
        rw [hfv] at ho
        exact drEq_sat (fun hd => by simpa [DRMode, hd] using hxMode ⟨j.val, hjk⟩) ho C hj
      · have hfv : fPar j.val = false := by simp [fPar, hjk, hmq]
        rw [hfv] at ho
        exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hj
      · have hfv : fPar j.val = false := by simp [fPar, hjk]
        rw [hfv] at ho
        exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hj
    · exact z81 dN fPar _ hparMode C hup
    · rw [z6]; intro h
      by_cases hs : s = sTrue
      · exfalso
        have hNle : 3 * k <= 2 ^ dN := Nat.le_pow_clog (by omega) (3 * k)
        have hroot : heapUpVal xor false fPar dN 1 = sTrue.val.testBit q.val := by
          rw [z84 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false,
            z99 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false fPar hNle
              (fun j hj => by simp [fPar, show ¬ j < 3 * k by omega])]
          rw [synOf_testBit, xorFin_eq_range _ fPar (fun j => by simp [fPar, j.isLt])]
          have hfx : ∀ L : List Bool, L.foldr xor false = xorList L := fun L => by
            induction L with | nil => rfl | cons a t ih => simp [ih]
          exact hfx _
        have hd : dead = false := by simp [dead, hs]
        have h1 := hparMode ⟨1, by have := Nat.one_le_pow dN 2 (by omega); rw [pow_succ]; omega⟩ (le_refl 1)
        rw [hd] at h1
        rw [show (⟨1, _⟩ : Fin (2 ^ (dN + 1))).val = 1 from rfl, hroot, ← hs] at h1
        dsimp only [ori] at h1
        cases hb : s.val.testBit q.val
        · simp [drFlip, hb, h1.2] at h
        · simp [drFlip, hb, h1.1] at h
      · dsimp [α, ori, lEv, vExcl, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
theorem leafCircuitClauses_sat (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) (v : V5 k -> Bool) :
    ∀ C ∈ (z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  rcases ori with ⟨rR, cR⟩
  let ori : Bool × Bool := (rR, cR)
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  let xDrv : Fin (3 * k) -> Bool := fun idx => v (drvPos hk ori idx)
  let sTrue := synOf (H m) xDrv
  let key : Fin k -> Bool := fun j => v (2, j)
  let drv : Fin k -> Bool := fun j => v (dTrack ori (z8 isCol), j)
  let dk := Nat.clog 2 k
  let dead : Bool := decide (s ≠ sTrue)
  have hkeyMode : ∀ j : Fin k,
      DRMode α dead (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s (drvIdx 0 j)) (key j) := by
    intro j; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal, sTrue, xDrv, key]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, z49, dTrack]; cases v (2, j) <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  have hdrvMode : ∀ j : Fin k,
      DRMode α dead (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s (drvIdx (z8 isCol) j)) (drv j) := by
    intro j; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal, sTrue, xDrv, drv]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, z49]; cases v (dTrack ori (z8 isCol), j) <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drXDual, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  have hWMode : ∀ t j sl,
      DRMode α dead (z91 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf t j sl)
        (z1 hk ori isCol leaf key drv t j sl) := by
    intro t j sl; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, z91, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv, key, drv]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte]; cases z1 hk ori isCol leaf key drv t j sl <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, z91, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  have hCMode : ∀ t sl u,
      DRMode α dead (drLeafChi (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf t sl u)
        (z41 hk ori isCol leaf key drv t sl u) := by
    intro t sl u; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drLeafChi, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv, key, drv]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte]; cases z41 hk ori isCol leaf key drv t sl u <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drLeafChi, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  have hMMode : ∀ t rc isPr u,
      DRMode α dead (drLeafMix (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf t rc isPr u)
        (z83 hk ori isCol leaf key drv t rc isPr u) := by
    intro t rc isPr u; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drLeafMix, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv, key, drv]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte]; cases z83 hk ori isCol leaf key drv t rc isPr u <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, drLeafMix, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  have hPMode : ∀ t isAcc,
      DRMode α dead (z137 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf t isAcc)
        (z22 hk ori isCol leaf key drv t isAcc) := by
    intro t isAcc; by_cases hs : s = sTrue
    · have hd : dead = false := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, z137, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv, key, drv]; simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte]; cases z22 hk ori isCol leaf key drv t isAcc <;> rfl)
    · have hd : dead = true := by simp [dead, hs]
      rw [hd]; constructor <;> (dsimp [α, ori, lEv, z137, vLeaf, vSyn, vMat, vAux, auxVal, sTrue, xDrv]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  intro C hC; change ClauseSat α C; dsimp only [z9] at hC
  simp only [List.mem_append] at hC
  rcases hC with (hcore | hdead) | hkill
  · by_cases hrev : (!branchRev ori isCol) = true
    on_goal 1 =>
      have hrev' : (!branchRev (rR, cR) isCol) = true := hrev
      simp only [hrev', ↓reduceIte] at hcore
    on_goal 2 =>
      have hrevF : (!branchRev ori isCol) = false := Bool.eq_false_iff.mpr hrev
      have hrevF' : (!branchRev (rR, cR) isCol) = false := hrevF
      simp only [hrevF', Bool.false_eq_true, ↓reduceIte] at hcore
    ·
      simp only [List.mem_append] at hcore
      rcases hcore with ((hinit | hround) | hfin) | hwrap
      · rw [List.mem_flatMap] at hinit; rcases hinit with ⟨j, _, hj⟩
        have ho := hWMode ⟨0, Nat.zero_lt_succ r⟩ j 0
        have hval : z1 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ j 0 =
            xor (key ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩) (drv j) := by
          simp [z1, hrev, fwdIterB, rotB]
        rw [hval] at ho
        exact drXor_sat (fun hd => by simpa [DRMode, hd] using hkeyMode _)
          (fun hd => by simpa [DRMode, hd] using hdrvMode j) ho C hj
      · rw [List.mem_flatMap] at hround; rcases hround with ⟨t, _, ht⟩
        rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
        simp only [List.mem_append] at hj
        let t0 : Fin (r + 1) := ⟨t.val, by omega⟩
        let t1 : Fin (r + 1) := ⟨t.val + 1, by omega⟩
        rcases hj with (((a | b) | c) | d) | e
        · have ho := hWMode t0 j 1
          have hv : z1 hk ori isCol leaf key drv t0 j 1 =
              xor (z1 hk ori isCol leaf key drv t0 j 0)
                (z1 hk ori isCol leaf key drv t0 ⟨(j.val + k - mixStride isCol % k) % k, Nat.mod_lt _ hk⟩ 0) := by
            simp [z1, hrev, rotB]
          rw [hv] at ho
          exact drXor_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 j 0)
            (fun hd => by simpa [DRMode, hd] using hWMode t0 _ 0) ho C a
        · have ho := hWMode t0 j 2
          have hv : z1 hk ori isCol leaf key drv t0 j 2 =
              xor (z1 hk ori isCol leaf key drv t0 j 1)
                (z1 hk ori isCol leaf key drv t0 ⟨(j.val + k - (k - mixStride isCol % k) % k) % k, Nat.mod_lt _ hk⟩ 0) := by
            simp [z1, hrev, mixB, rotB]
          rw [hv] at ho
          exact drXor_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 j 1)
            (fun hd => by simpa [DRMode, hd] using hWMode t0 _ 0) ho C b
        · have ho := hWMode t0 j 3
          have hv : z1 hk ori isCol leaf key drv t0 j 3 =
              (!(z1 hk ori isCol leaf key drv t0 ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ 2) &&
               z1 hk ori isCol leaf key drv t0 ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ 2) := by
            simp [z1, hrev]
          rw [hv] at ho
          exact drAnd_sat (fun hd => by simpa [DRMode, hd] using z154 (hWMode t0 _ 2))
            (fun hd => by simpa [DRMode, hd] using hWMode t0 _ 2) ho C c
        · have ho := hWMode t0 j 4
          have hv : z1 hk ori isCol leaf key drv t0 j 4 =
              xor (z1 hk ori isCol leaf key drv t0 j 2)
                (z1 hk ori isCol leaf key drv t0 j 3) := by
            simp [z1, hrev, stepB]
          rw [hv] at ho
          exact drXor_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 j 2)
            (fun hd => by simpa [DRMode, hd] using hWMode t0 j 3) ho C d
        · have ho := hWMode t1 j 0
          have hv : z1 hk ori isCol leaf key drv t1 j 0 =
              xor (z1 hk ori isCol leaf key drv t0 j 4)
                (xor (constBit k (z10 isCol r t.val) j)
                  (key ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩)) := by
            simp only [z1, hrev, ↓reduceIte, t0, t1, fwdIterB, fwdRoundB, rotB]
            cases stepB hk (mixB hk (mixStride isCol) _) j <;>
              cases key ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩ <;>
              cases constBit k (z10 isCol r t.val) j <;> rfl
          rw [hv] at ho
          exact drXor_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 j 4)
            (fun hd => by simpa [DRMode, hd] using z100 _ (hkeyMode _)) ho C e
      · rw [List.mem_flatMap] at hfin; rcases hfin with ⟨j, _, hj⟩
        have ho := hWMode ⟨0, Nat.zero_lt_succ r⟩ j 8
        have hv : z1 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ j 8 =
            z1 hk ori isCol leaf key drv ⟨r, Nat.lt_succ_self r⟩ j 0 := by
          simp [z1, hrev, z42]
        rw [hv] at ho
        exact drEq_sat (fun hd => by simpa [DRMode, hd] using hWMode ⟨r, Nat.lt_succ_self r⟩ j 0) ho C hj
      · have ho := hPMode ⟨r, Nat.lt_succ_self r⟩ true
        have hv : z22 hk ori isCol leaf key drv ⟨r, Nat.lt_succ_self r⟩ true = true := by
          simp [z22, hrev]
        rw [hv] at ho
        exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hwrap
    ·
      have hrevT : branchRev ori isCol = true := by cases hb : branchRev ori isCol <;> simp_all
      simp only [List.mem_append] at hcore
      rcases hcore with ((hinit | hwinit) | hround) | hfin
      · rw [List.mem_flatMap] at hinit; rcases hinit with ⟨j, _, hj⟩
        have ho := hWMode ⟨0, Nat.zero_lt_succ r⟩ j 0
        have hv : z1 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ j 0 = drv j := by
          simp [z1, hrev, z11]
        rw [hv] at ho
        exact drEq_sat (fun hd => by simpa [DRMode, hd] using hdrvMode j) ho C hj
      · have ho := hPMode ⟨0, Nat.zero_lt_succ r⟩ true
        have hv : z22 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ true = true := by
          simp [z22, hrev, z11]
        rw [hv] at ho
        exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hwinit
      · rw [List.mem_flatMap] at hround; rcases hround with ⟨t, _, ht⟩
        let t0 : Fin (r + 1) := ⟨t.val, by omega⟩
        let t1 : Fin (r + 1) := ⟨t.val + 1, by omega⟩
        let idx := r - 1 - t.val
        let δ := mixStride isCol
        let st := (z11 hk isCol r key drv leaf.val t.val).1
        let uW : Fin k -> Bool := fun i =>
          xor (xor (st i) (rotB hk (z16 isCol idx) key i)) (constBit k (z10 isCol r idx) i)
        let fChi : ℕ -> Bool × Bool := fun p => if hp : p < k then chiMapAt hk uW ⟨p, hp⟩ else affId
        let w := invChiB hk uW
        have hW6 : ∀ i : Fin k, z1 hk ori isCol leaf key drv t0 (z19 k hk i) 6 = w i := by
          intro i
          dsimp [z1, t0, w, invChiB]
          simp only [hrev, ↓reduceIte]
          exact z142 hk uW (z19 k hk i)
        simp only [List.mem_append] at ht
        rcases ht with ((((((huCl | hcl) | hcr) | ha1) | ha2) | ha3) | hco) | hmix
        · rw [List.mem_flatMap] at huCl; rcases huCl with ⟨j, _, hj⟩
          have ho := hWMode t0 j 1
          have hv : z1 hk ori isCol leaf key drv t0 j 1 =
              xor (z1 hk ori isCol leaf key drv t0 j 0)
                (xor (constBit k (z10 isCol r idx) j)
                  (key ⟨(j.val + k - z16 isCol idx % k) % k, Nat.mod_lt _ hk⟩)) := by
            simp only [z1, hrevF, Bool.false_eq_true, ↓reduceIte, t0, idx, rotB]
            cases (z11 hk isCol r key drv leaf.val t.val).1 j <;>
              cases key ⟨(j.val + k - z16 isCol idx % k) % k, Nat.mod_lt _ hk⟩ <;>
              cases constBit k (z10 isCol r idx) j <;> rfl
          rw [hv] at ho
          exact drXor_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 j 0)
            (fun hd => by simpa [DRMode, hd] using z100 _ (hkeyMode _)) ho C hj
        · rw [List.mem_flatMap] at hcl; rcases hcl with ⟨p, _, hp⟩
          let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by have hp' := p.isLt; dsimp only [dk] at *; rw [pow_succ]; omega⟩
          split_ifs at hp with hpk
          · rw [List.mem_append] at hp
            rcases hp with h1 | h2
            · have ho := hCMode t 0 u
              have hv : z41 hk ori isCol leaf key drv t 0 u =
                  !(z1 hk ori isCol leaf key drv t0 ⟨((z21 k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩ 1) := by
                dsimp [z41, z1, u, t0]; simp only [hrev, ↓reduceIte]
                rw [z30 affComp affId _ dk p.val p.isLt]; simp [hpk, chiMapAt]
              rw [hv] at ho
              exact drEq_sat (fun hd => by simpa [DRMode, hd] using z154 (hWMode t0 _ 1)) ho C h1
            · have ho := hCMode t 1 u
              have hv : z41 hk ori isCol leaf key drv t 1 u =
                  z1 hk ori isCol leaf key drv t0 (z21 k p.val hk) 1 := by
                dsimp [z41, z1, u, t0]; simp only [hrev, ↓reduceIte]
                rw [z30 affComp affId _ dk p.val p.isLt]; simp [hpk, chiMapAt]
              rw [hv] at ho
              exact drEq_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 _ 1) ho C h2
          · rw [List.mem_append] at hp
            rcases hp with h1 | h2
            · have ho := hCMode t 0 u
              have hv : z41 hk ori isCol leaf key drv t 0 u = true := by
                dsimp [z41, u]; rw [z30 affComp affId _ dk p.val p.isLt]; simp [hpk, affId]
              rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C h1
            · have ho := hCMode t 1 u
              have hv : z41 hk ori isCol leaf key drv t 1 u = false := by
                dsimp [z41, u]; rw [z30 affComp affId _ dk p.val p.isLt]; simp [hpk, affId]
              rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C h2
        · let rK : Fin (2 ^ (dk + 1)) := ⟨1, by have := Nat.one_le_pow dk 2 (by omega); rw [pow_succ]; omega⟩
          rcases hcr with ((a | b) | c) | d
          · have ho := hCMode t 2 rK
            have hv : z41 hk ori isCol leaf key drv t 2 rK = true := by
              dsimp [z41, rK]; rw [z60]; rfl
            rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C a
          · have ho := hCMode t 3 rK
            have hv : z41 hk ori isCol leaf key drv t 3 rK = false := by
              dsimp [z41, rK]; rw [z60]; rfl
            rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C b
          · have ho := hCMode t 4 rK
            have hv : z41 hk ori isCol leaf key drv t 4 rK = true := by
              dsimp [z41, rK]; rw [z126]; rfl
            rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C c
          · have ho := hCMode t 5 rK
            have hv : z41 hk ori isCol leaf key drv t 5 rK = false := by
              dsimp [z41, rK]; rw [z126]; rfl
            rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C d
        · exact heapAffUpClauses_sat dk fChi _ _
            (fun u _ => ⟨hCMode t 0 u, hCMode t 1 u⟩)
            (fun u _ _ => hCMode t 6 u) C ha1
        · exact heapAffPrefClauses_sat dk fChi _ _ _
            (fun u _ => ⟨hCMode t 0 u, hCMode t 1 u⟩)
            (fun u _ => ⟨hCMode t 2 u, hCMode t 3 u⟩)
            (fun u hu1 hu2 => by
              have h := hCMode t 7 ⟨2 * u.val + 1, by have hpow := pow_succ 2 (Nat.clog 2 k); dsimp only [dk] at hu2; omega⟩
              have hd1 : (2 * u.val + 1) / 2 = u.val := by omega
              have hd2 : (2 * u.val + 1) - 1 = 2 * u.val := by omega
              simpa [z41, hd1, hd2, fChi, uW, st, idx, ori] using h) C ha2
        · exact heapAffSufClauses_sat dk fChi _ _ _
            (fun u _ => ⟨hCMode t 0 u, hCMode t 1 u⟩)
            (fun u _ => ⟨hCMode t 4 u, hCMode t 5 u⟩)
            (fun u hu1 hu2 => by
              have h := hCMode t 8 ⟨2 * u.val, by have hpow := pow_succ 2 (Nat.clog 2 k); dsimp only [dk] at hu2; omega⟩
              have hd1 : (2 * u.val) / 2 = u.val := by omega
              simpa [z41, hd1, fChi, uW, st, idx, ori] using h) C ha3
        · rw [List.mem_flatMap] at hco; rcases hco with ⟨p, _, hp⟩
          have hp_pow : p.val < 2 ^ dk := lt_of_lt_of_le p.isLt (Nat.le_pow_clog (by omega) k)
          let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by have hp' := p.isLt; dsimp only [dk] at *; rw [pow_succ]; omega⟩
          simp only [List.mem_append] at hp
          rcases hp with (a | b) | c
          · exact z145 (dead := dead)
              (vx := chiMapAt hk uW p) (vy := z33 affComp affId fChi dk (2 ^ dk + p.val))
              (fun hd => by
                have h := z154 (hWMode t0 ⟨((z21 k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩ 1)
                rw [hd] at h; simpa [DRMode, z1, hrevF, chiMapAt, uW, st, idx] using h)
              (fun hd => by
                have h := hWMode t0 (z21 k p.val hk) 1
                rw [hd] at h; simpa [DRMode, z1, hrevF, chiMapAt, uW, st, idx] using h)
              (fun hd => by have h := hCMode t 4 u; rw [hd] at h; simpa [DRMode, z41, u, fChi, uW, st, idx] using h)
              (fun hd => by have h := hCMode t 5 u; rw [hd] at h; simpa [DRMode, z41, u, fChi, uW, st, idx] using h)
              (by simpa [z1, hrevF, u, t0, fChi, uW, st, idx] using hWMode t0 p 4)
              (by simpa [z1, hrevF, u, t0, fChi, uW, st, idx] using hWMode t0 p 2)
              (by simpa [z1, hrevF, u, t0, fChi, uW, st, idx] using hWMode t0 p 3) C a
          · exact drAnd_sat (dead := dead)
              (fun hd => by have h := hWMode t0 p 2; rw [hd] at h; simpa [DRMode, z1, hrevF, u, t0, fChi, uW, st, idx] using h)
              (fun hd => by have h := hCMode t 3 u; rw [hd] at h; simpa [DRMode, z41, u, fChi, uW, st, idx] using h)
              (by simpa [z1, hrevF, u, t0, fChi, uW, st, idx] using hWMode t0 p 5) C b
          · have ho := hWMode t0 p 6
            have hv : z1 hk ori isCol leaf key drv t0 p 6 =
                xor (z1 hk ori isCol leaf key drv t0 p 3)
                  (z1 hk ori isCol leaf key drv t0 p 5) := by
              simp [z1, hrevF, t0]
            rw [hv] at ho
            exact drXor_sat (dead := dead)
              (fun hd => by simpa [DRMode, hd, ori] using hWMode t0 p 3)
              (fun hd => by simpa [DRMode, hd, ori] using hWMode t0 p 5)
              (by simpa [ori] using ho) C c
        · split_ifs at hmix with h3 hk5
          ·
            simp only [List.mem_append] at hmix
            rcases hmix with (htr | hout) | hsw
            · rw [List.mem_flatMap] at htr; rcases htr with ⟨rc, _, hrc⟩
              let fMix : ℕ -> Bool := fun q => if q < k / 3 then singDiff hk δ w rc.val q else false
              have hupM : ∀ u : Fin (2 ^ (dk + 1)), 1 <= u.val ->
                  DRMode α dead (drLeafMix ori m s isCol leaf t rc false u) (heapUpVal xor false fMix dk u.val) :=
                fun u _ => by simpa [z83, h3, fMix, w, uW, st, idx, δ, dk] using hMMode t rc false u
              have hprM : ∀ u : Fin (2 ^ (dk + 1)), 1 <= u.val ->
                  DRMode α dead (drLeafMix ori m s isCol leaf t rc true u) (z17 xor false fMix dk u.val) :=
                fun u _ => by simpa [z83, h3, fMix, w, uW, st, idx, δ, dk] using hMMode t rc true u
              simp only [List.mem_append] at hrc
              rcases hrc with ((hlf | hrt) | hup) | hpr
              · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨q, _, hq⟩
                let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + q.val, by have hq' := q.isLt; dsimp only [dk] at *; rw [pow_succ]; omega⟩
                have hu1 : 1 <= u.val := by have := Nat.one_le_pow dk 2 (by omega); dsimp [u]; omega
                have ho := hupM u hu1
                rw [show u.val = 2 ^ dk + q.val from rfl, z30 xor false fMix dk q.val q.isLt] at ho
                split_ifs at hq with hqm
                · have hfv : fMix q.val = xor (w (sIdx hk δ (3 * q.val + rc.val + 1)))
                      (w (sIdx hk δ (3 * q.val + rc.val + 2))) := by simp [fMix, hqm, singDiff]
                  rw [hfv] at ho
                  exact drXor_sat
                    (fun hd => by simpa [DRMode, hd, hW6] using hWMode t0 (z19 k hk _) 6)
                    (fun hd => by simpa [DRMode, hd, hW6] using hWMode t0 (z19 k hk _) 6) ho C hq
                · have hfv : fMix q.val = false := by simp [fMix, hqm]
                  rw [hfv] at ho
                  exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hq
              · have ho := hprM ⟨1, by have := Nat.one_le_pow dk 2 (by omega); rw [pow_succ]; omega⟩ (le_refl 1)
                rw [show (⟨1, _⟩ : Fin (2 ^ (dk + 1))).val = 1 from rfl, z60] at ho
                exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hrt
              · exact z81 dk fMix _ hupM C hup
              · exact z129 dk fMix _ _ hupM hprM C hpr
            · rw [List.mem_flatMap] at hout; rcases hout with ⟨i, _, hi⟩
              let pv := (sInv hk δ i).val
              let rc : Fin 3 := ⟨pv % 3, Nat.mod_lt _ (by omega)⟩
              let qv := pv / 3
              have hqlt : qv < k / 3 := by have := (sInv hk δ i).isLt; omega
              have hq_pow : qv < 2 ^ dk := lt_of_lt_of_le (by have := (sInv hk δ i).isLt; omega)
                (Nat.le_pow_clog (by omega) k)
              let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + qv, by rw [pow_succ]; omega⟩
              have hpr_eq := (z93 hk δ w rc.val qv (Nat.le_of_lt hqlt)).1 hqlt
              have ho := hWMode t1 i 0
              have hst1 : z1 hk ori isCol leaf key drv t1 i 0 =
                  z4 hk δ w (leaf.val.testBit (2 * idx)) (leaf.val.testBit (2 * idx + 1)) pv := by
                dsimp [z1, t1, z11, revRoundB, z87]
                simp only [hrev, h3, ↓reduceIte]; rfl
              rw [hst1] at ho
              split_ifs at hi with hrc0 hrc1
              · have hv : z4 hk δ w (leaf.val.testBit (2 * idx)) (leaf.val.testBit (2 * idx + 1)) pv =
                    xor (leaf.val.testBit (2 * idx)) (singPref hk δ w rc.val qv) := by
                  dsimp [z4]; simp [pv, δ, rc, qv, hrc0]
                rw [hv, ← hpr_eq] at ho
                exact drEq_sat (fun hd => by
                  have h := z100 (leaf.val.testBit (2 * idx)) (hMMode t rc true u)
                  simpa [DRMode, hd, z83, h3, w, uW, st, idx, δ, dk, u] using h) ho C hi
              · have hv : z4 hk δ w (leaf.val.testBit (2 * idx)) (leaf.val.testBit (2 * idx + 1)) pv =
                    xor (leaf.val.testBit (2 * idx + 1)) (singPref hk δ w rc.val qv) := by
                  dsimp [z4]; simp [pv, δ, rc, qv, hrc0, hrc1]
                rw [hv, ← hpr_eq] at ho
                exact drEq_sat (fun hd => by
                  have h := z100 (leaf.val.testBit (2 * idx + 1)) (hMMode t rc true u)
                  simpa [DRMode, hd, z83, h3, w, uW, st, idx, δ, dk, u] using h) ho C hi
              · have hv : z4 hk δ w (leaf.val.testBit (2 * idx)) (leaf.val.testBit (2 * idx + 1)) pv =
                    xor (xor (xor (leaf.val.testBit (2 * idx)) (leaf.val.testBit (2 * idx + 1))) (w (sIdx hk δ 1)))
                      (singPref hk δ w rc.val qv) := by
                  dsimp [z4]
                  have hne0 : pv % 3 ≠ 0 := hrc0
                  have hne1 : pv % 3 ≠ 1 := hrc1
                  simp only [hne0, hne1, ↓reduceIte, rc, qv]
                  cases w (sIdx hk δ 1) <;> cases leaf.val.testBit (2 * idx) <;>
                    cases leaf.val.testBit (2 * idx + 1) <;> cases singPref hk δ w (pv % 3) (pv / 3) <;> rfl
                rw [hv, ← hpr_eq] at ho
                exact drXor_sat
                  (fun hd => by
                    have h := z100 (xor (leaf.val.testBit (2 * idx)) (leaf.val.testBit (2 * idx + 1)))
                      (hWMode t0 (z19 k hk (sIdx hk δ 1)) 6)
                    simpa [DRMode, hd, hW6] using h)
                  (fun hd => by simpa [DRMode, hd, z83, h3, w, uW, st, idx, δ, dk, u] using hMMode t rc true u)
                  ho C hi
            · rcases hsw with h1 | h2
              · have hs0 := (z93 hk δ w 0 0 (Nat.zero_le _)).2
                have hs1 := (z93 hk δ w 1 0 (Nat.zero_le _)).2
                have ho := hPMode t0 false
                have hv : z22 hk ori isCol leaf key drv t0 false =
                    (!(singPref hk δ w 0 (k / 3)) && !(singPref hk δ w 1 (k / 3))) := by
                  simp [z22, hrevF, Bool.false_eq_true, h3, wrapOkB, w, uW, st, idx, δ, t0]
                rw [hv, ← hs0, ← hs1] at ho
                exact drAnd_sat
                  (fun hd => by simpa [DRMode, hd, z83, h3, w, uW, st, idx, δ, dk] using z154 (hMMode t 0 false _))
                  (fun hd => by simpa [DRMode, hd, z83, h3, w, uW, st, idx, δ, dk] using z154 (hMMode t 1 false _))
                  ho C h1
              · have ho := hPMode t1 true
                have hv : z22 hk ori isCol leaf key drv t1 true =
                    (z22 hk ori isCol leaf key drv t0 true &&
                     z22 hk ori isCol leaf key drv t0 false) := by
                  simp [z22, hrev, h3, z11, revRoundB, t0, t1, idx, δ]
                rw [hv] at ho
                exact drAnd_sat
                  (fun hd => by simpa [DRMode, hd] using hPMode t0 true)
                  (fun hd => by simpa [DRMode, hd] using hPMode t0 false) ho C h2
          ·
            simp only [List.mem_append] at hmix
            rcases hmix with hcp | (h1 | h2)
            · rw [List.mem_flatMap] at hcp; rcases hcp with ⟨i, _, hi⟩
              have ho := hWMode t1 i 0
              have hv : z1 hk ori isCol leaf key drv t1 i 0 = w i := by
                dsimp [z1, t1, z11, revRoundB, invMixB]
                simp [hrev, h3, hk5, w, uW, st, idx]
              rw [hv, ← hW6 i] at ho
              exact drEq_sat (fun hd => by simpa [DRMode, hd] using hWMode t0 (z19 k hk i) 6) ho C hi
            · have ho := hPMode t0 false
              have hv : z22 hk ori isCol leaf key drv t0 false = true := by
                simp [z22, hrev, h3]
              rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C h1
            · have ho := hPMode t1 true
              have hv : z22 hk ori isCol leaf key drv t1 true =
                  (z22 hk ori isCol leaf key drv t0 true &&
                   z22 hk ori isCol leaf key drv t0 false) := by
                simp [z22, hrev, h3, z11, revRoundB, t0, t1, idx]
              rw [hv] at ho
              exact drAnd_sat
                (fun hd => by simpa [DRMode, hd] using hPMode t0 true)
                (fun hd => by simpa [DRMode, hd] using hPMode t0 false) ho C h2
          ·
            let fMix : ℕ -> Bool := fun p => if hp : p < k then mixDiffAt hk δ w ⟨p, hp⟩ else false
            have hupM : ∀ u : Fin (2 ^ (dk + 1)), 1 <= u.val ->
                DRMode α dead (drLeafMix ori m s isCol leaf t 0 false u) (heapUpVal xor false fMix dk u.val) :=
              fun u _ => by simpa [z83, h3, fMix, w, uW, st, idx, δ, dk] using hMMode t 0 false u
            have hprM : ∀ u : Fin (2 ^ (dk + 1)), 1 <= u.val ->
                DRMode α dead (drLeafMix ori m s isCol leaf t 0 true u) (z17 xor false fMix dk u.val) :=
              fun u _ => by simpa [z83, h3, fMix, w, uW, st, idx, δ, dk] using hMMode t 0 true u
            simp only [List.mem_append] at hmix
            rcases hmix with (((((hlf | hrt) | hup) | hpr) | hx0) | hout) | hsw
            · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨p, _, hp⟩
              let u : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by have hp' := p.isLt; dsimp only [dk] at *; rw [pow_succ]; omega⟩
              have hu1 : 1 <= u.val := by have := Nat.one_le_pow dk 2 (by omega); dsimp [u]; omega
              have ho := hupM u hu1
              rw [show u.val = 2 ^ dk + p.val from rfl, z30 xor false fMix dk p.val p.isLt] at ho
              split_ifs at hp with hpk
              · have hfv : fMix p.val = xor (w ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩)
                    (w ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩) := by simp [fMix, hpk, mixDiffAt]
                rw [hfv] at ho
                exact drXor_sat
                  (fun hd => by simpa [DRMode, hd, hW6] using hWMode t0 (z19 k hk _) 6)
                  (fun hd => by simpa [DRMode, hd, hW6] using hWMode t0 (z19 k hk _) 6) ho C hp
              · have hfv : fMix p.val = false := by simp [fMix, hpk]
                rw [hfv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hp
            · have ho := hprM ⟨1, by have := Nat.one_le_pow dk 2 (by omega); rw [pow_succ]; omega⟩ (le_refl 1)
              rw [show (⟨1, _⟩ : Fin (2 ^ (dk + 1))).val = 1 from rfl, z60] at ho
              exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C hrt
            · exact z81 dk fMix _ hupM C hup
            · exact z129 dk fMix _ _ hupM hprM C hpr
            · let pPos := inv3Pos k % k
              let pNeg := (k - pPos) % k
              have hpPos_lt : pPos < k := Nat.mod_lt _ hk
              have hpNeg_lt : pNeg < k := Nat.mod_lt _ hk
              have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
              rcases hx0 with a | b
              · have ho := hWMode t0 ⟨0, hk⟩ 7
                have hv : z1 hk ori isCol leaf key drv t0 ⟨0, hk⟩ 7 =
                    xor (w ⟨0, hk⟩) (z17 xor false fMix dk (2 ^ dk + pPos)) := by
                  rw [z124 hk δ w pPos hpPos_lt]
                  simp [z1, hrevF, Bool.false_eq_true, pPos, w, uW, st, idx, δ, t0]
                rw [hv] at ho
                exact drXor_sat
                  (fun hd => by simpa [DRMode, hd, hW6] using hWMode t0 (z19 k hk ⟨0, hk⟩) 6)
                  (fun hd => by simpa [DRMode, hd] using hprM _ (by have := Nat.one_le_pow (Nat.clog 2 k) 2 (by omega); dsimp; omega))
                  ho C a
              · have ho := hWMode t0 ⟨1 % k, Nat.mod_lt _ hk⟩ 7
                have hv : z1 hk ori isCol leaf key drv t0 ⟨1 % k, Nat.mod_lt _ hk⟩ 7 =
                    xor (z1 hk ori isCol leaf key drv t0 ⟨0, hk⟩ 7)
                      (z17 xor false fMix dk (2 ^ dk + pNeg)) := by
                  rw [z124 hk δ w pNeg hpNeg_lt]
                  simp [z1, hrevF, Bool.false_eq_true, h1m, pPos, pNeg, w, uW, st, idx, δ, t0]
                rw [hv] at ho
                exact drXor_sat
                  (fun hd => by simpa [DRMode, hd] using hWMode t0 ⟨0, hk⟩ 7)
                  (fun hd => by simpa [DRMode, hd] using hprM _ (by have := Nat.one_le_pow (Nat.clog 2 k) 2 (by omega); dsimp; omega))
                  ho C b
            · rw [List.mem_flatMap] at hout; rcases hout with ⟨i, _, hi⟩
              have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
              have ho := hWMode t1 i 0
              have hv : z1 hk ori isCol leaf key drv t1 i 0 =
                  xor (z1 hk ori isCol leaf key drv t0 ⟨1 % k, Nat.mod_lt _ hk⟩ 7)
                    (z17 xor false fMix dk (2 ^ dk + (m3dInv k δ hk i).val)) := by
                rw [z124 hk δ w (m3dInv k δ hk i).val (m3dInv k δ hk i).isLt]
                dsimp [z1, t0, t1, z11, revRoundB, invMixB]
                simp [hrevF, Bool.false_eq_true, h3, hk5, h1m, w, uW, st, idx, δ]
              rw [hv] at ho
              exact drXor_sat
                (fun hd => by simpa [DRMode, hd] using hWMode t0 ⟨1 % k, Nat.mod_lt _ hk⟩ 7)
                (fun hd => by simpa [DRMode, hd] using hprM _ (by have := Nat.one_le_pow (Nat.clog 2 k) 2 (by omega); dsimp; omega))
                ho C hi
            · rcases hsw with h1 | h2
              · have ho := hPMode t0 false
                have hv : z22 hk ori isCol leaf key drv t0 false = true := by
                  simp [z22, hrev, h3]
                rw [hv] at ho; exact drEq_sat (fun _ => ⟨rfl, rfl⟩) ho C h1
              · have ho := hPMode t1 true
                have hv : z22 hk ori isCol leaf key drv t1 true =
                    (z22 hk ori isCol leaf key drv t0 true &&
                     z22 hk ori isCol leaf key drv t0 false) := by
                  simp [z22, hrev, h3, z11, revRoundB, t0, t1, idx]
                rw [hv] at ho
                exact drAnd_sat
                  (fun hd => by simpa [DRMode, hd] using hPMode t0 true)
                  (fun hd => by simpa [DRMode, hd] using hPMode t0 false) ho C h2
      · rw [List.mem_flatMap] at hfin; rcases hfin with ⟨j, _, hj⟩
        have ho := hWMode ⟨0, Nat.zero_lt_succ r⟩ j 8
        have hv : z1 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ j 8 =
            xor (key ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩)
              (z1 hk ori isCol leaf key drv ⟨r, Nat.lt_succ_self r⟩ j 0) := by
          dsimp [z1, z108, rotB]
          simp only [hrevF, Bool.false_eq_true, ↓reduceIte, z164]
        rw [hv] at ho
        exact drXor_sat (fun hd => by simpa [DRMode, hd] using hkeyMode _)
          (fun hd => by simpa [DRMode, hd] using hWMode ⟨r, Nat.lt_succ_self r⟩ j 0) ho C hj
  ·
    by_cases hs : s = sTrue
    · have hW8 : ∀ j : Fin k, z1 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ j 8 =
          (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j := by
        intro j; cases hrev : branchRev ori isCol <;> simp [z1, z13, hrev]
      have hPr : z22 hk ori isCol leaf key drv ⟨r, Nat.lt_succ_self r⟩ true =
          (z13 hk r isCol (branchRev ori isCol) leaf key drv).2 := by
        cases hrev : branchRev ori isCol <;> simp [z22, z13, z108, z164, hrev]
      rcases hdead with h1 | h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases h1 with rfl | rfl
        · rw [z6]; intro hx
          dsimp [α, ori, lEv, vExcl, vSyn, vMat, vAux, auxVal] at hx; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori] at hx
        · rw [z6]; intro hp
          have hpm := hPMode ⟨r, Nat.lt_succ_self r⟩ true
          have hd : dead = false := by simp [dead, hs]
          rw [hd, hPr] at hpm
          have hfalse : (z13 hk r isCol (branchRev ori isCol) leaf key drv).2 = false := by
            rw [hpm.1] at hp; cases hok : (z13 hk r isCol (branchRev ori isCol) leaf key drv).2 <;> simp_all
          dsimp [α, ori, lEv, vLeafDead, vLeaf, vSyn, vMat, vAux, auxVal, z86]
          simp [hs, sTrue, xDrv, ori, key, drv, hfalse]
      · rw [List.mem_flatMap] at h2; rcases h2 with ⟨j, _, hj⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        have hwm := hWMode ⟨0, Nat.zero_lt_succ r⟩ j 8
        have hd : dead = false := by simp [dead, hs]
        rw [hd, hW8 j] at hwm
        rcases hj with rfl | rfl <;> rw [z45] <;> intro hraw hw
        · have h1 : v (z15 ori isCol, j) = true := by simpa [α, lEv, vRaw] using hraw
          have h2 : (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j = false := by
            rw [hwm.1] at hw; cases hb : (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j <;> simp_all
          have hne : (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 ≠
              fun j => v (z15 ori isCol, j) := fun heq => by
            have := congrFun heq j; rw [h1, h2] at this; exact Bool.false_ne_true this
          dsimp [α, ori, lEv, vLeafDead, vLeaf, vSyn, vMat, vAux, auxVal, z86]
          simp [hs, sTrue, xDrv, ori, key, drv, hne]
        · have h1 : v (z15 ori isCol, j) = false := by simpa [α, lEv, vRaw] using hraw
          have h2 : (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j = true := by
            rw [hwm.2] at hw; exact hw
          have hne : (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 ≠
              fun j => v (z15 ori isCol, j) := fun heq => by
            have := congrFun heq j; rw [h1, h2] at this; exact Bool.noConfusion this
          dsimp [α, ori, lEv, vLeafDead, vLeaf, vSyn, vMat, vAux, auxVal, z86]
          simp [hs, sTrue, xDrv, ori, key, drv, hne]
    · rcases hdead with h1 | h2
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases h1 with rfl | rfl <;> rw [z6] <;>
          (intro _; dsimp [α, ori, lEv, vLeafDead, vLeaf, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
      · rw [List.mem_flatMap] at h2; rcases h2 with ⟨j, _, hj⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl <;> rw [z45] <;>
          (intro _ _; dsimp [α, ori, lEv, vLeafDead, vLeaf, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
  ·
    rw [List.mem_flatMap] at hkill; rcases hkill with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    by_cases hs : s = sTrue
    · have hW8 : z1 hk ori isCol leaf key drv ⟨0, Nat.zero_lt_succ r⟩ j 8 =
          (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j := by
        cases hrev : branchRev ori isCol <;> simp [z1, z13, hrev]
      rcases hb with rfl | rfl <;> rw [z6] <;> intro h
      · dsimp [α, ori, lEv, vLeafDead, z90, vLeaf, vSyn, vMat, vAux, auxVal, z117] at h ⊢
        simp [hs, sTrue, xDrv, ori, key, drv] at h ⊢; exact Or.inl h
      · have hwm := hWMode ⟨0, Nat.zero_lt_succ r⟩ j 8
        have hd : dead = false := by simp [dead, hs]
        rw [hd, hW8] at hwm
        have hne : ((z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j != b) = true := by
          have hwm' : DRMode α false (z91 (rR, cR) m s isCol leaf 0 j 8)
              ((z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j) := hwm
          cases b <;> cases hval : (z13 hk r isCol (branchRev ori isCol) leaf key drv).1 j <;>
            simp [drFlip, hwm'.1, hwm'.2, hval] at h ⊢
        dsimp [α, ori, lEv, z90, vLeaf, vSyn, vMat, vAux, auxVal, z117]
        simp [hs, sTrue, xDrv, ori, key, drv, hne]
    · rcases hb with rfl | rfl <;> rw [z6] <;>
        (intro _; dsimp [α, ori, lEv, z90, vLeaf, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori])
theorem synAggClauses_sat (hk : 0 < k) (hk_odd : k % 2 = 1) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) (v : V5 k -> Bool)
    (hag : (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) /\
           (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j))) :
    ∀ C ∈ (z35 (k := k) (r := r) (h' := h') (R := R) hk ori m s),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  rcases ori with ⟨rR, cR⟩
  let ori : Bool × Bool := (rR, cR)
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  let xDrv : Fin (3 * k) -> Bool := fun idx => v (drvPos hk ori idx)
  let sTrue := synOf (H m) xDrv
  let dB := dBOf k r
  have hexLeaf : ∀ isCol : Bool, ∃ lf : Fin (z2 k r), z86 hk ori isCol lf v = false := by
    intro isCol
    have hbr : (fun j => v (if isCol then 4 else 3, j)) =
        z42 hk r isCol (fun j => v (2, j)) (fun j => v (if isCol then 1 else 0, j)) := by
      cases isCol
      · rw [z61]; exact hag.1
      · rw [z71]; exact hag.2
    obtain ⟨lf, hlf⟩ := z148 hk hk_odd r isCol (branchRev ori isCol)
      (fun j => v (2, j)) (fun j => v (if isCol then 1 else 0, j))
    refine ⟨lf, ?_⟩
    dsimp [z86]
    have hdrv_eq : (fun j => v (dTrack ori (z8 isCol), j)) =
        if branchRev ori isCol then z42 hk r isCol (fun j => v (2, j)) (fun j => v (if isCol then 1 else 0, j))
        else (fun j => v (if isCol then 1 else 0, j)) := by
      cases isCol <;> (simp only [Bool.false_eq_true, ↓reduceIte] at hbr; cases rR <;> cases cR <;> simp [ori, z8, branchRev, dTrack, hbr])
    have htgt_eq : (fun j => v (z15 ori isCol, j)) =
        if branchRev ori isCol then (fun j => v (if isCol then 1 else 0, j))
        else z42 hk r isCol (fun j => v (2, j)) (fun j => v (if isCol then 1 else 0, j)) := by
      cases isCol <;> (simp only [Bool.false_eq_true, ↓reduceIte] at hbr; cases rR <;> cases cR <;> simp [ori, z15, branchRev, hbr])
    rw [hdrv_eq, hlf, htgt_eq]; simp
  intro C hC; change ClauseSat α C; dsimp only [z35] at hC
  simp only [List.mem_append] at hC
  by_cases hs : s = sTrue
  · rcases hC with (((h1 | h2) | h3) | h4) | h5
    · rw [List.mem_flatMap] at h1; rcases h1 with ⟨isCol, _, hi⟩
      let fD : ℕ -> Bool := fun l => if hl : l < z2 k r then z86 hk ori isCol ⟨l, hl⟩ v else true
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with (hlf | ha) | rfl
      · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨l, _, hl⟩
        simp only [List.mem_singleton] at hl; rw [hl, z6]; intro h
        dsimp [α, ori, lEv, vLeafDead, vLeaf, z69, vSyn, vMat, vAux, auxVal] at h ⊢
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true] at h ⊢
        rw [z30 and true _ dB l.val l.isLt]
        have hlt : l.val < z2 k r := by rw [← z67]; exact l.isLt
        simp [hlt, h]
      · exact z95 dB fD _ (fun u _ => by
          dsimp [α, ori, lEv, z69, vSyn, vMat, vAux, auxVal, fD, dB]
          simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true]) C ha
      · rw [z6]; intro h
        exfalso
        obtain ⟨lf, hlf⟩ := hexLeaf isCol
        have hroot : heapUpVal and true fD dB 1 = false :=
          z66 (j := lf.val) (by rw [z67]; exact lf.isLt) (by simp [fD, lf.isLt, hlf])
        dsimp [α, ori, lEv, z69, vSyn, vMat, vAux, auxVal] at h
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true] at h
        change heapUpVal and true fD dB 1 = true at h
        rw [hroot] at h; exact Bool.false_ne_true h
    · simp only [List.mem_singleton] at h2; rw [h2, z6]; intro h
      dsimp [α, ori, lEv, vExcl, vSyn, vMat, vAux, auxVal] at h; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori] at h
    · rw [List.mem_flatMap] at h3; rcases h3 with ⟨isCol, _, hi⟩
      rw [List.mem_flatMap] at hi; rcases hi with ⟨j, _, hj⟩
      rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
      let fK : ℕ -> Bool := fun l =>
        if hl : l < z2 k r then z117 hk ori isCol ⟨l, hl⟩ v j b else true
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with (hlf | ha) | rfl
      · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨l, _, hl⟩
        simp only [List.mem_singleton] at hl; rw [hl, z6]; intro h
        dsimp [α, ori, lEv, z90, vLeaf, z68, vSyn, vMat, vAux, auxVal] at h ⊢
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true] at h ⊢
        rw [z30 and true _ dB l.val l.isLt]
        have hlt : l.val < z2 k r := by rw [← z67]; exact l.isLt
        simp [hlt, h]
      · exact z95 dB fK _ (fun u _ => by
          dsimp [α, ori, lEv, z68, vSyn, vMat, vAux, auxVal, fK, dB]
          simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true]) C ha
      · rw [z6]; intro h
        dsimp [α, ori, lEv, z68, vKillLit, vSyn, vMat, vAux, auxVal] at h ⊢
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, beq_true] at h ⊢
        by_cases hvb : v (z15 ori isCol, j) = b
        · exfalso
          obtain ⟨lf, hlf⟩ := hexLeaf isCol
          have hlf_eq : (z13 hk r isCol (branchRev ori isCol) lf
              (fun i => v (2, i)) (fun i => v (dTrack ori (z8 isCol), i))).1 j =
              v (z15 ori isCol, j) := by
            dsimp [z86] at hlf
            simp only [Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at hlf
            exact congrFun hlf.2 j
          have hkf : fK lf.val = false := by
            simp [fK, lf.isLt, z117, hlf, hlf_eq, hvb]
          have hroot : heapUpVal and true fK dB 1 = false :=
            z66 (j := lf.val) (by rw [z67]; exact lf.isLt) hkf
          change heapUpVal and true fK dB 1 = true at h
          rw [hroot] at h; exact Bool.false_ne_true h
        · cases h1 : v (z15 ori isCol, j) <;> cases b <;> simp_all
    · rw [List.mem_flatMap] at h4; rcases h4 with ⟨tr, _, ht⟩
      rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
      rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
      simp only [List.mem_singleton] at hb; rw [hb, z6]; intro h
      dsimp [α, ori, lEv, vSynDead, vSyn, vMat, vAux, auxVal] at h; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori] at h
    · rw [List.mem_flatMap] at h5; rcases h5 with ⟨slot, _, hsl⟩
      rw [List.mem_flatMap] at hsl; rcases hsl with ⟨j, _, hj⟩
      rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
      simp only [List.mem_singleton] at hb; rw [hb, z6]; intro h
      cases b
      · dsimp [α, ori, lEv, drFlip, drXDual, vKillLit, vSyn, vMat, vAux, auxVal, xDrv] at h ⊢
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, z49, beq_true] at h ⊢
        cases h1 : v (dTrack (rR, cR) slot, j) <;> simp_all
      · dsimp [α, ori, lEv, drFlip, drXDual, vKillLit, vSyn, vMat, vAux, auxVal, xDrv] at h ⊢
        simp only [hs, sTrue, xDrv, ori, ne_eq, not_true_eq_false, ↓reduceIte, z49, beq_true] at h ⊢
        cases h1 : v (dTrack (rR, cR) slot, j) <;> simp_all
  ·
    rcases hC with (((h1 | h2) | h3) | h4) | h5
    · rw [List.mem_flatMap] at h1; rcases h1 with ⟨isCol, _, hi⟩
      simp only [List.mem_append, List.mem_singleton] at hi
      rcases hi with (hlf | ha) | rfl
      · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨l, _, hl⟩
        simp only [List.mem_singleton] at hl; rw [hl, z6]; intro _
        dsimp [α, ori, lEv, z69, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
      · rw [z24, List.mem_flatMap] at ha; rcases ha with ⟨u, _, hu⟩
        split_ifs at hu with h
        · simp only [List.mem_singleton] at hu; rw [hu, z45]; intro _ _
          dsimp [α, ori, lEv, z69, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
        · simp at hu
      · rw [z6]; intro _; dsimp [α, ori, lEv, vSynDead, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
    · simp only [List.mem_singleton] at h2; rw [h2, z6]; intro _
      dsimp [α, ori, lEv, vSynDead, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
    · rw [List.mem_flatMap] at h3; rcases h3 with ⟨isCol, _, hi⟩
      rw [List.mem_flatMap] at hi; rcases hi with ⟨j, _, hj⟩
      rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
      simp only [List.mem_append, List.mem_singleton] at hb
      rcases hb with (hlf | ha) | rfl
      · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨l, _, hl⟩
        simp only [List.mem_singleton] at hl; rw [hl, z6]; intro _
        dsimp [α, ori, lEv, z68, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
      · rw [z24, List.mem_flatMap] at ha; rcases ha with ⟨u, _, hu⟩
        split_ifs at hu with h
        · simp only [List.mem_singleton] at hu; rw [hu, z45]; intro _ _
          dsimp [α, ori, lEv, z68, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
        · simp at hu
      · rw [z6]; intro _; dsimp [α, ori, lEv, vKillLit, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
    · rw [List.mem_flatMap] at h4; rcases h4 with ⟨tr, _, ht⟩
      rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
      rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
      simp only [List.mem_singleton] at hb; rw [hb, z6]; intro _
      dsimp [α, ori, lEv, vKillLit, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
    · rw [List.mem_flatMap] at h5; rcases h5 with ⟨slot, _, hsl⟩
      rw [List.mem_flatMap] at hsl; rcases hsl with ⟨j, _, hj⟩
      rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
      simp only [List.mem_singleton] at hb; rw [hb, z6]; intro _
      dsimp [α, ori, lEv, vKillLit, vSyn, vMat, vAux, auxVal]; simp only [sTrue, xDrv, ori] at hs; simp [hs, sTrue, xDrv, ori, sTrue, xDrv, ori]
theorem matAggClauses_sat (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (v : V5 k -> Bool) :
    ∀ C ∈ (z48 (k := k) (r := r) (h' := h') (R := R) ori m),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  rcases ori with ⟨rR, cR⟩
  let ori : Bool × Bool := (rR, cR)
  let α := Sum.elim v (auxVal (k := k) (r := r) (h' := h') (R := R) hk H v)
  let sTrue := synOf (H m) (fun idx => v (drvPos hk ori idx))
  intro C hC; change ClauseSat α C; dsimp only [z48] at hC
  rw [List.mem_append] at hC
  rcases hC with hdead | hlit
  · simp only [List.mem_append, List.mem_singleton] at hdead
    rcases hdead with (hlf | ha) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨s, _, hs⟩
      simp only [List.mem_singleton] at hs; rw [hs, z6]; intro h
      dsimp [α, ori, lEv, vSynDead, z156, vSyn, vMat, vAux, auxVal] at h ⊢
      rw [z30 and true _ h' s.val s.isLt]
      by_cases hst : s = sTrue
      · simp [hst, sTrue, ori] at h
      · have hne : s.val ≠ sTrue.val := fun heq => hst (Fin.ext heq)
        simp [sTrue, ori] at hne; simp [hne]
    · exact z95 h' (fun s => decide (s ≠ sTrue.val)) _ (fun u _ => by
        dsimp [α, ori, lEv, z156, vMat, vAux, auxVal, sTrue]; rfl) C ha
    · rw [clauseSat_cl1, lEv_negL]
      dsimp [α, ori, lEv, z156, vMat, vAux, auxVal]
      have hroot : heapUpVal and true (fun s => decide (s ≠ sTrue.val)) h' 1 = false :=
        z66 sTrue.isLt (by simp)
      dsimp only [sTrue, ori] at hroot
      simpa [ne_eq, decide_not] using hroot
  · rw [List.mem_flatMap] at hlit; rcases hlit with ⟨tr, _, ht⟩
    rw [List.mem_flatMap] at ht; rcases ht with ⟨j, _, hj⟩
    rw [List.mem_flatMap] at hj; rcases hj with ⟨b, _, hb⟩
    let fK : ℕ -> Bool := fun s => if s = sTrue.val then (v (tr, j) != b) else true
    simp only [List.mem_append, List.mem_singleton] at hb
    rcases hb with (hlf | ha) | rfl
    · rw [List.mem_flatMap] at hlf; rcases hlf with ⟨s, _, hs⟩
      simp only [List.mem_singleton] at hs; rw [hs, z6]; intro h
      dsimp [α, ori, lEv, vKillLit, vAllKilled, vSyn, vMat, vAux, auxVal] at h ⊢
      rw [z30 and true _ h' s.val s.isLt]
      by_cases hst : s = sTrue
      · simp [hst, sTrue, ori] at h ⊢; exact h
      · have hne : s.val ≠ sTrue.val := fun heq => hst (Fin.ext heq)
        simp [sTrue, ori] at hne; simp [hne]
    · exact z95 h' fK _ (fun u _ => by
        dsimp [α, ori, lEv, vAllKilled, vMat, vAux, auxVal, fK, sTrue]; rfl) C ha
    · rw [z6]; intro h
      dsimp [α, ori, lEv, vAllKilled, vRaw, vMat, vAux, auxVal] at h ⊢
      by_cases hvb : v (tr, j) = b
      · exfalso
        have hroot : heapUpVal and true fK h' 1 = false :=
          z66 sTrue.isLt (by simp [fK, hvb])
        change (heapUpVal and true fK h' 1 == true) = true at h
        rw [hroot] at h; exact Bool.false_ne_true h
      · cases h1 : v (tr, j) <;> cases b <;> simp_all
theorem fullClauses_sat (hk : 0 < k) (hk_odd : k % 2 = 1) (H : Fin R -> BMat h' (3 * k))
    (v : V5 k -> Bool)
    (hag : (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) /\
           (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j))) :
    ∀ C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H),
      ClauseSat (Sum.elim v (auxVal hk H v)) C := by
  intro C hC; dsimp only [z7] at hC
  simp only [List.mem_append] at hC
  rcases hC with (h1 | h2) | h3
  · exact constClauses_sat hk H v C h1
  · exact baseClauses_sat hk H v hag C h2
  · rw [List.mem_flatMap] at h3; rcases h3 with ⟨rR, _, h3⟩
    rw [List.mem_flatMap] at h3; rcases h3 with ⟨cR, _, h3⟩
    rw [List.mem_flatMap] at h3; rcases h3 with ⟨m, _, hm⟩
    dsimp only [z47] at hm
    simp only [List.mem_append] at hm
    rcases hm with ((ha | hb) | hc) | hd
    · exact upDownClauses_sat hk H (rR, cR) m v C ha
    · exact walshClauses_sat hk H (rR, cR) m v C hb
    · rw [List.mem_flatMap] at hc; rcases hc with ⟨s, _, hs⟩
      simp only [List.mem_append] at hs
      rcases hs with (hsi | hsl) | hsa
      · exact z159 hk H (rR, cR) m s v C hsi
      · rw [List.mem_flatMap] at hsl; rcases hsl with ⟨isCol, _, hi⟩
        rw [List.mem_flatMap] at hi; rcases hi with ⟨leaf, _, hl⟩
        exact leafCircuitClauses_sat hk H (rR, cR) m s isCol leaf v C hl
      · exact synAggClauses_sat hk hk_odd H (rR, cR) m s v hag C hsa
    · exact matAggClauses_sat hk H (rR, cR) m v C hd
theorem z98 (n : ℕ) (hn : 1 <= n) : 2 ^ Nat.clog 2 n <= 2 * n := by
  by_cases hn1 : n = 1
  · subst hn1; simp
  · have hlt : 1 < n := by omega
    have hclog_pos : 0 < Nat.clog 2 n := Nat.clog_pos (by omega) hlt
    have hprev : 2 ^ (Nat.clog 2 n - 1) < n := by
      by_contra hge; push_neg at hge
      have := Nat.clog_le_of_le_pow hge
      omega
    have hpow : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n - 1) := by
      have : Nat.clog 2 n = (Nat.clog 2 n - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ, mul_comm]
    omega
private theorem card_all_bound (hk : 0 < k) (h : ℕ) (hh' : h' <= h)
    (hR : R <= 3 * (h' + 1) * (Nat.clog 2 (3 * k + 1) + 1)) :
    Fintype.card (AuxAll k r h' R) <=
      10000 * (k + 1) * (r + 1) * z2 k r * (h + 1) ^ 2 *
        (Nat.clog 2 (3 * k + 1) + 1) * 2 ^ h := by
  set B := z2 k r
  set L := Nat.clog 2 (3 * k + 1) + 1
  set dN := Nat.clog 2 (3 * k)
  set dk := Nat.clog 2 k
  set dB := dBOf k r
  have hB1 : 1 <= B := z127 k r
  have hL1 : 1 <= L := by omega
  have h2h : 2 ^ h' <= 2 ^ h := Nat.pow_le_pow_right (by omega) hh'
  have h2hp : 1 <= 2 ^ h' := Nat.one_le_pow h' 2 (by omega)
  have h2dN : 2 ^ dN <= 6 * k := by
    have h1 : 2 ^ dN <= 2 * (3 * k) := z98 (3 * k) (by omega)
    omega
  have h2dk : 2 ^ dk <= 2 * k := z98 k hk
  have h2dB : 2 ^ dB = B := z67 k r
  have h2dN1 : 2 ^ (dN + 1) <= 12 * (k + 1) := by rw [pow_succ]; omega
  have h2dk1 : 2 ^ (dk + 1) <= 4 * (k + 1) := by rw [pow_succ]; omega
  have h2dB1 : 2 ^ (dB + 1) = 2 * B := by rw [pow_succ, h2dB]; ring
  have h2h1 : 2 ^ (h' + 1) = 2 * 2 ^ h' := by rw [pow_succ]; ring
  have hR' : R <= 3 * (h + 1) * L := by
    calc R <= 3 * (h' + 1) * L := hR
      _ <= 3 * (h + 1) * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 3 (by omega))
  have hmul1 : ∀ a b : ℕ, 1 <= b -> a <= a * b := fun a b hb => Nat.le_mul_of_pos_right a hb
  have hrB1 : 1 <= (r + 1) * B := Nat.mul_pos (Nat.succ_pos r) hB1
  have hBh1 : 1 <= (r + 1) * B * (h + 1) := by
    calc 1 <= (r + 1) * B := hrB1
      _ <= (r + 1) * B * (h + 1) := hmul1 _ _ (by omega)
  have hcard_leaf : Fintype.card (AuxLeaf k r) <= 300 * (k + 1) * (r + 1) := by
    simp only [AuxLeaf, AuxLeafWord, AuxLeafChi, AuxLeafMix, AuxLeafWrap, AuxLeafMeta,
      Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Fintype.card_unit]
    change (r + 1) * (k * (9 * 2)) + (r * (9 * (2 ^ (dk + 1) * 2)) +
      (r * (3 * (2 * (2 ^ (dk + 1) * 2))) + ((r + 1) * (2 * 2) + (1 + k * 2)))) <= _
    have h1 : (r + 1) * (k * (9 * 2)) <= 18 * (k + 1) * (r + 1) := by nlinarith only []
    have h2 : r * (9 * (2 ^ (dk + 1) * 2)) <= 72 * (k + 1) * (r + 1) := by nlinarith only [h2dk1]
    have h3 : r * (3 * (2 * (2 ^ (dk + 1) * 2))) <= 48 * (k + 1) * (r + 1) := by nlinarith only [h2dk1]
    have h4 : (r + 1) * (2 * 2) <= 4 * (k + 1) * (r + 1) := by nlinarith only []
    have h5 : 1 + k * 2 <= 3 * (k + 1) * (r + 1) := by nlinarith only []
    linarith only [h1, h2, h3, h4, h5]
  have hcard_syn : Fintype.card (AuxSyn k r h') <= 700 * (k + 1) * (r + 1) * B * (h + 1) := by
    have hsyn_eq : Fintype.card (AuxSyn k r h') =
        (3 * k * 2 + (h' * (2 ^ (dN + 1) * 2) + 2)) +
        (2 * (B * Fintype.card (AuxLeaf k r)) +
         (2 * 2 ^ (dB + 1) + (2 * (k * (2 * 2 ^ (dB + 1))) + 5 * (k * 2)))) := by
      have e1 := Fintype.card_sum (α := z155 k h') (β := (Bool × Fin (z2 k r) × AuxLeaf k r) ⊕ AuxSynAgg k r)
      have e2 := Fintype.card_sum (α := Bool × Fin (z2 k r) × AuxLeaf k r) (β := AuxSynAgg k r)
      have e3 := Fintype.card_prod (α := Bool) (β := Fin (z2 k r) × AuxLeaf k r)
      have e4 := Fintype.card_prod (α := Fin (z2 k r)) (β := AuxLeaf k r)
      have e5 : Fintype.card (z155 k h') = 3 * k * 2 + (h' * (2 ^ (dN + 1) * 2) + 2) := by
        simp [z155, dN]
      have e6 : Fintype.card (AuxSynAgg k r) = 2 * 2 ^ (dB + 1) + (2 * (k * (2 * 2 ^ (dB + 1))) + 5 * (k * 2)) := by
        simp [AuxSynAgg, dB]
      calc Fintype.card (AuxSyn k r h')
          = Fintype.card (z155 k h') + Fintype.card ((Bool × Fin (z2 k r) × AuxLeaf k r) ⊕ AuxSynAgg k r) := e1
        _ = _ := by rw [e2, e3, e4, e5, e6, Fintype.card_bool, Fintype.card_fin]
    rw [hsyn_eq]
    have h1 : 3 * k * 2 + (h' * (2 ^ (dN + 1) * 2) + 2) <= 32 * (k + 1) * (h + 1) := by nlinarith only [hh', h2dN1]
    have h2 : 2 * (B * Fintype.card (AuxLeaf k r)) <= 600 * (k + 1) * (r + 1) * B := by
      calc 2 * (B * Fintype.card (AuxLeaf k r))
          <= 2 * (B * (300 * (k + 1) * (r + 1))) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left B hcard_leaf)
        _ = 600 * (k + 1) * (r + 1) * B := by ring
    have h3 : 2 * 2 ^ (dB + 1) + (2 * (k * (2 * 2 ^ (dB + 1))) + 5 * (k * 2)) <= 22 * (k + 1) * B := by
      rw [h2dB1]; nlinarith only [hB1]
    have h4 : 32 * (k + 1) * (h + 1) <= 32 * (k + 1) * (r + 1) * B * (h + 1) := by
      calc 32 * (k + 1) * (h + 1)
          <= 32 * (k + 1) * (h + 1) * ((r + 1) * B) := hmul1 _ _ hrB1
        _ = 32 * (k + 1) * (r + 1) * B * (h + 1) := by ring
    have h5 : 600 * (k + 1) * (r + 1) * B <= 600 * (k + 1) * (r + 1) * B * (h + 1) :=
      hmul1 _ _ (by omega)
    have h6 : 22 * (k + 1) * B <= 22 * (k + 1) * (r + 1) * B * (h + 1) := by
      calc 22 * (k + 1) * B
          <= 22 * (k + 1) * B * ((r + 1) * (h + 1)) := hmul1 _ _ (Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos h))
        _ = 22 * (k + 1) * (r + 1) * B * (h + 1) := by ring
    have hM0 : 0 <= (k + 1) * (r + 1) * B * (h + 1) := Nat.zero_le _
    linarith only [h1, h2, h3, h4, h5, h6, hM0]
  have hcard_mat : Fintype.card (AuxMatrix k r h') <= 800 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
    have hmat_eq : Fintype.card (AuxMatrix k r h') =
        2 ^ h' * (2 * (2 ^ (dN + 1) * 2)) +
        (3 * k * ((h' + 1) * (2 ^ h' * 2)) +
         (2 ^ h' * Fintype.card (AuxSyn k r h') +
          (2 ^ (h' + 1) + 5 * (k * (2 * 2 ^ (h' + 1)))))) := by
      have e1 := Fintype.card_sum (α := AuxUpDown k h') (β := AuxWalsh k h' ⊕ (Fin (2 ^ h') × AuxSyn k r h') ⊕ AuxMatAgg k h')
      have e2 := Fintype.card_sum (α := AuxWalsh k h') (β := (Fin (2 ^ h') × AuxSyn k r h') ⊕ AuxMatAgg k h')
      have e3 := Fintype.card_sum (α := Fin (2 ^ h') × AuxSyn k r h') (β := AuxMatAgg k h')
      have e4 := Fintype.card_prod (α := Fin (2 ^ h')) (β := AuxSyn k r h')
      have e5 : Fintype.card (AuxUpDown k h') = 2 ^ h' * (2 * (2 ^ (dN + 1) * 2)) := by simp [AuxUpDown, dN]
      have e6 : Fintype.card (AuxWalsh k h') = 3 * k * ((h' + 1) * (2 ^ h' * 2)) := by simp [AuxWalsh]
      have e7 : Fintype.card (AuxMatAgg k h') = 2 ^ (h' + 1) + 5 * (k * (2 * 2 ^ (h' + 1))) := by simp [AuxMatAgg]
      calc Fintype.card (AuxMatrix k r h')
          = Fintype.card (AuxUpDown k h') + Fintype.card (AuxWalsh k h' ⊕ (Fin (2 ^ h') × AuxSyn k r h') ⊕ AuxMatAgg k h') := e1
        _ = _ := by rw [e2, e3, e4, e5, e6, e7, Fintype.card_fin]
    rw [hmat_eq]
    have h1 : 2 ^ h' * (2 * (2 ^ (dN + 1) * 2)) <= 48 * (k + 1) * 2 ^ h' := by
      calc 2 ^ h' * (2 * (2 ^ (dN + 1) * 2)) = 4 * 2 ^ (dN + 1) * 2 ^ h' := by ring
        _ <= 4 * (12 * (k + 1)) * 2 ^ h' := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 h2dN1)
        _ = 48 * (k + 1) * 2 ^ h' := by ring
    have h2 : 3 * k * ((h' + 1) * (2 ^ h' * 2)) <= 6 * (k + 1) * (h + 1) * 2 ^ h' := by
      have ha : 3 * k * (h' + 1) <= 3 * (k + 1) * (h + 1) := by nlinarith only [hh']
      calc 3 * k * ((h' + 1) * (2 ^ h' * 2))
          = (3 * k * (h' + 1)) * (2 * 2 ^ h') := by ring
        _ <= (3 * (k + 1) * (h + 1)) * (2 * 2 ^ h') := Nat.mul_le_mul_right _ ha
        _ = 6 * (k + 1) * (h + 1) * 2 ^ h' := by ring
    have h3 : 2 ^ h' * Fintype.card (AuxSyn k r h') <= 700 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
      calc 2 ^ h' * Fintype.card (AuxSyn k r h')
          <= 2 ^ h' * (700 * (k + 1) * (r + 1) * B * (h + 1)) := Nat.mul_le_mul_left _ hcard_syn
        _ = 700 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by ring
    have h4 : 2 ^ (h' + 1) + 5 * (k * (2 * 2 ^ (h' + 1))) <= 22 * (k + 1) * 2 ^ h' := by
      rw [h2h1]
      calc 2 * 2 ^ h' + 5 * (k * (2 * (2 * 2 ^ h'))) = (20 * k + 2) * 2 ^ h' := by ring
        _ <= (22 * (k + 1)) * 2 ^ h' := Nat.mul_le_mul_right _ (by omega)
        _ = 22 * (k + 1) * 2 ^ h' := by ring
    have h5a : 48 * (k + 1) * 2 ^ h' + 22 * (k + 1) * 2 ^ h' <= 70 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
      calc 48 * (k + 1) * 2 ^ h' + 22 * (k + 1) * 2 ^ h'
          = 70 * (k + 1) * 2 ^ h' := by ring
        _ <= 70 * (k + 1) * 2 ^ h' * ((r + 1) * B * (h + 1)) := hmul1 _ _ hBh1
        _ = 70 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by ring
    have h5b : 6 * (k + 1) * (h + 1) * 2 ^ h' <= 6 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
      calc 6 * (k + 1) * (h + 1) * 2 ^ h'
          <= 6 * (k + 1) * (h + 1) * 2 ^ h' * ((r + 1) * B) := hmul1 _ _ hrB1
        _ = 6 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by ring
    have hM0 : 0 <= (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := Nat.zero_le _
    linarith only [h1, h2, h3, h4, h5a, h5b, hM0]
  have hcard_all : Fintype.card (AuxAll k r h' R) <=
      10000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by
    have hall_eq : Fintype.card (AuxAll k r h' R) =
        2 + (2 * ((r + 1) * (k * 5)) + 2 * (2 * (R * Fintype.card (AuxMatrix k r h')))) := by
      have e1 := Fintype.card_sum (α := AuxConst) (β := AuxBase k r ⊕ (Bool × Bool × Fin R × AuxMatrix k r h'))
      have e2 := Fintype.card_sum (α := AuxBase k r) (β := Bool × Bool × Fin R × AuxMatrix k r h')
      have e3 := Fintype.card_prod (α := Bool) (β := Bool × Fin R × AuxMatrix k r h')
      have e4 := Fintype.card_prod (α := Bool) (β := Fin R × AuxMatrix k r h')
      have e5 := Fintype.card_prod (α := Fin R) (β := AuxMatrix k r h')
      have e6 : Fintype.card AuxConst = 2 := by simp [AuxConst]
      have e7 : Fintype.card (AuxBase k r) = 2 * ((r + 1) * (k * 5)) := by simp [AuxBase]
      calc Fintype.card (AuxAll k r h' R)
          = Fintype.card AuxConst + Fintype.card (AuxBase k r ⊕ (Bool × Bool × Fin R × AuxMatrix k r h')) := e1
        _ = _ := by simp only [e2, e3, e4, e5, e6, e7, Fintype.card_bool, Fintype.card_fin]
    rw [hall_eq]
    have h1 : 2 + 2 * ((r + 1) * (k * 5)) <= 12 * (k + 1) * (r + 1) := by nlinarith only []
    have h2 : 2 * (2 * (R * Fintype.card (AuxMatrix k r h'))) <=
        9600 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by
      calc 2 * (2 * (R * Fintype.card (AuxMatrix k r h')))
          = 4 * R * Fintype.card (AuxMatrix k r h') := by ring
        _ <= 4 * (3 * (h + 1) * L) * (800 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h) := by
            apply Nat.mul_le_mul
            · exact Nat.mul_le_mul_left 4 hR'
            · exact le_trans hcard_mat (Nat.mul_le_mul_left _ h2h)
        _ = 9600 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by ring
    have h3 : 12 * (k + 1) * (r + 1) <= 400 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by
      have hpos : 1 <= B * (h + 1) ^ 2 * L * 2 ^ h :=
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB1 (Nat.pow_pos (Nat.succ_pos h))) hL1) (Nat.pow_pos (by decide))
      calc 12 * (k + 1) * (r + 1)
          <= 12 * (k + 1) * (r + 1) * (B * (h + 1) ^ 2 * L * 2 ^ h) := hmul1 _ _ hpos
        _ <= 400 * (k + 1) * (r + 1) * (B * (h + 1) ^ 2 * L * 2 ^ h) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
        _ = 400 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by ring
    have hM0 : 0 <= (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := Nat.zero_le _
    linarith only [h1, h2, h3, hM0]
  exact hcard_all
private theorem len_leaf_bound (hk : 0 < k) (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) :
    (z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf).length <=
      300 * (k + 1) * (r + 1) := by
  set dk := Nat.clog 2 k
  have h2dk : 2 ^ dk <= 2 * k := z98 k hk
  dsimp [z9]
  simp only [List.length_append]
  refine le_trans (Nat.add_le_add (Nat.add_le_add (b := 280 * (k + 1) * (r + 1)) (d := 2 + k * 2) ?hcore ?hdead) (d := k * 4) ?hkill) ?hsum
  · by_cases hrev : (!branchRev ori isCol) = true
    · simp only [hrev, ↓reduceIte, List.length_append]
      refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (z0 _ _ 4 fun _ _ => by simp [drXor])
        (z0 _ _ (k * 20) fun _ _ =>
          le_trans (z0 _ _ 20 fun _ _ => by simp [drXor, drAnd]) (by simp)))
        (z0 _ _ 2 fun _ _ => by simp [drEq]))
        (le_of_eq (show (drEq (W := VarAll k r h' R) z26 _).length = 2 from rfl))) ?_
      simp only [List.length_finRange]; nlinarith only []
    · have hrevF : (!branchRev ori isCol) = false := Bool.eq_false_iff.mpr hrev
      simp only [hrevF, Bool.false_eq_true, ↓reduceIte, List.length_append]
      refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (z0 _ _ 2 fun _ _ => by simp [drEq])
        (le_of_eq (show (drEq (W := VarAll k r h' R) z26 _).length = 2 from rfl)))
        (z0 _ _ (260 * (k + 1)) fun t _ => by
          simp only [List.length_append]
          have ha := heapAff_lengths dk
            (fun u => (drLeafChi (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf t 0 u,
                       drLeafChi ori m s isCol leaf t 1 u))
            (fun u => (drLeafChi ori m s isCol leaf t 2 u, drLeafChi ori m s isCol leaf t 3 u))
            (fun u => (drLeafChi ori m s isCol leaf t 4 u, drLeafChi ori m s isCol leaf t 5 u))
            (drLeafChi ori m s isCol leaf t 6) (drLeafChi ori m s isCol leaf t 7) (drLeafChi ori m s isCol leaf t 8)
          refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
            (z0 _ _ 4 fun _ _ => by simp [drXor])
            (z0 _ _ 4 fun _ _ => by split_ifs <;> simp [drEq]))
            (by simp [drEq] : _ <= 8))
            ha.1) ha.2.1) ha.2.2)
            (z0 _ _ 20 fun _ _ => by simp [drAffComp, drAnd, drXor]))
            (d := 120 * (k + 1)) ?hmix) ?_
          · split_ifs
            · simp only [List.length_append]
              refine le_trans (Nat.add_le_add (Nat.add_le_add
                (z0 _ _ (14 * 2 ^ dk + 2) fun rc _ => by
                  simp only [List.length_append]
                  refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
                    (z0 _ _ 4 fun _ _ => by split_ifs <;> simp [drXor, drEq])
                    (le_of_eq (show (drEq (W := VarAll k r h' R) z3 _).length = 2 from rfl)))
                    (z63 dk _))
                    (z107 dk _ _)) ?_
                  simp only [List.length_finRange]; dsimp only [dk]; omega)
                (z0 _ _ 4 fun _ _ => by split_ifs <;> simp [drEq, drXor]))
                (by simp [drAnd] : _ <= 8)) ?_
              simp only [List.length_finRange]; nlinarith only [h2dk]
            · simp only [List.length_append]
              refine le_trans (Nat.add_le_add
                (z0 _ _ 2 fun _ _ => by simp [drEq])
                (by simp [drEq, drAnd] : _ <= 6)) ?_
              simp only [List.length_finRange]; omega
            · simp only [List.length_append]
              refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
                (z0 _ _ 4 fun _ _ => by split_ifs <;> simp [drXor, drEq])
                (le_of_eq (show (drEq (W := VarAll k r h' R) z3 _).length = 2 from rfl)))
                (z63 dk _))
                (z107 dk _ _))
                (by simp [drXor] : _ <= 8))
                (z0 _ _ 4 fun _ _ => by simp [drXor]))
                (by simp [drEq, drAnd] : _ <= 6)) ?_
              simp only [List.length_finRange]; nlinarith only [h2dk]
          · simp only [List.length_finRange]; nlinarith only [h2dk]))
        (z0 _ _ 4 fun _ _ => by simp [drXor])) ?_
      simp only [List.length_finRange]; nlinarith only []
  · simp only [List.length_cons]
    refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (z0 _ _ 2 fun _ _ => by simp) 1) 1) ?_
    simp only [List.length_finRange]; omega
  · exact le_trans (z0 _ _ 4 fun _ _ =>
      le_trans (z0 _ _ 2 fun _ _ => by simp) (by simp)) (by simp)
  · nlinarith only []
theorem size_bound_all (hk : 0 < k) (h : ℕ) (hh' : h' <= h)
    (H : Fin R -> BMat h' (3 * k))
    (hR : R <= 3 * (h' + 1) * (Nat.clog 2 (3 * k + 1) + 1)) :
    Fintype.card (AuxAll k r h' R) + 3 * (z7 (k := k) (r := r) (h' := h') (R := R) hk H).length <=
      16777216 * (k + 1) * (r + 1) * z2 k r * (h + 1) ^ 2 *
        (Nat.clog 2 (3 * k + 1) + 1) * 2 ^ h := by
  set B := z2 k r
  set L := Nat.clog 2 (3 * k + 1) + 1
  set dN := Nat.clog 2 (3 * k)
  set dk := Nat.clog 2 k
  set dB := dBOf k r
  have hB1 : 1 <= B := z127 k r
  have hL1 : 1 <= L := by omega
  have h2h : 2 ^ h' <= 2 ^ h := Nat.pow_le_pow_right (by omega) hh'
  have h2hp : 1 <= 2 ^ h' := Nat.one_le_pow h' 2 (by omega)
  have h2dN : 2 ^ dN <= 6 * k := by
    have h1 : 2 ^ dN <= 2 * (3 * k) := z98 (3 * k) (by omega)
    omega
  have h2dk : 2 ^ dk <= 2 * k := z98 k hk
  have h2dB : 2 ^ dB = B := z67 k r
  have h2dN1 : 2 ^ (dN + 1) <= 12 * (k + 1) := by rw [pow_succ]; omega
  have h2dk1 : 2 ^ (dk + 1) <= 4 * (k + 1) := by rw [pow_succ]; omega
  have h2dB1 : 2 ^ (dB + 1) = 2 * B := by rw [pow_succ, h2dB]; ring
  have h2h1 : 2 ^ (h' + 1) = 2 * 2 ^ h' := by rw [pow_succ]; ring
  have hR' : R <= 3 * (h + 1) * L := by
    calc R <= 3 * (h' + 1) * L := hR
      _ <= 3 * (h + 1) * L := Nat.mul_le_mul_right L (Nat.mul_le_mul_left 3 (by omega))
  have hmul1 : ∀ a b : ℕ, 1 <= b -> a <= a * b := fun a b hb => Nat.le_mul_of_pos_right a hb
  have hrB1 : 1 <= (r + 1) * B := Nat.mul_pos (Nat.succ_pos r) hB1
  have hBh1 : 1 <= (r + 1) * B * (h + 1) := by
    calc 1 <= (r + 1) * B := hrB1
      _ <= (r + 1) * B * (h + 1) := hmul1 _ _ (by omega)
  have hcard_all : Fintype.card (AuxAll k r h' R) <=
      10000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h :=
    card_all_bound (k := k) (r := r) (h' := h') (R := R) hk h hh' hR
  have hlen_base : (z64 (k := k) (r := r) (h' := h') (R := R) hk).length <= 50 * (k + 1) * (r + 1) := by
    dsimp [z64]
    refine le_trans (z0 _ _ (25 * (k + 1) * (r + 1)) fun isCol _ => ?_) (by simp; nlinarith only [])
    simp only [List.length_append]
    refine le_trans (Nat.add_le_add (Nat.add_le_add
      (z0 _ _ 4 fun _ _ => by simp [tsXor])
      (z0 _ _ (k * 19) fun _ _ =>
        le_trans (z0 _ _ 19 fun _ _ => by simp [tsXor, tsAnd]) (by simp)))
      (z0 _ _ 2 fun _ _ => by simp [tsEq])) ?_
    simp only [List.length_finRange]; nlinarith only []
  have hlen_updn : ∀ ori m, (z40 (k := k) (r := r) (h' := h') (R := R) hk H ori m).length <=
      90 * (k + 1) * 2 ^ h' := by
    intro ori m; dsimp [z40]
    refine le_trans (z0 _ _ (90 * (k + 1)) fun c _ => ?_) (by rw [List.length_finRange, mul_comm])
    simp only [List.length_append]
    refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (z0 _ _ 2 fun _ _ => by split_ifs <;> simp [drEq])
      (le_of_eq (show (drEq (W := VarAll k r h' R) z3 _).length = 2 from rfl)))
      (z63 dN _))
      (z160 dN _ _)) ?_
    simp only [List.length_finRange]; have h2N : 2 ^ Nat.clog 2 (3 * k) <= 6 * k := h2dN; dsimp only [dN]; omega
  have hlen_walsh : ∀ ori m, (z53 (k := k) (r := r) (h' := h') (R := R) hk H ori m).length <=
      18 * (k + 1) * (h + 1) * 2 ^ h' := by
    intro ori m; dsimp [z53]
    refine le_trans (z0 _ _ (6 * (h + 1) * 2 ^ h') fun i _ => ?_) (by
      rw [List.length_finRange]
      calc 3 * k * (6 * (h + 1) * 2 ^ h') = (18 * k) * ((h + 1) * 2 ^ h') := by ring
        _ <= (18 * (k + 1)) * ((h + 1) * 2 ^ h') := Nat.mul_le_mul_right _ (by omega)
        _ = 18 * (k + 1) * (h + 1) * 2 ^ h' := by ring)
    simp only [List.length_append]
    refine le_trans (Nat.add_le_add
      (z0 _ _ 2 fun _ _ => by split_ifs <;> simp)
      (z0 _ _ (2 ^ h' * 4) fun _ _ =>
        le_trans (z0 _ _ 4 fun _ _ =>
          le_trans (z0 _ _ 2 fun _ _ => by simp) (by simp)) (by simp))) ?_
    simp only [List.length_finRange]
    calc 2 ^ h' * 2 + h' * (2 ^ h' * 4) = (2 + 4 * h') * 2 ^ h' := by ring
      _ <= (6 * (h + 1)) * 2 ^ h' := Nat.mul_le_mul_right _ (by omega)
      _ = 6 * (h + 1) * 2 ^ h' := by ring
  have hlen_sinp : ∀ ori m s, (z12 (k := k) (r := r) (h' := h') (R := R) hk H ori m s).length <=
      60 * (k + 1) * (h + 1) := by
    intro ori m s; dsimp [z12]
    simp only [List.length_append]
    refine le_trans (Nat.add_le_add
      (z0 _ _ 5 fun _ _ => by simp)
      (z0 _ _ (6 * 2 ^ dN + 1) fun q _ => by
        simp only [List.length_append, List.length_singleton]
        refine le_trans (Nat.add_le_add (Nat.add_le_add
          (z0 _ _ 2 fun _ _ => by split_ifs <;> simp [drEq])
          (z63 dN _)) (le_refl 1)) ?_
        simp only [List.length_finRange]; dsimp only [dN]; omega)) ?_
    simp only [List.length_finRange]; nlinarith only [h2dN, hh']
  have hlen_leaf : ∀ ori m s isCol leaf,
      (z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf).length <=
        300 * (k + 1) * (r + 1) :=
    len_leaf_bound (k := k) (r := r) (h' := h') (R := R) hk
  have hlen_sagg : ∀ ori m s, (z35 (k := k) (r := r) (h' := h') (R := R) hk ori m s).length <=
      40 * (k + 1) * B := by
    intro ori m s; dsimp [z35]
    simp only [List.length_append, List.length_singleton]
    refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (z0 _ _ (2 * B + 1) fun isCol _ => by
        simp only [List.length_append, List.length_singleton]
        refine le_trans (Nat.add_le_add (Nat.add_le_add
          (z0 _ _ 1 fun _ _ => by simp)
          (z73 dB _)) (le_refl 1)) ?_
        simp only [List.length_finRange]; rw [h2dB]; omega)
      (le_refl 1))
      (z0 _ _ (k * (2 * (2 * B + 1))) fun isCol _ =>
        le_trans (z0 _ _ (2 * (2 * B + 1)) fun j _ =>
          le_trans (z0 _ _ (2 * B + 1) fun b _ => by
            simp only [List.length_append, List.length_singleton]
            refine le_trans (Nat.add_le_add (Nat.add_le_add
              (z0 _ _ 1 fun _ _ => by simp)
              (z73 dB _)) (le_refl 1)) ?_
            simp only [List.length_finRange]; rw [h2dB]; omega) (by simp)) (by simp)))
      (z0 _ _ (k * 2) fun _ _ =>
        le_trans (z0 _ _ 2 fun _ _ =>
          le_trans (z0 _ _ 1 fun _ _ => by simp) (by simp)) (by simp)))
      (z0 _ _ (k * 2) fun _ _ =>
        le_trans (z0 _ _ 2 fun _ _ =>
          le_trans (z0 _ _ 1 fun _ _ => by simp) (by simp)) (by simp))) ?_
    simp only [List.length_finRange, List.length_cons, List.length_nil]; nlinarith only [hB1]
  have hlen_magg : ∀ ori m, (z48 (k := k) (r := r) (h' := h') (R := R) ori m).length <=
      40 * (k + 1) * 2 ^ h' := by
    intro ori m; dsimp [z48]
    simp only [List.length_append, List.length_singleton]
    refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (z0 _ _ 1 fun _ _ => by simp)
      (z73 h' _))
      (le_refl 1))
      (z0 _ _ (k * (2 * (2 * 2 ^ h' + 1))) fun tr _ =>
        le_trans (z0 _ _ (2 * (2 * 2 ^ h' + 1)) fun j _ =>
          le_trans (z0 _ _ (2 * 2 ^ h' + 1) fun b _ => by
            simp only [List.length_append, List.length_singleton]
            refine le_trans (Nat.add_le_add (Nat.add_le_add
              (z0 _ _ 1 fun _ _ => by simp)
              (z73 h' _)) (le_refl 1)) ?_
            simp only [List.length_finRange]; omega) (by simp)) (by simp))) ?_
    simp only [List.length_finRange]; nlinarith only [h2hp]
  have hlen_mat : ∀ ori m, (z47 (k := k) (r := r) (h' := h') (R := R) hk H ori m).length <=
      1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
    intro ori m; dsimp [z47]
    simp only [List.length_append]
    have h1 := hlen_updn ori m
    have h2 := hlen_walsh ori m
    have h4 := hlen_magg ori m
    have h3 : ((List.finRange (2 ^ h')).flatMap fun s =>
        z12 hk H ori m s ++
        (([false, true] : List Bool).flatMap fun isCol =>
          (List.finRange (z2 k r)).flatMap fun leaf =>
            z9 hk ori m s isCol leaf) ++
        z35 hk ori m s).length <=
        2 ^ h' * (700 * (k + 1) * (r + 1) * B * (h + 1)) := by
      refine le_trans (z0 _ _ (700 * (k + 1) * (r + 1) * B * (h + 1)) fun s _ => ?_) (by simp)
      simp only [List.length_append]
      have ha := hlen_sinp ori m s
      have hb : (([false, true] : List Bool).flatMap fun isCol =>
          (List.finRange (z2 k r)).flatMap fun leaf =>
            z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf).length <=
          2 * (B * (300 * (k + 1) * (r + 1))) :=
        le_trans (z0 _ _ (B * (300 * (k + 1) * (r + 1))) fun isCol _ =>
          le_trans (z0 _ _ (300 * (k + 1) * (r + 1)) fun leaf _ =>
            hlen_leaf ori m s isCol leaf) (by simp [B])) (by simp)
      have hc := hlen_sagg ori m s
      have hpa : 60 * (k + 1) * (h + 1) <= 60 * (k + 1) * (r + 1) * B * (h + 1) := by
        calc 60 * (k + 1) * (h + 1) <= 60 * (k + 1) * (h + 1) * ((r + 1) * B) := hmul1 _ _ hrB1
          _ = 60 * (k + 1) * (r + 1) * B * (h + 1) := by ring
      have hpb : 2 * (B * (300 * (k + 1) * (r + 1))) <= 600 * (k + 1) * (r + 1) * B * (h + 1) := by
        calc 2 * (B * (300 * (k + 1) * (r + 1))) = 600 * (k + 1) * (r + 1) * B := by ring
          _ <= 600 * (k + 1) * (r + 1) * B * (h + 1) := hmul1 _ _ (by omega)
      have hpc : 40 * (k + 1) * B <= 40 * (k + 1) * (r + 1) * B * (h + 1) := by
        calc 40 * (k + 1) * B <= 40 * (k + 1) * B * ((r + 1) * (h + 1)) := hmul1 _ _ (Nat.mul_pos (Nat.succ_pos r) (Nat.succ_pos h))
          _ = 40 * (k + 1) * (r + 1) * B * (h + 1) := by ring
      linarith only [ha, hb, hc, hpa, hpb, hpc]
    have h1a : 90 * (k + 1) * 2 ^ h' + 40 * (k + 1) * 2 ^ h' <= 130 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
      calc 90 * (k + 1) * 2 ^ h' + 40 * (k + 1) * 2 ^ h' = 130 * (k + 1) * 2 ^ h' := by ring
        _ <= 130 * (k + 1) * 2 ^ h' * ((r + 1) * B * (h + 1)) := hmul1 _ _ hBh1
        _ = 130 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by ring
    have h1b : 18 * (k + 1) * (h + 1) * 2 ^ h' <= 18 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by
      calc 18 * (k + 1) * (h + 1) * 2 ^ h' <= 18 * (k + 1) * (h + 1) * 2 ^ h' * ((r + 1) * B) := hmul1 _ _ hrB1
        _ = 18 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by ring
    have h3' : 2 ^ h' * (700 * (k + 1) * (r + 1) * B * (h + 1)) =
        700 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := by ring
    have hM0 : 0 <= (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h' := Nat.zero_le _
    linarith only [h1, h2, h3, h4, h1a, h1b, h3', hM0]
  have hlen_full : (z7 (k := k) (r := r) (h' := h') (R := R) hk H).length <=
      20000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by
    dsimp [z7]
    simp only [List.length_append]
    have h0 : (z92 (k := k) (r := r) (h' := h') (R := R)).length = 2 := rfl
    have hm : (([false, true] : List Bool).flatMap fun rR =>
        ([false, true] : List Bool).flatMap fun cR =>
          (List.finRange R).flatMap fun m =>
            z47 (k := k) (r := r) (h' := h') (R := R) hk H (rR, cR) m).length <=
        12000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by
      have hstep1 := z0 ([false, true] : List Bool)
        (fun rR => ([false, true] : List Bool).flatMap fun cR =>
          (List.finRange R).flatMap fun m =>
            z47 (k := k) (r := r) (h' := h') (R := R) hk H (rR, cR) m)
        (2 * (R * (1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h'))) (fun rR _ =>
          le_trans (z0 _ _ (R * (1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h')) fun cR _ =>
            le_trans (z0 _ _ (1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h') fun m _ =>
              hlen_mat (rR, cR) m) (by simp)) (by simp))
      simp only [List.length_cons, List.length_nil] at hstep1
      calc _ <= 2 * (2 * (R * (1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h'))) := hstep1
        _ = 4 * R * (1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h') := by ring
        _ <= 4 * (3 * (h + 1) * L) * (1000 * (k + 1) * (r + 1) * B * (h + 1) * 2 ^ h) := by
            apply Nat.mul_le_mul
            · exact Nat.mul_le_mul_left 4 hR'
            · exact Nat.mul_le_mul_left _ h2h
        _ = 12000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by ring
    have hpos : 1 <= B * (h + 1) ^ 2 * L * 2 ^ h :=
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hB1 (Nat.pow_pos (Nat.succ_pos h))) hL1) (Nat.pow_pos (by decide))
    have hb' : 2 + 50 * (k + 1) * (r + 1) <= 8000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by
      have h1 : 2 + 50 * (k + 1) * (r + 1) <= 52 * (k + 1) * (r + 1) := by nlinarith only []
      calc 2 + 50 * (k + 1) * (r + 1)
          <= 52 * (k + 1) * (r + 1) := h1
        _ <= 52 * (k + 1) * (r + 1) * (B * (h + 1) ^ 2 * L * 2 ^ h) := hmul1 _ _ hpos
        _ <= 8000 * (k + 1) * (r + 1) * (B * (h + 1) ^ 2 * L * 2 ^ h) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
        _ = 8000 * (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := by ring
    have hM0 : 0 <= (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := Nat.zero_le _
    linarith only [h0, hlen_base, hm, hb', hM0]
  have hM0 : 0 <= (k + 1) * (r + 1) * B * (h + 1) ^ 2 * L * 2 ^ h := Nat.zero_le _
  linarith only [hcard_all, hlen_full, hM0]
end SatAndSize
section UnitProp
variable {k r h' R : ℕ}
private theorem mem_fullClauses_const (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) :
    ∀ C ∈ (z92 (k := k) (r := r) (h' := h') (R := R)),
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; rw [List.mem_toFinset]; dsimp only [z7]
  exact List.mem_append_left _ (List.mem_append_left _ hC)
private theorem mem_fullClauses_base (hk : 0 < k) (H : Fin R -> BMat h' (3 * k)) :
    ∀ C ∈ (z64 (k := k) (r := r) (h' := h') (R := R) hk),
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; rw [List.mem_toFinset]; dsimp only [z7]
  exact List.mem_append_left _ (List.mem_append_right _ hC)
private theorem z50 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ z47 (k := k) (r := r) (h' := h') (R := R) hk H ori m,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; rw [List.mem_toFinset]; dsimp only [z7]
  apply List.mem_append_right
  rw [List.mem_flatMap]; refine ⟨ori.1, by cases ori.1 <;> simp, ?_⟩
  rw [List.mem_flatMap]; refine ⟨ori.2, by cases ori.2 <;> simp, ?_⟩
  rw [List.mem_flatMap]; refine ⟨m, List.mem_finRange m, ?_⟩
  rcases ori with ⟨rR, cR⟩; exact hC
private theorem z37 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ z40 (k := k) (r := r) (h' := h') (R := R) hk H ori m,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; apply z50 hk H ori m
  dsimp only [z47]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hC))
private theorem z96 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ z53 (k := k) (r := r) (h' := h') (R := R) hk H ori m,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; apply z50 hk H ori m
  dsimp only [z47]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hC))
private theorem z20 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) :
    ∀ C ∈ z12 (k := k) (r := r) (h' := h') (R := R) hk H ori m s,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; apply z50 hk H ori m
  dsimp only [z47]
  apply List.mem_append_left; apply List.mem_append_right
  rw [List.mem_flatMap]; refine ⟨s, List.mem_finRange s, ?_⟩
  exact List.mem_append_left _ (List.mem_append_left _ hC)
private theorem z38 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r)) :
    ∀ C ∈ z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; apply z50 hk H ori m
  dsimp only [z47]
  apply List.mem_append_left; apply List.mem_append_right
  rw [List.mem_flatMap]; refine ⟨s, List.mem_finRange s, ?_⟩
  apply List.mem_append_left; apply List.mem_append_right
  rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
  rw [List.mem_flatMap]; exact ⟨leaf, List.mem_finRange leaf, hC⟩
private theorem z31 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h')) :
    ∀ C ∈ z35 (k := k) (r := r) (h' := h') (R := R) hk ori m s,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; apply z50 hk H ori m
  dsimp only [z47]
  apply List.mem_append_left; apply List.mem_append_right
  rw [List.mem_flatMap]; refine ⟨s, List.mem_finRange s, ?_⟩
  exact List.mem_append_right _ hC
private theorem z51 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) :
    ∀ C ∈ z48 (k := k) (r := r) (h' := h') (R := R) ori m,
      C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset := by
  intro C hC; apply z50 hk H ori m
  dsimp only [z47]
  exact List.mem_append_right _ hC
private theorem up_const_true (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (S : Set (Lit (VarAll k r h' R))) :
    vConstTrue (k := k) (r := r) (h' := h') (R := R) ∈
      (upS (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset)^[1] S := by
  rw [Function.iterate_one]
  apply upS_unit1
  exact mem_fullClauses_const hk H _ (by simp [z92, cl1])
private theorem z78 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (S : Set (Lit (VarAll k r h' R))) {t : ℕ} (ht : 1 <= t) :
    drFlip (z26 (k := k) (r := r) (h' := h') (R := R)) true ∈
      (upS (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset)^[t] S :=
  z5 _ _ ht (up_const_true hk H S)
private theorem z32 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (S : Set (Lit (VarAll k r h' R))) {t : ℕ} (ht : 1 <= t) :
    drFlip (z3 (k := k) (r := r) (h' := h') (R := R)) false ∈
      (upS (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset)^[t] S :=
  z5 _ _ ht (up_const_true hk H S)
private theorem z97 : ∀ {n : ℕ} (g : Fin n -> Bool),
    ((List.range n).map (fun j => if hj : j < n then g ⟨j, hj⟩ else false)).foldr xor false =
      xorFin g
  | 0, g => by simp [xorFin]
  | n + 1, g => by
    rw [List.range_succ_eq_map, List.map_cons, List.foldr_cons, z57]
    simp only [Nat.zero_lt_succ, ↓reduceDIte]
    congr 1
    rw [List.map_map]
    have hEq : ((List.range n).map ((fun j => if hj : j < n + 1 then g ⟨j, hj⟩ else false) ∘ Nat.succ)) =
        (List.range n).map (fun j => if hj : j < n then g (Fin.succ ⟨j, hj⟩) else false) := by
      refine List.map_congr_left fun j hj => ?_
      rw [List.mem_range] at hj
      have h1 : j + 1 < n + 1 := by omega
      simp [Function.comp, hj, h1, Fin.succ]
    rw [hEq]
    exact z97 (fun j => g j.succ)
private theorem z115 {n d : ℕ} (hle : n <= 2 ^ d) (g : Fin n -> Bool) :
    heapUpVal xor false (fun j => if hj : j < n then g ⟨j, hj⟩ else false) d 1 = xorFin g := by
  rw [z84 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false,
    z99 xor false Bool.xor_assoc Bool.false_xor Bool.xor_false _ hle
      (fun j hj => by simp [show ¬ j < n by omega]),
    z97]
private def mixBits (h' c s t : ℕ) : Fin (2 ^ h') :=
  ⟨toNat (fun q : Fin h' => if q.val < t then s.testBit q.val else c.testBit q.val), toNat_lt _⟩
private theorem z70 (h' c s t : ℕ) (q : ℕ) :
    (mixBits h' c s t).val.testBit q =
      if q < h' then (if q < t then s.testBit q else c.testBit q) else false := by
  by_cases hq : q < h'
  · simp only [mixBits, hq, ↓reduceIte]
    exact z102 (fun p : Fin h' => if p.val < t then s.testBit p.val else c.testBit p.val) ⟨q, hq⟩
  · simp only [hq, ↓reduceIte]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (mixBits h' c s t).isLt
      (Nat.pow_le_pow_right (by omega) (by omega)))
private theorem mixBits_zero {h' : ℕ} (c s : Fin (2 ^ h')) : mixBits h' c.val s.val 0 = c := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
  rw [z70]
  by_cases hq : q < h'
  · simp [hq]
  · simp only [hq, ↓reduceIte]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le c.isLt (Nat.pow_le_pow_right (by omega) (by omega)))).symm
private theorem mixBits_full {h' : ℕ} (c s : Fin (2 ^ h')) : mixBits h' c.val s.val h' = s := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
  rw [z70]
  by_cases hq : q < h'
  · simp [hq]
  · simp only [hq, ↓reduceIte]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) (by omega)))).symm
private theorem mixBits_clear {h' c s t : ℕ} (ht : t < h') (hct : c.testBit t = false) :
    (⟨z75 (mixBits h' c s (t + 1)).val t, z80 (mixBits h' c s (t + 1)).isLt⟩ : Fin (2 ^ h')) =
      mixBits h' c s t := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
  dsimp only
  rw [z89, z70, z70]
  by_cases hqt : q = t
  · subst hqt; simp [ht, hct]
  · simp only [if_neg hqt]
    by_cases hq : q < h'
    · simp only [hq, ↓reduceIte]
      have hiff : (q < t + 1) ↔ (q < t) := by omega
      simp [hiff]
    · simp [hq]
private theorem mixBits_set {h' c s t : ℕ} (ht : t < h') (hct : c.testBit t = true) :
    (⟨setBitNat (mixBits h' c s (t + 1)).val t, z104 (mixBits h' c s (t + 1)).isLt ht⟩ : Fin (2 ^ h')) =
      mixBits h' c s t := by
  apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
  dsimp only
  rw [z103, z70, z70]
  by_cases hqt : q = t
  · subst hqt; simp [ht, hct]
  · simp only [if_neg hqt]
    by_cases hq : q < h'
    · simp only [hq, ↓reduceIte]
      have hiff : (q < t + 1) ↔ (q < t) := by omega
      simp [hiff]
    · simp [hq]
private def dotPref (c s : ℕ) : ℕ -> Bool
  | 0 => false
  | t + 1 => xor (dotPref c s t) (c.testBit t && s.testBit t)
private theorem z158 (c s : ℕ) : ∀ t : ℕ, dotPref c s t = dotBool t c s := by
  intro t
  have hfold : ∀ n, dotPref c s n = ((List.range n).map (fun j => c.testBit j && s.testBit j)).foldl xor false := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => simp [dotPref, List.range_succ, ih]
  rw [hfold]
  have hlr : ∀ L : List Bool, L.foldl xor false = L.foldr xor false := by
    intro L
    have hgen : ∀ acc : Bool, L.foldl xor acc = xor acc (L.foldr xor false) := by
      induction L with
      | nil => intro acc; simp
      | cons a l ih => intro acc; simp only [List.foldl_cons, List.foldr_cons, ih, Bool.xor_assoc]
    rw [hgen false, Bool.false_xor]
  rw [hlr]; dsimp [dotBool]
  rw [← z97 (fun q : Fin t => c.testBit q.val && s.testBit q.val)]
  congr 1; refine List.map_congr_left fun j hj => ?_
  rw [List.mem_range] at hj; simp [hj]
private theorem up_walsh_chain (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (S : Set (Lit (VarAll k r h' R)))
    (i : Fin (3 * k)) (c s : Fin (2 ^ h')) (v0 : Bool) (t0 : ℕ)
    (hstart : vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨0, Nat.zero_lt_succ h'⟩ c v0 ∈
      (upS (z7 hk H).toFinset)^[t0] S) :
    ∀ (t : ℕ) (ht : t <= h'),
      vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨t, by omega⟩ (mixBits h' c.val s.val t)
        (xor v0 (dotPref c.val s.val t)) ∈ (upS (z7 hk H).toFinset)^[t0 + t] S := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  intro t
  induction t with
  | zero =>
    intro _; simp only [Nat.add_zero, dotPref, Bool.xor_false, mixBits_zero]; exact hstart
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    rw [show t0 + (t + 1) = (t0 + t) + 1 by omega, Function.iterate_succ_apply']
    set p := mixBits h' c.val s.val (t + 1)
    set bNew := xor v0 (dotPref c.val s.val (t + 1))
    have hst : p.val.testBit t = s.val.testBit t := by
      rw [z70]; simp [show t < h' by omega]
    have hmemW : ∀ C ∈ z53 (k := k) (r := r) (h' := h') (R := R) hk H ori m, C ∈ F :=
      z96 hk H ori m
    cases hct : c.val.testBit t
    ·
      have hp0 : (⟨z75 p.val t, z80 p.isLt⟩ : Fin (2 ^ h')) = mixBits h' c.val s.val t :=
        mixBits_clear (by omega) hct
      have hbEq : bNew = xor v0 (dotPref c.val s.val t) := by simp [bNew, dotPref, hct]
      have hCl : imp1 (vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨t, by omega⟩
          ⟨z75 p.val t, z80 p.isLt⟩ bNew)
          (vWalsh ori m i ⟨t + 1, Nat.lt_succ_of_le ht⟩ p bNew) ∈ F := by
        apply hmemW; dsimp only [z53]
        rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
        apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨⟨t, by omega⟩, List.mem_finRange _, ?_⟩
        rw [List.mem_flatMap]; refine ⟨p, List.mem_finRange p, ?_⟩
        rw [List.mem_flatMap]; refine ⟨bNew, by cases bNew <;> simp, ?_⟩
        simp
      have hprev' : vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨t, by omega⟩
          ⟨z75 p.val t, z80 p.isLt⟩ bNew ∈ (upS F)^[t0 + t] S := by
        rw [hp0, hbEq]; exact hprev
      exact upS_imp1 hCl hprev'
    ·
      have hp1 : (⟨setBitNat p.val t, z104 p.isLt (by omega)⟩ : Fin (2 ^ h')) = mixBits h' c.val s.val t :=
        mixBits_set (by omega) hct
      have hbEq : xor bNew (p.val.testBit t) = xor v0 (dotPref c.val s.val t) := by
        rw [hst]; simp only [bNew, dotPref, hct, Bool.true_and]
        cases v0 <;> cases dotPref c.val s.val t <;> cases s.val.testBit t <;> rfl
      have hCl : imp1 (vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨t, by omega⟩
          ⟨setBitNat p.val t, z104 p.isLt (by omega)⟩ (xor bNew (p.val.testBit t)))
          (vWalsh ori m i ⟨t + 1, Nat.lt_succ_of_le ht⟩ p bNew) ∈ F := by
        apply hmemW; dsimp only [z53]
        rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
        apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨⟨t, by omega⟩, List.mem_finRange _, ?_⟩
        rw [List.mem_flatMap]; refine ⟨p, List.mem_finRange p, ?_⟩
        rw [List.mem_flatMap]; refine ⟨bNew, by cases bNew <;> simp, ?_⟩
        simp
      have hprev' : vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨t, by omega⟩
          ⟨setBitNat p.val t, z104 p.isLt (by omega)⟩ (xor bNew (p.val.testBit t)) ∈ (upS F)^[t0 + t] S := by
        rw [hp1, hbEq]; exact hprev
      exact upS_imp1 hCl hprev'
private theorem z128 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R)
    (hm : ∀ i ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
      ∃ c : Fin (2 ^ h'), ∀ j ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
        rowMask (H m) c j = decide (j = i))
    (x : Fin (3 * k) -> Bool)
    (hxρ : ∀ idx : Fin (3 * k), ∀ b : Bool, ρ (drvPos hk ori idx) = some b -> x idx = b)
    (s : Fin (2 ^ h')) (hs : synOf (H m) x = s) :
    ∀ i : Fin (3 * k),
      drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) (x i) ∈
        (upS (z7 hk H).toFinset)^[4 + 2 * Nat.clog 2 (3 * k) + h'] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dN := Nat.clog 2 (3 * k)
  set U : Finset (Fin (3 * k)) := Finset.univ.filter (fun idx => ρ (drvPos hk ori idx) = none)
  have hNle : 3 * k <= 2 ^ dN := Nat.le_pow_clog (by omega) (3 * k)
  intro i
  by_cases hiU : i ∈ U
  · obtain ⟨c, hc⟩ := hm i hiU
    have hci : rowMask (H m) c i = true := by simpa using hc i hiU
    set up := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c false
    set dn := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c true
    set fX : ℕ -> Bool := fun j => if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && x ⟨j, hj⟩ else false
    have hFup : ∀ C ∈ z14 dN up, C ∈ F := by
      intro C hC; apply z37 hk H ori m
      dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
      exact List.mem_append_left _ (List.mem_append_right _ hC)
    have hFdn : ∀ C ∈ z27 dN up dn, C ∈ F := by
      intro C hC; apply z37 hk H ori m
      dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
      exact List.mem_append_right _ hC
    have hleaf : ∀ j (hj : j < 2 ^ dN), j ≠ i.val ->
        drFlip (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) (fX j) ∈ (upS F)^[2] S := by
      intro j hj hne
      have hcl_mem : ∀ C ∈ (if hjk : j < 3 * k then
          if rowMask (H m) c ⟨j, hjk⟩ then
            drEq (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
          else drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
        else drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)), C ∈ F := by
        intro C hC; apply z37 hk H ori m
        dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        rw [List.mem_flatMap]; exact ⟨⟨j, hj⟩, List.mem_finRange _, hC⟩
      change _ ∈ (upS F)^[1 + 1] S; rw [Function.iterate_succ_apply']
      by_cases hjk : j < 3 * k
      · by_cases hrm : rowMask (H m) c ⟨j, hjk⟩ = true
        · have hjnotU : (⟨j, hjk⟩ : Fin (3 * k)) ∉ U := by
            intro hmem
            have := hc ⟨j, hjk⟩ hmem
            have hneF : (⟨j, hjk⟩ : Fin (3 * k)) ≠ i := fun heq => hne (congrArg Fin.val heq)
            simp [hneF, hrm] at this
          have hsome : ρ (drvPos hk ori ⟨j, hjk⟩) = some (x ⟨j, hjk⟩) := by
            cases hopt : ρ (drvPos hk ori ⟨j, hjk⟩) with
            | none => exfalso; exact hjnotU (by simp [U, hopt])
            | some b => rw [hxρ ⟨j, hjk⟩ b hopt]
          have hraw : drFlip (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (x ⟨j, hjk⟩) ∈ (upS F)^[1] S := by
            apply z5 F S (by omega : 0 <= 1)
            change drFlip (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (x ⟨j, hjk⟩) ∈ S
            cases hxv : x ⟨j, hjk⟩ <;> exact ⟨drvPos hk ori ⟨j, hjk⟩, rfl, by simpa [drFlip, vRawDR, hxv] using hsome⟩
          have hCsub : ∀ C ∈ drEq (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
            intro C hC; exact hcl_mem C (by simp [hjk, hrm, hC])
          simpa [fX, hjk, hrm] using drEq_up hCsub hraw
        · have hrmf : rowMask (H m) c ⟨j, hjk⟩ = false := Bool.eq_false_iff.mpr hrm
          have hCsub : ∀ C ∈ drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
            intro C hC; exact hcl_mem C (by simp [hjk, hrmf, hC])
          simpa [fX, hjk, hrmf] using drEq_up hCsub (z32 hk H S (le_refl 1))
      · have hCsub : ∀ C ∈ drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
          intro C hC; exact hcl_mem C (by simp [hjk, hC])
        simpa [fX, hjk] using drEq_up hCsub (z32 hk H S (le_refl 1))
    have hroot : drFlip (dn ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) false ∈
        (upS F)^[2 + dN] S := by
      apply z5 F S (by omega : 2 <= 2 + dN)
      change _ ∈ (upS F)^[1 + 1] S; rw [Function.iterate_succ_apply']
      have hCsub : ∀ C ∈ drEq z3
          (dn ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; apply z37 hk H ori m
        dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hC))
      exact drEq_up hCsub (z32 hk H S (le_refl 1))
    have hi_pow : i.val < 2 ^ dN := lt_of_lt_of_le i.isLt hNle
    have hdn_leaf := z134 dN fX up dn hFup hFdn i.val 2 hleaf hroot dN (le_refl dN) i.val hi_pow
      (by simp) (by simp)
    have hidx_eq : hIdx dN (dN - dN) i.val = 2 ^ dN + i.val := by simp [hIdx]
    have hdn_at : drFlip (dn ⟨2 ^ dN + i.val, by change 2 ^ dN + i.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
        (z23 fX dN (2 ^ dN + i.val)) ∈ (upS F)^[2 + 2 * dN] S := by
      have h1 : (⟨hIdx dN (dN - dN) i.val, hIdx_lt (by omega) (by simpa using hi_pow)⟩ : Fin (2 ^ (dN + 1))) =
          ⟨2 ^ dN + i.val, by change 2 ^ dN + i.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx_eq
      rw [h1, hidx_eq, show 2 + dN + dN = 2 + 2 * dN by omega] at hdn_leaf
      exact hdn_leaf
    set v0 := z23 fX dN (2 ^ dN + i.val)
    have hw0 : vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨0, Nat.zero_lt_succ h'⟩ c v0 ∈
        (upS F)^[3 + 2 * dN] S := by
      rw [show 3 + 2 * dN = (2 + 2 * dN) + 1 by omega, Function.iterate_succ_apply']
      have hCl : imp1 (drFlip (dn ⟨2 ^ dN + i.val, by change 2 ^ dN + i.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) v0)
          (vWalsh ori m i ⟨0, Nat.zero_lt_succ h'⟩ c v0) ∈ F := by
        apply z96 hk H ori m
        dsimp only [z53]; rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
        apply List.mem_append_left
        rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
        simp only [hci, ↓reduceIte]
        cases hv0 : v0 <;> simp [drFlip, dn, dN, hv0]
      exact upS_imp1 hCl hdn_at
    have hwh := up_walsh_chain hk H ori m S i c s v0 (3 + 2 * dN) hw0 h' (le_refl h')
    rw [mixBits_full, z158] at hwh
    have hval : xor v0 (dotBool h' c.val s.val) = x i := by
      have hxs := z105 fX dN dN i.val (le_refl dN) hi_pow
      rw [hidx_eq, z30 xor false fX dN i.val hi_pow] at hxs
      have hfi : fX i.val = x i := by simp [fX, i.isLt, hci]
      have hrootVal : heapUpVal xor false fX dN 1 = dotBool h' c.val s.val := by
        rw [z115 hNle (fun j => rowMask (H m) c j && x j), rowMask_dot_eq, hs]
      rw [hfi, hrootVal] at hxs
      dsimp only [v0]
      cases hxi : x i <;> cases ha : z23 fX dN (2 ^ dN + i.val) <;> cases hd : dotBool h' c.val s.val <;> simp_all
    rw [hval] at hwh
    rw [show 4 + 2 * dN + h' = (3 + 2 * dN + h') + 1 by omega, Function.iterate_succ_apply']
    have hCl : imp1 (vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨h', Nat.lt_succ_self h'⟩ s (x i))
        (drFlip (drXDual ori m s i) (x i)) ∈ F := by
      apply z20 hk H ori m s
      dsimp only [z12]; apply List.mem_append_left
      rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
      cases x i <;> simp [drFlip]
    exact upS_imp1 hCl hwh
  ·
    have hsome : ρ (drvPos hk ori i) = some (x i) := by
      cases hopt : ρ (drvPos hk ori i) with
      | none => exfalso; exact hiU (by simp [U, hopt])
      | some b => rw [hxρ i b hopt]
    have hraw : vRaw (k := k) (r := r) (h' := h') (R := R) (drvPos hk ori i) (x i) ∈ S :=
      ⟨drvPos hk ori i, rfl, hsome⟩
    have h1 : drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) (x i) ∈ (upS F)^[1] S := by
      rw [Function.iterate_one]
      have hCl : imp1 (vRaw (drvPos hk ori i) (x i)) (drFlip (drXDual ori m s i) (x i)) ∈ F := by
        apply z20 hk H ori m s
        dsimp only [z12]; apply List.mem_append_left
        rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
        cases x i <;> simp [drFlip]
      exact upS_imp1 hCl hraw
    exact z5 F S (by omega : 1 <= 4 + 2 * dN + h') h1
private theorem up_excl_no_driver (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R)
    (hm : ∀ i ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
      ∃ c : Fin (2 ^ h'), ∀ j ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
        rowMask (H m) c j = decide (j = i))
    (s : Fin (2 ^ h'))
    (hno : ¬ ∃ x : Fin (3 * k) -> Bool,
      (∀ idx b, ρ (drvPos hk ori idx) = some b -> x idx = b) /\ synOf (H m) x = s) :
    vExcl (k := k) (r := r) (h' := h') (R := R) ori m s ∈
      (upS (z7 hk H).toFinset)^[6 + 3 * Nat.clog 2 (3 * k) + h'] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dN := Nat.clog 2 (3 * k)
  set U : Finset (Fin (3 * k)) := Finset.univ.filter (fun idx => ρ (drvPos hk ori idx) = none)
  have hNle : 3 * k <= 2 ^ dN := Nat.le_pow_clog (by omega) (3 * k)
  have hcand : ∀ i : Fin (3 * k), ∃ b : Bool,
      (∀ b0, ρ (drvPos hk ori i) = some b0 -> b = b0) /\
      drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) b ∈ (upS F)^[4 + 2 * dN + h'] S := by
    intro i
    by_cases hiU : i ∈ U
    · obtain ⟨c, hc⟩ := hm i hiU
      have hci : rowMask (H m) c i = true := by simpa using hc i hiU
      set up := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c false
      set dn := drUpDown (k := k) (r := r) (h' := h') (R := R) ori m c true
      set xPart : Fin (3 * k) -> Bool := fun j => (ρ (drvPos hk ori j)).getD false
      set fM : ℕ -> Bool := fun j => if hj : j < 3 * k then rowMask (H m) c ⟨j, hj⟩ && xPart ⟨j, hj⟩ else false
      have hFup : ∀ C ∈ z14 dN up, C ∈ F := by
        intro C hC; apply z37 hk H ori m
        dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
        exact List.mem_append_left _ (List.mem_append_right _ hC)
      have hFdn : ∀ C ∈ z27 dN up dn, C ∈ F := by
        intro C hC; apply z37 hk H ori m
        dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
        exact List.mem_append_right _ hC
      have hleaf : ∀ j (hj : j < 2 ^ dN), j ≠ i.val ->
          drFlip (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) (fM j) ∈ (upS F)^[2] S := by
        intro j hj hne
        have hcl_mem : ∀ C ∈ (if hjk : j < 3 * k then
            if rowMask (H m) c ⟨j, hjk⟩ then
              drEq (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
            else drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
          else drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)), C ∈ F := by
          intro C hC; apply z37 hk H ori m
          dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
          rw [List.mem_flatMap]; exact ⟨⟨j, hj⟩, List.mem_finRange _, hC⟩
        change _ ∈ (upS F)^[1 + 1] S; rw [Function.iterate_succ_apply']
        by_cases hjk : j < 3 * k
        · by_cases hrm : rowMask (H m) c ⟨j, hjk⟩ = true
          · have hjnotU : (⟨j, hjk⟩ : Fin (3 * k)) ∉ U := by
              intro hmem
              have := hc ⟨j, hjk⟩ hmem
              have hneF : (⟨j, hjk⟩ : Fin (3 * k)) ≠ i := fun heq => hne (congrArg Fin.val heq)
              simp [hneF, hrm] at this
            have hsome : ρ (drvPos hk ori ⟨j, hjk⟩) = some (xPart ⟨j, hjk⟩) := by
              cases hopt : ρ (drvPos hk ori ⟨j, hjk⟩) with
              | none => exfalso; exact hjnotU (by simp [U, hopt])
              | some b => simp [xPart, hopt]
            have hraw : drFlip (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (xPart ⟨j, hjk⟩) ∈ (upS F)^[1] S := by
              apply z5 F S (by omega : 0 <= 1)
              change drFlip (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (xPart ⟨j, hjk⟩) ∈ S
              cases hxv : xPart ⟨j, hjk⟩ <;> exact ⟨drvPos hk ori ⟨j, hjk⟩, rfl, by simpa [drFlip, vRawDR, hxv] using hsome⟩
            have hCsub : ∀ C ∈ drEq (vRawDR (drvPos hk ori ⟨j, hjk⟩)) (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
              intro C hC; exact hcl_mem C (by simp [hjk, hrm, hC])
            simpa [fM, hjk, hrm] using drEq_up hCsub hraw
          · have hrmf : rowMask (H m) c ⟨j, hjk⟩ = false := Bool.eq_false_iff.mpr hrm
            have hCsub : ∀ C ∈ drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
              intro C hC; exact hcl_mem C (by simp [hjk, hrmf, hC])
            simpa [fM, hjk, hrmf] using drEq_up hCsub (z32 hk H S (le_refl 1))
        · have hCsub : ∀ C ∈ drEq z3 (up ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
            intro C hC; exact hcl_mem C (by simp [hjk, hC])
          simpa [fM, hjk] using drEq_up hCsub (z32 hk H S (le_refl 1))
      have hroot : drFlip (dn ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) false ∈
          (upS F)^[2 + dN] S := by
        apply z5 F S (by omega : 2 <= 2 + dN)
        change _ ∈ (upS F)^[1 + 1] S; rw [Function.iterate_succ_apply']
        have hCsub : ∀ C ∈ drEq z3
            (dn ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
          intro C hC; apply z37 hk H ori m
          dsimp only [z40]; rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hC))
        exact drEq_up hCsub (z32 hk H S (le_refl 1))
      have hi_pow : i.val < 2 ^ dN := lt_of_lt_of_le i.isLt hNle
      have hdn_leaf := z134 dN fM up dn hFup hFdn i.val 2 hleaf hroot dN (le_refl dN) i.val hi_pow
        (by simp) (by simp)
      have hidx_eq : hIdx dN (dN - dN) i.val = 2 ^ dN + i.val := by simp [hIdx]
      have hdn_at : drFlip (dn ⟨2 ^ dN + i.val, by change 2 ^ dN + i.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
          (z23 fM dN (2 ^ dN + i.val)) ∈ (upS F)^[2 + 2 * dN] S := by
        have h1 : (⟨hIdx dN (dN - dN) i.val, hIdx_lt (by omega) (by simpa using hi_pow)⟩ : Fin (2 ^ (dN + 1))) =
            ⟨2 ^ dN + i.val, by change 2 ^ dN + i.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx_eq
        rw [h1, hidx_eq, show 2 + dN + dN = 2 + 2 * dN by omega] at hdn_leaf
        exact hdn_leaf
      set v0 := z23 fM dN (2 ^ dN + i.val)
      have hw0 : vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨0, Nat.zero_lt_succ h'⟩ c v0 ∈
          (upS F)^[3 + 2 * dN] S := by
        rw [show 3 + 2 * dN = (2 + 2 * dN) + 1 by omega, Function.iterate_succ_apply']
        have hCl : imp1 (drFlip (dn ⟨2 ^ dN + i.val, by change 2 ^ dN + i.val < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) v0)
            (vWalsh ori m i ⟨0, Nat.zero_lt_succ h'⟩ c v0) ∈ F := by
          apply z96 hk H ori m
          dsimp only [z53]; rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
          apply List.mem_append_left
          rw [List.mem_flatMap]; refine ⟨c, List.mem_finRange c, ?_⟩
          simp only [hci, ↓reduceIte]
          cases hv0 : v0 <;> simp [drFlip, dn, dN, hv0]
        exact upS_imp1 hCl hdn_at
      have hwh := up_walsh_chain hk H ori m S i c s v0 (3 + 2 * dN) hw0 h' (le_refl h')
      rw [mixBits_full, z158] at hwh
      set bOut := xor v0 (dotBool h' c.val s.val)
      refine ⟨bOut, ?_, ?_⟩
      · intro b0 hb0
        have hnone : ρ (drvPos hk ori i) = none := (Finset.mem_filter.mp hiU).2
        rw [hnone] at hb0; cases hb0
      · rw [show 4 + 2 * dN + h' = (3 + 2 * dN + h') + 1 by omega, Function.iterate_succ_apply']
        have hCl : imp1 (vWalsh (k := k) (r := r) (h' := h') (R := R) ori m i ⟨h', Nat.lt_succ_self h'⟩ s bOut)
            (drFlip (drXDual ori m s i) bOut) ∈ F := by
          apply z20 hk H ori m s
          dsimp only [z12]; apply List.mem_append_left
          rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
          cases hbOut : bOut <;> simp [drFlip, hbOut]
        exact upS_imp1 hCl hwh
    · cases hopt : ρ (drvPos hk ori i) with
      | none => exfalso; exact hiU (by simp [U, hopt])
      | some b =>
        refine ⟨b, ?_, ?_⟩
        · intro b0 hb0; exact Option.some.inj hb0
        · have h1 : drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) b ∈ (upS F)^[1] S := by
            rw [Function.iterate_one]
            have hCl : imp1 (vRaw (drvPos hk ori i) b) (drFlip (drXDual ori m s i) b) ∈ F := by
              apply z20 hk H ori m s
              dsimp only [z12]; apply List.mem_append_left
              rw [List.mem_flatMap]; refine ⟨i, List.mem_finRange i, ?_⟩
              cases b <;> simp [drFlip]
            exact upS_imp1 hCl ⟨drvPos hk ori i, rfl, hopt⟩
          exact z5 F S (by omega : 1 <= 4 + 2 * dN + h') h1
  choose xCand hxCandρ hxCandUP using hcand
  have hsyn_ne : synOf (H m) xCand ≠ s := fun heq => hno ⟨xCand, hxCandρ, heq⟩
  have hex_q : ∃ q : Fin h', (synOf (H m) xCand).val.testBit q.val ≠ s.val.testBit q.val := by
    by_contra hall; push_neg at hall
    apply hsyn_ne; apply Fin.ext; apply Nat.eq_of_testBit_eq; intro q
    by_cases hqh : q < h'
    · exact hall ⟨q, hqh⟩
    · have h1 : (synOf (H m) xCand).val.testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le (synOf (H m) xCand).isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      have h2 : s.val.testBit q = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le s.isLt (Nat.pow_le_pow_right (by omega) (by omega)))
      rw [h1, h2]
  obtain ⟨q, hq_ne⟩ := hex_q
  have hq_bad : xorFin (fun j : Fin (3 * k) => H m q j && xCand j) = !(s.val.testBit q.val) := by
    rw [← synOf_testBit (H m) xCand q]
    cases h1 : (synOf (H m) xCand).val.testBit q.val <;> cases h2 : s.val.testBit q.val <;> simp_all
  set upP := drPar (k := k) (r := r) (h' := h') (R := R) ori m s q
  set fPar : ℕ -> Bool := fun j => if hj : j < 3 * k then H m q ⟨j, hj⟩ && xCand ⟨j, hj⟩ else false
  have hFup : ∀ C ∈ z14 dN upP, C ∈ F := by
    intro C hC; apply z20 hk H ori m s
    dsimp only [z12]; apply List.mem_append_right
    rw [List.mem_flatMap]; refine ⟨q, List.mem_finRange q, ?_⟩
    exact List.mem_append_left _ (List.mem_append_right _ hC)
  have hleaf : ∀ j (hj : j < 2 ^ dN), ¬ False ->
      drFlip (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩) (fPar j) ∈ (upS F)^[5 + 2 * dN + h'] S := by
    intro j hj _
    have hcl_mem : ∀ C ∈ (if hjk : j < 3 * k then
        if H m q ⟨j, hjk⟩ then
          drEq (drXDual ori m s ⟨j, hjk⟩) (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
        else drEq z3 (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
      else drEq z3 (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)), C ∈ F := by
      intro C hC; apply z20 hk H ori m s
      dsimp only [z12]; apply List.mem_append_right
      rw [List.mem_flatMap]; refine ⟨q, List.mem_finRange q, ?_⟩
      apply List.mem_append_left; apply List.mem_append_left
      rw [List.mem_flatMap]; exact ⟨⟨j, hj⟩, List.mem_finRange _, hC⟩
    rw [show 5 + 2 * dN + h' = (4 + 2 * dN + h') + 1 by omega, Function.iterate_succ_apply']
    by_cases hjk : j < 3 * k
    · by_cases hmq : H m q ⟨j, hjk⟩ = true
      · have hCsub : ∀ C ∈ drEq (drXDual ori m s ⟨j, hjk⟩) (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
          intro C hC; exact hcl_mem C (by simp [hjk, hmq, hC])
        simpa [fPar, hjk, hmq] using drEq_up hCsub (hxCandUP ⟨j, hjk⟩)
      · have hmqf : H m q ⟨j, hjk⟩ = false := Bool.eq_false_iff.mpr hmq
        have hCsub : ∀ C ∈ drEq z3 (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
          intro C hC; exact hcl_mem C (by simp [hjk, hmqf, hC])
        simpa [fPar, hjk, hmqf] using drEq_up hCsub (z32 hk H S (by omega : 1 <= 4 + 2 * dN + h'))
    · have hCsub : ∀ C ∈ drEq z3 (upP ⟨2 ^ dN + j, by change 2 ^ dN + j < 2 ^ (dN + 1); rw [pow_succ]; omega⟩), C ∈ F := by
        intro C hC; exact hcl_mem C (by simp [hjk, hC])
      simpa [fPar, hjk] using drEq_up hCsub (z32 hk H S (by omega : 1 <= 4 + 2 * dN + h'))
  have hroot_up := z55 dN fPar upP hFup (fun _ => False) (5 + 2 * dN + h') hleaf
    dN 0 (le_refl dN) (by simp) (fun _ _ _ => id)
  have hidx1 : hIdx dN dN 0 = 1 := by simp [hIdx]
  have hroot_val : heapUpVal xor false fPar dN 1 = !(s.val.testBit q.val) := by
    rw [z115 hNle (fun j => H m q j && xCand j), hq_bad]
  have hroot_at : drFlip (upP ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
      (!(s.val.testBit q.val)) ∈ (upS F)^[5 + 3 * dN + h'] S := by
    have h1 : (⟨hIdx dN dN 0, hIdx_lt (le_refl dN) (by simp)⟩ : Fin (2 ^ (dN + 1))) =
        ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx1
    rw [h1, hidx1, hroot_val, show 5 + 2 * dN + h' + dN = 5 + 3 * dN + h' by omega] at hroot_up
    exact hroot_up
  rw [show 6 + 3 * dN + h' = (5 + 3 * dN + h') + 1 by omega, Function.iterate_succ_apply']
  have hCl : imp1 (drFlip (upP ⟨1, by have := Nat.one_le_pow dN 2 (by omega); change 1 < 2 ^ (dN + 1); rw [pow_succ]; omega⟩)
      (!(s.val.testBit q.val))) (vExcl ori m s) ∈ F := by
    apply z20 hk H ori m s
    dsimp only [z12]; apply List.mem_append_right
    rw [List.mem_flatMap]; refine ⟨q, List.mem_finRange q, ?_⟩
    exact List.mem_append_right _ (by simp [upP, dN])
  exact upS_imp1 hCl hroot_at
private theorem up_leaf (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r))
    (S : Set (Lit (VarAll k r h' R))) (x : Fin (3 * k) -> Bool) (T0 : ℕ) (hT0 : 1 <= T0)
    (hxUP : ∀ i : Fin (3 * k),
      drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) (x i) ∈
        (upS (z7 hk H).toFinset)^[T0] S) :
    (∀ j : Fin k,
      drFlip (z91 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf ⟨0, Nat.zero_lt_succ r⟩ j 8)
        ((z13 hk r isCol (branchRev ori isCol) leaf
          (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx (z8 isCol) j))).1 j) ∈
        (upS (z7 hk H).toFinset)^[T0 + (6 * Nat.clog 2 k + 14) * (r + 1)] S) /\
    drFlip (z137 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf ⟨r, Nat.lt_succ_self r⟩ true)
      ((z13 hk r isCol (branchRev ori isCol) leaf
        (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx (z8 isCol) j))).2) ∈
      (upS (z7 hk H).toFinset)^[T0 + (6 * Nat.clog 2 k + 14) * (r + 1)] S := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set dk := Nat.clog 2 k
  set key : Fin k -> Bool := fun j => x (drvIdx ⟨0, by omega⟩ j)
  set drv : Fin k -> Bool := fun j => x (drvIdx (z8 isCol) j)
  set W := z91 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  set C := drLeafChi (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  set M := drLeafMix (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  set P := z137 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf
  have hkle : k <= 2 ^ dk := Nat.le_pow_clog (by omega) k
  have hmemL : ∀ D ∈ z9 (k := k) (r := r) (h' := h') (R := R) hk ori m s isCol leaf, D ∈ F :=
    z38 hk H ori m s isCol leaf
  have hkeyUP : ∀ (j : Fin k) (t : ℕ), T0 <= t ->
      drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s (drvIdx ⟨0, by omega⟩ j)) (key j) ∈ (upS F)^[t] S :=
    fun j t ht => z5 F S ht (hxUP (drvIdx ⟨0, by omega⟩ j))
  have hdrvUP : ∀ (j : Fin k) (t : ℕ), T0 <= t ->
      drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s (drvIdx (z8 isCol) j)) (drv j) ∈ (upS F)^[t] S :=
    fun j t ht => z5 F S ht (hxUP (drvIdx (z8 isCol) j))
  cases hrev : branchRev ori isCol
  ·
    have hcore : ∀ D ∈ (
      ((List.finRange k).flatMap fun j =>
        let kj : Fin k := ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩
        drXor (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj)) (drXDual ori m s (drvIdx (z8 isCol) j))
          (W ⟨0, Nat.zero_lt_succ r⟩ j 0)) ++
      ((List.finRange r).flatMap fun t =>
        let t0 : Fin (r + 1) := ⟨t.val, by omega⟩
        let t1 : Fin (r + 1) := ⟨t.val + 1, by omega⟩
        let δ := mixStride isCol
        (List.finRange k).flatMap fun j =>
          let j1 : Fin k := ⟨(j.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
          let j2 : Fin k := ⟨(j.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
          let jc1 : Fin k := ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩
          let jc2 : Fin k := ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩
          let kj : Fin k := ⟨(j.val + k - z16 isCol t.val % k) % k, Nat.mod_lt _ hk⟩
          let cb := constBit k (z10 isCol r t.val) j
          drXor (W t0 j 0) (W t0 j1 0) (W t0 j 1) ++
          drXor (W t0 j 1) (W t0 j2 0) (W t0 j 2) ++
          drAnd (drNot (W t0 jc1 2)) (W t0 jc2 2) (W t0 j 3) ++
          drXor (W t0 j 2) (W t0 j 3) (W t0 j 4) ++
          drXor (W t0 j 4) (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj))) (W t1 j 0)) ++
      ((List.finRange k).flatMap fun j => drEq (W ⟨r, Nat.lt_succ_self r⟩ j 0) (W ⟨0, Nat.zero_lt_succ r⟩ j 8)) ++
      drEq z26 (P ⟨r, Nat.lt_succ_self r⟩ true)), D ∈ F := by
      intro D hD; apply hmemL; dsimp only [z9]
      rw [hrev]; simp only [Bool.not_false, ↓reduceIte]
      exact List.mem_append_left _ (List.mem_append_left _ hD)
    set init : Fin k -> Bool := fun j => xor (rotB hk (initRot isCol) key j) (drv j)
    have hW0 : ∀ j : Fin k, drFlip (W ⟨0, Nat.zero_lt_succ r⟩ j 0) (init j) ∈ (upS F)^[T0 + 1] S := by
      intro j
      rw [Function.iterate_succ_apply']
      let kj : Fin k := ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩
      have hCsub : ∀ D ∈ drXor (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj))
          (drXDual ori m s (drvIdx (z8 isCol) j)) (W ⟨0, Nat.zero_lt_succ r⟩ j 0), D ∈ F := by
        intro D hD; apply hcore
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hD⟩
      exact drXor_up hCsub (hkeyUP kj T0 (le_refl T0)) (hdrvUP j T0 (le_refl T0))
    have hWr : ∀ (t : ℕ) (ht : t <= r) (j : Fin k),
        drFlip (W ⟨t, by omega⟩ j 0) (fwdIterB hk isCol r key init t j) ∈ (upS F)^[T0 + 1 + 5 * t] S := by
      intro t
      induction t with
      | zero => intro _ j; simpa [fwdIterB] using hW0 j
      | succ t ih =>
        intro ht j
        have hprev : ∀ i : Fin k,
            drFlip (W ⟨t, by omega⟩ i 0) (fwdIterB hk isCol r key init t i) ∈ (upS F)^[T0 + 1 + 5 * t] S :=
          ih (by omega)
        set st := fwdIterB hk isCol r key init t
        set δ := mixStride isCol
        set ta := T0 + 1 + 5 * t
        have hRndCl : ∀ (i : Fin k) D, D ∈ (
            let j1 : Fin k := ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
            let j2 : Fin k := ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
            let jc1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
            let jc2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
            let kj : Fin k := ⟨(i.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩
            let cb := constBit k (z10 isCol r t) i
            drXor (W ⟨t, by omega⟩ i 0) (W ⟨t, by omega⟩ j1 0) (W ⟨t, by omega⟩ i 1) ++
            drXor (W ⟨t, by omega⟩ i 1) (W ⟨t, by omega⟩ j2 0) (W ⟨t, by omega⟩ i 2) ++
            drAnd (drNot (W ⟨t, by omega⟩ jc1 2)) (W ⟨t, by omega⟩ jc2 2) (W ⟨t, by omega⟩ i 3) ++
            drXor (W ⟨t, by omega⟩ i 2) (W ⟨t, by omega⟩ i 3) (W ⟨t, by omega⟩ i 4) ++
            drXor (W ⟨t, by omega⟩ i 4) (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj)))
              (W ⟨t + 1, by omega⟩ i 0)) -> D ∈ F := by
          intro i D hD; apply hcore
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
          rw [List.mem_flatMap]; refine ⟨⟨t, by omega⟩, List.mem_finRange _, ?_⟩
          rw [List.mem_flatMap]; exact ⟨i, List.mem_finRange i, hD⟩
        have hS1 : ∀ i : Fin k,
            drFlip (W ⟨t, by omega⟩ i 1) (xor (st i) (rotB hk δ st i)) ∈ (upS F)^[ta + 1] S := by
          intro i; rw [Function.iterate_succ_apply']
          have hCsub : ∀ D ∈ drXor (W ⟨t, by omega⟩ i 0)
              (W ⟨t, by omega⟩ ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩ 0) (W ⟨t, by omega⟩ i 1), D ∈ F :=
            fun D hD => hRndCl i D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hD))))
          exact drXor_up hCsub (hprev i) (hprev _)
        have hS2 : ∀ i : Fin k,
            drFlip (W ⟨t, by omega⟩ i 2) (mixB hk δ st i) ∈ (upS F)^[ta + 2] S := by
          intro i; rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
          have hCsub : ∀ D ∈ drXor (W ⟨t, by omega⟩ i 1)
              (W ⟨t, by omega⟩ ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩ 0) (W ⟨t, by omega⟩ i 2), D ∈ F :=
            fun D hD => hRndCl i D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hD))))
          exact drXor_up hCsub (hS1 i) (z5 F S (by omega : ta <= ta + 1) (hprev _))
        have hS3 : drFlip (W ⟨t, by omega⟩ j 3)
            (!(mixB hk δ st ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩) && mixB hk δ st ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩) ∈
            (upS F)^[ta + 3] S := by
          rw [show ta + 3 = (ta + 2) + 1 by omega, Function.iterate_succ_apply']
          have hCsub : ∀ D ∈ drAnd (drNot (W ⟨t, by omega⟩ ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ 2))
              (W ⟨t, by omega⟩ ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩ 2) (W ⟨t, by omega⟩ j 3), D ∈ F :=
            fun D hD => hRndCl j D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hD)))
          have hnot : drFlip (drNot (W ⟨t, by omega⟩ ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩ 2))
              (!(mixB hk δ st ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩)) ∈ (upS F)^[ta + 2] S := by
            rw [drFlip_not]; exact hS2 _
          exact drAnd_up hCsub hnot (hS2 _)
        have hS4 : drFlip (W ⟨t, by omega⟩ j 4) (stepB hk (mixB hk δ st) j) ∈ (upS F)^[ta + 4] S := by
          rw [show ta + 4 = (ta + 3) + 1 by omega, Function.iterate_succ_apply']
          have hCsub : ∀ D ∈ drXor (W ⟨t, by omega⟩ j 2) (W ⟨t, by omega⟩ j 3) (W ⟨t, by omega⟩ j 4), D ∈ F :=
            fun D hD => hRndCl j D (List.mem_append_left _ (List.mem_append_right _ hD))
          exact drXor_up hCsub (z5 F S (by omega : ta + 2 <= ta + 3) (hS2 j)) hS3
        rw [show T0 + 1 + 5 * (t + 1) = (ta + 4) + 1 by omega, Function.iterate_succ_apply']
        let kj : Fin k := ⟨(j.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩
        let cb := constBit k (z10 isCol r t) j
        have hCsub : ∀ D ∈ drXor (W ⟨t, by omega⟩ j 4)
            (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj))) (W ⟨t + 1, by omega⟩ j 0), D ∈ F :=
          fun D hD => hRndCl j D (List.mem_append_right _ hD)
        have hkc : drFlip (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj)))
            (xor cb (key kj)) ∈ (upS F)^[ta + 4] S := by
          rw [z101]; exact hkeyUP kj (ta + 4) (by omega)
        have hstep := drXor_up hCsub hS4 hkc
        have hEqVal : xor (stepB hk (mixB hk δ st) j) (xor cb (key kj)) =
            fwdIterB hk isCol r key init (t + 1) j := by
          dsimp only [fwdIterB, fwdRoundB, rotB, kj, cb, δ]
          cases stepB hk (mixB hk (mixStride isCol) st) j <;>
            cases key ⟨(j.val + k - z16 isCol t % k) % k, Nat.mod_lt _ hk⟩ <;>
            cases constBit k (z10 isCol r t) j <;> rfl
        rwa [hEqVal] at hstep
    dsimp only [z13]; rw [if_neg (by simp)]
    constructor
    · intro j
      apply z5 F S (by nlinarith : T0 + 1 + 5 * r + 1 <= T0 + (6 * dk + 14) * (r + 1))
      rw [Function.iterate_succ_apply']
      have hCsub : ∀ D ∈ drEq (W ⟨r, Nat.lt_succ_self r⟩ j 0) (W ⟨0, Nat.zero_lt_succ r⟩ j 8), D ∈ F := by
        intro D hD; apply hcore
        apply List.mem_append_left; apply List.mem_append_right
        rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hD⟩
      exact drEq_up hCsub (hWr r (le_refl r) j)
    · apply z5 F S (by nlinarith : T0 + 1 <= T0 + (6 * dk + 14) * (r + 1))
      rw [Function.iterate_succ_apply']
      have hCsub : ∀ D ∈ drEq z26 (P ⟨r, Nat.lt_succ_self r⟩ true), D ∈ F :=
        fun D hD => hcore D (List.mem_append_right _ hD)
      exact drEq_up hCsub (z78 hk H S hT0)
  ·
    have hW0 : ∀ j : Fin k,
        drFlip (W ⟨0, Nat.zero_lt_succ r⟩ j 0) ((z11 hk isCol r key drv leaf.val 0).1 j) ∈ (upS F)^[T0 + 1] S := by
      intro j; rw [Function.iterate_succ_apply']
      have hCsub : ∀ D ∈ drEq (drXDual ori m s (drvIdx (z8 isCol) j)) (W ⟨0, Nat.zero_lt_succ r⟩ j 0), D ∈ F := by
        intro D hD; apply hmemL; dsimp only [z9]
        rw [hrev]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        apply List.mem_append_left; apply List.mem_append_left
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hD⟩
      exact drEq_up hCsub (hdrvUP j T0 (le_refl T0))
    have hP0 : drFlip (P ⟨0, Nat.zero_lt_succ r⟩ true) ((z11 hk isCol r key drv leaf.val 0).2) ∈ (upS F)^[T0 + 1] S := by
      rw [Function.iterate_succ_apply']
      have hCsub : ∀ D ∈ drEq z26 (P ⟨0, Nat.zero_lt_succ r⟩ true), D ∈ F := by
        intro D hD; apply hmemL; dsimp only [z9]
        rw [hrev]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        apply List.mem_append_left; apply List.mem_append_left
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
        exact hD
      exact drEq_up hCsub (z78 hk H S hT0)
    set Sstep := 6 * dk + 12
    have hInv : ∀ (t : ℕ) (ht : t <= r),
        (∀ j : Fin k, drFlip (W ⟨t, by omega⟩ j 0) ((z11 hk isCol r key drv leaf.val t).1 j) ∈
          (upS F)^[T0 + 1 + Sstep * t] S) /\
        drFlip (P ⟨t, by omega⟩ true) ((z11 hk isCol r key drv leaf.val t).2) ∈
          (upS F)^[T0 + 1 + Sstep * t] S := by
      intro t
      induction t with
      | zero => intro _; simpa using ⟨hW0, hP0⟩
      | succ t ih =>
        intro ht
        obtain ⟨hprevW, hprevP⟩ := ih (by omega)
        set ta := T0 + 1 + Sstep * t
        set st := (z11 hk isCol r key drv leaf.val t).1
        set acc := (z11 hk isCol r key drv leaf.val t).2
        set idx := r - 1 - t
        set δ := mixStride isCol
        set u : Fin k -> Bool := fun j =>
          xor (xor (st j) (rotB hk (z16 isCol idx) key j)) (constBit k (z10 isCol r idx) j)
        set w : Fin k -> Bool := invChiB hk u
        set t0F : Fin (r + 1) := ⟨t, by omega⟩
        set t1F : Fin (r + 1) := ⟨t + 1, by omega⟩
        set tR : Fin r := ⟨t, by omega⟩
        set upA : Fin (2 ^ (dk + 1)) -> DualLit (VarAll k r h' R) × DualLit (VarAll k r h' R) := fun v => (C tR 0 v, C tR 1 v)
        set prA : Fin (2 ^ (dk + 1)) -> DualLit (VarAll k r h' R) × DualLit (VarAll k r h' R) := fun v => (C tR 2 v, C tR 3 v)
        set sfA : Fin (2 ^ (dk + 1)) -> DualLit (VarAll k r h' R) × DualLit (VarAll k r h' R) := fun v => (C tR 4 v, C tR 5 v)
        set tuA := C tR 6
        set tpA := C tR 7
        set tsA := C tR 8
        set rootK : Fin (2 ^ (dk + 1)) := ⟨1, by have := Nat.one_le_pow dk 2 (by omega); change 1 < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
        have hInRound : ∀ D, D ∈ (
            ((List.finRange k).flatMap fun j =>
              let kj : Fin k := ⟨(j.val + k - z16 isCol idx % k) % k, Nat.mod_lt _ hk⟩
              let cb := constBit k (z10 isCol r idx) j
              drXor (W t0F j 0) (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj))) (W t0F j 1)) ++
            ((List.finRange (2 ^ dk)).flatMap fun p =>
              let v : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by change 2 ^ dk + p.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
              if hp : p.val < k then
                let i0 := z21 k p.val hk
                let i1 : Fin k := ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩
                drEq (drNot (W t0F i1 1)) (upA v).1 ++ drEq (W t0F i0 1) (upA v).2
              else
                drEq z26 (upA v).1 ++ drEq z3 (upA v).2) ++
            (drEq z26 (prA rootK).1 ++ drEq z3 (prA rootK).2 ++
             drEq z26 (sfA rootK).1 ++ drEq z3 (sfA rootK).2) ++
            z39 dk upA tuA ++
            z28 dk upA prA tpA ++
            z36 dk upA sfA tsA ++
            ((List.finRange k).flatMap fun (p : Fin k) =>
              have hp_pow : p.val < 2 ^ dk := lt_of_lt_of_le p.isLt hkle
              let v : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by change 2 ^ dk + p.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
              let i0 := z21 k p.val hk
              let i1 : Fin k := ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩
              drAffComp (drNot (W t0F i1 1), W t0F i0 1) (sfA v) (W t0F p 2, W t0F p 3) (W t0F p 4) ++
              drAnd (W t0F p 2) (prA v).2 (W t0F p 5) ++
              drXor (W t0F p 3) (W t0F p 5) (W t0F p 6))) -> D ∈ F := by
          intro D hD; apply hmemL; dsimp only [z9]
          rw [hrev]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_left; apply List.mem_append_right
          rw [List.mem_flatMap]; refine ⟨tR, List.mem_finRange tR, ?_⟩
          exact List.mem_append_left _ hD
        have huUP : ∀ j : Fin k, drFlip (W t0F j 1) (u j) ∈ (upS F)^[ta + 1] S := by
          intro j; rw [Function.iterate_succ_apply']
          let kj : Fin k := ⟨(j.val + k - z16 isCol idx % k) % k, Nat.mod_lt _ hk⟩
          let cb := constBit k (z10 isCol r idx) j
          have hCsub : ∀ D ∈ drXor (W t0F j 0) (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj))) (W t0F j 1), D ∈ F := by
            intro D hD; apply hInRound
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hD⟩
          have hkc : drFlip (z34 cb (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj))) (xor cb (key kj)) ∈ (upS F)^[ta] S := by
            rw [z101]; exact hkeyUP kj ta (by omega)
          have hres := drXor_up hCsub (hprevW j) hkc
          have hEq : xor (st j) (xor cb (key kj)) = u j := by
            dsimp only [u, rotB, kj, cb]
            cases st j <;> cases key ⟨(j.val + k - z16 isCol idx % k) % k, Nat.mod_lt _ hk⟩ <;>
              cases constBit k (z10 isCol r idx) j <;> rfl
          rwa [hEq] at hres
        set fChi : ℕ -> Bool × Bool := fun q => if hq : q < k then chiMapAt hk u ⟨q, hq⟩ else affId
        have hchiLeaf : ∀ p (hp : p < 2 ^ dk),
            drFlip (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).1 (fChi p).1 ∈ (upS F)^[ta + 2] S /\
            drFlip (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).2 (fChi p).2 ∈ (upS F)^[ta + 2] S := by
          intro p hp
          have hmemP : ∀ D ∈ (if hpk : p < k then
              let i0 := z21 k p hk
              let i1 : Fin k := ⟨(i0.val + 1) % k, Nat.mod_lt _ hk⟩
              drEq (drNot (W t0F i1 1)) (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).1 ++
              drEq (W t0F i0 1) (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).2
            else
              drEq z26 (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).1 ++
              drEq z3 (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).2), D ∈ F := by
            intro D hD; apply hInRound
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
            apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
            rw [List.mem_flatMap]; exact ⟨⟨p, hp⟩, List.mem_finRange _, hD⟩
          rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
          by_cases hpk : p < k
          · constructor
            · have hCsub : ∀ D ∈ drEq (drNot (W t0F ⟨((z21 k p hk).val + 1) % k, Nat.mod_lt _ hk⟩ 1))
                  (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).1, D ∈ F :=
                fun D hD => hmemP D (by simp [hpk, hD])
              have hnot : drFlip (drNot (W t0F ⟨((z21 k p hk).val + 1) % k, Nat.mod_lt _ hk⟩ 1))
                  (!(u ⟨((z21 k p hk).val + 1) % k, Nat.mod_lt _ hk⟩)) ∈ (upS F)^[ta + 1] S := by
                rw [drFlip_not]; exact huUP _
              simpa [fChi, hpk, chiMapAt] using drEq_up hCsub hnot
            · have hCsub : ∀ D ∈ drEq (W t0F (z21 k p hk) 1)
                  (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).2, D ∈ F :=
                fun D hD => hmemP D (by simp [hpk, hD])
              simpa [fChi, hpk, chiMapAt] using drEq_up hCsub (huUP _)
          · constructor
            · have hCsub : ∀ D ∈ drEq z26 (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).1, D ∈ F :=
                fun D hD => hmemP D (by simp [hpk, hD])
              simpa [fChi, hpk, affId] using drEq_up hCsub (z78 hk H S (by omega : 1 <= ta + 1))
            · have hCsub : ∀ D ∈ drEq z3 (upA ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).2, D ∈ F :=
                fun D hD => hmemP D (by simp [hpk, hD])
              simpa [fChi, hpk, affId] using drEq_up hCsub (z32 hk H S (by omega : 1 <= ta + 1))
        have hchiRootMem : ∀ D ∈ (drEq z26 (prA rootK).1 ++ drEq z3 (prA rootK).2 ++
            drEq z26 (sfA rootK).1 ++ drEq z3 (sfA rootK).2), D ∈ F := by
          intro D hD; apply hInRound
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_left; exact List.mem_append_right _ hD
        have hFaffUp : ∀ D ∈ z39 dk upA tuA, D ∈ F := fun D hD =>
          hInRound D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hD))))
        have hFaffPr : ∀ D ∈ z28 dk upA prA tpA, D ∈ F := fun D hD =>
          hInRound D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hD)))
        have hFaffSf : ∀ D ∈ z36 dk upA sfA tsA, D ∈ F := fun D hD =>
          hInRound D (List.mem_append_left _ (List.mem_append_right _ hD))
        have hprRoot : drFlip (prA rootK).1 true ∈ (upS F)^[ta + 2 + 2 * dk] S /\
            drFlip (prA rootK).2 false ∈ (upS F)^[ta + 2 + 2 * dk] S := by
          constructor
          · apply z5 F S (by omega : ta + 2 <= ta + 2 + 2 * dk)
            rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
            exact drEq_up (fun D hD => hchiRootMem D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hD))))
              (z78 hk H S (by omega))
          · apply z5 F S (by omega : ta + 2 <= ta + 2 + 2 * dk)
            rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
            exact drEq_up (fun D hD => hchiRootMem D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hD))))
              (z32 hk H S (by omega))
        have hsfRoot : drFlip (sfA rootK).1 true ∈ (upS F)^[ta + 2 + 2 * dk] S /\
            drFlip (sfA rootK).2 false ∈ (upS F)^[ta + 2 + 2 * dk] S := by
          constructor
          · apply z5 F S (by omega : ta + 2 <= ta + 2 + 2 * dk)
            rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
            exact drEq_up (fun D hD => hchiRootMem D (List.mem_append_left _ (List.mem_append_right _ hD)))
              (z78 hk H S (by omega))
          · apply z5 F S (by omega : ta + 2 <= ta + 2 + 2 * dk)
            rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
            exact drEq_up (fun D hD => hchiRootMem D (List.mem_append_right _ hD))
              (z32 hk H S (by omega))
        have hwUP : ∀ i : Fin k, drFlip (W t0F (z19 k hk i) 6) (w i) ∈ (upS F)^[ta + 4 * dk + 6] S := by
          intro i
          set p := z19 k hk i
          have hp_pow : p.val < 2 ^ dk := lt_of_lt_of_le p.isLt hkle
          have hidx_eq : hIdx dk (dk - dk) p.val = 2 ^ dk + p.val := by simp [hIdx]
          have hfin_eq : (⟨hIdx dk (dk - dk) p.val, hIdx_lt (by omega) (by simpa using hp_pow)⟩ : Fin (2 ^ (dk + 1))) =
              ⟨2 ^ dk + p.val, by change 2 ^ dk + p.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx_eq
          have hpr_p := z165 dk fChi upA prA tuA tpA hFaffUp hFaffPr (ta + 2) hchiLeaf hprRoot dk (le_refl dk) p.val hp_pow
          have hsf_p := heapAffSuf_up dk fChi upA sfA tuA tsA hFaffUp hFaffSf (ta + 2) hchiLeaf hsfRoot dk (le_refl dk) p.val hp_pow
          rw [hfin_eq, hidx_eq, show ta + 2 + 2 * dk + 2 * dk = ta + 4 * dk + 2 by omega] at hpr_p hsf_p
          have hOutMem : ∀ D ∈ (
              drAffComp (drNot (W t0F ⟨((z21 k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩ 1),
                W t0F (z21 k p.val hk) 1) (sfA ⟨2 ^ dk + p.val, by change 2 ^ dk + p.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)
                (W t0F p 2, W t0F p 3) (W t0F p 4) ++
              drAnd (W t0F p 2) (prA ⟨2 ^ dk + p.val, by change 2 ^ dk + p.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩).2 (W t0F p 5) ++
              drXor (W t0F p 3) (W t0F p 5) (W t0F p 6)), D ∈ F := by
            intro D hD; apply hInRound; apply List.mem_append_right
            rw [List.mem_flatMap]; exact ⟨p, List.mem_finRange p, hD⟩
          have hu1_at : drFlip (drNot (W t0F ⟨((z21 k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩ 1))
              (chiMapAt hk u p).1 ∈ (upS F)^[ta + 4 * dk + 2] S := by
            dsimp only [chiMapAt]; rw [drFlip_not]; exact z5 F S (by omega : ta + 1 <= ta + 4 * dk + 2) (huUP _)
          have hu2_at : drFlip (W t0F (z21 k p.val hk) 1) (chiMapAt hk u p).2 ∈ (upS F)^[ta + 4 * dk + 2] S :=
            z5 F S (by omega : ta + 1 <= ta + 4 * dk + 2) (huUP _)
          have hfullSuf : drFlip (W t0F p 2) (affComp (chiMapAt hk u p) (z33 affComp affId fChi dk (2 ^ dk + p.val))).1 ∈
                (upS F)^[ta + 4 * dk + 4] S /\
              drFlip (W t0F p 3) (affComp (chiMapAt hk u p) (z33 affComp affId fChi dk (2 ^ dk + p.val))).2 ∈
                (upS F)^[ta + 4 * dk + 4] S := by
            rw [show ta + 4 * dk + 4 = 2 + (ta + 4 * dk + 2) by omega, Function.iterate_add_apply]
            exact z162 (fun D hD => hOutMem D (List.mem_append_left _ (List.mem_append_left _ hD)))
              hu1_at hu2_at hsf_p.1 hsf_p.2
          have h5 : drFlip (W t0F p 5)
              ((affComp (chiMapAt hk u p) (z33 affComp affId fChi dk (2 ^ dk + p.val))).1 &&
                (z17 affComp affId fChi dk (2 ^ dk + p.val)).2) ∈ (upS F)^[ta + 4 * dk + 5] S := by
            rw [show ta + 4 * dk + 5 = (ta + 4 * dk + 4) + 1 by omega, Function.iterate_succ_apply']
            exact drAnd_up (fun D hD => hOutMem D (List.mem_append_left _ (List.mem_append_right _ hD)))
              hfullSuf.1 (z5 F S (by omega : ta + 4 * dk + 2 <= ta + 4 * dk + 4) hpr_p.2)
          have h6 : drFlip (W t0F p 6)
              (xor (affComp (chiMapAt hk u p) (z33 affComp affId fChi dk (2 ^ dk + p.val))).2
                ((affComp (chiMapAt hk u p) (z33 affComp affId fChi dk (2 ^ dk + p.val))).1 &&
                  (z17 affComp affId fChi dk (2 ^ dk + p.val)).2)) ∈ (upS F)^[ta + 4 * dk + 6] S := by
            rw [show ta + 4 * dk + 6 = (ta + 4 * dk + 5) + 1 by omega, Function.iterate_succ_apply']
            exact drXor_up (fun D hD => hOutMem D (List.mem_append_right _ hD))
              (z5 F S (by omega : ta + 4 * dk + 4 <= ta + 4 * dk + 5) hfullSuf.2) h5
          have hchi := z142 hk u p
          dsimp only at hchi
          rw [hchi] at h6; exact h6
        have hMixMem : ∀ D, D ∈ (
            let wBit : Fin k -> DualLit (VarAll k r h' R) := fun i => W t0F (z19 k hk i) 6
            if k % 3 = 0 then
              let m3 := k / 3
              let b0 := leaf.val.testBit (2 * idx)
              let b1 := leaf.val.testBit (2 * idx + 1)
              let treeCl := (List.finRange 3).flatMap fun rc =>
                let upM := M tR rc false
                let prM := M tR rc true
                let lfCl := (List.finRange (2 ^ dk)).flatMap fun q =>
                  let v : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + q.val, by change 2 ^ dk + q.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
                  if q.val < m3 then
                    drXor (wBit (sIdx hk δ (3 * q.val + rc.val + 1)))
                      (wBit (sIdx hk δ (3 * q.val + rc.val + 2))) (upM v)
                  else
                    drEq z3 (upM v)
                lfCl ++ drEq z3 (prM rootK) ++
                z14 dk upM ++ z18 dk upM prM
              let outMixCl := (List.finRange k).flatMap fun (i : Fin k) =>
                let pv := (sInv hk δ i).val
                let rc : Fin 3 := ⟨pv % 3, Nat.mod_lt _ (by omega)⟩
                let qv := pv / 3
                have hq_pow : qv < 2 ^ dk := lt_of_lt_of_le (by have := (sInv hk δ i).isLt; omega) hkle
                let v : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + qv, by change 2 ^ dk + qv < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
                let prefW := M tR rc true v
                if rc.val = 0 then
                  drEq (z34 b0 prefW) (W t1F i 0)
                else if rc.val = 1 then
                  drEq (z34 b1 prefW) (W t1F i 0)
                else
                  drXor (z34 (xor b0 b1) (wBit (sIdx hk δ 1))) prefW (W t1F i 0)
              let stepWrapCl :=
                drAnd (drNot (M tR 0 false rootK)) (drNot (M tR 1 false rootK)) (P t0F false) ++
                drAnd (P t0F true) (P t0F false) (P t1F true)
              treeCl ++ outMixCl ++ stepWrapCl
            else if k < 5 then
              ((List.finRange k).flatMap fun i => drEq (wBit i) (W t1F i 0)) ++
              (drEq z26 (P t0F false) ++ drAnd (P t0F true) (P t0F false) (P t1F true))
            else
              let upM := M tR 0 false
              let prM := M tR 0 true
              let lfCl := (List.finRange (2 ^ dk)).flatMap fun p =>
                let v : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + p.val, by change 2 ^ dk + p.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
                if p.val < k then
                  let a1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
                  let a2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
                  drXor (wBit a1) (wBit a2) (upM v)
                else
                  drEq z3 (upM v)
              let pPos := inv3Pos k % k
              let pNeg := (k - pPos) % k
              have hpPos_lt : pPos < 2 ^ dk := lt_of_lt_of_le (Nat.mod_lt _ hk) hkle
              have hpNeg_lt : pNeg < 2 ^ dk := lt_of_lt_of_le (Nat.mod_lt _ hk) hkle
              let uPos : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + pPos, by rw [pow_succ]; omega⟩
              let uNeg : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + pNeg, by rw [pow_succ]; omega⟩
              let j0 : Fin k := ⟨0, hk⟩
              let j1 : Fin k := ⟨1 % k, Nat.mod_lt _ hk⟩
              let x0Cl :=
                drXor (wBit j0) (prM uPos) (W t0F j0 7) ++
                drXor (W t0F j0 7) (prM uNeg) (W t0F j1 7)
              let outMixCl := (List.finRange k).flatMap fun (i : Fin k) =>
                let mv := (m3dInv k δ hk i).val
                have hmv : mv < 2 ^ dk := lt_of_lt_of_le (m3dInv k δ hk i).isLt hkle
                let uM : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + mv, by rw [pow_succ]; omega⟩
                drXor (W t0F j1 7) (prM uM) (W t1F i 0)
              let stepWrapCl :=
                drEq z26 (P t0F false) ++
                drAnd (P t0F true) (P t0F false) (P t1F true)
              lfCl ++ drEq z3 (prM rootK) ++
                z14 dk upM ++ z18 dk upM prM ++
                x0Cl ++ outMixCl ++ stepWrapCl) -> D ∈ F := by
          intro D hD; apply hmemL; dsimp only [z9]
          rw [hrev]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          apply List.mem_append_left; apply List.mem_append_left
          apply List.mem_append_left; apply List.mem_append_right
          rw [List.mem_flatMap]; refine ⟨tR, List.mem_finRange tR, ?_⟩
          exact List.mem_append_right _ hD
        have hstep_eq : T0 + 1 + Sstep * (t + 1) = ta + 6 * dk + 12 := by dsimp [ta, Sstep]; ring
        by_cases hk3 : k % 3 = 0
        ·
          set b0 := leaf.val.testBit (2 * idx)
          set b1 := leaf.val.testBit (2 * idx + 1)
          have htree : ∀ rc : Fin 3,
              (∀ q (hq : q < k / 3),
                drFlip (M tR rc true ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩) (singPref hk δ w rc.val q) ∈
                  (upS F)^[ta + 6 * dk + 7] S) /\
              drFlip (M tR rc false rootK) (singPref hk δ w rc.val (k / 3)) ∈ (upS F)^[ta + 5 * dk + 7] S := by
            intro rc
            set upM := M tR rc false
            set prM := M tR rc true
            set fM : ℕ -> Bool := fun j => if j < k / 3 then singDiff hk δ w rc.val j else false
            have hInTree : ∀ D ∈ (
                ((List.finRange (2 ^ dk)).flatMap fun q =>
                  let v : Fin (2 ^ (dk + 1)) := ⟨2 ^ dk + q.val, by change 2 ^ dk + q.val < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
                  if q.val < k / 3 then
                    drXor (W t0F (z19 k hk (sIdx hk δ (3 * q.val + rc.val + 1))) 6)
                      (W t0F (z19 k hk (sIdx hk δ (3 * q.val + rc.val + 2))) 6) (upM v)
                  else drEq z3 (upM v)) ++
                drEq z3 (prM rootK) ++
                z14 dk upM ++ z18 dk upM prM), D ∈ F := by
              intro D hD; apply hMixMem; simp only [hk3, ↓reduceIte]
              apply List.mem_append_left; apply List.mem_append_left
              rw [List.mem_flatMap]; exact ⟨rc, List.mem_finRange rc, hD⟩
            have hlf : ∀ q (hq : q < 2 ^ dk),
                drFlip (upM ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩) (fM q) ∈ (upS F)^[ta + 4 * dk + 7] S := by
              intro q hq
              rw [show ta + 4 * dk + 7 = (ta + 4 * dk + 6) + 1 by omega, Function.iterate_succ_apply']
              have hqMem : ∀ D ∈ (if q < k / 3 then
                  drXor (W t0F (z19 k hk (sIdx hk δ (3 * q + rc.val + 1))) 6)
                    (W t0F (z19 k hk (sIdx hk δ (3 * q + rc.val + 2))) 6) (upM ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)
                else drEq z3 (upM ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)), D ∈ F := by
                intro D hD; apply hInTree
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                rw [List.mem_flatMap]; exact ⟨⟨q, hq⟩, List.mem_finRange _, hD⟩
              by_cases hq3 : q < k / 3
              · have hCsub : ∀ D ∈ drXor (W t0F (z19 k hk (sIdx hk δ (3 * q + rc.val + 1))) 6)
                    (W t0F (z19 k hk (sIdx hk δ (3 * q + rc.val + 2))) 6)
                    (upM ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩), D ∈ F :=
                  fun D hD => hqMem D (by simp [hq3, hD])
                simpa [fM, hq3, singDiff] using drXor_up hCsub (hwUP _) (hwUP _)
              · have hCsub : ∀ D ∈ drEq z3 (upM ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩), D ∈ F :=
                  fun D hD => hqMem D (by simp [hq3, hD])
                simpa [fM, hq3] using drEq_up hCsub (z32 hk H S (by omega : 1 <= ta + 4 * dk + 6))
            have hFup : ∀ D ∈ z14 dk upM, D ∈ F := fun D hD =>
              hInTree D (List.mem_append_left _ (List.mem_append_right _ hD))
            have hFpr : ∀ D ∈ z18 dk upM prM, D ∈ F := fun D hD =>
              hInTree D (List.mem_append_right _ hD)
            have hprRoot : drFlip (prM rootK) false ∈ (upS F)^[ta + 4 * dk + 7 + dk] S := by
              apply z5 F S (by omega : ta + 4 * dk + 7 <= ta + 4 * dk + 7 + dk)
              rw [show ta + 4 * dk + 7 = (ta + 4 * dk + 6) + 1 by omega, Function.iterate_succ_apply']
              exact drEq_up (fun D hD => hInTree D (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hD))))
                (z32 hk H S (by omega))
            constructor
            · intro q hq
              have hq2 : q < 2 ^ dk := lt_of_lt_of_le (lt_of_lt_of_le hq (Nat.div_le_self k 3)) hkle
              have hpr := z133 dk fM upM prM hFup hFpr (ta + 4 * dk + 7) hlf hprRoot dk (le_refl dk) q hq2
              have hidx_eq : hIdx dk (dk - dk) q = 2 ^ dk + q := by simp [hIdx]
              have hfin_eq : (⟨hIdx dk (dk - dk) q, hIdx_lt (by omega) (by simpa using hq2)⟩ : Fin (2 ^ (dk + 1))) =
                  ⟨2 ^ dk + q, by change 2 ^ dk + q < 2 ^ (dk + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx_eq
              rw [hfin_eq, hidx_eq, show ta + 4 * dk + 7 + dk + dk = ta + 6 * dk + 7 by omega] at hpr
              have hsp := (z93 hk δ w rc.val q (by omega)).1 hq
              rwa [hsp] at hpr
            · have hup := z55 dk fM upM hFup (fun _ => False) (ta + 4 * dk + 7)
                (fun j hj _ => hlf j hj) dk 0 (le_refl dk) (by simp) (fun _ _ _ => id)
              have hidx1 : hIdx dk dk 0 = 1 := by simp [hIdx]
              have hfin1 : (⟨hIdx dk dk 0, hIdx_lt (le_refl dk) (by simp)⟩ : Fin (2 ^ (dk + 1))) = rootK :=
                Fin.ext hidx1
              rw [hfin1, hidx1, show ta + 4 * dk + 7 + dk = ta + 5 * dk + 7 by omega] at hup
              have hsp := (z93 hk δ w rc.val 0 (by omega)).2
              rwa [hsp] at hup
          rw [hstep_eq]
          constructor
          · intro i
            apply z5 F S (by omega : ta + 6 * dk + 8 <= ta + 6 * dk + 12)
            rw [show ta + 6 * dk + 8 = (ta + 6 * dk + 7) + 1 by omega, Function.iterate_succ_apply']
            set pv := (sInv hk δ i).val
            set rc : Fin 3 := ⟨pv % 3, Nat.mod_lt _ (by omega)⟩
            set qv := pv / 3
            have hqv3 : qv < k / 3 := by have := (sInv hk δ i).isLt; omega
            have hq_pow : qv < 2 ^ dk := lt_of_lt_of_le (by have := (sInv hk δ i).isLt; omega) hkle
            set prefW := M tR rc true ⟨2 ^ dk + qv, by change 2 ^ dk + qv < 2 ^ (dk + 1); rw [pow_succ]; omega⟩
            have hprefUP := (htree rc).1 qv hqv3
            have hOutI : ∀ D ∈ (
                if rc.val = 0 then drEq (z34 b0 prefW) (W t1F i 0)
                else if rc.val = 1 then drEq (z34 b1 prefW) (W t1F i 0)
                else drXor (z34 (xor b0 b1) (W t0F (z19 k hk (sIdx hk δ 1)) 6)) prefW (W t1F i 0)), D ∈ F := by
              intro D hD; apply hMixMem; simp only [hk3, ↓reduceIte]
              apply List.mem_append_left; apply List.mem_append_right
              rw [List.mem_flatMap]; exact ⟨i, List.mem_finRange i, hD⟩
            have hresVal : (z11 hk isCol r key drv leaf.val (t + 1)).1 i =
                z87 hk δ w b0 b1 i := by
              simp [z11, revRoundB, hk3, st, idx, δ, u, w, b0, b1]
            rw [hresVal]; dsimp only [z87, z4]
            by_cases hrc0 : rc.val = 0
            · have hCsub : ∀ D ∈ drEq (z34 b0 prefW) (W t1F i 0), D ∈ F :=
                fun D hD => hOutI D (by simp [hrc0, hD])
              have hx : drFlip (z34 b0 prefW) (xor b0 (singPref hk δ w rc.val qv)) ∈ (upS F)^[ta + 6 * dk + 7] S := by
                rw [z101]; exact hprefUP
              have hd := drEq_up hCsub hx
              have hEqV : xor b0 (singPref hk δ w rc.val qv) =
                  xor (if (sInv hk δ i).val % 3 = 0 then b0 else if (sInv hk δ i).val % 3 = 1 then b1 else xor (xor (w (sIdx hk δ 1)) b0) b1)
                    (singPref hk δ w ((sInv hk δ i).val % 3) ((sInv hk δ i).val / 3)) := by
                have h0 : (sInv hk δ i).val % 3 = 0 := hrc0
                simp only [pv, rc, qv, h0, ↓reduceIte]
              rwa [hEqV] at hd
            · by_cases hrc1 : rc.val = 1
              · have hCsub : ∀ D ∈ drEq (z34 b1 prefW) (W t1F i 0), D ∈ F :=
                  fun D hD => hOutI D (by simp [hrc0, hrc1, hD])
                have hx : drFlip (z34 b1 prefW) (xor b1 (singPref hk δ w rc.val qv)) ∈ (upS F)^[ta + 6 * dk + 7] S := by
                  rw [z101]; exact hprefUP
                have hd := drEq_up hCsub hx
                have hEqV : xor b1 (singPref hk δ w rc.val qv) =
                    xor (if (sInv hk δ i).val % 3 = 0 then b0 else if (sInv hk δ i).val % 3 = 1 then b1 else xor (xor (w (sIdx hk δ 1)) b0) b1)
                      (singPref hk δ w ((sInv hk δ i).val % 3) ((sInv hk δ i).val / 3)) := by
                  have h1 : (sInv hk δ i).val % 3 = 1 := hrc1
                  simp [pv, rc, qv, h1]
                rwa [hEqV] at hd
              · have hCsub : ∀ D ∈ drXor (z34 (xor b0 b1) (W t0F (z19 k hk (sIdx hk δ 1)) 6))
                    prefW (W t1F i 0), D ∈ F :=
                  fun D hD => hOutI D (by simp [hrc0, hrc1, hD])
                have hx1 : drFlip (z34 (xor b0 b1) (W t0F (z19 k hk (sIdx hk δ 1)) 6))
                    (xor (xor b0 b1) (w (sIdx hk δ 1))) ∈ (upS F)^[ta + 6 * dk + 7] S := by
                  rw [z101]
                  exact z5 F S (by omega : ta + 4 * dk + 6 <= ta + 6 * dk + 7) (hwUP _)
                have hstep := drXor_up hCsub hx1 hprefUP
                have hEqB : xor (xor (xor b0 b1) (w (sIdx hk δ 1))) (singPref hk δ w rc.val qv) =
                    xor (if pv % 3 = 0 then b0 else if pv % 3 = 1 then b1 else xor (xor (w (sIdx hk δ 1)) b0) b1)
                      (singPref hk δ w (pv % 3) qv) := by
                  have hne0 : pv % 3 ≠ 0 := hrc0
                  have hne1 : pv % 3 ≠ 1 := hrc1
                  simp only [hne0, hne1, ↓reduceIte, rc]
                  cases b0 <;> cases b1 <;> cases w (sIdx hk δ 1) <;> cases singPref hk δ w (pv % 3) qv <;> rfl
                rwa [hEqB] at hstep
          ·
            apply z5 F S (by omega : ta + 5 * dk + 9 <= ta + 6 * dk + 12)
            have hP0f : drFlip (P t0F false) (wrapOkB hk δ w) ∈ (upS F)^[ta + 5 * dk + 8] S := by
              rw [show ta + 5 * dk + 8 = (ta + 5 * dk + 7) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drAnd (drNot (M tR 0 false rootK)) (drNot (M tR 1 false rootK)) (P t0F false), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, ↓reduceIte]
                exact List.mem_append_right _ (List.mem_append_left _ hD)
              have h0 : drFlip (drNot (M tR 0 false rootK)) (!(singPref hk δ w 0 (k / 3))) ∈ (upS F)^[ta + 5 * dk + 7] S := by
                rw [drFlip_not]; exact (htree 0).2
              have h1 : drFlip (drNot (M tR 1 false rootK)) (!(singPref hk δ w 1 (k / 3))) ∈ (upS F)^[ta + 5 * dk + 7] S := by
                rw [drFlip_not]; exact (htree 1).2
              exact drAnd_up hCsub h0 h1
            rw [show ta + 5 * dk + 9 = (ta + 5 * dk + 8) + 1 by omega, Function.iterate_succ_apply']
            have hCsub : ∀ D ∈ drAnd (P t0F true) (P t0F false) (P t1F true), D ∈ F := by
              intro D hD; apply hMixMem; simp only [hk3, ↓reduceIte]
              exact List.mem_append_right _ (List.mem_append_right _ hD)
            have hresP : (z11 hk isCol r key drv leaf.val (t + 1)).2 = (acc && wrapOkB hk δ w) := by
              simp [z11, revRoundB, hk3, st, acc, idx, δ, u, w]
            rw [hresP]
            exact drAnd_up hCsub (z5 F S (by omega : ta <= ta + 5 * dk + 8) hprevP) hP0f
        ·
          by_cases hk5 : k < 5
          · rw [hstep_eq]
            constructor
            · intro i
              apply z5 F S (by omega : ta + 4 * dk + 7 <= ta + 6 * dk + 12)
              rw [show ta + 4 * dk + 7 = (ta + 4 * dk + 6) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drEq (W t0F (z19 k hk i) 6) (W t1F i 0), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                apply List.mem_append_left; rw [List.mem_flatMap]; exact ⟨i, List.mem_finRange i, hD⟩
              have hresVal : (z11 hk isCol r key drv leaf.val (t + 1)).1 i = w i := by
                simp [z11, revRoundB, invMixB, hk3, hk5, st, idx, δ, u, w]
              rw [hresVal]; exact drEq_up hCsub (hwUP i)
            · apply z5 F S (by omega : ta + 2 <= ta + 6 * dk + 12)
              have hP0f : drFlip (P t0F false) true ∈ (upS F)^[ta + 1] S := by
                rw [Function.iterate_succ_apply']
                have hCsub : ∀ D ∈ drEq z26 (P t0F false), D ∈ F := by
                  intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                  exact List.mem_append_right _ (List.mem_append_left _ hD)
                exact drEq_up hCsub (z78 hk H S (by omega))
              rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drAnd (P t0F true) (P t0F false) (P t1F true), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                exact List.mem_append_right _ (List.mem_append_right _ hD)
              have hresP : (z11 hk isCol r key drv leaf.val (t + 1)).2 = (acc && true) := by
                simp [z11, revRoundB, hk3, st, acc, idx, δ, u, w]
              rw [hresP]
              exact drAnd_up hCsub (z5 F S (by omega : ta <= ta + 1) hprevP) hP0f
          ·
            set upM := M tR 0 false
            set prM := M tR 0 true
            set fM : ℕ -> Bool := fun q => if hq : q < k then mixDiffAt hk δ w ⟨q, hq⟩ else false
            have hlf : ∀ p (hp : p < 2 ^ dk),
                drFlip (upM ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩) (fM p) ∈ (upS F)^[ta + 4 * dk + 7] S := by
              intro p hp
              rw [show ta + 4 * dk + 7 = (ta + 4 * dk + 6) + 1 by omega, Function.iterate_succ_apply']
              have hpMem : ∀ D ∈ (if p < k then
                  let a1 : Fin k := ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩
                  let a2 : Fin k := ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩
                  drXor (W t0F (z19 k hk a1) 6) (W t0F (z19 k hk a2) 6)
                    (upM ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)
                else drEq z3 (upM ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                rw [List.mem_flatMap]; exact ⟨⟨p, hp⟩, List.mem_finRange _, hD⟩
              by_cases hpk : p < k
              · have hCsub : ∀ D ∈ drXor (W t0F (z19 k hk ⟨(3 * δ * p + δ) % k, Nat.mod_lt _ hk⟩) 6)
                    (W t0F (z19 k hk ⟨(3 * δ * p + 2 * δ) % k, Nat.mod_lt _ hk⟩) 6)
                    (upM ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩), D ∈ F :=
                  fun D hD => hpMem D (by simp [hpk, hD])
                simpa [fM, hpk, mixDiffAt] using drXor_up hCsub (hwUP _) (hwUP _)
              · have hCsub : ∀ D ∈ drEq z3 (upM ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩), D ∈ F :=
                  fun D hD => hpMem D (by simp [hpk, hD])
                simpa [fM, hpk] using drEq_up hCsub (z32 hk H S (by omega : 1 <= ta + 4 * dk + 6))
            have hFup : ∀ D ∈ z14 dk upM, D ∈ F := by
              intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              apply List.mem_append_left; exact List.mem_append_right _ hD
            have hFpr : ∀ D ∈ z18 dk upM prM, D ∈ F := by
              intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              exact List.mem_append_right _ hD
            have hprRoot : drFlip (prM rootK) false ∈ (upS F)^[ta + 4 * dk + 7 + dk] S := by
              apply z5 F S (by omega : ta + 4 * dk + 7 <= ta + 4 * dk + 7 + dk)
              rw [show ta + 4 * dk + 7 = (ta + 4 * dk + 6) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drEq z3 (prM rootK), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
                apply List.mem_append_left; apply List.mem_append_left; exact List.mem_append_right _ hD
              exact drEq_up hCsub (z32 hk H S (by omega))
            have hprAt : ∀ p (hp : p < k),
                drFlip (prM ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩) (mixPref hk δ w p) ∈
                  (upS F)^[ta + 6 * dk + 7] S := by
              intro p hp
              have hp2 : p < 2 ^ dk := lt_of_lt_of_le hp hkle
              have hpr := z133 dk fM upM prM hFup hFpr (ta + 4 * dk + 7) hlf hprRoot dk (le_refl dk) p hp2
              have hidx_eq : hIdx dk (dk - dk) p = 2 ^ dk + p := by simp [hIdx]
              have hfin_eq : (⟨hIdx dk (dk - dk) p, hIdx_lt (by omega) (by simpa using hp2)⟩ : Fin (2 ^ (dk + 1))) =
                  ⟨2 ^ dk + p, by change 2 ^ dk + p < 2 ^ (dk + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx_eq
              rw [hfin_eq, hidx_eq, show ta + 4 * dk + 7 + dk + dk = ta + 6 * dk + 7 by omega] at hpr
              have hmp := z124 hk δ w p hp
              dsimp only at hmp; rwa [hmp] at hpr
            set pPos := inv3Pos k % k
            set pNeg := (k - pPos) % k
            set j0 : Fin k := ⟨0, hk⟩
            set j1 : Fin k := ⟨1 % k, Nat.mod_lt _ hk⟩
            have hx0_a : drFlip (W t0F j0 7) (xor (w j0) (mixPref hk δ w pPos)) ∈ (upS F)^[ta + 6 * dk + 8] S := by
              rw [show ta + 6 * dk + 8 = (ta + 6 * dk + 7) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drXor (W t0F (z19 k hk j0) 6)
                  (prM ⟨2 ^ dk + pPos, by have := lt_of_lt_of_le (Nat.mod_lt (inv3Pos k) hk) hkle; change 2 ^ dk + pPos < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)
                  (W t0F j0 7), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
                exact List.mem_append_left _ hD
              exact drXor_up hCsub (z5 F S (by omega : ta + 4 * dk + 6 <= ta + 6 * dk + 7) (hwUP j0))
                (hprAt pPos (Nat.mod_lt _ hk))
            have hx0_b : drFlip (W t0F j1 7)
                (xor (xor (w j0) (mixPref hk δ w pPos)) (mixPref hk δ w pNeg)) ∈ (upS F)^[ta + 6 * dk + 9] S := by
              rw [show ta + 6 * dk + 9 = (ta + 6 * dk + 8) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drXor (W t0F j0 7)
                  (prM ⟨2 ^ dk + pNeg, by have := lt_of_lt_of_le (Nat.mod_lt (k - pPos) hk) hkle; change 2 ^ dk + pNeg < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)
                  (W t0F j1 7), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
                exact List.mem_append_right _ hD
              exact drXor_up hCsub hx0_a (z5 F S (by omega : ta + 6 * dk + 7 <= ta + 6 * dk + 8) (hprAt pNeg (Nat.mod_lt _ hk)))
            rw [hstep_eq]
            constructor
            · intro i
              apply z5 F S (by omega : ta + 6 * dk + 10 <= ta + 6 * dk + 12)
              rw [show ta + 6 * dk + 10 = (ta + 6 * dk + 9) + 1 by omega, Function.iterate_succ_apply']
              set mv := (m3dInv k δ hk i).val
              have hCsub : ∀ D ∈ drXor (W t0F j1 7)
                  (prM ⟨2 ^ dk + mv, by have := lt_of_lt_of_le (m3dInv k δ hk i).isLt hkle; change 2 ^ dk + mv < 2 ^ (dk + 1); rw [pow_succ]; omega⟩)
                  (W t1F i 0), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                apply List.mem_append_left; apply List.mem_append_right
                rw [List.mem_flatMap]; exact ⟨i, List.mem_finRange i, hD⟩
              have hresVal : (z11 hk isCol r key drv leaf.val (t + 1)).1 i =
                  xor (xor (xor (w j0) (mixPref hk δ w pPos)) (mixPref hk δ w pNeg)) (mixPref hk δ w mv) := by
                simp [z11, revRoundB, invMixB, hk3, hk5, st, idx, δ, u, w, j0, pPos, pNeg, mv]
              rw [hresVal]
              exact drXor_up hCsub hx0_b (z5 F S (by omega : ta + 6 * dk + 7 <= ta + 6 * dk + 9)
                (hprAt mv (m3dInv k δ hk i).isLt))
            · apply z5 F S (by omega : ta + 2 <= ta + 6 * dk + 12)
              have hP0f : drFlip (P t0F false) true ∈ (upS F)^[ta + 1] S := by
                rw [Function.iterate_succ_apply']
                have hCsub : ∀ D ∈ drEq z26 (P t0F false), D ∈ F := by
                  intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                  exact List.mem_append_right _ (List.mem_append_left _ hD)
                exact drEq_up hCsub (z78 hk H S (by omega))
              rw [show ta + 2 = (ta + 1) + 1 by omega, Function.iterate_succ_apply']
              have hCsub : ∀ D ∈ drAnd (P t0F true) (P t0F false) (P t1F true), D ∈ F := by
                intro D hD; apply hMixMem; simp only [hk3, hk5, ↓reduceIte]
                exact List.mem_append_right _ (List.mem_append_right _ hD)
              have hresP : (z11 hk isCol r key drv leaf.val (t + 1)).2 = (acc && true) := by
                simp [z11, revRoundB, hk3, st, acc, idx, δ, u, w]
              rw [hresP]
              exact drAnd_up hCsub (z5 F S (by omega : ta <= ta + 1) hprevP) hP0f
    obtain ⟨hWr, hPr⟩ := hInv r (le_refl r)
    rw [z164] at hWr hPr
    dsimp only [z13]; rw [if_pos rfl]; dsimp only [z108]
    constructor
    · intro j
      apply z5 F S (by dsimp [Sstep]; nlinarith : T0 + 1 + Sstep * r + 1 <= T0 + (6 * dk + 14) * (r + 1))
      rw [Function.iterate_succ_apply']
      let kj : Fin k := ⟨(j.val + k - initRot isCol % k) % k, Nat.mod_lt _ hk⟩
      have hCsub : ∀ D ∈ drXor (drXDual ori m s (drvIdx ⟨0, by omega⟩ kj)) (W ⟨r, Nat.lt_succ_self r⟩ j 0)
          (W ⟨0, Nat.zero_lt_succ r⟩ j 8), D ∈ F := by
        intro D hD; apply hmemL; dsimp only [z9]
        rw [hrev]; simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
        rw [List.mem_flatMap]; exact ⟨j, List.mem_finRange j, hD⟩
      exact drXor_up hCsub (hkeyUP kj (T0 + 1 + Sstep * r) (by omega)) (hWr j)
    · exact z5 F S (by dsimp [Sstep]; nlinarith : T0 + 1 + Sstep * r <= T0 + (6 * dk + 14) * (r + 1)) hPr
private def z25 (ori : Bool × Bool) (x : Fin (3 * k) -> Bool)
    (wF wT : Fin k -> Bool) : V5 k -> Bool := fun ⟨tr, j⟩ =>
  if tr = dTrack ori ⟨0, by omega⟩ then x (drvIdx ⟨0, by omega⟩ j)
  else if tr = dTrack ori ⟨1, by omega⟩ then x (drvIdx ⟨1, by omega⟩ j)
  else if tr = dTrack ori ⟨2, by omega⟩ then x (drvIdx ⟨2, by omega⟩ j)
  else if tr = z15 ori false then wF j
  else wT j
private theorem z46 (ori : Bool × Bool) (x : Fin (3 * k) -> Bool)
    (wF wT : Fin k -> Bool) (t : Fin 3) (j : Fin k) :
    z25 ori x wF wT (dTrack ori t, j) = x (drvIdx t j) := by
  have ht : t.val = 0 \/ t.val = 1 \/ t.val = 2 := by omega
  rcases ori with ⟨rR, cR⟩
  rcases ht with h0 | h1 | h2
  · have : t = ⟨0, by decide⟩ := Fin.ext h0; subst this; cases rR <;> cases cR <;> simp [z25, dTrack]
  · have : t = ⟨1, by decide⟩ := Fin.ext h1; subst this; cases rR <;> cases cR <;> simp [z25, dTrack]
  · have : t = ⟨2, by decide⟩ := Fin.ext h2; subst this; cases rR <;> cases cR <;> simp [z25, dTrack]
private theorem z119 (hk : 0 < k) (ori : Bool × Bool) (x : Fin (3 * k) -> Bool)
    (wF wT : Fin k -> Bool) (idx : Fin (3 * k)) :
    z25 ori x wF wT (drvPos hk ori idx) = x idx := by
  let t : Fin 3 := ⟨idx.val / k, Nat.div_lt_of_lt_mul (by have := idx.isLt; omega)⟩
  let j : Fin k := ⟨idx.val % k, Nat.mod_lt _ hk⟩
  have hidx : drvIdx t j = idx := Fin.ext (by dsimp [drvIdx, t, j]; rw [Nat.mul_comm]; exact Nat.div_add_mod idx.val k)
  rw [← hidx, z49, z46]
private theorem z29 (ori : Bool × Bool) (x : Fin (3 * k) -> Bool)
    (wF wT : Fin k -> Bool) (isCol : Bool) (j : Fin k) :
    z25 ori x wF wT (z15 ori isCol, j) = if isCol then wT j else wF j := by
  rcases ori with ⟨rR, cR⟩
  cases isCol <;> cases rR <;> cases cR <;> simp [z25, dTrack, z15]
private theorem z120 (hk : 0 < k) (hk_odd : k % 2 = 1)
    (ori : Bool × Bool) (x : Fin (3 * k) -> Bool)
    (leafF leafT : Fin (z2 k r))
    (key : Fin k -> Bool) (hkey : key = fun j => x (drvIdx ⟨0, by omega⟩ j))
    (okF : (z13 hk r false (branchRev ori false) leafF key (fun j => x (drvIdx (z8 false) j))).2 = true)
    (okT : (z13 hk r true (branchRev ori true) leafT key (fun j => x (drvIdx (z8 true) j))).2 = true) :
    let v := z25 ori x
      (z13 hk r false (branchRev ori false) leafF key (fun j => x (drvIdx (z8 false) j))).1
      (z13 hk r true (branchRev ori true) leafT key (fun j => x (drvIdx (z8 true) j))).1
    (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) /\
    (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j)) := by
  subst hkey
  rcases ori with ⟨rR, cR⟩
  set wF := (z13 hk r false rR leafF (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx ⟨1, by omega⟩ j))).1
  set wT := (z13 hk r true cR leafT (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx ⟨2, by omega⟩ j))).1
  have hsF := evalBranch_sound hk hk_odd r false rR leafF
    (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx ⟨1, by omega⟩ j)) okF
  have hsT := evalBranch_sound hk hk_odd r true cR leafT
    (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx ⟨2, by omega⟩ j)) okT
  have h2 : (fun j => z25 (rR, cR) x wF wT (2, j)) = (fun j => x (drvIdx ⟨0, by omega⟩ j)) := by
    ext j; exact z46 (rR, cR) x wF wT ⟨0, by decide⟩ j
  change (fun j => z25 (rR, cR) x wF wT (3, j)) = firstB hk r (fun j => z25 (rR, cR) x wF wT (2, j)) (fun j => z25 (rR, cR) x wF wT (0, j)) /\
         (fun j => z25 (rR, cR) x wF wT (4, j)) = secondB hk r (fun j => z25 (rR, cR) x wF wT (2, j)) (fun j => z25 (rR, cR) x wF wT (1, j))
  constructor
  · cases rR
    · simp only [↓reduceIte] at hsF
      have h3 : (fun j => z25 (false, cR) x wF wT (3, j)) = wF := by
        ext j; exact z29 (false, cR) x wF wT false j
      have h0 : (fun j => z25 (false, cR) x wF wT (0, j)) = (fun j => x (drvIdx ⟨1, by omega⟩ j)) := by
        ext j; exact z46 (false, cR) x wF wT ⟨1, by decide⟩ j
      rw [h3, h2, h0]; dsimp only [wF]; rw [hsF, z61]
    · simp only [↓reduceIte] at hsF
      have h0 : (fun j => z25 (true, cR) x wF wT (0, j)) = wF := by
        ext j; exact z29 (true, cR) x wF wT false j
      have h3 : (fun j => z25 (true, cR) x wF wT (3, j)) = (fun j => x (drvIdx ⟨1, by omega⟩ j)) := by
        ext j; exact z46 (true, cR) x wF wT ⟨1, by decide⟩ j
      rw [h3, h2, h0, ← z61, hsF]
  · cases cR
    · simp only [↓reduceIte] at hsT
      have h4 : (fun j => z25 (rR, false) x wF wT (4, j)) = wT := by
        ext j; exact z29 (rR, false) x wF wT true j
      have h1 : (fun j => z25 (rR, false) x wF wT (1, j)) = (fun j => x (drvIdx ⟨2, by omega⟩ j)) := by
        ext j; exact z46 (rR, false) x wF wT ⟨2, by decide⟩ j
      rw [h4, h2, h1]; dsimp only [wT]; rw [hsT, z71]
    · simp only [↓reduceIte] at hsT
      have h1 : (fun j => z25 (rR, true) x wF wT (1, j)) = wT := by
        ext j; exact z29 (rR, true) x wF wT true j
      have h4 : (fun j => z25 (rR, true) x wF wT (4, j)) = (fun j => x (drvIdx ⟨2, by omega⟩ j)) := by
        ext j; exact z46 (rR, true) x wF wT ⟨2, by decide⟩ j
      rw [h4, h2, h1, ← z71, hsT]
private def AgreesB (hk : 0 < k) (r : ℕ) (v : V5 k -> Bool) : Prop :=
  (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) /\
  (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j))
private def CompleteS (hk : 0 < k) (r : ℕ) (M : BMat h' (3 * k)) (ori : Bool × Bool)
    (ρ : V5 k -> Option Bool) (s : Fin (2 ^ h')) (v : V5 k -> Bool) : Prop :=
  AgreesB hk r v /\
  (∀ raw b, ρ raw = some b -> v raw = b) /\
  synOf M (fun idx => v (drvPos hk ori idx)) = s
private theorem z113 (hk : 0 < k) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R) (s : Fin (2 ^ h'))
    (isCol : Bool) (leaf : Fin (z2 k r))
    (x : Fin (3 * k) -> Bool) (T0 : ℕ) (hT0 : 1 <= T0)
    (hxUP : ∀ i : Fin (3 * k),
      drFlip (drXDual (k := k) (r := r) (h' := h') (R := R) ori m s i) (x i) ∈
        (upS (z7 hk H).toFinset)^[T0] (seedOf ρ))
    (hdead : let key := fun j => x (drvIdx ⟨0, by omega⟩ j)
             let drv := fun j => x (drvIdx (z8 isCol) j)
             let res := z13 hk r isCol (branchRev ori isCol) leaf key drv
             res.2 = false \/ ∃ j : Fin k, ∃ b : Bool, ρ (z15 ori isCol, j) = some b /\ res.1 j ≠ b) :
    vLeafDead (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf ∈
      (upS (z7 hk H).toFinset)^[T0 + (6 * Nat.clog 2 k + 14) * (r + 1) + 1] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dk := Nat.clog 2 k
  set T1 := T0 + (6 * dk + 14) * (r + 1)
  obtain ⟨hW8, hPlast⟩ := up_leaf hk H ori m s isCol leaf S x T0 hT0 hxUP
  rw [Function.iterate_succ_apply']
  rcases hdead with hok | ⟨j, b, hρj, hne⟩
  · rw [hok] at hPlast
    have hCl : imp1 (z137 (k := k) (r := r) (h' := h') (R := R) ori m s isCol leaf ⟨r, Nat.lt_succ_self r⟩ true).1
        (vLeafDead ori m s isCol leaf) ∈ F := by
      apply z38 hk H ori m s isCol leaf
      dsimp only [z9]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (by simp)))
    exact upS_imp1 hCl hPlast
  · have hW8j := hW8 j
    have hraw : vRaw (k := k) (r := r) (h' := h') (R := R) (z15 ori isCol, j) b ∈ (upS F)^[T1] S :=
      z5 F S (Nat.zero_le T1) ⟨(z15 ori isCol, j), rfl, hρj⟩
    have hflip : (z13 hk r isCol (branchRev ori isCol) leaf
        (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx (z8 isCol) j))).1 j = !b := by
      cases hb : b <;> cases hr : (z13 hk r isCol (branchRev ori isCol) leaf
        (fun j => x (drvIdx ⟨0, by omega⟩ j)) (fun j => x (drvIdx (z8 isCol) j))).1 j <;> simp_all
    rw [hflip] at hW8j
    cases b
    · have hCl : imp2 (vRaw (z15 ori isCol, j) false)
          (z91 ori m s isCol leaf ⟨0, Nat.zero_lt_succ r⟩ j 8).2
          (vLeafDead ori m s isCol leaf) ∈ F := by
        apply z38 hk H ori m s isCol leaf
        dsimp only [z9]
        apply List.mem_append_left; apply List.mem_append_right; apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, by simp⟩
      exact upS_imp2 hCl hraw hW8j
    · have hCl : imp2 (vRaw (z15 ori isCol, j) true)
          (z91 ori m s isCol leaf ⟨0, Nat.zero_lt_succ r⟩ j 8).1
          (vLeafDead ori m s isCol leaf) ∈ F := by
        apply z38 hk H ori m s isCol leaf
        dsimp only [z9]
        apply List.mem_append_left; apply List.mem_append_right; apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, by simp⟩
      exact upS_imp2 hCl hraw hW8j
private theorem up_syn_dead (hk : 0 < k) (hk_odd : k % 2 = 1) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R)
    (hm : ∀ i ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
      ∃ c : Fin (2 ^ h'), ∀ j ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
        rowMask (H m) c j = decide (j = i))
    (s : Fin (2 ^ h')) (hno : ¬ ∃ v, CompleteS hk r (H m) ori ρ s v) :
    vSynDead (k := k) (r := r) (h' := h') (R := R) ori m s ∈
      (upS (z7 hk H).toFinset)^[3 * Nat.clog 2 (3 * k) + h' + (6 * Nat.clog 2 k + 14) * (r + 1) + dBOf k r + 11] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dN := Nat.clog 2 (3 * k)
  set dk := Nat.clog 2 k
  set dB := dBOf k r
  set T_drv := 4 + 2 * dN + h'
  set T_leaf := T_drv + (6 * dk + 14) * (r + 1)
  by_cases hex : ∃ x : Fin (3 * k) -> Bool,
      (∀ idx b, ρ (drvPos hk ori idx) = some b -> x idx = b) /\ synOf (H m) x = s
  · obtain ⟨x, hxρ, hxs⟩ := hex
    have hxUP := z128 (r := r) hk H ori ρ m hm x hxρ s hxs
    set key : Fin k -> Bool := fun j => x (drvIdx ⟨0, by omega⟩ j)
    set surv : Bool -> Fin (z2 k r) -> Prop := fun isCol leaf =>
      let res := z13 hk r isCol (branchRev ori isCol) leaf key (fun j => x (drvIdx (z8 isCol) j))
      res.2 = true /\ ∀ j b, ρ (z15 ori isCol, j) = some b -> res.1 j = b
    have hdead_branch : (∀ leaf, ¬ surv false leaf) \/ (∀ leaf, ¬ surv true leaf) := by
      by_contra hboth; push_neg at hboth
      obtain ⟨⟨leafF, hF_ok, hF_ρ⟩, ⟨leafT, hT_ok, hT_ρ⟩⟩ := hboth
      set v := z25 ori x
        (z13 hk r false (branchRev ori false) leafF key (fun j => x (drvIdx (z8 false) j))).1
        (z13 hk r true (branchRev ori true) leafT key (fun j => x (drvIdx (z8 true) j))).1
      apply hno; refine ⟨v, z120 hk hk_odd ori x leafF leafT key rfl hF_ok hT_ok, ?_, ?_⟩
      · intro ⟨tr, j⟩ b hρ
        rcases z122 ori tr with ⟨slot, rfl⟩ | rfl | rfl
        · dsimp only [v]; rw [z46]
          exact hxρ (drvIdx slot j) b (by rwa [z49])
        · dsimp only [v]; rw [z29]; exact hF_ρ j b hρ
        · dsimp only [v]; rw [z29]; exact hT_ρ j b hρ
      · have hxv : (fun idx => v (drvPos hk ori idx)) = x := funext (z119 hk ori x _ _)
        rw [hxv, hxs]
    have hbranch : ∀ isCol : Bool, (∀ leaf, ¬ surv isCol leaf) ->
        vSynDead (k := k) (r := r) (h' := h') (R := R) ori m s ∈ (upS F)^[T_leaf + dB + 3] S := by
      intro isCol hall
      set nd := z69 (k := k) (r := r) (h' := h') (R := R) ori m s isCol
      have hlf : ∀ j (hj : j < 2 ^ dB), nd ⟨2 ^ dB + j, by change 2 ^ dB + j < 2 ^ (dB + 1); rw [pow_succ]; omega⟩ ∈ (upS F)^[T_leaf + 2] S := by
        intro j hj
        let lf : Fin (z2 k r) := ⟨j, by rw [← z67]; exact hj⟩
        have hns := hall lf
        have hdead : (z13 hk r isCol (branchRev ori isCol) lf key
            (fun i => x (drvIdx (z8 isCol) i))).2 = false \/
            ∃ i b, ρ (z15 ori isCol, i) = some b /\
              (z13 hk r isCol (branchRev ori isCol) lf key
                (fun i => x (drvIdx (z8 isCol) i))).1 i ≠ b := by
          by_contra h1; push_neg at h1
          apply hns; exact ⟨Bool.eq_true_of_not_eq_false h1.1, h1.2⟩
        have hld := z113 hk H ori ρ m s isCol lf x T_drv (by omega) hxUP hdead
        rw [show T_leaf + 2 = (T_leaf + 1) + 1 by omega, Function.iterate_succ_apply']
        have hCl : imp1 (vLeafDead ori m s isCol lf) (nd ⟨2 ^ dB + j, by change 2 ^ dB + j < 2 ^ (dB + 1); rw [pow_succ]; omega⟩) ∈ F := by
          apply z31 hk H ori m s
          dsimp only [z35]
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
          rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
          apply List.mem_append_left; apply List.mem_append_left
          rw [List.mem_flatMap]; exact ⟨⟨j, hj⟩, List.mem_finRange _, by simp [lf, nd, dB]⟩
        exact upS_imp1 hCl hld
      have hFand : ∀ C ∈ z24 dB nd, C ∈ F := by
        intro C hC; apply z31 hk H ori m s
        dsimp only [z35]
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
        exact List.mem_append_left _ (List.mem_append_right _ hC)
      have hroot := z153 dB nd hFand (T_leaf + 2) hlf dB 0 (le_refl dB) (by simp)
      have hidx1 : hIdx dB dB 0 = 1 := by simp [hIdx]
      have hfin1 : (⟨hIdx dB dB 0, hIdx_lt (le_refl dB) (by simp)⟩ : Fin (2 ^ (dB + 1))) =
          ⟨1, by have := Nat.one_le_pow dB 2 (by omega); change 1 < 2 ^ (dB + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx1
      rw [hfin1, show T_leaf + 2 + dB = T_leaf + dB + 2 by omega] at hroot
      rw [show T_leaf + dB + 3 = (T_leaf + dB + 2) + 1 by omega, Function.iterate_succ_apply']
      have hCl : imp1 (nd ⟨1, by have := Nat.one_le_pow dB 2 (by omega); change 1 < 2 ^ (dB + 1); rw [pow_succ]; omega⟩)
          (vSynDead ori m s) ∈ F := by
        apply z31 hk H ori m s
        dsimp only [z35]
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
        exact List.mem_append_right _ (by simp [nd, dB])
      exact upS_imp1 hCl hroot
    have hTle : T_leaf + dB + 3 <= 3 * dN + h' + (6 * dk + 14) * (r + 1) + dB + 11 := by
      dsimp [T_leaf, T_drv]; omega
    rcases hdead_branch with hF | hT
    · exact z5 F S hTle (hbranch false hF)
    · exact z5 F S hTle (hbranch true hT)
  · have hexcl := up_excl_no_driver (r := r) hk H ori ρ m hm s hex
    apply z5 F S (by omega : 7 + 3 * dN + h' <= 3 * dN + h' + (6 * dk + 14) * (r + 1) + dB + 11)
    rw [show 7 + 3 * dN + h' = (6 + 3 * dN + h') + 1 by omega, Function.iterate_succ_apply']
    have hCl : imp1 (vExcl ori m s) (vSynDead ori m s) ∈ F := by
      apply z31 hk H ori m s
      dsimp only [z35]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by simp))))
    exact upS_imp1 hCl hexcl
private theorem up_syn_killLit (hk : 0 < k) (hk_odd : k % 2 = 1) (H : Fin R -> BMat h' (3 * k))
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R)
    (hm : ∀ i ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
      ∃ c : Fin (2 ^ h'), ∀ j ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
        rowMask (H m) c j = decide (j = i))
    (s : Fin (2 ^ h')) (p : V5 k) (b : Bool)
    (hkill : ∀ v, CompleteS hk r (H m) ori ρ s v -> v p ≠ b) :
    vKillLit (k := k) (r := r) (h' := h') (R := R) ori m s p b ∈
      (upS (z7 hk H).toFinset)^[3 * Nat.clog 2 (3 * k) + h' + (6 * Nat.clog 2 k + 14) * (r + 1) + dBOf k r + 12] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dN := Nat.clog 2 (3 * k)
  set dk := Nat.clog 2 k
  set dB := dBOf k r
  set T_drv := 4 + 2 * dN + h'
  set T_leaf := T_drv + (6 * dk + 14) * (r + 1)
  set T_tot := 3 * dN + h' + (6 * dk + 14) * (r + 1) + dB + 12
  by_cases hexV : ∃ v, CompleteS hk r (H m) ori ρ s v
  · obtain ⟨v0, hv0_ag, hv0_ρ, hv0_syn⟩ := hexV
    set x : Fin (3 * k) -> Bool := fun idx => v0 (drvPos hk ori idx)
    have hxρ : ∀ idx b0, ρ (drvPos hk ori idx) = some b0 -> x idx = b0 :=
      fun idx b0 h => hv0_ρ (drvPos hk ori idx) b0 h
    have hxUP := z128 (r := r) hk H ori ρ m hm x hxρ s hv0_syn
    rcases p with ⟨tr, j⟩
    have htarget : ∀ isCol : Bool, (∀ v, CompleteS hk r (H m) ori ρ s v -> v (z15 ori isCol, j) ≠ b) ->
        vKillLit (k := k) (r := r) (h' := h') (R := R) ori m s (z15 ori isCol, j) b ∈ (upS F)^[T_tot] S := by
      intro isCol hkill_t
      set key : Fin k -> Bool := fun i => x (drvIdx ⟨0, by omega⟩ i)
      have hkey_v0 : key = fun i => v0 (2, i) := by
        ext i; dsimp only [key, x]; rw [z49]; rfl
      have hOtherSurv : ∃ leafO : Fin (z2 k r),
          let resO := z13 hk r (!isCol) (branchRev ori (!isCol)) leafO key
            (fun i => x (drvIdx (z8 (!isCol)) i))
          resO.2 = true /\ ∀ i b0, ρ (z15 ori (!isCol), i) = some b0 -> resO.1 i = b0 := by
        have hinp : ∃ leafO : Fin (z2 k r),
            z13 hk r (!isCol) (branchRev ori (!isCol)) leafO key
              (fun i => x (drvIdx (z8 (!isCol)) i)) =
            (fun i => v0 (z15 ori (!isCol), i), true) := by
          have hc := z148 hk hk_odd r (!isCol) (branchRev ori (!isCol)) key
            (fun i => v0 (if !isCol then 1 else 0, i))
          obtain ⟨leafO, hleafO⟩ := hc
          refine ⟨leafO, ?_⟩
          have hdrvEq : (fun i => x (drvIdx (z8 (!isCol)) i)) =
              (if branchRev ori (!isCol) then z42 hk r (!isCol) key (fun i => v0 (if !isCol then 1 else 0, i))
               else fun i => v0 (if !isCol then 1 else 0, i)) := by
            rcases ori with ⟨rR, cR⟩
            cases isCol <;> cases rR <;> cases cR <;>
              (ext i; dsimp only [x, branchRev, z8]; rw [z49];
               simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, dTrack, ↓reduceIte,
                 z61, z71, hkey_v0])
            · exact congrFun hv0_ag.2 i
            · exact congrFun hv0_ag.2 i
            · exact congrFun hv0_ag.1 i
            · exact congrFun hv0_ag.1 i
          have htgtEq : (if branchRev ori (!isCol) then fun i => v0 (if !isCol then 1 else 0, i)
              else z42 hk r (!isCol) key (fun i => v0 (if !isCol then 1 else 0, i))) =
              fun i => v0 (z15 ori (!isCol), i) := by
            rcases ori with ⟨rR, cR⟩
            cases isCol <;> cases rR <;> cases cR <;>
              simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, branchRev, z15, ↓reduceIte,
                z61, z71, hkey_v0]
            · exact hv0_ag.2.symm
            · exact hv0_ag.2.symm
            · exact hv0_ag.1.symm
            · exact hv0_ag.1.symm
          rw [hdrvEq, hleafO, htgtEq]
        obtain ⟨leafO, hleafO⟩ := hinp
        refine ⟨leafO, ?_, ?_⟩
        · rw [hleafO]
        · intro i b0 hρ; rw [hleafO]; exact hv0_ρ _ b0 hρ
      obtain ⟨leafO, hO_ok, hO_ρ⟩ := hOtherSurv
      set nd := z68 (k := k) (r := r) (h' := h') (R := R) ori m s isCol j b
      have hlf : ∀ l (hl : l < 2 ^ dB), nd ⟨2 ^ dB + l, by change 2 ^ dB + l < 2 ^ (dB + 1); rw [pow_succ]; omega⟩ ∈ (upS F)^[T_leaf + 3] S := by
        intro l hl
        let lf : Fin (z2 k r) := ⟨l, by rw [← z67]; exact hl⟩
        set res := z13 hk r isCol (branchRev ori isCol) lf key (fun i => x (drvIdx (z8 isCol) i))
        have hlk : z90 (k := k) (r := r) (h' := h') (R := R) ori m s isCol lf j b ∈ (upS F)^[T_leaf + 2] S := by
          by_cases hsurv : res.2 = true /\ ∀ i b0, ρ (z15 ori isCol, i) = some b0 -> res.1 i = b0
          ·
            have hne : res.1 j ≠ b := by
              cases isCol
              · set v := z25 ori x res.1
                  (z13 hk r true (branchRev ori true) leafO key (fun i => x (drvIdx (z8 true) i))).1
                have hvC : CompleteS hk r (H m) ori ρ s v := by
                  refine ⟨z120 hk hk_odd ori x lf leafO key rfl hsurv.1 hO_ok, ?_, ?_⟩
                  · intro ⟨tr1, j1⟩ b1 hρ1
                    rcases z122 ori tr1 with ⟨sl, rfl⟩ | rfl | rfl
                    · dsimp only [v]; rw [z46]; exact hxρ (drvIdx sl j1) b1 (by rwa [z49])
                    · dsimp only [v]; rw [z29]; exact hsurv.2 j1 b1 hρ1
                    · dsimp only [v]; rw [z29]; exact hO_ρ j1 b1 hρ1
                  · have hxv : (fun idx => v (drvPos hk ori idx)) = x := funext (z119 hk ori x _ _)
                    rw [hxv, hv0_syn]
                have := hkill_t v hvC
                simpa [v, z29] using this
              · set v := z25 ori x
                  (z13 hk r false (branchRev ori false) leafO key (fun i => x (drvIdx (z8 false) i))).1
                  res.1
                have hvC : CompleteS hk r (H m) ori ρ s v := by
                  refine ⟨z120 hk hk_odd ori x leafO lf key rfl hO_ok hsurv.1, ?_, ?_⟩
                  · intro ⟨tr1, j1⟩ b1 hρ1
                    rcases z122 ori tr1 with ⟨sl, rfl⟩ | rfl | rfl
                    · dsimp only [v]; rw [z46]; exact hxρ (drvIdx sl j1) b1 (by rwa [z49])
                    · dsimp only [v]; rw [z29]; exact hO_ρ j1 b1 hρ1
                    · dsimp only [v]; rw [z29]; exact hsurv.2 j1 b1 hρ1
                  · have hxv : (fun idx => v (drvPos hk ori idx)) = x := funext (z119 hk ori x _ _)
                    rw [hxv, hv0_syn]
                have := hkill_t v hvC
                simpa [v, z29] using this
            have hflip : res.1 j = !b := by cases hr : res.1 j <;> cases hb : b <;> simp_all
            have hW8 := (up_leaf hk H ori m s isCol lf S x T_drv (by omega) hxUP).1 j
            change drFlip (z91 ori m s isCol lf ⟨0, Nat.zero_lt_succ r⟩ j 8) (res.1 j) ∈ (upS F)^[T_leaf] S at hW8
            rw [hflip] at hW8
            apply z5 F S (by omega : T_leaf + 1 <= T_leaf + 2)
            rw [Function.iterate_succ_apply']
            have hCl : imp1 (drFlip (z91 ori m s isCol lf ⟨0, Nat.zero_lt_succ r⟩ j 8) (!b))
                (z90 ori m s isCol lf j b) ∈ F := by
              apply z38 hk H ori m s isCol lf
              dsimp only [z9]; apply List.mem_append_right
              rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
              rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, by simp⟩
            exact upS_imp1 hCl hW8
          ·
            have hdead : res.2 = false \/ ∃ i b0, ρ (z15 ori isCol, i) = some b0 /\ res.1 i ≠ b0 := by
              by_contra h1; push_neg at h1
              exact hsurv ⟨Bool.eq_true_of_not_eq_false h1.1, h1.2⟩
            have hld := z113 hk H ori ρ m s isCol lf x T_drv (by omega) hxUP hdead
            rw [show T_leaf + 2 = (T_leaf + 1) + 1 by omega, Function.iterate_succ_apply']
            have hCl : imp1 (vLeafDead ori m s isCol lf) (z90 ori m s isCol lf j b) ∈ F := by
              apply z38 hk H ori m s isCol lf
              dsimp only [z9]; apply List.mem_append_right
              rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
              rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, by simp⟩
            exact upS_imp1 hCl hld
        rw [show T_leaf + 3 = (T_leaf + 2) + 1 by omega, Function.iterate_succ_apply']
        have hCl : imp1 (z90 ori m s isCol lf j b) (nd ⟨2 ^ dB + l, by change 2 ^ dB + l < 2 ^ (dB + 1); rw [pow_succ]; omega⟩) ∈ F := by
          apply z31 hk H ori m s
          dsimp only [z35]
          apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
          rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
          rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
          rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, ?_⟩
          apply List.mem_append_left; apply List.mem_append_left
          rw [List.mem_flatMap]; exact ⟨⟨l, hl⟩, List.mem_finRange _, by simp [lf, nd, dB]⟩
        exact upS_imp1 hCl hlk
      have hFand : ∀ C ∈ z24 dB nd, C ∈ F := by
        intro C hC; apply z31 hk H ori m s
        dsimp only [z35]
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
        rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
        rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, ?_⟩
        exact List.mem_append_left _ (List.mem_append_right _ hC)
      have hroot := z153 dB nd hFand (T_leaf + 3) hlf dB 0 (le_refl dB) (by simp)
      have hidx1 : hIdx dB dB 0 = 1 := by simp [hIdx]
      have hfin1 : (⟨hIdx dB dB 0, hIdx_lt (le_refl dB) (by simp)⟩ : Fin (2 ^ (dB + 1))) =
          ⟨1, by have := Nat.one_le_pow dB 2 (by omega); change 1 < 2 ^ (dB + 1); rw [pow_succ]; omega⟩ := Fin.ext hidx1
      rw [hfin1, show T_leaf + 3 + dB = T_leaf + dB + 3 by omega] at hroot
      apply z5 F S (by dsimp [T_leaf, T_drv, T_tot]; omega : T_leaf + dB + 4 <= T_tot)
      rw [show T_leaf + dB + 4 = (T_leaf + dB + 3) + 1 by omega, Function.iterate_succ_apply']
      have hCl : imp1 (nd ⟨1, by have := Nat.one_le_pow dB 2 (by omega); change 1 < 2 ^ (dB + 1); rw [pow_succ]; omega⟩)
          (vKillLit ori m s (z15 ori isCol, j) b) ∈ F := by
        apply z31 hk H ori m s
        dsimp only [z35]
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨isCol, by cases isCol <;> simp, ?_⟩
        rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
        rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, ?_⟩
        exact List.mem_append_right _ (by simp [nd, dB])
      exact upS_imp1 hCl hroot
    rcases z122 ori tr with ⟨slot, rfl⟩ | rfl | rfl
    ·
      have hne : x (drvIdx slot j) ≠ b := by
        have hpos : drvPos hk ori (drvIdx slot j) = (dTrack ori slot, j) := z49 hk ori slot j
        have := hkill v0 ⟨hv0_ag, hv0_ρ, hv0_syn⟩
        simpa [x, hpos] using this
      have hxb : x (drvIdx slot j) = !b := by cases hx : x (drvIdx slot j) <;> cases hb : b <;> simp_all
      have hx_at := hxUP (drvIdx slot j)
      rw [hxb] at hx_at
      apply z5 F S (by dsimp [T_drv, T_tot]; omega : T_drv + 1 <= T_tot)
      rw [Function.iterate_succ_apply']
      have hCl : imp1 (drFlip (drXDual ori m s (drvIdx slot j)) (!b))
          (vKillLit ori m s (dTrack ori slot, j) b) ∈ F := by
        apply z31 hk H ori m s
        dsimp only [z35]; apply List.mem_append_right
        rw [List.mem_flatMap]; refine ⟨slot, List.mem_finRange slot, ?_⟩
        rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
        rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, by simp⟩
      exact upS_imp1 hCl hx_at
    · exact htarget false hkill
    · exact htarget true hkill
  ·
    have hdead := up_syn_dead hk hk_odd H ori ρ m hm s hexV
    have hTtot : T_tot = (3 * dN + h' + (6 * dk + 14) * (r + 1) + dB + 11) + 1 := rfl
    rw [hTtot, Function.iterate_succ_apply']
    have hCl : imp1 (vSynDead ori m s) (vKillLit ori m s p b) ∈ F := by
      rcases p with ⟨tr, j⟩
      apply z31 hk H ori m s
      dsimp only [z35]
      apply List.mem_append_left; apply List.mem_append_right
      rw [List.mem_flatMap]; refine ⟨tr, List.mem_finRange tr, ?_⟩
      rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
      rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, by simp⟩
    exact upS_imp1 hCl hdead
private theorem rounds_budget_ok (hk : 0 < k) (r h : ℕ) (hh' : h' <= h) :
    3 * Nat.clog 2 (3 * k) + 2 * h' + (6 * Nat.clog 2 k + 14) * (r + 1) + dBOf k r + 14 <=
      512 * ((r + 1) * (Nat.clog 2 (k + 1) + 1) + h + 1) := by
  set C := Nat.clog 2 (k + 1)
  have hdk : Nat.clog 2 k <= C := Nat.clog_mono_right 2 (by omega)
  have hdN : Nat.clog 2 (3 * k) <= C + 2 := by
    apply Nat.clog_le_of_le_pow
    have hle : k + 1 <= 2 ^ C := Nat.le_pow_clog (by omega) (k + 1)
    rw [pow_add]; norm_num; omega
  have hdB : dBOf k r <= 2 * r := by dsimp [dBOf]; split_ifs <;> omega
  have hmul : (6 * Nat.clog 2 k + 14) * (r + 1) <= (6 * C + 14) * (r + 1) :=
    Nat.mul_le_mul_right (r + 1) (by omega)
  have hcr : C <= (r + 1) * (C + 1) := by
    calc C <= C + 1 := Nat.le_succ C
      _ = 1 * (C + 1) := (Nat.one_mul _).symm
      _ <= (r + 1) * (C + 1) := Nat.mul_le_mul_right _ (by omega)
  have hr1 : r + 1 <= (r + 1) * (C + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h6 : (6 * C + 14) * (r + 1) <= 14 * ((r + 1) * (C + 1)) := by
    have : 6 * C + 14 <= 14 * (C + 1) := by omega
    calc (6 * C + 14) * (r + 1) <= 14 * (C + 1) * (r + 1) := Nat.mul_le_mul_right _ this
      _ = 14 * ((r + 1) * (C + 1)) := by ring
  omega
private theorem up_matAgg_unsat (hk : 0 < k) (hk_odd : k % 2 = 1) (H : Fin R -> BMat h' (3 * k))
    (rounds : ℕ)
    (hrounds : 3 * Nat.clog 2 (3 * k) + 2 * h' + (6 * Nat.clog 2 k + 14) * (r + 1) + dBOf k r + 14 <= rounds)
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R)
    (hm : ∀ i ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
      ∃ c : Fin (2 ^ h'), ∀ j ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
        rowMask (H m) c j = decide (j = i))
    (hno : ¬ ∃ v : V5 k -> Bool, AgreesB hk r v /\ ∀ raw b, ρ raw = some b -> v raw = b) :
    ∃ C ∈ (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset,
      ∀ l ∈ C, negL l ∈ (upS (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset)^[rounds] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dN := Nat.clog 2 (3 * k)
  set dk := Nat.clog 2 k
  set dB := dBOf k r
  set T_syn := 3 * dN + h' + (6 * dk + 14) * (r + 1) + dB + 11
  set deadNd := z156 (k := k) (r := r) (h' := h') (R := R) ori m
  set rootH : Fin (2 ^ (h' + 1)) := ⟨1, by have := Nat.one_le_pow h' 2 (by omega); rw [pow_succ]; omega⟩
  have hlf : ∀ j (hj : j < 2 ^ h'), deadNd ⟨2 ^ h' + j, by rw [pow_succ]; omega⟩ ∈ (upS F)^[T_syn + 1] S := by
    intro j hj
    have hno_s : ¬ ∃ v, CompleteS hk r (H m) ori ρ ⟨j, hj⟩ v := fun ⟨v, ha, hρ, _⟩ => hno ⟨v, ha, hρ⟩
    have hsd := up_syn_dead hk hk_odd H ori ρ m hm ⟨j, hj⟩ hno_s
    rw [Function.iterate_succ_apply']
    have hCl : imp1 (vSynDead ori m ⟨j, hj⟩) (deadNd ⟨2 ^ h' + j, by rw [pow_succ]; omega⟩) ∈ F := by
      apply z51 hk H ori m
      dsimp only [z48]; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      rw [List.mem_flatMap]; exact ⟨⟨j, hj⟩, List.mem_finRange _, by simp [deadNd]⟩
    exact upS_imp1 hCl hsd
  have hFand : ∀ C ∈ z24 h' deadNd, C ∈ F := by
    intro C hC; apply z51 hk H ori m
    dsimp only [z48]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hC))
  have hroot := z153 h' deadNd hFand (T_syn + 1) hlf h' 0 (le_refl h') (by simp)
  have hidx1 : hIdx h' h' 0 = 1 := by simp [hIdx]
  have hfin1 : (⟨hIdx h' h' 0, hIdx_lt (le_refl h') (by simp)⟩ : Fin (2 ^ (h' + 1))) = rootH := Fin.ext hidx1
  rw [hfin1] at hroot
  have hle_r : T_syn + 1 + h' <= rounds := by dsimp only [T_syn]; omega
  have hroot_r : deadNd rootH ∈ (upS F)^[rounds] S :=
    z5 F S hle_r hroot
  refine ⟨cl1 (negL (deadNd rootH)), ?_, ?_⟩
  · apply z51 hk H ori m
    dsimp only [z48]
    exact List.mem_append_left _ (List.mem_append_right _ (by simp [rootH, deadNd]))
  · intro l hl
    rw [cl1, Finset.mem_singleton] at hl; subst hl
    rw [negL_negL]; exact hroot_r
private theorem up_matAgg_entailed (hk : 0 < k) (hk_odd : k % 2 = 1) (H : Fin R -> BMat h' (3 * k))
    (rounds : ℕ)
    (hrounds : 3 * Nat.clog 2 (3 * k) + 2 * h' + (6 * Nat.clog 2 k + 14) * (r + 1) + dBOf k r + 14 <= rounds)
    (ori : Bool × Bool) (ρ : V5 k -> Option Bool) (m : Fin R)
    (hm : ∀ i ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
      ∃ c : Fin (2 ^ h'), ∀ j ∈ Finset.univ.filter (fun idx : Fin (3 * k) => ρ (drvPos hk ori idx) = none),
        rowMask (H m) c j = decide (j = i))
    (raw : V5 k) (sign : Bool)
    (hent : ∀ v : V5 k -> Bool, (AgreesB hk r v /\ ∀ p b, ρ p = some b -> v p = b) -> v raw = sign) :
    vRaw (k := k) (r := r) (h' := h') (R := R) raw sign ∈
      (upS (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset)^[rounds] (seedOf ρ) := by
  set F := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset
  set S := seedOf (M := AuxAll k r h' R) ρ
  set dN := Nat.clog 2 (3 * k)
  set dk := Nat.clog 2 k
  set dB := dBOf k r
  set T_syn := 3 * dN + h' + (6 * dk + 14) * (r + 1) + dB + 12
  set b := !sign
  rcases raw with ⟨tr, j⟩
  set nd := vAllKilled (k := k) (r := r) (h' := h') (R := R) ori m (tr, j) b
  set rootH : Fin (2 ^ (h' + 1)) := ⟨1, by have := Nat.one_le_pow h' 2 (by omega); rw [pow_succ]; omega⟩
  have hlf : ∀ l (hl : l < 2 ^ h'), nd ⟨2 ^ h' + l, by rw [pow_succ]; omega⟩ ∈ (upS F)^[T_syn + 1] S := by
    intro l hl
    have hkill : ∀ v, CompleteS hk r (H m) ori ρ ⟨l, hl⟩ v -> v (tr, j) ≠ b := by
      intro v ⟨ha, hρ, _⟩
      rw [hent v ⟨ha, hρ⟩]; cases sign <;> decide
    have hsk := up_syn_killLit hk hk_odd H ori ρ m hm ⟨l, hl⟩ (tr, j) b hkill
    rw [Function.iterate_succ_apply']
    have hCl : imp1 (vKillLit ori m ⟨l, hl⟩ (tr, j) b) (nd ⟨2 ^ h' + l, by rw [pow_succ]; omega⟩) ∈ F := by
      apply z51 hk H ori m
      dsimp only [z48]; apply List.mem_append_right
      rw [List.mem_flatMap]; refine ⟨tr, List.mem_finRange tr, ?_⟩
      rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
      rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, ?_⟩
      apply List.mem_append_left; apply List.mem_append_left
      rw [List.mem_flatMap]; exact ⟨⟨l, hl⟩, List.mem_finRange _, by simp [nd]⟩
    exact upS_imp1 hCl hsk
  have hFand : ∀ C ∈ z24 h' nd, C ∈ F := by
    intro C hC; apply z51 hk H ori m
    dsimp only [z48]; apply List.mem_append_right
    rw [List.mem_flatMap]; refine ⟨tr, List.mem_finRange tr, ?_⟩
    rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
    rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, ?_⟩
    exact List.mem_append_left _ (List.mem_append_right _ hC)
  have hroot := z153 h' nd hFand (T_syn + 1) hlf h' 0 (le_refl h') (by simp)
  have hidx1 : hIdx h' h' 0 = 1 := by simp [hIdx]
  have hfin1 : (⟨hIdx h' h' 0, hIdx_lt (le_refl h') (by simp)⟩ : Fin (2 ^ (h' + 1))) = rootH := Fin.ext hidx1
  rw [hfin1] at hroot
  have hle_r : T_syn + 1 + h' + 1 <= rounds := by dsimp only [T_syn]; omega
  change vRaw (tr, j) sign ∈ (upS F)^[rounds] S
  apply z5 F S hle_r
  rw [Function.iterate_succ_apply']
  have hCl : imp1 (nd rootH) (vRaw (tr, j) (!b)) ∈ F := by
    apply z51 hk H ori m
    dsimp only [z48]; apply List.mem_append_right
    rw [List.mem_flatMap]; refine ⟨tr, List.mem_finRange tr, ?_⟩
    rw [List.mem_flatMap]; refine ⟨j, List.mem_finRange j, ?_⟩
    rw [List.mem_flatMap]; refine ⟨b, by cases b <;> simp, ?_⟩
    exact List.mem_append_right _ (by simp [rootH, nd])
  have hCl' : imp1 (nd rootH) (vRaw (tr, j) sign) ∈ F := by
    have hbb : (!b) = sign := Bool.not_not sign
    rwa [hbb] at hCl
  exact upS_imp1 hCl' hroot
end UnitProp
theorem L_pcx_304_core (k r h : ℕ) (hk_odd : k % 2 = 1) (R_cnt : ℕ)
    (hbudR : 3 * Nat.clog 2 (3 * k) + 2 * min h (3 * k) +
      (6 * Nat.clog 2 k + 14) * (r + 1) + dBOf k r + 14 <= R_cnt) :
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let V := Fin 5 × Fin k
  let word := fun (v : V -> Bool) (track : Fin 5) =>
    ∑ j : Fin k, (v (track,j)).toNat * 2^j.val
  let agrees := fun (v : V -> Bool) =>
    word v 3 = first (word v 2) (word v 0) /\
    word v 4 = second (word v 2) (word v 1)
  let branch := if k % 3 = 0 then 4^r else 1
  ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
    m + (∑ C ∈ F, C.card) <= 16777216*(k+1)*(r+1)*branch*(h+1)^2*(Nat.clog 2 (3*k+1)+1)*2^h /\
    (∀ C ∈ F, C.card <= 3) /\
    (∀ v : V -> Bool, agrees v ↔ ∃ aux : Fin m -> Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim v aux) (↑F : Set _)) /\
    ∀ (rowRev colRev : Bool) (ρ : V -> Option Bool),
      let driver := fun j : V => j.1 = 2 \/
        j.1 = (if rowRev then 3 else 0) \/ j.1 = (if colRev then 4 else 1)
      (Finset.univ.filter (fun j : V => driver j /\ ρ j = none)).card <= h ->
      let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ raw : V, l.1 = Sum.inl raw /\ ρ raw = some l.2}
      let advance := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
        S ∪ {l | ∃ C ∈ F, l ∈ C /\ ∀ other ∈ C, other ≠ l ->
          PEqualNP.Search.negLit other ∈ S}
      let known := (advance^[R_cnt]) seed
      let complete := fun v : V -> Bool => agrees v /\
        ∀ (raw : V) (sign : Bool), ρ raw = some sign -> v raw = sign
      ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, PEqualNP.Search.negLit l ∈ known) /\
      ((∃ v, complete v) -> ∀ raw : V, ∀ sign : Bool,
        (∀ v, complete v -> v raw = sign) ↔ (Sum.inl raw, sign) ∈ known) := by
  intro rot step constant first second V word agrees branch
  have hk : 0 < k := by omega
  set h' := min h (3 * k)
  have hh'_le_h : h' <= h := Nat.min_le_left _ _
  have hh'_le_3k : h' <= 3 * k := Nat.min_le_right _ _
  obtain ⟨R, H, _hR_pos, hR_le, hH_sep⟩ := exists_mat_family_any (3 * k) h' hh'_le_3k
  let e : AuxAll k r h' R ≃ Fin (Fintype.card (AuxAll k r h' R)) := Fintype.equivFin (AuxAll k r h' R)
  set m : ℕ := Fintype.card (AuxAll k r h' R) with hm_def
  set F0 : Finset (Cl (VarAll k r h' R)) := (z7 (k := k) (r := r) (h' := h') (R := R) hk H).toFinset with hF0_def
  set F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m))) := F0.image (mapCl e) with hF_def
  have hag_iff : ∀ v : V -> Bool, agrees v ↔ AgreesB hk r v := by
    intro v
    have h1 : first (word v 2) (word v 0) = toNat (firstB hk r (fun j => v (2, j)) (fun j => v (0, j))) :=
      firstB_toNat hk r (fun j => v (2, j)) (fun j => v (0, j))
    have h2 : second (word v 2) (word v 1) = toNat (secondB hk r (fun j => v (2, j)) (fun j => v (1, j))) :=
      secondB_toNat hk r (fun j => v (2, j)) (fun j => v (1, j))
    change (toNat (fun j => v (3, j)) = first (word v 2) (word v 0) /\
            toNat (fun j => v (4, j)) = second (word v 2) (word v 1)) ↔ AgreesB hk r v
    rw [h1, h2]
    exact ⟨fun ⟨ha, hb⟩ => ⟨toNat_inj ha, toNat_inj hb⟩,
           fun ⟨ha, hb⟩ => ⟨congrArg toNat ha, congrArg toNat hb⟩⟩
  refine ⟨m, F, ?_, ?_, ?_, ?_⟩
  ·
    have hsum1 : ∑ C ∈ F, C.card <= ∑ C ∈ F0, C.card := mapCl_sum_card_le e F0
    have hsum2 : ∑ C ∈ F0, C.card <= 3 * F0.card := by
      calc ∑ C ∈ F0, C.card <= ∑ _C ∈ F0, 3 :=
            Finset.sum_le_sum fun C hC => z141 hk H C (List.mem_toFinset.mp hC)
        _ = F0.card * 3 := by simp
        _ = 3 * F0.card := Nat.mul_comm _ _
    have hcard_le : F0.card <= (z7 (k := k) (r := r) (h' := h') (R := R) hk H).length :=
      List.toFinset_card_le _
    have hsb := size_bound_all (k := k) (r := r) (h' := h') (R := R) hk h hh'_le_h H hR_le
    change Fintype.card (AuxAll k r h' R) + 3 * (z7 (k := k) (r := r) (h' := h') (R := R) hk H).length <=
      16777216 * (k + 1) * (r + 1) * branch * (h + 1) ^ 2 * (Nat.clog 2 (3 * k + 1) + 1) * 2 ^ h at hsb
    rw [← hm_def] at hsb
    omega
  ·
    intro C hC
    rw [hF_def, Finset.mem_image] at hC
    rcases hC with ⟨D, hD, rfl⟩
    rw [mapCl_card]
    exact z141 hk H D (List.mem_toFinset.mp hD)
  ·
    intro v
    rw [hag_iff v, hF_def, ← mapF_sat_iff e v F0]
    constructor
    · intro hag
      refine ⟨auxVal hk H v, ?_⟩
      intro C hC
      exact fullClauses_sat hk hk_odd H v hag C (List.mem_toFinset.mp hC)
    · rintro ⟨aux, hsat⟩
      exact baseClauses_sound hk v aux fun C hC =>
        hsat C (mem_fullClauses_base hk H C hC)
  ·
    intro rowRev colRev ρ driver hρ_card seed advance known complete
    set ori : Bool × Bool := (rowRev, colRev)
    set U : Finset (Fin (3 * k)) := Finset.univ.filter (fun idx => ρ (drvPos hk ori idx) = none)
    have hU_le_h : U.card <= h := by
      have himg : U.image (drvPos hk ori) ⊆
          Finset.univ.filter (fun j : V => driver j /\ ρ j = none) := by
        intro p hp
        rw [Finset.mem_image] at hp; rcases hp with ⟨idx, hidx, rfl⟩
        rw [Finset.mem_filter] at hidx ⊢
        refine ⟨Finset.mem_univ _, ?_, hidx.2⟩
        exact (z166 hk ori (drvPos hk ori idx)).mpr ⟨idx, rfl⟩
      have hcard_img : (U.image (drvPos hk ori)).card = U.card :=
        Finset.card_image_of_injective U (drvPos_inj hk ori)
      exact le_trans (hcard_img ▸ Finset.card_le_card himg) hρ_card
    have hU_le_3k : U.card <= 3 * k := by
      calc U.card <= (Finset.univ : Finset (Fin (3 * k))).card := Finset.card_le_univ U
        _ = 3 * k := by simp
    have hU_le_h' : U.card <= h' := le_min hU_le_h hU_le_3k
    obtain ⟨mIdx, hmIdx⟩ := hH_sep U hU_le_h'
    have hlift : ∀ v : V -> Bool,
        AgreesB hk r v -> (∀ raw b, ρ raw = some b -> v raw = b) ->
        ∃ α : Sum V (Fin m) -> Bool,
          (∀ p, α (Sum.inl p) = v p) /\
          PEqualNP.ProofComplexity.Satisfies α (↑F : Set _) /\
          (∀ l ∈ seed, α l.1 = l.2) := by
      intro v hag hρv
      have hsat0 : PEqualNP.ProofComplexity.Satisfies (Sum.elim v (auxVal hk H v)) (↑F0 : Set _) :=
        fun C hC => fullClauses_sat hk hk_odd H v hag C (List.mem_toFinset.mp hC)
      obtain ⟨aux', hsat'⟩ := (mapF_sat_iff e v F0).mp ⟨auxVal hk H v, hsat0⟩
      refine ⟨Sum.elim v aux', fun _ => rfl, hsat', ?_⟩
      intro l ⟨raw, hv, hρl⟩
      rw [hv]; exact hρv raw l.2 hρl
    have hadv : advance = upS F := rfl
    have hseed_eq : seed = seedOf (M := Fin m) ρ := rfl
    have hknown_eq : known = (upS F)^[R_cnt] (seedOf (M := Fin m) ρ) := by
      change (advance^[R_cnt]) seed = _
      rw [hadv, hseed_eq]
    constructor
    · constructor
      · intro hno
        have hnoB : ¬ ∃ v : V -> Bool, AgreesB hk r v /\ ∀ raw b, ρ raw = some b -> v raw = b := by
          rintro ⟨v, hag, hρv⟩; exact hno ⟨v, (hag_iff v).mpr hag, hρv⟩
        obtain ⟨C0, hC0, hneg0⟩ := up_matAgg_unsat hk hk_odd H R_cnt hbudR ori ρ mIdx hmIdx hnoB
        refine ⟨mapCl e C0, Finset.mem_image_of_mem (mapCl e) hC0, ?_⟩
        intro l hl
        dsimp only [mapCl] at hl
        rw [Finset.mem_image] at hl; rcases hl with ⟨l0, hl0, rfl⟩
        rw [hknown_eq, hF_def]
        exact z125 e F0 ρ R_cnt (negL l0) (hneg0 l0 hl0)
      · rintro ⟨C, hCF, hall⟩ ⟨v, hag, hρv⟩
        obtain ⟨α, _, hsatF, hseed⟩ := hlift v ((hag_iff v).mp hag) hρv
        have hsatC : PEqualNP.ProofComplexity.ClauseSat α C := hsatF C hCF
        rcases hsatC with ⟨l, hlC, hlα⟩
        have hmem_k : PEqualNP.Search.negLit l ∈ (upS F)^[R_cnt] (seedOf (M := Fin m) ρ) :=
          hknown_eq ▸ hall l hlC
        have hneg := z163 hsatF hseed R_cnt (PEqualNP.Search.negLit l) hmem_k
        rcases l with ⟨x, b⟩
        dsimp [PEqualNP.Search.negLit] at hneg
        rw [hlα] at hneg; cases b <;> cases hneg
    · intro _ raw sign
      constructor
      · intro hent
        have hentB : ∀ v : V -> Bool,
            (AgreesB hk r v /\ ∀ p b, ρ p = some b -> v p = b) -> v raw = sign :=
          fun v ⟨hag, hρv⟩ => hent v ⟨(hag_iff v).mpr hag, hρv⟩
        have h0 := up_matAgg_entailed hk hk_odd H R_cnt hbudR ori ρ mIdx hmIdx raw sign hentB
        rw [hknown_eq, hF_def]
        exact z125 e F0 ρ R_cnt (Sum.inl raw, sign) h0
      · intro hmem v ⟨hag, hρv⟩
        obtain ⟨α, hαinl, hsatF, hseed⟩ := hlift v ((hag_iff v).mp hag) hρv
        have hmem_k : (Sum.inl raw, sign) ∈ (upS F)^[R_cnt] (seedOf (M := Fin m) ρ) :=
          hknown_eq ▸ hmem
        have hsound := z163 hsatF hseed R_cnt (Sum.inl raw, sign) hmem_k
        simpa [hαinl raw] using hsound
end PEqualNP.Outside.L_pcx_304_aux

theorem PEqualNP.Outside.L_pcx_304 :
    ∀ (k r h : ℕ), k % 2 = 1 →
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor (word.testBit i)
        (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0
  let constant := fun (j : Nat) => 3 ^ (k + j) % 2 ^ k
  let first := fun (rowKey rowName : Nat) =>
    (List.range r).foldl (fun rowState rowIndex =>
      step (rowState ^^^ rot 1 rowState ^^^ rot (k - 1) rowState) ^^^
        rot (2 * rowIndex) rowKey ^^^ constant (rowIndex + 1)) (rot 1 rowKey ^^^ rowName)
  let second := fun (colKey colName : Nat) =>
    (List.range r).foldl (fun colState colIndex =>
      step (colState ^^^ rot 2 colState ^^^ rot (k - 2) colState) ^^^
        rot (3 * (colIndex + 1) + 1) colKey ^^^ constant (r + (colIndex + 1)))
      (rot 3 colKey ^^^ colName)
  let V := Fin 5 × Fin k
  let word := fun (v : V → Bool) (track : Fin 5) =>
    ∑ j : Fin k, (v (track,j)).toNat * 2^j.val
  let agrees := fun (v : V → Bool) =>
    word v 3 = first (word v 2) (word v 0) ∧
    word v 4 = second (word v 2) (word v 1)
  let branch := if k % 3 = 0 then 4^r else 1
  let rounds := 512*((r+1)*(Nat.clog 2 (k+1)+1)+h+1)
  ∃ (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))),
    m + (∑ C ∈ F, C.card) ≤ 16777216*(k+1)*(r+1)*branch*(h+1)^2*(Nat.clog 2 (3*k+1)+1)*2^h ∧
    (∀ C ∈ F, C.card ≤ 3) ∧
    (∀ v : V → Bool, agrees v ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim v aux) (↑F : Set _)) ∧
    ∀ (rowRev colRev : Bool) (ρ : V → Option Bool),
      let driver := fun j : V => j.1 = 2 ∨
        j.1 = (if rowRev then 3 else 0) ∨ j.1 = (if colRev then 4 else 1)
      (Finset.univ.filter (fun j : V => driver j ∧ ρ j = none)).card ≤ h →
      let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
        {l | ∃ raw : V, l.1 = Sum.inl raw ∧ ρ raw = some l.2}
      let advance := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
        S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
          PEqualNP.Search.negLit other ∈ S}
      let known := (advance^[rounds]) seed
      let complete := fun v : V → Bool => agrees v ∧
        ∀ (raw : V) (sign : Bool), ρ raw = some sign → v raw = sign
      ((¬ ∃ v, complete v) ↔ ∃ C ∈ F, ∀ l ∈ C, PEqualNP.Search.negLit l ∈ known) ∧
      ((∃ v, complete v) → ∀ raw : V, ∀ sign : Bool,
        (∀ v, complete v → v raw = sign) ↔ (Sum.inl raw, sign) ∈ known) := by
  intro k r h hk_odd
  exact PEqualNP.Outside.L_pcx_304_aux.L_pcx_304_core k r h hk_odd
    (512 * ((r + 1) * (Nat.clog 2 (k + 1) + 1) + h + 1))
    (PEqualNP.Outside.L_pcx_304_aux.rounds_budget_ok (h' := min h (3 * k)) (by omega) r h (Nat.min_le_left _ _))
