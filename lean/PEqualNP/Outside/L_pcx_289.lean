import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_289_aux

open PEqualNP.ProofComplexity PEqualNP.Search

/-! ## Section 1: Bit-level word algebra on `Fin k → Bool` -/

def toNat {k : ℕ} (x : Fin k → Bool) : ℕ :=
  ∑ j : Fin k, (x j).toNat * 2 ^ j.val

def ofNat (k w : ℕ) : Fin k → Bool :=
  fun j => w.testBit j.val

theorem toNat_lt {k : ℕ} (x : Fin k → Bool) : toNat x < 2 ^ k := by
  unfold toNat
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have hlt := ih (fun j => x j.castSucc)
    have hle : (x (Fin.last k)).toNat ≤ 1 := by cases x (Fin.last k) <;> simp
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    simp only [Fin.val_castSucc, Fin.val_last]
    nlinarith [Nat.one_le_pow k 2 (by omega)]

theorem testBit_toNat_aux (k : ℕ) (x : Fin k → Bool) (i : ℕ) :
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
    · have hki : k ≤ i := Nat.not_lt.mp hik
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

theorem testBit_toNat {k : ℕ} (x : Fin k → Bool) (i : ℕ) :
    (toNat x).testBit i = if h : i < k then x ⟨i, h⟩ else false :=
  testBit_toNat_aux k x i

theorem testBit_toNat_fin {k : ℕ} (x : Fin k → Bool) (i : Fin k) :
    (toNat x).testBit i.val = x i := by
  rw [testBit_toNat]; simp [i.isLt]

theorem ofNat_toNat {k : ℕ} (x : Fin k → Bool) : ofNat k (toNat x) = x := by
  ext i
  exact testBit_toNat_fin x i

theorem toNat_inj {k : ℕ} {x y : Fin k → Bool} (h : toNat x = toNat y) : x = y := by
  have := congrArg (ofNat k) h
  simpa [ofNat_toNat] using this

theorem toNat_ofNat {k w : ℕ} (hw : w < 2 ^ k) : toNat (ofNat k w) = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat]
  by_cases hi : i < k
  · simp [hi, ofNat]
  · simp only [hi, ↓reduceDIte]
    symm
    apply Nat.testBit_lt_two_pow
    calc w < 2 ^ k := hw
      _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hi)

theorem mod_two_pow_testBit (w k i : ℕ) :
    (w % 2 ^ k).testBit i = if i < k then w.testBit i else false := by
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < k <;> simp [hi]

theorem testBit_xor_apply (a b : ℕ) (i : ℕ) :
    (a ^^^ b).testBit i = xor (a.testBit i) (b.testBit i) :=
  Nat.testBit_xor a b i

theorem xor_toNat {k : ℕ} (x y : Fin k → Bool) :
    toNat (fun i => xor (x i) (y i)) = toNat x ^^^ toNat y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat, Nat.testBit_xor, testBit_toNat, testBit_toNat]
  split <;> simp

theorem testBit_one_ne {p : ℕ} (hp : p ≠ 0) : (1 : ℕ).testBit p = false := by
  cases p with
  | zero => contradiction
  | succ p =>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.div_eq_of_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero p))]

def rotB {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => x ⟨(i.val + k - s % k) % k, Nat.mod_lt _ hk⟩

theorem rot_toNat {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → Bool) :
    ((toNat x <<< (s % k)) ||| (toNat x >>> (k - s % k))) % 2 ^ k =
      toNat (rotB hk s x) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mod_two_pow_testBit, testBit_toNat]
  by_cases hi : i < k
  · simp only [hi, ↓reduceIte, ↓reduceDIte, Nat.testBit_or, Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight]
    set r := s % k
    have hr : r < k := Nat.mod_lt s hk
    by_cases hri : r ≤ i
    · have hb1 : decide (r ≤ i) = true := decide_eq_true hri
      have hb2 : (toNat x).testBit (k - r + i) = false := by
        rw [testBit_toNat]; simp [show ¬ k - r + i < k by omega]
      simp only [hb1, Bool.true_and, hb2, Bool.or_false]
      rw [testBit_toNat]; simp only [show i - r < k by omega, ↓reduceDIte]
      congr 1; rw [Fin.ext_iff]; dsimp [rotB]
      have : (i + k - r) = k + (i - r) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · have hi_lt : i < r := Nat.not_le.mp hri
      have hb1 : decide (r ≤ i) = false := decide_eq_false hri
      simp only [hb1, Bool.false_and, Bool.false_or]
      rw [testBit_toNat]; simp only [show k - r + i < k by omega, ↓reduceDIte]
      congr 1; rw [Fin.ext_iff]; dsimp [rotB]
      have hsub : i + k - r < k := by omega
      rw [Nat.mod_eq_of_lt hsub]; omega
  · simp [hi]

def stepB {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (x i)
    (!(x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩)

theorem step_toNat_aux {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) (m : ℕ) (hm : m ≤ k) :
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
      rw [show (toNat x).testBit m = x ⟨m, by omega⟩ from by rw [testBit_toNat]; simp [show m < k by omega]]
      rw [show (toNat x).testBit ((m + 1) % k) = x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩ from by
        rw [testBit_toNat]; simp [Nat.mod_lt _ hk]]
      rw [show (toNat x).testBit ((m + 2) % k) = x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩ from by
        rw [testBit_toNat]; simp [Nat.mod_lt _ hk]]
      by_cases hik : i < k
      · rw [testBit_toNat, testBit_toNat]; simp only [hik, ↓reduceDIte]
        by_cases him : i < m
        · have hnm : ¬ m ≤ i := by omega
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
            have hmi : m ≤ i := by omega
            have hpos : i - m ≠ 0 := by omega
            simp only [him, hnm1, ↓reduceIte, Bool.false_or, hmi, decide_true, Bool.true_and]
            cases xor (x ⟨m, by omega⟩) (!(x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩)
            · simp
            · change (1 : ℕ).testBit (i - m) = false; exact testBit_one_ne hpos
      · have hmi : m ≤ i := by omega
        have hlt_pow : lhs_prev < 2 ^ i := by
          calc lhs_prev < 2 ^ k := toNat_lt _
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (Nat.not_lt.mp hik)
        rw [Nat.testBit_lt_two_pow hlt_pow, testBit_toNat]; simp only [hik, ↓reduceDIte]
        simp only [Bool.false_or, hmi, decide_true, Bool.true_and]
        have hpos : i - m ≠ 0 := by omega
        cases xor (x ⟨m, by omega⟩) (!(x ⟨(m + 1) % k, Nat.mod_lt _ hk⟩) && x ⟨(m + 2) % k, Nat.mod_lt _ hk⟩)
        · simp
        · change (1 : ℕ).testBit (i - m) = false; exact testBit_one_ne hpos
    exact Nat.eq_of_testBit_eq hbit

theorem step_toNat {k : ℕ} (hk : 0 < k) (x : Fin k → Bool) :
    (List.range k).foldl (fun acc i =>
      acc ||| ((xor ((toNat x).testBit i)
        (!((toNat x).testBit ((i + 1) % k)) && (toNat x).testBit ((i + 2) % k))).toNat <<< i)) 0 =
    toNat (stepB hk x) := by
  rw [step_toNat_aux hk x k (le_refl k)]
  congr 1; ext j; simp [j.isLt]

def mixB {k : ℕ} (hk : 0 < k) (δ : ℕ) (x : Fin k → Bool) : Fin k → Bool :=
  fun i => xor (xor (x i) (rotB hk δ x i)) (rotB hk (k - δ % k) x i)

theorem mixB_toNat {k : ℕ} (hk : 0 < k) (δ : ℕ) (x : Fin k → Bool) :
    toNat x ^^^ ((toNat x <<< (δ % k)) ||| (toNat x >>> (k - δ % k))) % 2 ^ k ^^^
      ((toNat x <<< ((k - δ % k) % k)) ||| (toNat x >>> (k - (k - δ % k) % k))) % 2 ^ k =
    toNat (mixB hk δ x) := by
  rw [rot_toNat hk δ x, rot_toNat hk (k - δ % k) x, ← xor_toNat, ← xor_toNat]
  rfl

/-! ## Section 2: Exact Inverses (`invChiB`, `invMixB`) -/

def affId : Bool × Bool := (true, false)

def affComp (f g : Bool × Bool) : Bool × Bool :=
  (f.1 && g.1, xor f.2 (f.1 && g.2))

theorem affComp_assoc (f g h : Bool × Bool) :
    affComp (affComp f g) h = affComp f (affComp g h) := by
  rcases f with ⟨a1, b1⟩; rcases g with ⟨a2, b2⟩; rcases h with ⟨a3, b3⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases a3 <;> cases b3 <;> rfl

theorem affComp_id_left (f : Bool × Bool) : affComp affId f = f := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem affComp_id_right (f : Bool × Bool) : affComp f affId = f := by
  rcases f with ⟨a, b⟩; cases a <;> cases b <;> rfl

def affEval (f : Bool × Bool) (t : Bool) : Bool :=
  xor f.2 (f.1 && t)

theorem affEval_comp (f g : Bool × Bool) (t : Bool) :
    affEval (affComp f g) t = affEval f (affEval g t) := by
  rcases f with ⟨a1, b1⟩; rcases g with ⟨a2, b2⟩
  cases a1 <;> cases b1 <;> cases a2 <;> cases b2 <;> cases t <;> rfl

def stride2Idx (k p : ℕ) (hk : 0 < k) : Fin k :=
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

def stride2Inv (k : ℕ) (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val * ((k + 1) / 2)) % k, Nat.mod_lt _ hk⟩

theorem stride2_right_inv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (i : Fin k) :
    stride2Idx k (stride2Inv k hk i).val hk = i := by
  ext; dsimp [stride2Idx, stride2Inv]
  rw [odd_div_two_mul hk hk_odd i.val, Nat.mod_eq_of_lt i.isLt]

theorem stride2_left_inv {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (p : Fin k) :
    stride2Inv k hk (stride2Idx k p.val hk) = p := by
  ext; dsimp [stride2Idx, stride2Inv]
  have h1 : ((2 * p.val) % k * ((k + 1) / 2)) % k = (p.val * (2 * ((k + 1) / 2))) % k := by
    rw [Nat.mod_mul_mod]; ring_nf
  have h2k : 2 * ((k + 1) / 2) = k + 1 := by omega
  rw [h1, h2k, show p.val * (k + 1) = p.val * k + p.val by ring, Nat.add_mod, Nat.mul_mod_left,
    Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt p.isLt]

def chiMapAt {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) (p : Fin k) : Bool × Bool :=
  let i := stride2Idx k p.val hk
  (!(y ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩), y i)

def chiList {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) : List (Bool × Bool) :=
  List.ofFn (chiMapAt hk y)

def invChiAt {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) (p : Fin k) : Bool :=
  let hs := chiList hk y
  let pref := (hs.take p.val).foldl affComp affId
  let suf := (hs.drop p.val).foldr affComp affId
  (affComp suf pref).2

def invChiB {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) : Fin k → Bool :=
  fun i => invChiAt hk y (stride2Inv k hk i)

theorem foldr_affComp_drop (l : List (Bool × Bool)) (p : ℕ) (hp : p < l.length) :
    (l.drop p).foldr affComp affId = affComp l[p] ((l.drop (p + 1)).foldr affComp affId) := by
  rw [List.drop_eq_getElem_cons hp, List.foldr_cons]

theorem foldl_affComp_take_succ (l : List (Bool × Bool)) (p : ℕ) (hp : p < l.length) :
    (l.take (p + 1)).foldl affComp affId = affComp ((l.take p).foldl affComp affId) l[p] := by
  rw [List.take_succ_eq_append_getElem hp, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem fold_affComp_split (l : List (Bool × Bool)) (init : Bool × Bool) :
    l.foldl affComp init = affComp init (l.foldr affComp affId) := by
  induction l generalizing init with
  | nil => simp [affComp_id_right]
  | cons a t ih =>
    simp only [List.foldl_cons, List.foldr_cons]
    rw [ih (affComp init a), affComp_assoc]

theorem foldl_affComp_all_eq_foldr (l : List (Bool × Bool)) (p : ℕ) :
    affComp ((l.take p).foldl affComp affId) ((l.drop p).foldr affComp affId) =
      l.foldr affComp affId := by
  rw [fold_affComp_split, affComp_id_left]
  induction p generalizing l with
  | zero => simp [affComp_id_left]
  | succ p ih =>
    cases l with
    | nil => simp [affComp_id_left]
    | cons a t =>
      simp only [List.take_succ_cons, List.drop_succ_cons, List.foldr_cons]
      rw [affComp_assoc, ih t]

theorem affComp_fst_eq_all (l : List (Bool × Bool)) :
    (l.foldr affComp affId).1 = l.all (fun x => x.1) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldr_cons, affComp, List.all_cons, ih]

theorem step_stepB_key (x y : Fin k → Bool) (hk : 0 < k) (hy : y = stepB hk x) (i : Fin k) :
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

theorem stepB_zero_eq {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (x : Fin k → Bool)
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
      x ⟨(i0.val + 2 * n) % k, Nat.mod_lt _ hk⟩ = true ∧
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

theorem invChiB_zero {k : ℕ} (hk : 0 < k) (y : Fin k → Bool) (hy : ∀ q : Fin k, y q = false) :
    invChiB hk y = fun _ => false := by
  ext i
  dsimp [invChiB, invChiAt]
  have hs_snd : ∀ g ∈ chiList hk y, g.2 = false := by
    intro g hg
    simp only [chiList, List.mem_ofFn] at hg
    obtain ⟨p, rfl⟩ := hg
    exact hy _
  have htake : ∀ n (l : List (Bool × Bool)), (∀ g ∈ l, g.2 = false) →
      ((l.take n).foldl affComp affId).2 = false := by
    intro n l hl
    have hfold : ∀ (ll : List (Bool × Bool)) (init : Bool × Bool),
        init.2 = false → (∀ g ∈ ll, g.2 = false) → (ll.foldl affComp init).2 = false := by
      intro ll
      induction ll with
      | nil => intro init h _; exact h
      | cons a t ih =>
        intro init h1 h2
        apply ih
        · dsimp [affComp]; simp [h1, h2 a List.mem_cons_self]
        · intro g hg; exact h2 g (List.mem_cons_of_mem _ hg)
    exact hfold _ _ rfl (fun g hg => hl g (List.mem_of_mem_take hg))
  have hdrop : ∀ n (l : List (Bool × Bool)), (∀ g ∈ l, g.2 = false) →
      ((l.drop n).foldr affComp affId).2 = false := by
    intro n l hl
    have hfold : ∀ (ll : List (Bool × Bool)),
        (∀ g ∈ ll, g.2 = false) → (ll.foldr affComp affId).2 = false := by
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
  | nil => simp [affComp_id_left]
  | cons a t ih =>
    simp only [List.cons_append, List.foldr_cons, ih, affComp_assoc]

theorem invChiB_stepB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (x : Fin k → Bool) :
    invChiB hk (stepB hk x) = x := by
  by_cases hy : ∃ q : Fin k, stepB hk x q = true
  · set y := stepB hk x
    have hstep_rec : ∀ p : Fin k, x (stride2Idx k p.val hk) =
        affEval (chiMapAt hk y p) (x (stride2Idx k (⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk)) := by
      intro p
      set i := stride2Idx k p.val hk
      have hi2 : stride2Idx k (⟨(p.val + 1) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk =
          ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩ := by
        rw [Fin.ext_iff]; dsimp [stride2Idx, i]
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
        x (stride2Idx k p.val hk) =
        affEval (((List.range n).map (fun d =>
          chiMapAt hk y ⟨(p.val + d) % k, Nat.mod_lt _ hk⟩)).foldr affComp affId)
          (x (stride2Idx k (⟨(p.val + n) % k, Nat.mod_lt _ hk⟩ : Fin k).val hk)) := by
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
    set p := stride2Inv k hk i
    have hi_eq : stride2Idx k p.val hk = i := stride2_right_inv hk hk_odd i
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
      rw [fold_affComp_split, affComp_id_left]
    set M_p := affComp ((hs.drop p.val).foldr affComp affId) ((hs.take p.val).foldl affComp affId)
    have hMp_fst : M_p.1 = false := by
      have h1 : M_p.1 = (((hs.take p.val).foldl affComp affId).1 &&
          ((hs.drop p.val).foldr affComp affId).1) :=
        Bool.and_comm _ _
      have heq := congrArg Prod.fst (foldl_affComp_all_eq_foldr hs p.val)
      have hall : (hs.foldr affComp affId).1 = false := by
        rw [affComp_fst_eq_all]
        obtain ⟨q, hq⟩ := hy
        let q1 : Fin k := ⟨(q.val + k - 1) % k, Nat.mod_lt _ hk⟩
        let r := stride2Inv k hk q1
        have hr : (chiMapAt hk y r).1 = false := by
          dsimp [chiMapAt, r]
          have hst : (stride2Idx k (stride2Inv k hk q1).val hk).val = q1.val :=
            congrArg Fin.val (stride2_right_inv hk hk_odd q1)
          have hmod : (q1.val + 1) % k = q.val := by
            dsimp [q1]; rw [Nat.mod_add_mod]
            have : q.val + k - 1 + 1 = q.val + k := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt]
          have hfin : (⟨((stride2Idx k (stride2Inv k hk q1).val hk).val + 1) % k,
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

theorem stepB_invChiB {k : ℕ} (hk : 0 < k) (hk_odd : k % 2 = 1) (y : Fin k → Bool) :
    stepB hk (invChiB hk y) = y := by
  have hinj : Function.Injective (stepB hk) :=
    Function.LeftInverse.injective (invChiB_stepB hk hk_odd)
  have hsurj : Function.Surjective (stepB hk) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj y
  rw [invChiB_stepB hk hk_odd]

/-! ### Inverse Mix -/

def inv3Pos (k : ℕ) : ℕ :=
  if k % 6 = 1 then 4 * (k / 6) + 1 else 2 * (k / 6) + 2

def inv3dConst (k δ : ℕ) : ℕ :=
  if δ = 1 then inv3Pos k else (inv3Pos k * ((k + 1) / 2)) % k

theorem inv3dConst_spec {k δ : ℕ} (hk6 : k % 6 = 1 ∨ k % 6 = 5) (hk5 : 5 ≤ k)
    (hδ : δ = 1 ∨ δ = 2) :
    (3 * δ * inv3dConst k δ) % k = 1 := by
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
  · simpa [inv3dConst] using hpos
  · simp only [inv3dConst, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
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
  ⟨(i.val * inv3dConst k δ) % k, Nat.mod_lt _ hk⟩

theorem m3d_right_inv {k δ : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) (hk5 : 5 ≤ k)
    (hδ : δ = 1 ∨ δ = 2) (i : Fin k) :
    m3dIdx k δ (m3dInv k δ hk i).val hk = i := by
  ext; dsimp [m3dIdx, m3dInv]
  calc (3 * δ * ((i.val * inv3dConst k δ) % k)) % k
      = (3 * δ * (i.val * inv3dConst k δ)) % k := Nat.mul_mod_mod _ _ k
    _ = (i.val * (3 * δ * inv3dConst k δ)) % k := by ring_nf
    _ = ((i.val % k) * ((3 * δ * inv3dConst k δ) % k)) % k := Nat.mul_mod _ _ k
    _ = (i.val % k * 1) % k := by rw [inv3dConst_spec hk6 hk5 hδ]
    _ = i.val := by rw [Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt i.isLt]

def mixDiffAt {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) (p : Fin k) : Bool :=
  xor (y ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩)
      (y ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩)

def mixPref {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) (p : ℕ) : Bool :=
  ((List.range p).map (fun j => mixDiffAt hk δ y ⟨j % k, Nat.mod_lt _ hk⟩)).foldl xor false

def invMixB {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) : Fin k → Bool :=
  if k < 5 then y
  else
    let pPos : ℕ := inv3Pos k % k
    let pNeg : ℕ := (k - pPos) % k
    let x0 : Bool := xor (xor (y ⟨0, hk⟩) (mixPref hk δ y pPos)) (mixPref hk δ y pNeg)
    fun i => xor x0 (mixPref hk δ y (m3dInv k δ hk i).val)

theorem mixPref_succ {k : ℕ} (hk : 0 < k) (δ : ℕ) (y : Fin k → Bool) (p : ℕ) :
    mixPref hk δ y (p + 1) = xor (mixPref hk δ y p) (mixDiffAt hk δ y ⟨p % k, Nat.mod_lt _ hk⟩) := by
  dsimp [mixPref]
  rw [List.range_succ, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem mixB_one {k : ℕ} (hk : 0 < k) (hk1 : k = 1) (δ : ℕ) (x : Fin k → Bool) :
    mixB hk δ x = x := by
  subst hk1
  ext i
  have hi : i = ⟨0, hk⟩ := Fin.ext (by omega)
  subst hi
  dsimp [mixB, rotB]
  have h0 : ∀ a : ℕ, (⟨a % 1, Nat.mod_lt _ hk⟩ : Fin 1) = ⟨0, hk⟩ := fun a => Fin.ext (Nat.mod_one a)
  rw [h0, h0]
  cases h : x ⟨0, hk⟩ <;> simp [h]

theorem invMixB_mixB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (x : Fin k → Bool) :
    invMixB hk δ (mixB hk δ x) = x := by
  by_cases hk5 : k < 5
  · have hk1 : k = 1 := by omega
    dsimp [invMixB]
    simp only [hk5, ↓reduceIte]
    exact mixB_one hk hk1 δ x
  · have h5 : 5 ≤ k := Nat.not_lt.mp hk5
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
        simpa [inv3dConst] using this
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
        have hge : 2 ≤ m := by omega
        have hkm : 2 * k ≤ k * m := by linarith [Nat.mul_le_mul_left k hge]
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

theorem mixB_invMixB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (δ : ℕ) (hδ : δ = 1 ∨ δ = 2) (y : Fin k → Bool) :
    mixB hk δ (invMixB hk δ y) = y := by
  have hinj : Function.Injective (mixB hk δ) :=
    Function.LeftInverse.injective (invMixB_mixB hk hk6 δ hδ)
  have hsurj : Function.Surjective (mixB hk δ) := Finite.injective_iff_surjective.mp hinj
  obtain ⟨x, rfl⟩ := hsurj y
  rw [invMixB_mixB hk hk6 δ hδ]


/-! ## Section 3: Five-word relations, Blelloch scan, and Tseitin circuit compiler -/

def constBit (k j : ℕ) (i : Fin k) : Bool :=
  (3 ^ (k + j) % 2 ^ k).testBit i.val

theorem toNat_constBit {k j : ℕ} :
    toNat (constBit k j) = 3 ^ (k + j) % 2 ^ k := by
  unfold constBit
  exact toNat_ofNat (Nat.mod_lt _ (Nat.pow_pos (by omega)))

def firstB {k : ℕ} (hk : 0 < k) (r : ℕ) (rowKey rowName : Fin k → Bool) : Fin k → Bool :=
  (List.range r).foldl
    (fun rowState rowIndex =>
      fun i =>
        xor (xor (stepB hk (mixB hk 1 rowState) i) (rotB hk (2 * rowIndex) rowKey i))
          (constBit k (rowIndex + 1) i))
    (fun i => xor (rotB hk 1 rowKey i) (rowName i))

def secondB {k : ℕ} (hk : 0 < k) (r : ℕ) (colKey colName : Fin k → Bool) : Fin k → Bool :=
  (List.range r).foldl
    (fun colState colIndex =>
      fun i =>
        xor (xor (stepB hk (mixB hk 2 colState) i) (rotB hk (3 * (colIndex + 1) + 1) colKey i))
          (constBit k (r + (colIndex + 1)) i))
    (fun i => xor (rotB hk 3 colKey i) (colName i))

theorem foldl_range_toNat {k : ℕ} (r : ℕ)
    (fn : ℕ → ℕ → ℕ) (fb : (Fin k → Bool) → ℕ → (Fin k → Bool))
    (init : Fin k → Bool)
    (hstep : ∀ (x : Fin k → Bool) (idx : ℕ), fn (toNat x) idx = toNat (fb x idx)) :
    (List.range r).foldl fn (toNat init) = toNat ((List.range r).foldl fb init) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.foldl_cons, List.foldl_nil, ih, hstep]

theorem firstB_toNat {k : ℕ} (hk : 0 < k) (r : ℕ) (rowKey rowName : Fin k → Bool) :
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

theorem secondB_toNat {k : ℕ} (hk : 0 < k) (r : ℕ) (colKey colName : Fin k → Bool) :
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
      rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | hk3
      · rfl
      · rfl
      · rw [Nat.mod_eq_of_lt (by omega : 2 < k)]
    congr 1; exact congrArg x (Fin.ext (by dsimp; rw [hmod]))
  rw [← hm, step_toNat hk (mixB hk 2 x), rot_toNat hk (3 * (idx + 1) + 1) colKey,
    ← toNat_constBit (k := k) (j := r + (idx + 1)), ← xor_toNat, ← xor_toNat]

def invFirstRoundB' {k : ℕ} (hk : 0 < k) (rIdx : ℕ) (rowKey y : Fin k → Bool) : Fin k → Bool :=
  invMixB hk 1 (invChiB hk (fun i =>
    xor (xor (y i) (rotB hk (2 * rIdx) rowKey i)) (constBit k (rIdx + 1) i)))

def invFirstB {k : ℕ} (hk : 0 < k) (r : ℕ) (rowKey out : Fin k → Bool) : Fin k → Bool :=
  let rowState0 := (List.range r).reverse.foldl (fun st rIdx => invFirstRoundB' hk rIdx rowKey st) out
  fun i => xor (rotB hk 1 rowKey i) (rowState0 i)

def invSecondRoundB {k : ℕ} (hk : 0 < k) (r colIdx : ℕ) (colKey y : Fin k → Bool) : Fin k → Bool :=
  invMixB hk 2 (invChiB hk (fun i =>
    xor (xor (y i) (rotB hk (3 * (colIdx + 1) + 1) colKey i)) (constBit k (r + (colIdx + 1)) i)))

def invSecondB {k : ℕ} (hk : 0 < k) (r : ℕ) (colKey out : Fin k → Bool) : Fin k → Bool :=
  let colState0 := (List.range r).reverse.foldl (fun st colIdx => invSecondRoundB hk r colIdx colKey st) out
  fun i => xor (rotB hk 3 colKey i) (colState0 i)

theorem invFirstRoundB'_spec {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (rIdx : ℕ) (rowKey st : Fin k → Bool) :
    invFirstRoundB' hk rIdx rowKey (fun i =>
      xor (xor (stepB hk (mixB hk 1 st) i) (rotB hk (2 * rIdx) rowKey i))
        (constBit k (rIdx + 1) i)) = st := by
  have hk_odd : k % 2 = 1 := by omega
  dsimp [invFirstRoundB']
  have hfun : (fun i => xor (xor (xor (xor (stepB hk (mixB hk 1 st) i)
      (rotB hk (2 * rIdx) rowKey i)) (constBit k (rIdx + 1) i))
      (rotB hk (2 * rIdx) rowKey i)) (constBit k (rIdx + 1) i)) =
      stepB hk (mixB hk 1 st) := by
    ext i
    cases stepB hk (mixB hk 1 st) i <;> cases rotB hk (2 * rIdx) rowKey i <;>
      cases constBit k (rIdx + 1) i <;> rfl
  rw [hfun, invChiB_stepB hk hk_odd, invMixB_mixB hk hk6 1 (Or.inl rfl)]

theorem invSecondRoundB_spec {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r colIdx : ℕ) (colKey st : Fin k → Bool) :
    invSecondRoundB hk r colIdx colKey (fun i =>
      xor (xor (stepB hk (mixB hk 2 st) i) (rotB hk (3 * (colIdx + 1) + 1) colKey i))
        (constBit k (r + (colIdx + 1)) i)) = st := by
  have hk_odd : k % 2 = 1 := by omega
  dsimp [invSecondRoundB]
  have hfun : (fun i => xor (xor (xor (xor (stepB hk (mixB hk 2 st) i)
      (rotB hk (3 * (colIdx + 1) + 1) colKey i)) (constBit k (r + (colIdx + 1)) i))
      (rotB hk (3 * (colIdx + 1) + 1) colKey i)) (constBit k (r + (colIdx + 1)) i)) =
      stepB hk (mixB hk 2 st) := by
    ext i
    cases stepB hk (mixB hk 2 st) i <;> cases rotB hk (3 * (colIdx + 1) + 1) colKey i <;>
      cases constBit k (r + (colIdx + 1)) i <;> rfl
  rw [hfun, invChiB_stepB hk hk_odd, invMixB_mixB hk hk6 2 (Or.inr rfl)]

theorem invFirstB_firstB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : ℕ) (rowKey rowName : Fin k → Bool) :
    invFirstB hk r rowKey (firstB hk r rowKey rowName) = rowName := by
  have hfold : ∀ (l : List ℕ) (st : Fin k → Bool),
      l.reverse.foldl (fun s idx => invFirstRoundB' hk idx rowKey s)
        (l.foldl (fun s idx => fun i =>
          xor (xor (stepB hk (mixB hk 1 s) i) (rotB hk (2 * idx) rowKey i))
            (constBit k (idx + 1) i)) st) = st := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons a t ih =>
      intro st
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih, invFirstRoundB'_spec hk hk6]
  dsimp [invFirstB, firstB]
  rw [hfold]
  ext i
  cases rotB hk 1 rowKey i <;> cases rowName i <;> rfl

theorem invSecondB_secondB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : ℕ) (colKey colName : Fin k → Bool) :
    invSecondB hk r colKey (secondB hk r colKey colName) = colName := by
  have hfold : ∀ (l : List ℕ) (st : Fin k → Bool),
      l.reverse.foldl (fun s idx => invSecondRoundB hk r idx colKey s)
        (l.foldl (fun s idx => fun i =>
          xor (xor (stepB hk (mixB hk 2 s) i) (rotB hk (3 * (idx + 1) + 1) colKey i))
            (constBit k (r + (idx + 1)) i)) st) = st := by
    intro l
    induction l with
    | nil => intro st; rfl
    | cons a t ih =>
      intro st
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [ih, invSecondRoundB_spec hk hk6]
  dsimp [invSecondB, secondB]
  rw [hfold]
  ext i
  cases rotB hk 3 colKey i <;> cases colName i <;> rfl

/-! ### Circuit Builder and Blelloch Prefix Scan -/

structure GateDef (k : ℕ) where
  op : Bool → Bool → Bool
  a : Sum (Fin 5 × Fin k) ℕ
  b : Sum (Fin 5 × Fin k) ℕ
  depth : ℕ
  owner : Fin 5

structure WNode (k : ℕ) where
  wire : Sum (Fin 5 × Fin k) ℕ
  depth : ℕ

def readW {k : ℕ} (v : Fin 5 × Fin k → Bool) (vals : List Bool) : Sum (Fin 5 × Fin k) ℕ → Bool
  | Sum.inl j => v j
  | Sum.inr i => vals.getD i false

def stepEval {k : ℕ} (v : Fin 5 × Fin k → Bool) (vals : List Bool) (g : GateDef k) : List Bool :=
  vals ++ [g.op (readW v vals g.a) (readW v vals g.b)]

def evalList {k : ℕ} (v : Fin 5 × Fin k → Bool) (st : List (GateDef k)) : List Bool :=
  st.foldl (stepEval v) []

def evalW {k : ℕ} (v : Fin 5 × Fin k → Bool) (st : List (GateDef k)) (w : Sum (Fin 5 × Fin k) ℕ) : Bool :=
  readW v (evalList v st) w

theorem foldl_stepEval_len {k : ℕ} (v : Fin 5 × Fin k → Bool) (gs : List (GateDef k)) (vals : List Bool) :
    (gs.foldl (stepEval v) vals).length = vals.length + gs.length := by
  induction gs generalizing vals with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, stepEval, List.length_append, List.length_cons, List.length_nil]
    omega

theorem evalList_length {k : ℕ} (v : Fin 5 × Fin k → Bool) (st : List (GateDef k)) :
    (evalList v st).length = st.length := by
  simpa [evalList] using foldl_stepEval_len v st []

theorem foldl_stepEval_getD_lt {k : ℕ} (v : Fin 5 × Fin k → Bool) (gs : List (GateDef k))
    (vals : List Bool) (i : ℕ) (hi : i < vals.length) :
    (gs.foldl (stepEval v) vals).getD i false = vals.getD i false := by
  induction gs generalizing vals with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepEval v vals g).length := by
      simp only [stepEval, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih _ hlt]
    simp only [stepEval, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem evalList_append_getD_lt {k : ℕ} (v : Fin 5 × Fin k → Bool)
    (st more : List (GateDef k)) (i : ℕ) (hi : i < st.length) :
    (evalList v (st ++ more)).getD i false = (evalList v st).getD i false := by
  dsimp [evalList]
  rw [List.foldl_append]
  apply foldl_stepEval_getD_lt
  rw [← evalList]
  rw [evalList_length]; exact hi

theorem evalList_append_last {k : ℕ} (v : Fin 5 × Fin k → Bool)
    (st : List (GateDef k)) (g : GateDef k) :
    (evalList v (st ++ [g])).getD st.length false =
      g.op (evalW v st g.a) (evalW v st g.b) := by
  dsimp [evalList, evalW]
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  dsimp [stepEval]
  have hlen : (st.foldl (stepEval v) []).length = st.length := evalList_length v st
  rw [← hlen]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

def ValidWire {k : ℕ} (owner : Fin 5) (st : List (GateDef k)) : Sum (Fin 5 × Fin k) ℕ → ℕ → Prop
  | Sum.inl (t, _), _ => t = 2 ∨ t = owner
  | Sum.inr j, d => ∃ h : j < st.length, (st[j].owner = 2 ∨ st[j].owner = owner) ∧ st[j].depth ≤ d

def WF {k : ℕ} (st : List (GateDef k)) : Prop :=
  ∀ (i : ℕ) (hi : i < st.length),
    ValidWire st[i].owner (st.take i) st[i].a (st[i].depth - 1) ∧
    ValidWire st[i].owner (st.take i) st[i].b (st[i].depth - 1) ∧
    1 ≤ st[i].depth ∧
    (st[i].owner = 2 → st[i].depth = 1)

theorem ValidWire_mono {k : ℕ} {owner : Fin 5} {st : List (GateDef k)} (more : List (GateDef k))
    {w : Sum (Fin 5 × Fin k) ℕ} {d1 d2 : ℕ} (hd : d1 ≤ d2)
    (hv : ValidWire owner st w d1) :
    ValidWire owner (st ++ more) w d2 := by
  cases w with
  | inl p => exact hv
  | inr j =>
    obtain ⟨hj, ho, hd1⟩ := hv
    refine ⟨by simp; omega, ?_, ?_⟩
    · rw [List.getElem_append_left hj]; exact ho
    · rw [List.getElem_append_left hj]; omega

theorem ValidWire_take_mono {k : ℕ} {owner : Fin 5} {st : List (GateDef k)}
    {i : ℕ} (hi : i ≤ st.length) {w : Sum (Fin 5 × Fin k) ℕ} {d : ℕ}
    (hv : ValidWire owner (st.take i) w d) :
    ValidWire owner st w d := by
  cases w with
  | inl p => exact hv
  | inr j =>
    obtain ⟨hj, ho, hd⟩ := hv
    have hj_st : j < st.length := by simp at hj; omega
    simp only [List.getElem_take] at ho hd
    exact ⟨hj_st, ho, hd⟩

theorem evalW_append {k : ℕ} (v : Fin 5 × Fin k → Bool) {owner : Fin 5}
    {st : List (GateDef k)} (more : List (GateDef k)) {w : Sum (Fin 5 × Fin k) ℕ} {d : ℕ}
    (hv : ValidWire owner st w d) :
    evalW v (st ++ more) w = evalW v st w := by
  cases w with
  | inl j => rfl
  | inr i => exact evalList_append_getD_lt v st more i hv.1

theorem evalList_getElem {k : ℕ} (v : Fin 5 × Fin k → Bool) {st : List (GateDef k)} (hwf : WF st)
    (i : ℕ) (hi : i < st.length) :
    (evalList v st).getD i false =
      st[i].op (evalW v st st[i].a) (evalW v st st[i].b) := by
  have htake_len : (st.take i).length = i := by simp; omega
  have h1 : st = (st.take i ++ [st[i]]) ++ st.drop (i + 1) := by
    rw [← List.take_succ_eq_append_getElem hi, List.take_append_drop]
  have hlt1 : i < (st.take i ++ [st[i]]).length := by
    simp only [List.length_append, htake_len, List.length_singleton]; omega
  have ha_valid := (hwf i hi).1
  have hb_valid := (hwf i hi).2.1
  have hst_tail : st = st.take i ++ ([st[i]] ++ st.drop (i + 1)) := by
    rw [← List.append_assoc]; exact h1
  conv_lhs => rw [h1, evalList_append_getD_lt v (st.take i ++ [st[i]]) (st.drop (i + 1)) i hlt1]
  have hlast := evalList_append_last v (st.take i) st[i]
  rw [htake_len] at hlast
  rw [hlast]
  congr 1
  · have := (evalW_append v ([st[i]] ++ st.drop (i + 1)) ha_valid).symm
    rwa [← hst_tail] at this
  · have := (evalW_append v ([st[i]] ++ st.drop (i + 1)) hb_valid).symm
    rwa [← hst_tail] at this

def initGates (k : ℕ) (hk : 0 < k) : List (GateDef k) :=
  let w0 : Sum (Fin 5 × Fin k) ℕ := Sum.inl (2, ⟨0, hk⟩)
  [⟨xor, w0, w0, 1, 2⟩, ⟨fun a b => !(xor a b), w0, w0, 1, 2⟩]

def falseNode {k : ℕ} : WNode k := ⟨Sum.inr 0, 1⟩
def trueNode {k : ℕ} : WNode k := ⟨Sum.inr 1, 1⟩

theorem wf_initGates (k : ℕ) (hk : 0 < k) : WF (initGates k hk) := by
  intro i hi
  simp only [initGates, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    exact ⟨Or.inl rfl, Or.inl rfl, by simp [initGates], fun _ => rfl⟩

theorem valid_constNodes {k : ℕ} (hk : 0 < k) (owner : Fin 5) :
    ValidWire owner (initGates k hk) (falseNode (k := k)).wire 1 ∧
    ValidWire owner (initGates k hk) (trueNode (k := k)).wire 1 := by
  refine ⟨⟨by simp [initGates], Or.inl rfl, le_refl 1⟩, ⟨by simp [initGates], Or.inl rfl, le_refl 1⟩⟩

theorem eval_constNodes {k : ℕ} (hk : 0 < k) (v : Fin 5 × Fin k → Bool) :
    evalW v (initGates k hk) (falseNode (k := k)).wire = false ∧
    evalW v (initGates k hk) (trueNode (k := k)).wire = true := by
  dsimp [evalW, falseNode, trueNode, evalList, initGates, stepEval, readW]
  cases v (2, ⟨0, hk⟩) <;> simp

def addGate {k : ℕ} (st : List (GateDef k)) (owner : Fin 5) (_ho : owner ≠ 2)
    (op : Bool → Bool → Bool) (a b : WNode k) : List (GateDef k) × WNode k :=
  let d := max a.depth b.depth + 1
  (st ++ [⟨op, a.wire, b.wire, d, owner⟩], ⟨Sum.inr st.length, d⟩)

theorem addGate_wf {k : ℕ} (st : List (GateDef k)) (owner : Fin 5) (ho : owner ≠ 2)
    (op : Bool → Bool → Bool) (a b : WNode k)
    (hwf : WF st)
    (ha : ValidWire owner st a.wire a.depth)
    (hb : ValidWire owner st b.wire b.depth) :
    WF (addGate st owner ho op a b).1 ∧
    (∃ more, (addGate st owner ho op a b).1 = st ++ more ∧ more.length = 1) ∧
    ValidWire owner (addGate st owner ho op a b).1 (addGate st owner ho op a b).2.wire
      (addGate st owner ho op a b).2.depth ∧
    (addGate st owner ho op a b).2.depth = max a.depth b.depth + 1 := by
  dsimp [addGate]
  refine ⟨?_, ⟨_, rfl, rfl⟩, ?_, rfl⟩
  · intro i hi
    let g : GateDef k := ⟨op, a.wire, b.wire, max a.depth b.depth + 1, owner⟩
    by_cases hil : i < st.length
    · have htake : (st ++ [g]).take i = st.take i :=
        List.take_append_of_le_length (le_of_lt hil)
      have hget : (st ++ [g])[i]'hi = st[i]'hil :=
        List.getElem_append_left hil
      change ValidWire (st ++ [g])[i].owner ((st ++ [g]).take i) (st ++ [g])[i].a ((st ++ [g])[i].depth - 1) ∧
        ValidWire (st ++ [g])[i].owner ((st ++ [g]).take i) (st ++ [g])[i].b ((st ++ [g])[i].depth - 1) ∧
        1 ≤ (st ++ [g])[i].depth ∧ ((st ++ [g])[i].owner = 2 → (st ++ [g])[i].depth = 1)
      rw [htake, hget]
      exact hwf i hil
    · have hieq : i = st.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hi; omega
      subst hieq
      have htake : (st ++ [g]).take st.length = st := by simp
      have hget : (st ++ [g])[st.length]'hi = g := by simp
      change ValidWire (st ++ [g])[st.length].owner ((st ++ [g]).take st.length) (st ++ [g])[st.length].a
          ((st ++ [g])[st.length].depth - 1) ∧
        ValidWire (st ++ [g])[st.length].owner ((st ++ [g]).take st.length) (st ++ [g])[st.length].b
          ((st ++ [g])[st.length].depth - 1) ∧
        1 ≤ (st ++ [g])[st.length].depth ∧ ((st ++ [g])[st.length].owner = 2 → (st ++ [g])[st.length].depth = 1)
      rw [htake, hget]
      refine ⟨?_, ?_, by dsimp [g]; omega, fun h2 => absurd h2 ho⟩
      · simpa [g] using ValidWire_mono ([] : List (GateDef k)) (le_max_left _ _) ha
      · simpa [g] using ValidWire_mono ([] : List (GateDef k)) (le_max_right _ _) hb
  · refine ⟨by simp, ?_, ?_⟩
    · rw [List.getElem_append_right (le_refl _)]; simp
    · rw [List.getElem_append_right (le_refl _)]; simp

theorem addGate_eval {k : ℕ} (v : Fin 5 × Fin k → Bool)
    (st : List (GateDef k)) (owner : Fin 5) (ho : owner ≠ 2)
    (op : Bool → Bool → Bool) (a b : WNode k) :
    evalW v (addGate st owner ho op a b).1 (addGate st owner ho op a b).2.wire =
      op (evalW v st a.wire) (evalW v st b.wire) := by
  dsimp [addGate, evalW]
  exact evalList_append_last v st ⟨op, a.wire, b.wire, max a.depth b.depth + 1, owner⟩

/-! ### Blelloch Exclusive Scan on `List α` -/

def gPairUp {S α : Type} (comb : S → α → α → S × α) (st : S) : List α → S × List α
  | [] => (st, [])
  | [a] => (st, [a])
  | a :: b :: rest =>
    let (st1, c) := comb st a b
    let (st2, cs) := gPairUp comb st1 rest
    (st2, c :: cs)

theorem gPairUp_len {S α : Type} (comb : S → α → α → S × α) (st : S) (xs : List α) :
    (gPairUp comb st xs).2.length = (xs.length + 1) / 2 := by
  match xs with
  | [] => simp [gPairUp]
  | [a] => simp [gPairUp]
  | a :: b :: rest =>
    simp only [gPairUp, List.length_cons]
    rw [gPairUp_len comb _ rest]
    omega

def gExpandDown {S α : Type} (comb : S → α → α → S × α) (st : S) : List α → List α → S × List α
  | p :: ps, a :: _ :: rest =>
    let (st1, o) := comb st p a
    let (st2, cs) := gExpandDown comb st1 ps rest
    (st2, p :: o :: cs)
  | p :: _, [_] => (st, [p])
  | _, _ => (st, [])

def gScanExcl {S α : Type} (comb : S → α → α → S × α) (idVal : α) (st : S) (xs : List α) : S × List α :=
  if h : xs.length ≤ 1 then
    match xs with
    | [] => (st, [])
    | [_] => (st, [idVal])
  else
    let res1 := gPairUp comb st xs
    have hlt : res1.2.length < xs.length := by
      rw [gPairUp_len]; omega
    let res2 := gScanExcl comb idVal res1.1 res1.2
    gExpandDown comb res2.1 res2.2 xs
termination_by xs.length

theorem gExpandDown_len {S α : Type} (comb : S → α → α → S × α) (st : S) (ps xs : List α)
    (hlen : ps.length = (xs.length + 1) / 2) :
    (gExpandDown comb st ps xs).2.length = xs.length := by
  match ps, xs with
  | p :: ps, a :: _ :: rest =>
    simp only [gExpandDown, List.length_cons]
    rw [gExpandDown_len comb _ ps rest (by simp at hlen; omega)]
  | p :: _, [_] => simp [gExpandDown]
  | [], [] => simp [gExpandDown]
  | [], _ :: _ :: _ => simp at hlen; omega
  | [], [_] => simp at hlen
  | _ :: _, [] => simp at hlen

theorem gScanExcl_spec {k : ℕ} {α M : Type}
    (comb : List (GateDef k) → α → α → List (GateDef k) × α)
    (evalA : List (GateDef k) → α → M)
    (depthA : α → ℕ)
    (validA : List (GateDef k) → α → Prop)
    (opM : M → M → M) (idM : M) (idVal : α)
    (h_assoc : ∀ x y z : M, opM (opM x y) z = opM x (opM y z))
    (cCost dc : ℕ)
    (h_mono : ∀ (st more : List (GateDef k)) (a : α),
      validA st a → validA (st ++ more) a ∧ evalA (st ++ more) a = evalA st a)
    (h_comb : ∀ (st : List (GateDef k)) (a b : α),
      WF st → validA st a → validA st b →
      let (st', c) := comb st a b
      WF st' ∧ (∃ more, st' = st ++ more ∧ more.length ≤ cCost) ∧
      validA st' c ∧ evalA st' c = opM (evalA st a) (evalA st b) ∧
      depthA c ≤ max (depthA a) (depthA b) + dc) :
    ∀ (xs : List α) (st : List (GateDef k)) (d0 : ℕ),
      WF st → validA st idVal → evalA st idVal = idM → depthA idVal ≤ d0 →
      (∀ a ∈ xs, validA st a ∧ depthA a ≤ d0) →
      let (st', outs) := gScanExcl comb idVal st xs
      WF st' ∧
      (∃ more, st' = st ++ more ∧ more.length ≤ 2 * xs.length * cCost) ∧
      outs.length = xs.length ∧
      (∀ (i : ℕ) (hi : i < outs.length),
        validA st' outs[i] ∧
        depthA outs[i] ≤ d0 + 2 * dc * Nat.clog 2 xs.length ∧
        evalA st' outs[i] = ((xs.take i).map (evalA st)).foldl opM idM) := by
  intro xs
  induction hn_eq : xs.length using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
    subst hn_eq
    intro st d0 hwf hid hid_ev hdid hxs
    unfold gScanExcl
    split_ifs with hlen1
    · cases xs with
      | nil =>
        refine ⟨hwf, ⟨[], (List.append_nil st).symm, by simp⟩, rfl, fun i hi => by simp at hi⟩
      | cons a rest =>
        cases rest with
        | nil =>
          refine ⟨hwf, ⟨[], (List.append_nil st).symm, by simp⟩, rfl, fun i hi => ?_⟩
          have hi0 : i = 0 := by simp at hi; omega
          subst hi0
          have hclog : Nat.clog 2 1 = 0 := by decide
          refine ⟨hid, by simp [hdid, hclog], ?_⟩
          simp [hid_ev]
        | cons b bs =>
          simp at hlen1
    · have hn2 : 2 ≤ xs.length := by omega
      have hpair : ∀ (m : ℕ) (ys : List α), ys.length = m → ∀ (st0 : List (GateDef k)),
          WF st0 → (∀ a ∈ ys, validA st0 a ∧ depthA a ≤ d0) →
          WF (gPairUp comb st0 ys).1 ∧
          (∃ more, (gPairUp comb st0 ys).1 = st0 ++ more ∧ more.length ≤ (ys.length / 2) * cCost) ∧
          (gPairUp comb st0 ys).2.length = (ys.length + 1) / 2 ∧
          (∀ (q : ℕ) (hq : q < (gPairUp comb st0 ys).2.length),
            validA (gPairUp comb st0 ys).1 (gPairUp comb st0 ys).2[q] ∧
            depthA (gPairUp comb st0 ys).2[q] ≤ d0 + dc ∧
            if h2 : 2 * q + 1 < ys.length then
              evalA (gPairUp comb st0 ys).1 (gPairUp comb st0 ys).2[q] =
                opM (evalA st0 (ys[2 * q]'(by omega))) (evalA st0 (ys[2 * q + 1]'h2))
            else
              evalA (gPairUp comb st0 ys).1 (gPairUp comb st0 ys).2[q] =
                evalA st0 (ys[2 * q]'(by rw [gPairUp_len] at hq; omega))) := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ihm =>
          intro ys hm_eq st0 hwf0 hys
          cases ys with
          | nil =>
            exact ⟨hwf0, ⟨[], (List.append_nil st0).symm, by simp⟩, by simp [gPairUp],
              fun q hq => by simp [gPairUp] at hq⟩
          | cons a rest0 =>
            cases rest0 with
            | nil =>
              have ha := hys a (by simp)
              refine ⟨hwf0, ⟨[], (List.append_nil st0).symm, by simp⟩, by simp [gPairUp], ?_⟩
              dsimp only [gPairUp]
              intro q hq
              have hq0 : q = 0 := by simp at hq; omega
              subst hq0
              simp only [List.getElem_cons_zero]
              exact ⟨ha.1, by omega, by simp⟩
            | cons b rest =>
              have ha := hys a (by simp)
              have hb := hys b (by simp)
              have hcb := h_comb st0 a b hwf0 ha.1 hb.1
              obtain ⟨hwf_c, ⟨more_c, hst_c, hlen_c⟩, hvc, hevc, hdc⟩ := hcb
              have hrest_v : ∀ x ∈ rest, validA (comb st0 a b).1 x ∧ depthA x ≤ d0 := by
                intro x hx
                have hx0 := hys x (by simp [hx])
                rw [hst_c]
                exact ⟨(h_mono st0 more_c x hx0.1).1, hx0.2⟩
              have hrec := ihm rest.length (by simp at hm_eq; omega) rest rfl (comb st0 a b).1 hwf_c hrest_v
              obtain ⟨hwf_r, ⟨more_r, hst_r, hlen_r⟩, hlen_zs, hq_r⟩ := hrec
              dsimp [gPairUp]
              refine ⟨hwf_r, ?_, ?_, ?_⟩
              · refine ⟨more_c ++ more_r, ?_, ?_⟩
                · rw [hst_r, hst_c, List.append_assoc]
                · rw [List.length_append]
                  have hdiv : (rest.length + 1 + 1) / 2 = 1 + rest.length / 2 := by omega
                  rw [hdiv, Nat.add_mul, Nat.one_mul]; omega
              · simp [hlen_zs]; omega
              · intro q hq
                cases q with
                | zero =>
                  rw [List.getElem_cons_zero, hst_r]
                  have hm1 := h_mono (comb st0 a b).1 more_r (comb st0 a b).2 hvc
                  refine ⟨hm1.1, by omega, ?_⟩
                  simp only [Nat.mul_zero, Nat.zero_add]
                  rw [dif_pos (by omega), hm1.2, hevc]; rfl
                | succ q =>
                  rw [List.getElem_cons_succ]
                  have hqr := hq_r q (by simp at hq; exact hq)
                  refine ⟨hqr.1, hqr.2.1, ?_⟩
                  by_cases h2q1 : 2 * q + 1 < rest.length
                  · rw [dif_pos (by omega)]
                    have := hqr.2.2
                    rw [dif_pos h2q1] at this
                    have ha1 := (h_mono st0 more_c (rest[2 * q]) (hys _ (by simp)).1).2
                    have ha2 := (h_mono st0 more_c (rest[2 * q + 1]) (hys _ (by simp)).1).2
                    conv_lhs => rw [this, hst_c, ha1, ha2]
                    congr 1 <;> congr 1 <;> simp [show 2 * (q + 1) = 2 * q + 2 by ring]
                  · rw [dif_neg (by omega)]
                    have := hqr.2.2
                    rw [dif_neg h2q1] at this
                    have h2q_lt : 2 * q < rest.length := by
                      have h1 : q < (gPairUp comb (comb st0 a b).1 rest).2.length := by omega
                      rw [hlen_zs] at h1; omega
                    have h_all_lt : 2 * (q + 1) < (a :: b :: rest).length := by simp; omega
                    have ha1 := (h_mono st0 more_c (rest[2 * q]'h2q_lt) (hys _ (by simp)).1).2
                    have hsub : evalA (comb st0 a b).1 (rest[2 * q]'h2q_lt) =
                        evalA st0 ((a :: b :: rest)[2 * (q + 1)]'h_all_lt) := by
                      rw [hst_c, ha1]
                      simp [show 2 * (q + 1) = 2 * q + 2 by ring]
                    exact Eq.trans this hsub
      have hp_res := hpair xs.length xs rfl st hwf hxs
      obtain ⟨hwf1, ⟨more1, hst1, hlen_m1⟩, hlen_zs, hq_zs⟩ := hp_res
      set st1 := (gPairUp comb st xs).1
      set zs := (gPairUp comb st xs).2
      have hlt_n : zs.length < xs.length := by rw [hlen_zs]; omega
      have hid1 : validA st1 idVal := by rw [hst1]; exact (h_mono st more1 idVal hid).1
      have hid1_ev : evalA st1 idVal = idM := by
        rw [hst1, (h_mono st more1 idVal hid).2, hid_ev]
      have hzs_v : ∀ z ∈ zs, validA st1 z ∧ depthA z ≤ d0 + dc := by
        intro z hz
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hz
        exact ⟨(hq_zs q hq).1, (hq_zs q hq).2.1⟩
      have hscan2 := ih zs.length hlt_n zs rfl st1 (d0 + dc) hwf1 hid1 hid1_ev (by omega) hzs_v
      obtain ⟨hwf2, ⟨more2, hst2, hlen_m2⟩, hlen_ps, hq_ps⟩ := hscan2
      set st2 := (gScanExcl comb idVal st1 zs).1
      set ps := (gScanExcl comb idVal st1 zs).2
      have hclog : Nat.clog 2 xs.length = Nat.clog 2 zs.length + 1 := by
        have := Nat.clog_of_one_lt (by decide : 1 < 2) (by omega : 1 < xs.length)
        rw [hlen_zs]; simpa using this
      have hpair_foldl : ∀ (q : ℕ), q < zs.length →
          ((zs.take q).map (evalA st1)).foldl opM idM =
            ((xs.take (2 * q)).map (evalA st)).foldl opM idM := by
        intro q hq
        induction q with
        | zero => simp
        | succ q ihq =>
          have hq_lt : q < zs.length := by omega
          have h2q1 : 2 * q + 1 < xs.length := by rw [hlen_zs] at hq; omega
          have hzq := (hq_zs q hq_lt).2.2
          rw [dif_pos h2q1] at hzq
          rw [List.take_succ_eq_append_getElem hq_lt, List.map_append, List.map_singleton,
            List.foldl_append, List.foldl_cons, List.foldl_nil, ihq hq_lt, hzq]
          have htake2 : xs.take (2 * (q + 1)) = xs.take (2 * q) ++ [xs[2 * q]'(by omega), xs[2 * q + 1]'h2q1] := by
            rw [show 2 * (q + 1) = (2 * q + 1) + 1 by ring, List.take_succ_eq_append_getElem h2q1,
              List.take_succ_eq_append_getElem (by omega), List.append_assoc]; rfl
          rw [htake2, List.map_append, List.map_cons, List.map_singleton,
            List.foldl_append, List.foldl_cons, List.foldl_cons, List.foldl_nil, h_assoc]
      have hexp : ∀ (len_y : ℕ) (ys_rem ps_rem : List α) (st_cur : List (GateDef k)) (off : ℕ),
          ys_rem.length = len_y →
          ps_rem.length = (ys_rem.length + 1) / 2 →
          (hsum : ys_rem.length + 2 * off = xs.length) →
          (∀ (j : ℕ) (hj : j < ys_rem.length), ys_rem[j]'hj = xs[2 * off + j]'(by omega)) →
          WF st_cur →
          (∃ m_cur, st_cur = st ++ m_cur) →
          (∀ (q : ℕ) (hq : q < ps_rem.length),
            validA st_cur ps_rem[q] ∧ depthA ps_rem[q] ≤ d0 + dc + 2 * dc * Nat.clog 2 zs.length ∧
            evalA st_cur ps_rem[q] = ((xs.take (2 * (off + q))).map (evalA st)).foldl opM idM) →
          (∀ a ∈ ys_rem, validA st_cur a ∧ depthA a ≤ d0) →
          let (st3, outs) := gExpandDown comb st_cur ps_rem ys_rem
          WF st3 ∧
          (∃ more3, st3 = st_cur ++ more3 ∧ more3.length ≤ (ys_rem.length / 2) * cCost) ∧
          outs.length = ys_rem.length ∧
          (∀ (j : ℕ) (hj : j < outs.length),
            validA st3 outs[j] ∧
            depthA outs[j] ≤ d0 + 2 * dc * Nat.clog 2 xs.length ∧
            evalA st3 outs[j] = ((xs.take (2 * off + j)).map (evalA st)).foldl opM idM) := by
        intro len_y
        induction len_y using Nat.strong_induction_on with
        | ind len_y ih_y =>
          intro ys_rem ps_rem st_cur off hly hlp hsum hys_eq hwf_c ⟨m_cur, hm_cur⟩ hps_rem hys_rem
          match ys_rem, ps_rem with
          | [], [] =>
            dsimp [gExpandDown]
            exact ⟨hwf_c, ⟨[], (List.append_nil st_cur).symm, by simp⟩, rfl, fun j hj => by simp at hj⟩
          | [], _ :: _ =>
            dsimp [gExpandDown]
            exact ⟨hwf_c, ⟨[], (List.append_nil st_cur).symm, by simp⟩, rfl, fun j hj => by simp at hj⟩
          | [a], p :: _ =>
            dsimp [gExpandDown]
            have hp0 := hps_rem 0 (by simp)
            simp only [List.getElem_cons_zero] at hp0
            refine ⟨hwf_c, ⟨[], (List.append_nil st_cur).symm, by simp⟩, rfl, fun j hj => ?_⟩
            have hj0 : j = 0 := by simp at hj; omega
            subst hj0
            simp only [List.getElem_cons_zero]
            refine ⟨hp0.1, by rw [hclog, Nat.mul_add, Nat.mul_one]; omega, by simpa only [Nat.add_zero] using hp0.2.2⟩
          | a :: b :: rest, p :: ps' =>
            have ha := hys_rem a (by simp)
            have hp0 := hps_rem 0 (by simp)
            simp only [List.getElem_cons_zero] at hp0
            have hcb := h_comb st_cur p a hwf_c hp0.1 ha.1
            obtain ⟨hwf_1, ⟨more_1, hst_1, hlen_1⟩, hv_o, hev_o, hd_o⟩ := hcb
            set st_1 := (comb st_cur p a).1
            set o := (comb st_cur p a).2
            have ha_eq : a = xs[2 * off]'(by simp at hsum; omega) := by
              have := hys_eq 0 (by simp); simpa using this
            have hm_cur1 : ∃ m1, st_1 = st ++ m1 := ⟨m_cur ++ more_1, by rw [hst_1, hm_cur, List.append_assoc]⟩
            have hys1 : ∀ x ∈ rest, validA st_1 x ∧ depthA x ≤ d0 := by
              intro x hx
              have hx0 := hys_rem x (by simp [hx])
              rw [hst_1]
              exact ⟨(h_mono st_cur more_1 x hx0.1).1, hx0.2⟩
            have hps1 : ∀ (q : ℕ) (hq : q < ps'.length),
                validA st_1 ps'[q] ∧ depthA ps'[q] ≤ d0 + dc + 2 * dc * Nat.clog 2 zs.length ∧
                evalA st_1 ps'[q] = ((xs.take (2 * (off + 1 + q))).map (evalA st)).foldl opM idM := by
              intro q hq
              have hq1 := hps_rem (q + 1) (by simp; exact hq)
              simp only [List.getElem_cons_succ] at hq1
              rw [hst_1]
              have hmq := h_mono st_cur more_1 ps'[q] hq1.1
              refine ⟨hmq.1, hq1.2.1, ?_⟩
              rw [hmq.2, hq1.2.2]
              congr 2; ring
            have hrec := ih_y rest.length (by simp at hly; omega) rest ps' st_1 (off + 1) rfl
              (by simp at hlp; omega) (by simp at hsum; omega)
              (fun j hj => by
                have := hys_eq (j + 2) (by simp; omega)
                simpa [show 2 * (off + 1) + j = 2 * off + (j + 2) by ring] using this)
              hwf_1 hm_cur1 hps1 hys1
            obtain ⟨hwf_3, ⟨more_3, hst_3, hlen_3⟩, hlen_o, hj_3⟩ := hrec
            have hg_eq : gExpandDown comb st_cur (p :: ps') (a :: b :: rest) =
                ((gExpandDown comb st_1 ps' rest).1, p :: o :: (gExpandDown comb st_1 ps' rest).2) := rfl
            rw [hg_eq]
            refine ⟨hwf_3, ?_, ?_, ?_⟩
            · refine ⟨more_1 ++ more_3, by rw [hst_3, hst_1, List.append_assoc], ?_⟩
              rw [List.length_append]
              have hdiv_len : (a :: b :: rest).length / 2 = 1 + rest.length / 2 := by simp; omega
              rw [hdiv_len, Nat.add_mul, Nat.one_mul]; omega
            · simp [hlen_o]
            · intro j hj
              rcases j with _ | _ | j
              · rw [List.getElem_cons_zero]
                rw [hst_3, hst_1]
                have hm := h_mono st_cur (more_1 ++ more_3) p hp0.1
                rw [← List.append_assoc] at hm
                refine ⟨hm.1, by rw [hclog, Nat.mul_add, Nat.mul_one]; omega, ?_⟩
                rw [hm.2, hp0.2.2]; simp
              · rw [List.getElem_cons_succ, List.getElem_cons_zero, hst_3]
                have hm := h_mono st_1 more_3 o hv_o
                refine ⟨hm.1, by rw [hclog, Nat.mul_add, Nat.mul_one]; omega, ?_⟩
                rw [hm.2, hev_o, hp0.2.2]
                have ha_eval : evalA st_cur a = evalA st a := by
                  have hma := h_mono st m_cur a (hxs a (by rw [ha_eq]; simp)).1
                  rw [← hm_cur] at hma; exact hma.2
                rw [ha_eval, ha_eq]
                have htake1 : xs.take (2 * off + 1) = xs.take (2 * off) ++ [xs[2 * off]'(by simp at hsum; omega)] :=
                  List.take_succ_eq_append_getElem (by simp at hsum; omega)
                rw [htake1, List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
                simp
              · rw [List.getElem_cons_succ, List.getElem_cons_succ]
                have hj' := hj_3 j (by simp at hj; omega)
                refine ⟨hj'.1, hj'.2.1, ?_⟩
                rw [hj'.2.2]; congr 2; ring
          | [_], [] => simp at hlp
          | _ :: _ :: _, [] => simp at hlp; omega
      have hst2_eq : st2 = st ++ (more1 ++ more2) := by
        rw [hst2, hst1, List.append_assoc]
      have hps_base : ∀ (q : ℕ) (hq : q < ps.length),
          validA st2 ps[q] ∧ depthA ps[q] ≤ d0 + dc + 2 * dc * Nat.clog 2 zs.length ∧
          evalA st2 ps[q] = ((xs.take (2 * (0 + q))).map (evalA st)).foldl opM idM := by
        intro q hq
        have hq' := hq_ps q hq
        refine ⟨hq'.1, hq'.2.1, ?_⟩
        rw [hq'.2.2, Nat.zero_add, hpair_foldl q (by rw [← hlen_ps]; exact hq)]
      have hxs2 : ∀ a ∈ xs, validA st2 a ∧ depthA a ≤ d0 := by
        intro a ha
        have hx0 := hxs a ha
        rw [hst2_eq]
        exact ⟨(h_mono st (more1 ++ more2) a hx0.1).1, hx0.2⟩
      have hexp_res := hexp xs.length xs ps st2 0 rfl (by rw [hlen_ps, hlen_zs]) (by omega)
        (fun j hj => by simp) hwf2 ⟨more1 ++ more2, hst2_eq⟩ hps_base hxs2
      obtain ⟨hwf3, ⟨more3, hst3, hlen3⟩, hlen_out, h_out⟩ := hexp_res
      refine ⟨hwf3, ⟨more1 ++ more2 ++ more3, ?_, ?_⟩, hlen_out, ?_⟩
      · rw [hst3, hst2_eq, List.append_assoc]
      · rw [List.length_append, List.length_append]
        have hzs_cost : 2 * zs.length * cCost = 2 * ((xs.length + 1) / 2) * cCost := by rw [hlen_zs]
        have hsum_len : (xs.length / 2) * cCost + 2 * zs.length * cCost + (xs.length / 2) * cCost =
            2 * xs.length * cCost := by
          rw [hzs_cost, ← Nat.add_mul, ← Nat.add_mul,
            show xs.length / 2 + 2 * ((xs.length + 1) / 2) + xs.length / 2 = 2 * xs.length by omega]
        omega
      · intro i hi
        have hi' := h_out i hi
        simpa only [Nat.mul_zero, Nat.zero_add] using hi'

/-! ### Section 3b: Forward & Inverse Circuits and CNF Compilation -/

abbrev Vec (k : ℕ) := Fin k → WNode k

def ValidNode {k : ℕ} (owner : Fin 5) (st : List (GateDef k)) (w : WNode k) (d : ℕ) : Prop :=
  ValidWire owner st w.wire w.depth ∧ w.depth ≤ d

theorem ValidNode_mono {k : ℕ} {owner : Fin 5} {st : List (GateDef k)} (more : List (GateDef k))
    {w : WNode k} {d1 d2 : ℕ} (hd : d1 ≤ d2) (hv : ValidNode owner st w d1) :
    ValidNode owner (st ++ more) w d2 :=
  ⟨ValidWire_mono more (le_refl _) hv.1, le_trans hv.2 hd⟩

def VecValid {k : ℕ} (owner : Fin 5) (st : List (GateDef k)) (x : Vec k) (d : ℕ) : Prop :=
  ∀ i : Fin k, ValidNode owner st (x i) d

theorem VecValid_mono {k : ℕ} {owner : Fin 5} {st : List (GateDef k)} (more : List (GateDef k))
    {x : Vec k} {d1 d2 : ℕ} (hd : d1 ≤ d2) (hx : VecValid owner st x d1) :
    VecValid owner (st ++ more) x d2 :=
  fun i => ValidNode_mono more hd (hx i)

def evalVec {k : ℕ} (v : Fin 5 × Fin k → Bool) (st : List (GateDef k)) (x : Vec k) : Fin k → Bool :=
  fun i => evalW v st (x i).wire

theorem evalVec_append {k : ℕ} (v : Fin 5 × Fin k → Bool) {owner : Fin 5}
    {st : List (GateDef k)} (more : List (GateDef k)) {x : Vec k} {d : ℕ}
    (hx : VecValid owner st x d) :
    evalVec v (st ++ more) x = evalVec v st x := by
  ext i; exact evalW_append v more (hx i).1

def inVec (k : ℕ) (t : Fin 5) : Vec k :=
  fun i => ⟨Sum.inl (t, i), 0⟩

theorem inVec_valid {k : ℕ} (owner t : Fin 5) (ht : t = 2 ∨ t = owner) (st : List (GateDef k)) :
    VecValid owner st (inVec k t) 0 := by
  intro i
  exact ⟨ht.elim (fun h => Or.inl h) (fun h => Or.inr h), le_refl 0⟩

theorem inVec_eval {k : ℕ} (v : Fin 5 × Fin k → Bool) (st : List (GateDef k)) (t : Fin 5) :
    evalVec v st (inVec k t) = fun i => v (t, i) := rfl

def constNode (k j : ℕ) (i : Fin k) : WNode k :=
  if constBit k j i then trueNode else falseNode

theorem constNode_valid {k : ℕ} (hk : 0 < k) (owner : Fin 5) (j : ℕ) (i : Fin k)
    (more : List (GateDef k)) :
    ValidNode owner (initGates k hk ++ more) (constNode k j i) 1 := by
  dsimp [constNode]
  split_ifs
  · exact ValidNode_mono more (le_refl 1) ⟨(valid_constNodes hk owner).2, le_refl 1⟩
  · exact ValidNode_mono more (le_refl 1) ⟨(valid_constNodes hk owner).1, le_refl 1⟩

theorem constNode_eval {k : ℕ} (hk : 0 < k) (v : Fin 5 × Fin k → Bool) (j : ℕ) (i : Fin k)
    (more : List (GateDef k)) :
    evalW v (initGates k hk ++ more) (constNode k j i).wire = constBit k j i := by
  have hc := valid_constNodes hk 0
  have he := eval_constNodes hk v
  dsimp [constNode]
  split_ifs with h
  · rw [evalW_append v more hc.2, he.2, h]
  · rw [evalW_append v more hc.1, he.1]
    cases hc_eq : constBit k j i with
    | false => rfl
    | true => exact absurd hc_eq h

def buildMap {S α β : Type} (f : S → α → S × β) (st : S) : List α → S × List β
  | [] => (st, [])
  | x :: xs =>
    let (st1, y) := f st x
    let (st2, ys) := buildMap f st1 xs
    (st2, y :: ys)

theorem buildMap_len {S α β : Type} (f : S → α → S × β) (st : S) (xs : List α) :
    (buildMap f st xs).2.length = xs.length := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih => simp [buildMap, ih]

theorem buildMap_spec {k : ℕ} {α β : Type}
    (step : List (GateDef k) → α → List (GateDef k) × β)
    (inv : List (GateDef k) → Prop)
    (validB : List (GateDef k) → β → Prop)
    (propB : List (GateDef k) → α → β → Prop)
    (cCost : ℕ)
    (h_inv_mono : ∀ st more, inv st → WF (st ++ more) → inv (st ++ more))
    (h_mono : ∀ st more x b, validB st b → propB st x b → validB (st ++ more) b ∧ propB (st ++ more) x b)
    (h_step : ∀ st x, inv st → WF st →
      WF (step st x).1 ∧ (∃ more, (step st x).1 = st ++ more ∧ more.length ≤ cCost) ∧
      validB (step st x).1 (step st x).2 ∧ propB (step st x).1 x (step st x).2) :
    ∀ (xs : List α) (st : List (GateDef k)), inv st → WF st →
      WF (buildMap step st xs).1 ∧
      (∃ more, (buildMap step st xs).1 = st ++ more ∧ more.length ≤ xs.length * cCost) ∧
      (buildMap step st xs).2.length = xs.length ∧
      (∀ (i : ℕ) (hi : i < xs.length),
        validB (buildMap step st xs).1 ((buildMap step st xs).2[i]'(by rw [buildMap_len]; exact hi)) ∧
        propB (buildMap step st xs).1 xs[i] ((buildMap step st xs).2[i]'(by rw [buildMap_len]; exact hi))) := by
  intro xs
  induction xs with
  | nil =>
    intro st _ hwf
    exact ⟨hwf, ⟨[], (List.append_nil st).symm, by simp⟩, rfl, fun i hi => by simp at hi⟩
  | cons x xs ih =>
    intro st hinv hwf
    have hs := h_step st x hinv hwf
    obtain ⟨hwf1, ⟨more1, hst1, hlen1⟩, hvb, hpb⟩ := hs
    have hinv1 : inv (step st x).1 := by rw [hst1]; exact h_inv_mono st more1 hinv (by rw [← hst1]; exact hwf1)
    have hrec := ih (step st x).1 hinv1 hwf1
    obtain ⟨hwf2, ⟨more2, hst2, hlen2⟩, hlen_bs, hvb2⟩ := hrec
    dsimp [buildMap]
    refine ⟨hwf2, ⟨more1 ++ more2, by rw [hst2, hst1, List.append_assoc], ?_⟩, ?_, ?_⟩
    · rw [List.length_append, Nat.add_mul, Nat.one_mul]; omega
    · simp [hlen_bs]
    · intro i hi
      cases i with
      | zero =>
        simp only [List.getElem_cons_zero]
        rw [hst2]
        exact h_mono _ more2 x _ hvb hpb
      | succ i =>
        simp only [List.getElem_cons_succ]
        exact hvb2 i (by simp at hi; exact hi)

def buildVec {k : ℕ} (step : List (GateDef k) → Fin k → List (GateDef k) × WNode k)
    (st : List (GateDef k)) : List (GateDef k) × Vec k :=
  let res := buildMap step st (List.finRange k)
  (res.1, fun i => res.2.getD i.val falseNode)

theorem buildVec_spec {k : ℕ} (owner : Fin 5) (dOut cCost : ℕ)
    (step : List (GateDef k) → Fin k → List (GateDef k) × WNode k)
    (inv : List (GateDef k) → Prop)
    (target : (Fin 5 × Fin k → Bool) → Fin k → Bool)
    (h_inv_mono : ∀ st more, inv st → WF (st ++ more) → inv (st ++ more))
    (h_step : ∀ st i, inv st → WF st →
      WF (step st i).1 ∧ (∃ more, (step st i).1 = st ++ more ∧ more.length ≤ cCost) ∧
      ValidNode owner (step st i).1 (step st i).2 dOut ∧ (∀ v, evalW v (step st i).1 (step st i).2.wire = target v i)) :
    ∀ st : List (GateDef k), inv st → WF st →
      WF (buildVec step st).1 ∧ (∃ more, (buildVec step st).1 = st ++ more ∧ more.length ≤ k * cCost) ∧
      VecValid owner (buildVec step st).1 (buildVec step st).2 dOut ∧
      (∀ v, evalVec v (buildVec step st).1 (buildVec step st).2 = target v) := by
  intro st hinv hwf
  have hbm := buildMap_spec step inv
    (fun st' w => ValidNode owner st' w dOut)
    (fun st' i w => ∀ v, evalW v st' w.wire = target v i)
    cCost h_inv_mono
    (fun st' more i w hv hp =>
      ⟨ValidNode_mono more (le_refl _) hv, fun v => by rw [evalW_append v more hv.1, hp v]⟩)
    h_step (List.finRange k) st hinv hwf
  obtain ⟨hwf', ⟨more, hst', hlen⟩, hlen_bs, h_elem⟩ := hbm
  rw [List.length_finRange] at hlen hlen_bs
  refine ⟨hwf', ⟨more, hst', hlen⟩, ?_, ?_⟩
  · intro i
    have hi_lt : i.val < (List.finRange k).length := by rw [List.length_finRange]; exact i.isLt
    have hi_bs : i.val < (buildMap step st (List.finRange k)).2.length := by rw [hlen_bs]; exact i.isLt
    have heq : (buildMap step st (List.finRange k)).2.getD i.val falseNode =
        (buildMap step st (List.finRange k)).2[i.val]'hi_bs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_bs]; rfl
    dsimp [buildVec]; rw [heq]
    exact (h_elem i.val hi_lt).1
  · intro v; ext i
    have hi_lt : i.val < (List.finRange k).length := by rw [List.length_finRange]; exact i.isLt
    have hi_bs : i.val < (buildMap step st (List.finRange k)).2.length := by rw [hlen_bs]; exact i.isLt
    have heq : (buildMap step st (List.finRange k)).2.getD i.val falseNode =
        (buildMap step st (List.finRange k)).2[i.val]'hi_bs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_bs]; rfl
    dsimp [buildVec, evalVec]; rw [heq]
    have hget := (h_elem i.val hi_lt).2 v
    simpa [List.getElem_finRange] using hget

/-! #### Gate-level Vector Layers (`buildXorVec`, `buildMix`, `buildStep`, `buildXorKeyConst`) -/

def buildXorVec {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (a b : Vec k) : List (GateDef k) × Vec k :=
  buildVec (fun st0 i => addGate st0 owner ho xor (a i) (b i)) st

theorem buildXorVec_spec {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (a b : Vec k) (da db : ℕ)
    (hwf : WF st) (ha : VecValid owner st a da) (hb : VecValid owner st b db) :
    WF (buildXorVec owner ho st a b).1 ∧
    (∃ more, (buildXorVec owner ho st a b).1 = st ++ more ∧ more.length ≤ k) ∧
    VecValid owner (buildXorVec owner ho st a b).1 (buildXorVec owner ho st a b).2 (max da db + 1) ∧
    (∀ v, evalVec v (buildXorVec owner ho st a b).1 (buildXorVec owner ho st a b).2 =
      fun i => xor (evalVec v st a i) (evalVec v st b i)) := by
  let inv : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st ++ m
  have hbm := buildVec_spec owner (max da db + 1) 1
    (fun st0 i => addGate st0 owner ho xor (a i) (b i)) inv
    (fun v i => xor (evalVec v st a i) (evalVec v st b i))
    (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
    (fun st0 i ⟨m, hm⟩ hwf0 => by
      have ha0 : ValidWire owner st0 (a i).wire (a i).depth := by
        rw [hm]; exact ValidWire_mono m (le_refl _) (ha i).1
      have hb0 : ValidWire owner st0 (b i).wire (b i).depth := by
        rw [hm]; exact ValidWire_mono m (le_refl _) (hb i).1
      have had := addGate_wf st0 owner ho xor (a i) (b i) hwf0 ha0 hb0
      refine ⟨had.1, ⟨had.2.1.choose, had.2.1.choose_spec.1, by omega⟩, ⟨had.2.2.1, ?_⟩, ?_⟩
      · rw [had.2.2.2]; have := (ha i).2; have := (hb i).2; omega
      · intro v; rw [addGate_eval]
        rw [hm, evalW_append v m (ha i).1, evalW_append v m (hb i).1]; rfl)
    st ⟨[], (List.append_nil st).symm⟩ hwf
  refine ⟨hbm.1, ⟨hbm.2.1.choose, hbm.2.1.choose_spec.1, by have := hbm.2.1.choose_spec.2; omega⟩,
    hbm.2.2.1, hbm.2.2.2⟩

def addGate2 {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (op1 op2 : Bool → Bool → Bool) (st : List (GateDef k)) (a b c : WNode k) :
    List (GateDef k) × WNode k :=
  let (st1, w1) := addGate st owner ho op1 a b
  addGate st1 owner ho op2 w1 c

theorem addGate2_wf {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (op1 op2 : Bool → Bool → Bool) (st : List (GateDef k)) (a b c : WNode k)
    (da db dc : ℕ) (hwf : WF st)
    (ha : ValidNode owner st a da) (hb : ValidNode owner st b db) (hc : ValidNode owner st c dc) :
    WF (addGate2 owner ho op1 op2 st a b c).1 ∧
    (∃ more, (addGate2 owner ho op1 op2 st a b c).1 = st ++ more ∧ more.length ≤ 2) ∧
    ValidNode owner (addGate2 owner ho op1 op2 st a b c).1 (addGate2 owner ho op1 op2 st a b c).2
      (max (max da db + 1) dc + 1) ∧
    (∀ v, evalW v (addGate2 owner ho op1 op2 st a b c).1 (addGate2 owner ho op1 op2 st a b c).2.wire =
      op2 (op1 (evalW v st a.wire) (evalW v st b.wire)) (evalW v st c.wire)) := by
  dsimp [addGate2]
  have h1 := addGate_wf st owner ho op1 a b hwf ha.1 hb.1
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hvw1, hdw1⟩ := h1
  have hc1 : ValidWire owner (addGate st owner ho op1 a b).1 c.wire c.depth := by
    rw [hm1]; exact ValidWire_mono m1 (le_refl _) hc.1
  have h2 := addGate_wf _ owner ho op2 _ c hwf1 hvw1 hc1
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hvw2, hdw2⟩ := h2
  refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], by rw [List.length_append]; omega⟩, ⟨hvw2, ?_⟩, ?_⟩
  · rw [hdw2, hdw1]
    exact Nat.succ_le_succ (max_le
      (le_trans (Nat.succ_le_succ (max_le (le_trans ha.2 (le_max_left _ _)) (le_trans hb.2 (le_max_right _ _))))
        (le_max_left _ _))
      (le_trans hc.2 (le_max_right _ _)))
  · intro v; rw [addGate_eval, addGate_eval, hm1, evalW_append v m1 hc.1]

def buildMixVec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2) (δ : ℕ)
    (st : List (GateDef k)) (x : Vec k) : List (GateDef k) × Vec k :=
  buildVec (fun st0 i =>
    let i1 : Fin k := ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
    let i2 : Fin k := ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
    addGate2 owner ho xor xor st0 (x i) (x i1) (x i2)) st

theorem buildMixVec_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2) (δ : ℕ)
    (st : List (GateDef k)) (x : Vec k) (dx : ℕ)
    (hwf : WF st) (hx : VecValid owner st x dx) :
    WF (buildMixVec hk owner ho δ st x).1 ∧
    (∃ more, (buildMixVec hk owner ho δ st x).1 = st ++ more ∧ more.length ≤ 2 * k) ∧
    VecValid owner (buildMixVec hk owner ho δ st x).1 (buildMixVec hk owner ho δ st x).2 (dx + 2) ∧
    (∀ v, evalVec v (buildMixVec hk owner ho δ st x).1 (buildMixVec hk owner ho δ st x).2 =
      mixB hk δ (evalVec v st x)) := by
  let inv : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st ++ m
  have hbm := buildVec_spec owner (dx + 2) 2 _ inv
    (fun v => mixB hk δ (evalVec v st x))
    (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
    (fun st0 i ⟨m, hm⟩ hwf0 => by
      let i1 : Fin k := ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
      have hx0 : ValidNode owner st0 (x i) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i)
      have hx1 : ValidNode owner st0 (x i1) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i1)
      have hx2 : ValidNode owner st0 (x i2) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i2)
      have hg := addGate2_wf owner ho xor xor st0 (x i) (x i1) (x i2) dx dx dx hwf0 hx0 hx1 hx2
      refine ⟨hg.1, hg.2.1, ⟨hg.2.2.1.1, by
        have hle := hg.2.2.1.2
        simp [max_eq_left (by omega : dx ≤ dx + 1)] at hle; exact hle⟩, ?_⟩
      intro v; rw [hg.2.2.2 v, hm]
      rw [evalW_append v m (hx i).1, evalW_append v m (hx i1).1, evalW_append v m (hx i2).1]
      rfl)
    st ⟨[], (List.append_nil st).symm⟩ hwf
  refine ⟨hbm.1, ⟨hbm.2.1.choose, hbm.2.1.choose_spec.1, by have := hbm.2.1.choose_spec.2; omega⟩,
    hbm.2.2.1, hbm.2.2.2⟩

def buildStepVec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (x : Vec k) : List (GateDef k) × Vec k :=
  buildVec (fun st0 i =>
    let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    let i2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
    addGate2 owner ho (fun p q => !p && q) (fun a b => xor b a) st0 (x i1) (x i2) (x i)) st

theorem buildStepVec_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (x : Vec k) (dx : ℕ)
    (hwf : WF st) (hx : VecValid owner st x dx) :
    WF (buildStepVec hk owner ho st x).1 ∧
    (∃ more, (buildStepVec hk owner ho st x).1 = st ++ more ∧ more.length ≤ 2 * k) ∧
    VecValid owner (buildStepVec hk owner ho st x).1 (buildStepVec hk owner ho st x).2 (dx + 2) ∧
    (∀ v, evalVec v (buildStepVec hk owner ho st x).1 (buildStepVec hk owner ho st x).2 =
      stepB hk (evalVec v st x)) := by
  let inv : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st ++ m
  have hbm := buildVec_spec owner (dx + 2) 2 _ inv
    (fun v => stepB hk (evalVec v st x))
    (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
    (fun st0 i ⟨m, hm⟩ hwf0 => by
      let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
      have hx0 : ValidNode owner st0 (x i) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i)
      have hx1 : ValidNode owner st0 (x i1) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i1)
      have hx2 : ValidNode owner st0 (x i2) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i2)
      have hg := addGate2_wf owner ho (fun p q => !p && q) (fun a b => xor b a)
        st0 (x i1) (x i2) (x i) dx dx dx hwf0 hx1 hx2 hx0
      refine ⟨hg.1, hg.2.1, ⟨hg.2.2.1.1, by
        have hle := hg.2.2.1.2
        simp [max_eq_left (by omega : dx ≤ dx + 1)] at hle; exact hle⟩, ?_⟩
      intro v; rw [hg.2.2.2 v, hm]
      rw [evalW_append v m (hx i).1, evalW_append v m (hx i1).1, evalW_append v m (hx i2).1]
      rfl)
    st ⟨[], (List.append_nil st).symm⟩ hwf
  refine ⟨hbm.1, ⟨hbm.2.1.choose, hbm.2.1.choose_spec.1, by have := hbm.2.1.choose_spec.2; omega⟩,
    hbm.2.2.1, hbm.2.2.2⟩

def buildXorKeyConstVec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (shift cIdx : ℕ) (st : List (GateDef k)) (x key : Vec k) : List (GateDef k) × Vec k :=
  buildVec (fun st0 i =>
    let ik : Fin k := ⟨(i.val + k - shift % k) % k, Nat.mod_lt _ hk⟩
    addGate2 owner ho xor xor st0 (x i) (key ik) (constNode k cIdx i)) st

theorem buildXorKeyConstVec_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (shift cIdx : ℕ) (st : List (GateDef k)) (x key : Vec k) (dx : ℕ)
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0)
    (hx : VecValid owner st x dx) (hkey : VecValid owner st key 0) :
    WF (buildXorKeyConstVec hk owner ho shift cIdx st x key).1 ∧
    (∃ more, (buildXorKeyConstVec hk owner ho shift cIdx st x key).1 = st ++ more ∧ more.length ≤ 2 * k) ∧
    VecValid owner (buildXorKeyConstVec hk owner ho shift cIdx st x key).1
      (buildXorKeyConstVec hk owner ho shift cIdx st x key).2 (max dx 1 + 2) ∧
    (∀ v, evalVec v (buildXorKeyConstVec hk owner ho shift cIdx st x key).1
        (buildXorKeyConstVec hk owner ho shift cIdx st x key).2 = fun i =>
      xor (xor (evalVec v st x i) (rotB hk shift (evalVec v st key) i)) (constBit k cIdx i)) := by
  let inv : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st ++ m
  have hbm := buildVec_spec owner (max dx 1 + 2) 2
    (fun st0 i => addGate2 owner ho xor xor st0 (x i)
      (key ⟨(i.val + k - shift % k) % k, Nat.mod_lt _ hk⟩) (constNode k cIdx i)) inv
    (fun v i => xor (xor (evalVec v st x i) (rotB hk shift (evalVec v st key) i)) (constBit k cIdx i))
    (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
    (fun st0 i ⟨m, hm⟩ hwf0 => by
      let ik : Fin k := ⟨(i.val + k - shift % k) % k, Nat.mod_lt _ hk⟩
      have hx0 : ValidNode owner st0 (x i) dx := by rw [hm]; exact ValidNode_mono m (le_refl _) (hx i)
      have hk0 : ValidNode owner st0 (key ik) 0 := by rw [hm]; exact ValidNode_mono m (le_refl _) (hkey ik)
      obtain ⟨m0, hm0⟩ := hinit
      have hc0 : ValidNode owner st0 (constNode k cIdx i) 1 := by
        rw [hm, hm0, List.append_assoc]; exact constNode_valid hk owner cIdx i (m0 ++ m)
      have hg := addGate2_wf owner ho xor xor st0 (x i) (key ik) (constNode k cIdx i)
        dx 0 1 hwf0 hx0 hk0 hc0
      refine ⟨hg.1, hg.2.1, ⟨hg.2.2.1.1, by
        have hle := hg.2.2.1.2
        rw [Nat.max_eq_left (Nat.zero_le dx), Nat.max_eq_left (by omega : 1 ≤ dx + 1)] at hle
        exact le_trans hle (Nat.add_le_add_right (le_max_left dx 1) 2)⟩, ?_⟩
      intro v; rw [hg.2.2.2 v, hm]
      rw [evalW_append v m (hx i).1, evalW_append v m (hkey ik).1]
      have hce : evalW v (st ++ m) (constNode k cIdx i).wire = constBit k cIdx i := by
        rw [hm0, List.append_assoc]; exact constNode_eval hk v cIdx i (m0 ++ m)
      rw [hce]; rfl)
    st ⟨[], (List.append_nil st).symm⟩ hwf
  refine ⟨hbm.1, ⟨hbm.2.1.choose, hbm.2.1.choose_spec.1, by have := hbm.2.1.choose_spec.2; omega⟩,
    hbm.2.2.1, hbm.2.2.2⟩

/-! #### Forward Circuits (`buildFwdA`, `buildFwdB`) -/

def buildFwdRound {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ shift cIdx : ℕ) (st : List (GateDef k)) (x key : Vec k) : List (GateDef k) × Vec k :=
  let (st1, mx) := buildMixVec hk owner ho δ st x
  let (st2, sx) := buildStepVec hk owner ho st1 mx
  buildXorKeyConstVec hk owner ho shift cIdx st2 sx key

theorem buildFwdRound_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ shift cIdx : ℕ) (st : List (GateDef k)) (x key : Vec k) (dx : ℕ) (hdx : 1 ≤ dx)
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0)
    (hx : VecValid owner st x dx) (hkey : VecValid owner st key 0) :
    WF (buildFwdRound hk owner ho δ shift cIdx st x key).1 ∧
    (∃ more, (buildFwdRound hk owner ho δ shift cIdx st x key).1 = st ++ more ∧ more.length ≤ 6 * k) ∧
    VecValid owner (buildFwdRound hk owner ho δ shift cIdx st x key).1
      (buildFwdRound hk owner ho δ shift cIdx st x key).2 (dx + 6) ∧
    (∀ v, evalVec v (buildFwdRound hk owner ho δ shift cIdx st x key).1
        (buildFwdRound hk owner ho δ shift cIdx st x key).2 = fun i =>
      xor (xor (stepB hk (mixB hk δ (evalVec v st x)) i) (rotB hk shift (evalVec v st key) i))
        (constBit k cIdx i)) := by
  dsimp [buildFwdRound]
  have hm := buildMixVec_spec hk owner ho δ st x dx hwf hx
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hvm, hevm⟩ := hm
  have hs := buildStepVec_spec hk owner ho (buildMixVec hk owner ho δ st x).1
    (buildMixVec hk owner ho δ st x).2 (dx + 2) hwf1 hvm
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hvs, hevs⟩ := hs
  obtain ⟨m0, hm0⟩ := hinit
  have hinit2 : ∃ m', (buildStepVec hk owner ho (buildMixVec hk owner ho δ st x).1
      (buildMixVec hk owner ho δ st x).2).1 = initGates k hk ++ m' :=
    ⟨m0 ++ (m1 ++ m2), by rw [hm2, hm1, hm0, List.append_assoc, List.append_assoc]⟩
  have hkey2 : VecValid owner (buildStepVec hk owner ho (buildMixVec hk owner ho δ st x).1
      (buildMixVec hk owner ho δ st x).2).1 key 0 := by
    rw [hm2, hm1, List.append_assoc]; exact VecValid_mono (m1 ++ m2) (le_refl 0) hkey
  have hxkc := buildXorKeyConstVec_spec hk owner ho shift cIdx _ _ key (dx + 2 + 2) hwf2 hinit2
    hvs hkey2
  obtain ⟨hwf3, ⟨m3, hm3, hm3_len⟩, hvo, hevo⟩ := hxkc
  refine ⟨hwf3, ⟨m1 ++ m2 ++ m3, by rw [hm3, hm2, hm1]; simp only [List.append_assoc], ?_⟩,
    (fun i => ⟨(hvo i).1, by
      have hle := (hvo i).2
      rw [Nat.max_eq_left (by omega : 1 ≤ dx + 2 + 2)] at hle; omega⟩), ?_⟩
  · rw [List.length_append, List.length_append]; omega
  · intro v; rw [hevo v, hevs v, hevm v]
    have hk_ev : evalVec v (buildStepVec hk owner ho (buildMixVec hk owner ho δ st x).1
        (buildMixVec hk owner ho δ st x).2).1 key = evalVec v st key := by
      rw [hm2, hm1, List.append_assoc]; exact evalVec_append v (m1 ++ m2) hkey
    rw [hk_ev]

def buildFwdInit {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (initShift : ℕ) (st : List (GateDef k)) (key name : Vec k) : List (GateDef k) × Vec k :=
  buildXorVec owner ho st (fun i => key ⟨(i.val + k - initShift % k) % k, Nat.mod_lt _ hk⟩) name

def buildFwdLoop {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ : ℕ) (shiftFn constFn : ℕ → ℕ) (key : Vec k) :
    ℕ → List (GateDef k) → Vec k → List (GateDef k) × Vec k
  | 0, st, cur => (st, cur)
  | n + 1, st, cur =>
    let (st1, cur1) := buildFwdLoop hk owner ho δ shiftFn constFn key n st cur
    buildFwdRound hk owner ho δ (shiftFn n) (constFn n) st1 cur1 key

theorem buildFwdLoop_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ : ℕ) (shiftFn constFn : ℕ → ℕ) (key : Vec k) :
    ∀ (n : ℕ) (st : List (GateDef k)) (cur : Vec k) (d0 : ℕ), 1 ≤ d0 →
      WF st → (∃ m0, st = initGates k hk ++ m0) →
      VecValid owner st cur d0 → VecValid owner st key 0 →
      WF (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1 ∧
      (∃ more, (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1 = st ++ more ∧
        more.length ≤ 6 * k * n) ∧
      VecValid owner (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1
        (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).2 (d0 + 6 * n) ∧
      (∀ v, evalVec v (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1
          (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).2 =
        (List.range n).foldl (fun acc idx => fun i =>
          xor (xor (stepB hk (mixB hk δ acc) i) (rotB hk (shiftFn idx) (evalVec v st key) i))
            (constBit k (constFn idx) i)) (evalVec v st cur)) := by
  intro n
  induction n with
  | zero =>
    intro st cur d0 _ hwf _ hcur _
    exact ⟨hwf, ⟨[], (List.append_nil st).symm, by simp⟩, hcur, fun _ => rfl⟩
  | succ n ih =>
    intro st cur d0 hd0 hwf ⟨m0, hm0⟩ hcur hkey
    have hrec := ih st cur d0 hd0 hwf ⟨m0, hm0⟩ hcur hkey
    obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hvc1, hev1⟩ := hrec
    have hinit1 : ∃ m', (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1 =
        initGates k hk ++ m' := ⟨m0 ++ m1, by rw [hm1, hm0, List.append_assoc]⟩
    have hkey1 : VecValid owner (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1 key 0 := by
      rw [hm1]; exact VecValid_mono m1 (le_refl 0) hkey
    have hr := buildFwdRound_spec hk owner ho δ (shiftFn n) (constFn n)
      (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1
      (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).2 key (d0 + 6 * n) (by omega)
      hwf1 hinit1 hvc1 hkey1
    obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hvo2, hev2⟩ := hr
    dsimp [buildFwdLoop]
    refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], ?_⟩,
      (fun i => ⟨(hvo2 i).1, by have := (hvo2 i).2; omega⟩), ?_⟩
    · rw [List.length_append, Nat.mul_add, Nat.mul_one]; omega
    · intro v
      rw [hev2 v, hev1 v, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hk_ev : evalVec v (buildFwdLoop hk owner ho δ shiftFn constFn key n st cur).1 key =
          evalVec v st key := by
        rw [hm1]; exact evalVec_append v m1 hkey
      rw [hk_ev]

def buildFwdA {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) : List (GateDef k) × Vec k :=
  let (st1, initV) := buildFwdInit hk 0 (by decide) 1 st (inVec k 2) (inVec k 0)
  buildFwdLoop hk 0 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1) (inVec k 2) r st1 initV

def buildFwdB {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) : List (GateDef k) × Vec k :=
  let (st1, initV) := buildFwdInit hk 1 (by decide) 3 st (inVec k 2) (inVec k 1)
  buildFwdLoop hk 1 (by decide) 2 (fun idx => 3 * (idx + 1) + 1) (fun idx => r + (idx + 1)) (inVec k 2) r st1 initV

theorem buildFwdA_spec {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k))
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0) :
    WF (buildFwdA hk r st).1 ∧ (∃ more, (buildFwdA hk r st).1 = st ++ more ∧ more.length ≤ 6 * k * (r + 1)) ∧
    VecValid 0 (buildFwdA hk r st).1 (buildFwdA hk r st).2 (6 * r + 1) ∧
    (∀ v, evalVec v (buildFwdA hk r st).1 (buildFwdA hk r st).2 =
      firstB hk r (fun i => v (2, i)) (fun i => v (0, i))) := by
  dsimp [buildFwdA, buildFwdInit]
  have hi := buildXorVec_spec 0 (by decide) st
    (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 0) 0 0 hwf
    (fun i => inVec_valid 0 2 (Or.inl rfl) st _) (inVec_valid 0 0 (Or.inr rfl) st)
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := hi
  obtain ⟨m0, hm0⟩ := hinit
  have hinit1 : ∃ m', (buildXorVec 0 (by decide) st
      (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 0)).1 = initGates k hk ++ m' :=
    ⟨m0 ++ m1, by rw [hm1, hm0, List.append_assoc]⟩
  have hl := buildFwdLoop_spec hk 0 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1) (inVec k 2) r
    (buildXorVec 0 (by decide) st (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 0)).1
    (buildXorVec 0 (by decide) st (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 0)).2 1
    (le_refl 1) hwf1 hinit1 (by simpa using hv1) (inVec_valid 0 2 (Or.inl rfl) _)
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := hl
  refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], ?_⟩,
    (fun i => ⟨(hv2 i).1, by have := (hv2 i).2; omega⟩), ?_⟩
  · rw [List.length_append, Nat.mul_add, Nat.mul_one]; omega
  · intro v; rw [hev2 v, hev1 v]; rfl

/-! #### Inverse Circuits (`buildInvChi`, `buildInvMix`, `buildInvA`, `buildInvB`) -/

def affCompRev (a b : Bool × Bool) : Bool × Bool := affComp b a

theorem affCompRev_assoc (x y z : Bool × Bool) :
    affCompRev (affCompRev x y) z = affCompRev x (affCompRev y z) :=
  (affComp_assoc z y x).symm

theorem foldl_affCompRev_init (l : List (Bool × Bool)) (init : Bool × Bool) :
    l.foldl affCompRev init = affComp (l.foldl affCompRev affId) init := by
  induction l generalizing init with
  | nil => simp [affComp_id_left]
  | cons a t ih =>
    simp only [List.foldl_cons, affCompRev]
    rw [ih, ih (affComp a affId), affComp_id_right, affComp_assoc]

theorem foldr_drop_eq_reverse_take (l : List (Bool × Bool)) (n : ℕ) (hn : n ≤ l.length) :
    (l.drop (l.length - n)).foldr affComp affId =
      (l.reverse.take n).foldl affCompRev affId := by
  induction l using List.reverseRecOn generalizing n with
  | nil => simp at hn; subst hn; simp
  | append_singleton xs a ih =>
    rw [List.length_append, List.length_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    cases n with
    | zero => simp
    | succ n =>
      have hn' : n ≤ xs.length := by simp at hn; omega
      have hsub : xs.length + 1 - (n + 1) = xs.length - n := by omega
      rw [hsub, List.drop_append_of_le_length (by omega), foldr_affComp_append, ih n hn']
      simp only [List.foldr_cons, List.foldr_nil, List.take_succ_cons, List.foldl_cons]
      have hrev_id : affCompRev affId a = a := affComp_id_right a
      have hr_id : affComp a affId = a := affComp_id_right a
      rw [hrev_id, hr_id, foldl_affCompRev_init (xs.reverse.take n) a]

abbrev PairNode (k : ℕ) := WNode k × WNode k

def depthPair {k : ℕ} (p : PairNode k) : ℕ := max p.1.depth p.2.depth

def validPair {k : ℕ} (owner : Fin 5) (st : List (GateDef k)) (p : PairNode k) : Prop :=
  ValidWire owner st p.1.wire p.1.depth ∧ ValidWire owner st p.2.wire p.2.depth

def evalPair {k : ℕ} (v : Fin 5 × Fin k → Bool) (st : List (GateDef k)) (p : PairNode k) :
    Bool × Bool :=
  (evalW v st p.1.wire, evalW v st p.2.wire)

theorem validPair_mono {k : ℕ} {owner : Fin 5} {st : List (GateDef k)} (more : List (GateDef k))
    {p : PairNode k} (hp : validPair owner st p) :
    validPair owner (st ++ more) p :=
  ⟨ValidWire_mono more (le_refl _) hp.1, ValidWire_mono more (le_refl _) hp.2⟩

theorem evalPair_append {k : ℕ} (v : Fin 5 × Fin k → Bool) {owner : Fin 5}
    {st : List (GateDef k)} (more : List (GateDef k)) {p : PairNode k}
    (hp : validPair owner st p) :
    evalPair v (st ++ more) p = evalPair v st p := by
  dsimp [evalPair]
  rw [evalW_append v more hp.1, evalW_append v more hp.2]

def affCompGate {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2) (st : List (GateDef k))
    (a b : PairNode k) : List (GateDef k) × PairNode k :=
  let (st1, g1) := addGate st owner ho (fun x y => x && y) a.1 b.1
  let (st2, g2) := addGate st1 owner ho (fun x y => x && y) a.1 b.2
  let (st3, g3) := addGate st2 owner ho xor a.2 g2
  (st3, (g1, g3))

theorem affCompGate_spec {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (a b : PairNode k)
    (hwf : WF st) (ha : validPair owner st a) (hb : validPair owner st b) :
    WF (affCompGate owner ho st a b).1 ∧
    (∃ more, (affCompGate owner ho st a b).1 = st ++ more ∧ more.length ≤ 3) ∧
    validPair owner (affCompGate owner ho st a b).1 (affCompGate owner ho st a b).2 ∧
    depthPair (affCompGate owner ho st a b).2 ≤ max (depthPair a) (depthPair b) + 2 ∧
    (∀ v, evalPair v (affCompGate owner ho st a b).1 (affCompGate owner ho st a b).2 =
      affComp (evalPair v st a) (evalPair v st b)) := by
  dsimp [affCompGate]
  have h1 := addGate_wf st owner ho (fun x y => x && y) a.1 b.1 hwf ha.1 hb.1
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hd1⟩ := h1
  set st1 := (addGate st owner ho (fun x y => x && y) a.1 b.1).1
  set g1 := (addGate st owner ho (fun x y => x && y) a.1 b.1).2
  have ha1_1 : ValidWire owner st1 a.1.wire a.1.depth := by
    rw [hm1]; exact ValidWire_mono m1 (le_refl _) ha.1
  have hb2_1 : ValidWire owner st1 b.2.wire b.2.depth := by
    rw [hm1]; exact ValidWire_mono m1 (le_refl _) hb.2
  have h2 := addGate_wf st1 owner ho (fun x y => x && y) a.1 b.2 hwf1 ha1_1 hb2_1
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hd2⟩ := h2
  set st2 := (addGate st1 owner ho (fun x y => x && y) a.1 b.2).1
  set g2 := (addGate st1 owner ho (fun x y => x && y) a.1 b.2).2
  have ha2_2 : ValidWire owner st2 a.2.wire a.2.depth := by
    rw [hm2, hm1, List.append_assoc]; exact ValidWire_mono (m1 ++ m2) (le_refl _) ha.2
  have h3 := addGate_wf st2 owner ho xor a.2 g2 hwf2 ha2_2 hv2
  obtain ⟨hwf3, ⟨m3, hm3, hm3_len⟩, hv3, hd3⟩ := h3
  set st3 := (addGate st2 owner ho xor a.2 g2).1
  have hv1_2 : ValidWire owner st2 g1.wire g1.depth := by
    rw [hm2]; exact ValidWire_mono m2 (le_refl _) hv1
  have hv1_3 : ValidWire owner st3 g1.wire g1.depth := by
    rw [hm3]; exact ValidWire_mono m3 (le_refl _) hv1_2
  have ha2_1 : ValidWire owner st1 a.2.wire a.2.depth := by
    rw [hm1]; exact ValidWire_mono m1 (le_refl _) ha.2
  refine ⟨hwf3, ⟨m1 ++ m2 ++ m3, by rw [hm3, hm2, hm1]; simp only [List.append_assoc], by
    rw [List.length_append, List.length_append]; omega⟩, ⟨hv1_3, hv3⟩, ?_, ?_⟩
  · have ha1d : a.1.depth ≤ max (depthPair a) (depthPair b) := le_trans (le_max_left _ _) (le_max_left _ _)
    have ha2d : a.2.depth ≤ max (depthPair a) (depthPair b) := le_trans (le_max_right _ _) (le_max_left _ _)
    have hb1d : b.1.depth ≤ max (depthPair a) (depthPair b) := le_trans (le_max_left _ _) (le_max_right _ _)
    have hb2d : b.2.depth ≤ max (depthPair a) (depthPair b) := le_trans (le_max_right _ _) (le_max_right _ _)
    dsimp [depthPair]
    rw [hd3, hd2, hd1]
    exact max_le (by omega) (by omega)
  · intro v; dsimp [evalPair, affComp]
    apply Prod.ext
    · dsimp; rw [hm3, evalW_append v m3 hv1_2, hm2, evalW_append v m2 hv1, addGate_eval]
    · dsimp; rw [addGate_eval, addGate_eval, hm2, evalW_append v m2 ha2_1,
        hm1, evalW_append v m1 ha.2, evalW_append v m1 ha.1, evalW_append v m1 hb.2]

def affCompRevGate {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2) (st : List (GateDef k))
    (a b : PairNode k) : List (GateDef k) × PairNode k :=
  affCompGate owner ho st b a

def buildInvChi {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (y : Vec k) : List (GateDef k) × Vec k :=
  let leavesRes := buildMap (fun st0 (p : Fin k) =>
    let i := stride2Idx k p.val hk
    let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    let (st1, w1) := addGate st0 owner ho xor (y i1) trueNode
    (st1, ((w1, y i) : PairNode k))) st (List.finRange k)
  let prefRes := gScanExcl (affCompGate owner ho) (trueNode, falseNode) leavesRes.1 leavesRes.2
  let sufRes := gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) prefRes.1 leavesRes.2.reverse
  let combRes := buildVec (fun st0 (p : Fin k) =>
    let leafP := leavesRes.2.getD p.val (trueNode, falseNode)
    let prefP := prefRes.2.getD p.val (trueNode, falseNode)
    let sufP := sufRes.2.getD (k - 1 - p.val) (trueNode, falseNode)
    let (st1, sufAll) := affCompGate owner ho st0 leafP sufP
    let (st2, w1) := addGate st1 owner ho (fun a b => a && b) sufAll.1 prefP.2
    addGate st2 owner ho xor sufAll.2 w1) sufRes.1
  (combRes.1, fun i => combRes.2 (stride2Inv k hk i))

theorem buildInvChi_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (y : Vec k) (dy : ℕ)
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0) (hy : VecValid owner st y dy) :
    WF (buildInvChi hk owner ho st y).1 ∧
    (∃ more, (buildInvChi hk owner ho st y).1 = st ++ more ∧ more.length ≤ 18 * k) ∧
    VecValid owner (buildInvChi hk owner ho st y).1 (buildInvChi hk owner ho st y).2
      (max dy 1 + 5 + 4 * Nat.clog 2 k) ∧
    (∀ v, evalVec v (buildInvChi hk owner ho st y).1 (buildInvChi hk owner ho st y).2 =
      invChiB hk (evalVec v st y)) := by
  dsimp [buildInvChi]
  let leafStep : List (GateDef k) → Fin k → List (GateDef k) × PairNode k := fun st0 p =>
    let i := stride2Idx k p.val hk
    let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    let (st1, w1) := addGate st0 owner ho xor (y i1) trueNode
    (st1, (w1, y i))
  let invLeaf : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st ++ m
  have hleaves := buildMap_spec leafStep invLeaf
    (fun st0 pr => validPair owner st0 pr ∧ depthPair pr ≤ max dy 1 + 1)
    (fun st0 p pr => ∀ v, evalPair v st0 pr = chiMapAt hk (evalVec v st y) p)
    1
    (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
    (fun st0 more p pr ⟨hvp, hdp⟩ hev =>
      ⟨⟨validPair_mono more hvp, hdp⟩, fun v => by rw [evalPair_append v more hvp, hev v]⟩)
    (fun st0 p ⟨m, hm⟩ hwf0 => by
      dsimp only [leafStep]
      let i := stride2Idx k p.val hk
      let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
      have hy1 : ValidWire owner st0 (y i1).wire (y i1).depth := by
        rw [hm]; exact ValidWire_mono m (le_refl _) (hy i1).1
      have hy0 : ValidWire owner st0 (y i).wire (y i).depth := by
        rw [hm]; exact ValidWire_mono m (le_refl _) (hy i).1
      obtain ⟨m0, hm0⟩ := hinit
      have ht0 : ValidWire owner st0 (trueNode (k := k)).wire (trueNode (k := k)).depth := by
        rw [hm, hm0, List.append_assoc]
        exact ValidWire_mono (m0 ++ m) (le_refl 1) (valid_constNodes hk owner).2
      have had := addGate_wf st0 owner ho xor (y i1) trueNode hwf0 hy1 ht0
      obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hvw1, hdw1⟩ := had
      have hy0_1 : ValidWire owner (addGate st0 owner ho xor (y i1) trueNode).1 (y i).wire (y i).depth := by
        rw [hm1]; exact ValidWire_mono m1 (le_refl _) hy0
      refine ⟨hwf1, ⟨m1, hm1, by omega⟩, ⟨⟨hvw1, hy0_1⟩, ?_⟩, ?_⟩
      · dsimp [depthPair]; rw [hdw1]
        have := (hy i).2; have := (hy i1).2
        change max (max (y i1).depth (trueNode (k := k)).depth + 1) (y i).depth ≤ max dy 1 + 1
        dsimp [trueNode]; omega
      · intro v; dsimp [evalPair, chiMapAt]
        rw [addGate_eval, hm1, evalW_append v m1 hy0, hm, evalW_append v m (hy i1).1,
          evalW_append v m (hy i).1]
        have hte : evalW v (st ++ m) (trueNode (k := k)).wire = true := by
          rw [hm0, List.append_assoc, evalW_append v (m0 ++ m) (valid_constNodes hk 0).2]
          exact (eval_constNodes hk v).2
        rw [hte]
        change (evalW v st (y i1).wire ^^ true, evalW v st (y i).wire) =
          (!(evalVec v st y i1), evalVec v st y i)
        cases h : evalW v st (y i1).wire <;> simp [evalVec, h])
    (List.finRange k) st ⟨[], (List.append_nil st).symm⟩ hwf
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hlen_l, h_leaves⟩ := hleaves
  rw [List.length_finRange] at hm1_len hlen_l
  set st1 := (buildMap leafStep st (List.finRange k)).1
  set leaves := (buildMap leafStep st (List.finRange k)).2
  obtain ⟨m0, hm0⟩ := hinit
  have hconst1 : validPair owner st1 (trueNode, falseNode) := by
    rw [hm1, hm0, List.append_assoc]
    exact ⟨ValidWire_mono (m0 ++ m1) (le_refl 1) (valid_constNodes hk owner).2,
      ValidWire_mono (m0 ++ m1) (le_refl 1) (valid_constNodes hk owner).1⟩
  have hconst_ev1 : ∀ v, evalPair v st1 (trueNode, falseNode) = affId := fun v => by
    dsimp [evalPair, affId]
    rw [hm1, hm0, List.append_assoc]
    rw [evalW_append v (m0 ++ m1) (valid_constNodes hk 0).2,
      evalW_append v (m0 ++ m1) (valid_constNodes hk 0).1]
    exact Prod.ext (eval_constNodes hk v).2 (eval_constNodes hk v).1
  have hl_v : ∀ a ∈ leaves, validPair owner st1 a ∧ depthPair a ≤ max dy 1 + 1 := by
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp ha
    exact (h_leaves q (by rw [List.length_finRange, ← hlen_l]; exact hq)).1
  have hscan_pref : ∀ v,
      WF (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).1 ∧
      (∃ more, (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).1 =
        st1 ++ more ∧ more.length ≤ 2 * k * 3) ∧
      (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).2.length = k ∧
      (∀ (i : ℕ) (hi : i < (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).2.length),
        validPair owner (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).1
          ((gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).2[i]) ∧
        depthPair ((gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).2[i]) ≤
          max dy 1 + 1 + 4 * Nat.clog 2 k ∧
        evalPair v (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).1
          ((gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).2[i]) =
          ((leaves.take i).map (evalPair v st1)).foldl affComp affId) := by
    intro v
    have hsp := gScanExcl_spec (affCompGate owner ho) (evalPair v) depthPair (validPair owner)
      affComp affId (trueNode, falseNode) affComp_assoc 3 2
      (fun st0 more a ha => ⟨validPair_mono more ha, evalPair_append v more ha⟩)
      (fun st0 a b hwf0 ha hb => by
        have h := affCompGate_spec owner ho st0 a b hwf0 ha hb
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2 v, h.2.2.2.1⟩)
      leaves st1 (max dy 1 + 1) hwf1 hconst1 (hconst_ev1 v)
      (by dsimp [depthPair, trueNode, falseNode]; omega) hl_v
    simpa [hlen_l, show 2 * 2 = 4 by rfl] using hsp
  have hsp0 := hscan_pref (fun _ => false)
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hlen_pref, h_pref0⟩ := hsp0
  set st2 := (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).1
  set prefs := (gScanExcl (affCompGate owner ho) (trueNode, falseNode) st1 leaves).2
  have hconst2 : validPair owner st2 (trueNode, falseNode) := by
    rw [hm2]; exact validPair_mono m2 hconst1
  have hconst_ev2 : ∀ v, evalPair v st2 (trueNode, falseNode) = affId := fun v => by
    rw [hm2, evalPair_append v m2 hconst1, hconst_ev1 v]
  have hl_v2 : ∀ a ∈ leaves.reverse, validPair owner st2 a ∧ depthPair a ≤ max dy 1 + 1 := by
    intro a ha
    rw [List.mem_reverse] at ha
    have := hl_v a ha
    rw [hm2]
    exact ⟨validPair_mono m2 this.1, this.2⟩
  have hscan_suf : ∀ v,
      WF (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).1 ∧
      (∃ more, (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).1 =
        st2 ++ more ∧ more.length ≤ 2 * k * 3) ∧
      (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).2.length = k ∧
      (∀ (i : ℕ) (hi : i < (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).2.length),
        validPair owner (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).1
          ((gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).2[i]) ∧
        depthPair ((gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).2[i]) ≤
          max dy 1 + 1 + 4 * Nat.clog 2 k ∧
        evalPair v (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).1
          ((gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).2[i]) =
          ((leaves.reverse.take i).map (evalPair v st2)).foldl affCompRev affId) := by
    intro v
    have hsp := gScanExcl_spec (affCompRevGate owner ho) (evalPair v) depthPair (validPair owner)
      affCompRev affId (trueNode, falseNode) affCompRev_assoc 3 2
      (fun st0 more a ha => ⟨validPair_mono more ha, evalPair_append v more ha⟩)
      (fun st0 a b hwf0 ha hb => by
        dsimp [affCompRevGate, affCompRev]
        have h := affCompGate_spec owner ho st0 b a hwf0 hb ha
        exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2 v, by have := h.2.2.2.1; omega⟩)
      leaves.reverse st2 (max dy 1 + 1) hwf2 hconst2 (hconst_ev2 v)
      (by dsimp [depthPair, trueNode, falseNode]; omega) hl_v2
    simpa [List.length_reverse, hlen_l, show 2 * 2 = 4 by rfl] using hsp
  have hss0 := hscan_suf (fun _ => false)
  obtain ⟨hwf3, ⟨m3, hm3, hm3_len⟩, hlen_suf, h_suf0⟩ := hss0
  set st3 := (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).1
  set sufs := (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode) st2 leaves.reverse).2
  let invComb : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st3 ++ m
  let combStep : List (GateDef k) → Fin k → List (GateDef k) × WNode k := fun st0 p =>
    let leafP := leaves.getD p.val (trueNode, falseNode)
    let prefP := prefs.getD p.val (trueNode, falseNode)
    let sufP := sufs.getD (k - 1 - p.val) (trueNode, falseNode)
    let (st1', sufAll) := affCompGate owner ho st0 leafP sufP
    let (st2', w1) := addGate st1' owner ho (fun a b => a && b) sufAll.1 prefP.2
    addGate st2' owner ho xor sufAll.2 w1
  have hcomb := buildVec_spec owner (max dy 1 + 5 + 4 * Nat.clog 2 k) 5 combStep invComb
    (fun v p => invChiAt hk (evalVec v st y) p)
    (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
    (fun st0 p ⟨m, hm⟩ hwf0 => by
      dsimp only [combStep]
      have hp_l : p.val < leaves.length := by change p.val < (buildMap leafStep st (List.finRange k)).2.length; rw [hlen_l]; exact p.isLt
      have hp_p : p.val < prefs.length := by change p.val < (gScanExcl _ _ st1 leaves).2.length; rw [hlen_pref]; exact p.isLt
      have hp_s : k - 1 - p.val < sufs.length := by change k - 1 - p.val < (gScanExcl _ _ st2 leaves.reverse).2.length; rw [hlen_suf]; omega
      have hleaf_eq : leaves.getD p.val (trueNode, falseNode) = leaves[p.val]'hp_l := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_l]; rfl
      have hpref_eq : prefs.getD p.val (trueNode, falseNode) = prefs[p.val]'hp_p := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_p]; rfl
      have hsuf_eq : sufs.getD (k - 1 - p.val) (trueNode, falseNode) = sufs[k - 1 - p.val]'hp_s := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp_s]; rfl
      rw [hleaf_eq, hpref_eq, hsuf_eq]
      have hlv3 : validPair owner st3 (leaves[p.val]'hp_l) ∧
          depthPair (leaves[p.val]'hp_l) ≤ max dy 1 + 1 := by
        have h0 := (h_leaves p.val (by rw [List.length_finRange]; exact p.isLt)).1
        rw [hm3, hm2, List.append_assoc]
        exact ⟨validPair_mono (m2 ++ m3) h0.1, h0.2⟩
      have hpv3 : validPair owner st3 (prefs[p.val]'hp_p) ∧
          depthPair (prefs[p.val]'hp_p) ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := by
        have h0 := h_pref0 p.val hp_p
        rw [hm3]
        exact ⟨validPair_mono m3 h0.1, h0.2.1⟩
      have hsv3 : validPair owner st3 (sufs[k - 1 - p.val]'hp_s) ∧
          depthPair (sufs[k - 1 - p.val]'hp_s) ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := by
        have h0 := h_suf0 (k - 1 - p.val) hp_s
        exact ⟨h0.1, h0.2.1⟩
      have hlf0 : validPair owner st0 (leaves[p.val]'hp_l) := by rw [hm]; exact validPair_mono m hlv3.1
      have hsf0 : validPair owner st0 (sufs[k - 1 - p.val]'hp_s) := by rw [hm]; exact validPair_mono m hsv3.1
      have hpf0 : validPair owner st0 (prefs[p.val]'hp_p) := by rw [hm]; exact validPair_mono m hpv3.1
      have hag := affCompGate_spec owner ho st0 (leaves[p.val]'hp_l) (sufs[k - 1 - p.val]'hp_s)
        hwf0 hlf0 hsf0
      obtain ⟨hwf_a, ⟨m_a, hm_a, hm_a_len⟩, hva, hda, heva⟩ := hag
      set st_a := (affCompGate owner ho st0 _ _).1
      set sufAll := (affCompGate owner ho st0 _ _).2
      have hpf_a : ValidWire owner st_a (prefs[p.val]'hp_p).2.wire (prefs[p.val]'hp_p).2.depth := by
        rw [hm_a]; exact ValidWire_mono m_a (le_refl _) hpf0.2
      have hg1 := addGate_wf st_a owner ho (fun a b => a && b) sufAll.1 (prefs[p.val]'hp_p).2
        hwf_a hva.1 hpf_a
      obtain ⟨hwf_1, ⟨m_1, hm_1, hm_1_len⟩, hv_1, hd_1⟩ := hg1
      set st_1 := (addGate st_a owner ho (fun a b => a && b) sufAll.1 (prefs[p.val]'hp_p).2).1
      set w_1 := (addGate st_a owner ho (fun a b => a && b) sufAll.1 (prefs[p.val]'hp_p).2).2
      have hsuf2_1 : ValidWire owner st_1 sufAll.2.wire sufAll.2.depth := by
        rw [hm_1]; exact ValidWire_mono m_1 (le_refl _) hva.2
      have hg2 := addGate_wf st_1 owner ho xor sufAll.2 w_1 hwf_1 hsuf2_1 hv_1
      obtain ⟨hwf_2, ⟨m_2, hm_2, hm_2_len⟩, hv_2, hd_2⟩ := hg2
      refine ⟨hwf_2, ⟨m_a ++ m_1 ++ m_2, by rw [hm_2, hm_1, hm_a]; simp only [List.append_assoc], by
        rw [List.length_append, List.length_append]; omega⟩, ⟨hv_2, ?_⟩, ?_⟩
      · have hd_l : depthPair (leaves[p.val]'hp_l) ≤ max dy 1 + 1 := hlv3.2
        have hd_s : depthPair (sufs[k - 1 - p.val]'hp_s) ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := hsv3.2
        have hd_p : (prefs[p.val]'hp_p).2.depth ≤ max dy 1 + 1 + 4 * Nat.clog 2 k :=
          le_trans (le_max_right _ _) hpv3.2
        dsimp [depthPair] at hda hd_l hd_s
        have hd_suf1 : sufAll.1.depth ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := by
          have := le_max_left sufAll.1.depth sufAll.2.depth; omega
        have hd_suf2 : sufAll.2.depth ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := by
          have := le_max_right sufAll.1.depth sufAll.2.depth; omega
        rw [hd_2, hd_1]; omega
      · intro v
        rw [addGate_eval, addGate_eval, hm_1, evalW_append v m_1 hva.2]
        have h_st_suf : evalPair v st_a sufAll =
            affComp (evalPair v st0 (leaves[p.val]'hp_l)) (evalPair v st0 (sufs[k - 1 - p.val]'hp_s)) := heva v
        have h_pf_ev : evalW v st_a (prefs[p.val]'hp_p).2.wire = (evalPair v st2 (prefs[p.val]'hp_p)).2 := by
          rw [hm_a, evalW_append v m_a hpf0.2, hm, evalW_append v m hpv3.1.2,
            hm3, evalW_append v m3 (h_pref0 p.val hp_p).1.2]; rfl
        have h_leaves_map : leaves.map (evalPair v st1) = chiList hk (evalVec v st y) := by
          apply List.ext_getElem
          · simp [hlen_l, chiList]
          · intro q hq1 hq2
            simp only [List.getElem_map, chiList, List.getElem_ofFn]
            have hq_lt : q < k := by simp [chiList] at hq2; exact hq2
            have hq_fin : (List.finRange k)[q]'(by rw [List.length_finRange]; exact hq_lt) = ⟨q, hq_lt⟩ :=
              List.getElem_finRange _
            have := (h_leaves q (by rw [List.length_finRange]; exact hq_lt)).2 v
            rwa [hq_fin] at this
        have h_leaves_rev : leaves.reverse.map (evalPair v st2) = (chiList hk (evalVec v st y)).reverse := by
          rw [← h_leaves_map, List.map_reverse]
          congr 1
          apply List.map_congr_left
          intro a ha
          rw [hm2]
          exact evalPair_append v m2 (hl_v a ha).1
        have h_leaf_eq : evalPair v st0 (leaves[p.val]'hp_l) =
            (chiList hk (evalVec v st y))[p.val]'(by simp [chiList]) := by
          rw [hm, evalPair_append v m hlv3.1, hm3, hm2, List.append_assoc,
            evalPair_append v (m2 ++ m3) (h_leaves p.val (by rw [List.length_finRange]; exact p.isLt)).1.1]
          have heq_m : evalPair v st1 (leaves[p.val]'hp_l) =
              (leaves.map (evalPair v st1))[p.val]'(by rw [List.length_map]; exact hp_l) :=
            (List.getElem_map _).symm
          rw [heq_m]
          simp only [h_leaves_map]
        have h_pref_eq : evalPair v st2 (prefs[p.val]'hp_p) =
            (((chiList hk (evalVec v st y)).take p.val).foldl affComp affId) := by
          have hp_spec := ((hscan_pref v).2.2.2 p.val (by change p.val < (gScanExcl _ _ st1 leaves).2.length; rw [hlen_pref]; exact p.isLt)).2.2
          change evalPair v st2 (prefs[p.val]'hp_p) = _ at hp_spec
          simpa only [List.map_take, h_leaves_map] using hp_spec
        have h_suf_eq : evalPair v st0 (sufs[k - 1 - p.val]'hp_s) =
            ((chiList hk (evalVec v st y)).drop (p.val + 1)).foldr affComp affId := by
          rw [hm, evalPair_append v m hsv3.1]
          have hs_spec := ((hscan_suf v).2.2.2 (k - 1 - p.val) (by change k - 1 - p.val < (gScanExcl _ _ st2 leaves.reverse).2.length; rw [hlen_suf]; omega)).2.2
          change evalPair v st3 (sufs[k - 1 - p.val]'hp_s) = _ at hs_spec
          rw [hs_spec, List.map_take, h_leaves_rev]
          rw [← foldr_drop_eq_reverse_take (chiList hk (evalVec v st y)) (k - 1 - p.val) (by simp [chiList]; omega)]
          have hsub : (chiList hk (evalVec v st y)).length - (k - 1 - p.val) = p.val + 1 := by
            simp [chiList]; omega
          rw [hsub]
        have h_suf_all : evalPair v st_a sufAll = ((chiList hk (evalVec v st y)).drop p.val).foldr affComp affId := by
          rw [h_st_suf, h_leaf_eq, h_suf_eq]
          exact (foldr_affComp_drop (chiList hk (evalVec v st y)) p.val (by simp [chiList])).symm
        change xor (evalPair v st_a sufAll).2 ((evalPair v st_a sufAll).1 && evalW v st_a (prefs[p.val]'hp_p).2.wire) =
          invChiAt hk (evalVec v st y) p
        rw [h_suf_all, h_pf_ev, h_pref_eq]
        rfl)
    st3 ⟨[], (List.append_nil st3).symm⟩ hwf3
  obtain ⟨hwf4, ⟨m4, hm4, hm4_len⟩, hv4, hev4⟩ := hcomb
  refine ⟨hwf4, ⟨m1 ++ m2 ++ m3 ++ m4, ?_, ?_⟩, fun i => hv4 (stride2Inv k hk i), ?_⟩
  · rw [hm4, hm3, hm2, hm1]; simp only [List.append_assoc]
  · rw [List.length_append, List.length_append, List.length_append]; omega
  · intro v; ext i
    change evalVec v (buildVec combStep st3).1 (buildVec combStep st3).2 (stride2Inv k hk i) =
      invChiB hk (evalVec v st y) i
    rw [hev4 v]; rfl

def buildInvMix {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2) (δ : ℕ)
    (st : List (GateDef k)) (y : Vec k) : List (GateDef k) × Vec k :=
  if k < 5 then (st, y)
  else
    let diffsRes := buildMap (fun st0 (p : Fin k) =>
      let i1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
      addGate st0 owner ho xor (y i1) (y i2)) st (List.finRange k)
    let prefRes := gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode diffsRes.1 diffsRes.2
    let pPos : ℕ := inv3Pos k % k
    let pNeg : ℕ := (k - pPos) % k
    let (st1, g0) := addGate prefRes.1 owner ho xor (y ⟨0, hk⟩) (prefRes.2.getD pPos falseNode)
    let (st2, x0) := addGate st1 owner ho xor g0 (prefRes.2.getD pNeg falseNode)
    buildVec (fun st0 (i : Fin k) =>
      addGate st0 owner ho xor x0 (prefRes.2.getD (m3dInv k δ hk i).val falseNode)) st2

theorem buildInvMix_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2) (δ : ℕ)
    (st : List (GateDef k)) (y : Vec k) (dy : ℕ)
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0) (hy : VecValid owner st y dy) :
    WF (buildInvMix hk owner ho δ st y).1 ∧
    (∃ more, (buildInvMix hk owner ho δ st y).1 = st ++ more ∧ more.length ≤ 4 * k + 2) ∧
    VecValid owner (buildInvMix hk owner ho δ st y).1 (buildInvMix hk owner ho δ st y).2
      (max dy 1 + 4 + 2 * Nat.clog 2 k) ∧
    (∀ v, evalVec v (buildInvMix hk owner ho δ st y).1 (buildInvMix hk owner ho δ st y).2 =
      invMixB hk δ (evalVec v st y)) := by
  by_cases hk5 : k < 5
  · dsimp [buildInvMix]
    simp only [hk5, ↓reduceIte]
    exact ⟨hwf, ⟨[], (List.append_nil st).symm, by simp⟩,
      (fun i => ⟨(hy i).1, by have := (hy i).2; omega⟩),
      fun v => by dsimp [invMixB]; simp only [hk5, ↓reduceIte]⟩
  · dsimp [buildInvMix]
    simp only [hk5, ↓reduceIte]
    let diffStep : List (GateDef k) → Fin k → List (GateDef k) × WNode k := fun st0 p =>
      let i1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
      addGate st0 owner ho xor (y i1) (y i2)
    let invDiff : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st ++ m
    have hdiffs := buildMap_spec diffStep invDiff
      (fun st0 w => ValidNode owner st0 w (dy + 1))
      (fun st0 p w => ∀ v, evalW v st0 w.wire = mixDiffAt hk δ (evalVec v st y) p)
      1
      (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
      (fun st0 more p w hv hp => ⟨ValidNode_mono more (le_refl _) hv, fun v => by rw [evalW_append v more hv.1, hp v]⟩)
      (fun st0 p ⟨m, hm⟩ hwf0 => by
        dsimp only [diffStep]
        let i1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
        let i2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
        have hy1 : ValidWire owner st0 (y i1).wire (y i1).depth := by rw [hm]; exact ValidWire_mono m (le_refl _) (hy i1).1
        have hy2 : ValidWire owner st0 (y i2).wire (y i2).depth := by rw [hm]; exact ValidWire_mono m (le_refl _) (hy i2).1
        have had := addGate_wf st0 owner ho xor (y i1) (y i2) hwf0 hy1 hy2
        refine ⟨had.1, ⟨had.2.1.choose, had.2.1.choose_spec.1, by omega⟩, ⟨had.2.2.1, ?_⟩, ?_⟩
        · rw [had.2.2.2]; have := (hy i1).2; have := (hy i2).2; omega
        · intro v; rw [addGate_eval, hm, evalW_append v m (hy i1).1, evalW_append v m (hy i2).1]; rfl)
      (List.finRange k) st ⟨[], (List.append_nil st).symm⟩ hwf
    obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hlen_d, h_diffs⟩ := hdiffs
    rw [List.length_finRange] at hm1_len hlen_d
    set st1 := (buildMap diffStep st (List.finRange k)).1
    set diffs := (buildMap diffStep st (List.finRange k)).2
    obtain ⟨m0, hm0⟩ := hinit
    have hfn1 : ValidWire owner st1 (falseNode (k := k)).wire (falseNode (k := k)).depth := by
      rw [hm1, hm0, List.append_assoc]
      exact ValidWire_mono (m0 ++ m1) (le_refl 1) (valid_constNodes hk owner).1
    have hfn_ev1 : ∀ v, evalW v st1 (falseNode (k := k)).wire = false := fun v => by
      rw [hm1, hm0, List.append_assoc, evalW_append v (m0 ++ m1) (valid_constNodes hk 0).1]
      exact (eval_constNodes hk v).1
    have hd_v : ∀ a ∈ diffs, ValidWire owner st1 a.wire a.depth ∧ a.depth ≤ max dy 1 + 1 := by
      intro a ha
      obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp ha
      have hq' := (h_diffs q (by rw [List.length_finRange, ← hlen_d]; exact hq)).1
      exact ⟨hq'.1, le_trans hq'.2 (by omega)⟩
    have hscan : ∀ v,
        WF (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).1 ∧
        (∃ more, (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).1 =
          st1 ++ more ∧ more.length ≤ 2 * k * 1) ∧
        (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2.length = k ∧
        (∀ (i : ℕ) (hi : i < (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2.length),
          ValidWire owner (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).1
            ((gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2[i]).wire
            ((gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2[i]).depth ∧
          ((gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2[i]).depth ≤
            max dy 1 + 1 + 2 * Nat.clog 2 k ∧
          evalW v (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).1
            ((gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2[i]).wire =
            ((diffs.take i).map (fun w => evalW v st1 w.wire)).foldl xor false) := by
      intro v
      have hsp := gScanExcl_spec (fun st0 a b => addGate st0 owner ho xor a b)
        (fun st0 (w : WNode k) => evalW v st0 w.wire) (fun w => w.depth)
        (fun st0 w => ValidWire owner st0 w.wire w.depth)
        xor false falseNode Bool.xor_assoc 1 1
        (fun st0 more a ha => ⟨ValidWire_mono more (le_refl _) ha, evalW_append v more ha⟩)
        (fun st0 a b hwf0 ha hb => by
          have had := addGate_wf st0 owner ho xor a b hwf0 ha hb
          exact ⟨had.1, ⟨had.2.1.choose, had.2.1.choose_spec.1, by have := had.2.1.choose_spec.2; omega⟩,
            had.2.2.1, addGate_eval v st0 owner ho xor a b, le_of_eq had.2.2.2⟩)
        diffs st1 (max dy 1 + 1) hwf1 hfn1 (hfn_ev1 v) (by dsimp [falseNode]; omega) hd_v
      simpa [hlen_d, show 2 * 1 = 2 by rfl] using hsp
    have hs0 := hscan (fun _ => false)
    obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hlen_p, hp0⟩ := hs0
    set st2 := (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).1
    set prefs := (gScanExcl (fun st0 a b => addGate st0 owner ho xor a b) falseNode st1 diffs).2
    let pPos : ℕ := inv3Pos k % k
    let pNeg : ℕ := (k - pPos) % k
    have hpPos_lt : pPos < prefs.length := by rw [hlen_p]; exact Nat.mod_lt _ hk
    have hpNeg_lt : pNeg < prefs.length := by rw [hlen_p]; exact Nat.mod_lt _ hk
    have hpos_eq : prefs.getD pPos falseNode = prefs[pPos]'hpPos_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpPos_lt]; rfl
    have hneg_eq : prefs.getD pNeg falseNode = prefs[pNeg]'hpNeg_lt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpNeg_lt]; rfl
    have hy0_2 : ValidWire owner st2 (y ⟨0, hk⟩).wire (y ⟨0, hk⟩).depth := by
      rw [hm2, hm1, List.append_assoc]; exact ValidWire_mono (m1 ++ m2) (le_refl _) (hy ⟨0, hk⟩).1
    have hg0 := addGate_wf st2 owner ho xor (y ⟨0, hk⟩) (prefs.getD pPos falseNode) hwf2 hy0_2
      (by rw [hpos_eq]; exact (hp0 pPos hpPos_lt).1)
    obtain ⟨hwf_g0, ⟨mg0, hmg0, hmg0_len⟩, hvg0, hdg0⟩ := hg0
    set st3 := (addGate st2 owner ho xor (y ⟨0, hk⟩) (prefs.getD pPos falseNode)).1
    set g0 := (addGate st2 owner ho xor (y ⟨0, hk⟩) (prefs.getD pPos falseNode)).2
    have hpn_3 : ValidWire owner st3 (prefs.getD pNeg falseNode).wire (prefs.getD pNeg falseNode).depth := by
      rw [hmg0, hneg_eq]; exact ValidWire_mono mg0 (le_refl _) (hp0 pNeg hpNeg_lt).1
    have hx0 := addGate_wf st3 owner ho xor g0 (prefs.getD pNeg falseNode) hwf_g0 hvg0 hpn_3
    obtain ⟨hwf_x0, ⟨mx0, hmx0, hmx0_len⟩, hvx0, hdx0⟩ := hx0
    set st4 := (addGate st3 owner ho xor g0 (prefs.getD pNeg falseNode)).1
    set x0 := (addGate st3 owner ho xor g0 (prefs.getD pNeg falseNode)).2
    have hdx0_le : x0.depth ≤ max dy 1 + 3 + 2 * Nat.clog 2 k := by
      have hy0d : (y ⟨0, hk⟩).depth ≤ dy := (hy ⟨0, hk⟩).2
      have hpd1 : (prefs[pPos]'hpPos_lt).depth ≤ max dy 1 + 1 + 2 * Nat.clog 2 k := (hp0 pPos hpPos_lt).2.1
      have hpd2 : (prefs[pNeg]'hpNeg_lt).depth ≤ max dy 1 + 1 + 2 * Nat.clog 2 k := (hp0 pNeg hpNeg_lt).2.1
      rw [hdx0, hdg0]; rw [hpos_eq, hneg_eq] at *; omega
    have hpref_ev : ∀ v (q : ℕ) (hq : q < k),
        evalW v st2 (prefs[q]'(by rw [hlen_p]; exact hq)).wire = mixPref hk δ (evalVec v st y) q := by
      intro v q hq
      have hs := ((hscan v).2.2.2 q (by rw [(hscan v).2.2.1]; exact hq)).2.2
      rw [hs]
      have hmap : (diffs.take q).map (fun w => evalW v st1 w.wire) =
          (List.range q).map (fun j => mixDiffAt hk δ (evalVec v st y) ⟨j % k, Nat.mod_lt _ hk⟩) := by
        apply List.ext_getElem
        · simp [List.length_take, hlen_d, Nat.min_eq_left (Nat.le_of_lt hq)]
        · intro i hi1 hi2
          simp only [List.getElem_map, List.getElem_take, List.getElem_range]
          have hi_lt : i < k := by simp only [List.length_map, List.length_range] at hi2; omega
          have hdi := (h_diffs i (by rw [List.length_finRange]; exact hi_lt)).2 v
          have hfin : (List.finRange k)[i]'(by rw [List.length_finRange]; exact hi_lt) = ⟨i, hi_lt⟩ :=
            List.getElem_finRange _
          rw [hfin] at hdi
          rw [hdi]; congr 1; ext; exact (Nat.mod_eq_of_lt hi_lt).symm
      rw [hmap]; rfl
    let invOut : List (GateDef k) → Prop := fun st0 => ∃ m, st0 = st4 ++ m
    let outStep : List (GateDef k) → Fin k → List (GateDef k) × WNode k := fun st0 i =>
      addGate st0 owner ho xor x0 (prefs.getD (m3dInv k δ hk i).val falseNode)
    have houts := buildVec_spec owner (max dy 1 + 4 + 2 * Nat.clog 2 k) 1 outStep invOut
      (fun v i => invMixB hk δ (evalVec v st y) i)
      (fun st0 more ⟨m, hm⟩ _ => ⟨m ++ more, by rw [hm, List.append_assoc]⟩)
      (fun st0 i ⟨m, hm⟩ hwf0 => by
        dsimp only [outStep]
        have hi_p : (m3dInv k δ hk i).val < prefs.length := by rw [hlen_p]; exact (m3dInv k δ hk i).isLt
        have hi_eq : prefs.getD (m3dInv k δ hk i).val falseNode = prefs[(m3dInv k δ hk i).val]'hi_p := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_p]; rfl
        rw [hi_eq]
        have hx0' : ValidWire owner st0 x0.wire x0.depth := by rw [hm]; exact ValidWire_mono m (le_refl _) hvx0
        have hp_st4 : ValidWire owner st4 (prefs[(m3dInv k δ hk i).val]'hi_p).wire
            (prefs[(m3dInv k δ hk i).val]'hi_p).depth := by
          rw [hmx0, hmg0, List.append_assoc]
          exact ValidWire_mono (mg0 ++ mx0) (le_refl _) (hp0 _ hi_p).1
        have hp' : ValidWire owner st0 (prefs[(m3dInv k δ hk i).val]'hi_p).wire
            (prefs[(m3dInv k δ hk i).val]'hi_p).depth := by rw [hm]; exact ValidWire_mono m (le_refl _) hp_st4
        have had := addGate_wf st0 owner ho xor x0 (prefs[(m3dInv k δ hk i).val]'hi_p) hwf0 hx0' hp'
        refine ⟨had.1, ⟨had.2.1.choose, had.2.1.choose_spec.1, by omega⟩, ⟨had.2.2.1, ?_⟩, ?_⟩
        · have hpd := (hp0 _ hi_p).2.1
          rw [had.2.2.2]; omega
        · intro v; rw [addGate_eval, hm, evalW_append v m hvx0, evalW_append v m hp_st4]
          rw [addGate_eval, addGate_eval]
          rw [hmg0, evalW_append v mg0 (by rw [hneg_eq]; exact (hp0 pNeg hpNeg_lt).1)]
          rw [hmx0, hmg0, List.append_assoc, evalW_append v (mg0 ++ mx0) (hp0 _ hi_p).1]
          rw [hpos_eq, hneg_eq]
          rw [hpref_ev v pPos (Nat.mod_lt _ hk), hpref_ev v pNeg (Nat.mod_lt _ hk),
            hpref_ev v (m3dInv k δ hk i).val (m3dInv k δ hk i).isLt]
          rw [hm2, hm1, List.append_assoc, evalW_append v (m1 ++ m2) (hy ⟨0, hk⟩).1]
          dsimp [invMixB]
          simp only [hk5, ↓reduceIte]; rfl)
      st4 ⟨[], (List.append_nil st4).symm⟩ hwf_x0
    obtain ⟨hwf5, ⟨m5, hm5, hm5_len⟩, hv5, hev5⟩ := houts
    refine ⟨hwf5, ⟨m1 ++ m2 ++ mg0 ++ mx0 ++ m5, ?_, ?_⟩, hv5, hev5⟩
    · rw [hm5, hmx0, hmg0, hm2, hm1]; simp only [List.append_assoc]
    · rw [List.length_append, List.length_append, List.length_append, List.length_append]; omega

def buildInvRound {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ shift cIdx : ℕ) (st : List (GateDef k)) (y key : Vec k) : List (GateDef k) × Vec k :=
  let (st1, y1) := buildXorKeyConstVec hk owner ho shift cIdx st y key
  let (st2, y2) := buildInvChi hk owner ho st1 y1
  buildInvMix hk owner ho δ st2 y2

theorem buildInvRound_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ shift cIdx : ℕ) (st : List (GateDef k)) (y key : Vec k) (dy : ℕ)
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0)
    (hy : VecValid owner st y dy) (hkey : VecValid owner st key 0) :
    WF (buildInvRound hk owner ho δ shift cIdx st y key).1 ∧
    (∃ more, (buildInvRound hk owner ho δ shift cIdx st y key).1 = st ++ more ∧
      more.length ≤ 24 * k + 2) ∧
    VecValid owner (buildInvRound hk owner ho δ shift cIdx st y key).1
      (buildInvRound hk owner ho δ shift cIdx st y key).2 (dy + 12 + 6 * Nat.clog 2 k) ∧
    (∀ v, evalVec v (buildInvRound hk owner ho δ shift cIdx st y key).1
        (buildInvRound hk owner ho δ shift cIdx st y key).2 =
      invMixB hk δ (invChiB hk (fun i =>
        xor (xor (evalVec v st y i) (rotB hk shift (evalVec v st key) i)) (constBit k cIdx i)))) := by
  dsimp [buildInvRound]
  obtain ⟨m0, hm0⟩ := hinit
  have h1 := buildXorKeyConstVec_spec hk owner ho shift cIdx st y key dy hwf ⟨m0, hm0⟩ hy hkey
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := h1
  have h2 := buildInvChi_spec hk owner ho _ _ (max dy 1 + 2) hwf1
    ⟨m0 ++ m1, by rw [hm1, hm0, List.append_assoc]⟩ hv1
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := h2
  have h3 := buildInvMix_spec hk owner ho δ _ _ (max (max dy 1 + 2) 1 + 5 + 4 * Nat.clog 2 k) hwf2
    ⟨m0 ++ m1 ++ m2, by rw [hm2, hm1, hm0]; simp only [List.append_assoc]⟩ hv2
  obtain ⟨hwf3, ⟨m3, hm3, hm3_len⟩, hv3, hev3⟩ := h3
  refine ⟨hwf3, ⟨m1 ++ m2 ++ m3, by rw [hm3, hm2, hm1]; simp only [List.append_assoc], ?_⟩,
    (fun i => ⟨(hv3 i).1, by have := (hv3 i).2; omega⟩), ?_⟩
  · rw [List.length_append, List.length_append]; omega
  · intro v; rw [hev3 v, hev2 v, hev1 v]

def buildInvLoop {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ : ℕ) (shiftFn constFn : ℕ → ℕ) (key : Vec k) :
    ℕ → List (GateDef k) → Vec k → List (GateDef k) × Vec k
  | 0, st, cur => (st, cur)
  | n + 1, st, cur =>
    let (st1, cur1) := buildInvRound hk owner ho δ (shiftFn n) (constFn n) st cur key
    buildInvLoop hk owner ho δ shiftFn constFn key n st1 cur1

theorem buildInvLoop_spec {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ : ℕ) (shiftFn constFn : ℕ → ℕ) (key : Vec k) :
    ∀ (n : ℕ) (st : List (GateDef k)) (cur : Vec k) (d0 : ℕ),
      WF st → (∃ m0, st = initGates k hk ++ m0) →
      VecValid owner st cur d0 → VecValid owner st key 0 →
      WF (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).1 ∧
      (∃ more, (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).1 = st ++ more ∧
        more.length ≤ (24 * k + 2) * n) ∧
      VecValid owner (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).1
        (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).2
        (d0 + (12 + 6 * Nat.clog 2 k) * n) ∧
      (∀ v, evalVec v (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).1
          (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).2 =
        (List.range n).reverse.foldl (fun acc idx => invMixB hk δ (invChiB hk (fun i =>
          xor (xor (acc i) (rotB hk (shiftFn idx) (evalVec v st key) i))
            (constBit k (constFn idx) i)))) (evalVec v st cur)) := by
  intro n
  induction n with
  | zero =>
    intro st cur d0 hwf _ hcur _
    exact ⟨hwf, ⟨[], (List.append_nil st).symm, by simp⟩, hcur, fun _ => rfl⟩
  | succ n ih =>
    intro st cur d0 hwf ⟨m0, hm0⟩ hcur hkey
    have hr := buildInvRound_spec hk owner ho δ (shiftFn n) (constFn n) st cur key d0
      hwf ⟨m0, hm0⟩ hcur hkey
    obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := hr
    have hinit1 : ∃ m', (buildInvRound hk owner ho δ (shiftFn n) (constFn n) st cur key).1 =
        initGates k hk ++ m' := ⟨m0 ++ m1, by rw [hm1, hm0, List.append_assoc]⟩
    have hkey1 : VecValid owner (buildInvRound hk owner ho δ (shiftFn n) (constFn n) st cur key).1 key 0 := by
      rw [hm1]; exact VecValid_mono m1 (le_refl 0) hkey
    have hrec := ih _ _ (d0 + 12 + 6 * Nat.clog 2 k) hwf1 hinit1 hv1 hkey1
    obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := hrec
    dsimp [buildInvLoop]
    refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], ?_⟩,
      (fun i => ⟨(hv2 i).1, by have := (hv2 i).2; nlinarith⟩), ?_⟩
    · rw [List.length_append]; nlinarith
    · intro v
      rw [hev2 v, hev1 v, List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.foldl_cons]
      have hk_ev : evalVec v (buildInvRound hk owner ho δ (shiftFn n) (constFn n) st cur key).1 key =
          evalVec v st key := by
        rw [hm1]; exact evalVec_append v m1 hkey
      rw [hk_ev]

def buildInvA {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) : List (GateDef k) × Vec k :=
  let (st1, st0) := buildInvLoop hk 3 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1)
    (inVec k 2) r st (inVec k 3)
  buildXorVec 3 (by decide) st1 (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) st0

def buildInvB {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) : List (GateDef k) × Vec k :=
  let (st1, st0) := buildInvLoop hk 4 (by decide) 2 (fun idx => 3 * (idx + 1) + 1)
    (fun idx => r + (idx + 1)) (inVec k 2) r st (inVec k 4)
  buildXorVec 4 (by decide) st1 (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) st0

theorem buildInvA_spec {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k))
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0) :
    WF (buildInvA hk r st).1 ∧
    (∃ more, (buildInvA hk r st).1 = st ++ more ∧ more.length ≤ (24 * k + 2) * (r + 1)) ∧
    VecValid 3 (buildInvA hk r st).1 (buildInvA hk r st).2 (12 * (r + 1) * (Nat.clog 2 k + 1)) ∧
    (∀ v, evalVec v (buildInvA hk r st).1 (buildInvA hk r st).2 =
      invFirstB hk r (fun i => v (2, i)) (fun i => v (3, i))) := by
  dsimp [buildInvA]
  have hl := buildInvLoop_spec hk 3 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1)
    (inVec k 2) r st (inVec k 3) 0 hwf hinit (inVec_valid 3 3 (Or.inr rfl) st)
    (inVec_valid 3 2 (Or.inl rfl) st)
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := hl
  let keyShift : Vec k := fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩
  have hx := buildXorVec_spec 3 (by decide)
    (buildInvLoop hk 3 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1) (inVec k 2) r st (inVec k 3)).1
    keyShift
    (buildInvLoop hk 3 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1) (inVec k 2) r st (inVec k 3)).2
    0 ((12 + 6 * Nat.clog 2 k) * r) hwf1
    (fun i => inVec_valid 3 2 (Or.inl rfl) _ _) (by simpa using hv1)
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := hx
  have hmax : max 0 ((12 + 6 * Nat.clog 2 k) * r) = (12 + 6 * Nat.clog 2 k) * r := Nat.max_eq_right (Nat.zero_le _)
  refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], ?_⟩,
    (fun i => ⟨(hv2 i).1, by have := (hv2 i).2; rw [hmax] at this; nlinarith⟩), ?_⟩
  · rw [List.length_append]; nlinarith
  · intro v; rw [hev2 v, hev1 v]; rfl

theorem buildInvB_spec {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k))
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0) :
    WF (buildInvB hk r st).1 ∧
    (∃ more, (buildInvB hk r st).1 = st ++ more ∧ more.length ≤ (24 * k + 2) * (r + 1)) ∧
    VecValid 4 (buildInvB hk r st).1 (buildInvB hk r st).2 (12 * (r + 1) * (Nat.clog 2 k + 1)) ∧
    (∀ v, evalVec v (buildInvB hk r st).1 (buildInvB hk r st).2 =
      invSecondB hk r (fun i => v (2, i)) (fun i => v (4, i))) := by
  dsimp [buildInvB]
  have hl := buildInvLoop_spec hk 4 (by decide) 2 (fun idx => 3 * (idx + 1) + 1)
    (fun idx => r + (idx + 1)) (inVec k 2) r st (inVec k 4) 0 hwf hinit
    (inVec_valid 4 4 (Or.inr rfl) st) (inVec_valid 4 2 (Or.inl rfl) st)
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := hl
  let keyShift : Vec k := fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩
  have hx := buildXorVec_spec 4 (by decide)
    (buildInvLoop hk 4 (by decide) 2 (fun idx => 3 * (idx + 1) + 1) (fun idx => r + (idx + 1))
      (inVec k 2) r st (inVec k 4)).1
    keyShift
    (buildInvLoop hk 4 (by decide) 2 (fun idx => 3 * (idx + 1) + 1) (fun idx => r + (idx + 1))
      (inVec k 2) r st (inVec k 4)).2
    0 ((12 + 6 * Nat.clog 2 k) * r) hwf1
    (fun i => inVec_valid 4 2 (Or.inl rfl) _ _) (by simpa using hv1)
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := hx
  have hmax : max 0 ((12 + 6 * Nat.clog 2 k) * r) = (12 + 6 * Nat.clog 2 k) * r := Nat.max_eq_right (Nat.zero_le _)
  refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], ?_⟩,
    (fun i => ⟨(hv2 i).1, by have := (hv2 i).2; rw [hmax] at this; nlinarith⟩), ?_⟩
  · rw [List.length_append]; nlinarith
  · intro v; rw [hev2 v, hev1 v]; rfl





theorem buildFwdB_spec {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k))
    (hwf : WF st) (hinit : ∃ m0, st = initGates k hk ++ m0) :
    WF (buildFwdB hk r st).1 ∧ (∃ more, (buildFwdB hk r st).1 = st ++ more ∧ more.length ≤ 6 * k * (r + 1)) ∧
    VecValid 1 (buildFwdB hk r st).1 (buildFwdB hk r st).2 (6 * r + 1) ∧
    (∀ v, evalVec v (buildFwdB hk r st).1 (buildFwdB hk r st).2 =
      secondB hk r (fun i => v (2, i)) (fun i => v (1, i))) := by
  dsimp [buildFwdB, buildFwdInit]
  have hi := buildXorVec_spec 1 (by decide) st
    (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 1) 0 0 hwf
    (fun i => inVec_valid 1 2 (Or.inl rfl) st _) (inVec_valid 1 1 (Or.inr rfl) st)
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := hi
  obtain ⟨m0, hm0⟩ := hinit
  have hinit1 : ∃ m', (buildXorVec 1 (by decide) st
      (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 1)).1 = initGates k hk ++ m' :=
    ⟨m0 ++ m1, by rw [hm1, hm0, List.append_assoc]⟩
  have hl := buildFwdLoop_spec hk 1 (by decide) 2 (fun idx => 3 * (idx + 1) + 1) (fun idx => r + (idx + 1))
    (inVec k 2) r
    (buildXorVec 1 (by decide) st (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 1)).1
    (buildXorVec 1 (by decide) st (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 1)).2
    1 (le_refl 1) hwf1 hinit1 (by simpa using hv1) (inVec_valid 1 2 (Or.inl rfl) _)
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := hl
  refine ⟨hwf2, ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc], ?_⟩,
    (fun i => ⟨(hv2 i).1, by have := (hv2 i).2; omega⟩), ?_⟩
  · rw [List.length_append, Nat.mul_add, Nat.mul_one]; omega
  · intro v; rw [hev2 v, hev1 v]; rfl

/-! ### Section 3c: Gate Depth Bounds, Combined Circuit, CNF Compiler, and Unit Propagation -/

theorem firstB_invFirstB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : ℕ) (rowKey rowOut : Fin k → Bool) :
    firstB hk r rowKey (invFirstB hk r rowKey rowOut) = rowOut := by
  have hinj : Function.Injective (firstB hk r rowKey) := fun x y h => by
    have := congrArg (invFirstB hk r rowKey) h
    simpa [invFirstB_firstB hk hk6 r rowKey] using this
  obtain ⟨rowName, rfl⟩ := Finite.injective_iff_surjective.mp hinj rowOut
  rw [invFirstB_firstB hk hk6 r rowKey]

theorem secondB_invSecondB {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (r : ℕ) (colKey colOut : Fin k → Bool) :
    secondB hk r colKey (invSecondB hk r colKey colOut) = colOut := by
  have hinj : Function.Injective (secondB hk r colKey) := fun x y h => by
    have := congrArg (invSecondB hk r colKey) h
    simpa [invSecondB_secondB hk hk6 r colKey] using this
  obtain ⟨colName, rfl⟩ := Finite.injective_iff_surjective.mp hinj colOut
  rw [invSecondB_secondB hk hk6 r colKey]

def AllDepthLe {k : ℕ} (D : ℕ) (st : List (GateDef k)) : Prop :=
  ∀ g ∈ st, g.depth ≤ D

theorem AllDepthLe_mono {k : ℕ} {D1 D2 : ℕ} (hD : D1 ≤ D2) {st : List (GateDef k)}
    (hst : AllDepthLe D1 st) : AllDepthLe D2 st :=
  fun g hg => le_trans (hst g hg) hD

theorem addGate_allDepth {k : ℕ} (st : List (GateDef k)) (owner : Fin 5) (ho : owner ≠ 2)
    (op : Bool → Bool → Bool) (a b : WNode k) (D : ℕ)
    (ha : a.depth < D) (hb : b.depth < D) (hst : AllDepthLe D st) :
    AllDepthLe D (addGate st owner ho op a b).1 ∧
    (addGate st owner ho op a b).2.depth = max a.depth b.depth + 1 := by
  refine ⟨?_, rfl⟩
  intro g hg
  simp only [addGate, List.mem_append, List.mem_singleton] at hg
  rcases hg with hmem | rfl
  · exact hst g hmem
  · dsimp; omega

theorem addGate2_allDepth {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (op1 op2 : Bool → Bool → Bool) (st : List (GateDef k)) (a b c : WNode k) (D : ℕ)
    (ha : a.depth + 2 ≤ D) (hb : b.depth + 2 ≤ D) (hc : c.depth + 1 ≤ D)
    (hst : AllDepthLe D st) :
    AllDepthLe D (addGate2 owner ho op1 op2 st a b c).1 := by
  dsimp [addGate2]
  have h1 := addGate_allDepth st owner ho op1 a b D (by omega) (by omega) hst
  exact (addGate_allDepth _ owner ho op2 _ c D (by rw [h1.2]; omega) (by omega) h1.1).1

theorem buildMap_allDepth {k : ℕ} {α β : Type}
    (step : List (GateDef k) → α → List (GateDef k) × β) (D : ℕ)
    (hstep : ∀ st x, AllDepthLe D st → AllDepthLe D (step st x).1) :
    ∀ (xs : List α) (st : List (GateDef k)), AllDepthLe D st →
      AllDepthLe D (buildMap step st xs).1 := by
  intro xs
  induction xs with
  | nil => intro st hst; exact hst
  | cons x xs ih =>
    intro st hst
    exact ih (step st x).1 (hstep st x hst)

theorem buildVec_allDepth {k : ℕ} (step : List (GateDef k) → Fin k → List (GateDef k) × WNode k)
    (D : ℕ) (hstep : ∀ st i, AllDepthLe D st → AllDepthLe D (step st i).1)
    (st : List (GateDef k)) (hst : AllDepthLe D st) :
    AllDepthLe D (buildVec step st).1 :=
  buildMap_allDepth step D (fun st0 i h => hstep st0 i h) (List.finRange k) st hst

theorem gPairUp_allDepth {k : ℕ} {α : Type}
    (comb : List (GateDef k) → α → α → List (GateDef k) × α)
    (depthA : α → ℕ) (dc : ℕ)
    (h_comb : ∀ st a b D', AllDepthLe D' st → max (depthA a) (depthA b) + dc ≤ D' →
      AllDepthLe D' (comb st a b).1 ∧ depthA (comb st a b).2 ≤ max (depthA a) (depthA b) + dc) :
    ∀ (xs : List α) (st : List (GateDef k)) (d D' : ℕ),
      AllDepthLe D' st → (∀ x ∈ xs, depthA x ≤ d) → d + dc ≤ D' →
      AllDepthLe D' (gPairUp comb st xs).1 ∧ ∀ p ∈ (gPairUp comb st xs).2, depthA p ≤ d + dc := by
  intro xs
  induction n_eq : xs.length using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
    intro st d D' hst hxs hd
    cases xs with
    | nil => exact ⟨hst, fun p hp => by simp [gPairUp] at hp⟩
    | cons a rest0 =>
      cases rest0 with
      | nil =>
        refine ⟨hst, fun p hp => ?_⟩
        simp only [gPairUp, List.mem_singleton] at hp
        rw [hp]
        exact le_trans (hxs a (by simp)) (Nat.le_add_right _ _)
      | cons b rest =>
        have ha := hxs a (by simp)
        have hb := hxs b (by simp)
        have hc := h_comb st a b D' hst (by omega)
        have hrec := ih rest.length (by simp at n_eq; omega) rest rfl (comb st a b).1 d D' hc.1
          (fun x hx => hxs x (by simp [hx])) hd
        refine ⟨hrec.1, fun p hp => ?_⟩
        simp only [gPairUp, List.mem_cons] at hp
        rcases hp with rfl | hp'
        · exact le_trans hc.2 (by omega)
        · exact hrec.2 p hp'

theorem gExpandDown_allDepth {k : ℕ} {α : Type}
    (comb : List (GateDef k) → α → α → List (GateDef k) × α)
    (depthA : α → ℕ) (dc : ℕ)
    (h_comb : ∀ st a b D', AllDepthLe D' st → max (depthA a) (depthA b) + dc ≤ D' →
      AllDepthLe D' (comb st a b).1 ∧ depthA (comb st a b).2 ≤ max (depthA a) (depthA b) + dc) :
    ∀ (xs ps : List α) (st : List (GateDef k)) (dp dx D' : ℕ),
      AllDepthLe D' st → (∀ p ∈ ps, depthA p ≤ dp) → (∀ x ∈ xs, depthA x ≤ dx) →
      max dp dx + dc ≤ D' →
      AllDepthLe D' (gExpandDown comb st ps xs).1 ∧
      ∀ o ∈ (gExpandDown comb st ps xs).2, depthA o ≤ max dp dx + dc := by
  intro xs
  induction n_eq : xs.length using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
    intro ps st dp dx D' hst hps hxs hd
    match xs, ps with
    | [], [] => exact ⟨hst, fun o ho => by simp [gExpandDown] at ho⟩
    | [], _ :: _ => exact ⟨hst, fun o ho => by simp [gExpandDown] at ho⟩
    | [_], [] => exact ⟨hst, fun o ho => by simp [gExpandDown] at ho⟩
    | [_], p :: _ =>
      refine ⟨hst, fun o ho => ?_⟩
      simp only [gExpandDown, List.mem_singleton] at ho
      rw [ho]
      exact le_trans (le_trans (hps p (by simp)) (le_max_left _ _)) (Nat.le_add_right _ _)
    | a :: b :: rest, [] => exact ⟨hst, fun o ho => by simp [gExpandDown] at ho⟩
    | a :: b :: rest, p :: ps' =>
      have hp0 := hps p (by simp)
      have ha0 := hxs a (by simp)
      have hc := h_comb st p a D' hst (by omega)
      have hrec := ih rest.length (by simp at n_eq; omega) rest rfl ps' (comb st p a).1 dp dx D'
        hc.1 (fun q hq => hps q (by simp [hq])) (fun x hx => hxs x (by simp [hx])) hd
      refine ⟨hrec.1, fun o ho => ?_⟩
      simp only [gExpandDown, List.mem_cons] at ho
      rcases ho with rfl | rfl | ho'
      · exact le_trans (le_trans hp0 (le_max_left _ _)) (Nat.le_add_right _ _)
      · exact le_trans hc.2 (by omega)
      · exact hrec.2 o ho'

theorem gScanExcl_allDepth {k : ℕ} {α : Type}
    (comb : List (GateDef k) → α → α → List (GateDef k) × α)
    (depthA : α → ℕ) (dc : ℕ) (idVal : α)
    (h_comb : ∀ st a b D', AllDepthLe D' st → max (depthA a) (depthA b) + dc ≤ D' →
      AllDepthLe D' (comb st a b).1 ∧ depthA (comb st a b).2 ≤ max (depthA a) (depthA b) + dc) :
    ∀ (xs : List α) (st : List (GateDef k)) (d0 D' : ℕ),
      AllDepthLe D' st → depthA idVal ≤ d0 → (∀ x ∈ xs, depthA x ≤ d0) →
      d0 + 2 * dc * Nat.clog 2 xs.length ≤ D' →
      AllDepthLe D' (gScanExcl comb idVal st xs).1 ∧
      ∀ o ∈ (gScanExcl comb idVal st xs).2, depthA o ≤ d0 + 2 * dc * Nat.clog 2 xs.length := by
  intro xs
  induction n_eq : xs.length using Nat.strong_induction_on generalizing xs with
  | ind n ih =>
    intro st d0 D' hst hid hxs hd
    unfold gScanExcl
    split_ifs with hlen1
    · cases xs with
      | nil => exact ⟨hst, fun o ho => by simp at ho⟩
      | cons a rest =>
        cases rest with
        | nil =>
          refine ⟨hst, fun o ho => ?_⟩
          simp only [List.mem_singleton] at ho; subst ho
          exact le_trans hid (Nat.le_add_right _ _)
        | cons b bs => simp at hlen1
    · set zs := (gPairUp comb st xs).2
      have hlen_zs : zs.length = (xs.length + 1) / 2 := gPairUp_len comb st xs
      have hclog : Nat.clog 2 xs.length = Nat.clog 2 zs.length + 1 := by
        have := Nat.clog_of_one_lt (by decide : 1 < 2) (by omega : 1 < xs.length)
        rw [hlen_zs]; simpa using this
      rw [← n_eq] at hd
      have hD_step : d0 + dc ≤ D' := by rw [hclog, Nat.mul_add, Nat.mul_one] at hd; omega
      have hp := gPairUp_allDepth comb depthA dc h_comb xs st d0 D' hst hxs hD_step
      have hlt_n : zs.length < xs.length := by rw [hlen_zs]; omega
      have hD_rec : (d0 + dc) + 2 * dc * Nat.clog 2 zs.length ≤ D' := by
        rw [hclog, Nat.mul_add, Nat.mul_one] at hd; omega
      have hrec := ih zs.length (by omega) zs rfl (gPairUp comb st xs).1 (d0 + dc) D'
        hp.1 (le_trans hid (Nat.le_add_right _ _)) hp.2 hD_rec
      have he := gExpandDown_allDepth comb depthA dc h_comb xs
        (gScanExcl comb idVal (gPairUp comb st xs).1 zs).2
        (gScanExcl comb idVal (gPairUp comb st xs).1 zs).1
        (d0 + dc + 2 * dc * Nat.clog 2 zs.length) d0 D' hrec.1 hrec.2 hxs
        (by rw [hclog, Nat.mul_add, Nat.mul_one] at hd; omega)
      refine ⟨he.1, fun o ho => ?_⟩
      have ho' := he.2 o ho
      rw [← n_eq, hclog, Nat.mul_add, Nat.mul_one]; omega

theorem affCompGate_allDepth {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (a b : PairNode k) (D' : ℕ)
    (hst : AllDepthLe D' st) (hdep : max (depthPair a) (depthPair b) + 2 ≤ D') :
    AllDepthLe D' (affCompGate owner ho st a b).1 ∧
    depthPair (affCompGate owner ho st a b).2 ≤ max (depthPair a) (depthPair b) + 2 := by
  dsimp [affCompGate, depthPair] at *
  have h1 := addGate_allDepth st owner ho (fun x y => x && y) a.1 b.1 D'
    (by have := le_max_left a.1.depth a.2.depth; omega)
    (by have := le_max_left b.1.depth b.2.depth; omega) hst
  have h2 := addGate_allDepth _ owner ho (fun x y => x && y) a.1 b.2 D'
    (by have := le_max_left a.1.depth a.2.depth; omega)
    (by have := le_max_right b.1.depth b.2.depth; omega) h1.1
  have h3 := addGate_allDepth _ owner ho xor a.2 _ D'
    (by have := le_max_right a.1.depth a.2.depth; omega)
    (by rw [h2.2]; have := le_max_left a.1.depth a.2.depth; have := le_max_right b.1.depth b.2.depth; omega)
    h2.1
  refine ⟨h3.1, ?_⟩
  rw [h1.2, h3.2, h2.2]
  have := le_max_left a.1.depth a.2.depth
  have := le_max_right a.1.depth a.2.depth
  have := le_max_left b.1.depth b.2.depth
  have := le_max_right b.1.depth b.2.depth
  omega

theorem buildMap_allOut {S α β : Type} (step : S → α → S × β) (P : β → Prop)
    (hstep : ∀ s x, P (step s x).2) (xs : List α) (s : S) :
    ∀ b ∈ (buildMap step s xs).2, P b := by
  induction xs generalizing s with
  | nil => intro b hb; simp [buildMap] at hb
  | cons x xs ih =>
    intro b hb
    simp only [buildMap, List.mem_cons] at hb
    rcases hb with rfl | hb'
    · exact hstep s x
    · exact ih (step s x).1 b hb'

theorem buildVec_allOut {k : ℕ} (step : List (GateDef k) → Fin k → List (GateDef k) × WNode k)
    (d : ℕ) (hd : 1 ≤ d) (hstep : ∀ st i, (step st i).2.depth ≤ d)
    (st : List (GateDef k)) :
    ∀ i : Fin k, ((buildVec step st).2 i).depth ≤ d := by
  intro i; dsimp [buildVec]
  rw [List.getD_eq_getElem?_getD]
  cases h : (buildMap step st (List.finRange k)).2[i.val]? with
  | none => dsimp [falseNode]; exact hd
  | some w =>
    have hmem : w ∈ (buildMap step st (List.finRange k)).2 := List.mem_of_getElem? h
    exact buildMap_allOut step (fun w => w.depth ≤ d) hstep _ st w hmem

theorem buildXorVec_depth {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (x y : Vec k) (dx dy D : ℕ)
    (hst : AllDepthLe D st) (hx : ∀ i, (x i).depth ≤ dx) (hy : ∀ i, (y i).depth ≤ dy)
    (hD : max dx dy + 1 ≤ D) :
    AllDepthLe D (buildXorVec owner ho st x y).1 ∧
    ∀ i, ((buildXorVec owner ho st x y).2 i).depth ≤ max dx dy + 1 := by
  dsimp [buildXorVec]
  refine ⟨buildVec_allDepth _ D (fun s i h => (addGate_allDepth s owner ho xor (x i) (y i) D
    (by have := hx i; omega) (by have := hy i; omega) h).1) st hst, ?_⟩
  exact buildVec_allOut _ (max dx dy + 1) (by omega) (fun s i => by
    dsimp [addGate]; have := hx i; have := hy i; omega) st

theorem addGate_depth {k : ℕ} (st : List (GateDef k)) (owner : Fin 5) (ho : owner ≠ 2)
    (op : Bool → Bool → Bool) (a b : WNode k) :
    (addGate st owner ho op a b).2.depth = max a.depth b.depth + 1 := rfl

theorem addGate2_depth {k : ℕ} (owner : Fin 5) (ho : owner ≠ 2)
    (op1 op2 : Bool → Bool → Bool) (st : List (GateDef k)) (a b c : WNode k) :
    (addGate2 owner ho op1 op2 st a b c).2.depth = max (max a.depth b.depth + 1) c.depth + 1 := rfl

theorem ValidWire_take_full {k : ℕ} {owner : Fin 5} {st : List (GateDef k)}
    {n : ℕ} {w : Sum (Fin 5 × Fin k) ℕ} {d1 d2 : ℕ} (hd : d1 ≤ d2)
    (hw : ValidWire owner (st.take n) w d1) : ValidWire owner st w d2 := by
  cases w with
  | inl p => exact hw
  | inr j =>
    obtain ⟨hj, ho, hd1⟩ := hw
    have hjl : j < st.length := by simp at hj; omega
    have hget : (st.take n)[j]'hj = st[j]'hjl := List.getElem_take
    refine ⟨hjl, ?_, ?_⟩
    · rwa [← hget]
    · rw [← hget]; exact le_trans hd1 hd

theorem buildMixVec_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2) (δ : ℕ)
    (st : List (GateDef k)) (x : Vec k) (dx D : ℕ)
    (hst : AllDepthLe D st) (hx : ∀ i, (x i).depth ≤ dx) (hD : dx + 2 ≤ D) :
    AllDepthLe D (buildMixVec hk owner ho δ st x).1 ∧
    ∀ i, ((buildMixVec hk owner ho δ st x).2 i).depth ≤ dx + 2 := by
  dsimp [buildMixVec]
  refine ⟨buildVec_allDepth _ D (fun s i h => addGate2_allDepth owner ho xor xor s (x i)
    (x ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩)
    (x ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩) D
    (by have := hx i; omega)
    (by have := hx ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩; omega)
    (by have := hx ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩; omega) h) st hst, ?_⟩
  exact buildVec_allOut _ (dx + 2) (by omega) (fun s i => by
    rw [addGate2_depth]
    have := hx i
    have := hx ⟨(i.val + k - δ % k) % k, Nat.mod_lt _ hk⟩
    have := hx ⟨(i.val + k - (k - δ % k) % k) % k, Nat.mod_lt _ hk⟩
    omega) st

theorem buildStepVec_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (x : Vec k) (dx D : ℕ)
    (hst : AllDepthLe D st) (hx : ∀ i, (x i).depth ≤ dx) (hD : dx + 2 ≤ D) :
    AllDepthLe D (buildStepVec hk owner ho st x).1 ∧
    ∀ i, ((buildStepVec hk owner ho st x).2 i).depth ≤ dx + 2 := by
  dsimp [buildStepVec]
  refine ⟨buildVec_allDepth _ D (fun s i h => addGate2_allDepth owner ho (fun p q => (!p) && q)
    (fun a b => xor b a) s
    (x ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩)
    (x ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩) (x i) D
    (by have := hx ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩; omega)
    (by have := hx ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩; omega)
    (by have := hx i; omega) h) st hst, ?_⟩
  exact buildVec_allOut _ (dx + 2) (by omega) (fun s i => by
    rw [addGate2_depth]
    have := hx i
    have := hx ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    have := hx ⟨(i.val + 2) % k, Nat.mod_lt _ hk⟩
    omega) st

theorem buildXorKeyConstVec_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (shift cIdx : ℕ) (st : List (GateDef k)) (x key : Vec k) (dx D : ℕ)
    (hst : AllDepthLe D st) (hx : ∀ i, (x i).depth ≤ dx) (hkey : ∀ i, (key i).depth ≤ 0)
    (hD : max dx 1 + 2 ≤ D) :
    AllDepthLe D (buildXorKeyConstVec hk owner ho shift cIdx st x key).1 ∧
    ∀ i, ((buildXorKeyConstVec hk owner ho shift cIdx st x key).2 i).depth ≤ max dx 1 + 2 := by
  dsimp [buildXorKeyConstVec]
  have hconst : ∀ i : Fin k, (constNode k cIdx i).depth ≤ 1 := fun i => by
    dsimp [constNode]; split_ifs <;> simp [trueNode, falseNode]
  refine ⟨buildVec_allDepth _ D (fun s i h => addGate2_allDepth owner ho xor xor s (x i)
    (key ⟨(i.val + k - shift % k) % k, Nat.mod_lt _ hk⟩) (constNode k cIdx i) D
    (by have := hx i; omega)
    (by have := hkey ⟨(i.val + k - shift % k) % k, Nat.mod_lt _ hk⟩; omega)
    (by have := hconst i; omega) h) st hst, ?_⟩
  exact buildVec_allOut _ (max dx 1 + 2) (by omega) (fun s i => by
    rw [addGate2_depth]
    have := hx i
    have := hkey ⟨(i.val + k - shift % k) % k, Nat.mod_lt _ hk⟩
    have := hconst i
    omega) st

theorem buildFwdRound_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ shift cIdx : ℕ) (st : List (GateDef k)) (x key : Vec k) (dx D : ℕ) (hdx : 1 ≤ dx)
    (hst : AllDepthLe D st) (hx : ∀ i, (x i).depth ≤ dx) (hkey : ∀ i, (key i).depth ≤ 0)
    (hD : dx + 6 ≤ D) :
    AllDepthLe D (buildFwdRound hk owner ho δ shift cIdx st x key).1 ∧
    ∀ i, ((buildFwdRound hk owner ho δ shift cIdx st x key).2 i).depth ≤ dx + 6 := by
  dsimp [buildFwdRound]
  have hm := buildMixVec_depth hk owner ho δ st x dx D hst hx (by omega)
  have hs := buildStepVec_depth hk owner ho _ _ (dx + 2) D hm.1 hm.2 (by omega)
  have hxkc := buildXorKeyConstVec_depth hk owner ho shift cIdx _ _ key (dx + 4) D hs.1 hs.2 hkey
    (by rw [Nat.max_eq_left (by omega : 1 ≤ dx + 4)]; omega)
  refine ⟨hxkc.1, fun i => ?_⟩
  have h := hxkc.2 i
  rw [Nat.max_eq_left (by omega : 1 ≤ dx + 4)] at h
  exact h

theorem buildFwdLoop_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ : ℕ) (shiftFn constFn : ℕ → ℕ) (key : Vec k) :
    ∀ (r : ℕ) (st : List (GateDef k)) (cur : Vec k) (d0 D : ℕ),
      1 ≤ d0 → AllDepthLe D st → (∀ i, (cur i).depth ≤ d0) → (∀ i, (key i).depth ≤ 0) →
      d0 + 6 * r ≤ D →
      AllDepthLe D (buildFwdLoop hk owner ho δ shiftFn constFn key r st cur).1 ∧
      ∀ i, ((buildFwdLoop hk owner ho δ shiftFn constFn key r st cur).2 i).depth ≤ d0 + 6 * r := by
  intro r
  induction r with
  | zero =>
    intro st cur d0 D _ hst hcur _ _
    exact ⟨hst, fun i => le_trans (hcur i) (Nat.le_add_right _ _)⟩
  | succ r ih =>
    intro st cur d0 D hd0 hst hcur hkey hD
    dsimp [buildFwdLoop]
    have hrec := ih st cur d0 D hd0 hst hcur hkey (by omega)
    have hr := buildFwdRound_depth hk owner ho δ (shiftFn r) (constFn r) _ _ key (d0 + 6 * r) D
      (by omega) hrec.1 hrec.2 hkey (by omega)
    refine ⟨hr.1, fun i => ?_⟩
    have h := hr.2 i; omega

theorem buildFwdA_depth {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) (D : ℕ)
    (hst : AllDepthLe D st) (hD : 6 * r + 1 ≤ D) :
    AllDepthLe D (buildFwdA hk r st).1 := by
  dsimp [buildFwdA, buildFwdInit]
  have hx := buildXorVec_depth 0 (by decide) st
    (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 0) 0 0 D
    hst (fun _ => le_refl 0) (fun _ => le_refl 0) (by omega)
  exact (buildFwdLoop_depth hk 0 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1)
    (inVec k 2) r _ _ 1 D (le_refl 1) hx.1 hx.2 (fun _ => le_refl 0) (by omega)).1

theorem buildFwdB_depth {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) (D : ℕ)
    (hst : AllDepthLe D st) (hD : 6 * r + 1 ≤ D) :
    AllDepthLe D (buildFwdB hk r st).1 := by
  dsimp [buildFwdB, buildFwdInit]
  have hx := buildXorVec_depth 1 (by decide) st
    (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) (inVec k 1) 0 0 D
    hst (fun _ => le_refl 0) (fun _ => le_refl 0) (by omega)
  exact (buildFwdLoop_depth hk 1 (by decide) 2 (fun idx => 3 * (idx + 1) + 1)
    (fun idx => r + (idx + 1)) (inVec k 2) r _ _ 1 D (le_refl 1) hx.1 hx.2
    (fun _ => le_refl 0) (by omega)).1

theorem buildInvChi_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (st : List (GateDef k)) (y : Vec k) (dy D : ℕ)
    (hst : AllDepthLe D st) (hy : ∀ i, (y i).depth ≤ dy)
    (hD : max dy 1 + 5 + 4 * Nat.clog 2 k ≤ D) :
    AllDepthLe D (buildInvChi hk owner ho st y).1 ∧
    ∀ i, ((buildInvChi hk owner ho st y).2 i).depth ≤ max dy 1 + 5 + 4 * Nat.clog 2 k := by
  dsimp [buildInvChi]
  let leafStep : List (GateDef k) → Fin k → List (GateDef k) × PairNode k := fun st0 p =>
    let i := stride2Idx k p.val hk
    let i1 : Fin k := ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩
    let (st1, w1) := addGate st0 owner ho xor (y i1) trueNode
    (st1, ((w1, y i) : PairNode k))
  have hst1 : AllDepthLe D (buildMap leafStep st (List.finRange k)).1 :=
    buildMap_allDepth leafStep D (fun s p hs =>
      (addGate_allDepth s owner ho xor (y ⟨((stride2Idx k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩) trueNode D
        (by have := hy ⟨((stride2Idx k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩; have := le_max_left dy 1; omega)
        (by dsimp [trueNode]; have := le_max_right dy 1; omega) hs).1)
      (List.finRange k) st hst
  have hleaves : ∀ a ∈ (buildMap leafStep st (List.finRange k)).2,
      depthPair a ≤ max dy 1 + 1 :=
    buildMap_allOut leafStep (fun a => depthPair a ≤ max dy 1 + 1) (fun s p => by
      dsimp only [leafStep, depthPair]
      rw [addGate_depth]
      dsimp [trueNode]
      have hi := hy (stride2Idx k p.val hk)
      have hi1 := hy ⟨((stride2Idx k p.val hk).val + 1) % k, Nat.mod_lt _ hk⟩
      have hmax1 := le_max_left dy 1
      exact max_le (by omega) (by omega)) (List.finRange k) st
  have hlen_l : (buildMap leafStep st (List.finRange k)).2.length = k := by
    rw [buildMap_len, List.length_finRange]
  have hid : depthPair (trueNode (k := k), falseNode (k := k)) ≤ max dy 1 + 1 := by
    dsimp [depthPair, trueNode, falseNode]; omega
  have hpref := gScanExcl_allDepth (affCompGate owner ho) depthPair 2
    (trueNode (k := k), falseNode (k := k))
    (fun s a b D' hs hdep => affCompGate_allDepth owner ho s a b D' hs hdep)
    (buildMap leafStep st (List.finRange k)).2
    (buildMap leafStep st (List.finRange k)).1
    (max dy 1 + 1) D hst1 hid hleaves (by rw [hlen_l]; omega)
  have hrev_comb : ∀ (s : List (GateDef k)) (a b : PairNode k) (D' : ℕ),
      AllDepthLe D' s → max (depthPair a) (depthPair b) + 2 ≤ D' →
      AllDepthLe D' (affCompRevGate owner ho s a b).1 ∧
      depthPair (affCompRevGate owner ho s a b).2 ≤ max (depthPair a) (depthPair b) + 2 := by
    intro s a b D' hs hdep
    have h := affCompGate_allDepth owner ho s b a D' hs (by rw [max_comm]; exact hdep)
    exact ⟨h.1, by rw [max_comm] at h; exact h.2⟩
  have hleaves_rev : ∀ a ∈ (buildMap leafStep st (List.finRange k)).2.reverse,
      depthPair a ≤ max dy 1 + 1 := fun a ha => hleaves a (List.mem_reverse.mp ha)
  have hsuf := gScanExcl_allDepth (affCompRevGate owner ho) depthPair 2
    (trueNode (k := k), falseNode (k := k)) hrev_comb
    (buildMap leafStep st (List.finRange k)).2.reverse
    (gScanExcl (affCompGate owner ho) (trueNode, falseNode) (buildMap leafStep st (List.finRange k)).1
      (buildMap leafStep st (List.finRange k)).2).1
    (max dy 1 + 1) D hpref.1 hid hleaves_rev
    (by rw [List.length_reverse, hlen_l]; omega)
  rw [hlen_l] at hpref
  rw [List.length_reverse, hlen_l] at hsuf
  set st3 := (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode)
    (gScanExcl (affCompGate owner ho) (trueNode, falseNode)
      (buildMap leafStep st (List.finRange k)).1
      (buildMap leafStep st (List.finRange k)).2).1
    (buildMap leafStep st (List.finRange k)).2.reverse).1
  set leaves := (buildMap leafStep st (List.finRange k)).2
  set prefs := (gScanExcl (affCompGate owner ho) (trueNode, falseNode)
    (buildMap leafStep st (List.finRange k)).1 leaves).2
  set sufs := (gScanExcl (affCompRevGate owner ho) (trueNode, falseNode)
    (gScanExcl (affCompGate owner ho) (trueNode, falseNode)
      (buildMap leafStep st (List.finRange k)).1 leaves).1 leaves.reverse).2
  have hl_get : ∀ p : Fin k, depthPair (leaves.getD p.val (trueNode, falseNode)) ≤ max dy 1 + 1 := by
    intro p
    rw [List.getD_eq_getElem?_getD]
    cases h : leaves[p.val]? with
    | none => exact hid
    | some a => exact hleaves a (List.mem_of_getElem? h)
  have hp_get : ∀ p : Fin k,
      depthPair (prefs.getD p.val (trueNode, falseNode)) ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := by
    intro p
    rw [List.getD_eq_getElem?_getD]
    cases h : prefs[p.val]? with
    | none => exact le_trans hid (Nat.le_add_right _ _)
    | some a => exact hpref.2 a (List.mem_of_getElem? h)
  have hs_get : ∀ p : Fin k,
      depthPair (sufs.getD (k - 1 - p.val) (trueNode, falseNode)) ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := by
    intro p
    rw [List.getD_eq_getElem?_getD]
    cases h : sufs[k - 1 - p.val]? with
    | none => exact le_trans hid (Nat.le_add_right _ _)
    | some a => exact hsuf.2 a (List.mem_of_getElem? h)
  let outStep : List (GateDef k) → Fin k → List (GateDef k) × WNode k := fun st0 p =>
    let sufAll := affCompGate owner ho st0
      (leaves.getD p.val (trueNode, falseNode))
      (sufs.getD (k - 1 - p.val) (trueNode, falseNode))
    let pref := prefs.getD p.val (trueNode, falseNode)
    let (st1', w1) := addGate sufAll.1 owner ho (fun a b => a && b) sufAll.2.1 pref.2
    addGate st1' owner ho xor sufAll.2.2 w1
  have hout_all : AllDepthLe D (buildMap outStep st3 (List.finRange k)).1 :=
    buildMap_allDepth outStep D (fun s p hs => by
      dsimp only [outStep]
      have hl' := hl_get p
      have hs' := hs_get p
      have hp' := hp_get p
      set leaf := leaves.getD p.val (trueNode, falseNode)
      set suf := sufs.getD (k - 1 - p.val) (trueNode, falseNode)
      set pref := prefs.getD p.val (trueNode, falseNode)
      have hag := affCompGate_allDepth owner ho s leaf suf D hs (by omega)
      set st_ag := (affCompGate owner ho s leaf suf).1
      set p_ag := (affCompGate owner ho s leaf suf).2
      have hdp_bound : depthPair p_ag ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := le_trans hag.2 (by omega)
      have hdp1 : p_ag.1.depth ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := le_trans (le_max_left _ _) hdp_bound
      have hdp2 : p_ag.2.depth ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := le_trans (le_max_right _ _) hdp_bound
      have hpf2 : pref.2.depth ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := le_trans (le_max_right _ _) hp'
      have hg1 := addGate_allDepth st_ag owner ho (fun a b => a && b) p_ag.1 pref.2 D
        (by omega) (by omega) hag.1
      set st_1 := (addGate st_ag owner ho (fun a b => a && b) p_ag.1 pref.2).1
      set w_1 := (addGate st_ag owner ho (fun a b => a && b) p_ag.1 pref.2).2
      have hg1d : w_1.depth ≤ max dy 1 + 4 + 4 * Nat.clog 2 k := by
        rw [show w_1.depth = max p_ag.1.depth pref.2.depth + 1 from hg1.2]; omega
      exact (addGate_allDepth st_1 owner ho xor p_ag.2 w_1 D (by omega) (by omega) hg1.1).1)
      (List.finRange k) st3 hsuf.1
  have affCompGate_dp : ∀ (s : List (GateDef k)) (a b : PairNode k),
      depthPair (affCompGate owner ho s a b).2 ≤ max (depthPair a) (depthPair b) + 2 := by
    intro s a b; dsimp [affCompGate, addGate, depthPair]
    have := le_max_left a.1.depth a.2.depth; have := le_max_right a.1.depth a.2.depth
    have := le_max_left b.1.depth b.2.depth; have := le_max_right b.1.depth b.2.depth
    exact max_le (by omega) (by omega)
  let outVec := buildVec outStep st3
  have hout_mem : ∀ w ∈ (buildMap outStep st3 (List.finRange k)).2,
      w.depth ≤ max dy 1 + 5 + 4 * Nat.clog 2 k :=
    buildMap_allOut outStep (fun w => w.depth ≤ max dy 1 + 5 + 4 * Nat.clog 2 k) (fun s p => by
      dsimp only [outStep]
      rw [addGate_depth, addGate_depth]
      have hl' := hl_get p; have hs' := hs_get p; have hp' := hp_get p
      set leaf := leaves.getD p.val (trueNode, falseNode)
      set suf := sufs.getD (k - 1 - p.val) (trueNode, falseNode)
      set pref := prefs.getD p.val (trueNode, falseNode)
      have hag := affCompGate_dp s leaf suf
      set p_ag := (affCompGate owner ho s leaf suf).2
      have hdp_bound : depthPair p_ag ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := le_trans hag (by omega)
      have hpf2 : pref.2.depth ≤ max dy 1 + 1 + 4 * Nat.clog 2 k := le_trans (le_max_right _ _) hp'
      have hs1 : p_ag.1.depth ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := le_trans (le_max_left _ _) hdp_bound
      have hs2 : p_ag.2.depth ≤ max dy 1 + 3 + 4 * Nat.clog 2 k := le_trans (le_max_right _ _) hdp_bound
      omega) (List.finRange k) st3
  refine ⟨hout_all, fun i => ?_⟩
  change (outVec.2 (stride2Inv k hk i)).depth ≤ max dy 1 + 5 + 4 * Nat.clog 2 k
  dsimp [outVec, buildVec]
  rw [List.getD_eq_getElem?_getD]
  cases h : (buildMap outStep st3 (List.finRange k)).2[(stride2Inv k hk i).val]? with
  | none => dsimp [falseNode]; omega
  | some w => exact hout_mem w (List.mem_of_getElem? h)

theorem buildInvMix_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2) (δ : ℕ)
    (st : List (GateDef k)) (y : Vec k) (dy D : ℕ)
    (hst : AllDepthLe D st) (hy : ∀ i, (y i).depth ≤ dy)
    (hD : max dy 1 + 4 + 2 * Nat.clog 2 k ≤ D) :
    AllDepthLe D (buildInvMix hk owner ho δ st y).1 ∧
    ∀ i, ((buildInvMix hk owner ho δ st y).2 i).depth ≤ max dy 1 + 4 + 2 * Nat.clog 2 k := by
  by_cases hk5 : k < 5
  · dsimp [buildInvMix]; simp only [hk5, ↓reduceIte]
    exact ⟨hst, fun i => le_trans (hy i) (by omega)⟩
  · dsimp [buildInvMix]; simp only [hk5, ↓reduceIte]
    let diffStep : List (GateDef k) → Fin k → List (GateDef k) × WNode k := fun st0 p =>
      let i1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
      let i2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
      addGate st0 owner ho xor (y i1) (y i2)
    have hst1 : AllDepthLe D (buildMap diffStep st (List.finRange k)).1 :=
      buildMap_allDepth diffStep D (fun s p hs => by
        let i1 : Fin k := ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
        let i2 : Fin k := ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
        exact (addGate_allDepth s owner ho xor (y i1) (y i2) D
          (by have := hy i1; omega) (by have := hy i2; omega) hs).1)
        (List.finRange k) st hst
    have hdiffs : ∀ a ∈ (buildMap diffStep st (List.finRange k)).2, a.depth ≤ max dy 1 + 1 :=
      buildMap_allOut diffStep (fun a => a.depth ≤ max dy 1 + 1) (fun s p => by
        dsimp only [diffStep]; rw [addGate_depth]
        have hi1 := hy ⟨(3 * δ * p.val + δ) % k, Nat.mod_lt _ hk⟩
        have hi2 := hy ⟨(3 * δ * p.val + 2 * δ) % k, Nat.mod_lt _ hk⟩
        have hml := le_max_left dy 1; omega) (List.finRange k) st
    have hlen_d : (buildMap diffStep st (List.finRange k)).2.length = k := by
      rw [buildMap_len, List.length_finRange]
    have hfn_d : (falseNode (k := k)).depth ≤ max dy 1 + 1 := by dsimp [falseNode]; omega
    have hpref := gScanExcl_allDepth (fun s a b => addGate s owner ho xor a b)
      WNode.depth 1 (falseNode (k := k))
      (fun s a b D' hs hdep => ⟨(addGate_allDepth s owner ho xor a b D'
        (by have := le_max_left a.depth b.depth; omega)
        (by have := le_max_right a.depth b.depth; omega) hs).1,
        by rw [addGate_depth]⟩)
      (buildMap diffStep st (List.finRange k)).2
      (buildMap diffStep st (List.finRange k)).1
      (max dy 1 + 1) D hst1 hfn_d hdiffs (by rw [hlen_d]; omega)
    rw [hlen_d] at hpref
    set prefRes := gScanExcl (fun s a b => addGate s owner ho xor a b) falseNode
      (buildMap diffStep st (List.finRange k)).1 (buildMap diffStep st (List.finRange k)).2
    have hget : ∀ q : ℕ, (prefRes.2.getD q falseNode).depth ≤ max dy 1 + 1 + 2 * Nat.clog 2 k := by
      intro q
      rw [List.getD_eq_getElem?_getD]
      cases h : prefRes.2[q]? with
      | none => exact le_trans hfn_d (Nat.le_add_right _ _)
      | some w => exact hpref.2 w (List.mem_of_getElem? h)
    have hg0 := addGate_allDepth prefRes.1 owner ho xor (y ⟨0, hk⟩) (prefRes.2.getD (inv3Pos k % k) falseNode) D
      (by have := hy ⟨0, hk⟩; omega) (by have := hget (inv3Pos k % k); omega) hpref.1
    set g0 := (addGate prefRes.1 owner ho xor (y ⟨0, hk⟩) (prefRes.2.getD (inv3Pos k % k) falseNode)).2
    set st_g0 := (addGate prefRes.1 owner ho xor (y ⟨0, hk⟩) (prefRes.2.getD (inv3Pos k % k) falseNode)).1
    have hg0_d : g0.depth ≤ max dy 1 + 2 + 2 * Nat.clog 2 k := by
      rw [show g0.depth = max (y ⟨0, hk⟩).depth (prefRes.2.getD (inv3Pos k % k) falseNode).depth + 1 from hg0.2]
      have := hy ⟨0, hk⟩; have := hget (inv3Pos k % k); omega
    have hx0 := addGate_allDepth st_g0 owner ho xor g0
        (prefRes.2.getD ((k - inv3Pos k % k) % k) falseNode) D
      (by omega) (by have := hget ((k - inv3Pos k % k) % k); omega) hg0.1
    set x0 := (addGate st_g0 owner ho xor g0 (prefRes.2.getD ((k - inv3Pos k % k) % k) falseNode)).2
    set st_x0 := (addGate st_g0 owner ho xor g0 (prefRes.2.getD ((k - inv3Pos k % k) % k) falseNode)).1
    have hx0_d : x0.depth ≤ max dy 1 + 3 + 2 * Nat.clog 2 k := by
      rw [show x0.depth = max g0.depth (prefRes.2.getD ((k - inv3Pos k % k) % k) falseNode).depth + 1 from hx0.2]
      have := hget ((k - inv3Pos k % k) % k); omega
    refine ⟨buildVec_allDepth _ D (fun s i hs => (addGate_allDepth s owner ho xor x0
      (prefRes.2.getD (m3dInv k δ hk i).val falseNode) D
      (by omega) (by have := hget (m3dInv k δ hk i).val; omega) hs).1) st_x0 hx0.1, ?_⟩
    exact buildVec_allOut _ (max dy 1 + 4 + 2 * Nat.clog 2 k) (by omega) (fun s i => by
      rw [addGate_depth]; have := hget (m3dInv k δ hk i).val; omega) st_x0

theorem buildInvRound_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ shift cIdx : ℕ) (st : List (GateDef k)) (y key : Vec k) (dy D : ℕ)
    (hst : AllDepthLe D st) (hy : ∀ i, (y i).depth ≤ dy) (hkey : ∀ i, (key i).depth ≤ 0)
    (hD : dy + 12 + 6 * Nat.clog 2 k ≤ D) :
    AllDepthLe D (buildInvRound hk owner ho δ shift cIdx st y key).1 ∧
    ∀ i, ((buildInvRound hk owner ho δ shift cIdx st y key).2 i).depth ≤ dy + 12 + 6 * Nat.clog 2 k := by
  dsimp [buildInvRound]
  have h1 := buildXorKeyConstVec_depth hk owner ho shift cIdx st y key dy D hst hy hkey (by omega)
  have h2 := buildInvChi_depth hk owner ho _ _ (max dy 1 + 2) D h1.1 h1.2 (by omega)
  have h3 := buildInvMix_depth hk owner ho δ _ _ (max (max dy 1 + 2) 1 + 5 + 4 * Nat.clog 2 k) D
    h2.1 h2.2 (by omega)
  refine ⟨h3.1, fun i => ?_⟩
  have h := h3.2 i; omega

theorem buildInvLoop_depth {k : ℕ} (hk : 0 < k) (owner : Fin 5) (ho : owner ≠ 2)
    (δ : ℕ) (shiftFn constFn : ℕ → ℕ) (key : Vec k) :
    ∀ (n : ℕ) (st : List (GateDef k)) (cur : Vec k) (d0 D : ℕ),
      AllDepthLe D st → (∀ i, (cur i).depth ≤ d0) → (∀ i, (key i).depth ≤ 0) →
      d0 + (12 + 6 * Nat.clog 2 k) * n ≤ D →
      AllDepthLe D (buildInvLoop hk owner ho δ shiftFn constFn key n st cur).1 ∧
      ∀ i, ((buildInvLoop hk owner ho δ shiftFn constFn key n st cur).2 i).depth ≤
        d0 + (12 + 6 * Nat.clog 2 k) * n := by
  intro n
  induction n with
  | zero =>
    intro st cur d0 D hst hcur _ _
    dsimp [buildInvLoop]
    refine ⟨hst, fun i => ?_⟩
    exact hcur i
  | succ n ih =>
    intro st cur d0 D hst hcur hkey hD
    dsimp [buildInvLoop]
    have h1 := buildInvRound_depth hk owner ho δ (shiftFn n) (constFn n) st cur key d0 D hst hcur hkey
      (by have : (12 + 6 * Nat.clog 2 k) * (n + 1) = (12 + 6 * Nat.clog 2 k) * n + (12 + 6 * Nat.clog 2 k) := by ring
          omega)
    have hrec := ih _ _ (d0 + 12 + 6 * Nat.clog 2 k) D h1.1 (fun i => by have := h1.2 i; omega) hkey
      (by have : (12 + 6 * Nat.clog 2 k) * (n + 1) = (12 + 6 * Nat.clog 2 k) * n + (12 + 6 * Nat.clog 2 k) := by ring
          omega)
    refine ⟨hrec.1, fun i => ?_⟩
    have h := hrec.2 i
    have : (12 + 6 * Nat.clog 2 k) * (n + 1) = (12 + 6 * Nat.clog 2 k) * n + (12 + 6 * Nat.clog 2 k) := by ring
    omega

theorem buildInvA_depth {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) (D : ℕ)
    (hst : AllDepthLe D st) (hD : 12 * (r + 1) * (Nat.clog 2 k + 1) ≤ D) :
    AllDepthLe D (buildInvA hk r st).1 := by
  dsimp [buildInvA]
  have hmul : (12 + 6 * Nat.clog 2 k) * r + 1 ≤ 12 * (r + 1) * (Nat.clog 2 k + 1) := by
    have h1 : 12 + 6 * Nat.clog 2 k ≤ 12 * (Nat.clog 2 k + 1) := by omega
    calc (12 + 6 * Nat.clog 2 k) * r + 1 ≤ 12 * (Nat.clog 2 k + 1) * r + 1 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_right r h1) 1
      _ ≤ 12 * (r + 1) * (Nat.clog 2 k + 1) := by nlinarith
  have hl := buildInvLoop_depth hk 3 (by decide) 1 (fun idx => 2 * idx) (fun idx => idx + 1)
    (inVec k 2) r st (inVec k 3) 0 D hst (fun _ => le_refl 0) (fun _ => le_refl 0) (by omega)
  exact (buildXorVec_depth 3 (by decide) _
    (fun i => inVec k 2 ⟨(i.val + k - 1 % k) % k, Nat.mod_lt _ hk⟩) _ 0
    (0 + (12 + 6 * Nat.clog 2 k) * r) D hl.1 (fun _ => le_refl 0) hl.2
    (by rw [Nat.zero_add, max_eq_right (Nat.zero_le _)]; exact le_trans hmul hD)).1

theorem buildInvB_depth {k : ℕ} (hk : 0 < k) (r : ℕ) (st : List (GateDef k)) (D : ℕ)
    (hst : AllDepthLe D st) (hD : 12 * (r + 1) * (Nat.clog 2 k + 1) ≤ D) :
    AllDepthLe D (buildInvB hk r st).1 := by
  dsimp [buildInvB]
  have hmul : (12 + 6 * Nat.clog 2 k) * r + 1 ≤ 12 * (r + 1) * (Nat.clog 2 k + 1) := by
    have h1 : 12 + 6 * Nat.clog 2 k ≤ 12 * (Nat.clog 2 k + 1) := by omega
    calc (12 + 6 * Nat.clog 2 k) * r + 1 ≤ 12 * (Nat.clog 2 k + 1) * r + 1 := by
          exact Nat.add_le_add_right (Nat.mul_le_mul_right r h1) 1
      _ ≤ 12 * (r + 1) * (Nat.clog 2 k + 1) := by nlinarith
  have hl := buildInvLoop_depth hk 4 (by decide) 2 (fun idx => 3 * (idx + 1) + 1)
    (fun idx => r + (idx + 1)) (inVec k 2) r st (inVec k 4) 0 D hst
    (fun _ => le_refl 0) (fun _ => le_refl 0) (by omega)
  exact (buildXorVec_depth 4 (by decide) _
    (fun i => inVec k 2 ⟨(i.val + k - 3 % k) % k, Nat.mod_lt _ hk⟩) _ 0
    (0 + (12 + 6 * Nat.clog 2 k) * r) D hl.1 (fun _ => le_refl 0) hl.2
    (by rw [Nat.zero_add, max_eq_right (Nat.zero_le _)]; exact le_trans hmul hD)).1

structure CircuitOut (k : ℕ) where
  st : List (GateDef k)
  fwdA : Vec k
  fwdB : Vec k
  invA : Vec k
  invB : Vec k

def combinedCircuit {k : ℕ} (hk : 0 < k) (r : ℕ) : CircuitOut k :=
  let st0 := initGates k hk
  let (st1, fA) := buildFwdA hk r st0
  let (st2, fB) := buildFwdB hk r st1
  let (st3, iA) := buildInvA hk r st2
  let (st4, iB) := buildInvB hk r st3
  ⟨st4, fA, fB, iA, iB⟩

theorem combinedCircuit_spec {k : ℕ} (hk : 0 < k) (r : ℕ) :
    let out := combinedCircuit hk r
    WF out.st ∧
    2 ≤ out.st.length ∧
    out.st.length ≤ 66 * (k + 1) * (r + 1) ∧
    AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) out.st ∧
    VecValid 0 out.st out.fwdA (6 * r + 1) ∧
    VecValid 1 out.st out.fwdB (6 * r + 1) ∧
    VecValid 3 out.st out.invA (12 * (r + 1) * (Nat.clog 2 k + 1)) ∧
    VecValid 4 out.st out.invB (12 * (r + 1) * (Nat.clog 2 k + 1)) ∧
    (∀ v, evalVec v out.st out.fwdA = firstB hk r (fun i => v (2, i)) (fun i => v (0, i)) ∧
          evalVec v out.st out.fwdB = secondB hk r (fun i => v (2, i)) (fun i => v (1, i)) ∧
          evalVec v out.st out.invA = invFirstB hk r (fun i => v (2, i)) (fun i => v (3, i)) ∧
          evalVec v out.st out.invB = invSecondB hk r (fun i => v (2, i)) (fun i => v (4, i))) := by
  dsimp [combinedCircuit]
  set st0 := initGates k hk
  have hwf0 : WF st0 := wf_initGates k hk
  have hinit0 : ∃ m0, st0 = initGates k hk ++ m0 := ⟨[], (List.append_nil _).symm⟩
  have hdep0 : AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) st0 := fun g hg => by
    simp only [st0, initGates, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> exact by dsimp; nlinarith
  have hfa := buildFwdA_spec hk r st0 hwf0 hinit0
  obtain ⟨hwf1, ⟨m1, hm1, hm1_len⟩, hv1, hev1⟩ := hfa
  set st1 := (buildFwdA hk r st0).1
  set fA := (buildFwdA hk r st0).2
  have hdep1 : AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) st1 :=
    buildFwdA_depth hk r st0 (12 * (r + 1) * (Nat.clog 2 k + 1)) hdep0 (by nlinarith)
  have hfb := buildFwdB_spec hk r st1 hwf1 ⟨m1, hm1⟩
  obtain ⟨hwf2, ⟨m2, hm2, hm2_len⟩, hv2, hev2⟩ := hfb
  set st2 := (buildFwdB hk r st1).1
  set fB := (buildFwdB hk r st1).2
  have hdep2 : AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) st2 :=
    buildFwdB_depth hk r st1 (12 * (r + 1) * (Nat.clog 2 k + 1)) hdep1 (by nlinarith)
  have hia := buildInvA_spec hk r st2 hwf2 ⟨m1 ++ m2, by rw [hm2, hm1, List.append_assoc]⟩
  obtain ⟨hwf3, ⟨m3, hm3, hm3_len⟩, hv3, hev3⟩ := hia
  set st3 := (buildInvA hk r st2).1
  set iA := (buildInvA hk r st2).2
  have hdep3 : AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) st3 :=
    buildInvA_depth hk r st2 (12 * (r + 1) * (Nat.clog 2 k + 1)) hdep2 (le_refl _)
  have hib := buildInvB_spec hk r st3 hwf3
    ⟨m1 ++ m2 ++ m3, by rw [hm3, hm2, hm1]; simp only [st0, List.append_assoc]⟩
  obtain ⟨hwf4, ⟨m4, hm4, hm4_len⟩, hv4, hev4⟩ := hib
  set st4 := (buildInvB hk r st3).1
  set iB := (buildInvB hk r st3).2
  have hdep4 : AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) st4 :=
    buildInvB_depth hk r st3 (12 * (r + 1) * (Nat.clog 2 k + 1)) hdep3 (le_refl _)
  refine ⟨hwf4, ?_, ?_, hdep4, ?_, ?_, ?_, hv4, ?_⟩
  · rw [hm4, hm3, hm2, hm1]
    simp only [List.length_append, st0, initGates, List.length_cons, List.length_nil]; omega
  · rw [hm4, hm3, hm2, hm1]
    simp only [List.length_append, st0, initGates, List.length_cons, List.length_nil]
    have := hm1_len; have := hm2_len; have := hm3_len; have := hm4_len
    nlinarith
  · rw [hm4, hm3, hm2, List.append_assoc, List.append_assoc]
    exact VecValid_mono (m2 ++ (m3 ++ m4)) (le_refl _) hv1
  · rw [hm4, hm3, List.append_assoc]
    exact VecValid_mono (m3 ++ m4) (le_refl _) hv2
  · rw [hm4]
    exact VecValid_mono m4 (le_refl _) hv3
  · intro v
    refine ⟨?_, ?_, ?_, hev4 v⟩
    · rw [hm4, hm3, hm2, List.append_assoc, List.append_assoc, evalVec_append v _ hv1, hev1 v]
    · rw [hm4, hm3, List.append_assoc, evalVec_append v _ hv2, hev2 v]
    · rw [hm4, evalVec_append v _ hv3, hev3 v]

theorem combinedCircuit_pos {k : ℕ} (hk : 0 < k) (r : ℕ) :
    0 < (combinedCircuit hk r).st.length := by
  have := (combinedCircuit_spec hk r).2.1
  omega

def wireVar {k : ℕ} (m : ℕ) (hm : 0 < m) :
    Sum (Fin 5 × Fin k) ℕ → Sum (Fin 5 × Fin k) (Fin m)
  | Sum.inl p => Sum.inl p
  | Sum.inr j => Sum.inr ⟨j % m, Nat.mod_lt j hm⟩

def gateClauses {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length)
    (i : Fin st.length) : List (Clause (Sum (Fin 5 × Fin k) (Fin st.length))) :=
  let g := st[i.val]'i.isLt
  let va := wireVar st.length hpos g.a
  let vb := wireVar st.length hpos g.b
  let vc : Sum (Fin 5 × Fin k) (Fin st.length) := Sum.inr i
  [(false, false), (false, true), (true, false), (true, true)].map fun (b1, b2) =>
    ({(va, !b1), (vb, !b2), (vc, g.op b1 b2)} : Clause _)

def eqPairClauses {k : ℕ} (m : ℕ) (hm : 0 < m) (w : WNode k) (p : Fin 5 × Fin k) :
    List (Clause (Sum (Fin 5 × Fin k) (Fin m))) :=
  [{(wireVar m hm w.wire, false), (Sum.inl p, true)},
   {(wireVar m hm w.wire, true), (Sum.inl p, false)}]

def buildCNFList {k : ℕ} (out : CircuitOut k) (hpos : 0 < out.st.length) :
    List (Clause (Sum (Fin 5 × Fin k) (Fin out.st.length))) :=
  ((List.finRange out.st.length).flatMap (gateClauses out.st hpos)) ++
  ((List.finRange k).flatMap fun i =>
    eqPairClauses out.st.length hpos (out.fwdA i) (3, i) ++
    eqPairClauses out.st.length hpos (out.invA i) (0, i) ++
    eqPairClauses out.st.length hpos (out.fwdB i) (4, i) ++
    eqPairClauses out.st.length hpos (out.invB i) (1, i))

def buildCNF {k : ℕ} (out : CircuitOut k) (hpos : 0 < out.st.length) :
    Finset (Clause (Sum (Fin 5 × Fin k) (Fin out.st.length))) :=
  (buildCNFList out hpos).toFinset

theorem sum_card_toFinset_le {α : Type} [DecidableEq α] (L : List (Finset α)) :
    ∑ C ∈ L.toFinset, C.card ≤ (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons C rest ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hC : C ∈ rest.toFinset
    · rw [Finset.insert_eq_of_mem hC]; omega
    · rw [Finset.sum_insert hC]; omega

theorem sum_map_card_flatMap_le {α β : Type} (xs : List α) (f : α → List (Finset β)) (c : ℕ)
    (hf : ∀ x ∈ xs, ((f x).map Finset.card).sum ≤ c) :
    (((xs.flatMap f).map Finset.card).sum) ≤ xs.length * c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.length_cons]
    have hx := hf x (by simp)
    have hxs := ih (fun y hy => hf y (by simp [hy]))
    nlinarith

theorem gateClauses_card_le_3 {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length)
    (i : Fin st.length) :
    (∀ C ∈ gateClauses st hpos i, C.card ≤ 3) ∧
    ((gateClauses st hpos i).map Finset.card).sum ≤ 12 := by
  dsimp [gateClauses]
  have hle : ∀ b1 b2 : Bool,
      ({(wireVar st.length hpos (st[i.val]'i.isLt).a, !b1),
        (wireVar st.length hpos (st[i.val]'i.isLt).b, !b2),
        (Sum.inr i, (st[i.val]'i.isLt).op b1 b2)} :
        Clause (Sum (Fin 5 × Fin k) (Fin st.length))).card ≤ 3 := by
    intro b1 b2
    exact le_trans (Finset.card_insert_le _ _)
      (Nat.succ_le_succ (le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))))
  refine ⟨fun C hC => ?_, ?_⟩
  · simp only [List.mem_map] at hC
    obtain ⟨⟨b1, b2⟩, _, rfl⟩ := hC
    exact hle b1 b2
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have h00 := hle false false
    have h01 := hle false true
    have h10 := hle true false
    have h11 := hle true true
    omega

theorem eqPairClauses_card_le_3 {k : ℕ} (m : ℕ) (hm : 0 < m) (w : WNode k) (p : Fin 5 × Fin k) :
    (∀ C ∈ eqPairClauses m hm w p, C.card ≤ 3) ∧
    ((eqPairClauses m hm w p).map Finset.card).sum ≤ 4 := by
  dsimp [eqPairClauses]
  have h1 : ({(wireVar m hm w.wire, false), (Sum.inl p, true)} :
      Clause (Sum (Fin 5 × Fin k) (Fin m))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))
  have h2 : ({(wireVar m hm w.wire, true), (Sum.inl p, false)} :
      Clause (Sum (Fin 5 × Fin k) (Fin m))).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (Nat.succ_le_succ (by simp))
  refine ⟨fun C hC => ?_, by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; omega⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl <;> omega

theorem cnf_bounds {k r : ℕ} (hk : 0 < k) :
    let out := combinedCircuit hk r
    let hpos : 0 < out.st.length := combinedCircuit_pos hk r
    let F := buildCNF out hpos
    (∀ C ∈ F, C.card ≤ 3) ∧
    out.st.length + ∑ C ∈ F, C.card ≤ 4096 * (k + 1) * (r + 1) := by
  intro out hpos F
  have hspec := combinedCircuit_spec hk r
  have hm_le : out.st.length ≤ 66 * (k + 1) * (r + 1) := hspec.2.2.1
  refine ⟨fun C hC => ?_, ?_⟩
  · rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset] at hC
    dsimp [buildCNFList] at hC
    rw [List.mem_append] at hC
    rcases hC with hgate | heq
    · rw [List.mem_flatMap] at hgate
      obtain ⟨i, _, hi⟩ := hgate
      exact (gateClauses_card_le_3 out.st hpos i).1 C hi
    · rw [List.mem_flatMap] at heq
      obtain ⟨i, _, hi⟩ := heq
      simp only [List.mem_append] at hi
      rcases hi with ((h1 | h2) | h3) | h4
      · exact (eqPairClauses_card_le_3 out.st.length hpos (out.fwdA i) (3, i)).1 C h1
      · exact (eqPairClauses_card_le_3 out.st.length hpos (out.invA i) (0, i)).1 C h2
      · exact (eqPairClauses_card_le_3 out.st.length hpos (out.fwdB i) (4, i)).1 C h3
      · exact (eqPairClauses_card_le_3 out.st.length hpos (out.invB i) (1, i)).1 C h4
  · have hsum1 : ∑ C ∈ F, C.card ≤ ((buildCNFList out hpos).map Finset.card).sum :=
      sum_card_toFinset_le (buildCNFList out hpos)
    dsimp [buildCNFList] at hsum1
    rw [List.map_append, List.sum_append] at hsum1
    have hgate_sum : (((List.finRange out.st.length).flatMap (gateClauses out.st hpos)).map Finset.card).sum ≤
        out.st.length * 12 := by
      have := sum_map_card_flatMap_le (List.finRange out.st.length) (gateClauses out.st hpos) 12
        (fun i _ => (gateClauses_card_le_3 out.st hpos i).2)
      rwa [List.length_finRange] at this
    have heq_sum : (((List.finRange k).flatMap fun i =>
        eqPairClauses out.st.length hpos (out.fwdA i) (3, i) ++
        eqPairClauses out.st.length hpos (out.invA i) (0, i) ++
        eqPairClauses out.st.length hpos (out.fwdB i) (4, i) ++
        eqPairClauses out.st.length hpos (out.invB i) (1, i)).map Finset.card).sum ≤ k * 16 := by
      have := sum_map_card_flatMap_le (List.finRange k) (fun i =>
          eqPairClauses out.st.length hpos (out.fwdA i) (3, i) ++
          eqPairClauses out.st.length hpos (out.invA i) (0, i) ++
          eqPairClauses out.st.length hpos (out.fwdB i) (4, i) ++
          eqPairClauses out.st.length hpos (out.invB i) (1, i)) 16 (fun i _ => by
        simp only [List.map_append, List.sum_append]
        have h1 := (eqPairClauses_card_le_3 out.st.length hpos (out.fwdA i) (3, i)).2
        have h2 := (eqPairClauses_card_le_3 out.st.length hpos (out.invA i) (0, i)).2
        have h3 := (eqPairClauses_card_le_3 out.st.length hpos (out.fwdB i) (4, i)).2
        have h4 := (eqPairClauses_card_le_3 out.st.length hpos (out.invB i) (1, i)).2
        omega)
      rwa [List.length_finRange] at this
    nlinarith

theorem gateClauses_sat_iff {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length)
    (i : Fin st.length) (u : Sum (Fin 5 × Fin k) (Fin st.length) → Bool) :
    (∀ C ∈ gateClauses st hpos i, ClauseSat u C) ↔
    u (Sum.inr i) = (st[i.val]'i.isLt).op
      (u (wireVar st.length hpos (st[i.val]'i.isLt).a))
      (u (wireVar st.length hpos (st[i.val]'i.isLt).b)) := by
  dsimp [gateClauses]
  set g := st[i.val]'i.isLt
  set va := wireVar st.length hpos g.a
  set vb := wireVar st.length hpos g.b
  set vc : Sum (Fin 5 × Fin k) (Fin st.length) := Sum.inr i
  constructor
  · intro hsat
    have hmem : ({(va, !(u va)), (vb, !(u vb)), (vc, g.op (u va) (u vb))} : Clause _) ∈
        [(false, false), (false, true), (true, false), (true, true)].map (fun (b1, b2) =>
          ({(va, !b1), (vb, !b2), (vc, g.op b1 b2)} : Clause _)) := by
      rw [List.mem_map]
      refine ⟨(u va, u vb), ?_, rfl⟩
      cases u va <;> cases u vb <;> simp
    obtain ⟨l, hlC, hlu⟩ := hsat _ hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlC
    rcases hlC with rfl | rfl | rfl
    · simp at hlu
    · simp at hlu
    · exact hlu
  · intro heq C hC
    rw [List.mem_map] at hC
    obtain ⟨⟨b1, b2⟩, _, rfl⟩ := hC
    by_cases ha : u va = b1
    · by_cases hb : u vb = b2
      · exact ⟨(vc, g.op b1 b2), by simp, by simp [vc, heq, ha, hb]⟩
      · exact ⟨(vb, !b2), by simp, by cases hvb : u vb <;> cases b2 <;> simp_all⟩
    · exact ⟨(va, !b1), by simp, by cases hva : u va <;> cases b1 <;> simp_all⟩

theorem eqPairClauses_sat_iff {k : ℕ} (m : ℕ) (hm : 0 < m) (w : WNode k) (p : Fin 5 × Fin k)
    (u : Sum (Fin 5 × Fin k) (Fin m) → Bool) :
    (∀ C ∈ eqPairClauses m hm w p, ClauseSat u C) ↔
    u (wireVar m hm w.wire) = u (Sum.inl p) := by
  dsimp [eqPairClauses]
  constructor
  · intro hsat
    have h1 := hsat {(wireVar m hm w.wire, false), (Sum.inl p, true)} (by simp)
    have h2 := hsat {(wireVar m hm w.wire, true), (Sum.inl p, false)} (by simp)
    obtain ⟨l1, hl1, hu1⟩ := h1
    obtain ⟨l2, hl2, hu2⟩ := h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl1 hl2
    rcases hl1 with rfl | rfl <;> rcases hl2 with rfl | rfl <;>
      cases hw : u (wireVar m hm w.wire) <;> cases hp : u (Sum.inl p) <;> simp_all
  · intro heq C hC
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hC
    rcases hC with rfl | rfl
    · cases hp : u (Sum.inl p)
      · exact ⟨(wireVar m hm w.wire, false), by simp, by simp [heq, hp]⟩
      · exact ⟨(Sum.inl p, true), by simp, by simp [hp]⟩
    · cases hp : u (Sum.inl p)
      · exact ⟨(Sum.inl p, false), by simp, by simp [hp]⟩
      · exact ⟨(wireVar m hm w.wire, true), by simp, by simp [heq, hp]⟩

theorem wireVar_evalW_lt {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length)
    (v : Fin 5 × Fin k → Bool) (aux : Fin st.length → Bool)
    (haux : ∀ i : Fin st.length, aux i = evalW v st (Sum.inr i.val))
    {owner : Fin 5} {w : Sum (Fin 5 × Fin k) ℕ} {d : ℕ} (hw : ValidWire owner st w d) :
    Sum.elim v aux (wireVar st.length hpos w) = evalW v st w := by
  cases w with
  | inl p => rfl
  | inr j =>
    obtain ⟨hj, _⟩ := hw
    dsimp [wireVar]
    simp only [Nat.mod_eq_of_lt hj, Sum.elim_inr]
    exact haux ⟨j, hj⟩

theorem project_sound_of_agrees {k r : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (v : Fin 5 × Fin k → Bool)
    (h_agree : toNat (fun j => v (3, j)) = toNat (firstB hk r (fun j => v (2, j)) (fun j => v (0, j))) ∧
               toNat (fun j => v (4, j)) = toNat (secondB hk r (fun j => v (2, j)) (fun j => v (1, j)))) :
    let out := combinedCircuit hk r
    let hpos : 0 < out.st.length := combinedCircuit_pos hk r
    let F := buildCNF out hpos
    let aux : Fin out.st.length → Bool := fun i => evalW v out.st (Sum.inr i.val)
    Satisfies (Sum.elim v aux) (↑F : Set _) := by
  intro out hpos F aux C hC
  have hspec := combinedCircuit_spec hk r
  have hwf : WF out.st := hspec.1
  have hv1 := hspec.2.2.2.2.1
  have hv2 := hspec.2.2.2.2.2.1
  have hv3 := hspec.2.2.2.2.2.2.1
  have hv4 := hspec.2.2.2.2.2.2.2.1
  have hev := hspec.2.2.2.2.2.2.2.2 v
  have haux : ∀ i : Fin out.st.length, aux i = evalW v out.st (Sum.inr i.val) := fun _ => rfl
  have hf3 : (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) :=
    toNat_inj h_agree.1
  have hf4 : (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j)) :=
    toNat_inj h_agree.2
  rw [Finset.mem_coe, show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset] at hC
  dsimp [buildCNFList] at hC
  rw [List.mem_append] at hC
  rcases hC with hgate | heq
  · rw [List.mem_flatMap] at hgate
    obtain ⟨i, _, hi⟩ := hgate
    apply (gateClauses_sat_iff out.st hpos i (Sum.elim v aux)).mpr _ C hi
    have hgi := hwf i.val i.isLt
    have ha_w : ValidWire out.st[i.val].owner out.st out.st[i.val].a (out.st[i.val].depth - 1) :=
      ValidWire_take_full (le_refl _) hgi.1
    have hb_w : ValidWire out.st[i.val].owner out.st out.st[i.val].b (out.st[i.val].depth - 1) :=
      ValidWire_take_full (le_refl _) hgi.2.1
    rw [wireVar_evalW_lt out.st hpos v aux haux ha_w, wireVar_evalW_lt out.st hpos v aux haux hb_w]
    exact evalList_getElem v hwf i.val i.isLt
  · rw [List.mem_flatMap] at heq
    obtain ⟨i, _, hi⟩ := heq
    simp only [List.mem_append] at hi
    rcases hi with ((h1 | h2) | h3) | h4
    · apply (eqPairClauses_sat_iff out.st.length hpos (out.fwdA i) (3, i) (Sum.elim v aux)).mpr _ C h1
      rw [wireVar_evalW_lt out.st hpos v aux haux (hv1 i).1]
      have h := congrFun hev.1 i
      dsimp [evalVec] at h
      rw [h, ← hf3]; rfl
    · apply (eqPairClauses_sat_iff out.st.length hpos (out.invA i) (0, i) (Sum.elim v aux)).mpr _ C h2
      rw [wireVar_evalW_lt out.st hpos v aux haux (hv3 i).1]
      have h := congrFun hev.2.2.1 i
      dsimp [evalVec] at h
      rw [h, hf3, invFirstB_firstB hk hk6]; rfl
    · apply (eqPairClauses_sat_iff out.st.length hpos (out.fwdB i) (4, i) (Sum.elim v aux)).mpr _ C h3
      rw [wireVar_evalW_lt out.st hpos v aux haux (hv2 i).1]
      have h := congrFun hev.2.1 i
      dsimp [evalVec] at h
      rw [h, ← hf4]; rfl
    · apply (eqPairClauses_sat_iff out.st.length hpos (out.invB i) (1, i) (Sum.elim v aux)).mpr _ C h4
      rw [wireVar_evalW_lt out.st hpos v aux haux (hv4 i).1]
      have h := congrFun hev.2.2.2 i
      dsimp [evalVec] at h
      rw [h, hf4, invSecondB_secondB hk hk6]; rfl

theorem project_eval_aux {k r : ℕ} (hk : 0 < k)
    (v : Fin 5 × Fin k → Bool)
    (aux : Fin (combinedCircuit hk r).st.length → Bool)
    (hsat : Satisfies (Sum.elim v aux) (↑(buildCNF (combinedCircuit hk r) (combinedCircuit_pos hk r)) : Set _)) :
    ∀ i : Fin (combinedCircuit hk r).st.length,
      aux i = evalW v (combinedCircuit hk r).st (Sum.inr i.val) := by
  have hspec := combinedCircuit_spec hk r
  have hwf : WF (combinedCircuit hk r).st := hspec.1
  have hpos : 0 < (combinedCircuit hk r).st.length := combinedCircuit_pos hk r
  have hgate_mem : ∀ (i : Fin (combinedCircuit hk r).st.length) C,
      C ∈ gateClauses (combinedCircuit hk r).st hpos i → C ∈ buildCNF (combinedCircuit hk r) hpos := by
    intro i C hC
    rw [buildCNF, List.mem_toFinset, buildCNFList, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hC⟩)
  have hall : ∀ n : ℕ, ∀ (hn : n < (combinedCircuit hk r).st.length),
      aux ⟨n, hn⟩ = evalW v (combinedCircuit hk r).st (Sum.inr n) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      have hsat_i := (gateClauses_sat_iff (combinedCircuit hk r).st hpos ⟨n, hn⟩ (Sum.elim v aux)).mp
        (fun C hC => hsat C (hgate_mem ⟨n, hn⟩ C hC))
      have hgn := hwf n hn
      have hwire_eq : ∀ {owner : Fin 5} {w : Sum (Fin 5 × Fin k) ℕ} {d : ℕ},
          ValidWire owner ((combinedCircuit hk r).st.take n) w d →
          Sum.elim v aux (wireVar (combinedCircuit hk r).st.length hpos w) =
            evalW v (combinedCircuit hk r).st w := by
        intro owner w d hw
        cases w with
        | inl p => rfl
        | inr j =>
          obtain ⟨hj, _⟩ := hw
          have hjn : j < n := by simp only [List.length_take] at hj; omega
          have hj_lt : j < (combinedCircuit hk r).st.length := Nat.lt_trans hjn hn
          dsimp [wireVar]
          simp only [Nat.mod_eq_of_lt hj_lt]
          exact ih j hjn hj_lt
      have ha_eq := hwire_eq hgn.1
      have hb_eq := hwire_eq hgn.2.1
      dsimp at hsat_i
      rw [hsat_i, ha_eq, hb_eq]
      exact (evalList_getElem v hwf n hn).symm
  intro i
  exact hall i.val i.isLt

theorem project_spec {k r : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) :
    let out := combinedCircuit hk r
    let hpos : 0 < out.st.length := combinedCircuit_pos hk r
    let F := buildCNF out hpos
    ∀ v : Fin 5 × Fin k → Bool,
      (toNat (fun j => v (3, j)) = toNat (firstB hk r (fun j => v (2, j)) (fun j => v (0, j))) ∧
       toNat (fun j => v (4, j)) = toNat (secondB hk r (fun j => v (2, j)) (fun j => v (1, j)))) ↔
      ∃ aux : Fin out.st.length → Bool, Satisfies (Sum.elim v aux) (↑F : Set _) := by
  intro out hpos F v
  constructor
  · intro h
    exact ⟨fun i => evalW v out.st (Sum.inr i.val), project_sound_of_agrees hk hk6 v h⟩
  · rintro ⟨aux, hsat⟩
    have haux := project_eval_aux hk v aux hsat
    have hspec := combinedCircuit_spec hk r
    have hev := hspec.2.2.2.2.2.2.2.2 v
    have hv1 := hspec.2.2.2.2.1
    have hv2 := hspec.2.2.2.2.2.1
    have hf3 : (fun j => v (3, j)) = firstB hk r (fun j => v (2, j)) (fun j => v (0, j)) := by
      ext j
      have hmem : ∀ C ∈ eqPairClauses out.st.length hpos (out.fwdA j) (3, j), C ∈ F := by
        intro C hC
        rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp [hC]⟩)
      have heq := (eqPairClauses_sat_iff out.st.length hpos (out.fwdA j) (3, j) (Sum.elim v aux)).mp
        (fun C hC => hsat C (hmem C hC))
      rw [wireVar_evalW_lt out.st hpos v aux haux (hv1 j).1] at heq
      have h := congrFun hev.1 j
      dsimp [evalVec] at h
      rw [← h, heq]; rfl
    have hf4 : (fun j => v (4, j)) = secondB hk r (fun j => v (2, j)) (fun j => v (1, j)) := by
      ext j
      have hmem : ∀ C ∈ eqPairClauses out.st.length hpos (out.fwdB j) (4, j), C ∈ F := by
        intro C hC
        rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp [hC]⟩)
      have heq := (eqPairClauses_sat_iff out.st.length hpos (out.fwdB j) (4, j) (Sum.elim v aux)).mp
        (fun C hC => hsat C (hmem C hC))
      rw [wireVar_evalW_lt out.st hpos v aux haux (hv2 j).1] at heq
      have h := congrFun hev.2.1 j
      dsimp [evalVec] at h
      rw [← h, heq]; rfl
    exact ⟨congrArg toNat hf3, congrArg toNat hf4⟩

def upAdvance {V : Type} (F : Finset (Clause V)) (S : Set (Literal V)) : Set (Literal V) :=
  S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l → PEqualNP.Search.negLit other ∈ S}

theorem upAdvance_mono {V : Type} (F : Finset (Clause V)) {S T : Set (Literal V)} (hST : S ⊆ T) :
    upAdvance F S ⊆ upAdvance F T := by
  intro l hl
  rcases hl with hS | ⟨C, hCF, hlC, hother⟩
  · exact Or.inl (hST hS)
  · exact Or.inr ⟨C, hCF, hlC, fun other ho hne => hST (hother other ho hne)⟩

theorem upAdvance_sub {V : Type} (F : Finset (Clause V)) (S : Set (Literal V)) :
    S ⊆ upAdvance F S :=
  fun _ h => Or.inl h

theorem upAdvance_iter_mono {V : Type} (F : Finset (Clause V)) {d1 d2 : ℕ} (hd : d1 ≤ d2)
    (S : Set (Literal V)) :
    (upAdvance F)^[d1] S ⊆ (upAdvance F)^[d2] S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  clear hd
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show d1 + (k + 1) = (d1 + k) + 1 by omega, Function.iterate_succ_apply']
    exact fun l hl => upAdvance_sub F _ (ih hl)

theorem drive_gate_step {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length)
    (F : Finset (Clause (Sum (Fin 5 × Fin k) (Fin st.length))))
    (i : Fin st.length) (hF : ∀ C ∈ gateClauses st hpos i, C ∈ F)
    (u : Sum (Fin 5 × Fin k) (Fin st.length) → Bool)
    (hsat : Satisfies u (↑F : Set _))
    (S : Set (Literal (Sum (Fin 5 × Fin k) (Fin st.length))))
    (ha : (wireVar st.length hpos (st[i.val]'i.isLt).a,
           u (wireVar st.length hpos (st[i.val]'i.isLt).a)) ∈ S)
    (hb : (wireVar st.length hpos (st[i.val]'i.isLt).b,
           u (wireVar st.length hpos (st[i.val]'i.isLt).b)) ∈ S) :
    (Sum.inr i, u (Sum.inr i)) ∈ upAdvance F S := by
  set g := st[i.val]'i.isLt
  set va := wireVar st.length hpos g.a
  set vb := wireVar st.length hpos g.b
  set vc : Sum (Fin 5 × Fin k) (Fin st.length) := Sum.inr i
  have hgu : u vc = g.op (u va) (u vb) :=
    (gateClauses_sat_iff st hpos i u).mp (fun C hC => hsat C (hF C hC))
  have hmem : ({(va, !(u va)), (vb, !(u vb)), (vc, g.op (u va) (u vb))} : Clause _) ∈
      gateClauses st hpos i := by
    dsimp [gateClauses]
    rw [List.mem_map]
    refine ⟨(u va, u vb), ?_, rfl⟩
    cases u va <;> cases u vb <;> simp
  right
  refine ⟨{(va, !(u va)), (vb, !(u vb)), (vc, g.op (u va) (u vb))}, hF _ hmem, ?_, ?_⟩
  · simp [vc, hgu]
  · intro other ho hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with rfl | rfl | heq
    · simp only [PEqualNP.Search.negLit, Bool.not_not]; exact ha
    · simp only [PEqualNP.Search.negLit, Bool.not_not]; exact hb
    · exact absurd (by simpa [vc, hgu] using heq) hne

theorem drive_eq_fwd {k : ℕ} (m : ℕ) (hm : 0 < m) (w : WNode k) (p : Fin 5 × Fin k)
    (F : Finset (Clause (Sum (Fin 5 × Fin k) (Fin m))))
    (hF : ∀ C ∈ eqPairClauses m hm w p, C ∈ F)
    (u : Sum (Fin 5 × Fin k) (Fin m) → Bool)
    (hsat : Satisfies u (↑F : Set _))
    (S : Set (Literal (Sum (Fin 5 × Fin k) (Fin m))))
    (hw : (wireVar m hm w.wire, u (wireVar m hm w.wire)) ∈ S) :
    (Sum.inl p, u (Sum.inl p)) ∈ upAdvance F S := by
  have heq : u (wireVar m hm w.wire) = u (Sum.inl p) :=
    (eqPairClauses_sat_iff m hm w p u).mp (fun C hC => hsat C (hF C hC))
  cases hp : u (Sum.inl p)
  · right
    refine ⟨{(wireVar m hm w.wire, true), (Sum.inl p, false)}, hF _ (by simp [eqPairClauses]), ?_, ?_⟩
    · simp [hp]
    · intro other ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl
      · simpa [PEqualNP.Search.negLit, heq, hp] using hw
      · exact absurd rfl hne
  · right
    refine ⟨{(wireVar m hm w.wire, false), (Sum.inl p, true)}, hF _ (by simp [eqPairClauses]), ?_, ?_⟩
    · simp [hp]
    · intro other ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl
      · simpa [PEqualNP.Search.negLit, heq, hp] using hw
      · exact absurd rfl hne

theorem ValidWire_owner_lift {k : ℕ} {o1 o2 : Fin 5} {st : List (GateDef k)}
    {w : Sum (Fin 5 × Fin k) ℕ} {d : ℕ} (ho : o1 = 2 ∨ o1 = o2)
    (hw : ValidWire o1 st w d) : ValidWire o2 st w d := by
  cases w with
  | inl p =>
    rcases hw with h | h
    · exact Or.inl h
    · rcases ho with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
  | inr j =>
    obtain ⟨hj, hjo, hjd⟩ := hw
    refine ⟨hj, ?_, hjd⟩
    rcases hjo with h | h
    · exact Or.inl h
    · rcases ho with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h

theorem drive_validWire {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length) (hwf : WF st)
    (F : Finset (Clause (Sum (Fin 5 × Fin k) (Fin st.length))))
    (hF : ∀ (i : Fin st.length) C, C ∈ gateClauses st hpos i → C ∈ F)
    (u : Sum (Fin 5 × Fin k) (Fin st.length) → Bool) (hsat : Satisfies u (↑F : Set _))
    (owner : Fin 5) (S : Set (Literal (Sum (Fin 5 × Fin k) (Fin st.length))))
    (hseed : ∀ (t : Fin 5) (j : Fin k), t = 2 ∨ t = owner → (Sum.inl (t, j), u (Sum.inl (t, j))) ∈ S) :
    ∀ (δ : ℕ) (w : Sum (Fin 5 × Fin k) ℕ),
      ValidWire owner st w δ →
      (wireVar st.length hpos w, u (wireVar st.length hpos w)) ∈ (upAdvance F)^[δ] S := by
  intro δ
  induction δ with
  | zero =>
    intro w hw
    cases w with
    | inl p => exact hseed p.1 p.2 hw
    | inr i =>
      obtain ⟨hi, _, hd0⟩ := hw
      have h1 := (hwf i hi).2.2.1
      omega
  | succ δ ih =>
    intro w hw
    cases w with
    | inl p =>
      exact upAdvance_iter_mono F (Nat.zero_le (δ + 1)) S (hseed p.1 p.2 hw)
    | inr i =>
      obtain ⟨hi, ho, hdi⟩ := hw
      have hgi := hwf i hi
      have htake_a : ValidWire st[i].owner st st[i].a δ :=
        ValidWire_take_full (by omega : st[i].depth - 1 ≤ δ) hgi.1
      have htake_b : ValidWire st[i].owner st st[i].b δ :=
        ValidWire_take_full (by omega : st[i].depth - 1 ≤ δ) hgi.2.1
      have ha_v : ValidWire owner st st[i].a δ := ValidWire_owner_lift ho htake_a
      have hb_v : ValidWire owner st st[i].b δ := ValidWire_owner_lift ho htake_b
      dsimp [wireVar]
      simp only [Nat.mod_eq_of_lt hi]
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
      exact drive_gate_step st hpos F ⟨i, hi⟩ (hF ⟨i, hi⟩) u hsat ((upAdvance F)^[δ] S)
        (ih _ ha_v) (ih _ hb_v)

theorem drive_all_gates {k : ℕ} (st : List (GateDef k)) (hpos : 0 < st.length) (hwf : WF st)
    (F : Finset (Clause (Sum (Fin 5 × Fin k) (Fin st.length))))
    (hF : ∀ (i : Fin st.length) C, C ∈ gateClauses st hpos i → C ∈ F)
    (u : Sum (Fin 5 × Fin k) (Fin st.length) → Bool) (hsat : Satisfies u (↑F : Set _))
    (D : ℕ) (hdep : AllDepthLe D st)
    (S : Set (Literal (Sum (Fin 5 × Fin k) (Fin st.length))))
    (hseed : ∀ p : Fin 5 × Fin k, (Sum.inl p, u (Sum.inl p)) ∈ S) :
    ∀ i : Fin st.length, (Sum.inr i, u (Sum.inr i)) ∈ (upAdvance F)^[D] S := by
  have hle : ∀ (δ : ℕ) (i : Fin st.length), st[i.val].depth ≤ δ →
      (Sum.inr i, u (Sum.inr i)) ∈ (upAdvance F)^[δ] S := by
    intro δ
    induction δ with
    | zero =>
      intro i hi
      have h1 := (hwf i.val i.isLt).2.2.1
      omega
    | succ δ ih =>
      intro i hi
      have hgi := hwf i.val i.isLt
      have ha : (wireVar st.length hpos st[i.val].a,
                 u (wireVar st.length hpos st[i.val].a)) ∈ (upAdvance F)^[δ] S := by
        cases ha_w : st[i.val].a with
        | inl p =>
          exact upAdvance_iter_mono F (Nat.zero_le δ) S (hseed p)
        | inr j =>
          have hj := hgi.1
          rw [ha_w] at hj
          obtain ⟨hjt, _, hjd⟩ := hj
          have hjl : j < st.length := by simp at hjt; omega
          have hget : (st.take i.val)[j]'hjt = st[j]'hjl := List.getElem_take
          rw [hget] at hjd
          dsimp [wireVar]
          simp only [Nat.mod_eq_of_lt hjl]
          exact ih ⟨j, hjl⟩ (by dsimp; omega)
      have hb : (wireVar st.length hpos st[i.val].b,
                 u (wireVar st.length hpos st[i.val].b)) ∈ (upAdvance F)^[δ] S := by
        cases hb_w : st[i.val].b with
        | inl p =>
          exact upAdvance_iter_mono F (Nat.zero_le δ) S (hseed p)
        | inr j =>
          have hj := hgi.2.1
          rw [hb_w] at hj
          obtain ⟨hjt, _, hjd⟩ := hj
          have hjl : j < st.length := by simp at hjt; omega
          have hget : (st.take i.val)[j]'hjt = st[j]'hjl := List.getElem_take
          rw [hget] at hjd
          dsimp [wireVar]
          simp only [Nat.mod_eq_of_lt hjl]
          exact ih ⟨j, hjl⟩ (by dsimp; omega)
      rw [Function.iterate_succ_apply']
      exact drive_gate_step st hpos F i (hF i) u hsat ((upAdvance F)^[δ] S) ha hb
  intro i
  exact hle D i (hdep (st[i.val]'i.isLt) (List.getElem_mem _))

theorem drive_fwd_spec {k r : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) :
    let out := combinedCircuit hk r
    let hpos : 0 < out.st.length := combinedCircuit_pos hk r
    let F := buildCNF out hpos
    ∀ pins : Fin 5 × Fin k → Bool,
      let selected : Fin 5 × Fin k → Prop := fun j => j.1 = 2 ∨ j.1 = 0 ∨ j.1 = 1
      let seed : Set (Literal (Sum (Fin 5 × Fin k) (Fin out.st.length))) :=
        {l | ∃ j : Fin 5 × Fin k, selected j ∧ l = (Sum.inl j, pins j)}
      let known := (upAdvance F)^[16 * (r + 1)] seed
      ∃ u : Sum (Fin 5 × Fin k) (Fin out.st.length) → Bool,
        Satisfies u (↑F : Set _) ∧
        (∀ j : Fin 5 × Fin k, selected j → u (Sum.inl j) = pins j) ∧
        ∀ z : Sum (Fin 5 × Fin k) (Fin out.st.length),
          (false = true ∨ ∃ j : Fin 5 × Fin k, z = Sum.inl j) → (z, u z) ∈ known := by
  intro out hpos F pins selected seed known
  have hspec := combinedCircuit_spec hk r
  have hwf : WF out.st := hspec.1
  have hv1 := hspec.2.2.2.2.1
  have hv2 := hspec.2.2.2.2.2.1
  let v : Fin 5 × Fin k → Bool := fun (t, i) =>
    if t = 2 then pins (2, i)
    else if t = 0 then pins (0, i)
    else if t = 1 then pins (1, i)
    else if t = 3 then firstB hk r (fun q => pins (2, q)) (fun q => pins (0, q)) i
    else secondB hk r (fun q => pins (2, q)) (fun q => pins (1, q)) i
  have hv_sel : ∀ j : Fin 5 × Fin k, selected j → v j = pins j := by
    intro ⟨t, i⟩ ht
    rcases ht with h | h | h <;> subst h <;> rfl
  have hag : toNat (fun j => v (3, j)) = toNat (firstB hk r (fun j => v (2, j)) (fun j => v (0, j))) ∧
             toNat (fun j => v (4, j)) = toNat (secondB hk r (fun j => v (2, j)) (fun j => v (1, j))) := by
    constructor <;> rfl
  let aux : Fin out.st.length → Bool := fun i => evalW v out.st (Sum.inr i.val)
  let u : Sum (Fin 5 × Fin k) (Fin out.st.length) → Bool := Sum.elim v aux
  have hsat : Satisfies u (↑F : Set _) := project_sound_of_agrees hk hk6 v hag
  have hgateF : ∀ (i : Fin out.st.length) C, C ∈ gateClauses out.st hpos i → C ∈ F := by
    intro i C hC
    rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hC⟩)
  have heqF_A : ∀ (j : Fin k) C, C ∈ eqPairClauses out.st.length hpos (out.fwdA j) (3, j) → C ∈ F := by
    intro j C hC
    rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp [hC]⟩)
  have heqF_B : ∀ (j : Fin k) C, C ∈ eqPairClauses out.st.length hpos (out.fwdB j) (4, j) → C ∈ F := by
    intro j C hC
    rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, by simp [hC]⟩)
  have hseedA : ∀ (t : Fin 5) (j : Fin k), t = 2 ∨ t = 0 → (Sum.inl (t, j), u (Sum.inl (t, j))) ∈ seed := by
    intro t j ht
    have hsel : selected (t, j) := by rcases ht with rfl | rfl <;> simp [selected]
    exact ⟨(t, j), hsel, by rw [show u (Sum.inl (t, j)) = v (t, j) from rfl, hv_sel _ hsel]⟩
  have hseedB : ∀ (t : Fin 5) (j : Fin k), t = 2 ∨ t = 1 → (Sum.inl (t, j), u (Sum.inl (t, j))) ∈ seed := by
    intro t j ht
    have hsel : selected (t, j) := by rcases ht with rfl | rfl <;> simp [selected]
    exact ⟨(t, j), hsel, by rw [show u (Sum.inl (t, j)) = v (t, j) from rfl, hv_sel _ hsel]⟩
  refine ⟨u, hsat, hv_sel, fun z hz => ?_⟩
  rcases hz with hfalse | ⟨⟨t, j⟩, rfl⟩
  · cases hfalse
  · have h6r2 : 6 * r + 2 ≤ 16 * (r + 1) := by omega
    apply upAdvance_iter_mono F h6r2 seed
    fin_cases t
    · -- t = 0
      exact upAdvance_iter_mono F (Nat.zero_le _) seed (hseedA 0 j (Or.inr rfl))
    · -- t = 1
      exact upAdvance_iter_mono F (Nat.zero_le _) seed (hseedB 1 j (Or.inr rfl))
    · -- t = 2
      exact upAdvance_iter_mono F (Nat.zero_le _) seed (hseedA 2 j (Or.inl rfl))
    · -- t = 3
      have hw := drive_validWire out.st hpos hwf F hgateF u hsat 0 seed hseedA (6 * r + 1)
        (out.fwdA j).wire (ValidWire_mono [] (hv1 j).2 (hv1 j).1 |> fun h => by simpa using h)
      rw [show 6 * r + 2 = (6 * r + 1) + 1 by omega, Function.iterate_succ_apply']
      exact drive_eq_fwd out.st.length hpos (out.fwdA j) (3, j) F (heqF_A j) u hsat _ hw
    · -- t = 4
      have hw := drive_validWire out.st hpos hwf F hgateF u hsat 1 seed hseedB (6 * r + 1)
        (out.fwdB j).wire (ValidWire_mono [] (hv2 j).2 (hv2 j).1 |> fun h => by simpa using h)
      rw [show 6 * r + 2 = (6 * r + 1) + 1 by omega, Function.iterate_succ_apply']
      exact drive_eq_fwd out.st.length hpos (out.fwdB j) (4, j) F (heqF_B j) u hsat _ hw

theorem drive_full_spec {k r : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) :
    let out := combinedCircuit hk r
    let hpos : 0 < out.st.length := combinedCircuit_pos hk r
    let F := buildCNF out hpos
    ∀ revA revB : Bool, ∀ pins : Fin 5 × Fin k → Bool,
      let selected : Fin 5 × Fin k → Prop := fun j =>
        j.1 = 2 ∨ j.1 = (if revA then 3 else 0) ∨ j.1 = (if revB then 4 else 1)
      let seed : Set (Literal (Sum (Fin 5 × Fin k) (Fin out.st.length))) :=
        {l | ∃ j : Fin 5 × Fin k, selected j ∧ l = (Sum.inl j, pins j)}
      let known := (upAdvance F)^[64 * (r + 1) * (Nat.clog 2 k + 1)] seed
      ∃ u : Sum (Fin 5 × Fin k) (Fin out.st.length) → Bool,
        Satisfies u (↑F : Set _) ∧
        (∀ j : Fin 5 × Fin k, selected j → u (Sum.inl j) = pins j) ∧
        ∀ z : Sum (Fin 5 × Fin k) (Fin out.st.length),
          (true = true ∨ ∃ j : Fin 5 × Fin k, z = Sum.inl j) → (z, u z) ∈ known := by
  intro out hpos F revA revB pins selected seed known
  have hspec := combinedCircuit_spec hk r
  have hwf : WF out.st := hspec.1
  have hdep : AllDepthLe (12 * (r + 1) * (Nat.clog 2 k + 1)) out.st := hspec.2.2.2.1
  have hv1 := hspec.2.2.2.2.1
  have hv2 := hspec.2.2.2.2.2.1
  have hv3 := hspec.2.2.2.2.2.2.1
  have hv4 := hspec.2.2.2.2.2.2.2.1
  let row0 : Fin k → Bool :=
    if revA then invFirstB hk r (fun q => pins (2, q)) (fun q => pins (3, q)) else fun q => pins (0, q)
  let row3 : Fin k → Bool :=
    if revA then fun q => pins (3, q) else firstB hk r (fun q => pins (2, q)) (fun q => pins (0, q))
  let col1 : Fin k → Bool :=
    if revB then invSecondB hk r (fun q => pins (2, q)) (fun q => pins (4, q)) else fun q => pins (1, q)
  let col4 : Fin k → Bool :=
    if revB then fun q => pins (4, q) else secondB hk r (fun q => pins (2, q)) (fun q => pins (1, q))
  let v : Fin 5 × Fin k → Bool := fun (t, i) =>
    if t = 2 then pins (2, i)
    else if t = 0 then row0 i
    else if t = 1 then col1 i
    else if t = 3 then row3 i
    else col4 i
  have hv_sel : ∀ j : Fin 5 × Fin k, selected j → v j = pins j := by
    intro ⟨t, i⟩ ht
    rcases ht with h2 | hA | hB
    · subst h2; rfl
    · cases revA
      · simp at hA; subst hA; simp [v, row0]
      · simp at hA; subst hA; simp [v, row3]
    · cases revB
      · simp at hB; subst hB; simp [v, col1]
      · simp at hB; subst hB; simp [v, col4]
  have hag : toNat (fun j => v (3, j)) = toNat (firstB hk r (fun j => v (2, j)) (fun j => v (0, j))) ∧
             toNat (fun j => v (4, j)) = toNat (secondB hk r (fun j => v (2, j)) (fun j => v (1, j))) := by
    constructor
    · congr 1
      change row3 = firstB hk r (fun j => pins (2, j)) row0
      cases revA
      · rfl
      · exact (firstB_invFirstB hk hk6 r _ _).symm
    · congr 1
      change col4 = secondB hk r (fun j => pins (2, j)) col1
      cases revB
      · rfl
      · exact (secondB_invSecondB hk hk6 r _ _).symm
  let aux : Fin out.st.length → Bool := fun i => evalW v out.st (Sum.inr i.val)
  let u : Sum (Fin 5 × Fin k) (Fin out.st.length) → Bool := Sum.elim v aux
  have hsat : Satisfies u (↑F : Set _) := project_sound_of_agrees hk hk6 v hag
  have hgateF : ∀ (i : Fin out.st.length) C, C ∈ gateClauses out.st hpos i → C ∈ F := by
    intro i C hC
    rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
    exact Or.inl (List.mem_flatMap.mpr ⟨i, List.mem_finRange i, hC⟩)
  have heqF : ∀ j : Fin k,
      (∀ C ∈ eqPairClauses out.st.length hpos (out.fwdA j) (3, j), C ∈ F) ∧
      (∀ C ∈ eqPairClauses out.st.length hpos (out.invA j) (0, j), C ∈ F) ∧
      (∀ C ∈ eqPairClauses out.st.length hpos (out.fwdB j) (4, j), C ∈ F) ∧
      (∀ C ∈ eqPairClauses out.st.length hpos (out.invB j) (1, j), C ∈ F) := by
    intro j
    have hmem : ∀ C, C ∈ eqPairClauses out.st.length hpos (out.fwdA j) (3, j) ++
        eqPairClauses out.st.length hpos (out.invA j) (0, j) ++
        eqPairClauses out.st.length hpos (out.fwdB j) (4, j) ++
        eqPairClauses out.st.length hpos (out.invB j) (1, j) → C ∈ F := by
      intro C hC
      rw [show F = (buildCNFList out hpos).toFinset from rfl, List.mem_toFinset, buildCNFList, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨j, List.mem_finRange j, hC⟩)
    exact ⟨fun C h => hmem C (by simp [h]), fun C h => hmem C (by simp [h]),
           fun C h => hmem C (by simp [h]), fun C h => hmem C (by simp [h])⟩
  set D1 := 12 * (r + 1) * (Nat.clog 2 k + 1)
  have hD_fwd : 6 * r + 1 ≤ D1 := by dsimp [D1]; nlinarith
  have hall_tracks : ∀ p : Fin 5 × Fin k, (Sum.inl p, u (Sum.inl p)) ∈ (upAdvance F)^[D1 + 1] seed := by
    intro ⟨t, j⟩
    have hsel_mem : ∀ p, selected p → (Sum.inl p, u (Sum.inl p)) ∈ seed := fun p hp =>
      ⟨p, hp, by rw [show u (Sum.inl p) = v p from rfl, hv_sel p hp]⟩
    fin_cases t
    · -- t = 0
      cases hrevA : revA
      · exact upAdvance_iter_mono F (Nat.zero_le _) seed (hsel_mem (0, j) (by simp [selected, hrevA]))
      · have hseed3 : ∀ t' j', t' = 2 ∨ t' = 3 → (Sum.inl (t', j'), u (Sum.inl (t', j'))) ∈ seed :=
          fun t' j' ht' => hsel_mem _ (by rcases ht' with rfl | rfl <;> simp [selected, hrevA])
        have hw := drive_validWire out.st hpos hwf F hgateF u hsat 3 seed hseed3 D1
          (out.invA j).wire (ValidWire_mono [] (hv3 j).2 (hv3 j).1 |> fun h => by simpa using h)
        rw [Function.iterate_succ_apply']
        exact drive_eq_fwd out.st.length hpos (out.invA j) (0, j) F (heqF j).2.1 u hsat _ hw
    · -- t = 1
      cases hrevB : revB
      · exact upAdvance_iter_mono F (Nat.zero_le _) seed (hsel_mem (1, j) (by simp [selected, hrevB]))
      · have hseed4 : ∀ t' j', t' = 2 ∨ t' = 4 → (Sum.inl (t', j'), u (Sum.inl (t', j'))) ∈ seed :=
          fun t' j' ht' => hsel_mem _ (by rcases ht' with rfl | rfl <;> simp [selected, hrevB])
        have hw := drive_validWire out.st hpos hwf F hgateF u hsat 4 seed hseed4 D1
          (out.invB j).wire (ValidWire_mono [] (hv4 j).2 (hv4 j).1 |> fun h => by simpa using h)
        rw [Function.iterate_succ_apply']
        exact drive_eq_fwd out.st.length hpos (out.invB j) (1, j) F (heqF j).2.2.2 u hsat _ hw
    · -- t = 2
      exact upAdvance_iter_mono F (Nat.zero_le _) seed (hsel_mem (2, j) (Or.inl rfl))
    · -- t = 3
      cases hrevA : revA
      · have hseed0 : ∀ t' j', t' = 2 ∨ t' = 0 → (Sum.inl (t', j'), u (Sum.inl (t', j'))) ∈ seed :=
          fun t' j' ht' => hsel_mem _ (by rcases ht' with rfl | rfl <;> simp [selected, hrevA])
        have hw := drive_validWire out.st hpos hwf F hgateF u hsat 0 seed hseed0 D1
          (out.fwdA j).wire (ValidWire_mono [] (le_trans (hv1 j).2 hD_fwd) (hv1 j).1 |> fun h => by simpa using h)
        rw [Function.iterate_succ_apply']
        exact drive_eq_fwd out.st.length hpos (out.fwdA j) (3, j) F (heqF j).1 u hsat _ hw
      · exact upAdvance_iter_mono F (Nat.zero_le _) seed (hsel_mem (3, j) (by simp [selected, hrevA]))
    · -- t = 4
      cases hrevB : revB
      · have hseed1 : ∀ t' j', t' = 2 ∨ t' = 1 → (Sum.inl (t', j'), u (Sum.inl (t', j'))) ∈ seed :=
          fun t' j' ht' => hsel_mem _ (by rcases ht' with rfl | rfl <;> simp [selected, hrevB])
        have hw := drive_validWire out.st hpos hwf F hgateF u hsat 1 seed hseed1 D1
          (out.fwdB j).wire (ValidWire_mono [] (le_trans (hv2 j).2 hD_fwd) (hv2 j).1 |> fun h => by simpa using h)
        rw [Function.iterate_succ_apply']
        exact drive_eq_fwd out.st.length hpos (out.fwdB j) (4, j) F (heqF j).2.2.1 u hsat _ hw
      · exact upAdvance_iter_mono F (Nat.zero_le _) seed (hsel_mem (4, j) (by simp [selected, hrevB]))
  have hall_gates : ∀ i : Fin out.st.length,
      (Sum.inr i, u (Sum.inr i)) ∈ (upAdvance F)^[D1 + (D1 + 1)] seed := by
    rw [Function.iterate_add_apply]
    exact drive_all_gates out.st hpos hwf F hgateF u hsat D1 hdep _ hall_tracks
  have htot : D1 + (D1 + 1) ≤ 64 * (r + 1) * (Nat.clog 2 k + 1) := by dsimp [D1]; nlinarith
  refine ⟨u, hsat, hv_sel, fun z _ => ?_⟩
  apply upAdvance_iter_mono F htot seed
  cases z with
  | inl p => exact upAdvance_iter_mono F (by omega : D1 + 1 ≤ D1 + (D1 + 1)) seed (hall_tracks p)
  | inr i => exact hall_gates i

/-! ## Section 4: Linear Sensitivity and Lower Bound for `r = 1` -/

def pulseS0 (k : ℕ) (j i : Fin k) : Bool :=
  let t := (i.val + k - j.val) % k
  if k % 6 = 1 then decide (t % 6 < 3)
  else decide (2 ≤ t % 6 ∧ t % 6 < 5)

private def pulseFun (k t : ℕ) : Bool :=
  if k % 6 = 1 then decide (t % 6 < 3)
  else decide (2 ≤ t % 6 ∧ t % 6 < 5)

private lemma pulseS0_eq_pulseFun {k : ℕ} (j i : Fin k) :
    pulseS0 k j i = pulseFun k ((i.val + k - j.val) % k) := rfl

private lemma shift_sub_mod {k a b c : ℕ} (hb : b < k) :
    ((a + c) % k + k - b) % k = ((a + k - b) % k + c) % k := by
  have h1 : (a + c) % k + k - b = (a + c) % k + (k - b) := by omega
  have h2 : a + k - b = a + (k - b) := by omega
  rw [h1, h2, Nat.add_mod ((a + c) % k), Nat.mod_mod, ← Nat.add_mod]
  rw [Nat.add_mod ((a + (k - b)) % k), Nat.mod_mod, ← Nat.add_mod]
  congr 1; omega

private lemma sub_mod_eq_zero_iff {k a b : ℕ} (ha : a < k) (hb : b < k) :
    (a + k - b) % k = 0 ↔ a = b := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
    rcases c with _ | _ | c
    · omega
    · omega
    · have : k * 2 ≤ k * (c + 1 + 1) := Nat.mul_le_mul_left k (by omega)
      omega
  · rintro rfl
    have : a + k - a = k := by omega
    rw [this, Nat.mod_self]

private lemma mixB_pulseS0_eq {k : ℕ} (hk5 : 5 ≤ k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (j i : Fin k) :
    mixB (by omega : 0 < k) 1 (pulseS0 k j) i =
      let t := (i.val + k - j.val) % k
      decide (t = 0 ∨ t % 2 = 1) := by
  have hk : 0 < k := by omega
  set t := (i.val + k - j.val) % k
  have ht : t < k := Nat.mod_lt _ hk
  have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hk1mod : (k - 1) % k = k - 1 := Nat.mod_eq_of_lt (by omega)
  have h_prev : ((i.val + k - 1 % k) % k + k - j.val) % k = (t + (k - 1)) % k := by
    rw [h1mod]
    have hi : i.val + k - 1 = i.val + (k - 1) := by omega
    rw [hi]
    exact shift_sub_mod j.isLt
  have h_next : ((i.val + k - (k - 1 % k) % k) % k + k - j.val) % k = (t + 1) % k := by
    rw [h1mod, hk1mod]
    have hi : i.val + k - (k - 1) = i.val + 1 := by omega
    rw [hi]
    exact shift_sub_mod j.isLt
  simp only [mixB, rotB, pulseS0_eq_pulseFun, h_prev, h_next]
  change xor (xor (pulseFun k t) (pulseFun k ((t + (k - 1)) % k))) (pulseFun k ((t + 1) % k)) =
    decide (t = 0 ∨ t % 2 = 1)
  rcases eq_or_ne t 0 with ht0 | ht0
  · have hkm1 : (t + (k - 1)) % k = k - 1 := by
      rw [ht0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    have h01 : (t + 1) % k = 1 := by
      rw [ht0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [hkm1, h01, ht0]
    rcases hk6 with h6 | h6
    · have hm : (k - 1) % 6 = 0 := by omega
      simp [pulseFun, h6, hm]
    · have hm : (k - 1) % 6 = 4 := by omega
      simp [pulseFun, h6, hm]
  · rcases eq_or_ne t (k - 1) with htk | htk
    · have hkm2 : (t + (k - 1)) % k = k - 2 := by
        have : t + (k - 1) = k + (k - 2) := by omega
        rw [this, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hkm0 : (t + 1) % k = 0 := by
        have : t + 1 = k := by omega
        rw [this, Nat.mod_self]
      rw [hkm2, hkm0, htk]
      have hne0 : k - 1 ≠ 0 := by omega
      rcases hk6 with h6 | h6
      · have hm1 : (k - 1) % 6 = 0 := by omega
        have hm2 : (k - 2) % 6 = 5 := by omega
        have hm2' : (k - 1) % 2 = 0 := by omega
        simp [pulseFun, h6, hm1, hm2, hm2', hne0]
      · have hm1 : (k - 1) % 6 = 4 := by omega
        have hm2 : (k - 2) % 6 = 3 := by omega
        have hm2' : (k - 1) % 2 = 0 := by omega
        simp [pulseFun, h6, hm1, hm2, hm2', hne0]
    · have hp : (t + (k - 1)) % k = t - 1 := by
        have : t + (k - 1) = (t - 1) + k := by omega
        rw [this, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      have hn : (t + 1) % k = t + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hp, hn]
      obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [hs]
      simp only [Nat.add_sub_cancel]
      have hs6 : s % 6 = 0 ∨ s % 6 = 1 ∨ s % 6 = 2 ∨ s % 6 = 3 ∨ s % 6 = 4 ∨ s % 6 = 5 := by omega
      rcases hk6 with h6 | h6 <;>
        (rcases hs6 with h | h | h | h | h | h <;>
          simp [pulseFun, h6, Nat.add_mod, h] <;> omega)

theorem stepB_mixB_pulseS0 {k : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) (j : Fin k) :
    stepB hk (mixB hk 1 (pulseS0 k j)) = fun i => decide (i = j) := by
  funext i
  rcases eq_or_ne k 1 with rfl | hk1
  · have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp [stepB, mixB, rotB, pulseS0]
  · have hk5 : 5 ≤ k := by omega
    have h_mix : ∀ u : Fin k,
        mixB hk 1 (pulseS0 k j) u =
          decide ((u.val + k - j.val) % k = 0 ∨ (u.val + k - j.val) % k % 2 = 1) :=
      fun u => mixB_pulseS0_eq hk5 hk6 j u
    simp only [stepB, h_mix]
    set t := (i.val + k - j.val) % k
    have ht : t < k := Nat.mod_lt _ hk
    have h1 : ((i.val + 1) % k + k - j.val) % k = (t + 1) % k := shift_sub_mod j.isLt
    have h2 : ((i.val + 2) % k + k - j.val) % k = (t + 2) % k := shift_sub_mod j.isLt
    rw [h1, h2]
    have hij : (t = 0) ↔ (i = j) := by
      rw [sub_mod_eq_zero_iff i.isLt j.isLt, Fin.ext_iff]
    have hk2 : k % 2 = 1 := by omega
    rcases eq_or_ne t 0 with ht0 | ht0
    · have h01 : (t + 1) % k = 1 := by rw [ht0]; exact Nat.mod_eq_of_lt (by omega)
      have h02 : (t + 2) % k = 2 := by rw [ht0]; exact Nat.mod_eq_of_lt (by omega)
      have hij' : i = j := hij.mp ht0
      rw [h01, h02, ht0]
      simp [hij']
    · have hij_false : i ≠ j := fun h => ht0 (hij.mpr h)
      simp only [hij_false, decide_false]
      rcases eq_or_ne t (k - 2) with htk2 | htk2
      · have h1' : (t + 1) % k = k - 1 := by
          have : t + 1 = k - 1 := by omega
          rw [this]; exact Nat.mod_eq_of_lt (by omega)
        have h2' : (t + 2) % k = 0 := by
          have : t + 2 = k := by omega
          rw [this, Nat.mod_self]
        rw [h1', h2', htk2]
        have hmod1 : (k - 2) % 2 = 1 := by omega
        have hmod2 : (k - 1) % 2 = 0 := by omega
        have hne1 : k - 2 ≠ 0 := by omega
        have hne2 : k - 1 ≠ 0 := by omega
        simp [hmod1, hmod2, hne1, hne2]
      · rcases eq_or_ne t (k - 1) with htk1 | htk1
        · have h1' : (t + 1) % k = 0 := by
            have : t + 1 = k := by omega
            rw [this, Nat.mod_self]
          have h2' : (t + 2) % k = 1 := by
            have : t + 2 = k + 1 := by omega
            rw [this, Nat.add_mod_left]; exact Nat.mod_eq_of_lt (by omega)
          rw [h1', h2', htk1]
          have hmod1 : (k - 1) % 2 = 0 := by omega
          have hne1 : k - 1 ≠ 0 := by omega
          simp [hmod1, hne1]
        · have h1' : (t + 1) % k = t + 1 := Nat.mod_eq_of_lt (by omega)
          have h2' : (t + 2) % k = t + 2 := Nat.mod_eq_of_lt (by omega)
          rw [h1', h2']
          have ht2 : t % 2 = 0 ∨ t % 2 = 1 := by omega
          rcases ht2 with h | h <;> simp [ht0, h, Nat.add_mod]

private lemma neg_mod_invol {k t : ℕ} (ht : t < k) :
    (k - (k - t) % k) % k = t := by
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  · rw [Nat.mod_eq_of_lt (by omega : k - t < k)]
    have h_sub : k - (k - t) = t := by omega
    rw [h_sub]
    exact Nat.mod_eq_of_lt ht

private lemma neg_mod_inj {k a b : ℕ} (ha : a < k) (hb : b < k)
    (h : (k - a) % k = (k - b) % k) : a = b := by
  have h1 := congrArg (fun x => (k - x) % k) h
  rwa [neg_mod_invol ha, neg_mod_invol hb] at h1

private lemma card_filter_mod6_lt3 (q : ℕ) :
    ((Finset.range (6 * q)).filter (fun t => decide (t % 6 < 3) = true)).card = 3 * q := by
  rw [Finset.card_filter]
  induction q with
  | zero => simp
  | succ q ih =>
    have h_eq : 6 * (q + 1) = 6 * q + 1 + 1 + 1 + 1 + 1 + 1 := by omega
    rw [h_eq]
    simp only [Finset.sum_range_succ, Nat.add_assoc] at ih ⊢
    rw [ih]
    have h0 : (6 * q) % 6 = 0 := by omega
    have h1 : (6 * q + 1) % 6 = 1 := by omega
    have h2 : (6 * q + 2) % 6 = 2 := by omega
    have h3 : (6 * q + 3) % 6 = 3 := by omega
    have h4 : (6 * q + 4) % 6 = 4 := by omega
    have h5 : (6 * q + 5) % 6 = 5 := by omega
    simp [h0, h1, h2, h3, h4, h5]
    omega

private lemma card_filter_mod6_2to5 (q : ℕ) :
    ((Finset.range (6 * q)).filter (fun t => decide (2 ≤ t % 6 ∧ t % 6 < 5) = true)).card = 3 * q := by
  rw [Finset.card_filter]
  induction q with
  | zero => simp
  | succ q ih =>
    have h_eq : 6 * (q + 1) = 6 * q + 1 + 1 + 1 + 1 + 1 + 1 := by omega
    rw [h_eq]
    simp only [Finset.sum_range_succ, Nat.add_assoc] at ih ⊢
    rw [ih]
    have h0 : (6 * q) % 6 = 0 := by omega
    have h1 : (6 * q + 1) % 6 = 1 := by omega
    have h2 : (6 * q + 2) % 6 = 2 := by omega
    have h3 : (6 * q + 3) % 6 = 3 := by omega
    have h4 : (6 * q + 4) % 6 = 4 := by omega
    have h5 : (6 * q + 5) % 6 = 5 := by omega
    simp [h0, h1, h2, h3, h4, h5]
    omega

theorem count_sensitive_bits (k : ℕ) (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5) :
    (Finset.univ.filter (fun j : Fin k => pulseS0 k j ⟨0, hk⟩ = true)).card +
    (Finset.univ.filter (fun j : Fin k =>
      xor (pulseS0 k j ⟨0, hk⟩) (decide ((j.val + 1) % k = 0)) = true)).card =
    k + (if k % 6 = 5 then 2 else 0) := by
  rcases eq_or_ne k 1 with rfl | hk1
  · decide +revert
  · have hk5 : 5 ≤ k := by omega
    have hbij1 : (Finset.univ.filter (fun j : Fin k => pulseS0 k j ⟨0, hk⟩ = true)).card =
        ((Finset.range k).filter (fun t => pulseFun k t = true)).card := by
      refine Finset.card_bij (fun j _ => (0 + k - j.val) % k) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        exact ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk), hj.2⟩
      · intro j₁ _ j₂ _ h
        ext
        simp only [Nat.zero_add] at h
        exact neg_mod_inj j₁.isLt j₂.isLt h
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_range] at ht
        refine ⟨⟨(k - t) % k, Nat.mod_lt _ hk⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [pulseS0_eq_pulseFun]
          dsimp only
          rw [Nat.zero_add, neg_mod_invol ht.1]
          exact ht.2
        · rw [Nat.zero_add, neg_mod_invol ht.1]
    have hbij2 : (Finset.univ.filter (fun j : Fin k =>
          xor (pulseS0 k j ⟨0, hk⟩) (decide ((j.val + 1) % k = 0)) = true)).card =
        ((Finset.range k).filter (fun t => xor (pulseFun k t) (decide (t = 1)) = true)).card := by
      have h_eq : ∀ j : Fin k, ((k - j.val) % k = 1) ↔ ((j.val + 1) % k = 0) := by
        intro j
        constructor
        · intro h
          have h1 := congrArg (fun x => (k - x) % k) h
          rw [neg_mod_invol j.isLt, Nat.mod_eq_of_lt (by omega)] at h1
          rw [h1]
          have : k - 1 + 1 = k := by omega
          rw [this, Nat.mod_self]
        · intro h
          have hsub : j.val = k - 1 := by
            obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero h
            have hjlt := j.isLt
            rcases c with _ | _ | c
            · omega
            · omega
            · have : k * 2 ≤ k * (c + 1 + 1) := Nat.mul_le_mul_left k (by omega)
              omega
          rw [hsub]
          have : k - (k - 1) = 1 := by omega
          rw [this]; exact Nat.mod_eq_of_lt (by omega)
      refine Finset.card_bij (fun j _ => (0 + k - j.val) % k) ?_ ?_ ?_
      · intro j hj
        rw [Finset.mem_filter] at hj ⊢
        refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ hk), ?_⟩
        have h' := hj.2
        rw [pulseS0_eq_pulseFun] at h'
        change xor (pulseFun k ((0 + k - j.val) % k)) (decide ((j.val + 1) % k = 0)) = true at h'
        simpa [h_eq j] using h'
      · intro j₁ _ j₂ _ h
        ext
        simp only [Nat.zero_add] at h
        exact neg_mod_inj j₁.isLt j₂.isLt h
      · intro t ht
        rw [Finset.mem_filter, Finset.mem_range] at ht
        refine ⟨⟨(k - t) % k, Nat.mod_lt _ hk⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have h_eq' := h_eq ⟨(k - t) % k, Nat.mod_lt _ hk⟩
          dsimp only at h_eq'
          rw [neg_mod_invol ht.1] at h_eq'
          rw [pulseS0_eq_pulseFun]
          dsimp only
          rw [Nat.zero_add, neg_mod_invol ht.1]
          simpa [h_eq'] using ht.2
        · rw [Nat.zero_add, neg_mod_invol ht.1]
    rw [hbij1, hbij2]
    set q := k / 6
    rcases hk6 with h6 | h6
    · have hk_eq : k = 6 * q + 1 := by omega
      have h_filt1 : ((Finset.range k).filter (fun t => pulseFun k t = true)).card = 3 * q + 1 := by
        rw [hk_eq, Finset.card_filter, Finset.sum_range_succ]
        have hm : (6 * q) % 6 = 0 := by omega
        have hmod1 : (6 * q + 1) % 6 = 1 := by omega
        have hp : pulseFun (6 * q + 1) (6 * q) = true := by simp [pulseFun, hmod1, hm]
        have h_ite : (if pulseFun (6 * q + 1) (6 * q) = true then 1 else 0) = 1 := by simp [hp]
        rw [h_ite]
        have heq : ∑ x ∈ Finset.range (6 * q), (if pulseFun (6 * q + 1) x = true then 1 else 0) =
            ((Finset.range (6 * q)).filter (fun t => decide (t % 6 < 3) = true)).card := by
          rw [Finset.card_filter]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [pulseFun, hmod1]
        rw [heq, card_filter_mod6_lt3]
      have h_filt2 : ((Finset.range k).filter (fun t => xor (pulseFun k t) (decide (t = 1)) = true)).card = 3 * q := by
        have h_erase : (Finset.range k).filter (fun t => xor (pulseFun k t) (decide (t = 1)) = true) =
            ((Finset.range k).filter (fun t => pulseFun k t = true)).erase 1 := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
          rcases eq_or_ne t 1 with rfl | ht1
          · simp [pulseFun, h6]
          · simp [ht1]
        rw [h_erase, Finset.card_erase_of_mem]
        · rw [h_filt1]; omega
        · simp [pulseFun, h6, (by omega : 1 < k)]
      rw [h_filt1, h_filt2]
      have hne5 : k % 6 ≠ 5 := by omega
      simp [hne5]; omega
    · have hk_eq : k = 6 * q + 5 := by omega
      have h_filt1 : ((Finset.range k).filter (fun t => pulseFun k t = true)).card = 3 * q + 3 := by
        have hk_eq' : k = 6 * q + 1 + 1 + 1 + 1 + 1 := by omega
        rw [hk_eq', Finset.card_filter]
        simp only [Finset.sum_range_succ, Nat.add_assoc]
        have hm0 : (6 * q) % 6 = 0 := by omega
        have hm1 : (6 * q + 1) % 6 = 1 := by omega
        have hm2 : (6 * q + 2) % 6 = 2 := by omega
        have hm3 : (6 * q + 3) % 6 = 3 := by omega
        have hm4 : (6 * q + 4) % 6 = 4 := by omega
        have h_base : ∑ x ∈ Finset.range (6 * q),
            (if pulseFun (6 * q + (1 + (1 + (1 + (1 + 1))))) x = true then 1 else 0) = 3 * q := by
          have heq : ∑ x ∈ Finset.range (6 * q),
              (if pulseFun (6 * q + (1 + (1 + (1 + (1 + 1))))) x = true then 1 else 0) =
              ((Finset.range (6 * q)).filter (fun t => decide (2 ≤ t % 6 ∧ t % 6 < 5) = true)).card := by
            rw [Finset.card_filter]
            refine Finset.sum_congr rfl fun x _ => ?_
            simp [pulseFun]
          rw [heq, card_filter_mod6_2to5]
        rw [h_base]
        simp [pulseFun, hm0, hm1, hm2, hm3, hm4]
      have h_filt2 : ((Finset.range k).filter (fun t => xor (pulseFun k t) (decide (t = 1)) = true)).card = 3 * q + 4 := by
        have h_ins : (Finset.range k).filter (fun t => xor (pulseFun k t) (decide (t = 1)) = true) =
            insert 1 ((Finset.range k).filter (fun t => pulseFun k t = true)) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_range]
          rcases eq_or_ne t 1 with rfl | ht1
          · simp [pulseFun, h6, (by omega : 1 < k)]
          · simp [ht1]
        rw [h_ins, Finset.card_insert_of_notMem]
        · rw [h_filt1]
        · simp [pulseFun, h6]
      rw [h_filt1, h_filt2]
      simp [h6]; omega

theorem advance_support {V : Type} [DecidableEq V] {m : ℕ}
    (F : Finset (Clause (Sum V (Fin m)))) (h3 : ∀ C ∈ F, C.card ≤ 3)
    (selected : V → Bool) (d : ℕ) (pins : V → Bool) (l : Literal (Sum V (Fin m))) :
    let seed := {l' | ∃ j : V, selected j ∧ l' = (Sum.inl j, pins j)}
    let advance := fun S : Set (Literal (Sum V (Fin m))) =>
      S ∪ {l' | ∃ C ∈ F, l' ∈ C ∧ ∀ other ∈ C, other ≠ l' → negLit other ∈ S}
    l ∈ (advance^[d]) seed →
    ∃ T : Finset V, T.card ≤ 2 ^ d ∧ (∀ j ∈ T, selected j) ∧
      ∀ pins' : V → Bool, (∀ j ∈ T, pins' j = pins j) →
        l ∈ (advance^[d]) {l' | ∃ j : V, selected j ∧ l' = (Sum.inl j, pins' j)} := by
  intro seed advance hl
  induction d generalizing l with
  | zero =>
    simp only [Function.iterate_zero, id_eq] at hl ⊢
    rcases hl with ⟨j, hj, rfl⟩
    refine ⟨{j}, by simp, by simp [hj], fun pins' hp => ?_⟩
    exact ⟨j, hj, by rw [hp j (Finset.mem_singleton_self j)]⟩
  | succ d ih =>
    rw [Function.iterate_succ_apply'] at hl
    rcases hl with hl_prev | ⟨C, hCF, hlC, h_other⟩
    · rcases ih l hl_prev with ⟨T, hT_card, hT_sel, hT_pins⟩
      refine ⟨T, hT_card.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ d)), hT_sel, ?_⟩
      intro pins' hp
      rw [Function.iterate_succ_apply']
      exact Or.inl (hT_pins pins' hp)
    · have h_sub : ∀ other ∈ C.erase l,
          ∃ T_o : Finset V, T_o.card ≤ 2 ^ d ∧ (∀ j ∈ T_o, selected j) ∧
            ∀ pins' : V → Bool, (∀ j ∈ T_o, pins' j = pins j) →
              negLit other ∈ (advance^[d]) {l' | ∃ j : V, selected j ∧ l' = (Sum.inl j, pins' j)} := by
        intro other h_mem
        rw [Finset.mem_erase] at h_mem
        exact ih (negLit other) (h_other other h_mem.2 h_mem.1)
      choose T_map hT_map using h_sub
      refine ⟨(C.erase l).attach.biUnion (fun o => T_map o.1 o.2), ?_, ?_, ?_⟩
      · have h_card_erase : (C.erase l).card ≤ 2 := by
          have := Finset.card_erase_add_one hlC
          have := h3 C hCF
          omega
        calc ((C.erase l).attach.biUnion (fun o => T_map o.1 o.2)).card
            ≤ ∑ o ∈ (C.erase l).attach, (T_map o.1 o.2).card := Finset.card_biUnion_le
          _ ≤ ∑ _o ∈ (C.erase l).attach, 2 ^ d := Finset.sum_le_sum (fun o _ => (hT_map o.1 o.2).1)
          _ = (C.erase l).attach.card * 2 ^ d := by simp
          _ = (C.erase l).card * 2 ^ d := by rw [Finset.card_attach]
          _ ≤ 2 * 2 ^ d := Nat.mul_le_mul_right _ h_card_erase
          _ = 2 ^ (d + 1) := by ring
      · intro j hj
        rw [Finset.mem_biUnion] at hj
        rcases hj with ⟨o, _, hjo⟩
        exact (hT_map o.1 o.2).2.1 j hjo
      · intro pins' hp
        rw [Function.iterate_succ_apply']
        right
        refine ⟨C, hCF, hlC, fun other hoC hne => ?_⟩
        have ho_mem : other ∈ C.erase l := Finset.mem_erase.mpr ⟨hne, hoC⟩
        refine (hT_map other ho_mem).2.2 pins' (fun j hj => hp j ?_)
        rw [Finset.mem_biUnion]
        exact ⟨⟨other, ho_mem⟩, Finset.mem_attach _ _, hj⟩

theorem advance_sound {V : Type} {m : ℕ}
    (F : Finset (Clause (Sum V (Fin m)))) (u : Sum V (Fin m) → Bool)
    (hu : Satisfies u (↑F : Set _)) (S0 : Set (Literal (Sum V (Fin m))))
    (hS0 : ∀ l ∈ S0, u l.1 = l.2) (d : ℕ) :
    ∀ l ∈ ((fun S => S ∪ {l' | ∃ C ∈ F, l' ∈ C ∧ ∀ other ∈ C, other ≠ l' → negLit other ∈ S})^[d]) S0,
      u l.1 = l.2 := by
  induction d with
  | zero => simpa using hS0
  | succ d ih =>
    intro l hl
    rw [Function.iterate_succ_apply'] at hl
    rcases hl with hl_prev | ⟨C, hCF, hlC, h_other⟩
    · exact ih l hl_prev
    · obtain ⟨l₀, hl₀C, hl₀u⟩ := hu C hCF
      by_cases h_eq : l₀ = l
      · subst h_eq; exact hl₀u
      · have hneg := ih (negLit l₀) (h_other l₀ hl₀C h_eq)
        simp [negLit] at hneg
        rw [hl₀u] at hneg
        cases l₀.2 <;> simp at hneg

theorem lower_bound_r1 {k m d : ℕ} (hk : 0 < k) (hk6 : k % 6 = 1 ∨ k % 6 = 5)
    (F : Finset (Clause (Sum (Fin 5 × Fin k) (Fin m))))
    (hproj : (∀ C ∈ F, C.card ≤ 3) ∧
      ∀ v : Fin 5 × Fin k → Bool,
        (toNat (fun j => v (3, j)) = toNat (firstB hk 1 (fun j => v (2, j)) (fun j => v (0, j))) ∧
         toNat (fun j => v (4, j)) = toNat (secondB hk 1 (fun j => v (2, j)) (fun j => v (1, j)))) ↔
        ∃ aux : Fin m → Bool, Satisfies (Sum.elim v aux) (↑F : Set _))
    (hdrv : ∀ pins : Fin 5 × Fin k → Bool,
      let selected : Fin 5 × Fin k → Prop := fun j => j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 1
      let seed : Set (Literal (Sum (Fin 5 × Fin k) (Fin m))) :=
        {l | ∃ j : Fin 5 × Fin k, selected j ∧ l = (Sum.inl j, pins j)}
      let known := (upAdvance F)^[d] seed
      ∃ u : Sum (Fin 5 × Fin k) (Fin m) → Bool,
        Satisfies u (↑F : Set _) ∧
        (∀ j : Fin 5 × Fin k, selected j → u (Sum.inl j) = pins j) ∧
        ∀ z : Sum (Fin 5 × Fin k) (Fin m), (false = true ∨ ∃ j : Fin 5 × Fin k, z = Sum.inl j) → (z, u z) ∈ known) :
    k + (if k % 6 = 5 then 2 else 0) ≤ 2 ^ d := by
  have agree_row_of_sat : ∀ u : Sum (Fin 5 × Fin k) (Fin m) → Bool,
      Satisfies u (↑F : Set _) →
      (fun i => u (Sum.inl (0, i))) =
        invFirstB hk 1 (fun i => u (Sum.inl (2, i))) (fun i => u (Sum.inl (3, i))) := by
    intro u hu
    let v : Fin 5 × Fin k → Bool := fun j => u (Sum.inl j)
    let aux : Fin m → Bool := fun i => u (Sum.inr i)
    have hu_eq : Sum.elim v aux = u := by ext x; cases x <;> rfl
    have hsat : Satisfies (Sum.elim v aux) (↑F : Set _) := by rw [hu_eq]; exact hu
    have hag := (hproj.2 v).mpr ⟨aux, hsat⟩
    have h3 : (fun j => v (3, j)) = firstB hk 1 (fun j => v (2, j)) (fun j => v (0, j)) :=
      toNat_inj hag.1
    calc (fun i => u (Sum.inl (0, i)))
        = invFirstB hk 1 (fun j => v (2, j)) (firstB hk 1 (fun j => v (2, j)) (fun j => v (0, j))) :=
            (invFirstB_firstB hk hk6 1 _ _).symm
      _ = invFirstB hk 1 (fun i => u (Sum.inl (2, i))) (fun i => u (Sum.inl (3, i))) := by
            rw [← h3]
  let selB : Fin 5 × Fin k → Bool := fun j => decide (j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 1)
  have hsel_iff : ∀ j : Fin 5 × Fin k, (j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 1) ↔ selB j = true := by
    intro j; simp [selB]
  let pins0 : Fin 5 × Fin k → Bool := fun (t, i) => if t = 3 then constBit k 1 i else false
  have hu0 := hdrv pins0
  rcases hu0 with ⟨u0, hu0_sat, hu0_sel, hu0_known⟩
  have h_f00 : firstB hk 1 (fun _ => false) (fun _ => false) = fun i => constBit k 1 i := by
    ext i
    dsimp [firstB, stepB, mixB, rotB]
    simp
  have hu0_z0 : u0 (Sum.inl (0, ⟨0, hk⟩)) = false := by
    have hinv := agree_row_of_sat u0 hu0_sat
    have h2 : (fun i => u0 (Sum.inl (2, i))) = fun _ => false := funext fun i => by
      simpa [pins0] using hu0_sel (2, i) (Or.inl rfl)
    have h3 : (fun i => u0 (Sum.inl (3, i))) = fun i => constBit k 1 i := funext fun i => by
      simpa [pins0] using hu0_sel (3, i) (Or.inr (Or.inl rfl))
    have h0 := congrFun hinv ⟨0, hk⟩
    rw [h2, h3, ← h_f00, invFirstB_firstB hk hk6 1] at h0
    exact h0
  have hl0 : (Sum.inl (0, ⟨0, hk⟩), false) ∈
      ((fun S => S ∪ {l' | ∃ C ∈ F, l' ∈ C ∧ ∀ other ∈ C, other ≠ l' → negLit other ∈ S})^[d])
        {l' | ∃ j : Fin 5 × Fin k, selB j = true ∧ l' = (Sum.inl j, pins0 j)} := by
    have hk0 := hu0_known (Sum.inl (0, ⟨0, hk⟩)) (Or.inr ⟨(0, ⟨0, hk⟩), rfl⟩)
    rw [hu0_z0] at hk0
    have hset : ({l : Literal (Sum (Fin 5 × Fin k) (Fin m)) |
          ∃ j : Fin 5 × Fin k, (j.1 = 2 ∨ j.1 = 3 ∨ j.1 = 1) ∧ l = (Sum.inl j, pins0 j)}) =
        {l' | ∃ j : Fin 5 × Fin k, selB j = true ∧ l' = (Sum.inl j, pins0 j)} := by
      ext l; simp only [Set.mem_setOf_eq, hsel_iff]
    rw [hset] at hk0
    exact hk0
  obtain ⟨T, hT_card, hT_sel, hT_pins⟩ :=
    advance_support F hproj.1 selB d pins0 (Sum.inl (0, ⟨0, hk⟩), false) hl0
  have h_track3 : ∀ j : Fin k, pulseS0 k j ⟨0, hk⟩ = true → (3, j) ∈ T := by
    intro j hj
    by_contra hjT
    let pins1 : Fin 5 × Fin k → Bool := fun p => if p = (3, j) then !(constBit k 1 j) else pins0 p
    have h_eqT : ∀ p ∈ T, pins1 p = pins0 p := by
      intro p hp
      have hne : p ≠ (3, j) := fun h => hjT (by rw [← h]; exact hp)
      simp [pins1, hne]
    have hl1 := hT_pins pins1 h_eqT
    rcases hdrv pins1 with ⟨u1, hu1_sat, hu1_sel, _⟩
    have hS0 : ∀ l ∈ {l' : Literal (Sum (Fin 5 × Fin k) (Fin m)) |
        ∃ p : Fin 5 × Fin k, selB p = true ∧ l' = (Sum.inl p, pins1 p)}, u1 l.1 = l.2 := by
      rintro l ⟨p, hp, rfl⟩
      exact hu1_sel p ((hsel_iff p).mpr hp)
    have hu1_z0 : u1 (Sum.inl (0, ⟨0, hk⟩)) = false :=
      advance_sound F u1 hu1_sat _ hS0 d _ hl1
    have h2 : (fun i => u1 (Sum.inl (2, i))) = fun _ => false := funext fun i => by
      have hp := hu1_sel (2, i) (Or.inl rfl)
      have hne : (2, i) ≠ (3, j) := by simp
      simpa [pins1, pins0, hne] using hp
    have h3 : (fun i => u1 (Sum.inl (3, i))) =
        firstB hk 1 (fun _ => false) (pulseS0 k j) := by
      ext i
      have hp := hu1_sel (3, i) (Or.inr (Or.inl rfl))
      rw [hp]
      dsimp [firstB]
      have hinit_p : (fun x => xor (rotB hk 1 (fun _ => false) x) (pulseS0 k j x)) = pulseS0 k j := by
        ext x; dsimp [rotB]; simp
      rw [hinit_p, stepB_mixB_pulseS0 hk hk6 j]
      have hrot0 : rotB hk 0 (fun _ => false) i = false := rfl
      rw [hrot0]
      dsimp [pins1, pins0]
      by_cases hij : i = j
      · subst hij; simp [Bool.true_xor]
      · have hne : ((3 : Fin 5), i) ≠ (3, j) := by intro h; apply hij; exact congrArg Prod.snd h
        simp [hij, hne]
    have h0 := congrFun (agree_row_of_sat u1 hu1_sat) ⟨0, hk⟩
    rw [h2, h3, invFirstB_firstB hk hk6 1] at h0
    rw [hj] at h0
    rw [hu1_z0] at h0
    cases h0
  have h_track2 : ∀ j : Fin k,
      xor (pulseS0 k j ⟨0, hk⟩) (decide ((j.val + 1) % k = 0)) = true → (2, j) ∈ T := by
    intro j hj
    by_contra hjT
    let pins2 : Fin 5 × Fin k → Bool := fun p => if p = (2, j) then true else pins0 p
    have h_eqT : ∀ p ∈ T, pins2 p = pins0 p := by
      intro p hp
      have hne : p ≠ (2, j) := fun h => hjT (by rw [← h]; exact hp)
      simp [pins2, hne]
    have hl2 := hT_pins pins2 h_eqT
    rcases hdrv pins2 with ⟨u2, hu2_sat, hu2_sel, _⟩
    have hS0 : ∀ l ∈ {l' : Literal (Sum (Fin 5 × Fin k) (Fin m)) |
        ∃ p : Fin 5 × Fin k, selB p = true ∧ l' = (Sum.inl p, pins2 p)}, u2 l.1 = l.2 := by
      rintro l ⟨p, hp, rfl⟩
      exact hu2_sel p ((hsel_iff p).mpr hp)
    have hu2_z0 : u2 (Sum.inl (0, ⟨0, hk⟩)) = false :=
      advance_sound F u2 hu2_sat _ hS0 d _ hl2
    let rowKey2 : Fin k → Bool := fun i => decide (i = j)
    let rowName2 : Fin k → Bool := fun i => xor (pulseS0 k j i) (rotB hk 1 rowKey2 i)
    have h2 : (fun i => u2 (Sum.inl (2, i))) = rowKey2 := funext fun i => by
      have hp := hu2_sel (2, i) (Or.inl rfl)
      rw [hp]
      dsimp [pins2, pins0, rowKey2]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : ((2 : Fin 5), i) ≠ (2, j) := by intro h; apply hij; exact congrArg Prod.snd h
        simp [hij, hne]
    have h3 : (fun i => u2 (Sum.inl (3, i))) = firstB hk 1 rowKey2 rowName2 := by
      ext i
      have hp := hu2_sel (3, i) (Or.inr (Or.inl rfl))
      rw [hp]
      dsimp [pins2, pins0]
      dsimp [firstB]
      have hinit_p : (fun x => xor (rotB hk 1 rowKey2 x) (rowName2 x)) = pulseS0 k j := by
        ext x; dsimp [rowName2]
        cases rotB hk 1 rowKey2 x <;> cases pulseS0 k j x <;> rfl
      rw [hinit_p, stepB_mixB_pulseS0 hk hk6 j]
      have hrot0 : rotB hk 0 rowKey2 i = rowKey2 i := by
        dsimp [rotB]
        congr 1; apply Fin.ext; dsimp
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      rw [hrot0]
      dsimp [rowKey2]
      cases decide (i = j) <;> simp
    have h0 := congrFun (agree_row_of_sat u2 hu2_sat) ⟨0, hk⟩
    rw [h2, h3, invFirstB_firstB hk hk6 1] at h0
    have h_rot_0 : rotB hk 1 rowKey2 ⟨0, hk⟩ = decide ((j.val + 1) % k = 0) := by
      dsimp [rotB, rowKey2]
      simp only [Nat.zero_add, decide_eq_decide, Fin.ext_iff]
      rcases eq_or_ne k 1 with rfl | hk1
      · have hj0 := j.isLt
        omega
      · have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1m, Nat.mod_eq_of_lt (by omega : k - 1 < k)]
        constructor
        · intro hj'
          rw [← hj']
          have : k - 1 + 1 = k := by omega
          rw [this, Nat.mod_self]
        · intro hdiv
          obtain ⟨c, hc⟩ := Nat.dvd_of_mod_eq_zero hdiv
          have hjlt := j.isLt
          rcases c with _ | _ | c
          · omega
          · omega
          · have : k * 2 ≤ k * (c + 1 + 1) := Nat.mul_le_mul_left k (by omega)
            omega
    have hname0 : rowName2 ⟨0, hk⟩ = xor (pulseS0 k j ⟨0, hk⟩) (decide ((j.val + 1) % k = 0)) := by
      dsimp [rowName2]; rw [h_rot_0]
    rw [hname0, hj, hu2_z0] at h0
    cases h0
  let F3 := Finset.univ.filter (fun j : Fin k => pulseS0 k j ⟨0, hk⟩ = true)
  let F2 := Finset.univ.filter (fun j : Fin k =>
    xor (pulseS0 k j ⟨0, hk⟩) (decide ((j.val + 1) % k = 0)) = true)
  let S3 := F3.image (fun j => ((3 : Fin 5), j))
  let S2 := F2.image (fun j => ((2 : Fin 5), j))
  have hS3_sub : S3 ⊆ T := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨j, hj, rfl⟩
    rw [Finset.mem_filter] at hj
    exact h_track3 j hj.2
  have hS2_sub : S2 ⊆ T := by
    intro p hp
    rw [Finset.mem_image] at hp
    rcases hp with ⟨j, hj, rfl⟩
    rw [Finset.mem_filter] at hj
    exact h_track2 j hj.2
  have hdisj : Disjoint S3 S2 := by
    rw [Finset.disjoint_left]
    intro p hp3 hp2
    rw [Finset.mem_image] at hp3 hp2
    rcases hp3 with ⟨j3, _, rfl⟩
    rcases hp2 with ⟨j2, _, h_eq⟩
    cases h_eq
  have hS3_card : S3.card = F3.card :=
    Finset.card_image_of_injective F3 (fun _ _ h => congrArg Prod.snd h)
  have hS2_card : S2.card = F2.card :=
    Finset.card_image_of_injective F2 (fun _ _ h => congrArg Prod.snd h)
  have hsum : F3.card + F2.card = k + (if k % 6 = 5 then 2 else 0) :=
    count_sensitive_bits k hk hk6
  calc k + (if k % 6 = 5 then 2 else 0)
      = S3.card + S2.card := by rw [hS3_card, hS2_card, hsum]
    _ = (S3 ∪ S2).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ T.card := Finset.card_le_card (Finset.union_subset hS3_sub hS2_sub)
    _ ≤ 2 ^ d := hT_card

end PEqualNP.Outside.L_pcx_289_aux

theorem PEqualNP.Outside.L_pcx_289 :
    ∀ (k r : ℕ), (k % 6 = 1 ∨ k % 6 = 5) →
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
      let project := fun (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m)))) =>
        (∀ C ∈ F, C.card ≤ 3) ∧ ∀ v : V → Bool, agrees v ↔
          ∃ aux : Fin m → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim v aux) (↑F : Set _)
      let drive := fun (m : ℕ) (F : Finset (PEqualNP.ProofComplexity.Clause (Sum V (Fin m))))
          (d : ℕ) (rowRev colRev allWires : Bool) => ∀ pins : V → Bool,
        let selected := fun j : V => j.1 = 2 ∨ j.1 = (if rowRev then 3 else 0) ∨
          j.1 = (if colRev then 4 else 1)
        let seed : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) :=
          {l | ∃ j : V, selected j ∧ l = (Sum.inl j, pins j)}
        let advance := fun S : Set (PEqualNP.ProofComplexity.Literal (Sum V (Fin m))) =>
          S ∪ {l | ∃ C ∈ F, l ∈ C ∧ ∀ other ∈ C, other ≠ l →
            PEqualNP.Search.negLit other ∈ S}
        let known := (advance^[d]) seed
        ∃ u : Sum V (Fin m) → Bool,
          PEqualNP.ProofComplexity.Satisfies u (↑F : Set _) ∧
          (∀ j : V, selected j → u (Sum.inl j) = pins j) ∧
          ∀ z : Sum V (Fin m), (allWires = true ∨ ∃ j : V, z = Sum.inl j) → (z,u z) ∈ known
      (∃ m F, project m F ∧ m + (∑ C ∈ F, C.card) ≤ 4096*(k+1)*(r+1) ∧
        drive m F (16*(r+1)) false false false ∧
        ∀ revA revB : Bool,
          drive m F (64*(r+1)*(Nat.clog 2 k+1)) revA revB true) ∧
      (r = 1 → ∀ m F d, project m F → drive m F d true false false →
        k + (if k % 6 = 5 then 2 else 0) ≤ 2^d) := by
  intro k r hk6
  have hk : 0 < k := by omega
  have h_agrees_iff : ∀ (r' : ℕ) (v : Fin 5 × Fin k → Bool),
      ((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (3, j))) =
        (List.range r').foldl (fun rowState rowIndex =>
          ((List.range k).foldl (fun acc i =>
            acc ||| ((xor ((rowState ^^^ ((rowState <<< (1 % k)) ||| (rowState >>> (k - 1 % k))) % 2 ^ k ^^^
                ((rowState <<< ((k - 1) % k)) ||| (rowState >>> (k - (k - 1) % k))) % 2 ^ k).testBit i)
              (!((rowState ^^^ ((rowState <<< (1 % k)) ||| (rowState >>> (k - 1 % k))) % 2 ^ k ^^^
                ((rowState <<< ((k - 1) % k)) ||| (rowState >>> (k - (k - 1) % k))) % 2 ^ k).testBit ((i + 1) % k)) &&
                (rowState ^^^ ((rowState <<< (1 % k)) ||| (rowState >>> (k - 1 % k))) % 2 ^ k ^^^
                ((rowState <<< ((k - 1) % k)) ||| (rowState >>> (k - (k - 1) % k))) % 2 ^ k).testBit ((i + 2) % k))).toNat <<< i)) 0) ^^^
            (((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) <<< ((2 * rowIndex) % k)) |||
              ((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) >>> (k - (2 * rowIndex) % k))) % 2 ^ k ^^^
            3 ^ (k + (rowIndex + 1)) % 2 ^ k)
          ((((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) <<< (1 % k)) |||
            ((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) >>> (k - 1 % k))) % 2 ^ k ^^^
            (PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (0, j)))) ∧
       (PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (4, j))) =
        (List.range r').foldl (fun colState colIndex =>
          ((List.range k).foldl (fun acc i =>
            acc ||| ((xor ((colState ^^^ ((colState <<< (2 % k)) ||| (colState >>> (k - 2 % k))) % 2 ^ k ^^^
                ((colState <<< ((k - 2) % k)) ||| (colState >>> (k - (k - 2) % k))) % 2 ^ k).testBit i)
              (!((colState ^^^ ((colState <<< (2 % k)) ||| (colState >>> (k - 2 % k))) % 2 ^ k ^^^
                ((colState <<< ((k - 2) % k)) ||| (colState >>> (k - (k - 2) % k))) % 2 ^ k).testBit ((i + 1) % k)) &&
                (colState ^^^ ((colState <<< (2 % k)) ||| (colState >>> (k - 2 % k))) % 2 ^ k ^^^
                ((colState <<< ((k - 2) % k)) ||| (colState >>> (k - (k - 2) % k))) % 2 ^ k).testBit ((i + 2) % k))).toNat <<< i)) 0) ^^^
            (((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) <<< ((3 * (colIndex + 1) + 1) % k)) |||
              ((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) >>> (k - (3 * (colIndex + 1) + 1) % k))) % 2 ^ k ^^^
            3 ^ (k + (r' + (colIndex + 1))) % 2 ^ k)
          ((((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) <<< (3 % k)) |||
            ((PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (2, j))) >>> (k - 3 % k))) % 2 ^ k ^^^
            (PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (1, j))))) ↔
      (PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (3, j)) =
          PEqualNP.Outside.L_pcx_289_aux.toNat
            (PEqualNP.Outside.L_pcx_289_aux.firstB hk r' (fun j => v (2, j)) (fun j => v (0, j))) ∧
       PEqualNP.Outside.L_pcx_289_aux.toNat (fun j => v (4, j)) =
          PEqualNP.Outside.L_pcx_289_aux.toNat
            (PEqualNP.Outside.L_pcx_289_aux.secondB hk r' (fun j => v (2, j)) (fun j => v (1, j)))) := by
    intro r' v
    rw [PEqualNP.Outside.L_pcx_289_aux.firstB_toNat hk r',
      PEqualNP.Outside.L_pcx_289_aux.secondB_toNat hk r']
  refine ⟨?_, ?_⟩
  · let out := PEqualNP.Outside.L_pcx_289_aux.combinedCircuit hk r
    let hpos := PEqualNP.Outside.L_pcx_289_aux.combinedCircuit_pos hk r
    let F := PEqualNP.Outside.L_pcx_289_aux.buildCNF out hpos
    refine ⟨out.st.length, F, ?_, ?_, ?_, ?_⟩
    · refine ⟨(PEqualNP.Outside.L_pcx_289_aux.cnf_bounds hk).1, fun v => ?_⟩
      dsimp only
      exact Iff.trans (h_agrees_iff r v) (PEqualNP.Outside.L_pcx_289_aux.project_spec hk hk6 v)
    · exact (PEqualNP.Outside.L_pcx_289_aux.cnf_bounds hk).2
    · exact PEqualNP.Outside.L_pcx_289_aux.drive_fwd_spec hk hk6
    · exact PEqualNP.Outside.L_pcx_289_aux.drive_full_spec hk hk6
  · rintro rfl m F d hproj hdrv
    refine PEqualNP.Outside.L_pcx_289_aux.lower_bound_r1 hk hk6 F ?_ hdrv
    refine ⟨hproj.1, fun v => ?_⟩
    exact Iff.trans (h_agrees_iff 1 v).symm (hproj.2 v)
