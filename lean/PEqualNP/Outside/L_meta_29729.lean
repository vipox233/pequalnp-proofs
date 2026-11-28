import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29729

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack)

def rotK (k offset x : Nat) : Nat :=
  ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2 ^ k

def mixK (k gap value : Nat) : Nat :=
  value ^^^ rotK k gap value ^^^ rotK k (k - gap) value

def chiK (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))).toNat <<< site)) 0

def stepK (k r : Nat) (constants : Nat → Fin (2 ^ k)) (col : Bool) (raw prev t : Nat) : Nat :=
  chiK k (mixK k (if col then 2 else 1) prev) ^^^
    rotK k (if col then 3 * t + 1 else 2 * (t - 1)) raw ^^^
    (constants (if col then r + t else t)).val

def stateN (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) (n : Nat) : Nat :=
  (List.range n).foldl (fun v tick => stepK k r c side key v (tick + 1))
    (rotK k (if side then 3 else 1) key ^^^ name)

def cutK (wordAt offset len : Nat) : Nat := (wordAt >>> offset) % 2 ^ len

def hOf (k : Nat) : Nat := (k + 1) / 2
def zOf (k : Nat) : Nat := k - hOf k
def uOf (r : Nat) : Nat := 5 * r - 3
def extraOf (k r : Nat) : Nat := min (r - 2) (zOf k - 6 * r)
def swOf (k r : Nat) : Nat := min k (uOf r) + extraOf k r
def rowLenOf (k r : Nat) : Nat := min (hOf k) (k - uOf r)
def colLenOf (k r : Nat) : Nat := min (r + 3) (zOf k - uOf r)
def unusedOf (k r : Nat) : Nat := zOf k - (7 * r - 2)
def startOf (k r : Nat) : Nat := k - (2 * r - 2)
def seedOf (k r w : Nat) : Nat := rotK k (k - startOf k r % k) w % 2 ^ swOf k r

lemma dims_sum (k r : Nat) (hr : 4 ≤ r) :
    swOf k r + rowLenOf k r + colLenOf k r + unusedOf k r = k := by
  dsimp only [swOf, rowLenOf, colLenOf, unusedOf, extraOf, uOf, zOf, hOf]
  omega

lemma rotK_lt {k : Nat} (offset x : Nat) : rotK k offset x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rotK_testBit {k : Nat} (hk : 0 < k) {x : Nat} (hx : x < 2 ^ k)
    (offset i : Nat) (hi : i < k) :
    (rotK k offset x).testBit i = x.testBit ((i + k - offset % k) % k) := by
  dsimp only [rotK]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
    Nat.testBit_lor, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hs : offset % k < k := Nat.mod_lt offset hk
  by_cases hle : offset % k ≤ i
  · have hhi : x.testBit (k - offset % k + i) = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
    have hidx : (i + k - offset % k) % k = i - offset % k := by
      have h1 : i + k - offset % k = (i - offset % k) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_true hle, Bool.true_and, hhi, Bool.or_false, hidx]
  · have hidx : (i + k - offset % k) % k = k - offset % k + i := by
      have h1 : i + k - offset % k = k - offset % k + i := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [decide_eq_false hle, Bool.false_and, Bool.false_or, hidx]

lemma rotK_inj {k : Nat} (hk : 0 < k) (offset : Nat) {x y : Nat}
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) (h : rotK k offset x = rotK k offset y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < k
  · let i := (b + offset % k) % k
    have hi : i < k := Nat.mod_lt _ hk
    have htb : (rotK k offset x).testBit i = (rotK k offset y).testBit i := by rw [h]
    rw [rotK_testBit hk hx offset i hi, rotK_testBit hk hy offset i hi] at htb
    have heq : (i + k - offset % k) % k = b := by
      dsimp only [i]
      have hs : offset % k < k := Nat.mod_lt offset hk
      have h1 : (b + offset % k) % k + k - offset % k =
          (b + offset % k) % k + (k - offset % k) := by omega
      rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h2 : b + offset % k + (k - offset % k) = b + k := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hb]
    rw [heq] at htb
    exact htb
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]

lemma chiK_spec (k word : Nat) :
    chiK k word < 2 ^ k ∧
    ∀ i < k, (chiK k word).testBit i =
      xor (word.testBit i) (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k)) := by
  let bitFn : Nat → Bool := fun site =>
    xor (word.testBit site) (!(word.testBit ((site + 1) % k)) && word.testBit ((site + 2) % k))
  have htake : ∀ m ≤ k,
      let v := (List.range m).foldl (fun acc b => acc ||| ((bitFn b).toNat <<< b)) 0
      (∀ j, m ≤ j → v.testBit j = false) ∧ (∀ b < m, v.testBit b = bitFn b) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun _ _ => by simp, fun _ hb => by omega⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hprev.1 j (by omega)]
        have h1 : m ≤ j := by omega
        have hlt2 : (bitFn m).toNat < 2 ^ (j - m) := by
          have hle1 : (bitFn m).toNat ≤ 1 := by cases bitFn m <;> decide
          have hpow : 2 ≤ 2 ^ (j - m) := Nat.le_self_pow (by omega) 2
          omega
        rw [decide_eq_true h1, Bool.true_and, Nat.testBit_eq_false_of_lt hlt2]
        rfl
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
        by_cases hbm : b < m
        · rw [hprev.2 b hbm, decide_eq_false (by omega : ¬ m ≤ b), Bool.false_and, Bool.or_false]
        · have hbe : b = m := by omega
          subst hbe
          rw [hprev.1 b (le_refl _), decide_eq_true (le_refl _), Bool.true_and, Bool.false_or, Nat.sub_self]
          cases bitFn b <;> decide
  have hfull := htake k le_rfl
  refine ⟨?_, hfull.2⟩
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  exact hfull.1 j hj

lemma stateN_zero (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name : Nat) :
    stateN k r c side key name 0 = rotK k (if side then 3 else 1) key ^^^ name := rfl

lemma stateN_succ (k r : Nat) (c : Nat → Fin (2 ^ k)) (side : Bool) (key name n : Nat) :
    stateN k r c side key name (n + 1) =
    stepK k r c side key (stateN k r c side key name n) (n + 1) := by
  dsimp only [stateN]
  rw [List.range_succ, List.foldl_append]
  rfl

lemma stateN_lt {k r : Nat} (c : Nat → Fin (2 ^ k)) (side : Bool) (key : Nat)
    {name : Nat} (hname : name < 2 ^ k) :
    ∀ n : Nat, stateN k r c side key name n < 2 ^ k := by
  intro n
  cases n with
  | zero =>
    rw [stateN_zero]
    exact Nat.xor_lt_two_pow (rotK_lt _ _) hname
  | succ m =>
    rw [stateN_succ]
    dsimp only [stepK]
    exact Nat.xor_lt_two_pow
      (Nat.xor_lt_two_pow (chiK_spec k _).1 (rotK_lt _ _))
      (c _).isLt

lemma cutK_testBit (word offset len j : Nat) (hj : j < len) :
    (cutK word offset len).testBit j = word.testBit (offset + j) := by
  dsimp only [cutK]
  rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and, Nat.testBit_shiftRight]

def AgreeCyc (k x y lo len : Nat) : Prop :=
  ∀ d < len, x.testBit ((lo + d) % k) = y.testBit ((lo + d) % k)

lemma agreeCyc_rot {k : Nat} (hk : 0 < k) {x y : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (s lo len : Nat) (h : AgreeCyc k x y (lo + k - s % k) len) :
    AgreeCyc k (rotK k s x) (rotK k s y) lo len := by
  intro d hd
  have hi : (lo + d) % k < k := Nat.mod_lt _ hk
  rw [rotK_testBit hk hx s _ hi, rotK_testBit hk hy s _ hi]
  have hs : s % k < k := Nat.mod_lt s hk
  have heq : ((lo + d) % k + k - s % k) % k = ((lo + k - s % k) + d) % k := by
    have h1 : (lo + d) % k + k - s % k = (lo + d) % k + (k - s % k) := by omega
    rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    congr 1
    omega
  rw [heq]
  exact h d hd

lemma agreeCyc_mix {k gap : Nat} (hgap0 : 0 < gap) (hgap : gap < k) {u v : Nat}
    (hu : u < 2 ^ k) (hv : v < 2 ^ k) (lo len : Nat)
    (h : AgreeCyc k u v (lo + k - gap) (len + 2 * gap)) :
    AgreeCyc k (mixK k gap u) (mixK k gap v) lo len := by
  have hk : 0 < k := by omega
  intro d hd
  dsimp only [mixK]
  rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
  have h1 : u.testBit ((lo + d) % k) = v.testBit ((lo + d) % k) := by
    have heq : (lo + d) % k = (lo + k - gap + (d + gap)) % k := by
      have hsum : lo + k - gap + (d + gap) = (lo + d) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [heq]
    exact h (d + gap) (by omega)
  have h2 : (rotK k gap u).testBit ((lo + d) % k) = (rotK k gap v).testBit ((lo + d) % k) := by
    have hi : (lo + d) % k < k := Nat.mod_lt _ hk
    rw [rotK_testBit hk hu gap _ hi, rotK_testBit hk hv gap _ hi, Nat.mod_eq_of_lt hgap]
    have heq : ((lo + d) % k + k - gap) % k = (lo + k - gap + d) % k := by
      have hsub : (lo + d) % k + k - gap = (lo + d) % k + (k - gap) := by omega
      rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      congr 1
      omega
    rw [heq]
    exact h d (by omega)
  have h3 : (rotK k (k - gap) u).testBit ((lo + d) % k) = (rotK k (k - gap) v).testBit ((lo + d) % k) := by
    have hi : (lo + d) % k < k := Nat.mod_lt _ hk
    rw [rotK_testBit hk hu (k - gap) _ hi, rotK_testBit hk hv (k - gap) _ hi,
      Nat.mod_eq_of_lt (by omega : k - gap < k)]
    have heq : ((lo + d) % k + k - (k - gap)) % k = (lo + k - gap + (d + 2 * gap)) % k := by
      have hsub : (lo + d) % k + k - (k - gap) = (lo + d) % k + gap := by omega
      rw [hsub, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have hsum : lo + k - gap + (d + 2 * gap) = (lo + d + gap) + k := by omega
      rw [hsum, Nat.add_mod_right]
    rw [heq]
    exact h (d + 2 * gap) (by omega)
  rw [h1, h2, h3]

lemma agreeCyc_chi {k : Nat} (hk : 0 < k) {u v : Nat} (lo len : Nat)
    (h : AgreeCyc k u v lo (len + 2)) :
    AgreeCyc k (chiK k u) (chiK k v) lo len := by
  intro d hd
  have hi : (lo + d) % k < k := Nat.mod_lt _ hk
  rw [(chiK_spec k u).2 _ hi, (chiK_spec k v).2 _ hi]
  have h0 : u.testBit ((lo + d) % k) = v.testBit ((lo + d) % k) := h d (by omega)
  have h1 : u.testBit (((lo + d) % k + 1) % k) = v.testBit (((lo + d) % k + 1) % k) := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : lo + d + 1 = lo + (d + 1) := by omega
    rw [heq]
    exact h (d + 1) (by omega)
  have h2 : u.testBit (((lo + d) % k + 2) % k) = v.testBit (((lo + d) % k + 2) % k) := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have heq : lo + d + 2 = lo + (d + 2) := by omega
    rw [heq]
    exact h (d + 2) (by omega)
  rw [h0, h1, h2]

lemma agreeCyc_chi_mix {k gap : Nat} (hgap0 : 0 < gap) (hgap : gap < k) {u v : Nat}
    (hu : u < 2 ^ k) (hv : v < 2 ^ k) (lo len : Nat)
    (h : AgreeCyc k u v (lo + k - gap) (len + 2 * gap + 2)) :
    AgreeCyc k (chiK k (mixK k gap u)) (chiK k (mixK k gap v)) lo len := by
  have hk : 0 < k := by omega
  apply agreeCyc_chi hk lo len
  have h' : AgreeCyc k u v (lo + k - gap) ((len + 2) + 2 * gap) := by
    have heq : (len + 2) + 2 * gap = len + 2 * gap + 2 := by omega
    rw [heq]
    exact h
  exact agreeCyc_mix hgap0 hgap hu hv lo (len + 2) h'

def rowL (t : Nat) : Nat := max (t + 1) (2 * t - 2)

lemma row_stateN_congr {k r : Nat} (hr : 4 ≤ r) (hk : 5 * r - 2 ≤ k)
    (c : Nat → Fin (2 ^ k)) {row x y : Nat}
    (hrow : row < 2 ^ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ∀ t ≤ r, ∀ lo len : Nat,
      AgreeCyc k x y (lo + k - rowL t) (len + rowL t + 3 * t - 1) →
      AgreeCyc k (stateN k r c false x row t) (stateN k r c false y row t) lo len := by
  have hkpos : 0 < k := by omega
  intro t
  induction t with
  | zero =>
    intro _ lo len h
    rw [stateN_zero, stateN_zero]
    intro d hd
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    have hrot : (rotK k 1 x).testBit ((lo + d) % k) = (rotK k 1 y).testBit ((lo + d) % k) := by
      have h1 : AgreeCyc k x y (lo + k - 1 % k) len := by
        rw [Nat.mod_eq_of_lt (by omega : 1 < k)]
        intro e he
        exact h e (by dsimp only [rowL]; omega)
      exact agreeCyc_rot hkpos hx hy 1 lo len h1 d hd
    rw [hrot]
  | succ t ih =>
    intro ht lo len h
    have ht' : t ≤ r := by omega
    have hL_lt : rowL (t + 1) < k := by dsimp only [rowL]; omega
    have hLt_lt : rowL t < k := by dsimp only [rowL]; omega
    have hL_rec : rowL (t + 1) = max (rowL t + 1) (2 * t) := by dsimp only [rowL]; omega
    rw [stateN_succ, stateN_succ]
    have hprev_ag : AgreeCyc k x y ((lo + k - 1) + k - rowL t) ((len + 4) + rowL t + 3 * t - 1) := by
      intro d hd
      have hshift : ((lo + k - 1) + k - rowL t + d) % k =
          (lo + k - rowL (t + 1) + (d + (rowL (t + 1) - (rowL t + 1)))) % k := by
        have h1 : (lo + k - 1) + k - rowL t + d =
            (lo + k - rowL (t + 1) + (d + (rowL (t + 1) - (rowL t + 1)))) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hshift]
      exact h (d + (rowL (t + 1) - (rowL t + 1))) (by omega)
    have hprev := ih ht' (lo + k - 1) (len + 4) hprev_ag
    have hchimix := agreeCyc_chi_mix (gap := 1) (by omega : 0 < 1) (by omega : 1 < k)
      (stateN_lt c false x hrow t) (stateN_lt c false y hrow t) lo len hprev
    have hrot_ag : AgreeCyc k x y (lo + k - (2 * t) % k) len := by
      rw [Nat.mod_eq_of_lt (by omega : 2 * t < k)]
      intro d hd
      have hshift : (lo + k - 2 * t + d) % k =
          (lo + k - rowL (t + 1) + (d + (rowL (t + 1) - 2 * t))) % k := by
        congr 1; omega
      rw [hshift]
      exact h (d + (rowL (t + 1) - 2 * t)) (by omega)
    have hrot := agreeCyc_rot hkpos hx hy (2 * t) lo len hrot_ag
    intro d hd
    dsimp only [stepK]
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [hchimix d hd, hrot d hd]

lemma row_final_chimix_congr {k r : Nat} (hr : 4 ≤ r) (hk : 5 * r - 2 ≤ k)
    (c : Nat → Fin (2 ^ k)) {row x y : Nat}
    (hrow : row < 2 ^ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (i : Nat) (hi : i < k)
    (h : AgreeCyc k x y (i + k - (2 * r - 3)) (5 * r - 3)) :
    (chiK k (mixK k 1 (stateN k r c false x row (r - 1)))).testBit i =
    (chiK k (mixK k 1 (stateN k r c false y row (r - 1)))).testBit i := by
  have hkpos : 0 < k := by omega
  have hLr : rowL (r - 1) = 2 * r - 4 := by dsimp only [rowL]; omega
  have hprev_ag : AgreeCyc k x y ((i + k - 1) + k - rowL (r - 1)) (5 + rowL (r - 1) + 3 * (r - 1) - 1) := by
    intro d hd
    have hshift : ((i + k - 1) + k - rowL (r - 1) + d) % k = (i + k - (2 * r - 3) + d) % k := by
      have h1 : (i + k - 1) + k - rowL (r - 1) + d = (i + k - (2 * r - 3) + d) + k := by omega
      rw [h1, Nat.add_mod_right]
    rw [hshift]
    exact h d (by omega)
  have hprev := row_stateN_congr hr hk c hrow hx hy (r - 1) (by omega) (i + k - 1) 5 hprev_ag
  have hcm := agreeCyc_chi_mix (gap := 1) (by omega : 0 < 1) (by omega : 1 < k)
    (stateN_lt c false x hrow (r - 1)) (stateN_lt c false y hrow (r - 1)) i 1 hprev
  have h0 := hcm 0 (by omega)
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hi] at h0
  exact h0

def colL (t : Nat) : Nat := max (2 * t + 3) (3 * t + 1)

lemma col_stateN_congr {k r : Nat} (hr : 4 ≤ r) (hk : 5 * r - 2 ≤ k)
    (c : Nat → Fin (2 ^ k)) {col x y : Nat}
    (hcol : col < 2 ^ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    ∀ t ≤ r, ∀ lo len : Nat,
      AgreeCyc k x y (lo + k - colL t) (len + colL t + 4 * t - 3) →
      AgreeCyc k (stateN k r c true x col t) (stateN k r c true y col t) lo len := by
  have hkpos : 0 < k := by omega
  intro t
  induction t with
  | zero =>
    intro _ lo len h
    rw [stateN_zero, stateN_zero]
    intro d hd
    simp only [↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor]
    have hrot : (rotK k 3 x).testBit ((lo + d) % k) = (rotK k 3 y).testBit ((lo + d) % k) := by
      have h1 : AgreeCyc k x y (lo + k - 3 % k) len := by
        rw [Nat.mod_eq_of_lt (by omega : 3 < k)]
        intro e he
        exact h e (by dsimp only [colL]; omega)
      exact agreeCyc_rot hkpos hx hy 3 lo len h1 d hd
    rw [hrot]
  | succ t ih =>
    intro ht lo len h
    have ht' : t ≤ r := by omega
    have hL_lt : colL (t + 1) < k := by dsimp only [colL]; omega
    have hLt_lt : colL t < k := by dsimp only [colL]; omega
    have hL_rec : colL (t + 1) = max (colL t + 2) (3 * t + 4) := by dsimp only [colL]; omega
    rw [stateN_succ, stateN_succ]
    have hprev_ag : AgreeCyc k x y ((lo + k - 2) + k - colL t) ((len + 6) + colL t + 4 * t - 3) := by
      intro d hd
      have hshift : ((lo + k - 2) + k - colL t + d) % k =
          (lo + k - colL (t + 1) + (d + (colL (t + 1) - (colL t + 2)))) % k := by
        have h1 : (lo + k - 2) + k - colL t + d =
            (lo + k - colL (t + 1) + (d + (colL (t + 1) - (colL t + 2)))) + k := by omega
        rw [h1, Nat.add_mod_right]
      rw [hshift]
      exact h (d + (colL (t + 1) - (colL t + 2))) (by omega)
    have hprev := ih ht' (lo + k - 2) (len + 6) hprev_ag
    have hchimix := agreeCyc_chi_mix (gap := 2) (by omega : 0 < 2) (by omega : 2 < k)
      (stateN_lt c true x hcol t) (stateN_lt c true y hcol t) lo len hprev
    have hrot_ag : AgreeCyc k x y (lo + k - (3 * (t + 1) + 1) % k) len := by
      rw [Nat.mod_eq_of_lt (by omega : 3 * (t + 1) + 1 < k)]
      intro d hd
      have hshift : (lo + k - (3 * (t + 1) + 1) + d) % k =
          (lo + k - colL (t + 1) + (d + (colL (t + 1) - (3 * (t + 1) + 1)))) % k := by
        congr 1; omega
      rw [hshift]
      exact h (d + (colL (t + 1) - (3 * (t + 1) + 1))) (by omega)
    have hrot := agreeCyc_rot hkpos hx hy (3 * (t + 1) + 1) lo len hrot_ag
    intro d hd
    dsimp only [stepK]
    simp only [↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor]
    rw [hchimix d hd, hrot d hd]

lemma col_final_chimix_congr {k r : Nat} (hr : 4 ≤ r) (hk : 5 * r - 2 ≤ k)
    (c : Nat → Fin (2 ^ k)) {col x y : Nat}
    (hcol : col < 2 ^ k) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (i : Nat) (hi : i < k)
    (h : AgreeCyc k x y (i + k - 3 * r) (7 * r - 2)) :
    (chiK k (mixK k 2 (stateN k r c true x col (r - 1)))).testBit i =
    (chiK k (mixK k 2 (stateN k r c true y col (r - 1)))).testBit i := by
  have hkpos : 0 < k := by omega
  have hLc : colL (r - 1) = 3 * r - 2 := by dsimp only [colL]; omega
  have hprev_ag : AgreeCyc k x y ((i + k - 2) + k - colL (r - 1)) (7 + colL (r - 1) + 4 * (r - 1) - 3) := by
    intro d hd
    have hshift : ((i + k - 2) + k - colL (r - 1) + d) % k = (i + k - 3 * r + d) % k := by
      have h1 : (i + k - 2) + k - colL (r - 1) + d = (i + k - 3 * r + d) + k := by omega
      rw [h1, Nat.add_mod_right]
    rw [hshift]
    exact h d (by omega)
  have hprev := col_stateN_congr hr hk c hcol hx hy (r - 1) (by omega) (i + k - 2) 7 hprev_ag
  have hcm := agreeCyc_chi_mix (gap := 2) (by omega : 0 < 2) (by omega : 2 < k)
    (stateN_lt c true x hcol (r - 1)) (stateN_lt c true y hcol (r - 1)) i 1 hprev
  have h0 := hcm 0 (by omega)
  simp only [Nat.add_zero, Nat.mod_eq_of_lt hi] at h0
  exact h0

lemma inv_part {k r : Nat} (hr : 4 ≤ r)
    (sched : Nat → Fin (2 ^ k)) {row column original change : Nat}
    (hrow : row < 2 ^ k) (hcol : column < 2 ^ k)
    (horig : original < 2 ^ k) (hchg : change < 2 ^ unusedOf k r) :
    let mate := original ^^^ (change <<< (4 * r - 3))
    mate < 2 ^ k ∧
    stateN k r sched false original row r >>> zOf k =
      stateN k r sched false mate row r >>> zOf k ∧
    stateN k r sched true original column r >>> zOf k =
      stateN k r sched true mate column r >>> zOf k := by
  intro mate
  by_cases hun0 : unusedOf k r = 0
  · have hchg0 : change = 0 := by
      have h1 : 2 ^ unusedOf k r = 1 := by rw [hun0]; rfl
      omega
    have hmate_eq : mate = original := by dsimp only [mate]; rw [hchg0]; simp
    rw [hmate_eq]
    exact ⟨horig, rfl, rfl⟩
  · have hun_pos : 0 < unusedOf k r := by omega
    have hzg : 7 * r - 2 < zOf k := by dsimp only [unusedOf] at hun_pos; omega
    have hkgt : 5 * r - 2 ≤ k := by dsimp only [zOf, hOf] at *; omega
    have hshift_lt : change <<< (4 * r - 3) < 2 ^ k := by
      rw [Nat.shiftLeft_eq]
      have h1 : change * 2 ^ (4 * r - 3) < 2 ^ unusedOf k r * 2 ^ (4 * r - 3) :=
        Nat.mul_lt_mul_of_pos_right hchg (Nat.two_pow_pos _)
      rw [← pow_add] at h1
      have hexp : unusedOf k r + (4 * r - 3) ≤ k := by dsimp only [unusedOf, zOf, hOf] at *; omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hexp)
    have hmate_lt : mate < 2 ^ k := Nat.xor_lt_two_pow horig hshift_lt
    have hagree_out : ∀ b, (b < 4 * r - 3 ∨ zOf k - 3 * r - 1 ≤ b) →
        original.testBit b = mate.testBit b := by
      intro b hb
      dsimp only [mate]
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      rcases hb with hlo | hhi
      · rw [decide_eq_false (by omega : ¬ (4 * r - 3 ≤ b)), Bool.false_and, Bool.xor_false]
      · have hge : 4 * r - 3 ≤ b := by omega
        have hsub : unusedOf k r ≤ b - (4 * r - 3) := by dsimp only [unusedOf] at *; omega
        have hfalse : change.testBit (b - (4 * r - 3)) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hchg (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hsub))
        rw [decide_eq_true hge, Bool.true_and, hfalse, Bool.xor_false]
    have hrow_hi : ∀ i, zOf k ≤ i → i < k →
        (stateN k r sched false original row r).testBit i =
        (stateN k r sched false mate row r).testBit i := by
      intro i hi1 hi2
      have hLr : rowL r = 2 * r - 2 := by dsimp only [rowL]; omega
      have hag : AgreeCyc k original mate (i + k - rowL r) (1 + rowL r + 3 * r - 1) := by
        intro d hd
        by_cases hwrap : i + k - rowL r + d < 2 * k
        · have hmod : (i + k - rowL r + d) % k = i + k - rowL r + d - k := by
            have h1 : i + k - rowL r + d = (i + k - rowL r + d - k) + k := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          exact hagree_out _ (Or.inr (by omega))
        · have hmod : (i + k - rowL r + d) % k = i + k - rowL r + d - 2 * k := by
            have h1 : i + k - rowL r + d = (i + k - rowL r + d - 2 * k) + k * 2 := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by dsimp only [zOf, hOf] at *; omega)]
          rw [hmod]
          exact hagree_out _ (Or.inl (by omega))
      have h0 := row_stateN_congr hr hkgt sched hrow horig hmate_lt r le_rfl i 1 hag 0 (by omega)
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hi2] at h0
      exact h0
    have hcol_hi : ∀ i, zOf k ≤ i → i < k →
        (stateN k r sched true original column r).testBit i =
        (stateN k r sched true mate column r).testBit i := by
      intro i hi1 hi2
      have hLc : colL r = 3 * r + 1 := by dsimp only [colL]; omega
      have hag : AgreeCyc k original mate (i + k - colL r) (1 + colL r + 4 * r - 3) := by
        intro d hd
        by_cases hwrap : i + k - colL r + d < 2 * k
        · have hmod : (i + k - colL r + d) % k = i + k - colL r + d - k := by
            have h1 : i + k - colL r + d = (i + k - colL r + d - k) + k := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          exact hagree_out _ (Or.inr (by omega))
        · have hmod : (i + k - colL r + d) % k = i + k - colL r + d - 2 * k := by
            have h1 : i + k - colL r + d = (i + k - colL r + d - 2 * k) + k * 2 := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by dsimp only [zOf, hOf] at *; omega)]
          rw [hmod]
          exact hagree_out _ (Or.inl (by omega))
      have h0 := col_stateN_congr hr hkgt sched hcol horig hmate_lt r le_rfl i 1 hag 0 (by omega)
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hi2] at h0
      exact h0
    refine ⟨hmate_lt, ?_, ?_⟩
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
      by_cases hj : zOf k + j < k
      · exact hrow_hi (zOf k + j) (by omega) hj
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched false original hrow r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ zOf k + j))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched false mate hrow r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ zOf k + j)))]
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
      by_cases hj : zOf k + j < k
      · exact hcol_hi (zOf k + j) (by omega) hj
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched true original hcol r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ zOf k + j))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched true mate hcol r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ zOf k + j)))]

lemma phi_inj {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (sched : Nat → Fin (2 ^ k)) {row column x y : Nat}
    (hrow : row < 2 ^ k) (hcol : column < 2 ^ k)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (hseed : seedOf k r x = seedOf k r y)
    (hspare : cutK x (4 * r - 3) (unusedOf k r) = cutK y (4 * r - 3) (unusedOf k r))
    (hrowP : cutK (stateN k r sched false x row r) (k - rowLenOf k r) (rowLenOf k r) =
      cutK (stateN k r sched false y row r) (k - rowLenOf k r) (rowLenOf k r))
    (hcolP : cutK (stateN k r sched true x column r) (zOf k + (r + 3) - colLenOf k r) (colLenOf k r) =
      cutK (stateN k r sched true y column r) (zOf k + (r + 3) - colLenOf k r) (colLenOf k r)) :
    x = y := by
  have hsum := dims_sum k r hr
  by_cases hkle : k ≤ uOf r
  · have hsw : swOf k r = k := by
      dsimp only [swOf, extraOf, uOf, zOf, hOf] at *; omega
    have hrot_eq : rotK k (k - startOf k r % k) x = rotK k (k - startOf k r % k) y := by
      dsimp only [seedOf] at hseed
      rw [hsw, Nat.mod_eq_of_lt (rotK_lt _ _), Nat.mod_eq_of_lt (rotK_lt _ _)] at hseed
      exact hseed
    exact rotK_inj hkpos (k - startOf k r % k) hx hy hrot_eq
  · have hkgt : 5 * r - 2 ≤ k := by dsimp only [uOf] at hkle; omega
    have hstart_lt : startOf k r < k := by dsimp only [startOf]; omega
    have hstart_eq : k - startOf k r % k = 2 * r - 2 := by
      rw [Nat.mod_eq_of_lt hstart_lt]
      dsimp only [startOf]; omega
    have hseed_bit : ∀ j < swOf k r,
        x.testBit ((startOf k r + j) % k) = y.testBit ((startOf k r + j) % k) := by
      intro j hj
      have htb : (rotK k (k - startOf k r % k) x % 2 ^ swOf k r).testBit j =
          (rotK k (k - startOf k r % k) y % 2 ^ swOf k r).testBit j :=
        congrArg (fun n => n.testBit j) hseed
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
        decide_eq_true hj, Bool.true_and, Bool.true_and] at htb
      have hjlt : j < k := by omega
      rw [rotK_testBit hkpos hx _ j hjlt, rotK_testBit hkpos hy _ j hjlt,
        hstart_eq, Nat.mod_eq_of_lt (by omega : 2 * r - 2 < k)] at htb
      have hidx : (j + k - (2 * r - 2)) % k = (startOf k r + j) % k := by
        congr 1; dsimp only [startOf]; omega
      rw [hidx] at htb
      exact htb
    have htop : ∀ b, k - (2 * r - 2) ≤ b → b < k → x.testBit b = y.testBit b := by
      intro b hb1 hb2
      have hj : b - startOf k r < swOf k r := by dsimp only [startOf, swOf, uOf, extraOf]; omega
      have h := hseed_bit (b - startOf k r) hj
      have heq : (startOf k r + (b - startOf k r)) % k = b := by
        have h1 : startOf k r + (b - startOf k r) = b := by dsimp only [startOf]; omega
        rw [h1, Nat.mod_eq_of_lt hb2]
      rw [heq] at h
      exact h
    have hbot : ∀ b < 3 * r - 1 + extraOf k r, x.testBit b = y.testBit b := by
      intro b hb
      have hj : b + (2 * r - 2) < swOf k r := by dsimp only [swOf, uOf, extraOf] at hb ⊢; omega
      have h := hseed_bit (b + (2 * r - 2)) hj
      have heq : (startOf k r + (b + (2 * r - 2))) % k = b := by
        have h1 : startOf k r + (b + (2 * r - 2)) = b + k := by dsimp only [startOf]; omega
        have hblt : b < k := by dsimp only [extraOf, zOf, hOf] at hb; omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hblt]
      rw [heq] at h
      exact h
    have hsp : ∀ b, 4 * r - 3 ≤ b → b < 4 * r - 3 + unusedOf k r → x.testBit b = y.testBit b := by
      intro b hb1 hb2
      have hj : b - (4 * r - 3) < unusedOf k r := by omega
      have htb := congrArg (fun n => n.testBit (b - (4 * r - 3))) hspare
      rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at htb
      have heq : 4 * r - 3 + (b - (4 * r - 3)) = b := by omega
      rw [heq] at htb
      exact htb
    have hrow_solve : ∀ m ≤ rowLenOf k r, ∀ b, k - (2 * r - 2) - m ≤ b → b < k →
        x.testBit b = y.testBit b := by
      intro m
      induction m with
      | zero => intro _ b hb1 hb2; exact htop b (by omega) hb2
      | succ m ih =>
        intro hm b hb1 hb2
        by_cases hbm : k - (2 * r - 2) - m ≤ b
        · exact ih (by omega) b hbm hb2
        · have hb_eq : b = k - (2 * r - 2) - (m + 1) := by omega
          subst hb_eq
          set p := k - (2 * r - 2) - (m + 1)
          set i := k - (m + 1)
          have hi_lt : i < k := by dsimp only [i]; omega
          have hcone : AgreeCyc k x y (i + k - (2 * r - 3)) (5 * r - 3) := by
            intro d hd
            have hidx : (i + k - (2 * r - 3) + d) % k = (p + 1 + d) % k := by
              have h1 : i + k - (2 * r - 3) + d = (p + 1 + d) + k := by
                dsimp only [p, i, rowLenOf, uOf, hOf] at *; omega
              rw [h1, Nat.add_mod_right]
            rw [hidx]
            by_cases hwrap : p + 1 + d < k
            · rw [Nat.mod_eq_of_lt hwrap]
              exact ih (by omega) (p + 1 + d) (by dsimp only [p]; omega) hwrap
            · have hmod : (p + 1 + d) % k = p + 1 + d - k := by
                have h1 : p + 1 + d = (p + 1 + d - k) + k := by omega
                conv_lhs => rw [h1]
                rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p]; omega)]
              rw [hmod]
              exact hbot (p + 1 + d - k) (by dsimp only [p, extraOf]; omega)
          have hcm := row_final_chimix_congr hr hkgt sched hrow hx hy i hi_lt hcone
          have hst_eq : (stateN k r sched false x row r).testBit i =
              (stateN k r sched false y row r).testBit i := by
            have hj : i - (k - rowLenOf k r) < rowLenOf k r := by dsimp only [i]; omega
            have htb := congrArg (fun n => n.testBit (i - (k - rowLenOf k r))) hrowP
            rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at htb
            have heq : k - rowLenOf k r + (i - (k - rowLenOf k r)) = i := by dsimp only [i]; omega
            rw [heq] at htb
            exact htb
          have hstep_r : ∀ key : Nat,
              stateN k r sched false key row r =
              stepK k r sched false key (stateN k r sched false key row (r - 1)) r := by
            intro key
            have hr_eq : r = (r - 1) + 1 := by omega
            conv_lhs => arg 7; rw [hr_eq]
            rw [stateN_succ, ← hr_eq]
          rw [hstep_r x, hstep_r y] at hst_eq
          dsimp only [stepK] at hst_eq
          simp only [Bool.false_eq_true, ↓reduceIte] at hst_eq
          rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, hcm] at hst_eq
          have hrot_eq : (rotK k (2 * (r - 1)) x).testBit i =
              (rotK k (2 * (r - 1)) y).testBit i := by
            revert hst_eq
            generalize (chiK k (mixK k 1 (stateN k r sched false y row (r - 1)))).testBit i = a0
            generalize (rotK k (2 * (r - 1)) x).testBit i = b1
            generalize (rotK k (2 * (r - 1)) y).testBit i = b2
            generalize (sched r).val.testBit i = c0
            cases a0 <;> cases b1 <;> cases b2 <;> cases c0 <;> decide
          rw [rotK_testBit hkpos hx _ i hi_lt, rotK_testBit hkpos hy _ i hi_lt,
            Nat.mod_eq_of_lt (by omega : 2 * (r - 1) < k)] at hrot_eq
          have hp_idx : (i + k - 2 * (r - 1)) % k = p := by
            have h1 : i + k - 2 * (r - 1) = p + k := by
              dsimp only [p, i, rowLenOf, uOf, hOf] at *; omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p]; omega)]
          rw [hp_idx] at hrot_eq
          exact hrot_eq
    have hcol_solve : ∀ m ≤ colLenOf k r, ∀ b, k - (2 * r - 2) - rowLenOf k r - m ≤ b → b < k →
        x.testBit b = y.testBit b := by
      intro m
      induction m with
      | zero => intro _ b hb1 hb2; exact hrow_solve (rowLenOf k r) le_rfl b (by omega) hb2
      | succ m ih =>
        intro hm b hb1 hb2
        by_cases hbm : k - (2 * r - 2) - rowLenOf k r - m ≤ b
        · exact ih (by omega) b hbm hb2
        · have hb_eq : b = k - (2 * r - 2) - rowLenOf k r - (m + 1) := by omega
          subst hb_eq
          have hcol_pos : 0 < colLenOf k r := by omega
          have hzu : uOf r < zOf k := by dsimp only [colLenOf] at hcol_pos; omega
          have hrl_eq : rowLenOf k r = hOf k := by dsimp only [rowLenOf, uOf, zOf, hOf] at *; omega
          set q := k - (2 * r - 2) - rowLenOf k r - (m + 1)
          set i := zOf k + (r + 3) - (m + 1)
          have hi_lt : i < k := by dsimp only [i, uOf, zOf, hOf] at *; omega
          have hcone : AgreeCyc k x y (i + k - 3 * r) (7 * r - 2) := by
            intro d hd
            have hidx : (i + k - 3 * r + d) % k = (q + 1 + d) % k := by
              have h1 : i + k - 3 * r + d = (q + 1 + d) + k := by
                dsimp only [q, i, colLenOf, uOf, zOf, hOf] at *; omega
              rw [h1, Nat.add_mod_right]
            rw [hidx]
            by_cases hwrap : q + 1 + d < k
            · rw [Nat.mod_eq_of_lt hwrap]
              exact ih (by omega) (q + 1 + d) (by dsimp only [q]; omega) hwrap
            · have hmod : (q + 1 + d) % k = q + 1 + d - k := by
                have h1 : q + 1 + d = (q + 1 + d - k) + k := by omega
                conv_lhs => rw [h1]
                rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q, uOf, zOf, hOf] at *; omega)]
              rw [hmod]
              exact hbot (q + 1 + d - k) (by dsimp only [q, uOf, zOf, hOf, extraOf] at *; omega)
          have hcm := col_final_chimix_congr hr hkgt sched hcol hx hy i hi_lt hcone
          have hst_eq : (stateN k r sched true x column r).testBit i =
              (stateN k r sched true y column r).testBit i := by
            have hj : i - (zOf k + (r + 3) - colLenOf k r) < colLenOf k r := by dsimp only [i]; omega
            have htb := congrArg (fun n => n.testBit (i - (zOf k + (r + 3) - colLenOf k r))) hcolP
            rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at htb
            have heq : zOf k + (r + 3) - colLenOf k r + (i - (zOf k + (r + 3) - colLenOf k r)) = i := by
              dsimp only [i]; omega
            rw [heq] at htb
            exact htb
          have hstep_r : ∀ key : Nat,
              stateN k r sched true key column r =
              stepK k r sched true key (stateN k r sched true key column (r - 1)) r := by
            intro key
            have hr_eq : r = (r - 1) + 1 := by omega
            conv_lhs => arg 7; rw [hr_eq]
            rw [stateN_succ, ← hr_eq]
          rw [hstep_r x, hstep_r y] at hst_eq
          dsimp only [stepK] at hst_eq
          simp only [↓reduceIte] at hst_eq
          rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, hcm] at hst_eq
          have hrot_eq : (rotK k (3 * r + 1) x).testBit i =
              (rotK k (3 * r + 1) y).testBit i := by
            revert hst_eq
            generalize (chiK k (mixK k 2 (stateN k r sched true y column (r - 1)))).testBit i = a0
            generalize (rotK k (3 * r + 1) x).testBit i = b1
            generalize (rotK k (3 * r + 1) y).testBit i = b2
            generalize (sched (r + r)).val.testBit i = c0
            cases a0 <;> cases b1 <;> cases b2 <;> cases c0 <;> decide
          rw [rotK_testBit hkpos hx _ i hi_lt, rotK_testBit hkpos hy _ i hi_lt,
            Nat.mod_eq_of_lt (by omega : 3 * r + 1 < k)] at hrot_eq
          have hq_idx : (i + k - (3 * r + 1)) % k = q := by
            have h1 : i + k - (3 * r + 1) = q + k := by
              dsimp only [q, i, colLenOf, uOf, zOf, hOf] at *; omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q]; omega)]
          rw [hq_idx] at hrot_eq
          exact hrot_eq
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hbk : b < k
    · by_cases hhigh : k - (2 * r - 2) - rowLenOf k r - colLenOf k r ≤ b
      · exact hcol_solve (colLenOf k r) le_rfl b hhigh hbk
      · by_cases hlow : b < 3 * r - 1 + extraOf k r
        · exact hbot b hlow
        · exact hsp b (by dsimp only [extraOf, unusedOf, rowLenOf, colLenOf, uOf, zOf, hOf] at *; omega)
            (by dsimp only [extraOf, unusedOf, rowLenOf, colLenOf, uOf, zOf, hOf] at *; omega)
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]

def putBit (w p : Nat) (b : Bool) : Nat := w ||| (b.toNat <<< p)

lemma testBit_putBit_eq {w p : Nat} {b : Bool} (h0 : w.testBit p = false) :
    (putBit w p b).testBit p = b := by
  dsimp only [putBit]
  rw [Nat.testBit_lor, h0, Bool.false_or, Nat.testBit_shiftLeft]
  simp only [le_refl, decide_true, Bool.true_and, Nat.sub_self]
  cases b <;> decide

lemma testBit_putBit_ne {w p j : Nat} {b : Bool} (hne : j ≠ p) :
    (putBit w p b).testBit j = w.testBit j := by
  dsimp only [putBit]
  rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
  by_cases hle : p ≤ j
  · have hlt : b.toNat < 2 ^ (j - p) := by
      have hle1 : b.toNat ≤ 1 := by cases b <;> decide
      have hpow : 2 ≤ 2 ^ (j - p) := Nat.le_self_pow (by omega) 2
      omega
    rw [decide_eq_true hle, Bool.true_and, Nat.testBit_eq_false_of_lt hlt, Bool.or_false]
  · rw [decide_eq_false hle, Bool.false_and, Bool.or_false]

lemma putBit_lt {k w p : Nat} {b : Bool} (hw : w < 2 ^ k) (hp : p < k) :
    putBit w p b < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_putBit_ne (by omega)]
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hj))

def rowDec (k r : Nat) (c : Nat → Fin (2 ^ k)) (leftName a label : Nat) : Nat → Nat
  | 0 => rotK k (startOf k r) label
  | m + 1 =>
    let prev := rowDec k r c leftName a label m
    let p := k - (2 * r - 2) - (m + 1)
    let i := k - (m + 1)
    let st := stateN k r c false prev leftName (r - 1)
    let bit := xor (xor ((chiK k (mixK k 1 st)).testBit i) ((c r).val.testBit i)) (a.testBit (i - zOf k))
    putBit prev p bit

def colDec (k r : Nat) (c : Nat → Fin (2 ^ k)) (leftName rightName a b label : Nat) : Nat → Nat
  | 0 => rowDec k r c leftName a label (rowLenOf k r)
  | m + 1 =>
    let prev := colDec k r c leftName rightName a b label m
    let q := k - (2 * r - 2) - rowLenOf k r - (m + 1)
    let i := zOf k + (r + 3) - (m + 1)
    let st := stateN k r c true prev rightName (r - 1)
    let bit := xor (xor ((chiK k (mixK k 2 st)).testBit i) ((c (r + r)).val.testBit i)) (b.testBit (i - zOf k))
    putBit prev q bit

def decodeSeed (k r : Nat) (c : Nat → Fin (2 ^ k)) (leftName rightName a b label : Nat) : Nat :=
  colDec k r c leftName rightName a b label (colLenOf k r)

lemma seedOf_rotK_start {k r label : Nat} (hkpos : 0 < k) (hr : 4 ≤ r)
    (hlabel : label < 2 ^ swOf k r) :
    seedOf k r (rotK k (startOf k r) label) = label := by
  have hsum := dims_sum k r hr
  have hlabk : label < 2 ^ k :=
    lt_of_lt_of_le hlabel (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))
  apply Nat.eq_of_testBit_eq
  intro j
  dsimp only [seedOf]
  by_cases hj : j < swOf k r
  · rw [Nat.testBit_mod_two_pow, decide_eq_true hj, Bool.true_and]
    have hjk : j < k := by omega
    rw [rotK_testBit hkpos (rotK_lt _ _) _ j hjk]
    set s := startOf k r % k
    have hs : s < k := Nat.mod_lt _ hkpos
    have hidx1 : (j + k - (k - s) % k) % k = (j + s) % k := by
      by_cases hs0 : s = 0
      · rw [hs0, Nat.sub_zero, Nat.mod_self, Nat.sub_zero, Nat.add_zero, Nat.add_mod_right]
      · rw [Nat.mod_eq_of_lt (by omega : k - s < k)]
        congr 1; omega
    rw [hidx1, rotK_testBit hkpos hlabk (startOf k r) _ (Nat.mod_lt _ hkpos)]
    have hidx2 : ((j + s) % k + k - s) % k = j := by
      have h1 : (j + s) % k + k - s = (j + s) % k + (k - s) := by omega
      rw [h1, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h2 : j + s + (k - s) = j + k := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hjk]
    rw [hidx2]
  · rw [Nat.testBit_mod_two_pow, decide_eq_false hj, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlabel (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))).symm

lemma init_mid_false {k r label : Nat} (hr : 4 ≤ r) (_hkgt : 5 * r - 2 ≤ k)
    (hlabel : label < 2 ^ swOf k r) {b : Nat}
    (hb1 : 3 * r - 1 + extraOf k r ≤ b) (hb2 : b < k - (2 * r - 2)) :
    (rotK k (startOf k r) label).testBit b = false := by
  have hsum := dims_sum k r hr
  have hkpos : 0 < k := by omega
  have hlabk : label < 2 ^ k :=
    lt_of_lt_of_le hlabel (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))
  rw [rotK_testBit hkpos hlabk (startOf k r) b (by omega)]
  have hst : startOf k r % k = k - (2 * r - 2) := by
    dsimp only [startOf]; exact Nat.mod_eq_of_lt (by omega)
  rw [hst]
  have hidx : (b + k - (k - (2 * r - 2))) % k = b + (2 * r - 2) := by
    have h1 : b + k - (k - (2 * r - 2)) = b + (2 * r - 2) := by omega
    rw [h1, Nat.mod_eq_of_lt (by omega)]
  rw [hidx]
  have hge : swOf k r ≤ b + (2 * r - 2) := by
    dsimp only [swOf, uOf, extraOf] at *; omega
  exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlabel (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hge))

lemma rowDec_props {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) (a : Nat) {leftName label : Nat}
    (hleft : leftName < 2 ^ k) (hlabel : label < 2 ^ swOf k r) :
    ∀ m ≤ rowLenOf k r,
      let w := rowDec k r c leftName a label m
      w < 2 ^ k ∧
      (∀ b, (b < k - (2 * r - 2) - m ∨ k - (2 * r - 2) ≤ b) →
        w.testBit b = (rotK k (startOf k r) label).testBit b) ∧
      (∀ m' < m,
        (stateN k r c false w leftName r).testBit (k - (m' + 1)) = a.testBit (k - (m' + 1) - zOf k)) := by
  have hsum := dims_sum k r hr
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨rotK_lt _ _, fun _ _ => rfl, fun _ hm => by omega⟩
  | succ m ih =>
    intro hm
    have hrl_pos : 0 < rowLenOf k r := by omega
    have hkgt : 5 * r - 2 ≤ k := by dsimp only [rowLenOf, uOf] at hrl_pos; omega
    have hprev := ih (by omega)
    set prev := rowDec k r c leftName a label m
    set p := k - (2 * r - 2) - (m + 1)
    set i := k - (m + 1)
    set st := stateN k r c false prev leftName (r - 1)
    set bit := xor (xor ((chiK k (mixK k 1 st)).testBit i) ((c r).val.testBit i)) (a.testBit (i - zOf k))
    have hp_lt : p < k := by dsimp only [p]; omega
    have hp_lo : 3 * r - 1 + extraOf k r ≤ p := by
      dsimp only [p, swOf, uOf, extraOf] at *; omega
    have hp_hi : p < k - (2 * r - 2) := by dsimp only [p]; omega
    have hprev_p : prev.testBit p = false := by
      rw [hprev.2.1 p (Or.inl (by dsimp only [p]; omega))]
      exact init_mid_false hr hkgt hlabel hp_lo hp_hi
    have hnext_lt : putBit prev p bit < 2 ^ k := putBit_lt hprev.1 hp_lt
    have hnext_out : ∀ b, (b < k - (2 * r - 2) - (m + 1) ∨ k - (2 * r - 2) ≤ b) →
        (putBit prev p bit).testBit b = (rotK k (startOf k r) label).testBit b := by
      intro b hb
      rw [testBit_putBit_ne (by dsimp only [p]; omega)]
      exact hprev.2.1 b (by rcases hb with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr h2])
    have hnext_agree : ∀ b, b ≠ p → (putBit prev p bit).testBit b = prev.testBit b :=
      fun b hne => testBit_putBit_ne hne
    refine ⟨hnext_lt, hnext_out, ?_⟩
    intro m' hm'
    set i' := k - (m' + 1)
    set p' := k - (2 * r - 2) - (m' + 1)
    have hi'_lt : i' < k := by dsimp only [i']; omega
    have hcone : AgreeCyc k (putBit prev p bit) prev (i' + k - (2 * r - 3)) (5 * r - 3) := by
      intro d hd
      have hidx : (i' + k - (2 * r - 3) + d) % k = (p' + 1 + d) % k := by
        have h1 : i' + k - (2 * r - 3) + d = (p' + 1 + d) + k := by
          dsimp only [p', i', rowLenOf, uOf, hOf] at *; omega
        rw [h1, Nat.add_mod_right]
      rw [hidx]
      apply hnext_agree
      by_cases hwrap : p' + 1 + d < k
      · rw [Nat.mod_eq_of_lt hwrap]
        dsimp only [p, p']; omega
      · have hmod : (p' + 1 + d) % k = p' + 1 + d - k := by
          have h1 : p' + 1 + d = (p' + 1 + d - k) + k := by omega
          conv_lhs => rw [h1]
          rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p']; omega)]
        rw [hmod]
        dsimp only [p, p', extraOf] at *; omega
    have hcm := row_final_chimix_congr hr hkgt c hleft hnext_lt hprev.1 i' hi'_lt hcone
    have hstep_r : ∀ key : Nat,
        stateN k r c false key leftName r =
        stepK k r c false key (stateN k r c false key leftName (r - 1)) r := by
      intro key
      have hr_eq : r = (r - 1) + 1 := by omega
      conv_lhs => arg 7; rw [hr_eq]
      rw [stateN_succ, ← hr_eq]
    change (stateN k r c false (putBit prev p bit) leftName r).testBit i' = a.testBit (i' - zOf k)
    rw [hstep_r (putBit prev p bit)]
    dsimp only [stepK]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Nat.testBit_xor, Nat.testBit_xor, hcm,
      rotK_testBit hkpos hnext_lt _ i' hi'_lt, Nat.mod_eq_of_lt (by omega : 2 * (r - 1) < k)]
    have hp'_idx : (i' + k - 2 * (r - 1)) % k = p' := by
      have h1 : i' + k - 2 * (r - 1) = p' + k := by
        dsimp only [p', i', rowLenOf, uOf, hOf] at *; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p']; omega)]
    rw [hp'_idx]
    by_cases hmeq : m' = m
    · subst hmeq
      have hp_eq : p' = p := rfl
      have hi_eq : i' = i := rfl
      rw [hp_eq, testBit_putBit_eq hprev_p]
      dsimp only [bit, st, i]
      cases (chiK k (mixK k 1 (stateN k r c false prev leftName (r - 1)))).testBit (k - (m' + 1)) <;>
        cases (c r).val.testBit (k - (m' + 1)) <;>
        cases a.testBit (k - (m' + 1) - zOf k) <;> decide
    · have hltm : m' < m := by omega
      have hprev_eq := hprev.2.2 m' hltm
      rw [hstep_r prev] at hprev_eq
      dsimp only [stepK] at hprev_eq
      simp only [Bool.false_eq_true, ↓reduceIte] at hprev_eq
      rw [Nat.testBit_xor, Nat.testBit_xor,
        rotK_testBit hkpos hprev.1 _ i' hi'_lt, Nat.mod_eq_of_lt (by omega : 2 * (r - 1) < k),
        hp'_idx] at hprev_eq
      rw [hnext_agree p' (by dsimp only [p, p']; omega)]
      exact hprev_eq

lemma colDec_props {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) (a b : Nat) {leftName rightName label : Nat}
    (hleft : leftName < 2 ^ k) (hright : rightName < 2 ^ k) (hlabel : label < 2 ^ swOf k r) :
    ∀ m ≤ colLenOf k r,
      let w := colDec k r c leftName rightName a b label m
      w < 2 ^ k ∧
      (∀ bitPos, (bitPos < k - (2 * r - 2) - rowLenOf k r - m ∨ k - (2 * r - 2) ≤ bitPos) →
        w.testBit bitPos = (rotK k (startOf k r) label).testBit bitPos) ∧
      (∀ bitPos, k - (2 * r - 2) - rowLenOf k r ≤ bitPos →
        w.testBit bitPos = (rowDec k r c leftName a label (rowLenOf k r)).testBit bitPos) ∧
      (∀ m' < m,
        (stateN k r c true w rightName r).testBit (zOf k + (r + 3) - (m' + 1)) =
          b.testBit (zOf k + (r + 3) - (m' + 1) - zOf k)) := by
  have hsum := dims_sum k r hr
  intro m
  induction m with
  | zero =>
    intro _
    have hrow0 := rowDec_props hr hkpos c a hleft hlabel (rowLenOf k r) le_rfl
    exact ⟨hrow0.1, fun bp hbp => hrow0.2.1 bp (by simpa using hbp), fun _ _ => rfl, fun _ hm => by omega⟩
  | succ m ih =>
    intro hm
    have hcl_pos : 0 < colLenOf k r := by omega
    have hzu : uOf r < zOf k := by dsimp only [colLenOf] at hcl_pos; omega
    have hkgt : 5 * r - 2 ≤ k := by dsimp only [uOf, zOf, hOf] at *; omega
    have hrl_eq : rowLenOf k r = hOf k := by dsimp only [rowLenOf, uOf, zOf, hOf] at *; omega
    have hprev := ih (by omega)
    set prev := colDec k r c leftName rightName a b label m
    set q := k - (2 * r - 2) - rowLenOf k r - (m + 1)
    set i := zOf k + (r + 3) - (m + 1)
    set st := stateN k r c true prev rightName (r - 1)
    set bit := xor (xor ((chiK k (mixK k 2 st)).testBit i) ((c (r + r)).val.testBit i)) (b.testBit (i - zOf k))
    have hq_lt : q < k := by dsimp only [q]; omega
    have hq_lo : 3 * r - 1 + extraOf k r ≤ q := by
      dsimp only [q, swOf, uOf, extraOf] at *; omega
    have hq_hi : q < k - (2 * r - 2) := by dsimp only [q]; omega
    have hprev_q : prev.testBit q = false := by
      rw [hprev.2.1 q (Or.inl (by dsimp only [q]; omega))]
      exact init_mid_false hr hkgt hlabel hq_lo hq_hi
    have hnext_lt : putBit prev q bit < 2 ^ k := putBit_lt hprev.1 hq_lt
    have hnext_agree : ∀ bp, bp ≠ q → (putBit prev q bit).testBit bp = prev.testBit bp :=
      fun bp hne => testBit_putBit_ne hne
    refine ⟨hnext_lt, ?_, ?_, ?_⟩
    · intro bp hbp
      change (putBit prev q bit).testBit bp = (rotK k (startOf k r) label).testBit bp
      rw [hnext_agree bp (by dsimp only [q]; omega)]
      exact hprev.2.1 bp (by rcases hbp with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr h2])
    · intro bp hbp
      change (putBit prev q bit).testBit bp = (rowDec k r c leftName a label (rowLenOf k r)).testBit bp
      rw [hnext_agree bp (by dsimp only [q]; omega)]
      exact hprev.2.2.1 bp hbp
    · intro m' hm'
      set i' := zOf k + (r + 3) - (m' + 1)
      set q' := k - (2 * r - 2) - rowLenOf k r - (m' + 1)
      have hi'_lt : i' < k := by dsimp only [i', uOf, zOf, hOf] at *; omega
      have hcone : AgreeCyc k (putBit prev q bit) prev (i' + k - 3 * r) (7 * r - 2) := by
        intro d hd
        have hidx : (i' + k - 3 * r + d) % k = (q' + 1 + d) % k := by
          have h1 : i' + k - 3 * r + d = (q' + 1 + d) + k := by
            dsimp only [q', i', colLenOf, uOf, zOf, hOf] at *; omega
          rw [h1, Nat.add_mod_right]
        rw [hidx]
        apply hnext_agree
        by_cases hwrap : q' + 1 + d < k
        · rw [Nat.mod_eq_of_lt hwrap]
          dsimp only [q, q']; omega
        · have hmod : (q' + 1 + d) % k = q' + 1 + d - k := by
            have h1 : q' + 1 + d = (q' + 1 + d - k) + k := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q', uOf, zOf, hOf] at *; omega)]
          rw [hmod]
          dsimp only [q, q', uOf, zOf, hOf, extraOf] at *; omega
      have hcm := col_final_chimix_congr hr hkgt c hright hnext_lt hprev.1 i' hi'_lt hcone
      have hstep_r : ∀ key : Nat,
          stateN k r c true key rightName r =
          stepK k r c true key (stateN k r c true key rightName (r - 1)) r := by
        intro key
        have hr_eq : r = (r - 1) + 1 := by omega
        conv_lhs => arg 7; rw [hr_eq]
        rw [stateN_succ, ← hr_eq]
      change (stateN k r c true (putBit prev q bit) rightName r).testBit i' = b.testBit (i' - zOf k)
      rw [hstep_r (putBit prev q bit)]
      dsimp only [stepK]
      simp only [↓reduceIte]
      rw [Nat.testBit_xor, Nat.testBit_xor, hcm,
        rotK_testBit hkpos hnext_lt _ i' hi'_lt, Nat.mod_eq_of_lt (by omega : 3 * r + 1 < k)]
      have hq'_idx : (i' + k - (3 * r + 1)) % k = q' := by
        have h1 : i' + k - (3 * r + 1) = q' + k := by
          dsimp only [q', i', colLenOf, uOf, zOf, hOf] at *; omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q']; omega)]
      rw [hq'_idx]
      by_cases hmeq : m' = m
      · subst hmeq
        have hq_eq : q' = q := rfl
        rw [hq_eq, testBit_putBit_eq hprev_q]
        dsimp only [bit, st, i]
        cases (chiK k (mixK k 2 (stateN k r c true prev rightName (r - 1)))).testBit (zOf k + (r + 3) - (m' + 1)) <;>
          cases (c (r + r)).val.testBit (zOf k + (r + 3) - (m' + 1)) <;>
          cases b.testBit (zOf k + (r + 3) - (m' + 1) - zOf k) <;> decide
      · have hltm : m' < m := by omega
        have hprev_eq := hprev.2.2.2 m' hltm
        rw [hstep_r prev] at hprev_eq
        dsimp only [stepK] at hprev_eq
        simp only [↓reduceIte] at hprev_eq
        rw [Nat.testBit_xor, Nat.testBit_xor,
          rotK_testBit hkpos hprev.1 _ i' hi'_lt, Nat.mod_eq_of_lt (by omega : 3 * r + 1 < k),
          hq'_idx] at hprev_eq
        rw [hnext_agree q' (by dsimp only [q, q']; omega)]
        exact hprev_eq

lemma decodeSeed_spec {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) (a b : Nat) {leftName rightName label : Nat}
    (hleft : leftName < 2 ^ k) (hright : rightName < 2 ^ k) (hlabel : label < 2 ^ swOf k r) :
    let w0 := decodeSeed k r c leftName rightName a b label
    w0 < 2 ^ k ∧
    seedOf k r w0 = label ∧
    (∀ j < unusedOf k r, w0.testBit (4 * r - 3 + j) = false) ∧
    cutK (stateN k r c false w0 leftName r) (k - rowLenOf k r) (rowLenOf k r) =
      cutK a (hOf k - rowLenOf k r) (rowLenOf k r) ∧
    cutK (stateN k r c true w0 rightName r) (zOf k + (r + 3) - colLenOf k r) (colLenOf k r) =
      cutK b (r + 3 - colLenOf k r) (colLenOf k r) := by
  have hsum := dims_sum k r hr
  have hcol := colDec_props hr hkpos c a b hleft hright hlabel (colLenOf k r) le_rfl
  have hrow := rowDec_props hr hkpos c a hleft hlabel (rowLenOf k r) le_rfl
  set w0 := decodeSeed k r c leftName rightName a b label
  set wR := rowDec k r c leftName a label (rowLenOf k r)
  have hw0_lt : w0 < 2 ^ k := hcol.1
  have hseed_eq : seedOf k r w0 = label := by
    by_cases hkle : k ≤ uOf r
    · have hcl0 : colLenOf k r = 0 := by dsimp only [colLenOf, uOf, zOf, hOf] at *; omega
      have hrl0 : rowLenOf k r = 0 := by dsimp only [rowLenOf, uOf] at *; omega
      have hw0_eq : w0 = rotK k (startOf k r) label := by
        dsimp only [w0, decodeSeed]; rw [hcl0]; dsimp only [colDec]; rw [hrl0]; rfl
      rw [hw0_eq]
      exact seedOf_rotK_start hkpos hr hlabel
    · have hkgt : 5 * r - 2 ≤ k := by dsimp only [uOf] at hkle; omega
      have hstart_lt : startOf k r < k := by dsimp only [startOf]; omega
      have hstart_eq : k - startOf k r % k = 2 * r - 2 := by
        rw [Nat.mod_eq_of_lt hstart_lt]; dsimp only [startOf]; omega
      rw [← seedOf_rotK_start hkpos hr hlabel]
      apply Nat.eq_of_testBit_eq
      intro j
      dsimp only [seedOf]
      by_cases hj : j < swOf k r
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_true hj, Bool.true_and, Bool.true_and,
          rotK_testBit hkpos hw0_lt _ j (by omega),
          rotK_testBit hkpos (rotK_lt _ _) _ j (by omega),
          hstart_eq, Nat.mod_eq_of_lt (by omega : 2 * r - 2 < k)]
        set bp := (j + k - (2 * r - 2)) % k
        apply hcol.2.1 bp
        by_cases hj1 : j < 2 * r - 2
        · right
          have hbp : bp = j + k - (2 * r - 2) := Nat.mod_eq_of_lt (by omega)
          rw [hbp]; omega
        · left
          have hbp : bp = j - (2 * r - 2) := by
            dsimp only [bp]
            have h1 : j + k - (2 * r - 2) = (j - (2 * r - 2)) + k := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hbp]
          dsimp only [swOf, uOf, extraOf] at *; omega
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_false hj, Bool.false_and, Bool.false_and]
  have hun_zero : ∀ j < unusedOf k r, w0.testBit (4 * r - 3 + j) = false := by
    intro j hj
    have hun_pos : 0 < unusedOf k r := by omega
    have hkgt : 5 * r - 2 ≤ k := by dsimp only [unusedOf, zOf, hOf] at *; omega
    dsimp only [w0, decodeSeed]
    rw [hcol.2.1 (4 * r - 3 + j) (Or.inl (by dsimp only [unusedOf, rowLenOf, colLenOf, uOf, zOf, hOf, extraOf] at *; omega))]
    exact init_mid_false hr hkgt hlabel
      (by dsimp only [unusedOf, extraOf, zOf, hOf] at *; omega)
      (by dsimp only [unusedOf, zOf, hOf] at *; omega)
  have hrowP_eq : cutK (stateN k r c false w0 leftName r) (k - rowLenOf k r) (rowLenOf k r) =
      cutK a (hOf k - rowLenOf k r) (rowLenOf k r) := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < rowLenOf k r
    · rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj]
      have hrl_pos : 0 < rowLenOf k r := by omega
      have hrl_le_h : rowLenOf k r ≤ hOf k := Nat.min_le_left _ _
      have hrl_le_ku : rowLenOf k r ≤ k - uOf r := Nat.min_le_right _ _
      have hhk_le : hOf k ≤ k := by dsimp only [hOf]; omega
      have hzk : zOf k = k - hOf k := rfl
      have hu_eq : uOf r = 5 * r - 3 := rfl
      have hkgt : 5 * r - 2 ≤ k := by omega
      set m' := rowLenOf k r - 1 - j
      have hm' : m' < rowLenOf k r := by omega
      have hi_eq : k - rowLenOf k r + j = k - (m' + 1) := by omega
      have ha_eq : hOf k - rowLenOf k r + j = k - (m' + 1) - zOf k := by omega
      rw [hi_eq, ha_eq, ← hrow.2.2 m' hm']
      set i' := k - (m' + 1)
      have hi'_lt : i' < k := by dsimp only [i']; omega
      have hstep_r : ∀ key : Nat,
          stateN k r c false key leftName r =
          stepK k r c false key (stateN k r c false key leftName (r - 1)) r := by
        intro key
        have hr_eq : r = (r - 1) + 1 := by omega
        conv_lhs => arg 7; rw [hr_eq]
        rw [stateN_succ, ← hr_eq]
      have hsw_eq : swOf k r = 5 * r - 3 + extraOf k r := by
        dsimp only [swOf, uOf]; omega
      have hagree_top : ∀ bp, (bp < 3 * r - 1 + extraOf k r ∨ k - (2 * r - 2) - rowLenOf k r ≤ bp) →
          w0.testBit bp = wR.testBit bp := by
        intro bp hbp
        rcases hbp with hlo | hhi
        · dsimp only [w0, decodeSeed, wR]
          rw [hcol.2.1 bp (Or.inl (by omega)), hrow.2.1 bp (Or.inl (by omega))]
        · exact hcol.2.2.1 bp hhi
      have hcone : AgreeCyc k w0 wR (i' + k - (2 * r - 3)) (5 * r - 3) := by
        intro d hd
        set p' := k - (2 * r - 2) - (m' + 1)
        have hidx : (i' + k - (2 * r - 3) + d) % k = (p' + 1 + d) % k := by
          have h1 : i' + k - (2 * r - 3) + d = (p' + 1 + d) + k := by
            dsimp only [p', i']; omega
          rw [h1, Nat.add_mod_right]
        rw [hidx]
        by_cases hwrap : p' + 1 + d < k
        · rw [Nat.mod_eq_of_lt hwrap]
          exact hagree_top _ (Or.inr (by dsimp only [p']; omega))
        · have hmod : (p' + 1 + d) % k = p' + 1 + d - k := by
            have h1 : p' + 1 + d = (p' + 1 + d - k) + k := by omega
            conv_lhs => rw [h1]
            rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p']; omega)]
          rw [hmod]
          exact hagree_top _ (Or.inl (by dsimp only [p']; omega))
      have hcm := row_final_chimix_congr hr hkgt c hleft hw0_lt hrow.1 i' hi'_lt hcone
      rw [hstep_r w0, hstep_r wR]
      dsimp only [stepK]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, hcm,
        rotK_testBit hkpos hw0_lt _ i' hi'_lt, rotK_testBit hkpos hrow.1 _ i' hi'_lt,
        Nat.mod_eq_of_lt (by omega : 2 * (r - 1) < k)]
      have hp'_idx : (i' + k - 2 * (r - 1)) % k = k - (2 * r - 2) - (m' + 1) := by
        have h1 : i' + k - 2 * (r - 1) = (k - (2 * r - 2) - (m' + 1)) + k := by
          dsimp only [i']; omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hbit_eq : w0.testBit (k - (2 * r - 2) - (m' + 1)) = wR.testBit (k - (2 * r - 2) - (m' + 1)) :=
        hcol.2.2.1 _ (by omega)
      rw [hp'_idx, hbit_eq]
    · dsimp only [cutK]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
        decide_eq_false hj, Bool.false_and, Bool.false_and]
  have hcolP_eq : cutK (stateN k r c true w0 rightName r) (zOf k + (r + 3) - colLenOf k r) (colLenOf k r) =
      cutK b (r + 3 - colLenOf k r) (colLenOf k r) := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < colLenOf k r
    · rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj]
      set m' := colLenOf k r - 1 - j
      have hm' : m' < colLenOf k r := by omega
      have hcl_le : colLenOf k r ≤ r + 3 := Nat.min_le_left _ _
      have hi_eq : zOf k + (r + 3) - colLenOf k r + j = zOf k + (r + 3) - (m' + 1) := by omega
      have hb_eq : r + 3 - colLenOf k r + j = zOf k + (r + 3) - (m' + 1) - zOf k := by omega
      rw [hi_eq, hb_eq]
      exact hcol.2.2.2 m' hm'
    · dsimp only [cutK]
      rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
        decide_eq_false hj, Bool.false_and, Bool.false_and]
  exact ⟨hw0_lt, hseed_eq, hun_zero, hrowP_eq, hcolP_eq⟩

def packBits {L : Nat} (s : Fin L → Bool) : Nat :=
  (List.finRange L).foldl (fun acc j => acc ||| ((s j).toNat <<< j.val)) 0

lemma packBits_spec {L : Nat} (s : Fin L → Bool) :
    packBits s < 2 ^ L ∧ ∀ j : Fin L, (packBits s).testBit j.val = s j := by
  have htake : ∀ m (hm : m ≤ L),
      let v := ((List.finRange L).take m).foldl (fun acc j => acc ||| ((s j).toNat <<< j.val)) 0
      (∀ b, m ≤ b → v.testBit b = false) ∧ (∀ (b : Nat) (hb : b < m), v.testBit b = s ⟨b, by omega⟩) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ _ => by simp, fun _ hb => by omega⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hlen : m < (List.finRange L).length := by simp; omega
      have htake_succ : (List.finRange L).take (m + 1) =
          (List.finRange L).take m ++ [(List.finRange L)[m]'hlen] := List.take_succ_eq_append_getElem hlen
      have hget : (List.finRange L)[m]'hlen = ⟨m, by omega⟩ := by
        apply Fin.ext; simp
      dsimp only
      rw [htake_succ, hget, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hprev.1 b (by omega)]
        have hlt2 : (s ⟨m, by omega⟩).toNat < 2 ^ (b - m) := by
          have hle1 : (s ⟨m, by omega⟩).toNat ≤ 1 := by cases s ⟨m, by omega⟩ <;> decide
          have hpow : 2 ≤ 2 ^ (b - m) := Nat.le_self_pow (by omega) 2
          omega
        rw [decide_eq_true (by omega : m ≤ b), Bool.true_and, Nat.testBit_eq_false_of_lt hlt2, Bool.or_false]
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
        by_cases hbm : b < m
        · rw [hprev.2 b hbm, decide_eq_false (by omega : ¬ m ≤ b), Bool.false_and, Bool.or_false]
        · have hbe : b = m := by omega
          subst hbe
          rw [hprev.1 b (le_refl _), decide_eq_true (le_refl _), Bool.true_and, Bool.false_or, Nat.sub_self]
          cases s ⟨b, by omega⟩ <;> decide
  have hfull := htake L le_rfl
  rw [List.take_of_length_le (by simp)] at hfull
  refine ⟨?_, fun j => hfull.2 j.val j.isLt⟩
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  exact hfull.1 b hb

def fiberWord (k r : Nat) (c : Nat → Fin (2 ^ k)) (leftName rightName a b label : Nat)
    (s : Fin (unusedOf k r) → Bool) : Nat :=
  decodeSeed k r c leftName rightName a b label ^^^ (packBits s <<< (4 * r - 3))

lemma fiberWord_seed_cut {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) (a b : Nat) {leftName rightName label : Nat}
    (hleft : leftName < 2 ^ k) (hright : rightName < 2 ^ k) (hlabel : label < 2 ^ swOf k r)
    (s : Fin (unusedOf k r) → Bool) :
    let w := fiberWord k r c leftName rightName a b label s
    w < 2 ^ k ∧
    seedOf k r w = label ∧
    (∀ j : Fin (unusedOf k r), w.testBit (4 * r - 3 + j.val) = s j) ∧
    (∀ bp, (bp < 4 * r - 3 ∨ 4 * r - 3 + unusedOf k r ≤ bp) →
      w.testBit bp = (decodeSeed k r c leftName rightName a b label).testBit bp) := by
  have hsum := dims_sum k r hr
  have hdec := decodeSeed_spec hr hkpos c a b hleft hright hlabel
  have hpk := packBits_spec s
  have hinv := inv_part hr c hleft hright hdec.1 hpk.1
  set w0 := decodeSeed k r c leftName rightName a b label
  set w := fiberWord k r c leftName rightName a b label s
  have hw_lt : w < 2 ^ k := hinv.1
  have hout : ∀ bp, (bp < 4 * r - 3 ∨ 4 * r - 3 + unusedOf k r ≤ bp) →
      w.testBit bp = w0.testBit bp := by
    intro bp hbp
    dsimp only [w, fiberWord]
    rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
    rcases hbp with hlo | hhi
    · rw [decide_eq_false (by omega : ¬ (4 * r - 3 ≤ bp)), Bool.false_and, Bool.xor_false]
    · have hfalse : (packBits s).testBit (bp - (4 * r - 3)) = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hpk.1 (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
      rw [decide_eq_true (by omega : 4 * r - 3 ≤ bp), Bool.true_and, hfalse, Bool.xor_false]
  have hin : ∀ j : Fin (unusedOf k r), w.testBit (4 * r - 3 + j.val) = s j := by
    intro j
    dsimp only [w, fiberWord]
    rw [Nat.testBit_xor, hdec.2.2.1 j.val j.isLt, Bool.false_xor, Nat.testBit_shiftLeft,
      decide_eq_true (by omega : 4 * r - 3 ≤ 4 * r - 3 + j.val), Bool.true_and,
      Nat.add_sub_cancel_left, hpk.2 j]
  have hseed : seedOf k r w = label := by
    by_cases hun0 : unusedOf k r = 0
    · have hpk0 : packBits s = 0 := by
        have h1 : 2 ^ unusedOf k r = 1 := by rw [hun0]; rfl
        have := hpk.1; omega
      have hweq : w = w0 := by dsimp only [w, fiberWord, w0]; rw [hpk0]; simp
      rw [hweq]; exact hdec.2.1
    · have hun_pos : 0 < unusedOf k r := by omega
      have hkgt : 5 * r - 2 ≤ k := by dsimp only [unusedOf, zOf, hOf] at *; omega
      have hstart_lt : startOf k r < k := by dsimp only [startOf]; omega
      have hstart_eq : k - startOf k r % k = 2 * r - 2 := by
        rw [Nat.mod_eq_of_lt hstart_lt]; dsimp only [startOf]; omega
      rw [← hdec.2.1]
      apply Nat.eq_of_testBit_eq
      intro j
      dsimp only [seedOf]
      by_cases hj : j < swOf k r
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_true hj, Bool.true_and, Bool.true_and,
          rotK_testBit hkpos hw_lt _ j (by omega),
          rotK_testBit hkpos hdec.1 _ j (by omega),
          hstart_eq, Nat.mod_eq_of_lt (by omega : 2 * r - 2 < k)]
        set bp := (j + k - (2 * r - 2)) % k
        apply hout bp
        by_cases hj1 : j < 2 * r - 2
        · right
          have hbp : bp = j + k - (2 * r - 2) := Nat.mod_eq_of_lt (by omega)
          rw [hbp]; dsimp only [unusedOf, zOf, hOf] at *; omega
        · left
          have hbp : bp = j - (2 * r - 2) := by
            dsimp only [bp]
            have h1 : j + k - (2 * r - 2) = (j - (2 * r - 2)) + k := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hbp]; dsimp only [swOf, uOf, extraOf] at *; omega
      · rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_false hj, Bool.false_and, Bool.false_and]
  exact ⟨hw_lt, hseed, hin, hout⟩

lemma fiberWord_inj {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) {leftName rightName a b : Nat}
    (hleft : leftName < 2 ^ k) (hright : rightName < 2 ^ k)
    {l1 l2 : Fin (2 ^ swOf k r)} {s1 s2 : Fin (unusedOf k r) → Bool}
    (h : fiberWord k r c leftName rightName a b l1.val s1 =
         fiberWord k r c leftName rightName a b l2.val s2) :
    l1 = l2 ∧ s1 = s2 := by
  have h1 := fiberWord_seed_cut hr hkpos c a b hleft hright l1.isLt s1
  have h2 := fiberWord_seed_cut hr hkpos c a b hleft hright l2.isLt s2
  have hl : l1 = l2 := Fin.ext (by rw [← h1.2.1, ← h2.2.1, h])
  have hs : s1 = s2 := by
    funext j
    rw [← h1.2.2.1 j, ← h2.2.2.1 j, h]
  exact ⟨hl, hs⟩

lemma targets_iff_fiberWord {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) {leftName rightName a b w : Nat}
    (hleft : leftName < 2 ^ k) (hright : rightName < 2 ^ k)
    (hw : w < 2 ^ k) :
    (stateN k r c false w leftName r >>> zOf k = a ∧
     stateN k r c true w rightName r >>> zOf k = b) ↔
    ∃ (label : Fin (2 ^ swOf k r)) (s : Fin (unusedOf k r) → Bool),
      w = fiberWord k r c leftName rightName a b label.val s ∧
      stateN k r c false (decodeSeed k r c leftName rightName a b label.val) leftName r >>> zOf k = a ∧
      stateN k r c true (decodeSeed k r c leftName rightName a b label.val) rightName r >>> zOf k = b := by
  constructor
  · rintro ⟨ha, hb⟩
    let label : Fin (2 ^ swOf k r) := ⟨seedOf k r w, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
    let s : Fin (unusedOf k r) → Bool := fun j => w.testBit (4 * r - 3 + j.val)
    have hdec := decodeSeed_spec hr hkpos c a b hleft hright label.isLt
    have hfw := fiberWord_seed_cut hr hkpos c a b hleft hright label.isLt s
    have hpk := packBits_spec s
    have hinv := inv_part hr c hleft hright hdec.1 hpk.1
    set w' := fiberWord k r c leftName rightName a b label.val s
    have hcut_spare : cutK w' (4 * r - 3) (unusedOf k r) = cutK w (4 * r - 3) (unusedOf k r) := by
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < unusedOf k r
      · rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj]
        exact hfw.2.2.1 ⟨j, hj⟩
      · dsimp only [cutK]
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_false hj, Bool.false_and, Bool.false_and]
    have hrow_eq : cutK (stateN k r c false w' leftName r) (k - rowLenOf k r) (rowLenOf k r) =
        cutK (stateN k r c false w leftName r) (k - rowLenOf k r) (rowLenOf k r) := by
      have hsh : stateN k r c false w' leftName r >>> zOf k =
          stateN k r c false (decodeSeed k r c leftName rightName a b label.val) leftName r >>> zOf k :=
        hinv.2.1.symm
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < rowLenOf k r
      · rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj]
        have hge : zOf k ≤ k - rowLenOf k r + j := by dsimp only [zOf, hOf, rowLenOf] at *; omega
        have hidx : k - rowLenOf k r + j = zOf k + (k - rowLenOf k r + j - zOf k) := by omega
        rw [hidx, ← Nat.testBit_shiftRight, ← Nat.testBit_shiftRight, hsh, ha, Nat.testBit_shiftRight, ← hidx]
        have h1 := congrArg (fun n => n.testBit j) hdec.2.2.2.1
        rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at h1
        rw [h1]
        congr 1; dsimp only [zOf, hOf, rowLenOf] at *; omega
      · dsimp only [cutK]
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_false hj, Bool.false_and, Bool.false_and]
    have hcol_eq : cutK (stateN k r c true w' rightName r) (zOf k + (r + 3) - colLenOf k r) (colLenOf k r) =
        cutK (stateN k r c true w rightName r) (zOf k + (r + 3) - colLenOf k r) (colLenOf k r) := by
      have hsh : stateN k r c true w' rightName r >>> zOf k =
          stateN k r c true (decodeSeed k r c leftName rightName a b label.val) rightName r >>> zOf k :=
        hinv.2.2.symm
      apply Nat.eq_of_testBit_eq
      intro j
      by_cases hj : j < colLenOf k r
      · rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj]
        have hidx : zOf k + (r + 3) - colLenOf k r + j = zOf k + (r + 3 - colLenOf k r + j) := by
          have hcl_le : colLenOf k r ≤ r + 3 := Nat.min_le_left _ _
          omega
        have h1 := congrArg (fun n => n.testBit j) hdec.2.2.2.2
        rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at h1
        have hL : (stateN k r c true w' rightName r).testBit (zOf k + (r + 3) - colLenOf k r + j) =
            (stateN k r c true w' rightName r >>> zOf k).testBit (r + 3 - colLenOf k r + j) := by
          rw [Nat.testBit_shiftRight, hidx]
        have hR : (stateN k r c true w rightName r).testBit (zOf k + (r + 3) - colLenOf k r + j) =
            (stateN k r c true w rightName r >>> zOf k).testBit (r + 3 - colLenOf k r + j) := by
          rw [Nat.testBit_shiftRight, hidx]
        rw [hL, hR, hsh, hb, Nat.testBit_shiftRight, ← hidx, h1]
      · dsimp only [cutK]
        rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
          decide_eq_false hj, Bool.false_and, Bool.false_and]
    have hw_eq : w' = w :=
      phi_inj hr hkpos c hleft hright hfw.1 hw hfw.2.1 hcut_spare hrow_eq hcol_eq
    refine ⟨label, s, hw_eq.symm, ?_, ?_⟩
    · rw [hinv.2.1]; change stateN k r c false w' leftName r >>> zOf k = a; rw [hw_eq]; exact ha
    · rw [hinv.2.2]; change stateN k r c true w' rightName r >>> zOf k = b; rw [hw_eq]; exact hb
  · rintro ⟨label, s, rfl, ha, hb⟩
    have hdec := decodeSeed_spec hr hkpos c a b hleft hright label.isLt
    have hpk := packBits_spec s
    have hinv := inv_part hr c hleft hright hdec.1 hpk.1
    exact ⟨hinv.2.1.symm.trans ha, hinv.2.2.symm.trans hb⟩

def foldXor {α : Type*} (l : List α) (f : α → Bool) : Bool :=
  l.foldl (fun acc a => xor acc (f a)) false

lemma foldXor_init {α : Type*} (l : List α) (f : α → Bool) (init : Bool) :
    l.foldl (fun acc a => xor acc (f a)) init = xor init (foldXor l f) := by
  induction l generalizing init with
  | nil => simp [foldXor]
  | cons a t ih =>
    simp only [foldXor, List.foldl_cons, Bool.false_xor]
    rw [ih (xor init (f a)), ih (f a), Bool.xor_assoc]

lemma foldXor_cons {α : Type*} (a : α) (l : List α) (f : α → Bool) :
    foldXor (a :: l) f = xor (f a) (foldXor l f) := by
  dsimp only [foldXor]
  rw [List.foldl_cons, Bool.false_xor, foldXor_init]; rfl

lemma foldXor_append {α : Type*} (l1 l2 : List α) (f : α → Bool) :
    foldXor (l1 ++ l2) f = xor (foldXor l1 f) (foldXor l2 f) := by
  dsimp only [foldXor]
  rw [List.foldl_append, foldXor_init]; rfl

lemma foldXor_map {α β : Type*} (l : List α) (g : α → β) (f : β → Bool) :
    foldXor (l.map g) f = foldXor l (fun x => f (g x)) := by
  induction l with
  | nil => rfl
  | cons x t ih => rw [List.map_cons, foldXor_cons, foldXor_cons, ih]

lemma foldXor_congr {α : Type*} {l : List α} {f g : α → Bool} (h : ∀ a ∈ l, f a = g a) :
    foldXor l f = foldXor l g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [foldXor_cons, foldXor_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

lemma foldXor_false {α : Type*} (l : List α) :
    foldXor l (fun _ => false) = false := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [foldXor_cons, ih]; rfl

lemma foldXor_xor {α : Type*} (l : List α) (f g : α → Bool) :
    foldXor l (fun a => xor (f a) (g a)) = xor (foldXor l f) (foldXor l g) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [foldXor_cons, foldXor_cons, foldXor_cons, ih]
    cases f a <;> cases g a <;> cases foldXor t f <;> cases foldXor t g <;> rfl

lemma foldXor_and {α : Type*} (l : List α) (s : Bool) (f : α → Bool) :
    foldXor l (fun a => s && f a) = (s && foldXor l f) := by
  cases s with
  | false => simpa using foldXor_false l
  | true => simp [foldXor]

lemma foldXor_single {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {x : α} (hx : x ∈ l) {f : α → Bool} (hzero : ∀ a ∈ l, a ≠ x → f a = false) :
    foldXor l f = f x := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    rw [foldXor_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · have ht0 : foldXor t f = false := by
        rw [foldXor_congr (g := fun _ => false) (fun b hb => hzero b (List.mem_cons_of_mem _ hb) (fun h => hnd.1 (h ▸ hb)))]
        exact foldXor_false t
      rw [ht0, Bool.xor_false]
    · have ha0 : f a = false := hzero a List.mem_cons_self (fun h => hnd.1 (h ▸ hxt))
      rw [ha0, Bool.false_xor]
      exact ih hnd.2 hxt (fun b hb hne => hzero b (List.mem_cons_of_mem a hb) hne)

lemma foldXor_split {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    {x : α} (hx : x ∈ l) (f : α → Bool) :
    foldXor l f = xor (f x) (foldXor l (fun a => if a = x then false else f a)) := by
  have h1 : foldXor l f =
      foldXor l (fun a => xor (if a = x then f a else false) (if a = x then false else f a)) := by
    apply foldXor_congr
    intro a _
    by_cases hax : a = x <;> simp [hax]
  rw [h1, foldXor_xor]
  congr 1
  have hs := foldXor_single hnd hx (f := fun a => if a = x then f a else false) (fun a _ hne => by simp [hne])
  simpa using hs

def firstTrue {n : Nat} (cond : Fin n → Bool) (i : Fin n) : Bool :=
  cond i && !((List.finRange n).filter (fun j => decide (j.val < i.val)) |>.any cond)

lemma firstTrue_spec {n : Nat} (cond : Fin n → Bool) (i : Fin n) :
    firstTrue cond i = true ↔ cond i = true ∧ ∀ j : Fin n, j.val < i.val → cond j = false := by
  unfold firstTrue
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_false, List.mem_filter,
    List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by have := h2 j hj; cases h : cond j <;> simp_all⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun j hj => by simp [h2 j hj]⟩

lemma firstTrue_unique {n : Nat} (cond : Fin n → Bool) {i j : Fin n}
    (hi : firstTrue cond i = true) (hj : firstTrue cond j = true) : i = j := by
  have hi' := (firstTrue_spec cond i).mp hi
  have hj' := (firstTrue_spec cond j).mp hj
  by_contra hne
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · have := hj'.2 i hlt; rw [hi'.1] at this; exact Bool.noConfusion this
  · have := hi'.2 j hgt; rw [hj'.1] at this; exact Bool.noConfusion this

lemma exists_firstTrue_iff {n : Nat} (cond : Fin n → Bool) :
    (∃ i : Fin n, firstTrue cond i = true) ↔ (∃ i : Fin n, cond i = true) := by
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i, ((firstTrue_spec cond i).mp hi).1⟩
  · rintro ⟨i0, hi0⟩
    classical
    have hex : ∃ k : Nat, ∃ h : k < n, cond ⟨k, h⟩ = true := ⟨i0.val, i0.isLt, hi0⟩
    let k := Nat.find hex
    rcases Nat.find_spec hex with ⟨hk, hcond⟩
    refine ⟨⟨k, hk⟩, (firstTrue_spec cond ⟨k, hk⟩).mpr ⟨hcond, ?_⟩⟩
    intro j hj
    by_contra hne
    have hjtrue : cond j = true := by cases h : cond j <;> simp_all
    exact Nat.find_min hex hj ⟨j.isLt, hjtrue⟩

def bDot {L : Nat} (u v : Fin L → Bool) : Bool :=
  (List.finRange L).foldl (fun acc j => xor acc (u j && v j)) false

lemma bDot_eq_foldXor {L : Nat} (u v : Fin L → Bool) :
    bDot u v = foldXor (List.finRange L) (fun j => u j && v j) := rfl

lemma bDot_xor_left {L : Nat} (u1 u2 v : Fin L → Bool) :
    bDot (fun j => xor (u1 j) (u2 j)) v = xor (bDot u1 v) (bDot u2 v) := by
  rw [bDot_eq_foldXor, bDot_eq_foldXor, bDot_eq_foldXor, ← foldXor_xor]
  apply foldXor_congr
  intro j _
  cases u1 j <;> cases u2 j <;> cases v j <;> rfl

lemma bDot_and_left {L : Nat} (s : Bool) (u v : Fin L → Bool) :
    bDot (fun j => s && u j) v = (s && bDot u v) := by
  rw [bDot_eq_foldXor, bDot_eq_foldXor, ← foldXor_and]
  apply foldXor_congr
  intro j _
  cases s <;> cases u j <;> cases v j <;> rfl

lemma bDot_false_left {L : Nat} (v : Fin L → Bool) :
    bDot (fun _ => false) v = false := by
  rw [bDot_eq_foldXor]
  simpa using foldXor_false (List.finRange L)

lemma bDot_unit_left {L : Nat} (r : Fin L) (v : Fin L → Bool) :
    bDot (fun i => decide (r = i)) v = v r := by
  rw [bDot_eq_foldXor]
  have hs := foldXor_single (List.nodup_finRange L) (List.mem_finRange r)
    (f := fun i => decide (r = i) && v i) (fun a _ hne => by simp [Ne.symm hne])
  simpa using hs

abbrev GState (m C : Nat) := (Fin m → Bool) × (Fin m → Fin C → Bool) × (Fin m → Fin m → Bool)

def gStep {m C : Nat} (col : Nat) (st : GState m C) : GState m C :=
  if hcol : col < C then
    let c0 : Fin C := ⟨col, hcol⟩
    let cond : Fin m → Bool := fun r => !(st.1 r) && st.2.1 r c0
    let isPiv : Fin m → Bool := firstTrue cond
    let pivM : Fin C → Bool := fun c => (List.finRange m).any (fun r => isPiv r && st.2.1 r c)
    let pivP : Fin m → Bool := fun i => (List.finRange m).any (fun r => isPiv r && st.2.2 r i)
    (fun r => st.1 r || isPiv r,
     fun r c => xor (st.2.1 r c) ((!(isPiv r) && st.2.1 r c0) && pivM c),
     fun r i => xor (st.2.2 r i) ((!(isPiv r) && st.2.1 r c0) && pivP i))
  else st

def gElim {m C : Nat} (M0 : Fin m → Fin C → Bool) : GState m C :=
  (List.range C).foldl (fun st col => gStep col st)
    (fun _ => false, M0, fun r i => decide (r = i))

lemma gStep_spec {m C : Nat} (col : Nat) (hcol : col < C) (st : GState m C) :
    let c0 : Fin C := ⟨col, hcol⟩
    let cond : Fin m → Bool := fun r => !(st.1 r) && st.2.1 r c0
    let st' := gStep col st
    (∀ r, st'.1 r = true ↔ st.1 r = true ∨ firstTrue cond r = true) ∧
    ((∀ r, cond r = false) → st' = st) ∧
    (∀ p0, firstTrue cond p0 = true →
      st'.2.1 p0 = st.2.1 p0 ∧ st'.2.2 p0 = st.2.2 p0 ∧
      ∀ r, r ≠ p0 →
        st'.2.1 r = (fun c => xor (st.2.1 r c) (st.2.1 r c0 && st.2.1 p0 c)) ∧
        st'.2.2 r = (fun i => xor (st.2.2 r i) (st.2.1 r c0 && st.2.2 p0 i))) := by
  intro c0 cond st'
  have hst' : st' =
      let isPiv : Fin m → Bool := firstTrue cond
      let pivM : Fin C → Bool := fun c => (List.finRange m).any (fun r => isPiv r && st.2.1 r c)
      let pivP : Fin m → Bool := fun i => (List.finRange m).any (fun r => isPiv r && st.2.2 r i)
      (fun r => st.1 r || isPiv r,
       fun r c => xor (st.2.1 r c) ((!(isPiv r) && st.2.1 r c0) && pivM c),
       fun r i => xor (st.2.2 r i) ((!(isPiv r) && st.2.1 r c0) && pivP i)) := by
    simp only [st', gStep, hcol, ↓reduceDIte, c0, cond]
  refine ⟨?_, ?_, ?_⟩
  · intro r; rw [hst']; simp
  · intro hnone
    have hnoPiv : ∀ r, firstTrue cond r = false := by
      intro r
      cases h : firstTrue cond r
      · rfl
      · have := ((firstTrue_spec cond r).mp h).1; rw [hnone r] at this; exact Bool.noConfusion this
    rw [hst']
    rcases st with ⟨u, M, P⟩
    refine Prod.ext (funext fun r => by simp [hnoPiv r]) (Prod.ext ?_ ?_)
    · funext r c
      have hany : ((List.finRange m).any (fun r' => firstTrue cond r' && M r' c)) = false := by
        rw [List.any_eq_false]; intro r' _; simp [hnoPiv r']
      change xor (M r c) ((!(firstTrue cond r) && M r c0) && ((List.finRange m).any (fun r' => firstTrue cond r' && M r' c))) = M r c
      rw [hany, Bool.and_false, Bool.xor_false]
    · funext r i
      have hany : ((List.finRange m).any (fun r' => firstTrue cond r' && P r' i)) = false := by
        rw [List.any_eq_false]; intro r' _; simp [hnoPiv r']
      change xor (P r i) ((!(firstTrue cond r) && M r c0) && ((List.finRange m).any (fun r' => firstTrue cond r' && P r' i))) = P r i
      rw [hany, Bool.and_false, Bool.xor_false]
  · intro p0 hp0
    have huniq : ∀ r, firstTrue cond r = true ↔ r = p0 := fun r =>
      ⟨fun h => firstTrue_unique cond h hp0, fun h => h ▸ hp0⟩
    have hpivM : ∀ c, ((List.finRange m).any (fun r => firstTrue cond r && st.2.1 r c)) = st.2.1 p0 c := by
      intro c
      cases h : st.2.1 p0 c
      · rw [List.any_eq_false]
        intro r _
        by_cases hr : r = p0
        · subst hr; simp [h]
        · have hf : firstTrue cond r = false := by
            cases h' : firstTrue cond r
            · rfl
            · exact absurd ((huniq r).mp h') hr
          simp [hf]
      · rw [List.any_eq_true]
        exact ⟨p0, List.mem_finRange p0, by simp [hp0, h]⟩
    have hpivP : ∀ i, ((List.finRange m).any (fun r => firstTrue cond r && st.2.2 r i)) = st.2.2 p0 i := by
      intro i
      cases h : st.2.2 p0 i
      · rw [List.any_eq_false]
        intro r _
        by_cases hr : r = p0
        · subst hr; simp [h]
        · have hf : firstTrue cond r = false := by
            cases h' : firstTrue cond r
            · rfl
            · exact absurd ((huniq r).mp h') hr
          simp [hf]
      · rw [List.any_eq_true]
        exact ⟨p0, List.mem_finRange p0, by simp [hp0, h]⟩
    rw [hst']
    refine ⟨funext fun c => by simp [hp0], funext fun i => by simp [hp0], ?_⟩
    intro r hr
    have hrf : firstTrue cond r = false := by
      cases h' : firstTrue cond r
      · rfl
      · exact absurd ((huniq r).mp h') hr
    exact ⟨funext fun c => by simp [hrf, hpivM], funext fun i => by simp [hrf, hpivP]⟩

lemma gElim_invariants {m C : Nat} (M0 : Fin m → Fin C → Bool) :
    let st := gElim M0
    (∀ (b : Fin m → Bool) (x : Fin C → Bool),
      (∀ r : Fin m, bDot (st.2.1 r) x = bDot (st.2.2 r) b) ↔ (∀ i : Fin m, bDot (M0 i) x = b i)) ∧
    (∀ r, st.1 r = true → ∃ c : Fin C, st.2.1 r c = true ∧ ∀ j, j ≠ r → st.2.1 j c = false) ∧
    (∀ r, st.1 r = false → ∀ c : Fin C, st.2.1 r c = false) := by
  have hloop : ∀ t ≤ C,
      let st := (List.range t).foldl (fun s col => gStep col s) (fun _ => false, M0, fun r i => decide (r = i))
      (∀ (b : Fin m → Bool) (x : Fin C → Bool),
        (∀ r : Fin m, bDot (st.2.1 r) x = bDot (st.2.2 r) b) ↔ (∀ i : Fin m, bDot (M0 i) x = b i)) ∧
      (∀ r, st.1 r = true → ∃ c : Fin C, c.val < t ∧ st.2.1 r c = true ∧ ∀ j, j ≠ r → st.2.1 j c = false) ∧
      (∀ r, st.1 r = false → ∀ c : Fin C, c.val < t → st.2.1 r c = false) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨?_, fun _ h => Bool.noConfusion h, fun _ _ _ hc => by omega⟩
      intro b x
      constructor <;> (intro hall r; simpa [bDot_unit_left] using hall r)
    | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨heqv, hpiv, hzero⟩
      let st := (List.range t).foldl (fun s col => gStep col s) (fun _ => false, M0, fun r i => decide (r = i))
      have hnext : (List.range (t + 1)).foldl (fun s col => gStep col s)
          (fun _ => false, M0, fun r i => decide (r = i)) = gStep t st := by
        simp [List.range_succ, List.foldl_append, st]
      rw [hnext]
      have hcol : t < C := by omega
      let c0 : Fin C := ⟨t, hcol⟩
      let cond : Fin m → Bool := fun r => !(st.1 r) && st.2.1 r c0
      rcases gStep_spec t hcol st with ⟨hused, hnone, hsome⟩
      by_cases hex : ∃ r : Fin m, cond r = true
      · rcases (exists_firstTrue_iff cond).mpr hex with ⟨p0, hp0⟩
        rcases hsome p0 hp0 with ⟨hMp0, hPp0, hother⟩
        have hp0_cond := ((firstTrue_spec cond p0).mp hp0).1
        have hp0_unused : st.1 p0 = false := by
          simp only [cond, Bool.and_eq_true, Bool.not_eq_true'] at hp0_cond; exact hp0_cond.1
        have hp0_one : st.2.1 p0 c0 = true := by
          simp only [cond, Bool.and_eq_true] at hp0_cond; exact hp0_cond.2
        refine ⟨?_, ?_, ?_⟩
        · intro b x
          rw [← heqv b x]
          constructor
          · intro hall r
            by_cases hr : r = p0
            · subst hr; rw [← hMp0, ← hPp0]; exact hall r
            · have h1 := hall r
              have h2 := hall p0
              rw [(hother r hr).1, (hother r hr).2, bDot_xor_left, bDot_xor_left,
                bDot_and_left, bDot_and_left] at h1
              rw [hMp0, hPp0] at h2
              rw [h2] at h1
              revert h1
              generalize bDot (st.2.1 r) x = a1
              generalize bDot (st.2.2 r) b = a2
              generalize (st.2.1 r c0 && bDot (st.2.2 p0) b) = a3
              cases a1 <;> cases a2 <;> cases a3 <;> decide
          · intro hall r
            by_cases hr : r = p0
            · subst hr; rw [hMp0, hPp0]; exact hall r
            · rw [(hother r hr).1, (hother r hr).2, bDot_xor_left, bDot_xor_left,
                bDot_and_left, bDot_and_left, hall r, hall p0]
        · intro r hr
          rcases (hused r).mp hr with hr_old | hr_new
          · rcases hpiv r hr_old with ⟨c, hct, hrc1, hoth⟩
            have hp0_ne : p0 ≠ r := fun h => by rw [h, hr_old] at hp0_unused; exact Bool.noConfusion hp0_unused
            have hp0c0 : st.2.1 p0 c = false := hoth p0 hp0_ne
            refine ⟨c, by omega, ?_, ?_⟩
            · have hrp0 : r ≠ p0 := Ne.symm hp0_ne
              have := congrFun (hother r hrp0).1 c
              rw [this, hp0c0, Bool.and_false, Bool.xor_false, hrc1]
            · intro j hj
              by_cases hjp0 : j = p0
              · subst hjp0; rw [hMp0]; exact hp0c0
              · have := congrFun (hother j hjp0).1 c
                rw [this, hp0c0, Bool.and_false, Bool.xor_false, hoth j hj]
          · have hrp0 : r = p0 := firstTrue_unique cond hr_new hp0
            subst hrp0
            refine ⟨c0, by simp [c0], by rw [hMp0]; exact hp0_one, ?_⟩
            intro j hj
            have := congrFun (hother j hj).1 c0
            rw [this, hp0_one, Bool.and_true, Bool.xor_self]
        · intro r hr c hc
          have hr_old : st.1 r = false := by
            cases hu : st.1 r
            · rfl
            · have := (hused r).mpr (Or.inl hu); rw [hr] at this; exact Bool.noConfusion this
          have hr_ne : r ≠ p0 := by
            intro h; subst h
            have := (hused r).mpr (Or.inr hp0); rw [hr] at this; exact Bool.noConfusion this
          have hm := congrFun (hother r hr_ne).1 c
          by_cases hct : c.val < t
          · rw [hm, hzero r hr_old c hct, hzero p0 hp0_unused c hct, Bool.and_false, Bool.xor_false]
          · have hce : c = c0 := Fin.ext (by dsimp [c0]; omega)
            subst hce
            rw [hm, hp0_one, Bool.and_true, Bool.xor_self]
      · push Not at hex
        have hallf : ∀ r, cond r = false := fun r => by
          cases h : cond r
          · rfl
          · exact absurd h (hex r)
        rw [hnone hallf]
        refine ⟨heqv, ?_, ?_⟩
        · intro r hr
          rcases hpiv r hr with ⟨c, hct, h1, h2⟩
          exact ⟨c, by omega, h1, h2⟩
        · intro r hr c hc
          by_cases hct : c.val < t
          · exact hzero r hr c hct
          · have hce : c = c0 := Fin.ext (by dsimp [c0]; omega)
            subst hce
            have hcf := hallf r
            simp only [cond, hr, Bool.not_false, Bool.true_and] at hcf
            exact hcf
  rcases hloop C le_rfl with ⟨heqv, hpiv, hzero⟩
  exact ⟨heqv, fun r hr => let ⟨c, _, h1, h2⟩ := hpiv r hr; ⟨c, h1, h2⟩, fun r hr c => hzero r hr c c.isLt⟩

lemma gElim_card_eq {m C : Nat} (M0 : Fin m → Fin C → Bool) (b : Fin m → Bool) :
    let st := gElim M0
    let usedCard := (Finset.univ.filter (fun r : Fin m => st.1 r = true)).card
    usedCard ≤ C ∧
    ((Finset.univ : Finset (Fin C → Bool)).filter (fun s => ∀ i : Fin m, bDot (M0 i) s = b i)).card =
      if (List.finRange m).all (fun r => !(!(st.1 r) && bDot (st.2.2 r) b)) then
        2 ^ (C - usedCard)
      else 0 := by
  classical
  intro st usedCard
  rcases gElim_invariants M0 with ⟨heqv, hpiv, hzero⟩
  let U : Finset (Fin m) := Finset.univ.filter (fun r : Fin m => st.1 r = true)
  let pivCol : U → Fin C := fun r => Classical.choose (hpiv r.val (Finset.mem_filter.mp r.2).2)
  have hpivCol_spec : ∀ r : U, st.2.1 r.val (pivCol r) = true ∧ ∀ j, j ≠ r.val → st.2.1 j (pivCol r) = false :=
    fun r => Classical.choose_spec (hpiv r.val (Finset.mem_filter.mp r.2).2)
  have hpivCol_inj : Function.Injective pivCol := by
    intro r1 r2 h
    by_contra hne
    have hvalne : r1.val ≠ r2.val := fun hv => hne (Subtype.ext hv)
    have h1 := (hpivCol_spec r1).1
    have h2 := (hpivCol_spec r2).2 r1.val hvalne
    rw [h, h2] at h1
    exact Bool.noConfusion h1
  let PivCols : Finset (Fin C) := Finset.univ.image pivCol
  have hPivCard : PivCols.card = usedCard := by
    rw [Finset.card_image_of_injective _ hpivCol_inj, Finset.card_univ, Fintype.card_coe]
  have hused_le : usedCard ≤ C := by
    rw [← hPivCard]
    calc PivCols.card ≤ (Finset.univ : Finset (Fin C)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = C := by simp
  refine ⟨hused_le, ?_⟩
  let S : Finset (Fin C → Bool) :=
    (Finset.univ : Finset (Fin C → Bool)).filter (fun s => ∀ i : Fin m, bDot (M0 i) s = b i)
  have hS_eq : S = (Finset.univ : Finset (Fin C → Bool)).filter
      (fun s => ∀ r : Fin m, bDot (st.2.1 r) s = bDot (st.2.2 r) b) := by
    ext s; simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact (heqv b s).symm
  cases hcons : (List.finRange m).all (fun r => !(!(st.1 r) && bDot (st.2.2 r) b))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hex : ∃ r : Fin m, st.1 r = false ∧ bDot (st.2.2 r) b = true := by
      rw [List.all_eq_false] at hcons
      rcases hcons with ⟨r, _, hr⟩
      cases hu : st.1 r <;> cases hb : bDot (st.2.2 r) b <;> simp [hu, hb] at hr
      exact ⟨r, hu, hb⟩
    rcases hex with ⟨r0, hr0u, hr0b⟩
    have hSem : S = ∅ := by
      rw [hS_eq, Finset.eq_empty_iff_forall_notMem]
      intro s hs
      have hreq := (Finset.mem_filter.mp hs).2 r0
      have hm0 : st.2.1 r0 = fun _ => false := funext (hzero r0 hr0u)
      rw [hm0, bDot_false_left, hr0b] at hreq
      exact Bool.noConfusion hreq
    change S.card = 0
    rw [hSem, Finset.card_empty]
  · simp only [↓reduceIte]
    have hcons_all : ∀ r : Fin m, st.1 r = false → bDot (st.2.2 r) b = false := by
      rw [List.all_eq_true] at hcons
      intro r hr
      have h1 := hcons r (List.mem_finRange r)
      cases hb : bDot (st.2.2 r) b <;> simp [hr, hb] at h1 ⊢
    let FreeCols : Finset (Fin C) := Finset.univ \ PivCols
    have hFreeCard : FreeCols.card = C - usedCard := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hPivCard]
    let fwd : (Fin C → Bool) → (FreeCols → Bool) := fun s c => s c.val
    let bwd : (FreeCols → Bool) → (Fin C → Bool) := fun f c =>
      if hc : c ∈ FreeCols then f ⟨c, hc⟩
      else
        have hcP : c ∈ PivCols := by
          have : c ∈ Finset.univ \ PivCols → False := hc
          simpa using this
        let r : U := Classical.choose (Finset.mem_image.mp hcP)
        xor (bDot (st.2.2 r.val) b)
          (bDot (fun c' => if c' = c then false else st.2.1 r.val c')
            (fun c' => if h' : c' ∈ FreeCols then f ⟨c', h'⟩ else false))
    have hrow_free : ∀ (r : U) (c' : Fin C), c' ≠ pivCol r → st.2.1 r.val c' = true → c' ∈ FreeCols := by
      intro r c' hne htrue
      simp only [FreeCols, Finset.mem_sdiff, Finset.mem_univ, true_and]
      intro hmem
      rcases Finset.mem_image.mp hmem with ⟨r', _, hr'eq⟩
      have hrne : r.val ≠ r'.val := fun hv => hne (by rw [← hr'eq, Subtype.ext hv])
      have h0 := (hpivCol_spec r').2 r.val hrne
      rw [← hr'eq, h0] at htrue
      exact Bool.noConfusion htrue
    have hcard_eq : S.card = (Finset.univ : Finset (FreeCols → Bool)).card := by
      refine Finset.card_nbij' fwd bwd ?_ ?_ ?_ ?_
      · intro s _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
      · intro f _
        rw [Finset.mem_coe, hS_eq, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, fun r => ?_⟩
        by_cases hru : st.1 r = true
        · let rU : U := ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hru⟩⟩
          let c := pivCol rU
          have hcP : c ∈ PivCols := Finset.mem_image.mpr ⟨rU, Finset.mem_univ _, rfl⟩
          have hcNotF : c ∉ FreeCols := by simp [FreeCols, hcP]
          have hchoose : Classical.choose (Finset.mem_image.mp hcP) = rU := by
            have hspec := (Classical.choose_spec (Finset.mem_image.mp hcP)).2
            exact hpivCol_inj hspec
          have hbwd_c : bwd f c = xor (bDot (st.2.2 r) b)
              (bDot (fun c' => if c' = c then false else st.2.1 r c')
                (fun c' => if h' : c' ∈ FreeCols then f ⟨c', h'⟩ else false)) := by
            dsimp only [bwd]
            simp only [hcNotF, ↓reduceDIte, hchoose, rU]
          have hrest_eq : bDot (fun c' => if c' = c then false else st.2.1 r c') (bwd f) =
              bDot (fun c' => if c' = c then false else st.2.1 r c')
                (fun c' => if h' : c' ∈ FreeCols then f ⟨c', h'⟩ else false) := by
            rw [bDot_eq_foldXor, bDot_eq_foldXor]
            apply foldXor_congr
            intro c' _
            by_cases hc' : c' = c
            · simp [hc']
            · cases hm : st.2.1 r c'
              · simp
              · have hcf := hrow_free rU c' hc' hm
                simp [bwd, hcf]
          rw [bDot_eq_foldXor, foldXor_split (List.nodup_finRange C) (List.mem_finRange c),
            (hpivCol_spec rU).1, Bool.true_and]
          have hrest_fold : foldXor (List.finRange C) (fun a => if a = c then false else st.2.1 r a && bwd f a) =
              bDot (fun c' => if c' = c then false else st.2.1 r c') (bwd f) := by
            rw [bDot_eq_foldXor]
            apply foldXor_congr
            intro a _
            by_cases ha : a = c <;> simp [ha]
          rw [hrest_fold, hrest_eq, hbwd_c, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
        · have hrf : st.1 r = false := by cases h : st.1 r <;> simp_all
          have hm0 : st.2.1 r = fun _ => false := funext (hzero r hrf)
          rw [hm0, bDot_false_left, hcons_all r hrf]
      · intro s hs
        rw [Finset.mem_coe, hS_eq, Finset.mem_filter] at hs
        funext c
        by_cases hc : c ∈ FreeCols
        · simp [bwd, fwd, hc]
        · have hcP : c ∈ PivCols := by
            have : c ∈ Finset.univ \ PivCols → False := hc
            simpa using this
          let rU : U := Classical.choose (Finset.mem_image.mp hcP)
          have hrU_piv : pivCol rU = c := (Classical.choose_spec (Finset.mem_image.mp hcP)).2
          have hreq := hs.2 rU.val
          rw [bDot_eq_foldXor, foldXor_split (List.nodup_finRange C) (List.mem_finRange c)] at hreq
          have h1 : st.2.1 rU.val c = true := by rw [← hrU_piv]; exact (hpivCol_spec rU).1
          rw [h1, Bool.true_and] at hreq
          have hrest : foldXor (List.finRange C) (fun a => if a = c then false else st.2.1 rU.val a && s a) =
              bDot (fun c' => if c' = c then false else st.2.1 rU.val c')
                (fun c' => if h' : c' ∈ FreeCols then s c' else false) := by
            rw [bDot_eq_foldXor]
            apply foldXor_congr
            intro c' _
            by_cases hc' : c' = c
            · simp [hc']
            · cases hm : st.2.1 rU.val c'
              · simp
              · have hcf := hrow_free rU c' (by rw [hrU_piv]; exact hc') hm
                simp [hcf]
          rw [hrest] at hreq
          dsimp only [bwd, fwd]
          simp only [hc, ↓reduceDIte]
          change xor (bDot (st.2.2 rU.val) b)
            (bDot (fun c' => if c' = c then false else st.2.1 rU.val c')
              (fun c' => if h' : c' ∈ FreeCols then s c' else false)) = s c
          rw [← hreq, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      · intro f _
        funext c
        simp [fwd, bwd, c.2]
    change S.card = 2 ^ (C - usedCard)
    rw [hcard_eq, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hFreeCard]

def shiftRight1 {L : Nat} (v : Fin L → Bool) : Fin L → Bool :=
  fun j => if h : j.val + 1 < L then v ⟨j.val + 1, h⟩ else false

def pow2Step {m L : Nat} (used : Fin m → Bool) (idx : Nat) (v : Fin L → Bool) : Fin L → Bool :=
  if h : idx < m then
    fun j => if used ⟨idx, h⟩ then shiftRight1 v j else v j
  else v

def pow2Nullity {m : Nat} (L init : Nat) (used : Fin m → Bool) : Fin L → Bool :=
  (List.range m).foldl (fun v idx => pow2Step used idx v) (fun j => decide (j.val = init))

lemma pow2Nullity_spec {m L init : Nat} (used : Fin m → Bool)
    (hinit : init < L)
    (hle : (Finset.univ.filter (fun r : Fin m => used r = true)).card ≤ init) :
    ∀ j : Fin L, pow2Nullity L init used j =
      (2 ^ (init - (Finset.univ.filter (fun r : Fin m => used r = true)).card)).testBit j.val := by
  have hloop : ∀ t ≤ m,
      let v := (List.range t).foldl (fun v idx => pow2Step used idx v) (fun j : Fin L => decide (j.val = init))
      let cnt := (Finset.univ.filter (fun r : Fin m => r.val < t ∧ used r = true)).card
      cnt ≤ init ∧ ∀ j : Fin L, v j = decide (j.val = init - cnt) := by
    intro t
    induction t with
    | zero =>
      intro _
      have h0 : (Finset.univ.filter (fun r : Fin m => r.val < 0 ∧ used r = true)).card = 0 := by simp
      refine ⟨by omega, fun j => by rw [h0]; simp⟩
    | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨_, hv⟩
      set v := (List.range t).foldl (fun v idx => pow2Step used idx v) (fun j : Fin L => decide (j.val = init))
      have hnext : (List.range (t + 1)).foldl (fun v idx => pow2Step used idx v)
          (fun j : Fin L => decide (j.val = init)) = pow2Step used t v := by
        simp [List.range_succ, List.foldl_append, v]
      set S1 := Finset.univ.filter (fun r : Fin m => r.val < t + 1 ∧ used r = true)
      set S0 := Finset.univ.filter (fun r : Fin m => r.val < t ∧ used r = true)
      have hS1_le : S1.card ≤ init := by
        calc S1.card ≤ (Finset.univ.filter (fun r : Fin m => used r = true)).card :=
              Finset.card_le_card (fun r hr => by simp only [S1, Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢; exact hr.2)
          _ ≤ init := hle
      refine ⟨hS1_le, fun j => ?_⟩
      rw [hnext]
      dsimp only [pow2Step]
      have htm : t < m := by omega
      simp only [htm, ↓reduceDIte]
      cases hu : used ⟨t, htm⟩
      · have hSe : S1 = S0 := by
          ext r
          simp only [S1, S0, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hru⟩
            refine ⟨?_, hru⟩
            by_cases heq : r.val = t
            · have : r = ⟨t, htm⟩ := Fin.ext heq; rw [this, hu] at hru; exact Bool.noConfusion hru
            · omega
          · rintro ⟨hlt, hru⟩; exact ⟨by omega, hru⟩
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hSe]
        exact hv j
      · have hSe : S1 = insert ⟨t, htm⟩ S0 := by
          ext r
          simp only [S1, S0, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hru⟩
            by_cases heq : r.val = t
            · exact Or.inl (Fin.ext heq)
            · exact Or.inr ⟨by omega, hru⟩
          · rintro (rfl | ⟨hlt, hru⟩)
            · exact ⟨Nat.lt_succ_self t, hu⟩
            · exact ⟨by omega, hru⟩
        have hnotmem : (⟨t, htm⟩ : Fin m) ∉ S0 := by simp [S0]
        have hcard : S1.card = S0.card + 1 := by rw [hSe, Finset.card_insert_of_notMem hnotmem]
        simp only [↓reduceIte, shiftRight1]
        rw [hcard]
        by_cases hj1 : j.val + 1 < L
        · simp only [hj1, ↓reduceDIte]
          rw [hv ⟨j.val + 1, hj1⟩]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega
        · simp only [hj1, ↓reduceDIte]
          symm
          rw [decide_eq_false_iff_not]
          omega
  rcases hloop m le_rfl with ⟨_, hv⟩
  have hfilt : Finset.univ.filter (fun r : Fin m => r.val < m ∧ used r = true) =
      Finset.univ.filter (fun r : Fin m => used r = true) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]; intro _; exact r.isLt
  intro j
  dsimp only [pow2Nullity]
  rw [hv j, hfilt, Nat.testBit_two_pow]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact eq_comm

def parityK (k w : Nat) : Bool :=
  (List.range k).foldl (fun total bitPos => xor total (w.testBit bitPos)) false

def freeDim (k r pos : Nat) : Nat := min (unusedOf k r) (pos - (4 * r - 3))

def matAt (k r m pos : Nat) (A : Fin m → Fin (2 ^ k)) : Fin m → Fin (freeDim k r pos) → Bool :=
  fun i c => (A i).val.testBit (4 * r - 3 + c.val)

def adjRhs (k r m pos : Nat) (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (pref : Fin k → Bool)
    (i : Fin m) : Bool :=
  xor (rhs i)
    ((List.finRange (unusedOf k r)).foldl
      (fun acc c =>
        if freeDim k r pos ≤ c.val then
          xor acc ((A i).val.testBit (4 * r - 3 + c.val) &&
            (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false))
        else acc) false)

def prefMatch (k r pos : Nat) (w0 : Nat) (pref : Fin k → Bool) : Bool :=
  (List.finRange k).all (fun j =>
    !(decide (pos ≤ j.val) && !(decide (4 * r - 3 ≤ j.val ∧ j.val < 4 * r - 3 + unusedOf k r))) ||
      (w0.testBit j.val == pref j))

def passSeed (k r : Nat) (sched : Nat → Fin (2 ^ k)) (leftName rightName a b label : Nat) : Bool :=
  let w0 := decodeSeed k r sched leftName rightName a b label
  decide (stateN k r sched false w0 leftName r >>> zOf k = a) &&
    decide (stateN k r sched true w0 rightName r >>> zOf k = b)

def seedCons (k r m pos : Nat) (sched : Nat → Fin (2 ^ k)) (leftName rightName a b : Nat)
    (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (pref : Fin k → Bool) (label : Nat) : Bool :=
  let st := gElim (matAt k r m pos A)
  let w0 := decodeSeed k r sched leftName rightName a b label
  let bvec : Fin m → Bool := fun i => xor (parityK k (w0 &&& (A i).val)) (adjRhs k r m pos A rhs pref i)
  (List.finRange m).all (fun row => !(!(st.1 row) && bDot (st.2.2 row) bvec))

def seedOk (k r m pos : Nat) (sched : Nat → Fin (2 ^ k)) (leftName rightName a b : Nat)
    (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (pref : Fin k → Bool) (label : Nat) : Bool :=
  passSeed k r sched leftName rightName a b label &&
    prefMatch k r pos (decodeSeed k r sched leftName rightName a b label) pref &&
    seedCons k r m pos sched leftName rightName a b A rhs pref label

def countSpec (k r m pos : Nat) (sched : Nat → Fin (2 ^ k)) (leftName rightName a b : Nat)
    (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (pref : Fin k → Bool) : Nat :=
  let st := gElim (matAt k r m pos A)
  let usedCard := (Finset.univ.filter (fun row : Fin m => st.1 row = true)).card
  let stepVal := 2 ^ (freeDim k r pos - usedCard)
  ((List.finRange (2 ^ swOf k r)).map (fun label =>
    if seedOk k r m pos sched leftName rightName a b A rhs pref label.val then stepVal else 0)).sum

lemma parity_fiberWord_eq {k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    (c : Nat → Fin (2 ^ k)) (a b : Nat) {leftName rightName label : Nat}
    (hleft : leftName < 2 ^ k) (hright : rightName < 2 ^ k) (hlabel : label < 2 ^ swOf k r)
    (s : Fin (unusedOf k r) → Bool) (mask : Nat) :
    parityK k (fiberWord k r c leftName rightName a b label s &&& mask) =
      xor (parityK k (decodeSeed k r c leftName rightName a b label &&& mask))
        (foldXor (List.finRange (unusedOf k r)) (fun j => mask.testBit (4 * r - 3 + j.val) && s j)) := by
  have hdec := decodeSeed_spec hr hkpos c a b hleft hright hlabel
  have hfw := fiberWord_seed_cut hr hkpos c a b hleft hright hlabel s
  set w0 := decodeSeed k r c leftName rightName a b label
  set w := fiberWord k r c leftName rightName a b label s
  have hxor_bit : ∀ bp < k,
      (w &&& mask).testBit bp =
        xor ((w0 &&& mask).testBit bp)
          (if h : 4 * r - 3 ≤ bp ∧ bp < 4 * r - 3 + unusedOf k r then
            mask.testBit bp && s ⟨bp - (4 * r - 3), by omega⟩
          else false) := by
    intro bp _
    rw [Nat.testBit_and, Nat.testBit_and]
    by_cases h : 4 * r - 3 ≤ bp ∧ bp < 4 * r - 3 + unusedOf k r
    · simp only [h.1, h.2, and_self, ↓reduceDIte]
      have hj : bp - (4 * r - 3) < unusedOf k r := by omega
      have hbp_eq : 4 * r - 3 + (bp - (4 * r - 3)) = bp := by omega
      have hw0 : w0.testBit bp = false := by
        have := hdec.2.2.1 (bp - (4 * r - 3)) hj; rwa [hbp_eq] at this
      have hws : w.testBit bp = s ⟨bp - (4 * r - 3), hj⟩ := by
        have := hfw.2.2.1 ⟨bp - (4 * r - 3), hj⟩; rwa [hbp_eq] at this
      rw [hw0, hws, Bool.false_and, Bool.false_xor, Bool.and_comm]
    · simp only [h, ↓reduceDIte, Bool.xor_false]
      rw [hfw.2.2.2 bp (by omega)]
  change foldXor (List.range k) (fun bp => (w &&& mask).testBit bp) = _
  rw [foldXor_congr (fun bp hbp => hxor_bit bp (List.mem_range.mp hbp)), foldXor_xor]
  congr 1
  by_cases hun0 : unusedOf k r = 0
  · have h1 : foldXor (List.range k) (fun bp =>
        if h : 4 * r - 3 ≤ bp ∧ bp < 4 * r - 3 + unusedOf k r then
          mask.testBit bp && s ⟨bp - (4 * r - 3), by omega⟩
        else false) = false := by
      rw [foldXor_congr (g := fun _ => false) (fun bp _ => by simp [hun0])]
      exact foldXor_false _
    have hnil : List.finRange (unusedOf k r) = [] := List.eq_nil_of_length_eq_zero (by simp [hun0])
    have h2 : foldXor (List.finRange (unusedOf k r))
        (fun j => mask.testBit (4 * r - 3 + j.val) && s j) = false := by
      rw [hnil]; rfl
    rw [h1, h2]
  · have hun_pos : 0 < unusedOf k r := by omega
    have hsum := dims_sum k r hr
    have htop_le : 4 * r - 3 + unusedOf k r ≤ k := by dsimp only [unusedOf, zOf, hOf] at *; omega
    have hsplit1 : List.range k = List.range (4 * r - 3 + unusedOf k r) ++
        (List.range (k - (4 * r - 3 + unusedOf k r))).map (fun t => 4 * r - 3 + unusedOf k r + t) := by
      conv_lhs => rw [show k = (4 * r - 3 + unusedOf k r) + (k - (4 * r - 3 + unusedOf k r)) by omega]
      rw [List.range_add]
    have hsplit2 : List.range (4 * r - 3 + unusedOf k r) = List.range (4 * r - 3) ++
        (List.range (unusedOf k r)).map (fun t => 4 * r - 3 + t) := by
      rw [List.range_add]
    rw [hsplit1, hsplit2, foldXor_append, foldXor_append]
    have hlo0 : foldXor (List.range (4 * r - 3)) (fun bp =>
        if h : 4 * r - 3 ≤ bp ∧ bp < 4 * r - 3 + unusedOf k r then
          mask.testBit bp && s ⟨bp - (4 * r - 3), by omega⟩
        else false) = false := by
      rw [foldXor_congr (g := fun _ => false) (fun bp hbp => by
        have hlt := List.mem_range.mp hbp; simp [show ¬(4 * r - 3 ≤ bp) by omega])]
      exact foldXor_false _
    have hhi0 : foldXor ((List.range (k - (4 * r - 3 + unusedOf k r))).map (fun t => 4 * r - 3 + unusedOf k r + t))
        (fun bp => if h : 4 * r - 3 ≤ bp ∧ bp < 4 * r - 3 + unusedOf k r then
          mask.testBit bp && s ⟨bp - (4 * r - 3), by omega⟩
        else false) = false := by
      rw [foldXor_congr (g := fun _ => false) (fun bp hbp => by
        rcases List.mem_map.mp hbp with ⟨t, _, rfl⟩
        simp [show ¬(4 * r - 3 + unusedOf k r + t < 4 * r - 3 + unusedOf k r) by omega])]
      exact foldXor_false _
    rw [hlo0, hhi0, Bool.false_xor, Bool.xor_false, foldXor_map]
    have hfin : (List.finRange (unusedOf k r)).map Fin.val = List.range (unusedOf k r) := by
      apply List.ext_getElem <;> simp
    rw [← hfin, foldXor_map]
    apply foldXor_congr
    intro j _
    have hcond : 4 * r - 3 ≤ 4 * r - 3 + j.val ∧ 4 * r - 3 + j.val < 4 * r - 3 + unusedOf k r :=
      ⟨by omega, by omega⟩
    simp only [hcond.1, hcond.2, and_self, ↓reduceDIte]
    congr 2
    apply Fin.ext
    simp

lemma countSpec_eq_filter_length {k r m pos : Nat} (hr : 4 ≤ r) (hkpos : 0 < k) (_hpos : pos ≤ k)
    (sched : Nat → Fin (2 ^ k)) (leftName rightName : Fin (2 ^ k))
    (a b : Fin (2 ^ hOf k)) (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (pref : Fin k → Bool) :
    let solutions := (List.range (2 ^ k)).filter (fun w => decide (
      stateN k r sched false w leftName.val r >>> zOf k = a.val ∧
      stateN k r sched true w rightName.val r >>> zOf k = b.val ∧
      ∀ i : Fin m, parityK k (w &&& (A i).val) = rhs i))
    countSpec k r m pos sched leftName.val rightName.val a.val b.val A rhs pref =
      (solutions.filter (fun w =>
        (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == pref j)))).length := by
  classical
  intro solutions
  let P : Nat → Bool := fun w =>
    decide (stateN k r sched false w leftName.val r >>> zOf k = a.val ∧
      stateN k r sched true w rightName.val r >>> zOf k = b.val ∧
      ∀ i : Fin m, parityK k (w &&& (A i).val) = rhs i) &&
    (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == pref j))
  have hlen_eq : (solutions.filter (fun w =>
      (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == pref j)))).length =
      ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => P w.val = true)).card := by
    have hfilt : solutions.filter (fun w =>
        (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == pref j))) =
        (List.range (2 ^ k)).filter P := by
      dsimp only [solutions, P]
      rw [List.filter_filter]
      congr 1; funext w; exact Bool.and_comm _ _
    rw [hfilt]
    have hnd : ((List.range (2 ^ k)).filter P).Nodup := (List.nodup_range).filter P
    rw [← List.toFinset_card_of_nodup hnd]
    refine Finset.card_nbij' (fun w => if h : w < 2 ^ k then ⟨w, h⟩ else ⟨0, Nat.two_pow_pos k⟩)
      (fun w => w.val) ?_ ?_ ?_ ?_
    · intro w hw
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hw
      simp [hw.1, hw.2]
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      simp [List.mem_toFinset, List.mem_range, w.isLt, hw.2]
    · intro w hw
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter, List.mem_range] at hw
      simp [hw.1]
    · intro w _
      simp [w.isLt]
  rw [hlen_eq]
  let S_all : Finset (Fin (2 ^ swOf k r) × (Fin (freeDim k r pos) → Bool)) :=
    Finset.univ.filter (fun ls =>
      passSeed k r sched leftName.val rightName.val a.val b.val ls.1.val = true ∧
      prefMatch k r pos (decodeSeed k r sched leftName.val rightName.val a.val b.val ls.1.val) pref = true ∧
      ∀ i : Fin m,
        bDot (matAt k r m pos A i) ls.2 =
          xor (parityK k (decodeSeed k r sched leftName.val rightName.val a.val b.val ls.1.val &&& (A i).val))
            (adjRhs k r m pos A rhs pref i))
  let extS : (Fin (freeDim k r pos) → Bool) → (Fin (unusedOf k r) → Bool) := fun sf c =>
    if hc : c.val < freeDim k r pos then sf ⟨c.val, hc⟩
    else if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false
  have hfree_lt_iff : ∀ c : Fin (unusedOf k r), (pos ≤ 4 * r - 3 + c.val) ↔ freeDim k r pos ≤ c.val := by
    intro c
    have hc := c.isLt
    dsimp only [freeDim]
    omega
  have hun_lt_k : ∀ c : Fin (unusedOf k r), 4 * r - 3 + c.val < k := by
    intro c
    have hsum := dims_sum k r hr
    have hc := c.isLt
    dsimp only [unusedOf, zOf, hOf] at hc ⊢
    omega
  have hdot_split : ∀ (sf : Fin (freeDim k r pos) → Bool) (i : Fin m),
      foldXor (List.finRange (unusedOf k r))
        (fun c => (A i).val.testBit (4 * r - 3 + c.val) && extS sf c) =
      xor (bDot (matAt k r m pos A i) sf)
        (xor (rhs i) (adjRhs k r m pos A rhs pref i)) := by
    intro sf i
    have hfd_le : freeDim k r pos ≤ unusedOf k r := Nat.min_le_left _ _
    have hsplit : List.finRange (unusedOf k r) =
        (List.finRange (freeDim k r pos)).map (fun c => (⟨c.val, lt_of_lt_of_le c.isLt hfd_le⟩ : Fin (unusedOf k r))) ++
        (List.finRange (unusedOf k r)).drop (freeDim k r pos) := by
      apply List.ext_getElem
      · simp; omega
      · intro idx h1 h2
        apply Fin.ext
        by_cases hlt : idx < freeDim k r pos
        · rw [List.getElem_append_left (by simp; exact hlt)]; simp
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_map, List.length_finRange, List.getElem_drop, List.getElem_finRange, Fin.val_cast]
          omega
    have h1 : foldXor (List.finRange (unusedOf k r))
        (fun c => (A i).val.testBit (4 * r - 3 + c.val) && extS sf c) =
        xor (bDot (matAt k r m pos A i) sf)
          (foldXor ((List.finRange (unusedOf k r)).drop (freeDim k r pos))
            (fun c => (A i).val.testBit (4 * r - 3 + c.val) &&
              (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false))) := by
      conv_lhs => rw [hsplit]
      rw [foldXor_append]
      congr 1
      · rw [foldXor_map, bDot_eq_foldXor]
        apply foldXor_congr
        intro c _
        simp [extS, c.isLt, matAt]
      · apply foldXor_congr
        intro c hc
        have hge : freeDim k r pos ≤ c.val := by
          rw [List.mem_iff_getElem] at hc
          rcases hc with ⟨idx, hidx, rfl⟩
          simp only [List.getElem_drop, List.getElem_finRange, Fin.val_cast]
          omega
        simp [extS, show ¬(c.val < freeDim k r pos) by omega]
    have h2 : xor (rhs i) (adjRhs k r m pos A rhs pref i) =
        foldXor ((List.finRange (unusedOf k r)).drop (freeDim k r pos))
          (fun c => (A i).val.testBit (4 * r - 3 + c.val) &&
            (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false)) := by
      dsimp only [adjRhs]
      rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
      have hite : ∀ (l : List (Fin (unusedOf k r))) (f : Fin (unusedOf k r) → Bool),
          l.foldl (fun acc c => if freeDim k r pos ≤ c.val then xor acc (f c) else acc) false =
            foldXor l (fun c => if freeDim k r pos ≤ c.val then f c else false) := by
        intro l f
        have hgen : ∀ (init : Bool),
            l.foldl (fun acc c => if freeDim k r pos ≤ c.val then xor acc (f c) else acc) init =
            l.foldl (fun acc c => xor acc (if freeDim k r pos ≤ c.val then f c else false)) init := by
          induction l with
          | nil => intro _; rfl
          | cons a t ih =>
            intro init
            simp only [List.foldl_cons]
            by_cases h : freeDim k r pos ≤ a.val
            · simp only [h, ↓reduceIte]; exact ih _
            · simp only [h, ↓reduceIte, Bool.xor_false]; exact ih _
        exact hgen false
      rw [hite]
      conv_lhs => rw [hsplit]
      rw [foldXor_append]
      have hleft0 : foldXor ((List.finRange (freeDim k r pos)).map
            (fun c => (⟨c.val, lt_of_lt_of_le c.isLt hfd_le⟩ : Fin (unusedOf k r))))
          (fun c => if freeDim k r pos ≤ c.val then
            (A i).val.testBit (4 * r - 3 + c.val) &&
              (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false)
          else false) = false := by
        rw [foldXor_congr (g := fun _ => false) (fun c hc => by
          rcases List.mem_map.mp hc with ⟨c0, _, rfl⟩
          simp [show ¬(freeDim k r pos ≤ c0.val) by omega])]
        exact foldXor_false _
      rw [hleft0, Bool.false_xor]
      apply foldXor_congr
      intro c hc
      have hge : freeDim k r pos ≤ c.val := by
        rw [List.mem_iff_getElem] at hc
        rcases hc with ⟨idx, hidx, rfl⟩
        simp only [List.getElem_drop, List.getElem_finRange, Fin.val_cast]
        omega
      simp [hge]
    rw [h1, h2]
  have hbij : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun w => P w.val = true)).card = S_all.card := by
    symm
    refine Finset.card_nbij'
      (fun ls =>
        let w := fiberWord k r sched leftName.val rightName.val a.val b.val ls.1.val (extS ls.2)
        if h : w < 2 ^ k then ⟨w, h⟩ else ⟨0, Nat.two_pow_pos k⟩)
      (fun w =>
        (⟨seedOf k r w.val, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
         fun c => w.val.testBit (4 * r - 3 + c.val)))
      ?_ ?_ ?_ ?_
    · intro ls hls
      rw [Finset.mem_coe] at hls ⊢
      simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and] at hls
      rcases hls with ⟨hpass, hpm, haff⟩
      have hfw := fiberWord_seed_cut hr hkpos sched a.val b.val leftName.isLt rightName.isLt ls.1.isLt (extS ls.2)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hfw.1, ↓reduceDIte]
      dsimp only [P]
      rw [Bool.and_eq_true, decide_eq_true_eq]
      have htargets : stateN k r sched false (fiberWord k r sched leftName.val rightName.val a.val b.val ls.1.val (extS ls.2)) leftName.val r >>> zOf k = a.val ∧
          stateN k r sched true (fiberWord k r sched leftName.val rightName.val a.val b.val ls.1.val (extS ls.2)) rightName.val r >>> zOf k = b.val := by
        rw [targets_iff_fiberWord hr hkpos sched leftName.isLt rightName.isLt hfw.1]
        simp only [passSeed, Bool.and_eq_true, decide_eq_true_eq] at hpass
        exact ⟨ls.1, extS ls.2, rfl, hpass.1, hpass.2⟩
      refine ⟨⟨htargets.1, htargets.2, fun i => ?_⟩, ?_⟩
      · rw [parity_fiberWord_eq hr hkpos sched a.val b.val leftName.isLt rightName.isLt ls.1.isLt (extS ls.2),
          hdot_split ls.2 i, haff i]
        cases parityK k (decodeSeed k r sched leftName.val rightName.val a.val b.val ls.1.val &&& (A i).val) <;>
          cases rhs i <;> cases adjRhs k r m pos A rhs pref i <;> rfl
      · rw [List.all_eq_true]
        intro j _
        by_cases hjp : pos ≤ j.val
        · simp only [decide_eq_true hjp, Bool.not_true, Bool.false_or, beq_iff_eq]
          by_cases hinv : 4 * r - 3 ≤ j.val ∧ j.val < 4 * r - 3 + unusedOf k r
          · let c : Fin (unusedOf k r) := ⟨j.val - (4 * r - 3), by omega⟩
            have hjeq : 4 * r - 3 + c.val = j.val := by dsimp only [c]; omega
            have hge : freeDim k r pos ≤ c.val := (hfree_lt_iff c).mp (by rwa [hjeq])
            have hbit := hfw.2.2.1 c
            rw [hjeq] at hbit
            rw [hbit]
            dsimp only [extS]
            have hlt : 4 * r - 3 + c.val < k := by rw [hjeq]; exact j.isLt
            simp only [show ¬(c.val < freeDim k r pos) by omega, ↓reduceDIte, hlt]
            congr 1; exact Fin.ext hjeq
          · rw [hfw.2.2.2 j.val (by omega)]
            dsimp only [prefMatch] at hpm
            rw [List.all_eq_true] at hpm
            have hpmj := hpm j (List.mem_finRange j)
            simp only [decide_eq_true hjp, decide_eq_false hinv, Bool.not_false, Bool.and_true,
              Bool.not_true, Bool.false_or, beq_iff_eq] at hpmj
            exact hpmj
        · simp [hjp]
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      have hwP : P w.val = true := hw.2
      dsimp only [P] at hwP
      rw [Bool.and_eq_true, decide_eq_true_eq] at hwP
      rcases hwP with ⟨⟨ha, hb, haff⟩, hpref⟩
      have htf := (targets_iff_fiberWord hr hkpos sched leftName.isLt rightName.isLt w.isLt).mp ⟨ha, hb⟩
      rcases htf with ⟨label, s, hweq, hpa, hpb⟩
      have hfw := fiberWord_seed_cut hr hkpos sched a.val b.val leftName.isLt rightName.isLt label.isLt s
      have hseed : seedOf k r w.val = label.val := by rw [hweq]; exact hfw.2.1
      have hs_eq : s = extS (fun c => w.val.testBit (4 * r - 3 + c.val)) := by
        funext c
        dsimp only [extS]
        by_cases hcf : c.val < freeDim k r pos
        · simp only [hcf, ↓reduceDIte]; rw [hweq]; exact (hfw.2.2.1 c).symm
        · simp only [hcf, ↓reduceDIte, hun_lt_k c]
          rw [List.all_eq_true] at hpref
          have hpos_le : pos ≤ 4 * r - 3 + c.val := (hfree_lt_iff c).mpr (by omega)
          have hpr := hpref ⟨4 * r - 3 + c.val, hun_lt_k c⟩ (List.mem_finRange _)
          simp only [decide_eq_true hpos_le, Bool.not_true, Bool.false_or, beq_iff_eq] at hpr
          rw [← hpr, hweq]; exact (hfw.2.2.1 c).symm
      rw [Finset.mem_coe]
      simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hseed]
      refine ⟨?_, ?_, ?_⟩
      · simp [passSeed, hpa, hpb]
      · dsimp only [prefMatch]
        rw [List.all_eq_true]
        intro j _
        by_cases hjp : pos ≤ j.val
        · by_cases hinv : 4 * r - 3 ≤ j.val ∧ j.val < 4 * r - 3 + unusedOf k r
          · simp [hjp, hinv]
          · simp only [decide_eq_true hjp, decide_eq_false hinv, Bool.not_false, Bool.and_true,
              Bool.not_true, Bool.false_or, beq_iff_eq]
            rw [← hfw.2.2.2 j.val (by omega), ← hweq]
            rw [List.all_eq_true] at hpref
            have hpr := hpref j (List.mem_finRange j)
            simp only [decide_eq_true hjp, Bool.not_true, Bool.false_or, beq_iff_eq] at hpr
            exact hpr
        · simp [hjp]
      · intro i
        have hi := haff i
        rw [hweq, hs_eq, parity_fiberWord_eq hr hkpos sched a.val b.val leftName.isLt rightName.isLt label.isLt,
          hdot_split (fun c => w.val.testBit (4 * r - 3 + c.val)) i] at hi
        revert hi
        generalize parityK k (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val &&& (A i).val) = a1
        generalize bDot (matAt k r m pos A i) (fun c => w.val.testBit (4 * r - 3 + c.val)) = a2
        generalize rhs i = a3
        generalize adjRhs k r m pos A rhs pref i = a4
        cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> decide
    · intro ls _
      have hfw := fiberWord_seed_cut hr hkpos sched a.val b.val leftName.isLt rightName.isLt ls.1.isLt (extS ls.2)
      simp only [hfw.1, ↓reduceDIte]
      apply Prod.ext
      · exact Fin.ext hfw.2.1
      · funext c
        have hfd_le : freeDim k r pos ≤ unusedOf k r := Nat.min_le_left _ _
        have hbit := hfw.2.2.1 ⟨c.val, lt_of_lt_of_le c.isLt hfd_le⟩
        simp only [extS, c.isLt, ↓reduceDIte] at hbit
        exact hbit
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_filter] at hw
      have hwP : P w.val = true := hw.2
      dsimp only [P] at hwP
      rw [Bool.and_eq_true, decide_eq_true_eq] at hwP
      rcases hwP with ⟨⟨ha, hb, _⟩, hpref⟩
      have htf := (targets_iff_fiberWord hr hkpos sched leftName.isLt rightName.isLt w.isLt).mp ⟨ha, hb⟩
      rcases htf with ⟨label, s, hweq, _, _⟩
      have hfw := fiberWord_seed_cut hr hkpos sched a.val b.val leftName.isLt rightName.isLt label.isLt s
      have hseed : seedOf k r w.val = label.val := by rw [hweq]; exact hfw.2.1
      have hs_eq : extS (fun c => w.val.testBit (4 * r - 3 + c.val)) = s := by
        funext c
        dsimp only [extS]
        by_cases hcf : c.val < freeDim k r pos
        · simp only [hcf, ↓reduceDIte]; rw [hweq]; exact hfw.2.2.1 c
        · simp only [hcf, ↓reduceDIte, hun_lt_k c]
          rw [List.all_eq_true] at hpref
          have hpos_le : pos ≤ 4 * r - 3 + c.val := (hfree_lt_iff c).mpr (by omega)
          have hpr := hpref ⟨4 * r - 3 + c.val, hun_lt_k c⟩ (List.mem_finRange _)
          simp only [decide_eq_true hpos_le, Bool.not_true, Bool.false_or, beq_iff_eq] at hpr
          rw [← hpr, hweq]; exact hfw.2.2.1 c
      have hfw_eq : fiberWord k r sched leftName.val rightName.val a.val b.val (seedOf k r w.val)
          (extS (fun c => w.val.testBit (4 * r - 3 + c.val))) = w.val := by
        rw [hseed, hs_eq, ← hweq]
      dsimp only
      have hwlt : fiberWord k r sched leftName.val rightName.val a.val b.val (seedOf k r w.val)
          (extS (fun c => w.val.testBit (4 * r - 3 + c.val))) < 2 ^ k := by rw [hfw_eq]; exact w.isLt
      simp only [hwlt, ↓reduceDIte]
      exact Fin.ext hfw_eq
  rw [hbij]
  have hsum_card : S_all.card =
      ∑ label : Fin (2 ^ swOf k r),
        ((Finset.univ : Finset (Fin (freeDim k r pos) → Bool)).filter (fun sf =>
          passSeed k r sched leftName.val rightName.val a.val b.val label.val = true ∧
          prefMatch k r pos (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val) pref = true ∧
          ∀ i : Fin m,
            bDot (matAt k r m pos A i) sf =
              xor (parityK k (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val &&& (A i).val))
                (adjRhs k r m pos A rhs pref i))).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_nbij' (fun ls => ⟨ls.1, ls.2⟩) (fun p => (p.1, p.2)) ?_ ?_ ?_ ?_
    · intro ls hls
      rw [Finset.mem_coe] at hls ⊢
      simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and] at hls
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter]; exact hls
    · intro p hp
      rw [Finset.mem_coe] at hp ⊢
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_filter] at hp
      simp only [S_all, Finset.mem_filter, Finset.mem_univ, true_and]; exact hp
    · intro ls _; rfl
    · intro p _; rfl
  rw [hsum_card]
  dsimp only [countSpec]
  have hlist_sum : ∀ {N : Nat} (f : Fin N → Nat),
      ((List.finRange N).map f).sum = ∑ x : Fin N, f x := by
    intro N f
    rw [← Fin.sum_univ_def]
  rw [hlist_sum]
  apply Finset.sum_congr rfl
  intro label _
  dsimp only [seedOk, seedCons]
  by_cases hp : passSeed k r sched leftName.val rightName.val a.val b.val label.val = true ∧
      prefMatch k r pos (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val) pref = true
  · simp only [hp.1, hp.2, Bool.true_and, true_and]
    exact (gElim_card_eq (matAt k r m pos A)
      (fun i => xor (parityK k (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val &&& (A i).val))
        (adjRhs k r m pos A rhs pref i))).2.symm
  · have hf : (passSeed k r sched leftName.val rightName.val a.val b.val label.val &&
        prefMatch k r pos (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val) pref) = false := by
      cases h1 : passSeed k r sched leftName.val rightName.val a.val b.val label.val <;>
        cases h2 : prefMatch k r pos (decodeSeed k r sched leftName.val rightName.val a.val b.val label.val) pref <;>
        simp_all
    simp only [hf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    symm
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro sf hsf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsf
    exact hp ⟨hsf.1, hsf.2.1⟩

lemma list_split_of_pairwise_lt {l : List Nat} (hpw : l.Pairwise (· < ·)) (p : Nat → Bool)
    (hord : ∀ x ∈ l, ∀ y ∈ l, p x = true → p y = false → x < y) :
    l = l.filter p ++ l.filter (fun x => !(p x)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.pairwise_cons] at hpw
    have ih' := ih hpw.2 (fun x hx y hy => hord x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy))
    cases hpa : p a
    · have htp : t.filter p = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hpy
        have hlt1 : a < y := hpw.1 y hy
        have hlt2 : y < a := hord y (List.mem_cons_of_mem a hy) a List.mem_cons_self (by simpa using hpy) hpa
        omega
      have htf : t.filter (fun x => !(p x)) = t := by
        rw [List.filter_eq_self]
        intro y hy
        cases hpy : p y
        · rfl
        · have hlt1 : a < y := hpw.1 y hy
          have hlt2 : y < a := hord y (List.mem_cons_of_mem a hy) a List.mem_cons_self hpy hpa
          omega
      simp [hpa, htp, htf]
    · simp only [List.filter_cons, hpa, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.cons_append]
      congr 1

lemma lt_of_top_bits_eq {k pos x y : Nat} (hpos : pos < k) (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (htop : ∀ j, pos < j → j < k → x.testBit j = y.testBit j)
    (hx0 : x.testBit pos = false) (hy1 : y.testBit pos = true) : x < y := by
  have hdiv : x / 2 ^ (pos + 1) = y / 2 ^ (pos + 1) := by
    apply Nat.eq_of_testBit_eq
    intro j
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    by_cases hlt : pos + 1 + j < k
    · exact htop (pos + 1 + j) (by omega) hlt
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]
  have hxmod : x % 2 ^ (pos + 1) < 2 ^ pos := by
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [Nat.testBit_mod_two_pow]
    by_cases hjp : j = pos
    · subst hjp; simp [hx0]
    · rw [decide_eq_false (by omega : ¬ j < pos + 1), Bool.false_and]
  have hymod : 2 ^ pos ≤ y % 2 ^ (pos + 1) := by
    by_contra hlt
    have hfalse : (y % 2 ^ (pos + 1)).testBit pos = false := Nat.testBit_eq_false_of_lt (by omega)
    rw [Nat.testBit_mod_two_pow, decide_eq_true (by omega : pos < pos + 1), Bool.true_and, hy1] at hfalse
    exact Bool.noConfusion hfalse
  have hdx := Nat.div_add_mod x (2 ^ (pos + 1))
  have hdy := Nat.div_add_mod y (2 ^ (pos + 1))
  rw [hdiv] at hdx
  omega

def selectStep (k : Nat) (cnt : Nat → (Fin k → Bool) → Nat) (t : Nat)
    (st : (Fin k → Bool) × Nat) : (Fin k → Bool) × Nat :=
  if t < k then
    let pos := k - 1 - t
    let prefL : Fin k → Bool := fun j => if j.val = pos then false else st.1 j
    let leftCnt := cnt pos prefL
    let goRight := !(decide (st.2 < leftCnt))
    let pref' : Fin k → Bool := fun j => if j.val = pos then goRight else st.1 j
    let rem' := if goRight then (st.2 + (2 ^ (k + 1) - 1 - leftCnt + 1)) % 2 ^ (k + 1) else st.2
    (pref', rem')
  else st

def selectRun (k : Nat) (cnt : Nat → (Fin k → Bool) → Nat) (rank : Nat) :
    (Fin k → Bool) × Nat :=
  (List.range k).foldl (fun st t => selectStep k cnt t st) (fun _ => false, rank)

lemma selectRun_spec {k : Nat} (sols : List Nat)
    (hpw : sols.Pairwise (· < ·))
    (hlt : ∀ w ∈ sols, w < 2 ^ k)
    (cnt : Nat → (Fin k → Bool) → Nat)
    (hcnt : ∀ pos ≤ k, ∀ pref : Fin k → Bool,
      cnt pos pref = (sols.filter (fun w =>
        (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == pref j)))).length)
    (rank : Nat) (hrank : rank < sols.length) :
    ∀ d : Fin k, (selectRun k cnt rank).1 d = (sols.getD rank 0).testBit d.val := by
  have hsol_len : sols.length ≤ 2 ^ k := by
    have hnd : sols.Nodup := hpw.imp (fun h => Nat.ne_of_lt h)
    rw [← List.toFinset_card_of_nodup hnd]
    calc sols.toFinset.card ≤ (Finset.range (2 ^ k)).card :=
          Finset.card_le_card (fun w hw => Finset.mem_range.mpr (hlt w (List.mem_toFinset.mp hw)))
      _ = 2 ^ k := Finset.card_range _
  have hloop : ∀ t ≤ k,
      let st := (List.range t).foldl (fun st s => selectStep k cnt s st) (fun _ => false, rank)
      let sub := sols.filter (fun w =>
        (List.finRange k).all (fun j => !(decide (k - t ≤ j.val)) || (w.testBit j.val == st.1 j)))
      st.2 < sub.length ∧ sub.getD st.2 0 = sols.getD rank 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      have hsub : sols.filter (fun w =>
          (List.finRange k).all (fun j => !(decide (k - 0 ≤ j.val)) || (w.testBit j.val == false))) = sols := by
        rw [List.filter_eq_self]
        intro w _
        rw [List.all_eq_true]
        intro j _
        simp
      dsimp only [List.range_zero, List.foldl_nil]
      rw [hsub]
      exact ⟨hrank, rfl⟩
    | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨hrem_lt, hget_eq⟩
      set st := (List.range t).foldl (fun st s => selectStep k cnt s st) (fun _ => false, rank)
      set sub := sols.filter (fun w =>
        (List.finRange k).all (fun j => !(decide (k - t ≤ j.val)) || (w.testBit j.val == st.1 j)))
      have hnext : (List.range (t + 1)).foldl (fun st s => selectStep k cnt s st) (fun _ => false, rank) =
          selectStep k cnt t st := by
        simp [List.range_succ, List.foldl_append, st]
      rw [hnext]
      have htk : t < k := by omega
      dsimp only [selectStep]
      simp only [htk, ↓reduceIte]
      set pos := k - 1 - t
      set prefL : Fin k → Bool := fun j => if j.val = pos then false else st.1 j
      set leftCnt := cnt pos prefL
      set goRight := !(decide (st.2 < leftCnt))
      set pref' : Fin k → Bool := fun j => if j.val = pos then goRight else st.1 j
      set rem' := if goRight then (st.2 + (2 ^ (k + 1) - 1 - leftCnt + 1)) % 2 ^ (k + 1) else st.2
      have hpos_eq : k - (t + 1) = pos := by omega
      have hsub_pw : sub.Pairwise (· < ·) := hpw.filter _
      have hsub_split : sub = sub.filter (fun w => !(w.testBit pos)) ++ sub.filter (fun w => w.testBit pos) := by
        have hsp := list_split_of_pairwise_lt hsub_pw (fun w => !(w.testBit pos)) (by
          intro x hx y hy hxp hyp
          have hx' := List.mem_filter.mp hx
          have hy' := List.mem_filter.mp hy
          have htop : ∀ j, pos < j → j < k → x.testBit j = y.testBit j := by
            intro j hj1 hj2
            have hxj := List.all_eq_true.mp hx'.2 ⟨j, hj2⟩ (List.mem_finRange _)
            have hyj := List.all_eq_true.mp hy'.2 ⟨j, hj2⟩ (List.mem_finRange _)
            have hge : k - t ≤ j := by omega
            simp only [decide_eq_true hge, Bool.not_true, Bool.false_or, beq_iff_eq] at hxj hyj
            rw [hxj, hyj]
          have hx0 : x.testBit pos = false := by cases h : x.testBit pos <;> simp_all
          have hy1 : y.testBit pos = true := by cases h : y.testBit pos <;> simp_all
          exact lt_of_top_bits_eq (by omega) (hlt x hx'.1) (hlt y hy'.1) htop hx0 hy1)
        simpa only [Bool.not_not] using hsp
      have hleft_eq : sub.filter (fun w => !(w.testBit pos)) =
          sols.filter (fun w =>
            (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == prefL j))) := by
        dsimp only [sub]
        rw [List.filter_filter]
        congr 1; funext w
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_finRange, true_implies,
          Bool.or_eq_true, decide_eq_false_iff_not, beq_iff_eq]
        constructor
        · rintro ⟨hw0, hall⟩ j
          by_cases hjp : pos ≤ j.val
          · right
            by_cases hje : j.val = pos
            · simp [prefL, hje, hw0]
            · have hge : k - t ≤ j.val := by omega
              rcases hall j with hno | hyes
              · exact absurd hge hno
              · simp [prefL, hje, hyes]
          · exact Or.inl hjp
        · intro hall
          refine ⟨?_, fun j => ?_⟩
          · rcases hall ⟨pos, by omega⟩ with hno | hyes
            · exact absurd le_rfl hno
            · simpa [prefL] using hyes
          · by_cases hge : k - t ≤ j.val
            · right
              rcases hall j with hno | hyes
              · exact absurd (by omega : pos ≤ j.val) hno
              · simpa [prefL, show j.val ≠ pos by omega] using hyes
            · exact Or.inl hge
      have hright_eq : sub.filter (fun w => w.testBit pos) =
          sols.filter (fun w =>
            (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == (fun j => if j.val = pos then true else st.1 j) j))) := by
        dsimp only [sub]
        rw [List.filter_filter]
        congr 1; funext w
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq]
        constructor
        · rintro ⟨hw1, hall⟩ j
          by_cases hjp : pos ≤ j.val
          · right
            by_cases hje : j.val = pos
            · simp [hje, hw1]
            · have hge : k - t ≤ j.val := by omega
              rcases hall j with hno | hyes
              · exact absurd hge hno
              · simp [hje, hyes]
          · exact Or.inl hjp
        · intro hall
          refine ⟨?_, fun j => ?_⟩
          · rcases hall ⟨pos, by omega⟩ with hno | hyes
            · exact absurd le_rfl hno
            · simpa using hyes
          · by_cases hge : k - t ≤ j.val
            · right
              rcases hall j with hno | hyes
              · exact absurd (by omega : pos ≤ j.val) hno
              · simpa [show j.val ≠ pos by omega] using hyes
            · exact Or.inl hge
      have hleftCnt_eq : leftCnt = (sub.filter (fun w => !(w.testBit pos))).length := by
        rw [hleft_eq]; exact hcnt pos (by omega) prefL
      have hsub_len : sub.length = (sub.filter (fun w => !(w.testBit pos))).length +
          (sub.filter (fun w => w.testBit pos)).length := by
        conv_lhs => rw [hsub_split]
        exact List.length_append
      have hsub_le_pow : sub.length ≤ 2 ^ k := by
        calc sub.length ≤ sols.length := List.length_filter_le _ _
          _ ≤ 2 ^ k := hsol_len
      have hpow_lt : 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
      by_cases hgo : st.2 < leftCnt
      · have hgr : goRight = false := by simp [goRight, hgo]
        have hpref'_eq : pref' = prefL := by funext j; simp [pref', prefL, hgr]
        have hrem'_eq : rem' = st.2 := by simp [rem', hgr]
        change rem' < (sols.filter (fun w =>
          (List.finRange k).all (fun j => !(decide (k - (t + 1) ≤ j.val)) || (w.testBit j.val == pref' j)))).length ∧
          (sols.filter (fun w =>
            (List.finRange k).all (fun j => !(decide (k - (t + 1) ≤ j.val)) || (w.testBit j.val == pref' j)))).getD rem' 0 =
            sols.getD rank 0
        rw [hpos_eq, hpref'_eq, ← hleft_eq, hrem'_eq]
        have hltL : st.2 < (sub.filter (fun w => !(w.testBit pos))).length := by omega
        refine ⟨hltL, ?_⟩
        rw [← hget_eq]
        conv_rhs => rw [hsub_split]
        rw [List.getD_eq_getElem _ _ hltL, List.getD_eq_getElem _ _ (by rw [← hsub_split]; exact hrem_lt),
          List.getElem_append_left hltL]
      · have hgr : goRight = true := by simp [goRight, hgo]
        have hleL : leftCnt ≤ st.2 := by omega
        have hrem_lt_pow : st.2 < 2 ^ (k + 1) := by omega
        have hlc_lt_pow : leftCnt < 2 ^ (k + 1) := by omega
        have hrem'_eq : rem' = st.2 - leftCnt := by
          dsimp only [rem']
          simp only [hgr, ↓reduceIte]
          have h1 : st.2 + (2 ^ (k + 1) - 1 - leftCnt + 1) = (st.2 - leftCnt) + 2 ^ (k + 1) := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        change rem' < (sols.filter (fun w =>
          (List.finRange k).all (fun j => !(decide (k - (t + 1) ≤ j.val)) || (w.testBit j.val == pref' j)))).length ∧
          (sols.filter (fun w =>
            (List.finRange k).all (fun j => !(decide (k - (t + 1) ≤ j.val)) || (w.testBit j.val == pref' j)))).getD rem' 0 =
            sols.getD rank 0
        have hpref'_eq : pref' = fun j => if j.val = pos then true else st.1 j := by
          funext j; simp [pref', hgr]
        rw [hpos_eq, hpref'_eq, ← hright_eq, hrem'_eq]
        have hltR : st.2 - leftCnt < (sub.filter (fun w => w.testBit pos)).length := by omega
        refine ⟨hltR, ?_⟩
        rw [← hget_eq]
        conv_rhs => rw [hsub_split]
        rw [List.getD_eq_getElem _ _ hltR, List.getD_eq_getElem _ _ (by rw [← hsub_split]; exact hrem_lt),
          List.getElem_append_right (by omega)]
        congr 1; omega
  rcases hloop k le_rfl with ⟨hrem_lt, hget_eq⟩
  set st := selectRun k cnt rank
  set sub := sols.filter (fun w =>
    (List.finRange k).all (fun j => !(decide (k - k ≤ j.val)) || (w.testBit j.val == st.1 j)))
  have hmem : sols.getD rank 0 ∈ sub := by
    rw [← hget_eq, List.getD_eq_getElem _ _ hrem_lt]
    exact List.getElem_mem hrem_lt
  have hcond := (List.mem_filter.mp hmem).2
  intro d
  have hd := List.all_eq_true.mp hcond d (List.mem_finRange d)
  simp only [Nat.sub_self, Nat.zero_le, decide_true, Bool.not_true, Bool.false_or, beq_iff_eq] at hd
  exact hd.symm

abbrev Sig (N : Nat) := (Fin N → Bool) → Bool

def Scheduled (N : Nat) (sz : Nat) (S : Set (Sig N)) : Prop :=
  ∃ gs : List Gate, gs.length = sz ∧ ReadsBack N ⟨gs, 0⟩ ∧ FanInTwo ⟨gs, 0⟩ ∧
    ∀ a ∈ S, ∃ i : Nat, i < N + sz ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x

lemma wireLength (C : Circuit) (w : List Bool) :
    (C.wires w).length = w.length + C.gates.length := by
  rcases C with ⟨gs, out⟩
  change (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    w).length = w.length + gs.length
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma startSched (N : Nat) :
    Scheduled N 0 (Set.range (fun i : Fin N => fun x : Fin N → Bool => x i)) := by
  refine ⟨[], rfl, by simp [ReadsBack], by simp [FanInTwo], ?_⟩
  intro a ha
  obtain ⟨i, rfl⟩ := Set.mem_range.mp ha
  refine ⟨i.val, by simp, fun x => ?_⟩
  change (List.ofFn x).getD i.val false = x i
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma realizeDeps {N sz : Nat} {S : Set (Sig N)} {gs : List Gate}
    (hw : ∀ a ∈ S, ∃ i : Nat, i < N + sz ∧
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false = a x)
    (deps : List (Sig N)) (hdeps : ∀ a ∈ deps, a ∈ S) :
    ∃ is : List Nat, is.length = deps.length ∧ (∀ i ∈ is, i < N + sz) ∧
      ∀ x : Fin N → Bool,
        is.map (fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false) =
          deps.map (fun a => a x) := by
  induction deps with
  | nil => exact ⟨[], rfl, by simp, by simp⟩
  | cons a deps ih =>
    obtain ⟨i, hi, hval⟩ := hw a (hdeps a List.mem_cons_self)
    obtain ⟨is, hlen, hbound, hvals⟩ := ih (fun b hb => hdeps b (List.mem_cons_of_mem a hb))
    refine ⟨i :: is, by simp [hlen], ?_, fun x => ?_⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hi
      · exact hbound j hj
    · simp only [List.map_cons, hval x, hvals x]

lemma pushSched {N sz : Nat} {S : Set (Sig N)}
    (h : Scheduled N sz S) (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ S)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Scheduled N (sz + 1) (insert out S) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨is, his, hbound, hvalues⟩ := realizeDeps hw deps hdeps
  let g : Gate := ⟨op, is⟩
  have hlength (x : Fin N → Bool) :
      ((Circuit.mk gs 0).wires (List.ofFn x)).length = N + sz := by
    rw [wireLength]; simpa using congrArg (N + ·) hgs
  have hsnoc (x : Fin N → Bool) :
      (Circuit.mk (gs ++ [g]) 0).wires (List.ofFn x) =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x] := by
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (Circuit.mk gs 0).wires (List.ofFn x) ++
      [op.eval (is.map fun i => ((Circuit.mk gs 0).wires (List.ofFn x)).getD i false)] =
        (Circuit.mk gs 0).wires (List.ofFn x) ++ [out x]
    rw [hvalues x, hval x]
  refine ⟨gs ++ [g], by simp [hgs], ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (gs ++ [g]).length at hj
    change i ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at hi
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact hr j hj' i hi
    · have heq : j = gs.length := by simp at hj; omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      have hi' : i ∈ is := by simpa [g] using hi
      simpa [hgs] using hbound i hi'
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact hf g' hg'
    · rw [List.mem_singleton.mp hg']
      exact ⟨hop, by change is.length ≤ 2; simpa only [his] using hlen⟩
  · intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · refine ⟨N + sz, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append_right _ _ _ _ (by simp [hlength x])]
      simp [hlength x]
    · obtain ⟨i, hi, hval'⟩ := hw a ha
      refine ⟨i, by omega, fun x => ?_⟩
      rw [hsnoc x, List.getD_append _ _ _ _ (by simpa [hlength x] using hi), hval' x]

lemma finishOutputs {N sz k : Nat} {S : Set (Sig N)}
    (h : Scheduled N sz S)
    (outSig : Sig N) (hout : outSig ∈ S)
    (cntSigs : Fin (k + 1) → Sig N) (hcnt : ∀ j, cntSigs j ∈ S)
    (keySigs : Fin k → Sig N) (hkey : ∀ d, keySigs d ∈ S) :
    ∃ (C : Circuit) (countWire : Fin (k + 1) → Fin (N + C.size)) (keyWire : Fin k → Fin (N + C.size)),
      FanInTwo C ∧ ReadsBack N C ∧ C.output < N + C.size ∧ C.size = sz ∧
      ∀ x : Fin N → Bool,
        C.eval (List.ofFn x) = outSig x ∧
        (∀ j : Fin (k + 1), (C.wires (List.ofFn x)).getD (countWire j).val false = cntSigs j x) ∧
        (∀ d : Fin k, (C.wires (List.ofFn x)).getD (keyWire d).val false = keySigs d x) := by
  obtain ⟨gs, hgs, hr, hf, hw⟩ := h
  obtain ⟨io, hio, hvo⟩ := hw outSig hout
  have hc : ∀ j : Fin (k + 1), ∃ i : Fin (N + gs.length),
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = cntSigs j x := by
    intro j; obtain ⟨i, hi, hv⟩ := hw (cntSigs j) (hcnt j); exact ⟨⟨i, by omega⟩, hv⟩
  have hk : ∀ d : Fin k, ∃ i : Fin (N + gs.length),
      ∀ x : Fin N → Bool, ((Circuit.mk gs 0).wires (List.ofFn x)).getD i.val false = keySigs d x := by
    intro d; obtain ⟨i, hi, hv⟩ := hw (keySigs d) (hkey d); exact ⟨⟨i, by omega⟩, hv⟩
  choose countWire hcw using hc
  choose keyWire hkw using hk
  refine ⟨⟨gs, io⟩, countWire, keyWire, hf, hr, by change io < N + gs.length; omega, hgs, ?_⟩
  intro x
  exact ⟨hvo x, fun j => hcw j x, fun d => hkw d x⟩

def Build {N : Nat} (A B : Set (Sig N)) (b : Nat) : Prop :=
  ∀ (sz : Nat) (S : Set (Sig N)), Scheduled N sz S → A ⊆ S →
    ∃ c ≤ b, Scheduled N (sz + c) (S ∪ B)

lemma idleB {N : Nat} {A B : Set (Sig N)} (h : B ⊆ A) : Build A B 0 :=
  fun _ _ hs ha => ⟨0, le_rfl, by simpa [Set.union_eq_left.mpr (h.trans ha)] using hs⟩

lemma relaxB {N : Nat} {A A' B B' : Set (Sig N)} {b b' : Nat}
    (H : Build A B b) (hA : A ⊆ A') (hB : B' ⊆ A' ∪ B) (hb : b ≤ b') : Build A' B' b' :=
  fun sz S hs ha => by
    obtain ⟨c, hc, hsc⟩ := H sz S hs (hA.trans ha)
    obtain ⟨gs, hgs, hr, hf, hw⟩ := hsc
    refine ⟨c, hc.trans hb, gs, hgs, hr, hf, fun a hmem => ?_⟩
    rcases hmem with h1 | h2
    · exact hw a (Or.inl h1)
    · rcases hB h2 with h2a | h2b
      · exact hw a (Or.inl (ha h2a))
      · exact hw a (Or.inr h2b)

lemma seqB {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A (B ∪ C) (b + c) :=
  fun sz S hs ha => by
    obtain ⟨c1, hc1, hs1⟩ := H1 sz S hs ha
    obtain ⟨c2, hc2, hs2⟩ := H2 (sz + c1) (S ∪ B) hs1
      (Set.union_subset (ha.trans Set.subset_union_left) Set.subset_union_right)
    refine ⟨c1 + c2, Nat.add_le_add hc1 hc2, ?_⟩
    simpa [Nat.add_assoc, Set.union_assoc] using hs2

lemma seq2B {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build (A ∪ B) C c) : Build A C (b + c) :=
  relaxB (seqB H1 H2) le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

lemma extB {N : Nat} {A B : Set (Sig N)} {b : Nat} (H : Build A B b) : Build A (A ∪ B) b :=
  relaxB H le_rfl le_rfl le_rfl

lemma transB {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build B C c) : Build A C (b + c) :=
  relaxB (seqB H1 (relaxB H2 Set.subset_union_right Set.subset_union_right le_rfl))
    le_rfl (fun _ h => Or.inr (Or.inr h)) le_rfl

lemma unionB {N : Nat} {A B C : Set (Sig N)} {b c : Nat}
    (H1 : Build A B b) (H2 : Build A C c) : Build A (B ∪ C) (b + c) :=
  seqB H1 (relaxB H2 Set.subset_union_left Set.subset_union_right le_rfl)

lemma gateB {N : Nat} {A : Set (Sig N)} (op : GateOp) (deps : List (Sig N)) (out : Sig N)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : deps.length ≤ 2) (hdeps : ∀ a ∈ deps, a ∈ A)
    (hval : ∀ x, out x = op.eval (deps.map fun a => a x)) :
    Build A {out} 1 :=
  fun _ _ hs ha => ⟨1, le_rfl, by
    simpa [Set.union_singleton] using
      pushSched hs op deps out hop hlen (fun a hm => ha (hdeps a hm)) hval⟩

lemma constB {N : Nat} {A : Set (Sig N)} (b : Bool) : Build A {fun _ => b} 1 := by
  cases b with
  | false => exact gateB .or [] (fun _ => false) (by simp) (by simp) (by simp) (fun _ => rfl)
  | true => exact gateB .and [] (fun _ => true) (by simp) (by simp) (by simp) (fun _ => rfl)

lemma notB {N : Nat} {A : Set (Sig N)} {f : Sig N} (hf : f ∈ A) :
    Build A {fun x => !(f x)} 1 :=
  gateB .not [f] (fun x => !(f x)) (by simp) (by simp) (by simpa using hf) (fun _ => rfl)

lemma andB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x && g x} 1 :=
  gateB .and [f, g] (fun x => f x && g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

lemma orB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x || g x} 1 :=
  gateB .or [f, g] (fun x => f x || g x) (by simp) (by simp)
    (by intro a ha; simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; rcases ha with rfl | rfl <;> assumption)
    (fun _ => by simp [GateOp.eval])

lemma xorB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => xor (f x) (g x)} 4 := by
  let s1 : Sig N := fun x => f x || g x
  let s2 : Sig N := fun x => f x && g x
  let s3 : Sig N := fun x => !(s2 x)
  let s4 : Sig N := fun x => s1 x && s3 x
  have h1 : Build A {s1} 1 := orB hf hg
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hf) (Or.inl hg)
  have h3 : Build ((A ∪ {s1}) ∪ {s2}) {s3} 1 := notB (Or.inr rfl)
  have h4 : Build (((A ∪ {s1}) ∪ {s2}) ∪ {s3}) {s4} 1 :=
    andB (Or.inl (Or.inl (Or.inr rfl))) (Or.inr rfl)
  have heq : s4 = fun x => xor (f x) (g x) := by
    funext x; simp only [s4, s3, s2, s1]; cases f x <;> cases g x <;> rfl
  rw [← heq]
  exact relaxB (transB (transB (transB (extB h1) (extB h2)) (extB h3)) h4)
    le_rfl Set.subset_union_right (by omega)

lemma eqBoolB {N : Nat} {A : Set (Sig N)} {f g : Sig N} (hf : f ∈ A) (hg : g ∈ A) :
    Build A {fun x => f x == g x} 5 := by
  have h1 : Build A {fun x => xor (f x) (g x)} 4 := xorB hf hg
  have h2 : Build (A ∪ {fun x => xor (f x) (g x)}) {fun x => !(xor (f x) (g x))} 1 := notB (Or.inr rfl)
  have heq : (fun x => !(xor (f x) (g x))) = fun x => f x == g x := by
    funext x; cases f x <;> cases g x <;> rfl
  rw [← heq]
  exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by omega)

lemma iteB {N : Nat} {A : Set (Sig N)} {c a b : Sig N}
    (hc : c ∈ A) (ha : a ∈ A) (hb : b ∈ A) :
    Build A {fun x => if c x then a x else b x} 4 := by
  let s1 : Sig N := fun x => !(c x)
  let s2 : Sig N := fun x => c x && a x
  let s3 : Sig N := fun x => s1 x && b x
  let s4 : Sig N := fun x => s2 x || s3 x
  have h1 : Build A {s1} 1 := notB hc
  have h2 : Build (A ∪ {s1}) {s2} 1 := andB (Or.inl hc) (Or.inl ha)
  have h3 : Build ((A ∪ {s1}) ∪ {s2}) {s3} 1 := andB (Or.inl (Or.inr rfl)) (Or.inl (Or.inl hb))
  have h4 : Build (((A ∪ {s1}) ∪ {s2}) ∪ {s3}) {s4} 1 := orB (Or.inl (Or.inr rfl)) (Or.inr rfl)
  have heq : s4 = fun x => if c x then a x else b x := by
    funext x; simp only [s4, s3, s2, s1]; cases c x <;> cases a x <;> cases b x <;> rfl
  rw [← heq]
  exact relaxB (transB (transB (transB (extB h1) (extB h2)) (extB h3)) h4)
    le_rfl Set.subset_union_right (by omega)

lemma chiBitB {N : Nat} {A : Set (Sig N)} {a b c : Sig N}
    (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) :
    Build A {fun x => xor (a x) (!(b x) && c x)} 6 := by
  have h1 : Build A {fun x => !(b x)} 1 := notB hb
  have h2 : Build (A ∪ {fun x => !(b x)}) {fun x => !(b x) && c x} 1 := andB (Or.inr rfl) (Or.inl hc)
  have h3 : Build ((A ∪ {fun x => !(b x)}) ∪ {fun x => !(b x) && c x})
      {fun x => xor (a x) (!(b x) && c x)} 4 := xorB (Or.inl (Or.inl ha)) (Or.inr rfl)
  exact relaxB (transB (transB (extB h1) (extB h2)) h3) le_rfl Set.subset_union_right (by omega)

lemma listB {N : Nat} {α : Type*} {A : Set (Sig N)} (F : α → Set (Sig N)) (c : Nat)
    (l : List α) (h : ∀ a ∈ l, Build A (F a) c) :
    Build A (⋃ a ∈ l, F a) (l.length * c) := by
  induction l with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    intro f hf
    simp at hf
  | cons a l ih =>
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
    have hu := unionB h1 h2
    refine relaxB hu le_rfl ?_ (by simp only [List.length_cons, Nat.succ_mul]; omega)
    intro f hf
    simp only [Set.mem_iUnion, List.mem_cons] at hf
    rcases hf with ⟨b, rfl | hbl, hfb⟩
    · exact Or.inr (Or.inl hfb)
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨b, hbl, hfb⟩))

lemma finB {N n : Nat} {A : Set (Sig N)} (F : Fin n → Set (Sig N)) (c : Nat)
    (h : ∀ i : Fin n, Build A (F i) c) :
    Build A (⋃ i : Fin n, F i) (n * c) := by
  have hl := listB F c (List.finRange n) (fun i _ => h i)
  rw [List.length_finRange] at hl
  refine relaxB hl le_rfl ?_ le_rfl
  intro f hf
  rcases Set.mem_iUnion.mp hf with ⟨i, hfi⟩
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, List.mem_finRange i, hfi⟩)

lemma finSigB {N n : Nat} {A : Set (Sig N)} (F : Fin n → Sig N) (c : Nat)
    (h : ∀ i : Fin n, Build A {F i} c) :
    Build A (Set.range F) (n * c) := by
  refine relaxB (finB (fun i => {F i}) c h) le_rfl ?_ le_rfl
  rintro _ ⟨i, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, rfl⟩)

lemma fin2SigB {N n1 n2 : Nat} {A : Set (Sig N)} (F : Fin n1 → Fin n2 → Sig N) (c : Nat)
    (h : ∀ i j, Build A {F i j} c) :
    Build A {f | ∃ i j, F i j = f} (n1 * (n2 * c)) := by
  refine relaxB (finB (fun i => Set.range (F i)) (n2 * c) (fun i => finSigB (F i) c (fun j => h i j)))
    le_rfl ?_ le_rfl
  rintro f ⟨i, j, rfl⟩
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, ⟨j, rfl⟩⟩)

lemma iterB {N : Nat} {α : Type*} (Sigs : ((Fin N → Bool) → α) → Set (Sig N))
    (step : Nat → α → α) (c : Nat) (Base : Set (Sig N))
    (hstep : ∀ t (st : (Fin N → Bool) → α), Build (Base ∪ Sigs st) (Sigs (fun x => step t (st x))) c) :
    ∀ (T : Nat) (st0 : (Fin N → Bool) → α),
      Sigs st0 ⊆ Base →
      Build Base (Sigs (fun x => (List.range T).foldl (fun st t => step t st) (st0 x))) (T * c) := by
  intro T
  induction T with
  | zero =>
    intro st0 h0
    simpa using idleB h0
  | succ T ih =>
    intro st0 h0
    have hprev := ih st0 h0
    set stT : (Fin N → Bool) → α := fun x => (List.range T).foldl (fun st t => step t st) (st0 x)
    have hnext := hstep T stT
    have heq : (fun x => (List.range (T + 1)).foldl (fun st t => step t st) (st0 x)) =
        (fun x => step T (stT x)) := by
      funext x; simp [List.range_succ, List.foldl_append, stT]
    rw [heq]
    exact relaxB (seq2B hprev hnext) le_rfl Set.subset_union_right (by rw [Nat.succ_mul])

lemma andListB {N : Nat} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (htrue : (fun _ => true) ∈ A) :
    Build A {fun x => xs.all (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    simpa using idleB (Set.singleton_subset_iff.mpr htrue)
  | cons a xs ih =>
    have h1 := ih (fun f hf => hxs f (List.mem_cons_of_mem a hf))
    have h2 : Build (A ∪ {fun x => xs.all (fun f => f x)})
        {fun x => a x && xs.all (fun f => f x)} 1 :=
      andB (Or.inl (hxs a List.mem_cons_self)) (Or.inr rfl)
    simpa [List.length_cons] using seq2B h1 h2

lemma orListB {N : Nat} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => xs.any (fun f => f x)} xs.length := by
  induction xs with
  | nil =>
    simpa using idleB (Set.singleton_subset_iff.mpr hfalse)
  | cons a xs ih =>
    have h1 := ih (fun f hf => hxs f (List.mem_cons_of_mem a hf))
    have h2 : Build (A ∪ {fun x => xs.any (fun f => f x)})
        {fun x => a x || xs.any (fun f => f x)} 1 :=
      orB (Or.inl (hxs a List.mem_cons_self)) (Or.inr rfl)
    simpa [List.length_cons] using seq2B h1 h2

lemma xorListB {N : Nat} {A : Set (Sig N)} (xs : List (Sig N))
    (hxs : ∀ f ∈ xs, f ∈ A) (hfalse : (fun _ => false) ∈ A) :
    Build A {fun x => foldXor xs (fun f => f x)} (4 * xs.length) := by
  induction xs with
  | nil =>
    simpa [foldXor] using idleB (Set.singleton_subset_iff.mpr hfalse)
  | cons a xs ih =>
    have h1 := ih (fun f hf => hxs f (List.mem_cons_of_mem a hf))
    have h2 : Build (A ∪ {fun x => foldXor xs (fun f => f x)})
        {fun x => xor (a x) (foldXor xs (fun f => f x))} 4 :=
      xorB (Or.inl (hxs a List.mem_cons_self)) (Or.inr rfl)
    have heq : (fun x => xor (a x) (foldXor xs (fun f => f x))) =
        (fun x => foldXor (a :: xs) (fun f => f x)) := by
      funext x; exact (foldXor_cons a xs (fun f => f x)).symm
    rw [heq] at h2
    exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by simp only [List.length_cons]; omega)

def faSum (a b c : Bool) : Bool := xor (xor a b) c
def faCarry (a b c : Bool) : Bool := (a && b) || (xor a b && c)

lemma fullAdderB {N : Nat} {A : Set (Sig N)} {fa fb fc : Sig N}
    (ha : fa ∈ A) (hb : fb ∈ A) (hc : fc ∈ A) :
    Build A ({fun x => faSum (fa x) (fb x) (fc x), fun x => faCarry (fa x) (fb x) (fc x)}) 9 := by
  let t1 : Sig N := fun x => xor (fa x) (fb x)
  let sOut : Sig N := fun x => xor (t1 x) (fc x)
  let c1 : Sig N := fun x => fa x && fb x
  let c2 : Sig N := fun x => t1 x && fc x
  let cOut : Sig N := fun x => c1 x || c2 x
  have h1 : Build A {t1} 4 := xorB ha hb
  have h2 : Build (A ∪ {t1}) {sOut} 4 := xorB (Or.inr rfl) (Or.inl hc)
  have h3 : Build ((A ∪ {t1}) ∪ {sOut}) {c1} 1 := andB (Or.inl (Or.inl ha)) (Or.inl (Or.inl hb))
  have h4 : Build (((A ∪ {t1}) ∪ {sOut}) ∪ {c1}) {c2} 1 :=
    andB (Or.inl (Or.inl (Or.inr rfl))) (Or.inl (Or.inl (Or.inl hc)))
  have h5 : Build ((((A ∪ {t1}) ∪ {sOut}) ∪ {c1}) ∪ {c2}) {cOut} 1 :=
    orB (Or.inl (Or.inr rfl)) (Or.inr rfl)
  let abOr : Sig N := fun x => fa x || fb x
  let abAnd : Sig N := fun x => fa x && fb x
  let abNand : Sig N := fun x => !(abAnd x)
  let t1' : Sig N := fun x => abOr x && abNand x
  let tcOr : Sig N := fun x => t1' x || fc x
  let tcAnd : Sig N := fun x => t1' x && fc x
  let tcNand : Sig N := fun x => !(tcAnd x)
  let sOut' : Sig N := fun x => tcOr x && tcNand x
  let cOut' : Sig N := fun x => abAnd x || tcAnd x
  have g1 : Build A {abOr} 1 := orB ha hb
  have g2 : Build (A ∪ {abOr}) {abAnd} 1 := andB (Or.inl ha) (Or.inl hb)
  have g3 : Build (A ∪ ({abOr} ∪ {abAnd})) {abNand} 1 := notB (Or.inr (Or.inr rfl))
  have g4 : Build (A ∪ (({abOr} ∪ {abAnd}) ∪ {abNand})) {t1'} 1 :=
    andB (Or.inr (Or.inl (Or.inl rfl))) (Or.inr (Or.inr rfl))
  have g5 : Build (A ∪ ((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'})) {tcOr} 1 :=
    orB (Or.inr (Or.inr rfl)) (Or.inl hc)
  have g6 : Build (A ∪ (((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr})) {tcAnd} 1 :=
    andB (Or.inr (Or.inl (Or.inr rfl))) (Or.inl hc)
  have g7 : Build (A ∪ ((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr}) ∪ {tcAnd})) {tcNand} 1 :=
    notB (Or.inr (Or.inr rfl))
  have g8 : Build (A ∪ (((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand})) {sOut'} 1 :=
    andB (Or.inr (Or.inl (Or.inl (Or.inr rfl)))) (Or.inr (Or.inr rfl))
  have g9 : Build (A ∪ ((((((({abOr} ∪ {abAnd}) ∪ {abNand}) ∪ {t1'}) ∪ {tcOr}) ∪ {tcAnd}) ∪ {tcNand}) ∪ {sOut'})) {cOut'} 1 :=
    orB (Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr rfl))))))))
        (Or.inr (Or.inl (Or.inl (Or.inr rfl))))
  have hall := seqB (seqB (seqB (seqB (seqB (seqB (seqB (seqB g1 g2) g3) g4) g5) g6) g7) g8) g9
  have hsEq : sOut' = fun x => faSum (fa x) (fb x) (fc x) := by
    funext x; simp only [sOut', tcOr, tcNand, tcAnd, t1', abOr, abNand, abAnd, faSum]
    cases fa x <;> cases fb x <;> cases fc x <;> rfl
  have hcEq : cOut' = fun x => faCarry (fa x) (fb x) (fc x) := by
    funext x; simp only [cOut', tcAnd, t1', abOr, abNand, abAnd, faCarry]
    cases fa x <;> cases fb x <;> cases fc x <;> rfl
  refine relaxB hall le_rfl ?_ (by omega)
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl
  · rw [← hsEq]; exact Or.inr (Or.inl (Or.inr rfl))
  · rw [← hcEq]; exact Or.inr (Or.inr rfl)

def rippleCarry (a b : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => faCarry (a.testBit j) (b.testBit j) (rippleCarry a b j)

lemma testBit_eq_decide_div_mod (x j : Nat) :
    x.testBit j = decide ((x / 2 ^ j) % 2 = 1) := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]
  have hlt : (x / 2 ^ j) % 2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : (x / 2 ^ j) % 2 = 0 ∨ (x / 2 ^ j) % 2 = 1 := by omega
  rcases hcases with h | h <;> simp [h]

lemma mod_two_pow_succ_eq (a j : Nat) :
    a % 2 ^ (j + 1) = a % 2 ^ j + (if a.testBit j then 2 ^ j else 0) := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hdiv1 := Nat.div_add_mod a (2 ^ j)
  have hdiv2 := Nat.div_add_mod (a / 2 ^ j) 2
  have ha_eq : a = (a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2)) + 2 ^ (j + 1) * (a / 2 ^ j / 2) := by
    rw [Nat.pow_succ]
    have h1 : 2 ^ j * (a / 2 ^ j) = 2 ^ j * (2 * (a / 2 ^ j / 2) + (a / 2 ^ j) % 2) := by rw [hdiv2]
    rw [Nat.mul_add] at h1
    have h2 : 2 ^ j * (2 * (a / 2 ^ j / 2)) = 2 ^ j * 2 * (a / 2 ^ j / 2) := by ring
    omega
  have hlt_rem : a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) < 2 ^ (j + 1) := by
    have h1 : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ hpos
    have h2 : (a / 2 ^ j) % 2 ≤ 1 := by have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
    have h3 : 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j := by
      calc 2 ^ j * ((a / 2 ^ j) % 2) ≤ 2 ^ j * 1 := Nat.mul_le_mul_left _ h2
        _ = 2 ^ j := Nat.mul_one _
    rw [Nat.pow_succ]; omega
  have h1 : a % 2 ^ (j + 1) = a % 2 ^ j + 2 ^ j * ((a / 2 ^ j) % 2) := by
    conv_lhs => rw [ha_eq]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
  rw [h1, testBit_eq_decide_div_mod a j]
  have hcases : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  rcases hcases with h | h <;> simp [h]

lemma rippleCarry_spec (a b : Nat) :
    ∀ j : Nat,
      rippleCarry a b j = decide (2 ^ j ≤ a % 2 ^ j + b % 2 ^ j) ∧
      (a + b).testBit j = faSum (a.testBit j) (b.testBit j) (rippleCarry a b j) := by
  intro j
  have hcarry : ∀ k : Nat, rippleCarry a b k = decide (2 ^ k ≤ a % 2 ^ k + b % 2 ^ k) := by
    intro k
    induction k with
    | zero => simp [rippleCarry, Nat.mod_one]
    | succ k ih =>
      unfold rippleCarry
      rw [ih, mod_two_pow_succ_eq a k, mod_two_pow_succ_eq b k]
      have ha_lt : a % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hb_lt : b % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
      have hp : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ]; omega
      cases h1 : a.testBit k <;> cases h2 : b.testBit k <;>
        by_cases h3 : 2 ^ k ≤ a % 2 ^ k + b % 2 ^ k <;>
        simp [faCarry, h3, hp] <;> omega
  refine ⟨hcarry j, ?_⟩
  rw [hcarry j]
  have hdiv : (a + b) / 2 ^ j =
      a / 2 ^ j + b / 2 ^ j + (a % 2 ^ j + b % 2 ^ j) / 2 ^ j := by
    have ha := Nat.div_add_mod a (2 ^ j)
    have hb := Nat.div_add_mod b (2 ^ j)
    have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
    have hsum : a + b = (a % 2 ^ j + b % 2 ^ j) + (a / 2 ^ j + b / 2 ^ j) * 2 ^ j := by
      have : 2 ^ j * (a / 2 ^ j) = (a / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      have : 2 ^ j * (b / 2 ^ j) = (b / 2 ^ j) * 2 ^ j := Nat.mul_comm _ _
      rw [Nat.add_mul]; omega
    rw [hsum, Nat.add_mul_div_right _ _ hpos]; omega
  have hcdiv : (a % 2 ^ j + b % 2 ^ j) / 2 ^ j = if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0 := by
    have ha_lt : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb_lt : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    by_cases hle : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j
    · simp only [hle, ↓reduceIte]
      have hsub : a % 2 ^ j + b % 2 ^ j = (a % 2 ^ j + b % 2 ^ j - 2 ^ j) + 1 * 2 ^ j := by omega
      rw [hsub, Nat.add_mul_div_right _ _ (Nat.two_pow_pos j), Nat.div_eq_of_lt (by omega)]
    · simp only [hle, ↓reduceIte]; exact Nat.div_eq_of_lt (by omega)
  rw [testBit_eq_decide_div_mod (a + b) j, testBit_eq_decide_div_mod a j,
    testBit_eq_decide_div_mod b j, hdiv, hcdiv]
  have ha2 : (a / 2 ^ j) % 2 = 0 ∨ (a / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (a / 2 ^ j) (by omega : 0 < 2); omega
  have hb2 : (b / 2 ^ j) % 2 = 0 ∨ (b / 2 ^ j) % 2 = 1 := by
    have := Nat.mod_lt (b / 2 ^ j) (by omega : 0 < 2); omega
  have hmod : (a / 2 ^ j + b / 2 ^ j + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 =
      ((a / 2 ^ j) % 2 + (b / 2 ^ j) % 2 + if 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j then 1 else 0) % 2 := by omega
  rw [hmod]
  by_cases hc : 2 ^ j ≤ a % 2 ^ j + b % 2 ^ j <;>
  rcases ha2 with ha | ha <;> rcases hb2 with hb | hb <;> simp [faSum, hc, ha, hb]

def bitsOf {N : Nat} (L : Nat) (F : (Fin N → Bool) → Nat) : Fin L → Sig N :=
  fun j x => (F x).testBit j.val

lemma rippleB {N : Nat} {A : Set (Sig N)} (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A) :
    ∀ L : Nat,
      (∀ j : Fin L, (fun x => (F x).testBit j.val) ∈ A) →
      (∀ j : Fin L, (fun x => (G x).testBit j.val) ∈ A) →
      Build A
        ((Set.range (bitsOf L (fun x => F x + G x))) ∪ {fun x => rippleCarry (F x) (G x) L})
        (9 * L) := by
  intro L
  induction L with
  | zero =>
    intro _ _
    simp only [Nat.mul_zero]
    apply idleB
    intro f hf
    rcases hf with ⟨j, _⟩ | rfl
    · exact Fin.elim0 j
    · exact hfalse
  | succ L ih =>
    intro hF hG
    have hprev := ih (fun j => hF j.castSucc) (fun j => hG j.castSucc)
    have hstep : Build
        (A ∪ (Set.range (bitsOf L (fun x => F x + G x)) ∪ {fun x => rippleCarry (F x) (G x) L}))
        ({fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L),
          fun x => faCarry ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L)}) 9 :=
      fullAdderB (Or.inl (hF (Fin.last L))) (Or.inl (hG (Fin.last L))) (Or.inr (Or.inr rfl))
    have hseq := seqB hprev hstep
    refine relaxB hseq le_rfl ?_ (by omega)
    intro f hf
    rcases hf with ⟨j, rfl⟩ | rfl
    · by_cases hj : j.val < L
      · have hjeq : bitsOf (L + 1) (fun x => F x + G x) j =
            bitsOf L (fun x => F x + G x) ⟨j.val, hj⟩ := rfl
        rw [hjeq]
        exact Or.inr (Or.inl (Or.inl ⟨⟨j.val, hj⟩, rfl⟩))
      · have hjeq : j.val = L := by omega
        have hfeq : bitsOf (L + 1) (fun x => F x + G x) j =
            fun x => faSum ((F x).testBit L) ((G x).testBit L) (rippleCarry (F x) (G x) L) := by
          funext x; unfold bitsOf; rw [hjeq]; exact (rippleCarry_spec (F x) (G x) L).2
        rw [hfeq]
        exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

lemma sumTwoB {N : Nat} {A : Set (Sig N)} (L : Nat) (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A) :
    Build A (Set.range (bitsOf L (fun x => F x + G x))) (9 * L) :=
  relaxB (rippleB F G hfalse L hF hG) le_rfl (fun _ hf => Or.inr (Or.inl hf)) le_rfl

def sumListVal {N : Nat} : List ((Fin N → Bool) → Nat) → (Fin N → Bool) → Nat
  | [] => fun _ => 0
  | f :: fs => fun x => f x + sumListVal fs x

lemma sumListVal_eq_sum {N : Nat} (Fs : List ((Fin N → Bool) → Nat)) (x : Fin N → Bool) :
    sumListVal Fs x = (Fs.map (fun F => F x)).sum := by
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp [sumListVal, ih]

lemma sumListB {N : Nat} {A : Set (Sig N)} (L : Nat)
    (hfalse : (fun _ => false) ∈ A)
    (Fs : List ((Fin N → Bool) → Nat))
    (hFs : ∀ F ∈ Fs, ∀ j : Fin L, bitsOf L F j ∈ A) :
    Build A (Set.range (bitsOf L (sumListVal Fs))) (Fs.length * (9 * L)) := by
  induction Fs with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul]
    apply idleB
    rintro _ ⟨j, rfl⟩
    have : bitsOf L (sumListVal ([] : List ((Fin N → Bool) → Nat))) j = fun _ => false := by
      funext x; simp [bitsOf, sumListVal]
    rw [this]; exact hfalse
  | cons F Fs ih =>
    have h1 := ih (fun G hG => hFs G (List.mem_cons_of_mem F hG))
    have h2 : Build (A ∪ Set.range (bitsOf L (sumListVal Fs)))
        (Set.range (bitsOf L (fun x => F x + sumListVal Fs x))) (9 * L) :=
      sumTwoB L F (sumListVal Fs) (Or.inl hfalse)
        (fun j => Or.inl (hFs F List.mem_cons_self j))
        (fun j => Or.inr ⟨j, rfl⟩)
    refine relaxB (seq2B h1 h2) le_rfl Set.subset_union_right ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

lemma testBit_two_pow_sub_one_sub {L b j : Nat} (hb : b < 2 ^ L) (hj : j < L) :
    (2 ^ L - 1 - b).testBit j = !(b.testBit j) := by
  have h1 : (2 ^ L - 1 - b) + b = 2 ^ L - 1 := by omega
  have hpow : ∀ n k, (2 ^ n - 1).testBit k = decide (k < n) := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      rw [testBit_eq_decide_div_mod]
      cases k with
      | zero =>
        simp only [Nat.pow_zero, Nat.div_one, Nat.zero_lt_succ, decide_true]
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hm : (2 ^ (n + 1) - 1) % 2 = 1 := by rw [Nat.pow_succ]; omega
        simp [hm]
      | succ k =>
        have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
        have hdiv : (2 ^ (n + 1) - 1) / 2 ^ (k + 1) = (2 ^ n - 1) / 2 ^ k := by
          rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.div_div_eq_div_mul]
          congr 1; omega
        rw [hdiv, ← testBit_eq_decide_div_mod, ih k]; simp
  have hcarry : ∀ k ≤ L, rippleCarry (2 ^ L - 1 - b) b k = false := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hkL : k < L := by omega
      have hspec := (rippleCarry_spec (2 ^ L - 1 - b) b k).2
      rw [h1, hpow L k, decide_eq_true hkL, ih (by omega)] at hspec
      unfold rippleCarry
      rw [ih (by omega)]
      simp only [faSum, Bool.xor_false] at hspec
      cases hA : (2 ^ L - 1 - b).testBit k <;> cases hB : b.testBit k <;>
        simp [hA, hB, faCarry] at hspec ⊢
  have hspec := (rippleCarry_spec (2 ^ L - 1 - b) b j).2
  rw [h1, hpow L j, decide_eq_true hj, hcarry j (by omega)] at hspec
  simp only [faSum, Bool.xor_false] at hspec
  cases hA : (2 ^ L - 1 - b).testBit j <;> cases hB : b.testBit j <;>
    simp [hA, hB] at hspec ⊢

lemma subModB {N : Nat} {A : Set (Sig N)} (L : Nat) (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A) (htrue : (fun _ => true) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A)
    (hGlt : ∀ x, G x < 2 ^ L) :
    Build A (Set.range (bitsOf L (fun x => (F x + (2 ^ L - 1 - G x + 1)) % 2 ^ L))) (19 * L) := by
  let compG : (Fin N → Bool) → Nat := fun x => 2 ^ L - 1 - G x
  let oneF : (Fin N → Bool) → Nat := fun _ => 1
  have hcomp : Build A (Set.range (bitsOf L compG)) L := by
    have h1 := finSigB (A := A) (fun j : Fin L => fun x => !(bitsOf L G j x)) 1
      (fun j => notB (hG j))
    refine relaxB h1 le_rfl ?_ (by omega)
    rintro _ ⟨j, rfl⟩
    have heq : bitsOf L compG j = fun x => !(bitsOf L G j x) := by
      funext x; exact testBit_two_pow_sub_one_sub (hGlt x) j.isLt
    rw [heq]; exact Or.inr ⟨j, rfl⟩
  have hone : ∀ j : Fin L, bitsOf L oneF j ∈ A := by
    intro j
    by_cases hj : j.val = 0
    · have heq : bitsOf L oneF j = fun _ => true := by funext x; simp [bitsOf, oneF, hj]
      rw [heq]; exact htrue
    · have heq : bitsOf L oneF j = fun _ => false := by
        funext x; simp only [bitsOf, oneF]
        exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
          (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
      rw [heq]; exact hfalse
  have hadd1 : Build (A ∪ Set.range (bitsOf L compG))
      (Set.range (bitsOf L (fun x => compG x + oneF x))) (9 * L) :=
    sumTwoB L compG oneF (Or.inl hfalse) (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (hone j))
  have hadd2 : Build (A ∪ (Set.range (bitsOf L compG) ∪
      Set.range (bitsOf L (fun x => compG x + oneF x))))
      (Set.range (bitsOf L (fun x => F x + (compG x + oneF x)))) (9 * L) :=
    sumTwoB L F (fun x => compG x + oneF x) (Or.inl hfalse)
      (fun j => Or.inl (hF j)) (fun j => Or.inr (Or.inr ⟨j, rfl⟩))
  refine relaxB (seq2B (seqB hcomp hadd1) hadd2) le_rfl ?_ (by omega)
  rintro _ ⟨j, rfl⟩
  have heq : bitsOf L (fun x => (F x + (2 ^ L - 1 - G x + 1)) % 2 ^ L) j =
      bitsOf L (fun x => F x + (compG x + oneF x)) j := by
    funext x; unfold bitsOf compG oneF; dsimp only
    rw [Nat.testBit_mod_two_pow, decide_eq_true j.isLt, Bool.true_and]
  rw [heq]; exact Or.inr ⟨j, rfl⟩

def ltAux (a b : Nat) : Nat → Bool
  | 0 => false
  | j + 1 => (!(a.testBit j) && b.testBit j) || ((!(a.testBit j) || b.testBit j) && ltAux a b j)

lemma ltAux_spec (a b : Nat) : ∀ j : Nat, ltAux a b j = decide (a % 2 ^ j < b % 2 ^ j) := by
  intro j
  induction j with
  | zero => simp [ltAux, Nat.mod_one]
  | succ j ih =>
    unfold ltAux
    rw [ih, mod_two_pow_succ_eq a j, mod_two_pow_succ_eq b j]
    have ha : a % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb : b % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    cases a.testBit j
    · cases b.testBit j
      · simp
      · have hlt : a % 2 ^ j < b % 2 ^ j + 2 ^ j := by omega
        simp [hlt]
    · cases b.testBit j
      · have hge : ¬(a % 2 ^ j + 2 ^ j < b % 2 ^ j) := by omega
        simp [hge]
      · simp

lemma ltB {N : Nat} {A : Set (Sig N)} (L : Nat) (F G : (Fin N → Bool) → Nat)
    (hfalse : (fun _ => false) ∈ A)
    (hF : ∀ j : Fin L, bitsOf L F j ∈ A)
    (hG : ∀ j : Fin L, bitsOf L G j ∈ A)
    (hFlt : ∀ x, F x < 2 ^ L) (hGlt : ∀ x, G x < 2 ^ L) :
    Build A {fun x => decide (F x < G x)} (5 * L) := by
  have haux : ∀ j ≤ L, Build A {fun x => ltAux (F x) (G x) j} (5 * j) := by
    intro j
    induction j with
    | zero =>
      intro _; simpa [ltAux] using idleB (Set.singleton_subset_iff.mpr hfalse)
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      set aS : Sig N := bitsOf L F ⟨j, hj⟩
      set bS : Sig N := bitsOf L G ⟨j, hj⟩
      set pS : Sig N := fun x => ltAux (F x) (G x) j
      have haA : aS ∈ A := hF ⟨j, hj⟩
      have hbA : bS ∈ A := hG ⟨j, hj⟩
      let na : Sig N := fun x => !(aS x)
      let s1 : Sig N := fun x => na x && bS x
      let s2 : Sig N := fun x => na x || bS x
      let s3 : Sig N := fun x => s2 x && pS x
      let s4 : Sig N := fun x => s1 x || s3 x
      have g1 : Build (A ∪ {pS}) {na} 1 := notB (Or.inl haA)
      have g2 : Build ((A ∪ {pS}) ∪ {na}) {s1} 1 := andB (Or.inr rfl) (Or.inl (Or.inl hbA))
      have g3 : Build (((A ∪ {pS}) ∪ {na}) ∪ {s1}) {s2} 1 :=
        orB (Or.inl (Or.inr rfl)) (Or.inl (Or.inl (Or.inl hbA)))
      have g4 : Build ((((A ∪ {pS}) ∪ {na}) ∪ {s1}) ∪ {s2}) {s3} 1 :=
        andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr rfl))))
      have g5 : Build (((((A ∪ {pS}) ∪ {na}) ∪ {s1}) ∪ {s2}) ∪ {s3}) {s4} 1 :=
        orB (Or.inl (Or.inl (Or.inr rfl))) (Or.inr rfl)
      have hstep : Build (A ∪ {pS}) {s4} 5 :=
        relaxB (transB (transB (transB (transB (extB g1) (extB g2)) (extB g3)) (extB g4)) g5)
          le_rfl Set.subset_union_right (by omega)
      have heq : s4 = fun x => ltAux (F x) (G x) (j + 1) := by
        funext x; rfl
      rw [heq] at hstep
      exact relaxB (seq2B hprev hstep) le_rfl Set.subset_union_right (by omega)
  have hL := haux L le_rfl
  have heq : (fun x => ltAux (F x) (G x) L) = fun x => decide (F x < G x) := by
    funext x
    rw [ltAux_spec, Nat.mod_eq_of_lt (hFlt x), Nat.mod_eq_of_lt (hGlt x)]
  rw [heq] at hL
  exact hL

lemma firstTrueB {N n : Nat} {A : Set (Sig N)} (cond : Fin n → Sig N)
    (hfalse : (fun _ => false) ∈ A)
    (hcond : ∀ i : Fin n, cond i ∈ A) :
    Build A (Set.range (fun i : Fin n => fun x => firstTrue (fun j => cond j x) i)) (n * (n + 2)) := by
  refine finSigB (fun i : Fin n => fun x => firstTrue (fun j => cond j x) i) (n + 2) ?_
  intro i
  let xs : List (Sig N) := ((List.finRange n).filter (fun j => decide (j.val < i.val))).map cond
  have hxs : ∀ f ∈ xs, f ∈ A := by
    intro f hf; rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact hcond j
  have h1 : Build A {fun x => xs.any (fun f => f x)} xs.length := orListB xs hxs hfalse
  have h2 : Build (A ∪ {fun x => xs.any (fun f => f x)})
      {fun x => !(xs.any (fun f => f x))} 1 := notB (Or.inr rfl)
  have h3 : Build ((A ∪ {fun x => xs.any (fun f => f x)}) ∪ {fun x => !(xs.any (fun f => f x))})
      {fun x => cond i x && !(xs.any (fun f => f x))} 1 :=
    andB (Or.inl (Or.inl (hcond i))) (Or.inr rfl)
  have hlen : xs.length ≤ n := by
    calc xs.length = ((List.finRange n).filter (fun j => decide (j.val < i.val))).length := List.length_map _
      _ ≤ (List.finRange n).length := List.length_filter_le _ _
      _ = n := List.length_finRange
  have heq : (fun x => cond i x && !(xs.any (fun f => f x))) =
      (fun x => firstTrue (fun j => cond j x) i) := by
    funext x; simp [firstTrue, xs, List.any_map]
  rw [← heq]
  exact relaxB (transB (transB (extB h1) (extB h2)) h3) le_rfl Set.subset_union_right (by omega)

def gSigs {N m C : Nat} (st : (Fin N → Bool) → GState m C) : Set (Sig N) :=
  Set.range (fun r : Fin m => fun x => (st x).1 r) ∪
  {f | ∃ r c, (fun x => (st x).2.1 r c) = f} ∪
  {f | ∃ r i, (fun x => (st x).2.2 r i) = f}

lemma gStepB {N m C : Nat} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base)
    (col : Nat) (st : (Fin N → Bool) → GState m C) :
    Build (Base ∪ gSigs st) (gSigs (fun x => gStep col (st x)))
      (m * (m + 4) + (C + m) * (2 * m) + m * (1 + (C + m) * 7)) := by
  by_cases hcol : col < C
  · let c0 : Fin C := ⟨col, hcol⟩
    let cond : Fin m → Sig N := fun r x => !((st x).1 r) && (st x).2.1 r c0
    let isPiv : Fin m → Sig N := fun r x => firstTrue (fun j => cond j x) r
    let pivM : Fin C → Sig N := fun c x => (List.finRange m).any (fun r => isPiv r x && (st x).2.1 r c)
    let pivP : Fin m → Sig N := fun i x => (List.finRange m).any (fun r => isPiv r x && (st x).2.2 r i)
    have hcondB : Build (Base ∪ gSigs st) (Set.range cond) (m * 2) := by
      refine finSigB cond 2 (fun r => ?_)
      have h1 : Build (Base ∪ gSigs st) {fun x => !((st x).1 r)} 1 :=
        notB (Or.inr (Or.inl (Or.inl ⟨r, rfl⟩)))
      have h2 : Build ((Base ∪ gSigs st) ∪ {fun x => !((st x).1 r)}) {cond r} 1 :=
        andB (Or.inr rfl) (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c0, rfl⟩))))
      exact seq2B h1 h2
    have hftB : Build ((Base ∪ gSigs st) ∪ Set.range cond) (Set.range isPiv) (m * (m + 2)) :=
      firstTrueB cond (Or.inl (Or.inl hfalse)) (fun r => Or.inr ⟨r, rfl⟩)
    let A1 := (Base ∪ gSigs st) ∪ (Set.range cond ∪ Set.range isPiv)
    have h1 : Build (Base ∪ gSigs st) (Set.range cond ∪ Set.range isPiv) (m * 2 + m * (m + 2)) :=
      seqB hcondB hftB
    have hpivMB : Build A1 (Set.range pivM) (C * (2 * m)) := by
      refine finSigB pivM (2 * m) (fun c => ?_)
      let term : Fin m → Sig N := fun r x => isPiv r x && (st x).2.1 r c
      have ht : Build A1 (Set.range term) (m * 1) :=
        finSigB term 1 (fun r =>
          andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c, rfl⟩)))))
      have hor : Build (A1 ∪ Set.range term) {pivM c} m := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange m).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange m).map term).any (fun f => f x)) = pivM c := by
          funext x; simp [pivM, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have hpivPB : Build A1 (Set.range pivP) (m * (2 * m)) := by
      refine finSigB pivP (2 * m) (fun i => ?_)
      let term : Fin m → Sig N := fun r x => isPiv r x && (st x).2.2 r i
      have ht : Build A1 (Set.range term) (m * 1) :=
        finSigB term 1 (fun r =>
          andB (Or.inr (Or.inr ⟨r, rfl⟩)) (Or.inl (Or.inr (Or.inr ⟨r, i, rfl⟩))))
      have hor : Build (A1 ∪ Set.range term) {pivP i} m := by
        have h := orListB (A := A1 ∪ Set.range term) ((List.finRange m).map term)
          (fun f hf => by rcases List.mem_map.mp hf with ⟨r, _, rfl⟩; exact Or.inr ⟨r, rfl⟩)
          (Or.inl (Or.inl (Or.inl hfalse)))
        have heq : (fun x => ((List.finRange m).map term).any (fun f => f x)) = pivP i := by
          funext x; simp [pivP, term, List.any_map]; rfl
        rw [heq, List.length_map, List.length_finRange] at h
        exact h
      exact relaxB (seq2B ht hor) le_rfl Set.subset_union_right (by omega)
    have h2 : Build A1 (Set.range pivM ∪ Set.range pivP) (C * (2 * m) + m * (2 * m)) :=
      unionB hpivMB hpivPB
    let A2 := A1 ∪ (Set.range pivM ∪ Set.range pivP)
    have h3 : Build A2 (gSigs (fun x => gStep col (st x))) (m * (1 + (C + m) * 7)) := by
      have husedB : Build A2 (Set.range (fun r : Fin m => fun x => (gStep col (st x)).1 r)) (m * 1) :=
        finSigB _ 1 (fun r => by
          have heq : (fun x => (gStep col (st x)).1 r) = fun x => (st x).1 r || isPiv r x := by
            funext x; simp [gStep, hcol, isPiv, cond, c0]
          rw [heq]
          exact orB (Or.inl (Or.inl (Or.inr (Or.inl (Or.inl ⟨r, rfl⟩)))))
            (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩))))
      have hMB : Build A2 {f | ∃ r c, (fun x => (gStep col (st x)).2.1 r c) = f} (m * (C * 7)) :=
        fin2SigB _ 7 (fun r c => by
          let np : Sig N := fun x => !(isPiv r x)
          let flag : Sig N := fun x => np x && (st x).2.1 r c0
          let delta : Sig N := fun x => flag x && pivM c x
          let out : Sig N := fun x => xor ((st x).2.1 r c) (delta x)
          have hb1 : Build A2 {np} 1 := notB (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩)))
          have hb2 : Build (A2 ∪ {np}) {flag} 1 :=
            andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c0, rfl⟩))))))
          have hb3 : Build ((A2 ∪ {np}) ∪ {flag}) {delta} 1 :=
            andB (Or.inr rfl) (Or.inl (Or.inl (Or.inr (Or.inl ⟨c, rfl⟩))))
          have hb4 : Build (((A2 ∪ {np}) ∪ {flag}) ∪ {delta}) {out} 4 :=
            xorB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c, rfl⟩))))))))
              (Or.inr rfl)
          have heq : out = fun x => (gStep col (st x)).2.1 r c := by
            funext x; simp [out, delta, flag, np, gStep, hcol, isPiv, cond, c0, pivM]
          rw [← heq]
          exact relaxB (transB (transB (transB (extB hb1) (extB hb2)) (extB hb3)) hb4)
            le_rfl Set.subset_union_right (by omega))
      have hPB : Build A2 {f | ∃ r i, (fun x => (gStep col (st x)).2.2 r i) = f} (m * (m * 7)) :=
        fin2SigB _ 7 (fun r i => by
          let np : Sig N := fun x => !(isPiv r x)
          let flag : Sig N := fun x => np x && (st x).2.1 r c0
          let delta : Sig N := fun x => flag x && pivP i x
          let out : Sig N := fun x => xor ((st x).2.2 r i) (delta x)
          have hb1 : Build A2 {np} 1 := notB (Or.inl (Or.inr (Or.inr ⟨r, rfl⟩)))
          have hb2 : Build (A2 ∪ {np}) {flag} 1 :=
            andB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl (Or.inr ⟨r, c0, rfl⟩))))))
          have hb3 : Build ((A2 ∪ {np}) ∪ {flag}) {delta} 1 :=
            andB (Or.inr rfl) (Or.inl (Or.inl (Or.inr (Or.inr ⟨i, rfl⟩))))
          have hb4 : Build (((A2 ∪ {np}) ∪ {flag}) ∪ {delta}) {out} 4 :=
            xorB (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨r, i, rfl⟩)))))))
              (Or.inr rfl)
          have heq : out = fun x => (gStep col (st x)).2.2 r i := by
            funext x; simp [out, delta, flag, np, gStep, hcol, isPiv, cond, c0, pivP]
          rw [← heq]
          exact relaxB (transB (transB (transB (extB hb1) (extB hb2)) (extB hb3)) hb4)
            le_rfl Set.subset_union_right (by omega))
      exact relaxB (unionB (unionB husedB hMB) hPB) le_rfl Set.subset_union_right (by ring_nf; omega)
    exact relaxB (transB (transB (extB h1) (extB h2)) h3) le_rfl Set.subset_union_right (by ring_nf; omega)
  · have heq : (fun x => gStep col (st x)) = st := by funext x; simp [gStep, hcol]
    rw [heq]
    exact relaxB (idleB (A := Base ∪ gSigs st) (B := gSigs st) Set.subset_union_right)
      le_rfl Set.subset_union_right (Nat.zero_le _)

lemma gElimB {N m C : Nat} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (M0 : (Fin N → Bool) → Fin m → Fin C → Bool)
    (hM0 : ∀ r c, (fun x => M0 x r c) ∈ Base) :
    Build Base (gSigs (fun x => gElim (M0 x)))
      (C * (m * (m + 4) + (C + m) * (2 * m) + m * (1 + (C + m) * 7))) := by
  let st0 : (Fin N → Bool) → GState m C := fun x => (fun _ => false, M0 x, fun r i => decide (r = i))
  have hst0 : gSigs st0 ⊆ Base := by
    rintro f ((⟨r, rfl⟩ | ⟨r, c, rfl⟩) | ⟨r, i, rfl⟩)
    · exact hfalse
    · exact hM0 r c
    · by_cases hri : r = i
      · simpa [st0, hri] using htrue
      · simpa [st0, hri] using hfalse
  exact iterB (Sigs := gSigs) (step := gStep)
    (c := m * (m + 4) + (C + m) * (2 * m) + m * (1 + (C + m) * 7))
    (Base := Base) (fun col st => gStepB Base hfalse col st) C st0 hst0

lemma pow2NullityB {N m L : Nat} (Base : Set (Sig N))
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (init : Nat) (used : (Fin N → Bool) → Fin m → Bool)
    (hused : ∀ r : Fin m, (fun x => used x r) ∈ Base) :
    Build Base (Set.range (fun j : Fin L => fun x => pow2Nullity L init (used x) j))
      (m * (L * 4)) := by
  let Sigs : ((Fin N → Bool) → (Fin L → Bool)) → Set (Sig N) :=
    fun v => Set.range (fun j : Fin L => fun x => v x j)
  let stepFn : Nat → ((Fin N → Bool) → (Fin L → Bool)) → ((Fin N → Bool) → (Fin L → Bool)) :=
    fun idx v x => pow2Step (used x) idx (v x)
  have hloop : ∀ t : Nat,
      Build Base (Sigs (fun x => (List.range t).foldl (fun v idx => pow2Step (used x) idx v)
        (fun j : Fin L => decide (j.val = init)))) (t * (L * 4)) := by
    intro t
    induction t with
    | zero =>
      simp only [Nat.zero_mul]
      apply idleB
      rintro _ ⟨j, rfl⟩
      by_cases hj : j.val = init
      · simpa [hj] using htrue
      · simpa [hj] using hfalse
    | succ t ih =>
      set vT : (Fin N → Bool) → Fin L → Bool := fun x =>
        (List.range t).foldl (fun v idx => pow2Step (used x) idx v) (fun j : Fin L => decide (j.val = init))
      have heq : (fun x => (List.range (t + 1)).foldl (fun v idx => pow2Step (used x) idx v)
          (fun j : Fin L => decide (j.val = init))) = fun x => pow2Step (used x) t (vT x) := by
        funext x; simp [List.range_succ, List.foldl_append, vT]
      rw [heq]
      have hst : Build (Base ∪ Sigs vT) (Sigs (fun x => pow2Step (used x) t (vT x))) (L * 4) := by
        by_cases htm : t < m
        · refine finSigB (fun j : Fin L => fun x => pow2Step (used x) t (vT x) j) 4 (fun j => ?_)
          have hj_eq : (fun x => pow2Step (used x) t (vT x) j) =
              fun x => if used x ⟨t, htm⟩ then shiftRight1 (vT x) j else vT x j := by
            funext x; simp [pow2Step, htm]
          rw [hj_eq]
          have hsh_mem : (fun x => shiftRight1 (vT x) j) ∈ Base ∪ Sigs vT := by
            by_cases hj1 : j.val + 1 < L
            · have : (fun x => shiftRight1 (vT x) j) = fun x => vT x ⟨j.val + 1, hj1⟩ := by
                funext x; simp [shiftRight1, hj1]
              rw [this]; exact Or.inr ⟨⟨j.val + 1, hj1⟩, rfl⟩
            · have : (fun x => shiftRight1 (vT x) j) = fun _ => false := by
                funext x; simp [shiftRight1, hj1]
              rw [this]; exact Or.inl hfalse
          exact iteB (Or.inl (hused ⟨t, htm⟩)) hsh_mem (Or.inr ⟨j, rfl⟩)
        · have heq' : (fun x => pow2Step (used x) t (vT x)) = vT := by
            funext x; simp [pow2Step, htm]
          rw [heq']
          exact relaxB (idleB Set.subset_union_right) le_rfl Set.subset_union_right (Nat.zero_le _)
      exact relaxB (seq2B ih hst) le_rfl Set.subset_union_right (by rw [Nat.succ_mul])
  exact hloop m

lemma xorWordsB {N k : Nat} {A : Set (Sig N)} (W V : (Fin N → Bool) → Nat)
    (hW : ∀ j : Fin k, bitsOf k W j ∈ A)
    (hV : ∀ j : Fin k, bitsOf k V j ∈ A) :
    Build A (Set.range (bitsOf k (fun x => W x ^^^ V x))) (k * 4) := by
  refine finSigB (bitsOf k (fun x => W x ^^^ V x)) 4 (fun j => ?_)
  have heq : bitsOf k (fun x => W x ^^^ V x) j = fun x => xor (bitsOf k W j x) (bitsOf k V j x) := by
    funext x; simp [bitsOf, Nat.testBit_xor]
  rw [heq]
  exact xorB (hW j) (hV j)

lemma rotKB_mem {N k : Nat} (hkpos : 0 < k) {A : Set (Sig N)} (offset : Nat)
    (W : (Fin N → Bool) → Nat) (hW : ∀ j : Fin k, bitsOf k W j ∈ A)
    (hWlt : ∀ x, W x < 2 ^ k) :
    ∀ j : Fin k, bitsOf k (fun x => rotK k offset (W x)) j ∈ A := by
  intro j
  have heq : bitsOf k (fun x => rotK k offset (W x)) j =
      bitsOf k W ⟨(j.val + k - offset % k) % k, Nat.mod_lt _ hkpos⟩ := by
    funext x; exact rotK_testBit hkpos (hWlt x) offset j.val j.isLt
  rw [heq]
  exact hW _

lemma mixKB {N k : Nat} (hkpos : 0 < k) {A : Set (Sig N)} (gap : Nat)
    (W : (Fin N → Bool) → Nat) (hW : ∀ j : Fin k, bitsOf k W j ∈ A)
    (hWlt : ∀ x, W x < 2 ^ k) :
    Build A (Set.range (bitsOf k (fun x => mixK k gap (W x)))) (k * 8) := by
  have h1 := xorWordsB W (fun x => rotK k gap (W x)) hW (rotKB_mem hkpos gap W hW hWlt)
  have h2 := xorWordsB (A := A ∪ Set.range (bitsOf k (fun x => W x ^^^ rotK k gap (W x))))
    (fun x => W x ^^^ rotK k gap (W x)) (fun x => rotK k (k - gap) (W x))
    (fun j => Or.inr ⟨j, rfl⟩)
    (fun j => Or.inl (rotKB_mem hkpos (k - gap) W hW hWlt j))
  exact relaxB (seq2B h1 h2) le_rfl Set.subset_union_right (by omega)

lemma chiKB {N k : Nat} (hkpos : 0 < k) {A : Set (Sig N)}
    (W : (Fin N → Bool) → Nat) (hW : ∀ j : Fin k, bitsOf k W j ∈ A) :
    Build A (Set.range (bitsOf k (fun x => chiK k (W x)))) (k * 6) := by
  refine finSigB (bitsOf k (fun x => chiK k (W x))) 6 (fun j => ?_)
  have heq : bitsOf k (fun x => chiK k (W x)) j =
      fun x => xor (bitsOf k W j x)
        (!(bitsOf k W ⟨(j.val + 1) % k, Nat.mod_lt _ hkpos⟩ x) &&
          bitsOf k W ⟨(j.val + 2) % k, Nat.mod_lt _ hkpos⟩ x) := by
    funext x; exact (chiK_spec k (W x)).2 j.val j.isLt
  rw [heq]
  exact chiBitB (hW j) (hW _) (hW _)

lemma stepKB {N k r : Nat} (hkpos : 0 < k) {A : Set (Sig N)}
    (sched : (Fin N → Bool) → Nat → Fin (2 ^ k)) (col : Bool) (t : Nat)
    (raw prev : (Fin N → Bool) → Nat)
    (hraw : ∀ j : Fin k, bitsOf k raw j ∈ A) (hrawLt : ∀ x, raw x < 2 ^ k)
    (hprev : ∀ j : Fin k, bitsOf k prev j ∈ A) (hprevLt : ∀ x, prev x < 2 ^ k)
    (hconst : ∀ j : Fin k, bitsOf k (fun x => (sched x (if col then r + t else t)).val) j ∈ A) :
    Build A (Set.range (bitsOf k (fun x => stepK k r (sched x) col (raw x) (prev x) t))) (k * 22) := by
  have h1 := mixKB hkpos (if col then 2 else 1) prev hprev hprevLt
  have h2 := chiKB (A := A ∪ Set.range (bitsOf k (fun x => mixK k (if col then 2 else 1) (prev x))))
    hkpos (fun x => mixK k (if col then 2 else 1) (prev x)) (fun j => Or.inr ⟨j, rfl⟩)
  have h12 := seq2B h1 h2
  have h3 := xorWordsB
    (A := A ∪ Set.range (bitsOf k (fun x => chiK k (mixK k (if col then 2 else 1) (prev x)))))
    (fun x => chiK k (mixK k (if col then 2 else 1) (prev x)))
    (fun x => rotK k (if col then 3 * t + 1 else 2 * (t - 1)) (raw x))
    (fun j => Or.inr ⟨j, rfl⟩)
    (fun j => Or.inl (rotKB_mem hkpos _ raw hraw hrawLt j))
  have h123 := seq2B h12 h3
  have h4 := xorWordsB
    (A := A ∪ Set.range (bitsOf k (fun x =>
      chiK k (mixK k (if col then 2 else 1) (prev x)) ^^^
        rotK k (if col then 3 * t + 1 else 2 * (t - 1)) (raw x))))
    (fun x => chiK k (mixK k (if col then 2 else 1) (prev x)) ^^^
      rotK k (if col then 3 * t + 1 else 2 * (t - 1)) (raw x))
    (fun x => (sched x (if col then r + t else t)).val)
    (fun j => Or.inr ⟨j, rfl⟩)
    (fun j => Or.inl (hconst j))
  exact relaxB (seq2B h123 h4) le_rfl Set.subset_union_right (by omega)

lemma stateNB {N k r : Nat} (hkpos : 0 < k) {A : Set (Sig N)}
    (sched : (Fin N → Bool) → Nat → Fin (2 ^ k)) (side : Bool)
    (key name : (Fin N → Bool) → Nat)
    (hkey : ∀ j : Fin k, bitsOf k key j ∈ A) (hkeyLt : ∀ x, key x < 2 ^ k)
    (hname : ∀ j : Fin k, bitsOf k name j ∈ A) (hnameLt : ∀ x, name x < 2 ^ k)
    (hsched : ∀ t, 1 ≤ t → t ≤ 2 * r → ∀ j : Fin k, bitsOf k (fun x => (sched x t).val) j ∈ A) :
    ∀ t ≤ r, Build A (Set.range (bitsOf k (fun x => stateN k r (sched x) side (key x) (name x) t)))
      (4 * k + t * (22 * k)) := by
  intro t
  induction t with
  | zero =>
    intro _
    have h0 := xorWordsB (fun x => rotK k (if side then 3 else 1) (key x)) name
      (rotKB_mem hkpos _ key hkey hkeyLt) hname
    exact relaxB h0 le_rfl Set.subset_union_right (by omega)
  | succ t ih =>
    intro ht
    have hprev := ih (by omega)
    have hst := stepKB
      (A := A ∪ Set.range (bitsOf k (fun x => stateN k r (sched x) side (key x) (name x) t)))
      hkpos sched side (t + 1) key (fun x => stateN k r (sched x) side (key x) (name x) t)
      (fun j => Or.inl (hkey j)) hkeyLt
      (fun j => Or.inr ⟨j, rfl⟩) (fun x => stateN_lt (sched x) side (key x) (hnameLt x) t)
      (fun j => Or.inl (hsched (if side then r + (t + 1) else t + 1)
        (by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
        (by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega) j))
    have heq : (fun x => stateN k r (sched x) side (key x) (name x) (t + 1)) =
        fun x => stepK k r (sched x) side (key x) (stateN k r (sched x) side (key x) (name x) t) (t + 1) := by
      funext x; exact stateN_succ k r (sched x) side (key x) (name x) t
    rw [heq]
    exact relaxB (seq2B hprev hst) le_rfl Set.subset_union_right (by exact le_of_eq (by ring))

lemma decodeSeedB {N k r : Nat} (hr : 4 ≤ r) (hkpos : 0 < k) {Base : Set (Sig N)}
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (sched : (Fin N → Bool) → Nat → Fin (2 ^ k))
    (leftName rightName a b : (Fin N → Bool) → Nat)
    (hsched : ∀ t, 1 ≤ t → t ≤ 2 * r → ∀ j : Fin k, bitsOf k (fun x => (sched x t).val) j ∈ Base)
    (hleft : ∀ j : Fin k, bitsOf k leftName j ∈ Base) (hleftLt : ∀ x, leftName x < 2 ^ k)
    (hright : ∀ j : Fin k, bitsOf k rightName j ∈ Base) (hrightLt : ∀ x, rightName x < 2 ^ k)
    (ha : ∀ j : Fin (hOf k), bitsOf (hOf k) a j ∈ Base)
    (hb : ∀ j : Fin (hOf k), bitsOf (hOf k) b j ∈ Base)
    (label : Fin (2 ^ swOf k r)) :
    Build Base (Set.range (bitsOf k (fun x => decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val)))
      ((rowLenOf k r + colLenOf k r) * (22 * k * r + 18 * k + 8)) := by
  have hsum := dims_sum k r hr
  have hrowB : ∀ m ≤ rowLenOf k r,
      Build Base (Set.range (bitsOf k (fun x => rowDec k r (sched x) (leftName x) (a x) label.val m)))
        (m * (22 * k * r + 18 * k + 8)) := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [Nat.zero_mul]
      apply idleB
      rintro _ ⟨j, rfl⟩
      by_cases hbit : (rotK k (startOf k r) label.val).testBit j.val = true
      · have heq : bitsOf k (fun x => rowDec k r (sched x) (leftName x) (a x) label.val 0) j = fun _ => true := by
          funext x; simp [bitsOf, rowDec, hbit]
        rw [heq]; exact htrue
      · have hbf : (rotK k (startOf k r) label.val).testBit j.val = false := by
          cases h : (rotK k (startOf k r) label.val).testBit j.val <;> simp_all
        have heq : bitsOf k (fun x => rowDec k r (sched x) (leftName x) (a x) label.val 0) j = fun _ => false := by
          funext x; simp [bitsOf, rowDec, hbf]
        rw [heq]; exact hfalse
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      set prev : (Fin N → Bool) → Nat := fun x => rowDec k r (sched x) (leftName x) (a x) label.val m
      have hprevLt : ∀ x, prev x < 2 ^ k := fun x =>
        (rowDec_props hr hkpos (sched x) (a x) (hleftLt x) label.isLt m (by omega)).1
      have hrl_pos : 0 < rowLenOf k r := by omega
      have hrl_le_h : rowLenOf k r ≤ hOf k := Nat.min_le_left _ _
      have hrl_le_ku : rowLenOf k r ≤ k - uOf r := Nat.min_le_right _ _
      have hu_eq : uOf r = 5 * r - 3 := rfl
      have hkgt : 5 * r - 2 ≤ k := by omega
      set p := k - (2 * r - 2) - (m + 1)
      set i := k - (m + 1)
      have hi_lt : i < k := by dsimp only [i]; omega
      have hiz_lt : i - zOf k < hOf k := by dsimp only [i, zOf, hOf] at *; omega
      have hp_lt : p < k := by dsimp only [p]; omega
      have hprev_p : ∀ x, (prev x).testBit p = false := by
        intro x
        have hpr := rowDec_props hr hkpos (sched x) (a x) (hleftLt x) label.isLt m (by omega)
        rw [hpr.2.1 p (Or.inl (by dsimp only [p]; omega))]
        have hsw_eq : swOf k r = 5 * r - 3 + extraOf k r := by dsimp only [swOf, uOf]; omega
        exact init_mid_false hr hkgt label.isLt (by dsimp only [p]; omega) (by dsimp only [p]; omega)
      let A1 := Base ∪ Set.range (bitsOf k prev)
      have hst := stateNB (A := A1) hkpos sched false prev leftName
        (fun j => Or.inr ⟨j, rfl⟩) hprevLt
        (fun j => Or.inl (hleft j)) hleftLt
        (fun t ht1 ht2 j => Or.inl (hsched t ht1 ht2 j)) (r - 1) (by omega)
      set st : (Fin N → Bool) → Nat := fun x => stateN k r (sched x) false (prev x) (leftName x) (r - 1)
      have hmx := mixKB (A := A1 ∪ Set.range (bitsOf k st)) hkpos 1 st
        (fun j => Or.inr ⟨j, rfl⟩) (fun x => stateN_lt (sched x) false (prev x) (hleftLt x) (r - 1))
      have hch := chiKB (A := A1 ∪ Set.range (bitsOf k (fun x => mixK k 1 (st x))))
        hkpos (fun x => mixK k 1 (st x)) (fun j => Or.inr ⟨j, rfl⟩)
      have h123 := seq2B (seq2B hst hmx) hch
      let bit1 : Sig N := fun x => xor ((chiK k (mixK k 1 (st x))).testBit i) ((sched x r).val.testBit i)
      let bit2 : Sig N := fun x => xor (bit1 x) ((a x).testBit (i - zOf k))
      have hx1 : Build (A1 ∪ Set.range (bitsOf k (fun x => chiK k (mixK k 1 (st x))))) {bit1} 4 :=
        xorB (Or.inr ⟨⟨i, hi_lt⟩, rfl⟩) (Or.inl (Or.inl (hsched r (by omega) (by omega) ⟨i, hi_lt⟩)))
      have hx2 : Build ((A1 ∪ Set.range (bitsOf k (fun x => chiK k (mixK k 1 (st x))))) ∪ {bit1}) {bit2} 4 :=
        xorB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (ha ⟨i - zOf k, hiz_lt⟩))))
      have hbit := seq2B h123 (seq2B hx1 hx2)
      have hstep : Build A1 (Set.range (bitsOf k (fun x => rowDec k r (sched x) (leftName x) (a x) label.val (m + 1))))
          (22 * k * r + 18 * k + 8) := by
        have hcost_le : 4 * k + (r - 1) * (22 * k) + k * 8 + k * 6 + (4 + 4) ≤ 22 * k * r + 18 * k + 8 := by
          have hmul : (r - 1) * (22 * k) ≤ 22 * k * r := by
            calc (r - 1) * (22 * k) ≤ r * (22 * k) := Nat.mul_le_mul_right _ (by omega)
              _ = 22 * k * r := Nat.mul_comm _ _
          omega
        refine relaxB hbit le_rfl ?_ hcost_le
        rintro _ ⟨j, rfl⟩
        by_cases hjp : j.val = p
        · have heq : bitsOf k (fun x => rowDec k r (sched x) (leftName x) (a x) label.val (m + 1)) j = bit2 := by
            funext x; unfold bitsOf; dsimp only [rowDec]; rw [hjp, testBit_putBit_eq (hprev_p x)]
          rw [heq]; exact Or.inr rfl
        · have heq : bitsOf k (fun x => rowDec k r (sched x) (leftName x) (a x) label.val (m + 1)) j =
              bitsOf k prev j := by
            funext x; unfold bitsOf; dsimp only [rowDec]; exact testBit_putBit_ne hjp
          rw [heq]; exact Or.inl (Or.inr ⟨j, rfl⟩)
      exact relaxB (seq2B hprev hstep) le_rfl Set.subset_union_right (by exact le_of_eq (by ring))
  have hcolB : ∀ m ≤ colLenOf k r,
      Build Base (Set.range (bitsOf k (fun x => colDec k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val m)))
        ((rowLenOf k r + m) * (22 * k * r + 18 * k + 8)) := by
    intro m
    induction m with
    | zero =>
      intro _; simpa [colDec] using hrowB (rowLenOf k r) le_rfl
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      set prev : (Fin N → Bool) → Nat := fun x => colDec k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val m
      have hprevLt : ∀ x, prev x < 2 ^ k := fun x =>
        (colDec_props hr hkpos (sched x) (a x) (b x) (hleftLt x) (hrightLt x) label.isLt m (by omega)).1
      have hcl_pos : 0 < colLenOf k r := by omega
      have hcl_le_r3 : colLenOf k r ≤ r + 3 := Nat.min_le_left _ _
      have hcl_le_zu : colLenOf k r ≤ zOf k - uOf r := Nat.min_le_right _ _
      have hzu : uOf r < zOf k := by omega
      have hzk : zOf k = k - hOf k := rfl
      have hhk : hOf k = (k + 1) / 2 := rfl
      have hu_eq : uOf r = 5 * r - 3 := rfl
      have hkgt : 5 * r - 2 ≤ k := by omega
      have hrl_eq : rowLenOf k r = hOf k := by dsimp only [rowLenOf]; omega
      set q := k - (2 * r - 2) - rowLenOf k r - (m + 1)
      set i := zOf k + (r + 3) - (m + 1)
      have hi_lt : i < k := by dsimp only [i]; omega
      have hiz_lt : i - zOf k < hOf k := by dsimp only [i]; omega
      have hq_lt : q < k := by dsimp only [q]; omega
      have hprev_q : ∀ x, (prev x).testBit q = false := by
        intro x
        have hpr := colDec_props hr hkpos (sched x) (a x) (b x) (hleftLt x) (hrightLt x) label.isLt m (by omega)
        rw [hpr.2.1 q (Or.inl (by dsimp only [q]; omega))]
        have hsw_eq : swOf k r = 5 * r - 3 + extraOf k r := by dsimp only [swOf, uOf]; omega
        exact init_mid_false hr hkgt label.isLt (by dsimp only [q]; omega) (by dsimp only [q]; omega)
      let A1 := Base ∪ Set.range (bitsOf k prev)
      have hst := stateNB (A := A1) hkpos sched true prev rightName
        (fun j => Or.inr ⟨j, rfl⟩) hprevLt
        (fun j => Or.inl (hright j)) hrightLt
        (fun t ht1 ht2 j => Or.inl (hsched t ht1 ht2 j)) (r - 1) (by omega)
      set st : (Fin N → Bool) → Nat := fun x => stateN k r (sched x) true (prev x) (rightName x) (r - 1)
      have hmx := mixKB (A := A1 ∪ Set.range (bitsOf k st)) hkpos 2 st
        (fun j => Or.inr ⟨j, rfl⟩) (fun x => stateN_lt (sched x) true (prev x) (hrightLt x) (r - 1))
      have hch := chiKB (A := A1 ∪ Set.range (bitsOf k (fun x => mixK k 2 (st x))))
        hkpos (fun x => mixK k 2 (st x)) (fun j => Or.inr ⟨j, rfl⟩)
      have h123 := seq2B (seq2B hst hmx) hch
      let bit1 : Sig N := fun x => xor ((chiK k (mixK k 2 (st x))).testBit i) ((sched x (r + r)).val.testBit i)
      let bit2 : Sig N := fun x => xor (bit1 x) ((b x).testBit (i - zOf k))
      have hx1 : Build (A1 ∪ Set.range (bitsOf k (fun x => chiK k (mixK k 2 (st x))))) {bit1} 4 :=
        xorB (Or.inr ⟨⟨i, hi_lt⟩, rfl⟩) (Or.inl (Or.inl (hsched (r + r) (by omega) (by omega) ⟨i, hi_lt⟩)))
      have hx2 : Build ((A1 ∪ Set.range (bitsOf k (fun x => chiK k (mixK k 2 (st x))))) ∪ {bit1}) {bit2} 4 :=
        xorB (Or.inr rfl) (Or.inl (Or.inl (Or.inl (hb ⟨i - zOf k, hiz_lt⟩))))
      have hbit := seq2B h123 (seq2B hx1 hx2)
      have hstep : Build A1 (Set.range (bitsOf k (fun x => colDec k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val (m + 1))))
          (22 * k * r + 18 * k + 8) := by
        have hcost_le : 4 * k + (r - 1) * (22 * k) + k * 8 + k * 6 + (4 + 4) ≤ 22 * k * r + 18 * k + 8 := by
          have hmul : (r - 1) * (22 * k) ≤ 22 * k * r := by
            calc (r - 1) * (22 * k) ≤ r * (22 * k) := Nat.mul_le_mul_right _ (by omega)
              _ = 22 * k * r := Nat.mul_comm _ _
          omega
        refine relaxB hbit le_rfl ?_ hcost_le
        rintro _ ⟨j, rfl⟩
        by_cases hjq : j.val = q
        · have heq : bitsOf k (fun x => colDec k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val (m + 1)) j = bit2 := by
            funext x; unfold bitsOf; dsimp only [colDec]; rw [hjq, testBit_putBit_eq (hprev_q x)]
          rw [heq]; exact Or.inr rfl
        · have heq : bitsOf k (fun x => colDec k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val (m + 1)) j =
              bitsOf k prev j := by
            funext x; unfold bitsOf; dsimp only [colDec]; exact testBit_putBit_ne hjq
          rw [heq]; exact Or.inl (Or.inr ⟨j, rfl⟩)
      exact relaxB (seq2B hprev hstep) le_rfl Set.subset_union_right (by exact le_of_eq (by ring))
  exact hcolB (colLenOf k r) le_rfl

lemma shiftRight_eq_iff_bits {k : Nat} {v target : Nat} (hv : v < 2 ^ k) (ht : target < 2 ^ hOf k) :
    decide (v >>> zOf k = target) =
      (List.finRange (hOf k)).all (fun j => v.testBit (zOf k + j.val) == target.testBit j.val) := by
  have hzk : zOf k + hOf k = k := by dsimp only [zOf, hOf]; omega
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  constructor
  · intro heq j; rw [← Nat.testBit_shiftRight, heq]
  · intro hall
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_shiftRight]
    by_cases hj : j < hOf k
    · exact hall ⟨j, hj⟩
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]

lemma passSeedB {N k r : Nat} (hkpos : 0 < k) {Base : Set (Sig N)}
    (htrue : (fun _ => true) ∈ Base)
    (sched : (Fin N → Bool) → Nat → Fin (2 ^ k))
    (leftName rightName a b w0 : (Fin N → Bool) → Nat)
    (hsched : ∀ t, 1 ≤ t → t ≤ 2 * r → ∀ j : Fin k, bitsOf k (fun x => (sched x t).val) j ∈ Base)
    (hleft : ∀ j : Fin k, bitsOf k leftName j ∈ Base) (hleftLt : ∀ x, leftName x < 2 ^ k)
    (hright : ∀ j : Fin k, bitsOf k rightName j ∈ Base) (hrightLt : ∀ x, rightName x < 2 ^ k)
    (ha : ∀ j : Fin (hOf k), bitsOf (hOf k) a j ∈ Base) (haLt : ∀ x, a x < 2 ^ hOf k)
    (hb : ∀ j : Fin (hOf k), bitsOf (hOf k) b j ∈ Base) (hbLt : ∀ x, b x < 2 ^ hOf k)
    (hw0 : ∀ j : Fin k, bitsOf k w0 j ∈ Base) (hw0Lt : ∀ x, w0 x < 2 ^ k) :
    Build Base {(fun x => decide (stateN k r (sched x) false (w0 x) (leftName x) r >>> zOf k = a x) &&
        decide (stateN k r (sched x) true (w0 x) (rightName x) r >>> zOf k = b x))}
      (44 * k * r + 8 * k + 12 * hOf k + 1) := by
  have hzk : zOf k + hOf k = k := by dsimp only [zOf, hOf]; omega
  have hL := stateNB hkpos sched false w0 leftName hw0 hw0Lt hleft hleftLt hsched r le_rfl
  have hR := stateNB hkpos sched true w0 rightName hw0 hw0Lt hright hrightLt hsched r le_rfl
  have hLR := unionB hL hR
  let A1 := Base ∪ (Set.range (bitsOf k (fun x => stateN k r (sched x) false (w0 x) (leftName x) r)) ∪
    Set.range (bitsOf k (fun x => stateN k r (sched x) true (w0 x) (rightName x) r)))
  let eqL : Fin (hOf k) → Sig N := fun j x =>
    (stateN k r (sched x) false (w0 x) (leftName x) r).testBit (zOf k + j.val) == (a x).testBit j.val
  let eqR : Fin (hOf k) → Sig N := fun j x =>
    (stateN k r (sched x) true (w0 x) (rightName x) r).testBit (zOf k + j.val) == (b x).testBit j.val
  have heqLB : Build A1 (Set.range eqL) (hOf k * 5) :=
    finSigB eqL 5 (fun j => eqBoolB (Or.inr (Or.inl ⟨⟨zOf k + j.val, by omega⟩, rfl⟩)) (Or.inl (ha j)))
  have heqRB : Build A1 (Set.range eqR) (hOf k * 5) :=
    finSigB eqR 5 (fun j => eqBoolB (Or.inr (Or.inr ⟨⟨zOf k + j.val, by omega⟩, rfl⟩)) (Or.inl (hb j)))
  have heqLR := unionB heqLB heqRB
  let A2 := A1 ∪ (Set.range eqL ∪ Set.range eqR)
  have handL : Build A2 {(fun x => decide (stateN k r (sched x) false (w0 x) (leftName x) r >>> zOf k = a x))} (hOf k) := by
    have h := andListB (A := A2) ((List.finRange (hOf k)).map eqL)
      (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr (Or.inl ⟨j, rfl⟩))
      (Or.inl (Or.inl htrue))
    have heq : (fun x => ((List.finRange (hOf k)).map eqL).all (fun f => f x)) =
        fun x => decide (stateN k r (sched x) false (w0 x) (leftName x) r >>> zOf k = a x) := by
      funext x
      rw [shiftRight_eq_iff_bits (stateN_lt (sched x) false (w0 x) (hleftLt x) r) (haLt x)]
      simp [List.all_map, eqL]; rfl
    rw [heq, List.length_map, List.length_finRange] at h
    exact h
  have handR : Build A2 {(fun x => decide (stateN k r (sched x) true (w0 x) (rightName x) r >>> zOf k = b x))} (hOf k) := by
    have h := andListB (A := A2) ((List.finRange (hOf k)).map eqR)
      (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr (Or.inr ⟨j, rfl⟩))
      (Or.inl (Or.inl htrue))
    have heq : (fun x => ((List.finRange (hOf k)).map eqR).all (fun f => f x)) =
        fun x => decide (stateN k r (sched x) true (w0 x) (rightName x) r >>> zOf k = b x) := by
      funext x
      rw [shiftRight_eq_iff_bits (stateN_lt (sched x) true (w0 x) (hrightLt x) r) (hbLt x)]
      simp [List.all_map, eqR]; rfl
    rw [heq, List.length_map, List.length_finRange] at h
    exact h
  have handBoth : Build (A2 ∪ ({(fun x => decide (stateN k r (sched x) false (w0 x) (leftName x) r >>> zOf k = a x))} ∪
      {(fun x => decide (stateN k r (sched x) true (w0 x) (rightName x) r >>> zOf k = b x))}))
      {(fun x => decide (stateN k r (sched x) false (w0 x) (leftName x) r >>> zOf k = a x) &&
        decide (stateN k r (sched x) true (w0 x) (rightName x) r >>> zOf k = b x))} 1 :=
    andB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  have hall := seq2B hLR (seq2B heqLR (seq2B (unionB handL handR) handBoth))
  exact relaxB hall le_rfl Set.subset_union_right (by ring_nf; omega)

lemma parityAndB {N k : Nat} {A : Set (Sig N)}
    (hfalse : (fun _ => false) ∈ A)
    (W M : (Fin N → Bool) → Nat)
    (hW : ∀ j : Fin k, bitsOf k W j ∈ A)
    (hM : ∀ j : Fin k, bitsOf k M j ∈ A) :
    Build A {fun x => parityK k (W x &&& M x)} (5 * k) := by
  let term : Fin k → Sig N := fun j x => bitsOf k W j x && bitsOf k M j x
  have ht : Build A (Set.range term) (k * 1) := finSigB term 1 (fun j => andB (hW j) (hM j))
  have hx := xorListB (A := A ∪ Set.range term) ((List.finRange k).map term)
    (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr ⟨j, rfl⟩)
    (Or.inl hfalse)
  have heq : (fun x => foldXor ((List.finRange k).map term) (fun f => f x)) =
      fun x => parityK k (W x &&& M x) := by
    funext x
    rw [foldXor_map]
    have hfin : (List.finRange k).map Fin.val = List.range k := by apply List.ext_getElem <;> simp
    change foldXor (List.finRange k) (fun j => (W x).testBit j.val && (M x).testBit j.val) =
      foldXor (List.range k) (fun j => (W x &&& M x).testBit j)
    rw [← hfin, foldXor_map]
    apply foldXor_congr
    intro j _
    exact (Nat.testBit_and (W x) (M x) j.val).symm
  rw [heq, List.length_map, List.length_finRange] at hx
  exact relaxB (seq2B ht hx) le_rfl Set.subset_union_right (by omega)

lemma adjRhs_eq_foldXor {k r m pos : Nat} (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool)
    (pref : Fin k → Bool) (i : Fin m) :
    adjRhs k r m pos A rhs pref i =
      xor (rhs i)
        (foldXor (List.finRange (unusedOf k r))
          (fun c =>
            if freeDim k r pos ≤ c.val then
              (A i).val.testBit (4 * r - 3 + c.val) &&
                (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false)
            else false)) := by
  dsimp only [adjRhs]
  congr 1
  have hgen : ∀ (l : List (Fin (unusedOf k r))) (init : Bool),
      l.foldl (fun acc c =>
        if freeDim k r pos ≤ c.val then
          xor acc ((A i).val.testBit (4 * r - 3 + c.val) &&
            (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false))
        else acc) init =
      l.foldl (fun acc c =>
        xor acc (if freeDim k r pos ≤ c.val then
          (A i).val.testBit (4 * r - 3 + c.val) &&
            (if h : 4 * r - 3 + c.val < k then pref ⟨4 * r - 3 + c.val, h⟩ else false)
        else false)) init := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t ih =>
      intro init
      simp only [List.foldl_cons]
      by_cases h : freeDim k r pos ≤ a.val
      · simp only [h, ↓reduceIte]; exact ih _
      · simp only [h, ↓reduceIte, Bool.xor_false]; exact ih _
  exact hgen (List.finRange (unusedOf k r)) false

lemma countQueryB {N k r m pos : Nat} (hr : 4 ≤ r) (hkpos : 0 < k) (_hpos : pos ≤ k)
    {Base : Set (Sig N)}
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (sched : (Fin N → Bool) → Nat → Fin (2 ^ k))
    (leftName rightName a b : (Fin N → Bool) → Nat)
    (A : (Fin N → Bool) → Fin m → Fin (2 ^ k))
    (rhs : (Fin N → Bool) → Fin m → Bool)
    (pref : (Fin N → Bool) → Fin k → Bool)
    (hA : ∀ i : Fin m, ∀ j : Fin k, bitsOf k (fun x => (A x i).val) j ∈ Base)
    (hrhs : ∀ i : Fin m, (fun x => rhs x i) ∈ Base)
    (hpref : ∀ j : Fin k, (fun x => pref x j) ∈ Base)
    (hw0 : ∀ label : Fin (2 ^ swOf k r), ∀ j : Fin k,
      bitsOf k (fun x => decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val) j ∈ Base)
    (hpass : ∀ label : Fin (2 ^ swOf k r),
      (fun x => passSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val) ∈ Base)
    (hbasePar : ∀ (label : Fin (2 ^ swOf k r)) (i : Fin m),
      (fun x => parityK k (decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val &&& (A x i).val)) ∈ Base)
    (hgUsed : ∀ row : Fin m, (fun x => (gElim (matAt k r m pos (A x))).1 row) ∈ Base)
    (hgPay : ∀ row i : Fin m, (fun x => (gElim (matAt k r m pos (A x))).2.2 row i) ∈ Base)
    (hpow2 : ∀ j : Fin (k + 1),
      (fun x => pow2Nullity (k + 1) (freeDim k r pos) (gElim (matAt k r m pos (A x))).1 j) ∈ Base) :
    Build Base
      (Set.range (bitsOf (k + 1) (fun x =>
        countSpec k r m pos (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (pref x))))
      (2 ^ swOf k r * (24 * (k + m + 1) ^ 2)) := by
  have hsum := dims_sum k r hr
  have hun_le : unusedOf k r ≤ k := by omega
  have hfd_lt : freeDim k r pos < k + 1 := by
    have : freeDim k r pos ≤ unusedOf k r := Nat.min_le_left _ _
    omega
  let adjS : Fin m → Sig N := fun i x => adjRhs k r m pos (A x) (rhs x) (pref x) i
  have hadjB : Build Base (Set.range adjS) (m * (5 * k + 4)) := by
    refine finSigB adjS (5 * k + 4) (fun i => ?_)
    let term : Fin (unusedOf k r) → Sig N := fun c x =>
      if freeDim k r pos ≤ c.val then
        (A x i).val.testBit (4 * r - 3 + c.val) &&
          (if h : 4 * r - 3 + c.val < k then pref x ⟨4 * r - 3 + c.val, h⟩ else false)
      else false
    have htermB : Build Base (Set.range term) (unusedOf k r * 1) := by
      refine finSigB term 1 (fun c => ?_)
      by_cases hcf : freeDim k r pos ≤ c.val
      · by_cases hck : 4 * r - 3 + c.val < k
        · have heq : term c = fun x => bitsOf k (fun x => (A x i).val) ⟨4 * r - 3 + c.val, hck⟩ x &&
              pref x ⟨4 * r - 3 + c.val, hck⟩ := by
            funext x; simp [term, hcf, hck, bitsOf]
          rw [heq]; exact andB (hA i ⟨4 * r - 3 + c.val, hck⟩) (hpref ⟨4 * r - 3 + c.val, hck⟩)
        · have heq : term c = fun _ => false := by funext x; simp [term, hcf, hck]
          rw [heq]; exact relaxB (idleB (Set.singleton_subset_iff.mpr hfalse)) le_rfl Set.subset_union_right (by omega)
      · have heq : term c = fun _ => false := by funext x; simp [term, hcf]
        rw [heq]; exact relaxB (idleB (Set.singleton_subset_iff.mpr hfalse)) le_rfl Set.subset_union_right (by omega)
    have hxor := xorListB (A := Base ∪ Set.range term) ((List.finRange (unusedOf k r)).map term)
      (fun f hf => by rcases List.mem_map.mp hf with ⟨c, _, rfl⟩; exact Or.inr ⟨c, rfl⟩)
      (Or.inl hfalse)
    rw [List.length_map, List.length_finRange] at hxor
    have hfin := xorB (A := Base ∪ {fun x => foldXor ((List.finRange (unusedOf k r)).map term) (fun f => f x)})
      (Or.inl (hrhs i)) (Or.inr rfl)
    have heq : (fun x => xor (rhs x i) (foldXor ((List.finRange (unusedOf k r)).map term) (fun f => f x))) = adjS i := by
      funext x
      dsimp only [adjS]
      rw [foldXor_map, adjRhs_eq_foldXor]
    rw [heq] at hfin
    exact relaxB (seq2B (seq2B htermB hxor) hfin) le_rfl Set.subset_union_right (by omega)
  let A1 := Base ∪ Set.range adjS
  let contrib : Fin (2 ^ swOf k r) → (Fin N → Bool) → Nat := fun label x =>
    let st := gElim (matAt k r m pos (A x))
    let usedCard := (Finset.univ.filter (fun row : Fin m => st.1 row = true)).card
    if seedOk k r m pos (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (pref x) label.val then
      2 ^ (freeDim k r pos - usedCard)
    else 0
  have hcontribB : ∀ label : Fin (2 ^ swOf k r),
      Build A1 (Set.range (bitsOf (k + 1) (contrib label))) (7 * k + 8 * m + 5 * m * m + 3) := by
    intro label
    let pmBit : Fin k → Sig N := fun j x =>
      !(decide (pos ≤ j.val) && !(decide (4 * r - 3 ≤ j.val ∧ j.val < 4 * r - 3 + unusedOf k r))) ||
        ((decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val).testBit j.val == pref x j)
    have hpmBitB : Build A1 (Set.range pmBit) (k * 5) := by
      refine finSigB pmBit 5 (fun j => ?_)
      by_cases hcond : pos ≤ j.val ∧ ¬(4 * r - 3 ≤ j.val ∧ j.val < 4 * r - 3 + unusedOf k r)
      · have heq : pmBit j = fun x =>
            bitsOf k (fun x => decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val) j x == pref x j := by
          funext x
          dsimp only [pmBit, bitsOf]
          rw [decide_eq_true hcond.1, decide_eq_false hcond.2]
          simp
        rw [heq]
        exact eqBoolB (Or.inl (hw0 label j)) (Or.inl (hpref j))
      · have heq : pmBit j = fun _ => true := by
          funext x
          dsimp only [pmBit]
          by_cases h1 : pos ≤ j.val
          · have h2 : 4 * r - 3 ≤ j.val ∧ j.val < 4 * r - 3 + unusedOf k r := by tauto
            simp [h1, h2]
          · simp [h1]
        rw [heq]
        exact relaxB (idleB (Set.singleton_subset_iff.mpr (Or.inl htrue))) le_rfl Set.subset_union_right (by omega)
    let pmSig : Sig N := fun x =>
      prefMatch k r pos (decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val) (pref x)
    have hpmB : Build A1 {pmSig} (6 * k) := by
      have ha := andListB (A := A1 ∪ Set.range pmBit) ((List.finRange k).map pmBit)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨j, _, rfl⟩; exact Or.inr ⟨j, rfl⟩)
        (Or.inl (Or.inl htrue))
      have heq : (fun x => ((List.finRange k).map pmBit).all (fun f => f x)) = pmSig := by
        funext x; simp [pmSig, prefMatch, pmBit, List.all_map]; rfl
      rw [heq, List.length_map, List.length_finRange] at ha
      exact relaxB (seq2B hpmBitB ha) le_rfl Set.subset_union_right (by omega)
    let bvec : Fin m → Sig N := fun i x =>
      xor (parityK k (decodeSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val &&& (A x i).val))
        (adjRhs k r m pos (A x) (rhs x) (pref x) i)
    have hbvecB : Build A1 (Set.range bvec) (m * 4) :=
      finSigB bvec 4 (fun i => xorB (Or.inl (hbasePar label i)) (Or.inr ⟨i, rfl⟩))
    let A2 := A1 ∪ ({pmSig} ∪ Set.range bvec)
    have hstep1 : Build A1 ({pmSig} ∪ Set.range bvec) (6 * k + m * 4) := unionB hpmB hbvecB
    let rowOk : Fin m → Sig N := fun row x =>
      !(!((gElim (matAt k r m pos (A x))).1 row) &&
        bDot ((gElim (matAt k r m pos (A x))).2.2 row) (fun i => bvec i x))
    have hrowOkB : Build A2 (Set.range rowOk) (m * (5 * m + 3)) := by
      refine finSigB rowOk (5 * m + 3) (fun row => ?_)
      let term : Fin m → Sig N := fun i x => (gElim (matAt k r m pos (A x))).2.2 row i && bvec i x
      have ht : Build A2 (Set.range term) (m * 1) :=
        finSigB term 1 (fun i => andB (Or.inl (Or.inl (hgPay row i))) (Or.inr (Or.inr ⟨i, rfl⟩)))
      have hx := xorListB (A := A2 ∪ Set.range term) ((List.finRange m).map term)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨i, _, rfl⟩; exact Or.inr ⟨i, rfl⟩)
        (Or.inl (Or.inl (Or.inl hfalse)))
      have hdot_eq : (fun x => foldXor ((List.finRange m).map term) (fun f => f x)) =
          fun x => bDot ((gElim (matAt k r m pos (A x))).2.2 row) (fun i => bvec i x) := by
        funext x; rw [foldXor_map, bDot_eq_foldXor]
      rw [hdot_eq, List.length_map, List.length_finRange] at hx
      let dotS : Sig N := fun x => bDot ((gElim (matAt k r m pos (A x))).2.2 row) (fun i => bvec i x)
      have hdotB : Build A2 {dotS} (5 * m) := relaxB (seq2B ht hx) le_rfl Set.subset_union_right (by omega)
      have hn1 : Build (A2 ∪ {dotS}) {fun x => !((gElim (matAt k r m pos (A x))).1 row)} 1 :=
        notB (Or.inl (Or.inl (Or.inl (hgUsed row))))
      have ha1 : Build ((A2 ∪ {dotS}) ∪ {fun x => !((gElim (matAt k r m pos (A x))).1 row)})
          {fun x => !((gElim (matAt k r m pos (A x))).1 row) && dotS x} 1 :=
        andB (Or.inr rfl) (Or.inl (Or.inr rfl))
      have hn2 : Build (((A2 ∪ {dotS}) ∪ {fun x => !((gElim (matAt k r m pos (A x))).1 row)}) ∪
          {fun x => !((gElim (matAt k r m pos (A x))).1 row) && dotS x}) {rowOk row} 1 :=
        notB (Or.inr rfl)
      exact relaxB (seq2B hdotB (transB (transB (extB hn1) (extB ha1)) hn2)) le_rfl Set.subset_union_right (by omega)
    let consSig : Sig N := fun x =>
      seedCons k r m pos (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (pref x) label.val
    have hconsB : Build A2 {consSig} (m * (5 * m + 4)) := by
      have ha := andListB (A := A2 ∪ Set.range rowOk) ((List.finRange m).map rowOk)
        (fun f hf => by rcases List.mem_map.mp hf with ⟨row, _, rfl⟩; exact Or.inr ⟨row, rfl⟩)
        (Or.inl (Or.inl (Or.inl htrue)))
      have heq : (fun x => ((List.finRange m).map rowOk).all (fun f => f x)) = consSig := by
        funext x; simp [consSig, seedCons, rowOk, bvec, List.all_map]; rfl
      rw [heq, List.length_map, List.length_finRange] at ha
      exact relaxB (seq2B hrowOkB ha) le_rfl Set.subset_union_right (by ring_nf; omega)
    let ok1 : Sig N := fun x =>
      passSeed k r (sched x) (leftName x) (rightName x) (a x) (b x) label.val && pmSig x
    let okSig : Sig N := fun x =>
      seedOk k r m pos (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (pref x) label.val
    have hok1B : Build (A2 ∪ {consSig}) {ok1} 1 :=
      andB (Or.inl (Or.inl (Or.inl (hpass label)))) (Or.inl (Or.inr (Or.inl rfl)))
    have hok2B : Build ((A2 ∪ {consSig}) ∪ {ok1}) {okSig} 1 :=
      andB (Or.inr rfl) (Or.inl (Or.inr rfl))
    have hokB : Build A2 {okSig} (m * (5 * m + 4) + 2) :=
      relaxB (seq2B hconsB (seq2B hok1B hok2B)) le_rfl Set.subset_union_right (by omega)
    have hbitsB : Build (A2 ∪ {okSig}) (Set.range (bitsOf (k + 1) (contrib label))) (k + 1) := by
      have h1 := finSigB (bitsOf (k + 1) (contrib label)) 1 (fun j => by
        have heq : bitsOf (k + 1) (contrib label) j =
            fun x => okSig x && pow2Nullity (k + 1) (freeDim k r pos) (gElim (matAt k r m pos (A x))).1 j := by
          funext x
          dsimp only [bitsOf, contrib, okSig]
          have hle := (gElim_card_eq (matAt k r m pos (A x)) (fun _ => false)).1
          have hpn := pow2Nullity_spec (L := k + 1) (gElim (matAt k r m pos (A x))).1 hfd_lt hle j
          cases seedOk k r m pos (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (pref x) label.val
          · simp
          · simp [hpn]
        rw [heq]
        exact andB (A := A2 ∪ {okSig}) (Or.inr rfl) (Or.inl (Or.inl (Or.inl (hpow2 j)))))
      exact relaxB h1 le_rfl Set.subset_union_right (by omega)
    exact relaxB (seq2B hstep1 (seq2B hokB hbitsB)) le_rfl Set.subset_union_right (by ring_nf; omega)
  have hallC : Build A1 (⋃ label : Fin (2 ^ swOf k r), Set.range (bitsOf (k + 1) (contrib label)))
      (2 ^ swOf k r * (7 * k + 8 * m + 5 * m * m + 3)) :=
    finB (fun label => Set.range (bitsOf (k + 1) (contrib label))) (7 * k + 8 * m + 5 * m * m + 3) hcontribB
  have hsumB := sumListB (A := A1 ∪ ⋃ label : Fin (2 ^ swOf k r), Set.range (bitsOf (k + 1) (contrib label)))
    (k + 1) (Or.inl (Or.inl hfalse)) ((List.finRange (2 ^ swOf k r)).map contrib) (fun F hF j => by
      rcases List.mem_map.mp hF with ⟨label, _, rfl⟩
      exact Or.inr (Set.mem_iUnion.mpr ⟨label, ⟨j, rfl⟩⟩))
  have hsum_eq : sumListVal ((List.finRange (2 ^ swOf k r)).map contrib) =
      fun x => countSpec k r m pos (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (pref x) := by
    funext x
    rw [sumListVal_eq_sum, List.map_map]
    rfl
  rw [hsum_eq, List.length_map, List.length_finRange] at hsumB
  have hcost : m * (5 * k + 4) + (2 ^ swOf k r * (7 * k + 8 * m + 5 * m * m + 3) +
      2 ^ swOf k r * (9 * (k + 1))) ≤ 2 ^ swOf k r * (24 * (k + m + 1) ^ 2) := by
    have hpow1 : 1 ≤ 2 ^ swOf k r := Nat.one_le_two_pow
    have h1 : m * (5 * k + 4) ≤ 2 ^ swOf k r * (5 * k * m + 4 * m) := by
      calc m * (5 * k + 4) = 1 * (5 * k * m + 4 * m) := by ring
        _ ≤ 2 ^ swOf k r * (5 * k * m + 4 * m) := Nat.mul_le_mul_right _ hpow1
    have h2 : (5 * k * m + 4 * m) + (7 * k + 8 * m + 5 * m * m + 3) + 9 * (k + 1) ≤ 24 * (k + m + 1) ^ 2 := by
      have hsq : 24 * (k + m + 1) ^ 2 = 24 * (k * k) + 48 * (k * m) + 24 * (m * m) + 48 * k + 48 * m + 24 := by ring
      have hlhs : (5 * k * m + 4 * m) + (7 * k + 8 * m + 5 * m * m + 3) + 9 * (k + 1) =
          5 * (k * m) + 5 * (m * m) + 16 * k + 12 * m + 12 := by ring
      rw [hsq, hlhs]; omega
    calc m * (5 * k + 4) + (2 ^ swOf k r * (7 * k + 8 * m + 5 * m * m + 3) + 2 ^ swOf k r * (9 * (k + 1)))
        ≤ 2 ^ swOf k r * (5 * k * m + 4 * m) + (2 ^ swOf k r * (7 * k + 8 * m + 5 * m * m + 3) + 2 ^ swOf k r * (9 * (k + 1))) :=
          Nat.add_le_add_right h1 _
      _ = 2 ^ swOf k r * ((5 * k * m + 4 * m) + (7 * k + 8 * m + 5 * m * m + 3) + 9 * (k + 1)) := by ring
      _ ≤ 2 ^ swOf k r * (24 * (k + m + 1) ^ 2) := Nat.mul_le_mul_left _ h2
  exact relaxB (seq2B hadjB (seq2B hallC hsumB)) le_rfl Set.subset_union_right hcost

lemma countSpec_lt_pow {k r m pos : Nat} (hr : 4 ≤ r) (hkpos : 0 < k) (hpos : pos ≤ k)
    (sched : Nat → Fin (2 ^ k)) (leftName rightName : Fin (2 ^ k))
    (a b : Fin (2 ^ hOf k)) (A : Fin m → Fin (2 ^ k)) (rhs : Fin m → Bool) (pref : Fin k → Bool) :
    countSpec k r m pos sched leftName.val rightName.val a.val b.val A rhs pref < 2 ^ (k + 1) := by
  rw [countSpec_eq_filter_length hr hkpos hpos sched leftName rightName a b A rhs pref]
  have h2 : 2 ^ k < 2 ^ (k + 1) := by rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
  exact lt_of_le_of_lt ((List.length_filter_le _ _).trans ((List.length_filter_le _ _).trans (by rw [List.length_range]))) h2

def selSigs {N k : Nat} (st : (Fin N → Bool) → (Fin k → Bool) × Nat) : Set (Sig N) :=
  Set.range (fun j : Fin k => fun x => (st x).1 j) ∪
  Set.range (bitsOf (k + 1) (fun x => (st x).2))

lemma selectRunB {N k r m : Nat} (hr : 4 ≤ r) (hkpos : 0 < k)
    {Base : Set (Sig N)}
    (hfalse : (fun _ => false) ∈ Base) (htrue : (fun _ => true) ∈ Base)
    (sched : (Fin N → Bool) → Nat → Fin (2 ^ k))
    (leftName rightName : (Fin N → Bool) → Fin (2 ^ k))
    (a b : (Fin N → Bool) → Fin (2 ^ hOf k))
    (A : (Fin N → Bool) → Fin m → Fin (2 ^ k))
    (rhs : (Fin N → Bool) → Fin m → Bool)
    (rank : (Fin N → Bool) → Fin (2 ^ k))
    (hA : ∀ i : Fin m, ∀ j : Fin k, bitsOf k (fun x => (A x i).val) j ∈ Base)
    (hrhs : ∀ i : Fin m, (fun x => rhs x i) ∈ Base)
    (hrank : ∀ j : Fin k, bitsOf k (fun x => (rank x).val) j ∈ Base)
    (hw0 : ∀ label : Fin (2 ^ swOf k r), ∀ j : Fin k,
      bitsOf k (fun x => decodeSeed k r (sched x) (leftName x).val (rightName x).val (a x).val (b x).val label.val) j ∈ Base)
    (hpass : ∀ label : Fin (2 ^ swOf k r),
      (fun x => passSeed k r (sched x) (leftName x).val (rightName x).val (a x).val (b x).val label.val) ∈ Base)
    (hbasePar : ∀ (label : Fin (2 ^ swOf k r)) (i : Fin m),
      (fun x => parityK k (decodeSeed k r (sched x) (leftName x).val (rightName x).val (a x).val (b x).val label.val &&& (A x i).val)) ∈ Base)
    (hgUsed : ∀ pos : Fin (k + 1), ∀ row : Fin m, (fun x => (gElim (matAt k r m pos.val (A x))).1 row) ∈ Base)
    (hgPay : ∀ pos : Fin (k + 1), ∀ row i : Fin m, (fun x => (gElim (matAt k r m pos.val (A x))).2.2 row i) ∈ Base)
    (hpow2 : ∀ pos : Fin (k + 1), ∀ j : Fin (k + 1),
      (fun x => pow2Nullity (k + 1) (freeDim k r pos.val) (gElim (matAt k r m pos.val (A x))).1 j) ∈ Base) :
    let cnt : (Fin N → Bool) → Nat → (Fin k → Bool) → Nat := fun x pos pref =>
      countSpec k r m pos (sched x) (leftName x).val (rightName x).val (a x).val (b x).val (A x) (rhs x) pref
    Build Base (selSigs (fun x => selectRun k (cnt x) (rank x).val))
      (k * (2 ^ swOf k r * (54 * (k + m + 1) ^ 2))) := by
  intro cnt
  have hloop : ∀ t ≤ k,
      let st : (Fin N → Bool) → (Fin k → Bool) × Nat := fun x =>
        (List.range t).foldl (fun st s => selectStep k (cnt x) s st) (fun _ => false, (rank x).val)
      (∀ x, (st x).2 < 2 ^ (k + 1)) ∧
      Build Base (selSigs st) (t * (2 ^ swOf k r * (54 * (k + m + 1) ^ 2))) := by
    intro t
    induction t with
    | zero =>
      intro _
      refine ⟨fun x => lt_of_lt_of_le (rank x).isLt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)), ?_⟩
      simp only [Nat.zero_mul]
      apply idleB
      rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact hfalse
      · by_cases hjk : j.val < k
        · exact hrank ⟨j.val, hjk⟩
        · have heq : bitsOf (k + 1) (fun x => (rank x).val) j = fun _ => false := by
            funext x; dsimp only [bitsOf]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (rank x).isLt
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
          dsimp only [List.range_zero, List.foldl_nil]
          rw [heq]; exact hfalse
    | succ t ih =>
      intro ht
      rcases ih (by omega) with ⟨hremLt, hprev⟩
      set st : (Fin N → Bool) → (Fin k → Bool) × Nat := fun x =>
        (List.range t).foldl (fun st s => selectStep k (cnt x) s st) (fun _ => false, (rank x).val)
      have hnext_eq : (fun x => (List.range (t + 1)).foldl (fun st s => selectStep k (cnt x) s st)
          (fun _ => false, (rank x).val)) = fun x => selectStep k (cnt x) t (st x) := by
        funext x; simp [List.range_succ, List.foldl_append, st]
      rw [hnext_eq]
      have htk : t < k := by omega
      set pos := k - 1 - t
      have hpos_le : pos ≤ k := by dsimp only [pos]; omega
      have hpos_lt : pos < k + 1 := by omega
      let prefL : (Fin N → Bool) → Fin k → Bool := fun x j => if j.val = pos then false else (st x).1 j
      let leftCnt : (Fin N → Bool) → Nat := fun x => cnt x pos (prefL x)
      let goRight : Sig N := fun x => !(decide ((st x).2 < leftCnt x))
      let subVal : (Fin N → Bool) → Nat := fun x => ((st x).2 + (2 ^ (k + 1) - 1 - leftCnt x + 1)) % 2 ^ (k + 1)
      let rem' : (Fin N → Bool) → Nat := fun x => if goRight x then subVal x else (st x).2
      have hrem'_lt : ∀ x, (selectStep k (cnt x) t (st x)).2 < 2 ^ (k + 1) := by
        intro x
        dsimp only [selectStep]
        simp only [htk, ↓reduceIte]
        split_ifs
        · exact Nat.mod_lt _ (Nat.two_pow_pos _)
        · exact hremLt x
      refine ⟨hrem'_lt, ?_⟩
      let A1 := Base ∪ selSigs st
      have hprefL_mem : ∀ j : Fin k, (fun x => prefL x j) ∈ A1 := by
        intro j
        by_cases hjp : j.val = pos
        · have heq : (fun x => prefL x j) = fun _ => false := by funext x; simp [prefL, hjp]
          rw [heq]; exact Or.inl hfalse
        · have heq : (fun x => prefL x j) = fun x => (st x).1 j := by funext x; simp [prefL, hjp]
          rw [heq]; exact Or.inr (Or.inl ⟨j, rfl⟩)
      have hqB : Build A1 (Set.range (bitsOf (k + 1) leftCnt)) (2 ^ swOf k r * (24 * (k + m + 1) ^ 2)) :=
        countQueryB hr hkpos hpos_le (Or.inl hfalse) (Or.inl htrue)
          sched (fun x => (leftName x).val) (fun x => (rightName x).val)
          (fun x => (a x).val) (fun x => (b x).val) A rhs prefL
          (fun i j => Or.inl (hA i j)) (fun i => Or.inl (hrhs i)) hprefL_mem
          (fun label j => Or.inl (hw0 label j)) (fun label => Or.inl (hpass label))
          (fun label i => Or.inl (hbasePar label i))
          (fun row => Or.inl (hgUsed ⟨pos, hpos_lt⟩ row))
          (fun row i => Or.inl (hgPay ⟨pos, hpos_lt⟩ row i))
          (fun j => Or.inl (hpow2 ⟨pos, hpos_lt⟩ j))
      have hlc_lt : ∀ x, leftCnt x < 2 ^ (k + 1) := fun x =>
        countSpec_lt_pow hr hkpos hpos_le (sched x) (leftName x) (rightName x) (a x) (b x) (A x) (rhs x) (prefL x)
      let A2 := A1 ∪ Set.range (bitsOf (k + 1) leftCnt)
      have hltB : Build A2 {fun x => decide ((st x).2 < leftCnt x)} (5 * (k + 1)) :=
        ltB (k + 1) (fun x => (st x).2) leftCnt (Or.inl (Or.inl hfalse))
          (fun j => Or.inl (Or.inr (Or.inr ⟨j, rfl⟩)))
          (fun j => Or.inr ⟨j, rfl⟩) hremLt hlc_lt
      have hgrB : Build A2 {goRight} (5 * (k + 1) + 1) :=
        seq2B hltB (notB (Or.inr rfl))
      have hsubB : Build A2 (Set.range (bitsOf (k + 1) subVal)) (19 * (k + 1)) :=
        subModB (k + 1) (fun x => (st x).2) leftCnt (Or.inl (Or.inl hfalse)) (Or.inl (Or.inl htrue))
          (fun j => Or.inl (Or.inr (Or.inr ⟨j, rfl⟩)))
          (fun j => Or.inr ⟨j, rfl⟩) hlc_lt
      have hgsB := unionB hgrB hsubB
      let A3 := A2 ∪ ({goRight} ∪ Set.range (bitsOf (k + 1) subVal))
      have hremB : Build A3 (Set.range (bitsOf (k + 1) rem')) ((k + 1) * 4) := by
        refine finSigB (bitsOf (k + 1) rem') 4 (fun j => ?_)
        have heq : bitsOf (k + 1) rem' j =
            fun x => if goRight x then bitsOf (k + 1) subVal j x else bitsOf (k + 1) (fun x => (st x).2) j x := by
          funext x; dsimp only [bitsOf, rem']; cases goRight x <;> rfl
        rw [heq]
        exact iteB (Or.inr (Or.inl rfl)) (Or.inr (Or.inr ⟨j, rfl⟩)) (Or.inl (Or.inl (Or.inr (Or.inr ⟨j, rfl⟩))))
      have hstep : Build A1 (selSigs (fun x => selectStep k (cnt x) t (st x)))
          (2 ^ swOf k r * (54 * (k + m + 1) ^ 2)) := by
        have hcost : 2 ^ swOf k r * (24 * (k + m + 1) ^ 2) +
            ((5 * (k + 1) + 1 + 19 * (k + 1)) + (k + 1) * 4) ≤ 2 ^ swOf k r * (54 * (k + m + 1) ^ 2) := by
          have hpow1 : 1 ≤ 2 ^ swOf k r := Nat.one_le_two_pow
          have h1 : (5 * (k + 1) + 1 + 19 * (k + 1)) + (k + 1) * 4 ≤ 30 * (k + m + 1) ^ 2 := by
            have hsq : (k + m + 1) ^ 2 = k * k + 2 * k * m + m * m + 2 * k + 2 * m + 1 := by ring
            rw [hsq]; omega
          calc 2 ^ swOf k r * (24 * (k + m + 1) ^ 2) + ((5 * (k + 1) + 1 + 19 * (k + 1)) + (k + 1) * 4)
              ≤ 2 ^ swOf k r * (24 * (k + m + 1) ^ 2) + 1 * (30 * (k + m + 1) ^ 2) := by omega
            _ ≤ 2 ^ swOf k r * (24 * (k + m + 1) ^ 2) + 2 ^ swOf k r * (30 * (k + m + 1) ^ 2) :=
                Nat.add_le_add_left (Nat.mul_le_mul_right _ hpow1) _
            _ = 2 ^ swOf k r * (54 * (k + m + 1) ^ 2) := by ring
        refine relaxB (seq2B hqB (seqB hgsB hremB)) le_rfl ?_ hcost
        rintro f (⟨j, rfl⟩ | ⟨j, rfl⟩)
        · dsimp only
          by_cases hjp : j.val = pos
          · have heq : (fun x => (selectStep k (cnt x) t (st x)).1 j) = goRight := by
              funext x; simp [selectStep, htk, pos, hjp, goRight, leftCnt, prefL]
            rw [heq]; exact Or.inr (Or.inl (Or.inl rfl))
          · have heq : (fun x => (selectStep k (cnt x) t (st x)).1 j) = fun x => (st x).1 j := by
              funext x; simp [selectStep, htk, pos, hjp]
            rw [heq]; exact Or.inl (Or.inr (Or.inl ⟨j, rfl⟩))
        · have heq : bitsOf (k + 1) (fun x => (selectStep k (cnt x) t (st x)).2) j = bitsOf (k + 1) rem' j := by
            funext x; simp [bitsOf, selectStep, htk, pos, rem', goRight, subVal, leftCnt, prefL]
          rw [heq]; exact Or.inr (Or.inr ⟨j, rfl⟩)
      exact relaxB (seq2B hprev hstep) le_rfl Set.subset_union_right (by exact le_of_eq (by ring))
  exact (hloop k le_rfl).2

def readNat {n : Nat} (x : Fin n → Bool) (off len : Nat) : Nat :=
  (List.range len).foldl (fun acc j =>
    acc ||| ((if h : off + j < n then x ⟨off + j, h⟩ else false).toNat <<< j)) 0

lemma readNat_spec {n : Nat} (x : Fin n → Bool) (off len : Nat) :
    readNat x off len < 2 ^ len ∧
    ∀ j < len, (readNat x off len).testBit j =
      if h : off + j < n then x ⟨off + j, h⟩ else false := by
  let bitFn : Nat → Bool := fun j => if h : off + j < n then x ⟨off + j, h⟩ else false
  have htake : ∀ m ≤ len,
      let v := (List.range m).foldl (fun acc j => acc ||| ((bitFn j).toNat <<< j)) 0
      (∀ b, m ≤ b → v.testBit b = false) ∧ (∀ b < m, v.testBit b = bitFn b) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨fun _ _ => by simp, fun _ hb => by omega⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      dsimp only
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      refine ⟨?_, ?_⟩
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft, hprev.1 b (by omega)]
        have hlt2 : (bitFn m).toNat < 2 ^ (b - m) := by
          have hle1 : (bitFn m).toNat ≤ 1 := by cases bitFn m <;> decide
          have hpow : 2 ≤ 2 ^ (b - m) := Nat.le_self_pow (by omega) 2
          omega
        rw [decide_eq_true (by omega : m ≤ b), Bool.true_and, Nat.testBit_eq_false_of_lt hlt2, Bool.or_false]
      · intro b hb
        rw [Nat.testBit_lor, Nat.testBit_shiftLeft]
        by_cases hbm : b < m
        · rw [hprev.2 b hbm, decide_eq_false (by omega : ¬ m ≤ b), Bool.false_and, Bool.or_false]
        · have hbe : b = m := by omega
          subst hbe
          rw [hprev.1 b (le_refl _), decide_eq_true (le_refl _), Bool.true_and, Bool.false_or, Nat.sub_self]
          cases bitFn b <;> decide
  have hfull := htake len le_rfl
  refine ⟨?_, hfull.2⟩
  apply Nat.lt_pow_two_of_testBit
  intro b hb
  exact hfull.1 b hb

lemma readNat_eq_of_bits {n : Nat} (x : Fin n → Bool) (off len val : Nat)
    (hlen : off + len ≤ n) (hval : val < 2 ^ len)
    (hbits : ∀ j (hj : j < len), x ⟨off + j, by omega⟩ = val.testBit j) :
    readNat x off len = val := by
  have hsp := readNat_spec x off len
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < len
  · rw [hsp.2 j hj]
    have hlt : off + j < n := by omega
    simp only [hlt, ↓reduceDIte]
    exact hbits j hj
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hsp.1 (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hval (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]

lemma length_flatMap_const {α β : Type*} (l : List α) (f : α → List β) (d : Nat)
    (hfd : ∀ a ∈ l, (f a).length = d) : (l.flatMap f).length = l.length * d := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.flatMap_cons, List.length_append, hfd a List.mem_cons_self,
      ih (fun b hb => hfd b (List.mem_cons_of_mem a hb)), List.length_cons, Nat.succ_mul]
    omega

lemma getD_flatMap_const {α : Type*} (l : List α) (f : α → List Bool) (d : Nat)
    (hfd : ∀ a ∈ l, (f a).length = d) (i j : Nat) (hi : i < l.length) (hj : j < d) :
    (l.flatMap f).getD (i * d + j) false = (f (l[i]'hi)).getD j false := by
  induction l generalizing i with
  | nil => cases hi
  | cons a t ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_append _ _ _ _ (by rw [hfd a List.mem_cons_self]; exact hj)]
    | succ i =>
      have hlen_a : (f a).length = d := hfd a List.mem_cons_self
      have hge : (f a).length ≤ (i + 1) * d + j := by rw [hlen_a, Nat.succ_mul]; omega
      rw [List.getD_append_right _ _ _ _ hge]
      have hsub : (i + 1) * d + j - (f a).length = i * d + j := by rw [hlen_a, Nat.succ_mul]; omega
      rw [hsub]
      exact ih (fun b hb => hfd b (List.mem_cons_of_mem a hb)) i (by simp at hi; omega)

lemma stateN_congr_sched {k r : Nat} (c1 c2 : Nat → Fin (2 ^ k))
    (hc : ∀ t, 1 ≤ t → t ≤ 2 * r → c1 t = c2 t)
    (side : Bool) (key name : Nat) :
    ∀ t ≤ r, stateN k r c1 side key name t = stateN k r c2 side key name t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [stateN_succ, stateN_succ, ih (by omega)]
    dsimp only [stepK]
    rw [hc (if side then r + (t + 1) else t + 1)
      (by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)
      (by cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega)]

lemma ofFn_getD_eq {n : Nat} (l : List Bool) (hl : l.length = n) :
    List.ofFn (fun i : Fin n => l.getD i.val false) = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro i h1 h2
    simp only [List.getElem_ofFn]
    exact List.getD_eq_getElem l false h2

lemma main_k0 (r m : Nat) (hr : 4 ≤ r) :
    let k := 0
    let h := (k+1)/2
    let z := k-h
    let u := 5*r-3
    let extra := min (r-2) (z-6*r)
    let seedWidth := min k u + extra
    let rot := fun (offset x : Nat) =>
      ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
    let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
    let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
      acc ||| ((xor (word.testBit site)
        (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
    let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
      chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
        (constants (if col then r+t else t)).val
    let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
      (List.range r).foldl (fun v tick => step c side key v (tick+1))
        (rot (if side then 3 else 1) key ^^^ name)
    let n := 2*r*k+3*k+2*h+m*(k+1)
    let bits := fun (len data : Nat) => (List.range len).map (fun pos => data.testBit pos)
    let parity := fun (natWord : Nat) => (List.range k).foldl
      (fun total bitPos => xor total (natWord.testBit bitPos)) false
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
        (countWire : Fin (k+1) → Fin (n+C.size)) (keyWire : Fin k → Fin (n+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.output < n+C.size ∧ C.size ≤ 1048576*(k+m+1)^5*(r+1)*2^seedWidth ∧
      ∀ (schedule : Nat → Fin (2^k)) (leftName rightName : Fin (2^k))
          (a b : Fin (2^h)) (A : Fin m → Fin (2^k)) (rhs : Fin m → Bool)
          (rank : Fin (2^k)),
        let input := (List.range (2*r)).flatMap (fun idx => bits k (schedule (idx+1)).val) ++
          bits k leftName.val ++ bits k rightName.val ++ bits h a.val ++ bits h b.val ++
          (List.ofFn A).flatMap (fun entry => bits k entry.val) ++ List.ofFn rhs ++ bits k rank.val
        let solutions := (List.range (2^k)).filter (fun w => decide (
          state schedule false w leftName.val >>> z = a.val ∧
          state schedule true w rightName.val >>> z = b.val ∧
          ∀ i : Fin m, parity (w &&& (A i).val) = rhs i))
        C.eval input = decide (rank.val < solutions.length) ∧
        (∀ j : Fin (k+1), (C.wires input).getD (countWire j).val false = solutions.length.testBit j.val) ∧
        (∀ d : Fin k, (C.wires input).getD (keyWire d).val false =
          ((solutions.getD rank.val 0).testBit d.val)) := by
  intro k h z u extra seedWidth rot mix chi step state n bits parity
  have hn : n = m := by dsimp only [n, h, k]; omega
  let Base0 : Set (Sig n) := Set.range (fun i : Fin n => fun x : Fin n → Bool => x i)
  have hcf : Build Base0 {fun _ => false} 1 := constB false
  let xs : List (Sig n) := (List.finRange n).map (fun i x => x i)
  have hor : Build (Base0 ∪ {fun _ => false}) {fun x => xs.any (fun f => f x)} n := by
    have h1 := orListB (A := Base0 ∪ {fun _ => false}) xs
      (fun f hf => by rcases List.mem_map.mp hf with ⟨i, _, rfl⟩; exact Or.inl ⟨i, rfl⟩)
      (Or.inr rfl)
    rw [List.length_map, List.length_finRange] at h1
    exact h1
  let outSig : Sig n := fun x => !(xs.any (fun f => f x))
  have hnot : Build ((Base0 ∪ {fun _ => false}) ∪ {fun x => xs.any (fun f => f x)}) {outSig} 1 :=
    notB (Or.inr rfl)
  have hB : Build Base0 {outSig} (1 + n + 1) :=
    relaxB (seq2B hcf (seq2B hor hnot)) le_rfl Set.subset_union_right (by omega)
  obtain ⟨sz, hsz_le, hsched⟩ := hB 0 Base0 (startSched n) le_rfl
  rw [Nat.zero_add] at hsched
  obtain ⟨C, countWire, keyWire, hfan, hrb, hout, hcsz, hev⟩ :=
    finishOutputs hsched outSig (Or.inr rfl) (fun _ => outSig) (fun _ => Or.inr rfl)
      (fun d => d.elim0) (fun d => d.elim0)
  have hbudget : C.size ≤ 1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ seedWidth := by
    have hsw0 : seedWidth = 0 := by dsimp only [seedWidth, extra, u, z, h, k]; omega
    have h1 : 1 ≤ (m + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h2 : m + 2 ≤ 1048576 * (m + 1) ^ 5 := by
      calc m + 2 ≤ 2 * (m + 1) := by omega
        _ = 2 * (m + 1) * 1 := by ring
        _ ≤ 1048576 * (m + 1) * (m + 1) ^ 4 :=
            Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) h1
        _ = 1048576 * (m + 1) ^ 5 := by ring
    have h3 : 1048576 * (m + 1) ^ 5 ≤ 1048576 * (m + 1) ^ 5 * (r + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    rw [hcsz, hsw0]
    dsimp only [k]
    simp only [Nat.zero_add, pow_zero, mul_one]
    omega
  refine ⟨C, countWire, keyWire, hfan, hrb, hout, hbudget, ?_⟩
  intro schedule leftName rightName a b A rhs rank input solutions
  have hinp_eq : input = List.ofFn rhs := by
    have hh0 : h = 0 := by decide
    have hbits_k : ∀ d, bits k d = [] := fun _ => rfl
    have hbits_h : ∀ d, bits h d = [] := fun d => by rw [hh0]; rfl
    have hfl : ∀ {α : Type} (l : List α), l.flatMap (fun _ => ([] : List Bool)) = [] := fun l => by
      induction l with
      | nil => rfl
      | cons _ _ ih => exact ih
    dsimp only [input]
    simp [hbits_k, hbits_h, hfl]
  have hlen_inp : input.length = n := by rw [hinp_eq, List.length_ofFn, hn]
  let x : Fin n → Bool := fun i => input.getD i.val false
  have hof : List.ofFn x = input := ofFn_getD_eq input hlen_inp
  have hx_rhs : ∀ i : Fin m, x ⟨i.val, by omega⟩ = rhs i := by
    intro i; dsimp only [x]; rw [hinp_eq, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hst0 : ∀ side key name, state schedule side key name = 0 := by
    intro side key name
    have hstep0 : ∀ col raw prev t, step schedule col raw prev t = 0 := by
      intro col raw prev t
      have hc0 : (schedule (if col then r + t else t)).val = 0 := by
        have := (schedule (if col then r + t else t)).isLt; dsimp only [k] at this; omega
      have hr0 : ∀ o v, rot o v = 0 := fun o v => by dsimp only [rot, k]; simp [Nat.mod_one]
      dsimp only [step, chi, k]; rw [hr0, hc0]; simp
    dsimp only [state]
    have hlr : (List.range r).foldl (fun v tick => step schedule side key v (tick + 1))
        (rot (if side then 3 else 1) key ^^^ name) =
        step schedule side key
          ((List.range (r - 1)).foldl (fun v tick => step schedule side key v (tick + 1))
            (rot (if side then 3 else 1) key ^^^ name)) r := by
      have hre : r = (r - 1) + 1 := by omega
      conv_lhs => rw [hre]
      rw [List.range_succ, List.foldl_append]
      simp [← hre]
    rw [hlr, hstep0]
  have hsol_eq : solutions = if outSig x then [0] else [] := by
    have ha0 : a.val = 0 := by have := a.isLt; dsimp only [h, k] at this; omega
    have hb0 : b.val = 0 := by have := b.isLt; dsimp only [h, k] at this; omega
    have hout_iff : outSig x = true ↔ ∀ i : Fin m, rhs i = false := by
      dsimp only [outSig, xs]
      simp only [Bool.not_eq_true', List.any_eq_false, List.mem_map, List.mem_finRange, true_and,
        forall_exists_index, forall_apply_eq_imp_iff]
      constructor
      · intro h i; have := h ⟨i.val, by omega⟩; rw [hx_rhs i] at this; exact Bool.eq_false_iff.mpr this
      · intro h i
        have hi : i.val < m := by omega
        have := h ⟨i.val, hi⟩
        have hxi := hx_rhs ⟨i.val, hi⟩
        simpa using hxi.trans this
    dsimp only [solutions]
    have hr1 : List.range (2 ^ k) = [0] := rfl
    rw [hr1, List.filter_cons, List.filter_nil]
    have hpar0 : ∀ w, parity w = false := fun _ => rfl
    by_cases hall : ∀ i : Fin m, rhs i = false
    · have hout_t : outSig x = true := hout_iff.mpr hall
      simp [hout_t, hst0, ha0, hb0, hpar0, hall]
    · have hout_f : outSig x = false := by
        cases h' : outSig x
        · rfl
        · exact absurd (hout_iff.mp h') hall
      have hnd : ¬(state schedule false 0 leftName.val >>> z = a.val ∧
          state schedule true 0 rightName.val >>> z = b.val ∧
          ∀ i : Fin m, parity (0 &&& (A i).val) = rhs i) := by
        rintro ⟨_, _, hall'⟩
        apply hall; intro i; exact (hall' i).symm.trans (hpar0 _)
      rw [decide_eq_false hnd, hout_f]
  have hrank0 : rank.val = 0 := by have := rank.isLt; dsimp only [k] at this; omega
  have hevx := hev x
  rw [hof] at hevx
  refine ⟨?_, ?_, fun d => Fin.elim0 d⟩
  · rw [hevx.1, hsol_eq, hrank0]
    cases outSig x <;> decide
  · intro j
    have hj0 : j.val = 0 := by have := j.isLt; dsimp only [k] at this; omega
    rw [hevx.2.1 j, hsol_eq, hj0]
    cases outSig x <;> decide

lemma main_29729 : ∀ (k r m : Nat), 4 ≤ r →
    let h := (k+1)/2
    let z := k-h
    let u := 5*r-3
    let extra := min (r-2) (z-6*r)
    let seedWidth := min k u + extra
    let rot := fun (offset x : Nat) =>
      ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
    let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
    let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
      acc ||| ((xor (word.testBit site)
        (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
    let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
      chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
        (constants (if col then r+t else t)).val
    let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
      (List.range r).foldl (fun v tick => step c side key v (tick+1))
        (rot (if side then 3 else 1) key ^^^ name)
    let n := 2*r*k+3*k+2*h+m*(k+1)
    let bits := fun (len data : Nat) => (List.range len).map (fun pos => data.testBit pos)
    let parity := fun (natWord : Nat) => (List.range k).foldl
      (fun total bitPos => xor total (natWord.testBit bitPos)) false
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
        (countWire : Fin (k+1) → Fin (n+C.size)) (keyWire : Fin k → Fin (n+C.size)),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      C.output < n+C.size ∧ C.size ≤ 1048576*(k+m+1)^5*(r+1)*2^seedWidth ∧
      ∀ (schedule : Nat → Fin (2^k)) (leftName rightName : Fin (2^k))
          (a b : Fin (2^h)) (A : Fin m → Fin (2^k)) (rhs : Fin m → Bool)
          (rank : Fin (2^k)),
        let input := (List.range (2*r)).flatMap (fun idx => bits k (schedule (idx+1)).val) ++
          bits k leftName.val ++ bits k rightName.val ++ bits h a.val ++ bits h b.val ++
          (List.ofFn A).flatMap (fun entry => bits k entry.val) ++ List.ofFn rhs ++ bits k rank.val
        let solutions := (List.range (2^k)).filter (fun w => decide (
          state schedule false w leftName.val >>> z = a.val ∧
          state schedule true w rightName.val >>> z = b.val ∧
          ∀ i : Fin m, parity (w &&& (A i).val) = rhs i))
        C.eval input = decide (rank.val < solutions.length) ∧
        (∀ j : Fin (k+1), (C.wires input).getD (countWire j).val false = solutions.length.testBit j.val) ∧
        (∀ d : Fin k, (C.wires input).getD (keyWire d).val false =
          ((solutions.getD rank.val 0).testBit d.val)) := by
  intro k r m hr
  by_cases hk0 : k = 0
  · subst hk0; exact main_k0 r m hr
  · have hkpos : 0 < k := by omega
    intro h z u extra seedWidth rot mix chi step state n bits parity
    have hsum := dims_sum k r hr
    let Base0 : Set (Sig n) := Set.range (fun i : Fin n => fun x : Fin n → Bool => x i)
    have hconsts : Build Base0 ({fun _ => false} ∪ {fun _ => true}) 2 :=
      unionB (constB false) (constB true)
    let Base1 := Base0 ∪ ({fun _ => false} ∪ {fun _ => true})
    have hfalse1 : (fun _ => false) ∈ Base1 := Or.inr (Or.inl rfl)
    have htrue1 : (fun _ => true) ∈ Base1 := Or.inr (Or.inr rfl)
    let inSched : (Fin n → Bool) → Nat → Fin (2 ^ k) := fun x t =>
      if 1 ≤ t ∧ t ≤ 2 * r then ⟨readNat x ((t - 1) * k) k, (readNat_spec x _ k).1⟩
      else ⟨0, Nat.two_pow_pos k⟩
    let inLeft : (Fin n → Bool) → Fin (2 ^ k) := fun x =>
      ⟨readNat x (2 * r * k) k, (readNat_spec x _ k).1⟩
    let inRight : (Fin n → Bool) → Fin (2 ^ k) := fun x =>
      ⟨readNat x (2 * r * k + k) k, (readNat_spec x _ k).1⟩
    let inA : (Fin n → Bool) → Fin (2 ^ hOf k) := fun x =>
      ⟨readNat x (2 * r * k + 2 * k) (hOf k), (readNat_spec x _ (hOf k)).1⟩
    let inB : (Fin n → Bool) → Fin (2 ^ hOf k) := fun x =>
      ⟨readNat x (2 * r * k + 2 * k + hOf k) (hOf k), (readNat_spec x _ (hOf k)).1⟩
    let inMat : (Fin n → Bool) → Fin m → Fin (2 ^ k) := fun x i =>
      ⟨readNat x (2 * r * k + 2 * k + 2 * hOf k + i.val * k) k, (readNat_spec x _ k).1⟩
    let inRhs : (Fin n → Bool) → Fin m → Bool := fun x i =>
      if hi : 2 * r * k + 2 * k + 2 * hOf k + m * k + i.val < n then
        x ⟨2 * r * k + 2 * k + 2 * hOf k + m * k + i.val, hi⟩
      else false
    let inRank : (Fin n → Bool) → Fin (2 ^ k) := fun x =>
      ⟨readNat x (2 * r * k + 2 * k + 2 * hOf k + m * k + m) k, (readNat_spec x _ k).1⟩
    have hn_eq : n = 2 * r * k + 2 * k + 2 * hOf k + m * k + m + k := by
      dsimp only [n, h, hOf]; ring
    have hread_mem : ∀ (off len : Nat), off + len ≤ n → ∀ j : Fin len,
        bitsOf len (fun x : Fin n → Bool => readNat x off len) j ∈ Base1 := by
      intro off len hle j
      have hlt : off + j.val < n := by omega
      have heq : bitsOf len (fun x : Fin n → Bool => readNat x off len) j =
          fun x : Fin n → Bool => x ⟨off + j.val, hlt⟩ := by
        funext x; dsimp only [bitsOf]; rw [(readNat_spec x off len).2 j.val j.isLt]; simp [hlt]
      rw [heq]; exact Or.inl ⟨⟨off + j.val, hlt⟩, rfl⟩
    have hsched_mem : ∀ t, 1 ≤ t → t ≤ 2 * r → ∀ j : Fin k,
        bitsOf k (fun x => (inSched x t).val) j ∈ Base1 := by
      intro t ht1 ht2 j
      have hle : (t - 1) * k + k ≤ n := by
        have h1 : (t - 1) * k + k = t * k := by rw [← Nat.succ_mul]; congr 1; omega
        have h2 : t * k ≤ 2 * r * k := Nat.mul_le_mul_right k ht2
        omega
      have heq : bitsOf k (fun x => (inSched x t).val) j =
          bitsOf k (fun x => readNat x ((t - 1) * k) k) j := by
        funext x; dsimp only [bitsOf, inSched]; simp [ht1, ht2]
      rw [heq]; exact hread_mem _ k hle j
    have hleft_mem : ∀ j : Fin k, bitsOf k (fun x => (inLeft x).val) j ∈ Base1 :=
      hread_mem (2 * r * k) k (by omega)
    have hright_mem : ∀ j : Fin k, bitsOf k (fun x => (inRight x).val) j ∈ Base1 :=
      hread_mem (2 * r * k + k) k (by omega)
    have ha_mem : ∀ j : Fin (hOf k), bitsOf (hOf k) (fun x => (inA x).val) j ∈ Base1 :=
      hread_mem (2 * r * k + 2 * k) (hOf k) (by omega)
    have hb_mem : ∀ j : Fin (hOf k), bitsOf (hOf k) (fun x => (inB x).val) j ∈ Base1 :=
      hread_mem (2 * r * k + 2 * k + hOf k) (hOf k) (by omega)
    have hA_mem : ∀ i : Fin m, ∀ j : Fin k, bitsOf k (fun x => (inMat x i).val) j ∈ Base1 := by
      intro i
      have hle : 2 * r * k + 2 * k + 2 * hOf k + i.val * k + k ≤ n := by
        have h1 : i.val * k + k = (i.val + 1) * k := by rw [Nat.succ_mul]
        have h2 : (i.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k i.isLt
        omega
      exact hread_mem _ k hle
    have hrhs_mem : ∀ i : Fin m, (fun x => inRhs x i) ∈ Base1 := by
      intro i
      have hi : 2 * r * k + 2 * k + 2 * hOf k + m * k + i.val < n := by omega
      have heq : (fun x => inRhs x i) = fun x => x ⟨2 * r * k + 2 * k + 2 * hOf k + m * k + i.val, hi⟩ := by
        funext x; dsimp only [inRhs]; simp [hi]
      rw [heq]; exact Or.inl ⟨_, rfl⟩
    have hrank_mem : ∀ j : Fin k, bitsOf k (fun x => (inRank x).val) j ∈ Base1 :=
      hread_mem (2 * r * k + 2 * k + 2 * hOf k + m * k + m) k (by omega)
    let w0Fn : Fin (2 ^ swOf k r) → (Fin n → Bool) → Nat := fun label x =>
      decodeSeed k r (inSched x) (inLeft x).val (inRight x).val (inA x).val (inB x).val label.val
    let passFn : Fin (2 ^ swOf k r) → Sig n := fun label x =>
      passSeed k r (inSched x) (inLeft x).val (inRight x).val (inA x).val (inB x).val label.val
    let bparFn : Fin (2 ^ swOf k r) → Fin m → Sig n := fun label i x =>
      parityK k (w0Fn label x &&& (inMat x i).val)
    let seedSigs : Fin (2 ^ swOf k r) → Set (Sig n) := fun label =>
      Set.range (bitsOf k (w0Fn label)) ∪ ({passFn label} ∪ Set.range (bparFn label))
    have hseedB : Build Base1 (⋃ label : Fin (2 ^ swOf k r), seedSigs label)
        (2 ^ swOf k r * (120 * (k + m + 1) ^ 2 * (r + 1))) := by
      refine finB seedSigs (120 * (k + m + 1) ^ 2 * (r + 1)) (fun label => ?_)
      have hdec := decodeSeedB hr hkpos hfalse1 htrue1 inSched
        (fun x => (inLeft x).val) (fun x => (inRight x).val)
        (fun x => (inA x).val) (fun x => (inB x).val)
        hsched_mem hleft_mem (fun x => (inLeft x).isLt)
        hright_mem (fun x => (inRight x).isLt) ha_mem hb_mem label
      have hw0Lt : ∀ x, w0Fn label x < 2 ^ k := fun x =>
        (decodeSeed_spec hr hkpos (inSched x) (inA x).val (inB x).val
          (inLeft x).isLt (inRight x).isLt label.isLt).1
      have hps := passSeedB (Base := Base1 ∪ Set.range (bitsOf k (w0Fn label)))
        hkpos (Or.inl htrue1) inSched
        (fun x => (inLeft x).val) (fun x => (inRight x).val)
        (fun x => (inA x).val) (fun x => (inB x).val) (w0Fn label)
        (fun t ht1 ht2 j => Or.inl (hsched_mem t ht1 ht2 j))
        (fun j => Or.inl (hleft_mem j)) (fun x => (inLeft x).isLt)
        (fun j => Or.inl (hright_mem j)) (fun x => (inRight x).isLt)
        (fun j => Or.inl (ha_mem j)) (fun x => (inA x).isLt)
        (fun j => Or.inl (hb_mem j)) (fun x => (inB x).isLt)
        (fun j => Or.inr ⟨j, rfl⟩) hw0Lt
      have hbp : Build (Base1 ∪ Set.range (bitsOf k (w0Fn label))) (Set.range (bparFn label)) (m * (5 * k)) :=
        finSigB (bparFn label) (5 * k) (fun i =>
          parityAndB (Or.inl hfalse1) (w0Fn label) (fun x => (inMat x i).val)
            (fun j => Or.inr ⟨j, rfl⟩) (fun j => Or.inl (hA_mem i j)))
      have hcost : (rowLenOf k r + colLenOf k r) * (22 * k * r + 18 * k + 8) +
          (44 * k * r + 8 * k + 12 * hOf k + 1 + m * (5 * k)) ≤ 120 * (k + m + 1) ^ 2 * (r + 1) := by
        have hrc : rowLenOf k r + colLenOf k r ≤ k := by omega
        have hhle : hOf k ≤ k := by dsimp only [hOf]; omega
        have h1 : (rowLenOf k r + colLenOf k r) * (22 * k * r + 18 * k + 8) ≤
            k * (22 * k * r + 18 * k + 8) := Nat.mul_le_mul_right _ hrc
        have h2 : k * (22 * k * r + 18 * k + 8) + (44 * k * r + 8 * k + 12 * k + 1 + m * (5 * k)) ≤
            120 * (k + m + 1) ^ 2 * (r + 1) := by
          have hexp : 120 * (k + m + 1) ^ 2 * (r + 1) =
              120 * (k * k * r) + 120 * (k * k) + 240 * (k * m * r) + 240 * (k * m) +
              120 * (m * m * r) + 120 * (m * m) + 240 * (k * r) + 240 * k +
              240 * (m * r) + 240 * m + 120 * r + 120 := by ring
          have hlhs : k * (22 * k * r + 18 * k + 8) + (44 * k * r + 8 * k + 12 * k + 1 + m * (5 * k)) =
              22 * (k * k * r) + 18 * (k * k) + 44 * (k * r) + 28 * k + 5 * (k * m) + 1 := by ring
          rw [hexp, hlhs]; omega
        omega
      exact relaxB (seqB hdec (unionB hps hbp)) le_rfl Set.subset_union_right hcost
    let gaussPosSigs : Fin (k + 1) → Set (Sig n) := fun pos =>
      gSigs (fun x => gElim (matAt k r m pos.val (inMat x))) ∪
      Set.range (fun j : Fin (k + 1) => fun x => pow2Nullity (k + 1) (freeDim k r pos.val)
        (gElim (matAt k r m pos.val (inMat x))).1 j)
    have hgaussB : Build Base1 (⋃ pos : Fin (k + 1), gaussPosSigs pos)
        ((k + 1) * (19 * (k + m + 1) ^ 3)) := by
      refine finB gaussPosSigs (19 * (k + m + 1) ^ 3) (fun pos => ?_)
      have hfd_le : freeDim k r pos.val ≤ k := by
        have : freeDim k r pos.val ≤ unusedOf k r := Nat.min_le_left _ _
        omega
      have hge := gElimB (Base := Base1) hfalse1 htrue1 (fun x => matAt k r m pos.val (inMat x)) (fun row c => by
        have hlt : 4 * r - 3 + c.val < k := by
          have hc := c.isLt
          have hfd_u : freeDim k r pos.val ≤ unusedOf k r := Nat.min_le_left _ _
          dsimp only [unusedOf, zOf, hOf] at hfd_u
          omega
        exact hA_mem row ⟨4 * r - 3 + c.val, hlt⟩)
      have hpn := pow2NullityB (Base := Base1 ∪ gSigs (fun x => gElim (matAt k r m pos.val (inMat x))))
        (L := k + 1) (Or.inl hfalse1) (Or.inl htrue1) (freeDim k r pos.val)
        (fun x => (gElim (matAt k r m pos.val (inMat x))).1)
        (fun row => Or.inr (Or.inl (Or.inl ⟨row, rfl⟩)))
      have hcost : freeDim k r pos.val * (m * (m + 4) + (freeDim k r pos.val + m) * (2 * m) +
          m * (1 + (freeDim k r pos.val + m) * 7)) + m * ((k + 1) * 4) ≤ 19 * (k + m + 1) ^ 3 := by
        have h1 : m * (m + 4) + (freeDim k r pos.val + m) * (2 * m) +
            m * (1 + (freeDim k r pos.val + m) * 7) ≤ 15 * (k + m + 1) ^ 2 := by
          have hle1 : freeDim k r pos.val + m ≤ k + m := by omega
          have hm1 : (freeDim k r pos.val + m) * (2 * m) ≤ (k + m) * (2 * m) := Nat.mul_le_mul_right _ hle1
          have hm2 : m * (1 + (freeDim k r pos.val + m) * 7) ≤ m * (1 + (k + m) * 7) :=
            Nat.mul_le_mul_left _ (by omega)
          have hsq : 15 * (k + m + 1) ^ 2 = 15 * (k * k) + 30 * (k * m) + 15 * (m * m) + 30 * k + 30 * m + 15 := by ring
          have hrhs : m * (m + 4) + (k + m) * (2 * m) + m * (1 + (k + m) * 7) =
              10 * (m * m) + 9 * (k * m) + 5 * m := by ring
          have hstep1 : m * (m + 4) + (freeDim k r pos.val + m) * (2 * m) + m * (1 + (freeDim k r pos.val + m) * 7) ≤
              m * (m + 4) + (k + m) * (2 * m) + m * (1 + (k + m) * 7) := by omega
          rw [hrhs] at hstep1
          rw [hsq]
          omega
        have h2 : freeDim k r pos.val * (m * (m + 4) + (freeDim k r pos.val + m) * (2 * m) +
            m * (1 + (freeDim k r pos.val + m) * 7)) ≤ (k + m + 1) * (15 * (k + m + 1) ^ 2) :=
          Nat.mul_le_mul (by omega) h1
        have h3 : m * ((k + 1) * 4) ≤ 4 * (k + m + 1) ^ 3 := by
          have hcube : 4 * (k + m + 1) ^ 3 = 4 * (k + m + 1) * (k + m + 1) * (k + m + 1) := by ring
          have hkm : m * (k + 1) ≤ (k + m + 1) * (k + m + 1) := Nat.mul_le_mul (by omega) (by omega)
          have hkm3 : (k + m + 1) * (k + m + 1) ≤ (k + m + 1) ^ 3 := by
            calc (k + m + 1) * (k + m + 1) = (k + m + 1) ^ 2 * 1 := by ring
              _ ≤ (k + m + 1) ^ 2 * (k + m + 1) := Nat.mul_le_mul_left _ (by omega)
              _ = (k + m + 1) ^ 3 := by ring
          have : m * ((k + 1) * 4) = 4 * (m * (k + 1)) := by ring
          omega
        have hcube15 : (k + m + 1) * (15 * (k + m + 1) ^ 2) = 15 * (k + m + 1) ^ 3 := by ring
        omega
      exact relaxB (seqB hge hpn) le_rfl Set.subset_union_right hcost
    let Base2 := Base1 ∪ ((⋃ label : Fin (2 ^ swOf k r), seedSigs label) ∪
      (⋃ pos : Fin (k + 1), gaussPosSigs pos))
    have hpreB := unionB hseedB hgaussB
    let cntFn : (Fin n → Bool) → Nat → (Fin k → Bool) → Nat := fun x pos pref =>
      countSpec k r m pos (inSched x) (inLeft x).val (inRight x).val (inA x).val (inB x).val
        (inMat x) (inRhs x) pref
    let totalFn : (Fin n → Bool) → Nat := fun x => cntFn x k (fun _ => false)
    have htotalB : Build Base2 (Set.range (bitsOf (k + 1) totalFn)) (2 ^ swOf k r * (24 * (k + m + 1) ^ 2)) :=
      countQueryB hr hkpos le_rfl (Or.inl hfalse1) (Or.inl htrue1)
        inSched (fun x => (inLeft x).val) (fun x => (inRight x).val)
        (fun x => (inA x).val) (fun x => (inB x).val) inMat inRhs (fun _ _ => false)
        (fun i j => Or.inl (hA_mem i j)) (fun i => Or.inl (hrhs_mem i)) (fun _ => Or.inl hfalse1)
        (fun label j => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨label, Or.inl ⟨j, rfl⟩⟩)))
        (fun label => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨label, Or.inr (Or.inl rfl)⟩)))
        (fun label i => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨label, Or.inr (Or.inr ⟨i, rfl⟩)⟩)))
        (fun row => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, Or.inl (Or.inl (Or.inl ⟨row, rfl⟩))⟩)))
        (fun row i => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, Or.inl (Or.inr ⟨row, i, rfl⟩)⟩)))
        (fun j => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, Or.inr ⟨j, rfl⟩⟩)))
    have hselB : Build Base2 (selSigs (fun x => selectRun k (cntFn x) (inRank x).val))
        (k * (2 ^ swOf k r * (54 * (k + m + 1) ^ 2))) :=
      selectRunB hr hkpos (Or.inl hfalse1) (Or.inl htrue1) inSched inLeft inRight inA inB inMat inRhs inRank
        (fun i j => Or.inl (hA_mem i j)) (fun i => Or.inl (hrhs_mem i)) (fun j => Or.inl (hrank_mem j))
        (fun label j => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨label, Or.inl ⟨j, rfl⟩⟩)))
        (fun label => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨label, Or.inr (Or.inl rfl)⟩)))
        (fun label i => Or.inr (Or.inl (Set.mem_iUnion.mpr ⟨label, Or.inr (Or.inr ⟨i, rfl⟩)⟩)))
        (fun pos row => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨pos, Or.inl (Or.inl (Or.inl ⟨row, rfl⟩))⟩)))
        (fun pos row i => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨pos, Or.inl (Or.inr ⟨row, i, rfl⟩)⟩)))
        (fun pos j => Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨pos, Or.inr ⟨j, rfl⟩⟩)))
    have htsB := unionB htotalB hselB
    let Base3 := Base2 ∪ (Set.range (bitsOf (k + 1) totalFn) ∪ selSigs (fun x => selectRun k (cntFn x) (inRank x).val))
    let validSig : Sig n := fun x => decide ((inRank x).val < totalFn x)
    have hvalidB : Build Base3 {validSig} (5 * (k + 1)) :=
      ltB (k + 1) (fun x => (inRank x).val) totalFn (Or.inl (Or.inl hfalse1))
        (fun j => by
          by_cases hjk : j.val < k
          · exact Or.inl (Or.inl (hrank_mem ⟨j.val, hjk⟩))
          · have heq : bitsOf (k + 1) (fun x => (inRank x).val) j = fun _ => false := by
              funext x; dsimp only [bitsOf]
              exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (inRank x).isLt
                (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
            rw [heq]; exact Or.inl (Or.inl hfalse1))
        (fun j => Or.inr (Or.inl ⟨j, rfl⟩))
        (fun x => lt_of_lt_of_le (inRank x).isLt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))
        (fun x => countSpec_lt_pow hr hkpos le_rfl (inSched x) (inLeft x) (inRight x) (inA x) (inB x) (inMat x) (inRhs x) _)
    let keyOut : Fin k → Sig n := fun d x => validSig x && (selectRun k (cntFn x) (inRank x).val).1 d
    have hkeyB : Build (Base3 ∪ {validSig}) (Set.range keyOut) (k * 1) :=
      finSigB keyOut 1 (fun d => andB (Or.inr rfl) (Or.inl (Or.inr (Or.inr (Or.inl ⟨d, rfl⟩)))))
    have hfinB := seqB hconsts (seqB hpreB (seqB htsB (seqB hvalidB hkeyB)))
    have htotalCost :
        2 + (2 ^ swOf k r * (120 * (k + m + 1) ^ 2 * (r + 1)) + (k + 1) * (19 * (k + m + 1) ^ 3) +
          (2 ^ swOf k r * (24 * (k + m + 1) ^ 2) + k * (2 ^ swOf k r * (54 * (k + m + 1) ^ 2)) +
            (5 * (k + 1) + k * 1))) ≤ 1048576 * (k + m + 1) ^ 5 * (r + 1) * 2 ^ seedWidth := by
      have hsw_eq : seedWidth = swOf k r := rfl
      rw [hsw_eq]
      set S := k + m + 1
      set W := 2 ^ swOf k r
      have hS1 : 1 ≤ S := by dsimp only [S]; omega
      have hW1 : 1 ≤ W := Nat.one_le_two_pow
      have hS2 : S ^ 2 ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by omega)
      have hS3 : S ^ 3 ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by omega)
      have hS4 : S ^ 4 ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by omega)
      have hS1_5 : S ≤ S ^ 5 := by calc S = S ^ 1 := (Nat.pow_one S).symm
        _ ≤ S ^ 5 := Nat.pow_le_pow_right hS1 (by omega)
      have h1_5 : 1 ≤ S ^ 5 := Nat.one_le_pow _ _ hS1
      have hA1 : 2 ≤ 2 * S ^ 5 * (r + 1) * W := by
        calc 2 = 2 * 1 * 1 * 1 := by ring
          _ ≤ 2 * S ^ 5 * (r + 1) * W :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 h1_5) (by omega)) hW1
      have hA2 : W * (120 * S ^ 2 * (r + 1)) ≤ 120 * S ^ 5 * (r + 1) * W := by
        calc W * (120 * S ^ 2 * (r + 1)) = 120 * S ^ 2 * (r + 1) * W := by ring
          _ ≤ 120 * S ^ 5 * (r + 1) * W :=
            Nat.mul_le_mul_right W (Nat.mul_le_mul_right (r + 1) (Nat.mul_le_mul_left 120 hS2))
      have hA3 : (k + 1) * (19 * S ^ 3) ≤ 19 * S ^ 5 * (r + 1) * W := by
        have hkS : k + 1 ≤ S := by dsimp only [S]; omega
        calc (k + 1) * (19 * S ^ 3) ≤ S * (19 * S ^ 3) := Nat.mul_le_mul_right _ hkS
          _ = 19 * S ^ 4 * 1 * 1 := by ring
          _ ≤ 19 * S ^ 5 * (r + 1) * W :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 19 hS4) (by omega)) hW1
      have hA4 : W * (24 * S ^ 2) ≤ 24 * S ^ 5 * (r + 1) * W := by
        calc W * (24 * S ^ 2) = 24 * S ^ 2 * 1 * W := by ring
          _ ≤ 24 * S ^ 5 * (r + 1) * W :=
            Nat.mul_le_mul_right W (Nat.mul_le_mul (Nat.mul_le_mul_left 24 hS2) (by omega))
      have hA5 : k * (W * (54 * S ^ 2)) ≤ 54 * S ^ 5 * (r + 1) * W := by
        have hkS : k ≤ S := by dsimp only [S]; omega
        calc k * (W * (54 * S ^ 2)) ≤ S * (W * (54 * S ^ 2)) := Nat.mul_le_mul_right _ hkS
          _ = 54 * S ^ 3 * 1 * W := by ring
          _ ≤ 54 * S ^ 5 * (r + 1) * W :=
            Nat.mul_le_mul_right W (Nat.mul_le_mul (Nat.mul_le_mul_left 54 hS3) (by omega))
      have hA6 : 5 * (k + 1) + k * 1 ≤ 6 * S ^ 5 * (r + 1) * W := by
        have hk6 : 5 * (k + 1) + k * 1 ≤ 6 * S := by dsimp only [S]; omega
        calc 5 * (k + 1) + k * 1 ≤ 6 * S := hk6
          _ = 6 * S * 1 * 1 := by ring
          _ ≤ 6 * S ^ 5 * (r + 1) * W :=
            Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 6 hS1_5) (by omega)) hW1
      calc 2 + (W * (120 * S ^ 2 * (r + 1)) + (k + 1) * (19 * S ^ 3) +
            (W * (24 * S ^ 2) + k * (W * (54 * S ^ 2)) + (5 * (k + 1) + k * 1)))
          ≤ 2 * S ^ 5 * (r + 1) * W + (120 * S ^ 5 * (r + 1) * W + 19 * S ^ 5 * (r + 1) * W +
            (24 * S ^ 5 * (r + 1) * W + 54 * S ^ 5 * (r + 1) * W + 6 * S ^ 5 * (r + 1) * W)) := by omega
        _ = 225 * (S ^ 5 * (r + 1) * W) := by ring
        _ ≤ 1048576 * (S ^ 5 * (r + 1) * W) := Nat.mul_le_mul_right _ (by omega)
        _ = 1048576 * S ^ 5 * (r + 1) * W := by ring
    obtain ⟨sz, hsz_le, hsched⟩ := hfinB 0 Base0 (startSched n) le_rfl
    rw [Nat.zero_add] at hsched
    obtain ⟨C, countWire, keyWire, hfan, hrb, hout, hcsz, hev⟩ :=
      finishOutputs hsched validSig
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
        (bitsOf (k + 1) totalFn)
        (fun j => Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨j, rfl⟩)))))
        keyOut
        (fun d => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, rfl⟩)))))
    refine ⟨C, countWire, keyWire, hfan, hrb, hout, by rw [hcsz]; exact hsz_le.trans htotalCost, ?_⟩
    intro schedule leftName rightName a b A rhs rank input solutions
    let p0 := (List.range (2 * r)).flatMap (fun idx => bits k (schedule (idx + 1)).val)
    let p1 := bits k leftName.val
    let p2 := bits k rightName.val
    let p3 := bits h a.val
    let p4 := bits h b.val
    let p5 := (List.ofFn A).flatMap (fun entry => bits k entry.val)
    let p6 := List.ofFn rhs
    let p7 := bits k rank.val
    have hp0_len : p0.length = 2 * r * k := by
      dsimp only [p0]
      rw [length_flatMap_const _ _ k (fun _ _ => by simp [bits]), List.length_range]
    have hp1_len : p1.length = k := by simp [p1, bits]
    have hp2_len : p2.length = k := by simp [p2, bits]
    have hp3_len : p3.length = h := by simp [p3, bits]
    have hp4_len : p4.length = h := by simp [p4, bits]
    have hp5_len : p5.length = m * k := by
      dsimp only [p5]
      rw [length_flatMap_const _ _ k (fun _ _ => by simp [bits]), List.length_ofFn]
    have hp6_len : p6.length = m := by simp [p6]
    have hp7_len : p7.length = k := by simp [p7, bits]
    have hinp_len : input.length = n := by
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).length = n
      simp only [List.length_append, hp0_len, hp1_len, hp2_len, hp3_len, hp4_len, hp5_len, hp6_len, hp7_len]
      dsimp only [n]; ring
    let x : Fin n → Bool := fun i => input.getD i.val false
    have hof : List.ofFn x = input := ofFn_getD_eq input hinp_len
    have hx_sched : ∀ t, 1 ≤ t → t ≤ 2 * r → inSched x t = schedule t := by
      intro t ht1 ht2
      apply Fin.ext
      dsimp only [inSched]
      simp only [ht1, ht2, and_self, ↓reduceIte]
      apply readNat_eq_of_bits x ((t - 1) * k) k (schedule t).val (by
        have : (t - 1) * k + k = t * k := by rw [← Nat.succ_mul]; congr 1; omega
        have : t * k ≤ 2 * r * k := Nat.mul_le_mul_right k ht2
        omega) (schedule t).isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD ((t - 1) * k + j) false = (schedule t).val.testBit j
      have hlt0 : (t - 1) * k + j < p0.length := by
        rw [hp0_len]
        have : (t - 1) * k + k = t * k := by rw [← Nat.succ_mul]; congr 1; omega
        have : t * k ≤ 2 * r * k := Nat.mul_le_mul_right k ht2
        omega
      simp only [List.append_assoc]
      rw [List.getD_append _ _ _ _ hlt0]
      dsimp only [p0]
      rw [getD_flatMap_const (List.range (2 * r)) (fun idx => bits k (schedule (idx + 1)).val) k
        (fun _ _ => by simp [bits]) (t - 1) j (by simp; omega) hj]
      simp only [List.getElem_range, bits, Nat.sub_add_cancel ht1]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
    have hx_left : inLeft x = leftName := by
      apply Fin.ext
      apply readNat_eq_of_bits x (2 * r * k) k leftName.val (by omega) leftName.isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD (2 * r * k + j) false = leftName.val.testBit j
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len, Nat.add_sub_cancel_left,
        List.getD_append _ _ _ _ (by rw [hp1_len]; exact hj)]
      dsimp only [p1, bits]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
    have hx_right : inRight x = rightName := by
      apply Fin.ext
      apply readNat_eq_of_bits x (2 * r * k + k) k rightName.val (by omega) rightName.isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD (2 * r * k + k + j) false = rightName.val.testBit j
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len,
        List.getD_append_right _ _ _ _ (by rw [hp1_len]; omega), hp1_len,
        List.getD_append _ _ _ _ (by rw [hp2_len]; omega)]
      have hidx : 2 * r * k + k + j - 2 * r * k - k = j := by omega
      rw [hidx]
      dsimp only [p2, bits]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
    have hx_a : inA x = a := by
      apply Fin.ext
      apply readNat_eq_of_bits x (2 * r * k + 2 * k) (hOf k) a.val (by omega) a.isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD (2 * r * k + 2 * k + j) false = a.val.testBit j
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len,
        List.getD_append_right _ _ _ _ (by rw [hp1_len]; omega), hp1_len,
        List.getD_append_right _ _ _ _ (by rw [hp2_len]; omega), hp2_len,
        List.getD_append _ _ _ _ (by rw [hp3_len]; dsimp only [h, hOf] at *; omega)]
      have hidx : 2 * r * k + 2 * k + j - 2 * r * k - k - k = j := by omega
      rw [hidx]
      dsimp only [p3, bits]
      rw [List.getD_eq_getElem _ _ (by simp; exact hj), List.getElem_map, List.getElem_range]
    have hx_b : inB x = b := by
      apply Fin.ext
      apply readNat_eq_of_bits x (2 * r * k + 2 * k + hOf k) (hOf k) b.val (by omega) b.isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD (2 * r * k + 2 * k + hOf k + j) false = b.val.testBit j
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len,
        List.getD_append_right _ _ _ _ (by rw [hp1_len]; omega), hp1_len,
        List.getD_append_right _ _ _ _ (by rw [hp2_len]; omega), hp2_len,
        List.getD_append_right _ _ _ _ (by rw [hp3_len]; dsimp only [h, hOf] at *; omega), hp3_len,
        List.getD_append _ _ _ _ (by rw [hp4_len]; dsimp only [h, hOf] at *; omega)]
      have hidx : 2 * r * k + 2 * k + hOf k + j - 2 * r * k - k - k - h = j := by dsimp only [h, hOf]; omega
      rw [hidx]
      dsimp only [p4, bits]
      rw [List.getD_eq_getElem _ _ (by simp; exact hj), List.getElem_map, List.getElem_range]
    have hx_A : inMat x = A := by
      funext i
      apply Fin.ext
      apply readNat_eq_of_bits x (2 * r * k + 2 * k + 2 * hOf k + i.val * k) k (A i).val (by
        have h1 : i.val * k + k = (i.val + 1) * k := by rw [Nat.succ_mul]
        have h2 : (i.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k i.isLt
        omega) (A i).isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD
        (2 * r * k + 2 * k + 2 * hOf k + i.val * k + j) false = (A i).val.testBit j
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len,
        List.getD_append_right _ _ _ _ (by rw [hp1_len]; omega), hp1_len,
        List.getD_append_right _ _ _ _ (by rw [hp2_len]; omega), hp2_len,
        List.getD_append_right _ _ _ _ (by rw [hp3_len]; dsimp only [h, hOf] at *; omega), hp3_len,
        List.getD_append_right _ _ _ _ (by rw [hp4_len]; dsimp only [h, hOf] at *; omega), hp4_len,
        List.getD_append _ _ _ _ (by
          rw [hp5_len]
          have h1 : i.val * k + k = (i.val + 1) * k := by rw [Nat.succ_mul]
          have h2 : (i.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k i.isLt
          dsimp only [h, hOf] at *; omega)]
      have hidx : 2 * r * k + 2 * k + 2 * hOf k + i.val * k + j - 2 * r * k - k - k - h - h = i.val * k + j := by
        dsimp only [h, hOf]; omega
      rw [hidx]
      dsimp only [p5]
      rw [getD_flatMap_const (List.ofFn A) (fun entry => bits k entry.val) k
        (fun _ _ => by simp [bits]) i.val j (by simp) hj]
      simp only [List.getElem_ofFn, bits]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
    have hx_rhs : inRhs x = rhs := by
      funext i
      dsimp only [inRhs]
      have hi : 2 * r * k + 2 * k + 2 * hOf k + m * k + i.val < n := by omega
      simp only [hi, ↓reduceDIte]
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD
        (2 * r * k + 2 * k + 2 * hOf k + m * k + i.val) false = rhs i
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len,
        List.getD_append_right _ _ _ _ (by rw [hp1_len]; omega), hp1_len,
        List.getD_append_right _ _ _ _ (by rw [hp2_len]; omega), hp2_len,
        List.getD_append_right _ _ _ _ (by rw [hp3_len]; dsimp only [h, hOf] at *; omega), hp3_len,
        List.getD_append_right _ _ _ _ (by rw [hp4_len]; dsimp only [h, hOf] at *; omega), hp4_len,
        List.getD_append_right _ _ _ _ (by rw [hp5_len]; dsimp only [h, hOf] at *; omega), hp5_len,
        List.getD_append _ _ _ _ (by rw [hp6_len]; dsimp only [h, hOf] at *; omega)]
      have hidx : 2 * r * k + 2 * k + 2 * hOf k + m * k + i.val - 2 * r * k - k - k - h - h - m * k = i.val := by
        dsimp only [h, hOf]; omega
      rw [hidx]
      dsimp only [p6]
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hx_rank : inRank x = rank := by
      apply Fin.ext
      apply readNat_eq_of_bits x (2 * r * k + 2 * k + 2 * hOf k + m * k + m) k rank.val (by omega) rank.isLt
      intro j hj
      dsimp only [x]
      change (p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6 ++ p7).getD
        (2 * r * k + 2 * k + 2 * hOf k + m * k + m + j) false = rank.val.testBit j
      simp only [List.append_assoc]
      rw [List.getD_append_right _ _ _ _ (by rw [hp0_len]; omega), hp0_len,
        List.getD_append_right _ _ _ _ (by rw [hp1_len]; omega), hp1_len,
        List.getD_append_right _ _ _ _ (by rw [hp2_len]; omega), hp2_len,
        List.getD_append_right _ _ _ _ (by rw [hp3_len]; dsimp only [h, hOf] at *; omega), hp3_len,
        List.getD_append_right _ _ _ _ (by rw [hp4_len]; dsimp only [h, hOf] at *; omega), hp4_len,
        List.getD_append_right _ _ _ _ (by rw [hp5_len]; dsimp only [h, hOf] at *; omega), hp5_len,
        List.getD_append_right _ _ _ _ (by rw [hp6_len]; dsimp only [h, hOf] at *; omega), hp6_len]
      have hidx : 2 * r * k + 2 * k + 2 * hOf k + m * k + m + j - 2 * r * k - k - k - h - h - m * k - m = j := by
        dsimp only [h, hOf]; omega
      rw [hidx]
      dsimp only [p7, bits]
      rw [List.getD_eq_getElem _ _ (by simp [hj]), List.getElem_map, List.getElem_range]
    have hcnt_spec : ∀ pos ≤ k, ∀ pref : Fin k → Bool,
        cntFn x pos pref = (solutions.filter (fun w =>
          (List.finRange k).all (fun j => !(decide (pos ≤ j.val)) || (w.testBit j.val == pref j)))).length := by
      intro pos hpos pref
      dsimp only [cntFn]
      rw [hx_left, hx_right, hx_a, hx_b, hx_A, hx_rhs]
      rw [countSpec_eq_filter_length hr hkpos hpos (inSched x) leftName rightName a b A rhs pref]
      congr 2
      apply List.filter_congr
      intro w _
      congr 1
      have hs1 := stateN_congr_sched (inSched x) schedule hx_sched false w leftName.val r le_rfl
      have hs2 := stateN_congr_sched (inSched x) schedule hx_sched true w rightName.val r le_rfl
      rw [hs1, hs2]
      rfl
    have htotal_eq : totalFn x = solutions.length := by
      dsimp only [totalFn]
      rw [hcnt_spec k le_rfl (fun _ => false)]
      have hself : solutions.filter (fun w =>
          (List.finRange k).all (fun j => !(decide (k ≤ j.val)) || (w.testBit j.val == false))) = solutions := by
        rw [List.filter_eq_self]
        intro w _
        rw [List.all_eq_true]
        intro j _
        simp
      rw [hself]
    have hevx := hev x
    rw [hof] at hevx
    refine ⟨?_, ?_, ?_⟩
    · rw [hevx.1]
      dsimp only [validSig]
      rw [hx_rank, htotal_eq]
    · intro j
      rw [hevx.2.1 j]
      dsimp only [bitsOf]
      rw [htotal_eq]
    · intro d
      rw [hevx.2.2 d]
      dsimp only [keyOut, validSig]
      rw [hx_rank, htotal_eq]
      by_cases hlt : rank.val < solutions.length
      · simp only [hlt, decide_true, Bool.true_and]
        have hpw : solutions.Pairwise (· < ·) := (List.pairwise_lt_range).filter _
        have hlt_w : ∀ w ∈ solutions, w < 2 ^ k := fun w hw => List.mem_range.mp (List.mem_filter.mp hw).1
        exact selectRun_spec solutions hpw hlt_w (cntFn x) hcnt_spec rank.val hlt d
      · simp only [hlt, decide_false, Bool.false_and]
        have hge : solutions.length ≤ rank.val := by omega
        rw [List.getD_eq_default solutions 0 hge]
        simp

end PEqualNP.Outside.L_meta_29729

theorem PEqualNP.Outside.L_meta_29729 : ∀ (k r m : Nat), 4 ≤ r →
  let h := (k+1)/2
  let z := k-h
  let u := 5*r-3
  let extra := min (r-2) (z-6*r)
  let seedWidth := min k u + extra
  let rot := fun (offset x : Nat) =>
    ((x <<< (offset % k)) ||| (x >>> (k-offset % k))) % 2^k
  let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
  let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site+1) % k)) && word.testBit ((site+2) % k))).toNat <<< site)) 0
  let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
    chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
      (constants (if col then r+t else t)).val
  let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
    (List.range r).foldl (fun v tick => step c side key v (tick+1))
      (rot (if side then 3 else 1) key ^^^ name)
  let n := 2*r*k+3*k+2*h+m*(k+1)
  let bits := fun (len data : Nat) => (List.range len).map (fun pos => data.testBit pos)
  let parity := fun (natWord : Nat) => (List.range k).foldl
    (fun total bitPos => xor total (natWord.testBit bitPos)) false
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
      (countWire : Fin (k+1) → Fin (n+C.size)) (keyWire : Fin k → Fin (n+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
    C.output < n+C.size ∧ C.size ≤ 1048576*(k+m+1)^5*(r+1)*2^seedWidth ∧
    ∀ (schedule : Nat → Fin (2^k)) (leftName rightName : Fin (2^k))
        (a b : Fin (2^h)) (A : Fin m → Fin (2^k)) (rhs : Fin m → Bool)
        (rank : Fin (2^k)),
      let input := (List.range (2*r)).flatMap (fun idx => bits k (schedule (idx+1)).val) ++
        bits k leftName.val ++ bits k rightName.val ++ bits h a.val ++ bits h b.val ++
        (List.ofFn A).flatMap (fun entry => bits k entry.val) ++ List.ofFn rhs ++ bits k rank.val
      let solutions := (List.range (2^k)).filter (fun w => decide (
        state schedule false w leftName.val >>> z = a.val ∧
        state schedule true w rightName.val >>> z = b.val ∧
        ∀ i : Fin m, parity (w &&& (A i).val) = rhs i))
      C.eval input = decide (rank.val < solutions.length) ∧
      (∀ j : Fin (k+1), (C.wires input).getD (countWire j).val false = solutions.length.testBit j.val) ∧
      (∀ d : Fin k, (C.wires input).getD (keyWire d).val false =
        ((solutions.getD rank.val 0).testBit d.val)) :=
  PEqualNP.Outside.L_meta_29729.main_29729
