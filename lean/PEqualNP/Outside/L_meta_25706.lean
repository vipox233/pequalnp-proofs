import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25706_aux

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

lemma rotK_lt {k : Nat} (offset x : Nat) : rotK k offset x < 2 ^ k :=
  Nat.mod_lt _ (by positivity)

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
      refine ⟨fun j _ => by simp, fun b hb => by omega⟩
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
        by_cases hbm : b = m
        · subst hbm
          rw [hprev.1 b le_rfl, decide_eq_true le_rfl, Bool.true_and, Bool.false_or, Nat.sub_self]
          cases bitFn b <;> decide
        · have hlt : b < m := by omega
          have hnot : ¬(m ≤ b) := by omega
          rw [decide_eq_false hnot, Bool.false_and, Bool.or_false, hprev.2 b hlt]
  have hfull := htake k le_rfl
  refine ⟨?_, hfull.2⟩
  by_contra hge
  have h1 : 2 ^ k ≤ chiK k word := by omega
  have hne : chiK k word ≠ 0 := by
    have hpos : 0 < 2 ^ k := by positivity
    omega
  have hlog : k ≤ Nat.log2 (chiK k word) := (Nat.le_log2 hne).mpr h1
  have htrue : (chiK k word).testBit (Nat.log2 (chiK k word)) = true := Nat.testBit_log2 hne
  have hfalse : (chiK k word).testBit (Nat.log2 (chiK k word)) = false := hfull.1 _ hlog
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

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

lemma agreeCyc_mod {k x y lo len : Nat} (h : AgreeCyc k x y lo len) :
    AgreeCyc k x y (lo % k) len := by
  intro d hd
  have h1 : (lo % k + d) % k = (lo + d) % k := by rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  exact h d hd

lemma agreeCyc_sub {k x y lo len lo' len' : Nat} (hk : 0 < k)
    (h : AgreeCyc k x y lo len)
    (hsub : ∀ d < len', ∃ e < len, (lo' + d) % k = (lo + e) % k) :
    AgreeCyc k x y lo' len' := by
  intro d hd
  rcases hsub d hd with ⟨e, he, heq⟩
  rw [heq]
  exact h e he

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
    rw [rotK_testBit hk hu gap _ hi, rotK_testBit hk hv gap _ hi]
    have hmod : gap % k = gap := Nat.mod_eq_of_lt hgap
    rw [hmod]
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
        congr 1
        omega
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
        congr 1
        omega
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

lemma inv_part (k r : Nat) (hr : 4 ≤ r)
    (sched : Nat → Fin (2 ^ k)) (row column : Fin (2 ^ k)) :
    let h := (k + 1) / 2
    let z := k - h
    let unused := z - (7 * r - 2)
    ∀ (original : Fin (2 ^ k)) (change : Fin (2 ^ unused)),
      let mate := original.val ^^^ (change.val <<< (4 * r - 3))
      stateN k r sched false original.val row.val r >>> z =
        stateN k r sched false mate row.val r >>> z ∧
      stateN k r sched true original.val column.val r >>> z =
        stateN k r sched true mate column.val r >>> z := by
  intro h z unused original change mate
  by_cases hun0 : unused = 0
  · have hchg0 : change.val = 0 := by
      have h1 : 2 ^ unused = 1 := by rw [hun0]; rfl
      have h2 := change.isLt
      omega
    have hmate_eq : mate = original.val := by
      dsimp only [mate]
      rw [hchg0]
      simp
    rw [hmate_eq]
    exact ⟨rfl, rfl⟩
  · have hun_pos : 0 < unused := by omega
    have hzg : 7 * r - 2 < z := by dsimp only [unused] at hun_pos; omega
    have hkgt : 5 * r - 2 ≤ k := by dsimp only [z, h] at *; omega
    have hshift_lt : change.val <<< (4 * r - 3) < 2 ^ k := by
      rw [Nat.shiftLeft_eq]
      have h1 : change.val * 2 ^ (4 * r - 3) < 2 ^ unused * 2 ^ (4 * r - 3) :=
        Nat.mul_lt_mul_of_pos_right change.isLt (by positivity)
      rw [← pow_add] at h1
      have hexp : unused + (4 * r - 3) ≤ k := by dsimp only [unused, z, h] at *; omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hexp)
    have hmate_lt : mate < 2 ^ k := Nat.xor_lt_two_pow original.isLt hshift_lt
    have hagree_out : ∀ b, (b < 4 * r - 3 ∨ z - 3 * r - 1 ≤ b) →
        original.val.testBit b = mate.testBit b := by
      intro b hb
      dsimp only [mate]
      rw [Nat.testBit_xor, Nat.testBit_shiftLeft]
      rcases hb with hlo | hhi
      · have hnot : ¬(4 * r - 3 ≤ b) := by omega
        rw [decide_eq_false hnot, Bool.false_and, Bool.xor_false]
      · have hge : 4 * r - 3 ≤ b := by omega
        have hsub : unused ≤ b - (4 * r - 3) := by dsimp only [unused] at *; omega
        have hfalse : change.val.testBit (b - (4 * r - 3)) = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le change.isLt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hsub))
        rw [decide_eq_true hge, Bool.true_and, hfalse, Bool.xor_false]
    have hrow_hi : ∀ i, z ≤ i → i < k →
        (stateN k r sched false original.val row.val r).testBit i =
        (stateN k r sched false mate row.val r).testBit i := by
      intro i hi1 hi2
      have hLr : rowL r = 2 * r - 2 := by dsimp only [rowL]; omega
      have hag : AgreeCyc k original.val mate (i + k - rowL r) (1 + rowL r + 3 * r - 1) := by
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
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by dsimp only [z, h] at *; omega)]
          rw [hmod]
          exact hagree_out _ (Or.inl (by omega))
      have h0 := row_stateN_congr hr hkgt sched row.isLt original.isLt hmate_lt r le_rfl i 1 hag 0 (by omega)
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hi2] at h0
      exact h0
    have hcol_hi : ∀ i, z ≤ i → i < k →
        (stateN k r sched true original.val column.val r).testBit i =
        (stateN k r sched true mate column.val r).testBit i := by
      intro i hi1 hi2
      have hLc : colL r = 3 * r + 1 := by dsimp only [colL]; omega
      have hag : AgreeCyc k original.val mate (i + k - colL r) (1 + colL r + 4 * r - 3) := by
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
            rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by dsimp only [z, h] at *; omega)]
          rw [hmod]
          exact hagree_out _ (Or.inl (by omega))
      have h0 := col_stateN_congr hr hkgt sched column.isLt original.isLt hmate_lt r le_rfl i 1 hag 0 (by omega)
      simp only [Nat.add_zero, Nat.mod_eq_of_lt hi2] at h0
      exact h0
    constructor
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
      by_cases hj : z + j < k
      · exact hrow_hi (z + j) (by omega) hj
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched false original.val row.isLt r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ z + j))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched false mate row.isLt r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ z + j)))]
    · apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
      by_cases hj : z + j < k
      · exact hcol_hi (z + j) (by omega) hj
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched true original.val column.isLt r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ z + j))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (stateN_lt sched true mate column.isLt r)
              (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : k ≤ z + j)))]

end PEqualNP.Outside.L_meta_25706_aux

open PEqualNP.Outside.L_meta_25706_aux

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_25706 :
∀ (k r : Nat), 4 ≤ r →
  let h := (k+1)/2
  let z := k-h
  let u := 5*r-3
  let extra := min (r-2) (z-6*r)
  let seedWidth := min k u + extra
  let rot := fun (offset x : Nat) =>
    ((x <<< (offset % k)) ||| (x >>> (k - offset % k))) % 2^k
  let mix := fun (gap value : Nat) => value ^^^ rot gap value ^^^ rot (k-gap) value
  let chi := fun (word : Nat) => (List.range k).foldl (fun acc site =>
    acc ||| ((xor (word.testBit site)
      (!(word.testBit ((site+1)%k)) && word.testBit ((site+2)%k))).toNat <<< site)) 0
  let step := fun (constants : Nat → Fin (2^k)) (col : Bool) (raw prev t : Nat) =>
    chi (mix (if col then 2 else 1) prev) ^^^ rot (if col then 3*t+1 else 2*(t-1)) raw ^^^
      (constants (if col then r+t else t)).val
  let state := fun (c : Nat → Fin (2^k)) (side : Bool) (key name : Nat) =>
    (List.range r).foldl (fun v tick => step c side key v (tick+1))
      (rot (if side then 3 else 1) key ^^^ name)
  let rowLen := min h (k-u)
  let colLen := min (r+3) (z-u)
  let unused := z-(7*r-2)
  let start := k-(2*r-2)
  let cut := fun (wordAt offset len : Nat) => (wordAt >>> offset) % 2^len
  let seed := fun (w : Nat) => rot (k - (start % k)) w % 2^seedWidth
  ∀ (sched : Nat → Fin (2^k)) (row column : Fin (2^k)),
    let rowPart := fun rowKey => cut (state sched false rowKey row.val) (k-rowLen) rowLen
    let colPart := fun colKey => cut (state sched true colKey column.val) (z+(r+3)-colLen) colLen
    seedWidth+rowLen+colLen+unused = k ∧
    (∀ (label : Fin (2^seedWidth)) (spare : Fin (2^unused))
        (ra : Fin (2^rowLen)) (ca : Fin (2^colLen)),
      ∃! key : Fin (2^k), seed key.val = label.val ∧
        cut key.val (4*r-3) unused = spare.val ∧ rowPart key.val = ra.val ∧
        colPart key.val = ca.val) ∧
    (∀ (original : Fin (2^k)) (change : Fin (2^unused)),
      let mate := original.val ^^^ (change.val <<< (4*r-3))
      state sched false original.val row.val >>> z = state sched false mate row.val >>> z ∧
        state sched true original.val column.val >>> z = state sched true mate column.val >>> z) := by
  intro k r hr h z u extra seedWidth rot mix chi step state rowLen colLen unused start cut seed
    sched row column rowPart colPart
  have hsum : seedWidth + rowLen + colLen + unused = k := by
    dsimp only [seedWidth, rowLen, colLen, unused, extra, u, z, h]
    omega
  refine ⟨hsum, ?_, ?_⟩
  · let Phi : Fin (2 ^ k) →
        Fin (2 ^ seedWidth) × Fin (2 ^ unused) × Fin (2 ^ rowLen) × Fin (2 ^ colLen) :=
      fun key =>
        (⟨seed key.val, Nat.mod_lt _ (by positivity)⟩,
         ⟨cut key.val (4 * r - 3) unused, Nat.mod_lt _ (by positivity)⟩,
         ⟨rowPart key.val, Nat.mod_lt _ (by positivity)⟩,
         ⟨colPart key.val, Nat.mod_lt _ (by positivity)⟩)
    have hPhi_inj : Function.Injective Phi := by
      intro x y hxy
      have hseed : seed x.val = seed y.val :=
        congrArg Fin.val (congrArg Prod.fst hxy)
      have hspare : cut x.val (4 * r - 3) unused = cut y.val (4 * r - 3) unused :=
        congrArg Fin.val (congrArg (fun p => p.2.1) hxy)
      have hrowP : rowPart x.val = rowPart y.val :=
        congrArg Fin.val (congrArg (fun p => p.2.2.1) hxy)
      have hcolP : colPart x.val = colPart y.val :=
        congrArg Fin.val (congrArg (fun p => p.2.2.2) hxy)
      by_cases hk0 : k = 0
      · subst hk0
        exact Fin.ext (by omega)
      · have hkpos : 0 < k := by omega
        by_cases hkle : k ≤ u
        · have hsw : seedWidth = k := by
            dsimp only [seedWidth, extra, u, z, h]
            omega
          have hrot_eq : rotK k (k - start % k) x.val = rotK k (k - start % k) y.val := by
            have hxlt : rotK k (k - start % k) x.val < 2 ^ k := rotK_lt _ _
            have hylt : rotK k (k - start % k) y.val < 2 ^ k := rotK_lt _ _
            dsimp only [seed] at hseed
            rw [hsw] at hseed
            change rotK k (k - start % k) x.val % 2 ^ k = rotK k (k - start % k) y.val % 2 ^ k at hseed
            rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hseed
            exact hseed
          exact Fin.ext (rotK_inj hkpos (k - start % k) x.isLt y.isLt hrot_eq)
        · have hkgt : 5 * r - 2 ≤ k := by dsimp only [u] at hkle; omega
          have hstart_lt : start < k := by dsimp only [start]; omega
          have hstart_eq : k - start % k = 2 * r - 2 := by
            rw [Nat.mod_eq_of_lt hstart_lt]
            dsimp only [start]
            omega
          have hseed_bit : ∀ j < seedWidth,
              x.val.testBit ((start + j) % k) = y.val.testBit ((start + j) % k) := by
            intro j hj
            have htb : (rotK k (k - start % k) x.val % 2 ^ seedWidth).testBit j =
                (rotK k (k - start % k) y.val % 2 ^ seedWidth).testBit j :=
              congrArg (fun n => n.testBit j) hseed
            rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
              decide_eq_true hj, Bool.true_and, Bool.true_and] at htb
            have hjlt : j < k := by omega
            rw [rotK_testBit hkpos x.isLt _ j hjlt, rotK_testBit hkpos y.isLt _ j hjlt,
              hstart_eq, Nat.mod_eq_of_lt (by omega : 2 * r - 2 < k)] at htb
            have hidx : (j + k - (2 * r - 2)) % k = (start + j) % k := by
              congr 1
              dsimp only [start]
              omega
            rw [hidx] at htb
            exact htb
          have htop : ∀ b, k - (2 * r - 2) ≤ b → b < k → x.val.testBit b = y.val.testBit b := by
            intro b hb1 hb2
            have hj : b - start < seedWidth := by dsimp only [start, seedWidth, u, extra]; omega
            have h := hseed_bit (b - start) hj
            have heq : (start + (b - start)) % k = b := by
              have h1 : start + (b - start) = b := by dsimp only [start]; omega
              rw [h1, Nat.mod_eq_of_lt hb2]
            rw [heq] at h
            exact h
          have hbot : ∀ b < 3 * r - 1 + extra, x.val.testBit b = y.val.testBit b := by
            intro b hb
            have hj : b + (2 * r - 2) < seedWidth := by dsimp only [seedWidth, u, extra]; omega
            have h := hseed_bit (b + (2 * r - 2)) hj
            have heq : (start + (b + (2 * r - 2))) % k = b := by
              have h1 : start + (b + (2 * r - 2)) = b + k := by dsimp only [start]; omega
              have hblt : b < k := by dsimp only [extra, z, h] at hb; omega
              rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hblt]
            rw [heq] at h
            exact h
          have hsp : ∀ b, 4 * r - 3 ≤ b → b < 4 * r - 3 + unused →
              x.val.testBit b = y.val.testBit b := by
            intro b hb1 hb2
            have hj : b - (4 * r - 3) < unused := by omega
            have htb : (cutK x.val (4 * r - 3) unused).testBit (b - (4 * r - 3)) =
                (cutK y.val (4 * r - 3) unused).testBit (b - (4 * r - 3)) := by
              exact congrArg (fun n => n.testBit (b - (4 * r - 3))) hspare
            rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at htb
            have heq : 4 * r - 3 + (b - (4 * r - 3)) = b := by omega
            rw [heq] at htb
            exact htb
          have hrow_solve : ∀ m ≤ rowLen, ∀ b, k - (2 * r - 2) - m ≤ b → b < k →
              x.val.testBit b = y.val.testBit b := by
            intro m
            induction m with
            | zero =>
              intro _ b hb1 hb2
              exact htop b (by omega) hb2
            | succ m ih =>
              intro hm b hb1 hb2
              by_cases hbm : k - (2 * r - 2) - m ≤ b
              · exact ih (by omega) b hbm hb2
              · have hb_eq : b = k - (2 * r - 2) - (m + 1) := by omega
                subst hb_eq
                set p := k - (2 * r - 2) - (m + 1)
                set i := k - (m + 1)
                have hi_lt : i < k := by dsimp only [i]; omega
                have hcone : AgreeCyc k x.val y.val (i + k - (2 * r - 3)) (5 * r - 3) := by
                  intro d hd
                  have hidx : (i + k - (2 * r - 3) + d) % k = (p + 1 + d) % k := by
                    have h1 : i + k - (2 * r - 3) + d = (p + 1 + d) + k := by
                      dsimp only [p, i, rowLen, u, h] at *; omega
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
                    exact hbot (p + 1 + d - k) (by dsimp only [p, extra]; omega)
                have hcm := row_final_chimix_congr hr hkgt sched row.isLt x.isLt y.isLt i hi_lt hcone
                have hst_eq : (stateN k r sched false x.val row.val r).testBit i =
                    (stateN k r sched false y.val row.val r).testBit i := by
                  have hj : i - (k - rowLen) < rowLen := by dsimp only [i]; omega
                  have htb : (cutK (stateN k r sched false x.val row.val r) (k - rowLen) rowLen).testBit
                      (i - (k - rowLen)) =
                      (cutK (stateN k r sched false y.val row.val r) (k - rowLen) rowLen).testBit
                      (i - (k - rowLen)) :=
                    congrArg (fun n => n.testBit (i - (k - rowLen))) hrowP
                  rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at htb
                  have heq : k - rowLen + (i - (k - rowLen)) = i := by dsimp only [i]; omega
                  rw [heq] at htb
                  exact htb
                have hstep_r : ∀ key : Nat,
                    stateN k r sched false key row.val r =
                    stepK k r sched false key (stateN k r sched false key row.val (r - 1)) r := by
                  intro key
                  have hr_eq : r = (r - 1) + 1 := by omega
                  conv_lhs => arg 7; rw [hr_eq]
                  rw [stateN_succ, ← hr_eq]
                rw [hstep_r x.val, hstep_r y.val] at hst_eq
                dsimp only [stepK] at hst_eq
                simp only [Bool.false_eq_true, ↓reduceIte] at hst_eq
                rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, hcm] at hst_eq
                have hrot_eq : (rotK k (2 * (r - 1)) x.val).testBit i =
                    (rotK k (2 * (r - 1)) y.val).testBit i := by
                  revert hst_eq
                  generalize (chiK k (mixK k 1 (stateN k r sched false y.val row.val (r - 1)))).testBit i = a0
                  generalize (rotK k (2 * (r - 1)) x.val).testBit i = b1
                  generalize (rotK k (2 * (r - 1)) y.val).testBit i = b2
                  generalize (sched r).val.testBit i = c0
                  cases a0 <;> cases b1 <;> cases b2 <;> cases c0 <;> decide
                rw [rotK_testBit hkpos x.isLt _ i hi_lt, rotK_testBit hkpos y.isLt _ i hi_lt,
                  Nat.mod_eq_of_lt (by omega : 2 * (r - 1) < k)] at hrot_eq
                have hp_idx : (i + k - 2 * (r - 1)) % k = p := by
                  have h1 : i + k - 2 * (r - 1) = p + k := by
                    dsimp only [p, i, rowLen, u, h] at *; omega
                  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [p]; omega)]
                rw [hp_idx] at hrot_eq
                exact hrot_eq
          have hcol_solve : ∀ m ≤ colLen, ∀ b, k - (2 * r - 2) - rowLen - m ≤ b → b < k →
              x.val.testBit b = y.val.testBit b := by
            intro m
            induction m with
            | zero =>
              intro _ b hb1 hb2
              exact hrow_solve rowLen le_rfl b (by omega) hb2
            | succ m ih =>
              intro hm b hb1 hb2
              by_cases hbm : k - (2 * r - 2) - rowLen - m ≤ b
              · exact ih (by omega) b hbm hb2
              · have hb_eq : b = k - (2 * r - 2) - rowLen - (m + 1) := by omega
                subst hb_eq
                have hcol_pos : 0 < colLen := by omega
                have hzu : u < z := by dsimp only [colLen] at hcol_pos; omega
                have hrl_eq : rowLen = h := by dsimp only [rowLen, u, z, h] at *; omega
                have hkz : k - rowLen = z := by dsimp only [z, h] at *; omega
                set q := k - (2 * r - 2) - rowLen - (m + 1)
                set i := z + (r + 3) - (m + 1)
                have hi_lt : i < k := by dsimp only [i, u, z, h] at *; omega
                have hcone : AgreeCyc k x.val y.val (i + k - 3 * r) (7 * r - 2) := by
                  intro d hd
                  have hidx : (i + k - 3 * r + d) % k = (q + 1 + d) % k := by
                    have h1 : i + k - 3 * r + d = (q + 1 + d) + k := by
                      dsimp only [q, i, colLen, u, z, h] at *; omega
                    rw [h1, Nat.add_mod_right]
                  rw [hidx]
                  by_cases hwrap : q + 1 + d < k
                  · rw [Nat.mod_eq_of_lt hwrap]
                    exact ih (by omega) (q + 1 + d) (by dsimp only [q]; omega) hwrap
                  · have hmod : (q + 1 + d) % k = q + 1 + d - k := by
                      have h1 : q + 1 + d = (q + 1 + d - k) + k := by omega
                      conv_lhs => rw [h1]
                      rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q, u, z, h] at *; omega)]
                    rw [hmod]
                    exact hbot (q + 1 + d - k) (by dsimp only [q, u, z, h, extra] at *; omega)
                have hcm := col_final_chimix_congr hr hkgt sched column.isLt x.isLt y.isLt i hi_lt hcone
                have hst_eq : (stateN k r sched true x.val column.val r).testBit i =
                    (stateN k r sched true y.val column.val r).testBit i := by
                  have hj : i - (z + (r + 3) - colLen) < colLen := by dsimp only [i]; omega
                  have htb : (cutK (stateN k r sched true x.val column.val r) (z + (r + 3) - colLen) colLen).testBit
                      (i - (z + (r + 3) - colLen)) =
                      (cutK (stateN k r sched true y.val column.val r) (z + (r + 3) - colLen) colLen).testBit
                      (i - (z + (r + 3) - colLen)) :=
                    congrArg (fun n => n.testBit (i - (z + (r + 3) - colLen))) hcolP
                  rw [cutK_testBit _ _ _ _ hj, cutK_testBit _ _ _ _ hj] at htb
                  have heq : z + (r + 3) - colLen + (i - (z + (r + 3) - colLen)) = i := by
                    dsimp only [i]; omega
                  rw [heq] at htb
                  exact htb
                have hstep_r : ∀ key : Nat,
                    stateN k r sched true key column.val r =
                    stepK k r sched true key (stateN k r sched true key column.val (r - 1)) r := by
                  intro key
                  have hr_eq : r = (r - 1) + 1 := by omega
                  conv_lhs => arg 7; rw [hr_eq]
                  rw [stateN_succ, ← hr_eq]
                rw [hstep_r x.val, hstep_r y.val] at hst_eq
                dsimp only [stepK] at hst_eq
                simp only [↓reduceIte] at hst_eq
                rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, hcm] at hst_eq
                have hrot_eq : (rotK k (3 * r + 1) x.val).testBit i =
                    (rotK k (3 * r + 1) y.val).testBit i := by
                  revert hst_eq
                  generalize (chiK k (mixK k 2 (stateN k r sched true y.val column.val (r - 1)))).testBit i = a0
                  generalize (rotK k (3 * r + 1) x.val).testBit i = b1
                  generalize (rotK k (3 * r + 1) y.val).testBit i = b2
                  generalize (sched (r + r)).val.testBit i = c0
                  cases a0 <;> cases b1 <;> cases b2 <;> cases c0 <;> decide
                rw [rotK_testBit hkpos x.isLt _ i hi_lt, rotK_testBit hkpos y.isLt _ i hi_lt,
                  Nat.mod_eq_of_lt (by omega : 3 * r + 1 < k)] at hrot_eq
                have hq_idx : (i + k - (3 * r + 1)) % k = q := by
                  have h1 : i + k - (3 * r + 1) = q + k := by
                    dsimp only [q, i, colLen, u, z, h] at *; omega
                  rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by dsimp only [q]; omega)]
                rw [hq_idx] at hrot_eq
                exact hrot_eq
          apply Fin.ext
          apply Nat.eq_of_testBit_eq
          intro b
          by_cases hbk : b < k
          · by_cases hhigh : k - (2 * r - 2) - rowLen - colLen ≤ b
            · exact hcol_solve colLen le_rfl b hhigh hbk
            · by_cases hlow : b < 3 * r - 1 + extra
              · exact hbot b hlow
              · exact hsp b (by dsimp only [extra, unused, rowLen, colLen, u, z, h] at *; omega)
                  (by dsimp only [extra, unused, rowLen, colLen, u, z, h] at *; omega)
          · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega))),
                Nat.testBit_eq_false_of_lt (lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)))]
    have hcard : Fintype.card (Fin (2 ^ k)) =
        Fintype.card (Fin (2 ^ seedWidth) × Fin (2 ^ unused) × Fin (2 ^ rowLen) × Fin (2 ^ colLen)) := by
      simp only [Fintype.card_prod, Fintype.card_fin]
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega
    have hPhi_bij : Function.Bijective Phi :=
      (Fintype.bijective_iff_injective_and_card Phi).2 ⟨hPhi_inj, hcard⟩
    intro label spare ra ca
    rcases hPhi_bij.2 (label, spare, ra, ca) with ⟨key, hkey⟩
    refine ⟨key, ?_, ?_⟩
    · exact ⟨congrArg Fin.val (congrArg Prod.fst hkey),
        congrArg Fin.val (congrArg (fun p => p.2.1) hkey),
        congrArg Fin.val (congrArg (fun p => p.2.2.1) hkey),
        congrArg Fin.val (congrArg (fun p => p.2.2.2) hkey)⟩
    · rintro key' ⟨h1, h2, h3, h4⟩
      apply hPhi_inj
      rw [hkey]
      exact Prod.ext (Fin.ext h1) (Prod.ext (Fin.ext h2) (Prod.ext (Fin.ext h3) (Fin.ext h4)))
  · exact inv_part k r hr sched row column
