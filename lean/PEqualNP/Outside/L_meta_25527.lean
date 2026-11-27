import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25527

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def rot (k s word : Nat) : Nat :=
  ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k

def step (k word : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (word.testBit i)
      (!(word.testBit ((i + 1) % k)) && word.testBit ((i + 2) % k))).toNat <<< i)) 0

def mix (k word : Nat) : Nat :=
  word ^^^ rot k 1 word ^^^ rot k (k - 1) word

def cval (k j : Nat) : Nat :=
  3 ^ (k + j) % 2 ^ k

def rowState (k rounds key row : Nat) : Nat :=
  (List.range rounds).foldl (fun rowState rowIndex =>
    step k (rowState ^^^ rot k 1 rowState ^^^ rot k (k - 1) rowState) ^^^
      rot k (2 * rowIndex) key ^^^ cval k (rowIndex + 1)) (rot k 1 key ^^^ row)

def colState (k r rounds key col : Nat) : Nat :=
  (List.range rounds).foldl (fun colState colIndex =>
    step k (colState ^^^ rot k 2 colState ^^^ rot k (k - 2) colState) ^^^
      rot k (3 * (colIndex + 1) + 1) key ^^^ cval k (r + (colIndex + 1))) (rot k 3 key ^^^ col)

lemma xor_cancel_left (c a b : Bool) : xor (xor c a) (xor c b) = xor a b := by
  cases c <;> cases a <;> cases b <;> rfl

lemma xor_cancel_right (a b c : Bool) : xor (xor a c) (xor b c) = xor a b := by
  cases c <;> cases a <;> cases b <;> rfl

lemma xor_triple_diff (a1 a2 y z : Bool) :
    xor (xor (xor a1 y) z) (xor (xor a2 y) z) = xor a1 a2 := by
  cases a1 <;> cases a2 <;> cases y <;> cases z <;> rfl

lemma rot_lt (k s word : Nat) : rot k s word < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma cval_lt (k j : Nat) : cval k j < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma testBit_pack (f : Nat → Bool) (n j : Nat) :
    ((List.range n).foldl (fun acc m => acc ||| ((f m).toNat <<< m)) 0).testBit j =
      (decide (j < n) && f j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.testBit_or, ih, Nat.shiftLeft_eq]
    by_cases h : n = j
    · subst h; cases f n <;> simp
    · have hcmp : j < n + 1 ↔ j < n := by omega
      cases f n <;> simp [h, hcmp]

lemma step_lt (k word : Nat) : step k word < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  unfold step
  rw [testBit_pack]
  simp [Nat.not_lt_of_ge hj]

lemma rowState_zero (k key row : Nat) :
    rowState k 0 key row = rot k 1 key ^^^ row := rfl

lemma rowState_succ (k t key row : Nat) :
    rowState k (t + 1) key row =
      step k (mix k (rowState k t key row)) ^^^ rot k (2 * t) key ^^^ cval k (t + 1) := by
  unfold rowState mix
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma rowState_lt {k row : Nat} (hr : row < 2 ^ k) (t key : Nat) :
    rowState k t key row < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 1 key) hr
  | succ t =>
    rw [rowState_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k _ _)) (cval_lt k _)

lemma colState_zero (k r key col : Nat) :
    colState k r 0 key col = rot k 3 key ^^^ col := rfl

lemma colState_succ (k r t key col : Nat) :
    colState k r (t + 1) key col =
      step k (colState k r t key col ^^^ rot k 2 (colState k r t key col) ^^^
        rot k (k - 2) (colState k r t key col)) ^^^
        rot k (3 * (t + 1) + 1) key ^^^ cval k (r + (t + 1)) := by
  unfold colState
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma colState_lt {k col : Nat} (hc : col < 2 ^ k) (r t key : Nat) :
    colState k r t key col < 2 ^ k := by
  cases t with
  | zero => exact Nat.xor_lt_two_pow (rot_lt k 3 key) hc
  | succ t =>
    rw [colState_succ]
    exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt k _) (rot_lt k _ _)) (cval_lt k _)

lemma testBit_rot {k s word b : Nat} (hw : word < 2 ^ k) (hb : b < k) :
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

lemma testBit_step {k word b : Nat} (hb : b < k) :
    (step k word).testBit b =
      xor (word.testBit b) (!(word.testBit ((b + 1) % k)) && word.testBit ((b + 2) % k)) := by
  unfold step
  rw [testBit_pack]
  simp [hb]

lemma testBit_mix {k word b : Nat} (hk : 2 ≤ k) (hw : word < 2 ^ k) (hb : b < k) :
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

lemma mod_sub_eq {k p s : Nat} (hk : 0 < k) (hsp : s ≤ p) :
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

lemma mod_ne_of_lt_diff {k a b : Nat} (hlt : a < b) (hd : b - a < k) :
    a % k ≠ b % k := by
  have hk : 0 < k := by omega
  have ha : a % k < k := Nat.mod_lt a hk
  have hb : b % k = (a % k + (b - a)) % k := by
    rw [Nat.mod_add_mod, show a + (b - a) = b by omega]
  rw [hb]
  by_cases hs : a % k + (b - a) < k
  · rw [Nat.mod_eq_of_lt hs]; omega
  · have hge : k ≤ a % k + (b - a) := by omega
    have hlt' : a % k + (b - a) - k < k := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt']; omega

lemma testBit_putBit_eq {w p : Nat} {b : Bool} (h0 : w.testBit p = false) :
    (w ||| (b.toNat <<< p)).testBit p = b := by
  rw [Nat.testBit_or, h0, Bool.false_or, Nat.testBit_shiftLeft]
  cases b <;> simp

lemma testBit_putBit_ne {w p j : Nat} {b : Bool} (hne : j ≠ p) :
    (w ||| (b.toNat <<< p)).testBit j = w.testBit j := by
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hle : p ≤ j
  · have hsub : 1 ≤ j - p := by omega
    have hbt : b.toNat.testBit (j - p) = false := by
      cases b
      · simp
      · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1)
          (Nat.pow_le_pow_right Nat.zero_lt_two hsub))
    simp [hle, hbt]
  · simp [hle]

lemma putBit_lt {k w p : Nat} {b : Bool} (hw : w < 2 ^ k) (hp : p < k) :
    w ||| (b.toNat <<< p) < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_putBit_ne (by omega)]
  exact Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hj))

def lineStep (k u : Nat) (src : Nat → Bool) : Nat → Nat → Bool
  | 0, p => src p
  | s + 1, p =>
    let prev := lineStep k u src s
    let m0 := xor (xor (prev p) (prev (p - 1))) (prev (p + 1))
    let m1 := xor (xor (prev (p + 1)) (prev p)) (prev (p + 2))
    let m2 := xor (xor (prev (p + 2)) (prev (p + 1))) (prev (p + 3))
    let st := xor m0 (!m1 && m2)
    let inj := xor (src (p + 1 - 2 * s)) (u.testBit ((p + 1 - 2 * s) % k))
    xor (xor st inj) ((cval k (s + 1)).testBit (p % k))

lemma lineStep_succ (k u : Nat) (src : Nat → Bool) (s p : Nat) :
    lineStep k u src (s + 1) p =
      xor (xor (xor (xor (xor (lineStep k u src s p) (lineStep k u src s (p - 1)))
          (lineStep k u src s (p + 1)))
        (!(xor (xor (lineStep k u src s (p + 1)) (lineStep k u src s p))
          (lineStep k u src s (p + 2))) &&
         (xor (xor (lineStep k u src s (p + 2)) (lineStep k u src s (p + 1)))
          (lineStep k u src s (p + 3)))))
        (xor (src (p + 1 - 2 * s)) (u.testBit ((p + 1 - 2 * s) % k))))
        ((cval k (s + 1)).testBit (p % k)) := rfl

lemma lineStep_eq_rowState {k u key : Nat} (hk : 2 ≤ k) (hu : u < 2 ^ k) (hkey : key < 2 ^ k) :
    let src := fun pos : Nat => (rot k 1 key ^^^ u).testBit (pos % k)
    ∀ s p, 2 * s ≤ p → lineStep k u src s p = (rowState k s key u).testBit (p % k) := by
  intro src s
  have hk0 : 0 < k := by omega
  induction s with
  | zero =>
    intro p _
    rfl
  | succ s ih =>
    intro p hp
    simp only [lineStep]
    rw [rowState_succ, Nat.testBit_xor, Nat.testBit_xor, testBit_step (Nat.mod_lt p hk0)]
    have hm : ∀ d, (mix k (rowState k s key u)).testBit ((p % k + d) % k) =
        xor (xor (lineStep k u src s (p + d))
                 (lineStep k u src s (p + d - 1)))
            (lineStep k u src s (p + d + 1)) := by
      intro d
      have hlt : (p % k + d) % k < k := Nat.mod_lt _ hk0
      rw [testBit_mix hk (rowState_lt hu s key) hlt]
      have h0 : (p % k + d) % k = (p + d) % k := Nat.mod_add_mod p k d
      have h1 : ((p + d) % k + k - 1) % k = (p + d - 1) % k := by
        have h1m : 1 = 1 % k := (Nat.mod_eq_of_lt (by omega)).symm
        conv_lhs => rw [h1m]
        exact mod_sub_eq hk0 (by omega)
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
    rw [hm0, hm1, hm2]
    have hinj : xor (src (p + 1 - 2 * s)) (u.testBit ((p + 1 - 2 * s) % k)) =
        (rot k (2 * s) key).testBit (p % k) := by
      simp only [src, Nat.testBit_xor]
      have hrot1 : (rot k 1 key).testBit ((p + 1 - 2 * s) % k) =
          key.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot hkey (Nat.mod_lt _ hk0)]
        have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
        have hsub : p + 1 - 2 * s - 1 = p - 2 * s := by omega
        rw [← hsub]
        have h1' := mod_sub_eq hk0 (p := p + 1 - 2 * s) (s := 1) (by omega)
        rw [h1m] at h1' ⊢
        exact congrArg key.testBit h1'
      have hrot2 : (rot k (2 * s) key).testBit (p % k) =
          key.testBit ((p - 2 * s) % k) := by
        rw [testBit_rot hkey (Nat.mod_lt _ hk0), mod_sub_eq hk0 (by omega)]
      rw [hrot1, hrot2]
      cases key.testBit ((p - 2 * s) % k) <;> cases u.testBit ((p + 1 - 2 * s) % k) <;> rfl
    rw [hinj]

lemma lineStep_agree_right (k u : Nat) (f g : Nat → Bool) (L : Nat)
    (hfg : ∀ p, L < p → f p = g p) :
    ∀ s p, max (L + s + 1) (L + 2 * s - 2) ≤ p →
      lineStep k u f s p = lineStep k u g s p := by
  intro s
  induction s with
  | zero =>
    intro p hp
    simp only [lineStep]
    exact hfg p (by omega)
  | succ s ih =>
    intro p hp
    simp only [lineStep]
    have h0 := ih (p - 1) (by omega)
    have h1 := ih p (by omega)
    have h2 := ih (p + 1) (by omega)
    have h3 := ih (p + 2) (by omega)
    have h4 := ih (p + 3) (by omega)
    have hi := hfg (p + 1 - 2 * s) (by omega)
    rw [h0, h1, h2, h3, h4, hi]

def wt (len code : Nat) : Nat :=
  ((List.range len).filter (fun idx => code.testBit idx)).length

lemma wt_zero (code : Nat) : wt 0 code = 0 := rfl

lemma wt_le (len code : Nat) : wt len code ≤ len := by
  simpa [wt] using List.length_filter_le (fun idx => code.testBit idx) (List.range len)

lemma wt_succ (len code : Nat) :
    wt (len + 1) code = wt len code + (code.testBit len).toNat := by
  unfold wt
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : code.testBit len <;> simp [h]

lemma wt_mono_sub {a b : Nat} (code : Nat) (h : a ≤ b) :
    wt b code ≤ wt a code + (b - a) := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this; simp [wt]
  | succ b ih =>
    by_cases hle : a ≤ b
    · have := ih hle
      rw [wt_succ]
      cases code.testBit b <;> simp <;> omega
    · have : a = b + 1 := by omega
      subst this; omega

lemma wt_congr {len c1 c2 : Nat} (h : ∀ j < len, c1.testBit j = c2.testBit j) :
    wt len c1 = wt len c2 := by
  unfold wt
  congr 1
  apply List.filter_congr
  intro j hj
  exact h j (List.mem_range.mp hj)

def guardBit (k u idx b key : Nat) : Bool :=
  let prev := rowState k (idx + 4) key u
  xor (xor (prev.testBit (b % k)) (prev.testBit ((b + 1) % k)))
    (prev.testBit ((b + 2) % k))

def traceRun (k u q len key : Nat) : Nat × Nat :=
  (List.range len).foldl (fun (posCode : Nat × Nat) idx =>
    let pos := posCode.1 - 2
    let hit := guardBit k u idx pos key
    (pos - (if hit then 0 else 1), posCode.2 ||| (hit.toNat <<< idx)))
    (q - 13, 0)

lemma traceRun_zero (k u q key : Nat) :
    traceRun k u q 0 key = (q - 13, 0) := rfl

lemma traceRun_succ (k u q len key : Nat) :
    traceRun k u q (len + 1) key =
      let tr := traceRun k u q len key
      let pos := tr.1 - 2
      let hit := guardBit k u len pos key
      (pos - (if hit then 0 else 1), tr.2 ||| (hit.toNat <<< len)) := by
  unfold traceRun
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma traceRun_spec {k u key : Nat} (hk : 2 ≤ k) (hu : u < 2 ^ k) (hkey : key < 2 ^ k) (q : Nat) :
    let src := fun pos : Nat => (rot k 1 key ^^^ u).testBit (pos % k)
    let trunc := fun pos : Nat => if pos < q then src pos else false
    ∀ (len : Nat), 3 * len + 16 ≤ q →
      let tr := traceRun k u q len key
      tr.1 = q + wt len tr.2 - 3 * (len + 4) - 1 ∧
      (∀ d, len ≤ d → tr.2.testBit d = false) ∧
      (∀ p, 2 * (len + 4) ≤ p → p ≤ tr.1 →
        lineStep k u src (len + 4) p = lineStep k u trunc (len + 4) p) := by
  intro src trunc len
  induction len with
  | zero =>
    intro hq
    refine ⟨by simp [traceRun, wt]; omega, fun d _ => by simp [traceRun], ?_⟩
    have h4 : ∀ s, s ≤ 4 → ∀ p, 2 * s ≤ p → p ≤ q - 1 - 3 * s →
        lineStep k u src s p = lineStep k u trunc s p := by
      intro s
      induction s with
      | zero =>
        intro _ p _ hp
        simp only [lineStep, trunc, show p < q by omega, ↓reduceIte]
      | succ s ih =>
        intro hs p hp1 hp2
        simp only [lineStep]
        have h0 := ih (by omega) (p - 1) (by omega) (by omega)
        have h1 := ih (by omega) p (by omega) (by omega)
        have h2 := ih (by omega) (p + 1) (by omega) (by omega)
        have h3 := ih (by omega) (p + 2) (by omega) (by omega)
        have h4' := ih (by omega) (p + 3) (by omega) (by omega)
        have hsrc : trunc (p + 1 - 2 * s) = src (p + 1 - 2 * s) := by
          simp only [trunc, show p + 1 - 2 * s < q by omega, ↓reduceIte]
        rw [h0, h1, h2, h3, h4', hsrc]
    intro p hp1 hp2
    exact h4 4 (by omega) p hp1 (by simp only [traceRun, List.range_zero, List.foldl_nil] at hp2; omega)
  | succ len ih =>
    intro hq
    rcases ih (by omega) with ⟨hpos_prev, hhi_prev, hagree_prev⟩
    set tr0 := traceRun k u q len key with htr0
    let pos := tr0.1 - 2
    let hit := guardBit k u len pos key
    have htr1_1 : (traceRun k u q (len + 1) key).1 = pos - (if hit then 0 else 1) := by
      rw [traceRun_succ]
    have htr1_2 : (traceRun k u q (len + 1) key).2 = tr0.2 ||| (hit.toNat <<< len) := by
      rw [traceRun_succ]
    have hbit_new : ∀ d, (traceRun k u q (len + 1) key).2.testBit d =
        if d = len then hit else tr0.2.testBit d := by
      intro d
      rw [htr1_2]
      by_cases hd : d = len
      · subst hd
        simp only [↓reduceIte, testBit_putBit_eq (hhi_prev d (le_refl d))]
      · simp only [hd, ↓reduceIte, testBit_putBit_ne hd]
    have hones_succ : wt (len + 1) (traceRun k u q (len + 1) key).2 =
        wt len tr0.2 + hit.toNat := by
      rw [wt_succ, hbit_new len]
      simp only [↓reduceIte]
      have hcongr : wt len (traceRun k u q (len + 1) key).2 = wt len tr0.2 := by
        apply wt_congr
        intro d hd
        rw [hbit_new d]
        simp only [show d ≠ len by omega, ↓reduceIte]
      rw [hcongr]
    have hones_le : wt len tr0.2 ≤ len := wt_le len tr0.2
    refine ⟨?_, ?_, ?_⟩
    · rw [htr1_1, hones_succ]
      simp only [pos]
      cases hit <;> simp <;> omega
    · intro d hd
      rw [hbit_new d]
      simp only [show d ≠ len by omega, ↓reduceIte]
      exact hhi_prev d (by omega)
    · intro p hp1 hp2
      rw [htr1_1] at hp2
      have htr0_le_q : tr0.1 < q := by omega
      have hsrc_inj : trunc (p + 1 - 2 * (len + 4)) = src (p + 1 - 2 * (len + 4)) := by
        simp only [trunc, show p + 1 - 2 * (len + 4) < q by omega, ↓reduceIte]
      have hstep_eq : len + 1 + 4 = (len + 4) + 1 := by omega
      rw [hstep_eq, lineStep_succ k u src (len + 4) p, lineStep_succ k u trunc (len + 4) p, hsrc_inj]
      by_cases hlt : p + 3 ≤ tr0.1
      · have h0 := hagree_prev (p - 1) (by omega) (by omega)
        have h1 := hagree_prev p (by omega) (by omega)
        have h2 := hagree_prev (p + 1) (by omega) (by omega)
        have h3 := hagree_prev (p + 2) (by omega) (by omega)
        have h4 := hagree_prev (p + 3) (by omega) (by omega)
        rw [h0, h1, h2, h3, h4]
      · have hhit_true : hit = true := by
          cases hh : hit
          · rw [hh] at hp2; simp only [Bool.false_eq_true, ↓reduceIte, pos] at hp2; omega
          · rfl
        have hp_eq : p = pos := by
          rw [hhit_true] at hp2; simp only [↓reduceIte, Nat.sub_zero, pos] at hp2 ⊢; omega
        have h0 := hagree_prev (p - 1) (by omega) (by omega)
        have h1 := hagree_prev p (by omega) (by omega)
        have h2 := hagree_prev (p + 1) (by omega) (by omega)
        have h3 := hagree_prev (p + 2) (by omega) (by omega)
        have hm1_true : xor (xor (lineStep k u src (len + 4) (p + 1))
            (lineStep k u src (len + 4) p))
            (lineStep k u src (len + 4) (p + 2)) = true := by
          rw [lineStep_eq_rowState hk hu hkey (len + 4) (p + 1) (by omega),
              lineStep_eq_rowState hk hu hkey (len + 4) p (by omega),
              lineStep_eq_rowState hk hu hkey (len + 4) (p + 2) (by omega)]
          have : hit = true := hhit_true
          simp only [hit, guardBit, ← hp_eq] at this
          rw [← this]
          cases (rowState k (len + 4) key u).testBit (p % k) <;>
          cases (rowState k (len + 4) key u).testBit ((p + 1) % k) <;>
          cases (rowState k (len + 4) key u).testBit ((p + 2) % k) <;> rfl
        rw [h1, h2, h3] at hm1_true
        rw [h0, h1, h2, h3, hm1_true]
        simp

lemma traceRun_lt_two_pow {k u key : Nat} (hk : 2 ≤ k) (hu : u < 2 ^ k) (hkey : key < 2 ^ k)
    (q len : Nat) (hq : 3 * len + 16 ≤ q) :
    (traceRun k u q len key).2 < 2 ^ len := by
  apply Nat.lt_pow_two_of_testBit
  exact (traceRun_spec hk hu hkey q len hq).2.1

lemma startBit_eq_of_keyBit {k u a z p : Nat} (hk : 2 ≤ k) (ha : a < 2 ^ k) (hz : z < 2 ^ k)
    (hp : 1 ≤ p) (hbit : a.testBit ((p - 1) % k) = z.testBit ((p - 1) % k)) :
    (rot k 1 a ^^^ u).testBit (p % k) = (rot k 1 z ^^^ u).testBit (p % k) := by
  have hk0 : 0 < k := by omega
  have h1m : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot ha (Nat.mod_lt p hk0),
    testBit_rot hz (Nat.mod_lt p hk0)]
  have hmod : (p % k + k - 1 % k) % k = (p - 1) % k := mod_sub_eq hk0 hp
  rw [hmod, hbit]

lemma startBit_xor_eq {k u a z p : Nat} (hk : 2 ≤ k) (ha : a < 2 ^ k) (hz : z < 2 ^ k)
    (hp : 1 ≤ p) :
    xor ((rot k 1 a ^^^ u).testBit (p % k)) ((rot k 1 z ^^^ u).testBit (p % k)) =
      xor (a.testBit ((p - 1) % k)) (z.testBit ((p - 1) % k)) := by
  have hk0 : 0 < k := by omega
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_rot ha (Nat.mod_lt p hk0),
    testBit_rot hz (Nat.mod_lt p hk0), mod_sub_eq hk0 hp]
  exact xor_cancel_right _ _ _

lemma traceRun_agree_above {k u a z q L : Nat} (hk : 2 ≤ k) (hu : u < 2 ^ k)
    (ha : a < 2 ^ k) (hz : z < 2 ^ k)
    (hagree : ∀ p, L < p → p < q → (rot k 1 a ^^^ u).testBit (p % k) = (rot k 1 z ^^^ u).testBit (p % k)) :
    ∀ len, 3 * len + 16 ≤ q →
      (∀ idx < len,
        2 * (idx + 4) ≤ (traceRun k u q idx z).1 - 2 ∧
        L + 2 * (idx + 4) - 2 ≤ (traceRun k u q idx z).1 - 2) →
      traceRun k u q len a = traceRun k u q len z := by
  intro len
  induction len with
  | zero => intro _ _; rfl
  | succ len ih =>
    intro hq hcond
    have hprev : traceRun k u q len a = traceRun k u q len z :=
      ih (by omega) (fun idx hidx => hcond idx (by omega))
    rw [traceRun_succ, traceRun_succ, hprev]
    have hcl := hcond len (Nat.lt_succ_self len)
    set b := (traceRun k u q len z).1 - 2
    have hspec_a := traceRun_spec hk hu ha q len (by omega)
    have hspec_z := traceRun_spec hk hu hz q len (by omega)
    rw [hprev] at hspec_a
    let trA := fun p => if p < q then (rot k 1 a ^^^ u).testBit (p % k) else false
    let trZ := fun p => if p < q then (rot k 1 z ^^^ u).testBit (p % k) else false
    have htr_agree : ∀ p, L < p → trA p = trZ p := by
      intro p hp
      simp only [trA, trZ]
      by_cases hpq : p < q
      · simp only [hpq, ↓reduceIte]; exact hagree p hp hpq
      · simp only [hpq, ↓reduceIte]
    have hbit : ∀ δ ≤ 2,
        (rowState k (len + 4) a u).testBit ((b + δ) % k) =
        (rowState k (len + 4) z u).testBit ((b + δ) % k) := by
      intro δ hδ
      rw [← lineStep_eq_rowState hk hu ha (len + 4) (b + δ) (by omega),
          ← lineStep_eq_rowState hk hu hz (len + 4) (b + δ) (by omega),
          hspec_a.2.2 (b + δ) (by omega) (by omega),
          hspec_z.2.2 (b + δ) (by omega) (by omega)]
      exact lineStep_agree_right k u trA trZ L htr_agree (len + 4) (b + δ) (by omega)
    have hg : guardBit k u len b a = guardBit k u len b z := by
      dsimp only [guardBit]
      have h0 := hbit 0 (by decide)
      have h1 := hbit 1 (by decide)
      have h2 := hbit 2 (by decide)
      simp only [Nat.add_zero] at h0
      rw [h0, h1, h2]
    dsimp only
    rw [hg]

lemma guard_xor_eq {k u a z q s : Nat} (hk : 2 ≤ k) (hu : u < 2 ^ k)
    (ha : a < 2 ^ k) (hz : z < 2 ^ k) (hq : 3 * s + 16 ≤ q)
    (htr : traceRun k u q s a = traceRun k u q s z) :
    let b := (traceRun k u q s z).1 - 2
    let left := b + 5 - 2 * (s + 5)
    2 * (s + 4) + 2 ≤ b → 1 ≤ left → left < q →
    (∀ p, left < p → p < q → (rot k 1 a ^^^ u).testBit (p % k) = (rot k 1 z ^^^ u).testBit (p % k)) →
    xor (guardBit k u s b a) (guardBit k u s b z) =
      xor (a.testBit ((left - 1) % k)) (z.testBit ((left - 1) % k)) := by
  intro b left hb_ge hleft1 hleftq hagree
  have hspec_a := traceRun_spec hk hu ha q s hq
  have hspec_z := traceRun_spec hk hu hz q s hq
  rw [htr] at hspec_a
  let trA := fun p => if p < q then (rot k 1 a ^^^ u).testBit (p % k) else false
  let trZ := fun p => if p < q then (rot k 1 z ^^^ u).testBit (p % k) else false
  have htr_agree : ∀ p, left < p → trA p = trZ p := by
    intro p hp
    simp only [trA, trZ]
    by_cases hpq : p < q
    · simp only [hpq, ↓reduceIte]; exact hagree p hp hpq
    · simp only [hpq, ↓reduceIte]
  have hga : guardBit k u s b a =
      xor (xor (lineStep k u trA (s + 4) b) (lineStep k u trA (s + 4) (b + 1)))
        (lineStep k u trA (s + 4) (b + 2)) := by
    dsimp only [guardBit]
    rw [← lineStep_eq_rowState hk hu ha (s + 4) b (by omega),
        ← lineStep_eq_rowState hk hu ha (s + 4) (b + 1) (by omega),
        ← lineStep_eq_rowState hk hu ha (s + 4) (b + 2) (by omega),
        hspec_a.2.2 b (by omega) (by omega),
        hspec_a.2.2 (b + 1) (by omega) (by omega),
        hspec_a.2.2 (b + 2) (by omega) (by omega)]
  have hgz : guardBit k u s b z =
      xor (xor (lineStep k u trZ (s + 4) b) (lineStep k u trZ (s + 4) (b + 1)))
        (lineStep k u trZ (s + 4) (b + 2)) := by
    dsimp only [guardBit]
    rw [← lineStep_eq_rowState hk hu hz (s + 4) b (by omega),
        ← lineStep_eq_rowState hk hu hz (s + 4) (b + 1) (by omega),
        ← lineStep_eq_rowState hk hu hz (s + 4) (b + 2) (by omega),
        hspec_z.2.2 b (by omega) (by omega),
        hspec_z.2.2 (b + 1) (by omega) (by omega),
        hspec_z.2.2 (b + 2) (by omega) (by omega)]
  have hb1 : lineStep k u trA (s + 4) (b + 1) = lineStep k u trZ (s + 4) (b + 1) :=
    lineStep_agree_right k u trA trZ left htr_agree (s + 4) (b + 1) (by omega)
  have hb2 : lineStep k u trA (s + 4) (b + 2) = lineStep k u trZ (s + 4) (b + 2) :=
    lineStep_agree_right k u trA trZ left htr_agree (s + 4) (b + 2) (by omega)
  have hb0 : xor (lineStep k u trA (s + 4) b) (lineStep k u trZ (s + 4) b) =
      xor (a.testBit ((left - 1) % k)) (z.testBit ((left - 1) % k)) := by
    have hs4 : s + 4 = (s + 3) + 1 := by omega
    rw [hs4, lineStep_succ k u trA (s + 3) b, lineStep_succ k u trZ (s + 3) b]
    have hp0 := lineStep_agree_right k u trA trZ left htr_agree (s + 3) (b - 1) (by omega)
    have hp1 := lineStep_agree_right k u trA trZ left htr_agree (s + 3) b (by omega)
    have hp2 := lineStep_agree_right k u trA trZ left htr_agree (s + 3) (b + 1) (by omega)
    have hp3 := lineStep_agree_right k u trA trZ left htr_agree (s + 3) (b + 2) (by omega)
    have hp4 := lineStep_agree_right k u trA trZ left htr_agree (s + 3) (b + 3) (by omega)
    have hidx : b + 1 - 2 * (s + 3) = left := by omega
    rw [hp0, hp1, hp2, hp3, hp4, hidx]
    rw [xor_cancel_right, xor_cancel_left, xor_cancel_right]
    simp only [trA, trZ, hleftq, ↓reduceIte]
    exact startBit_xor_eq hk ha hz hleft1
  rw [hga, hgz, hb1, hb2, xor_triple_diff, hb0]

lemma row_xor_eq {k r d u a z j' : Nat} (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    (hu : u < 2 ^ k) (ha : a < 2 ^ k) (hz : z < 2 ^ k) :
    let h := (k + 1) / 2
    let i := k - h
    let q := k + i + 3 * r - d
    let n := r - 5
    let m := wt n (traceRun k u q n z).2 - d
    let pos0 := q - k + j'
    j' < m →
    traceRun k u q n a = traceRun k u q n z →
    (∀ p, pos0 < p → p < q → (rot k 1 a ^^^ u).testBit (p % k) = (rot k 1 z ^^^ u).testBit (p % k)) →
    xor ((rowState k r a u).testBit (i + j')) ((rowState k r z u).testBit (i + j')) =
      xor (a.testBit ((pos0 - 1) % k)) (z.testBit ((pos0 - 1) % k)) := by
  intro h i q n m pos0 hj' htr hagree
  have hk2 : 2 ≤ k := by omega
  have hwt_le : wt n (traceRun k u q n z).2 ≤ n := wt_le n _
  have hm_le : m ≤ n - d := by omega
  have hik : i + m ≤ k := by omega
  have hqn : 3 * n + 16 ≤ q := by omega
  have hspec_a := traceRun_spec hk2 hu ha q n hqn
  have hspec_z := traceRun_spec hk2 hu hz q n hqn
  rw [htr] at hspec_a
  have htr1 : (traceRun k u q n z).1 = k + i + m + 2 := by
    have h1 := hspec_z.1
    omega
  let p := k + i + j'
  have hp_mod : p % k = i + j' := by
    have : p = i + j' + 1 * k := by omega
    rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hp_ge : 2 * r ≤ p := by omega
  have hr1 : r = (r - 1) + 1 := by omega
  have hn4 : n + 4 = r - 1 := by omega
  rw [← hp_mod, ← lineStep_eq_rowState hk2 hu ha r p hp_ge,
      ← lineStep_eq_rowState hk2 hu hz r p hp_ge, hr1,
      lineStep_succ k u _ (r - 1) p, lineStep_succ k u _ (r - 1) p]
  let trA := fun t => if t < q then (rot k 1 a ^^^ u).testBit (t % k) else false
  let trZ := fun t => if t < q then (rot k 1 z ^^^ u).testBit (t % k) else false
  have htr_agree : ∀ t, pos0 < t → trA t = trZ t := by
    intro t ht
    simp only [trA, trZ]
    by_cases htq : t < q
    · simp only [htq, ↓reduceIte]; exact hagree t ht htq
    · simp only [htq, ↓reduceIte]
  have hprev : ∀ d', p - 1 ≤ d' → d' ≤ p + 3 →
      lineStep k u (fun t => (rot k 1 a ^^^ u).testBit (t % k)) (r - 1) d' =
      lineStep k u (fun t => (rot k 1 z ^^^ u).testBit (t % k)) (r - 1) d' := by
    intro d' hd1 hd2
    have ha' := hspec_a.2.2 d' (by omega) (by rw [htr1]; omega)
    have hz' := hspec_z.2.2 d' (by omega) (by rw [htr1]; omega)
    rw [hn4] at ha' hz'
    rw [ha', hz']
    exact lineStep_agree_right k u trA trZ pos0 htr_agree (r - 1) d' (by omega)
  have h0 := hprev (p - 1) (by omega) (by omega)
  have h1 := hprev p (by omega) (by omega)
  have h2 := hprev (p + 1) (by omega) (by omega)
  have h3 := hprev (p + 2) (by omega) (by omega)
  have h4 := hprev (p + 3) (by omega) (by omega)
  have hinj : p + 1 - 2 * (r - 1) = pos0 := by omega
  rw [h0, h1, h2, h3, h4, hinj, xor_cancel_right, xor_cancel_left, xor_cancel_right]
  exact startBit_xor_eq hk2 ha hz (by omega)

def leavesAux (d : Nat) : Nat → Nat → Nat → Nat → List (Nat × Nat × Nat)
  | 0, a, s, code => [(a, code, s - d)]
  | rem + 1, a, s, code =>
    if s + (rem + 1) ≤ d then
      [(a, code, 0)]
    else
      leavesAux d rem (a + 1) s code ++
      leavesAux d rem (a + 1) (s + 1) (code ||| (1 <<< a))

def leaves (n d : Nat) : List (Nat × Nat × Nat) :=
  leavesAux d n 0 0 0

def binomCharge (k n d rem s : Nat) : Nat :=
  ((List.range (rem + 1)).map (fun e => Nat.choose rem e * 2 ^ (k - n - (s + e - d)))).sum

lemma sum_choose_range (m : Nat) :
    ((List.range (m + 1)).map (fun e => Nat.choose m e)).sum = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons]
    simp only [Function.comp_def, Nat.choose_zero_right]
    have hsplit : ∀ l : List Nat,
        (l.map (fun e => Nat.choose (m + 1) (e + 1))).sum =
        (l.map (fun e => Nat.choose m e)).sum + (l.map (fun e => Nat.choose m (e + 1))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ihx =>
        simp only [List.map_cons, List.sum_cons, ihx]
        rw [Nat.choose_succ_succ, Nat.succ_eq_add_one]
        omega
    rw [hsplit (List.range (m + 1)), ih]
    have hshift : 1 + ((List.range (m + 1)).map (fun e => Nat.choose m (e + 1))).sum =
        ((List.range (m + 1)).map (fun e => Nat.choose m e)).sum := by
      conv_rhs => rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def, Nat.choose_zero_right]
      conv_lhs => rw [List.range_succ]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self m), Nat.add_zero]
    rw [Nat.pow_succ]
    omega

lemma sum_map_mul_right (l : List Nat) (f : Nat → Nat) (c : Nat) :
    (l.map (fun e => f e * c)).sum = (l.map f).sum * c := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_mul]

lemma binomCharge_succ (k n d rem s : Nat) :
    binomCharge k n d (rem + 1) s =
      binomCharge k n d rem s + binomCharge k n d rem (s + 1) := by
  unfold binomCharge
  let g : Nat → Nat := fun x => 2 ^ (k - n - (x - d))
  change ((List.range (rem + 2)).map (fun e => Nat.choose (rem + 1) e * g (s + e))).sum =
    ((List.range (rem + 1)).map (fun e => Nat.choose rem e * g (s + e))).sum +
    ((List.range (rem + 1)).map (fun e => Nat.choose rem e * g (s + 1 + e))).sum
  conv_lhs => rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def,
    Nat.choose_zero_right, Nat.add_zero, Nat.one_mul]
  have hsplit : ∀ l : List Nat,
      (l.map (fun e => Nat.choose (rem + 1) (e + 1) * g (s + (e + 1)))).sum =
      (l.map (fun e => Nat.choose rem e * g (s + 1 + e))).sum +
      (l.map (fun e => Nat.choose rem (e + 1) * g (s + 1 + e))).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [Nat.choose_succ_succ, show s + (x + 1) = s + 1 + x by omega, Nat.add_mul]
      simp only [Nat.succ_eq_add_one]
      omega
  rw [hsplit (List.range (rem + 1))]
  have hrhs : ((List.range (rem + 1)).map (fun e => Nat.choose rem e * g (s + e))).sum =
      g s + ((List.range (rem + 1)).map (fun e => Nat.choose rem (e + 1) * g (s + 1 + e))).sum := by
    conv_lhs => rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, Function.comp_def,
      Nat.choose_zero_right, Nat.add_zero, Nat.one_mul]
    conv_rhs => rw [List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self rem), Nat.zero_mul, Nat.add_zero]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro x _
    rw [show s + (x + 1) = s + 1 + x by omega]
  rw [hrhs]
  omega

lemma leavesAux_charge (k n d : Nat) (hnk : n ≤ k) :
    ∀ rem a s code, a + rem = n →
      ((leavesAux d rem a s code).map (fun leaf => 2 ^ (k - (leaf.1 + leaf.2.2)))).sum =
        binomCharge k n d rem s := by
  intro rem
  induction rem with
  | zero =>
    intro a s code ha
    have han : a = n := by omega
    subst han
    simp [leavesAux, binomCharge, Nat.sub_add_eq]
  | succ rem ih =>
    intro a s code ha
    unfold leavesAux
    by_cases hstop : s + (rem + 1) ≤ d
    · simp only [hstop, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.add_zero]
      unfold binomCharge
      have hcongr : (List.range (rem + 2)).map (fun e => Nat.choose (rem + 1) e * 2 ^ (k - n - (s + e - d))) =
          (List.range (rem + 2)).map (fun e => Nat.choose (rem + 1) e * 2 ^ (k - n)) := by
        apply List.map_congr_left
        intro e he
        have helt : e < rem + 2 := List.mem_range.mp he
        have hzero : s + e - d = 0 := by omega
        rw [hzero, Nat.sub_zero]
      rw [hcongr, sum_map_mul_right, sum_choose_range, ← Nat.pow_add]
      congr 1
      omega
    · simp only [hstop, ↓reduceIte, List.map_append, List.sum_append]
      rw [ih (a + 1) s code (by omega), ih (a + 1) (s + 1) _ (by omega), binomCharge_succ]

def GoodLeaf (n d : Nat) (leaf : Nat × Nat × Nat) : Prop :=
  leaf.1 ≤ n ∧
  leaf.2.1 < 2 ^ leaf.1 ∧
  (∀ idx < leaf.1, d < wt idx leaf.2.1 + (n - idx)) ∧
  leaf.2.2 = wt leaf.1 leaf.2.1 - d ∧
  (0 < leaf.2.2 → leaf.1 = n)

lemma leavesAux_good (n d : Nat) :
    ∀ rem a s code, a + rem = n → code < 2 ^ a → s = wt a code →
      (∀ idx < a, d < wt idx code + (n - idx)) →
      ∀ leaf ∈ leavesAux d rem a s code, GoodLeaf n d leaf := by
  intro rem
  induction rem with
  | zero =>
    intro a s code ha hlt hs hreach leaf hmem
    simp only [leavesAux, List.mem_singleton] at hmem
    subst hmem
    simp only [GoodLeaf]
    refine ⟨by omega, hlt, hreach, by rw [← hs], fun _ => by omega⟩
  | succ rem ih =>
    intro a s code ha hlt hs hreach leaf hmem
    unfold leavesAux at hmem
    by_cases hstop : s + (rem + 1) ≤ d
    · simp only [hstop, ↓reduceIte, List.mem_singleton] at hmem
      subst hmem
      simp only [GoodLeaf]
      refine ⟨by omega, hlt, hreach, by rw [← hs]; omega, fun h => by omega⟩
    · simp only [hstop, ↓reduceIte, List.mem_append] at hmem
      have hhi : ∀ j, a ≤ j → code.testBit j = false := fun j hj =>
        Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hj))
      rcases hmem with hL | hR
      · apply ih (a + 1) s code (by omega) (hlt.trans (Nat.pow_lt_pow_right (by decide) (by omega)))
        · rw [wt_succ, hhi a (le_refl a)]; simp [hs]
        · intro idx hidx
          by_cases hlt' : idx < a
          · exact hreach idx hlt'
          · have heq : idx = a := by omega
            subst heq; omega
        · exact hL
      · set code1 := code ||| (1 <<< a)
        have hlt1 : code1 < 2 ^ (a + 1) := by
          have : code1 = code ||| ((true : Bool).toNat <<< a) := rfl
          rw [this]
          exact putBit_lt (hlt.trans (Nat.pow_lt_pow_right (by decide) (by omega))) (Nat.lt_succ_self a)
        have hbits1 : ∀ j < a, code1.testBit j = code.testBit j := fun j hj =>
          testBit_putBit_ne (b := true) (by omega)
        have hwt1 : wt (a + 1) code1 = s + 1 := by
          rw [wt_succ, wt_congr hbits1, ← hs]
          have hb : code1.testBit a = true := testBit_putBit_eq (b := true) (hhi a (le_refl a))
          rw [hb]; rfl
        apply ih (a + 1) (s + 1) code1 (by omega) hlt1 hwt1.symm
        · intro idx hidx
          have hwt_eq : wt idx code1 = wt idx code :=
            wt_congr (fun j hj => hbits1 j (by omega))
          rw [hwt_eq]
          by_cases hlt' : idx < a
          · exact hreach idx hlt'
          · have heq : idx = a := by omega
            subst heq; omega
        · exact hR

lemma leavesAux_cover {k u q n d key : Nat} :
    ∀ rem a s code, a + rem = n → code < 2 ^ a → s = wt a code →
      (traceRun k u q a key).2 = code →
      ∃ leaf ∈ leavesAux d rem a s code, (traceRun k u q leaf.1 key).2 = leaf.2.1 := by
  intro rem
  induction rem with
  | zero =>
    intro a s code _ _ _ htr
    exact ⟨(a, code, s - d), by simp [leavesAux], htr⟩
  | succ rem ih =>
    intro a s code ha hlt hs htr
    unfold leavesAux
    by_cases hstop : s + (rem + 1) ≤ d
    · simp only [hstop, ↓reduceIte]
      exact ⟨(a, code, 0), by simp, htr⟩
    · simp only [hstop, ↓reduceIte]
      have hhi : ∀ j, a ≤ j → code.testBit j = false := fun j hj =>
        Nat.testBit_lt_two_pow (hlt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hj))
      have hstep : (traceRun k u q (a + 1) key).2 =
          code ||| ((guardBit k u a ((traceRun k u q a key).1 - 2) key).toNat <<< a) := by
        rw [traceRun_succ]
        dsimp only
        rw [htr]
      cases hbit : guardBit k u a ((traceRun k u q a key).1 - 2) key
      · rw [hbit] at hstep
        simp only [Bool.toNat_false, Nat.zero_shiftLeft, Nat.or_zero] at hstep
        have hwt0 : s = wt (a + 1) code := by
          rw [wt_succ, hhi a (le_refl a)]; simp [hs]
        obtain ⟨leaf, hmem, hl⟩ := ih (a + 1) s code (by omega)
          (hlt.trans (Nat.pow_lt_pow_right (by decide) (by omega))) hwt0 hstep
        exact ⟨leaf, List.mem_append_left _ hmem, hl⟩
      · rw [hbit] at hstep
        set code1 := code ||| (1 <<< a)
        have hlt1 : code1 < 2 ^ (a + 1) := by
          have : code1 = code ||| ((true : Bool).toNat <<< a) := rfl
          rw [this]
          exact putBit_lt (hlt.trans (Nat.pow_lt_pow_right (by decide) (by omega))) (Nat.lt_succ_self a)
        have hbits1 : ∀ j < a, code1.testBit j = code.testBit j := fun j hj =>
          testBit_putBit_ne (b := true) (by omega)
        have hwt1 : s + 1 = wt (a + 1) code1 := by
          rw [wt_succ, wt_congr hbits1, ← hs]
          have hb : code1.testBit a = true := testBit_putBit_eq (b := true) (hhi a (le_refl a))
          rw [hb]; rfl
        obtain ⟨leaf, hmem, hl⟩ := ih (a + 1) (s + 1) code1 (by omega) hlt1 hwt1 hstep
        exact ⟨leaf, List.mem_append_right _ hmem, hl⟩

def bPos (q code idx : Nat) : Nat :=
  q + wt idx code - 3 * (idx + 5)

def gPos (q code idx : Nat) : Nat :=
  bPos q code idx + 5 - 2 * (idx + 5)

def rPos (k q m l : Nat) : Nat :=
  q - k + (m - 1 - l)

def leafPosList (k q : Nat) (leaf : Nat × Nat × Nat) : List Nat :=
  (List.range leaf.1).map (gPos q leaf.2.1) ++
  (List.range leaf.2.2).map (rPos k q leaf.2.2)

def leafPivBits (k q : Nat) (leaf : Nat × Nat × Nat) : List Nat :=
  (leafPosList k q leaf).map (fun p => (p - 1) % k)

def freeBits (k q : Nat) (leaf : Nat × Nat × Nat) : List Nat :=
  (List.range k).filter (fun j => !(decide (j ∈ leafPivBits k q leaf)))

def expandFree : List Nat → List Nat
  | [] => [0]
  | b :: bs =>
    let rest := expandFree bs
    rest ++ rest.map (fun w => w ||| (1 <<< b))

def maskFree (bs : List Nat) (w : Nat) : Nat :=
  bs.foldl (fun acc b => acc ||| ((w.testBit b).toNat <<< b)) 0

lemma expandFree_length (bs : List Nat) :
    (expandFree bs).length = 2 ^ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [expandFree, List.length_append, List.length_map, List.length_cons, ih]
    rw [Nat.pow_succ]
    omega

lemma expandFree_mem_lt {k : Nat} : ∀ (bs : List Nat), (∀ b ∈ bs, b < k) →
    ∀ w ∈ expandFree bs, w < 2 ^ k := by
  intro bs
  induction bs with
  | nil =>
    intro _ w hw
    simp only [expandFree, List.mem_singleton] at hw
    subst hw
    exact Nat.two_pow_pos k
  | cons b bs ih =>
    intro hbs w hw
    simp only [expandFree, List.mem_append, List.mem_map] at hw
    have hb : b < k := hbs b (List.mem_cons_self ..)
    have hbs' : ∀ x ∈ bs, x < k := fun x hx => hbs x (List.mem_cons_of_mem b hx)
    rcases hw with hw | ⟨v, hv, rfl⟩
    · exact ih hbs' w hw
    · have : v ||| (1 <<< b) = v ||| ((true : Bool).toNat <<< b) := rfl
      rw [this]
      exact putBit_lt (ih hbs' v hv) hb

lemma expandFree_outside_false : ∀ (bs : List Nat) (w : Nat),
    w ∈ expandFree bs → ∀ j, j ∉ bs → w.testBit j = false := by
  intro bs
  induction bs with
  | nil =>
    intro w hw j _
    simp only [expandFree, List.mem_singleton] at hw
    subst hw
    simp
  | cons b bs ih =>
    intro w hw j hj
    have hjb : j ≠ b := fun h => hj (h ▸ List.mem_cons_self ..)
    have hjbs : j ∉ bs := fun h => hj (List.mem_cons_of_mem b h)
    simp only [expandFree, List.mem_append, List.mem_map] at hw
    rcases hw with hw | ⟨v, hv, rfl⟩
    · exact ih w hw j hjbs
    · have : v ||| (1 <<< b) = v ||| ((true : Bool).toNat <<< b) := rfl
      rw [this, testBit_putBit_ne hjb]
      exact ih v hv j hjbs

lemma mem_expandFree_of_outside_false {k : Nat} : ∀ (bs : List Nat),
    ∀ w < 2 ^ k, (∀ j, j ∉ bs → w.testBit j = false) → w ∈ expandFree bs := by
  intro bs
  induction bs with
  | nil =>
    intro w _ h0
    have hw : w = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      simpa using h0 j (by simp)
    subst hw
    simp [expandFree]
  | cons b bs ih =>
    intro w hw h0
    let w' := if w.testBit b then w ^^^ (1 <<< b) else w
    have hw'_lt : w' < 2 ^ k := by
      dsimp only [w']
      by_cases hwb : w.testBit b = true
      · simp only [hwb, ↓reduceIte]
        have hb : b < k := by
          by_contra hge
          have hkb : k ≤ b := by omega
          have := Nat.testBit_lt_two_pow (i := b) (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hkb))
          rw [hwb] at this
          exact Bool.noConfusion this
        exact Nat.xor_lt_two_pow hw (by rw [Nat.shiftLeft_eq, Nat.one_mul]; exact Nat.pow_lt_pow_right (by decide) hb)
      · simp [hwb, hw]
    have hw'_bit : ∀ j, w'.testBit j = if j = b then false else w.testBit j := by
      intro j
      dsimp only [w']
      by_cases hwb : w.testBit b = true
      · simp only [hwb, ↓reduceIte, Nat.testBit_xor, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
        by_cases hjb : j = b
        · subst hjb; simp [hwb]
        · simp [hjb, Ne.symm hjb]
      · have hwf : w.testBit b = false := Bool.eq_false_iff.mpr hwb
        simp only [hwf, Bool.false_eq_true, ↓reduceIte]
        by_cases hjb : j = b
        · subst hjb; simp [hwf]
        · simp [hjb]
    have hw'_out : ∀ j, j ∉ bs → w'.testBit j = false := by
      intro j hj
      rw [hw'_bit]
      by_cases hjb : j = b
      · simp [hjb]
      · simp only [hjb, ↓reduceIte]
        exact h0 j (fun hm => by rcases List.mem_cons.mp hm with rfl | hm' <;> contradiction)
    have hmem' : w' ∈ expandFree bs := ih w' hw'_lt hw'_out
    simp only [expandFree, List.mem_append, List.mem_map]
    by_cases hwb : w.testBit b = true
    · right
      refine ⟨w', hmem', ?_⟩
      apply Nat.eq_of_testBit_eq
      intro j
      have : w' ||| (1 <<< b) = w' ||| ((true : Bool).toNat <<< b) := rfl
      rw [this]
      by_cases hjb : j = b
      · subst hjb
        rw [testBit_putBit_eq (by rw [hw'_bit]; simp), hwb]
      · rw [testBit_putBit_ne hjb, hw'_bit]
        simp only [hjb, ↓reduceIte]
    · left
      have heq : w' = w := by simp [w', hwb]
      rwa [← heq]

lemma testBit_maskFree (bs : List Nat) (w j : Nat) :
    (maskFree bs w).testBit j = (decide (j ∈ bs) && w.testBit j) := by
  have hgen : ∀ acc : Nat,
      (bs.foldl (fun a b => a ||| ((w.testBit b).toNat <<< b)) acc).testBit j =
      (acc.testBit j || (decide (j ∈ bs) && w.testBit j)) := by
    induction bs with
    | nil => intro acc; simp
    | cons b bs ih =>
      intro acc
      simp only [List.foldl_cons, ih, List.mem_cons]
      by_cases hjb : j = b
      · subst hjb
        rw [Nat.testBit_or, Nat.testBit_shiftLeft]
        cases w.testBit j <;> simp
      · rw [testBit_putBit_ne hjb]
        simp [hjb]
  simpa [maskFree] using hgen 0

lemma maskFree_lt {k : Nat} (bs : List Nat) (hbs : ∀ b ∈ bs, b < k) (w : Nat) :
    maskFree bs w < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_maskFree]
  have hnot : j ∉ bs := fun hm => by have := hbs j hm; omega
  simp [hnot]

lemma leafPosList_props {k r d : Nat} (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    {leaf : Nat × Nat × Nat} (hgood : GoodLeaf (r - 5) d leaf) :
    let h := (k + 1) / 2
    let i := k - h
    let q := k + i + 3 * r - d
    (leafPosList k q leaf).length = leaf.1 + leaf.2.2 ∧
    (∀ p ∈ leafPosList k q leaf, q - k ≤ p ∧ p < q) ∧
    (leafPosList k q leaf).Pairwise (· > ·) ∧
    (leafPivBits k q leaf).Nodup ∧
    (∀ j ∈ leafPivBits k q leaf, j < k) ∧
    (freeBits k q leaf).length = k - (leaf.1 + leaf.2.2) := by
  intro h i q
  rcases hgood with ⟨hlen, hcode, hreach, hm_eq, hm_pos⟩
  have hwt_le : ∀ a, wt a leaf.2.1 ≤ a := fun a => wt_le a leaf.2.1
  have hlen_pos : (leafPosList k q leaf).length = leaf.1 + leaf.2.2 := by
    simp [leafPosList]
  have hbounds : ∀ p ∈ leafPosList k q leaf, q - k ≤ p ∧ p < q := by
    intro p hp
    simp only [leafPosList, List.mem_append, List.mem_map, List.mem_range] at hp
    rcases hp with ⟨idx, hidx, rfl⟩ | ⟨l, hl, rfl⟩
    · have hri := hreach idx hidx
      have hwi := hwt_le idx
      dsimp only [gPos, bPos]
      omega
    · have hwn := hwt_le leaf.1
      dsimp only [rPos]
      omega
  have hpair : (leafPosList k q leaf).Pairwise (· > ·) := by
    unfold leafPosList
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      simp only [List.length_map, List.length_range] at ha hb
      simp only [List.getElem_map, List.getElem_range]
      have hsub := wt_mono_sub leaf.2.1 (Nat.le_of_lt hab)
      have hwa := hwt_le a
      have hwb := hwt_le b
      have hrb := hreach b hb
      dsimp only [gPos, bPos]
      omega
    · rw [List.pairwise_iff_getElem]
      intro a b ha hb hab
      simp only [List.length_map, List.length_range] at ha hb
      simp only [List.getElem_map, List.getElem_range]
      dsimp only [rPos]
      omega
    · intro x hx y hy
      simp only [List.mem_map, List.mem_range] at hx hy
      rcases hx with ⟨idx, hidx, rfl⟩
      rcases hy with ⟨l, hl, rfl⟩
      have hln : leaf.1 = r - 5 := hm_pos (by omega)
      have hsub := wt_mono_sub leaf.2.1 (Nat.le_of_lt hidx)
      have hwi := hwt_le idx
      have hwn := hwt_le leaf.1
      dsimp only [gPos, bPos, rPos]
      omega
  have hnodup : (leafPivBits k q leaf).Nodup := by
    unfold leafPivBits
    rw [List.nodup_map_iff_inj_on (List.Pairwise.nodup (List.Pairwise.imp (fun {a b} h => ne_of_gt h) hpair))]
    intro x hx y hy hxy
    have hbx := hbounds x hx
    have hby := hbounds y hy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exfalso
      exact mod_ne_of_lt_diff (a := x - 1) (b := y - 1) (by omega) (by omega) hxy
    · exact heq
    · exfalso
      exact mod_ne_of_lt_diff (a := y - 1) (b := x - 1) (by omega) (by omega) hxy.symm
  have hpiv_lt : ∀ j ∈ leafPivBits k q leaf, j < k := by
    intro j hj
    simp only [leafPivBits, List.mem_map] at hj
    rcases hj with ⟨p, _, rfl⟩
    exact Nat.mod_lt _ (by omega)
  have hfree_len : (freeBits k q leaf).length = k - (leaf.1 + leaf.2.2) := by
    set piv := leafPivBits k q leaf
    have hpiv_len : piv.length = leaf.1 + leaf.2.2 := by
      simp [piv, leafPivBits, hlen_pos]
    have hpart : ((List.range k).filter (fun j => decide (j ∈ piv))).length +
        ((List.range k).filter (fun j => !(decide (j ∈ piv)))).length = (List.range k).length := by
      have haux : ∀ (l : List Nat) (p : Nat → Bool),
          (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
        intro l p
        induction l with
        | nil => simp
        | cons x xs ih => cases hp : p x <;> simp [hp] <;> omega
      exact haux (List.range k) (fun j => decide (j ∈ piv))
    have hperm : ((List.range k).filter (fun j => decide (j ∈ piv))).Perm piv := by
      rw [List.perm_iff_count]
      intro x
      have hnd1 : ((List.range k).filter (fun j => decide (j ∈ piv))).Nodup :=
        List.nodup_range.filter _
      by_cases hx : x ∈ piv
      · have hxlt : x < k := hpiv_lt x hx
        rw [List.count_eq_one_of_mem hnd1 (by simp [hx, hxlt]),
            List.count_eq_one_of_mem hnodup hx]
      · rw [List.count_eq_zero_of_not_mem (by simp [hx]),
            List.count_eq_zero_of_not_mem hx]
    have hflen : ((List.range k).filter (fun j => decide (j ∈ piv))).length = piv.length :=
      hperm.length_eq
    rw [List.length_range, hflen, hpiv_len] at hpart
    change ((List.range k).filter (fun j => !(decide (j ∈ piv)))).length = k - (leaf.1 + leaf.2.2)
    omega
  exact ⟨hlen_pos, hbounds, hpair, hnodup, hpiv_lt, hfree_len⟩

def guardRecoverStep (k q code u : Nat) (key idx : Nat) : Nat :=
  let b := bPos q code idx
  let p := gPos q code idx
  let kp := (p - 1) % k
  let g := guardBit k u idx b key
  let bitVal := xor g (code.testBit idx)
  key ||| (bitVal.toNat <<< kp)

def guardRecover (k q s code u key0 : Nat) : Nat :=
  (List.range s).foldl (guardRecoverStep k q code u) key0

def rowRecoverStep (k r i q m u : Nat) (key l : Nat) : Nat :=
  let p := rPos k q m l
  let kp := (p - 1) % k
  let bitVal := (rowState k r key u).testBit (i + (m - 1 - l))
  key ||| (bitVal.toNat <<< kp)

def rowRecoverAux (k r i q m steps u key1 : Nat) : Nat :=
  (List.range steps).foldl (rowRecoverStep k r i q m u) key1

def recoverKey (k r i q : Nat) (leaf : Nat × Nat × Nat) (key0 u : Nat) : Nat :=
  rowRecoverAux k r i q leaf.2.2 leaf.2.2 u (guardRecover k q leaf.1 leaf.2.1 u key0)

lemma guardRecover_zero (k q code u key0 : Nat) :
    guardRecover k q 0 code u key0 = key0 := rfl

lemma guardRecover_succ (k q s code u key0 : Nat) :
    guardRecover k q (s + 1) code u key0 =
      guardRecoverStep k q code u (guardRecover k q s code u key0) s := by
  unfold guardRecover
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma rowRecoverAux_zero (k r i q m u key1 : Nat) :
    rowRecoverAux k r i q m 0 u key1 = key1 := rfl

lemma rowRecoverAux_succ (k r i q m steps u key1 : Nat) :
    rowRecoverAux k r i q m (steps + 1) u key1 =
      rowRecoverStep k r i q m u (rowRecoverAux k r i q m steps u key1) steps := by
  unfold rowRecoverAux
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma list_getElem_leafPivBits_left (k q : Nat) (leaf : Nat × Nat × Nat)
    {s : Nat} (hs : s < leaf.1) :
    (leafPivBits k q leaf)[s]'(by simp [leafPivBits, leafPosList]; omega) =
      (gPos q leaf.2.1 s - 1) % k := by
  simp only [leafPivBits, leafPosList, List.map_append, List.map_map]
  rw [List.getElem_append_left (by simp; omega)]
  simp

lemma list_getElem_leafPivBits_right (k q : Nat) (leaf : Nat × Nat × Nat)
    {l : Nat} (hl : l < leaf.2.2) :
    (leafPivBits k q leaf)[leaf.1 + l]'(by simp [leafPivBits, leafPosList]; omega) =
      (rPos k q leaf.2.2 l - 1) % k := by
  simp only [leafPivBits, leafPosList, List.map_append, List.map_map]
  rw [List.getElem_append_right (by simp)]
  simp

lemma guardRecover_lt_and_zero {k r d : Nat} (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    {leaf : Nat × Nat × Nat} (hgood : GoodLeaf (r - 5) d leaf)
    {key0 u : Nat} (hk0 : key0 < 2 ^ k)
    (hzero : ∀ j ∈ leafPivBits k (k + (k - (k + 1) / 2) + 3 * r - d) leaf, key0.testBit j = false) :
    let q := k + (k - (k + 1) / 2) + 3 * r - d
    ∀ s ≤ leaf.1,
      guardRecover k q s leaf.2.1 u key0 < 2 ^ k ∧
      (∀ j ∈ (leafPivBits k q leaf).drop s, (guardRecover k q s leaf.2.1 u key0).testBit j = false) := by
  intro q
  have hk0pos : 0 < k := by omega
  have hprops := leafPosList_props hr hdn hk hgood
  have hnodup : (leafPivBits k q leaf).Nodup := hprops.2.2.2.1
  intro s
  induction s with
  | zero =>
    intro _
    exact ⟨hk0, hzero⟩
  | succ s ih =>
    intro hs
    rcases ih (by omega) with ⟨hlt, hz⟩
    rw [guardRecover_succ]
    dsimp only [guardRecoverStep]
    have hkp_lt : (gPos q leaf.2.1 s - 1) % k < k := Nat.mod_lt _ hk0pos
    refine ⟨putBit_lt hlt hkp_lt, ?_⟩
    intro j hj
    have hmem_drop : j ∈ (leafPivBits k q leaf).drop s := by
      have hsub := List.drop_subset_drop_left (l := leafPivBits k q leaf) (Nat.le_succ s)
      exact hsub hj
    have hne : j ≠ (gPos q leaf.2.1 s - 1) % k := by
      intro heq
      subst heq
      have hlen_pb : s < (leafPivBits k q leaf).length := by
        simp [leafPivBits, leafPosList]; omega
      have hget : (leafPivBits k q leaf)[s]'hlen_pb = (gPos q leaf.2.1 s - 1) % k :=
        list_getElem_leafPivBits_left k q leaf (by omega)
      rw [List.mem_iff_getElem] at hj
      rcases hj with ⟨idx, hidx, hval⟩
      rw [List.getElem_drop] at hval
      have hidx_lt : s + 1 + idx < (leafPivBits k q leaf).length := by
        simp at hidx; omega
      have hsame := (List.nodup_iff_injective_getElem.mp hnodup) (a₁ := ⟨s, hlen_pb⟩)
        (a₂ := ⟨s + 1 + idx, hidx_lt⟩) (by simpa [hget] using hval.symm)
      have : s = s + 1 + idx := congrArg Fin.val hsame
      omega
    rw [testBit_putBit_ne hne]
    exact hz j hmem_drop

lemma rowRecoverAux_lt_and_zero {k r d : Nat} (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    {leaf : Nat × Nat × Nat} (hgood : GoodLeaf (r - 5) d leaf)
    {key0 u : Nat} (hk0 : key0 < 2 ^ k)
    (hzero : ∀ j ∈ leafPivBits k (k + (k - (k + 1) / 2) + 3 * r - d) leaf, key0.testBit j = false) :
    let i := k - (k + 1) / 2
    let q := k + i + 3 * r - d
    let key1 := guardRecover k q leaf.1 leaf.2.1 u key0
    ∀ steps ≤ leaf.2.2,
      rowRecoverAux k r i q leaf.2.2 steps u key1 < 2 ^ k ∧
      (∀ j ∈ (leafPivBits k q leaf).drop (leaf.1 + steps),
        (rowRecoverAux k r i q leaf.2.2 steps u key1).testBit j = false) := by
  intro i q key1
  have hk0pos : 0 < k := by omega
  have hprops := leafPosList_props hr hdn hk hgood
  have hnodup : (leafPivBits k q leaf).Nodup := hprops.2.2.2.1
  have hbase := guardRecover_lt_and_zero hr hdn hk hgood (u := u) hk0 hzero leaf.1 (le_refl _)
  intro steps
  induction steps with
  | zero =>
    intro _
    simpa [rowRecoverAux_zero, key1] using hbase
  | succ steps ih =>
    intro hst
    rcases ih (by omega) with ⟨hlt, hz⟩
    rw [rowRecoverAux_succ]
    dsimp only [rowRecoverStep]
    have hkp_lt : (rPos k q leaf.2.2 steps - 1) % k < k := Nat.mod_lt _ hk0pos
    refine ⟨putBit_lt hlt hkp_lt, ?_⟩
    intro j hj
    have hmem_drop : j ∈ (leafPivBits k q leaf).drop (leaf.1 + steps) := by
      have hsub := List.drop_subset_drop_left (l := leafPivBits k q leaf) (show leaf.1 + steps ≤ leaf.1 + (steps + 1) by omega)
      exact hsub hj
    have hne : j ≠ (rPos k q leaf.2.2 steps - 1) % k := by
      intro heq
      subst heq
      have hlen_pb : leaf.1 + steps < (leafPivBits k q leaf).length := by
        simp [leafPivBits, leafPosList]; omega
      have hget : (leafPivBits k q leaf)[leaf.1 + steps]'hlen_pb = (rPos k q leaf.2.2 steps - 1) % k :=
        list_getElem_leafPivBits_right k q leaf (by omega)
      rw [List.mem_iff_getElem] at hj
      rcases hj with ⟨idx, hidx, hval⟩
      rw [List.getElem_drop] at hval
      have hidx_lt : leaf.1 + (steps + 1) + idx < (leafPivBits k q leaf).length := by
        simp at hidx; omega
      have hsame := (List.nodup_iff_injective_getElem.mp hnodup) (a₁ := ⟨leaf.1 + steps, hlen_pb⟩)
        (a₂ := ⟨leaf.1 + (steps + 1) + idx, hidx_lt⟩) (by simpa [hget] using hval.symm)
      have : leaf.1 + steps = leaf.1 + (steps + 1) + idx := congrArg Fin.val hsame
      omega
    rw [testBit_putBit_ne hne]
    exact hz j hmem_drop

lemma traceRun_prefix_bit (k u q : Nat) :
    ∀ a b, b ≤ a → ∀ key j, j < b →
      (traceRun k u q a key).2.testBit j = (traceRun k u q b key).2.testBit j := by
  intro a
  induction a with
  | zero =>
    intro b hb _ j hj
    omega
  | succ a ih =>
    intro b hb key j hj
    by_cases hba : b ≤ a
    · rw [traceRun_succ]
      dsimp only
      rw [testBit_putBit_ne (by omega)]
      exact ih b hba key j hj
    · have : b = a + 1 := by omega
      subst this; rfl

lemma not_mem_drop_of_gt {k q : Nat} {leaf : Nat × Nat × Nat}
    (hbounds : ∀ p ∈ leafPosList k q leaf, q - k ≤ p ∧ p < q)
    (hpair : (leafPosList k q leaf).Pairwise (· > ·))
    (hqk : 2 ≤ q - k) {t : Nat} (ht : t < (leafPosList k q leaf).length)
    {p : Nat} (hp1 : (leafPosList k q leaf)[t]'ht < p) (hp2 : p < q) :
    (p - 1) % k ∉ (leafPivBits k q leaf).drop t := by
  intro hmem
  rw [List.mem_iff_getElem] at hmem
  rcases hmem with ⟨idx, hidx, hval⟩
  rw [List.getElem_drop] at hval
  have hidx_lt : t + idx < (leafPosList k q leaf).length := by
    simp [leafPivBits] at hidx; omega
  have hval' : ((leafPosList k q leaf)[t + idx]'hidx_lt - 1) % k = (p - 1) % k := by
    simpa [leafPivBits] using hval
  set p' := (leafPosList k q leaf)[t + idx]'hidx_lt
  have hp'_le : p' ≤ (leafPosList k q leaf)[t]'ht := by
    by_cases hi0 : idx = 0
    · subst hi0; simp [p']
    · exact Nat.le_of_lt (List.pairwise_iff_getElem.mp hpair t (t + idx) ht hidx_lt (by omega))
  have hbp' := hbounds p' (List.getElem_mem hidx_lt)
  exact mod_ne_of_lt_diff (a := p' - 1) (b := p - 1) (by omega) (by omega) hval'

lemma bPos_ge {k r d s code : Nat} (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    (hs : s < r - 5) :
    2 * (s + 4) + 2 ≤ bPos (k + (k - (k + 1) / 2) + 3 * r - d) code s := by
  dsimp only [bPos]
  omega

lemma recoverKey_exact {k r d : Nat} (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    {leaf : Nat × Nat × Nat} (hgood : GoodLeaf (r - 5) d leaf)
    {u w key0 : Nat} (hu : u < 2 ^ k) (hw : w < 2 ^ k) (hk0 : key0 < 2 ^ k)
    (hpass : rowState k r w u < 2 ^ (k - (k + 1) / 2))
    (htr : (traceRun k u (k + (k - (k + 1) / 2) + 3 * r - d) leaf.1 w).2 = leaf.2.1)
    (hfree : ∀ j < k, j ∉ leafPivBits k (k + (k - (k + 1) / 2) + 3 * r - d) leaf →
      key0.testBit j = w.testBit j)
    (hzero : ∀ j ∈ leafPivBits k (k + (k - (k + 1) / 2) + 3 * r - d) leaf, key0.testBit j = false) :
    recoverKey k r (k - (k + 1) / 2) (k + (k - (k + 1) / 2) + 3 * r - d) leaf key0 u = w := by
  set h := (k + 1) / 2
  set i := k - h
  set q := k + i + 3 * r - d
  set n := r - 5
  have hk2 : 2 ≤ k := by omega
  have hk0pos : 0 < k := by omega
  have hqk : 2 ≤ q - k := by omega
  have hprops := leafPosList_props hr hdn hk hgood
  rcases hgood with ⟨hlen, hcode, hreach, hm_eq, hm_pos⟩
  have hqn : 3 * n + 16 ≤ q := by omega
  have hwt_le : ∀ a, wt a leaf.2.1 ≤ a := fun a => wt_le a leaf.2.1
  have htrace_wt : ∀ a ≤ leaf.1, wt a (traceRun k u q a w).2 = wt a leaf.2.1 := by
    intro a ha
    apply wt_congr
    intro j hj
    rw [← htr]
    exact (traceRun_prefix_bit k u q leaf.1 a ha w j hj).symm
  have htrace_fst : ∀ a ≤ leaf.1, (traceRun k u q a w).1 = q + wt a leaf.2.1 - 3 * (a + 4) - 1 := by
    intro a ha
    have hsp := (traceRun_spec hk2 hu hw q a (by omega)).1
    rw [htrace_wt a ha] at hsp
    exact hsp
  have hguard_inv : ∀ s ≤ leaf.1,
      ∀ j < k, j ∉ (leafPivBits k q leaf).drop s →
        (guardRecover k q s leaf.2.1 u key0).testBit j = w.testBit j := by
    intro s
    induction s with
    | zero =>
      intro _ j hj hnot
      exact hfree j hj hnot
    | succ s ih =>
      intro hs
      have hprev_ag := ih (by omega)
      have hprev_ltz := guardRecover_lt_and_zero hr hdn hk ⟨hlen, hcode, hreach, hm_eq, hm_pos⟩ (u := u) hk0 hzero s (by omega)
      set ks := guardRecover k q s leaf.2.1 u key0
      have hst_lt : s < (leafPosList k q leaf).length := by simp [leafPosList]; omega
      have hget_pos : (leafPosList k q leaf)[s]'hst_lt = gPos q leaf.2.1 s := by
        simp only [leafPosList]
        rw [List.getElem_append_left (by simp; omega)]
        simp
      have hstart_ag : ∀ p, gPos q leaf.2.1 s < p → p < q →
          (rot k 1 ks ^^^ u).testBit (p % k) = (rot k 1 w ^^^ u).testBit (p % k) := by
        intro p hp1 hp2
        have hnot := not_mem_drop_of_gt hprops.2.1 hprops.2.2.1 hqk hst_lt (by rwa [hget_pos]) hp2
        have hbp := hprops.2.1 (gPos q leaf.2.1 s) (by rw [← hget_pos]; exact List.getElem_mem hst_lt)
        exact startBit_eq_of_keyBit hk2 hprev_ltz.1 hw (by omega)
          (hprev_ag ((p - 1) % k) (Nat.mod_lt _ hk0pos) hnot)
      have htr_eq : traceRun k u q s ks = traceRun k u q s w := by
        apply traceRun_agree_above hk2 hu hprev_ltz.1 hw hstart_ag s (by omega)
        intro idx hidx
        have hf := htrace_fst idx (by omega)
        have hsub := wt_mono_sub leaf.2.1 (Nat.le_of_lt hidx)
        have hwi := hwt_le idx
        have hws := hwt_le s
        dsimp only [gPos, bPos]
        omega
      have hb_eq : (traceRun k u q s w).1 - 2 = bPos q leaf.2.1 s := by
        rw [htrace_fst s (by omega)]
        dsimp only [bPos]
        have hws := hwt_le s
        omega
      have hbp := hprops.2.1 (gPos q leaf.2.1 s) (by rw [← hget_pos]; exact List.getElem_mem hst_lt)
      have hb_ge : 2 * (s + 4) + 2 ≤ bPos q leaf.2.1 s := bPos_ge hr hdn hk (by omega)
      have hg_ge : 1 ≤ gPos q leaf.2.1 s := by have := hbp.1; omega
      have hgx := guard_xor_eq hk2 hu hprev_ltz.1 hw (by omega) htr_eq
      rw [hb_eq] at hgx
      have hgx' : xor (guardBit k u s (bPos q leaf.2.1 s) ks) (guardBit k u s (bPos q leaf.2.1 s) w) =
          xor (ks.testBit ((gPos q leaf.2.1 s - 1) % k)) (w.testBit ((gPos q leaf.2.1 s - 1) % k)) :=
        hgx hb_ge hg_ge hbp.2 hstart_ag
      have hgz : guardBit k u s (bPos q leaf.2.1 s) w = leaf.2.1.testBit s := by
        have hbit_eq : leaf.2.1.testBit s = (traceRun k u q (s + 1) w).2.testBit s := by
          rw [← htr]
          exact traceRun_prefix_bit k u q leaf.1 (s + 1) hs w s (Nat.lt_succ_self s)
        rw [hbit_eq, traceRun_succ]
        dsimp only
        rw [hb_eq, testBit_putBit_eq ((traceRun_spec hk2 hu hw q s (by omega)).2.1 s (le_refl s))]
      have hks0 : ks.testBit ((gPos q leaf.2.1 s - 1) % k) = false := by
        apply hprev_ltz.2
        have hlen_pb : s < (leafPivBits k q leaf).length := by simp [leafPivBits, leafPosList]; omega
        have hmem_s : (leafPivBits k q leaf)[s]'hlen_pb ∈ (leafPivBits k q leaf).drop s := by
          rw [List.mem_iff_getElem]
          exact ⟨0, by simp; omega, by simp⟩
        rwa [list_getElem_leafPivBits_left k q leaf (by omega)] at hmem_s
      have hbit_rec : xor (guardBit k u s (bPos q leaf.2.1 s) ks) (leaf.2.1.testBit s) =
          w.testBit ((gPos q leaf.2.1 s - 1) % k) := by
        rw [← hgz, hgx', hks0, Bool.false_xor]
      intro j hj hnot
      rw [guardRecover_succ]
      dsimp only [guardRecoverStep]
      change (ks ||| ((xor (guardBit k u s (bPos q leaf.2.1 s) ks) (leaf.2.1.testBit s)).toNat <<<
        ((gPos q leaf.2.1 s - 1) % k))).testBit j = w.testBit j
      rw [hbit_rec]
      by_cases hje : j = (gPos q leaf.2.1 s - 1) % k
      · subst hje
        exact testBit_putBit_eq hks0
      · rw [testBit_putBit_ne hje]
        apply hprev_ag j hj
        intro hmem
        have hlen_pb : s < (leafPivBits k q leaf).length := by simp [leafPivBits, leafPosList]; omega
        rw [List.drop_eq_getElem_cons hlen_pb, List.mem_cons] at hmem
        rcases hmem with rfl | htail
        · rw [list_getElem_leafPivBits_left k q leaf (by omega)] at hje
          exact hje rfl
        · exact hnot htail
  have hrow_inv : ∀ steps ≤ leaf.2.2,
      ∀ j < k, j ∉ (leafPivBits k q leaf).drop (leaf.1 + steps) →
        (rowRecoverAux k r i q leaf.2.2 steps u (guardRecover k q leaf.1 leaf.2.1 u key0)).testBit j =
          w.testBit j := by
    intro steps
    induction steps with
    | zero =>
      intro _ j hj hnot
      simpa [rowRecoverAux_zero] using hguard_inv leaf.1 (le_refl _) j hj hnot
    | succ steps ih =>
      intro hst
      have hprev_ag := ih (by omega)
      have hprev_ltz := rowRecoverAux_lt_and_zero hr hdn hk ⟨hlen, hcode, hreach, hm_eq, hm_pos⟩ (u := u) hk0 hzero steps (by omega)
      set kl := rowRecoverAux k r i q leaf.2.2 steps u (guardRecover k q leaf.1 leaf.2.1 u key0)
      have hln : leaf.1 = n := hm_pos (by omega)
      have hst_lt : leaf.1 + steps < (leafPosList k q leaf).length := by simp [leafPosList]; omega
      have hget_pos : (leafPosList k q leaf)[leaf.1 + steps]'hst_lt = rPos k q leaf.2.2 steps := by
        simp only [leafPosList]
        rw [List.getElem_append_right (by simp)]
        simp
      have hstart_ag : ∀ p, rPos k q leaf.2.2 steps < p → p < q →
          (rot k 1 kl ^^^ u).testBit (p % k) = (rot k 1 w ^^^ u).testBit (p % k) := by
        intro p hp1 hp2
        have hnot := not_mem_drop_of_gt hprops.2.1 hprops.2.2.1 hqk hst_lt (by rwa [hget_pos]) hp2
        have hbp := hprops.2.1 (rPos k q leaf.2.2 steps) (by rw [← hget_pos]; exact List.getElem_mem hst_lt)
        exact startBit_eq_of_keyBit hk2 hprev_ltz.1 hw (by omega)
          (hprev_ag ((p - 1) % k) (Nat.mod_lt _ hk0pos) hnot)
      have htr_eq : traceRun k u q n kl = traceRun k u q n w := by
        apply traceRun_agree_above hk2 hu hprev_ltz.1 hw hstart_ag n hqn
        intro idx hidx
        have hf := htrace_fst idx (by omega)
        have hsub := wt_mono_sub leaf.2.1 (show idx ≤ leaf.1 by omega)
        have hwi := hwt_le idx
        have hwn := hwt_le leaf.1
        dsimp only [rPos]
        omega
      have hj'_lt : leaf.2.2 - 1 - steps < wt n (traceRun k u q n w).2 - d := by
        have : (traceRun k u q n w).2 = leaf.2.1 := by rw [← hln]; exact htr
        rw [this, ← hln, ← hm_eq]
        omega
      have hrx := row_xor_eq hr hdn hk hu hprev_ltz.1 hw (j' := leaf.2.2 - 1 - steps) hj'_lt htr_eq hstart_ag
      have hw_bit0 : (rowState k r w u).testBit (i + (leaf.2.2 - 1 - steps)) = false :=
        Nat.testBit_lt_two_pow (hpass.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two (by omega)))
      have hkl0 : kl.testBit ((rPos k q leaf.2.2 steps - 1) % k) = false := by
        apply hprev_ltz.2
        have hlen_pb : leaf.1 + steps < (leafPivBits k q leaf).length := by simp [leafPivBits, leafPosList]; omega
        have hmem_s : (leafPivBits k q leaf)[leaf.1 + steps]'hlen_pb ∈ (leafPivBits k q leaf).drop (leaf.1 + steps) := by
          rw [List.mem_iff_getElem]
          exact ⟨0, by simp; omega, by simp⟩
        rwa [list_getElem_leafPivBits_right k q leaf (by omega)] at hmem_s
      have hbit_rec : (rowState k r kl u).testBit (i + (leaf.2.2 - 1 - steps)) =
          w.testBit ((rPos k q leaf.2.2 steps - 1) % k) := by
        rw [hw_bit0, Bool.xor_false] at hrx
        change (rowState k r kl u).testBit (i + (leaf.2.2 - 1 - steps)) =
          xor (kl.testBit ((rPos k q leaf.2.2 steps - 1) % k)) (w.testBit ((rPos k q leaf.2.2 steps - 1) % k)) at hrx
        rw [hkl0, Bool.false_xor] at hrx
        exact hrx
      intro j hj hnot
      rw [rowRecoverAux_succ]
      dsimp only [rowRecoverStep]
      change (kl ||| (((rowState k r kl u).testBit (i + (leaf.2.2 - 1 - steps))).toNat <<<
        ((rPos k q leaf.2.2 steps - 1) % k))).testBit j = w.testBit j
      rw [hbit_rec]
      by_cases hje : j = (rPos k q leaf.2.2 steps - 1) % k
      · subst hje
        exact testBit_putBit_eq hkl0
      · rw [testBit_putBit_ne hje]
        apply hprev_ag j hj
        intro hmem
        have hlen_pb : leaf.1 + steps < (leafPivBits k q leaf).length := by simp [leafPivBits, leafPosList]; omega
        rw [List.drop_eq_getElem_cons hlen_pb, List.mem_cons] at hmem
        rcases hmem with rfl | htail
        · rw [list_getElem_leafPivBits_right k q leaf (by omega)] at hje
          exact hje rfl
        · exact hnot htail
  have hfinal_lt := (rowRecoverAux_lt_and_zero hr hdn hk ⟨hlen, hcode, hreach, hm_eq, hm_pos⟩ (u := u) hk0 hzero leaf.2.2 (le_refl _)).1
  have hdrop_nil : (leafPivBits k q leaf).drop (leaf.1 + leaf.2.2) = [] := by
    rw [List.drop_eq_nil_iff]
    simp [leafPivBits, leafPosList]
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · exact hrow_inv leaf.2.2 (le_refl _) j hj (by rw [hdrop_nil]; simp)
  · have hkj : k ≤ j := by omega
    dsimp only [recoverKey]
    rw [Nat.testBit_lt_two_pow (hfinal_lt.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hkj)),
        Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right Nat.zero_lt_two hkj))]

abbrev BitFn (n : Nat) := (Fin n → Bool) → Bool
abbrev Word (n : Nat) := (Fin n → Bool) → Nat

def Valid (n : Nat) (gs : List Gate) : Prop :=
  FanInTwo ⟨gs, 0⟩ ∧ ReadsBack n ⟨gs, 0⟩

def wireVal {n : Nat} (gs : List Gate) (i : Nat) (x : Fin n → Bool) : Bool :=
  ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).getD i false

def Has (n : Nat) (gs : List Gate) (f : BitFn n) : Prop :=
  ∃ i < n + gs.length, ∀ x, wireVal gs i x = f x

def Ext (n : Nat) (gs ds : List Gate) : Prop :=
  ∀ {f}, Has n gs f → Has n ds f

def Grow (n : Nat) (gs : List Gate) (cost : Nat) (p : List Gate → Prop) : Prop :=
  ∃ ds, Valid n ds ∧ Ext n gs ds ∧ ds.length ≤ gs.length + cost ∧ p ds

def HasWord (n k : Nat) (gs : List Gate) (W : Word n) : Prop :=
  ∀ j : Fin k, Has n gs (fun x => (W x).testBit j.val)

lemma empty_valid (n : Nat) : Valid n [] :=
  ⟨by simp [FanInTwo], by simp [ReadsBack]⟩

lemma input_has {n : Nat} (i : Fin n) : Has n [] (fun x => x i) := by
  refine ⟨i.val, i.isLt, ?_⟩
  intro x
  simp [wireVal, Circuit.wires, List.getD_eq_getElem?_getD, i.isLt]

lemma Grow.pure {n : Nat} {gs : List Gate} (hgs : Valid n gs) {p : List Gate → Prop} (hp : p gs) :
    Grow n gs 0 p :=
  ⟨gs, hgs, fun h => h, by omega, hp⟩

lemma Grow.weaken {n a b : Nat} {gs : List Gate} {p q : List Gate → Prop}
    (h : Grow n gs a p) (hab : a ≤ b) (hpq : ∀ ds, p ds → q ds) : Grow n gs b q := by
  obtain ⟨ds, hv, he, hc, hp⟩ := h
  exact ⟨ds, hv, he, by omega, hpq ds hp⟩

lemma Grow.bind {n a b : Nat} {gs : List Gate} {p q : List Gate → Prop}
    (h : Grow n gs a p) (f : ∀ ds, Valid n ds → Ext n gs ds → p ds → Grow n ds b q) :
    Grow n gs (a + b) q := by
  obtain ⟨ds, hv, he, hc, hp⟩ := h
  obtain ⟨es, hv', he', hc', hq⟩ := f ds hv he hp
  exact ⟨es, hv', fun x => he' (he x), by omega, hq⟩

lemma wireLen (gs : List Gate) (x : List Bool) :
    ((⟨gs, 0⟩ : Circuit).wires x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simp [Circuit.wires, List.foldl_append] at ih ⊢
    omega

lemma emitGate {n : Nat} {gs : List Gate} (hgs : Valid n gs) (g : Gate)
    (ok : g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (back : ∀ i ∈ g.inputs, i < n + gs.length) :
    Grow n gs 1 (fun ds => Has n ds (fun x => g.op.eval (g.inputs.map fun i => wireVal gs i x))) := by
  let ds := gs ++ [g]
  have hvalid : Valid n ds := by
    refine ⟨?_, ?_⟩
    · intro g' h
      change g' ∈ gs ++ [g] at h
      rcases List.mem_append.mp h with h | h
      · exact hgs.1 g' h
      · simpa using (show g' = g from List.mem_singleton.mp h) ▸ ok
    · intro j hj w hw
      change j < (gs ++ [g]).length at hj
      change w ∈ ((gs ++ [g]).getD j _).inputs at hw
      by_cases h : j < gs.length
      · rw [List.getD_append _ _ _ _ h] at hw
        exact hgs.2 j h w hw
      · have he : j = gs.length := by simp at hj; omega
        subst j
        simp at hw
        exact back w hw
  have hv (x : Fin n → Bool) :
      ((⟨ds, 0⟩ : Circuit).wires (List.ofFn x)) =
        ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)) ++
        [g.op.eval (g.inputs.map fun i => wireVal gs i x)] := by
    simp [ds, wireVal, Circuit.wires, List.foldl_append]
  have hl (x : Fin n → Bool) :
      ((⟨gs, 0⟩ : Circuit).wires (List.ofFn x)).length = n + gs.length := by
    simp [wireLen]
  refine ⟨ds, hvalid, ?_, by simp [ds], n + gs.length, by simp [ds], ?_⟩
  · intro f hf
    obtain ⟨i, hi, he⟩ := hf
    refine ⟨i, by simp [ds]; omega, ?_⟩
    intro x
    unfold wireVal
    rw [hv, List.getD_append _ _ _ _ (by rw [hl]; exact hi)]
    exact he x
  · intro x
    unfold wireVal
    rw [hv, ← hl x]
    simp [wireVal, List.getD_eq_getElem?_getD]

lemma emitConst {n : Nat} {gs : List Gate} (hgs : Valid n gs) (b : Bool) :
    Grow n gs 1 (fun ds => Has n ds (fun _ => b)) := by
  cases b with
  | false => simpa [GateOp.eval] using emitGate hgs ⟨.or, []⟩ (by simp) (by simp)
  | true => simpa [GateOp.eval] using emitGate hgs ⟨.and, []⟩ (by simp) (by simp)

lemma emitNot {n : Nat} {gs : List Gate} (hgs : Valid n gs) {f : BitFn n} (a : Has n gs f) :
    Grow n gs 1 (fun ds => Has n ds (fun x => !(f x))) := by
  obtain ⟨i, hi, he⟩ := a
  simpa [GateOp.eval, he] using emitGate hgs ⟨.not, [i]⟩ (by simp) (by simpa using hi)

lemma emitAnd {n : Nat} {gs : List Gate} (hgs : Valid n gs) {f g : BitFn n}
    (a : Has n gs f) (b : Has n gs g) :
    Grow n gs 1 (fun ds => Has n ds (fun x => f x && g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using emitGate hgs ⟨.and, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma emitOr {n : Nat} {gs : List Gate} (hgs : Valid n gs) {f g : BitFn n}
    (a : Has n gs f) (b : Has n gs g) :
    Grow n gs 1 (fun ds => Has n ds (fun x => f x || g x)) := by
  obtain ⟨i, hi, he⟩ := a
  obtain ⟨j, hj, hf⟩ := b
  simpa [GateOp.eval, he, hf] using emitGate hgs ⟨.or, [i, j]⟩ (by simp) (by simp [hi, hj])

lemma emitXor {n : Nat} {gs : List Gate} (hgs : Valid n gs) {f g : BitFn n}
    (a : Has n gs f) (b : Has n gs g) :
    Grow n gs 4 (fun ds => Has n ds (fun x => xor (f x) (g x))) := by
  apply (emitAnd hgs a b).bind (b := 3)
  intro d1 v1 e1 hab
  apply (emitNot v1 hab).bind (b := 2)
  intro d2 v2 e2 hn
  apply (emitOr v2 (e2 (e1 a)) (e2 (e1 b))).bind (b := 1)
  intro d3 v3 e3 hor
  apply (emitAnd v3 hor (e3 hn)).weaken (le_refl _)
  intro d4 h
  have eq (x) : ((f x || g x) && !(f x && g x)) = xor (f x) (g x) := by
    cases f x <;> cases g x <;> decide
  simpa only [eq] using h

lemma emitXorConst {n : Nat} {gs : List Gate} (hgs : Valid n gs) {f : BitFn n}
    (a : Has n gs f) (b : Bool) :
    Grow n gs 1 (fun ds => Has n ds (fun x => xor (f x) b)) := by
  cases b with
  | false =>
    have h := Grow.pure hgs (p := fun ds => Has n ds f) a
    simpa using h.weaken (b := 1) (by decide) (fun _ t => t)
  | true => simpa using emitNot hgs a

lemma emitChiBit {n : Nat} {gs : List Gate} (hgs : Valid n gs) {a b c : BitFn n}
    (ha : Has n gs a) (hb : Has n gs b) (hc : Has n gs c) :
    Grow n gs 6 (fun ds => Has n ds (fun x => xor (a x) (!(b x) && c x))) := by
  apply (emitNot hgs hb).bind (b := 5)
  intro d1 v1 e1 hnot
  apply (emitAnd v1 hnot (e1 hc)).bind (b := 4)
  intro d2 v2 e2 hand
  exact emitXor v2 (e2 (e1 ha)) hand

lemma collectList {n : Nat} {α : Type} {gs : List Gate} (hgs : Valid n gs) (l : List α)
    (f : α → BitFn n) (cost : Nat)
    (emit : ∀ ds, Valid n ds → Ext n gs ds → ∀ i ∈ l, Grow n ds cost (fun es => Has n es (f i))) :
    Grow n gs (l.length * cost) (fun ds => ∀ i ∈ l, Has n ds (f i)) := by
  induction l with
  | nil => simpa using (Grow.pure hgs (p := fun ds => ∀ i ∈ ([] : List α), Has n ds (f i)) (by simp))
  | cons a l ih =>
    have t := ih (fun ds hv e i hi => emit ds hv e i (by simp [hi]))
    have out := t.bind (b := cost) (q := fun es => ∀ i ∈ a :: l, Has n es (f i)) (by
      intro ds hv e haveL
      obtain ⟨es, hv', e', c', ha⟩ := emit ds hv e a (by simp)
      refine ⟨es, hv', e', c', ?_⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | h
      · exact ha
      · exact e' (haveL i h))
    simpa [Nat.succ_mul] using out

lemma collectFin {n m : Nat} {gs : List Gate} (hgs : Valid n gs) (f : Fin m → BitFn n) (cost : Nat)
    (emit : ∀ ds, Valid n ds → Ext n gs ds → ∀ i, Grow n ds cost (fun es => Has n es (f i))) :
    Grow n gs (m * cost) (fun ds => ∀ i, Has n ds (f i)) := by
  simpa using collectList hgs (List.finRange m) f cost (fun ds hv e i _ => emit ds hv e i)

lemma anySlots {n : Nat} {α : Type} {gs : List Gate} (hgs : Valid n gs) (l : List α)
    (f : α → BitFn n) (cost : Nat)
    (emit : ∀ ds, Valid n ds → Ext n gs ds → ∀ i ∈ l, Grow n ds cost (fun es => Has n es (f i))) :
    Grow n gs (1 + l.length * (cost + 1)) (fun ds => Has n ds (fun x => l.any (fun i => f i x))) := by
  induction l with
  | nil =>
    simpa using emitConst hgs false
  | cons a l ih =>
    have t := ih (fun ds hv e i hi => emit ds hv e i (by simp [hi]))
    have out := t.bind (b := cost + 1)
      (q := fun es => Has n es (fun x => (a :: l).any (fun i => f i x))) (by
      intro ds hv e acc
      apply (emit ds hv e a (by simp)).bind (b := 1)
      intro es hv' e' ha
      simpa using emitOr hv' ha (e' acc))
    simpa [Nat.succ_mul, Nat.add_assoc] using out

lemma anyBits {n : Nat} {α : Type} {gs : List Gate} (hgs : Valid n gs) (l : List α)
    (f : α → BitFn n) (h : ∀ i ∈ l, Has n gs (f i)) :
    Grow n gs (1 + l.length) (fun ds => Has n ds (fun x => l.any (fun i => f i x))) := by
  simpa using anySlots hgs l f 0 (fun ds hv e i hi => Grow.pure hv (e (h i hi)))

lemma wordLift {n k : Nat} {gs ds : List Gate} {W : Word n} (e : Ext n gs ds)
    (h : HasWord n k gs W) : HasWord n k ds W :=
  fun j => e (h j)

lemma wordRotated {n k s : Nat} {gs : List Gate} {W : Word n} (hk : 0 < k)
    (h : HasWord n k gs W) (hw : ∀ x, W x < 2 ^ k) :
    HasWord n k gs (fun x => rot k s (W x)) := by
  intro j
  have heq : (fun x => (rot k s (W x)).testBit j.val) =
      fun x => (W x).testBit ((j.val + k - s % k) % k) := by
    funext x
    exact testBit_rot (hw x) j.isLt
  rw [heq]
  exact h ⟨(j.val + k - s % k) % k, Nat.mod_lt _ hk⟩

lemma emitXorWords {n k : Nat} {gs : List Gate} (hgs : Valid n gs) {W V : Word n}
    (hW : HasWord n k gs W) (hV : HasWord n k gs V) :
    Grow n gs (k * 4) (fun ds => HasWord n k ds (fun x => W x ^^^ V x)) := by
  apply collectFin hgs (fun j x => (W x ^^^ V x).testBit j.val) 4
  intro ds hv e j
  simpa only [Nat.testBit_xor] using emitXor hv (e (hW j)) (e (hV j))

lemma emitStepWord {n k : Nat} {gs : List Gate} (hgs : Valid n gs) (hk : 0 < k) {W : Word n}
    (hW : HasWord n k gs W) :
    Grow n gs (k * 6) (fun ds => HasWord n k ds (fun x => step k (W x))) := by
  apply collectFin hgs (fun j x => (step k (W x)).testBit j.val) 6
  intro ds hv e j
  have heq : (fun x => (step k (W x)).testBit j.val) =
      fun x => xor ((W x).testBit j.val)
        (!((W x).testBit ((j.val + 1) % k)) && (W x).testBit ((j.val + 2) % k)) := by
    funext x
    exact testBit_step j.isLt
  rw [heq]
  exact emitChiBit hv (e (hW j)) (e (hW ⟨(j.val + 1) % k, Nat.mod_lt _ hk⟩))
    (e (hW ⟨(j.val + 2) % k, Nat.mod_lt _ hk⟩))

lemma emitXorConstWord {n k : Nat} {gs : List Gate} (hgs : Valid n gs) {W : Word n}
    (hW : HasWord n k gs W) (c : Nat) :
    Grow n gs (k * 1) (fun ds => HasWord n k ds (fun x => W x ^^^ c)) := by
  apply collectFin hgs (fun j x => (W x ^^^ c).testBit j.val) 1
  intro ds hv e j
  simpa only [Nat.testBit_xor] using emitXorConst hv (e (hW j)) (c.testBit j.val)

lemma emitRound {n k : Nat} {gs : List Gate} (hgs : Valid n gs) (hk : 0 < k) (d sh c : Nat)
    {W V : Word n} (hW : HasWord n k gs W) (hV : HasWord n k gs V)
    (bW : ∀ x, W x < 2 ^ k) (bV : ∀ x, V x < 2 ^ k) :
    Grow n gs (k * 19) (fun ds => HasWord n k ds (fun x =>
      step k (V x ^^^ rot k d (V x) ^^^ rot k (k - d) (V x)) ^^^ rot k sh (W x) ^^^ c)) := by
  have ha := wordRotated (s := d) hk hV bV
  have hb := wordRotated (s := k - d) hk hV bV
  have hkey := wordRotated (s := sh) hk hW bW
  obtain ⟨d1, v1, e1, c1, t1⟩ := emitXorWords hgs hV ha
  obtain ⟨d2, v2, e2, c2, t2⟩ := emitXorWords v1 t1 (wordLift e1 hb)
  obtain ⟨d3, v3, e3, c3, t3⟩ := emitStepWord v2 hk t2
  obtain ⟨d4, v4, e4, c4, t4⟩ := emitXorWords v3 t3 (wordLift e3 (wordLift e2 (wordLift e1 hkey)))
  obtain ⟨d5, v5, e5, c5, t5⟩ := emitXorConstWord v4 t4 c
  exact ⟨d5, v5, fun x => e5 (e4 (e3 (e2 (e1 x)))), by omega, t5⟩

lemma emitRowState {n k : Nat} {gs : List Gate} (hgs : Valid n gs) (hk : 0 < k) (t : Nat)
    {W U : Word n} (hW : HasWord n k gs W) (hU : HasWord n k gs U)
    (bW : ∀ x, W x < 2 ^ k) (bU : ∀ x, U x < 2 ^ k) :
    Grow n gs (4 * k + 19 * k * t) (fun ds => HasWord n k ds (fun x => rowState k t (W x) (U x))) := by
  induction t with
  | zero =>
    simpa [rowState_zero, Nat.mul_comm] using emitXorWords hgs (wordRotated (s := 1) hk hW bW) hU
  | succ t ih =>
    obtain ⟨d1, v1, e1, c1, p1⟩ := ih
    obtain ⟨d2, v2, e2, c2, p2⟩ := emitRound v1 hk 1 (2 * t) (cval k (t + 1)) (wordLift e1 hW) p1
      bW (fun x => rowState_lt (bU x) t (W x))
    refine ⟨d2, v2, fun x => e2 (e1 x), ?_, ?_⟩
    · rw [Nat.mul_succ]; omega
    · simpa only [rowState_succ, mix] using p2

lemma emitColState {n k : Nat} {gs : List Gate} (hgs : Valid n gs) (hk : 0 < k) (r t : Nat)
    {W V : Word n} (hW : HasWord n k gs W) (hV : HasWord n k gs V)
    (bW : ∀ x, W x < 2 ^ k) (bV : ∀ x, V x < 2 ^ k) :
    Grow n gs (4 * k + 19 * k * t) (fun ds => HasWord n k ds (fun x => colState k r t (W x) (V x))) := by
  induction t with
  | zero =>
    simpa [colState_zero, Nat.mul_comm] using emitXorWords hgs (wordRotated (s := 3) hk hW bW) hV
  | succ t ih =>
    obtain ⟨d1, v1, e1, c1, p1⟩ := ih
    obtain ⟨d2, v2, e2, c2, p2⟩ := emitRound v1 hk 2 (3 * (t + 1) + 1) (cval k (r + (t + 1)))
      (wordLift e1 hW) p1 bW (fun x => colState_lt (bV x) r t (W x))
    refine ⟨d2, v2, fun x => e2 (e1 x), ?_, ?_⟩
    · rw [Nat.mul_succ]; omega
    · simpa only [colState_succ] using p2

def highIndices (k low : Nat) : List Nat :=
  (List.range k).filter (fun i => decide (low ≤ i))

lemma highEq {k low v : Nat} (bv : v < 2 ^ k) :
    (!(highIndices k low).any (fun i => v.testBit i)) = decide (v < 2 ^ low) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_cases small : i < k
    · simpa using h i (by simp [highIndices, small, hi])
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le bv (Nat.pow_le_pow_right (by decide) (by omega)))
  · intro h i hi
    have hlo : low ≤ i := by simpa [highIndices] using (List.mem_filter.mp hi).2
    simp [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hlo))]

lemma emitTestHigh {n k : Nat} {gs : List Gate} (hgs : Valid n gs) (low : Nat)
    {W : Word n} (hW : HasWord n k gs W) (bW : ∀ x, W x < 2 ^ k) :
    Grow n gs (k + 2) (fun ds => Has n ds (fun x => decide (W x < 2 ^ low))) := by
  have emit (i : Nat) (hi : i ∈ highIndices k low) : Has n gs (fun x => (W x).testBit i) := by
    have ilt : i < k := List.mem_range.mp (List.mem_filter.mp hi).1
    exact hW ⟨i, ilt⟩
  obtain ⟨d1, v1, e1, c1, hd1⟩ := anyBits hgs (highIndices k low) (fun i x => (W x).testBit i) emit
  obtain ⟨d2, v2, e2, c2, hd2⟩ := emitNot v1 hd1
  have hlen : (highIndices k low).length ≤ k := by
    simpa [highIndices] using List.length_filter_le (fun i : Nat => decide (low ≤ i)) (List.range k)
  refine ⟨d2, v2, fun x => e2 (e1 x), by omega, ?_⟩
  simpa only [highEq (bW _)] using hd2

lemma emitVerify {n k : Nat} {gs : List Gate} (hgs : Valid n gs) (hk : 0 < k) (r low : Nat)
    {W U V : Word n} (hW : HasWord n k gs W) (hU : HasWord n k gs U) (hV : HasWord n k gs V)
    (bW : ∀ x, W x < 2 ^ k) (bU : ∀ x, U x < 2 ^ k) (bV : ∀ x, V x < 2 ^ k) :
    Grow n gs (38 * k * r + 10 * k + 5) (fun ds => Has n ds (fun x =>
      decide (rowState k r (W x) (U x) < 2 ^ low) && decide (colState k r r (W x) (V x) < 2 ^ low))) := by
  obtain ⟨d1, v1, e1, c1, a1⟩ := emitRowState hgs hk r hW hU bW bU
  obtain ⟨d2, v2, e2, c2, u2⟩ := emitTestHigh v1 low a1 (fun x => rowState_lt (bU x) r (W x))
  obtain ⟨d3, v3, e3, c3, b3⟩ := emitColState v2 hk r r (wordLift e2 (wordLift e1 hW))
    (wordLift e2 (wordLift e1 hV)) bW bV
  obtain ⟨d4, v4, e4, c4, v4h⟩ := emitTestHigh v3 low b3 (fun x => colState_lt (bV x) r r (W x))
  obtain ⟨d5, v5, e5, c5, p5⟩ := emitAnd v4 (e4 (e3 u2)) v4h
  refine ⟨d5, v5, fun x => e5 (e4 (e3 (e2 (e1 x)))), ?_, p5⟩
  simp only [Nat.mul_assoc] at *
  omega

lemma hasWord_const {n k : Nat} {gs : List Gate} (c : Nat)
    (h0 : Has n gs (fun _ => false)) (h1 : Has n gs (fun _ => true)) :
    HasWord n k gs (fun _ => c) := by
  intro j
  cases hc : c.testBit j.val
  · simpa [hc] using h0
  · simpa [hc] using h1

lemma hasWord_putBit {n k p : Nat} {gs : List Gate} {W : Word n} {f : BitFn n}
    (hW : HasWord n k gs W) (hf : Has n gs f) (h0 : ∀ x, (W x).testBit p = false) :
    HasWord n k gs (fun x => W x ||| ((f x).toNat <<< p)) := by
  intro j
  by_cases hjp : j.val = p
  · have heq : (fun x => (W x ||| ((f x).toNat <<< p)).testBit j.val) = f := by
      funext x; rw [hjp, testBit_putBit_eq (h0 x)]
    rw [heq]; exact hf
  · have heq : (fun x => (W x ||| ((f x).toNat <<< p)).testBit j.val) = fun x => (W x).testBit j.val := by
      funext x; exact testBit_putBit_ne hjp
    rw [heq]; exact hW j

lemma emitGuardRecover {n k r d : Nat} {gs : List Gate} (hgs : Valid n gs)
    (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    {leaf : Nat × Nat × Nat} (hgood : GoodLeaf (r - 5) d leaf)
    {U : Word n} (hU : HasWord n k gs U) (bU : ∀ x, U x < 2 ^ k)
    (h0 : Has n gs (fun _ => false)) (h1 : Has n gs (fun _ => true))
    {key0 : Nat} (hk0 : key0 < 2 ^ k)
    (hzero : ∀ j ∈ leafPivBits k (k + (k - (k + 1) / 2) + 3 * r - d) leaf, key0.testBit j = false) :
    let q := k + (k - (k + 1) / 2) + 3 * r - d
    ∀ s ≤ leaf.1,
      Grow n gs (s * (4 * k + 19 * k * r + 9))
        (fun ds => HasWord n k ds (fun x => guardRecover k q s leaf.2.1 (U x) key0)) := by
  intro q
  have hkpos : 0 < k := by omega
  have hprops := leafPosList_props hr hdn hk hgood
  intro s
  induction s with
  | zero =>
    intro _
    simpa [guardRecover_zero] using Grow.pure hgs (hasWord_const (k := k) key0 h0 h1)
  | succ s ih =>
    intro hs
    obtain ⟨d1, v1, e1, c1, w1⟩ := ih (by omega)
    have hltz : ∀ x, guardRecover k q s leaf.2.1 (U x) key0 < 2 ^ k ∧
        (guardRecover k q s leaf.2.1 (U x) key0).testBit ((gPos q leaf.2.1 s - 1) % k) = false := by
      intro x
      have h := guardRecover_lt_and_zero hr hdn hk hgood hk0 hzero (u := U x) s (by omega)
      refine ⟨h.1, h.2 _ ?_⟩
      have hlen_pb : s < (leafPivBits k q leaf).length := by simp [leafPivBits, leafPosList]; omega
      have hmem_s : (leafPivBits k q leaf)[s]'hlen_pb ∈ (leafPivBits k q leaf).drop s := by
        rw [List.mem_iff_getElem]
        exact ⟨0, by simp; omega, by simp⟩
      rwa [list_getElem_leafPivBits_left k q leaf (by omega)] at hmem_s
    obtain ⟨d2, v2, e2, c2, st2⟩ := emitRowState v1 hkpos (s + 4) w1 (wordLift e1 hU)
      (fun x => (hltz x).1) bU
    set b := bPos q leaf.2.1 s
    have hb0 : Has n d2 (fun x => (rowState k (s + 4) (guardRecover k q s leaf.2.1 (U x) key0) (U x)).testBit (b % k)) :=
      st2 ⟨b % k, Nat.mod_lt _ hkpos⟩
    have hb1 : Has n d2 (fun x => (rowState k (s + 4) (guardRecover k q s leaf.2.1 (U x) key0) (U x)).testBit ((b + 1) % k)) :=
      st2 ⟨(b + 1) % k, Nat.mod_lt _ hkpos⟩
    have hb2 : Has n d2 (fun x => (rowState k (s + 4) (guardRecover k q s leaf.2.1 (U x) key0) (U x)).testBit ((b + 2) % k)) :=
      st2 ⟨(b + 2) % k, Nat.mod_lt _ hkpos⟩
    obtain ⟨d3, v3, e3, c3, x01⟩ := emitXor v2 hb0 hb1
    obtain ⟨d4, v4, e4, c4, xg⟩ := emitXor v3 x01 (e3 hb2)
    obtain ⟨d5, v5, e5, c5, xb⟩ := emitXorConst v4 xg (leaf.2.1.testBit s)
    have hword := hasWord_putBit (wordLift e5 (wordLift e4 (wordLift e3 (wordLift e2 w1)))) xb (fun x => (hltz x).2)
    have hs4_le : s + 4 ≤ r := by rcases hgood with ⟨hl, _⟩; omega
    have hmul : 19 * k * (s + 4) ≤ 19 * k * r := Nat.mul_le_mul_left (19 * k) hs4_le
    refine ⟨d5, v5, fun x => e5 (e4 (e3 (e2 (e1 x)))), ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · simpa only [guardRecover_succ, guardRecoverStep, guardBit] using hword

lemma emitRowRecover {n k r d : Nat} {gs : List Gate} (hgs : Valid n gs)
    (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r)
    {leaf : Nat × Nat × Nat} (hgood : GoodLeaf (r - 5) d leaf)
    {U : Word n} (hU : HasWord n k gs U) (bU : ∀ x, U x < 2 ^ k)
    {key0 : Nat} (hk0 : key0 < 2 ^ k)
    (hzero : ∀ j ∈ leafPivBits k (k + (k - (k + 1) / 2) + 3 * r - d) leaf, key0.testBit j = false)
    (hK1 : HasWord n k gs (fun x => guardRecover k (k + (k - (k + 1) / 2) + 3 * r - d) leaf.1 leaf.2.1 (U x) key0)) :
    let i := k - (k + 1) / 2
    let q := k + i + 3 * r - d
    ∀ steps ≤ leaf.2.2,
      Grow n gs (steps * (4 * k + 19 * k * r))
        (fun ds => HasWord n k ds (fun x =>
          rowRecoverAux k r i q leaf.2.2 steps (U x) (guardRecover k q leaf.1 leaf.2.1 (U x) key0))) := by
  intro i q
  have hkpos : 0 < k := by omega
  have hprops := leafPosList_props hr hdn hk hgood
  have him_le : i + leaf.2.2 ≤ k := by
    rcases hgood with ⟨hl, _, _, hmeq, _⟩
    have hwl := wt_le leaf.1 leaf.2.1
    omega
  intro steps
  induction steps with
  | zero =>
    intro _
    simpa [rowRecoverAux_zero] using Grow.pure hgs hK1
  | succ steps ih =>
    intro hst
    obtain ⟨d1, v1, e1, c1, w1⟩ := ih (by omega)
    have hltz : ∀ x, rowRecoverAux k r i q leaf.2.2 steps (U x) (guardRecover k q leaf.1 leaf.2.1 (U x) key0) < 2 ^ k ∧
        (rowRecoverAux k r i q leaf.2.2 steps (U x) (guardRecover k q leaf.1 leaf.2.1 (U x) key0)).testBit
          ((rPos k q leaf.2.2 steps - 1) % k) = false := by
      intro x
      have h := rowRecoverAux_lt_and_zero hr hdn hk hgood hk0 hzero (u := U x) steps (by omega)
      refine ⟨h.1, h.2 _ ?_⟩
      have hlen_pb : leaf.1 + steps < (leafPivBits k q leaf).length := by simp [leafPivBits, leafPosList]; omega
      have hmem_s : (leafPivBits k q leaf)[leaf.1 + steps]'hlen_pb ∈ (leafPivBits k q leaf).drop (leaf.1 + steps) := by
        rw [List.mem_iff_getElem]
        exact ⟨0, by simp; omega, by simp⟩
      rwa [list_getElem_leafPivBits_right k q leaf (by omega)] at hmem_s
    obtain ⟨d2, v2, e2, c2, st2⟩ := emitRowState v1 hkpos r w1 (wordLift e1 hU)
      (fun x => (hltz x).1) bU
    have hbit : Has n d2 (fun x =>
        (rowState k r (rowRecoverAux k r i q leaf.2.2 steps (U x)
          (guardRecover k q leaf.1 leaf.2.1 (U x) key0)) (U x)).testBit (i + (leaf.2.2 - 1 - steps))) :=
      st2 ⟨i + (leaf.2.2 - 1 - steps), by omega⟩
    have hword := hasWord_putBit (wordLift e2 w1) hbit (fun x => (hltz x).2)
    refine ⟨d2, v2, fun x => e2 (e1 x), ?_, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · simpa only [rowRecoverAux_succ, rowRecoverStep] using hword

lemma nameIndexSucc {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

lemma nameIndexLt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp [tableIndex]
  | succ n ih =>
    intro x
    rw [nameIndexSucc, pow_succ]
    have := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

lemma nameIndexBit : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i.val = x i := by
  intro n
  induction n with
  | zero => intro x i; exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := nameIndexLt (fun i : Fin n => x i.castSucc)
    rw [nameIndexSucc]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

def rowWord (k : Nat) (x : Fin (k + k) → Bool) : Nat :=
  (Fin.ofNat (2 ^ k) (tableIndex fun i : Fin k => x (Fin.castAdd k i))).val

def colWord (k : Nat) (x : Fin (k + k) → Bool) : Nat :=
  (Fin.ofNat (2 ^ k) (tableIndex fun i : Fin k => x (Fin.natAdd k i))).val

lemma rowWord_lt (k : Nat) (x : Fin (k + k) → Bool) : rowWord k x < 2 ^ k :=
  (Fin.ofNat (2 ^ k) _).isLt

lemma colWord_lt (k : Nat) (x : Fin (k + k) → Bool) : colWord k x < 2 ^ k :=
  (Fin.ofNat (2 ^ k) _).isLt

lemma hasWord_row (k : Nat) : HasWord (k + k) k [] (rowWord k) := by
  intro j
  have heq : (fun x => (rowWord k x).testBit j.val) = fun x => x (Fin.castAdd k j) := by
    funext x
    change ((tableIndex fun i : Fin k => x (Fin.castAdd k i)) % 2 ^ k).testBit j.val = _
    rw [Nat.mod_eq_of_lt (nameIndexLt _), nameIndexBit]
  rw [heq]
  exact input_has (Fin.castAdd k j)

lemma hasWord_col (k : Nat) : HasWord (k + k) k [] (colWord k) := by
  intro j
  have heq : (fun x => (colWord k x).testBit j.val) = fun x => x (Fin.natAdd k j) := by
    funext x
    change ((tableIndex fun i : Fin k => x (Fin.natAdd k i)) % 2 ^ k).testBit j.val = _
    rw [Nat.mod_eq_of_lt (nameIndexLt _), nameIndexBit]
  rw [heq]
  exact input_has (Fin.natAdd k j)

lemma budget_le (k r : Nat) :
    k * (4 * k + 19 * k * r + 9) + (38 * k * r + 10 * k + 5) + 4 ≤
      128 * (k + 1) ^ 2 * (r + 1) := by
  have h1 : 4 * k + 19 * k * r + 9 ≤ 24 * (k + 1) * (r + 1) := by
    have : 24 * (k + 1) * (r + 1) = 24 * (k * r) + 24 * k + 24 * r + 24 := by ring
    simp only [Nat.mul_assoc] at *
    omega
  have h2 : k * (4 * k + 19 * k * r + 9) ≤ (k + 1) * (24 * (k + 1) * (r + 1)) :=
    Nat.mul_le_mul (Nat.le_succ k) h1
  have h3 : 38 * k * r + 10 * k + 9 ≤ 38 * (k + 1) * (r + 1) := by
    have : 38 * (k + 1) * (r + 1) = 38 * (k * r) + 38 * k + 38 * r + 38 := by ring
    simp only [Nat.mul_assoc] at *
    omega
  have h4 : 38 * (k + 1) * (r + 1) ≤ (k + 1) * (38 * (k + 1) * (r + 1)) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
  have h5 : (k + 1) * (24 * (k + 1) * (r + 1)) + (k + 1) * (38 * (k + 1) * (r + 1)) =
      62 * (k + 1) ^ 2 * (r + 1) := by ring
  have h6 : 62 * (k + 1) ^ 2 * (r + 1) ≤ 128 * (k + 1) ^ 2 * (r + 1) :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
  omega

lemma main (k r d : Nat) (hr : 6 ≤ r) (hdn : d ≤ r - 5) (hk : k + 3 + d = 5 * r) :
    let h := (k + 1) / 2
    let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
      (List.range (2 ^ k)).any (fun w =>
        decide (rowState k r w row.val < 2 ^ (k - h)) &&
        decide (colState k r r w col.val < 2 ^ (k - h)))
    let n := r - 5
    let slots := ((List.range (n + 1)).map (fun successes =>
      Nat.choose n successes * 2 ^ (k - n - (successes - d)))).sum
    ∃ C : Circuit,
      FanInTwo C ∧
      ReadsBack (k + k) C ∧
      C.size ≤ 128 * (k + 1) ^ 2 * (r + 1) * slots ∧
      ∀ bits : Fin (k + k) → Bool,
        C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits := by
  intro h graph n slots
  set i := k - h
  set q := k + i + 3 * r - d
  have hk2 : 2 ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hnk : n ≤ k := by omega
  have hqn : 3 * n + 16 ≤ q := by omega
  set allLeaves := leaves n d
  have hallGood : ∀ leaf ∈ allLeaves, GoodLeaf n d leaf :=
    leavesAux_good n d n 0 0 0 (by omega) (by decide) rfl (fun idx hidx => by omega)
  let allSlots : List ((Nat × Nat × Nat) × Nat) :=
    allLeaves.flatMap (fun leaf => (expandFree (freeBits k q leaf)).map (fun key0 => (leaf, key0)))
  have hslots_len : allSlots.length = slots := by
    have hmap : ∀ l : List (Nat × Nat × Nat), (∀ leaf ∈ l, GoodLeaf n d leaf) →
        (l.flatMap (fun leaf => (expandFree (freeBits k q leaf)).map (fun key0 => (leaf, key0)))).length =
        (l.map (fun leaf => 2 ^ (k - (leaf.1 + leaf.2.2)))).sum := by
      intro l hl
      induction l with
      | nil => simp
      | cons leaf ls ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_map, List.map_cons, List.sum_cons]
        have hgl := hl leaf (List.mem_cons_self ..)
        have hfl := (leafPosList_props hr hdn hk hgl).2.2.2.2.2
        rw [expandFree_length, hfl, ih (fun x hx => hl x (List.mem_cons_of_mem leaf hx))]
    rw [hmap allLeaves hallGood]
    have hchg := leavesAux_charge k n d hnk n 0 0 0 (by omega)
    simpa [allLeaves, leaves, binomCharge, slots] using hchg
  have hslots_pos : 1 ≤ slots := by
    have hmem : 0 ∈ List.range (n + 1) := List.mem_range.mpr (Nat.succ_pos n)
    have hle : Nat.choose n 0 * 2 ^ (k - n - (0 - d)) ≤ slots :=
      List.le_sum_of_mem (List.mem_map_of_mem hmem)
    have h1 : 1 ≤ 2 ^ (k - n - (0 - d)) := Nat.one_le_two_pow
    simp only [Nat.choose_zero_right, Nat.one_mul] at hle
    omega
  let slotBudget := k * (4 * k + 19 * k * r + 9) + (38 * k * r + 10 * k + 5)
  let slotFn : (Nat × Nat × Nat) × Nat → BitFn (k + k) := fun sl x =>
    let w := recoverKey k r i q sl.1 sl.2 (rowWord k x)
    decide (rowState k r w (rowWord k x) < 2 ^ i) &&
    decide (colState k r r w (colWord k x) < 2 ^ i)
  obtain ⟨g1, v1, e1, c1, hfalse⟩ := emitConst (empty_valid (k + k)) false
  obtain ⟨g2, v2, e2, c2, htrue⟩ := emitConst v1 true
  have hslot_emit : ∀ ds, Valid (k + k) ds → Ext (k + k) g2 ds →
      ∀ sl ∈ allSlots, Grow (k + k) ds slotBudget (fun es => Has (k + k) es (slotFn sl)) := by
    intro ds hv e sl hsl
    simp only [allSlots, List.mem_flatMap, List.mem_map] at hsl
    rcases hsl with ⟨leaf, hleaf, key0, hkey0, rfl⟩
    have hgl : GoodLeaf n d leaf := hallGood leaf hleaf
    have hprops := leafPosList_props hr hdn hk hgl
    have hfree_lt : ∀ b ∈ freeBits k q leaf, b < k := by
      intro b hb
      exact List.mem_range.mp (List.mem_filter.mp hb).1
    have hk0_lt : key0 < 2 ^ k := expandFree_mem_lt (freeBits k q leaf) hfree_lt key0 hkey0
    have hk0_zero : ∀ j ∈ leafPivBits k q leaf, key0.testBit j = false := by
      intro j hj
      apply expandFree_outside_false (freeBits k q leaf) key0 hkey0 j
      intro hmem
      have hf := (List.mem_filter.mp hmem).2
      simp [hj] at hf
    have hU : HasWord (k + k) k ds (rowWord k) := wordLift e (wordLift e2 (wordLift e1 (hasWord_row k)))
    have hV : HasWord (k + k) k ds (colWord k) := wordLift e (wordLift e2 (wordLift e1 (hasWord_col k)))
    have hf0 : Has (k + k) ds (fun _ => false) := e (e2 hfalse)
    have ht1 : Has (k + k) ds (fun _ => true) := e htrue
    obtain ⟨d1, vd1, ed1, cd1, w1⟩ := emitGuardRecover hv hr hdn hk hgl hU (rowWord_lt k) hf0 ht1 hk0_lt hk0_zero leaf.1 (le_refl _)
    obtain ⟨d2, vd2, ed2, cd2, w2⟩ := emitRowRecover vd1 hr hdn hk hgl (wordLift ed1 hU) (rowWord_lt k) hk0_lt hk0_zero w1 leaf.2.2 (le_refl _)
    have hw_lt : ∀ x, recoverKey k r i q leaf key0 (rowWord k x) < 2 ^ k := fun x =>
      (rowRecoverAux_lt_and_zero hr hdn hk hgl hk0_lt hk0_zero (u := rowWord k x) leaf.2.2 (le_refl _)).1
    obtain ⟨d3, vd3, ed3, cd3, w3⟩ := emitVerify vd2 hkpos r i w2
      (wordLift ed2 (wordLift ed1 hU)) (wordLift ed2 (wordLift ed1 hV))
      hw_lt (rowWord_lt k) (colWord_lt k)
    have hsum_le : leaf.1 + leaf.2.2 ≤ k := by
      rcases hgl with ⟨hl, _, _, hmeq, _⟩
      have hwl := wt_le leaf.1 leaf.2.1
      omega
    have hrec_le : leaf.1 * (4 * k + 19 * k * r + 9) + leaf.2.2 * (4 * k + 19 * k * r) ≤
        k * (4 * k + 19 * k * r + 9) := by
      have h1 : leaf.2.2 * (4 * k + 19 * k * r) ≤ leaf.2.2 * (4 * k + 19 * k * r + 9) :=
        Nat.mul_le_mul_left _ (by omega)
      calc
        leaf.1 * (4 * k + 19 * k * r + 9) + leaf.2.2 * (4 * k + 19 * k * r)
            ≤ leaf.1 * (4 * k + 19 * k * r + 9) + leaf.2.2 * (4 * k + 19 * k * r + 9) :=
          Nat.add_le_add_left h1 _
        _ = (leaf.1 + leaf.2.2) * (4 * k + 19 * k * r + 9) := (Nat.add_mul _ _ _).symm
        _ ≤ k * (4 * k + 19 * k * r + 9) := Nat.mul_le_mul_right _ hsum_le
    refine ⟨d3, vd3, fun x => ed3 (ed2 (ed1 x)), ?_, w3⟩
    dsimp only [slotBudget]
    omega
  obtain ⟨g3, v3, _, c3, outWire, hout_lt, hout_eval⟩ := anySlots v2 allSlots slotFn slotBudget hslot_emit
  have htotal : g3.length ≤ 128 * (k + 1) ^ 2 * (r + 1) * slots := by
    have hlen_g2 : g2.length ≤ 2 := by
      simp only [List.length_nil] at c1
      omega
    have hstep1 : g3.length ≤ 3 + slots * (slotBudget + 1) := by
      rw [hslots_len] at c3
      omega
    have hstep2 : 3 + slots * (slotBudget + 1) ≤ slots * (slotBudget + 4) := by
      have : slots * (slotBudget + 4) = slots * (slotBudget + 1) + 3 * slots := by ring
      omega
    have hstep3 : slots * (slotBudget + 4) ≤ 128 * (k + 1) ^ 2 * (r + 1) * slots := by
      rw [Nat.mul_comm (128 * (k + 1) ^ 2 * (r + 1)) slots]
      exact Nat.mul_le_mul_left slots (budget_le k r)
    omega
  refine ⟨⟨g3, outWire⟩, v3.1, v3.2, htotal, ?_⟩
  intro x
  change wireVal g3 outWire x = PEqualNP.Represents.adjFun (k := k) (l := k) graph x
  rw [hout_eval x]
  change allSlots.any (fun sl => slotFn sl x) =
    (List.range (2 ^ k)).any (fun w =>
      decide (rowState k r w (rowWord k x) < 2 ^ i) &&
      decide (colState k r r w (colWord k x) < 2 ^ i))
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨sl, hsl, hok⟩
    simp only [allSlots, List.mem_flatMap, List.mem_map] at hsl
    rcases hsl with ⟨leaf, hleaf, key0, hkey0, rfl⟩
    have hgl := hallGood leaf hleaf
    have hfree_lt : ∀ b ∈ freeBits k q leaf, b < k := fun b hb =>
      List.mem_range.mp (List.mem_filter.mp hb).1
    have hk0_lt : key0 < 2 ^ k := expandFree_mem_lt (freeBits k q leaf) hfree_lt key0 hkey0
    have hk0_zero : ∀ j ∈ leafPivBits k q leaf, key0.testBit j = false := by
      intro j hj
      apply expandFree_outside_false (freeBits k q leaf) key0 hkey0 j
      intro hmem
      have hf := (List.mem_filter.mp hmem).2
      simp [hj] at hf
    have hw_lt : recoverKey k r i q leaf key0 (rowWord k x) < 2 ^ k :=
      (rowRecoverAux_lt_and_zero hr hdn hk hgl hk0_lt hk0_zero (u := rowWord k x) leaf.2.2 (le_refl _)).1
    exact ⟨recoverKey k r i q leaf key0 (rowWord k x), hw_lt, hok⟩
  · rintro ⟨w, hw, hok⟩
    have hpass : rowState k r w (rowWord k x) < 2 ^ i :=
      of_decide_eq_true (Bool.and_eq_true_iff.mp hok).1
    obtain ⟨leaf, hleaf, htr⟩ := leavesAux_cover (k := k) (u := rowWord k x) (q := q) (n := n) (d := d) (key := w)
      n 0 0 0 (by omega) (by decide) rfl rfl
    have hgl : GoodLeaf n d leaf := hallGood leaf hleaf
    set fb := freeBits k q leaf
    set key0 := maskFree fb w
    have hfb_lt : ∀ b ∈ fb, b < k := fun b hb => List.mem_range.mp (List.mem_filter.mp hb).1
    have hk0_lt : key0 < 2 ^ k := maskFree_lt fb hfb_lt w
    have hk0_out : ∀ j, j ∉ fb → key0.testBit j = false := by
      intro j hj
      rw [testBit_maskFree]
      simp [hj]
    have hk0_mem : key0 ∈ expandFree fb := mem_expandFree_of_outside_false fb key0 hk0_lt hk0_out
    have hfree_ag : ∀ j < k, j ∉ leafPivBits k q leaf → key0.testBit j = w.testBit j := by
      intro j hj hnot
      have hjfb : j ∈ fb := by simp [fb, freeBits, hj, hnot]
      rw [testBit_maskFree]
      simp [hjfb]
    have hk0_zero : ∀ j ∈ leafPivBits k q leaf, key0.testBit j = false := by
      intro j hj
      apply hk0_out j
      intro hmem
      have hf := (List.mem_filter.mp hmem).2
      simp [hj] at hf
    have hrec : recoverKey k r i q leaf key0 (rowWord k x) = w :=
      recoverKey_exact hr hdn hk hgl (rowWord_lt k x) hw hk0_lt hpass htr hfree_ag hk0_zero
    refine ⟨(leaf, key0), ?_, ?_⟩
    · simp only [allSlots, List.mem_flatMap, List.mem_map]
      exact ⟨leaf, hleaf, key0, hk0_mem, rfl⟩
    · dsimp only [slotFn]
      rwa [hrec]

end PEqualNP.Outside.L_meta_25527

theorem PEqualNP.Outside.L_meta_25527 : ∀ (k r d : Nat), 6 ≤ r → d ≤ r - 5 → k + 3 + d = 5 * r →
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
  let h := (k + 1) / 2
  let graph : Fin (2 ^ k) → Fin (2 ^ k) → Bool := fun row col =>
    (List.range (2 ^ k)).any (fun w =>
      decide (first w row.val < 2 ^ (k - h)) && decide (second w col.val < 2 ^ (k - h)))
  let n := r - 5
  let slots := ((List.range (n + 1)).map (fun successes =>
    Nat.choose n successes * 2 ^ (k - n - (successes - d)))).sum
  ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + k) C ∧
    C.size ≤ 128 * (k + 1) ^ 2 * (r + 1) * slots ∧
    ∀ bits : Fin (k + k) → Bool,
      C.eval (List.ofFn bits) = PEqualNP.Represents.adjFun (k := k) (l := k) graph bits :=
  PEqualNP.Outside.L_meta_25527.main
