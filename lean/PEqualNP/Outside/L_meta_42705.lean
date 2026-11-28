import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42705_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def isNonlin (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def ValidCirc (w : ℕ) (C : Circuit) : Prop :=
  NestedCover.ReadsBack w C ∧ ∀ g ∈ C.gates, g.inputs.length ≤ 2

def ix (k : ℕ) (hk : 0 < k) (i : ℕ) : Fin k :=
  ⟨i % k, Nat.mod_lt _ hk⟩

def wAdd {k : ℕ} (u v : Fin k → Bool) (i : Fin k) : Bool :=
  xor (u i) (v i)

def wRot (k : ℕ) (hk : 0 < k) (s : ℕ) (w : Fin k → Bool) (i : Fin k) : Bool :=
  w (ix k hk (i.val + k - s % k))

def wMix (k : ℕ) (hk : 0 < k) (d : ℕ) (w : Fin k → Bool) (i : Fin k) : Bool :=
  xor (w (ix k hk (i.val + k - d % k))) (xor (w i) (w (ix k hk (i.val + d))))

def readBit (k : ℕ) (hk : 0 < k) (col : Bool) (u x : Fin k → Bool) (i : Fin k) : Bool :=
  let d := if col then 2 else 1
  let R := wMix k hk d (wAdd u (wRot k hk (if col then 3 else 1) x))
  xor (wRot k hk (if col then 4 else 0) x i)
    (xor (R i) (!(R (ix k hk (i.val + 1))) && R (ix k hk (i.val + 2))))

def lossVal (k : ℕ) : ℕ :=
  if 9 ≤ k ∧ 3 ∣ k then 2 else 0

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2z_false : b2z false = 0 := rfl
lemma b2z_true : b2z true = 1 := rfl
lemma b2z_xor (a b : Bool) : b2z (xor a b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide
lemma b2z_not (a : Bool) : b2z (!a) = 1 + b2z a := by
  cases a <;> decide
lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide
lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp_all [b2z]

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_eq (C : Circuit) (w : List Bool) : C.wires w = wiresFrom C.gates w := rfl
lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl
lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [wiresFrom_cons, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_snoc_self (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
  simp

lemma getD_ofFn_lt {α : Type} {n : ℕ} (f : Fin n → α) (d : α) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

def ReadsBackList (w0 : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < w0 + j

lemma readsBack_of_list (w0 : ℕ) (C : Circuit) (h : ReadsBackList w0 C.gates) :
    NestedCover.ReadsBack w0 C := by
  intro j hj i hi
  simp only [NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some] at hi
  exact h j hj i hi

lemma readsBackList_nil (w0 : ℕ) : ReadsBackList w0 [] := by
  intro j hj; simp at hj

lemma readsBackList_append (w0 : ℕ) (gs1 gs2 : List Gate)
    (h1 : ReadsBackList w0 gs1) (h2 : ReadsBackList (w0 + gs1.length) gs2) :
    ReadsBackList w0 (gs1 ++ gs2) := by
  intro j hj i hi
  by_cases hlt : j < gs1.length
  · rw [List.getElem_append_left hlt] at hi
    exact h1 j hlt i hi
  · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
    rw [List.getElem_append_right hge] at hi
    have hlt2 : j - gs1.length < gs2.length := by simp at hj; omega
    have := h2 (j - gs1.length) hlt2 i hi
    omega

lemma readsBackList_single (w0 : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < w0) :
    ReadsBackList w0 [g] := by
  intro j hj i hi
  have hj0 : j = 0 := by simp at hj; omega
  subst hj0
  simpa using h i hi

def mkConst (b : Bool) : Gate := if b then ⟨.not, []⟩ else ⟨.or, []⟩
def mkNot (i : ℕ) : Gate := ⟨.not, [i]⟩
def mkXnor (i j : ℕ) : Gate := ⟨.mod 2, [i, j]⟩
def mkAnd (i j : ℕ) : Gate := ⟨.and, [i, j]⟩

lemma isNonlin_mkConst (b : Bool) : isNonlin (mkConst b) = false := by cases b <;> rfl
lemma isNonlin_mkNot (i : ℕ) : isNonlin (mkNot i) = false := rfl
lemma isNonlin_mkXnor (i j : ℕ) : isNonlin (mkXnor i j) = false := rfl
lemma isNonlin_mkAnd (i j : ℕ) : isNonlin (mkAnd i j) = true := rfl

lemma eval_mkConst (b : Bool) (w : List Bool) :
    (mkConst b).op.eval ((mkConst b).inputs.map fun i => w.getD i false) = b := by
  cases b <;> rfl

lemma eval_mkNot (i : ℕ) (w : List Bool) :
    (mkNot i).op.eval ((mkNot i).inputs.map fun idx => w.getD idx false) = !(w.getD i false) := rfl

lemma eval_mkXnor (i j : ℕ) (w : List Bool) :
    (mkXnor i j).op.eval ((mkXnor i j).inputs.map fun idx => w.getD idx false) =
      !(xor (w.getD i false) (w.getD j false)) := by
  simp only [mkXnor, List.map, GateOp.eval]
  cases w.getD i false <;> cases w.getD j false <;> rfl

lemma eval_mkAnd (i j : ℕ) (w : List Bool) :
    (mkAnd i j).op.eval ((mkAnd i j).inputs.map fun idx => w.getD idx false) =
      (w.getD i false && w.getD j false) := by
  simp only [mkAnd, List.map, GateOp.eval]
  cases w.getD i false <;> cases w.getD j false <;> rfl

def xorListGates (start : ℕ) (c : Bool) : List ℕ → List Gate
  | [] => [mkConst c]
  | a :: ws =>
    let rest := xorListGates start c ws
    let p := start + 2 * ws.length
    rest ++ [mkXnor p a, mkNot (p + 1)]

lemma length_xorListGates (start : ℕ) (c : Bool) (ws : List ℕ) :
    (xorListGates start c ws).length = 2 * ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih => simp [xorListGates, ih]; omega

lemma countP_nonlin_xorListGates (start : ℕ) (c : Bool) (ws : List ℕ) :
    (xorListGates start c ws).countP isNonlin = 0 := by
  induction ws with
  | nil => simp [xorListGates, isNonlin_mkConst]
  | cons a ws ih =>
    simp [xorListGates, List.countP_append, ih, isNonlin_mkXnor, isNonlin_mkNot]

lemma fanin_xorListGates (start : ℕ) (c : Bool) (ws : List ℕ) :
    ∀ g ∈ xorListGates start c ws, g.inputs.length ≤ 2 := by
  induction ws with
  | nil => intro g hg; simp [xorListGates] at hg; subst hg; cases c <;> simp [mkConst]
  | cons a ws ih =>
    intro g hg
    simp [xorListGates] at hg
    rcases hg with h | rfl | rfl
    · exact ih g h
    · simp [mkXnor]
    · simp [mkNot]

lemma readsBack_xorListGates (start : ℕ) (c : Bool) (ws : List ℕ)
    (hws : ∀ a ∈ ws, a < start) : ReadsBackList start (xorListGates start c ws) := by
  induction ws with
  | nil =>
    apply readsBackList_single
    intro i hi; cases c <;> simp [mkConst] at hi
  | cons a ws ih =>
    have ha : a < start := hws a (by simp)
    have hrest : ReadsBackList start (xorListGates start c ws) :=
      ih (fun x hx => hws x (by simp [hx]))
    unfold xorListGates
    apply readsBackList_append _ _ _ hrest
    rw [length_xorListGates]
    change ReadsBackList _ ([mkXnor (start + 2 * ws.length) a] ++ [mkNot (start + 2 * ws.length + 1)])
    apply readsBackList_append
    · apply readsBackList_single
      intro i hi; simp [mkXnor] at hi; rcases hi with rfl | rfl <;> omega
    · apply readsBackList_single
      intro i hi; simp [mkNot] at hi; subst hi; simp

lemma eval_xorListGates (c : Bool) (ws : List ℕ) (w : List Bool)
    (hws : ∀ a ∈ ws, a < w.length) :
    (wiresFrom (xorListGates w.length c ws) w).getD (w.length + 2 * ws.length) false =
      ws.foldr (fun a acc => xor (w.getD a false) acc) c := by
  induction ws with
  | nil =>
    simp only [xorListGates, List.length_nil, mul_zero, add_zero, List.foldr_nil]
    rw [wiresFrom_cons, wiresFrom_nil, getD_snoc_self, eval_mkConst]
  | cons a ws ih =>
    have ha : a < w.length := hws a (by simp)
    have ih' := ih (fun x hx => hws x (by simp [hx]))
    unfold xorListGates
    rw [wiresFrom_append]
    set w1 := wiresFrom (xorListGates w.length c ws) w
    have hw1len : w1.length = w.length + (2 * ws.length + 1) := by
      rw [length_wiresFrom, length_xorListGates]
    have hwa : w1.getD a false = w.getD a false := getD_wiresFrom_lt _ _ a ha
    rw [wiresFrom_cons, wiresFrom_cons, wiresFrom_nil]
    have hidx : w.length + 2 * (ws.length + 1) = (w1 ++ [(mkXnor (w.length + 2 * ws.length) a).op.eval
        ((mkXnor (w.length + 2 * ws.length) a).inputs.map fun i => w1.getD i false)]).length := by
      simp [hw1len]; omega
    rw [show w.length + 2 * (a :: ws).length = w.length + 2 * (ws.length + 1) by simp]
    rw [hidx, getD_snoc_self, eval_mkNot]
    have hidx1 : w.length + 2 * ws.length + 1 = w1.length := by omega
    rw [hidx1, getD_snoc_self, eval_mkXnor, hwa, ih']
    simp only [List.foldr_cons]
    cases w.getD a false <;> cases ws.foldr (fun a acc => xor (w.getD a false) acc) c <;> rfl

def appendSpecs (start : ℕ) : List (Bool × List ℕ) → List Gate × List ℕ
  | [] => ([], [])
  | (c, ws) :: rest =>
    let g1 := xorListGates start c ws
    let tap1 := start + 2 * ws.length
    let (gs2, taps2) := appendSpecs (start + g1.length) rest
    (g1 ++ gs2, tap1 :: taps2)

lemma appendSpecs_taps_len (start : ℕ) (specs : List (Bool × List ℕ)) :
    (appendSpecs start specs).2.length = specs.length := by
  induction specs generalizing start with
  | nil => rfl
  | cons s rest ih => simp [appendSpecs, ih]

lemma appendSpecs_nonlin (start : ℕ) (specs : List (Bool × List ℕ)) :
    (appendSpecs start specs).1.countP isNonlin = 0 := by
  induction specs generalizing start with
  | nil => rfl
  | cons s rest ih =>
    rcases s with ⟨c, ws⟩
    simp [appendSpecs, List.countP_append, countP_nonlin_xorListGates, ih]

lemma appendSpecs_fanin (start : ℕ) (specs : List (Bool × List ℕ)) :
    ∀ g ∈ (appendSpecs start specs).1, g.inputs.length ≤ 2 := by
  induction specs generalizing start with
  | nil => intro g hg; simp [appendSpecs] at hg
  | cons s rest ih =>
    rcases s with ⟨c, ws⟩
    intro g hg
    simp [appendSpecs] at hg
    rcases hg with h | h
    · exact fanin_xorListGates _ _ _ g h
    · exact ih _ g h

lemma appendSpecs_readsBack (start : ℕ) (specs : List (Bool × List ℕ))
    (hspecs : ∀ s ∈ specs, ∀ a ∈ s.2, a < start) :
    ReadsBackList start (appendSpecs start specs).1 := by
  induction specs generalizing start with
  | nil => exact readsBackList_nil start
  | cons s rest ih =>
    rcases s with ⟨c, ws⟩
    simp only [appendSpecs]
    apply readsBackList_append
    · exact readsBack_xorListGates start c ws (hspecs (c, ws) (by simp))
    · exact ih (start + (xorListGates start c ws).length)
        (fun s' hs' a ha => Nat.lt_of_lt_of_le (hspecs s' (by simp [hs']) a ha) (Nat.le_add_right _ _))

lemma appendSpecs_taps_lt (start : ℕ) (specs : List (Bool × List ℕ)) :
    ∀ t ∈ (appendSpecs start specs).2, t < start + (appendSpecs start specs).1.length := by
  induction specs generalizing start with
  | nil => intro t ht; simp [appendSpecs] at ht
  | cons s rest ih =>
    rcases s with ⟨c, ws⟩
    intro t ht
    simp only [appendSpecs, List.mem_cons, List.length_append] at ht ⊢
    rcases ht with rfl | ht
    · rw [length_xorListGates]; omega
    · have h := ih (start + (xorListGates start c ws).length) t ht
      omega

lemma appendSpecs_eval (specs : List (Bool × List ℕ)) (w : List Bool)
    (hspecs : ∀ s ∈ specs, ∀ a ∈ s.2, a < w.length)
    (i : ℕ) (hi : i < specs.length) :
    (wiresFrom (appendSpecs w.length specs).1 w).getD
      ((appendSpecs w.length specs).2.getD i 0) false =
      specs[i].2.foldr (fun a acc => xor (w.getD a false) acc) specs[i].1 := by
  induction specs generalizing w i with
  | nil => simp at hi
  | cons s rest ih =>
    rcases s with ⟨c, ws⟩
    simp only [appendSpecs]
    rw [wiresFrom_append]
    set w1 := wiresFrom (xorListGates w.length c ws) w
    have hw1len : w1.length = w.length + (xorListGates w.length c ws).length := length_wiresFrom _ _
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, List.getElem_cons_zero]
      have htap : w.length + 2 * ws.length < w1.length := by
        rw [hw1len, length_xorListGates]; omega
      rw [getD_wiresFrom_lt _ w1 _ htap]
      exact eval_xorListGates c ws w (hspecs (c, ws) (by simp))
    | succ i' =>
      simp only [List.getD_cons_succ, List.getElem_cons_succ]
      have hi' : i' < rest.length := by simp at hi; omega
      have hrest : ∀ s' ∈ rest, ∀ a ∈ s'.2, a < w1.length := by
        intro s' hs' a ha
        have hlt := hspecs s' (by simp [hs']) a ha
        omega
      have hEq := ih w1 hrest i' hi'
      rw [hw1len] at hEq
      rw [hEq]
      have hsub : ∀ a ∈ rest[i'].2, w1.getD a false = w.getD a false := by
        intro a ha
        exact getD_wiresFrom_lt _ w a (hspecs rest[i'] (by simp) a ha)
      clear hEq
      generalize rest[i'].1 = c0
      revert hsub
      induction rest[i'].2 with
      | nil => intro _; rfl
      | cons a l ihl =>
        intro hsub
        simp only [List.foldr_cons]
        rw [hsub a (by simp), ihl (fun x hx => hsub x (by simp [hx]))]

lemma mod_of_lt_two (k x : ℕ) (h : x < 2 * k) :
    x % k = if x < k then x else x - k := by
  split_ifs with h1
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)

lemma mod_of_lt_three (k x : ℕ) (h : x < 3 * k) :
    x % k = if x < k then x else if x < 2 * k then x - k else x - 2 * k := by
  split_ifs with h1 h2
  · exact Nat.mod_eq_of_lt h1
  · rw [Nat.mod_eq_sub_mod (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
        show x - k - k = x - 2 * k by omega]
    exact Nat.mod_eq_of_lt (by omega)

lemma mod_add_cancel (k a b : ℕ) : (a % k + b) % k = (a + b) % k := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma mod_add_k_sub (k a d : ℕ) (hd : d ≤ k) : (a % k + k - d) % k = (a + (k - d)) % k := by
  rw [show a % k + k - d = a % k + (k - d) by omega, mod_add_cancel]

lemma mod_add_k_sub_self (k a d : ℕ) (hd : d ≤ k) : (a + k - d) % k = (a + (k - d)) % k := by
  rw [show a + k - d = a + (k - d) by omega]

def singleBit (k : ℕ) (p : Fin k) : Fin k → Bool :=
  fun i => decide (i = p)

lemma wMix_singleBit (k : ℕ) (hk : 0 < k) (p i : Fin k) :
    wMix k hk 1 (singleBit k p) i =
      xor (decide (ix k hk (i.val + k - 1 % k) = p))
        (xor (decide (i = p)) (decide (ix k hk (i.val + 1) = p))) := rfl

lemma wMix_add {k : ℕ} (hk : 0 < k) (d : ℕ) (u v : Fin k → Bool) (i : Fin k) :
    wMix k hk d (wAdd u v) i = xor (wMix k hk d u i) (wMix k hk d v i) := by
  simp only [wMix, wAdd]
  cases u (ix k hk (i.val + k - d % k)) <;> cases v (ix k hk (i.val + k - d % k)) <;>
  cases u i <;> cases v i <;>
  cases u (ix k hk (i.val + d)) <;> cases v (ix k hk (i.val + d)) <;> rfl

lemma wMix_zero {k : ℕ} (hk : 0 < k) (d : ℕ) (i : Fin k) :
    wMix k hk d (fun _ => false) i = false := by
  simp [wMix]

lemma rowDiff_ge4 (k : ℕ) (hk : 4 ≤ k) (x : Fin k → Bool) (i : Fin k) :
    have hk0 : 0 < k := by omega
    xor (readBit k hk0 false (singleBit k i) x i)
        (readBit k hk0 false (fun _ => false) x i) =
      !(wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (i.val + 2))) := by
  have hk0 : 0 < k := by omega
  have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hi_lt : i.val < k := i.isLt
  have hc0 : wMix k hk0 1 (singleBit k i) i = true := by
    rw [wMix_singleBit]
    have h1 : ix k hk0 (i.val + k - 1 % k) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix, h1mod] at h
      rw [mod_of_lt_two k (i.val + k - 1) (by omega)] at h; split_ifs at h <;> omega
    have h2 : ix k hk0 (i.val + 1) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
      rw [mod_of_lt_two k (i.val + 1) (by omega)] at h; split_ifs at h <;> omega
    simp [h1, h2]
  have hc1 : wMix k hk0 1 (singleBit k i) (ix k hk0 (i.val + 1)) = true := by
    rw [wMix_singleBit]
    have h1 : ix k hk0 ((ix k hk0 (i.val + 1)).val + k - 1 % k) = i := by
      rw [Fin.ext_iff]; simp only [ix, h1mod]
      rw [mod_add_k_sub k (i.val + 1) 1 (by omega), mod_of_lt_three k _ (by omega)]
      split_ifs <;> omega
    have h2 : ix k hk0 (i.val + 1) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
      rw [mod_of_lt_two k (i.val + 1) (by omega)] at h; split_ifs at h <;> omega
    have h3 : ix k hk0 ((ix k hk0 (i.val + 1)).val + 1) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
      rw [mod_add_cancel, mod_of_lt_two k _ (by omega)] at h; split_ifs at h <;> omega
    simp [h1, h2, h3]
  have hc2 : wMix k hk0 1 (singleBit k i) (ix k hk0 (i.val + 2)) = false := by
    rw [wMix_singleBit]
    have h1 : ix k hk0 ((ix k hk0 (i.val + 2)).val + k - 1 % k) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix, h1mod] at h
      rw [mod_add_k_sub k (i.val + 2) 1 (by omega), mod_of_lt_three k _ (by omega)] at h
      split_ifs at h <;> omega
    have h2 : ix k hk0 (i.val + 2) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
      rw [mod_of_lt_two k _ (by omega)] at h; split_ifs at h <;> omega
    have h3 : ix k hk0 ((ix k hk0 (i.val + 2)).val + 1) ≠ i := by
      intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
      rw [mod_add_cancel, mod_of_lt_two k _ (by omega)] at h; split_ifs at h <;> omega
    simp [h1, h2, h3]
  simp only [readBit, Bool.false_eq_true, ↓reduceIte, wMix_add, wMix_zero, Bool.false_xor,
    hc0, hc1, hc2, Bool.true_xor]
  cases wRot k hk0 0 x i <;>
  cases wMix k hk0 1 (wRot k hk0 1 x) i <;>
  cases wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (i.val + 1)) <;>
  cases wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (i.val + 2)) <;> rfl

lemma readBit_row_zero_recover (k : ℕ) (hk : 0 < k) (x : Fin k → Bool) (i : Fin k) :
    let R0 := wMix k hk 1 (wRot k hk 1 x)
    xor (readBit k hk false (fun _ => false) x i)
      (xor (R0 i) (!(R0 (ix k hk (i.val + 1))) && R0 (ix k hk (i.val + 2)))) = x i := by
  have h0 : wRot k hk 0 x i = x i := by
    simp only [wRot, Nat.zero_mod, Nat.sub_zero, ix]
    congr 1; apply Fin.ext; simp [Nat.mod_eq_of_lt i.isLt]
  simp only [readBit, Bool.false_eq_true, ↓reduceIte, h0, wMix_add, wMix_zero, Bool.false_xor]
  cases x i <;> cases wMix k hk 1 (wRot k hk 1 x) i <;>
  cases (!(wMix k hk 1 (wRot k hk 1 x) (ix k hk (i.val + 1))) &&
    wMix k hk 1 (wRot k hk 1 x) (ix k hk (i.val + 2))) <;> rfl

lemma wMix_rot1_eq (k : ℕ) (hk : 2 ≤ k) (x : Fin k → Bool) (i : Fin k) :
    have hk0 : 0 < k := by omega
    wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (i.val + 1)) =
      xor (x (ix k hk0 (i.val + k - 1))) (xor (x i) (x (ix k hk0 (i.val + 1)))) := by
  have hk0 : 0 < k := by omega
  have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hi := i.isLt
  simp only [wMix, wRot, ix, h1mod]
  have e1 : (((i.val + 1) % k + k - 1) % k + k - 1) % k = (i.val + k - 1) % k := by
    rw [mod_add_k_sub k (i.val + 1) 1 (by omega), mod_add_k_sub k _ 1 (by omega),
        mod_of_lt_three k _ (by omega), mod_of_lt_two k _ (by omega)]
    split_ifs <;> omega
  have e2 : ((i.val + 1) % k + k - 1) % k = i.val := by
    rw [mod_add_k_sub k (i.val + 1) 1 (by omega), mod_of_lt_three k _ (by omega)]
    split_ifs <;> omega
  have e3 : (((i.val + 1) % k + 1) % k + k - 1) % k = (i.val + 1) % k := by
    rw [mod_add_cancel, mod_add_k_sub k (i.val + 1 + 1) 1 (by omega),
        mod_of_lt_three k _ (by omega), mod_of_lt_two k _ (by omega)]
    split_ifs <;> omega
  have f1 : (⟨(((i.val + 1) % k + k - 1) % k + k - 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) =
      ⟨(i.val + k - 1) % k, Nat.mod_lt _ hk0⟩ := Fin.ext e1
  have f2 : (⟨((i.val + 1) % k + k - 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) = i := Fin.ext e2
  have f3 : (⟨(((i.val + 1) % k + 1) % k + k - 1) % k, Nat.mod_lt _ hk0⟩ : Fin k) =
      ⟨(i.val + 1) % k, Nat.mod_lt _ hk0⟩ := Fin.ext e3
  rw [f1, f2, f3]

lemma sum_wMix_zmod (k : ℕ) (hk : 2 ≤ k) (w : Fin k → Bool) :
    have hk0 : 0 < k := by omega
    ∑ i : Fin k, b2z (wMix k hk0 1 w i) = ∑ i : Fin k, b2z (w i) := by
  have hk0 : 0 < k := by omega
  have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  simp_rw [wMix, b2z_xor, Finset.sum_add_distrib]
  let ePrev : Equiv.Perm (Fin k) :=
    { toFun := fun i => ix k hk0 (i.val + k - 1 % k)
      invFun := fun i => ix k hk0 (i.val + 1)
      left_inv := fun i => by
        apply Fin.ext; simp only [ix, h1mod]
        rw [mod_add_cancel, show i.val + k - 1 + 1 = i.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      right_inv := fun i => by
        apply Fin.ext; simp only [ix, h1mod]
        rw [mod_add_k_sub k (i.val + 1) 1 (by omega), mod_of_lt_three k _ (by omega)]
        split_ifs <;> omega }
  let eNext : Equiv.Perm (Fin k) := ePrev.symm
  have h1 : ∑ i : Fin k, b2z (w (ix k hk0 (i.val + k - 1 % k))) = ∑ i : Fin k, b2z (w i) :=
    Equiv.sum_comp ePrev (fun i => b2z (w i))
  have h2 : ∑ i : Fin k, b2z (w (ix k hk0 (i.val + 1))) = ∑ i : Fin k, b2z (w i) :=
    Equiv.sum_comp eNext (fun i => b2z (w i))
  rw [h1, h2]
  have htwo : ∀ a : ZMod 2, a + (a + a) = a := by decide
  exact htwo _

def invMixIndices (k : ℕ) (hk : 4 ≤ k) (j : Fin k) : List (Fin k) :=
  have hk0 : 0 < k := by omega
  if k % 3 = 1 then
    (List.finRange k) ++ (List.range (k / 3)).map (fun r => ix k hk0 (j.val + 3 * r + 3))
  else
    (List.finRange k) ++ (List.range (k / 3 + 1)).map (fun r => ix k hk0 (j.val + 3 * r + 2))

lemma foldr_xor_b2z {α : Type} (f : α → Bool) (l : List α) :
    b2z (l.foldr (fun a acc => xor (f a) acc) false) = (l.map (fun a => b2z (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [b2z_xor, ih]

lemma invMixIndices_correct (k : ℕ) (hk : 4 ≤ k) (hndiv : ¬ 3 ∣ k) (x : Fin k → Bool) (j : Fin k) :
    have hk0 : 0 < k := by omega
    (invMixIndices k hk j).foldr (fun idx acc => xor (wMix k hk0 1 (wRot k hk0 1 x) idx) acc) false =
      x j := by
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  apply b2z_inj
  rw [foldr_xor_b2z]
  set R0 := wMix k hk0 1 (wRot k hk0 1 x)
  have htot : ((List.finRange k).map (fun a => b2z (R0 a))).sum = ∑ i : Fin k, b2z (x i) := by
    have hfr : ((List.finRange k).map (fun a => b2z (R0 a))).sum = ∑ a : Fin k, b2z (R0 a) := by
      simp [Finset.sum, Fin.univ_def]
    rw [hfr, sum_wMix_zmod k hk2]
    let eRot : Equiv.Perm (Fin k) :=
      { toFun := fun i => ix k hk0 (i.val + k - 1 % k)
        invFun := fun i => ix k hk0 (i.val + 1)
        left_inv := fun i => by
          apply Fin.ext; simp only [ix, Nat.mod_eq_of_lt (by omega : 1 < k)]
          rw [mod_add_cancel, show i.val + k - 1 + 1 = i.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
        right_inv := fun i => by
          apply Fin.ext; simp only [ix, Nat.mod_eq_of_lt (by omega : 1 < k)]
          rw [mod_add_k_sub k (i.val + 1) 1 (by omega), mod_of_lt_three k _ (by omega)]
          split_ifs <;> omega }
    exact Equiv.sum_comp eRot (fun i => b2z (x i))
  have hstep : ∀ t : ℕ, b2z (R0 (ix k hk0 (t + 1))) =
      b2z (x (ix k hk0 (t + k - 1))) + b2z (x (ix k hk0 t)) + b2z (x (ix k hk0 (t + 1))) := by
    intro t
    have hEq := wMix_rot1_eq k hk2 x (ix k hk0 t)
    dsimp only at hEq
    have h1 : ix k hk0 ((ix k hk0 t).val + 1) = ix k hk0 (t + 1) := by
      apply Fin.ext; simp only [ix]; exact mod_add_cancel k t 1
    have h2 : ix k hk0 ((ix k hk0 t).val + k - 1) = ix k hk0 (t + k - 1) := by
      apply Fin.ext; simp only [ix]
      rw [mod_add_k_sub k t 1 (by omega), mod_add_k_sub_self k t 1 (by omega)]
    rw [h1, h2] at hEq
    change b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (t + 1))) = _
    rw [hEq, b2z_xor, b2z_xor, add_assoc]
  have hblock : ∀ q : ℕ,
      ((List.range q).map (fun r => b2z (R0 (ix k hk0 (j.val + 3 * r + 3))))).sum =
        ((List.range (3 * q)).map (fun s => b2z (x (ix k hk0 (j.val + 1 + s))))).sum := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih]
      have h3 : 3 * (q + 1) = 3 * q + 3 := by omega
      rw [h3, List.range_succ, List.range_succ, List.range_succ]
      simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
      have hst := hstep (j.val + 3 * q + 2)
      have ha1 : j.val + 3 * q + 2 + 1 = j.val + 3 * q + 3 := by omega
      have ha2 : ix k hk0 (j.val + 3 * q + 2 + k - 1) = ix k hk0 (j.val + 1 + 3 * q) := by
        apply Fin.ext; simp only [ix]
        rw [show j.val + 3 * q + 2 + k - 1 = (j.val + 1 + 3 * q) + k by omega, Nat.add_mod_right]
      have ha3 : ix k hk0 (j.val + 3 * q + 2) = ix k hk0 (j.val + 1 + (3 * q + 1)) := by
        congr 1; omega
      have ha4 : ix k hk0 (j.val + 3 * q + 2 + 1) = ix k hk0 (j.val + 1 + (3 * q + 2)) := by
        congr 1; omega
      conv_lhs at hst => rw [ha1]
      conv_rhs at hst => rw [ha2, ha3, ha4]
      rw [hst]; ring
  have hsum_range : ∀ offset : ℕ,
      ((List.range k).map (fun s => b2z (x (ix k hk0 (offset + s))))).sum = ∑ i : Fin k, b2z (x i) := by
    intro offset
    have h1 : ((List.range k).map (fun s => b2z (x (ix k hk0 (offset + s))))).sum =
        ∑ s : Fin k, b2z (x (ix k hk0 (offset + s.val))) := by
      have hmr : (List.finRange k).map (fun s : Fin k => s.val) = List.range k :=
        List.ext_getElem (by simp) (fun i h1 h2 => by simp)
      simp only [Finset.sum, Fin.univ_def, Multiset.map_coe, Multiset.sum_coe]
      rw [← hmr, List.map_map]
      rfl
    rw [h1]
    let eShift : Equiv.Perm (Fin k) :=
      { toFun := fun s => ix k hk0 (offset + s.val)
        invFun := fun s => ix k hk0 (s.val + k - offset % k)
        left_inv := fun s => by
          apply Fin.ext; simp only [ix]
          rw [mod_add_k_sub k (offset + s.val) (offset % k) (Nat.le_of_lt (Nat.mod_lt _ hk0))]
          have hdiv : (offset / k) * k + offset % k = offset := by linarith [Nat.div_add_mod offset k]
          have hmodlt := Nat.mod_lt offset hk0
          rw [show offset + s.val + (k - offset % k) = s.val + (offset / k + 1) * k by
            calc offset + s.val + (k - offset % k) = ((offset / k) * k + offset % k) + s.val + (k - offset % k) := by rw [hdiv]
              _ = s.val + ((offset / k) * k + k) := by omega
              _ = s.val + (offset / k + 1) * k := by ring]
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt s.isLt]
        right_inv := fun s => by
          apply Fin.ext; simp only [ix]
          have hdiv : (offset / k) * k + offset % k = offset := by linarith [Nat.div_add_mod offset k]
          have hmodlt := Nat.mod_lt offset hk0
          rw [Nat.add_comm offset _, mod_add_cancel,
              show s.val + k - offset % k + offset = s.val + (offset / k + 1) * k by
                calc s.val + k - offset % k + offset = s.val + k - offset % k + ((offset / k) * k + offset % k) := by rw [hdiv]
                  _ = s.val + ((offset / k) * k + k) := by omega
                  _ = s.val + (offset / k + 1) * k := by ring,
              Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt s.isLt] }
    exact Equiv.sum_comp eShift (fun i => b2z (x i))
  unfold invMixIndices
  split_ifs with hmod1
  · rw [List.map_append, List.sum_append, List.map_map, htot]
    change ∑ i : Fin k, b2z (x i) +
      ((List.range (k / 3)).map (fun r => b2z (R0 (ix k hk0 (j.val + 3 * r + 3))))).sum = b2z (x j)
    rw [hblock (k / 3)]
    have hk_eq : k = 3 * (k / 3) + 1 := by omega
    have htot2 := hsum_range (j.val + 1)
    have hrange_eq : List.range k = List.range (3 * (k / 3)) ++ [3 * (k / 3)] := by
      conv_lhs => rw [hk_eq]
      exact List.range_succ
    rw [hrange_eq, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton] at htot2
    have hlast : ix k hk0 (j.val + 1 + 3 * (k / 3)) = j := by
      apply Fin.ext; simp only [ix]
      rw [show j.val + 1 + 3 * (k / 3) = j.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    rw [hlast] at htot2
    rw [← htot2]
    have hcancel : ∀ a b : ZMod 2, (a + b) + a = b := by decide
    exact hcancel _ _
  · have hmod2 : k % 3 = 2 := by omega
    rw [List.map_append, List.sum_append, List.map_map, htot]
    change ∑ i : Fin k, b2z (x i) +
      ((List.range (k / 3 + 1)).map (fun r => b2z (R0 (ix k hk0 (j.val + 3 * r + 2))))).sum = b2z (x j)
    have hblock2 : ∀ q : ℕ,
        ((List.range q).map (fun r => b2z (R0 (ix k hk0 (j.val + 3 * r + 2))))).sum =
          ((List.range (3 * q)).map (fun s => b2z (x (ix k hk0 (j.val + s))))).sum := by
      intro q
      induction q with
      | zero => simp
      | succ q ih =>
        rw [List.range_succ, List.map_append, List.sum_append, ih]
        have h3 : 3 * (q + 1) = 3 * q + 3 := by omega
        rw [h3, List.range_succ, List.range_succ, List.range_succ]
        simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        have hst := hstep (j.val + 3 * q + 1)
        have ha1 : j.val + 3 * q + 1 + 1 = j.val + 3 * q + 2 := by omega
        have ha2 : ix k hk0 (j.val + 3 * q + 1 + k - 1) = ix k hk0 (j.val + 3 * q) := by
          apply Fin.ext; simp only [ix]
          rw [show j.val + 3 * q + 1 + k - 1 = (j.val + 3 * q) + k by omega, Nat.add_mod_right]
        have ha3 : ix k hk0 (j.val + 3 * q + 1) = ix k hk0 (j.val + (3 * q + 1)) := by
          congr 1
        have ha4 : ix k hk0 (j.val + 3 * q + 1 + 1) = ix k hk0 (j.val + (3 * q + 2)) := by
          congr 1
        conv_lhs at hst => rw [ha1]
        conv_rhs at hst => rw [ha2, ha3, ha4]
        rw [hst]; ring
    rw [hblock2 (k / 3 + 1)]
    have hk_eq : 3 * (k / 3 + 1) = k + 1 := by omega
    rw [hk_eq, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, hsum_range j.val]
    have hlast : ix k hk0 (j.val + k) = j := by
      apply Fin.ext; simp only [ix, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    rw [hlast]
    have hcancel : ∀ a b : ZMod 2, a + (a + b) = b := by decide
    exact hcancel _ _

def recAnchor0 (i : ℕ) : Bool := i % 3 == 0 || i % 3 == 2
def recAnchor1 (i : ℕ) : Bool := i % 3 == 1 || i % 3 == 2

def recR0Indices (k : ℕ) (hk : 0 < k) : ℕ → List (Fin k)
  | 0 => []
  | 1 => []
  | m + 2 => ix k hk (m + 2) :: (recR0Indices k hk m ++ recR0Indices k hk (m + 1))

lemma rec_correct (k : ℕ) (hk : 2 ≤ k) (x : Fin k → Bool) :
    ∀ m (hm : m < k),
      have hk0 : 0 < k := by omega
      xor (if recAnchor0 m then x ⟨0, hk0⟩ else false)
        (xor (if recAnchor1 m then x ⟨1, by omega⟩ else false)
          ((recR0Indices k hk0 m).foldr (fun idx acc => xor (wMix k hk0 1 (wRot k hk0 1 x) idx) acc) false)) =
        x ⟨m, hm⟩ := by
  have hk0 : 0 < k := by omega
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    dsimp only
    match m with
    | 0 => simp [recAnchor0, recAnchor1, recR0Indices]
    | 1 => simp [recAnchor0, recAnchor1, recR0Indices]
    | m + 2 =>
      have ih0 := ih m (by omega) (by omega)
      have ih1 := ih (m + 1) (by omega) (by omega)
      dsimp only at ih0 ih1
      have hstep := wMix_rot1_eq k hk x ⟨m + 1, by omega⟩
      dsimp only at hstep
      have h1 : ix k hk0 (m + 1 + 1) = ix k hk0 (m + 2) := rfl
      have h2 : ix k hk0 (m + 1 + k - 1) = ⟨m, by omega⟩ := by
        apply Fin.ext; simp only [ix]
        rw [show m + 1 + k - 1 = m + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have h3 : ix k hk0 (m + 1 + 1) = ⟨m + 2, hm⟩ := by
        apply Fin.ext; simp only [ix, Nat.mod_eq_of_lt hm]
      rw [h2] at hstep
      have hstep' : wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (m + 2)) =
          xor (x ⟨m, by omega⟩) (xor (x ⟨m + 1, by omega⟩) (x ⟨m + 2, hm⟩)) := by
        simpa [h1, h3] using hstep
      apply b2z_inj
      simp only [recR0Indices, List.foldr_cons, List.foldr_append, b2z_xor]
      have hf_app : ∀ (l1 l2 : List (Fin k)) (f : Fin k → Bool),
          b2z (l1.foldr (fun idx acc => xor (f idx) acc) (l2.foldr (fun idx acc => xor (f idx) acc) false)) =
            b2z (l1.foldr (fun idx acc => xor (f idx) acc) false) +
              b2z (l2.foldr (fun idx acc => xor (f idx) acc) false) := by
        intro l1 l2 f
        induction l1 with
        | nil => simp [b2z_false]
        | cons a l1 ihl => simp [b2z_xor, ihl, add_assoc]
      rw [hf_app]
      have hz0 := congrArg b2z ih0
      have hz1 := congrArg b2z ih1
      have hzs := congrArg b2z hstep'
      simp only [b2z_xor] at hz0 hz1 hzs
      have ha0 : b2z (if recAnchor0 (m + 2) then x ⟨0, hk0⟩ else false) =
          b2z (if recAnchor0 m then x ⟨0, hk0⟩ else false) +
            b2z (if recAnchor0 (m + 1) then x ⟨0, hk0⟩ else false) := by
        have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
        rcases this with h | h | h <;>
        · have h1' : (m + 1) % 3 = (m % 3 + 1) % 3 := by omega
          have h2' : (m + 2) % 3 = (m % 3 + 2) % 3 := by omega
          simp [recAnchor0, h, h1', h2']
          cases x ⟨0, hk0⟩ <;> decide
      have ha1 : b2z (if recAnchor1 (m + 2) then x ⟨1, by omega⟩ else false) =
          b2z (if recAnchor1 m then x ⟨1, by omega⟩ else false) +
            b2z (if recAnchor1 (m + 1) then x ⟨1, by omega⟩ else false) := by
        have : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
        rcases this with h | h | h <;>
        · have h1' : (m + 1) % 3 = (m % 3 + 1) % 3 := by omega
          have h2' : (m + 2) % 3 = (m % 3 + 2) % 3 := by omega
          simp [recAnchor1, h, h1', h2']
          cases x ⟨1, by omega⟩ <;> decide
      rw [ha0, ha1, hzs, ← hz0, ← hz1]
      have h2z : (2 : ZMod 2) = 0 := by decide
      apply sub_eq_zero.mp
      calc _ = 2 * (b2z (if recAnchor0 m = true then x ⟨0, hk0⟩ else false) +
                    b2z (if recAnchor0 (m + 1) = true then x ⟨0, hk0⟩ else false) +
                    b2z (if recAnchor1 m = true then x ⟨1, by omega⟩ else false) +
                    b2z (if recAnchor1 (m + 1) = true then x ⟨1, by omega⟩ else false) +
                    b2z (List.foldr (fun idx acc => wMix k hk0 1 (wRot k hk0 1 x) idx ^^ acc) false (recR0Indices k hk0 m)) +
                    b2z (List.foldr (fun idx acc => wMix k hk0 1 (wRot k hk0 1 x) idx ^^ acc) false (recR0Indices k hk0 (m + 1)))) := by ring
        _ = 0 := by rw [h2z, zero_mul]

lemma readBit_const_k1 (col : Bool) (u x : Fin 1 → Bool) (i : Fin 1) :
    readBit 1 (by omega) col u x i = u 0 := by
  have hx : x = ![x 0] := by funext r; fin_cases r; rfl
  have hu : u = ![u 0] := by funext r; fin_cases r; rfl
  rw [hx, hu]
  revert col i
  generalize x 0 = x0; generalize u 0 = u0
  revert x0 u0; decide

lemma readBit_const_k3 (col : Bool) (u : Fin 3 → Bool) (c : Bool) (i : Fin 3) :
    readBit 3 (by omega) col u (fun _ => c) i = readBit 3 (by omega) col u (fun _ => false) i := by
  have hu : u = ![u 0, u 1, u 2] := by funext r; fin_cases r <;> rfl
  rw [hu]
  revert col c i
  generalize u 0 = u0; generalize u 1 = u1; generalize u 2 = u2
  revert u0 u1 u2; decide

lemma lower_k1_or_k3 (k : ℕ) (hk : 0 < k) (hk13 : k = 1 ∨ k = 3) (n b t : ℕ)
    (h : ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
        (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
        (side : (Fin n → Fin k → Bool) → Fin b → Bool) (C : Circuit)
        (tap : Fin n → Fin k → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i) : n ≤ b := by
  obtain ⟨a, bank, key, name, site, side, C, tap, _, _, _, hdec⟩ := h
  let emb : (Fin n → Bool) → (Fin n → Fin k → Bool) := fun c j _ => c j
  have hrb : ∀ c : Fin n → Bool, ∀ l : Fin a,
      readBit k hk (bank l) (name l) (emb c (key l)) (site l) =
        readBit k hk (bank l) (name l) (fun _ => false) (site l) := by
    intro c l
    rcases hk13 with rfl | rfl
    · simp [readBit_const_k1]
    · exact readBit_const_k3 (bank l) (name l) (c (key l)) (site l)
  have hinj : Function.Injective (fun c : Fin n → Bool => side (emb c)) := by
    intro c1 c2 hside
    dsimp only at hside
    funext j
    have hdata :
        List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (emb c1 (key l)) (site l)) ++
          List.ofFn (side (emb c1)) =
        List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (emb c2 (key l)) (site l)) ++
          List.ofFn (side (emb c2)) := by
      congr 1
      · congr 1; funext l; rw [hrb c1 l, hrb c2 l]
      · rw [hside]
    have h1 := hdec (emb c1) j ⟨0, hk⟩
    have h2 := hdec (emb c2) j ⟨0, hk⟩
    dsimp only at h1 h2
    rw [hdata] at h1
    exact h1.symm.trans h2
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hcard

def updBit {n k : ℕ} (x : Fin n → Fin k → Bool) (j : Fin n) (p : Fin k) : Fin n → Fin k → Bool :=
  fun j' i' => if j' = j ∧ i' = p then !(x j' i') else x j' i'

def deriv2 {n k : ℕ} (f : (Fin n → Fin k → Bool) → ZMod 2) (j : Fin n) (p q : Fin k) : ZMod 2 :=
  let z : Fin n → Fin k → Bool := fun _ _ => false
  f z + f (updBit z j p) + f (updBit z j q) + f (updBit (updBit z j p) j q)

lemma deriv2_add {n k : ℕ} (f g : (Fin n → Fin k → Bool) → ZMod 2) (j : Fin n) (p q : Fin k) :
    deriv2 (f + g) j p q = deriv2 f j p q + deriv2 g j p q := by
  simp only [deriv2, Pi.add_apply]; ring

lemma deriv2_smul {n k : ℕ} (c : ZMod 2) (f : (Fin n → Fin k → Bool) → ZMod 2) (j : Fin n) (p q : Fin k) :
    deriv2 (c • f) j p q = c * deriv2 f j p q := by
  simp only [deriv2, Pi.smul_apply, smul_eq_mul]; ring

lemma deriv2_sum {n k : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n → Fin k → Bool) → ZMod 2) (j : Fin n) (p q : Fin k) :
    deriv2 (∑ x ∈ s, f x) j p q = ∑ x ∈ s, deriv2 (f x) j p q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [deriv2]
  | insert a s ha ih => rw [Finset.sum_insert ha, deriv2_add, ih, Finset.sum_insert ha]

lemma deriv2_const {n k : ℕ} (c : ZMod 2) (j : Fin n) (p q : Fin k) :
    deriv2 (fun _ => c) j p q = 0 := by
  simp only [deriv2]; revert c; decide

lemma deriv2_coord {n k : ℕ} (j0 j : Fin n) (i0 p q : Fin k) :
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (x j0 i0)) j p q = 0 := by
  simp only [deriv2, updBit]
  by_cases h1 : j0 = j ∧ i0 = p <;> by_cases h2 : j0 = j ∧ i0 = q
  · have hpq : p = q := h1.2.symm.trans h2.2
    subst hpq; simp [h1, b2z]; decide
  · have hpq : p ≠ q := fun h => h2 ⟨h1.1, h1.2.trans h⟩
    have hqp : q ≠ p := Ne.symm hpq
    simp [h1, h2, hpq, hqp, b2z]; decide
  · have hpq : p ≠ q := fun h => h1 ⟨h2.1, h2.2.trans h.symm⟩
    have hqp : q ≠ p := Ne.symm hpq
    simp [h1, h2, hpq, hqp, b2z]; decide
  · simp [h1, h2, b2z]

lemma deriv2_readBit_ne_key {n k : ℕ} (hk : 0 < k) (col : Bool) (u : Fin k → Bool)
    (j0 j : Fin n) (i0 p q : Fin k) (hne : j0 ≠ j) :
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk col u (x j0) i0)) j p q = 0 := by
  simp only [deriv2]
  have h1 : updBit (fun _ _ => false) j p j0 = (fun _ => false) := by
    funext i; simp [updBit, hne]
  have h2 : updBit (fun _ _ => false) j q j0 = (fun _ => false) := by
    funext i; simp [updBit, hne]
  have h3 : updBit (updBit (fun _ _ => false) j p) j q j0 = (fun _ => false) := by
    funext i; simp [updBit, hne]
  rw [h1, h2, h3]
  generalize b2z (readBit k hk col u (fun _ => false) i0) = v
  revert v; decide

lemma deriv2_readBit_eq_key {n k : ℕ} (hk : 0 < k) (col : Bool) (u : Fin k → Bool)
    (j : Fin n) (i0 p q : Fin k) (hpq : p ≠ q) :
    let d := if col then 2 else 1
    let s := if col then 3 else 1
    let A := fun r : Fin k => b2z (wMix k hk d (wRot k hk s (singleBit k r)) (ix k hk (i0.val + 1)))
    let B := fun r : Fin k => b2z (wMix k hk d (wRot k hk s (singleBit k r)) (ix k hk (i0.val + 2)))
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk col u (x j) i0)) j p q =
      A p * B q + A q * B p := by
  intro d s A B
  simp only [deriv2]
  have hp : updBit (fun _ _ => false) j p j = singleBit k p := by
    funext r; simp [updBit, singleBit]
  have hq : updBit (fun _ _ => false) j q j = singleBit k q := by
    funext r; simp [updBit, singleBit]
  have hpq' : updBit (updBit (fun _ _ => false) j p) j q j = wAdd (singleBit k p) (singleBit k q) := by
    funext r; simp only [updBit, wAdd, singleBit]
    by_cases hrp : r = p <;> by_cases hrq : r = q
    · exact absurd (hrp.symm.trans hrq) hpq
    · simp [hrp, hrq]
    · simp [hrp, hrq]
    · simp [hrp, hrq]
  rw [hp, hq, hpq']
  have hrb_exp : ∀ x : Fin k → Bool,
      b2z (readBit k hk col u x i0) =
        b2z (wRot k hk (if col then 4 else 0) x i0) +
        b2z (wMix k hk d (wAdd u (wRot k hk s x)) i0) +
        (1 + b2z (wMix k hk d (wAdd u (wRot k hk s x)) (ix k hk (i0.val + 1)))) *
          b2z (wMix k hk d (wAdd u (wRot k hk s x)) (ix k hk (i0.val + 2))) := by
    intro x
    simp only [readBit, d, s, b2z_xor, b2z_and, b2z_not, add_assoc]
  rw [hrb_exp, hrb_exp, hrb_exp, hrb_exp]
  have hrot0 : ∀ s0 (r : Fin k), wRot k hk s0 (fun _ => false) r = false := by intro s0 r; rfl
  have hmix_lin : ∀ (idx : Fin k) (x : Fin k → Bool),
      b2z (wMix k hk d (wAdd u (wRot k hk s x)) idx) =
        b2z (wMix k hk d u idx) + b2z (wMix k hk d (wRot k hk s x) idx) := by
    intro idx x; rw [wMix_add, b2z_xor]
  simp_rw [hmix_lin]
  have hmix_sum : ∀ (idx : Fin k),
      b2z (wMix k hk d (wRot k hk s (wAdd (singleBit k p) (singleBit k q))) idx) =
        b2z (wMix k hk d (wRot k hk s (singleBit k p)) idx) +
          b2z (wMix k hk d (wRot k hk s (singleBit k q)) idx) := by
    intro idx
    have heq : wRot k hk s (wAdd (singleBit k p) (singleBit k q)) =
        wAdd (wRot k hk s (singleBit k p)) (wRot k hk s (singleBit k q)) := by funext r; rfl
    rw [heq, wMix_add, b2z_xor]
  have hmix_zero : ∀ (idx : Fin k),
      b2z (wMix k hk d (wRot k hk s (fun _ => false)) idx) = 0 := by
    intro idx
    have heq : wRot k hk s (fun _ => false) = (fun _ => false) := by funext r; rfl
    rw [heq, wMix_zero, b2z_false]
  have hrot4_sum :
      b2z (wRot k hk (if col then 4 else 0) (wAdd (singleBit k p) (singleBit k q)) i0) =
        b2z (wRot k hk (if col then 4 else 0) (singleBit k p) i0) +
          b2z (wRot k hk (if col then 4 else 0) (singleBit k q) i0) := by
    exact b2z_xor _ _
  rw [hrot0, b2z_false, hrot4_sum, hmix_zero, hmix_zero, hmix_zero, hmix_sum, hmix_sum, hmix_sum]
  change _ = A p * B q + A q * B p
  dsimp only [A, B]
  generalize b2z (wRot k hk (if col then 4 else 0) (singleBit k p) i0) = r4p
  generalize b2z (wRot k hk (if col then 4 else 0) (singleBit k q) i0) = r4q
  generalize b2z (wMix k hk d u i0) = u0
  generalize b2z (wMix k hk d u (ix k hk (i0.val + 1))) = u1
  generalize b2z (wMix k hk d u (ix k hk (i0.val + 2))) = u2
  generalize b2z (wMix k hk d (wRot k hk s (singleBit k p)) i0) = mp
  generalize b2z (wMix k hk d (wRot k hk s (singleBit k q)) i0) = mq
  generalize b2z (wMix k hk d (wRot k hk s (singleBit k p)) (ix k hk (i0.val + 1))) = ap
  generalize b2z (wMix k hk d (wRot k hk s (singleBit k q)) (ix k hk (i0.val + 1))) = aq
  generalize b2z (wMix k hk d (wRot k hk s (singleBit k p)) (ix k hk (i0.val + 2))) = bp
  generalize b2z (wMix k hk d (wRot k hk s (singleBit k q)) (ix k hk (i0.val + 2))) = bq
  have h2z : (2 : ZMod 2) = 0 := by decide
  have h4z : (4 : ZMod 2) = 0 := by decide
  apply sub_eq_zero.mp
  ring_nf
  simp [h2z, h4z]

lemma deriv2_readBit_indep_u {n k : ℕ} (hk : 0 < k) (col : Bool) (u v : Fin k → Bool)
    (j0 j : Fin n) (i0 p q : Fin k) (hpq : p ≠ q) :
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk col u (x j0) i0)) j p q =
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk col v (x j0) i0)) j p q := by
  by_cases hj : j0 = j
  · subst hj; rw [deriv2_readBit_eq_key hk col u j0 i0 p q hpq, deriv2_readBit_eq_key hk col v j0 i0 p q hpq]
  · rw [deriv2_readBit_ne_key hk col u j0 j i0 p q hj, deriv2_readBit_ne_key hk col v j0 j i0 p q hj]

lemma mix_rot_singleBit_eq (k : ℕ) (hk : 9 ≤ k) (d s : ℕ) (hd0 : 1 ≤ d) (hd : d ≤ 2) (hs : s ≤ 3)
    (r idx : Fin k) :
    have hk0 : 0 < k := by omega
    wMix k hk0 d (wRot k hk0 s (singleBit k r)) idx =
      decide (r.val = (idx.val + k - s - d) % k ∨
              r.val = (idx.val + k - s) % k ∨
              r.val = (idx.val + k - s + d) % k) := by
  have hk0 : 0 < k := by omega
  have hrlt := r.isLt; have hilt := idx.isLt
  have hd_mod : d % k = d := Nat.mod_eq_of_lt (by omega)
  have hs_mod : s % k = s := Nat.mod_eq_of_lt (by omega)
  have h1 : (ix k hk0 ((ix k hk0 (idx.val + k - d % k)).val + k - s % k)).val =
      (idx.val + k - s - d) % k := by
    simp only [ix, hd_mod, hs_mod]
    rw [mod_add_k_sub k (idx.val + k - d) s (by omega),
        mod_of_lt_three k _ (by omega), mod_of_lt_two k _ (by omega)]
    split_ifs <;> omega
  have h2 : (ix k hk0 (idx.val + k - s % k)).val = (idx.val + k - s) % k := by
    simp [ix, hs_mod]
  have h3 : (ix k hk0 ((ix k hk0 (idx.val + d)).val + k - s % k)).val =
      (idx.val + k - s + d) % k := by
    simp only [ix, hs_mod]
    rw [mod_add_k_sub k (idx.val + d) s (by omega),
        mod_of_lt_three k _ (by omega), mod_of_lt_three k _ (by omega)]
    split_ifs <;> omega
  simp only [wMix, wRot, singleBit, Fin.ext_iff, h1, h2, h3]
  have h12 : (idx.val + k - s - d) % k ≠ (idx.val + k - s) % k := by
    rw [mod_of_lt_three k _ (by omega), mod_of_lt_three k _ (by omega)]
    split_ifs <;> omega
  have h13 : (idx.val + k - s - d) % k ≠ (idx.val + k - s + d) % k := by
    rw [mod_of_lt_three k _ (by omega), mod_of_lt_three k _ (by omega)]
    split_ifs <;> omega
  have h23 : (idx.val + k - s) % k ≠ (idx.val + k - s + d) % k := by
    rw [mod_of_lt_three k _ (by omega), mod_of_lt_three k _ (by omega)]
    split_ifs <;> omega
  by_cases c1 : (idx.val + k - s - d) % k = r.val <;>
  by_cases c2 : (idx.val + k - s) % k = r.val <;>
  by_cases c3 : (idx.val + k - s + d) % k = r.val
  · exact absurd (c1.trans c2.symm) h12
  · exact absurd (c1.trans c2.symm) h12
  · exact absurd (c1.trans c3.symm) h13
  · simp [c1, c2, c3]
  · exact absurd (c2.trans c3.symm) h23
  · simp [c1, c2, c3]
  · simp [c1, c2, c3]
  · simp [c1, c2, c3, Ne.symm]

lemma mix_rot_shift (k : ℕ) (hk : 9 ≤ k) (d s : ℕ) (hd0 : 1 ≤ d) (hd : d ≤ 2) (hs : s ≤ 3)
    (a b : ℕ) :
    have hk0 : 0 < k := by omega
    wMix k hk0 d (wRot k hk0 s (singleBit k (ix k hk0 a))) (ix k hk0 b) =
      decide ((a + s + d) % k = b % k ∨ (a + s) % k = b % k ∨ (a + s) % k = (b + d) % k) := by
  dsimp only
  have hk0 : 0 < k := by omega
  have hbase := mix_rot_singleBit_eq k hk d s hd0 hd hs (ix k hk0 a) (ix k hk0 b)
  dsimp only at hbase
  rw [hbase]
  simp only [ix]
  have h1 : a % k = (b % k + k - s - d) % k ↔ (a + s + d) % k = b % k := by
    haveI : NeZero k := ⟨by omega⟩
    rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff']
    rw [show b % k + k - s - d = b % k + (k - s - d) by omega]
    push_cast
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  have h2 : a % k = (b % k + k - s) % k ↔ (a + s) % k = b % k := by
    haveI : NeZero k := ⟨by omega⟩
    rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff']
    rw [show b % k + k - s = b % k + (k - s) by omega]
    push_cast
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), ZMod.natCast_self]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  have h3 : a % k = (b % k + k - s + d) % k ↔ (a + s) % k = (b + d) % k := by
    haveI : NeZero k := ⟨by omega⟩
    rw [← ZMod.natCast_eq_natCast_iff', ← ZMod.natCast_eq_natCast_iff']
    rw [show b % k + k - s + d = b % k + (k - s) + d by omega]
    push_cast
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), ZMod.natCast_self]
    constructor <;> intro h
    · linear_combination h
    · linear_combination h
  simp only [h1, h2, h3]

lemma mod_eq_shift_iff (k : ℕ) (hk : 9 ≤ k) (i i0 : Fin k) (c : ℕ) (hc : c < k) :
    (i.val + c) % k = i0.val ↔ (i.val + c = i0.val ∨ i.val + c = i0.val + k) := by
  have hi := i.isLt; have hi0 := i0.isLt
  rw [mod_of_lt_two k (i.val + c) (by omega)]
  split_ifs <;> omega

lemma mix_rot_shift_eq_false (k : ℕ) (hk : 9 ≤ k) (d s : ℕ) (hd0 : 1 ≤ d) (hd : d ≤ 2) (hs : s ≤ 3)
    (a b : ℕ) (ha : a < 3 * k) (hb : b < 3 * k)
    (h1 : (a + s + d) % k ≠ b % k) (h2 : (a + s) % k ≠ b % k) (h3 : (a + s) % k ≠ (b + d) % k) :
    have hk0 : 0 < k := by omega
    wMix k hk0 d (wRot k hk0 s (singleBit k (ix k hk0 a))) (ix k hk0 b) = false := by
  dsimp only
  have hm := mix_rot_shift k hk d s hd0 hd hs a b
  dsimp only at hm
  rw [hm]; simp [h1, h2, h3]

lemma mod_ne_of_lt3 (k a b : ℕ) (ha : a < 3 * k) (hb : b < 3 * k)
    (h : a ≠ b ∧ a ≠ b + k ∧ a ≠ b + 2 * k ∧ b ≠ a + k ∧ b ≠ a + 2 * k) : a % k ≠ b % k := by
  rw [mod_of_lt_three k a ha, mod_of_lt_three k b hb]
  split_ifs <;> omega

lemma mod_eq_imp_diff (k a b : ℕ) (ha : a < 3 * k) (hb : b < 3 * k) (h : a % k = b % k) :
    a = b ∨ a = b + k ∨ a = b + 2 * k ∨ b = a + k ∨ b = a + 2 * k := by
  rw [mod_of_lt_three k a ha, mod_of_lt_three k b hb] at h
  split_ifs at h <;> omega

lemma deriv2_dist5 {n k : ℕ} (hk : 9 ≤ k) (h3 : 3 ∣ k) (col : Bool) (u : Fin k → Bool)
    (j : Fin n) (i0 i : Fin k) :
    have hk0 : 0 < k := by omega
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk0 col u (x j) i0))
      j (ix k hk0 (i.val + k - 4)) (ix k hk0 (i.val + 1)) =
      if col = true ∧ i0 = i then 1 else 0 := by
  dsimp only
  have hk0 : 0 < k := by omega
  have hne10 : k ≠ 10 := by omega
  have hi := i.isLt; have hi0 := i0.isLt
  have hpq : ix k hk0 (i.val + k - 4) ≠ ix k hk0 (i.val + 1) := by
    intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
    exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
  rw [deriv2_readBit_eq_key hk0 col u j i0 _ _ hpq]
  cases col
  · simp only [Bool.false_eq_true, ↓reduceIte, false_and]
    have hms := fun a b => mix_rot_shift k hk 1 1 (by omega) (by omega) (by omega) a b
    dsimp only at hms
    have hAB : ∀ (p1 p2 : ℕ), p1 = i.val + k - 4 ∨ p1 = i.val + 1 →
        p2 = i.val + k - 4 ∨ p2 = i.val + 1 → p1 ≠ p2 →
        b2z (wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 p1))) (ix k hk0 (i0.val + 1))) *
        b2z (wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 p2))) (ix k hk0 (i0.val + 2))) = 0 := by
      intro p1 p2 hp1 hp2 hne
      rw [hms, hms]
      by_cases h1 : (p1 + 1 + 1) % k = (i0.val + 1) % k ∨ (p1 + 1) % k = (i0.val + 1) % k ∨
                    (p1 + 1) % k = (i0.val + 1 + 1) % k
      · have h2 : ¬((p2 + 1 + 1) % k = (i0.val + 2) % k ∨ (p2 + 1) % k = (i0.val + 2) % k ∨
                    (p2 + 1) % k = (i0.val + 2 + 1) % k) := by
          intro h2
          rcases hp1 with rfl | rfl <;> rcases hp2 with rfl | rfl
          · exact hne rfl
          · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            · have d1 := mod_eq_imp_diff k _ _ (by omega) (by omega) h1
              have d2 := mod_eq_imp_diff k _ _ (by omega) (by omega) h2
              omega
          · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            · have d1 := mod_eq_imp_diff k _ _ (by omega) (by omega) h1
              have d2 := mod_eq_imp_diff k _ _ (by omega) (by omega) h2
              omega
          · exact hne rfl
        simp [h2, b2z]
      · simp [h1, b2z]
    rw [hAB _ _ (Or.inl rfl) (Or.inr rfl) (by omega), hAB _ _ (Or.inr rfl) (Or.inl rfl) (by omega), add_zero]
  · simp only [↓reduceIte, true_and]
    have hms := fun a b => mix_rot_shift k hk 2 3 (by omega) (by omega) (by omega) a b
    dsimp only at hms
    by_cases heq : i0 = i
    · subst heq; simp only [↓reduceIte]
      have h1 : wMix k hk0 2 (wRot k hk0 3 (singleBit k (ix k hk0 (i0.val + k - 4)))) (ix k hk0 (i0.val + 1)) = true := by
        rw [hms]; apply decide_eq_true; left
        rw [show i0.val + k - 4 + 3 + 2 = (i0.val + 1) + k by omega, Nat.add_mod_right]
      have h2 : wMix k hk0 2 (wRot k hk0 3 (singleBit k (ix k hk0 (i0.val + 1)))) (ix k hk0 (i0.val + 2)) = true := by
        rw [hms]; apply decide_eq_true; right; right; congr 1
      have h3 : wMix k hk0 2 (wRot k hk0 3 (singleBit k (ix k hk0 (i0.val + 1)))) (ix k hk0 (i0.val + 1)) = false := by
        apply mix_rot_shift_eq_false k hk 2 3 (by omega) (by omega) (by omega) _ _ (by omega) (by omega) <;>
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega)
      rw [h1, h2, h3]; simp [b2z]
    · have hne_val : i0.val ≠ i.val := fun h => heq (Fin.ext h)
      simp only [heq, ↓reduceIte]
      have hAB : ∀ (p1 p2 : ℕ), p1 = i.val + k - 4 ∨ p1 = i.val + 1 →
          p2 = i.val + k - 4 ∨ p2 = i.val + 1 → p1 ≠ p2 →
          b2z (wMix k hk0 2 (wRot k hk0 3 (singleBit k (ix k hk0 p1))) (ix k hk0 (i0.val + 1))) *
          b2z (wMix k hk0 2 (wRot k hk0 3 (singleBit k (ix k hk0 p2))) (ix k hk0 (i0.val + 2))) = 0 := by
        intro p1 p2 hp1 hp2 hne
        rw [hms, hms]
        by_cases h1 : (p1 + 3 + 2) % k = (i0.val + 1) % k ∨ (p1 + 3) % k = (i0.val + 1) % k ∨
                      (p1 + 3) % k = (i0.val + 1 + 2) % k
        · have h2 : ¬((p2 + 3 + 2) % k = (i0.val + 2) % k ∨ (p2 + 3) % k = (i0.val + 2) % k ∨
                      (p2 + 3) % k = (i0.val + 2 + 2) % k) := by
            intro h2
            rcases hp1 with rfl | rfl <;> rcases hp2 with rfl | rfl
            · exact hne rfl
            · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
              · have d1 := mod_eq_imp_diff k _ _ (by omega) (by omega) h1
                have d2 := mod_eq_imp_diff k _ _ (by omega) (by omega) h2
                omega
            · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
              · have d1 := mod_eq_imp_diff k _ _ (by omega) (by omega) h1
                have d2 := mod_eq_imp_diff k _ _ (by omega) (by omega) h2
                omega
            · exact hne rfl
          simp [h2, b2z]
        · simp [h1, b2z]
      rw [hAB _ _ (Or.inl rfl) (Or.inr rfl) (by omega), hAB _ _ (Or.inr rfl) (Or.inl rfl) (by omega), add_zero]

lemma deriv2_dist3_row {n k : ℕ} (hk : 9 ≤ k) (u : Fin k → Bool)
    (j : Fin n) (i0 i : Fin k) :
    have hk0 : 0 < k := by omega
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk0 false u (x j) i0))
      j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) =
      if i0 = i then 1 else 0 := by
  dsimp only
  have hk0 : 0 < k := by omega
  have hi := i.isLt; have hi0 := i0.isLt
  have hpq : ix k hk0 (i.val + k - 1) ≠ ix k hk0 (i.val + 2) := by
    intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
    exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
  rw [deriv2_readBit_eq_key hk0 false u j i0 _ _ hpq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hms := fun a b => mix_rot_shift k hk 1 1 (by omega) (by omega) (by omega) a b
  dsimp only at hms
  by_cases heq : i0 = i
  · subst heq; simp only [↓reduceIte]
    have h1 : wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 (i0.val + k - 1)))) (ix k hk0 (i0.val + 1)) = true := by
      rw [hms]; apply decide_eq_true; left
      rw [show i0.val + k - 1 + 1 + 1 = (i0.val + 1) + k by omega, Nat.add_mod_right]
    have h2 : wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 (i0.val + 2)))) (ix k hk0 (i0.val + 2)) = true := by
      rw [hms]; apply decide_eq_true; right; right; congr 1
    have h3 : wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 (i0.val + 2)))) (ix k hk0 (i0.val + 1)) = false := by
      apply mix_rot_shift_eq_false k hk 1 1 (by omega) (by omega) (by omega) _ _ (by omega) (by omega) <;>
      exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega)
    rw [h1, h2, h3]; simp [b2z]
  · have hne_val : i0.val ≠ i.val := fun h => heq (Fin.ext h)
    simp only [heq, ↓reduceIte]
    have hAB : ∀ (p1 p2 : ℕ), p1 = i.val + k - 1 ∨ p1 = i.val + 2 →
        p2 = i.val + k - 1 ∨ p2 = i.val + 2 → p1 ≠ p2 →
        b2z (wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 p1))) (ix k hk0 (i0.val + 1))) *
        b2z (wMix k hk0 1 (wRot k hk0 1 (singleBit k (ix k hk0 p2))) (ix k hk0 (i0.val + 2))) = 0 := by
      intro p1 p2 hp1 hp2 hne
      rw [hms, hms]
      by_cases h1 : (p1 + 1 + 1) % k = (i0.val + 1) % k ∨ (p1 + 1) % k = (i0.val + 1) % k ∨
                    (p1 + 1) % k = (i0.val + 1 + 1) % k
      · have h2 : ¬((p2 + 1 + 1) % k = (i0.val + 2) % k ∨ (p2 + 1) % k = (i0.val + 2) % k ∨
                    (p2 + 1) % k = (i0.val + 2 + 1) % k) := by
          intro h2
          rcases hp1 with rfl | rfl <;> rcases hp2 with rfl | rfl
          · exact hne rfl
          · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            · have d1 := mod_eq_imp_diff k _ _ (by omega) (by omega) h1
              have d2 := mod_eq_imp_diff k _ _ (by omega) (by omega) h2
              omega
          · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
            · have d1 := mod_eq_imp_diff k _ _ (by omega) (by omega) h1
              have d2 := mod_eq_imp_diff k _ _ (by omega) (by omega) h2
              omega
          · exact hne rfl
        simp [h2, b2z]
      · simp [h1, b2z]
    rw [hAB _ _ (Or.inl rfl) (Or.inr rfl) (by omega), hAB _ _ (Or.inr rfl) (Or.inl rfl) (by omega), add_zero]

lemma affine_gate_eval (g : Gate) (hlen : g.inputs.length ≤ 2) (hnl : isNonlin g = false) :
    ∃ (c0 c1 c2 : ZMod 2),
      (g.inputs.length = 0 → c1 = 0 ∧ c2 = 0) ∧
      (g.inputs.length = 1 → c2 = 0) ∧
      ∀ (w : List Bool),
        b2z (g.op.eval (g.inputs.map fun i => w.getD i false)) =
          c0 + c1 * b2z (w.getD (g.inputs.getD 0 0) false) +
            c2 * b2z (w.getD (g.inputs.getD 1 0) false) := by
  rcases g with ⟨op, ins⟩
  match ins with
  | [] =>
    refine ⟨b2z (op.eval []), 0, 0, fun _ => ⟨rfl, rfl⟩, fun h => by simp at h, fun w => by simp⟩
  | [i0] =>
    refine ⟨b2z (op.eval [false]), b2z (op.eval [false]) + b2z (op.eval [true]), 0,
      fun h => by simp at h, fun _ => rfl, fun w => ?_⟩
    simp only [List.map, List.getD_cons_zero, zero_mul, add_zero]
    cases w.getD i0 false <;> cases op.eval [false] <;> cases op.eval [true] <;> decide
  | [i0, i1] =>
    simp only [isNonlin, List.length_cons, List.length_nil, beq_self_eq_true, Bool.true_and] at hnl
    have haff : b2z (op.eval [false, false]) + b2z (op.eval [false, true]) +
        b2z (op.eval [true, false]) + b2z (op.eval [true, true]) = 0 := by
      have := congrArg b2z hnl
      simp only [b2z_xor, b2z_false] at this
      rw [← this]; ring
    refine ⟨b2z (op.eval [false, false]),
            b2z (op.eval [false, false]) + b2z (op.eval [true, false]),
            b2z (op.eval [false, false]) + b2z (op.eval [false, true]),
            fun h => by simp at h, fun h => by simp at h, fun w => ?_⟩
    simp only [List.map, List.getD_cons_zero, List.getD_cons_succ]
    cases w.getD i0 false <;> cases w.getD i1 false <;>
    cases hff : op.eval [false, false] <;> cases hft : op.eval [false, true] <;>
    cases htf : op.eval [true, false] <;> cases htt : op.eval [true, true] <;>
    simp_all [b2z] <;> decide
  | _ :: _ :: _ :: _ => simp at hlen

lemma card_filter_fin_eq_countP {α : Type} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun j : Fin l.length => p l[j.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.countP_cons]
    rw [Fin.card_filter_univ_succ]
    simp only [Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ, ih]
    cases p a <;> simp

def kerWord (k : ℕ) (c : Fin 2 → Bool) (i : Fin k) : Bool :=
  if i.val % 3 = 0 then c 0 else if i.val % 3 = 1 then c 1 else xor (c 0) (c 1)

lemma wMix_kerWord (k : ℕ) (hk : 9 ≤ k) (h3 : 3 ∣ k) (d : ℕ) (hd : d = 1 ∨ d = 2)
    (s : ℕ) (c : Fin 2 → Bool) (i : Fin k) :
    have hk0 : 0 < k := by omega
    wMix k hk0 d (wRot k hk0 s (kerWord k c)) i = false := by
  have hk0 : 0 < k := by omega
  have hd_mod : d % k = d := Nat.mod_eq_of_lt (by omega)
  have hs_lt : s % k < k := Nat.mod_lt _ hk0
  have hmod3 : ∀ a : ℕ, (a % k) % 3 = a % 3 := fun a => Nat.mod_mod_of_dvd a h3
  simp only [wMix, wRot, kerWord, ix, hd_mod, hmod3]
  have hr : ((i.val + k - d) % k + k - s % k) % 3 = (i.val + 3 * k - s % k - d) % 3 := by
    rw [← hmod3 ((i.val + k - d) % k + k - s % k),
        mod_add_k_sub k (i.val + k - d) (s % k) (by omega), hmod3]
    omega
  have h0 : (i.val + k - s % k) % 3 = (i.val + 3 * k - s % k) % 3 := by omega
  have h1 : ((i.val + d) % k + k - s % k) % 3 = (i.val + 3 * k - s % k + d) % 3 := by
    rw [← hmod3 ((i.val + d) % k + k - s % k),
        mod_add_k_sub k (i.val + d) (s % k) (by omega), hmod3]
    omega
  rw [hr, h0, h1]
  have hm : (i.val + 3 * k - s % k) % 3 = 0 ∨ (i.val + 3 * k - s % k) % 3 = 1 ∨
      (i.val + 3 * k - s % k) % 3 = 2 := by omega
  rcases hd with rfl | rfl <;> rcases hm with h | h | h <;>
  · have hm1 : (i.val + 3 * k - s % k - 1) % 3 = ((i.val + 3 * k - s % k) % 3 + 2) % 3 := by omega
    have hm2 : (i.val + 3 * k - s % k - 2) % 3 = ((i.val + 3 * k - s % k) % 3 + 1) % 3 := by omega
    have hp1 : (i.val + 3 * k - s % k + 1) % 3 = ((i.val + 3 * k - s % k) % 3 + 1) % 3 := by omega
    have hp2 : (i.val + 3 * k - s % k + 2) % 3 = ((i.val + 3 * k - s % k) % 3 + 2) % 3 := by omega
    simp only [h, hm1, hm2, hp1, hp2]
    cases c 0 <;> cases c 1 <;> rfl

lemma readBit_on_kerWord (k : ℕ) (hk : 9 ≤ k) (h3 : 3 ∣ k) (col : Bool) (u : Fin k → Bool)
    (c : Fin 2 → Bool) (i : Fin k) :
    have hk0 : 0 < k := by omega
    b2z (readBit k hk0 col u (kerWord k c) i) =
      b2z (wRot k hk0 (if col then 4 else 0) (kerWord k c) i) +
      b2z (readBit k hk0 col u (fun _ => false) i) := by
  have hk0 : 0 < k := by omega
  have hd : (if col then 2 else 1) = 1 ∨ (if col then 2 else 1) = 2 := by cases col <;> simp
  have hmk : ∀ idx : Fin k,
      wMix k hk0 (if col then 2 else 1) (wAdd u (wRot k hk0 (if col then 3 else 1) (kerWord k c))) idx =
        wMix k hk0 (if col then 2 else 1) u idx := by
    intro idx
    rw [wMix_add, wMix_kerWord k hk h3 _ hd, Bool.xor_false]
  have hmk0 : ∀ idx : Fin k,
      wMix k hk0 (if col then 2 else 1) (wAdd u (wRot k hk0 (if col then 3 else 1) (fun _ => false))) idx =
        wMix k hk0 (if col then 2 else 1) u idx := by
    intro idx
    have hr : wRot k hk0 (if col then 3 else 1) (fun _ => false) = (fun _ => false) := by funext r; rfl
    rw [hr, wMix_add, wMix_zero, Bool.xor_false]
  have hr0 : wRot k hk0 (if col then 4 else 0) (fun _ => false) i = false := rfl
  simp only [readBit, hmk, hmk0, hr0, Bool.false_xor, b2z_xor]

lemma lower_ge9_div3 (k : ℕ) (hk : 9 ≤ k) (h3 : 3 ∣ k) (n b t : ℕ)
    (h : ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
        (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
        (side : (Fin n → Fin k → Bool) → Fin b → Bool) (C : Circuit)
        (tap : Fin n → Fin k → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k (by omega) (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i) : n * 2 ≤ b + t := by
  classical
  have hk0 : 0 < k := by omega
  obtain ⟨a, bank, key, name, site, side, C, tap, ⟨hRB, hFan⟩, hNL, hTapLt, hDec⟩ := h
  let U := Fin n → Fin k → Bool
  let dataOf : U → List Bool := fun x =>
    List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l)) ++
      List.ofFn (side x)
  let wireFn : ℕ → (U → ZMod 2) := fun w x => b2z ((C.wires (dataOf x)).getD w false)
  let rbFn : Fin a → (U → ZMod 2) := fun l x =>
    b2z (readBit k hk0 (bank l) (name l) (x (key l)) (site l))
  let constOne : U → ZMod 2 := fun _ => 1
  let B : Submodule (ZMod 2) (U → ZMod 2) :=
    Submodule.span (ZMod 2) (insert constOne (Set.range rbFn))
  let sideSet : Finset (U → ZMod 2) :=
    Finset.univ.image (fun r : Fin b => fun x : U => b2z (side x r))
  let nlIdx : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j : Fin C.gates.length => isNonlin C.gates[j.val] = true)
  let nlSet : Finset (U → ZMod 2) :=
    nlIdx.image (fun j : Fin C.gates.length => wireFn (a + b + j.val))
  let E : Submodule (ZMod 2) (U → ZMod 2) :=
    Submodule.span (ZMod 2) ((sideSet ∪ nlSet : Finset (U → ZMod 2)) : Set (U → ZMod 2))
  have hE_rank : Module.finrank (ZMod 2) E ≤ b + t := by
    have h1 : Module.finrank (ZMod 2) E ≤ (sideSet ∪ nlSet).card := by
      simpa [E] using finrank_span_le_card ((sideSet ∪ nlSet : Finset (U → ZMod 2)) : Set (U → ZMod 2))
    have h2 : (sideSet ∪ nlSet).card ≤ sideSet.card + nlSet.card := Finset.card_union_le _ _
    have h3s : sideSet.card ≤ b := by
      calc sideSet.card ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
        _ = b := by simp
    have h4nl : nlSet.card ≤ t := by
      calc nlSet.card ≤ nlIdx.card := Finset.card_image_le
        _ = C.gates.countP isNonlin := card_filter_fin_eq_countP C.gates isNonlin
        _ ≤ t := hNL
    omega
  have hWire_mem : ∀ w < a + b + C.gates.length, wireFn w ∈ B ⊔ E := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      have hdata_len : ∀ x, (dataOf x).length = a + b := by
        intro x; simp [dataOf, List.length_append, List.length_ofFn]
      by_cases hlt_a : w < a
      · have heq : wireFn w = rbFn ⟨w, hlt_a⟩ := by
          funext x
          simp only [wireFn, wiresFrom_eq]
          rw [getD_wiresFrom_lt _ (dataOf x) w (by rw [hdata_len]; omega)]
          simp only [dataOf]
          rw [List.getD_append _ _ _ _ (by simp [hlt_a]), getD_ofFn_lt _ _ w hlt_a]
        rw [heq]
        exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨w, hlt_a⟩, rfl⟩))
      · by_cases hlt_ab : w < a + b
        · have heq : wireFn w = (fun x : U => b2z (side x ⟨w - a, by omega⟩)) := by
            funext x
            simp only [wireFn, wiresFrom_eq]
            rw [getD_wiresFrom_lt _ (dataOf x) w (by rw [hdata_len]; omega)]
            simp only [dataOf]
            rw [List.getD_append_right _ _ _ _ (by simp; omega)]
            simp only [List.length_ofFn]
            rw [getD_ofFn_lt _ _ (w - a) (by omega)]
          rw [heq]
          apply Submodule.mem_sup_right
          apply Submodule.subset_span
          exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨w - a, by omega⟩, Finset.mem_univ _, rfl⟩))
        · set j : ℕ := w - (a + b)
          have hj : j < C.gates.length := by omega
          have hw_eq : w = a + b + j := by omega
          by_cases hnlj : isNonlin C.gates[j] = true
          · apply Submodule.mem_sup_right
            apply Submodule.subset_span
            rw [hw_eq]
            exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp [nlIdx, hnlj], rfl⟩))
          · have hnlj' : isNonlin C.gates[j] = false := by cases h' : isNonlin C.gates[j] <;> simp_all
            obtain ⟨c0, c1, c2, hlen0, hlen1, haff⟩ := affine_gate_eval C.gates[j] (hFan _ (List.getElem_mem hj)) hnlj'
            have hrb_j : ∀ idx ∈ C.gates[j].inputs, idx < w := by
              intro idx hidx
              have := hRB j hj idx
              simp only [NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
                Option.getD_some] at this
              have := this hidx
              omega
            let f1 : U → ZMod 2 :=
              if 0 < C.gates[j].inputs.length then wireFn (C.gates[j].inputs.getD 0 0) else 0
            let f2 : U → ZMod 2 :=
              if 1 < C.gates[j].inputs.length then wireFn (C.gates[j].inputs.getD 1 0) else 0
            have hf1_mem : f1 ∈ B ⊔ E := by
              dsimp only [f1]
              split_ifs with h0
              · have hmem : C.gates[j].inputs.getD 0 0 ∈ C.gates[j].inputs := by
                  rw [List.getD_eq_getElem _ _ h0]; exact List.getElem_mem h0
                exact ih _ (hrb_j _ hmem) (by have := hrb_j _ hmem; omega)
              · exact Submodule.zero_mem _
            have hf2_mem : f2 ∈ B ⊔ E := by
              dsimp only [f2]
              split_ifs with h1
              · have hmem : C.gates[j].inputs.getD 1 0 ∈ C.gates[j].inputs := by
                  rw [List.getD_eq_getElem _ _ h1]; exact List.getElem_mem h1
                exact ih _ (hrb_j _ hmem) (by have := hrb_j _ hmem; omega)
              · exact Submodule.zero_mem _
            have hconst_mem : constOne ∈ B ⊔ E :=
              Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert _ _))
            have heq : wireFn w = c0 • constOne + c1 • f1 + c2 • f2 := by
              funext x
              have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
                simpa using (List.take_append_getElem_cons_drop hj).symm
              have hwi : (C.wires (dataOf x)).getD w false =
                  C.gates[j].op.eval (C.gates[j].inputs.map fun idx =>
                    (wiresFrom (C.gates.take j) (dataOf x)).getD idx false) := by
                conv_lhs => rw [wiresFrom_eq, hsplit, wiresFrom_append, wiresFrom_cons]
                have hlen1' : (wiresFrom (C.gates.take j) (dataOf x)).length = w := by
                  rw [length_wiresFrom, hdata_len, List.length_take_of_le (by omega)]; omega
                rw [getD_wiresFrom_lt _ _ w (by simp [hlen1'])]
                rw [← hlen1', getD_snoc_self]
              have hmap : ∀ idx ∈ C.gates[j].inputs,
                  (wiresFrom (C.gates.take j) (dataOf x)).getD idx false =
                    (C.wires (dataOf x)).getD idx false := by
                intro idx hidx
                have hlt_w := hrb_j idx hidx
                conv_rhs => rw [wiresFrom_eq, hsplit, wiresFrom_append]
                have hlen1' : (wiresFrom (C.gates.take j) (dataOf x)).length = w := by
                  rw [length_wiresFrom, hdata_len, List.length_take_of_le (by omega)]; omega
                exact (getD_wiresFrom_lt _ _ idx (by omega)).symm
              have hev2 := haff (wiresFrom (C.gates.take j) (dataOf x))
              simp only [wireFn, hwi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, constOne, mul_one]
              rw [hev2]
              congr 1
              · congr 1
                dsimp only [f1]
                split_ifs with h0
                · have hmem : C.gates[j].inputs.getD 0 0 ∈ C.gates[j].inputs := by
                    rw [List.getD_eq_getElem _ _ h0]; exact List.getElem_mem h0
                  rw [hmap _ hmem]
                · have hc1 : c1 = 0 := (hlen0 (by omega)).1
                  simp [hc1]
              · dsimp only [f2]
                split_ifs with h1
                · have hmem : C.gates[j].inputs.getD 1 0 ∈ C.gates[j].inputs := by
                    rw [List.getD_eq_getElem _ _ h1]; exact List.getElem_mem h1
                  rw [hmap _ hmem]
                · have hlen_le1 : C.gates[j].inputs.length = 0 ∨ C.gates[j].inputs.length = 1 := by omega
                  have hc2 : c2 = 0 := by
                    rcases hlen_le1 with h0 | h1'
                    · exact (hlen0 h0).2
                    · exact hlen1 h1'
                  simp [hc2]
            rw [heq]
            exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hconst_mem)
              (Submodule.smul_mem _ _ hf1_mem)) (Submodule.smul_mem _ _ hf2_mem)

  let coordFn : Fin n × Fin 2 → (U → ZMod 2) := fun p x => b2z (x p.1 ⟨p.2.val, by omega⟩)
  let A : Submodule (ZMod 2) (U → ZMod 2) := Submodule.span (ZMod 2) (Set.range coordFn)
  have hA_le : A ≤ B ⊔ E := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨j, r⟩, rfl⟩
    have heq : coordFn (j, r) = wireFn (tap j ⟨r.val, by omega⟩) := by
      funext x
      simp only [coordFn, wireFn, dataOf]
      rw [hDec x j ⟨r.val, by omega⟩]
    rw [heq]
    exact hWire_mem _ (hTapLt j ⟨r.val, by omega⟩)

  let res : (U → ZMod 2) →ₗ[ZMod 2] ((Fin n → Fin 2 → Bool) → ZMod 2) :=
    { toFun := fun f c => f (fun j => kerWord k (c j))
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl }

  have hAB_ker : ∀ f ∈ A ⊓ B, res f = 0 := by
    intro f ⟨hfA, hfB⟩
    have hf0 : f (fun _ _ => false) = 0 := by
      refine Submodule.span_induction (p := fun g _ => g (fun _ _ => false) = 0) ?_ ?_ ?_ ?_ hfA
      · rintro _ ⟨p, rfl⟩; rfl
      · rfl
      · intro x y _ _ hx hy; simp [hx, hy]
      · intro c x _ hx; simp [hx]
    have hf_d2 : ∀ j p q, deriv2 f j p q = 0 := by
      intro j p q
      refine Submodule.span_induction (p := fun g _ => deriv2 g j p q = 0) ?_ ?_ ?_ ?_ hfA
      · rintro _ ⟨⟨j0, r⟩, rfl⟩; exact deriv2_coord j0 j ⟨r.val, by omega⟩ p q
      · simp [deriv2]
      · intro x y _ _ hx hy; rw [deriv2_add, hx, hy, add_zero]
      · intro c x _ hx; rw [deriv2_smul, hx, mul_zero]

    have hfB' : ∃ (c0 : ZMod 2) (coeff : Fin a → ZMod 2),
        f = c0 • constOne + ∑ l : Fin a, coeff l • rbFn l := by
      have hfB0 : f ∈ Submodule.span (ZMod 2) (insert constOne (Set.range rbFn)) := hfB
      rw [Submodule.mem_span_insert] at hfB0
      obtain ⟨c0, g, hg, rfl⟩ := hfB0
      have hg' : g ∈ Submodule.span (ZMod 2) (Set.range rbFn) := hg
      rw [Submodule.mem_span_range_iff_exists_fun] at hg'
      obtain ⟨coeff, rfl⟩ := hg'
      exact ⟨c0, coeff, rfl⟩
    obtain ⟨c0, coeff, hf_eq⟩ := hfB'

    have hcol_zero : ∀ (j : Fin n) (i : Fin k),
        ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j ∧ site l = i), coeff l = 0 := by
      intro j i
      have hd := hf_d2 j (ix k hk0 (i.val + k - 4)) (ix k hk0 (i.val + 1))
      rw [hf_eq, deriv2_add, deriv2_smul, deriv2_const, mul_zero, zero_add, deriv2_sum] at hd
      have hterm : ∀ l : Fin a,
          deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 4)) (ix k hk0 (i.val + 1)) =
            if bank l = true ∧ key l = j ∧ site l = i then coeff l else 0 := by
        intro l
        rw [deriv2_smul]
        by_cases hkj : key l = j
        · have hrb_eq : rbFn l = (fun x : U => b2z (readBit k hk0 (bank l) (name l) (x j) (site l))) := by
            funext x; simp [rbFn, hkj]
          rw [hrb_eq, deriv2_dist5 hk h3 (bank l) (name l) j (site l) i]
          by_cases hc : bank l = true ∧ site l = i
          · simp [hc, hkj]
          · simp [hc, hkj]
        · rw [deriv2_readBit_ne_key hk0 (bank l) (name l) (key l) j (site l) _ _ hkj, mul_zero]
          simp [hkj]
      simp_rw [hterm] at hd
      simpa [Finset.sum_filter] using hd

    have hrow_zero : ∀ (j : Fin n) (i : Fin k),
        ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false ∧ key l = j ∧ site l = i), coeff l = 0 := by
      intro j i
      have hpq : ix k hk0 (i.val + k - 1) ≠ ix k hk0 (i.val + 2) := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
        have hi := i.isLt
        rw [mod_of_lt_two k _ (by omega), mod_of_lt_two k _ (by omega)] at h
        split_ifs at h <;> omega
      have hd := hf_d2 j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2))
      rw [hf_eq, deriv2_add, deriv2_smul, deriv2_const, mul_zero, zero_add, deriv2_sum] at hd
      have hsplit_col :
          ∑ l : Fin a, deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) =
          (∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true),
            deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2))) +
          (∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false),
            deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2))) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin a => bank l = true)]
        congr 1
      rw [hsplit_col] at hd
      have hcol_part :
          ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true),
            deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) = 0 := by
        have hfiber :
            ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true),
              deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) =
            ∑ p : Fin n × Fin k,
              ∑ l ∈ (Finset.univ.filter (fun l : Fin a => bank l = true)).filter (fun l => (key l, site l) = p),
                deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) :=
          (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
        rw [hfiber]
        apply Finset.sum_eq_zero
        rintro ⟨j0, i0⟩ _
        have hval : ∀ l ∈ (Finset.univ.filter (fun l : Fin a => bank l = true)).filter (fun l => (key l, site l) = (j0, i0)),
            deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) =
              coeff l * deriv2 (fun x : U => b2z (readBit k hk0 true (fun _ => false) (x j0) i0))
                j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hl
          rcases hl with ⟨hb, hkj, hsi⟩
          rw [deriv2_smul]
          congr 1
          have hrb_eq : rbFn l = (fun x : U => b2z (readBit k hk0 true (name l) (x j0) i0)) := by
            funext x; simp [rbFn, hb, hkj, hsi]
          rw [hrb_eq]
          exact deriv2_readBit_indep_u hk0 true (name l) (fun _ => false) j0 j i0 _ _ hpq
        rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
        have hfilt : (Finset.univ.filter (fun l : Fin a => bank l = true)).filter (fun l => (key l, site l) = (j0, i0)) =
            Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j0 ∧ site l = i0) := by
          ext l; simp [and_assoc]
        rw [hfilt, hcol_zero j0 i0, zero_mul]
      rw [hcol_part, zero_add] at hd
      have hterm : ∀ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false),
          deriv2 (coeff l • rbFn l) j (ix k hk0 (i.val + k - 1)) (ix k hk0 (i.val + 2)) =
            if key l = j ∧ site l = i then coeff l else 0 := by
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
        rw [deriv2_smul]
        by_cases hkj : key l = j
        · have hrb_eq : rbFn l = (fun x : U => b2z (readBit k hk0 false (name l) (x j) (site l))) := by
            funext x; simp [rbFn, hl, hkj]
          rw [hrb_eq, deriv2_dist3_row hk (name l) j (site l) i]
          by_cases hsi : site l = i <;> simp [hkj, hsi]
        · rw [deriv2_readBit_ne_key hk0 (bank l) (name l) (key l) j (site l) _ _ hkj, mul_zero]
          simp [hkj]
      rw [Finset.sum_congr rfl hterm] at hd
      have hfilt2 :
          (∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false), if key l = j ∧ site l = i then coeff l else 0) =
          ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false ∧ key l = j ∧ site l = i), coeff l := by
        rw [Finset.sum_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro l _
        by_cases h1 : bank l = false <;> by_cases h2 : key l = j ∧ site l = i <;> simp [h1, h2]
      rw [← hfilt2]
      simpa using hd

    funext c
    simp only [res, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply]
    have hdiff : f (fun j => kerWord k (c j)) = f (fun _ _ => false) := by
      rw [hf_eq]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, constOne]
      have hsum_eq :
          ∑ l : Fin a, coeff l * rbFn l (fun j => kerWord k (c j)) =
            (∑ l : Fin a, coeff l * b2z (wRot k hk0 (if bank l then 4 else 0) (kerWord k (c (key l))) (site l))) +
            ∑ l : Fin a, coeff l * rbFn l (fun _ _ => false) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro l _
        simp only [rbFn]
        rw [readBit_on_kerWord k hk h3 (bank l) (name l) (c (key l)) (site l), mul_add]
      rw [hsum_eq]
      have hrot_zero :
          ∑ l : Fin a, coeff l * b2z (wRot k hk0 (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) = 0 := by
        have hfiber :
            ∑ l : Fin a, coeff l * b2z (wRot k hk0 (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) =
            ∑ p : Bool × Fin n × Fin k,
              ∑ l ∈ Finset.univ.filter (fun l : Fin a => (bank l, key l, site l) = p),
                coeff l * b2z (wRot k hk0 (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) :=
          (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
        rw [hfiber]
        apply Finset.sum_eq_zero
        rintro ⟨col, j0, i0⟩ _
        have hval : ∀ l ∈ Finset.univ.filter (fun l : Fin a => (bank l, key l, site l) = (col, j0, i0)),
            coeff l * b2z (wRot k hk0 (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) =
              coeff l * b2z (wRot k hk0 (if col then 4 else 0) (kerWord k (c j0)) i0) := by
          intro l hl
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hl
          rcases hl with ⟨hb, hkj, hsi⟩
          rw [hb, hkj, hsi]
        rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
        have hfilt : Finset.univ.filter (fun l : Fin a => (bank l, key l, site l) = (col, j0, i0)) =
            Finset.univ.filter (fun l : Fin a => bank l = col ∧ key l = j0 ∧ site l = i0) := by
          ext l; simp [Prod.mk.injEq]
        rw [hfilt]
        cases col
        · rw [hrow_zero j0 i0, zero_mul]
        · rw [hcol_zero j0 i0, zero_mul]
      rw [hrot_zero, zero_add]
    rw [hdiff, hf0]

  have hLI : LinearIndependent (ZMod 2) (fun p : Fin n × Fin 2 => res (coordFn p)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    let c : Fin n → Fin 2 → Bool := fun j r => decide ((j, r) = p)
    have h0 := congrFun hg c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
    have hev : ∀ q : Fin n × Fin 2, res (coordFn q) c = if q = p then 1 else 0 := by
      rintro ⟨j, r⟩
      simp only [res, LinearMap.coe_mk, AddHom.coe_mk, coordFn, kerWord, c]
      fin_cases r <;> simp [b2z]
    simp_rw [hev] at h0
    simpa using h0
  have h2n_le : n * 2 ≤ Module.finrank (ZMod 2) (A.map res) := by
    have hmem : ∀ p : Fin n × Fin 2, res (coordFn p) ∈ A.map res := fun p =>
      ⟨coordFn p, Submodule.subset_span ⟨p, rfl⟩, rfl⟩
    let v : Fin n × Fin 2 → A.map res := fun p => ⟨res (coordFn p), hmem p⟩
    have hvLI : LinearIndependent (ZMod 2) v := by
      have hcomp : ((A.map res).subtype ∘ v) = (fun p => res (coordFn p)) := rfl
      rw [← hcomp] at hLI
      exact LinearIndependent.of_comp (A.map res).subtype hLI
    have hle := hvLI.fintype_card_le_finrank
    simpa [Fintype.card_prod, Fintype.card_fin] using hle

  let q := B.mkQ
  have hker_le : LinearMap.ker (q.domRestrict A) ≤ LinearMap.ker (res.domRestrict A) := by
    rintro ⟨f, hfA⟩ hfq
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hfq ⊢
    dsimp only [q] at hfq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfq
    exact hAB_ker f ⟨hfA, hfq⟩
  have hker_rank : Module.finrank (ZMod 2) (LinearMap.ker (q.domRestrict A)) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (res.domRestrict A)) :=
    Submodule.finrank_mono hker_le
  have hrn_res := LinearMap.finrank_range_add_finrank_ker (res.domRestrict A)
  have hrn_q := LinearMap.finrank_range_add_finrank_ker (q.domRestrict A)
  have hrange_res : LinearMap.range (res.domRestrict A) = A.map res := by
    ext y; simp [Submodule.mem_map]
  have hrange_q : LinearMap.range (q.domRestrict A) = A.map q := by
    ext y; simp [Submodule.mem_map]
  rw [hrange_res] at hrn_res
  rw [hrange_q] at hrn_q
  have hAq_le_Eq : A.map q ≤ E.map q := by
    calc A.map q ≤ (B ⊔ E).map q := Submodule.map_mono hA_le
      _ = B.map q ⊔ E.map q := Submodule.map_sup _ _ _
      _ = ⊥ ⊔ E.map q := by
        congr 1
        rw [Submodule.eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        exact (Submodule.Quotient.mk_eq_zero B).mpr hx
      _ = E.map q := bot_sup_eq _
  have hEq_rank : Module.finrank (ZMod 2) (E.map q) ≤ Module.finrank (ZMod 2) E := by
    have h1 := LinearMap.finrank_range_le (q.domRestrict E)
    have h2 : LinearMap.range (q.domRestrict E) = E.map q := by ext y; simp [Submodule.mem_map]
    rw [h2] at h1; exact h1
  have hAq_rank : Module.finrank (ZMod 2) (A.map q) ≤ b + t :=
    le_trans (Submodule.finrank_mono hAq_le_Eq) (le_trans hEq_rank hE_rank)
  omega

lemma upper_k1 (n b t : ℕ) (hnb : n ≤ b) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin 1 → Bool) (site : Fin a → Fin 1)
      (side : (Fin n → Fin 1 → Bool) → Fin b → Bool) (C : Circuit)
      (tap : Fin n → Fin 1 → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin 1 → Bool) (j : Fin n) (i : Fin 1),
        let data := List.ofFn (fun l : Fin a => readBit 1 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    fun x r => if hr : r.val < n then x ⟨r.val, hr⟩ 0 else false,
    ⟨[], 0⟩, fun j _ => j.val,
    ⟨readsBack_of_list _ _ (readsBackList_nil _), fun _ hg => by simp at hg⟩,
    by simp, fun j _ => by simp; omega, fun x j i => ?_⟩
  fin_cases i
  simp [Circuit.wires, j.isLt, show j.val < b by omega]

lemma readBit_k2_diff0 (x : Fin 2 → Bool) :
    xor (readBit 2 (by omega) false (singleBit 2 1) x 0)
        (readBit 2 (by omega) false (fun _ => false) x 0) = x 1 := by
  have hx : x = ![x 0, x 1] := by funext r; fin_cases r <;> rfl
  rw [hx]; generalize x 0 = a; generalize x 1 = b; revert a b; decide

lemma readBit_k2_diff1 (x : Fin 2 → Bool) :
    xor (readBit 2 (by omega) false (singleBit 2 0) x 1)
        (readBit 2 (by omega) false (fun _ => false) x 1) = x 0 := by
  have hx : x = ![x 0, x 1] := by funext r; fin_cases r <;> rfl
  rw [hx]; generalize x 0 = a; generalize x 1 = b; revert a b; decide

lemma flatMap_const_getElem {β : Type} (m d : ℕ) (f : Fin m → List β)
    (hd : ∀ r, (f r).length = d) (j : Fin m) (i : Fin d) :
    ((List.finRange m).flatMap f)[d * j.val + i.val]'(by
      rw [List.length_flatMap]; simp [hd]; nlinarith [j.isLt, i.isLt]) =
    (f j)[i.val]'(by rw [hd]; exact i.isLt) := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    simp only [List.finRange_succ, List.flatMap_cons]
    cases j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, mul_zero, zero_add]
      rw [List.getElem_append_left (by rw [hd]; exact i.isLt)]
    | succ j0 =>
      have hge : (f 0).length ≤ d * (j0.succ).val + i.val := by
        rw [hd]; simp [Nat.mul_add]; omega
      rw [List.getElem_append_right hge]
      simp only [hd, Fin.val_succ, List.flatMap_map]
      have hsub : d * (j0.val + 1) + i.val - d = d * j0.val + i.val := by
        rw [Nat.mul_add, mul_one]; omega
      simp only [hsub]
      exact ih (fun r => f r.succ) (fun r => hd r.succ) j0

lemma upper_k2 (n b t : ℕ) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin 2 → Bool) (site : Fin a → Fin 2)
      (side : (Fin n → Fin 2 → Bool) → Fin b → Bool) (C : Circuit)
      (tap : Fin n → Fin 2 → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin 2 → Bool) (j : Fin n) (i : Fin 2),
        let data := List.ofFn (fun l : Fin a => readBit 2 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i := by

  let a := 4 * n
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := fun l => ⟨l.val / 4, by omega⟩
  let name : Fin a → Fin 2 → Bool := fun l =>
    if l.val % 4 = 1 then singleBit 2 1 else if l.val % 4 = 3 then singleBit 2 0 else fun _ => false
  let site : Fin a → Fin 2 := fun l => if l.val % 4 < 2 then 0 else 1
  let specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => [(false, [4 * j.val + 3, 4 * j.val + 2]),
                                          (false, [4 * j.val + 1, 4 * j.val])])
  let res := appendSpecs (a + b) specs
  let C : Circuit := ⟨res.1, 0⟩
  let tap : Fin n → Fin 2 → ℕ := fun j i => res.2.getD (2 * j.val + i.val) 0
  have hspecs_lt : ∀ s ∈ specs, ∀ w ∈ s.2, w < a + b := by
    intro s hs w hw
    simp only [specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    obtain ⟨j, rfl | rfl⟩ := hs <;> simp at hw <;> rcases hw with rfl | rfl <;> omega
  have hspecs_len : specs.length = 2 * n := by
    simp [specs, List.length_flatMap]; omega
  refine ⟨a, bank, key, name, site, fun _ _ => false, C, tap,
    ⟨readsBack_of_list _ _ (appendSpecs_readsBack _ _ hspecs_lt), appendSpecs_fanin _ _⟩,
    by simp [C, res, appendSpecs_nonlin],
    fun j i => by
      have hi : 2 * j.val + i.val < res.2.length := by rw [appendSpecs_taps_len, hspecs_len]; omega
      have hmem : tap j i ∈ res.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact appendSpecs_taps_lt _ _ _ hmem,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit 2 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
    List.ofFn (fun _ : Fin b => false)
  have hdata_len : data.length = a + b := by simp [data]
  have hidx : 2 * j.val + i.val < specs.length := by rw [hspecs_len]; omega
  have hev := appendSpecs_eval specs data (by simpa [hdata_len] using hspecs_lt) (2 * j.val + i.val) hidx
  rw [hdata_len] at hev
  change (wiresFrom res.1 data).getD (tap j i) false = x j i
  rw [hev]
  have hspec_at : specs[2 * j.val + i.val] =
      if i.val = 0 then (false, [4 * j.val + 3, 4 * j.val + 2])
      else (false, [4 * j.val + 1, 4 * j.val]) := by
    have h := flatMap_const_getElem n 2
      (fun j => [(false, [4 * j.val + 3, 4 * j.val + 2]),
                 (false, [4 * j.val + 1, 4 * j.val])]) (fun _ => rfl) j i
    fin_cases i <;> simpa [specs] using h
  rw [hspec_at]
  have hget : ∀ (idx : ℕ) (hidx' : idx < a),
      data.getD idx false = readBit 2 (by omega) (bank ⟨idx, hidx'⟩) (name ⟨idx, hidx'⟩)
        (x (key ⟨idx, hidx'⟩)) (site ⟨idx, hidx'⟩) := by
    intro idx hidx'
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hidx']), getD_ofFn_lt _ _ idx hidx']
  fin_cases i
  · simp only [Fin.val_zero, ↓reduceIte, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    rw [hget (4 * j.val + 3) (by omega), hget (4 * j.val + 2) (by omega)]
    have hk1 : key ⟨4 * j.val + 3, by omega⟩ = j := Fin.ext (by simp [key]; omega)
    have hk2 : key ⟨4 * j.val + 2, by omega⟩ = j := Fin.ext (by simp [key]; omega)
    have hn1 : name ⟨4 * j.val + 3, by omega⟩ = singleBit 2 0 := by simp [name]
    have hn2 : name ⟨4 * j.val + 2, by omega⟩ = (fun _ => false) := by simp [name]
    have hs1 : site ⟨4 * j.val + 3, by omega⟩ = 1 := by simp [site]
    have hs2 : site ⟨4 * j.val + 2, by omega⟩ = 1 := by simp [site]
    rw [hk1, hk2, hn1, hn2, hs1, hs2]
    exact readBit_k2_diff1 (x j)
  · simp only [Fin.val_one, Nat.one_ne_zero, ↓reduceIte, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    rw [hget (4 * j.val + 1) (by omega), hget (4 * j.val) (by omega)]
    have hk1 : key ⟨4 * j.val + 1, by omega⟩ = j := Fin.ext (by simp [key]; omega)
    have hk2 : key ⟨4 * j.val, by omega⟩ = j := Fin.ext (by simp [key])
    have hn1 : name ⟨4 * j.val + 1, by omega⟩ = singleBit 2 1 := by simp [name]
    have hn2 : name ⟨4 * j.val, by omega⟩ = (fun _ => false) := by simp [name]
    have hs1 : site ⟨4 * j.val + 1, by omega⟩ = 0 := by simp [site]
    have hs2 : site ⟨4 * j.val, by omega⟩ = 0 := by simp [site]
    rw [hk1, hk2, hn1, hn2, hs1, hs2]
    exact readBit_k2_diff0 (x j)

lemma readBit_k3_xor (x : Fin 3 → Bool) (i : Fin 3) :
    xor (readBit 3 (by omega) false (fun _ => false) x 0)
        (xor (readBit 3 (by omega) false (fun _ => false) x i) (x 0)) = x i := by
  have hx : x = ![x 0, x 1, x 2] := by funext r; fin_cases r <;> rfl
  rw [hx]; revert i; generalize x 0 = a; generalize x 1 = b; generalize x 2 = c
  revert a b c; decide

lemma upper_k3 (n b t : ℕ) (hnb : n ≤ b) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin 3 → Bool) (site : Fin a → Fin 3)
      (side : (Fin n → Fin 3 → Bool) → Fin b → Bool) (C : Circuit)
      (tap : Fin n → Fin 3 → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin 3 → Bool) (j : Fin n) (i : Fin 3),
        let data := List.ofFn (fun l : Fin a => readBit 3 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i := by
  let a := 3 * n
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := fun l => ⟨l.val / 3, by omega⟩
  let name : Fin a → Fin 3 → Bool := fun _ _ => false
  let site : Fin a → Fin 3 := fun l => ⟨l.val % 3, Nat.mod_lt _ (by omega)⟩
  let side : (Fin n → Fin 3 → Bool) → Fin b → Bool :=
    fun x r => if hr : r.val < n then x ⟨r.val, hr⟩ 0 else false
  let specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange 3).map (fun i =>
      (false, [3 * j.val, 3 * j.val + i.val, a + j.val])))
  let res := appendSpecs (a + b) specs
  let C : Circuit := ⟨res.1, 0⟩
  let tap : Fin n → Fin 3 → ℕ := fun j i => res.2.getD (3 * j.val + i.val) 0
  have hspecs_lt : ∀ s ∈ specs, ∀ w ∈ s.2, w < a + b := by
    intro s hs w hw
    simp only [specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    simp at hw; rcases hw with rfl | rfl | rfl <;> omega
  have hspecs_len : specs.length = 3 * n := by
    simp [specs, List.length_flatMap]; omega
  refine ⟨a, bank, key, name, site, side, C, tap,
    ⟨readsBack_of_list _ _ (appendSpecs_readsBack _ _ hspecs_lt), appendSpecs_fanin _ _⟩,
    by simp [C, res, appendSpecs_nonlin],
    fun j i => by
      have hi : 3 * j.val + i.val < res.2.length := by rw [appendSpecs_taps_len, hspecs_len]; omega
      have hmem : tap j i ∈ res.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact appendSpecs_taps_lt _ _ _ hmem,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit 3 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
    List.ofFn (side x)
  have hdata_len : data.length = a + b := by simp [data]
  have hidx : 3 * j.val + i.val < specs.length := by rw [hspecs_len]; omega
  have hev := appendSpecs_eval specs data (by simpa [hdata_len] using hspecs_lt) (3 * j.val + i.val) hidx
  rw [hdata_len] at hev
  change (wiresFrom res.1 data).getD (tap j i) false = x j i
  rw [hev]
  have hspec_at : specs[3 * j.val + i.val] = (false, [3 * j.val, 3 * j.val + i.val, a + j.val]) := by
    have h := flatMap_const_getElem n 3
      (fun j => (List.finRange 3).map (fun i => (false, [3 * j.val, 3 * j.val + i.val, a + j.val])))
      (fun _ => by simp) j i
    simpa [specs] using h
  rw [hspec_at]
  simp only [List.foldr_cons, List.foldr_nil, Bool.xor_false]
  have hgetA : ∀ (idx : ℕ) (hidx' : idx < a),
      data.getD idx false = readBit 3 (by omega) false (fun _ => false) (x ⟨idx / 3, by omega⟩)
        ⟨idx % 3, Nat.mod_lt _ (by omega)⟩ := by
    intro idx hidx'
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hidx']), getD_ofFn_lt _ _ idx hidx']
  have hgetS : data.getD (a + j.val) false = x j 0 := by
    simp only [data]
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rw [getD_ofFn_lt _ _ j.val (by omega)]
    simp [side, j.isLt]
  rw [hgetA (3 * j.val) (by omega), hgetA (3 * j.val + i.val) (by omega), hgetS]
  have hjlt := j.isLt; have hilt := i.isLt
  have hk1 : (⟨3 * j.val / 3, by omega⟩ : Fin n) = j := Fin.ext (by simp)
  have hk2 : (⟨(3 * j.val + i.val) / 3, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
  have hs1 : (⟨3 * j.val % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = 0 := Fin.ext (by simp)
  have hs2 : (⟨(3 * j.val + i.val) % 3, Nat.mod_lt _ (by omega)⟩ : Fin 3) = i := Fin.ext (by simp)
  rw [hk1, hk2, hs1, hs2]
  exact readBit_k3_xor (x j) i

lemma k6_x2_formula (x : Fin 6 → Bool) :
    let col0 := fun i : Fin 6 => readBit 6 (by omega) true (fun _ => false) x i
    let R01 := xor (readBit 6 (by omega) false (singleBit 6 5) x 5)
                   (readBit 6 (by omega) false (fun _ => false) x 5)
    xor R01 (xor (col0 0) (xor (col0 3) (xor (col0 4) (col0 5)))) = !(x 2) := by
  have hR : xor (readBit 6 (by omega) false (singleBit 6 5) x 5)
                (readBit 6 (by omega) false (fun _ => false) x 5) =
            !(wMix 6 (by omega) 1 (wRot 6 (by omega) 1 x) 1) := by
    simpa [ix] using rowDiff_ge4 6 (by omega) x 5
  have hmix : wMix 6 (by omega) 1 (wRot 6 (by omega) 1 x) 1 =
      xor (x 5) (xor (x 0) (x 1)) := by
    simpa [ix] using wMix_rot1_eq 6 (by omega) x 0
  have hcol : ∀ x0 x1 x2 x3 x4 x5 : Bool,
      let f : Fin 6 → Bool := ![x0, x1, x2, x3, x4, x5]
      xor (readBit 6 (by omega) true (fun _ => false) f 0)
        (xor (readBit 6 (by omega) true (fun _ => false) f 3)
          (xor (readBit 6 (by omega) true (fun _ => false) f 4)
               (readBit 6 (by omega) true (fun _ => false) f 5))) =
        xor x5 (xor x0 (xor x1 x2)) := by
    decide
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i; fin_cases i <;> rfl
  dsimp only
  rw [hR, hmix]
  conv_lhs => rw [hx]
  rw [hcol]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 5 <;> rfl

lemma k6_col_diff (x : Fin 6 → Bool) (i : Fin 6) :
    xor (readBit 6 (by omega) true (fun _ => false) x 0)
        (readBit 6 (by omega) true (fun _ => false) x i) =
      xor (x 2) (x (ix 6 (by omega) (i.val + 2))) := by
  have hdec : ∀ (x0 x1 x2 x3 x4 x5 : Bool) (i : Fin 6),
      let f : Fin 6 → Bool := ![x0, x1, x2, x3, x4, x5]
      xor (readBit 6 (by omega) true (fun _ => false) f 0)
          (readBit 6 (by omega) true (fun _ => false) f i) =
        xor (f 2) (f (ix 6 (by omega) (i.val + 2))) := by
    decide
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext r; fin_cases r <;> rfl
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  exact hdec (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i

lemma upper_k6 (n b t : ℕ) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin 6 → Bool) (site : Fin a → Fin 6)
      (side : (Fin n → Fin 6 → Bool) → Fin b → Bool) (C : Circuit)
      (tap : Fin n → Fin 6 → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin 6 → Bool) (j : Fin n) (i : Fin 6),
        let data := List.ofFn (fun l : Fin a => readBit 6 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i := by

  let a := 8 * n
  let bank : Fin a → Bool := fun l => decide (l.val % 8 < 6)
  let key : Fin a → Fin n := fun l => ⟨l.val / 8, by omega⟩
  let name : Fin a → Fin 6 → Bool := fun l =>
    if l.val % 8 = 6 then singleBit 6 5 else fun _ => false
  let site : Fin a → Fin 6 := fun l =>
    if h : l.val % 8 < 6 then ⟨l.val % 8, h⟩ else 5

  let specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange 6).map (fun i =>
      (true, [8 * j.val + 6, 8 * j.val + 7, 8 * j.val + 3, 8 * j.val + 4, 8 * j.val + 5,
              8 * j.val + (i.val + 4) % 6])))
  let res := appendSpecs (a + b) specs
  let C : Circuit := ⟨res.1, 0⟩
  let tap : Fin n → Fin 6 → ℕ := fun j i => res.2.getD (6 * j.val + i.val) 0
  have hspecs_lt : ∀ s ∈ specs, ∀ w ∈ s.2, w < a + b := by
    intro s hs w hw
    simp only [specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    simp at hw; rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hspecs_len : specs.length = 6 * n := by
    simp [specs, List.length_flatMap]; omega
  refine ⟨a, bank, key, name, site, fun _ _ => false, C, tap,
    ⟨readsBack_of_list _ _ (appendSpecs_readsBack _ _ hspecs_lt), appendSpecs_fanin _ _⟩,
    by simp [C, res, appendSpecs_nonlin],
    fun j i => by
      have hi : 6 * j.val + i.val < res.2.length := by rw [appendSpecs_taps_len, hspecs_len]; omega
      have hmem : tap j i ∈ res.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact appendSpecs_taps_lt _ _ _ hmem,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit 6 (by omega) (bank l) (name l) (x (key l)) (site l)) ++
    List.ofFn (fun _ : Fin b => false)
  have hdata_len : data.length = a + b := by simp [data]
  have hidx : 6 * j.val + i.val < specs.length := by rw [hspecs_len]; omega
  have hev := appendSpecs_eval specs data (by simpa [hdata_len] using hspecs_lt) (6 * j.val + i.val) hidx
  rw [hdata_len] at hev
  change (wiresFrom res.1 data).getD (tap j i) false = x j i
  rw [hev]
  have hspec_at : specs[6 * j.val + i.val] =
      (true, [8 * j.val + 6, 8 * j.val + 7, 8 * j.val + 3, 8 * j.val + 4, 8 * j.val + 5,
              8 * j.val + (i.val + 4) % 6]) := by
    have h := flatMap_const_getElem n 6
      (fun j => (List.finRange 6).map (fun i =>
        (true, [8 * j.val + 6, 8 * j.val + 7, 8 * j.val + 3, 8 * j.val + 4, 8 * j.val + 5,
                8 * j.val + (i.val + 4) % 6])))
      (fun _ => by simp) j i
    simpa [specs] using h
  rw [hspec_at]
  have hgetC : ∀ (r : Fin 6), data.getD (8 * j.val + r.val) false =
      readBit 6 (by omega) true (fun _ => false) (x j) r := by
    intro r
    have hjlt := j.isLt; have hrlt := r.isLt
    have hlt : 8 * j.val + r.val < a := by omega
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hlt]), getD_ofFn_lt _ _ _ hlt]
    have hb : bank ⟨8 * j.val + r.val, hlt⟩ = true := by simp [bank]; omega
    have hk : key ⟨8 * j.val + r.val, hlt⟩ = j := Fin.ext (by simp [key]; omega)
    have hn : name ⟨8 * j.val + r.val, hlt⟩ = (fun _ => false) := by simp [name]; omega
    have hs : site ⟨8 * j.val + r.val, hlt⟩ = r := Fin.ext (by
      have hmod8 : (8 * j.val + r.val) % 8 = r.val := by omega
      simp [site, hmod8, hrlt])
    rw [hb, hk, hn, hs]
  have hget6 : data.getD (8 * j.val + 6) false = readBit 6 (by omega) false (singleBit 6 5) (x j) 5 := by
    have hjlt := j.isLt
    have hlt : 8 * j.val + 6 < a := by omega
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hlt]), getD_ofFn_lt _ _ _ hlt]
    have hb : bank ⟨8 * j.val + 6, hlt⟩ = false := by simp [bank]
    have hk : key ⟨8 * j.val + 6, hlt⟩ = j := Fin.ext (by simp [key]; omega)
    have hn : name ⟨8 * j.val + 6, hlt⟩ = singleBit 6 5 := by simp [name]
    have hs : site ⟨8 * j.val + 6, hlt⟩ = 5 := Fin.ext (by simp [site])
    rw [hb, hk, hn, hs]
  have hget7 : data.getD (8 * j.val + 7) false = readBit 6 (by omega) false (fun _ => false) (x j) 5 := by
    have hjlt := j.isLt
    have hlt : 8 * j.val + 7 < a := by omega
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hlt]), getD_ofFn_lt _ _ _ hlt]
    have hb : bank ⟨8 * j.val + 7, hlt⟩ = false := by simp [bank]
    have hk : key ⟨8 * j.val + 7, hlt⟩ = j := Fin.ext (by simp [key]; omega)
    have hn : name ⟨8 * j.val + 7, hlt⟩ = (fun _ => false) := by simp [name]
    have hs : site ⟨8 * j.val + 7, hlt⟩ = 5 := Fin.ext (by simp [site])
    rw [hb, hk, hn, hs]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [hget6, hget7,
      show data.getD (8 * j.val + 3) false = readBit 6 (by omega) true (fun _ => false) (x j) 3 from hgetC 3,
      show data.getD (8 * j.val + 4) false = readBit 6 (by omega) true (fun _ => false) (x j) 4 from hgetC 4,
      show data.getD (8 * j.val + 5) false = readBit 6 (by omega) true (fun _ => false) (x j) 5 from hgetC 5,
      hgetC ⟨(i.val + 4) % 6, Nat.mod_lt _ (by omega)⟩]
  have hx2 := k6_x2_formula (x j)
  have hcd := k6_col_diff (x j) ⟨(i.val + 4) % 6, Nat.mod_lt _ (by omega)⟩
  have hix : ix 6 (by omega) ((i.val + 4) % 6 + 2) = i := Fin.ext (by simp [ix]; omega)
  rw [hix] at hcd
  apply b2z_inj
  have hz1 := congrArg b2z hx2
  have hz2 := congrArg b2z hcd
  simp only [b2z_xor, b2z_not, b2z_true] at hz1 hz2 ⊢
  have h2z : ∀ z : ZMod 2, z + z = 0 := by decide
  have h00 : b2z (readBit 6 (by omega) true (fun _ => false) (x j) 0) +
      b2z (readBit 6 (by omega) true (fun _ => false) (x j) 0) = 0 := h2z _
  calc
    b2z (readBit 6 (by omega) false (singleBit 6 5) (x j) 5) +
      (b2z (readBit 6 (by omega) false (fun _ => false) (x j) 5) +
        (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 3) +
          (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 4) +
            (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 5) +
              (b2z (readBit 6 (by omega) true (fun _ => false) (x j) ⟨(i.val + 4) % 6, Nat.mod_lt _ (by omega)⟩) + 1)))))
    = b2z (readBit 6 (by omega) false (singleBit 6 5) (x j) 5) +
      (b2z (readBit 6 (by omega) false (fun _ => false) (x j) 5) +
        (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 3) +
          (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 4) +
            (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 5) +
              (b2z (readBit 6 (by omega) true (fun _ => false) (x j) ⟨(i.val + 4) % 6, Nat.mod_lt _ (by omega)⟩) + 1))))) +
      (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 0) +
        b2z (readBit 6 (by omega) true (fun _ => false) (x j) 0)) := by rw [h00, add_zero]
    _ = (b2z (readBit 6 (by omega) false (singleBit 6 5) (x j) 5) +
        b2z (readBit 6 (by omega) false (fun _ => false) (x j) 5) +
        (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 0) +
          (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 3) +
            (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 4) +
              b2z (readBit 6 (by omega) true (fun _ => false) (x j) 5))))) +
      (b2z (readBit 6 (by omega) true (fun _ => false) (x j) 0) +
        b2z (readBit 6 (by omega) true (fun _ => false) (x j) ⟨(i.val + 4) % 6, Nat.mod_lt _ (by omega)⟩)) + 1 := by ring
    _ = (1 + b2z (x j 2)) + (b2z (x j 2) + b2z (x j i)) + 1 := by rw [hz1, hz2]
    _ = b2z (x j i) + ((1 + 1) + (b2z (x j 2) + b2z (x j 2))) := by ring
    _ = b2z (x j i) := by rw [h2z, h2z, add_zero, add_zero]

lemma upper_ge4_ndiv3 (k : ℕ) (hk : 4 ≤ k) (hndiv : ¬ 3 ∣ k) (n b t : ℕ) :
    have hk0 : 0 < k := by omega
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
      (side : (Fin n → Fin k → Bool) → Fin b → Bool) (C : Circuit)
      (tap : Fin n → Fin k → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i := by
  have hk0 : 0 < k := by omega

  let a := 2 * (n * k)
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := fun l => ⟨(l.val / 2) / k, by
    have : l.val / 2 < n * k := by omega
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
  let site : Fin a → Fin k := fun l => ⟨(l.val / 2) % k, Nat.mod_lt _ hk0⟩
  let name : Fin a → Fin k → Bool := fun l =>
    if l.val % 2 = 0 then singleBit k (site l) else fun _ => false
  let r0Pair : Fin n → Fin k → List ℕ := fun j q =>
    let r := (q.val + k - 2) % k
    [2 * (j.val * k + r), 2 * (j.val * k + r) + 1]
  let specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange k).map (fun i =>
      let idxs := invMixIndices k hk i
      (decide (idxs.length % 2 = 1), idxs.flatMap (r0Pair j))))
  let res := appendSpecs (a + b) specs
  let C : Circuit := ⟨res.1, 0⟩
  let tap : Fin n → Fin k → ℕ := fun j i => res.2.getD (k * j.val + i.val) 0
  have hspecs_lt : ∀ s ∈ specs, ∀ w ∈ s.2, w < a + b := by
    intro s hs w hw
    simp only [specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    simp only [List.mem_flatMap, r0Pair, List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain ⟨q, _, rfl | rfl⟩ := hw <;>
    · have hr : (q.val + k - 2) % k < k := Nat.mod_lt _ hk0
      have hj : j.val * k + (q.val + k - 2) % k < n * k := by
        calc j.val * k + (q.val + k - 2) % k < j.val * k + k := by omega
          _ = (j.val + 1) * k := by ring
          _ ≤ n * k := Nat.mul_le_mul_right k j.isLt
      omega
  have hspecs_len : specs.length = k * n := by
    simp [specs, List.length_flatMap]; ring
  refine ⟨a, bank, key, name, site, fun _ _ => false, C, tap,
    ⟨readsBack_of_list _ _ (appendSpecs_readsBack _ _ hspecs_lt), appendSpecs_fanin _ _⟩,
    by simp [C, res, appendSpecs_nonlin],
    fun j i => by
      have hi : k * j.val + i.val < res.2.length := by
        rw [appendSpecs_taps_len, hspecs_len]; nlinarith [j.isLt, i.isLt]
      have hmem : tap j i ∈ res.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact appendSpecs_taps_lt _ _ _ hmem,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l)) ++
    List.ofFn (fun _ : Fin b => false)
  have hdata_len : data.length = a + b := by simp [data]
  have hidx : k * j.val + i.val < specs.length := by rw [hspecs_len]; nlinarith [j.isLt, i.isLt]
  have hev := appendSpecs_eval specs data (by simpa [hdata_len] using hspecs_lt) (k * j.val + i.val) hidx
  rw [hdata_len] at hev
  change (wiresFrom res.1 data).getD (tap j i) false = x j i
  rw [hev]
  have hspec_at : specs[k * j.val + i.val] =
      (decide ((invMixIndices k hk i).length % 2 = 1), (invMixIndices k hk i).flatMap (r0Pair j)) := by
    have h := flatMap_const_getElem n k
      (fun j => (List.finRange k).map (fun i =>
        (decide ((invMixIndices k hk i).length % 2 = 1), (invMixIndices k hk i).flatMap (r0Pair j))))
      (fun _ => by simp) j i
    simpa [specs] using h
  rw [hspec_at]
  have hpair : ∀ q : Fin k,
      xor (data.getD (2 * (j.val * k + (q.val + k - 2) % k)) false)
          (data.getD (2 * (j.val * k + (q.val + k - 2) % k) + 1) false) =
        !(wMix k hk0 1 (wRot k hk0 1 (x j)) q) := by
    intro q
    set r := (q.val + k - 2) % k
    have hr : r < k := Nat.mod_lt _ hk0
    have hlt1 : 2 * (j.val * k + r) < a := by
      have : j.val * k + r < n * k := by
        calc j.val * k + r < j.val * k + k := by omega
          _ = (j.val + 1) * k := by ring
          _ ≤ n * k := Nat.mul_le_mul_right k j.isLt
      omega
    have hlt2 : 2 * (j.val * k + r) + 1 < a := by omega
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hlt1]), getD_ofFn_lt _ _ _ hlt1,
        List.getD_append _ _ _ _ (by simp [hlt2]), getD_ofFn_lt _ _ _ hlt2]
    have hk1 : key ⟨2 * (j.val * k + r), hlt1⟩ = j := by
      apply Fin.ext; simp only [key]
      have hdiv : 2 * (j.val * k + r) / 2 = j.val * k + r := by omega
      rw [hdiv, Nat.mul_comm j.val k, Nat.mul_add_div hk0, Nat.div_eq_of_lt hr, add_zero]
    have hk2 : key ⟨2 * (j.val * k + r) + 1, hlt2⟩ = j := by
      apply Fin.ext; simp only [key]
      have hdiv : (2 * (j.val * k + r) + 1) / 2 = j.val * k + r := by omega
      rw [hdiv, Nat.mul_comm j.val k, Nat.mul_add_div hk0, Nat.div_eq_of_lt hr, add_zero]
    have hs1 : site ⟨2 * (j.val * k + r), hlt1⟩ = ⟨r, hr⟩ := by
      apply Fin.ext; simp only [site]
      have hdiv : 2 * (j.val * k + r) / 2 = j.val * k + r := by omega
      rw [hdiv, Nat.mul_add_mod_of_lt hr]
    have hs2 : site ⟨2 * (j.val * k + r) + 1, hlt2⟩ = ⟨r, hr⟩ := by
      apply Fin.ext; simp only [site]
      have hdiv : (2 * (j.val * k + r) + 1) / 2 = j.val * k + r := by omega
      rw [hdiv, Nat.mul_add_mod_of_lt hr]
    have hn1 : name ⟨2 * (j.val * k + r), hlt1⟩ = singleBit k ⟨r, hr⟩ := by
      simp [name, hs1]
    have hn2 : name ⟨2 * (j.val * k + r) + 1, hlt2⟩ = (fun _ => false) := by
      simp [name]
    rw [hk1, hk2, hs1, hs2, hn1, hn2]
    have hrd := rowDiff_ge4 k hk (x j) ⟨r, hr⟩
    have hq_eq : ix k hk0 (r + 2) = q := Fin.ext (by
      simp only [ix, r]
      rw [mod_add_cancel, show q.val + k - 2 + 2 = q.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt])
    simpa [bank, hq_eq] using hrd

  have hfold : ∀ (l : List (Fin k)),
      (l.flatMap (r0Pair j)).foldr (fun w acc => xor (data.getD w false) acc) (decide (l.length % 2 = 1)) =
        l.foldr (fun q acc => xor (wMix k hk0 1 (wRot k hk0 1 (x j)) q) acc) false := by
    intro l
    induction l with
    | nil => rfl
    | cons q l ih =>
      simp only [List.flatMap_cons, List.foldr_append, r0Pair, List.foldr_cons, List.foldr_nil,
        List.length_cons]
      have hxor_assoc : ∀ a b c : Bool, xor a (xor b c) = xor (xor a b) c := by
        intro a b c; cases a <;> cases b <;> cases c <;> rfl
      rw [hxor_assoc, hpair q]
      have hflip : ∀ (ws : List ℕ) (b : Bool),
          ws.foldr (fun w acc => xor (data.getD w false) acc) (!b) =
            !(ws.foldr (fun w acc => xor (data.getD w false) acc) b) := by
        intro ws b
        induction ws with
        | nil => rfl
        | cons w ws ihw =>
          simp only [List.foldr_cons, ihw]
          cases data.getD w false <;> cases ws.foldr (fun w acc => xor (data.getD w false) acc) b <;> rfl
      have hpar : decide ((l.length + 1) % 2 = 1) = !(decide (l.length % 2 = 1)) := by
        by_cases h : l.length % 2 = 1 <;> simp [h, show (l.length + 1) % 2 = 1 ↔ l.length % 2 ≠ 1 by omega]
      rw [hpar, hflip, ih]
      cases wMix k hk0 1 (wRot k hk0 1 (x j)) q <;>
      cases l.foldr (fun q acc => xor (wMix k hk0 1 (wRot k hk0 1 (x j)) q) acc) false <;> rfl
  rw [hfold (invMixIndices k hk i)]
  exact invMixIndices_correct k hk hndiv (x j) i

lemma upper_ge9_div3 (k : ℕ) (hk : 9 ≤ k) (n b t : ℕ) (hbt : n * 2 ≤ b + t) :
    have hk0 : 0 < k := by omega
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
      (side : (Fin n → Fin k → Bool) → Fin b → Bool) (C : Circuit)
      (tap : Fin n → Fin k → ℕ),
      ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
      (∀ j i, tap j i < a + b + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l)) ++
          List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i := by
  have hk0 : 0 < k := by omega
  have hk4 : 4 ≤ k := by omega
  have hk2 : 2 ≤ k := by omega

  let a := 2 * (n * k)
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := fun l => ⟨(l.val / 2) / k, by
    have : l.val / 2 < n * k := by omega
    exact Nat.div_lt_of_lt_mul (by rwa [mul_comm])⟩
  let site : Fin a → Fin k := fun l => ⟨(l.val / 2) % k, Nat.mod_lt _ hk0⟩
  let name : Fin a → Fin k → Bool := fun l =>
    if l.val % 2 = 0 then singleBit k (site l) else fun _ => false
  let side : (Fin n → Fin k → Bool) → Fin b → Bool := fun x r =>
    if hr : r.val < 2 * n then x ⟨r.val / 2, by omega⟩ ⟨r.val % 2, by omega⟩ else false

  let r0Specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange k).map (fun q =>
      let r := (q.val + k - 2) % k
      (true, [2 * (j.val * k + r), 2 * (j.val * k + r) + 1])))
  let st1 := appendSpecs (a + b) r0Specs
  let w1 := a + b + st1.1.length
  let tapR0 : Fin n → Fin k → ℕ := fun j q => st1.2.getD (k * j.val + q.val) 0

  let m := 2 * n - b
  let nlGatePair : ℕ → List Gate := fun d =>
    if hd : d < m then
      let p := b + d
      let j : Fin n := ⟨p / 2, by omega⟩
      let r1 : Fin k := ix k hk0 (p % 2 + 1)
      let r2 : Fin k := ix k hk0 (p % 2 + 2)
      [mkNot (tapR0 j r1), mkAnd (w1 + 2 * d) (tapR0 j r2)]
    else [mkConst false, mkConst false]
  let nlGates : List Gate := (List.range m).flatMap nlGatePair
  let w2 := w1 + nlGates.length

  let anchorWires : Fin n → Fin 2 → List ℕ := fun j r =>
    let p := 2 * j.val + r.val
    if p < b then [a + p]
    else [2 * (j.val * k + r.val) + 1, tapR0 j ⟨r.val, by omega⟩, w1 + 2 * (p - b) + 1]
  let outSpecs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange k).map (fun i =>
      let ws0 := if recAnchor0 i.val then anchorWires j 0 else []
      let ws1 := if recAnchor1 i.val then anchorWires j 1 else []
      let wsR := (recR0Indices k hk0 i.val).map (tapR0 j)
      (false, ws0 ++ ws1 ++ wsR)))
  let st3 := appendSpecs w2 outSpecs
  let C : Circuit := ⟨st1.1 ++ nlGates ++ st3.1, 0⟩
  let tap : Fin n → Fin k → ℕ := fun j i => st3.2.getD (k * j.val + i.val) 0
  have hr0_lt : ∀ s ∈ r0Specs, ∀ w ∈ s.2, w < a + b := by
    intro s hs w hw
    simp only [r0Specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, q, rfl⟩ := hs
    simp at hw
    have hr : (q.val + k - 2) % k < k := Nat.mod_lt _ hk0
    have hj : j.val * k + (q.val + k - 2) % k < n * k := by
      calc j.val * k + (q.val + k - 2) % k < j.val * k + k := by omega
        _ = (j.val + 1) * k := by ring
        _ ≤ n * k := Nat.mul_le_mul_right k j.isLt
    rcases hw with rfl | rfl <;> omega
  have hr0_len : r0Specs.length = k * n := by simp [r0Specs, List.length_flatMap]; ring
  have htapR0_lt : ∀ j q, tapR0 j q < w1 := by
    intro j q
    have hi : k * j.val + q.val < st1.2.length := by
      rw [appendSpecs_taps_len, hr0_len]; nlinarith [j.isLt, q.isLt]
    have hmem : tapR0 j q ∈ st1.2 := by
      dsimp only [tapR0]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact appendSpecs_taps_lt _ _ _ hmem
  have hnl_len : nlGates.length = 2 * m := by
    have h2 : ∀ d, (nlGatePair d).length = 2 := by intro d; dsimp only [nlGatePair]; split_ifs <;> rfl
    simp [nlGates, List.length_flatMap, h2]; omega
  have hnl_nonlin : nlGates.countP isNonlin = m := by
    have hgen : ∀ (q : ℕ) (hq : q ≤ m), ((List.range q).flatMap nlGatePair).countP isNonlin = q := by
      intro q hq
      induction q with
      | zero => rfl
      | succ q ih =>
        rw [List.range_succ, List.flatMap_append, List.countP_append, ih (by omega)]
        simp [nlGatePair, show q < m by omega, isNonlin_mkNot, isNonlin_mkAnd]
    exact hgen m le_rfl
  have hnl_fanin : ∀ g ∈ nlGates, g.inputs.length ≤ 2 := by
    intro g hg
    simp only [nlGates, List.mem_flatMap, List.mem_range] at hg
    obtain ⟨d, hd, hgd⟩ := hg
    simp only [nlGatePair, hd, ↓reduceDIte, List.mem_cons, List.not_mem_nil, or_false] at hgd
    rcases hgd with rfl | rfl <;> simp [mkNot, mkAnd]
  have hnl_rb : ReadsBackList w1 nlGates := by
    intro idx hidx i hi
    have hq_lt : idx / 2 < m := by rw [hnl_len] at hidx; omega
    have hget : nlGates[idx] =
        if idx % 2 = 0 then
          mkNot (tapR0 ⟨(b + idx / 2) / 2, by omega⟩ (ix k hk0 ((b + idx / 2) % 2 + 1)))
        else
          mkAnd (w1 + 2 * (idx / 2)) (tapR0 ⟨(b + idx / 2) / 2, by omega⟩ (ix k hk0 ((b + idx / 2) % 2 + 2))) := by
      have h2 : ∀ d, (nlGatePair d).length = 2 := by intro d; dsimp only [nlGatePair]; split_ifs <;> rfl
      have hfm : ∀ (q : ℕ) (hq : q ≤ m) (idx' : ℕ) (hidx' : idx' < 2 * q),
          ((List.range q).flatMap nlGatePair)[idx']'(by
              rw [List.length_flatMap]; simp [h2]; omega) =
          if idx' % 2 = 0 then
            mkNot (tapR0 ⟨(b + idx' / 2) / 2, by omega⟩ (ix k hk0 ((b + idx' / 2) % 2 + 1)))
          else
            mkAnd (w1 + 2 * (idx' / 2)) (tapR0 ⟨(b + idx' / 2) / 2, by omega⟩ (ix k hk0 ((b + idx' / 2) % 2 + 2))) := by
        intro q hq
        induction q with
        | zero => intro idx' hidx'; omega
        | succ q ih =>
          intro idx' hidx'
          simp only [List.range_succ, List.flatMap_append]
          by_cases hlt : idx' < 2 * q
          · rw [List.getElem_append_left (by rw [List.length_flatMap]; simp [h2]; omega)]
            exact ih (by omega) idx' hlt
          · rw [List.getElem_append_right (by rw [List.length_flatMap]; simp [h2]; omega)]
            have hlen : ((List.range q).flatMap nlGatePair).length = 2 * q := by
              rw [List.length_flatMap]; simp [h2]; omega
            have hdiv : idx' / 2 = q := by omega
            have hqm : q < m := by omega
            by_cases hmod : idx' % 2 = 0
            · have hsub : idx' - 2 * q = 0 := by omega
              simp [hlen, hsub, hdiv, hmod, nlGatePair, hqm]
            · have hsub : idx' - 2 * q = 1 := by omega
              simp [hlen, hsub, hdiv, hmod, nlGatePair, hqm]
      exact hfm m le_rfl idx (by omega)
    rw [hget] at hi
    split_ifs at hi with hmod
    · simp [mkNot] at hi; subst hi; exact Nat.lt_of_lt_of_le (htapR0_lt _ _) (Nat.le_add_right _ _)
    · simp [mkAnd] at hi
      rcases hi with rfl | rfl
      · omega
      · exact Nat.lt_of_lt_of_le (htapR0_lt _ _) (Nat.le_add_right _ _)
  have hout_lt : ∀ s ∈ outSpecs, ∀ w ∈ s.2, w < w2 := by
    intro s hs w hw
    simp only [outSpecs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    simp only [List.mem_append, List.mem_map] at hw
    have hanc : ∀ r : Fin 2, ∀ w ∈ anchorWires j r, w < w2 := by
      intro r w hw
      dsimp only [anchorWires] at hw
      split_ifs at hw with hpb
      · simp at hw; subst hw; omega
      · simp at hw
        rcases hw with rfl | rfl | rfl
        · have : j.val * k + r.val < n * k := by
            calc j.val * k + r.val < j.val * k + k := by omega
              _ = (j.val + 1) * k := by ring
              _ ≤ n * k := Nat.mul_le_mul_right k j.isLt
          omega
        · have := htapR0_lt j ⟨r.val, by omega⟩; omega
        · rw [show w2 = w1 + 2 * m by simp [w2, hnl_len]]; omega
    rcases hw with (h | h) | ⟨q, _, rfl⟩
    · split_ifs at h with h0
      · exact hanc 0 w h
      · simp at h
    · split_ifs at h with h1
      · exact hanc 1 w h
      · simp at h
    · have := htapR0_lt j q; omega
  have hout_len : outSpecs.length = k * n := by simp [outSpecs, List.length_flatMap]; ring
  have hC_rb : ReadsBackList (a + b) C.gates := by
    dsimp only [C]
    apply readsBackList_append
    · apply readsBackList_append
      · exact appendSpecs_readsBack _ _ hr0_lt
      · exact hnl_rb
    · simp only [List.length_append]
      rw [show a + b + (st1.1.length + nlGates.length) = w2 by simp [w2, w1]; omega]
      exact appendSpecs_readsBack _ _ hout_lt
  have hC_fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    intro g hg
    simp only [C, List.mem_append] at hg
    rcases hg with (h | h) | h
    · exact appendSpecs_fanin _ _ g h
    · exact hnl_fanin g h
    · exact appendSpecs_fanin _ _ g h
  have hC_nl : C.gates.countP isNonlin ≤ t := by
    dsimp only [C, st1, st3, m]
    simp only [List.countP_append, appendSpecs_nonlin, hnl_nonlin]
    omega
  refine ⟨a, bank, key, name, site, side, C, tap,
    ⟨readsBack_of_list _ _ hC_rb, hC_fan⟩, hC_nl,
    fun j i => by
      have hi : k * j.val + i.val < st3.2.length := by
        rw [appendSpecs_taps_len, hout_len]; nlinarith [j.isLt, i.isLt]
      have hmem : tap j i ∈ st3.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      have hlt := appendSpecs_taps_lt _ _ _ hmem
      dsimp only [C, w2, w1, st1, st3] at hlt ⊢
      simp only [List.length_append]
      omega,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l)) ++
    List.ofFn (side x)
  have hdata_len : data.length = a + b := by simp [data]
  set v1 := wiresFrom st1.1 data
  have hv1_len : v1.length = w1 := by rw [length_wiresFrom, hdata_len]
  set v2 := wiresFrom nlGates v1
  have hv2_len : v2.length = w2 := by rw [length_wiresFrom, hv1_len]

  have hv1_R0 : ∀ (j0 : Fin n) (q : Fin k),
      v1.getD (tapR0 j0 q) false = wMix k hk0 1 (wRot k hk0 1 (x j0)) q := by
    intro j0 q
    have hidx : k * j0.val + q.val < r0Specs.length := by rw [hr0_len]; nlinarith [j0.isLt, q.isLt]
    have hev := appendSpecs_eval r0Specs data (by simpa [hdata_len] using hr0_lt) (k * j0.val + q.val) hidx
    rw [hdata_len] at hev
    change v1.getD (tapR0 j0 q) false = _
    rw [hev]
    have hspec_at : r0Specs[k * j0.val + q.val] =
        (true, [2 * (j0.val * k + (q.val + k - 2) % k), 2 * (j0.val * k + (q.val + k - 2) % k) + 1]) := by
      have h := flatMap_const_getElem n k
        (fun j0 => (List.finRange k).map (fun q =>
          (true, [2 * (j0.val * k + (q.val + k - 2) % k), 2 * (j0.val * k + (q.val + k - 2) % k) + 1])))
        (fun _ => by simp) j0 q
      simpa [r0Specs] using h
    rw [hspec_at]
    simp only [List.foldr_cons, List.foldr_nil]
    set r := (q.val + k - 2) % k
    have hr : r < k := Nat.mod_lt _ hk0
    have hlt1 : 2 * (j0.val * k + r) < a := by
      have : j0.val * k + r < n * k := by
        calc j0.val * k + r < j0.val * k + k := by omega
          _ = (j0.val + 1) * k := by ring
          _ ≤ n * k := Nat.mul_le_mul_right k j0.isLt
      omega
    have hlt2 : 2 * (j0.val * k + r) + 1 < a := by omega
    simp only [data]
    rw [List.getD_append _ _ _ _ (by simp [hlt1]), getD_ofFn_lt _ _ _ hlt1,
        List.getD_append _ _ _ _ (by simp [hlt2]), getD_ofFn_lt _ _ _ hlt2]
    have hk1 : key ⟨2 * (j0.val * k + r), hlt1⟩ = j0 := by
      apply Fin.ext; simp only [key]
      have hdiv : 2 * (j0.val * k + r) / 2 = j0.val * k + r := by omega
      rw [hdiv, Nat.mul_comm j0.val k, Nat.mul_add_div hk0, Nat.div_eq_of_lt hr, add_zero]
    have hk2 : key ⟨2 * (j0.val * k + r) + 1, hlt2⟩ = j0 := by
      apply Fin.ext; simp only [key]
      have hdiv : (2 * (j0.val * k + r) + 1) / 2 = j0.val * k + r := by omega
      rw [hdiv, Nat.mul_comm j0.val k, Nat.mul_add_div hk0, Nat.div_eq_of_lt hr, add_zero]
    have hs1 : site ⟨2 * (j0.val * k + r), hlt1⟩ = ⟨r, hr⟩ := by
      apply Fin.ext; simp only [site]
      have hdiv : 2 * (j0.val * k + r) / 2 = j0.val * k + r := by omega
      rw [hdiv, Nat.mul_add_mod_of_lt hr]
    have hs2 : site ⟨2 * (j0.val * k + r) + 1, hlt2⟩ = ⟨r, hr⟩ := by
      apply Fin.ext; simp only [site]
      have hdiv : (2 * (j0.val * k + r) + 1) / 2 = j0.val * k + r := by omega
      rw [hdiv, Nat.mul_add_mod_of_lt hr]
    have hn1 : name ⟨2 * (j0.val * k + r), hlt1⟩ = singleBit k ⟨r, hr⟩ := by simp [name, hs1]
    have hn2 : name ⟨2 * (j0.val * k + r) + 1, hlt2⟩ = (fun _ => false) := by simp [name]
    rw [hk1, hk2, hs1, hs2, hn1, hn2]
    have hrd := rowDiff_ge4 k hk4 (x j0) ⟨r, hr⟩
    dsimp only at hrd
    have hq_eq : ix k hk0 (r + 2) = q := Fin.ext (by
      simp only [ix, r]
      rw [mod_add_cancel, show q.val + k - 2 + 2 = q.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt q.isLt])
    rw [hq_eq] at hrd
    have hxor_t : ∀ u v : Bool, xor u (xor v true) = !(xor u v) := by
      intro u v; cases u <;> cases v <;> rfl
    rw [hxor_t, hrd, Bool.not_not]

  have hv2_nl : ∀ (d : ℕ) (hd : d < m),
      let p := b + d
      let j0 : Fin n := ⟨p / 2, by omega⟩
      let r1 : Fin k := ix k hk0 (p % 2 + 1)
      let r2 : Fin k := ix k hk0 (p % 2 + 2)
      v2.getD (w1 + 2 * d + 1) false =
        (!(wMix k hk0 1 (wRot k hk0 1 (x j0)) r1) && wMix k hk0 1 (wRot k hk0 1 (x j0)) r2) := by
    intro d hd
    have hsplit : List.range m = List.range d ++ d :: (List.range (m - d - 1)).map (fun z => d + 1 + z) := by
      have h1 : m = d + 1 + (m - d - 1) := by omega
      conv_lhs => rw [h1, List.range_add, List.range_succ]
      simp [List.append_assoc]
    have hnl_split : nlGates =
        ((List.range d).flatMap nlGatePair) ++
        [mkNot (tapR0 ⟨(b + d) / 2, by omega⟩ (ix k hk0 ((b + d) % 2 + 1))),
         mkAnd (w1 + 2 * d) (tapR0 ⟨(b + d) / 2, by omega⟩ (ix k hk0 ((b + d) % 2 + 2)))] ++
        (((List.range (m - d - 1)).map (fun z => d + 1 + z)).flatMap nlGatePair) := by
      dsimp only [nlGates]
      conv_lhs => rw [hsplit]
      simp [List.flatMap_append, List.flatMap_cons, List.append_assoc, nlGatePair, hd]
    set gPre := (List.range d).flatMap nlGatePair
    have hgPre_len : gPre.length = 2 * d := by
      have h2 : ∀ d', (nlGatePair d').length = 2 := by intro d'; dsimp only [nlGatePair]; split_ifs <;> rfl
      simp [gPre, List.length_flatMap, h2]; omega
    set vPre := wiresFrom gPre v1
    have hvPre_len : vPre.length = w1 + 2 * d := by rw [length_wiresFrom, hv1_len, hgPre_len]
    change (wiresFrom nlGates v1).getD (w1 + 2 * d + 1) false = _
    rw [hnl_split, wiresFrom_append, wiresFrom_append]
    set j0 : Fin n := ⟨(b + d) / 2, by omega⟩
    set r1 : Fin k := ix k hk0 ((b + d) % 2 + 1)
    set r2 : Fin k := ix k hk0 ((b + d) % 2 + 2)
    set vMid := wiresFrom [mkNot (tapR0 j0 r1), mkAnd (w1 + 2 * d) (tapR0 j0 r2)] vPre
    have hvMid_len : vMid.length = w1 + 2 * d + 2 := by rw [length_wiresFrom, hvPre_len]; simp
    rw [getD_wiresFrom_lt _ vMid (w1 + 2 * d + 1) (by omega)]
    simp only [vMid, wiresFrom_cons, wiresFrom_nil]
    have hlen_not : (vPre ++ [(mkNot (tapR0 j0 r1)).op.eval
        ((mkNot (tapR0 j0 r1)).inputs.map fun i => vPre.getD i false)]).length = w1 + 2 * d + 1 := by
      simp [hvPre_len]
    rw [← hlen_not, getD_snoc_self, eval_mkAnd]
    have hget1 : (vPre ++ [(mkNot (tapR0 j0 r1)).op.eval
        ((mkNot (tapR0 j0 r1)).inputs.map fun i => vPre.getD i false)]).getD (w1 + 2 * d) false =
        !(wMix k hk0 1 (wRot k hk0 1 (x j0)) r1) := by
      rw [← hvPre_len, getD_snoc_self, eval_mkNot]
      rw [getD_wiresFrom_lt gPre v1 _ (by rw [hv1_len]; exact htapR0_lt j0 r1), hv1_R0]
    have hget2 : (vPre ++ [(mkNot (tapR0 j0 r1)).op.eval
        ((mkNot (tapR0 j0 r1)).inputs.map fun i => vPre.getD i false)]).getD (tapR0 j0 r2) false =
        wMix k hk0 1 (wRot k hk0 1 (x j0)) r2 := by
      have hlt : tapR0 j0 r2 < vPre.length := by rw [hvPre_len]; have := htapR0_lt j0 r2; omega
      rw [List.getD_append _ _ _ _ hlt, getD_wiresFrom_lt gPre v1 _ (by rw [hv1_len]; exact htapR0_lt j0 r2), hv1_R0]
    rw [hget1, hget2]

  have hv2_anc : ∀ (r : Fin 2),
      (anchorWires j r).foldr (fun w acc => xor (v2.getD w false) acc) false = x j ⟨r.val, by omega⟩ := by
    intro r
    dsimp only [anchorWires]
    split_ifs with hpb
    · simp only [List.foldr_cons, List.foldr_nil, Bool.xor_false]
      have hlt_d : a + (2 * j.val + r.val) < data.length := by rw [hdata_len]; omega
      rw [getD_wiresFrom_lt nlGates v1 _ (by rw [hv1_len]; omega),
          getD_wiresFrom_lt st1.1 data _ hlt_d]
      simp only [data]
      rw [List.getD_append_right _ _ _ _ (by simp [List.length_ofFn])]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [getD_ofFn_lt _ _ _ hpb]
      simp only [side]
      have hlt2n : 2 * j.val + r.val < 2 * n := by omega
      simp only [hlt2n, ↓reduceDIte]
      have hj_eq : (⟨(2 * j.val + r.val) / 2, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
      have hr_eq : (⟨(2 * j.val + r.val) % 2, by omega⟩ : Fin k) = ⟨r.val, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj_eq, hr_eq]
    · simp only [List.foldr_cons, List.foldr_nil, Bool.xor_false]
      have hlt_a : 2 * (j.val * k + r.val) + 1 < a := by
        have : j.val * k + r.val < n * k := by
          calc j.val * k + r.val < j.val * k + k := by omega
            _ = (j.val + 1) * k := by ring
            _ ≤ n * k := Nat.mul_le_mul_right k j.isLt
        omega
      have h1 : v2.getD (2 * (j.val * k + r.val) + 1) false =
          readBit k hk0 false (fun _ => false) (x j) ⟨r.val, by omega⟩ := by
        rw [getD_wiresFrom_lt nlGates v1 _ (by rw [hv1_len]; omega),
            getD_wiresFrom_lt st1.1 data _ (by rw [hdata_len]; omega)]
        simp only [data]
        rw [List.getD_append _ _ _ _ (by simp [hlt_a]), getD_ofFn_lt _ _ _ hlt_a]
        have hk1 : key ⟨2 * (j.val * k + r.val) + 1, hlt_a⟩ = j := by
          apply Fin.ext; simp only [key]
          have hdiv : (2 * (j.val * k + r.val) + 1) / 2 = j.val * k + r.val := by omega
          rw [hdiv, Nat.mul_comm j.val k, Nat.mul_add_div hk0, Nat.div_eq_of_lt (by omega : r.val < k), add_zero]
        have hs1 : site ⟨2 * (j.val * k + r.val) + 1, hlt_a⟩ = ⟨r.val, by omega⟩ := by
          apply Fin.ext; simp only [site]
          have hdiv : (2 * (j.val * k + r.val) + 1) / 2 = j.val * k + r.val := by omega
          rw [hdiv, Nat.mul_add_mod_of_lt (by omega : r.val < k)]
        have hn1 : name ⟨2 * (j.val * k + r.val) + 1, hlt_a⟩ = (fun _ => false) := by simp [name]
        rw [hk1, hs1, hn1]
      have h2 : v2.getD (tapR0 j ⟨r.val, by omega⟩) false =
          wMix k hk0 1 (wRot k hk0 1 (x j)) ⟨r.val, by omega⟩ := by
        rw [getD_wiresFrom_lt nlGates v1 _ (by rw [hv1_len]; exact htapR0_lt _ _), hv1_R0]
      have hd_lt : 2 * j.val + r.val - b < m := by omega
      have h3 := hv2_nl (2 * j.val + r.val - b) hd_lt
      have hp_eq : b + (2 * j.val + r.val - b) = 2 * j.val + r.val := by omega
      have hrlt := r.isLt
      have hj_eq : (⟨(b + (2 * j.val + r.val - b)) / 2, by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
      have hr1_eq : ix k hk0 ((b + (2 * j.val + r.val - b)) % 2 + 1) = ix k hk0 (r.val + 1) := by
        congr 1; omega
      have hr2_eq : ix k hk0 ((b + (2 * j.val + r.val - b)) % 2 + 2) = ix k hk0 (r.val + 2) := by
        congr 1; omega
      rw [h1, h2, h3, hj_eq, hr1_eq, hr2_eq]
      exact readBit_row_zero_recover k hk0 (x j) ⟨r.val, by omega⟩

  change (wiresFrom (st1.1 ++ nlGates ++ st3.1) data).getD (tap j i) false = x j i
  rw [wiresFrom_append, wiresFrom_append]
  have hidx : k * j.val + i.val < outSpecs.length := by rw [hout_len]; nlinarith [j.isLt, i.isLt]
  have hev := appendSpecs_eval outSpecs v2 (by simpa [hv2_len] using hout_lt) (k * j.val + i.val) hidx
  rw [hv2_len] at hev
  rw [hev]
  have hspec_at : outSpecs[k * j.val + i.val] =
      (false, (if recAnchor0 i.val then anchorWires j 0 else []) ++
              (if recAnchor1 i.val then anchorWires j 1 else []) ++
              (recR0Indices k hk0 i.val).map (tapR0 j)) := by
    have h := flatMap_const_getElem n k
      (fun j => (List.finRange k).map (fun i =>
        (false, (if recAnchor0 i.val then anchorWires j 0 else []) ++
                (if recAnchor1 i.val then anchorWires j 1 else []) ++
                (recR0Indices k hk0 i.val).map (tapR0 j))))
      (fun _ => by simp) j i
    simpa [outSpecs] using h
  rw [hspec_at]
  have hfold_app : ∀ (l1 l2 : List ℕ) (c : Bool),
      (l1 ++ l2).foldr (fun w acc => xor (v2.getD w false) acc) c =
        xor (l1.foldr (fun w acc => xor (v2.getD w false) acc) false)
            (l2.foldr (fun w acc => xor (v2.getD w false) acc) c) := by
    intro l1 l2 c
    induction l1 with
    | nil => simp
    | cons w l1 ih =>
      simp only [List.cons_append, List.foldr_cons, ih]
      cases v2.getD w false <;> cases l1.foldr (fun w acc => xor (v2.getD w false) acc) false <;>
      cases l2.foldr (fun w acc => xor (v2.getD w false) acc) c <;> rfl
  rw [hfold_app, hfold_app]
  have h0 : (if recAnchor0 i.val then anchorWires j 0 else []).foldr (fun w acc => xor (v2.getD w false) acc) false =
      if recAnchor0 i.val then x j ⟨0, hk0⟩ else false := by
    split_ifs <;> [exact hv2_anc 0; rfl]
  have h1 : (if recAnchor1 i.val then anchorWires j 1 else []).foldr (fun w acc => xor (v2.getD w false) acc) false =
      if recAnchor1 i.val then x j ⟨1, by omega⟩ else false := by
    split_ifs <;> [exact hv2_anc 1; rfl]
  have hR : ((recR0Indices k hk0 i.val).map (tapR0 j)).foldr (fun w acc => xor (v2.getD w false) acc) false =
      (recR0Indices k hk0 i.val).foldr (fun q acc => xor (wMix k hk0 1 (wRot k hk0 1 (x j)) q) acc) false := by
    induction recR0Indices k hk0 i.val with
    | nil => rfl
    | cons q qs ih =>
      simp only [List.map_cons, List.foldr_cons, ih]
      rw [getD_wiresFrom_lt nlGates v1 _ (by rw [hv1_len]; exact htapR0_lt _ _), hv1_R0]
  rw [h0, h1, hR]
  have hrec := rec_correct k hk2 (x j) i.val i.isLt
  have hassoc : ∀ a b c : Bool, xor (xor a b) c = xor a (xor b c) := by
    intro a b c; cases a <;> cases b <;> cases c <;> rfl
  rw [hassoc, hrec]

lemma main_proof :
    ∀ (k : ℕ) (hk : 0 < k),
      ∀ (n b t : ℕ),
        (∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
            (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
            (side : (Fin n → Fin k → Bool) → Fin b → Bool) (C : Circuit)
            (tap : Fin n → Fin k → ℕ),
          ValidCirc (a + b) C ∧ C.gates.countP isNonlin ≤ t ∧
          (∀ j i, tap j i < a + b + C.gates.length) ∧
          ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
            let data := List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l)) ++
              List.ofFn (side x)
            (C.wires data).getD (tap j i) false = x j i) ↔
          (if k = 1 ∨ k = 3 then n ≤ b else n * lossVal k ≤ b + t) := by
  intro k hk n b t
  constructor
  · intro h
    split_ifs with h13
    · exact lower_k1_or_k3 k hk h13 n b t h
    · unfold lossVal
      split_ifs with h93
      · exact lower_ge9_div3 k h93.1 h93.2 n b t h
      · simp
  · intro h
    by_cases hk1 : k = 1
    · subst hk1; simp at h; exact upper_k1 n b t h
    · by_cases hk3 : k = 3
      · subst hk3; simp at h; exact upper_k3 n b t h
      · have hnot13 : ¬(k = 1 ∨ k = 3) := by omega
        simp only [hnot13, ↓reduceIte, lossVal] at h
        by_cases hk2 : k = 2
        · subst hk2; exact upper_k2 n b t
        · have hk4 : 4 ≤ k := by omega
          by_cases h3 : 3 ∣ k
          · by_cases hk6 : k = 6
            · subst hk6; exact upper_k6 n b t
            · have hk9 : 9 ≤ k := by omega
              simp only [hk9, h3, and_self, ↓reduceIte] at h
              exact upper_ge9_div3 k hk9 n b t h
          · exact upper_ge4_ndiv3 k hk4 h3 n b t

end PEqualNP.Outside.L_meta_42705_aux

theorem PEqualNP.Outside.L_meta_42705 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  PEqualNP.MetaComplexity.NestedCover.ReadsBack w C ∧
  ∀ g ∈ C.gates, g.inputs.length ≤ 2
∀ (k : Nat) (hk : 0 < k),
  let W := Fin k → Bool
  let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
  let rot := fun (s : Nat) (w : W) (i : Fin k) => w (ix (i.val+k-s % k))
  let mix := fun (d : Nat) (w : W) (i : Fin k) =>
    xor (w (ix (i.val+k-d % k))) (xor (w i) (w (ix (i.val+d))))
  let readBit := fun (col : Bool) (u x : W) (i : Fin k) =>
    let d := if col then 2 else 1
    let R := mix d (add u (rot (if col then 3 else 1) x))
    xor (rot (if col then 4 else 0) x i)
      (xor (R i) (!(R (ix (i.val+1))) && R (ix (i.val+2))))
  let loss := if 9 ≤ k ∧ 3 ∣ k then 2 else 0
  ∀ (n b t : Nat),
    let U := Fin n → W
    (∃ (a : Nat) (bank : Fin a → Bool) (key : Fin a → Fin n)
        (name : Fin a → W) (site : Fin a → Fin k)
        (side : U → Fin b → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
        (tap : Fin n → Fin k → Nat),
      valid (a+b) C ∧ C.gates.countP nonlinear ≤ t ∧
      (∀ j i, tap j i < a+b+C.gates.length) ∧
      ∀ (x : U) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit (bank l) (name l) (x (key l)) (site l)) ++ List.ofFn (side x)
        (C.wires data).getD (tap j i) false = x j i) ↔
      (if k = 1 ∨ k = 3 then n ≤ b else n*loss ≤ b+t)) :=
  PEqualNP.Outside.L_meta_42705_aux.main_proof
