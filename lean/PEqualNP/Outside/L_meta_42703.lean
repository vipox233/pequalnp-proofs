import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42703_aux

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

def dVal (k : ℕ) : ℕ :=
  k - lossVal k

def priceVal (k : ℕ) : ℕ :=
  if k = 6 then 7 else dVal k + (dVal k + 1) / 2

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

lemma wiresFrom_tail (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_tail gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_tail gs w
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

lemma mod_ne_of_lt3 (k a b : ℕ) (ha : a < 3 * k) (hb : b < 3 * k)
    (h : a ≠ b ∧ a ≠ b + k ∧ a ≠ b + 2 * k ∧ b ≠ a + k ∧ b ≠ a + 2 * k) : a % k ≠ b % k := by
  rw [mod_of_lt_three k a ha, mod_of_lt_three k b hb]
  split_ifs <;> omega

lemma mod_eq_imp_diff (k a b : ℕ) (ha : a < 3 * k) (hb : b < 3 * k) (h : a % k = b % k) :
    a = b ∨ a = b + k ∨ a = b + 2 * k ∨ b = a + k ∨ b = a + 2 * k := by
  rw [mod_of_lt_three k a ha, mod_of_lt_three k b hb] at h
  split_ifs at h <;> omega

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

lemma lower_imposs_k13 (k : ℕ) (hk : 0 < k) (hk13 : k = 1 ∨ k = 3) (n : ℕ) (hn : 0 < n)
    (h : ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
        (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
        (C : Circuit) (tap : Fin n → Fin k → ℕ),
      ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal k ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i) : False := by
  obtain ⟨a, bank, key, name, site, C, tap, _, _, _, hdec⟩ := h
  let x0 : Fin n → Fin k → Bool := fun _ _ => false
  let x1 : Fin n → Fin k → Bool := fun _ _ => true
  have hdata :
      List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x0 (key l)) (site l)) =
      List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x1 (key l)) (site l)) := by
    congr 1
    funext l
    rcases hk13 with rfl | rfl
    · simp [readBit_const_k1]
    · exact (readBit_const_k3 (bank l) (name l) true (site l)).symm
  have h0 := hdec x0 ⟨0, hn⟩ ⟨0, hk⟩
  have h1 := hdec x1 ⟨0, hn⟩ ⟨0, hk⟩
  dsimp only [x0, x1] at h0 h1
  rw [hdata] at h0
  have heq : false = true := h0.symm.trans h1
  cases heq

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

lemma mix_rot_shift_eq_false (k : ℕ) (hk : 9 ≤ k) (d s : ℕ) (hd0 : 1 ≤ d) (hd : d ≤ 2) (hs : s ≤ 3)
    (a b : ℕ)
    (h1 : (a + s + d) % k ≠ b % k) (h2 : (a + s) % k ≠ b % k) (h3 : (a + s) % k ≠ (b + d) % k) :
    have hk0 : 0 < k := by omega
    wMix k hk0 d (wRot k hk0 s (singleBit k (ix k hk0 a))) (ix k hk0 b) = false := by
  dsimp only
  have hm := mix_rot_shift k hk d s hd0 hd hs a b
  dsimp only at hm
  rw [hm]; simp [h1, h2, h3]

lemma deriv2_dist5 {n k : ℕ} (hk : 9 ≤ k) (hne10 : k ≠ 10) (col : Bool) (u : Fin k → Bool)
    (j : Fin n) (i0 i : Fin k) :
    have hk0 : 0 < k := by omega
    deriv2 (fun x : Fin n → Fin k → Bool => b2z (readBit k hk0 col u (x j) i0))
      j (ix k hk0 (i.val + k - 4)) (ix k hk0 (i.val + 1)) =
      if col = true ∧ i0 = i then 1 else 0 := by
  dsimp only
  have hk0 : 0 < k := by omega
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
        apply mix_rot_shift_eq_false k hk 2 3 (by omega) (by omega) (by omega) <;>
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
      apply mix_rot_shift_eq_false k hk 1 1 (by omega) (by omega) (by omega) <;>
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

def constOneW (k : ℕ) : (Fin k → Bool) → ZMod 2 := fun _ => 1

def coordW (k : ℕ) (i : Fin k) : (Fin k → Bool) → ZMod 2 := fun w => b2z (w i)

def rbW (k : ℕ) (hk : 0 < k) (col : Bool) (u : Fin k → Bool) (s : Fin k) :
    (Fin k → Bool) → ZMod 2 :=
  fun w => b2z (readBit k hk col u w s)

def rb0 (k : ℕ) (hk : 0 < k) (col : Bool) (s : Fin k) : (Fin k → Bool) → ZMod 2 :=
  rbW k hk col (fun _ => false) s

def L1_W (k : ℕ) (hk : 0 < k) (col : Bool) (s : Fin k) : (Fin k → Bool) → ZMod 2 :=
  fun w => b2z (wMix k hk (if col then 2 else 1) (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 1)))

def L2_W (k : ℕ) (hk : 0 < k) (col : Bool) (s : Fin k) : (Fin k → Bool) → ZMod 2 :=
  fun w => b2z (wMix k hk (if col then 2 else 1) (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 2)))

lemma rbDiff_decomp (k : ℕ) (hk : 0 < k) (col : Bool) (u : Fin k → Bool) (s : Fin k) :
    let d := if col then 2 else 1
    let u0 := b2z (wMix k hk d u s)
    let u1 := b2z (wMix k hk d u (ix k hk (s.val + 1)))
    let u2 := b2z (wMix k hk d u (ix k hk (s.val + 2)))
    rbW k hk col u s + rb0 k hk col s =
      (u0 + (1 + u1) * u2) • constOneW k + u2 • L1_W k hk col s + u1 • L2_W k hk col s := by
  intro d u0 u1 u2
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, rbW, rb0, constOneW, L1_W, L2_W, mul_one,
    readBit, b2z_xor, b2z_and, b2z_not, wMix_add, wMix_zero, Bool.false_xor]
  change (b2z (wRot k hk (if col then 4 else 0) w s) +
      (u0 + b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) s) +
        (1 + (u1 + b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 1))))) *
        (u2 + b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 2)))))) +
    (b2z (wRot k hk (if col then 4 else 0) w s) +
      (b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) s) +
        (1 + b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 1)))) *
        b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 2))))) =
    u0 + (1 + u1) * u2 +
      u2 * b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 1))) +
      u1 * b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 2)))
  generalize b2z (wRot k hk (if col then 4 else 0) w s) = r4
  generalize b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) s) = r0
  generalize b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 1))) = l1
  generalize b2z (wMix k hk d (wRot k hk (if col then 3 else 1) w) (ix k hk (s.val + 2))) = l2
  have h2z : (2 : ZMod 2) = 0 := by decide
  apply sub_eq_zero.mp
  ring_nf
  simp [h2z]

def D2W (k : ℕ) : ((Fin k → Bool) → ZMod 2) →ₗ[ZMod 2] (Fin k → Fin k → ZMod 2) where
  toFun f p q :=
    f (fun _ => false) + f (singleBit k p) + f (singleBit k q) + f (wAdd (singleBit k p) (singleBit k q))
  map_add' f g := by funext p q; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext p q; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

lemma D2W_diag (k : ℕ) (f : (Fin k → Bool) → ZMod 2) (p : Fin k) :
    D2W k f p p = 0 := by
  simp only [D2W, LinearMap.coe_mk, AddHom.coe_mk]
  have hpp : wAdd (singleBit k p) (singleBit k p) = fun _ => false := by
    funext r; simp only [wAdd, singleBit]; cases decide (r = p) <;> rfl
  rw [hpp]
  generalize f (fun _ => false) = a
  generalize f (singleBit k p) = b
  revert a b; decide

lemma D2W_eq_deriv2 (k : ℕ) (f : (Fin k → Bool) → ZMod 2) (p q : Fin k) (hpq : p ≠ q) :
    D2W k f p q = deriv2 (n := 1) (fun x : Fin 1 → Fin k → Bool => f (x 0)) 0 p q := by
  simp only [D2W, LinearMap.coe_mk, AddHom.coe_mk, deriv2]
  have hp : updBit (fun _ _ => false) (0 : Fin 1) p 0 = singleBit k p := by
    funext r; simp [updBit, singleBit]
  have hq : updBit (fun _ _ => false) (0 : Fin 1) q 0 = singleBit k q := by
    funext r; simp [updBit, singleBit]
  have hpq' : updBit (updBit (fun _ _ => false) (0 : Fin 1) p) 0 q 0 = wAdd (singleBit k p) (singleBit k q) := by
    funext r; simp only [updBit, wAdd, singleBit]
    by_cases hrp : r = p <;> by_cases hrq : r = q
    · exact absurd (hrp.symm.trans hrq) hpq
    · simp [hrp, hrq]
    · simp [hrp, hrq]
    · simp [hrp, hrq]
  rw [hp, hq, hpq']

lemma D2W_constOneW (k : ℕ) : D2W k (constOneW k) = 0 := by
  funext p q; simp only [D2W, LinearMap.coe_mk, AddHom.coe_mk, constOneW, Pi.zero_apply]; decide

lemma D2W_coordW (k : ℕ) (i : Fin k) : D2W k (coordW k i) = 0 := by
  funext p q
  by_cases hpq : p = q
  · subst hpq; exact D2W_diag k (coordW k i) p
  · rw [D2W_eq_deriv2 k (coordW k i) p q hpq]
    exact deriv2_coord (n := 1) 0 0 i p q

lemma D2W_rbW_eq_rb0 (k : ℕ) (hk : 0 < k) (col : Bool) (u : Fin k → Bool) (s : Fin k) :
    D2W k (rbW k hk col u s) = D2W k (rb0 k hk col s) := by
  funext p q
  by_cases hpq : p = q
  · subst hpq; rw [D2W_diag, D2W_diag]
  · rw [D2W_eq_deriv2 k _ p q hpq, D2W_eq_deriv2 k _ p q hpq]
    exact deriv2_readBit_indep_u (n := 1) hk col u (fun _ => false) 0 0 s p q hpq

def d2wFast (k : ℕ) (hk : 0 < k) (col : Bool) (s p q : Fin k) : ZMod 2 :=
  let d := if col then 2 else 1
  let sh := if col then 3 else 1
  let ap := b2z (wMix k hk d (wRot k hk sh (singleBit k p)) (ix k hk (s.val + 1)))
  let aq := b2z (wMix k hk d (wRot k hk sh (singleBit k q)) (ix k hk (s.val + 1)))
  let bp := b2z (wMix k hk d (wRot k hk sh (singleBit k p)) (ix k hk (s.val + 2)))
  let bq := b2z (wMix k hk d (wRot k hk sh (singleBit k q)) (ix k hk (s.val + 2)))
  ap * bq + aq * bp

lemma D2W_rb0_eq_fast (k : ℕ) (hk : 0 < k) (col : Bool) (s p q : Fin k) (hpq : p ≠ q) :
    D2W k (rb0 k hk col s) p q = d2wFast k hk col s p q := by
  rw [D2W_eq_deriv2 k _ p q hpq]
  exact deriv2_readBit_eq_key (n := 1) hk col (fun _ => false) 0 s p q hpq

lemma d2wFast_nonzero_k2 : ∀ (col : Bool) (s : Fin 2), ∃ p q : Fin 2, p ≠ q ∧ d2wFast 2 (by omega) col s p q ≠ 0 := by
  decide +kernel

lemma d2wFast_nonzero_k4 : ∀ (col : Bool) (s : Fin 4), ∃ p q : Fin 4, p ≠ q ∧ d2wFast 4 (by omega) col s p q ≠ 0 := by
  decide +kernel

lemma d2wFast_nonzero_k6 : ∀ (col : Bool) (s : Fin 6), ∃ p q : Fin 6, p ≠ q ∧ d2wFast 6 (by omega) col s p q ≠ 0 := by
  decide +kernel

lemma d2wFast_inj_k4 :
    ∀ (c1 c2 : Bool) (s1 s2 : Fin 4),
      (∀ p q : Fin 4, p ≠ q → d2wFast 4 (by omega) c1 s1 p q = d2wFast 4 (by omega) c2 s2 p q) →
        c1 = c2 ∧ s1 = s2 := by
  decide +kernel

def bsIdx (k : ℕ) (bs : Bool × Fin k) : Fin (2 * k) :=
  if bs.1 then ⟨k + bs.2.val, by omega⟩ else ⟨bs.2.val, by omega⟩

def P5 : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
def M5 : Fin 10 → ℕ :=
  ![383, 503, 1014, 1006, 879, 625, 410, 677, 856, 143]

def P7 : Fin 14 → Fin 7 × Fin 7 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,5),(2,6),(3,4),(3,6)]
def M7 : Fin 14 → ℕ :=
  ![2494, 4005, 16036, 13469, 10200, 16203, 14687, 12609, 2075, 261, 2208, 1540, 12416, 1561]

def P8 : Fin 16 → Fin 8 × Fin 8 :=
  ![(0,1),(0,2),(0,3),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,6),(1,7),(2,3),(2,4),(2,5),(3,4),(4,5)]
def M8 : Fin 16 → ℕ :=
  ![12189, 12191, 12063, 16159, 29402, 35736, 11149, 11165, 897, 10295, 1387, 10947, 29, 1856, 12405, 46]

def P10 : Fin 20 → Fin 10 × Fin 10 :=
  ![(0,1),(0,2),(0,3),(0,5),(0,7),(0,8),(1,2),(1,3),(1,4),(1,6),(1,8),(2,3),(2,4),(2,9),(3,4),(3,5),(4,5),(4,6),(5,6),(6,7)]
def M10 : Fin 20 → ℕ :=
  ![9598, 9596, 9724, 13820, 46588, 177660, 472564, 604148, 10143, 10175, 1921, 8251, 1029, 8512, 61, 1409, 14457, 52357, 225600, 53]

lemma P5_ne : ∀ t : Fin 10, (P5 t).1 ≠ (P5 t).2 := by decide +kernel
lemma inv_k5 : ∀ bs1 bs2 : Bool × Fin 5,
    (∑ t : Fin 10, b2z ((M5 (bsIdx 5 bs1)).testBit t.val) * d2wFast 5 (by omega) bs2.1 bs2.2 (P5 t).1 (P5 t).2) =
      if bs1 = bs2 then 1 else 0 := by decide +kernel

lemma P7_ne : ∀ t : Fin 14, (P7 t).1 ≠ (P7 t).2 := by decide +kernel
lemma inv_k7 : ∀ bs1 bs2 : Bool × Fin 7,
    (∑ t : Fin 14, b2z ((M7 (bsIdx 7 bs1)).testBit t.val) * d2wFast 7 (by omega) bs2.1 bs2.2 (P7 t).1 (P7 t).2) =
      if bs1 = bs2 then 1 else 0 := by decide +kernel

lemma P8_ne : ∀ t : Fin 16, (P8 t).1 ≠ (P8 t).2 := by decide +kernel
lemma inv_k8 : ∀ bs1 bs2 : Bool × Fin 8,
    (∑ t : Fin 16, b2z ((M8 (bsIdx 8 bs1)).testBit t.val) * d2wFast 8 (by omega) bs2.1 bs2.2 (P8 t).1 (P8 t).2) =
      if bs1 = bs2 then 1 else 0 := by decide +kernel

lemma P10_ne : ∀ t : Fin 20, (P10 t).1 ≠ (P10 t).2 := by decide +kernel
lemma inv_k10 : ∀ bs1 bs2 : Bool × Fin 10,
    (∑ t : Fin 20, b2z ((M10 (bsIdx 10 bs1)).testBit t.val) * d2wFast 10 (by omega) bs2.1 bs2.2 (P10 t).1 (P10 t).2) =
      if bs1 = bs2 then 1 else 0 := by decide +kernel

lemma bucket_sum_zero_of_inv (k : ℕ) (hk : 0 < k) (P : Fin (2 * k) → Fin k × Fin k)
    (M : Fin (2 * k) → ℕ)
    (hPne : ∀ t, (P t).1 ≠ (P t).2)
    (hInv : ∀ bs1 bs2 : Bool × Fin k,
      (∑ t : Fin (2 * k), b2z ((M (bsIdx k bs1)).testBit t.val) * d2wFast k hk bs2.1 bs2.2 (P t).1 (P t).2) =
        if bs1 = bs2 then 1 else 0)
    (S : Bool × Fin k → ZMod 2)
    (hD : ∀ p q : Fin k, ∑ bs : Bool × Fin k, S bs * D2W k (rb0 k hk bs.1 bs.2) p q = 0)
    (bs1 : Bool × Fin k) : S bs1 = 0 := by
  have hsum0 : ∑ t : Fin (2 * k), b2z ((M (bsIdx k bs1)).testBit t.val) *
      (∑ bs2 : Bool × Fin k, S bs2 * d2wFast k hk bs2.1 bs2.2 (P t).1 (P t).2) = 0 := by
    apply Finset.sum_eq_zero
    intro t _
    have ht := hD (P t).1 (P t).2
    have hEq : ∑ bs2 : Bool × Fin k, S bs2 * d2wFast k hk bs2.1 bs2.2 (P t).1 (P t).2 =
        ∑ bs2 : Bool × Fin k, S bs2 * D2W k (rb0 k hk bs2.1 bs2.2) (P t).1 (P t).2 := by
      apply Finset.sum_congr rfl; intro bs2 _
      rw [D2W_rb0_eq_fast k hk bs2.1 bs2.2 (P t).1 (P t).2 (hPne t)]
    rw [hEq, ht, mul_zero]
  have hswap : ∑ t : Fin (2 * k), b2z ((M (bsIdx k bs1)).testBit t.val) *
      (∑ bs2 : Bool × Fin k, S bs2 * d2wFast k hk bs2.1 bs2.2 (P t).1 (P t).2) =
      ∑ bs2 : Bool × Fin k, S bs2 *
        (∑ t : Fin (2 * k), b2z ((M (bsIdx k bs1)).testBit t.val) * d2wFast k hk bs2.1 bs2.2 (P t).1 (P t).2) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro bs2 _
    apply Finset.sum_congr rfl; intro t _
    ring
  rw [hswap] at hsum0
  simp_rw [hInv bs1] at hsum0
  simpa using hsum0

lemma bucket_sum_zero (k : ℕ) (hk : 0 < k)
    (hk_case : k = 5 ∨ k = 7 ∨ k = 8 ∨ k = 10 ∨ (9 ≤ k ∧ k ≠ 10))
    (m : ℕ) (bank_j : Fin m → Bool) (name_j : Fin m → Fin k → Bool) (site_j : Fin m → Fin k)
    (coeff : Fin m → ZMod 2)
    (hD : D2W k (∑ r : Fin m, coeff r • rbW k hk (bank_j r) (name_j r) (site_j r)) = 0) :
    ∀ bs : Bool × Fin k,
      ∑ r ∈ Finset.univ.filter (fun r : Fin m => (bank_j r, site_j r) = bs), coeff r = 0 := by
  let S : Bool × Fin k → ZMod 2 := fun bs =>
    ∑ r ∈ Finset.univ.filter (fun r : Fin m => (bank_j r, site_j r) = bs), coeff r
  have hDS : ∀ p q : Fin k, ∑ bs : Bool × Fin k, S bs * D2W k (rb0 k hk bs.1 bs.2) p q = 0 := by
    intro p q
    have h0 : D2W k (∑ r : Fin m, coeff r • rbW k hk (bank_j r) (name_j r) (site_j r)) p q = 0 := by
      rw [hD]; rfl
    rw [map_sum] at h0
    simp only [LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0
    have hfiber :
        ∑ r : Fin m, coeff r * D2W k (rbW k hk (bank_j r) (name_j r) (site_j r)) p q =
        ∑ bs : Bool × Fin k,
          ∑ r ∈ Finset.univ.filter (fun r : Fin m => (bank_j r, site_j r) = bs),
            coeff r * D2W k (rbW k hk (bank_j r) (name_j r) (site_j r)) p q :=
      (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
    rw [hfiber] at h0
    have hcongr : ∀ bs : Bool × Fin k,
        ∑ r ∈ Finset.univ.filter (fun r : Fin m => (bank_j r, site_j r) = bs),
          coeff r * D2W k (rbW k hk (bank_j r) (name_j r) (site_j r)) p q =
        S bs * D2W k (rb0 k hk bs.1 bs.2) p q := by
      intro bs
      dsimp only [S]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hb : bank_j r = bs.1 := congrArg Prod.fst hr
      have hs : site_j r = bs.2 := congrArg Prod.snd hr
      rw [D2W_rbW_eq_rb0, hb, hs]
    simp_rw [hcongr] at h0
    exact h0
  rcases hk_case with rfl | rfl | rfl | rfl | ⟨hk9, hne10⟩
  · exact bucket_sum_zero_of_inv 5 hk P5 M5 P5_ne inv_k5 S hDS
  · exact bucket_sum_zero_of_inv 7 hk P7 M7 P7_ne inv_k7 S hDS
  · exact bucket_sum_zero_of_inv 8 hk P8 M8 P8_ne inv_k8 S hDS
  · exact bucket_sum_zero_of_inv 10 hk P10 M10 P10_ne inv_k10 S hDS
  · have hcol : ∀ s : Fin k, S (true, s) = 0 := by
      intro s
      have hpq : ix k hk (s.val + k - 4) ≠ ix k hk (s.val + 1) := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
        have hs := s.isLt
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h0 := hDS (ix k hk (s.val + k - 4)) (ix k hk (s.val + 1))
      have hterm : ∀ bs : Bool × Fin k,
          S bs * D2W k (rb0 k hk bs.1 bs.2) (ix k hk (s.val + k - 4)) (ix k hk (s.val + 1)) =
            if bs = (true, s) then S bs else 0 := by
        rintro ⟨col, i0⟩
        rw [D2W_eq_deriv2 k _ _ _ hpq]
        have hd5 := deriv2_dist5 (n := 1) hk9 hne10 col (fun _ => false) 0 i0 s
        dsimp only at hd5
        change S (col, i0) * deriv2 (fun x : Fin 1 → Fin k → Bool => b2z (readBit k hk col (fun _ => false) (x 0) i0)) 0 _ _ = _
        rw [hd5]
        by_cases hc : col = true ∧ i0 = s
        · rcases hc with ⟨rfl, rfl⟩; simp
        · have hne : (col, i0) ≠ (true, s) := by intro h; exact hc ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
          simp [hc, hne]
      simp_rw [hterm] at h0
      simpa using h0
    intro bs
    rcases bs with ⟨col, s⟩
    cases col
    · have hpq : ix k hk (s.val + k - 1) ≠ ix k hk (s.val + 2) := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
        have hs := s.isLt
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h0 := hDS (ix k hk (s.val + k - 1)) (ix k hk (s.val + 2))
      have hterm : ∀ bs : Bool × Fin k,
          S bs * D2W k (rb0 k hk bs.1 bs.2) (ix k hk (s.val + k - 1)) (ix k hk (s.val + 2)) =
            if bs = (false, s) then S bs else 0 := by
        rintro ⟨col0, i0⟩
        cases col0
        · rw [D2W_eq_deriv2 k _ _ _ hpq]
          have hd3 := deriv2_dist3_row (n := 1) hk9 (fun _ => false) 0 i0 s
          dsimp only at hd3
          change S (false, i0) * deriv2 (fun x : Fin 1 → Fin k → Bool => b2z (readBit k hk false (fun _ => false) (x 0) i0)) 0 _ _ = _
          rw [hd3]
          by_cases hi : i0 = s
          · subst hi; simp
          · simp [hi]
        · rw [hcol i0, zero_mul]; simp
      simp_rw [hterm] at h0
      have h0' : S (false, s) = 0 := by simpa using h0
      exact h0'
    · exact hcol s

lemma submodule_eq_of_le_of_finrank_le {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] {S1 S2 : Submodule (ZMod 2) M}
    (hle : S1 ≤ S2) (hrank : Module.finrank (ZMod 2) S2 ≤ Module.finrank (ZMod 2) S1) : S1 = S2 := by
  by_contra hne
  have hnot : ¬(S2 ≤ S1) := fun h => hne (le_antisymm hle h)
  rw [SetLike.not_le_iff_exists] at hnot
  obtain ⟨x, hx2, hx1⟩ := hnot
  let f := S1.mkQ.domRestrict S2
  have hnz : S1.mkQ x ≠ 0 := fun h => hx1 ((Submodule.Quotient.mk_eq_zero S1).mp h)
  have hmem_range : S1.mkQ x ∈ LinearMap.range f := ⟨⟨x, hx2⟩, rfl⟩
  have hrange_ge1 : 1 ≤ Module.finrank (ZMod 2) (LinearMap.range f) := by
    have hLI1 : LinearIndependent (ZMod 2) (fun _ : Fin 1 => (⟨S1.mkQ x, hmem_range⟩ : LinearMap.range f)) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      fin_cases i
      have h1 : g 0 • S1.mkQ x = 0 := by simpa using congrArg Subtype.val hg
      have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      rcases hc (g 0) with h | h
      · exact h
      · rw [h, one_smul] at h1; exact absurd h1 hnz
    simpa [Fintype.card_fin] using hLI1.fintype_card_le_finrank
  have hker_ge : Module.finrank (ZMod 2) S1 ≤ Module.finrank (ZMod 2) (LinearMap.ker f) := by
    let emb : S1 →ₗ[ZMod 2] LinearMap.ker f :=
      { toFun := fun y => ⟨⟨y.1, hle y.2⟩, by simp [f, (Submodule.Quotient.mk_eq_zero S1).mpr y.2]⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective emb := by
      intro a b hab
      apply Subtype.ext
      exact congrArg (fun z => z.1.1) hab
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  omega

lemma finrank_finset_sup_le {ι M : Type*} [DecidableEq ι] [AddCommGroup M] [Module (ZMod 2) M]
    [Module.Finite (ZMod 2) M] (s : Finset ι) (V : ι → Submodule (ZMod 2) M) :
    Module.finrank (ZMod 2) ↥(s.sup V) ≤ ∑ i ∈ s, Module.finrank (ZMod 2) (V i) := by
  induction s using Finset.induction_on with
  | empty => simp [finrank_bot]
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.sum_insert ha]
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq (V a) (s.sup V)
    omega

lemma coordW_LI (k : ℕ) : LinearIndependent (ZMod 2) (coordW k) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg (singleBit k i)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, coordW, singleBit] at h0
  have hev : ∀ j : Fin k, g j * b2z (decide (j = i)) = if j = i then g j else 0 := by
    intro j; by_cases h : j = i <;> simp [h, b2z]
  simp_rw [hev] at h0
  simpa using h0

lemma finrank_A_W (k : ℕ) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (coordW k))) = k := by
  simpa [Fintype.card_fin] using finrank_span_eq_card (coordW_LI k)

lemma mem_A_W_zero (k : ℕ) (f : (Fin k → Bool) → ZMod 2)
    (hf : f ∈ Submodule.span (ZMod 2) (Set.range (coordW k))) : f (fun _ => false) = 0 := by
  refine Submodule.span_induction (p := fun g _ => g (fun _ => false) = 0) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨i, rfl⟩; rfl
  · rfl
  · intro x y _ _ hx hy; simp [hx, hy]
  · intro c x _ hx; simp [hx]

lemma affW_LI (k : ℕ) :
    LinearIndependent (ZMod 2) (Fin.cases (constOneW k) (coordW k) : Fin (k + 1) → (Fin k → Bool) → ZMod 2) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h0 : g 0 = 0 := by
    have hz := congrFun hg (fun _ => false)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, constOneW, coordW, b2z_false, mul_zero, mul_one,
      Finset.sum_const_zero, add_zero] at hz
    exact hz
  intro r
  cases r using Fin.cases with
  | zero => exact h0
  | succ i =>
    have hs := congrFun hg (singleBit k i)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Fin.sum_univ_succ,
      Fin.cases_zero, Fin.cases_succ, h0, zero_mul, zero_add, coordW, singleBit] at hs
    have hev : ∀ j : Fin k, g j.succ * b2z (decide (j = i)) = if j = i then g j.succ else 0 := by
      intro j; by_cases h : j = i <;> simp [h, b2z]
    simp_rw [hev] at hs
    simpa using hs

set_option maxHeartbeats 800000 in
lemma single_key_lower (k : ℕ) (hk : 0 < k) (hk1 : k ≠ 1) (hk3 : k ≠ 3)
    (m : ℕ) (bank_j : Fin m → Bool) (name_j : Fin m → Fin k → Bool) (site_j : Fin m → Fin k)
    (hA : dVal k ≤ Module.finrank (ZMod 2)
        ↥(Submodule.span (ZMod 2) (Set.range (coordW k)) ⊓
          Submodule.span (ZMod 2) (insert (constOneW k) (Set.range (fun r : Fin m => rbW k hk (bank_j r) (name_j r) (site_j r)))))) :
    priceVal k ≤ m := by
  classical
  let W := Fin k → Bool
  let A_W : Submodule (ZMod 2) (W → ZMod 2) := Submodule.span (ZMod 2) (Set.range (coordW k))
  let rb_j : Fin m → (W → ZMod 2) := fun r => rbW k hk (bank_j r) (name_j r) (site_j r)
  let B_j : Submodule (ZMod 2) (W → ZMod 2) := Submodule.span (ZMod 2) (insert (constOneW k) (Set.range rb_j))
  have hz2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  by_cases h246 : k = 2 ∨ k = 4 ∨ k = 6
  · have hd_eq : dVal k = k := by
      rcases h246 with rfl | rfl | rfl <;> decide
    have hAW_le : A_W ≤ B_j := by
      have hinf_eq : A_W ⊓ B_j = A_W := by
        apply submodule_eq_of_le_of_finrank_le inf_le_left
        rw [finrank_A_W, ← hd_eq]
        exact hA
      exact inf_eq_left.mp hinf_eq
    let affVec : Fin (k + 1) → (W → ZMod 2) := Fin.cases (constOneW k) (coordW k)
    let V_aff : Submodule (ZMod 2) (W → ZMod 2) := Submodule.span (ZMod 2) (Set.range affVec)
    have hV_rank : Module.finrank (ZMod 2) V_aff = k + 1 := by
      simpa [Fintype.card_fin] using finrank_span_eq_card (affW_LI k)
    have hV_le_B : V_aff ≤ B_j := by
      rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      cases r using Fin.cases with
      | zero => exact Submodule.subset_span (Set.mem_insert _ _)
      | succ i => exact hAW_le (Submodule.subset_span ⟨i, rfl⟩)
    have hB_rank_le : Module.finrank (ZMod 2) B_j ≤ m + 1 := by
      let S_gen : Finset (W → ZMod 2) := insert (constOneW k) (Finset.univ.image rb_j)
      have hS_eq : (S_gen : Set (W → ZMod 2)) = insert (constOneW k) (Set.range rb_j) := by
        ext f; simp [S_gen]
      have h1 : Module.finrank (ZMod 2) B_j ≤ S_gen.card := by
        have hsp : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S_gen : Set (W → ZMod 2))) ≤ S_gen.card := by
          simpa using finrank_span_le_card (R := ZMod 2) (S_gen : Set (W → ZMod 2))
        rwa [hS_eq] at hsp
      have h2 : S_gen.card ≤ (Finset.univ.image rb_j).card + 1 := Finset.card_insert_le _ _
      have h3 : (Finset.univ.image rb_j).card ≤ m := by
        simpa [Fintype.card_fin] using Finset.card_image_le (s := (Finset.univ : Finset (Fin m))) (f := rb_j)
      omega
    have hm_pos : 0 < m := by
      by_contra hm0
      have hm_eq : m = 0 := by omega
      have hle := Submodule.finrank_mono hV_le_B
      omega
    let r0 : Fin m := ⟨0, hm_pos⟩
    have hD_nz : ∀ r : Fin m, D2W k (rb_j r) ≠ 0 := by
      intro r hzero
      have hnz : ∃ p q : Fin k, p ≠ q ∧ d2wFast k hk (bank_j r) (site_j r) p q ≠ 0 := by
        rcases h246 with rfl | rfl | rfl
        · exact d2wFast_nonzero_k2 (bank_j r) (site_j r)
        · exact d2wFast_nonzero_k4 (bank_j r) (site_j r)
        · exact d2wFast_nonzero_k6 (bank_j r) (site_j r)
      obtain ⟨p, q, hpq, hne⟩ := hnz
      have h1 : D2W k (rb_j r) p q = 0 := by rw [hzero]; rfl
      rw [show rb_j r = rbW k hk (bank_j r) (name_j r) (site_j r) from rfl,
          D2W_rbW_eq_rb0, D2W_rb0_eq_fast k hk _ _ p q hpq] at h1
      exact hne h1
    have hV_le_ker : V_aff.comap B_j.subtype ≤ LinearMap.ker ((D2W k).domRestrict B_j) := by
      rintro ⟨f, hfB⟩ hfV
      simp only [Submodule.mem_comap, Submodule.coe_subtype, LinearMap.mem_ker,
        LinearMap.domRestrict_apply] at hfV ⊢
      refine Submodule.span_induction (p := fun g _ => D2W k g = 0) ?_ ?_ ?_ ?_ hfV
      · rintro _ ⟨r, rfl⟩
        cases r using Fin.cases with
        | zero => exact D2W_constOneW k
        | succ i => exact D2W_coordW k i
      · exact map_zero (D2W k)
      · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
      · intro c x _ hx; rw [map_smul, hx, smul_zero]
    have hker_ge : k + 1 ≤ Module.finrank (ZMod 2) (LinearMap.ker ((D2W k).domRestrict B_j)) := by
      have hLI_sub : LinearIndependent (ZMod 2) (fun r : Fin (k + 1) =>
          (⟨⟨affVec r, hV_le_B (Submodule.subset_span ⟨r, rfl⟩)⟩,
            hV_le_ker (Submodule.subset_span ⟨r, rfl⟩)⟩ : LinearMap.ker ((D2W k).domRestrict B_j))) := by
        apply LinearIndependent.of_comp (B_j.subtype.comp (LinearMap.ker ((D2W k).domRestrict B_j)).subtype)
        exact affW_LI k
      simpa [Fintype.card_fin] using hLI_sub.fintype_card_le_finrank
    have hrange_eq : LinearMap.range ((D2W k).domRestrict B_j) = B_j.map (D2W k) := by
      ext y; simp [Submodule.mem_map]
    have hrange_ge1 : 1 ≤ Module.finrank (ZMod 2) (B_j.map (D2W k)) := by
      have hmem : D2W k (rb_j r0) ∈ B_j.map (D2W k) :=
        ⟨rb_j r0, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨r0, rfl⟩), rfl⟩
      have hLI1 : LinearIndependent (ZMod 2) (fun _ : Fin 1 => (⟨D2W k (rb_j r0), hmem⟩ : B_j.map (D2W k))) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        fin_cases i
        have h1 : g 0 • D2W k (rb_j r0) = 0 := by
          have := congrArg Subtype.val hg
          simpa using this
        rcases hz2_cases (g 0) with h | h
        · exact h
        · rw [h, one_smul] at h1; exact absurd h1 (hD_nz r0)
      simpa [Fintype.card_fin] using hLI1.fintype_card_le_finrank
    have hrn := LinearMap.finrank_range_add_finrank_ker ((D2W k).domRestrict B_j)
    rw [hrange_eq] at hrn
    have hk1_le_m : k + 1 ≤ m := by
      have hsum : (k + 1) + 1 ≤ m + 1 :=
        calc (k + 1) + 1
            ≤ Module.finrank (ZMod 2) (LinearMap.ker ((D2W k).domRestrict B_j)) +
              Module.finrank (ZMod 2) (B_j.map (D2W k)) := Nat.add_le_add hker_ge hrange_ge1
          _ = Module.finrank (ZMod 2) (B_j.map (D2W k)) +
              Module.finrank (ZMod 2) (LinearMap.ker ((D2W k).domRestrict B_j)) := Nat.add_comm _ _
          _ = Module.finrank (ZMod 2) B_j := hrn
          _ ≤ m + 1 := hB_rank_le
      omega
    rcases h246 with rfl | rfl | rfl
    · have hp2 : priceVal 2 = 3 := by decide
      rw [hp2]; omega
    · have hprice4 : priceVal 4 = 6 := by decide
      rw [hprice4]
      by_contra hm_lt
      have hm5 : m = 5 := by omega
      have hrange_eq1 : Module.finrank (ZMod 2) (B_j.map (D2W 4)) = 1 := by
        have hle1 : Module.finrank (ZMod 2) (B_j.map (D2W 4)) + (4 + 1) ≤ 5 + 1 :=
          calc Module.finrank (ZMod 2) (B_j.map (D2W 4)) + (4 + 1)
              ≤ Module.finrank (ZMod 2) (B_j.map (D2W 4)) +
                Module.finrank (ZMod 2) (LinearMap.ker ((D2W 4).domRestrict B_j)) := Nat.add_le_add_left hker_ge _
            _ = Module.finrank (ZMod 2) B_j := hrn
            _ ≤ m + 1 := hB_rank_le
            _ = 5 + 1 := by rw [hm5]
        omega
      have hall_eq : ∀ r : Fin m, D2W 4 (rb_j r) = D2W 4 (rb_j r0) := by
        intro r
        by_contra hne
        have hmem0 : D2W 4 (rb_j r0) ∈ B_j.map (D2W 4) :=
          ⟨rb_j r0, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨r0, rfl⟩), rfl⟩
        have hmemr : D2W 4 (rb_j r) ∈ B_j.map (D2W 4) :=
          ⟨rb_j r, Submodule.subset_span (Set.mem_insert_of_mem _ ⟨r, rfl⟩), rfl⟩
        let v2 : Fin 2 → B_j.map (D2W 4) := ![⟨D2W 4 (rb_j r0), hmem0⟩, ⟨D2W 4 (rb_j r), hmemr⟩]
        have hLI2 : LinearIndependent (ZMod 2) v2 := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          have hval : g 0 • D2W 4 (rb_j r0) + g 1 • D2W 4 (rb_j r) = 0 := by
            have := congrArg Subtype.val hg
            simpa [v2, Fin.sum_univ_two] using this
          have h01 : g 0 = 0 ∧ g 1 = 0 := by
            rcases hz2_cases (g 0) with h0 | h0 <;> rcases hz2_cases (g 1) with h1 | h1
            · exact ⟨h0, h1⟩
            · rw [h0, h1, zero_smul, zero_add, one_smul] at hval; exact absurd hval (hD_nz r)
            · rw [h0, h1, one_smul, zero_smul, add_zero] at hval; exact absurd hval (hD_nz r0)
            · rw [h0, h1, one_smul, one_smul] at hval
              have heq_r : D2W 4 (rb_j r) = D2W 4 (rb_j r0) := by
                funext p q
                have hpq := congrFun (congrFun hval p) q
                simp only [Pi.add_apply, Pi.zero_apply] at hpq
                generalize D2W 4 (rb_j r0) p q = a at hpq ⊢
                generalize D2W 4 (rb_j r) p q = b at hpq ⊢
                revert a b hpq; decide
              exact absurd heq_r hne
          intro idx; fin_cases idx
          · exact h01.1
          · exact h01.2
        have h2le := hLI2.fintype_card_le_finrank
        simp only [Fintype.card_fin] at h2le
        omega
      let col0 := bank_j r0
      let s0 := site_j r0
      have hall_bs : ∀ r : Fin m, bank_j r = col0 ∧ site_j r = s0 := by
        intro r
        apply d2wFast_inj_k4 (bank_j r) col0 (site_j r) s0
        intro p q hpq
        have h1 := congrFun (congrFun (hall_eq r) p) q
        change D2W 4 (rbW 4 hk (bank_j r) (name_j r) (site_j r)) p q =
          D2W 4 (rbW 4 hk col0 (name_j r0) s0) p q at h1
        rw [D2W_rbW_eq_rb0, D2W_rbW_eq_rb0,
            D2W_rb0_eq_fast 4 hk _ _ p q hpq, D2W_rb0_eq_fast 4 hk _ _ p q hpq] at h1
        exact h1
      let S4 : Finset (W → ZMod 2) :=
        {constOneW 4, rb0 4 hk col0 s0, L1_W 4 hk col0 s0, L2_W 4 hk col0 s0}
      have hB_le_S4 : B_j ≤ Submodule.span (ZMod 2) (S4 : Set (W → ZMod 2)) := by
        rw [Submodule.span_le]
        intro f hf
        rcases hf with rfl | ⟨r, rfl⟩
        · exact Submodule.subset_span (by simp [S4])
        · obtain ⟨hb, hs⟩ := hall_bs r
          have hdec := rbDiff_decomp 4 hk col0 (name_j r) s0
          dsimp only at hdec
          have hrb_eq : rb_j r = rb0 4 hk col0 s0 + (rbW 4 hk col0 (name_j r) s0 + rb0 4 hk col0 s0) := by
            funext w
            simp only [rb_j, hb, hs, Pi.add_apply]
            generalize rbW 4 hk col0 (name_j r) s0 w = a
            generalize rb0 4 hk col0 s0 w = b
            revert a b; decide
          rw [hrb_eq, hdec]
          refine Submodule.add_mem _ (Submodule.subset_span (by simp [S4])) ?_
          refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
          · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S4]))
          · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S4]))
          · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [S4]))
      have hS4_rank : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S4 : Set (W → ZMod 2))) ≤ 4 := by
        have h1 : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S4 : Set (W → ZMod 2))) ≤ S4.card := by
          simpa using finrank_span_le_card (R := ZMod 2) (S4 : Set (W → ZMod 2))
        have h2 : S4.card ≤ 4 := by
          dsimp only [S4]
          calc ({constOneW 4, rb0 4 hk col0 s0, L1_W 4 hk col0 s0, L2_W 4 hk col0 s0} : Finset _).card
              ≤ ({rb0 4 hk col0 s0, L1_W 4 hk col0 s0, L2_W 4 hk col0 s0} : Finset _).card + 1 := Finset.card_insert_le _ _
            _ ≤ ({L1_W 4 hk col0 s0, L2_W 4 hk col0 s0} : Finset _).card + 1 + 1 := by linarith [Finset.card_insert_le (rb0 4 hk col0 s0) {L1_W 4 hk col0 s0, L2_W 4 hk col0 s0}]
            _ ≤ ({L2_W 4 hk col0 s0} : Finset _).card + 1 + 1 + 1 := by linarith [Finset.card_insert_le (L1_W 4 hk col0 s0) {L2_W 4 hk col0 s0}]
            _ = 4 := by simp
        exact le_trans h1 h2
      have h5_le_4 : 5 ≤ 4 :=
        calc 5 = Module.finrank (ZMod 2) V_aff := hV_rank.symm
          _ ≤ Module.finrank (ZMod 2) B_j := Submodule.finrank_mono hV_le_B
          _ ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S4 : Set (W → ZMod 2))) := Submodule.finrank_mono hB_le_S4
          _ ≤ 4 := hS4_rank
      omega
    · have hp6 : priceVal 6 = 7 := by decide
      rw [hp6]; omega
  · have hk_case : k = 5 ∨ k = 7 ∨ k = 8 ∨ k = 10 ∨ (9 ≤ k ∧ k ≠ 10) := by omega
    have hprice_eq : priceVal k = dVal k + (dVal k + 1) / 2 := by
      have hk6 : k ≠ 6 := by omega
      simp [priceVal, hk6]
    rw [hprice_eq]
    let C1 : Submodule (ZMod 2) (W → ZMod 2) := Submodule.span (ZMod 2) {constOneW k}
    let Q1 := C1.mkQ
    have hker_Q1 : LinearMap.ker (Q1.domRestrict (A_W ⊓ B_j)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro ⟨f, hfA, hfB⟩ hfk
      simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hfk
      dsimp only [Q1] at hfk
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfk
      rw [Submodule.mem_span_singleton] at hfk
      obtain ⟨c, rfl⟩ := hfk
      have hz := mem_A_W_zero k (c • constOneW k) hfA
      simp only [Pi.smul_apply, smul_eq_mul, constOneW, mul_one] at hz
      apply Subtype.ext
      simp [hz]
    have hd_le_Q1 : dVal k ≤ Module.finrank (ZMod 2) ((A_W ⊓ B_j).map Q1) := by
      have hrn := LinearMap.finrank_range_add_finrank_ker (Q1.domRestrict (A_W ⊓ B_j))
      have hrange : LinearMap.range (Q1.domRestrict (A_W ⊓ B_j)) = (A_W ⊓ B_j).map Q1 := by
        ext y; simp [Submodule.mem_map]
      rw [hrange, hker_Q1, finrank_bot, add_zero] at hrn
      rw [hrn]
      exact hA
    let F_bs : Bool × Fin k → Finset (Fin m) := fun bs =>
      Finset.univ.filter (fun r : Fin m => (bank_j r, site_j r) = bs)
    let V_bs : Bool × Fin k → Submodule (ZMod 2) ((W → ZMod 2) ⧸ C1) := fun bs =>
      if (F_bs bs).card ≤ 1 then ⊥
      else if h2 : (F_bs bs).card = 2 then
        let pair := Classical.choose (Finset.card_eq_two.mp h2)
        let r1 := Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp h2))
        Submodule.span (ZMod 2) {Q1 (rb_j pair + rb_j r1)}
      else
        Submodule.span (ZMod 2) (({Q1 (L1_W k hk bs.1 bs.2), Q1 (L2_W k hk bs.1 bs.2)} : Finset _) : Set _)
    have hV_bound : ∀ bs : Bool × Fin k,
        3 * Module.finrank (ZMod 2) (V_bs bs) ≤ 2 * (F_bs bs).card := by
      intro bs
      by_cases h1 : (F_bs bs).card ≤ 1
      · have hV_eq : V_bs bs = ⊥ := by dsimp only [V_bs]; exact if_pos h1
        rw [hV_eq, finrank_bot]; omega
      · by_cases h2 : (F_bs bs).card = 2
        · have hV_eq : V_bs bs = Submodule.span (ZMod 2)
              {Q1 (rb_j (Classical.choose (Finset.card_eq_two.mp h2)) +
                rb_j (Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp h2))))} := by
            dsimp only [V_bs]; rw [if_neg h1, dif_pos h2]
          rw [hV_eq]
          have hfr : Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
              {Q1 (rb_j (Classical.choose (Finset.card_eq_two.mp h2)) +
                rb_j (Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp h2))))}) ≤ 1 := by
            simpa using finrank_span_le_card (R := ZMod 2)
              ({Q1 (rb_j (Classical.choose (Finset.card_eq_two.mp h2)) +
                rb_j (Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp h2))))} : Set _)
          omega
        · let S2 : Finset ((W → ZMod 2) ⧸ C1) := {Q1 (L1_W k hk bs.1 bs.2), Q1 (L2_W k hk bs.1 bs.2)}
          have hV_eq : V_bs bs = Submodule.span (ZMod 2) (S2 : Set ((W → ZMod 2) ⧸ C1)) := by
            dsimp only [V_bs, S2]; rw [if_neg h1, dif_neg h2]
          rw [hV_eq]
          have h3 : 3 ≤ (F_bs bs).card := by omega
          have hfr : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S2 : Set ((W → ZMod 2) ⧸ C1))) ≤ 2 := by
            have h1' : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (S2 : Set ((W → ZMod 2) ⧸ C1))) ≤ S2.card := by
              simpa using finrank_span_le_card (R := ZMod 2) (S2 : Set ((W → ZMod 2) ⧸ C1))
            have h2' : S2.card ≤ 2 := by
              dsimp only [S2]
              calc ({Q1 (L1_W k hk bs.1 bs.2), Q1 (L2_W k hk bs.1 bs.2)} : Finset _).card
                  ≤ ({Q1 (L2_W k hk bs.1 bs.2)} : Finset _).card + 1 := Finset.card_insert_le _ _
                _ = 2 := by simp
            exact le_trans h1' h2'
          omega
    have hmap_le : (A_W ⊓ B_j).map Q1 ≤ Finset.univ.sup V_bs := by
      rintro _ ⟨f, ⟨hfA, hfB⟩, rfl⟩
      have hfB' : ∃ (c0 : ZMod 2) (coeff : Fin m → ZMod 2),
          f = c0 • constOneW k + ∑ r : Fin m, coeff r • rb_j r := by
        have hfB0 : f ∈ Submodule.span (ZMod 2) (insert (constOneW k) (Set.range rb_j)) := hfB
        rw [Submodule.mem_span_insert] at hfB0
        obtain ⟨c0, g, hg, rfl⟩ := hfB0
        rw [Submodule.mem_span_range_iff_exists_fun] at hg
        obtain ⟨coeff, rfl⟩ := hg
        exact ⟨c0, coeff, rfl⟩
      obtain ⟨c0, coeff, rfl⟩ := hfB'
      have hD0 : D2W k (∑ r : Fin m, coeff r • rb_j r) = 0 := by
        have hAf : D2W k (c0 • constOneW k + ∑ r : Fin m, coeff r • rb_j r) = 0 := by
          refine Submodule.span_induction (p := fun g _ => D2W k g = 0) ?_ ?_ ?_ ?_ hfA
          · rintro _ ⟨i, rfl⟩; exact D2W_coordW k i
          · exact map_zero (D2W k)
          · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
          · intro c x _ hx; rw [map_smul, hx, smul_zero]
        rw [map_add, map_smul, D2W_constOneW, smul_zero, zero_add] at hAf
        exact hAf
      have hS0 := bucket_sum_zero k hk hk_case m bank_j name_j site_j coeff hD0
      have hQconst : Q1 (c0 • constOneW k) = 0 := by
        dsimp only [Q1]
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      rw [map_add, hQconst, zero_add]
      have hfiber :
          ∑ r : Fin m, coeff r • rb_j r =
          ∑ bs : Bool × Fin k, ∑ r ∈ F_bs bs, coeff r • rb_j r :=
        (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
      rw [hfiber, map_sum]
      refine Submodule.sum_mem _ ?_
      intro bs _
      have hle_sup : V_bs bs ≤ Finset.univ.sup V_bs :=
        Finset.le_sup (f := V_bs) (Finset.mem_univ bs)
      apply hle_sup
      have hsum_bs : ∑ r ∈ F_bs bs, coeff r = 0 := hS0 bs
      dsimp only [V_bs]
      by_cases h1 : (F_bs bs).card ≤ 1
      · simp only [h1, ↓reduceIte]
        have h0_or_1 : (F_bs bs).card = 0 ∨ (F_bs bs).card = 1 := by omega
        rcases h0_or_1 with hc0 | hc1
        · rw [Finset.card_eq_zero.mp hc0, Finset.sum_empty, map_zero]
          exact Submodule.zero_mem _
        · obtain ⟨r0, hr0⟩ := Finset.card_eq_one.mp hc1
          rw [hr0, Finset.sum_singleton] at hsum_bs ⊢
          rw [hsum_bs, zero_smul, map_zero]
          exact Submodule.zero_mem _
      · by_cases h2 : (F_bs bs).card = 2
        · simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
          set r0 := Classical.choose (Finset.card_eq_two.mp h2)
          have hr0_spec := Classical.choose_spec (Finset.card_eq_two.mp h2)
          set r1 := Classical.choose hr0_spec
          have hr1_spec := Classical.choose_spec hr0_spec
          obtain ⟨hne, hpair⟩ := hr1_spec
          rw [hpair, Finset.sum_pair hne] at hsum_bs
          have hsum_eq : ∑ r ∈ F_bs bs, coeff r • rb_j r = coeff r0 • rb_j r0 + coeff r1 • rb_j r1 := by
            rw [hpair, Finset.sum_pair hne]
          rw [hsum_eq]
          have hc_eq : coeff r1 = coeff r0 := by
            generalize coeff r0 = a at hsum_bs ⊢
            generalize coeff r1 = b at hsum_bs ⊢
            revert a b hsum_bs; decide
          rw [hc_eq, ← smul_add, map_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        · simp only [h1, h2, ↓reduceIte, ↓reduceDIte]
          have hshift : ∑ r ∈ F_bs bs, coeff r • rb_j r =
              ∑ r ∈ F_bs bs, coeff r • (rb_j r + rb0 k hk bs.1 bs.2) := by
            have h0 : ∑ r ∈ F_bs bs, coeff r • rb0 k hk bs.1 bs.2 = 0 := by
              rw [← Finset.sum_smul, hsum_bs, zero_smul]
            calc ∑ r ∈ F_bs bs, coeff r • rb_j r
                = (∑ r ∈ F_bs bs, coeff r • rb_j r) + ∑ r ∈ F_bs bs, coeff r • rb0 k hk bs.1 bs.2 := by
                  rw [h0, add_zero]
              _ = ∑ r ∈ F_bs bs, (coeff r • rb_j r + coeff r • rb0 k hk bs.1 bs.2) := by
                  rw [Finset.sum_add_distrib]
              _ = ∑ r ∈ F_bs bs, coeff r • (rb_j r + rb0 k hk bs.1 bs.2) := by
                  apply Finset.sum_congr rfl; intro r _; rw [smul_add]
          rw [hshift, map_sum]
          refine Submodule.sum_mem _ ?_
          intro r hr
          simp only [F_bs, Finset.mem_filter, Finset.mem_univ, true_and] at hr
          have hbr : bank_j r = bs.1 := congrArg Prod.fst hr
          have hsr : site_j r = bs.2 := congrArg Prod.snd hr
          rw [map_smul]
          apply Submodule.smul_mem
          have hrb_eq : rb_j r = rbW k hk bs.1 (name_j r) bs.2 := by
            simp only [rb_j, hbr, hsr]
          rw [hrb_eq, rbDiff_decomp k hk bs.1 (name_j r) bs.2, map_add, map_add, map_smul, map_smul, map_smul]
          have hQc : Q1 (constOneW k) = 0 := by
            dsimp only [Q1]
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Submodule.subset_span rfl
          rw [hQc, smul_zero, zero_add]
          exact Submodule.add_mem _
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
            (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hcard_sum : ∑ bs : Bool × Fin k, (F_bs bs).card = m := by
      have h := Finset.card_eq_sum_card_fiberwise
        (s := (Finset.univ : Finset (Fin m))) (t := (Finset.univ : Finset (Bool × Fin k)))
        (f := fun r : Fin m => (bank_j r, site_j r)) (fun _ _ => Finset.mem_univ _)
      simpa [F_bs, Fintype.card_fin] using h.symm
    have h3d_le_2m : 3 * dVal k ≤ 2 * m := by
      calc 3 * dVal k
          ≤ 3 * Module.finrank (ZMod 2) ((A_W ⊓ B_j).map Q1) := Nat.mul_le_mul_left 3 hd_le_Q1
        _ ≤ 3 * Module.finrank (ZMod 2) ↥(Finset.univ.sup V_bs) :=
            Nat.mul_le_mul_left 3 (Submodule.finrank_mono hmap_le)
        _ ≤ 3 * ∑ bs : Bool × Fin k, Module.finrank (ZMod 2) (V_bs bs) :=
            Nat.mul_le_mul_left 3 (finrank_finset_sup_le Finset.univ V_bs)
        _ = ∑ bs : Bool × Fin k, 3 * Module.finrank (ZMod 2) (V_bs bs) := Finset.mul_sum _ _ _
        _ ≤ ∑ bs : Bool × Fin k, 2 * (F_bs bs).card := Finset.sum_le_sum (fun bs _ => hV_bound bs)
        _ = 2 * ∑ bs : Bool × Fin k, (F_bs bs).card := (Finset.mul_sum _ _ _).symm
        _ = 2 * m := by rw [hcard_sum]
    omega

set_option maxHeartbeats 800000 in
lemma lower_bound (k : ℕ) (hk : 0 < k) (hk1 : k ≠ 1) (hk3 : k ≠ 3) (n q : ℕ)
    (h : ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
        (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
        (C : Circuit) (tap : Fin n → Fin k → ℕ),
      a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal k ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i) : n * priceVal k ≤ q := by
  classical
  obtain ⟨a, bank, key, name, site, C, tap, haq, ⟨hRB, hFan⟩, hNL, hTapLt, hDec⟩ := h
  let U := Fin n → Fin k → Bool
  let dataOf : U → List Bool := fun x =>
    List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l))
  let wireFn : ℕ → (U → ZMod 2) := fun w x => b2z ((C.wires (dataOf x)).getD w false)
  let rbFn : Fin a → (U → ZMod 2) := fun l x =>
    b2z (readBit k hk (bank l) (name l) (x (key l)) (site l))
  let constOne : U → ZMod 2 := fun _ => 1
  let B : Submodule (ZMod 2) (U → ZMod 2) :=
    Submodule.span (ZMod 2) (insert constOne (Set.range rbFn))
  let nlIdx : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun j : Fin C.gates.length => isNonlin C.gates[j.val] = true)
  let nlSet : Finset (U → ZMod 2) :=
    nlIdx.image (fun j : Fin C.gates.length => wireFn (a + j.val))
  let E : Submodule (ZMod 2) (U → ZMod 2) :=
    Submodule.span (ZMod 2) (nlSet : Set (U → ZMod 2))
  have hE_rank : Module.finrank (ZMod 2) E ≤ n * lossVal k := by
    have h1 : Module.finrank (ZMod 2) E ≤ nlSet.card := by
      simpa [E] using finrank_span_le_card (R := ZMod 2) (nlSet : Set (U → ZMod 2))
    have h2 : nlSet.card ≤ n * lossVal k := by
      calc nlSet.card ≤ nlIdx.card := Finset.card_image_le
        _ = C.gates.countP isNonlin := card_filter_fin_eq_countP C.gates isNonlin
        _ ≤ n * lossVal k := hNL
    omega
  have hWire_mem : ∀ w < a + C.gates.length, wireFn w ∈ B ⊔ E := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw
      have hdata_len : ∀ x, (dataOf x).length = a := by
        intro x; simp [dataOf, List.length_ofFn]
      by_cases hlt_a : w < a
      · have heq : wireFn w = rbFn ⟨w, hlt_a⟩ := by
          funext x
          simp only [wireFn, wiresFrom_eq]
          rw [getD_wiresFrom_lt _ (dataOf x) w (by rw [hdata_len]; omega)]
          simp only [dataOf]
          rw [getD_ofFn_lt _ _ w hlt_a]
        rw [heq]
        exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨w, hlt_a⟩, rfl⟩))
      · set j : ℕ := w - a
        have hj : j < C.gates.length := by omega
        have hw_eq : w = a + j := by omega
        by_cases hnlj : isNonlin C.gates[j] = true
        · apply Submodule.mem_sup_right
          apply Submodule.subset_span
          rw [hw_eq]
          exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp [nlIdx, hnlj], rfl⟩)
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
  let coordFn : Fin n × Fin k → (U → ZMod 2) := fun p x => b2z (x p.1 p.2)
  let A_full : Submodule (ZMod 2) (U → ZMod 2) := Submodule.span (ZMod 2) (Set.range coordFn)
  have hA_le : A_full ≤ B ⊔ E := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨j, i⟩, rfl⟩
    have heq : coordFn (j, i) = wireFn (tap j i) := by
      funext x
      simp only [coordFn, wireFn, dataOf]
      rw [hDec x j i]
    rw [heq]
    exact hWire_mem _ (hTapLt j i)
  have hper_key : ∀ j0 : Fin n,
      priceVal k ≤ (Finset.univ.filter (fun l : Fin a => key l = j0)).card := by
    intro j0
    let L_j0 : Finset (Fin a) := Finset.univ.filter (fun l : Fin a => key l = j0)
    let m := L_j0.card
    let e : Fin m ≃ {l : Fin a // l ∈ L_j0} :=
      (Fintype.equivFinOfCardEq (by simp [m])).symm
    let bank_j : Fin m → Bool := fun r => bank (e r).1
    let name_j : Fin m → Fin k → Bool := fun r => name (e r).1
    let site_j : Fin m → Fin k := fun r => site (e r).1
    let projKey : (U → ZMod 2) →ₗ[ZMod 2] ((Fin k → Bool) → ZMod 2) :=
      { toFun := fun f w => f (fun j => if j = j0 then w else fun _ => false)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let B_j0 : Submodule (ZMod 2) ((Fin k → Bool) → ZMod 2) :=
      Submodule.span (ZMod 2) (insert (constOneW k) (Set.range (fun r : Fin m => rbW k hk (bank_j r) (name_j r) (site_j r))))
    have hB_map : B.map projKey ≤ B_j0 := by
      rw [Submodule.map_le_iff_le_comap, Submodule.span_le]
      intro f hf
      change projKey f ∈ B_j0
      rcases hf with rfl | ⟨l, rfl⟩
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · by_cases hl : key l = j0
        · have hlmem : l ∈ L_j0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩
          let r : Fin m := e.symm ⟨l, hlmem⟩
          have heq : projKey (rbFn l) = rbW k hk (bank_j r) (name_j r) (site_j r) := by
            funext w
            have her : (e r).1 = l := congrArg Subtype.val (e.apply_symm_apply ⟨l, hlmem⟩)
            simp only [projKey, LinearMap.coe_mk, AddHom.coe_mk, rbFn, rbW, bank_j, name_j, site_j,
              her, hl, ↓reduceIte]
          rw [heq]
          exact Submodule.subset_span (Set.mem_insert_of_mem _ ⟨r, rfl⟩)
        · have heq : projKey (rbFn l) =
              b2z (readBit k hk (bank l) (name l) (fun _ => false) (site l)) • constOneW k := by
            funext w
            simp only [projKey, LinearMap.coe_mk, AddHom.coe_mk, rbFn, hl, ↓reduceIte,
              Pi.smul_apply, smul_eq_mul, constOneW, mul_one]
          rw [heq]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    apply single_key_lower k hk hk1 hk3 m bank_j name_j site_j
    by_cases h93 : 9 ≤ k ∧ 3 ∣ k
    · rcases h93 with ⟨hk9, h3⟩
      have hne10 : k ≠ 10 := by omega
      have hloss2 : lossVal k = 2 := by simp [lossVal, hk9, h3]
      have hd_eq : dVal k = k - 2 := by simp [dVal, hloss2]
      let res : (U → ZMod 2) →ₗ[ZMod 2] ((Fin n → Fin 2 → Bool) → ZMod 2) :=
        { toFun := fun f c => f (fun j => kerWord k (c j))
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have hAB_ker : ∀ f ∈ A_full ⊓ B, res f = 0 := by
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
          · rintro _ ⟨⟨j1, i1⟩, rfl⟩; exact deriv2_coord j1 j i1 p q
          · simp [deriv2]
          · intro x y _ _ hx hy; rw [deriv2_add, hx, hy, add_zero]
          · intro c x _ hx; rw [deriv2_smul, hx, mul_zero]
        have hfB' : ∃ (c0 : ZMod 2) (coeff : Fin a → ZMod 2),
            f = c0 • constOne + ∑ l : Fin a, coeff l • rbFn l := by
          have hfB0 : f ∈ Submodule.span (ZMod 2) (insert constOne (Set.range rbFn)) := hfB
          rw [Submodule.mem_span_insert] at hfB0
          obtain ⟨c0, g, hg, rfl⟩ := hfB0
          rw [Submodule.mem_span_range_iff_exists_fun] at hg
          obtain ⟨coeff, rfl⟩ := hg
          exact ⟨c0, coeff, rfl⟩
        obtain ⟨c0, coeff, hf_eq⟩ := hfB'
        have hcol_zero : ∀ (j : Fin n) (i : Fin k),
            ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j ∧ site l = i), coeff l = 0 := by
          intro j i
          have hd := hf_d2 j (ix k hk (i.val + k - 4)) (ix k hk (i.val + 1))
          rw [hf_eq, deriv2_add, deriv2_smul, deriv2_const, mul_zero, zero_add, deriv2_sum] at hd
          have hterm : ∀ l : Fin a,
              deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 4)) (ix k hk (i.val + 1)) =
                if bank l = true ∧ key l = j ∧ site l = i then coeff l else 0 := by
            intro l
            rw [deriv2_smul]
            by_cases hkj : key l = j
            · have hrb_eq : rbFn l = (fun x : U => b2z (readBit k hk (bank l) (name l) (x j) (site l))) := by
                funext x; simp [rbFn, hkj]
              rw [hrb_eq, deriv2_dist5 hk9 hne10 (bank l) (name l) j (site l) i]
              by_cases hc : bank l = true ∧ site l = i <;> simp [hc, hkj]
            · rw [deriv2_readBit_ne_key hk (bank l) (name l) (key l) j (site l) _ _ hkj, mul_zero]
              simp [hkj]
          simp_rw [hterm] at hd
          simpa [Finset.sum_filter] using hd
        have hrow_zero : ∀ (j : Fin n) (i : Fin k),
            ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false ∧ key l = j ∧ site l = i), coeff l = 0 := by
          intro j i
          have hpq : ix k hk (i.val + k - 1) ≠ ix k hk (i.val + 2) := by
            intro h; rw [Fin.ext_iff] at h; simp only [ix] at h
            have hi := i.isLt
            rw [mod_of_lt_two k _ (by omega), mod_of_lt_two k _ (by omega)] at h
            split_ifs at h <;> omega
          have hd := hf_d2 j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2))
          rw [hf_eq, deriv2_add, deriv2_smul, deriv2_const, mul_zero, zero_add, deriv2_sum] at hd
          have hsplit_col :
              ∑ l : Fin a, deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) =
              (∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true),
                deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2))) +
              (∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false),
                deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2))) := by
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun l : Fin a => bank l = true)]
            congr 1
          rw [hsplit_col] at hd
          have hcol_part :
              ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true),
                deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) = 0 := by
            have hfiber :
                ∑ l ∈ Finset.univ.filter (fun l : Fin a => bank l = true),
                  deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) =
                ∑ p : Fin n × Fin k,
                  ∑ l ∈ (Finset.univ.filter (fun l : Fin a => bank l = true)).filter (fun l => (key l, site l) = p),
                    deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) :=
              (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
            rw [hfiber]
            apply Finset.sum_eq_zero
            rintro ⟨j1, i1⟩ _
            have hval : ∀ l ∈ (Finset.univ.filter (fun l : Fin a => bank l = true)).filter (fun l => (key l, site l) = (j1, i1)),
                deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) =
                  coeff l * deriv2 (fun x : U => b2z (readBit k hk true (fun _ => false) (x j1) i1))
                    j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) := by
              intro l hl
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hl
              rcases hl with ⟨hb, hkj, hsi⟩
              rw [deriv2_smul]
              congr 1
              have hrb_eq : rbFn l = (fun x : U => b2z (readBit k hk true (name l) (x j1) i1)) := by
                funext x; simp [rbFn, hb, hkj, hsi]
              rw [hrb_eq]
              exact deriv2_readBit_indep_u hk true (name l) (fun _ => false) j1 j i1 _ _ hpq
            rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
            have hfilt : (Finset.univ.filter (fun l : Fin a => bank l = true)).filter (fun l => (key l, site l) = (j1, i1)) =
                Finset.univ.filter (fun l : Fin a => bank l = true ∧ key l = j1 ∧ site l = i1) := by
              ext l; simp [and_assoc]
            rw [hfilt, hcol_zero j1 i1, zero_mul]
          rw [hcol_part, zero_add] at hd
          have hterm : ∀ l ∈ Finset.univ.filter (fun l : Fin a => bank l = false),
              deriv2 (coeff l • rbFn l) j (ix k hk (i.val + k - 1)) (ix k hk (i.val + 2)) =
                if key l = j ∧ site l = i then coeff l else 0 := by
            intro l hl
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
            rw [deriv2_smul]
            by_cases hkj : key l = j
            · have hrb_eq : rbFn l = (fun x : U => b2z (readBit k hk false (name l) (x j) (site l))) := by
                funext x; simp [rbFn, hl, hkj]
              rw [hrb_eq, deriv2_dist3_row hk9 (name l) j (site l) i]
              by_cases hsi : site l = i <;> simp [hkj, hsi]
            · rw [deriv2_readBit_ne_key hk (bank l) (name l) (key l) j (site l) _ _ hkj, mul_zero]
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
                (∑ l : Fin a, coeff l * b2z (wRot k hk (if bank l then 4 else 0) (kerWord k (c (key l))) (site l))) +
                ∑ l : Fin a, coeff l * rbFn l (fun _ _ => false) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl; intro l _
            simp only [rbFn]
            rw [readBit_on_kerWord k hk9 h3 (bank l) (name l) (c (key l)) (site l), mul_add]
          rw [hsum_eq]
          have hrot_zero :
              ∑ l : Fin a, coeff l * b2z (wRot k hk (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) = 0 := by
            have hfiber :
                ∑ l : Fin a, coeff l * b2z (wRot k hk (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) =
                ∑ p : Bool × Fin n × Fin k,
                  ∑ l ∈ Finset.univ.filter (fun l : Fin a => (bank l, key l, site l) = p),
                    coeff l * b2z (wRot k hk (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) :=
              (Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _).symm
            rw [hfiber]
            apply Finset.sum_eq_zero
            rintro ⟨col, j1, i1⟩ _
            have hval : ∀ l ∈ Finset.univ.filter (fun l : Fin a => (bank l, key l, site l) = (col, j1, i1)),
                coeff l * b2z (wRot k hk (if bank l then 4 else 0) (kerWord k (c (key l))) (site l)) =
                  coeff l * b2z (wRot k hk (if col then 4 else 0) (kerWord k (c j1)) i1) := by
              intro l hl
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hl
              rcases hl with ⟨hb, hkj, hsi⟩
              rw [hb, hkj, hsi]
            rw [Finset.sum_congr rfl hval, ← Finset.sum_mul]
            have hfilt : Finset.univ.filter (fun l : Fin a => (bank l, key l, site l) = (col, j1, i1)) =
                Finset.univ.filter (fun l : Fin a => bank l = col ∧ key l = j1 ∧ site l = i1) := by
              ext l; simp [Prod.mk.injEq]
            rw [hfilt]
            cases col
            · rw [hrow_zero j1 i1, zero_mul]
            · rw [hcol_zero j1 i1, zero_mul]
          rw [hrot_zero, zero_add]
        rw [hdiff, hf0]
      have hLI_res : LinearIndependent (ZMod 2)
          (fun p : Fin n × Fin 2 => res (coordFn (p.1, ⟨p.2.val, by omega⟩))) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg p
        let c : Fin n → Fin 2 → Bool := fun j r => decide ((j, r) = p)
        have h0 := congrFun hg c
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
        have hev : ∀ q : Fin n × Fin 2, res (coordFn (q.1, ⟨q.2.val, by omega⟩)) c = if q = p then 1 else 0 := by
          rintro ⟨j, r⟩
          simp only [res, LinearMap.coe_mk, AddHom.coe_mk, coordFn, kerWord, c]
          fin_cases r <;> simp [b2z]
        simp_rw [hev] at h0
        simpa using h0
      have h2n_le : n * 2 ≤ Module.finrank (ZMod 2) (A_full.map res) := by
        have hmem : ∀ p : Fin n × Fin 2, res (coordFn (p.1, ⟨p.2.val, by omega⟩)) ∈ A_full.map res := fun p =>
          ⟨coordFn (p.1, ⟨p.2.val, by omega⟩), Submodule.subset_span ⟨(p.1, ⟨p.2.val, by omega⟩), rfl⟩, rfl⟩
        let v : Fin n × Fin 2 → A_full.map res := fun p => ⟨res (coordFn (p.1, ⟨p.2.val, by omega⟩)), hmem p⟩
        have hvLI : LinearIndependent (ZMod 2) v := by
          have hcomp : ((A_full.map res).subtype ∘ v) = (fun p => res (coordFn (p.1, ⟨p.2.val, by omega⟩))) := rfl
          rw [← hcomp] at hLI_res
          exact LinearIndependent.of_comp (A_full.map res).subtype hLI_res
        simpa [Fintype.card_prod, Fintype.card_fin] using hvLI.fintype_card_le_finrank
      let qB := B.mkQ
      have hker_le : LinearMap.ker (qB.domRestrict A_full) ≤ LinearMap.ker (res.domRestrict A_full) := by
        rintro ⟨f, hfA⟩ hfq
        simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply] at hfq ⊢
        dsimp only [qB] at hfq
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hfq
        exact hAB_ker f ⟨hfA, hfq⟩
      have hAq_le_Eq : A_full.map qB ≤ E.map qB := by
        calc A_full.map qB ≤ (B ⊔ E).map qB := Submodule.map_mono hA_le
          _ = B.map qB ⊔ E.map qB := Submodule.map_sup _ _ _
          _ = ⊥ ⊔ E.map qB := by
            congr 1
            rw [Submodule.eq_bot_iff]
            rintro _ ⟨x, hx, rfl⟩
            exact (Submodule.Quotient.mk_eq_zero B).mpr hx
          _ = E.map qB := bot_sup_eq _
      have hEq_rank : Module.finrank (ZMod 2) (E.map qB) ≤ Module.finrank (ZMod 2) E := by
        have h1 := LinearMap.finrank_range_le (qB.domRestrict E)
        have h2 : LinearMap.range (qB.domRestrict E) = E.map qB := by ext y; simp [Submodule.mem_map]
        rw [h2] at h1; exact h1
      have hAq_rank : Module.finrank (ZMod 2) (A_full.map qB) ≤ n * 2 := by
        have h2eq : n * lossVal k = n * 2 := by rw [hloss2]
        rw [← h2eq]
        exact le_trans (Submodule.finrank_mono hAq_le_Eq) (le_trans hEq_rank hE_rank)
      have hrn_res := LinearMap.finrank_range_add_finrank_ker (res.domRestrict A_full)
      have hrn_q := LinearMap.finrank_range_add_finrank_ker (qB.domRestrict A_full)
      have hrange_res : LinearMap.range (res.domRestrict A_full) = A_full.map res := by
        ext y; simp [Submodule.mem_map]
      have hrange_q : LinearMap.range (qB.domRestrict A_full) = A_full.map qB := by
        ext y; simp [Submodule.mem_map]
      rw [hrange_res] at hrn_res
      rw [hrange_q] at hrn_q
      have hker_eq : LinearMap.ker (qB.domRestrict A_full) = LinearMap.ker (res.domRestrict A_full) :=
        submodule_eq_of_le_of_finrank_le hker_le (by omega)
      let r0Fn : Fin (k - 2) → (U → ZMod 2) := fun t =>
        coordFn (j0, ⟨t.val, by omega⟩) + coordFn (j0, ⟨t.val + 1, by omega⟩) + coordFn (j0, ⟨t.val + 2, by omega⟩)
      let r0W : Fin (k - 2) → ((Fin k → Bool) → ZMod 2) := fun t =>
        coordW k ⟨t.val, by omega⟩ + coordW k ⟨t.val + 1, by omega⟩ + coordW k ⟨t.val + 2, by omega⟩
      have hr0_mem : ∀ t : Fin (k - 2), r0W t ∈ Submodule.span (ZMod 2) (Set.range (coordW k)) ⊓ B_j0 := by
        intro t
        constructor
        · exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
            (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
        · have hr0A : r0Fn t ∈ A_full :=
            Submodule.add_mem _ (Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
              (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
          have hr0res : res (r0Fn t) = 0 := by
            funext c
            simp only [res, LinearMap.coe_mk, AddHom.coe_mk, r0Fn, coordFn, kerWord, Pi.add_apply, Pi.zero_apply]
            have hm : t.val % 3 = 0 ∨ t.val % 3 = 1 ∨ t.val % 3 = 2 := by omega
            rcases hm with h0 | h1 | h2
            · have h1' : (t.val + 1) % 3 = 1 := by omega
              have h2' : (t.val + 2) % 3 = 2 := by omega
              simp [h0, h1', h2', b2z_xor]
              cases c j0 0 <;> cases c j0 1 <;> decide
            · have h1' : (t.val + 1) % 3 = 2 := by omega
              have h2' : (t.val + 2) % 3 = 0 := by omega
              simp [h1, h1', h2', b2z_xor]
              cases c j0 0 <;> cases c j0 1 <;> decide
            · have h1' : (t.val + 1) % 3 = 0 := by omega
              have h2' : (t.val + 2) % 3 = 1 := by omega
              simp [h2, h1', h2', b2z_xor]
              cases c j0 0 <;> cases c j0 1 <;> decide
          have hr0B : r0Fn t ∈ B := by
            have hker_mem : (⟨r0Fn t, hr0A⟩ : A_full) ∈ LinearMap.ker (qB.domRestrict A_full) := by
              rw [hker_eq]
              exact hr0res
            simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, qB, Submodule.mkQ_apply,
              Submodule.Quotient.mk_eq_zero] at hker_mem
            exact hker_mem
          have hproj_eq : projKey (r0Fn t) = r0W t := by
            funext w
            simp [projKey, r0Fn, r0W, coordFn, coordW]
          rw [← hproj_eq]
          exact hB_map ⟨r0Fn t, hr0B, rfl⟩
      have hr0_LI : LinearIndependent (ZMod 2) r0W := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        have hstrong : ∀ s : ℕ, (hs : s < k - 2) → g ⟨s, hs⟩ = 0 := by
          intro s
          induction s using Nat.strong_induction_on with
          | ind s ih =>
            intro hs
            have h0 := congrFun hg (singleBit k ⟨s, by omega⟩)
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
            have hterm : ∀ t : Fin (k - 2), g t * r0W t (singleBit k ⟨s, by omega⟩) =
                if t.val = s then g t else 0 := by
              intro t
              by_cases hlt : t.val < s
              · rw [ih t.val hlt t.isLt, zero_mul]
                simp [Nat.ne_of_lt hlt]
              · by_cases heq : t.val = s
                · simp only [heq, ↓reduceIte, r0W, coordW, singleBit, Pi.add_apply]
                  have h1 : (⟨t.val, by omega⟩ : Fin k) = ⟨s, by omega⟩ := Fin.ext heq
                  have h2 : (⟨t.val + 1, by omega⟩ : Fin k) ≠ ⟨s, by omega⟩ := by
                    intro h; have := congrArg Fin.val h; dsimp at this; omega
                  have h3 : (⟨t.val + 2, by omega⟩ : Fin k) ≠ ⟨s, by omega⟩ := by
                    intro h; have := congrArg Fin.val h; dsimp at this; omega
                  simp [h1, h2, h3, b2z]
                · have hgt : s < t.val := by omega
                  simp only [heq, ↓reduceIte, r0W, coordW, singleBit, Pi.add_apply]
                  have h1 : (⟨t.val, by omega⟩ : Fin k) ≠ ⟨s, by omega⟩ := by
                    intro h; have := congrArg Fin.val h; dsimp at this; omega
                  have h2 : (⟨t.val + 1, by omega⟩ : Fin k) ≠ ⟨s, by omega⟩ := by
                    intro h; have := congrArg Fin.val h; dsimp at this; omega
                  have h3 : (⟨t.val + 2, by omega⟩ : Fin k) ≠ ⟨s, by omega⟩ := by
                    intro h; have := congrArg Fin.val h; dsimp at this; omega
                  simp [h1, h2, h3, b2z]
            simp_rw [hterm] at h0
            have hsum_eq : ∑ t : Fin (k - 2), (if t.val = s then g t else 0) = g ⟨s, hs⟩ := by
              have : ∀ t : Fin (k - 2), (if t.val = s then g t else 0) = if t = ⟨s, hs⟩ then g t else 0 := by
                intro t; by_cases h : t.val = s
                · have ht : t = ⟨s, hs⟩ := Fin.ext h; simp [h, ht]
                · have ht : t ≠ ⟨s, hs⟩ := fun e => h (congrArg Fin.val e); simp [h, ht]
              simp_rw [this]; simp
            rw [hsum_eq] at h0
            exact h0
        intro t; exact hstrong t.val t.isLt
      have hvLI : LinearIndependent (ZMod 2)
          (fun t : Fin (k - 2) => (⟨r0W t, hr0_mem t⟩ : ↥(Submodule.span (ZMod 2) (Set.range (coordW k)) ⊓ B_j0))) :=
        LinearIndependent.of_comp (Submodule.span (ZMod 2) (Set.range (coordW k)) ⊓ B_j0).subtype hr0_LI
      rw [hd_eq]
      simpa [Fintype.card_fin] using hvLI.fintype_card_le_finrank
    · have hloss0 : lossVal k = 0 := by simp [lossVal, h93]
      have hd_eq : dVal k = k := by simp [dVal, hloss0]
      have hnl_empty : nlSet = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro f hf
        have hpos : 0 < nlSet.card := Finset.card_pos.mpr ⟨f, hf⟩
        have hle : nlSet.card ≤ 0 := by
          calc nlSet.card ≤ nlIdx.card := Finset.card_image_le
            _ = C.gates.countP isNonlin := card_filter_fin_eq_countP C.gates isNonlin
            _ ≤ n * lossVal k := hNL
            _ = 0 := by rw [hloss0, mul_zero]
        omega
      have hE_bot : E = ⊥ := by simp [E, hnl_empty]
      have hA_le_B : A_full ≤ B := by simpa [hE_bot] using hA_le
      have hAW_le_B : Submodule.span (ZMod 2) (Set.range (coordW k)) ≤ B_j0 := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        have hcB : coordFn (j0, i) ∈ B := hA_le_B (Submodule.subset_span ⟨(j0, i), rfl⟩)
        have hproj : projKey (coordFn (j0, i)) = coordW k i := by
          funext w; simp [projKey, coordFn, coordW]
        rw [← hproj]
        exact hB_map ⟨coordFn (j0, i), hcB, rfl⟩
      rw [hd_eq, inf_eq_left.mpr hAW_le_B, finrank_A_W]
  have hsum_a : ∑ j0 : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j0)).card = a := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Fin a))) (t := (Finset.univ : Finset (Fin n)))
      (f := key) (fun _ _ => Finset.mem_univ _)
    simpa [Fintype.card_fin] using h.symm
  have hnp_le_a : n * priceVal k ≤ a := by
    calc n * priceVal k = ∑ _j0 : Fin n, priceVal k := by simp
      _ ≤ ∑ j0 : Fin n, (Finset.univ.filter (fun l : Fin a => key l = j0)).card :=
          Finset.sum_le_sum (fun j0 _ => hper_key j0)
      _ = a := hsum_a
  omega

lemma rowDiff1_ge4 (k : ℕ) (hk : 4 ≤ k) (x : Fin k → Bool) (i : Fin k) :
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

lemma rowDiff2_ge4 (k : ℕ) (hk : 4 ≤ k) (x : Fin k → Bool) (i : Fin k) :
    have hk0 : 0 < k := by omega
    xor (readBit k hk0 false (singleBit k (ix k hk0 (i.val + 3))) x i)
        (readBit k hk0 false (fun _ => false) x i) =
      if k = 4 then wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (i.val + 1))
      else !(wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (i.val + 1))) := by
  have hk0 : 0 < k := by omega
  by_cases hk4 : k = 4
  · subst hk4
    clear hk0
    have hdec : ∀ (x0 x1 x2 x3 : Bool) (i : Fin 4),
        let f : Fin 4 → Bool := ![x0, x1, x2, x3]
        xor (readBit 4 (Nat.zero_lt_succ 3) false (singleBit 4 (ix 4 (Nat.zero_lt_succ 3) (i.val + 3))) f i)
            (readBit 4 (Nat.zero_lt_succ 3) false (fun _ => false) f i) =
          wMix 4 (Nat.zero_lt_succ 3) 1 (wRot 4 (Nat.zero_lt_succ 3) 1 f) (ix 4 (Nat.zero_lt_succ 3) (i.val + 1)) := by
      decide +kernel
    have hx : x = ![x 0, x 1, x 2, x 3] := by funext r; fin_cases r <;> rfl
    dsimp only
    simp only [↓reduceIte]
    rw [hx]
    exact hdec (x 0) (x 1) (x 2) (x 3) i
  · have hk5 : 5 ≤ k := by omega
    simp only [hk4, ↓reduceIte]
    have h1mod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    have hi_lt : i.val < k := i.isLt
    set p : Fin k := ix k hk0 (i.val + 3)
    have hc0 : wMix k hk0 1 (singleBit k p) i = false := by
      rw [wMix_singleBit]
      have h1 : ix k hk0 (i.val + k - 1 % k) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p, h1mod] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h2 : i ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p] at h
        rw [mod_of_lt_two k (i.val + 3) (by omega)] at h; split_ifs at h <;> omega
      have h3 : ix k hk0 (i.val + 1) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      simp [h1, h2, h3]
    have hc1 : wMix k hk0 1 (singleBit k p) (ix k hk0 (i.val + 1)) = false := by
      rw [wMix_singleBit]
      have h1 : ix k hk0 ((ix k hk0 (i.val + 1)).val + k - 1 % k) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p, h1mod] at h
        rw [mod_add_k_sub k (i.val + 1) 1 (by omega)] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h2 : ix k hk0 (i.val + 1) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h3 : ix k hk0 ((ix k hk0 (i.val + 1)).val + 1) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p] at h
        rw [mod_add_cancel] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      simp [h1, h2, h3]
    have hc2 : wMix k hk0 1 (singleBit k p) (ix k hk0 (i.val + 2)) = true := by
      rw [wMix_singleBit]
      have h1 : ix k hk0 ((ix k hk0 (i.val + 2)).val + k - 1 % k) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p, h1mod] at h
        rw [mod_add_k_sub k (i.val + 2) 1 (by omega)] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h2 : ix k hk0 (i.val + 2) ≠ p := by
        intro h; rw [Fin.ext_iff] at h; simp only [ix, p] at h
        exact mod_ne_of_lt3 k _ _ (by omega) (by omega) (by omega) h
      have h3 : ix k hk0 ((ix k hk0 (i.val + 2)).val + 1) = p := by
        apply Fin.ext; simp only [ix, p]; rw [mod_add_cancel]
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

lemma foldr_xor_b2z {α : Type} (f : α → Bool) (l : List α) :
    b2z (l.foldr (fun a acc => xor (f a) acc) false) = (l.map (fun a => b2z (f a))).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [b2z_xor, ih]

lemma sum_shift_range (k : ℕ) (hk0 : 0 < k) (x : Fin k → Bool) (offset : ℕ) :
    ((List.range k).map (fun s => b2z (x (ix k hk0 (offset + s))))).sum = ∑ i : Fin k, b2z (x i) := by
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

lemma r0_step_zmod (k : ℕ) (hk : 2 ≤ k) (x : Fin k → Bool) (t : ℕ) :
    have hk0 : 0 < k := by omega
    b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (t + 1))) =
      b2z (x (ix k hk0 (t + k - 1))) + b2z (x (ix k hk0 t)) + b2z (x (ix k hk0 (t + 1))) := by
  have hk0 : 0 < k := by omega
  have hEq := wMix_rot1_eq k hk x (ix k hk0 t)
  dsimp only at hEq
  have h1 : ix k hk0 ((ix k hk0 t).val + 1) = ix k hk0 (t + 1) := by
    apply Fin.ext; simp only [ix]; exact mod_add_cancel k t 1
  have h2 : ix k hk0 ((ix k hk0 t).val + k - 1) = ix k hk0 (t + k - 1) := by
    apply Fin.ext; simp only [ix]
    rw [mod_add_k_sub k t 1 (by omega), mod_add_k_sub_self k t 1 (by omega)]
  rw [h1, h2] at hEq
  change b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (t + 1))) = _
  rw [hEq, b2z_xor, b2z_xor, add_assoc]

lemma r0_block_sum (k : ℕ) (hk : 2 ≤ k) (x : Fin k → Bool) (base q : ℕ) :
    have hk0 : 0 < k := by omega
    ((List.range q).map (fun r => b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (base + 3 * r + 2))))).sum =
      ((List.range (3 * q)).map (fun s => b2z (x (ix k hk0 (base + s))))).sum := by
  dsimp only
  have hk0 : 0 < k := by omega
  induction q with
  | zero => simp
  | succ q ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    have h3 : 3 * (q + 1) = 3 * q + 3 := by omega
    rw [h3, List.range_succ, List.range_succ, List.range_succ]
    simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    have hst := r0_step_zmod k hk x (base + 3 * q + 1)
    dsimp only at hst
    have ha1 : base + 3 * q + 1 + 1 = base + 3 * q + 2 := by omega
    have ha2 : ix k hk0 (base + 3 * q + 1 + k - 1) = ix k hk0 (base + 3 * q) := by
      apply Fin.ext; simp only [ix]
      rw [show base + 3 * q + 1 + k - 1 = (base + 3 * q) + k by omega, Nat.add_mod_right]
    have ha3 : ix k hk0 (base + 3 * q + 1) = ix k hk0 (base + (3 * q + 1)) := by congr 1
    have ha4 : ix k hk0 (base + 3 * q + 1 + 1) = ix k hk0 (base + (3 * q + 2)) := by congr 1
    conv_lhs at hst => rw [ha1]
    conv_rhs at hst => rw [ha2, ha3, ha4]
    rw [hst]; ring

def invMixIndices (k : ℕ) (hk : 4 ≤ k) (j : Fin k) : List (Fin k) :=
  have hk0 : 0 < k := by omega
  if k % 3 = 1 then
    (List.finRange k) ++ (List.range (k / 3)).map (fun r => ix k hk0 (j.val + 3 * r + 3))
  else
    (List.finRange k) ++ (List.range (k / 3 + 1)).map (fun r => ix k hk0 (j.val + 3 * r + 2))

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
  unfold invMixIndices
  split_ifs with hmod1
  · rw [List.map_append, List.sum_append, List.map_map, htot]
    have hblk := r0_block_sum k hk2 x (j.val + 1) (k / 3)
    dsimp only at hblk
    have hEq : ((List.range (k / 3)).map (fun r => b2z (R0 (ix k hk0 (j.val + 3 * r + 3))))).sum =
        ((List.range (3 * (k / 3))).map (fun s => b2z (x (ix k hk0 (j.val + 1 + s))))).sum := by
      rw [← hblk]
      congr 1; apply List.map_congr_left; intro r _; congr 2; apply Fin.ext; simp only [ix]; congr 1; omega
    change ∑ i : Fin k, b2z (x i) +
      ((List.range (k / 3)).map (fun r => b2z (R0 (ix k hk0 (j.val + 3 * r + 3))))).sum = b2z (x j)
    rw [hEq]
    have hk_eq : k = 3 * (k / 3) + 1 := by omega
    have htot2 := sum_shift_range k hk0 x (j.val + 1)
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
    rw [r0_block_sum k hk2 x j.val (k / 3 + 1)]
    have hk_eq : 3 * (k / 3 + 1) = k + 1 := by omega
    rw [hk_eq, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        sum_shift_range k hk0 x j.val]
    have hlast : ix k hk0 (j.val + k) = j := by
      apply Fin.ext; simp only [ix, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]
    rw [hlast]
    have hcancel : ∀ a b : ZMod 2, a + (a + b) = b := by decide
    exact hcancel _ _

lemma mod3_cosum_R0 (k : ℕ) (hk : 9 ≤ k) (h3 : 3 ∣ k) (x : Fin k → Bool) (r : ℕ) :
    have hk0 : 0 < k := by omega
    ((List.range (k / 3)).map (fun m => b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (r + 3 * m))))).sum =
      ∑ i : Fin k, b2z (x i) := by
  dsimp only
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hblk := r0_block_sum k hk2 x (r + k - 2) (k / 3)
  dsimp only at hblk
  have hEq : ((List.range (k / 3)).map (fun m => b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (r + 3 * m))))).sum =
      ((List.range (k / 3)).map (fun m => b2z (wMix k hk0 1 (wRot k hk0 1 x) (ix k hk0 (r + k - 2 + 3 * m + 2))))).sum := by
    congr 1; apply List.map_congr_left; intro m _
    congr 2; apply Fin.ext; simp only [ix]
    rw [show r + k - 2 + 3 * m + 2 = (r + 3 * m) + k by omega, Nat.add_mod_right]
  rw [hEq, hblk, show 3 * (k / 3) = k by omega]
  exact sum_shift_range k hk0 x (r + k - 2)

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

lemma upper_n0 (k : ℕ) (hk : 0 < k) (q : ℕ) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin 0)
      (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
      (C : Circuit) (tap : Fin 0 → Fin k → ℕ),
      a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ 0 * lossVal k ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin 0 → Fin k → Bool) (j : Fin 0) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ⟨[], 0⟩, fun j => Fin.elim0 j,
    Nat.zero_le q, ⟨readsBack_of_list 0 _ (readsBackList_nil 0), fun _ hg => by simp at hg⟩,
    by simp, fun j => Fin.elim0 j, fun _ j => Fin.elim0 j⟩

lemma k2_formulas (x : Fin 2 → Bool) :
    xor (readBit 2 (by omega) false (fun _ => false) x 1)
        (readBit 2 (by omega) false (singleBit 2 1) x 0) = x 0 ∧
    xor (readBit 2 (by omega) false (fun _ => false) x 0)
        (readBit 2 (by omega) false (singleBit 2 1) x 0) = x 1 := by
  have hx : x = ![x 0, x 1] := by funext r; fin_cases r <;> rfl
  rw [hx]; generalize x 0 = a; generalize x 1 = b; revert a b; decide

lemma upper_k2 (n q : ℕ) (hq : n * priceVal 2 ≤ q) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin 2 → Bool) (site : Fin a → Fin 2)
      (C : Circuit) (tap : Fin n → Fin 2 → ℕ),
      a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal 2 ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin 2 → Bool) (j : Fin n) (i : Fin 2),
        let data := List.ofFn (fun l : Fin a => readBit 2 (by omega) (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i := by
  have hprice2 : priceVal 2 = 3 := by decide
  let a := 3 * n
  have haq : a ≤ q := by dsimp only [a]; rw [hprice2] at hq; omega
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := fun l => ⟨l.val / 3, by omega⟩
  let name : Fin a → Fin 2 → Bool := fun l => if l.val % 3 = 2 then singleBit 2 1 else fun _ => false
  let site : Fin a → Fin 2 := fun l => if l.val % 3 = 1 then 1 else 0
  let specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => [(false, [3 * j.val + 1, 3 * j.val + 2]),
                                          (false, [3 * j.val, 3 * j.val + 2])])
  let res := appendSpecs a specs
  let C : Circuit := ⟨res.1, 0⟩
  let tap : Fin n → Fin 2 → ℕ := fun j i => res.2.getD (2 * j.val + i.val) 0
  have hspecs_lt : ∀ s ∈ specs, ∀ w ∈ s.2, w < a := by
    intro s hs w hw
    simp only [specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons, List.not_mem_nil,
      or_false] at hs
    obtain ⟨j, rfl | rfl⟩ := hs <;> simp at hw <;> rcases hw with rfl | rfl <;> omega
  have hspecs_len : specs.length = 2 * n := by
    simp [specs, List.length_flatMap]; omega
  refine ⟨a, bank, key, name, site, C, tap, haq,
    ⟨readsBack_of_list _ _ (appendSpecs_readsBack _ _ hspecs_lt), appendSpecs_fanin _ _⟩,
    by simp [C, res, appendSpecs_nonlin],
    fun j i => by
      have hi : 2 * j.val + i.val < res.2.length := by rw [appendSpecs_taps_len, hspecs_len]; omega
      have hmem : tap j i ∈ res.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact appendSpecs_taps_lt _ _ _ hmem,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit 2 (by omega) (bank l) (name l) (x (key l)) (site l))
  have hdata_len : data.length = a := by simp [data]
  have hidx : 2 * j.val + i.val < specs.length := by rw [hspecs_len]; omega
  have hev := appendSpecs_eval specs data (by simpa [hdata_len] using hspecs_lt) (2 * j.val + i.val) hidx
  rw [hdata_len] at hev
  change (wiresFrom res.1 data).getD (tap j i) false = x j i
  rw [hev]
  have hspec_at : specs[2 * j.val + i.val] =
      if i.val = 0 then (false, [3 * j.val + 1, 3 * j.val + 2])
      else (false, [3 * j.val, 3 * j.val + 2]) := by
    have h := flatMap_const_getElem n 2
      (fun j => [(false, [3 * j.val + 1, 3 * j.val + 2]),
                 (false, [3 * j.val, 3 * j.val + 2])]) (fun _ => rfl) j i
    fin_cases i <;> simpa [specs] using h
  rw [hspec_at]
  have hget : ∀ (idx : ℕ) (hidx' : idx < a),
      data.getD idx false = readBit 2 (by omega) (bank ⟨idx, hidx'⟩) (name ⟨idx, hidx'⟩)
        (x (key ⟨idx, hidx'⟩)) (site ⟨idx, hidx'⟩) := by
    intro idx hidx'
    simp only [data]; exact getD_ofFn_lt _ _ idx hidx'
  fin_cases i
  · simp only [Fin.val_zero, ↓reduceIte, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    rw [hget (3 * j.val + 1) (by omega), hget (3 * j.val + 2) (by omega)]
    have hk1 : key ⟨3 * j.val + 1, by omega⟩ = j := Fin.ext (by simp [key]; omega)
    have hk2 : key ⟨3 * j.val + 2, by omega⟩ = j := Fin.ext (by simp [key]; omega)
    have hn1 : name ⟨3 * j.val + 1, by omega⟩ = (fun _ => false) := by simp [name]
    have hn2 : name ⟨3 * j.val + 2, by omega⟩ = singleBit 2 1 := by simp [name]
    have hs1 : site ⟨3 * j.val + 1, by omega⟩ = 1 := by simp [site]
    have hs2 : site ⟨3 * j.val + 2, by omega⟩ = 0 := by simp [site]
    rw [hk1, hk2, hn1, hn2, hs1, hs2]
    exact (k2_formulas (x j)).1
  · simp only [Fin.val_one, Nat.one_ne_zero, ↓reduceIte, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    rw [hget (3 * j.val) (by omega), hget (3 * j.val + 2) (by omega)]
    have hk1 : key ⟨3 * j.val, by omega⟩ = j := Fin.ext (by simp [key])
    have hk2 : key ⟨3 * j.val + 2, by omega⟩ = j := Fin.ext (by simp [key]; omega)
    have hn1 : name ⟨3 * j.val, by omega⟩ = (fun _ => false) := by simp [name]
    have hn2 : name ⟨3 * j.val + 2, by omega⟩ = singleBit 2 1 := by simp [name]
    have hs1 : site ⟨3 * j.val, by omega⟩ = 0 := by simp [site]
    have hs2 : site ⟨3 * j.val + 2, by omega⟩ = 0 := by simp [site]
    rw [hk1, hk2, hn1, hn2, hs1, hs2]
    exact (k2_formulas (x j)).2

def k6Read (x : Fin 6 → Bool) (r : Fin 7) : Bool :=
  if h : r.val < 5 then readBit 6 (by omega) true (fun _ => false) x ⟨r.val, by omega⟩
  else if r.val = 5 then readBit 6 (by omega) true (singleBit 6 0) x 0
  else readBit 6 (by omega) true (singleBit 6 1) x 0

def k6Idxs : Fin 6 → List (Fin 7)
  | 0 => [2, 5]
  | 1 => [0, 1, 3, 6]
  | 2 => [0, 2, 4, 5]
  | 3 => [1, 2, 4, 5]
  | 4 => [4, 5]
  | 5 => [2, 3, 4, 5]

lemma k6_formulas (x : Fin 6 → Bool) (i : Fin 6) :
    (k6Idxs i).foldr (fun r acc => xor (k6Read x r) acc) false = x i := by
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by funext r; fin_cases r <;> rfl
  rw [hx]
  revert i
  generalize x 0 = x0; generalize x 1 = x1; generalize x 2 = x2
  generalize x 3 = x3; generalize x 4 = x4; generalize x 5 = x5
  revert x0 x1 x2 x3 x4 x5; decide +kernel

lemma upper_k6 (n q : ℕ) (hq : n * priceVal 6 ≤ q) :
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin 6 → Bool) (site : Fin a → Fin 6)
      (C : Circuit) (tap : Fin n → Fin 6 → ℕ),
      a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal 6 ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin 6 → Bool) (j : Fin n) (i : Fin 6),
        let data := List.ofFn (fun l : Fin a => readBit 6 (by omega) (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i := by
  have hprice6 : priceVal 6 = 7 := by decide
  let a := 7 * n
  have haq : a ≤ q := by dsimp only [a]; rw [hprice6] at hq; omega
  let bank : Fin a → Bool := fun _ => true
  let key : Fin a → Fin n := fun l => ⟨l.val / 7, by omega⟩
  let name : Fin a → Fin 6 → Bool := fun l =>
    if l.val % 7 = 5 then singleBit 6 0
    else if l.val % 7 = 6 then singleBit 6 1
    else fun _ => false
  let site : Fin a → Fin 6 := fun l =>
    if h : l.val % 7 < 5 then ⟨l.val % 7, by omega⟩ else 0
  let specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange 6).map (fun i =>
      (false, (k6Idxs i).map (fun r => 7 * j.val + r.val))))
  let res := appendSpecs a specs
  let C : Circuit := ⟨res.1, 0⟩
  let tap : Fin n → Fin 6 → ℕ := fun j i => res.2.getD (6 * j.val + i.val) 0
  have hspecs_lt : ∀ s ∈ specs, ∀ w ∈ s.2, w < a := by
    intro s hs w hw
    simp only [specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    simp only [List.mem_map] at hw
    obtain ⟨r, _, rfl⟩ := hw
    omega
  have hspecs_len : specs.length = 6 * n := by
    simp [specs, List.length_flatMap]; omega
  refine ⟨a, bank, key, name, site, C, tap, haq,
    ⟨readsBack_of_list _ _ (appendSpecs_readsBack _ _ hspecs_lt), appendSpecs_fanin _ _⟩,
    by simp [C, res, appendSpecs_nonlin],
    fun j i => by
      have hi : 6 * j.val + i.val < res.2.length := by rw [appendSpecs_taps_len, hspecs_len]; omega
      have hmem : tap j i ∈ res.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      exact appendSpecs_taps_lt _ _ _ hmem,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit 6 (by omega) (bank l) (name l) (x (key l)) (site l))
  have hdata_len : data.length = a := by simp [data]
  have hidx : 6 * j.val + i.val < specs.length := by rw [hspecs_len]; omega
  have hev := appendSpecs_eval specs data (by simpa [hdata_len] using hspecs_lt) (6 * j.val + i.val) hidx
  rw [hdata_len] at hev
  change (wiresFrom res.1 data).getD (tap j i) false = x j i
  rw [hev]
  have hspec_at : specs[6 * j.val + i.val] =
      (false, (k6Idxs i).map (fun r => 7 * j.val + r.val)) := by
    have h := flatMap_const_getElem n 6
      (fun j => (List.finRange 6).map (fun i =>
        (false, (k6Idxs i).map (fun r => 7 * j.val + r.val))))
      (fun _ => by simp) j i
    simpa [specs] using h
  rw [hspec_at]
  have hgetR : ∀ r : Fin 7, data.getD (7 * j.val + r.val) false = k6Read (x j) r := by
    intro r
    have hlt : 7 * j.val + r.val < a := by omega
    simp only [data]
    rw [getD_ofFn_lt _ _ _ hlt]
    have hkj : key ⟨7 * j.val + r.val, hlt⟩ = j := Fin.ext (by simp [key]; omega)
    have hmod : (7 * j.val + r.val) % 7 = r.val := by omega
    rw [hkj]
    dsimp only [k6Read, bank, name, site]
    simp only [hmod]
    fin_cases r <;> rfl
  have hfold_map : ∀ l : List (Fin 7),
      (l.map (fun r => 7 * j.val + r.val)).foldr (fun w acc => xor (data.getD w false) acc) false =
        l.foldr (fun r acc => xor (k6Read (x j) r) acc) false := by
    intro l
    induction l with
    | nil => rfl
    | cons r l ih => simp only [List.map_cons, List.foldr_cons, hgetR r, ih]
  rw [hfold_map, k6_formulas]

def tileKey (n P : ℕ) (hP : 0 < P) (l : Fin (n * P)) : Fin n :=
  ⟨l.val / P, Nat.div_lt_of_lt_mul (Nat.mul_comm n P ▸ l.isLt)⟩

def tileSite (k d n : ℕ) (hdk : d ≤ k) (hd1 : 1 ≤ d) (l : Fin (n * (d + (d + 1) / 2))) : Fin k :=
  let P := d + (d + 1) / 2
  let u := l.val % P
  if hu : u < 3 * (d / 2) then ⟨2 * (u / 3), by omega⟩
  else ⟨2 * (d / 2), by
    have hlt : u < P := Nat.mod_lt _ (by omega)
    omega⟩

def tileName (k d n : ℕ) (hk4 : 4 ≤ k) (hdk : d ≤ k) (hd1 : 1 ≤ d)
    (l : Fin (n * (d + (d + 1) / 2))) : Fin k → Bool :=
  have hk0 : 0 < k := by omega
  let P := d + (d + 1) / 2
  let u := l.val % P
  if hu : u < 3 * (d / 2) then
    if u % 3 = 0 then fun _ => false
    else if u % 3 = 1 then singleBit k ⟨2 * (u / 3), by omega⟩
    else singleBit k (ix k hk0 (2 * (u / 3) + 3))
  else
    if u = 3 * (d / 2) then fun _ => false
    else singleBit k (ix k hk0 (2 * (d / 2) + 3))

def r0TileSpec (k d : ℕ) (j : Fin n) (t : Fin d) : Bool × List ℕ :=
  let P := d + (d + 1) / 2
  let base := j.val * P
  let p := t.val / 2
  if t.val % 2 = 0 ∧ t.val + 1 < d then (decide (k ≠ 4), [base + 3 * p, base + 3 * p + 2])
  else if t.val % 2 = 1 then (true, [base + 3 * p, base + 3 * p + 1])
  else (decide (k ≠ 4), [base + 3 * (d / 2), base + 3 * (d / 2) + 1])

lemma r0TileSpec_lt (k d n : ℕ) (j : Fin n) (t : Fin d) :
    ∀ w ∈ (r0TileSpec k d j t).2, w < n * (d + (d + 1) / 2) := by
  intro w hw
  have ht := t.isLt
  have hj : j.val * (d + (d + 1) / 2) + (d + (d + 1) / 2) ≤ n * (d + (d + 1) / 2) := by
    calc j.val * (d + (d + 1) / 2) + (d + (d + 1) / 2) = (j.val + 1) * (d + (d + 1) / 2) := by ring
      _ ≤ n * (d + (d + 1) / 2) := Nat.mul_le_mul_right _ j.isLt
  dsimp only [r0TileSpec] at hw
  split_ifs at hw with h1 h2
  · simp at hw; rcases hw with rfl | rfl <;> omega
  · simp at hw; rcases hw with rfl | rfl <;> omega
  · simp at hw; rcases hw with rfl | rfl <;> omega

lemma tileData_getD (k d n : ℕ) (hk4 : 4 ≤ k) (hdk : d ≤ k) (hd1 : 1 ≤ d)
    (x : Fin n → Fin k → Bool) (j : Fin n) (u : ℕ) (hu : u < d + (d + 1) / 2) :
    have hk0 : 0 < k := by omega
    have hP : 0 < d + (d + 1) / 2 := by omega
    let P := d + (d + 1) / 2
    let data := List.ofFn (fun l : Fin (n * P) =>
      readBit k hk0 false (tileName k d n hk4 hdk hd1 l) (x (tileKey n P hP l)) (tileSite k d n hdk hd1 l))
    have hlt : j.val * P + u < n * P := by
      calc j.val * P + u < j.val * P + P := by omega
        _ = (j.val + 1) * P := by ring
        _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
    data.getD (j.val * P + u) false =
      readBit k hk0 false (tileName k d n hk4 hdk hd1 ⟨j.val * P + u, hlt⟩)
        (x j) (tileSite k d n hdk hd1 ⟨j.val * P + u, hlt⟩) := by
  have hk0 : 0 < k := by omega
  have hP : 0 < d + (d + 1) / 2 := by omega
  set P := d + (d + 1) / 2
  have hlt : j.val * P + u < n * P := by
    calc j.val * P + u < j.val * P + P := by omega
      _ = (j.val + 1) * P := by ring
      _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
  dsimp only
  rw [getD_ofFn_lt _ _ _ hlt]
  have hkj : tileKey n P hP ⟨j.val * P + u, hlt⟩ = j := by
    apply Fin.ext; simp only [tileKey]
    rw [Nat.mul_comm j.val P, Nat.mul_add_div hP, Nat.div_eq_of_lt hu, add_zero]
  rw [hkj]

lemma eval_r0TileSpec (k d n : ℕ) (hk4 : 4 ≤ k) (hdk : d ≤ k) (hd1 : 1 ≤ d)
    (x : Fin n → Fin k → Bool) (j : Fin n) (t : Fin d) :
    have hk0 : 0 < k := by omega
    have hP : 0 < d + (d + 1) / 2 := by omega
    let P := d + (d + 1) / 2
    let data := List.ofFn (fun l : Fin (n * P) =>
      readBit k hk0 false (tileName k d n hk4 hdk hd1 l) (x (tileKey n P hP l)) (tileSite k d n hdk hd1 l))
    (r0TileSpec k d j t).2.foldr (fun w acc => xor (data.getD w false) acc) (r0TileSpec k d j t).1 =
      wMix k hk0 1 (wRot k hk0 1 (x j)) (ix k hk0 (t.val + 1)) := by
  have hk0 : 0 < k := by omega
  have hP : 0 < d + (d + 1) / 2 := by omega
  set P := d + (d + 1) / 2
  set data := List.ofFn (fun l : Fin (n * P) =>
    readBit k hk0 false (tileName k d n hk4 hdk hd1 l) (x (tileKey n P hP l)) (tileSite k d n hdk hd1 l))
  dsimp only [r0TileSpec]
  have ht := t.isLt
  have hmod_u : ∀ u : ℕ, u < P → (j.val * P + u) % (d + (d + 1) / 2) = u := fun u hu => Nat.mul_add_mod_of_lt hu
  have hlt_u : ∀ u : ℕ, u < P → j.val * P + u < n * P := fun u hu => by
    calc j.val * P + u < j.val * P + P := by omega
      _ = (j.val + 1) * P := by ring
      _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
  split_ifs with h1 h2
  · simp only [List.foldr_cons, List.foldr_nil]
    set p := t.val / 2
    have hu0 : 3 * p < P := by omega
    have hu2 : 3 * p + 2 < P := by omega
    rw [Nat.add_assoc (j.val * P) (3 * p) 2,
        tileData_getD k d n hk4 hdk hd1 x j (3 * p) hu0,
        tileData_getD k d n hk4 hdk hd1 x j (3 * p + 2) hu2]
    have hs0 : tileSite k d n hdk hd1 ⟨j.val * P + 3 * p, hlt_u _ hu0⟩ = ⟨2 * p, by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod_u (3 * p) hu0, show 3 * p < 3 * (d / 2) by omega, ↓reduceDIte]; omega
    have hs2 : tileSite k d n hdk hd1 ⟨j.val * P + (3 * p + 2), hlt_u _ hu2⟩ = ⟨2 * p, by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod_u (3 * p + 2) hu2, show 3 * p + 2 < 3 * (d / 2) by omega, ↓reduceDIte]; omega
    have hn0 : tileName k d n hk4 hdk hd1 ⟨j.val * P + 3 * p, hlt_u _ hu0⟩ = (fun _ => false) := by
      simp only [tileName, hmod_u (3 * p) hu0]
      have hlt : 3 * p < 3 * (d / 2) := by omega
      simp [hlt]
    have hn2 : tileName k d n hk4 hdk hd1 ⟨j.val * P + (3 * p + 2), hlt_u _ hu2⟩ = singleBit k (ix k hk0 (2 * p + 3)) := by
      simp only [tileName, hmod_u (3 * p + 2) hu2]
      have hlt : 3 * p + 2 < 3 * (d / 2) := by omega
      have hdiv : (3 * p + 2) / 3 = p := by omega
      have hmod0 : (3 * p + 2) % 3 ≠ 0 := by omega
      have hmod1 : (3 * p + 2) % 3 ≠ 1 := by omega
      simp [hlt, hdiv, hmod0, hmod1]
    rw [hs0, hs2, hn0, hn2]
    have hrd := rowDiff2_ge4 k hk4 (x j) ⟨2 * p, by omega⟩
    dsimp only at hrd
    have ht_eq : 2 * p + 1 = t.val + 1 := by omega
    rw [ht_eq] at hrd
    have hxor_comm_c : ∀ a b c : Bool, xor a (xor b c) = xor (xor b a) c := by
      intro a b c; cases a <;> cases b <;> cases c <;> rfl
    rw [hxor_comm_c, hrd]
    by_cases hk4' : k = 4 <;> simp [hk4']
  · simp only [List.foldr_cons, List.foldr_nil]
    set p := t.val / 2
    have hu0 : 3 * p < P := by omega
    have hu1 : 3 * p + 1 < P := by omega
    rw [Nat.add_assoc (j.val * P) (3 * p) 1,
        tileData_getD k d n hk4 hdk hd1 x j (3 * p) hu0,
        tileData_getD k d n hk4 hdk hd1 x j (3 * p + 1) hu1]
    have hs0 : tileSite k d n hdk hd1 ⟨j.val * P + 3 * p, hlt_u _ hu0⟩ = ⟨2 * p, by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod_u (3 * p) hu0, show 3 * p < 3 * (d / 2) by omega, ↓reduceDIte]; omega
    have hs1 : tileSite k d n hdk hd1 ⟨j.val * P + (3 * p + 1), hlt_u _ hu1⟩ = ⟨2 * p, by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod_u (3 * p + 1) hu1, show 3 * p + 1 < 3 * (d / 2) by omega, ↓reduceDIte]; omega
    have hn0 : tileName k d n hk4 hdk hd1 ⟨j.val * P + 3 * p, hlt_u _ hu0⟩ = (fun _ => false) := by
      simp only [tileName, hmod_u (3 * p) hu0]
      have hlt : 3 * p < 3 * (d / 2) := by omega
      simp [hlt]
    have hn1 : tileName k d n hk4 hdk hd1 ⟨j.val * P + (3 * p + 1), hlt_u _ hu1⟩ = singleBit k ⟨2 * p, by omega⟩ := by
      simp only [tileName, hmod_u (3 * p + 1) hu1]
      have hlt : 3 * p + 1 < 3 * (d / 2) := by omega
      have hdiv : (3 * p + 1) / 3 = p := by omega
      have hmod0 : (3 * p + 1) % 3 ≠ 0 := by omega
      have hmod1 : (3 * p + 1) % 3 = 1 := by omega
      simp [hlt, hdiv, hmod0, hmod1]
    rw [hs0, hs1, hn0, hn1]
    have hrd := rowDiff1_ge4 k hk4 (x j) ⟨2 * p, by omega⟩
    dsimp only at hrd
    have ht_eq : 2 * p + 2 = t.val + 1 := by omega
    rw [ht_eq] at hrd
    have hxor_comm_c : ∀ a b : Bool, xor a (xor b true) = !(xor b a) := by
      intro a b; cases a <;> cases b <;> rfl
    rw [hxor_comm_c, hrd, Bool.not_not]
  · simp only [List.foldr_cons, List.foldr_nil]
    have hu0 : 3 * (d / 2) < P := by omega
    have hu1 : 3 * (d / 2) + 1 < P := by omega
    rw [Nat.add_assoc (j.val * P) (3 * (d / 2)) 1,
        tileData_getD k d n hk4 hdk hd1 x j (3 * (d / 2)) hu0,
        tileData_getD k d n hk4 hdk hd1 x j (3 * (d / 2) + 1) hu1]
    have hs0 : tileSite k d n hdk hd1 ⟨j.val * P + 3 * (d / 2), hlt_u _ hu0⟩ = ⟨2 * (d / 2), by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod_u (3 * (d / 2)) hu0, show ¬(3 * (d / 2) < 3 * (d / 2)) by omega, ↓reduceDIte]
    have hs1 : tileSite k d n hdk hd1 ⟨j.val * P + (3 * (d / 2) + 1), hlt_u _ hu1⟩ = ⟨2 * (d / 2), by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod_u (3 * (d / 2) + 1) hu1, show ¬(3 * (d / 2) + 1 < 3 * (d / 2)) by omega, ↓reduceDIte]
    have hn0 : tileName k d n hk4 hdk hd1 ⟨j.val * P + 3 * (d / 2), hlt_u _ hu0⟩ = (fun _ => false) := by
      simp only [tileName, hmod_u (3 * (d / 2)) hu0]; simp
    have hn1 : tileName k d n hk4 hdk hd1 ⟨j.val * P + (3 * (d / 2) + 1), hlt_u _ hu1⟩ =
        singleBit k (ix k hk0 (2 * (d / 2) + 3)) := by
      simp only [tileName, hmod_u (3 * (d / 2) + 1) hu1]
      have hge : ¬(3 * (d / 2) + 1 < 3 * (d / 2)) := by omega
      have hne : 3 * (d / 2) + 1 ≠ 3 * (d / 2) := by omega
      simp [hge, hne]
    rw [hs0, hs1, hn0, hn1]
    have hrd := rowDiff2_ge4 k hk4 (x j) ⟨2 * (d / 2), by omega⟩
    dsimp only at hrd
    have ht_eq : 2 * (d / 2) + 1 = t.val + 1 := by omega
    rw [ht_eq] at hrd
    have hxor_comm_c : ∀ a b c : Bool, xor a (xor b c) = xor (xor b a) c := by
      intro a b c; cases a <;> cases b <;> cases c <;> rfl
    rw [hxor_comm_c, hrd]
    by_cases hk4' : k = 4 <;> simp [hk4']

lemma upper_ge4_ndiv3 (k : ℕ) (hk4 : 4 ≤ k) (hndiv : ¬ 3 ∣ k) (n q : ℕ) (hq : n * priceVal k ≤ q) :
    have hk0 : 0 < k := by omega
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
      (C : Circuit) (tap : Fin n → Fin k → ℕ),
      a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal k ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i := by
  have hk0 : 0 < k := by omega
  have hk6 : k ≠ 6 := by intro h; subst h; exact hndiv (by decide)
  have hloss0 : lossVal k = 0 := by
    simp only [lossVal]; split_ifs with h
    · exact absurd h.2 hndiv
    · rfl
  have hd_eq : dVal k = k := by simp [dVal, hloss0]
  have hprice_eq : priceVal k = k + (k + 1) / 2 := by simp [priceVal, hk6, hd_eq]
  have hd1 : 1 ≤ k := by omega
  let P := k + (k + 1) / 2
  have hP : 0 < P := by omega
  let a := n * P
  have haq : a ≤ q := by dsimp only [a, P]; rw [hprice_eq] at hq; exact hq
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := tileKey n P hP
  let site : Fin a → Fin k := tileSite k k n le_rfl hd1
  let name : Fin a → Fin k → Bool := tileName k k n hk4 le_rfl hd1
  let r0Specs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange k).map (fun t => r0TileSpec k k j t))
  let st1 := appendSpecs a r0Specs
  let w1 := a + st1.1.length
  let tapR0_t : Fin n → Fin k → ℕ := fun j t => st1.2.getD (k * j.val + t.val) 0
  let tapR0 : Fin n → Fin k → ℕ := fun j r => tapR0_t j ⟨(r.val + k - 1) % k, Nat.mod_lt _ hk0⟩
  let outSpecs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange k).map (fun i =>
      (false, (invMixIndices k hk4 i).map (tapR0 j))))
  let st2 := appendSpecs w1 outSpecs
  let C : Circuit := ⟨st1.1 ++ st2.1, 0⟩
  let tap : Fin n → Fin k → ℕ := fun j i => st2.2.getD (k * j.val + i.val) 0
  have hr0_lt : ∀ s ∈ r0Specs, ∀ w ∈ s.2, w < a := by
    intro s hs w hw
    simp only [r0Specs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, t, rfl⟩ := hs
    exact r0TileSpec_lt k k n j t w hw
  have hr0_len : r0Specs.length = k * n := by simp [r0Specs, List.length_flatMap]; ring
  have htapR0_lt : ∀ j r, tapR0 j r < w1 := by
    intro j r
    set t : Fin k := ⟨(r.val + k - 1) % k, Nat.mod_lt _ hk0⟩
    have hi : k * j.val + t.val < st1.2.length := by
      rw [appendSpecs_taps_len, hr0_len]; nlinarith [j.isLt, t.isLt]
    have hmem : tapR0 j r ∈ st1.2 := by
      dsimp only [tapR0, tapR0_t]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact appendSpecs_taps_lt _ _ _ hmem
  have hout_lt : ∀ s ∈ outSpecs, ∀ w ∈ s.2, w < w1 := by
    intro s hs w hw
    simp only [outSpecs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    simp only [List.mem_map] at hw
    obtain ⟨r, _, rfl⟩ := hw
    exact htapR0_lt j r
  have hout_len : outSpecs.length = k * n := by simp [outSpecs, List.length_flatMap]; ring
  refine ⟨a, bank, key, name, site, C, tap, haq,
    ⟨readsBack_of_list _ _ (readsBackList_append a st1.1 st2.1
        (appendSpecs_readsBack a r0Specs hr0_lt) (appendSpecs_readsBack w1 outSpecs hout_lt)),
      fun g hg => by
        simp only [C, List.mem_append] at hg
        rcases hg with h | h
        · exact appendSpecs_fanin _ _ g h
        · exact appendSpecs_fanin _ _ g h⟩,
    by simp [C, List.countP_append, st1, st2, appendSpecs_nonlin],
    fun j i => by
      have hi : k * j.val + i.val < st2.2.length := by
        rw [appendSpecs_taps_len, hout_len]; nlinarith [j.isLt, i.isLt]
      have hmem : tap j i ∈ st2.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      have hlt := appendSpecs_taps_lt _ _ _ hmem
      dsimp only [C, w1, st1, st2] at hlt ⊢
      simp only [List.length_append]
      omega,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l))
  have hdata_len : data.length = a := by simp [data]
  set v1 := wiresFrom st1.1 data
  have hv1_len : v1.length = w1 := by rw [length_wiresFrom, hdata_len]
  have hv1_R0 : ∀ (j0 : Fin n) (r : Fin k),
      v1.getD (tapR0 j0 r) false = wMix k hk0 1 (wRot k hk0 1 (x j0)) r := by
    intro j0 r
    set t : Fin k := ⟨(r.val + k - 1) % k, Nat.mod_lt _ hk0⟩
    have hidx : k * j0.val + t.val < r0Specs.length := by rw [hr0_len]; nlinarith [j0.isLt, t.isLt]
    have hev := appendSpecs_eval r0Specs data (by simpa [hdata_len] using hr0_lt) (k * j0.val + t.val) hidx
    rw [hdata_len] at hev
    change v1.getD (tapR0_t j0 t) false = _
    rw [hev]
    have hspec_at : r0Specs[k * j0.val + t.val] = r0TileSpec k k j0 t := by
      have h := flatMap_const_getElem n k
        (fun j0 => (List.finRange k).map (fun t => r0TileSpec k k j0 t))
        (fun _ => by simp) j0 t
      simpa [r0Specs] using h
    rw [hspec_at]
    have htile := eval_r0TileSpec k k n hk4 le_rfl hd1 x j0 t
    dsimp only at htile
    have ht_ix : ix k hk0 (t.val + 1) = r := by
      apply Fin.ext; simp only [ix, t]
      rw [mod_add_cancel, show r.val + k - 1 + 1 = r.val + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt r.isLt]
    rw [ht_ix] at htile
    exact htile
  change (wiresFrom (st1.1 ++ st2.1) data).getD (tap j i) false = x j i
  rw [wiresFrom_append]
  have hidx : k * j.val + i.val < outSpecs.length := by rw [hout_len]; nlinarith [j.isLt, i.isLt]
  have hev := appendSpecs_eval outSpecs v1 (by simpa [hv1_len] using hout_lt) (k * j.val + i.val) hidx
  rw [hv1_len] at hev
  rw [hev]
  have hspec_at : outSpecs[k * j.val + i.val] = (false, (invMixIndices k hk4 i).map (tapR0 j)) := by
    have h := flatMap_const_getElem n k
      (fun j => (List.finRange k).map (fun i => (false, (invMixIndices k hk4 i).map (tapR0 j))))
      (fun _ => by simp) j i
    simpa [outSpecs] using h
  rw [hspec_at]
  have hfold_map : ∀ l : List (Fin k),
      (l.map (tapR0 j)).foldr (fun w acc => xor (v1.getD w false) acc) false =
        l.foldr (fun r acc => xor (wMix k hk0 1 (wRot k hk0 1 (x j)) r) acc) false := by
    intro l
    induction l with
    | nil => rfl
    | cons r l ih => simp only [List.map_cons, List.foldr_cons, hv1_R0 j r, ih]
  rw [hfold_map]
  exact invMixIndices_correct k hk4 hndiv (x j) i

lemma eval_nlBlock_wires (v : List Bool) (w1 w2 w3 w4 : ℕ)
    (h2 : w2 < v.length) (h3 : w3 < v.length) (h4 : w4 < v.length) :
    let gs := [mkNot w1, mkAnd v.length w2, mkNot w3, mkAnd (v.length + 2) w4]
    (wiresFrom gs v).getD (v.length + 1) false = (!(v.getD w1 false) && v.getD w2 false) ∧
    (wiresFrom gs v).getD (v.length + 3) false = (!(v.getD w3 false) && v.getD w4 false) := by
  dsimp only
  simp only [wiresFrom_cons, wiresFrom_nil]
  set b1 := (mkNot w1).op.eval ((mkNot w1).inputs.map fun w => v.getD w false)
  have hb1 : b1 = !(v.getD w1 false) := eval_mkNot w1 v
  set v1 := v ++ [b1]
  have hv1_len : v1.length = v.length + 1 := by simp [v1]
  set b2 := (mkAnd v.length w2).op.eval ((mkAnd v.length w2).inputs.map fun w => v1.getD w false)
  have hb2 : b2 = (!(v.getD w1 false) && v.getD w2 false) := by
    dsimp only [b2]; rw [eval_mkAnd]
    have hg1 : v1.getD v.length false = b1 := getD_snoc_self v b1
    have hg2 : v1.getD w2 false = v.getD w2 false := List.getD_append _ _ _ _ h2
    rw [hg1, hg2, hb1]
  set v2 := v1 ++ [b2]
  have hv2_len : v2.length = v.length + 2 := by simp [v2, hv1_len]
  set b3 := (mkNot w3).op.eval ((mkNot w3).inputs.map fun w => v2.getD w false)
  have hb3 : b3 = !(v.getD w3 false) := by
    dsimp only [b3]; rw [eval_mkNot]
    have hg3 : v2.getD w3 false = v.getD w3 false := by
      rw [show v2 = v ++ [b1, b2] by simp [v2, v1], List.getD_append _ _ _ _ h3]
    rw [hg3]
  set v3 := v2 ++ [b3]
  have hv3_len : v3.length = v.length + 3 := by simp [v3, hv2_len]
  set b4 := (mkAnd (v.length + 2) w4).op.eval ((mkAnd (v.length + 2) w4).inputs.map fun w => v3.getD w false)
  have hb4 : b4 = (!(v.getD w3 false) && v.getD w4 false) := by
    dsimp only [b4]; rw [eval_mkAnd]
    have hg1 : v3.getD (v.length + 2) false = b3 := by rw [← hv2_len]; exact getD_snoc_self v2 b3
    have hg2 : v3.getD w4 false = v.getD w4 false := by
      rw [show v3 = v ++ [b1, b2, b3] by simp [v3, v2, v1], List.getD_append _ _ _ _ h4]
    rw [hg1, hg2, hb3]
  constructor
  · rw [show v3 ++ [b4] = v2 ++ [b3, b4] by simp [v3],
        List.getD_append _ _ _ _ (by rw [hv2_len]; omega),
        show v.length + 1 = v1.length from hv1_len.symm, getD_snoc_self, hb2]
  · rw [show v.length + 3 = v3.length from hv3_len.symm, getD_snoc_self, hb4]

set_option maxHeartbeats 800000 in
lemma upper_ge9_div3 (k : ℕ) (hk9 : 9 ≤ k) (h3 : 3 ∣ k) (n q : ℕ) (hq : n * priceVal k ≤ q) :
    have hk0 : 0 < k := by omega
    ∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
      (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
      (C : Circuit) (tap : Fin n → Fin k → ℕ),
      a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal k ∧
      (∀ j i, tap j i < a + C.gates.length) ∧
      ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i := by
  have hk0 : 0 < k := by omega
  have hk2 : 2 ≤ k := by omega
  have hk4 : 4 ≤ k := by omega
  have hk6 : k ≠ 6 := by omega
  have hloss2 : lossVal k = 2 := by simp [lossVal, hk9, h3]
  let d := k - 2
  have hd_eq : dVal k = d := by simp [dVal, hloss2, d]
  have hprice_eq : priceVal k = d + (d + 1) / 2 := by simp [priceVal, hk6, hd_eq]
  have hdk : d ≤ k := by omega
  have hd1 : 1 ≤ d := by omega
  let P := d + (d + 1) / 2
  have hP : 0 < P := by omega
  let a := n * P
  have haq : a ≤ q := by dsimp only [a, P]; rw [hprice_eq] at hq; exact hq
  let bank : Fin a → Bool := fun _ => false
  let key : Fin a → Fin n := tileKey n P hP
  let site : Fin a → Fin k := tileSite k d n hdk hd1
  let name : Fin a → Fin k → Bool := tileName k d n hk4 hdk hd1
  let r0MidSpecs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange d).map (fun t => r0TileSpec k d j t))
  let st1a := appendSpecs a r0MidSpecs
  let w1a := a + st1a.1.length
  let tapR0_mid : Fin n → Fin d → ℕ := fun j t => st1a.2.getD (d * j.val + t.val) 0
  let K := k / 3
  have hK3 : 3 ≤ K := by omega
  have h3K : 3 * K = k := by omega
  let specR0_0 : Fin n → Bool × List ℕ := fun j =>
    (false,
      ((List.finRange K).map (fun m => tapR0_mid j ⟨3 * m.val, by omega⟩)) ++
      ((List.finRange (K - 1)).map (fun m => tapR0_mid j ⟨3 * m.val + 2, by omega⟩)))
  let specR0_last : Fin n → Bool × List ℕ := fun j =>
    (false,
      ((List.finRange K).map (fun m => tapR0_mid j ⟨3 * m.val, by omega⟩)) ++
      ((List.finRange (K - 1)).map (fun m => tapR0_mid j ⟨3 * m.val + 1, by omega⟩)))
  let r0MissSpecs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => [specR0_0 j, specR0_last j])
  let st1b := appendSpecs w1a r0MissSpecs
  let w1b := w1a + st1b.1.length
  let tapR0_0 : Fin n → ℕ := fun j => st1b.2.getD (2 * j.val) 0
  let tapR0_last : Fin n → ℕ := fun j => st1b.2.getD (2 * j.val + 1) 0
  let tapR0 : Fin n → Fin k → ℕ := fun j r =>
    if h0 : r.val = 0 then tapR0_0 j
    else if hl : r.val = k - 1 then tapR0_last j
    else tapR0_mid j ⟨r.val - 1, by omega⟩
  let nlBlock : Fin n → List Gate := fun j =>
    [mkNot (tapR0 j ⟨1, by omega⟩),
     mkAnd (w1b + 4 * j.val) (tapR0 j ⟨2, by omega⟩),
     mkNot (tapR0 j ⟨3, by omega⟩),
     mkAnd (w1b + 4 * j.val + 2) (tapR0 j ⟨4, by omega⟩)]
  let nlGates : List Gate := (List.finRange n).flatMap nlBlock
  let w2 := w1b + nlGates.length
  let x0Wires : Fin n → List ℕ := fun j =>
    [j.val * P, tapR0 j ⟨0, hk0⟩, w1b + 4 * j.val + 1]
  let x2Wires : Fin n → List ℕ := fun j =>
    [j.val * P + 3, tapR0 j ⟨2, by omega⟩, w1b + 4 * j.val + 3]
  let x1Wires : Fin n → List ℕ := fun j =>
    x0Wires j ++ x2Wires j ++ [tapR0 j ⟨2, by omega⟩]
  let outSpecs : List (Bool × List ℕ) :=
    (List.finRange n).flatMap (fun j => (List.finRange k).map (fun i =>
      let ws0 := if recAnchor0 i.val then x0Wires j else []
      let ws1 := if recAnchor1 i.val then x1Wires j else []
      let wsR := (recR0Indices k hk0 i.val).map (tapR0 j)
      (false, ws0 ++ ws1 ++ wsR)))
  let st3 := appendSpecs w2 outSpecs
  let C : Circuit := ⟨st1a.1 ++ st1b.1 ++ nlGates ++ st3.1, 0⟩
  let tap : Fin n → Fin k → ℕ := fun j i => st3.2.getD (k * j.val + i.val) 0
  have hr0Mid_lt : ∀ s ∈ r0MidSpecs, ∀ w ∈ s.2, w < a := by
    intro s hs w hw
    simp only [r0MidSpecs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, t, rfl⟩ := hs
    exact r0TileSpec_lt k d n j t w hw
  have hr0Mid_len : r0MidSpecs.length = d * n := by simp [r0MidSpecs, List.length_flatMap]; ring
  have htapMid_lt : ∀ j t, tapR0_mid j t < w1a := by
    intro j t
    have hi : d * j.val + t.val < st1a.2.length := by
      rw [appendSpecs_taps_len, hr0Mid_len]; nlinarith [j.isLt, t.isLt]
    have hmem : tapR0_mid j t ∈ st1a.2 := by
      dsimp only [tapR0_mid]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact appendSpecs_taps_lt _ _ _ hmem
  have hr0Miss_lt : ∀ s ∈ r0MissSpecs, ∀ w ∈ s.2, w < w1a := by
    intro s hs w hw
    simp only [r0MissSpecs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_cons,
      List.not_mem_nil, or_false] at hs
    obtain ⟨j, rfl | rfl⟩ := hs
    · simp only [specR0_0, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨m, _, rfl⟩ | ⟨m, _, rfl⟩ <;> exact htapMid_lt j _
    · simp only [specR0_last, List.mem_append, List.mem_map] at hw
      rcases hw with ⟨m, _, rfl⟩ | ⟨m, _, rfl⟩ <;> exact htapMid_lt j _
  have hr0Miss_len : r0MissSpecs.length = 2 * n := by simp [r0MissSpecs, List.length_flatMap]; omega
  have htap0_lt : ∀ j, tapR0_0 j < w1b := by
    intro j
    have hi : 2 * j.val < st1b.2.length := by rw [appendSpecs_taps_len, hr0Miss_len]; omega
    have hmem : tapR0_0 j ∈ st1b.2 := by
      dsimp only [tapR0_0]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact appendSpecs_taps_lt _ _ _ hmem
  have htapLast_lt : ∀ j, tapR0_last j < w1b := by
    intro j
    have hi : 2 * j.val + 1 < st1b.2.length := by rw [appendSpecs_taps_len, hr0Miss_len]; omega
    have hmem : tapR0_last j ∈ st1b.2 := by
      dsimp only [tapR0_last]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
    exact appendSpecs_taps_lt _ _ _ hmem
  have htapR0_lt : ∀ j r, tapR0 j r < w1b := by
    intro j r
    dsimp only [tapR0]
    split_ifs with h0 hl
    · exact htap0_lt j
    · exact htapLast_lt j
    · have := htapMid_lt j ⟨r.val - 1, by omega⟩; omega
  have hnl_len : nlGates.length = 4 * n := by
    have h4 : ∀ j : Fin n, (nlBlock j).length = 4 := fun _ => rfl
    simp [nlGates, List.length_flatMap, h4]; ring
  have hnl_nonlin : nlGates.countP isNonlin = 2 * n := by
    have hgen : ∀ (m : ℕ) (f : Fin m → List Gate),
        (∀ j, (f j).countP isNonlin = 2) → ((List.finRange m).flatMap f).countP isNonlin = 2 * m := by
      intro m
      induction m with
      | zero => intro f _; rfl
      | succ m ih =>
        intro f hf
        simp only [List.finRange_succ, List.flatMap_cons, List.countP_append, List.flatMap_map]
        rw [hf 0, ih (fun j => f j.succ) (fun j => hf j.succ)]
        omega
    apply hgen n nlBlock
    intro j
    rfl
  have hnl_fanin : ∀ g ∈ nlGates, g.inputs.length ≤ 2 := by
    intro g hg
    simp only [nlGates, List.mem_flatMap, List.mem_finRange, true_and, nlBlock, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ := hg <;> simp [mkNot, mkAnd]
  have hnl_rb : ReadsBackList w1b nlGates := by
    intro idx hidx i hi
    have hj_lt : idx / 4 < n := by rw [hnl_len] at hidx; omega
    let j : Fin n := ⟨idx / 4, hj_lt⟩
    let r : Fin 4 := ⟨idx % 4, Nat.mod_lt _ (by omega)⟩
    have hidx_eq : 4 * j.val + r.val = idx := by dsimp only [j, r]; omega
    have hget : nlGates[idx] = (nlBlock j)[r.val]'(by exact r.isLt) := by
      have hfm := flatMap_const_getElem n 4 nlBlock (fun _ => rfl) j r
      simpa [nlGates, hidx_eq] using hfm
    rw [hget] at hi
    have hr4 : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 := by omega
    rcases hr4 with h0 | h1 | h2 | h3'
    · simp only [h0, nlBlock, List.getElem_cons_zero, mkNot, List.mem_cons, List.not_mem_nil, or_false] at hi
      subst hi; exact Nat.lt_of_lt_of_le (htapR0_lt j _) (Nat.le_add_right _ _)
    · simp only [h1, nlBlock, List.getElem_cons_succ, List.getElem_cons_zero, mkAnd, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · dsimp only [j]; omega
      · exact Nat.lt_of_lt_of_le (htapR0_lt j _) (Nat.le_add_right _ _)
    · simp only [h2, nlBlock, List.getElem_cons_succ, List.getElem_cons_zero, mkNot, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      subst hi; exact Nat.lt_of_lt_of_le (htapR0_lt j _) (Nat.le_add_right _ _)
    · simp only [h3', nlBlock, List.getElem_cons_succ, List.getElem_cons_zero, mkAnd, List.mem_cons,
        List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · dsimp only [j]; omega
      · exact Nat.lt_of_lt_of_le (htapR0_lt j _) (Nat.le_add_right _ _)
  have hout_lt : ∀ s ∈ outSpecs, ∀ w ∈ s.2, w < w2 := by
    intro s hs w hw
    simp only [outSpecs, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hs
    obtain ⟨j, i, rfl⟩ := hs
    have hjP : j.val * P + P ≤ n * P := by
      calc j.val * P + P = (j.val + 1) * P := by ring
        _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
    have hx0_lt : ∀ w ∈ x0Wires j, w < w2 := by
      intro w hw; simp only [x0Wires, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · omega
      · have := htapR0_lt j ⟨0, hk0⟩; omega
      · rw [show w2 = w1b + 4 * n by simp [w2, hnl_len]]; omega
    have hx2_lt : ∀ w ∈ x2Wires j, w < w2 := by
      intro w hw; simp only [x2Wires, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · omega
      · have := htapR0_lt j ⟨2, by omega⟩; omega
      · rw [show w2 = w1b + 4 * n by simp [w2, hnl_len]]; omega
    have hx1_lt : ∀ w ∈ x1Wires j, w < w2 := by
      intro w hw; simp only [x1Wires, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (h | h) | rfl
      · exact hx0_lt w h
      · exact hx2_lt w h
      · have := htapR0_lt j ⟨2, by omega⟩; omega
    simp only [List.mem_append, List.mem_map] at hw
    rcases hw with (h | h) | ⟨r, _, rfl⟩
    · split_ifs at h with h0
      · exact hx0_lt w h
      · simp at h
    · split_ifs at h with h1
      · exact hx1_lt w h
      · simp at h
    · have := htapR0_lt j r; omega
  have hout_len : outSpecs.length = k * n := by simp [outSpecs, List.length_flatMap]; ring
  have hC_rb : ReadsBackList a C.gates := by
    dsimp only [C]
    apply readsBackList_append
    · apply readsBackList_append
      · apply readsBackList_append
        · exact appendSpecs_readsBack _ _ hr0Mid_lt
        · exact appendSpecs_readsBack _ _ hr0Miss_lt
      · simp only [List.length_append]
        rw [show a + (st1a.1.length + st1b.1.length) = w1b by simp [w1b, w1a]; omega]
        exact hnl_rb
    · simp only [List.length_append]
      rw [show a + (st1a.1.length + st1b.1.length + nlGates.length) = w2 by simp [w2, w1b, w1a]; omega]
      exact appendSpecs_readsBack _ _ hout_lt
  have hC_fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    intro g hg
    simp only [C, List.mem_append] at hg
    rcases hg with ((h | h) | h) | h
    · exact appendSpecs_fanin _ _ g h
    · exact appendSpecs_fanin _ _ g h
    · exact hnl_fanin g h
    · exact appendSpecs_fanin _ _ g h
  have hC_nl : C.gates.countP isNonlin ≤ n * lossVal k := by
    dsimp only [C, st1a, st1b, st3]
    simp only [List.countP_append, appendSpecs_nonlin, hnl_nonlin, hloss2]
    omega
  refine ⟨a, bank, key, name, site, C, tap, haq,
    ⟨readsBack_of_list _ _ hC_rb, hC_fan⟩, hC_nl,
    fun j i => by
      have hi : k * j.val + i.val < st3.2.length := by
        rw [appendSpecs_taps_len, hout_len]; nlinarith [j.isLt, i.isLt]
      have hmem : tap j i ∈ st3.2 := by
        dsimp only [tap]; rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
      have hlt := appendSpecs_taps_lt _ _ _ hmem
      dsimp only [C, w2, w1b, w1a, st1a, st1b, st3] at hlt ⊢
      simp only [List.length_append]
      omega,
    fun x j i => ?_⟩
  set data := List.ofFn (fun l : Fin a => readBit k hk0 (bank l) (name l) (x (key l)) (site l))
  have hdata_len : data.length = a := by simp [data]
  set v1a := wiresFrom st1a.1 data
  have hv1a_len : v1a.length = w1a := by rw [length_wiresFrom, hdata_len]
  set v1b := wiresFrom st1b.1 v1a
  have hv1b_len : v1b.length = w1b := by rw [length_wiresFrom, hv1a_len]
  set v2 := wiresFrom nlGates v1b
  have hv2_len : v2.length = w2 := by rw [length_wiresFrom, hv1b_len]
  have hv1a_mid : ∀ (j0 : Fin n) (t : Fin d),
      v1a.getD (tapR0_mid j0 t) false = wMix k hk0 1 (wRot k hk0 1 (x j0)) ⟨t.val + 1, by omega⟩ := by
    intro j0 t
    have hidx : d * j0.val + t.val < r0MidSpecs.length := by rw [hr0Mid_len]; nlinarith [j0.isLt, t.isLt]
    have hev := appendSpecs_eval r0MidSpecs data (by simpa [hdata_len] using hr0Mid_lt) (d * j0.val + t.val) hidx
    rw [hdata_len] at hev
    change v1a.getD (tapR0_mid j0 t) false = _
    rw [hev]
    have hspec_at : r0MidSpecs[d * j0.val + t.val] = r0TileSpec k d j0 t := by
      have h := flatMap_const_getElem n d
        (fun j0 => (List.finRange d).map (fun t => r0TileSpec k d j0 t))
        (fun _ => by simp) j0 t
      simpa [r0MidSpecs] using h
    rw [hspec_at]
    have htile := eval_r0TileSpec k d n hk4 hdk hd1 x j0 t
    dsimp only at htile
    have ht_ix : ix k hk0 (t.val + 1) = ⟨t.val + 1, by omega⟩ := by
      apply Fin.ext; simp only [ix, Nat.mod_eq_of_lt (by omega : t.val + 1 < k)]
    rw [ht_ix] at htile
    exact htile
  have hv1b_R0 : ∀ (j0 : Fin n) (r : Fin k),
      v1b.getD (tapR0 j0 r) false = wMix k hk0 1 (wRot k hk0 1 (x j0)) r := by
    intro j0 r
    set R0 := wMix k hk0 1 (wRot k hk0 1 (x j0))
    have hsum_finRange : ∀ (M : ℕ) (f : Fin M → ℕ) (g : ℕ → ZMod 2),
        ((List.finRange M).map (fun m => g (f m))).sum =
          ((List.range M).map (fun m => if hm : m < M then g (f ⟨m, hm⟩) else 0)).sum := by
      intro M f g
      congr 1
      apply List.ext_getElem (by simp)
      intro idx h1 h2
      simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
      have hidx : idx < M := by simpa using h1
      simp [hidx]
    dsimp only [tapR0]
    split_ifs with h0 hl
    · have hr0 : r = ⟨0, hk0⟩ := Fin.ext h0
      rw [hr0]
      have hidx : 2 * j0.val < r0MissSpecs.length := by rw [hr0Miss_len]; omega
      have hev := appendSpecs_eval r0MissSpecs v1a (by simpa [hv1a_len] using hr0Miss_lt) (2 * j0.val) hidx
      rw [hv1a_len] at hev
      change v1b.getD (tapR0_0 j0) false = R0 ⟨0, hk0⟩
      rw [hev]
      have hspec_at : r0MissSpecs[2 * j0.val] = specR0_0 j0 := by
        have h := flatMap_const_getElem n 2 (fun j0 => [specR0_0 j0, specR0_last j0]) (fun _ => rfl) j0 0
        simpa [r0MissSpecs] using h
      rw [hspec_at]
      apply b2z_inj
      rw [foldr_xor_b2z]
      simp only [specR0_0, List.map_append, List.sum_append, List.map_map]
      have h1 : ((List.finRange K).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val, by omega⟩) false))).sum =
          ∑ i : Fin k, b2z (x j0 i) := by
        have hm1 := mod3_cosum_R0 k hk9 h3 (x j0) 1
        dsimp only at hm1
        rw [← hm1]
        congr 1
        apply List.ext_getElem (by simp [K])
        intro idx h1' h2'
        have hidxK : idx < K := by simpa using h1'
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply, Fin.val_cast]
        rw [hv1a_mid j0 ⟨3 * idx, by omega⟩]
        congr 2; apply Fin.ext; simp only [ix]
        rw [Nat.mod_eq_of_lt (by omega : 1 + 3 * idx < k)]; omega
      have h2 : ((List.finRange (K - 1)).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val + 2, by omega⟩) false))).sum +
          b2z (R0 ⟨0, hk0⟩) = ∑ i : Fin k, b2z (x j0 i) := by
        have hm0 := mod3_cosum_R0 k hk9 h3 (x j0) 0
        dsimp only at hm0
        rw [← hm0]
        have hrange : List.range K = 0 :: (List.range (K - 1)).map (fun m => m + 1) := by
          have hK_eq : K = (K - 1) + 1 := by omega
          conv_lhs => rw [hK_eq, List.range_succ_eq_map]
        rw [show k / 3 = K from rfl, hrange, List.map_cons, List.sum_cons, List.map_map]
        have h0eq : ix k hk0 (0 + 3 * 0) = ⟨0, hk0⟩ := Fin.ext (by simp [ix])
        rw [h0eq, add_comm]
        congr 1
        congr 1
        apply List.ext_getElem (by simp)
        intro idx h1' h2'
        have hidxK : idx < K - 1 := by simpa using h1'
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply, Fin.val_cast]
        rw [hv1a_mid j0 ⟨3 * idx + 2, by omega⟩]
        congr 2; apply Fin.ext; simp only [ix]
        rw [Nat.mod_eq_of_lt (by omega : 0 + 3 * (idx + 1) < k)]; omega
      change ((List.finRange K).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val, by omega⟩) false))).sum +
          ((List.finRange (K - 1)).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val + 2, by omega⟩) false))).sum =
        b2z (R0 ⟨0, hk0⟩)
      rw [h1, ← h2]
      have hcancel : ∀ u v : ZMod 2, (u + v) + u = v := by decide
      exact hcancel _ _
    · have hrl : r = ⟨k - 1, by omega⟩ := Fin.ext hl
      rw [hrl]
      have hidx : 2 * j0.val + 1 < r0MissSpecs.length := by rw [hr0Miss_len]; omega
      have hev := appendSpecs_eval r0MissSpecs v1a (by simpa [hv1a_len] using hr0Miss_lt) (2 * j0.val + 1) hidx
      rw [hv1a_len] at hev
      change v1b.getD (tapR0_last j0) false = R0 ⟨k - 1, by omega⟩
      rw [hev]
      have hspec_at : r0MissSpecs[2 * j0.val + 1] = specR0_last j0 := by
        have h := flatMap_const_getElem n 2 (fun j0 => [specR0_0 j0, specR0_last j0]) (fun _ => rfl) j0 1
        simpa [r0MissSpecs] using h
      rw [hspec_at]
      apply b2z_inj
      rw [foldr_xor_b2z]
      simp only [specR0_last, List.map_append, List.sum_append, List.map_map]
      have h1 : ((List.finRange K).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val, by omega⟩) false))).sum =
          ∑ i : Fin k, b2z (x j0 i) := by
        have hm1 := mod3_cosum_R0 k hk9 h3 (x j0) 1
        dsimp only at hm1
        rw [← hm1]
        congr 1
        apply List.ext_getElem (by simp [K])
        intro idx h1' h2'
        have hidxK : idx < K := by simpa using h1'
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply, Fin.val_cast]
        rw [hv1a_mid j0 ⟨3 * idx, by omega⟩]
        congr 2; apply Fin.ext; simp only [ix]
        rw [Nat.mod_eq_of_lt (by omega : 1 + 3 * idx < k)]; omega
      have h2 : ((List.finRange (K - 1)).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val + 1, by omega⟩) false))).sum +
          b2z (R0 ⟨k - 1, by omega⟩) = ∑ i : Fin k, b2z (x j0 i) := by
        have hm2 := mod3_cosum_R0 k hk9 h3 (x j0) 2
        dsimp only at hm2
        rw [← hm2]
        have hrange : List.range K = List.range (K - 1) ++ [K - 1] := by
          have hK_eq : K = (K - 1) + 1 := by omega
          conv_lhs => rw [hK_eq, List.range_succ]
        rw [show k / 3 = K from rfl, hrange, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
        have hleq : ix k hk0 (2 + 3 * (K - 1)) = ⟨k - 1, by omega⟩ := by
          apply Fin.ext; simp only [ix]
          rw [show 2 + 3 * (K - 1) = k - 1 by omega, Nat.mod_eq_of_lt (by omega)]
        rw [hleq]
        congr 1
        congr 1
        apply List.ext_getElem (by simp)
        intro idx h1' h2'
        have hidxK : idx < K - 1 := by simpa using h1'
        simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Function.comp_apply, Fin.val_cast]
        rw [hv1a_mid j0 ⟨3 * idx + 1, by omega⟩]
        congr 2; apply Fin.ext; simp only [ix]
        rw [Nat.mod_eq_of_lt (by omega : 2 + 3 * idx < k)]; omega
      change ((List.finRange K).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val, by omega⟩) false))).sum +
          ((List.finRange (K - 1)).map (fun m => b2z (v1a.getD (tapR0_mid j0 ⟨3 * m.val + 1, by omega⟩) false))).sum =
        b2z (R0 ⟨k - 1, by omega⟩)
      rw [h1, ← h2]
      have hcancel : ∀ u v : ZMod 2, (u + v) + u = v := by decide
      exact hcancel _ _
    · rw [getD_wiresFrom_lt st1b.1 v1a _ (by rw [hv1a_len]; exact htapMid_lt j0 _), hv1a_mid]
      congr 1; apply Fin.ext; dsimp; omega
  have hv2_nl :
      v2.getD (w1b + 4 * j.val + 1) false =
        (!(wMix k hk0 1 (wRot k hk0 1 (x j)) ⟨1, by omega⟩) &&
          wMix k hk0 1 (wRot k hk0 1 (x j)) ⟨2, by omega⟩) ∧
      v2.getD (w1b + 4 * j.val + 3) false =
        (!(wMix k hk0 1 (wRot k hk0 1 (x j)) ⟨3, by omega⟩) &&
          wMix k hk0 1 (wRot k hk0 1 (x j)) ⟨4, by omega⟩) := by
    have hsplit_fin : List.finRange n =
        ((List.finRange j.val).map (fun m => ⟨m.val, by have := m.isLt; have := j.isLt; omega⟩)) ++
        j :: ((List.finRange (n - j.val - 1)).map (fun m => ⟨j.val + 1 + m.val, by have := m.isLt; have := j.isLt; omega⟩)) := by
      have hget_cons : ∀ {α : Type} (a : α) (l : List α) (m : ℕ) (hm : m < (a :: l).length) (hm0 : 0 < m),
          (a :: l)[m] = l[m - 1]'(by simp at hm; omega) := fun a l m hm hm0 => by
        cases m with
        | zero => omega
        | succ m' => rfl
      apply List.ext_getElem
      · simp; omega
      · intro idx h1 h2
        simp only [List.getElem_finRange]
        by_cases hlt : idx < j.val
        · rw [List.getElem_append_left (by simp; omega)]
          simp [hlt]
        · rw [List.getElem_append_right (by simp; omega)]
          simp only [List.length_map, List.length_finRange]
          by_cases heq : idx = j.val
          · subst heq; simp
          · rw [hget_cons _ _ _ _ (by omega)]
            simp only [List.getElem_map, List.getElem_finRange]
            apply Fin.ext; dsimp; omega
    set gPre := ((List.finRange j.val).map (fun m => (⟨m.val, by have := m.isLt; have := j.isLt; omega⟩ : Fin n))).flatMap nlBlock
    set gPost := ((List.finRange (n - j.val - 1)).map (fun m => (⟨j.val + 1 + m.val, by have := m.isLt; have := j.isLt; omega⟩ : Fin n))).flatMap nlBlock
    have hnl_split : nlGates = gPre ++ nlBlock j ++ gPost := by
      dsimp only [nlGates, gPre, gPost]
      conv_lhs => rw [hsplit_fin]
      rw [List.flatMap_append, List.flatMap_cons, ← List.append_assoc]
    have hgPre_len : gPre.length = 4 * j.val := by
      have hgen : ∀ (l : List (Fin n)), (l.flatMap nlBlock).length = 4 * l.length := by
        intro l
        induction l with
        | nil => rfl
        | cons a l ih => simp [List.flatMap_cons, nlBlock, ih]; omega
      dsimp only [gPre]
      rw [hgen, List.length_map, List.length_finRange]
    set vPre := wiresFrom gPre v1b
    have hvPre_len : vPre.length = w1b + 4 * j.val := by rw [length_wiresFrom, hv1b_len, hgPre_len]
    set vMid := wiresFrom (nlBlock j) vPre
    have hvMid_len : vMid.length = w1b + 4 * j.val + 4 := by
      rw [length_wiresFrom, hvPre_len]; simp [nlBlock]
    have hv2_eq : v2 = wiresFrom gPost vMid := by
      change wiresFrom nlGates v1b = _
      rw [hnl_split, wiresFrom_append, wiresFrom_append]
    have hvPre_R0 : ∀ r : Fin k, vPre.getD (tapR0 j r) false = wMix k hk0 1 (wRot k hk0 1 (x j)) r := by
      intro r
      rw [getD_wiresFrom_lt gPre v1b _ (by rw [hv1b_len]; exact htapR0_lt j r), hv1b_R0]
    have hblk := eval_nlBlock_wires vPre (tapR0 j ⟨1, by omega⟩) (tapR0 j ⟨2, by omega⟩)
      (tapR0 j ⟨3, by omega⟩) (tapR0 j ⟨4, by omega⟩)
      (by rw [hvPre_len]; have := htapR0_lt j ⟨2, by omega⟩; omega)
      (by rw [hvPre_len]; have := htapR0_lt j ⟨3, by omega⟩; omega)
      (by rw [hvPre_len]; have := htapR0_lt j ⟨4, by omega⟩; omega)
    dsimp only at hblk
    rw [hvPre_len, hvPre_R0, hvPre_R0, hvPre_R0, hvPre_R0] at hblk
    constructor
    · rw [hv2_eq, getD_wiresFrom_lt gPost vMid _ (by rw [hvMid_len]; omega)]
      exact hblk.1
    · rw [hv2_eq, getD_wiresFrom_lt gPost vMid _ (by rw [hvMid_len]; omega)]
      exact hblk.2
  have hv2_R0 : ∀ r : Fin k, v2.getD (tapR0 j r) false = wMix k hk0 1 (wRot k hk0 1 (x j)) r := by
    intro r
    rw [getD_wiresFrom_lt nlGates v1b _ (by rw [hv1b_len]; exact htapR0_lt j r), hv1b_R0]
  have hv2_data : ∀ u : ℕ, u < P → v2.getD (j.val * P + u) false = data.getD (j.val * P + u) false := by
    intro u hu
    have hlt_a : j.val * P + u < a := by
      calc j.val * P + u < j.val * P + P := by omega
        _ = (j.val + 1) * P := by ring
        _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
    rw [getD_wiresFrom_lt nlGates v1b _ (by rw [hv1b_len]; omega),
        getD_wiresFrom_lt st1b.1 v1a _ (by rw [hv1a_len]; omega),
        getD_wiresFrom_lt st1a.1 data _ (by rw [hdata_len]; omega)]
  have hv2_x0 : (x0Wires j).foldr (fun w acc => xor (v2.getD w false) acc) false = x j ⟨0, hk0⟩ := by
    simp only [x0Wires, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    have hP0 : 0 < P := hP
    have hlt0 : j.val * P + 0 < n * P := by
      calc j.val * P + 0 < j.val * P + P := by omega
        _ = (j.val + 1) * P := by ring
        _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
    rw [show j.val * P = j.val * P + 0 by omega, hv2_data 0 hP0,
        tileData_getD k d n hk4 hdk hd1 x j 0 hP0, hv2_R0 ⟨0, hk0⟩, hv2_nl.1]
    have hmod0 : (j.val * P + 0) % (d + (d + 1) / 2) = 0 := Nat.mul_add_mod_of_lt hP0
    have hs0 : tileSite k d n hdk hd1 ⟨j.val * P + 0, hlt0⟩ = ⟨0, hk0⟩ := by
      apply Fin.ext; simp only [tileSite, hmod0, show 0 < 3 * (d / 2) by omega, ↓reduceDIte]
    have hn0 : tileName k d n hk4 hdk hd1 ⟨j.val * P + 0, hlt0⟩ = (fun _ => false) := by
      simp only [tileName, hmod0, show 0 < 3 * (d / 2) by omega, ↓reduceDIte]; rfl
    rw [hs0, hn0]
    have hrec := readBit_row_zero_recover k hk0 (x j) ⟨0, hk0⟩
    have hi1 : ix k hk0 (0 + 1) = ⟨1, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 1 < k)])
    have hi2 : ix k hk0 (0 + 2) = ⟨2, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 2 < k)])
    simpa [hi1, hi2] using hrec
  have hv2_x2 : (x2Wires j).foldr (fun w acc => xor (v2.getD w false) acc) false = x j ⟨2, by omega⟩ := by
    simp only [x2Wires, List.foldr_cons, List.foldr_nil, Bool.xor_false]
    have hP3 : 3 < P := by omega
    have hlt3 : j.val * P + 3 < n * P := by
      calc j.val * P + 3 < j.val * P + P := by omega
        _ = (j.val + 1) * P := by ring
        _ ≤ n * P := Nat.mul_le_mul_right P j.isLt
    rw [hv2_data 3 hP3, tileData_getD k d n hk4 hdk hd1 x j 3 hP3, hv2_R0 ⟨2, by omega⟩, hv2_nl.2]
    have hmod3 : (j.val * P + 3) % (d + (d + 1) / 2) = 3 := Nat.mul_add_mod_of_lt hP3
    have hs3 : tileSite k d n hdk hd1 ⟨j.val * P + 3, hlt3⟩ = ⟨2, by omega⟩ := by
      apply Fin.ext; simp only [tileSite, hmod3, show 3 < 3 * (d / 2) by omega, ↓reduceDIte]
    have hn3 : tileName k d n hk4 hdk hd1 ⟨j.val * P + 3, hlt3⟩ = (fun _ => false) := by
      simp only [tileName, hmod3, show 3 < 3 * (d / 2) by omega, ↓reduceDIte]; rfl
    rw [hs3, hn3]
    have hrec := readBit_row_zero_recover k hk0 (x j) ⟨2, by omega⟩
    have hi3 : ix k hk0 (2 + 1) = ⟨3, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 3 < k)])
    have hi4 : ix k hk0 (2 + 2) = ⟨4, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 4 < k)])
    simpa [hi3, hi4] using hrec
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
  have hv2_x1 : (x1Wires j).foldr (fun w acc => xor (v2.getD w false) acc) false = x j ⟨1, by omega⟩ := by
    simp only [x1Wires]
    rw [hfold_app, hfold_app, hv2_x0, hv2_x2]
    simp only [List.foldr_cons, List.foldr_nil, Bool.xor_false, hv2_R0]
    have hstep := wMix_rot1_eq k hk2 (x j) ⟨1, by omega⟩
    dsimp only at hstep
    have h1 : ix k hk0 (1 + 1) = ⟨2, by omega⟩ := Fin.ext (by simp [ix, Nat.mod_eq_of_lt (by omega : 2 < k)])
    have h2 : ix k hk0 (1 + k - 1) = ⟨0, hk0⟩ := Fin.ext (by simp [ix])
    rw [h1, h2] at hstep
    rw [hstep]
    cases x j ⟨0, hk0⟩ <;> cases x j ⟨1, by omega⟩ <;> cases x j ⟨2, by omega⟩ <;> rfl
  change (wiresFrom (st1a.1 ++ st1b.1 ++ nlGates ++ st3.1) data).getD (tap j i) false = x j i
  rw [wiresFrom_append, wiresFrom_append, wiresFrom_append]
  have hidx : k * j.val + i.val < outSpecs.length := by rw [hout_len]; nlinarith [j.isLt, i.isLt]
  have hev := appendSpecs_eval outSpecs v2 (by simpa [hv2_len] using hout_lt) (k * j.val + i.val) hidx
  rw [hv2_len] at hev
  rw [hev]
  have hspec_at : outSpecs[k * j.val + i.val] =
      (false, (if recAnchor0 i.val then x0Wires j else []) ++
              (if recAnchor1 i.val then x1Wires j else []) ++
              (recR0Indices k hk0 i.val).map (tapR0 j)) := by
    have h := flatMap_const_getElem n k
      (fun j => (List.finRange k).map (fun i =>
        (false, (if recAnchor0 i.val then x0Wires j else []) ++
                (if recAnchor1 i.val then x1Wires j else []) ++
                (recR0Indices k hk0 i.val).map (tapR0 j))))
      (fun _ => by simp) j i
    simpa [outSpecs] using h
  rw [hspec_at]
  rw [hfold_app, hfold_app]
  have h0 : (if recAnchor0 i.val then x0Wires j else []).foldr (fun w acc => xor (v2.getD w false) acc) false =
      if recAnchor0 i.val then x j ⟨0, hk0⟩ else false := by
    split_ifs <;> [exact hv2_x0; rfl]
  have h1 : (if recAnchor1 i.val then x1Wires j else []).foldr (fun w acc => xor (v2.getD w false) acc) false =
      if recAnchor1 i.val then x j ⟨1, by omega⟩ else false := by
    split_ifs <;> [exact hv2_x1; rfl]
  have hR : ((recR0Indices k hk0 i.val).map (tapR0 j)).foldr (fun w acc => xor (v2.getD w false) acc) false =
      (recR0Indices k hk0 i.val).foldr (fun r acc => xor (wMix k hk0 1 (wRot k hk0 1 (x j)) r) acc) false := by
    induction recR0Indices k hk0 i.val with
    | nil => rfl
    | cons r rs ih => simp only [List.map_cons, List.foldr_cons, hv2_R0 r, ih]
  rw [h0, h1, hR]
  have hrec := rec_correct k hk2 (x j) i.val i.isLt
  have hassoc : ∀ a b c : Bool, xor (xor a b) c = xor a (xor b c) := by
    intro a b c; cases a <;> cases b <;> cases c <;> rfl
  rw [hassoc, hrec]

lemma main_proof :
    ∀ (k : ℕ) (hk : 0 < k),
      ∀ (n q : ℕ),
        (∃ (a : ℕ) (bank : Fin a → Bool) (key : Fin a → Fin n)
            (name : Fin a → Fin k → Bool) (site : Fin a → Fin k)
            (C : Circuit) (tap : Fin n → Fin k → ℕ),
          a ≤ q ∧ ValidCirc a C ∧ C.gates.countP isNonlin ≤ n * lossVal k ∧
          (∀ j i, tap j i < a + C.gates.length) ∧
          ∀ (x : Fin n → Fin k → Bool) (j : Fin n) (i : Fin k),
            let data := List.ofFn (fun l : Fin a => readBit k hk (bank l) (name l) (x (key l)) (site l))
            (C.wires data).getD (tap j i) false = x j i) ↔
          (n = 0 ∨ (k ≠ 1 ∧ k ≠ 3)) ∧ n * priceVal k ≤ q := by
  intro k hk n q
  constructor
  · intro h
    by_cases hn0 : n = 0
    · subst hn0; exact ⟨Or.inl rfl, by simp⟩
    · have hn : 0 < n := by omega
      have hk1 : k ≠ 1 := by
        intro hk1
        obtain ⟨a, bank, key, name, site, C, tap, _, hV, hNL, hTap, hDec⟩ := h
        exact lower_imposs_k13 k hk (Or.inl hk1) n hn ⟨a, bank, key, name, site, C, tap, hV, hNL, hTap, hDec⟩
      have hk3 : k ≠ 3 := by
        intro hk3
        obtain ⟨a, bank, key, name, site, C, tap, _, hV, hNL, hTap, hDec⟩ := h
        exact lower_imposs_k13 k hk (Or.inr hk3) n hn ⟨a, bank, key, name, site, C, tap, hV, hNL, hTap, hDec⟩
      exact ⟨Or.inr ⟨hk1, hk3⟩, lower_bound k hk hk1 hk3 n q h⟩
  · rintro ⟨hnk, hq⟩
    by_cases hn0 : n = 0
    · subst hn0; exact upper_n0 k hk q
    · have hne13 : k ≠ 1 ∧ k ≠ 3 := hnk.resolve_left hn0
      by_cases hk2 : k = 2
      · subst hk2; exact upper_k2 n q hq
      · have hk4 : 4 ≤ k := by omega
        by_cases h3 : 3 ∣ k
        · by_cases hk6 : k = 6
          · subst hk6; exact upper_k6 n q hq
          · have hk9 : 9 ≤ k := by omega
            exact upper_ge9_div3 k hk9 h3 n q hq
        · exact upper_ge4_ndiv3 k hk4 h3 n q hq

end PEqualNP.Outside.L_meta_42703_aux

theorem PEqualNP.Outside.L_meta_42703 : (
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
  ∀ (n q : Nat),
    let d := k-loss
    let price := if k = 6 then 7 else d + (d+1)/2
    (∃ (a : Nat) (bank : Fin a → Bool) (key : Fin a → Fin n)
        (name : Fin a → W) (site : Fin a → Fin k)
        (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Fin k → Nat),
      a ≤ q ∧ valid a C ∧ C.gates.countP nonlinear ≤ n*loss ∧
      (∀ j i, tap j i < a+C.gates.length) ∧
      ∀ (x : Fin n → W) (j : Fin n) (i : Fin k),
        let data := List.ofFn (fun l : Fin a => readBit (bank l) (name l) (x (key l)) (site l))
        (C.wires data).getD (tap j i) false = x j i) ↔
      (n = 0 ∨ (k ≠ 1 ∧ k ≠ 3)) ∧ n*price ≤ q) :=
  PEqualNP.Outside.L_meta_42703_aux.main_proof
