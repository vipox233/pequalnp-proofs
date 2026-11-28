import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1281_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section CircuitBasics

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_ge_length {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : l.length ≤ i) :
    l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_take {α : Type*} (l : List α) (m k : ℕ) (d : α) (hk : k < m) :
    (l.take m).getD k d = l.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk]

lemma getD_drop {α : Type*} (l : List α) (m k : ℕ) (d : α) :
    (l.drop m).getD k d = l.getD (m + k) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_mem {α : Type*} (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

lemma list_any_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a tl ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma notCount_le_length (gs : List Gate) (o : ℕ) :
    notCount ⟨gs, o⟩ ≤ gs.length :=
  List.length_filter_le _ _

def nonNot (gs : List Gate) : ℕ := gs.length - notCount ⟨gs, 0⟩

lemma nonNot_nil : nonNot [] = 0 := rfl

lemma nonNot_append (gs1 gs2 : List Gate) :
    nonNot (gs1 ++ gs2) = nonNot gs1 + nonNot gs2 := by
  dsimp only [nonNot]
  rw [List.length_append, notCount_append]
  have h1 := notCount_le_length gs1 0
  have h2 := notCount_le_length gs2 0
  omega

lemma notCount_singleton_and (ins : List ℕ) : notCount ⟨[⟨GateOp.and, ins⟩], 0⟩ = 0 := by
  simp [notCount]

lemma notCount_singleton_or (ins : List ℕ) : notCount ⟨[⟨GateOp.or, ins⟩], 0⟩ = 0 := by
  simp [notCount]

lemma notCount_singleton_not (ins : List ℕ) : notCount ⟨[⟨GateOp.not, ins⟩], 0⟩ = 1 := by
  simp [notCount]

lemma nonNot_singleton_and (ins : List ℕ) : nonNot [⟨GateOp.and, ins⟩] = 1 := by
  simp [nonNot, notCount_singleton_and]

lemma nonNot_singleton_or (ins : List ℕ) : nonNot [⟨GateOp.or, ins⟩] = 1 := by
  simp [nonNot, notCount_singleton_or]

lemma nonNot_singleton_not (ins : List ℕ) : nonNot [⟨GateOp.not, ins⟩] = 0 := by
  simp [nonNot, notCount_singleton_not]

lemma fanInTwo_nil (o : ℕ) : FanInTwo ⟨[], o⟩ := by
  intro g hg; cases hg

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma readsBack_nil (m o : ℕ) : ReadsBack m ⟨[], o⟩ := by
  intro j hj; cases hj

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

def inpVec {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length {n : ℕ} (x : Finset (Fin n)) : (inpVec x).length = n + 2 := by
  simp [inpVec]

lemma inpVec_getD_fin {n : ℕ} (x : Finset (Fin n)) (i : Fin n) :
    (inpVec x).getD i.val false = decide (i ∈ x) := by
  dsimp only [inpVec]
  rw [getD_append_left _ _ i.val false (by simp [i.isLt])]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma inpVec_getD_false {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD n false = false := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ n false (by simp)]
  simp

lemma inpVec_getD_true {n : ℕ} (x : Finset (Fin n)) :
    (inpVec x).getD (n + 1) false = true := by
  dsimp only [inpVec]
  rw [getD_append_right _ _ (n + 1) false (by simp)]
  have hsub : n + 1 - n = 1 := by omega
  simp [hsub]

lemma bool_le_iff (a b : Bool) : a ≤ b ↔ (a = true → b = true) := by
  cases a <;> cases b <;> decide

lemma not_true_le_false (h : (true : Bool) ≤ false) : False := by
  have := (bool_le_iff true false).mp h rfl
  cases this

lemma inpVec_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) (k : ℕ) :
    (inpVec u).getD k false ≤ (inpVec v).getD k false := by
  by_cases hk1 : k < n
  · have hu := inpVec_getD_fin u ⟨k, hk1⟩
    have hv := inpVec_getD_fin v ⟨k, hk1⟩
    dsimp only at hu hv
    rw [hu, hv, bool_le_iff]
    intro h
    exact decide_eq_true (huv (of_decide_eq_true h))
  · by_cases hk2 : k = n
    · subst hk2; rw [inpVec_getD_false, inpVec_getD_false]
    · by_cases hk3 : k = n + 1
      · subst hk3; rw [inpVec_getD_true, inpVec_getD_true]
      · rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]
        rw [getD_ge_length _ k false (by rw [inpVec_length]; omega)]

lemma all_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).all id ≤ (l.map g).all id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).all id <;> cases h2 : (tl.map g).all id <;> simp_all

lemma any_map_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (l.map f).any id ≤ (l.map g).any id := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    have ha := h a (List.mem_cons_self ..)
    have htl := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    cases hfa : f a <;> cases hga : g a <;>
      cases h1 : (tl.map f).any id <;> cases h2 : (tl.map g).any id <;> simp_all

lemma not_headD_anti (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i ≤ g i) :
    (!((l.map g).headD false)) ≤ (!((l.map f).headD false)) := by
  cases l with
  | nil => simp
  | cons a tl =>
    simp only [List.map_cons, List.headD_cons]
    have ha := h a (List.mem_cons_self ..)
    cases hfa : f a <;> cases hga : g a <;> simp_all

end CircuitBasics

section LowerBound

def evalNotCode : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w =>
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    let rest := evalNotCode gs (w ++ [v])
    match g.op with
    | GateOp.not => (if v then 2 ^ (notCount ⟨gs, 0⟩) else 0) + rest
    | _ => rest

lemma evalNotCode_lt (gs : List Gate) (w : List Bool) :
    evalNotCode gs w < 2 ^ (notCount ⟨gs, 0⟩) := by
  induction gs generalizing w with
  | nil => simp [evalNotCode, notCount]
  | cons g gs ih =>
    dsimp only [evalNotCode]
    cases hg : g.op with
    | not =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ + 1 := by simp [notCount, hg]
      rw [hnc, pow_succ]
      cases hv : GateOp.not.eval (g.inputs.map fun i => w.getD i false) with
      | false =>
        have hrest := ih (w ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        omega
      | true =>
        have hrest := ih (w ++ [true])
        simp only [↓reduceIte]
        omega
    | and =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | or =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | mod k =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _
    | maj =>
      have hnc : notCount ⟨g :: gs, 0⟩ = notCount ⟨gs, 0⟩ := by simp [notCount, hg]
      rw [hnc]; exact ih _

lemma append_singleton_getD_mono (w1 w2 : List Bool) (v1 v2 : Bool)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false ≤ w2.getD i false)
    (hv : v1 ≤ v2) (i : ℕ) :
    (w1 ++ [v1]).getD i false ≤ (w2 ++ [v2]).getD i false := by
  by_cases hi : i < w1.length
  · rw [getD_append_left w1 [v1] i false hi]
    rw [getD_append_left w2 [v2] i false (by omega)]
    exact hw i
  · rw [getD_append_right w1 [v1] i false (by omega)]
    rw [getD_append_right w2 [v2] i false (by omega)]
    rw [hlen]
    by_cases h0 : i - w2.length = 0
    · rw [h0]; simpa using hv
    · rw [getD_ge_length [v1] _ false (by simp; omega)]
      rw [getD_ge_length [v2] _ false (by simp; omega)]

lemma evalNotCode_dichotomy (gs : List Gate) (w1 w2 : List Bool)
    (hfit : FanInTwo ⟨gs, 0⟩)
    (hlen : w1.length = w2.length)
    (hw : ∀ i, w1.getD i false ≤ w2.getD i false) :
    evalNotCode gs w2 < evalNotCode gs w1 ∨
    (evalNotCode gs w2 = evalNotCode gs w1 ∧
      ∀ i, (wiresFrom gs w1).getD i false ≤ (wiresFrom gs w2).getD i false) := by
  induction gs generalizing w1 w2 with
  | nil => exact Or.inr ⟨rfl, hw⟩
  | cons g gs ih =>
    have hgfit := hfit g (List.mem_cons_self ..)
    have hgsfit : FanInTwo ⟨gs, 0⟩ := fun g' hg' => hfit g' (List.mem_cons_of_mem _ hg')
    dsimp only [evalNotCode, wiresFrom_cons]
    rcases hgfit.1 with h_and | h_or | h_not
    · rw [h_and]
      have hv : GateOp.and.eval (g.inputs.map fun i => w1.getD i false) ≤
          GateOp.and.eval (g.inputs.map fun i => w2.getD i false) :=
        all_map_mono g.inputs _ _ (fun i _ => hw i)
      exact ih _ _ hgsfit (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [h_or]
      have hv : GateOp.or.eval (g.inputs.map fun i => w1.getD i false) ≤
          GateOp.or.eval (g.inputs.map fun i => w2.getD i false) :=
        any_map_mono g.inputs _ _ (fun i _ => hw i)
      exact ih _ _ hgsfit (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [h_not]
      set v1 := GateOp.not.eval (g.inputs.map fun i => w1.getD i false)
      set v2 := GateOp.not.eval (g.inputs.map fun i => w2.getD i false)
      have hvanti : v2 ≤ v1 := not_headD_anti g.inputs _ _ (fun i _ => hw i)
      cases hv1 : v1 <;> cases hv2 : v2
      · have hw' := append_singleton_getD_mono w1 w2 false false hlen hw (le_refl false)
        rcases ih (w1 ++ [false]) (w2 ++ [false]) hgsfit (by simp [hlen]) hw' with hlt | ⟨heq, hle⟩
        · left; simpa using hlt
        · right; exact ⟨by simpa using heq, hle⟩
      · rw [hv1, hv2] at hvanti
        exact absurd hvanti not_true_le_false
      · left
        have hlt2 := evalNotCode_lt gs (w2 ++ [false])
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        omega
      · have hw' := append_singleton_getD_mono w1 w2 true true hlen hw (le_refl true)
        rcases ih (w1 ++ [true]) (w2 ++ [true]) hgsfit (by simp [hlen]) hw' with hlt | ⟨heq, hle⟩
        · left; simp only [↓reduceIte]; omega
        · right; exact ⟨by simp only [↓reduceIte, heq], hle⟩

end LowerBound

section Builder

def Extends (base : ℕ) (gs1 gs2 : List Gate) : Prop :=
  ∃ extra : List Gate, gs2 = gs1 ++ extra ∧ FanInTwo ⟨extra, 0⟩ ∧
    ReadsBack (base + gs1.length) ⟨extra, 0⟩

lemma Extends.refl (base : ℕ) (gs : List Gate) : Extends base gs gs :=
  ⟨[], by simp, fanInTwo_nil 0, readsBack_nil _ 0⟩

lemma Extends.trans {base : ℕ} {gs1 gs2 gs3 : List Gate}
    (h1 : Extends base gs1 gs2) (h2 : Extends base gs2 gs3) :
    Extends base gs1 gs3 := by
  rcases h1 with ⟨e1, rfl, hf1, hr1⟩
  rcases h2 with ⟨e2, rfl, hf2, hr2⟩
  refine ⟨e1 ++ e2, by rw [List.append_assoc], fanInTwo_append hf1 hf2, ?_⟩
  have hr2' : ReadsBack ((base + gs1.length) + e1.length) ⟨e2, 0⟩ := by
    simpa [List.length_append, Nat.add_assoc] using hr2
  exact readsBack_append hr1 hr2'

lemma Extends.length_le {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl, _, _⟩; simp

lemma Extends.wire_eq {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2)
    (w : List Bool) (hw : w.length = base) (i : ℕ) (hi : i < base + gs1.length) :
    (wiresFrom gs2 w).getD i false = (wiresFrom gs1 w).getD i false := by
  rcases h with ⟨e, rfl, _, _⟩
  rw [wiresFrom_append]
  exact wiresFrom_getD_lt e (wiresFrom gs1 w) i (by rw [wiresFrom_length, hw]; exact hi)

def emitAnd (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], base + gs.length)

def emitOr (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], base + gs.length)

def emitNot (base : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], base + gs.length)

lemma emitAnd_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitAnd base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [emitAnd]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.and, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append, notCount_singleton_and, add_zero]
  · rw [nonNot_append, nonNot_singleton_and]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitOr base gs a b
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) := by
  dsimp only [emitOr]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.or, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append, notCount_singleton_or, add_zero]
  · rw [nonNot_append, nonNot_singleton_or]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitNot_spec (base : ℕ) (gs : List Gate) (a : ℕ)
    (ha : a < base + gs.length) :
    let r := emitNot base gs a
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧
    nonNot r.1 = nonNot gs ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false = !((wiresFrom gs w).getD a false) := by
  dsimp only [emitNot]
  refine ⟨?_, by simp, ?_, ?_, ?_⟩
  · refine ⟨[⟨GateOp.not, [a]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_singleton] at hi
      subst hi; omega
  · rw [notCount_append, notCount_singleton_not]
  · rw [nonNot_append, nonNot_singleton_not, add_zero]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

def buildMerged (base notM : ℕ) : List Gate → List ℕ → List ℕ → List Gate × List ℕ
  | gs, [], _ => (gs, [])
  | gs, a :: as, [] =>
    let r := emitAnd base gs a notM
    let rest := buildMerged base notM r.1 as []
    (rest.1, r.2 :: rest.2)
  | gs, a :: as, b :: bs =>
    let r1 := emitAnd base gs a notM
    let r2 := emitOr base r1.1 r1.2 b
    let rest := buildMerged base notM r2.1 as bs
    (rest.1, r2.2 :: rest.2)

lemma buildMerged_spec (base notM : ℕ) (leftW rightW : List ℕ) (gs : List Gate)
    (hnotM : notM < base + gs.length)
    (hL : ∀ i ∈ leftW, i < base + gs.length)
    (hR : ∀ i ∈ rightW, i < base + gs.length)
    (hlen : rightW.length ≤ leftW.length) :
    let r := buildMerged base notM gs leftW rightW
    Extends base gs r.1 ∧
    r.2.length = leftW.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + leftW.length + rightW.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < leftW.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          if t < rightW.length then
            ((wiresFrom gs w).getD (leftW.getD t 0) false && (wiresFrom gs w).getD notM false) ||
              (wiresFrom gs w).getD (rightW.getD t 0) false
          else
            (wiresFrom gs w).getD (leftW.getD t 0) false && (wiresFrom gs w).getD notM false := by
  induction leftW generalizing rightW gs with
  | nil =>
    dsimp only [buildMerged]
    have hrnil : rightW = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hlen)
    subst hrnil
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons a as ih =>
    have ha : a < base + gs.length := hL a (List.mem_cons_self ..)
    have has : ∀ i ∈ as, i < base + gs.length := fun i hi => hL i (List.mem_cons_of_mem _ hi)
    cases rightW with
    | nil =>
      dsimp only [buildMerged]
      set r1 := emitAnd base gs a notM with hr1
      have h1 := emitAnd_spec base gs a notM ha hnotM
      rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
      have hgl1 := hext1.length_le
      set rest := buildMerged base notM r1.1 as [] with hrest
      have h2 := ih [] r1.1 (by omega) (fun i hi => lt_of_lt_of_le (has i hi) (by omega))
        (fun _ h => by cases h) (by simp)
      rw [← hrest] at h2
      rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega,
        by simp only [List.length_cons, List.length_nil] at hnn2 ⊢; omega, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · omega
        · exact hlt2 i hi
      · intro w hw t ht
        cases t with
        | zero =>
          change (wiresFrom rest.1 w).getD r1.2 false = _
          simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
          rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
        | succ t' =>
          have ht' : t' < as.length := by simp at ht; omega
          change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
          simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte]
          have hv := hval2 w hw t' ht'
          simp only [List.length_nil, Nat.not_lt_zero, ↓reduceIte] at hv
          rw [hv, hext1.wire_eq w hw _ (has _ (getD_mem as t' 0 ht')), hext1.wire_eq w hw notM hnotM]; rfl
    | cons b bs =>
      dsimp only [buildMerged]
      have hb : b < base + gs.length := hR b (List.mem_cons_self ..)
      have hbs : ∀ i ∈ bs, i < base + gs.length := fun i hi => hR i (List.mem_cons_of_mem _ hi)
      set r1 := emitAnd base gs a notM with hr1
      have h1 := emitAnd_spec base gs a notM ha hnotM
      rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
      have hgl1 := hext1.length_le
      set r2 := emitOr base r1.1 r1.2 b with hr2
      have h2 := emitOr_spec base r1.1 r1.2 b hlt1 (by omega)
      rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      have hext12 := hext1.trans hext2
      set rest := buildMerged base notM r2.1 as bs with hrest
      have h3 := ih bs r2.1 (by omega) (fun i hi => lt_of_lt_of_le (has i hi) (by omega))
        (fun i hi => lt_of_lt_of_le (hbs i hi) (by omega)) (by simp at hlen; omega)
      rw [← hrest] at h3
      rcases h3 with ⟨hext3, hlen3, hlt3, hnc3, hnn3, hval3⟩
      have hgl3 := hext3.length_le
      refine ⟨hext12.trans hext3, by simp [hlen3], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · omega
        · exact hlt3 i hi
      · intro w hw t ht
        cases t with
        | zero =>
          change (wiresFrom rest.1 w).getD r2.2 false = _
          simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte]
          rw [hext3.wire_eq w hw _ hlt2, hval2 w hw, hval1 w hw, hext1.wire_eq w hw b hb]; rfl
        | succ t' =>
          have ht' : t' < as.length := by simp at ht; omega
          change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
          simp only [List.length_cons, Nat.add_lt_add_iff_right]
          rw [hval3 w hw t' ht']
          split_ifs with hrt
          · rw [hext12.wire_eq w hw _ (has _ (getD_mem as t' 0 ht')),
                hext12.wire_eq w hw notM hnotM,
                hext12.wire_eq w hw _ (hbs _ (getD_mem bs t' 0 hrt))]; rfl
          · rw [hext12.wire_eq w hw _ (has _ (getD_mem as t' 0 ht')),
                hext12.wire_eq w hw notM hnotM]; rfl

def mapAndWith (base c : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, z :: zs =>
    let r := emitAnd base gs c z
    let rest := mapAndWith base c r.1 zs
    (rest.1, r.2 :: rest.2)

lemma mapAndWith_spec (base c : ℕ) (zs : List ℕ) (gs : List Gate)
    (hc : c < base + gs.length) (hzs : ∀ i ∈ zs, i < base + gs.length) :
    let r := mapAndWith base c gs zs
    Extends base gs r.1 ∧
    r.2.length = zs.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + zs.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < zs.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          ((wiresFrom gs w).getD c false && (wiresFrom gs w).getD (zs.getD t 0) false) := by
  induction zs generalizing gs with
  | nil =>
    dsimp only [mapAndWith]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons z zs ih =>
    dsimp only [mapAndWith]
    have hz : z < base + gs.length := hzs z (List.mem_cons_self ..)
    have hzs' : ∀ i ∈ zs, i < base + gs.length := fun i hi => hzs i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs c z with hr1
    have h1 := emitAnd_spec base gs c z hc hz
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set rest := mapAndWith base c r1.1 zs with hrest
    have h2 := ih r1.1 (by omega) (fun i hi => lt_of_lt_of_le (hzs' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro w hw t ht
      cases t with
      | zero =>
        change (wiresFrom rest.1 w).getD r1.2 false = _
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
      | succ t' =>
        have ht' : t' < zs.length := by simp at ht; omega
        change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
        rw [hval2 w hw t' ht', hext1.wire_eq w hw c hc,
            hext1.wire_eq w hw _ (hzs' _ (getD_mem zs t' 0 ht'))]; rfl

def mapOrWith (base c : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, z :: zs =>
    let r := emitOr base gs c z
    let rest := mapOrWith base c r.1 zs
    (rest.1, r.2 :: rest.2)

lemma mapOrWith_spec (base c : ℕ) (zs : List ℕ) (gs : List Gate)
    (hc : c < base + gs.length) (hzs : ∀ i ∈ zs, i < base + gs.length) :
    let r := mapOrWith base c gs zs
    Extends base gs r.1 ∧
    r.2.length = zs.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + zs.length ∧
    ∀ (w : List Bool), w.length = base →
      ∀ (t : ℕ), t < zs.length →
        (wiresFrom r.1 w).getD (r.2.getD t 0) false =
          ((wiresFrom gs w).getD c false || (wiresFrom gs w).getD (zs.getD t 0) false) := by
  induction zs generalizing gs with
  | nil =>
    dsimp only [mapOrWith]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp, (fun _ _ t ht => by simp at ht)⟩
  | cons z zs ih =>
    dsimp only [mapOrWith]
    have hz : z < base + gs.length := hzs z (List.mem_cons_self ..)
    have hzs' : ∀ i ∈ zs, i < base + gs.length := fun i hi => hzs i (List.mem_cons_of_mem _ hi)
    set r1 := emitOr base gs c z with hr1
    have h1 := emitOr_spec base gs c z hc hz
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set rest := mapOrWith base c r1.1 zs with hrest
    have h2 := ih r1.1 (by omega) (fun i hi => lt_of_lt_of_le (hzs' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro w hw t ht
      cases t with
      | zero =>
        change (wiresFrom rest.1 w).getD r1.2 false = _
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]; rfl
      | succ t' =>
        have ht' : t' < zs.length := by simp at ht; omega
        change (wiresFrom rest.1 w).getD (rest.2.getD t' 0) false = _
        rw [hval2 w hw t' ht', hext1.wire_eq w hw c hc,
            hext1.wire_eq w hw _ (hzs' _ (getD_mem zs t' 0 ht'))]; rfl

def chainInv (base : ℕ) : ℕ → List Gate → List ℕ → List Gate × List ℕ
  | 0, gs, _ => (gs, [])
  | r + 1, gs, ys =>
    if ys.length = 0 then (gs, [])
    else
      let q := ys.length / 2
      let leftW := ys.take q
      let mWire := ys.getD q 0
      let rightW := ys.drop (q + 1)
      let rNot := emitNot base gs mWire
      let notM := rNot.2
      let rMerge := buildMerged base notM rNot.1 leftW rightW
      let rRec := chainInv base r rMerge.1 rMerge.2
      let rLeft := mapAndWith base notM rRec.1 rRec.2
      let rRight := mapOrWith base notM rLeft.1 (rRec.2.take rightW.length)
      (rRight.1, rLeft.2 ++ [notM] ++ rRight.2)

lemma chainInv_spec (base : ℕ) :
    ∀ (r : ℕ) (gs : List Gate) (ys : List ℕ),
      ys.length < 2 ^ r →
      (∀ i ∈ ys, i < base + gs.length) →
      let res := chainInv base r gs ys
      Extends base gs res.1 ∧
      res.2.length = ys.length ∧
      (∀ i ∈ res.2, i < base + res.1.length) ∧
      notCount ⟨res.1, 0⟩ ≤ notCount ⟨gs, 0⟩ + r ∧
      nonNot res.1 ≤ nonNot gs + 4 * ys.length ∧
      ∀ (w : List Bool), w.length = base →
        (∀ (i j : ℕ), i < ys.length → j < ys.length → i ≤ j →
          (wiresFrom gs w).getD (ys.getD j 0) false ≤ (wiresFrom gs w).getD (ys.getD i 0) false) →
        ∀ (k : ℕ), k < ys.length →
          (wiresFrom res.1 w).getD (res.2.getD k 0) false =
            !((wiresFrom gs w).getD (ys.getD k 0) false) := by
  intro r
  induction r with
  | zero =>
    intro gs ys hlen _
    dsimp only [chainInv]
    have hnil : ys = [] := List.eq_nil_of_length_eq_zero (by simp only [pow_zero] at hlen; omega)
    subst hnil
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), by omega, by simp,
      (fun _ _ _ k hk => by simp at hk)⟩
  | succ r ih =>
    intro gs ys hlen hys
    dsimp only [chainInv]
    split_ifs with h0
    · have hnil : ys = [] := List.eq_nil_of_length_eq_zero h0
      subst hnil
      dsimp only
      refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), by omega, by simp,
        (fun _ _ _ k hk => by simp at hk)⟩
    · set q := ys.length / 2 with hq_def
      set leftW := ys.take q with hleftW_def
      set mWire := ys.getD q 0 with hmWire_def
      set rightW := ys.drop (q + 1) with hrightW_def
      have hq_lt : q < ys.length := by omega
      have hL_len : leftW.length = q := by rw [hleftW_def, List.length_take]; omega
      have hR_len : rightW.length = ys.length - (q + 1) := by rw [hrightW_def, List.length_drop]
      have hRL_le : rightW.length ≤ leftW.length := by omega
      have hm_lt : mWire < base + gs.length := hys _ (getD_mem ys q 0 hq_lt)
      have hL_lt : ∀ i ∈ leftW, i < base + gs.length := fun i hi => hys i (List.mem_of_mem_take hi)
      have hR_lt : ∀ i ∈ rightW, i < base + gs.length := fun i hi => hys i (List.mem_of_mem_drop hi)
      set rNot := emitNot base gs mWire with hrNot
      have hNot := emitNot_spec base gs mWire hm_lt
      rw [← hrNot] at hNot
      rcases hNot with ⟨hextN, hltN, hncN, hnnN, hvalN⟩
      have hglN := hextN.length_le
      set rMerge := buildMerged base rNot.2 rNot.1 leftW rightW with hrMerge
      have hMerge := buildMerged_spec base rNot.2 leftW rightW rNot.1 hltN
        (fun i hi => lt_of_lt_of_le (hL_lt i hi) (by omega))
        (fun i hi => lt_of_lt_of_le (hR_lt i hi) (by omega)) hRL_le
      rw [← hrMerge] at hMerge
      rcases hMerge with ⟨hextM, hlenM, hltM, hncM, hnnM, hvalM⟩
      have hglM := hextM.length_le
      have hq_pow : rMerge.2.length < 2 ^ r := by
        have hpow : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
        omega
      set rRec := chainInv base r rMerge.1 rMerge.2 with hrRec
      have hRec := ih rMerge.1 rMerge.2 hq_pow hltM
      rw [← hrRec] at hRec
      rcases hRec with ⟨hextR, hlenR, hltR, hncR, hnnR, hvalR⟩
      have hglR := hextR.length_le
      set rLeft := mapAndWith base rNot.2 rRec.1 rRec.2 with hrLeft
      have hnotM_R : rNot.2 < base + rRec.1.length := by omega
      have hLeft := mapAndWith_spec base rNot.2 rRec.2 rRec.1 hnotM_R hltR
      rw [← hrLeft] at hLeft
      rcases hLeft with ⟨hextL, hlenL, hltL, hncL, hnnL, hvalL⟩
      have hglL := hextL.length_le
      set rRight := mapOrWith base rNot.2 rLeft.1 (rRec.2.take rightW.length) with hrRight
      have hnotM_L : rNot.2 < base + rLeft.1.length := by omega
      have hTake_lt : ∀ i ∈ rRec.2.take rightW.length, i < base + rLeft.1.length := fun i hi =>
        lt_of_lt_of_le (hltR i (List.mem_of_mem_take hi)) (by omega)
      have hRight := mapOrWith_spec base rNot.2 (rRec.2.take rightW.length) rLeft.1 hnotM_L hTake_lt
      rw [← hrRight] at hRight
      rcases hRight with ⟨hextRi, hlenRi, hltRi, hncRi, hnnRi, hvalRi⟩
      have hglRi := hextRi.length_le
      have hTake_len : (rRec.2.take rightW.length).length = rightW.length := by
        rw [List.length_take]; omega
      have hext_all : Extends base gs rRight.1 :=
        (((hextN.trans hextM).trans hextR).trans hextL).trans hextRi
      have hlen_out : (rLeft.2 ++ [rNot.2] ++ rRight.2).length = ys.length := by
        simp only [List.length_append, List.length_singleton]; omega
      dsimp only
      refine ⟨hext_all, hlen_out, ?_, by omega, by omega, ?_⟩
      · intro i hi
        simp only [List.mem_append, List.mem_singleton] at hi
        rcases hi with (hi | rfl) | hi
        · exact lt_of_lt_of_le (hltL i hi) (by omega)
        · omega
        · exact hltRi i hi
      · intro w hw hdec k hk
        have hval_notM : (wiresFrom rNot.1 w).getD rNot.2 false =
            !((wiresFrom gs w).getD (ys.getD q 0) false) := hvalN w hw
        have hval_merge_eval : ∀ (t : ℕ), t < q →
            (wiresFrom rMerge.1 w).getD (rMerge.2.getD t 0) false =
              if (wiresFrom gs w).getD (ys.getD q 0) false = false then
                (wiresFrom gs w).getD (ys.getD t 0) false
              else
                if q + 1 + t < ys.length then
                  (wiresFrom gs w).getD (ys.getD (q + 1 + t) 0) false
                else false := by
          intro t ht
          have hvm := hvalM w hw t (by omega)
          rw [hvm, hval_notM]
          have hL_el : leftW.getD t 0 = ys.getD t 0 := getD_take ys q t 0 ht
          rw [hL_el, hextN.wire_eq w hw _ (hys _ (getD_mem ys t 0 (by omega)))]
          cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
          · simp only [Bool.not_false, Bool.and_true, ↓reduceIte]
            split_ifs with hrt
            · have hR_el : rightW.getD t 0 = ys.getD (q + 1 + t) 0 := getD_drop ys (q + 1) t 0
              rw [hR_el, hextN.wire_eq w hw _ (hys _ (getD_mem ys (q + 1 + t) 0 (by omega)))]
              have hle := hdec q (q + 1 + t) hq_lt (by omega) (by omega)
              rw [hmq] at hle
              have h0f : (wiresFrom gs w).getD (ys.getD (q + 1 + t) 0) false = false := by
                cases hv : (wiresFrom gs w).getD (ys.getD (q + 1 + t) 0) false
                · rfl
                · rw [hv] at hle; exact absurd hle not_true_le_false
              rw [h0f, Bool.or_false]
            · rfl
          · simp only [Bool.not_true, Bool.and_false, Bool.false_or, Bool.true_eq_false, ↓reduceIte]
            split_ifs with hrt1 hrt2
            · have hR_el : rightW.getD t 0 = ys.getD (q + 1 + t) 0 := getD_drop ys (q + 1) t 0
              rw [hR_el, hextN.wire_eq w hw _ (hys _ (getD_mem ys (q + 1 + t) 0 hrt2))]
            · omega
            · omega
            · rfl
        have hdec_merge : ∀ (i j : ℕ), i < rMerge.2.length → j < rMerge.2.length → i ≤ j →
            (wiresFrom rMerge.1 w).getD (rMerge.2.getD j 0) false ≤
              (wiresFrom rMerge.1 w).getD (rMerge.2.getD i 0) false := by
          intro i j hi hj hij
          rw [hval_merge_eval i (by omega), hval_merge_eval j (by omega)]
          cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
          · simp only [↓reduceIte]; exact hdec i j (by omega) (by omega) hij
          · simp only [Bool.true_eq_false, ↓reduceIte]
            split_ifs with h1 h2
            · exact hdec (q + 1 + i) (q + 1 + j) h2 h1 (by omega)
            · omega
            · exact Bool.false_le _
            · exact le_refl false
        have hval_rec := hvalR w hw hdec_merge
        have hextNR : Extends base rNot.1 rRec.1 := hextM.trans hextR
        have hextNL : Extends base rNot.1 rLeft.1 := hextNR.trans hextL
        have hextNRi : Extends base rNot.1 rRight.1 := hextNL.trans hextRi
        by_cases hk_lt : k < q
        · have hk1 : k < (rLeft.2 ++ [rNot.2]).length := by
            simp only [List.length_append, List.length_singleton]; omega
          have hget : (rLeft.2 ++ [rNot.2] ++ rRight.2).getD k 0 = rLeft.2.getD k 0 := by
            rw [getD_append_left _ _ k 0 hk1, getD_append_left _ _ k 0 (by omega)]
          rw [hget, hextRi.wire_eq w hw _ (hltL _ (getD_mem rLeft.2 k 0 (by omega))),
              hvalL w hw k (by omega), hextNR.wire_eq w hw rNot.2 hltN, hval_notM,
              hval_rec k (by omega), hval_merge_eval k hk_lt]
          cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
          · simp
          · have hle := hdec k q (by omega) hq_lt (by omega)
            rw [hmq] at hle
            have hkt : (wiresFrom gs w).getD (ys.getD k 0) false = true := by
              cases hv : (wiresFrom gs w).getD (ys.getD k 0) false
              · rw [hv] at hle; exact absurd hle not_true_le_false
              · rfl
            rw [hkt]; simp
        · by_cases hk_eq : k = q
          · rw [hk_eq]
            have hk1 : q < (rLeft.2 ++ [rNot.2]).length := by
              simp only [List.length_append, List.length_singleton]; omega
            have hget : (rLeft.2 ++ [rNot.2] ++ rRight.2).getD q 0 = rNot.2 := by
              rw [getD_append_left _ _ q 0 hk1, getD_append_right _ _ q 0 (by omega)]
              have hsub : q - rLeft.2.length = 0 := by omega
              rw [hsub]; rfl
            rw [hget, hextNRi.wire_eq w hw rNot.2 hltN, hval_notM]
          · set t := k - (q + 1)
            have ht_lt : t < rightW.length := by omega
            have hk_eq' : q + 1 + t = k := by omega
            have hlen_prefix : (rLeft.2 ++ [rNot.2]).length = q + 1 := by
              simp only [List.length_append, List.length_singleton]; omega
            have hget : (rLeft.2 ++ [rNot.2] ++ rRight.2).getD k 0 = rRight.2.getD t 0 := by
              rw [getD_append_right _ _ k 0 (by omega), hlen_prefix]
            rw [hget, hvalRi w hw t (by omega), hextNL.wire_eq w hw rNot.2 hltN, hval_notM,
                getD_take rRec.2 rightW.length t 0 ht_lt,
                hextL.wire_eq w hw _ (hltR _ (getD_mem rRec.2 t 0 (by omega))),
                hval_rec t (by omega), hval_merge_eval t (by omega)]
            cases hmq : (wiresFrom gs w).getD (ys.getD q 0) false
            · have hle := hdec q k hq_lt hk (by omega)
              rw [hmq] at hle
              have hkf : (wiresFrom gs w).getD (ys.getD k 0) false = false := by
                cases hv : (wiresFrom gs w).getD (ys.getD k 0) false
                · rfl
                · rw [hv] at hle; exact absurd hle not_true_le_false
              rw [hkf]; simp
            · simp only [Bool.not_true, Bool.false_or, Bool.true_eq_false, ↓reduceIte]
              rw [hk_eq', if_pos hk]

def emitAndList (base oneWire : ℕ) : List Gate → List ℕ → List Gate × ℕ
  | gs, [] => (gs, oneWire)
  | gs, w :: ws =>
    let r := emitAnd base gs oneWire w
    emitAndList base r.2 r.1 ws

lemma emitAndList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (oneWire : ℕ) (gs : List Gate),
      oneWire < base + gs.length →
      (∀ i ∈ ws, i < base + gs.length) →
      let r := emitAndList base oneWire gs ws
      Extends base gs r.1 ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + ws.length ∧
      ∀ (w : List Bool), w.length = base →
        (wiresFrom r.1 w).getD r.2 false =
          ((wiresFrom gs w).getD oneWire false && ws.all (fun i => (wiresFrom gs w).getD i false)) := by
  intro ws
  induction ws with
  | nil =>
    intro oneWire gs ho _
    dsimp only [emitAndList]
    refine ⟨Extends.refl base gs, ho, rfl, by omega, fun _ _ => by simp⟩
  | cons a ws ih =>
    intro oneWire gs ho hws
    dsimp only [emitAndList]
    have ha : a < base + gs.length := hws a (List.mem_cons_self ..)
    have hws' : ∀ i ∈ ws, i < base + gs.length := fun i hi => hws i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs oneWire a with hr1
    have h1 := emitAnd_spec base gs oneWire a ho ha
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    have h2 := ih r1.2 r1.1 hlt1 (fun i hi => lt_of_lt_of_le (hws' i hi) (by omega))
    rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    refine ⟨hext1.trans hext2, hlt2, by omega, by simp only [List.length_cons]; omega, ?_⟩
    intro w hw
    rw [hval2 w hw, hval1 w hw]
    simp only [List.all_cons]
    have hcongr_aux : ∀ ws' : List ℕ, (∀ i ∈ ws', i < base + gs.length) →
        ws'.all (fun i => (wiresFrom r1.1 w).getD i false) =
        ws'.all (fun i => (wiresFrom gs w).getD i false) := by
      intro ws'
      induction ws' with
      | nil => intro _; rfl
      | cons b bs ihb =>
        intro hbs
        simp only [List.all_cons]
        rw [hext1.wire_eq w hw b (hbs b (List.mem_cons_self ..))]
        congr 1
        exact ihb (fun i hi => hbs i (List.mem_cons_of_mem _ hi))
    rw [hcongr_aux ws hws', Bool.and_assoc]

def emitOrList (base zeroWire : ℕ) : List Gate → List ℕ → List Gate × ℕ
  | gs, [] => (gs, zeroWire)
  | gs, w :: ws =>
    let r := emitOr base gs zeroWire w
    emitOrList base r.2 r.1 ws

lemma emitOrList_spec (base : ℕ) :
    ∀ (ws : List ℕ) (zeroWire : ℕ) (gs : List Gate),
      zeroWire < base + gs.length →
      (∀ i ∈ ws, i < base + gs.length) →
      let r := emitOrList base zeroWire gs ws
      Extends base gs r.1 ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + ws.length ∧
      ∀ (w : List Bool), w.length = base →
        (wiresFrom r.1 w).getD r.2 false =
          ((wiresFrom gs w).getD zeroWire false || ws.any (fun i => (wiresFrom gs w).getD i false)) := by
  intro ws
  induction ws with
  | nil =>
    intro zeroWire gs hz _
    dsimp only [emitOrList]
    refine ⟨Extends.refl base gs, hz, rfl, by omega, fun _ _ => by simp⟩
  | cons a ws ih =>
    intro zeroWire gs hz hws
    dsimp only [emitOrList]
    have ha : a < base + gs.length := hws a (List.mem_cons_self ..)
    have hws' : ∀ i ∈ ws, i < base + gs.length := fun i hi => hws i (List.mem_cons_of_mem _ hi)
    set r1 := emitOr base gs zeroWire a with hr1
    have h1 := emitOr_spec base gs zeroWire a hz ha
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    have h2 := ih r1.2 r1.1 hlt1 (fun i hi => lt_of_lt_of_le (hws' i hi) (by omega))
    rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    refine ⟨hext1.trans hext2, hlt2, by omega, by simp only [List.length_cons]; omega, ?_⟩
    intro w hw
    rw [hval2 w hw, hval1 w hw]
    simp only [List.any_cons]
    have hcongr : ws.any (fun i => (wiresFrom r1.1 w).getD i false) =
        ws.any (fun i => (wiresFrom gs w).getD i false) := by
      apply list_any_congr
      intro i hi
      exact hext1.wire_eq w hw i (hws' i hi)
    rw [hcongr, Bool.or_assoc]

def padNots (base zeroWire : ℕ) : List Gate → ℕ → List Gate
  | gs, 0 => gs
  | gs, k + 1 =>
    let r := emitNot base gs zeroWire
    padNots base zeroWire r.1 k

lemma padNots_spec (base zeroWire : ℕ) (hz : zeroWire < base) :
    ∀ (k : ℕ) (gs : List Gate),
      Extends base gs (padNots base zeroWire gs k) ∧
      notCount ⟨padNots base zeroWire gs k, 0⟩ = notCount ⟨gs, 0⟩ + k ∧
      nonNot (padNots base zeroWire gs k) = nonNot gs := by
  intro k
  induction k with
  | zero => intro gs; exact ⟨Extends.refl base gs, by simp [padNots], rfl⟩
  | succ k ih =>
    intro gs
    dsimp only [padNots]
    have h1 := emitNot_spec base gs zeroWire (by omega)
    rcases h1 with ⟨hext1, _, hnc1, hnn1, _⟩
    have h2 := ih (emitNot base gs zeroWire).1
    exact ⟨hext1.trans h2.1, by omega, by omega⟩

end Builder

section PairEval

def bits (l : ℕ) (x : Finset (Fin l)) : List Bool :=
  List.ofFn (fun i : Fin l => decide (i ∈ x))

def pairVec (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) : List Bool :=
  bits n x ++ bits m z ++ [false, true]

lemma pairVec_length (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairVec n m x z).length = n + m + 2 := by
  simp [pairVec, bits]; omega

lemma pairVec_getD_left (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) (i : Fin n) :
    (pairVec n m x z).getD i.val false = decide (i ∈ x) := by
  dsimp only [pairVec, bits]
  rw [getD_append_left _ _ i.val false (by simp; omega)]
  rw [getD_append_left _ _ i.val false (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma pairVec_getD_right (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) (j : Fin m) :
    (pairVec n m x z).getD (n + j.val) false = decide (j ∈ z) := by
  dsimp only [pairVec, bits]
  rw [getD_append_left _ _ (n + j.val) false (by simp)]
  rw [getD_append_right _ _ (n + j.val) false (by simp)]
  have hlen : (List.ofFn fun i : Fin n => decide (i ∈ x)).length = n := by simp
  rw [hlen, Nat.add_sub_cancel_left]
  simp [List.getD_eq_getElem?_getD, j.isLt]

lemma pairVec_getD_false (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairVec n m x z).getD (n + m) false = false := by
  dsimp only [pairVec, bits]
  rw [getD_append_right _ _ (n + m) false (by simp)]
  have hlen : (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++
      List.ofFn (fun i : Fin m => decide (i ∈ z))).length = n + m := by simp
  rw [hlen, Nat.sub_self]
  rfl

lemma pairVec_getD_true (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairVec n m x z).getD (n + m + 1) false = true := by
  dsimp only [pairVec, bits]
  rw [getD_append_right _ _ (n + m + 1) false (by simp)]
  have hlen : (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++
      List.ofFn (fun i : Fin m => decide (i ∈ z))).length = n + m := by simp
  rw [hlen, show n + m + 1 - (n + m) = 1 by omega]
  rfl

lemma pairVec_mono {n m : ℕ} {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)}
    (hx : x1 ⊆ x2) (hz : z1 ⊆ z2) (k : ℕ) :
    (pairVec n m x1 z1).getD k false ≤ (pairVec n m x2 z2).getD k false := by
  by_cases h1 : k < n
  · have a := pairVec_getD_left n m x1 z1 ⟨k, h1⟩
    have b := pairVec_getD_left n m x2 z2 ⟨k, h1⟩
    dsimp only at a b
    rw [a, b, bool_le_iff]
    intro h; exact decide_eq_true (hx (of_decide_eq_true h))
  · by_cases h2 : k < n + m
    · have hk' : k - n < m := by omega
      have hkeq : n + (k - n) = k := by omega
      have a := pairVec_getD_right n m x1 z1 ⟨k - n, hk'⟩
      have b := pairVec_getD_right n m x2 z2 ⟨k - n, hk'⟩
      dsimp only at a b
      rw [hkeq] at a b
      rw [a, b, bool_le_iff]
      intro h; exact decide_eq_true (hz (of_decide_eq_true h))
    · by_cases h3 : k = n + m
      · subst h3; rw [pairVec_getD_false, pairVec_getD_false]
      · by_cases h4 : k = n + m + 1
        · subst h4; rw [pairVec_getD_true, pairVec_getD_true]
        · rw [getD_ge_length _ k false (by rw [pairVec_length]; omega)]
          rw [getD_ge_length _ k false (by rw [pairVec_length]; omega)]

lemma wiresFrom_mono (gs : List Gate) (hmono : Monotone2 ⟨gs, 0⟩) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length) (hw : ∀ i, w1.getD i false ≤ w2.getD i false) (i : ℕ) :
    (wiresFrom gs w1).getD i false ≤ (wiresFrom gs w2).getD i false := by
  induction gs generalizing w1 w2 with
  | nil => exact hw i
  | cons g gs ih =>
    have hg := hmono g (List.mem_cons_self ..)
    have hgs : Monotone2 ⟨gs, 0⟩ := fun g' hg' => hmono g' (List.mem_cons_of_mem _ hg')
    rcases hg.1 with h_and | h_or
    · rw [wiresFrom_cons, wiresFrom_cons]
      have hv : g.op.eval (g.inputs.map fun k => w1.getD k false) ≤
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        rw [h_and]
        exact all_map_mono g.inputs _ _ (fun k _ => hw k)
      exact ih hgs _ _ (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)
    · rw [wiresFrom_cons, wiresFrom_cons]
      have hv : g.op.eval (g.inputs.map fun k => w1.getD k false) ≤
          g.op.eval (g.inputs.map fun k => w2.getD k false) := by
        rw [h_or]
        exact any_map_mono g.inputs _ _ (fun k _ => hw k)
      exact ih hgs _ _ (by simp [hlen]) (append_singleton_getD_mono w1 w2 _ _ hlen hw hv)

lemma notCount_cons (g : Gate) (gs : List Gate) :
    notCount ⟨g :: gs, 0⟩ = notCount ⟨[g], 0⟩ + notCount ⟨gs, 0⟩ := by
  have heq : g :: gs = [g] ++ gs := rfl
  rw [heq, notCount_append]

lemma notCount_pos_of_mem (gs : List Gate) (g : Gate) (hg : g ∈ gs) (hn : g.op = GateOp.not) :
    0 < notCount ⟨gs, 0⟩ := by
  induction gs with
  | nil => cases hg
  | cons a tl ih =>
    rw [notCount_cons]
    simp only [List.mem_cons] at hg
    rcases hg with hga | hg
    · subst hga
      rcases g with ⟨op, ins⟩
      dsimp at hn; subst hn
      rw [notCount_singleton_not]; omega
    · have := ih hg; omega

lemma monotone2_of_fanInTwo_notZero (gs : List Gate) (hfit : FanInTwo ⟨gs, 0⟩)
    (h0 : notCount ⟨gs, 0⟩ = 0) : Monotone2 ⟨gs, 0⟩ := by
  intro g hg
  have hf := hfit g hg
  refine ⟨?_, hf.2⟩
  rcases hf.1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (notCount_pos_of_mem gs g hg h) (by omega)

lemma split_first_not : ∀ (gs : List Gate), 0 < notCount ⟨gs, 0⟩ →
    ∃ pre g post, gs = pre ++ g :: post ∧ notCount ⟨pre, 0⟩ = 0 ∧
      g.op = GateOp.not ∧ notCount ⟨gs, 0⟩ = notCount ⟨post, 0⟩ + 1 := by
  intro gs
  induction gs with
  | nil => intro h; simp [notCount] at h
  | cons g gs ih =>
    intro h
    by_cases hn : g.op = GateOp.not
    · refine ⟨[], g, gs, rfl, rfl, hn, ?_⟩
      rcases g with ⟨op, ins⟩
      dsimp at hn; subst hn
      rw [notCount_cons, notCount_singleton_not]; omega
    · have hsing0 : notCount ⟨[g], 0⟩ = 0 := by
        rcases g with ⟨op, ins⟩
        cases ho : op with
        | not => exact absurd ho hn
        | and => exact notCount_singleton_and _
        | or => exact notCount_singleton_or _
        | mod _ => simp [notCount, ho]
        | maj => simp [notCount, ho]
      rw [notCount_cons, hsing0, zero_add] at h
      obtain ⟨pre, g1, post, heq, hpre0, hg1, hcnt⟩ := ih h
      refine ⟨g :: pre, g1, post, by rw [heq]; rfl, ?_, hg1, ?_⟩
      · rw [notCount_cons, hsing0, hpre0]
      · rw [notCount_cons, hsing0, zero_add]; exact hcnt

end PairEval

section MatroidHelpers

lemma rk_ins_le {n : ℕ} (R : Finset (Fin n) → ℕ) (hcard : ∀ x, R x ≤ x.card)
    (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) (x : Finset (Fin n)) (j : Fin n) :
    R (insert j x) ≤ R x + 1 := by
  have h1 := hsub x {j}
  have h2 : R {j} ≤ 1 := by simpa using hcard {j}
  have h3 : x ∪ {j} = insert j x := by ext a; simp
  rw [h3] at h1
  omega

lemma rk_anti {n : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    {x y : Finset (Fin n)} (hxy : x ⊆ y) (j : Fin n)
    (hy : R y < R (insert j y)) : R x < R (insert j x) := by
  have h1 := hsub (insert j x) y
  have hu : insert j x ∪ y = insert j y := by
    ext a; simp only [Finset.mem_union, Finset.mem_insert]
    constructor
    · rintro ((rfl | ha) | ha)
      · exact Or.inl rfl
      · exact Or.inr (hxy ha)
      · exact Or.inr ha
    · rintro (rfl | ha)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr ha
  have hi : x ⊆ insert j x ∩ y := fun a ha => Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, hxy ha⟩
  have hmi : R x ≤ R (insert j x ∩ y) := hmono hi
  rw [hu] at h1
  omega

lemma rk_union_closed {n : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (s u : Finset (Fin n)) (hcl : ∀ j ∈ s, R (insert j u) ≤ R u) :
    R (s ∪ u) = R u := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hsu := ih (fun j hj => hcl j (Finset.mem_insert_of_mem hj))
    have ha' : R (insert a (s ∪ u)) ≤ R (s ∪ u) := by
      by_contra hlt
      have hgt : R (s ∪ u) < R (insert a (s ∪ u)) := by omega
      have h1 := rk_anti R hmono hsub Finset.subset_union_right a hgt
      have h2 := hcl a (Finset.mem_insert_self a s)
      omega
    have heq : R (insert a (s ∪ u)) = R (s ∪ u) :=
      Nat.le_antisymm ha' (hmono (Finset.subset_insert a (s ∪ u)))
    rw [Finset.insert_union, heq, hsu]

lemma rk_extend_exists {n : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x : Finset (Fin n)) (hx : R x < R Finset.univ) :
    ∃ j : Fin n, R x < R (insert j x) := by
  by_contra hall
  push Not at hall
  have hu := rk_union_closed R hmono hsub Finset.univ x (fun j _ => hall j)
  rw [Finset.union_eq_left.mpr (Finset.subset_univ x)] at hu
  omega

lemma rk_indep_exists {n : ℕ} (R : Finset (Fin n) → ℕ) (h0 : R ∅ = 0)
    (hmono : Monotone R) (hcard : ∀ x, R x ≤ x.card)
    (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x : Finset (Fin n)) (k : ℕ) (hk : k ≤ R x) :
    ∃ s : Finset (Fin n), s ⊆ x ∧ s.card = k ∧ R s = k := by
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset x, rfl, h0⟩
  | succ k ih =>
    obtain ⟨s, hsx, hscard, hsrk⟩ := ih (Nat.le_of_succ_le hk)
    have hex : ∃ j ∈ x, R s < R (insert j s) := by
      by_contra hall
      push Not at hall
      have hu := rk_union_closed R hmono hsub x s hall
      rw [Finset.union_eq_left.mpr hsx] at hu
      omega
    obtain ⟨j, hjx, hfj⟩ := hex
    have hj_not : j ∉ s := fun hjs => by rw [Finset.insert_eq_of_mem hjs] at hfj; exact Nat.lt_irrefl _ hfj
    have hle := rk_ins_le R hcard hsub s j
    refine ⟨insert j s, Finset.insert_subset hjx hsx, ?_, by omega⟩
    rw [Finset.card_insert_of_notMem hj_not, hscard]

end MatroidHelpers

section ChainLowerBound

def FitWires (n m : ℕ) (R : Finset (Fin n) → ℕ) (C : Circuit)
    (old : Fin n → ℕ) (pad : Fin m → ℕ) : Prop :=
  ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
    let w := C.wires (pairVec n m x z)
    (∀ i, R x < R (insert i x) → w.getD (old i) false = true) ∧
    (∀ i ∈ x, w.getD (old i) false = false) ∧
    (∀ j, w.getD (pad j) false = decide (j ∉ z))

lemma fall_of_chain_step {n m : ℕ} (R : Finset (Fin n) → ℕ) (C : Circuit)
    (old : Fin n → ℕ) (pad : Fin m → ℕ)
    (hfit : FitWires n m R C old pad)
    {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)}
    (hstep : (∃ i, R x1 < R (insert i x1) ∧ x2 = insert i x1 ∧ z2 = z1) ∨
             (∃ j, j ∉ z1 ∧ x2 = x1 ∧ z2 = insert j z1)) :
    x1 ⊆ x2 ∧ z1 ⊆ z2 ∧
    ∃ wire, (C.wires (pairVec n m x1 z1)).getD wire false = true ∧
            (C.wires (pairVec n m x2 z2)).getD wire false = false := by
  rcases hstep with ⟨i, hinc, hx2, hz2⟩ | ⟨j, hj, hx2, hz2⟩
  · rw [hx2, hz2]
    refine ⟨Finset.subset_insert i x1, Finset.Subset.refl _, old i, ?_, ?_⟩
    · exact (hfit x1 z1).1 i hinc
    · exact (hfit (insert i x1) z1).2.1 i (Finset.mem_insert_self i x1)
  · rw [hx2, hz2]
    refine ⟨Finset.Subset.refl _, Finset.subset_insert j z1, pad j, ?_, ?_⟩
    · rw [(hfit x1 z1).2.2 j]; exact decide_eq_true hj
    · rw [(hfit x1 (insert j z1)).2.2 j]; simp

lemma chain_evalNotCode_drop {n m : ℕ} (R : Finset (Fin n) → ℕ) (C : Circuit)
    (hfan : FanInTwo C) (old : Fin n → ℕ) (pad : Fin m → ℕ)
    (hfit : FitWires n m R C old pad) (gs : List Gate)
    (hgs : FanInTwo ⟨gs, 0⟩) :
    ∀ (ch : List (Finset (Fin n) × Finset (Fin m))) (hch : ch ≠ []),
      (∀ k, k + 1 < ch.length →
        let p1 := ch.getD k (∅, ∅)
        let p2 := ch.getD (k + 1) (∅, ∅)
        (∃ i, R p1.1 < R (insert i p1.1) ∧ p2.1 = insert i p1.1 ∧ p2.2 = p1.2) ∨
        (∃ j, j ∉ p1.2 ∧ p2.1 = p1.1 ∧ p2.2 = insert j p1.2)) →
      ∀ (pre : List Gate), C.gates = pre ++ gs → notCount ⟨pre, 0⟩ = 0 →
        evalNotCode gs (wiresFrom pre (pairVec n m (ch.getLast hch).1 (ch.getLast hch).2)) + (ch.length - 1) ≤
          evalNotCode gs (wiresFrom pre (pairVec n m (ch.head hch).1 (ch.head hch).2)) := by
  intro ch
  induction ch with
  | nil => intro hne; exact absurd rfl hne
  | cons a tl ih =>
    intro hne hstep pre hceq hpre0
    cases tl with
    | nil => simp
    | cons b tl' =>
      have h0 : 0 + 1 < (a :: b :: tl').length := by simp
      have hs0 := hstep 0 h0
      simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
        List.getElem?_cons_succ] at hs0
      have hfb := fall_of_chain_step R C old pad hfit hs0
      rcases hfb with ⟨hxab, hzab, wire, hwt, hwf⟩
      have hmono_pre : Monotone2 ⟨pre, 0⟩ :=
        monotone2_of_fanInTwo_notZero pre (fun g hg => hfan g (by rw [hceq]; exact List.mem_append_left _ hg)) hpre0
      have hlenp : (wiresFrom pre (pairVec n m a.1 a.2)).length =
          (wiresFrom pre (pairVec n m b.1 b.2)).length := by
        rw [wiresFrom_length, wiresFrom_length, pairVec_length, pairVec_length]
      have hw_le : ∀ i, (wiresFrom pre (pairVec n m a.1 a.2)).getD i false ≤
          (wiresFrom pre (pairVec n m b.1 b.2)).getD i false :=
        wiresFrom_mono pre hmono_pre _ _ (by rw [pairVec_length, pairVec_length]) (pairVec_mono hxab hzab)
      have hdich := evalNotCode_dichotomy gs _ _ hgs hlenp hw_le
      have hlt_step : evalNotCode gs (wiresFrom pre (pairVec n m b.1 b.2)) <
          evalNotCode gs (wiresFrom pre (pairVec n m a.1 a.2)) := by
        rcases hdich with hlt | ⟨_, hle⟩
        · exact hlt
        · exfalso
          have h3 := hle wire
          have hwA : (wiresFrom gs (wiresFrom pre (pairVec n m a.1 a.2))).getD wire false =
              (C.wires (pairVec n m a.1 a.2)).getD wire false := by
            rw [← wiresFrom_append, ← hceq]; rfl
          have hwB : (wiresFrom gs (wiresFrom pre (pairVec n m b.1 b.2))).getD wire false =
              (C.wires (pairVec n m b.1 b.2)).getD wire false := by
            rw [← wiresFrom_append, ← hceq]; rfl
          rw [hwA, hwB, hwt, hwf] at h3
          exact not_true_le_false h3
      have hih := ih (by simp) (fun k hk => by
        have hk' : (k + 1) + 1 < (a :: b :: tl').length := by simp at hk ⊢; omega
        exact hstep (k + 1) hk') pre hceq hpre0
      have hlast : (a :: b :: tl').getLast hne = (b :: tl').getLast (by simp) := rfl
      have hhead : (b :: tl').head (by simp) = b := rfl
      have hheadA : (a :: b :: tl').head hne = a := rfl
      rw [hlast, hheadA]
      rw [hhead] at hih
      simp only [List.length_cons] at hih ⊢
      omega

end ChainLowerBound

section MonotoneSynth

noncomputable def emitCube (base oneWire n : ℕ) {m : ℕ} (gs : List Gate)
    (p1 : Finset (Fin n)) (p2 : Finset (Fin m)) : List Gate × ℕ :=
  let ws := (p1.toList.map Fin.val) ++ (p2.toList.map (fun j : Fin m => n + j.val))
  emitAndList base oneWire gs ws

lemma emitCube_spec (n m : ℕ) (base oneWire : ℕ) (hbas : base = n + m + 2)
    (ho : oneWire < base) (gs : List Gate)
    (p1 : Finset (Fin n)) (p2 : Finset (Fin m)) :
    let r := emitCube base oneWire n gs p1 p2
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom r.1 (pairVec n m x z)).getD r.2 false =
        ((pairVec n m x z).getD oneWire false && decide (p1 ⊆ x ∧ p2 ⊆ z)) := by
  dsimp only [emitCube]
  set ws := (p1.toList.map Fin.val) ++ (p2.toList.map (fun j : Fin m => n + j.val))
  have hws : ∀ i ∈ ws, i < base + gs.length := by
    intro i hi
    simp only [ws, List.mem_append, List.mem_map] at hi
    rcases hi with ⟨a, _, rfl⟩ | ⟨b, _, rfl⟩
    · have := a.isLt; omega
    · have := b.isLt; omega
  have h1 := emitAndList_spec base ws oneWire gs (by omega) hws
  rcases h1 with ⟨hext, hlt, hnc, _, hval⟩
  refine ⟨hext, hlt, hnc, ?_⟩
  intro x z
  have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
  rw [hval (pairVec n m x z) hlen]
  have hone : (wiresFrom gs (pairVec n m x z)).getD oneWire false = (pairVec n m x z).getD oneWire false :=
    wiresFrom_getD_lt gs (pairVec n m x z) oneWire (by rw [hlen]; exact ho)
  rw [hone]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq, ws, List.mem_append, List.mem_map, Finset.mem_toList]
  constructor
  · intro h
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have h0 := h a.val (Or.inl ⟨a, ha, rfl⟩)
      rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := a.isLt; omega), pairVec_getD_left] at h0
      exact of_decide_eq_true h0
    · have h0 := h (n + b.val) (Or.inr ⟨b, hb, rfl⟩)
      rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := b.isLt; omega), pairVec_getD_right] at h0
      exact of_decide_eq_true h0
  · rintro ⟨hx, hz⟩ i (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
    · rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := a.isLt; omega), pairVec_getD_left]
      exact decide_eq_true (hx ha)
    · rw [wiresFrom_getD_lt _ _ _ (by rw [hlen, hbas]; have := b.isLt; omega), pairVec_getD_right]
      exact decide_eq_true (hz hb)

noncomputable def emitMonoAux (n m base zeroWire oneWire : ℕ) :
    List Gate → List (Finset (Fin n) × Finset (Fin m)) → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, p :: ps =>
    let rc := emitCube base oneWire n gs p.1 p.2
    let rr := emitMonoAux n m base zeroWire oneWire rc.1 ps
    (rr.1, rc.2 :: rr.2)

lemma emitMonoAux_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (ho : oneWire < base) :
    ∀ (ps : List (Finset (Fin n) × Finset (Fin m))) (gs : List Gate),
      let r := emitMonoAux n m base zeroWire oneWire gs ps
      Extends base gs r.1 ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
        (r.2.any (fun w => (wiresFrom r.1 (pairVec n m x z)).getD w false)) =
          ps.any (fun p => (pairVec n m x z).getD oneWire false && decide (p.1 ⊆ x ∧ p.2 ⊆ z)) := by
  intro ps
  induction ps with
  | nil =>
    intro gs
    dsimp only [emitMonoAux]
    refine ⟨Extends.refl base gs, (fun _ h => by cases h), rfl, fun _ _ => rfl⟩
  | cons p ps ih =>
    intro gs
    dsimp only [emitMonoAux]
    set rc := emitCube base oneWire n gs p.1 p.2 with hrc
    have hc := emitCube_spec n m base oneWire hbas ho gs p.1 p.2
    rw [← hrc] at hc
    rcases hc with ⟨hext1, hlt1, hnc1, hval1⟩
    set rr := emitMonoAux n m base zeroWire oneWire rc.1 ps with hrr
    have hr := ih rc.1
    rw [← hrr] at hr
    rcases hr with ⟨hext2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, ?_, by omega, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · have := hext2.length_le; omega
      · exact hlt2 w hw
    · intro x z
      have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
      simp only [List.any_cons]
      rw [hext2.wire_eq _ hlen _ hlt1, hval1 x z, hval2 x z]

noncomputable def emitMonoQ (n m base zeroWire oneWire : ℕ) (gs : List Gate)
    (Q : Finset (Fin n) → Finset (Fin m) → Bool) : List Gate × ℕ :=
  let ps := (Finset.univ.filter (fun p : Finset (Fin n) × Finset (Fin m) => Q p.1 p.2 = true)).toList
  let r1 := emitMonoAux n m base zeroWire oneWire gs ps
  emitOrList base zeroWire r1.1 r1.2

lemma emitMonoQ_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (hz : zeroWire < base) (ho : oneWire < base) (gs : List Gate)
    (Q : Finset (Fin n) → Finset (Fin m) → Bool)
    (hQmono : ∀ (x1 x2 : Finset (Fin n)) (z1 z2 : Finset (Fin m)), x1 ⊆ x2 → z1 ⊆ z2 → Q x1 z1 = true → Q x2 z2 = true)
    (hzero : ∀ x z, (pairVec n m x z).getD zeroWire false = false)
    (hone : ∀ x z, (pairVec n m x z).getD oneWire false = true) :
    let r := emitMonoQ n m base zeroWire oneWire gs Q
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom r.1 (pairVec n m x z)).getD r.2 false = Q x z := by
  dsimp only [emitMonoQ]
  set ps := (Finset.univ.filter (fun p : Finset (Fin n) × Finset (Fin m) => Q p.1 p.2 = true)).toList
  set r1 := emitMonoAux n m base zeroWire oneWire gs ps with hr1
  have h1 := emitMonoAux_spec n m base zeroWire oneWire hbas ho ps gs
  rw [← hr1] at h1
  rcases h1 with ⟨hext1, hlt1, hnc1, hval1⟩
  have hz' : zeroWire < base + r1.1.length := by omega
  have h2 := emitOrList_spec base r1.2 zeroWire r1.1 hz' hlt1
  rcases h2 with ⟨hext2, hlt2, hnc2, _, hval2⟩
  refine ⟨hext1.trans hext2, hlt2, by omega, ?_⟩
  intro x z
  have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
  rw [hval2 _ hlen, wiresFrom_getD_lt _ _ _ (by rw [hlen]; exact hz), hzero x z, Bool.false_or, hval1 x z]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, ps, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hpQ, _, hx, hz'⟩
    exact hQmono p.1 x p.2 z hx hz' hpQ
  · intro hQx
    refine ⟨(x, z), hQx, hone x z, Finset.Subset.refl _, Finset.Subset.refl _⟩

end MonotoneSynth

section Conjunct1

noncomputable def buildThreshList (n m base zeroWire oneWire : ℕ) (R : Finset (Fin n) → ℕ) :
    List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, k :: ks =>
    let r1 := emitMonoQ n m base zeroWire oneWire gs (fun x z => decide (k + 1 ≤ R x + z.card))
    let rr := buildThreshList n m base zeroWire oneWire R r1.1 ks
    (rr.1, r1.2 :: rr.2)

lemma buildThreshList_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (hz : zeroWire < base) (ho : oneWire < base) (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hzero : ∀ x z, (pairVec n m x z).getD zeroWire false = false)
    (hone : ∀ x z, (pairVec n m x z).getD oneWire false = true) :
    ∀ (ks : List ℕ) (gs : List Gate),
      let r := buildThreshList n m base zeroWire oneWire R gs ks
      Extends base gs r.1 ∧
      r.2.length = ks.length ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (t : ℕ), t < ks.length →
        (wiresFrom r.1 (pairVec n m x z)).getD (r.2.getD t 0) false =
          decide (ks.getD t 0 + 1 ≤ R x + z.card) := by
  intro ks
  induction ks with
  | nil =>
    intro gs; dsimp only [buildThreshList]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, (fun _ _ t ht => by change t < 0 at ht; omega)⟩
  | cons k ks ih =>
    intro gs; dsimp only [buildThreshList]
    have hQm : ∀ (x1 x2 : Finset (Fin n)) (z1 z2 : Finset (Fin m)), x1 ⊆ x2 → z1 ⊆ z2 →
        decide (k + 1 ≤ R x1 + z1.card) = true → decide (k + 1 ≤ R x2 + z2.card) = true := by
      intro x1 x2 z1 z2 hx hz' h1
      rw [decide_eq_true_eq] at h1 ⊢
      have hRx := hmono hx
      have hzc := Finset.card_le_card hz'
      omega
    set r1 := emitMonoQ n m base zeroWire oneWire gs (fun x z => decide (k + 1 ≤ R x + z.card)) with hr1
    have h1 := emitMonoQ_spec n m base zeroWire oneWire hbas hz ho gs _ hQm hzero hone
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hval1⟩
    set rr := buildThreshList n m base zeroWire oneWire R r1.1 ks with hrr
    have hr := ih r1.1
    rw [← hrr] at hr
    rcases hr with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · have := hext2.length_le; omega
      · exact hlt2 w hw
    · intro x z t ht
      have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
      cases t with
      | zero =>
        change (wiresFrom rr.1 (pairVec n m x z)).getD r1.2 false = _
        rw [hext2.wire_eq _ hlen _ hlt1, hval1 x z]; rfl
      | succ t' =>
        have ht' : t' < ks.length := by simp at ht; omega
        exact hval2 x z t' ht'

def combineNys (base zeroWire : ℕ) : List Gate → List ℕ → List ℕ → List Gate × ℕ
  | gs, [], _ => (gs, zeroWire)
  | gs, _, [] => (gs, zeroWire)
  | gs, ny :: nys, g :: gsQ =>
    let rA := emitAnd base gs ny g
    let rR := combineNys base zeroWire rA.1 nys gsQ
    emitOr base rR.1 rA.2 rR.2

lemma combineNys_spec (base zeroWire : ℕ) (hz : zeroWire < base) :
    ∀ (nys gsQ : List ℕ) (gs : List Gate),
      nys.length = gsQ.length →
      (∀ w ∈ nys, w < base + gs.length) →
      (∀ w ∈ gsQ, w < base + gs.length) →
      let r := combineNys base zeroWire gs nys gsQ
      Extends base gs r.1 ∧
      r.2 < base + r.1.length ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (w : List Bool), w.length = base →
        ((wiresFrom r.1 w).getD r.2 false = true ↔
          (wiresFrom gs w).getD zeroWire false = true ∨
          ∃ t < nys.length, (wiresFrom gs w).getD (nys.getD t 0) false = true ∧
                            (wiresFrom gs w).getD (gsQ.getD t 0) false = true) := by
  intro nys
  induction nys with
  | nil =>
    intro gsQ gs _ _ _
    dsimp only [combineNys]
    refine ⟨Extends.refl base gs, by omega, rfl, fun _ _ => by simp⟩
  | cons ny nys ih =>
    intro gsQ gs hlen hny hgq
    cases gsQ with
    | nil => simp at hlen
    | cons g gsQ =>
      dsimp only [combineNys]
      have hny0 : ny < base + gs.length := hny ny (List.mem_cons_self ..)
      have hgq0 : g < base + gs.length := hgq g (List.mem_cons_self ..)
      set rA := emitAnd base gs ny g with hrA
      have hA := emitAnd_spec base gs ny g hny0 hgq0
      rw [← hrA] at hA
      rcases hA with ⟨hextA, hltA, hncA, _, hvalA⟩
      have hglA := hextA.length_le
      set rR := combineNys base zeroWire rA.1 nys gsQ with hrR
      have hR := ih gsQ rA.1 (by simp at hlen; exact hlen)
        (fun w hw => lt_of_lt_of_le (hny w (List.mem_cons_of_mem _ hw)) (by omega))
        (fun w hw => lt_of_lt_of_le (hgq w (List.mem_cons_of_mem _ hw)) (by omega))
      rw [← hrR] at hR
      rcases hR with ⟨hextR, hltR, hncR, hvalR⟩
      have hglR := hextR.length_le
      have hextAR := hextA.trans hextR
      set rO := emitOr base rR.1 rA.2 rR.2 with hrO
      have hO := emitOr_spec base rR.1 rA.2 rR.2 (by omega) hltR
      rw [← hrO] at hO
      rcases hO with ⟨hextO, hltO, hncO, _, hvalO⟩
      refine ⟨hextAR.trans hextO, hltO, by omega, ?_⟩
      intro w hw
      rw [hvalO w hw, Bool.or_eq_true, hextR.wire_eq w hw _ hltA, hvalA w hw, Bool.and_eq_true, hvalR w hw]
      have hcongr : ∀ t < nys.length,
          ((wiresFrom rA.1 w).getD (nys.getD t 0) false = true ∧
           (wiresFrom rA.1 w).getD (gsQ.getD t 0) false = true) ↔
          ((wiresFrom gs w).getD (nys.getD t 0) false = true ∧
           (wiresFrom gs w).getD (gsQ.getD t 0) false = true) := by
        intro t ht
        rw [hextA.wire_eq w hw _ (hny _ (List.mem_cons_of_mem _ (getD_mem nys t 0 ht))),
            hextA.wire_eq w hw _ (hgq _ (List.mem_cons_of_mem _ (getD_mem gsQ t 0 (by simp at hlen; omega))))]
      rw [hextA.wire_eq w hw zeroWire (by omega)]
      constructor
      · rintro (⟨h1, h2⟩ | h0 | ⟨t, ht, h1, h2⟩)
        · exact Or.inr ⟨0, by simp, h1, h2⟩
        · exact Or.inl h0
        · obtain ⟨h1', h2'⟩ := (hcongr t ht).mp ⟨h1, h2⟩
          exact Or.inr ⟨t + 1, by simp; omega, h1', h2'⟩
      · rintro (h0 | ⟨t, ht, h1, h2⟩)
        · exact Or.inr (Or.inl h0)
        · cases t with
          | zero => exact Or.inl ⟨h1, h2⟩
          | succ t' =>
            have ht' : t' < nys.length := by simp at ht; omega
            exact Or.inr (Or.inr ⟨t', ht', (hcongr t' ht').mpr ⟨h1, h2⟩⟩)

noncomputable def buildGainList (n m base zeroWire oneWire : ℕ) (Q : ℕ → ℕ → Finset (Fin n) → Finset (Fin m) → Bool)
    (ks nys : List ℕ) : List Gate → ℕ → List Gate × List ℕ
  | gs, 0 => (gs, [])
  | gs, count + 1 =>
    let rr := buildGainList n m base zeroWire oneWire Q ks nys gs count
    let rQ := buildThreshListAux n m base zeroWire oneWire (Q count) rr.1 ks
    let rC := combineNys base zeroWire rQ.1 nys rQ.2
    (rC.1, rr.2 ++ [rC.2])
where
  buildThreshListAux (n m base zeroWire oneWire : ℕ) (Qi : ℕ → Finset (Fin n) → Finset (Fin m) → Bool) :
      List Gate → List ℕ → List Gate × List ℕ
    | gs, [] => (gs, [])
    | gs, k :: ks =>
      let r1 := emitMonoQ n m base zeroWire oneWire gs (Qi k)
      let rr := buildThreshListAux n m base zeroWire oneWire Qi r1.1 ks
      (rr.1, r1.2 :: rr.2)

lemma buildThreshListAux_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (hz : zeroWire < base) (ho : oneWire < base)
    (Qi : ℕ → Finset (Fin n) → Finset (Fin m) → Bool)
    (hQm : ∀ k x1 x2 z1 z2, x1 ⊆ x2 → z1 ⊆ z2 → Qi k x1 z1 = true → Qi k x2 z2 = true)
    (hzero : ∀ x z, (pairVec n m x z).getD zeroWire false = false)
    (hone : ∀ x z, (pairVec n m x z).getD oneWire false = true) :
    ∀ (ks : List ℕ) (gs : List Gate),
      let r := buildGainList.buildThreshListAux n m base zeroWire oneWire Qi gs ks
      Extends base gs r.1 ∧
      r.2.length = ks.length ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (t : ℕ), t < ks.length →
        (wiresFrom r.1 (pairVec n m x z)).getD (r.2.getD t 0) false = Qi (ks.getD t 0) x z := by
  intro ks
  induction ks with
  | nil =>
    intro gs; dsimp only [buildGainList.buildThreshListAux]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, (fun _ _ t ht => by change t < 0 at ht; omega)⟩
  | cons k ks ih =>
    intro gs; dsimp only [buildGainList.buildThreshListAux]
    set r1 := emitMonoQ n m base zeroWire oneWire gs (Qi k) with hr1
    have h1 := emitMonoQ_spec n m base zeroWire oneWire hbas hz ho gs (Qi k) (hQm k) hzero hone
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hval1⟩
    set rr := buildGainList.buildThreshListAux n m base zeroWire oneWire Qi r1.1 ks with hrr
    have hr := ih r1.1
    rw [← hrr] at hr
    rcases hr with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, ?_⟩
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · have := hext2.length_le; omega
      · exact hlt2 w hw
    · intro x z t ht
      have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
      cases t with
      | zero =>
        change (wiresFrom rr.1 (pairVec n m x z)).getD r1.2 false = _
        rw [hext2.wire_eq _ hlen _ hlt1, hval1 x z]; rfl
      | succ t' =>
        have ht' : t' < ks.length := by simp at ht; omega
        exact hval2 x z t' ht'

lemma buildGainList_spec (n m base zeroWire oneWire : ℕ) (hbas : base = n + m + 2)
    (hz : zeroWire < base) (ho : oneWire < base)
    (Q : ℕ → ℕ → Finset (Fin n) → Finset (Fin m) → Bool)
    (hQm : ∀ c k x1 x2 z1 z2, x1 ⊆ x2 → z1 ⊆ z2 → Q c k x1 z1 = true → Q c k x2 z2 = true)
    (hzero : ∀ x z, (pairVec n m x z).getD zeroWire false = false)
    (hone : ∀ x z, (pairVec n m x z).getD oneWire false = true)
    (ks nys : List ℕ) (gs0 : List Gate) (hlen_kn : nys.length = ks.length)
    (hnys_lt : ∀ w ∈ nys, w < base + gs0.length) :
    ∀ (cnt : ℕ),
      let r := buildGainList n m base zeroWire oneWire Q ks nys gs0 cnt
      Extends base gs0 r.1 ∧
      r.2.length = cnt ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs0, 0⟩ ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (c : ℕ), c < cnt →
        ((wiresFrom r.1 (pairVec n m x z)).getD (r.2.getD c 0) false = true ↔
          ∃ t < ks.length, (wiresFrom gs0 (pairVec n m x z)).getD (nys.getD t 0) false = true ∧
            Q c (ks.getD t 0) x z = true) := by
  intro cnt
  induction cnt with
  | zero =>
    dsimp only [buildGainList]
    refine ⟨Extends.refl base gs0, rfl, (fun _ h => by cases h), rfl, (fun _ _ _ hc => by omega)⟩
  | succ cnt ih =>
    dsimp only [buildGainList]
    set rr := buildGainList n m base zeroWire oneWire Q ks nys gs0 cnt with hrr
    rcases ih with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hgl1 := hext1.length_le
    set rQ := buildGainList.buildThreshListAux n m base zeroWire oneWire (Q cnt) rr.1 ks with hrQ
    have hQ := buildThreshListAux_spec n m base zeroWire oneWire hbas hz ho (Q cnt) (hQm cnt) hzero hone ks rr.1
    rw [← hrQ] at hQ
    rcases hQ with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
    have hgl2 := hext2.length_le
    have hnys_lt2 : ∀ w ∈ nys, w < base + rQ.1.length := fun w hw => by have := hnys_lt w hw; omega
    set rC := combineNys base zeroWire rQ.1 nys rQ.2 with hrC
    have hC := combineNys_spec base zeroWire hz nys rQ.2 rQ.1 (by omega) hnys_lt2 hlt2
    rw [← hrC] at hC
    rcases hC with ⟨hext3, hlt3, hnc3, hval3⟩
    have hgl3 := hext3.length_le
    have hext23 := hext2.trans hext3
    have hext123 := hext1.trans hext23
    refine ⟨hext123, by simp [hlen1], ?_, by omega, ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hlt1 w hw; omega
      · exact hlt3
    · intro x z c hc
      have hlen : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
      by_cases hcc : c < cnt
      · rw [getD_append_left _ _ c 0 (by omega)]
        rw [hext23.wire_eq _ hlen _ (hlt1 _ (getD_mem rr.2 c 0 (by omega)))]
        exact hval1 x z c hcc
      · have hceq : c = cnt := by omega
        have hc_eq : c = cnt := hceq
        rw [hc_eq, getD_append_right _ _ cnt 0 (by omega), show cnt - rr.2.length = 0 by omega]
        change (wiresFrom rC.1 (pairVec n m x z)).getD rC.2 false = true ↔ _
        rw [hval3 _ hlen, wiresFrom_getD_lt _ _ _ (by rw [hlen]; exact hz), hzero x z]
        simp only [Bool.false_eq_true, false_or]
        constructor
        · rintro ⟨t, ht, hny, hq⟩
          have ht' : t < ks.length := by omega
          rw [hext2.wire_eq _ hlen _ (by have := hnys_lt _ (getD_mem nys t 0 ht); omega),
              hext1.wire_eq _ hlen _ (hnys_lt _ (getD_mem nys t 0 ht))] at hny
          rw [hval2 x z t ht'] at hq
          exact ⟨t, ht', hny, hq⟩
        · rintro ⟨t, ht, hny, hq⟩
          refine ⟨t, by omega, ?_, ?_⟩
          · rw [hext2.wire_eq _ hlen _ (by have := hnys_lt _ (getD_mem nys t 0 (by omega)); omega),
                hext1.wire_eq _ hlen _ (hnys_lt _ (getD_mem nys t 0 (by omega)))]
            exact hny
          · rw [hval2 x z t ht]; exact hq

lemma conjunct1_proof (a n : ℕ) (R : Finset (Fin n) → ℕ)
    (hn : n ≤ 2 ^ a) (hmono : Monotone R) (hcard : ∀ x, R x ≤ x.card) :
    let h := 2 ^ a
    let b := a + 1
    let d := R Finset.univ
    let m := 2 * h - 1 - d
    let N := n + m
    ∃ C : Circuit,
      (FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size) ∧
      (∃ (old : Fin n → Fin (N + 2 + C.size)) (pad : Fin m → Fin (N + 2 + C.size)),
        ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
          let w := C.wires (pairVec n m x z)
          (∀ i, R x < R (insert i x) → w.getD (old i).val false = true) ∧
          (∀ i ∈ x, w.getD (old i).val false = false) ∧
          (∀ j, w.getD (pad j).val false = decide (j ∉ z))) ∧
      notCount C = b := by
  intro h b d m N
  let base := N + 2
  let zeroWire := N
  let oneWire := N + 1
  have hbas : base = n + m + 2 := rfl
  have hz : zeroWire < base := by omega
  have ho : oneWire < base := by omega
  have hzero : ∀ x z, (pairVec n m x z).getD zeroWire false = false := fun x z => pairVec_getD_false n m x z
  have hone : ∀ x z, (pairVec n m x z).getD oneWire false = true := fun x z => pairVec_getD_true n m x z
  have hd_le_n : d ≤ n := by simpa [d] using hcard Finset.univ
  have h_pos : 1 ≤ h := Nat.one_le_two_pow
  let K := 2 * h - 1
  let ks := List.range K
  have hks_len : ks.length = K := List.length_range
  have hK_lt : K < 2 ^ b := by
    have hb : 2 ^ b = 2 * h := by dsimp only [b, h]; rw [pow_succ]; ring
    omega
  let rTh := buildThreshList n m base zeroWire oneWire R [] ks
  have hTh := buildThreshList_spec n m base zeroWire oneWire hbas hz ho R hmono hzero hone ks []
  dsimp only at hTh
  rcases hTh with ⟨hextTh, hlenTh, hltTh, hncTh, hvalTh⟩
  let rInv := chainInv base b rTh.1 rTh.2
  have hInv := chainInv_spec base b rTh.1 rTh.2 (by rw [hlenTh, hks_len]; exact hK_lt) hltTh
  dsimp only at hInv
  rcases hInv with ⟨hextInv, hlenInv, hltInv, hncInv, _, hvalInv⟩
  have hncInv_le : notCount ⟨rInv.1, 0⟩ ≤ b := by
    have h0 : notCount ⟨rTh.1, 0⟩ = 0 := by rw [hncTh, notCount_nil]
    dsimp only [rInv] at hncInv ⊢; omega
  let extraNot := b - notCount ⟨rInv.1, 0⟩
  let gsBase := padNots base zeroWire rInv.1 extraNot
  have hPadNot := padNots_spec base zeroWire (by omega) extraNot rInv.1
  rcases hPadNot with ⟨hextPadNot, hncPadNot, _⟩
  have hextToBase : Extends base [] gsBase := (hextTh.trans hextInv).trans hextPadNot
  have hBase_nc : notCount ⟨gsBase, 0⟩ = b := by rw [hncPadNot]; dsimp only [extraNot]; omega
  have hgl_base : rInv.1.length ≤ gsBase.length := hextPadNot.length_le
  have hnys_lt_base : ∀ w ∈ rInv.2, w < base + gsBase.length := fun w hw => lt_of_lt_of_le (hltInv w hw) (Nat.add_le_add_left hgl_base base)
  let Qold : ℕ → ℕ → Finset (Fin n) → Finset (Fin m) → Bool := fun c k x z =>
    if hc : c < n then decide (k + 1 ≤ R (insert ⟨c, hc⟩ x) + z.card) else false
  have hQold_m : ∀ c k x1 x2 z1 z2, x1 ⊆ x2 → z1 ⊆ z2 → Qold c k x1 z1 = true → Qold c k x2 z2 = true := by
    intro c k x1 x2 z1 z2 hx hz' h1
    dsimp only [Qold] at h1 ⊢
    by_cases hc : c < n
    · simp only [hc, ↓reduceDIte, decide_eq_true_eq] at h1 ⊢
      have hRx := hmono (Finset.insert_subset_insert ⟨c, hc⟩ hx)
      have hzc := Finset.card_le_card hz'
      omega
    · simp only [hc, ↓reduceDIte] at h1; cases h1
  let rOld := buildGainList n m base zeroWire oneWire Qold ks rInv.2 gsBase n
  have hOld := buildGainList_spec n m base zeroWire oneWire hbas hz ho Qold hQold_m hzero hone
    ks rInv.2 gsBase (by rw [hlenInv, hlenTh]) hnys_lt_base n
  dsimp only at hOld
  rcases hOld with ⟨hextOld, hlenOld, hltOld, hncOld, hvalOld⟩
  have hnys_lt_old : ∀ w ∈ rInv.2, w < base + rOld.1.length := fun w hw => lt_of_lt_of_le (hnys_lt_base w hw) (Nat.add_le_add_left hextOld.length_le base)
  let Qpad : ℕ → ℕ → Finset (Fin n) → Finset (Fin m) → Bool := fun c k x z =>
    if hc : c < m then decide (k + 1 ≤ R x + (insert ⟨c, hc⟩ z).card) else false
  have hQpad_m : ∀ c k x1 x2 z1 z2, x1 ⊆ x2 → z1 ⊆ z2 → Qpad c k x1 z1 = true → Qpad c k x2 z2 = true := by
    intro c k x1 x2 z1 z2 hx hz' h1
    dsimp only [Qpad] at h1 ⊢
    by_cases hc : c < m
    · simp only [hc, ↓reduceDIte, decide_eq_true_eq] at h1 ⊢
      have hRx := hmono hx
      have hzc := Finset.card_le_card (Finset.insert_subset_insert ⟨c, hc⟩ hz')
      omega
    · simp only [hc, ↓reduceDIte] at h1; cases h1
  let rPad := buildGainList n m base zeroWire oneWire Qpad ks rInv.2 rOld.1 m
  have hPad := buildGainList_spec n m base zeroWire oneWire hbas hz ho Qpad hQpad_m hzero hone
    ks rInv.2 rOld.1 (by rw [hlenInv, hlenTh]) hnys_lt_old m
  dsimp only at hPad
  rcases hPad with ⟨hextPad, hlenPad, hltPad, hncPad, hvalPad⟩
  have hextAll : Extends base [] rPad.1 := (hextToBase.trans hextOld).trans hextPad
  rcases hextAll with ⟨eAll, heqAll, hfanAll, hrbAll⟩
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at heqAll hrbAll
  subst heqAll
  refine ⟨⟨rPad.1, 0⟩, ⟨hfanAll, hrbAll, by simp [Circuit.size]⟩, ?_, ?_⟩
  · refine ⟨fun i => ⟨rOld.2.getD i.val 0, by
        have hlt := hltOld _ (getD_mem rOld.2 i.val 0 (by rw [hlenOld]; exact i.isLt))
        have hgl := hextPad.length_le
        have : rOld.1.length ≤ rPad.1.length := hextPad.length_le; exact lt_of_lt_of_le hlt (Nat.add_le_add_left this base)⟩,
      fun j => ⟨rPad.2.getD j.val 0, by
        have hlt := hltPad _ (getD_mem rPad.2 j.val 0 (by rw [hlenPad]; exact j.isLt))
        exact hlt⟩, ?_⟩
    intro x z
    have hlenV : (pairVec n m x z).length = base := by rw [pairVec_length, hbas]
    have hny_val : ∀ t < K, (wiresFrom gsBase (pairVec n m x z)).getD (rInv.2.getD t 0) false =
        decide (R x + z.card ≤ t) := by
      intro t ht
      have hkt : t < rTh.2.length := by rw [hlenTh, hks_len]; exact ht
      have hdec : ∀ (i j : ℕ), i < rTh.2.length → j < rTh.2.length → i ≤ j →
          (wiresFrom rTh.1 (pairVec n m x z)).getD (rTh.2.getD j 0) false ≤
            (wiresFrom rTh.1 (pairVec n m x z)).getD (rTh.2.getD i 0) false := by
        intro i j hi hj hij
        rw [hvalTh x z i (by rw [← hlenTh]; exact hi), hvalTh x z j (by rw [← hlenTh]; exact hj), bool_le_iff]
        intro h2
        rw [decide_eq_true_eq] at h2 ⊢
        have hi_eq : ks.getD i 0 = i := by
          have hiK : i < K := by rw [← hks_len, ← hlenTh]; exact hi
          simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range hiK, Option.getD_some]
        have hj_eq : ks.getD j 0 = j := by
          have hjK : j < K := by rw [← hks_len, ← hlenTh]; exact hj
          simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range hjK, Option.getD_some]
        rw [hi_eq]; rw [hj_eq] at h2; omega
      have htInv : t < rInv.2.length := by rw [hlenInv]; exact hkt
      rw [hextPadNot.wire_eq _ hlenV _ (hltInv _ (getD_mem rInv.2 t 0 htInv))]
      rw [hvalInv (pairVec n m x z) hlenV hdec t hkt]
      rw [hvalTh x z t (by rw [hks_len]; exact ht)]
      have ht_eq : ks.getD t 0 = t := by
        simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range ht, Option.getD_some]
      rw [ht_eq]
      cases hle : decide (t + 1 ≤ R x + z.card) with
      | true => rw [decide_eq_true_eq] at hle; simp; omega
      | false => rw [decide_eq_false_iff_not] at hle; simp; omega
    have hny_old : ∀ t < K, (wiresFrom rOld.1 (pairVec n m x z)).getD (rInv.2.getD t 0) false =
        decide (R x + z.card ≤ t) := by
      intro t ht
      rw [hextOld.wire_eq _ hlenV _ (hnys_lt_base _ (getD_mem rInv.2 t 0 (by rw [hlenInv, hlenTh, hks_len]; exact ht)))]
      exact hny_val t ht
    refine ⟨?_, ?_, ?_⟩
    · intro i hinc
      change (wiresFrom rPad.1 (pairVec n m x z)).getD (rOld.2.getD i.val 0) false = true
      rw [hextPad.wire_eq _ hlenV _ (hltOld _ (getD_mem rOld.2 i.val 0 (by rw [hlenOld]; exact i.isLt)))]
      rw [hvalOld x z i.val i.isLt]
      let r := R x + z.card
      have hRx_lt_d : R x < d := lt_of_lt_of_le hinc (hmono (Finset.subset_univ _))
      have hz_le_m : z.card ≤ m := by simpa using Finset.card_le_univ z
      have hr_lt : r < K := by omega
      refine ⟨r, by rw [hks_len]; exact hr_lt, ?_, ?_⟩
      · rw [hny_val r hr_lt]; exact decide_eq_true (le_refl _)
      · have hr_eq : ks.getD r 0 = r := by
          simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range hr_lt, Option.getD_some]
        rw [hr_eq]
        dsimp only [Qold]
        rw [dif_pos i.isLt, decide_eq_true_eq]
        change R x + z.card + 1 ≤ R (insert i x) + z.card
        omega
    · intro i hix
      change (wiresFrom rPad.1 (pairVec n m x z)).getD (rOld.2.getD i.val 0) false = false
      rw [hextPad.wire_eq _ hlenV _ (hltOld _ (getD_mem rOld.2 i.val 0 (by rw [hlenOld]; exact i.isLt)))]
      cases hval : (wiresFrom rOld.1 (pairVec n m x z)).getD (rOld.2.getD i.val 0) false with
      | false => rfl
      | true =>
        exfalso
        rw [hvalOld x z i.val i.isLt] at hval
        rcases hval with ⟨t, ht, hny, hq⟩
        rw [hks_len] at ht
        rw [hny_val t ht, decide_eq_true_eq] at hny
        have ht_eq : ks.getD t 0 = t := by
          simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range ht, Option.getD_some]
        rw [ht_eq] at hq
        dsimp only [Qold] at hq
        rw [dif_pos i.isLt, decide_eq_true_eq] at hq
        have hins : insert ⟨i.val, i.isLt⟩ x = x := Finset.insert_eq_of_mem hix
        rw [hins] at hq
        omega
    · intro j
      change (wiresFrom rPad.1 (pairVec n m x z)).getD (rPad.2.getD j.val 0) false = decide (j ∉ z)
      apply Bool.eq_iff_iff.mpr
      rw [hvalPad x z j.val j.isLt, decide_eq_true_eq]
      constructor
      · rintro ⟨t, ht, hny, hq⟩ hmem
        rw [hks_len] at ht
        rw [hny_old t ht, decide_eq_true_eq] at hny
        have ht_eq : ks.getD t 0 = t := by
          simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range ht, Option.getD_some]
        rw [ht_eq] at hq
        dsimp only [Qpad] at hq
        rw [dif_pos j.isLt, decide_eq_true_eq] at hq
        have hins : insert ⟨j.val, j.isLt⟩ z = z := Finset.insert_eq_of_mem hmem
        rw [hins] at hq
        omega
      · intro hnot
        let r := R x + z.card
        have hRx_le_d : R x ≤ d := hmono (Finset.subset_univ _)
        have hzc_lt_m : z.card < m := by
          have hsub : z ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr (fun heq => hnot (heq ▸ Finset.mem_univ j))
          have hlt := Finset.card_lt_card hsub
          simpa using hlt
        have hr_lt : r < K := by omega
        refine ⟨r, by rw [hks_len]; exact hr_lt, ?_, ?_⟩
        · rw [hny_old r hr_lt]; exact decide_eq_true (le_refl _)
        · have hr_eq : ks.getD r 0 = r := by
            simp only [ks, List.getD_eq_getElem?_getD, List.getElem?_range hr_lt, Option.getD_some]
          rw [hr_eq]
          dsimp only [Qpad]
          rw [dif_pos j.isLt, decide_eq_true_eq]
          have hc : (insert (⟨j.val, j.isLt⟩ : Fin m) z).card = z.card + 1 :=
            Finset.card_insert_of_notMem hnot
          rw [hc]
          omega
  · change notCount ⟨rPad.1, 0⟩ = b
    rw [hncPad, hncOld]; exact hBase_nc

end Conjunct1

section Conjunct2

def evens {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: tl => a :: evens tl

def odds {α : Type*} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: tl => b :: odds tl

def interleave {α : Type*} : List α → List α → List α
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => a :: b :: interleave as bs

lemma evens_length {α : Type*} (l : List α) : (evens l).length = (l.length + 1) / 2 := by
  induction l using evens.induct with
  | case1 => simp [evens]
  | case2 _ => simp [evens]
  | case3 _ _ tl ih => simp [evens, ih]; omega

lemma odds_length {α : Type*} (l : List α) : (odds l).length = l.length / 2 := by
  induction l using odds.induct with
  | case1 => simp [odds]
  | case2 _ => simp [odds]
  | case3 _ _ tl ih => simp [odds, ih]; omega

lemma evens_mem {α : Type*} : ∀ {l : List α} {x : α}, x ∈ evens l → x ∈ l
  | [], _ => fun h => by cases h
  | [_], _ => fun h => h
  | a :: b :: tl, x => fun h => by
    simp only [evens, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (evens_mem h))

lemma odds_mem {α : Type*} : ∀ {l : List α} {x : α}, x ∈ odds l → x ∈ l
  | [], _ => fun h => by cases h
  | [_], _ => fun h => by cases h
  | a :: b :: tl, x => fun h => by
    simp only [odds, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (odds_mem h))

lemma interleave_length {α : Type*} : ∀ (as bs : List α), (interleave as bs).length = as.length + bs.length
  | [], bs => by simp [interleave]
  | a :: as, [] => by simp [interleave]
  | a :: as, b :: bs => by simp [interleave, interleave_length as bs]; omega

lemma interleave_mem {α : Type*} : ∀ {as bs : List α} {x : α}, x ∈ interleave as bs → x ∈ as ∨ x ∈ bs
  | [], bs, _ => fun h => Or.inr h
  | a :: as, [], _ => fun h => Or.inl h
  | a :: as, b :: bs, x => fun h => by
    simp only [interleave, List.mem_cons] at h ⊢
    rcases h with rfl | rfl | h
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)
    · rcases interleave_mem h with h1 | h2
      · exact Or.inl (Or.inr h1)
      · exact Or.inr (Or.inr h2)

lemma evens_map {α β : Type*} (f : α → β) : ∀ l : List α, evens (l.map f) = (evens l).map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: tl => by simp [evens, evens_map f tl]

lemma odds_map {α β : Type*} (f : α → β) : ∀ l : List α, odds (l.map f) = (odds l).map f
  | [] => rfl
  | [_] => rfl
  | a :: b :: tl => by simp [odds, odds_map f tl]

lemma interleave_map {α β : Type*} (f : α → β) : ∀ (as bs : List α),
    interleave (as.map f) (bs.map f) = (interleave as bs).map f
  | [], bs => by simp [interleave]
  | a :: as, [] => by simp [interleave]
  | a :: as, b :: bs => by simp [interleave, interleave_map f as bs]

def fixInnerBool : List Bool → List Bool
  | a :: b :: tl => (a || b) :: (a && b) :: fixInnerBool tl
  | rest => rest

def adjCmpBool : List Bool → List Bool
  | [] => []
  | e :: os => e :: fixInnerBool os

def oeMergeBool : ℕ → List Bool → List Bool → List Bool
  | 0, a :: _, b :: _ => [a || b, a && b]
  | 0, as, bs => as ++ bs
  | k + 1, as, bs =>
    adjCmpBool (interleave (oeMergeBool k (evens as) (evens bs)) (oeMergeBool k (odds as) (odds bs)))

def oeSortBool : ℕ → List Bool → List Bool
  | 0, xs => xs
  | r + 1, xs =>
    let half := 2 ^ r
    oeMergeBool r (oeSortBool r (xs.take half)) (oeSortBool r (xs.drop half))

def sortedBool (c m : ℕ) : List Bool :=
  List.replicate c true ++ List.replicate (m - c) false

lemma sortedBool_evens_odds (c m : ℕ) (hc : c ≤ 2 * m) :
    evens (sortedBool c (2 * m)) = sortedBool ((c + 1) / 2) m ∧
    odds (sortedBool c (2 * m)) = sortedBool (c / 2) m := by
  induction c using Nat.strong_induction_on generalizing m with
  | ind c ih =>
    rcases c with _ | _ | c'
    · simp only [sortedBool, Nat.zero_add, Nat.zero_div, Nat.sub_zero, List.replicate_zero, List.nil_append]
      clear ih
      induction m with
      | zero => simp [evens, odds]
      | succ m ihm =>
        have hrep : List.replicate (2 * (m + 1)) false = false :: false :: List.replicate (2 * m) false := by
          rw [show 2 * (m + 1) = 2 * m + 2 by omega, List.replicate_succ, List.replicate_succ]
        rw [hrep]
        have hih := ihm (by omega)
        simp [evens, odds, hih.1, hih.2, List.replicate_succ]
    · simp only [sortedBool]
      cases m with
      | zero => omega
      | succ m =>
        have hsub : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
        have hrep : List.replicate 1 true ++ List.replicate (2 * (m + 1) - 1) false =
            true :: false :: List.replicate (2 * m) false := by
          rw [hsub, List.replicate_one, List.replicate_succ]; rfl
        rw [hrep]
        have h0 : sortedBool 0 (2 * m) = List.replicate (2 * m) false := by simp [sortedBool]
        have ih0 := ih 0 (by omega) m (by omega)
        rw [h0] at ih0
        simp [sortedBool, evens, odds, ih0.1, ih0.2, List.replicate_succ]
    · cases m with
      | zero => omega
      | succ m =>
        have hrep : sortedBool (c' + 2) (2 * (m + 1)) = true :: true :: sortedBool c' (2 * m) := by
          dsimp only [sortedBool]
          rw [List.replicate_succ, List.replicate_succ, show 2 * (m + 1) - (c' + 2) = 2 * m - c' by omega]
          rfl
        rw [hrep]
        have ihc := ih c' (by omega) m (by omega)
        simp only [evens, odds, ihc.1, ihc.2]
        constructor
        · dsimp only [sortedBool]
          rw [show (c' + 2 + 1) / 2 = (c' + 1) / 2 + 1 by omega, List.replicate_succ,
              show m + 1 - ((c' + 1) / 2 + 1) = m - (c' + 1) / 2 by omega]
          rfl
        · dsimp only [sortedBool]
          rw [show (c' + 2) / 2 = c' / 2 + 1 by omega, List.replicate_succ,
              show m + 1 - (c' / 2 + 1) = m - c' / 2 by omega]
          rfl

lemma fixInnerBool_replicate_false (m : ℕ) :
    fixInnerBool (List.replicate m false) = List.replicate m false := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    rcases m with _ | _ | m
    · rfl
    · rfl
    · rw [show m + 2 = m + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]
      simp [fixInnerBool, ih m (by omega)]

lemma adjCmpBool_interleave_sorted (ce co m : ℕ) (hce : ce ≤ m) (hco : co ≤ m)
    (hle : co ≤ ce) (hd : ce ≤ co + 2) :
    adjCmpBool (interleave (sortedBool ce m) (sortedBool co m)) = sortedBool (ce + co) (2 * m) := by
  induction co generalizing ce m with
  | zero =>
    cases m with
    | zero =>
      have hce0 : ce = 0 := by omega
      subst hce0; rfl
    | succ m =>
      have hO : sortedBool 0 (m + 1) = false :: List.replicate m false := by
        simp [sortedBool, List.replicate_succ]
      have hi : ∀ k, interleave (List.replicate k false) (List.replicate k false) = List.replicate (2 * k) false := by
        intro k
        induction k with
        | zero => rfl
        | succ k ihk =>
          rw [List.replicate_succ, interleave, ihk, show 2 * (k + 1) = 2 * k + 1 + 1 by omega,
              List.replicate_succ, List.replicate_succ]
      rcases ce with _ | _ | _ | ce'
      · rw [hO]
        dsimp only [interleave, adjCmpBool, fixInnerBool]
        rw [hi m, ← List.replicate_succ, fixInnerBool_replicate_false]
        simp only [Bool.false_or, Bool.false_and, sortedBool, Nat.zero_add, Nat.sub_zero,
          List.replicate_zero, List.nil_append]
        rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega, List.replicate_succ, List.replicate_succ]
        rfl
      · have hE : sortedBool 1 (m + 1) = true :: List.replicate m false := by
          simp [sortedBool, List.replicate_succ]
        rw [hE, hO]
        dsimp only [interleave, adjCmpBool, fixInnerBool]
        rw [hi m, ← List.replicate_succ, fixInnerBool_replicate_false]
        simp only [sortedBool, Nat.add_zero]
        rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega, List.replicate_one, List.replicate_succ]
        rfl
      · cases m with
        | zero => omega
        | succ m =>
          have hE : sortedBool 2 (m + 2) = true :: true :: List.replicate m false := by
            simp [sortedBool, List.replicate_succ]
          have hO' : sortedBool 0 (m + 2) = false :: false :: List.replicate m false := by
            simp [sortedBool, List.replicate_succ]
          rw [hE, hO']
          dsimp only [interleave, adjCmpBool, fixInnerBool]
          rw [hi m, ← List.replicate_succ, fixInnerBool_replicate_false]
          simp only [Bool.false_or, Bool.or_true, Bool.false_and, sortedBool, Nat.add_zero,
            show 2 * (m + 2) - 2 = 2 * m + 2 by omega, show (1 + 1) * m = 2 * m by ring]
          simp [List.replicate_succ]
      · omega
  | succ co ih =>
    cases m with
    | zero => omega
    | succ m =>
      have hce_pos : 1 ≤ ce := by omega
      obtain ⟨ce', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ce ≠ 0)
      have hE : sortedBool (ce' + 1) (m + 1) = true :: sortedBool ce' m := by
        simp [sortedBool, List.replicate_succ]
      have hO : sortedBool (co + 1) (m + 1) = true :: sortedBool co m := by
        simp [sortedBool, List.replicate_succ]
      rw [hE, hO]
      dsimp only [interleave, adjCmpBool]
      have hrec : fixInnerBool (true :: interleave (sortedBool ce' m) (sortedBool co m)) =
          true :: adjCmpBool (interleave (sortedBool ce' m) (sortedBool co m)) := by
        cases htail : interleave (sortedBool ce' m) (sortedBool co m) with
        | nil => rfl
        | cons x tl => simp [fixInnerBool, adjCmpBool]
      rw [hrec, ih ce' m (by omega) (by omega) (by omega) (by omega)]
      simp only [sortedBool]
      rw [show ce' + 1 + (co + 1) = ce' + co + 2 by omega,
          show 2 * (m + 1) - (ce' + co + 2) = 2 * m - (ce' + co) by omega,
          List.replicate_succ, List.replicate_succ]
      rfl

lemma oeMergeBool_sorted : ∀ (k ce cb : ℕ), ce ≤ 2 ^ k → cb ≤ 2 ^ k →
    oeMergeBool k (sortedBool ce (2 ^ k)) (sortedBool cb (2 ^ k)) = sortedBool (ce + cb) (2 ^ (k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro ce cb hce hcb
    simp only [pow_zero] at hce hcb
    by_cases hce0 : ce = 0 <;> by_cases hcb0 : cb = 0
    · subst hce0 hcb0; rfl
    · have : cb = 1 := by omega
      subst hce0 this; rfl
    · have : ce = 1 := by omega
      subst hcb0 this; rfl
    · have : ce = 1 := by omega
      have : cb = 1 := by omega
      subst ‹ce = 1› ‹cb = 1›; rfl
  | succ k ih =>
    intro ce cb hce hcb
    dsimp only [oeMergeBool]
    have hm : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hev_a := (sortedBool_evens_odds ce (2 ^ k) (by omega)).1
    have hod_a := (sortedBool_evens_odds ce (2 ^ k) (by omega)).2
    have hev_b := (sortedBool_evens_odds cb (2 ^ k) (by omega)).1
    have hod_b := (sortedBool_evens_odds cb (2 ^ k) (by omega)).2
    rw [← hm] at hev_a hod_a hev_b hod_b
    rw [hev_a, hev_b, hod_a, hod_b]
    rw [ih _ _ (by omega) (by omega), ih _ _ (by omega) (by omega)]
    rw [adjCmpBool_interleave_sorted _ _ (2 ^ (k + 1)) (by omega) (by omega) (by omega) (by omega)]
    congr 1
    · omega
    · rw [pow_succ _ (k + 1)]; ring

lemma oeSortBool_sorted : ∀ (r : ℕ) (xs : List Bool), xs.length = 2 ^ r →
    ∃ c ≤ 2 ^ r, oeSortBool r xs = sortedBool c (2 ^ r) := by
  intro r
  induction r with
  | zero =>
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons x tl =>
      have htl : tl = [] := List.eq_nil_of_length_eq_zero (by rw [pow_zero, List.length_cons] at hlen; omega)
      subst htl
      cases x
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨1, by simp, rfl⟩
  | succ r ih =>
    intro xs hlen
    dsimp only [oeSortBool]
    have hlen1 : (xs.take (2 ^ r)).length = 2 ^ r := by
      rw [List.length_take, hlen, pow_succ]; omega
    have hlen2 : (xs.drop (2 ^ r)).length = 2 ^ r := by
      rw [List.length_drop, hlen, pow_succ]; omega
    obtain ⟨c1, hc1, hs1⟩ := ih (xs.take (2 ^ r)) hlen1
    obtain ⟨c2, hc2, hs2⟩ := ih (xs.drop (2 ^ r)) hlen2
    rw [hs1, hs2, oeMergeBool_sorted r c1 c2 hc1 hc2]
    exact ⟨c1 + c2, by rw [pow_succ]; omega, rfl⟩

lemma oeSortBool_count : ∀ (r : ℕ) (xs : List Bool), xs.length = 2 ^ r →
    (oeSortBool r xs).count true = xs.count true := by
  have hfix : ∀ l : List Bool, (fixInnerBool l).count true = l.count true := by
    intro l
    induction hlen : l.length using Nat.strong_induction_on generalizing l with
    | ind len ih =>
      rcases l with _ | ⟨a, _ | ⟨b, tl⟩⟩
      · rfl
      · rfl
      · simp only [fixInnerBool, List.count_cons]
        have htl := ih tl.length (by simp at hlen; omega) tl rfl
        cases a <;> cases b <;> simp [htl] <;> omega
  have hadj : ∀ l : List Bool, (adjCmpBool l).count true = l.count true := by
    intro l
    cases l with
    | nil => rfl
    | cons e os => simp [adjCmpBool, List.count_cons, hfix os]
  have hint : ∀ as bs : List Bool, (interleave as bs).count true = as.count true + bs.count true := by
    intro as
    induction as with
    | nil => intro bs; simp [interleave]
    | cons a as iha =>
      intro bs
      cases bs with
      | nil => simp [interleave]
      | cons b bs => simp [interleave, List.count_cons, iha bs]; omega
  have hevod : ∀ l : List Bool, (evens l).count true + (odds l).count true = l.count true := by
    intro l
    induction l using evens.induct with
    | case1 => simp [evens, odds]
    | case2 a => simp [evens, odds]
    | case3 a b tl ih => simp only [evens, odds, List.count_cons] at ih ⊢; omega
  have hmrg : ∀ (k : ℕ) (as bs : List Bool), as.length = 2 ^ k → bs.length = 2 ^ k →
      (oeMergeBool k as bs).count true = as.count true + bs.count true := by
    intro k
    induction k with
    | zero =>
      intro as bs ha hb
      rcases as with _ | ⟨a, as'⟩
      · simp at ha
      · rcases bs with _ | ⟨b, bs'⟩
        · simp at hb
        · have ha' : as' = [] := List.eq_nil_of_length_eq_zero (by rw [pow_zero, List.length_cons] at ha; omega)
          have hb' : bs' = [] := List.eq_nil_of_length_eq_zero (by rw [pow_zero, List.length_cons] at hb; omega)
          subst ha' hb'
          cases a <;> cases b <;> simp [oeMergeBool, List.count_cons] <;> omega
    | succ k ih =>
      intro as bs ha hb
      dsimp only [oeMergeBool]
      rw [hadj, hint, ih _ _ (by rw [evens_length, ha, pow_succ]; omega) (by rw [evens_length, hb, pow_succ]; omega),
          ih _ _ (by rw [odds_length, ha, pow_succ]; omega) (by rw [odds_length, hb, pow_succ]; omega)]
      have h1 := hevod as
      have h2 := hevod bs
      omega
  intro r
  induction r with
  | zero => intro _ _; rfl
  | succ r ih =>
    intro xs hlen
    dsimp only [oeSortBool]
    have hlen1 : (xs.take (2 ^ r)).length = 2 ^ r := by rw [List.length_take, hlen, pow_succ]; omega
    have hlen2 : (xs.drop (2 ^ r)).length = 2 ^ r := by rw [List.length_drop, hlen, pow_succ]; omega
    have hlenS1 : (oeSortBool r (xs.take (2 ^ r))).length = 2 ^ r := by
      rcases oeSortBool_sorted r (xs.take (2 ^ r)) hlen1 with ⟨c1, hc1, hs1⟩
      rw [hs1, sortedBool]; simp; omega
    have hlenS2 : (oeSortBool r (xs.drop (2 ^ r))).length = 2 ^ r := by
      rcases oeSortBool_sorted r (xs.drop (2 ^ r)) hlen2 with ⟨c2, hc2, hs2⟩
      rw [hs2, sortedBool]; simp; omega
    rw [hmrg r _ _ hlenS1 hlenS2]
    rw [ih _ hlen1, ih _ hlen2]
    conv_rhs => rw [← List.take_append_drop (2 ^ r) xs]
    rw [List.count_append]

def cmpPair (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × (ℕ × ℕ) :=
  let r1 := emitOr base gs a b
  let r2 := emitAnd base r1.1 a b
  (r2.1, (r1.2, r2.2))

def uncmpPair (base : ℕ) (gs : List Gate) (a b nhi nlo : ℕ) : List Gate × (ℕ × ℕ) :=
  let r1 := emitAnd base gs b nlo
  let r2 := emitOr base r1.1 r1.2 nhi
  let r3 := emitAnd base r2.1 a nlo
  let r4 := emitOr base r3.1 r3.2 nhi
  (r4.1, (r2.2, r4.2))

lemma cmpPair_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := cmpPair base gs a b
    Extends base gs r.1 ∧ r.2.1 < base + r.1.length ∧ r.2.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ nonNot r.1 = nonNot gs + 2 ∧
    ∀ w, w.length = base →
      (wiresFrom r.1 w).getD r.2.1 false = ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) ∧
      (wiresFrom r.1 w).getD r.2.2 false = ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [cmpPair]
  set r1 := emitOr base gs a b with hr1
  have h1 := emitOr_spec base gs a b ha hb
  rw [← hr1] at h1
  rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
  have hgl1 := hext1.length_le
  set r2 := emitAnd base r1.1 a b with hr2
  have h2 := emitAnd_spec base r1.1 a b (by omega) (by omega)
  rw [← hr2] at h2
  rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
  refine ⟨hext1.trans hext2, lt_of_lt_of_le hlt1 (by have := hext2.length_le; omega), hlt2, by omega, by omega, ?_⟩
  intro w hw
  rw [hext2.wire_eq w hw _ hlt1, hval1 w hw, hval2 w hw, hext1.wire_eq w hw a ha, hext1.wire_eq w hw b hb]
  exact ⟨rfl, rfl⟩

lemma uncmpPair_spec (base : ℕ) (gs : List Gate) (a b nhi nlo : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length)
    (hnhi : nhi < base + gs.length) (hnlo : nlo < base + gs.length) :
    let r := uncmpPair base gs a b nhi nlo
    Extends base gs r.1 ∧ r.2.1 < base + r.1.length ∧ r.2.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧ nonNot r.1 = nonNot gs + 4 ∧
    ∀ w, w.length = base →
      (wiresFrom gs w).getD nhi false = !((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) →
      (wiresFrom gs w).getD nlo false = !((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) →
      (wiresFrom r.1 w).getD r.2.1 false = !((wiresFrom gs w).getD a false) ∧
      (wiresFrom r.1 w).getD r.2.2 false = !((wiresFrom gs w).getD b false) := by
  dsimp only [uncmpPair]
  set r1 := emitAnd base gs b nlo with hr1
  have h1 := emitAnd_spec base gs b nlo hb hnlo
  rw [← hr1] at h1; rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩; have hgl1 := hext1.length_le
  set r2 := emitOr base r1.1 r1.2 nhi with hr2
  have h2 := emitOr_spec base r1.1 r1.2 nhi hlt1 (by omega)
  rw [← hr2] at h2; rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩; have hgl2 := hext2.length_le
  set r3 := emitAnd base r2.1 a nlo with hr3
  have h3 := emitAnd_spec base r2.1 a nlo (by omega) (by omega)
  rw [← hr3] at h3; rcases h3 with ⟨hext3, hlt3, hnc3, hnn3, hval3⟩; have hgl3 := hext3.length_le
  set r4 := emitOr base r3.1 r3.2 nhi with hr4
  have h4 := emitOr_spec base r3.1 r3.2 nhi hlt3 (by omega)
  rw [← hr4] at h4; rcases h4 with ⟨hext4, hlt4, hnc4, hnn4, hval4⟩
  refine ⟨((hext1.trans hext2).trans hext3).trans hext4,
    lt_of_lt_of_le hlt2 (by have := hext3.length_le; have := hext4.length_le; omega),
    hlt4, by omega, by omega, ?_⟩
  intro w hw h_nhi h_nlo
  have h12 := hext1.trans hext2
  have h34 := hext3.trans hext4
  rw [h34.wire_eq w hw _ hlt2, hval2 w hw, hval1 w hw,
      hext1.wire_eq w hw nhi (by omega), h_nhi, h_nlo]
  rw [hval4 w hw, hval3 w hw, h12.wire_eq w hw a (by omega), h12.wire_eq w hw nlo (by omega),
      hext3.wire_eq w hw nhi (by omega), h12.wire_eq w hw nhi (by omega), h_nhi, h_nlo]
  cases (wiresFrom gs w).getD a false <;> cases (wiresFrom gs w).getD b false <;> simp

def fixInnerInv (base : ℕ) : List Gate → List ℕ →
    List Gate × List ℕ × (List Gate → List ℕ → List Gate × List ℕ)
  | gs, [] => (gs, [], fun gs' _ => (gs', []))
  | gs, [x] => (gs, [x], fun gs' nxs => (gs', nxs))
  | gs, a :: b :: tl =>
    let rC := cmpPair base gs a b
    let rRest := fixInnerInv base rC.1 tl
    let undo : List Gate → List ℕ → List Gate × List ℕ := fun gs' nout =>
      match nout with
      | nhi :: nlo :: ntl =>
        let rU := uncmpPair base gs' a b nhi nlo
        let rR := rRest.2.2 rU.1 ntl
        (rR.1, rU.2.1 :: rU.2.2 :: rR.2)
      | _ => (gs', [])
    (rRest.1, rC.2.1 :: rC.2.2 :: rRest.2.1, undo)

lemma fixInnerInv_spec (base : ℕ) :
    ∀ (l : List ℕ) (gs : List Gate),
      (∀ i ∈ l, i < base + gs.length) →
      let res := fixInnerInv base gs l
      Extends base gs res.1 ∧
      res.2.1.length = l.length ∧
      (∀ i ∈ res.2.1, i < base + res.1.length) ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot res.1 ≤ nonNot gs + 2 * (l.length / 2) ∧
      (∀ w, w.length = base →
        res.2.1.map (fun i => (wiresFrom res.1 w).getD i false) =
          fixInnerBool (l.map (fun i => (wiresFrom gs w).getD i false))) ∧
      (∀ (gs' : List Gate) (nout : List ℕ),
        Extends base res.1 gs' → nout.length = res.2.1.length →
        (∀ u ∈ nout, u < base + gs'.length) →
        let ru := res.2.2 gs' nout
        Extends base gs' ru.1 ∧
        ru.2.length = l.length ∧
        (∀ u ∈ ru.2, u < base + ru.1.length) ∧
        notCount ⟨ru.1, 0⟩ = notCount ⟨gs', 0⟩ ∧
        nonNot ru.1 ≤ nonNot gs' + 4 * (l.length / 2) ∧
        ∀ w, w.length = base →
          (∀ t < res.2.1.length, (wiresFrom gs' w).getD (nout.getD t 0) false =
            !((wiresFrom gs' w).getD (res.2.1.getD t 0) false)) →
          ∀ t < l.length, (wiresFrom ru.1 w).getD (ru.2.getD t 0) false =
            !((wiresFrom gs' w).getD (l.getD t 0) false)) := by
  have hmain : ∀ (len : ℕ) (l : List ℕ), l.length = len → ∀ (gs : List Gate),
      (∀ i ∈ l, i < base + gs.length) →
      let res := fixInnerInv base gs l
      Extends base gs res.1 ∧
      res.2.1.length = l.length ∧
      (∀ i ∈ res.2.1, i < base + res.1.length) ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot res.1 ≤ nonNot gs + 2 * (l.length / 2) ∧
      (∀ w, w.length = base →
        res.2.1.map (fun i => (wiresFrom res.1 w).getD i false) =
          fixInnerBool (l.map (fun i => (wiresFrom gs w).getD i false))) ∧
      (∀ (gs' : List Gate) (nout : List ℕ),
        Extends base res.1 gs' → nout.length = res.2.1.length →
        (∀ u ∈ nout, u < base + gs'.length) →
        let ru := res.2.2 gs' nout
        Extends base gs' ru.1 ∧
        ru.2.length = l.length ∧
        (∀ u ∈ ru.2, u < base + ru.1.length) ∧
        notCount ⟨ru.1, 0⟩ = notCount ⟨gs', 0⟩ ∧
        nonNot ru.1 ≤ nonNot gs' + 4 * (l.length / 2) ∧
        ∀ w, w.length = base →
          (∀ t < res.2.1.length, (wiresFrom gs' w).getD (nout.getD t 0) false =
            !((wiresFrom gs' w).getD (res.2.1.getD t 0) false)) →
          ∀ t < l.length, (wiresFrom ru.1 w).getD (ru.2.getD t 0) false =
            !((wiresFrom gs' w).getD (l.getD t 0) false)) := by
    intro len
    induction len using Nat.strong_induction_on with
    | ind len ih =>
      intro l hlen_l gs hlt
      rcases l with _ | ⟨a, _ | ⟨b, tl⟩⟩
      · dsimp only [fixInnerInv]
        refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by omega, (fun _ _ => rfl), ?_⟩
        intro gs' nout _ _ _
        refine ⟨Extends.refl base gs', rfl, (fun _ h => by cases h), rfl, by omega, (fun _ _ _ t ht => by change t < 0 at ht; omega)⟩
      · dsimp only [fixInnerInv]
        refine ⟨Extends.refl base gs, rfl, hlt, rfl, by omega, (fun _ _ => rfl), ?_⟩
        intro gs' nout _ hlen hnout
        refine ⟨Extends.refl base gs', by simpa using hlen, hnout, rfl, by omega, ?_⟩
        intro w hw hneg t ht
        have ht0 : t = 0 := by simp at ht; omega
        subst ht0; exact hneg 0 (by simp)
      · dsimp only [fixInnerInv]
        have ha : a < base + gs.length := hlt a (List.mem_cons_self ..)
        have hb : b < base + gs.length := hlt b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
        have htl : ∀ i ∈ tl, i < base + gs.length := fun i hi =>
          hlt i (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hi))
        set rC := cmpPair base gs a b with hrC
        have hC := cmpPair_spec base gs a b ha hb
        rw [← hrC] at hC
        rcases hC with ⟨hextC, hltC1, hltC2, hncC, hnnC, hvalC⟩
        have hglC := hextC.length_le
        set rRest := fixInnerInv base rC.1 tl with hrRest
        have hRest := ih tl.length (by rw [← hlen_l]; simp) tl rfl rC.1
          (fun i hi => lt_of_lt_of_le (htl i hi) (Nat.add_le_add_left hglC base))
        rw [← hrRest] at hRest
        rcases hRest with ⟨hextR, hlenR, hltR, hncR, hnnR, hvalR, hundoR⟩
        have hglR := hextR.length_le
        have hhalf : (a :: b :: tl).length / 2 = tl.length / 2 + 1 := by simp; omega
        refine ⟨hextC.trans hextR, by simp [hlenR], ?_, by omega, by omega, ?_, ?_⟩
        · intro i hi
          simp only [List.mem_cons] at hi
          rcases hi with rfl | rfl | hi
          · exact lt_of_lt_of_le hltC1 (Nat.add_le_add_left hglR base)
          · exact lt_of_lt_of_le hltC2 (Nat.add_le_add_left hglR base)
          · exact hltR i hi
        · intro w hw
          simp only [List.map_cons, fixInnerBool]
          rw [hextR.wire_eq w hw _ hltC1, hextR.wire_eq w hw _ hltC2, (hvalC w hw).1, (hvalC w hw).2, hvalR w hw]
          congr 1; congr 1; congr 1
          apply List.map_congr_left
          intro i hi
          exact hextC.wire_eq w hw i (htl i hi)
        · intro gs' nout hext' hlen' hnout'
          rcases nout with _ | ⟨nhi, _ | ⟨nlo, ntl⟩⟩ <;> try (simp [hlenR] at hlen'; done)
          have hnhi : nhi < base + gs'.length := hnout' nhi (List.mem_cons_self ..)
          have hnlo : nlo < base + gs'.length := hnout' nlo (List.mem_cons_of_mem _ (List.mem_cons_self ..))
          have hntl : ∀ u ∈ ntl, u < base + gs'.length := fun u hu =>
            hnout' u (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hu))
          have hgl' := hext'.length_le
          set rU := uncmpPair base gs' a b nhi nlo with hrU
          have hU := uncmpPair_spec base gs' a b nhi nlo
            (by omega) (by omega) hnhi hnlo
          rw [← hrU] at hU
          rcases hU with ⟨hextU, hltU1, hltU2, hncU, hnnU, hvalU⟩
          have hglU := hextU.length_le
          set rR := rRest.2.2 rU.1 ntl with hrR
          have hntl_len : ntl.length = tl.length := by simp [hlenR] at hlen'; exact hlen'
          have hR := hundoR rU.1 ntl (hext'.trans hextU) (by rw [hlenR]; exact hntl_len)
            (fun u hu => lt_of_lt_of_le (hntl u hu) (Nat.add_le_add_left hglU base))
          rw [← hrR] at hR
          rcases hR with ⟨hextR', hlenR', hltR', hncR', hnnR', hvalR'⟩
          have hglR' := hextR'.length_le
          dsimp only
          have hlen_ru : (rU.2.1 :: rU.2.2 :: rR.2).length = (a :: b :: tl).length := by simp [hlenR']
          have hnc_ru : notCount ⟨rR.1, 0⟩ = notCount ⟨gs', 0⟩ := by omega
          have hnn_ru : nonNot rR.1 ≤ nonNot gs' + 4 * ((a :: b :: tl).length / 2) := by
            dsimp only [nonNot] at hnnU hnnR' ⊢; omega
          refine ⟨hextU.trans hextR', hlen_ru, ?_, hnc_ru, hnn_ru, ?_⟩
          · intro u hu
            simp only [List.mem_cons] at hu
            rcases hu with rfl | rfl | hu
            · exact lt_of_lt_of_le hltU1 (Nat.add_le_add_left hglR' base)
            · exact lt_of_lt_of_le hltU2 (Nat.add_le_add_left hglR' base)
            · exact hltR' u hu
          · intro w hw hneg t ht
            have hextC' : Extends base rC.1 gs' := hextR.trans hext'
            have hextG' : Extends base gs gs' := hextC.trans hextC'
            have h_nhi : (wiresFrom gs' w).getD nhi false =
                !((wiresFrom gs' w).getD a false || (wiresFrom gs' w).getD b false) := by
              have h0 := hneg 0 (by simp)
              change (wiresFrom gs' w).getD nhi false = !((wiresFrom gs' w).getD rC.2.1 false) at h0
              rw [h0, hextC'.wire_eq w hw _ hltC1, (hvalC w hw).1,
                  hextG'.wire_eq w hw a ha, hextG'.wire_eq w hw b hb]
            have h_nlo : (wiresFrom gs' w).getD nlo false =
                !((wiresFrom gs' w).getD a false && (wiresFrom gs' w).getD b false) := by
              have h1 := hneg 1 (by simp)
              change (wiresFrom gs' w).getD nlo false = !((wiresFrom gs' w).getD rC.2.2 false) at h1
              rw [h1, hextC'.wire_eq w hw _ hltC2, (hvalC w hw).2,
                  hextG'.wire_eq w hw a ha, hextG'.wire_eq w hw b hb]
            obtain ⟨hua, hub⟩ := hvalU w hw h_nhi h_nlo
            have hnegR : ∀ s < rRest.2.1.length, (wiresFrom rU.1 w).getD (ntl.getD s 0) false =
                !((wiresFrom rU.1 w).getD (rRest.2.1.getD s 0) false) := by
              intro s hs
              rw [hextU.wire_eq w hw _ (hntl _ (getD_mem ntl s 0 (by rw [hntl_len, ← hlenR]; exact hs))),
                  hextU.wire_eq w hw _ (lt_of_lt_of_le (hltR _ (getD_mem rRest.2.1 s 0 hs)) (Nat.add_le_add_left hgl' base))]
              exact hneg (s + 2) (by simp; exact hs)
            have hR' := hvalR' w hw hnegR
            rcases t with _ | _ | t'
            · change (wiresFrom rR.1 w).getD rU.2.1 false = !((wiresFrom gs' w).getD a false)
              rw [hextR'.wire_eq w hw _ hltU1, hua]
            · change (wiresFrom rR.1 w).getD rU.2.2 false = !((wiresFrom gs' w).getD b false)
              rw [hextR'.wire_eq w hw _ hltU2, hub]
            · have ht' : t' < tl.length := by simp only [List.length_cons] at ht; omega
              change (wiresFrom rR.1 w).getD (rR.2.getD t' 0) false = !((wiresFrom gs' w).getD (tl.getD t' 0) false)
              rw [hR' t' ht', hextU.wire_eq w hw _ (lt_of_lt_of_le (htl _ (getD_mem tl t' 0 ht')) (Nat.add_le_add_left (by omega) base))]
  exact fun l gs hlt => hmain l.length l rfl gs hlt

def adjCmpInv (base : ℕ) (gs : List Gate) (xs : List ℕ) :
    List Gate × List ℕ × (List Gate → List ℕ → List Gate × List ℕ) :=
  match xs with
  | [] => (gs, [], fun gs' _ => (gs', []))
  | e :: os =>
    let r := fixInnerInv base gs os
    let undo : List Gate → List ℕ → List Gate × List ℕ := fun gs' nout =>
      match nout with
      | ne :: nos =>
        let rU := r.2.2 gs' nos
        (rU.1, ne :: rU.2)
      | _ => (gs', [])
    (r.1, e :: r.2.1, undo)

lemma hinter_getD_even {α : Type*} (d : α) : ∀ (l1 l2 : List α) (t : ℕ),
    l1.length = l2.length → t < l1.length →
    (interleave l1 l2).getD (2 * t) d = l1.getD t d
  | [], _, _, _, ht => by simp at ht
  | _ :: _, [], _, hlen, _ => by simp at hlen
  | a :: _, _ :: _, 0, _, _ => rfl
  | _ :: l1, _ :: l2, t + 1, hlen, ht => by
    simp only [interleave, show 2 * (t + 1) = (2 * t) + 2 by omega]
    exact hinter_getD_even d l1 l2 t (by simp at hlen; omega) (by simp at ht; omega)

lemma hinter_getD_odd {α : Type*} (d : α) : ∀ (l1 l2 : List α) (t : ℕ),
    l1.length = l2.length → t < l2.length →
    (interleave l1 l2).getD (2 * t + 1) d = l2.getD t d
  | [], _, _, hlen, ht => by simp at hlen; omega
  | _ :: _, [], _, _, ht => by simp at ht
  | _ :: _, b :: _, 0, _, _ => rfl
  | _ :: l1, _ :: l2, t + 1, hlen, ht => by
    simp only [interleave, show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by omega]
    exact hinter_getD_odd d l1 l2 t (by simp at hlen; omega) (by simp at ht; omega)

lemma hevens_getD {α : Type*} (d : α) : ∀ (l : List α) (t : ℕ),
    2 * t < l.length → (evens l).getD t d = l.getD (2 * t) d
  | [], _, ht => by simp at ht
  | [_], t, ht => by simp at ht; subst ht; rfl
  | _ :: _ :: _, 0, _ => rfl
  | _ :: _ :: tl, t + 1, ht => by
    simp only [evens, show 2 * (t + 1) = (2 * t) + 2 by omega]
    exact hevens_getD d tl t (by simp at ht; omega)

lemma hodds_getD {α : Type*} (d : α) : ∀ (l : List α) (t : ℕ),
    2 * t + 1 < l.length → (odds l).getD t d = l.getD (2 * t + 1) d
  | [], _, ht => by simp at ht
  | [_], _, ht => by simp at ht
  | _ :: _ :: _, 0, _ => rfl
  | _ :: _ :: tl, t + 1, ht => by
    simp only [odds, show 2 * (t + 1) + 1 = (2 * t + 1) + 2 by omega]
    exact hodds_getD d tl t (by simp at ht; omega)

lemma arith_merge_fwd (k : ℕ) :
    2 * (k + 1) * 2 ^ k + 2 * (k + 1) * 2 ^ k + 2 * (2 ^ (k + 2) / 2) ≤ 2 * (k + 1 + 1) * 2 ^ (k + 1) := by
  have h1 : 2 ^ (k + 2) / 2 = 2 ^ (k + 1) := by rw [pow_succ]; omega
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h1, h2]; nlinarith

lemma arith_merge_bwd (k : ℕ) :
    4 * (2 ^ (k + 2) / 2) + 4 * (k + 1) * 2 ^ k + 4 * (k + 1) * 2 ^ k ≤ 4 * (k + 1 + 1) * 2 ^ (k + 1) := by
  have h1 : 2 ^ (k + 2) / 2 = 2 ^ (k + 1) := by rw [pow_succ]; omega
  have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [h1, h2]; nlinarith

lemma arith_sort_fwd (r : ℕ) :
    r * (r + 1) * 2 ^ r + r * (r + 1) * 2 ^ r + 2 * (r + 1) * 2 ^ r ≤ (r + 1) * (r + 1 + 1) * 2 ^ (r + 1) := by
  have h1 : r * (r + 1) + r * (r + 1) + 2 * (r + 1) ≤ (r + 1) * (r + 1 + 1) * 2 := by nlinarith
  calc r * (r + 1) * 2 ^ r + r * (r + 1) * 2 ^ r + 2 * (r + 1) * 2 ^ r
      = (r * (r + 1) + r * (r + 1) + 2 * (r + 1)) * 2 ^ r := by ring
    _ ≤ ((r + 1) * (r + 1 + 1) * 2) * 2 ^ r := Nat.mul_le_mul_right _ h1
    _ = (r + 1) * (r + 1 + 1) * 2 ^ (r + 1) := by rw [pow_succ]; ring

lemma arith_sort_bwd (r : ℕ) :
    4 * (r + 1) * 2 ^ r + 2 * r * (r + 1) * 2 ^ r + 2 * r * (r + 1) * 2 ^ r ≤
      2 * (r + 1) * (r + 1 + 1) * 2 ^ (r + 1) := by
  have h1 : 4 * (r + 1) + 2 * r * (r + 1) + 2 * r * (r + 1) ≤ 2 * (r + 1) * (r + 1 + 1) * 2 := by nlinarith
  calc 4 * (r + 1) * 2 ^ r + 2 * r * (r + 1) * 2 ^ r + 2 * r * (r + 1) * 2 ^ r
      = (4 * (r + 1) + 2 * r * (r + 1) + 2 * r * (r + 1)) * 2 ^ r := by ring
    _ ≤ (2 * (r + 1) * (r + 1 + 1) * 2) * 2 ^ r := Nat.mul_le_mul_right _ h1
    _ = 2 * (r + 1) * (r + 1 + 1) * 2 ^ (r + 1) := by rw [pow_succ]; ring

lemma adjCmpInv_spec (base : ℕ) (gs : List Gate) (xs : List ℕ)
    (hxs : ∀ i ∈ xs, i < base + gs.length) :
    let res := adjCmpInv base gs xs
    Extends base gs res.1 ∧
    res.2.1.length = xs.length ∧
    (∀ i ∈ res.2.1, i < base + res.1.length) ∧
    notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot res.1 ≤ nonNot gs + 2 * (xs.length / 2) ∧
    (∀ w, w.length = base →
      res.2.1.map (fun i => (wiresFrom res.1 w).getD i false) =
        adjCmpBool (xs.map (fun i => (wiresFrom gs w).getD i false))) ∧
    (∀ (gs' : List Gate) (nout : List ℕ),
      Extends base res.1 gs' → nout.length = res.2.1.length →
      (∀ u ∈ nout, u < base + gs'.length) →
      let ru := res.2.2 gs' nout
      Extends base gs' ru.1 ∧
      ru.2.length = xs.length ∧
      (∀ u ∈ ru.2, u < base + ru.1.length) ∧
      notCount ⟨ru.1, 0⟩ = notCount ⟨gs', 0⟩ ∧
      nonNot ru.1 ≤ nonNot gs' + 4 * (xs.length / 2) ∧
      ∀ w, w.length = base →
        (∀ t < res.2.1.length, (wiresFrom gs' w).getD (nout.getD t 0) false =
          !((wiresFrom gs' w).getD (res.2.1.getD t 0) false)) →
        ∀ t < xs.length, (wiresFrom ru.1 w).getD (ru.2.getD t 0) false =
          !((wiresFrom gs' w).getD (xs.getD t 0) false)) := by
  cases xs with
  | nil =>
    dsimp only [adjCmpInv]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by omega, (fun _ _ => rfl), ?_⟩
    intro gs' nout _ _ _
    refine ⟨Extends.refl base gs', rfl, (fun _ h => by cases h), rfl, by omega, (fun _ _ _ t ht => by change t < 0 at ht; omega)⟩
  | cons e os =>
    dsimp only [adjCmpInv]
    have he : e < base + gs.length := hxs e (List.mem_cons_self ..)
    have hos : ∀ i ∈ os, i < base + gs.length := fun i hi => hxs i (List.mem_cons_of_mem _ hi)
    have hr := fixInnerInv_spec base os gs hos
    set r := fixInnerInv base gs os with hrr
    rcases hr with ⟨hext, hlen, hlt, hnc, hnn, hval, hundo⟩
    have hgl := hext.length_le
    have hhalf : os.length / 2 ≤ (e :: os).length / 2 := by simp; omega
    refine ⟨hext, by simp [hlen], ?_, hnc, by omega, ?_, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt i hi
    · intro w hw
      simp only [List.map_cons, adjCmpBool, hext.wire_eq w hw e he, hval w hw]
    · intro gs' nout hext' hlen' hnout'
      rcases nout with _ | ⟨ne, nos⟩ <;> try (simp [hlen] at hlen'; done)
      have hne : ne < base + gs'.length := hnout' ne (List.mem_cons_self ..)
      have hnos : ∀ u ∈ nos, u < base + gs'.length := fun u hu => hnout' u (List.mem_cons_of_mem _ hu)
      have hnos_len : nos.length = os.length := by simp [hlen] at hlen'; exact hlen'
      have hu := hundo gs' nos hext' (by rw [hlen]; exact hnos_len) hnos
      set ru := r.2.2 gs' nos with hru
      rcases hu with ⟨hextU, hlenU, hltU, hncU, hnnU, hvalU⟩
      have hglU := hextU.length_le
      dsimp only
      have hlen_ru : (ne :: ru.2).length = (e :: os).length := by simp [hlenU]
      have hnn_ru : nonNot ru.1 ≤ nonNot gs' + 4 * ((e :: os).length / 2) := by
        dsimp only [nonNot] at hnnU ⊢; omega
      refine ⟨hextU, hlen_ru, ?_, hncU, hnn_ru, ?_⟩
      · intro u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact lt_of_lt_of_le hne (Nat.add_le_add_left hglU base)
        · exact hltU u hu
      · intro w hw hneg t ht
        cases t with
        | zero =>
          change (wiresFrom ru.1 w).getD ne false = !((wiresFrom gs' w).getD e false)
          rw [hextU.wire_eq w hw ne hne]
          have h0 := hneg 0 (by simp)
          change (wiresFrom gs' w).getD ne false = !((wiresFrom gs' w).getD e false) at h0
          rw [h0]
        | succ t' =>
          have ht' : t' < os.length := by simp at ht; omega
          have hneg' : ∀ s < r.2.1.length, (wiresFrom gs' w).getD (nos.getD s 0) false =
              !((wiresFrom gs' w).getD (r.2.1.getD s 0) false) := fun s hs => hneg (s + 1) (by simp; exact hs)
          exact hvalU w hw hneg' t' ht'

def oeMergeInv (base : ℕ) : ℕ → List Gate → List ℕ → List ℕ →
    List Gate × List ℕ × (List Gate → List ℕ → List Gate × List ℕ × List ℕ)
  | 0, gs, a :: _, b :: _ =>
    let rC := cmpPair base gs a b
    let undo : List Gate → List ℕ → List Gate × List ℕ × List ℕ := fun gs' nout =>
      match nout with
      | nhi :: nlo :: _ =>
        let rU := uncmpPair base gs' a b nhi nlo
        (rU.1, [rU.2.1], [rU.2.2])
      | _ => (gs', [], [])
    (rC.1, [rC.2.1, rC.2.2], undo)
  | 0, gs, as, bs => (gs, as ++ bs, fun gs' _ => (gs', [], []))
  | k + 1, gs, as, bs =>
    let rE := oeMergeInv base k gs (evens as) (evens bs)
    let rO := oeMergeInv base k rE.1 (odds as) (odds bs)
    let inter := interleave rE.2.1 rO.2.1
    let rA := adjCmpInv base rO.1 inter
    let undo : List Gate → List ℕ → List Gate × List ℕ × List ℕ := fun gs' nout =>
      let rU_A := rA.2.2 gs' nout
      let nE := evens rU_A.2
      let nO := odds rU_A.2
      let rU_O := rO.2.2 rU_A.1 nO
      let rU_E := rE.2.2 rU_O.1 nE
      (rU_E.1, interleave rU_E.2.1 rU_O.2.1, interleave rU_E.2.2 rU_O.2.2)
    (rA.1, rA.2.1, undo)

lemma oeMergeInv_spec (base : ℕ) :
    ∀ (k : ℕ) (gs : List Gate) (as bs : List ℕ),
      as.length = 2 ^ k → bs.length = 2 ^ k →
      (∀ i ∈ as, i < base + gs.length) → (∀ i ∈ bs, i < base + gs.length) →
      let res := oeMergeInv base k gs as bs
      Extends base gs res.1 ∧
      res.2.1.length = 2 ^ (k + 1) ∧
      (∀ i ∈ res.2.1, i < base + res.1.length) ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot res.1 ≤ nonNot gs + 2 * (k + 1) * 2 ^ k ∧
      (∀ w, w.length = base →
        res.2.1.map (fun i => (wiresFrom res.1 w).getD i false) =
          oeMergeBool k (as.map (fun i => (wiresFrom gs w).getD i false))
                        (bs.map (fun i => (wiresFrom gs w).getD i false))) ∧
      (∀ (gs' : List Gate) (nout : List ℕ),
        Extends base res.1 gs' → nout.length = 2 ^ (k + 1) →
        (∀ u ∈ nout, u < base + gs'.length) →
        let ru := res.2.2 gs' nout
        Extends base gs' ru.1 ∧
        ru.2.1.length = 2 ^ k ∧ ru.2.2.length = 2 ^ k ∧
        (∀ u ∈ ru.2.1, u < base + ru.1.length) ∧
        (∀ u ∈ ru.2.2, u < base + ru.1.length) ∧
        notCount ⟨ru.1, 0⟩ = notCount ⟨gs', 0⟩ ∧
        nonNot ru.1 ≤ nonNot gs' + 4 * (k + 1) * 2 ^ k ∧
        ∀ w, w.length = base →
          (∀ t < 2 ^ (k + 1), (wiresFrom gs' w).getD (nout.getD t 0) false =
            !((wiresFrom gs' w).getD (res.2.1.getD t 0) false)) →
          (∀ t < 2 ^ k, (wiresFrom ru.1 w).getD (ru.2.1.getD t 0) false =
            !((wiresFrom gs' w).getD (as.getD t 0) false)) ∧
          (∀ t < 2 ^ k, (wiresFrom ru.1 w).getD (ru.2.2.getD t 0) false =
            !((wiresFrom gs' w).getD (bs.getD t 0) false))) := by
  intro k
  induction k with
  | zero =>
    intro gs as bs ha hb has hbs
    obtain ⟨a, as', rfl⟩ : ∃ a as', as = a :: as' := by
      cases as with | nil => simp at ha | cons a as' => exact ⟨a, as', rfl⟩
    obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with | nil => simp at hb | cons b bs' => exact ⟨b, bs', rfl⟩
    have has' : as' = [] := List.eq_nil_of_length_eq_zero (by rw [pow_zero, List.length_cons] at ha; omega)
    have hbs' : bs' = [] := List.eq_nil_of_length_eq_zero (by rw [pow_zero, List.length_cons] at hb; omega)
    subst has' hbs'
    dsimp only [oeMergeInv]
    have ha0 : a < base + gs.length := has a (List.mem_cons_self ..)
    have hb0 : b < base + gs.length := hbs b (List.mem_cons_self ..)
    set rC := cmpPair base gs a b with hrC
    have hC := cmpPair_spec base gs a b ha0 hb0
    rw [← hrC] at hC
    rcases hC with ⟨hextC, hltC1, hltC2, hncC, hnnC, hvalC⟩
    refine ⟨hextC, rfl, ?_, hncC, by simp; omega, ?_, ?_⟩
    · intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption
    · intro w hw
      simp only [List.map_cons, List.map_nil, oeMergeBool]
      rw [(hvalC w hw).1, (hvalC w hw).2]
    · intro gs' nout hext' hlen' hnout'
      rcases nout with _ | ⟨nhi, _ | ⟨nlo, ntl⟩⟩ <;> try (simp at hlen'; done)
      have hnhi : nhi < base + gs'.length := hnout' nhi (List.mem_cons_self ..)
      have hnlo : nlo < base + gs'.length := hnout' nlo (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hglC := hextC.length_le
      have hgl' := hext'.length_le
      have hntl_len : ntl.length = 0 := by simp only [List.length_cons, pow_succ, pow_zero] at hlen'; omega
      have hntl_nil : ntl = [] := List.eq_nil_of_length_eq_zero hntl_len
      subst hntl_nil
      dsimp only
      set rU := uncmpPair base gs' a b nhi nlo with hrU
      have hU := uncmpPair_spec base gs' a b nhi nlo (by omega) (by omega) hnhi hnlo
      rw [← hrU] at hU
      rcases hU with ⟨hextU, hltU1, hltU2, hncU, hnnU, hvalU⟩
      refine ⟨hextU, rfl, rfl, fun u hu => by simp at hu; subst hu; exact hltU1,
        fun u hu => by simp at hu; subst hu; exact hltU2, hncU,
        by dsimp only [nonNot] at hnnU ⊢; simp; omega, ?_⟩
      intro w hw hneg
      have hextG' : Extends base gs gs' := hextC.trans hext'
      have h_nhi : (wiresFrom gs' w).getD nhi false =
          !((wiresFrom gs' w).getD a false || (wiresFrom gs' w).getD b false) := by
        have h0 := hneg 0 (by simp)
        change (wiresFrom gs' w).getD nhi false = !((wiresFrom gs' w).getD rC.2.1 false) at h0
        rw [h0, hext'.wire_eq w hw _ hltC1, (hvalC w hw).1,
            hextG'.wire_eq w hw a ha0, hextG'.wire_eq w hw b hb0]
      have h_nlo : (wiresFrom gs' w).getD nlo false =
          !((wiresFrom gs' w).getD a false && (wiresFrom gs' w).getD b false) := by
        have h1 := hneg 1 (by simp)
        change (wiresFrom gs' w).getD nlo false = !((wiresFrom gs' w).getD rC.2.2 false) at h1
        rw [h1, hext'.wire_eq w hw _ hltC2, (hvalC w hw).2,
            hextG'.wire_eq w hw a ha0, hextG'.wire_eq w hw b hb0]
      obtain ⟨hua, hub⟩ := hvalU w hw h_nhi h_nlo
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · have : t = 0 := by simp at ht; omega
        subst this; exact hua
      · have : t = 0 := by simp at ht; omega
        subst this; exact hub
  | succ k ih =>
    intro gs as bs ha hb has hbs
    dsimp only [oeMergeInv]
    have hae_len : (evens as).length = 2 ^ k := by rw [evens_length, ha, pow_succ]; omega
    have hao_len : (odds as).length = 2 ^ k := by rw [odds_length, ha, pow_succ]; omega
    have hbe_len : (evens bs).length = 2 ^ k := by rw [evens_length, hb, pow_succ]; omega
    have hbo_len : (odds bs).length = 2 ^ k := by rw [odds_length, hb, pow_succ]; omega
    set rE := oeMergeInv base k gs (evens as) (evens bs) with hrE
    have hE := ih gs (evens as) (evens bs) hae_len hbe_len
      (fun i hi => has i (evens_mem hi)) (fun i hi => hbs i (evens_mem hi))
    rw [← hrE] at hE
    rcases hE with ⟨hextE, hlenE, hltE, hncE, hnnE, hvalE, hundoE⟩
    have hglE := hextE.length_le
    set rO := oeMergeInv base k rE.1 (odds as) (odds bs) with hrO
    have hO := ih rE.1 (odds as) (odds bs) hao_len hbo_len
      (fun i hi => lt_of_lt_of_le (has i (odds_mem hi)) (Nat.add_le_add_left hglE base))
      (fun i hi => lt_of_lt_of_le (hbs i (odds_mem hi)) (Nat.add_le_add_left hglE base))
    rw [← hrO] at hO
    rcases hO with ⟨hextO, hlenO, hltO, hncO, hnnO, hvalO, hundoO⟩
    have hglO := hextO.length_le
    set inter := interleave rE.2.1 rO.2.1
    have hinter_len : inter.length = 2 ^ (k + 2) := by
      rw [interleave_length, hlenE, hlenO, pow_succ]; ring
    have hinter_lt : ∀ i ∈ inter, i < base + rO.1.length := fun i hi => by
      rcases interleave_mem hi with hi1 | hi2
      · exact lt_of_lt_of_le (hltE i hi1) (Nat.add_le_add_left hglO base)
      · exact hltO i hi2
    set rA := adjCmpInv base rO.1 inter with hrA
    have hA := adjCmpInv_spec base rO.1 inter hinter_lt
    rw [← hrA] at hA
    rcases hA with ⟨hextA, hlenA, hltA, hncA, hnnA, hvalA, hundoA⟩
    have hextEOA := (hextE.trans hextO).trans hextA
    have hpow2 : 2 ^ (k + 1 + 1) = 2 ^ (k + 2) := rfl
    have hpow_arith : 2 * (k + 1) * 2 ^ k + 2 * (k + 1) * 2 ^ k + 2 * (2 ^ (k + 2) / 2) ≤
        2 * (k + 1 + 1) * 2 ^ (k + 1) := by
      have h1 : 2 ^ (k + 2) / 2 = 2 ^ (k + 1) := by rw [pow_succ]; omega
      have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      rw [h1, h2]
      nlinarith
    refine ⟨hextEOA, by omega, hltA, by omega, by omega, ?_, ?_⟩
    · intro w hw
      rw [hvalA w hw]
      have hinter_map : inter.map (fun i => (wiresFrom rO.1 w).getD i false) =
          interleave (rE.2.1.map fun i => (wiresFrom rE.1 w).getD i false)
                     (rO.2.1.map fun i => (wiresFrom rO.1 w).getD i false) := by
        dsimp only [inter]
        rw [← interleave_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hextO.wire_eq w hw i (hltE i hi)
      rw [hinter_map, hvalE w hw, hvalO w hw]
      dsimp only [oeMergeBool]
      have hm1 : List.map (fun i => (wiresFrom gs w).getD i false) (evens as) =
          evens (List.map (fun i => (wiresFrom gs w).getD i false) as) := by
        rw [evens_map]
      have hm2 : List.map (fun i => (wiresFrom gs w).getD i false) (evens bs) =
          evens (List.map (fun i => (wiresFrom gs w).getD i false) bs) := by
        rw [evens_map]
      have hm3 : List.map (fun i => (wiresFrom rE.1 w).getD i false) (odds as) =
          odds (List.map (fun i => (wiresFrom gs w).getD i false) as) := by
        rw [odds_map]; apply List.map_congr_left; intro i hi; exact hextE.wire_eq w hw i (has i (odds_mem hi))
      have hm4 : List.map (fun i => (wiresFrom rE.1 w).getD i false) (odds bs) =
          odds (List.map (fun i => (wiresFrom gs w).getD i false) bs) := by
        rw [odds_map]; apply List.map_congr_left; intro i hi; exact hextE.wire_eq w hw i (hbs i (odds_mem hi))
      rw [hm1, hm2, hm3, hm4]
    · intro gs' nout hext' hlen' hnout'
      set rUA := rA.2.2 gs' nout with hrUA
      have hUA := hundoA gs' nout hext' (by omega) hnout'
      rw [← hrUA] at hUA
      rcases hUA with ⟨hextUA, hlenUA, hltUA, hncUA, hnnUA, hvalUA⟩
      have hnE_len : (evens rUA.2).length = 2 ^ (k + 1) := by rw [evens_length, hlenUA, hinter_len, pow_succ]; omega
      have hnO_len : (odds rUA.2).length = 2 ^ (k + 1) := by rw [odds_length, hlenUA, hinter_len, pow_succ]; omega
      have hextO_UA : Extends base rO.1 rUA.1 := hextA.trans (hext'.trans hextUA)
      set rUO := rO.2.2 rUA.1 (odds rUA.2) with hrUO
      have hUO := hundoO rUA.1 (odds rUA.2) hextO_UA hnO_len (fun u hu => hltUA u (odds_mem hu))
      rw [← hrUO] at hUO
      rcases hUO with ⟨hextUO, hlenUO1, hlenUO2, hltUO1, hltUO2, hncUO, hnnUO, hvalUO⟩
      have hglUO := hextUO.length_le
      have hextE_UO : Extends base rE.1 rUO.1 := hextO.trans (hextO_UA.trans hextUO)
      set rUE := rE.2.2 rUO.1 (evens rUA.2) with hrUE
      have hUE := hundoE rUO.1 (evens rUA.2) hextE_UO hnE_len (fun u hu => lt_of_lt_of_le (hltUA u (evens_mem hu)) (Nat.add_le_add_left hglUO base))
      rw [← hrUE] at hUE
      rcases hUE with ⟨hextUE, hlenUE1, hlenUE2, hltUE1, hltUE2, hncUE, hnnUE, hvalUE⟩
      have hglUE := hextUE.length_le
      have hpow_bwd := arith_merge_bwd k
      refine ⟨(hextUA.trans hextUO).trans hextUE,
        by rw [interleave_length, hlenUE1, hlenUO1, pow_succ]; ring,
        by rw [interleave_length, hlenUE2, hlenUO2, pow_succ]; ring,
        fun u hu => by
          rcases interleave_mem hu with h1 | h2
          · exact hltUE1 u h1
          · exact lt_of_lt_of_le (hltUO1 u h2) (Nat.add_le_add_left hglUE base),
        fun u hu => by
          rcases interleave_mem hu with h1 | h2
          · exact hltUE2 u h1
          · exact lt_of_lt_of_le (hltUO2 u h2) (Nat.add_le_add_left hglUE base),
        by omega, by omega, ?_⟩

      intro w hw hneg
      have hnegA := hvalUA w hw (fun t ht => hneg t (by omega))
      have hnegO : ∀ t < 2 ^ (k + 1), (wiresFrom rUA.1 w).getD ((odds rUA.2).getD t 0) false =
          !((wiresFrom rUA.1 w).getD (rO.2.1.getD t 0) false) := by
        intro t ht
        rw [hodds_getD 0 rUA.2 t (by rw [hlenUA, hinter_len, pow_succ]; omega)]
        rw [hnegA (2 * t + 1) (by rw [hinter_len, pow_succ]; omega)]
        have hi : inter.getD (2 * t + 1) 0 = rO.2.1.getD t 0 :=
          hinter_getD_odd 0 rE.2.1 rO.2.1 t (by omega) (by omega)
        rw [hi]
        have hgl' := hext'.length_le
        have hglA := hextA.length_le
        have hltO_t : rO.2.1.getD t 0 < base + rO.1.length := hltO _ (getD_mem rO.2.1 t 0 (by omega))
        rw [hextUA.wire_eq w hw _ (by omega)]
      have hUO' := hvalUO w hw hnegO
      have hnegE : ∀ t < 2 ^ (k + 1), (wiresFrom rUO.1 w).getD ((evens rUA.2).getD t 0) false =
          !((wiresFrom rUO.1 w).getD (rE.2.1.getD t 0) false) := by
        intro t ht
        rw [hevens_getD 0 rUA.2 t (by rw [hlenUA, hinter_len, pow_succ]; omega)]
        rw [hextUO.wire_eq w hw _ (hltUA _ (getD_mem rUA.2 (2 * t) 0 (by rw [hlenUA, hinter_len, pow_succ]; omega)))]
        rw [hnegA (2 * t) (by rw [hinter_len, pow_succ]; omega)]
        have hi : inter.getD (2 * t) 0 = rE.2.1.getD t 0 :=
          hinter_getD_even 0 rE.2.1 rO.2.1 t (by omega) (by omega)
        rw [hi]
        have hgl' := hext'.length_le

        have hlt_e_val : rE.2.1.getD t 0 < base + rE.1.length := hltE _ (getD_mem rE.2.1 t 0 (by omega))
        have h1 : (wiresFrom rUO.1 w).getD (rE.2.1.getD t 0) false = (wiresFrom rE.1 w).getD (rE.2.1.getD t 0) false :=
          hextE_UO.wire_eq w hw _ hlt_e_val
        have h2 : (wiresFrom gs' w).getD (rE.2.1.getD t 0) false = (wiresFrom rE.1 w).getD (rE.2.1.getD t 0) false :=
          (hextO.trans (hextA.trans hext')).wire_eq w hw _ hlt_e_val
        rw [h1, h2]
      have hUE' := hvalUE w hw hnegE

      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rcases Nat.even_or_odd' t with ⟨q, rfl | rfl⟩
        · rw [hinter_getD_even 0 rUE.2.1 rUO.2.1 q (by omega) (by omega)]
          rw [hUE'.1 q (by omega)]
          rw [hevens_getD 0 as q (by rw [ha, pow_succ]; omega)]
          rw [hextUO.wire_eq w hw _ (lt_of_lt_of_le (has _ (getD_mem as (2 * q) 0 (by omega))) (by have := hextE.length_le; have := hextO.length_le; have := hextA.length_le; have := hext'.length_le; have := hextUA.length_le; omega))]
          rw [hextUA.wire_eq w hw _ (lt_of_lt_of_le (has _ (getD_mem as (2 * q) 0 (by omega))) (by have := hextE.length_le; have := hextO.length_le; have := hextA.length_le; have := hext'.length_le; omega))]
        · rw [hinter_getD_odd 0 rUE.2.1 rUO.2.1 q (by omega) (by omega)]
          rw [hextUE.wire_eq w hw _ (hltUO1 _ (getD_mem rUO.2.1 q 0 (by omega)))]
          rw [hUO'.1 q (by omega)]
          rw [hodds_getD 0 as q (by rw [ha, pow_succ]; omega)]
          rw [hextUA.wire_eq w hw _ (lt_of_lt_of_le (has _ (getD_mem as (2 * q + 1) 0 (by omega))) (by have := hextE.length_le; have := hextO.length_le; have := hextA.length_le; have := hext'.length_le; omega))]
      · rcases Nat.even_or_odd' t with ⟨q, rfl | rfl⟩
        · rw [hinter_getD_even 0 rUE.2.2 rUO.2.2 q (by omega) (by omega)]
          rw [hUE'.2 q (by omega)]
          rw [hevens_getD 0 bs q (by rw [hb, pow_succ]; omega)]
          rw [hextUO.wire_eq w hw _ (lt_of_lt_of_le (hbs _ (getD_mem bs (2 * q) 0 (by omega))) (by have := hextE.length_le; have := hextO.length_le; have := hextA.length_le; have := hext'.length_le; have := hextUA.length_le; omega))]
          rw [hextUA.wire_eq w hw _ (lt_of_lt_of_le (hbs _ (getD_mem bs (2 * q) 0 (by omega))) (by have := hextE.length_le; have := hextO.length_le; have := hextA.length_le; have := hext'.length_le; omega))]
        · rw [hinter_getD_odd 0 rUE.2.2 rUO.2.2 q (by omega) (by omega)]
          rw [hextUE.wire_eq w hw _ (hltUO2 _ (getD_mem rUO.2.2 q 0 (by omega)))]
          rw [hUO'.2 q (by omega)]
          rw [hodds_getD 0 bs q (by rw [hb, pow_succ]; omega)]
          rw [hextUA.wire_eq w hw _ (lt_of_lt_of_le (hbs _ (getD_mem bs (2 * q + 1) 0 (by omega))) (by have := hextE.length_le; have := hextO.length_le; have := hextA.length_le; have := hext'.length_le; omega))]

def oeSortInv (base : ℕ) : ℕ → List Gate → List ℕ →
    List Gate × List ℕ × (List Gate → List ℕ → List Gate × List ℕ)
  | 0, gs, xs => (gs, xs, fun gs' nxs => (gs', nxs))
  | r + 1, gs, xs =>
    let half := 2 ^ r
    let s1 := oeSortInv base r gs (xs.take half)
    let s2 := oeSortInv base r s1.1 (xs.drop half)
    let mrg := oeMergeInv base r s2.1 s1.2.1 s2.2.1
    let undo : List Gate → List ℕ → List Gate × List ℕ := fun gs' nout =>
      let rm := mrg.2.2 gs' nout
      let rs2 := s2.2.2 rm.1 rm.2.2
      let rs1 := s1.2.2 rs2.1 rm.2.1
      (rs1.1, rs1.2 ++ rs2.2)
    (mrg.1, mrg.2.1, undo)

lemma oeSortInv_spec (base : ℕ) :
    ∀ (r : ℕ) (gs : List Gate) (xs : List ℕ),
      xs.length = 2 ^ r →
      (∀ i ∈ xs, i < base + gs.length) →
      let res := oeSortInv base r gs xs
      Extends base gs res.1 ∧
      res.2.1.length = 2 ^ r ∧
      (∀ i ∈ res.2.1, i < base + res.1.length) ∧
      notCount ⟨res.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot res.1 ≤ nonNot gs + r * (r + 1) * 2 ^ r ∧
      (∀ w, w.length = base →
        res.2.1.map (fun i => (wiresFrom res.1 w).getD i false) =
          oeSortBool r (xs.map (fun i => (wiresFrom gs w).getD i false))) ∧
      (∀ (gs' : List Gate) (nout : List ℕ),
        Extends base res.1 gs' → nout.length = 2 ^ r →
        (∀ u ∈ nout, u < base + gs'.length) →
        let ru := res.2.2 gs' nout
        Extends base gs' ru.1 ∧
        ru.2.length = 2 ^ r ∧
        (∀ u ∈ ru.2, u < base + ru.1.length) ∧
        notCount ⟨ru.1, 0⟩ = notCount ⟨gs', 0⟩ ∧
        nonNot ru.1 ≤ nonNot gs' + 2 * r * (r + 1) * 2 ^ r ∧
        ∀ w, w.length = base →
          (∀ t < 2 ^ r, (wiresFrom gs' w).getD (nout.getD t 0) false =
            !((wiresFrom gs' w).getD (res.2.1.getD t 0) false)) →
          ∀ t < 2 ^ r, (wiresFrom ru.1 w).getD (ru.2.getD t 0) false =
            !((wiresFrom gs' w).getD (xs.getD t 0) false)) := by
  intro r
  induction r with
  | zero =>
    intro gs xs hlen hxs
    dsimp only [oeSortInv]
    refine ⟨Extends.refl base gs, hlen, hxs, rfl, by simp, fun _ _ => rfl, ?_⟩
    intro gs' nout _ hlen' hnout'
    refine ⟨Extends.refl base gs', hlen', hnout', rfl, by simp, ?_⟩
    intro w hw hneg t ht
    exact hneg t ht
  | succ r ih =>
    intro gs xs hlen hxs
    dsimp only [oeSortInv]
    have hlen1 : (xs.take (2 ^ r)).length = 2 ^ r := by rw [List.length_take, hlen, pow_succ]; omega
    have hlen2 : (xs.drop (2 ^ r)).length = 2 ^ r := by rw [List.length_drop, hlen, pow_succ]; omega
    set s1 := oeSortInv base r gs (xs.take (2 ^ r)) with hs1
    have h1 := ih gs (xs.take (2 ^ r)) hlen1 (fun i hi => hxs i (List.mem_of_mem_take hi))
    rw [← hs1] at h1
    rcases h1 with ⟨hext1, hlenS1, hltS1, hncS1, hnnS1, hvalS1, hundoS1⟩
    have hgl1 := hext1.length_le
    set s2 := oeSortInv base r s1.1 (xs.drop (2 ^ r)) with hs2
    have h2 := ih s1.1 (xs.drop (2 ^ r)) hlen2 (fun i hi => lt_of_lt_of_le (hxs i (List.mem_of_mem_drop hi)) (Nat.add_le_add_left hgl1 base))
    rw [← hs2] at h2
    rcases h2 with ⟨hext2, hlenS2, hltS2, hncS2, hnnS2, hvalS2, hundoS2⟩
    have hgl2 := hext2.length_le
    set mrg := oeMergeInv base r s2.1 s1.2.1 s2.2.1 with hmrg
    have hm := oeMergeInv_spec base r s2.1 s1.2.1 s2.2.1 hlenS1 hlenS2
      (fun i hi => lt_of_lt_of_le (hltS1 i hi) (Nat.add_le_add_left hgl2 base)) hltS2
    rw [← hmrg] at hm
    rcases hm with ⟨hextM, hlenM, hltM, hncM, hnnM, hvalM, hundoM⟩
    have hpow2 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ]; ring
    have h_nn_fwd := arith_sort_fwd r
    refine ⟨(hext1.trans hext2).trans hextM, hlenM, hltM, by omega, by omega, ?_, ?_⟩
    · intro w hw
      rw [hvalM w hw]
      have hs1_map : s1.2.1.map (fun i => (wiresFrom s2.1 w).getD i false) =
          oeSortBool r ((xs.take (2 ^ r)).map (fun i => (wiresFrom gs w).getD i false)) := by
        rw [← hvalS1 w hw]
        apply List.map_congr_left
        intro i hi
        exact hext2.wire_eq w hw i (hltS1 i hi)
      have hs2_map : s2.2.1.map (fun i => (wiresFrom s2.1 w).getD i false) =
          oeSortBool r ((xs.drop (2 ^ r)).map (fun i => (wiresFrom gs w).getD i false)) := by
        rw [hvalS2 w hw]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact hext1.wire_eq w hw i (hxs i (List.mem_of_mem_drop hi))
      rw [hs1_map, hs2_map]
      dsimp only [oeSortBool]
      rw [List.map_take, List.map_drop]
    · intro gs' nout hext' hlen' hnout'
      set rm := mrg.2.2 gs' nout with hrm
      have hm' := hundoM gs' nout hext' hlen' hnout'
      rw [← hrm] at hm'
      rcases hm' with ⟨hextUM, hlenUM1, hlenUM2, hltUM1, hltUM2, hncUM, hnnUM, hvalUM⟩
      have hglUM := hextUM.length_le
      set rs2 := s2.2.2 rm.1 rm.2.2 with hrs2
      have hU2 := hundoS2 rm.1 rm.2.2 (hextM.trans (hext'.trans hextUM)) hlenUM2 hltUM2
      rw [← hrs2] at hU2
      rcases hU2 with ⟨hextUS2, hlenUS2, hltUS2, hncUS2, hnnUS2, hvalUS2⟩
      have hglUS2 := hextUS2.length_le
      set rs1 := s1.2.2 rs2.1 rm.2.1 with hrs1
      have hU1 := hundoS1 rs2.1 rm.2.1 ((hext2.trans hextM).trans ((hext'.trans hextUM).trans hextUS2))
        hlenUM1 (fun u hu => lt_of_lt_of_le (hltUM1 u hu) (Nat.add_le_add_left hglUS2 base))
      rw [← hrs1] at hU1
      rcases hU1 with ⟨hextUS1, hlenUS1, hltUS1, hncUS1, hnnUS1, hvalUS1⟩
      have hglUS1 := hextUS1.length_le
      have h_nn_bwd := arith_sort_bwd r
      refine ⟨(hextUM.trans hextUS2).trans hextUS1, by rw [List.length_append, hlenUS1, hlenUS2, hpow2]; omega,
        fun u hu => by
          rcases List.mem_append.mp hu with h1 | h2
          · exact hltUS1 u h1
          · exact lt_of_lt_of_le (hltUS2 u h2) (Nat.add_le_add_left hglUS1 base),
        by omega, by omega, ?_⟩
      intro w hw hneg t ht
      have hUM_neg := hvalUM w hw hneg
      have hnegS2 : ∀ s < 2 ^ r, (wiresFrom rm.1 w).getD (rm.2.2.getD s 0) false =
          !((wiresFrom rm.1 w).getD (s2.2.1.getD s 0) false) := by
        intro s hs
        rw [hUM_neg.2 s hs]
        rw [hextUM.wire_eq w hw _ (by have := hltS2 _ (getD_mem s2.2.1 s 0 (by omega)); have := hextM.length_le; have := hext'.length_le; omega)]
      have hUS2' := hvalUS2 w hw hnegS2
      have hnegS1 : ∀ s < 2 ^ r, (wiresFrom rs2.1 w).getD (rm.2.1.getD s 0) false =
          !((wiresFrom rs2.1 w).getD (s1.2.1.getD s 0) false) := by
        intro s hs
        rw [hextUS2.wire_eq w hw _ (hltUM1 _ (getD_mem rm.2.1 s 0 (by omega))), hUM_neg.1 s hs]
        have hlt_s1 : s1.2.1.getD s 0 < base + mrg.1.length := by
          have := hltS1 _ (getD_mem s1.2.1 s 0 (by omega)); have := hextM.length_le; omega
        have hext_gs_rs2 : Extends base s1.1 rs2.1 := (hext2.trans hextM).trans (hext'.trans (hextUM.trans hextUS2))
        have hext_gs_gs' : Extends base s1.1 gs' := (hext2.trans hextM).trans hext'
        have hlt_s1_base : s1.2.1.getD s 0 < base + s1.1.length := hltS1 _ (getD_mem s1.2.1 s 0 (by omega))
        rw [hext_gs_rs2.wire_eq w hw _ hlt_s1_base, hext_gs_gs'.wire_eq w hw _ hlt_s1_base]
      have hUS1' := hvalUS1 w hw hnegS1
      by_cases ht1 : t < 2 ^ r
      · rw [getD_append_left _ _ t 0 (by omega), hUS1' t ht1, getD_take xs (2 ^ r) t 0 ht1]
        have hext_21 : Extends base gs' rs2.1 := hextUM.trans hextUS2
        rw [hext_21.wire_eq w hw _ (lt_of_lt_of_le (hxs _ (getD_mem xs t 0 (by omega)))
          (by have := hext1.length_le; have := hext2.length_le; have := hextM.length_le; have := hext'.length_le; omega))]
      · have ht2 : t - 2 ^ r < 2 ^ r := by rw [hpow2] at ht; omega
        rw [getD_append_right _ _ t 0 (by omega), hlenUS1, hextUS1.wire_eq w hw _ (hltUS2 _ (getD_mem rs2.2 (t - 2 ^ r) 0 (by omega))),
            hUS2' (t - 2 ^ r) ht2, getD_drop xs (2 ^ r) (t - 2 ^ r) 0,
            show 2 ^ r + (t - 2 ^ r) = t by omega]
        rw [hextUM.wire_eq w hw _ (lt_of_lt_of_le (hxs _ (getD_mem xs t 0 (by omega)))
          (by have := hext1.length_le; have := hext2.length_le; have := hextM.length_le; have := hext'.length_le; omega))]

lemma getD_map_eq {α β : Type*} (f : α → β) (l : List α) (i : ℕ) (d1 : α) (d2 : β)
    (hi : i < l.length) : (l.map f).getD i d2 = f (l.getD i d1) := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma conjunct2_proof (a n : ℕ) (R : Finset (Fin n) → ℕ)
    (hn : n ≤ 2 ^ a) (hcard : ∀ x, R x ≤ x.card) :
    let h := 2 ^ a
    let b := a + 1
    let d := R Finset.univ
    let m := 2 * h - 1 - d
    let N := n + m
    ∃ C : Circuit,
      (FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size) ∧
      (∃ (old : Fin n → Fin (N + 2 + C.size)) (pad : Fin m → Fin (N + 2 + C.size)),
        ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
          let w := C.wires (pairVec n m x z)
          (∀ i, R x < R (insert i x) → w.getD (old i).val false = true) ∧
          (∀ i ∈ x, w.getD (old i).val false = false) ∧
          (∀ j, w.getD (pad j).val false = decide (j ∉ z))) ∧
      notCount C = b + 1 ∧
      C.size ≤ 48 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by
  intro h b d m N
  let base := N + 2
  let zeroWire := N
  let oneWire := N + 1
  have hd_le_n : d ≤ n := by simpa [d] using hcard Finset.univ
  have h_pos : 1 ≤ h := Nat.one_le_two_pow
  have hN_pos : 1 ≤ N := by omega
  have hN_lt : N < 2 ^ (b + 1) := by
    have hb1 : 2 ^ (b + 1) = 4 * h := by dsimp only [b, h]; rw [pow_succ, pow_succ]; ring
    omega
  have ha_le_log : a ≤ Nat.log2 (N + 2) := by
    by_cases ha0 : a = 0
    · subst ha0; exact Nat.zero_le _
    · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha0
      have hh2 : 2 ≤ h := by
        have : 2 ^ 1 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha1
        simpa [h] using this
      have hpow_le : 2 ^ a ≤ N + 2 := by omega
      exact (Nat.le_log2 (by omega)).mpr hpow_le
  let r := Nat.log2 N + 1
  have hr_pow_gt : N < 2 ^ r := Nat.lt_log2_self
  have hr_pow_le : 2 ^ r ≤ 2 * N := by
    dsimp only [r]
    rw [pow_succ]
    have hlog := Nat.log2_self_le (by omega : N ≠ 0)
    omega
  have hr_le_log : r ≤ Nat.log2 (N + 2) + 1 := by
    have : Nat.log2 N ≤ Nat.log2 (N + 2) := (Nat.le_log2 (by omega)).mpr (le_trans (Nat.log2_self_le (by omega)) (by omega))
    omega
  let xs := List.range N ++ List.replicate (2 ^ r - N) zeroWire
  have hxs_len : xs.length = 2 ^ r := by simp [xs, List.length_range]; omega
  have hxs_lt : ∀ i ∈ xs, i < base := by
    intro i hi
    simp only [xs, List.mem_append, List.mem_range, List.mem_replicate] at hi
    rcases hi with hi | ⟨_, rfl⟩ <;> omega
  let rS := oeSortInv base r [] xs
  have hS := oeSortInv_spec base r [] xs hxs_len (by simpa using hxs_lt)
  dsimp only at hS
  rcases hS with ⟨hextS, hlenS, hltS, hncS, hnnS, hvalS, hundoS⟩
  let ys := rS.2.1.take N
  have hys_len : ys.length = N := by rw [List.length_take, hlenS]; omega
  have hys_lt : ∀ i ∈ ys, i < base + rS.1.length := fun i hi => hltS i (List.mem_of_mem_take hi)
  let rInv := chainInv base (b + 1) rS.1 ys
  have hInv := chainInv_spec base (b + 1) rS.1 ys (by rw [hys_len]; exact hN_lt) hys_lt
  dsimp only at hInv
  rcases hInv with ⟨hextInv, hlenInv, hltInv, hncInv, hnnInv, hvalInv⟩
  have hglInv := hextInv.length_le
  let nout := rInv.2 ++ List.replicate (2 ^ r - N) oneWire
  have hnout_len : nout.length = 2 ^ r := by
    have hr2 : rInv.2.length = N := by rw [hlenInv, hys_len]
    rw [List.length_append, hr2, List.length_replicate]; omega
  have hnout_lt : ∀ u ∈ nout, u < base + rInv.1.length := by
    intro u hu
    simp only [nout, List.mem_append, List.mem_replicate] at hu
    rcases hu with hu | ⟨_, rfl⟩
    · exact hltInv u hu
    · omega
  let rB := rS.2.2 rInv.1 nout
  have hB := hundoS rInv.1 nout hextInv hnout_len hnout_lt
  rcases hB with ⟨hextB, hlenB, hltB, hncB, hnnB, hvalB⟩
  have hncInv_le : notCount ⟨rInv.1, 0⟩ ≤ b + 1 := by
    have h0 : notCount ⟨rS.1, 0⟩ = 0 := by rw [hncS, notCount_nil]
    dsimp only [rInv] at hncInv ⊢; omega
  let extraNot := b + 1 - notCount ⟨rB.1, 0⟩
  let gsFinal := padNots base zeroWire rB.1 extraNot
  have hPad := padNots_spec base zeroWire (by omega) extraNot rB.1
  rcases hPad with ⟨hextPad, hncPad, hnnPad⟩
  have hextAll : Extends base [] gsFinal := ((hextS.trans hextInv).trans hextB).trans hextPad
  rcases hextAll with ⟨eAll, heqAll, hfanAll, hrbAll⟩
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at heqAll hrbAll
  subst heqAll
  have hglPad := hextPad.length_le
  refine ⟨⟨gsFinal, 0⟩, ⟨hfanAll, hrbAll, by simp [Circuit.size]⟩, ?_, ?_, ?_⟩
  · refine ⟨fun i => ⟨rB.2.getD i.val 0, by
        have hlt := hltB _ (getD_mem rB.2 i.val 0 (by rw [hlenB]; have := i.isLt; omega))
        exact lt_of_lt_of_le hlt (Nat.add_le_add_left hglPad base)⟩,
      fun j => ⟨rB.2.getD (n + j.val) 0, by
        have hlt := hltB _ (getD_mem rB.2 (n + j.val) 0 (by rw [hlenB]; have := j.isLt; omega))
        exact lt_of_lt_of_le hlt (Nat.add_le_add_left hglPad base)⟩, ?_⟩
    intro x z
    have hlenV : (pairVec n m x z).length = base := by rw [pairVec_length]
    have hsort_prop : ∃ c ≤ N, rS.2.1.map (fun i => (wiresFrom rS.1 (pairVec n m x z)).getD i false) =
        sortedBool c (2 ^ r) := by
      have hmap := hvalS (pairVec n m x z) hlenV
      obtain ⟨c, hc2r, hsb⟩ := oeSortBool_sorted r (xs.map (fun i => (wiresFrom [] (pairVec n m x z)).getD i false))
        (by rw [List.length_map, hxs_len])
      have hcnt : c = (xs.map (fun i => (wiresFrom [] (pairVec n m x z)).getD i false)).count true := by
        have h1 := oeSortBool_count r (xs.map (fun i => (wiresFrom [] (pairVec n m x z)).getD i false)) (by rw [List.length_map, hxs_len])
        rw [hsb] at h1
        have hcnt_sb : (sortedBool c (2 ^ r)).count true = c := by
          dsimp only [sortedBool]
          rw [List.count_append, List.count_replicate, List.count_replicate]
          simp
        omega
      have hcnt_le_N : c ≤ N := by
        rw [hcnt]
        have hwnil : xs.map (fun i => (wiresFrom [] (pairVec n m x z)).getD i false) =
            xs.map (fun i => (pairVec n m x z).getD i false) :=
          List.map_congr_left (fun i _ => by rw [wiresFrom_nil])
        have hzw : (pairVec n m x z).getD zeroWire false = false := pairVec_getD_false n m x z
        rw [hwnil]
        simp only [xs, List.map_append, List.map_replicate, List.count_append, hzw]
        have hrep_cnt : (List.replicate (2 ^ r - N) false).count true = 0 := by simp [List.count_replicate]
        rw [hrep_cnt, add_zero]
        exact (List.count_le_length).trans (by simp [List.length_range])
      refine ⟨c, hcnt_le_N, ?_⟩
      rw [hmap]; exact hsb
    rcases hsort_prop with ⟨c, hcN, hsb⟩
    have hys_eval : ∀ t < N, (wiresFrom rS.1 (pairVec n m x z)).getD (ys.getD t 0) false = decide (t < c) := by
      intro t ht
      rw [getD_take rS.2.1 N t 0 ht]
      have hget : (rS.2.1.map (fun i => (wiresFrom rS.1 (pairVec n m x z)).getD i false)).getD t false =
          (wiresFrom rS.1 (pairVec n m x z)).getD (rS.2.1.getD t 0) false :=
        getD_map_eq _ rS.2.1 t 0 false (by rw [hlenS]; exact Nat.lt_trans ht hr_pow_gt)
      rw [← hget, hsb]
      dsimp only [sortedBool]
      by_cases htc : t < c
      · rw [getD_append_left _ _ t false (by simp; exact htc)]
        simp [List.getD_eq_getElem?_getD, htc]
      · rw [getD_append_right _ _ t false (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, show t - c < 2 ^ r - c by omega, htc]
    have hdec_ys : ∀ i j : ℕ, i < ys.length → j < ys.length → i ≤ j →
        (wiresFrom rS.1 (pairVec n m x z)).getD (ys.getD j 0) false ≤
          (wiresFrom rS.1 (pairVec n m x z)).getD (ys.getD i 0) false := by
      intro i j hi hj hij
      rw [hys_eval i (by omega), hys_eval j (by omega), bool_le_iff]
      intro h2; rw [decide_eq_true_eq] at h2 ⊢; omega
    have hInv' := hvalInv (pairVec n m x z) hlenV hdec_ys
    have hneg_nout : ∀ t < 2 ^ r, (wiresFrom rInv.1 (pairVec n m x z)).getD (nout.getD t 0) false =
        !((wiresFrom rInv.1 (pairVec n m x z)).getD (rS.2.1.getD t 0) false) := by
      intro t ht
      by_cases htN : t < N
      · rw [getD_append_left _ _ t 0 (by rw [hlenInv, hys_len]; exact htN)]
        rw [hInv' t (by rw [hys_len]; exact htN)]
        rw [hextInv.wire_eq _ hlenV _ (hltS _ (getD_mem rS.2.1 t 0 (by rw [hlenS]; exact ht)))]
        rw [getD_take rS.2.1 N t 0 htN]
      · rw [getD_append_right _ _ t 0 (by rw [hlenInv, hys_len]; omega)]
        have hrep : (List.replicate (2 ^ r - N) oneWire).getD (t - rInv.2.length) 0 = oneWire := by
          rw [hlenInv, hys_len]
          simp [List.getD_eq_getElem?_getD, show t - N < 2 ^ r - N by omega]
        rw [hrep, hextInv.wire_eq _ hlenV oneWire (by omega),
            wiresFrom_getD_lt _ _ oneWire (by rw [hlenV]; omega), pairVec_getD_true]
        rw [hextInv.wire_eq _ hlenV _ (hltS _ (getD_mem rS.2.1 t 0 (by rw [hlenS]; exact ht)))]
        have hget : (rS.2.1.map (fun i => (wiresFrom rS.1 (pairVec n m x z)).getD i false)).getD t false =
            (wiresFrom rS.1 (pairVec n m x z)).getD (rS.2.1.getD t 0) false :=
          getD_map_eq _ rS.2.1 t 0 false (by rw [hlenS]; exact ht)
        rw [← hget, hsb]
        dsimp only [sortedBool]
        rw [getD_append_right _ _ t false (by simp; omega)]
        simp [List.getD_eq_getElem?_getD, show t - c < 2 ^ r - c by omega]
    have hB' := hvalB (pairVec n m x z) hlenV hneg_nout
    have h_comp : ∀ t < N, (wiresFrom gsFinal (pairVec n m x z)).getD (rB.2.getD t 0) false =
        !((pairVec n m x z).getD t false) := by
      intro t ht
      rw [hextPad.wire_eq _ hlenV _ (hltB _ (getD_mem rB.2 t 0 (by rw [hlenB]; exact lt_trans ht hr_pow_gt)))]
      rw [hB' t (lt_trans ht hr_pow_gt)]
      rw [hextInv.wire_eq _ hlenV _ (lt_of_lt_of_le (hxs_lt _ (getD_mem xs t 0 (by rw [hxs_len]; exact lt_trans ht hr_pow_gt))) (by omega))]
      rw [hextS.wire_eq _ hlenV _ (hxs_lt _ (getD_mem xs t 0 (by rw [hxs_len]; exact lt_trans ht hr_pow_gt)))]
      have hxt : xs.getD t 0 = t := by
        rw [getD_append_left _ _ t 0 (by simp [List.length_range]; exact ht)]
        simp [List.getD_eq_getElem?_getD, ht]
      rw [hxt]; rfl
    refine ⟨?_, ?_, ?_⟩
    · intro i hinc
      have hi_not : i ∉ x := fun hix => by rw [Finset.insert_eq_of_mem hix] at hinc; exact Nat.lt_irrefl _ hinc
      change (wiresFrom gsFinal (pairVec n m x z)).getD (rB.2.getD i.val 0) false = true
      rw [h_comp i.val (by have := i.isLt; omega), pairVec_getD_left]
      simp [hi_not]
    · intro i hix
      change (wiresFrom gsFinal (pairVec n m x z)).getD (rB.2.getD i.val 0) false = false
      rw [h_comp i.val (by have := i.isLt; omega), pairVec_getD_left]
      simp [hix]
    · intro j
      change (wiresFrom gsFinal (pairVec n m x z)).getD (rB.2.getD (n + j.val) 0) false = decide (j ∉ z)
      rw [h_comp (n + j.val) (by have := j.isLt; omega), pairVec_getD_right]
      by_cases hjz : j ∈ z <;> simp [hjz]
  · change notCount ⟨gsFinal, 0⟩ = b + 1
    have hncB_le : notCount ⟨rB.1, 0⟩ ≤ b + 1 := by rw [hncB]; exact hncInv_le
    dsimp only [gsFinal, extraNot] at hncPad ⊢
    omega
  · change gsFinal.length ≤ 48 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2
    have hlen_decomp : gsFinal.length = notCount ⟨gsFinal, 0⟩ + nonNot gsFinal := by
      have := notCount_le_length gsFinal 0
      dsimp only [nonNot]; omega
    rw [hlen_decomp, hncPad, hnnPad]
    have hncB_le : notCount ⟨rB.1, 0⟩ ≤ b + 1 := by rw [hncB]; exact hncInv_le
    have hnc_tot : notCount ⟨rB.1, 0⟩ + extraNot = b + 1 := by dsimp only [extraNot]; omega
    have hnn_tot : nonNot rB.1 ≤ 3 * r * (r + 1) * 2 ^ r + 4 * N := by
      rw [hys_len] at hnnInv
      have h0 : nonNot [] = 0 := nonNot_nil
      rw [h0] at hnnS
      have h3r : r * (r + 1) * 2 ^ r + 2 * r * (r + 1) * 2 ^ r = 3 * r * (r + 1) * 2 ^ r := by ring
      linarith [hnnS, hnnInv, hnnB, h3r]
    have hb_le : b + 1 ≤ Nat.log2 (N + 2) + 2 := by dsimp only [b]; omega
    have hL : 1 ≤ (Nat.log2 (N + 2) + 2) ^ 2 := Nat.one_le_pow 2 _ (by omega)
    have h3 : 3 * r * (r + 1) * 2 ^ r ≤ 6 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by
      have h1 : r ≤ Nat.log2 (N + 2) + 2 := by omega
      have h2 : r + 1 ≤ Nat.log2 (N + 2) + 2 := by omega
      have hpow : 3 * r * (r + 1) ≤ 3 * (Nat.log2 (N + 2) + 2) ^ 2 := by
        rw [sq, ← mul_assoc]
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 3 h1) h2
      calc 3 * r * (r + 1) * 2 ^ r
          ≤ 3 * (Nat.log2 (N + 2) + 2) ^ 2 * (2 * N) := Nat.mul_le_mul hpow hr_pow_le
        _ = 6 * N * (Nat.log2 (N + 2) + 2) ^ 2 := by ring
        _ ≤ 6 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by gcongr; omega
    have h4 : 4 * N ≤ 4 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by
      calc 4 * N ≤ 4 * (N + 2) * 1 := by omega
        _ ≤ 4 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := Nat.mul_le_mul_left _ hL
    have hb2 : b + 1 ≤ 1 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by
      have hlog_ge : Nat.log2 (N + 2) + 2 ≤ N + 2 := by
        have hself := Nat.log2_self_le (by omega : N + 2 ≠ 0)
        have hlt2 := Nat.lt_two_pow_self (n := Nat.log2 (N + 2))
        cases hm : Nat.log2 (N + 2) with
        | zero => omega
        | succ m' =>
          cases m' with
          | zero => omega
          | succ m'' =>
            have hpow2 : m'' + 4 ≤ 2 ^ (m'' + 2) := by
              clear hself hlt2 hm
              induction m'' with
              | zero => norm_num
              | succ t iht =>
                rw [show t + 1 + 2 = (t + 2) + 1 by omega, pow_succ]
                have h1 : t + 1 + 4 ≤ (t + 4) * 2 := by omega
                have h2 : (t + 4) * 2 ≤ 2 ^ (t + 2) * 2 := Nat.mul_le_mul_right 2 iht
                omega
            rw [hm, show m'' + 1 + 1 = m'' + 2 by omega] at hself
            omega
      calc b + 1 ≤ Nat.log2 (N + 2) + 2 := hb_le
        _ ≤ 1 * (N + 2) * 1 := by omega
        _ ≤ 1 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := Nat.mul_le_mul_left _ hL
    have hsum_le : notCount ⟨rB.1, 0⟩ + extraNot + nonNot rB.1 ≤ 11 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by
      calc notCount ⟨rB.1, 0⟩ + extraNot + nonNot rB.1
          ≤ (b + 1) + (3 * r * (r + 1) * 2 ^ r + 4 * N) := by omega
        _ ≤ 1 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 +
            (6 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 + 4 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2) := by omega
        _ = 11 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by ring
    have h48 : 11 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 ≤ 48 * (N + 2) * (Nat.log2 (N + 2) + 2) ^ 2 := by gcongr; norm_num
    omega

end Conjunct2

section Conjunct3

def mkListChainX {n m : ℕ} (z : Finset (Fin m)) :
    List (Fin n) → Finset (Fin n) → List (Finset (Fin n) × Finset (Fin m))
  | [], cur => [(cur, z)]
  | i :: is, cur => (cur, z) :: mkListChainX z is (insert i cur)

def mkListChainZ {n m : ℕ} (x : Finset (Fin n)) :
    List (Fin m) → Finset (Fin m) → List (Finset (Fin n) × Finset (Fin m))
  | [], cur => [(x, cur)]
  | j :: js, cur => (x, cur) :: mkListChainZ x js (insert j cur)

lemma list_getD_zero_eq_head {α : Type*} (d : α) (l : List α) (h : l ≠ []) :
    l.getD 0 d = l.head h := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

lemma list_getLast_eq_getD_pred {α : Type*} (d : α) (l : List α) (h : l ≠ []) :
    l.getLast h = l.getD (l.length - 1) d := by
  rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (Nat.sub_lt (List.length_pos_of_ne_nil h) Nat.one_pos), Option.getD_some]

lemma mkListChainX_ne {n m : ℕ} (z : Finset (Fin m)) (xs : List (Fin n)) (cur : Finset (Fin n)) :
    mkListChainX z xs cur ≠ [] := by
  cases xs <;> simp [mkListChainX]

lemma mkListChainZ_ne {n m : ℕ} (x : Finset (Fin n)) (zs : List (Fin m)) (cur : Finset (Fin m)) :
    mkListChainZ x zs cur ≠ [] := by
  cases zs <;> simp [mkListChainZ]

def downChain {n m : ℕ} (xs : List (Fin n)) (zs : List (Fin m)) :
    List (Finset (Fin n) × Finset (Fin m)) :=
  (mkListChainX (∅ : Finset (Fin m)) xs ∅).dropLast ++ mkListChainZ xs.toFinset zs ∅

lemma downChain_spec {n m : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hcard : ∀ x, R x ≤ x.card) (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (B : Finset (Fin n)) (hB : R B = B.card) (z : Finset (Fin m)) :
    let ch := downChain B.toList z.toList
    ch ≠ [] ∧
    ch.length = B.card + z.card + 1 ∧
    ch.head (by simp [ch, downChain]; cases z.toList <;> simp [mkListChainZ]) = (∅, ∅) ∧
    ch.getLast (by simp [ch, downChain]; cases z.toList <;> simp [mkListChainZ]) = (B, z) ∧
    (∀ k, k + 1 < ch.length →
      let p1 := ch.getD k (∅, ∅)
      let p2 := ch.getD (k + 1) (∅, ∅)
      (∃ i, R p1.1 < R (insert i p1.1) ∧ p2.1 = insert i p1.1 ∧ p2.2 = p1.2) ∨
      (∃ j, j ∉ p1.2 ∧ p2.1 = p1.1 ∧ p2.2 = insert j p1.2)) := by

  have hX_prop : ∀ (xs : List (Fin n)) (cur : Finset (Fin n)),
      xs.Nodup → (∀ i ∈ xs, i ∉ cur) → R (cur ∪ xs.toFinset) = R cur + xs.length →
      let l := mkListChainX (∅ : Finset (Fin m)) xs cur
      l ≠ [] ∧ l.length = xs.length + 1 ∧
      l.head (mkListChainX_ne _ xs cur) = (cur, ∅) ∧
      l.getLast (mkListChainX_ne _ xs cur) = (cur ∪ xs.toFinset, ∅) ∧
      (∀ k, k + 1 < l.length →
        let p1 := l.getD k (∅, ∅); let p2 := l.getD (k + 1) (∅, ∅)
        ∃ i, R p1.1 < R (insert i p1.1) ∧ p2.1 = insert i p1.1 ∧ p2.2 = p1.2) := by
    intro xs
    induction xs with
    | nil =>
      intro cur _ _ _; dsimp only [mkListChainX]
      refine ⟨by simp, rfl, rfl, by simp, fun k hk => by simp at hk⟩
    | cons a xs ih =>
      intro cur hnd hdisj hrk
      rcases List.nodup_cons.mp hnd with ⟨hax, hnd'⟩
      have hdisj' : ∀ i ∈ xs, i ∉ insert a cur := fun i hi hm => by
        rcases Finset.mem_insert.mp hm with rfl | hmc
        · exact hax hi
        · exact hdisj i (List.mem_cons_of_mem _ hi) hmc
      have heq_u : insert a cur ∪ xs.toFinset = cur ∪ (a :: xs).toFinset := by
        ext t; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto
      have hrk_a : R (insert a cur) = R cur + 1 := by
        have h1 := rk_ins_le R hcard hsub cur a
        have h2 : R (cur ∪ (a :: xs).toFinset) ≤ R (insert a cur) + xs.length := by
          rw [← heq_u]
          clear ih heq_u hdisj' hax hnd' hdisj hnd hrk
          have : ∀ (bs : List (Fin n)) (c0 : Finset (Fin n)), R (c0 ∪ bs.toFinset) ≤ R c0 + bs.length := by
            intro bs; induction bs with | nil => intro c0; simp | cons b bs ihb =>
              intro c0
              have hstep := rk_ins_le R hcard hsub (c0 ∪ bs.toFinset) b
              have hu2 : c0 ∪ (b :: bs).toFinset = insert b (c0 ∪ bs.toFinset) := by
                ext t; simp [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
              rw [hu2]; have := ihb c0; simp only [List.length_cons] at *; omega
          exact this xs (insert a cur)
        simp only [List.length_cons] at hrk
        omega
      have hrk' : R (insert a cur ∪ xs.toFinset) = R (insert a cur) + xs.length := by
        rw [heq_u, hrk, hrk_a]; simp only [List.length_cons]; omega
      have ih' := ih (insert a cur) hnd' hdisj' hrk'
      rcases ih' with ⟨hne, hlen, hhd, hlst, hstep⟩
      dsimp only [mkListChainX]
      refine ⟨by simp, by simp [hlen], rfl, ?_, ?_⟩
      · rw [List.getLast_cons hne, hlst, heq_u]
      · intro k hk
        cases k with
        | zero =>
          have hhd' : (mkListChainX (∅ : Finset (Fin m)) xs (insert a cur)).getD 0 (∅, ∅) = (insert a cur, ∅) := by
            cases xs <;> simp [mkListChainX]
          change ∃ i, R cur < R (insert i cur) ∧ ((mkListChainX ∅ xs (insert a cur)).getD 0 (∅, ∅)).1 = insert i cur ∧
              ((mkListChainX ∅ xs (insert a cur)).getD 0 (∅, ∅)).2 = ∅
          rw [hhd']
          exact ⟨a, by omega, rfl, rfl⟩
        | succ k' =>
          exact hstep k' (by simp at hk; omega)
  have hZ_prop : ∀ (x : Finset (Fin n)) (zs : List (Fin m)) (cur : Finset (Fin m)),
      zs.Nodup → (∀ j ∈ zs, j ∉ cur) →
      let l := mkListChainZ x zs cur
      l ≠ [] ∧ l.length = zs.length + 1 ∧
      l.head (mkListChainZ_ne x zs cur) = (x, cur) ∧
      l.getLast (mkListChainZ_ne x zs cur) = (x, cur ∪ zs.toFinset) ∧
      (∀ k, k + 1 < l.length →
        let p1 := l.getD k (∅, ∅); let p2 := l.getD (k + 1) (∅, ∅)
        ∃ j, j ∉ p1.2 ∧ p2.1 = p1.1 ∧ p2.2 = insert j p1.2) := by
    intro x zs
    induction zs with
    | nil =>
      intro cur _ _; dsimp only [mkListChainZ]
      refine ⟨by simp, rfl, rfl, by simp, fun k hk => by simp at hk⟩
    | cons a zs ih =>
      intro cur hnd hdisj
      rcases List.nodup_cons.mp hnd with ⟨haz, hnd'⟩
      have hdisj' : ∀ j ∈ zs, j ∉ insert a cur := fun j hj hm => by
        rcases Finset.mem_insert.mp hm with rfl | hmc
        · exact haz hj
        · exact hdisj j (List.mem_cons_of_mem _ hj) hmc
      have ih' := ih (insert a cur) hnd' hdisj'
      rcases ih' with ⟨hne, hlen, hhd, hlst, hstep⟩
      dsimp only [mkListChainZ]
      have heq_u : insert a cur ∪ zs.toFinset = cur ∪ (a :: zs).toFinset := by
        ext t; simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]; tauto
      refine ⟨by simp, by simp [hlen], rfl, ?_, ?_⟩
      · rw [List.getLast_cons hne, hlst, heq_u]
      · intro k hk
        cases k with
        | zero =>
          cases zs with
          | nil => exact ⟨a, hdisj a (List.mem_cons_self ..), rfl, rfl⟩
          | cons b bs => exact ⟨a, hdisj a (List.mem_cons_self ..), rfl, rfl⟩
        | succ k' => exact hstep k' (by simp at hk; omega)
  have hBnd : B.toList.Nodup := Finset.nodup_toList B
  have hZnd : z.toList.Nodup := Finset.nodup_toList z
  have hBrk : R (∅ ∪ B.toList.toFinset) = R ∅ + B.toList.length := by
    rw [Finset.empty_union, Finset.toList_toFinset, hB, Finset.length_toList]
    have hR0 : R ∅ = 0 := by
      have := hcard ∅; simp at this; exact this
    omega
  have hX := hX_prop B.toList ∅ hBnd (fun _ _ h => by cases h) hBrk
  have hZ := hZ_prop B z.toList ∅ hZnd (fun _ _ h => by cases h)
  rcases hX with ⟨hneX, hlenX, hhdX, hlstX, hstepX⟩
  rcases hZ with ⟨hneZ, hlenZ, hhdZ, hlstZ, hstepZ⟩
  dsimp only [downChain]
  have hB_to : B.toList.toFinset = B := Finset.toList_toFinset B
  have hdl_len : (mkListChainX (∅ : Finset (Fin m)) B.toList ∅).dropLast.length = B.card := by
    rw [List.length_dropLast, hlenX, Finset.length_toList]; omega
  set lX := mkListChainX (∅ : Finset (Fin m)) B.toList ∅
  set lZ := mkListChainZ B z.toList ∅
  have hZ_eq : mkListChainZ B.toList.toFinset z.toList ∅ = lZ := by rw [hB_to]
  have hne_ch0 : lX.dropLast ++ mkListChainZ B.toList.toFinset z.toList ∅ ≠ [] := by
    rw [hZ_eq]; simp [hneZ]
  have hne_ch : lX.dropLast ++ lZ ≠ [] := by simp [hneZ]
  have hX_split : lX = lX.dropLast ++ [lX.getLast hneX] := (List.dropLast_append_getLast hneX).symm
  have hlen_lX : lX.length = lX.dropLast.length + 1 := by
    conv_lhs => rw [hX_split]
    rw [List.length_append, List.length_singleton]
  have hlen_ch : (lX.dropLast ++ lZ).length = B.card + z.card + 1 := by
    rw [List.length_append, hdl_len, hlenZ, Finset.length_toList]; omega
  refine ⟨hne_ch0, ?_, ?_, ?_, ?_⟩
  · rw [hZ_eq]; exact hlen_ch
  · rw [← list_getD_zero_eq_head (∅, ∅) (lX.dropLast ++ mkListChainZ B.toList.toFinset z.toList ∅) _]
    rw [hZ_eq]
    by_cases h_nil : lX.dropLast = []
    · have hBc : B.card = 0 := by rw [← hdl_len, h_nil]; rfl
      have hBe : B = ∅ := Finset.card_eq_zero.mp hBc
      rw [h_nil, List.nil_append]
      have hZ0 : lZ.getD 0 (∅, ∅) = (B, ∅) := by dsimp only [lZ]; cases z.toList <;> rfl
      rw [hZ0, hBe]
    · have hpos : 0 < lX.dropLast.length := List.length_pos_of_ne_nil h_nil
      rw [getD_append_left _ _ 0 (∅, ∅) hpos]
      have h1 : lX.dropLast.getD 0 (∅, ∅) = lX.getD 0 (∅, ∅) := by
        conv_rhs => rw [hX_split]
        exact (getD_append_left lX.dropLast [lX.getLast hneX] 0 (∅, ∅) hpos).symm
      rw [h1, list_getD_zero_eq_head (∅, ∅) lX hneX, hhdX]
  · rw [list_getLast_eq_getD_pred (∅, ∅) (lX.dropLast ++ mkListChainZ B.toList.toFinset z.toList ∅) hne_ch0]
    rw [hZ_eq]
    rw [← list_getLast_eq_getD_pred (∅, ∅) (lX.dropLast ++ lZ) hne_ch]
    rw [List.getLast_append_of_ne_nil _ hneZ, hlstZ, Finset.empty_union, Finset.toList_toFinset]
  · intro k hk
    rw [hZ_eq] at hk ⊢
    by_cases hk1 : k + 1 < lX.dropLast.length
    · rw [getD_append_left lX.dropLast lZ k (∅, ∅) (by omega), getD_append_left lX.dropLast lZ (k + 1) (∅, ∅) hk1]
      have h1 : lX.dropLast.getD k (∅, ∅) = lX.getD k (∅, ∅) := by
        conv_rhs => rw [hX_split]
        exact (getD_append_left lX.dropLast [lX.getLast hneX] k (∅, ∅) (by omega)).symm
      have h2 : lX.dropLast.getD (k + 1) (∅, ∅) = lX.getD (k + 1) (∅, ∅) := by
        conv_rhs => rw [hX_split]
        exact (getD_append_left lX.dropLast [lX.getLast hneX] (k + 1) (∅, ∅) hk1).symm
      rw [h1, h2]
      exact Or.inl (hstepX k (by omega))
    · by_cases hk2 : k < lX.dropLast.length
      · have hkeq : k + 1 = lX.dropLast.length := by omega
        rw [getD_append_left lX.dropLast lZ k (∅, ∅) hk2, getD_append_right lX.dropLast lZ (k + 1) (∅, ∅) (by omega),
            show k + 1 - lX.dropLast.length = 0 by omega]
        have h1 : lX.dropLast.getD k (∅, ∅) = lX.getD k (∅, ∅) := by
          conv_rhs => rw [hX_split]
          exact (getD_append_left lX.dropLast [lX.getLast hneX] k (∅, ∅) hk2).symm
        have h2 : lZ.getD 0 (∅, ∅) = lX.getLast hneX := by
          have hhdZ' : lZ.getD 0 (∅, ∅) = (B, ∅) := by dsimp only [lZ]; cases z.toList <;> rfl
          rw [hhdZ', hlstX, Finset.empty_union, hB_to]
        have h2' : lX.getLast hneX = lX.getD (k + 1) (∅, ∅) := by
          conv_rhs => rw [hX_split]
          rw [getD_append_right lX.dropLast [lX.getLast hneX] (k + 1) (∅, ∅) (by omega),
              show k + 1 - lX.dropLast.length = 0 by omega]
          rfl
        rw [h1, h2, h2']
        exact Or.inl (hstepX k (by omega))
      · have hk_ge : lX.dropLast.length ≤ k := by omega
        rw [getD_append_right lX.dropLast lZ k (∅, ∅) hk_ge, getD_append_right lX.dropLast lZ (k + 1) (∅, ∅) (by omega),
            show k + 1 - lX.dropLast.length = (k - lX.dropLast.length) + 1 by omega]
        rw [List.length_append] at hk
        have hlt_z : k - lX.dropLast.length + 1 < lZ.length := by
          dsimp only [lX, lZ] at hk hk_ge ⊢
          omega
        exact Or.inr (hstepZ (k - lX.dropLast.length) hlt_z)

lemma upChain_exists {n m : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hcard : ∀ x, R x ≤ x.card) (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x : Finset (Fin n)) (z : Finset (Fin m)) :
    ∃ ch : List (Finset (Fin n) × Finset (Fin m)),
      ∃ hne : ch ≠ [],
      ch.length = (R Finset.univ - R x) + (m - z.card) + 1 ∧
      ch.head hne = (x, z) ∧
      (∀ k, k + 1 < ch.length →
        let p1 := ch.getD k (∅, ∅); let p2 := ch.getD (k + 1) (∅, ∅)
        (∃ i, R p1.1 < R (insert i p1.1) ∧ p2.1 = insert i p1.1 ∧ p2.2 = p1.2) ∨
        (∃ j, j ∉ p1.2 ∧ p2.1 = p1.1 ∧ p2.2 = insert j p1.2)) := by
  have hX : ∀ (k : ℕ) (x0 : Finset (Fin n)), R Finset.univ - R x0 = k →
      ∃ l : List (Finset (Fin n) × Finset (Fin m)),
        ∃ hne : l ≠ [], l.length = k + 1 ∧ l.head hne = (x0, z) ∧
        (∀ t, t + 1 < l.length →
          let p1 := l.getD t (∅, ∅); let p2 := l.getD (t + 1) (∅, ∅)
          ∃ i, R p1.1 < R (insert i p1.1) ∧ p2.1 = insert i p1.1 ∧ p2.2 = p1.2) := by
    intro k
    induction k with
    | zero =>
      intro x0 _
      exact ⟨[(x0, z)], by simp, rfl, rfl, fun t ht => by simp at ht⟩
    | succ k ih =>
      intro x0 hdiff
      have hlt : R x0 < R Finset.univ := by omega
      obtain ⟨i, hi⟩ := rk_extend_exists R hmono hsub x0 hlt
      have hle := rk_ins_le R hcard hsub x0 i
      have hdiff' : R Finset.univ - R (insert i x0) = k := by omega
      obtain ⟨l', hne', hlen', hhd', hstep'⟩ := ih (insert i x0) hdiff'
      refine ⟨(x0, z) :: l', by simp, by simp [hlen'], rfl, ?_⟩
      intro t ht
      cases t with
      | zero =>
        simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
          List.getElem?_cons_succ]
        have hl0 : l'[0]?.getD (∅, ∅) = (insert i x0, z) := by
          cases l' with
          | nil => exact absurd rfl hne'
          | cons a tl => exact hhd'
        rw [hl0]
        exact ⟨i, hi, rfl, rfl⟩
      | succ t' => exact hstep' t' (by simp at ht; omega)
  obtain ⟨lX, hneX, hlenX, hhdX, hstepX⟩ := hX (R Finset.univ - R x) x rfl
  let xEnd := (lX.getLast hneX).1
  let js := (Finset.univ \ z).toList
  have hjs_nd : js.Nodup := Finset.nodup_toList _
  have hjs_disj : ∀ j ∈ js, j ∉ z := fun j hj => (Finset.mem_sdiff.mp (Finset.mem_toList.mp hj)).2
  have hjs_len : js.length = m - z.card := by
    dsimp only [js]; rw [Finset.length_toList, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  have hZ : ∀ (js' : List (Fin m)) (z0 : Finset (Fin m)), js'.Nodup → (∀ j ∈ js', j ∉ z0) →
      let lZ := mkListChainZ xEnd js' z0
      lZ ≠ [] ∧ lZ.length = js'.length + 1 ∧
      lZ.head (mkListChainZ_ne xEnd js' z0) = (xEnd, z0) ∧
      (∀ t, t + 1 < lZ.length →
        let p1 := lZ.getD t (∅, ∅); let p2 := lZ.getD (t + 1) (∅, ∅)
        ∃ j, j ∉ p1.2 ∧ p2.1 = p1.1 ∧ p2.2 = insert j p1.2) := by
    intro js'
    induction js' with
    | nil => intro z0 _ _; exact ⟨by simp [mkListChainZ], rfl, rfl, fun t ht => by simp [mkListChainZ] at ht⟩
    | cons a js' ih =>
      intro z0 hnd hdj
      rcases List.nodup_cons.mp hnd with ⟨ha, hnd'⟩
      have hdj' : ∀ j ∈ js', j ∉ insert a z0 := fun j hj hm => by
        rcases Finset.mem_insert.mp hm with rfl | hm'
        · exact ha hj
        · exact hdj j (List.mem_cons_of_mem _ hj) hm'
      obtain ⟨hneZ, hlenZ, hhdZ, hstepZ⟩ := ih (insert a z0) hnd' hdj'
      refine ⟨by simp [mkListChainZ], by simp [mkListChainZ, hlenZ], rfl, ?_⟩
      intro t ht
      cases t with
      | zero =>
        cases js' <;> exact ⟨a, hdj a (List.mem_cons_self ..), rfl, rfl⟩
      | succ t' => exact hstepZ t' (by simp [mkListChainZ] at ht; omega)
  obtain ⟨hneZ, hlenZ, hhdZ, hstepZ⟩ := hZ js z hjs_nd hjs_disj
  have hlX_last_z : (lX.getLast hneX).2 = z := by
    have hconst : ∀ k < lX.length, (lX.getD k (∅, ∅)).2 = z := by
      intro k hk
      induction k with
      | zero =>
        have h0 : lX.getD 0 (∅, ∅) = lX.head hneX := by cases lX with | nil => exact absurd rfl hneX | cons a tl => rfl
        rw [h0, hhdX]
      | succ k' ihk =>
        have hst := hstepX k' hk
        rw [← ihk (by omega)]
        rcases hst with ⟨_, _, _, hz2⟩
        exact hz2
    have hlast_eq : lX.getLast hneX = lX.getD (lX.length - 1) (∅, ∅) := by
      rw [List.getLast_eq_getElem, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (Nat.sub_lt (List.length_pos_of_ne_nil hneX) Nat.one_pos), Option.getD_some]
    rw [hlast_eq]
    exact hconst (lX.length - 1) (Nat.sub_lt (List.length_pos_of_ne_nil hneX) Nat.one_pos)
  set lZ := mkListChainZ xEnd js z
  have hlX_split : lX = lX.dropLast ++ [lX.getLast hneX] := (List.dropLast_append_getLast hneX).symm
  have hdl_len : lX.dropLast.length = R Finset.univ - R x := by rw [List.length_dropLast, hlenX]; omega
  refine ⟨lX.dropLast ++ lZ, by simp [hneZ], by rw [List.length_append, hdl_len, hlenZ, hjs_len]; omega, ?_, ?_⟩
  · cases hdl : lX.dropLast with
    | nil =>
      have h0 : lX.length = 1 := by
        have : lX.dropLast.length = 0 := by rw [hdl]; rfl
        rw [List.length_dropLast] at this; have := List.length_pos_of_ne_nil hneX; omega
      have hlast : lX.getLast hneX = lX.head hneX := by
        cases lX with | nil => exact absurd rfl hneX | cons a tl =>
          have htl : tl = [] := List.eq_nil_of_length_eq_zero (by rw [List.length_cons] at h0; omega)
          subst htl; rfl
      have hxz : (xEnd, z) = (x, z) := by
        dsimp only [xEnd]; rw [hlast, hhdX]
      simp [hneZ]
      have hlZ0 : lZ.head hneZ = (xEnd, z) := hhdZ
      rw [hlZ0, hxz]
    | cons hd tl =>
      have hhd_eq : lX.head hneX = hd := by
        have h1 := congrArg (fun l : List (Finset (Fin n) × Finset (Fin m)) => l.getD 0 (∅, ∅)) hlX_split
        rw [hdl] at h1
        have h2 : lX.getD 0 (∅, ∅) = lX.head hneX := by cases lX with | nil => exact absurd rfl hneX | cons _ _ => rfl
        rw [← h2]; exact h1
      rw [← hhd_eq]; exact hhdX
  · intro k hk
    by_cases hk1 : k + 1 < lX.dropLast.length
    · rw [getD_append_left _ _ k (∅, ∅) (by omega), getD_append_left _ _ (k + 1) (∅, ∅) hk1]
      have h1 : lX.dropLast.getD k (∅, ∅) = lX.getD k (∅, ∅) := by
        have h1' := getD_append_left lX.dropLast [lX.getLast hneX] k (∅, ∅) (by omega)
        rw [← hlX_split] at h1'; exact h1'.symm
      have h2 : lX.dropLast.getD (k + 1) (∅, ∅) = lX.getD (k + 1) (∅, ∅) := by
        have h2' := getD_append_left lX.dropLast [lX.getLast hneX] (k + 1) (∅, ∅) hk1
        rw [← hlX_split] at h2'; exact h2'.symm
      rw [h1, h2]; exact Or.inl (hstepX k (by omega))
    · by_cases hk2 : k < lX.dropLast.length
      · rw [getD_append_left _ _ k (∅, ∅) hk2, getD_append_right _ _ (k + 1) (∅, ∅) (by omega),
            show k + 1 - lX.dropLast.length = 0 by omega]
        have h1 : lX.dropLast.getD k (∅, ∅) = lX.getD k (∅, ∅) := by
          have h1' := getD_append_left lX.dropLast [lX.getLast hneX] k (∅, ∅) hk2
          rw [← hlX_split] at h1'; exact h1'.symm
        have h2 : lZ.getD 0 (∅, ∅) = lX.getLast hneX := by
          have hhd0 : lZ.getD 0 (∅, ∅) = (xEnd, z) := by
            rw [list_getD_zero_eq_head (∅, ∅) lZ hneZ, hhdZ]
          rw [hhd0]; exact Prod.ext rfl hlX_last_z.symm
        have h2' : lX.getLast hneX = lX.getD (k + 1) (∅, ∅) := by
          conv_rhs => rw [hlX_split]
          rw [getD_append_right _ _ (k + 1) (∅, ∅) (by omega), show k + 1 - lX.dropLast.length = 0 by omega]; rfl
        rw [h1, h2, h2']
        exact Or.inl (hstepX k (by rw [hlX_split, List.length_append, List.length_singleton]; omega))
      · have hk_ge : lX.dropLast.length ≤ k := by omega
        rw [getD_append_right _ _ k (∅, ∅) hk_ge, getD_append_right _ _ (k + 1) (∅, ∅) (by omega),
            show k + 1 - lX.dropLast.length = (k - lX.dropLast.length) + 1 by omega]
        rw [List.length_append] at hk
        exact Or.inr (hstepZ (k - lX.dropLast.length) (by omega))

lemma conjunct3_proof (a n : ℕ) (R : Finset (Fin n) → ℕ)
    (hn : n ≤ 2 ^ a) (h0 : R ∅ = 0) (hmono : Monotone R)
    (hcard : ∀ x, R x ≤ x.card) (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) :
    let h := 2 ^ a
    let b := a + 1
    let d := R Finset.univ
    let m := 2 * h - 1 - d
    let N := n + m
    ∀ C : Circuit,
      (FanInTwo C ∧ ReadsBack (N + 2) C ∧ C.output < N + 2 + C.size) →
      (∃ (old : Fin n → Fin (N + 2 + C.size)) (pad : Fin m → Fin (N + 2 + C.size)),
        ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
          let w := C.wires (pairVec n m x z)
          (∀ i, R x < R (insert i x) → w.getD (old i).val false = true) ∧
          (∀ i ∈ x, w.getD (old i).val false = false) ∧
          (∀ j, w.getD (pad j).val false = decide (j ∉ z))) →
      b ≤ notCount C ∧
      (notCount C = b → ∃ P : Circuit,
        (FanInTwo P ∧ ReadsBack (N + 2) P ∧ P.output < N + 2 + P.size) ∧
        Monotone2 P ∧ P.size < C.size ∧
        ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
          P.eval (pairVec n m x z) = decide (h ≤ R x + z.card)) := by
  intro h b d m N C ⟨hfan, hrb, hout⟩ ⟨old, pad, hfit_fin⟩
  have hfit : FitWires n m R C (fun i => (old i).val) (fun j => (pad j).val) := hfit_fin
  have hd_le_n : d ≤ n := by simpa [d] using hcard Finset.univ
  have h_pos : 1 ≤ h := Nat.one_le_two_pow
  obtain ⟨B, _, hBcard, hBrk⟩ := rk_indep_exists R h0 hmono hcard hsub Finset.univ d (le_refl d)
  have hb_lb : b ≤ notCount C := by
    have hch := downChain_spec R hmono hcard hsub B (by rw [hBrk, hBcard]) (Finset.univ : Finset (Fin m))
    rcases hch with ⟨hne, hlen, _, _, hstep⟩
    have hdrop := chain_evalNotCode_drop R C hfan _ _ hfit C.gates hfan
      (downChain B.toList (Finset.univ : Finset (Fin m)).toList) hne hstep [] rfl rfl
    have hlt := evalNotCode_lt C.gates (pairVec n m ((downChain B.toList (Finset.univ : Finset (Fin m)).toList).head hne).1
      ((downChain B.toList (Finset.univ : Finset (Fin m)).toList).head hne).2)
    have hpow : (downChain B.toList (Finset.univ : Finset (Fin m)).toList).length - 1 = 2 ^ b - 1 := by
      rw [hlen, hBcard, Finset.card_univ, Fintype.card_fin]
      have hb : 2 ^ b = 2 * h := by dsimp only [b, h]; rw [pow_succ]; ring
      omega
    have hnot_lt : 2 ^ b - 1 < 2 ^ notCount C := by
      simp only [wiresFrom_nil] at hdrop
      have hnc_eq : notCount ⟨C.gates, 0⟩ = notCount C := rfl
      rw [hnc_eq] at hlt
      have : evalNotCode C.gates (pairVec n m ((downChain B.toList (Finset.univ : Finset (Fin m)).toList).head hne).1
          ((downChain B.toList (Finset.univ : Finset (Fin m)).toList).head hne).2) < 2 ^ notCount C := hlt
      omega
    have hpow_le : 2 ^ b ≤ 2 ^ notCount C := by omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  refine ⟨hb_lb, fun hnc => ?_⟩
  have hnc_pos : 0 < notCount ⟨C.gates, 0⟩ := by change 0 < notCount C; omega
  obtain ⟨pre, g1, post, hceq, hpre0, hg1, hpost_nc⟩ := split_first_not C.gates hnc_pos
  have hpre_fan : FanInTwo ⟨pre, 0⟩ := fun g hg => hfan g (by rw [hceq]; exact List.mem_append_left _ hg)
  have hpost_fan : FanInTwo ⟨post, 0⟩ := fun g hg => hfan g (by rw [hceq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
  have hpre_mono : Monotone2 ⟨pre, 0⟩ := monotone2_of_fanInTwo_notZero pre hpre_fan hpre0
  have hpre_rb : ReadsBack (N + 2) ⟨pre, 0⟩ := by
    intro j hj i hi
    have hj_len : j < pre.length := hj
    have hjC : j < C.gates.length := by rw [hceq, List.length_append, List.length_cons]; omega
    have h1 := hrb j hjC
    rw [gateAt_eq_getElem _ j hjC] at h1
    rw [gateAt_eq_getElem _ j hj_len] at hi
    have hget : C.gates[j]'hjC = pre[j]'hj_len := by simp [hceq, List.getElem_append_left hj_len]
    rw [hget] at h1
    exact h1 i hi
  have hg1_rb : ∀ i ∈ g1.inputs, i < N + 2 + pre.length := by
    intro i hi
    have hj : pre.length < C.gates.length := by rw [hceq, List.length_append, List.length_cons]; omega
    have h1 := hrb pre.length hj i
    rw [gateAt_eq_getElem _ pre.length hj] at h1
    have hget : C.gates[pre.length]'hj = g1 := by simp [hceq]
    rw [hget] at h1
    exact h1 hi
  have hpost_nc_a : notCount ⟨post, 0⟩ = a := by
    have : notCount ⟨C.gates, 0⟩ = notCount C := rfl
    omega

  have hconst_contra : ∀ (ch : List (Finset (Fin n) × Finset (Fin m))) (hne : ch ≠ []),
      h ≤ ch.length - 1 →
      (∀ k, k + 1 < ch.length →
        let p1 := ch.getD k (∅, ∅); let p2 := ch.getD (k + 1) (∅, ∅)
        (∃ i, R p1.1 < R (insert i p1.1) ∧ p2.1 = insert i p1.1 ∧ p2.2 = p1.2) ∨
        (∃ j, j ∉ p1.2 ∧ p2.1 = p1.1 ∧ p2.2 = insert j p1.2)) →
      ∀ val0 : Bool,
        (∀ p ∈ ch, g1.op.eval (g1.inputs.map fun i => (wiresFrom pre (pairVec n m p.1 p.2)).getD i false) = val0) →
        False := by
    intro ch hne hlen_ge hstep val0 hconst
    have hg1_post : FanInTwo ⟨g1 :: post, 0⟩ := fun g hg =>
      hfan g (by rw [hceq]; exact List.mem_append_right _ hg)
    have hdrop := chain_evalNotCode_drop R C hfan _ _ hfit (g1 :: post) hg1_post ch hne hstep pre hceq hpre0
    have hmem_head : ch.head hne ∈ ch := List.head_mem hne
    have hmem_last : ch.getLast hne ∈ ch := List.getLast_mem hne
    have hev_head : evalNotCode (g1 :: post) (wiresFrom pre (pairVec n m (ch.head hne).1 (ch.head hne).2)) =
        (if val0 then 2 ^ a else 0) + evalNotCode post (wiresFrom pre (pairVec n m (ch.head hne).1 (ch.head hne).2) ++ [val0]) := by
      have hev0 := hconst _ hmem_head; rw [hg1] at hev0; dsimp only [evalNotCode]; rw [hg1, hev0, hpost_nc_a]
    have hev_last : evalNotCode (g1 :: post) (wiresFrom pre (pairVec n m (ch.getLast hne).1 (ch.getLast hne).2)) =
        (if val0 then 2 ^ a else 0) + evalNotCode post (wiresFrom pre (pairVec n m (ch.getLast hne).1 (ch.getLast hne).2) ++ [val0]) := by
      have hev0 := hconst _ hmem_last; rw [hg1] at hev0; dsimp only [evalNotCode]; rw [hg1, hev0, hpost_nc_a]
    rw [hev_head, hev_last] at hdrop
    have hlt_post := evalNotCode_lt post (wiresFrom pre (pairVec n m (ch.head hne).1 (ch.head hne).2) ++ [val0])
    rw [hpost_nc_a] at hlt_post
    omega
  have hg1_ne : g1.inputs ≠ [] := by
    intro heq_nil
    have hch := downChain_spec R hmono hcard hsub B (by rw [hBrk, hBcard]) (Finset.univ : Finset (Fin m))
    rcases hch with ⟨hne, hlen, _, _, hstep⟩
    apply hconst_contra _ hne (by rw [hlen, hBcard, Finset.card_univ, Fintype.card_fin]; omega) hstep true
    intro p _
    rw [heq_nil, hg1]; rfl
  obtain ⟨w_out, tl_g1, hg1_eq⟩ := List.exists_cons_of_ne_nil hg1_ne
  have hw_lt : w_out < N + 2 + pre.length := hg1_rb w_out (by rw [hg1_eq]; exact List.mem_cons_self ..)
  let P : Circuit := ⟨pre, w_out⟩
  have hP_eval : ∀ x z, g1.op.eval (g1.inputs.map fun i => (wiresFrom pre (pairVec n m x z)).getD i false) =
      !(P.eval (pairVec n m x z)) := by
    intro x z
    rw [hg1, hg1_eq]
    rfl
  refine ⟨P, ⟨hpre_fan, hpre_rb, hw_lt⟩, hpre_mono, by dsimp only [Circuit.size, P]; rw [hceq]; simp, ?_⟩
  intro x z
  have hP_mono : ∀ x1 x2 z1 z2, x1 ⊆ x2 → z1 ⊆ z2 →
      P.eval (pairVec n m x1 z1) ≤ P.eval (pairVec n m x2 z2) := fun x1 x2 z1 z2 hx hz =>
    wiresFrom_mono pre hpre_mono _ _ (by rw [pairVec_length, pairVec_length]) (pairVec_mono hx hz) w_out
  cases hcase : decide (h ≤ R x + z.card) with
  | false =>
    rw [decide_eq_false_iff_not] at hcase
    cases hp : P.eval (pairVec n m x z) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨ch, hne, hlen, hhd, hstep⟩ := upChain_exists R hmono hcard hsub x z
      have h_sub_chain : ∀ k < ch.length, x ⊆ (ch.getD k (∅, ∅)).1 ∧ z ⊆ (ch.getD k (∅, ∅)).2 := by
        intro k hk
        induction k with
        | zero =>
          have h0 : ch.getD 0 (∅, ∅) = ch.head hne := by cases ch with | nil => exact absurd rfl hne | cons a tl => rfl
          rw [h0, hhd]; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
        | succ k' ihk =>
          obtain ⟨ihx, ihz⟩ := ihk (by omega)
          rcases hstep k' hk with ⟨i, _, hx2, hz2⟩ | ⟨j, _, hx2, hz2⟩
          · rw [hx2, hz2]; exact ⟨ihx.trans (Finset.subset_insert _ _), ihz⟩
          · rw [hx2, hz2]; exact ⟨ihx, ihz.trans (Finset.subset_insert _ _)⟩
      apply hconst_contra ch hne (by omega) hstep false
      intro p hp_mem
      obtain ⟨k, hk, hgetk⟩ := List.getElem_of_mem hp_mem
      have hsubp := h_sub_chain k hk
      have hgetk' : ch.getD k (∅, ∅) = p := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact hgetk
      rw [hgetk'] at hsubp
      have hle := hP_mono x p.1 z p.2 hsubp.1 hsubp.2
      rw [hp] at hle
      have hpt : P.eval (pairVec n m p.1 p.2) = true := by
        cases hv : P.eval (pairVec n m p.1 p.2)
        · rw [hv] at hle; exact absurd hle not_true_le_false
        · rfl
      rw [hP_eval p.1 p.2, hpt]; rfl
  | true =>
    rw [decide_eq_true_eq] at hcase
    cases hp : P.eval (pairVec n m x z) with
    | true => rfl
    | false =>
      exfalso
      obtain ⟨Bx, hBxx, hBx_card, hBx_rk⟩ := rk_indep_exists R h0 hmono hcard hsub x (R x) (le_refl (R x))
      have hch := downChain_spec R hmono hcard hsub Bx (by rw [hBx_rk, hBx_card]) z
      rcases hch with ⟨hne, hlen, _, hlst, hstep⟩
      let ch := downChain Bx.toList z.toList
      have h_sub_chain : ∀ p ∈ ch, p.1 ⊆ x ∧ p.2 ⊆ z := by
        intro p hp_mem
        obtain ⟨k, hk, hgetk⟩ := List.getElem_of_mem hp_mem
        have h_mon : ∀ k < ch.length, (ch.getD k (∅, ∅)).1 ⊆ Bx ∧ (ch.getD k (∅, ∅)).2 ⊆ z := by
          intro k hk
          have hrev : ∀ s, k + s < ch.length →
              (ch.getD k (∅, ∅)).1 ⊆ (ch.getD (k + s) (∅, ∅)).1 ∧
              (ch.getD k (∅, ∅)).2 ⊆ (ch.getD (k + s) (∅, ∅)).2 := by
            intro s
            induction s with
            | zero => intro _; exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
            | succ s ihs =>
              intro hks
              obtain ⟨ih1, ih2⟩ := ihs (by omega)
              have hst := hstep (k + s) hks
              change (∃ i, R (ch.getD (k + s) (∅, ∅)).1 < R (insert i (ch.getD (k + s) (∅, ∅)).1) ∧
                  (ch.getD (k + s + 1) (∅, ∅)).1 = insert i (ch.getD (k + s) (∅, ∅)).1 ∧
                  (ch.getD (k + s + 1) (∅, ∅)).2 = (ch.getD (k + s) (∅, ∅)).2) ∨
                (∃ j, j ∉ (ch.getD (k + s) (∅, ∅)).2 ∧
                  (ch.getD (k + s + 1) (∅, ∅)).1 = (ch.getD (k + s) (∅, ∅)).1 ∧
                  (ch.getD (k + s + 1) (∅, ∅)).2 = insert j (ch.getD (k + s) (∅, ∅)).2) at hst
              rcases hst with ⟨i, _, hx2, hz2⟩ | ⟨j, _, hx2, hz2⟩
              · rw [show k + (s + 1) = k + s + 1 by omega, hx2, hz2]; exact ⟨ih1.trans (Finset.subset_insert _ _), ih2⟩
              · rw [show k + (s + 1) = k + s + 1 by omega, hx2, hz2]; exact ⟨ih1, ih2.trans (Finset.subset_insert _ _)⟩
          have hfin := hrev (ch.length - 1 - k) (by omega)
          have hlast_eq : ch.getD (k + (ch.length - 1 - k)) (∅, ∅) = ch.getLast hne := by
            rw [show k + (ch.length - 1 - k) = ch.length - 1 by omega, List.getLast_eq_getElem,
                List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          rw [hlast_eq, hlst] at hfin
          exact hfin
        have h1 := h_mon k hk
        have hgetk' : ch.getD k (∅, ∅) = p := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact hgetk
        rw [hgetk'] at h1
        exact ⟨h1.1.trans hBxx, h1.2⟩
      apply hconst_contra ch hne (by rw [hlen, hBx_card]; exact hcase) hstep true
      intro p hp_mem
      have hsubp := h_sub_chain p hp_mem
      have hle := hP_mono p.1 x p.2 z hsubp.1 hsubp.2
      rw [hp] at hle
      have hpf : P.eval (pairVec n m p.1 p.2) = false := by
        cases hv : P.eval (pairVec n m p.1 p.2)
        · rfl
        · rw [hv] at hle; exact absurd hle not_true_le_false
      rw [hP_eval p.1 p.2, hpf]; rfl

end Conjunct3

section Conjunct4

def inpU (n : ℕ) (y : Finset (Fin n)) : List Bool :=
  bits n y ++ [false, true]

lemma inpU_length (n : ℕ) (y : Finset (Fin n)) : (inpU n y).length = n + 2 := by
  simp [inpU, bits]

lemma inpU_getD_fin (n : ℕ) (y : Finset (Fin n)) (i : Fin n) :
    (inpU n y).getD i.val false = decide (i ∈ y) := by
  dsimp only [inpU, bits]
  rw [getD_append_left _ _ i.val false (by simp)]
  simp [List.getD_eq_getElem?_getD, i.isLt]

lemma inpU_getD_false (n : ℕ) (y : Finset (Fin n)) :
    (inpU n y).getD n false = false := by
  dsimp only [inpU, bits]
  rw [getD_append_right _ _ n false (by simp)]
  simp

lemma inpU_getD_true (n : ℕ) (y : Finset (Fin n)) :
    (inpU n y).getD (n + 1) false = true := by
  dsimp only [inpU, bits]
  rw [getD_append_right _ _ (n + 1) false (by simp)]
  simp

def inlineCircuit (base n : ℕ) (gs : List Gate) (inMap : ℕ → ℕ) (U : Circuit) : List Gate × ℕ :=
  let off := base + gs.length
  let remap : ℕ → ℕ := fun w => if w < n + 2 then inMap w else off + (w - (n + 2))
  let extra : List Gate := U.gates.map (fun g : Gate => Gate.mk g.op (g.inputs.map remap))
  (gs ++ extra, remap U.output)

lemma inlineCircuit_spec (base n : ℕ) (gs : List Gate) (inMap : ℕ → ℕ) (U : Circuit)
    (hfanU : FanInTwo U) (hrbU : ReadsBack (n + 2) U) (houtU : U.output < n + 2 + U.size)
    (hinMap : ∀ w < n + 2, inMap w < base + gs.length) :
    let r := inlineCircuit base n gs inMap U
    Extends base gs r.1 ∧
    r.1.length = gs.length + U.size ∧
    r.2 < base + r.1.length ∧
    ∀ (initW uIn : List Bool), initW.length = base → uIn.length = n + 2 →
      (∀ w < n + 2, (wiresFrom gs initW).getD (inMap w) false = uIn.getD w false) →
      (wiresFrom r.1 initW).getD r.2 false = U.eval uIn := by
  dsimp only [inlineCircuit]
  set off := base + gs.length
  let remap : ℕ → ℕ := fun w => if w < n + 2 then inMap w else off + (w - (n + 2))
  set extra : List Gate := U.gates.map (fun g : Gate => Gate.mk g.op (g.inputs.map remap))
  have hext : Extends base gs (gs ++ extra) := by
    refine ⟨extra, rfl, ?_, ?_⟩
    · intro g hg
      simp only [extra, List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have hf := hfanU g' hg'
      exact ⟨hf.1, by simp [hf.2]⟩
    · intro j hj i hi
      have hj' : j < U.gates.length := by simp [extra] at hj; exact hj
      rw [gateAt_eq_getElem _ j hj] at hi
      have hg' : extra[j] = ⟨U.gates[j].op, U.gates[j].inputs.map remap⟩ := by simp [extra]
      rw [hg'] at hi
      simp only [List.mem_map] at hi
      obtain ⟨w, hw, rfl⟩ := hi
      have hrbj := hrbU j hj' w (by rw [gateAt_eq_getElem _ j hj']; exact hw)
      dsimp only [remap]
      split_ifs with hwn
      · have := hinMap w hwn; omega
      · omega
  have hlen : (gs ++ extra).length = gs.length + U.size := by simp [extra, Circuit.size]
  have hout_lt : remap U.output < base + (gs ++ extra).length := by
    dsimp only [remap]; split_ifs with h1
    · have := hinMap U.output h1; omega
    · rw [hlen]; omega
  refine ⟨hext, hlen, hout_lt, ?_⟩
  intro initW uIn hlenI hlenU hin_eq
  have hind : ∀ k ≤ U.gates.length, ∀ w < n + 2 + k,
      (wiresFrom (extra.take k) (wiresFrom gs initW)).getD (remap w) false =
      (wiresFrom (U.gates.take k) uIn).getD w false := by
    intro k
    induction k with
    | zero =>
      intro _ w hw
      simp only [List.take_zero, wiresFrom_nil]
      have hwn : w < n + 2 := by omega
      dsimp only [remap]
      rw [if_pos hwn]
      exact hin_eq w hwn
    | succ k ih =>
      intro hk w hw
      have hk_lt : k < U.gates.length := by omega
      have hU_split : U.gates.take (k + 1) = U.gates.take k ++ [U.gates[k]] := List.take_succ_eq_append_getElem hk_lt
      have hlen_ex : extra.length = U.gates.length := List.length_map _
      have he_split : extra.take (k + 1) = extra.take k ++ [extra[k]'(by rw [hlen_ex]; exact hk_lt)] :=
        List.take_succ_eq_append_getElem (by rw [hlen_ex]; exact hk_lt)
      rw [hU_split, he_split, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_cons, wiresFrom_nil, wiresFrom_nil]
      have hlenE : (wiresFrom (extra.take k) (wiresFrom gs initW)).length = off + k := by
        rw [wiresFrom_length, wiresFrom_length, hlenI, List.length_take, min_eq_left (by rw [hlen_ex]; omega)]
      have hlenUk : (wiresFrom (U.gates.take k) uIn).length = n + 2 + k := by
        rw [wiresFrom_length, hlenU, List.length_take, min_eq_left (by omega)]
      have hg_eval : (extra[k]'(by rw [hlen_ex]; exact hk_lt)).op.eval
            ((extra[k]'(by rw [hlen_ex]; exact hk_lt)).inputs.map fun i => (wiresFrom (extra.take k) (wiresFrom gs initW)).getD i false) =
          U.gates[k].op.eval (U.gates[k].inputs.map fun i => (wiresFrom (U.gates.take k) uIn).getD i false) := by
        have heg : extra[k]'(by rw [hlen_ex]; exact hk_lt) = Gate.mk U.gates[k].op (U.gates[k].inputs.map remap) := by
          simp only [extra, List.getElem_map]
        rw [heg]
        congr 1
        simp only [List.map_map]
        apply List.map_congr_left
        intro i hi
        have hil : i < n + 2 + k := hrbU k hk_lt i (by rw [gateAt_eq_getElem _ k hk_lt]; exact hi)
        exact ih (by omega) i hil
      rw [hg_eval]
      by_cases hw_lt : w < n + 2 + k
      · have hrm_lt : remap w < off + k := by
          dsimp only [remap]; split_ifs with hwn
          · have := hinMap w hwn; omega
          · omega
        rw [getD_append_left _ _ _ false (by rw [hlenE]; exact hrm_lt),
            getD_append_left _ _ _ false (by rw [hlenUk]; exact hw_lt)]
        exact ih (by omega) w hw_lt
      · have hweq : w = n + 2 + k := by omega
        subst hweq
        have hrm_eq : remap (n + 2 + k) = off + k := by
          dsimp only [remap]; rw [if_neg (by omega)]; omega
        rw [hrm_eq, getD_append_right _ _ (off + k) false (by rw [hlenE]),
            getD_append_right _ _ (n + 2 + k) false (by rw [hlenUk]),
            hlenE, hlenUk, Nat.sub_self, Nat.sub_self]
  have hlen_ex_top : extra.length = U.gates.length := List.length_map _
  have hfull := hind U.gates.length (le_refl _) U.output houtU
  rw [List.take_length, ← hlen_ex_top, List.take_length] at hfull
  rw [wiresFrom_append]
  dsimp only [Circuit.eval, Circuit.wires]
  exact hfull

def greedySet {n : ℕ} (R : Finset (Fin n) → ℕ) (d : ℕ) (x : Finset (Fin n)) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | k + 1 =>
    let S := greedySet R d x k
    if hk : k < n then
      let i : Fin n := ⟨k, hk⟩
      if i ∈ x ∨ R (S.erase i) < d then S else S.erase i
    else S

lemma mem_greedySet_of_le {n : ℕ} (R : Finset (Fin n) → ℕ) (d : ℕ) (x : Finset (Fin n)) :
    ∀ (k : ℕ) (j : Fin n), k ≤ j.val → j ∈ greedySet R d x k := by
  intro k j hj
  induction k with
  | zero => exact Finset.mem_univ j
  | succ k ih =>
    have ih' := ih (by omega)
    dsimp only [greedySet]
    split_ifs with hkn hcond
    · exact ih'
    · refine Finset.mem_erase.mpr ⟨?_, ih'⟩
      intro heq; have hv := congrArg Fin.val heq; dsimp at hv; omega
    · exact ih'

lemma greedySet_props {n : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R) (x : Finset (Fin n)) :
    let d := R Finset.univ
    ∀ k ≤ n,
      x ⊆ greedySet R d x k ∧
      R (greedySet R d x k) = d ∧
      ∀ j : Fin n, j.val < k → j ∈ greedySet R d x k → j ∉ x → R ((greedySet R d x k).erase j) < d := by
  intro d k hk
  induction k with
  | zero =>
    dsimp only [greedySet]
    exact ⟨Finset.subset_univ x, rfl, fun j hj => by omega⟩
  | succ k ih =>
    obtain ⟨ih_sub, ih_rk, ih_min⟩ := ih (by omega)
    dsimp only [greedySet]
    rw [dif_pos (by omega : k < n)]
    set S := greedySet R d x k
    let ik : Fin n := ⟨k, hk⟩
    by_cases hcond : ik ∈ x ∨ R (S.erase ik) < d
    · rw [if_pos hcond]
      refine ⟨ih_sub, ih_rk, fun j hj hjs hjx => ?_⟩
      by_cases hjk : j.val < k
      · exact ih_min j hjk hjs hjx
      · have hik_val : ik.val = k := rfl
        have hj_eq : j = ik := Fin.ext (by omega)
        subst hj_eq
        rcases hcond with h1 | h2
        · exact absurd h1 hjx
        · exact h2
    · rw [if_neg hcond]
      push Not at hcond
      rcases hcond with ⟨hik_not, hr_ge⟩
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        refine Finset.mem_erase.mpr ⟨?_, ih_sub ha⟩
        intro heq; subst heq; exact hik_not ha
      · exact Nat.le_antisymm (hmono (Finset.subset_univ _)) hr_ge
      · intro j hj hjs hjx
        have hj_ne : j ≠ ik := fun heq => by subst heq; exact (Finset.mem_erase.mp hjs).1 rfl
        have hik_val : ik.val = k := rfl
        have hjk : j.val < k := by have := Fin.val_ne_of_ne hj_ne; omega
        have h1 := ih_min j hjk (Finset.mem_erase.mp hjs).2 hjx
        have hsub_er : (S.erase ik).erase j ⊆ S.erase j := Finset.erase_subset_erase j (Finset.erase_subset ik S)
        exact lt_of_le_of_lt (hmono hsub_er) h1

lemma matroid_gain_iff_swap {n : ℕ} (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hcard : ∀ x, R x ≤ x.card) (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (x S : Finset (Fin n)) (hxS : x ⊆ S) (hRS : R S = R Finset.univ)
    (hmin : ∀ j ∈ S, j ∉ x → R (S.erase j) < R Finset.univ) (i : Fin n) :
    R x < R (insert i x) ↔ (i ∉ x ∧ ∃ j ∈ S, j ∉ x ∧ R Finset.univ ≤ R (insert i (S.erase j))) := by
  let d := R Finset.univ
  constructor
  · intro hinc
    have hi_not : i ∉ x := fun hix => by rw [Finset.insert_eq_of_mem hix] at hinc; exact Nat.lt_irrefl _ hinc
    refine ⟨hi_not, ?_⟩
    by_contra hall
    push Not at hall
    have h_ind : ∀ m : ℕ, ∀ T : Finset (Fin n), x ⊆ T → T ⊆ S → (S \ T).card = m →
        R (insert i T) = R T := by
      intro m
      induction m with
      | zero =>
        intro T _ hTS hm
        have hST : S = T := Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp hm)) hTS
        subst hST
        exact Nat.le_antisymm (by rw [hRS]; exact hmono (Finset.subset_univ _)) (hmono (Finset.subset_insert _ _))
      | succ m ihm =>
        intro T hxT hTS hm
        have hne : (S \ T).Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨j, hj⟩ := hne
        obtain ⟨hjS, hjT⟩ := Finset.mem_sdiff.mp hj
        have hjx : j ∉ x := fun h => hjT (hxT h)
        let T' := insert j T
        have hxT' : x ⊆ T' := hxT.trans (Finset.subset_insert j T)
        have hT'S : T' ⊆ S := Finset.insert_subset hjS hTS
        have hm' : (S \ T').card = m := by
          have hs : S \ T' = (S \ T).erase j := by
            ext a; simp only [Finset.mem_sdiff, Finset.mem_erase, T', Finset.mem_insert]; tauto
          rw [hs, Finset.card_erase_of_mem hj, hm]; omega
        have hRT' := ihm T' hxT' hT'S hm'
        have hj_in_S_erase : R (S.erase j) < d := hmin j hjS hjx
        have h_swap : R (insert i (S.erase j)) < d := hall j hjS hjx
        have hu1 : T' ∪ S.erase j = S := by
          ext a; simp only [Finset.mem_union, T', Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ((rfl | ha) | ⟨_, ha⟩) <;> [exact hjS; exact hTS ha; exact ha]
          · intro ha; by_cases haj : a = j
            · exact Or.inl (Or.inl haj)
            · exact Or.inr ⟨haj, ha⟩
        have hi1 : T' ∩ S.erase j = T := by
          ext a; simp only [Finset.mem_inter, T', Finset.mem_insert, Finset.mem_erase]
          constructor
          · rintro ⟨rfl | ha, hne, _⟩
            · exact absurd rfl hne
            · exact ha
          · intro ha; refine ⟨Or.inr ha, fun heq => hjT (heq ▸ ha), hTS ha⟩
        have hs1 := hsub T' (S.erase j)
        rw [hu1, hi1, hRS] at hs1
        have hu2 : insert i T' ∪ insert i (S.erase j) = insert i S := by
          conv_rhs => rw [← hu1]
          ext a; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        have hi2 : insert i T' ∩ insert i (S.erase j) = insert i T := by
          rw [← hi1]; ext a; simp only [Finset.mem_inter, Finset.mem_insert]; tauto
        have hs2 := hsub (insert i T') (insert i (S.erase j))
        rw [hu2, hi2] at hs2
        have h_iS : d ≤ R (insert i S) := by dsimp only [d]; rw [← hRS]; exact hmono (Finset.subset_insert _ _)
        have h_T'le := rk_ins_le R hcard hsub T j
        change R T' ≤ R T + 1 at h_T'le
        exact Nat.le_antisymm (by omega) (hmono (Finset.subset_insert i T))
    have heq := h_ind (S \ x).card x (Finset.Subset.refl x) hxS rfl
    omega
  · rintro ⟨hi_not, j, hjS, hjx, hswap⟩
    have hj_min : R (S.erase j) < d := hmin j hjS hjx
    have hi_not_er : i ∉ S.erase j := fun him => by
      have hins : insert i (S.erase j) = S.erase j := Finset.insert_eq_of_mem him
      rw [hins] at hswap; omega
    have hu : insert i x ∪ S.erase j = insert i (S.erase j) := by
      ext a; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ((rfl | ha) | ⟨hne, ha⟩)
        · exact Or.inl rfl
        · exact Or.inr ⟨fun heq => hjx (heq ▸ ha), hxS ha⟩
        · exact Or.inr ⟨hne, ha⟩
      · rintro (rfl | ⟨hne, ha⟩)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨hne, ha⟩
    have hi : insert i x ∩ S.erase j = x := by
      ext a; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨rfl | ha, hne, haS⟩
        · exact absurd (Finset.mem_erase.mpr ⟨hne, haS⟩) hi_not_er
        · exact ha
      · intro ha; exact ⟨Or.inr ha, fun heq => hjx (heq ▸ ha), hxS ha⟩
    have h1 := hsub (insert i x) (S.erase j)
    rw [hu, hi] at h1
    omega

def greedyStep (n base zeroWire oneWire : ℕ) (U : Circuit) (k : ℕ) (inS : List ℕ) (gs : List Gate) :
    List Gate × List ℕ :=
  let inMap : ℕ → ℕ := fun w =>
    if w < n then (if w = k then zeroWire else inS.getD w zeroWire)
    else if w = n then zeroWire else oneWire
  let rU := inlineCircuit base n gs inMap U
  let rN := emitNot base rU.1 rU.2
  let rO := emitOr base rN.1 k rN.2
  (rO.1, inS.take k ++ [rO.2] ++ inS.drop (k + 1))

def greedyLoop (n base zeroWire oneWire : ℕ) (U : Circuit) : ℕ → List ℕ → List Gate → List Gate × List ℕ
  | 0, inS, gs => (gs, inS)
  | k + 1, inS, gs =>
    let rr := greedyLoop n base zeroWire oneWire U k inS gs
    greedyStep n base zeroWire oneWire U k rr.2 rr.1

lemma greedyStep_spec (n : ℕ) (R : Finset (Fin n) → ℕ) (hmono : Monotone R) (U : Circuit)
    (hfanU : FanInTwo U) (hrbU : ReadsBack (n + 2) U) (houtU : U.output < n + 2 + U.size)
    (hU_eval : ∀ y : Finset (Fin n), U.eval (inpU n y) = decide (R Finset.univ ≤ R y)) :
    let base := n + 2
    let zeroWire := n
    let oneWire := n + 1
    ∀ (k : ℕ) (hk : k < n) (inS : List ℕ) (gs : List Gate),
      inS.length = n → (∀ w ∈ inS, w < base + gs.length) →
      let r := greedyStep n base zeroWire oneWire U k inS gs
      Extends base gs r.1 ∧
      r.1.length = gs.length + (U.size + 2) ∧
      r.2.length = n ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      ∀ (x : Finset (Fin n)),
        (∀ j : Fin n, (wiresFrom gs (inpU n x)).getD (inS.getD j.val zeroWire) false =
          decide (j ∈ greedySet R (R Finset.univ) x k)) →
        ∀ j : Fin n, (wiresFrom r.1 (inpU n x)).getD (r.2.getD j.val zeroWire) false =
          decide (j ∈ greedySet R (R Finset.univ) x (k + 1)) := by
  intro base zeroWire oneWire k hk inS gs hlen hlt
  dsimp only [greedyStep]
  let inMap : ℕ → ℕ := fun w =>
    if w < n then (if w = k then zeroWire else inS.getD w zeroWire)
    else if w = n then zeroWire else oneWire
  have hinMap : ∀ w < n + 2, inMap w < base + gs.length := fun w hw => by
    dsimp only [inMap]
    split_ifs with h1 h2
    · omega
    · have := hlt _ (getD_mem inS w zeroWire (by omega)); exact this
    · omega
    · omega
  set rU := inlineCircuit base n gs inMap U with hrU
  have hU := inlineCircuit_spec base n gs inMap U hfanU hrbU houtU hinMap
  rw [← hrU] at hU
  rcases hU with ⟨hextU, hlenU, hltU, hvalU⟩
  set rN := emitNot base rU.1 rU.2 with hrN
  have hN := emitNot_spec base rU.1 rU.2 hltU
  rw [← hrN] at hN
  rcases hN with ⟨hextN, hltN, _, _, hvalN⟩
  set rO := emitOr base rN.1 k rN.2 with hrO
  have hglU := hextU.length_le
  have hglN := hextN.length_le
  have hO := emitOr_spec base rN.1 k rN.2 (by omega) hltN
  rw [← hrO] at hO
  rcases hO with ⟨hextO, hltO, _, _, hvalO⟩
  have hglO := hextO.length_le
  have hextAll := (hextU.trans hextN).trans hextO
  have hlen_out : (inS.take k ++ [rO.2] ++ inS.drop (k + 1)).length = n := by
    simp [List.length_take, List.length_drop, hlen]; omega
  have hlenN_len : rN.1.length = rU.1.length + 1 := by simp [emitNot, hrN]
  have hlenO_len : rO.1.length = rN.1.length + 1 := by simp [emitOr, hrO]
  refine ⟨hextAll, by omega, hlen_out, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with (hw | rfl) | hw
    · have := hlt w (List.mem_of_mem_take hw); omega
    · exact hltO
    · have := hlt w (List.mem_of_mem_drop hw); omega
  · intro x hxS j
    have hlen_in : (inpU n x).length = base := inpU_length n x
    let S := greedySet R (R Finset.univ) x k
    let ik : Fin n := ⟨k, hk⟩
    have hU_val : (wiresFrom rU.1 (inpU n x)).getD rU.2 false =
        decide (R Finset.univ ≤ R (S.erase ik)) := by
      rw [hvalU (inpU n x) (inpU n (S.erase ik)) hlen_in (inpU_length n (S.erase ik)) ?_, hU_eval (S.erase ik)]
      intro w hw
      dsimp only [inMap]
      by_cases hwn : w < n
      · rw [if_pos hwn]
        by_cases hwk : w = k
        · subst hwk
          rw [if_pos rfl, wiresFrom_getD_lt _ _ zeroWire (by rw [hlen_in]; omega),
              inpU_getD_false, inpU_getD_fin n (S.erase ik) ik]
          simp [ik]
        · rw [if_neg hwk, hxS ⟨w, hwn⟩, inpU_getD_fin n (S.erase ik) ⟨w, hwn⟩]
          have hne : (⟨w, hwn⟩ : Fin n) ≠ ik := fun h => hwk (congrArg Fin.val h)
          simp [Finset.mem_erase, hne, S]
      · rw [if_neg hwn]
        by_cases hweq : w = n
        · rw [if_pos hweq, wiresFrom_getD_lt _ _ zeroWire (by rw [hlen_in]; omega), inpU_getD_false]
          subst hweq; rw [inpU_getD_false]
        · rw [if_neg hweq, wiresFrom_getD_lt _ _ oneWire (by rw [hlen_in]; omega), inpU_getD_true]
          have : w = n + 1 := by omega
          subst this; rw [inpU_getD_true]
    have hO_val : (wiresFrom rO.1 (inpU n x)).getD rO.2 false =
        decide (ik ∈ x ∨ R (S.erase ik) < R Finset.univ) := by
      rw [hvalO _ hlen_in, (hextU.trans hextN).wire_eq _ hlen_in k (by omega),
          wiresFrom_getD_lt _ _ k (by rw [hlen_in]; omega), inpU_getD_fin n x ik,
          hvalN _ hlen_in, hU_val]
      by_cases hix : ik ∈ x <;> by_cases hrk : R Finset.univ ≤ R (S.erase ik) <;> simp [hix, hrk]; omega
    simp only [greedySet, dif_pos hk]
    by_cases hjk : j.val < k
    · have hget : (inS.take k ++ [rO.2] ++ inS.drop (k + 1)).getD j.val zeroWire = inS.getD j.val zeroWire := by
        rw [getD_append_left _ _ j.val zeroWire (by simp [List.length_take, hlen]; omega),
            getD_append_left _ _ j.val zeroWire (by simp [List.length_take, hlen]; omega),
            getD_take inS k j.val zeroWire hjk]
      rw [hget, hextAll.wire_eq _ hlen_in _ (hlt _ (getD_mem inS j.val zeroWire (by rw [hlen]; exact j.isLt))), hxS j]
      split_ifs with hcond
      · rfl
      · have hne : j ≠ ⟨k, hk⟩ := fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega
        simp [Finset.mem_erase, hne, S]
    · by_cases hjeq : j.val = k
      · have hj_eq : j = ik := Fin.ext hjeq
        subst hj_eq
        have hget : (inS.take k ++ [rO.2] ++ inS.drop (k + 1)).getD ik.val zeroWire = rO.2 := by
          rw [getD_append_left _ _ ik.val zeroWire (by simp [List.length_take, hlen]; omega),
              getD_append_right _ _ ik.val zeroWire (by simp [List.length_take, hlen]; omega),
              List.length_take, min_eq_left (by omega), Nat.sub_self]; rfl
        rw [hget, hO_val]
        dsimp only [S, ik] at *
        have hk_mem : (⟨k, hk⟩ : Fin n) ∈ greedySet R (R Finset.univ) x k :=
          mem_greedySet_of_le R (R Finset.univ) x k ⟨k, hk⟩ (le_refl k)
        by_cases hcond : (⟨k, hk⟩ : Fin n) ∈ x ∨ R ((greedySet R (R Finset.univ) x k).erase ⟨k, hk⟩) < R Finset.univ
        · rw [if_pos hcond]; apply Bool.eq_iff_iff.mpr; simp [hcond, hk_mem]
        · rw [if_neg hcond]
          have hmem : (⟨k, hk⟩ : Fin n) ∉ (greedySet R (R Finset.univ) x k).erase ⟨k, hk⟩ := Finset.notMem_erase _ _
          apply Bool.eq_iff_iff.mpr; simp [hcond, hmem]
      · have hjgt : k + 1 ≤ j.val := by omega
        have hlen_pre : (inS.take k ++ [rO.2]).length = k + 1 := by
          rw [List.length_append, List.length_take, List.length_singleton, min_eq_left (by omega)]
        have hget : (inS.take k ++ [rO.2] ++ inS.drop (k + 1)).getD j.val zeroWire = inS.getD j.val zeroWire := by
          rw [getD_append_right _ _ j.val zeroWire (by omega), hlen_pre, getD_drop inS (k + 1) (j.val - (k + 1)) zeroWire,
              show k + 1 + (j.val - (k + 1)) = j.val by omega]
        rw [hget, hextAll.wire_eq _ hlen_in _ (hlt _ (getD_mem inS j.val zeroWire (by rw [hlen]; exact j.isLt))), hxS j]
        split_ifs with hcond
        · rfl
        · have hne : j ≠ ⟨k, hk⟩ := fun h => by have hv := congrArg Fin.val h; dsimp at hv; omega
          simp [Finset.mem_erase, hne, S]

lemma greedyLoop_spec (n : ℕ) (R : Finset (Fin n) → ℕ) (hmono : Monotone R) (U : Circuit)
    (hfanU : FanInTwo U) (hrbU : ReadsBack (n + 2) U) (houtU : U.output < n + 2 + U.size)
    (hU_eval : ∀ y : Finset (Fin n), U.eval (inpU n y) = decide (R Finset.univ ≤ R y)) :
    let base := n + 2
    let zeroWire := n
    let oneWire := n + 1
    ∀ (k : ℕ) (hk : k ≤ n) (inS0 : List ℕ) (gs0 : List Gate),
      inS0.length = n → (∀ w ∈ inS0, w < base + gs0.length) →
      (∀ x j, (wiresFrom gs0 (inpU n x)).getD (inS0.getD j.val zeroWire) false =
        decide (j ∈ greedySet R (R Finset.univ) x 0)) →
      let r := greedyLoop n base zeroWire oneWire U k inS0 gs0
      Extends base gs0 r.1 ∧
      r.1.length = gs0.length + k * (U.size + 2) ∧
      r.2.length = n ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      ∀ x j, (wiresFrom r.1 (inpU n x)).getD (r.2.getD j.val zeroWire) false =
        decide (j ∈ greedySet R (R Finset.univ) x k) := by
  intro base zeroWire oneWire k
  induction k with
  | zero =>
    intro _ inS0 gs0 hlen hlt hinit
    dsimp only [greedyLoop]
    exact ⟨Extends.refl base gs0, by simp, hlen, hlt, hinit⟩
  | succ k ih =>
    intro hk inS0 gs0 hlen hlt hinit
    dsimp only [greedyLoop]
    set rr := greedyLoop n base zeroWire oneWire U k inS0 gs0 with hrr
    have h1 := ih (by omega) inS0 gs0 hlen hlt hinit
    dsimp only at h1; try rw [← hrr] at h1
    rcases h1 with ⟨hext1, hlen1, hlenR, hltR, hvalR⟩
    have h2 := greedyStep_spec n R hmono U hfanU hrbU houtU hU_eval k (by omega) rr.2 rr.1 hlenR hltR
    rcases h2 with ⟨hext2, hlen2, hlenO, hltO, hvalO⟩
    refine ⟨hext1.trans hext2, by rw [hlen2, hlen1]; ring, hlenO, hltO, fun x => hvalO x (hvalR x)⟩

def buildNx (base : ℕ) : List Gate → ℕ → List Gate × List ℕ
  | gs, 0 => (gs, [])
  | gs, k + 1 =>
    let rr := buildNx base gs k
    let rN := emitNot base rr.1 k
    (rN.1, rr.2 ++ [rN.2])

lemma buildNx_spec (n base : ℕ) (hn : n ≤ base) (gs : List Gate) :
    ∀ k ≤ n,
      let r := buildNx base gs k
      Extends base gs r.1 ∧
      r.1.length = gs.length + k ∧
      r.2.length = k ∧
      (∀ w ∈ r.2, w < base + r.1.length) ∧
      ∀ (w : List Bool), w.length = base →
        ∀ j < k, (wiresFrom r.1 w).getD (r.2.getD j 0) false = !(w.getD j false) := by
  intro k
  induction k with
  | zero =>
    intro _
    dsimp only [buildNx]
    exact ⟨Extends.refl base gs, by simp, rfl, fun _ h => by simp at h, fun _ _ _ hj => by omega⟩
  | succ k ih =>
    intro hk
    dsimp only [buildNx]
    set rr := buildNx base gs k with hrr
    have h1 := ih (by omega)
    dsimp only at h1; try rw [← hrr] at h1
    rcases h1 with ⟨hext1, hlen1, hlenR, hltR, hvalR⟩
    set rN := emitNot base rr.1 k with hrN
    have hN := emitNot_spec base rr.1 k (by omega)
    rw [← hrN] at hN
    rcases hN with ⟨hextN, hltN, _, _, hvalN⟩
    have hglN := hextN.length_le
    have hlenN_eq : rN.1.length = rr.1.length + 1 := by simp [emitNot, hrN]
    refine ⟨hext1.trans hextN, by omega, by simp [hlenR], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hltR w hw; omega
      · exact hltN
    · intro w hw j hj
      by_cases hjk : j < k
      · rw [getD_append_left _ _ j 0 (by omega), hextN.wire_eq w hw _ (hltR _ (getD_mem rr.2 j 0 (by omega)))]
        exact hvalR w hw j hjk
      · have hjeq : j = k := by omega
        subst hjeq
        rw [getD_append_right _ _ j 0 (by omega), hlenR, Nat.sub_self]
        change (wiresFrom rN.1 w).getD rN.2 false = _
        rw [hvalN w hw, hext1.wire_eq w hw j (by omega), wiresFrom_getD_lt gs w j (by rw [hw]; omega)]

def swapInner (n base zeroWire oneWire : ℕ) (U : Circuit) (inS nx : List ℕ) (i : ℕ) :
    ℕ → List Gate → List Gate × List ℕ
  | 0, gs => (gs, [])
  | j + 1, gs =>
    let rr := swapInner n base zeroWire oneWire U inS nx i j gs
    let inMap : ℕ → ℕ := fun w =>
      if w < n then (if w = i then oneWire else if w = j then zeroWire else inS.getD w zeroWire)
      else if w = n then zeroWire else oneWire
    let rU := inlineCircuit base n rr.1 inMap U
    let rA1 := emitAnd base rU.1 (inS.getD j zeroWire) (nx.getD j zeroWire)
    let rA2 := emitAnd base rA1.1 rU.2 rA1.2
    (rA2.1, rr.2 ++ [rA2.2])

lemma swapInner_spec (n : ℕ) (R : Finset (Fin n) → ℕ) (U : Circuit)
    (hfanU : FanInTwo U) (hrbU : ReadsBack (n + 2) U) (houtU : U.output < n + 2 + U.size)
    (hU_eval : ∀ y : Finset (Fin n), U.eval (inpU n y) = decide (R Finset.univ ≤ R y)) :
    let base := n + 2
    let zeroWire := n
    let oneWire := n + 1
    ∀ (inS nx : List ℕ) (gs : List Gate),
      inS.length = n → nx.length = n →
      (∀ w ∈ inS, w < base + gs.length) → (∀ w ∈ nx, w < base + gs.length) →
      ∀ (i : Fin n) (m : ℕ) (hm : m ≤ n),
        let r := swapInner n base zeroWire oneWire U inS nx i m gs
        Extends base gs r.1 ∧
        r.1.length = gs.length + m * (U.size + 2) ∧
        r.2.length = m ∧
        (∀ w ∈ r.2, w < base + r.1.length) ∧
        ∀ (x S : Finset (Fin n)),
          (∀ j : Fin n, (wiresFrom gs (inpU n x)).getD (inS.getD j.val zeroWire) false = decide (j ∈ S)) →
          (∀ j : Fin n, (wiresFrom gs (inpU n x)).getD (nx.getD j.val zeroWire) false = decide (j ∉ x)) →
          ∀ j : ℕ, j < m →
            ((wiresFrom r.1 (inpU n x)).getD (r.2.getD j 0) false = true ↔
              ∃ hj : j < n, let fj : Fin n := ⟨j, hj⟩
                fj ∈ S ∧ fj ∉ x ∧ R Finset.univ ≤ R (insert i (S.erase fj))) := by
  intro base zeroWire oneWire inS nx gs hinS_len hnx_len hinS_lt hnx_lt i m
  induction m with
  | zero =>
    intro _
    dsimp only [swapInner]
    exact ⟨Extends.refl base gs, by simp, rfl, fun _ h => by simp at h, fun _ _ _ _ _ hj => by omega⟩
  | succ m ih =>
    intro hm
    dsimp only [swapInner]
    set rr := swapInner n base zeroWire oneWire U inS nx i m gs with hrr
    have h1 := ih (by omega)
    dsimp only at h1; try rw [← hrr] at h1
    rcases h1 with ⟨hext1, hlen1, hlenR, hltR, hvalR⟩
    have hgl1 := hext1.length_le
    let inMap : ℕ → ℕ := fun w =>
      if w < n then (if w = i.val then oneWire else if w = m then zeroWire else inS.getD w zeroWire)
      else if w = n then zeroWire else oneWire
    have hinMap : ∀ w < n + 2, inMap w < base + rr.1.length := fun w hw => by
      dsimp only [inMap]
      split_ifs with h1 h2 h3
      · omega
      · omega
      · have := hinS_lt _ (getD_mem inS w zeroWire (by omega)); omega
      · omega
      · omega
    set rU := inlineCircuit base n rr.1 inMap U with hrU
    have hU := inlineCircuit_spec base n rr.1 inMap U hfanU hrbU houtU hinMap
    rw [← hrU] at hU
    rcases hU with ⟨hextU, hlenU, hltU, hvalU⟩
    have hglU := hextU.length_le
    have hm_lt : m < n := by omega
    have hinS_m : inS.getD m zeroWire < base + rU.1.length := by
      have := hinS_lt _ (getD_mem inS m zeroWire (by omega)); omega
    have hnx_m : nx.getD m zeroWire < base + rU.1.length := by
      have := hnx_lt _ (getD_mem nx m zeroWire (by omega)); omega
    set rA1 := emitAnd base rU.1 (inS.getD m zeroWire) (nx.getD m zeroWire) with hrA1
    have hA1 := emitAnd_spec base rU.1 _ _ hinS_m hnx_m
    rw [← hrA1] at hA1
    rcases hA1 with ⟨hextA1, hltA1, _, _, hvalA1⟩
    have hglA1 := hextA1.length_le
    set rA2 := emitAnd base rA1.1 rU.2 rA1.2 with hrA2
    have hA2 := emitAnd_spec base rA1.1 rU.2 rA1.2 (by omega) hltA1
    rw [← hrA2] at hA2
    rcases hA2 with ⟨hextA2, hltA2, _, _, hvalA2⟩
    have hglA2 := hextA2.length_le
    have hextStep := (hextU.trans hextA1).trans hextA2
    have hlenA1 : rA1.1.length = rU.1.length + 1 := by simp [emitAnd, hrA1]
    have hlenA2 : rA2.1.length = rA1.1.length + 1 := by simp [emitAnd, hrA2]
    refine ⟨hext1.trans hextStep, by rw [hlenA2, hlenA1, hlenU, hlen1]; ring,
      by simp [hlenR], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hltR w hw; omega
      · exact hltA2
    · intro x S hxS hnx j hj
      have hlen_in : (inpU n x).length = base := inpU_length n x
      by_cases hjm : j < m
      · rw [getD_append_left _ _ j 0 (by omega), hextStep.wire_eq _ hlen_in _ (hltR _ (getD_mem rr.2 j 0 (by omega)))]
        exact hvalR x S hxS hnx j hjm
      · have hjeq : j = m := by omega
        subst hjeq
        rw [getD_append_right _ _ j 0 (by omega), hlenR, Nat.sub_self]
        change (wiresFrom rA2.1 (inpU n x)).getD rA2.2 false = true ↔ _
        let fm : Fin n := ⟨j, hm_lt⟩
        have hU_val : (wiresFrom rU.1 (inpU n x)).getD rU.2 false =
            decide (R Finset.univ ≤ R (insert i (S.erase fm))) := by
          rw [hvalU (inpU n x) (inpU n (insert i (S.erase fm))) hlen_in (inpU_length n _) ?_, hU_eval]
          intro w hw
          dsimp only [inMap]
          by_cases hwn : w < n
          · rw [if_pos hwn]
            by_cases hwi : w = i.val
            · have heq : (⟨w, hwn⟩ : Fin n) = i := Fin.ext hwi
              rw [if_pos hwi, hext1.wire_eq _ hlen_in oneWire (by omega),
                  wiresFrom_getD_lt _ _ oneWire (by rw [hlen_in]; omega), inpU_getD_true,
                  show w = (⟨w, hwn⟩ : Fin n).val from rfl, inpU_getD_fin, heq]
              simp
            · rw [if_neg hwi]
              by_cases hwj : w = j
              · have heq : (⟨w, hwn⟩ : Fin n) = fm := Fin.ext hwj
                rw [if_pos hwj, hext1.wire_eq _ hlen_in zeroWire (by omega),
                    wiresFrom_getD_lt _ _ zeroWire (by rw [hlen_in]; omega), inpU_getD_false,
                    show w = (⟨w, hwn⟩ : Fin n).val from rfl, inpU_getD_fin, heq]
                have hne : fm ≠ i := fun h => hwi (by rw [← h, hwj])
                simp [Finset.mem_insert, Finset.mem_erase, hne]
              · rw [if_neg hwj, hext1.wire_eq _ hlen_in _ (hinS_lt _ (getD_mem inS w zeroWire (by omega))),
                    hxS ⟨w, hwn⟩]
                conv_rhs => rw [show w = (⟨w, hwn⟩ : Fin n).val from rfl, inpU_getD_fin]
                have hne_i : (⟨w, hwn⟩ : Fin n) ≠ i := fun h => hwi (congrArg Fin.val h)
                have hne_j : (⟨w, hwn⟩ : Fin n) ≠ fm := fun h => hwj (congrArg Fin.val h)
                simp [Finset.mem_insert, Finset.mem_erase, hne_i, hne_j]
          · rw [if_neg hwn]
            by_cases hwn2 : w = n
            · rw [if_pos hwn2, hext1.wire_eq _ hlen_in zeroWire (by omega),
                  wiresFrom_getD_lt _ _ zeroWire (by rw [hlen_in]; omega), inpU_getD_false]
              subst hwn2; rw [inpU_getD_false]
            · rw [if_neg hwn2, hext1.wire_eq _ hlen_in oneWire (by omega),
                  wiresFrom_getD_lt _ _ oneWire (by rw [hlen_in]; omega), inpU_getD_true]
              have : w = n + 1 := by omega
              subst this; rw [inpU_getD_true]
        rw [hvalA2 _ hlen_in, Bool.and_eq_true, hextA1.wire_eq _ hlen_in _ hltU, hU_val,
            hvalA1 _ hlen_in, Bool.and_eq_true,
            hextU.wire_eq _ hlen_in _ (by have := hinS_lt _ (getD_mem inS j zeroWire (by omega)); omega),
            hext1.wire_eq _ hlen_in _ (hinS_lt _ (getD_mem inS j zeroWire (by omega))),
            hextU.wire_eq _ hlen_in _ (by have := hnx_lt _ (getD_mem nx j zeroWire (by omega)); omega),
            hext1.wire_eq _ hlen_in _ (hnx_lt _ (getD_mem nx j zeroWire (by omega))),
            hxS fm, hnx fm]
        simp only [decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨hm_lt, h2, h3, h1⟩
        · rintro ⟨_, h2, h3, h1⟩; exact ⟨h1, h2, h3⟩

def swapOuter (n base zeroWire oneWire : ℕ) (U : Circuit) (inS nx : List ℕ) :
    ℕ → List Gate → List Gate × List ℕ
  | 0, gs => (gs, [])
  | i + 1, gs =>
    let rr := swapOuter n base zeroWire oneWire U inS nx i gs
    let rIn :=
      if hi : i < n then swapInner n base zeroWire oneWire U inS nx i n rr.1
      else (rr.1, [])
    let rOr := emitOrList base zeroWire rIn.1 rIn.2
    let rOut := emitAnd base rOr.1 (nx.getD i zeroWire) rOr.2
    (rOut.1, rr.2 ++ [rOut.2])

lemma swapOuter_spec (n : ℕ) (R : Finset (Fin n) → ℕ) (hmono : Monotone R)
    (hcard : ∀ x, R x ≤ x.card) (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y)
    (U : Circuit) (hfanU : FanInTwo U) (hrbU : ReadsBack (n + 2) U) (houtU : U.output < n + 2 + U.size)
    (hU_eval : ∀ y : Finset (Fin n), U.eval (inpU n y) = decide (R Finset.univ ≤ R y)) :
    let base := n + 2
    let zeroWire := n
    let oneWire := n + 1
    ∀ (inS nx : List ℕ) (gs : List Gate),
      inS.length = n → nx.length = n →
      (∀ w ∈ inS, w < base + gs.length) → (∀ w ∈ nx, w < base + gs.length) →
      ∀ (m : ℕ) (hm : m ≤ n),
        let r := swapOuter n base zeroWire oneWire U inS nx m gs
        Extends base gs r.1 ∧
        r.1.length ≤ gs.length + m * (n * (U.size + 2) + n + 1) ∧
        r.2.length = m ∧
        (∀ w ∈ r.2, w < base + r.1.length) ∧
        ∀ (x S : Finset (Fin n)), x ⊆ S → R S = R Finset.univ →
          (∀ j ∈ S, j ∉ x → R (S.erase j) < R Finset.univ) →
          (∀ j : Fin n, (wiresFrom gs (inpU n x)).getD (inS.getD j.val zeroWire) false = decide (j ∈ S)) →
          (∀ j : Fin n, (wiresFrom gs (inpU n x)).getD (nx.getD j.val zeroWire) false = decide (j ∉ x)) →
          ∀ i : Fin n, i.val < m →
            (wiresFrom r.1 (inpU n x)).getD (r.2.getD i.val 0) false = decide (R x < R (insert i x)) := by
  intro base zeroWire oneWire inS nx gs hinS_len hnx_len hinS_lt hnx_lt m
  induction m with
  | zero =>
    intro _
    dsimp only [swapOuter]
    exact ⟨Extends.refl base gs, by simp, rfl, fun _ h => by simp at h, fun _ _ _ _ _ _ _ i hi => by omega⟩
  | succ m ih =>
    intro hm
    dsimp only [swapOuter]
    have hm_lt : m < n := by omega
    set rr := swapOuter n base zeroWire oneWire U inS nx m gs with hrr
    have h1 := ih (by omega)
    dsimp only at h1; try rw [← hrr] at h1
    rcases h1 with ⟨hext1, hlen1, hlenR, hltR, hvalR⟩
    have hgl1 := hext1.length_le
    rw [dif_pos hm_lt]
    set rIn := swapInner n base zeroWire oneWire U inS nx m n rr.1 with hrIn
    have hIn := swapInner_spec n R U hfanU hrbU houtU hU_eval inS nx rr.1 hinS_len hnx_len
      (fun w hw => lt_of_lt_of_le (hinS_lt w hw) (Nat.add_le_add_left hgl1 base))
      (fun w hw => lt_of_lt_of_le (hnx_lt w hw) (Nat.add_le_add_left hgl1 base)) ⟨m, hm_lt⟩ n (le_refl n)
    rw [← hrIn] at hIn
    rcases hIn with ⟨hextIn, hlenIn, hlenIn2, hltIn, hvalIn⟩
    have hglIn := hextIn.length_le
    set rOr := emitOrList base zeroWire rIn.1 rIn.2 with hrOr
    have hOr := emitOrList_spec base rIn.2 zeroWire rIn.1 (by omega) hltIn
    rw [← hrOr] at hOr
    rcases hOr with ⟨hextOr, hltOr, hncOr, hnnOr, hvalOr⟩
    have hglOr := hextOr.length_le
    have hlen_or_diff : rOr.1.length ≤ rIn.1.length + n := by
      have hsub := notCount_le_length rOr.1 0
      have hsub2 := notCount_le_length rIn.1 0
      dsimp only [nonNot] at hnnOr
      omega
    have hnx_m_lt : nx.getD m zeroWire < base + rOr.1.length := by
      have := hnx_lt _ (getD_mem nx m zeroWire (by rw [hnx_len]; exact hm_lt)); omega
    set rOut := emitAnd base rOr.1 (nx.getD m zeroWire) rOr.2 with hrOut
    have hOut := emitAnd_spec base rOr.1 (nx.getD m zeroWire) rOr.2 hnx_m_lt hltOr
    rw [← hrOut] at hOut
    rcases hOut with ⟨hextOut, hltOut, _, _, hvalOut⟩
    have hglOut := hextOut.length_le
    have hextStep := (hextIn.trans hextOr).trans hextOut
    have hlen_tot : rOut.1.length ≤ gs.length + (m + 1) * (n * (U.size + 2) + n + 1) := by
      have hlo : rOut.1.length = rOr.1.length + 1 := by simp [emitAnd, hrOut]
      rw [hlo]
      have : gs.length + (m + 1) * (n * (U.size + 2) + n + 1) =
          gs.length + m * (n * (U.size + 2) + n + 1) + (n * (U.size + 2) + n + 1) := by ring
      omega
    refine ⟨hext1.trans hextStep, hlen_tot, by simp [hlenR], ?_, ?_⟩
    · intro w hw
      simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · have := hltR w hw; omega
      · exact hltOut
    · intro x S hxS hRS hmin hxS_w hnx_w i hi
      have hlen_in : (inpU n x).length = base := inpU_length n x
      by_cases him : i.val < m
      · rw [getD_append_left _ _ i.val 0 (by omega), hextStep.wire_eq _ hlen_in _ (hltR _ (getD_mem rr.2 i.val 0 (by omega)))]
        exact hvalR x S hxS hRS hmin hxS_w hnx_w i him
      · have hieq : i = ⟨m, hm_lt⟩ := Fin.ext (by dsimp; omega)
        subst hieq
        rw [getD_append_right _ _ m 0 (by omega), hlenR, Nat.sub_self]
        change (wiresFrom rOut.1 (inpU n x)).getD rOut.2 false = _
        have hnx_rr : ∀ j : Fin n, (wiresFrom rr.1 (inpU n x)).getD (nx.getD j.val zeroWire) false = decide (j ∉ x) := by
          intro j
          rw [hext1.wire_eq _ hlen_in _ (hnx_lt _ (getD_mem nx j.val zeroWire (by rw [hnx_len]; exact j.isLt))), hnx_w j]
        have hxS_rr : ∀ j : Fin n, (wiresFrom rr.1 (inpU n x)).getD (inS.getD j.val zeroWire) false = decide (j ∈ S) := by
          intro j
          rw [hext1.wire_eq _ hlen_in _ (hinS_lt _ (getD_mem inS j.val zeroWire (by rw [hinS_len]; exact j.isLt))), hxS_w j]
        have hIn_iff := hvalIn x S hxS_rr hnx_rr
        have hOr_iff : (wiresFrom rOr.1 (inpU n x)).getD rOr.2 false = true ↔
            ∃ j ∈ S, j ∉ x ∧ R Finset.univ ≤ R (insert ⟨m, hm_lt⟩ (S.erase j)) := by
          rw [hvalOr _ hlen_in, hextIn.wire_eq _ hlen_in zeroWire (by omega),
              hext1.wire_eq _ hlen_in zeroWire (by omega),
              wiresFrom_getD_lt _ _ zeroWire (by rw [hlen_in]; omega), inpU_getD_false, Bool.false_or,
              List.any_eq_true]
          constructor
          · rintro ⟨w, hw_mem, hw_t⟩
            obtain ⟨k, hk, hgetk⟩ := List.getElem_of_mem hw_mem
            have hk_lt : k < n := by rw [← hlenIn2]; exact hk
            have hk_eq : rIn.2.getD k 0 = w := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]; exact hgetk
            rw [← hk_eq] at hw_t
            have h1 := (hIn_iff k hk_lt).mp hw_t
            rcases h1 with ⟨hk', hS', hx', hsw⟩
            exact ⟨⟨k, hk'⟩, hS', hx', hsw⟩
          · rintro ⟨fj, hjS, hjx, hsw⟩
            refine ⟨rIn.2.getD fj.val 0, getD_mem rIn.2 fj.val 0 (by rw [hlenIn2]; exact fj.isLt), ?_⟩
            exact (hIn_iff fj.val fj.isLt).mpr ⟨fj.isLt, hjS, hjx, hsw⟩
        apply Bool.eq_iff_iff.mpr
        rw [hvalOut _ hlen_in, Bool.and_eq_true, hOr_iff,
            hextOr.wire_eq _ hlen_in _ (by have := hnx_lt _ (getD_mem nx m zeroWire (by rw [hnx_len]; exact hm_lt)); omega),
            hextIn.wire_eq _ hlen_in _ (by have := hnx_lt _ (getD_mem nx m zeroWire (by rw [hnx_len]; exact hm_lt)); omega),
            hnx_rr ⟨m, hm_lt⟩, decide_eq_true_eq, decide_eq_true_eq]
        exact (matroid_gain_iff_swap R hmono hcard hsub x S hxS hRS hmin ⟨m, hm_lt⟩).symm

lemma conjunct4_proof (n : ℕ) (R : Finset (Fin n) → ℕ)
    (hmono : Monotone R) (hcard : ∀ x, R x ≤ x.card) (hsub : ∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) :
    let d := R Finset.univ
    ∀ U : Circuit,
      (FanInTwo U ∧ ReadsBack (n + 2) U ∧ U.output < n + 2 + U.size) →
      (∀ x : Finset (Fin n), U.eval (inpU n x) = decide (d ≤ R x)) →
      ∃ G : Circuit,
        (FanInTwo G ∧ ReadsBack (n + 2) G ∧ G.output < n + 2 + G.size) ∧
        G.size ≤ 4 * (n + 1) ^ 2 * (U.size + 2) ∧
        ∃ t : Fin n → Fin (n + 2 + G.size), ∀ (x : Finset (Fin n)) (i : Fin n),
          (G.wires (inpU n x)).getD (t i).val false = decide (R x < R (insert i x)) := by
  intro d U ⟨hfanU, hrbU, houtU⟩ hU_eval
  let base := n + 2
  let zeroWire := n
  let oneWire := n + 1
  let inS0 := List.replicate n oneWire
  have hinS0_len : inS0.length = n := List.length_replicate
  have hinS0_lt : ∀ w ∈ inS0, w < base := fun w hw => by
    rw [List.mem_replicate] at hw; omega
  have hinS0_val : ∀ x (j : Fin n), (wiresFrom [] (inpU n x)).getD (inS0.getD j.val zeroWire) false =
      decide (j ∈ greedySet R d x 0) := by
    intro x j
    have : inS0.getD j.val zeroWire = oneWire := by simp [inS0, List.getD_eq_getElem?_getD, j.isLt]
    rw [this, wiresFrom_nil, inpU_getD_true]
    dsimp only [greedySet]; simp
  let rGr := greedyLoop n base zeroWire oneWire U n inS0 []
  have hGr := greedyLoop_spec n R hmono U hfanU hrbU houtU hU_eval n (le_refl n) inS0 [] hinS0_len hinS0_lt hinS0_val
  dsimp only at hGr
  rcases hGr with ⟨hextGr, hlenGr, hlenS, hltS, hvalS⟩
  have hglGr := hextGr.length_le
  let rNx := buildNx base rGr.1 n
  have hNx := buildNx_spec n base (by omega) rGr.1 n (le_refl n)
  dsimp only at hNx
  rcases hNx with ⟨hextNx, hlenNx, hlenN, hltN, hvalN⟩
  have hglNx := hextNx.length_le
  let rSw := swapOuter n base zeroWire oneWire U rGr.2 rNx.2 n rNx.1
  have hglNx' : rGr.1.length ≤ rNx.1.length := hglNx
  have hSw := swapOuter_spec n R hmono hcard hsub U hfanU hrbU houtU hU_eval rGr.2 rNx.2 rNx.1
    hlenS hlenN (fun w hw => lt_of_lt_of_le (hltS w hw) (Nat.add_le_add_left hglNx' (n + 2))) hltN n (le_refl n)
  dsimp only at hSw
  rcases hSw with ⟨hextSw, hlenSw, hlenOut, hltOut, hvalOut⟩
  have hextAll : Extends base [] rSw.1 := (hextGr.trans hextNx).trans hextSw
  rcases hextAll with ⟨eAll, heqAll, hfanAll, hrbAll⟩
  simp only [List.nil_append, List.length_nil, Nat.add_zero] at heqAll hrbAll
  subst heqAll
  refine ⟨⟨rSw.1, 0⟩, ⟨hfanAll, hrbAll, by simp [Circuit.size]⟩, ?_, ?_⟩
  · change rSw.1.length ≤ 4 * (n + 1) ^ 2 * (U.size + 2)
    have hsz : rSw.1.length ≤ n * (U.size + 2) + n + n * (n * (U.size + 2) + n + 1) := by
      rw [hlenNx, hlenGr] at hlenSw; simp only [List.length_nil, Nat.zero_add] at hlenSw; exact hlenSw
    have hUpos : 2 ≤ U.size + 2 := by omega
    have hsq : n ^ 2 + 2 * n ≤ (n ^ 2 + 2 * n) * (U.size + 2) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  · refine ⟨fun i => ⟨rSw.2.getD i.val 0, by
        have hlt := hltOut _ (getD_mem rSw.2 i.val 0 (by rw [hlenOut]; exact i.isLt))
        change _ < base + rSw.1.length; exact hlt⟩, ?_⟩
    intro x i
    have hlen_in : (inpU n x).length = base := inpU_length n x
    have hgp := greedySet_props R hmono x n (le_refl n)
    rcases hgp with ⟨hxS, hRS, hmin⟩
    have hmin' : ∀ j ∈ greedySet R d x n, j ∉ x → R ((greedySet R d x n).erase j) < d := fun j hj hjx =>
      hmin j j.isLt hj hjx
    have hxS_w : ∀ j : Fin n, (wiresFrom rNx.1 (inpU n x)).getD (rGr.2.getD j.val zeroWire) false =
        decide (j ∈ greedySet R d x n) := fun j => by
      rw [hextNx.wire_eq _ hlen_in _ (hltS _ (getD_mem rGr.2 j.val zeroWire (by rw [hlenS]; exact j.isLt))), hvalS x j]
    have hnx_w : ∀ j : Fin n, (wiresFrom rNx.1 (inpU n x)).getD (rNx.2.getD j.val zeroWire) false =
        decide (j ∉ x) := fun j => by
      have heq_d : rNx.2.getD j.val zeroWire = rNx.2.getD j.val 0 := by
        have hlt_j : j.val < rNx.2.length := by rw [hlenN]; exact j.isLt
        clear * - hlt_j
        generalize rNx.2 = lst at *; generalize j.val = idx at *
        induction lst generalizing idx with
        | nil => simp at hlt_j
        | cons hd tl ih =>
          cases idx with
          | zero => rfl
          | succ idx' => exact ih idx' (by simp at hlt_j; omega)
      rw [heq_d, hvalN (inpU n x) hlen_in j.val j.isLt, inpU_getD_fin]
      by_cases hjx : j ∈ x <;> simp [hjx]
    exact hvalOut x (greedySet R d x n) hxS hRS hmin' hxS_w hnx_w i i.isLt

end Conjunct4

end PEqualNP.Outside.L_lib_1281_aux

theorem PEqualNP.Outside.L_lib_1281 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (a n : Nat) (R : Finset (Fin n) → Nat), n ≤ 2^a →
  R ∅ = 0 → Monotone R → (∀ x, R x ≤ x.card) →
  (∀ x y, R (x ∪ y) + R (x ∩ y) ≤ R x + R y) →
  let h := 2^a
  let b := a+1
  let d := R Finset.univ
  let m := 2*h-1-d
  let N := n+m
  let bits := fun (l : Nat) (x : Finset (Fin l)) => List.ofFn (fun i : Fin l => decide (i ∈ x))
  let valid := fun (w : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (w+2) C ∧ C.output < w+2+C.size
  let fits := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    valid N C ∧ ∃ (old : Fin n → Fin (N+2+C.size)) (pad : Fin m → Fin (N+2+C.size)),
      ∀ x z, let w := C.wires (bits n x ++ bits m z ++ [false,true])
             (∀ i, R x < R (insert i x) → w.getD (old i).val false = true) ∧
             (∀ i ∈ x, w.getD (old i).val false = false) ∧
             (∀ j, w.getD (pad j).val false = decide (j ∉ z))
  (∃ C, fits C ∧ PEqualNP.NotBracket.notCount C = b) ∧
  (∃ C, fits C ∧ PEqualNP.NotBracket.notCount C = b+1 ∧
    C.size ≤ 48*(N+2)*(Nat.log2 (N+2)+2)^2) ∧
  (∀ C, fits C → b ≤ PEqualNP.NotBracket.notCount C ∧
    (PEqualNP.NotBracket.notCount C = b → ∃ P, valid N P ∧ PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size < C.size ∧ ∀ x z, P.eval (bits n x ++ bits m z ++ [false,true]) = decide (h ≤ R x + z.card))) ∧
  ∀ U, valid n U → (∀ x, U.eval (bits n x ++ [false,true]) = decide (d ≤ R x)) →
    ∃ G, valid n G ∧ G.size ≤ 4*(n+1)^2*(U.size+2) ∧
      ∃ t : Fin n → Fin (n+2+G.size), ∀ x i,
        (G.wires (bits n x ++ [false,true])).getD (t i).val false = decide (R x < R (insert i x))) := by
  intro a n R hn h0 hmono hcard hsub
  dsimp only
  have hbits_eq : ∀ (l : ℕ) (x : Finset (Fin l)),
      List.ofFn (fun i : Fin l => @decide (i ∈ x) (Classical.propDecidable (i ∈ x))) =
      PEqualNP.Outside.L_lib_1281_aux.bits l x := by
    intro l x
    dsimp only [PEqualNP.Outside.L_lib_1281_aux.bits]
    congr 1
    funext i
    rw [Subsingleton.elim (Classical.propDecidable (i ∈ x)) (Finset.decidableMem i x)]
  have hpair_eq : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * 2 ^ a - 1 - R Finset.univ))),
      (List.ofFn (fun i : Fin n => @decide (i ∈ x) (Classical.propDecidable (i ∈ x))) ++
       List.ofFn (fun i : Fin (2 * 2 ^ a - 1 - R Finset.univ) => @decide (i ∈ z) (Classical.propDecidable (i ∈ z))) ++
       [false, true]) =
      PEqualNP.Outside.L_lib_1281_aux.pairVec n (2 * 2 ^ a - 1 - R Finset.univ) x z := by
    intro x z
    rw [hbits_eq, hbits_eq]
    rfl
  have hsub' : ∀ x y : Finset (Fin n), R (x ∪ y) + R (x ∩ y) ≤ R x + R y := by
    intro x y; convert hsub x y
  have hins_eq : ∀ (i : Fin n) (x : Finset (Fin n)),
      @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (instDecidableEqFin n)) i x =
      @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) (fun a b => Classical.propDecidable (a = b))) i x := by
    intro i x
    exact congrArg (fun inst => @insert (Fin n) (Finset (Fin n)) (@Finset.instInsert (Fin n) inst) i x)
      (Subsingleton.elim (instDecidableEqFin n) (fun a b => Classical.propDecidable (a = b)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨C, hv, ⟨old, pad, hfit⟩, hnc⟩ :=
      PEqualNP.Outside.L_lib_1281_aux.conjunct1_proof a n R hn hmono hcard
    refine ⟨C, ⟨hv, old, pad, fun x z => ?_⟩, hnc⟩
    rw [hpair_eq x z]
    have h1 := hfit x z
    refine ⟨fun i hi => h1.1 i (by rw [hins_eq]; exact hi), h1.2.1, fun j => ?_⟩
    rw [h1.2.2 j]; convert rfl
  · obtain ⟨C, hv, ⟨old, pad, hfit⟩, hnc, hsz⟩ :=
      PEqualNP.Outside.L_lib_1281_aux.conjunct2_proof a n R hn hcard
    refine ⟨C, ⟨hv, old, pad, fun x z => ?_⟩, hnc, hsz⟩
    rw [hpair_eq x z]
    have h1 := hfit x z
    refine ⟨fun i hi => h1.1 i (by rw [hins_eq]; exact hi), h1.2.1, fun j => ?_⟩
    rw [h1.2.2 j]; convert rfl
  · intro C ⟨hv, old, pad, hfit⟩
    have hfit' : ∃ (old' : Fin n → Fin (n + (2 * 2 ^ a - 1 - R Finset.univ) + 2 + C.size))
        (pad' : Fin (2 * 2 ^ a - 1 - R Finset.univ) → Fin (n + (2 * 2 ^ a - 1 - R Finset.univ) + 2 + C.size)),
        ∀ x z, let w := C.wires (PEqualNP.Outside.L_lib_1281_aux.pairVec n (2 * 2 ^ a - 1 - R Finset.univ) x z)
          (∀ i, R x < R (insert i x) → w.getD (old' i).val false = true) ∧
          (∀ i ∈ x, w.getD (old' i).val false = false) ∧
          (∀ j, w.getD (pad' j).val false = decide (j ∉ z)) := by
      refine ⟨old, pad, fun x z => ?_⟩
      have h1 := hfit x z
      rw [hpair_eq x z] at h1
      refine ⟨fun i hi => h1.1 i (by rw [← hins_eq]; exact hi), h1.2.1, fun j => ?_⟩
      rw [h1.2.2 j]; convert rfl
    obtain ⟨hb, hP⟩ := PEqualNP.Outside.L_lib_1281_aux.conjunct3_proof a n R hn h0 hmono hcard hsub' C hv hfit'
    refine ⟨hb, fun hnc => ?_⟩
    obtain ⟨P, hvP, hmP, hszP, hevP⟩ := hP hnc
    refine ⟨P, hvP, hmP, hszP, fun x z => ?_⟩
    rw [hpair_eq x z, hevP x z]
    convert rfl
  · intro U hvU hU_eval
    have hU' : ∀ x : Finset (Fin n),
        U.eval (PEqualNP.Outside.L_lib_1281_aux.inpU n x) = decide (R Finset.univ ≤ R x) := by
      intro x
      dsimp only [PEqualNP.Outside.L_lib_1281_aux.inpU]
      rw [← hbits_eq n x, hU_eval x]
      convert rfl
    obtain ⟨G, hvG, hszG, t, ht⟩ :=
      PEqualNP.Outside.L_lib_1281_aux.conjunct4_proof n R hmono hcard hsub' U hvU hU'
    refine ⟨G, hvG, hszG, t, fun x i => ?_⟩
    have h1 := ht x i
    dsimp only [PEqualNP.Outside.L_lib_1281_aux.inpU] at h1
    rw [← hbits_eq n x] at h1
    rw [h1, hins_eq]
    convert rfl
