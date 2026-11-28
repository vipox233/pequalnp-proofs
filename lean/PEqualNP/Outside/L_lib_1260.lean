import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1260_aux

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

lemma evalNotCode_lt_of_fall {n : ℕ} (C : Circuit) (tap : Fin n → ℕ)
    (hfit : FanInTwo C) {u v : Finset (Fin n)} (huv : u ⊆ v) {j : Fin n}
    (hu : (C.wires (inpVec u)).getD (tap j) false = true)
    (hv : (C.wires (inpVec v)).getD (tap j) false = false) :
    evalNotCode C.gates (inpVec v) < evalNotCode C.gates (inpVec u) := by
  have hfit' : FanInTwo ⟨C.gates, 0⟩ := hfit
  rcases evalNotCode_dichotomy C.gates (inpVec u) (inpVec v) hfit'
      (by rw [inpVec_length, inpVec_length]) (inpVec_mono huv) with hlt | ⟨_, hle⟩
  · exact hlt
  · exfalso
    have h3 := hle (tap j)
    change (C.wires (inpVec u)).getD (tap j) false ≤ (C.wires (inpVec v)).getD (tap j) false at h3
    rw [hu, hv] at h3
    exact not_true_le_false h3

def Hgraph (n : ℕ) (i j : Fin n) : Prop :=
  i ≠ j ∧ (5 ≤ i.val ∨ 5 ≤ j.val ∨ (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)

lemma evalNotCode_add_chain {n : ℕ} (C : Circuit) (tap : Fin n → ℕ)
    (hfit : FanInTwo C)
    (hpos : ∀ (x : Finset (Fin n)) (j : Fin n), (∀ i ∈ x, Hgraph n i j) →
      (C.wires (inpVec x)).getD (tap j) false = true)
    (hneg : ∀ (x : Finset (Fin n)) (j : Fin n), j ∈ x →
      (C.wires (inpVec x)).getD (tap j) false = false)
    (S : Finset (Fin n)) (hS : ∀ i ∈ S, i.val < 5) :
    ∀ m : ℕ, 5 + m ≤ n →
      evalNotCode C.gates (inpVec (S ∪ Finset.univ.filter (fun i : Fin n => 5 ≤ i.val ∧ i.val < 5 + m))) + m ≤
        evalNotCode C.gates (inpVec S) := by
  intro m
  induction m with
  | zero =>
    intro _
    have hfilt : (Finset.univ.filter (fun i : Fin n => 5 ≤ i.val ∧ i.val < 5 + 0)) = ∅ := by
      ext i; simp
    rw [hfilt, Finset.union_empty, add_zero]
  | succ m ih =>
    intro hm
    have hih := ih (by omega)
    let u := S ∪ Finset.univ.filter (fun i : Fin n => 5 ≤ i.val ∧ i.val < 5 + m)
    let v := S ∪ Finset.univ.filter (fun i : Fin n => 5 ≤ i.val ∧ i.val < 5 + (m + 1))
    let w : Fin n := ⟨5 + m, by omega⟩
    have huv : u ⊆ v := by
      intro i hi
      rcases Finset.mem_union.mp hi with hiS | hiF
      · exact Finset.mem_union_left _ hiS
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩)
        have hF := (Finset.mem_filter.mp hiF).2
        omega
    have hHu : ∀ i ∈ u, Hgraph n i w := by
      intro i hi
      have hilt : i.val < 5 + m := by
        rcases Finset.mem_union.mp hi with hiS | hiF
        · have := hS i hiS; omega
        · exact (Finset.mem_filter.mp hiF).2.2
      refine ⟨?_, Or.inr (Or.inl (by dsimp [w]; omega))⟩
      intro heq
      have : i.val = 5 + m := congrArg Fin.val heq
      omega
    have hwv : w ∈ v := by
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩)
      dsimp [w]; omega
    have hlt := evalNotCode_lt_of_fall C tap hfit huv (hpos u w hHu) (hneg v w hwv)
    dsimp only [u, v] at hlt
    omega

lemma lower_bound_false {k r : ℕ} (hk : 2 ≤ k)
    (C : Circuit) (tap : Fin (5 + (2 ^ k - 3)) → ℕ)
    (hfit : FanInTwo C) (hnot : notCount C ≤ r)
    (hpos : ∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) (j : Fin (5 + (2 ^ k - 3))),
      (∀ i ∈ x, Hgraph (5 + (2 ^ k - 3)) i j) →
      (C.wires (inpVec x)).getD (tap j) false = true)
    (hneg : ∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) (j : Fin (5 + (2 ^ k - 3))), j ∈ x →
      (C.wires (inpVec x)).getD (tap j) false = false) :
    k ≤ r := by
  let t := 2 ^ k - 3
  let n := 5 + t
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  have h1 : evalNotCode C.gates (inpVec ({v0} : Finset (Fin n))) <
      evalNotCode C.gates (inpVec (∅ : Finset (Fin n))) :=
    evalNotCode_lt_of_fall C tap hfit (Finset.empty_subset _)
      (hpos ∅ v0 (by simp)) (hneg {v0} v0 (Finset.mem_singleton_self _))
  have h2 : evalNotCode C.gates (inpVec ({v0, v1} : Finset (Fin n))) <
      evalNotCode C.gates (inpVec ({v0} : Finset (Fin n))) :=
    evalNotCode_lt_of_fall C tap hfit (by intro x hx; simp at hx ⊢; exact Or.inl hx)
      (hpos {v0} v1 (by
        intro i hi
        simp only [Finset.mem_singleton] at hi
        subst hi
        refine ⟨by intro h; have := congrArg Fin.val h; dsimp [v0, v1] at this; omega,
          Or.inr (Or.inr (Or.inl (by dsimp [v0, v1])))⟩))
      (hneg {v0, v1} v1 (by simp))
  have hS : ∀ i ∈ ({v0, v1} : Finset (Fin n)), i.val < 5 := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> dsimp [v0, v1] <;> omega
  have hchain := evalNotCode_add_chain C tap hfit hpos hneg {v0, v1} hS t (by omega)
  have hlt := evalNotCode_lt C.gates (inpVec (∅ : Finset (Fin n)))
  have hnot_eq : notCount ⟨C.gates, 0⟩ = notCount C := rfl
  rw [hnot_eq] at hlt
  have hpow_le : 2 ^ notCount C ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hnot
  have h2k_le : 2 ^ k ≤ 2 ^ r := by omega
  by_contra hlt_r
  have hrk : r + 1 ≤ k := by omega
  have hpow_lt : 2 ^ r < 2 ^ k := by
    have := Nat.pow_le_pow_right (n := 2) (by norm_num) hrk
    rw [pow_succ] at this
    have hpos2 : 0 < 2 ^ r := Nat.pos_of_ne_zero (by positivity)
    omega
  omega

lemma lower_bound_true {k r : ℕ} (hk : 2 ≤ k)
    (C : Circuit) (tap : Fin (5 + (2 ^ k - 3)) → ℕ)
    (hfit : FanInTwo C) (hnot : notCount C ≤ r)
    (hpos : ∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) (j : Fin (5 + (2 ^ k - 3))),
      (∀ i ∈ x, Hgraph (5 + (2 ^ k - 3)) i j) →
      (C.wires (inpVec x)).getD (tap j) false = true)
    (hneg : ∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) (j : Fin (5 + (2 ^ k - 3))), j ∈ x →
      (C.wires (inpVec x)).getD (tap j) false = false)
    (hdec : ∀ (u v : Finset (Fin (5 + (2 ^ k - 3)))), u ⊆ v → ∀ j,
      (C.wires (inpVec v)).getD (tap j) false = true →
      (C.wires (inpVec u)).getD (tap j) false = true) :
    k + 1 ≤ r := by
  let t := 2 ^ k - 3
  let n := 5 + t
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  let v3 : Fin n := ⟨3, by omega⟩
  let v4 : Fin n := ⟨4, by omega⟩
  have h3falls : ∃ S : Finset (Fin n), (∀ i ∈ S, i.val < 5) ∧
      evalNotCode C.gates (inpVec S) + 3 ≤ evalNotCode C.gates (inpVec (∅ : Finset (Fin n))) := by
    cases h24 : (C.wires (inpVec ({v2} : Finset (Fin n)))).getD (tap v4) false
    · have hf02_4 : (C.wires (inpVec ({v0, v2} : Finset (Fin n)))).getD (tap v4) false = false := by
        cases hval : (C.wires (inpVec ({v0, v2} : Finset (Fin n)))).getD (tap v4) false
        · rfl
        · have hsub : ({v2} : Finset (Fin n)) ⊆ {v0, v2} := by intro x hx; simp at hx ⊢; exact Or.inr hx
          have := hdec {v2} {v0, v2} hsub v4 hval
          rw [h24] at this; cases this
      have f1 : evalNotCode C.gates (inpVec ({v0} : Finset (Fin n))) < evalNotCode C.gates (inpVec ∅) :=
        evalNotCode_lt_of_fall C tap hfit (Finset.empty_subset _)
          (hpos ∅ v0 (by simp)) (hneg {v0} v0 (Finset.mem_singleton_self _))
      have f2 : evalNotCode C.gates (inpVec ({v0, v2} : Finset (Fin n))) <
          evalNotCode C.gates (inpVec ({v0} : Finset (Fin n))) :=
        evalNotCode_lt_of_fall C tap hfit (by intro x hx; simp at hx ⊢; exact Or.inl hx)
          (hpos {v0} v4 (by
            intro i hi; simp only [Finset.mem_singleton] at hi; subst hi
            exact ⟨by intro h; have := congrArg Fin.val h; dsimp [v0, v4] at this; omega,
              Or.inr (Or.inr (Or.inr (by dsimp [v0, v4])))⟩))
          hf02_4
      have f3 : evalNotCode C.gates (inpVec ({v0, v1, v2} : Finset (Fin n))) <
          evalNotCode C.gates (inpVec ({v0, v2} : Finset (Fin n))) :=
        evalNotCode_lt_of_fall C tap hfit (by intro x hx; simp at hx ⊢; rcases hx with rfl | rfl <;> tauto)
          (hpos {v0, v2} v1 (by
            intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl
            · exact ⟨by intro h; have := congrArg Fin.val h; dsimp [v0, v1] at this; omega,
                Or.inr (Or.inr (Or.inl (by dsimp [v0, v1])))⟩
            · exact ⟨by intro h; have := congrArg Fin.val h; dsimp [v2, v1] at this; omega,
                Or.inr (Or.inr (Or.inr (by dsimp [v2, v1])))⟩))
          (hneg {v0, v1, v2} v1 (by simp))
      refine ⟨{v0, v1, v2}, ?_, by omega⟩
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> dsimp [v0, v1, v2] <;> omega
    · have f1 : evalNotCode C.gates (inpVec ({v2} : Finset (Fin n))) < evalNotCode C.gates (inpVec ∅) :=
        evalNotCode_lt_of_fall C tap hfit (Finset.empty_subset _)
          (hpos ∅ v2 (by simp)) (hneg {v2} v2 (Finset.mem_singleton_self _))
      have f2 : evalNotCode C.gates (inpVec ({v2, v4} : Finset (Fin n))) <
          evalNotCode C.gates (inpVec ({v2} : Finset (Fin n))) :=
        evalNotCode_lt_of_fall C tap hfit (by intro x hx; simp at hx ⊢; exact Or.inl hx)
          h24 (hneg {v2, v4} v4 (by simp))
      have f3 : evalNotCode C.gates (inpVec ({v2, v3, v4} : Finset (Fin n))) <
          evalNotCode C.gates (inpVec ({v2, v4} : Finset (Fin n))) :=
        evalNotCode_lt_of_fall C tap hfit (by intro x hx; simp at hx ⊢; rcases hx with rfl | rfl <;> tauto)
          (hpos {v2, v4} v3 (by
            intro i hi; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
            rcases hi with rfl | rfl
            · exact ⟨by intro h; have := congrArg Fin.val h; dsimp [v2, v3] at this; omega,
                Or.inr (Or.inr (Or.inl (by dsimp [v2, v3])))⟩
            · exact ⟨by intro h; have := congrArg Fin.val h; dsimp [v4, v3] at this; omega,
                Or.inr (Or.inr (Or.inr (by dsimp [v4, v3])))⟩))
          (hneg {v2, v3, v4} v3 (by simp))
      refine ⟨{v2, v3, v4}, ?_, by omega⟩
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> dsimp [v2, v3, v4] <;> omega
  rcases h3falls with ⟨S, hS, h3⟩
  have hchain := evalNotCode_add_chain C tap hfit hpos hneg S hS t (by omega)
  have hlt := evalNotCode_lt C.gates (inpVec (∅ : Finset (Fin n)))
  have hnot_eq : notCount ⟨C.gates, 0⟩ = notCount C := rfl
  rw [hnot_eq] at hlt
  have hpow_le : 2 ^ notCount C ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hnot
  have h2k_lt : 2 ^ k < 2 ^ r := by omega
  by_contra hlt_r
  have hrk : r ≤ k := by omega
  have hpow_le2 : 2 ^ r ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hrk
  omega

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

def threshStepAux (base w : ℕ) : List Gate → ℕ → List ℕ → List Gate × List ℕ
  | gs, p, [] =>
    let r := emitAnd base gs p w
    (r.1, [r.2])
  | gs, p, q :: qs =>
    let r1 := emitAnd base gs p w
    let r2 := emitOr base r1.1 q r1.2
    let rest := threshStepAux base w r2.1 q qs
    (rest.1, r2.2 :: rest.2)

lemma threshStepAux_spec (base w : ℕ) (qs : List ℕ) (p : ℕ) (gs : List Gate)
    (hw : w < base + gs.length) (hp : p < base + gs.length)
    (hqs : ∀ i ∈ qs, i < base + gs.length) :
    let r := threshStepAux base w gs p qs
    Extends base gs r.1 ∧
    r.2.length = qs.length + 1 ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 2 * qs.length + 1 ∧
    ∀ (v : List Bool), v.length = base →
      ∀ (j : ℕ), j < qs.length + 1 →
        (wiresFrom r.1 v).getD (r.2.getD j 0) false =
          if j < qs.length then
            (wiresFrom gs v).getD (qs.getD j 0) false ||
              ((wiresFrom gs v).getD ((p :: qs).getD j 0) false && (wiresFrom gs v).getD w false)
          else
            (wiresFrom gs v).getD ((p :: qs).getD qs.length 0) false && (wiresFrom gs v).getD w false := by
  induction qs generalizing p gs with
  | nil =>
    dsimp only [threshStepAux]
    have h1 := emitAnd_spec base gs p w hp hw
    rcases h1 with ⟨hext, hlt, hnc, hnn, hval⟩
    refine ⟨hext, rfl, ?_, hnc, by simp [hnn], ?_⟩
    · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact hlt
    · intro v hv j hj
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      simpa using hval v hv
  | cons q qs ih =>
    dsimp only [threshStepAux]
    have hq : q < base + gs.length := hqs q (List.mem_cons_self ..)
    have hqs' : ∀ i ∈ qs, i < base + gs.length := fun i hi => hqs i (List.mem_cons_of_mem _ hi)
    set r1 := emitAnd base gs p w with hr1
    have h1 := emitAnd_spec base gs p w hp hw
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set r2 := emitOr base r1.1 q r1.2 with hr2
    have h2 := emitOr_spec base r1.1 q r1.2 (by omega) hlt1
    rw [← hr2] at h2
    rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    have hext12 := hext1.trans hext2
    set rest := threshStepAux base w r2.1 q qs with hrest
    have h3 := ih q r2.1 (by omega) (by omega) (fun i hi => lt_of_lt_of_le (hqs' i hi) (by omega))
    rw [← hrest] at h3
    rcases h3 with ⟨hext3, hlen3, hlt3, hnc3, hnn3, hval3⟩
    have hgl3 := hext3.length_le
    refine ⟨hext12.trans hext3, by simp [hlen3], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt3 i hi
    · intro v hv j hj
      cases j with
      | zero =>
        change (wiresFrom rest.1 v).getD r2.2 false = _
        simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte]
        rw [hext3.wire_eq v hv _ hlt2, hval2 v hv, hval1 v hv, hext1.wire_eq v hv q hq]
        rfl
      | succ j' =>
        have hj' : j' < qs.length + 1 := by simp at hj; omega
        change (wiresFrom rest.1 v).getD (rest.2.getD j' 0) false = _
        simp only [List.length_cons, Nat.add_lt_add_iff_right]
        rw [hval3 v hv j' hj']
        split_ifs with hlt
        · have hmem1 : qs.getD j' 0 ∈ qs := getD_mem qs j' 0 hlt
          have hmem2 : (q :: qs).getD j' 0 ∈ q :: qs := getD_mem (q :: qs) j' 0 (by simp; omega)
          rw [hext12.wire_eq v hv _ (hqs' _ hmem1),
              hext12.wire_eq v hv _ (hqs _ hmem2),
              hext12.wire_eq v hv w hw]
          rfl
        · have hmem2 : (q :: qs).getD qs.length 0 ∈ q :: qs := getD_mem (q :: qs) qs.length 0 (by simp)
          rw [hext12.wire_eq v hv _ (hqs _ hmem2), hext12.wire_eq v hv w hw]
          rfl

def monotoneCountThresh (base oneWire : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [oneWire])
  | gs, w :: ws =>
    let r1 := monotoneCountThresh base oneWire gs ws
    match r1.2 with
    | [] => (r1.1, [oneWire])
    | p0 :: ps =>
      let r2 := threshStepAux base w r1.1 p0 ps
      (r2.1, p0 :: r2.2)

lemma monotoneCountThresh_spec (base oneWire : ℕ) (ws : List ℕ) (gs : List Gate)
    (hone : oneWire < base + gs.length) (hws : ∀ i ∈ ws, i < base + gs.length) :
    let r := monotoneCountThresh base oneWire gs ws
    Extends base gs r.1 ∧
    r.2.length = ws.length + 1 ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + ws.length ^ 2 ∧
    ∀ (v : List Bool), v.length = base → (wiresFrom gs v).getD oneWire false = true →
      ∀ (ℓ : ℕ), ℓ ≤ ws.length →
        (wiresFrom r.1 v).getD (r.2.getD ℓ 0) false =
          decide (ℓ ≤ (ws.filter fun i => (wiresFrom gs v).getD i false).length) := by
  induction ws generalizing gs with
  | nil =>
    dsimp only [monotoneCountThresh]
    refine ⟨Extends.refl base gs, rfl, ?_, rfl, by simp, ?_⟩
    · intro i hi; simp only [List.mem_singleton] at hi; subst hi; exact hone
    · intro v _ h1 ℓ hℓ
      simp only [List.length_nil, Nat.le_zero] at hℓ
      subst hℓ
      simpa using h1
  | cons w ws ih =>
    dsimp only [monotoneCountThresh]
    have hw : w < base + gs.length := hws w (List.mem_cons_self ..)
    have hws' : ∀ i ∈ ws, i < base + gs.length := fun i hi => hws i (List.mem_cons_of_mem _ hi)
    set r1 := monotoneCountThresh base oneWire gs ws with hr1
    have h1 := ih gs hone hws'
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    cases hr : r1.2 with
    | nil => rw [hr] at hlen1; simp at hlen1
    | cons p0 ps =>
      dsimp only
      have hps_len : ps.length = ws.length := by rw [hr] at hlen1; simp at hlen1; omega
      have hp0_lt : p0 < base + r1.1.length := hlt1 p0 (by rw [hr]; exact List.mem_cons_self ..)
      have hps_lt : ∀ i ∈ ps, i < base + r1.1.length := fun i hi =>
        hlt1 i (by rw [hr]; exact List.mem_cons_of_mem _ hi)
      set r2 := threshStepAux base w r1.1 p0 ps with hr2
      have h2 := threshStepAux_spec base w ps p0 r1.1 (by omega) hp0_lt hps_lt
      rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      have hsq : (ws.length + 1) ^ 2 = ws.length ^ 2 + 2 * ws.length + 1 := by ring
      refine ⟨hext1.trans hext2, by simp [hlen2, hps_len], ?_, by omega,
        by simp only [List.length_cons]; omega, ?_⟩
      · intro i hi
        simp only [List.mem_cons] at hi
        rcases hi with rfl | hi
        · omega
        · exact hlt2 i hi
      · intro v hv h1v ℓ hℓ
        simp only [List.length_cons] at hℓ
        have hevalw : (wiresFrom r1.1 v).getD w false = (wiresFrom gs v).getD w false :=
          hext1.wire_eq v hv w hw
        have hcount_le : (ws.filter fun i => (wiresFrom gs v).getD i false).length ≤ ws.length :=
          List.length_filter_le _ _
        cases ℓ with
        | zero =>
          change (wiresFrom r2.1 v).getD p0 false = _
          rw [hext2.wire_eq v hv p0 hp0_lt]
          have hv0 := hval1 v hv h1v 0 (Nat.zero_le _)
          rw [hr] at hv0
          simpa using hv0
        | succ j =>
          change (wiresFrom r2.1 v).getD (r2.2.getD j 0) false = _
          have hj_lt : j < ps.length + 1 := by omega
          rw [hval2 v hv j hj_lt, hevalw]
          by_cases hjl : j < ps.length
          · rw [if_pos hjl]
            have hj1 : j + 1 ≤ ws.length := by omega
            have hvj1 := hval1 v hv h1v (j + 1) hj1
            have hvj := hval1 v hv h1v j (by omega)
            rw [hr] at hvj1 hvj
            change (wiresFrom r1.1 v).getD (ps.getD j 0) false = _ at hvj1
            rw [hvj1, hvj, List.filter_cons]
            cases hgw : (wiresFrom gs v).getD w false
            · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.or_false]
            · simp only [↓reduceIte, Bool.and_true, List.length_cons]
              apply Bool.eq_iff_iff.mpr
              simp only [Bool.or_eq_true, decide_eq_true_eq]
              omega
          · rw [if_neg hjl]
            have hjeq : j = ws.length := by omega
            subst hjeq
            have hvj := hval1 v hv h1v ws.length (le_refl _)
            rw [hr, ← hps_len] at hvj
            rw [hvj, List.filter_cons]
            cases hgw : (wiresFrom gs v).getD w false
            · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false]
              symm; exact decide_eq_false (by omega)
            · simp only [↓reduceIte, Bool.and_true, List.length_cons]
              apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega

def compareThresh (base : ℕ) : List Gate → ℕ → List ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [], _ => (gs, acc)
  | gs, acc, _, [] => (gs, acc)
  | gs, acc, a :: as, b :: bs =>
    let r1 := emitAnd base gs a b
    let r2 := emitOr base r1.1 acc r1.2
    compareThresh base r2.1 r2.2 as bs

lemma compareThresh_spec (base : ℕ) (as bs : List ℕ) (gs : List Gate) (acc : ℕ)
    (hlen : as.length = bs.length)
    (hacc : acc < base + gs.length)
    (has : ∀ i ∈ as, i < base + gs.length)
    (hbs : ∀ i ∈ bs, i < base + gs.length) :
    let r := compareThresh base gs acc as bs
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 2 * as.length ∧
    ∀ (v : List Bool), v.length = base →
      (wiresFrom r.1 v).getD r.2 false =
        ((wiresFrom gs v).getD acc false ||
          (List.range as.length).any fun ℓ =>
            (wiresFrom gs v).getD (as.getD ℓ 0) false &&
            (wiresFrom gs v).getD (bs.getD ℓ 0) false) := by
  induction as generalizing bs gs acc with
  | nil =>
    cases bs with
    | nil =>
      dsimp only [compareThresh]
      refine ⟨Extends.refl base gs, hacc, rfl, by simp, fun v _ => by simp⟩
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      dsimp only [compareThresh]
      have ha : a < base + gs.length := has a (List.mem_cons_self ..)
      have hb : b < base + gs.length := hbs b (List.mem_cons_self ..)
      have has' : ∀ i ∈ as, i < base + gs.length := fun i hi => has i (List.mem_cons_of_mem _ hi)
      have hbs' : ∀ i ∈ bs, i < base + gs.length := fun i hi => hbs i (List.mem_cons_of_mem _ hi)
      set r1 := emitAnd base gs a b with hr1
      have h1 := emitAnd_spec base gs a b ha hb
      rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
      have hgl1 := hext1.length_le
      set r2 := emitOr base r1.1 acc r1.2 with hr2
      have h2 := emitOr_spec base r1.1 acc r1.2 (by omega) hlt1
      rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      have hext12 := hext1.trans hext2
      have h3 := ih bs r2.1 r2.2 (by simp at hlen; omega) hlt2
        (fun i hi => lt_of_lt_of_le (has' i hi) (by omega))
        (fun i hi => lt_of_lt_of_le (hbs' i hi) (by omega))
      rcases h3 with ⟨hext3, hlt3, hnc3, hnn3, hval3⟩
      refine ⟨hext12.trans hext3, hlt3, by omega, by simp only [List.length_cons]; omega, ?_⟩
      intro v hv
      rw [hval3 v hv, hval2 v hv, hval1 v hv, hext1.wire_eq v hv acc hacc]
      have hany_eq : ((List.range as.length).any fun ℓ =>
          (wiresFrom r2.1 v).getD (as.getD ℓ 0) false &&
          (wiresFrom r2.1 v).getD (bs.getD ℓ 0) false) =
        ((List.range as.length).any fun ℓ =>
          (wiresFrom gs v).getD (as.getD ℓ 0) false &&
          (wiresFrom gs v).getD (bs.getD ℓ 0) false) := by
        refine list_any_congr _ _ _ fun ℓ hℓ => ?_
        have hℓ' : ℓ < as.length := List.mem_range.mp hℓ
        rw [hext12.wire_eq v hv _ (has' _ (getD_mem as ℓ 0 hℓ')),
            hext12.wire_eq v hv _ (hbs' _ (getD_mem bs ℓ 0 (by simp at hlen; omega)))]
      rw [hany_eq, Bool.or_assoc]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.length_cons]
      constructor
      · rintro (⟨h1a, h1b⟩ | ⟨ℓ, hℓ, h2a, h2b⟩)
        · exact ⟨0, by omega, h1a, h1b⟩
        · exact ⟨ℓ + 1, by omega, h2a, h2b⟩
      · rintro ⟨ℓ, hℓ, h2a, h2b⟩
        cases ℓ with
        | zero => exact Or.inl ⟨h2a, h2b⟩
        | succ ℓ' => exact Or.inr ⟨ℓ', by omega, h2a, h2b⟩

def addGeWire (zeroWire : ℕ) (addW : List ℕ) (u : ℕ) : ℕ :=
  if u < addW.length then addW.getD u 0 else zeroWire

def combineOne (base zeroWire oneWire rim1 rim2 : ℕ) (addW : List ℕ) (gs : List Gate) (ℓ : ℕ) :
    List Gate × ℕ :=
  match ℓ with
  | 0 => (gs, oneWire)
  | 1 => emitOr base gs (addGeWire zeroWire addW 1) rim1
  | ℓ' + 2 =>
    let r1 := emitAnd base gs rim1 (addGeWire zeroWire addW (ℓ' + 1))
    let r2 := emitAnd base r1.1 rim2 (addGeWire zeroWire addW ℓ')
    let r3 := emitOr base r2.1 (addGeWire zeroWire addW (ℓ' + 2)) r1.2
    emitOr base r3.1 r3.2 r2.2

lemma combineOne_spec (base zeroWire oneWire rim1 rim2 : ℕ) (addW : List ℕ) (gs : List Gate) (ℓ : ℕ)
    (hzero : zeroWire < base + gs.length) (hone : oneWire < base + gs.length)
    (hr1 : rim1 < base + gs.length) (hr2 : rim2 < base + gs.length)
    (hadd : ∀ i ∈ addW, i < base + gs.length) :
    let r := combineOne base zeroWire oneWire rim1 rim2 addW gs ℓ
    Extends base gs r.1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 ≤ nonNot gs + 4 ∧
    ∀ (v : List Bool) (cr ca : ℕ), v.length = base →
      (wiresFrom gs v).getD zeroWire false = false →
      (wiresFrom gs v).getD oneWire false = true →
      cr ≤ 2 → ca + 1 ≤ addW.length →
      (wiresFrom gs v).getD rim1 false = decide (1 ≤ cr) →
      (wiresFrom gs v).getD rim2 false = decide (2 ≤ cr) →
      (∀ u, u < addW.length → (wiresFrom gs v).getD (addW.getD u 0) false = decide (u ≤ ca)) →
      (wiresFrom r.1 v).getD r.2 false = decide (ℓ ≤ cr + ca) := by
  have hge_lt : ∀ u, addGeWire zeroWire addW u < base + gs.length := by
    intro u; dsimp only [addGeWire]
    split_ifs with hu
    · exact hadd _ (getD_mem addW u 0 hu)
    · exact hzero
  have hge_eval : ∀ (v : List Bool) (ca : ℕ) (u : ℕ),
      (wiresFrom gs v).getD zeroWire false = false →
      ca + 1 ≤ addW.length →
      (∀ u', u' < addW.length → (wiresFrom gs v).getD (addW.getD u' 0) false = decide (u' ≤ ca)) →
      (wiresFrom gs v).getD (addGeWire zeroWire addW u) false = decide (u ≤ ca) := by
    intro v ca u hz hca hadd_ev
    dsimp only [addGeWire]
    split_ifs with hu
    · exact hadd_ev u hu
    · rw [hz]; symm; exact decide_eq_false (by omega)
  cases ℓ with
  | zero =>
    dsimp only [combineOne]
    refine ⟨Extends.refl base gs, hone, rfl, by omega, ?_⟩
    intro v cr ca _ _ h1 _ _ _ _ _; simpa using h1
  | succ ℓ' =>
    cases ℓ' with
    | zero =>
      dsimp only [combineOne]
      have h1 := emitOr_spec base gs (addGeWire zeroWire addW 1) rim1 (hge_lt 1) hr1
      rcases h1 with ⟨hext, hlt, hnc, hnn, hval⟩
      refine ⟨hext, hlt, hnc, by omega, ?_⟩
      intro v cr ca hv hz _ hcr hca hrim1 _ hadd_ev
      rw [hval v hv, hge_eval v ca 1 hz hca hadd_ev, hrim1]
      apply Bool.eq_iff_iff.mpr; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega
    | succ ℓ'' =>
      dsimp only [combineOne]
      set r1 := emitAnd base gs rim1 (addGeWire zeroWire addW (ℓ'' + 1)) with hr1_def
      have h1 := emitAnd_spec base gs rim1 (addGeWire zeroWire addW (ℓ'' + 1)) hr1 (hge_lt (ℓ'' + 1))
      rw [← hr1_def] at h1
      rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
      have hgl1 := hext1.length_le
      set r2 := emitAnd base r1.1 rim2 (addGeWire zeroWire addW ℓ'') with hr2_def
      have h2 := emitAnd_spec base r1.1 rim2 (addGeWire zeroWire addW ℓ'') (by omega)
        (lt_of_lt_of_le (hge_lt ℓ'') (by omega))
      rw [← hr2_def] at h2
      rcases h2 with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
      have hgl2 := hext2.length_le
      have hext12 := hext1.trans hext2
      set r3 := emitOr base r2.1 (addGeWire zeroWire addW (ℓ'' + 2)) r1.2 with hr3_def
      have h3 := emitOr_spec base r2.1 (addGeWire zeroWire addW (ℓ'' + 2)) r1.2
        (lt_of_lt_of_le (hge_lt (ℓ'' + 2)) (by omega)) (by omega)
      rw [← hr3_def] at h3
      rcases h3 with ⟨hext3, hlt3, hnc3, hnn3, hval3⟩
      have hgl3 := hext3.length_le
      have hext123 := hext12.trans hext3
      have h4 := emitOr_spec base r3.1 r3.2 r2.2 hlt3 (by omega)
      rcases h4 with ⟨hext4, hlt4, hnc4, hnn4, hval4⟩
      refine ⟨hext123.trans hext4, hlt4, by omega, by omega, ?_⟩
      intro v cr ca hv hz _ hcr hca hrim1 hrim2 hadd_ev
      rw [hval4 v hv, hval3 v hv, hext3.wire_eq v hv r2.2 hlt2, hval2 v hv,
          hext2.wire_eq v hv r1.2 hlt1, hval1 v hv,
          hext12.wire_eq v hv _ (hge_lt (ℓ'' + 2)),
          hext1.wire_eq v hv rim2 hr2, hext1.wire_eq v hv _ (hge_lt ℓ'')]
      rw [hge_eval v ca (ℓ'' + 2) hz hca hadd_ev,
          hge_eval v ca (ℓ'' + 1) hz hca hadd_ev,
          hge_eval v ca ℓ'' hz hca hadd_ev, hrim1, hrim2]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      omega

def combineList (base zeroWire oneWire rim1 rim2 : ℕ) (addW : List ℕ) :
    List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, ℓ :: ls =>
    let r1 := combineOne base zeroWire oneWire rim1 rim2 addW gs ℓ
    let r2 := combineList base zeroWire oneWire rim1 rim2 addW r1.1 ls
    (r2.1, r1.2 :: r2.2)

lemma combineList_spec (base zeroWire oneWire rim1 rim2 : ℕ) (addW : List ℕ) (ls : List ℕ) (gs : List Gate)
    (hzero : zeroWire < base + gs.length) (hone : oneWire < base + gs.length)
    (hr1 : rim1 < base + gs.length) (hr2 : rim2 < base + gs.length)
    (hadd : ∀ i ∈ addW, i < base + gs.length) :
    let r := combineList base zeroWire oneWire rim1 rim2 addW gs ls
    Extends base gs r.1 ∧
    r.2.length = ls.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 ≤ nonNot gs + 4 * ls.length ∧
    ∀ (v : List Bool) (cr ca : ℕ), v.length = base →
      (wiresFrom gs v).getD zeroWire false = false →
      (wiresFrom gs v).getD oneWire false = true →
      cr ≤ 2 → ca + 1 ≤ addW.length →
      (wiresFrom gs v).getD rim1 false = decide (1 ≤ cr) →
      (wiresFrom gs v).getD rim2 false = decide (2 ≤ cr) →
      (∀ u, u < addW.length → (wiresFrom gs v).getD (addW.getD u 0) false = decide (u ≤ ca)) →
      ∀ (i : ℕ), i < ls.length →
        (wiresFrom r.1 v).getD (r.2.getD i 0) false = decide (ls.getD i 0 ≤ cr + ca) := by
  induction ls generalizing gs with
  | nil =>
    dsimp only [combineList]
    refine ⟨Extends.refl base gs, rfl, (fun _ h => by cases h), rfl, by simp,
      fun _ _ _ _ _ _ _ _ _ _ _ i hi => by simp at hi⟩
  | cons ℓ ls ih =>
    dsimp only [combineList]
    set r1 := combineOne base zeroWire oneWire rim1 rim2 addW gs ℓ with hr1_def
    have h1 := combineOne_spec base zeroWire oneWire rim1 rim2 addW gs ℓ hzero hone hr1 hr2 hadd
    rw [← hr1_def] at h1
    rcases h1 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    set r2 := combineList base zeroWire oneWire rim1 rim2 addW r1.1 ls with hr2_def
    have h2 := ih r1.1 (by omega) (by omega) (by omega) (by omega)
      (fun i hi => lt_of_lt_of_le (hadd i hi) (by omega))
    rw [← hr2_def] at h2
    rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, by simp [hlen2], ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi
      · omega
      · exact hlt2 i hi
    · intro v cr ca hv hz h1v hcr hca hrim1 hrim2 hadd_ev i hi
      cases i with
      | zero =>
        change (wiresFrom r2.1 v).getD r1.2 false = decide (ℓ ≤ cr + ca)
        rw [hext2.wire_eq v hv r1.2 hlt1]
        exact hval1 v cr ca hv hz h1v hcr hca hrim1 hrim2 hadd_ev
      | succ i' =>
        have hi' : i' < ls.length := by simp at hi; omega
        change (wiresFrom r2.1 v).getD (r2.2.getD i' 0) false = decide (ls.getD i' 0 ≤ cr + ca)
        exact hval2 v cr ca hv (by rw [hext1.wire_eq v hv zeroWire hzero]; exact hz)
          (by rw [hext1.wire_eq v hv oneWire hone]; exact h1v) hcr hca
          (by rw [hext1.wire_eq v hv rim1 hr1]; exact hrim1)
          (by rw [hext1.wire_eq v hv rim2 hr2]; exact hrim2)
          (fun u hu => by rw [hext1.wire_eq v hv _ (hadd _ (getD_mem addW u 0 hu))]; exact hadd_ev u hu)
          i' hi'

def buildAssoc {α : Type*} [DecidableEq α] (step : List Gate → α → List Gate × ℕ)
    (dflt : ℕ) : List Gate → List α → List Gate × (α → ℕ)
  | gs, [] => (gs, fun _ => dflt)
  | gs, a :: as =>
    let r := step gs a
    let rest := buildAssoc step dflt r.1 as
    (rest.1, fun x => if x = a then r.2 else rest.2 x)

lemma buildAssoc_ext_spec {α : Type*} [DecidableEq α] (base dflt : ℕ) (gs0 : List Gate)
    (step : List Gate → α → List Gate × ℕ)
    (cost : α → ℕ)
    (spec : α → List Bool → Bool)
    (hstep : ∀ (gs : List Gate) (a : α), Extends base gs0 gs →
      Extends base gs (step gs a).1 ∧
      (step gs a).2 < base + (step gs a).1.length ∧
      notCount ⟨(step gs a).1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot (step gs a).1 ≤ nonNot gs + cost a ∧
      ∀ (w : List Bool), w.length = base →
        (wiresFrom (step gs a).1 w).getD (step gs a).2 false = spec a w) :
    ∀ (ks : List α) (gs : List Gate), Extends base gs0 gs → dflt < base + gs.length →
      let r := buildAssoc step dflt gs ks
      Extends base gs r.1 ∧
      (∀ x, r.2 x < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + (ks.map cost).sum ∧
      ∀ (w : List Bool), w.length = base → ∀ a ∈ ks,
        (wiresFrom r.1 w).getD (r.2 a) false = spec a w := by
  intro ks
  induction ks with
  | nil =>
    intro gs _ hdflt
    dsimp only [buildAssoc]
    refine ⟨Extends.refl base gs, fun _ => hdflt, rfl, by simp, fun _ _ _ ha => by cases ha⟩
  | cons a ks ih =>
    intro gs hExt0 hdflt
    dsimp only [buildAssoc]
    rcases hstep gs a hExt0 with ⟨hext1, hlt1, hnc1, hnn1, hval1⟩
    have hgl1 := hext1.length_le
    rcases ih (step gs a).1 (hExt0.trans hext1) (by omega) with ⟨hext2, hlt2, hnc2, hnn2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext1.trans hext2, ?_, by omega, by simp only [List.map_cons, List.sum_cons]; omega, ?_⟩
    · intro x
      by_cases hx : x = a
      · simp only [hx, ↓reduceIte]; omega
      · simp only [hx, ↓reduceIte]; exact hlt2 x
    · intro w hw b hb
      by_cases hba : b = a
      · subst hba
        simp only [↓reduceIte]
        rw [hext2.wire_eq w hw _ hlt1, hval1 w hw]
      · simp only [hba, ↓reduceIte]
        exact hval2 w hw b ((List.mem_cons.mp hb).resolve_left hba)

lemma sum_const_le {α : Type*} (l : List α) (c : ℕ) : (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons _ tl ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

end Builder

section UpperBoundFalse

def rimClique {n : ℕ} (x : Finset (Fin n)) : ℕ :=
  if ∃ a ∈ x, ∃ b ∈ x, a.val < 5 ∧ b.val < 5 ∧ (a.val + 1) % 5 = b.val then 2
  else if ∃ a ∈ x, a.val < 5 then 1
  else 0

def addCount {n : ℕ} (x : Finset (Fin n)) : ℕ :=
  (x.filter fun i : Fin n => 5 ≤ i.val).card

lemma rimClique_le_two {n : ℕ} (x : Finset (Fin n)) : rimClique x ≤ 2 := by
  dsimp only [rimClique]; split_ifs <;> omega

lemma rimClique_ge_one {n : ℕ} (x : Finset (Fin n)) :
    1 ≤ rimClique x ↔ ∃ a ∈ x, a.val < 5 := by
  dsimp only [rimClique]
  split_ifs with h2 h1
  · rcases h2 with ⟨a, ha, _, _, ha5, _, _⟩
    exact ⟨fun _ => ⟨a, ha, ha5⟩, fun _ => by omega⟩
  · exact ⟨fun _ => h1, fun _ => by omega⟩
  · exact ⟨fun h => by omega, fun h => absurd h h1⟩

lemma rimClique_ge_two {n : ℕ} (x : Finset (Fin n)) :
    2 ≤ rimClique x ↔ ∃ a ∈ x, ∃ b ∈ x, a.val < 5 ∧ b.val < 5 ∧ (a.val + 1) % 5 = b.val := by
  dsimp only [rimClique]
  split_ifs with h2 h1
  · exact ⟨fun _ => h2, fun _ => by omega⟩
  · exact ⟨fun h => by omega, fun h => absurd h h2⟩
  · exact ⟨fun h => by omega, fun h => absurd h h2⟩

lemma rimClique_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) :
    rimClique u ≤ rimClique v := by
  dsimp only [rimClique]
  split_ifs with h2u h2v h1v h1u h2v' h1v'
  · exact le_refl 2
  · exfalso; rcases h2u with ⟨a, ha, b, hb, h1, h2, h3⟩
    exact h2v ⟨a, huv ha, b, huv hb, h1, h2, h3⟩
  · exfalso; rcases h2u with ⟨a, ha, b, hb, h1, h2, h3⟩
    exact h2v ⟨a, huv ha, b, huv hb, h1, h2, h3⟩
  · omega
  · exact le_refl 1
  · exfalso; rcases h1u with ⟨a, ha, h1⟩; exact h1v' ⟨a, huv ha, h1⟩
  · omega
  · omega
  · exact le_refl 0

lemma addCount_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) :
    addCount u ≤ addCount v :=
  Finset.card_le_card (Finset.filter_subset_filter _ huv)

lemma addCount_le_sub {n : ℕ} (x : Finset (Fin n)) : addCount x ≤ n - 5 := by
  have hsub : x.filter (fun i : Fin n => 5 ≤ i.val) ⊆
      Finset.univ.filter (fun i : Fin n => 5 ≤ i.val) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.filter (fun i : Fin n => 5 ≤ i.val)).card = n - 5 := by
    have hbij : (Finset.univ.filter (fun i : Fin n => 5 ≤ i.val)).card = (Finset.range (n - 5)).card := by
      refine Finset.card_bij (fun i _ => i.val - 5) ?_ ?_ ?_
      · intro i hi
        have hi5 : 5 ≤ i.val := (Finset.mem_filter.mp hi).2
        exact Finset.mem_range.mpr (by omega)
      · intro i1 h1 i2 h2 heq
        have h1' := (Finset.mem_filter.mp h1).2
        have h2' := (Finset.mem_filter.mp h2).2
        exact Fin.ext (by omega)
      · intro m hm
        have hm' : m < n - 5 := Finset.mem_range.mp hm
        refine ⟨⟨5 + m, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩, by dsimp; omega⟩
    rw [hbij, Finset.card_range]
  dsimp only [addCount]
  omega

lemma count_list_filter_eq_addCount {n : ℕ} (x : Finset (Fin n)) (hn : 5 ≤ n) :
    (((List.range (n - 5)).map (fun m => 5 + m)).filter
      (fun i => (inpVec x).getD i false)).length = addCount x := by
  have hnodup : ((List.range (n - 5)).map (fun m => 5 + m)).Nodup :=
    List.nodup_range.map (fun _ _ h => by omega)
  have h1 : (((List.range (n - 5)).map (fun m => 5 + m)).filter
      (fun i => (inpVec x).getD i false)).length =
      ((((List.range (n - 5)).map (fun m => 5 + m)).filter
        (fun i => (inpVec x).getD i false)).toFinset).card := by
    rw [List.toFinset_card_of_nodup (hnodup.filter _)]
  rw [h1]
  refine Finset.card_bij (fun i hi => ⟨i, by
    rw [List.mem_toFinset, List.mem_filter] at hi
    rcases List.mem_map.mp hi.1 with ⟨m, hm, rfl⟩
    have := List.mem_range.mp hm; omega⟩) ?_ ?_ ?_
  · intro i hi
    rw [List.mem_toFinset, List.mem_filter] at hi
    rcases List.mem_map.mp hi.1 with ⟨m, hm, rfl⟩
    have hm' := List.mem_range.mp hm
    have hv := inpVec_getD_fin x ⟨5 + m, by omega⟩
    dsimp only at hv
    rw [hv, decide_eq_true_eq] at hi
    exact Finset.mem_filter.mpr ⟨hi.2, by dsimp; omega⟩
  · intro i1 _ i2 _ heq; exact congrArg Fin.val heq
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjx, hj5⟩
    refine ⟨j.val, ?_, Fin.eta j _⟩
    rw [List.mem_toFinset, List.mem_filter]
    refine ⟨List.mem_map.mpr ⟨j.val - 5, List.mem_range.mpr (by omega), by omega⟩, ?_⟩
    rw [inpVec_getD_fin x j, decide_eq_true_eq]; exact hjx

lemma count_list_filter_erase_eq_addCount {n : ℕ} (x : Finset (Fin n)) (j : Fin n) (hj5 : 5 ≤ j.val) :
    ((((List.range (n - 5)).map (fun m => 5 + m)).filter (fun i => i ≠ j.val)).filter
      (fun i => (inpVec x).getD i false)).length = addCount (x.erase j) := by
  have hnodup : (((List.range (n - 5)).map (fun m => 5 + m)).filter (fun i => i ≠ j.val)).Nodup :=
    (List.nodup_range.map (fun _ _ h => by omega)).filter _
  have h1 : (((((List.range (n - 5)).map (fun m => 5 + m)).filter (fun i => i ≠ j.val)).filter
      (fun i => (inpVec x).getD i false))).length =
      ((((((List.range (n - 5)).map (fun m => 5 + m)).filter (fun i => i ≠ j.val)).filter
        (fun i => (inpVec x).getD i false))).toFinset).card := by
    rw [List.toFinset_card_of_nodup (hnodup.filter _)]
  rw [h1]
  refine Finset.card_bij (fun i hi => ⟨i, by
    rw [List.mem_toFinset, List.mem_filter, List.mem_filter] at hi
    rcases List.mem_map.mp hi.1.1 with ⟨m, hm, rfl⟩
    have := List.mem_range.mp hm; omega⟩) ?_ ?_ ?_
  · intro i hi
    rw [List.mem_toFinset, List.mem_filter, List.mem_filter] at hi
    rcases List.mem_map.mp hi.1.1 with ⟨m, hm, rfl⟩
    have hm' := List.mem_range.mp hm
    have hv := inpVec_getD_fin x ⟨5 + m, by omega⟩
    dsimp only at hv
    have hi2 := hi.2
    rw [hv, decide_eq_true_eq] at hi2
    have hne : (⟨5 + m, by omega⟩ : Fin n) ≠ j := by
      intro h; have hval := congrArg Fin.val h; exact (of_decide_eq_true hi.1.2) hval
    exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, hi2⟩, by dsimp; omega⟩
  · intro i1 _ i2 _ heq; exact congrArg Fin.val heq
  · intro i hi
    rcases Finset.mem_filter.mp hi with ⟨hie, hi5⟩
    rcases Finset.mem_erase.mp hie with ⟨hne, hix⟩
    refine ⟨i.val, ?_, Fin.eta i _⟩
    rw [List.mem_toFinset, List.mem_filter, List.mem_filter]
    refine ⟨⟨List.mem_map.mpr ⟨i.val - 5, List.mem_range.mpr (by omega), by omega⟩,
      decide_eq_true (fun h => hne (Fin.ext h))⟩, ?_⟩
    rw [inpVec_getD_fin x i, decide_eq_true_eq]; exact hix

def emitRim (base : ℕ) (gs : List Gate) : List Gate × (ℕ × ℕ) :=
  -- rim1 = 0 ∨ 1 ∨ 2 ∨ 3 ∨ 4
  let o1 := emitOr base gs 0 1
  let o2 := emitOr base o1.1 o1.2 2
  let o3 := emitOr base o2.1 o2.2 3
  let o4 := emitOr base o3.1 o3.2 4
  -- rim2 = (0∧1) ∨ (1∧2) ∨ (2∧3) ∨ (3∧4) ∨ (4∧0)
  let a0 := emitAnd base o4.1 0 1
  let a1 := emitAnd base a0.1 1 2
  let a2 := emitAnd base a1.1 2 3
  let a3 := emitAnd base a2.1 3 4
  let a4 := emitAnd base a3.1 4 0
  let e1 := emitOr base a4.1 a0.2 a1.2
  let e2 := emitOr base e1.1 e1.2 a2.2
  let e3 := emitOr base e2.1 e2.2 a3.2
  let e4 := emitOr base e3.1 e3.2 a4.2
  (e4.1, (o4.2, e4.2))

lemma emitRim_spec (n : ℕ) (hn : 5 ≤ n) (gs : List Gate) :
    let r := emitRim (n + 2) gs
    Extends (n + 2) gs r.1 ∧
    r.2.1 < (n + 2) + r.1.length ∧
    r.2.2 < (n + 2) + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    nonNot r.1 = nonNot gs + 13 ∧
    ∀ (x : Finset (Fin n)),
      (wiresFrom r.1 (inpVec x)).getD r.2.1 false = decide (1 ≤ rimClique x) ∧
      (wiresFrom r.1 (inpVec x)).getD r.2.2 false = decide (2 ≤ rimClique x) := by
  dsimp only [emitRim]
  set base := n + 2
  have hb : ∀ i < 5, i < base + gs.length := fun i hi => by omega
  set o1 := emitOr base gs 0 1 with ho1
  have h_o1 := emitOr_spec base gs 0 1 (hb 0 (by omega)) (hb 1 (by omega)); rw [← ho1] at h_o1
  rcases h_o1 with ⟨e_o1, l_o1, nc_o1, nn_o1, v_o1⟩; have g_o1 := e_o1.length_le
  set o2 := emitOr base o1.1 o1.2 2 with ho2
  have h_o2 := emitOr_spec base o1.1 o1.2 2 l_o1 (by omega); rw [← ho2] at h_o2
  rcases h_o2 with ⟨e_o2, l_o2, nc_o2, nn_o2, v_o2⟩; have g_o2 := e_o2.length_le
  set o3 := emitOr base o2.1 o2.2 3 with ho3
  have h_o3 := emitOr_spec base o2.1 o2.2 3 l_o2 (by omega); rw [← ho3] at h_o3
  rcases h_o3 with ⟨e_o3, l_o3, nc_o3, nn_o3, v_o3⟩; have g_o3 := e_o3.length_le
  set o4 := emitOr base o3.1 o3.2 4 with ho4
  have h_o4 := emitOr_spec base o3.1 o3.2 4 l_o3 (by omega); rw [← ho4] at h_o4
  rcases h_o4 with ⟨e_o4, l_o4, nc_o4, nn_o4, v_o4⟩; have g_o4 := e_o4.length_le
  have eo14 := ((e_o1.trans e_o2).trans e_o3).trans e_o4
  set a0 := emitAnd base o4.1 0 1 with ha0
  have h_a0 := emitAnd_spec base o4.1 0 1 (by omega) (by omega); rw [← ha0] at h_a0
  rcases h_a0 with ⟨e_a0, l_a0, nc_a0, nn_a0, v_a0⟩; have g_a0 := e_a0.length_le
  set a1 := emitAnd base a0.1 1 2 with ha1
  have h_a1 := emitAnd_spec base a0.1 1 2 (by omega) (by omega); rw [← ha1] at h_a1
  rcases h_a1 with ⟨e_a1, l_a1, nc_a1, nn_a1, v_a1⟩; have g_a1 := e_a1.length_le
  set a2 := emitAnd base a1.1 2 3 with ha2
  have h_a2 := emitAnd_spec base a1.1 2 3 (by omega) (by omega); rw [← ha2] at h_a2
  rcases h_a2 with ⟨e_a2, l_a2, nc_a2, nn_a2, v_a2⟩; have g_a2 := e_a2.length_le
  set a3 := emitAnd base a2.1 3 4 with ha3
  have h_a3 := emitAnd_spec base a2.1 3 4 (by omega) (by omega); rw [← ha3] at h_a3
  rcases h_a3 with ⟨e_a3, l_a3, nc_a3, nn_a3, v_a3⟩; have g_a3 := e_a3.length_le
  set a4 := emitAnd base a3.1 4 0 with ha4
  have h_a4 := emitAnd_spec base a3.1 4 0 (by omega) (by omega); rw [← ha4] at h_a4
  rcases h_a4 with ⟨e_a4, l_a4, nc_a4, nn_a4, v_a4⟩; have g_a4 := e_a4.length_le
  set e1 := emitOr base a4.1 a0.2 a1.2 with he1
  have h_e1 := emitOr_spec base a4.1 a0.2 a1.2 (by omega) (by omega); rw [← he1] at h_e1
  rcases h_e1 with ⟨e_e1, l_e1, nc_e1, nn_e1, v_e1⟩; have g_e1 := e_e1.length_le
  set e2 := emitOr base e1.1 e1.2 a2.2 with he2
  have h_e2 := emitOr_spec base e1.1 e1.2 a2.2 l_e1 (by omega); rw [← he2] at h_e2
  rcases h_e2 with ⟨e_e2, l_e2, nc_e2, nn_e2, v_e2⟩; have g_e2 := e_e2.length_le
  set e3 := emitOr base e2.1 e2.2 a3.2 with he3
  have h_e3 := emitOr_spec base e2.1 e2.2 a3.2 l_e2 (by omega); rw [← he3] at h_e3
  rcases h_e3 with ⟨e_e3, l_e3, nc_e3, nn_e3, v_e3⟩; have g_e3 := e_e3.length_le
  set e4 := emitOr base e3.1 e3.2 a4.2 with he4
  have h_e4 := emitOr_spec base e3.1 e3.2 a4.2 l_e3 (by omega); rw [← he4] at h_e4
  rcases h_e4 with ⟨e_e4, l_e4, nc_e4, nn_e4, v_e4⟩; have g_e4 := e_e4.length_le
  have e_rest : Extends base o4.1 e4.1 :=
    (((((((e_a0.trans e_a1).trans e_a2).trans e_a3).trans e_a4).trans e_e1).trans e_e2).trans e_e3).trans e_e4
  have e_all : Extends base gs e4.1 := eo14.trans e_rest
  refine ⟨e_all, by omega, l_e4, by omega, by omega, ?_⟩
  intro x
  have hlen : (inpVec x).length = base := inpVec_length x
  have hget : ∀ (gs' : List Gate) (i : ℕ) (hi : i < 5),
      (wiresFrom gs' (inpVec x)).getD i false = decide ((⟨i, by omega⟩ : Fin n) ∈ x) := by
    intro gs' i hi
    rw [wiresFrom_getD_lt gs' (inpVec x) i (by rw [hlen]; omega)]
    exact inpVec_getD_fin x ⟨i, by omega⟩
  constructor
  · rw [e_rest.wire_eq (inpVec x) hlen o4.2 l_o4, v_o4 _ hlen, v_o3 _ hlen, v_o2 _ hlen, v_o1 _ hlen,
        hget gs 0 (by omega), hget gs 1 (by omega), hget o1.1 2 (by omega),
        hget o2.1 3 (by omega), hget o3.1 4 (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, rimClique_ge_one]
    constructor
    · rintro ((((h | h) | h) | h) | h)
      · exact ⟨⟨0, by omega⟩, h, by dsimp; omega⟩
      · exact ⟨⟨1, by omega⟩, h, by dsimp; omega⟩
      · exact ⟨⟨2, by omega⟩, h, by dsimp; omega⟩
      · exact ⟨⟨3, by omega⟩, h, by dsimp; omega⟩
      · exact ⟨⟨4, by omega⟩, h, by dsimp; omega⟩
    · rintro ⟨⟨v, hvn⟩, hvx, hv5⟩
      interval_cases v
      · exact Or.inl (Or.inl (Or.inl (Or.inl hvx)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr hvx)))
      · exact Or.inl (Or.inl (Or.inr hvx))
      · exact Or.inl (Or.inr hvx)
      · exact Or.inr hvx
  · have e_a0_a4 : Extends base a0.1 a4.1 := ((e_a1.trans e_a2).trans e_a3).trans e_a4
    have e_a1_a4 : Extends base a1.1 a4.1 := (e_a2.trans e_a3).trans e_a4
    have e_a2_e1 : Extends base a2.1 e1.1 := (e_a3.trans e_a4).trans e_e1
    have e_a3_e2 : Extends base a3.1 e2.1 := (e_a4.trans e_e1).trans e_e2
    have e_a4_e3 : Extends base a4.1 e3.1 := (e_e1.trans e_e2).trans e_e3
    rw [v_e4 _ hlen, v_e3 _ hlen, v_e2 _ hlen, v_e1 _ hlen,
        e_a4_e3.wire_eq _ hlen a4.2 l_a4, e_a3_e2.wire_eq _ hlen a3.2 l_a3,
        e_a2_e1.wire_eq _ hlen a2.2 l_a2, e_a1_a4.wire_eq _ hlen a1.2 l_a1,
        e_a0_a4.wire_eq _ hlen a0.2 l_a0,
        v_a0 _ hlen, v_a1 _ hlen, v_a2 _ hlen, v_a3 _ hlen, v_a4 _ hlen,
        hget o4.1 0 (by omega), hget o4.1 1 (by omega), hget a0.1 1 (by omega),
        hget a0.1 2 (by omega), hget a1.1 2 (by omega), hget a1.1 3 (by omega),
        hget a2.1 3 (by omega), hget a2.1 4 (by omega), hget a3.1 4 (by omega),
        hget a3.1 0 (by omega)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, rimClique_ge_two]
    constructor
    · rintro ((((⟨h0, h1⟩ | ⟨h1, h2⟩) | ⟨h2, h3⟩) | ⟨h3, h4⟩) | ⟨h4, h0⟩)
      · exact ⟨⟨0, by omega⟩, h0, ⟨1, by omega⟩, h1, by dsimp; omega, by dsimp; omega, rfl⟩
      · exact ⟨⟨1, by omega⟩, h1, ⟨2, by omega⟩, h2, by dsimp; omega, by dsimp; omega, rfl⟩
      · exact ⟨⟨2, by omega⟩, h2, ⟨3, by omega⟩, h3, by dsimp; omega, by dsimp; omega, rfl⟩
      · exact ⟨⟨3, by omega⟩, h3, ⟨4, by omega⟩, h4, by dsimp; omega, by dsimp; omega, rfl⟩
      · exact ⟨⟨4, by omega⟩, h4, ⟨0, by omega⟩, h0, by dsimp; omega, by dsimp; omega, by dsimp⟩
    · rintro ⟨⟨a, han⟩, hax, ⟨b, hbn⟩, hbx, ha5, hb5, hab⟩
      interval_cases a <;> interval_cases b <;> simp at hab
      · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hax, hbx⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hax, hbx⟩)))
      · exact Or.inl (Or.inl (Or.inr ⟨hax, hbx⟩))
      · exact Or.inl (Or.inr ⟨hax, hbx⟩)
      · exact Or.inr ⟨hax, hbx⟩

lemma upper_bound_false {k : ℕ} (hk : 2 ≤ k) :
    let t := 2 ^ k - 3
    let n := 5 + t
    ∃ (C : Circuit) (tap : Fin n → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ j, tap j < n + 2 + C.size) ∧
      notCount C ≤ k ∧ C.size ≤ 128 * (n + 1) ^ 3 ∧
      let f := fun (x : Finset (Fin n)) (j : Fin n) =>
        (C.wires (inpVec x)).getD (tap j) false
      (∀ x j, (∀ i ∈ x, Hgraph n i j) → f x j = true) ∧
      (∀ x j, j ∈ x → f x j = false) := by
  intro t n
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hn5 : 5 ≤ n := by omega
  have ht_eq : n - 5 = t := by omega
  have h2k_eq : t + 3 = 2 ^ k := by omega
  set base := n + 2
  set zeroW := n
  set oneW := n + 1
  -- Step 1: rim clique wires (rim1, rim2)
  set rRim := emitRim base [] with hrRim
  have hRim := emitRim_spec n hn5 []
  rw [← hrRim] at hRim
  rcases hRim with ⟨eRim, lRim1, lRim2, ncRim, nnRim, vRim⟩
  -- Step 2: full addCount thresholds
  let addList : List ℕ := (List.range t).map (fun m => 5 + m)
  have hadd_len : addList.length = t := by simp [addList]
  have hadd_lt : ∀ i ∈ addList, i < base + rRim.1.length := by
    intro i hi; rcases List.mem_map.mp hi with ⟨m, hm, rfl⟩
    have := List.mem_range.mp hm; omega
  set rAdd := monotoneCountThresh base oneW rRim.1 addList with hrAdd
  have hAdd := monotoneCountThresh_spec base oneW addList rRim.1 (by omega) hadd_lt
  rw [← hrAdd] at hAdd
  rcases hAdd with ⟨eAdd, lenAdd, lAdd, ncAdd, nnAdd, vAdd⟩
  have gAdd := eAdd.length_le
  -- Step 3: combine rim + add for levels 1..t+2
  set rFull := combineList base zeroW oneW rRim.2.1 rRim.2.2 rAdd.2 rAdd.1
    ((List.range (t + 2)).map (fun ℓ => ℓ + 1)) with hrFull
  have hFull := combineList_spec base zeroW oneW rRim.2.1 rRim.2.2 rAdd.2
    ((List.range (t + 2)).map (fun ℓ => ℓ + 1)) rAdd.1
    (by omega) (by omega) (by omega) (by omega) lAdd
  rw [← hrFull] at hFull
  rcases hFull with ⟨eFull, lenFull, lFull, ncFull, nnFull, vFull⟩
  have gFull := eFull.length_le
  -- Step 4: chainInv on rFull.2 (length t + 2 = 2^k - 1 < 2^k)
  have hlen_full_lt : rFull.2.length < 2 ^ k := by rw [lenFull, List.length_map, List.length_range]; omega
  set rInv := chainInv base k rFull.1 rFull.2 with hrInv
  have hInv := chainInv_spec base k rFull.1 rFull.2 hlen_full_lt lFull
  rw [← hrInv] at hInv
  rcases hInv with ⟨eInv, lenInv, lInv, ncInv, nnInv, vInv⟩
  have gInv := eInv.length_le
  let leW : List ℕ := rInv.2 ++ [oneW]
  have hleW_len : leW.length = t + 3 := by
    simp only [leW, List.length_append, List.length_singleton, lenInv, lenFull, List.length_map, List.length_range]
  have hleW_lt : ∀ i ∈ leW, i < base + rInv.1.length := by
    intro i hi
    simp only [leW, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact lInv i hi
    · omega
  have e0Inv : Extends base [] rInv.1 := ((eRim.trans eAdd).trans eFull).trans eInv
  have eRimInv : Extends base rRim.1 rInv.1 := (eAdd.trans eFull).trans eInv
  have eAddInv : Extends base rAdd.1 rInv.1 := eFull.trans eInv
  have hFull_eval : ∀ (x : Finset (Fin n)) (i : ℕ), i < t + 2 →
      (wiresFrom rFull.1 (inpVec x)).getD (rFull.2.getD i 0) false =
        decide (i + 1 ≤ rimClique x + addCount x) := by
    intro x i hi
    have hlen := inpVec_length x
    have hca : addCount x + 1 ≤ rAdd.2.length := by
      have := addCount_le_sub x; omega
    have hadd_ev : ∀ u, u < rAdd.2.length →
        (wiresFrom rAdd.1 (inpVec x)).getD (rAdd.2.getD u 0) false = decide (u ≤ addCount x) := by
      intro u hu
      have h1w : (wiresFrom rRim.1 (inpVec x)).getD oneW false = true := by
        rw [wiresFrom_getD_lt rRim.1 (inpVec x) oneW (by rw [hlen]; omega), inpVec_getD_true]
      rw [vAdd (inpVec x) hlen h1w u (by omega)]
      have hfilt : (addList.filter fun i => (wiresFrom rRim.1 (inpVec x)).getD i false).length = addCount x := by
        have hcongr : (addList.filter fun i => (wiresFrom rRim.1 (inpVec x)).getD i false) =
            (addList.filter fun i => (inpVec x).getD i false) := by
          refine List.filter_congr fun w hw => ?_
          rcases List.mem_map.mp hw with ⟨m, hm, rfl⟩
          have := List.mem_range.mp hm
          exact wiresFrom_getD_lt rRim.1 (inpVec x) (5 + m) (by rw [hlen]; omega)
        rw [hcongr]
        have hcnt := count_list_filter_eq_addCount x hn5
        rw [ht_eq] at hcnt
        exact hcnt
      rw [hfilt]
    have hv := vFull (inpVec x) (rimClique x) (addCount x) hlen
      (by rw [wiresFrom_getD_lt rAdd.1 (inpVec x) zeroW (by rw [hlen]; omega), inpVec_getD_false])
      (by rw [wiresFrom_getD_lt rAdd.1 (inpVec x) oneW (by rw [hlen]; omega), inpVec_getD_true])
      (rimClique_le_two x) hca
      (by rw [eAdd.wire_eq (inpVec x) hlen rRim.2.1 lRim1]; exact (vRim x).1)
      (by rw [eAdd.wire_eq (inpVec x) hlen rRim.2.2 lRim2]; exact (vRim x).2)
      hadd_ev i (by simp [hi])
    have hget_l : (((List.range (t + 2)).map fun ℓ => ℓ + 1).getD i 0) = i + 1 := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [hget_l] at hv
    exact hv
  have hleW_eval : ∀ (x : Finset (Fin n)) (ℓ : ℕ), ℓ < t + 3 →
      (wiresFrom rInv.1 (inpVec x)).getD (leW.getD ℓ 0) false =
        decide (rimClique x + addCount x ≤ ℓ) := by
    intro x ℓ hℓ
    have hlen := inpVec_length x
    by_cases hlt : ℓ < t + 2
    · have hget : leW.getD ℓ 0 = rInv.2.getD ℓ 0 :=
        getD_append_left rInv.2 [oneW] ℓ 0 (by rw [lenInv, lenFull, List.length_map, List.length_range]; exact hlt)
      rw [hget]
      have hdec : ∀ (i j : ℕ), i < rFull.2.length → j < rFull.2.length → i ≤ j →
          (wiresFrom rFull.1 (inpVec x)).getD (rFull.2.getD j 0) false ≤
            (wiresFrom rFull.1 (inpVec x)).getD (rFull.2.getD i 0) false := by
        intro i j hi hj hij
        rw [lenFull, List.length_map, List.length_range] at hi hj
        rw [hFull_eval x j hj, hFull_eval x i hi, bool_le_iff]
        intro h; exact decide_eq_true (by have := of_decide_eq_true h; omega)
      rw [vInv (inpVec x) hlen hdec ℓ (by rw [lenFull, List.length_map, List.length_range]; exact hlt),
          hFull_eval x ℓ hlt]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega
    · have heq : ℓ = t + 2 := by omega
      subst heq
      have hget : leW.getD (t + 2) 0 = oneW := by
        rw [getD_append_right rInv.2 [oneW] (t + 2) 0
          (by rw [lenInv, lenFull, List.length_map, List.length_range])]
        have hsub : t + 2 - rInv.2.length = 0 := by
          rw [lenInv, lenFull, List.length_map, List.length_range]; omega
        rw [hsub]; rfl
      rw [hget, wiresFrom_getD_lt rInv.1 (inpVec x) oneW (by rw [hlen]; omega), inpVec_getD_true]
      have hc1 := rimClique_le_two x
      have hc2 := addCount_le_sub x
      symm; exact decide_eq_true (by omega)
  -- Step 5: for each vertex j : Fin n, compute neighborhood rank thresholds & compare with leW
  let nbRank : Finset (Fin n) → Fin n → ℕ := fun x j =>
    let nb := x.filter (fun i => Hgraph n i j)
    rimClique nb + addCount nb
  let stepJ : List Gate → Fin n → List Gate × ℕ := fun gs j =>
    if j.val < 5 then
      let p1 := (j.val + 4) % 5
      let p2 := (j.val + 1) % 5
      let r1 := emitOr base gs p1 p2
      let r2 := combineList base zeroW oneW r1.2 zeroW rAdd.2 r1.1 (List.range (t + 3))
      compareThresh base r2.1 zeroW leW r2.2
    else
      let remList := addList.filter (fun i => i ≠ j.val)
      let r1 := monotoneCountThresh base oneW gs remList
      let r2 := combineList base zeroW oneW rRim.2.1 rRim.2.2 r1.2 r1.1 (List.range (t + 3))
      compareThresh base r2.1 zeroW leW r2.2
  have hstepJ : ∀ (gs : List Gate) (j : Fin n), Extends base rInv.1 gs →
      Extends base gs (stepJ gs j).1 ∧
      (stepJ gs j).2 < base + (stepJ gs j).1.length ∧
      notCount ⟨(stepJ gs j).1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot (stepJ gs j).1 ≤ nonNot gs + (t ^ 2 + 6 * t + 19) ∧
      ∀ (w : List Bool), w.length = base →
        ∀ (x : Finset (Fin n)), w = inpVec x →
          (wiresFrom (stepJ gs j).1 w).getD (stepJ gs j).2 false =
            decide (rimClique x + addCount x ≤ nbRank x j) := by
    intro gs j hExtInv
    have gInvGs := hExtInv.length_le
    have eRimGs : Extends base rRim.1 gs := eRimInv.trans hExtInv
    have eAddGs : Extends base rAdd.1 gs := eAddInv.trans hExtInv
    have gRimGs := eRimGs.length_le
    have gAddGs := eAddGs.length_le
    dsimp only [stepJ]
    split_ifs with hj5
    · set p1 := (j.val + 4) % 5
      set p2 := (j.val + 1) % 5
      have hp1 : p1 < 5 := Nat.mod_lt _ (by omega)
      have hp2 : p2 < 5 := Nat.mod_lt _ (by omega)
      set r1 := emitOr base gs p1 p2 with hr1
      have h1 := emitOr_spec base gs p1 p2 (by omega) (by omega); rw [← hr1] at h1
      rcases h1 with ⟨e1, l1, nc1, nn1, v1⟩; have g1 := e1.length_le
      set r2 := combineList base zeroW oneW r1.2 zeroW rAdd.2 r1.1 (List.range (t + 3)) with hr2
      have h2 := combineList_spec base zeroW oneW r1.2 zeroW rAdd.2 (List.range (t + 3)) r1.1
        (by omega) (by omega) l1 (by omega) (fun i hi => lt_of_lt_of_le (lAdd i hi) (by omega))
      rw [← hr2] at h2
      rcases h2 with ⟨e2, len2, l2, nc2, nn2, v2⟩; have g2 := e2.length_le
      set r3 := compareThresh base r2.1 zeroW leW r2.2 with hr3
      have h3 := compareThresh_spec base leW r2.2 r2.1 zeroW
        (by rw [hleW_len, len2, List.length_range]) (by omega)
        (fun i hi => lt_of_lt_of_le (hleW_lt i hi) (by omega)) l2
      rw [← hr3] at h3
      rcases h3 with ⟨e3, l3, nc3, nn3, v3⟩
      refine ⟨(e1.trans e2).trans e3, l3, by omega, by simp only [List.length_range] at nn2; omega, ?_⟩
      intro w hw x hx; subst hx
      set nb := x.filter (fun i => Hgraph n i j)
      have hnb_rim_le : rimClique nb ≤ 1 := by
        by_contra hgt
        have h2r : 2 ≤ rimClique nb := by omega
        rcases (rimClique_ge_two nb).mp h2r with ⟨a, ha, b, hb, ha5, hb5, hab⟩
        have hHa := (Finset.mem_filter.mp ha).2
        have hHb := (Finset.mem_filter.mp hb).2
        have hjv : j.val < 5 := hj5
        rcases hHa with ⟨hna, ha5' | hj5' | ha1 | ha2⟩ <;> try omega
        · rcases hHb with ⟨hnb, hb5' | hj5'' | hb1 | hb2⟩ <;> omega
        · rcases hHb with ⟨hnb, hb5' | hj5'' | hb1 | hb2⟩ <;> omega
      have hnb_rim1 : (wiresFrom r1.1 (inpVec x)).getD r1.2 false = decide (1 ≤ rimClique nb) := by
        rw [v1 (inpVec x) hw, wiresFrom_getD_lt gs (inpVec x) p1 (by rw [hw]; omega),
            wiresFrom_getD_lt gs (inpVec x) p2 (by rw [hw]; omega),
            inpVec_getD_fin x ⟨p1, by omega⟩, inpVec_getD_fin x ⟨p2, by omega⟩]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, decide_eq_true_eq, rimClique_ge_one, nb, Finset.mem_filter]
        constructor
        · rintro (h | h)
          · refine ⟨⟨p1, by omega⟩, ⟨h, ?_⟩, hp1⟩
            refine ⟨by intro heq; have := congrArg Fin.val heq; dsimp [p1] at this; omega,
              Or.inr (Or.inr (Or.inl (by dsimp [p1]; omega)))⟩
          · refine ⟨⟨p2, by omega⟩, ⟨h, ?_⟩, hp2⟩
            refine ⟨by intro heq; have := congrArg Fin.val heq; dsimp [p2] at this; omega,
              Or.inr (Or.inr (Or.inr rfl))⟩
        · rintro ⟨a, ⟨hax, hHa⟩, ha5⟩
          rcases hHa with ⟨hne, h5a | h5j | h1 | h2⟩ <;> try omega
          · have ha_eq : (⟨p1, by omega⟩ : Fin n) = a := Fin.ext (by dsimp [p1]; omega)
            left; rwa [ha_eq]
          · have ha_eq : (⟨p2, by omega⟩ : Fin n) = a := Fin.ext (by dsimp [p2]; omega)
            right; rwa [ha_eq]
      have hnb_add : addCount nb = addCount x := by
        dsimp only [addCount, nb]
        congr 1; ext i
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hix, _⟩, hi5⟩; exact ⟨hix, hi5⟩
        · rintro ⟨hix, hi5⟩
          refine ⟨⟨hix, ⟨?_, Or.inl hi5⟩⟩, hi5⟩
          intro heq; have := congrArg Fin.val heq; omega
      have hnb_add_ev : ∀ u, u < rAdd.2.length →
          (wiresFrom r1.1 (inpVec x)).getD (rAdd.2.getD u 0) false = decide (u ≤ addCount nb) := by
        intro u hu
        rw [(eAddGs.trans e1).wire_eq (inpVec x) hw _ (lAdd _ (getD_mem rAdd.2 u 0 hu))]
        have h1w : (wiresFrom rRim.1 (inpVec x)).getD oneW false = true := by
          rw [wiresFrom_getD_lt rRim.1 (inpVec x) oneW (by rw [hw]; omega), inpVec_getD_true]
        rw [vAdd (inpVec x) hw h1w u (by omega), hnb_add]
        have hcongr : (addList.filter fun i => (wiresFrom rRim.1 (inpVec x)).getD i false) =
            (addList.filter fun i => (inpVec x).getD i false) := by
          refine List.filter_congr fun w hw' => ?_
          rcases List.mem_map.mp hw' with ⟨m, hm, rfl⟩
          have := List.mem_range.mp hm
          exact wiresFrom_getD_lt rRim.1 (inpVec x) (5 + m) (by rw [hw]; omega)
        rw [hcongr]
        have hcnt := count_list_filter_eq_addCount x hn5
        rw [ht_eq] at hcnt
        dsimp only [addList]
        rw [hcnt]
      have hr2_ev : ∀ ℓ, ℓ < t + 3 →
          (wiresFrom r2.1 (inpVec x)).getD (r2.2.getD ℓ 0) false = decide (ℓ ≤ nbRank x j) := by
        intro ℓ hℓ
        have hv := v2 (inpVec x) (rimClique nb) (addCount nb) hw
          (by rw [wiresFrom_getD_lt r1.1 (inpVec x) zeroW (by rw [hw]; omega), inpVec_getD_false])
          (by rw [wiresFrom_getD_lt r1.1 (inpVec x) oneW (by rw [hw]; omega), inpVec_getD_true])
          (by omega) (by have := addCount_le_sub nb; omega) hnb_rim1
          (by rw [wiresFrom_getD_lt r1.1 (inpVec x) zeroW (by rw [hw]; omega), inpVec_getD_false]
              symm; exact decide_eq_false (by omega))
          hnb_add_ev ℓ (by simp [hℓ])
        have hget_r : (List.range (t + 3)).getD ℓ 0 = ℓ := by simp [List.getD_eq_getElem?_getD, hℓ]
        rw [hget_r] at hv; exact hv
      rw [v3 (inpVec x) hw, wiresFrom_getD_lt r2.1 (inpVec x) zeroW (by rw [hw]; omega),
          inpVec_getD_false, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, hleW_len]
      have hExtInv2 : Extends base rInv.1 r2.1 := (hExtInv.trans e1).trans e2
      constructor
      · rintro ⟨ℓ, hℓ, hA, hB⟩
        rw [hExtInv2.wire_eq (inpVec x) hw _ (hleW_lt _ (getD_mem leW ℓ 0 (by omega))),
            hleW_eval x ℓ hℓ, decide_eq_true_eq] at hA
        rw [hr2_ev ℓ hℓ, decide_eq_true_eq] at hB
        omega
      · intro hle
        have htot : rimClique x + addCount x < t + 3 := by
          have := rimClique_le_two x; have := addCount_le_sub x; omega
        refine ⟨rimClique x + addCount x, htot, ?_, ?_⟩
        · rw [hExtInv2.wire_eq (inpVec x) hw _ (hleW_lt _ (getD_mem leW _ 0 (by omega))),
              hleW_eval x _ htot, decide_eq_true_eq]
        · rw [hr2_ev _ htot, decide_eq_true_eq]; exact hle
    · have hj5' : 5 ≤ j.val := by omega
      let remList := addList.filter (fun i => i ≠ j.val)
      have hrem_len : remList.length ≤ t := by
        have hfl := List.length_filter_le (fun i => decide (i ≠ j.val)) addList
        rw [hadd_len] at hfl
        exact hfl
      have hrem_lt : ∀ i ∈ remList, i < base + gs.length := by
        intro i hi
        have hi' := (List.mem_filter.mp hi).1
        exact lt_of_lt_of_le (hadd_lt i hi') (by omega)
      set r1 := monotoneCountThresh base oneW gs remList with hr1
      have h1 := monotoneCountThresh_spec base oneW remList gs (by omega) hrem_lt
      rw [← hr1] at h1
      rcases h1 with ⟨e1, len1, l1, nc1, nn1, v1⟩; have g1 := e1.length_le
      set r2 := combineList base zeroW oneW rRim.2.1 rRim.2.2 r1.2 r1.1 (List.range (t + 3)) with hr2
      have h2 := combineList_spec base zeroW oneW rRim.2.1 rRim.2.2 r1.2 (List.range (t + 3)) r1.1
        (by omega) (by omega) (by omega) (by omega) l1
      rw [← hr2] at h2
      rcases h2 with ⟨e2, len2, l2, nc2, nn2, v2⟩; have g2 := e2.length_le
      set r3 := compareThresh base r2.1 zeroW leW r2.2 with hr3
      have h3 := compareThresh_spec base leW r2.2 r2.1 zeroW
        (by rw [hleW_len, len2, List.length_range]) (by omega)
        (fun i hi => lt_of_lt_of_le (hleW_lt i hi) (by omega)) l2
      rw [← hr3] at h3
      rcases h3 with ⟨e3, l3, nc3, nn3, v3⟩
      have hsq_le : remList.length ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hrem_len 2
      refine ⟨(e1.trans e2).trans e3, l3, by omega, by simp only [List.length_range] at nn2; omega, ?_⟩
      intro w hw x hx; subst hx
      set nb := x.filter (fun i => Hgraph n i j)
      have hnb_eq : nb = x.erase j := by
        ext i
        dsimp only [nb]
        rw [Finset.mem_filter, Finset.mem_erase]
        dsimp only [Hgraph]
        constructor
        · rintro ⟨hix, hne, _⟩; exact ⟨hne, hix⟩
        · rintro ⟨hne, hix⟩; exact ⟨hix, hne, Or.inr (Or.inl hj5')⟩
      have hnb_rim : rimClique nb = rimClique x := by
        rw [hnb_eq]
        have hiff1 : (∃ a ∈ x.erase j, a.val < 5) ↔ (∃ a ∈ x, a.val < 5) := by
          constructor
          · rintro ⟨a, ha, h5⟩; exact ⟨a, (Finset.mem_erase.mp ha).2, h5⟩
          · rintro ⟨a, ha, h5⟩; exact ⟨a, Finset.mem_erase.mpr ⟨by intro h; subst h; omega, ha⟩, h5⟩
        have hiff2 : (∃ a ∈ x.erase j, ∃ b ∈ x.erase j, a.val < 5 ∧ b.val < 5 ∧ (a.val + 1) % 5 = b.val) ↔
            (∃ a ∈ x, ∃ b ∈ x, a.val < 5 ∧ b.val < 5 ∧ (a.val + 1) % 5 = b.val) := by
          constructor
          · rintro ⟨a, ha, b, hb, h1, h2, h3⟩
            exact ⟨a, (Finset.mem_erase.mp ha).2, b, (Finset.mem_erase.mp hb).2, h1, h2, h3⟩
          · rintro ⟨a, ha, b, hb, h1, h2, h3⟩
            exact ⟨a, Finset.mem_erase.mpr ⟨by intro h; subst h; omega, ha⟩,
              b, Finset.mem_erase.mpr ⟨by intro h; subst h; omega, hb⟩, h1, h2, h3⟩
        dsimp only [rimClique]
        simp only [hiff1, hiff2]
      have hnb_add_count : (remList.filter fun i => (wiresFrom gs (inpVec x)).getD i false).length =
          addCount nb := by
        rw [hnb_eq]
        have hcongr : (remList.filter fun i => (wiresFrom gs (inpVec x)).getD i false) =
            (remList.filter fun i => (inpVec x).getD i false) := by
          refine List.filter_congr fun i hi => ?_
          have hi' := (List.mem_filter.mp hi).1
          rcases List.mem_map.mp hi' with ⟨m, hm, rfl⟩
          have := List.mem_range.mp hm
          exact wiresFrom_getD_lt gs (inpVec x) (5 + m) (by rw [hw]; omega)
        rw [hcongr]
        have hcnt := count_list_filter_erase_eq_addCount x j hj5'
        rw [ht_eq] at hcnt
        exact hcnt
      have hnb_add_le : addCount nb ≤ remList.length := by
        rw [← hnb_add_count]; exact List.length_filter_le _ _
      have hnb_add_ev : ∀ u, u < r1.2.length →
          (wiresFrom r1.1 (inpVec x)).getD (r1.2.getD u 0) false = decide (u ≤ addCount nb) := by
        intro u hu
        have h1w : (wiresFrom gs (inpVec x)).getD oneW false = true := by
          rw [wiresFrom_getD_lt gs (inpVec x) oneW (by rw [hw]; omega), inpVec_getD_true]
        rw [v1 (inpVec x) hw h1w u (by omega), hnb_add_count]
      have hr2_ev : ∀ ℓ, ℓ < t + 3 →
          (wiresFrom r2.1 (inpVec x)).getD (r2.2.getD ℓ 0) false = decide (ℓ ≤ nbRank x j) := by
        intro ℓ hℓ
        have hv := v2 (inpVec x) (rimClique nb) (addCount nb) hw
          (by rw [wiresFrom_getD_lt r1.1 (inpVec x) zeroW (by rw [hw]; omega), inpVec_getD_false])
          (by rw [wiresFrom_getD_lt r1.1 (inpVec x) oneW (by rw [hw]; omega), inpVec_getD_true])
          (rimClique_le_two nb) (by omega)
          (by rw [(eRimGs.trans e1).wire_eq (inpVec x) hw rRim.2.1 lRim1, hnb_rim]; exact (vRim x).1)
          (by rw [(eRimGs.trans e1).wire_eq (inpVec x) hw rRim.2.2 lRim2, hnb_rim]; exact (vRim x).2)
          hnb_add_ev ℓ (by simp [hℓ])
        have hget_r : (List.range (t + 3)).getD ℓ 0 = ℓ := by simp [List.getD_eq_getElem?_getD, hℓ]
        rw [hget_r] at hv; exact hv
      rw [v3 (inpVec x) hw, wiresFrom_getD_lt r2.1 (inpVec x) zeroW (by rw [hw]; omega),
          inpVec_getD_false, Bool.false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, hleW_len]
      have hExtInv2 : Extends base rInv.1 r2.1 := (hExtInv.trans e1).trans e2
      constructor
      · rintro ⟨ℓ, hℓ, hA, hB⟩
        rw [hExtInv2.wire_eq (inpVec x) hw _ (hleW_lt _ (getD_mem leW ℓ 0 (by omega))),
            hleW_eval x ℓ hℓ, decide_eq_true_eq] at hA
        rw [hr2_ev ℓ hℓ, decide_eq_true_eq] at hB
        omega
      · intro hle
        have htot : rimClique x + addCount x < t + 3 := by
          have := rimClique_le_two x; have := addCount_le_sub x; omega
        refine ⟨rimClique x + addCount x, htot, ?_, ?_⟩
        · rw [hExtInv2.wire_eq (inpVec x) hw _ (hleW_lt _ (getD_mem leW _ 0 (by omega))),
              hleW_eval x _ htot, decide_eq_true_eq]
        · rw [hr2_ev _ htot, decide_eq_true_eq]; exact hle
  -- Simple direct induction over List.finRange n
  have hBuildAll : ∀ (js : List (Fin n)) (gs : List Gate), Extends base rInv.1 gs →
      let r := buildAssoc stepJ zeroW gs js
      Extends base gs r.1 ∧
      (∀ j, r.2 j < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + js.length * (t ^ 2 + 6 * t + 19) ∧
      ∀ (x : Finset (Fin n)), ∀ j ∈ js,
        (wiresFrom r.1 (inpVec x)).getD (r.2 j) false =
          decide (rimClique x + addCount x ≤ nbRank x j) := by
    intro js
    induction js with
    | nil =>
      intro gs _
      dsimp only [buildAssoc]
      refine ⟨Extends.refl base gs, fun _ => by omega, rfl, by simp, fun _ _ h => by cases h⟩
    | cons a js ih =>
      intro gs hExt
      dsimp only [buildAssoc]
      rcases hstepJ gs a hExt with ⟨he1, hl1, hnc1, hnn1, hv1⟩
      have g1 := he1.length_le
      rcases ih (stepJ gs a).1 (hExt.trans he1) with ⟨he2, hl2, hnc2, hnn2, hv2⟩
      have g2 := he2.length_le
      have hmul : (js.length + 1) * (t ^ 2 + 6 * t + 19) =
          js.length * (t ^ 2 + 6 * t + 19) + (t ^ 2 + 6 * t + 19) := by ring
      refine ⟨he1.trans he2, ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
      · intro j; by_cases hj : j = a
        · simp only [hj, ↓reduceIte]; omega
        · simp only [hj, ↓reduceIte]; exact hl2 j
      · intro x j hj
        by_cases hja : j = a
        · subst hja; simp only [↓reduceIte]
          rw [he2.wire_eq (inpVec x) (inpVec_length x) _ hl1, hv1 (inpVec x) (inpVec_length x) x rfl]
        · simp only [hja, ↓reduceIte]
          exact hv2 x j ((List.mem_cons.mp hj).resolve_left hja)
  set rAll := buildAssoc stepJ zeroW rInv.1 (List.finRange n) with hrAll
  have hAll := hBuildAll (List.finRange n) rInv.1 (Extends.refl base rInv.1)
  rw [← hrAll] at hAll
  rcases hAll with ⟨eAll, lAll, ncAll, nnAll, vAll⟩
  have eFinal : Extends base [] rAll.1 := e0Inv.trans eAll
  rcases eFinal with ⟨extra, hEq, hFit, hRB⟩
  simp only [List.nil_append, List.length_nil, add_zero] at hEq hRB
  subst hEq
  let C : Circuit := ⟨rAll.1, 0⟩
  have hCnot : notCount C ≤ k := by
    change notCount ⟨rAll.1, 0⟩ ≤ k
    rw [ncAll]
    have h0 : notCount ⟨[], 0⟩ = 0 := rfl
    omega
  have hk_le_n : k ≤ n := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  have hCsize : C.size ≤ 128 * (n + 1) ^ 3 := by
    have hnn_fin : nonNot rAll.1 ≤ 13 + t ^ 2 + 4 * (t + 2) + 4 * (t + 2) + n * (t ^ 2 + 6 * t + 19) := by
      simp only [List.length_finRange, List.length_map, List.length_range] at nnAll nnFull lenFull
      rw [nonNot_nil, zero_add] at nnRim
      rw [hadd_len] at nnAdd
      omega
    have hsz : C.size = nonNot rAll.1 + notCount C := by
      change rAll.1.length = rAll.1.length - notCount ⟨rAll.1, 0⟩ + notCount ⟨rAll.1, 0⟩
      have := notCount_le_length rAll.1 0
      omega
    have ht_le_n : t ≤ n := by omega
    have htsq : t ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left ht_le_n 2
    have hnt_le : n * (t ^ 2 + 6 * t + 19) ≤ n * (n ^ 2 + 6 * n + 19) :=
      Nat.mul_le_mul_left n (by omega)
    have hexp1 : n * (n ^ 2 + 6 * n + 19) = n ^ 3 + 6 * n ^ 2 + 19 * n := by ring
    have hexp2 : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    omega
  refine ⟨C, rAll.2, hFit, hRB, by dsimp [C]; omega, lAll, hCnot, hCsize, ?_, ?_⟩
  · intro x j hH
    change (wiresFrom rAll.1 (inpVec x)).getD (rAll.2 j) false = true
    rw [vAll x j (List.mem_finRange j), decide_eq_true_eq]
    have hnb_eq : x.filter (fun i => Hgraph n i j) = x := by
      ext i; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hH i
    dsimp only [nbRank]; rw [hnb_eq]
  · intro x j hjx
    change (wiresFrom rAll.1 (inpVec x)).getD (rAll.2 j) false = false
    rw [vAll x j (List.mem_finRange j), decide_eq_false_iff_not]
    dsimp only [nbRank]
    set nb := x.filter (fun i => Hgraph n i j)
    by_cases hj5 : j.val < 5
    · have hnb_add : addCount nb = addCount x := by
        dsimp only [addCount, nb]; congr 1; ext i; simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hix, _⟩, hi5⟩; exact ⟨hix, hi5⟩
        · rintro ⟨hix, hi5⟩; exact ⟨⟨hix, ⟨by intro h; have := congrArg Fin.val h; omega, Or.inl hi5⟩⟩, hi5⟩
      have hnb_rim_lt : rimClique nb < rimClique x := by
        have hnb_rim_le : rimClique nb ≤ 1 := by
          by_contra hgt
          rcases (rimClique_ge_two nb).mp (by omega) with ⟨a, ha, b, hb, ha5, hb5, hab⟩
          have hHa := (Finset.mem_filter.mp ha).2
          have hHb := (Finset.mem_filter.mp hb).2
          rcases hHa with ⟨_, ha5' | hj5' | ha1 | ha2⟩ <;> try omega
          · rcases hHb with ⟨_, hb5' | hj5'' | hb1 | hb2⟩ <;> try omega
          · rcases hHb with ⟨_, hb5' | hj5'' | hb1 | hb2⟩ <;> try omega
        by_cases h1 : 1 ≤ rimClique nb
        · rcases (rimClique_ge_one nb).mp h1 with ⟨a, ha, ha5⟩
          rcases Finset.mem_filter.mp ha with ⟨hax, hHa⟩
          have h2x : 2 ≤ rimClique x := by
            rw [rimClique_ge_two]
            rcases hHa with ⟨_, ha5' | hj5' | ha1 | ha2⟩ <;> try omega
            · exact ⟨a, hax, j, hjx, ha5, hj5, ha1⟩
            · exact ⟨j, hjx, a, hax, hj5, ha5, ha2⟩
          omega
        · have h1x : 1 ≤ rimClique x := (rimClique_ge_one x).mpr ⟨j, hjx, hj5⟩
          omega
      omega
    · have hj5' : 5 ≤ j.val := by omega
      have hnb_sub : nb ⊆ x := Finset.filter_subset _ x
      have hnb_rim_le : rimClique nb ≤ rimClique x := rimClique_mono hnb_sub
      have hnb_add_lt : addCount nb < addCount x := by
        have hsub : nb.filter (fun i : Fin n => 5 ≤ i.val) ⊆
            (x.filter (fun i : Fin n => 5 ≤ i.val)).erase j := by
          intro i hi
          rcases Finset.mem_filter.mp hi with ⟨hinb, hi5⟩
          rcases Finset.mem_filter.mp hinb with ⟨hix, hne, _⟩
          exact Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨hix, hi5⟩⟩
        have hmem : j ∈ x.filter (fun i : Fin n => 5 ≤ i.val) :=
          Finset.mem_filter.mpr ⟨hjx, hj5'⟩
        have hcard1 := Finset.card_le_card hsub
        have hcard2 := Finset.card_erase_of_mem hmem
        have hpos : 0 < (x.filter (fun i : Fin n => 5 ≤ i.val)).card :=
          Finset.card_pos.mpr ⟨j, hmem⟩
        dsimp only [addCount]; omega
      omega

end UpperBoundFalse

section UpperBoundTrue

def colOf (v : ℕ) : ℕ :=
  if v = 0 ∨ v = 2 then 0
  else if v = 1 ∨ v = 3 then 1
  else if v = 4 then 2
  else v - 2

lemma colOf_lt {n : ℕ} (hn : 5 ≤ n) (j : Fin n) : colOf j.val < n - 2 := by
  dsimp only [colOf]; split_ifs <;> omega

lemma colOf_proper {n : ℕ} (i j : Fin n) (h : Hgraph n i j) : colOf i.val ≠ colOf j.val := by
  rcases h with ⟨hne, hi5 | hj5 | h1 | h2⟩
  · have hne' : i.val ≠ j.val := fun heq => hne (Fin.ext heq)
    dsimp only [colOf]; split_ifs <;> omega
  · have hne' : i.val ≠ j.val := fun heq => hne (Fin.ext heq)
    dsimp only [colOf]; split_ifs <;> omega
  · have hne' : i.val ≠ j.val := fun heq => hne (Fin.ext heq)
    dsimp only [colOf]; split_ifs <;> omega
  · have hne' : i.val ≠ j.val := fun heq => hne (Fin.ext heq)
    dsimp only [colOf]; split_ifs <;> omega

def colorOcc {n : ℕ} (x : Finset (Fin n)) (c : ℕ) : Bool :=
  decide (∃ i ∈ x, colOf i.val = c)

lemma colorOcc_mono {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) (c : ℕ) :
    colorOcc u c = true → colorOcc v c = true := by
  intro h
  rcases of_decide_eq_true h with ⟨i, hi, hc⟩
  exact decide_eq_true ⟨i, huv hi, hc⟩

lemma upper_bound_true {k : ℕ} (hk : 2 ≤ k) :
    let t := 2 ^ k - 3
    let n := 5 + t
    ∃ (C : Circuit) (tap : Fin n → ℕ),
      FanInTwo C ∧ ReadsBack (n + 2) C ∧
      C.output < n + 2 + C.size ∧ (∀ j, tap j < n + 2 + C.size) ∧
      notCount C ≤ k + 1 ∧ C.size ≤ 128 * (n + 1) ^ 3 ∧
      let f := fun (x : Finset (Fin n)) (j : Fin n) =>
        (C.wires (inpVec x)).getD (tap j) false
      ((∀ x j, (∀ i ∈ x, Hgraph n i j) → f x j = true) ∧ (∀ x j, j ∈ x → f x j = false)) ∧
      (∀ u v, u ⊆ v → ∀ j, f v j = true → f u j = true) := by
  intro t n
  have hpow4 : 4 ≤ 2 ^ k := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hn5 : 5 ≤ n := by omega
  set M := 3 + t
  have hM_eq : M = 2 ^ k := by omega
  have hM_sub : n - 2 = M := by omega
  set base := n + 2
  set zeroW := n
  set oneW := n + 1
  -- Step 1: 2 OR gates for color 0 (0 ∨ 2) and color 1 (1 ∨ 3)
  set rC0 := emitOr base [] 0 2 with hrC0
  have hC0 := emitOr_spec base [] 0 2 (by omega) (by omega); rw [← hrC0] at hC0
  rcases hC0 with ⟨eC0, lC0, ncC0, nnC0, vC0⟩; have gC0 := eC0.length_le
  set rC1 := emitOr base rC0.1 1 3 with hrC1
  have hC1 := emitOr_spec base rC0.1 1 3 (by omega) (by omega); rw [← hrC1] at hC1
  rcases hC1 with ⟨eC1, lC1, ncC1, nnC1, vC1⟩; have gC1 := eC1.length_le
  have e0C1 : Extends base [] rC1.1 := eC0.trans eC1
  let colW : List ℕ := rC0.2 :: rC1.2 :: 4 :: ((List.range t).map fun m => 5 + m)
  have hcolW_len : colW.length = M := by simp [colW, M]; omega
  have hcolW_lt : ∀ i ∈ colW, i < base + rC1.1.length := by
    intro i hi
    simp only [colW, List.mem_cons, List.mem_map, List.mem_range] at hi
    rcases hi with rfl | rfl | rfl | ⟨m, hm, rfl⟩ <;> omega
  have hcolW_eval : ∀ (x : Finset (Fin n)) (c : ℕ), c < M →
      (wiresFrom rC1.1 (inpVec x)).getD (colW.getD c 0) false = colorOcc x c := by
    intro x c hc
    have hlen := inpVec_length x
    rcases c with _ | _ | _ | m
    · change (wiresFrom rC1.1 (inpVec x)).getD rC0.2 false = colorOcc x 0
      rw [eC1.wire_eq _ hlen rC0.2 lC0, vC0 _ hlen, wiresFrom_nil,
          inpVec_getD_fin x ⟨0, by omega⟩, inpVec_getD_fin x ⟨2, by omega⟩]
      apply Bool.eq_iff_iff.mpr
      simp only [colorOcc, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h0 | h2)
        · exact ⟨⟨0, by omega⟩, h0, rfl⟩
        · exact ⟨⟨2, by omega⟩, h2, rfl⟩
      · rintro ⟨⟨v, hvn⟩, hvx, hcv⟩
        have hv02 : v = 0 ∨ v = 2 := by dsimp [colOf] at hcv; split_ifs at hcv <;> omega
        rcases hv02 with rfl | rfl
        · exact Or.inl hvx
        · exact Or.inr hvx
    · change (wiresFrom rC1.1 (inpVec x)).getD rC1.2 false = colorOcc x 1
      rw [vC1 _ hlen, wiresFrom_getD_lt rC0.1 _ 1 (by rw [hlen]; omega),
          wiresFrom_getD_lt rC0.1 _ 3 (by rw [hlen]; omega),
          inpVec_getD_fin x ⟨1, by omega⟩, inpVec_getD_fin x ⟨3, by omega⟩]
      apply Bool.eq_iff_iff.mpr
      simp only [colorOcc, Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (h1 | h3)
        · exact ⟨⟨1, by omega⟩, h1, rfl⟩
        · exact ⟨⟨3, by omega⟩, h3, rfl⟩
      · rintro ⟨⟨v, hvn⟩, hvx, hcv⟩
        have hv13 : v = 1 ∨ v = 3 := by dsimp [colOf] at hcv; split_ifs at hcv <;> omega
        rcases hv13 with rfl | rfl
        · exact Or.inl hvx
        · exact Or.inr hvx
    · change (wiresFrom rC1.1 (inpVec x)).getD 4 false = colorOcc x 2
      rw [wiresFrom_getD_lt rC1.1 _ 4 (by rw [hlen]; omega), inpVec_getD_fin x ⟨4, by omega⟩]
      apply Bool.eq_iff_iff.mpr
      simp only [colorOcc, decide_eq_true_eq]
      constructor
      · intro h4; exact ⟨⟨4, by omega⟩, h4, rfl⟩
      · rintro ⟨⟨v, hvn⟩, hvx, hcv⟩
        have hv4 : v = 4 := by dsimp [colOf] at hcv; split_ifs at hcv <;> omega
        subst hv4; exact hvx
    · have hm : m < t := by omega
      have hget : colW.getD (m + 3) 0 = 5 + m := by
        simp [colW, List.getD_eq_getElem?_getD, hm]
      rw [hget, wiresFrom_getD_lt rC1.1 _ (5 + m) (by rw [hlen]; omega),
          inpVec_getD_fin x ⟨5 + m, by omega⟩]
      apply Bool.eq_iff_iff.mpr
      simp only [colorOcc, decide_eq_true_eq]
      constructor
      · intro h5m
        refine ⟨⟨5 + m, by omega⟩, h5m, ?_⟩
        dsimp [colOf]; split_ifs <;> omega
      · rintro ⟨⟨v, hvn⟩, hvx, hcv⟩
        have hvm : v = 5 + m := by dsimp [colOf] at hcv; split_ifs at hcv <;> omega
        subst hvm; exact hvx
  -- Step 2: total occupied colors threshold bank
  set rTot := monotoneCountThresh base oneW rC1.1 colW with hrTot
  have hTot := monotoneCountThresh_spec base oneW colW rC1.1 (by omega) hcolW_lt
  rw [← hrTot] at hTot
  rcases hTot with ⟨eTot, lenTot, lTot, ncTot, nnTot, vTot⟩; have gTot := eTot.length_le
  -- Step 3: chainInv on rTot.2.tail (length M = 2^k < 2^(k+1))
  let posTot : List ℕ := rTot.2.tail
  have hposTot_len : posTot.length = M := by simp [posTot, lenTot, hcolW_len]
  have hposTot_lt : ∀ i ∈ posTot, i < base + rTot.1.length := fun i hi => lTot i (List.mem_of_mem_tail hi)
  have hM_lt_pow : posTot.length < 2 ^ (k + 1) := by
    rw [hposTot_len, hM_eq, pow_succ]
    have : 0 < 2 ^ k := by positivity
    omega
  set rInv := chainInv base (k + 1) rTot.1 posTot with hrInv
  have hInv := chainInv_spec base (k + 1) rTot.1 posTot hM_lt_pow hposTot_lt
  rw [← hrInv] at hInv
  rcases hInv with ⟨eInv, lenInv, lInv, ncInv, nnInv, vInv⟩; have gInv := eInv.length_le
  let leW : List ℕ := rInv.2 ++ [oneW]
  have hleW_len : leW.length = M + 1 := by simp [leW, lenInv, hposTot_len]
  have hleW_lt : ∀ i ∈ leW, i < base + rInv.1.length := by
    intro i hi
    simp only [leW, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact lInv i hi
    · omega
  let totCount : Finset (Fin n) → ℕ := fun x =>
    ((List.range M).filter (fun c => colorOcc x c)).length
  have htot_eq_colW : ∀ (x : Finset (Fin n)),
      (colW.filter fun i => (wiresFrom rC1.1 (inpVec x)).getD i false).length = totCount x := by
    intro x
    have hmap : colW = (List.range M).map (fun c => colW.getD c 0) := by
      apply List.ext_getElem
      · simp [hcolW_len]
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_range]
        simp [List.getD_eq_getElem?_getD, hi1]
    conv_lhs => rw [hmap, List.filter_map, List.length_map]
    congr 1
    refine List.filter_congr fun c hc => ?_
    exact hcolW_eval x c (List.mem_range.mp hc)
  have htot_le_M : ∀ x, totCount x ≤ M := fun x => by
    dsimp only [totCount]; exact le_trans (List.length_filter_le _ _) (by simp)
  have hposTot_eval : ∀ (x : Finset (Fin n)) (i : ℕ), i < M →
      (wiresFrom rTot.1 (inpVec x)).getD (posTot.getD i 0) false = decide (i + 1 ≤ totCount x) := by
    intro x i hi
    have hlen := inpVec_length x
    have h1w : (wiresFrom rC1.1 (inpVec x)).getD oneW false = true := by
      rw [wiresFrom_getD_lt rC1.1 _ oneW (by rw [hlen]; omega), inpVec_getD_true]
    have htail : posTot.getD i 0 = rTot.2.getD (i + 1) 0 := by
      cases hr : rTot.2 with
      | nil => rw [hr] at lenTot; simp at lenTot
      | cons h tl => simp [posTot, hr]
    rw [htail, vTot (inpVec x) hlen h1w (i + 1) (by rw [hcolW_len]; omega), htot_eq_colW x]
  have hleW_eval : ∀ (x : Finset (Fin n)) (ℓ : ℕ), ℓ < M + 1 →
      (wiresFrom rInv.1 (inpVec x)).getD (leW.getD ℓ 0) false = decide (totCount x ≤ ℓ) := by
    intro x ℓ hℓ
    have hlen := inpVec_length x
    by_cases hlt : ℓ < M
    · have hget : leW.getD ℓ 0 = rInv.2.getD ℓ 0 :=
        getD_append_left rInv.2 [oneW] ℓ 0 (by rw [lenInv, hposTot_len]; exact hlt)
      rw [hget]
      have hdec : ∀ (i j : ℕ), i < posTot.length → j < posTot.length → i ≤ j →
          (wiresFrom rTot.1 (inpVec x)).getD (posTot.getD j 0) false ≤
            (wiresFrom rTot.1 (inpVec x)).getD (posTot.getD i 0) false := by
        intro i j hi hj hij
        rw [hposTot_len] at hi hj
        rw [hposTot_eval x j hj, hposTot_eval x i hi, bool_le_iff]
        intro h; exact decide_eq_true (by have := of_decide_eq_true h; omega)
      rw [vInv (inpVec x) hlen hdec ℓ (by rw [hposTot_len]; exact hlt), hposTot_eval x ℓ hlt]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      omega
    · have heq : ℓ = M := by omega
      subst heq
      have hget : leW.getD M 0 = oneW := by
        rw [getD_append_right rInv.2 [oneW] M 0 (by rw [lenInv, hposTot_len])]
        have hsub : M - rInv.2.length = 0 := by rw [lenInv, hposTot_len]; omega
        rw [hsub]; rfl
      rw [hget, wiresFrom_getD_lt rInv.1 (inpVec x) oneW (by rw [hlen]; omega), inpVec_getD_true]
      symm; exact decide_eq_true (htot_le_M x)
  have eC1Inv : Extends base rC1.1 rInv.1 := eTot.trans eInv
  have gC1Inv := eC1Inv.length_le
  -- Step 4: for each color c < M, compute omitCount thresholds and compare with leW
  let stepC : List Gate → ℕ → List Gate × ℕ := fun gs c =>
    let omitW := colW.take c ++ colW.drop (c + 1)
    let r1 := monotoneCountThresh base oneW gs omitW
    let geW := r1.2 ++ [zeroW]
    compareThresh base r1.1 zeroW leW geW
  have hstepC : ∀ (gs : List Gate) (c : ℕ), c < M → Extends base rInv.1 gs →
      Extends base gs (stepC gs c).1 ∧
      (stepC gs c).2 < base + (stepC gs c).1.length ∧
      notCount ⟨(stepC gs c).1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot (stepC gs c).1 ≤ nonNot gs + (M ^ 2 + 2 * (M + 1)) ∧
      ∀ (x : Finset (Fin n)),
        (wiresFrom (stepC gs c).1 (inpVec x)).getD (stepC gs c).2 false = !(colorOcc x c) := by
    intro gs c hc hExtInv
    have gInvGs := hExtInv.length_le
    have eC1Gs : Extends base rC1.1 gs := eC1Inv.trans hExtInv
    have gC1Gs := eC1Gs.length_le
    dsimp only [stepC]
    let omitW := colW.take c ++ colW.drop (c + 1)
    have homit_len : omitW.length = M - 1 := by
      simp only [omitW, List.length_append, List.length_take, List.length_drop, hcolW_len]; omega
    have homit_lt : ∀ i ∈ omitW, i < base + gs.length := by
      intro i hi
      simp only [omitW, List.mem_append] at hi
      rcases hi with hi | hi
      · exact lt_of_lt_of_le (hcolW_lt i (List.mem_of_mem_take hi)) (by omega)
      · exact lt_of_lt_of_le (hcolW_lt i (List.mem_of_mem_drop hi)) (by omega)
    set r1 := monotoneCountThresh base oneW gs omitW with hr1
    have h1 := monotoneCountThresh_spec base oneW omitW gs (by omega) homit_lt
    rw [← hr1] at h1
    rcases h1 with ⟨e1, len1, l1, nc1, nn1, v1⟩; have g1 := e1.length_le
    let geW := r1.2 ++ [zeroW]
    have hgeW_len : geW.length = M + 1 := by
      simp only [geW, List.length_append, List.length_singleton, len1, homit_len]; omega
    have hgeW_lt : ∀ i ∈ geW, i < base + r1.1.length := by
      intro i hi
      simp only [geW, List.mem_append, List.mem_singleton] at hi
      rcases hi with hi | rfl
      · exact l1 i hi
      · omega
    set r2 := compareThresh base r1.1 zeroW leW geW with hr2
    have h2 := compareThresh_spec base leW geW r1.1 zeroW
      (by rw [hleW_len, hgeW_len]) (by omega)
      (fun i hi => lt_of_lt_of_le (hleW_lt i hi) (by omega)) hgeW_lt
    rw [← hr2] at h2
    rcases h2 with ⟨e2, l2, nc2, nn2, v2⟩
    have hsq : omitW.length ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left (by omega) 2
    refine ⟨e1.trans e2, l2, by omega, by rw [hleW_len] at nn2; omega, ?_⟩
    intro x
    have hlen := inpVec_length x
    have homit_count : (omitW.filter fun i => (wiresFrom gs (inpVec x)).getD i false).length +
        (if colorOcc x c then 1 else 0) = totCount x := by
      have hsplit : colW = colW.take c ++ [colW.getD c 0] ++ colW.drop (c + 1) := by
        have hc' : c < colW.length := by rw [hcolW_len]; exact hc
        have h1s := List.take_append_drop c colW
        have h2s : colW.drop c = colW[c] :: colW.drop (c + 1) := List.drop_eq_getElem_cons hc'
        have hget : colW.getD c 0 = colW[c] := by simp [List.getD_eq_getElem?_getD, hc']
        rw [hget, ← List.singleton_append, List.append_assoc]
        conv_lhs => rw [← h1s]
        rw [h2s]; rfl
      have hcongr_col : (colW.filter fun i => (wiresFrom gs (inpVec x)).getD i false) =
          (colW.filter fun i => (wiresFrom rC1.1 (inpVec x)).getD i false) :=
        List.filter_congr fun i hi => eC1Gs.wire_eq (inpVec x) hlen i (hcolW_lt i hi)
      have htot' : (colW.filter fun i => (wiresFrom gs (inpVec x)).getD i false).length = totCount x := by
        rw [hcongr_col, htot_eq_colW x]
      rw [← htot']
      conv_rhs => rw [hsplit]
      simp only [omitW, List.filter_append, List.length_append, List.filter_cons, List.filter_nil]
      have hmid : (wiresFrom gs (inpVec x)).getD (colW.getD c 0) false = colorOcc x c := by
        rw [eC1Gs.wire_eq (inpVec x) hlen _ (hcolW_lt _ (getD_mem colW c 0 (by rw [hcolW_len]; exact hc)))]
        exact hcolW_eval x c hc
      rw [hmid]
      cases colorOcc x c <;> simp <;> omega
    set omitC := (omitW.filter fun i => (wiresFrom gs (inpVec x)).getD i false).length
    have homitC_le : omitC ≤ M - 1 := by
      have := List.length_filter_le (fun i => (wiresFrom gs (inpVec x)).getD i false) omitW
      omega
    have hgeW_ev : ∀ ℓ, ℓ < M + 1 →
        (wiresFrom r1.1 (inpVec x)).getD (geW.getD ℓ 0) false = decide (ℓ ≤ omitC) := by
      intro ℓ hℓ
      have h1w : (wiresFrom gs (inpVec x)).getD oneW false = true := by
        rw [wiresFrom_getD_lt gs (inpVec x) oneW (by rw [hlen]; omega), inpVec_getD_true]
      by_cases hlt : ℓ < M
      · have hget : geW.getD ℓ 0 = r1.2.getD ℓ 0 :=
          getD_append_left r1.2 [zeroW] ℓ 0 (by rw [len1, homit_len]; omega)
        rw [hget, v1 (inpVec x) hlen h1w ℓ (by rw [homit_len]; omega)]
      · have heq : ℓ = M := by omega
        subst heq
        have hget : geW.getD M 0 = zeroW := by
          rw [getD_append_right r1.2 [zeroW] M 0 (by rw [len1, homit_len]; omega)]
          have hsub : M - r1.2.length = 0 := by rw [len1, homit_len]; omega
          rw [hsub]; rfl
        rw [hget, wiresFrom_getD_lt r1.1 (inpVec x) zeroW (by rw [hlen]; omega), inpVec_getD_false]
        symm; exact decide_eq_false (by omega)
    rw [v2 (inpVec x) hlen, wiresFrom_getD_lt r1.1 (inpVec x) zeroW (by rw [hlen]; omega),
        inpVec_getD_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true', hleW_len]
    have hExtInv1 : Extends base rInv.1 r1.1 := hExtInv.trans e1
    constructor
    · rintro ⟨ℓ, hℓ, hA, hB⟩
      rw [hExtInv1.wire_eq (inpVec x) hlen _ (hleW_lt _ (getD_mem leW ℓ 0 (by omega))),
          hleW_eval x ℓ hℓ, decide_eq_true_eq] at hA
      rw [hgeW_ev ℓ hℓ, decide_eq_true_eq] at hB
      cases hco : colorOcc x c
      · rfl
      · rw [hco] at homit_count; simp at homit_count; omega
    · intro hfalse
      have htot_eq_omit : totCount x = omitC := by
        rw [hfalse] at homit_count; simp at homit_count; omega
      have htot_lt : totCount x < M + 1 := by have := htot_le_M x; omega
      refine ⟨totCount x, htot_lt, ?_, ?_⟩
      · rw [hExtInv1.wire_eq (inpVec x) hlen _ (hleW_lt _ (getD_mem leW _ 0 (by omega))),
            hleW_eval x _ htot_lt, decide_eq_true_eq]
      · rw [hgeW_ev _ htot_lt, decide_eq_true_eq]; omega
  -- Build all M color negation taps
  have hBuildCols : ∀ (cs : List ℕ) (gs : List Gate), (∀ c ∈ cs, c < M) → Extends base rInv.1 gs →
      let r := buildAssoc stepC zeroW gs cs
      Extends base gs r.1 ∧
      (∀ c, r.2 c < base + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      nonNot r.1 ≤ nonNot gs + cs.length * (M ^ 2 + 2 * (M + 1)) ∧
      ∀ (x : Finset (Fin n)), ∀ c ∈ cs,
        (wiresFrom r.1 (inpVec x)).getD (r.2 c) false = !(colorOcc x c) := by
    intro cs
    induction cs with
    | nil =>
      intro gs _ _
      dsimp only [buildAssoc]
      refine ⟨Extends.refl base gs, fun _ => by omega, rfl, by simp, fun _ _ h => by cases h⟩
    | cons a cs ih =>
      intro gs hcs hExt
      dsimp only [buildAssoc]
      have ha : a < M := hcs a (List.mem_cons_self ..)
      have hcs' : ∀ c ∈ cs, c < M := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
      rcases hstepC gs a ha hExt with ⟨he1, hl1, hnc1, hnn1, hv1⟩
      have g1 := he1.length_le
      rcases ih (stepC gs a).1 hcs' (hExt.trans he1) with ⟨he2, hl2, hnc2, hnn2, hv2⟩
      have g2 := he2.length_le
      have hmul : (cs.length + 1) * (M ^ 2 + 2 * (M + 1)) =
          cs.length * (M ^ 2 + 2 * (M + 1)) + (M ^ 2 + 2 * (M + 1)) := by ring
      refine ⟨he1.trans he2, ?_, by omega, by simp only [List.length_cons]; omega, ?_⟩
      · intro c; by_cases hc : c = a
        · simp only [hc, ↓reduceIte]; omega
        · simp only [hc, ↓reduceIte]; exact hl2 c
      · intro x c hc
        by_cases hca : c = a
        · subst hca; simp only [↓reduceIte]
          rw [he2.wire_eq (inpVec x) (inpVec_length x) _ hl1, hv1 x]
        · simp only [hca, ↓reduceIte]
          exact hv2 x c ((List.mem_cons.mp hc).resolve_left hca)
  set rAll := buildAssoc stepC zeroW rInv.1 (List.range M) with hrAll
  have hAll := hBuildCols (List.range M) rInv.1 (fun c hc => List.mem_range.mp hc) (Extends.refl base rInv.1)
  rw [← hrAll] at hAll
  rcases hAll with ⟨eAll, lAll, ncAll, nnAll, vAll⟩
  have eFinal : Extends base [] rAll.1 := (e0C1.trans eC1Inv).trans eAll
  rcases eFinal with ⟨extra, hEq, hFit, hRB⟩
  simp only [List.nil_append, List.length_nil, add_zero] at hEq hRB
  subst hEq
  let C : Circuit := ⟨rAll.1, 0⟩
  let tap : Fin n → ℕ := fun j => rAll.2 (colOf j.val)
  have hCnot : notCount C ≤ k + 1 := by
    change notCount ⟨rAll.1, 0⟩ ≤ k + 1
    rw [ncAll]
    have h0 : notCount ⟨[], 0⟩ = 0 := rfl
    omega
  have hk_le_n : k + 1 ≤ n := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  have hCsize : C.size ≤ 128 * (n + 1) ^ 3 := by
    have hnn_fin : nonNot rAll.1 ≤ 2 + M ^ 2 + 4 * M + M * (M ^ 2 + 2 * (M + 1)) := by
      simp only [List.length_range] at nnAll
      rw [nonNot_nil, zero_add] at nnC0
      rw [hcolW_len] at nnTot
      rw [hposTot_len] at nnInv
      omega
    have hsz : C.size = nonNot rAll.1 + notCount C := by
      change rAll.1.length = rAll.1.length - notCount ⟨rAll.1, 0⟩ + notCount ⟨rAll.1, 0⟩
      have := notCount_le_length rAll.1 0
      omega
    have hM_le_n : M ≤ n := by omega
    have hMsq : M ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hM_le_n 2
    have hMcube : M ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left hM_le_n 3
    have hexp1 : M * (M ^ 2 + 2 * (M + 1)) = M ^ 3 + 2 * M ^ 2 + 2 * M := by ring
    have hexp2 : (n + 1) ^ 3 = n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by ring
    omega
  have htap_eval : ∀ (x : Finset (Fin n)) (j : Fin n),
      (C.wires (inpVec x)).getD (tap j) false = !(colorOcc x (colOf j.val)) := by
    intro x j
    have hcj : colOf j.val < M := by have := colOf_lt hn5 j; omega
    exact vAll x (colOf j.val) (List.mem_range.mpr hcj)
  refine ⟨C, tap, hFit, hRB, by dsimp [C]; omega, fun j => lAll (colOf j.val), hCnot, hCsize, ⟨?_, ?_⟩, ?_⟩
  · intro x j hH
    dsimp only
    rw [htap_eval x j]
    simp only [colorOcc, Bool.not_eq_true', decide_eq_false_iff_not, not_exists, not_and]
    intro i hi
    exact colOf_proper i j (hH i hi)
  · intro x j hjx
    dsimp only
    rw [htap_eval x j]
    simp only [colorOcc, Bool.not_eq_false', decide_eq_true_eq]
    exact ⟨j, hjx, rfl⟩
  · intro u v huv j hvt
    dsimp only at hvt ⊢
    rw [htap_eval u j]
    rw [htap_eval v j] at hvt
    cases hcu : colorOcc u (colOf j.val)
    · rfl
    · have hcv := colorOcc_mono huv (colOf j.val) hcu
      rw [hcv] at hvt; cases hvt

end UpperBoundTrue

section MainProof

theorem main :
∀ k : Nat, 2 ≤ k →
  let t := 2^k - 3
  let n := 5+t
  let X := Finset (Fin n)
  let H := fun (i j : Fin n) => i ≠ j ∧
    (5 ≤ i.val ∨ 5 ≤ j.val ∨ (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)
  let possible := fun (decreasing : Bool) (r s : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ s ∧
      let f := fun (x : X) (j : Fin n) =>
        (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true])).getD (tap j) false
      ((∀ x j, (∀ i ∈ x, H i j) → f x j = true) ∧ (∀ x j, j ∈ x → f x j = false)) ∧
      (decreasing = true → ∀ u v, u ⊆ v → ∀ j, f v j = true → f u j = true)
  (∀ r : Nat, ((∃ s, possible false r s) ↔ k ≤ r) ∧ ((∃ s, possible true r s) ↔ k+1 ≤ r)) ∧
  possible false k (128*(n+1)^3) ∧ possible true (k+1) (128*(n+1)^3) := by
  intro k hk
  dsimp only
  have hUF := upper_bound_false hk
  have hUT := upper_bound_true hk
  have hPF : ∃ (C : Circuit) (tap : Fin (5 + (2 ^ k - 3)) → ℕ),
      FanInTwo C ∧ ReadsBack (5 + (2 ^ k - 3) + 2) C ∧
      C.output < 5 + (2 ^ k - 3) + 2 + C.size ∧
      (∀ j, tap j < 5 + (2 ^ k - 3) + 2 + C.size) ∧
      notCount C ≤ k ∧ C.size ≤ 128 * (5 + (2 ^ k - 3) + 1) ^ 3 ∧
      ((∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) j,
        (∀ i ∈ x, Hgraph (5 + (2 ^ k - 3)) i j) → (C.wires (inpVec x)).getD (tap j) false = true) ∧
       (∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) j,
        j ∈ x → (C.wires (inpVec x)).getD (tap j) false = false)) ∧
      (false = true → ∀ (u v : Finset (Fin (5 + (2 ^ k - 3)))), u ⊆ v → ∀ j,
        (C.wires (inpVec v)).getD (tap j) false = true →
        (C.wires (inpVec u)).getD (tap j) false = true) := by
    rcases hUF with ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨C, tap, h1, h2, h3, h4, h5, h6, ⟨h7, h8⟩, fun h => by cases h⟩
  have hPT : ∃ (C : Circuit) (tap : Fin (5 + (2 ^ k - 3)) → ℕ),
      FanInTwo C ∧ ReadsBack (5 + (2 ^ k - 3) + 2) C ∧
      C.output < 5 + (2 ^ k - 3) + 2 + C.size ∧
      (∀ j, tap j < 5 + (2 ^ k - 3) + 2 + C.size) ∧
      notCount C ≤ k + 1 ∧ C.size ≤ 128 * (5 + (2 ^ k - 3) + 1) ^ 3 ∧
      ((∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) j,
        (∀ i ∈ x, Hgraph (5 + (2 ^ k - 3)) i j) → (C.wires (inpVec x)).getD (tap j) false = true) ∧
       (∀ (x : Finset (Fin (5 + (2 ^ k - 3)))) j,
        j ∈ x → (C.wires (inpVec x)).getD (tap j) false = false)) ∧
      (true = true → ∀ (u v : Finset (Fin (5 + (2 ^ k - 3)))), u ⊆ v → ∀ j,
        (C.wires (inpVec v)).getD (tap j) false = true →
        (C.wires (inpVec u)).getD (tap j) false = true) := by
    rcases hUT with ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, fun _ => h8⟩
  refine ⟨?_, hPF, hPT⟩
  intro r
  constructor
  · constructor
    · rintro ⟨s, C, tap, hfit, _, _, _, hnot, _, ⟨hpos, hneg⟩, _⟩
      exact lower_bound_false hk C tap hfit hnot hpos hneg
    · intro hkr
      rcases hPF with ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩
      exact ⟨128 * (5 + (2 ^ k - 3) + 1) ^ 3, C, tap, h1, h2, h3, h4, le_trans h5 hkr, h6, h7, h8⟩
  · constructor
    · rintro ⟨s, C, tap, hfit, _, _, _, hnot, _, ⟨hpos, hneg⟩, hdec⟩
      exact lower_bound_true hk C tap hfit hnot hpos hneg (hdec rfl)
    · intro hkr
      rcases hPT with ⟨C, tap, h1, h2, h3, h4, h5, h6, h7, h8⟩
      exact ⟨128 * (5 + (2 ^ k - 3) + 1) ^ 3, C, tap, h1, h2, h3, h4, le_trans h5 hkr, h6, h7, h8⟩

end MainProof

end PEqualNP.Outside.L_lib_1260_aux

theorem PEqualNP.Outside.L_lib_1260 :
∀ k : Nat, 2 ≤ k →
  let t := 2^k - 3
  let n := 5+t
  let X := Finset (Fin n)
  let H := fun (i j : Fin n) => i ≠ j ∧
    (5 ≤ i.val ∨ 5 ≤ j.val ∨ (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val)
  let possible := fun (decreasing : Bool) (r s : Nat) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin n → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ j, tap j < n+2+C.size) ∧
      PEqualNP.NotBracket.notCount C ≤ r ∧ C.size ≤ s ∧
      let f := fun (x : X) (j : Fin n) =>
        (C.wires (List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true])).getD (tap j) false
      ((∀ x j, (∀ i ∈ x, H i j) → f x j = true) ∧ (∀ x j, j ∈ x → f x j = false)) ∧
      (decreasing = true → ∀ u v, u ⊆ v → ∀ j, f v j = true → f u j = true)
  (∀ r : Nat, ((∃ s, possible false r s) ↔ k ≤ r) ∧ ((∃ s, possible true r s) ↔ k+1 ≤ r)) ∧
  possible false k (128*(n+1)^3) ∧ possible true (k+1) (128*(n+1)^3) :=
  PEqualNP.Outside.L_lib_1260_aux.main
