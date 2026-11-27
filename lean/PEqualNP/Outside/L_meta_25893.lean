import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25893

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open scoped BigOperators

def GoodGate (g : Gate) : Prop :=
  g.inputs.length ≤ 2 ∧ (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))

def GoodGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧ ∀ g ∈ gs, GoodGate g

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun u g => u ++ [g.op.eval (g.inputs.map fun i => u.getD i false)]) w

def Extends (gs₁ gs₂ : List Gate) : Prop :=
  ∃ extra, gs₂ = gs₁ ++ extra

lemma extends_refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma extends_trans {gs₁ gs₂ gs₃ : List Gate} (h₁ : Extends gs₁ gs₂) (h₂ : Extends gs₂ gs₃) :
    Extends gs₁ gs₃ := by
  rcases h₁ with ⟨e₁, rfl⟩
  rcases h₂ with ⟨e₂, rfl⟩
  exact ⟨e₁ ++ e₂, by simp [List.append_assoc]⟩

lemma extends_length {gs₁ gs₂ : List Gate} (h : Extends gs₁ gs₂) : gs₁.length ≤ gs₂.length := by
  rcases h with ⟨e, rfl⟩
  simp

lemma evalGates_nil (w : List Bool) : evalGates [] w = w := rfl

lemma evalGates_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    evalGates (g :: gs) w =
      evalGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma evalGates_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    evalGates (gs₁ ++ gs₂) w = evalGates gs₂ (evalGates gs₁ w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    rw [evalGates_cons, ih]
    simp
    omega

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    (evalGates gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [evalGates_cons, ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma evalGates_extends_getD {gs₁ gs₂ : List Gate} (h : Extends gs₁ gs₂) (xs : List Bool)
    {i : ℕ} (hi : i < xs.length + gs₁.length) :
    (evalGates gs₂ xs).getD i false = (evalGates gs₁ xs).getD i false := by
  rcases h with ⟨extra, rfl⟩
  rw [evalGates_append, evalGates_getD_lt]
  rw [evalGates_length]
  exact hi

lemma evalGates_push_getD (gs : List Gate) (g : Gate) (xs : List Bool) :
    (evalGates (gs ++ [g]) xs).getD (xs.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (evalGates gs xs).getD i false) := by
  rw [evalGates_append, evalGates_cons, evalGates_nil]
  have hlen : (evalGates gs xs).length = xs.length + gs.length := evalGates_length gs xs
  simp [List.getD_eq_getElem?_getD, ← hlen]

lemma goodGates_nil (n : ℕ) : GoodGates n [] := by
  refine ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩

lemma goodGates_push {n : ℕ} {gs : List Gate} {g : Gate} (hgs : GoodGates n gs)
    (hg : GoodGate g) (hin : ∀ i ∈ g.inputs, i < n + gs.length) :
    GoodGates n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.1 j hlt i hi
    · have hj_eq : j = gs.length := by omega
      subst hj_eq
      have hget : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        simp [gateAt, List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hgs.2 g' h
    · exact hg

def addNot (n : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.not, [a]⟩], n + gs.length)

def addAnd (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.and, [a, b]⟩], n + gs.length)

def addOr (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.or, [a, b]⟩], n + gs.length)

def addXor (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := addOr n gs a b
  let r2 := addAnd n r1.1 a b
  let r3 := addNot n r2.1 r2.2
  addAnd n r3.1 r1.2 r3.2

def addZero (n : ℕ) (gs : List Gate) : List Gate × ℕ :=
  let r1 := addNot n gs 0
  addAnd n r1.1 0 r1.2

lemma addNot_spec {n : ℕ} {gs : List Gate} {a : ℕ} (hgs : GoodGates n gs) (ha : a < n + gs.length) :
    let r := addNot n gs a
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false = !((evalGates gs xs).getD a false) := by
  refine ⟨⟨[⟨.not, [a]⟩], rfl⟩, ?_, by simp [addNot], by simp [addNot], ?_⟩
  · refine goodGates_push hgs ⟨by simp, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩ ?_
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ha
  · intro xs hxs
    simp only [addNot]
    have h := evalGates_push_getD gs ⟨.not, [a]⟩ xs
    rw [hxs] at h
    simpa [GateOp.eval] using h

lemma addAnd_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addAnd n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false = ((evalGates gs xs).getD a false && (evalGates gs xs).getD b false) := by
  refine ⟨⟨[⟨.and, [a, b]⟩], rfl⟩, ?_, by simp [addAnd], by simp [addAnd], ?_⟩
  · refine goodGates_push hgs ⟨by simp, Or.inl rfl⟩ ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro xs hxs
    simp only [addAnd]
    have h := evalGates_push_getD gs ⟨.and, [a, b]⟩ xs
    rw [hxs] at h
    simpa [GateOp.eval] using h

lemma addOr_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addOr n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false = ((evalGates gs xs).getD a false || (evalGates gs xs).getD b false) := by
  refine ⟨⟨[⟨.or, [a, b]⟩], rfl⟩, ?_, by simp [addOr], by simp [addOr], ?_⟩
  · refine goodGates_push hgs ⟨by simp, Or.inr (Or.inl rfl)⟩ ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro xs hxs
    simp only [addOr]
    have h := evalGates_push_getD gs ⟨.or, [a, b]⟩ xs
    rw [hxs] at h
    simpa [GateOp.eval] using h

lemma addXor_spec {n : ℕ} {gs : List Gate} {a b : ℕ} (hgs : GoodGates n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let r := addXor n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 4 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false = xor ((evalGates gs xs).getD a false) ((evalGates gs xs).getD b false) := by
  have h1 := addOr_spec hgs ha hb
  have h2 := addAnd_spec h1.2.1 (lt_of_lt_of_le ha (by omega)) (lt_of_lt_of_le hb (by omega))
  have h3 := addNot_spec h2.2.1 h2.2.2.2.1
  have h1_w_lt : (addOr n gs a b).2 < n + (addNot n (addAnd n (addOr n gs a b).1 a b).1 (addAnd n (addOr n gs a b).1 a b).2).1.length := by
    have := h1.2.2.2.1
    omega
  have h4 := addAnd_spec h3.2.1 h1_w_lt h3.2.2.2.1
  refine ⟨extends_trans h1.1 (extends_trans h2.1 (extends_trans h3.1 h4.1)), h4.2.1, ?_, h4.2.2.2.1, ?_⟩
  · dsimp only [addXor]
    omega
  · intro xs hxs
    dsimp only [addXor]
    rw [h4.2.2.2.2 xs hxs]
    have e1 := evalGates_extends_getD (extends_trans h2.1 h3.1) xs (by rw [hxs]; exact h1.2.2.2.1)
    rw [e1, h3.2.2.2.2 xs hxs, h2.2.2.2.2 xs hxs]
    have e2a := evalGates_extends_getD h1.1 xs (by rw [hxs]; exact ha)
    have e2b := evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hb)
    rw [h1.2.2.2.2 xs hxs, e2a, e2b]
    cases (evalGates gs xs).getD a false <;> cases (evalGates gs xs).getD b false <;> rfl

lemma addZero_spec {n : ℕ} (hn : 0 < n) {gs : List Gate} (hgs : GoodGates n gs) :
    let r := addZero n gs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 2 ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n → (evalGates r.1 xs).getD r.2 false = false := by
  have h1 := addNot_spec hgs (by omega : 0 < n + gs.length)
  have h2 := addAnd_spec h1.2.1 (by omega : 0 < n + (addNot n gs 0).1.length) h1.2.2.2.1
  refine ⟨extends_trans h1.1 h2.1, h2.2.1, by dsimp [addZero]; omega, h2.2.2.2.1, ?_⟩
  intro xs hxs
  dsimp only [addZero]
  rw [h2.2.2.2.2 xs hxs, h1.2.2.2.2 xs hxs]
  have e := evalGates_extends_getD h1.1 xs (by rw [hxs]; exact Nat.add_pos_left hn gs.length)
  rw [e]
  cases (evalGates gs xs).getD 0 false <;> rfl

def addAndFold (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws =>
    let r := addAnd n gs acc w
    addAndFold n r.1 r.2 ws

def addAndList (n : ℕ) (gs : List Gate) (z : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, z)
  | w :: ws => addAndFold n gs w ws

def addOrFold (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws =>
    let r := addOr n gs acc w
    addOrFold n r.1 r.2 ws

def addOrList (n : ℕ) (gs : List Gate) (z : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, z)
  | w :: ws => addOrFold n gs w ws

def addXorFold (n : ℕ) (gs : List Gate) (acc : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, acc)
  | w :: ws =>
    let r := addXor n gs acc w
    addXorFold n r.1 r.2 ws

def addXorList (n : ℕ) (gs : List Gate) (z : ℕ) : List ℕ → List Gate × ℕ
  | [] => (gs, z)
  | w :: ws => addXorFold n gs w ws

lemma addAndFold_spec {n : ℕ} {gs : List Gate} {acc : ℕ} {ws : List ℕ}
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length)
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    let r := addAndFold n gs acc ws
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + ws.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false =
          ((evalGates gs xs).getD acc false && ws.all (fun w => (evalGates gs xs).getD w false)) := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addAndFold], hacc, fun xs _ => by simp [addAndFold]⟩
  | cons w ws ih =>
    have hw : w < n + gs.length := hws w (by simp)
    have h1 := addAnd_spec hgs hacc hw
    have hws' : ∀ w' ∈ ws, w' < n + (addAnd n gs acc w).1.length := by
      intro w' hw'
      have := hws w' (by simp [hw'])
      omega
    have ih' := ih h1.2.1 h1.2.2.2.1 hws'
    refine ⟨extends_trans h1.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ?_⟩
    · simp only [addAndFold, List.length_cons]
      omega
    · intro xs hxs
      simp only [addAndFold]
      rw [ih'.2.2.2.2 xs hxs, h1.2.2.2.2 xs hxs]
      simp only [List.all_cons, Bool.and_assoc]
      congr 2
      rw [Bool.eq_iff_iff]
      simp only [List.all_eq_true]
      constructor
      · intro h w' hw'
        have hw'_lt := hws w' (List.mem_cons_of_mem w hw')
        have heq := evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hw'_lt)
        rw [← heq]
        exact h w' hw'
      · intro h w' hw'
        have hw'_lt := hws w' (List.mem_cons_of_mem w hw')
        have heq := evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hw'_lt)
        rw [heq]
        exact h w' hw'

lemma addAndList_spec {n : ℕ} {gs : List Gate} {z : ℕ} {ws : List ℕ}
    (hgs : GoodGates n gs) (hz : z < n + gs.length)
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    let r := addAndList n gs z ws
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + ws.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false =
          (if ws = [] then (evalGates gs xs).getD z false else ws.all (fun w => (evalGates gs xs).getD w false)) := by
  cases ws with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addAndList], hz, fun xs _ => by simp [addAndList]⟩
  | cons w₀ ws =>
    have h := addAndFold_spec hgs (hws w₀ (by simp)) (fun w' hw' => hws w' (List.mem_cons_of_mem w₀ hw'))
    refine ⟨h.1, h.2.1, by simp [addAndList]; omega, h.2.2.2.1, fun xs hxs => ?_⟩
    simpa [addAndList] using h.2.2.2.2 xs hxs

lemma addOrFold_spec {n : ℕ} {gs : List Gate} {acc : ℕ} {ws : List ℕ}
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length)
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    let r := addOrFold n gs acc ws
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + ws.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false =
          ((evalGates gs xs).getD acc false || ws.any (fun w => (evalGates gs xs).getD w false)) := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addOrFold], hacc, fun xs _ => by simp [addOrFold]⟩
  | cons w ws ih =>
    have hw : w < n + gs.length := hws w (by simp)
    have h1 := addOr_spec hgs hacc hw
    have hws' : ∀ w' ∈ ws, w' < n + (addOr n gs acc w).1.length := by
      intro w' hw'
      have := hws w' (by simp [hw'])
      omega
    have ih' := ih h1.2.1 h1.2.2.2.1 hws'
    refine ⟨extends_trans h1.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ?_⟩
    · simp only [addOrFold, List.length_cons]
      omega
    · intro xs hxs
      simp only [addOrFold]
      rw [ih'.2.2.2.2 xs hxs, h1.2.2.2.2 xs hxs]
      simp only [List.any_cons, Bool.or_assoc]
      congr 2
      rw [Bool.eq_iff_iff]
      simp only [List.any_eq_true]
      constructor
      · rintro ⟨w', hw', hval⟩
        refine ⟨w', hw', ?_⟩
        have hw'_lt := hws w' (List.mem_cons_of_mem w hw')
        rwa [← evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hw'_lt)]
      · rintro ⟨w', hw', hval⟩
        refine ⟨w', hw', ?_⟩
        have hw'_lt := hws w' (List.mem_cons_of_mem w hw')
        rwa [evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hw'_lt)]

lemma addOrList_spec {n : ℕ} {gs : List Gate} {z : ℕ} {ws : List ℕ}
    (hgs : GoodGates n gs) (hz : z < n + gs.length)
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    let r := addOrList n gs z ws
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + ws.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false =
          (if ws = [] then (evalGates gs xs).getD z false else ws.any (fun w => (evalGates gs xs).getD w false)) := by
  cases ws with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addOrList], hz, fun xs _ => by simp [addOrList]⟩
  | cons w₀ ws =>
    have h := addOrFold_spec hgs (hws w₀ (by simp)) (fun w' hw' => hws w' (List.mem_cons_of_mem w₀ hw'))
    refine ⟨h.1, h.2.1, by simp [addOrList]; omega, h.2.2.2.1, fun xs hxs => ?_⟩
    simpa [addOrList] using h.2.2.2.2 xs hxs

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

lemma xor_eq_b2z (a b : Bool) :
    xor a b = decide (b2z a + b2z b = 1) := by
  cases a <;> cases b <;> decide

lemma b2z_decide_eq (x : ZMod 2) : b2z (decide (x = 1)) = x := by
  fin_cases x <;> rfl

lemma addXorFold_spec {n : ℕ} {gs : List Gate} {acc : ℕ} {ws : List ℕ}
    (hgs : GoodGates n gs) (hacc : acc < n + gs.length)
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    let r := addXorFold n gs acc ws
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + 4 * ws.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false =
          decide (b2z ((evalGates gs xs).getD acc false) +
            (ws.map (fun w => b2z ((evalGates gs xs).getD w false))).sum = 1) := by
  induction ws generalizing gs acc with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addXorFold], hacc, fun xs _ => ?_⟩
    simp only [addXorFold, List.map_nil, List.sum_nil, add_zero]
    cases (evalGates gs xs).getD acc false <;> decide
  | cons w ws ih =>
    have hw : w < n + gs.length := hws w (by simp)
    have h1 := addXor_spec hgs hacc hw
    have hws' : ∀ w' ∈ ws, w' < n + (addXor n gs acc w).1.length := by
      intro w' hw'
      have := hws w' (by simp [hw'])
      omega
    have ih' := ih h1.2.1 h1.2.2.2.1 hws'
    refine ⟨extends_trans h1.1 ih'.1, ih'.2.1, ?_, ih'.2.2.2.1, ?_⟩
    · simp only [addXorFold, List.length_cons]
      omega
    · intro xs hxs
      simp only [addXorFold]
      rw [ih'.2.2.2.2 xs hxs, h1.2.2.2.2 xs hxs, xor_eq_b2z, b2z_decide_eq]
      simp only [List.map_cons, List.sum_cons, add_assoc]
      have hmap : List.map (fun w_1 => b2z ((evalGates (addXor n gs acc w).1 xs).getD w_1 false)) ws =
          List.map (fun w => b2z ((evalGates gs xs).getD w false)) ws := by
        apply List.map_congr_left
        intro w' hw'
        have hw'_lt := hws w' (List.mem_cons_of_mem w hw')
        rw [evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hw'_lt)]
      rw [hmap]

lemma addXorList_spec {n : ℕ} {gs : List Gate} {z : ℕ} {ws : List ℕ}
    (hgs : GoodGates n gs) (hz : z < n + gs.length)
    (hws : ∀ w ∈ ws, w < n + gs.length)
    (hz_false : ∀ xs : List Bool, xs.length = n → (evalGates gs xs).getD z false = false) :
    let r := addXorList n gs z ws
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 4 * ws.length ∧ r.2 < n + r.1.length ∧
      ∀ xs : List Bool, xs.length = n →
        (evalGates r.1 xs).getD r.2 false =
          decide ((ws.map (fun w => b2z ((evalGates gs xs).getD w false))).sum = 1) := by
  cases ws with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addXorList], hz, fun xs hxs => ?_⟩
    simp only [addXorList, List.map_nil, List.sum_nil]
    rw [hz_false xs hxs]
    decide
  | cons w₀ ws =>
    have h := addXorFold_spec hgs (hws w₀ (by simp)) (fun w' hw' => hws w' (List.mem_cons_of_mem w₀ hw'))
    refine ⟨h.1, h.2.1, by simp [addXorList]; omega, h.2.2.2.1, fun xs hxs => ?_⟩
    simpa [addXorList] using h.2.2.2.2 xs hxs

def buildVecAux (f : List Gate → ℕ → List Gate × ℕ) : ℕ → List Gate → List Gate × (ℕ → ℕ)
  | 0, gs => (gs, fun _ => 0)
  | m + 1, gs =>
    let r1 := buildVecAux f m gs
    let r2 := f r1.1 m
    (r2.1, fun j => if j = m then r2.2 else r1.2 j)

lemma buildVecAux_spec {n : ℕ} (f : List Gate → ℕ → List Gate × ℕ) (cost : ℕ → ℕ)
    (m : ℕ) (gs : List Gate) (hgs : GoodGates n gs)
    (hf : ∀ (gs' : List Gate) (j : ℕ), j < m → GoodGates n gs' → Extends gs gs' →
      let r := f gs' j
      Extends gs' r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs'.length + cost j ∧ r.2 < n + r.1.length) :
    let r := buildVecAux f m gs
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + ∑ j ∈ Finset.range m, cost j ∧
      (∀ j < m, r.2 j < n + r.1.length) ∧
      ∀ (j : ℕ), j < m → ∀ (xs : List Bool), xs.length = n →
        (evalGates r.1 xs).getD (r.2 j) false =
          (evalGates (f (buildVecAux f j gs).1 j).1 xs).getD (f (buildVecAux f j gs).1 j).2 false := by
  induction m with
  | zero =>
    refine ⟨extends_refl gs, hgs, by simp [buildVecAux], fun j hj => by omega, fun j hj => by omega⟩
  | succ m ih =>
    have ih' := ih (fun gs' j hj => hf gs' j (Nat.lt_succ_of_lt hj))
    have hstep := hf (buildVecAux f m gs).1 m (Nat.lt_succ_self m) ih'.2.1 ih'.1
    refine ⟨extends_trans ih'.1 hstep.1, hstep.2.1, ?_, ?_, ?_⟩
    · simp only [buildVecAux, Finset.sum_range_succ]
      omega
    · intro j _hj
      simp only [buildVecAux]
      split_ifs with hjm
      · exact hstep.2.2.2
      · have hjm' : j < m := by omega
        have := ih'.2.2.2.1 j hjm'
        have := extends_length hstep.1
        omega
    · intro j hj xs hxs
      simp only [buildVecAux]
      split_ifs with hjm
      · subst hjm; rfl
      · have hjm' : j < m := by omega
        rw [evalGates_extends_getD hstep.1 xs (by rw [hxs]; exact ih'.2.2.2.1 j hjm')]
        exact ih'.2.2.2.2 j hjm' xs hxs

def addVecXor (s n : ℕ) (gs : List Gate) (a b : Fin s → ℕ) : List Gate × (Fin s → ℕ) :=
  let r := buildVecAux (fun gs' j =>
    if hj : j < s then addXor n gs' (a ⟨j, hj⟩) (b ⟨j, hj⟩) else (gs', 0)) s gs
  (r.1, fun j => r.2 j.val)

lemma addVecXor_spec {s n : ℕ} {gs : List Gate} {a b : Fin s → ℕ}
    (hgs : GoodGates n gs)
    (ha : ∀ j : Fin s, a j < n + gs.length) (hb : ∀ j : Fin s, b j < n + gs.length) :
    let r := addVecXor s n gs a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 4 * s ∧
      (∀ j : Fin s, r.2 j < n + r.1.length) ∧
      ∀ (j : Fin s) (xs : List Bool), xs.length = n →
        (evalGates r.1 xs).getD (r.2 j) false =
          xor ((evalGates gs xs).getD (a j) false) ((evalGates gs xs).getD (b j) false) := by
  let f : List Gate → ℕ → List Gate × ℕ := fun gs' j =>
    if hj : j < s then addXor n gs' (a ⟨j, hj⟩) (b ⟨j, hj⟩) else (gs', 0)
  have hf : ∀ (gs' : List Gate) (j : ℕ), j < s → GoodGates n gs' → Extends gs gs' →
      let r := f gs' j
      Extends gs' r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs'.length + 4 ∧ r.2 < n + r.1.length := by
    intro gs' j hj hgs' hext
    have hlen := extends_length hext
    dsimp only [f]
    split_ifs
    have hax := addXor_spec hgs' (lt_of_lt_of_le (ha ⟨j, hj⟩) (by omega))
      (lt_of_lt_of_le (hb ⟨j, hj⟩) (by omega))
    exact ⟨hax.1, hax.2.1, by omega, hax.2.2.2.1⟩
  have hbva := buildVecAux_spec f (fun _ => 4) s gs hgs hf
  refine ⟨hbva.1, hbva.2.1, ?_, fun j => hbva.2.2.2.1 j.val j.isLt, ?_⟩
  · have := hbva.2.2.1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at this
    change (buildVecAux f s gs).1.length ≤ gs.length + 4 * s
    omega
  · intro j xs hxs
    change (evalGates (buildVecAux f s gs).1 xs).getD ((buildVecAux f s gs).2 j.val) false = _
    rw [hbva.2.2.2.2 j.val j.isLt xs hxs]
    dsimp only [f]
    split_ifs with hj
    · have hsub := buildVecAux_spec f (fun _ => 4) j.val gs hgs (fun gs' i hi => hf gs' i (lt_trans hi j.isLt))
      have hlen := extends_length hsub.1
      have hax := addXor_spec hsub.2.1 (lt_of_lt_of_le (ha j) (by omega))
        (lt_of_lt_of_le (hb j) (by omega))
      rw [hax.2.2.2.2 xs hxs]
      rw [evalGates_extends_getD hsub.1 xs (by rw [hxs]; exact ha j)]
      rw [evalGates_extends_getD hsub.1 xs (by rw [hxs]; exact hb j)]
    · exact absurd j.isLt hj

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [List.flatMap_cons, List.sum_append, ih]

lemma list_sum_map_finRange {n : ℕ} {α : Type*} [AddCommMonoid α] (f : Fin n → α) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  rw [Fin.sum_univ_def]

def mulPairs (s r : ℕ) : List (Fin s × Fin s) :=
  (List.finRange s).flatMap (fun p =>
    ((List.finRange s).filter (fun q => decide (p.val + q.val = r))).map (fun q => (p, q)))

lemma mulPairs_length_sum (s : ℕ) (hs : 0 < s) :
    ∑ r ∈ Finset.range (2 * s - 1), (mulPairs s r).length = s * s := by
  have hlen : ∀ r, (mulPairs s r).length =
      ∑ p : Fin s, ∑ q : Fin s, if p.val + q.val = r then 1 else 0 := by
    intro r
    simp only [mulPairs, List.length_flatMap, List.length_map, list_sum_map_finRange]
    congr 1; ext p
    have : ∀ (l : List (Fin s)),
        (l.filter (fun q => decide (p.val + q.val = r))).length =
          (l.map (fun q => if p.val + q.val = r then 1 else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        by_cases hx : p.val + x.val = r
        · simp [hx, ih]; omega
        · simp [hx, ih]
    rw [this, list_sum_map_finRange]
  simp_rw [hlen]
  rw [Finset.sum_comm]
  have h1 : ∑ p : Fin s, ∑ r ∈ Finset.range (2 * s - 1),
      ∑ q : Fin s, (if p.val + q.val = r then 1 else 0) =
      ∑ p : Fin s, ∑ q : Fin s, ∑ r ∈ Finset.range (2 * s - 1),
      (if p.val + q.val = r then 1 else 0) := by
    congr 1; ext p; exact Finset.sum_comm
  rw [h1]
  have h2 : ∀ p q : Fin s, ∑ r ∈ Finset.range (2 * s - 1),
      (if p.val + q.val = r then 1 else 0) = 1 := by
    intro p q
    have hlt : p.val + q.val < 2 * s - 1 := by omega
    rw [Finset.sum_ite_eq]
    simp [hlt]
  simp_rw [h2]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

def addAndPairs (n : ℕ) (a b : Fin s → ℕ) (gs : List Gate) :
    List (Fin s × Fin s) → List Gate × List ℕ
  | [] => (gs, [])
  | (p, q) :: rest =>
    let r1 := addAnd n gs (a p) (b q)
    let r2 := addAndPairs n a b r1.1 rest
    (r2.1, r1.2 :: r2.2)

lemma addAndPairs_spec {s n : ℕ} {a b : Fin s → ℕ} {gs : List Gate}
    (hgs : GoodGates n gs)
    (ha : ∀ j : Fin s, a j < n + gs.length) (hb : ∀ j : Fin s, b j < n + gs.length)
    (ps : List (Fin s × Fin s)) :
    let r := addAndPairs n a b gs ps
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length = gs.length + ps.length ∧
      (∀ w ∈ r.2, w < n + r.1.length) ∧
      ∀ xs : List Bool, xs.length = n →
        (r.2.map (fun w => b2z ((evalGates r.1 xs).getD w false))).sum =
          (ps.map (fun pq => b2z ((evalGates gs xs).getD (a pq.1) false) *
            b2z ((evalGates gs xs).getD (b pq.2) false))).sum := by
  induction ps generalizing gs with
  | nil =>
    refine ⟨extends_refl gs, hgs, by simp [addAndPairs], fun w hw => by simp [addAndPairs] at hw,
      fun xs _ => by simp [addAndPairs]⟩
  | cons pq rest ih =>
    rcases pq with ⟨p, q⟩
    have h1 := addAnd_spec hgs (ha p) (hb q)
    have ha' : ∀ j : Fin s, a j < n + (addAnd n gs (a p) (b q)).1.length := fun j =>
      lt_of_lt_of_le (ha j) (by have := h1.2.2.1; omega)
    have hb' : ∀ j : Fin s, b j < n + (addAnd n gs (a p) (b q)).1.length := fun j =>
      lt_of_lt_of_le (hb j) (by have := h1.2.2.1; omega)
    have ih' := ih h1.2.1 ha' hb'
    have hlen_ext := extends_length ih'.1
    refine ⟨extends_trans h1.1 ih'.1, ih'.2.1, ?_, ?_, ?_⟩
    · simp only [addAndPairs, List.length_cons]
      omega
    · intro w hw
      simp only [addAndPairs, List.mem_cons] at hw
      rcases hw with rfl | hw
      · have h2 := h1.2.2.2.1
        dsimp only [addAndPairs]
        omega
      · exact ih'.2.2.2.1 w hw
    · intro xs hxs
      simp only [addAndPairs, List.map_cons, List.sum_cons]
      rw [evalGates_extends_getD ih'.1 xs (by rw [hxs]; exact h1.2.2.2.1)]
      rw [h1.2.2.2.2 xs hxs]
      rw [ih'.2.2.2.2 xs hxs]
      have ea : ∀ j : Fin s, (evalGates (addAnd n gs (a p) (b q)).1 xs).getD (a j) false =
          (evalGates gs xs).getD (a j) false :=
        fun j => evalGates_extends_getD h1.1 xs (by rw [hxs]; exact ha j)
      have eb : ∀ j : Fin s, (evalGates (addAnd n gs (a p) (b q)).1 xs).getD (b j) false =
          (evalGates gs xs).getD (b j) false :=
        fun j => evalGates_extends_getD h1.1 xs (by rw [hxs]; exact hb j)
      have hmul : b2z ((evalGates gs xs).getD (a p) false && (evalGates gs xs).getD (b q) false) =
          b2z ((evalGates gs xs).getD (a p) false) * b2z ((evalGates gs xs).getD (b q) false) := by
        cases (evalGates gs xs).getD (a p) false <;> cases (evalGates gs xs).getD (b q) false <;> rfl
      rw [hmul]
      congr 1
      congr 1
      apply List.map_congr_left
      intro pq' _
      rw [ea pq'.1, eb pq'.2]

lemma mulPairs_sum_eq {s : ℕ} (u v : Fin s → ZMod 2) (r : ℕ) :
    ((mulPairs s r).map (fun pq => u pq.1 * v pq.2)).sum =
      ∑ p : Fin s, ∑ q : Fin s, if p.val + q.val = r then u p * v q else 0 := by
  simp only [mulPairs, List.map_flatMap, list_sum_flatMap, list_sum_map_finRange]
  congr 1; ext p
  have hlist : ∀ (l : List (Fin s)),
      (List.map (fun pq : Fin s × Fin s => u pq.1 * v pq.2)
        (List.map (fun q => (p, q)) (l.filter (fun q => decide (p.val + q.val = r))))).sum =
        (l.map (fun q => if p.val + q.val = r then u p * v q else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih =>
      simp only [List.filter_cons]
      by_cases hx : p.val + x.val = r
      · simp only [hx, decide_true, List.map_cons, List.sum_cons, ite_true]
        rw [ih]
      · simp only [hx, decide_false, List.map_cons, List.sum_cons, ite_false, zero_add]
        exact ih
  rw [hlist, list_sum_map_finRange]

def addMulGF (s : ℕ) (rem : Fin (2 * s - 1) → Fin s → ZMod 2) (n : ℕ)
    (gs : List Gate) (z : ℕ) (a b : Fin s → ℕ) : List Gate × (Fin s → ℕ) :=
  let c := buildVecAux (fun gs' r =>
    let r1 := addAndPairs n a b gs' (mulPairs s r)
    addXorList n r1.1 z r1.2) (2 * s - 1) gs
  let out := buildVecAux (fun gs' j =>
    if hj : j < s then
      let ws := ((List.finRange (2 * s - 1)).filter (fun r => decide (rem r ⟨j, hj⟩ = 1))).map (fun r => c.2 r.val)
      addXorList n gs' z ws
    else (gs', 0)) s c.1
  (out.1, fun j => out.2 j.val)

lemma addMulGF_spec {s n : ℕ} (hs : 0 < s) (rem : Fin (2 * s - 1) → Fin s → ZMod 2)
    {gs : List Gate} {z : ℕ} {a b : Fin s → ℕ}
    (hgs : GoodGates n gs) (hz : z < n + gs.length)
    (hz_false : ∀ xs : List Bool, xs.length = n → (evalGates gs xs).getD z false = false)
    (ha : ∀ j : Fin s, a j < n + gs.length) (hb : ∀ j : Fin s, b j < n + gs.length) :
    let r := addMulGF s rem n gs z a b
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + 13 * (s * s) ∧
      (∀ j : Fin s, r.2 j < n + r.1.length) ∧
      ∀ (j : Fin s) (xs : List Bool), xs.length = n →
        (evalGates r.1 xs).getD (r.2 j) false =
          decide ((∑ p : Fin s, ∑ q : Fin s,
            rem ⟨p.val + q.val, by omega⟩ j *
              b2z ((evalGates gs xs).getD (a p) false) *
              b2z ((evalGates gs xs).getD (b q) false)) = 1) := by
  let fc : List Gate → ℕ → List Gate × ℕ := fun gs' r =>
    let r1 := addAndPairs n a b gs' (mulPairs s r)
    addXorList n r1.1 z r1.2
  have hfc : ∀ (gs' : List Gate) (r : ℕ), r < 2 * s - 1 → GoodGates n gs' → Extends gs gs' →
      let res := fc gs' r
      Extends gs' res.1 ∧ GoodGates n res.1 ∧ res.1.length ≤ gs'.length + 5 * (mulPairs s r).length ∧
        res.2 < n + res.1.length := by
    intro gs' r _ hgs' hext
    have hlen := extends_length hext
    have h1 := addAndPairs_spec hgs' (fun j => lt_of_lt_of_le (ha j) (by omega))
      (fun j => lt_of_lt_of_le (hb j) (by omega)) (mulPairs s r)
    have h2 := addXorList_spec h1.2.1 (lt_of_lt_of_le hz (by omega)) h1.2.2.2.1 (fun xs hxs => by
      rw [evalGates_extends_getD (extends_trans hext h1.1) xs (by rw [hxs]; exact hz)]
      exact hz_false xs hxs)
    have hlen2 : (addAndPairs n a b gs' (mulPairs s r)).2.length = (mulPairs s r).length := by
      have : ∀ l gs0, (addAndPairs n a b gs0 l).2.length = l.length := by
        intro l; induction l with
        | nil => intro _; rfl
        | cons pq rest ih => intro _; simp [addAndPairs, ih]
      exact this _ _
    refine ⟨extends_trans h1.1 h2.1, h2.2.1, ?_, h2.2.2.2.1⟩
    dsimp only [fc]
    omega
  have hc := buildVecAux_spec fc (fun r => 5 * (mulPairs s r).length) (2 * s - 1) gs hgs hfc
  let c := buildVecAux fc (2 * s - 1) gs
  let fout : List Gate → ℕ → List Gate × ℕ := fun gs' j =>
    if hj : j < s then
      let ws := ((List.finRange (2 * s - 1)).filter (fun r => decide (rem r ⟨j, hj⟩ = 1))).map (fun r => c.2 r.val)
      addXorList n gs' z ws
    else (gs', 0)
  have hfout : ∀ (gs' : List Gate) (j : ℕ), j < s → GoodGates n gs' → Extends c.1 gs' →
      let res := fout gs' j
      Extends gs' res.1 ∧ GoodGates n res.1 ∧ res.1.length ≤ gs'.length + 4 * (2 * s - 1) ∧
        res.2 < n + res.1.length := by
    intro gs' j hj hgs' hext
    have hlen := extends_length hext
    have hc_ext := extends_length hc.1
    have hgs_le : gs.length ≤ gs'.length := le_trans hc_ext hlen
    dsimp only [fout]
    split_ifs
    have hws_lt : ∀ w ∈ ((List.finRange (2 * s - 1)).filter (fun r => decide (rem r ⟨j, hj⟩ = 1))).map
        (fun r => c.2 r.val), w < n + gs'.length := by
      intro w hw
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
      rcases hw with ⟨r, _, rfl⟩
      have hcr : c.2 r.val < n + c.1.length := hc.2.2.2.1 r.val r.isLt
      omega
    have h2 := addXorList_spec hgs' (lt_of_lt_of_le hz (by omega)) hws_lt (fun xs hxs => by
      rw [evalGates_extends_getD (extends_trans hc.1 hext) xs (by rw [hxs]; exact hz)]
      exact hz_false xs hxs)
    have hlen_ws : (((List.finRange (2 * s - 1)).filter (fun r => decide (rem r ⟨j, hj⟩ = 1))).map
        (fun r => c.2 r.val)).length ≤ 2 * s - 1 := by
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    exact ⟨h2.1, h2.2.1, by omega, h2.2.2.2.1⟩
  have hout := buildVecAux_spec fout (fun _ => 4 * (2 * s - 1)) s c.1 hc.2.1 hfout
  refine ⟨extends_trans hc.1 hout.1, hout.2.1, ?_, fun j => hout.2.2.2.1 j.val j.isLt, ?_⟩
  · have hsum1 : ∑ r ∈ Finset.range (2 * s - 1), 5 * (mulPairs s r).length = 5 * (s * s) := by
      rw [← Finset.mul_sum, mulPairs_length_sum s hs]
    have hsum2 : ∑ _j ∈ Finset.range s, 4 * (2 * s - 1) ≤ 8 * (s * s) := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h4 : 4 * (2 * s - 1) ≤ 8 * s := by omega
      nlinarith
    have hc1 : c.1.length ≤ gs.length + 5 * (s * s) := by
      have := hc.2.2.1
      change c.1.length ≤ gs.length + ∑ j ∈ Finset.range (2 * s - 1), 5 * (mulPairs s j).length at this
      omega
    have ho1 := hout.2.2.1
    change (buildVecAux fout s c.1).1.length ≤ gs.length + 13 * (s * s)
    dsimp only [c] at ho1
    omega
  · intro j xs hxs
    change (evalGates (buildVecAux fout s c.1).1 xs).getD ((buildVecAux fout s c.1).2 j.val) false = _
    rw [hout.2.2.2.2 j.val j.isLt xs hxs]
    dsimp only [fout]
    split_ifs with hj
    · have hsub := buildVecAux_spec fout (fun _ => 4 * (2 * s - 1)) j.val c.1 hc.2.1
        (fun gs' i hi => hfout gs' i (lt_trans hi j.isLt))
      have hsub_len := extends_length hsub.1
      have hc_len := extends_length hc.1
      set gs' := (buildVecAux fout j.val c.1).1
      set ws := ((List.finRange (2 * s - 1)).filter (fun r => decide (rem r j = 1))).map (fun r => c.2 r.val)
      have hws_lt : ∀ w ∈ ws, w < n + gs'.length := by
        intro w hw
        simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
        rcases hw with ⟨r, _, rfl⟩
        have hcr : c.2 r.val < n + c.1.length := hc.2.2.2.1 r.val r.isLt
        omega
      have hx := addXorList_spec hsub.2.1
        (lt_of_lt_of_le hz (Nat.add_le_add_left (le_trans hc_len hsub_len) n)) hws_lt (fun xs hxs => by
        rw [evalGates_extends_getD (extends_trans hc.1 hsub.1) xs (by rw [hxs]; exact hz)]
        exact hz_false xs hxs)
      rw [hx.2.2.2.2 xs hxs]
      have hc_val : ∀ r : Fin (2 * s - 1),
          b2z ((evalGates gs' xs).getD (c.2 r.val) false) =
            ∑ p : Fin s, ∑ q : Fin s, if p.val + q.val = r.val then
              b2z ((evalGates gs xs).getD (a p) false) * b2z ((evalGates gs xs).getD (b q) false) else 0 := by
        intro r
        rw [evalGates_extends_getD hsub.1 xs (by rw [hxs]; exact hc.2.2.2.1 r.val r.isLt)]
        change b2z ((evalGates (buildVecAux fc (2 * s - 1) gs).1 xs).getD
          ((buildVecAux fc (2 * s - 1) gs).2 r.val) false) = _
        rw [hc.2.2.2.2 r.val r.isLt xs hxs]
        dsimp only [fc]
        have hsub_c := buildVecAux_spec fc (fun r => 5 * (mulPairs s r).length) r.val gs hgs
          (fun gs0 i hi => hfc gs0 i (lt_trans hi r.isLt))
        have hsub_c_len := extends_length hsub_c.1
        set gs0 := (buildVecAux fc r.val gs).1
        have h1 := addAndPairs_spec hsub_c.2.1
          (fun p => lt_of_lt_of_le (ha p) (Nat.add_le_add_left hsub_c_len n))
          (fun q => lt_of_lt_of_le (hb q) (Nat.add_le_add_left hsub_c_len n)) (mulPairs s r.val)
        have h2 := addXorList_spec h1.2.1
          (lt_of_lt_of_le hz (Nat.add_le_add_left (le_trans hsub_c_len (extends_length h1.1)) n))
          h1.2.2.2.1 (fun xs hxs => by
          rw [evalGates_extends_getD (extends_trans hsub_c.1 h1.1) xs (by rw [hxs]; exact hz)]
          exact hz_false xs hxs)
        rw [h2.2.2.2.2 xs hxs, b2z_decide_eq, h1.2.2.2.2 xs hxs]
        have ha_ext : ∀ p : Fin s, (evalGates (buildVecAux fc r.val gs).1 xs).getD (a p) false = (evalGates gs xs).getD (a p) false :=
          fun p => evalGates_extends_getD hsub_c.1 xs (by rw [hxs]; exact ha p)
        have hb_ext : ∀ q : Fin s, (evalGates (buildVecAux fc r.val gs).1 xs).getD (b q) false = (evalGates gs xs).getD (b q) false :=
          fun q => evalGates_extends_getD hsub_c.1 xs (by rw [hxs]; exact hb q)
        simp_rw [ha_ext, hb_ext]
        exact mulPairs_sum_eq (fun p => b2z ((evalGates gs xs).getD (a p) false))
          (fun q => b2z ((evalGates gs xs).getD (b q) false)) r.val
      have hws_sum : (ws.map (fun w => b2z ((evalGates gs' xs).getD w false))).sum =
          ∑ r : Fin (2 * s - 1), if rem r j = 1 then b2z ((evalGates gs' xs).getD (c.2 r.val) false) else 0 := by
        dsimp only [ws]
        rw [List.map_map]
        have hlist : ∀ (l : List (Fin (2 * s - 1))),
            (List.map ((fun w => b2z ((evalGates gs' xs).getD w false)) ∘ fun r => c.2 r.val)
              (l.filter (fun r => decide (rem r j = 1)))).sum =
              (l.map (fun r => if rem r j = 1 then b2z ((evalGates gs' xs).getD (c.2 r.val) false) else 0)).sum := by
          intro l
          induction l with
          | nil => simp
          | cons x xs ih =>
            simp only [List.filter_cons]
            by_cases hx : rem x j = 1
            · simp only [hx, decide_true, List.map_cons, List.sum_cons, ite_true]
              rw [Function.comp_apply, ih]
            · simp only [hx, decide_false, List.map_cons, List.sum_cons, ite_false, zero_add]
              exact ih
        rw [hlist, list_sum_map_finRange]
      rw [hws_sum]
      simp_rw [hc_val]
      have hcoeff : ∀ r : Fin (2 * s - 1),
          (if rem r j = 1 then ∑ p : Fin s, ∑ q : Fin s,
            if p.val + q.val = r.val then
              b2z ((evalGates gs xs).getD (a p) false) * b2z ((evalGates gs xs).getD (b q) false) else 0
          else 0) =
          ∑ p : Fin s, ∑ q : Fin s,
            if p.val + q.val = r.val then
              rem r j * b2z ((evalGates gs xs).getD (a p) false) * b2z ((evalGates gs xs).getD (b q) false)
            else 0 := by
        intro r
        rcases zmod2_cases (rem r j) with hr0 | hr1
        · simp [hr0]
        · simp [hr1]
      simp_rw [hcoeff]
      rw [Finset.sum_comm]
      have hswap : ∑ p : Fin s, ∑ r : Fin (2 * s - 1), ∑ q : Fin s,
          (if p.val + q.val = r.val then
            rem r j * b2z ((evalGates gs xs).getD (a p) false) * b2z ((evalGates gs xs).getD (b q) false) else 0) =
          ∑ p : Fin s, ∑ q : Fin s, ∑ r : Fin (2 * s - 1),
          (if p.val + q.val = r.val then
            rem r j * b2z ((evalGates gs xs).getD (a p) false) * b2z ((evalGates gs xs).getD (b q) false) else 0) := by
        congr 1; ext p; exact Finset.sum_comm
      rw [hswap]
      congr 1
      apply congr_arg (· = 1)
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      have hlt : p.val + q.val < 2 * s - 1 := by omega
      rw [Finset.sum_eq_single ⟨p.val + q.val, hlt⟩]
      · simp
      · intro r _ hne
        have : p.val + q.val ≠ r.val := fun h => hne (Fin.ext h.symm)
        simp [this]
      · intro _hmem
        exact absurd (Finset.mem_univ _) _hmem
    · exact absurd j.isLt hj

def addHornerAux (s : ℕ) (rem : Fin (2 * s - 1) → Fin s → ZMod 2) (d : ℕ)
    (n : ℕ) (z : ℕ) (xPad : Fin d → Fin s → ℕ) (uWires : Fin s → ℕ) :
    ℕ → List Gate × (Fin s → ℕ) → List Gate × (Fin s → ℕ)
  | 0, st => st
  | r + 1, st =>
    let r1 := addMulGF s rem n st.1 z st.2 uWires
    let xr := if hr : r < d then xPad ⟨r, hr⟩ else fun _ => z
    let r2 := addVecXor s n r1.1 r1.2 xr
    addHornerAux s rem d n z xPad uWires r r2

lemma addHornerAux_spec {s d n : ℕ} (hs : 0 < s) (rem : Fin (2 * s - 1) → Fin s → ZMod 2)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] (b : Module.Basis (Fin s) (ZMod 2) K)
    (hrem : ∀ x y : K, ∀ j : Fin s,
      (∑ p : Fin s, ∑ q : Fin s,
        rem ⟨p.val + q.val, by omega⟩ j * b.repr x p * b.repr y q) = b.repr (x * y) j)
    {gs0 : List Gate} {z : ℕ} {xPad : Fin d → Fin s → ℕ} {uWires : Fin s → ℕ}
    (hz : z < n + gs0.length)
    (hz_false : ∀ xs : List Bool, xs.length = n → (evalGates gs0 xs).getD z false = false)
    (hxPad : ∀ i : Fin d, ∀ j : Fin s, xPad i j < n + gs0.length)
    (hu : ∀ j : Fin s, uWires j < n + gs0.length)
    (r : ℕ) (hr : r ≤ d) (st : List Gate × (Fin s → ℕ))
    (hst_ext : Extends gs0 st.1) (hst_good : GoodGates n st.1)
    (hst_w : ∀ j : Fin s, st.2 j < n + st.1.length) :
    let res := addHornerAux s rem d n z xPad uWires r st
    Extends st.1 res.1 ∧ GoodGates n res.1 ∧
      res.1.length ≤ st.1.length + r * (13 * (s * s) + 4 * s) ∧
      (∀ j : Fin s, res.2 j < n + res.1.length) ∧
      ∀ (xs : List Bool), xs.length = n →
        ∀ (uVal accVal : K) (xVal : Fin d → K),
          (∀ j : Fin s, b2z ((evalGates gs0 xs).getD (uWires j) false) = b.repr uVal j) →
          (∀ j : Fin s, b2z ((evalGates st.1 xs).getD (st.2 j) false) = b.repr accVal j) →
          (∀ i : Fin d, ∀ j : Fin s, b2z ((evalGates gs0 xs).getD (xPad i j) false) = b.repr (xVal i) j) →
          ∀ j : Fin s, b2z ((evalGates res.1 xs).getD (res.2 j) false) =
            b.repr (accVal * uVal ^ r +
              ∑ i ∈ Finset.range r, if hi : i < d then xVal ⟨i, hi⟩ * uVal ^ i else 0) j := by
  induction r generalizing st with
  | zero =>
    refine ⟨extends_refl st.1, hst_good, by simp [addHornerAux], hst_w, ?_⟩
    intro xs _ uVal accVal _ _ hacc _ j
    simp only [addHornerAux, pow_zero, mul_one, Finset.range_zero, Finset.sum_empty, add_zero]
    exact hacc j
  | succ r ih =>
    have hst_len := extends_length hst_ext
    have hrz : z < n + st.1.length := lt_of_lt_of_le hz (by omega)
    have hru : ∀ j : Fin s, uWires j < n + st.1.length := fun j => lt_of_lt_of_le (hu j) (by omega)
    have hz_st : ∀ xs : List Bool, xs.length = n → (evalGates st.1 xs).getD z false = false := fun xs hxs => by
      rw [evalGates_extends_getD hst_ext xs (by rw [hxs]; exact hz)]
      exact hz_false xs hxs
    have hm := addMulGF_spec hs rem hst_good hrz hz_st hst_w hru
    set r1 := addMulGF s rem n st.1 z st.2 uWires
    have hm_len := extends_length hm.1
    have hrd : r < d := by omega
    have hxr_lt : ∀ j : Fin s, xPad ⟨r, hrd⟩ j < n + r1.1.length := fun j =>
      lt_of_lt_of_le (hxPad ⟨r, hrd⟩ j) (by omega)
    have hv := addVecXor_spec hm.2.1 hm.2.2.2.1 hxr_lt
    set r2 := addVecXor s n r1.1 r1.2 (xPad ⟨r, hrd⟩)
    have ih' := ih (by omega) r2 (extends_trans hst_ext (extends_trans hm.1 hv.1)) hv.2.1 hv.2.2.2.1
    have hres_eq : addHornerAux s rem d n z xPad uWires (r + 1) st =
        addHornerAux s rem d n z xPad uWires r r2 := by
      change addHornerAux s rem d n z xPad uWires r (addVecXor s n r1.1 r1.2 (if hr' : r < d then xPad ⟨r, hr'⟩ else fun _ => z)) = _
      split_ifs
      rfl
    rw [hres_eq]
    refine ⟨extends_trans hm.1 (extends_trans hv.1 ih'.1), ih'.2.1, ?_, ih'.2.2.2.1, ?_⟩
    · have hm1 := hm.2.2.1
      have hv1 := hv.2.2.1
      have hi1 := ih'.2.2.1
      rw [Nat.succ_mul]
      omega
    · intro xs hxs uVal accVal xVal huVal hacc hxVal j
      have h_r2 : ∀ j' : Fin s, b2z ((evalGates r2.1 xs).getD (r2.2 j') false) =
          b.repr (accVal * uVal + xVal ⟨r, hrd⟩) j' := by
        intro j'
        rw [hv.2.2.2.2 j' xs hxs]
        rw [xor_eq_b2z, b2z_decide_eq]
        rw [hm.2.2.2.2 j' xs hxs, b2z_decide_eq]
        have hu_st : ∀ q : Fin s, b2z ((evalGates st.1 xs).getD (uWires q) false) = b.repr uVal q := fun q => by
          rw [evalGates_extends_getD hst_ext xs (by rw [hxs]; exact hu q)]
          exact huVal q
        simp_rw [hacc, hu_st]
        rw [hrem accVal uVal j']
        rw [evalGates_extends_getD (extends_trans hst_ext hm.1) xs (by rw [hxs]; exact hxPad ⟨r, hrd⟩ j')]
        rw [hxVal ⟨r, hrd⟩ j', map_add, Finsupp.coe_add, Pi.add_apply]
      rw [ih'.2.2.2.2 xs hxs uVal (accVal * uVal + xVal ⟨r, hrd⟩) xVal huVal h_r2 hxVal j]
      congr 1
      rw [Finset.sum_range_succ]
      split_ifs
      ring

lemma testBit_inj_of_lt {x y b : ℕ} (hx : x < 2 ^ b) (hy : y < 2 ^ b)
    (h : ∀ q : Fin b, x.testBit q.val = y.testBit q.val) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < b
  · exact h ⟨i, hi⟩
  · have h2 : 2 ^ b ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx h2), Nat.testBit_lt_two_pow (lt_of_lt_of_le hy h2)]

def addDecoder (s m b : ℕ) (wBits : Fin m → Fin s → Bool) (n : ℕ)
    (gs : List Gate) (z : ℕ) (yWires : Fin b → ℕ) : List Gate × (Fin s → ℕ) :=
  let notY := buildVecAux (fun gs' q =>
    if hq : q < b then addNot n gs' (yWires ⟨q, hq⟩) else (gs', 0)) b gs
  let ind := buildVecAux (fun gs' i =>
    let ws := (List.finRange b).map (fun q => if i.testBit q.val then yWires q else notY.2 q.val)
    addAndList n gs' z ws) m notY.1
  let out := buildVecAux (fun gs' c =>
    if hc : c < s then
      let ws := ((List.finRange m).filter (fun i => wBits i ⟨c, hc⟩)).map (fun i => ind.2 i.val)
      addOrList n gs' z ws
    else (gs', 0)) s ind.1
  (out.1, fun c => out.2 c.val)

lemma addDecoder_spec {s m b n : ℕ} (hb : 0 < b) (hm2b : m ≤ 2 ^ b)
    (wBits : Fin m → Fin s → Bool) {gs : List Gate} {z : ℕ} {yWires : Fin b → ℕ}
    (hgs : GoodGates n gs) (hz : z < n + gs.length)
    (hz_false : ∀ xs : List Bool, xs.length = n → (evalGates gs xs).getD z false = false)
    (hy : ∀ q : Fin b, yWires q < n + gs.length) :
    let r := addDecoder s m b wBits n gs z yWires
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + (b + m * b + s * m) ∧
      (∀ c : Fin s, r.2 c < n + r.1.length) ∧
      ∀ (xs : List Bool) (i₀ : Fin m), xs.length = n →
        (∀ q : Fin b, (evalGates gs xs).getD (yWires q) false = i₀.val.testBit q.val) →
        ∀ c : Fin s, (evalGates r.1 xs).getD (r.2 c) false = wBits i₀ c := by
  let fnot : List Gate → ℕ → List Gate × ℕ := fun gs' q =>
    if hq : q < b then addNot n gs' (yWires ⟨q, hq⟩) else (gs', 0)
  have hfnot : ∀ (gs' : List Gate) (q : ℕ), q < b → GoodGates n gs' → Extends gs gs' →
      let r := fnot gs' q
      Extends gs' r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs'.length + 1 ∧ r.2 < n + r.1.length := by
    intro gs' q hq hgs' hext
    have hlen := extends_length hext
    dsimp only [fnot]
    split_ifs
    have h1 := addNot_spec hgs' (lt_of_lt_of_le (hy ⟨q, hq⟩) (by omega))
    exact ⟨h1.1, h1.2.1, by omega, h1.2.2.2.1⟩
  have hnot := buildVecAux_spec fnot (fun _ => 1) b gs hgs hfnot
  let notY := buildVecAux fnot b gs
  have hnot_len : gs.length ≤ notY.1.length := extends_length hnot.1
  let find : List Gate → ℕ → List Gate × ℕ := fun gs' i =>
    let ws := (List.finRange b).map (fun q => if i.testBit q.val then yWires q else notY.2 q.val)
    addAndList n gs' z ws
  have hfind : ∀ (gs' : List Gate) (i : ℕ), i < m → GoodGates n gs' → Extends notY.1 gs' →
      let r := find gs' i
      Extends gs' r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs'.length + b ∧ r.2 < n + r.1.length := by
    intro gs' i _ hgs' hext
    have hlen := extends_length hext
    dsimp only [find]
    have hws : ∀ w ∈ (List.finRange b).map (fun q => if i.testBit q.val then yWires q else notY.2 q.val),
        w < n + gs'.length := by
      intro w hw
      simp only [List.mem_map, List.mem_finRange, true_and] at hw
      rcases hw with ⟨q, rfl⟩
      split_ifs
      · exact lt_of_lt_of_le (hy q) (Nat.add_le_add_left (le_trans hnot_len hlen) n)
      · have hnq : notY.2 q.val < n + notY.1.length := hnot.2.2.2.1 q.val q.isLt
        exact lt_of_lt_of_le hnq (Nat.add_le_add_left hlen n)
    have h2 := addAndList_spec hgs' (lt_of_lt_of_le hz (Nat.add_le_add_left (le_trans hnot_len hlen) n)) hws
    have hlen_ws : ((List.finRange b).map (fun q => if i.testBit q.val then yWires q else notY.2 q.val)).length = b := by
      simp
    exact ⟨h2.1, h2.2.1, by omega, h2.2.2.2.1⟩
  have hind := buildVecAux_spec find (fun _ => b) m notY.1 hnot.2.1 hfind
  let ind := buildVecAux find m notY.1
  have hind_len : notY.1.length ≤ ind.1.length := extends_length hind.1
  let fout : List Gate → ℕ → List Gate × ℕ := fun gs' c =>
    if hc : c < s then
      let ws := ((List.finRange m).filter (fun i => wBits i ⟨c, hc⟩)).map (fun i => ind.2 i.val)
      addOrList n gs' z ws
    else (gs', 0)
  have hfout : ∀ (gs' : List Gate) (c : ℕ), c < s → GoodGates n gs' → Extends ind.1 gs' →
      let r := fout gs' c
      Extends gs' r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs'.length + m ∧ r.2 < n + r.1.length := by
    intro gs' c hc hgs' hext
    have hlen := extends_length hext
    dsimp only [fout]
    split_ifs
    have hws : ∀ w ∈ ((List.finRange m).filter (fun i => wBits i ⟨c, hc⟩)).map (fun i => ind.2 i.val),
        w < n + gs'.length := by
      intro w hw
      simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
      rcases hw with ⟨i, _, rfl⟩
      have hiq : ind.2 i.val < n + ind.1.length := hind.2.2.2.1 i.val i.isLt
      exact lt_of_lt_of_le hiq (Nat.add_le_add_left hlen n)
    have h2 := addOrList_spec hgs'
      (lt_of_lt_of_le hz (Nat.add_le_add_left (le_trans hnot_len (le_trans hind_len hlen)) n)) hws
    have hlen_ws : (((List.finRange m).filter (fun i => wBits i ⟨c, hc⟩)).map (fun i => ind.2 i.val)).length ≤ m := by
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    exact ⟨h2.1, h2.2.1, by omega, h2.2.2.2.1⟩
  have hout := buildVecAux_spec fout (fun _ => m) s ind.1 hind.2.1 hfout
  refine ⟨extends_trans hnot.1 (extends_trans hind.1 hout.1), hout.2.1, ?_, fun c => hout.2.2.2.1 c.val c.isLt, ?_⟩
  · have h1 := hnot.2.2.1
    have h2 := hind.2.2.1
    have h3 := hout.2.2.1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h1 h2 h3
    have h1' : notY.1.length ≤ gs.length + b := by
      change notY.1.length ≤ gs.length + b * 1 at h1
      omega
    have h2' : ind.1.length ≤ notY.1.length + m * b := h2
    have h3' : (buildVecAux fout s ind.1).1.length ≤ ind.1.length + s * m := h3
    change (buildVecAux fout s ind.1).1.length ≤ gs.length + (b + m * b + s * m)
    omega
  · intro xs i₀ hxs hy_bits c
    change (evalGates (buildVecAux fout s ind.1).1 xs).getD ((buildVecAux fout s ind.1).2 c.val) false = _
    rw [hout.2.2.2.2 c.val c.isLt xs hxs]
    dsimp only [fout]
    split_ifs with hc
    · have hsub := buildVecAux_spec fout (fun _ => m) c.val ind.1 hind.2.1
        (fun gs' i hi => hfout gs' i (lt_trans hi c.isLt))
      have hsub_len := extends_length hsub.1
      set gs' := (buildVecAux fout c.val ind.1).1
      set ws := ((List.finRange m).filter (fun i => wBits i c)).map (fun i => ind.2 i.val)
      have hws_lt : ∀ w ∈ ws, w < n + gs'.length := by
        intro w hw
        simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
        rcases hw with ⟨i, _, rfl⟩
        have hiq : ind.2 i.val < n + ind.1.length := hind.2.2.2.1 i.val i.isLt
        omega
      have hor := addOrList_spec hsub.2.1
        (lt_of_lt_of_le hz (Nat.add_le_add_left (le_trans hnot_len (le_trans hind_len hsub_len)) n)) hws_lt
      rw [hor.2.2.2.2 xs hxs]
      have hind_val : ∀ i : Fin m,
          (evalGates gs' xs).getD (ind.2 i.val) false = decide (i = i₀) := by
        intro i
        rw [evalGates_extends_getD hsub.1 xs (by rw [hxs]; exact hind.2.2.2.1 i.val i.isLt)]
        change (evalGates (buildVecAux find m notY.1).1 xs).getD
          ((buildVecAux find m notY.1).2 i.val) false = _
        rw [hind.2.2.2.2 i.val i.isLt xs hxs]
        dsimp only [find]
        have hsub_i := buildVecAux_spec find (fun _ => b) i.val notY.1 hnot.2.1
          (fun gs0 j hj => hfind gs0 j (lt_trans hj i.isLt))
        have hsub_i_len := extends_length hsub_i.1
        set gs0 := (buildVecAux find i.val notY.1).1
        have hws_i : ∀ w ∈ (List.finRange b).map (fun q => if i.val.testBit q.val then yWires q else notY.2 q.val),
            w < n + gs0.length := by
          intro w hw
          simp only [List.mem_map, List.mem_finRange, true_and] at hw
          rcases hw with ⟨q, rfl⟩
          split_ifs
          · exact lt_of_lt_of_le (hy q) (Nat.add_le_add_left (le_trans hnot_len hsub_i_len) n)
          · have hnq : notY.2 q.val < n + notY.1.length := hnot.2.2.2.1 q.val q.isLt
            exact lt_of_lt_of_le hnq (Nat.add_le_add_left hsub_i_len n)
        have hand := addAndList_spec hsub_i.2.1
          (lt_of_lt_of_le hz (Nat.add_le_add_left (le_trans hnot_len hsub_i_len) n)) hws_i
        rw [hand.2.2.2.2 xs hxs]
        have hne : ((List.finRange b).map (fun q => if i.val.testBit q.val then yWires q else notY.2 q.val)) ≠ [] := by
          intro h
          have := congr_arg List.length h
          simp at this
          omega
        by_cases hne' : ((List.finRange b).map (fun q => if i.val.testBit q.val then yWires q else notY.2 q.val)) = []
        · exact absurd hne' hne
        · simp only [hne', ite_false]
          rw [Bool.eq_iff_iff]
          simp only [List.all_eq_true, List.mem_map, List.mem_finRange, true_and, decide_eq_true_eq]
          constructor
          · intro hall
            apply Fin.ext
            apply testBit_inj_of_lt (lt_of_lt_of_le i.isLt hm2b) (lt_of_lt_of_le i₀.isLt hm2b)
            intro q
            have hq := hall (if i.val.testBit q.val then yWires q else notY.2 q.val) ⟨q, rfl⟩
            by_cases hbit : i.val.testBit q.val
            · simp only [hbit, ite_true] at hq
              rw [evalGates_extends_getD (extends_trans hnot.1 hsub_i.1) xs (by rw [hxs]; exact hy q)] at hq
              rw [hy_bits q] at hq
              rw [hbit, hq]
            · have hbit_f : i.val.testBit q.val = false := Bool.eq_false_iff.mpr hbit
              simp only [hbit_f, Bool.false_eq_true, ite_false] at hq
              rw [evalGates_extends_getD hsub_i.1 xs (by rw [hxs]; exact hnot.2.2.2.1 q.val q.isLt)] at hq
              change (evalGates (buildVecAux fnot b gs).1 xs).getD
                ((buildVecAux fnot b gs).2 q.val) false = true at hq
              rw [hnot.2.2.2.2 q.val q.isLt xs hxs] at hq
              dsimp only [fnot] at hq
              split_ifs at hq
              · have hsub_n := buildVecAux_spec fnot (fun _ => 1) q.val gs hgs
                  (fun gs1 r hr => hfnot gs1 r (lt_trans hr q.isLt))
                have hn_len := extends_length hsub_n.1
                have hn1 := addNot_spec hsub_n.2.1 (lt_of_lt_of_le (hy q) (Nat.add_le_add_left hn_len n))
                rw [hn1.2.2.2.2 xs hxs] at hq
                rw [evalGates_extends_getD hsub_n.1 xs (by rw [hxs]; exact hy q)] at hq
                rw [hy_bits q] at hq
                have h0_f : i₀.val.testBit q.val = false := by revert hq; cases i₀.val.testBit q.val <;> simp
                rw [hbit_f, h0_f]
              · exact absurd q.isLt (by assumption)
          · rintro rfl w ⟨q, rfl⟩
            by_cases hbit : i.val.testBit q.val
            · simp only [hbit, ite_true]
              rw [evalGates_extends_getD (extends_trans hnot.1 hsub_i.1) xs (by rw [hxs]; exact hy q)]
              rw [hy_bits q, hbit]
            · have hbit_f : i.val.testBit q.val = false := Bool.eq_false_iff.mpr hbit
              simp only [hbit_f, Bool.false_eq_true, ite_false]
              rw [evalGates_extends_getD hsub_i.1 xs (by rw [hxs]; exact hnot.2.2.2.1 q.val q.isLt)]
              change (evalGates (buildVecAux fnot b gs).1 xs).getD
                ((buildVecAux fnot b gs).2 q.val) false = true
              rw [hnot.2.2.2.2 q.val q.isLt xs hxs]
              dsimp only [fnot]
              split_ifs
              · have hsub_n := buildVecAux_spec fnot (fun _ => 1) q.val gs hgs
                  (fun gs1 r hr => hfnot gs1 r (lt_trans hr q.isLt))
                have hn_len := extends_length hsub_n.1
                have hn1 := addNot_spec hsub_n.2.1 (lt_of_lt_of_le (hy q) (Nat.add_le_add_left hn_len n))
                rw [hn1.2.2.2.2 xs hxs]
                rw [evalGates_extends_getD hsub_n.1 xs (by rw [hxs]; exact hy q)]
                rw [hy_bits q]
                simp [hbit_f]
              · exact absurd q.isLt (by assumption)
      by_cases hw_empty : ws = []
      · simp only [hw_empty, ite_true]
        rw [evalGates_extends_getD (extends_trans hnot.1 (extends_trans hind.1 hsub.1)) xs (by rw [hxs]; exact hz)]
        rw [hz_false xs hxs]
        by_contra htrue
        have h1 : wBits i₀ c = true := Bool.eq_true_of_not_eq_false (fun hf => htrue (by simp [hf]))
        have hmem : ind.2 i₀.val ∈ ws := by
          simp only [ws, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
          exact ⟨i₀, h1, rfl⟩
        rw [hw_empty] at hmem
        simp at hmem
      · simp only [hw_empty, ite_false]
        rw [Bool.eq_iff_iff]
        simp only [ws, List.any_eq_true, List.mem_map, List.mem_filter, List.mem_finRange, true_and]
        constructor
        · rintro ⟨w, ⟨i, hi, rfl⟩, hval⟩
          rw [hind_val i] at hval
          have : i = i₀ := of_decide_eq_true hval
          subst this
          exact hi
        · intro h1
          refine ⟨ind.2 i₀.val, ⟨i₀, h1, rfl⟩, ?_⟩
          rw [hind_val i₀]
          simp
    · exact absurd c.isLt hc

lemma ker_card_of_surjective_gen {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [DecidableEq V] {s : ℕ} (hs : 3 ≤ s) (hcard : Fintype.card V = 2 ^ s)
    (A : V →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (hA : Function.Surjective A) (z : Fin 3 → ZMod 2) :
    (Finset.univ.filter (fun v : V => A v = z)).card = 2 ^ (s - 3) := by
  obtain ⟨v₀, hv₀⟩ := hA z
  let e : {v : V // A v = z} ≃ LinearMap.ker A :=
    { toFun := fun v => ⟨v.1 - v₀, by simp [LinearMap.mem_ker, v.2, hv₀]⟩
      invFun := fun v => ⟨v.1 + v₀, by simp [LinearMap.mem_ker.mp v.2, hv₀]⟩
      left_inv := fun v => by ext; simp
      right_inv := fun v => by ext; simp }
  have h1 : (Finset.univ.filter (fun v : V => A v = z)).card = Fintype.card {v : V // A v = z} := by
    rw [Fintype.card_subtype]
  rw [h1, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  have hq : Nat.card (V ⧸ LinearMap.ker A) = 8 := by
    rw [Nat.card_congr (A.quotKerEquivOfSurjective hA).toEquiv, Nat.card_eq_fintype_card]
    decide
  have hmul := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker A)
  rw [hq, Nat.card_eq_fintype_card, hcard] at hmul
  have h2s : 2 ^ s = 8 * 2 ^ (s - 3) := by
    have : 2 ^ 3 = 8 := by norm_num
    rw [← this, ← pow_add]
    congr 1
    omega
  omega

lemma small_case (k : ℕ) (hk4 : 4 ≤ k) (hk17 : k ≤ 17) :
    let F := ZMod 2
    let V := Fin k → F
    ∃ (M t : ℕ) (mask : Fin M ↪ V) (address : Fin M ↪ (Fin t → Bool))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      0 < M ∧ M ≤ 8960 * k ∧ 2 ^ t ≤ 2 * M ∧
      (∀ (A : V →ₗ[F] (Fin 3 → F)), Function.Surjective A → ∀ z : Fin 3 → F,
        M ≤ 128 * ((Finset.univ : Finset (Fin M)).filter (fun j => A (mask j) = z)).card) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + t) C ∧
      C.output < k + t + C.size ∧ C.size ≤ 4000 * k * (Nat.log2 k + 1) ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      ∀ (x : Fin k → Bool) (j : Fin M),
        C.eval (List.ofFn x ++ List.ofFn (address j)) =
          decide ((∑ i : Fin k, (if x i then (1 : F) else 0) * mask j i) = 1) := by
  let M := 2 ^ k
  let t := k
  let maskFn : Fin M → (Fin k → ZMod 2) := fun j i => if j.val.testBit i.val then 1 else 0
  have hmask_inj : Function.Injective maskFn := by
    intro j₁ j₂ h
    apply Fin.ext
    apply testBit_inj_of_lt j₁.isLt j₂.isLt
    intro i
    have hi := congr_fun h i
    dsimp only [maskFn] at hi
    cases hj1 : j₁.val.testBit i.val <;> cases hj2 : j₂.val.testBit i.val
    · rfl
    · simp [hj1, hj2] at hi
    · simp [hj1, hj2] at hi
    · rfl
  let mask : Fin M ↪ (Fin k → ZMod 2) := ⟨maskFn, hmask_inj⟩
  let addrFn : Fin M → (Fin t → Bool) := fun j i => j.val.testBit i.val
  have haddr_inj : Function.Injective addrFn := by
    intro j₁ j₂ h
    apply Fin.ext
    apply testBit_inj_of_lt j₁.isLt j₂.isLt
    intro i
    exact congr_fun h i
  let address : Fin M ↪ (Fin t → Bool) := ⟨addrFn, haddr_inj⟩
  let n := k + t
  have hn : 0 < n := by omega
  let r0 := addZero n []
  have hr0 := addZero_spec hn (goodGates_nil n)
  let f : List Gate → ℕ → List Gate × ℕ := fun gs' i =>
    if _ : i < k then addAnd n gs' i (k + i) else (gs', 0)
  have hf : ∀ (gs' : List Gate) (i : ℕ), i < k → GoodGates n gs' → Extends r0.1 gs' →
      let r := f gs' i
      Extends gs' r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs'.length + 1 ∧ r.2 < n + r.1.length := by
    intro gs' i hi hgs' hext
    have hlen := extends_length hext
    dsimp only [f]
    split_ifs
    have ha := addAnd_spec hgs' (by omega : i < n + gs'.length) (by omega : k + i < n + gs'.length)
    exact ⟨ha.1, ha.2.1, by omega, ha.2.2.2.1⟩
  let ands := buildVecAux f k r0.1
  have hands := buildVecAux_spec f (fun _ => 1) k r0.1 hr0.2.1 hf
  have hands_len : r0.1.length ≤ ands.1.length := extends_length hands.1
  let ws := (List.finRange k).map (fun i => ands.2 i.val)
  have hws : ∀ w ∈ ws, w < n + ands.1.length := by
    intro w hw
    simp only [ws, List.mem_map, List.mem_finRange, true_and] at hw
    rcases hw with ⟨i, rfl⟩
    exact hands.2.2.2.1 i.val i.isLt
  let out := addXorList n ands.1 r0.2 ws
  have hzr : r0.2 < n + r0.1.length := hr0.2.2.2.1
  have hout := addXorList_spec hands.2.1 (lt_of_lt_of_le hzr (Nat.add_le_add_left hands_len n)) hws (fun xs hxs => by
    rw [evalGates_extends_getD hands.1 xs (by rw [hxs]; exact hzr)]
    exact hr0.2.2.2.2 xs hxs)
  let C : Circuit := ⟨out.1, out.2⟩
  refine ⟨M, t, mask, address, C, Nat.pow_pos (by norm_num), ?_, ?_, ?_, hout.2.1.1, hout.2.2.2.1, ?_, ?_, ?_⟩
  · dsimp only [M]
    interval_cases k <;> norm_num
  · dsimp only [M, t]
    omega
  · intro A hA z
    have hbij : Function.Bijective maskFn := by
      refine (Fintype.bijective_iff_injective_and_card maskFn).mpr ⟨hmask_inj, ?_⟩
      simp [M]
    let e := Equiv.ofBijective maskFn hbij
    have hfilt : (Finset.univ.filter (fun j : Fin M => A (mask j) = z)).card =
        (Finset.univ.filter (fun v : Fin k → ZMod 2 => A v = z)).card := by
      refine Finset.card_bij (fun j _ => mask j) ?_ ?_ ?_
      · intro j hj
        simpa using (Finset.mem_filter.mp hj).2
      · intro j₁ _ j₂ _ h
        exact mask.injective h
      · intro v hv
        refine ⟨e.symm v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · change A (maskFn (e.symm v)) = z
          have he : maskFn (e.symm v) = v := e.apply_symm_apply v
          rw [he]
          exact (Finset.mem_filter.mp hv).2
        · exact e.apply_symm_apply v
    rw [hfilt]
    have hcardV : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by simp [ZMod.card]
    rw [ker_card_of_surjective_gen (by omega) hcardV A hA z]
    have h2k : M = 8 * 2 ^ (k - 3) := by
      dsimp only [M]
      have : 8 = 2 ^ 3 := by norm_num
      rw [this, ← pow_add]
      congr 1
      omega
    omega
  · dsimp only [C, Circuit.size]
    have h1 : r0.1.length = 2 := hr0.2.2.1
    have h2 := hands.2.2.1
    have h3 := hout.2.2.1
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    have hws_len : ws.length = k := by simp [ws]
    have h2' : ands.1.length ≤ r0.1.length + k * 1 := h2
    have h3' : out.1.length ≤ ands.1.length + 4 * ws.length := h3
    have hsz : out.1.length ≤ 5 * k + 2 := by omega
    have hlog : 1 ≤ Nat.log2 k + 1 := by omega
    nlinarith
  · intro g hg
    exact hout.2.1.2 g hg
  · intro x j
    change (evalGates out.1 (List.ofFn x ++ List.ofFn (address j))).getD out.2 false = _
    have hxs_len : (List.ofFn x ++ List.ofFn (address j)).length = n := by
      simp [n, t]
    rw [hout.2.2.2.2 _ hxs_len]
    congr 1
    apply congr_arg (· = 1)
    dsimp only [ws]
    rw [List.map_map, list_sum_map_finRange]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Function.comp_apply]
    change b2z ((evalGates (buildVecAux f k r0.1).1 (List.ofFn x ++ List.ofFn (address j))).getD
      ((buildVecAux f k r0.1).2 i.val) false) = _
    rw [hands.2.2.2.2 i.val i.isLt _ hxs_len]
    simp only [f, i.isLt, ↓reduceDIte]
    have hsub := buildVecAux_spec f (fun _ => 1) i.val r0.1 hr0.2.1 (fun gs' r hr => hf gs' r (lt_trans hr i.isLt))
    have hsub_len := extends_length hsub.1
    have ha := addAnd_spec hsub.2.1 (by omega : i.val < n + (buildVecAux f i.val r0.1).1.length)
      (by omega : k + i.val < n + (buildVecAux f i.val r0.1).1.length)
    rw [ha.2.2.2.2 _ hxs_len]
    have hxi : (evalGates (buildVecAux f i.val r0.1).1 (List.ofFn x ++ List.ofFn (address j))).getD i.val false = x i := by
      rw [evalGates_extends_getD (extends_trans hr0.1 hsub.1) _ (by rw [hxs_len]; omega)]
      rw [evalGates_getD_lt _ _ (by rw [hxs_len]; omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]
    have hyi : (evalGates (buildVecAux f i.val r0.1).1 (List.ofFn x ++ List.ofFn (address j))).getD (k + i.val) false =
        address j ⟨i.val, i.isLt⟩ := by
      rw [evalGates_extends_getD (extends_trans hr0.1 hsub.1) _ (by rw [hxs_len]; omega)]
      rw [evalGates_getD_lt _ _ (by rw [hxs_len]; omega)]
      simp [List.getD_eq_getElem?_getD, t]
    rw [hxi, hyi]
    cases x i <;> cases htb : j.val.testBit i.val <;> simp [htb, b2z, mask, maskFn, address, addrFn]

lemma exists_powerBasis (s : ℕ) (hs : s ≠ 0) :
    ∃ (α : GaloisField 2 s) (b : Module.Basis (Fin s) (ZMod 2) (GaloisField 2 s)),
      ∀ j : Fin s, b j = α ^ j.val := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod 2) (GaloisField 2 s)
  let pb0 := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := ZMod 2) α)
  let e : IntermediateField.adjoin (ZMod 2) ({α} : Set (GaloisField 2 s)) ≃ₐ[ZMod 2] GaloisField 2 s :=
    (IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv
  let pb := pb0.map e
  have hdim : pb.dim = s := by
    rw [← pb.finrank, GaloisField.finrank 2 hs]
  let b := pb.basis.reindex (finCongr hdim)
  refine ⟨α, b, fun j => ?_⟩
  have hgen : pb.gen = α := by
    dsimp only [pb, pb0, e]
    simp
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow, hgen]
  simp

lemma trace_nondeg (s : ℕ) {a : GaloisField 2 s} (ha : a ≠ 0) :
    ∃ y : GaloisField 2 s, Algebra.trace (ZMod 2) (GaloisField 2 s) (a * y) ≠ 0 := by
  have htr := (traceForm_nondegenerate (ZMod 2) (GaloisField 2 s)).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra h
  push Not at h
  exact ha (htr h)

noncomputable def toBitsEquiv (s : ℕ) (hs : s ≠ 0)
    (b : Module.Basis (Fin s) (ZMod 2) (GaloisField 2 s)) :
    GaloisField 2 s ≃ₗ[ZMod 2] (Fin s → ZMod 2) := by
  letI : Fintype (GaloisField 2 s) := Fintype.ofFinite (GaloisField 2 s)
  let f : GaloisField 2 s →ₗ[ZMod 2] (Fin s → ZMod 2) :=
    { toFun := fun v j => Algebra.trace (ZMod 2) (GaloisField 2 s) (b j * v)
      map_add' := fun v₁ v₂ => by ext j; simp [mul_add]
      map_smul' := fun r v => by
        ext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Algebra.mul_smul_comm, map_smul] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    obtain ⟨y, hy⟩ := trace_nondeg s hv0
    have hy_sum : y = ∑ j : Fin s, b.repr y j • b j := (b.sum_repr y).symm
    have hmul : y * v = ∑ j : Fin s, b.repr y j • (b j * v) := by
      conv_lhs => rw [hy_sum]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_mul_assoc]
    have htr0 : Algebra.trace (ZMod 2) (GaloisField 2 s) (y * v) = 0 := by
      rw [hmul, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      have hj0 : Algebra.trace (ZMod 2) (GaloisField 2 s) (b j * v) = 0 := congr_fun hv j
      rw [hj0, mul_zero]
    rw [mul_comm] at htr0
    exact hy htr0
  have hbij : Function.Bijective f := by
    refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩
    have hk : Fintype.card (GaloisField 2 s) = 2 ^ s := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 s hs]
    rw [hk]
    simp [ZMod.card]
  exact LinearEquiv.ofBijective f hbij

lemma exists_dual_trace (s : ℕ) (hs : s ≠ 0)
    (b : Module.Basis (Fin s) (ZMod 2) (GaloisField 2 s))
    (ℓ : GaloisField 2 s →ₗ[ZMod 2] ZMod 2) :
    ∃ α : GaloisField 2 s, ∀ v : GaloisField 2 s,
      ℓ v = Algebra.trace (ZMod 2) (GaloisField 2 s) (α * v) := by
  let _ : Fintype (GaloisField 2 s) := Fintype.ofFinite (GaloisField 2 s)
  let f : GaloisField 2 s →ₗ[ZMod 2] (Fin s → ZMod 2) :=
    { toFun := fun α j => Algebra.trace (ZMod 2) (GaloisField 2 s) (α * b j)
      map_add' := fun a₁ a₂ => by ext j; simp [add_mul]
      map_smul' := fun r a => by
        ext j
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_mul_assoc, map_smul] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro α hα
    by_contra hα0
    obtain ⟨y, hy⟩ := trace_nondeg s hα0
    have hy_sum : y = ∑ j : Fin s, b.repr y j • b j := (b.sum_repr y).symm
    have hmul : α * y = ∑ j : Fin s, b.repr y j • (α * b j) := by
      conv_lhs => rw [hy_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.mul_smul_comm]
    have htr0 : Algebra.trace (ZMod 2) (GaloisField 2 s) (α * y) = 0 := by
      rw [hmul, map_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      have hj0 : Algebra.trace (ZMod 2) (GaloisField 2 s) (α * b j) = 0 := congr_fun hα j
      rw [hj0, mul_zero]
    exact hy htr0
  have hsurj : Function.Surjective f := by
    refine ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩).2
    have hk : Fintype.card (GaloisField 2 s) = 2 ^ s := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 s hs]
    rw [hk]
    simp [ZMod.card]
  obtain ⟨α, hα⟩ := hsurj (fun j => ℓ (b j))
  refine ⟨α, fun v => ?_⟩
  have hv_sum : v = ∑ j : Fin s, b.repr v j • b j := (b.sum_repr v).symm
  calc ℓ v
      = ℓ (∑ j : Fin s, b.repr v j • b j) := by conv_lhs => rw [hv_sum]
    _ = ∑ j : Fin s, b.repr v j * ℓ (b j) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul]
    _ = ∑ j : Fin s, b.repr v j * Algebra.trace (ZMod 2) (GaloisField 2 s) (α * b j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj' : f α j = Algebra.trace (ZMod 2) (GaloisField 2 s) (α * b j) := rfl
        rw [← hj', congr_fun hα j]
    _ = Algebra.trace (ZMod 2) (GaloisField 2 s) (α * ∑ j : Fin s, b.repr v j • b j) := by
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Algebra.mul_smul_comm, map_smul, smul_eq_mul]
    _ = Algebra.trace (ZMod 2) (GaloisField 2 s) (α * v) := by rw [← hv_sum]

lemma exists_lam_of_proper (S : Submodule (ZMod 2) (Fin 3 → ZMod 2)) (hS : S ≠ ⊤) :
    ∃ lam : Fin 3 → ZMod 2, lam ≠ 0 ∧ ∀ y ∈ S, (∑ c : Fin 3, lam c * y c) = 0 := by
  have hlt : Module.finrank (ZMod 2) S < 3 := by
    have hle : Module.finrank (ZMod 2) S ≤ 3 := by
      simpa using Submodule.finrank_le (R := ZMod 2) S
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hS
    apply Submodule.eq_top_of_finrank_eq
    simpa using heq
  have : FiniteDimensional (ZMod 2) S := Module.Finite.of_injective S.subtype Subtype.val_injective
  let b := Module.finBasis (ZMod 2) S
  let evalF : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin (Module.finrank (ZMod 2) S) → ZMod 2) :=
    { toFun := fun lam i => ∑ c : Fin 3, lam c * (b i).1 c
      map_add' := fun l₁ l₂ => by ext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r l => by ext i; simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker evalF ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective evalF := LinearMap.ker_eq_bot.mp hbot
    have hcard := Fintype.card_le_of_injective evalF hinj
    have h1 : Fintype.card (Fin 3 → ZMod 2) = 8 := by decide
    have h2 : Fintype.card (Fin (Module.finrank (ZMod 2) S) → ZMod 2) =
        2 ^ Module.finrank (ZMod 2) S := by
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [h1, h2] at hcard
    have : 2 ^ Module.finrank (ZMod 2) S < 8 := Nat.pow_lt_pow_right (by norm_num) hlt
    omega
  obtain ⟨lam, hlam, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨lam, hne, fun y hy => ?_⟩
  have hker_eval : ∀ i, (∑ c : Fin 3, lam c * (b i).1 c) = 0 :=
    congr_fun (LinearMap.mem_ker.mp hlam)
  have hy_rep : (⟨y, hy⟩ : S) = ∑ i, b.repr ⟨y, hy⟩ i • b i := (b.sum_repr ⟨y, hy⟩).symm
  have hy_val : y = ∑ i, b.repr ⟨y, hy⟩ i • (b i).1 := by
    have h := congr_arg Subtype.val hy_rep
    change y = (∑ i, b.repr ⟨y, hy⟩ i • b i : S).1 at h
    simpa only [Submodule.coe_sum, SetLike.val_smul] using h
  rw [hy_val]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ c : Fin 3, lam c * ∑ i, b.repr ⟨y, hy⟩ i * (b i).1 c
      = ∑ i, b.repr ⟨y, hy⟩ i * ∑ c : Fin 3, lam c * (b i).1 c := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = 0 := by simp [hker_eval]

def tuples {α : Type*} [DecidableEq α] (U : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | i + 1 => (tuples U i).biUnion (fun l => (U.filter (fun x => x ∉ l)).image (fun x => x :: l))

lemma tuples_mem {α : Type*} [DecidableEq α] {U : Finset α} {i : ℕ} {l : List α}
    (hl : l ∈ tuples U i) : l.length = i ∧ l.Nodup ∧ ∀ x ∈ l, x ∈ U := by
  induction i generalizing l with
  | zero =>
    simp only [tuples, Finset.mem_singleton] at hl
    subst hl
    simp
  | succ i ih =>
    simp only [tuples, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hl
    rcases hl with ⟨l', hl', x, ⟨hxU, hxl⟩, rfl⟩
    have ih' := ih hl'
    refine ⟨by simp [ih'.1], List.nodup_cons.mpr ⟨hxl, ih'.2.1⟩, fun y hy => ?_⟩
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hxU
    · exact ih'.2.2 y hy

lemma tuples_disjoint {α : Type*} [DecidableEq α] (U : Finset α) (i : ℕ) :
    (tuples U i : Set (List α)).PairwiseDisjoint
      (fun l => (U.filter (fun x => x ∉ l)).image (fun x => x :: l)) := by
  intro l₁ _ l₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro y hy₁ hy₂
  simp only [Finset.mem_image, Finset.mem_filter] at hy₁ hy₂
  rcases hy₁ with ⟨x₁, _, rfl⟩
  rcases hy₂ with ⟨x₂, _, heq⟩
  exact hne (List.cons.inj heq).2.symm

lemma tuples_card_succ {α : Type*} [DecidableEq α] (U : Finset α) (i : ℕ) (_hi : i ≤ U.card) :
    (tuples U (i + 1)).card = (U.card - i) * (tuples U i).card := by
  rw [tuples, Finset.card_biUnion (tuples_disjoint U i)]
  have hcard : ∀ l ∈ tuples U i, ((U.filter (fun x => x ∉ l)).image (fun x => x :: l)).card = U.card - i := by
    intro l hl
    rw [Finset.card_image_of_injective _ (fun x₁ x₂ h => (List.cons.inj h).1)]
    have hm := tuples_mem hl
    have hfilt : U.filter (fun x => x ∉ l) = U \ l.toFinset := by
      ext x; simp
    have hsub : l.toFinset ⊆ U := by
      intro x hx
      exact hm.2.2 x (List.mem_toFinset.mp hx)
    rw [hfilt, Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup hm.2.1, hm.1]
  rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul, mul_comm]

lemma tuples_card_pos {α : Type*} [DecidableEq α] (U : Finset α) (i : ℕ) (hi : i ≤ U.card) :
    0 < (tuples U i).card := by
  induction i with
  | zero => simp [tuples]
  | succ i ih =>
    rw [tuples_card_succ U i (Nat.le_of_succ_le hi)]
    exact Nat.mul_pos (Nat.sub_pos_of_lt hi) (ih (Nat.le_of_succ_le hi))

def hits {α : Type*} [DecidableEq α] (S : Finset α) (l : List α) : ℕ :=
  l.countP (fun x => decide (x ∈ S))

noncomputable def wt {α : Type*} [DecidableEq α] (S : Finset α) (s : ℕ) (l : List α) : ℚ :=
  if s ≤ hits S l then 0 else (1 / 8 : ℚ) ^ hits S l

lemma wt_nonneg {α : Type*} [DecidableEq α] (S : Finset α) (s : ℕ) (l : List α) :
    0 ≤ wt S s l := by
  dsimp only [wt]
  split_ifs
  · exact le_refl 0
  · positivity

lemma toFinset_filter_card_le_countP {α : Type*} [DecidableEq α] (S : Finset α) (l : List α) :
    (l.toFinset ∩ S).card ≤ hits S l := by
  induction l with
  | nil => simp [hits]
  | cons x xs ih =>
    simp only [hits, List.toFinset_cons, List.countP_cons]
    by_cases hx : x ∈ S
    · have hsub : insert x xs.toFinset ∩ S ⊆ insert x (xs.toFinset ∩ S) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_insert] at hy ⊢
        rcases hy with ⟨rfl | hy1, hy2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hy1, hy2⟩
      have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
      simp only [hx, decide_true, ↓reduceIte]
      dsimp only [hits] at ih
      omega
    · have heq : insert x xs.toFinset ∩ S = xs.toFinset ∩ S := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨rfl | h1, h2⟩
          · exact absurd h2 hx
          · exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr h1, h2⟩
      rw [heq]
      simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih

lemma wt_step {α : Type*} [DecidableEq α] {U S : Finset α} {s i : ℕ}
    (hsU : S ⊆ U) (hi : i < U.card) (hs_ge : U.card ≤ 10 * (S.card - (s - 1))) :
    ∑ l ∈ tuples U (i + 1), wt S s l ≤
      (73 / 80 : ℚ) * (U.card - i : ℚ) * ∑ l ∈ tuples U i, wt S s l := by
  rw [tuples, Finset.sum_biUnion (tuples_disjoint U i)]
  have hinner : ∀ l ∈ tuples U i,
      ∑ y ∈ (U.filter (fun x => x ∉ l)).image (fun x => x :: l), wt S s y ≤
        (73 / 80 : ℚ) * (U.card - i : ℚ) * wt S s l := by
    intro l hl
    rw [Finset.sum_image (fun x₁ _ x₂ _ h => (List.cons.inj h).1)]
    set U' := U.filter (fun x => x ∉ l)
    have hm := tuples_mem hl
    have hU'card : U'.card = U.card - i := by
      have hfilt : U' = U \ l.toFinset := by ext x; simp [U']
      have hsub : l.toFinset ⊆ U := fun x hx => hm.2.2 x (List.mem_toFinset.mp hx)
      rw [hfilt, Finset.card_sdiff_of_subset hsub, List.toFinset_card_of_nodup hm.2.1, hm.1]
    by_cases hdone : s ≤ hits S l
    · have h0 : ∀ x ∈ U', wt S s (x :: l) = 0 := by
        intro x _
        have hge : s ≤ hits S (x :: l) := by
          simp only [hits, List.countP_cons]
          dsimp only [hits] at hdone
          by_cases hx : x ∈ S <;> simp [hx] <;> omega
        simp [wt, hge]
      rw [Finset.sum_eq_zero h0]
      simp [wt, hdone]
    · have hlt : hits S l < s := Nat.lt_of_not_le hdone
      have hUS : U' ∩ S = S \ (l.toFinset ∩ S) := by
        ext x
        simp only [U', Finset.mem_inter, Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset]
        constructor
        · rintro ⟨⟨_, hxl⟩, hxS⟩
          exact ⟨hxS, fun h => hxl h.1⟩
        · rintro ⟨hxS, hnl⟩
          exact ⟨⟨hsU hxS, fun hx => hnl ⟨hx, hxS⟩⟩, hxS⟩
      have hS_card : S.card - (s - 1) ≤ (U' ∩ S).card := by
        rw [hUS, Finset.card_sdiff_of_subset Finset.inter_subset_right]
        have hle := toFinset_filter_card_le_countP S l
        omega
      have h10 : U'.card ≤ 10 * (U' ∩ S).card := by
        rw [hU'card]
        exact (Nat.sub_le U.card i).trans (hs_ge.trans (Nat.mul_le_mul_left 10 hS_card))
      rw [← Finset.sum_filter_add_sum_filter_not U' (fun x => x ∈ S)]
      have hS_bound : ∀ x ∈ U'.filter (fun x => x ∈ S), wt S s (x :: l) ≤ (1 / 8 : ℚ) * wt S s l := by
        intro x hx
        have hxS : x ∈ S := (Finset.mem_filter.mp hx).2
        have hhit : hits S (x :: l) = hits S l + 1 := by
          simp [hits, hxS]
        dsimp only [wt]
        simp only [hdone, ite_false, hhit]
        split_ifs
        · positivity
        · rw [pow_succ']
      have hNS_bound : ∀ x ∈ U'.filter (fun x => x ∉ S), wt S s (x :: l) ≤ wt S s l := by
        intro x hx
        have hxS : x ∉ S := (Finset.mem_filter.mp hx).2
        have hhit : hits S (x :: l) = hits S l := by
          simp [hits, hxS]
        simp [wt, hhit, hdone]
      have hsum1 := Finset.sum_le_sum hS_bound
      have hsum2 := Finset.sum_le_sum hNS_bound
      simp only [Finset.sum_const, nsmul_eq_mul] at hsum1 hsum2
      have hpart : (U'.filter (fun x => x ∈ S)).card + (U'.filter (fun x => x ∉ S)).card = U'.card :=
        Finset.card_filter_add_card_filter_not (fun x => x ∈ S)
      have hU'S_eq : U'.filter (fun x => x ∈ S) = U' ∩ S := by
        ext x; simp
      rw [hU'S_eq] at hsum1 hpart
      have h10q : (U'.card : ℚ) ≤ 10 * ((U' ∩ S).card : ℚ) := by exact_mod_cast h10
      have hpartq : ((U' ∩ S).card : ℚ) + ((U'.filter (fun x => x ∉ S)).card : ℚ) = (U'.card : ℚ) := by
        exact_mod_cast hpart
      have hU'q : (U'.card : ℚ) = (U.card : ℚ) - (i : ℚ) := by
        rw [hU'card, Nat.cast_sub (le_of_lt hi)]
      have hwnn : 0 ≤ wt S s l := wt_nonneg S s l
      have hcoef : ((U' ∩ S).card : ℚ) * (1 / 8 : ℚ) + ((U'.filter (fun x => x ∉ S)).card : ℚ) ≤
          (73 / 80 : ℚ) * (U.card - i : ℚ) := by
        linarith
      calc ∑ x ∈ U'.filter (fun x => x ∈ S), wt S s (x :: l) +
            ∑ x ∈ U'.filter (fun x => x ∉ S), wt S s (x :: l)
          ≤ ((U' ∩ S).card : ℚ) * ((1 / 8 : ℚ) * wt S s l) +
            ((U'.filter (fun x => x ∉ S)).card : ℚ) * wt S s l := add_le_add hsum1 hsum2
        _ = (((U' ∩ S).card : ℚ) * (1 / 8 : ℚ) + ((U'.filter (fun x => x ∉ S)).card : ℚ)) * wt S s l := by ring
        _ ≤ ((73 / 80 : ℚ) * (U.card - i : ℚ)) * wt S s l := mul_le_mul_of_nonneg_right hcoef hwnn
  calc ∑ l ∈ tuples U i, ∑ y ∈ (U.filter (fun x => x ∉ l)).image (fun x => x :: l), wt S s y
      ≤ ∑ l ∈ tuples U i, (73 / 80 : ℚ) * (U.card - i : ℚ) * wt S s l := Finset.sum_le_sum hinner
    _ = (73 / 80 : ℚ) * (U.card - i : ℚ) * ∑ l ∈ tuples U i, wt S s l := by
        rw [Finset.mul_sum]

lemma wt_bound {α : Type*} [DecidableEq α] {U S : Finset α} (hsU : S ⊆ U) (s : ℕ)
    (hs_ge : U.card ≤ 10 * (S.card - (s - 1))) (m : ℕ) (hm : m ≤ U.card) :
    ∑ l ∈ tuples U m, wt S s l ≤ (73 / 80 : ℚ) ^ m * ((tuples U m).card : ℚ) := by
  induction m with
  | zero =>
    simp only [tuples, Finset.sum_singleton, wt, hits, List.countP_nil, pow_zero,
      Finset.card_singleton, Nat.cast_one, mul_one]
    split_ifs <;> norm_num
  | succ m ih =>
    have hm' : m < U.card := hm
    have ih' := ih (Nat.le_of_lt hm')
    have hstep := wt_step hsU hm' hs_ge
    have hcard : ((tuples U (m + 1)).card : ℚ) = (U.card - m : ℚ) * ((tuples U m).card : ℚ) := by
      rw [tuples_card_succ U m (Nat.le_of_lt hm')]
      have : m ≤ U.card := Nat.le_of_lt hm'
      push_cast [this]
      ring
    have hnn : (0 : ℚ) ≤ (73 / 80 : ℚ) * (U.card - m : ℚ) := by
      have : (m : ℚ) ≤ (U.card : ℚ) := by exact_mod_cast Nat.le_of_lt hm'
      linarith
    calc ∑ l ∈ tuples U (m + 1), wt S s l
        ≤ (73 / 80 : ℚ) * (U.card - m : ℚ) * ∑ l ∈ tuples U m, wt S s l := hstep
      _ ≤ (73 / 80 : ℚ) * (U.card - m : ℚ) * ((73 / 80 : ℚ) ^ m * ((tuples U m).card : ℚ)) :=
          mul_le_mul_of_nonneg_left ih' hnn
      _ = (73 / 80 : ℚ) ^ (m + 1) * ((tuples U (m + 1)).card : ℚ) := by
          rw [hcard, pow_succ']
          ring

lemma sum_pow2_lt (n : ℕ) (f : ℕ → Bool) :
    (∑ j ∈ Finset.range n, if f j then 2 ^ j else 0) < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    cases f n <;> simp <;> omega

lemma testBit_two_pow_add {n A : ℕ} (hA : A < 2 ^ n) (c : ℕ) :
    (2 ^ n + A).testBit c = if c = n then true else A.testBit c := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq]
  rcases lt_trichotomy c n with hlt | rfl | hgt
  · have hne : c ≠ n := ne_of_lt hlt
    simp only [hne, ite_false]
    have hpow : 2 ^ n = 2 ^ c * 2 ^ (n - c) := by rw [← pow_add, Nat.add_sub_of_le (le_of_lt hlt)]
    have hdiv2 : 2 ∣ 2 ^ (n - c) := dvd_pow_self 2 (by omega)
    rw [hpow, Nat.mul_add_div (Nat.pow_pos (by norm_num))]
    rcases hdiv2 with ⟨m, hm⟩
    rw [hm]
    simp [Nat.add_mod]
  · simp only [↓reduceIte]
    have hdiv : (2 ^ c + A) / 2 ^ c = 1 := by
      apply Nat.div_eq_of_lt_le
      · simp
      · have htwo : (1 + 1) * 2 ^ c = 2 ^ c + 2 ^ c := by ring
        omega
    rw [hdiv]
    norm_num
  · have hne : c ≠ n := ne_of_gt hgt
    simp only [hne, ite_false]
    have h2 : 2 ^ n + A < 2 ^ c := by
      have : 2 ^ (n + 1) ≤ 2 ^ c := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ'] at this
      omega
    have hA' : A < 2 ^ c := lt_of_le_of_lt (Nat.le_add_left _ _) h2
    rw [Nat.div_eq_of_lt h2, Nat.div_eq_of_lt hA']

lemma sum_pow2_testBit (n : ℕ) (f : ℕ → Bool) (c : ℕ) :
    (∑ j ∈ Finset.range n, if f j then 2 ^ j else 0).testBit c = if c < n then f c else false := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    cases hfn : f n
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [ih]
      rcases lt_trichotomy c n with hlt | rfl | hgt
      · simp [hlt, Nat.lt_succ_of_lt hlt]
      · simp [hfn]
      · have h1 : ¬ (c < n) := by omega
        have h2 : ¬ (c < n + 1) := by omega
        simp [h1, h2]
    · simp only [↓reduceIte]
      rw [add_comm, testBit_two_pow_add (sum_pow2_lt n f) c, ih]
      rcases lt_trichotomy c n with hlt | rfl | hgt
      · have hne : c ≠ n := ne_of_lt hlt
        simp [hne, hlt, Nat.lt_succ_of_lt hlt]
      · simp [hfn]
      · have hne : c ≠ n := ne_of_gt hgt
        have h1 : ¬ (c < n) := by omega
        have h2 : ¬ (c < n + 1) := by omega
        simp [hne, h1, h2]

lemma list_countP_eq_filter_card {α : Type*} (l : List α) (p : α → Bool) :
    l.countP p = (Finset.univ.filter (fun i : Fin l.length => p l[i.val] = true)).card := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.countP_cons, ih, Finset.card_filter, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, List.getElem_cons_zero, Fin.val_succ, List.getElem_cons_succ]
    by_cases hpx : p x = true <;> simp [hpx]
    omega

structure InnerWordsData (s : ℕ) (b : Module.Basis (Fin s) (ZMod 2) (GaloisField 2 s)) where
  m : ℕ
  t_w : ℕ
  w : Fin m ↪ GaloisField 2 s
  addr_w : Fin m ↪ (Fin t_w → Bool)
  hm_pos : 0 < m
  ht_pos : 0 < t_w
  h2t : 2 ^ t_w ≤ 2 * m
  hm_bound : (s ≤ 11 → m = 2 ^ s - 1) ∧ (12 ≤ s → m = 64 * s)
  hw_ne : ∀ i : Fin m, w i ≠ 0
  hw_equi : ∀ (B : GaloisField 2 s →ₗ[ZMod 2] (Fin 3 → ZMod 2)), Function.Surjective B →
    ∀ z : Fin 3 → ZMod 2, m ≤ 64 * (Finset.univ.filter (fun i : Fin m => B (w i) = z)).card
  dec : ℕ → List Gate → ℕ → (Fin t_w → ℕ) → List Gate × (Fin s → ℕ)
  hdec : ∀ (n : ℕ) (gs : List Gate) (z : ℕ) (yWires : Fin t_w → ℕ),
    GoodGates n gs → z < n + gs.length →
    (∀ xs : List Bool, xs.length = n → (evalGates gs xs).getD z false = false) →
    (∀ q : Fin t_w, yWires q < n + gs.length) →
    let r := dec n gs z yWires
    Extends gs r.1 ∧ GoodGates n r.1 ∧ r.1.length ≤ gs.length + (128 * (s * s) + s) ∧
      (∀ c : Fin s, r.2 c < n + r.1.length) ∧
      ∀ (xs : List Bool) (i₀ : Fin m), xs.length = n →
        (∀ q : Fin t_w, (evalGates gs xs).getD (yWires q) false = addr_w i₀ q) →
        ∀ c : Fin s, b2z ((evalGates r.1 xs).getD (r.2 c) false) = b.repr (w i₀) c

lemma exists_inner_words (s : ℕ) (hs : 6 ≤ s)
    (b : Module.Basis (Fin s) (ZMod 2) (GaloisField 2 s)) :
    Nonempty (InnerWordsData s b) := by
  classical
  let _instF : Fintype (GaloisField 2 s) := Fintype.ofFinite (GaloisField 2 s)
  have hs0 : s ≠ 0 := by omega
  by_cases hs11 : s ≤ 11
  · let m := 2 ^ s - 1
    have hm_pos : 0 < m := by
      have : 1 < 2 ^ s := Nat.one_lt_pow hs0 (by norm_num)
      omega
    let wFn : Fin m → GaloisField 2 s := fun i =>
      b.equivFun.symm (fun c => if (i.val + 1).testBit c.val then 1 else 0)
    have hw_inj : Function.Injective wFn := by
      intro i₁ i₂ h
      have h' := b.equivFun.symm.injective h
      apply Fin.ext
      have hi1 : i₁.val + 1 < 2 ^ s := by omega
      have hi2 : i₂.val + 1 < 2 ^ s := by omega
      have htb := testBit_inj_of_lt hi1 hi2 (fun c => by
        have hc := congr_fun h' c
        cases h1 : (i₁.val + 1).testBit c.val <;> cases h2 : (i₂.val + 1).testBit c.val <;>
          simp [h1, h2] at hc ⊢)
      omega
    have hw_ne : ∀ i : Fin m, wFn i ≠ 0 := by
      intro i hi
      have h' : ∀ c : Fin s, b.equivFun (wFn i) c = 0 := fun c => by
        rw [hi, map_zero, Pi.zero_apply]
      have hi1 : i.val + 1 < 2 ^ s := by omega
      have heq0 : i.val + 1 = 0 := testBit_inj_of_lt hi1 (Nat.pow_pos (by norm_num)) (fun c => by
        have hc := h' c
        dsimp only [wFn] at hc
        rw [LinearEquiv.apply_symm_apply] at hc
        rw [Nat.zero_testBit]
        cases h1 : (i.val + 1).testBit c.val <;> simp [h1] at hc ⊢)
      omega
    let addrFn : Fin m → (Fin s → Bool) := fun i c => (i.val + 1).testBit c.val
    have haddr_inj : Function.Injective addrFn := by
      intro i₁ i₂ h
      apply Fin.ext
      have htb := testBit_inj_of_lt (by omega : i₁.val + 1 < 2 ^ s) (by omega : i₂.val + 1 < 2 ^ s)
        (fun c => congr_fun h c)
      omega
    refine ⟨{
      m := m
      t_w := s
      w := ⟨wFn, hw_inj⟩
      addr_w := ⟨addrFn, haddr_inj⟩
      hm_pos := hm_pos
      ht_pos := by omega
      h2t := by dsimp only [m]; omega
      hm_bound := ⟨fun _ => rfl, fun h12 => absurd h12 (by omega)⟩
      hw_ne := hw_ne
      hw_equi := ?_
      dec := fun _ gs _ yWires => (gs, yWires)
      hdec := ?_
    }⟩
    · intro B hB z
      have hKcard : Fintype.card (GaloisField 2 s) = 2 ^ s := by
        rw [← Nat.card_eq_fintype_card, GaloisField.card 2 s hs0]
      have hfib := ker_card_of_surjective_gen (by omega) hKcard B hB z
      let U : Finset (GaloisField 2 s) := Finset.univ.erase 0
      have hU_ge : 2 ^ (s - 3) - 1 ≤ (U.filter (fun x => B x = z)).card := by
        have hdiff : (Finset.univ.filter (fun x => B x = z)) \ {0} ⊆ U.filter (fun x => B x = z) := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, U, Finset.mem_erase] at hx ⊢
          exact ⟨⟨hx.2, trivial⟩, hx.1⟩
        have hc := Finset.card_le_card hdiff
        have hpart_s := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun x => B x = z)) {0}
        have hinter_le : (Finset.univ.filter (fun x => B x = z) ∩ {0}).card ≤ 1 :=
          (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
        omega
      have hsurj_w : ∀ x ∈ U, ∃ i : Fin m, wFn i = x := by
        intro x hx
        have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
        let f : ℕ → Bool := fun j => if hj : j < s then decide (b.repr x ⟨j, hj⟩ = 1) else false
        let valNat := ∑ j ∈ Finset.range s, if f j then 2 ^ j else 0
        have hval_lt : valNat < 2 ^ s := sum_pow2_lt s f
        have hval_pos : 0 < valNat := by
          by_contra h0
          have h0' : valNat = 0 := by omega
          have hzero : ∀ c : Fin s, b.repr x c = 0 := by
            intro c
            have hle : (if f c.val then 2 ^ c.val else 0) ≤ valNat :=
              Finset.single_le_sum (f := fun j => if f j then 2 ^ j else 0)
                (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr c.isLt)
            rw [h0'] at hle
            have hp : 0 < 2 ^ c.val := Nat.pow_pos (by norm_num)
            rcases zmod2_cases (b.repr x c) with hc0 | hc1
            · exact hc0
            · have hfc : f c.val = true := by simp [f, c.isLt, hc1]
              simp [hfc] at hle
          apply hx0
          apply b.repr.injective
          ext c
          simp [hzero c]
        refine ⟨⟨valNat - 1, by omega⟩, ?_⟩
        apply b.equivFun.injective
        ext c
        have hsub1 : (valNat - 1) + 1 = valNat := by omega
        simp only [wFn, LinearEquiv.apply_symm_apply, hsub1]
        have htb : valNat.testBit c.val = f c.val := by
          rw [sum_pow2_testBit s f c.val]
          simp [c.isLt]
        rw [htb]
        simp only [f, dite_true, c.isLt, Module.Basis.equivFun_apply]
        rcases zmod2_cases (b.repr x c) with hc0 | hc1
        · simp [hc0]
        · simp [hc1]
      have hU_bij : (U.filter (fun x => B x = z)).card =
          (Finset.univ.filter (fun i : Fin m => B (wFn i) = z)).card := by
        refine Finset.card_bij (fun x hx => Classical.choose (hsurj_w x (Finset.mem_filter.mp hx).1)) ?_ ?_ ?_
        · intro x hx
          have hspec := Classical.choose_spec (hsurj_w x (Finset.mem_filter.mp hx).1)
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hspec]
          exact (Finset.mem_filter.mp hx).2
        · intro x₁ hx₁ x₂ hx₂ heq
          have h1 := Classical.choose_spec (hsurj_w x₁ (Finset.mem_filter.mp hx₁).1)
          have h2 := Classical.choose_spec (hsurj_w x₂ (Finset.mem_filter.mp hx₂).1)
          rw [← h1, ← h2, heq]
        · intro i hi
          refine ⟨wFn i, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hw_ne i, Finset.mem_univ _⟩,
            (Finset.mem_filter.mp hi).2⟩, ?_⟩
          apply hw_inj
          exact Classical.choose_spec (hsurj_w (wFn i) (Finset.mem_erase.mpr ⟨hw_ne i, Finset.mem_univ _⟩))
      change m ≤ 64 * (Finset.univ.filter (fun i : Fin m => B (wFn i) = z)).card
      rw [← hU_bij]
      have h64 : m ≤ 64 * (2 ^ (s - 3) - 1) := by
        dsimp only [m]
        have h2s : 2 ^ s = 8 * 2 ^ (s - 3) := by
          have : 8 = 2 ^ 3 := by norm_num
          rw [this, ← pow_add]
          congr 1; omega
        have hge8 : 8 ≤ 2 ^ (s - 3) := by
          have : 2 ^ 3 ≤ 2 ^ (s - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
          simpa using this
        omega
      exact h64.trans (Nat.mul_le_mul_left 64 hU_ge)
    · intro n gs z yWires hgs hz _ hy
      refine ⟨extends_refl gs, hgs, Nat.le_add_right _ _, hy, fun xs i₀ _ hy_bits c => ?_⟩
      rw [hy_bits c]
      dsimp only [addrFn, wFn, b2z]
      simp only [Function.Embedding.coeFn_mk]
      have hev : b.repr (b.equivFun.symm (fun c => if (i₀.val + 1).testBit c.val = true then 1 else 0)) c =
          if (i₀.val + 1).testBit c.val = true then 1 else 0 := by
        rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      rw [hev]
  · have hs12 : 12 ≤ s := by omega
    have hm_le_pow : 64 * s < 2 ^ s := by
      clear b
      induction s, hs12 using Nat.le_induction with
      | base => norm_num
      | succ s' hs' ih =>
        rw [pow_succ']
        omega
    have hm_le_10 : 2 ^ s - 1 ≤ 10 * (2 ^ (s - 3) - s) := by
      clear b hs12
      have hstep : ∀ n : ℕ, 12 ≤ n → 10 * n ≤ 2 ^ (n - 2) := by
        intro n hn
        induction n, hn using Nat.le_induction with
        | base => norm_num
        | succ n' hn' ih =>
          have : n' - 2 + 1 = n' + 1 - 2 := by omega
          rw [← this, pow_succ']
          omega
      have h10n := hstep s (by omega)
      have h2s : 2 ^ s = 8 * 2 ^ (s - 3) := by
        have : 8 = 2 ^ 3 := by norm_num
        rw [this, ← pow_add]
        congr 1; omega
      have h2s2 : 2 ^ (s - 2) = 2 * 2 ^ (s - 3) := by
        have : s - 2 = (s - 3) + 1 := by omega
        rw [this, pow_succ']
      have hle_s : s ≤ 2 ^ (s - 3) := by omega
      omega
    let m := 64 * s
    let t_w := Nat.clog 2 m
    have hm_pos : 0 < m := by omega
    have ht_pos : 0 < t_w := by
      by_contra h0
      have h0' : t_w = 0 := by omega
      have hle : m ≤ 2 ^ t_w := Nat.le_pow_clog (by norm_num : 1 < 2) m
      rw [h0'] at hle
      dsimp only [m] at hle
      omega
    have hm_le_2t : m ≤ 2 ^ t_w := Nat.le_pow_clog (by norm_num : 1 < 2) m
    have h2t_le : 2 ^ t_w ≤ 2 * m := by
      have hp : 2 ^ t_w.pred < m := Nat.pow_pred_clog_lt_self 2 (by dsimp only [m]; omega)
      have hpred : t_w.pred = t_w - 1 := Nat.pred_eq_sub_one (n := t_w)
      have hpow : 2 ^ t_w = 2 * 2 ^ t_w.pred := by
        have : t_w = t_w.pred + 1 := by omega
        conv_lhs => rw [this, pow_succ']
      omega
    have ht_le_s : t_w ≤ s := by
      by_contra hgt
      have hpred : t_w.pred = t_w - 1 := Nat.pred_eq_sub_one (n := t_w)
      have hle1 : s ≤ t_w.pred := by omega
      have hp : 2 ^ t_w.pred < m := Nat.pow_pred_clog_lt_self 2 (by dsimp only [m]; omega)
      have hpow : 2 ^ s ≤ 2 ^ t_w.pred := Nat.pow_le_pow_right (by norm_num) hle1
      have hm_eq : m = 64 * s := rfl
      omega
    let U : Finset (GaloisField 2 s) := Finset.univ.erase 0
    have hKcard : Fintype.card (GaloisField 2 s) = 2 ^ s := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 s hs0]
    have hUcard : U.card = 2 ^ s - 1 := by
      simp [U, Finset.card_erase_of_mem (Finset.mem_univ _), hKcard]
    have hm_le_U : m ≤ U.card := by
      rw [hUcard]
      have hm_eq : m = 64 * s := rfl
      omega
    let lin : (Fin 3 → Fin s → ZMod 2) → GaloisField 2 s → Fin 3 → ZMod 2 :=
      fun f x c => ∑ j : Fin s, b.repr x j * f c j
    let S : (Fin 3 → Fin s → ZMod 2) × (Fin 3 → ZMod 2) → Finset (GaloisField 2 s) :=
      fun p => U.filter (fun x => lin p.1 x = p.2)
    let GoodPairs := (Finset.univ : Finset ((Fin 3 → Fin s → ZMod 2) × (Fin 3 → ZMod 2))).filter
      (fun p => 2 ^ (s - 3) - 1 ≤ (S p).card)
    let bad := fun p => (tuples U m).filter (fun l => hits (S p) l < s)
    have hbad_bound : ∀ p ∈ GoodPairs, (bad p).card * (8 * 2 ^ (5 * s)) < (tuples U m).card := by
      intro p hp
      have hp_card : 2 ^ (s - 3) - 1 ≤ (S p).card := (Finset.mem_filter.mp hp).2
      have hs_ge : U.card ≤ 10 * ((S p).card - (s - 1)) := by
        rw [hUcard]
        omega
      have hwt := wt_bound (Finset.filter_subset _ U : S p ⊆ U) s hs_ge m hm_le_U
      have hlow : ∀ l ∈ bad p, 8 * (1 / 8 : ℚ) ^ s ≤ wt (S p) s l := by
        intro l hl
        have hlt : hits (S p) l < s := (Finset.mem_filter.mp hl).2
        simp only [wt, not_le_of_gt hlt, ↓reduceIte]
        have h1 : (1 / 8 : ℚ) ^ (s - 1) ≤ (1 / 8 : ℚ) ^ hits (S p) l := by
          apply pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have h2 : 8 * (1 / 8 : ℚ) ^ s = (1 / 8 : ℚ) ^ (s - 1) := by
          have : s = (s - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
          ring
        linarith
      have hsum_bad : ((bad p).card : ℚ) * (8 * (1 / 8 : ℚ) ^ s) ≤ ∑ l ∈ bad p, wt (S p) s l := by
        have := Finset.sum_le_sum hlow
        simpa [Finset.sum_const, nsmul_eq_mul] using this
      have hsub_sum : ∑ l ∈ bad p, wt (S p) s l ≤ ∑ l ∈ tuples U m, wt (S p) s l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun l _ _ => wt_nonneg _ _ _)
      have hq : ((bad p).card : ℚ) * (8 * (1 / 8 : ℚ) ^ s) ≤ (73 / 80 : ℚ) ^ m * ((tuples U m).card : ℚ) :=
        hsum_bad.trans (hsub_sum.trans hwt)
      have hmul_pos : (0 : ℚ) < 8 ^ s * 2 ^ (5 * s) := by positivity
      have hq2 := mul_le_mul_of_nonneg_right hq (le_of_lt hmul_pos)
      have hlhs : ((bad p).card : ℚ) * (8 * (1 / 8 : ℚ) ^ s) * (8 ^ s * 2 ^ (5 * s)) =
          ((bad p).card : ℚ) * (8 * 2 ^ (5 * s)) := by
        have h8 : (1 / 8 : ℚ) ^ s * 8 ^ s = 1 := by rw [← mul_pow]; norm_num
        calc ((bad p).card : ℚ) * (8 * (1 / 8 : ℚ) ^ s) * (8 ^ s * 2 ^ (5 * s))
            = ((bad p).card : ℚ) * (8 * ((1 / 8 : ℚ) ^ s * 8 ^ s) * 2 ^ (5 * s)) := by ring
          _ = ((bad p).card : ℚ) * (8 * 2 ^ (5 * s)) := by rw [h8]; ring
      have hrhs : (73 / 80 : ℚ) ^ m * ((tuples U m).card : ℚ) * (8 ^ s * 2 ^ (5 * s)) =
          ((73 / 80 : ℚ) ^ 64 * 256) ^ s * ((tuples U m).card : ℚ) := by
        have hm_eq : m = 64 * s := rfl
        have h256 : (8 : ℚ) ^ s * 2 ^ (5 * s) = 256 ^ s := by
          have : (2 : ℚ) ^ (5 * s) = (2 ^ 5) ^ s := by rw [← pow_mul]
          rw [this, ← mul_pow]
          norm_num
        rw [hm_eq, pow_mul, h256]
        calc ((73 / 80 : ℚ) ^ 64) ^ s * ((tuples U (64 * s)).card : ℚ) * 256 ^ s
            = (((73 / 80 : ℚ) ^ 64) ^ s * 256 ^ s) * ((tuples U (64 * s)).card : ℚ) := by ring
          _ = ((73 / 80 : ℚ) ^ 64 * 256) ^ s * ((tuples U (64 * s)).card : ℚ) := by rw [← mul_pow]
      have hlt_one : ((73 / 80 : ℚ) ^ 64 * 256) ^ s < 1 := by
        have hbase : (73 / 80 : ℚ) ^ 64 * 256 < 1 := by norm_num
        have hnn : 0 ≤ (73 / 80 : ℚ) ^ 64 * 256 := by positivity
        exact pow_lt_one₀ hnn hbase hs0
      have hpos_card : (0 : ℚ) < ((tuples U m).card : ℚ) := by
        exact_mod_cast tuples_card_pos U m hm_le_U
      have hstrict : ((bad p).card : ℚ) * (8 * 2 ^ (5 * s)) < ((tuples U m).card : ℚ) := by
        rw [hlhs] at hq2
        rw [hrhs] at hq2
        have h1 : ((73 / 80 : ℚ) ^ 64 * 256) ^ s * ((tuples U m).card : ℚ) < 1 * ((tuples U m).card : ℚ) :=
          mul_lt_mul_of_pos_right hlt_one hpos_card
        linarith
      exact_mod_cast hstrict
    have hunion_lt : (GoodPairs.biUnion bad).card < (tuples U m).card := by
      by_cases hne : GoodPairs.Nonempty
      · have hsum_lt : (∑ p ∈ GoodPairs, (bad p).card) * (8 * 2 ^ (5 * s)) <
            GoodPairs.card * (tuples U m).card := by
          rw [Finset.sum_mul]
          calc ∑ p ∈ GoodPairs, (bad p).card * (8 * 2 ^ (5 * s))
              < ∑ _p ∈ GoodPairs, (tuples U m).card := Finset.sum_lt_sum_of_nonempty hne hbad_bound
            _ = GoodPairs.card * (tuples U m).card := by simp [Finset.sum_const, smul_eq_mul]
        have hgp_le : GoodPairs.card ≤ 8 * 2 ^ (5 * s) := by
          have h1 : GoodPairs.card ≤ Fintype.card ((Fin 3 → Fin s → ZMod 2) × (Fin 3 → ZMod 2)) :=
            Finset.card_le_univ GoodPairs
          have h2 : Fintype.card ((Fin 3 → Fin s → ZMod 2) × (Fin 3 → ZMod 2)) = 8 * 2 ^ (3 * s) := by
            simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, ZMod.card]
            have : (2 ^ s) ^ 3 = 2 ^ (3 * s) := by rw [← pow_mul]; ring_nf
            rw [this]
            ring
          have h3 : 2 ^ (3 * s) ≤ 2 ^ (5 * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hcb : (GoodPairs.biUnion bad).card ≤ ∑ p ∈ GoodPairs, (bad p).card := Finset.card_biUnion_le
        have hmul_le : (GoodPairs.biUnion bad).card * (8 * 2 ^ (5 * s)) <
            (8 * 2 ^ (5 * s)) * (tuples U m).card := by
          calc (GoodPairs.biUnion bad).card * (8 * 2 ^ (5 * s))
              ≤ (∑ p ∈ GoodPairs, (bad p).card) * (8 * 2 ^ (5 * s)) :=
                Nat.mul_le_mul_right _ hcb
            _ < GoodPairs.card * (tuples U m).card := hsum_lt
            _ ≤ (8 * 2 ^ (5 * s)) * (tuples U m).card := Nat.mul_le_mul_right _ hgp_le
        have hpos8 : 0 < 8 * 2 ^ (5 * s) := by positivity
        nlinarith
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.biUnion_empty, Finset.card_empty]
        exact tuples_card_pos U m hm_le_U
    have hdiff_ne : (tuples U m \ GoodPairs.biUnion bad).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      have hsub : tuples U m ⊆ GoodPairs.biUnion bad := Finset.sdiff_eq_empty_iff_subset.mp h0
      have := Finset.card_le_card hsub
      omega
    obtain ⟨l, hl⟩ := hdiff_ne
    rw [Finset.mem_sdiff, Finset.mem_biUnion] at hl
    rcases hl with ⟨hl_tup, hl_not_bad⟩
    have hl_mem := tuples_mem hl_tup
    let wFn : Fin m → GaloisField 2 s := fun i => l[i.val]'(by omega)
    have hw_inj : Function.Injective wFn := by
      intro i₁ i₂ h
      apply Fin.ext
      exact (hl_mem.2.1.getElem_inj_iff).mp h
    have hw_ne : ∀ i : Fin m, wFn i ≠ 0 := by
      intro i
      have hiU : wFn i ∈ U := hl_mem.2.2 _ (List.getElem_mem _)
      exact (Finset.mem_erase.mp hiU).1
    let addrFn : Fin m → (Fin t_w → Bool) := fun i q => i.val.testBit q.val
    have haddr_inj : Function.Injective addrFn := by
      intro i₁ i₂ h
      apply Fin.ext
      exact testBit_inj_of_lt (lt_of_lt_of_le i₁.isLt hm_le_2t) (lt_of_lt_of_le i₂.isLt hm_le_2t)
        (fun q => congr_fun h q)
    let wBits : Fin m → Fin s → Bool := fun i c => decide (b.repr (wFn i) c = 1)
    refine ⟨{
      m := m
      t_w := t_w
      w := ⟨wFn, hw_inj⟩
      addr_w := ⟨addrFn, haddr_inj⟩
      hm_pos := hm_pos
      ht_pos := ht_pos
      h2t := h2t_le
      hm_bound := ⟨fun h11 => absurd h11 (by omega), fun _ => rfl⟩
      hw_ne := hw_ne
      hw_equi := ?_
      dec := addDecoder s m t_w wBits
      hdec := ?_
    }⟩
    · intro B hB z
      let f : Fin 3 → Fin s → ZMod 2 := fun c j => B (b j) c
      have hlin : ∀ x : GaloisField 2 s, lin f x = B x := by
        intro x
        ext c
        have hx : x = ∑ j : Fin s, b.repr x j • b j := (b.sum_repr x).symm
        conv_rhs => rw [hx, map_sum]
        simp [lin, f, map_smul, smul_eq_mul]
      have hfib := ker_card_of_surjective_gen (by omega) hKcard B hB z
      have hU_ge : 2 ^ (s - 3) - 1 ≤ (S (f, z)).card := by
        have hdiff : (Finset.univ.filter (fun x => B x = z)) \ {0} ⊆ S (f, z) := by
          intro x hx
          simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton, S, U, Finset.mem_erase] at hx ⊢
          exact ⟨⟨hx.2, trivial⟩, by rw [hlin x]; exact hx.1⟩
        have hc := Finset.card_le_card hdiff
        have hpart_s := Finset.card_sdiff_add_card_inter (Finset.univ.filter (fun x => B x = z)) {0}
        have hinter_le : (Finset.univ.filter (fun x => B x = z) ∩ {0}).card ≤ 1 :=
          (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
        omega
      have hgp : (f, z) ∈ GoodPairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU_ge⟩
      have hnot : l ∉ bad (f, z) := fun hb => hl_not_bad ⟨(f, z), hgp, hb⟩
      have hhits : s ≤ hits (S (f, z)) l := by
        by_contra hlt
        exact hnot (Finset.mem_filter.mpr ⟨hl_tup, Nat.lt_of_not_le hlt⟩)
      have hcnt : hits (S (f, z)) l =
          (Finset.univ.filter (fun i : Fin m => B (wFn i) = z)).card := by
        dsimp only [hits]
        rw [list_countP_eq_filter_card]
        refine Finset.card_bij (fun i _ => ⟨i.val, by omega⟩) ?_ ?_ ?_
        · intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hmem : l[i.val] ∈ S (f, z) := of_decide_eq_true hi'
          have hwi : wFn ⟨i.val, by omega⟩ = l[i.val] := rfl
          rw [hwi, ← hlin (l[i.val])]
          exact (Finset.mem_filter.mp hmem).2
        · intro i₁ _ i₂ _ heq
          apply Fin.ext
          simpa using congr_arg Fin.val heq
        · intro i hi
          have hi' := (Finset.mem_filter.mp hi).2
          refine ⟨⟨i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          simp only [decide_eq_true_eq, S, Finset.mem_filter]
          refine ⟨hl_mem.2.2 _ (List.getElem_mem _), ?_⟩
          have hwi : wFn i = l[i.val] := rfl
          rw [← hwi, hlin]
          exact hi'
      change m ≤ 64 * (Finset.univ.filter (fun i : Fin m => B (wFn i) = z)).card
      rw [← hcnt]
      have hm_eq : m = 64 * s := rfl
      omega
    · intro n gs z yWires hgs hz hz_false hy
      have hd := addDecoder_spec ht_pos hm_le_2t wBits hgs hz hz_false hy
      refine ⟨hd.1, hd.2.1, ?_, hd.2.2.2.1, fun xs i₀ hxs hy_bits c => ?_⟩
      · have hlen := hd.2.2.1
        have hbd : t_w + m * t_w + s * m ≤ 128 * (s * s) + s := by
          have hm_eq : m = 64 * s := rfl
          nlinarith
        omega
      · rw [hd.2.2.2.2 xs i₀ hxs hy_bits c]
        dsimp only [wBits, b2z]
        rcases zmod2_cases (b.repr (wFn i₀) c) with hc0 | hc1
        · simp [hc0]
        · simp [hc1]

lemma two_pow_linear (m : ℕ) (hm : 7 ≤ m) : 28 * m ≤ (m - 1) * 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m' hm' ih =>
    have hpow : 2 ^ (m' + 1 - 1) = 2 * 2 ^ (m' - 1) := by
      have : m' + 1 - 1 = (m' - 1) + 1 := by omega
      rw [this, pow_succ']
    rw [hpow]
    have h1 : m' + 1 - 1 = m' := by omega
    rw [h1]
    have hle : (m' - 1) * 2 ^ (m' - 1) ≤ m' * 2 ^ (m' - 1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    linarith

lemma choose_s (k : ℕ) (hk : 18 ≤ k) :
    ∃ s : ℕ, 6 ≤ s ∧ 14 * k ≤ s * 2 ^ s ∧ 2 * s ≤ k ∧ s ≤ Nat.log2 k + 5 ∧
      (7 ≤ s → (s - 1) * 2 ^ (s - 1) < 14 * k) := by
  classical
  let P : ℕ → Prop := fun s => 6 ≤ s ∧ 14 * k ≤ s * 2 ^ s
  have hex : ∃ s, P s := by
    let s₀ := Nat.log2 (14 * k) + 1
    have hlt14 : 14 * k < 2 ^ s₀ := Nat.lt_log2_self
    have hge7 : 7 ≤ Nat.log2 (14 * k) := by
      by_contra hlt
      have h1 := (Nat.log2_lt (by omega : 14 * k ≠ 0)).mp (by omega : Nat.log2 (14 * k) < 7)
      norm_num at h1
      omega
    have hs₀6 : 6 ≤ s₀ := by omega
    have hmul : 2 ^ s₀ ≤ s₀ * 2 ^ s₀ := Nat.le_mul_of_pos_left _ (by omega)
    exact ⟨s₀, hs₀6, (le_of_lt hlt14).trans hmul⟩
  let s := Nat.find hex
  have hspec : P s := Nat.find_spec hex
  have hs6 : 6 ≤ s := hspec.1
  have hs_ge : 14 * k ≤ s * 2 ^ s := hspec.2
  have hs_min : 7 ≤ s → (s - 1) * 2 ^ (s - 1) < 14 * k := by
    intro hs7
    have hmin := Nat.find_min hex (by omega : s - 1 < s)
    by_contra hle
    push Not at hle
    exact hmin ⟨by omega, hle⟩
  have hs_le_log : s ≤ Nat.log2 k + 5 := by
    let s₀ := Nat.log2 (14 * k) + 1
    have hlt14 : 14 * k < 2 ^ s₀ := Nat.lt_log2_self
    have hge7 : 7 ≤ Nat.log2 (14 * k) := by
      by_contra hlt
      have h1 := (Nat.log2_lt (by omega : 14 * k ≠ 0)).mp (by omega : Nat.log2 (14 * k) < 7)
      norm_num at h1
      omega
    have hs₀P : P s₀ := ⟨by omega, (le_of_lt hlt14).trans (Nat.le_mul_of_pos_left _ (by omega))⟩
    have hs_le_s₀ : s ≤ s₀ := Nat.find_min' hex hs₀P
    have hlog_k : k < 2 ^ (Nat.log2 k + 1) := Nat.lt_log2_self
    have h14_lt : 14 * k < 2 ^ (Nat.log2 k + 5) := by
      have : 2 ^ (Nat.log2 k + 5) = 16 * 2 ^ (Nat.log2 k + 1) := by
        rw [show Nat.log2 k + 5 = (Nat.log2 k + 1) + 4 by omega, pow_add]
        norm_num
        ring
      omega
    have hlog14 : Nat.log2 (14 * k) < Nat.log2 k + 5 :=
      (Nat.log2_lt (by omega : 14 * k ≠ 0)).mpr h14_lt
    omega
  have h2sk : 2 * s ≤ k := by
    by_cases hs7 : 7 ≤ s
    · have h1 := two_pow_linear s hs7
      have h2 := hs_min hs7
      omega
    · omega
  exact ⟨s, hs6, hs_ge, h2sk, hs_le_log, hs_min⟩

lemma large_eval_correct
    (k s d t : ℕ) (hs0 : s ≠ 0) (hd_pos : 0 < d) (hk_le_ds : k ≤ d * s)
    (b : Module.Basis (Fin s) (ZMod 2) (GaloisField 2 s))
    (iw : InnerWordsData s b)
    (toBits : GaloisField 2 s ≃ₗ[ZMod 2] Fin s → ZMod 2)
    (htb_def : ∀ v c, toBits v c = Algebra.trace (ZMod 2) (GaloisField 2 s) (b c * v))
    (maskVal : GaloisField 2 s × Fin iw.m → (Fin k → ZMod 2))
    (hmask_def : ∀ u i₀ (idx : Fin k),
      maskVal (u, i₀) idx = toBits (u ^ (idx.val / s) * iw.w i₀) ⟨idx.val % s, Nat.mod_lt _ (Nat.pos_of_ne_zero hs0)⟩)
    (zWire : ℕ) (uWires dec_2 hor_2 fm_2 : Fin s → ℕ)
    (xPad : Fin d → Fin s → ℕ) (rem : Fin (2 * s - 1) → Fin s → ZMod 2)
    (hrem : ∀ x y : GaloisField 2 s, ∀ j : Fin s,
      (∑ p : Fin s, ∑ q : Fin s,
        rem ⟨p.val + q.val, by have := p.isLt; have := q.isLt; omega⟩ j * b.repr x p * b.repr y q) = b.repr (x * y) j)
    (dec_1 hor_1 fm_1 out_1 : List Gate) (out_2 : ℕ) (trWS : List ℕ)
    (htrWS_def : trWS = ((List.finRange s).filter (fun j => decide (Algebra.trace (ZMod 2) (GaloisField 2 s) (b j) = 1))).map fm_2)
    (xs : List Bool) (hxs_len : xs.length = k + t)
    (u : GaloisField 2 s) (i₀ : Fin iw.m) (x : Fin k → Bool)
    (hx_in : ∀ idx : Fin k, (evalGates dec_1 xs).getD idx.val false = x idx)
    (hu_in : ∀ q : Fin s, b2z ((evalGates dec_1 xs).getD (uWires q) false) = b.repr u q)
    (hdec_val : ∀ c : Fin s, b2z ((evalGates dec_1 xs).getD (dec_2 c) false) = b.repr (iw.w i₀) c)
    (hhz_dec : (evalGates dec_1 xs).getD zWire false = false)
    (hxPad_def : ∀ r : Fin d, ∀ c : Fin s, xPad r c = if _ : r.val * s + c.val < k then r.val * s + c.val else zWire)
    (hdec_ext_hor : Extends dec_1 hor_1)
    (hdec_lt : ∀ c : Fin s, dec_2 c < (k + t) + dec_1.length)
    (hhor_eval : ∀ (uVal accVal : GaloisField 2 s) (xVal : Fin d → GaloisField 2 s),
      (∀ j : Fin s, b2z ((evalGates dec_1 xs).getD (uWires j) false) = b.repr uVal j) →
      (∀ j : Fin s, b2z ((evalGates dec_1 xs).getD (xPad ⟨d - 1, by omega⟩ j) false) = b.repr accVal j) →
      (∀ (i : Fin d) (j : Fin s), b2z ((evalGates dec_1 xs).getD (xPad i j) false) = b.repr (xVal i) j) →
      ∀ j : Fin s, b2z ((evalGates hor_1 xs).getD (hor_2 j) false) =
        b.repr (accVal * uVal ^ (d - 1) +
          ∑ i ∈ Finset.range (d - 1), if hi : i < d then xVal ⟨i, hi⟩ * uVal ^ i else 0) j)
    (hfm_eval : ∀ c : Fin s, (evalGates fm_1 xs).getD (fm_2 c) false =
      decide ((∑ p : Fin s, ∑ q : Fin s,
        rem ⟨p.val + q.val, by have := p.isLt; have := q.isLt; omega⟩ c *
          b2z ((evalGates hor_1 xs).getD (hor_2 p) false) *
          b2z ((evalGates hor_1 xs).getD (dec_2 q) false)) = 1))
    (hout_eval : (evalGates out_1 xs).getD out_2 false =
      decide ((trWS.map (fun w => b2z ((evalGates fm_1 xs).getD w false))).sum = 1)) :
    (evalGates out_1 xs).getD out_2 false =
      decide ((∑ idx : Fin k, (if x idx then (1 : ZMod 2) else 0) * maskVal (u, i₀) idx) = 1) := by
  let xVal : Fin d → GaloisField 2 s := fun r =>
    b.equivFun.symm (fun c => if h : r.val * s + c.val < k then b2z (x ⟨r.val * s + c.val, h⟩) else 0)
  have hxPad_val : ∀ r : Fin d, ∀ c : Fin s,
      b2z ((evalGates dec_1 xs).getD (xPad r c) false) = b.repr (xVal r) c := by
    intro r c
    rw [hxPad_def r c]
    have hrep : b.repr (xVal r) c =
        if h : r.val * s + c.val < k then b2z (x ⟨r.val * s + c.val, h⟩) else 0 := by
      dsimp only [xVal]
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hrep]
    split_ifs with h
    · rw [hx_in ⟨r.val * s + c.val, h⟩]
    · rw [hhz_dec]
      rfl
  have hP_val : ∀ c : Fin s,
      b2z ((evalGates hor_1 xs).getD (hor_2 c) false) =
        b.repr (∑ r : Fin d, xVal r * u ^ r.val) c := by
    intro c
    have hacc_val : ∀ q : Fin s,
        b2z ((evalGates dec_1 xs).getD (xPad ⟨d - 1, by omega⟩ q) false) = b.repr (xVal ⟨d - 1, by omega⟩) q :=
      fun q => hxPad_val ⟨d - 1, by omega⟩ q
    have h := hhor_eval u (xVal ⟨d - 1, by omega⟩) xVal hu_in hacc_val hxPad_val c
    rw [h]
    congr 1
    have hsum_d : xVal ⟨d - 1, by omega⟩ * u ^ (d - 1) +
        ∑ r ∈ Finset.range (d - 1), (if hr : r < d then xVal ⟨r, hr⟩ * u ^ r else 0) =
        ∑ r : Fin d, xVal r * u ^ r.val := by
      have hrhs : ∑ r : Fin d, xVal r * u ^ r.val =
          ∑ r ∈ Finset.range d, (if hr : r < d then xVal ⟨r, hr⟩ * u ^ r else 0) := by
        rw [← Fin.sum_univ_eq_sum_range (fun r => if hr : r < d then xVal ⟨r, hr⟩ * u ^ r else 0)]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp [r.isLt]
      rw [hrhs]
      have hd_eq : d = (d - 1) + 1 := by omega
      conv_rhs => arg 1; rw [hd_eq]
      rw [Finset.sum_range_succ]
      rw [add_comm]
      congr 1
      simp [hd_pos]
    rw [hsum_d]
  have hfm_val : ∀ c : Fin s,
      b2z ((evalGates fm_1 xs).getD (fm_2 c) false) =
        b.repr ((∑ r : Fin d, xVal r * u ^ r.val) * iw.w i₀) c := by
    intro c
    rw [hfm_eval c, b2z_decide_eq]
    have hdec_ext : ∀ q : Fin s, b2z ((evalGates hor_1 xs).getD (dec_2 q) false) = b.repr (iw.w i₀) q := fun q => by
      rw [evalGates_extends_getD hdec_ext_hor xs (by rw [hxs_len]; exact hdec_lt q)]
      exact hdec_val q
    simp_rw [hP_val, hdec_ext]
    exact hrem _ _ c
  rw [hout_eval]
  congr 1
  apply congr_arg (· = 1)
  have htr_eq : (trWS.map (fun w => b2z ((evalGates fm_1 xs).getD w false))).sum =
      Algebra.trace (ZMod 2) (GaloisField 2 s) ((∑ r : Fin d, xVal r * u ^ r.val) * iw.w i₀) := by
    rw [htrWS_def, List.map_map]
    have hlist : ∀ (l : List (Fin s)),
        (List.map ((fun w => b2z ((evalGates fm_1 xs).getD w false)) ∘ fm_2)
          (l.filter (fun j => decide (Algebra.trace (ZMod 2) (GaloisField 2 s) (b j) = 1)))).sum =
          (l.map (fun j => b.repr ((∑ r : Fin d, xVal r * u ^ r.val) * iw.w i₀) j *
            Algebra.trace (ZMod 2) (GaloisField 2 s) (b j))).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a tl ih =>
        simp only [List.filter_cons, List.map_cons, List.sum_cons]
        rcases zmod2_cases (Algebra.trace (ZMod 2) (GaloisField 2 s) (b a)) with ha0 | ha1
        · have hdec0 : decide ((0 : ZMod 2) = 1) = false := by decide
          rw [ha0, hdec0]
          simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add]
          exact ih
        · have hdec1 : decide ((1 : ZMod 2) = 1) = true := by decide
          rw [ha1, hdec1]
          simp only [↓reduceIte, List.map_cons, List.sum_cons, mul_one, Function.comp_apply]
          rw [hfm_val a, ih]
    rw [hlist, list_sum_map_finRange]
    set Z := (∑ r : Fin d, xVal r * u ^ r.val) * iw.w i₀
    have hZ : Z = ∑ j : Fin s, b.repr Z j • b j := (b.sum_repr Z).symm
    conv_rhs => rw [hZ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul]
  rw [htr_eq]
  have hinner : ∑ idx : Fin k, (if x idx = true then (1 : ZMod 2) else 0) * maskVal (u, i₀) idx =
      Algebra.trace (ZMod 2) (GaloisField 2 s) ((∑ r : Fin d, xVal r * u ^ r.val) * iw.w i₀) := by
    simp_rw [hmask_def u i₀]
    have hs_pos : 0 < s := Nat.pos_of_ne_zero hs0
    have hreidx : ∑ idx : Fin k, (if x idx = true then (1 : ZMod 2) else 0) *
        toBits (u ^ (idx.val / s) * iw.w i₀) ⟨idx.val % s, Nat.mod_lt _ hs_pos⟩ =
        ∑ r : Fin d, ∑ c : Fin s,
          (if h : r.val * s + c.val < k then b2z (x ⟨r.val * s + c.val, h⟩) else 0) *
            toBits (u ^ r.val * iw.w i₀) c := by
      have hsum_d : ∑ r : Fin d, ∑ c : Fin s,
          (if h : r.val * s + c.val < k then b2z (x ⟨r.val * s + c.val, h⟩) else 0) *
            toBits (u ^ r.val * iw.w i₀) c =
          ∑ idx : Fin (d * s),
            (if h : idx.val < k then b2z (x ⟨idx.val, h⟩) else 0) *
              toBits (u ^ (idx.val / s) * iw.w i₀) ⟨idx.val % s, Nat.mod_lt _ hs_pos⟩ := by
        let eDS : Fin d × Fin s ≃ Fin (d * s) := finProdFinEquiv
        rw [← Fintype.sum_prod_type']
        refine Fintype.sum_equiv eDS _ _ fun ⟨r, c⟩ => ?_
        have he : (eDS (r, c)).val = r.val * s + c.val := by
          simp only [eDS, finProdFinEquiv, Equiv.coe_fn_mk]
          ring
        have hdiv : (r.val * s + c.val) / s = r.val := by
          rw [mul_comm, Nat.mul_add_div hs_pos, Nat.div_eq_of_lt c.isLt, add_zero]
        have hmod : (r.val * s + c.val) % s = c.val := by
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt c.isLt]
        simp only [he, hdiv, hmod]
      let g : ℕ → ZMod 2 := fun idx =>
        (if h : idx < k then b2z (x ⟨idx, h⟩) else 0) *
          toBits (u ^ (idx / s) * iw.w i₀) ⟨idx % s, Nat.mod_lt _ hs_pos⟩
      have hre_lhs : ∑ idx : Fin k, (if x idx = true then (1 : ZMod 2) else 0) *
          toBits (u ^ (idx.val / s) * iw.w i₀) ⟨idx.val % s, Nat.mod_lt _ hs_pos⟩ =
          ∑ idx : Fin k, g idx.val := by
        refine Finset.sum_congr rfl fun idx _ => ?_
        simp [g, idx.isLt, b2z]
      have hre_rhs : ∑ idx : Fin (d * s),
          (if h : idx.val < k then b2z (x ⟨idx.val, h⟩) else 0) *
            toBits (u ^ (idx.val / s) * iw.w i₀) ⟨idx.val % s, Nat.mod_lt _ hs_pos⟩ =
          ∑ idx : Fin (d * s), g idx.val := rfl
      rw [hre_lhs, hsum_d, hre_rhs, Fin.sum_univ_eq_sum_range g, Fin.sum_univ_eq_sum_range g]
      have hsplit : ∑ idx ∈ Finset.range (d * s),
          (if h : idx < k then b2z (x ⟨idx, h⟩) else 0) *
            toBits (u ^ (idx / s) * iw.w i₀) ⟨idx % s, Nat.mod_lt _ hs_pos⟩ =
          ∑ idx ∈ Finset.range k,
            (if h : idx < k then b2z (x ⟨idx, h⟩) else 0) *
              toBits (u ^ (idx / s) * iw.w i₀) ⟨idx % s, Nat.mod_lt _ hs_pos⟩ := by
        rw [← Finset.sum_sdiff (Finset.range_mono hk_le_ds)]
        have h0 : ∑ idx ∈ Finset.range (d * s) \ Finset.range k,
            (if h : idx < k then b2z (x ⟨idx, h⟩) else 0) *
              toBits (u ^ (idx / s) * iw.w i₀) ⟨idx % s, Nat.mod_lt _ hs_pos⟩ = 0 := by
          refine Finset.sum_eq_zero fun idx hidx => ?_
          have hge : ¬ (idx < k) := by
            have := (Finset.mem_sdiff.mp hidx).2
            simpa [Finset.mem_range] using this
          simp [hge]
        rw [h0, zero_add]
      rw [hsplit]
    rw [hreidx, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hxVal : xVal r = ∑ c : Fin s,
        (if h : r.val * s + c.val < k then b2z (x ⟨r.val * s + c.val, h⟩) else 0) • b c := by
      have hx0 := (b.sum_repr (xVal r)).symm
      conv_lhs => rw [hx0]
      refine Finset.sum_congr rfl fun c _ => ?_
      congr 1
      dsimp only [xVal]
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [hxVal, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Algebra.smul_mul_assoc, Algebra.smul_mul_assoc, map_smul, smul_eq_mul]
    congr 1
    rw [htb_def, mul_assoc]
  rw [hinner]

lemma large_case (k : ℕ) (hk : 18 ≤ k) :
    let F := ZMod 2
    let V := Fin k → F
    ∃ (M t : ℕ) (mask : Fin M ↪ V) (address : Fin M ↪ (Fin t → Bool))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      0 < M ∧ M ≤ 8960 * k ∧ 2 ^ t ≤ 2 * M ∧
      (∀ (A : V →ₗ[F] (Fin 3 → F)), Function.Surjective A → ∀ z : Fin 3 → F,
        M ≤ 128 * ((Finset.univ : Finset (Fin M)).filter (fun j => A (mask j) = z)).card) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (k + t) C ∧
      C.output < k + t + C.size ∧ C.size ≤ 4000 * k * (Nat.log2 k + 1) ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
        (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
      ∀ (x : Fin k → Bool) (j : Fin M),
        C.eval (List.ofFn x ++ List.ofFn (address j)) =
          decide ((∑ i : Fin k, (if x i then (1 : F) else 0) * mask j i) = 1) := by
  classical
  obtain ⟨s, hs6, hs_ge, h2sk, hs_log, hs_min⟩ := choose_s k hk
  have hs0 : s ≠ 0 := by omega
  obtain ⟨α, b, hb⟩ := exists_powerBasis s hs0
  obtain ⟨iw⟩ := exists_inner_words s hs6 b
  let _instF : Fintype (GaloisField 2 s) := Fintype.ofFinite (GaloisField 2 s)
  have hKcard : Fintype.card (GaloisField 2 s) = 2 ^ s := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 s hs0]
  let d := (k + s - 1) / s
  have hd_pos : 0 < d := Nat.div_pos (by omega) (by omega)
  have hk_le_ds : k ≤ d * s := by
    have hdiv := Nat.div_add_mod (k + s - 1) s
    have hmod : (k + s - 1) % s < s := Nat.mod_lt _ (by omega)
    dsimp only [d]
    rw [mul_comm] at hdiv
    omega
  have hds_sub_lt : (d - 1) * s < k := by
    have hmul : d * s ≤ k + s - 1 := Nat.div_mul_le_self (k + s - 1) s
    have : d * s = (d - 1) * s + s := by
      have : d = (d - 1) + 1 := by omega
      conv_lhs => rw [this, add_mul, one_mul]
    omega
  have hds_lt_2k : d * s < 2 * k := by
    have hmul : d * s ≤ k + s - 1 := Nat.div_mul_le_self (k + s - 1) s
    omega
  let M := 2 ^ s * iw.m
  let t := s + iw.t_w
  have hM_pos : 0 < M := Nat.mul_pos (Nat.pow_pos (by norm_num)) iw.hm_pos
  have hM_le : M ≤ 8960 * k := by
    by_cases hs6eq : s = 6
    · have hm11 := iw.hm_bound.1 (by omega)
      dsimp only [M]
      rw [hm11, hs6eq]
      norm_num
      omega
    · have hs7 : 7 ≤ s := by omega
      have hmin := hs_min hs7
      have h8960 : 320 * (s - 1) * 2 ^ s < 8960 * k := by
        have h2s : 2 ^ s = 2 * 2 ^ (s - 1) := by
          have : s = (s - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ']
        rw [h2s]
        linarith
      by_cases hs11 : s ≤ 11
      · have hm11 := iw.hm_bound.1 hs11
        have h2s_le : 2 ^ s ≤ 320 * (s - 1) := by
          interval_cases s <;> norm_num
        dsimp only [M]
        rw [hm11]
        have : 2 ^ s * (2 ^ s - 1) ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        nlinarith
      · have hm12 := iw.hm_bound.2 (by omega)
        dsimp only [M]
        rw [hm12]
        have h64 : 64 * s ≤ 320 * (s - 1) := by omega
        nlinarith
  have h2t : 2 ^ t ≤ 2 * M := by
    dsimp only [t, M]
    rw [pow_add]
    have := iw.h2t
    nlinarith
  let toBits := toBitsEquiv s hs0 b
  let unpack : (Fin d → GaloisField 2 s) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    { toFun := fun v idx => toBits (v ⟨idx.val / s, (Nat.div_lt_iff_lt_mul (by omega)).mpr (lt_of_lt_of_le idx.isLt hk_le_ds)⟩)
        ⟨idx.val % s, Nat.mod_lt _ (by omega)⟩
      map_add' := fun v₁ v₂ => by ext idx; simp
      map_smul' := fun r v => by ext idx; simp }
  have hunpack_surj : Function.Surjective unpack := by
    intro y
    let v : Fin d → GaloisField 2 s := fun r =>
      toBits.symm (fun c => if h : r.val * s + c.val < k then y ⟨r.val * s + c.val, h⟩ else 0)
    refine ⟨v, ?_⟩
    ext idx
    dsimp only [unpack, LinearMap.coe_mk, AddHom.coe_mk, v]
    rw [LinearEquiv.apply_symm_apply]
    have hidx : (idx.val / s) * s + idx.val % s = idx.val := by
      rw [mul_comm, Nat.div_add_mod]
    simp only [hidx, idx.isLt, dite_true]
  let eK : GaloisField 2 s ≃ Fin (2 ^ s) := Fintype.equivFinOfCardEq hKcard
  let eM : GaloisField 2 s × Fin iw.m ≃ Fin M :=
    (eK.prodCongr (Equiv.refl (Fin iw.m))).trans finProdFinEquiv
  let maskPair : GaloisField 2 s × Fin iw.m → (Fin k → ZMod 2) := fun p =>
    unpack (fun r => p.1 ^ r.val * iw.w p.2)
  have hmask_inj : Function.Injective maskPair := by
    rintro ⟨u₁, i₁⟩ ⟨u₂, i₂⟩ heq
    have h0 : toBits (u₁ ^ 0 * iw.w i₁) = toBits (u₂ ^ 0 * iw.w i₂) := by
      ext c
      have hidx := congr_fun heq ⟨c.val, by omega⟩
      dsimp only [maskPair, unpack, LinearMap.coe_mk, AddHom.coe_mk] at hidx
      have hdiv : c.val / s = 0 := Nat.div_eq_of_lt c.isLt
      have hmod : c.val % s = c.val := Nat.mod_eq_of_lt c.isLt
      simpa [hdiv, hmod] using hidx
    have hw_eq : iw.w i₁ = iw.w i₂ := by
      have := toBits.injective h0
      simpa using this
    have hi_eq : i₁ = i₂ := iw.w.injective hw_eq
    subst hi_eq
    have h1 : toBits (u₁ ^ 1 * iw.w i₁) = toBits (u₂ ^ 1 * iw.w i₁) := by
      ext c
      have hidx := congr_fun heq ⟨s + c.val, by omega⟩
      dsimp only [maskPair, unpack, LinearMap.coe_mk, AddHom.coe_mk] at hidx
      have hdiv : (s + c.val) / s = 1 := by
        apply Nat.div_eq_of_lt_le
        · omega
        · have : (1 + 1) * s = s + s := by ring
          have := c.isLt
          omega
      have hmod : (s + c.val) % s = c.val := by
        rw [Nat.add_mod_left, Nat.mod_eq_of_lt c.isLt]
      simpa [hdiv, hmod] using hidx
    have huw : u₁ * iw.w i₁ = u₂ * iw.w i₁ := by
      have := toBits.injective h1
      simpa using this
    have hu_eq : u₁ = u₂ := mul_right_cancel₀ (iw.hw_ne i₁) huw
    rw [hu_eq]
  let mask : Fin M ↪ (Fin k → ZMod 2) :=
    ⟨fun j => maskPair (eM.symm j), fun j₁ j₂ h => eM.symm.injective (hmask_inj h)⟩
  let addrPair : GaloisField 2 s × Fin iw.m → (Fin t → Bool) := fun p q =>
    if hq : q.val < s then decide (b.repr p.1 ⟨q.val, hq⟩ = 1)
    else iw.addr_w p.2 ⟨q.val - s, by omega⟩
  have haddr_inj : Function.Injective addrPair := by
    rintro ⟨u₁, i₁⟩ ⟨u₂, i₂⟩ heq
    have hu : u₁ = u₂ := by
      apply b.repr.injective
      ext c
      have hq := congr_fun heq ⟨c.val, by omega⟩
      dsimp only [addrPair] at hq
      simp only [c.isLt, dite_true] at hq
      rcases zmod2_cases (b.repr u₁ c) with h1 | h1 <;> rcases zmod2_cases (b.repr u₂ c) with h2 | h2
      · rw [h1, h2]
      · simp [h1, h2] at hq
      · simp [h1, h2] at hq
      · rw [h1, h2]
    have hi : i₁ = i₂ := by
      apply iw.addr_w.injective
      ext q
      have hq := congr_fun heq ⟨s + q.val, by omega⟩
      dsimp only [addrPair] at hq
      have hns : ¬ (s + q.val < s) := by omega
      simp only [hns, dite_false] at hq
      have hq' : iw.addr_w i₁ q = iw.addr_w i₂ q := by
        have hqlt : q.val < iw.t_w := q.isLt
        have heq1 : (⟨s + q.val - s, by omega⟩ : Fin iw.t_w) = q := Fin.ext (by dsimp only; omega)
        simpa [heq1] using hq
      exact hq'
    rw [hu, hi]
  let address : Fin M ↪ (Fin t → Bool) :=
    ⟨fun j => addrPair (eM.symm j), fun j₁ j₂ h => eM.symm.injective (haddr_inj h)⟩
  let n := k + t
  have hn : 0 < n := by omega
  let r0 := addZero n []
  have hr0 := addZero_spec hn (goodGates_nil n)
  let uWires : Fin s → ℕ := fun j => k + j.val
  let yWires : Fin iw.t_w → ℕ := fun q => k + s + q.val
  have hu_lt : ∀ j : Fin s, uWires j < n + r0.1.length := fun j => by
    dsimp only [uWires, n, t]
    omega
  have hy_lt : ∀ q : Fin iw.t_w, yWires q < n + r0.1.length := fun q => by
    dsimp only [yWires, n, t]
    omega
  have hz_lt : r0.2 < n + r0.1.length := hr0.2.2.2.1
  let dec := iw.dec n r0.1 r0.2 yWires
  have hdec := iw.hdec n r0.1 r0.2 yWires hr0.2.1 hz_lt hr0.2.2.2.2 hy_lt
  have hdec_len := extends_length hdec.1
  let xPad : Fin d → Fin s → ℕ := fun r c =>
    if h : r.val * s + c.val < k then r.val * s + c.val else r0.2
  have hxPad_lt : ∀ r : Fin d, ∀ c : Fin s, xPad r c < n + dec.1.length := fun r c => by
    dsimp only [xPad]
    split_ifs with h
    · omega
    · exact lt_of_lt_of_le hz_lt (Nat.add_le_add_left hdec_len n)
  let rem : Fin (2 * s - 1) → Fin s → ZMod 2 := fun r j => b.repr (α ^ r.val) j
  have hrem : ∀ x y : GaloisField 2 s, ∀ j : Fin s,
      (∑ p : Fin s, ∑ q : Fin s,
        rem ⟨p.val + q.val, by have := p.isLt; have := q.isLt; omega⟩ j * b.repr x p * b.repr y q) = b.repr (x * y) j := by
    intro x y j
    have hx : x = ∑ p : Fin s, b.repr x p • b p := (b.sum_repr x).symm
    have hy : y = ∑ q : Fin s, b.repr y q • b q := (b.sum_repr y).symm
    have hxy : x * y = ∑ p : Fin s, ∑ q : Fin s, (b.repr x p * b.repr y q) • (α ^ (p.val + q.val)) := by
      conv_lhs => rw [hx, hy, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hb p, hb q, pow_add]
    have heqv : b.repr (x * y) j = b.equivFun (x * y) j := rfl
    rw [heqv, hxy, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [map_smul, Pi.smul_apply, smul_eq_mul, ← Module.Basis.equivFun_apply]
    dsimp only [rem]
    simp only [Module.Basis.equivFun_apply]
    ring
  have hhz_dec : ∀ xs : List Bool, xs.length = n → (evalGates dec.1 xs).getD r0.2 false = false := fun xs hxs => by
    rw [evalGates_extends_getD hdec.1 xs (by rw [hxs]; exact hz_lt)]
    exact hr0.2.2.2.2 xs hxs
  have hu_dec : ∀ j : Fin s, uWires j < n + dec.1.length := fun j =>
    lt_of_lt_of_le (hu_lt j) (Nat.add_le_add_left hdec_len n)
  let horner := addHornerAux s rem d n r0.2 xPad uWires (d - 1) (dec.1, xPad ⟨d - 1, by omega⟩)
  have hhorner := addHornerAux_spec (by omega : 0 < s) rem (GaloisField 2 s) b hrem
    (lt_of_lt_of_le hz_lt (Nat.add_le_add_left hdec_len n)) hhz_dec hxPad_lt hu_dec
    (d - 1) (by omega) (dec.1, xPad ⟨d - 1, by omega⟩) (extends_refl _) hdec.2.1
    (fun j => hxPad_lt ⟨d - 1, by omega⟩ j)
  have hhor_len := extends_length hhorner.1
  have hhz_hor : ∀ xs : List Bool, xs.length = n → (evalGates horner.1 xs).getD r0.2 false = false := fun xs hxs => by
    rw [evalGates_extends_getD hhorner.1 xs (by rw [hxs]; exact lt_of_lt_of_le hz_lt (Nat.add_le_add_left hdec_len n))]
    exact hhz_dec xs hxs
  have hdec_w_hor : ∀ c : Fin s, dec.2 c < n + horner.1.length := fun c =>
    lt_of_lt_of_le (hdec.2.2.2.1 c) (Nat.add_le_add_left hhor_len n)
  let finalMul := addMulGF s rem n horner.1 r0.2 horner.2 dec.2
  have hfm := addMulGF_spec (by omega : 0 < s) rem hhorner.2.1
    (lt_of_lt_of_le hz_lt (Nat.add_le_add_left (le_trans hdec_len hhor_len) n))
    hhz_hor hhorner.2.2.2.1 hdec_w_hor
  have hfm_len := extends_length hfm.1
  let trWS := ((List.finRange s).filter (fun j => decide (Algebra.trace (ZMod 2) (GaloisField 2 s) (b j) = 1))).map
    (fun j => finalMul.2 j)
  have htrWS_lt : ∀ w ∈ trWS, w < n + finalMul.1.length := by
    intro w hw
    simp only [trWS, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hw
    rcases hw with ⟨j, _, rfl⟩
    exact hfm.2.2.2.1 j
  have hhz_fm : ∀ xs : List Bool, xs.length = n → (evalGates finalMul.1 xs).getD r0.2 false = false := fun xs hxs => by
    rw [evalGates_extends_getD hfm.1 xs (by rw [hxs]; exact lt_of_lt_of_le hz_lt (Nat.add_le_add_left (le_trans hdec_len hhor_len) n))]
    exact hhz_hor xs hxs
  let out := addXorList n finalMul.1 r0.2 trWS
  have hout := addXorList_spec hfm.2.1
    (lt_of_lt_of_le hz_lt (Nat.add_le_add_left (le_trans hdec_len (le_trans hhor_len hfm_len)) n))
    htrWS_lt hhz_fm
  let C : Circuit := ⟨out.1, out.2⟩
  refine ⟨M, t, mask, address, C, hM_pos, hM_le, h2t, ?_, hout.2.1.1, hout.2.2.2.1, ?_, ?_, ?_⟩
  · intro A hA z
    let A' : (Fin d → GaloisField 2 s) →ₗ[ZMod 2] (Fin 3 → ZMod 2) := A.comp unpack
    have hA' : Function.Surjective A' := hA.comp hunpack_surj
    let ℓ : Fin 3 → Fin d → GaloisField 2 s →ₗ[ZMod 2] ZMod 2 := fun c r =>
      { toFun := fun w => A' (Pi.single r w) c
        map_add' := fun w₁ w₂ => by simp [Pi.single_add]
        map_smul' := fun a w => by simp [Pi.single_smul] }
    have hα_ex : ∀ c : Fin 3, ∀ r : Fin d, ∃ αcr : GaloisField 2 s,
        ∀ w : GaloisField 2 s, ℓ c r w = Algebra.trace (ZMod 2) (GaloisField 2 s) (αcr * w) :=
      fun c r => exists_dual_trace s hs0 b (ℓ c r)
    let αcr : Fin 3 → Fin d → GaloisField 2 s := fun c r => Classical.choose (hα_ex c r)
    have hαcr : ∀ c r w, ℓ c r w = Algebra.trace (ZMod 2) (GaloisField 2 s) (αcr c r * w) :=
      fun c r w => Classical.choose_spec (hα_ex c r) w
    have hA'_eq : ∀ v : Fin d → GaloisField 2 s, ∀ c : Fin 3,
        A' v c = ∑ r : Fin d, Algebra.trace (ZMod 2) (GaloisField 2 s) (αcr c r * v r) := by
      intro v c
      have hv : v = ∑ r : Fin d, Pi.single r (v r) := (Finset.univ_sum_single v).symm
      conv_lhs => rw [hv, map_sum]
      simp only [Finset.sum_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact hαcr c r (v r)
    let P : Fin 3 → Polynomial (GaloisField 2 s) := fun c =>
      ∑ r : Fin d, Polynomial.C (αcr c r) * Polynomial.X ^ r.val
    have hP_eval : ∀ u : GaloisField 2 s, ∀ c : Fin 3,
        (P c).eval u = ∑ r : Fin d, αcr c r * u ^ r.val := by
      intro u c
      simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
    have hAmask : ∀ (u : GaloisField 2 s) (i : Fin iw.m) (c : Fin 3),
        A (mask (eM (u, i))) c = Algebra.trace (ZMod 2) (GaloisField 2 s) ((P c).eval u * iw.w i) := by
      intro u i c
      have hmask_e : mask (eM (u, i)) = unpack (fun r => u ^ r.val * iw.w i) := by
        change maskPair (eM.symm (eM (u, i))) = _
        rw [eM.symm_apply_apply]
      rw [hmask_e]
      change A' (fun r => u ^ r.val * iw.w i) c = _
      rw [hA'_eq, hP_eval, Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [mul_assoc]
    let Q : (Fin 3 → ZMod 2) → Polynomial (GaloisField 2 s) := fun lam =>
      ∑ c : Fin 3, if lam c = 1 then P c else 0
    have hQ_ne : ∀ lam : Fin 3 → ZMod 2, lam ≠ 0 → Q lam ≠ 0 := by
      intro lam hlam hQ0
      have hcoeff0 : ∀ r : Fin d, ∑ c : Fin 3, (if lam c = 1 then αcr c r else 0) = 0 := by
        intro r
        have hc := congr_arg (fun p : Polynomial (GaloisField 2 s) => p.coeff r.val) hQ0
        dsimp only [Q] at hc
        rw [← Polynomial.lcoeff_apply, map_sum] at hc
        simp only [Polynomial.lcoeff_apply, Polynomial.coeff_zero] at hc
        have hPc : ∀ c : Fin 3, (if lam c = 1 then P c else 0).coeff r.val =
            if lam c = 1 then αcr c r else 0 := by
          intro c
          by_cases h1 : lam c = 1
          · simp only [h1, ite_true, P]
            rw [← Polynomial.lcoeff_apply, map_sum]
            simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
            rw [Finset.sum_eq_single r]
            · simp
            · intro r' _ hne
              have : r.val ≠ r'.val := fun h => hne (Fin.ext h.symm)
              simp only [this, ite_false]
            · intro hm
              exact absurd (Finset.mem_univ r) hm
          · simp only [h1, ite_false, Polynomial.coeff_zero]
        simp_rw [hPc] at hc
        exact hc
      have hne0 : ∃ c : Fin 3, lam c ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hlam (funext hall)
      obtain ⟨c₀, hc₀⟩ := hne0
      have hc₀1 : lam c₀ = 1 := by
        rcases zmod2_cases (lam c₀) with h0 | h1
        · exact absurd h0 hc₀
        · exact h1
      obtain ⟨v, hv⟩ := hA' (Pi.single c₀ (1 : ZMod 2) : Fin 3 → ZMod 2)
      have hlhs0 : ∑ c : Fin 3, lam c * A' v c = 0 := by
        simp_rw [hA'_eq v]
        have hswap : ∑ c : Fin 3, lam c * ∑ r : Fin d, Algebra.trace (ZMod 2) (GaloisField 2 s) (αcr c r * v r) =
            ∑ r : Fin d, Algebra.trace (ZMod 2) (GaloisField 2 s)
              ((∑ c : Fin 3, if lam c = 1 then αcr c r else 0) * v r) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_mul, map_sum]
          refine Finset.sum_congr rfl fun c _ => ?_
          rcases zmod2_cases (lam c) with hc0 | hc1
          · simp [hc0]
          · simp [hc1]
        rw [hswap]
        refine Finset.sum_eq_zero fun r _ => ?_
        rw [hcoeff0 r, zero_mul, map_zero]
      rw [hv] at hlhs0
      have hlhs1 : ∑ c : Fin 3, lam c * (Pi.single c₀ (1 : ZMod 2) : Fin 3 → ZMod 2) c = 1 := by
        rw [Finset.sum_eq_single c₀]
        · simp [hc₀1]
        · intro c _ hne
          simp [Pi.single_eq_of_ne hne]
        · intro hm
          exact absurd (Finset.mem_univ c₀) hm
      rw [hlhs1] at hlhs0
      exact absurd hlhs0 (by decide)
    have hQ_deg : ∀ lam : Fin 3 → ZMod 2, (Q lam).natDegree ≤ d - 1 := by
      intro lam
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun c _ => ?_
      by_cases h1 : lam c = 1
      · simp only [h1, ite_true, P]
        refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
        refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := r.isLt; omega)
      · simp [h1]
    let Bad : Finset (GaloisField 2 s) :=
      ((Finset.univ : Finset (Fin 3 → ZMod 2)).filter (fun lam => lam ≠ 0)).biUnion
        (fun lam => (Q lam).roots.toFinset)
    have hBad_card : Bad.card ≤ 7 * (d - 1) := by
      have h1 : Bad.card ≤ ∑ lam ∈ (Finset.univ.filter (fun lam : Fin 3 → ZMod 2 => lam ≠ 0)),
          (Q lam).roots.toFinset.card := Finset.card_biUnion_le
      have h2 : ∑ lam ∈ (Finset.univ.filter (fun lam : Fin 3 → ZMod 2 => lam ≠ 0)),
          (Q lam).roots.toFinset.card ≤
          ∑ _lam ∈ (Finset.univ.filter (fun lam : Fin 3 → ZMod 2 => lam ≠ 0)), (d - 1) := by
        refine Finset.sum_le_sum fun lam hlam => ?_
        have hne := (Finset.mem_filter.mp hlam).2
        have hr1 : (Q lam).roots.toFinset.card ≤ (Q lam).roots.card := Multiset.toFinset_card_le _
        have hr2 : (Q lam).roots.card ≤ (Q lam).natDegree := Polynomial.card_roots' _
        exact hr1.trans (hr2.trans (hQ_deg lam))
      have h3 : (Finset.univ.filter (fun lam : Fin 3 → ZMod 2 => lam ≠ 0)).card = 7 := by decide
      simp only [Finset.sum_const, smul_eq_mul, h3] at h2
      exact h1.trans h2
    have h2Bad : 2 * Bad.card ≤ 2 ^ s := by
      have h14 : 14 * (d - 1) * s < 14 * k := by
        have : 14 * (d - 1) * s = 14 * ((d - 1) * s) := by ring
        rw [this]
        exact Nat.mul_lt_mul_of_pos_left hds_sub_lt (by norm_num)
      have hlt : 14 * (d - 1) * s < s * 2 ^ s := lt_of_lt_of_le h14 hs_ge
      have hdiv : 14 * (d - 1) < 2 ^ s := by
        nlinarith
      omega
    let Good : Finset (GaloisField 2 s) := Finset.univ \ Bad
    have h2Good : 2 ^ s ≤ 2 * Good.card := by
      have hsub : Bad ⊆ Finset.univ := Finset.subset_univ Bad
      have hcard : Good.card = Fintype.card (GaloisField 2 s) - Bad.card := Finset.card_sdiff_of_subset hsub
      rw [hKcard] at hcard
      omega
    have hGood_hits : ∀ u ∈ Good, iw.m ≤ 64 * (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card := by
      intro u hu
      have hu_not : u ∉ Bad := (Finset.mem_sdiff.mp hu).2
      let Bu : GaloisField 2 s →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
        { toFun := fun w c => Algebra.trace (ZMod 2) (GaloisField 2 s) ((P c).eval u * w)
          map_add' := fun w₁ w₂ => by ext c; simp [mul_add]
          map_smul' := fun r w => by ext c; simp [Algebra.mul_smul_comm] }
      have hBu_surj : Function.Surjective Bu := by
        by_contra hns
        have hne_top : LinearMap.range Bu ≠ ⊤ := fun htop => hns (LinearMap.range_eq_top.mp htop)
        obtain ⟨lam, hlam_ne, hlam_orth⟩ := exists_lam_of_proper (LinearMap.range Bu) hne_top
        have hlam_zero : ∀ w : GaloisField 2 s,
            Algebra.trace (ZMod 2) (GaloisField 2 s)
              ((∑ c : Fin 3, if lam c = 1 then (P c).eval u else 0) * w) = 0 := by
          intro w
          have ho := hlam_orth (Bu w) (LinearMap.mem_range_self Bu w)
          rw [Finset.sum_mul, map_sum]
          rw [← ho]
          refine Finset.sum_congr rfl fun c _ => ?_
          rcases zmod2_cases (lam c) with hc0 | hc1
          · simp [hc0]
          · simp [hc1, Bu]
        have hsum_zero : (∑ c : Fin 3, if lam c = 1 then (P c).eval u else 0) = 0 := by
          by_contra hnz
          obtain ⟨w, hw⟩ := trace_nondeg s hnz
          exact hw (hlam_zero w)
        have hQu : (Q lam).eval u = 0 := by
          simp only [Q, Polynomial.eval_finsetSum]
          refine (Finset.sum_congr rfl fun c _ => ?_).trans hsum_zero
          by_cases h1 : lam c = 1 <;> simp [h1]
        have hmem_bad : u ∈ Bad := by
          simp only [Bad, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
            Multiset.mem_toFinset]
          exact ⟨lam, hlam_ne, (Polynomial.mem_roots (hQ_ne lam hlam_ne)).mpr hQu⟩
        exact hu_not hmem_bad
      have hiw := iw.hw_equi Bu hBu_surj z
      have heq_f : ∀ i : Fin iw.m, A (mask (eM (u, i))) = Bu (iw.w i) := by
        intro i
        ext c
        exact hAmask u i c
      simpa [heq_f] using hiw
    have hsum_good : Good.card * iw.m ≤ 64 * ∑ u ∈ Good,
        (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card := by
      rw [Finset.mul_sum]
      calc Good.card * iw.m
          = ∑ _u ∈ Good, iw.m := by simp [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ u ∈ Good, 64 * (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card :=
            Finset.sum_le_sum hGood_hits
    have hsum_le_all : ∑ u ∈ Good,
        (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card ≤
        (Finset.univ.filter (fun j : Fin M => A (mask j) = z)).card := by
      have h1 : ∑ u ∈ Good, (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card ≤
          ∑ u : GaloisField 2 s, (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      have h2 : ∑ u : GaloisField 2 s, (Finset.univ.filter (fun i : Fin iw.m => A (mask (eM (u, i))) = z)).card =
          (Finset.univ.filter (fun p : GaloisField 2 s × Fin iw.m => A (mask (eM p)) = z)).card := by
        rw [Finset.card_filter, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.card_filter]
      have h3 : (Finset.univ.filter (fun p : GaloisField 2 s × Fin iw.m => A (mask (eM p)) = z)).card =
          (Finset.univ.filter (fun j : Fin M => A (mask j) = z)).card := by
        refine Finset.card_bij (fun p _ => eM p) ?_ ?_ ?_
        · intro p hp
          simpa using (Finset.mem_filter.mp hp).2
        · intro p₁ _ p₂ _ h
          exact eM.injective h
        · intro j hj
          exact ⟨eM.symm j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hj).2⟩,
            by simp⟩
      omega
    dsimp only [M]
    nlinarith
  · dsimp only [C, Circuit.size]
    have h1 : r0.1.length = 2 := hr0.2.2.1
    have h2 : dec.1.length ≤ r0.1.length + (128 * (s * s) + s) := hdec.2.2.1
    have h3 : horner.1.length ≤ dec.1.length + (d - 1) * (13 * (s * s) + 4 * s) := hhorner.2.2.1
    have h4 : finalMul.1.length ≤ horner.1.length + 13 * (s * s) := hfm.2.2.1
    have h5 : out.1.length ≤ finalMul.1.length + 4 * trWS.length := hout.2.2.1
    have htr_len : trWS.length ≤ s := by
      dsimp only [trWS]
      rw [List.length_map]
      exact (List.length_filter_le _ _).trans (by simp)
    have hsz : out.1.length ≤ 2 + 128 * (s * s) + s + d * (13 * (s * s) + 4 * s) + 4 * s := by
      have hd1 : (d - 1) * (13 * (s * s) + 4 * s) + 13 * (s * s) ≤ d * (13 * (s * s) + 4 * s) := by
        have : d = (d - 1) + 1 := by omega
        conv_rhs => rw [this, add_mul, one_mul]
        omega
      omega
    have hds_k : d * (13 * (s * s) + 4 * s) ≤ 2 * k * (13 * s + 4) := by
      calc d * (13 * (s * s) + 4 * s)
          = (d * s) * (13 * s + 4) := by ring
        _ ≤ (2 * k) * (13 * s + 4) := Nat.mul_le_mul_right _ (le_of_lt hds_lt_2k)
    have hss_k : s * s ≤ k * s := Nat.mul_le_mul_right _ (by omega)
    have hs_log2 : s ≤ 2 * (Nat.log2 k + 1) := by
      have h4 : 4 ≤ Nat.log2 k := by
        by_contra hlt
        have := (Nat.log2_lt (by omega : k ≠ 0)).mp (by omega : Nat.log2 k < 4)
        norm_num at this
        omega
      omega
    have hlog1 : 1 ≤ Nat.log2 k + 1 := by omega
    have h128_bound : 128 * (s * s) ≤ 256 * (k * (Nat.log2 k + 1)) := by
      calc 128 * (s * s)
          ≤ 128 * (k * s) := Nat.mul_le_mul_left 128 hss_k
        _ ≤ 128 * (k * (2 * (Nat.log2 k + 1))) := Nat.mul_le_mul_left 128 (Nat.mul_le_mul_left k hs_log2)
        _ = 256 * (k * (Nat.log2 k + 1)) := by ring
    have hds_bound : d * (13 * (s * s) + 4 * s) ≤ 60 * (k * (Nat.log2 k + 1)) := by
      have h13s : 13 * s + 4 ≤ 30 * (Nat.log2 k + 1) := by omega
      calc d * (13 * (s * s) + 4 * s)
          ≤ 2 * k * (13 * s + 4) := hds_k
        _ ≤ 2 * k * (30 * (Nat.log2 k + 1)) := Nat.mul_le_mul_left (2 * k) h13s
        _ = 60 * (k * (Nat.log2 k + 1)) := by ring
    have hs5_bound : 5 * s ≤ 10 * (k * (Nat.log2 k + 1)) := by
      have hle_k : 10 * (Nat.log2 k + 1) ≤ 10 * (k * (Nat.log2 k + 1)) :=
        Nat.mul_le_mul_left 10 (Nat.le_mul_of_pos_left (Nat.log2 k + 1) (by omega))
      omega
    have h2_bound : 2 ≤ 2 * (k * (Nat.log2 k + 1)) := by
      have h1_le : 1 ≤ k * (Nat.log2 k + 1) := Nat.mul_pos (by omega) hlog1
      omega
    calc out.1.length
        ≤ 2 + 128 * (s * s) + s + d * (13 * (s * s) + 4 * s) + 4 * s := hsz
      _ = 2 + 128 * (s * s) + d * (13 * (s * s) + 4 * s) + 5 * s := by ring
      _ ≤ 2 * (k * (Nat.log2 k + 1)) + 256 * (k * (Nat.log2 k + 1)) +
            60 * (k * (Nat.log2 k + 1)) + 10 * (k * (Nat.log2 k + 1)) := by omega
      _ ≤ 4000 * k * (Nat.log2 k + 1) := by
          have : 2 * (k * (Nat.log2 k + 1)) + 256 * (k * (Nat.log2 k + 1)) +
              60 * (k * (Nat.log2 k + 1)) + 10 * (k * (Nat.log2 k + 1)) =
              328 * (k * (Nat.log2 k + 1)) := by ring
          rw [this]
          have : 4000 * k * (Nat.log2 k + 1) = 4000 * (k * (Nat.log2 k + 1)) := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ (by norm_num)
  · intro g hg
    exact hout.2.1.2 g hg
  · intro x j
    change (evalGates out.1 (List.ofFn x ++ List.ofFn (address j))).getD out.2 false = _
    set xs := List.ofFn x ++ List.ofFn (address j)
    have hxs_len : xs.length = n := by simp [xs, n]
    obtain ⟨u, i₀, rfl⟩ : ∃ u i₀, eM (u, i₀) = j := ⟨(eM.symm j).1, (eM.symm j).2, by simp⟩
    have hx_in : ∀ idx : Fin k, (evalGates dec.1 xs).getD idx.val false = x idx := by
      intro idx
      rw [evalGates_extends_getD hdec.1 xs (by rw [hxs_len]; dsimp only [n, t]; omega)]
      rw [evalGates_extends_getD hr0.1 xs (by rw [hxs_len]; dsimp only [n, t]; omega)]
      rw [evalGates_getD_lt _ _ (by rw [hxs_len]; dsimp only [n, t]; omega)]
      simp [xs, List.getD_eq_getElem?_getD, List.getElem?_append_left, idx.isLt]
    have hu_in : ∀ q : Fin s, b2z ((evalGates dec.1 xs).getD (uWires q) false) = b.repr u q := by
      intro q
      rw [evalGates_extends_getD hdec.1 xs (by rw [hxs_len]; exact hu_lt q)]
      rw [evalGates_extends_getD hr0.1 xs (by rw [hxs_len]; dsimp only [uWires, n, t]; omega)]
      rw [evalGates_getD_lt _ _ (by rw [hxs_len]; dsimp only [uWires, n, t]; omega)]
      have helem : xs.getD (k + q.val) false = address (eM (u, i₀)) ⟨q.val, by omega⟩ := by
        dsimp only [xs]
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp), List.length_ofFn,
          Nat.add_sub_cancel_left, List.getElem?_ofFn]
        simp only [show q.val < t by omega, ↓reduceDIte]
        rfl
      dsimp only [uWires]
      rw [helem]
      have haddr : address (eM (u, i₀)) ⟨q.val, by omega⟩ = decide (b.repr u q = 1) := by
        change addrPair (eM.symm (eM (u, i₀))) ⟨q.val, by omega⟩ = _
        rw [eM.symm_apply_apply]
        dsimp only [addrPair]
        simp only [q.isLt, ↓reduceDIte]
      rw [haddr]
      rcases zmod2_cases (b.repr u q) with hq0 | hq1
      · simp [hq0, b2z]
      · simp [hq1, b2z]
    have hy_in : ∀ q : Fin iw.t_w, (evalGates r0.1 xs).getD (yWires q) false = iw.addr_w i₀ q := by
      intro q
      rw [evalGates_extends_getD hr0.1 xs (by rw [hxs_len]; dsimp only [yWires, n, t]; omega)]
      rw [evalGates_getD_lt _ _ (by rw [hxs_len]; dsimp only [yWires, n, t]; omega)]
      have helem : xs.getD (k + s + q.val) false = address (eM (u, i₀)) ⟨s + q.val, by omega⟩ := by
        dsimp only [xs]
        rw [List.getD_eq_getElem?_getD, add_assoc, List.getElem?_append_right (by simp), List.length_ofFn,
          Nat.add_sub_cancel_left, List.getElem?_ofFn]
        simp only [show s + q.val < t by omega, ↓reduceDIte]
        rfl
      dsimp only [yWires]
      rw [helem]
      change addrPair (eM.symm (eM (u, i₀))) ⟨s + q.val, by omega⟩ = _
      rw [eM.symm_apply_apply]
      dsimp only [addrPair]
      have hns : ¬ (s + q.val < s) := by omega
      simp only [hns, ↓reduceDIte, Nat.add_sub_cancel_left, Fin.eta]
    have hdec_val : ∀ c : Fin s, b2z ((evalGates dec.1 xs).getD (dec.2 c) false) = b.repr (iw.w i₀) c :=
      hdec.2.2.2.2 xs i₀ hxs_len hy_in
    exact large_eval_correct k s d t hs0 hd_pos hk_le_ds b iw toBits (fun _ _ => rfl)
      (fun p => mask (eM p))
      (fun u' i' idx => by
        change maskPair (eM.symm (eM (u', i'))) idx = _
        rw [eM.symm_apply_apply]
        rfl)
      r0.2 uWires dec.2 horner.2 finalMul.2 xPad rem hrem
      dec.1 horner.1 finalMul.1 out.1 out.2 trWS rfl xs hxs_len u i₀ x
      hx_in hu_in hdec_val (hhz_dec xs hxs_len) (fun _ _ => rfl) hhorner.1
      hdec.2.2.2.1 (hhorner.2.2.2.2 xs hxs_len) (fun c => hfm.2.2.2.2 c xs hxs_len)
      (hout.2.2.2.2 xs hxs_len)

end PEqualNP.Outside.L_meta_25893

theorem PEqualNP.Outside.L_meta_25893 : (∀ k : ℕ, 4 ≤ k →
  let F := ZMod 2
  let V := Fin k → F
  ∃ (M t : ℕ) (mask : Fin M ↪ V) (address : Fin M ↪ (Fin t → Bool))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
    0 < M ∧ M ≤ 8960*k ∧ 2^t ≤ 2*M ∧
    (∀ (A : V →ₗ[F] (Fin 3 → F)), Function.Surjective A → ∀ z : Fin 3 → F,
      M ≤ 128*((Finset.univ : Finset (Fin M)).filter (fun j => A (mask j) = z)).card) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (k+t) C ∧
    C.output < k+t+C.size ∧ C.size ≤ 4000*k*(Nat.log2 k+1) ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2 ∧
      (g.op = .and ∨ g.op = .or ∨ (g.op = .not ∧ g.inputs.length = 1))) ∧
    ∀ (x : Fin k → Bool) (j : Fin M),
      C.eval (List.ofFn x ++ List.ofFn (address j)) =
        decide ((∑ i : Fin k, (if x i then (1 : F) else 0) * mask j i) = 1)) := by
  intro k hk
  by_cases hk17 : k ≤ 17
  · exact PEqualNP.Outside.L_meta_25893.small_case k hk hk17
  · exact PEqualNP.Outside.L_meta_25893.large_case k (by omega)
