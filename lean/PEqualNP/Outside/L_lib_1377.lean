import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1377_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section TraceFacts

def swOf {n : ℕ} (f : Fin (n + 1) → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun s : Fin n => f s.castSucc ≠ f s.succ)

def traceFn {n : ℕ} (S : Finset (Fin n)) (x : Bool) (t : Fin (n + 1)) : Bool :=
  Bool.xor x (decide ((S.filter (fun s => s.val < t.val)).card % 2 = 1))

theorem filter_lt_succ {n : ℕ} (S : Finset (Fin n)) (s : Fin n) :
    S.filter (fun u : Fin n => u.val < s.succ.val) =
    if s ∈ S then insert s (S.filter (fun u : Fin n => u.val < s.castSucc.val))
    else S.filter (fun u : Fin n => u.val < s.castSucc.val) := by
  ext u
  by_cases hs : s ∈ S <;> simp only [hs, ite_true, ite_false, Finset.mem_filter, Finset.mem_insert,
    Fin.val_succ, Fin.val_castSucc]
  · constructor
    · rintro ⟨huS, hlt⟩
      by_cases hus : u = s
      · exact Or.inl hus
      · right
        have hne : u.val ≠ s.val := fun h => hus (Fin.ext h)
        exact ⟨huS, by omega⟩
    · rintro (rfl | ⟨huS, hlt⟩)
      · exact ⟨hs, by omega⟩
      · exact ⟨huS, by omega⟩
  · constructor
    · rintro ⟨huS, hlt⟩
      have hne : u.val ≠ s.val := fun h => hs (Fin.ext h ▸ huS)
      exact ⟨huS, by omega⟩
    · rintro ⟨huS, hlt⟩
      exact ⟨huS, by omega⟩

theorem traceFn_step {n : ℕ} (S : Finset (Fin n)) (x : Bool) (s : Fin n) :
    traceFn S x s.succ = Bool.xor (traceFn S x s.castSucc) (decide (s ∈ S)) := by
  unfold traceFn
  rw [filter_lt_succ]
  by_cases hs : s ∈ S
  · have hnot : s ∉ S.filter (fun u : Fin n => u.val < s.castSucc.val) := by
      simp [Fin.val_castSucc]
    simp only [hs, ite_true, decide_true, Finset.card_insert_of_notMem hnot]
    cases x <;> generalize (S.filter (fun u : Fin n => u.val < s.castSucc.val)).card = c <;>
      rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [Nat.add_mod, h]
  · simp [hs]

theorem traceFn_zero {n : ℕ} (S : Finset (Fin n)) (x : Bool) :
    traceFn S x 0 = x := by
  have hempty : S.filter (fun s : Fin n => s.val < (0 : Fin (n + 1)).val) = ∅ := by
    ext u; simp
  simp [traceFn, hempty]

theorem swOf_traceFn {n : ℕ} (S : Finset (Fin n)) (x : Bool) :
    swOf (traceFn S x) = S := by
  ext s
  simp only [swOf, Finset.mem_filter, Finset.mem_univ, true_and, traceFn_step]
  by_cases hs : s ∈ S
  · simp only [hs, decide_true, iff_true]
    cases traceFn S x s.castSucc <;> decide
  · simp [hs]

theorem eq_traceFn_swOf {n : ℕ} (f : Fin (n + 1) → Bool) (t : Fin (n + 1)) :
    f t = traceFn (swOf f) (f 0) t := by
  rcases t with ⟨k, hk⟩
  induction k with
  | zero =>
    change f 0 = traceFn (swOf f) (f 0) 0
    rw [traceFn_zero]
  | succ k ih =>
    let s : Fin n := ⟨k, by omega⟩
    have h1 : (⟨k + 1, hk⟩ : Fin (n + 1)) = s.succ := by ext; rfl
    have h0 : (⟨k, by omega⟩ : Fin (n + 1)) = s.castSucc := by ext; rfl
    rw [h1, traceFn_step, ← h0, ← ih (by omega)]
    by_cases hneq : f s.castSucc ≠ f s.succ
    · have hmem : s ∈ swOf f := by simp [swOf, hneq]
      simp only [hmem, decide_true, h0]
      cases hfc : f s.castSucc <;> cases hfs : f s.succ <;> simp_all
    · push_neg at hneq
      have hmem : s ∉ swOf f := by simp [swOf, hneq]
      simp [hmem, h0, hneq]

theorem swOf_not {n : ℕ} (f : Fin (n + 1) → Bool) :
    swOf (fun t => !(f t)) = swOf f := by
  ext s
  simp [swOf]

theorem swOf_const {n : ℕ} (c : Bool) : swOf (fun _ : Fin (n + 1) => c) = ∅ := by
  ext s; simp [swOf]

theorem swOf_input {n : ℕ} (j : Fin n) :
    swOf (fun t : Fin (n + 1) => decide (j.val < t.val)) = {j} := by
  ext s
  simp only [swOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Fin.val_castSucc, Fin.val_succ]
  constructor
  · intro hne
    have : s.val = j.val := by
      by_contra h
      have h1 : decide (j.val < s.val) = decide (j.val < s.val + 1) := by
        apply Bool.eq_iff_iff.mpr; simp; omega
      exact hne h1
    exact Fin.ext this
  · rintro rfl
    have h1 : decide (s.val < s.val) = false := by simp
    have h2 : decide (s.val < s.val + 1) = true := by simp
    rw [h1, h2]
    decide

theorem input_eq_traceFn {n : ℕ} (j : Fin n) (t : Fin (n + 1)) :
    decide (j.val < t.val) = traceFn {j} false t := by
  have h := eq_traceFn_swOf (fun u : Fin (n + 1) => decide (j.val < u.val)) t
  rw [swOf_input] at h
  simpa using h

end TraceFacts

section WireEval
open scoped Classical

def pref (n : ℕ) (t : Fin (n + 1)) : List Bool :=
  List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false, true]

def wval (n : ℕ) (gs : List Gate) (w : ℕ) (t : Fin (n + 1)) : Bool :=
  ((Circuit.mk gs 0).wires (pref n t)).getD w false

noncomputable def posCount (gs : List Gate) : ℕ :=
  (gs.filter (fun g => decide (g.op ≠ GateOp.not))).length

theorem posCount_append (gs : List Gate) (g : Gate) :
    posCount (gs ++ [g]) = posCount gs + if g.op = GateOp.not then 0 else 1 := by
  unfold posCount
  by_cases h : g.op = GateOp.not <;> simp [List.filter_append, h]

theorem notCount_append (gs : List Gate) (g : Gate) :
    PEqualNP.NotBracket.notCount ⟨gs ++ [g], 0⟩ =
      PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + if g.op = GateOp.not then 1 else 0 := by
  unfold PEqualNP.NotBracket.notCount
  by_cases h : g.op = GateOp.not <;> simp [List.filter_append, h]

theorem posCount_add_notCount (gs : List Gate) :
    posCount gs + PEqualNP.NotBracket.notCount ⟨gs, 0⟩ = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [posCount, PEqualNP.NotBracket.notCount]
  | append_singleton gs g ih =>
    rw [posCount_append, notCount_append, List.length_append, List.length_singleton]
    by_cases h : g.op = GateOp.not <;> simp [h] <;> omega

theorem size_sub_notCount (C : Circuit) :
    C.size - PEqualNP.NotBracket.notCount C = posCount C.gates := by
  have h := posCount_add_notCount C.gates
  change C.gates.length - PEqualNP.NotBracket.notCount ⟨C.gates, 0⟩ = posCount C.gates
  omega

theorem wirelen (gs : List Gate) (u : List Bool) :
    ((Circuit.mk gs 0).wires u).length = u.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton gs g ih =>
    simpa [Circuit.wires, List.foldl_append, Nat.add_assoc] using congrArg Nat.succ ih

theorem pref_length (n : ℕ) (t : Fin (n + 1)) : (pref n t).length = n + 2 := by
  simp [pref]

theorem wval_append_old (n : ℕ) (gs : List Gate) (g : Gate) {w : ℕ} (hw : w < n + 2 + gs.length)
    (t : Fin (n + 1)) : wval n (gs ++ [g]) w t = wval n gs w t := by
  have len := wirelen gs (pref n t)
  rw [pref_length] at len
  simp only [wval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (pref n t)) ++ [_]).getD w false = _
  exact List.getD_append _ _ _ _ (by omega)

theorem wval_append_prefix (n : ℕ) (gs extra : List Gate) {w : ℕ} (hw : w < n + 2 + gs.length)
    (t : Fin (n + 1)) : wval n (gs ++ extra) w t = wval n gs w t := by
  induction extra using List.reverseRecOn with
  | nil => simp
  | append_singleton ex g ih =>
    rw [← List.append_assoc, wval_append_old n (gs ++ ex) g (by simp; omega), ih]

theorem wval_append_new (n : ℕ) (gs : List Gate) (g : Gate) (t : Fin (n + 1)) :
    wval n (gs ++ [g]) (n + 2 + gs.length) t = g.op.eval (g.inputs.map fun p => wval n gs p t) := by
  have len := wirelen gs (pref n t)
  rw [pref_length] at len
  simp only [wval, Circuit.wires, List.foldl_append, List.foldl_cons, List.foldl_nil]
  change (((Circuit.mk gs 0).wires (pref n t)) ++ [_]).getD _ false = _
  rw [← len, List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem wval_input (n : ℕ) (gs : List Gate) (j : Fin n) (t : Fin (n + 1)) :
    wval n gs j.val t = decide (j.val < t.val) := by
  rw [show gs = [] ++ gs from rfl, wval_append_prefix n [] gs (by have := j.isLt; simp; omega)]
  simp only [wval, Circuit.wires, List.foldl_nil, pref]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

theorem wval_false (n : ℕ) (gs : List Gate) (t : Fin (n + 1)) :
    wval n gs n t = false := by
  rw [show gs = [] ++ gs from rfl, wval_append_prefix n [] gs (by simp)]
  simp [wval, Circuit.wires, pref]

theorem wval_true (n : ℕ) (gs : List Gate) (t : Fin (n + 1)) :
    wval n gs (n + 1) t = true := by
  rw [show gs = [] ++ gs from rfl, wval_append_prefix n [] gs (by simp)]
  simp [wval, Circuit.wires, pref]

theorem readsBack_lt {n : ℕ} {gs : List Gate} (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {w u : ℕ} (h1 : n + 2 ≤ w) (h2 : w < n + 2 + gs.length)
    (hu : u ∈ (gs[w - (n + 2)]'(by omega)).inputs) : u < w := by
  have hrb := hBack (w - (n + 2)) (by change w - (n + 2) < gs.length; omega) u
  have hga : gateAt ⟨gs, 0⟩ (w - (n + 2)) = gs[w - (n + 2)]'(by omega) := by
    unfold gateAt
    exact List.getD_eq_getElem gs ⟨.or, []⟩ (show w - (n + 2) < gs.length by omega)
  rw [hga] at hrb
  have hu' : u < n + 2 + (w - (n + 2)) := hrb hu
  omega

theorem wval_gate_eval (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (j : ℕ) (hj : j < gs.length) (t : Fin (n + 1)) :
    wval n gs (n + 2 + j) t =
      (gs[j]).op.eval ((gs[j]).inputs.map fun p => wval n gs p t) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 : gs.take (j + 1) = gs.take j ++ [gs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]
      rfl
    rw [← h1, List.take_append_drop]
  have hlen : (gs.take j).length = j := List.length_take_of_le (by omega)
  have h1 : wval n gs (n + 2 + j) t = wval n (gs.take j ++ [gs[j]]) (n + 2 + j) t := by
    conv_lhs => rw [hsplit]
    exact wval_append_prefix n (gs.take j ++ [gs[j]]) (gs.drop (j + 1))
      (by simp only [List.length_append, List.length_singleton, hlen]; omega) t
  rw [h1]
  have h2 : wval n (gs.take j ++ [gs[j]]) (n + 2 + (gs.take j).length) t =
      (gs[j]).op.eval ((gs[j]).inputs.map fun p => wval n (gs.take j) p t) :=
    wval_append_new n (gs.take j) gs[j] t
  rw [hlen] at h2
  rw [h2]
  congr 1
  apply List.map_congr_left
  intro p hp
  have hpLt : p < n + 2 + j := by
    have hrb := hBack j hj p
    have hga : gateAt ⟨gs, 0⟩ j = gs[j] := by
      unfold gateAt
      exact List.getD_eq_getElem gs ⟨.or, []⟩ hj
    rw [hga] at hrb
    exact hrb hp
  conv_rhs => rw [hsplit, List.append_assoc]
  exact (wval_append_prefix n (gs.take j) ([gs[j]] ++ gs.drop (j + 1)) (by omega) t).symm

theorem extendBack (n : ℕ) (gs : List Gate) (g : Gate) (h : ReadsBack (n + 2) ⟨gs, 0⟩)
    (ok : ∀ p ∈ g.inputs, p < n + 2 + gs.length) : ReadsBack (n + 2) ⟨gs ++ [g], 0⟩ := by
  intro j hj p hp
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hj' : j < gs.length
  · apply h j hj' p
    simpa only [gateAt, List.getD_append _ _ _ _ hj'] using hp
  · obtain rfl : j = gs.length := by omega
    apply ok
    simpa [gateAt, List.getD_append_right _ _ _ _ (le_refl _)] using hp

theorem extendFan (gs : List Gate) (g : Gate) (h : FanInTwo ⟨gs, 0⟩)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) (hlen : g.inputs.length ≤ 2) :
    FanInTwo ⟨gs ++ [g], 0⟩ := by
  intro u hu
  rcases List.mem_append.mp hu with hold | hnew
  · exact h u hold
  · obtain rfl := List.mem_singleton.mp hnew
    exact ⟨hop, hlen⟩

end WireEval

section ForwardConstruction

def tollFn {n a : ℕ} (W : Fin (a + 1) → Fin (n + 1) → Bool)
    (S : Finset (Fin n)) (birth want : Bool) : ℕ :=
  if want ≠ birth ∨ (∃ i : Fin (a + 1), swOf (W i) = S ∧ W i 0 ≠ birth) then 1 else 0

def leafFn {n a : ℕ} (W : Fin (a + 1) → Fin (n + 1) → Bool)
    (S : Finset (Fin n)) (z : Bool) (k : ℕ) : Prop :=
  S.card = 1 ∧ tollFn W S false z ≤ k

def treeFn {n a : ℕ} (W : Fin (a + 1) → Fin (n + 1) → Bool) :
    ℕ → Finset (Fin n) → Bool → ℕ → Prop :=
  Nat.rec (motive := fun _ => Finset (Fin n) → Bool → ℕ → Prop) (leafFn W)
    (fun _ child S z k => leafFn W S z k ∨
      ∃ (A B : Finset (Fin n)) (x y op : Bool) (ka kb : Fin (k + 1)),
        A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = S ∧
        (∀ i : Fin (a + 1), swOf (W i) ⊆ S → swOf (W i) ≠ S → swOf (W i) ⊆ A ∨ swOf (W i) ⊆ B) ∧
        let gate := fun (v w : Bool) => if op then (v && w) else (v || w)
        (∀ t, gate (traceFn A x t) (traceFn B y t) = traceFn S (gate x y) t) ∧
        child A x ka.val ∧ child B y kb.val ∧ ka.val + kb.val + tollFn W S (gate x y) z ≤ k)

theorem append_optional_not {n a : ℕ} (W : Fin (a + 1) → Fin (n + 1) → Bool)
    (S : Finset (Fin n)) (birth want : Bool) (gs : List Gate)
    (hFan : FanInTwo ⟨gs, 0⟩) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (p0 : ℕ) (hp0 : p0 < n + 2 + gs.length)
    (hval0 : ∀ t, wval n gs p0 t = traceFn S birth t) :
    ∃ extra : List Gate,
      FanInTwo ⟨gs ++ extra, 0⟩ ∧ ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
      posCount (gs ++ extra) = posCount gs ∧
      PEqualNP.NotBracket.notCount ⟨gs ++ extra, 0⟩ =
        PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + tollFn W S birth want ∧
      (∃ pw < n + 2 + (gs ++ extra).length, ∀ t, wval n (gs ++ extra) pw t = traceFn S want t) ∧
      (∀ i : Fin (a + 1), swOf (W i) = S →
        ∃ pi < n + 2 + (gs ++ extra).length, ∀ t, wval n (gs ++ extra) pi t = W i t) := by
  by_cases ht : want ≠ birth ∨ (∃ i : Fin (a + 1), swOf (W i) = S ∧ W i 0 ≠ birth)
  · have htoll : tollFn W S birth want = 1 := by simp [tollFn, ht]
    let g : Gate := ⟨GateOp.not, [p0]⟩
    refine ⟨[g], extendFan gs g hFan (Or.inr (Or.inr rfl)) (by simp [g]),
      extendBack n gs g hBack (by simpa [g] using hp0),
      by simp [posCount_append, g],
      by simp [notCount_append, g, htoll], ?_, ?_⟩
    · have hnot : ∀ t, wval n (gs ++ [g]) (n + 2 + gs.length) t = traceFn S (!birth) t := by
        intro t
        rw [wval_append_new]
        simp only [g, GateOp.eval, List.map_cons, List.map_nil, hval0 t, traceFn]
        cases birth <;> cases decide ((S.filter fun s => s.val < t.val).card % 2 = 1) <;> rfl
      by_cases hwb : want = birth
      · subst hwb
        exact ⟨p0, by simp; omega, fun t => (wval_append_old n gs g hp0 t).trans (hval0 t)⟩
      · have hwn : want = !birth := by cases want <;> cases birth <;> simp_all
        subst hwn
        exact ⟨n + 2 + gs.length, by simp, hnot⟩
    · intro i hi
      by_cases hwb : W i 0 = birth
      · refine ⟨p0, by simp; omega, fun t => ?_⟩
        rw [wval_append_old n gs g hp0 t, hval0 t, eq_traceFn_swOf (W i) t, hi, hwb]
      · have hwn : W i 0 = !birth := by
          cases h1 : W i 0 <;> cases h2 : birth <;> simp_all
        refine ⟨n + 2 + gs.length, by simp, fun t => ?_⟩
        rw [wval_append_new]
        simp only [g, GateOp.eval, List.map_cons, List.map_nil, hval0 t]
        rw [eq_traceFn_swOf (W i) t, hi, hwn]
        unfold traceFn
        cases birth <;> cases decide ((S.filter fun s => s.val < t.val).card % 2 = 1) <;> rfl
  · have htoll : tollFn W S birth want = 0 := by simp [tollFn, ht]
    have hwb : want = birth := by
      by_contra hne; exact ht (Or.inl hne)
    refine ⟨[], by simpa using hFan, by simpa using hBack, by simp,
      by simp [htoll], ⟨p0, by simpa using hp0, fun t => by simp [hval0 t, hwb]⟩, ?_⟩
    intro i hi
    have hi0 : W i 0 = birth := by
      by_contra hne; exact ht (Or.inr ⟨i, hi, hne⟩)
    refine ⟨p0, by simpa using hp0, fun t => ?_⟩
    simp only [List.append_nil]
    rw [hval0 t, eq_traceFn_swOf (W i) t, hi, hi0]

theorem build_from_tree {n a : ℕ} (W : Fin (a + 1) → Fin (n + 1) → Bool) (d : ℕ) :
    ∀ (S : Finset (Fin n)) (z : Bool) (k : ℕ) (gs : List Gate),
      FanInTwo ⟨gs, 0⟩ → ReadsBack (n + 2) ⟨gs, 0⟩ →
      treeFn W d S z k →
      ∃ extra : List Gate,
        FanInTwo ⟨gs ++ extra, 0⟩ ∧ ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
        posCount (gs ++ extra) ≤ posCount gs + (S.card - 1) ∧
        PEqualNP.NotBracket.notCount ⟨gs ++ extra, 0⟩ ≤
          PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + k ∧
        (∃ pz < n + 2 + (gs ++ extra).length, ∀ t, wval n (gs ++ extra) pz t = traceFn S z t) ∧
        (∀ i : Fin (a + 1), swOf (W i) ⊆ S → (swOf (W i)).Nonempty →
          ∃ pi < n + 2 + (gs ++ extra).length, ∀ t, wval n (gs ++ extra) pi t = W i t) := by
  have build_leaf : ∀ (S : Finset (Fin n)) (z : Bool) (k : ℕ) (gs : List Gate),
      FanInTwo ⟨gs, 0⟩ → ReadsBack (n + 2) ⟨gs, 0⟩ → leafFn W S z k →
      ∃ extra : List Gate,
        FanInTwo ⟨gs ++ extra, 0⟩ ∧ ReadsBack (n + 2) ⟨gs ++ extra, 0⟩ ∧
        posCount (gs ++ extra) ≤ posCount gs + (S.card - 1) ∧
        PEqualNP.NotBracket.notCount ⟨gs ++ extra, 0⟩ ≤
          PEqualNP.NotBracket.notCount ⟨gs, 0⟩ + k ∧
        (∃ pz < n + 2 + (gs ++ extra).length, ∀ t, wval n (gs ++ extra) pz t = traceFn S z t) ∧
        (∀ i : Fin (a + 1), swOf (W i) ⊆ S → (swOf (W i)).Nonempty →
          ∃ pi < n + 2 + (gs ++ extra).length, ∀ t, wval n (gs ++ extra) pi t = W i t) := by
    intro S z k gs hFan hBack ⟨hcard, htoll⟩
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hcard
    have hval0 : ∀ t, wval n gs j.val t = traceFn {j} false t := fun t => by
      rw [wval_input, input_eq_traceFn]
    obtain ⟨extra, hF', hB', hPos, hNot, hPz, hTap⟩ :=
      append_optional_not W {j} false z gs hFan hBack j.val (by have := j.isLt; omega) hval0
    refine ⟨extra, hF', hB', by omega, by omega, hPz, ?_⟩
    intro i hsub hne
    have heq : swOf (W i) = {j} := by
      rcases hne with ⟨u, hu⟩
      have huj : u = j := Finset.mem_singleton.mp (hsub hu)
      subst huj
      exact Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hu)
    exact hTap i heq
  induction d with
  | zero => exact build_leaf
  | succ d ih =>
    intro S z k gs hFan hBack hTree
    rcases hTree with hLeaf | ⟨A, B, x, y, op, ka, kb, hAne, hBne, hDisj, hUn, hSplit, hGate, hA, hB, hSum⟩
    · exact build_leaf S z k gs hFan hBack hLeaf
    · obtain ⟨exA, hFanA, hBackA, hPosA, hNotA, ⟨pA, hpA, hvalA⟩, hTapA⟩ :=
        ih A x ka.val gs hFan hBack hA
      obtain ⟨exB, hFanB, hBackB, hPosB, hNotB, ⟨pB, hpB, hvalB⟩, hTapB⟩ :=
        ih B y kb.val (gs ++ exA) hFanA hBackA hB
      let gs2 := gs ++ exA ++ exB
      have hpA2 : pA < n + 2 + gs2.length := by
        simp only [gs2, List.length_append] at *
        omega
      have hvalA2 : ∀ t, wval n gs2 pA t = traceFn A x t := fun t => by
        rw [wval_append_prefix n (gs ++ exA) exB hpA t, hvalA t]
      let gpos : Gate := ⟨if op then GateOp.and else GateOp.or, [pA, pB]⟩
      have hFan3 : FanInTwo ⟨gs2 ++ [gpos], 0⟩ :=
        extendFan gs2 gpos hFanB (by cases op <;> simp [gpos]) (by simp [gpos])
      have hBack3 : ReadsBack (n + 2) ⟨gs2 ++ [gpos], 0⟩ :=
        extendBack n gs2 gpos hBackB (by intro p hp; simp [gpos] at hp; rcases hp with rfl | rfl <;> omega)
      have hvalS : ∀ t, wval n (gs2 ++ [gpos]) (n + 2 + gs2.length) t =
          traceFn S (if op then x && y else x || y) t := by
        intro t
        rw [wval_append_new]
        have hg := hGate t
        cases op
        · simp only [gpos, Bool.false_eq_true, ite_false, GateOp.eval, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, Bool.or_false, id_eq]
          rw [hvalA2 t]
          dsimp only [gs2]
          rw [hvalB t]
          simpa using hg
        · simp only [gpos, ite_true, GateOp.eval, List.map_cons, List.map_nil,
            List.all_cons, List.all_nil, Bool.and_true, id_eq]
          rw [hvalA2 t]
          dsimp only [gs2]
          rw [hvalB t]
          simpa using hg
      obtain ⟨exN, hFan4, hBack4, hPos4, hNot4, hPz, hTapS⟩ :=
        append_optional_not W S (if op then x && y else x || y) z (gs2 ++ [gpos])
          hFan3 hBack3 (n + 2 + gs2.length) (by simp) hvalS
      have hcardS : S.card = A.card + B.card := by
        rw [← hUn, Finset.card_union_of_disjoint hDisj]
      have hApos : 1 ≤ A.card := Finset.Nonempty.card_pos hAne
      have hBpos : 1 ≤ B.card := Finset.Nonempty.card_pos hBne
      have hgopNot : gpos.op ≠ GateOp.not := by cases op <;> simp [gpos]
      have hPos3 : posCount (gs2 ++ [gpos]) = posCount gs2 + 1 := by
        simp [posCount_append, hgopNot]
      have hNot3 : PEqualNP.NotBracket.notCount ⟨gs2 ++ [gpos], 0⟩ =
          PEqualNP.NotBracket.notCount ⟨gs2, 0⟩ := by
        simp [notCount_append, hgopNot]
      refine ⟨exA ++ exB ++ [gpos] ++ exN, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [gs2, List.append_assoc] using hFan4
      · simpa [gs2, List.append_assoc] using hBack4
      · have heqL : gs ++ (exA ++ exB ++ [gpos] ++ exN) = gs2 ++ [gpos] ++ exN := by
          simp [gs2, List.append_assoc]
        rw [heqL, hPos4, hPos3]
        dsimp only [gs2] at hPosB ⊢
        omega
      · have heqL : gs ++ (exA ++ exB ++ [gpos] ++ exN) = gs2 ++ [gpos] ++ exN := by
          simp [gs2, List.append_assoc]
        rw [heqL, hNot4, hNot3]
        dsimp only [gs2] at hNotB ⊢
        dsimp only at hSum
        omega
      · simpa [gs2, List.append_assoc] using hPz
      · intro i hsub hne
        have heqList : gs ++ (exA ++ exB ++ [gpos] ++ exN) = gs2 ++ [gpos] ++ exN := by
          simp [gs2, List.append_assoc]
        rw [heqList]
        by_cases hiS : swOf (W i) = S
        · exact hTapS i hiS
        · rcases hSplit i hsub hiS with hsubA | hsubB
          · obtain ⟨pi, hpi, hvali⟩ := hTapA i hsubA hne
            refine ⟨pi, by simp only [gs2, List.length_append] at *; omega, fun t => ?_⟩
            have h1 : gs2 ++ [gpos] ++ exN = (gs ++ exA) ++ (exB ++ [gpos] ++ exN) := by
              simp [gs2, List.append_assoc]
            rw [h1, wval_append_prefix n (gs ++ exA) (exB ++ [gpos] ++ exN) hpi t, hvali t]
          · obtain ⟨pi, hpi, hvali⟩ := hTapB i hsubB hne
            refine ⟨pi, by simp only [gs2, List.length_append] at *; omega, fun t => ?_⟩
            have h1 : gs2 ++ [gpos] ++ exN = gs2 ++ ([gpos] ++ exN) := by
              simp [List.append_assoc]
            rw [h1, wval_append_prefix n gs2 ([gpos] ++ exN) hpi t, hvali t]

end ForwardConstruction

section BackwardExtraction
open scoped Classical

noncomputable def isPosWire (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  if h : n + 2 ≤ w ∧ w < n + 2 + gs.length then
    decide ((gs[w - (n + 2)]'(by omega)).op ≠ GateOp.not)
  else
    false

noncomputable def isNotWire (n : ℕ) (gs : List Gate) (w : ℕ) : Bool :=
  if h : n + 2 ≤ w ∧ w < n + 2 + gs.length then
    decide ((gs[w - (n + 2)]'(by omega)).op = GateOp.not)
  else
    false

noncomputable def posWires (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.range (n + 2 + gs.length)).filter (fun w => isPosWire n gs w = true)

noncomputable def notWires (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.range (n + 2 + gs.length)).filter (fun w => isNotWire n gs w = true)

noncomputable def skelWires (n : ℕ) (gs : List Gate) : Finset ℕ :=
  Finset.range n ∪ posWires n gs

theorem mem_posWires {n : ℕ} {gs : List Gate} {w : ℕ} :
    w ∈ posWires n gs ↔ ∃ (h1 : n + 2 ≤ w) (h2 : w < n + 2 + gs.length),
      (gs[w - (n + 2)]'(by omega)).op ≠ GateOp.not := by
  unfold posWires
  rw [Finset.mem_filter, Finset.mem_range]
  unfold isPosWire
  constructor
  · rintro ⟨hw, hpos⟩
    split_ifs at hpos with h
    exact ⟨h.1, h.2, by simpa using hpos⟩
  · rintro ⟨h1, h2, hne⟩
    refine ⟨h2, ?_⟩
    have h : n + 2 ≤ w ∧ w < n + 2 + gs.length := ⟨h1, h2⟩
    simp [h, hne]

theorem mem_notWires {n : ℕ} {gs : List Gate} {w : ℕ} :
    w ∈ notWires n gs ↔ ∃ (h1 : n + 2 ≤ w) (h2 : w < n + 2 + gs.length),
      (gs[w - (n + 2)]'(by omega)).op = GateOp.not := by
  unfold notWires
  rw [Finset.mem_filter, Finset.mem_range]
  unfold isNotWire
  constructor
  · rintro ⟨hw, hnot⟩
    split_ifs at hnot with h
    exact ⟨h.1, h.2, by simpa using hnot⟩
  · rintro ⟨h1, h2, heq⟩
    refine ⟨h2, ?_⟩
    have h : n + 2 ≤ w ∧ w < n + 2 + gs.length := ⟨h1, h2⟩
    simp [h, heq]

theorem posWires_card (n : ℕ) (gs : List Gate) : (posWires n gs).card = posCount gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    have hempty : posWires n [] = ∅ := by
      ext w; rw [mem_posWires]; simp; omega
    simp [hempty, posCount]
  | append_singleton gs g ih =>
    have hset : posWires n (gs ++ [g]) =
        if g.op = GateOp.not then posWires n gs else insert (n + 2 + gs.length) (posWires n gs) := by
      ext w
      by_cases hg : g.op = GateOp.not
      · simp only [hg, ite_true, mem_posWires]
        constructor
        · rintro ⟨h1, h2, hne⟩
          simp only [List.length_append, List.length_singleton] at h2
          have hlt : w < n + 2 + gs.length := by
            by_contra hge
            have hwEq : w - (n + 2) = gs.length := by omega
            have : ((gs ++ [g])[w - (n + 2)]'(by simp; omega)).op = g.op := by
              simp [hwEq]
            exact hne (this.trans hg)
          refine ⟨h1, hlt, ?_⟩
          simpa [List.getElem_append_left (show w - (n + 2) < gs.length by omega)] using hne
        · rintro ⟨h1, h2, hne⟩
          refine ⟨h1, by simp; omega, ?_⟩
          simpa [List.getElem_append_left (show w - (n + 2) < gs.length by omega)] using hne
      · simp only [hg, ite_false, Finset.mem_insert, mem_posWires]
        constructor
        · rintro ⟨h1, h2, hne⟩
          simp only [List.length_append, List.length_singleton] at h2
          by_cases hlast : w = n + 2 + gs.length
          · exact Or.inl hlast
          · right
            have hlt : w < n + 2 + gs.length := by omega
            refine ⟨h1, hlt, ?_⟩
            simpa [List.getElem_append_left (show w - (n + 2) < gs.length by omega)] using hne
        · rintro (rfl | ⟨h1, h2, hne⟩)
          · refine ⟨by omega, by simp, ?_⟩
            simpa using hg
          · refine ⟨h1, by simp; omega, ?_⟩
            simpa [List.getElem_append_left (show w - (n + 2) < gs.length by omega)] using hne
    rw [hset, posCount_append]
    by_cases hg : g.op = GateOp.not
    · simp [hg, ih]
    · have hnotMem : n + 2 + gs.length ∉ posWires n gs := by
        rw [mem_posWires]; rintro ⟨_, h2, _⟩; omega
      simp [hg, Finset.card_insert_of_notMem hnotMem, ih]

theorem notWires_card (n : ℕ) (gs : List Gate) :
    (notWires n gs).card = PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  have h1 : (posWires n gs ∪ notWires n gs).card = gs.length := by
    have heq : posWires n gs ∪ notWires n gs = (Finset.range gs.length).image (fun j => n + 2 + j) := by
      ext w
      rw [Finset.mem_union, mem_posWires, mem_notWires, Finset.mem_image]
      constructor
      · rintro (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)
        · exact ⟨w - (n + 2), Finset.mem_range.mpr (by omega), by omega⟩
        · exact ⟨w - (n + 2), Finset.mem_range.mpr (by omega), by omega⟩
      · rintro ⟨j, hj, rfl⟩
        have hj' : j < gs.length := Finset.mem_range.mp hj
        by_cases hop : (gs[j]'hj').op = GateOp.not
        · right; refine ⟨by omega, by omega, ?_⟩; simpa using hop
        · left; refine ⟨by omega, by omega, ?_⟩; simpa using hop
    rw [heq, Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  have hdisj : Disjoint (posWires n gs) (notWires n gs) := by
    rw [Finset.disjoint_left]
    intro w hp hn
    rw [mem_posWires] at hp
    rw [mem_notWires] at hn
    rcases hp with ⟨_, _, hne⟩
    rcases hn with ⟨_, _, heq⟩
    exact hne heq
  rw [Finset.card_union_of_disjoint hdisj, posWires_card] at h1
  have h2 := posCount_add_notCount gs
  omega

noncomputable def rootOf (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) : ℕ → ℕ :=
  WellFounded.fix (measure id).wf fun w ih =>
    if h : n + 2 ≤ w ∧ w < n + 2 + gs.length then
      if (gs[w - (n + 2)]'(by omega)).op = GateOp.not then
        match hargs : (gs[w - (n + 2)]'(by omega)).inputs with
        | [] => w
        | u :: _ =>
          have hu : u < w := readsBack_lt hBack h.1 h.2 (by simp [hargs])
          ih u hu
      else w
    else w

theorem rootOf_eq (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (w : ℕ) :
    rootOf n gs hBack w =
    if h : n + 2 ≤ w ∧ w < n + 2 + gs.length then
      if (gs[w - (n + 2)]'(by omega)).op = GateOp.not then
        match (gs[w - (n + 2)]'(by omega)).inputs with
        | [] => w
        | u :: _ => rootOf n gs hBack u
      else w
    else w := by
  conv_lhs => unfold rootOf
  rw [WellFounded.fix_eq]
  by_cases h : n + 2 ≤ w ∧ w < n + 2 + gs.length
  · rw [dif_pos h, dif_pos h]
    by_cases hop : (gs[w - (n + 2)]'(by omega)).op = GateOp.not
    · rw [if_pos hop, if_pos hop]
      split
      · rename_i heq; simp [heq]
      · rename_i u rest heq; simp [heq]; rfl
    · rw [if_neg hop, if_neg hop]
  · rw [dif_neg h, dif_neg h]

theorem rootOf_le (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (w : ℕ) :
    rootOf n gs hBack w ≤ w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [rootOf_eq]
    by_cases h : n + 2 ≤ w ∧ w < n + 2 + gs.length
    · rw [dif_pos h]
      by_cases hop : (gs[w - (n + 2)]'(by omega)).op = GateOp.not
      · rw [if_pos hop]
        generalize hargs : (gs[w - (n + 2)]'(by omega)).inputs = args
        cases args with
        | nil => exact le_refl _
        | cons u rest =>
          have hu : u < w := readsBack_lt hBack h.1 h.2 (by simp [hargs])
          exact (ih u hu).trans (Nat.le_of_lt hu)
      · rw [if_neg hop]
    · rw [dif_neg h]

theorem rootOf_self_of_skel (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {w : ℕ} (hw : w ∈ skelWires n gs) : rootOf n gs hBack w = w := by
  rw [rootOf_eq]
  simp only [skelWires, Finset.mem_union, Finset.mem_range, mem_posWires] at hw
  rcases hw with hlt | ⟨h1, h2, hpos⟩
  · have h : ¬ (n + 2 ≤ w ∧ w < n + 2 + gs.length) := by omega
    rw [dif_neg h]
  · have h : n + 2 ≤ w ∧ w < n + 2 + gs.length := ⟨h1, h2⟩
    rw [dif_pos h, if_neg hpos]

theorem swOf_rootOf (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (w : ℕ) :
    swOf (wval n gs w) = swOf (wval n gs (rootOf n gs hBack w)) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [rootOf_eq]
    by_cases h : n + 2 ≤ w ∧ w < n + 2 + gs.length
    · rw [dif_pos h]
      by_cases hop : (gs[w - (n + 2)]'(by omega)).op = GateOp.not
      · rw [if_pos hop]
        generalize hargs : (gs[w - (n + 2)]'(by omega)).inputs = args
        cases args with
        | nil => rfl
        | cons u rest =>
          have hu : u < w := readsBack_lt hBack h.1 h.2 (by simp [hargs])
          have hneg : wval n gs w = fun t => !(wval n gs u t) := by
            funext t
            have hwe := wval_gate_eval n gs hBack (w - (n + 2)) (by omega) t
            have hwEq : n + 2 + (w - (n + 2)) = w := by omega
            rw [hwEq] at hwe
            rw [hwe, hop, hargs]
            simp [GateOp.eval]
          rw [hneg, swOf_not, ih u hu]
      · rw [if_neg hop]
    · rw [dif_neg h]

theorem rootOf_mem_skel_of_sw_nonempty (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {w : ℕ} (hw : w < n + 2 + gs.length) (hne : (swOf (wval n gs w)).Nonempty) :
    rootOf n gs hBack w ∈ skelWires n gs := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [swOf_rootOf n gs hBack] at hne
    rw [rootOf_eq] at hne ⊢
    by_cases h : n + 2 ≤ w ∧ w < n + 2 + gs.length
    · rw [dif_pos h] at hne ⊢
      by_cases hop : (gs[w - (n + 2)]'(by omega)).op = GateOp.not
      · rw [if_pos hop] at hne ⊢
        generalize hargs : (gs[w - (n + 2)]'(by omega)).inputs = args at hne ⊢
        cases args with
        | nil =>
          have hconst : wval n gs w = fun _ => true := by
            funext t
            have hwe := wval_gate_eval n gs hBack (w - (n + 2)) (by omega) t
            have hwEq : n + 2 + (w - (n + 2)) = w := by omega
            rw [hwEq] at hwe
            rw [hwe, hop, hargs]
            simp [GateOp.eval]
          rw [hconst, swOf_const] at hne
          exact False.elim (Finset.not_nonempty_empty hne)
        | cons u rest =>
          have hu : u < w := readsBack_lt hBack h.1 h.2 (by simp [hargs])
          rw [← swOf_rootOf n gs hBack] at hne
          exact ih u hu (by omega) hne
      · rw [if_neg hop]
        simp only [skelWires, Finset.mem_union, mem_posWires]
        exact Or.inr ⟨h.1, h.2, hop⟩
    · rw [dif_neg h] at hne ⊢
      by_cases hlt : w < n
      · simp [skelWires, hlt]
      · have hcases : w = n ∨ w = n + 1 := by omega
        rcases hcases with hwEq | hwEq
        · rw [hwEq] at hne
          have : wval n gs n = fun _ => false := funext (wval_false n gs)
          rw [this, swOf_const] at hne
          exact False.elim (Finset.not_nonempty_empty hne)
        · rw [hwEq] at hne
          have : wval n gs (n + 1) = fun _ => true := funext (wval_true n gs)
          rw [this, swOf_const] at hne
          exact False.elim (Finset.not_nonempty_empty hne)

theorem ne_base_mem_notWires (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {w : ℕ} (hw : w < n + 2 + gs.length) (hne : w ≠ rootOf n gs hBack w) :
    w ∈ notWires n gs := by
  rw [rootOf_eq] at hne
  by_cases h : n + 2 ≤ w ∧ w < n + 2 + gs.length
  · rw [dif_pos h] at hne
    by_cases hop : (gs[w - (n + 2)]'(by omega)).op = GateOp.not
    · rw [mem_notWires]; exact ⟨h.1, h.2, hop⟩
    · rw [if_neg hop] at hne; exact False.elim (hne rfl)
  · rw [dif_neg h] at hne; exact False.elim (hne rfl)

noncomputable def skelCh (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (p : ℕ) : Finset ℕ :=
  if h : n + 2 ≤ p ∧ p < n + 2 + gs.length then
    if (gs[p - (n + 2)]'(by omega)).op ≠ GateOp.not then
      ((gs[p - (n + 2)]'(by omega)).inputs.toFinset.image (rootOf n gs hBack)).filter
        (fun q => q ∈ skelWires n gs)
    else ∅
  else ∅

theorem skelCh_lt (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {p q : ℕ} (hq : q ∈ skelCh n gs hBack p) : q < p := by
  unfold skelCh at hq
  by_cases h : n + 2 ≤ p ∧ p < n + 2 + gs.length
  · rw [dif_pos h] at hq
    by_cases hop : (gs[p - (n + 2)]'(by omega)).op ≠ GateOp.not
    · rw [if_pos hop, Finset.mem_filter, Finset.mem_image] at hq
      rcases hq with ⟨⟨u, hu, rfl⟩, _⟩
      have huLt : u < p := readsBack_lt hBack h.1 h.2 (List.mem_toFinset.mp hu)
      exact lt_of_le_of_lt (rootOf_le n gs hBack u) huLt
    · rw [if_neg hop] at hq; exact False.elim (Finset.notMem_empty q hq)
  · rw [dif_neg h] at hq; exact False.elim (Finset.notMem_empty q hq)

theorem skelCh_sub_skel (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {p q : ℕ} (hq : q ∈ skelCh n gs hBack p) : q ∈ skelWires n gs := by
  unfold skelCh at hq
  by_cases h : n + 2 ≤ p ∧ p < n + 2 + gs.length
  · rw [dif_pos h] at hq
    by_cases hop : (gs[p - (n + 2)]'(by omega)).op ≠ GateOp.not
    · rw [if_pos hop, Finset.mem_filter] at hq
      exact hq.2
    · rw [if_neg hop] at hq; exact False.elim (Finset.notMem_empty q hq)
  · rw [dif_neg h] at hq; exact False.elim (Finset.notMem_empty q hq)

theorem skelCh_card_le_two (n : ℕ) (gs : List Gate) (hFan : FanInTwo ⟨gs, 0⟩)
    (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (p : ℕ) : (skelCh n gs hBack p).card ≤ 2 := by
  unfold skelCh
  split_ifs with h hop
  · have hlen : (gs[p - (n + 2)]'(by omega)).inputs.length ≤ 2 :=
      (hFan _ (List.getElem_mem (show p - (n + 2) < gs.length by omega))).2
    calc Finset.card (((gs[p - (n + 2)]'(by omega)).inputs.toFinset.image (rootOf n gs hBack)).filter
            (fun q => q ∈ skelWires n gs))
        ≤ ((gs[p - (n + 2)]'(by omega)).inputs.toFinset.image (rootOf n gs hBack)).card :=
          Finset.card_filter_le _ _
      _ ≤ (gs[p - (n + 2)]'(by omega)).inputs.toFinset.card := Finset.card_image_le
      _ ≤ (gs[p - (n + 2)]'(by omega)).inputs.length := List.toFinset_card_le _
      _ ≤ 2 := hlen
  · simp
  · simp

theorem swOf_sub_biUnion_skelCh (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {p : ℕ} (hp : p ∈ posWires n gs) :
    swOf (wval n gs p) ⊆ (skelCh n gs hBack p).biUnion (fun q => swOf (wval n gs q)) := by
  intro s hs
  rw [mem_posWires] at hp
  rcases hp with ⟨hp1, hp2, hpos⟩
  have h : n + 2 ≤ p ∧ p < n + 2 + gs.length := ⟨hp1, hp2⟩
  simp only [swOf, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  have h1 := wval_gate_eval n gs hBack (p - (n + 2)) (by omega) s.castSucc
  have h2 := wval_gate_eval n gs hBack (p - (n + 2)) (by omega) s.succ
  have hpEq : n + 2 + (p - (n + 2)) = p := by omega
  rw [hpEq] at h1 h2
  have hex : ∃ u ∈ (gs[p - (n + 2)]'(by omega)).inputs,
      wval n gs u s.castSucc ≠ wval n gs u s.succ := by
    by_contra hall
    push_neg at hall
    have hmap : ((gs[p - (n + 2)]'(by omega)).inputs.map fun u => wval n gs u s.castSucc) =
        ((gs[p - (n + 2)]'(by omega)).inputs.map fun u => wval n gs u s.succ) :=
      List.map_congr_left hall
    rw [h1, h2, hmap] at hs
    exact hs rfl
  rcases hex with ⟨u, hu, hune⟩
  have huLt : u < n + 2 + gs.length :=
    lt_trans (readsBack_lt hBack h.1 h.2 hu) h.2
  have hsu : s ∈ swOf (wval n gs u) := by simp [swOf, hune]
  have hrSkel : rootOf n gs hBack u ∈ skelWires n gs :=
    rootOf_mem_skel_of_sw_nonempty n gs hBack huLt ⟨s, hsu⟩
  have hrCh : rootOf n gs hBack u ∈ skelCh n gs hBack p := by
    unfold skelCh
    rw [dif_pos h, if_pos hpos, Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨u, List.mem_toFinset.mpr hu, rfl⟩, hrSkel⟩
  rw [swOf_rootOf n gs hBack] at hsu
  exact Finset.mem_biUnion.mpr ⟨rootOf n gs hBack u, hrCh, hsu⟩

noncomputable def cone (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) : ℕ → Finset ℕ :=
  WellFounded.fix (measure id).wf fun r ih =>
    if r ∈ posWires n gs then
      insert r ((skelCh n gs hBack r).attach.biUnion fun ⟨q, hq⟩ => ih q (skelCh_lt n gs hBack hq))
    else {r}

theorem cone_eq (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) :
    cone n gs hBack r =
    if r ∈ posWires n gs then
      insert r ((skelCh n gs hBack r).biUnion (cone n gs hBack))
    else {r} := by
  conv_lhs => unfold cone
  rw [WellFounded.fix_eq]
  split_ifs with h
  · congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨a, ha, hx⟩; exact ⟨a, ha, hx⟩
    · rintro ⟨a, ha, hx⟩; exact ⟨a, ha, hx⟩
  · rfl

theorem mem_cone_self (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) :
    r ∈ cone n gs hBack r := by
  rw [cone_eq]
  split_ifs <;> simp

theorem cone_le (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {r v : ℕ} (hv : v ∈ cone n gs hBack r) : v ≤ r := by
  induction r using Nat.strong_induction_on generalizing v with
  | ind r ih =>
    rw [cone_eq] at hv
    split_ifs at hv with h
    · rcases Finset.mem_insert.mp hv with rfl | hbi
      · exact le_refl _
      · rcases Finset.mem_biUnion.mp hbi with ⟨q, hq, hvq⟩
        have hqr := skelCh_lt n gs hBack hq
        exact (ih q hqr hvq).trans (Nat.le_of_lt hqr)
    · rw [Finset.mem_singleton.mp hv]

theorem cone_sub_skel (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {r : ℕ} (hr : r ∈ skelWires n gs) : cone n gs hBack r ⊆ skelWires n gs := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro v hv
    rw [cone_eq] at hv
    split_ifs at hv with h
    · rcases Finset.mem_insert.mp hv with rfl | hbi
      · exact hr
      · rcases Finset.mem_biUnion.mp hbi with ⟨q, hq, hvq⟩
        exact ih q (skelCh_lt n gs hBack hq) (skelCh_sub_skel n gs hBack hq) hvq
    · rw [Finset.mem_singleton.mp hv]; exact hr

theorem cone_mono_ch (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {p q : ℕ} (hp : p ∈ posWires n gs) (hq : q ∈ skelCh n gs hBack p) :
    cone n gs hBack q ⊆ cone n gs hBack p := by
  intro v hv
  rw [cone_eq n gs hBack p, if_pos hp]
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨q, hq, hv⟩)

noncomputable def conePos (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) : Finset ℕ :=
  cone n gs hBack r ∩ posWires n gs

noncomputable def coneLeaf (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun s : Fin n => s.val ∈ cone n gs hBack r)

theorem coneLeaf_card (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) :
    (coneLeaf n gs hBack r).card = (cone n gs hBack r ∩ Finset.range n).card := by
  have heq : cone n gs hBack r ∩ Finset.range n = (coneLeaf n gs hBack r).image Fin.val := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_image, coneLeaf,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩; exact ⟨⟨x, hlt⟩, hx, rfl⟩
    · rintro ⟨s, hs, rfl⟩; exact ⟨hs, s.isLt⟩
  rw [heq, Finset.card_image_of_injective _ Fin.val_injective]

theorem cone_card_split (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {r : ℕ} (hr : r ∈ skelWires n gs) :
    (cone n gs hBack r).card = (coneLeaf n gs hBack r).card + (conePos n gs hBack r).card := by
  rw [coneLeaf_card]
  have hun : cone n gs hBack r = (cone n gs hBack r ∩ Finset.range n) ∪ conePos n gs hBack r := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, conePos]
    constructor
    · intro hx
      have hxs := cone_sub_skel n gs hBack hr hx
      simp only [skelWires, Finset.mem_union] at hxs
      rcases hxs with h1 | h2
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, h2⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint (cone n gs hBack r ∩ Finset.range n) (conePos n gs hBack r) := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    simp only [Finset.mem_inter, Finset.mem_range, conePos, mem_posWires] at h1 h2
    rcases h2 with ⟨_, hge, _, _⟩
    omega
  conv_lhs => rw [hun]
  exact Finset.card_union_of_disjoint hdisj

theorem swOf_sub_coneLeaf (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {r : ℕ} (hr : r ∈ skelWires n gs) :
    swOf (wval n gs r) ⊆ coneLeaf n gs hBack r := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hp : r ∈ posWires n gs
    · intro s hs
      have hbi := swOf_sub_biUnion_skelCh n gs hBack hp hs
      rcases Finset.mem_biUnion.mp hbi with ⟨q, hq, hsq⟩
      have hql := ih q (skelCh_lt n gs hBack hq) (skelCh_sub_skel n gs hBack hq) hsq
      simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hql ⊢
      exact cone_mono_ch n gs hBack hp hq hql
    · have hlt : r < n := by
        simp only [skelWires, Finset.mem_union, Finset.mem_range] at hr
        exact hr.resolve_right hp
      have hval : wval n gs r = fun t => decide (r < t.val) :=
        funext (wval_input n gs ⟨r, hlt⟩)
      rw [hval]
      intro s hs
      have hsr : s ∈ swOf (fun t : Fin (n + 1) => decide ((⟨r, hlt⟩ : Fin n).val < t.val)) := hs
      rw [swOf_input] at hsr
      have heq : s = ⟨r, hlt⟩ := Finset.mem_singleton.mp hsr
      subst heq
      simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact mem_cone_self n gs hBack r

theorem exists_parent_in_cone (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {r v : ℕ} (hv : v ∈ cone n gs hBack r) (hne : v ≠ r) :
    ∃ p ∈ conePos n gs hBack r, v ∈ skelCh n gs hBack p := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    rw [cone_eq] at hv
    split_ifs at hv with hp
    · rcases Finset.mem_insert.mp hv with rfl | hbi
      · exact False.elim (hne rfl)
      · rcases Finset.mem_biUnion.mp hbi with ⟨q, hq, hvq⟩
        by_cases hvqEq : v = q
        · subst hvqEq
          exact ⟨r, Finset.mem_inter.mpr ⟨mem_cone_self n gs hBack r, hp⟩, hq⟩
        · obtain ⟨p, hpq, hvp⟩ := ih q (skelCh_lt n gs hBack hq) hvq hvqEq
          exact ⟨p, Finset.mem_inter.mpr ⟨cone_mono_ch n gs hBack hp hq (Finset.mem_inter.mp hpq).1,
            (Finset.mem_inter.mp hpq).2⟩, hvp⟩
    · exact False.elim (hne (Finset.mem_singleton.mp hv))

noncomputable def coneEdges (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) :
    Finset (ℕ × ℕ) :=
  (conePos n gs hBack r).biUnion (fun p => (skelCh n gs hBack p).image (fun q => (p, q)))

theorem coneEdges_card_eq_sum (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (r : ℕ) :
    (coneEdges n gs hBack r).card = ∑ p ∈ conePos n gs hBack r, (skelCh n gs hBack p).card := by
  unfold coneEdges
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
  · intro p1 _ p2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_image] at h1 h2
    rcases h1 with ⟨_, _, rfl⟩
    rcases h2 with ⟨_, _, heq⟩
    exact hne (Prod.mk.inj heq).1.symm

theorem cone_trans (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {u v w : ℕ} (huv : u ∈ cone n gs hBack v) (hvw : v ∈ cone n gs hBack w) :
    u ∈ cone n gs hBack w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rw [cone_eq] at hvw
    split_ifs at hvw with hw
    · rcases Finset.mem_insert.mp hvw with rfl | hbi
      · exact huv
      · rcases Finset.mem_biUnion.mp hbi with ⟨c, hc, hvc⟩
        exact cone_mono_ch n gs hBack hw hc (ih c (skelCh_lt n gs hBack hc) hvc)
    · rw [Finset.mem_singleton.mp hvw] at huv; exact huv

theorem coneEdges_snd_mem (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    {r : ℕ} {e : ℕ × ℕ} (he : e ∈ coneEdges n gs hBack r) : e.2 ∈ (cone n gs hBack r).erase r := by
  simp only [coneEdges, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨p, hp, q, hq, rfl⟩
  simp only [Finset.mem_erase, conePos, Finset.mem_inter] at hp ⊢
  have hqr : q < p := skelCh_lt n gs hBack hq
  have hpr : p ≤ r := cone_le n gs hBack hp.1
  have hqCone : q ∈ cone n gs hBack r :=
    cone_trans n gs hBack (cone_mono_ch n gs hBack hp.2 hq (mem_cone_self n gs hBack q)) hp.1
  exact ⟨by omega, hqCone⟩

theorem coneEdges_card_eq_indeg_sum (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (r : ℕ) :
    (coneEdges n gs hBack r).card =
      ∑ v ∈ (cone n gs hBack r).erase r, ((coneEdges n gs hBack r).filter (fun e => e.2 = v)).card := by
  exact Finset.card_eq_sum_card_fiberwise (fun e he => coneEdges_snd_mem n gs hBack he)

theorem tight_tree_facts (n : ℕ) (gs : List Gate)
    (hFan : FanInTwo ⟨gs, 0⟩) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (hPosLe : posCount gs ≤ n - 1) (hn : 0 < n)
    (r0 : ℕ) (hr0 : r0 ∈ skelWires n gs) (hFull : coneLeaf n gs hBack r0 = Finset.univ) :
    conePos n gs hBack r0 = posWires n gs ∧
    (conePos n gs hBack r0).card = n - 1 ∧
    (∀ p ∈ posWires n gs, (skelCh n gs hBack p).card = 2) ∧
    (∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2) ∧
    cone n gs hBack r0 = skelWires n gs := by
  have h1 : (cone n gs hBack r0).card = n + (conePos n gs hBack r0).card := by
    rw [cone_card_split n gs hBack hr0, hFull, Finset.card_univ, Fintype.card_fin]
  have hErase : ((cone n gs hBack r0).erase r0).card = n + (conePos n gs hBack r0).card - 1 := by
    rw [Finset.card_erase_of_mem (mem_cone_self n gs hBack r0), h1]
  have hindegGe : ∀ v ∈ (cone n gs hBack r0).erase r0,
      1 ≤ ((coneEdges n gs hBack r0).filter (fun e => e.2 = v)).card := by
    intro v hv
    rcases Finset.mem_erase.mp hv with ⟨hne, hvCone⟩
    obtain ⟨p, hp, hvp⟩ := exists_parent_in_cone n gs hBack hvCone hne
    have hmem : (p, v) ∈ (coneEdges n gs hBack r0).filter (fun e => e.2 = v) :=
      Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨v, hvp, rfl⟩⟩, rfl⟩
    exact Finset.card_pos.mpr ⟨(p, v), hmem⟩
  have hLow : ((cone n gs hBack r0).erase r0).card ≤ (coneEdges n gs hBack r0).card := by
    rw [coneEdges_card_eq_indeg_sum]
    calc ((cone n gs hBack r0).erase r0).card
        = ∑ _v ∈ (cone n gs hBack r0).erase r0, 1 := by simp
      _ ≤ ∑ v ∈ (cone n gs hBack r0).erase r0,
            ((coneEdges n gs hBack r0).filter (fun e => e.2 = v)).card :=
          Finset.sum_le_sum hindegGe
  have hHigh : (coneEdges n gs hBack r0).card ≤ 2 * (conePos n gs hBack r0).card := by
    rw [coneEdges_card_eq_sum]
    calc ∑ p ∈ conePos n gs hBack r0, (skelCh n gs hBack p).card
        ≤ ∑ _p ∈ conePos n gs hBack r0, 2 :=
          Finset.sum_le_sum (fun p _ => skelCh_card_le_two n gs hFan hBack p)
      _ = 2 * (conePos n gs hBack r0).card := by simp [Nat.mul_comm]
  have hSubPos : conePos n gs hBack r0 ⊆ posWires n gs := Finset.inter_subset_right
  have hPosCardLe : (conePos n gs hBack r0).card ≤ n - 1 := by
    calc (conePos n gs hBack r0).card
        ≤ (posWires n gs).card := Finset.card_le_card hSubPos
      _ = posCount gs := posWires_card n gs
      _ ≤ n - 1 := hPosLe
  have hPosCardEq : (conePos n gs hBack r0).card = n - 1 := by omega
  have hPosEq : conePos n gs hBack r0 = posWires n gs := by
    apply Finset.eq_of_subset_of_card_le hSubPos
    rw [posWires_card]; omega
  have hEdgesEq : (coneEdges n gs hBack r0).card = 2 * (conePos n gs hBack r0).card := by omega
  have hChTwo : ∀ p ∈ posWires n gs, (skelCh n gs hBack p).card = 2 := by
    have hsum : ∑ p ∈ conePos n gs hBack r0, (skelCh n gs hBack p).card =
        ∑ _p ∈ conePos n gs hBack r0, 2 := by
      rw [← coneEdges_card_eq_sum, hEdgesEq]; simp [Nat.mul_comm]
    have hall := (Finset.sum_eq_sum_iff_of_le (fun p _ => skelCh_card_le_two n gs hFan hBack p)).mp hsum
    intro p hp
    exact hall p (hPosEq ▸ hp)
  have hIndegOne : ∀ v ∈ (cone n gs hBack r0).erase r0,
      ((coneEdges n gs hBack r0).filter (fun e => e.2 = v)).card = 1 := by
    have hsum : ∑ _v ∈ (cone n gs hBack r0).erase r0, 1 =
        ∑ v ∈ (cone n gs hBack r0).erase r0,
          ((coneEdges n gs hBack r0).filter (fun e => e.2 = v)).card := by
      rw [← coneEdges_card_eq_indeg_sum]; simp [hEdgesEq, hErase]; omega
    have hall := (Finset.sum_eq_sum_iff_of_le hindegGe).mp hsum
    intro v hv
    exact (hall v hv).symm
  have hUniqPar : ∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2 := by
    intro p1 hp1 p2 hp2 v hv1 hv2
    have he1 : (p1, v) ∈ coneEdges n gs hBack r0 := by
      simp only [coneEdges, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨p1, hPosEq ▸ hp1, v, hv1, rfl⟩
    have he2 : (p2, v) ∈ coneEdges n gs hBack r0 := by
      simp only [coneEdges, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨p2, hPosEq ▸ hp2, v, hv2, rfl⟩
    have hvEr : v ∈ (cone n gs hBack r0).erase r0 := coneEdges_snd_mem n gs hBack he1
    have hcard1 := hIndegOne v hvEr
    have h1 : (p1, v) ∈ (coneEdges n gs hBack r0).filter (fun e => e.2 = v) :=
      Finset.mem_filter.mpr ⟨he1, rfl⟩
    have h2 : (p2, v) ∈ (coneEdges n gs hBack r0).filter (fun e => e.2 = v) :=
      Finset.mem_filter.mpr ⟨he2, rfl⟩
    have heq := Finset.card_le_one.mp (le_of_eq hcard1) (p1, v) h1 (p2, v) h2
    exact (Prod.mk.inj heq).1
  have hConeEq : cone n gs hBack r0 = skelWires n gs := by
    ext x
    constructor
    · exact fun hx => cone_sub_skel n gs hBack hr0 hx
    · intro hx
      simp only [skelWires, Finset.mem_union, Finset.mem_range] at hx
      rcases hx with hlt | hpos
      · have : (⟨x, hlt⟩ : Fin n) ∈ coneLeaf n gs hBack r0 := by rw [hFull]; exact Finset.mem_univ _
        simpa [coneLeaf] using this
      · rw [← hPosEq] at hpos
        exact (Finset.mem_inter.mp hpos).1
  exact ⟨hPosEq, hPosCardEq, hChTwo, hUniqPar, hConeEq⟩

theorem cone_laminar (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (hUniq : ∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2)
    {u w : ℕ} (hne : (cone n gs hBack u ∩ cone n gs hBack w).Nonempty) :
    u ∈ cone n gs hBack w ∨ w ∈ cone n gs hBack u := by
  let S := cone n gs hBack u ∩ cone n gs hBack w
  let m := S.max' hne
  have hm : m ∈ S := Finset.max'_mem S hne
  rcases Finset.mem_inter.mp hm with ⟨hmu, hmw⟩
  by_cases h1 : m = u
  · left; exact h1 ▸ hmw
  · by_cases h2 : m = w
    · right; exact h2 ▸ hmu
    · obtain ⟨p1, hp1, hmp1⟩ := exists_parent_in_cone n gs hBack hmu h1
      obtain ⟨p2, hp2, hmp2⟩ := exists_parent_in_cone n gs hBack hmw h2
      have hp1eq : p1 = p2 :=
        hUniq p1 (Finset.mem_inter.mp hp1).2 p2 (Finset.mem_inter.mp hp2).2 m hmp1 hmp2
      subst hp1eq
      have hpS : p1 ∈ S := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp1).1, (Finset.mem_inter.mp hp2).1⟩
      have hle : p1 ≤ m := Finset.le_max' S p1 hpS
      have hlt : m < p1 := skelCh_lt n gs hBack hmp1
      omega

theorem cone_disjoint_ch (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (hUniq : ∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2)
    {p q1 q2 : ℕ} (hp : p ∈ posWires n gs)
    (hq1 : q1 ∈ skelCh n gs hBack p) (hq2 : q2 ∈ skelCh n gs hBack p) (hne : q1 ≠ q2) :
    Disjoint (cone n gs hBack q1) (cone n gs hBack q2) := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hneInt
  have hnon := Finset.nonempty_iff_ne_empty.mpr hneInt
  rcases cone_laminar n gs hBack hUniq hnon with h12 | h21
  · obtain ⟨p2, hp2, hq1p2⟩ := exists_parent_in_cone n gs hBack h12 hne
    have hpeq := hUniq p hp p2 (Finset.mem_inter.mp hp2).2 q1 hq1 hq1p2
    subst hpeq
    have hle := cone_le n gs hBack (Finset.mem_inter.mp hp2).1
    have hlt := skelCh_lt n gs hBack hq2
    omega
  · obtain ⟨p1, hp1, hq2p1⟩ := exists_parent_in_cone n gs hBack h21 hne.symm
    have hpeq := hUniq p hp p1 (Finset.mem_inter.mp hp1).2 q2 hq2 hq2p1
    subst hpeq
    have hle := cone_le n gs hBack (Finset.mem_inter.mp hp1).1
    have hlt := skelCh_lt n gs hBack hq1
    omega

theorem coneLeaf_nonempty (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (hChTwo : ∀ p ∈ posWires n gs, (skelCh n gs hBack p).card = 2)
    {r : ℕ} (hr : r ∈ skelWires n gs) : (coneLeaf n gs hBack r).Nonempty := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hp : r ∈ posWires n gs
    · have hc := hChTwo r hp
      obtain ⟨q, hq⟩ := Finset.card_pos.mp (by omega : 0 < (skelCh n gs hBack r).card)
      obtain ⟨s, hs⟩ := ih q (skelCh_lt n gs hBack hq) (skelCh_sub_skel n gs hBack hq)
      exact ⟨s, by
        simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        exact cone_mono_ch n gs hBack hp hq hs⟩
    · have hlt : r < n := by
        simp only [skelWires, Finset.mem_union, Finset.mem_range] at hr
        exact hr.resolve_right hp
      exact ⟨⟨r, hlt⟩, by simp [coneLeaf, mem_cone_self]⟩

theorem swOf_eq_coneLeaf_all (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (_hChTwo : ∀ p ∈ posWires n gs, (skelCh n gs hBack p).card = 2)
    (hUniq : ∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2)
    (r0 : ℕ) (hr0 : r0 ∈ skelWires n gs) (hsw0 : swOf (wval n gs r0) = coneLeaf n gs hBack r0) :
    ∀ v ∈ cone n gs hBack r0, swOf (wval n gs v) = coneLeaf n gs hBack v := by
  intro v hv

  have haux : ∀ d v, v ∈ cone n gs hBack r0 → r0 - v ≤ d →
      swOf (wval n gs v) = coneLeaf n gs hBack v := by
    intro d
    induction d with
    | zero =>
      intro v hv hle
      have hvr : v ≤ r0 := cone_le n gs hBack hv
      have heq : v = r0 := by omega
      subst heq; exact hsw0
    | succ d ih =>
      intro v hv hle
      by_cases hvr : v = r0
      · subst hvr; exact hsw0
      · obtain ⟨p, hp, hvp⟩ := exists_parent_in_cone n gs hBack hv hvr
        have hpCone : p ∈ cone n gs hBack r0 := (Finset.mem_inter.mp hp).1
        have hpPos : p ∈ posWires n gs := (Finset.mem_inter.mp hp).2
        have hvpLt : v < p := skelCh_lt n gs hBack hvp
        have hprLe : p ≤ r0 := cone_le n gs hBack hpCone
        have hswP : swOf (wval n gs p) = coneLeaf n gs hBack p := ih p hpCone (by omega)
        apply Finset.Subset.antisymm (swOf_sub_coneLeaf n gs hBack (cone_sub_skel n gs hBack hr0 hv))
        intro s hs
        have hsP : s ∈ coneLeaf n gs hBack p := by
          simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          exact cone_mono_ch n gs hBack hpPos hvp hs
        rw [← hswP] at hsP
        have hbi := swOf_sub_biUnion_skelCh n gs hBack hpPos hsP
        rcases Finset.mem_biUnion.mp hbi with ⟨q, hqp, hsq⟩
        by_cases hqv : q = v
        · exact hqv ▸ hsq
        · have hdisj := cone_disjoint_ch n gs hBack hUniq hpPos hvp hqp (Ne.symm hqv)
          have hsqL := swOf_sub_coneLeaf n gs hBack (skelCh_sub_skel n gs hBack hqp) hsq
          simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hs hsqL
          exact False.elim (Finset.disjoint_left.mp hdisj hs hsqL)
  exact haux (r0 - v) v hv (le_refl _)

theorem coneLeaf_inj (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (hChTwo : ∀ p ∈ posWires n gs, (skelCh n gs hBack p).card = 2)
    (hUniq : ∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2)
    {u v : ℕ} (hu : u ∈ skelWires n gs) (hv : v ∈ skelWires n gs)
    (heq : coneLeaf n gs hBack u = coneLeaf n gs hBack v) : u = v := by
  obtain ⟨s, hs⟩ := coneLeaf_nonempty n gs hBack hChTwo hu
  have hsv : s ∈ coneLeaf n gs hBack v := heq ▸ hs
  simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hs hsv
  have hnon : (cone n gs hBack u ∩ cone n gs hBack v).Nonempty := ⟨s.val, Finset.mem_inter.mpr ⟨hs, hsv⟩⟩
  by_contra hne
  rcases cone_laminar n gs hBack hUniq hnon with huv | hvu
  · obtain ⟨p, hp, hup⟩ := exists_parent_in_cone n gs hBack huv hne
    have hpPos : p ∈ posWires n gs := (Finset.mem_inter.mp hp).2
    have hcard := hChTwo p hpPos
    obtain ⟨q1, q2, hqne, hchEq⟩ := Finset.card_eq_two.mp hcard
    have hqother : ∃ q ∈ skelCh n gs hBack p, q ≠ u := by
      rw [hchEq] at hup ⊢
      rcases Finset.mem_insert.mp hup with rfl | h2
      · exact ⟨q2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hqne.symm⟩
      · rw [Finset.mem_singleton.mp h2]
        exact ⟨q1, Finset.mem_insert_self _ _, hqne⟩
    rcases hqother with ⟨q, hqp, hqu⟩
    obtain ⟨t, ht⟩ := coneLeaf_nonempty n gs hBack hChTwo (skelCh_sub_skel n gs hBack hqp)
    have hdisj := cone_disjoint_ch n gs hBack hUniq hpPos hup hqp hqu.symm
    have htv : t ∈ coneLeaf n gs hBack v := by
      simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact cone_trans n gs hBack (cone_mono_ch n gs hBack hpPos hqp ht) (Finset.mem_inter.mp hp).1
    rw [← heq] at htv
    simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at ht htv
    exact Finset.disjoint_left.mp hdisj htv ht
  · obtain ⟨p, hp, hvp⟩ := exists_parent_in_cone n gs hBack hvu (Ne.symm hne)
    have hpPos : p ∈ posWires n gs := (Finset.mem_inter.mp hp).2
    have hcard := hChTwo p hpPos
    obtain ⟨q1, q2, hqne, hchEq⟩ := Finset.card_eq_two.mp hcard
    have hqother : ∃ q ∈ skelCh n gs hBack p, q ≠ v := by
      rw [hchEq] at hvp ⊢
      rcases Finset.mem_insert.mp hvp with rfl | h2
      · exact ⟨q2, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hqne.symm⟩
      · rw [Finset.mem_singleton.mp h2]
        exact ⟨q1, Finset.mem_insert_self _ _, hqne⟩
    rcases hqother with ⟨q, hqp, hqv⟩
    obtain ⟨t, ht⟩ := coneLeaf_nonempty n gs hBack hChTwo (skelCh_sub_skel n gs hBack hqp)
    have hdisj := cone_disjoint_ch n gs hBack hUniq hpPos hvp hqp hqv.symm
    have htu : t ∈ coneLeaf n gs hBack u := by
      simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact cone_trans n gs hBack (cone_mono_ch n gs hBack hpPos hqp ht) (Finset.mem_inter.mp hp).1
    rw [heq] at htu
    simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at ht htu
    exact Finset.disjoint_left.mp hdisj htu ht

noncomputable def notGroup (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) : Finset ℕ :=
  (notWires n gs).filter (fun w => rootOf n gs hBack w = r)

noncomputable def notBudget (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) : ℕ :=
  ∑ w ∈ cone n gs hBack r, (notGroup n gs hBack w).card

theorem notBudget_le_notCount (n : ℕ) (gs : List Gate) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩) (r : ℕ) :
    notBudget n gs hBack r ≤ PEqualNP.NotBracket.notCount ⟨gs, 0⟩ := by
  rw [← notWires_card n gs]
  unfold notBudget notGroup
  have h1 : ∑ w ∈ cone n gs hBack r, ((notWires n gs).filter (fun u => rootOf n gs hBack u = w)).card =
      ((cone n gs hBack r).biUnion (fun w => (notWires n gs).filter (fun u => rootOf n gs hBack u = w))).card := by
    symm
    apply Finset.card_biUnion
    intro w1 _ w2 _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro u h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact hne (h1.2.symm.trans h2.2)
  rw [h1]
  apply Finset.card_le_card
  intro u hu
  rcases Finset.mem_biUnion.mp hu with ⟨w, _, hw⟩
  exact (Finset.mem_filter.mp hw).1

theorem extract_tree {n a : ℕ} (W : Fin (a + 1) → Fin (n + 1) → Bool)
    (gs : List Gate) (tap : Fin (a + 1) → ℕ)
    (hFan : FanInTwo ⟨gs, 0⟩) (hBack : ReadsBack (n + 2) ⟨gs, 0⟩)
    (hTapLt : ∀ i, tap i < n + 2 + gs.length)
    (hTapVal : ∀ t i, wval n gs (tap i) t = W i t)
    (hChTwo : ∀ p ∈ posWires n gs, (skelCh n gs hBack p).card = 2)
    (hUniq : ∀ p1 ∈ posWires n gs, ∀ p2 ∈ posWires n gs, ∀ v,
      v ∈ skelCh n gs hBack p1 → v ∈ skelCh n gs hBack p2 → p1 = p2)
    (hSwAll : ∀ v ∈ skelWires n gs, swOf (wval n gs v) = coneLeaf n gs hBack v) :
    ∀ (d : ℕ) (v w_want k : ℕ),
      v ∈ skelWires n gs → w_want < n + 2 + gs.length → rootOf n gs hBack w_want = v →
      (conePos n gs hBack v).card ≤ d → notBudget n gs hBack v ≤ k →
      treeFn W d (coneLeaf n gs hBack v) (wval n gs w_want 0) k := by
  have htollBound : ∀ v w_want, v ∈ skelWires n gs → w_want < n + 2 + gs.length →
      rootOf n gs hBack w_want = v →
      tollFn W (coneLeaf n gs hBack v) (wval n gs v 0) (wval n gs w_want 0) ≤
        (notGroup n gs hBack v).card := by
    intro v w_want hv hw hroot
    unfold tollFn
    split_ifs with ht
    · rcases ht with hne | ⟨i, hswi, hwi0⟩
      · have hneW : w_want ≠ v := fun h => hne (h ▸ rfl)
        have hwNot : w_want ∈ notWires n gs :=
          ne_base_mem_notWires n gs hBack hw (hroot.symm ▸ hneW)
        have hmem : w_want ∈ notGroup n gs hBack v := Finset.mem_filter.mpr ⟨hwNot, hroot⟩
        exact Finset.card_pos.mpr ⟨w_want, hmem⟩
      · have hneSw : (swOf (wval n gs (tap i))).Nonempty := by
          have : swOf (wval n gs (tap i)) = swOf (W i) := by
            congr 1; funext t; exact hTapVal t i
          rw [this, hswi]
          exact coneLeaf_nonempty n gs hBack hChTwo hv
        have hrSkel : rootOf n gs hBack (tap i) ∈ skelWires n gs :=
          rootOf_mem_skel_of_sw_nonempty n gs hBack (hTapLt i) hneSw
        have hrLeaf : coneLeaf n gs hBack (rootOf n gs hBack (tap i)) = coneLeaf n gs hBack v := by
          rw [← hSwAll _ hrSkel, ← swOf_rootOf n gs hBack]
          have : wval n gs (tap i) = W i := funext (fun t => hTapVal t i)
          rw [this, hswi]
        have hrEq : rootOf n gs hBack (tap i) = v :=
          coneLeaf_inj n gs hBack hChTwo hUniq hrSkel hv hrLeaf
        have hneTap : tap i ≠ v := by
          intro heq
          have h0 : wval n gs (tap i) 0 = W i 0 := hTapVal 0 i
          rw [heq] at h0
          exact hwi0 h0.symm
        have hnotTap : tap i ∈ notWires n gs :=
          ne_base_mem_notWires n gs hBack (hTapLt i) (hrEq.symm ▸ hneTap)
        have hmem : tap i ∈ notGroup n gs hBack v := Finset.mem_filter.mpr ⟨hnotTap, hrEq⟩
        exact Finset.card_pos.mpr ⟨tap i, hmem⟩
    · exact Nat.zero_le _
  have hLeafCase : ∀ v w_want k, v ∈ skelWires n gs → v ∉ posWires n gs →
      w_want < n + 2 + gs.length → rootOf n gs hBack w_want = v →
      notBudget n gs hBack v ≤ k →
      leafFn W (coneLeaf n gs hBack v) (wval n gs w_want 0) k := by
    intro v w_want k hv hnotPos hw hroot hbud
    have hvLt : v < n := by
      simp only [skelWires, Finset.mem_union, Finset.mem_range] at hv
      exact hv.resolve_right hnotPos
    have hconeV : cone n gs hBack v = {v} := by rw [cone_eq, if_neg hnotPos]
    have hleafV : coneLeaf n gs hBack v = {⟨v, hvLt⟩} := by
      ext s
      simp only [coneLeaf, hconeV, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton, Fin.ext_iff]
    have hval0 : wval n gs v 0 = false := by
      rw [wval_input n gs ⟨v, hvLt⟩ 0]; simp
    have hbudEq : notBudget n gs hBack v = (notGroup n gs hBack v).card := by
      simp [notBudget, hconeV]
    refine ⟨by rw [hleafV]; simp, ?_⟩
    have htb := htollBound v w_want hv hw hroot
    rw [hval0] at htb
    omega
  intro d
  induction d with
  | zero =>
    intro v w_want k hv hw hroot hpos hbud
    have hnotPos : v ∉ posWires n gs := by
      intro hp
      have : v ∈ conePos n gs hBack v := Finset.mem_inter.mpr ⟨mem_cone_self n gs hBack v, hp⟩
      have : 0 < (conePos n gs hBack v).card := Finset.card_pos.mpr ⟨v, this⟩
      omega
    exact hLeafCase v w_want k hv hnotPos hw hroot hbud
  | succ d ih =>
    intro v w_want k hv hw hroot hpos hbud
    by_cases hvPos : v ∈ posWires n gs
    · right
      obtain ⟨hv1, hv2, hgNot0⟩ := mem_posWires.mp hvPos
      have hvBounds : n + 2 ≤ v ∧ v < n + 2 + gs.length := ⟨hv1, hv2⟩
      let g := gs[v - (n + 2)]'(by omega)
      have hgNot : g.op ≠ GateOp.not := hgNot0
      have hgFan := hFan g (List.getElem_mem (show v - (n + 2) < gs.length by omega))
      have hCh2 := hChTwo v hvPos
      have hInLen : g.inputs.length = 2 := by
        have hle : g.inputs.length ≤ 2 := hgFan.2
        have hge : 2 ≤ g.inputs.length := by
          calc 2 = (skelCh n gs hBack v).card := hCh2.symm
            _ ≤ (g.inputs.toFinset.image (rootOf n gs hBack)).card := by
              unfold skelCh
              simp only [hvBounds, hgNot0, ne_eq, not_false_eq_true, dite_true, ite_true]
              exact Finset.card_filter_le (g.inputs.toFinset.image (rootOf n gs hBack))
                (fun q => q ∈ skelWires n gs)
            _ ≤ g.inputs.toFinset.card := Finset.card_image_le
            _ ≤ g.inputs.length := List.toFinset_card_le _
        omega
      rcases List.length_eq_two.mp hInLen with ⟨u1, u2, hInEq⟩
      let q1 := rootOf n gs hBack u1
      let q2 := rootOf n gs hBack u2
      have hChEq : skelCh n gs hBack v = {q1, q2} := by
        have hsub : skelCh n gs hBack v ⊆ {q1, q2} := by
          intro q hq
          unfold skelCh at hq
          simp only [hvBounds, hgNot0, ne_eq, not_false_eq_true, dite_true, ite_true] at hq
          change q ∈ (g.inputs.toFinset.image (rootOf n gs hBack)).filter (fun q => q ∈ skelWires n gs) at hq
          rw [hInEq] at hq
          simp only [Finset.mem_filter, Finset.mem_image, List.mem_toFinset, List.mem_cons,
            List.not_mem_nil, or_false] at hq
          rcases hq with ⟨⟨u, rfl | rfl, rfl⟩, _⟩
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        apply Finset.eq_of_subset_of_card_le hsub
        rw [hCh2]
        exact Finset.card_le_two
      have hqNe : q1 ≠ q2 := by
        intro heq
        rw [heq, Finset.pair_eq_singleton] at hChEq
        rw [hChEq, Finset.card_singleton] at hCh2
        omega
      have hq1Ch : q1 ∈ skelCh n gs hBack v := by rw [hChEq]; simp
      have hq2Ch : q2 ∈ skelCh n gs hBack v := by rw [hChEq]; simp
      have hq1Skel : q1 ∈ skelWires n gs := skelCh_sub_skel n gs hBack hq1Ch
      have hq2Skel : q2 ∈ skelWires n gs := skelCh_sub_skel n gs hBack hq2Ch
      have hDisjCone : Disjoint (cone n gs hBack q1) (cone n gs hBack q2) :=
        cone_disjoint_ch n gs hBack hUniq hvPos hq1Ch hq2Ch hqNe
      have hConeSplit : cone n gs hBack v = insert v (cone n gs hBack q1 ∪ cone n gs hBack q2) := by
        rw [cone_eq, if_pos hvPos, hChEq, Finset.biUnion_insert, Finset.singleton_biUnion]
      have hvNotQ1 : v ∉ cone n gs hBack q1 := fun h =>
        Nat.not_le.mpr (skelCh_lt n gs hBack hq1Ch) (cone_le n gs hBack h)
      have hvNotQ2 : v ∉ cone n gs hBack q2 := fun h =>
        Nat.not_le.mpr (skelCh_lt n gs hBack hq2Ch) (cone_le n gs hBack h)
      have hvNotUn : v ∉ cone n gs hBack q1 ∪ cone n gs hBack q2 := by
        simp [hvNotQ1, hvNotQ2]
      have hBudSplit : notBudget n gs hBack v =
          notBudget n gs hBack q1 + notBudget n gs hBack q2 + (notGroup n gs hBack v).card := by
        unfold notBudget
        rw [hConeSplit, Finset.sum_insert hvNotUn, Finset.sum_union hDisjCone]
        omega
      have hLeafUn : coneLeaf n gs hBack q1 ∪ coneLeaf n gs hBack q2 = coneLeaf n gs hBack v := by
        ext s
        simp only [Finset.mem_union, coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and,
          hConeSplit, Finset.mem_insert]
        constructor
        · rintro (h1 | h2)
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr h2)
        · rintro (hveq | h1 | h2)
          · have := s.isLt; omega
          · exact Or.inl h1
          · exact Or.inr h2
      have hLeafDisj : Disjoint (coneLeaf n gs hBack q1) (coneLeaf n gs hBack q2) := by
        rw [Finset.disjoint_left]
        intro s h1 h2
        simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        exact Finset.disjoint_left.mp hDisjCone h1 h2
      have hvInPos : v ∈ conePos n gs hBack v :=
        Finset.mem_inter.mpr ⟨mem_cone_self n gs hBack v, hvPos⟩
      have hPosSub1 : (conePos n gs hBack q1).card ≤ d := by
        have hsub : conePos n gs hBack q1 ⊆ (conePos n gs hBack v).erase v := by
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxc, hxp⟩
          exact Finset.mem_erase.mpr ⟨fun heq => hvNotQ1 (heq ▸ hxc),
            Finset.mem_inter.mpr ⟨cone_mono_ch n gs hBack hvPos hq1Ch hxc, hxp⟩⟩
        have hlt := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hvInPos] at hlt
        have hposV : 1 ≤ (conePos n gs hBack v).card := Finset.card_pos.mpr ⟨v, hvInPos⟩
        omega
      have hPosSub2 : (conePos n gs hBack q2).card ≤ d := by
        have hsub : conePos n gs hBack q2 ⊆ (conePos n gs hBack v).erase v := by
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hxc, hxp⟩
          exact Finset.mem_erase.mpr ⟨fun heq => hvNotQ2 (heq ▸ hxc),
            Finset.mem_inter.mpr ⟨cone_mono_ch n gs hBack hvPos hq2Ch hxc, hxp⟩⟩
        have hlt := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hvInPos] at hlt
        have hposV : 1 ≤ (conePos n gs hBack v).card := Finset.card_pos.mpr ⟨v, hvInPos⟩
        omega
      have hu1Lt : u1 < n + 2 + gs.length :=
        lt_trans (readsBack_lt hBack hvBounds.1 hvBounds.2 (by simp [g, hInEq])) hvBounds.2
      have hu2Lt : u2 < n + 2 + gs.length :=
        lt_trans (readsBack_lt hBack hvBounds.1 hvBounds.2 (by simp [g, hInEq])) hvBounds.2
      let op : Bool := decide (g.op = GateOp.and)
      let x := wval n gs u1 0
      let y := wval n gs u2 0
      let ka : Fin (k + 1) := ⟨notBudget n gs hBack q1, by omega⟩
      let kb : Fin (k + 1) := ⟨notBudget n gs hBack q2, by omega⟩
      have hGateVal : ∀ t, (if op then wval n gs u1 t && wval n gs u2 t
          else wval n gs u1 t || wval n gs u2 t) = wval n gs v t := by
        intro t
        have hwe := wval_gate_eval n gs hBack (v - (n + 2)) (by omega) t
        have hvEq : n + 2 + (v - (n + 2)) = v := by omega
        rw [hvEq] at hwe
        rw [hwe]
        change _ = g.op.eval (g.inputs.map fun p => wval n gs p t)
        rw [hInEq]
        rcases hgFan.1 with hand | hor | hnot
        · simp [op, hand, GateOp.eval]
        · simp [op, hor, GateOp.eval]
        · exact False.elim (hgNot hnot)
      have hv0Eq : wval n gs v 0 = (if op then x && y else x || y) := (hGateVal 0).symm
      have hGateTrace : ∀ t,
          (if op then traceFn (coneLeaf n gs hBack q1) x t && traceFn (coneLeaf n gs hBack q2) y t
           else traceFn (coneLeaf n gs hBack q1) x t || traceFn (coneLeaf n gs hBack q2) y t) =
          traceFn (coneLeaf n gs hBack v) (if op then x && y else x || y) t := by
        intro t
        have hu1Tr : traceFn (coneLeaf n gs hBack q1) x t = wval n gs u1 t := by
          rw [← hSwAll q1 hq1Skel, ← swOf_rootOf n gs hBack u1]
          exact (eq_traceFn_swOf (wval n gs u1) t).symm
        have hu2Tr : traceFn (coneLeaf n gs hBack q2) y t = wval n gs u2 t := by
          rw [← hSwAll q2 hq2Skel, ← swOf_rootOf n gs hBack u2]
          exact (eq_traceFn_swOf (wval n gs u2) t).symm
        have hvTr : traceFn (coneLeaf n gs hBack v) (if op then x && y else x || y) t = wval n gs v t := by
          rw [← hv0Eq, ← hSwAll v hv]
          exact (eq_traceFn_swOf (wval n gs v) t).symm
        rw [hu1Tr, hu2Tr, hvTr, hGateVal t]
      have hSplitW : ∀ i : Fin (a + 1), swOf (W i) ⊆ coneLeaf n gs hBack v →
          swOf (W i) ≠ coneLeaf n gs hBack v →
          swOf (W i) ⊆ coneLeaf n gs hBack q1 ∨ swOf (W i) ⊆ coneLeaf n gs hBack q2 := by
        intro i hsub hne
        by_cases hemp : swOf (W i) = ∅
        · left; rw [hemp]; exact Finset.empty_subset _
        · have hneSw : (swOf (wval n gs (tap i))).Nonempty := by
            have : wval n gs (tap i) = W i := funext (fun t => hTapVal t i)
            rw [this]
            exact Finset.nonempty_iff_ne_empty.mpr hemp
          have hrSkel : rootOf n gs hBack (tap i) ∈ skelWires n gs :=
            rootOf_mem_skel_of_sw_nonempty n gs hBack (hTapLt i) hneSw
          let ri := rootOf n gs hBack (tap i)
          have hriLeaf : coneLeaf n gs hBack ri = swOf (W i) := by
            rw [← hSwAll ri hrSkel, ← swOf_rootOf n gs hBack (tap i)]
            congr 1; funext t; exact hTapVal t i
          obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          have hsRi : s.val ∈ cone n gs hBack ri := by
            have : s ∈ coneLeaf n gs hBack ri := hriLeaf.symm ▸ hs
            simpa [coneLeaf] using this
          have hsV : s.val ∈ cone n gs hBack v := by
            have : s ∈ coneLeaf n gs hBack v := hsub hs
            simpa [coneLeaf] using this
          have hnon : (cone n gs hBack ri ∩ cone n gs hBack v).Nonempty :=
            ⟨s.val, Finset.mem_inter.mpr ⟨hsRi, hsV⟩⟩
          rcases cone_laminar n gs hBack hUniq hnon with hriV | hvRi
          · have hriNeV : ri ≠ v := fun h => hne (hriLeaf.symm.trans (h ▸ rfl))
            rw [hConeSplit, Finset.mem_insert] at hriV
            rcases hriV.resolve_left hriNeV |> Finset.mem_union.mp with h1 | h2
            · left
              rw [← hriLeaf]
              intro u hu
              simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
              exact cone_trans n gs hBack hu h1
            · right
              rw [← hriLeaf]
              intro u hu
              simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
              exact cone_trans n gs hBack hu h2
          · exfalso
            have hVsubRi : coneLeaf n gs hBack v ⊆ swOf (W i) := by
              rw [← hriLeaf]
              intro u hu
              simp only [coneLeaf, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
              exact cone_trans n gs hBack hu hvRi
            exact hne (Finset.Subset.antisymm hsub hVsubRi)
      have htb := htollBound v w_want hv hw hroot
      rw [hv0Eq] at htb
      refine ⟨coneLeaf n gs hBack q1, coneLeaf n gs hBack q2, x, y, op, ka, kb,
        coneLeaf_nonempty n gs hBack hChTwo hq1Skel,
        coneLeaf_nonempty n gs hBack hChTwo hq2Skel,
        hLeafDisj, hLeafUn, hSplitW, hGateTrace,
        ih q1 u1 ka.val hq1Skel hu1Lt rfl hPosSub1 (le_refl _),
        ih q2 u2 kb.val hq2Skel hu2Lt rfl hPosSub2 (le_refl _),
        by dsimp only [ka, kb]; omega⟩
    · left
      exact hLeafCase v w_want k hv hvPos hw hroot hbud

end BackwardExtraction

end PEqualNP.Outside.L_lib_1377_aux

open PEqualNP.Outside.L_lib_1377_aux

theorem PEqualNP.Outside.L_lib_1377 : (∀ (n a b : Nat) (W : Fin (a+1) → Fin (n+1) → Bool), 0 < n →
  let switches := fun (i : Fin (a+1)) => Finset.univ.filter (fun s : Fin n =>
    W i s.castSucc ≠ W i s.succ)
  switches 0 = Finset.univ →
  let trace := fun (S : Finset (Fin n)) (x : Bool) (t : Fin (n+1)) =>
    Bool.xor x (decide ((S.filter (fun s => s.val < t.val)).card % 2 = 1))
  let toll := fun (S : Finset (Fin n)) (birth want : Bool) =>
    if want ≠ birth ∨ (∃ i, switches i = S ∧ W i 0 ≠ birth) then 1 else 0
  let leaf := fun (S : Finset (Fin n)) (z : Bool) (k : Nat) =>
    S.card = 1 ∧ toll S false z ≤ k
  let tree := Nat.rec (motive := fun _ => Finset (Fin n) → Bool → Nat → Prop) leaf
    (fun _ child S z k => leaf S z k ∨
      ∃ (A B : Finset (Fin n)) (x y op : Bool) (ka kb : Fin (k+1)),
        A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ A ∪ B = S ∧
        (∀ i, switches i ⊆ S → switches i ≠ S → switches i ⊆ A ∨ switches i ⊆ B) ∧
        let gate := fun (v w : Bool) => if op then (v && w) else (v || w)
        (∀ t, gate (trace A x t) (trace B y t) = trace S (gate x y) t) ∧
        child A x ka.val ∧ child B y kb.val ∧ ka.val+kb.val+toll S (gate x y) z ≤ k) (n-1)
  tree Finset.univ (W 0 0) b ↔
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin (a+1) → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ n-1 ∧ PEqualNP.NotBracket.notCount C ≤ b ∧
      ∀ t i, (C.wires (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD
        (tap i) false = W i t) := by
  intro n a b W hn switches hsw0 trace toll leaf tree
  have htreeEq : tree Finset.univ (W 0 0) b ↔ treeFn W (n - 1) Finset.univ (W 0 0) b := Iff.rfl
  rw [htreeEq]
  constructor
  · intro hTree
    obtain ⟨gs, hFan, hBack, hPos, hNot, _, hTap⟩ :=
      build_from_tree W (n - 1) Finset.univ (W 0 0) b []
        (by simp [PEqualNP.MetaComplexity.FanInTwo])
        (by simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]) hTree
    simp only [List.nil_append, posCount, List.filter_nil, List.length_nil, zero_add,
      Finset.card_univ, Fintype.card_fin] at hFan hBack hPos hNot hTap
    have hTapAll : ∀ i : Fin (a + 1), ∃ p < n + 2 + gs.length, ∀ t, wval n gs p t = W i t := by
      intro i
      by_cases hne : (swOf (W i)).Nonempty
      · exact hTap i (Finset.subset_univ _) hne
      · have hemp : swOf (W i) = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hconst : ∀ t, W i t = W i 0 := by
          intro t
          rw [eq_traceFn_swOf (W i) t, hemp]
          have h0 : (∅ : Finset (Fin n)).filter (fun s => s.val < t.val) = ∅ := by simp
          simp [traceFn, h0]
        cases h0 : W i 0
        · exact ⟨n, by omega, fun t => by rw [wval_false, hconst t, h0]⟩
        · exact ⟨n + 1, by omega, fun t => by rw [wval_true, hconst t, h0]⟩
    choose tap htapLt htapVal using hTapAll
    refine ⟨⟨gs, 0⟩, tap, hFan, hBack, by change 0 < n + 2 + gs.length; omega,
      htapLt, ?_, ?_, fun t i => htapVal i t⟩
    · rw [size_sub_notCount]
      exact hPos
    · simpa [PEqualNP.NotBracket.notCount] using hNot
  · rintro ⟨C, tap, hFan, hBack, _, hTapLt, hPosLe, hNotLe, hTapVal⟩
    have hPosLe' : posCount C.gates ≤ n - 1 := by
      rw [← size_sub_notCount]; exact hPosLe
    have hswTap0 : swOf (wval n C.gates (tap 0)) = Finset.univ := by
      have : wval n C.gates (tap 0) = W 0 := funext (fun t => hTapVal t 0)
      rw [this]; exact hsw0
    have hne0 : (swOf (wval n C.gates (tap 0))).Nonempty := by
      rw [hswTap0]
      exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    let r0 := rootOf n C.gates hBack (tap 0)
    have hr0Skel : r0 ∈ skelWires n C.gates :=
      rootOf_mem_skel_of_sw_nonempty n C.gates hBack (hTapLt 0) hne0
    have hswR0 : swOf (wval n C.gates r0) = Finset.univ := by
      rw [← swOf_rootOf n C.gates hBack (tap 0)]; exact hswTap0
    have hLeafR0 : coneLeaf n C.gates hBack r0 = Finset.univ := by
      apply Finset.Subset.antisymm (Finset.subset_univ _)
      rw [← hswR0]
      exact swOf_sub_coneLeaf n C.gates hBack hr0Skel
    obtain ⟨_, hPosCard, hChTwo, hUniq, hConeEq⟩ :=
      tight_tree_facts n C.gates hFan hBack hPosLe' hn r0 hr0Skel hLeafR0
    have hSwAll : ∀ v ∈ skelWires n C.gates, swOf (wval n C.gates v) = coneLeaf n C.gates hBack v := by
      intro v hv
      exact swOf_eq_coneLeaf_all n C.gates hBack hChTwo hUniq r0 hr0Skel (by rw [hswR0, hLeafR0])
        v (hConeEq.symm ▸ hv)
    have hBud : notBudget n C.gates hBack r0 ≤ b :=
      (notBudget_le_notCount n C.gates hBack r0).trans hNotLe
    have hEx := extract_tree W C.gates tap hFan hBack hTapLt hTapVal hChTwo hUniq hSwAll
      (n - 1) r0 (tap 0) b hr0Skel (hTapLt 0) rfl (le_of_eq hPosCard) hBud
    rw [hLeafR0, show wval n C.gates (tap 0) 0 = W 0 0 from hTapVal 0 0] at hEx
    exact hEx
