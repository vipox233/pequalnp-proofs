import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33622_aux.Classify

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

lemma isNotOp_eq_true_iff (op : GateOp) : isNotOp op = true ↔ op = .not := by
  cases op <;> simp [isNotOp]

def legalC (N h : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N + N + h) C ∧ C.output < N + N + h + C.size ∧
  ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
    (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))

def inpVec {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) : List Bool :=
  oneEach x y ++ List.ofFn w

def tableC (N h : ℕ) (C : Circuit) (w : Fin h → Bool) (x y : Fin N) : Bool :=
  C.eval (inpVec w x y)

def areaC {N : ℕ} (H : Fin N → Fin N → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true)).card

def lineUnionC (N h : ℕ) (C : Circuit) (R S : Finset (Fin N)) : Prop :=
  ∀ (w : Fin h → Bool) (x y : Fin N), tableC N h C w x y = decide (x ∈ R ∨ y ∈ S)

lemma inpVec_length {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) :
    (inpVec w x y).length = N + N + h := by
  simp [inpVec, oneEach, Nat.add_assoc]

lemma foldl_wires_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_prefix (gs : List Gate) (init : List Bool) (k : ℕ) (hk : k < init.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD k false =
      init.getD k false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
      simp; omega
    rw [ih _ hk', List.getD_eq_getElem _ _ hk', List.getElem_append_left hk, List.getD_eq_getElem _ _ hk]

lemma foldl_wires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨.or, []⟩).inputs, i < init.length + k) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD (init.length + j) false =
      (gs.getD j ⟨.or, []⟩).op.eval
        ((gs.getD j ⟨.or, []⟩).inputs.map fun i =>
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD i false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, add_zero, List.getD_cons_zero]
      have hlen : init.length < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
        simp
      rw [foldl_wires_getD_prefix gs _ init.length hlen]
      rw [List.getD_eq_getElem _ _ hlen, List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < init.length := by
        have := hback 0 (by simp) i (by simpa using hi)
        omega
      have hilt' : i < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
        simp; omega
      rw [foldl_wires_getD_prefix gs _ i hilt', List.getD_eq_getElem _ _ hilt',
        List.getElem_append_left hilt, List.getD_eq_getElem _ _ hilt]
    | succ j =>
      simp only [List.foldl_cons, List.getD_cons_succ]
      let init' := init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]
      have hlen' : init'.length = init.length + 1 := by simp [init']
      have hidx : init.length + (j + 1) = init'.length + j := by omega
      rw [hidx]
      have hj' : j < gs.length := by simp at hj; omega
      have hback' : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨.or, []⟩).inputs, i < init'.length + k := by
        intro k hk i hi
        have := hback (k + 1) (by simp; omega) i (by simpa using hi)
        omega
      exact ih init' j hj' hback'

def wireVal (C : Circuit) (inp : List Bool) (w : ℕ) : Bool :=
  (C.wires inp).getD w false

lemma wireVal_input {n : ℕ} (C : Circuit) (inp : List Bool) (hinp : inp.length = n)
    (w : ℕ) (hw : w < n) :
    wireVal C inp w = inp.getD w false := by
  unfold wireVal Circuit.wires
  exact foldl_wires_getD_prefix C.gates inp w (by omega)

lemma wireVal_gate {n : ℕ} (C : Circuit) (hread : ReadsBack n C) (inp : List Bool) (hinp : inp.length = n)
    (w : ℕ) (hw1 : n ≤ w) (hw2 : w - n < C.gates.length) :
    wireVal C inp w = (gateAt C (w - n)).op.eval ((gateAt C (w - n)).inputs.map (wireVal C inp)) := by
  have heq : w = inp.length + (w - n) := by omega
  unfold wireVal Circuit.wires
  conv_lhs => rw [heq]
  have hback : ∀ k < C.gates.length, ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < inp.length + k := by
    intro k hk i hi; rw [hinp]; exact hread k hk i hi
  exact foldl_wires_getD_gate C.gates inp (w - n) hw2 hback

lemma inpVec_getD_row {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) (i : ℕ) (hi : i < N) :
    (inpVec w x y).getD i false = decide (⟨i, hi⟩ = x) := by
  unfold inpVec oneEach
  have hlen : i < ((List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))) ++ List.ofFn w).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : i < (List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))).length := by
    simp; omega
  rw [List.getElem_append_left h1]
  have h2 : i < (List.ofFn (fun k : Fin N => decide (k = x))).length := by simp; omega
  rw [List.getElem_append_left h2, List.getElem_ofFn]

lemma inpVec_getD_col {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) (i : ℕ) (hi1 : N ≤ i) (hi2 : i < N + N) :
    (inpVec w x y).getD i false = decide (⟨i - N, by omega⟩ = y) := by
  unfold inpVec oneEach
  have hlen : i < ((List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))) ++ List.ofFn w).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : i < (List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))).length := by
    simp; omega
  rw [List.getElem_append_left h1]
  have h2 : (List.ofFn (fun k : Fin N => decide (k = x))).length ≤ i := by simp; omega
  rw [List.getElem_append_right h2]
  simp only [List.length_ofFn, List.getElem_ofFn]

lemma inpVec_getD_seed {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) (i : ℕ)
    (hi1 : N + N ≤ i) (hi2 : i < N + N + h) :
    (inpVec w x y).getD i false = w ⟨i - (N + N), by omega⟩ := by
  unfold inpVec oneEach
  have hlen : i < ((List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))) ++ List.ofFn w).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : (List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))).length ≤ i := by
    simp; omega
  rw [List.getElem_append_right h1]
  simp only [List.length_append, List.length_ofFn, List.getElem_ofFn]

def reachWires (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if _ : n ≤ w ∧ w - n < C.gates.length then
    insert w (((gateAt C (w - n)).inputs.filter (· < w)).attach.foldr
      (fun u acc => reachWires n C u.1 ∪ acc) ∅)
  else {w}
termination_by w
decreasing_by
  have hu := (List.mem_filter.mp u.2).2
  exact of_decide_eq_true hu

lemma self_mem_reachWires (n : ℕ) (C : Circuit) (w : ℕ) : w ∈ reachWires n C w := by
  rw [reachWires]
  split_ifs
  · exact Finset.mem_insert_self w _
  · exact Finset.mem_singleton_self w

lemma mem_foldr_union {α : Type*} [DecidableEq α] (l : List α) (f : α → Finset ℕ) (x : ℕ) :
    x ∈ l.foldr (fun a acc => f a ∪ acc) ∅ ↔ ∃ a ∈ l, x ∈ f a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hxb⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hxb⟩
    · rintro ⟨b, rfl | hb, hxb⟩
      · exact Or.inl hxb
      · exact Or.inr ⟨b, hb, hxb⟩

lemma mem_reachWires_iff {n : ℕ} {C : Circuit} (hread : ReadsBack n C) (w v : ℕ) :
    v ∈ reachWires n C w ↔
      v = w ∨ (n ≤ w ∧ w - n < C.gates.length ∧ ∃ u ∈ (gateAt C (w - n)).inputs, v ∈ reachWires n C u) := by
  rw [reachWires]
  split_ifs with hw
  · rw [Finset.mem_insert, mem_foldr_union]
    constructor
    · rintro (rfl | ⟨⟨u, hu⟩, _, hvu⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hw.1, hw.2, u, (List.mem_filter.mp hu).1, hvu⟩
    · rintro (rfl | ⟨_, _, u, hu, hvu⟩)
      · exact Or.inl rfl
      · have hult : u < w := by
          have := hread (w - n) hw.2 u hu; omega
        have huf : u ∈ (gateAt C (w - n)).inputs.filter (· < w) :=
          List.mem_filter.mpr ⟨hu, decide_eq_true hult⟩
        exact Or.inr ⟨⟨u, huf⟩, List.mem_attach _ _, hvu⟩
  · simp only [Finset.mem_singleton, iff_self_or]
    rintro ⟨h1, h2, _⟩; exact (hw ⟨h1, h2⟩).elim

lemma le_of_mem_reachWires {n : ℕ} {C : Circuit} (hread : ReadsBack n C) :
    ∀ (w v : ℕ), v ∈ reachWires n C w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [mem_reachWires_iff hread] at hv
    rcases hv with rfl | ⟨hw1, hw2, u, hu, hvu⟩
    · exact le_rfl
    · have hult : u < w := by have := hread (w - n) hw2 u hu; omega
      exact le_trans (ih u hult v hvu) (le_of_lt hult)

lemma reachWires_subset_of_mem {n : ℕ} {C : Circuit} (hread : ReadsBack n C) :
    ∀ (w u : ℕ), u ∈ reachWires n C w → reachWires n C u ⊆ reachWires n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    rw [mem_reachWires_iff hread] at hu
    rcases hu with rfl | ⟨hw1, hw2, a, ha, hua⟩
    · exact Finset.Subset.refl _
    · have halt : a < w := by have := hread (w - n) hw2 a ha; omega
      have hsub1 : reachWires n C u ⊆ reachWires n C a := ih a halt u hua
      intro v hv
      rw [mem_reachWires_iff hread]
      exact Or.inr ⟨hw1, hw2, a, ha, hsub1 hv⟩

lemma reachWires_lt_bound {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    ∀ v ∈ reachWires n C w, v < n + C.gates.length := by
  intro v hv
  exact lt_of_le_of_lt (le_of_mem_reachWires hread w v hv) hw

lemma wireVal_congr_on_reach {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (inp₁ inp₂ : List Bool) (h1 : inp₁.length = n) (h2 : inp₂.length = n) :
    ∀ (w : ℕ), w < n + C.gates.length →
      (∀ v ∈ reachWires n C w, v < n → inp₁.getD v false = inp₂.getD v false) →
      wireVal C inp₁ w = wireVal C inp₂ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hagree
    by_cases hlt : w < n
    · rw [wireVal_input C inp₁ h1 w hlt, wireVal_input C inp₂ h2 w hlt]
      exact hagree w (self_mem_reachWires n C w) hlt
    · have hw1 : n ≤ w := Nat.le_of_not_lt hlt
      have hw2 : w - n < C.gates.length := by omega
      rw [wireVal_gate C hread inp₁ h1 w hw1 hw2, wireVal_gate C hread inp₂ h2 w hw1 hw2]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hult : u < w := by have := hread (w - n) hw2 u hu; omega
      have husub : reachWires n C u ⊆ reachWires n C w :=
        reachWires_subset_of_mem hread w u
          ((mem_reachWires_iff hread w u).mpr (Or.inr ⟨hw1, hw2, u, hu, self_mem_reachWires n C u⟩))
      exact ih u hult (by omega) (fun v hv hvn => hagree v (husub hv) hvn)

lemma gateOp_and_mono (l₁ l₂ : List Bool) (h : List.Forall₂ (fun a b => a = true → b = true) l₁ l₂) :
    GateOp.eval .and l₁ = true → GateOp.eval .and l₂ = true := by
  induction h with
  | nil => intro _; rfl
  | cons hab _ ih =>
    simp only [GateOp.eval, List.all_cons, id_eq, Bool.and_eq_true]
    intro ⟨ha, hl⟩
    exact ⟨hab ha, ih hl⟩

lemma gateOp_or_mono (l₁ l₂ : List Bool) (h : List.Forall₂ (fun a b => a = true → b = true) l₁ l₂) :
    GateOp.eval .or l₁ = true → GateOp.eval .or l₂ = true := by
  induction h with
  | nil => intro h; cases h
  | cons hab _ ih =>
    simp only [GateOp.eval, List.any_cons, id_eq, Bool.or_eq_true]
    rintro (ha | hl)
    · exact Or.inl (hab ha)
    · exact Or.inr (ih hl)

lemma wireVal_mono_on_reach {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (inp₁ inp₂ : List Bool) (h1 : inp₁.length = n) (h2 : inp₂.length = n) :
    ∀ (w : ℕ), w < n + C.gates.length →
      (∀ u ∈ reachWires n C w, n ≤ u → (gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or) →
      (∀ v ∈ reachWires n C w, v < n → inp₁.getD v false = true → inp₂.getD v false = true) →
      wireVal C inp₁ w = true → wireVal C inp₂ w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmon hle hval
    by_cases hlt : w < n
    · rw [wireVal_input C inp₁ h1 w hlt] at hval
      rw [wireVal_input C inp₂ h2 w hlt]
      exact hle w (self_mem_reachWires n C w) hlt hval
    · have hw1 : n ≤ w := Nat.le_of_not_lt hlt
      have hw2 : w - n < C.gates.length := by omega
      rw [wireVal_gate C hread inp₁ h1 w hw1 hw2] at hval
      rw [wireVal_gate C hread inp₂ h2 w hw1 hw2]
      have hpair : List.Forall₂ (fun a b => a = true → b = true)
          ((gateAt C (w - n)).inputs.map (wireVal C inp₁))
          ((gateAt C (w - n)).inputs.map (wireVal C inp₂)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
        intro u hu
        have hult : u < w := by have := hread (w - n) hw2 u hu; omega
        have husub : reachWires n C u ⊆ reachWires n C w :=
          reachWires_subset_of_mem hread w u
            ((mem_reachWires_iff hread w u).mpr (Or.inr ⟨hw1, hw2, u, hu, self_mem_reachWires n C u⟩))
        exact ih u hult (by omega) (fun z hz hzn => hmon z (husub hz) hzn)
          (fun v hv hvn => hle v (husub hv) hvn)
      rcases hmon w (self_mem_reachWires n C w) hw1 with hop | hop
      · rw [hop] at hval ⊢; exact gateOp_and_mono _ _ hpair hval
      · rw [hop] at hval ⊢; exact gateOp_or_mono _ _ hpair hval

lemma wireVal_false_of_all_false {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (inp : List Bool) (hinp : inp.length = n) :
    ∀ (w : ℕ), w < n + C.gates.length →
      (∀ u ∈ reachWires n C w, n ≤ u →
        ((gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or) ∧
        (gateAt C (u - n)).inputs ≠ []) →
      (∀ v ∈ reachWires n C w, v < n → inp.getD v false = false) →
      wireVal C inp w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmon hzero
    by_cases hlt : w < n
    · rw [wireVal_input C inp hinp w hlt]
      exact hzero w (self_mem_reachWires n C w) hlt
    · have hw1 : n ≤ w := Nat.le_of_not_lt hlt
      have hw2 : w - n < C.gates.length := by omega
      rw [wireVal_gate C hread inp hinp w hw1 hw2]
      have hgate := hmon w (self_mem_reachWires n C w) hw1
      have hmap : ∀ u ∈ (gateAt C (w - n)).inputs, wireVal C inp u = false := by
        intro u hu
        have hult : u < w := by have := hread (w - n) hw2 u hu; omega
        have husub : reachWires n C u ⊆ reachWires n C w :=
          reachWires_subset_of_mem hread w u
            ((mem_reachWires_iff hread w u).mpr (Or.inr ⟨hw1, hw2, u, hu, self_mem_reachWires n C u⟩))
        exact ih u hult (by omega) (fun z hz hzn => hmon z (husub hz) hzn)
          (fun v hv hvn => hzero v (husub hv) hvn)
      rcases hgate with ⟨hop | hop, hne⟩
      · rw [hop]
        cases hins : (gateAt C (w - n)).inputs with
        | nil => exact (hne hins).elim
        | cons a rest =>
          have ha : wireVal C inp a = false := hmap a (by rw [hins]; exact List.mem_cons_self)
          simp [GateOp.eval, ha]
      · rw [hop]
        simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq]
        rintro b ⟨u, hu, rfl⟩
        simp [hmap u hu]

def readsW (n : ℕ) (C : Circuit) (G : Finset ℕ) (v : ℕ) : ℕ :=
  ∑ u ∈ G, (gateAt C (u - n)).inputs.count v

lemma readsW_pos_of_mem_ne {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (v : ℕ) (hv : v ∈ reachWires n C w) (hne : v ≠ w) :
    1 ≤ readsW n C ((reachWires n C w).filter (n ≤ ·)) v := by
  have hex : ∀ (z : ℕ), v ∈ reachWires n C z → v ≠ z →
      ∃ u ∈ (reachWires n C z).filter (n ≤ ·), v ∈ (gateAt C (u - n)).inputs := by
    intro z
    induction z using Nat.strong_induction_on with
    | ind z ih =>
      intro hvz hvnz
      rw [mem_reachWires_iff hread] at hvz
      rcases hvz with rfl | ⟨hz1, hz2, a, ha, hva⟩
      · exact (hvnz rfl).elim
      · by_cases hva_eq : v = a
        · subst hva_eq
          exact ⟨z, Finset.mem_filter.mpr ⟨self_mem_reachWires n C z, hz1⟩, ha⟩
        · have halt : a < z := by have := hread (z - n) hz2 a ha; omega
          obtain ⟨u, hu, hvu⟩ := ih a halt hva hva_eq
          have hasub : reachWires n C a ⊆ reachWires n C z :=
            reachWires_subset_of_mem hread z a
              ((mem_reachWires_iff hread z a).mpr (Or.inr ⟨hz1, hz2, a, ha, self_mem_reachWires n C a⟩))
          exact ⟨u, Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩, hvu⟩
  obtain ⟨u, hu, hvu⟩ := hex w hv hne
  have h1 : 1 ≤ (gateAt C (u - n)).inputs.count v := List.count_pos_iff.mpr hvu
  have h2 : (gateAt C (u - n)).inputs.count v ≤ readsW n C ((reachWires n C w).filter (n ≤ ·)) v :=
    Finset.single_le_sum (f := fun z => (gateAt C (z - n)).inputs.count v) (fun _ _ => Nat.zero_le _) hu
  omega

lemma list_length_eq_sum_count {α : Type*} [DecidableEq α] (l : List α) (S : Finset α)
    (hsub : ∀ x ∈ l, x ∈ S) :
    l.length = ∑ x ∈ S, l.count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ S := hsub a List.mem_cons_self
    have hl : ∀ x ∈ l, x ∈ S := fun x hx => hsub x (List.mem_cons_of_mem a hx)
    rw [List.length_cons, ih hl]
    have hsplit : ∀ x ∈ S, (a :: l).count x = l.count x + (if x = a then 1 else 0) := by
      intro x _
      rw [List.count_cons]
      by_cases hxa : x = a
      · subst hxa; simp
      · have hax : a ≠ x := Ne.symm hxa; simp [hxa, hax]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' S a, if_pos ha]

lemma sum_inputs_eq_sum_reads {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    let V := reachWires n C w
    let G := V.filter (n ≤ ·)
    ∑ u ∈ G, (gateAt C (u - n)).inputs.length = ∑ v ∈ V.erase w, readsW n C G v := by
  intro V G
  have hlen : ∀ u ∈ G, (gateAt C (u - n)).inputs.length =
      ∑ v ∈ V.erase w, (gateAt C (u - n)).inputs.count v := by
    intro u hu
    apply list_length_eq_sum_count
    intro v hv
    have huV : u ∈ V := (Finset.mem_filter.mp hu).1
    have hun : n ≤ u := (Finset.mem_filter.mp hu).2
    have hult : u - n < C.gates.length := by
      have := le_of_mem_reachWires hread w u huV; omega
    have hvlt : v < u := by have := hread (u - n) hult v hv; omega
    have hule : u ≤ w := le_of_mem_reachWires hread w u huV
    have hvne : v ≠ w := by omega
    have hvV : v ∈ V := by
      have hsub := reachWires_subset_of_mem hread w u huV
      exact hsub ((mem_reachWires_iff hread u v).mpr (Or.inr ⟨hun, hult, v, hv, self_mem_reachWires n C v⟩))
    exact Finset.mem_erase.mpr ⟨hvne, hvV⟩
  rw [Finset.sum_congr rfl hlen, Finset.sum_comm]
  rfl

lemma accounting_ineq {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (hleg : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (w : ℕ) (hw : w < n + C.gates.length) :
    let V := reachWires n C w
    let G := V.filter (n ≤ ·)
    let I := V.filter (· < n)
    let n0 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 0)).card
    let n1 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false)).card
    let nnot := (G.filter (fun u => isNotOp (gateAt C (u - n)).op = true)).card
    I.card + 2 * n0 + n1 + nnot ≤ G.card + 1 ∧
      (I.card + 2 * n0 + n1 + nnot = G.card + 1 →
        ∀ v ∈ V.erase w, readsW n C G v = 1) := by
  intro V G I n0 n1 nnot
  have hVpart : V.card = G.card + I.card := by
    have hdisj : Disjoint G I := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
    have hunion : G ∪ I = V := by
      ext x; simp only [G, I, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx; by_cases h : n ≤ x
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hgate_mem : ∀ u ∈ G, gateAt C (u - n) ∈ C.gates := by
    intro u hu
    have huV := (Finset.mem_filter.mp hu).1
    have hun := (Finset.mem_filter.mp hu).2
    have hult : u - n < C.gates.length := by
      have := le_of_mem_reachWires hread w u huV; omega
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hult]
    exact List.getElem_mem hult
  have hslot_formula : ∑ u ∈ G, (gateAt C (u - n)).inputs.length + 2 * n0 + n1 + nnot = 2 * G.card := by
    have hpt : ∀ u ∈ G,
        (gateAt C (u - n)).inputs.length +
        (if (gateAt C (u - n)).inputs.length = 0 then 2 else 0) +
        (if (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false then 1 else 0) +
        (if isNotOp (gateAt C (u - n)).op = true then 1 else 0) = 2 := by
      intro u hu
      rcases hleg _ (hgate_mem u hu) with ⟨hlen, hop | hop | ⟨hop, h1⟩⟩
      · have : (gateAt C (u - n)).inputs.length = 0 ∨ (gateAt C (u - n)).inputs.length = 1 ∨
            (gateAt C (u - n)).inputs.length = 2 := by omega
        rcases this with h | h | h <;> simp [h, hop, isNotOp]
      · have : (gateAt C (u - n)).inputs.length = 0 ∨ (gateAt C (u - n)).inputs.length = 1 ∨
            (gateAt C (u - n)).inputs.length = 2 := by omega
        rcases this with h | h | h <;> simp [h, hop, isNotOp]
      · simp [hop, h1, isNotOp]
    have hsum := Finset.sum_congr rfl hpt
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite,
      Finset.sum_const_zero, add_zero] at hsum
    have h2 : (G.filter (fun u => (gateAt C (u - n)).inputs.length = 0)).card * 2 = 2 * n0 := by
      simp [n0]; ring
    have h1 : (G.filter (fun u => (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false)).card * 1 = n1 := by
      simp [n1]
    have hnot : (G.filter (fun u => isNotOp (gateAt C (u - n)).op = true)).card * 1 = nnot := by
      simp [nnot]
    have hG2 : G.card * 2 = 2 * G.card := by ring
    omega
  have hsum_eq : ∑ u ∈ G, (gateAt C (u - n)).inputs.length = ∑ v ∈ V.erase w, readsW n C G v :=
    sum_inputs_eq_sum_reads hread w hw
  have hge1 : ∀ v ∈ V.erase w, 1 ≤ readsW n C G v := by
    intro v hv
    exact readsW_pos_of_mem_ne hread w v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  have hsum_ge : (V.erase w).card ≤ ∑ v ∈ V.erase w, readsW n C G v := by
    calc (V.erase w).card = ∑ _v ∈ V.erase w, 1 := by simp
      _ ≤ ∑ v ∈ V.erase w, readsW n C G v := Finset.sum_le_sum hge1
  have herase : (V.erase w).card + 1 = V.card := by
    have := Finset.card_erase_add_one (self_mem_reachWires n C w)
    exact this
  constructor
  · omega
  · intro heq v hv
    have hsum_tight : ∑ x ∈ V.erase w, readsW n C G x = ∑ _x ∈ V.erase w, 1 := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one]; omega
    by_contra hne
    have hgt : 2 ≤ readsW n C G v := by have := hge1 v hv; omega
    have hstrict : ∑ _x ∈ V.erase w, 1 < ∑ x ∈ V.erase w, readsW n C G x :=
      Finset.sum_lt_sum hge1 ⟨v, hv, by omega⟩
    omega

lemma disjoint_children_of_reads_one {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hreads : ∀ v ∈ (reachWires n C w).erase w, readsW n C ((reachWires n C w).filter (n ≤ ·)) v = 1)
    (u a b : ℕ) (hu : u ∈ (reachWires n C w).filter (n ≤ ·))
    (hins : (gateAt C (u - n)).inputs = [a, b]) :
    Disjoint (reachWires n C a) (reachWires n C b) := by
  let V := reachWires n C w
  let G := V.filter (n ≤ ·)
  have huV : u ∈ V := (Finset.mem_filter.mp hu).1
  have hun : n ≤ u := (Finset.mem_filter.mp hu).2
  have hult : u - n < C.gates.length := by
    have := le_of_mem_reachWires hread w u huV; omega
  have ha_in : a ∈ (gateAt C (u - n)).inputs := by rw [hins]; exact List.mem_cons_self
  have hb_in : b ∈ (gateAt C (u - n)).inputs := by rw [hins]; exact List.mem_cons_of_mem a List.mem_cons_self
  have halt : a < u := by have := hread (u - n) hult a ha_in; omega
  have hblt : b < u := by have := hread (u - n) hult b hb_in; omega
  have hule : u ≤ w := le_of_mem_reachWires hread w u huV
  have hasub : reachWires n C a ⊆ V :=
    reachWires_subset_of_mem hread w a
      (reachWires_subset_of_mem hread w u huV
        ((mem_reachWires_iff hread u a).mpr (Or.inr ⟨hun, hult, a, ha_in, self_mem_reachWires n C a⟩)))
  have hbsub : reachWires n C b ⊆ V :=
    reachWires_subset_of_mem hread w b
      (reachWires_subset_of_mem hread w u huV
        ((mem_reachWires_iff hread u b).mpr (Or.inr ⟨hun, hult, b, hb_in, self_mem_reachWires n C b⟩)))
  have hab : a ≠ b := by
    intro heq; subst heq
    have ha_er : a ∈ V.erase w := Finset.mem_erase.mpr ⟨by omega, hasub (self_mem_reachWires n C a)⟩
    have h1 : readsW n C G a = 1 := hreads a ha_er
    have h2 : (gateAt C (u - n)).inputs.count a ≤ readsW n C G a :=
      Finset.single_le_sum (f := fun z => (gateAt C (z - n)).inputs.count a) (fun _ _ => Nat.zero_le _) hu
    rw [hins] at h2
    simp at h2; omega
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hne
  have hne' : (reachWires n C a ∩ reachWires n C b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨m, hm_mem, hm_max⟩ : ∃ m ∈ reachWires n C a ∩ reachWires n C b,
      ∀ z ∈ reachWires n C a ∩ reachWires n C b, z ≤ m :=
    ⟨(reachWires n C a ∩ reachWires n C b).max' hne', Finset.max'_mem _ hne',
      fun z hz => Finset.le_max' _ z hz⟩
  have hma : m ∈ reachWires n C a := (Finset.mem_inter.mp hm_mem).1
  have hmb : m ∈ reachWires n C b := (Finset.mem_inter.mp hm_mem).2
  have hm_er : m ∈ V.erase w := by
    have hmle : m ≤ a := le_of_mem_reachWires hread a m hma
    exact Finset.mem_erase.mpr ⟨by omega, hasub hma⟩
  have hrm : readsW n C G m = 1 := hreads m hm_er
  have hfind : ∀ (r : ℕ), m ∈ reachWires n C r → m ≠ r →
      ∃ p ∈ (reachWires n C r).filter (n ≤ ·), m ∈ (gateAt C (p - n)).inputs := by
    intro r hmr hmne
    have hpos := readsW_pos_of_mem_ne hread r m hmr hmne
    by_contra hnone; push Not at hnone
    have hz : readsW n C ((reachWires n C r).filter (n ≤ ·)) m = 0 := by
      unfold readsW
      apply Finset.sum_eq_zero; intro p hp
      exact List.count_eq_zero.mpr (hnone p hp)
    omega
  by_cases hma_eq : m = a
  · subst hma_eq
    have hmb_ne : m ≠ b := hab
    obtain ⟨p, hp, hmp⟩ := hfind b hmb hmb_ne
    have hpG : p ∈ G := Finset.mem_filter.mpr ⟨hbsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have hpu : p ≠ u := by
      have := le_of_mem_reachWires hread b p (Finset.mem_filter.mp hp).1; omega
    have h2 : (gateAt C (u - n)).inputs.count m + (gateAt C (p - n)).inputs.count m ≤ readsW n C G m := by
      have hpair : {u, p} ⊆ G := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      have hle := Finset.sum_le_sum_of_subset (f := fun z => (gateAt C (z - n)).inputs.count m) hpair
      rw [Finset.sum_pair hpu.symm] at hle
      exact hle
    have hc1 : 1 ≤ (gateAt C (u - n)).inputs.count m := List.count_pos_iff.mpr ha_in
    have hc2 : 1 ≤ (gateAt C (p - n)).inputs.count m := List.count_pos_iff.mpr hmp
    omega
  · by_cases hmb_eq : m = b
    · subst hmb_eq
      obtain ⟨p, hp, hmp⟩ := hfind a hma hma_eq
      have hpG : p ∈ G := Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
      have hpu : p ≠ u := by
        have := le_of_mem_reachWires hread a p (Finset.mem_filter.mp hp).1; omega
      have h2 : (gateAt C (u - n)).inputs.count m + (gateAt C (p - n)).inputs.count m ≤ readsW n C G m := by
        have hpair : {u, p} ⊆ G := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
        have hle := Finset.sum_le_sum_of_subset (f := fun z => (gateAt C (z - n)).inputs.count m) hpair
        rw [Finset.sum_pair hpu.symm] at hle
        exact hle
      have hc1 : 1 ≤ (gateAt C (u - n)).inputs.count m := List.count_pos_iff.mpr hb_in
      have hc2 : 1 ≤ (gateAt C (p - n)).inputs.count m := List.count_pos_iff.mpr hmp
      omega
    · obtain ⟨p1, hp1, hmp1⟩ := hfind a hma hma_eq
      obtain ⟨p2, hp2, hmp2⟩ := hfind b hmb hmb_eq
      by_cases hp12 : p1 = p2
      · subst hp12
        have hp_inter : p1 ∈ reachWires n C a ∩ reachWires n C b :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp1).1, (Finset.mem_filter.mp hp2).1⟩
        have hle_max : p1 ≤ m := hm_max p1 hp_inter
        have hp1n : n ≤ p1 := (Finset.mem_filter.mp hp1).2
        have hp1lt : p1 - n < C.gates.length := by
          have := le_of_mem_reachWires hread a p1 (Finset.mem_filter.mp hp1).1; omega
        have hmlt : m < p1 := by have := hread (p1 - n) hp1lt m hmp1; omega
        omega
      · have hp1G : p1 ∈ G := Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hp1).1, (Finset.mem_filter.mp hp1).2⟩
        have hp2G : p2 ∈ G := Finset.mem_filter.mpr ⟨hbsub (Finset.mem_filter.mp hp2).1, (Finset.mem_filter.mp hp2).2⟩
        have h2 : (gateAt C (p1 - n)).inputs.count m + (gateAt C (p2 - n)).inputs.count m ≤ readsW n C G m := by
          have hpair : {p1, p2} ⊆ G := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
          have hle := Finset.sum_le_sum_of_subset (f := fun z => (gateAt C (z - n)).inputs.count m) hpair
          rw [Finset.sum_pair hp12] at hle
          exact hle
        have hc1 : 1 ≤ (gateAt C (p1 - n)).inputs.count m := List.count_pos_iff.mpr hmp1
        have hc2 : 1 ≤ (gateAt C (p2 - n)).inputs.count m := List.count_pos_iff.mpr hmp2
        omega

lemma area_le_of_subset {N : ℕ} (H₁ H₂ : Fin N → Fin N → Bool)
    (h : ∀ x y, H₁ x y = true → H₂ x y = true) :
    areaC H₁ ≤ areaC H₂ := by
  apply Finset.card_le_card
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨Finset.mem_univ z, h z.1 z.2 hz.2⟩

lemma area_or_le {N : ℕ} (H₁ H₂ : Fin N → Fin N → Bool) :
    areaC (fun x y => H₁ x y || H₂ x y) ≤ areaC H₁ + areaC H₂ := by
  have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (H₁ z.1 z.2 || H₂ z.1 z.2) = true) ⊆
      (Finset.univ.filter (fun z => H₁ z.1 z.2 = true)) ∪ (Finset.univ.filter (fun z => H₂ z.1 z.2 = true)) := by
    intro z hz
    rw [Finset.mem_filter, Bool.or_eq_true] at hz
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hz.2 with h1 | h2
    · exact Or.inl ⟨Finset.mem_univ z, h1⟩
    · exact Or.inr ⟨Finset.mem_univ z, h2⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

lemma area_ge_of_unnamed_true {N : ℕ} (H : Fin N → Fin N → Bool) (R S : Finset (Fin N))
    (h : ∀ x y, x ∉ R → y ∉ S → H x y = true) :
    (N - R.card) * (N - S.card) ≤ areaC H := by
  have hsub : Rᶜ ×ˢ Sᶜ ⊆ (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true) := by
    intro z hz
    rcases Finset.mem_product.mp hz with ⟨hx, hy⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ z, h z.1 z.2 (Finset.mem_compl.mp hx) (Finset.mem_compl.mp hy)⟩
  have hcard : (Rᶜ ×ˢ Sᶜ).card = (N - R.card) * (N - S.card) := by
    rw [Finset.card_product, Finset.card_compl, Finset.card_compl, Fintype.card_fin]
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma area_le_of_lines {N : ℕ} (H : Fin N → Fin N → Bool) (R S : Finset (Fin N))
    (h : ∀ x y, H x y = true → x ∈ R ∨ y ∈ S) :
    areaC H ≤ (R.card + S.card) * N := by
  have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true) ⊆
      (R ×ˢ (Finset.univ : Finset (Fin N))) ∪ ((Finset.univ : Finset (Fin N)) ×ˢ S) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product]
    rcases h z.1 z.2 hz.2 with hr | hs
    · exact Or.inl ⟨hr, Finset.mem_univ z.2⟩
    · exact Or.inr ⟨Finset.mem_univ z.1, hs⟩
  have hle := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin] at hle
  have hrw : R.card * N + N * S.card = (R.card + S.card) * N := by ring
  rw [hrw] at hle; exact hle

lemma mul_compl_ge {N r s : ℕ} (hrs : r + s ≤ N) :
    N * (N - (r + s)) ≤ (N - r) * (N - s) := by
  let a := N - (r + s)
  have hN : N = a + r + s := by omega
  have hr : N - r = a + s := by omega
  have hs : N - s = a + r := by omega
  rw [hr, hs]
  have heq : (a + s) * (a + r) = (a + r + s) * a + r * s := by ring
  rw [heq, ← hN]
  exact Nat.le_add_right _ _

inductive BTree (N h : ℕ) where
  | row (x : Fin N)
  | col (y : Fin N)
  | seed (j : Fin h)
  | not (t : BTree N h)
  | and (t₁ t₂ : BTree N h)
  | or (t₁ t₂ : BTree N h)

def BTree.evalRaw {N h : ℕ} : BTree N h → (Fin N → Bool) → (Fin N → Bool) → (Fin h → Bool) → Bool
  | .row x, rx, _, _ => rx x
  | .col y, _, cy, _ => cy y
  | .seed j, _, _, w => w j
  | .not t, rx, cy, w => !(t.evalRaw rx cy w)
  | .and t₁ t₂, rx, cy, w => t₁.evalRaw rx cy w && t₂.evalRaw rx cy w
  | .or t₁ t₂, rx, cy, w => t₁.evalRaw rx cy w || t₂.evalRaw rx cy w

def BTree.eval {N h : ℕ} (t : BTree N h) (w : Fin h → Bool) (x y : Fin N) : Bool :=
  t.evalRaw (fun i => decide (i = x)) (fun j => decide (j = y)) w

def BTree.rows {N h : ℕ} : BTree N h → Finset (Fin N)
  | .row x => {x}
  | .col _ => ∅
  | .seed _ => ∅
  | .not t => t.rows
  | .and t₁ t₂ => t₁.rows ∪ t₂.rows
  | .or t₁ t₂ => t₁.rows ∪ t₂.rows

def BTree.cols {N h : ℕ} : BTree N h → Finset (Fin N)
  | .row _ => ∅
  | .col y => {y}
  | .seed _ => ∅
  | .not t => t.cols
  | .and t₁ t₂ => t₁.cols ∪ t₂.cols
  | .or t₁ t₂ => t₁.cols ∪ t₂.cols

def BTree.seeds {N h : ℕ} : BTree N h → Finset (Fin h)
  | .row _ => ∅
  | .col _ => ∅
  | .seed j => {j}
  | .not t => t.seeds
  | .and t₁ t₂ => t₁.seeds ∪ t₂.seeds
  | .or t₁ t₂ => t₁.seeds ∪ t₂.seeds

def BTree.notCount {N h : ℕ} : BTree N h → ℕ
  | .row _ => 0
  | .col _ => 0
  | .seed _ => 0
  | .not t => t.notCount + 1
  | .and t₁ t₂ => t₁.notCount + t₂.notCount
  | .or t₁ t₂ => t₁.notCount + t₂.notCount

def BTree.andCount {N h : ℕ} : BTree N h → ℕ
  | .row _ => 0
  | .col _ => 0
  | .seed _ => 0
  | .not t => t.andCount
  | .and t₁ t₂ => t₁.andCount + t₂.andCount + 1
  | .or t₁ t₂ => t₁.andCount + t₂.andCount

def BTree.lineCount {N h : ℕ} (t : BTree N h) : ℕ :=
  t.rows.card + t.cols.card

def BTree.ReadOnce {N h : ℕ} : BTree N h → Prop
  | .row _ => True
  | .col _ => True
  | .seed _ => True
  | .not t => t.ReadOnce
  | .and t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧
      Disjoint t₁.rows t₂.rows ∧ Disjoint t₁.cols t₂.cols ∧ Disjoint t₁.seeds t₂.seeds
  | .or t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧
      Disjoint t₁.rows t₂.rows ∧ Disjoint t₁.cols t₂.cols ∧ Disjoint t₁.seeds t₂.seeds

lemma BTree.nonempty_leaves {N h : ℕ} (t : BTree N h) :
    t.rows.Nonempty ∨ t.cols.Nonempty ∨ t.seeds.Nonempty := by
  induction t with
  | row x => exact Or.inl ⟨x, Finset.mem_singleton_self x⟩
  | col y => exact Or.inr (Or.inl ⟨y, Finset.mem_singleton_self y⟩)
  | seed j => exact Or.inr (Or.inr ⟨j, Finset.mem_singleton_self j⟩)
  | not t ih => exact ih
  | and t₁ _ ih₁ _ =>
    rcases ih₁ with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨x, Finset.mem_union_left _ hx⟩
    · exact Or.inr (Or.inl ⟨y, Finset.mem_union_left _ hy⟩)
    · exact Or.inr (Or.inr ⟨j, Finset.mem_union_left _ hj⟩)
  | or t₁ _ ih₁ _ =>
    rcases ih₁ with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨x, Finset.mem_union_left _ hx⟩
    · exact Or.inr (Or.inl ⟨y, Finset.mem_union_left _ hy⟩)
    · exact Or.inr (Or.inr ⟨j, Finset.mem_union_left _ hj⟩)

lemma BTree.evalRaw_congr {N h : ℕ} (t : BTree N h)
    (rx₁ rx₂ cy₁ cy₂ : Fin N → Bool) (w₁ w₂ : Fin h → Bool)
    (hr : ∀ x ∈ t.rows, rx₁ x = rx₂ x)
    (hc : ∀ y ∈ t.cols, cy₁ y = cy₂ y)
    (hs : ∀ j ∈ t.seeds, w₁ j = w₂ j) :
    t.evalRaw rx₁ cy₁ w₁ = t.evalRaw rx₂ cy₂ w₂ := by
  induction t with
  | row x => exact hr x (Finset.mem_singleton_self x)
  | col y => exact hc y (Finset.mem_singleton_self y)
  | seed j => exact hs j (Finset.mem_singleton_self j)
  | not t ih =>
    simp only [BTree.evalRaw, ih hr hc hs]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.evalRaw]
    rw [ih₁ (fun x hx => hr x (Finset.mem_union_left _ hx))
            (fun y hy => hc y (Finset.mem_union_left _ hy))
            (fun j hj => hs j (Finset.mem_union_left _ hj)),
        ih₂ (fun x hx => hr x (Finset.mem_union_right _ hx))
            (fun y hy => hc y (Finset.mem_union_right _ hy))
            (fun j hj => hs j (Finset.mem_union_right _ hj))]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.evalRaw]
    rw [ih₁ (fun x hx => hr x (Finset.mem_union_left _ hx))
            (fun y hy => hc y (Finset.mem_union_left _ hy))
            (fun j hj => hs j (Finset.mem_union_left _ hj)),
        ih₂ (fun x hx => hr x (Finset.mem_union_right _ hx))
            (fun y hy => hc y (Finset.mem_union_right _ hy))
            (fun j hj => hs j (Finset.mem_union_right _ hj))]

lemma BTree.evalRaw_mono {N h : ℕ} (t : BTree N h) (hnot : t.notCount = 0)
    (rx₁ rx₂ cy₁ cy₂ : Fin N → Bool) (w₁ w₂ : Fin h → Bool)
    (hr : ∀ x, rx₁ x = true → rx₂ x = true)
    (hc : ∀ y, cy₁ y = true → cy₂ y = true)
    (hs : ∀ j, w₁ j = true → w₂ j = true) :
    t.evalRaw rx₁ cy₁ w₁ = true → t.evalRaw rx₂ cy₂ w₂ = true := by
  induction t with
  | row x => exact hr x
  | col y => exact hc y
  | seed j => exact hs j
  | not _ _ => simp [BTree.notCount] at hnot
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw, Bool.and_eq_true]
    intro ⟨h1, h2⟩
    exact ⟨ih₁ (by omega) h1, ih₂ (by omega) h2⟩
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw, Bool.or_eq_true]
    rintro (h1 | h2)
    · exact Or.inl (ih₁ (by omega) h1)
    · exact Or.inr (ih₂ (by omega) h2)

lemma BTree.evalRaw_zero_false {N h : ℕ} (t : BTree N h) (hnot : t.notCount = 0)
    (w : Fin h → Bool) (hw : ∀ j ∈ t.seeds, w j = false) :
    t.evalRaw (fun _ => false) (fun _ => false) w = false := by
  induction t with
  | row _ => rfl
  | col _ => rfl
  | seed j => exact hw j (Finset.mem_singleton_self j)
  | not _ _ => simp [BTree.notCount] at hnot
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw,
      ih₁ (by omega) (fun j hj => hw j (Finset.mem_union_left _ hj)),
      ih₂ (by omega) (fun j hj => hw j (Finset.mem_union_right _ hj)), Bool.and_self]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw,
      ih₁ (by omega) (fun j hj => hw j (Finset.mem_union_left _ hj)),
      ih₂ (by omega) (fun j hj => hw j (Finset.mem_union_right _ hj)), Bool.or_self]

lemma BTree.eval_eq_seed_of_only_seed {N h : ℕ} (t : BTree N h)
    (hnot : t.notCount = 0) (hr : t.rows = ∅) (hc : t.cols = ∅)
    (j : Fin h) (hs : ∀ k ∈ t.seeds, k = j) :
    ∀ (w : Fin h → Bool) (x y : Fin N), t.eval w x y = w j := by
  intro w x y
  induction t with
  | row x' => simp [BTree.rows] at hr
  | col y' => simp [BTree.cols] at hc
  | seed k =>
    have hk : k = j := hs k (Finset.mem_singleton_self k)
    subst hk; rfl
  | not _ _ => simp [BTree.notCount] at hnot
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.rows, Finset.union_eq_empty] at hr
    simp only [BTree.cols, Finset.union_eq_empty] at hc
    simp only [BTree.eval, BTree.evalRaw]
    have h1 := ih₁ (by omega) hr.1 hc.1 (fun k hk => hs k (Finset.mem_union_left _ hk))
    have h2 := ih₂ (by omega) hr.2 hc.2 (fun k hk => hs k (Finset.mem_union_right _ hk))
    simp only [BTree.eval] at h1 h2
    rw [h1, h2, Bool.and_self]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.rows, Finset.union_eq_empty] at hr
    simp only [BTree.cols, Finset.union_eq_empty] at hc
    simp only [BTree.eval, BTree.evalRaw]
    have h1 := ih₁ (by omega) hr.1 hc.1 (fun k hk => hs k (Finset.mem_union_left _ hk))
    have h2 := ih₂ (by omega) hr.2 hc.2 (fun k hk => hs k (Finset.mem_union_right _ hk))
    simp only [BTree.eval] at h1 h2
    rw [h1, h2, Bool.or_self]

lemma BTree.eval_of_no_not_no_and {N h : ℕ} (t : BTree N h)
    (hnot : t.notCount = 0) (hand : t.andCount = 0) (hseed : t.seeds = ∅) :
    ∀ (w : Fin h → Bool) (x y : Fin N), t.eval w x y = decide (x ∈ t.rows ∨ y ∈ t.cols) := by
  intro w x y
  induction t with
  | row x' => simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | col y' => simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | seed j => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and _ _ _ _ => simp [BTree.andCount] at hand
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.andCount] at hand
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    have h1 := ih₁ (by omega) (by omega) hseed.1
    have h2 := ih₂ (by omega) (by omega) hseed.2
    simp only [BTree.eval, BTree.evalRaw] at h1 h2 ⊢
    rw [h1, h2]
    simp only [BTree.rows, BTree.cols, Finset.mem_union]
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto

lemma BTree.tree_not_one_decr {N h : ℕ} (t : BTree N h) (w : Fin h → Bool)
    (hro : t.ReadOnce) (hseed : t.seeds = ∅) (hnot : t.notCount = 1) :
    (∃ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w = true →
      t.evalRaw (fun _ => false) (fun _ => false) w = true) ∨
    (∃ y ∈ t.cols, t.evalRaw (fun _ => false) (fun j => decide (j = y)) w = true →
      t.evalRaw (fun _ => false) (fun _ => false) w = true) := by
  induction t with
  | row _ => simp [BTree.notCount] at hnot
  | col _ => simp [BTree.notCount] at hnot
  | seed _ => simp [BTree.notCount] at hnot
  | not u _ =>
    simp only [BTree.notCount] at hnot
    have hu0 : u.notCount = 0 := by omega
    have hne : u.rows.Nonempty ∨ u.cols.Nonempty := by
      rcases u.nonempty_leaves with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [show u.seeds = ∅ from hseed] at h3; exact (Finset.not_nonempty_empty h3).elim
    rcases hne with ⟨x, hx⟩ | ⟨y, hy⟩
    · left; refine ⟨x, hx, fun h => ?_⟩
      simp only [BTree.evalRaw, Bool.not_eq_true'] at h ⊢
      by_contra hne0
      have huT : u.evalRaw (fun _ => false) (fun _ => false) w = true := by
        cases hval : u.evalRaw (fun _ => false) (fun _ => false) w
        · exact (hne0 hval).elim
        · rfl
      have hmon := u.evalRaw_mono hu0 (fun _ => false) (fun i => decide (i = x))
        (fun _ => false) (fun _ => false) w w (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => h) huT
      rw [hmon] at h; cases h
    · right; refine ⟨y, hy, fun h => ?_⟩
      simp only [BTree.evalRaw, Bool.not_eq_true'] at h ⊢
      by_contra hne0
      have huT : u.evalRaw (fun _ => false) (fun _ => false) w = true := by
        cases hval : u.evalRaw (fun _ => false) (fun _ => false) w
        · exact (hne0 hval).elim
        · rfl
      have hmon := u.evalRaw_mono hu0 (fun _ => false) (fun _ => false)
        (fun _ => false) (fun j => decide (j = y)) w w (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => h) huT
      rw [hmon] at h; cases h
  | and u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    by_cases hu1 : u.notCount = 1
    · rcases ihu hrou hseed.1 hu1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_left _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
        have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnv (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        exact ⟨hdec h.1, hv_eq ▸ h.2⟩
      · right; refine ⟨y, Finset.mem_union_left _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
        have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynv (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        exact ⟨hdec h.1, hv_eq ▸ h.2⟩
    · have hv1 : v.notCount = 1 := by omega
      rcases ihv hrov hseed.2 hv1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_right _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
        have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnu (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        exact ⟨hu_eq ▸ h.1, hdec h.2⟩
      · right; refine ⟨y, Finset.mem_union_right _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
        have hu_eq : u.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynu (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        exact ⟨hu_eq ▸ h.1, hdec h.2⟩
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    by_cases hu1 : u.notCount = 1
    · rcases ihu hrou hseed.1 hu1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_left _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
        have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnv (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hdec h1)
        · exact Or.inr (hv_eq ▸ h2)
      · right; refine ⟨y, Finset.mem_union_left _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
        have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynv (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hdec h1)
        · exact Or.inr (hv_eq ▸ h2)
    · have hv1 : v.notCount = 1 := by omega
      rcases ihv hrov hseed.2 hv1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_right _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
        have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnu (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hu_eq ▸ h1)
        · exact Or.inr (hdec h2)
      · right; refine ⟨y, Finset.mem_union_right _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
        have hu_eq : u.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynu (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hu_eq ▸ h1)
        · exact Or.inr (hdec h2)

lemma BTree.tree_seedless_tight {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅)
    (hrow : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true)
    (hcol : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true) :
    ∀ (w : Fin h → Bool) (x y : Fin N), t.eval w x y = decide (x ∈ t.rows ∨ y ∈ t.cols) := by
  induction t with
  | row x' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | col y' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | seed _ => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    exfalso
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨_, _, hdisjR, hdisjC, _⟩
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun j hj => by rw [hseed.2] at hj; exact (Finset.notMem_empty j hj).elim)
    have hune : u.rows.Nonempty ∨ u.cols.Nonempty := by
      rcases u.nonempty_leaves with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [hseed.1] at h3; exact (Finset.not_nonempty_empty h3).elim
    rcases hune with ⟨x, hx⟩ | ⟨y, hy⟩
    · have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ =
          v.evalRaw (fun _ => false) (fun _ => false) w₀ :=
        v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
      rw [hv_eq, hv0] at h1; cases h1.2
    · have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ =
          v.evalRaw (fun _ => false) (fun _ => false) w₀ :=
        v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
          have : j ≠ y := fun heq => hynv (heq ▸ hj); simp [this]) (fun _ _ => rfl)
      rw [hv_eq, hv0] at h1; cases h1.2
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      u.evalRaw_zero_false (by omega) w₀ (fun j hj => by rw [hseed.1] at hj; exact (Finset.notMem_empty j hj).elim)
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun j hj => by rw [hseed.2] at hj; exact (Finset.notMem_empty j hj).elim)
    have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
          have : j ≠ y := fun heq => hynv (heq ▸ hj); simp [this]) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
          have : j ≠ y := fun heq => hynu (heq ▸ hj); simp [this]) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have h1 := ihu hrou (by omega) hseed.1 hru hcu
    have h2 := ihv hrov (by omega) hseed.2 hrv hcv
    intro w x y
    simp only [BTree.eval, BTree.evalRaw] at h1 h2 ⊢
    rw [h1 w x y, h2 w x y]
    simp only [BTree.rows, BTree.cols, Finset.mem_union]
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto

lemma BTree.tree_seed_false {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool) (j₀ : Fin h)
    (hro : t.ReadOnce) (hnot : t.notCount = 0)
    (hseed : ∀ k ∈ t.seeds, k = j₀) (hw₀ : w₀ j₀ = false)
    (hrow : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true)
    (hcol : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true) :
    ∀ (w : Fin h → Bool) (x y : Fin N),
      t.eval w x y = decide ((j₀ ∈ t.seeds ∧ w j₀ = true) ∨ x ∈ t.rows ∨ y ∈ t.cols) := by
  induction t with
  | row x' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, BTree.seeds,
      Finset.notMem_empty, Finset.mem_singleton, false_and, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | col y' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, BTree.seeds,
      Finset.notMem_empty, Finset.mem_singleton, false_and, false_or]; exact decide_eq_decide.mpr eq_comm
  | seed k =>
    have hk : k = j₀ := hseed k (Finset.mem_singleton_self k)
    subst hk
    intro w x y; simp [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, BTree.seeds]
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    exfalso
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨_, _, hdisjR, hdisjC, hdisjS⟩
    have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      u.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_left _ hk)]; exact hw₀)
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_right _ hk)]; exact hw₀)
    have hex : (u.rows.Nonempty ∨ u.cols.Nonempty) ∨ (v.rows.Nonempty ∨ v.cols.Nonempty) := by
      rcases u.nonempty_leaves with h1 | h2 | ⟨k1, hk1⟩
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · rcases v.nonempty_leaves with h1 | h2 | ⟨k2, hk2⟩
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h2)
        · have heq1 : k1 = j₀ := hseed k1 (Finset.mem_union_left _ hk1)
          have heq2 : k2 = j₀ := hseed k2 (Finset.mem_union_right _ hk2)
          subst heq1; subst heq2
          exact (Finset.disjoint_left.mp hdisjS hk1 hk2).elim
    rcases hex with (⟨x, hx⟩ | ⟨y, hy⟩) | (⟨x, hx⟩ | ⟨y, hy⟩)
    · have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; cases h1.2
    · have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; cases h1.2
    · have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; cases h1.1
    · have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; cases h1.1
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      u.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_left _ hk)]; exact hw₀)
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_right _ hk)]; exact hw₀)
    have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have h1 := ihu hrou (by omega) (fun k hk => hseed k (Finset.mem_union_left _ hk)) hru hcu
    have h2 := ihv hrov (by omega) (fun k hk => hseed k (Finset.mem_union_right _ hk)) hrv hcv
    intro w x y
    simp only [BTree.eval, BTree.evalRaw] at h1 h2 ⊢
    rw [h1 w x y, h2 w x y]
    simp only [BTree.rows, BTree.cols, BTree.seeds, Finset.mem_union]
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((⟨h1, h2⟩ | h1 | h1) | (⟨h1, h2⟩ | h1 | h1))
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr (Or.inl (Or.inr h1))
      · exact Or.inr (Or.inr (Or.inr h1))
    · rintro (⟨h1 | h1, h2⟩ | (h1 | h1) | (h1 | h1))
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inl (Or.inr (Or.inr h1))
      · exact Or.inr (Or.inr (Or.inr h1))

lemma BTree.tree_seed_true {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool) (j₀ : Fin h)
    (hro : t.ReadOnce) (hnot : t.notCount = 0)
    (hseed : t.seeds = {j₀}) (hw₀ : w₀ j₀ = true)
    (hzero : t.evalRaw (fun _ => false) (fun _ => false) w₀ = false)
    (hrow : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true)
    (hcol : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true) :
    ∃ B D : Finset (Fin N), B ⊆ t.rows ∧ D ⊆ t.cols ∧ (B ≠ t.rows ∨ D ≠ t.cols) ∧
      ∀ (w : Fin h → Bool) (x y : Fin N),
        t.eval w x y = decide (x ∈ B ∨ y ∈ D ∨ (w j₀ = true ∧ (x ∈ t.rows ∨ y ∈ t.cols))) := by
  induction t with
  | row _ => simp [BTree.seeds] at hseed
  | col _ => simp [BTree.seeds] at hseed
  | seed k =>
    have hk : k = j₀ := by
      have : k ∈ ({j₀} : Finset (Fin h)) := hseed ▸ Finset.mem_singleton_self k
      exact Finset.mem_singleton.mp this
    subst hk
    simp [BTree.evalRaw, hw₀] at hzero
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, hdisjS⟩
    have hsplit : (u.seeds = {j₀} ∧ v.seeds = ∅) ∨ (u.seeds = ∅ ∧ v.seeds = {j₀}) := by
      have hj : j₀ ∈ u.seeds ∪ v.seeds := by
        change j₀ ∈ (BTree.and u v).seeds; rw [hseed]; exact Finset.mem_singleton_self j₀
      rcases Finset.mem_union.mp hj with hju | hjv
      · left
        have hsubU : u.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_left _ hk
        have hU : u.seeds = {j₀} := Finset.Subset.antisymm hsubU (Finset.singleton_subset_iff.mpr hju)
        have hV : v.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_right _ hk)
          subst hk0; exact Finset.disjoint_left.mp hdisjS hju hk
        exact ⟨hU, hV⟩
      · right
        have hsubV : v.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_right _ hk
        have hV : v.seeds = {j₀} := Finset.Subset.antisymm hsubV (Finset.singleton_subset_iff.mpr hjv)
        have hU : u.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_left _ hk)
          subst hk0; exact Finset.disjoint_right.mp hdisjS hjv hk
        exact ⟨hU, hV⟩
    rcases hsplit with ⟨hU, hV⟩ | ⟨hU, hV⟩
    · have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
        v.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hV] at hk; exact (Finset.notMem_empty k hk).elim)
      have hur : u.rows = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
        have h1 := hrow x (Finset.mem_union_left _ hx)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
        have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
          (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
        rw [hv_eq] at h1; cases h1.2
      have huc : u.cols = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro y hy
        have h1 := hcol y (Finset.mem_union_left _ hy)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
        have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
          (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
            have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hv0
        rw [hv_eq] at h1; cases h1.2
      have huev := u.eval_eq_seed_of_only_seed (by omega) hur huc j₀ (fun k hk => by rw [hU] at hk; exact Finset.mem_singleton.mp hk)
      have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := fun x hx =>
        (Bool.and_eq_true _ _ |>.mp (hrow x (Finset.mem_union_right _ hx))).2
      have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := fun y hy =>
        (Bool.and_eq_true _ _ |>.mp (hcol y (Finset.mem_union_right _ hy))).2
      have hvev := v.tree_seedless_tight w₀ hrov (by omega) hV hrv hcv
      have hvne : v.rows.Nonempty ∨ v.cols.Nonempty := by
        rcases v.nonempty_leaves with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · rw [hV] at h3; exact (Finset.not_nonempty_empty h3).elim
      refine ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
      · simp only [BTree.rows, BTree.cols, hur, huc, Finset.empty_union]
        rcases hvne with h1 | h2
        · exact Or.inl (Finset.nonempty_iff_ne_empty.mp h1).symm
        · exact Or.inr (Finset.nonempty_iff_ne_empty.mp h2).symm
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, hur, huc, Finset.empty_union,
          Finset.notMem_empty, false_or] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]
    · have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
        u.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hU] at hk; exact (Finset.notMem_empty k hk).elim)
      have hvr : v.rows = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
        have h1 := hrow x (Finset.mem_union_right _ hx)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
        have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
          (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
        rw [hu_eq] at h1; cases h1.1
      have hvc : v.cols = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro y hy
        have h1 := hcol y (Finset.mem_union_right _ hy)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
        have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
          (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
            have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hu0
        rw [hu_eq] at h1; cases h1.1
      have hvev := v.eval_eq_seed_of_only_seed (by omega) hvr hvc j₀ (fun k hk => by rw [hV] at hk; exact Finset.mem_singleton.mp hk)
      have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := fun x hx =>
        (Bool.and_eq_true _ _ |>.mp (hrow x (Finset.mem_union_left _ hx))).1
      have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := fun y hy =>
        (Bool.and_eq_true _ _ |>.mp (hcol y (Finset.mem_union_left _ hy))).1
      have huev := u.tree_seedless_tight w₀ hrou (by omega) hU hru hcu
      have hune : u.rows.Nonempty ∨ u.cols.Nonempty := by
        rcases u.nonempty_leaves with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · rw [hU] at h3; exact (Finset.not_nonempty_empty h3).elim
      refine ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
      · simp only [BTree.rows, BTree.cols, hvr, hvc, Finset.union_empty]
        rcases hune with h1 | h2
        · exact Or.inl (Finset.nonempty_iff_ne_empty.mp h1).symm
        · exact Or.inr (Finset.nonempty_iff_ne_empty.mp h2).symm
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, hvr, hvc, Finset.union_empty,
          Finset.notMem_empty, false_or] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; tauto
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, hdisjS⟩
    simp only [BTree.evalRaw, Bool.or_eq_false_iff] at hzero
    have hsplit : (u.seeds = {j₀} ∧ v.seeds = ∅) ∨ (u.seeds = ∅ ∧ v.seeds = {j₀}) := by
      have hj : j₀ ∈ u.seeds ∪ v.seeds := by
        change j₀ ∈ (BTree.or u v).seeds; rw [hseed]; exact Finset.mem_singleton_self j₀
      rcases Finset.mem_union.mp hj with hju | hjv
      · left
        have hsubU : u.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_left _ hk
        have hU : u.seeds = {j₀} := Finset.Subset.antisymm hsubU (Finset.singleton_subset_iff.mpr hju)
        have hV : v.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_right _ hk)
          subst hk0; exact Finset.disjoint_left.mp hdisjS hju hk
        exact ⟨hU, hV⟩
      · right
        have hsubV : v.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_right _ hk
        have hV : v.seeds = {j₀} := Finset.Subset.antisymm hsubV (Finset.singleton_subset_iff.mpr hjv)
        have hU : u.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_left _ hk)
          subst hk0; exact Finset.disjoint_right.mp hdisjS hjv hk
        exact ⟨hU, hV⟩
    have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hzero.2
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hzero.2
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hzero.1
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hzero.1
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    rcases hsplit with ⟨hU, hV⟩ | ⟨hU, hV⟩
    · obtain ⟨B₁, D₁, hB₁, hD₁, hne₁, huev⟩ := ihu hrou (by omega) hU hzero.1 hru hcu
      have hvev := v.tree_seedless_tight w₀ hrov (by omega) hV hrv hcv
      refine ⟨B₁ ∪ v.rows, D₁ ∪ v.cols, Finset.union_subset_union_left hB₁,
        Finset.union_subset_union_left hD₁, ?_, ?_⟩
      · rcases hne₁ with hBne | hDne
        · left; intro heq; apply hBne; apply Finset.Subset.antisymm hB₁
          intro x hx
          have hxm : x ∈ B₁ ∪ v.rows := heq ▸ Finset.mem_union_left _ hx
          exact (Finset.mem_union.mp hxm).resolve_right (Finset.disjoint_left.mp hdisjR hx)
        · right; intro heq; apply hDne; apply Finset.Subset.antisymm hD₁
          intro y hy
          have hym : y ∈ D₁ ∪ v.cols := heq ▸ Finset.mem_union_left _ hy
          exact (Finset.mem_union.mp hym).resolve_right (Finset.disjoint_left.mp hdisjC hy)
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        simp only [BTree.rows, BTree.cols, Finset.mem_union]
        rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h1 | h1 | ⟨hw, h1 | h1⟩) | (h1 | h1))
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl (Or.inl h1))
          · exact Or.inr (Or.inr ⟨hw, Or.inl (Or.inl h1)⟩)
          · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inl h1)⟩)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inl (Or.inr h1))
        · rintro ((h1 | h1) | (h1 | h1) | ⟨hw, (h1 | h1) | (h1 | h1)⟩)
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr h1)
          · exact Or.inl (Or.inr (Or.inr ⟨hw, Or.inl h1⟩))
          · exact Or.inr (Or.inl h1)
          · exact Or.inl (Or.inr (Or.inr ⟨hw, Or.inr h1⟩))
          · exact Or.inr (Or.inr h1)
    · obtain ⟨B₁, D₁, hB₁, hD₁, hne₁, hvev⟩ := ihv hrov (by omega) hV hzero.2 hrv hcv
      have huev := u.tree_seedless_tight w₀ hrou (by omega) hU hru hcu
      refine ⟨u.rows ∪ B₁, u.cols ∪ D₁, Finset.union_subset_union_right hB₁,
        Finset.union_subset_union_right hD₁, ?_, ?_⟩
      · rcases hne₁ with hBne | hDne
        · left; intro heq; apply hBne; apply Finset.Subset.antisymm hB₁
          intro x hx
          have hxm : x ∈ u.rows ∪ B₁ := heq ▸ Finset.mem_union_right _ hx
          exact (Finset.mem_union.mp hxm).resolve_left (Finset.disjoint_right.mp hdisjR hx)
        · right; intro heq; apply hDne; apply Finset.Subset.antisymm hD₁
          intro y hy
          have hym : y ∈ u.cols ∪ D₁ := heq ▸ Finset.mem_union_right _ hy
          exact (Finset.mem_union.mp hym).resolve_left (Finset.disjoint_right.mp hdisjC hy)
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        simp only [BTree.rows, BTree.cols, Finset.mem_union]
        rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h1 | h1) | (h1 | h1 | ⟨hw, h1 | h1⟩))
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inl (Or.inr h1))
          · exact Or.inr (Or.inr ⟨hw, Or.inl (Or.inr h1)⟩)
          · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inr h1)⟩)
        · rintro ((h1 | h1) | (h1 | h1) | ⟨hw, (h1 | h1) | (h1 | h1)⟩)
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inr ⟨hw, Or.inl h1⟩))
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inr (Or.inr ⟨hw, Or.inr h1⟩))

def BTree.hasBigAnd {N h : ℕ} : BTree N h → Prop
  | .row _ => False
  | .col _ => False
  | .seed _ => False
  | .not t => t.hasBigAnd
  | .and u v => (2 ≤ u.lineCount ∨ 2 ≤ v.lineCount) ∨ u.hasBigAnd ∨ v.hasBigAnd
  | .or u v => u.hasBigAnd ∨ v.hasBigAnd

lemma BTree.area_le_lineCount {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hnot : t.notCount = 0) (hseed : t.seeds = ∅) :
    areaC (t.eval w₀) ≤ t.lineCount * N := by
  apply area_le_of_lines (t.eval w₀) t.rows t.cols
  intro x y hxy
  by_contra hneither; push Not at hneither
  have heq : t.eval w₀ x y = t.evalRaw (fun _ => false) (fun _ => false) w₀ :=
    t.evalRaw_congr _ _ _ _ _ _
      (fun i hi => by have : i ≠ x := fun h => hneither.1 (h ▸ hi); simp [this])
      (fun j hj => by have : j ≠ y := fun h => hneither.2 (h ▸ hj); simp [this])
      (fun _ _ => rfl)
  rw [heq, t.evalRaw_zero_false hnot w₀ (fun j hj => by rw [hseed] at hj; exact (Finset.notMem_empty j hj).elim)] at hxy
  cases hxy

lemma BTree.lineCount_pos {N h : ℕ} (t : BTree N h) (hseed : t.seeds = ∅) :
    1 ≤ t.lineCount := by
  rcases t.nonempty_leaves with h1 | h2 | h3
  · have := Finset.card_pos.mpr h1; unfold BTree.lineCount; omega
  · have := Finset.card_pos.mpr h2; unfold BTree.lineCount; omega
  · rw [hseed] at h3; exact (Finset.not_nonempty_empty h3).elim

lemma BTree.lineCount_and {N h : ℕ} (u v : BTree N h)
    (hR : Disjoint u.rows v.rows) (hC : Disjoint u.cols v.cols) :
    (BTree.and u v).lineCount = u.lineCount + v.lineCount := by
  simp only [BTree.lineCount, BTree.rows, BTree.cols,
    Finset.card_union_of_disjoint hR, Finset.card_union_of_disjoint hC]
  omega

lemma BTree.lineCount_or {N h : ℕ} (u v : BTree N h)
    (hR : Disjoint u.rows v.rows) (hC : Disjoint u.cols v.cols) :
    (BTree.or u v).lineCount = u.lineCount + v.lineCount := by
  simp only [BTree.lineCount, BTree.rows, BTree.cols,
    Finset.card_union_of_disjoint hR, Finset.card_union_of_disjoint hC]
  omega

lemma BTree.area_le_of_hasBigAnd {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅) (hbig : t.hasBigAnd) :
    areaC (t.eval w₀) + 2 * N ≤ t.lineCount * N := by
  induction t with
  | row _ => exact hbig.elim
  | col _ => exact hbig.elim
  | seed _ => exact hbig.elim
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hlc := BTree.lineCount_and u v hdisjR hdisjC
    have hleU : areaC ((BTree.and u v).eval w₀) ≤ areaC (u.eval w₀) :=
      area_le_of_subset _ _ (fun x y h => (Bool.and_eq_true _ _ |>.mp h).1)
    have hleV : areaC ((BTree.and u v).eval w₀) ≤ areaC (v.eval w₀) :=
      area_le_of_subset _ _ (fun x y h => (Bool.and_eq_true _ _ |>.mp h).2)
    have hU := u.area_le_lineCount w₀ (by omega) hseed.1
    have hV := v.area_le_lineCount w₀ (by omega) hseed.2
    rw [hlc, Nat.add_mul]
    rcases hbig with (h2u | h2v) | hbu | hbv
    · have : 2 * N ≤ u.lineCount * N := Nat.mul_le_mul_right N h2u
      omega
    · have : 2 * N ≤ v.lineCount * N := Nat.mul_le_mul_right N h2v
      omega
    · have := ihu hrou (by omega) hseed.1 hbu; omega
    · have := ihv hrov (by omega) hseed.2 hbv; omega
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hlc := BTree.lineCount_or u v hdisjR hdisjC
    have hor : areaC ((BTree.or u v).eval w₀) ≤ areaC (u.eval w₀) + areaC (v.eval w₀) :=
      area_or_le (u.eval w₀) (v.eval w₀)
    have hU := u.area_le_lineCount w₀ (by omega) hseed.1
    have hV := v.area_le_lineCount w₀ (by omega) hseed.2
    rw [hlc, Nat.add_mul]
    rcases hbig with hbu | hbv
    · have := ihu hrou (by omega) hseed.1 hbu; omega
    · have := ihv hrov (by omega) hseed.2 hbv; omega

lemma BTree.single_leaf_form {N h : ℕ} (t : BTree N h)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅) (hlc : t.lineCount = 1) :
    t.andCount = 0 ∧
    ((∃ x : Fin N, t.rows = {x} ∧ t.cols = ∅ ∧ ∀ w a b, t.eval w a b = decide (a = x)) ∨
     (∃ y : Fin N, t.rows = ∅ ∧ t.cols = {y} ∧ ∀ w a b, t.eval w a b = decide (b = y))) := by
  induction t with
  | row x =>
    refine ⟨rfl, Or.inl ⟨x, rfl, rfl, fun _ a _ => by simp only [BTree.eval, BTree.evalRaw]; exact decide_eq_decide.mpr eq_comm⟩⟩
  | col y =>
    refine ⟨rfl, Or.inr ⟨y, rfl, rfl, fun _ _ b => by simp only [BTree.eval, BTree.evalRaw]; exact decide_eq_decide.mpr eq_comm⟩⟩
  | seed _ => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    exfalso
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨_, _, hdisjR, hdisjC, _⟩
    have h1 := u.lineCount_pos hseed.1
    have h2 := v.lineCount_pos hseed.2
    have hlc' := BTree.lineCount_and u v hdisjR hdisjC
    omega
  | or u v _ _ =>
    exfalso
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨_, _, hdisjR, hdisjC, _⟩
    have h1 := u.lineCount_pos hseed.1
    have h2 := v.lineCount_pos hseed.2
    have hlc' := BTree.lineCount_or u v hdisjR hdisjC
    omega

lemma BTree.area_le_of_no_bigAnd {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅) (hnbig : ¬ t.hasBigAnd) :
    areaC (t.eval w₀) + 2 * t.andCount * N ≤ t.lineCount * N + t.andCount := by
  induction t with
  | row x =>
    have hle := (BTree.row x : BTree N h).area_le_lineCount w₀ rfl rfl
    simp only [BTree.andCount, Nat.mul_zero, Nat.zero_mul, add_zero]
    exact hle
  | col y =>
    have hle := (BTree.col y : BTree N h).area_le_lineCount w₀ rfl rfl
    simp only [BTree.andCount, Nat.mul_zero, Nat.zero_mul, add_zero]
    exact hle
  | seed _ => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    simp only [BTree.hasBigAnd, not_or] at hnbig
    have hu1 : u.lineCount = 1 := by have := u.lineCount_pos hseed.1; omega
    have hv1 : v.lineCount = 1 := by have := v.lineCount_pos hseed.2; omega
    obtain ⟨hua, huf⟩ := u.single_leaf_form hrou (by omega) hseed.1 hu1
    obtain ⟨hva, hvf⟩ := v.single_leaf_form hrov (by omega) hseed.2 hv1
    have hlc : (BTree.and u v).lineCount = 2 := by
      rw [BTree.lineCount_and u v hdisjR hdisjC, hu1, hv1]
    have hac : (BTree.and u v).andCount = 1 := by simp [BTree.andCount, hua, hva]
    have harea1 : areaC ((BTree.and u v).eval w₀) ≤ 1 := by
      rcases huf with ⟨x₁, hru, _, huev⟩ | ⟨y₁, _, hcu, huev⟩ <;>
      rcases hvf with ⟨x₂, hrv, _, hvev⟩ | ⟨y₂, _, hcv, hvev⟩
      · have hne : x₁ ≠ x₂ := by
          intro h; subst h; exact Finset.disjoint_left.mp hdisjR (hru ▸ Finset.mem_singleton_self x₁) (hrv ▸ Finset.mem_singleton_self x₁)
        have h0 : areaC ((BTree.and u v).eval w₀) = 0 := by
          unfold areaC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro ⟨a, b⟩ _
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true, not_and]
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval] at h1 h2
          rw [h1, h2]; simp only [decide_eq_true_eq]
          intro ha1 ha2; exact hne (ha1.symm.trans ha2)
        omega
      · have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (BTree.and u v).eval w₀ z.1 z.2 = true) ⊆ {(x₁, y₂)} := by
          intro ⟨a, b⟩ hz
          rw [Finset.mem_filter] at hz
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true] at h1 h2 hz
          rw [h1, h2] at hz
          simp only [decide_eq_true_eq] at hz
          rw [Finset.mem_singleton]; exact Prod.ext hz.2.1 hz.2.2
        exact le_trans (Finset.card_le_card hsub) (by simp)
      · have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (BTree.and u v).eval w₀ z.1 z.2 = true) ⊆ {(x₂, y₁)} := by
          intro ⟨a, b⟩ hz
          rw [Finset.mem_filter] at hz
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true] at h1 h2 hz
          rw [h1, h2] at hz
          simp only [decide_eq_true_eq] at hz
          rw [Finset.mem_singleton]; exact Prod.ext hz.2.2 hz.2.1
        exact le_trans (Finset.card_le_card hsub) (by simp)
      · have hne : y₁ ≠ y₂ := by
          intro h; subst h; exact Finset.disjoint_left.mp hdisjC (hcu ▸ Finset.mem_singleton_self y₁) (hcv ▸ Finset.mem_singleton_self y₁)
        have h0 : areaC ((BTree.and u v).eval w₀) = 0 := by
          unfold areaC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro ⟨a, b⟩ _
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true, not_and]
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval] at h1 h2
          rw [h1, h2]; simp only [decide_eq_true_eq]
          intro hb1 hb2; exact hne (hb1.symm.trans hb2)
        omega
    rw [hlc, hac]; omega
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    simp only [BTree.hasBigAnd, not_or] at hnbig
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hu := ihu hrou (by omega) hseed.1 hnbig.1
    have hv := ihv hrov (by omega) hseed.2 hnbig.2
    have hor : areaC ((BTree.or u v).eval w₀) ≤ areaC (u.eval w₀) + areaC (v.eval w₀) :=
      area_or_le (u.eval w₀) (v.eval w₀)
    have hlc := BTree.lineCount_or u v hdisjR hdisjC
    have hac : (BTree.or u v).andCount = u.andCount + v.andCount := rfl
    rw [hlc, hac]
    have h1 : 2 * (u.andCount + v.andCount) * N = 2 * u.andCount * N + 2 * v.andCount * N := by ring
    have h2 : (u.lineCount + v.lineCount) * N = u.lineCount * N + v.lineCount * N := by ring
    omega

def unfoldTree {N h : ℕ} (hN : 0 < N) (C : Circuit) (w : ℕ) : BTree N h :=
  if _ : N + N + h ≤ w ∧ w - (N + N + h) < C.gates.length then
    let g := gateAt C (w - (N + N + h))
    match g.op, g.inputs with
    | .not, [a] => if _ : a < w then .not (unfoldTree hN C a) else .row ⟨0, hN⟩
    | .and, [a, b] => if _ : a < w ∧ b < w then .and (unfoldTree hN C a) (unfoldTree hN C b) else .row ⟨0, hN⟩
    | .or, [a, b] => if _ : a < w ∧ b < w then .or (unfoldTree hN C a) (unfoldTree hN C b) else .row ⟨0, hN⟩
    | _, [a] => if _ : a < w then unfoldTree hN C a else .row ⟨0, hN⟩
    | _, _ => .row ⟨0, hN⟩
  else if hw1 : w < N then .row ⟨w, hw1⟩
  else if hw2 : w < N + N then .col ⟨w - N, by omega⟩
  else if hw3 : w < N + N + h then .seed ⟨w - (N + N), by omega⟩
  else .row ⟨0, hN⟩
termination_by w

lemma unfoldTree_props {N h : ℕ} (hN : 0 < N) (C : Circuit)
    (hread : ReadsBack (N + N + h) C)
    (hleg : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) :
    ∀ (w : ℕ), w < N + N + h + C.gates.length →
      (∀ u ∈ reachWires (N + N + h) C w, N + N + h ≤ u → (gateAt C (u - (N + N + h))).inputs ≠ []) →
      (∀ v ∈ (reachWires (N + N + h) C w).erase w,
        readsW (N + N + h) C ((reachWires (N + N + h) C w).filter (N + N + h ≤ ·)) v = 1) →
      let t := unfoldTree (h := h) hN C w
      (∀ wd x y, t.eval wd x y = wireVal C (inpVec wd x y) w) ∧
      (∀ x : Fin N, x ∈ t.rows ↔ x.val ∈ reachWires (N + N + h) C w) ∧
      (∀ y : Fin N, y ∈ t.cols ↔ N + y.val ∈ reachWires (N + N + h) C w) ∧
      (∀ j : Fin h, j ∈ t.seeds ↔ N + N + j.val ∈ reachWires (N + N + h) C w) ∧
      t.ReadOnce ∧
      t.notCount = ((reachWires (N + N + h) C w).filter
        (fun u => N + N + h ≤ u ∧ isNotOp (gateAt C (u - (N + N + h))).op = true)).card := by
  set n := N + N + h
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne0 hreads
    have hreads_child : ∀ a, a ∈ reachWires n C w →
        ∀ v ∈ (reachWires n C a).erase a,
          readsW n C ((reachWires n C a).filter (n ≤ ·)) v = 1 := by
      intro a ha v hv
      have hasub := reachWires_subset_of_mem hread w a ha
      have hv_ne_a : v ≠ a := (Finset.mem_erase.mp hv).1
      have hv_in_a : v ∈ reachWires n C a := (Finset.mem_erase.mp hv).2
      have hge1 := readsW_pos_of_mem_ne hread a v hv_in_a hv_ne_a
      have hvlt : v < a := lt_of_le_of_ne (le_of_mem_reachWires hread a v hv_in_a) hv_ne_a
      have hale : a ≤ w := le_of_mem_reachWires hread w a ha
      have hv_er_w : v ∈ (reachWires n C w).erase w := Finset.mem_erase.mpr ⟨by omega, hasub hv_in_a⟩
      have hle1 : readsW n C ((reachWires n C a).filter (n ≤ ·)) v ≤
          readsW n C ((reachWires n C w).filter (n ≤ ·)) v := by
        apply Finset.sum_le_sum_of_subset
        intro u hu
        exact Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
      have h1 := hreads v hv_er_w
      omega
    by_cases hge : n ≤ w
    · have hw2 : w - n < C.gates.length := by omega
      have hmemC : gateAt C (w - n) ∈ C.gates := by
        unfold gateAt; rw [List.getD_eq_getElem _ _ hw2]; exact List.getElem_mem hw2
      rcases hleg _ hmemC with ⟨hlen, hop⟩
      have hne_w : (gateAt C (w - n)).inputs ≠ [] := hne0 w (self_mem_reachWires n C w) hge
      have hnot_filter : ∀ (a : ℕ) (ha : a ∈ (gateAt C (w - n)).inputs),
          a ∈ reachWires n C w ∧ a < w := by
        intro a ha
        have halt : a < w := by have := hread (w - n) hw2 a ha; omega
        have ham : a ∈ reachWires n C w :=
          (mem_reachWires_iff hread w a).mpr (Or.inr ⟨hge, hw2, a, ha, self_mem_reachWires n C a⟩)
        exact ⟨ham, halt⟩
      cases hins : (gateAt C (w - n)).inputs with
      | nil => exact (hne_w hins).elim
      | cons a rest =>
        cases rest with
        | nil =>
          have ha_in : a ∈ (gateAt C (w - n)).inputs := by rw [hins]; exact List.mem_cons_self
          obtain ⟨ha_mem, halt⟩ := hnot_filter a ha_in
          have hasub := reachWires_subset_of_mem hread w a ha_mem
          have hreach_eq : reachWires n C w = insert w (reachWires n C a) := by
            ext v; rw [mem_reachWires_iff hread, Finset.mem_insert]
            constructor
            · rintro (rfl | ⟨_, _, u, hu, hvu⟩)
              · exact Or.inl rfl
              · rw [hins, List.mem_singleton] at hu; subst hu; exact Or.inr hvu
            · rintro (rfl | hva)
              · exact Or.inl rfl
              · exact Or.inr ⟨hge, hw2, a, ha_in, hva⟩
          have hw_not_a : w ∉ reachWires n C a := by
            intro hm; have := le_of_mem_reachWires hread a w hm; omega
          obtain ⟨heva, hrowa, hcola, hseeda, hroa, hnota⟩ :=
            ih a halt (by omega) (fun u hu hun => hne0 u (hasub hu) hun) (hreads_child a ha_mem)
          rcases hop with hop_eq | hop_eq | ⟨hop_eq, _⟩
          · have htree : unfoldTree (h := h) hN C w = unfoldTree (h := h) hN C a := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, hroa, ?_⟩
            · rw [heva wd x y, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · rw [hrowa x, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · rw [hcola y, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · rw [hseeda j, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · rw [hnota, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              simp [hnf]
          · have htree : unfoldTree (h := h) hN C w = unfoldTree (h := h) hN C a := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, hroa, ?_⟩
            · rw [heva wd x y, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · rw [hrowa x, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · rw [hcola y, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · rw [hseeda j, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · rw [hnota, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              simp [hnf]
          · have htree : unfoldTree (h := h) hN C w = .not (unfoldTree (h := h) hN C a) := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, hroa, ?_⟩
            · simp only [BTree.eval, BTree.evalRaw]
              have h1 := heva wd x y; simp only [BTree.eval] at h1
              rw [h1, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · simp only [BTree.rows]; rw [hrowa x, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · simp only [BTree.cols]; rw [hcola y, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · simp only [BTree.seeds]; rw [hseeda j, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · simp only [BTree.notCount]
              have hnot_w : n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true := ⟨hge, by rw [hop_eq]; rfl⟩
              rw [hnota, hreach_eq, Finset.filter_insert, if_pos hnot_w, Finset.card_insert_of_notMem]
              intro hm; exact hw_not_a (Finset.mem_filter.mp hm).1
        | cons b rest' =>
          have hnil : rest' = [] := List.length_eq_zero_iff.mp (by rw [hins] at hlen; simp only [List.length_cons] at hlen; omega)
          subst hnil
          have ha_in : a ∈ (gateAt C (w - n)).inputs := by rw [hins]; exact List.mem_cons_self
          have hb_in : b ∈ (gateAt C (w - n)).inputs := by rw [hins]; exact List.mem_cons_of_mem a List.mem_cons_self
          obtain ⟨ha_mem, halt⟩ := hnot_filter a ha_in
          obtain ⟨hb_mem, hblt⟩ := hnot_filter b hb_in
          have hasub := reachWires_subset_of_mem hread w a ha_mem
          have hbsub := reachWires_subset_of_mem hread w b hb_mem
          have hdisj : Disjoint (reachWires n C a) (reachWires n C b) :=
            disjoint_children_of_reads_one hread w hw hreads w a b
              (Finset.mem_filter.mpr ⟨self_mem_reachWires n C w, hge⟩) hins
          have hreach_eq : reachWires n C w = insert w (reachWires n C a ∪ reachWires n C b) := by
            ext v; rw [mem_reachWires_iff hread, Finset.mem_insert, Finset.mem_union]
            constructor
            · rintro (rfl | ⟨_, _, u, hu, hvu⟩)
              · exact Or.inl rfl
              · rw [hins] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl
                · exact Or.inr (Or.inl hvu)
                · exact Or.inr (Or.inr hvu)
            · rintro (rfl | hva | hvb)
              · exact Or.inl rfl
              · exact Or.inr ⟨hge, hw2, a, ha_in, hva⟩
              · exact Or.inr ⟨hge, hw2, b, hb_in, hvb⟩
          obtain ⟨heva, hrowa, hcola, hseeda, hroa, hnota⟩ :=
            ih a halt (by omega) (fun u hu hun => hne0 u (hasub hu) hun) (hreads_child a ha_mem)
          obtain ⟨hevb, hrowb, hcolb, hseedb, hrob, hnotb⟩ :=
            ih b hblt (by omega) (fun u hu hun => hne0 u (hbsub hu) hun) (hreads_child b hb_mem)
          have hdisjR : Disjoint (unfoldTree (h := h) hN C a).rows (unfoldTree (h := h) hN C b).rows := by
            rw [Finset.disjoint_left]; intro x hx1 hx2
            exact Finset.disjoint_left.mp hdisj ((hrowa x).mp hx1) ((hrowb x).mp hx2)
          have hdisjC : Disjoint (unfoldTree (h := h) hN C a).cols (unfoldTree (h := h) hN C b).cols := by
            rw [Finset.disjoint_left]; intro y hy1 hy2
            exact Finset.disjoint_left.mp hdisj ((hcola y).mp hy1) ((hcolb y).mp hy2)
          have hdisjS : Disjoint (unfoldTree (h := h) hN C a).seeds (unfoldTree (h := h) hN C b).seeds := by
            rw [Finset.disjoint_left]; intro j hj1 hj2
            exact Finset.disjoint_left.mp hdisj ((hseeda j).mp hj1) ((hseedb j).mp hj2)
          rcases hop with hop_eq | hop_eq | ⟨_, h1⟩
          · have htree : unfoldTree (h := h) hN C w = .and (unfoldTree (h := h) hN C a) (unfoldTree (h := h) hN C b) := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt, hblt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, ⟨hroa, hrob, hdisjR, hdisjC, hdisjS⟩, ?_⟩
            · simp only [BTree.eval, BTree.evalRaw]
              have h1 := heva wd x y; have h2 := hevb wd x y
              simp only [BTree.eval] at h1 h2
              rw [h1, h2, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · simp only [BTree.rows, Finset.mem_union]; rw [hrowa x, hrowb x, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · simp only [BTree.cols, Finset.mem_union]; rw [hcola y, hcolb y, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · simp only [BTree.seeds, Finset.mem_union]; rw [hseeda j, hseedb j, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · simp only [BTree.notCount]
              rw [hnota, hnotb, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              rw [if_neg hnf, Finset.filter_union, Finset.card_union_of_disjoint]
              exact Finset.disjoint_filter_filter hdisj
          · have htree : unfoldTree (h := h) hN C w = .or (unfoldTree (h := h) hN C a) (unfoldTree (h := h) hN C b) := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt, hblt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, ⟨hroa, hrob, hdisjR, hdisjC, hdisjS⟩, ?_⟩
            · simp only [BTree.eval, BTree.evalRaw]
              have h1 := heva wd x y; have h2 := hevb wd x y
              simp only [BTree.eval] at h1 h2
              rw [h1, h2, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · simp only [BTree.rows, Finset.mem_union]; rw [hrowa x, hrowb x, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · simp only [BTree.cols, Finset.mem_union]; rw [hcola y, hcolb y, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · simp only [BTree.seeds, Finset.mem_union]; rw [hseeda j, hseedb j, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · simp only [BTree.notCount]
              rw [hnota, hnotb, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              rw [if_neg hnf, Finset.filter_union, Finset.card_union_of_disjoint]
              exact Finset.disjoint_filter_filter hdisj
          · rw [hins] at h1; simp at h1
    · have hlt : w < n := Nat.lt_of_not_ge hge
      have hreach_sing : reachWires n C w = {w} := by
        rw [reachWires]; simp [hge]
      have hnot_zero : ((reachWires n C w).filter
          (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true)).card = 0 := by
        rw [hreach_sing, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u hu; rw [Finset.mem_singleton.mp hu]; omega
      by_cases hw1 : w < N
      · have htree : unfoldTree (h := h) hN C w = .row ⟨w, hw1⟩ := by
          rw [unfoldTree]; simp [show ¬ (N + N + h ≤ w) from hge, hw1]
        dsimp only; rw [htree]
        refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, trivial, ?_⟩
        · rw [wireVal_input C _ (inpVec_length wd x y) w hlt, inpVec_getD_row wd x y w hw1]
          rfl
        · simp only [BTree.rows, Finset.mem_singleton, hreach_sing]
          exact ⟨fun hx => congrArg Fin.val hx, fun hx => Fin.ext hx⟩
        · simp only [BTree.cols, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
        · simp only [BTree.seeds, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
        · simp [BTree.notCount, hnot_zero]
      · by_cases hw2 : w < N + N
        · have htree : unfoldTree (h := h) hN C w = .col ⟨w - N, by omega⟩ := by
            rw [unfoldTree]; simp [show ¬ (N + N + h ≤ w) from hge, hw1, hw2]
          dsimp only; rw [htree]
          refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, trivial, ?_⟩
          · rw [wireVal_input C _ (inpVec_length wd x y) w hlt, inpVec_getD_col wd x y w (by omega) hw2]
            rfl
          · simp only [BTree.rows, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp only [BTree.cols, Finset.mem_singleton, hreach_sing, Fin.ext_iff]; omega
          · simp only [BTree.seeds, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp [BTree.notCount, hnot_zero]
        · have htree : unfoldTree (h := h) hN C w = .seed ⟨w - (N + N), by omega⟩ := by
            rw [unfoldTree]; simp [show ¬ (N + N + h ≤ w) from hge, hw1, hw2, show w < N + N + h from hlt]
          dsimp only; rw [htree]
          refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, trivial, ?_⟩
          · rw [wireVal_input C _ (inpVec_length wd x y) w hlt, inpVec_getD_seed wd x y w (by omega) hlt]
            rfl
          · simp only [BTree.rows, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp only [BTree.cols, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp only [BTree.seeds, Finset.mem_singleton, hreach_sing, Fin.ext_iff]; omega
          · simp [BTree.notCount, hnot_zero]

lemma part1_classification (N g : ℕ) (hg : 0 < g) (hgN : g + 1 < N)
    (h : ℕ) (C : Circuit) (hleg : legalC N h C) (hsize : C.size ≤ g)
    (w₀ : Fin h → Bool)
    (hlo : (g - 1) * N + 1 < areaC (tableC N h C w₀))
    (hhi : areaC (tableC N h C w₀) < N * (N - g)) :
    (∃ R S : Finset (Fin N), g ≤ R.card + S.card ∧ R.card + S.card ≤ g + 1 ∧ lineUnionC N h C R S) ∨
    ∃ (R S : Finset (Fin N)) (j : Fin h), R.card + S.card = g ∧
      ((w₀ j = false ∧ ∀ (w : Fin h → Bool) (x y : Fin N),
        tableC N h C w x y = decide (w j = true ∨ x ∈ R ∨ y ∈ S)) ∨
       (w₀ j = true ∧ ∃ B D : Finset (Fin N), B ⊆ R ∧ D ⊆ S ∧ (B ≠ R ∨ D ≠ S) ∧
        ∀ (w : Fin h → Bool) (x y : Fin N), tableC N h C w x y =
          decide (x ∈ B ∨ y ∈ D ∨ (w j = true ∧ (x ∈ R ∨ y ∈ S))))) := by
  let n := N + N + h
  have hN : 0 < N := by omega
  rcases hleg with ⟨hread, hout, hgates⟩
  have hout' : C.output < n + C.gates.length := hout
  let V := reachWires n C C.output
  let G := V.filter (n ≤ ·)
  let I := V.filter (· < n)
  let n0 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 0)).card
  let n1 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false)).card
  let nnot := (G.filter (fun u => isNotOp (gateAt C (u - n)).op = true)).card
  have hG_le : G.card ≤ g := by
    have hsub : G ⊆ (Finset.range C.gates.length).image (fun k => n + k) := by
      intro u hu
      have huV := (Finset.mem_filter.mp hu).1
      have hun := (Finset.mem_filter.mp hu).2
      have hult : u - n < C.gates.length := by
        have := le_of_mem_reachWires hread C.output u huV; omega
      exact Finset.mem_image.mpr ⟨u - n, Finset.mem_range.mpr hult, by omega⟩
    have hle := le_trans (Finset.card_le_card hsub) Finset.card_image_le
    rw [Finset.card_range] at hle
    exact le_trans hle hsize
  obtain ⟨hacc0, hacc_tight0⟩ := accounting_ineq hread hgates C.output hout'
  have hacc : I.card + 2 * n0 + n1 + nnot ≤ G.card + 1 := hacc0
  have hacc_tight : I.card + 2 * n0 + n1 + nnot = G.card + 1 →
      ∀ v ∈ V.erase C.output, readsW n C G v = 1 := hacc_tight0
  let R₀ : Finset (Fin N) := Finset.univ.filter (fun x => x.val ∈ V)
  let S₀ : Finset (Fin N) := Finset.univ.filter (fun y => N + y.val ∈ V)
  let J₀ : Finset (Fin h) := Finset.univ.filter (fun j => N + N + j.val ∈ V)
  have hI_card : I.card = R₀.card + S₀.card + J₀.card := by
    let IR := I.filter (· < N)
    let IS := I.filter (fun v => N ≤ v ∧ v < N + N)
    let IJ := I.filter (fun v => N + N ≤ v)
    have hRcard : IR.card = R₀.card := by
      apply Finset.card_bij (fun v hv => ⟨v, (Finset.mem_filter.mp hv).2⟩)
      · intro v hv
        have hvI := (Finset.mem_filter.mp hv).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hvI).1⟩
      · intro a _ b _ hab; exact congrArg Fin.val hab
      · intro x hx
        refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).2, by omega⟩, x.isLt⟩, rfl⟩
    have hScard : IS.card = S₀.card := by
      apply Finset.card_bij (fun v hv => ⟨v - N, by have := (Finset.mem_filter.mp hv).2; omega⟩)
      · intro v hv
        have hvI := (Finset.mem_filter.mp hv).1
        have hv2 := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have heq : N + (v - N) = v := by omega
        rw [heq]; exact (Finset.mem_filter.mp hvI).1
      · intro a ha b hb hab
        have ha2 := (Finset.mem_filter.mp ha).2
        have hb2 := (Finset.mem_filter.mp hb).2
        have := congrArg Fin.val hab; dsimp at this; omega
      · intro y hy
        refine ⟨N + y.val, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hy).2, by omega⟩, by omega⟩, Fin.ext (by simp)⟩
    have hJcard : IJ.card = J₀.card := by
      apply Finset.card_bij (fun v hv => ⟨v - (N + N), by
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
        have h2 := (Finset.mem_filter.mp hv).2; omega⟩)
      · intro v hv
        have hvI := (Finset.mem_filter.mp hv).1
        have hv2 := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have heq : N + N + (v - (N + N)) = v := by omega
        rw [heq]; exact (Finset.mem_filter.mp hvI).1
      · intro a ha b hb hab
        have ha2 := (Finset.mem_filter.mp ha).2
        have hb2 := (Finset.mem_filter.mp hb).2
        have := congrArg Fin.val hab; dsimp at this; omega
      · intro j hj
        refine ⟨N + N + j.val, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hj).2, by omega⟩, by omega⟩, Fin.ext (by simp)⟩
    have hunion : I = IR ∪ IS ∪ IJ := by
      ext v; simp only [IR, IS, IJ, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hv
        by_cases h1 : v < N
        · exact Or.inl (Or.inl ⟨hv, h1⟩)
        · by_cases h2 : v < N + N
          · exact Or.inl (Or.inr ⟨hv, by omega, h2⟩)
          · exact Or.inr ⟨hv, by omega⟩
      · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
    have hd1 : Disjoint IR IS := by rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
    have hd2 : Disjoint (IR ∪ IS) IJ := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [IR, IS, IJ, Finset.mem_union, Finset.mem_filter] at hx1 hx2
      omega
    rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      hRcard, hScard, hJcard]
  have hL_le : R₀.card + S₀.card + J₀.card + 2 * n0 + n1 + nnot ≤ g + 1 := by omega
  have hR_lt : R₀.card < N := by omega
  have hS_lt : S₀.card < N := by omega
  obtain ⟨x_un, hx_un⟩ : ∃ x : Fin N, x ∉ R₀ := by
    by_contra hnone; push Not at hnone
    have : R₀ = Finset.univ := Finset.eq_univ_iff_forall.mpr hnone
    rw [this, Finset.card_univ, Fintype.card_fin] at hR_lt; omega
  obtain ⟨y_un, hy_un⟩ : ∃ y : Fin N, y ∉ S₀ := by
    by_contra hnone; push Not at hnone
    have : S₀ = Finset.univ := Finset.eq_univ_iff_forall.mpr hnone
    rw [this, Finset.card_univ, Fintype.card_fin] at hS_lt; omega
  have hunnamed_const : ∀ x y : Fin N, x ∉ R₀ → y ∉ S₀ →
      tableC N h C w₀ x y = tableC N h C w₀ x_un y_un := by
    intro x y hx hy
    apply wireVal_congr_on_reach hread _ _ (inpVec_length w₀ x y) (inpVec_length w₀ x_un y_un) C.output hout'
    intro v hv hvn
    by_cases hv1 : v < N
    · rw [inpVec_getD_row w₀ x y v hv1, inpVec_getD_row w₀ x_un y_un v hv1]
      have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      have h1 : (⟨v, hv1⟩ : Fin N) ≠ x := fun h => hx (h ▸ hvR)
      have h2 : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
      simp [h1, h2]
    · by_cases hv2 : v < N + N
      · rw [inpVec_getD_col w₀ x y v (by omega) hv2, inpVec_getD_col w₀ x_un y_un v (by omega) hv2]
        have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : N + (v - N) = v := by omega
          rw [this]; exact hv
        have h1 : (⟨v - N, by omega⟩ : Fin N) ≠ y := fun h => hy (h ▸ hvS)
        have h2 : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
        simp [h1, h2]
      · rw [inpVec_getD_seed w₀ x y v (by omega) hvn, inpVec_getD_seed w₀ x_un y_un v (by omega) hvn]
  have hb0_false : tableC N h C w₀ x_un y_un = false := by
    by_contra hb0
    have hb0T : tableC N h C w₀ x_un y_un = true := by
      cases hv : tableC N h C w₀ x_un y_un
      · exact (hb0 hv).elim
      · rfl
    by_cases hLg : R₀.card + S₀.card ≤ g
    · have h1 := area_ge_of_unnamed_true (tableC N h C w₀) R₀ S₀
        (fun x y hx hy => (hunnamed_const x y hx hy).trans hb0T)
      have h2 := mul_compl_ge (N := N) (r := R₀.card) (s := S₀.card) (by omega)
      have h3 : N * (N - g) ≤ N * (N - (R₀.card + S₀.card)) := Nat.mul_le_mul_left N (by omega)
      omega
    · have hL_eq : R₀.card + S₀.card = g + 1 := by omega
      have hJ0 : J₀.card = 0 := by omega
      have hn0_0 : n0 = 0 := by omega
      have hnnot_0 : nnot = 0 := by omega
      have hmon : ∀ u ∈ V, n ≤ u →
          ((gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or) ∧
          (gateAt C (u - n)).inputs ≠ [] := by
        intro u hu hun
        have huG : u ∈ G := Finset.mem_filter.mpr ⟨hu, hun⟩
        have hult : u - n < C.gates.length := by
          have := le_of_mem_reachWires hread C.output u hu; omega
        have hmemC : gateAt C (u - n) ∈ C.gates := by
          unfold gateAt; rw [List.getD_eq_getElem _ _ hult]; exact List.getElem_mem hult
        have hnot_ne : (gateAt C (u - n)).op ≠ .not := by
          intro hEq
          have hmem : u ∈ G.filter (fun z => isNotOp (gateAt C (z - n)).op = true) :=
            Finset.mem_filter.mpr ⟨huG, by rw [hEq]; rfl⟩
          have hpos : 0 < nnot := Finset.card_pos.mpr ⟨u, hmem⟩
          omega
        have hlen_ne : (gateAt C (u - n)).inputs ≠ [] := by
          intro hEq
          have hmem : u ∈ G.filter (fun z => (gateAt C (z - n)).inputs.length = 0) :=
            Finset.mem_filter.mpr ⟨huG, by simp [hEq]⟩
          have hpos : 0 < n0 := Finset.card_pos.mpr ⟨u, hmem⟩
          omega
        rcases (hgates _ hmemC).2 with h1 | h2 | ⟨h3, _⟩
        · exact ⟨Or.inl h1, hlen_ne⟩
        · exact ⟨Or.inr h2, hlen_ne⟩
        · exact (hnot_ne h3).elim
      have hzero : ∀ v ∈ V, v < n → (inpVec w₀ x_un y_un).getD v false = false := by
        intro v hv hvn
        by_cases hv1 : v < N
        · rw [inpVec_getD_row w₀ x_un y_un v hv1]
          have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
          have : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
          simp [this]
        · by_cases hv2 : v < N + N
          · rw [inpVec_getD_col w₀ x_un y_un v (by omega) hv2]
            have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have : N + (v - N) = v := by omega
              rw [this]; exact hv
            have : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
            simp [this]
          · exfalso
            have hvJ : ⟨v - (N + N), by omega⟩ ∈ J₀ := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have : N + N + (v - (N + N)) = v := by omega
              rw [this]; exact hv
            have hpos : 0 < J₀.card := Finset.card_pos.mpr ⟨_, hvJ⟩
            omega
      have hf := wireVal_false_of_all_false hread _ (inpVec_length w₀ x_un y_un) C.output hout' hmon hzero
      change wireVal C (inpVec w₀ x_un y_un) C.output = true at hb0T
      rw [hf] at hb0T; cases hb0T
  have hlines_cov : ∀ x y : Fin N, tableC N h C w₀ x y = true → x ∈ R₀ ∨ y ∈ S₀ := by
    intro x y hxy
    by_contra hneither; push Not at hneither
    rw [hunnamed_const x y hneither.1 hneither.2, hb0_false] at hxy
    cases hxy
  have harea_ub := area_le_of_lines (tableC N h C w₀) R₀ S₀ hlines_cov
  have hL_ge : g ≤ R₀.card + S₀.card := by
    by_contra hlt
    have hle : R₀.card + S₀.card ≤ g - 1 := by omega
    have hmul : (R₀.card + S₀.card) * N ≤ (g - 1) * N := Nat.mul_le_mul_right N hle
    omega
  have hne0_of_n0 : n0 = 0 → ∀ u ∈ V, n ≤ u → (gateAt C (u - n)).inputs ≠ [] := by
    intro hn0 u hu hun hnil
    have hmem : u ∈ G.filter (fun z => (gateAt C (z - n)).inputs.length = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu, hun⟩, by simp [hnil]⟩
    have := Finset.card_pos.mpr ⟨u, hmem⟩
    omega
  by_cases hL_eq : R₀.card + S₀.card = g
  · have hn0_0 : n0 = 0 := by omega
    have hsing_row : ∀ x ∈ R₀, tableC N h C w₀ x y_un = true := by
      intro x hx
      by_contra hnotT
      have hxf : tableC N h C w₀ x y_un = false := by
        cases hv : tableC N h C w₀ x y_un
        · rfl
        · exact (hnotT hv).elim
      have hcov' : ∀ a b : Fin N, tableC N h C w₀ a b = true → a ∈ R₀.erase x ∨ b ∈ S₀ := by
        intro a b hab
        rcases hlines_cov a b hab with haR | hbS
        · by_cases hax : a = x
          · subst hax
            by_cases hbS' : b ∈ S₀
            · exact Or.inr hbS'
            · exfalso
              have heq : tableC N h C w₀ a b = tableC N h C w₀ a y_un := by
                apply wireVal_congr_on_reach hread _ _ (inpVec_length w₀ a b) (inpVec_length w₀ a y_un) C.output hout'
                intro v hv hvn
                by_cases hv1 : v < N
                · rw [inpVec_getD_row w₀ a b v hv1, inpVec_getD_row w₀ a y_un v hv1]
                · by_cases hv2 : v < N + N
                  · rw [inpVec_getD_col w₀ a b v (by omega) hv2, inpVec_getD_col w₀ a y_un v (by omega) hv2]
                    have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
                      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                      have : N + (v - N) = v := by omega
                      rw [this]; exact hv
                    have h1 : (⟨v - N, by omega⟩ : Fin N) ≠ b := fun h => hbS' (h ▸ hvS)
                    have h2 : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
                    simp [h1, h2]
                  · rw [inpVec_getD_seed w₀ a b v (by omega) hvn, inpVec_getD_seed w₀ a y_un v (by omega) hvn]
              rw [heq, hxf] at hab; cases hab
          · exact Or.inl (Finset.mem_erase.mpr ⟨hax, haR⟩)
        · exact Or.inr hbS
      have hub := area_le_of_lines (tableC N h C w₀) (R₀.erase x) S₀ hcov'
      have her := Finset.card_erase_add_one hx
      have heq_card : (R₀.erase x).card + S₀.card = g - 1 := by omega
      rw [heq_card] at hub; omega
    have hsing_col : ∀ y ∈ S₀, tableC N h C w₀ x_un y = true := by
      intro y hy
      by_contra hnotT
      have hyf : tableC N h C w₀ x_un y = false := by
        cases hv : tableC N h C w₀ x_un y
        · rfl
        · exact (hnotT hv).elim
      have hcov' : ∀ a b : Fin N, tableC N h C w₀ a b = true → a ∈ R₀ ∨ b ∈ S₀.erase y := by
        intro a b hab
        rcases hlines_cov a b hab with haR | hbS
        · exact Or.inl haR
        · by_cases hby : b = y
          · subst hby
            by_cases haR' : a ∈ R₀
            · exact Or.inl haR'
            · exfalso
              have heq : tableC N h C w₀ a b = tableC N h C w₀ x_un b := by
                apply wireVal_congr_on_reach hread _ _ (inpVec_length w₀ a b) (inpVec_length w₀ x_un b) C.output hout'
                intro v hv hvn
                by_cases hv1 : v < N
                · rw [inpVec_getD_row w₀ a b v hv1, inpVec_getD_row w₀ x_un b v hv1]
                  have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
                  have h1 : (⟨v, hv1⟩ : Fin N) ≠ a := fun h => haR' (h ▸ hvR)
                  have h2 : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
                  simp [h1, h2]
                · by_cases hv2 : v < N + N
                  · rw [inpVec_getD_col w₀ a b v (by omega) hv2, inpVec_getD_col w₀ x_un b v (by omega) hv2]
                  · rw [inpVec_getD_seed w₀ a b v (by omega) hvn, inpVec_getD_seed w₀ x_un b v (by omega) hvn]
              rw [heq, hyf] at hab; cases hab
          · exact Or.inr (Finset.mem_erase.mpr ⟨hby, hbS⟩)
      have hub := area_le_of_lines (tableC N h C w₀) R₀ (S₀.erase y) hcov'
      have her := Finset.card_erase_add_one hy
      have heq_card : R₀.card + (S₀.erase y).card = g - 1 := by omega
      rw [heq_card] at hub; omega
    by_cases hnot_pos : nnot = 1
    · exfalso
      have hJ0 : J₀.card = 0 := by omega
      have htight : I.card + 2 * n0 + n1 + nnot = G.card + 1 := by omega
      have hreads := hacc_tight htight
      obtain ⟨hev, hrows, hcols, hseeds, hro, hnotc⟩ :=
        unfoldTree_props hN C hread hgates C.output hout' (hne0_of_n0 hn0_0) hreads
      let t := unfoldTree (h := h) hN C C.output
      have ht_rows : t.rows = R₀ := by
        ext x; rw [hrows x]; simp [R₀, V, n]
      have ht_cols : t.cols = S₀ := by
        ext y; rw [hcols y]; simp [S₀, V, n]
      have ht_seeds : t.seeds = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro j hj
        have : j ∈ J₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hseeds j).mp hj⟩
        have := Finset.card_pos.mpr ⟨j, this⟩; omega
      have ht_not : t.notCount = 1 := by
        rw [hnotc]
        have heq : V.filter (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true) =
            G.filter (fun u => isNotOp (gateAt C (u - n)).op = true) := by
          ext u; simp [G, Finset.mem_filter, and_assoc]
        rw [heq]; exact hnot_pos
      have ht0 : t.evalRaw (fun _ => false) (fun _ => false) w₀ = false := by
        have h1 : t.eval w₀ x_un y_un = false := (hev w₀ x_un y_un).trans hb0_false
        trans (t.eval w₀ x_un y_un)
        · unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _
            (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
            (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
            (fun _ _ => rfl)
        · exact h1
      rcases t.tree_not_one_decr w₀ hro ht_seeds ht_not with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · have hxR : x ∈ R₀ := ht_rows ▸ hx
        have h1 : t.eval w₀ x y_un = true := (hev w₀ x y_un).trans (hsing_row x hxR)
        have h2 : t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl)
            (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
            (fun _ _ => rfl)
        have h3 := hdec h2; rw [ht0] at h3; cases h3
      · have hyS : y ∈ S₀ := ht_cols ▸ hy
        have h1 : t.eval w₀ x_un y = true := (hev w₀ x_un y).trans (hsing_col y hyS)
        have h2 : t.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true := by
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _
            (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
            (fun _ _ => rfl) (fun _ _ => rfl)
        have h3 := hdec h2; rw [ht0] at h3; cases h3
    · have hnnot_0 : nnot = 0 := by omega
      by_cases hJ_pos : J₀.card = 1
      · right
        obtain ⟨j₀, hj₀_eq⟩ := Finset.card_eq_one.mp hJ_pos
        have htight : I.card + 2 * n0 + n1 + nnot = G.card + 1 := by omega
        have hreads := hacc_tight htight
        obtain ⟨hev, hrows, hcols, hseeds, hro, hnotc⟩ :=
          unfoldTree_props hN C hread hgates C.output hout' (hne0_of_n0 hn0_0) hreads
        let t := unfoldTree (h := h) hN C C.output
        have ht_rows : t.rows = R₀ := by ext x; rw [hrows x]; simp [R₀, V, n]
        have ht_cols : t.cols = S₀ := by ext y; rw [hcols y]; simp [S₀, V, n]
        have ht_seeds : t.seeds = {j₀} := by
          rw [← hj₀_eq]; ext j; rw [hseeds j]; simp [J₀, V, n]
        have ht_not : t.notCount = 0 := by
          rw [hnotc]
          have heq : V.filter (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true) =
              G.filter (fun u => isNotOp (gateAt C (u - n)).op = true) := by
            ext u; simp [G, Finset.mem_filter, and_assoc]
          rw [heq]; exact hnnot_0
        have ht0 : t.evalRaw (fun _ => false) (fun _ => false) w₀ = false := by
          have h1 : t.eval w₀ x_un y_un = false := (hev w₀ x_un y_un).trans hb0_false
          trans (t.eval w₀ x_un y_un)
          · unfold BTree.eval
            exact t.evalRaw_congr _ _ _ _ _ _
              (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
              (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
              (fun _ _ => rfl)
          · exact h1
        have hrow_t : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
          intro x hx
          have h1 : t.eval w₀ x y_un = true := (hev w₀ x y_un).trans (hsing_row x (ht_rows ▸ hx))
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl)
            (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
            (fun _ _ => rfl)
        have hcol_t : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
          intro y hy
          have h1 : t.eval w₀ x_un y = true := (hev w₀ x_un y).trans (hsing_col y (ht_cols ▸ hy))
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _
            (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
            (fun _ _ => rfl) (fun _ _ => rfl)
        refine ⟨R₀, S₀, j₀, hL_eq, ?_⟩
        cases hwj : w₀ j₀
        · left
          refine ⟨rfl, fun w x y => ?_⟩
          change wireVal C (inpVec w x y) C.output = _
          rw [← hev w x y]
          have hres := t.tree_seed_false w₀ j₀ hro ht_not (fun k hk => by rw [ht_seeds] at hk; exact Finset.mem_singleton.mp hk)
            hwj hrow_t hcol_t w x y
          rw [ht_rows, ht_cols, ht_seeds] at hres
          simpa using hres
        · right
          obtain ⟨B, D, hB, hD, hne, hres⟩ :=
            t.tree_seed_true w₀ j₀ hro ht_not ht_seeds hwj ht0 hrow_t hcol_t
          rw [ht_rows] at hB hne hres; rw [ht_cols] at hD hne hres
          exact ⟨rfl, B, D, hB, hD, hne, fun w x y => (hev w x y).symm.trans (hres w x y)⟩
      · left
        have hJ0 : J₀.card = 0 := by omega
        have hmon : ∀ u ∈ V, n ≤ u → (gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or := by
          intro u hu hun
          have huG : u ∈ G := Finset.mem_filter.mpr ⟨hu, hun⟩
          have hult : u - n < C.gates.length := by
            have := le_of_mem_reachWires hread C.output u hu; omega
          have hmemC : gateAt C (u - n) ∈ C.gates := by
            unfold gateAt; rw [List.getD_eq_getElem _ _ hult]; exact List.getElem_mem hult
          rcases (hgates _ hmemC).2 with h1 | h2 | ⟨h3, _⟩
          · exact Or.inl h1
          · exact Or.inr h2
          · exfalso
            have hmem : u ∈ G.filter (fun z => isNotOp (gateAt C (z - n)).op = true) := Finset.mem_filter.mpr ⟨huG, by rw [h3]; rfl⟩
            have := Finset.card_pos.mpr ⟨u, hmem⟩; omega
        refine ⟨R₀, S₀, by omega, by omega, fun w x y => ?_⟩
        have hindep : tableC N h C w x y = tableC N h C w₀ x y := by
          apply wireVal_congr_on_reach hread _ _ (inpVec_length w x y) (inpVec_length w₀ x y) C.output hout'
          intro v hv hvn
          by_cases hv1 : v < N
          · rw [inpVec_getD_row w x y v hv1, inpVec_getD_row w₀ x y v hv1]
          · by_cases hv2 : v < N + N
            · rw [inpVec_getD_col w x y v (by omega) hv2, inpVec_getD_col w₀ x y v (by omega) hv2]
            · exfalso
              have hvJ : ⟨v - (N + N), by omega⟩ ∈ J₀ := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                have : N + N + (v - (N + N)) = v := by omega
                rw [this]; exact hv
              have := Finset.card_pos.mpr ⟨_, hvJ⟩; omega
        rw [hindep]
        by_cases hmem : x ∈ R₀ ∨ y ∈ S₀
        · simp only [hmem, decide_true]
          rcases hmem with hxR | hyS
          · apply wireVal_mono_on_reach hread (inpVec w₀ x y_un) (inpVec w₀ x y)
              (inpVec_length w₀ x y_un) (inpVec_length w₀ x y) C.output hout' hmon _ (hsing_row x hxR)
            intro v hv hvn hvt
            by_cases hv1 : v < N
            · rw [inpVec_getD_row w₀ x y_un v hv1] at hvt
              rw [inpVec_getD_row w₀ x y v hv1]; exact hvt
            · by_cases hv2 : v < N + N
              · rw [inpVec_getD_col w₀ x y_un v (by omega) hv2] at hvt
                have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  have : N + (v - N) = v := by omega
                  rw [this]; exact hv
                have : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
                simp [this] at hvt
              · rw [inpVec_getD_seed w₀ x y_un v (by omega) hvn] at hvt
                rw [inpVec_getD_seed w₀ x y v (by omega) hvn]; exact hvt
          · apply wireVal_mono_on_reach hread (inpVec w₀ x_un y) (inpVec w₀ x y)
              (inpVec_length w₀ x_un y) (inpVec_length w₀ x y) C.output hout' hmon _ (hsing_col y hyS)
            intro v hv hvn hvt
            by_cases hv1 : v < N
            · rw [inpVec_getD_row w₀ x_un y v hv1] at hvt
              have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
              have : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
              simp [this] at hvt
            · by_cases hv2 : v < N + N
              · rw [inpVec_getD_col w₀ x_un y v (by omega) hv2] at hvt
                rw [inpVec_getD_col w₀ x y v (by omega) hv2]; exact hvt
              · rw [inpVec_getD_seed w₀ x_un y v (by omega) hvn] at hvt
                rw [inpVec_getD_seed w₀ x y v (by omega) hvn]; exact hvt
        · push Not at hmem
          simp only [hmem.1, hmem.2, or_self, decide_false]
          exact (hunnamed_const x y hmem.1 hmem.2).trans hb0_false
  · left
    have hL_eq1 : R₀.card + S₀.card = g + 1 := by omega
    have hJ0 : J₀.card = 0 := by omega
    have hn0_0 : n0 = 0 := by omega
    have hnnot_0 : nnot = 0 := by omega
    have htight : I.card + 2 * n0 + n1 + nnot = G.card + 1 := by omega
    have hreads := hacc_tight htight
    obtain ⟨hev, hrows, hcols, hseeds, hro, hnotc⟩ :=
      unfoldTree_props hN C hread hgates C.output hout' (hne0_of_n0 hn0_0) hreads
    let t := unfoldTree (h := h) hN C C.output
    have ht_rows : t.rows = R₀ := by ext x; rw [hrows x]; simp [R₀, V, n]
    have ht_cols : t.cols = S₀ := by ext y; rw [hcols y]; simp [S₀, V, n]
    have ht_seeds : t.seeds = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro j hj
      have : j ∈ J₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hseeds j).mp hj⟩
      have := Finset.card_pos.mpr ⟨j, this⟩; omega
    have ht_not : t.notCount = 0 := by
      rw [hnotc]
      have heq : V.filter (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true) =
          G.filter (fun u => isNotOp (gateAt C (u - n)).op = true) := by
        ext u; simp [G, Finset.mem_filter, and_assoc]
      rw [heq]; exact hnnot_0
    have harea_eq : areaC (t.eval w₀) = areaC (tableC N h C w₀) := by
      congr 1; funext x y; exact hev w₀ x y
    have hlc_t : t.lineCount = g + 1 := by
      unfold BTree.lineCount; rw [ht_rows, ht_cols]; exact hL_eq1
    have hand_zero : t.andCount = 0 := by
      by_contra hne
      have hm : 1 ≤ t.andCount := by omega
      by_cases hbig : t.hasBigAnd
      · have hle := t.area_le_of_hasBigAnd w₀ hro ht_not ht_seeds hbig
        rw [harea_eq, hlc_t] at hle
        have hg_mul : (g - 1) * N + 2 * N = (g + 1) * N := by
          have : g - 1 + 2 = g + 1 := by omega
          rw [← Nat.add_mul, this]
        omega
      · have hle := t.area_le_of_no_bigAnd w₀ hro ht_not ht_seeds hbig
        rw [harea_eq, hlc_t] at hle
        have hstep : 2 * N + (t.andCount - 1) ≤ 2 * t.andCount * N := by
          have h1 : 2 * t.andCount * N = 2 * N + 2 * (t.andCount - 1) * N := by
            have : t.andCount = 1 + (t.andCount - 1) := by omega
            conv_lhs => rw [this]
            ring
          have h2 : t.andCount - 1 ≤ 2 * (t.andCount - 1) * N := by
            calc t.andCount - 1 = (t.andCount - 1) * 1 := by ring
              _ ≤ (t.andCount - 1) * (2 * N) := Nat.mul_le_mul_left _ (by omega)
              _ = 2 * (t.andCount - 1) * N := by ring
          omega
        have hg_mul : (g - 1) * N + 2 * N = (g + 1) * N := by
          have : g - 1 + 2 = g + 1 := by omega
          rw [← Nat.add_mul, this]
        omega
    refine ⟨R₀, S₀, by omega, by omega, fun w x y => ?_⟩
    change wireVal C (inpVec w x y) C.output = _
    rw [← hev w x y, t.eval_of_no_not_no_and ht_not hand_zero ht_seeds w x y, ht_rows, ht_cols]


end PEqualNP.Outside.L_meta_33622_aux.Classify

namespace PEqualNP.Outside.L_meta_33622_aux.CircAux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

abbrev Legal (N : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N + N) C ∧ C.output < N + N + C.size ∧
  ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
    (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wiresPrefix (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl wiresStep x

lemma wiresPrefix_nil (x : List Bool) : wiresPrefix [] x = x := rfl

lemma wiresPrefix_concat (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresPrefix (gs ++ [g]) x = wiresStep (wiresPrefix gs x) g := by
  simp [wiresPrefix, List.foldl_append]

lemma wiresPrefix_length (gs : List Gate) (x : List Bool) :
    (wiresPrefix gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresPrefix]
  | append_singleton gs g ih =>
    rw [wiresPrefix_concat, wiresStep, List.length_append, List.length_singleton, ih,
      List.length_append, List.length_singleton]
    omega

lemma getD_append_lt {α : Type*} (l₁ l₂ : List α) (i : ℕ) (d : α) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_append_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD]

lemma wiresPrefix_take_getD (gs : List Gate) (x : List Bool) (k w : ℕ)
    (hk : k ≤ gs.length) (hw : w < x.length + k) :
    (wiresPrefix gs x).getD w false = (wiresPrefix (gs.take k) x).getD w false := by
  induction gs using List.reverseRecOn generalizing k with
  | nil => simp at hk; subst hk; rfl
  | append_singleton gs g ih =>
    by_cases hle : k ≤ gs.length
    · rw [List.take_append_of_le_length hle, wiresPrefix_concat, wiresStep,
        getD_append_lt _ _ _ _ (by rw [wiresPrefix_length]; omega)]
      exact ih k hle hw
    · have hk_eq : k = gs.length + 1 := by simp at hk; omega
      subst hk_eq
      rw [List.take_of_length_le (by simp)]

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := by
  have h := wiresPrefix_take_getD C.gates x 0 i (Nat.zero_le _) (by omega)
  change (wiresPrefix C.gates x).getD i false = x.getD i false
  simpa [wiresPrefix] using h

lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ)
    (hRB : ReadsBack x.length C) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  have h1 := wiresPrefix_take_getD C.gates x (j + 1) (x.length + j) (by omega) (by omega)
  have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] := by
    rw [List.take_succ_eq_append_getElem hj]
  have hgate : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD, hj]
  change (wiresPrefix C.gates x).getD (x.length + j) false = _
  rw [h1, htake, wiresPrefix_concat, wiresStep]
  have hlen : (wiresPrefix (C.gates.take j) x).length = x.length + j := by
    rw [wiresPrefix_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [← hlen, getD_append_eq, hgate]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' : i < x.length + j := hRB j hj i (by rwa [hgate])
  exact (wiresPrefix_take_getD C.gates x j i (by omega) hi').symm

def isNot : GateOp → Bool
  | .not => true
  | _ => false

def frontierAux (n : ℕ) (C : Circuit) : ℕ → Finset ℕ × ℕ × Bool → Finset ℕ × ℕ × Bool
  | 0, st => st
  | k + 1, (F, e, hn) =>
    if n + k ∈ F then
      let g := gateAt C k
      frontierAux n C k ((F.erase (n + k)) ∪ g.inputs.toFinset, e + 1, hn || isNot g.op)
    else
      frontierAux n C k (F, e, hn)

lemma frontierAux_inv (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hG : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hcard : F.card + (if hn then 1 else 0) ≤ e + 1) :
    let res := frontierAux n C m (F, e, hn)
    (∀ w ∈ res.1, w < n) ∧
    res.1.card + (if res.2.2 then 1 else 0) ≤ res.2.1 + 1 ∧
    res.2.1 ≤ e + m := by
  induction m generalizing F e hn with
  | zero =>
    simp only [frontierAux]
    refine ⟨by simpa using hF, hcard, by omega⟩
  | succ k ih =>
    by_cases hmem : n + k ∈ F
    · simp only [frontierAux, hmem, ↓reduceIte]
      have hk : k < C.gates.length := by omega
      have hg_mem : gateAt C k ∈ C.gates := by
        simp [gateAt, List.getD, hk]
      have hg := hG (gateAt C k) hg_mem
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have hwF := Finset.mem_of_mem_erase hw1
          have hne := Finset.ne_of_mem_erase hw1
          have := hF w hwF
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have herase : (F.erase (n + k)).card + 1 = F.card := Finset.card_erase_add_one hmem
      have hunion : ((F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset).card ≤
          (F.erase (n + k)).card + (gateAt C k).inputs.toFinset.card := Finset.card_union_le _ _
      have htofin : (gateAt C k).inputs.toFinset.card ≤ (gateAt C k).inputs.length :=
        List.toFinset_card_le _
      have hcard' : ((F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset).card +
          (if hn || isNot (gateAt C k).op then 1 else 0) ≤ (e + 1) + 1 := by
        rcases hg.2 with hand | hor | ⟨hnot, hlen1⟩
        · simp only [hand, isNot, Bool.or_false]
          have := hg.1
          omega
        · simp only [hor, isNot, Bool.or_false]
          have := hg.1
          omega
        · simp only [hnot, isNot, Bool.or_true]
          cases hn <;> simp at hcard ⊢ <;> omega
      have hrec := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hcard'
      exact ⟨hrec.1, hrec.2.1, by omega⟩
    · simp only [frontierAux, hmem, ↓reduceIte]
      have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have hlt := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      have hrec := ih (by omega) F e hn hF' hcard
      exact ⟨hrec.1, hrec.2.1, by omega⟩

lemma frontierAux_agree (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hagree : ∀ w ∈ (frontierAux n C m (F, e, hn)).1, x.getD w false = y.getD w false) :
    ∀ w ∈ F, (C.wires x).getD w false = (C.wires y).getD w false := by
  induction m generalizing F e hn with
  | zero =>
    intro w hw
    have hw_lt : w < n := by simpa using hF w hw
    rw [wires_getD_input C x w (by omega), wires_getD_input C y w (by omega)]
    exact hagree w hw
  | succ k ih =>
    simp only [frontierAux] at hagree
    split_ifs at hagree with hmem
    · have hk : k < C.gates.length := by omega
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have := hF w (Finset.mem_of_mem_erase hw1)
          have := Finset.ne_of_mem_erase hw1
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have ih_res := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hagree
      intro w hw
      by_cases hwk : w = n + k
      · subst hwk
        have hgx := wires_getD_gate C x k (hx ▸ hRB) hk
        have hgy := wires_getD_gate C y k (hy ▸ hRB) hk
        rw [hx] at hgx; rw [hy] at hgy
        rw [hgx, hgy]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
      · exact ih_res w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩))
    · have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      exact ih (by omega) F e hn hF' hagree

lemma frontierAux_mono (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hG : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (m : ℕ) (hm : m ≤ C.gates.length) (F : Finset ℕ) (e : ℕ) (hn : Bool)
    (hF : ∀ w ∈ F, w < n + m)
    (hnoNot : (frontierAux n C m (F, e, hn)).2.2 = false)
    (hmono : ∀ w ∈ (frontierAux n C m (F, e, hn)).1,
      x.getD w false = true → y.getD w false = true) :
    ∀ w ∈ F, (C.wires x).getD w false = true → (C.wires y).getD w false = true := by
  induction m generalizing F e hn with
  | zero =>
    intro w hw hwx
    have hw_lt : w < n := by simpa using hF w hw
    rw [wires_getD_input C x w (by omega)] at hwx
    rw [wires_getD_input C y w (by omega)]
    exact hmono w hw hwx
  | succ k ih =>
    simp only [frontierAux] at hnoNot hmono
    split_ifs at hnoNot hmono with hmem
    · have hk : k < C.gates.length := by omega
      have hF' : ∀ w ∈ (F.erase (n + k)) ∪ (gateAt C k).inputs.toFinset, w < n + k := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw1 | hw2
        · have := hF w (Finset.mem_of_mem_erase hw1)
          have := Finset.ne_of_mem_erase hw1
          omega
        · exact hRB k hk w (List.mem_toFinset.mp hw2)
      have ih_res := ih (by omega) _ (e + 1) (hn || isNot (gateAt C k).op) hF' hnoNot hmono
      have hnot_false : (hn || isNot (gateAt C k).op) = false := by
        clear ih_res hmono hF'
        suffices ∀ m' F' e' hn', (frontierAux n C m' (F', e', hn')).2.2 = false → hn' = false by
          exact this k _ _ _ hnoNot
        intro m'
        induction m' with
        | zero => intro _ _ _ h; exact h
        | succ j ihj =>
          intro F' e' hn' h
          simp only [frontierAux] at h
          split_ifs at h with h1
          · have := ihj _ _ _ h
            exact (by simpa using this : hn' = false ∧ _).1
          · exact ihj _ _ _ h
      have hop_ne_not : (gateAt C k).op ≠ .not := by
        intro hnot
        simp [hnot, isNot] at hnot_false
      have hg := hG (gateAt C k) (by simp [gateAt, List.getD, hk])
      intro w hw hwx
      by_cases hwk : w = n + k
      · subst hwk
        have hgx := wires_getD_gate C x k (hx ▸ hRB) hk
        have hgy := wires_getD_gate C y k (hy ▸ hRB) hk
        rw [hx] at hgx; rw [hy] at hgy
        rw [hgx] at hwx; rw [hgy]
        rcases hg.2 with hand | hor | ⟨hnot, _⟩
        · rw [hand] at hwx ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
            and_imp, forall_apply_eq_imp_iff₂] at hwx ⊢
          intro i hi
          exact ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)) (hwx i hi)
        · rw [hor] at hwx ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hwx ⊢
          rcases hwx with ⟨_, ⟨i, hi, rfl⟩, htrue⟩
          exact ⟨(C.wires y).getD i false, ⟨i, hi, rfl⟩,
            ih_res i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi)) htrue⟩
        · exact absurd hnot hop_ne_not
      · exact ih_res w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwk, hw⟩)) hwx
    · have hF' : ∀ w ∈ F, w < n + k := by
        intro w hw
        have := hF w hw
        have hne : w ≠ n + k := fun heq => hmem (heq ▸ hw)
        omega
      exact ih (by omega) F e hn hF' hnoNot hmono

lemma oneEach_length {N : ℕ} (x y : Fin N) : (oneEach x y).length = N + N := by
  simp [oneEach]

lemma oneEach_getD_left {N : ℕ} (x y : Fin N) (i : ℕ) (hi : i < N) :
    (oneEach x y).getD i false = decide (i = x.val) := by
  unfold oneEach
  rw [getD_append_lt _ _ _ _ (by simp [hi])]
  simp [List.getD, hi, Fin.ext_iff]

lemma oneEach_getD_right {N : ℕ} (x y : Fin N) (j : ℕ) (hj : j < N) :
    (oneEach x y).getD (N + j) false = decide (j = y.val) := by
  unfold oneEach
  simp [List.getD, List.getElem?_append_right, hj, Fin.ext_iff]


lemma area_le_A_gen {N g d p : ℕ} (hg : 0 < g) (hN : 2 * g + 1 < N)
    (hdp : d ≤ p) (hpN : p ≤ N)
    (hmin : ∀ i : ℕ, i ≤ g + 1 → d ≤ i * (g + 1 - i) → p ≤ i * (g + 1 - i))
    (C : Circuit) (hleg : Legal N C) (hsize : C.size ≤ g)
    (harea_d : ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card ≤ (g + 1) * N - d) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card ≤ (g + 1) * N - p := by
  by_cases hd0_eq : d = 0
  · subst hd0_eq
    have hp0 : p ≤ 0 := by
      have := hmin 0 (Nat.zero_le _) (Nat.zero_le _)
      simpa using this
    have hp_eq : p = 0 := by omega
    subst hp_eq
    exact harea_d
  by_cases hpd_eq : p = d
  · subst hpd_eq
    exact harea_d
  have hd0 : 0 < d := by omega
  have hdp_lt : d < p := by omega
  set tbl : Fin N → Fin N → Bool := fun x y => C.eval (oneEach x y)
  set T : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => tbl z.1 z.2 = true)
  set res := frontierAux (N + N) C C.gates.length ({C.output}, 0, false)
  have hinv := frontierAux_inv (N + N) C hleg.1 hleg.2.2 C.gates.length (le_refl _)
    {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) (by simp)
  set F0 : Finset ℕ := res.1
  set SR : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val ∈ F0)
  set SC : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => N + y.val ∈ F0)
  have hSR_SC_card : SR.card + SC.card = F0.card := by
    have hdisj : Disjoint (SR.image Fin.val) (SC.image (fun y : Fin N => N + y.val)) := by
      rw [Finset.disjoint_left]
      intro w hw1 hw2
      rcases Finset.mem_image.mp hw1 with ⟨x, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨y, _, hy⟩
      omega
    have heq : SR.image Fin.val ∪ SC.image (fun y : Fin N => N + y.val) = F0 := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SR, SC]
      constructor
      · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩) <;> assumption
      · intro hw
        have hwlt := hinv.1 w hw
        by_cases h : w < N
        · left; exact ⟨⟨w, h⟩, hw, rfl⟩
        · right
          have hw' : N + (w - N) = w := by omega
          exact ⟨⟨w - N, by omega⟩, by rwa [hw'], hw'⟩
    rw [← heq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
  have hF0_le : F0.card + (if res.2.2 then 1 else 0) ≤ g + 1 := by
    have h1 : F0.card + (if res.2.2 then 1 else 0) ≤ res.2.1 + 1 := hinv.2.1
    have h2 : res.2.1 ≤ 0 + C.gates.length := hinv.2.2
    have h3 : C.gates.length ≤ g := hsize
    omega
  have hab_le : SR.card + SC.card ≤ g + 1 := by omega
  have hSR_lt : SR.card < N := by omega
  have hSC_lt : SC.card < N := by omega
  obtain ⟨x0, hx0⟩ : ∃ x : Fin N, x ∉ SR := by
    by_contra hall; push_neg at hall
    have : SR = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hSR_lt; omega
  obtain ⟨y0, hy0⟩ : ∃ y : Fin N, y ∉ SC := by
    by_contra hall; push_neg at hall
    have : SC = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [this, Finset.card_univ, Fintype.card_fin] at hSC_lt; omega
  have h_agree : ∀ x₁ y₁ x₂ y₂ : Fin N,
      (∀ x ∈ SR, (x = x₁ ↔ x = x₂)) → (∀ y ∈ SC, (y = y₁ ↔ y = y₂)) →
      tbl x₁ y₁ = tbl x₂ y₂ := by
    intro x₁ y₁ x₂ y₂ hxr hyc
    apply frontierAux_agree (N + N) C hleg.1 (oneEach x₁ y₁) (oneEach x₂ y₂)
      (oneEach_length x₁ y₁) (oneEach_length x₂ y₂) C.gates.length (le_refl _)
      {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1)
    · intro w hw
      have hwlt := hinv.1 w hw
      by_cases h : w < N
      · rw [oneEach_getD_left x₁ y₁ w h, oneEach_getD_left x₂ y₂ w h]
        have hmem : (⟨w, h⟩ : Fin N) ∈ SR := by simp [SR, F0, res, hw]
        have hiff := hxr ⟨w, h⟩ hmem
        simp [Fin.ext_iff] at hiff
        simp [hiff]
      · have hj : w - N < N := by omega
        have hw_eq : w = N + (w - N) := by omega
        rw [hw_eq, oneEach_getD_right x₁ y₁ (w - N) hj, oneEach_getD_right x₂ y₂ (w - N) hj]
        have hmem : (⟨w - N, hj⟩ : Fin N) ∈ SC := by simp [SC, F0, res, ← hw_eq, hw]
        have hiff := hyc ⟨w - N, hj⟩ hmem
        simp [Fin.ext_iff] at hiff
        simp [hiff]
    · simp
  have hout_false : ∀ x y : Fin N, x ∉ SR → y ∉ SC → tbl x y = false := by
    have hconst : ∀ x y : Fin N, x ∉ SR → y ∉ SC → tbl x y = tbl x0 y0 := by
      intro x y hx hy
      apply h_agree x y x0 y0
      · intro a ha; constructor <;> intro h <;> subst h <;> contradiction
      · intro b hb; constructor <;> intro h <;> subst h <;> contradiction
    cases h0 : tbl x0 y0
    · intro x y hx hy; rw [hconst x y hx hy, h0]
    · exfalso
      have hsub : SRᶜ ×ˢ SCᶜ ⊆ T := by
        intro z hz
        simp only [Finset.mem_product, Finset.mem_compl] at hz
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hconst z.1 z.2 hz.1 hz.2, h0]
      have hcard_le := Finset.card_le_card hsub
      rw [Finset.card_product, Finset.card_compl, Finset.card_compl, Fintype.card_fin] at hcard_le
      have h1 : (N - SR.card) * (N - SC.card) ≥ (N - (g + 1)) * N := by
        have h2 : SR.card * N + SC.card * N ≤ (g + 1) * N := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right N hab_le
        have h3 : (N - SR.card) * (N - SC.card) + SR.card * N + SC.card * N =
            N * N + SR.card * SC.card := by
          zify [le_of_lt hSR_lt, le_of_lt hSC_lt]; ring
        have h4 : (N - (g + 1)) * N + (g + 1) * N = N * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        omega
      have h5 : (g + 1) * N ≤ (N - (g + 1)) * N := Nat.mul_le_mul_right N (by omega)
      have hpos : 0 < (g + 1) * N := Nat.mul_pos (by omega) (by omega)
      change T.card ≤ (g + 1) * N - d at harea_d
      omega
  set U : Finset (Fin N × Fin N) := Finset.univ.filter (fun z => z.1 ∈ SR ∨ z.2 ∈ SC)
  have hT_sub_U : T ⊆ U := by
    intro z hz
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnot
    push_neg at hnot
    have := hout_false z.1 z.2 hnot.1 hnot.2
    rw [this] at hz; exact Bool.false_ne_true hz
  have hU_card : U.card = (SR.card + SC.card) * N - SR.card * SC.card := by
    have hU_eq : U = (SR ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ SC) := by
      ext z; simp [U]
    have hU_inter : (SR ×ˢ Finset.univ) ∩ (Finset.univ ×ˢ SC) = SR ×ˢ SC := by
      ext z; simp
    have hinc := Finset.card_union_add_card_inter (SR ×ˢ (Finset.univ : Finset (Fin N)))
      ((Finset.univ : Finset (Fin N)) ×ˢ SC)
    rw [← hU_eq, hU_inter, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_univ, Fintype.card_fin] at hinc
    have hmul : SR.card * SC.card ≤ SR.card * N + N * SC.card := by
      calc SR.card * SC.card ≤ SR.card * N := Nat.mul_le_mul_left _ (le_of_lt hSC_lt)
        _ ≤ SR.card * N + N * SC.card := Nat.le_add_right _ _
    have hadd : (SR.card + SC.card) * N = SR.card * N + N * SC.card := by ring
    omega
  have hT_le_U : T.card ≤ (SR.card + SC.card) * N - SR.card * SC.card := by
    rw [← hU_card]; exact Finset.card_le_card hT_sub_U
  by_cases hsum_le : SR.card + SC.card ≤ g
  · have h1 : (SR.card + SC.card) * N ≤ g * N := Nat.mul_le_mul_right N hsum_le
    have h2 : g * N + N = (g + 1) * N := by ring
    omega
  · have hsum_eq : SR.card + SC.card = g + 1 := by omega
    by_cases hprod : d ≤ SR.card * SC.card
    · have hge := hmin SR.card (by omega) (by rwa [show g + 1 - SR.card = SC.card by omega])
      rw [show g + 1 - SR.card = SC.card by omega] at hge
      rw [hsum_eq] at hT_le_U
      omega
    · have hprod_lt : SR.card * SC.card < d := by omega
      have hnoNot : res.2.2 = false := by
        cases h : res.2.2
        · rfl
        · rw [h] at hF0_le; simp at hF0_le; omega
      by_cases hrow_false : ∃ x ∈ SR, tbl x y0 = false
      · rcases hrow_false with ⟨x1, hx1, hfx1⟩
        set Bad : Finset (Fin N × Fin N) := {x1} ×ˢ SCᶜ
        have hBad_sub : Bad ⊆ U \ T := by
          intro z hz
          simp only [Bad, Finset.mem_product, Finset.mem_singleton, Finset.mem_compl] at hz
          rcases hz with ⟨hz1, hy⟩
          simp only [Finset.mem_sdiff, U, T, Finset.mem_filter, Finset.mem_univ, true_and]
          refine ⟨Or.inl (hz1 ▸ hx1), ?_⟩
          have heq : tbl z.1 z.2 = tbl x1 y0 := by
            rw [hz1]
            apply h_agree x1 z.2 x1 y0 (fun _ _ => Iff.rfl)
            intro b hb; constructor <;> intro h <;> subst h <;> contradiction
          rw [heq, hfx1]; decide
        have hcard_bad : Bad.card = N - SC.card := by
          simp [Bad, Finset.card_product, Finset.card_compl, Fintype.card_fin]
        have hdiff := Finset.card_le_card hBad_sub
        rw [hcard_bad, Finset.card_sdiff_of_subset hT_sub_U, hU_card, hsum_eq] at hdiff
        have h1 : g * N + N = (g + 1) * N := by ring
        have hSR_pos : 0 < SR.card := Finset.card_pos.mpr ⟨x1, hx1⟩
        have h2 : SC.card ≤ SR.card * SC.card := Nat.le_mul_of_pos_left SC.card hSR_pos
        omega
      · by_cases hcol_false : ∃ y ∈ SC, tbl x0 y = false
        · rcases hcol_false with ⟨y1, hy1, hfy1⟩
          set Bad : Finset (Fin N × Fin N) := SRᶜ ×ˢ {y1}
          have hBad_sub : Bad ⊆ U \ T := by
            intro z hz
            simp only [Bad, Finset.mem_product, Finset.mem_singleton, Finset.mem_compl] at hz
            rcases hz with ⟨hx, hz2⟩
            simp only [Finset.mem_sdiff, U, T, Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨Or.inr (hz2 ▸ hy1), ?_⟩
            have heq : tbl z.1 z.2 = tbl x0 y1 := by
              rw [hz2]
              apply h_agree z.1 y1 x0 y1
              · intro a ha; constructor <;> intro h <;> subst h <;> contradiction
              · exact fun _ _ => Iff.rfl
            rw [heq, hfy1]; decide
          have hcard_bad : Bad.card = N - SR.card := by
            simp [Bad, Finset.card_product, Finset.card_compl, Fintype.card_fin]
          have hdiff := Finset.card_le_card hBad_sub
          rw [hcard_bad, Finset.card_sdiff_of_subset hT_sub_U, hU_card, hsum_eq] at hdiff
          have h1 : g * N + N = (g + 1) * N := by ring
          have hSC_pos : 0 < SC.card := Finset.card_pos.mpr ⟨y1, hy1⟩
          have h2 : SR.card ≤ SR.card * SC.card := Nat.le_mul_of_pos_right SR.card hSC_pos
          omega
        · exfalso
          push_neg at hrow_false hcol_false
          have hU_sub_T : U ⊆ T := by
            intro z hz
            simp only [U, Finset.mem_filter, Finset.mem_univ, true_and] at hz
            simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hz with hx | hy
            · have hbase : tbl z.1 y0 = true := Bool.eq_true_of_not_eq_false (hrow_false z.1 hx)
              apply frontierAux_mono (N + N) C hleg.1 hleg.2.2 (oneEach z.1 y0) (oneEach z.1 z.2)
                (oneEach_length _ _) (oneEach_length _ _) C.gates.length (le_refl _)
                {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) hnoNot
              · intro w hw hwt
                have hwlt := hinv.1 w hw
                by_cases h : w < N
                · rw [oneEach_getD_left z.1 y0 w h] at hwt
                  rw [oneEach_getD_left z.1 z.2 w h]; exact hwt
                · have hj : w - N < N := by omega
                  have hw_eq : w = N + (w - N) := by omega
                  rw [hw_eq, oneEach_getD_right z.1 y0 (w - N) hj] at hwt
                  have hyeq : (⟨w - N, hj⟩ : Fin N) = y0 := Fin.ext (of_decide_eq_true hwt)
                  have hmem : (⟨w - N, hj⟩ : Fin N) ∈ SC := by simp [SC, F0, res, ← hw_eq, hw]
                  rw [hyeq] at hmem; exact absurd hmem hy0
              · simp
              · exact hbase
            · have hbase : tbl x0 z.2 = true := Bool.eq_true_of_not_eq_false (hcol_false z.2 hy)
              apply frontierAux_mono (N + N) C hleg.1 hleg.2.2 (oneEach x0 z.2) (oneEach z.1 z.2)
                (oneEach_length _ _) (oneEach_length _ _) C.gates.length (le_refl _)
                {C.output} 0 false (by intro w hw; simp at hw; subst hw; exact hleg.2.1) hnoNot
              · intro w hw hwt
                have hwlt := hinv.1 w hw
                by_cases h : w < N
                · rw [oneEach_getD_left x0 z.2 w h] at hwt
                  have hxeq : (⟨w, h⟩ : Fin N) = x0 := Fin.ext (of_decide_eq_true hwt)
                  have hmem : (⟨w, h⟩ : Fin N) ∈ SR := by simp [SR, F0, res, hw]
                  rw [hxeq] at hmem; exact absurd hmem hx0
                · have hj : w - N < N := by omega
                  have hw_eq : w = N + (w - N) := by omega
                  rw [hw_eq, oneEach_getD_right x0 z.2 (w - N) hj] at hwt
                  rw [hw_eq, oneEach_getD_right z.1 z.2 (w - N) hj]; exact hwt
              · simp
              · exact hbase
          have hT_eq_U : T.card = U.card := le_antisymm (Finset.card_le_card hT_sub_U)
            (Finset.card_le_card hU_sub_T)
          rw [hU_card, hsum_eq] at hT_eq_U
          have hmul_le : SR.card * SC.card ≤ (g + 1) * N := by
            have : SR.card * SC.card < N := by omega
            have : 1 * N ≤ (g + 1) * N := Nat.mul_le_mul_right N (by omega)
            omega
          have hd_le : d ≤ (g + 1) * N := by
            have : 1 * N ≤ (g + 1) * N := Nat.mul_le_mul_right N (by omega)
            omega
          change T.card ≤ (g + 1) * N - d at harea_d
          omega

def targetI (N t u : ℕ) (x y : Fin N) : Bool :=
  decide ((y.val + N - x.val + N - u % N) % N < t)

lemma card_targetI_col {N t : ℕ} (ht : t ≤ N) (u : ℕ) (x : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun y => targetI N t u x y = true)).card = t := by
  have hN : 0 < N := by exact Fin.pos x
  let f : Fin N → Fin N := fun y => ⟨(y.val + N - x.val + N - u % N) % N, Nat.mod_lt _ hN⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro y₁ y₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hx := x.isLt; have hu := Nat.mod_lt u hN
    have hy1 := y₁.isLt; have hy2 := y₂.isLt
    have h1 : (y₁.val + (N - x.val) + (N - u % N)) % N = (y₂.val + (N - x.val) + (N - u % N)) % N := by
      have e1 : y₁.val + N - x.val + N - u % N = y₁.val + (N - x.val) + (N - u % N) := by omega
      have e2 : y₂.val + N - x.val + N - u % N = y₂.val + (N - x.val) + (N - u % N) := by omega
      rw [← e1, ← e2]; exact hv
    have h2 : (y₁.val + ((N - x.val) + (N - u % N))) % N =
        (y₂.val + ((N - x.val) + (N - u % N))) % N := by
      simpa [Nat.add_assoc] using h1
    apply Fin.ext
    have h3 : (y₁.val + ((N - x.val) + (N - u % N))) % N =
        (y₁.val + ((N - x.val) + (N - u % N)) % N) % N := by
      rw [Nat.add_mod, Nat.add_mod y₁.val, Nat.mod_mod]
    have h4 : (y₂.val + ((N - x.val) + (N - u % N))) % N =
        (y₂.val + ((N - x.val) + (N - u % N)) % N) % N := by
      rw [Nat.add_mod, Nat.add_mod y₂.val, Nat.mod_mod]
    set c := ((N - x.val) + (N - u % N)) % N
    have hc : c < N := Nat.mod_lt _ hN
    rw [h3, h4] at h2
    by_cases h1c : y₁.val + c < N <;> by_cases h2c : y₂.val + c < N
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at h2; omega
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_sub_mod (by omega),
        Nat.mod_eq_of_lt (by omega)] at h2; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt h2c] at h2; omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h2; omega
  let e := Equiv.ofBijective f hbij
  have hcard : ((Finset.univ : Finset (Fin N)).filter (fun y => (f y).val < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card := by
    refine Finset.card_bij (fun y _ => f y) (fun y hy => by simpa using hy)
      (fun a _ b _ h => hbij.1 h) (fun z hz => ?_)
    obtain ⟨y, hy⟩ := hbij.2 z
    exact ⟨y, by simpa [hy] using hz, hy⟩
  have hlt : ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card = t := by
    refine (Finset.card_bij (fun z _ => z.val) (fun z hz => by simp at hz ⊢; exact hz)
      (fun a _ b _ h => Fin.ext h) (fun k hk => ?_)).trans (Finset.card_range t)
    simp at hk
    exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
  simpa [targetI, f] using hcard.trans hlt

lemma card_targetI_row {N t : ℕ} (ht : t ≤ N) (u : ℕ) (y : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun x => targetI N t u x y = true)).card = t := by
  have hN : 0 < N := Fin.pos y
  let f : Fin N → Fin N := fun x => ⟨(y.val + N - x.val + N - u % N) % N, Nat.mod_lt _ hN⟩
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, rfl⟩
    intro x₁ x₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hy := y.isLt; have hu := Nat.mod_lt u hN
    have hx1 := x₁.isLt; have hx2 := x₂.isLt
    have h1 : ((N - x₁.val) + (y.val + (N - u % N))) % N =
        ((N - x₂.val) + (y.val + (N - u % N))) % N := by
      have e1 : y.val + N - x₁.val + N - u % N = (N - x₁.val) + (y.val + (N - u % N)) := by omega
      have e2 : y.val + N - x₂.val + N - u % N = (N - x₂.val) + (y.val + (N - u % N)) := by omega
      rw [← e1, ← e2]; exact hv
    set c := (y.val + (N - u % N)) % N
    have hc : c < N := Nat.mod_lt _ hN
    have h3 : ((N - x₁.val) + (y.val + (N - u % N))) % N = ((N - x₁.val) + c) % N := by
      rw [Nat.add_mod, Nat.add_mod (N - x₁.val), Nat.mod_mod]
    have h4 : ((N - x₂.val) + (y.val + (N - u % N))) % N = ((N - x₂.val) + c) % N := by
      rw [Nat.add_mod, Nat.add_mod (N - x₂.val), Nat.mod_mod]
    rw [h3, h4] at h1
    apply Fin.ext
    by_cases h1c : N - x₁.val + c < N <;> by_cases h2c : N - x₂.val + c < N
    · rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_of_lt h2c] at h1; omega
    · have hlt2 : N - x₂.val + c - N < N := by omega
      rw [Nat.mod_eq_of_lt h1c, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at h1
      omega
    · have hlt1 : N - x₁.val + c - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt h2c] at h1
      omega
    · have hlt1 : N - x₁.val + c - N < N := by omega
      have hlt2 : N - x₂.val + c - N < N := by omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2] at h1
      omega
  have hcard : ((Finset.univ : Finset (Fin N)).filter (fun x => (f x).val < t)).card =
      ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card := by
    refine Finset.card_bij (fun x _ => f x) (fun x hx => by simpa using hx)
      (fun a _ b _ h => hbij.1 h) (fun z hz => ?_)
    obtain ⟨x, hx⟩ := hbij.2 z
    exact ⟨x, by simpa [hx] using hz, hx⟩
  have hlt : ((Finset.univ : Finset (Fin N)).filter (fun z : Fin N => z.val < t)).card = t := by
    refine (Finset.card_bij (fun z _ => z.val) (fun z hz => by simp at hz ⊢; exact hz)
      (fun a _ b _ h => Fin.ext h) (fun k hk => ?_)).trans (Finset.card_range t)
    simp at hk
    exact ⟨⟨k, by omega⟩, by simp [hk], rfl⟩
  simpa [targetI, f] using hcard.trans hlt

lemma card_targetI_u {N t : ℕ} (ht : t ≤ N) (x y : Fin N) :
    ((Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t u.val x y = true)).card = t := by
  have hN : 0 < N := Fin.pos x
  have heq : (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t u.val x y = true) =
      (Finset.univ : Finset (Fin N)).filter (fun u : Fin N => targetI N t x.val u y = true) := by
    apply Finset.filter_congr
    intro u _
    simp only [targetI, Nat.mod_eq_of_lt u.isLt, Nat.mod_eq_of_lt x.isLt]
    have h1 : y.val + N - x.val + N - u.val = y.val + N - u.val + N - x.val := by
      have := x.isLt; have := u.isLt; omega
    rw [h1]
  rw [heq]
  exact card_targetI_row ht x.val y

lemma card_targetI_all {N t : ℕ} (ht : t ≤ N) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => targetI N t u z.1 z.2 = true)).card =
      N * t := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have hinner : ∀ x : Fin N, ∑ y : Fin N, (if targetI N t u x y = true then 1 else 0) = t := by
    intro x
    rw [← Finset.card_filter]
    exact card_targetI_col ht u x
  simp [hinner]

lemma loss_add_two_overlap {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) (u : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z ≠ targetI N t u z.1 z.2)).card +
      2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z = true ∧ targetI N t u z.1 z.2 = true)).card =
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card + N * t := by
  rw [← card_targetI_all ht u]
  simp only [Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  cases P z <;> cases targetI N t u z.1 z.2 <;> simp

lemma sum_overlap_eq {N t : ℕ} (ht : t ≤ N) (P : Fin N × Fin N → Bool) :
    ∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z = true ∧ targetI N t u.val z.1 z.2 = true)).card =
    t * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : P z = true
  · simp only [hp, true_and, ↓reduceIte, mul_one]
    rw [← Finset.card_filter]
    exact card_targetI_u ht z.1 z.2
  · simp [hp]

lemma sum_loss_eq {N t : ℕ} (hNt : N < 2 * t) (ht : t ≤ N) (P : Fin N × Fin N → Bool) :
    ∑ u : Fin N, ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => P z ≠ targetI N t u.val z.1 z.2)).card +
      (2 * t - N) * ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card =
    N * (N * t) := by
  have hsum : ∑ u : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z ≠ targetI N t u.val z.1 z.2)).card +
      2 * ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => P z = true ∧ targetI N t u.val z.1 z.2 = true)).card) =
      ∑ _u : Fin N, (((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card +
        N * t) := by
    apply Finset.sum_congr rfl
    intro u _
    exact loss_add_two_overlap ht P u.val
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_overlap_eq ht P,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  set a := ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => P z = true)).card
  have h1 : 2 * (t * a) = (2 * t - N) * a + N * a := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega), Nat.mul_assoc]
  have h2 : N * (a + N * t) = N * a + N * (N * t) := by ring
  omega

def orChain (n : ℕ) (w0 : ℕ) (ws : List ℕ) : Circuit :=
  { gates := (List.range ws.length).zipWith
      (fun k w => ⟨GateOp.or, [if k = 0 then w0 else n + k - 1, w]⟩) ws
    output := if ws.length = 0 then w0 else n + ws.length - 1 }

lemma orChain_size (n w0 : ℕ) (ws : List ℕ) : (orChain n w0 ws).size = ws.length := by
  simp [Circuit.size, orChain]

lemma orChain_readsBack (n w0 : ℕ) (ws : List ℕ) (hw0 : w0 < n) (hws : ∀ w ∈ ws, w < n) :
    ReadsBack n (orChain n w0 ws) := by
  intro j hj i hi
  simp only [orChain, List.length_zipWith, List.length_range, min_self] at hj
  have hgate : gateAt (orChain n w0 ws) j =
      ⟨GateOp.or, [if j = 0 then w0 else n + j - 1, ws[j]]⟩ := by
    simp [gateAt, orChain, List.getD, hj]
  rw [hgate] at hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · split_ifs <;> omega
  · have := hws ws[j] (List.getElem_mem hj)
    omega

lemma orChain_legal (N w0 : ℕ) (ws : List ℕ) (hw0 : w0 < N + N)
    (hws : ∀ w ∈ ws, w < N + N) : Legal N (orChain (N + N) w0 ws) := by
  refine ⟨orChain_readsBack (N + N) w0 ws hw0 hws, ?_, ?_⟩
  · rw [orChain_size]
    simp only [orChain]
    split_ifs <;> omega
  · intro gate hgate
    rw [List.mem_iff_getElem] at hgate
    rcases hgate with ⟨j, hj, rfl⟩
    simp [orChain]

lemma orChain_eval (n w0 : ℕ) (ws : List ℕ) (hw0 : w0 < n) (hws : ∀ w ∈ ws, w < n)
    (x : List Bool) (hx : x.length = n) :
    (orChain n w0 ws).eval x = (w0 :: ws).any (fun w => x.getD w false) := by
  have hRB := orChain_readsBack n w0 ws hw0 hws
  have hwire : ∀ j < ws.length,
      ((orChain n w0 ws).wires x).getD (n + j) false =
        (w0 :: ws.take (j + 1)).any (fun w => x.getD w false) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hgt := wires_getD_gate (orChain n w0 ws) x 0 (hx ▸ hRB) (by simp [orChain, hj])
      rw [hx] at hgt
      have hga : gateAt (orChain n w0 ws) 0 = ⟨GateOp.or, [w0, ws[0]]⟩ := by
        simp [gateAt, orChain, List.getD, hj]
      rw [hgt, hga]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [wires_getD_input _ _ w0 (by omega),
        wires_getD_input _ _ ws[0] (by have := hws ws[0] (List.getElem_mem hj); omega)]
      rw [List.take_succ_eq_append_getElem hj]
      simp
    | succ k ih =>
      intro hj
      have hgt := wires_getD_gate (orChain n w0 ws) x (k + 1) (hx ▸ hRB)
        (by simp [orChain, hj])
      rw [hx] at hgt
      have hga : gateAt (orChain n w0 ws) (k + 1) = ⟨GateOp.or, [n + k, ws[k + 1]]⟩ := by
        simp [gateAt, orChain, List.getD, hj]
      rw [hgt, hga]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false]
      rw [ih (by omega),
        wires_getD_input _ _ ws[k + 1] (by have := hws ws[k + 1] (List.getElem_mem hj); omega)]
      rw [List.take_succ_eq_append_getElem hj]
      simp only [List.any_cons, List.any_append, List.any_nil, Bool.or_false]
      exact Bool.or_assoc _ _ _
  cases hlen : ws.length with
  | zero =>
    have hws_nil : ws = [] := List.eq_nil_of_length_eq_zero hlen
    subst hws_nil
    simp only [Circuit.eval, orChain, List.length_nil, ↓reduceIte, List.any_cons, List.any_nil,
      Bool.or_false]
    exact wires_getD_input _ _ w0 (by omega)
  | succ m =>
    have h1 := hwire m (by omega)
    rw [show m + 1 = ws.length from hlen.symm, List.take_length] at h1
    simpa [Circuit.eval, orChain, hlen] using h1


end PEqualNP.Outside.L_meta_33622_aux.CircAux

namespace PEqualNP.Outside.L_meta_33622_aux.Cycle

open Finset


def sig (N t k : ℕ) : ℕ := (k % (N / Nat.gcd t N)) * t + k / (N / Nat.gcd t N)

theorem L_pos {N : ℕ} (hN : 0 < N) (t : ℕ) : 0 < N / Nat.gcd t N :=
  Nat.div_pos (Nat.le_of_dvd hN (Nat.gcd_dvd_right t N)) (Nat.gcd_pos_of_pos_right t hN)

theorem NLg (N t : ℕ) : N = N / Nat.gcd t N * Nat.gcd t N :=
  (Nat.div_mul_cancel (Nat.gcd_dvd_right t N)).symm

theorem sig_inj {N : ℕ} (hN : 0 < N) (t : ℕ) (k k' : ℕ) (hk : k < N) (hk' : k' < N)
    (h : sig N t k % N = sig N t k' % N) : k = k' := by
  unfold sig at h
  have hL := L_pos hN t
  have hNL := NLg N t
  have hg : 0 < Nat.gcd t N := Nat.gcd_pos_of_pos_right t hN
  set L := N / Nat.gcd t N with hLd
  have hc : k / L < Nat.gcd t N := Nat.div_lt_of_lt_mul (by rw [← hNL]; exact hk)
  have hc' : k' / L < Nat.gcd t N := Nat.div_lt_of_lt_mul (by rw [← hNL]; exact hk')
  have hgN : (k % L) * t + k / L ≡ (k' % L) * t + k' / L [MOD Nat.gcd t N] :=
    Nat.ModEq.of_dvd (Nat.gcd_dvd_right t N) h
  have ht0 : t % Nat.gcd t N = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_left t N)
  have e1 : ∀ m, (m % L) * t + m / L ≡ m / L [MOD Nat.gcd t N] := by
    intro m
    unfold Nat.ModEq
    rw [Nat.add_mod, Nat.mul_mod, ht0, mul_zero, Nat.zero_mod, zero_add, Nat.mod_mod]
  have hcc : k / L = k' / L := by
    have h2 := ((e1 k).symm.trans hgN).trans (e1 k')
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at h2
  rw [hcc] at h
  have h3 : (k % L) * t ≡ (k' % L) * t [MOD N] := Nat.ModEq.add_right_cancel' (k' / L) h
  have h4 : k % L ≡ k' % L [MOD L] := by
    have := Nat.ModEq.cancel_right_div_gcd hN h3
    rwa [Nat.gcd_comm] at this
  unfold Nat.ModEq at h4
  rw [Nat.mod_mod, Nat.mod_mod] at h4
  rw [← Nat.div_add_mod k L, ← Nat.div_add_mod k' L, hcc, h4]

theorem Lt_eq {N : ℕ} (hN : 0 < N) (t : ℕ) : N / Nat.gcd t N * t = N * (t / Nat.gcd t N) := by
  have hg : 0 < Nat.gcd t N := Nat.gcd_pos_of_pos_right t hN
  obtain ⟨L, hL⟩ := Nat.gcd_dvd_right t N
  obtain ⟨t', ht'⟩ := Nat.gcd_dvd_left t N
  generalize Nat.gcd t N = g at *
  subst hL ht'
  rw [Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]
  ring

def G (f : ℕ → ℕ) (N t B k : ℕ) : ℕ := f (sig N t k + B + t) - f (sig N t k + B)

theorem block (f : ℕ → ℕ) (hf : Monotone f) {N : ℕ} (hN : 0 < N) (t B q j : ℕ)
    (hj : j ≤ N / Nat.gcd t N) :
    ∑ i ∈ range j, G f N t B (N / Nat.gcd t N * q + i) = f (q + j * t + B) - f (q + B) := by
  have hL := L_pos hN t
  have hs : ∀ i ∈ range j, G f N t B (N / Nat.gcd t N * q + i) =
      (fun i => f (q + i * t + B)) (i + 1) - (fun i => f (q + i * t + B)) i := by
    intro i hi
    rw [Finset.mem_range] at hi
    unfold G sig
    have e1 : (N / Nat.gcd t N * q + i) % (N / Nat.gcd t N) = i := by
      rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    have e2 : (N / Nat.gcd t N * q + i) / (N / Nat.gcd t N) = q := by
      rw [add_comm, Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt (by omega), zero_add]
    rw [e1, e2]
    dsimp only
    rw [show i * t + q + B + t = q + (i + 1) * t + B by ring,
      show i * t + q + B = q + i * t + B by ring]
  rw [Finset.sum_congr rfl hs, Finset.sum_range_tsub (f := fun i => f (q + i * t + B))
    (fun a b hab => hf (by nlinarith))]
  simp

theorem full (f : ℕ → ℕ) (hf : Monotone f) {N : ℕ} (hN : 0 < N)
    (hsh : ∀ j m, f (j + N * m) = f j + m) (t B q : ℕ) :
    ∑ k ∈ range (N / Nat.gcd t N * q), G f N t B k = q * (t / Nat.gcd t N) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show N / Nat.gcd t N * (q + 1) = N / Nat.gcd t N * q + N / Nat.gcd t N by ring,
      Finset.sum_range_add, ih, block f hf hN t B q _ le_rfl]
    have hLt := Lt_eq hN t
    rw [show q + N / Nat.gcd t N * t + B = q + B + N * (t / Nat.gcd t N) by rw [hLt]; ring, hsh]
    rw [Nat.add_sub_cancel_left]
    ring

theorem total (f : ℕ → ℕ) (hf : Monotone f) {N : ℕ} (hN : 0 < N)
    (hsh : ∀ j m, f (j + N * m) = f j + m) (t B r : ℕ) :
    ∑ k ∈ range r, G f N t B k = r / (N / Nat.gcd t N) * (t / Nat.gcd t N) +
      (f (r / (N / Nat.gcd t N) + r % (N / Nat.gcd t N) * t + B) -
        f (r / (N / Nat.gcd t N) + B)) := by
  have hL := L_pos hN t
  conv_lhs => rw [← Nat.div_add_mod r (N / Nat.gcd t N)]
  rw [Finset.sum_range_add, full f hf hN hsh, block f hf hN t B _ _ (Nat.mod_lt _ hL).le]

def C (N u M : ℕ) : ℕ := (M + N - 1 - u) / N

theorem C_mono (N u : ℕ) : Monotone (C N u) := fun a b h => Nat.div_le_div_right (by omega)

theorem C_shift {N u : ℕ} (hN : 0 < N) (hu : u < N) (j m : ℕ) :
    C N u (j + N * m) = C N u j + m := by
  unfold C
  rw [show j + N * m + N - 1 - u = (j + N - 1 - u) + N * m by omega, Nat.add_mul_div_left _ _ hN]

theorem diffmod {N u : ℕ} (hN : 0 < N) (hu : u < N) (M d : ℕ) :
    C N u (M + d) - C N u M = C N u (M % N + d) - C N u (M % N) := by
  have h := Nat.mod_add_div M N
  have e1 : C N u (M + d) = C N u (M % N + d) + M / N := by
    rw [← C_shift hN hu]; congr 1; omega
  have e2 : C N u M = C N u (M % N) + M / N := by
    rw [← C_shift hN hu]; congr 1; omega
  rw [e1, e2]; omega

theorem diffcong {N u : ℕ} (hN : 0 < N) (hu : u < N) (M M' d : ℕ) (h : M % N = M' % N) :
    C N u (M + d) - C N u M = C N u (M' + d) - C N u M' := by
  rw [diffmod hN hu M d, diffmod hN hu M' d, h]

theorem dm {N : ℕ} (_hN : 0 < N) (x : ℕ) (h : x < 3 * N) :
    (x < N ∧ x / N = 0 ∧ x % N = x) ∨ (N ≤ x ∧ x < 2 * N ∧ x / N = 1 ∧ x % N = x - N) ∨
      (2 * N ≤ x ∧ x / N = 2 ∧ x % N = x - 2 * N) := by
  rcases Nat.lt_or_ge x N with h1 | h1
  · left; exact ⟨h1, Nat.div_eq_of_lt h1, Nat.mod_eq_of_lt h1⟩
  rcases Nat.lt_or_ge x (2 * N) with h2 | h2
  · right; left
    refine ⟨h1, h2, Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  · right; right
    refine ⟨h2, Nat.div_eq_of_lt_le (by omega) (by omega), ?_⟩
    rw [Nat.mod_eq_sub_mod (by omega : x ≥ N), Nat.mod_eq_sub_mod (by omega : x - N ≥ N),
      Nat.mod_eq_of_lt (by omega)]
    omega

theorem ind_eq {N : ℕ} (hN : 0 < N) {t u : ℕ} (ht : t ≤ N) (hu : u < N) (E : ℕ) :
    (if (E + N - u) % N < t then 1 else 0) = C N u (E + 1 + N - t + t) - C N u (E + 1 + N - t) := by
  have h := Nat.mod_add_div E N
  have hρ := Nat.mod_lt E hN
  have e1 : (E + N - u) % N = (E % N + N - u) % N := by
    rw [show E + N - u = (E % N + N - u) + N * (E / N) by omega, Nat.add_mul_mod_self_left]
  rw [diffcong hN hu (E + 1 + N - t) (E % N + 1 + N - t) t (by
    rw [show E + 1 + N - t = (E % N + 1 + N - t) + N * (E / N) by omega,
      Nat.add_mul_mod_self_left]), e1]
  unfold C
  generalize E % N = ρ at *
  rcases dm hN (ρ + N - u) (by omega) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩ <;>
  rcases dm hN (ρ + 1 + N - t + t + N - 1 - u) (by omega) with
    ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  rcases dm hN (ρ + 1 + N - t + N - 1 - u) (by omega) with
    ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩ <;>
  split_ifs <;> omega

theorem partB {N : ℕ} (hN : 0 < N) {u : ℕ} (hu : u < N) (P M : ℕ) :
    C N u (P + M) - C N u P = M / N + (if (u + N - P % N) % N < M % N then 1 else 0) := by
  have hP := Nat.mod_add_div P N
  have hM := Nat.mod_add_div M N
  have e1 : C N u (P + M) = C N u (P % N + M % N) + (P / N + M / N) := by
    rw [← C_shift hN hu]; congr 1; rw [mul_add]; omega
  have e2 : C N u P = C N u (P % N) + P / N := by
    rw [← C_shift hN hu]; congr 1; omega
  rw [e1, e2]
  have h1 := Nat.mod_lt P hN
  have h2 := Nat.mod_lt M hN
  unfold C
  generalize P % N = ρ at *
  generalize M % N = μ at *
  generalize P / N = a at *
  generalize M / N = b at *
  rcases dm hN (u + N - ρ) (by omega) with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3, a4⟩ | ⟨a1, a2, a3⟩ <;>
  rcases dm hN (ρ + μ + N - 1 - u) (by omega) with
    ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  rcases dm hN (ρ + N - 1 - u) (by omega) with
    ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩ <;>
  split_ifs <;> omega

theorem ceil_ge {N : ℕ} (hN : 0 < N) (c M : ℕ) :
    M / N + (if c < M % N then 1 else 0) ≤ (M + N - 1) / N := by
  have hM := Nat.mod_add_div M N
  have h2 := Nat.mod_lt M hN
  rw [show M + N - 1 = (M % N + N - 1) + N * (M / N) by omega, Nat.add_mul_div_left _ _ hN]
  rcases dm hN (M % N + N - 1) (by omega) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  split_ifs <;> omega

def xv (N t a : ℕ) : ℕ := (N - sig N t a % N) % N

def rowF {N : ℕ} (hN : 0 < N) (t : ℕ) : Fin N → Fin N :=
  fun k => ⟨xv N t k.val, Nat.mod_lt _ hN⟩

theorem rowF_inj {N : ℕ} (hN : 0 < N) (t : ℕ) : Function.Injective (rowF hN t) := by
  intro k k' h
  have h1 : xv N t k.val = xv N t k'.val := Fin.mk.inj_iff.mp h
  apply Fin.ext
  apply sig_inj hN t k.val k'.val k.isLt k'.isLt
  unfold xv at h1
  have a1 := Nat.mod_lt (sig N t k.val) hN
  have a2 := Nat.mod_lt (sig N t k'.val) hN
  generalize sig N t k.val % N = A at *
  generalize sig N t k'.val % N = A' at *
  rcases dm hN (N - A) (by omega) with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3, b4⟩ | ⟨b1, b2, b3⟩ <;>
  rcases dm hN (N - A') (by omega) with ⟨c1, c2, c3⟩ | ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3⟩ <;>
  omega

noncomputable def order {N : ℕ} (hN : 0 < N) (t : ℕ) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (rowF hN t)
    ((Fintype.bijective_iff_injective_and_card (rowF hN t)).mpr ⟨rowF_inj hN t, rfl⟩)

def lv (N t r : ℕ) : ℕ := r % (N / Nat.gcd t N) * t

def c0 (N t r s : ℕ) : ℕ :=
  (3 * N + t - 1 - r / (N / Nat.gcd t N) - s / (N / Nat.gcd (lv N t r) N)) % N

def yv (N t r s b : ℕ) : ℕ := (sig N (lv N t r) b + c0 N t r s) % N

def cols {N : ℕ} (hN : 0 < N) (t r s : ℕ) : Finset (Fin N) :=
  (range s).image (fun b => (⟨yv N t r s b, Nat.mod_lt _ hN⟩ : Fin N))

theorem yv_inj {N : ℕ} (hN : 0 < N) (t r s : ℕ) (hs : s ≤ N) :
    Set.InjOn (fun b => (⟨yv N t r s b, Nat.mod_lt _ hN⟩ : Fin N)) (range s) := by
  intro b hb b' hb' h
  simp only [coe_range, Set.mem_Iio] at hb hb'
  have h1 : yv N t r s b = yv N t r s b' := Fin.mk.inj_iff.mp h
  unfold yv at h1
  have h2 : sig N (lv N t r) b % N = sig N (lv N t r) b' % N :=
    Nat.ModEq.add_right_cancel' (c0 N t r s) h1
  exact sig_inj hN _ b b' (by omega) (by omega) h2

theorem rowsum {N : ℕ} (hN : 0 < N) (t r : ℕ) (hr : r ≤ N) (h : ℕ → ℕ) :
    ∑ x ∈ (univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r), h x.val =
      ∑ a ∈ range r, h (xv N t a) := by
  rw [sum_filter, ← Equiv.sum_comp (order hN t)]
  simp only [Equiv.symm_apply_apply]
  have ho : ∀ k : Fin N, (order hN t k).val = xv N t k.val := fun k => rfl
  simp only [ho]
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < r then h (xv N t a) else 0) N, ← sum_filter]
  congr 1
  ext a
  simp only [mem_filter, mem_range]
  omega

theorem xv_cast {N : ℕ} (hN : 0 < N) (t a : ℕ) :
    ((xv N t a : ℕ) : ZMod N) = -((sig N t a : ℕ) : ZMod N) := by
  unfold xv
  rw [ZMod.natCast_mod, Nat.cast_sub (Nat.mod_lt _ hN).le, ZMod.natCast_mod, ZMod.natCast_self,
    zero_sub]

theorem termeq {N t u : ℕ} (hN : 0 < N) (ht : t ≤ N) (hu : u < N) (a y phase : ℕ) :
    (if (y + phase + N - xv N t a + N - u) % N < t then 1 else 0) =
      G (C N u) N t (y + phase + 1 + N - t) a := by
  rw [ind_eq hN ht hu]
  unfold G
  apply diffcong hN hu
  have hx : xv N t a < N := Nat.mod_lt _ hN
  rw [← ZMod.natCast_eq_natCast_iff']
  have h1 : xv N t a ≤ y + phase + N := by omega
  have h2 : t ≤ y + phase + N - xv N t a + 1 + N := by omega
  have h3 : t ≤ y + phase + 1 + N := by omega
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, xv_cast hN, ZMod.natCast_self]
  ring

theorem modA {N : ℕ} (t q σ c phase : ℕ) (ht : t ≤ N) :
    (q + ((σ + c) % N + phase + 1 + N - t)) % N = (σ + (c + q + phase + 1 + N - t)) % N := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have k1 : (((σ + c) % N + phase + 1 + N - t : ℕ) : ZMod N) =
      (σ : ZMod N) + c + phase + 1 + N - t := by
    rw [Nat.cast_sub (by omega)]; push_cast [ZMod.natCast_mod]; ring
  have k2 : ((c + q + phase + 1 + N - t : ℕ) : ZMod N) = (c : ZMod N) + q + phase + 1 + N - t := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  simp only [Nat.cast_add, k1, k2]
  ring

theorem modB {N : ℕ} (hN : 0 < N) (t q q2 phase : ℕ) (ht : t ≤ N) (hq : q ≤ N) (hq2 : q2 ≤ N) :
    (q2 + ((3 * N + t - 1 - q - q2) % N + q + phase + 1 + N - t)) % N = phase % N := by
  rw [← ZMod.natCast_eq_natCast_iff']
  have k0 : (((3 * N + t - 1 - q - q2) : ℕ) : ZMod N) = 3 * (N : ZMod N) + t - 1 - q - q2 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have k1 : (((3 * N + t - 1 - q - q2) % N + q + phase + 1 + N - t : ℕ) : ZMod N) =
      (((3 * N + t - 1 - q - q2) : ℕ) : ZMod N) + q + phase + 1 + N - t := by
    rw [Nat.cast_sub (by omega)]; push_cast [ZMod.natCast_mod]; ring
  simp only [Nat.cast_add, k1, k0, ZMod.natCast_self]
  ring

theorem hitsC {N t : ℕ} (hN : 0 < N) (ht : t ≤ N) (r s : ℕ) (hr : r ≤ N) (hs : s ≤ N)
    (phase : ℕ) (u : Fin N) :
    ((((univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r)) ×ˢ
      cols hN t r s).filter
      (fun z => (z.2.val + phase + N - z.1.val + N - u.val) % N < t)).card =
      C N u.val (phase + r * s * t) - C N u.val phase := by
  have hu := u.isLt
  have step1 : ((((univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r)) ×ˢ
      cols hN t r s).filter
      (fun z => (z.2.val + phase + N - z.1.val + N - u.val) % N < t)).card =
      ∑ b ∈ range s, ∑ a ∈ range r,
        (if (yv N t r s b + phase + N - xv N t a + N - u.val) % N < t then 1 else 0) := by
    rw [card_filter, sum_product, sum_comm, cols, sum_image (yv_inj hN t r s hs)]
    apply sum_congr rfl; intro b _
    exact rowsum hN t r hr
      (fun x0 => if (yv N t r s b + phase + N - x0 + N - u.val) % N < t then 1 else 0)
  rw [step1]
  have hq : r / (N / Nat.gcd t N) ≤ N := le_trans (Nat.div_le_self _ _) hr
  have hq2 : s / (N / Nat.gcd (lv N t r) N) ≤ N := le_trans (Nat.div_le_self _ _) hs
  have step2 : ∀ b ∈ range s, ∑ a ∈ range r,
      (if (yv N t r s b + phase + N - xv N t a + N - u.val) % N < t then 1 else 0) =
      r / (N / Nat.gcd t N) * (t / Nat.gcd t N) +
        G (C N u.val) N (lv N t r) (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t) b := by
    intro b _
    rw [sum_congr rfl (fun a _ => termeq hN ht hu a (yv N t r s b) phase),
      total (C N u.val) (C_mono N u.val) hN (C_shift hN hu)]
    congr 1
    unfold G
    rw [show r / (N / Nat.gcd t N) + r % (N / Nat.gcd t N) * t + (yv N t r s b + phase + 1 + N - t)
      = (r / (N / Nat.gcd t N) + (yv N t r s b + phase + 1 + N - t)) + lv N t r by unfold lv; ring]
    apply diffcong hN hu
    unfold yv
    exact modA t _ _ _ phase ht
  rw [sum_congr rfl step2, sum_add_distrib, sum_const, card_range, smul_eq_mul,
    total (C N u.val) (C_mono N u.val) hN (C_shift hN hu)]
  have hm : (s / (N / Nat.gcd (lv N t r) N) +
      (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t)) % N = phase % N := by
    unfold c0
    exact modB hN t _ _ phase ht hq hq2
  have hLt := Lt_eq hN t
  have hLt2 := Lt_eq hN (lv N t r)
  have hr' := Nat.div_add_mod r (N / Nat.gcd t N)
  have hs' := Nat.div_add_mod s (N / Nat.gcd (lv N t r) N)
  have hl : lv N t r = r % (N / Nat.gcd t N) * t := rfl
  rw [show s / (N / Nat.gcd (lv N t r) N) + s % (N / Nat.gcd (lv N t r) N) * lv N t r +
      (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t) =
      (s / (N / Nat.gcd (lv N t r) N) + (c0 N t r s + r / (N / Nat.gcd t N) + phase + 1 + N - t))
        + s % (N / Nat.gcd (lv N t r) N) * lv N t r by ring]
  rw [diffcong hN hu _ phase _ hm]
  have mono : C N u.val phase ≤ C N u.val (phase + s % (N / Nat.gcd (lv N t r) N) * lv N t r) :=
    C_mono N u.val (Nat.le_add_right _ _)
  generalize r / (N / Nat.gcd t N) = q at *
  generalize r % (N / Nat.gcd t N) = j at *
  generalize t / Nat.gcd t N = t' at *
  generalize N / Nat.gcd t N = L at *
  generalize s / (N / Nat.gcd (lv N t r) N) = q2 at *
  generalize s % (N / Nat.gcd (lv N t r) N) = j2 at *
  generalize lv N t r / Nat.gcd (lv N t r) N = l' at *
  generalize N / Nat.gcd (lv N t r) N = L2 at *
  generalize lv N t r = l at *
  have key : r * s * t = j2 * l + N * (s * (q * t') + q2 * l') := by
    have : (r : ℤ) * s * t = j2 * l + N * (s * (q * t') + q2 * l') := by
      have a1 : ((L : ℤ) * t) = N * t' := by exact_mod_cast hLt
      have a2 : ((L : ℤ) * q + j) = r := by exact_mod_cast hr'
      have a3 : ((L2 : ℤ) * l) = N * l' := by exact_mod_cast hLt2
      have a4 : ((L2 : ℤ) * q2 + j2) = s := by exact_mod_cast hs'
      have a5 : (l : ℤ) = j * t := by exact_mod_cast hl
      linear_combination (-((s : ℤ) * t)) * a2 + ((s : ℤ) * q) * a1 - (s : ℤ) * a5 -
        (l : ℤ) * a4 + (q2 : ℤ) * a3
    exact_mod_cast this
  rw [key, show phase + (j2 * l + N * (s * (q * t') + q2 * l')) =
    phase + j2 * l + N * (s * (q * t') + q2 * l') by ring, C_shift hN hu]
  omega

theorem rows_card {N : ℕ} (hN : 0 < N) (t r : ℕ) (hr : r ≤ N) :
    ((univ : Finset (Fin N)).filter (fun x => ((order hN t).symm x).val < r)).card = r := by
  rw [card_eq_sum_ones]
  exact (rowsum hN t r hr (fun _ => 1)).trans (by simp)

theorem cols_card {N : ℕ} (hN : 0 < N) (t r s : ℕ) (hs : s ≤ N) : (cols hN t r s).card = s := by
  unfold cols
  rw [card_image_of_injOn (yv_inj hN t r s hs), card_range]


end PEqualNP.Outside.L_meta_33622_aux.Cycle


namespace PEqualNP.Outside.L_meta_33622_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def mkLinesCirc (N : ℕ) (R S : Finset (Fin N)) : Circuit :=
  let ws0 : Finset ℕ := R.image Fin.val ∪ S.image (fun y => N + y.val)
  match ws0.sort (· ≤ ·) with
  | [] => ⟨[], 0⟩
  | w0 :: ws => CircAux.orChain (N + N) w0 ws

lemma wireSet_card_eq {N : ℕ} (R S : Finset (Fin N)) :
    (R.image Fin.val ∪ S.image (fun y => N + y.val)).card = R.card + S.card := by
  have hdisj : Disjoint (R.image Fin.val) (S.image (fun y => N + y.val)) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rcases Finset.mem_image.mp hw1 with ⟨x, _, rfl⟩
    rcases Finset.mem_image.mp hw2 with ⟨y, _, hy⟩
    have := x.isLt
    omega
  rw [Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]

lemma wireSet_lt {N : ℕ} (R S : Finset (Fin N)) {w : ℕ}
    (hw : w ∈ R.image Fin.val ∪ S.image (fun y => N + y.val)) : w < N + N := by
  rcases Finset.mem_union.mp hw with h1 | h2
  · rcases Finset.mem_image.mp h1 with ⟨x, _, rfl⟩
    have := x.isLt; omega
  · rcases Finset.mem_image.mp h2 with ⟨y, _, rfl⟩
    have := y.isLt; omega

lemma mkLinesCirc_table {N : ℕ} (R S : Finset (Fin N)) (hpos : 1 ≤ R.card + S.card)
    (x y : Fin N) :
    (mkLinesCirc N R S).eval (oneEach x y) = decide (x ∈ R ∨ y ∈ S) := by
  set ws0 : Finset ℕ := R.image Fin.val ∪ S.image (fun z => N + z.val)
  have hlen : (ws0.sort (· ≤ ·)).length = R.card + S.card := by
    rw [Finset.length_sort, wireSet_card_eq]
  unfold mkLinesCirc
  dsimp only
  change (match ws0.sort (· ≤ ·) with | [] => (⟨[], 0⟩ : Circuit) | w0 :: ws => CircAux.orChain (N + N) w0 ws).eval (oneEach x y) = _
  cases hsort : ws0.sort (· ≤ ·) with
  | nil => rw [hsort] at hlen; simp at hlen; omega
  | cons w0 ws =>
    have hw0_lt : w0 < N + N := wireSet_lt R S ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp))
    have hws_lt : ∀ w ∈ ws, w < N + N := fun w hw =>
      wireSet_lt R S ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp [hw]))
    rw [CircAux.orChain_eval (N + N) w0 ws hw0_lt hws_lt (oneEach x y) (CircAux.oneEach_length x y)]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨w, hw, hwt⟩
      have hw_mem : w ∈ ws0 := (Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; exact hw)
      rcases Finset.mem_union.mp hw_mem with h1 | h2
      · rcases Finset.mem_image.mp h1 with ⟨x', hx', rfl⟩
        rw [CircAux.oneEach_getD_left x y x'.val x'.isLt] at hwt
        exact Or.inl (by rwa [← Fin.ext (of_decide_eq_true hwt)])
      · rcases Finset.mem_image.mp h2 with ⟨y', hy', rfl⟩
        rw [CircAux.oneEach_getD_right x y y'.val y'.isLt] at hwt
        exact Or.inr (by rwa [← Fin.ext (of_decide_eq_true hwt)])
    · rintro (hx | hy)
      · refine ⟨x.val, ?_, ?_⟩
        · have : x.val ∈ ws0.sort (· ≤ ·) :=
            (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
          rwa [hsort] at this
        · rw [CircAux.oneEach_getD_left x y x.val x.isLt]; simp
      · refine ⟨N + y.val, ?_, ?_⟩
        · have : N + y.val ∈ ws0.sort (· ≤ ·) :=
            (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hy, rfl⟩))
          rwa [hsort] at this
        · rw [CircAux.oneEach_getD_right x y y.val y.isLt]; simp

lemma mkLinesCirc_legal_size {N : ℕ} (R S : Finset (Fin N)) (hpos : 1 ≤ R.card + S.card) :
    CircAux.Legal N (mkLinesCirc N R S) ∧ (mkLinesCirc N R S).size = R.card + S.card - 1 := by
  set ws0 : Finset ℕ := R.image Fin.val ∪ S.image (fun z => N + z.val)
  have hlen : (ws0.sort (· ≤ ·)).length = R.card + S.card := by
    rw [Finset.length_sort, wireSet_card_eq]
  unfold mkLinesCirc
  dsimp only
  change CircAux.Legal N (match ws0.sort (· ≤ ·) with | [] => ⟨[], 0⟩ | w0 :: ws => CircAux.orChain (N + N) w0 ws) ∧
    (match ws0.sort (· ≤ ·) with | [] => (⟨[], 0⟩ : Circuit) | w0 :: ws => CircAux.orChain (N + N) w0 ws).size = _
  cases hsort : ws0.sort (· ≤ ·) with
  | nil => rw [hsort] at hlen; simp at hlen; omega
  | cons w0 ws =>
    have hw0_lt : w0 < N + N := wireSet_lt R S ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp))
    have hws_lt : ∀ w ∈ ws, w < N + N := fun w hw =>
      wireSet_lt R S ((Finset.mem_sort (· ≤ ·)).mp (by rw [hsort]; simp [hw]))
    have hws_len : ws.length = R.card + S.card - 1 := by
      rw [hsort] at hlen; simp at hlen; omega
    exact ⟨CircAux.orChain_legal N w0 ws hw0_lt hws_lt, by rw [CircAux.orChain_size, hws_len]⟩

lemma lineUnion_area {N : ℕ} (R S : Finset (Fin N)) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.1 ∈ R ∨ z.2 ∈ S) = true)).card =
      (R.card + S.card) * N - R.card * S.card := by
  have hfilt : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => decide (z.1 ∈ R ∨ z.2 ∈ S) = true) =
      (R ×ˢ Finset.univ) ∪ (Finset.univ ×ˢ S) := by
    ext z; simp
  have hinter : (R ×ˢ (Finset.univ : Finset (Fin N))) ∩ (Finset.univ ×ˢ S) = R ×ˢ S := by
    ext z; simp
  have hinc := Finset.card_union_add_card_inter (R ×ˢ (Finset.univ : Finset (Fin N)))
    ((Finset.univ : Finset (Fin N)) ×ˢ S)
  rw [← hfilt, hinter, Finset.card_product, Finset.card_product, Finset.card_product,
    Finset.card_univ, Fintype.card_fin] at hinc
  have hadd : (R.card + S.card) * N = R.card * N + N * S.card := by ring
  omega

lemma lineUnion_loss_eq {N t : ℕ} (ht : t ≤ N) (R S : Finset (Fin N)) (u : Fin N) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => decide (z.1 ∈ R ∨ z.2 ∈ S) ≠ CircAux.targetI N t u.val z.1 z.2)).card +
      2 * (R.card + S.card) * t =
    ((R.card + S.card) * N - R.card * S.card) + N * t +
      2 * ((R ×ˢ S).filter (fun z => CircAux.targetI N t u.val z.1 z.2 = true)).card := by
  have h1 := CircAux.loss_add_two_overlap ht (fun z => decide (z.1 ∈ R ∨ z.2 ∈ S)) u.val
  rw [lineUnion_area R S] at h1
  set SR_I := (Finset.univ : Finset (Fin N × Fin N)).filter
    (fun z => z.1 ∈ R ∧ CircAux.targetI N t u.val z.1 z.2 = true)
  set SC_I := (Finset.univ : Finset (Fin N × Fin N)).filter
    (fun z => z.2 ∈ S ∧ CircAux.targetI N t u.val z.1 z.2 = true)
  have hunion : SR_I ∪ SC_I = (Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => decide (z.1 ∈ R ∨ z.2 ∈ S) = true ∧ CircAux.targetI N t u.val z.1 z.2 = true) := by
    ext z; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      SR_I, SC_I, decide_eq_true_eq]; tauto
  have hinter : SR_I ∩ SC_I = (R ×ˢ S).filter (fun z => CircAux.targetI N t u.val z.1 z.2 = true) := by
    ext z; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, Finset.mem_product,
      true_and, SR_I, SC_I]; tauto
  have hSR_I : SR_I.card = R.card * t := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    have hfx : ∀ x : Fin N, ∑ y : Fin N,
        (if x ∈ R ∧ CircAux.targetI N t u.val x y = true then 1 else 0) =
        if x ∈ R then t else 0 := by
      intro x
      by_cases hx : x ∈ R
      · simp only [hx, true_and, ↓reduceIte]
        rw [← Finset.card_filter]; exact CircAux.card_targetI_col ht u.val x
      · simp [hx]
    rw [Finset.sum_congr rfl (fun x _ => hfx x),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
  have hSC_I : SC_I.card = S.card * t := by
    rw [Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
    have hfy : ∀ y : Fin N, ∑ x : Fin N,
        (if y ∈ S ∧ CircAux.targetI N t u.val x y = true then 1 else 0) =
        if y ∈ S then t else 0 := by
      intro y
      by_cases hy : y ∈ S
      · simp only [hy, true_and, ↓reduceIte]
        rw [← Finset.card_filter]; exact CircAux.card_targetI_row ht u.val y
      · simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => hfy y),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
  have hinc := Finset.card_union_add_card_inter SR_I SC_I
  rw [hunion, hinter, hSR_I, hSC_I, ← Nat.add_mul] at hinc
  have h2t : 2 * (R.card + S.card) * t = 2 * ((R.card + S.card) * t) := by ring
  omega

def shiftCol {N : ℕ} (hN : 0 < N) (phase : ℕ) (y : Fin N) : Fin N :=
  ⟨(y.val + phase) % N, Nat.mod_lt _ hN⟩

lemma shiftCol_inj {N : ℕ} (hN : 0 < N) (phase : ℕ) :
    Function.Injective (shiftCol hN phase) := by
  intro y₁ y₂ h
  have hv : (y₁.val + phase) % N = (y₂.val + phase) % N := congrArg Fin.val h
  have hmod : y₁.val % N = y₂.val % N := Nat.ModEq.add_right_cancel' phase hv
  rw [Nat.mod_eq_of_lt y₁.isLt, Nat.mod_eq_of_lt y₂.isLt] at hmod
  exact Fin.ext hmod

lemma shiftCol_mod_eq {N : ℕ} (hN : 0 < N) (phase : ℕ) (x y u : Fin N) :
    ((shiftCol hN phase y).val + N - x.val + N - u.val % N) % N =
      (y.val + phase + N - x.val + N - u.val) % N := by
  rw [Nat.mod_eq_of_lt u.isLt]
  simp only [shiftCol]
  rw [← ZMod.natCast_eq_natCast_iff']
  have hx := x.isLt
  have hu := u.isLt
  have h1 : x.val ≤ (y.val + phase) % N + N := by omega
  have h2 : u.val ≤ (y.val + phase) % N + N - x.val + N := by omega
  have h3 : x.val ≤ y.val + phase + N := by omega
  have h4 : u.val ≤ y.val + phase + N - x.val + N := by omega
  push_cast [Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4, ZMod.natCast_mod]
  ring

lemma shifted_hits_eq {N t : ℕ} (hN : 0 < N) (ht : t ≤ N) (r s : ℕ) (hr : r ≤ N) (hs : s ≤ N)
    (phase : ℕ) (u : Fin N) :
    ((((Finset.univ : Finset (Fin N)).filter (fun x => ((Cycle.order hN t).symm x).val < r)) ×ˢ
      ((Cycle.cols hN t r s).image (shiftCol hN phase))).filter
      (fun z => CircAux.targetI N t u.val z.1 z.2 = true)).card =
      Cycle.C N u.val (phase + r * s * t) - Cycle.C N u.val phase := by
  rw [← Cycle.hitsC hN ht r s hr hs phase u]
  symm
  refine Finset.card_bij (fun z _ => (z.1, shiftCol hN phase z.2)) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, CircAux.targetI,
      decide_eq_true_eq] at hz ⊢
    refine ⟨⟨hz.1.1, ⟨z.2, hz.1.2, rfl⟩⟩, ?_⟩
    rw [shiftCol_mod_eq hN phase z.1 z.2 u]
    exact hz.2
  · intro z₁ _ z₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (shiftCol_inj hN phase h.2)
  · rintro ⟨x, y'⟩ hw
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image, CircAux.targetI,
      decide_eq_true_eq] at hw
    rcases hw with ⟨⟨hx, ⟨y, hy, rfl⟩⟩, hlt⟩
    refine ⟨(x, y), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨hx, hy⟩, ?_⟩
    rwa [← shiftCol_mod_eq hN phase x y u]

lemma classify_lines_of_area {N g : ℕ} (hg : 0 < g) (hN : 2 * g + 1 < N)
    (C : Circuit) (hleg : CircAux.Legal N C) (hsize : C.size ≤ g)
    (hlo : (g - 1) * N + 1 < ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card)
    (hhi : ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun z => C.eval (oneEach z.1 z.2) = true)).card < N * (N - g)) :
    ∃ R S : Finset (Fin N), (R.card + S.card = g ∨ R.card + S.card = g + 1) ∧
      ∀ x y : Fin N, C.eval (oneEach x y) = decide (x ∈ R ∨ y ∈ S) := by
  let w0 : Fin 0 → Bool := Fin.elim0
  have htab0 : ∀ x y : Fin N, Classify.tableC N 0 C w0 x y = C.eval (oneEach x y) := by
    intro x y
    simp [Classify.tableC, Classify.inpVec, List.ofFn_zero]
  have harea0 : Classify.areaC (Classify.tableC N 0 C w0) =
      ((Finset.univ : Finset (Fin N × Fin N)).filter
        (fun z => C.eval (oneEach z.1 z.2) = true)).card := by
    unfold Classify.areaC
    congr 1; ext z; simp [htab0]
  have hleg0 : Classify.legalC N 0 C := by
    simpa [Classify.legalC, CircAux.Legal] using hleg
  have hcls := Classify.part1_classification N g hg (by omega) 0 C hleg0 hsize w0
    (by rwa [harea0]) (by rwa [harea0])
  rcases hcls with ⟨R, S, hge, hle, hlu⟩ | ⟨_, _, j, _⟩
  · refine ⟨R, S, by omega, fun x y => ?_⟩
    rw [← htab0 x y]
    exact hlu w0 x y
  · exact Fin.elim0 j

lemma exists_odd_of_odd_sum {α : Type*} (s : Finset α) (f : α → ℕ) (h : Odd (∑ i ∈ s, f i)) :
    ∃ i ∈ s, Odd (f i) := by
  by_contra hall
  push_neg at hall
  have heven : ∀ i ∈ s, 2 ∣ f i := by
    intro i hi
    rcases hall i hi with ⟨k, hk⟩
    exact ⟨k, by omega⟩
  have hdvd : 2 ∣ ∑ i ∈ s, f i := Finset.dvd_sum heven
  rw [Nat.odd_iff] at h
  have hmod0 : (∑ i ∈ s, f i) % 2 = 0 := Nat.mod_eq_zero_of_dvd hdvd
  omega

set_option maxHeartbeats 1200000 in
lemma main_proof : ∀ (N g t d M p : ℕ), 0 < g → 2*g+1 < N → N < 2*t → t ≤ N → 0 < M →
  d ≤ p → p ≤ N →
  (p = N ∨ ∃ r : ℕ, r ≤ g+1 ∧ p = r*(g+1-r)) →
  (∀ r : ℕ, r ≤ g+1 → d ≤ r*(g+1-r) → p ≤ r*(g+1-r)) →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 = true)).card
  let loss := fun (C : Circ) (u : ℕ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card
  let b := g+1
  let A := b*N-p
  let a := 2*t-N
  let j := (M*p*t) % N
  let effective := fun (c r : ℕ) => (b-c)*N + r*(c-r)
  let improves := 0 < j ∧ ∃ c r : ℕ, (c=g ∨ c=b) ∧ r ≤ c ∧ p < effective c r ∧
    Odd (effective c r-p) ∧ a*(effective c r-p)+2*j ≤ N
  let rounded := M*(N*t-b*a-p)+2*((M*p*t+N-1)/N)
  let best := rounded - @ite ℕ improves (Classical.propDecidable _) 1 0
  let fits := fun (C : Circ) => legal C ∧ C.size ≤ g ∧ area C ≤ b*N-d
  let total := fun (D : Fin M → Circ) (u : X) => ∑ i, loss (D i) u.val
  let lines := fun (C : Circ) => ∃ R S : Finset X,
    (R.card+S.card = g ∨ R.card+S.card = b) ∧
    ∀ x y : X, table C x y = decide (x ∈ R ∨ y ∈ S)
  (∃ D : Fin M → Circ, (∀ i, fits (D i) ∧ lines (D i)) ∧
    (∀ i : Fin M, i.val+1 < M → area (D i) = A) ∧
    (¬improves → ∀ i, area (D i) = A) ∧ ∀ u : X, total D u ≤ best) ∧
  ∀ D : Fin M → Circ, (∀ i, fits (D i)) →
    (∃ u : X, best ≤ total D u) ∧
    (improves → (∀ u : X, total D u ≤ best) →
      let deficit := M*A - ∑ i, area (D i)
      Odd deficit ∧ a*deficit + 2*j ≤ N ∧ ∀ i, lines (D i)) := by
  intro N g t d M p hg hN hNt ht hM hdp hpN hp_form hp_min
  intro X Circ legal table area loss b A a j effective improves rounded best fits total lines
  have hN_pos : 0 < N := by omega
  have hb_ge2 : 2 ≤ b := by omega
  have h2b_le_N : 2 * b ≤ N := by omega
  have hb_lt_N : b < N := by omega
  have ha_pos : 0 < a := by omega
  have ha_le_N : a ≤ N := by omega
  have ht_pos : 0 < t := by omega
  have hp_le_bN : p ≤ b * N := by
    have : 1 * N ≤ b * N := Nat.mul_le_mul_right N (by omega)
    omega
  have hba_p_N_le_Nt : b * a + p + N ≤ N * t := by
    have h1 : 2 * b * t ≤ N * t := Nat.mul_le_mul_right t h2b_le_N
    have h2 : 2 * b * t = b * a + b * N := by
      have haN : a + N = 2 * t := by omega
      calc 2 * b * t = b * (2 * t) := by ring
        _ = b * (a + N) := by rw [haN]
        _ = b * a + b * N := by ring
    have h3 : 2 * N ≤ b * N := Nat.mul_le_mul_right N hb_ge2
    omega
  have hba_le_Nt : b * a ≤ N * t := by omega
  have hba_p_le_Nt : b * a + p ≤ N * t := by omega
  have hN_le_term : N ≤ N * t - b * a - p := by omega
  have hrounded_pos : 1 ≤ rounded := by
    have h1 : 1 * N ≤ M * (N * t - b * a - p) := Nat.mul_le_mul hM hN_le_term
    change 1 ≤ M * (N * t - b * a - p) + 2 * ((M * p * t + N - 1) / N)
    omega
  set q := (M * p * t) / N with hq_def
  have hqj : N * q + j = M * p * t := Nat.div_add_mod (M * p * t) N
  have hj_lt : j < N := Nat.mod_lt (M * p * t) hN_pos
  have hceil_j0 : j = 0 → (M * p * t + N - 1) / N = q := by
    intro hj0
    rw [show M * p * t + N - 1 = (N - 1) + N * q by omega,
      Nat.add_mul_div_left _ _ hN_pos, Nat.div_eq_of_lt (by omega), zero_add]
  have hceil_jpos : 0 < j → (M * p * t + N - 1) / N = q + 1 := by
    intro hjpos
    have hNq : N * (q + 1) = N * q + N := by ring
    rw [show M * p * t + N - 1 = (j - 1) + N * (q + 1) by omega,
      Nat.add_mul_div_left _ _ hN_pos, Nat.div_eq_of_lt (by omega), zero_add]
  have h_alg : N * (N * t - b * a - p) + 2 * p * t + a * A = N * (N * t) := by
    have h1 : N * (N * t - b * a - p) + N * p + N * (b * a) = N * (N * t) := by
      rw [← mul_add, Nat.sub_add_cancel (by omega), ← mul_add, Nat.sub_add_cancel hba_le_Nt]
    have h2 : a * A + a * p = a * (b * N) := by
      rw [← mul_add, Nat.sub_add_cancel hp_le_bN]
    have h3 : a * p + N * p = 2 * p * t := by
      have haN : a + N = 2 * t := by omega
      calc a * p + N * p = (a + N) * p := by ring
        _ = (2 * t) * p := by rw [haN]
        _ = 2 * p * t := by ring
    have h4 : N * (b * a) = a * (b * N) := by ring
    omega
  have hfits_le_A : ∀ C : Circ, fits C → area C ≤ A := by
    intro C hC
    exact CircAux.area_le_A_gen hg hN hdp hpN hp_min C hC.1 hC.2.1 hC.2.2
  constructor
  · have hbase_shape : ∃ c₀ r₀ : ℕ, (c₀ = g ∨ c₀ = b) ∧ r₀ ≤ c₀ ∧ effective c₀ r₀ = p := by
      rcases hp_form with rfl | ⟨r, hr, hpr⟩
      · refine ⟨g, 0, Or.inl rfl, Nat.zero_le _, ?_⟩
        simp [effective, b]
      · refine ⟨b, r, Or.inr rfl, hr, ?_⟩
        simp [effective, b, hpr]
    rcases hbase_shape with ⟨c₀, r₀, hc₀, hr₀, heff₀⟩
    have hbuild : ∀ (cf rf : ℕ → ℕ),
        (∀ k, (cf k = g ∨ cf k = b) ∧ rf k ≤ cf k) →
        (∀ k, k < M → d ≤ effective (cf k) (rf k)) →
        let E_tot := ∑ k ∈ Finset.range M, effective (cf k) (rf k)
        ∃ D : Fin M → Circ,
          (∀ i, fits (D i) ∧ lines (D i)) ∧
          (∀ i : Fin M, area (D i) = b * N - effective (cf i.val) (rf i.val)) ∧
          (∀ u : X, total D u + E_tot ≤ M * (N * t - b * a) + 2 * ((E_tot * t + N - 1) / N)) := by
      intro cf rf hcf hcf_d E_tot
      let sf : ℕ → ℕ := fun k => cf k - rf k
      let eff : ℕ → ℕ := fun k => effective (cf k) (rf k)
      let P : ℕ → ℕ := fun k => ∑ m ∈ Finset.range k, eff m * t
      let Rset : ℕ → Finset X := fun k =>
        (Finset.univ : Finset X).filter (fun x => ((Cycle.order hN_pos t).symm x).val < rf k)
      let Sset : ℕ → Finset X := fun k =>
        (Cycle.cols hN_pos t (rf k) (sf k)).image (shiftCol hN_pos (P k))
      let D : Fin M → Circ := fun i => mkLinesCirc N (Rset i.val) (Sset i.val)
      have hRcard : ∀ k, (Rset k).card = rf k := by
        intro k
        have hle : rf k ≤ N := by have := hcf k; omega
        exact Cycle.rows_card hN_pos t (rf k) hle
      have hScard : ∀ k, (Sset k).card = sf k := by
        intro k
        have hle : sf k ≤ N := by dsimp only [sf]; have := hcf k; omega
        rw [Finset.card_image_of_injective _ (shiftCol_inj hN_pos (P k))]
        exact Cycle.cols_card hN_pos t (rf k) (sf k) hle
      have hRScard : ∀ k, (Rset k).card + (Sset k).card = cf k := by
        intro k; rw [hRcard k, hScard k]; dsimp only [sf]; have := (hcf k).2; omega
      have hpos_card : ∀ k, 1 ≤ (Rset k).card + (Sset k).card := by
        intro k; rw [hRScard k]; have := (hcf k).1; omega
      have hD_tab : ∀ (i : Fin M) (x y : X),
          table (D i) x y = decide (x ∈ Rset i.val ∨ y ∈ Sset i.val) := by
        intro i x y
        exact mkLinesCirc_table (Rset i.val) (Sset i.val) (hpos_card i.val) x y
      have hD_area : ∀ i : Fin M, area (D i) = b * N - eff i.val := by
        intro i
        have heq : area (D i) = ((Finset.univ : Finset (X × X)).filter
            (fun z => decide (z.1 ∈ Rset i.val ∨ z.2 ∈ Sset i.val) = true)).card := by
          dsimp only [area]; congr 1; ext z; simp [hD_tab i]
        rw [heq, lineUnion_area, hRScard, hRcard, hScard]
        have hci := hcf i.val
        have hmul : rf i.val * sf i.val ≤ cf i.val * N := Nat.mul_le_mul hci.2 (by dsimp only [sf]; omega)
        have hbc : (b - cf i.val) * N + cf i.val * N = b * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        dsimp only [eff, effective, sf]
        dsimp only [sf] at hmul
        omega
      have hD_fl : ∀ i : Fin M, fits (D i) ∧ lines (D i) := by
        intro i
        have hls := mkLinesCirc_legal_size (Rset i.val) (Sset i.val) (hpos_card i.val)
        have hci := hcf i.val
        refine ⟨⟨hls.1, ?_, ?_⟩, ⟨Rset i.val, Sset i.val, by rw [hRScard]; exact hci.1, hD_tab i⟩⟩
        · rw [hls.2, hRScard]; omega
        · rw [hD_area i]
          have hd_le := hcf_d i.val i.isLt
          dsimp only [eff]
          omega
      refine ⟨D, hD_fl, hD_area, ?_⟩
      intro u
      have hstep : ∀ (i : Fin M),
          loss (D i) u.val + 2 * b * t =
            (b * N - eff i.val) + N * t +
            2 * (Cycle.C N u.val (P (i.val + 1)) - Cycle.C N u.val (P i.val)) := by
        intro i
        have hloss_eq : loss (D i) u.val =
            ((Finset.univ : Finset (X × X)).filter
              (fun z => decide (z.1 ∈ Rset i.val ∨ z.2 ∈ Sset i.val) ≠
                CircAux.targetI N t u.val z.1 z.2)).card := by
          dsimp only [loss]; congr 1; ext z; simp [hD_tab i, CircAux.targetI]
        have hl := lineUnion_loss_eq ht (Rset i.val) (Sset i.val) u
        rw [← hloss_eq, hRScard, hRcard, hScard] at hl
        have hci := hcf i.val
        have hrfN : rf i.val ≤ N := by omega
        have hsfN : sf i.val ≤ N := by dsimp only [sf]; omega
        have hhits := shifted_hits_eq hN_pos ht (rf i.val) (sf i.val) hrfN hsfN (P i.val) u
        rw [hhits] at hl
        have hP_succ : P (i.val + 1) =
            (P i.val + rf i.val * sf i.val * t) + N * ((b - cf i.val) * t) := by
          simp only [P, Finset.sum_range_succ, eff, effective, sf]
          ring
        have hC_succ : Cycle.C N u.val (P (i.val + 1)) =
            Cycle.C N u.val (P i.val + rf i.val * sf i.val * t) + (b - cf i.val) * t := by
          rw [hP_succ, Cycle.C_shift hN_pos u.isLt]
        have hC_mono_step : Cycle.C N u.val (P i.val) ≤
            Cycle.C N u.val (P i.val + rf i.val * sf i.val * t) :=
          Cycle.C_mono N u.val (Nat.le_add_right _ _)
        have h2bt : 2 * cf i.val * t + 2 * ((b - cf i.val) * t) = 2 * b * t := by
          have : cf i.val + (b - cf i.val) = b := by omega
          calc 2 * cf i.val * t + 2 * ((b - cf i.val) * t)
              = 2 * (cf i.val + (b - cf i.val)) * t := by ring
            _ = 2 * b * t := by rw [this]
        have hmul : rf i.val * sf i.val ≤ cf i.val * N :=
          Nat.mul_le_mul hci.2 (by dsimp only [sf]; omega)
        have hbc : (b - cf i.val) * N + cf i.val * N = b * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        have harea_eq : cf i.val * N - rf i.val * sf i.val = b * N - eff i.val := by
          dsimp only [eff, effective, sf]
          dsimp only [sf] at hmul
          omega
        rw [harea_eq] at hl
        omega
      have hsum_all :
          (∑ i : Fin M, (loss (D i) u.val + 2 * b * t)) =
          (∑ i : Fin M, ((b * N - eff i.val) + N * t +
            2 * (Cycle.C N u.val (P (i.val + 1)) - Cycle.C N u.val (P i.val)))) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, ← Finset.mul_sum] at hsum_all
      have htele : (∑ i : Fin M, (Cycle.C N u.val (P (i.val + 1)) - Cycle.C N u.val (P i.val))) =
          Cycle.C N u.val (P M) - Cycle.C N u.val (P 0) := by
        rw [Fin.sum_univ_eq_sum_range (fun k => Cycle.C N u.val (P (k + 1)) - Cycle.C N u.val (P k)) M]
        have hPmono : Monotone (fun k => Cycle.C N u.val (P k)) := by
          intro x y hxy
          exact Cycle.C_mono N u.val (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hxy))
        exact Finset.sum_range_tsub hPmono M
      have hP0 : P 0 = 0 := by simp [P]
      have hPM : P M = E_tot * t := by
        simp only [P, E_tot, eff, Finset.sum_mul]
      have hC_bound : Cycle.C N u.val (P M) - Cycle.C N u.val (P 0) ≤ (E_tot * t + N - 1) / N := by
        conv_lhs => rw [hP0, hPM, ← zero_add (E_tot * t), Cycle.partB hN_pos u.isLt 0 (E_tot * t)]
        exact Cycle.ceil_ge hN_pos _ _
      have hsum_eff : (∑ i : Fin M, (b * N - eff i.val)) + E_tot = M * (b * N) := by
        rw [Fin.sum_univ_eq_sum_range (fun k => b * N - eff k) M]
        change (∑ k ∈ Finset.range M, (b * N - eff k)) + (∑ k ∈ Finset.range M, eff k) = M * (b * N)
        rw [← Finset.sum_add_distrib]
        have hle_bN : ∀ k ∈ Finset.range M, (b * N - eff k) + eff k = b * N := by
          intro k _
          have hck := hcf k
          have hmul : rf k * sf k ≤ cf k * N := Nat.mul_le_mul hck.2 (by dsimp only [sf]; omega)
          have hbc : (b - cf k) * N + cf k * N = b * N := by
            rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
          have heff_le : eff k ≤ b * N := by
            dsimp only [eff, effective]
            dsimp only [sf] at hmul
            omega
          exact Nat.sub_add_cancel heff_le
        rw [Finset.sum_congr rfl hle_bN, Finset.sum_const, Finset.card_range, smul_eq_mul]
      have h2bt_id : b * N + N * t = 2 * b * t + (N * t - b * a) := by
        have haN : a + N = 2 * t := by omega
        have h2bt : 2 * b * t = b * a + b * N := by
          calc 2 * b * t = b * (2 * t) := by ring
            _ = b * (a + N) := by rw [haN]
            _ = b * a + b * N := by ring
        omega
      have hM_id : M * (b * N) + M * (N * t) = M * (2 * b * t) + M * (N * t - b * a) := by
        rw [← mul_add, ← mul_add, h2bt_id]
      rw [htele] at hsum_all
      change total D u + M * (2 * b * t) =
        (∑ i : Fin M, (b * N - eff i.val)) + M * (N * t) +
          2 * (Cycle.C N u.val (P M) - Cycle.C N u.val (P 0)) at hsum_all
      omega
    by_cases himp : improves
    · rcases himp with ⟨hj_pos, c₁, r₁, hc₁, hr₁, hp_lt, hodd_d, hineq_d⟩
      have himp_true : improves := ⟨hj_pos, c₁, r₁, hc₁, hr₁, hp_lt, hodd_d, hineq_d⟩
      let cf : ℕ → ℕ := fun k => if k + 1 < M then c₀ else c₁
      let rf : ℕ → ℕ := fun k => if k + 1 < M then r₀ else r₁
      have hcf : ∀ k, (cf k = g ∨ cf k = b) ∧ rf k ≤ cf k := by
        intro k
        simp only [cf, rf]
        split_ifs
        · exact ⟨hc₀, hr₀⟩
        · exact ⟨hc₁, hr₁⟩
      have hcf_d : ∀ k, k < M → d ≤ effective (cf k) (rf k) := by
        intro k _; simp only [cf, rf]; split_ifs
        · rw [heff₀]; exact hdp
        · omega
      obtain ⟨D, hD_fl, hD_area, hD_tot⟩ := hbuild cf rf hcf hcf_d
      refine ⟨D, hD_fl, ?_, fun hni => absurd himp_true hni, ?_⟩
      · intro i hi
        rw [hD_area i]
        simp only [cf, rf, hi, ↓reduceIte, heff₀]
        rfl
      · intro u
        have htot_u := hD_tot u
        set δ := effective c₁ r₁ - p with hδ_def
        rcases hodd_d with ⟨k, hk⟩
        have hEtot : (∑ m ∈ Finset.range M, effective (cf m) (rf m)) = M * p + δ := by
          have hM1 : M = (M - 1) + 1 := by omega
          conv_lhs => rw [hM1]
          rw [Finset.sum_range_succ]
          have hprev : ∀ m ∈ Finset.range (M - 1), effective (cf m) (rf m) = p := by
            intro m hm
            rw [Finset.mem_range] at hm
            have hm' : m + 1 < M := by omega
            simp only [cf, rf, hm', ↓reduceIte, heff₀]
          have hlast : ¬((M - 1) + 1 < M) := by omega
          rw [Finset.sum_congr rfl hprev, Finset.sum_const, Finset.card_range, smul_eq_mul]
          simp only [cf, rf, hlast, ↓reduceIte]
          have hMp : (M - 1) * p + p = M * p := by
            conv_rhs => rw [hM1]
            ring
          omega
        rw [hEtot] at htot_u
        have hj_dt : j + δ * t ≤ (k + 1) * N := by
          have h2 : 2 * (j + δ * t) ≤ 2 * ((k + 1) * N) := by
            have haN : a + N = 2 * t := by omega
            have hl : 2 * (j + δ * t) = δ * N + (a * δ + 2 * j) := by
              calc 2 * (j + δ * t) = δ * (2 * t) + 2 * j := by ring
                _ = δ * (a + N) + 2 * j := by rw [← haN]
                _ = δ * N + (a * δ + 2 * j) := by ring
            have hr : 2 * ((k + 1) * N) = δ * N + N := by
              rw [hk]; ring
            omega
          omega
        have hceil_le : ((M * p + δ) * t + N - 1) / N ≤ q + k + 1 := by
          have hle_num : (M * p + δ) * t + N - 1 ≤ (N - 1) + N * (q + k + 1) := by
            have hmul : (M * p + δ) * t = M * p * t + δ * t := by ring
            have hrhs : N * (q + k + 1) = N * q + (k + 1) * N := by ring
            omega
          calc ((M * p + δ) * t + N - 1) / N
              ≤ ((N - 1) + N * (q + k + 1)) / N := Nat.div_le_div_right hle_num
            _ = (N - 1) / N + (q + k + 1) := Nat.add_mul_div_left _ _ hN_pos
            _ = q + k + 1 := by rw [Nat.div_eq_of_lt (by omega), zero_add]
        have hrounded_eq : rounded = M * (N * t - b * a - p) + 2 * q + 2 := by
          change M * (N * t - b * a - p) + 2 * ((M * p * t + N - 1) / N) = _
          rw [hceil_jpos hj_pos]; ring
        have hbest_eq : best = M * (N * t - b * a - p) + 2 * q + 1 := by
          change rounded - @ite ℕ improves (Classical.propDecidable _) 1 0 = _
          rw [if_pos himp_true, hrounded_eq]; omega
        have hM_sub : M * (N * t - b * a) = M * (N * t - b * a - p) + M * p := by
          rw [← mul_add, Nat.sub_add_cancel (by omega)]
        rw [hbest_eq]
        omega
    · let cf : ℕ → ℕ := fun _ => c₀
      let rf : ℕ → ℕ := fun _ => r₀
      have hcf : ∀ k, (cf k = g ∨ cf k = b) ∧ rf k ≤ cf k := fun _ => ⟨hc₀, hr₀⟩
      have hcf_d : ∀ k, k < M → d ≤ effective (cf k) (rf k) := by
        intro _ _; simp only [cf, rf, heff₀]; exact hdp
      obtain ⟨D, hD_fl, hD_area, hD_tot⟩ := hbuild cf rf hcf hcf_d
      refine ⟨D, hD_fl, ?_, ?_, ?_⟩
      · intro i _; rw [hD_area i]; simp only [cf, rf, heff₀]; rfl
      · intro _ i; rw [hD_area i]; simp only [cf, rf, heff₀]; rfl
      · intro u
        have htot_u := hD_tot u
        have hEtot : (∑ m ∈ Finset.range M, effective (cf m) (rf m)) = M * p := by
          simp [cf, rf, heff₀, Finset.sum_const, smul_eq_mul]
        rw [hEtot] at htot_u
        have hM_sub : M * (N * t - b * a) = M * (N * t - b * a - p) + M * p := by
          rw [← mul_add, Nat.sub_add_cancel (by omega)]
        have hbest_eq : best = rounded := by
          change rounded - @ite ℕ improves (Classical.propDecidable _) 1 0 = rounded
          rw [if_neg himp]; omega
        rw [hbest_eq]
        change total D u ≤ M * (N * t - b * a - p) + 2 * ((M * p * t + N - 1) / N)
        omega
  · intro D hD
    set S_area := ∑ i : Fin M, area (D i) with hS_def
    have hS_le : S_area ≤ M * A := by
      calc S_area ≤ ∑ _i : Fin M, A := Finset.sum_le_sum (fun i _ => hfits_le_A (D i) (hD i))
        _ = M * A := by simp
    set deficit := M * A - S_area with hdef_def
    have hS_add_def : S_area + deficit = M * A := Nat.add_sub_of_le hS_le
    have hsum_tot_raw : (∑ u : X, total D u) + a * S_area = M * (N * (N * t)) := by
      have h1 : ∀ i : Fin M,
          (∑ u : X, loss (D i) u.val) + a * area (D i) = N * (N * t) := fun i =>
        CircAux.sum_loss_eq hNt ht (fun z => table (D i) z.1 z.2)
      have h2 : ∑ i : Fin M, ((∑ u : X, loss (D i) u.val) + a * area (D i)) =
          ∑ _i : Fin M, N * (N * t) := Finset.sum_congr rfl (fun i _ => h1 i)
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h2
      exact h2
    have hsum_tot : ∑ u : X, total D u =
        N * (M * (N * t - b * a - p)) + 2 * (M * p * t) + a * deficit := by
      have hM_alg : M * (N * (N * t - b * a - p) + 2 * p * t + a * A) = M * (N * (N * t)) :=
        congrArg (M * ·) h_alg
      have htmp : (∑ u : X, total D u) + a * (M * A) =
          M * (N * (N * t)) + a * deficit := by
        calc (∑ u : X, total D u) + a * (M * A)
            = (∑ u : X, total D u) + a * (S_area + deficit) := by rw [hS_add_def]
          _ = ((∑ u : X, total D u) + a * S_area) + a * deficit := by ring
          _ = M * (N * (N * t)) + a * deficit := by rw [hsum_tot_raw]
      have hlin : M * (N * (N * t - b * a - p) + 2 * p * t + a * A) =
          N * (M * (N * t - b * a - p)) + 2 * (M * p * t) + a * (M * A) := by ring
      omega
    have hsum_j0 : j = 0 → ∑ u : X, total D u = N * rounded + a * deficit := by
      intro hj0
      have hr : rounded = M * (N * t - b * a - p) + 2 * q := by
        change M * (N * t - b * a - p) + 2 * ((M * p * t + N - 1) / N) = _
        rw [hceil_j0 hj0]
      rw [hsum_tot, hr, ← hqj, hj0, add_zero]
      ring
    have hsum_jpos : 0 < j →
        2 ≤ rounded ∧ ∑ u : X, total D u = N * (rounded - 2) + (a * deficit + 2 * j) := by
      intro hjpos
      have hr : rounded = M * (N * t - b * a - p) + 2 * q + 2 := by
        change M * (N * t - b * a - p) + 2 * ((M * p * t + N - 1) / N) = _
        rw [hceil_jpos hjpos]; ring
      refine ⟨by omega, ?_⟩
      have hr2 : rounded - 2 = M * (N * t - b * a - p) + 2 * q := by omega
      rw [hsum_tot, hr2, ← hqj]
      ring
    have hpar : ∀ u : X, (total D u + deficit) % 2 = rounded % 2 := by
      intro u
      let ov : Fin M → ℕ := fun i =>
        ((Finset.univ : Finset (X × X)).filter
          (fun z => table (D i) z.1 z.2 = true ∧ CircAux.targetI N t u.val z.1 z.2 = true)).card
      have hov_sum : total D u + 2 * (∑ i : Fin M, ov i) = S_area + M * (N * t) := by
        have h1 : ∀ i : Fin M, loss (D i) u.val + 2 * ov i = area (D i) + N * t := fun i =>
          CircAux.loss_add_two_overlap ht (fun z => table (D i) z.1 z.2) u.val
        have h2 := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h1 i)
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, smul_eq_mul] at h2
        have hNM : N * (M * t) = M * (N * t) := by ring
        rw [hNM] at h2
        exact h2
      set ceil_val := (M * p * t + N - 1) / N
      have hZ : ((total D u + deficit : ℕ) : ℤ) - (rounded : ℤ) =
          2 * ((M : ℤ) * b * t - (∑ i : Fin M, ov i : ℕ) - ceil_val) := by
        have h1Z : (total D u : ℤ) + 2 * ((∑ i : Fin M, ov i : ℕ) : ℤ) =
            (S_area : ℤ) + (M : ℤ) * ((N : ℤ) * t) := by exact_mod_cast hov_sum
        have h2Z : (S_area : ℤ) + (deficit : ℤ) + (M : ℤ) * p = (M : ℤ) * ((b : ℤ) * N) := by
          have hnat : S_area + deficit + M * p = M * (b * N) := by
            have hAp : A + p = b * N := Nat.sub_add_cancel hp_le_bN
            calc S_area + deficit + M * p = M * A + M * p := by rw [hS_add_def]
              _ = M * (A + p) := by ring
              _ = M * (b * N) := by rw [hAp]
          exact_mod_cast hnat
        have h3Z : (rounded : ℤ) + (M : ℤ) * (b : ℤ) * (2 * t) + (M : ℤ) * p =
            (M : ℤ) * ((N : ℤ) * t) + (M : ℤ) * (b : ℤ) * N + 2 * (ceil_val : ℤ) := by
          have hnat : rounded + M * b * (2 * t) + M * p = M * (N * t) + M * b * N + 2 * ceil_val := by
            have hterm : (N * t - b * a - p) + b * a + p = N * t := by omega
            have haN : a + N = 2 * t := by omega
            have hba : b * a + b * N = b * (2 * t) := by rw [← mul_add, haN]
            have hr : rounded = M * (N * t - b * a - p) + 2 * ceil_val := rfl
            calc rounded + M * b * (2 * t) + M * p
                = M * (N * t - b * a - p) + 2 * ceil_val + M * (b * a + b * N) + M * p := by
                    rw [hr, mul_assoc M b (2 * t), ← hba]
              _ = M * ((N * t - b * a - p) + b * a + p) + M * b * N + 2 * ceil_val := by ring
              _ = M * (N * t) + M * b * N + 2 * ceil_val := by rw [hterm]
          exact_mod_cast hnat
        rw [Nat.cast_add]
        linear_combination h1Z + h2Z - h3Z
      omega
    have hex_j0 : j = 0 → ∃ u : X, rounded ≤ total D u := by
      intro hj0
      by_contra hlt
      push Not at hlt
      have hle : ∑ u : X, total D u ≤ N * (rounded - 1) := by
        calc ∑ u : X, total D u ≤ ∑ _u : X, (rounded - 1) :=
              Finset.sum_le_sum (fun u _ => by have := hlt u; omega)
          _ = N * (rounded - 1) := by dsimp only [X]; simp
      rw [hsum_j0 hj0] at hle
      have h1 : N * (rounded - 1) + N = N * rounded := by
        have hr1 : (rounded - 1) + 1 = rounded := by omega
        conv_rhs => rw [← hr1]
        ring
      omega
    have hex_m1 : ∃ u : X, rounded - 1 ≤ total D u := by
      by_cases hj0 : j = 0
      · rcases hex_j0 hj0 with ⟨u, hu⟩
        exact ⟨u, by omega⟩
      · have hjpos : 0 < j := by omega
        obtain ⟨hr2, hsum⟩ := hsum_jpos hjpos
        by_contra hlt
        push Not at hlt
        have hle : ∑ u : X, total D u ≤ N * (rounded - 2) := by
          calc ∑ u : X, total D u ≤ ∑ _u : X, (rounded - 2) :=
                Finset.sum_le_sum (fun u _ => by have := hlt u; omega)
            _ = N * (rounded - 2) := by dsimp only [X]; simp
        rw [hsum] at hle
        omega
    have hrigid : (∀ u : X, total D u ≤ rounded - 1) →
        improves ∧ Odd deficit ∧ a * deficit + 2 * j ≤ N ∧ ∀ i, lines (D i) := by
      intro hall
      have hj_pos : 0 < j := by
        by_contra hj0
        have hj_eq : j = 0 := by omega
        rcases hex_j0 hj_eq with ⟨u, hu⟩
        have := hall u
        omega
      obtain ⟨hr2, hsum⟩ := hsum_jpos hj_pos
      have hineq : a * deficit + 2 * j ≤ N := by
        have hle : ∑ u : X, total D u ≤ N * (rounded - 1) := by
          calc ∑ u : X, total D u ≤ ∑ _u : X, (rounded - 1) :=
                Finset.sum_le_sum (fun u _ => hall u)
            _ = N * (rounded - 1) := by dsimp only [X]; simp
        rw [hsum] at hle
        have h1 : N * (rounded - 1) = N * (rounded - 2) + N := by
          have : rounded - 1 = (rounded - 2) + 1 := by omega
          rw [this, mul_add, mul_one]
        omega
      have hodd : Odd deficit := by
        rcases hex_m1 with ⟨u₀, hu₀⟩
        have heq : total D u₀ = rounded - 1 := by have := hall u₀; omega
        have hp0 := hpar u₀
        rw [heq] at hp0
        rw [Nat.odd_iff]
        omega
      have hsum_def : ∑ i : Fin M, (A - area (D i)) = deficit := by
        have h1 : (∑ i : Fin M, (A - area (D i))) + S_area = M * A := by
          change (∑ i : Fin M, (A - area (D i))) + (∑ i : Fin M, area (D i)) = M * A
          rw [← Finset.sum_add_distrib]
          have h2 : ∀ i ∈ (Finset.univ : Finset (Fin M)), (A - area (D i)) + area (D i) = A := by
            intro i _
            exact Nat.sub_add_cancel (hfits_le_A (D i) (hD i))
          rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul]
        omega
      have hdef_le : deficit ≤ N - 2 := by
        have : 1 * deficit ≤ a * deficit := Nat.mul_le_mul_right deficit ha_pos
        omega
      have hlines : ∀ i : Fin M, lines (D i) := by
        intro i
        have hdi_le : A - area (D i) ≤ deficit := by
          rw [← hsum_def]
          exact Finset.single_le_sum (f := fun k => A - area (D k))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        have harea_le : area (D i) ≤ A := hfits_le_A (D i) (hD i)
        have hlo : (g - 1) * N + 1 < area (D i) := by
          have hg2 : (g - 1) * N + 2 * N = b * N := by
            have : (g - 1) + 2 = b := by omega
            rw [← Nat.add_mul, this]
          omega
        have hhi : area (D i) < N * (N - g) := by
          have hlt1 : b * N < (N - g) * N := Nat.mul_lt_mul_of_pos_right (by omega) hN_pos
          have hcomm : (N - g) * N = N * (N - g) := mul_comm _ _
          omega
        exact classify_lines_of_area hg hN (D i) (hD i).1 (hD i).2.1 hlo hhi
      have himp : improves := by
        have hodd_sum : Odd (∑ i : Fin M, (A - area (D i))) := by rwa [hsum_def]
        obtain ⟨i₀, _, hodd_i0⟩ := exists_odd_of_odd_sum Finset.univ (fun i => A - area (D i)) hodd_sum
        rcases hlines i₀ with ⟨R, S, hc, htab⟩
        have harea_i0 : area (D i₀) = (R.card + S.card) * N - R.card * S.card := by
          have heq : area (D i₀) = ((Finset.univ : Finset (X × X)).filter
              (fun z => decide (z.1 ∈ R ∨ z.2 ∈ S) = true)).card := by
            dsimp only [area]; congr 1; ext z; simp [htab]
          rw [heq, lineUnion_area]
        set c := R.card + S.card
        set r := R.card
        have hr_le : r ≤ c := Nat.le_add_right _ _
        have hS_eq : S.card = c - r := by omega
        have hmul_le : r * (c - r) ≤ c * N := by
          have hSN : S.card ≤ N := by
            have := Finset.card_le_univ S; dsimp only [X] at this; simpa using this
          rw [← hS_eq]
          exact Nat.mul_le_mul hr_le hSN
        have hbc : (b - c) * N + c * N = b * N := by
          rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
        have harea_eff : area (D i₀) + effective c r = b * N := by
          rw [harea_i0, hS_eq]
          dsimp only [effective]
          omega
        have harea_le : area (D i₀) ≤ A := hfits_le_A (D i₀) (hD i₀)
        have hdiff_eq : A - area (D i₀) = effective c r - p := by omega
        have hodd_eff : Odd (effective c r - p) := by rwa [← hdiff_eq]
        have hp_lt_eff : p < effective c r := by
          rw [Nat.odd_iff] at hodd_eff
          omega
        have hdi_le : effective c r - p ≤ deficit := by
          rw [← hdiff_eq, ← hsum_def]
          exact Finset.single_le_sum (f := fun k => A - area (D k))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
        have hineq_eff : a * (effective c r - p) + 2 * j ≤ N := by
          have := Nat.mul_le_mul_left a hdi_le
          omega
        exact ⟨hj_pos, c, r, hc, hr_le, hp_lt_eff, hodd_eff, hineq_eff⟩
      exact ⟨himp, hodd, hineq, hlines⟩
    by_cases himp : improves
    · have hbest_eq : best = rounded - 1 := by
        change rounded - @ite ℕ improves (Classical.propDecidable _) 1 0 = _
        rw [if_pos himp]
      rw [hbest_eq]
      refine ⟨hex_m1, fun _ hall => (hrigid hall).2⟩
    · have hbest_eq : best = rounded := by
        change rounded - @ite ℕ improves (Classical.propDecidable _) 1 0 = rounded
        rw [if_neg himp]; omega
      rw [hbest_eq]
      refine ⟨?_, fun h => absurd h himp⟩
      by_contra hlt
      push Not at hlt
      have hall : ∀ u : X, total D u ≤ rounded - 1 := fun u => by have := hlt u; omega
      exact himp (hrigid hall).1

end PEqualNP.Outside.L_meta_33622_aux


theorem PEqualNP.Outside.L_meta_33622 : (∀ (N g t d M p : ℕ), 0 < g → 2*g+1 < N → N < 2*t → t ≤ N → 0 < M →
  d ≤ p → p ≤ N →
  (p = N ∨ ∃ r : ℕ, r ≤ g+1 ∧ p = r*(g+1-r)) →
  (∀ r : ℕ, r ≤ g+1 → d ≤ r*(g+1-r) → p ≤ r*(g+1-r)) →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let area := fun (C : Circ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 = true)).card
  let loss := fun (C : Circ) (u : ℕ) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => table C z.1 z.2 ≠
      decide ((z.2.val + N - z.1.val + N - u % N) % N < t))).card
  let b := g+1
  let A := b*N-p
  let a := 2*t-N
  let j := (M*p*t) % N
  let effective := fun (c r : ℕ) => (b-c)*N + r*(c-r)
  let improves := 0 < j ∧ ∃ c r : ℕ, (c=g ∨ c=b) ∧ r ≤ c ∧ p < effective c r ∧
    Odd (effective c r-p) ∧ a*(effective c r-p)+2*j ≤ N
  let rounded := M*(N*t-b*a-p)+2*((M*p*t+N-1)/N)
  let best := rounded - @ite ℕ improves (Classical.propDecidable _) 1 0
  let fits := fun (C : Circ) => legal C ∧ C.size ≤ g ∧ area C ≤ b*N-d
  let total := fun (D : Fin M → Circ) (u : X) => ∑ i, loss (D i) u.val
  let lines := fun (C : Circ) => ∃ R S : Finset X,
    (R.card+S.card = g ∨ R.card+S.card = b) ∧
    ∀ x y : X, table C x y = decide (x ∈ R ∨ y ∈ S)
  (∃ D : Fin M → Circ, (∀ i, fits (D i) ∧ lines (D i)) ∧
    (∀ i : Fin M, i.val+1 < M → area (D i) = A) ∧
    (¬improves → ∀ i, area (D i) = A) ∧ ∀ u : X, total D u ≤ best) ∧
  ∀ D : Fin M → Circ, (∀ i, fits (D i)) →
    (∃ u : X, best ≤ total D u) ∧
    (improves → (∀ u : X, total D u ≤ best) →
      let deficit := M*A - ∑ i, area (D i)
      Odd deficit ∧ a*deficit + 2*j ≤ N ∧ ∀ i, lines (D i))) :=
  PEqualNP.Outside.L_meta_33622_aux.main_proof
