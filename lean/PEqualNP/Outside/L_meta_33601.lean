import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33601_aux

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

def buildOrChain (N : ℕ) (x₀ y₀ : Fin N) : ℕ → List Gate
  | 0 => [⟨.and, [x₀.val, N + y₀.val]⟩]
  | k + 1 => buildOrChain N x₀ y₀ k ++ [(⟨.or, [N + N + k, k]⟩ : Gate)]

lemma buildOrChain_length (N : ℕ) (x₀ y₀ : Fin N) (m : ℕ) :
    (buildOrChain N x₀ y₀ m).length = m + 1 := by
  induction m with
  | zero => rfl
  | succ k ih => simp [buildOrChain, ih]

lemma buildOrChain_readsBack (N : ℕ) (x₀ y₀ : Fin N) (m : ℕ) (hm : m ≤ N) :
    ReadsBack (N + N + 0) ⟨buildOrChain N x₀ y₀ m, 0⟩ := by
  induction m with
  | zero =>
    intro j hj i hi
    simp only [buildOrChain, List.length_singleton] at hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [gateAt, buildOrChain, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · have := x₀.isLt; omega
    · have := y₀.isLt; omega
  | succ k ih =>
    intro j hj i hi
    simp only [buildOrChain_length] at hj
    by_cases hjk : j < k + 1
    · have hget : gateAt ⟨buildOrChain N x₀ y₀ (k + 1), 0⟩ j = gateAt ⟨buildOrChain N x₀ y₀ k, 0⟩ j := by
        unfold gateAt; dsimp only [buildOrChain]
        have hlen : j < (buildOrChain N x₀ y₀ k).length := by rw [buildOrChain_length]; exact hjk
        have hlen' : j < (buildOrChain N x₀ y₀ k ++ [(⟨.or, [N + N + k, k]⟩ : Gate)]).length := by simp; omega
        rw [List.getD_eq_getElem _ _ hlen', List.getElem_append_left hlen, List.getD_eq_getElem _ _ hlen]
      rw [hget] at hi
      exact ih (by omega) j (by rw [buildOrChain_length]; exact hjk) i hi
    · have hjeq : j = k + 1 := by omega
      subst hjeq
      have hget : gateAt ⟨buildOrChain N x₀ y₀ (k + 1), 0⟩ (k + 1) = ⟨.or, [N + N + k, k]⟩ := by
        unfold gateAt; dsimp only [buildOrChain]
        have hlen : (buildOrChain N x₀ y₀ k).length = k + 1 := buildOrChain_length N x₀ y₀ k
        have hlt : k + 1 < (buildOrChain N x₀ y₀ k ++ [(⟨.or, [N + N + k, k]⟩ : Gate)]).length := by simp [hlen]
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by omega)]
        simp [hlen]
      rw [hget] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega

lemma buildOrChain_gates_legal (N : ℕ) (x₀ y₀ : Fin N) (m : ℕ) :
    ∀ gate ∈ buildOrChain N x₀ y₀ m, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)) := by
  induction m with
  | zero => intro gate hg; simp [buildOrChain] at hg; subst hg; simp
  | succ k ih =>
    intro gate hg; simp only [buildOrChain, List.mem_append, List.mem_singleton] at hg
    rcases hg with h1 | rfl
    · exact ih gate h1
    · simp

lemma buildOrChain_eval (N : ℕ) (x₀ y₀ : Fin N) (m : ℕ) (hm : m ≤ N)
    (w : Fin 0 → Bool) (x y : Fin N) :
    wireVal ⟨buildOrChain N x₀ y₀ m, 0⟩ (inpVec w x y) (N + N + m) =
      decide (x.val < m ∨ (x = x₀ ∧ y = y₀)) := by
  induction m with
  | zero =>
    have hread := buildOrChain_readsBack N x₀ y₀ 0 (by omega)
    have hlen : (inpVec w x y).length = N + N + 0 := inpVec_length w x y
    rw [wireVal_gate _ hread _ hlen (N + N + 0) (by omega) (by rw [buildOrChain_length]; omega)]
    have hsub : N + N + 0 - (N + N + 0) = 0 := by omega
    rw [hsub]
    simp only [gateAt, buildOrChain, List.getD_cons_zero, List.map_cons, List.map_nil, GateOp.eval,
      List.all_cons, List.all_nil, id_eq, Bool.and_true]
    rw [wireVal_input _ _ hlen x₀.val (by have := x₀.isLt; omega),
      wireVal_input _ _ hlen (N + y₀.val) (by have := y₀.isLt; omega),
      inpVec_getD_row w x y x₀.val x₀.isLt,
      inpVec_getD_col w x y (N + y₀.val) (by omega) (by have := y₀.isLt; omega)]
    simp [eq_comm]
  | succ k ih =>
    have hread := buildOrChain_readsBack N x₀ y₀ (k + 1) hm
    have hlen : (inpVec w x y).length = N + N + 0 := inpVec_length w x y
    rw [wireVal_gate _ hread _ hlen (N + N + (k + 1)) (by omega) (by rw [buildOrChain_length]; omega)]
    have hsub : N + N + (k + 1) - (N + N + 0) = k + 1 := by omega
    rw [hsub]
    have hget : gateAt ⟨buildOrChain N x₀ y₀ (k + 1), 0⟩ (k + 1) = ⟨.or, [N + N + k, k]⟩ := by
      unfold gateAt; dsimp only [buildOrChain]
      have hl : (buildOrChain N x₀ y₀ k).length = k + 1 := buildOrChain_length N x₀ y₀ k
      have hlt : k + 1 < (buildOrChain N x₀ y₀ k ++ [(⟨.or, [N + N + k, k]⟩ : Gate)]).length := by simp [hl]
      rw [List.getD_eq_getElem _ _ hlt, List.getElem_append_right (by omega)]
      simp [hl]
    rw [hget]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have hprev : wireVal ⟨buildOrChain N x₀ y₀ (k + 1), 0⟩ (inpVec w x y) (N + N + k) =
        wireVal ⟨buildOrChain N x₀ y₀ k, 0⟩ (inpVec w x y) (N + N + k) := by
      unfold wireVal Circuit.wires; dsimp only [buildOrChain]
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hlt : N + N + k < ((buildOrChain N x₀ y₀ k).foldl
          (fun ww gg => ww ++ [gg.op.eval (gg.inputs.map fun i => ww.getD i false)]) (inpVec w x y)).length := by
        rw [foldl_wires_length, inpVec_length, buildOrChain_length]; omega
      have hlt' : N + N + k < (((buildOrChain N x₀ y₀ k).foldl
          (fun (ww : List Bool) (gg : Gate) => ww ++ [gg.op.eval (gg.inputs.map fun i => ww.getD i false)]) (inpVec w x y)) ++
          [GateOp.eval .or (List.map (fun i => ((buildOrChain N x₀ y₀ k).foldl
            (fun (ww : List Bool) (gg : Gate) => ww ++ [gg.op.eval (gg.inputs.map fun i => ww.getD i false)])
            (inpVec w x y)).getD i false) [N + N + k, k])]).length := by
        rw [List.length_append, List.length_singleton]; omega
      rw [List.getD_eq_getElem _ _ hlt', List.getElem_append_left hlt, List.getD_eq_getElem _ _ hlt]
    rw [hprev, ih (by omega),
      wireVal_input _ _ hlen k (by omega),
      inpVec_getD_row w x y k (by omega)]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((h1 | h2) | h3)
      · exact Or.inl (by omega)
      · exact Or.inr h2
      · exact Or.inl (by have := congrArg Fin.val h3; dsimp at this; omega)
    · rintro (h1 | h2)
      · by_cases hlt : x.val < k
        · exact Or.inl (Or.inl hlt)
        · exact Or.inr (Fin.ext (by dsimp; omega))
      · exact Or.inl (Or.inr h2)

lemma part2_endpoint (N g : ℕ) (hg : 0 < g) (hgN : g + 1 < N) :
    ∃ (C : Circuit) (R : Finset (Fin N)) (x₀ y₀ : Fin N),
      legalC N 0 C ∧ C.size ≤ g ∧ R.card = g - 1 ∧ x₀ ∉ R ∧
      (∀ (w : Fin 0 → Bool) (x y : Fin N), tableC N 0 C w x y = decide (x ∈ R ∨ (x = x₀ ∧ y = y₀))) ∧
      (∀ w : Fin 0 → Bool, areaC (tableC N 0 C w) = (g - 1) * N + 1) ∧
      ¬ ∃ R' S' : Finset (Fin N), lineUnionC N 0 C R' S' := by
  let R : Finset (Fin N) := Finset.univ.filter (fun x : Fin N => x.val < g - 1)
  let x₀ : Fin N := ⟨g - 1, by omega⟩
  let y₀ : Fin N := ⟨0, by omega⟩
  let C : Circuit := ⟨buildOrChain N x₀ y₀ (g - 1), N + N + (g - 1)⟩
  have hRcard : R.card = g - 1 := by
    rw [← Fintype.card_fin (g - 1), ← Finset.card_univ]
    apply Finset.card_bij (fun (x : Fin N) (hx : x ∈ R) => (⟨x.val, (Finset.mem_filter.mp hx).2⟩ : Fin (g - 1)))
    · intro _ _; exact Finset.mem_univ _
    · intro a _ b _ hab; exact Fin.ext (by simpa using congrArg Fin.val hab)
    · intro j _
      exact ⟨⟨j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩, rfl⟩
  have hx0_not : x₀ ∉ R := by simp [R, x₀]
  have htab : ∀ (w : Fin 0 → Bool) (x y : Fin N),
      tableC N 0 C w x y = decide (x ∈ R ∨ (x = x₀ ∧ y = y₀)) := by
    intro w x y
    have h1 := buildOrChain_eval N x₀ y₀ (g - 1) (by omega) w x y
    change wireVal ⟨buildOrChain N x₀ y₀ (g - 1), 0⟩ (inpVec w x y) (N + N + (g - 1)) = _
    rw [h1]
    simp [R]
  refine ⟨C, R, x₀, y₀, ?_, ?_, hRcard, hx0_not, htab, ?_, ?_⟩
  · refine ⟨buildOrChain_readsBack N x₀ y₀ (g - 1) (by omega), ?_, buildOrChain_gates_legal N x₀ y₀ (g - 1)⟩
    change N + N + (g - 1) < N + N + 0 + (buildOrChain N x₀ y₀ (g - 1)).length
    rw [buildOrChain_length]; omega
  · change (buildOrChain N x₀ y₀ (g - 1)).length ≤ g
    rw [buildOrChain_length]; omega
  · intro w
    have hset : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => tableC N 0 C w z.1 z.2 = true) =
        insert (x₀, y₀) (R ×ˢ (Finset.univ : Finset (Fin N))) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_product,
        and_true, Prod.mk.injEq, htab w a b, decide_eq_true_eq]
      tauto
    unfold areaC
    rw [hset, Finset.card_insert_of_notMem, Finset.card_product, hRcard, Finset.card_univ, Fintype.card_fin]
    simp [hx0_not]
  · rintro ⟨R', S', hlu⟩
    let w : Fin 0 → Bool := fun j => j.elim0
    let x₁ : Fin N := ⟨g, by omega⟩
    have hx₁_notR : x₁ ∉ R := by simp [R, x₁]
    have hx₁_ne : x₁ ≠ x₀ := by intro h; have := congrArg Fin.val h; simp [x₁, x₀] at this; omega
    have hS_empty : ∀ y : Fin N, y ∉ S' := by
      intro y hy
      have h1 := hlu w x₁ y
      rw [htab w x₁ y] at h1
      simp [hx₁_notR, hx₁_ne, hy] at h1
    have hx0_in : x₀ ∈ R' := by
      have h1 := hlu w x₀ y₀
      rw [htab w x₀ y₀] at h1
      simp [hS_empty y₀] at h1
      exact h1
    let y₁ : Fin N := ⟨1, by omega⟩
    have hy₁_ne : y₁ ≠ y₀ := by intro h; have := congrArg Fin.val h; simp [y₁, y₀] at this
    have h1 := hlu w x₀ y₁
    rw [htab w x₀ y₁] at h1
    simp [hx0_not, hy₁_ne, hx0_in] at h1

lemma main_proof : ∀ (N g : ℕ), 0 < g → g + 1 < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N + h) C ∧ C.output < N + N + h + C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let area := fun (H : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 = true)).card
  let lineUnion := fun (h : ℕ) (C : Circ) (R S : Finset X) =>
    ∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (x ∈ R ∨ y ∈ S)
  (∀ (h : ℕ) (C : Circ), legal h C → C.size ≤ g → ∀ w₀ : Fin h → Bool,
    (g - 1) * N + 1 < area (table h C w₀) → area (table h C w₀) < N * (N - g) →
      (∃ R S : Finset X, g ≤ R.card + S.card ∧ R.card + S.card ≤ g + 1 ∧ lineUnion h C R S) ∨
      ∃ (R S : Finset X) (j : Fin h), R.card + S.card = g ∧
        ((w₀ j = false ∧ ∀ (w : Fin h → Bool) (x y : X),
          table h C w x y = decide (w j = true ∨ x ∈ R ∨ y ∈ S)) ∨
         (w₀ j = true ∧ ∃ B D : Finset X, B ⊆ R ∧ D ⊆ S ∧ (B ≠ R ∨ D ≠ S) ∧
          ∀ (w : Fin h → Bool) (x y : X), table h C w x y =
            decide (x ∈ B ∨ y ∈ D ∨ (w j = true ∧ (x ∈ R ∨ y ∈ S)))))) ∧
  ∃ (C : Circ) (R : Finset X) (x₀ y₀ : X), legal 0 C ∧ C.size ≤ g ∧
    R.card = g - 1 ∧ x₀ ∉ R ∧
    (∀ (w : Fin 0 → Bool) (x y : X), table 0 C w x y = decide (x ∈ R ∨ (x = x₀ ∧ y = y₀))) ∧
    (∀ w : Fin 0 → Bool, area (table 0 C w) = (g - 1) * N + 1) ∧
    ¬ ∃ R' S' : Finset X, lineUnion 0 C R' S' := by
  intro N g hg hgN
  exact ⟨part1_classification N g hg hgN, part2_endpoint N g hg hgN⟩

end PEqualNP.Outside.L_meta_33601_aux

theorem PEqualNP.Outside.L_meta_33601 : (∀ (N g : ℕ), 0 < g → g+1 < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let legal := fun (h : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N+h) C ∧ C.output < N+N+h+C.size ∧
    ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))
  let table := fun (h : ℕ) (C : Circ) (w : Fin h → Bool) (x y : X) =>
    C.eval (PEqualNP.Represents.oneEach x y ++ List.ofFn w)
  let area := fun (H : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => H z.1 z.2 = true)).card
  let lineUnion := fun (h : ℕ) (C : Circ) (R S : Finset X) =>
    ∀ (w : Fin h → Bool) (x y : X), table h C w x y = decide (x ∈ R ∨ y ∈ S)
  (∀ (h : ℕ) (C : Circ), legal h C → C.size ≤ g → ∀ w₀ : Fin h → Bool,
    (g-1)*N+1 < area (table h C w₀) → area (table h C w₀) < N*(N-g) →
      (∃ R S : Finset X, g ≤ R.card+S.card ∧ R.card+S.card ≤ g+1 ∧ lineUnion h C R S) ∨
      ∃ (R S : Finset X) (j : Fin h), R.card+S.card = g ∧
        ((w₀ j = false ∧ ∀ (w : Fin h → Bool) (x y : X),
          table h C w x y = decide (w j = true ∨ x ∈ R ∨ y ∈ S)) ∨
         (w₀ j = true ∧ ∃ B D : Finset X, B ⊆ R ∧ D ⊆ S ∧ (B ≠ R ∨ D ≠ S) ∧
          ∀ (w : Fin h → Bool) (x y : X), table h C w x y =
            decide (x ∈ B ∨ y ∈ D ∨ (w j = true ∧ (x ∈ R ∨ y ∈ S)))))) ∧
  ∃ (C : Circ) (R : Finset X) (x₀ y₀ : X), legal 0 C ∧ C.size ≤ g ∧
    R.card = g-1 ∧ x₀ ∉ R ∧
    (∀ (w : Fin 0 → Bool) (x y : X), table 0 C w x y = decide (x ∈ R ∨ (x=x₀ ∧ y=y₀))) ∧
    (∀ w : Fin 0 → Bool, area (table 0 C w) = (g-1)*N+1) ∧
    ¬∃ R' S' : Finset X, lineUnion 0 C R' S') :=
  PEqualNP.Outside.L_meta_33601_aux.main_proof
