import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

namespace PEqualNP.Outside.L_lib_1175

abbrev Lit (b : Nat) := Fin b × Bool
abbrev Hidden (b : Nat) := Finset (Lit b)
abbrev Clause (b n : Nat) := Finset ((Fin n × Bool) × Bool) × Hidden b

def holds {b : Nat} (D : Hidden b) (h : Fin b → Bool) : Prop :=
  ∃ l ∈ D, h l.1 = l.2

def encodes {b n : Nat} (C : Finset (Clause b n)) : Prop :=
  ∀ x : Fin n → Bool → Bool, (∃ i, x i false = true ∧ x i true = true) ↔
    ∃ h : Fin b → Bool, ∀ c ∈ C,
      (∃ l ∈ c.1, x l.1.1 l.1.2 = l.2) ∨ holds c.2 h

def feasible (b s n : Nat) : Prop :=
  ∃ C : Finset (Clause b n), encodes C ∧ (∀ c ∈ C, c.1.card + c.2.card ≤ 3) ∧ C.card ≤ 2 * n + s

def negLit {b : Nat} (l : Lit b) : Lit b := (l.1, !l.2)

lemma negLit_negLit {b : Nat} (l : Lit b) : negLit (negLit l) = l := by
  rcases l with ⟨i, r⟩
  cases r <;> rfl

lemma negLit_ne {b : Nat} (l : Lit b) : negLit l ≠ l := by
  rcases l with ⟨i, r⟩
  cases r <;> simp [negLit]

lemma negLit_inj {b : Nat} : Function.Injective (@negLit b) := by
  intro l₁ l₂ h
  have := congrArg negLit h
  simpa [negLit_negLit] using this

lemma bool_ne_not (r : Bool) : r ≠ !r := by
  cases r <;> decide

lemma bool_eq_not_false {r : Bool} (h : r = !r) : False :=
  bool_ne_not r h

def litCode {b : Nat} (l : Lit b) : Nat :=
  l.1.val * 2 + if l.2 then 1 else 0

lemma negLit_true_of_ne {b : Nat} {h : Fin b → Bool} {x : Lit b} (hx : h x.1 ≠ x.2) :
    h (negLit x).1 = (negLit x).2 := by
  rcases x with ⟨i, r⟩
  simp only [negLit]
  cases hi : h i <;> cases r <;> simp_all

lemma litCode_inj {b : Nat} : Function.Injective (@litCode b) := by
  intro ⟨i₁, r₁⟩ ⟨i₂, r₂⟩ h
  have h' : i₁.val * 2 + (if r₁ then 1 else 0) = i₂.val * 2 + (if r₂ then 1 else 0) := h
  cases r₁ <;> cases r₂ <;> simp only [Bool.false_eq_true, ↓reduceIte] at h'
  · have hv : i₁.val = i₂.val := by omega
    exact Prod.ext (Fin.ext hv) rfl
  · omega
  · omega
  · have hv : i₁.val = i₂.val := by omega
    exact Prod.ext (Fin.ext hv) rfl

lemma sum_card_filter_comm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop)
    [∀ a, DecidablePred (P a)] [∀ b, DecidablePred (fun a => P a b)] :
    ∑ a ∈ s, (t.filter (fun b => P a b)).card = ∑ b ∈ t, (s.filter (fun a => P a b)).card := by
  have h1 : ∀ (u : Finset β) (q : β → Prop) [DecidablePred q],
      (u.filter q).card = ∑ b ∈ u, if q b then 1 else 0 := by
    intro u q _
    induction u using Finset.induction_on with
    | empty => simp
    | @insert x u hx ih =>
      by_cases hq : q x
      · rw [Finset.filter_insert, ite_eq_left hq,
            Finset.card_insert_of_notMem, Finset.sum_insert hx,
            ite_eq_left hq, ih]
        · omega
        · intro hm; exact hx (Finset.mem_filter.mp hm).1
      · rw [Finset.filter_insert, ite_eq_right hq,
            Finset.sum_insert hx, ite_eq_right hq, ih]
        omega
  have h2 : ∀ (u : Finset α) (q : α → Prop) [DecidablePred q],
      (u.filter q).card = ∑ a ∈ u, if q a then 1 else 0 := by
    intro u q _
    induction u using Finset.induction_on with
    | empty => simp
    | @insert x u hx ih =>
      by_cases hq : q x
      · rw [Finset.filter_insert, ite_eq_left hq,
            Finset.card_insert_of_notMem, Finset.sum_insert hx,
            ite_eq_left hq, ih]
        · omega
        · intro hm; exact hx (Finset.mem_filter.mp hm).1
      · rw [Finset.filter_insert, ite_eq_right hq,
            Finset.sum_insert hx, ite_eq_right hq, ih]
        omega
  trans (∑ a ∈ s, ∑ b ∈ t, if P a b then 1 else 0)
  · exact Finset.sum_congr rfl fun a _ => h1 t (P a)
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => (h2 s (fun a => P a b)).symm

-- Part 1: Signed equality cycle attains n = 2 * b

def cycHidden (b : Nat) (hb : 2 ≤ b) (i : Fin (2 * b)) : Hidden b :=
  if h1 : i.val + 1 < b then
    {(⟨i.val, by omega⟩, false), (⟨i.val + 1, h1⟩, true)}
  else if _h2 : i.val < b then
    {(⟨b - 1, by omega⟩, false), (⟨0, by omega⟩, false)}
  else if _h3 : i.val + 1 < 2 * b then
    {(⟨i.val - b, by omega⟩, true), (⟨i.val - b + 1, by omega⟩, false)}
  else
    {(⟨b - 1, by omega⟩, true), (⟨0, by omega⟩, true)}

lemma cycHidden_card_le (b : Nat) (hb : 2 ≤ b) (i : Fin (2 * b)) :
    (cycHidden b hb i).card ≤ 2 := by
  unfold cycHidden
  split_ifs <;> exact (Finset.card_insert_le _ _).trans (by simp)

def cycClause (b : Nat) (hb : 2 ≤ b) (p : Fin (2 * b) × Bool) : Clause b (2 * b) :=
  ({(p, true)}, cycHidden b hb p.1)

lemma cycHidden_sat_removed (b : Nat) (hb : 2 ≤ b) (i : Fin (2 * b)) :
    ∃ h : Fin b → Bool, ∀ k : Fin (2 * b), k ≠ i → holds (cycHidden b hb k) h := by
  by_cases hi : i.val < b
  · refine ⟨fun j => decide (j.val ≤ i.val), ?_⟩
    intro k hki
    have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
    unfold cycHidden
    by_cases h1 : k.val + 1 < b
    · rw [dite_eq_left h1]
      by_cases hlt : k.val < i.val
      · refine ⟨(⟨k.val + 1, h1⟩, true), by simp, ?_⟩
        simp only [decide_eq_true_eq]; omega
      · refine ⟨(⟨k.val, by omega⟩, false), by simp, ?_⟩
        simp only [decide_eq_false_iff_not]; omega
    · rw [dite_eq_right h1]
      by_cases h2 : k.val < b
      · rw [dite_eq_left h2]
        refine ⟨(⟨b - 1, by omega⟩, false), by simp, ?_⟩
        simp only [decide_eq_false_iff_not]; omega
      · rw [dite_eq_right h2]
        by_cases h3 : k.val + 1 < 2 * b
        · rw [dite_eq_left h3]
          by_cases hle : k.val - b ≤ i.val
          · refine ⟨(⟨k.val - b, by omega⟩, true), by simp, ?_⟩
            simp only [decide_eq_true_eq]; omega
          · refine ⟨(⟨k.val - b + 1, by omega⟩, false), by simp, ?_⟩
            simp only [decide_eq_false_iff_not]; omega
        · rw [dite_eq_right h3]
          refine ⟨(⟨0, by omega⟩, true), by simp, ?_⟩
          simp only [decide_eq_true_eq]; omega
  · refine ⟨fun j => decide (i.val - b < j.val), ?_⟩
    intro k hki
    have hval : k.val ≠ i.val := fun h => hki (Fin.ext h)
    unfold cycHidden
    by_cases h1 : k.val + 1 < b
    · rw [dite_eq_left h1]
      by_cases hle : k.val ≤ i.val - b
      · refine ⟨(⟨k.val, by omega⟩, false), by simp, ?_⟩
        simp only [decide_eq_false_iff_not]; omega
      · refine ⟨(⟨k.val + 1, h1⟩, true), by simp, ?_⟩
        simp only [decide_eq_true_eq]; omega
    · rw [dite_eq_right h1]
      by_cases h2 : k.val < b
      · rw [dite_eq_left h2]
        refine ⟨(⟨0, by omega⟩, false), by simp, ?_⟩
        simp only [decide_eq_false_iff_not]; omega
      · rw [dite_eq_right h2]
        by_cases h3 : k.val + 1 < 2 * b
        · rw [dite_eq_left h3]
          by_cases hlt : k.val - b < i.val - b
          · refine ⟨(⟨k.val - b + 1, by omega⟩, false), by simp, ?_⟩
            simp only [decide_eq_false_iff_not]; omega
          · refine ⟨(⟨k.val - b, by omega⟩, true), by simp, ?_⟩
            simp only [decide_eq_true_eq]; omega
        · rw [dite_eq_right h3]
          refine ⟨(⟨b - 1, by omega⟩, true), by simp, ?_⟩
          simp only [decide_eq_true_eq]; omega

lemma cycHidden_unsat (b : Nat) (hb : 2 ≤ b) (h : Fin b → Bool)
    (hall : ∀ k : Fin (2 * b), holds (cycHidden b hb k) h) : False := by
  cases h0 : h ⟨0, by omega⟩
  · have hfalse : ∀ j : Nat, (hj : j < b) → h ⟨j, hj⟩ = false := by
      intro j
      induction j with
      | zero => intro _; exact h0
      | succ j ih =>
        intro hj
        have hk := hall ⟨b + j, by omega⟩
        unfold cycHidden at hk
        dsimp only at hk
        rw [dite_eq_right (by omega), dite_eq_right (by omega),
            dite_eq_left (by omega)] at hk
        rcases hk with ⟨l, hl, hlv⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · have hjf := ih (by omega)
          have hsub : b + j - b = j := by omega
          simp only [hsub] at hlv
          rw [hjf] at hlv; cases hlv
        · have hsub : b + j - b + 1 = j + 1 := by omega
          simpa [hsub] using hlv
    have hlast := hall ⟨2 * b - 1, by omega⟩
    unfold cycHidden at hlast
    dsimp only at hlast
    rw [dite_eq_right (by omega), dite_eq_right (by omega),
        dite_eq_right (by omega)] at hlast
    rcases hlast with ⟨l, hl, hlv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · rw [hfalse (b - 1) (by omega)] at hlv; cases hlv
    · rw [h0] at hlv; cases hlv
  · have htrue : ∀ j : Nat, (hj : j < b) → h ⟨j, hj⟩ = true := by
      intro j
      induction j with
      | zero => intro _; exact h0
      | succ j ih =>
        intro hj
        have hk := hall ⟨j, by omega⟩
        unfold cycHidden at hk
        dsimp only at hk
        rw [dite_eq_left (by omega)] at hk
        rcases hk with ⟨l, hl, hlv⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · rw [ih (by omega)] at hlv; cases hlv
        · exact hlv
    have hlast := hall ⟨b - 1, by omega⟩
    unfold cycHidden at hlast
    dsimp only at hlast
    rw [dite_eq_right (by omega), dite_eq_left (by omega)] at hlast
    rcases hlast with ⟨l, hl, hlv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · rw [htrue (b - 1) (by omega)] at hlv; cases hlv
    · rw [h0] at hlv; cases hlv

lemma feasible_two_mul (b s : Nat) (hb : 2 ≤ b) : feasible b s (2 * b) := by
  let C : Finset (Clause b (2 * b)) :=
    (Finset.univ : Finset (Fin (2 * b) × Bool)).image (cycClause b hb)
  refine ⟨C, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨i, hif, hit⟩
      obtain ⟨h, hh⟩ := cycHidden_sat_removed b hb i
      refine ⟨h, ?_⟩
      intro c hc
      rcases Finset.mem_image.mp hc with ⟨⟨k, a⟩, _, rfl⟩
      by_cases hki : k = i
      · subst hki
        left
        refine ⟨((k, a), true), by simp [cycClause], ?_⟩
        cases a <;> assumption
      · right
        exact hh k hki
    · rintro ⟨h, hh⟩
      by_contra hnone
      have hnot : ∀ k : Fin (2 * b), ¬(x k false = true ∧ x k true = true) := by
        intro k hk; exact hnone ⟨k, hk⟩
      apply cycHidden_unsat b hb h
      intro k
      have ha : ∃ a : Bool, x k a = false := by
        cases hf : x k false
        · exact ⟨false, hf⟩
        · cases ht : x k true
          · exact ⟨true, ht⟩
          · exact False.elim (hnot k ⟨hf, ht⟩)
      rcases ha with ⟨a, hxa⟩
      have hc : cycClause b hb (k, a) ∈ C :=
        Finset.mem_image.mpr ⟨(k, a), Finset.mem_univ _, rfl⟩
      rcases hh _ hc with ⟨l, hl, hlv⟩ | hh'
      · simp only [cycClause, Finset.mem_singleton] at hl
        subst hl
        simp only [hxa] at hlv
        cases hlv
      · exact hh'
  · intro c hc
    rcases Finset.mem_image.mp hc with ⟨p, _, rfl⟩
    have h2 := cycHidden_card_le b hb p.1
    simp only [cycClause, Finset.card_singleton]
    omega
  · calc C.card ≤ (Finset.univ : Finset (Fin (2 * b) × Bool)).card := Finset.card_image_le
      _ = 2 * b * 2 := by simp
      _ ≤ 2 * (2 * b) + s := by omega

-- Part 2a: Extracting minimal hidden conflict & ternary bound

lemma no_unsat_empty_hidden {b n : Nat} (hn : 4 ≤ n) {C : Finset (Clause b n)}
    (henc : encodes C) (hw : ∀ c ∈ C, c.1.card + c.2.card ≤ 3)
    {c : Clause b n} (hc : c ∈ C) (hc2 : c.2 = ∅)
    (x : Fin n → Bool → Bool) : ∃ l ∈ c.1, x l.1.1 l.1.2 = l.2 := by
  by_contra hno
  have hcard : (c.1.image (fun l => l.1.1)).card < (Finset.univ : Finset (Fin n)).card := by
    have h1 : (c.1.image (fun l => l.1.1)).card ≤ c.1.card := Finset.card_image_le
    have h2 : c.1.card ≤ 3 := by have := hw c hc; omega
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  let x' : Fin n → Bool → Bool := fun j r => if j = i₀ then true else x j r
  have hpair : ∃ i, x' i false = true ∧ x' i true = true :=
    ⟨i₀, by simp [x'], by simp [x']⟩
  obtain ⟨h, hh⟩ := (henc x').mp hpair
  rcases hh c hc with ⟨l, hl, hlv⟩ | ⟨l, hl, _⟩
  · have hne : l.1.1 ≠ i₀ := fun heq =>
      hi₀ (Finset.mem_image.mpr ⟨l, hl, heq⟩)
    simp only [x', ite_eq_right hne] at hlv
    exact hno ⟨l, hl, hlv⟩
  · rw [hc2] at hl; exact False.elim (Finset.notMem_empty _ hl)

def posLits {b n : Nat} (c : Clause b n) : Finset (Fin n × Bool) :=
  Finset.univ.filter (fun v => (v, true) ∈ c.1)

lemma posLits_card_le {b n : Nat} (c : Clause b n) : (posLits c).card ≤ c.1.card := by
  refine Finset.card_le_card_of_injOn (fun v => (v, true)) ?_ ?_
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro v₁ _ v₂ _ h
    exact congrArg Prod.fst h

lemma two_mul_n_le_pos_clauses {b n : Nat} (hn : 4 ≤ n) {C : Finset (Clause b n)}
    (henc : encodes C) (hw : ∀ c ∈ C, c.1.card + c.2.card ≤ 3) :
    2 * n ≤ (C.filter (fun c => 1 ≤ (posLits c).card)).card := by
  classical
  let Cgood := C.filter (fun c => c.2.Nonempty ∧ ¬∃ w, (w, false) ∈ c.1 ∧ (w, true) ∈ c.1)
  let C1 := Cgood.filter (fun c => (posLits c).card = 1)
  let C2 := Cgood.filter (fun c => (posLits c).card = 2)
  let A : Fin n × Bool → Finset (Clause b n) := fun v =>
    Cgood.filter (fun c => (v, true) ∈ c.1 ∧ ((v.1, !v.2), true) ∉ c.1)
  have hgood_le2 : ∀ c ∈ Cgood, (posLits c).card ≤ 2 := by
    intro c hc
    have hmem : c ∈ C := (Finset.mem_filter.mp hc).1
    have hne : c.2.Nonempty := (Finset.mem_filter.mp hc).2.1
    have hc2 : 1 ≤ c.2.card := Finset.card_pos.mpr hne
    have hwc := hw c hmem
    have hp := posLits_card_le c
    omega
  have hA_step : ∀ (v : Fin n × Bool) (x : Fin n → Bool → Bool),
      (∀ j, ¬(x j false = true ∧ x j true = true)) →
      x v.1 v.2 = false → x v.1 (!v.2) = true →
      ∃ c ∈ A v, ¬∃ l ∈ c.1, x l.1.1 l.1.2 = l.2 := by
    intro ⟨i, r⟩ x hpf hxr hxnr
    let x' : Fin n → Bool → Bool := fun j q => if (j, q) = (i, r) then true else x j q
    have hpair : ∃ j, x' j false = true ∧ x' j true = true := by
      refine ⟨i, ?_, ?_⟩
      · cases r
        · simp [x']
        · simp only [x', Prod.mk.injEq, true_and, Bool.false_eq_true, ↓reduceIte]
          exact hxnr
      · cases r
        · simp only [x', Prod.mk.injEq, true_and, Bool.true_eq_false, ↓reduceIte]
          exact hxnr
        · simp [x']
    obtain ⟨h, hh⟩ := (henc x').mp hpair
    have hunsat : ¬∀ c ∈ C, (∃ l ∈ c.1, x l.1.1 l.1.2 = l.2) ∨ holds c.2 h := by
      intro hall
      obtain ⟨j, hj⟩ := (henc x).mpr ⟨h, hall⟩
      exact hpf j hj
    have hex_fail : ∃ c ∈ C, (¬∃ l ∈ c.1, x l.1.1 l.1.2 = l.2) ∧ ¬holds c.2 h := by
      by_contra hno
      apply hunsat
      intro c hc
      by_cases h1 : ∃ l ∈ c.1, x l.1.1 l.1.2 = l.2
      · exact Or.inl h1
      · by_cases h2 : holds c.2 h
        · exact Or.inr h2
        · exact False.elim (hno ⟨c, hc, h1, h2⟩)
    obtain ⟨c, hcC, hcx, hch⟩ := hex_fail
    have hc2ne : c.2.Nonempty := by
      by_contra he
      rw [Finset.not_nonempty_iff_eq_empty] at he
      exact hcx (no_unsat_empty_hidden hn henc hw hcC he x)
    have hnot_taut : ¬∃ w, (w, false) ∈ c.1 ∧ (w, true) ∈ c.1 := by
      rintro ⟨⟨j, q⟩, hf, ht⟩
      cases hxq : x j q
      · exact hcx ⟨((j, q), false), hf, hxq⟩
      · exact hcx ⟨((j, q), true), ht, hxq⟩
    have hcgood : c ∈ Cgood := Finset.mem_filter.mpr ⟨hcC, hc2ne, hnot_taut⟩
    have hcx' : ∃ l ∈ c.1, x' l.1.1 l.1.2 = l.2 :=
      (hh c hcC).resolve_right hch
    rcases hcx' with ⟨⟨⟨j, q⟩, p⟩, hl, hlv⟩
    have hne : x j q ≠ p := fun heq => hcx ⟨((j, q), p), hl, heq⟩
    have hjp : (j, q) = (i, r) := by
      by_contra hneq
      simp only [x', ite_eq_right hneq] at hlv
      exact hne hlv
    have hp : p = true := by
      simp only [x', ite_eq_left hjp] at hlv
      exact hlv.symm
    have hmem1 : ((i, r), true) ∈ c.1 := by
      rcases Prod.mk.inj hjp with ⟨rfl, rfl⟩
      subst hp; exact hl
    have hmem2 : ((i, !r), true) ∉ c.1 := fun hm =>
      hcx ⟨((i, !r), true), hm, hxnr⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨hcgood, hmem1, hmem2⟩, hcx⟩
  have hA_dich : ∀ v : Fin n × Bool,
      (∃ c ∈ C1, c ∈ A v) ∨ 2 ≤ (A v ∩ C2).card := by
    intro ⟨i, r⟩
    by_cases h1 : ∃ c ∈ C1, c ∈ A (i, r)
    · exact Or.inl h1
    · right
      have hsub : A (i, r) ⊆ C2 := by
        intro c hc
        have hcg : c ∈ Cgood := (Finset.mem_filter.mp hc).1
        have hmem : (i, r) ∈ posLits c :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2.1⟩
        have hge1 : 1 ≤ (posLits c).card := Finset.card_pos.mpr ⟨(i, r), hmem⟩
        have hle2 : (posLits c).card ≤ 2 := hgood_le2 c hcg
        have hne1 : (posLits c).card ≠ 1 := fun heq =>
          h1 ⟨c, Finset.mem_filter.mpr ⟨hcg, heq⟩, hc⟩
        exact Finset.mem_filter.mpr ⟨hcg, by omega⟩
      let x₁ : Fin n → Bool → Bool := fun j q => decide (j = i ∧ q = !r)
      have hx₁pf : ∀ j, ¬(x₁ j false = true ∧ x₁ j true = true) := by
        intro j ⟨hf, ht⟩
        simp only [x₁, decide_eq_true_eq] at hf ht
        cases hf.2.trans ht.2.symm
      have hx₁f : x₁ i r = false := by
        simp only [x₁, decide_eq_false_iff_not, true_and]
        exact bool_ne_not r
      have hx₁t : x₁ i (!r) = true := by simp [x₁]
      obtain ⟨c₁, hc₁A, _⟩ := hA_step (i, r) x₁ hx₁pf hx₁f hx₁t
      have hc₁2 : c₁ ∈ C2 := hsub hc₁A
      have hc₁card : (posLits c₁).card = 2 := (Finset.mem_filter.mp hc₁2).2
      have hpos1 : (i, r) ∈ posLits c₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc₁A).2.1⟩
      have hne_er : ((posLits c₁).erase (i, r)).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hpos1, hc₁card]
        omega
      obtain ⟨⟨j, q⟩, hjq⟩ := hne_er
      have hjq_ne : (j, q) ≠ (i, r) := (Finset.mem_erase.mp hjq).1
      have hjq_pos : ((j, q), true) ∈ c₁.1 :=
        (Finset.mem_filter.mp (Finset.mem_erase.mp hjq).2).2
      have hj_ne_i : j ≠ i := by
        intro hji
        subst hji
        have hq_ne : q ≠ r := fun hqr => hjq_ne (by subst hqr; rfl)
        have hq_eq : q = !r := by cases q <;> cases r <;> simp_all
        subst hq_eq
        exact (Finset.mem_filter.mp hc₁A).2.2 hjq_pos
      let x₂ : Fin n → Bool → Bool := fun k p =>
        decide ((k = i ∧ p = !r) ∨ (k = j ∧ p = q))
      have hx₂pf : ∀ k, ¬(x₂ k false = true ∧ x₂ k true = true) := by
        intro k ⟨hf, ht⟩
        simp only [x₂, decide_eq_true_eq] at hf ht
        rcases hf with ⟨rfl, hfr⟩ | ⟨rfl, hfq⟩
        · rcases ht with ⟨_, htr⟩ | ⟨hji, _⟩
          · cases hfr.trans htr.symm
          · exact hj_ne_i hji.symm
        · rcases ht with ⟨hji, _⟩ | ⟨_, htq⟩
          · exact hj_ne_i hji
          · cases hfq.trans htq.symm
      have hx₂f : x₂ i r = false := by
        simp only [x₂, decide_eq_false_iff_not]
        rintro (⟨_, hr⟩ | ⟨hij, _⟩)
        · exact bool_ne_not r hr
        · exact hj_ne_i hij.symm
      have hx₂t : x₂ i (!r) = true := by simp [x₂]
      obtain ⟨c₂, hc₂A, hc₂x⟩ := hA_step (i, r) x₂ hx₂pf hx₂f hx₂t
      have hc₂ne : c₂ ≠ c₁ := by
        intro heq; subst heq
        exact hc₂x ⟨((j, q), true), hjq_pos, by simp [x₂]⟩
      have hpair_sub : ({c₁, c₂} : Finset (Clause b n)) ⊆ A (i, r) ∩ C2 := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hc₁A, hc₁2⟩
        · exact Finset.mem_inter.mpr ⟨hc₂A, hsub hc₂A⟩
      calc 2 = ({c₁, c₂} : Finset (Clause b n)).card := (Finset.card_pair hc₂ne.symm).symm
        _ ≤ (A (i, r) ∩ C2).card := Finset.card_le_card hpair_sub
  let P1 : Finset (Fin n × Bool) := Finset.univ.filter (fun v => ∃ c ∈ C1, c ∈ A v)
  let P2 : Finset (Fin n × Bool) := Finset.univ \ P1
  have hP1 : P1.card ≤ C1.card := by
    let f : Fin n × Bool → Clause b n := fun v =>
      if h : ∃ c ∈ C1, c ∈ A v then Classical.choose h else (∅, ∅)
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro v hv
      have h : ∃ c ∈ C1, c ∈ A v := (Finset.mem_filter.mp hv).2
      simp only [f, dite_eq_left h]
      exact (Classical.choose_spec h).1
    · intro v₁ hv₁ v₂ hv₂ heq
      have h₁ : ∃ c ∈ C1, c ∈ A v₁ := (Finset.mem_filter.mp hv₁).2
      have h₂ : ∃ c ∈ C1, c ∈ A v₂ := (Finset.mem_filter.mp hv₂).2
      simp only [f, dite_eq_left h₁,
                    dite_eq_left h₂] at heq
      set c := Classical.choose h₁
      have hc1 : c ∈ C1 := (Classical.choose_spec h₁).1
      have hv₁c : v₁ ∈ posLits c :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Classical.choose_spec h₁).2).2.1⟩
      have hv₂c : v₂ ∈ posLits c := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Classical.choose_spec h₂).2).2.1⟩
      have hcard1 : (posLits c).card = 1 := (Finset.mem_filter.mp hc1).2
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      rw [hw, Finset.mem_singleton] at hv₁c hv₂c
      exact hv₁c.trans hv₂c.symm
  have hP2 : P2.card ≤ C2.card := by
    have hlow : 2 * P2.card ≤ ∑ v ∈ P2, (C2.filter (fun c => v ∈ posLits c)).card := by
      calc 2 * P2.card = ∑ _v ∈ P2, 2 := by simp [Nat.mul_comm]
        _ ≤ ∑ v ∈ P2, (C2.filter (fun c => v ∈ posLits c)).card := by
          refine Finset.sum_le_sum fun v hv => ?_
          have hnot1 : ¬∃ c ∈ C1, c ∈ A v := by
            intro h; exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hge2 : 2 ≤ (A v ∩ C2).card := (hA_dich v).resolve_left hnot1
          refine hge2.trans (Finset.card_le_card fun c hc => ?_)
          have hcA := (Finset.mem_inter.mp hc).1
          have hc2 := (Finset.mem_inter.mp hc).2
          exact Finset.mem_filter.mpr ⟨hc2,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hcA).2.1⟩⟩
    have hsw : ∑ v ∈ P2, (C2.filter (fun c => v ∈ posLits c)).card =
        ∑ c ∈ C2, (P2.filter (fun v => v ∈ posLits c)).card :=
      sum_card_filter_comm P2 C2 (fun v c => v ∈ posLits c)
    have hup : ∑ c ∈ C2, (P2.filter (fun v => v ∈ posLits c)).card ≤ 2 * C2.card := by
      calc ∑ c ∈ C2, (P2.filter (fun v => v ∈ posLits c)).card
          ≤ ∑ c ∈ C2, (posLits c).card := by
            refine Finset.sum_le_sum fun c _ => Finset.card_le_card fun v hv =>
              (Finset.mem_filter.mp hv).2
        _ = ∑ _c ∈ C2, 2 := Finset.sum_congr rfl fun c hc => (Finset.mem_filter.mp hc).2
        _ = 2 * C2.card := by simp [Nat.mul_comm]
    omega
  have hdisj : Disjoint C1 C2 := by
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    have h1 := (Finset.mem_filter.mp hc1).2
    have h2 := (Finset.mem_filter.mp hc2).2
    omega
  have hsub : C1 ∪ C2 ⊆ C.filter (fun c => 1 ≤ (posLits c).card) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc1 | hc2
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hc1).1).1,
        by rw [(Finset.mem_filter.mp hc1).2]⟩
    · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hc2).1).1,
        by rw [(Finset.mem_filter.mp hc2).2]; omega⟩
  have hPsum : P1.card + P2.card = 2 * n := by
    have h1 : P1 ∪ P2 = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ P1)
    have h2 : Disjoint P1 P2 := Finset.disjoint_sdiff
    have h3 : (P1 ∪ P2).card = P1.card + P2.card := Finset.card_union_of_disjoint h2
    rw [h1] at h3
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h3
    omega
  have hCsum : C1.card + C2.card ≤ (C.filter (fun c => 1 ≤ (posLits c).card)).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  omega

-- Part 3: Implication graph & Krom's 2-SAT completeness

def BEdge {b : Nat} (HB : Finset (Hidden b)) (x y : Lit b) : Prop :=
  ({negLit x, y} : Hidden b) ∈ HB

def BReach {b : Nat} (HB : Finset (Hidden b)) (x y : Lit b) : Prop :=
  Relation.ReflTransGen (BEdge HB) x y

lemma BReach_mono {b : Nat} {HB₁ HB₂ : Finset (Hidden b)} (hsub : HB₁ ⊆ HB₂)
    {x y : Lit b} (h : BReach HB₁ x y) : BReach HB₂ x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih => exact Relation.ReflTransGen.tail ih (hsub he)

lemma BEdge_contra {b : Nat} {HB : Finset (Hidden b)} {x y : Lit b}
    (h : BEdge HB x y) : BEdge HB (negLit y) (negLit x) := by
  unfold BEdge at h ⊢
  rw [negLit_negLit, Finset.pair_comm]
  exact h

lemma BReach_contra {b : Nat} {HB : Finset (Hidden b)} {x y : Lit b}
    (h : BReach HB x y) : BReach HB (negLit y) (negLit x) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih => exact Relation.ReflTransGen.head (BEdge_contra he) ih

lemma BReach_sound {b : Nat} {HB : Finset (Hidden b)} {h : Fin b → Bool}
    (hsat : ∀ D ∈ HB, holds D h) {x y : Lit b} (hr : BReach HB x y)
    (hx : h x.1 = x.2) : h y.1 = y.2 := by
  induction hr with
  | refl => exact hx
  | tail _ he ih =>
    rcases hsat _ he with ⟨l, hl, hlv⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl
    · simp only [negLit] at hlv
      rw [ih] at hlv
      exact False.elim (bool_eq_not_false hlv)
    · exact hlv

lemma holds_of_BEdge_closed {b : Nat} {HB : Finset (Hidden b)}
    (h2 : ∀ D ∈ HB, D.card = 2) {h : Fin b → Bool}
    (hcl : ∀ x y, BEdge HB x y → h x.1 = x.2 → h y.1 = y.2) :
    ∀ D ∈ HB, holds D h := by
  intro D hD
  obtain ⟨l₁, l₂, _, rfl⟩ := Finset.card_eq_two.mp (h2 D hD)
  by_cases hl1 : h l₁.1 = l₁.2
  · exact ⟨l₁, by simp, hl1⟩
  · have hneg : h (negLit l₁).1 = (negLit l₁).2 := by
      simp only [negLit]
      cases h1 : h l₁.1 <;> cases h2' : l₁.2 <;> simp_all
    have hedge : BEdge HB (negLit l₁) l₂ := by
      unfold BEdge
      rw [negLit_negLit]
      exact hD
    exact ⟨l₂, by simp, hcl _ _ hedge hneg⟩

lemma krom_sat {b : Nat} (HB : Finset (Hidden b)) (h2 : ∀ D ∈ HB, D.card = 2)
    (W : Finset (Lit b))
    (hnoSelf : ∀ x, ¬(BReach HB x (negLit x) ∧ BReach HB (negLit x) x))
    (hcons : ∀ u ∈ W, ∀ v ∈ W, ¬BReach HB u (negLit v)) :
    ∃ h : Fin b → Bool, (∀ D ∈ HB, holds D h) ∧ (∀ u ∈ W, h u.1 = u.2) := by
  classical
  let Cons := (Finset.univ : Finset (Lit b)).powerset.filter
    (fun S => W ⊆ S ∧ ∀ u ∈ S, ∀ v ∈ S, ¬BReach HB u (negLit v))
  have hWmem : W ∈ Cons :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ W),
      Finset.Subset.refl W, hcons⟩
  obtain ⟨S, hSmem, hSmax⟩ := Finset.exists_max_image Cons Finset.card ⟨W, hWmem⟩
  have hWS : W ⊆ S := (Finset.mem_filter.mp hSmem).2.1
  have hScons : ∀ u ∈ S, ∀ v ∈ S, ¬BReach HB u (negLit v) :=
    (Finset.mem_filter.mp hSmem).2.2
  have hcov : ∀ i : Fin b, (i, false) ∈ S ∨ (i, true) ∈ S := by
    intro i
    by_contra hneither
    push Not at hneither
    rcases hneither with ⟨hf, ht⟩
    have hbad : ∀ r : Bool, (i, r) ∉ S →
        BReach HB (i, r) (negLit (i, r)) ∨ ∃ u ∈ S, BReach HB u (negLit (i, r)) := by
      intro r hr
      by_contra hok
      push Not at hok
      rcases hok with ⟨hns, hnu⟩
      let S' := insert (i, r) S
      have hS'mem : S' ∈ Cons := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
          hWS.trans (Finset.subset_insert _ _), ?_⟩
        intro u hu v hv hreach
        simp only [S', Finset.mem_insert] at hu hv
        rcases hu with rfl | hu
        · rcases hv with rfl | hv
          · exact hns hreach
          · exact hnu v hv (by simpa [negLit_negLit] using BReach_contra hreach)
        · rcases hv with rfl | hv
          · exact hnu u hu hreach
          · exact hScons u hu v hv hreach
      have hle := hSmax S' hS'mem
      have hgt : S.card < S'.card := by
        simp only [S', Finset.card_insert_of_notMem hr]; omega
      omega
    rcases hbad true ht with htf | ⟨u, hu, hut⟩
    · rcases hbad false hf with hft | ⟨v, hv, hvf⟩
      · exact hnoSelf (i, true) ⟨htf, hft⟩
      · have hv_to_f : BReach HB v (negLit (i, true)) :=
          Relation.ReflTransGen.trans hvf htf
        have ht_to_nv : BReach HB (i, true) (negLit v) := by
          simpa [negLit_negLit] using BReach_contra hv_to_f
        exact hScons v hv v hv (Relation.ReflTransGen.trans hvf ht_to_nv)
    · rcases hbad false hf with hft | ⟨v, hv, hvf⟩
      · have hu_to_t : BReach HB u (negLit (i, false)) :=
          Relation.ReflTransGen.trans hut hft
        have hf_to_nu : BReach HB (i, false) (negLit u) := by
          simpa [negLit_negLit] using BReach_contra hu_to_t
        exact hScons u hu u hu (Relation.ReflTransGen.trans hut hf_to_nu)
      · have hf_to_nv : BReach HB (i, false) (negLit v) := by
          simpa [negLit_negLit] using BReach_contra hvf
        exact hScons u hu v hv (Relation.ReflTransGen.trans hut hf_to_nv)
  have hnot_both : ∀ i : Fin b, ¬((i, false) ∈ S ∧ (i, true) ∈ S) := by
    intro i ⟨hf, ht⟩
    exact hScons (i, false) hf (i, true) ht Relation.ReflTransGen.refl
  let h : Fin b → Bool := fun i => decide ((i, true) ∈ S)
  have hiff : ∀ l : Lit b, h l.1 = l.2 ↔ l ∈ S := by
    intro ⟨i, r⟩
    cases r
    · simp only [h, decide_eq_false_iff_not]
      constructor
      · intro hnt; exact (hcov i).resolve_right hnt
      · intro hf ht; exact hnot_both i ⟨hf, ht⟩
    · simp only [h, decide_eq_true_eq]
  refine ⟨h, holds_of_BEdge_closed h2 ?_, fun u hu => (hiff u).mpr (hWS hu)⟩
  intro x y hedge hx
  rw [hiff] at hx ⊢
  by_contra hy
  have hny : negLit y ∈ S := by
    rcases y with ⟨i, r⟩
    cases r
    · exact (hcov i).resolve_left hy
    · exact (hcov i).resolve_right hy
  exact hScons x hx (negLit y) hny (by
    rw [negLit_negLit]; exact Relation.ReflTransGen.single hedge)

-- Part 4: Binary-only conflicts (HT = ∅)

def IsBPath {b : Nat} (HB : Finset (Hidden b)) : List (Lit b) → Prop
  | [] => False
  | [_] => True
  | x :: y :: t => BEdge HB x y ∧ IsBPath HB (y :: t)

def pathClauses {b : Nat} : List (Lit b) → Finset (Hidden b)
  | [] => ∅
  | [_] => ∅
  | x :: y :: t => insert ({negLit x, y} : Hidden b) (pathClauses (y :: t))

lemma pathClauses_sub {b : Nat} {HB : Finset (Hidden b)} {L : List (Lit b)}
    (hp : IsBPath HB L) : pathClauses L ⊆ HB := by
  match L with
  | [] => exact False.elim hp
  | [_] => exact Finset.empty_subset _
  | x :: y :: t =>
    simp only [pathClauses]
    exact Finset.insert_subset hp.1 (pathClauses_sub hp.2)

lemma pathClauses_card_le {b : Nat} (L : List (Lit b)) :
    (pathClauses L).card + 1 ≤ L.length ∨ L = [] := by
  match L with
  | [] => right; rfl
  | [_] => left; simp [pathClauses]
  | x :: y :: t =>
    left
    have ih := pathClauses_card_le (y :: t)
    rcases ih with h | h
    · simp only [pathClauses, List.length_cons] at h ⊢
      have := Finset.card_insert_le ({negLit x, y} : Hidden b) (pathClauses (y :: t))
      omega
    · cases h

lemma IsBPath_reach_of_sub {b : Nat} {HB : Finset (Hidden b)} {L : List (Lit b)}
    (hp : IsBPath HB L) :
    ∀ i j : Nat, (hi : i ≤ j) → (hj : j < L.length) →
      BReach (pathClauses L) L[i] L[j] := by
  match L with
  | [] => exact False.elim hp
  | [x] =>
    intro i j hi hj
    simp only [List.length_singleton] at hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0; subst hj0
    exact Relation.ReflTransGen.refl
  | x :: y :: t =>
    intro i j hi hj
    cases i with
    | zero =>
      cases j with
      | zero => exact Relation.ReflTransGen.refl
      | succ j =>
        have hedge : BEdge (pathClauses (x :: y :: t)) x y := by
          simp [BEdge, pathClauses]
        have htail := IsBPath_reach_of_sub hp.2 0 j (Nat.zero_le j) (by simpa using hj)
        have hmono := BReach_mono (Finset.subset_insert ({negLit x, y} : Hidden b) _) htail
        exact Relation.ReflTransGen.head hedge hmono
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have htail := IsBPath_reach_of_sub hp.2 i j (by omega) (by simpa using hj)
        exact BReach_mono (Finset.subset_insert ({negLit x, y} : Hidden b) _) htail

lemma isBPath_append_singleton {b : Nat} {HB : Finset (Hidden b)} {L : List (Lit b)}
    {u v : Lit b} (hp : IsBPath HB L) (hl : L.getLast? = some u) (he : BEdge HB u v) :
    IsBPath HB (L ++ [v]) := by
  induction L with
  | nil => exact False.elim hp
  | cons a t ih =>
    cases t with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact ⟨he, trivial⟩
    | cons c ts =>
      exact ⟨hp.1, ih hp.2 (by simpa using hl)⟩

lemma exists_isBPath_of_BReach {b : Nat} {HB : Finset (Hidden b)} {x y : Lit b}
    (hr : BReach HB x y) :
    ∃ L : List (Lit b), IsBPath HB L ∧ L.head? = some x ∧ L.getLast? = some y := by
  induction hr with
  | refl => exact ⟨[x], trivial, rfl, rfl⟩
  | @tail u v _ he ih =>
    rcases ih with ⟨L, hp, hh, hl⟩
    refine ⟨L ++ [v], isBPath_append_singleton hp hl he, ?_, by simp⟩
    cases L with
    | nil => cases hh
    | cons a _ => simpa using hh

lemma isBPath_drop {b : Nat} {HB : Finset (Hidden b)} (L : List (Lit b)) (k : Nat)
    (hp : IsBPath HB L) (hk : k < L.length) : IsBPath HB (L.drop k) := by
  induction L generalizing k with
  | nil => exact False.elim hp
  | cons z ts ih =>
    cases k with
    | zero => exact hp
    | succ k =>
      cases ts with
      | nil => simp at hk
      | cons z2 ts2 => exact ih k hp.2 (by simpa using hk)

lemma isBPath_shortcut {b : Nat} {HB : Finset (Hidden b)} (M : List (Lit b)) (p q : Nat)
    (hpM : IsBPath HB M) (hpq : p < q) (hq : q < M.length) (hMq : M[p]'(by omega) = M[q]) :
    ∃ M' : List (Lit b), M'.length < M.length ∧ IsBPath HB M' ∧
      M'.head? = M.head? ∧ M'.getLast? = M.getLast? := by
  induction M generalizing p q with
  | nil => exact False.elim hpM
  | cons u t ih =>
    cases p with
    | zero =>
      simp only [List.length_cons] at hq
      refine ⟨(u :: t).drop q, by simp; omega, isBPath_drop (u :: t) q hpM (by simp; omega), ?_, ?_⟩
      · rw [List.head?_drop, List.getElem?_eq_getElem (by simp; omega)]
        simpa using hMq.symm
      · rw [List.getLast?_drop, ite_eq_right (by simp; omega)]
    | succ p =>
      cases q with
      | zero => omega
      | succ q =>
        cases t with
        | nil => simp at hq
        | cons v ts =>
          obtain ⟨M', hM'len, hM'p, hM'h, hM'l⟩ :=
            ih p q hpM.2 (by omega) (by simpa using hq) (by simpa using hMq)
          cases M' with
          | nil => exact False.elim hM'p
          | cons w ws =>
            simp only [List.head?_cons, Option.some.injEq] at hM'h
            subst hM'h
            refine ⟨u :: w :: ws, by simpa using hM'len, ⟨hpM.1, hM'p⟩, rfl, ?_⟩
            simpa using hM'l

lemma exists_shortest_BPath {b : Nat} {HB : Finset (Hidden b)} {x y : Lit b}
    (hr : BReach HB x y) :
    ∃ L : List (Lit b), IsBPath HB L ∧ L.head? = some x ∧ L.getLast? = some y ∧
      L.Nodup := by
  classical
  have hex : ∃ n, ∃ L : List (Lit b),
      L.length = n ∧ IsBPath HB L ∧ L.head? = some x ∧ L.getLast? = some y := by
    obtain ⟨L, hp, hh, hl⟩ := exists_isBPath_of_BReach hr
    exact ⟨L.length, L, rfl, hp, hh, hl⟩
  obtain ⟨L, hlen, hp, hh, hl⟩ := Nat.find_spec hex
  have hmin : ∀ L' : List (Lit b),
      IsBPath HB L' → L'.head? = some x → L'.getLast? = some y → L.length ≤ L'.length := by
    intro L' hp' hh' hl'
    rw [hlen]
    exact Nat.find_min' hex ⟨L', rfl, hp', hh', hl'⟩
  refine ⟨L, hp, hh, hl, ?_⟩
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  by_contra hne
  have hlt : i.val < j.val ∨ j.val < i.val := Nat.lt_or_gt.mp (fun h => hne (Fin.ext h))
  have hcut : ∀ (a c : Fin L.length), a.val < c.val → L[a.val] = L[c.val] → False := by
    intro a c hac heq
    obtain ⟨M', hM'len, hM'p, hM'h, hM'l⟩ := isBPath_shortcut L a.val c.val hp hac c.isLt heq
    have := hmin M' hM'p (hM'h.trans hh) (hM'l.trans hl)
    omega
  rcases hlt with h | h
  · exact hcut i j h hij
  · exact hcut j i h hij.symm

lemma prefix_isBPath {b : Nat} {HB : Finset (Hidden b)} {L : List (Lit b)}
    (hp : IsBPath HB L) (k : Nat) (hk : 1 ≤ k) (hkl : k ≤ L.length) :
    IsBPath HB (L.take k) := by
  induction L generalizing k with
  | nil => exact False.elim hp
  | cons x t ih =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => trivial
      | succ k =>
        cases t with
        | nil => simp at hkl
        | cons y ts =>
          exact ⟨hp.1, ih hp.2 (k + 1) (by omega) (by simpa using hkl)⟩

lemma getLast_eq_getElem {α : Type*} {L : List α} {y : α} (hl : L.getLast? = some y)
    (hlen : 0 < L.length) : L[L.length - 1]'(by omega) = y := by
  have h1 : L.getLast? = L[L.length - 1]? := List.getLast?_eq_getElem?
  rw [hl, List.getElem?_eq_getElem (by omega)] at h1
  exact (Option.some.inj h1).symm

lemma pair_conflict_clauses {b : Nat} {HB : Finset (Hidden b)} {u v : Lit b}
    (hr : BReach HB u (negLit v)) :
    (∃ HB' ⊆ HB, HB'.card ≤ b ∧ BReach HB' u (negLit u)) ∨
    (∃ HB' ⊆ HB, HB'.card + 1 ≤ b ∧ BReach HB' u (negLit v)) := by
  obtain ⟨L, hp, hh, hl, hnd⟩ := exists_shortest_BPath hr
  have hlen_pos : 0 < L.length := by
    cases L with
    | nil => exact False.elim hp
    | cons _ _ => simp
  have hhead : L[0]'hlen_pos = u := by
    cases L with
    | nil => exact False.elim hp
    | cons a _ => simpa using hh
  have hlast : L[L.length - 1]'(by omega) = negLit v := getLast_eq_getElem hl hlen_pos
  by_cases hcomp : ∃ r : Nat, ∃ hr : r < L.length, ∃ i : Nat, ∃ hi : i < r, L[r]'hr = negLit (L[i]'(by omega))
  · left
    classical
    let r := Nat.find hcomp
    obtain ⟨hrlt, i, hir, hreq⟩ := Nat.find_spec hcomp
    have hminr : ∀ r' < r, ∀ (hr' : r' < L.length) (i' : Nat) (hi' : i' < r'),
        L[r']'hr' ≠ negLit (L[i']'(by omega)) := by
      intro r' hr' hlt' i' hi' heq
      exact Nat.find_min hcomp hr' ⟨hlt', i', hi', heq⟩
    have hr_le_b : r ≤ b := by
      have hinj : Set.InjOn (fun k : Fin r => (L[k.val]'(by omega)).1)
          ↑(Finset.univ : Finset (Fin r)) := by
        intro k₁ _ k₂ _ heq
        by_contra hne
        have hlt : k₁.val < k₂.val ∨ k₂.val < k₁.val :=
          Nat.lt_or_gt.mp (fun h => hne (Fin.ext h))
        have hpair : ∀ a c : Fin r, a.val < c.val →
            (L[a.val]'(by omega)).1 = (L[c.val]'(by omega)).1 → False := by
          intro a c hac hfst
          have hne_lit : L[a.val]'(by omega) ≠ L[c.val]'(by omega) := by
            intro hlit
            have hinj' := List.nodup_iff_injective_getElem.mp hnd
            have hfe := congrArg Fin.val (@hinj' ⟨a.val, by omega⟩ ⟨c.val, by omega⟩ hlit)
            dsimp only at hfe
            omega
          have hneg : L[c.val]'(by omega) = negLit (L[a.val]'(by omega)) := by
            rcases hLa : L[a.val]'(by omega) with ⟨va, ra⟩
            rcases hLc : L[c.val]'(by omega) with ⟨vc, rc⟩
            rw [hLa, hLc] at hfst hne_lit
            simp only at hfst; subst hfst
            cases ra <;> cases rc <;> simp_all [negLit]
          exact hminr c.val c.isLt (by omega) a.val hac hneg
        rcases hlt with h | h
        · exact hpair k₁ k₂ h heq
        · exact hpair k₂ k₁ h heq.symm
      have hcard := Finset.card_le_card_of_injOn
        (fun k : Fin r => (L[k.val]'(by omega)).1)
        (fun _ _ => Finset.mem_univ _) hinj
      simpa using hcard
    let L' := L.take (r + 1)
    have hL'len : L'.length = r + 1 := by simp [L']; omega
    have hL'p : IsBPath HB L' := prefix_isBPath hp (r + 1) (by omega) (by omega)
    let HB' := pathClauses L'
    refine ⟨HB', pathClauses_sub hL'p, ?_, ?_⟩
    · rcases pathClauses_card_le L' with hc | he
      · have hHBc : HB'.card = (pathClauses L').card := rfl; omega
      · rw [he] at hL'len; simp at hL'len
    · have h0r : BReach HB' (L'[0]'(by omega)) (L'[r]'(by omega)) :=
        IsBPath_reach_of_sub hL'p 0 r (Nat.zero_le _) (by omega)
      have h0i : BReach HB' (L'[0]'(by omega)) (L'[i]'(by omega)) :=
        IsBPath_reach_of_sub hL'p 0 i (Nat.zero_le _) (by omega)
      have he0 : L'[0]'(by omega) = u := by simp [L', hhead]
      have her : L'[r]'(by omega) = negLit (L'[i]'(by omega)) := by
        simp only [L', List.getElem_take]
        exact hreq
      rw [he0] at h0r h0i
      rw [her] at h0r
      exact Relation.ReflTransGen.trans h0r (BReach_contra h0i)
  · right
    push Not at hcomp
    have hL_le_b : L.length ≤ b := by
      have hinj : Set.InjOn (fun k : Fin L.length => L[k.val].1)
          ↑(Finset.univ : Finset (Fin L.length)) := by
        intro k₁ _ k₂ _ heq
        by_contra hne
        have hlt : k₁.val < k₂.val ∨ k₂.val < k₁.val :=
          Nat.lt_or_gt.mp (fun h => hne (Fin.ext h))
        have hpair : ∀ a c : Fin L.length, a.val < c.val → L[a.val].1 = L[c.val].1 → False := by
          intro a c hac hfst
          have hne_lit : L[a.val] ≠ L[c.val] := by
            intro hlit
            have hinj' := List.nodup_iff_injective_getElem.mp hnd
            have hfe := congrArg Fin.val (@hinj' a c hlit)
            omega
          have hneg : L[c.val] = negLit L[a.val] := by
            rcases hLa : L[a.val] with ⟨va, ra⟩
            rcases hLc : L[c.val] with ⟨vc, rc⟩
            rw [hLa, hLc] at hfst hne_lit
            simp only at hfst; subst hfst
            cases ra <;> cases rc <;> simp_all [negLit]
          exact hcomp c.val c.isLt a.val hac hneg
        rcases hlt with h | h
        · exact hpair k₁ k₂ h heq
        · exact hpair k₂ k₁ h heq.symm
      have hcard := Finset.card_le_card_of_injOn (fun k : Fin L.length => L[k.val].1)
        (fun _ _ => Finset.mem_univ _) hinj
      simpa using hcard
    refine ⟨pathClauses L, pathClauses_sub hp, ?_, ?_⟩
    · rcases pathClauses_card_le L with hc | he
      · omega
      · subst he; exact False.elim hp
    · have h0 := IsBPath_reach_of_sub hp 0 (L.length - 1) (Nat.zero_le _) (by omega)
      rw [hhead, hlast] at h0
      exact h0

lemma self_conflict_clauses {b : Nat} {HB : Finset (Hidden b)} {u : Lit b}
    (hr : BReach HB u (negLit u)) :
    ∃ HB' ⊆ HB, HB'.card ≤ b ∧ BReach HB' u (negLit u) := by
  rcases pair_conflict_clauses hr with h | ⟨HB', hsub, hcard, hreach⟩
  · exact h
  · exact ⟨HB', hsub, by omega, hreach⟩

lemma binary_only_bound {b : Nat} (hb : 2 ≤ b)
    (HB : Finset (Hidden b)) (h2 : ∀ D ∈ HB, D.card = 2)
    (HU : Finset (Lit b))
    (hunsat : ¬∃ h : Fin b → Bool, (∀ D ∈ HB, holds D h) ∧ (∀ u ∈ HU, h u.1 = u.2))
    (hmin : ∀ HB' ⊆ HB, ∀ HU' ⊆ HU,
      (¬∃ h : Fin b → Bool, (∀ D ∈ HB', holds D h) ∧ (∀ u ∈ HU', h u.1 = u.2)) →
      HB' = HB ∧ HU' = HU) :
    HB.card + 2 * HU.card ≤ 2 * b + 2 := by
  by_cases hU : HU = ∅
  · subst hU
    have hex : ∃ x, BReach HB x (negLit x) ∧ BReach HB (negLit x) x := by
      by_contra hno
      push Not at hno
      obtain ⟨h, hh, _⟩ := krom_sat HB h2 ∅ (fun x ⟨h1, h2'⟩ => hno x h1 h2')
        (fun _ hu => False.elim (Finset.notMem_empty _ hu))
      exact hunsat ⟨h, hh, fun _ hu => False.elim (Finset.notMem_empty _ hu)⟩
    rcases hex with ⟨x, h1, h2'⟩
    obtain ⟨HB₁, hsub₁, hc₁, hr₁⟩ := self_conflict_clauses h1
    have h2'' : BReach HB (negLit x) (negLit (negLit x)) := by rwa [negLit_negLit]
    obtain ⟨HB₂, hsub₂, hc₂, hr₂⟩ := self_conflict_clauses h2''
    have hsub : HB₁ ∪ HB₂ ⊆ HB := Finset.union_subset hsub₁ hsub₂
    have huns : ¬∃ h : Fin b → Bool, (∀ D ∈ HB₁ ∪ HB₂, holds D h) ∧
        (∀ u ∈ (∅ : Finset (Lit b)), h u.1 = u.2) := by
      rintro ⟨h, hh, _⟩
      have hr₁' : BReach (HB₁ ∪ HB₂) x (negLit x) := BReach_mono Finset.subset_union_left hr₁
      have hr₂' : BReach (HB₁ ∪ HB₂) (negLit x) x := by
        simpa [negLit_negLit] using BReach_mono Finset.subset_union_right hr₂
      by_cases hx : h x.1 = x.2
      · have hnx := BReach_sound hh hr₁' hx
        simp only [negLit] at hnx; rw [hx] at hnx
        exact bool_eq_not_false hnx
      · exact hx (BReach_sound hh hr₂' (negLit_true_of_ne hx))
    have heq := (hmin (HB₁ ∪ HB₂) hsub ∅ (Finset.Subset.refl _) huns).1
    have hc : HB.card ≤ HB₁.card + HB₂.card := by
      rw [← heq]; exact Finset.card_union_le _ _
    simp only [Finset.card_empty]
    omega
  · obtain ⟨u₀, hu₀⟩ := Finset.nonempty_iff_ne_empty.mpr hU
    have hsat_er : ∃ h : Fin b → Bool, (∀ D ∈ HB, holds D h) ∧
        (∀ u ∈ HU.erase u₀, h u.1 = u.2) := by
      by_contra hno
      have heq := (hmin HB (Finset.Subset.refl _) (HU.erase u₀) (Finset.erase_subset _ _) hno).2
      have : u₀ ∈ HU.erase u₀ := by rw [heq]; exact hu₀
      exact Finset.notMem_erase u₀ HU this
    obtain ⟨h0, h0B, _⟩ := hsat_er
    have hnoSelf : ∀ x, ¬(BReach HB x (negLit x) ∧ BReach HB (negLit x) x) := by
      intro x ⟨h1, h2'⟩
      by_cases hx : h0 x.1 = x.2
      · have hnx := BReach_sound h0B h1 hx
        simp only [negLit] at hnx; rw [hx] at hnx
        exact bool_eq_not_false hnx
      · exact hx (BReach_sound h0B h2' (negLit_true_of_ne hx))
    have hex : ∃ u ∈ HU, ∃ v ∈ HU, BReach HB u (negLit v) := by
      by_contra hno
      push Not at hno
      exact hunsat (krom_sat HB h2 HU hnoSelf hno)
    rcases hex with ⟨u, hu, v, hv, huv⟩
    rcases pair_conflict_clauses huv with ⟨HB', hsub, hcard, hself⟩ | ⟨HB', hsub, hcard, hpair⟩
    · have huns : ¬∃ h : Fin b → Bool, (∀ D ∈ HB', holds D h) ∧
          (∀ w ∈ ({u} : Finset (Lit b)), h w.1 = w.2) := by
        rintro ⟨h, hB', hU'⟩
        have hhu : h u.1 = u.2 := hU' u (Finset.mem_singleton_self u)
        have hnu := BReach_sound hB' hself hhu
        simp only [negLit] at hnu; rw [hhu] at hnu
        exact bool_eq_not_false hnu
      have ⟨heqB, heqU⟩ := hmin HB' hsub {u} (Finset.singleton_subset_iff.mpr hu) huns
      rw [← heqB, ← heqU, Finset.card_singleton]
      omega
    · have huns : ¬∃ h : Fin b → Bool, (∀ D ∈ HB', holds D h) ∧
          (∀ w ∈ ({u, v} : Finset (Lit b)), h w.1 = w.2) := by
        rintro ⟨h, hB', hU'⟩
        have hhu : h u.1 = u.2 := hU' u (by simp)
        have hhv : h v.1 = v.2 := hU' v (by simp)
        have hnv := BReach_sound hB' hpair hhu
        simp only [negLit] at hnv; rw [hhv] at hnv
        exact bool_eq_not_false hnv
      have hUsub : ({u, v} : Finset (Lit b)) ⊆ HU := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      have ⟨heqB, heqU⟩ := hmin HB' hsub {u, v} hUsub huns
      have hUcard : HU.card ≤ 2 := by
        rw [← heqU]; exact (Finset.card_insert_le _ _).trans (by simp)
      rw [← heqB]
      omega

-- Part 5: SCCs, Quotient DAG, Consistent Paths, Charging

noncomputable def sccOf {b : Nat} (HB : Finset (Hidden b)) (x : Lit b) : Finset (Lit b) :=
  letI := Classical.decPred (fun y : Lit b => BReach HB x y ∧ BReach HB y x)
  Finset.univ.filter (fun y => BReach HB x y ∧ BReach HB y x)

def negSCC {b : Nat} (S : Finset (Lit b)) : Finset (Lit b) :=
  S.image negLit

def sccCode {b : Nat} (S : Finset (Lit b)) : Nat :=
  if h : S.Nonempty then (S.image litCode).min' (h.image litCode) else 0

lemma mem_sccOf {b : Nat} {HB : Finset (Hidden b)} {x y : Lit b} :
    y ∈ sccOf HB x ↔ BReach HB x y ∧ BReach HB y x := by
  classical
  simp [sccOf]

lemma mem_sccOf_self {b : Nat} (HB : Finset (Hidden b)) (x : Lit b) :
    x ∈ sccOf HB x :=
  mem_sccOf.mpr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

lemma sccOf_eq_of_mem {b : Nat} {HB : Finset (Hidden b)} {x y : Lit b}
    (h : y ∈ sccOf HB x) : sccOf HB y = sccOf HB x := by
  have ⟨hxy, hyx⟩ := mem_sccOf.mp h
  ext z
  simp only [mem_sccOf]
  exact ⟨fun ⟨hyz, hzy⟩ => ⟨Relation.ReflTransGen.trans hxy hyz, Relation.ReflTransGen.trans hzy hyx⟩,
         fun ⟨hxz, hzx⟩ => ⟨Relation.ReflTransGen.trans hyx hxz, Relation.ReflTransGen.trans hzx hxy⟩⟩

lemma negSCC_negSCC {b : Nat} (S : Finset (Lit b)) : negSCC (negSCC S) = S := by
  ext x
  simp only [negSCC, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩; simpa [negLit_negLit] using hz
  · intro hx; exact ⟨negLit x, ⟨x, hx, rfl⟩, negLit_negLit x⟩

lemma negSCC_card {b : Nat} (S : Finset (Lit b)) : (negSCC S).card = S.card :=
  Finset.card_image_of_injective S negLit_inj

lemma sccOf_negLit {b : Nat} (HB : Finset (Hidden b)) (x : Lit b) :
    sccOf HB (negLit x) = negSCC (sccOf HB x) := by
  ext y
  simp only [mem_sccOf, negSCC, Finset.mem_image]
  constructor
  · intro ⟨h1, h2⟩
    refine ⟨negLit y, ⟨?_, ?_⟩, negLit_negLit y⟩
    · simpa [negLit_negLit] using BReach_contra h2
    · simpa [negLit_negLit] using BReach_contra h1
  · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
    exact ⟨BReach_contra h2, BReach_contra h1⟩

lemma sccCode_inj_on_disjoint {b : Nat} {S₁ S₂ : Finset (Lit b)}
    (h1 : S₁.Nonempty) (h2 : S₂.Nonempty)
    (hdisj : S₁ ≠ S₂ → Disjoint S₁ S₂)
    (heq : sccCode S₁ = sccCode S₂) : S₁ = S₂ := by
  by_contra hne
  simp only [sccCode, dite_eq_left h1,
             dite_eq_left h2] at heq
  have hm1 : (S₁.image litCode).min' (h1.image litCode) ∈ S₁.image litCode :=
    Finset.min'_mem _ _
  have hm2 : (S₂.image litCode).min' (h2.image litCode) ∈ S₂.image litCode :=
    Finset.min'_mem _ _
  rw [heq] at hm1
  rcases Finset.mem_image.mp hm1 with ⟨x₁, hx₁, hcx₁⟩
  rcases Finset.mem_image.mp hm2 with ⟨x₂, hx₂, hcx₂⟩
  have hx : x₁ = x₂ := litCode_inj (hcx₁.trans hcx₂.symm)
  subst hx
  exact Finset.disjoint_left.mp (hdisj hne) hx₁ hx₂

lemma isBPath_last_edge {b : Nat} {HB : Finset (Hidden b)} (M : List (Lit b))
    (hpM : IsBPath HB M) (h2 : 2 ≤ M.length) :
    BEdge HB (M[M.length - 2]'(by omega)) (M[M.length - 1]'(by omega)) := by
  induction M with
  | nil => exact False.elim hpM
  | cons a t ih =>
    cases t with
    | nil => simp at h2
    | cons c ts =>
      cases ts with
      | nil => exact hpM.1
      | cons d ts2 => exact ih hpM.2 (by simp)

lemma scc_out_clauses {b : Nat} (HB : Finset (Hidden b)) (r : Lit b) :
    ∃ B_out ⊆ HB, B_out.card + 1 ≤ (sccOf HB r).card ∧
      ∀ v ∈ sccOf HB r, BReach B_out r v := by
  classical
  let S := sccOf HB r
  have hrS : r ∈ S := mem_sccOf_self HB r
  have hexLen : ∀ v ∈ S, ∃ n, ∃ L : List (Lit b),
      L.length = n ∧ IsBPath HB L ∧ L.head? = some r ∧ L.getLast? = some v := by
    intro v hv
    obtain ⟨L, hp, hh, hl⟩ := exists_isBPath_of_BReach (mem_sccOf.mp hv).1
    exact ⟨L.length, L, rfl, hp, hh, hl⟩
  let dist : Lit b → Nat := fun v =>
    if hv : v ∈ S then Nat.find (hexLen v hv) else 0
  have hpred : ∀ v ∈ S.erase r, ∃ u ∈ S, BEdge HB u v ∧ dist u < dist v := by
    intro v hv
    have hvS : v ∈ S := (Finset.mem_erase.mp hv).2
    have hvr : v ≠ r := (Finset.mem_erase.mp hv).1
    obtain ⟨L, hlen, hp, hh, hl⟩ := Nat.find_spec (hexLen v hvS)
    have hlen_ge2 : 2 ≤ L.length := by
      match L with
      | [] => exact False.elim hp
      | [a] =>
        simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hh hl
        exact absurd (hl.symm.trans hh) hvr
      | _ :: _ :: _ => simp
    let u := L[L.length - 2]'(by omega)
    have hLpre : IsBPath HB (L.take (L.length - 1)) :=
      prefix_isBPath hp (L.length - 1) (by omega) (by omega)
    have hpre_len : (L.take (L.length - 1)).length = L.length - 1 := by
      rw [List.length_take]; omega
    have hpre_head : (L.take (L.length - 1)).head? = some r := by
      cases L with
      | nil => exact False.elim hp
      | cons a t =>
        cases hlen1 : (a :: t).length - 1 with
        | zero => simp only [List.length_cons] at hlen_ge2 hlen1; omega
        | succ k => simpa [List.take_succ_cons] using hh
    have hpre_last : (L.take (L.length - 1)).getLast? = some u := by
      have hgl : (L.take (L.length - 1)).getLast? =
          (L.take (L.length - 1))[(L.take (L.length - 1)).length - 1]? := List.getLast?_eq_getElem?
      rw [hgl, hpre_len, List.getElem?_eq_getElem (by rw [hpre_len]; omega), List.getElem_take]
      rfl
    have hedge : BEdge HB u v := by
      have h1 := isBPath_last_edge L hp hlen_ge2
      have hv_eq : L[L.length - 1]'(by omega) = v := getLast_eq_getElem hl (by omega)
      rw [hv_eq] at h1
      exact h1
    have huS : u ∈ S := by
      have hru : BReach HB r u := by
        have h0 := IsBPath_reach_of_sub hLpre 0 (L.length - 2) (Nat.zero_le _) (by rw [hpre_len]; omega)
        have h0eq : (L.take (L.length - 1))[0]'(by rw [hpre_len]; omega) = r := by
          rw [List.getElem_take]
          cases L with
          | nil => exact False.elim hp
          | cons a _ => simpa using hh
        have hueq : (L.take (L.length - 1))[L.length - 2]'(by rw [hpre_len]; omega) = u := by
          rw [List.getElem_take]
        rw [h0eq, hueq] at h0
        exact BReach_mono (pathClauses_sub hLpre) h0
      have hur : BReach HB u r :=
        Relation.ReflTransGen.head hedge (mem_sccOf.mp hvS).2
      exact mem_sccOf.mpr ⟨hru, hur⟩
    have hdu : dist u < dist v := by
      simp only [dist, dite_eq_left huS,
                 dite_eq_left hvS]
      have hle : Nat.find (hexLen u huS) ≤ (L.take (L.length - 1)).length :=
        Nat.find_min' (hexLen u huS) ⟨L.take (L.length - 1), rfl, hLpre, hpre_head, hpre_last⟩
      omega
    exact ⟨u, huS, hedge, hdu⟩
  let pred : Lit b → Lit b := fun v =>
    if hv : v ∈ S.erase r then Classical.choose (hpred v hv) else r
  let B_out : Finset (Hidden b) := (S.erase r).image (fun v => ({negLit (pred v), v} : Hidden b))
  refine ⟨B_out, ?_, ?_, ?_⟩
  · intro D hD
    rcases Finset.mem_image.mp hD with ⟨v, hv, rfl⟩
    simp only [pred, dite_eq_left hv]
    exact (Classical.choose_spec (hpred v hv)).2.1
  · calc B_out.card + 1 ≤ (S.erase r).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ = S.card := by rw [Finset.card_erase_of_mem hrS]; have := Finset.card_pos.mpr ⟨r, hrS⟩; omega
  · have hstrong : ∀ d : Nat, ∀ v ∈ S, dist v = d → BReach B_out r v := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro v hv hd
        by_cases hvr : v = r
        · subst hvr; exact Relation.ReflTransGen.refl
        · have hve : v ∈ S.erase r := Finset.mem_erase.mpr ⟨hvr, hv⟩
          have hspec := Classical.choose_spec (hpred v hve)
          have huS : pred v ∈ S := by
            simp only [pred, dite_eq_left hve]; exact hspec.1
          have hdu : dist (pred v) < d := by
            rw [← hd]; simp only [pred, dite_eq_left hve]
            exact hspec.2.2
          have hreach_u := ih (dist (pred v)) hdu (pred v) huS rfl
          have hedge : BEdge B_out (pred v) v := Finset.mem_image.mpr ⟨v, hve, rfl⟩
          exact Relation.ReflTransGen.tail hreach_u hedge
    intro v hv
    exact hstrong (dist v) v hv rfl

lemma scc_in_clauses {b : Nat} (HB : Finset (Hidden b)) (r : Lit b) :
    ∃ B_in ⊆ HB, B_in.card + 1 ≤ (sccOf HB r).card ∧
      ∀ v ∈ sccOf HB r, BReach B_in v r := by
  obtain ⟨B_out, hsub, hcard, hreach⟩ := scc_out_clauses HB (negLit r)
  refine ⟨B_out, hsub, ?_, ?_⟩
  · rw [sccOf_negLit, negSCC_card] at hcard; exact hcard
  · intro v hv
    have hnv : negLit v ∈ sccOf HB (negLit r) := by
      rw [sccOf_negLit]; exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    simpa [negLit_negLit] using BReach_contra (hreach (negLit v) hnv)

-- Consistent canonical paths on a finite DAG

def listEdges {α : Type*} [DecidableEq α] : List α → Finset (α × α)
  | [] => ∅
  | [_] => ∅
  | a :: b :: t => insert (a, b) (listEdges (b :: t))

lemma mem_listEdges_mem_left {α : Type*} [DecidableEq α] {L : List α} {x y : α}
    (h : (x, y) ∈ listEdges L) : x ∈ L := by
  match L with
  | [] => exact False.elim (Finset.notMem_empty _ h)
  | [_] => exact False.elim (Finset.notMem_empty _ h)
  | a :: b :: t =>
    simp only [listEdges, Finset.mem_insert, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h'
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_listEdges_mem_left h')

lemma mem_listEdges_mem_right {α : Type*} [DecidableEq α] {L : List α} {x y : α}
    (h : (x, y) ∈ listEdges L) : y ∈ L := by
  match L with
  | [] => exact False.elim (Finset.notMem_empty _ h)
  | [_] => exact False.elim (Finset.notMem_empty _ h)
  | a :: b :: t =>
    simp only [listEdges, Finset.mem_insert, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩ | h'
    · exact List.mem_cons_of_mem a List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_listEdges_mem_right h')

noncomputable def dagPath {α : Type*} (QReach : α → α → Prop) (nextHop : α → α → α) :
    Nat → α → α → List α
  | 0, S, _ => [S]
  | k + 1, S, T =>
    letI := Classical.dec (QReach S T ∧ S ≠ T)
    if QReach S T ∧ S ≠ T then
      S :: dagPath QReach nextHop k (nextHop S T) T
    else [S]

lemma dagPath_head {α : Type*} (QReach : α → α → Prop) (nextHop : α → α → α)
    (k : Nat) (S T : α) : ∃ t, dagPath QReach nextHop k S T = S :: t := by
  cases k with
  | zero => exact ⟨[], rfl⟩
  | succ k =>
    unfold dagPath
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨[], rfl⟩

lemma reflTransGen_mono_rel {α : Type*} {R₁ R₂ : α → α → Prop}
    (hsub : ∀ a b, R₁ a b → R₂ a b) {x y : α}
    (hr : Relation.ReflTransGen R₁ x y) : Relation.ReflTransGen R₂ x y := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ he ih => exact Relation.ReflTransGen.tail ih (hsub _ _ he)

lemma dag_charging_bound {b : Nat} (Q : Finset (Finset (Lit b)))
    (QEdge : Finset (Lit b) → Finset (Lit b) → Prop)
    (hQne : ∀ S ∈ Q, S.Nonempty)
    (hQdisj : ∀ S₁ ∈ Q, ∀ S₂ ∈ Q, S₁ ≠ S₂ → Disjoint S₁ S₂)
    (hQEdge_mem : ∀ S T, QEdge S T → S ∈ Q ∧ T ∈ Q ∧ S ≠ T)
    (hacyc : ∀ S T, Relation.ReflTransGen QEdge S T → Relation.ReflTransGen QEdge T S → S = T)
    {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (src dst : ι → Finset (Lit b))
    (hsrc : ∀ i ∈ I, src i ∈ Q) (hdst : ∀ i ∈ I, dst i ∈ Q)
    (hreach : ∀ i ∈ I, Relation.ReflTransGen QEdge (src i) (dst i))
    (Qzero : Finset (Finset (Lit b))) (hQzero_sub : Qzero ⊆ Q)
    (hQzero_avoid : ∀ i ∈ I, ∀ S ∈ Qzero, ¬Relation.ReflTransGen QEdge (src i) S) :
    ∃ E : Finset (Finset (Lit b) × Finset (Lit b)),
      (∀ e ∈ E, QEdge e.1 e.2) ∧
      (∀ i ∈ I, Relation.ReflTransGen (fun A B => (A, B) ∈ E) (src i) (dst i)) ∧
      E.card + Qzero.card ≤ Q.card + Nat.choose I.card 2 := by
  classical
  let QReach := Relation.ReflTransGen QEdge
  let reachSet : Finset (Lit b) → Finset (Finset (Lit b)) := fun S =>
    Q.filter (fun W => QReach S W)
  have hreachSet_lt : ∀ S U, QEdge S U → (reachSet U).card < (reachSet S).card := by
    intro S U hSU
    have ⟨hSQ, _, hne⟩ := hQEdge_mem S U hSU
    refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩)
    · intro W hW
      have ⟨hWQ, hUW⟩ := Finset.mem_filter.mp hW
      exact Finset.mem_filter.mpr ⟨hWQ, Relation.ReflTransGen.head hSU hUW⟩
    · intro heq
      have hSmem : S ∈ reachSet S := Finset.mem_filter.mpr ⟨hSQ, Relation.ReflTransGen.refl⟩
      rw [← heq] at hSmem
      exact hne (hacyc S U (Relation.ReflTransGen.single hSU) (Finset.mem_filter.mp hSmem).2)
  let cands : Finset (Lit b) → Finset (Lit b) → Finset (Finset (Lit b)) := fun S T =>
    Q.filter (fun U => QEdge S U ∧ QReach U T)
  have hcands_ne : ∀ S T, QReach S T → S ≠ T → (cands S T).Nonempty := by
    intro S T hST hne
    rcases Relation.ReflTransGen.cases_head hST with rfl | ⟨U, hSU, hUT⟩
    · exact False.elim (hne rfl)
    · exact ⟨U, Finset.mem_filter.mpr ⟨(hQEdge_mem S U hSU).2.1, hSU, hUT⟩⟩
  let nextHop : Finset (Lit b) → Finset (Lit b) → Finset (Lit b) := fun S T =>
    if h : (cands S T).Nonempty then
      Classical.choose (Finset.exists_min_image (cands S T) sccCode h)
    else S
  have hnextHop_spec : ∀ S T, QReach S T → S ≠ T →
      QEdge S (nextHop S T) ∧ QReach (nextHop S T) T ∧
      ∀ U, QEdge S U → QReach U T → sccCode (nextHop S T) ≤ sccCode U := by
    intro S T hST hne
    have hcn := hcands_ne S T hST hne
    have hsp := Classical.choose_spec (Finset.exists_min_image (cands S T) sccCode hcn)
    simp only [nextHop, dite_eq_left hcn]
    refine ⟨(Finset.mem_filter.mp hsp.1).2.1, (Finset.mem_filter.mp hsp.1).2.2, ?_⟩
    intro U hSU hUT
    exact hsp.2 U (Finset.mem_filter.mpr ⟨(hQEdge_mem S U hSU).2.1, hSU, hUT⟩)
  let go := dagPath QReach nextHop
  have hgo_props : ∀ k S T, (reachSet S).card ≤ k → S ∈ Q → T ∈ Q → QReach S T →
      (∀ e ∈ listEdges (go k S T), QEdge e.1 e.2 ∧ e.2 = nextHop e.1 T) ∧
      (∀ W ∈ go k S T, W ∈ Q ∧ QReach S W ∧ QReach W T) ∧
      (S ∈ go k S T ∧ T ∈ go k S T) ∧
      (Relation.ReflTransGen (fun A B => (A, B) ∈ listEdges (go k S T)) S T) ∧
      (∀ X₁ X₂ V, (X₁, V) ∈ listEdges (go k S T) → (X₂, V) ∈ listEdges (go k S T) → X₁ = X₂) ∧
      (∀ Z V, Z ∈ go k S T → V ∈ go k S T → QReach Z V → Z ≠ V →
        (Z, nextHop Z T) ∈ listEdges (go k S T) ∧ nextHop Z T ∈ go k S T ∧
        QReach (nextHop Z T) V) := by
    intro k
    induction k with
    | zero =>
      intro S T hle hSQ _ _
      have hpos : 1 ≤ (reachSet S).card :=
        Finset.card_pos.mpr ⟨S, Finset.mem_filter.mpr ⟨hSQ, Relation.ReflTransGen.refl⟩⟩
      omega
    | succ k ih =>
      intro S T hle hSQ hTQ hST
      by_cases hne : S = T
      · subst hne
        have hgo : go (k + 1) S S = [S] := by
          show dagPath QReach nextHop (k + 1) S S = [S]
          unfold dagPath; simp
        rw [hgo]
        refine ⟨fun e he => False.elim (Finset.notMem_empty _ he), ?_, ?_, ?_, ?_, ?_⟩
        · intro W hW
          simp only [List.mem_singleton] at hW; subst hW
          exact ⟨hSQ, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
        · simp
        · exact Relation.ReflTransGen.refl
        · intro _ _ _ h; exact False.elim (Finset.notMem_empty _ h)
        · intro Z V hZ hV _ hne
          simp only [List.mem_singleton] at hZ hV; exact False.elim (hne (hZ.trans hV.symm))
      · have hgo : go (k + 1) S T = S :: go k (nextHop S T) T := by
          show dagPath QReach nextHop (k + 1) S T = S :: dagPath QReach nextHop k (nextHop S T) T
          conv_lhs => unfold dagPath
          exact ite_eq_left (And.intro hST hne)
        set U := nextHop S T
        have ⟨hSU, hUT, _⟩ := hnextHop_spec S T hST hne
        have hUQ : U ∈ Q := (hQEdge_mem S U hSU).2.1
        have hlt : (reachSet U).card ≤ k := by
          have := hreachSet_lt S U hSU; omega
        have ⟨hE, hMem, ⟨hUin, hTin⟩, hR, hUniq, hStep⟩ := ih U T hlt hUQ hTQ hUT
        have hlistEdges : listEdges (go (k + 1) S T) = insert (S, U) (listEdges (go k U T)) := by
          rw [hgo]
          obtain ⟨t, ht⟩ := dagPath_head QReach nextHop k U T
          change go k U T = U :: t at ht
          rw [ht]
          rfl
        have hnot_in_tail : ∀ W ∈ go k U T, W ≠ S := by
          intro W hW hWS
          rw [hWS] at hW
          exact (hQEdge_mem S U hSU).2.2
            (hacyc S U (Relation.ReflTransGen.single hSU) (hMem S hW).2.1)
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e he
          rw [hlistEdges, Finset.mem_insert] at he
          rcases he with rfl | he'
          · exact ⟨hSU, rfl⟩
          · exact hE e he'
        · intro W hW
          rw [hgo, List.mem_cons] at hW
          rcases hW with rfl | hW'
          · exact ⟨hSQ, Relation.ReflTransGen.refl, hST⟩
          · have ⟨hWQ, hUW, hWT⟩ := hMem W hW'
            exact ⟨hWQ, Relation.ReflTransGen.head hSU hUW, hWT⟩
        · rw [hgo]; exact ⟨List.mem_cons_self, List.mem_cons_of_mem S hTin⟩
        · rw [hlistEdges]
          refine Relation.ReflTransGen.head (Finset.mem_insert_self _ _) ?_
          exact reflTransGen_mono_rel (fun _ _ h => Finset.mem_insert_of_mem h) hR
        · intro X₁ X₂ V h1 h2
          rw [hlistEdges, Finset.mem_insert] at h1 h2
          have hVneU_of_tail : ∀ X, (X, U) ∈ listEdges (go k U T) → False := by
            intro X hXU
            have hXmem : X ∈ go k U T := mem_listEdges_mem_left hXU
            have hUX : QReach U X := (hMem X hXmem).2.1
            have hXU_e : QEdge X U := (hE (X, U) hXU).1
            exact (hQEdge_mem X U hXU_e).2.2 (hacyc X U (Relation.ReflTransGen.single hXU_e) hUX)
          rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
          · exact (Prod.mk.inj h1).1.trans (Prod.mk.inj h2).1.symm
          · rw [(Prod.mk.inj h1).2] at h2; exact False.elim (hVneU_of_tail X₂ h2)
          · rw [(Prod.mk.inj h2).2] at h1; exact False.elim (hVneU_of_tail X₁ h1)
          · exact hUniq X₁ X₂ V h1 h2
        · intro Z V hZ hV hZV hZneV
          rw [hgo, List.mem_cons] at hZ hV
          rcases hZ with hZS | hZ'
          · subst hZS
            rcases hV with hVS | hV'
            · exact False.elim (hZneV hVS.symm)
            · refine ⟨?_, ?_, (hMem V hV').2.1⟩
              · rw [hlistEdges]; exact Finset.mem_insert_self _ _
              · rw [hgo]; exact List.mem_cons_of_mem Z hUin
          · rcases hV with rfl | hV'
            · exact False.elim (hnot_in_tail Z hZ'
                (hacyc Z V hZV (Relation.ReflTransGen.head hSU (hMem Z hZ').2.1)))
            · have ⟨h1, h2, h3⟩ := hStep Z V hZ' hV' hZV hZneV
              refine ⟨?_, ?_, h3⟩
              · rw [hlistEdges]; exact Finset.mem_insert_of_mem h1
              · rw [hgo]; exact List.mem_cons_of_mem S h2
  let P : ι → List (Finset (Lit b)) := fun i => go Q.card (src i) (dst i)
  have hP : ∀ i ∈ I,
      (∀ e ∈ listEdges (P i), QEdge e.1 e.2 ∧ e.2 = nextHop e.1 (dst i)) ∧
      (∀ W ∈ P i, W ∈ Q ∧ QReach (src i) W ∧ QReach W (dst i)) ∧
      (src i ∈ P i ∧ dst i ∈ P i) ∧
      (Relation.ReflTransGen (fun A B => (A, B) ∈ listEdges (P i)) (src i) (dst i)) ∧
      (∀ X₁ X₂ V, (X₁, V) ∈ listEdges (P i) → (X₂, V) ∈ listEdges (P i) → X₁ = X₂) ∧
      (∀ Z V, Z ∈ P i → V ∈ P i → QReach Z V → Z ≠ V →
        (Z, nextHop Z (dst i)) ∈ listEdges (P i) ∧ nextHop Z (dst i) ∈ P i ∧
        QReach (nextHop Z (dst i)) V) := by
    intro i hi
    exact hgo_props Q.card (src i) (dst i) (Finset.card_le_card (Finset.filter_subset _ _))
      (hsrc i hi) (hdst i hi) (hreach i hi)
  have hfirst_shared : ∀ i ∈ I, ∀ j ∈ I, ∀ X₁ X₂ V,
      (X₁, V) ∈ listEdges (P i) → (X₂, V) ∈ listEdges (P j) → X₁ ≠ X₂ →
      ∀ Z, Z ∈ P i → Z ∈ P j → QReach V Z := by
    intro i hi j hj X₁ X₂ V h1 h2 hXne Z hZi hZj
    by_contra hnot
    have hV_i : V ∈ P i := mem_listEdges_mem_right h1
    have hV_j : V ∈ P j := mem_listEdges_mem_right h2
    have hZV : QReach Z V := by
      have hord : ∀ (L : List (Finset (Lit b))),
          (∀ e ∈ listEdges L, QEdge e.1 e.2) →
          ∀ A B, A ∈ L → B ∈ L → QReach A B ∨ QReach B A := by
        intro L
        induction L with
        | nil => intro _ _ _ hA; cases hA
        | cons a t ih =>
          intro hLe A B hA hB
          have hreach_all : ∀ (a' : Finset (Lit b)) (t' : List (Finset (Lit b))),
              (∀ e ∈ listEdges (a' :: t'), QEdge e.1 e.2) →
              ∀ W ∈ a' :: t', QReach a' W := by
            intro a' t'
            induction t' generalizing a' with
            | nil => intro _ W hW; simp at hW; subst hW; exact Relation.ReflTransGen.refl
            | cons c ts iht =>
              intro hLe0 W hW
              rcases List.mem_cons.mp hW with rfl | hW'
              · exact Relation.ReflTransGen.refl
              · have hac : QEdge a' c := hLe0 (a', c) (Finset.mem_insert_self _ _)
                have hLe' : ∀ e ∈ listEdges (c :: ts), QEdge e.1 e.2 :=
                  fun e he => hLe0 e (Finset.mem_insert_of_mem he)
                exact Relation.ReflTransGen.head hac (iht c hLe' W hW')
          rcases List.mem_cons.mp hA with hAa | hA'
          · subst hAa; exact Or.inl (hreach_all A t hLe B hB)
          · rcases List.mem_cons.mp hB with hBa | hB'
            · subst hBa; exact Or.inr (hreach_all B t hLe A hA)
            · exact ih (fun e he => hLe e (by
                cases t with
                | nil => exact False.elim (Finset.notMem_empty _ he)
                | cons _ _ => exact Finset.mem_insert_of_mem he)) A B hA' hB'
      rcases hord (P i) (fun e he => ((hP i hi).1 e he).1) Z V hZi hV_i with h | h
      · exact h
      · exact False.elim (hnot h)
    have hZneV : Z ≠ V := fun heq => hnot (heq ▸ Relation.ReflTransGen.refl)
    have hsame : ∀ k : Nat, ∀ W, (reachSet W).card = k →
        W ∈ P i → W ∈ P j → QReach W V → W ≠ V → X₁ = X₂ := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro W hWk hWi hWj hWV hWneV
        have ⟨hWU1e, hU1i, hU1V⟩ := (hP i hi).2.2.2.2.2 W V hWi hV_i hWV hWneV
        have ⟨hWU2e, hU2j, hU2V⟩ := (hP j hj).2.2.2.2.2 W V hWj hV_j hWV hWneV
        set U₁ := nextHop W (dst i)
        set U₂ := nextHop W (dst j)
        have hWU1 : QEdge W U₁ := ((hP i hi).1 _ hWU1e).1
        have hWU2 : QEdge W U₂ := ((hP j hj).1 _ hWU2e).1
        have hWne_di : W ≠ dst i := fun heq =>
          hWneV (hacyc W V hWV (heq ▸ ((hP i hi).2.1 V hV_i).2.2))
        have hWne_dj : W ≠ dst j := fun heq =>
          hWneV (hacyc W V hWV (heq ▸ ((hP j hj).2.1 V hV_j).2.2))
        have hle1 : sccCode U₁ ≤ sccCode U₂ :=
          (hnextHop_spec W (dst i) ((hP i hi).2.1 W hWi).2.2 hWne_di).2.2 U₂ hWU2
            (Relation.ReflTransGen.trans hU2V ((hP i hi).2.1 V hV_i).2.2)
        have hle2 : sccCode U₂ ≤ sccCode U₁ :=
          (hnextHop_spec W (dst j) ((hP j hj).2.1 W hWj).2.2 hWne_dj).2.2 U₁ hWU1
            (Relation.ReflTransGen.trans hU1V ((hP j hj).2.1 V hV_j).2.2)
        have hU1Q : U₁ ∈ Q := (hQEdge_mem W U₁ hWU1).2.1
        have hU2Q : U₂ ∈ Q := (hQEdge_mem W U₂ hWU2).2.1
        have hUeq : U₁ = U₂ := sccCode_inj_on_disjoint (hQne U₁ hU1Q) (hQne U₂ hU2Q)
          (hQdisj U₁ hU1Q U₂ hU2Q) (Nat.le_antisymm hle1 hle2)
        rw [← hUeq] at hWU2e hU2j
        by_cases hU1Veq : U₁ = V
        · subst hU1Veq
          have h1' := (hP i hi).2.2.2.2.1 X₁ W U₁ h1 hWU1e
          have h2' := (hP j hj).2.2.2.2.1 X₂ W U₁ h2 hWU2e
          exact h1'.trans h2'.symm
        · exact ih (reachSet U₁).card (by rw [← hWk]; exact hreachSet_lt W U₁ hWU1)
            U₁ rfl hU1i hU2j hU1V hU1Veq
    exact hXne (hsame (reachSet Z).card Z rfl hZi hZj hZV hZneV)
  let E := I.biUnion (fun i => listEdges (P i))
  refine ⟨E, ?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_biUnion.mp he with ⟨i, hi, hei⟩
    exact ((hP i hi).1 e hei).1
  · intro i hi
    exact reflTransGen_mono_rel
      (fun _ _ h => Finset.mem_biUnion.mpr ⟨i, hi, h⟩) (hP i hi).2.2.2.1
  · let inSet : Finset (Lit b) → Finset (Finset (Lit b)) := fun V =>
      Q.filter (fun X => (X, V) ∈ E)
    have hE_eq_sum : E.card = ∑ V ∈ Q, (inSet V).card := by
      have hE_eq : E = Q.biUnion (fun V => (inSet V).image (fun X => (X, V))) := by
        ext ⟨X, V⟩
        simp only [Finset.mem_biUnion, Finset.mem_image, inSet, Finset.mem_filter]
        constructor
        · intro hXV
          rcases Finset.mem_biUnion.mp hXV with ⟨i, hi, hei⟩
          have hQ := hQEdge_mem X V ((hP i hi).1 (X, V) hei).1
          exact ⟨V, hQ.2.1, X, ⟨hQ.1, hXV⟩, rfl⟩
        · rintro ⟨V', _, X', ⟨_, hX'⟩, hpair⟩
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          exact hX'
      rw [hE_eq, Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun V _ => ?_
        exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
      · intro V₁ _ V₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e he1 he2
        rcases Finset.mem_image.mp he1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp he2 with ⟨_, _, hpair⟩
        exact hne (Prod.mk.inj hpair).2.symm
    have hin_zero : ∀ V ∈ Qzero, (inSet V).card = 0 := by
      intro V hV
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro X hX
      rcases Finset.mem_biUnion.mp (Finset.mem_filter.mp hX).2 with ⟨i, hi, hei⟩
      have hVin : V ∈ P i := mem_listEdges_mem_right hei
      exact hQzero_avoid i hi V hV ((hP i hi).2.1 V hVin).2.1
    let basePred : Finset (Lit b) → Finset (Lit b) := fun V =>
      if h : (inSet V).Nonempty then Classical.choose h else ∅
    let excessSet : Finset (Finset (Lit b) × Finset (Lit b)) :=
      Q.biUnion (fun V => ((inSet V).erase (basePred V)).image (fun X => (X, V)))
    have hexcess_card : excessSet.card = ∑ V ∈ Q, ((inSet V).card - 1) := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun V _ => ?_
        rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
        by_cases hne : (inSet V).Nonempty
        · have hmem : basePred V ∈ inSet V := by
            simp only [basePred, dite_eq_left hne]
            exact Classical.choose_spec hne
          exact Finset.card_erase_of_mem hmem
        · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
      · intro V₁ _ V₂ _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro e he1 he2
        rcases Finset.mem_image.mp he1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp he2 with ⟨_, _, hpair⟩
        exact hne (Prod.mk.inj hpair).2.symm
    have hexcess_le : excessSet.card ≤ Nat.choose I.card 2 := by
      by_cases hI : I.Nonempty
      · obtain ⟨i₀, _⟩ := hI
        rw [← Finset.card_powersetCard 2 I]
        have hpick : ∀ e ∈ E, ∃ i ∈ I, e ∈ listEdges (P i) := fun e he =>
          Finset.mem_biUnion.mp he
        let pathOf : Finset (Lit b) × Finset (Lit b) → ι := fun e =>
          if h : e ∈ E then Classical.choose (hpick e h) else i₀
        have hpathOf_spec : ∀ e, (he : e ∈ E) →
            pathOf e ∈ I ∧ e ∈ listEdges (P (pathOf e)) := by
          intro e he
          simp only [pathOf, dite_eq_left he]
          exact Classical.choose_spec (hpick e he)
        let charge : Finset (Lit b) × Finset (Lit b) → Finset ι := fun e =>
          {pathOf (basePred e.2, e.2), pathOf e}
        have hex_mem : ∀ e ∈ excessSet,
            e.2 ∈ Q ∧ e.1 ∈ inSet e.2 ∧ e.1 ≠ basePred e.2 ∧
            basePred e.2 ∈ inSet e.2 ∧ e ∈ E ∧ (basePred e.2, e.2) ∈ E := by
          intro ⟨X, V⟩ he
          rcases Finset.mem_biUnion.mp he with ⟨V', hV'Q, hXV'⟩
          rcases Finset.mem_image.mp hXV' with ⟨X', hX'er, hpair⟩
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          have hXne : X' ≠ basePred V' := (Finset.mem_erase.mp hX'er).1
          have hXin : X' ∈ inSet V' := (Finset.mem_erase.mp hX'er).2
          have hneV : (inSet V').Nonempty := ⟨X', hXin⟩
          have hbase : basePred V' ∈ inSet V' := by
            simp only [basePred, dite_eq_left hneV]
            exact Classical.choose_spec hneV
          exact ⟨hV'Q, hXin, hXne, hbase, (Finset.mem_filter.mp hXin).2,
                 (Finset.mem_filter.mp hbase).2⟩
        refine Finset.card_le_card_of_injOn charge ?_ ?_
        · intro e he
          have ⟨_, _, hXne, _, heE, hbE⟩ := hex_mem e he
          have ⟨hp0I, hp0E⟩ := hpathOf_spec (basePred e.2, e.2) hbE
          have ⟨hp1I, hp1E⟩ := hpathOf_spec e heE
          have hpne : pathOf (basePred e.2, e.2) ≠ pathOf e := by
            intro hpeq
            rw [hpeq] at hp0E
            exact hXne ((hP (pathOf e) hp1I).2.2.2.2.1 e.1 (basePred e.2) e.2 hp1E hp0E)
          refine Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hpne⟩
          intro k hk
          simp only [charge, Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl <;> assumption
        · intro e₁ he₁ e₂ he₂ heq
          have ⟨_, _, hX1ne, _, he1E, hb1E⟩ := hex_mem e₁ he₁
          have ⟨_, _, hX2ne, _, he2E, hb2E⟩ := hex_mem e₂ he₂
          have ⟨hp01I, hp01E⟩ := hpathOf_spec (basePred e₁.2, e₁.2) hb1E
          have ⟨hp11I, hp11E⟩ := hpathOf_spec e₁ he1E
          have ⟨hp02I, hp02E⟩ := hpathOf_spec (basePred e₂.2, e₂.2) hb2E
          have ⟨hp12I, hp12E⟩ := hpathOf_spec e₂ he2E
          set a₁ := pathOf (basePred e₁.2, e₁.2)
          set d₁ := pathOf e₁
          set a₂ := pathOf (basePred e₂.2, e₂.2)
          set d₂ := pathOf e₂
          have ha1d1 : a₁ ≠ d₁ := by
            intro h; rw [h] at hp01E
            exact hX1ne ((hP d₁ hp11I).2.2.2.2.1 e₁.1 (basePred e₁.2) e₁.2 hp11E hp01E)
          have ha2d2 : a₂ ≠ d₂ := by
            intro h; rw [h] at hp02E
            exact hX2ne ((hP d₂ hp12I).2.2.2.2.1 e₂.1 (basePred e₂.2) e₂.2 hp12E hp02E)
          have hpair_cases : (a₁ = a₂ ∧ d₁ = d₂) ∨ (a₁ = d₂ ∧ d₁ = a₂) := by
            have heq' : ({a₁, d₁} : Finset ι) = {a₂, d₂} := heq
            have ha1 : a₁ ∈ ({a₂, d₂} : Finset ι) := by rw [← heq']; simp
            have hd1 : d₁ ∈ ({a₂, d₂} : Finset ι) := by rw [← heq']; simp
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha1 hd1
            rcases ha1 with h1 | h1 <;> rcases hd1 with h2 | h2
            · exact False.elim (ha1d1 (h1.trans h2.symm))
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2⟩
            · exact False.elim (ha1d1 (h1.trans h2.symm))
          have hVeq : e₁.2 = e₂.2 := by
            rcases hpair_cases with ⟨ha, hd⟩ | ⟨ha, hd⟩
            · have h12 : QReach e₁.2 e₂.2 := hfirst_shared a₁ hp01I d₁ hp11I
                (basePred e₁.2) e₁.1 e₁.2 hp01E hp11E hX1ne.symm e₂.2
                (ha ▸ mem_listEdges_mem_right hp02E) (hd ▸ mem_listEdges_mem_right hp12E)
              have h21 : QReach e₂.2 e₁.2 := hfirst_shared a₂ hp02I d₂ hp12I
                (basePred e₂.2) e₂.1 e₂.2 hp02E hp12E hX2ne.symm e₁.2
                (ha ▸ mem_listEdges_mem_right hp01E) (hd ▸ mem_listEdges_mem_right hp11E)
              exact hacyc e₁.2 e₂.2 h12 h21
            · have h12 : QReach e₁.2 e₂.2 := hfirst_shared a₁ hp01I d₁ hp11I
                (basePred e₁.2) e₁.1 e₁.2 hp01E hp11E hX1ne.symm e₂.2
                (ha ▸ mem_listEdges_mem_right hp12E) (hd ▸ mem_listEdges_mem_right hp02E)
              have h21 : QReach e₂.2 e₁.2 := hfirst_shared a₂ hp02I d₂ hp12I
                (basePred e₂.2) e₂.1 e₂.2 hp02E hp12E hX2ne.symm e₁.2
                (hd ▸ mem_listEdges_mem_right hp11E) (ha ▸ mem_listEdges_mem_right hp01E)
              exact hacyc e₁.2 e₂.2 h12 h21
          have ha_eq : a₁ = a₂ := by
            simp only [a₁, a₂, hVeq]
          have hd_eq : d₁ = d₂ := by
            rcases hpair_cases with ⟨_, hd⟩ | ⟨h1, _⟩
            · exact hd
            · exact False.elim (ha2d2 (ha_eq.symm.trans h1))
          have hXeq : e₁.1 = e₂.1 := by
            have hp12E' : (e₂.1, e₁.2) ∈ listEdges (P d₁) := by
              rw [hVeq, hd_eq]; exact hp12E
            exact (hP d₁ hp11I).2.2.2.2.1 e₁.1 e₂.1 e₁.2 hp11E hp12E'
          exact Prod.ext hXeq hVeq
      · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
        have hEempty : E = ∅ := by simp [E, hIempty]
        have hex_zero : excessSet.card = 0 := by
          rw [hexcess_card]
          exact Finset.sum_eq_zero fun V _ => by
            have : inSet V = ∅ := by simp [inSet, hEempty]
            simp [this]
        omega
    have hsum_le : E.card + Qzero.card ≤ Q.card + excessSet.card := by
      rw [hE_eq_sum, hexcess_card]
      have hsplit : ∑ V ∈ Q, (inSet V).card = ∑ V ∈ Q \ Qzero, (inSet V).card := by
        rw [← Finset.sum_sdiff hQzero_sub]
        have hz : ∑ V ∈ Qzero, (inSet V).card = 0 :=
          Finset.sum_eq_zero fun V hV => hin_zero V hV
        omega
      have hle_nz : ∑ V ∈ Q \ Qzero, (inSet V).card ≤
          (Q \ Qzero).card + ∑ V ∈ Q \ Qzero, ((inSet V).card - 1) := by
        calc ∑ V ∈ Q \ Qzero, (inSet V).card
            ≤ ∑ V ∈ Q \ Qzero, (1 + ((inSet V).card - 1)) :=
              Finset.sum_le_sum fun V _ => by omega
          _ = ∑ _V ∈ Q \ Qzero, 1 + ∑ V ∈ Q \ Qzero, ((inSet V).card - 1) :=
              Finset.sum_add_distrib
          _ = (Q \ Qzero).card + ∑ V ∈ Q \ Qzero, ((inSet V).card - 1) := by simp
      have hsum_sub : ∑ V ∈ Q \ Qzero, ((inSet V).card - 1) ≤ ∑ V ∈ Q, ((inSet V).card - 1) :=
        Finset.sum_le_sum_of_subset Finset.sdiff_subset
      have hQsplit : (Q \ Qzero).card + Qzero.card = Q.card :=
        Finset.card_sdiff_add_card_eq_card hQzero_sub
      omega
    omega

-- Part 5b: Ternary-present conflict bound (HT.Nonempty)

lemma ternary_present_bound {b s : Nat} (hb : 2 ≤ b)
    (HT HB : Finset (Hidden b)) (HU : Finset (Lit b))
    (hHTne : HT.Nonempty)
    (hHTcard : HT.card ≤ s) (hHTw : ∀ D ∈ HT, D.card ≤ 3)
    (hHB2 : ∀ D ∈ HB, D.card = 2)
    (hunsat : ¬∃ h : Fin b → Bool,
      (∀ D ∈ HT, holds D h) ∧ (∀ D ∈ HB, holds D h) ∧ (∀ u ∈ HU, h u.1 = u.2))
    (hmin : ∀ HT' ⊆ HT, ∀ HB' ⊆ HB, ∀ HU' ⊆ HU,
      (¬∃ h : Fin b → Bool,
        (∀ D ∈ HT', holds D h) ∧ (∀ D ∈ HB', holds D h) ∧ (∀ u ∈ HU', h u.1 = u.2)) →
      HT' = HT ∧ HB' = HB ∧ HU' = HU) :
    HB.card + 2 * HU.card ≤ 2 * b + Nat.choose (Nat.choose (3 * s + 1) 2) 2 + 3 * s := by
  classical
  have hsatBU : ∃ h : Fin b → Bool, (∀ D ∈ HB, holds D h) ∧ (∀ u ∈ HU, h u.1 = u.2) := by
    by_contra hno
    have huns : ¬∃ h : Fin b → Bool,
        (∀ D ∈ (∅ : Finset (Hidden b)), holds D h) ∧ (∀ D ∈ HB, holds D h) ∧
        (∀ u ∈ HU, h u.1 = u.2) := by
      rintro ⟨h, _, hB, hU⟩; exact hno ⟨h, hB, hU⟩
    have heqT := (hmin ∅ (Finset.empty_subset _) HB (Finset.Subset.refl _) HU
      (Finset.Subset.refl _) huns).1
    exact hHTne.ne_empty heqT.symm
  obtain ⟨hsat, hsatB, hsatU⟩ := hsatBU
  have hnoSelf : ∀ x : Lit b, ¬(BReach HB x (negLit x) ∧ BReach HB (negLit x) x) := by
    intro x ⟨h1, h2⟩
    by_cases hx : hsat x.1 = x.2
    · have hnx := BReach_sound hsatB h1 hx
      simp only [negLit] at hnx; rw [hx] at hnx
      exact bool_eq_not_false hnx
    · exact hx (BReach_sound hsatB h2 (negLit_true_of_ne hx))
  have hnoUnit : ∀ u ∈ HU, ∀ v ∈ HU, ¬BReach HB u (negLit v) := by
    intro u hu v hv hr
    have hnv := BReach_sound hsatB hr (hsatU u hu)
    simp only [negLit] at hnv; rw [hsatU v hv] at hnv
    exact bool_eq_not_false hnv
  let Q : Finset (Finset (Lit b)) := (Finset.univ : Finset (Lit b)).image (sccOf HB)
  have hQne : ∀ S ∈ Q, S.Nonempty := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
    exact ⟨x, mem_sccOf_self HB x⟩
  have hQdisj : ∀ S₁ ∈ Q, ∀ S₂ ∈ Q, S₁ ≠ S₂ → Disjoint S₁ S₂ := by
    intro S₁ hS₁ S₂ hS₂ hne
    rcases Finset.mem_image.mp hS₁ with ⟨x₁, _, rfl⟩
    rcases Finset.mem_image.mp hS₂ with ⟨x₂, _, rfl⟩
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact hne ((sccOf_eq_of_mem hz₁).symm.trans (sccOf_eq_of_mem hz₂))
  have hQneg_mem : ∀ S ∈ Q, negSCC S ∈ Q := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
    rw [← sccOf_negLit]
    exact Finset.mem_image.mpr ⟨negLit x, Finset.mem_univ _, rfl⟩
  have hQneg_ne : ∀ S ∈ Q, negSCC S ≠ S := by
    intro S hS heq
    rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
    have hx : negLit x ∈ sccOf HB x := by
      rw [← heq]; exact Finset.mem_image.mpr ⟨x, mem_sccOf_self HB x, rfl⟩
    exact hnoSelf x (mem_sccOf.mp hx)
  have hQsum : ∑ S ∈ Q, S.card = 2 * b := by
    have hunion : Q.biUnion id = Finset.univ := by
      ext x
      simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
      exact ⟨sccOf HB x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, mem_sccOf_self HB x⟩
    have hcard : (Q.biUnion id).card = ∑ S ∈ Q, S.card :=
      Finset.card_biUnion (fun S₁ h1 S₂ h2 hne => hQdisj S₁ h1 S₂ h2 hne)
    rw [hunion] at hcard
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hcard
    omega
  let Qhalf : Finset (Finset (Lit b)) := Q.filter (fun S => sccCode S < sccCode (negSCC S))
  have hQhalf_cover : Q = Qhalf ∪ Qhalf.image negSCC := by
    ext S
    simp only [Finset.mem_union, Qhalf, Finset.mem_filter, Finset.mem_image]
    constructor
    · intro hSQ
      have hne_code : sccCode S ≠ sccCode (negSCC S) := fun heq =>
        hQneg_ne S hSQ (sccCode_inj_on_disjoint (hQne S hSQ) (hQne _ (hQneg_mem S hSQ))
          (hQdisj S hSQ _ (hQneg_mem S hSQ)) heq).symm
      rcases Nat.lt_or_gt.mp hne_code with hlt | hgt
      · exact Or.inl ⟨hSQ, hlt⟩
      · right
        refine ⟨negSCC S, ⟨hQneg_mem S hSQ, ?_⟩, negSCC_negSCC S⟩
        rwa [negSCC_negSCC]
    · rintro (⟨hSQ, _⟩ | ⟨T, ⟨hTQ, _⟩, rfl⟩)
      · exact hSQ
      · exact hQneg_mem T hTQ
  have hQhalf_disj : Disjoint Qhalf (Qhalf.image negSCC) := by
    rw [Finset.disjoint_left]
    intro S h1 h2
    have hlt1 := (Finset.mem_filter.mp h1).2
    rcases Finset.mem_image.mp h2 with ⟨T, hT, rfl⟩
    have hlt2 := (Finset.mem_filter.mp hT).2
    rw [negSCC_negSCC] at hlt1
    omega
  have hQhalf_card : 2 * Qhalf.card = Q.card := by
    have h1 := congrArg Finset.card hQhalf_cover
    have hneg_inj : Function.Injective (@negSCC b) := fun A B h => by
      have := congrArg negSCC h; simpa [negSCC_negSCC] using this
    rw [Finset.card_union_of_disjoint hQhalf_disj,
        Finset.card_image_of_injective Qhalf hneg_inj] at h1
    omega
  have hQhalf_sum : ∑ S ∈ Qhalf, 2 * S.card = 2 * b := by
    have h1 : ∑ S ∈ Q, S.card = ∑ S ∈ Qhalf, S.card + ∑ S ∈ Qhalf.image negSCC, S.card := by
      conv_lhs => rw [hQhalf_cover]
      exact Finset.sum_union hQhalf_disj
    have h2 : ∑ S ∈ Qhalf.image negSCC, S.card = ∑ S ∈ Qhalf, S.card := by
      rw [Finset.sum_image (fun A _ B _ h => by
        have := congrArg negSCC h; simpa [negSCC_negSCC] using this)]
      exact Finset.sum_congr rfl fun S _ => negSCC_card S
    have h3 : ∑ S ∈ Qhalf, 2 * S.card = ∑ S ∈ Qhalf, (S.card + S.card) :=
      Finset.sum_congr rfl fun S _ => by omega
    rw [h3, Finset.sum_add_distrib]
    omega
  have hSCC_both : ∀ S ∈ Qhalf, ∃ BS ⊆ HB, BS.card + 2 ≤ 2 * S.card ∧
      ∀ x ∈ S, ∀ y ∈ S, BReach BS x y := by
    intro S hS
    have hSQ : S ∈ Q := (Finset.mem_filter.mp hS).1
    obtain ⟨r, hr⟩ := hQne S hSQ
    have hSeq : sccOf HB r = S := by
      rcases Finset.mem_image.mp hSQ with ⟨x, _, rfl⟩
      exact sccOf_eq_of_mem hr
    obtain ⟨Bout, hsub1, hc1, hr1⟩ := scc_out_clauses HB r
    obtain ⟨Bin, hsub2, hc2, hr2⟩ := scc_in_clauses HB r
    rw [hSeq] at hc1 hc2 hr1 hr2
    refine ⟨Bout ∪ Bin, Finset.union_subset hsub1 hsub2, ?_, ?_⟩
    · have := Finset.card_union_le Bout Bin; omega
    · intro x hx y hy
      exact Relation.ReflTransGen.trans
        (BReach_mono Finset.subset_union_right (hr2 x hx))
        (BReach_mono Finset.subset_union_left (hr1 y hy))
  let pickBS : Finset (Lit b) → Finset (Hidden b) := fun S =>
    if h : S ∈ Qhalf then Classical.choose (hSCC_both S h) else ∅
  let B_int : Finset (Hidden b) := Qhalf.biUnion pickBS
  have hBint_sub : B_int ⊆ HB := by
    intro D hD
    rcases Finset.mem_biUnion.mp hD with ⟨S, hS, hDS⟩
    simp only [pickBS, dite_eq_left hS] at hDS
    exact (Classical.choose_spec (hSCC_both S hS)).1 hDS
  have hBint_card : B_int.card + Q.card ≤ 2 * b := by
    have h1 : B_int.card ≤ ∑ S ∈ Qhalf, (pickBS S).card := Finset.card_biUnion_le
    have h2 : ∑ S ∈ Qhalf, ((pickBS S).card + 2) ≤ ∑ S ∈ Qhalf, 2 * S.card := by
      refine Finset.sum_le_sum fun S hS => ?_
      simp only [pickBS, dite_eq_left hS]
      exact (Classical.choose_spec (hSCC_both S hS)).2.1
    rw [Finset.sum_add_distrib] at h2
    have hc2 : ∑ _S ∈ Qhalf, 2 = 2 * Qhalf.card := by simp [Nat.mul_comm]
    rw [hc2] at h2
    omega
  have hBint_conn : ∀ S ∈ Q, ∀ x ∈ S, ∀ y ∈ S, BReach B_int x y := by
    intro S hSQ x hx y hy
    rw [hQhalf_cover, Finset.mem_union] at hSQ
    rcases hSQ with hSh | hSn
    · have hsub : pickBS S ⊆ B_int := Finset.subset_biUnion_of_mem pickBS hSh
      have hsp := Classical.choose_spec (hSCC_both S hSh)
      have hr : BReach (pickBS S) x y := by
        simp only [pickBS, dite_eq_left hSh]
        exact hsp.2.2 x hx y hy
      exact BReach_mono hsub hr
    · rcases Finset.mem_image.mp hSn with ⟨T, hTh, rfl⟩
      rcases Finset.mem_image.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
      have hsub : pickBS T ⊆ B_int := Finset.subset_biUnion_of_mem pickBS hTh
      have hsp := Classical.choose_spec (hSCC_both T hTh)
      have hr : BReach (pickBS T) y' x' := by
        simp only [pickBS, dite_eq_left hTh]
        exact hsp.2.2 y' hy' x' hx'
      exact BReach_contra (BReach_mono hsub hr)
  let QEdge : Finset (Lit b) → Finset (Lit b) → Prop := fun S T =>
    S ∈ Q ∧ T ∈ Q ∧ S ≠ T ∧ ∃ x ∈ S, ∃ y ∈ T, BEdge HB x y
  let QReach := Relation.ReflTransGen QEdge
  have hQEdge_mem : ∀ S T, QEdge S T → S ∈ Q ∧ T ∈ Q ∧ S ≠ T := fun _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩
  have hQReach_iff : ∀ x y : Lit b, QReach (sccOf HB x) (sccOf HB y) ↔ BReach HB x y := by
    intro x y
    constructor
    · intro hr
      have hgen : ∀ S T, QReach S T → S ∈ Q → ∀ a ∈ S, ∀ d ∈ T, BReach HB a d := by
        intro S T hST
        induction hST with
        | refl =>
          intro hSQ a ha d hd
          exact BReach_mono hBint_sub (hBint_conn S hSQ a ha d hd)
        | @tail M N _ hMN ih =>
          intro hSQ a ha d hd
          rcases hMN with ⟨_, hNQ, _, u, huM, v, hvN, huv⟩
          have hau : BReach HB a u := ih hSQ a ha u huM
          have hvd : BReach HB v d := BReach_mono hBint_sub (hBint_conn N hNQ v hvN d hd)
          exact Relation.ReflTransGen.trans hau (Relation.ReflTransGen.head huv hvd)
      exact hgen (sccOf HB x) (sccOf HB y) hr
        (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
        x (mem_sccOf_self HB x) y (mem_sccOf_self HB y)
    · intro hr
      induction hr with
      | refl => exact Relation.ReflTransGen.refl
      | @tail u v _ huv ih =>
        by_cases heq : sccOf HB u = sccOf HB v
        · rwa [← heq]
        · refine Relation.ReflTransGen.tail ih ⟨?_, ?_, heq, u, mem_sccOf_self HB u,
            v, mem_sccOf_self HB v, huv⟩
          · exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
          · exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
  have hacyc : ∀ S T, QReach S T → QReach T S → S = T := by
    intro S T hST hTS
    rcases Relation.ReflTransGen.cases_head hST with rfl | ⟨U, hSU, _⟩
    · rfl
    · have hSQ : S ∈ Q := hSU.1
      have hTQ : T ∈ Q := by
        rcases Relation.ReflTransGen.cases_tail hST with rfl | ⟨_, _, hNT⟩
        · exact hSQ
        · exact hNT.2.1
      rcases Finset.mem_image.mp hSQ with ⟨x, _, rfl⟩
      rcases Finset.mem_image.mp hTQ with ⟨y, _, rfl⟩
      have hxy := (hQReach_iff x y).mp hST
      have hyx := (hQReach_iff y x).mp hTS
      exact (sccOf_eq_of_mem (mem_sccOf.mpr ⟨hxy, hyx⟩)).symm
  -- Literals of HT, V_unit, V_self, V_ok, Pairs, HU'
  let defLit : Lit b := (⟨0, by omega⟩, false)
  let VT : Finset (Lit b) := HT.biUnion id
  have hVT_card : VT.card ≤ 3 * s := by
    calc VT.card ≤ ∑ D ∈ HT, D.card := Finset.card_biUnion_le
      _ ≤ ∑ _D ∈ HT, 3 := Finset.sum_le_sum fun D hD => hHTw D hD
      _ = HT.card * 3 := by simp
      _ ≤ 3 * s := by omega
  let repU : Finset (Lit b) → Lit b := fun S =>
    if h : (HU ∩ S).Nonempty then Classical.choose h else defLit
  have hrepU_spec : ∀ u ∈ HU,
      repU (sccOf HB u) ∈ HU ∧ repU (sccOf HB u) ∈ sccOf HB u ∧
      sccOf HB (repU (sccOf HB u)) = sccOf HB u := by
    intro u hu
    have hne : (HU ∩ sccOf HB u).Nonempty := ⟨u, Finset.mem_inter.mpr ⟨hu, mem_sccOf_self HB u⟩⟩
    have hmem : repU (sccOf HB u) ∈ HU ∩ sccOf HB u := by
      simp only [repU, dite_eq_left hne]
      exact Classical.choose_spec hne
    have h1 := (Finset.mem_inter.mp hmem).1
    have h2 := (Finset.mem_inter.mp hmem).2
    exact ⟨h1, h2, sccOf_eq_of_mem h2⟩
  let Vunit : Finset (Lit b) := VT.filter (fun a => ∃ u ∈ HU, BReach HB u (negLit a))
  let Vself : Finset (Lit b) := (VT \ Vunit).filter (fun a => BReach HB a (negLit a))
  let Vok : Finset (Lit b) := (VT \ Vunit) \ Vself
  let pickU : Lit b → Lit b := fun a =>
    if h : ∃ u ∈ HU, BReach HB u (negLit a) then
      repU (sccOf HB (Classical.choose h))
    else defLit
  have hpickU_spec : ∀ a ∈ Vunit,
      pickU a ∈ HU ∧ BReach HB (pickU a) (negLit a) ∧
      pickU a = repU (sccOf HB (pickU a)) := by
    intro a ha
    have hex : ∃ u ∈ HU, BReach HB u (negLit a) := (Finset.mem_filter.mp ha).2
    have hcu : Classical.choose hex ∈ HU := (Classical.choose_spec hex).1
    have hcr : BReach HB (Classical.choose hex) (negLit a) := (Classical.choose_spec hex).2
    have ⟨h1, h2, h3⟩ := hrepU_spec (Classical.choose hex) hcu
    simp only [pickU, dite_eq_left hex]
    refine ⟨h1, ?_, ?_⟩
    · exact Relation.ReflTransGen.trans (mem_sccOf.mp h2).2 hcr
    · rw [h3]
  let HU' : Finset (Lit b) := Vunit.image pickU
  have hHU'_sub : HU' ⊆ HU := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
    exact (hpickU_spec a ha).1
  have hHU'_card : HU'.card ≤ 3 * s := by
    calc HU'.card ≤ Vunit.card := Finset.card_image_le
      _ ≤ VT.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ 3 * s := hVT_card
  have hHU'_rep : ∀ u ∈ HU', u = repU (sccOf HB u) := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨a, ha, rfl⟩
    exact (hpickU_spec a ha).2.2
  let Qzero : Finset (Finset (Lit b)) := HU'.image (fun u => sccOf HB (negLit u))
  have hQzero_sub : Qzero ⊆ Q := by
    intro S hS
    rcases Finset.mem_image.mp hS with ⟨u, _, rfl⟩
    exact Finset.mem_image.mpr ⟨negLit u, Finset.mem_univ _, rfl⟩
  have hQzero_card : Qzero.card = HU'.card := by
    refine Finset.card_image_of_injOn ?_
    intro u₁ hu₁ u₂ hu₂ heq
    dsimp only at heq
    rw [sccOf_negLit, sccOf_negLit] at heq
    have hscc : sccOf HB u₁ = sccOf HB u₂ := by
      have := congrArg negSCC heq; simpa [negSCC_negSCC] using this
    rw [hHU'_rep u₁ hu₁, hHU'_rep u₂ hu₂, hscc]
  -- Incompatible pairs in Vok
  let Pairs : Finset (Finset (Lit b)) :=
    (Vok.powersetCard 2).filter (fun K => ∃ a ∈ K, ∃ d ∈ K, a ≠ d ∧ BReach HB a (negLit d))
  let I : Finset (Finset (Lit b)) := (Vunit ∪ Vself).image (fun a : Lit b => ({a} : Finset (Lit b))) ∪ Pairs
  have hI_card : I.card ≤ Nat.choose (3 * s + 1) 2 := by
    have hdisj : Disjoint ((Vunit ∪ Vself).image (fun a : Lit b => ({a} : Finset (Lit b)))) Pairs := by
      rw [Finset.disjoint_left]
      intro K h1 h2
      rcases Finset.mem_image.mp h1 with ⟨a, _, rfl⟩
      have hc2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h2).1).2
      simp at hc2
    have h1 : ((Vunit ∪ Vself).image (fun a : Lit b => ({a} : Finset (Lit b)))).card ≤ VT.card := by
      calc ((Vunit ∪ Vself).image (fun a : Lit b => ({a} : Finset (Lit b)))).card ≤ (Vunit ∪ Vself).card := Finset.card_image_le
        _ ≤ VT.card := Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
            ((Finset.filter_subset _ _).trans Finset.sdiff_subset))
    have h2 : Pairs.card ≤ Nat.choose VT.card 2 := by
      calc Pairs.card ≤ (Vok.powersetCard 2).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = Nat.choose Vok.card 2 := Finset.card_powersetCard 2 Vok
        _ ≤ Nat.choose VT.card 2 := Nat.choose_le_choose 2
            (Finset.card_le_card (Finset.sdiff_subset.trans Finset.sdiff_subset))
    have hsum : I.card ≤ Nat.choose (VT.card + 1) 2 := by
      rw [Finset.card_union_of_disjoint hdisj, Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.add_le_add h1 h2
    exact hsum.trans (Nat.choose_le_choose 2 (by omega))
  -- Define endpoints src, dst for each K ∈ I
  let pairA : Finset (Lit b) → Lit b := fun K =>
    if h : ∃ a ∈ K, ∃ d ∈ K, a ≠ d ∧ BReach HB a (negLit d) then Classical.choose h else defLit
  let pairD : Finset (Lit b) → Lit b := fun K =>
    if h : ∃ a ∈ K, ∃ d ∈ K, a ≠ d ∧ BReach HB a (negLit d) then
      Classical.choose (Classical.choose_spec h).2
    else defLit
  have hpair_spec : ∀ K ∈ Pairs,
      pairA K ∈ K ∧ pairD K ∈ K ∧ pairA K ≠ pairD K ∧
      BReach HB (pairA K) (negLit (pairD K)) ∧
      pairA K ∈ Vok ∧ pairD K ∈ Vok := by
    intro K hK
    have hex := (Finset.mem_filter.mp hK).2
    have hsub := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hK).1).1
    have hsp1 := Classical.choose_spec hex
    have hsp2 := Classical.choose_spec hsp1.2
    simp only [pairA, pairD, dite_eq_left hex]
    exact ⟨hsp1.1, hsp2.1, hsp2.2.1, hsp2.2.2, hsub hsp1.1, hsub hsp2.1⟩
  let singLit : Finset (Lit b) → Lit b := fun K =>
    if h : K.Nonempty then Classical.choose h else defLit
  have hsingLit : ∀ a : Lit b, singLit {a} = a := by
    intro a
    have hne : ({a} : Finset (Lit b)).Nonempty := Finset.singleton_nonempty a
    simp only [singLit, dite_eq_left hne]
    exact Finset.mem_singleton.mp (Classical.choose_spec hne)
  let src : Finset (Lit b) → Finset (Lit b) := fun K =>
    if K.card = 1 then
      let a := singLit K
      if a ∈ Vunit then sccOf HB (pickU a) else sccOf HB a
    else sccOf HB (pairA K)
  let dst : Finset (Lit b) → Finset (Lit b) := fun K =>
    if K.card = 1 then sccOf HB (negLit (singLit K))
    else sccOf HB (negLit (pairD K))
  have hsrcQ : ∀ K ∈ I, src K ∈ Q := by
    intro K _
    dsimp only [src]
    split_ifs <;> exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hdstQ : ∀ K ∈ I, dst K ∈ Q := by
    intro K _
    unfold dst
    split_ifs <;> exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  have hI_reach : ∀ K ∈ I, QReach (src K) (dst K) := by
    intro K hK
    rcases Finset.mem_union.mp hK with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨a, ha, rfl⟩
      simp only [src, dst, Finset.card_singleton, ↓reduceIte, hsingLit]
      by_cases hau : a ∈ Vunit
      · rw [ite_eq_left hau]
        exact (hQReach_iff _ _).mpr (hpickU_spec a hau).2.1
      · rw [ite_eq_right hau]
        have has : a ∈ Vself := (Finset.mem_union.mp ha).resolve_left hau
        exact (hQReach_iff _ _).mpr (Finset.mem_filter.mp has).2
    · have hc2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h2).1).2
      simp only [src, dst, hc2, show (2 = 1) = False by decide, ↓reduceIte]
      exact (hQReach_iff _ _).mpr (hpair_spec K h2).2.2.2.1
  have hQzero_avoid : ∀ K ∈ I, ∀ S ∈ Qzero, ¬QReach (src K) S := by
    intro K hK S hS hR
    rcases Finset.mem_image.mp hS with ⟨u, hu', rfl⟩
    have hu : u ∈ HU := hHU'_sub hu'
    rcases Finset.mem_union.mp hK with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨a, ha, rfl⟩
      simp only [src, Finset.card_singleton, ↓reduceIte, hsingLit] at hR
      by_cases hau : a ∈ Vunit
      · rw [ite_eq_left hau] at hR
        exact hnoUnit (pickU a) (hpickU_spec a hau).1 u hu ((hQReach_iff _ _).mp hR)
      · rw [ite_eq_right hau] at hR
        have has : a ∈ Vself := (Finset.mem_union.mp ha).resolve_left hau
        have haVT : a ∈ VT := (Finset.mem_sdiff.mp (Finset.mem_filter.mp has).1).1
        have hbr : BReach HB a (negLit u) := (hQReach_iff _ _).mp hR
        have hcon : BReach HB u (negLit a) := by simpa [negLit_negLit] using BReach_contra hbr
        exact hau (Finset.mem_filter.mpr ⟨haVT, u, hu, hcon⟩)
    · have hc2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp h2).1).2
      simp only [src, hc2, show (2 = 1) = False by decide, ↓reduceIte] at hR
      have haVok : pairA K ∈ Vok := (hpair_spec K h2).2.2.2.2.1
      have haNotU : pairA K ∉ Vunit := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp haVok).1).2
      have haVT : pairA K ∈ VT := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp haVok).1).1
      have hbr : BReach HB (pairA K) (negLit u) := (hQReach_iff _ _).mp hR
      have hcon : BReach HB u (negLit (pairA K)) := by simpa [negLit_negLit] using BReach_contra hbr
      exact haNotU (Finset.mem_filter.mpr ⟨haVT, u, hu, hcon⟩)
  -- Apply DAG charging bound!
  obtain ⟨E, hEQ, hEReach, hEcard⟩ := dag_charging_bound Q QEdge hQne hQdisj hQEdge_mem hacyc
    I src dst hsrcQ hdstQ hI_reach Qzero hQzero_sub hQzero_avoid
  -- Realize each quotient edge in E by one binary clause in HB
  have hedge_cl : ∀ e ∈ E, ∃ D ∈ HB, ∃ x ∈ e.1, ∃ y ∈ e.2, D = ({negLit x, y} : Hidden b) := by
    intro e he
    rcases hEQ e he with ⟨_, _, _, x, hx, y, hy, hxy⟩
    exact ⟨{negLit x, y}, hxy, x, hx, y, hy, rfl⟩
  let pickCl : Finset (Lit b) × Finset (Lit b) → Hidden b := fun e =>
    if h : e ∈ E then Classical.choose (hedge_cl e h) else ∅
  let B_ext : Finset (Hidden b) := E.image pickCl
  have hBext_sub : B_ext ⊆ HB := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨e, he, rfl⟩
    simp only [pickCl, dite_eq_left he]
    exact (Classical.choose_spec (hedge_cl e he)).1
  have hBext_card : B_ext.card ≤ E.card := Finset.card_image_le
  let B' : Finset (Hidden b) := B_int ∪ B_ext
  have hB'_sub : B' ⊆ HB := Finset.union_subset hBint_sub hBext_sub
  -- Any path in E lifts to BReach B'
  have hE_to_B' : ∀ S T, Relation.ReflTransGen (fun A B => (A, B) ∈ E) S T →
      S ∈ Q → ∀ a ∈ S, ∀ d ∈ T, BReach B' a d := by
    intro S T hST
    induction hST with
    | refl =>
      intro hSQ a ha d hd
      exact BReach_mono Finset.subset_union_left (hBint_conn S hSQ a ha d hd)
    | @tail M N _ hMN ih =>
      intro hSQ a ha d hd
      have hNQ : N ∈ Q := (hEQ (M, N) hMN).2.1
      have hsp := Classical.choose_spec (hedge_cl (M, N) hMN)
      rcases hsp.2 with ⟨u, huM, v, hvN, hDeq⟩
      have hDmem : ({negLit u, v} : Hidden b) ∈ B' := by
        apply Finset.mem_union_right
        refine Finset.mem_image.mpr ⟨(M, N), hMN, ?_⟩
        simp only [pickCl, dite_eq_left hMN]
        exact hDeq
      have hau : BReach B' a u := ih hSQ a ha u huM
      have hvd : BReach B' v d := BReach_mono Finset.subset_union_left (hBint_conn N hNQ v hvN d hd)
      exact Relation.ReflTransGen.trans hau (Relation.ReflTransGen.head hDmem hvd)
  -- Show (HT, B', HU') is UNSAT!
  have hunsat' : ¬∃ h : Fin b → Bool,
      (∀ D ∈ HT, holds D h) ∧ (∀ D ∈ B', holds D h) ∧ (∀ u ∈ HU', h u.1 = u.2) := by
    rintro ⟨h, hT, hB', hU'⟩
    let S : Finset (Lit b) := VT.filter (fun l => h l.1 = l.2)
    have hS_hits : ∀ D ∈ HT, ∃ l ∈ D, l ∈ S := by
      intro D hD
      rcases hT D hD with ⟨l, hlD, hlv⟩
      exact ⟨l, hlD, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨D, hD, hlD⟩, hlv⟩⟩
    have hS_unsat : ¬∃ h' : Fin b → Bool,
        (∀ D ∈ HB, holds D h') ∧ (∀ u ∈ HU ∪ S, h' u.1 = u.2) := by
      rintro ⟨h', h'B, h'US⟩
      apply hunsat
      refine ⟨h', ?_, h'B, fun u hu => h'US u (Finset.mem_union_left S hu)⟩
      intro D hD
      obtain ⟨l, hlD, hlS⟩ := hS_hits D hD
      exact ⟨l, hlD, h'US l (Finset.mem_union_right HU hlS)⟩
    have hconflict : ∃ u ∈ HU ∪ S, ∃ v ∈ HU ∪ S, BReach HB u (negLit v) := by
      by_contra hno
      push Not at hno
      exact hS_unsat (krom_sat HB hHB2 (HU ∪ S) hnoSelf hno)
    rcases hconflict with ⟨u, hu, v, hv, huv⟩
    have hkill_sing : ∀ a ∈ S, a ∈ Vunit ∪ Vself → False := by
      intro a haS haUS
      have ha_true : h a.1 = a.2 := (Finset.mem_filter.mp haS).2
      have hmemI : ({a} : Finset (Lit b)) ∈ I :=
        Finset.mem_union_left Pairs (Finset.mem_image.mpr ⟨a, haUS, rfl⟩)
      have hER := hEReach {a} hmemI
      by_cases hau : a ∈ Vunit
      · simp only [src, dst, Finset.card_singleton, ↓reduceIte, hsingLit,
          ite_eq_left hau] at hER
        have hbr : BReach B' (pickU a) (negLit a) := hE_to_B' _ _ hER
          (Finset.mem_image.mpr ⟨pickU a, Finset.mem_univ _, rfl⟩)
          (pickU a) (mem_sccOf_self HB (pickU a)) (negLit a) (mem_sccOf_self HB (negLit a))
        have hu_true : h (pickU a).1 = (pickU a).2 :=
          hU' (pickU a) (Finset.mem_image.mpr ⟨a, hau, rfl⟩)
        have hna := BReach_sound hB' hbr hu_true
        simp only [negLit] at hna; rw [ha_true] at hna
        exact bool_eq_not_false hna
      · simp only [src, dst, Finset.card_singleton, ↓reduceIte, hsingLit,
          ite_eq_right hau] at hER
        have hbr : BReach B' a (negLit a) := hE_to_B' _ _ hER
          (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩)
          a (mem_sccOf_self HB a) (negLit a) (mem_sccOf_self HB (negLit a))
        have hna := BReach_sound hB' hbr ha_true
        simp only [negLit] at hna; rw [ha_true] at hna
        exact bool_eq_not_false hna
    rcases Finset.mem_union.mp hu with huU | huS <;> rcases Finset.mem_union.mp hv with hvU | hvS
    · exact hnoUnit u huU v hvU huv
    · have hvVT : v ∈ VT := (Finset.mem_filter.mp hvS).1
      exact hkill_sing v hvS (Finset.mem_union_left Vself (Finset.mem_filter.mpr ⟨hvVT, u, huU, huv⟩))
    · have huVT : u ∈ VT := (Finset.mem_filter.mp huS).1
      have hcon : BReach HB v (negLit u) := by simpa [negLit_negLit] using BReach_contra huv
      exact hkill_sing u huS (Finset.mem_union_left Vself (Finset.mem_filter.mpr ⟨huVT, v, hvU, hcon⟩))
    · by_cases huUS : u ∈ Vunit ∪ Vself
      · exact hkill_sing u huS huUS
      · by_cases hvUS : v ∈ Vunit ∪ Vself
        · exact hkill_sing v hvS hvUS
        · have huVT : u ∈ VT := (Finset.mem_filter.mp huS).1
          have hvVT : v ∈ VT := (Finset.mem_filter.mp hvS).1
          have hune : u ≠ v := by
            intro heq; subst heq
            have hnotU : u ∉ Vunit := fun h => huUS (Finset.mem_union_left _ h)
            exact huUS (Finset.mem_union_right _ (Finset.mem_filter.mpr
              ⟨Finset.mem_sdiff.mpr ⟨huVT, hnotU⟩, huv⟩))
          have huVok : u ∈ Vok :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨huVT, fun h => huUS (Finset.mem_union_left _ h)⟩,
              fun h => huUS (Finset.mem_union_right _ h)⟩
          have hvVok : v ∈ Vok :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hvVT, fun h => hvUS (Finset.mem_union_left _ h)⟩,
              fun h => hvUS (Finset.mem_union_right _ h)⟩
          let K : Finset (Lit b) := {u, v}
          have hKP : K ∈ Pairs := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, Finset.card_pair hune⟩,
              ⟨u, by simp [K], v, by simp [K], hune, huv⟩⟩
            intro z hz; simp only [K, Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          have hKI : K ∈ I := Finset.mem_union_right _ hKP
          have hER := hEReach K hKI
          have hKc2 : K.card = 2 := Finset.card_pair hune
          simp only [src, dst, hKc2, show (2 = 1) = False by decide, ↓reduceIte] at hER
          have hbr : BReach B' (pairA K) (negLit (pairD K)) := hE_to_B' _ _ hER
            (Finset.mem_image.mpr ⟨pairA K, Finset.mem_univ _, rfl⟩)
            (pairA K) (mem_sccOf_self HB (pairA K))
            (negLit (pairD K)) (mem_sccOf_self HB (negLit (pairD K)))
          have hpA_mem : pairA K ∈ K := (hpair_spec K hKP).1
          have hpD_mem : pairD K ∈ K := (hpair_spec K hKP).2.1
          have hpA_true : h (pairA K).1 = (pairA K).2 := by
            simp only [K, Finset.mem_insert, Finset.mem_singleton] at hpA_mem
            rcases hpA_mem with h1 | h1 <;> rw [h1]
            · exact (Finset.mem_filter.mp huS).2
            · exact (Finset.mem_filter.mp hvS).2
          have hpD_true : h (pairD K).1 = (pairD K).2 := by
            simp only [K, Finset.mem_insert, Finset.mem_singleton] at hpD_mem
            rcases hpD_mem with h1 | h1 <;> rw [h1]
            · exact (Finset.mem_filter.mp huS).2
            · exact (Finset.mem_filter.mp hvS).2
          have hnd := BReach_sound hB' hbr hpA_true
          simp only [negLit] at hnd; rw [hpD_true] at hnd
          exact bool_eq_not_false hnd
  -- Minimality gives B' = HB and HU' = HU
  have ⟨_, hBeq, hUeq⟩ := hmin HT (Finset.Subset.refl _) B' hB'_sub HU' hHU'_sub hunsat'
  have hB'card : B'.card ≤ B_int.card + B_ext.card := Finset.card_union_le B_int B_ext
  have hchoose : Nat.choose I.card 2 ≤ Nat.choose (Nat.choose (3 * s + 1) 2) 2 :=
    Nat.choose_le_choose 2 hI_card
  rw [← hBeq, ← hUeq]
  omega

-- Part 6: Putting everything together for the upper bound

lemma upper_bound (b s n : Nat) (hb : 2 ≤ b) (hfeas : feasible b s n) :
    n ≤ 2 * b + max 2 (Nat.choose (Nat.choose (3 * s + 1) 2) 2 + 3 * s) := by
  by_cases hsmall : n ≤ 6
  · omega
  have hn4 : 4 ≤ n := by omega
  rcases hfeas with ⟨C, henc, hw, hCcard⟩
  classical
  let C0 : Finset (Clause b n) := C.filter (fun c => ∀ l ∈ c.1, l.2 = true)
  have hC0_unsat : ¬∃ h : Fin b → Bool, ∀ c ∈ C0, holds c.2 h := by
    rintro ⟨h, hh⟩
    let x0 : Fin n → Bool → Bool := fun _ _ => false
    have hsat : ∀ c ∈ C, (∃ l ∈ c.1, x0 l.1.1 l.1.2 = l.2) ∨ holds c.2 h := by
      intro c hc
      by_cases hpos : ∀ l ∈ c.1, l.2 = true
      · exact Or.inr (hh c (Finset.mem_filter.mpr ⟨hc, hpos⟩))
      · push Not at hpos
        rcases hpos with ⟨l, hl, hlf⟩
        have hfl : l.2 = false := by cases h2 : l.2 <;> simp_all
        exact Or.inl ⟨l, hl, hfl.symm⟩
    obtain ⟨i, hif, _⟩ := (henc x0).mpr ⟨h, hsat⟩
    cases hif
  let UnsatSub := C0.powerset.filter (fun M => ¬∃ h : Fin b → Bool, ∀ c ∈ M, holds c.2 h)
  have hC0mem : C0 ∈ UnsatSub :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl C0), hC0_unsat⟩
  obtain ⟨M, hMmem, hMmin⟩ := Finset.exists_min_image UnsatSub Finset.card ⟨C0, hC0mem⟩
  have hMsub : M ⊆ C0 := Finset.mem_powerset.mp (Finset.mem_filter.mp hMmem).1
  have hMunsat : ¬∃ h : Fin b → Bool, ∀ c ∈ M, holds c.2 h := (Finset.mem_filter.mp hMmem).2
  have hM_eq_of_unsat : ∀ M' ⊆ M, (¬∃ h : Fin b → Bool, ∀ c ∈ M', holds c.2 h) → M' = M := by
    intro M' hsub huns
    have hM'mem : M' ∈ UnsatSub :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hsub.trans hMsub), huns⟩
    exact Finset.eq_of_subset_of_card_le hsub (hMmin M' hM'mem)
  have hMsubC : M ⊆ C := hMsub.trans (Finset.filter_subset _ _)
  have hMpos : ∀ c ∈ M, ∀ l ∈ c.1, l.2 = true := fun c hc => (Finset.mem_filter.mp (hMsub hc)).2
  have hM_inj : ∀ c₁ ∈ M, ∀ c₂ ∈ M, c₁.2 = c₂.2 → c₁ = c₂ := by
    intro c₁ hc₁ c₂ hc₂ heq
    by_contra hne
    have huns : ¬∃ h : Fin b → Bool, ∀ c ∈ M.erase c₂, holds c.2 h := by
      rintro ⟨h, hh⟩
      apply hMunsat
      refine ⟨h, fun c hc => ?_⟩
      by_cases hcc : c = c₂
      · subst hcc
        rw [← heq]
        exact hh c₁ (Finset.mem_erase.mpr ⟨hne, hc₁⟩)
      · exact hh c (Finset.mem_erase.mpr ⟨hcc, hc⟩)
    have hMeq := hM_eq_of_unsat (M.erase c₂) (Finset.erase_subset _ _) huns
    have : c₂ ∈ M.erase c₂ := by rw [hMeq]; exact hc₂
    exact Finset.notMem_erase c₂ M this
  have hM_ne_empty : ∀ c ∈ M, 1 ≤ c.2.card := by
    intro c hc
    by_contra h0
    have hce : c.2 = ∅ := Finset.card_eq_zero.mp (by omega)
    obtain ⟨l, hl, hlv⟩ := no_unsat_empty_hidden hn4 henc hw (hMsubC hc) hce (fun _ _ => false)
    rw [hMpos c hc l hl] at hlv
    cases hlv
  have hM_le3 : ∀ c ∈ M, c.2.card ≤ 3 := fun c hc => by have := hw c (hMsubC hc); omega
  -- Partition M into T, B, U
  let T := M.filter (fun c => c.2.card = 3)
  let B := M.filter (fun c => c.2.card = 2)
  let U := M.filter (fun c => c.2.card = 1)
  -- Bound n ≤ B.card + 2 * U.card
  have hn_le : n ≤ B.card + 2 * U.card := by
    have hcov : (Finset.univ : Finset (Fin n)) ⊆ M.biUnion (fun c => c.1.image (fun l => l.1.1)) := by
      intro i _
      let xi : Fin n → Bool → Bool := fun j _ => decide (j = i)
      have hpair : ∃ k, xi k false = true ∧ xi k true = true := ⟨i, by simp [xi], by simp [xi]⟩
      obtain ⟨h, hh⟩ := (henc xi).mp hpair
      have hex : ∃ c ∈ M, ¬holds c.2 h := by
        by_contra hno; push Not at hno; exact hMunsat ⟨h, hno⟩
      obtain ⟨c, hcM, hch⟩ := hex
      obtain ⟨l, hl, hlv⟩ := (hh c (hMsubC hcM)).resolve_right hch
      rw [hMpos c hcM l hl] at hlv
      simp only [xi, decide_eq_true_eq] at hlv
      exact Finset.mem_biUnion.mpr ⟨c, hcM, Finset.mem_image.mpr ⟨l, hl, hlv⟩⟩
    have hn1 : n ≤ ∑ c ∈ M, c.1.card := by
      calc n = (Finset.univ : Finset (Fin n)).card := by simp
        _ ≤ (M.biUnion (fun c => c.1.image (fun l => l.1.1))).card := Finset.card_le_card hcov
        _ ≤ ∑ c ∈ M, (c.1.image (fun l => l.1.1)).card := Finset.card_biUnion_le
        _ ≤ ∑ c ∈ M, c.1.card := Finset.sum_le_sum fun c _ => Finset.card_image_le
    have hn2 : ∑ c ∈ M, c.1.card ≤ ∑ c ∈ M, (3 - c.2.card) :=
      Finset.sum_le_sum fun c hc => by have := hw c (hMsubC hc); omega
    have hMpart : M = T ∪ (B ∪ U) := by
      ext c
      simp only [T, B, U, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hc
        have h1 := hM_ne_empty c hc
        have h3 := hM_le3 c hc
        rcases (by omega : c.2.card = 3 ∨ c.2.card = 2 ∨ c.2.card = 1) with h | h | h
        · exact Or.inl ⟨hc, h⟩
        · exact Or.inr (Or.inl ⟨hc, h⟩)
        · exact Or.inr (Or.inr ⟨hc, h⟩)
      · rintro (⟨hc, _⟩ | ⟨hc, _⟩ | ⟨hc, _⟩) <;> exact hc
    have hdTB : Disjoint T (B ∪ U) := by
      rw [Finset.disjoint_left]
      intro c h1 h2
      have hc1 := (Finset.mem_filter.mp h1).2
      rcases Finset.mem_union.mp h2 with h2 | h2 <;>
        have hc2 := (Finset.mem_filter.mp h2).2 <;> omega
    have hdBU : Disjoint B U := by
      rw [Finset.disjoint_left]
      intro c h1 h2
      have hc1 := (Finset.mem_filter.mp h1).2
      have hc2 := (Finset.mem_filter.mp h2).2
      omega
    have hsum_eq : ∑ c ∈ M, (3 - c.2.card) = B.card + 2 * U.card := by
      rw [hMpart, Finset.sum_union hdTB, Finset.sum_union hdBU]
      have hT0 : ∑ c ∈ T, (3 - c.2.card) = 0 :=
        Finset.sum_eq_zero fun c hc => by have := (Finset.mem_filter.mp hc).2; omega
      have hB1 : ∑ c ∈ B, (3 - c.2.card) = B.card := by
        calc ∑ c ∈ B, (3 - c.2.card) = ∑ _c ∈ B, 1 :=
              Finset.sum_congr rfl fun c hc => by have := (Finset.mem_filter.mp hc).2; omega
          _ = B.card := by simp
      have hU2 : ∑ c ∈ U, (3 - c.2.card) = 2 * U.card := by
        calc ∑ c ∈ U, (3 - c.2.card) = ∑ _c ∈ U, 2 :=
              Finset.sum_congr rfl fun c hc => by have := (Finset.mem_filter.mp hc).2; omega
          _ = 2 * U.card := by simp [Nat.mul_comm]
      omega
    omega
  -- Bound T.card ≤ s
  have hT_le_s : T.card ≤ s := by
    let Cpos := C.filter (fun c => 1 ≤ (posLits c).card)
    have h2n : 2 * n ≤ Cpos.card := two_mul_n_le_pos_clauses hn4 henc hw
    have hdisj : Disjoint T Cpos := by
      rw [Finset.disjoint_left]
      intro c hcT hcP
      have hc3 : c.2.card = 3 := (Finset.mem_filter.mp hcT).2
      have hcM : c ∈ M := (Finset.mem_filter.mp hcT).1
      have hwc := hw c (hMsubC hcM)
      have hpos := (Finset.mem_filter.mp hcP).2
      have hpl := posLits_card_le c
      omega
    have hsub : T ∪ Cpos ⊆ C :=
      Finset.union_subset ((Finset.filter_subset _ _).trans hMsubC) (Finset.filter_subset _ _)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    omega
  -- Extract pure hidden sets HT, HB, HU
  let HT : Finset (Hidden b) := T.image Prod.snd
  let HB : Finset (Hidden b) := B.image Prod.snd
  let HU : Finset (Lit b) := Finset.univ.filter (fun l => ({l} : Hidden b) ∈ U.image Prod.snd)
  have hHT_card : HT.card = T.card :=
    Finset.card_image_of_injOn (fun c₁ h1 c₂ h2 heq =>
      hM_inj c₁ (Finset.filter_subset _ _ h1) c₂ (Finset.filter_subset _ _ h2) heq)
  have hHB_card : HB.card = B.card :=
    Finset.card_image_of_injOn (fun c₁ h1 c₂ h2 heq =>
      hM_inj c₁ (Finset.filter_subset _ _ h1) c₂ (Finset.filter_subset _ _ h2) heq)
  have hHU_card : HU.card = U.card := by
    have hbij : HU.image (fun a : Lit b => ({a} : Finset (Lit b))) = U.image Prod.snd := by
      ext D
      simp only [Finset.mem_image, HU, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨l, hl, rfl⟩; exact hl
      · rintro ⟨c, hcU, rfl⟩
        obtain ⟨l, hl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hcU).2
        exact ⟨l, ⟨c, hcU, hl⟩, hl.symm⟩
    have h1 : HU.card = (HU.image (fun a : Lit b => ({a} : Finset (Lit b)))).card :=
      (Finset.card_image_of_injective HU (fun a d h => Finset.singleton_injective h)).symm
    have h2 : (U.image Prod.snd).card = U.card :=
      Finset.card_image_of_injOn (fun c₁ h1 c₂ h2 heq =>
        hM_inj c₁ (Finset.filter_subset _ _ h1) c₂ (Finset.filter_subset _ _ h2) heq)
    rw [h1, hbij, h2]
  have hHTw : ∀ D ∈ HT, D.card ≤ 3 := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨c, hc, rfl⟩
    have := (Finset.mem_filter.mp hc).2; omega
  have hHB2 : ∀ D ∈ HB, D.card = 2 := by
    intro D hD
    rcases Finset.mem_image.mp hD with ⟨c, hc, rfl⟩
    exact (Finset.mem_filter.mp hc).2
  have hunsat_H : ¬∃ h : Fin b → Bool,
      (∀ D ∈ HT, holds D h) ∧ (∀ D ∈ HB, holds D h) ∧ (∀ u ∈ HU, h u.1 = u.2) := by
    rintro ⟨h, h1, h2, h3⟩
    apply hMunsat
    refine ⟨h, fun c hc => ?_⟩
    have hc1 := hM_ne_empty c hc
    have hc3 := hM_le3 c hc
    by_cases h3c : c.2.card = 3
    · exact h1 c.2 (Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, h3c⟩, rfl⟩)
    · by_cases h2c : c.2.card = 2
      · exact h2 c.2 (Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, h2c⟩, rfl⟩)
      · have h1c : c.2.card = 1 := by omega
        obtain ⟨l, hl⟩ := Finset.card_eq_one.mp h1c
        have hlHU : l ∈ HU := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.mem_image.mpr ⟨c, Finset.mem_filter.mpr ⟨hc, h1c⟩, hl⟩⟩
        rw [hl]
        exact ⟨l, Finset.mem_singleton_self l, h3 l hlHU⟩
  have hmin_H : ∀ HT' ⊆ HT, ∀ HB' ⊆ HB, ∀ HU' ⊆ HU,
      (¬∃ h : Fin b → Bool,
        (∀ D ∈ HT', holds D h) ∧ (∀ D ∈ HB', holds D h) ∧ (∀ u ∈ HU', h u.1 = u.2)) →
      HT' = HT ∧ HB' = HB ∧ HU' = HU := by
    intro HT' hTs HB' hBs HU' hUs huns'
    let M' := T.filter (fun c => c.2 ∈ HT') ∪ B.filter (fun c => c.2 ∈ HB') ∪
      U.filter (fun c => ∃ l ∈ HU', c.2 = {l})
    have hM'sub : M' ⊆ M := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) ?_
      · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
      · exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hM'uns : ¬∃ h : Fin b → Bool, ∀ c ∈ M', holds c.2 h := by
      rintro ⟨h, hh⟩
      apply huns'
      refine ⟨h, ?_, ?_, ?_⟩
      · intro D hD
        rcases Finset.mem_image.mp (hTs hD) with ⟨c, hcT, rfl⟩
        exact hh c (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcT, hD⟩)))
      · intro D hD
        rcases Finset.mem_image.mp (hBs hD) with ⟨c, hcB, rfl⟩
        exact hh c (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcB, hD⟩)))
      · intro u hu
        have huU := (Finset.mem_filter.mp (hUs hu)).2
        rcases Finset.mem_image.mp huU with ⟨c, hcU, hce⟩
        have hholds := hh c (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcU, u, hu, hce⟩))
        rw [hce] at hholds
        rcases hholds with ⟨l, hl, hlv⟩
        rw [Finset.mem_singleton.mp hl] at hlv
        exact hlv
    have hMeq := hM_eq_of_unsat M' hM'sub hM'uns
    refine ⟨Finset.Subset.antisymm hTs ?_, Finset.Subset.antisymm hBs ?_, Finset.Subset.antisymm hUs ?_⟩
    · intro D hD
      rcases Finset.mem_image.mp hD with ⟨c, hcT, rfl⟩
      have hcM' : c ∈ M' := by rw [hMeq]; exact (Finset.mem_filter.mp hcT).1
      have hc3 : c.2.card = 3 := (Finset.mem_filter.mp hcT).2
      rcases Finset.mem_union.mp hcM' with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · exact (Finset.mem_filter.mp h1).2
        · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2; omega
      · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h3).1).2; omega
    · intro D hD
      rcases Finset.mem_image.mp hD with ⟨c, hcB, rfl⟩
      have hcM' : c ∈ M' := by rw [hMeq]; exact (Finset.mem_filter.mp hcB).1
      have hc2 : c.2.card = 2 := (Finset.mem_filter.mp hcB).2
      rcases Finset.mem_union.mp hcM' with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2; omega
        · exact (Finset.mem_filter.mp h2).2
      · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h3).1).2; omega
    · intro u hu
      rcases Finset.mem_image.mp (Finset.mem_filter.mp hu).2 with ⟨c, hcU, hce⟩
      have hcM' : c ∈ M' := by rw [hMeq]; exact (Finset.mem_filter.mp hcU).1
      have hc1 : c.2.card = 1 := (Finset.mem_filter.mp hcU).2
      rcases Finset.mem_union.mp hcM' with h12 | h3
      · rcases Finset.mem_union.mp h12 with h1 | h2
        · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2; omega
        · have := (Finset.mem_filter.mp (Finset.mem_filter.mp h2).1).2; omega
      · rcases (Finset.mem_filter.mp h3).2 with ⟨l, hl, hcl⟩
        have : u = l := Finset.singleton_injective (hce.symm.trans hcl)
        subst this; exact hl
  -- Split on HT = ∅ vs HT.Nonempty
  by_cases hHTe : HT = ∅
  · have huns_bin : ¬∃ h : Fin b → Bool, (∀ D ∈ HB, holds D h) ∧ (∀ u ∈ HU, h u.1 = u.2) := by
      rintro ⟨h, hB, hU⟩
      exact hunsat_H ⟨h, fun D hD => by rw [hHTe] at hD; exact False.elim (Finset.notMem_empty _ hD), hB, hU⟩
    have hmin_bin : ∀ HB' ⊆ HB, ∀ HU' ⊆ HU,
        (¬∃ h : Fin b → Bool, (∀ D ∈ HB', holds D h) ∧ (∀ u ∈ HU', h u.1 = u.2)) →
        HB' = HB ∧ HU' = HU := by
      intro HB' hBs HU' hUs huns'
      have hres := hmin_H ∅ (Finset.empty_subset _) HB' hBs HU' hUs (by
        rintro ⟨h, _, hB', hU'⟩; exact huns' ⟨h, hB', hU'⟩)
      exact ⟨hres.2.1, hres.2.2⟩
    have hbin := binary_only_bound hb HB hHB2 HU huns_bin hmin_bin
    omega
  · have hHTne : HT.Nonempty := Finset.nonempty_iff_ne_empty.mpr hHTe
    have htern := ternary_present_bound (s := s) hb HT HB HU hHTne (by rw [hHT_card]; exact hT_le_s) hHTw hHB2 hunsat_H hmin_H
    omega

end PEqualNP.Outside.L_lib_1175

theorem PEqualNP.Outside.L_lib_1175 : ∀ b s : Nat, 2 ≤ b →
  let feasible := fun n : Nat =>
    let Hidden := Finset (Fin b × Bool)
    let Clause := Finset ((Fin n × Bool) × Bool) × Hidden
    let holds := fun (D : Hidden) (h : Fin b → Bool) => ∃ l ∈ D, h l.1=l.2
    let encodes := fun (C : Finset Clause) =>
      ∀ x : Fin n → Bool → Bool, (∃ i, x i false=true ∧ x i true=true) ↔
        ∃ h : Fin b → Bool, ∀ c ∈ C,
          (∃ l ∈ c.1, x l.1.1 l.1.2=l.2) ∨ holds c.2 h
    (∃ C : Finset Clause, encodes C ∧ (∀ c ∈ C, c.1.card+c.2.card ≤ 3) ∧ C.card ≤ 2*n+s)
  let p := Nat.choose (3*s+1) 2
  feasible (2*b) ∧ ∀ n : Nat, feasible n → n ≤ 2*b + max 2 (Nat.choose p 2 + 3*s) := by
  intro b s hb
  exact ⟨PEqualNP.Outside.L_lib_1175.feasible_two_mul b s hb,
         fun n hf => PEqualNP.Outside.L_lib_1175.upper_bound b s n hb hf⟩
