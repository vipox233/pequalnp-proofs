import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_269_aux

open PEqualNP.ProofComplexity
open Classical

abbrev V (n m : ℕ) : Type := Fin n ⊕ (Fin m × ℕ)

def lit {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (j : ℕ) : Literal (V n m) :=
  if j = 0 then ((Sum.inl (src e).1 : V n m), (src e).2)
  else if j = len e then ((Sum.inl (dst e).1 : V n m), (dst e).2)
  else ((Sum.inr (e, j) : V n m), true)

def stepClause {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (j : ℕ) : Clause (V n m) :=
  {((lit src dst len e j).1, !(lit src dst len e j).2), lit src dst len e (j + 1)}

def bigSet {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ) :
    Set (Clause (V n m)) :=
  {C | ∃ e j, j < len e ∧ C = stepClause src dst len e j}

def baseClause {n m : ℕ} (src dst : Fin m → Fin n × Bool)
    (e : Fin m) : Clause (V n m) :=
  {((Sum.inl (src e).1 : V n m), !(src e).2), ((Sum.inl (dst e).1 : V n m), (dst e).2)}

def chainClause {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (k : ℕ) : Clause (V n m) :=
  {((Sum.inl (src e).1 : V n m), !(src e).2), lit src dst len e k}

lemma isDerivation_append {α : Type} [DecidableEq α] {F : Set (Clause α)}
    {π1 π2 : List (Clause α)}
    (h1 : IsDerivation F π1) (h2 : IsDerivation F π2) :
    IsDerivation F (π1 ++ π2) := by
  induction h1 with
  | nil => exact h2
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hA hB hres ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hA) (List.mem_append_left _ hB) hres

lemma isDerivation_of_ax_or_res {α : Type} [DecidableEq α] {F G : Set (Clause α)}
    {π pref : List (Clause α)}
    (hπ : IsDerivation F π) (hpref : IsDerivation G pref)
    (hFG : ∀ C ∈ F, C ∈ G ∨ ∃ A ∈ pref, ∃ B ∈ pref, IsResolvent A B C) :
    IsDerivation G (π ++ pref) := by
  induction hπ with
  | nil => exact hpref
  | ax _ hC ih =>
    rcases hFG _ hC with hG | ⟨A, hA, B, hB, hres⟩
    · exact IsDerivation.ax ih hG
    · exact IsDerivation.res ih (List.mem_append_right _ hA) (List.mem_append_right _ hB) hres
  | res _ hA hB hres ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hA) (List.mem_append_left _ hB) hres

lemma lit_zero {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ) (e : Fin m) :
    lit src dst len e 0 = ((Sum.inl (src e).1 : V n m), (src e).2) := by
  simp [lit]

lemma lit_len {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ) (e : Fin m)
    (hlen : 0 < len e) :
    lit src dst len e (len e) = ((Sum.inl (dst e).1 : V n m), (dst e).2) := by
  have hne : len e ≠ 0 := Nat.ne_of_gt hlen
  simp [lit, hne]

lemma lit_mid {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ) (e : Fin m)
    {k : ℕ} (hk0 : 0 < k) (hk : k < len e) :
    lit src dst len e k = ((Sum.inr (e, k) : V n m), true) := by
  have h1 : k ≠ 0 := Nat.ne_of_gt hk0
  have h2 : k ≠ len e := Nat.ne_of_lt hk
  simp [lit, h1, h2]

lemma chainClause_one {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ) (e : Fin m) :
    chainClause src dst len e 1 = stepClause src dst len e 0 := by
  simp [chainClause, stepClause, lit_zero]

lemma chainClause_len {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ) (e : Fin m)
    (hlen : 0 < len e) :
    chainClause src dst len e (len e) = baseClause src dst e := by
  simp [chainClause, baseClause, lit_len src dst len e hlen]

lemma stepClause_zero_eq_base {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (hlen : len e = 1) :
    stepClause src dst len e 0 = baseClause src dst e := by
  rw [← chainClause_one, ← hlen, chainClause_len src dst len e (by omega)]

lemma isResolvent_chain_step {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) {k : ℕ} (hk0 : 0 < k) (hk : k < len e) :
    IsResolvent (chainClause src dst len e k) (stepClause src dst len e k)
      (chainClause src dst len e (k + 1)) := by
  refine ⟨Sum.inr (e, k), ?_, ?_, ?_⟩
  · rw [chainClause, lit_mid src dst len e hk0 hk]
    simp
  · rw [stepClause, lit_mid src dst len e hk0 hk]
    simp
  · have hlitk : lit src dst len e k = ((Sum.inr (e, k) : V n m), true) :=
      lit_mid src dst len e hk0 hk
    have hne1 : ((Sum.inl (src e).1 : V n m), !(src e).2) ≠ ((Sum.inr (e, k) : V n m), true) := by
      simp
    have hne2 : lit src dst len e (k + 1) ≠ ((Sum.inr (e, k) : V n m), false) := by
      by_cases hkl : k + 1 = len e
      · rw [hkl, lit_len src dst len e (by omega)]
        simp
      · rw [lit_mid src dst len e (by omega) (by omega)]
        simp
    ext l
    simp only [chainClause, stepClause, hlitk, Bool.not_true, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · left; exact ⟨hne1, Or.inl rfl⟩
      · right; exact ⟨hne2, Or.inr rfl⟩
    · rintro (⟨hneq, rfl | rfl⟩ | ⟨hneq, rfl | rfl⟩)
      · exact Or.inl rfl
      · exact absurd rfl hneq
      · exact absurd rfl hneq
      · exact Or.inr rfl

def buildChain {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) : ℕ → List (Clause (V n m))
  | 0 => []
  | 1 => [stepClause src dst len e 1, stepClause src dst len e 0]
  | t + 2 =>
      stepClause src dst len e (t + 2) ::
      chainClause src dst len e (t + 2) ::
      buildChain src dst len e (t + 1)

lemma buildChain_length {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) (t : ℕ) :
    (buildChain src dst len e t).length = 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    cases t with
    | zero => rfl
    | succ t' =>
      simp only [buildChain, List.length_cons, ih]
      omega

lemma buildChain_mem {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) {t : ℕ} (ht : 1 ≤ t) :
    chainClause src dst len e t ∈ buildChain src dst len e t ∧
    stepClause src dst len e t ∈ buildChain src dst len e t := by
  cases t with
  | zero => omega
  | succ t' =>
    cases t' with
    | zero =>
      simp [buildChain, chainClause_one]
    | succ t'' =>
      simp [buildChain]

lemma buildChain_derivation {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (e : Fin m) {t : ℕ} (ht : t < len e) :
    IsDerivation (bigSet src dst len) (buildChain src dst len e t) := by
  induction t with
  | zero => exact IsDerivation.nil
  | succ t ih =>
    cases t with
    | zero =>
      have h0 : stepClause src dst len e 0 ∈ bigSet src dst len :=
        ⟨e, 0, by omega, rfl⟩
      have h1 : stepClause src dst len e 1 ∈ bigSet src dst len :=
        ⟨e, 1, ht, rfl⟩
      exact IsDerivation.ax (IsDerivation.ax IsDerivation.nil h0) h1
    | succ t' =>
      have hprev := ih (by omega)
      have hmem := buildChain_mem src dst len e (t := t' + 1) (by omega)
      have hres := isResolvent_chain_step src dst len e (k := t' + 1) (by omega) (by omega)
      have hder1 : IsDerivation (bigSet src dst len)
          (chainClause src dst len e (t' + 2) :: buildChain src dst len e (t' + 1)) :=
        IsDerivation.res hprev hmem.1 hmem.2 hres
      have hax : stepClause src dst len e (t' + 2) ∈ bigSet src dst len :=
        ⟨e, t' + 2, ht, rfl⟩
      exact IsDerivation.ax hder1 hax

lemma build_pref_for_set {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (hlen : ∀ e, 0 < len e) (S : Finset (Fin m)) :
    ∃ pref : List (Clause (V n m)),
      IsDerivation (bigSet src dst len) pref ∧
      pref.length = 2 * S.sum (fun e => len e - 1) ∧
      ∀ e ∈ S, baseClause src dst e ∈ bigSet src dst len ∨
        ∃ A ∈ pref, ∃ B ∈ pref, IsResolvent A B (baseClause src dst e) := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨[], IsDerivation.nil, by simp, by simp⟩
  | @insert e S he ih =>
    rcases ih with ⟨pref, hpref, hlen_pref, hS⟩
    refine ⟨buildChain src dst len e (len e - 1) ++ pref, ?_, ?_, ?_⟩
    · exact isDerivation_append (buildChain_derivation src dst len e (by have := hlen e; omega)) hpref
    · rw [List.length_append, buildChain_length, hlen_pref, Finset.sum_insert he, mul_add]
    · intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with hxe | hxS
      · subst x
        by_cases h1 : len e = 1
        · left
          refine ⟨e, 0, by omega, ?_⟩
          exact (stepClause_zero_eq_base src dst len e h1).symm
        · right
          have hge2 : 2 ≤ len e := by have := hlen e; omega
          have hm := buildChain_mem src dst len e (t := len e - 1) (by omega)
          have hres := isResolvent_chain_step src dst len e (k := len e - 1) (by omega) (by omega)
          have hsum : len e - 1 + 1 = len e := by omega
          rw [hsum, chainClause_len src dst len e (hlen e)] at hres
          exact ⟨chainClause src dst len e (len e - 1), List.mem_append_left _ hm.1,
            stepClause src dst len e (len e - 1), List.mem_append_left _ hm.2, hres⟩
      · rcases hS x hxS with hbig | ⟨A, hA, B, hB, hres⟩
        · exact Or.inl hbig
        · exact Or.inr ⟨A, List.mem_append_right _ hA, B, List.mem_append_right _ hB, hres⟩

lemma backward_dir {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (hlen : ∀ e, 0 < len e) (K : ℕ)
    (S : Finset (Fin m)) (π : List (Clause (V n m)))
    (href : IsRefutation {C | ∃ idx ∈ S, C = baseClause src dst idx} π)
    (hK : π.length + 2 * S.sum (fun idx => len idx - 1) ≤ K) :
    ∃ π', IsRefutation (bigSet src dst len) π' ∧ π'.length ≤ K := by
  rcases build_pref_for_set src dst len hlen S with ⟨pref, hpref, hlen_pref, hS⟩
  refine ⟨π ++ pref, ⟨?_, List.mem_append_left _ href.2⟩, ?_⟩
  · refine isDerivation_of_ax_or_res href.1 hpref ?_
    rintro C ⟨e, he, rfl⟩
    exact hS e he
  · rw [List.length_append, hlen_pref]
    exact hK

def negLit {α : Type} (l : Literal α) : Literal α := (l.1, !l.2)

@[simp] lemma negLit_negLit {α : Type} (l : Literal α) : negLit (negLit l) = l := by
  cases l
  simp [negLit]

lemma negLit_ne_self {α : Type} (l : Literal α) : negLit l ≠ l := by
  cases l with
  | mk v b =>
    cases b <;> simp [negLit]

def IsTaut {α : Type} (C : Clause α) : Prop :=
  ∃ l ∈ C, negLit l ∈ C

lemma not_isTaut_empty {α : Type} : ¬ IsTaut (∅ : Clause α) := by
  rintro ⟨l, hl, _⟩
  exact Finset.notMem_empty l hl

lemma isTaut_mono {α : Type} {A B : Clause α} (h : A ⊆ B) (hA : IsTaut A) : IsTaut B := by
  rcases hA with ⟨l, hl1, hl2⟩
  exact ⟨l, h hl1, h hl2⟩

lemma mem_of_isTaut_insert {α : Type} [DecidableEq α] {p : Literal α} {A : Clause α}
    (hins : IsTaut (insert p A)) (hA : ¬ IsTaut A) : negLit p ∈ A := by
  rcases hins with ⟨l, hl1, hl2⟩
  rw [Finset.mem_insert] at hl1 hl2
  rcases hl1 with rfl | hl1A
  · rcases hl2 with heq | hl2A
    · exact absurd heq (negLit_ne_self l)
    · exact hl2A
  · rcases hl2 with heq | hl2A
    · have : negLit p = l := by rw [← heq, negLit_negLit]
      rw [this]
      exact hl1A
    · exact absurd ⟨l, hl1A, hl2A⟩ hA

lemma res_image_decomp {α : Type} [DecidableEq α] (f : Literal α → Literal α)
    (hf : ∀ l, f (negLit l) = negLit (f l))
    {C D R : Clause α} {v : α}
    (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D)
    (hR : R = C.erase (v, true) ∪ D.erase (v, false)) :
    let p := f (v, true)
    let A := (C.erase (v, true)).image f
    let B := (D.erase (v, false)).image f
    C.image f = insert p A ∧
    D.image f = insert (negLit p) B ∧
    R.image f = A ∪ B := by
  have hC : C = insert (v, true) (C.erase (v, true)) := (Finset.insert_erase hvC).symm
  have hD : D = insert (v, false) (D.erase (v, false)) := (Finset.insert_erase hvD).symm
  have hneg : f (v, false) = negLit (f (v, true)) := by
    have : ((v, false) : Literal α) = negLit (v, true) := rfl
    rw [this, hf]
  refine ⟨?_, ?_, ?_⟩
  · conv_lhs => rw [hC]
    rw [Finset.image_insert]
  · conv_lhs => rw [hD]
    rw [Finset.image_insert, hneg]
  · rw [hR, Finset.image_union]

lemma res_image_not_both_taut {α : Type} [DecidableEq α] (f : Literal α → Literal α)
    (hf : ∀ l, f (negLit l) = negLit (f l))
    {C D R : Clause α} {v : α}
    (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D)
    (hR : R = C.erase (v, true) ∪ D.erase (v, false))
    (hnt : ¬ IsTaut (R.image f)) :
    ¬ (IsTaut (C.image f) ∧ IsTaut (D.image f)) := by
  have hdec := res_image_decomp f hf hvC hvD hR
  rintro ⟨htC, htD⟩
  have hntA : ¬ IsTaut ((C.erase (v, true)).image f) :=
    fun h => hnt (by rw [hdec.2.2]; exact isTaut_mono Finset.subset_union_left h)
  have hntB : ¬ IsTaut ((D.erase (v, false)).image f) :=
    fun h => hnt (by rw [hdec.2.2]; exact isTaut_mono Finset.subset_union_right h)
  rw [hdec.1] at htC
  rw [hdec.2.1] at htD
  have h1 : negLit (f (v, true)) ∈ (C.erase (v, true)).image f :=
    mem_of_isTaut_insert htC hntA
  have h2 : negLit (negLit (f (v, true))) ∈ (D.erase (v, false)).image f :=
    mem_of_isTaut_insert htD hntB
  rw [negLit_negLit] at h2
  apply hnt
  rw [hdec.2.2]
  exact ⟨f (v, true), Finset.mem_union_right _ h2, Finset.mem_union_left _ h1⟩

lemma res_image_sub_right {α : Type} [DecidableEq α] (f : Literal α → Literal α)
    (hf : ∀ l, f (negLit l) = negLit (f l))
    {C D R : Clause α} {v : α}
    (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D)
    (hR : R = C.erase (v, true) ∪ D.erase (v, false))
    (hnt : ¬ IsTaut (R.image f)) (htC : IsTaut (C.image f)) :
    D.image f ⊆ R.image f := by
  have hdec := res_image_decomp f hf hvC hvD hR
  have hntA : ¬ IsTaut ((C.erase (v, true)).image f) :=
    fun h => hnt (by rw [hdec.2.2]; exact isTaut_mono Finset.subset_union_left h)
  rw [hdec.1] at htC
  have h1 : negLit (f (v, true)) ∈ (C.erase (v, true)).image f :=
    mem_of_isTaut_insert htC hntA
  rw [hdec.2.1, hdec.2.2]
  intro l hl
  rw [Finset.mem_insert] at hl
  rcases hl with rfl | hlB
  · exact Finset.mem_union_left _ h1
  · exact Finset.mem_union_right _ hlB

lemma res_image_sub_left {α : Type} [DecidableEq α] (f : Literal α → Literal α)
    (hf : ∀ l, f (negLit l) = negLit (f l))
    {C D R : Clause α} {v : α}
    (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D)
    (hR : R = C.erase (v, true) ∪ D.erase (v, false))
    (hnt : ¬ IsTaut (R.image f)) (htD : IsTaut (D.image f)) :
    C.image f ⊆ R.image f := by
  have hdec := res_image_decomp f hf hvC hvD hR
  have hntB : ¬ IsTaut ((D.erase (v, false)).image f) :=
    fun h => hnt (by rw [hdec.2.2]; exact isTaut_mono Finset.subset_union_right h)
  rw [hdec.2.1] at htD
  have h2 : f (v, true) ∈ (D.erase (v, false)).image f := by
    have := mem_of_isTaut_insert htD hntB
    rwa [negLit_negLit] at this
  rw [hdec.1, hdec.2.2]
  intro l hl
  rw [Finset.mem_insert] at hl
  rcases hl with rfl | hlA
  · exact Finset.mem_union_right _ h2
  · exact Finset.mem_union_left _ hlA

lemma res_image_sub_step {α : Type} [DecidableEq α] (f : Literal α → Literal α)
    (hf : ∀ l, f (negLit l) = negLit (f l))
    {C D R C' D' : Clause α} {v : α}
    (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D)
    (hR : R = C.erase (v, true) ∪ D.erase (v, false))
    (hC' : C' ⊆ C.image f) (hD' : D' ⊆ D.image f) :
    C' ⊆ R.image f ∨ D' ⊆ R.image f ∨
    ∃ R', (IsResolvent C' D' R' ∨ IsResolvent D' C' R') ∧ R' ⊆ R.image f := by
  have hdec := res_image_decomp f hf hvC hvD hR
  set p := f (v, true)
  set A := (C.erase (v, true)).image f
  set B := (D.erase (v, false)).image f
  rw [hdec.1] at hC'
  rw [hdec.2.1] at hD'
  rw [hdec.2.2]
  by_cases hpC : p ∈ C'
  · by_cases hnpD : negLit p ∈ D'
    · right; right
      refine ⟨C'.erase p ∪ D'.erase (negLit p), ?_, ?_⟩
      · rcases hp : p with ⟨w, b⟩
        cases b
        · right
          refine ⟨w, ?_, ?_, ?_⟩
          · simpa [negLit, hp] using hnpD
          · simpa [hp] using hpC
          · rw [Finset.union_comm]; simp [negLit]
        · left
          refine ⟨w, ?_, ?_, ?_⟩
          · simpa [hp] using hpC
          · simpa [negLit, hp] using hnpD
          · simp [negLit]
      · intro l hl
        rw [Finset.mem_union] at hl ⊢
        rcases hl with hl1 | hl2
        · left
          have h1 := Finset.mem_erase.mp hl1
          have h2 := Finset.mem_insert.mp (hC' h1.2)
          exact h2.resolve_left h1.1
        · right
          have h1 := Finset.mem_erase.mp hl2
          have h2 := Finset.mem_insert.mp (hD' h1.2)
          exact h2.resolve_left h1.1
    · right; left
      intro l hl
      have h1 := Finset.mem_insert.mp (hD' hl)
      have hne : l ≠ negLit p := fun heq => hnpD (heq ▸ hl)
      exact Finset.mem_union_right _ (h1.resolve_left hne)
  · left
    intro l hl
    have h1 := Finset.mem_insert.mp (hC' hl)
    have hne : l ≠ p := fun heq => hpC (heq ▸ hl)
    exact Finset.mem_union_left _ (h1.resolve_left hne)

def substLit {n m : ℕ} (src dst : Fin m → Fin n × Bool) (bp : Fin m → ℕ) :
    Literal (V n m) → Literal (V n m)
  | (Sum.inl v, b) => (Sum.inl v, b)
  | (Sum.inr (e, j), b) =>
      if j ≤ bp e then (Sum.inl (src e).1, if b then (src e).2 else !(src e).2)
      else (Sum.inl (dst e).1, if b then (dst e).2 else !(dst e).2)

def substClause {n m : ℕ} (src dst : Fin m → Fin n × Bool) (bp : Fin m → ℕ)
    (C : Clause (V n m)) : Clause (V n m) :=
  C.image (substLit src dst bp)

lemma substLit_neg {n m : ℕ} (src dst : Fin m → Fin n × Bool) (bp : Fin m → ℕ)
    (l : Literal (V n m)) :
    substLit src dst bp (negLit l) = negLit (substLit src dst bp l) := by
  rcases l with ⟨v | ⟨e, j⟩, b⟩
  · simp [substLit, negLit]
  · cases b <;> by_cases h : j ≤ bp e <;> simp [substLit, negLit, h]

lemma substLit_lit_le {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (bp : Fin m → ℕ) (e : Fin m) {k : ℕ} (hk : k ≤ bp e) (hbp : bp e < len e) :
    substLit src dst bp (lit src dst len e k) = ((Sum.inl (src e).1 : V n m), (src e).2) := by
  by_cases hk0 : k = 0
  · subst hk0
    simp [lit, substLit]
  · have hkl : k ≠ len e := by omega
    simp [lit, hk0, hkl, substLit, hk]

lemma substLit_lit_gt {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (bp : Fin m → ℕ) (e : Fin m) {k : ℕ} (hk : bp e < k) (hkl : k ≤ len e) :
    substLit src dst bp (lit src dst len e k) = ((Sum.inl (dst e).1 : V n m), (dst e).2) := by
  have hk0 : k ≠ 0 := by omega
  by_cases hkeq : k = len e
  · subst hkeq
    simp [lit, hk0, substLit]
  · have hnotle : ¬ k ≤ bp e := by omega
    simp [lit, hk0, hkeq, substLit, hnotle]

lemma substClause_step_taut {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (bp : Fin m → ℕ) (e : Fin m) {j : ℕ} (hj : j < len e) (hbp : bp e < len e)
    (hne : j ≠ bp e) :
    IsTaut (substClause src dst bp (stepClause src dst len e j)) := by
  have himg : substClause src dst bp (stepClause src dst len e j) =
      {negLit (substLit src dst bp (lit src dst len e j)),
       substLit src dst bp (lit src dst len e (j + 1))} := by
    have hneg : ((lit src dst len e j).1, !(lit src dst len e j).2) =
        negLit (lit src dst len e j) := rfl
    simp [substClause, stepClause, hneg, substLit_neg]
  rw [himg]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 := substLit_lit_le src dst len bp e (k := j) (by omega) hbp
    have h2 := substLit_lit_le src dst len bp e (k := j + 1) (by omega) hbp
    rw [h1, h2]
    exact ⟨((Sum.inl (src e).1 : V n m), (src e).2), by simp, by simp⟩
  · have h1 := substLit_lit_gt src dst len bp e (k := j) hgt (by omega)
    have h2 := substLit_lit_gt src dst len bp e (k := j + 1) (by omega) (by omega)
    rw [h1, h2]
    exact ⟨((Sum.inl (dst e).1 : V n m), (dst e).2), by simp, by simp⟩

lemma substClause_step_eq {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (bp : Fin m → ℕ) (e : Fin m) (hbp : bp e < len e) :
    substClause src dst bp (stepClause src dst len e (bp e)) = baseClause src dst e := by
  have hneg : ((lit src dst len e (bp e)).1, !(lit src dst len e (bp e)).2) =
      negLit (lit src dst len e (bp e)) := rfl
  have h1 := substLit_lit_le src dst len bp e (k := bp e) (le_refl _) hbp
  have h2 := substLit_lit_gt src dst len bp e (k := bp e + 1) (by omega) (by omega)
  rw [substClause, stepClause, hneg]
  simp only [Finset.image_insert, Finset.image_singleton, substLit_neg, h1, h2]
  rfl

lemma stepClause_inj_pos {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    {e1 e2 : Fin m} {j1 j2 : ℕ}
    (hj1 : 1 ≤ j1) (hj1l : j1 < len e1) (hj2 : 1 ≤ j2) (hj2l : j2 < len e2)
    (heq : stepClause src dst len e1 j1 = stepClause src dst len e2 j2) :
    e1 = e2 ∧ j1 = j2 := by
  have hmem1 : ((Sum.inr (e1, j1) : V n m), false) ∈ stepClause src dst len e1 j1 := by
    rw [stepClause, lit_mid src dst len e1 (by omega) hj1l]
    simp
  rw [heq] at hmem1
  rw [stepClause, lit_mid src dst len e2 (by omega) hj2l] at hmem1
  simp only [Bool.not_true, Finset.mem_insert, Finset.mem_singleton] at hmem1
  rcases hmem1 with h | h
  · simp only [Prod.mk.injEq, Sum.inr.injEq, and_true] at h
    exact h
  · exfalso
    by_cases hlast : j2 + 1 = len e2
    · rw [hlast, lit_len src dst len e2 (by omega)] at h
      simp at h
    · rw [lit_mid src dst len e2 (by omega) (by omega)] at h
      simp at h

inductive DAGStep (α : Type) (L : ℕ) where
  | ax : DAGStep α L
  | res (p1 p2 : Fin L) (v : α) : DAGStep α L

def liftStep {α : Type} {L : ℕ} : DAGStep α L → DAGStep α (L + 1)
  | .ax => .ax
  | .res p1 p2 v => .res p1.castSucc p2.castSucc v

def isAx {α : Type} {L : ℕ} : DAGStep α L → Bool
  | .ax => true
  | .res _ _ _ => false

structure ProofDAG (α : Type) [DecidableEq α] (F : Set (Clause α)) where
  size : ℕ
  clause : Fin size → Clause α
  step : Fin size → DAGStep α size
  valid : ∀ i : Fin size, match step i with
    | .ax => clause i ∈ F
    | .res p1 p2 v =>
        p1.val < i.val ∧ p2.val < i.val ∧
        (v, true) ∈ clause p1 ∧ (v, false) ∈ clause p2 ∧
        clause i = (clause p1).erase (v, true) ∪ (clause p2).erase (v, false)

lemma dag_of_derivation {α : Type} [DecidableEq α] {F : Set (Clause α)}
    {π : List (Clause α)} (hπ : IsDerivation F π) :
    ∃ D : ProofDAG α F, D.size = π.length ∧ ∀ C ∈ π, ∃ i : Fin D.size, D.clause i = C := by
  induction hπ with
  | nil =>
    refine ⟨⟨0, Fin.elim0, Fin.elim0, fun i => Fin.elim0 i⟩, rfl, ?_⟩
    intro C hC
    cases hC
  | @ax π C _ hC ih =>
    rcases ih with ⟨D, hsize, hmem⟩
    let D' : ProofDAG α F :=
      { size := D.size + 1
        clause := Fin.lastCases C D.clause
        step := Fin.lastCases DAGStep.ax (fun j => liftStep (D.step j))
        valid := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · simp [hC]
          · intro j
            simp only [Fin.lastCases_castSucc]
            have hv := D.valid j
            cases hs : D.step j with
            | ax =>
              rw [hs] at hv
              simpa [liftStep] using hv
            | res p1 p2 v =>
              rw [hs] at hv
              simpa [liftStep] using hv }
    refine ⟨D', by simp [D', hsize], ?_⟩
    intro X hX
    rw [List.mem_cons] at hX
    rcases hX with rfl | hXπ
    · exact ⟨Fin.last D.size, by simp [D']⟩
    · rcases hmem X hXπ with ⟨j, rfl⟩
      exact ⟨j.castSucc, by simp [D']⟩
  | @res π A B R _ hA hB hres ih =>
    rcases ih with ⟨D, hsize, hmem⟩
    rcases hmem A hA with ⟨p1, hp1⟩
    rcases hmem B hB with ⟨p2, hp2⟩
    rcases hres with ⟨v, hv1, hv2, hR⟩
    let D' : ProofDAG α F :=
      { size := D.size + 1
        clause := Fin.lastCases R D.clause
        step := Fin.lastCases (DAGStep.res p1.castSucc p2.castSucc v)
          (fun j => liftStep (D.step j))
        valid := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Fin.val_castSucc, Fin.val_last]
            exact ⟨p1.isLt, p2.isLt, hp1.symm ▸ hv1, hp2.symm ▸ hv2,
              by rw [hp1, hp2]; exact hR⟩
          · intro j
            simp only [Fin.lastCases_castSucc]
            have hv := D.valid j
            cases hs : D.step j with
            | ax =>
              rw [hs] at hv
              simpa [liftStep] using hv
            | res q1 q2 w =>
              rw [hs] at hv
              simpa [liftStep] using hv }
    refine ⟨D', by simp [D', hsize], ?_⟩
    intro X hX
    rw [List.mem_cons] at hX
    rcases hX with rfl | hXπ
    · exact ⟨Fin.last D.size, by simp [D']⟩
    · rcases hmem X hXπ with ⟨j, rfl⟩
      exact ⟨j.castSucc, by simp [D']⟩

inductive Anc {α : Type} [DecidableEq α] {F : Set (Clause α)}
    (D : ProofDAG α F) (root : Fin D.size) : Fin D.size → Prop
  | refl : Anc D root root
  | parent1 {i p1 p2 v} : Anc D root i → D.step i = .res p1 p2 v → Anc D root p1
  | parent2 {i p1 p2 v} : Anc D root i → D.step i = .res p1 p2 v → Anc D root p2

lemma partition_prefix {α : Type} [DecidableEq α] {F : Set (Clause α)}
    (D : ProofDAG α F) (T : Finset (Fin D.size)) :
    ∀ k ≤ D.size,
      let Tk := T.filter (fun i => i.val < k)
      ∃ P : Finset (Finset (Fin D.size)),
        (∀ C ∈ P, C.Nonempty ∧ C ⊆ Tk) ∧
        (∀ C1 ∈ P, ∀ C2 ∈ P, C1 ≠ C2 → Disjoint C1 C2) ∧
        (∀ u ∈ Tk, ∃ C ∈ P, u ∈ C) ∧
        (∀ u ∈ Tk, ∀ p1 p2 v, D.step u = .res p1 p2 v →
          ∀ C ∈ P, u ∈ C → (p1 ∈ Tk → p1 ∈ C) ∧ (p2 ∈ Tk → p2 ∈ C)) ∧
        2 * (Tk.filter (fun i => isAx (D.step i) = true)).card ≤ Tk.card + P.card := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨∅, by simp, by simp, ?_, ?_, ?_⟩
    · intro u hu
      simp at hu
    · intro u hu
      simp at hu
    · simp
  | succ k ih =>
    rcases ih (Nat.le_of_succ_le hk) with ⟨P, hPsub, hPdisj, hPcov, hPclosed, hPcard⟩
    set Tk := T.filter (fun i => i.val < k)
    set Tk1 := T.filter (fun i => i.val < k + 1)
    let idx : Fin D.size := ⟨k, hk⟩
    by_cases hidx : idx ∈ T
    · have hidx_not_Tk : idx ∉ Tk := by
        simp [Tk, idx]
      have hTk1_eq : Tk1 = insert idx Tk := by
        ext x
        simp only [Tk1, Tk, Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hxT, hxk⟩
          by_cases hxe : x.val = k
          · left; exact Fin.ext hxe
          · right; exact ⟨hxT, by omega⟩
        · rintro (rfl | ⟨hxT, hxk⟩)
          · exact ⟨hidx, by simp [idx]⟩
          · exact ⟨hxT, by omega⟩
      have hTk1_card : Tk1.card = Tk.card + 1 := by
        rw [hTk1_eq, Finset.card_insert_of_notMem hidx_not_Tk]
      have hidx_not_P : ∀ C ∈ P, idx ∉ C := by
        intro C hC hmem
        exact hidx_not_Tk ((hPsub C hC).2 hmem)
      cases hstep : D.step idx with
      | ax =>
        let P1 := insert ({idx} : Finset (Fin D.size)) P
        have hsing_not_P : ({idx} : Finset (Fin D.size)) ∉ P := by
          intro hmem
          exact hidx_not_P _ hmem (Finset.mem_singleton_self idx)
        refine ⟨P1, ?_, ?_, ?_, ?_, ?_⟩
        · intro C hC
          rw [Finset.mem_insert] at hC
          rcases hC with rfl | hCP
          · refine ⟨Finset.singleton_nonempty idx, ?_⟩
            rw [hTk1_eq]
            intro x hx
            rw [Finset.mem_singleton] at hx
            subst hx
            exact Finset.mem_insert_self _ _
          · refine ⟨(hPsub C hCP).1, ?_⟩
            rw [hTk1_eq]
            exact Finset.Subset.trans (hPsub C hCP).2 (Finset.subset_insert _ _)
        · intro C1 hC1 C2 hC2 hne
          rw [Finset.mem_insert] at hC1 hC2
          rcases hC1 with rfl | h1 <;> rcases hC2 with rfl | h2
          · exact absurd rfl hne
          · rw [Finset.disjoint_singleton_left]
            exact hidx_not_P C2 h2
          · rw [Finset.disjoint_singleton_right]
            exact hidx_not_P C1 h1
          · exact hPdisj C1 h1 C2 h2 hne
        · intro u hu
          rw [hTk1_eq, Finset.mem_insert] at hu
          rcases hu with rfl | huTk
          · exact ⟨{idx}, Finset.mem_insert_self _ _, Finset.mem_singleton_self _⟩
          · rcases hPcov u huTk with ⟨C, hCP, huC⟩
            exact ⟨C, Finset.mem_insert_of_mem hCP, huC⟩
        · intro u hu p1 p2 v hsu C hC huC
          rw [hTk1_eq, Finset.mem_insert] at hu
          rcases hu with rfl | huTk
          · rw [hstep] at hsu
            cases hsu
          · rw [Finset.mem_insert] at hC
            rcases hC with rfl | hCP
            · rw [Finset.mem_singleton] at huC
              subst huC
              exact absurd huTk hidx_not_Tk
            · have hv := D.valid u
              rw [hsu] at hv
              have hu_lt : u.val < k := (Finset.mem_filter.mp huTk).2
              have hcl := hPclosed u huTk p1 p2 v hsu C hCP huC
              constructor
              · intro hp1
                have hp1Tk : p1 ∈ Tk :=
                  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp1).1, by omega⟩
                exact hcl.1 hp1Tk
              · intro hp2
                have hp2Tk : p2 ∈ Tk :=
                  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, by omega⟩
                exact hcl.2 hp2Tk
        · have hax_eq : Tk1.filter (fun i => isAx (D.step i) = true) =
              insert idx (Tk.filter (fun i => isAx (D.step i) = true)) := by
            rw [hTk1_eq, Finset.filter_insert]
            simp [hstep, isAx]
          have hax_not : idx ∉ Tk.filter (fun i => isAx (D.step i) = true) := by
            intro h
            exact hidx_not_Tk (Finset.mem_filter.mp h).1
          rw [hax_eq, Finset.card_insert_of_notMem hax_not, hTk1_card]
          have hP1card : P1.card = P.card + 1 := Finset.card_insert_of_notMem hsing_not_P
          rw [hP1card]
          omega
      | res q1 q2 w =>
        let touched := P.filter (fun C => q1 ∈ C ∨ q2 ∈ C)
        let merged : Finset (Fin D.size) := insert idx (touched.biUnion id)
        let P1 := insert merged (P \ touched)
        have ht_sub : touched ⊆ P := Finset.filter_subset _ _
        have ht_le2 : touched.card ≤ 2 := by
          have hsub : touched ⊆ P.filter (fun C => q1 ∈ C) ∪ P.filter (fun C => q2 ∈ C) := by
            intro C hC
            rw [Finset.mem_filter] at hC
            rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
            rcases hC.2 with h1 | h2
            · exact Or.inl ⟨hC.1, h1⟩
            · exact Or.inr ⟨hC.1, h2⟩
          have hc1 : (P.filter (fun C => q1 ∈ C)).card ≤ 1 := by
            refine Finset.card_le_one.mpr ?_
            intro C1 h1 C2 h2
            rw [Finset.mem_filter] at h1 h2
            by_contra hne
            exact Finset.disjoint_left.mp (hPdisj C1 h1.1 C2 h2.1 hne) h1.2 h2.2
          have hc2 : (P.filter (fun C => q2 ∈ C)).card ≤ 1 := by
            refine Finset.card_le_one.mpr ?_
            intro C1 h1 C2 h2
            rw [Finset.mem_filter] at h1 h2
            by_contra hne
            exact Finset.disjoint_left.mp (hPdisj C1 h1.1 C2 h2.1 hne) h1.2 h2.2
          calc touched.card
              ≤ (P.filter (fun C => q1 ∈ C) ∪ P.filter (fun C => q2 ∈ C)).card :=
                Finset.card_le_card hsub
            _ ≤ (P.filter (fun C => q1 ∈ C)).card + (P.filter (fun C => q2 ∈ C)).card :=
                Finset.card_union_le _ _
            _ ≤ 1 + 1 := Nat.add_le_add hc1 hc2
            _ = 2 := rfl
        have hmerged_not_in : merged ∉ P \ touched := by
          intro hmem
          have hPmem : merged ∈ P := (Finset.mem_sdiff.mp hmem).1
          exact hidx_not_P merged hPmem (Finset.mem_insert_self idx _)
        refine ⟨P1, ?_, ?_, ?_, ?_, ?_⟩
        · intro C hC
          rw [Finset.mem_insert] at hC
          rcases hC with rfl | hCsd
          · refine ⟨⟨idx, Finset.mem_insert_self _ _⟩, ?_⟩
            rw [hTk1_eq]
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hxbi
            · exact Finset.mem_insert_self _ _
            · rw [Finset.mem_biUnion] at hxbi
              rcases hxbi with ⟨C', hC't, hxC'⟩
              exact Finset.mem_insert_of_mem ((hPsub C' (ht_sub hC't)).2 hxC')
          · have hCP := (Finset.mem_sdiff.mp hCsd).1
            refine ⟨(hPsub C hCP).1, ?_⟩
            rw [hTk1_eq]
            exact Finset.Subset.trans (hPsub C hCP).2 (Finset.subset_insert _ _)
        · intro C1 hC1 C2 hC2 hne
          rw [Finset.mem_insert] at hC1 hC2
          rcases hC1 with rfl | h1 <;> rcases hC2 with rfl | h2
          · exact absurd rfl hne
          · have h2P := (Finset.mem_sdiff.mp h2).1
            have h2nt := (Finset.mem_sdiff.mp h2).2
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            rw [Finset.mem_insert] at hx1
            rcases hx1 with rfl | hxbi
            · exact hidx_not_P C2 h2P hx2
            · rw [Finset.mem_biUnion] at hxbi
              rcases hxbi with ⟨C', hC't, hxC'⟩
              have hC'ne : C' ≠ C2 := fun heq => h2nt (heq ▸ hC't)
              exact Finset.disjoint_left.mp (hPdisj C' (ht_sub hC't) C2 h2P hC'ne) hxC' hx2
          · have h1P := (Finset.mem_sdiff.mp h1).1
            have h1nt := (Finset.mem_sdiff.mp h1).2
            rw [Finset.disjoint_right]
            intro x hx2 hx1
            rw [Finset.mem_insert] at hx2
            rcases hx2 with rfl | hxbi
            · exact hidx_not_P C1 h1P hx1
            · rw [Finset.mem_biUnion] at hxbi
              rcases hxbi with ⟨C', hC't, hxC'⟩
              have hC'ne : C' ≠ C1 := fun heq => h1nt (heq ▸ hC't)
              exact Finset.disjoint_left.mp (hPdisj C' (ht_sub hC't) C1 h1P hC'ne) hxC' hx1
          · exact hPdisj C1 (Finset.mem_sdiff.mp h1).1 C2 (Finset.mem_sdiff.mp h2).1 hne
        · intro u hu
          rw [hTk1_eq, Finset.mem_insert] at hu
          rcases hu with rfl | huTk
          · exact ⟨merged, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
          · rcases hPcov u huTk with ⟨C, hCP, huC⟩
            by_cases hCt : C ∈ touched
            · refine ⟨merged, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
              exact Finset.mem_biUnion.mpr ⟨C, hCt, huC⟩
            · exact ⟨C, Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hCP, hCt⟩), huC⟩
        · intro u hu p1 p2 v hsu C hC huC
          rw [hTk1_eq, Finset.mem_insert] at hu
          rcases hu with rfl | huTk
          · rw [hstep] at hsu
            cases hsu
            have hCeq : C = merged := by
              rw [Finset.mem_insert] at hC
              rcases hC with rfl | hCsd
              · rfl
              · exact absurd huC (hidx_not_P C (Finset.mem_sdiff.mp hCsd).1)
            subst hCeq
            have hv := D.valid idx
            rw [hstep] at hv
            constructor
            · intro hp1
              have hp1Tk : q1 ∈ Tk :=
                Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp1).1, hv.1⟩
              rcases hPcov q1 hp1Tk with ⟨C1, hC1P, hq1C1⟩
              have hC1t : C1 ∈ touched := Finset.mem_filter.mpr ⟨hC1P, Or.inl hq1C1⟩
              exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨C1, hC1t, hq1C1⟩)
            · intro hp2
              have hp2Tk : q2 ∈ Tk :=
                Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, hv.2.1⟩
              rcases hPcov q2 hp2Tk with ⟨C2, hC2P, hq2C2⟩
              have hC2t : C2 ∈ touched := Finset.mem_filter.mpr ⟨hC2P, Or.inr hq2C2⟩
              exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨C2, hC2t, hq2C2⟩)
          · have hv := D.valid u
            rw [hsu] at hv
            have hu_lt : u.val < k := (Finset.mem_filter.mp huTk).2
            rw [Finset.mem_insert] at hC
            rcases hC with rfl | hCsd
            · rw [Finset.mem_insert] at huC
              rcases huC with rfl | hubi
              · exact absurd huTk hidx_not_Tk
              · rw [Finset.mem_biUnion] at hubi
                rcases hubi with ⟨C', hC't, huC'⟩
                have hcl := hPclosed u huTk p1 p2 v hsu C' (ht_sub hC't) huC'
                constructor
                · intro hp1
                  have hp1Tk : p1 ∈ Tk :=
                    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp1).1, by omega⟩
                  exact Finset.mem_insert_of_mem
                    (Finset.mem_biUnion.mpr ⟨C', hC't, hcl.1 hp1Tk⟩)
                · intro hp2
                  have hp2Tk : p2 ∈ Tk :=
                    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, by omega⟩
                  exact Finset.mem_insert_of_mem
                    (Finset.mem_biUnion.mpr ⟨C', hC't, hcl.2 hp2Tk⟩)
            · have hCP := (Finset.mem_sdiff.mp hCsd).1
              have hcl := hPclosed u huTk p1 p2 v hsu C hCP huC
              constructor
              · intro hp1
                have hp1Tk : p1 ∈ Tk :=
                  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp1).1, by omega⟩
                exact hcl.1 hp1Tk
              · intro hp2
                have hp2Tk : p2 ∈ Tk :=
                  Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp2).1, by omega⟩
                exact hcl.2 hp2Tk
        · have hax_eq : Tk1.filter (fun i => isAx (D.step i) = true) =
              Tk.filter (fun i => isAx (D.step i) = true) := by
            rw [hTk1_eq, Finset.filter_insert]
            simp [hstep, isAx]
          have hP1card : P1.card = (P \ touched).card + 1 :=
            Finset.card_insert_of_notMem hmerged_not_in
          have hsd : (P \ touched).card + touched.card = P.card :=
            Finset.card_sdiff_add_card_eq_card ht_sub
          rw [hax_eq, hTk1_card, hP1card]
          omega
    · have hTk1_eq : Tk1 = Tk := by
        ext x
        simp only [Tk1, Tk, Finset.mem_filter]
        constructor
        · rintro ⟨hxT, hxk⟩
          refine ⟨hxT, ?_⟩
          by_contra hge
          have hxeq : x = idx := Fin.ext (by simp only [idx]; omega)
          exact hidx (hxeq ▸ hxT)
        · rintro ⟨hxT, hxk⟩
          exact ⟨hxT, by omega⟩
      rw [hTk1_eq]
      exact ⟨P, hPsub, hPdisj, hPcov, hPclosed, hPcard⟩

lemma dag_taut_boundary_bound {α : Type} [DecidableEq α] {F : Set (Clause α)}
    (D : ProofDAG α F) (root : Fin D.size)
    (T : Finset (Fin D.size))
    (hTsub : ∀ i ∈ T, Anc D root i)
    (hroot : root ∉ T)
    (hno_both : ∀ i : Fin D.size, Anc D root i → i ∉ T →
      ∀ p1 p2 v, D.step i = .res p1 p2 v → ¬ (p1 ∈ T ∧ p2 ∈ T)) :
    2 * (T.filter (fun i => isAx (D.step i) = true)).card ≤
      T.card + (((Finset.univ.filter (fun i => Anc D root i)) \ T).filter (fun i =>
        match D.step i with
        | .ax => False
        | .res p1 p2 _ => p1 ∈ T ∨ p2 ∈ T)).card := by
  set R : Finset (Fin D.size) := Finset.univ.filter (fun i => Anc D root i)
  set B : Finset (Fin D.size) := (R \ T).filter (fun i =>
    match D.step i with
    | .ax => False
    | .res p1 p2 _ => p1 ∈ T ∨ p2 ∈ T)
  have hpart := partition_prefix D T D.size (le_refl _)
  have hTeq : T.filter (fun i => i.val < D.size) = T := by
    ext i
    simp
  rw [hTeq] at hpart
  rcases hpart with ⟨P, hPsub, hPdisj, hPcov, hPclosed, hPcard⟩
  have hreach_bd : ∀ i : Fin D.size, Anc D root i →
      ∀ C ∈ P, i ∈ C →
        ∃ b ∈ B, ∃ u ∈ C, ∃ p1 p2 v, D.step b = .res p1 p2 v ∧ (u = p1 ∨ u = p2) := by
    intro i hanc
    induction hanc with
    | refl =>
      intro C hCP hrootC
      exact absurd ((hPsub C hCP).2 hrootC) hroot
    | @parent1 j p1 p2 v hj hstep ih =>
      intro C hCP hp1C
      by_cases hjT : j ∈ T
      · rcases hPcov j hjT with ⟨C', hC'P, hjC'⟩
        have hp1T : p1 ∈ T := (hPsub C hCP).2 hp1C
        have hp1C' : p1 ∈ C' := (hPclosed j hjT p1 p2 v hstep C' hC'P hjC').1 hp1T
        have hCeq : C' = C := by
          by_contra hne
          exact Finset.disjoint_left.mp (hPdisj C' hC'P C hCP hne) hp1C' hp1C
        rw [hCeq] at hjC'
        exact ih C hCP hjC'
      · have hjR : j ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        have hp1T : p1 ∈ T := (hPsub C hCP).2 hp1C
        have hjB : j ∈ B := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hjR, hjT⟩, ?_⟩
          rw [hstep]
          exact Or.inl hp1T
        exact ⟨j, hjB, p1, hp1C, p1, p2, v, hstep, Or.inl rfl⟩
    | @parent2 j p1 p2 v hj hstep ih =>
      intro C hCP hp2C
      by_cases hjT : j ∈ T
      · rcases hPcov j hjT with ⟨C', hC'P, hjC'⟩
        have hp2T : p2 ∈ T := (hPsub C hCP).2 hp2C
        have hp2C' : p2 ∈ C' := (hPclosed j hjT p1 p2 v hstep C' hC'P hjC').2 hp2T
        have hCeq : C' = C := by
          by_contra hne
          exact Finset.disjoint_left.mp (hPdisj C' hC'P C hCP hne) hp2C' hp2C
        rw [hCeq] at hjC'
        exact ih C hCP hjC'
      · have hjR : j ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
        have hp2T : p2 ∈ T := (hPsub C hCP).2 hp2C
        have hjB : j ∈ B := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hjR, hjT⟩, ?_⟩
          rw [hstep]
          exact Or.inr hp2T
        exact ⟨j, hjB, p2, hp2C, p1, p2, v, hstep, Or.inr rfl⟩
  have hexB : ∀ C ∈ P, ∃ b ∈ B, ∃ u ∈ C, ∃ p1 p2 v,
      D.step b = .res p1 p2 v ∧ (u = p1 ∨ u = p2) := by
    intro C hCP
    rcases (hPsub C hCP).1 with ⟨i, hiC⟩
    have hiT : i ∈ T := (hPsub C hCP).2 hiC
    exact hreach_bd i (hTsub i hiT) C hCP hiC
  let pickB : Finset (Fin D.size) → Fin D.size := fun C =>
    if h : C ∈ P then Classical.choose (hexB C h) else root
  have hP_le_B : P.card ≤ B.card := by
    refine Finset.card_le_card_of_injOn pickB ?_ ?_
    · intro C hCP
      simp only [Finset.mem_coe] at hCP ⊢
      have hpick : pickB C = Classical.choose (hexB C hCP) := by simp [pickB, hCP]
      rw [hpick]
      exact (Classical.choose_spec (hexB C hCP)).1
    · intro C1 hC1 C2 hC2 heq
      simp only [Finset.mem_coe] at hC1 hC2
      have h1 : pickB C1 = Classical.choose (hexB C1 hC1) := by simp [pickB, hC1]
      have h2 : pickB C2 = Classical.choose (hexB C2 hC2) := by simp [pickB, hC2]
      rw [h1, h2] at heq
      set b := Classical.choose (hexB C1 hC1)
      have hb1 := Classical.choose_spec (hexB C1 hC1)
      have hb2 := Classical.choose_spec (hexB C2 hC2)
      rw [← heq] at hb2
      rcases hb1 with ⟨hbB, u1, hu1C1, p1, p2, v, hsb, hu1p⟩
      rcases hb2 with ⟨_, u2, hu2C2, q1, q2, w, hsb2, hu2q⟩
      rw [hsb] at hsb2
      cases hsb2
      have hb_sd := (Finset.mem_filter.mp hbB).1
      have hbR : Anc D root b := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb_sd).1).2
      have hbnotT : b ∉ T := (Finset.mem_sdiff.mp hb_sd).2
      have hnb := hno_both b hbR hbnotT p1 p2 v hsb
      have hu1T : u1 ∈ T := (hPsub C1 hC1).2 hu1C1
      have hu2T : u2 ∈ T := (hPsub C2 hC2).2 hu2C2
      have hu_eq : u1 = u2 := by
        rcases hu1p with rfl | rfl <;> rcases hu2q with rfl | rfl
        · rfl
        · exact absurd ⟨hu1T, hu2T⟩ hnb
        · exact absurd ⟨hu2T, hu1T⟩ hnb
        · rfl
      by_contra hne
      rw [← hu_eq] at hu2C2
      exact Finset.disjoint_left.mp (hPdisj C1 hC1 C2 hC2 hne) hu1C1 hu2C2
  omega

lemma build_sub_deriv {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (D : ProofDAG (V n m) (bigSet src dst len)) (root : Fin D.size)
    (S : Finset (Fin m)) (bp : Fin m → ℕ)
    (hbp : ∀ e, bp e < len e)
    (hnotS : ∀ e, e ∉ S → ∀ i : Fin D.size, Anc D root i →
      D.step i = .ax → D.clause i ≠ stepClause src dst len e (bp e)) :
    let R : Finset (Fin D.size) := Finset.univ.filter (fun i => Anc D root i)
    let T : Finset (Fin D.size) := R.filter (fun i => IsTaut (substClause src dst bp (D.clause i)))
    let B : Finset (Fin D.size) := (R \ T).filter (fun i =>
      match D.step i with
      | .ax => False
      | .res p1 p2 _ => p1 ∈ T ∨ p2 ∈ T)
    let baseF : Set (Clause (V n m)) := {C | ∃ idx ∈ S, C = baseClause src dst idx}
    ∀ k ≤ D.size,
      ∃ π : List (Clause (V n m)),
        IsDerivation baseF π ∧
        π.length ≤ ((R \ (T ∪ B)).filter (fun i => i.val < k)).card ∧
        ∀ i ∈ R \ T, i.val < k → ∃ C' ∈ π, C' ⊆ substClause src dst bp (D.clause i) := by
  intro R T B baseF k hk
  induction k with
  | zero =>
    refine ⟨[], IsDerivation.nil, by simp, ?_⟩
    intro i _ hi
    omega
  | succ k ih =>
    rcases ih (Nat.le_of_succ_le hk) with ⟨π, hπ, hlen_π, hcov⟩
    let idx : Fin D.size := ⟨k, hk⟩
    have hsub_filt : (R \ (T ∪ B)).filter (fun i => i.val < k) ⊆
        (R \ (T ∪ B)).filter (fun i => i.val < k + 1) := by
      intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, by omega⟩
    have hlen_le_next : π.length ≤ ((R \ (T ∪ B)).filter (fun i => i.val < k + 1)).card :=
      le_trans hlen_π (Finset.card_le_card hsub_filt)
    by_cases hidx_RT : idx ∈ R \ T
    · have hidxR : Anc D root idx := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hidx_RT).1).2
      have hidxnotT : ¬ IsTaut (substClause src dst bp (D.clause idx)) := by
        intro ht
        have hmemT : idx ∈ T :=
          Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hidx_RT).1, ht⟩
        exact (Finset.mem_sdiff.mp hidx_RT).2 hmemT
      by_cases hidxB : idx ∈ B
      · refine ⟨π, hπ, hlen_le_next, ?_⟩
        intro i hi hilt
        by_cases hieq : i = idx
        · subst hieq
          have hBcond := (Finset.mem_filter.mp hidxB).2
          have hv := D.valid idx
          cases hstep : D.step idx with
          | ax =>
            rw [hstep] at hBcond
            exact False.elim hBcond
          | res p1 p2 v =>
            rw [hstep] at hBcond hv
            have hp1R : p1 ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Anc.parent1 hidxR hstep⟩
            have hp2R : p2 ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Anc.parent2 hidxR hstep⟩
            have hnb := res_image_not_both_taut (substLit src dst bp) (substLit_neg src dst bp)
              hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hidxnotT
            rcases hBcond with hp1T | hp2T
            · have ht1 : IsTaut (substClause src dst bp (D.clause p1)) :=
                (Finset.mem_filter.mp hp1T).2
              have hp2notT : p2 ∉ T := fun h => hnb ⟨ht1, (Finset.mem_filter.mp h).2⟩
              have hp2RT : p2 ∈ R \ T := Finset.mem_sdiff.mpr ⟨hp2R, hp2notT⟩
              rcases hcov p2 hp2RT hv.2.1 with ⟨D', hD'π, hD'sub⟩
              have hsub := res_image_sub_right (substLit src dst bp) (substLit_neg src dst bp)
                hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hidxnotT ht1
              exact ⟨D', hD'π, Finset.Subset.trans hD'sub hsub⟩
            · have ht2 : IsTaut (substClause src dst bp (D.clause p2)) :=
                (Finset.mem_filter.mp hp2T).2
              have hp1notT : p1 ∉ T := fun h => hnb ⟨(Finset.mem_filter.mp h).2, ht2⟩
              have hp1RT : p1 ∈ R \ T := Finset.mem_sdiff.mpr ⟨hp1R, hp1notT⟩
              rcases hcov p1 hp1RT hv.1 with ⟨C', hC'π, hC'sub⟩
              have hsub := res_image_sub_left (substLit src dst bp) (substLit_neg src dst bp)
                hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hidxnotT ht2
              exact ⟨C', hC'π, Finset.Subset.trans hC'sub hsub⟩
        · have hlt : i.val < k := by
            have : i.val ≠ k := fun h => hieq (Fin.ext h)
            omega
          exact hcov i hi hlt
      · have hidx_good : idx ∈ R \ (T ∪ B) := by
          rw [Finset.mem_sdiff, Finset.mem_union]
          exact ⟨(Finset.mem_sdiff.mp hidx_RT).1,
            not_or.mpr ⟨(Finset.mem_sdiff.mp hidx_RT).2, hidxB⟩⟩
        have hfilt_eq : (R \ (T ∪ B)).filter (fun i => i.val < k + 1) =
            insert idx ((R \ (T ∪ B)).filter (fun i => i.val < k)) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hx, hxk⟩
            by_cases hxe : x.val = k
            · left; exact Fin.ext hxe
            · right; exact ⟨hx, by omega⟩
          · rintro (rfl | ⟨hx, hxk⟩)
            · exact ⟨hidx_good, by simp [idx]⟩
            · exact ⟨hx, by omega⟩
        have hidx_not_filt : idx ∉ (R \ (T ∪ B)).filter (fun i => i.val < k) := by
          simp [idx]
        have hcard_succ : ((R \ (T ∪ B)).filter (fun i => i.val < k + 1)).card =
            ((R \ (T ∪ B)).filter (fun i => i.val < k)).card + 1 := by
          rw [hfilt_eq, Finset.card_insert_of_notMem hidx_not_filt]
        have hv := D.valid idx
        cases hstep : D.step idx with
        | ax =>
          rw [hstep] at hv
          rcases hv with ⟨e, j, hj, hcl⟩
          have hjeq : j = bp e := by
            by_contra hne
            have ht := substClause_step_taut src dst len bp e hj (hbp e) hne
            rw [← hcl] at ht
            exact hidxnotT ht
          subst hjeq
          have heS : e ∈ S := by
            by_contra henotS
            exact hnotS e henotS idx hidxR hstep hcl
          have hsub_eq : substClause src dst bp (D.clause idx) = baseClause src dst e := by
            rw [hcl]
            exact substClause_step_eq src dst len bp e (hbp e)
          refine ⟨baseClause src dst e :: π, IsDerivation.ax hπ ⟨e, heS, rfl⟩, ?_, ?_⟩
          · rw [List.length_cons, hcard_succ]
            omega
          · intro i hi hilt
            by_cases hieq : i = idx
            · subst hieq
              exact ⟨baseClause src dst e, List.mem_cons_self, by rw [hsub_eq]⟩
            · have hlt : i.val < k := by
                have : i.val ≠ k := fun h => hieq (Fin.ext h)
                omega
              rcases hcov i hi hlt with ⟨C', hC'π, hC'sub⟩
              exact ⟨C', List.mem_cons_of_mem _ hC'π, hC'sub⟩
        | res p1 p2 v =>
          rw [hstep] at hv
          have hp1notT : p1 ∉ T := by
            intro hp1T
            apply hidxB
            refine Finset.mem_filter.mpr ⟨hidx_RT, ?_⟩
            rw [hstep]
            exact Or.inl hp1T
          have hp2notT : p2 ∉ T := by
            intro hp2T
            apply hidxB
            refine Finset.mem_filter.mpr ⟨hidx_RT, ?_⟩
            rw [hstep]
            exact Or.inr hp2T
          have hp1RT : p1 ∈ R \ T := Finset.mem_sdiff.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Anc.parent1 hidxR hstep⟩, hp1notT⟩
          have hp2RT : p2 ∈ R \ T := Finset.mem_sdiff.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Anc.parent2 hidxR hstep⟩, hp2notT⟩
          rcases hcov p1 hp1RT hv.1 with ⟨C', hC'π, hC'sub⟩
          rcases hcov p2 hp2RT hv.2.1 with ⟨D', hD'π, hD'sub⟩
          have hstep_res := res_image_sub_step (substLit src dst bp) (substLit_neg src dst bp)
            hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hC'sub hD'sub
          rcases hstep_res with hC'R | hD'R | ⟨R', hres', hR'sub⟩
          · refine ⟨π, hπ, hlen_le_next, ?_⟩
            intro i hi hilt
            by_cases hieq : i = idx
            · subst hieq
              exact ⟨C', hC'π, hC'R⟩
            · have hlt : i.val < k := by
                have : i.val ≠ k := fun h => hieq (Fin.ext h)
                omega
              exact hcov i hi hlt
          · refine ⟨π, hπ, hlen_le_next, ?_⟩
            intro i hi hilt
            by_cases hieq : i = idx
            · subst hieq
              exact ⟨D', hD'π, hD'R⟩
            · have hlt : i.val < k := by
                have : i.val ≠ k := fun h => hieq (Fin.ext h)
                omega
              exact hcov i hi hlt
          · have hder' : IsDerivation baseF (R' :: π) := by
              rcases hres' with hr1 | hr2
              · exact IsDerivation.res hπ hC'π hD'π hr1
              · exact IsDerivation.res hπ hD'π hC'π hr2
            refine ⟨R' :: π, hder', ?_, ?_⟩
            · rw [List.length_cons, hcard_succ]
              omega
            · intro i hi hilt
              by_cases hieq : i = idx
              · subst hieq
                exact ⟨R', List.mem_cons_self, hR'sub⟩
              · have hlt : i.val < k := by
                  have : i.val ≠ k := fun h => hieq (Fin.ext h)
                  omega
                rcases hcov i hi hlt with ⟨X, hXπ, hXsub⟩
                exact ⟨X, List.mem_cons_of_mem _ hXπ, hXsub⟩
    · refine ⟨π, hπ, hlen_le_next, ?_⟩
      intro i hi hilt
      have hne : i ≠ idx := fun h => hidx_RT (h ▸ hi)
      have hlt : i.val < k := by
        have : i.val ≠ k := fun h => hne (Fin.ext h)
        omega
      exact hcov i hi hlt

lemma forward_dir {n m : ℕ} (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ)
    (hlen : ∀ e, 0 < len e) (K : ℕ)
    (π : List (Clause (V n m)))
    (href : IsRefutation (bigSet src dst len) π)
    (hK : π.length ≤ K) :
    ∃ S : Finset (Fin m), ∃ π',
      IsRefutation {C | ∃ idx ∈ S, C = baseClause src dst idx} π' ∧
      π'.length + 2 * S.sum (fun idx => len idx - 1) ≤ K := by
  rcases dag_of_derivation href.1 with ⟨D, hsize, hmem⟩
  rcases hmem ∅ href.2 with ⟨root, hroot_cl⟩
  let R : Finset (Fin D.size) := Finset.univ.filter (fun i => Anc D root i)
  let S : Finset (Fin m) := Finset.univ.filter (fun e =>
    ∀ j < len e, ∃ i : Fin D.size, Anc D root i ∧
      D.step i = .ax ∧ D.clause i = stepClause src dst len e j)
  have hex_miss : ∀ e, e ∉ S →
      ∃ j < len e, ∀ i : Fin D.size, Anc D root i →
        D.step i = .ax → D.clause i ≠ stepClause src dst len e j := by
    intro e he
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at he
    push Not at he
    exact he
  let bp : Fin m → ℕ := fun e =>
    if h : e ∈ S then 0 else Classical.choose (hex_miss e h)
  have hbp_lt : ∀ e, bp e < len e := by
    intro e
    by_cases h : e ∈ S
    · simp [bp, h, hlen e]
    · have hbp_eq : bp e = Classical.choose (hex_miss e h) := by simp [bp, h]
      rw [hbp_eq]
      exact (Classical.choose_spec (hex_miss e h)).1
  have hbp_notS : ∀ e, e ∉ S → ∀ i : Fin D.size, Anc D root i →
      D.step i = .ax → D.clause i ≠ stepClause src dst len e (bp e) := by
    intro e he
    have hbp_eq : bp e = Classical.choose (hex_miss e he) := by simp [bp, he]
    rw [hbp_eq]
    exact (Classical.choose_spec (hex_miss e he)).2
  let T : Finset (Fin D.size) :=
    R.filter (fun i => IsTaut (substClause src dst bp (D.clause i)))
  let B : Finset (Fin D.size) := (R \ T).filter (fun i =>
    match D.step i with
    | .ax => False
    | .res p1 p2 _ => p1 ∈ T ∨ p2 ∈ T)
  let Tax : Finset (Fin D.size) := T.filter (fun i => isAx (D.step i) = true)
  have hroot_not_T : root ∉ T := by
    intro h
    have ht := (Finset.mem_filter.mp h).2
    rw [hroot_cl] at ht
    simp only [substClause, Finset.image_empty] at ht
    exact not_isTaut_empty ht
  have hT_anc : ∀ i ∈ T, Anc D root i := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hno_both : ∀ i : Fin D.size, Anc D root i → i ∉ T →
      ∀ p1 p2 v, D.step i = .res p1 p2 v → ¬ (p1 ∈ T ∧ p2 ∈ T) := by
    intro i hiR hinotT p1 p2 v hstep
    have hv := D.valid i
    rw [hstep] at hv
    have hnt : ¬ IsTaut (substClause src dst bp (D.clause i)) := by
      intro ht
      exact hinotT (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiR⟩, ht⟩)
    rintro ⟨hp1T, hp2T⟩
    exact res_image_not_both_taut (substLit src dst bp) (substLit_neg src dst bp)
      hv.2.2.1 hv.2.2.2.1 hv.2.2.2.2 hnt
      ⟨(Finset.mem_filter.mp hp1T).2, (Finset.mem_filter.mp hp2T).2⟩
  have hbd : 2 * Tax.card ≤ T.card + B.card := by
    convert dag_taut_boundary_bound D root T hT_anc hroot_not_T hno_both using 2
    congr 1
    ext i
    simp only [B, R, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    cases D.step i <;> simp
  have hsum_le_Tax : S.sum (fun e => len e - 1) ≤ Tax.card := by
    let pairs : Finset (Σ _ : Fin m, ℕ) := S.sigma (fun e => Finset.Ico 1 (len e))
    have hpairs_card : pairs.card = S.sum (fun e => len e - 1) := by
      rw [Finset.card_sigma]
      refine Finset.sum_congr rfl ?_
      intro e _
      rw [Nat.card_Ico]
    have hex_ax : ∀ p ∈ pairs, ∃ i : Fin D.size,
        Anc D root i ∧ D.step i = .ax ∧ D.clause i = stepClause src dst len p.1 p.2 := by
      intro p hp
      rw [Finset.mem_sigma] at hp
      have heS := (Finset.mem_filter.mp hp.1).2
      have hjlt : p.2 < len p.1 := (Finset.mem_Ico.mp hp.2).2
      exact heS p.2 hjlt
    let pickAx : (Σ _ : Fin m, ℕ) → Fin D.size := fun p =>
      if h : p ∈ pairs then Classical.choose (hex_ax p h) else root
    have hle : pairs.card ≤ Tax.card := by
      refine Finset.card_le_card_of_injOn pickAx ?_ ?_
      · intro p hp
        simp only [Finset.mem_coe] at hp ⊢
        have hpick : pickAx p = Classical.choose (hex_ax p hp) := by simp [pickAx, hp]
        rw [hpick]
        set i := Classical.choose (hex_ax p hp)
        have hspec := Classical.choose_spec (hex_ax p hp)
        have hpm := Finset.mem_sigma.mp hp
        have heS : p.1 ∈ S := hpm.1
        have hico := Finset.mem_Ico.mp hpm.2
        have hbp0 : bp p.1 = 0 := by simp [bp, heS]
        have hne : p.2 ≠ bp p.1 := by omega
        have ht : IsTaut (substClause src dst bp (D.clause i)) := by
          rw [hspec.2.2]
          exact substClause_step_taut src dst len bp p.1 hico.2 (hbp_lt p.1) hne
        have hiR : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hspec.1⟩
        have hiT : i ∈ T := Finset.mem_filter.mpr ⟨hiR, ht⟩
        exact Finset.mem_filter.mpr ⟨hiT, by rw [hspec.2.1]; rfl⟩
      · intro p1 hp1 p2 hp2 heq
        simp only [Finset.mem_coe] at hp1 hp2
        have h1 : pickAx p1 = Classical.choose (hex_ax p1 hp1) := by simp [pickAx, hp1]
        have h2 : pickAx p2 = Classical.choose (hex_ax p2 hp2) := by simp [pickAx, hp2]
        rw [h1, h2] at heq
        have hs1 := Classical.choose_spec (hex_ax p1 hp1)
        have hs2 := Classical.choose_spec (hex_ax p2 hp2)
        have hcl_eq : stepClause src dst len p1.1 p1.2 = stepClause src dst len p2.1 p2.2 := by
          rw [← hs1.2.2, heq, hs2.2.2]
        have hi1 := Finset.mem_Ico.mp (Finset.mem_sigma.mp hp1).2
        have hi2 := Finset.mem_Ico.mp (Finset.mem_sigma.mp hp2).2
        have ⟨he, hj⟩ := stepClause_inj_pos src dst len hi1.1 hi1.2 hi2.1 hi2.2 hcl_eq
        cases p1
        cases p2
        simp only at he hj
        subst he
        subst hj
        rfl
    omega
  have hsub := build_sub_deriv src dst len D root S bp hbp_lt hbp_notS D.size (le_refl _)
  rcases hsub with ⟨π', hπ', hlen_π', hcov'⟩
  have hroot_RT : root ∈ R \ T := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, Anc.refl⟩, hroot_not_T⟩
  rcases hcov' root hroot_RT root.isLt with ⟨C', hC'π', hC'sub⟩
  have hC'empty : C' = ∅ := by
    rw [hroot_cl] at hC'sub
    simp only [substClause, Finset.image_empty, Finset.subset_empty] at hC'sub
    exact hC'sub
  rw [hC'empty] at hC'π'
  have hfilt_all : (R \ (T ∪ B)).filter (fun i => i.val < D.size) = R \ (T ∪ B) := by
    ext i
    simp
  rw [hfilt_all] at hlen_π'
  have hTB_sub : T ∪ B ⊆ R := by
    refine Finset.union_subset (Finset.filter_subset _ _) ?_
    exact Finset.Subset.trans (Finset.filter_subset _ _) Finset.sdiff_subset
  have hTB_disj : Disjoint T B := by
    rw [Finset.disjoint_right]
    intro x hxB hxT
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxB).1).2 hxT
  have hR_split : (R \ (T ∪ B)).card + (T ∪ B).card = R.card :=
    Finset.card_sdiff_add_card_eq_card hTB_sub
  have hTB_card : (T ∪ B).card = T.card + B.card :=
    Finset.card_union_of_disjoint hTB_disj
  have hR_le : R.card ≤ D.size := by
    calc R.card ≤ (Finset.univ : Finset (Fin D.size)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = D.size := Fintype.card_fin D.size
  refine ⟨S, π', ⟨hπ', hC'π'⟩, ?_⟩
  omega

theorem main :
    (∀ (n m : ℕ) (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ),
      (∀ e, 0 < len e ∧ (src e).1 ≠ (dst e).1) →
      let V := Fin n ⊕ (Fin m × ℕ)
      let lit := fun (e : Fin m) (j : ℕ) =>
        if j = 0 then ((Sum.inl (src e).1 : V), (src e).2)
        else if j = len e then ((Sum.inl (dst e).1 : V), (dst e).2)
        else ((Sum.inr (e,j) : V), true)
      let step := fun (e : Fin m) (j : ℕ) =>
        ({((lit e j).1, !(lit e j).2), lit e (j+1)} : PEqualNP.ProofComplexity.Clause V)
      let big : Set (PEqualNP.ProofComplexity.Clause V) := {C | ∃ e j, j < len e ∧ C = step e j}
      let base := fun clauseIndex : Fin m =>
        ({((Sum.inl (src clauseIndex).1 : V), !(src clauseIndex).2), ((Sum.inl (dst clauseIndex).1 : V), (dst clauseIndex).2)} :
          PEqualNP.ProofComplexity.Clause V)
      Function.Injective base →
      ∀ K : ℕ,
        (∃ π, PEqualNP.ProofComplexity.IsRefutation big π ∧ π.length ≤ K) ↔
        ∃ S : Finset (Fin m), ∃ π, PEqualNP.ProofComplexity.IsRefutation
          {C | ∃ idx ∈ S, C = base idx} π ∧ π.length + 2*S.sum (fun idx => len idx-1) ≤ K) := by
  intro n m src dst len hlen
  dsimp only
  intro _ K
  constructor
  · rintro ⟨π, href, hK⟩
    exact forward_dir src dst len (fun e => (hlen e).1) K π href hK
  · rintro ⟨S, π, href, hK⟩
    exact backward_dir src dst len (fun e => (hlen e).1) K S π href hK

end PEqualNP.Outside.L_pcx_269_aux

theorem PEqualNP.Outside.L_pcx_269 : (∀ (n m : ℕ) (src dst : Fin m → Fin n × Bool) (len : Fin m → ℕ),
  (∀ e, 0 < len e ∧ (src e).1 ≠ (dst e).1) →
  let V := Fin n ⊕ (Fin m × ℕ)
  let lit := fun (e : Fin m) (j : ℕ) =>
    if j = 0 then ((Sum.inl (src e).1 : V), (src e).2)
    else if j = len e then ((Sum.inl (dst e).1 : V), (dst e).2)
    else ((Sum.inr (e,j) : V), true)
  let step := fun (e : Fin m) (j : ℕ) =>
    ({((lit e j).1, !(lit e j).2), lit e (j+1)} : PEqualNP.ProofComplexity.Clause V)
  let big : Set (PEqualNP.ProofComplexity.Clause V) := {C | ∃ e j, j < len e ∧ C = step e j}
  let base := fun clauseIndex : Fin m =>
    ({((Sum.inl (src clauseIndex).1 : V), !(src clauseIndex).2), ((Sum.inl (dst clauseIndex).1 : V), (dst clauseIndex).2)} :
      PEqualNP.ProofComplexity.Clause V)
  Function.Injective base →
  ∀ K : ℕ,
    (∃ π, PEqualNP.ProofComplexity.IsRefutation big π ∧ π.length ≤ K) ↔
    ∃ S : Finset (Fin m), ∃ π, PEqualNP.ProofComplexity.IsRefutation
      {C | ∃ idx ∈ S, C = base idx} π ∧ π.length + 2*S.sum (fun idx => len idx-1) ≤ K) := by
  exact PEqualNP.Outside.L_pcx_269_aux.main
