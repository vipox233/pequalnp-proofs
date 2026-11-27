import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_294_aux

open scoped BigOperators
open PEqualNP.ProofComplexity

abbrev Raw {n : ℕ} (w : Fin n → ℕ) := (i : Fin n) × Fin (w i)

def parity {n : ℕ} {w : Fin n → ℕ} (y : Raw w → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)

def liftAx {n : ℕ} {w : Fin n → ℕ}
    (F : Set (Clause (Fin n))) (A : Clause (Raw w)) : Prop :=
  ∃ C ∈ F, ∃ y : Raw w → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
    A = ((Finset.univ : Finset (Raw w)).filter (fun b => b.1 ∈ C.image Prod.fst)).image
      (fun b => (b, !(y b)))

def shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Derivable {n : ℕ} {w : Fin n → ℕ}
    (F : Set (Clause (Fin n))) (W : ℕ) (C : Clause (Raw w)) : Prop :=
  ∃ (N J : Finset (List Bool)) (line : List Bool → Clause (Raw w)),
    shape N J ∧ line [] = C ∧ (∀ p ∈ N, (line p).card ≤ W) ∧
    (∀ p ∈ N \ J, liftAx F (line p)) ∧
    ∀ p ∈ J, IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)

def eqFormula {n : ℕ} (E : Fin n → Fin n → Bool → Prop) : Set (Clause (Fin n)) :=
  {C | ∃ u v s a, E u v s ∧ C = {(u, !a), (v, a ^^ s)}}

def rawClause {n : ℕ} {w : Fin n → ℕ} (X : Finset (Raw w)) (y : Raw w → Bool) : Clause (Raw w) :=
  X.image (fun b => (b, !(y b)))

def blockRaw {n : ℕ} (w : Fin n → ℕ) (S : Finset (Fin n)) : Finset (Raw w) :=
  (Finset.univ : Finset (Raw w)).filter (fun b => b.1 ∈ S)

def blockClause {n : ℕ} {w : Fin n → ℕ} (S : Finset (Fin n)) (y : Raw w → Bool) : Clause (Raw w) :=
  rawClause (blockRaw w S) y

lemma rawClause_card {n : ℕ} {w : Fin n → ℕ} (X : Finset (Raw w)) (y : Raw w → Bool) :
    (rawClause X y).card = X.card := by
  unfold rawClause
  apply Finset.card_image_of_injOn
  intro a _ b _ h
  exact (Prod.mk.inj h).1

lemma blockRaw_single_card {n : ℕ} (w : Fin n → ℕ) (i : Fin n) :
    (blockRaw w {i}).card = w i := by
  have heq : blockRaw w {i} = (Finset.univ : Finset (Fin (w i))).image (fun j => (⟨i, j⟩ : Raw w)) := by
    ext ⟨a, j⟩
    simp only [blockRaw, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and,
      Finset.mem_image]
    constructor
    · rintro rfl; exact ⟨j, rfl⟩
    · rintro ⟨j', h⟩; exact (Sigma.mk.inj_iff.mp h).1.symm
  rw [heq, Finset.card_image_of_injOn]
  · simp
  · intro j₁ _ j₂ _ h
    have := Sigma.mk.inj_iff.mp h
    exact eq_of_heq this.2

lemma blockRaw_pair_card {n : ℕ} (w : Fin n → ℕ) {u v : Fin n} (hne : u ≠ v) :
    (blockRaw w {u, v}).card = w u + w v := by
  have hun : blockRaw w {u, v} = blockRaw w {u} ∪ blockRaw w {v} := by
    ext b; simp [blockRaw]
  have hdisj : Disjoint (blockRaw w {u}) (blockRaw w {v}) := by
    rw [Finset.disjoint_left]
    intro b h1 h2
    simp only [blockRaw, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  rw [hun, Finset.card_union_of_disjoint hdisj, blockRaw_single_card, blockRaw_single_card]

lemma blockRaw_pair_card_le {n : ℕ} (w : Fin n → ℕ) (u v : Fin n) :
    (blockRaw w {u, v}).card ≤ w u + w v := by
  by_cases h : u = v
  · subst h
    have : ({u, u} : Finset (Fin n)) = {u} := by simp
    rw [this, blockRaw_single_card]
    omega
  · rw [blockRaw_pair_card w h]

lemma parity_update_self {n : ℕ} {w : Fin n → ℕ} (y : Raw w → Bool) (i : Fin n) (j₀ : Fin (w i)) (val : Bool) :
    parity (Function.update y ⟨i, j₀⟩ val) i = xor (parity y i) (xor (y ⟨i, j₀⟩) val) := by
  unfold parity
  set S1 := (Finset.univ : Finset (Fin (w i))).filter (fun j => Function.update y ⟨i, j₀⟩ val ⟨i, j⟩ = true)
  set S0 := (Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)
  have hsame : ∀ j : Fin (w i), j ≠ j₀ → (j ∈ S1 ↔ j ∈ S0) := by
    intro j hj
    have hne : (⟨i, j⟩ : Raw w) ≠ ⟨i, j₀⟩ := by
      intro h; exact hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
    simp [S1, S0, Function.update_of_ne hne]
  have herase : S1.erase j₀ = S0.erase j₀ := by
    ext j
    simp only [Finset.mem_erase]
    by_cases hj : j = j₀
    · simp [hj]
    · simp [hj, hsame j hj]
  have h1 : j₀ ∈ S1 ↔ val = true := by simp [S1]
  have h0 : j₀ ∈ S0 ↔ y ⟨i, j₀⟩ = true := by simp [S0]
  have hc1 : S1.card = (S1.erase j₀).card + if val = true then 1 else 0 := by
    by_cases hv : val = true
    · simp [hv, Finset.card_erase_add_one (h1.mpr hv)]
    · simp [hv, Finset.erase_eq_of_notMem (mt h1.mp hv)]
  have hc0 : S0.card = (S0.erase j₀).card + if y ⟨i, j₀⟩ = true then 1 else 0 := by
    by_cases hy : y ⟨i, j₀⟩ = true
    · simp [hy, Finset.card_erase_add_one (h0.mpr hy)]
    · simp [hy, Finset.erase_eq_of_notMem (mt h0.mp hy)]
  rw [hc1, hc0, herase]
  cases hy : y ⟨i, j₀⟩ <;> cases hv : val <;> simp only [Bool.false_eq_true, ↓reduceIte,
    Bool.not_true, Bool.not_false, Bool.xor_false, Bool.xor_true, add_zero]
  · by_cases hodd : Odd (S0.erase j₀).card
    · have hnot : ¬ Odd ((S0.erase j₀).card + 1) := by
        rw [Nat.odd_iff] at hodd ⊢; omega
      simp [hodd, hnot]
    · have hodd' : Odd ((S0.erase j₀).card + 1) := by
        rw [Nat.odd_iff] at hodd ⊢; omega
      simp [hodd, hodd']
  · by_cases hodd : Odd (S0.erase j₀).card
    · have hnot : ¬ Odd ((S0.erase j₀).card + 1) := by
        rw [Nat.odd_iff] at hodd ⊢; omega
      simp [hodd, hnot]
    · have hodd' : Odd ((S0.erase j₀).card + 1) := by
        rw [Nat.odd_iff] at hodd ⊢; omega
      simp [hodd, hodd']

lemma parity_update_ne {n : ℕ} {w : Fin n → ℕ} (y : Raw w → Bool) {i₁ i₂ : Fin n}
    (hne : i₁ ≠ i₂) (j₀ : Fin (w i₁)) (val : Bool) :
    parity (Function.update y ⟨i₁, j₀⟩ val) i₂ = parity y i₂ := by
  have hS : (Finset.univ : Finset (Fin (w i₂))).filter (fun j => Function.update y ⟨i₁, j₀⟩ val ⟨i₂, j⟩ = true) =
      (Finset.univ : Finset (Fin (w i₂))).filter (fun j => y ⟨i₂, j⟩ = true) := by
    ext j
    have hne' : (⟨i₂, j⟩ : Raw w) ≠ ⟨i₁, j₀⟩ := by
      intro h; exact hne (Sigma.mk.inj_iff.mp h).1.symm
    simp [Function.update_of_ne hne']
  unfold parity
  rw [hS]

lemma parity_congr {n : ℕ} {w : Fin n → ℕ} {y₁ y₂ : Raw w → Bool} {i : Fin n}
    (h : ∀ j : Fin (w i), y₁ ⟨i, j⟩ = y₂ ⟨i, j⟩) :
    parity y₁ i = parity y₂ i := by
  have hS : (Finset.univ : Finset (Fin (w i))).filter (fun j => y₁ ⟨i, j⟩ = true) =
      (Finset.univ : Finset (Fin (w i))).filter (fun j => y₂ ⟨i, j⟩ = true) := by
    ext j
    simp [h j]
  unfold parity
  rw [hS]

lemma derivable_ax {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {C : Clause (Raw w)} (hax : liftAx F C) (hcard : C.card ≤ W) :
    Derivable F W C := by
  refine ⟨{[]}, ∅, fun _ => C, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨Finset.mem_singleton_self [], Finset.empty_subset _, ?_, ?_⟩
    · intro p b hp
      rw [Finset.mem_singleton] at hp
      exact absurd hp (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
    · intro p hp; exact absurd hp (Finset.notMem_empty p)
  · intro _ _; exact hcard
  · intro _ _; exact hax
  · intro p hp; exact absurd hp (Finset.notMem_empty p)

lemma derivable_res {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {C₁ C₂ R : Clause (Raw w)}
    (h1 : Derivable F W C₁) (h2 : Derivable F W C₂)
    (hres : IsResolvent C₁ C₂ R) (hR : R.card ≤ W) :
    Derivable F W R := by
  rcases h1 with ⟨N₁, J₁, line₁, hsh1, hroot1, hcard1, hax1, hres1⟩
  rcases h2 with ⟨N₂, J₂, line₂, hsh2, hroot2, hcard2, hax2, hres2⟩
  let N : Finset (List Bool) := insert [] (N₁.image (false :: ·) ∪ N₂.image (true :: ·))
  let J : Finset (List Bool) := insert [] (J₁.image (false :: ·) ∪ J₂.image (true :: ·))
  let line : List Bool → Clause (Raw w) := fun p =>
    match p with
    | [] => R
    | false :: q => line₁ q
    | true :: q => line₂ q
  refine ⟨N, J, line, ?_, rfl, ?_, ?_, ?_⟩
  · refine ⟨Finset.mem_insert_self _ _, ?_, ?_, ?_⟩
    · intro p hp
      simp only [J, N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · left; rfl
      · right; left; exact ⟨q, hsh1.2.1 hq, rfl⟩
      · right; right; exact ⟨q, hsh2.2.1 hq, rfl⟩
    · intro p b hp
      simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with hnil | ⟨q, hq, heq⟩ | ⟨q, hq, heq⟩
      · exact absurd hnil (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
      · cases p with
        | nil => exact Finset.mem_insert_self _ _
        | cons c r =>
            simp only [List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, hsh1.2.2.1 r b hq, rfl⟩))
      · cases p with
        | nil => exact Finset.mem_insert_self _ _
        | cons c r =>
            simp only [List.cons_append, List.cons.injEq] at heq
            rcases heq with ⟨rfl, rfl⟩
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r, hsh2.2.2.1 r b hq, rfl⟩))
    · intro p hp
      simp only [J, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
      rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · constructor
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], hsh1.1, rfl⟩))
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], hsh2.1, rfl⟩))
      · rcases hsh1.2.2.2 q hq with ⟨hf, ht⟩
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
               Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩))⟩
      · rcases hsh2.2.2.2 q hq with ⟨hf, ht⟩
        exact ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [false], hf, rfl⟩)),
               Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [true], ht, rfl⟩))⟩
  · intro p hp
    simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact hR
    · exact hcard1 q hq
    · exact hcard2 q hq
  · intro p hp
    rw [Finset.mem_sdiff] at hp
    rcases hp with ⟨hpN, hpJ⟩
    simp only [N, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hpN
    rcases hpN with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact absurd (Finset.mem_insert_self _ _) hpJ
    · apply hax1 q
      rw [Finset.mem_sdiff]
      refine ⟨hq, fun hqJ => hpJ (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hqJ, rfl⟩)))⟩
    · apply hax2 q
      rw [Finset.mem_sdiff]
      refine ⟨hq, fun hqJ => hpJ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hqJ, rfl⟩)))⟩
  · intro p hp
    simp only [J, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · simpa [line, hroot1, hroot2] using hres
    · simpa [line] using hres1 q hq
    · simpa [line] using hres2 q hq

lemma isResolvent_rawClause {n : ℕ} {w : Fin n → ℕ}
    (X₁ X₂ : Finset (Raw w)) (b₀ : Raw w) (hb1 : b₀ ∈ X₁) (hb2 : b₀ ∈ X₂) (y : Raw w → Bool) :
    IsResolvent
      (rawClause X₁ (Function.update y b₀ false))
      (rawClause X₂ (Function.update y b₀ true))
      (rawClause ((X₁ ∪ X₂).erase b₀) y) := by
  refine ⟨b₀, ?_, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨b₀, hb1, by simp⟩
  · exact Finset.mem_image.mpr ⟨b₀, hb2, by simp⟩
  · ext ⟨b, pol⟩
    simp only [rawClause, Finset.mem_union, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨a, ⟨hane, ha⟩, hpair⟩
      simp only [Prod.mk.injEq] at hpair
      rcases hpair with ⟨rfl, rfl⟩
      rcases ha with ha1 | ha2
      · left
        refine ⟨by intro h; exact hane (Prod.mk.inj h).1, a, ha1, ?_⟩
        simp [Function.update_of_ne hane]
      · right
        refine ⟨by intro h; exact hane (Prod.mk.inj h).1, a, ha2, ?_⟩
        simp [Function.update_of_ne hane]
    · rintro (⟨hneq, a, ha1, hpair⟩ | ⟨hneq, a, ha2, hpair⟩)
      · simp only [Prod.mk.injEq] at hpair
        rcases hpair with ⟨rfl, rfl⟩
        have hane : a ≠ b₀ := by
          intro h; subst h; simp at hneq
        refine ⟨a, ⟨hane, Or.inl ha1⟩, ?_⟩
        simp [Function.update_of_ne hane]
      · simp only [Prod.mk.injEq] at hpair
        rcases hpair with ⟨rfl, rfl⟩
        have hane : a ≠ b₀ := by
          intro h; subst h; simp at hneq
        refine ⟨a, ⟨hane, Or.inr ha2⟩, ?_⟩
        simp [Function.update_of_ne hane]

lemma derivable_empty_of_all_raw {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ} :
    ∀ X : Finset (Raw w), X.card ≤ W →
      (∀ y : Raw w → Bool, Derivable (w := w) F W (rawClause X y)) →
      Derivable (w := w) F W ∅ := by
  intro X
  induction X using Finset.induction_on with
  | empty =>
      intro _ hall
      simpa [rawClause] using hall (fun _ => false)
  | insert b₀ X' hb₀ ih =>
      intro hcard hall
      have hcard' : X'.card ≤ W := by
        rw [Finset.card_insert_of_notMem hb₀] at hcard; omega
      apply ih hcard'
      intro y
      have hT := hall (Function.update y b₀ false)
      have hF := hall (Function.update y b₀ true)
      have hres := isResolvent_rawClause (insert b₀ X') (insert b₀ X') b₀
        (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _) y
      have hun : ((insert b₀ X' ∪ insert b₀ X').erase b₀) = X' := by
        rw [Finset.union_idempotent, Finset.erase_insert hb₀]
      rw [hun] at hres
      exact derivable_res hT hF hres (by rw [rawClause_card]; exact hcard')

def EqDer {n : ℕ} {w : Fin n → ℕ} (F : Set (Clause (Fin n))) (W : ℕ)
    (u v : Fin n) (s : Bool) : Prop :=
  ∀ y : Raw w → Bool, xor (parity y u) (parity y v) ≠ s → Derivable F W (blockClause {u, v} y)

lemma eqDer_symm {n : ℕ} {w : Fin n → ℕ} {F : Set (Clause (Fin n))} {W : ℕ}
    {u v : Fin n} {s : Bool} (h : EqDer (w := w) F W u v s) :
    EqDer (w := w) F W v u s := by
  intro y hne
  have hne' : xor (parity y u) (parity y v) ≠ s := by rwa [Bool.xor_comm]
  have h1 := h y hne'
  have hpair : ({v, u} : Finset (Fin n)) = {u, v} := Finset.pair_comm v u
  simpa [blockClause, hpair] using h1

lemma eqDer_of_edge {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {u v : Fin n} {s : Bool} (he : E u v s)
    (hcard : if u = v then w u ≤ W else w u + w v ≤ W) :
    EqDer (w := w) (eqFormula E) W u v s := by
  intro y hne
  let a : Bool := parity y u
  let C : Clause (Fin n) := {(u, !a), (v, a ^^ s)}
  have hCF : C ∈ eqFormula E := ⟨u, v, s, a, he, rfl⟩
  have hCy : ∀ lit ∈ C, parity y lit.1 ≠ lit.2 := by
    intro lit hlit
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hlit
    rcases hlit with rfl | rfl
    · simp [a]
    · intro h
      apply hne
      dsimp only at h
      rw [h]
      dsimp only [a]
      cases parity y u <;> cases s <;> rfl
  have himg : C.image Prod.fst = {u, v} := by
    ext x; simp [C]
  have hax : liftAx (eqFormula E) (blockClause {u, v} y) := by
    refine ⟨C, hCF, y, hCy, ?_⟩
    simp [blockClause, rawClause, blockRaw, himg]
  have hc : (blockClause {u, v} y).card ≤ W := by
    rw [blockClause, rawClause_card]
    by_cases huv : u = v
    · subst huv
      have : ({u, u} : Finset (Fin n)) = {u} := by simp
      rw [this, blockRaw_single_card]
      simpa using hcard
    · rw [blockRaw_pair_card w huv]
      simpa [huv] using hcard
  exact derivable_ax hax hc

lemma bool_trans_1 (pr pb pa s₁ s₂ : Bool)
    (h : xor pr pb ≠ xor s₁ s₂) (h1 : xor pr pa ≠ s₁) : xor (!pa) pb ≠ s₂ := by
  cases pr <;> cases pb <;> cases pa <;> cases s₁ <;> cases s₂ <;> simp_all

lemma bool_trans_2 (pr pb pa s₁ s₂ : Bool)
    (h : xor pr pb ≠ xor s₁ s₂) (h1 : xor pr pa = s₁) : xor pa pb ≠ s₂ := by
  cases pr <;> cases pb <;> cases pa <;> cases s₁ <;> cases s₂ <;> simp_all

lemma bool_trans_3 (pr pa s₁ : Bool) (h1 : xor pr pa = s₁) : xor pr (!pa) ≠ s₁ := by
  cases pr <;> cases pa <;> cases s₁ <;> simp_all

lemma bool_flip_neq (pu pv pm s₁ s₂ : Bool)
    (h1 : xor pu pm ≠ s₁) (h2 : xor (!pm) pv ≠ s₂) : xor pu pv ≠ xor s₁ s₂ := by
  cases pu <;> cases pv <;> cases pm <;> cases s₁ <;> cases s₂ <;> simp_all

lemma bool_ax_contra (pu pv a s : Bool)
    (h1 : pu ≠ !a) (h2 : pv ≠ xor a s) (h3 : xor pu pv = s) : False := by
  cases pu <;> cases pv <;> cases a <;> cases s <;> simp_all

lemma eqDer_trans {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    {F : Set (Clause (Fin n))} {W : ℕ} {r a b : Fin n} {s₁ s₂ : Bool}
    (hra : r ≠ a) (hab : a ≠ b)
    (h1 : EqDer (w := w) F W r a s₁) (h2 : EqDer (w := w) F W a b s₂)
    (hwsum : w r + w a + w b ≤ W + 1) :
    EqDer (w := w) F W r b (xor s₁ s₂) := by
  intro y hne
  let A_raw : Finset (Raw w) := blockRaw w {a}
  let RB_raw : Finset (Raw w) := blockRaw w {r, b}
  have hAcard : A_raw.card = w a := blockRaw_single_card w a
  have hRBcard : RB_raw.card ≤ w r + w b := blockRaw_pair_card_le w r b
  have hdisj : Disjoint RB_raw A_raw := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [RB_raw, A_raw, blockRaw, Finset.mem_filter, Finset.mem_univ, Finset.mem_insert,
      Finset.mem_singleton, true_and] at hx1 hx2
    rcases hx1 with hxr | hxb
    · exact hra (hxr.symm.trans hx2)
    · exact hab (hx2.symm.trans hxb)
  have hstep : ∀ (m : ℕ) (S : Finset (Raw w)), S ⊆ A_raw → S.card < A_raw.card →
      A_raw.card - S.card ≤ m + 1 →
      ∀ z : Raw w → Bool, (∀ x ∈ RB_raw, z x = y x) →
        Derivable F W (rawClause (RB_raw ∪ S) z) := by
    intro m
    induction m with
    | zero =>
        intro S hSA hSlt hm z hz
        have hdiff_ne : (A_raw \ S).Nonempty := Finset.sdiff_nonempty.mpr (fun h => by
          have := Finset.card_le_card h; omega)
        rcases hdiff_ne with ⟨b₀, hb₀⟩
        rw [Finset.mem_sdiff] at hb₀
        rcases hb₀ with ⟨hb₀A, hb₀S⟩
        have hSeq : S = A_raw.erase b₀ := by
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            rw [Finset.mem_erase]
            exact ⟨fun h => hb₀S (h ▸ hx), hSA hx⟩
          · rw [Finset.card_erase_of_mem hb₀A]; omega
        have hb₀_fst : b₀.1 = a := by
          simpa [A_raw, blockRaw] using hb₀A
        rcases b₀ with ⟨a', j₀⟩
        dsimp only at hb₀_fst
        subst a'
        let zT := Function.update z ⟨a, j₀⟩ false
        let zF := Function.update z ⟨a, j₀⟩ true
        have hzT_r : parity zT r = parity y r := by
          dsimp only [zT]
          rw [parity_update_ne z hra.symm]
          apply parity_congr
          intro j
          exact hz ⟨r, j⟩ (by simp [RB_raw, blockRaw])
        have hzT_b : parity zT b = parity y b := by
          dsimp only [zT]
          rw [parity_update_ne z hab]
          apply parity_congr
          intro j
          exact hz ⟨b, j⟩ (by simp [RB_raw, blockRaw])
        have hzF_r : parity zF r = parity y r := by
          dsimp only [zF]
          rw [parity_update_ne z hra.symm]
          apply parity_congr
          intro j
          exact hz ⟨r, j⟩ (by simp [RB_raw, blockRaw])
        have hzF_b : parity zF b = parity y b := by
          dsimp only [zF]
          rw [parity_update_ne z hab]
          apply parity_congr
          intro j
          exact hz ⟨b, j⟩ (by simp [RB_raw, blockRaw])
        have hflip : parity zF a = !(parity zT a) := by
          have hT := parity_update_self z a j₀ false
          have hF := parity_update_self z a j₀ true
          dsimp only [zT, zF]
          rw [hT, hF]
          cases parity z a <;> cases z ⟨a, j₀⟩ <;> rfl
        have hcard_res : (rawClause (RB_raw ∪ S) z).card ≤ W := by
          rw [rawClause_card, Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hSA hdisj)]
          omega
        have hun_ra_ab : (blockRaw w {r, a} ∪ blockRaw w {a, b}).erase ⟨a, j₀⟩ = RB_raw ∪ S := by
          rw [hSeq]
          ext x
          simp only [Finset.mem_erase, Finset.mem_union, RB_raw, A_raw, blockRaw,
            Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_and]
          by_cases hx : x = ⟨a, j₀⟩
          · subst hx; simp [hra.symm, hab]
          · simp [hx]; tauto
        have hun_ab_ra : (blockRaw w {a, b} ∪ blockRaw w {r, a}).erase ⟨a, j₀⟩ = RB_raw ∪ S := by
          rw [Finset.union_comm]; exact hun_ra_ab
        by_cases hT1 : xor (parity zT r) (parity zT a) ≠ s₁
        · have hd1 : Derivable F W (rawClause (blockRaw w {r, a}) zT) := h1 zT hT1
          have hF2 : xor (parity zF a) (parity zF b) ≠ s₂ := by
            rw [hflip, hzF_b]
            rw [hzT_r] at hT1
            exact bool_trans_1 _ _ _ _ _ hne hT1
          have hd2 : Derivable F W (rawClause (blockRaw w {a, b}) zF) := h2 zF hF2
          have hres := isResolvent_rawClause (blockRaw w {r, a}) (blockRaw w {a, b}) ⟨a, j₀⟩
            (by simp [blockRaw]) (by simp [blockRaw]) z
          rw [hun_ra_ab] at hres
          exact derivable_res hd1 hd2 hres hcard_res
        · push Not at hT1
          have hT2 : xor (parity zT a) (parity zT b) ≠ s₂ := by
            rw [hzT_b]; rw [hzT_r] at hT1
            exact bool_trans_2 _ _ _ _ _ hne hT1
          have hF1 : xor (parity zF r) (parity zF a) ≠ s₁ := by
            rw [hzF_r, hflip]; rw [hzT_r] at hT1
            exact bool_trans_3 _ _ _ hT1
          have hd1 : Derivable F W (rawClause (blockRaw w {a, b}) zT) := h2 zT hT2
          have hd2 : Derivable F W (rawClause (blockRaw w {r, a}) zF) := h1 zF hF1
          have hres := isResolvent_rawClause (blockRaw w {a, b}) (blockRaw w {r, a}) ⟨a, j₀⟩
            (by simp [blockRaw]) (by simp [blockRaw]) z
          rw [hun_ab_ra] at hres
          exact derivable_res hd1 hd2 hres hcard_res
    | succ m ih =>
        intro S hSA hSlt hm z hz
        by_cases hbase : A_raw.card - S.card ≤ m + 1
        · exact ih S hSA hSlt hbase z hz
        · have hdiff_ne : (A_raw \ S).Nonempty := Finset.sdiff_nonempty.mpr (fun h => by
            have := Finset.card_le_card h; omega)
          rcases hdiff_ne with ⟨b₀, hb₀⟩
          rw [Finset.mem_sdiff] at hb₀
          rcases hb₀ with ⟨hb₀A, hb₀S⟩
          let S' := insert b₀ S
          have hS'A : S' ⊆ A_raw := Finset.insert_subset_iff.mpr ⟨hb₀A, hSA⟩
          have hS'card : S'.card = S.card + 1 := Finset.card_insert_of_notMem hb₀S
          have hS'lt : S'.card < A_raw.card := by omega
          have hb₀_not_RB : b₀ ∉ RB_raw := fun h => (Finset.disjoint_left.mp hdisj h) hb₀A
          have hdT := ih S' hS'A hS'lt (by omega) (Function.update z b₀ false) (fun x hx => by
            have hne' : x ≠ b₀ := fun h => hb₀_not_RB (h ▸ hx)
            rw [Function.update_of_ne hne', hz x hx])
          have hdF := ih S' hS'A hS'lt (by omega) (Function.update z b₀ true) (fun x hx => by
            have hne' : x ≠ b₀ := fun h => hb₀_not_RB (h ▸ hx)
            rw [Function.update_of_ne hne', hz x hx])
          have hres := isResolvent_rawClause (RB_raw ∪ S') (RB_raw ∪ S') b₀
            (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
            (Finset.mem_union_right _ (Finset.mem_insert_self _ _)) z
          have hun : ((RB_raw ∪ S') ∪ (RB_raw ∪ S')).erase b₀ = RB_raw ∪ S := by
            rw [Finset.union_idempotent]
            ext x
            simp only [Finset.mem_erase, Finset.mem_union, S', Finset.mem_insert]
            by_cases hx : x = b₀
            · subst hx; simp [hb₀_not_RB, hb₀S]
            · simp [hx]
          rw [hun] at hres
          have hcard_res : (rawClause (RB_raw ∪ S) z).card ≤ W := by
            rw [rawClause_card, Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hSA hdisj)]
            omega
          exact derivable_res hdT hdF hres hcard_res
  have hpos : 0 < A_raw.card := by rw [hAcard]; exact hw a
  have hfin := hstep (A_raw.card - 1) ∅ (Finset.empty_subset _) (by simpa using hpos) (by simp; omega) y (fun _ _ => rfl)
  simpa [RB_raw, blockClause] using hfin

lemma walk_complete {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    (root : Fin n) (len : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool)
    (hv0 : v 0 = root) (hvlen : v len = root)
    (hodd : Odd (((Finset.range len).filter (fun j => s j)).card))
    (hwalk : ∀ j < len, E (v j) (v (j + 1)) (s j) ∧ w root + w (v j) + w (v (j + 1)) ≤ W + 1) :
    Derivable (w := w) (eqFormula E) W ∅ := by
  let pref : ℕ → Bool := fun m => decide (Odd (((Finset.range m).filter (fun j => s j)).card))
  have hpref_step : ∀ m : ℕ, pref (m + 1) = xor (pref m) (s m) := by
    intro m
    unfold pref
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : m ∉ (Finset.range m).filter (fun j => s j) := by simp
    cases hsm : s m
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.xor_false]
    · simp only [↓reduceIte, Finset.card_insert_of_notMem hnot, Bool.xor_true]
      by_cases h : Odd (((Finset.range m).filter (fun j => s j)).card)
      · have hnot' : ¬ Odd (((Finset.range m).filter (fun j => s j)).card + 1) := by
          rw [Nat.odd_iff] at h ⊢; omega
        simp [h, hnot']
      · have hodd' : Odd (((Finset.range m).filter (fun j => s j)).card + 1) := by
          rw [Nat.odd_iff] at h ⊢; omega
        simp [h, hodd']
  have hind : ∀ m ≤ len, Derivable (w := w) (eqFormula E) W ∅ ∨
      EqDer (w := w) (eqFormula E) W root (v m) (pref m) := by
    intro m
    induction m with
    | zero =>
        intro _
        right
        rw [hv0]
        intro y hne
        simp [pref] at hne
    | succ m ih =>
        intro hm
        rcases ih (by omega) with hdone | heq
        · exact Or.inl hdone
        · rcases hwalk m (by omega) with ⟨hedge, hwsum⟩
          have hwm1 : 1 ≤ w (v m) := hw (v m)
          have hwm2 : 1 ≤ w (v (m + 1)) := hw (v (m + 1))
          have hwr : 1 ≤ w root := hw root
          have hstep_ed : EqDer (w := w) (eqFormula E) W (v m) (v (m + 1)) (s m) := by
            apply eqDer_of_edge hedge
            split_ifs <;> omega
          by_cases h1 : root = v m
          · rw [← h1] at heq hstep_ed
            by_cases hp : pref m = true
            · left
              rw [hp] at heq
              apply derivable_empty_of_all_raw (blockRaw w {root}) (by rw [blockRaw_single_card]; omega)
              intro y
              have := heq y (by simp)
              simpa [blockClause] using this
            · right
              have hpf : pref m = false := Bool.eq_false_iff.mpr hp
              rw [hpref_step, hpf, Bool.false_xor]
              exact hstep_ed
          · by_cases h2 : v m = v (m + 1)
            · rw [← h2] at hedge hstep_ed ⊢
              by_cases hsm : s m = true
              · left
                rw [hsm] at hstep_ed
                apply derivable_empty_of_all_raw (blockRaw w {v m}) (by rw [blockRaw_single_card]; omega)
                intro y
                have := hstep_ed y (by simp)
                simpa [blockClause] using this
              · right
                have hsmf : s m = false := Bool.eq_false_iff.mpr hsm
                rw [hpref_step, hsmf, Bool.xor_false]
                exact heq
            · right
              rw [hpref_step]
              exact eqDer_trans hw h1 h2 heq hstep_ed hwsum
  rcases hind len le_rfl with hdone | heq
  · exact hdone
  · have hlen_pos : 0 < len := by
      by_contra h0
      have hlen0 : len = 0 := by omega
      subst hlen0
      simp at hodd
    have hwrW : w root ≤ W := by
      have hw0 := (hwalk 0 hlen_pos).2
      have := hw (v 0)
      have := hw (v 1)
      omega
    rw [hvlen] at heq
    have hpt : pref len = true := decide_eq_true hodd
    rw [hpt] at heq
    apply derivable_empty_of_all_raw (blockRaw w {root}) (by rw [blockRaw_single_card]; exact hwrW)
    intro y
    have := heq y (by simp)
    simpa [blockClause] using this

def Direct {n : ℕ} (w : Fin n → ℕ) (E : Fin n → Fin n → Bool → Prop) (W : ℕ)
    (u v : Fin n) (s : Bool) : Prop :=
  E u v s ∧ (if u = v then w u ≤ W else w u + w v ≤ W)

def Cl {n : ℕ} (w : Fin n → ℕ) (E : Fin n → Fin n → Bool → Prop) (W : ℕ)
    (u v : Fin n) (s : Bool) : Prop :=
  ∀ P : Fin n → Fin n → Bool → Prop,
    (∀ x, P x x false) →
    (∀ x y t, Direct w E W x y t → P x y t) →
    (∀ x y t, P x y t → P y x t) →
    (∀ x m y t₁ t₂, P x m t₁ → P m y t₂ → w x + w m + w y ≤ W + 1 → P x y (xor t₁ t₂)) →
    P u v s

lemma cl_refl {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ} (x : Fin n) :
    Cl w E W x x false := fun _ h _ _ _ => h x

lemma cl_edge {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {x y : Fin n} {t : Bool} (h : Direct w E W x y t) :
    Cl w E W x y t := fun _ _ hE _ _ => hE x y t h

lemma cl_symm {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {x y : Fin n} {t : Bool} (h : Cl w E W x y t) :
    Cl w E W y x t := fun P h1 h2 h3 h4 => h3 x y t (h P h1 h2 h3 h4)

lemma cl_trans {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {x m y : Fin n} {t₁ t₂ : Bool} (h₁ : Cl w E W x m t₁) (h₂ : Cl w E W m y t₂)
    (ht : w x + w m + w y ≤ W + 1) :
    Cl w E W x y (xor t₁ t₂) :=
  fun P h1 h2 h3 h4 => h4 x m y t₁ t₂ (h₁ P h1 h2 h3 h4) (h₂ P h1 h2 h3 h4) ht

def fullBlocks {n : ℕ} {w : Fin n → ℕ} (C : Clause (Raw w)) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => ∀ j : Fin (w i), (⟨i, j⟩, false) ∈ C ∨ (⟨i, j⟩, true) ∈ C)

def Falsifies {n : ℕ} {w : Fin n → ℕ} (y : Raw w → Bool) (C : Clause (Raw w)) : Prop :=
  ∀ lit ∈ C, y lit.1 ≠ lit.2

def ClSat {n : ℕ} {w : Fin n → ℕ} (E : Fin n → Fin n → Bool → Prop) (W : ℕ)
    (B : Finset (Fin n)) (y : Raw w → Bool) : Prop :=
  ∀ u ∈ B, ∀ v ∈ B, ∀ s : Bool, Cl w E W u v s → xor (parity y u) (parity y v) = s

def Safe {n : ℕ} {w : Fin n → ℕ} (E : Fin n → Fin n → Bool → Prop) (W : ℕ)
    (C : Clause (Raw w)) : Prop :=
  ∃ y : Raw w → Bool, Falsifies y C ∧ ClSat E W (fullBlocks C) y

lemma fullBlocks_weight_le {n : ℕ} {w : Fin n → ℕ} (C : Clause (Raw w))
    {u v m : Fin n} (huv : u ≠ v) (hum : u ≠ m) (hvm : v ≠ m)
    (hu : u ∈ fullBlocks C) (hv : v ∈ fullBlocks C)
    (j₀ : Fin (w m)) (hm : ∀ j : Fin (w m), j ≠ j₀ → (⟨m, j⟩, false) ∈ C ∨ (⟨m, j⟩, true) ∈ C) :
    w u + w m + w v ≤ C.card + 1 := by
  let S : Finset (Raw w) := blockRaw w {u} ∪ blockRaw w {v} ∪ (blockRaw w {m}).erase ⟨m, j₀⟩
  have hsub : S ⊆ C.image Prod.fst := by
    intro ⟨a, j⟩ hmem
    simp only [S, Finset.mem_union, Finset.mem_erase, blockRaw, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_singleton, true_and] at hmem
    rw [Finset.mem_image]
    rcases hmem with (rfl | rfl) | ⟨hne, rfl⟩
    · rcases (Finset.mem_filter.mp hu).2 j with h | h
      · exact ⟨(⟨a, j⟩, false), h, rfl⟩
      · exact ⟨(⟨a, j⟩, true), h, rfl⟩
    · rcases (Finset.mem_filter.mp hv).2 j with h | h
      · exact ⟨(⟨a, j⟩, false), h, rfl⟩
      · exact ⟨(⟨a, j⟩, true), h, rfl⟩
    · have hjne : j ≠ j₀ := fun h => hne (by subst h; rfl)
      rcases hm j hjne with h | h
      · exact ⟨(⟨a, j⟩, false), h, rfl⟩
      · exact ⟨(⟨a, j⟩, true), h, rfl⟩
  have hd1 : Disjoint (blockRaw w {u}) (blockRaw w {v}) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [blockRaw, Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton, true_and] at hx1 hx2
    exact huv (hx1.symm.trans hx2)
  have hd2 : Disjoint (blockRaw w {u} ∪ blockRaw w {v}) ((blockRaw w {m}).erase ⟨m, j₀⟩) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_union, Finset.mem_erase, blockRaw, Finset.mem_filter, Finset.mem_univ,
      Finset.mem_singleton, true_and] at hx1 hx2
    rcases hx1 with h1 | h2
    · exact hum (h1.symm.trans hx2.2)
    · exact hvm (h2.symm.trans hx2.2)
  have hScard : S.card = w u + w v + (w m - 1) := by
    dsimp only [S]
    rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      Finset.card_erase_of_mem (by simp [blockRaw]),
      blockRaw_single_card, blockRaw_single_card, blockRaw_single_card]
  have hle1 : S.card ≤ (C.image Prod.fst).card := Finset.card_le_card hsub
  have hle2 : (C.image Prod.fst).card ≤ C.card := Finset.card_image_le
  have hwm : 1 ≤ w m := by
    have := j₀.isLt; omega
  omega

lemma safe_res_step {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    (hnoLoop : ∀ i, ¬ Cl w E W i i true)
    (hnoOpp : ∀ i j, ¬ (Cl w E W i j false ∧ Cl w E W i j true))
    {C₁ C₂ R : Clause (Raw w)} (hRcard : R.card ≤ W)
    (hres : IsResolvent C₁ C₂ R) (hsafe : Safe E W R) :
    Safe E W C₁ ∨ Safe E W C₂ := by
  rcases hres with ⟨⟨m, j₀⟩, hC1, hC2, hReq⟩
  rcases hsafe with ⟨y, hyF, hyCl⟩
  by_cases h1taut : (⟨m, j₀⟩, false) ∈ C₁
  · right
    have hmemR : (⟨m, j₀⟩, false) ∈ R := by
      rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, h1taut⟩)
    have hyb : y ⟨m, j₀⟩ = true := by
      have := hyF (⟨m, j₀⟩, false) hmemR
      cases h : y ⟨m, j₀⟩ <;> simp_all
    refine ⟨y, ?_, ?_⟩
    · intro lit hlit
      by_cases hl : lit = (⟨m, j₀⟩, false)
      · subst hl; simp [hyb]
      · exact hyF lit (by rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hl, hlit⟩))
    · have hsub : fullBlocks C₂ ⊆ fullBlocks R := by
        intro i hi
        simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        intro j
        by_cases hbm : (⟨i, j⟩ : Raw w) = ⟨m, j₀⟩
        · left; rw [hbm]; exact hmemR
        · rcases hi j with h | h
          · left; rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun heq => hbm (Prod.mk.inj heq).1, h⟩)
          · right; rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp, h⟩)
      exact fun u hu v hv s hcl => hyCl u (hsub hu) v (hsub hv) s hcl
  · by_cases h2taut : (⟨m, j₀⟩, true) ∈ C₂
    · left
      have hmemR : (⟨m, j₀⟩, true) ∈ R := by
        rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp, h2taut⟩)
      have hyb : y ⟨m, j₀⟩ = false := by
        have := hyF (⟨m, j₀⟩, true) hmemR
        cases h : y ⟨m, j₀⟩ <;> simp_all
      refine ⟨y, ?_, ?_⟩
      · intro lit hlit
        by_cases hl : lit = (⟨m, j₀⟩, true)
        · subst hl; simp [hyb]
        · exact hyF lit (by rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hl, hlit⟩))
      · have hsub : fullBlocks C₁ ⊆ fullBlocks R := by
          intro i hi
          simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
          intro j
          by_cases hbm : (⟨i, j⟩ : Raw w) = ⟨m, j₀⟩
          · right; rw [hbm]; exact hmemR
          · rcases hi j with h | h
            · left; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, h⟩)
            · right; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun heq => hbm (Prod.mk.inj heq).1, h⟩)
        exact fun u hu v hv s hcl => hyCl u (hsub hu) v (hsub hv) s hcl
    · let yT := Function.update y ⟨m, j₀⟩ false
      let yF := Function.update y ⟨m, j₀⟩ true
      have hyT_F : Falsifies yT C₁ := by
        intro lit hlit
        by_cases hl : lit = (⟨m, j₀⟩, true)
        · subst hl; simp [yT]
        · have hne : lit.1 ≠ ⟨m, j₀⟩ := by
            intro h
            rcases lit with ⟨b, pol⟩
            dsimp only at h
            subst h
            cases pol
            · exact h1taut hlit
            · exact hl rfl
          dsimp only [yT]
          rw [Function.update_of_ne hne]
          exact hyF lit (by rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hl, hlit⟩))
      have hyF_F : Falsifies yF C₂ := by
        intro lit hlit
        by_cases hl : lit = (⟨m, j₀⟩, false)
        · subst hl; simp [yF]
        · have hne : lit.1 ≠ ⟨m, j₀⟩ := by
            intro h
            rcases lit with ⟨b, pol⟩
            dsimp only at h
            subst h
            cases pol
            · exact hl rfl
            · exact h2taut hlit
          dsimp only [yF]
          rw [Function.update_of_ne hne]
          exact hyF lit (by rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hl, hlit⟩))
      have hsub1 : (fullBlocks C₁).erase m ⊆ fullBlocks R := by
        intro i hi
        rw [Finset.mem_erase] at hi
        rcases hi with ⟨him, hiC1⟩
        simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hiC1 ⊢
        intro j
        have hne : (⟨i, j⟩ : Raw w) ≠ ⟨m, j₀⟩ := fun h => him (Sigma.mk.inj_iff.mp h).1
        rcases hiC1 j with h | h
        · left; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, h⟩)
        · right; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun heq => hne (Prod.mk.inj heq).1, h⟩)
      have hsub2 : (fullBlocks C₂).erase m ⊆ fullBlocks R := by
        intro i hi
        rw [Finset.mem_erase] at hi
        rcases hi with ⟨him, hiC2⟩
        simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hiC2 ⊢
        intro j
        have hne : (⟨i, j⟩ : Raw w) ≠ ⟨m, j₀⟩ := fun h => him (Sigma.mk.inj_iff.mp h).1
        rcases hiC2 j with h | h
        · left; rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun heq => hne (Prod.mk.inj heq).1, h⟩)
        · right; rw [hReq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp, h⟩)
      by_cases hs1 : ClSat E W (fullBlocks C₁) yT
      · exact Or.inl ⟨yT, hyT_F, hs1⟩
      · by_cases hs2 : ClSat E W (fullBlocks C₂) yF
        · exact Or.inr ⟨yF, hyF_F, hs2⟩
        · exfalso
          have hex1 : ∃ u ∈ (fullBlocks C₁).erase m, ∃ s₁ : Bool,
              Cl w E W u m s₁ ∧ xor (parity y u) (parity yT m) ≠ s₁ := by
            unfold ClSat at hs1
            push Not at hs1
            rcases hs1 with ⟨a, ha, b, hb, s₁, hcl, hneq⟩
            by_cases ham : a = m
            · subst a
              by_cases hbm : b = m
              · subst b
                cases s₁
                · simp at hneq
                · exact absurd hcl (hnoLoop m)
              · refine ⟨b, Finset.mem_erase.mpr ⟨hbm, hb⟩, s₁, cl_symm hcl, ?_⟩
                dsimp only [yT] at hneq ⊢
                rw [parity_update_ne y (Ne.symm hbm)] at hneq
                rwa [Bool.xor_comm]
            · by_cases hbm : b = m
              · subst b
                refine ⟨a, Finset.mem_erase.mpr ⟨ham, ha⟩, s₁, hcl, ?_⟩
                dsimp only [yT] at hneq ⊢
                rwa [parity_update_ne y (Ne.symm ham)] at hneq
              · dsimp only [yT] at hneq
                rw [parity_update_ne y (Ne.symm ham), parity_update_ne y (Ne.symm hbm)] at hneq
                exact absurd (hyCl a (hsub1 (Finset.mem_erase.mpr ⟨ham, ha⟩))
                  b (hsub1 (Finset.mem_erase.mpr ⟨hbm, hb⟩)) s₁ hcl) hneq
          have hex2 : ∃ v ∈ (fullBlocks C₂).erase m, ∃ s₂ : Bool,
              Cl w E W m v s₂ ∧ xor (parity yF m) (parity y v) ≠ s₂ := by
            unfold ClSat at hs2
            push Not at hs2
            rcases hs2 with ⟨a, ha, b, hb, s₂, hcl, hneq⟩
            by_cases ham : a = m
            · subst a
              by_cases hbm : b = m
              · subst b
                cases s₂
                · simp at hneq
                · exact absurd hcl (hnoLoop m)
              · refine ⟨b, Finset.mem_erase.mpr ⟨hbm, hb⟩, s₂, hcl, ?_⟩
                dsimp only [yF] at hneq ⊢
                rwa [parity_update_ne y (Ne.symm hbm)] at hneq
            · by_cases hbm : b = m
              · subst b
                refine ⟨a, Finset.mem_erase.mpr ⟨ham, ha⟩, s₂, cl_symm hcl, ?_⟩
                dsimp only [yF] at hneq ⊢
                rw [parity_update_ne y (Ne.symm ham)] at hneq
                rwa [Bool.xor_comm]
              · dsimp only [yF] at hneq
                rw [parity_update_ne y (Ne.symm ham), parity_update_ne y (Ne.symm hbm)] at hneq
                exact absurd (hyCl a (hsub2 (Finset.mem_erase.mpr ⟨ham, ha⟩))
                  b (hsub2 (Finset.mem_erase.mpr ⟨hbm, hb⟩)) s₂ hcl) hneq
          rcases hex1 with ⟨u, hu, s₁, hcl1, hneq1⟩
          rcases hex2 with ⟨v, hv, s₂, hcl2, hneq2⟩
          have hflip : parity yF m = !(parity yT m) := by
            have hT := parity_update_self y m j₀ false
            have hF := parity_update_self y m j₀ true
            dsimp only [yT, yF]
            rw [hT, hF]
            cases parity y m <;> cases y ⟨m, j₀⟩ <;> rfl
          have huv_neq : xor (parity y u) (parity y v) ≠ xor s₁ s₂ := by
            rw [hflip] at hneq2
            exact bool_flip_neq _ _ _ _ _ hneq1 hneq2
          by_cases huv : u = v
          · subst huv
            have hsne : s₁ ≠ s₂ := by
              cases s₁ <;> cases s₂ <;> simp_all
            cases s₁ <;> cases s₂
            · exact hsne rfl
            · exact hnoOpp u m ⟨hcl1, cl_symm hcl2⟩
            · exact hnoOpp u m ⟨cl_symm hcl2, hcl1⟩
            · exact hsne rfl
          · have hm_in_C1 : m ∈ fullBlocks C₁ := by
              by_contra hnot
              apply hs1
              have hsub1' : fullBlocks C₁ ⊆ fullBlocks R := by
                intro i hi
                exact hsub1 (Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hi), hi⟩)
              intro a ha b hb s hcl
              have ham : a ≠ m := fun h => hnot (h ▸ ha)
              have hbm : b ≠ m := fun h => hnot (h ▸ hb)
              rw [parity_update_ne y (Ne.symm ham), parity_update_ne y (Ne.symm hbm)]
              exact hyCl a (hsub1' ha) b (hsub1' hb) s hcl
            have hm_rest : ∀ j : Fin (w m), j ≠ j₀ → (⟨m, j⟩, false) ∈ R ∨ (⟨m, j⟩, true) ∈ R := by
              intro j hj
              have hne : (⟨m, j⟩ : Raw w) ≠ ⟨m, j₀⟩ := fun h => hj (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
              rcases (Finset.mem_filter.mp hm_in_C1).2 j with h | h
              · left; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, h⟩)
              · right; rw [hReq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun heq => hne (Prod.mk.inj heq).1, h⟩)
            have htrip : w u + w m + w v ≤ W + 1 := by
              have hle := fullBlocks_weight_le R huv (Finset.ne_of_mem_erase hu)
                (Finset.ne_of_mem_erase hv) (hsub1 hu) (hsub2 hv) j₀ hm_rest
              omega
            have hcl12 : Cl w E W u v (xor s₁ s₂) := cl_trans hcl1 hcl2 htrip
            exact huv_neq (hyCl u (hsub1 hu) v (hsub2 hv) (xor s₁ s₂) hcl12)

lemma leaf_not_safe {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {A : Clause (Raw w)} (hcardA : A.card ≤ W) (hleaf : liftAx (eqFormula E) A)
    (hsafe : Safe E W A) : False := by
  rcases hleaf with ⟨C, ⟨u, v, s, a, he, rfl⟩, y₀, hCy₀, hAeq⟩
  rcases hsafe with ⟨y, hyF, hyCl⟩
  have himg : ({(u, !a), (v, a ^^ s)} : Clause (Fin n)).image Prod.fst = {u, v} := by
    ext x; simp
  rw [himg] at hAeq
  have hdir : Direct w E W u v s := by
    refine ⟨he, ?_⟩
    have hc : A.card = (blockRaw w {u, v}).card := by
      rw [hAeq]
      exact rawClause_card (blockRaw w {u, v}) y₀
    by_cases huv : u = v
    · subst huv
      have : ({u, u} : Finset (Fin n)) = {u} := by simp
      rw [this, blockRaw_single_card] at hc
      simpa using (by omega : w u ≤ W)
    · rw [blockRaw_pair_card w huv] at hc
      simpa [huv] using (by omega : w u + w v ≤ W)
  have hcl : Cl w E W u v s := cl_edge hdir
  have hu_full : u ∈ fullBlocks A := by
    simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    have hmem : (⟨u, j⟩, !(y₀ ⟨u, j⟩)) ∈ A := by
      rw [hAeq]; exact Finset.mem_image.mpr ⟨⟨u, j⟩, by simp, rfl⟩
    cases hy0 : y₀ ⟨u, j⟩
    · right; simpa [hy0] using hmem
    · left; simpa [hy0] using hmem
  have hv_full : v ∈ fullBlocks A := by
    simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j
    have hmem : (⟨v, j⟩, !(y₀ ⟨v, j⟩)) ∈ A := by
      rw [hAeq]; exact Finset.mem_image.mpr ⟨⟨v, j⟩, by simp, rfl⟩
    cases hy0 : y₀ ⟨v, j⟩
    · right; simpa [hy0] using hmem
    · left; simpa [hy0] using hmem
  have hy_u : parity y u = parity y₀ u := by
    apply parity_congr
    intro j
    have hmem : (⟨u, j⟩, !(y₀ ⟨u, j⟩)) ∈ A := by
      rw [hAeq]; exact Finset.mem_image.mpr ⟨⟨u, j⟩, by simp, rfl⟩
    have hf := hyF _ hmem
    dsimp only at hf
    cases h1 : y ⟨u, j⟩ <;> cases h2 : y₀ ⟨u, j⟩ <;> simp_all
  have hy_v : parity y v = parity y₀ v := by
    apply parity_congr
    intro j
    have hmem : (⟨v, j⟩, !(y₀ ⟨v, j⟩)) ∈ A := by
      rw [hAeq]; exact Finset.mem_image.mpr ⟨⟨v, j⟩, by simp, rfl⟩
    have hf := hyF _ hmem
    dsimp only at hf
    cases h1 : y ⟨v, j⟩ <;> cases h2 : y₀ ⟨v, j⟩ <;> simp_all
  have hsat := hyCl u hu_full v hv_full s hcl
  rw [hy_u, hy_v] at hsat
  have h1 := hCy₀ (u, !a) (by simp)
  have h2 := hCy₀ (v, a ^^ s) (by simp)
  dsimp only at h1 h2
  exact bool_ax_contra _ _ _ _ h1 h2 hsat

lemma small_implies_cl_contra {n : ℕ} {w : Fin n → ℕ} (hw : ∀ i, 0 < w i)
    {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    (hsmall : Derivable (w := w) (eqFormula E) W ∅) :
    (∃ i, Cl w E W i i true) ∨ (∃ i j, i ≠ j ∧ Cl w E W i j false ∧ Cl w E W i j true) := by
  by_contra hcons
  push Not at hcons
  have hnoLoop : ∀ i, ¬ Cl w E W i i true := hcons.1
  have hnoOpp : ∀ i j, ¬ (Cl w E W i j false ∧ Cl w E W i j true) := by
    intro i j ⟨hf, ht⟩
    by_cases hij : i = j
    · subst hij; exact hnoLoop i ht
    · exact hcons.2 i j hij hf ht
  rcases hsmall with ⟨N, J, line, hsh, hroot, hcard, hax, hres⟩
  let maxL : ℕ := N.sup List.length
  have hsafe_leaf : ∀ (m : ℕ) (p : List Bool), p ∈ N → Safe E W (line p) →
      maxL - p.length ≤ m → False := by
    intro m
    induction m with
    | zero =>
        intro p hpN hpSafe hlen
        by_cases hpJ : p ∈ J
        · have hch := (hsh.2.2.2 p hpJ).1
          have hle : (p ++ [false]).length ≤ maxL := Finset.le_sup (f := List.length) hch
          simp at hle
          omega
        · exact leaf_not_safe (hcard p hpN) (hax p (Finset.mem_sdiff.mpr ⟨hpN, hpJ⟩)) hpSafe
    | succ m ih =>
        intro p hpN hpSafe hlen
        by_cases hpJ : p ∈ J
        · rcases hsh.2.2.2 p hpJ with ⟨hfN, htN⟩
          have hlen1 : maxL - (p ++ [false]).length ≤ m := by
            have hle : (p ++ [false]).length ≤ maxL := Finset.le_sup (f := List.length) hfN
            simp at hle ⊢; omega
          have hlen2 : maxL - (p ++ [true]).length ≤ m := by
            have hle : (p ++ [true]).length ≤ maxL := Finset.le_sup (f := List.length) htN
            simp at hle ⊢; omega
          rcases safe_res_step hnoLoop hnoOpp (hcard p hpN) (hres p hpJ) hpSafe with h1 | h2
          · exact ih (p ++ [false]) hfN h1 hlen1
          · exact ih (p ++ [true]) htN h2 hlen2
        · exact leaf_not_safe (hcard p hpN) (hax p (Finset.mem_sdiff.mpr ⟨hpN, hpJ⟩)) hpSafe
  have hrootSafe : Safe E W (line []) := by
    rw [hroot]
    refine ⟨fun _ => false, fun _ h => absurd h (Finset.notMem_empty _), ?_⟩
    intro u hu
    simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have h0 := hu ⟨0, hw u⟩
    simp only [Finset.notMem_empty, or_self] at h0
  exact hsafe_leaf maxL [] hsh.1 hrootSafe (by simp)

def GoodEdge {n : ℕ} (w : Fin n → ℕ) (E : Fin n → Fin n → Bool → Prop) (W : ℕ)
    (U : Finset (Fin n)) (x y : Fin n) (s : Bool) : Prop :=
  E x y s ∧ x ∈ U ∧ y ∈ U ∧ ∃ z ∈ U, w z + w x + w y ≤ W + 1

def GWalk {n : ℕ} (w : Fin n → ℕ) (E : Fin n → Fin n → Bool → Prop) (W : ℕ)
    (U : Finset (Fin n)) (a b : Fin n) (p : Bool) : Prop :=
  ∃ (len : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool),
    v 0 = a ∧ v len = b ∧
    decide (Odd (((Finset.range len).filter (fun j => s j)).card)) = p ∧
    ∀ j < len, GoodEdge w E W U (v j) (v (j + 1)) (s j)

lemma gwalk_refl {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {U : Finset (Fin n)} (a : Fin n) : GWalk w E W U a a false :=
  ⟨0, fun _ => a, fun _ => false, rfl, rfl, by decide, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

lemma gwalk_single {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {U : Finset (Fin n)} {a b : Fin n} {t : Bool} (h : GoodEdge w E W U a b t) :
    GWalk w E W U a b t := by
  refine ⟨1, fun k => if k = 0 then a else b, fun _ => t, rfl, rfl, ?_, ?_⟩
  · cases t <;> decide
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using h

lemma gwalk_mono {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {U₁ U₂ : Finset (Fin n)} (hsub : U₁ ⊆ U₂) {a b : Fin n} {p : Bool}
    (hw : GWalk w E W U₁ a b p) : GWalk w E W U₂ a b p := by
  rcases hw with ⟨len, v, s, h0, hl, hp, hedge⟩
  refine ⟨len, v, s, h0, hl, hp, fun j hj => ?_⟩
  rcases hedge j hj with ⟨he, hx, hy, z, hz, hwz⟩
  exact ⟨he, hsub hx, hsub hy, z, hsub hz, hwz⟩

lemma gwalk_append {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop} {W : ℕ}
    {U : Finset (Fin n)} {a b c : Fin n} {p₁ p₂ : Bool}
    (h1 : GWalk w E W U a b p₁) (h2 : GWalk w E W U b c p₂) :
    GWalk w E W U a c (xor p₁ p₂) := by
  rcases h1 with ⟨l₁, v₁, s₁, h10, h1l, hp1, he1⟩
  rcases h2 with ⟨l₂, v₂, s₂, h20, h2l, hp2, he2⟩
  let v : ℕ → Fin n := fun k => if k ≤ l₁ then v₁ k else v₂ (k - l₁)
  let s : ℕ → Bool := fun k => if k < l₁ then s₁ k else s₂ (k - l₁)
  refine ⟨l₁ + l₂, v, s, ?_, ?_, ?_, ?_⟩
  · simp [v, h10]
  · by_cases hl2 : l₂ = 0
    · subst hl2; simp [v, h1l, ← h20, h2l]
    · simp [v, show ¬ l₁ + l₂ ≤ l₁ by omega, h2l]
  · have hpart : ((Finset.range (l₁ + l₂)).filter (fun j => s j)).card =
        ((Finset.range l₁).filter (fun j => s₁ j)).card +
        ((Finset.range l₂).filter (fun j => s₂ j)).card := by
      let S1 := (Finset.range l₁).filter (fun j => s₁ j)
      let S2 := ((Finset.range l₂).filter (fun j => s₂ j)).image (· + l₁)
      have hdisj : Disjoint S1 S2 := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [S1, S2, Finset.mem_filter, Finset.mem_range, Finset.mem_image] at hx1 hx2
        rcases hx2 with ⟨y, _, rfl⟩
        omega
      have hun : (Finset.range (l₁ + l₂)).filter (fun j => s j) = S1 ∪ S2 := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, S1, S2, Finset.mem_image]
        by_cases hx : x < l₁
        · simp only [s, hx, ↓reduceIte, true_and]
          constructor
          · rintro ⟨_, hsx⟩; exact Or.inl hsx
          · rintro (hsx | ⟨y, _, rfl⟩)
            · exact ⟨by omega, hsx⟩
            · omega
        · constructor
          · rintro ⟨hlt, hsx⟩
            right
            refine ⟨x - l₁, ⟨by omega, ?_⟩, by omega⟩
            simpa [s, hx] using hsx
          · rintro (⟨hlt, _⟩ | ⟨y, ⟨hyl, hsy⟩, rfl⟩)
            · omega
            · refine ⟨by omega, ?_⟩
              simp [s, show ¬ y + l₁ < l₁ by omega, hsy]
      rw [hun, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
    rw [hpart, ← hp1, ← hp2]
    set c1 := ((Finset.range l₁).filter (fun j => s₁ j)).card
    set c2 := ((Finset.range l₂).filter (fun j => s₂ j)).card
    by_cases h1 : Odd c1 <;> by_cases h2 : Odd c2
    · have hnot : ¬ Odd (c1 + c2) := by rw [Nat.odd_iff] at h1 h2 ⊢; omega
      simp [h1, h2, hnot]
    · have hodd : Odd (c1 + c2) := by rw [Nat.odd_iff] at h1 h2 ⊢; omega
      simp [h1, h2, hodd]
    · have hodd : Odd (c1 + c2) := by rw [Nat.odd_iff] at h1 h2 ⊢; omega
      simp [h1, h2, hodd]
    · have hnot : ¬ Odd (c1 + c2) := by rw [Nat.odd_iff] at h1 h2 ⊢; omega
      simp [h1, h2, hnot]
  · intro j hj
    by_cases hj1 : j < l₁
    · have hle1 : j ≤ l₁ := by omega
      have hle2 : j + 1 ≤ l₁ := by omega
      simpa [v, s, hj1, hle1, hle2] using he1 j hj1
    · have hlt2 : j - l₁ < l₂ := by omega
      have hej := he2 (j - l₁) hlt2
      have hsub : j + 1 - l₁ = j - l₁ + 1 := by omega
      have hvj : v j = v₂ (j - l₁) := by
        by_cases heq : j = l₁
        · subst heq; simp [v, h1l, h20]
        · simp [v, show ¬ j ≤ l₁ by omega]
      have hvj1 : v (j + 1) = v₂ (j - l₁ + 1) := by
        simp [v, show ¬ j + 1 ≤ l₁ by omega, hsub]
      have hsj : s j = s₂ (j - l₁) := by simp [s, hj1]
      rw [hvj, hvj1, hsj]
      exact hej

lemma gwalk_rev {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hEsym : ∀ u v s, E u v s → E v u s) {W : ℕ}
    {U : Finset (Fin n)} {a b : Fin n} {p : Bool}
    (hw : GWalk w E W U a b p) : GWalk w E W U b a p := by
  rcases hw with ⟨len, v, s, h0, hl, hp, hedge⟩
  let v' : ℕ → Fin n := fun k => v (len - k)
  let s' : ℕ → Bool := fun k => s (len - 1 - k)
  refine ⟨len, v', s', ?_, ?_, ?_, ?_⟩
  · simp [v', hl]
  · simp [v', h0]
  · have hcard : ((Finset.range len).filter (fun j => s' j)).card =
        ((Finset.range len).filter (fun j => s j)).card := by
      refine Finset.card_bij (fun j _ => len - 1 - j) ?_ ?_ ?_
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range, s'] at hj ⊢
        exact ⟨by omega, hj.2⟩
      · intro j₁ hj₁ j₂ hj₂ heq
        simp only [Finset.mem_filter, Finset.mem_range] at hj₁ hj₂
        omega
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_range] at hk
        refine ⟨len - 1 - k, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range, s']
        refine ⟨by omega, ?_⟩
        rw [show len - 1 - (len - 1 - k) = k by omega]
        exact hk.2
    rw [hcard, hp]
  · intro j hj
    have hidx : len - 1 - j < len := by omega
    rcases hedge (len - 1 - j) hidx with ⟨he, hx, hy, z, hz, hwz⟩
    have h1 : len - (j + 1) = len - 1 - j := by omega
    have h2 : len - j = len - 1 - j + 1 := by omega
    dsimp only [v', s']
    rw [h1, h2]
    exact ⟨hEsym _ _ _ he, hy, hx, z, hz, by omega⟩

lemma cl_structure {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hEsym : ∀ u v s, E u v s → E v u s) {W : ℕ}
    {u v : Fin n} {s : Bool} (hcl : Cl w E W u v s) :
    (u = v ∧ s = false) ∨
    Direct w E W u v s ∨
    ∃ U : Finset (Fin n), u ∈ U ∧ v ∈ U ∧
      (∃ z ∈ U, w z + w u + w v ≤ W + 1) ∧
      (∀ x ∈ U, ∃ t : Bool, GWalk w E W U u x t) ∧
      GWalk w E W U u v s := by
  let P : Fin n → Fin n → Bool → Prop := fun a b t =>
    (a = b ∧ t = false) ∨
    Direct w E W a b t ∨
    ∃ U : Finset (Fin n), a ∈ U ∧ b ∈ U ∧
      (∃ z ∈ U, w z + w a + w b ≤ W + 1) ∧
      (∀ x ∈ U, ∃ p : Bool, GWalk w E W U a x p) ∧
      GWalk w E W U a b t
  apply hcl P
  · intro x; exact Or.inl ⟨rfl, rfl⟩
  · intro x y t hdir; exact Or.inr (Or.inl hdir)
  · intro x y t hP
    rcases hP with ⟨rfl, rfl⟩ | ⟨he, hcard⟩ | ⟨U, hxU, hyU, ⟨z, hzU, hwz⟩, hconn, hwalk⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · right; left
      refine ⟨hEsym _ _ _ he, ?_⟩
      by_cases hxy : x = y
      · subst hxy; simpa using hcard
      · have hyx : y ≠ x := Ne.symm hxy
        simp only [hxy, hyx, ↓reduceIte] at hcard ⊢; omega
    · right; right
      refine ⟨U, hyU, hxU, ⟨z, hzU, by omega⟩, ?_, gwalk_rev hEsym hwalk⟩
      intro c hcU
      rcases hconn c hcU with ⟨p, hp⟩
      exact ⟨xor t p, gwalk_append (gwalk_rev hEsym hwalk) hp⟩
  · intro x m y t₁ t₂ h1 h2 htrip
    rcases h1 with ⟨rfl, rfl⟩ | h1rest
    · simpa using h2
    · rcases h2 with ⟨rfl, rfl⟩ | h2rest
      · rw [Bool.xor_false]; exact Or.inr h1rest
      · right; right
        have hpart1 : ∃ U₁ : Finset (Fin n), x ∈ U₁ ∧ m ∈ U₁ ∧
            (∀ c ∈ U₁, c = y ∨ ∃ p, GWalk w E W U₁ x c p) ∧
            GWalk w E W U₁ x m t₁ := by
          rcases h1rest with ⟨he1, _⟩ | ⟨U₁, hxU1, hmU1, _, hconn1, hw1⟩
          · let U₁ : Finset (Fin n) := {x, m, y}
            have hge : GoodEdge w E W U₁ x m t₁ :=
              ⟨he1, by simp [U₁], by simp [U₁], y, by simp [U₁], by omega⟩
            refine ⟨U₁, by simp [U₁], by simp [U₁], ?_, gwalk_single hge⟩
            intro c hc
            simp only [U₁, Finset.mem_insert, Finset.mem_singleton] at hc
            rcases hc with hcx | hcm | hcy
            · rw [hcx]; exact Or.inr ⟨false, gwalk_refl x⟩
            · rw [hcm]; exact Or.inr ⟨t₁, gwalk_single hge⟩
            · exact Or.inl hcy
          · exact ⟨U₁, hxU1, hmU1, fun c hc => Or.inr (hconn1 c hc), hw1⟩
        have hpart2 : ∃ U₂ : Finset (Fin n), m ∈ U₂ ∧ y ∈ U₂ ∧
            (∀ c ∈ U₂, c = x ∨ ∃ p, GWalk w E W U₂ m c p) ∧
            GWalk w E W U₂ m y t₂ := by
          rcases h2rest with ⟨he2, _⟩ | ⟨U₂, hmU2, hyU2, _, hconn2, hw2⟩
          · let U₂ : Finset (Fin n) := {x, m, y}
            have hge : GoodEdge w E W U₂ m y t₂ :=
              ⟨he2, by simp [U₂], by simp [U₂], x, by simp [U₂], by omega⟩
            refine ⟨U₂, by simp [U₂], by simp [U₂], ?_, gwalk_single hge⟩
            intro c hc
            simp only [U₂, Finset.mem_insert, Finset.mem_singleton] at hc
            rcases hc with hcx | hcm | hcy
            · exact Or.inl hcx
            · rw [hcm]; exact Or.inr ⟨false, gwalk_refl m⟩
            · rw [hcy]; exact Or.inr ⟨t₂, gwalk_single hge⟩
          · exact ⟨U₂, hmU2, hyU2, fun c hc => Or.inr (hconn2 c hc), hw2⟩
        rcases hpart1 with ⟨U₁, hx1, hm1, hc1, hw1⟩
        rcases hpart2 with ⟨U₂, hm2, hy2, hc2, hw2⟩
        let U := U₁ ∪ U₂
        have hw1' := gwalk_mono (Finset.subset_union_left (s₂ := U₂)) hw1
        have hw2' := gwalk_mono (Finset.subset_union_right (s₁ := U₁)) hw2
        refine ⟨U, Finset.mem_union_left _ hx1, Finset.mem_union_right _ hy2,
          ⟨m, Finset.mem_union_left _ hm1, by omega⟩, ?_, gwalk_append hw1' hw2'⟩
        intro c hcU
        rcases Finset.mem_union.mp hcU with hcU1 | hcU2
        · rcases hc1 c hcU1 with hcy | ⟨p, hp⟩
          · rw [hcy]; exact ⟨xor t₁ t₂, gwalk_append hw1' hw2'⟩
          · exact ⟨p, gwalk_mono (Finset.subset_union_left (s₂ := U₂)) hp⟩
        · rcases hc2 c hcU2 with hcx | ⟨p, hp⟩
          · rw [hcx]; exact ⟨false, gwalk_refl x⟩
          · exact ⟨xor t₁ p, gwalk_append hw1' (gwalk_mono (Finset.subset_union_right (s₁ := U₁)) hp)⟩

lemma closed_gwalk_to_rhs {n : ℕ} {w : Fin n → ℕ} {E : Fin n → Fin n → Bool → Prop}
    (hEsym : ∀ u v s, E u v s → E v u s) {W : ℕ}
    (U : Finset (Fin n)) (i : Fin n) (hiU : i ∈ U)
    (hconn : ∀ x ∈ U, ∃ t : Bool, GWalk w E W U i x t)
    (hloop : GWalk w E W U i i true) :
    ∃ (root : Fin n) (len : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool),
      v 0 = root ∧ v len = root ∧ Odd (((Finset.range len).filter (fun j => s j)).card) ∧
      ∀ j < len, E (v j) (v (j + 1)) (s j) ∧ w root + w (v j) + w (v (j + 1)) ≤ W + 1 := by
  rcases Finset.exists_min_image U w ⟨i, hiU⟩ with ⟨root, hrootU, hmin⟩
  rcases hconn root hrootU with ⟨t, hpath⟩
  have hback : GWalk w E W U root i t := gwalk_rev hEsym hpath
  have hfull : GWalk w E W U root root (xor (xor t true) t) :=
    gwalk_append (gwalk_append hback hloop) hpath
  have hpar : xor (xor t true) t = true := by cases t <;> rfl
  rw [hpar] at hfull
  rcases hfull with ⟨len, v, s, h0, hl, hp, hedge⟩
  refine ⟨root, len, v, s, h0, hl, of_decide_eq_true hp, fun j hj => ?_⟩
  rcases hedge j hj with ⟨he, _, _, z, hzU, hwz⟩
  have hle : w root ≤ w z := hmin z hzU
  exact ⟨he, by omega⟩

theorem main296 : (∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let small := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (W : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
      shape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, (line p).card ≤ W) ∧
      (∀ p ∈ N \ J, liftAx F (line p)) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
        (line (p ++ [false])) (line (p ++ [true])) (line p)
  ∀ (E : Fin n → Fin n → Bool → Prop), (∀ u v s, E u v s → E v u s) →
    let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C |
      ∃ u v s a, E u v s ∧ C = {(u,!a),(v,a ^^ s)}}
    ∀ W : ℕ, Iff (small F W)
      ((∃ i, E i i true ∧ w i ≤ W) ∨
       (∃ i j, i ≠ j ∧ E i j false ∧ E i j true ∧ w i+w j ≤ W) ∨
       ∃ (root : Fin n) (len : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool),
         v 0 = root ∧ v len = root ∧ Odd (((Finset.range len).filter (fun j => s j)).card) ∧
         ∀ j < len, E (v j) (v (j+1)) (s j) ∧
           w root + w (v j) + w (v (j+1)) ≤ W+1)) := by
  intro n hn w hw Raw parity liftAx shape small E hEsym F W
  constructor
  · intro hsmall
    have hcontra := PEqualNP.Outside.L_pcx_294_aux.small_implies_cl_contra hw (E := E) hsmall
    rcases hcontra with ⟨i, hloop⟩ | ⟨i, j, hij, hf, ht⟩
    · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym hloop with
        ⟨_, hfalse⟩ | ⟨he, hcard⟩ | ⟨U, hiU, _, _, hconn, hgwalk⟩
      · exact absurd hfalse (by decide)
      · exact Or.inl ⟨i, he, by simpa using hcard⟩
      · exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U i hiU hconn hgwalk))
    · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym hf with
        ⟨heq, _⟩ | ⟨hef, hcf⟩ | ⟨U₁, hi1, hj1, ⟨z1, hz1, hw1⟩, hconn1, hgw1⟩
      · exact absurd heq hij
      · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym ht with
          ⟨heq, _⟩ | ⟨het, _⟩ | ⟨U₂, hi2, hj2, ⟨z2, hz2, hw2⟩, hconn2, hgw2⟩
        · exact absurd heq hij
        · exact Or.inr (Or.inl ⟨i, j, hij, hef, het, by simpa [hij] using hcf⟩)
        · have hge : PEqualNP.Outside.L_pcx_294_aux.GoodEdge w E W U₂ j i false :=
            ⟨hEsym _ _ _ hef, hj2, hi2, z2, hz2, by omega⟩
          have hloop := PEqualNP.Outside.L_pcx_294_aux.gwalk_append hgw2
            (PEqualNP.Outside.L_pcx_294_aux.gwalk_single hge)
          exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U₂ i hi2 hconn2
            (by simpa using hloop)))
      · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym ht with
          ⟨heq, _⟩ | ⟨het, _⟩ | ⟨U₂, hi2, hj2, _, hconn2, hgw2⟩
        · exact absurd heq hij
        · have hge : PEqualNP.Outside.L_pcx_294_aux.GoodEdge w E W U₁ j i true :=
            ⟨hEsym _ _ _ het, hj1, hi1, z1, hz1, by omega⟩
          have hloop := PEqualNP.Outside.L_pcx_294_aux.gwalk_append hgw1
            (PEqualNP.Outside.L_pcx_294_aux.gwalk_single hge)
          exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U₁ i hi1 hconn1
            (by simpa using hloop)))
        · let U := U₁ ∪ U₂
          have hgw1' := PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_left (s₂ := U₂)) hgw1
          have hgw2' := PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_right (s₁ := U₁)) hgw2
          have hloop := PEqualNP.Outside.L_pcx_294_aux.gwalk_append hgw1'
            (PEqualNP.Outside.L_pcx_294_aux.gwalk_rev hEsym hgw2')
          have hconn : ∀ x ∈ U, ∃ t, PEqualNP.Outside.L_pcx_294_aux.GWalk w E W U i x t := by
            intro x hx
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · rcases hconn1 x hx1 with ⟨t, ht'⟩
              exact ⟨t, PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_left (s₂ := U₂)) ht'⟩
            · rcases hconn2 x hx2 with ⟨t, ht'⟩
              exact ⟨t, PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_right (s₁ := U₁)) ht'⟩
          exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U i
            (Finset.mem_union_left _ hi1) hconn (by simpa using hloop)))
  · change _ → PEqualNP.Outside.L_pcx_294_aux.Derivable (w := w) (PEqualNP.Outside.L_pcx_294_aux.eqFormula E) W ∅
    rintro (⟨i, he, hwi⟩ | ⟨i, j, hij, hef, het, hwij⟩ | ⟨root, len, v, s, hv0, hvlen, hodd, hwalk⟩)
    · have hed := PEqualNP.Outside.L_pcx_294_aux.eqDer_of_edge (w := w) (W := W) he (by simpa using hwi)
      apply PEqualNP.Outside.L_pcx_294_aux.derivable_empty_of_all_raw
        (PEqualNP.Outside.L_pcx_294_aux.blockRaw w {i})
        (by rw [PEqualNP.Outside.L_pcx_294_aux.blockRaw_single_card]; exact hwi)
      intro y
      simpa [PEqualNP.Outside.L_pcx_294_aux.blockClause] using hed y (by simp)
    · have hedF := PEqualNP.Outside.L_pcx_294_aux.eqDer_of_edge (w := w) (W := W) hef (by simpa [hij] using hwij)
      have hedT := PEqualNP.Outside.L_pcx_294_aux.eqDer_of_edge (w := w) (W := W) het (by simpa [hij] using hwij)
      apply PEqualNP.Outside.L_pcx_294_aux.derivable_empty_of_all_raw
        (PEqualNP.Outside.L_pcx_294_aux.blockRaw w {i, j})
        (by rw [PEqualNP.Outside.L_pcx_294_aux.blockRaw_pair_card w hij]; exact hwij)
      intro y
      by_cases hp : xor (PEqualNP.Outside.L_pcx_294_aux.parity y i) (PEqualNP.Outside.L_pcx_294_aux.parity y j) = false
      · exact hedT y (by rw [hp]; decide)
      · exact hedF y hp
    · exact PEqualNP.Outside.L_pcx_294_aux.walk_complete hw root len v s hv0 hvlen hodd hwalk


end PEqualNP.Outside.L_pcx_294_aux

theorem PEqualNP.Outside.L_pcx_294 : (∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let small := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (W : ℕ) =>
    ∃ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
      shape N J ∧ line [] = ∅ ∧ (∀ p ∈ N, (line p).card ≤ W) ∧
      (∀ p ∈ N \ J, liftAx F (line p)) ∧
      ∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
        (line (p ++ [false])) (line (p ++ [true])) (line p)
  ∀ (E : Fin n → Fin n → Bool → Prop), (∀ u v s, E u v s → E v u s) →
    let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := {C |
      ∃ u v s a, E u v s ∧ C = {(u,!a),(v,a ^^ s)}}
    ∀ W : ℕ,
      Iff (¬ small F W)
        (∃ R : Fin n → Fin n → Bool → Prop,
          (∀ i j s, E i j s → (if i = j then w i else w i + w j) ≤ W → R i j s) ∧
          (∀ i j s, R i j s → R j i s) ∧ (∀ i, ¬ R i i true) ∧
          (∀ i j s t, R i j s → R i j t → s = t) ∧
          ∀ i j k s t, i ≠ j → j ≠ k → i ≠ k → w i + w j + w k ≤ W+1 →
            R i j s → R j k t → R i k (s ^^ t))) := by
  intro n hn w hw Raw parity liftAx shape small E hEsym F W
  have h296 : small F W ↔
      ((∃ i, E i i true ∧ w i ≤ W) ∨
       (∃ i j, i ≠ j ∧ E i j false ∧ E i j true ∧ w i+w j ≤ W) ∨
       ∃ (root : Fin n) (len : ℕ) (v : ℕ → Fin n) (s : ℕ → Bool),
         v 0 = root ∧ v len = root ∧ Odd (((Finset.range len).filter (fun j => s j)).card) ∧
         ∀ j < len, E (v j) (v (j+1)) (s j) ∧
           w root + w (v j) + w (v (j+1)) ≤ W+1) :=
    PEqualNP.Outside.L_pcx_294_aux.main296 n hn w hw E hEsym W
  have hkey : ((∃ i, PEqualNP.Outside.L_pcx_294_aux.Cl w E W i i true) ∨
      (∃ i j, i ≠ j ∧ PEqualNP.Outside.L_pcx_294_aux.Cl w E W i j false ∧
        PEqualNP.Outside.L_pcx_294_aux.Cl w E W i j true)) → small F W := by
    intro hcontra
    refine h296.mpr ?_
    rcases hcontra with ⟨i, hloop⟩ | ⟨i, j, hij, hf, ht⟩
    · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym hloop with
        ⟨_, hfalse⟩ | ⟨he, hcard⟩ | ⟨U, hiU, _, _, hconn, hgwalk⟩
      · exact absurd hfalse (by decide)
      · exact Or.inl ⟨i, he, by simpa using hcard⟩
      · exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U i hiU hconn hgwalk))
    · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym hf with
        ⟨heq, _⟩ | ⟨hef, hcf⟩ | ⟨U₁, hi1, hj1, ⟨z1, hz1, hw1⟩, hconn1, hgw1⟩
      · exact absurd heq hij
      · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym ht with
          ⟨heq, _⟩ | ⟨het, _⟩ | ⟨U₂, hi2, hj2, ⟨z2, hz2, hw2⟩, hconn2, hgw2⟩
        · exact absurd heq hij
        · exact Or.inr (Or.inl ⟨i, j, hij, hef, het, by simpa [hij] using hcf⟩)
        · have hge : PEqualNP.Outside.L_pcx_294_aux.GoodEdge w E W U₂ j i false :=
            ⟨hEsym _ _ _ hef, hj2, hi2, z2, hz2, by omega⟩
          have hloop := PEqualNP.Outside.L_pcx_294_aux.gwalk_append hgw2
            (PEqualNP.Outside.L_pcx_294_aux.gwalk_single hge)
          exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U₂ i hi2 hconn2
            (by simpa using hloop)))
      · rcases PEqualNP.Outside.L_pcx_294_aux.cl_structure hEsym ht with
          ⟨heq, _⟩ | ⟨het, _⟩ | ⟨U₂, hi2, hj2, _, hconn2, hgw2⟩
        · exact absurd heq hij
        · have hge : PEqualNP.Outside.L_pcx_294_aux.GoodEdge w E W U₁ j i true :=
            ⟨hEsym _ _ _ het, hj1, hi1, z1, hz1, by omega⟩
          have hloop := PEqualNP.Outside.L_pcx_294_aux.gwalk_append hgw1
            (PEqualNP.Outside.L_pcx_294_aux.gwalk_single hge)
          exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U₁ i hi1 hconn1
            (by simpa using hloop)))
        · let U := U₁ ∪ U₂
          have hgw1' := PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_left (s₂ := U₂)) hgw1
          have hgw2' := PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_right (s₁ := U₁)) hgw2
          have hloop := PEqualNP.Outside.L_pcx_294_aux.gwalk_append hgw1'
            (PEqualNP.Outside.L_pcx_294_aux.gwalk_rev hEsym hgw2')
          have hconn : ∀ x ∈ U, ∃ t, PEqualNP.Outside.L_pcx_294_aux.GWalk w E W U i x t := by
            intro x hx
            rcases Finset.mem_union.mp hx with hx1 | hx2
            · rcases hconn1 x hx1 with ⟨t, ht'⟩
              exact ⟨t, PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_left (s₂ := U₂)) ht'⟩
            · rcases hconn2 x hx2 with ⟨t, ht'⟩
              exact ⟨t, PEqualNP.Outside.L_pcx_294_aux.gwalk_mono (Finset.subset_union_right (s₁ := U₁)) ht'⟩
          exact Or.inr (Or.inr (PEqualNP.Outside.L_pcx_294_aux.closed_gwalk_to_rhs hEsym U i
            (Finset.mem_union_left _ hi1) hconn (by simpa using hloop)))
  constructor
  · intro hns
    refine ⟨PEqualNP.Outside.L_pcx_294_aux.Cl w E W, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j s he hc
      refine PEqualNP.Outside.L_pcx_294_aux.cl_edge ⟨he, ?_⟩
      by_cases hij : i = j
      · simpa [hij] using hc
      · simpa [hij] using hc
    · intro i j s h
      exact PEqualNP.Outside.L_pcx_294_aux.cl_symm h
    · intro i h
      exact hns (hkey (Or.inl ⟨i, h⟩))
    · intro i j s t hs ht
      by_contra hne
      apply hns
      apply hkey
      by_cases hij : i = j
      · subst hij
        left
        refine ⟨i, ?_⟩
        cases s <;> cases t <;> simp_all
      · right
        refine ⟨i, j, hij, ?_, ?_⟩ <;> cases s <;> cases t <;> simp_all
    · intro i j k s t _ _ _ hw3 h1 h2
      exact PEqualNP.Outside.L_pcx_294_aux.cl_trans h1 h2 hw3
  · rintro ⟨R, hR1, hR2, hR3, hR4, hR5⟩ hsmall
    have hcl : ∀ u v s, PEqualNP.Outside.L_pcx_294_aux.Cl w E W u v s →
        ((u = v ∧ s = false) ∨ R u v s) := by
      intro u v s h
      refine h (fun x y t => (x = y ∧ t = false) ∨ R x y t) ?_ ?_ ?_ ?_
      · intro x
        exact Or.inl ⟨rfl, rfl⟩
      · intro x y t hd
        right
        refine hR1 x y t hd.1 ?_
        have hd2 := hd.2
        by_cases hxy : x = y
        · simpa [hxy] using hd2
        · simpa [hxy] using hd2
      · rintro x y t (⟨rfl, rfl⟩ | h)
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr (hR2 _ _ _ h)
      · intro x m y t₁ t₂ h1 h2 hw3
        rcases h1 with ⟨rfl, rfl⟩ | h1
        · simpa using h2
        rcases h2 with ⟨rfl, rfl⟩ | h2
        · simpa using (Or.inr h1 : (x = m ∧ t₁ = false) ∨ R x m t₁)
        by_cases hxm : x = m
        · subst hxm
          have ht1 : t₁ = false := by
            cases t₁ with
            | false => rfl
            | true => exact absurd h1 (hR3 x)
          subst ht1
          simpa using (Or.inr h2 : (x = y ∧ t₂ = false) ∨ R x y t₂)
        by_cases hmy : m = y
        · subst hmy
          have ht2 : t₂ = false := by
            cases t₂ with
            | false => rfl
            | true => exact absurd h2 (hR3 m)
          subst ht2
          simpa using (Or.inr h1 : (x = m ∧ t₁ = false) ∨ R x m t₁)
        by_cases hxy : x = y
        · subst hxy
          have ht12 := hR4 x m t₁ t₂ h1 (hR2 _ _ _ h2)
          subst ht12
          exact Or.inl ⟨rfl, by simp⟩
        · exact Or.inr (hR5 x m y t₁ t₂ hxm hmy hxy hw3 h1 h2)
    rcases PEqualNP.Outside.L_pcx_294_aux.small_implies_cl_contra hw (E := E) hsmall with
      ⟨i, h⟩ | ⟨i, j, hij, hf, ht⟩
    · rcases hcl _ _ _ h with ⟨_, h'⟩ | h'
      · exact absurd h' (by decide)
      · exact hR3 i h'
    · rcases hcl _ _ _ hf with ⟨h', _⟩ | h1
      · exact hij h'
      rcases hcl _ _ _ ht with ⟨h', _⟩ | h2
      · exact hij h'
      exact absurd (hR4 i j false true h1 h2) (by decide)
