import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1202_aux

open scoped Classical

section Graph

variable {m : ℕ}

structure ValidNb (m : ℕ) (nb : (Fin m × Bool) → Finset (Fin m × Bool)) : Prop where
  no_loop : ∀ p, p ∉ nb p
  card_le : ∀ p, (nb p).card ≤ 2
  symm : ∀ p q, q ∈ nb p ↔ p ∈ nb q
  mark : ∀ i, (i, true) ∈ nb (i, false)

lemma ValidNb.mark_symm {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (i : Fin m) (b : Bool) : (i, !b) ∈ nb (i, b) := by
  cases b
  · exact h.mark i
  · exact (h.symm (i, false) (i, true)).mp (h.mark i)

lemma ValidNb.ext_unique {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) {p q₁ q₂ : Fin m × Bool}
    (h1 : q₁ ∈ nb p) (h2 : q₂ ∈ nb p) (hn1 : q₁.1 ≠ p.1) (hn2 : q₂.1 ≠ p.1) :
    q₁ = q₂ := by
  have hm : (p.1, !p.2) ∈ nb p := h.mark_symm p.1 p.2
  have he : ((nb p).erase (p.1, !p.2)).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hm]
    have hc := h.card_le p
    omega
  have h1' : q₁ ∈ (nb p).erase (p.1, !p.2) :=
    Finset.mem_erase.mpr ⟨fun heq => hn1 (by have := congrArg Prod.fst heq; exact this), h1⟩
  have h2' : q₂ ∈ (nb p).erase (p.1, !p.2) :=
    Finset.mem_erase.mpr ⟨fun heq => hn2 (by have := congrArg Prod.fst heq; exact this), h2⟩
  exact Finset.card_le_one.mp he _ h1' _ h2'

noncomputable def eMult (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (i j : Fin m) : ℕ :=
  if i = j then 0
  else ((Finset.univ : Finset (Bool × Bool)).filter (fun p => (j, p.2) ∈ nb (i, p.1))).card

lemma eMult_self (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (i : Fin m) :
    eMult nb i i = 0 := by
  simp [eMult]

lemma eMult_symm {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (i j : Fin m) : eMult nb i j = eMult nb j i := by
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : j ≠ i := Ne.symm hij
    simp only [eMult, hij, hji, ↓reduceIte]
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      exact (h.symm (i, p.1) (j, p.2)).mp hp
    · intro p₁ _ p₂ _ heq
      cases p₁; cases p₂
      simp only [Prod.mk.injEq] at heq
      exact Prod.ext heq.2 heq.1
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      refine ⟨(q.2, q.1), ?_, Prod.ext rfl rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (h.symm (j, q.1) (i, q.2)).mp hq

lemma eMult_pos_iff {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (i j : Fin m) :
    0 < eMult nb i j ↔ i ≠ j ∧ ∃ b₁ b₂ : Bool, (j, b₂) ∈ nb (i, b₁) := by
  by_cases hij : i = j
  · subst hij; simp [eMult]
  · simp only [eMult, hij, ↓reduceIte, ne_eq, not_false_eq_true, true_and, Finset.card_pos]
    constructor
    · rintro ⟨⟨b₁, b₂⟩, hp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact ⟨b₁, b₂, hp⟩
    · rintro ⟨b₁, b₂, hp⟩
      exact ⟨(b₁, b₂), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩

def tipHas (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (S : Finset (Fin m)) (i : Fin m) (b : Bool) : Prop :=
  ∃ j ∈ S, j ≠ i ∧ ∃ b' : Bool, (j, b') ∈ nb (i, b)

lemma eMult_eq_tip_sum {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (i j : Fin m) :
    eMult nb i j =
      (if j ≠ i ∧ ∃ b', (j, b') ∈ nb (i, false) then 1 else 0) +
      (if j ≠ i ∧ ∃ b', (j, b') ∈ nb (i, true) then 1 else 0) := by
  by_cases hij : i = j
  · subst hij; simp [eMult]
  · have hji : j ≠ i := Ne.symm hij
    simp only [eMult, hij, hji, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    have huniv : (Finset.univ : Finset (Bool × Bool)) =
        (Finset.univ.image (fun b₂ : Bool => (false, b₂))) ∪
        (Finset.univ.image (fun b₂ : Bool => (true, b₂))) := by
      ext ⟨b₁, b₂⟩
      cases b₁ <;> simp
    have hdisj : Disjoint
        ((Finset.univ.image (fun b₂ : Bool => (false, b₂))).filter (fun p => (j, p.2) ∈ nb (i, p.1)))
        ((Finset.univ.image (fun b₂ : Bool => (true, b₂))).filter (fun p => (j, p.2) ∈ nb (i, p.1))) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp1 hp2
      rcases hp1.1 with ⟨_, rfl⟩
      rcases hp2.1 with ⟨_, hEq⟩
      exact Bool.false_ne_true (congrArg Prod.fst hEq).symm
    rw [huniv, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
    have hhalf : ∀ b₁ : Bool,
        ((Finset.univ.image (fun b₂ : Bool => (b₁, b₂))).filter (fun p => (j, p.2) ∈ nb (i, p.1))).card =
          if ∃ b₂, (j, b₂) ∈ nb (i, b₁) then 1 else 0 := by
      intro b₁
      set T := (Finset.univ.image (fun b₂ : Bool => (b₁, b₂))).filter (fun p => (j, p.2) ∈ nb (i, p.1))
      have hle : T.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro p₁ hp₁ p₂ hp₂
        simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp₁ hp₂
        rcases hp₁.1 with ⟨b₂, rfl⟩
        rcases hp₂.1 with ⟨b₂', rfl⟩
        have heq := h.ext_unique hp₁.2 hp₂.2 hji hji
        have hsnd : b₂ = b₂' := congrArg Prod.snd heq
        exact Prod.ext rfl hsnd
      split_ifs with hex
      · rcases hex with ⟨b₂, hb₂⟩
        have hmem : (b₁, b₂) ∈ T := by
          simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨⟨b₂, rfl⟩, hb₂⟩
        have hpos : 0 < T.card := Finset.card_pos.mpr ⟨(b₁, b₂), hmem⟩
        omega
      · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro p hp
        simp only [T, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hp
        rcases hp.1 with ⟨b₂, rfl⟩
        exact hex ⟨b₂, hp.2⟩
    rw [hhalf false, hhalf true]

lemma eDeg_eq_tip_count {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (S : Finset (Fin m)) (i : Fin m) :
    ∑ j ∈ S, eMult nb i j =
      (if tipHas nb S i false then 1 else 0) +
      (if tipHas nb S i true then 1 else 0) := by
  have hsum : ∑ j ∈ S, eMult nb i j =
      (∑ j ∈ S, if j ≠ i ∧ ∃ b', (j, b') ∈ nb (i, false) then 1 else 0) +
      (∑ j ∈ S, if j ≠ i ∧ ∃ b', (j, b') ∈ nb (i, true) then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => eMult_eq_tip_sum h i j
  rw [hsum]
  have hpart : ∀ b : Bool,
      (∑ j ∈ S, if j ≠ i ∧ ∃ b', (j, b') ∈ nb (i, b) then 1 else 0) =
        if tipHas nb S i b then 1 else 0 := by
    intro b
    rw [Finset.sum_boole, Nat.cast_id]
    set T := S.filter (fun j => j ≠ i ∧ ∃ b', (j, b') ∈ nb (i, b))
    have hle : T.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j₁ hj₁ j₂ hj₂
      simp only [T, Finset.mem_filter] at hj₁ hj₂
      rcases hj₁.2.2 with ⟨b₁, hb₁⟩
      rcases hj₂.2.2 with ⟨b₂, hb₂⟩
      exact congrArg Prod.fst (h.ext_unique hb₁ hb₂ hj₁.2.1 hj₂.2.1)
    split_ifs with htip
    · rcases htip with ⟨j, hjS, hji, b', hb'⟩
      have hmem : j ∈ T := Finset.mem_filter.mpr ⟨hjS, hji, b', hb'⟩
      have hpos : 0 < T.card := Finset.card_pos.mpr ⟨j, hmem⟩
      omega
    · rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro j hj
      simp only [T, Finset.mem_filter] at hj
      exact htip ⟨j, hj.1, hj.2.1, hj.2.2⟩
  rw [hpart false, hpart true]

lemma eDeg_le_two {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (S : Finset (Fin m)) (i : Fin m) :
    ∑ j ∈ S, eMult nb i j ≤ 2 := by
  rw [eDeg_eq_tip_count h S i]
  split_ifs <;> omega

lemma eMult_le_two {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (i j : Fin m) : eMult nb i j ≤ 2 := by
  have := eDeg_le_two h {j} i
  simpa using this

lemma handshaking {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (D : Finset (Fin m)) :
    Even (∑ i ∈ D, ∑ j ∈ D, eMult nb i j) := by
  induction D using Finset.induction_on with
  | empty => simp
  | @insert a D ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ∑ j ∈ insert a D, eMult nb a j = ∑ j ∈ D, eMult nb a j := by
      rw [Finset.sum_insert ha, eMult_self, zero_add]
    have h2 : ∑ i ∈ D, ∑ j ∈ insert a D, eMult nb i j =
        (∑ i ∈ D, eMult nb a i) + ∑ i ∈ D, ∑ j ∈ D, eMult nb i j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_insert ha, eMult_symm h i a]
    rw [h1, h2]
    rcases ih with ⟨k, hk⟩
    refine ⟨(∑ j ∈ D, eMult nb a j) + k, ?_⟩
    omega

/-! ### Part 2: Cover-to-coloring bijection -/

def IsCover (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (S : Finset (Fin m))
    (x : (Fin m × Bool) → Bool) : Prop :=
  (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
  ∀ i, xor (x (i, false)) (x (i, true)) = decide (i ∈ S)

def IsCol (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (S : Finset (Fin m))
    (c : Fin m → Bool) : Prop :=
  (∀ i, i ∉ S → c i = false) ∧
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (j, c j) ∉ nb (i, c i)

noncomputable def colCount (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (S : Finset (Fin m)) : ℕ :=
  ((Finset.univ : Finset (Fin m → Bool)).filter (IsCol nb S)).card

noncomputable def colCountAt (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (S : Finset (Fin m)) (u : Fin m) (b : Bool) : ℕ :=
  ((Finset.univ : Finset (Fin m → Bool)).filter (fun c => IsCol nb S c ∧ c u = b)).card

lemma cover_card_eq_colCount {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (S : Finset (Fin m)) :
    ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (IsCover nb S)).card =
      colCount nb S := by
  unfold colCount
  refine Finset.card_bij (fun x _ i => if i ∈ S then x (i, false) else false) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨hcov, hxor⟩
    refine ⟨fun i hi => by simp [hi], ?_⟩
    intro i hi j hj hij hnb
    simp only [hi, hj, ↓reduceIte] at hnb
    have hxi : x (i, x (i, false)) = false := by
      have hxi_xor := hxor i
      simp only [hi, decide_true] at hxi_xor
      cases hf : x (i, false) <;> cases ht : x (i, true) <;> simp_all
    have hxj : x (j, x (j, false)) = false := by
      have hxj_xor := hxor j
      simp only [hj, decide_true] at hxj_xor
      cases hf : x (j, false) <;> cases ht : x (j, true) <;> simp_all
    rcases hcov (i, x (i, false)) (j, x (j, false)) hnb with h1 | h2
    · rw [hxi] at h1; exact Bool.false_ne_true h1
    · rw [hxj] at h2; exact Bool.false_ne_true h2
  · intro x₁ hx₁ x₂ hx₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    funext ⟨i, b⟩
    have hi_eq := congrFun heq i
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte] at hi_eq
      have h1 := hx₁.2 i; have h2 := hx₂.2 i
      simp only [hi, decide_true] at h1 h2
      cases b
      · exact hi_eq
      · rw [← hi_eq] at h2
        cases h1f : x₁ (i, false) <;> cases h1t : x₁ (i, true) <;>
          cases h2t : x₂ (i, true) <;> simp_all
    · have h1 := hx₁.2 i; have h2 := hx₂.2 i
      simp only [hi, decide_false] at h1 h2
      have hm1 := hx₁.1 (i, false) (i, true) (h.mark i)
      have hm2 := hx₂.1 (i, false) (i, true) (h.mark i)
      cases b <;>
        cases h1f : x₁ (i, false) <;> cases h1t : x₁ (i, true) <;>
        cases h2f : x₂ (i, false) <;> cases h2t : x₂ (i, true) <;> simp_all
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    let x : (Fin m × Bool) → Bool := fun p => if p.1 ∈ S then (p.2 != c p.1) else true
    refine ⟨x, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro p q hqp
        by_cases hp : p.1 ∈ S
        · by_cases hq : q.1 ∈ S
          · by_cases hpq : p.1 = q.1
            · have hne : p.2 ≠ q.2 := by
                intro hb
                have : p = q := Prod.ext hpq hb
                subst this
                exact h.no_loop p hqp
              dsimp only [x]
              simp only [hp, hq, ↓reduceIte]
              rw [hpq]
              cases hp2 : p.2 <;> cases hq2 : q.2 <;> cases hc' : c q.1 <;> simp_all
            · dsimp only [x]
              simp only [hp, hq, ↓reduceIte]
              cases hp2 : p.2 <;> cases hcp : c p.1 <;> cases hq2 : q.2 <;> cases hcq : c q.1 <;> simp
              all_goals
                have hforb := hc.2 p.1 hp q.1 hq hpq
                rw [hcp, hcq] at hforb
                have hp_eq : p = (p.1, p.2) := rfl
                have hq_eq : q = (q.1, q.2) := rfl
                rw [hp_eq, hp2, hq_eq, hq2] at hqp
                exact absurd hqp hforb
          · right; simp [x, hq]
        · left; simp [x, hp]
      · intro i
        dsimp only [x]
        by_cases hi : i ∈ S
        · simp only [hi, ↓reduceIte, decide_true]
          cases c i <;> rfl
        · simp [hi]
    · funext i
      dsimp only [x]
      by_cases hi : i ∈ S
      · simp only [hi, ↓reduceIte]
        cases c i <;> rfl
      · simp [hi, hc.1 i hi]

lemma colCount_pair {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) {i j : Fin m} (hij : i ≠ j)
    {S : Finset (Fin m)} (hS : ∀ k, k ∈ S ↔ k = i ∨ k = j) :
    colCount nb S = 4 - eMult nb i j := by
  have hiS : i ∈ S := (hS i).mpr (Or.inl rfl)
  have hjS : j ∈ S := (hS j).mpr (Or.inr rfl)
  have hcard_total :
      ((Finset.univ : Finset (Bool × Bool)).filter (fun p => (j, p.2) ∈ nb (i, p.1))).card +
      ((Finset.univ : Finset (Bool × Bool)).filter (fun p => (j, p.2) ∉ nb (i, p.1))).card = 4 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Bool × Bool)))
      (p := fun p => (j, p.2) ∈ nb (i, p.1))
    simpa using this
  have hbij : colCount nb S =
      ((Finset.univ : Finset (Bool × Bool)).filter (fun p => (j, p.2) ∉ nb (i, p.1))).card := by
    unfold colCount
    refine Finset.card_bij (fun c _ => (c i, c j)) ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact hc.2 i hiS j hjS hij
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
      simp only [Prod.mk.injEq] at heq
      funext k
      by_cases hki : k = i
      · subst hki; exact heq.1
      · by_cases hkj : k = j
        · subst hkj; exact heq.2
        · have hk : k ∉ S := fun hm => by rcases (hS k).mp hm with rfl | rfl <;> contradiction
          rw [hc₁.1 k hk, hc₂.1 k hk]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨fun k => if k = i then p.1 else if k = j then p.2 else false, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro k hk
          have hne : k ≠ i ∧ k ≠ j := ⟨fun he => hk ((hS k).mpr (Or.inl he)),
            fun he => hk ((hS k).mpr (Or.inr he))⟩
          simp [hne.1, hne.2]
        · intro a ha b hb hab
          rcases (hS a).mp ha with rfl | rfl <;> rcases (hS b).mp hb with rfl | rfl
          · exact absurd rfl hab
          · simp only [↓reduceIte, Ne.symm hij]; exact hp
          · simp only [↓reduceIte, Ne.symm hij]
            intro hmem
            exact hp ((h.symm _ _).mp hmem)
          · exact absurd rfl hab
      · simp [hij.symm]
  rw [hbij]
  simp only [eMult, hij, ↓reduceIte]
  omega

lemma colCount_split (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (S : Finset (Fin m)) (u : Fin m) (b : Bool) :
    colCount nb S = colCountAt nb S u b + colCountAt nb S u (!b) := by
  unfold colCount colCountAt
  have h1 : (Finset.univ.filter (fun c => IsCol nb S c ∧ c u = b)) =
      (Finset.univ.filter (IsCol nb S)).filter (fun c => c u = b) := by
    ext c; simp
  have h2 : (Finset.univ.filter (fun c => IsCol nb S c ∧ c u = !b)) =
      (Finset.univ.filter (IsCol nb S)).filter (fun c => ¬ (c u = b)) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases c u <;> cases b <;> simp
  rw [h1, h2, Finset.card_filter_add_card_filter_not]

lemma colCount_empty (nb : (Fin m × Bool) → Finset (Fin m × Bool)) :
    colCount nb ∅ = 1 := by
  unfold colCount
  have heq : (Finset.univ : Finset (Fin m → Bool)).filter (IsCol nb ∅) = {fun _ => false} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hc; funext i; exact hc.1 i (Finset.notMem_empty i)
    · rintro rfl; exact ⟨fun _ _ => rfl, fun _ h => absurd h (Finset.notMem_empty _)⟩
  rw [heq, Finset.card_singleton]

lemma colCount_union_no_edges {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) {A B : Finset (Fin m)} (hdisj : Disjoint A B)
    (hno : ∀ a ∈ A, ∀ b ∈ B, eMult nb a b = 0) :
    colCount nb (A ∪ B) = colCount nb A * colCount nb B := by
  unfold colCount
  rw [← Finset.card_product]
  refine Finset.card_bij
    (fun c _ => (fun i => if i ∈ A then c i else false, fun i => if i ∈ B then c i else false))
    ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hc ⊢
    constructor
    · refine ⟨fun i hi => by simp [hi], ?_⟩
      intro i hi j hj hij
      simp only [hi, hj, ↓reduceIte]
      exact hc.2 i (Finset.mem_union_left B hi) j (Finset.mem_union_left B hj) hij
    · refine ⟨fun i hi => by simp [hi], ?_⟩
      intro i hi j hj hij
      simp only [hi, hj, ↓reduceIte]
      exact hc.2 i (Finset.mem_union_right A hi) j (Finset.mem_union_right A hj) hij
  · intro c₁ hc₁ c₂ hc₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
    simp only [Prod.mk.injEq] at heq
    funext i
    by_cases hA : i ∈ A
    · have := congrFun heq.1 i; simpa [hA] using this
    · by_cases hB : i ∈ B
      · have := congrFun heq.2 i; simpa [hB] using this
      · have hAB : i ∉ A ∪ B := by simp [hA, hB]
        rw [hc₁.1 i hAB, hc₂.1 i hAB]
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨hp1, hp2⟩
    let c : Fin m → Bool := fun i => if i ∈ A then p.1 i else if i ∈ B then p.2 i else false
    refine ⟨c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp only [Finset.mem_union, not_or] at hi
        simp [c, hi.1, hi.2]
      · intro i hi j hj hij
        simp only [Finset.mem_union] at hi hj
        rcases hi with hiA | hiB <;> rcases hj with hjA | hjB
        · simp only [c, hiA, hjA, ↓reduceIte]
          exact hp1.2 i hiA j hjA hij
        · intro hmem
          have hpos : 0 < eMult nb i j := (eMult_pos_iff i j).mpr ⟨hij, c i, c j, hmem⟩
          have h0 := hno i hiA j hjB
          omega
        · intro hmem
          have hpos : 0 < eMult nb i j := (eMult_pos_iff i j).mpr ⟨hij, c i, c j, hmem⟩
          have h0 : eMult nb i j = 0 := by rw [eMult_symm h i j]; exact hno j hjA i hiB
          omega
        · have hiNA : i ∉ A := Finset.disjoint_right.mp hdisj hiB
          have hjNA : j ∉ A := Finset.disjoint_right.mp hdisj hjB
          simp only [c, hiNA, hjNA, hiB, hjB, ↓reduceIte]
          exact hp2.2 i hiB j hjB hij
    · ext i
      · simp only [c]
        by_cases hA : i ∈ A
        · simp [hA]
        · simp [hA, hp1.1 i hA]
      · simp only [c]
        by_cases hB : i ∈ B
        · have hNA : i ∉ A := Finset.disjoint_right.mp hdisj hB
          simp [hB, hNA]
        · simp [hB, hp2.1 i hB]


/-! ### Part 3: Vertex deletion, paths, cycles, and component product -/

lemma colCountAt_erase_of_nb {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (C : Finset (Fin m))
    {u v : Fin m} (hu : u ∈ C) (hv : v ∈ C) (hvu : v ≠ u) {bu bv : Bool}
    (hnb : (v, bv) ∈ nb (u, bu)) :
    colCountAt nb C u bu = colCountAt nb (C.erase u) v (!bv) := by
  unfold colCountAt
  refine Finset.card_bij (fun c _ i => if i = u then false else c i) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hc with ⟨hcol, hcu⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      by_cases hiu : i = u
      · simp [hiu]
      · have hiC : i ∉ C := fun hmem => hi (Finset.mem_erase.mpr ⟨hiu, hmem⟩)
        simp [hiu, hcol.1 i hiC]
    · intro i hi j hj hij
      rcases Finset.mem_erase.mp hi with ⟨hiu, hiC⟩
      rcases Finset.mem_erase.mp hj with ⟨hju, hjC⟩
      simp only [hiu, hju, ↓reduceIte]
      exact hcol.2 i hiC j hjC hij
    · simp only [hvu, ↓reduceIte]
      have hforb := hcol.2 u hu v hv hvu.symm
      rw [hcu] at hforb
      have hne : c v ≠ bv := fun heq => hforb (heq ▸ hnb)
      cases hcv : c v <;> cases bv <;> simp_all
  · intro c₁ hc₁ c₂ hc₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
    funext i
    by_cases hiu : i = u
    · subst hiu; rw [hc₁.2, hc₂.2]
    · have := congrFun heq i; simpa [hiu] using this
  · intro c' hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    rcases hc' with ⟨hcol', hcv'⟩
    let c : Fin m → Bool := fun i => if i = u then bu else c' i
    refine ⟨c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, by simp [c]⟩
      · intro i hi
        have hiu : i ≠ u := fun heq => hi (heq ▸ hu)
        have hi' : i ∉ C.erase u := fun hmem => hi (Finset.mem_of_mem_erase hmem)
        simp [c, hiu, hcol'.1 i hi']
      · intro i hi j hj hij
        by_cases hiu : i = u
        · subst hiu
          have hju : j ≠ i := Ne.symm hij
          simp only [c, ↓reduceIte, hju]
          intro hmem
          have heq := h.ext_unique hmem hnb hju hvu
          have hjv : j = v := congrArg Prod.fst heq
          have hcb : c' j = bv := congrArg Prod.snd heq
          rw [hjv, hcv'] at hcb
          cases bv <;> simp at hcb
        · by_cases hju : j = u
          · subst hju
            simp only [c, hiu, ↓reduceIte]
            intro hmem
            have hmem' := (h.symm (i, c' i) (j, bu)).mp hmem
            have heq := h.ext_unique hmem' hnb hiu hvu
            have hiv : i = v := congrArg Prod.fst heq
            have hcb : c' i = bv := congrArg Prod.snd heq
            rw [hiv, hcv'] at hcb
            cases bv <;> simp at hcb
          · simp only [c, hiu, hju, ↓reduceIte]
            exact hcol'.2 i (Finset.mem_erase.mpr ⟨hiu, hi⟩)
              j (Finset.mem_erase.mpr ⟨hju, hj⟩) hij
    · funext i
      by_cases hiu : i = u
      · subst hiu
        simp [hcol'.1 i (Finset.notMem_erase i C)]
      · simp [c, hiu]

lemma colCountAt_erase_of_not_tipHas {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (C : Finset (Fin m))
    {u : Fin m} (hu : u ∈ C) {bu : Bool} (hno : ¬ tipHas nb C u bu) :
    colCountAt nb C u bu = colCount nb (C.erase u) := by
  unfold colCountAt colCount
  refine Finset.card_bij (fun c _ i => if i = u then false else c i) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rcases hc with ⟨hcol, _⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      by_cases hiu : i = u
      · simp [hiu]
      · have hiC : i ∉ C := fun hmem => hi (Finset.mem_erase.mpr ⟨hiu, hmem⟩)
        simp [hiu, hcol.1 i hiC]
    · intro i hi j hj hij
      rcases Finset.mem_erase.mp hi with ⟨hiu, hiC⟩
      rcases Finset.mem_erase.mp hj with ⟨hju, hjC⟩
      simp only [hiu, hju, ↓reduceIte]
      exact hcol.2 i hiC j hjC hij
  · intro c₁ hc₁ c₂ hc₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc₁ hc₂
    funext i
    by_cases hiu : i = u
    · subst hiu; rw [hc₁.2, hc₂.2]
    · have := congrFun heq i; simpa [hiu] using this
  · intro c' hc'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    let c : Fin m → Bool := fun i => if i = u then bu else c' i
    refine ⟨c, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, by simp [c]⟩
      · intro i hi
        have hiu : i ≠ u := fun heq => hi (heq ▸ hu)
        have hi' : i ∉ C.erase u := fun hmem => hi (Finset.mem_of_mem_erase hmem)
        simp [c, hiu, hc'.1 i hi']
      · intro i hi j hj hij
        by_cases hiu : i = u
        · subst hiu
          have hju : j ≠ i := Ne.symm hij
          simp only [c, ↓reduceIte, hju]
          intro hmem
          exact hno ⟨j, hj, hju, c' j, hmem⟩
        · by_cases hju : j = u
          · subst hju
            simp only [c, hiu, ↓reduceIte]
            intro hmem
            have hmem' := (h.symm (i, c' i) (j, bu)).mp hmem
            exact hno ⟨i, hi, hiu, c' i, hmem'⟩
          · simp only [c, hiu, hju, ↓reduceIte]
            exact hc'.2 i (Finset.mem_erase.mpr ⟨hiu, hi⟩)
              j (Finset.mem_erase.mpr ⟨hju, hj⟩) hij
    · funext i
      by_cases hiu : i = u
      · subst hiu
        simp [hc'.1 i (Finset.notMem_erase i C)]
      · simp [c, hiu]

def eConn (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (S : Finset (Fin m)) :
    Fin m → Fin m → Prop :=
  Relation.ReflTransGen (fun i j => i ∈ S ∧ j ∈ S ∧ 0 < eMult nb i j)

noncomputable def eComp (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (S : Finset (Fin m)) (i : Fin m) : Finset (Fin m) :=
  S.filter (eConn nb S i)

noncomputable def eRoots (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (S : Finset (Fin m)) : Finset (Fin m) :=
  S.filter (fun i => ∀ j ∈ eComp nb S i, i ≤ j)

def Connected (nb : (Fin m × Bool) → Finset (Fin m × Bool)) (C : Finset (Fin m)) : Prop :=
  C.Nonempty ∧ ∀ u ∈ C, ∀ v ∈ C, eConn nb C u v

lemma eConn_symm {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (S : Finset (Fin m)) {u v : Fin m}
    (huv : eConn nb S u v) : eConn nb S v u := by
  induction huv with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    rcases hab with ⟨ha, hb, hpos⟩
    have hpos' : 0 < eMult nb b a := by rw [eMult_symm h]; exact hpos
    exact Relation.ReflTransGen.head ⟨hb, ha, hpos'⟩ ih

lemma eConn_trans {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (S : Finset (Fin m)) {u v w : Fin m}
    (h1 : eConn nb S u v) (h2 : eConn nb S v w) : eConn nb S u w :=
  Relation.ReflTransGen.trans h1 h2

lemma connected_erase_of_neighbors {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) {C : Finset (Fin m)} (hconn : Connected nb C)
    {u v : Fin m} (hv : v ∈ C.erase u)
    (hnb : ∀ w ∈ C, w ≠ u → 0 < eMult nb u w → eConn nb (C.erase u) v w) :
    Connected nb (C.erase u) := by
  have hvC : v ∈ C := Finset.mem_of_mem_erase hv
  have hreach : ∀ y ∈ C.erase u, eConn nb (C.erase u) v y := by
    intro y hy
    have hyC : y ∈ C := Finset.mem_of_mem_erase hy
    have hvy : eConn nb C v y := hconn.2 v hvC y hyC
    have hstep : ∀ z, eConn nb C v z → z = u ∨ eConn nb (C.erase u) v z := by
      intro z hpath
      induction hpath with
      | refl => exact Or.inr .refl
      | @tail a b _ hab ih =>
        rcases hab with ⟨haC, hbC, hpos⟩
        by_cases hbu : b = u
        · exact Or.inl hbu
        · by_cases hau : a = u
          · subst hau
            exact Or.inr (hnb b hbC hbu hpos)
          · rcases ih with rfl | hpa
            · exact absurd rfl hau
            · exact Or.inr (hpa.tail ⟨Finset.mem_erase.mpr ⟨hau, haC⟩,
                Finset.mem_erase.mpr ⟨hbu, hbC⟩, hpos⟩)
    rcases hstep y hvy with rfl | hr
    · exact absurd hy (Finset.notMem_erase _ _)
    · exact hr
  refine ⟨⟨v, hv⟩, fun x hx y hy => ?_⟩
  exact eConn_trans (C.erase u) (eConn_symm h (C.erase u) (hreach x hx)) (hreach y hy)

lemma path_lemma {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (h : ValidNb m nb) :
    ∀ n : ℕ, ∀ C : Finset (Fin m), C.card = n → Connected nb C →
      ∀ u ∈ C, ∀ bfree : Bool, ¬ tipHas nb C u bfree →
        colCountAt nb C u (!bfree) = 1 ∧ colCount nb C = C.card + 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro C hcard hconn u hu bfree hfree
    by_cases hle1 : C.card ≤ 1
    · have hCeq : C = {u} := by
        ext w
        simp only [Finset.mem_singleton]
        constructor
        · intro hw
          exact Finset.card_le_one.mp hle1 _ hw _ hu
        · rintro rfl; exact hu
      subst hCeq
      have hAt : ∀ b : Bool, colCountAt nb {u} u b = 1 := by
        intro b
        unfold colCountAt
        have heq : (Finset.univ : Finset (Fin m → Bool)).filter
            (fun c => IsCol nb {u} c ∧ c u = b) = {fun i => if i = u then b else false} := by
          ext c
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hcol, hcu⟩
            funext i
            by_cases hiu : i = u
            · subst hiu; simp [hcu]
            · simp [hiu, hcol.1 i (by simp [hiu])]
          · rintro rfl
            refine ⟨⟨fun i hi => by simp [Finset.mem_singleton.not.mp hi], ?_⟩, by simp⟩
            intro i hi j hj hij
            simp only [Finset.mem_singleton] at hi hj
            subst hi; subst hj; exact absurd rfl hij
        rw [heq, Finset.card_singleton]
      refine ⟨hAt (!bfree), ?_⟩
      rw [colCount_split nb {u} u bfree, hAt bfree, hAt (!bfree)]
      simp
    · have hgt1 : 1 < C.card := by omega
      have hex_ne : ∃ w ∈ C, w ≠ u := by
        rcases Finset.exists_mem_ne hgt1 u with ⟨w, hw, hwu⟩
        exact ⟨w, hw, hwu⟩
      rcases hex_ne with ⟨w0, hw0C, hw0u⟩
      have hpath := hconn.2 u hu w0 hw0C
      have hex_adj : ∃ v ∈ C, v ≠ u ∧ 0 < eMult nb u v := by
        rcases Relation.ReflTransGen.cases_head hpath with rfl | ⟨b, hab, _⟩
        · exact absurd rfl hw0u
        · rcases hab with ⟨_, hbC, hpos⟩
          have hbu : b ≠ u := by
            intro heq; subst heq; rw [eMult_self] at hpos; omega
          exact ⟨b, hbC, hbu, hpos⟩
      rcases hex_adj with ⟨v0, hv0C, hv0u, hv0pos⟩
      rcases (eMult_pos_iff u v0).mp hv0pos with ⟨_, b1, b2, hnb0⟩
      have hb1 : b1 = !bfree := by
        cases hb : b1 <;> cases hbf : bfree
        · exfalso; rw [hb] at hnb0; rw [hbf] at hfree; exact hfree ⟨v0, hv0C, hv0u, b2, hnb0⟩
        · rfl
        · rfl
        · exfalso; rw [hb] at hnb0; rw [hbf] at hfree; exact hfree ⟨v0, hv0C, hv0u, b2, hnb0⟩
      rw [hb1] at hnb0
      let C' := C.erase u
      have hv0C' : v0 ∈ C' := Finset.mem_erase.mpr ⟨hv0u, hv0C⟩
      have hC'card : C'.card = C.card - 1 := Finset.card_erase_of_mem hu
      have hC'conn : Connected nb C' := by
        refine connected_erase_of_neighbors h hconn hv0C' ?_
        intro w hwC hwu hwpos
        rcases (eMult_pos_iff u w).mp hwpos with ⟨_, bw1, bw2, hnbw⟩
        have hbw1 : bw1 = !bfree := by
          cases hb : bw1 <;> cases hbf : bfree
          · exfalso; rw [hb] at hnbw; rw [hbf] at hfree; exact hfree ⟨w, hwC, hwu, bw2, hnbw⟩
          · rfl
          · rfl
          · exfalso; rw [hb] at hnbw; rw [hbf] at hfree; exact hfree ⟨w, hwC, hwu, bw2, hnbw⟩
        rw [hbw1] at hnbw
        have heq := h.ext_unique hnbw hnb0 hwu hv0u
        have hweq : w = v0 := congrArg Prod.fst heq
        subst hweq
        exact .refl
      have hv0_free : ¬ tipHas nb C' v0 b2 := by
        rintro ⟨w, hwC', hwv0, bw, hnbw⟩
        have hnb0' : (u, !bfree) ∈ nb (v0, b2) := (h.symm (u, !bfree) (v0, b2)).mp hnb0
        have heq := h.ext_unique hnbw hnb0' hwv0 hv0u.symm
        have hwu : w = u := congrArg Prod.fst heq
        subst hwu
        exact (Finset.notMem_erase w C) hwC'
      have hlt : C'.card < n := by omega
      rcases ih C'.card hlt C' rfl hC'conn v0 hv0C' b2 hv0_free with ⟨hA', hB'⟩
      have hAt_nbf : colCountAt nb C u (!bfree) = 1 := by
        rw [colCountAt_erase_of_nb h C hu hv0C hv0u hnb0, hA']
      have hAt_bf : colCountAt nb C u bfree = C'.card + 1 := by
        rw [colCountAt_erase_of_not_tipHas h C hu hfree, hB']
      refine ⟨hAt_nbf, ?_⟩
      rw [colCount_split nb C u bfree, hAt_bf, hAt_nbf]
      omega

lemma cycle_lemma {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (h : ValidNb m nb)
    (C : Finset (Fin m)) (hconn : Connected nb C)
    (hdeg2 : ∀ j ∈ C, ∑ k ∈ C, eMult nb j k = 2) :
    colCount nb C = 2 := by
  rcases hconn.1 with ⟨u, hu⟩
  have hdu := hdeg2 u hu
  rw [eDeg_eq_tip_count h C u] at hdu
  have htip0 : tipHas nb C u false := by
    by_contra h0; simp only [h0, ↓reduceIte] at hdu; split_ifs at hdu <;> omega
  have htip1 : tipHas nb C u true := by
    by_contra h1; simp only [h1, ↓reduceIte] at hdu; split_ifs at hdu <;> omega
  rcases htip0 with ⟨v0, hv0C, hv0u, b0, hnb0⟩
  rcases htip1 with ⟨v1, hv1C, hv1u, b1, hnb1⟩
  let C' := C.erase u
  have hv0C' : v0 ∈ C' := Finset.mem_erase.mpr ⟨hv0u, hv0C⟩
  have hv1C' : v1 ∈ C' := Finset.mem_erase.mpr ⟨hv1u, hv1C⟩
  have hconn01 : eConn nb C' v0 v1 := by
    by_cases hv01 : v0 = v1
    · subst hv01; exact .refl
    · by_contra hnot
      let D := eComp nb C' v0
      have hv0D : v0 ∈ D := Finset.mem_filter.mpr ⟨hv0C', .refl⟩
      have hv1ND : v1 ∉ D := fun hmem => hnot (Finset.mem_filter.mp hmem).2
      have huND : u ∉ D := fun hmem =>
        (Finset.notMem_erase u C) (Finset.mem_filter.mp hmem).1
      have hdeg_v0 : ∑ k ∈ D, eMult nb v0 k = 1 := by
        rw [eDeg_eq_tip_count h D v0]
        have hno_b0 : ¬ tipHas nb D v0 b0 := by
          rintro ⟨w, hwD, hwv0, bw, hnbw⟩
          have hnb0' := (h.symm (u, false) (v0, b0)).mp hnb0
          have heq := h.ext_unique hnbw hnb0' hwv0 hv0u.symm
          have hwu : w = u := congrArg Prod.fst heq
          subst hwu; exact huND hwD
        have hyes_nb0 : tipHas nb D v0 (!b0) := by
          have hdv0 := hdeg2 v0 hv0C
          rw [eDeg_eq_tip_count h C v0] at hdv0
          have htipC : tipHas nb C v0 (!b0) := by
            cases hb : b0
            · simp only [Bool.not_false]
              by_contra hn; simp only [hn, ↓reduceIte] at hdv0; split_ifs at hdv0 <;> omega
            · simp only [Bool.not_true]
              by_contra hn; simp only [hn, ↓reduceIte] at hdv0; split_ifs at hdv0 <;> omega
          rcases htipC with ⟨w, hwC, hwv0, bw, hnbw⟩
          have hwu : w ≠ u := by
            rintro rfl
            have hnbw' := (h.symm (v0, !b0) (w, bw)).mp hnbw
            cases bw
            · have heq := h.ext_unique hnbw' hnb0 hv0u hv0u
              have hb_eq : (!b0) = b0 := by simpa using congrArg Prod.snd heq
              cases b0 <;> simp at hb_eq
            · have heq := h.ext_unique hnbw' hnb1 hv0u hv1u
              exact hv01 (congrArg Prod.fst heq)
          have hwC' : w ∈ C' := Finset.mem_erase.mpr ⟨hwu, hwC⟩
          have hpos : 0 < eMult nb v0 w := (eMult_pos_iff v0 w).mpr ⟨hwv0.symm, !b0, bw, hnbw⟩
          have hwD : w ∈ D := Finset.mem_filter.mpr
            ⟨hwC', Relation.ReflTransGen.single ⟨hv0C', hwC', hpos⟩⟩
          exact ⟨w, hwD, hwv0, bw, hnbw⟩
        cases b0
        · simp only [Bool.not_false] at hyes_nb0
          simp [hno_b0, hyes_nb0]
        · simp only [Bool.not_true] at hyes_nb0
          simp [hno_b0, hyes_nb0]
      have hdeg_other : ∀ x ∈ D.erase v0, ∑ k ∈ D, eMult nb x k = 2 := by
        intro x hx
        rcases Finset.mem_erase.mp hx with ⟨hxv0, hxD⟩
        rcases Finset.mem_filter.mp hxD with ⟨hxC', hconnx⟩
        have hxC : x ∈ C := Finset.mem_of_mem_erase hxC'
        have hxu : x ≠ u := (Finset.mem_erase.mp hxC').1
        have hxv1 : x ≠ v1 := fun heq => hv1ND (heq ▸ hxD)
        rw [eDeg_eq_tip_count h D x]
        have hboth : ∀ b : Bool, tipHas nb D x b := by
          intro b
          have hdx := hdeg2 x hxC
          rw [eDeg_eq_tip_count h C x] at hdx
          have htipC : tipHas nb C x b := by
            cases b
            · by_contra hn; simp only [hn, ↓reduceIte] at hdx; split_ifs at hdx <;> omega
            · by_contra hn; simp only [hn, ↓reduceIte] at hdx; split_ifs at hdx <;> omega
          rcases htipC with ⟨w, hwC, hwx, bw, hnbw⟩
          have hwu : w ≠ u := by
            rintro rfl
            have hnbw' := (h.symm (x, b) (w, bw)).mp hnbw
            cases bw
            · exact hxv0 (congrArg Prod.fst (h.ext_unique hnbw' hnb0 hxu hv0u))
            · exact hxv1 (congrArg Prod.fst (h.ext_unique hnbw' hnb1 hxu hv1u))
          have hwC' : w ∈ C' := Finset.mem_erase.mpr ⟨hwu, hwC⟩
          have hpos : 0 < eMult nb x w := (eMult_pos_iff x w).mpr ⟨hwx.symm, b, bw, hnbw⟩
          have hwD : w ∈ D := Finset.mem_filter.mpr ⟨hwC', hconnx.tail ⟨hxC', hwC', hpos⟩⟩
          exact ⟨w, hwD, hwx, bw, hnbw⟩
        simp [hboth false, hboth true]
      have htot : ∑ x ∈ D, ∑ k ∈ D, eMult nb x k = 1 + 2 * (D.erase v0).card := by
        rw [← Finset.add_sum_erase _ _ hv0D, hdeg_v0,
            Finset.sum_congr rfl hdeg_other, Finset.sum_const, smul_eq_mul, mul_comm]
      rcases handshaking h D with ⟨t, ht⟩
      omega
  have hC'conn : Connected nb C' := by
    refine connected_erase_of_neighbors h hconn hv0C' ?_
    intro w hwC hwu hwpos
    rcases (eMult_pos_iff u w).mp hwpos with ⟨_, bw1, bw2, hnbw⟩
    cases bw1
    · have hweq : w = v0 := congrArg Prod.fst (h.ext_unique hnbw hnb0 hwu hv0u)
      subst hweq; exact .refl
    · have hweq : w = v1 := congrArg Prod.fst (h.ext_unique hnbw hnb1 hwu hv1u)
      subst hweq; exact hconn01
  have hv0_free : ¬ tipHas nb C' v0 b0 := by
    rintro ⟨w, hwC', hwv0, bw, hnbw⟩
    have hnb0' := (h.symm (u, false) (v0, b0)).mp hnb0
    have hwu : w = u := congrArg Prod.fst (h.ext_unique hnbw hnb0' hwv0 hv0u.symm)
    subst hwu; exact (Finset.notMem_erase w C) hwC'
  have hv1_free : ¬ tipHas nb C' v1 b1 := by
    rintro ⟨w, hwC', hwv1, bw, hnbw⟩
    have hnb1' := (h.symm (u, true) (v1, b1)).mp hnb1
    have hwu : w = u := congrArg Prod.fst (h.ext_unique hnbw hnb1' hwv1 hv1u.symm)
    subst hwu; exact (Finset.notMem_erase w C) hwC'
  have h1 := (path_lemma h C'.card C' rfl hC'conn v0 hv0C' b0 hv0_free).1
  have h2 := (path_lemma h C'.card C' rfl hC'conn v1 hv1C' b1 hv1_free).1
  rw [colCount_split nb C u false]
  simp only [Bool.not_false]
  rw [colCountAt_erase_of_nb h C hu hv0C hv0u hnb0,
      colCountAt_erase_of_nb h C hu hv1C hv1u hnb1, h1, h2]

lemma comp_connected {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (h : ValidNb m nb)
    (S : Finset (Fin m)) {r : Fin m} (hr : r ∈ S) :
    Connected nb (eComp nb S r) := by
  have hrC : r ∈ eComp nb S r := Finset.mem_filter.mpr ⟨hr, .refl⟩
  have hreach : ∀ y ∈ eComp nb S r, eConn nb (eComp nb S r) r y := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨_, hpath⟩
    have hstep : ∀ z, eConn nb S r z → z ∈ eComp nb S r ∧ eConn nb (eComp nb S r) r z := by
      intro z hz
      induction hz with
      | refl => exact ⟨hrC, .refl⟩
      | @tail a b hab_path hab ih =>
        rcases hab with ⟨haS, hbS, hpos⟩
        have hbC : b ∈ eComp nb S r :=
          Finset.mem_filter.mpr ⟨hbS, hab_path.tail ⟨haS, hbS, hpos⟩⟩
        exact ⟨hbC, ih.2.tail ⟨ih.1, hbC, hpos⟩⟩
    exact (hstep y hpath).2
  refine ⟨⟨r, hrC⟩, fun x hx y hy => ?_⟩
  exact eConn_trans _ (eConn_symm h _ (hreach x hx)) (hreach y hy)

lemma deg_comp_eq {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (S : Finset (Fin m)) {r j : Fin m} (hj : j ∈ eComp nb S r) :
    ∑ k ∈ S, eMult nb j k = ∑ k ∈ eComp nb S r, eMult nb j k := by
  symm
  refine Finset.sum_subset (Finset.filter_subset _ S) ?_
  intro k hkS hkNC
  by_contra hne
  have hpos : 0 < eMult nb j k := Nat.pos_of_ne_zero hne
  rcases Finset.mem_filter.mp hj with ⟨hjS, hconnj⟩
  exact hkNC (Finset.mem_filter.mpr ⟨hkS, hconnj.tail ⟨hjS, hkS, hpos⟩⟩)

lemma colCount_comp {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (h : ValidNb m nb)
    (S : Finset (Fin m)) {r : Fin m} (hr : r ∈ S) :
    colCount nb (eComp nb S r) =
      if ∀ j ∈ eComp nb S r, (∑ k ∈ S, eMult nb j k) = 2 then 2
      else (eComp nb S r).card + 1 := by
  have hconn := comp_connected h S hr
  split_ifs with hall
  · refine cycle_lemma h (eComp nb S r) hconn ?_
    intro j hj
    rw [← deg_comp_eq S hj]
    exact hall j hj
  · push Not at hall
    rcases hall with ⟨u, huC, hne2⟩
    have hle2 := eDeg_le_two h (eComp nb S r) u
    rw [← deg_comp_eq S huC] at hle2
    have hlt2 : ∑ k ∈ eComp nb S r, eMult nb u k < 2 := by
      rw [← deg_comp_eq S huC]; omega
    rw [eDeg_eq_tip_count h (eComp nb S r) u] at hlt2
    by_cases hf : tipHas nb (eComp nb S r) u false
    · have ht : ¬ tipHas nb (eComp nb S r) u true := by
        intro ht; simp [hf, ht] at hlt2
      exact (path_lemma h _ _ rfl hconn u huC true ht).2
    · exact (path_lemma h _ _ rfl hconn u huC false hf).2

lemma eComp_eq_of_eConn {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (h : ValidNb m nb)
    (S : Finset (Fin m)) {a b : Fin m} (hab : eConn nb S a b) :
    eComp nb S a = eComp nb S b := by
  ext x
  simp only [eComp, Finset.mem_filter]
  exact ⟨fun ⟨hx, hax⟩ => ⟨hx, eConn_trans S (eConn_symm h S hab) hax⟩,
         fun ⟨hx, hbx⟩ => ⟨hx, eConn_trans S hab hbx⟩⟩

lemma colCount_eq_prod {nb : (Fin m × Bool) → Finset (Fin m × Bool)} (h : ValidNb m nb)
    (S : Finset (Fin m)) :
    colCount nb S = ∏ r ∈ eRoots nb S,
      if ∀ j ∈ eComp nb S r, (∑ k ∈ S, eMult nb j k) = 2 then 2
      else (eComp nb S r).card + 1 := by
  have hdisj_roots : ∀ r₁ ∈ eRoots nb S, ∀ r₂ ∈ eRoots nb S, r₁ ≠ r₂ →
      Disjoint (eComp nb S r₁) (eComp nb S r₂) ∧
      ∀ a ∈ eComp nb S r₁, ∀ b ∈ eComp nb S r₂, eMult nb a b = 0 := by
    intro r₁ hr₁ r₂ hr₂ hne
    rcases Finset.mem_filter.mp hr₁ with ⟨hr₁S, hmin₁⟩
    rcases Finset.mem_filter.mp hr₂ with ⟨hr₂S, hmin₂⟩
    have hnot_conn : ¬ eConn nb S r₁ r₂ := by
      intro h12
      have hle1 : r₁ ≤ r₂ := hmin₁ r₂ (Finset.mem_filter.mpr ⟨hr₂S, h12⟩)
      have hle2 : r₂ ≤ r₁ := hmin₂ r₁ (Finset.mem_filter.mpr ⟨hr₁S, eConn_symm h S h12⟩)
      exact hne (le_antisymm hle1 hle2)
    constructor
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hnot_conn (eConn_trans S (Finset.mem_filter.mp hx1).2
        (eConn_symm h S (Finset.mem_filter.mp hx2).2))
    · intro a ha b hb
      by_contra h0
      have hpos : 0 < eMult nb a b := Nat.pos_of_ne_zero h0
      rcases Finset.mem_filter.mp ha with ⟨haS, hra⟩
      rcases Finset.mem_filter.mp hb with ⟨hbS, hrb⟩
      exact hnot_conn (eConn_trans S (hra.tail ⟨haS, hbS, hpos⟩) (eConn_symm h S hrb))
  have hbi : ∀ R ⊆ eRoots nb S,
      colCount nb (R.biUnion (eComp nb S)) = ∏ r ∈ R, colCount nb (eComp nb S r) := by
    intro R
    induction R using Finset.induction_on with
    | empty =>
      intro _
      simp [colCount_empty]
    | @insert r R hrR ih =>
      intro hsub
      have hr : r ∈ eRoots nb S := hsub (Finset.mem_insert_self r R)
      have hRsub : R ⊆ eRoots nb S := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      rw [Finset.biUnion_insert, Finset.prod_insert hrR]
      have hdisj : Disjoint (eComp nb S r) (R.biUnion (eComp nb S)) := by
        rw [Finset.disjoint_biUnion_right]
        intro r' hr'
        have hne : r ≠ r' := fun heq => hrR (heq ▸ hr')
        exact (hdisj_roots r hr r' (hRsub hr') hne).1
      have hno : ∀ a ∈ eComp nb S r, ∀ b ∈ R.biUnion (eComp nb S), eMult nb a b = 0 := by
        intro a ha b hb
        rcases Finset.mem_biUnion.mp hb with ⟨r', hr', hbr'⟩
        have hne : r ≠ r' := fun heq => hrR (heq ▸ hr')
        exact (hdisj_roots r hr r' (hRsub hr') hne).2 a ha b hbr'
      rw [colCount_union_no_edges h hdisj hno, ih hRsub]
  have hcover_S : (eRoots nb S).biUnion (eComp nb S) = S := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨r, _, hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hxS
      have hne : (eComp nb S x).Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hxS, .refl⟩⟩
      let r := (eComp nb S x).min' hne
      have hrC : r ∈ eComp nb S x := Finset.min'_mem _ hne
      rcases Finset.mem_filter.mp hrC with ⟨hrS, hxr⟩
      have hcomp_eq : eComp nb S r = eComp nb S x := eComp_eq_of_eConn h S (eConn_symm h S hxr)
      have hr_root : r ∈ eRoots nb S := by
        refine Finset.mem_filter.mpr ⟨hrS, fun j hj => ?_⟩
        rw [hcomp_eq] at hj
        exact Finset.min'_le _ j hj
      exact ⟨r, hr_root, by rw [hcomp_eq]; exact Finset.mem_filter.mpr ⟨hxS, .refl⟩⟩
  conv_lhs => rw [← hcover_S]
  rw [hbi (eRoots nb S) Finset.Subset.rfl]
  refine Finset.prod_congr rfl fun r hr => ?_
  exact colCount_comp h S (Finset.mem_filter.mp hr).1

/-! ### Part 4: Realizing any valid multiplicity matrix -/

noncomputable def slot (mult : Fin m → Fin m → ℕ) (i j : Fin m) : Bool :=
  decide (∃ k : Fin m, k < j ∧ mult i k = 1)

def extAdj (mult : Fin m → Fin m → ℕ) (p q : Fin m × Bool) : Prop :=
  (mult p.1 q.1 = 2 ∧ p.2 = q.2) ∨
  (mult p.1 q.1 = 1 ∧ p.2 = slot mult p.1 q.1 ∧ q.2 = slot mult q.1 p.1)

noncomputable def buildNb (mult : Fin m → Fin m → ℕ) (p : Fin m × Bool) :
    Finset (Fin m × Bool) :=
  insert (p.1, !p.2) (Finset.univ.filter (extAdj mult p))

lemma sum_le_univ_pair {f : Fin m → ℕ} {a b : Fin m} (hab : a ≠ b) :
    f a + f b ≤ ∑ x : Fin m, f x := by
  have hsub : ({a, b} : Finset (Fin m)) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset hsub (f := f)
  rw [Finset.sum_pair hab] at hle
  exact hle

lemma sum_le_univ_triple {f : Fin m → ℕ} {a b c : Fin m}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f a + f b + f c ≤ ∑ x : Fin m, f x := by
  have hsub : ({a, b, c} : Finset (Fin m)) ⊆ Finset.univ := Finset.subset_univ _
  have hle := Finset.sum_le_sum_of_subset hsub (f := f)
  have ha : a ∉ ({b, c} : Finset (Fin m)) := by simp [hab, hac]
  rw [Finset.sum_insert ha, Finset.sum_pair hbc] at hle
  omega

lemma slot_inj {mult : Fin m → Fin m → ℕ} {i j₁ j₂ : Fin m}
    (hdeg : ∑ x : Fin m, mult i x ≤ 2)
    (h1 : mult i j₁ = 1) (h2 : mult i j₂ = 1)
    (hslot : slot mult i j₁ = slot mult i j₂) : j₁ = j₂ := by
  by_contra hne
  have aux : ∀ a b : Fin m, a < b → mult i a = 1 → mult i b = 1 →
      slot mult i a ≠ slot mult i b := by
    intro a b hab ha hb heq
    have hsb : slot mult i b = true := by
      simp only [slot, decide_eq_true_eq]
      exact ⟨a, hab, ha⟩
    rw [hsb] at heq
    simp only [slot, decide_eq_true_eq] at heq
    rcases heq with ⟨k, hka, hk⟩
    have h3 := sum_le_univ_triple (f := mult i) (ne_of_lt hka) (ne_of_lt (lt_trans hka hab))
      (ne_of_lt hab)
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact aux j₁ j₂ hlt h1 h2 hslot
  · exact aux j₂ j₁ hgt h2 h1 hslot.symm

lemma buildNb_valid {mult : Fin m → Fin m → ℕ}
    (hself : ∀ i, mult i i = 0)
    (hsymm : ∀ i j, mult i j = mult j i)
    (hdeg : ∀ i, ∑ x : Fin m, mult i x ≤ 2) :
    ValidNb m (buildNb mult) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [buildNb, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with h1 | h2
    · have := congrArg Prod.snd h1; cases p.2 <;> simp at this
    · rcases h2 with ⟨h2, _⟩ | ⟨h1, _, _⟩
      · rw [hself] at h2; omega
      · rw [hself] at h1; omega
  · intro p
    unfold buildNb
    have hle1 : (Finset.univ.filter (extAdj mult p)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro q₁ hq₁ q₂ hq₂
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
      rcases hq₁ with ⟨h1, hb1⟩ | ⟨h1, hs1, hq1⟩ <;>
        rcases hq₂ with ⟨h2, hb2⟩ | ⟨h2, hs2, hq2⟩
      · have hfst : q₁.1 = q₂.1 := by
          by_contra hne
          have hsum := sum_le_univ_pair (f := mult p.1) hne
          have := hdeg p.1
          omega
        exact Prod.ext hfst (hb1.symm.trans hb2)
      · exfalso
        by_cases hfst : q₁.1 = q₂.1
        · rw [hfst] at h1; omega
        · have hsum := sum_le_univ_pair (f := mult p.1) hfst
          have := hdeg p.1
          omega
      · exfalso
        by_cases hfst : q₁.1 = q₂.1
        · rw [hfst] at h1; omega
        · have hsum := sum_le_univ_pair (f := mult p.1) hfst
          have := hdeg p.1
          omega
      · have hfst : q₁.1 = q₂.1 := slot_inj (hdeg p.1) h1 h2 (hs1.symm.trans hs2)
        have hsnd : q₁.2 = q₂.2 := by rw [hq1, hq2, hfst]
        exact Prod.ext hfst hsnd
    have hcard := Finset.card_insert_le (p.1, !p.2) (Finset.univ.filter (extAdj mult p))
    omega
  · intro p q
    simp only [buildNb, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (rfl | hq)
      · left; exact Prod.ext rfl (Bool.not_not p.2).symm
      · right
        rcases hq with ⟨h2, hb⟩ | ⟨h1, hs1, hs2⟩
        · left; exact ⟨(hsymm p.1 q.1).symm.trans h2, hb.symm⟩
        · right; exact ⟨(hsymm p.1 q.1).symm.trans h1, hs2, hs1⟩
    · rintro (rfl | hp)
      · left; exact Prod.ext rfl (Bool.not_not q.2).symm
      · right
        rcases hp with ⟨h2, hb⟩ | ⟨h1, hs1, hs2⟩
        · left; exact ⟨(hsymm q.1 p.1).symm.trans h2, hb.symm⟩
        · right; exact ⟨(hsymm q.1 p.1).symm.trans h1, hs2, hs1⟩
  · intro i
    simp [buildNb]

lemma buildNb_eMult {mult : Fin m → Fin m → ℕ}
    (hself : ∀ i, mult i i = 0)
    (hle : ∀ i j, mult i j ≤ 2) (i j : Fin m) :
    eMult (buildNb mult) i j = mult i j := by
  by_cases hij : i = j
  · subst hij; rw [eMult_self, hself]
  · simp only [eMult, hij, ↓reduceIte]
    have hji : j ≠ i := Ne.symm hij
    have hmem : ∀ p : Bool × Bool,
        (j, p.2) ∈ buildNb mult (i, p.1) ↔ extAdj mult (i, p.1) (j, p.2) := by
      intro p
      simp only [buildNb, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
        Prod.mk.injEq, hji, false_and, false_or]
    have hfilt : (Finset.univ : Finset (Bool × Bool)).filter (fun p => (j, p.2) ∈ buildNb mult (i, p.1)) =
        (Finset.univ : Finset (Bool × Bool)).filter (fun p => extAdj mult (i, p.1) (j, p.2)) := by
      ext p; simp [hmem]
    rw [hfilt]
    have hmle := hle i j
    interval_cases hm : mult i j
    · have heq : (Finset.univ : Finset (Bool × Bool)).filter
          (fun p => extAdj mult (i, p.1) (j, p.2)) = ∅ := by
        ext p; simp [extAdj, hm]
      rw [heq, Finset.card_empty]
    · have heq : (Finset.univ : Finset (Bool × Bool)).filter
          (fun p => extAdj mult (i, p.1) (j, p.2)) = {(slot mult i j, slot mult j i)} := by
        ext ⟨b1, b2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Prod.mk.injEq, extAdj, hm]
        simp
      rw [heq, Finset.card_singleton]
    · have heq : (Finset.univ : Finset (Bool × Bool)).filter
          (fun p => extAdj mult (i, p.1) (j, p.2)) = {(false, false), (true, true)} := by
        ext ⟨b1, b2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq, extAdj, hm]
        cases b1 <;> cases b2 <;> simp
      rw [heq]
      decide

lemma cover_card_eq_colCount_any {nb : (Fin m × Bool) → Finset (Fin m × Bool)}
    (h : ValidNb m nb) (S : Finset (Fin m))
    (ft : Fintype ((Fin m × Bool) → Bool))
    (decMem : ∀ i, Decidable (i ∈ S))
    (decP : DecidablePred (fun x : (Fin m × Bool) → Bool =>
      (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
      ∀ i, xor (x (i, false)) (x (i, true)) = @decide (i ∈ S) (decMem i))) :
    (@Finset.filter _ _ decP (@Finset.univ ((Fin m × Bool) → Bool) ft)).card =
      colCount nb S := by
  rw [← cover_card_eq_colCount h S]
  refine Finset.card_bij (fun x _ => x) ?_ (fun _ _ _ _ h => h) ?_
  · intro x hx
    simp only [Finset.mem_filter, @Finset.mem_univ _ ft, Finset.mem_univ, true_and, IsCover] at hx ⊢
    refine ⟨hx.1, fun i => ?_⟩
    have hi := hx.2 i
    by_cases hmem : i ∈ S
    · simp only [hmem, decide_true] at hi ⊢; exact hi
    · simp only [hmem, decide_false] at hi ⊢; exact hi
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsCover] at hx
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.mem_filter, @Finset.mem_univ _ ft, true_and]
    refine ⟨hx.1, fun i => ?_⟩
    have hi := hx.2 i
    by_cases hmem : i ∈ S
    · simp only [hmem, decide_true] at hi ⊢; exact hi
    · simp only [hmem, decide_false] at hi ⊢; exact hi

end Graph

/-! ### Part 5: Main equivalence -/

theorem main :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m : Nat) (F : Finset (Fin m) → Nat),
      let V := Fin m
      let mult := fun (i j : V) => if i = j then 0 else 4 - F {i,j}
      let conn := fun (S : Finset V) => Relation.ReflTransGen
        (fun i j : V => i ∈ S ∧ j ∈ S ∧ 0 < mult i j)
      let comp := fun (S : Finset V) (i : V) => S.filter (conn S i)
      let roots := fun (S : Finset V) => S.filter (fun i => ∀ j ∈ comp S i, i ≤ j)
      let degree := fun (S : Finset V) (i : V) => ∑ j ∈ S, mult i j
      (∃ nb : (V × Bool) → Finset (V × Bool),
        (∀ p, p ∉ nb p ∧ (nb p).card ≤ 2) ∧ (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧
        (∀ i, (i,true) ∈ nb (i,false)) ∧
        ∀ S, F S = ((Finset.univ : Finset ((V × Bool) → Bool)).filter (fun x =>
          (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
          ∀ i, xor (x (i,false)) (x (i,true)) = decide (i ∈ S))).card) ↔
      (∀ i j : V, i ≠ j → 2 ≤ F {i,j} ∧ F {i,j} ≤ 4) ∧
      (∀ i, degree Finset.univ i ≤ 2) ∧
      ∀ S, F S = ∏ i ∈ roots S,
        if ∀ j ∈ comp S i, degree S j = 2 then 2 else (comp S i).card+1 := by
  intro m F V mult conn comp roots degree
  constructor
  · rintro ⟨nb, h1, h2, h3, hF⟩
    have hV : ValidNb m nb := ⟨fun p => (h1 p).1, fun p => (h1 p).2, h2, h3⟩
    have hF_col : ∀ S, F S = colCount nb S := fun S =>
      (hF S).trans (cover_card_eq_colCount_any hV S _ _ _)
    have hpair : ∀ (i j : Fin m) (S : Finset (Fin m)), i ≠ j →
        (∀ k, k ∈ S ↔ k = i ∨ k = j) → F S = 4 - eMult nb i j :=
      fun i j S hij hS => (hF_col S).trans (colCount_pair hV hij hS)
    have hmult_eq : ∀ i j : Fin m, mult i j = eMult nb i j := by
      intro i j
      dsimp only [mult]
      split_ifs with hij
      · subst hij; symm; exact eMult_self nb i
      · rw [hpair i j _ hij (by intro k; simp)]
        have hle := eMult_le_two hV i j
        omega
    have hmult_fun : mult = eMult nb := funext fun i => funext fun j => hmult_eq i j
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      rw [hpair i j _ hij (by intro k; simp)]
      have hle := eMult_le_two hV i j
      omega
    · intro i
      dsimp only [degree]
      rw [hmult_fun]
      exact eDeg_le_two hV Finset.univ i
    · intro S
      rw [hF_col S, colCount_eq_prod hV S]
      have hconn_eq : ∀ a b, conn S a b ↔ eConn nb S a b := by
        intro a b; dsimp only [conn]; unfold eConn; rw [hmult_fun]
      have hcomp_eq : ∀ i, comp S i = eComp nb S i := by
        intro i; dsimp only [comp]; unfold eComp; ext x; simp [hconn_eq]
      have hroots_eq : roots S = eRoots nb S := by
        dsimp only [roots, V]; unfold eRoots; ext x; simp [hcomp_eq]
      rw [hroots_eq]
      refine Finset.prod_congr rfl fun r _ => ?_
      have hdeg_eq : ∀ j, degree S j = ∑ k ∈ S, eMult nb j k := by
        intro j; dsimp only [degree]; rw [hmult_fun]
      simp only [hcomp_eq, hdeg_eq]
      split_ifs <;> rfl
  · rintro ⟨hrange, hdeg, hprod⟩
    have hself : ∀ i, mult i i = 0 := by
      intro i; dsimp only [mult]; simp
    have hsymm : ∀ i j, mult i j = mult j i := by
      intro i j
      dsimp only [mult]
      by_cases hij : i = j
      · subst hij; rfl
      · have hji : j ≠ i := Ne.symm hij
        simp only [hij, hji, ↓reduceIte]
        congr 2; ext x; simp [or_comm]
    have hle : ∀ i j, mult i j ≤ 2 := by
      intro i j
      dsimp only [mult]
      split_ifs with hij
      · omega
      · have := (hrange i j hij).1
        omega
    let nb := buildNb mult
    have hV : ValidNb m nb := buildNb_valid hself hsymm (by simpa [degree] using hdeg)
    have hmult_eq : ∀ i j, eMult nb i j = mult i j := buildNb_eMult hself hle
    have hmult_fun : eMult nb = mult := funext fun i => funext fun j => hmult_eq i j
    refine ⟨nb, fun p => ⟨hV.no_loop p, hV.card_le p⟩, hV.symm, hV.mark, ?_⟩
    intro S
    dsimp only [V]
    refine Eq.trans ?_ (cover_card_eq_colCount_any hV S _ _ _).symm
    rw [colCount_eq_prod hV S, hprod S]
    have hconn_eq : ∀ a b, eConn nb S a b ↔ conn S a b := by
      intro a b; dsimp only [conn]; unfold eConn; rw [hmult_fun]
    have hcomp_eq : ∀ i, eComp nb S i = comp S i := by
      intro i; dsimp only [comp]; unfold eComp; ext x; simp [hconn_eq]
    have hroots_eq : eRoots nb S = roots S := by
      dsimp only [roots, V]; unfold eRoots; ext x; simp [hcomp_eq]
    rw [hroots_eq]
    refine Finset.prod_congr rfl fun r _ => ?_
    have hdeg_eq : ∀ j, (∑ k ∈ S, eMult nb j k) = degree S j := by
      intro j; dsimp only [degree]; rw [hmult_fun]
    simp only [hcomp_eq, hdeg_eq]
    split_ifs <;> rfl

end PEqualNP.Outside.L_lib_1202_aux

theorem PEqualNP.Outside.L_lib_1202 : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m : Nat) (F : Finset (Fin m) → Nat),
  let V := Fin m
  let mult := fun (i j : V) => if i = j then 0 else 4 - F {i,j}
  let conn := fun (S : Finset V) => Relation.ReflTransGen
    (fun i j : V => i ∈ S ∧ j ∈ S ∧ 0 < mult i j)
  let comp := fun (S : Finset V) (i : V) => S.filter (conn S i)
  let roots := fun (S : Finset V) => S.filter (fun i => ∀ j ∈ comp S i, i ≤ j)
  let degree := fun (S : Finset V) (i : V) => ∑ j ∈ S, mult i j
  (∃ nb : (V × Bool) → Finset (V × Bool),
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 2) ∧ (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    ∀ S, F S = ((Finset.univ : Finset ((V × Bool) → Bool)).filter (fun x =>
      (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
      ∀ i, xor (x (i,false)) (x (i,true)) = decide (i ∈ S))).card) ↔
  (∀ i j : V, i ≠ j → 2 ≤ F {i,j} ∧ F {i,j} ≤ 4) ∧
  (∀ i, degree Finset.univ i ≤ 2) ∧
  ∀ S, F S = ∏ i ∈ roots S,
    if ∀ j ∈ comp S i, degree S j = 2 then 2 else (comp S i).card+1 :=
  PEqualNP.Outside.L_lib_1202_aux.main
