import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1065

open Finset

def w (l : Bool) : ℤ := if l then -1 else 1

def cst (l : Bool) : ℤ := if l then 1 else 0

def D {α : Type} [DecidableEq α] (L : List α) (label : Fin L.length → Bool) (a : α) : ℤ :=
  ∑ q, if L.get q = a then w (label q) else 0

theorem D_nil {α : Type} [DecidableEq α] (label : Fin ([] : List α).length → Bool) (a : α) :
    D [] label a = 0 := Fin.sum_univ_zero _

theorem D_cons {α : Type} [DecidableEq α] (x : α) (L : List α) (l0 : Bool)
    (lab : Fin L.length → Bool) (a : α) :
    D (x :: L) (Fin.cons l0 lab : Fin (L.length + 1) → Bool) a
      = (if x = a then w l0 else 0) + D L lab a := by
  unfold D
  show (∑ q : Fin (L.length + 1), _) = _
  rw [Fin.sum_univ_succ]
  simp

theorem D_bound {α : Type} [DecidableEq α] (a : α) : ∀ (L : List α) (label : Fin L.length → Bool),
    -(L.count a : ℤ) ≤ D L label a ∧ D L label a ≤ L.count a ∧ (D L label a + L.count a) % 2 = 0
  | [], label => by rw [D_nil]; simp
  | x :: L, label => by
    revert label
    show ∀ label : Fin (L.length + 1) → Bool, _
    intro label
    have h := D_cons x L (label 0) (Fin.tail label) a
    rw [Fin.cons_self_tail] at h
    have ih := D_bound a L (Fin.tail label)
    generalize label 0 = l0 at h
    rw [h, List.count_cons]
    by_cases hx : x = a <;> cases l0 <;> simp [hx, w] <;> omega

theorem D_construct {α : Type} [DecidableEq α] (P : α → Prop) : ∀ (L : List α) (c : α → ℤ),
    (∀ a, P a → -(L.count a : ℤ) ≤ c a ∧ c a ≤ L.count a ∧ (c a + L.count a) % 2 = 0) →
    ∃ label : Fin L.length → Bool, ∀ a, P a → D L label a = c a
  | [], c, hc => ⟨(Fin.elim0 : Fin 0 → Bool), fun a ha => by
      have := hc a ha
      rw [D_nil]
      simp only [List.count_nil, Nat.cast_zero] at this
      omega⟩
  | x :: L, c, hc => by
    set l0 := decide (c x ≤ 0) with hl0
    obtain ⟨lab', hlab'⟩ := D_construct P L (fun a => c a - if x = a then w l0 else 0) (by
      intro a ha
      have h := hc a ha
      by_cases hx : x = a
      · subst hx
        rw [List.count_cons_self] at h
        push_cast at h
        rw [if_pos rfl]
        by_cases hc0 : c x ≤ 0
        · have : w l0 = -1 := by simp [hl0, w, hc0]
          rw [this]; omega
        · have : w l0 = 1 := by simp [hl0, w, hc0]
          rw [this]; omega
      · simp only [List.count_cons, hx, if_false, beq_iff_eq, add_zero] at h
        simp only [hx, if_false, sub_zero]
        exact h)
    refine ⟨(Fin.cons l0 lab' : Fin (L.length + 1) → Bool), fun a ha => ?_⟩
    rw [D_cons, hlab' a ha]
    ring

theorem natAbs_iff (d : ℤ) (m : ℕ) :
    (d.natAbs ≤ m ∧ d.natAbs % 2 = m % 2) ↔ (-(m : ℤ) ≤ d ∧ d ≤ m ∧ (d + m) % 2 = 0) := by
  rcases Int.natAbs_eq d with h | h <;> constructor <;> intro hh <;> omega

variable {n : ℕ}

theorem alt_sum (W : Finset (Fin n)) :
    W.powerset.sum (fun V => (-1 : ℤ) ^ (W.card - V.card)) = if W = ∅ then 1 else 0 := by
  have h : ∀ V ∈ W.powerset, (-1 : ℤ) ^ (W.card - V.card) = (-1) ^ W.card * (-1) ^ V.card := by
    intro V hV
    have hle : V.card ≤ W.card := card_le_card (mem_powerset.mp hV)
    have e : (-1 : ℤ) ^ W.card = (-1) ^ (W.card - V.card) * (-1) ^ V.card := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e, mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  rw [sum_congr rfl h, ← mul_sum, sum_powerset_neg_one_pow_card]
  split_ifs with hW <;> simp [hW]

theorem mob_ind (A S : Finset (Fin n)) :
    S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * (if A ⊆ T then 1 else 0))
      = if A = S then 1 else 0 := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← sum_filter]
  by_cases hAS : A ⊆ S
  · have key : (S.powerset.filter (fun T => A ⊆ T)).sum (fun T => (-1 : ℤ) ^ (S.card - T.card))
        = (S \ A).powerset.sum (fun V => (-1 : ℤ) ^ ((S \ A).card - V.card)) := by
      apply sum_nbij' (fun T => T \ A) (fun V => V ∪ A)
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        simp only [mem_powerset]
        exact sdiff_subset_sdiff hT.1 le_rfl
      · intro V hV
        simp only [mem_powerset] at hV
        simp only [mem_filter, mem_powerset]
        exact ⟨union_subset (hV.trans sdiff_subset) hAS, subset_union_right⟩
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        exact sdiff_union_of_subset hT.2
      · intro V hV
        simp only [mem_powerset] at hV
        exact union_sdiff_cancel_right (disjoint_of_subset_left hV disjoint_sdiff_self_left)
      · intro T hT
        simp only [mem_filter, mem_powerset] at hT
        have h1 := card_sdiff_add_card_eq_card hAS
        have h2 := card_sdiff_add_card_eq_card hT.2
        have h3 := card_le_card hT.1
        congr 1
        omega
    rw [key, alt_sum]
    by_cases hA : A = S
    · subst hA; simp
    · rw [if_neg hA, if_neg]
      intro he
      exact hA (subset_antisymm hAS (sdiff_eq_empty_iff_subset.mp he))
  · have : S.powerset.filter (fun T => A ⊆ T) = ∅ := by
      rw [filter_eq_empty_iff]
      intro T hT hA
      exact hAS (hA.trans (mem_powerset.mp hT))
    rw [this, sum_empty, if_neg]
    rintro rfl
    exact hAS subset_rfl

theorem mob_eq_zero (H : Finset (Fin n) → ℤ)
    (h : ∀ S : Finset (Fin n), S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * H T) = 0) :
    ∀ S, H S = 0 := by
  intro S
  refine Finset.strongInduction (p := fun S : Finset (Fin n) => H S = 0) (fun S ih => ?_) S
  have hS := h S
  rw [sum_eq_single S] at hS
  · simpa using hS
  · intro T hT hne
    rw [ih T (ssubset_of_subset_of_ne (mem_powerset.mp hT) hne), mul_zero]
  · intro hS'
    exact absurd (mem_powerset_self S) hS'

def model (L : List (Finset (Fin n))) (label : Fin L.length → Bool) (b : ℤ)
    (T : Finset (Fin n)) : ℤ :=
  b + ∑ q, (cst (label q) + w (label q) * (if L.get q ⊆ T then 1 else 0))

theorem mob_model (L : List (Finset (Fin n))) (label : Fin L.length → Bool) (b : ℤ)
    (S : Finset (Fin n)) :
    S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * model L label b T)
      = (if S = ∅ then b + ∑ q, cst (label q) else 0) + D L label S := by
  have e1 : ∀ T ∈ S.powerset, (-1 : ℤ) ^ (S.card - T.card) * model L label b T
      = b * (-1 : ℤ) ^ (S.card - T.card) + ∑ q, (cst (label q) * (-1 : ℤ) ^ (S.card - T.card)
          + w (label q) * ((-1 : ℤ) ^ (S.card - T.card) * (if L.get q ⊆ T then 1 else 0))) := by
    intro T _
    unfold model
    rw [mul_add, mul_sum]
    congr 1
    · ring
    · exact sum_congr rfl fun q _ => by ring
  rw [sum_congr rfl e1, sum_add_distrib, sum_comm]
  simp only [sum_add_distrib, ← mul_sum, alt_sum, mob_ind]
  unfold D
  by_cases hS : S = ∅ <;> simp [hS, mul_ite, add_assoc]

theorem ind_eq (A T : Finset (Fin n)) (l : Bool) :
    (if decide ((!decide (Disjoint A (univ \ T))) = l) = true then (1 : ℤ) else 0)
      = cst l + w l * (if A ⊆ T then 1 else 0) := by
  have h : Disjoint A (univ \ T) ↔ A ⊆ T := by
    rw [← compl_eq_univ_sdiff]
    exact disjoint_compl_right_iff
  by_cases hA : A ⊆ T <;> cases l <;> simp [h, hA, cst, w]

theorem len_filter : ∀ (m : ℕ) (p : Fin m → Bool),
    (((List.finRange m).filter p).length : ℤ) = ∑ q, if p q = true then (1 : ℤ) else 0
  | 0, p => by simp
  | m + 1, p => by
    have ih := len_filter m (fun i => p i.succ)
    rw [Fin.sum_univ_succ, ← ih, List.finRange_succ, List.filter_cons, List.filter_map]
    cases h : p 0 <;> simp [h, Function.comp_def] <;> ring

theorem len_model (L : List (Finset (Fin n))) (label : Fin L.length → Bool) (b : ℤ)
    (T : Finset (Fin n)) :
    b + (((List.finRange L.length).filter (fun q =>
        decide ((!decide (Disjoint (L.get q) (univ \ T))) = label q))).length : Int)
      = model L label b T := by
  rw [len_filter]
  unfold model
  congr 1
  exact sum_congr rfl fun q _ => ind_eq _ _ _

theorem realize_fwd (G : Finset (Fin n) → ℤ) (L : List (Finset (Fin n)))
    (label : Fin L.length → Bool) (b : ℤ)
    (h : ∀ X : Finset (Fin n), G X = b + (((List.finRange L.length).filter (fun q =>
        decide ((!decide (Disjoint (L.get q) X)) = label q))).length : Int))
    (S : Finset (Fin n)) :
    S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * G (univ \ T))
      = (if S = ∅ then b + ∑ q, cst (label q) else 0) + D L label S := by
  rw [← mob_model]
  refine sum_congr rfl fun T _ => ?_
  rw [h, len_model]

theorem realize_bwd (G : Finset (Fin n) → ℤ) (L : List (Finset (Fin n)))
    (label : Fin L.length → Bool) (b : ℤ)
    (h : ∀ S : Finset (Fin n), S.powerset.sum (fun T => (-1 : ℤ) ^ (S.card - T.card) * G (univ \ T))
      = (if S = ∅ then b + ∑ q, cst (label q) else 0) + D L label S) :
    ∀ X : Finset (Fin n), G X = b + (((List.finRange L.length).filter (fun q =>
        decide ((!decide (Disjoint (L.get q) X)) = label q))).length : Int) := by
  intro X
  have hz := mob_eq_zero (fun T => G (univ \ T) - model L label b T) (fun S => by
    simp only [mul_sub, sum_sub_distrib]
    rw [h S, mob_model]
    ring) (univ \ X)
  have hX : univ \ (univ \ X) = X := by ext; simp
  simp only [hX] at hz
  have hm := len_model L label b (univ \ X)
  rw [hX] at hm
  linarith

theorem sum_count_le (s : Finset (Finset (Fin n))) :
    ∀ L : List (Finset (Fin n)), ∑ S ∈ s, L.count S ≤ L.length
  | [] => by simp
  | x :: L => by
    have ih := sum_count_le s L
    simp only [List.count_cons, sum_add_distrib, List.length_cons, beq_iff_eq]
    have : ∑ S ∈ s, (if x = S then 1 else 0) ≤ 1 := by
      rw [sum_ite_eq]
      split_ifs <;> simp
    omega

end PEqualNP.Outside.L_lib_1065

open PEqualNP.Outside.L_lib_1065 in
theorem PEqualNP.Outside.L_lib_1065 : ∀ (n t : Nat) (F : Fin t → Finset (Fin n) → Int),
  let supports := Finset.univ.erase (∅ : Finset (Fin n))
  let coef := fun (i : Fin t) (S : Finset (Fin n)) => S.powerset.sum
    (fun T => (-1 : Int)^(S.card-T.card)*F i (Finset.univ \ T))
  let peak := fun S => (Finset.univ : Finset (Fin t)).sup (fun i => (coef i S).natAbs)
  let compatible := ∀ S ∈ supports, ∀ i j, (coef i S).natAbs % 2 = (coef j S).natAbs % 2
  let cost := supports.sum peak
  let realizes := fun L : List (Finset (Fin n)) =>
    ∀ i : Fin t, ∃ (b : Int) (label : Fin L.length → Bool), ∀ X : Finset (Fin n),
      F i X = b + (((List.finRange L.length).filter (fun q =>
        decide ((!decide (Disjoint (L.get q) X)) = label q))).length : Int)
  (∀ L, realizes L ↔ ∀ S ∈ supports, ∀ i,
    (coef i S).natAbs ≤ L.count S ∧ (coef i S).natAbs % 2 = (L.count S) % 2) ∧
  ((∃ L, realizes L) ↔ compatible) ∧
  (compatible → ∃ L, realizes L ∧ L.length = cost) ∧
  ∀ L, realizes L → cost ≤ L.length := by
  intro n t F supports coef peak compatible cost realizes
  have hsup : ∀ S, S ∈ supports ↔ S ≠ ∅ := fun S => by simp [supports]
  have P1 : ∀ L, realizes L ↔ ∀ S ∈ supports, ∀ i,
      (coef i S).natAbs ≤ L.count S ∧ (coef i S).natAbs % 2 = (L.count S) % 2 := by
    intro L
    constructor
    · intro hr S hS i
      obtain ⟨b, label, h⟩ := hr i
      have e := realize_fwd (F i) L label b h S
      rw [if_neg ((hsup S).1 hS), zero_add] at e
      have e' : coef i S = D L label S := e
      rw [natAbs_iff, e']
      exact D_bound S L label
    · intro hc i
      obtain ⟨label, hl⟩ := D_construct (fun S => S ≠ ∅) L (coef i)
        (fun S hS => (natAbs_iff _ _).1 (hc S ((hsup S).2 hS) i))
      refine ⟨coef i ∅ - ∑ q, cst (label q) - D L label ∅, label,
        realize_bwd (F i) L label _ ?_⟩
      intro S
      by_cases hS : S = ∅
      · subst hS
        rw [if_pos rfl]
        show coef i ∅ = _
        ring
      · rw [if_neg hS, zero_add]
        exact (hl S hS).symm
  let L0 : List (Finset (Fin n)) := supports.toList.flatMap (fun S => List.replicate (peak S) S)
  have Lc : ∀ S ∈ supports, L0.count S = peak S := by
    intro S hS
    simp only [L0, List.count_flatMap, List.count_replicate, Function.comp_def, beq_iff_eq,
      Finset.sum_map_toList]
    rw [Finset.sum_ite_eq' supports S, if_pos hS]
  have Llen : L0.length = cost := by
    show _ = supports.sum peak
    simp only [L0, List.length_flatMap, List.length_replicate, Finset.sum_map_toList]
  have Pc : compatible → ∀ S ∈ supports, ∀ i,
      (coef i S).natAbs ≤ peak S ∧ (coef i S).natAbs % 2 = peak S % 2 := by
    intro hc S hS i
    refine ⟨Finset.le_sup (f := fun i => (coef i S).natAbs) (Finset.mem_univ i), ?_⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin t)) ⟨i, Finset.mem_univ i⟩
      (fun i => (coef i S).natAbs)
    show _ = ((Finset.univ : Finset (Fin t)).sup fun i => (coef i S).natAbs) % 2
    rw [hj]
    exact hc S hS i j
  have R0 : compatible → realizes L0 := fun hc =>
    (P1 L0).2 (fun S hS i => by rw [Lc S hS]; exact Pc hc S hS i)
  have lower : ∀ L, realizes L → cost ≤ L.length := by
    intro L hr
    have h1 := (P1 L).1 hr
    calc cost = ∑ S ∈ supports, peak S := rfl
      _ ≤ ∑ S ∈ supports, L.count S :=
          Finset.sum_le_sum fun S hS => Finset.sup_le fun i _ => (h1 S hS i).1
      _ ≤ L.length := sum_count_le supports L
  refine ⟨P1, ⟨fun ⟨L, hr⟩ => ?_, fun hc => ⟨L0, R0 hc⟩⟩, fun hc => ⟨L0, R0 hc, Llen⟩, lower⟩
  intro S hS i j
  have h := (P1 L).1 hr S hS
  rw [(h i).2, (h j).2]
