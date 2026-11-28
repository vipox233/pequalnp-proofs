import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_916

open Finset

variable {m : ℕ}

def tri (A : Finset (Finset (Fin m))) (t : ℕ) : Prop :=
  ∃ (rows : Fin t → Finset (Fin m)) (cols : Fin t → Fin m),
    (∀ i, rows i ∈ A) ∧ (∀ i, cols i ∈ rows i) ∧ ∀ i j, j < i → cols j ∉ rows i

def small (d : ℕ) (A : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  A.filter (fun R => R.Nonempty ∧ R.card ≤ d)

def lower (x : Fin m) (A : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  (A.filter (fun R => x ∈ R)).image (fun R => R.erase x)

theorem tri_cons {A : Finset (Finset (Fin m))} {t : ℕ} (R : Finset (Fin m)) (hR : R ∈ A)
    (x : Fin m) (hx : x ∈ R) (h : tri (A.filter (fun R => x ∉ R)) t) : tri A (t + 1) := by
  obtain ⟨rows, cols, h1, h2, h3⟩ := h
  refine ⟨Fin.cons R rows, Fin.cons x cols, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; exact hR
    · simp only [Fin.cons_succ]; exact (Finset.mem_filter.1 (h1 i)).1
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.cons_zero]; exact hx
    · simp only [Fin.cons_succ]; exact h2 i
  · intro i j hji
    induction i using Fin.cases with
    | zero => exact absurd hji (Fin.not_lt_zero j)
    | succ i =>
      induction j using Fin.cases with
      | zero => simp only [Fin.cons_zero, Fin.cons_succ]; exact (Finset.mem_filter.1 (h1 i)).2
      | succ j => simp only [Fin.cons_succ]; exact h3 i j (Fin.succ_lt_succ_iff.1 hji)

theorem lower_lift {A : Finset (Finset (Fin m))} {x : Fin m} {R' : Finset (Fin m)}
    (h : R' ∈ lower x A) : insert x R' ∈ A ∧ x ∉ R' := by
  unfold lower at h
  rw [Finset.mem_image] at h
  obtain ⟨R, hR, rfl⟩ := h
  rw [Finset.mem_filter] at hR
  rw [Finset.insert_erase hR.2]
  exact ⟨hR.1, Finset.notMem_erase x R⟩

theorem tri_lift {A : Finset (Finset (Fin m))} {t : ℕ} (x : Fin m)
    (h : tri (lower x A) t) : tri A t := by
  obtain ⟨rows, cols, h1, h2, h3⟩ := h
  refine ⟨fun i => insert x (rows i), cols, fun i => (lower_lift (h1 i)).1,
    fun i => Finset.mem_insert_of_mem (h2 i), ?_⟩
  intro i j hji hm
  rw [Finset.mem_insert] at hm
  rcases hm with hm | hm
  · exact (lower_lift (h1 j)).2 (hm ▸ h2 j)
  · exact h3 i j hji hm

theorem tri_snoc {A : Finset (Finset (Fin m))} {t : ℕ} (x : Fin m) (hx : {x} ∈ A)
    (h : tri (lower x A) t) : tri A (t + 1) := by
  obtain ⟨rows, cols, h1, h2, h3⟩ := h
  refine ⟨Fin.snoc (α := fun _ => Finset (Fin m)) (fun i => insert x (rows i)) {x},
    Fin.snoc (α := fun _ => Fin m) cols x, ?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]; exact hx
    · simp only [Fin.snoc_castSucc]; exact (lower_lift (h1 i)).1
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]; exact Finset.mem_singleton_self x
    · simp only [Fin.snoc_castSucc]; exact Finset.mem_insert_of_mem (h2 i)
  · intro i j hji
    induction j using Fin.lastCases with
    | last => exact absurd hji (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc, Finset.mem_singleton]
        intro he
        exact (lower_lift (h1 j)).2 (he ▸ h2 j)
      | cast i =>
        simp only [Fin.snoc_castSucc, Finset.mem_insert]
        rintro (hm | hm)
        · exact (lower_lift (h1 j)).2 (hm ▸ h2 j)
        · exact h3 i j (Fin.castSucc_lt_castSucc_iff.1 hji) hm

theorem small_zero (A : Finset (Finset (Fin m))) : small 0 A = ∅ := by
  apply Finset.filter_eq_empty_iff.2
  rintro R - ⟨hne, hc⟩
  have : R.card = 0 := by omega
  rw [Finset.card_eq_zero] at this
  rw [this] at hne
  exact Finset.not_nonempty_empty hne

theorem split_card (d : ℕ) (x : Fin m) (A : Finset (Finset (Fin m))) :
    (small d A).card ≤ (small d (A.filter (fun R => x ∉ R))).card +
      (small (d - 1) (lower x A)).card + (if ({x} : Finset (Fin m)) ∈ A then 1 else 0) := by
  have e := Finset.card_filter_add_card_filter_not (s := small d A) (fun R => x ∈ R)
  have e1 : (small d A).filter (fun R => ¬ x ∈ R) = small d (A.filter (fun R => x ∉ R)) := by
    ext R; simp only [small, Finset.mem_filter]; tauto
  let T : Finset (Finset (Fin m)) := if ({x} : Finset (Fin m)) ∈ A then {∅} else ∅
  have e2 : ((small d A).filter (fun R => x ∈ R)).card ≤ (small (d - 1) (lower x A) ∪ T).card := by
    apply Finset.card_le_card_of_injOn (fun R => R.erase x)
    · intro R hR
      simp only [Finset.coe_filter, small, Finset.mem_filter, Set.mem_setOf_eq] at hR
      obtain ⟨⟨hRA, -, hcard⟩, hxR⟩ := hR
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      by_cases hne : (R.erase x).Nonempty
      · left
        simp only [small, Finset.mem_filter]
        refine ⟨?_, hne, ?_⟩
        · unfold lower; exact Finset.mem_image.2 ⟨R, Finset.mem_filter.2 ⟨hRA, hxR⟩, rfl⟩
        · rw [Finset.card_erase_of_mem hxR]; omega
      · right
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        have hRx : R = {x} := by
          rw [← Finset.insert_erase hxR, hne]; rfl
        have : ({x} : Finset (Fin m)) ∈ A := hRx ▸ hRA
        simp only [T, if_pos this, Finset.mem_singleton]
        exact hne
    · intro R1 h1 R2 h2 h12
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at h1 h2
      have := congrArg (insert x) h12
      simp only at this
      rwa [Finset.insert_erase h1.2, Finset.insert_erase h2.2] at this
  have e3 : T.card = if ({x} : Finset (Fin m)) ∈ A then 1 else 0 := by
    simp only [T]; split_ifs <;> simp
  have := Finset.card_union_le (small (d - 1) (lower x A)) T
  rw [e1] at e
  omega

theorem mainQ : ∀ (d s m : ℕ) (A : Finset (Finset (Fin m))), ¬ tri A (s + 1) →
    (small d A).card ≤ Nat.choose (d + s - 1) d := by
  intro d
  induction d with
  | zero => intro s m A _; simp [small_zero]
  | succ d' ihd =>
    intro s
    induction s with
    | zero =>
      intro m A hA
      have : small (d' + 1) A = ∅ := by
        apply Finset.filter_eq_empty_iff.2
        rintro R hR ⟨⟨y, hy⟩, -⟩
        apply hA
        refine ⟨fun _ => R, fun _ => y, fun _ => hR, fun _ => hy, fun i j hji => ?_⟩
        exfalso
        have := i.isLt; have := j.isLt
        rw [Fin.lt_iff_val_lt_val] at hji
        omega
      rw [this]; simp
    | succ s' ihs =>
      intro m A hA
      by_cases hem : small (d' + 1) A = ∅
      · rw [hem]; simp
      obtain ⟨R0, hR0⟩ := Finset.nonempty_iff_ne_empty.2 hem
      simp only [small, Finset.mem_filter] at hR0
      obtain ⟨hR0A, ⟨x, hx⟩, -⟩ := hR0
      have h1 : ¬ tri (A.filter (fun R => x ∉ R)) (s' + 1) :=
        fun h => hA (tri_cons R0 hR0A x hx h)
      have hc1 := ihs m _ h1
      have hsplit := split_card (d' + 1) x A
      simp only [Nat.add_sub_cancel] at hsplit
      have e1 : d' + 1 + (s' + 1) - 1 = (d' + s') + 1 := by omega
      have e2 : d' + 1 + s' - 1 = d' + s' := by omega
      rw [e2] at hc1
      have P1 : Nat.choose (d' + s' + 1) (d' + 1) =
          Nat.choose (d' + s') d' + Nat.choose (d' + s') (d' + 1) := Nat.choose_succ_succ _ _
      rw [e1, P1]
      by_cases hx1 : ({x} : Finset (Fin m)) ∈ A
      · rw [if_pos hx1] at hsplit
        have h3 : ¬ tri (lower x A) (s' + 1) := fun h => hA (tri_snoc x hx1 h)
        have hc2 := ihd s' m _ h3
        have key : (small d' (lower x A)).card + 1 ≤ Nat.choose (d' + s') d' := by
          rcases Nat.eq_zero_or_pos d' with h0 | hpos
          · subst h0
            rw [small_zero, Nat.choose_zero_right]; simp
          · obtain ⟨d'', rfl⟩ : ∃ d'', d' = d'' + 1 := ⟨d' - 1, by omega⟩
            have e3 : d'' + 1 + s' - 1 = d'' + s' := by omega
            have P2 : Nat.choose (d'' + 1 + s') (d'' + 1) =
                Nat.choose (d'' + s') d'' + Nat.choose (d'' + s') (d'' + 1) := by
              rw [show d'' + 1 + s' = (d'' + s') + 1 by omega]; exact Nat.choose_succ_succ _ _
            rw [e3] at hc2
            have hp := Nat.choose_pos (show d'' ≤ d'' + s' by omega)
            omega
        omega
      · rw [if_neg hx1] at hsplit
        have h2 : ¬ tri (lower x A) (s' + 1 + 1) := fun h => hA (tri_lift x h)
        have hc2 := ihd (s' + 1) m _ h2
        have e3 : d' + (s' + 1) - 1 = d' + s' := by omega
        rw [e3] at hc2
        omega

theorem tri_inj {A : Finset (Finset (Fin m))} {t : ℕ} (rows : Fin t → Finset (Fin m))
    (cols : Fin t → Fin m) (h2 : ∀ i, cols i ∈ rows i) (h3 : ∀ i j, j < i → cols j ∉ rows i) :
    Function.Injective rows ∧ Function.Injective cols := by
  constructor
  · intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (hij ▸ h2 i) (h3 j i h)
    · exact h
    · exact absurd (hij ▸ h2 j) (h3 i j h)
  · intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (hij ▸ h2 j) (h3 j i h)
    · exact h
    · exact absurd (hij ▸ h2 i) (h3 i j h)

end PEqualNP.Outside.L_lib_916

open PEqualNP.Outside.L_lib_916 in
theorem PEqualNP.Outside.L_lib_916 : ∀ d s : ℕ, 0 < d → 0 < s →
  let triangle := fun (m : ℕ) (A : Finset (Finset (Fin m))) (t : ℕ) =>
    ∃ (rows : Fin t ↪ ↥A) (cols : Fin t ↪ Fin m),
      (∀ i, cols i ∈ (rows i).val) ∧ ∀ i j, j < i → cols j ∉ (rows i).val
  let m₀ := d+s-1
  let extremal := (Finset.univ : Finset (Fin m₀)).powersetCard d
  (∀ (m : ℕ) (A : Finset (Finset (Fin m))), ¬ triangle m A (s+1) →
    (A.filter (fun R => R.Nonempty ∧ R.card ≤ d)).card ≤ Nat.choose m₀ d) ∧
  extremal.card = Nat.choose m₀ d ∧ triangle m₀ extremal s ∧ ¬ triangle m₀ extremal (s+1) := by
  intro d s hd hs triangle m₀ extremal
  have conv : ∀ (m t : ℕ) (A : Finset (Finset (Fin m))), tri A t → triangle m A t := by
    intro m t A ⟨rows, cols, h1, h2, h3⟩
    obtain ⟨hr, hc⟩ := tri_inj (A := A) rows cols h2 h3
    exact ⟨⟨fun i => ⟨rows i, h1 i⟩, fun i j hij => hr (congrArg Subtype.val hij)⟩,
      ⟨cols, hc⟩, h2, h3⟩
  refine ⟨fun m A hA => mainQ d s m A (fun h => hA (conv m _ A h)), ?_, ?_, ?_⟩
  · simp [extremal, m₀, Finset.card_powersetCard]
  · apply conv
    let Tail : Finset (Fin m₀) := Finset.univ.filter (fun x : Fin m₀ => s ≤ x.val)
    have hT : Tail.card = d - 1 := by
      have e := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m₀)))
        (fun x : Fin m₀ => x.val < s)
      have e1 := Fin.card_filter_val_lt (n := m₀) (m := s)
      have e2 : (Finset.univ.filter (fun x : Fin m₀ => ¬ x.val < s)) = Tail := by
        ext x; simp [Tail]
      rw [e2, Finset.card_univ, Fintype.card_fin] at e
      have e3 : (Finset.univ.filter (fun x : Fin m₀ => x.val < s)).card = min m₀ s := e1
      rw [e3] at e
      simp only [m₀] at e ⊢
      omega
    refine ⟨fun i => insert ⟨i.val, by simp only [m₀]; omega⟩ Tail,
      fun i => ⟨i.val, by simp only [m₀]; omega⟩, ?_, ?_, ?_⟩
    · intro i
      simp only [extremal, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      rw [Finset.card_insert_of_notMem]
      · omega
      · simp [Tail]
    · intro i; exact Finset.mem_insert_self _ _
    · intro i j hji hm
      rw [Finset.mem_insert] at hm
      rcases hm with hm | hm
      · have := congrArg Fin.val hm
        simp only at this
        exact absurd (Fin.ext this) (ne_of_lt hji)
      · simp only [Tail, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        have := j.isLt
        omega
  · rintro ⟨rows, cols, h2, h3⟩
    let C : Finset (Fin m₀) := Finset.univ.image (fun j : Fin s => cols (Fin.castSucc j))
    have hC : C.card = s := by
      simp only [C]
      rw [Finset.card_image_of_injective (f := fun j : Fin s => cols (Fin.castSucc j)) _
        (fun a b h => Fin.castSucc_injective s (cols.injective h))]
      simp
    have hR : (rows (Fin.last s)).val.card = d := by
      have := (rows (Fin.last s)).2
      simp only [extremal, Finset.mem_powersetCard] at this
      exact this.2
    have hdisj : Disjoint (rows (Fin.last s)).val C := by
      rw [Finset.disjoint_right]
      intro y hy
      simp only [C, Finset.mem_image, Finset.mem_univ, true_and] at hy
      obtain ⟨j, rfl⟩ := hy
      exact h3 (Fin.last s) (Fin.castSucc j) (Fin.castSucc_lt_last j)
    have := Finset.card_le_univ ((rows (Fin.last s)).val ∪ C)
    rw [Finset.card_union_of_disjoint hdisj, hR, hC, Fintype.card_fin] at this
    simp only [m₀] at this
    omega
