import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_53171_aux

open Finset

/-- Positions `i` where an error block ends before the last index. -/
def Dset (E : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (range (r - 1)).filter (fun i => i ∈ E ∧ i + 1 ∉ E)

/-- Positions `i` just before an error block starts. -/
def Uraw (E : Finset ℕ) (r : ℕ) : Finset ℕ :=
  (range (r - 1)).filter (fun i => i ∉ E ∧ i + 1 ∈ E)

/-- First indices of error blocks not starting at zero. -/
def Uset (E : Finset ℕ) (r : ℕ) : Finset ℕ := (Uraw E r).image (· + 1)

theorem mem_Dset {E : Finset ℕ} {r i : ℕ} :
    i ∈ Dset E r ↔ i + 1 < r ∧ i ∈ E ∧ i + 1 ∉ E := by
  simp only [Dset, mem_filter, mem_range]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩

theorem mem_Uset {E : Finset ℕ} {r j : ℕ} :
    j ∈ Uset E r ↔ 0 < j ∧ j < r ∧ j - 1 ∉ E ∧ j ∈ E := by
  simp only [Uset, Uraw, mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨i, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨by omega, by omega, ?_, h3⟩
    simpa using h2
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨j - 1, ⟨by omega, h2, ?_⟩, by omega⟩
    rwa [Nat.sub_add_cancel h0]

theorem card_Uset (E : Finset ℕ) (r : ℕ) : (Uset E r).card = (Uraw E r).card := by
  unfold Uset
  exact card_image_of_injective _ (add_left_injective 1)

theorem Dset_sub {E : Finset ℕ} {r : ℕ} : Dset E r ⊆ E := fun _ h => (mem_Dset.1 h).2.1

theorem Uset_sub {E : Finset ℕ} {r : ℕ} : Uset E r ⊆ E := fun _ h => (mem_Uset.1 h).2.2.2

theorem Dset_next {E : Finset ℕ} {r i : ℕ} (h : i ∈ Dset E r) : i + 1 ∉ Dset E r :=
  fun h' => (mem_Dset.1 h).2.2 (Dset_sub h')

theorem Uset_next {E : Finset ℕ} {r j : ℕ} (h : j ∈ Uset E r) : j + 1 ∉ Uset E r := by
  intro h'
  have := (mem_Uset.1 h').2.2.1
  simp only [Nat.add_sub_cancel] at this
  exact this (Uset_sub h)

theorem extractE {r : ℕ} {a label : ℕ → Bool} {w : ℕ → ℕ} {budget : ℕ}
    {inst : DecidablePred fun i => a i ≠ label i}
    (h : (@Finset.filter ℕ (fun i => a i ≠ label i) inst (range r)).sum w ≤ budget) :
    ∃ E : Finset ℕ, E ⊆ range r ∧ (∀ i < r, i ∈ E ↔ a i ≠ label i) ∧ E.sum w ≤ budget := by
  refine ⟨_, filter_subset _ _, fun i hi => ?_, h⟩
  rw [mem_filter, mem_range]
  simp [hi]

theorem extractS {r K : ℕ} {a : ℕ → Bool}
    {inst : DecidablePred fun i => a i ≠ a (i + 1)}
    (h : (@Finset.filter ℕ (fun i => a i ≠ a (i + 1)) inst (range (r - 1))).card ≤ K) :
    ∃ S : Finset ℕ, (∀ i, i ∈ S ↔ i < r - 1 ∧ a i ≠ a (i + 1)) ∧ S.card ≤ K := by
  refine ⟨_, fun i => ?_, h⟩
  rw [mem_filter, mem_range]

theorem flag (r : ℕ) (a label : ℕ → Bool) (hl : ∀ i, label (i + 1) = !label i)
    (E : Finset ℕ) (hE : ∀ i < r, i ∈ E ↔ a i ≠ label i)
    (S : Finset ℕ) (hS : ∀ i, i ∈ S ↔ i < r - 1 ∧ a i ≠ a (i + 1)) :
    S.card + ((Dset E r).card + (Uraw E r).card) = r - 1 := by
  have hS' : S = (range (r - 1)).filter (fun i => a i ≠ a (i + 1)) := by
    ext i; rw [hS, mem_filter, mem_range]
  rw [hS', Dset, Uraw, card_filter, card_filter, card_filter, ← sum_add_distrib,
    ← sum_add_distrib]
  have h1s : ∑ i ∈ range (r - 1), (1 : ℕ) = r - 1 := by simp
  refine Eq.trans ?_ h1s
  apply sum_congr rfl
  intro i hi
  rw [mem_range] at hi
  have h1 := hE i (by omega)
  have h2 := hE (i + 1) (by omega)
  have h3 := hl i
  have key : (a i = a (i + 1)) ↔ ¬ (i ∈ E ↔ i + 1 ∈ E) := by
    rw [h1, h2, h3]
    cases a i <;> cases a (i + 1) <;> cases label i <;> decide
  by_cases h4 : i ∈ E <;> by_cases h5 : i + 1 ∈ E <;> simp [h4, h5, key]

theorem build (r K : ℕ) (w : ℕ → ℕ) (label : ℕ → Bool) (hl : ∀ i, label (i + 1) = !label i)
    (E : Finset ℕ) (hEr : E ⊆ range r) (hF : r - 1 - K ≤ (Dset E r).card + (Uraw E r).card)
    (budget : ℕ) (hc : E.sum w ≤ budget) :
    ∃ a : ℕ → Bool, (∀ S : Finset ℕ, (∀ i, i ∈ S ↔ i < r - 1 ∧ a i ≠ a (i + 1)) → S.card ≤ K) ∧
      (∀ T : Finset ℕ, (∀ i, i ∈ T ↔ i < r ∧ a i ≠ label i) → T.sum w ≤ budget) := by
  have key : ∀ b : Bool, (!b) ≠ b := by decide
  refine ⟨fun i => if i ∈ E then !label i else label i, ?_, ?_⟩
  · intro S hS
    have hE : ∀ i < r, i ∈ E ↔ (fun i => if i ∈ E then !label i else label i) i ≠ label i := by
      intro i _
      by_cases h : i ∈ E <;> simp [h, key]
    have := flag r _ label hl E hE S hS
    omega
  · intro T hT
    have hTE : T = E := by
      ext i
      rw [hT]
      by_cases h : i ∈ E
      · simp [h, mem_range.1 (hEr h), key]
      · simp [h]
    rw [hTE]; exact hc

theorem concl {r K budget : ℕ} {a label : ℕ → Bool} {w : ℕ → ℕ}
    {inst1 : DecidablePred fun i => a i ≠ a (i + 1)}
    {inst2 : DecidablePred fun i => a i ≠ label i}
    (h1 : ∀ S : Finset ℕ, (∀ i, i ∈ S ↔ i < r - 1 ∧ a i ≠ a (i + 1)) → S.card ≤ K)
    (h2 : ∀ T : Finset ℕ, (∀ i, i ∈ T ↔ i < r ∧ a i ≠ label i) → T.sum w ≤ budget) :
    (@Finset.filter ℕ (fun i => a i ≠ a (i + 1)) inst1 (range (r - 1))).card ≤ K ∧
      (@Finset.filter ℕ (fun i => a i ≠ label i) inst2 (range r)).sum w ≤ budget :=
  ⟨h1 _ (fun i => by rw [mem_filter, mem_range]), h2 _ (fun i => by rw [mem_filter, mem_range])⟩

theorem sel_odd (r d : ℕ) (hd : d % 2 = 1) (E : Finset ℕ)
    (hF : d ≤ (Dset E r).card + (Uraw E r).card) :
    ∃ M : Finset ℕ, M ⊆ range r ∧ M.card = (d + 1) / 2 ∧ (∀ i ∈ M, (i + 1) % r ∉ M) ∧
      M ⊆ E := by
  rw [← card_Uset] at hF
  by_cases hD : (d + 1) / 2 ≤ (Dset E r).card
  · obtain ⟨M, hMs, hMc⟩ := exists_subset_card_eq hD
    refine ⟨M, fun i hi => ?_, hMc, fun i hi => ?_, hMs.trans Dset_sub⟩
    · have := (mem_Dset.1 (hMs hi)).1; rw [mem_range]; omega
    · have h1 := mem_Dset.1 (hMs hi)
      rw [Nat.mod_eq_of_lt h1.1]
      intro h2
      exact h1.2.2 (Dset_sub (hMs h2))
  · have hU : (d + 1) / 2 ≤ (Uset E r).card := by omega
    obtain ⟨M, hMs, hMc⟩ := exists_subset_card_eq hU
    refine ⟨M, fun i hi => ?_, hMc, fun i hi => ?_, hMs.trans Uset_sub⟩
    · exact mem_range.2 (mem_Uset.1 (hMs hi)).2.1
    · have h1 := mem_Uset.1 (hMs hi)
      intro h2
      by_cases hlt : i + 1 < r
      · rw [Nat.mod_eq_of_lt hlt] at h2
        exact Uset_next (hMs hi) (hMs h2)
      · have h3 : (i + 1) % r = 0 := by
          have : i + 1 = r := by omega
          rw [this, Nat.mod_self]
        rw [h3] at h2
        exact absurd (mem_Uset.1 (hMs h2)).1 (lt_irrefl 0)

theorem even_inner (r m : ℕ) (w edge : ℕ → ℕ) (hedge : ∀ i, i ≠ 0 → edge i = w i)
    (E S : Finset ℕ) (hSE : S ⊆ E) (hS : ∀ i ∈ S, 1 ≤ i ∧ i + 2 ≤ r)
    (hSn : ∀ i ∈ S, i + 1 ∉ S) (hm : m ≤ S.card) :
    ∃ M : Finset ℕ, M ⊆ range (r - 1) ∧ M.card = m ∧ (∀ i ∈ M, (i + 1) % (r - 1) ∉ M) ∧
      M.sum edge ≤ E.sum w := by
  obtain ⟨M, hMs, hMc⟩ := exists_subset_card_eq hm
  refine ⟨M, fun i hi => ?_, hMc, fun i hi => ?_, ?_⟩
  · have := hS i (hMs hi); rw [mem_range]; omega
  · have h1 := hS i (hMs hi)
    intro h2
    by_cases hlt : i + 1 < r - 1
    · rw [Nat.mod_eq_of_lt hlt] at h2
      exact hSn i (hMs hi) (hMs h2)
    · have h3 : (i + 1) % (r - 1) = 0 := by
        have : i + 1 = r - 1 := by omega
        rw [this, Nat.mod_self]
      rw [h3] at h2
      have := hS 0 (hMs h2); omega
  · calc M.sum edge = M.sum w :=
          sum_congr rfl (fun i hi => hedge i (by have := hS i (hMs hi); omega))
      _ ≤ E.sum w := sum_le_sum_of_subset (hMs.trans hSE)

theorem even_wrap (r m : ℕ) (hr : 3 ≤ r) (hm1 : 1 ≤ m) (w edge : ℕ → ℕ)
    (hedge0 : edge 0 = w 0 + w (r - 1)) (hedge : ∀ i, i ≠ 0 → edge i = w i)
    (E S : Finset ℕ) (h0 : 0 ∈ E) (hr1 : r - 1 ∈ E) (hSE : S ⊆ E)
    (hS : ∀ i ∈ S, 2 ≤ i ∧ i + 3 ≤ r)
    (hSn : ∀ i ∈ S, i + 1 ∉ S) (hm : m - 1 ≤ S.card) :
    ∃ M : Finset ℕ, M ⊆ range (r - 1) ∧ M.card = m ∧ (∀ i ∈ M, (i + 1) % (r - 1) ∉ M) ∧
      M.sum edge ≤ E.sum w := by
  obtain ⟨M, hMs, hMc⟩ := exists_subset_card_eq hm
  have h0M : 0 ∉ M := fun h => by have := hS 0 (hMs h); omega
  have hrM : r - 1 ∉ M := fun h => by have := hS (r - 1) (hMs h); omega
  refine ⟨insert 0 M, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [mem_insert] at hi
    rw [mem_range]
    rcases hi with rfl | hi
    · omega
    · have := hS i (hMs hi); omega
  · rw [card_insert_of_notMem h0M]; omega
  · intro i hi
    rw [mem_insert] at hi
    rcases hi with rfl | hi
    · rw [Nat.mod_eq_of_lt (by omega), mem_insert]
      rintro (h | h)
      · omega
      · have := hS _ (hMs h); omega
    · have h1 := hS i (hMs hi)
      rw [Nat.mod_eq_of_lt (by omega), mem_insert]
      rintro (h | h)
      · omega
      · exact hSn i (hMs hi) (hMs h)
  · rw [sum_insert h0M, hedge0]
    have hsub : insert 0 (insert (r - 1) M) ⊆ E := by
      intro i hi
      rw [mem_insert, mem_insert] at hi
      rcases hi with rfl | rfl | hi
      · exact h0
      · exact hr1
      · exact hSE (hMs hi)
    have h0' : 0 ∉ insert (r - 1) M := by
      rw [mem_insert]; rintro (h | h)
      · omega
      · exact h0M h
    have hle : w 0 + (w (r - 1) + M.sum w) ≤ E.sum w := by
      have := sum_le_sum_of_subset (f := w) hsub
      rwa [sum_insert h0', sum_insert hrM] at this
    have heq : M.sum edge = M.sum w :=
      sum_congr rfl (fun i hi => hedge i (by have := hS i (hMs hi); omega))
    rw [heq]; omega

theorem sel_even (r d : ℕ) (hd : d % 2 = 0) (hd1 : 1 ≤ d) (hr : 3 ≤ r) (w edge : ℕ → ℕ)
    (hedge0 : edge 0 = w 0 + w (r - 1)) (hedge : ∀ i, i ≠ 0 → edge i = w i)
    (E : Finset ℕ) (hF : d ≤ (Dset E r).card + (Uraw E r).card) :
    ∃ M : Finset ℕ, M ⊆ range (r - 1) ∧ M.card = (d + 1) / 2 ∧
      (∀ i ∈ M, (i + 1) % (r - 1) ∉ M) ∧ M.sum edge ≤ E.sum w := by
  rw [← card_Uset] at hF
  by_cases hboth : 0 ∈ E ∧ r - 1 ∈ E
  · obtain ⟨h0, hr1⟩ := hboth
    by_cases hD : (d + 1) / 2 ≤ (Dset E r).card
    · have hc := pred_card_le_card_erase (s := Dset E r) (a := if 1 ∈ E then 1 else 0)
      apply even_wrap r ((d + 1) / 2) hr (by omega) w edge hedge0 hedge E
        ((Dset E r).erase (if 1 ∈ E then 1 else 0)) h0 hr1 ((erase_subset _ _).trans Dset_sub)
      · intro i hi
        rw [mem_erase] at hi
        obtain ⟨hic, hi⟩ := hi
        have h1 := mem_Dset.1 hi
        refine ⟨?_, ?_⟩
        · by_contra hlt
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · have h1E : (1 : ℕ) ∉ E := by simpa using h1.2.2
            simp [h1E] at hic
          · simp [h1.2.1] at hic
        · by_contra hlt
          have : i + 1 = r - 1 := by omega
          rw [this] at h1
          exact h1.2.2 hr1
      · intro i hi h
        exact Dset_next (mem_of_mem_erase hi) (mem_of_mem_erase h)
      · omega
    · have hU : (d + 1) / 2 ≤ (Uset E r).card := by omega
      have hc := pred_card_le_card_erase (s := Uset E r)
        (a := if r - 2 ∈ E then r - 2 else r - 1)
      apply even_wrap r ((d + 1) / 2) hr (by omega) w edge hedge0 hedge E
        ((Uset E r).erase (if r - 2 ∈ E then r - 2 else r - 1)) h0 hr1
        ((erase_subset _ _).trans Uset_sub)
      · intro j hj
        rw [mem_erase] at hj
        obtain ⟨hjc, hj⟩ := hj
        have h1 := mem_Uset.1 hj
        refine ⟨?_, ?_⟩
        · by_contra hlt
          have : j = 1 := by omega
          subst this
          exact h1.2.2.1 (by simpa using h0)
        · by_contra hlt
          have : j = r - 1 ∨ j = r - 2 := by omega
          rcases this with rfl | rfl
          · have h2 : r - 2 ∉ E := by
              have := h1.2.2.1
              rwa [show r - 1 - 1 = r - 2 by omega] at this
            simp [h2] at hjc
          · simp [h1.2.2.2] at hjc
      · intro i hi h
        exact Uset_next (mem_of_mem_erase hi) (mem_of_mem_erase h)
      · omega
  · have hc1 := pred_card_le_card_erase (s := Dset E r) (a := 0)
    have hc2 := pred_card_le_card_erase (s := Uset E r) (a := r - 1)
    have hsum : d ≤ ((Dset E r).erase 0).card + ((Uset E r).erase (r - 1)).card + 1 := by
      by_cases h0 : 0 ∈ E
      · have hr1 : r - 1 ∉ E := fun h => hboth ⟨h0, h⟩
        have h' : (Uset E r).erase (r - 1) = Uset E r :=
          erase_eq_of_notMem (fun h => hr1 (Uset_sub h))
        rw [h']; omega
      · have h' : (Dset E r).erase 0 = Dset E r :=
          erase_eq_of_notMem (fun h => h0 (Dset_sub h))
        rw [h']; omega
    by_cases hD : (d + 1) / 2 ≤ ((Dset E r).erase 0).card
    · refine even_inner r _ w edge hedge E ((Dset E r).erase 0)
        ((erase_subset _ _).trans Dset_sub) ?_ ?_ hD
      · intro i hi
        rw [mem_erase] at hi
        have := (mem_Dset.1 hi.2).1
        have := hi.1
        exact ⟨by omega, by omega⟩
      · intro i hi h
        exact Dset_next (mem_of_mem_erase hi) (mem_of_mem_erase h)
    · refine even_inner r _ w edge hedge E ((Uset E r).erase (r - 1))
        ((erase_subset _ _).trans Uset_sub) ?_ ?_ (by omega)
      · intro i hi
        rw [mem_erase] at hi
        have h1 := (mem_Uset.1 hi.2)
        have := h1.1
        have := h1.2.1
        have := hi.1
        exact ⟨by omega, by omega⟩
      · intro i hi h
        exact Uset_next (mem_of_mem_erase hi) (mem_of_mem_erase h)

theorem rev_odd (r d : ℕ) (hd : d % 2 = 1) (hr : 2 ≤ r) (M : Finset ℕ) (hMN : M ⊆ range r)
    (hMc : M.card = (d + 1) / 2) (hMi : ∀ i ∈ M, (i + 1) % r ∉ M) :
    d ≤ (Dset M r).card + (Uraw M r).card := by
  rw [← card_Uset]
  have hT1 : (M.erase (r - 1)).card ≤ (Dset M r).card := by
    apply card_le_card
    intro i hi
    rw [mem_erase] at hi
    have hir := mem_range.1 (hMN hi.2)
    have hne := hi.1
    rw [mem_Dset]
    refine ⟨by omega, hi.2, ?_⟩
    have := hMi i hi.2
    rwa [Nat.mod_eq_of_lt (by omega)] at this
  have hT2 : (M.erase 0).card ≤ (Uset M r).card := by
    apply card_le_card
    intro j hj
    rw [mem_erase] at hj
    have hjr := mem_range.1 (hMN hj.2)
    have hne := hj.1
    rw [mem_Uset]
    refine ⟨by omega, hjr, ?_, hj.2⟩
    intro h
    have := hMi (j - 1) h
    rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hjr] at this
    exact this hj.2
  have hc1 := pred_card_le_card_erase (s := M) (a := r - 1)
  have hc2 := pred_card_le_card_erase (s := M) (a := 0)
  by_cases hr1 : r - 1 ∈ M
  · have h0 : 0 ∉ M := by
      have := hMi (r - 1) hr1
      rwa [Nat.sub_add_cancel (by omega), Nat.mod_self] at this
    rw [erase_eq_of_notMem h0] at hT2
    omega
  · rw [erase_eq_of_notMem hr1] at hT1
    omega

theorem rev_even0 (r d : ℕ) (hd : d % 2 = 0) (M : Finset ℕ) (hMN : M ⊆ range (r - 1))
    (hMc : M.card = (d + 1) / 2) (hMi : ∀ i ∈ M, (i + 1) % (r - 1) ∉ M) (h0 : 0 ∉ M) :
    d ≤ (Dset M r).card + (Uraw M r).card := by
  rw [← card_Uset]
  have hT1 : M.card ≤ (Dset M r).card := by
    apply card_le_card
    intro i hi
    have hir := mem_range.1 (hMN hi)
    rw [mem_Dset]
    refine ⟨by omega, hi, ?_⟩
    intro h
    by_cases hlt : i + 1 < r - 1
    · have := hMi i hi
      rw [Nat.mod_eq_of_lt hlt] at this
      exact this h
    · have := mem_range.1 (hMN h); omega
  have hT2 : M.card ≤ (Uset M r).card := by
    apply card_le_card
    intro j hj
    have hjr := mem_range.1 (hMN hj)
    have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
    rw [mem_Uset]
    refine ⟨by omega, by omega, ?_, hj⟩
    intro h
    have := hMi (j - 1) h
    rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hjr] at this
    exact this hj
  omega

theorem rev_even1 (r d : ℕ) (hd : d % 2 = 0) (hr : 3 ≤ r) (M : Finset ℕ)
    (hMN : M ⊆ range (r - 1))
    (hMc : M.card = (d + 1) / 2) (hMi : ∀ i ∈ M, (i + 1) % (r - 1) ∉ M) (h0 : 0 ∈ M) :
    d ≤ (Dset (insert (r - 1) M) r).card + (Uraw (insert (r - 1) M) r).card := by
  rw [← card_Uset]
  have hrM : r - 1 ∉ M := fun h => by have := mem_range.1 (hMN h); omega
  have hr2 : r - 2 ∉ M := by
    intro h
    have := hMi (r - 2) h
    rw [show r - 2 + 1 = r - 1 by omega, Nat.mod_self] at this
    exact this h0
  have hT1 : M.card ≤ (Dset (insert (r - 1) M) r).card := by
    apply card_le_card
    intro i hi
    have hir := mem_range.1 (hMN hi)
    rw [mem_Dset, mem_insert, mem_insert]
    refine ⟨by omega, Or.inr hi, ?_⟩
    rintro (h | h)
    · apply hr2; rwa [show r - 2 = i by omega]
    · by_cases hlt : i + 1 < r - 1
      · have := hMi i hi
        rw [Nat.mod_eq_of_lt hlt] at this
        exact this h
      · have := mem_range.1 (hMN h); omega
  have hT2 : (insert (r - 1) (M.erase 0)).card ≤ (Uset (insert (r - 1) M) r).card := by
    apply card_le_card
    intro j hj
    rw [mem_insert] at hj
    rw [mem_Uset, mem_insert, mem_insert]
    rcases hj with rfl | hj
    · refine ⟨by omega, by omega, ?_, Or.inl rfl⟩
      rintro (h | h)
      · omega
      · apply hr2; rwa [show r - 2 = r - 1 - 1 by omega]
    · rw [mem_erase] at hj
      have hjr := mem_range.1 (hMN hj.2)
      have hne := hj.1
      refine ⟨by omega, by omega, ?_, Or.inr hj.2⟩
      rintro (h | h)
      · omega
      · have := hMi (j - 1) h
        rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hjr] at this
        exact this hj.2
  have hcard : (insert (r - 1) (M.erase 0)).card = M.card := by
    rw [card_insert_of_notMem (fun h => hrM (mem_of_mem_erase h)), card_erase_of_mem h0]
    have : 0 < M.card := card_pos.2 ⟨0, h0⟩
    omega
  omega

theorem main_aux :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (K r : Nat), K+2 ≤ r → ∀ (w : Nat → Nat) (z : Bool) (budget : Nat),
      let d := r-1-K
      let even := d % 2 = 0
      let N := if even then r-1 else r
      let m := (d+1)/2
      let edge := fun i : Nat => if even ∧ i=0 then w 0+w (r-1) else w i
      let label := fun i : Nat => if i % 2 = 0 then z else !z
      (∃ a : Nat → Bool,
        ((Finset.range (r-1)).filter (fun i => a i ≠ a (i+1))).card ≤ K ∧
        ((Finset.range r).filter (fun i => a i ≠ label i)).sum w ≤ budget) ↔
      ∃ M : Finset Nat, M ⊆ Finset.range N ∧ M.card = m ∧
        (∀ i ∈ M, (i+1) % N ∉ M) ∧ M.sum edge ≤ budget := by
  intro K r hKr w z budget d even N m edge label
  have hd : d = r - 1 - K := rfl
  have hm : m = (d + 1) / 2 := rfl
  have hev : even ↔ d % 2 = 0 := Iff.rfl
  have hl : ∀ i, label (i + 1) = !label i := by
    intro i
    simp only [label]
    split_ifs <;> first | omega | simp
  have hNe : even → N = r - 1 := by
    intro h; simp only [N]; simp [h]
  have hNo : ¬ even → N = r := by
    intro h; simp only [N]; simp [h]
  have hedge0 : even → edge 0 = w 0 + w (r - 1) := by
    intro h; simp only [edge]; simp [h]
  have hedgei : ∀ i, (¬ even ∨ i ≠ 0) → edge i = w i := by
    intro i h; simp only [edge]
    rcases h with h | h <;> simp [h]
  clear_value label edge m N even d
  subst hd hm
  constructor
  · rintro ⟨a, hsw, hcost⟩
    obtain ⟨E, hEr, hE, hcE⟩ := extractE hcost
    obtain ⟨S, hS, hSK⟩ := extractS hsw
    have hF := flag r a label hl E hE S hS
    have hF' : r - 1 - K ≤ (Dset E r).card + (Uraw E r).card := by omega
    by_cases he : even
    · rw [hNe he]
      have hd2 := hev.1 he
      obtain ⟨M, h1, h2, h3, h4⟩ := sel_even r (r - 1 - K) hd2 (by omega) (by omega) w edge
        (hedge0 he) (fun i hi => hedgei i (Or.inr hi)) E hF'
      exact ⟨M, h1, h2, h3, h4.trans hcE⟩
    · rw [hNo he]
      have hd2 : (r - 1 - K) % 2 = 1 := by
        have := mt hev.2 he
        omega
      obtain ⟨M, h1, h2, h3, h4⟩ := sel_odd r (r - 1 - K) hd2 E hF'
      refine ⟨M, h1, h2, h3, ?_⟩
      calc M.sum edge = M.sum w := sum_congr rfl (fun i _ => hedgei i (Or.inl he))
        _ ≤ E.sum w := sum_le_sum_of_subset h4
        _ ≤ budget := hcE
  · rintro ⟨M, hMN, hMc, hMi, hMs⟩
    by_cases he : even
    · rw [hNe he] at hMN hMi
      have hd2 := hev.1 he
      have hr3 : 3 ≤ r := by omega
      by_cases h0 : 0 ∈ M
      · have hrM : r - 1 ∉ M := fun h => by have := mem_range.1 (hMN h); omega
        obtain ⟨a, h1, h2⟩ := build r K w label hl (insert (r - 1) M) (by
            intro i hi
            rw [mem_insert] at hi
            rcases hi with rfl | hi
            · rw [mem_range]; omega
            · have := mem_range.1 (hMN hi); rw [mem_range]; omega)
          (rev_even1 r _ hd2 hr3 M hMN hMc hMi h0) budget (by
            have e1 : (insert (r - 1) M).sum w = w (r - 1) + (w 0 + (M.erase 0).sum w) := by
              rw [sum_insert hrM, ← add_sum_erase M w h0]
            have e2 : M.sum edge = w 0 + w (r - 1) + (M.erase 0).sum w := by
              rw [← add_sum_erase M edge h0, hedge0 he,
                sum_congr rfl (fun i hi => hedgei i (Or.inr (ne_of_mem_erase hi)))]
            rw [e1]; rw [e2] at hMs; omega)
        exact ⟨a, concl h1 h2⟩
      · obtain ⟨a, h1, h2⟩ := build r K w label hl M (fun i hi => by
            have := mem_range.1 (hMN hi); rw [mem_range]; omega)
          (rev_even0 r _ hd2 M hMN hMc hMi h0) budget (by
            have hs : M.sum edge = M.sum w :=
              sum_congr rfl (fun i hi => hedgei i (Or.inr (fun h => h0 (h ▸ hi))))
            rw [hs] at hMs
            exact hMs)
        exact ⟨a, concl h1 h2⟩
    · rw [hNo he] at hMN hMi
      have hd2 : (r - 1 - K) % 2 = 1 := by
        have := mt hev.2 he
        omega
      obtain ⟨a, h1, h2⟩ := build r K w label hl M hMN
        (rev_odd r _ hd2 (by omega) M hMN hMc hMi) budget (by
          have hs : M.sum edge = M.sum w :=
            sum_congr rfl (fun i _ => hedgei i (Or.inl he))
          rw [hs] at hMs
          exact hMs)
      exact ⟨a, concl h1 h2⟩

end PEqualNP.Outside.L_meta_53171_aux

theorem PEqualNP.Outside.L_meta_53171 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (K r : Nat), K+2 ≤ r → ∀ (w : Nat → Nat) (z : Bool) (budget : Nat),
      let d := r-1-K
      let even := d % 2 = 0
      let N := if even then r-1 else r
      let m := (d+1)/2
      let edge := fun i : Nat => if even ∧ i=0 then w 0+w (r-1) else w i
      let label := fun i : Nat => if i % 2 = 0 then z else !z
      (∃ a : Nat → Bool,
        ((Finset.range (r-1)).filter (fun i => a i ≠ a (i+1))).card ≤ K ∧
        ((Finset.range r).filter (fun i => a i ≠ label i)).sum w ≤ budget) ↔
      ∃ M : Finset Nat, M ⊆ Finset.range N ∧ M.card = m ∧
        (∀ i ∈ M, (i+1) % N ∉ M) ∧ M.sum edge ≤ budget :=
  PEqualNP.Outside.L_meta_53171_aux.main_aux
