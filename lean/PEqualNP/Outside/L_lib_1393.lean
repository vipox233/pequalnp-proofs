import Mathlib
import PEqualNP.Defs

-- Several graphs on the same vertices, a vertex set S, and the question whether a set contains an edge.
--
-- A set inside S together with a set outside S contains an edge of graph t exactly when the inside part
-- does, or the outside part does, or some outside vertex has a neighbour in the inside part (`hit_union`).
-- First part: taking the outside set empty and then a single vertex reads off the inside answer and, when
-- that is negative, every neighbourhood test; conversely these data decide all three cases.
-- Second part, from a one-bit code z: for a fixed graph and a fixed outside set the answer is a function
-- of z. It is false at the empty inside set, so wherever it is not constant it is true exactly when z
-- differs from z of the empty set (`code`). With the empty outside set this identifies the edges inside S
-- of every graph having one; with one outside vertex it identifies every nonempty neighbourhood. An edge
-- inside S and a nonempty neighbourhood cannot both occur: on a single neighbour the second test is true
-- and the first is false. So either no edge leaves S and the graphs with an edge inside S agree on pairs,
-- or S has no inside edge and the nonempty neighbourhoods agree on single vertices. Conversely the bit
-- `some graph has an edge inside A`, respectively `A meets some neighbourhood`, is a code.

namespace PEqualNP.Outside.L_lib_1393

variable {n q : ℕ}

/-- `A` contains an edge of graph `t`. -/
abbrev hit (E : Fin q → Fin n → Fin n → Bool) (t : Fin q) (A : Finset (Fin n)) : Prop :=
  ∃ u ∈ A, ∃ v ∈ A, E t u v = true

/-- The neighbours of `v` inside `S` in graph `t`. -/
def nbr (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)) (t : Fin q) (v : Fin n) :
    Finset (Fin n) :=
  S.filter (fun u => E t u v = true)

theorem mem_nbr (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)) (t : Fin q) (v u : Fin n) :
    u ∈ nbr E S t v ↔ u ∈ S ∧ E t u v = true := by
  simp [nbr]

theorem hit_mono {E : Fin q → Fin n → Fin n → Bool} {t : Fin q} {A A' : Finset (Fin n)}
    (h : A ⊆ A') (hA : hit E t A) : hit E t A' := by
  obtain ⟨u, hu, v, hv, e⟩ := hA
  exact ⟨u, h hu, v, h hv, e⟩

theorem not_hit_empty (E : Fin q → Fin n → Fin n → Bool) (t : Fin q) :
    ¬ hit E t (∅ : Finset (Fin n)) := by
  rintro ⟨a, ha, -⟩
  exact Finset.notMem_empty a ha

theorem not_hit_single (E : Fin q → Fin n → Fin n → Bool) (hirr : ∀ t v, E t v v = false)
    (t : Fin q) (v : Fin n) : ¬ hit E t {v} := by
  rintro ⟨a, ha, b, hb, e⟩
  rw [Finset.mem_singleton] at ha hb
  rw [ha, hb, hirr] at e
  exact Bool.false_ne_true e

theorem hit_pair (E : Fin q → Fin n → Fin n → Bool) (hsym : ∀ t u v, E t u v = E t v u)
    (hirr : ∀ t v, E t v v = false) (t : Fin q) (u v : Fin n) :
    hit E t {u, v} ↔ E t u v = true := by
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    rw [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb, hirr] at e; exact absurd e Bool.false_ne_true
    · rw [ha, hb] at e; exact e
    · rw [ha, hb, hsym] at e; exact e
    · rw [ha, hb, hirr] at e; exact absurd e Bool.false_ne_true
  · intro e
    exact ⟨u, Finset.mem_insert_self _ _, v,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _), e⟩

theorem hit_union (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n))
    (hsym : ∀ t u v, E t u v = E t v u) (t : Fin q) (A B : Finset (Fin n)) (hA : A ⊆ S) :
    hit E t (A ∪ B) ↔ hit E t A ∨ hit E t B ∨ ∃ v ∈ B, (A ∩ nbr E S t v).Nonempty := by
  constructor
  · rintro ⟨u, hu, v, hv, e⟩
    rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
    · exact Or.inl ⟨u, hu, v, hv, e⟩
    · exact Or.inr (Or.inr ⟨v, hv, u,
        Finset.mem_inter.2 ⟨hu, (mem_nbr E S t v u).2 ⟨hA hu, e⟩⟩⟩)
    · exact Or.inr (Or.inr ⟨u, hu, v,
        Finset.mem_inter.2 ⟨hv, (mem_nbr E S t u v).2 ⟨hA hv, by rw [hsym]; exact e⟩⟩⟩)
    · exact Or.inr (Or.inl ⟨u, hu, v, hv, e⟩)
  · rintro (h | h | ⟨v, hv, u, hu⟩)
    · exact hit_mono Finset.subset_union_left h
    · exact hit_mono Finset.subset_union_right h
    · obtain ⟨hu1, hu2⟩ := Finset.mem_inter.1 hu
      exact ⟨u, Finset.mem_union_left _ hu1, v, Finset.mem_union_right _ hv,
        ((mem_nbr E S t v u).1 hu2).2⟩

theorem hit_add (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n))
    (hsym : ∀ t u v, E t u v = E t v u) (hirr : ∀ t v, E t v v = false) (t : Fin q)
    (A : Finset (Fin n)) (hA : A ⊆ S) (v : Fin n) :
    hit E t (A ∪ {v}) ↔ hit E t A ∨ (A ∩ nbr E S t v).Nonempty := by
  rw [hit_union E S hsym t A {v} hA]
  constructor
  · rintro (h | h | ⟨w, hw, hne⟩)
    · exact Or.inl h
    · exact absurd h (not_hit_single E hirr t v)
    · rw [Finset.mem_singleton] at hw
      rw [hw] at hne
      exact Or.inr hne
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨v, Finset.mem_singleton_self v, h⟩)

theorem single_inter (u : Fin n) (N : Finset (Fin n)) :
    (({u} : Finset (Fin n)) ∩ N).Nonempty ↔ u ∈ N := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h1, h2⟩ := Finset.mem_inter.1 hx
    rw [Finset.mem_singleton] at h1
    rw [← h1]
    exact h2
  · intro h
    exact ⟨u, Finset.mem_inter.2 ⟨Finset.mem_singleton_self u, h⟩⟩

/-- A test that is a function of the one-bit code, false at the empty set and true somewhere, is true
exactly where the code differs from its value at the empty set. -/
theorem code (S : Finset (Fin n)) (z : Finset (Fin n) → Bool) (φ : Finset (Fin n) → Prop)
    (r : Bool → Prop) (H : ∀ A, A ⊆ S → (φ A ↔ r (z A))) (h0 : ¬ φ ∅)
    (hP : ∃ P, P ⊆ S ∧ φ P) : ∀ A, A ⊆ S → (φ A ↔ z A ≠ z ∅) := by
  obtain ⟨P, hPS, hφP⟩ := hP
  have r0 : ¬ r (z ∅) := fun h => h0 ((H ∅ (Finset.empty_subset S)).2 h)
  have rP : r (z P) := (H P hPS).1 hφP
  intro A hA
  rw [H A hA]
  constructor
  · intro hr e
    rw [e] at hr
    exact r0 hr
  · intro hne
    have hPne : z P ≠ z ∅ := fun e => r0 (by rw [← e]; exact rP)
    have hAP : z A = z P := by
      revert hne hPne
      cases z A <;> cases z P <;> cases z ∅ <;> simp
    rw [hAP]
    exact rP

theorem part1 (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n))
    (hsym : ∀ t u v, E t u v = E t v u) (hirr : ∀ t v, E t v v = false) :
    ∀ A A' : Finset (Fin n), A ⊆ S → A' ⊆ S →
      ((∀ t B, Disjoint S B → (hit E t (A ∪ B) ↔ hit E t (A' ∪ B))) ↔
        ∀ t, (hit E t A ↔ hit E t A') ∧
          (¬ hit E t A → ∀ v ∉ S, ((A ∩ nbr E S t v).Nonempty ↔ (A' ∩ nbr E S t v).Nonempty))) := by
  intro A A' hA hA'
  constructor
  · intro H t
    have h1 : hit E t A ↔ hit E t A' := by
      have h := H t ∅ (Finset.disjoint_empty_right S)
      rwa [Finset.union_empty, Finset.union_empty] at h
    refine ⟨h1, fun hnA v hv => ?_⟩
    have h2 := H t {v} (Finset.disjoint_singleton_right.2 hv)
    rw [hit_add E S hsym hirr t A hA v, hit_add E S hsym hirr t A' hA' v] at h2
    have hnA' : ¬ hit E t A' := fun h => hnA (h1.2 h)
    constructor
    · intro h
      rcases h2.1 (Or.inr h) with h3 | h3
      · exact absurd h3 hnA'
      · exact h3
    · intro h
      rcases h2.2 (Or.inr h) with h3 | h3
      · exact absurd h3 hnA
      · exact h3
  · intro H t B hB
    obtain ⟨h1, h2⟩ := H t
    rw [hit_union E S hsym t A B hA, hit_union E S hsym t A' B hA']
    by_cases hAh : hit E t A
    · exact ⟨fun _ => Or.inl (h1.1 hAh), fun _ => Or.inl hAh⟩
    · have hnA' : ¬ hit E t A' := fun h => hAh (h1.2 h)
      constructor
      · rintro (h | h | ⟨v, hv, hne⟩)
        · exact absurd h hAh
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨v, hv, (h2 hAh v (Finset.disjoint_right.1 hB hv)).1 hne⟩)
      · rintro (h | h | ⟨v, hv, hne⟩)
        · exact absurd h hnA'
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨v, hv, (h2 hAh v (Finset.disjoint_right.1 hB hv)).2 hne⟩)

theorem part2 (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n))
    (hsym : ∀ t u v, E t u v = E t v u) (hirr : ∀ t v, E t v v = false) :
    (∃ (z : Finset (Fin n) → Bool) (read : Fin q → Bool → Finset (Fin n) → Prop),
      ∀ t A, A ⊆ S → ∀ B, Disjoint S B → (hit E t (A ∪ B) ↔ read t (z A) B)) ↔
    (((∀ t v, v ∉ S → nbr E S t v = ∅) ∧
        ∀ t z, hit E t S → hit E z S → ∀ u ∈ S, ∀ v ∈ S, E t u v = E z u v) ∨
      ((∀ t, ¬ hit E t S) ∧ ∀ t z v w, v ∉ S → w ∉ S →
        (nbr E S t v).Nonempty → (nbr E S z w).Nonempty → nbr E S t v = nbr E S z w)) := by
  constructor
  · rintro ⟨z, read, hz⟩
    have F1 : ∀ t, hit E t S → ∀ A, A ⊆ S → (hit E t A ↔ z A ≠ z ∅) := by
      intro t ht
      apply code S z (fun A => hit E t A) (fun b => read t b ∅)
      · intro A hA
        have h := hz t A hA ∅ (Finset.disjoint_empty_right S)
        rwa [Finset.union_empty] at h
      · exact not_hit_empty E t
      · exact ⟨S, Finset.Subset.refl S, ht⟩
    have F2 : ∀ t v, v ∉ S → (nbr E S t v).Nonempty → ∀ A, A ⊆ S →
        ((hit E t A ∨ (A ∩ nbr E S t v).Nonempty) ↔ z A ≠ z ∅) := by
      intro t v hv hne
      apply code S z (fun A => hit E t A ∨ (A ∩ nbr E S t v).Nonempty) (fun b => read t b {v})
      · intro A hA
        have h := hz t A hA {v} (Finset.disjoint_singleton_right.2 hv)
        rwa [hit_add E S hsym hirr t A hA v] at h
      · rintro (h | h)
        · exact not_hit_empty E t h
        · obtain ⟨x, hx⟩ := h
          exact Finset.notMem_empty x (Finset.mem_inter.1 hx).1
      · obtain ⟨u, hu⟩ := hne
        exact ⟨{u}, Finset.singleton_subset_iff.2 ((mem_nbr E S t v u).1 hu).1,
          Or.inr ((single_inter u _).2 hu)⟩
    by_cases hint : ∃ t, hit E t S
    · left
      obtain ⟨t0, ht0⟩ := hint
      refine ⟨?_, ?_⟩
      · intro t v hv
        by_contra hne
        obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hne
        have hsub : ({u} : Finset (Fin n)) ⊆ S :=
          Finset.singleton_subset_iff.2 ((mem_nbr E S t v u).1 hu).1
        have h1 := (F2 t v hv ⟨u, hu⟩ {u} hsub).1 (Or.inr ((single_inter u _).2 hu))
        exact not_hit_single E hirr t0 u ((F1 t0 ht0 {u} hsub).2 h1)
      · intro t z' ht hz' u hu v hv
        have hsub : ({u, v} : Finset (Fin n)) ⊆ S := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with hx | hx
          · rw [hx]; exact hu
          · rw [hx]; exact hv
        have h1 := F1 t ht {u, v} hsub
        have h2 := F1 z' hz' {u, v} hsub
        rw [hit_pair E hsym hirr] at h1 h2
        exact Bool.eq_iff_iff.2 (h1.trans h2.symm)
    · right
      refine ⟨fun t ht => hint ⟨t, ht⟩, ?_⟩
      intro t z' v w hv hw hne1 hne2
      ext u
      by_cases huS : u ∈ S
      · have hsub : ({u} : Finset (Fin n)) ⊆ S := Finset.singleton_subset_iff.2 huS
        have a1 : u ∈ nbr E S t v ↔ z {u} ≠ z ∅ := by
          rw [← F2 t v hv hne1 {u} hsub]
          constructor
          · intro h
            exact Or.inr ((single_inter u _).2 h)
          · rintro (h | h)
            · exact absurd h (not_hit_single E hirr t u)
            · exact (single_inter u _).1 h
        have a2 : u ∈ nbr E S z' w ↔ z {u} ≠ z ∅ := by
          rw [← F2 z' w hw hne2 {u} hsub]
          constructor
          · intro h
            exact Or.inr ((single_inter u _).2 h)
          · rintro (h | h)
            · exact absurd h (not_hit_single E hirr z' u)
            · exact (single_inter u _).1 h
        exact a1.trans a2.symm
      · exact ⟨fun h => absurd ((mem_nbr E S t v u).1 h).1 huS,
          fun h => absurd ((mem_nbr E S z' w u).1 h).1 huS⟩
  · rintro (⟨hno, hsame⟩ | ⟨hnoint, hcommon⟩)
    · classical
      refine ⟨fun A => decide (∃ t0, hit E t0 A),
        fun t b B => (b = true ∧ hit E t S) ∨ hit E t B, ?_⟩
      intro t A hA B hB
      rw [hit_union E S hsym t A B hA]
      constructor
      · rintro (h | h | ⟨v, hv, x, hx⟩)
        · exact Or.inl ⟨decide_eq_true ⟨t, h⟩, hit_mono hA h⟩
        · exact Or.inr h
        · exfalso
          have he := hno t v (Finset.disjoint_right.1 hB hv)
          rw [he] at hx
          exact Finset.notMem_empty x (Finset.mem_inter.1 hx).2
      · rintro (⟨h1, h2⟩ | h)
        · obtain ⟨t0, u, hu, v, hv, e⟩ := of_decide_eq_true h1
          refine Or.inl ⟨u, hu, v, hv, ?_⟩
          rw [hsame t t0 h2 (hit_mono hA ⟨u, hu, v, hv, e⟩) u (hA hu) v (hA hv)]
          exact e
        · exact Or.inr (Or.inl h)
    · classical
      refine ⟨fun A => decide (∃ t v, v ∉ S ∧ (A ∩ nbr E S t v).Nonempty),
        fun t b B => hit E t B ∨ (b = true ∧ ∃ v ∈ B, (nbr E S t v).Nonempty), ?_⟩
      intro t A hA B hB
      rw [hit_union E S hsym t A B hA]
      constructor
      · rintro (h | h | ⟨v, hv, hne⟩)
        · exact absurd (hit_mono hA h) (hnoint t)
        · exact Or.inl h
        · exact Or.inr ⟨decide_eq_true ⟨t, v, Finset.disjoint_right.1 hB hv, hne⟩, v, hv,
            hne.mono Finset.inter_subset_right⟩
      · rintro (h | ⟨h1, v, hv, hne⟩)
        · exact Or.inr (Or.inl h)
        · obtain ⟨t', v', hv', hne'⟩ := of_decide_eq_true h1
          have e := hcommon t t' v v' (Finset.disjoint_right.1 hB hv) hv' hne
            (hne'.mono Finset.inter_subset_right)
          exact Or.inr (Or.inr ⟨v, hv, by rw [e]; exact hne'⟩)

end PEqualNP.Outside.L_lib_1393

theorem PEqualNP.Outside.L_lib_1393 :
∀ (n q : Nat) (E : Fin q → Fin n → Fin n → Bool) (S : Finset (Fin n)),
  (∀ t u v, E t u v = E t v u) → (∀ t v, E t v v = false) →
  let hit := fun (t : Fin q) (A : Finset (Fin n)) => ∃ u ∈ A, ∃ v ∈ A, E t u v = true
  let nbr := fun (t : Fin q) (v : Fin n) => S.filter (fun u => E t u v = true)
  let one := ∃ (z : Finset (Fin n) → Bool) (read : Fin q → Bool → Finset (Fin n) → Prop),
    ∀ t A, A ⊆ S → ∀ B, Disjoint S B → (hit t (A ∪ B) ↔ read t (z A) B)
  (∀ A A' : Finset (Fin n), A ⊆ S → A' ⊆ S →
    ((∀ t B, Disjoint S B → (hit t (A ∪ B) ↔ hit t (A' ∪ B))) ↔
      ∀ t, (hit t A ↔ hit t A') ∧
        (¬hit t A → ∀ v ∉ S, ((A ∩ nbr t v).Nonempty ↔ (A' ∩ nbr t v).Nonempty)))) ∧
  (one ↔
    ((∀ t v, v ∉ S → nbr t v = ∅) ∧
      ∀ t z, hit t S → hit z S → ∀ u ∈ S, ∀ v ∈ S, E t u v = E z u v) ∨
    ((∀ t, ¬hit t S) ∧ ∀ t z v w, v ∉ S → w ∉ S →
      (nbr t v).Nonempty → (nbr z w).Nonempty → nbr t v = nbr z w)) := by
  intro n q E S hsym hirr hit nbr one
  exact ⟨PEqualNP.Outside.L_lib_1393.part1 E S hsym hirr,
    PEqualNP.Outside.L_lib_1393.part2 E S hsym hirr⟩
