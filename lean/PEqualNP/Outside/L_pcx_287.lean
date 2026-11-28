import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_287

open PEqualNP.ProofComplexity

private abbrev V := Fin 4 ⊕ (Fin 6 × ℕ)

private def src : Fin 6 → Fin 4 × Bool :=
  ![(0, true), (2, true), (0, false), (0, false), (1, false), (1, false)]

private def dst : Fin 6 → Fin 4 × Bool :=
  ![(1, false), (3, false), (2, true), (3, true), (2, true), (3, true)]

private def negLit {α : Type} (l : Literal α) : Literal α :=
  (l.1, !l.2)

private lemma negLit_negLit {α : Type} (l : Literal α) : negLit (negLit l) = l := by
  rcases l with ⟨v, b⟩
  simp [negLit]

private lemma negLit_ne_self {α : Type} (l : Literal α) : negLit l ≠ l := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [negLit]

private lemma negLit_inj {α : Type} {l₁ l₂ : Literal α} (h : negLit l₁ = negLit l₂) : l₁ = l₂ := by
  have := congrArg negLit h
  simpa [negLit_negLit] using this

private def baseC (e : Fin 6) : Clause (Fin 4) :=
  {negLit (src e), dst e}

private def baseFin : Finset (Clause (Fin 4)) :=
  Finset.univ.image baseC

private def baseSet : Set (Clause (Fin 4)) :=
  ↑baseFin

private def litOf (len : Fin 6 → ℕ) (e : Fin 6) (j : ℕ) : Literal V :=
  if j = 0 then ((Sum.inl (src e).1 : V), (src e).2)
  else if j = len e then ((Sum.inl (dst e).1 : V), (dst e).2)
  else ((Sum.inr (e, j) : V), true)

private def stepOf (len : Fin 6 → ℕ) (e : Fin 6) (j : ℕ) : Clause V :=
  ({negLit (litOf len e j), litOf len e (j + 1)} : Clause V)

private def famOf (len : Fin 6 → ℕ) : Set (Clause V) :=
  {C | ∃ e j, j < len e ∧ C = stepOf len e j}

private def liftLit (l : Literal (Fin 4)) : Literal V :=
  (Sum.inl l.1, l.2)

private def liftClause (C : Clause (Fin 4)) : Clause V :=
  C.image liftLit

private def baseV (e : Fin 6) : Clause V :=
  liftClause (baseC e)

private lemma isDerivation_mono {α : Type} [DecidableEq α] {F G : Set (Clause α)}
    {π : List (Clause α)} (hFG : F ⊆ G) (h : IsDerivation F π) : IsDerivation G π := by
  induction h with
  | nil => exact IsDerivation.nil
  | ax _ hC ih => exact IsDerivation.ax ih (hFG hC)
  | res _ hC hD hR ih => exact IsDerivation.res ih hC hD hR

private lemma isDerivation_append {α : Type} [DecidableEq α] {F : Set (Clause α)}
    {π₁ π₂ : List (Clause α)} (h₁ : IsDerivation F π₁) (h₂ : IsDerivation F π₂) :
    IsDerivation F (π₁ ++ π₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

private lemma clauseSat_resolvent {α : Type} [DecidableEq α] {a : α → Bool} {C D R : Clause α}
    (hR : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  cases hv : a v
  · rcases hC with ⟨l, hlC, hla⟩
    have hne : l ≠ (v, true) := by
      intro heq
      rw [heq] at hla
      exact Bool.false_ne_true (hv.symm.trans hla)
    exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hlC⟩), hla⟩
  · rcases hD with ⟨l, hlD, hla⟩
    have hne : l ≠ (v, false) := by
      intro heq
      rw [heq] at hla
      exact Bool.false_ne_true (hla.symm.trans hv)
    exact ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hlD⟩), hla⟩

private lemma isDerivation_sound {α : Type} [DecidableEq α] {F : Set (Clause α)}
    {π : List (Clause α)} (h : IsDerivation F π) {a : α → Bool} (ha : Satisfies a F) :
    ∀ C ∈ π, ClauseSat a C := by
  induction h with
  | nil => intro C hC; simp at hC
  | ax _ hC ih =>
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact ha _ hC
    · exact ih _ hX
  | res _ hC hD hR ih =>
    intro X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact clauseSat_resolvent hR (ih _ hC) (ih _ hD)
    · exact ih _ hX

private lemma not_isRefutation_of_satisfiable {α : Type} [DecidableEq α] {F : Set (Clause α)}
    (hsat : Satisfiable F) {π : List (Clause α)} (href : IsRefutation F π) : False := by
  rcases hsat with ⟨a, ha⟩
  rcases isDerivation_sound href.1 ha ∅ href.2 with ⟨l, hl, _⟩
  exact Finset.notMem_empty l hl

private def baseWitness : Fin 6 → Fin 4 → Bool
  | ⟨0, _⟩ => fun i => i == 0 || i == 1
  | ⟨1, _⟩ => fun i => i == 2 || i == 3
  | ⟨2, _⟩ => fun i => i == 1 || i == 3
  | ⟨3, _⟩ => fun i => i == 1 || i == 2
  | ⟨4, _⟩ => fun i => i == 0 || i == 3
  | ⟨5, _⟩ => fun i => i == 0 || i == 2

private lemma baseWitness_spec :
    ∀ e₀ e : Fin 6, (∃ l ∈ baseC e, baseWitness e₀ l.1 = l.2) ↔ e ≠ e₀ := by
  decide

private lemma baseWitness_falsifies_self :
    ∀ e₀ : Fin 6, baseWitness e₀ (src e₀).1 = (src e₀).2 ∧
      baseWitness e₀ (dst e₀).1 ≠ (dst e₀).2 := by
  decide

private def famWitness (len : Fin 6 → ℕ) (e₀ : Fin 6) (j₀ : ℕ) : V → Bool
  | Sum.inl v => baseWitness e₀ v
  | Sum.inr (e, j) =>
      if e = e₀ then decide (j ≤ j₀)
      else decide (baseWitness e₀ (src e).1 = (src e).2)

private lemma famWitness_not_self (len : Fin 6 → ℕ) (e₀ : Fin 6) (j₀ : ℕ) (hj₀ : j₀ < len e₀) :
    ¬ ClauseSat (famWitness len e₀ j₀) (stepOf len e₀ j₀) := by
  intro hsat
  rcases hsat with ⟨l, hl, hla⟩
  have hf := baseWitness_falsifies_self e₀
  simp only [stepOf, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl
  · dsimp only [negLit, litOf] at hla
    by_cases h0 : j₀ = 0
    · rw [if_pos h0] at hla
      dsimp only [famWitness] at hla
      rw [hf.1] at hla
      exact (Bool.not_eq_self _).mp hla.symm
    · have hne : j₀ ≠ len e₀ := by omega
      rw [if_neg h0, if_neg hne] at hla
      dsimp only [famWitness] at hla
      simp only [ite_true, le_refl, decide_true, Bool.not_true] at hla
      exact Bool.false_ne_true hla.symm
  · dsimp only [litOf] at hla
    have h1 : j₀ + 1 ≠ 0 := by omega
    rw [if_neg h1] at hla
    by_cases hlast : j₀ + 1 = len e₀
    · rw [if_pos hlast] at hla
      dsimp only [famWitness] at hla
      exact hf.2 hla
    · rw [if_neg hlast] at hla
      dsimp only [famWitness] at hla
      simp only [ite_true, show ¬(j₀ + 1 ≤ j₀) by omega, decide_false] at hla
      exact Bool.false_ne_true hla

private lemma famWitness_sat_other (len : Fin 6 → ℕ) (e₀ : Fin 6) (j₀ : ℕ) (hj₀ : j₀ < len e₀)
    (e : Fin 6) (j : ℕ) (hj : j < len e) (hne : ¬(e = e₀ ∧ j = j₀)) :
    ClauseSat (famWitness len e₀ j₀) (stepOf len e j) := by
  by_cases he : e = e₀
  · subst he
    have hjne : j ≠ j₀ := fun h => hne ⟨rfl, h⟩
    by_cases hlt : j < j₀
    · refine ⟨litOf len e (j + 1), by simp [stepOf], ?_⟩
      dsimp only [litOf]
      have h1 : j + 1 ≠ 0 := by omega
      rw [if_neg h1]
      by_cases hlast : j + 1 = len e
      · exfalso
        omega
      · rw [if_neg hlast]
        dsimp only [famWitness]
        simp only [ite_true, decide_eq_true_eq]
        omega
    · refine ⟨negLit (litOf len e j), by simp [stepOf], ?_⟩
      have hgt : j₀ < j := by omega
      dsimp only [negLit, litOf]
      rw [if_neg (by omega : j ≠ 0), if_neg (by omega : j ≠ len e)]
      dsimp only [famWitness]
      simp only [ite_true, Bool.not_true, decide_eq_false_iff_not]
      omega
  · have hbase : ∃ l ∈ baseC e, baseWitness e₀ l.1 = l.2 :=
      (baseWitness_spec e₀ e).2 he
    by_cases hsrc : baseWitness e₀ (src e).1 = (src e).2
    · have hdst : baseWitness e₀ (dst e).1 = (dst e).2 := by
        rcases hbase with ⟨l, hl, hla⟩
        simp only [baseC, negLit, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · exfalso
          rw [hsrc] at hla
          exact (Bool.not_eq_self _).mp hla.symm
        · exact hla
      refine ⟨litOf len e (j + 1), by simp [stepOf], ?_⟩
      dsimp only [litOf]
      rw [if_neg (by omega : j + 1 ≠ 0)]
      by_cases hlast : j + 1 = len e
      · rw [if_pos hlast]
        exact hdst
      · rw [if_neg hlast]
        dsimp only [famWitness]
        rw [if_neg he]
        simp [hsrc]
    · refine ⟨negLit (litOf len e j), by simp [stepOf], ?_⟩
      dsimp only [negLit, litOf]
      by_cases h0 : j = 0
      · rw [if_pos h0]
        dsimp only [famWitness]
        cases h1 : baseWitness e₀ (src e).1 <;> cases h2 : (src e).2 <;> simp_all
      · rw [if_neg h0, if_neg (by omega : j ≠ len e)]
        dsimp only [famWitness]
        rw [if_neg he]
        simp [hsrc]

private lemma stepOf_inj (len : Fin 6 → ℕ) {e₁ e₂ : Fin 6} {j₁ j₂ : ℕ}
    (h₁ : j₁ < len e₁) (h₂ : j₂ < len e₂) (heq : stepOf len e₁ j₁ = stepOf len e₂ j₂) :
    e₁ = e₂ ∧ j₁ = j₂ := by
  by_contra hne
  have hsat := famWitness_sat_other len e₂ j₂ h₂ e₁ j₁ h₁ hne
  rw [heq] at hsat
  exact famWitness_not_self len e₂ j₂ h₂ hsat

private lemma famOf_sdiff_satisfiable (len : Fin 6 → ℕ) (e₀ : Fin 6) (j₀ : ℕ) (hj₀ : j₀ < len e₀) :
    Satisfiable (famOf len \ {stepOf len e₀ j₀}) := by
  refine ⟨famWitness len e₀ j₀, ?_⟩
  intro C hC
  rcases hC with ⟨⟨e, j, hj, rfl⟩, hneC⟩
  have hne : ¬(e = e₀ ∧ j = j₀) := by
    rintro ⟨rfl, rfl⟩
    exact hneC rfl
  exact famWitness_sat_other len e₀ j₀ hj₀ e j hj hne

private def IsTaut {α : Type} (C : Clause α) : Prop :=
  ∃ v : α, (v, true) ∈ C ∧ (v, false) ∈ C

private lemma isTaut_mono {α : Type} {C D : Clause α} (hsub : C ⊆ D) (ht : IsTaut C) : IsTaut D := by
  rcases ht with ⟨v, h1, h2⟩
  exact ⟨v, hsub h1, hsub h2⟩

private lemma not_isTaut_empty {α : Type} : ¬ IsTaut (∅ : Clause α) := by
  rintro ⟨v, h1, _⟩
  exact Finset.notMem_empty _ h1

private lemma taut_parent_left_sub {α β : Type} [DecidableEq α] [DecidableEq β]
    (σ : Literal α → Literal β) (hσ : ∀ l, σ (negLit l) = negLit (σ l))
    {C D R : Clause α} (hR : IsResolvent C D R)
    (htC : IsTaut (C.image σ)) (hngR : ¬ IsTaut (R.image σ)) :
    D.image σ ⊆ R.image σ := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  rcases htC with ⟨w, hwT, hwF⟩
  have hsubC : (C.erase (v, true)).image σ ⊆ (C.erase (v, true) ∪ D.erase (v, false)).image σ :=
    Finset.image_subset_image Finset.subset_union_left
  have hsubD : (D.erase (v, false)).image σ ⊆ (C.erase (v, true) ∪ D.erase (v, false)).image σ :=
    Finset.image_subset_image Finset.subset_union_right
  have hnotBoth : ¬((w, true) ∈ (C.erase (v, true)).image σ ∧ (w, false) ∈ (C.erase (v, true)).image σ) := by
    rintro ⟨h1, h2⟩
    exact hngR ⟨w, hsubC h1, hsubC h2⟩
  have hvF_in : σ (v, false) ∈ (C.erase (v, true)).image σ := by
    rcases Finset.mem_image.mp hwT with ⟨l₁, hl₁C, hl₁eq⟩
    rcases Finset.mem_image.mp hwF with ⟨l₂, hl₂C, hl₂eq⟩
    by_cases h1 : l₁ = (v, true)
    · subst h1
      have h2ne : l₂ ≠ (v, true) := by
        intro h2
        rw [h2] at hl₂eq
        have := hl₁eq.symm.trans hl₂eq
        exact Bool.false_ne_true (congrArg Prod.snd this).symm
      have hneg : σ (v, false) = (w, false) := by
        have h := hσ (v, true)
        dsimp only [negLit] at h
        rw [hl₁eq] at h
        simpa using h
      rw [hneg]
      exact Finset.mem_image.mpr ⟨l₂, Finset.mem_erase.mpr ⟨h2ne, hl₂C⟩, hl₂eq⟩
    · by_cases h2 : l₂ = (v, true)
      · subst h2
        have hneg : σ (v, false) = (w, true) := by
          have h := hσ (v, true)
          dsimp only [negLit] at h
          rw [hl₂eq] at h
          simpa using h
        rw [hneg]
        exact Finset.mem_image.mpr ⟨l₁, Finset.mem_erase.mpr ⟨h1, hl₁C⟩, hl₁eq⟩
      · exfalso
        exact hnotBoth ⟨Finset.mem_image.mpr ⟨l₁, Finset.mem_erase.mpr ⟨h1, hl₁C⟩, hl₁eq⟩,
          Finset.mem_image.mpr ⟨l₂, Finset.mem_erase.mpr ⟨h2, hl₂C⟩, hl₂eq⟩⟩
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨l, hlD, rfl⟩
  by_cases hl : l = (v, false)
  · subst hl
    exact hsubC hvF_in
  · exact hsubD (Finset.mem_image.mpr ⟨l, Finset.mem_erase.mpr ⟨hl, hlD⟩, rfl⟩)

private lemma taut_parent_right_sub {α β : Type} [DecidableEq α] [DecidableEq β]
    (σ : Literal α → Literal β) (hσ : ∀ l, σ (negLit l) = negLit (σ l))
    {C D R : Clause α} (hR : IsResolvent C D R)
    (htD : IsTaut (D.image σ)) (hngR : ¬ IsTaut (R.image σ)) :
    C.image σ ⊆ R.image σ := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  rcases htD with ⟨w, hwT, hwF⟩
  have hsubC : (C.erase (v, true)).image σ ⊆ (C.erase (v, true) ∪ D.erase (v, false)).image σ :=
    Finset.image_subset_image Finset.subset_union_left
  have hsubD : (D.erase (v, false)).image σ ⊆ (C.erase (v, true) ∪ D.erase (v, false)).image σ :=
    Finset.image_subset_image Finset.subset_union_right
  have hnotBoth : ¬((w, true) ∈ (D.erase (v, false)).image σ ∧ (w, false) ∈ (D.erase (v, false)).image σ) := by
    rintro ⟨h1, h2⟩
    exact hngR ⟨w, hsubD h1, hsubD h2⟩
  have hvT_in : σ (v, true) ∈ (D.erase (v, false)).image σ := by
    rcases Finset.mem_image.mp hwT with ⟨l₁, hl₁D, hl₁eq⟩
    rcases Finset.mem_image.mp hwF with ⟨l₂, hl₂D, hl₂eq⟩
    by_cases h1 : l₁ = (v, false)
    · subst h1
      have h2ne : l₂ ≠ (v, false) := by
        intro h2
        rw [h2] at hl₂eq
        have := hl₁eq.symm.trans hl₂eq
        exact Bool.false_ne_true (congrArg Prod.snd this).symm
      have hneg : σ (v, true) = (w, false) := by
        have h := hσ (v, false)
        dsimp only [negLit] at h
        rw [hl₁eq] at h
        simpa using h
      rw [hneg]
      exact Finset.mem_image.mpr ⟨l₂, Finset.mem_erase.mpr ⟨h2ne, hl₂D⟩, hl₂eq⟩
    · by_cases h2 : l₂ = (v, false)
      · subst h2
        have hneg : σ (v, true) = (w, true) := by
          have h := hσ (v, false)
          dsimp only [negLit] at h
          rw [hl₂eq] at h
          simpa using h
        rw [hneg]
        exact Finset.mem_image.mpr ⟨l₁, Finset.mem_erase.mpr ⟨h1, hl₁D⟩, hl₁eq⟩
      · exfalso
        exact hnotBoth ⟨Finset.mem_image.mpr ⟨l₁, Finset.mem_erase.mpr ⟨h1, hl₁D⟩, hl₁eq⟩,
          Finset.mem_image.mpr ⟨l₂, Finset.mem_erase.mpr ⟨h2, hl₂D⟩, hl₂eq⟩⟩
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨l, hlC, rfl⟩
  by_cases hl : l = (v, true)
  · subst hl
    exact hsubD hvT_in
  · exact hsubC (Finset.mem_image.mpr ⟨l, Finset.mem_erase.mpr ⟨hl, hlC⟩, rfl⟩)

private lemma good_parents_step {α β : Type} [DecidableEq α] [DecidableEq β]
    (σ : Literal α → Literal β) (hσ : ∀ l, σ (negLit l) = negLit (σ l))
    {C D R : Clause α} (hR : IsResolvent C D R)
    {C' D' : Clause β} (hC' : C' ⊆ C.image σ) (hD' : D' ⊆ D.image σ) :
    C' ⊆ R.image σ ∨ D' ⊆ R.image σ ∨
      ∃ R' : Clause β, (IsResolvent C' D' R' ∨ IsResolvent D' C' R') ∧ R' ⊆ R.image σ := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  set l := σ (v, true) with hl_def
  have hneg : σ (v, false) = negLit l := by
    have h := hσ (v, true)
    simpa [negLit, hl_def] using h
  have hsubC : (C'.erase l) ⊆ (C.erase (v, true) ∪ D.erase (v, false)).image σ := by
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxne, hxC'⟩
    rcases Finset.mem_image.mp (hC' hxC') with ⟨a, haC, rfl⟩
    have hane : a ≠ (v, true) := fun h => hxne (by rw [h, hl_def])
    exact Finset.mem_image.mpr ⟨a, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hane, haC⟩), rfl⟩
  have hsubD : (D'.erase (negLit l)) ⊆ (C.erase (v, true) ∪ D.erase (v, false)).image σ := by
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hxne, hxD'⟩
    rcases Finset.mem_image.mp (hD' hxD') with ⟨a, haD, rfl⟩
    have hane : a ≠ (v, false) := fun h => hxne (by rw [h, hneg])
    exact Finset.mem_image.mpr ⟨a, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hane, haD⟩), rfl⟩
  by_cases hlC' : l ∈ C'
  · by_cases hlD' : negLit l ∈ D'
    · right; right
      rcases l with ⟨w, b⟩
      cases b
      · refine ⟨D'.erase (w, true) ∪ C'.erase (w, false), Or.inr ⟨w, ?_, hlC', rfl⟩, ?_⟩
        · simpa [negLit] using hlD'
        · exact Finset.union_subset (by simpa [negLit] using hsubD) hsubC
      · refine ⟨C'.erase (w, true) ∪ D'.erase (w, false), Or.inl ⟨w, hlC', ?_, rfl⟩, ?_⟩
        · simpa [negLit] using hlD'
        · exact Finset.union_subset hsubC (by simpa [negLit] using hsubD)
    · right; left
      intro x hx
      exact hsubD (Finset.mem_erase.mpr ⟨fun h => hlD' (h ▸ hx), hx⟩)
  · left
    intro x hx
    exact hsubC (Finset.mem_erase.mpr ⟨fun h => hlC' (h ▸ hx), hx⟩)

private def dropSub (len : Fin 6 → ℕ) (e₀ : Fin 6) (l : Literal V) : Literal V :=
  if l.1 = Sum.inr (e₀, len e₀ - 1) then
    ((Sum.inl (dst e₀).1 : V), if l.2 then (dst e₀).2 else !(dst e₀).2)
  else l

private lemma dropSub_negLit (len : Fin 6 → ℕ) (e₀ : Fin 6) (l : Literal V) :
    dropSub len e₀ (negLit l) = negLit (dropSub len e₀ l) := by
  rcases l with ⟨v, b⟩
  dsimp only [dropSub, negLit]
  by_cases h : v = Sum.inr (e₀, len e₀ - 1)
  · rw [if_pos h, if_pos h]
    cases b <;> simp
  · rw [if_neg h, if_neg h]

private lemma dropSub_step_last (len : Fin 6 → ℕ) (e₀ : Fin 6) (hge : 2 ≤ len e₀) :
    IsTaut ((stepOf len e₀ (len e₀ - 1)).image (dropSub len e₀)) := by
  have h1 : litOf len e₀ (len e₀ - 1) = (Sum.inr (e₀, len e₀ - 1), true) := by
    dsimp only [litOf]
    rw [if_neg (by omega), if_neg (by omega)]
  have h2 : litOf len e₀ (len e₀ - 1 + 1) = (Sum.inl (dst e₀).1, (dst e₀).2) := by
    dsimp only [litOf]
    rw [if_neg (by omega), if_pos (by omega)]
  have hm1 : dropSub len e₀ (negLit (litOf len e₀ (len e₀ - 1))) =
      ((Sum.inl (dst e₀).1 : V), !(dst e₀).2) := by
    rw [h1]
    simp [negLit, dropSub]
  have hm2 : dropSub len e₀ (litOf len e₀ (len e₀ - 1 + 1)) =
      ((Sum.inl (dst e₀).1 : V), (dst e₀).2) := by
    rw [h2]
    simp [dropSub]
  refine ⟨Sum.inl (dst e₀).1, ?_, ?_⟩
  · cases hd : (dst e₀).2
    · exact Finset.mem_image.mpr ⟨negLit (litOf len e₀ (len e₀ - 1)), by simp [stepOf], by rw [hm1, hd]; rfl⟩
    · exact Finset.mem_image.mpr ⟨litOf len e₀ (len e₀ - 1 + 1), by simp [stepOf], by rw [hm2, hd]⟩
  · cases hd : (dst e₀).2
    · exact Finset.mem_image.mpr ⟨litOf len e₀ (len e₀ - 1 + 1), by simp [stepOf], by rw [hm2, hd]⟩
    · exact Finset.mem_image.mpr ⟨negLit (litOf len e₀ (len e₀ - 1)), by simp [stepOf], by rw [hm1, hd]; rfl⟩

private lemma dropSub_step_other (len : Fin 6 → ℕ) (e₀ : Fin 6) (hge : 2 ≤ len e₀)
    (e : Fin 6) (j : ℕ) (hj : j < len e) (hne : ¬(e = e₀ ∧ j = len e₀ - 1)) :
    (stepOf len e j).image (dropSub len e₀) =
      stepOf (Function.update len e₀ (len e₀ - 1)) e j ∧
    j < Function.update len e₀ (len e₀ - 1) e := by
  set len' := Function.update len e₀ (len e₀ - 1) with hlen'_def
  have hlen'_e : ∀ x, len' x = if x = e₀ then len e₀ - 1 else len x := by
    intro x
    by_cases hx : x = e₀
    · subst hx; simp [len']
    · simp [len', hx]
  have hj' : j < len' e := by
    rw [hlen'_e]
    split_ifs with he
    · subst he; omega
    · exact hj
  refine ⟨?_, hj'⟩
  have hlit_eq : ∀ m, m ≤ len' e →
      dropSub len e₀ (litOf len e m) = litOf len' e m := by
    intro m hm
    dsimp only [litOf]
    by_cases h0 : m = 0
    · rw [if_pos h0, if_pos h0]
      simp [dropSub]
    · rw [if_neg h0, if_neg h0]
      by_cases he : e = e₀
      · subst he
        have hlen'0 : len' e = len e - 1 := by simp [len']
        rw [hlen'0] at hm ⊢
        have hmne : m ≠ len e := by omega
        rw [if_neg hmne]
        by_cases hlast : m = len e - 1
        · rw [if_pos hlast]
          simp [dropSub, hlast]
        · rw [if_neg hlast]
          simp [dropSub, hlast]
      · have hlen'e : len' e = len e := by simp [len', he]
        rw [hlen'e]
        by_cases hlast : m = len e
        · rw [if_pos hlast]
          simp [dropSub]
        · rw [if_neg hlast]
          simp [dropSub, he]
  have h1 : dropSub len e₀ (negLit (litOf len e j)) = negLit (litOf len' e j) := by
    rw [dropSub_negLit, hlit_eq j (by omega)]
  have h2 : dropSub len e₀ (litOf len e (j + 1)) = litOf len' e (j + 1) :=
    hlit_eq (j + 1) (by omega)
  simp only [stepOf, Finset.image_insert, Finset.image_singleton, h1, h2]

private lemma contract_one_step_deriv (len : Fin 6 → ℕ) (e₀ : Fin 6) (hge : 2 ≤ len e₀)
    (π : List (Clause V)) (hπ : IsDerivation (famOf len) π) :
    let σ := dropSub len e₀
    let len' := Function.update len e₀ (len e₀ - 1)
    ∃ (π' : List (Clause V)) (nBad nBridge : ℕ),
      IsDerivation (famOf len') π' ∧
      (∀ C ∈ π, ¬ IsTaut (C.image σ) → ∃ C' ∈ π', C' ⊆ C.image σ) ∧
      π'.length + nBad + nBridge ≤ π.length ∧
      (nBad = 0 → ∀ C ∈ π, ¬ IsTaut (C.image σ)) ∧
      (nBridge = 0 → ∃ πg : List (Clause V),
        IsDerivation (famOf len \ {stepOf len e₀ (len e₀ - 1)}) πg ∧
        ∀ C ∈ π, ¬ IsTaut (C.image σ) → C ∈ πg) := by
  intro σ len'
  induction hπ with
  | nil =>
    refine ⟨[], 0, 0, IsDerivation.nil, ?_, by simp, ?_, ?_⟩
    · intro C hC; simp at hC
    · intro _ C hC; simp at hC
    · intro _; exact ⟨[], IsDerivation.nil, fun C hC => by simp at hC⟩
  | @ax π C hπ hC ih =>
    rcases ih with ⟨π', nBad, nBridge, hder', hmap, hlen, hnb, hbr⟩
    by_cases hgood : ¬ IsTaut (C.image σ)
    · rcases hC with ⟨e, j, hj, rfl⟩
      have hne : ¬(e = e₀ ∧ j = len e₀ - 1) := by
        rintro ⟨rfl, rfl⟩
        exact hgood (dropSub_step_last len e hge)
      have hdrop := dropSub_step_other len e₀ hge e j hj hne
      have hmem' : (stepOf len e j).image σ ∈ famOf len' :=
        ⟨e, j, hdrop.2, hdrop.1⟩
      have hne_last : stepOf len e j ≠ stepOf len e₀ (len e₀ - 1) := by
        intro heq
        exact hne (stepOf_inj len hj (by omega) heq)
      refine ⟨(stepOf len e j).image σ :: π', nBad, nBridge,
        IsDerivation.ax hder' hmem', ?_, ?_, ?_, ?_⟩
      · intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact ⟨(stepOf len e j).image σ, List.mem_cons_self, Finset.Subset.refl _⟩
        · rcases hmap X hX hXg with ⟨C', hC'π', hsub⟩
          exact ⟨C', List.mem_cons_of_mem _ hC'π', hsub⟩
      · simp only [List.length_cons]; omega
      · intro h0 X hX
        rcases List.mem_cons.mp hX with rfl | hX
        · exact hgood
        · exact hnb h0 X hX
      · intro h0
        rcases hbr h0 with ⟨πg, hderg, hmapg⟩
        refine ⟨stepOf len e j :: πg,
          IsDerivation.ax hderg ⟨⟨e, j, hj, rfl⟩, hne_last⟩, ?_⟩
        intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hmapg X hX hXg)
    · refine ⟨π', nBad + 1, nBridge, hder', ?_, ?_, ?_, ?_⟩
      · intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact False.elim (hgood hXg)
        · exact hmap X hX hXg
      · simp only [List.length_cons]; omega
      · intro h0; omega
      · intro h0
        rcases hbr h0 with ⟨πg, hderg, hmapg⟩
        refine ⟨πg, hderg, ?_⟩
        intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact False.elim (hgood hXg)
        · exact hmapg X hX hXg
  | @res π C D R hπ hC hD hR ih =>
    rcases ih with ⟨π', nBad, nBridge, hder', hmap, hlen, hnb, hbr⟩
    by_cases hgoodR : ¬ IsTaut (R.image σ)
    · by_cases hgoodCD : ¬ IsTaut (C.image σ) ∧ ¬ IsTaut (D.image σ)
      · rcases hmap C hC hgoodCD.1 with ⟨C', hC'π', hC'sub⟩
        rcases hmap D hD hgoodCD.2 with ⟨D', hD'π', hD'sub⟩
        rcases good_parents_step σ (dropSub_negLit len e₀) hR hC'sub hD'sub with
          hC'R | hD'R | ⟨R', hR'res, hR'sub⟩
        · refine ⟨π', nBad, nBridge, hder', ?_, ?_, ?_, ?_⟩
          · intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact ⟨C', hC'π', hC'R⟩
            · exact hmap X hX hXg
          · simp only [List.length_cons]; omega
          · intro h0 X hX
            rcases List.mem_cons.mp hX with rfl | hX
            · exact hgoodR
            · exact hnb h0 X hX
          · intro h0
            rcases hbr h0 with ⟨πg, hderg, hmapg⟩
            refine ⟨R :: πg,
              IsDerivation.res hderg (hmapg C hC hgoodCD.1) (hmapg D hD hgoodCD.2) hR, ?_⟩
            intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmapg X hX hXg)
        · refine ⟨π', nBad, nBridge, hder', ?_, ?_, ?_, ?_⟩
          · intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact ⟨D', hD'π', hD'R⟩
            · exact hmap X hX hXg
          · simp only [List.length_cons]; omega
          · intro h0 X hX
            rcases List.mem_cons.mp hX with rfl | hX
            · exact hgoodR
            · exact hnb h0 X hX
          · intro h0
            rcases hbr h0 with ⟨πg, hderg, hmapg⟩
            refine ⟨R :: πg,
              IsDerivation.res hderg (hmapg C hC hgoodCD.1) (hmapg D hD hgoodCD.2) hR, ?_⟩
            intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmapg X hX hXg)
        · have hder'R : IsDerivation (famOf len') (R' :: π') := by
            rcases hR'res with h1 | h2
            · exact IsDerivation.res hder' hC'π' hD'π' h1
            · exact IsDerivation.res hder' hD'π' hC'π' h2
          refine ⟨R' :: π', nBad, nBridge, hder'R, ?_, ?_, ?_, ?_⟩
          · intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact ⟨R', List.mem_cons_self, hR'sub⟩
            · rcases hmap X hX hXg with ⟨E', hE'π', hsub⟩
              exact ⟨E', List.mem_cons_of_mem _ hE'π', hsub⟩
          · simp only [List.length_cons]; omega
          · intro h0 X hX
            rcases List.mem_cons.mp hX with rfl | hX
            · exact hgoodR
            · exact hnb h0 X hX
          · intro h0
            rcases hbr h0 with ⟨πg, hderg, hmapg⟩
            refine ⟨R :: πg,
              IsDerivation.res hderg (hmapg C hC hgoodCD.1) (hmapg D hD hgoodCD.2) hR, ?_⟩
            intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (hmapg X hX hXg)
      · have hRwit : ∃ E' ∈ π', E' ⊆ R.image σ := by
          by_cases htC : IsTaut (C.image σ)
          · have hDsub := taut_parent_left_sub σ (dropSub_negLit len e₀) hR htC hgoodR
            have hgoodD : ¬ IsTaut (D.image σ) := fun htD => hgoodR (isTaut_mono hDsub htD)
            rcases hmap D hD hgoodD with ⟨D', hD'π', hD'sub⟩
            exact ⟨D', hD'π', hD'sub.trans hDsub⟩
          · have htD : IsTaut (D.image σ) := by
              by_contra hgoodD
              exact hgoodCD ⟨htC, hgoodD⟩
            have hCsub := taut_parent_right_sub σ (dropSub_negLit len e₀) hR htD hgoodR
            rcases hmap C hC htC with ⟨C', hC'π', hC'sub⟩
            exact ⟨C', hC'π', hC'sub.trans hCsub⟩
        refine ⟨π', nBad, nBridge + 1, hder', ?_, ?_, ?_, ?_⟩
        · intro X hX hXg
          rcases List.mem_cons.mp hX with rfl | hX
          · exact hRwit
          · exact hmap X hX hXg
        · simp only [List.length_cons]; omega
        · intro h0
          exfalso
          exact hgoodCD ⟨hnb h0 C hC, hnb h0 D hD⟩
        · intro h0; omega
    · refine ⟨π', nBad + 1, nBridge, hder', ?_, ?_, ?_, ?_⟩
      · intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact False.elim (hgoodR hXg)
        · exact hmap X hX hXg
      · simp only [List.length_cons]; omega
      · intro h0; omega
      · intro h0
        rcases hbr h0 with ⟨πg, hderg, hmapg⟩
        refine ⟨πg, hderg, ?_⟩
        intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact False.elim (hgoodR hXg)
        · exact hmapg X hX hXg

private lemma contract_one_step (len : Fin 6 → ℕ) (e₀ : Fin 6) (hge : 2 ≤ len e₀)
    {π : List (Clause V)} (href : IsRefutation (famOf len) π) :
    ∃ π' : List (Clause V),
      IsRefutation (famOf (Function.update len e₀ (len e₀ - 1))) π' ∧
      π'.length + 2 ≤ π.length := by
  rcases contract_one_step_deriv len e₀ hge π href.1 with
    ⟨π', nBad, nBridge, hder', hmap, hlen, hnb, hbr⟩
  have hgood0 : ¬ IsTaut ((∅ : Clause V).image (dropSub len e₀)) := by
    simpa using not_isTaut_empty (α := V)
  rcases hmap ∅ href.2 hgood0 with ⟨C', hC'π', hsub⟩
  have hC'0 : C' = ∅ := by simpa using hsub
  subst hC'0
  have hsat := famOf_sdiff_satisfiable len e₀ (len e₀ - 1) (by omega)
  have hbr_pos : 1 ≤ nBridge := by
    by_contra h0
    have h0' : nBridge = 0 := by omega
    rcases hbr h0' with ⟨πg, hderg, hmapg⟩
    exact not_isRefutation_of_satisfiable hsat ⟨hderg, hmapg ∅ href.2 hgood0⟩
  have hnb_pos : 1 ≤ nBad := by
    by_contra h0
    have h0' : nBad = 0 := by omega
    have hall := hnb h0'
    have hder_sdiff : IsDerivation (famOf len \ {stepOf len e₀ (len e₀ - 1)}) π := by
      have haux : ∀ ρ, IsDerivation (famOf len) ρ →
          (∀ C ∈ ρ, ¬ IsTaut (C.image (dropSub len e₀))) →
          IsDerivation (famOf len \ {stepOf len e₀ (len e₀ - 1)}) ρ := by
        intro ρ hρ
        induction hρ with
        | nil => intro _; exact IsDerivation.nil
        | @ax ρ C hρ hC ih =>
          intro hgood
          have hne : C ≠ stepOf len e₀ (len e₀ - 1) := by
            intro heq
            rw [heq] at hgood
            exact hgood (stepOf len e₀ (len e₀ - 1)) List.mem_cons_self
              (dropSub_step_last len e₀ hge)
          exact IsDerivation.ax
            (ih (fun X hX => hgood X (List.mem_cons_of_mem _ hX))) ⟨hC, hne⟩
        | @res ρ C D R hρ hC hD hR ih =>
          intro hgood
          exact IsDerivation.res
            (ih (fun X hX => hgood X (List.mem_cons_of_mem _ hX))) hC hD hR
      exact haux π href.1 hall
    exact not_isRefutation_of_satisfiable hsat ⟨hder_sdiff, href.2⟩
  exact ⟨π', ⟨hder', hC'π'⟩, by omega⟩

private lemma contract_to_one (k : ℕ) :
    ∀ (len : Fin 6 → ℕ), (∀ e, 1 ≤ len e) → (∑ e : Fin 6, (len e - 1)) = k →
    ∀ {π : List (Clause V)}, IsRefutation (famOf len) π →
    ∃ π₁ : List (Clause V), IsRefutation (famOf (fun _ => 1)) π₁ ∧
      π₁.length + 2 * k ≤ π.length := by
  induction k with
  | zero =>
    intro len hpos hsum π href
    have hlen1 : len = fun _ => 1 := by
      funext e
      have h0 : len e - 1 = 0 := by
        have hle := Finset.single_le_sum (f := fun x : Fin 6 => len x - 1)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
        omega
      have hp := hpos e
      omega
    subst hlen1
    exact ⟨π, href, by omega⟩
  | succ k ih =>
    intro len hpos hsum π href
    have hex : ∃ e₀ : Fin 6, 2 ≤ len e₀ := by
      by_contra hall
      push_neg at hall
      have h0 : (∑ e : Fin 6, (len e - 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro e _
        have := hall e
        omega
      omega
    rcases hex with ⟨e₀, hge⟩
    rcases contract_one_step len e₀ hge href with ⟨π', href', hlen'⟩
    set len' := Function.update len e₀ (len e₀ - 1)
    have hpos' : ∀ e, 1 ≤ len' e := by
      intro e
      by_cases he : e = e₀
      · subst he; simp [len']; omega
      · simp [len', he, hpos e]
    have hsum' : (∑ e : Fin 6, (len' e - 1)) = k := by
      have hsplit := Finset.add_sum_erase Finset.univ (fun e : Fin 6 => len e - 1) (Finset.mem_univ e₀)
      have hsplit' := Finset.add_sum_erase Finset.univ (fun e : Fin 6 => len' e - 1) (Finset.mem_univ e₀)
      have herase : ∑ e ∈ Finset.univ.erase e₀, (len' e - 1) =
          ∑ e ∈ Finset.univ.erase e₀, (len e - 1) := by
        apply Finset.sum_congr rfl
        intro e he
        have hne : e ≠ e₀ := (Finset.mem_erase.mp he).1
        simp [len', hne]
      have he0 : len' e₀ = len e₀ - 1 := by simp [len']
      rw [herase, he0] at hsplit'
      omega
    rcases ih len' hpos' hsum' href' with ⟨π₁, href₁, hlen₁⟩
    exact ⟨π₁, href₁, by omega⟩

private def projLit : Literal V → Literal (Fin 4)
  | (Sum.inl v, b) => (v, b)
  | (Sum.inr _, b) => (0, b)

private lemma projLit_negLit (l : Literal V) : projLit (negLit l) = negLit (projLit l) := by
  rcases l with ⟨v | p, b⟩ <;> rfl

private lemma projLit_step_one (e : Fin 6) :
    (stepOf (fun _ => 1) e 0).image projLit = baseC e := by
  simp [stepOf, litOf, negLit, projLit, baseC]

private lemma refutation_one_to_base {π₁ : List (Clause V)}
    (href : IsRefutation (famOf (fun _ => 1)) π₁) :
    ∃ π₀ : List (Clause (Fin 4)), IsRefutation baseSet π₀ ∧ π₀.length ≤ π₁.length := by
  have haux : ∀ π : List (Clause V), IsDerivation (famOf (fun _ => 1)) π →
      ∃ π₀ : List (Clause (Fin 4)),
        IsDerivation baseSet π₀ ∧
        (∀ C ∈ π, ¬ IsTaut (C.image projLit) → ∃ C' ∈ π₀, C' ⊆ C.image projLit) ∧
        π₀.length ≤ π.length := by
    intro π hπ
    induction hπ with
    | nil =>
      exact ⟨[], IsDerivation.nil, fun C hC => by simp at hC, le_rfl⟩
    | @ax π C hπ hC ih =>
      rcases ih with ⟨π₀, hder₀, hmap, hlen⟩
      rcases hC with ⟨e, j, hj, rfl⟩
      dsimp only at hj
      have hj0 : j = 0 := by omega
      subst hj0
      have himg : (stepOf (fun _ => 1) e 0).image projLit = baseC e := projLit_step_one e
      refine ⟨baseC e :: π₀, IsDerivation.ax hder₀ (Finset.mem_image_of_mem baseC (Finset.mem_univ e)),
        ?_, by simp only [List.length_cons]; omega⟩
      intro X hX hXg
      rcases List.mem_cons.mp hX with rfl | hX
      · exact ⟨baseC e, List.mem_cons_self, by rw [himg]⟩
      · rcases hmap X hX hXg with ⟨C', hC'π₀, hsub⟩
        exact ⟨C', List.mem_cons_of_mem _ hC'π₀, hsub⟩
    | @res π C D R hπ hC hD hR ih =>
      rcases ih with ⟨π₀, hder₀, hmap, hlen⟩
      by_cases hgoodR : ¬ IsTaut (R.image projLit)
      · by_cases htC : IsTaut (C.image projLit)
        · have hDsub := taut_parent_left_sub projLit projLit_negLit hR htC hgoodR
          have hgoodD : ¬ IsTaut (D.image projLit) := fun htD => hgoodR (isTaut_mono hDsub htD)
          rcases hmap D hD hgoodD with ⟨D', hD'π₀, hD'sub⟩
          refine ⟨π₀, hder₀, ?_, by simp only [List.length_cons]; omega⟩
          intro X hX hXg
          rcases List.mem_cons.mp hX with rfl | hX
          · exact ⟨D', hD'π₀, hD'sub.trans hDsub⟩
          · exact hmap X hX hXg
        · by_cases htD : IsTaut (D.image projLit)
          · have hCsub := taut_parent_right_sub projLit projLit_negLit hR htD hgoodR
            rcases hmap C hC htC with ⟨C', hC'π₀, hC'sub⟩
            refine ⟨π₀, hder₀, ?_, by simp only [List.length_cons]; omega⟩
            intro X hX hXg
            rcases List.mem_cons.mp hX with rfl | hX
            · exact ⟨C', hC'π₀, hC'sub.trans hCsub⟩
            · exact hmap X hX hXg
          · rcases hmap C hC htC with ⟨C', hC'π₀, hC'sub⟩
            rcases hmap D hD htD with ⟨D', hD'π₀, hD'sub⟩
            rcases good_parents_step projLit projLit_negLit hR hC'sub hD'sub with
              hC'R | hD'R | ⟨R', hR'res, hR'sub⟩
            · refine ⟨π₀, hder₀, ?_, by simp only [List.length_cons]; omega⟩
              intro X hX hXg
              rcases List.mem_cons.mp hX with rfl | hX
              · exact ⟨C', hC'π₀, hC'R⟩
              · exact hmap X hX hXg
            · refine ⟨π₀, hder₀, ?_, by simp only [List.length_cons]; omega⟩
              intro X hX hXg
              rcases List.mem_cons.mp hX with rfl | hX
              · exact ⟨D', hD'π₀, hD'R⟩
              · exact hmap X hX hXg
            · have hder₀R : IsDerivation baseSet (R' :: π₀) := by
                rcases hR'res with h1 | h2
                · exact IsDerivation.res hder₀ hC'π₀ hD'π₀ h1
                · exact IsDerivation.res hder₀ hD'π₀ hC'π₀ h2
              refine ⟨R' :: π₀, hder₀R, ?_, by simp only [List.length_cons]; omega⟩
              intro X hX hXg
              rcases List.mem_cons.mp hX with rfl | hX
              · exact ⟨R', List.mem_cons_self, hR'sub⟩
              · rcases hmap X hX hXg with ⟨E', hE'π₀, hsub⟩
                exact ⟨E', List.mem_cons_of_mem _ hE'π₀, hsub⟩
      · refine ⟨π₀, hder₀, ?_, by simp only [List.length_cons]; omega⟩
        intro X hX hXg
        rcases List.mem_cons.mp hX with rfl | hX
        · exact False.elim (hgoodR hXg)
        · exact hmap X hX hXg
  rcases haux π₁ href.1 with ⟨π₀, hder₀, hmap, hlen⟩
  have hgood0 : ¬ IsTaut ((∅ : Clause V).image projLit) := by
    simpa using not_isTaut_empty (α := Fin 4)
  rcases hmap ∅ href.2 hgood0 with ⟨C', hC'π₀, hsub⟩
  have hC'0 : C' = ∅ := by simpa using hsub
  subst hC'0
  exact ⟨π₀, ⟨hder₀, hC'π₀⟩, hlen⟩

private def IsResSeq (F : Set (Clause (Fin 4))) : List (Clause (Fin 4)) → Prop
  | [] => True
  | R :: tl =>
      (∃ C D, (C ∈ F ∨ C ∈ tl) ∧ (D ∈ F ∨ D ∈ tl) ∧ IsResolvent C D R) ∧ IsResSeq F tl

private lemma extract_resSeq {F : Set (Clause (Fin 4))} {π : List (Clause (Fin 4))}
    (hπ : IsDerivation F π) :
    ∃ (used : Finset (Clause (Fin 4))) (rs : List (Clause (Fin 4))),
      (∀ C ∈ used, C ∈ F) ∧
      IsDerivation (used : Set (Clause (Fin 4))) π ∧
      (∀ C ∈ π, C ∈ used ∨ C ∈ rs) ∧
      used.card + rs.length ≤ π.length ∧
      IsResSeq F rs := by
  induction hπ with
  | nil =>
    exact ⟨∅, [], fun _ h => by simp at h, IsDerivation.nil, fun _ h => by simp at h, by simp, trivial⟩
  | @ax π C hπ hC ih =>
    rcases ih with ⟨used, rs, husedF, hder, hmem, hlen, hrs⟩
    have hsub : (used : Set (Clause (Fin 4))) ⊆ (insert C used : Finset (Clause (Fin 4))) := by
      intro X hX
      exact Finset.mem_insert_of_mem hX
    refine ⟨insert C used, rs, ?_,
      IsDerivation.ax (isDerivation_mono hsub hder) (Finset.mem_insert_self C used),
      ?_, ?_, hrs⟩
    · intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact hC
      · exact husedF X hX
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact Or.inl (Finset.mem_insert_self X used)
      · rcases hmem X hX with h1 | h2
        · exact Or.inl (Finset.mem_insert_of_mem h1)
        · exact Or.inr h2
    · have hcard := Finset.card_insert_le C used
      simp only [List.length_cons]
      omega
  | @res π C D R hπ hC hD hR ih =>
    rcases ih with ⟨used, rs, husedF, hder, hmem, hlen, hrs⟩
    have hC' : C ∈ F ∨ C ∈ rs := by
      rcases hmem C hC with h1 | h2
      · exact Or.inl (husedF C h1)
      · exact Or.inr h2
    have hD' : D ∈ F ∨ D ∈ rs := by
      rcases hmem D hD with h1 | h2
      · exact Or.inl (husedF D h1)
      · exact Or.inr h2
    refine ⟨used, R :: rs, husedF, IsDerivation.res hder hC hD hR, ?_, ?_, ⟨⟨C, D, hC', hD', hR⟩, hrs⟩⟩
    · intro X hX
      rcases List.mem_cons.mp hX with rfl | hX
      · exact Or.inr List.mem_cons_self
      · rcases hmem X hX with h1 | h2
        · exact Or.inl h1
        · exact Or.inr (List.mem_cons_of_mem _ h2)
    · simp only [List.length_cons]
      omega

private lemma suffix_at_empty {F : Set (Clause (Fin 4))} :
    ∀ {rs : List (Clause (Fin 4))}, IsResSeq F rs → (∅ : Clause (Fin 4)) ∈ rs →
    ∃ pre : List (Clause (Fin 4)),
      IsResSeq F ((∅ : Clause (Fin 4)) :: pre) ∧ pre.length + 1 ≤ rs.length := by
  intro rs
  induction rs with
  | nil => intro _ h; simp at h
  | cons R tl ih =>
    intro hrs hmem
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact ⟨tl, hrs, by simp⟩
    · rcases ih hrs.2 htl with ⟨pre, hpre, hlen⟩
      exact ⟨pre, hpre, by simp only [List.length_cons]; omega⟩

private lemma isResolvent_empty {C D : Clause (Fin 4)} (h : IsResolvent C D ∅) :
    ∃ v : Fin 4, C = {(v, true)} ∧ D = {(v, false)} := by
  rcases h with ⟨v, hvC, hvD, heq⟩
  have h1 : C.erase (v, true) = ∅ := by
    have : C.erase (v, true) ⊆ ∅ := by
      rw [heq]; exact Finset.subset_union_left
    exact Finset.subset_empty.mp this
  have h2 : D.erase (v, false) = ∅ := by
    have : D.erase (v, false) ⊆ ∅ := by
      rw [heq]; exact Finset.subset_union_right
    exact Finset.subset_empty.mp this
  refine ⟨v, ?_, ?_⟩
  · ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ C.erase (v, true) := Finset.mem_erase.mpr ⟨hne, hl⟩
      rw [h1] at this
      exact Finset.notMem_empty l this
    · rintro rfl; exact hvC
  · ext l
    simp only [Finset.mem_singleton]
    constructor
    · intro hl
      by_contra hne
      have : l ∈ D.erase (v, false) := Finset.mem_erase.mpr ⟨hne, hl⟩
      rw [h2] at this
      exact Finset.notMem_empty l this
    · rintro rfl; exact hvD

private lemma isResolvent_negUnit_parents_ne {C D : Clause (Fin 4)} {v : Fin 4}
    (h : IsResolvent C D {(v, false)}) :
    C ≠ {(v, true)} ∧ D ≠ {(v, true)} := by
  rcases h with ⟨w, hwC, hwD, heq⟩
  constructor
  · rintro rfl
    have hwv : w = v := by
      have := Finset.mem_singleton.mp hwC
      exact congrArg Prod.fst this
    subst hwv
    have hmem : (w, false) ∈ ({(w, true)} : Clause (Fin 4)).erase (w, true) ∪ D.erase (w, false) := by
      rw [← heq]; exact Finset.mem_singleton_self _
    simp at hmem
  · rintro rfl
    have := Finset.mem_singleton.mp hwD
    exact Bool.false_ne_true (congrArg Prod.snd this)

private lemma isResolvent_posUnit_parents_ne {C D : Clause (Fin 4)} {v : Fin 4}
    (h : IsResolvent C D {(v, true)}) :
    C ≠ {(v, false)} ∧ D ≠ {(v, false)} := by
  rcases h with ⟨w, hwC, hwD, heq⟩
  constructor
  · rintro rfl
    have := Finset.mem_singleton.mp hwC
    exact Bool.false_ne_true (congrArg Prod.snd this).symm
  · rintro rfl
    have hwv : w = v := by
      have := Finset.mem_singleton.mp hwD
      exact congrArg Prod.fst this
    subst hwv
    have hmem : (w, true) ∈ C.erase (w, true) ∪ ({(w, false)} : Clause (Fin 4)).erase (w, false) := by
      rw [← heq]; exact Finset.mem_singleton_self _
    simp at hmem

private def baseList : List (Clause (Fin 4)) :=
  [baseC 0, baseC 1, baseC 2, baseC 3, baseC 4, baseC 5]

private lemma mem_baseList_of_mem_baseSet {C : Clause (Fin 4)} (h : C ∈ baseSet) :
    C ∈ baseList := by
  rcases Finset.mem_image.mp h with ⟨e, _, rfl⟩
  fin_cases e <;> simp [baseList]

private def partner : Fin 4 → Fin 4 := ![1, 0, 3, 2]

private def symFwd (a b : Fin 4) (x : Fin 4) : Fin 4 :=
  if x = a then 0 else if x = partner a then 1 else if x = partner b then 2 else 3

private def symInv (a b : Fin 4) (x : Fin 4) : Fin 4 :=
  if x = 0 then a else if x = 1 then partner a else if x = 2 then partner b else b

private def mapClause4 (f : Fin 4 → Fin 4) (C : Clause (Fin 4)) : Clause (Fin 4) :=
  C.image (fun l => (f l.1, l.2))

private lemma sym_bijective :
    ∀ a b : Fin 4, a.val / 2 ≠ b.val / 2 →
      ∀ x : Fin 4, symFwd a b (symInv a b x) = x ∧ symInv a b (symFwd a b x) = x := by
  decide

private lemma sym_preserves_baseFin :
    ∀ a b : Fin 4, a.val / 2 ≠ b.val / 2 →
      baseFin.image (mapClause4 (symFwd a b)) = baseFin := by
  decide

private lemma mapClause4_resolvent {f : Fin 4 → Fin 4} (hf : Function.Bijective f)
    {C D R : Clause (Fin 4)} (hR : IsResolvent C D R) :
    IsResolvent (mapClause4 f C) (mapClause4 f D) (mapClause4 f R) := by
  rcases hR with ⟨v, hvC, hvD, rfl⟩
  have hinj : Function.Injective (fun l : Literal (Fin 4) => (f l.1, l.2)) := by
    intro l₁ l₂ h
    rcases l₁ with ⟨x₁, b₁⟩
    rcases l₂ with ⟨x₂, b₂⟩
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact Prod.ext (hf.1 h1) h2
  refine ⟨f v, Finset.mem_image.mpr ⟨(v, true), hvC, rfl⟩,
    Finset.mem_image.mpr ⟨(v, false), hvD, rfl⟩, ?_⟩
  simp only [mapClause4, Finset.image_union, Finset.image_erase hinj]

private lemma mapClause4_isResSeq {f : Fin 4 → Fin 4} (hf : Function.Bijective f)
    (hF : baseFin.image (mapClause4 f) = baseFin) :
    ∀ {rs : List (Clause (Fin 4))}, IsResSeq baseSet rs →
      IsResSeq baseSet (rs.map (mapClause4 f)) := by
  intro rs
  induction rs with
  | nil => intro _; trivial
  | cons R tl ih =>
    intro hrs
    rcases hrs with ⟨⟨C, D, hC, hD, hR⟩, htl⟩
    have hmem : ∀ X, (X ∈ baseSet ∨ X ∈ tl) →
        mapClause4 f X ∈ baseSet ∨ mapClause4 f X ∈ tl.map (mapClause4 f) := by
      intro X hX
      rcases hX with h1 | h2
      · left
        change mapClause4 f X ∈ baseFin
        rw [← hF]
        exact Finset.mem_image_of_mem _ h1
      · right
        exact List.mem_map_of_mem h2
    exact ⟨⟨mapClause4 f C, mapClause4 f D, hmem C hC, hmem D hD, mapClause4_resolvent hf hR⟩,
      ih htl⟩

private def r1Can : Clause (Fin 4) := {(0, true), (3, false)}

private def p1CanList : List (Clause (Fin 4)) := r1Can :: baseList

private def p2CanList : List (Clause (Fin 4)) := {(0, true)} :: p1CanList

private def cand2List : List (Clause (Fin 4)) :=
  [{(0, true)}, {(0, false), (2, true)}, {(0, false), (3, true)}, {(0, true), (1, true)},
   {(0, true), (2, false)}, {(0, true), (3, false)}, {(1, false), (2, true)},
   {(1, false), (3, false)}, {(1, false), (3, true)}, {(1, true), (2, false)},
   {(1, true), (3, false)}]

private def cand3List : List (Clause (Fin 4)) :=
  [{(0, true)}, {(1, false)}, {(0, false), (2, true)}, {(0, false), (3, true)},
   {(0, true), (1, true)}, {(0, true), (2, false)}, {(0, true), (3, false)},
   {(1, false), (2, true)}, {(1, false), (3, false)}, {(1, false), (3, true)},
   {(1, true), (2, false)}, {(1, true), (3, false)}]

private abbrev isResExt (C D R : Clause (Fin 4)) (v : Fin 4) : Prop :=
  (v, true) ∈ C ∧ (v, false) ∈ D ∧
  ∀ l : Literal (Fin 4), l ∈ R ↔ (l ∈ C ∧ l ≠ (v, true)) ∨ (l ∈ D ∧ l ≠ (v, false))

private lemma isResExt_of_resolvent {C D R : Clause (Fin 4)} {v : Fin 4}
    (hvC : (v, true) ∈ C) (hvD : (v, false) ∈ D)
    (heq : R = C.erase (v, true) ∪ D.erase (v, false)) : isResExt C D R v := by
  refine ⟨hvC, hvD, fun l => ?_⟩
  rw [heq]
  simp only [Finset.mem_union, Finset.mem_erase]
  tauto

private lemma eq_of_isResExt {C D R₁ R₂ : Clause (Fin 4)} {v : Fin 4}
    (h₁ : isResExt C D R₁ v) (h₂ : isResExt C D R₂ v) : R₁ = R₂ := by
  ext l
  exact (h₁.2.2 l).trans (h₂.2.2 l).symm

private def isResB (C D R : Clause (Fin 4)) (v : Fin 4) : Bool :=
  decide ((v, true) ∈ C) && decide ((v, false) ∈ D) &&
  (List.finRange 4).all fun w =>
    [false, true].all fun p =>
      let l : Literal (Fin 4) := (w, p)
      decide (l ∈ R) ==
        ((decide (l ∈ C) && decide (l ≠ (v, true))) ||
         (decide (l ∈ D) && decide (l ≠ (v, false))))

private lemma isResB_iff (C D R : Clause (Fin 4)) (v : Fin 4) :
    isResB C D R v = true ↔ isResExt C D R v := by
  simp only [isResB, isResExt, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, List.mem_cons, List.not_mem_nil, or_false, beq_iff_eq,
    forall_true_left]
  constructor
  · rintro ⟨⟨h1, h2⟩, hall⟩
    refine ⟨h1, h2, fun l => ?_⟩
    rcases l with ⟨w, p⟩
    have hp : p = false ∨ p = true := by cases p <;> simp
    have h := hall w p hp
    have hiff : decide ((w, p) ∈ R) = true ↔
        (((decide ((w, p) ∈ C) && decide ((w, p) ≠ (v, true))) ||
          (decide ((w, p) ∈ D) && decide ((w, p) ≠ (v, false)))) = true) := by
      rw [h]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hiff
    tauto
  · rintro ⟨h1, h2, hall⟩
    refine ⟨⟨h1, h2⟩, fun w p _ => ?_⟩
    have h := hall (w, p)
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    tauto

private lemma s1_mem_canon_b :
    baseList.all (fun C => baseList.all (fun D => (List.finRange 4).all (fun v =>
      !(decide ((v, true) ∈ C) && decide ((v, false) ∈ D)) ||
      (List.finRange 4).any (fun a => (List.finRange 4).any (fun b =>
        decide (a.val / 2 ≠ b.val / 2) && isResB C D {(a, true), (b, false)} v))))) = true := by
  decide

private lemma s1_mem_canon :
    ∀ C ∈ baseList, ∀ D ∈ baseList, ∀ v : Fin 4,
      (v, true) ∈ C → (v, false) ∈ D →
      ∃ a b : Fin 4, a.val / 2 ≠ b.val / 2 ∧ isResExt C D {(a, true), (b, false)} v := by
  intro C hC D hD v hvC hvD
  have h := s1_mem_canon_b
  simp only [List.all_eq_true, List.any_eq_true, List.mem_finRange, true_and,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_true,
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h C hC D hD v trivial with (hbad | hbad) | ⟨a, b, hab, hres⟩
  · exact False.elim (hbad hvC)
  · exact False.elim (hbad hvD)
  · exact ⟨a, b, hab, (isResB_iff _ _ _ _).mp hres⟩

private lemma sym_maps_r1 :
    ∀ a b : Fin 4, a.val / 2 ≠ b.val / 2 →
      mapClause4 (symFwd a b) {(a, true), (b, false)} = r1Can := by
  decide

private lemma baseFin_card : baseFin.card = 6 := by decide

private lemma empty_not_mem_baseFin : (∅ : Clause (Fin 4)) ∉ baseFin := by decide

private lemma unit_not_mem_baseFin :
    ∀ (v : Fin 4) (b : Bool), ({(v, b)} : Clause (Fin 4)) ∉ baseFin := by
  decide

private lemma r1Can_not_unit :
    ∀ (v : Fin 4) (b : Bool), r1Can ≠ {(v, b)} := by
  decide

private lemma p1_res_mem_cand2_b :
    p1CanList.all (fun C => p1CanList.all (fun D => (List.finRange 4).all (fun v =>
      !(decide ((v, true) ∈ C) && decide ((v, false) ∈ D)) ||
      cand2List.any (fun R => isResB C D R v)))) = true := by
  decide

private lemma p1_res_mem_cand2 :
    ∀ C ∈ p1CanList, ∀ D ∈ p1CanList, ∀ v : Fin 4,
      (v, true) ∈ C → (v, false) ∈ D →
      ∃ R ∈ cand2List, isResExt C D R v := by
  intro C hC D hD v hvC hvD
  have h := p1_res_mem_cand2_b
  simp only [List.all_eq_true, List.any_eq_true, List.mem_finRange,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_true,
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h C hC D hD v trivial with (hbad | hbad) | ⟨R, hRmem, hres⟩
  · exact False.elim (hbad hvC)
  · exact False.elim (hbad hvD)
  · exact ⟨R, hRmem, (isResB_iff _ _ _ _).mp hres⟩

private lemma cand2_no_negUnit_and_unique_posUnit :
    ∀ b ∈ cand2List,
      (∀ v : Fin 4, ¬ ∀ l : Literal (Fin 4), l ∈ b ↔ l = (v, false)) ∧
      (∀ v : Fin 4, (∀ l : Literal (Fin 4), l ∈ b ↔ l = (v, true)) → v = 0) := by
  decide

private lemma cand2_ne_negUnit {b : Clause (Fin 4)} (hb : b ∈ cand2List) (v : Fin 4) :
    b ≠ {(v, false)} := by
  intro heq
  exact (cand2_no_negUnit_and_unique_posUnit b hb).1 v (fun l => by rw [heq]; exact Finset.mem_singleton)

private lemma cand2_eq_posUnit_zero {b : Clause (Fin 4)} (hb : b ∈ cand2List) (v : Fin 4)
    (heq : b = {(v, true)}) : v = 0 :=
  (cand2_no_negUnit_and_unique_posUnit b hb).2 v (fun l => by rw [heq]; exact Finset.mem_singleton)

private lemma p1_step3_negUnit_b :
    cand2List.all (fun b => (b :: p1CanList).all (fun C => (b :: p1CanList).all (fun D =>
      (List.finRange 4).all (fun w => (List.finRange 4).all (fun v =>
        !isResB C D {(v, false)} w ||
        (((List.finRange 4).all (fun x => [false, true].all (fun p =>
          decide ((x, p) ∈ b) == decide ((x, p) = ((0 : Fin 4), true))))) &&
         decide (v = 1))))))) = true := by
  decide

private lemma p1_step3_negUnit :
    ∀ b ∈ cand2List, ∀ C ∈ b :: p1CanList, ∀ D ∈ b :: p1CanList, ∀ w v : Fin 4,
      isResExt C D {(v, false)} w →
      (∀ l : Literal (Fin 4), l ∈ b ↔ l = (0, true)) ∧ v = 1 := by
  intro b hb C hC D hD w v hres
  have h := p1_step3_negUnit_b
  simp only [List.all_eq_true, List.mem_finRange, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, forall_true_left] at h
  have hresB : isResB C D {(v, false)} w = true := (isResB_iff _ _ _ _).mpr hres
  rcases h b hb C hC D hD w v with hbad | ⟨hbext, hv1⟩
  · rw [hresB] at hbad; exact False.elim (Bool.false_ne_true hbad.symm)
  · refine ⟨fun l => ?_, hv1⟩
    rcases l with ⟨x, p⟩
    have hp : p ∈ ([false, true] : List Bool) := by cases p <;> simp
    have hx := hbext x p hp
    have hiff : decide ((x, p) ∈ b) = true ↔ decide ((x, p) = ((0 : Fin 4), true)) = true := by
      rw [hx]
    simpa [decide_eq_true_eq] using hiff

private lemma p2_no_pos1 :
    ∀ C ∈ p2CanList, ∀ D ∈ p2CanList, ∀ w : Fin 4,
      ¬ isResExt C D {(1, true)} w := by
  decide

private lemma p2_res_mem_cand3_b :
    p2CanList.all (fun C => p2CanList.all (fun D => (List.finRange 4).all (fun w =>
      !(decide ((w, true) ∈ C) && decide ((w, false) ∈ D)) ||
      cand3List.any (fun R => isResB C D R w)))) = true := by
  decide

private lemma p2_res_mem_cand3 :
    ∀ C ∈ p2CanList, ∀ D ∈ p2CanList, ∀ w : Fin 4,
      (w, true) ∈ C → (w, false) ∈ D →
      ∃ R ∈ cand3List, isResExt C D R w := by
  intro C hC D hD w hwC hwD
  have h := p2_res_mem_cand3_b
  simp only [List.all_eq_true, List.any_eq_true, List.mem_finRange,
    Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, Bool.and_eq_true,
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  rcases h C hC D hD w trivial with (hbad | hbad) | ⟨R, hRmem, hres⟩
  · exact False.elim (hbad hwC)
  · exact False.elim (hbad hwD)
  · exact ⟨R, hRmem, (isResB_iff _ _ _ _).mp hres⟩

private lemma p2_step4_no_neg0 :
    ∀ c ∈ cand3List, ∀ C ∈ c :: p2CanList, ∀ D ∈ c :: p2CanList, ∀ w : Fin 4,
      ¬ isResExt C D {(0, false)} w := by
  decide

private lemma check1_p1_list {b : Clause (Fin 4)} (hb : b ∈ cand2List) (v : Fin 4)
    {C₁ D₁ : Clause (Fin 4)} (hC₁ : C₁ ∈ b :: p1CanList) (hD₁ : D₁ ∈ b :: p1CanList)
    (hR₁ : IsResolvent C₁ D₁ {(v, false)})
    (hpos : b = {(v, true)} ∨ ∃ C₂ D₂, C₂ ∈ b :: p1CanList ∧ D₂ ∈ b :: p1CanList ∧
      IsResolvent C₂ D₂ {(v, true)}) : False := by
  rcases hR₁ with ⟨w₁, hw₁C, hw₁D, heq₁⟩
  rcases p1_step3_negUnit b hb C₁ hC₁ D₁ hD₁ w₁ v (isResExt_of_resolvent hw₁C hw₁D heq₁) with ⟨hb0_ext, rfl⟩
  have hb0 : b = {(0, true)} := by
    ext l
    simp only [Finset.mem_singleton]
    exact hb0_ext l
  rcases hpos with hb1 | ⟨C₂, D₂, hC₂, hD₂, w₂, hw₂C, hw₂D, heq₂⟩
  · have heq := hb0.symm.trans hb1
    have hmem : ((0 : Fin 4), true) ∈ ({((1 : Fin 4), true)} : Clause (Fin 4)) := by
      rw [← heq]; exact Finset.mem_singleton_self _
    simp at hmem
  · rw [hb0] at hC₂ hD₂
    exact p2_no_pos1 C₂ hC₂ D₂ hD₂ w₂ (isResExt_of_resolvent hw₂C hw₂D heq₂)

private lemma no_short_pair_canon (pre : List (Clause (Fin 4))) (hlen : pre.length ≤ 4)
    (hrs : IsResSeq baseSet pre) (v : Fin 4)
    (hpos : {(v, true)} ∈ pre) (hneg : {(v, false)} ∈ pre) : False := by
  match pre with
  | [] => simp at hpos
  | [a] =>
    simp only [List.mem_singleton] at hpos hneg
    have heq := hpos.trans hneg.symm
    have hmem : (v, true) ∈ ({(v, false)} : Clause (Fin 4)) := by
      rw [← heq]; exact Finset.mem_singleton_self _
    simp at hmem
  | [b, a] =>
    rcases hrs with ⟨_, ⟨⟨C, D, hC, hD, w, hwC, hwD, ha_eq⟩, _⟩⟩
    have hC' : C ∈ baseList := mem_baseList_of_mem_baseSet (by simpa using hC)
    have hD' : D ∈ baseList := mem_baseList_of_mem_baseSet (by simpa using hD)
    rcases s1_mem_canon C hC' D hD' w hwC hwD with ⟨x, y, hxy, hxy_ext⟩
    have ha_form : a = {(x, true), (y, false)} :=
      eq_of_isResExt (isResExt_of_resolvent hwC hwD ha_eq) hxy_ext
    have hane : ∀ u p, a ≠ {(u, p)} := by
      intro u p heq
      have hm := congrArg (mapClause4 (symFwd x y)) (ha_form.symm.trans heq)
      rw [sym_maps_r1 x y hxy] at hm
      exact r1Can_not_unit (symFwd x y u) p (by simpa [mapClause4] using hm)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpos hneg
    have hbpos : {(v, true)} = b := by
      rcases hpos with h1 | h2
      · exact h1
      · exact False.elim (hane v true h2.symm)
    have hbneg : {(v, false)} = b := by
      rcases hneg with h1 | h2
      · exact h1
      · exact False.elim (hane v false h2.symm)
    have heq := hbpos.trans hbneg.symm
    have hmem : (v, true) ∈ ({(v, false)} : Clause (Fin 4)) := by
      rw [← heq]; exact Finset.mem_singleton_self _
    simp at hmem
  | [c, b, a] =>
    rcases hrs with ⟨⟨Cc, Dc, hCc, hDc, hRc⟩, ⟨⟨Cb, Db, hCb, hDb, hRb⟩,
      ⟨⟨Ca, Da, hCa, hDa, wa, hwaC, hwaD, ha_eq⟩, _⟩⟩⟩
    have hCa' : Ca ∈ baseList := mem_baseList_of_mem_baseSet (by simpa using hCa)
    have hDa' : Da ∈ baseList := mem_baseList_of_mem_baseSet (by simpa using hDa)
    rcases s1_mem_canon Ca hCa' Da hDa' wa hwaC hwaD with ⟨x, y, hxy, hxy_ext⟩
    have ha_form : a = {(x, true), (y, false)} :=
      eq_of_isResExt (isResExt_of_resolvent hwaC hwaD ha_eq) hxy_ext
    subst ha_form
    let f := symFwd x y
    have hbij : Function.Bijective f :=
      Function.bijective_iff_has_inverse.mpr ⟨symInv x y, fun z => (sym_bijective x y hxy z).2,
        fun z => (sym_bijective x y hxy z).1⟩
    have hF := sym_preserves_baseFin x y hxy
    have hfa : mapClause4 f {(x, true), (y, false)} = r1Can := sym_maps_r1 x y hxy
    have hseq' := mapClause4_isResSeq hbij hF (rs := [c, b, {(x, true), (y, false)}])
      ⟨⟨Cc, Dc, hCc, hDc, hRc⟩, ⟨⟨Cb, Db, hCb, hDb, hRb⟩,
        ⟨⟨Ca, Da, hCa, hDa, ⟨wa, hwaC, hwaD, ha_eq⟩⟩, trivial⟩⟩⟩
    simp only [List.map_cons, List.map_nil, hfa] at hseq'
    rcases hseq' with ⟨⟨Cc', Dc', hCc', hDc', hRc'⟩, ⟨⟨Cb', Db', hCb', hDb', hRb'⟩, _⟩⟩
    set b' := mapClause4 f b
    set c' := mapClause4 f c
    set v' := f v
    have hCb_in : Cb' ∈ p1CanList := by
      rcases hCb' with h1 | h2
      · exact List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1)
      · rw [List.mem_singleton.mp h2]; exact List.mem_cons_self
    have hDb_in : Db' ∈ p1CanList := by
      rcases hDb' with h1 | h2
      · exact List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1)
      · rw [List.mem_singleton.mp h2]; exact List.mem_cons_self
    have hb' : b' ∈ cand2List := by
      rcases hRb' with ⟨w, hwC, hwD, heq⟩
      rcases p1_res_mem_cand2 Cb' hCb_in Db' hDb_in w hwC hwD with ⟨R, hRmem, hRext⟩
      have hb_eq : b' = R := eq_of_isResExt (isResExt_of_resolvent hwC hwD heq) hRext
      rwa [hb_eq]
    have hCc_in : Cc' ∈ b' :: p1CanList := by
      rcases hCc' with h1 | h2
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hDc_in : Dc' ∈ b' :: p1CanList := by
      rcases hDc' with h1 | h2
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hpos' : {(v', true)} ∈ ([c', b', r1Can] : List (Clause (Fin 4))) := by
      have hm := List.mem_map_of_mem (f := mapClause4 f) hpos
      simp only [List.map_cons, List.map_nil, hfa] at hm
      have hunit : mapClause4 f {(v, true)} = {(v', true)} := by simp [mapClause4, v']
      rwa [hunit] at hm
    have hneg' : {(v', false)} ∈ ([c', b', r1Can] : List (Clause (Fin 4))) := by
      have hm := List.mem_map_of_mem (f := mapClause4 f) hneg
      simp only [List.map_cons, List.map_nil, hfa] at hm
      have hunit : mapClause4 f {(v, false)} = {(v', false)} := by simp [mapClause4, v']
      rwa [hunit] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpos' hneg'
    have hneg_eq : c' = {(v', false)} := by
      rcases hneg' with h1 | h2 | h3
      · exact h1.symm
      · exact False.elim (cand2_ne_negUnit hb' v' h2.symm)
      · exact False.elim (r1Can_not_unit v' false h3.symm)
    have hpos_eq : b' = {(v', true)} := by
      rcases hpos' with h1 | h2 | h3
      · exfalso
        have heq := h1.trans hneg_eq
        have hm : (v', true) ∈ ({(v', false)} : Clause (Fin 4)) := by
          rw [← heq]; exact Finset.mem_singleton_self _
        simp at hm
      · exact h2.symm
      · exact False.elim (r1Can_not_unit v' true h3.symm)
    have hRc'' : IsResolvent Cc' Dc' {(v', false)} := by rwa [← hneg_eq]
    exact check1_p1_list hb' v' hCc_in hDc_in hRc'' (Or.inl hpos_eq)
  | [d, c, b, a] =>
    rcases hrs with ⟨⟨Cd, Dd, hCd, hDd, hRd⟩, ⟨⟨Cc, Dc, hCc, hDc, hRc⟩,
      ⟨⟨Cb, Db, hCb, hDb, hRb⟩, ⟨⟨Ca, Da, hCa, hDa, wa, hwaC, hwaD, ha_eq⟩, _⟩⟩⟩⟩
    have hCa' : Ca ∈ baseList := mem_baseList_of_mem_baseSet (by simpa using hCa)
    have hDa' : Da ∈ baseList := mem_baseList_of_mem_baseSet (by simpa using hDa)
    rcases s1_mem_canon Ca hCa' Da hDa' wa hwaC hwaD with ⟨x, y, hxy, hxy_ext⟩
    have ha_form : a = {(x, true), (y, false)} :=
      eq_of_isResExt (isResExt_of_resolvent hwaC hwaD ha_eq) hxy_ext
    subst ha_form
    let f := symFwd x y
    have hbij : Function.Bijective f :=
      Function.bijective_iff_has_inverse.mpr ⟨symInv x y, fun z => (sym_bijective x y hxy z).2,
        fun z => (sym_bijective x y hxy z).1⟩
    have hF := sym_preserves_baseFin x y hxy
    have hfa : mapClause4 f {(x, true), (y, false)} = r1Can := sym_maps_r1 x y hxy
    have hseq' := mapClause4_isResSeq hbij hF (rs := [d, c, b, {(x, true), (y, false)}])
      ⟨⟨Cd, Dd, hCd, hDd, hRd⟩, ⟨⟨Cc, Dc, hCc, hDc, hRc⟩,
        ⟨⟨Cb, Db, hCb, hDb, hRb⟩, ⟨⟨Ca, Da, hCa, hDa, ⟨wa, hwaC, hwaD, ha_eq⟩⟩, trivial⟩⟩⟩⟩
    simp only [List.map_cons, List.map_nil, hfa] at hseq'
    rcases hseq' with ⟨⟨Cd', Dd', hCd', hDd', hRd'⟩, ⟨⟨Cc', Dc', hCc', hDc', hRc'⟩,
      ⟨⟨Cb', Db', hCb', hDb', hRb'⟩, _⟩⟩⟩
    set b' := mapClause4 f b
    set c' := mapClause4 f c
    set d' := mapClause4 f d
    set v' := f v
    have hCb_in : Cb' ∈ p1CanList := by
      rcases hCb' with h1 | h2
      · exact List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1)
      · rw [List.mem_singleton.mp h2]; exact List.mem_cons_self
    have hDb_in : Db' ∈ p1CanList := by
      rcases hDb' with h1 | h2
      · exact List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1)
      · rw [List.mem_singleton.mp h2]; exact List.mem_cons_self
    have hb' : b' ∈ cand2List := by
      rcases hRb' with ⟨w, hwC, hwD, heq⟩
      rcases p1_res_mem_cand2 Cb' hCb_in Db' hDb_in w hwC hwD with ⟨R, hRmem, hRext⟩
      have hb_eq : b' = R := eq_of_isResExt (isResExt_of_resolvent hwC hwD heq) hRext
      rwa [hb_eq]
    have hCc_in : Cc' ∈ b' :: p1CanList := by
      rcases hCc' with h1 | h2
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hDc_in : Dc' ∈ b' :: p1CanList := by
      rcases hDc' with h1 | h2
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
        rcases h2 with rfl | rfl
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ List.mem_cons_self
    have hpos' : {(v', true)} ∈ ([d', c', b', r1Can] : List (Clause (Fin 4))) := by
      have hm := List.mem_map_of_mem (f := mapClause4 f) hpos
      simp only [List.map_cons, List.map_nil, hfa] at hm
      have hunit : mapClause4 f {(v, true)} = {(v', true)} := by simp [mapClause4, v']
      rwa [hunit] at hm
    have hneg' : {(v', false)} ∈ ([d', c', b', r1Can] : List (Clause (Fin 4))) := by
      have hm := List.mem_map_of_mem (f := mapClause4 f) hneg
      simp only [List.map_cons, List.map_nil, hfa] at hm
      have hunit : mapClause4 f {(v, false)} = {(v', false)} := by simp [mapClause4, v']
      rwa [hunit] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpos' hneg'
    have hne_pn : ({(v', true)} : Clause (Fin 4)) ≠ {(v', false)} := by
      intro heq
      have hm : (v', true) ∈ ({(v', false)} : Clause (Fin 4)) := by
        rw [← heq]; exact Finset.mem_singleton_self _
      simp at hm
    have hneg_cd : {(v', false)} = d' ∨ {(v', false)} = c' := by
      rcases hneg' with h1 | h2 | h3 | h4
      · exact Or.inl h1
      · exact Or.inr h2
      · exact False.elim (cand2_ne_negUnit hb' v' h3.symm)
      · exact False.elim (r1Can_not_unit v' false h4.symm)
    by_cases hbp : b' = {(v', true)}
    · have hv0 : v' = 0 := cand2_eq_posUnit_zero hb' v' hbp
      have hbp0 : b' = {(0, true)} := by rwa [hv0] at hbp
      rcases hneg_cd with hd_eq | hc_eq
      · have hd0 : d' = {(0, false)} := by rw [← hd_eq, hv0]
        have hc2 : c' ∈ cand3List := by
          rcases hRc' with ⟨w, hwC, hwD, heq⟩
          rw [hbp0] at hCc_in hDc_in
          rcases p2_res_mem_cand3 Cc' hCc_in Dc' hDc_in w hwC hwD with ⟨R, hRmem, hRext⟩
          have hc_eq' : c' = R := eq_of_isResExt (isResExt_of_resolvent hwC hwD heq) hRext
          rwa [hc_eq']
        have hCd_in : Cd' ∈ c' :: p2CanList := by
          rcases hCd' with h1 | h2
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1)))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl | rfl
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (by rw [hbp0]; exact List.mem_cons_self)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have hDd_in : Dd' ∈ c' :: p2CanList := by
          rcases hDd' with h1 | h2
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1)))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl | rfl
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (by rw [hbp0]; exact List.mem_cons_self)
            · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
        rcases hRd' with ⟨w, hwC, hwD, heq⟩
        exact p2_step4_no_neg0 c' hc2 Cd' hCd_in Dd' hDd_in w
          (isResExt_of_resolvent hwC hwD (hd0.symm.trans heq))
      · have hRc'' : IsResolvent Cc' Dc' {(v', false)} := by rwa [hc_eq]
        exact check1_p1_list hb' v' hCc_in hDc_in hRc'' (Or.inl hbp)
    · have hpos_cd : {(v', true)} = d' ∨ {(v', true)} = c' := by
        rcases hpos' with h1 | h2 | h3 | h4
        · exact Or.inl h1
        · exact Or.inr h2
        · exact False.elim (hbp h3.symm)
        · exact False.elim (r1Can_not_unit v' true h4.symm)
      rcases hneg_cd with hd_eq | hc_eq
      · have hc_eq : {(v', true)} = c' := by
          rcases hpos_cd with h1 | h2
          · exact False.elim (hne_pn (h1.trans hd_eq.symm))
          · exact h2
        have hRd'' : IsResolvent Cd' Dd' {(v', false)} := by rwa [hd_eq]
        have hRc'' : IsResolvent Cc' Dc' {(v', true)} := by rwa [hc_eq]
        have hpar := isResolvent_negUnit_parents_ne hRd''
        have hCd_in : Cd' ∈ b' :: p1CanList := by
          rcases hCd' with h1 | h2
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl | rfl
            · exact False.elim (hpar.1 hc_eq.symm)
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
        have hDd_in : Dd' ∈ b' :: p1CanList := by
          rcases hDd' with h1 | h2
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl | rfl
            · exact False.elim (hpar.2 hc_eq.symm)
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
        exact check1_p1_list hb' v' hCd_in hDd_in hRd'' (Or.inr ⟨Cc', Dc', hCc_in, hDc_in, hRc''⟩)
      · have hd_eq : {(v', true)} = d' := by
          rcases hpos_cd with h1 | h2
          · exact h1
          · exact False.elim (hne_pn (h2.trans hc_eq.symm))
        have hRd'' : IsResolvent Cd' Dd' {(v', true)} := by rwa [hd_eq]
        have hRc'' : IsResolvent Cc' Dc' {(v', false)} := by rwa [hc_eq]
        have hpar := isResolvent_posUnit_parents_ne hRd''
        have hCd_in : Cd' ∈ b' :: p1CanList := by
          rcases hCd' with h1 | h2
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl | rfl
            · exact False.elim (hpar.1 hc_eq.symm)
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
        have hDd_in : Dd' ∈ b' :: p1CanList := by
          rcases hDd' with h1 | h2
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (mem_baseList_of_mem_baseSet h1))
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
            rcases h2 with rfl | rfl | rfl
            · exact False.elim (hpar.2 hc_eq.symm)
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ List.mem_cons_self
        exact check1_p1_list hb' v' hCc_in hDc_in hRc'' (Or.inr ⟨Cd', Dd', hCd_in, hDd_in, hRd''⟩)
  | _ :: _ :: _ :: _ :: _ :: _ =>
    simp only [List.length_cons] at hlen
    omega

private lemma base_refutation_ge_12 {π₀ : List (Clause (Fin 4))} (href : IsRefutation baseSet π₀) :
    12 ≤ π₀.length := by
  rcases extract_resSeq href.1 with ⟨used, rs, husedF, hder, hmem, hlen, hrs⟩
  have hused_eq : used = baseFin := by
    apply Finset.Subset.antisymm
    · intro C hC; exact husedF C hC
    · intro C hC
      rcases Finset.mem_image.mp hC with ⟨e₀, _, rfl⟩
      by_contra hnot
      have hsat : Satisfiable (used : Set (Clause (Fin 4))) := by
        refine ⟨baseWitness e₀, ?_⟩
        intro X hX
        have hXbase : X ∈ baseFin := husedF X hX
        rcases Finset.mem_image.mp hXbase with ⟨e, _, rfl⟩
        have hne : e ≠ e₀ := fun heq => hnot (heq ▸ hX)
        exact (baseWitness_spec e₀ e).2 hne
      exact not_isRefutation_of_satisfiable hsat ⟨hder, href.2⟩
  have hcard : used.card = 6 := by rw [hused_eq, baseFin_card]
  have h0rs : (∅ : Clause (Fin 4)) ∈ rs := by
    rcases hmem ∅ href.2 with h1 | h2
    · rw [hused_eq] at h1
      exact False.elim (empty_not_mem_baseFin h1)
    · exact h2
  rcases suffix_at_empty hrs h0rs with ⟨pre, hpre, hprelen⟩
  rcases hpre with ⟨⟨C, D, hC, hD, hR⟩, hpre_seq⟩
  rcases isResolvent_empty hR with ⟨v, rfl, rfl⟩
  have hpos : ({(v, true)} : Clause (Fin 4)) ∈ pre := by
    rcases hC with h1 | h2
    · exact False.elim (unit_not_mem_baseFin v true h1)
    · exact h2
  have hneg : ({(v, false)} : Clause (Fin 4)) ∈ pre := by
    rcases hD with h1 | h2
    · exact False.elim (unit_not_mem_baseFin v false h1)
    · exact h2
  have h5 : 5 ≤ pre.length := by
    by_contra hlt
    exact no_short_pair_canon pre (by omega) hpre_seq v hpos hneg
  omega

private lemma shared_lower_bound (t : ℕ) (ht : 0 < t) {π : List (Clause V)}
    (href : IsRefutation (famOf (fun _ => t)) π) : 12 * t ≤ π.length := by
  have hsum : (∑ _ : Fin 6, (t - 1)) = 6 * (t - 1) := by
    simp [Finset.sum_const, Finset.card_fin]
  rcases contract_to_one (6 * (t - 1)) (fun _ => t) (fun _ => ht) hsum href with
    ⟨π₁, href₁, hlen₁⟩
  rcases refutation_one_to_base href₁ with ⟨π₀, href₀, hlen₀⟩
  have h12 := base_refutation_ge_12 href₀
  omega

private def subJ (t : ℕ) (J : Fin 6 → Fin t) : Literal V → Literal (Fin 4)
  | (Sum.inl v, b) => (v, b)
  | (Sum.inr (e, j), b) =>
      if j ≤ (J e).val then ((src e).1, if b then (src e).2 else !(src e).2)
      else ((dst e).1, if b then (dst e).2 else !(dst e).2)

private lemma subJ_negLit (t : ℕ) (J : Fin 6 → Fin t) (l : Literal V) :
    subJ t J (negLit l) = negLit (subJ t J l) := by
  rcases l with ⟨v | ⟨e, j⟩, b⟩
  · rfl
  · by_cases h : j ≤ (J e).val <;> cases b <;> simp [subJ, negLit, h]

private lemma subJ_litOf (t : ℕ) (J : Fin 6 → Fin t) (e : Fin 6) (m : ℕ) (hm : m ≤ t) :
    subJ t J (litOf (fun _ => t) e m) = if m ≤ (J e).val then src e else dst e := by
  dsimp only [litOf]
  by_cases h0 : m = 0
  · rw [if_pos h0]
    simp [subJ, h0]
  · rw [if_neg h0]
    by_cases ht : m = t
    · rw [if_pos ht]
      have hgt : ¬(t ≤ (J e).val) := by have := (J e).isLt; omega
      simp [subJ, ht, hgt]
    · rw [if_neg ht]
      by_cases h : m ≤ (J e).val <;> simp [subJ, h]

private lemma subJ_stepOf_eq (t : ℕ) (J : Fin 6 → Fin t) (e : Fin 6) :
    (stepOf (fun _ => t) e (J e).val).image (subJ t J) = baseC e := by
  have h1 : subJ t J (negLit (litOf (fun _ => t) e (J e).val)) = negLit (src e) := by
    rw [subJ_negLit, subJ_litOf t J e (J e).val (by have := (J e).isLt; omega)]
    simp
  have h2 : subJ t J (litOf (fun _ => t) e ((J e).val + 1)) = dst e := by
    rw [subJ_litOf t J e ((J e).val + 1) (by have := (J e).isLt; omega)]
    simp [show ¬((J e).val + 1 ≤ (J e).val) by omega]
  simp only [stepOf, Finset.image_insert, Finset.image_singleton, h1, h2, baseC]

private lemma subJ_stepOf_taut (t : ℕ) (J : Fin 6 → Fin t) (e : Fin 6) (j : ℕ)
    (hj : j < t) (hne : j ≠ (J e).val) :
    IsTaut ((stepOf (fun _ => t) e j).image (subJ t J)) := by
  have h1 := subJ_litOf t J e j (by omega)
  have h2 := subJ_litOf t J e (j + 1) (by omega)
  by_cases hlt : j < (J e).val
  · have ha : subJ t J (negLit (litOf (fun _ => t) e j)) = negLit (src e) := by
      rw [subJ_negLit, h1, if_pos (by omega)]
    have hb : subJ t J (litOf (fun _ => t) e (j + 1)) = src e := by
      rw [h2, if_pos (by omega)]
    refine ⟨(src e).1, ?_, ?_⟩
    · cases hs : (src e).2
      · exact Finset.mem_image.mpr ⟨negLit (litOf (fun _ => t) e j), by simp [stepOf], by rw [ha, negLit, hs]; rfl⟩
      · exact Finset.mem_image.mpr ⟨litOf (fun _ => t) e (j + 1), by simp [stepOf], by rw [hb, ← hs]⟩
    · cases hs : (src e).2
      · exact Finset.mem_image.mpr ⟨litOf (fun _ => t) e (j + 1), by simp [stepOf], by rw [hb, ← hs]⟩
      · exact Finset.mem_image.mpr ⟨negLit (litOf (fun _ => t) e j), by simp [stepOf], by rw [ha, negLit, hs]; rfl⟩
  · have hgt : (J e).val < j := by omega
    have ha : subJ t J (negLit (litOf (fun _ => t) e j)) = negLit (dst e) := by
      rw [subJ_negLit, h1, if_neg (by omega)]
    have hb : subJ t J (litOf (fun _ => t) e (j + 1)) = dst e := by
      rw [h2, if_neg (by omega)]
    refine ⟨(dst e).1, ?_, ?_⟩
    · cases hd : (dst e).2
      · exact Finset.mem_image.mpr ⟨negLit (litOf (fun _ => t) e j), by simp [stepOf], by rw [ha, negLit, hd]; rfl⟩
      · exact Finset.mem_image.mpr ⟨litOf (fun _ => t) e (j + 1), by simp [stepOf], by rw [hb, ← hd]⟩
    · cases hd : (dst e).2
      · exact Finset.mem_image.mpr ⟨litOf (fun _ => t) e (j + 1), by simp [stepOf], by rw [hb, ← hd]⟩
      · exact Finset.mem_image.mpr ⟨negLit (litOf (fun _ => t) e j), by simp [stepOf], by rw [ha, negLit, hd]; rfl⟩

private def subtree (nodes : Finset (List Bool)) (p : List Bool) : Finset (List Bool) :=
  nodes.filter (fun q => p <+: q)

private lemma subtree_child_sub (nodes : Finset (List Bool)) (p : List Bool) (a : Bool) :
    subtree nodes (p ++ [a]) ⊆ (subtree nodes p).erase p := by
  intro q hq
  simp only [subtree, Finset.mem_filter] at hq
  refine Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hq.1, List.IsPrefix.trans (List.prefix_append p [a]) hq.2⟩⟩
  intro hqp
  rw [hqp] at hq
  have hlen := List.IsPrefix.length_le hq.2
  simp at hlen

private lemma subtree_child_card_lt (nodes : Finset (List Bool)) {p : List Bool}
    (hp : p ∈ nodes) (a : Bool) :
    (subtree nodes (p ++ [a])).card < (subtree nodes p).card := by
  have hp_in : p ∈ subtree nodes p := Finset.mem_filter.mpr ⟨hp, List.prefix_refl p⟩
  calc (subtree nodes (p ++ [a])).card
      ≤ ((subtree nodes p).erase p).card := Finset.card_le_card (subtree_child_sub nodes p a)
    _ < (subtree nodes p).card := Finset.card_erase_lt_of_mem hp_in

private lemma subtree_children_disjoint (nodes : Finset (List Bool)) (p : List Bool) :
    Disjoint (subtree nodes (p ++ [false])) (subtree nodes (p ++ [true])) := by
  rw [Finset.disjoint_left]
  intro q h1 h2
  rcases (Finset.mem_filter.mp h1).2 with ⟨s1, hs1⟩
  rcases (Finset.mem_filter.mp h2).2 with ⟨s2, hs2⟩
  have heq : (p ++ [false]) ++ s1 = (p ++ [true]) ++ s2 := hs1.trans hs2.symm
  simp only [List.append_assoc, List.append_cancel_left_eq, List.cons_append, List.nil_append,
    List.cons.injEq] at heq
  exact Bool.false_ne_true heq.1

private lemma base_split_sat :
    ∀ (v : Fin 4) (SL : Finset (Fin 6)),
      (∃ mask : Fin 16,
        mask.val.testBit v.val = false ∧
        ∀ e ∈ SL, ∃ l ∈ baseC e, mask.val.testBit l.1.val = l.2) ∨
      (∃ mask : Fin 16,
        mask.val.testBit v.val = true ∧
        ∀ e ∈ Finset.univ \ SL, ∃ l ∈ baseC e, mask.val.testBit l.1.val = l.2) := by
  decide

private lemma base_two_sides_card_ge_7 {w : Fin 4} {b : Bool} {SL SR : Finset (Fin 6)}
    (hL : ∀ a : Fin 4 → Bool, (∀ e ∈ SL, ClauseSat a (baseC e)) → a w = b)
    (hR : ∀ a : Fin 4 → Bool, (∀ e ∈ SR, ClauseSat a (baseC e)) → a w = !b) :
    7 ≤ SL.card + SR.card := by
  by_contra hlt
  have hle6 : SL.card + SR.card ≤ 6 := by omega
  have hunion : SL ∪ SR = Finset.univ := by
    by_contra hne
    have hex : ∃ e₀ : Fin 6, e₀ ∉ SL ∪ SR := by
      by_contra hall
      push_neg at hall
      apply hne
      ext e
      simp [hall e]
    rcases hex with ⟨e₀, he₀⟩
    have hsatL : ∀ e ∈ SL, ClauseSat (baseWitness e₀) (baseC e) := by
      intro e he
      exact (baseWitness_spec e₀ e).2 (fun h => he₀ (Finset.mem_union_left _ (h ▸ he)))
    have hsatR : ∀ e ∈ SR, ClauseSat (baseWitness e₀) (baseC e) := by
      intro e he
      exact (baseWitness_spec e₀ e).2 (fun h => he₀ (Finset.mem_union_right _ (h ▸ he)))
    have h1 := hL (baseWitness e₀) hsatL
    have h2 := hR (baseWitness e₀) hsatR
    exact (Bool.not_eq_self b).mp (h2.symm.trans h1)
  have hinter0 : (SL ∩ SR).card = 0 := by
    have hcu := Finset.card_union_add_card_inter SL SR
    rw [hunion, Finset.card_univ, Fintype.card_fin] at hcu
    omega
  have hdisj : Disjoint SL SR := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hinter0)
  have hSR_eq : SR = Finset.univ \ SL := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro heSR heSL
      exact Finset.disjoint_left.mp hdisj heSL heSR
    · intro hnotSL
      have : e ∈ SL ∪ SR := by rw [hunion]; exact Finset.mem_univ e
      rcases Finset.mem_union.mp this with h1 | h2
      · exact False.elim (hnotSL h1)
      · exact h2
  cases b
  · rcases base_split_sat w SR with ⟨mask, hmv, hsat⟩ | ⟨mask, hmv, hsat⟩
    · have h1 := hR (fun i => mask.val.testBit i.val) hsat
      simp [hmv] at h1
    · have hSL_eq : SL = Finset.univ \ SR := by
        rw [hSR_eq, Finset.sdiff_sdiff_eq_self (Finset.subset_univ SL)]
      rw [← hSL_eq] at hsat
      have h1 := hL (fun i => mask.val.testBit i.val) hsat
      simp [hmv] at h1
  · rcases base_split_sat w SL with ⟨mask, hmv, hsat⟩ | ⟨mask, hmv, hsat⟩
    · have h1 := hL (fun i => mask.val.testBit i.val) hsat
      simp [hmv] at h1
    · rw [← hSR_eq] at hsat
      have h1 := hR (fun i => mask.val.testBit i.val) hsat
      simp [hmv] at h1

private lemma tree_sound_usedBase (t : ℕ) (J : Fin 6 → Fin t)
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause V)
    (hleaf : ∀ p ∈ nodes, p ∉ inner → line p ∈ famOf (fun _ => t))
    (hinner : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    ∀ k : ℕ, ∀ p ∈ nodes, (subtree nodes p).card = k →
      ¬ IsTaut ((line p).image (subJ t J)) →
      ∀ a : Fin 4 → Bool,
        (∀ e : Fin 6, (∃ q ∈ subtree nodes p \ inner, line q = stepOf (fun _ => t) e (J e).val) →
          ClauseSat a (baseC e)) →
        ClauseSat a ((line p).image (subJ t J)) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro p hp hcard hgood a ha
    by_cases hpin : p ∈ inner
    · rcases hinner p hpin with ⟨hL_in, hR_in, hRes⟩
      have hL_lt : (subtree nodes (p ++ [false])).card < k := by
        rw [← hcard]; exact subtree_child_card_lt nodes hp false
      have hR_lt : (subtree nodes (p ++ [true])).card < k := by
        rw [← hcard]; exact subtree_child_card_lt nodes hp true
      have hsubL : subtree nodes (p ++ [false]) \ inner ⊆ subtree nodes p \ inner :=
        Finset.sdiff_subset_sdiff ((subtree_child_sub nodes p false).trans (Finset.erase_subset _ _)) (Finset.Subset.refl _)
      have hsubR : subtree nodes (p ++ [true]) \ inner ⊆ subtree nodes p \ inner :=
        Finset.sdiff_subset_sdiff ((subtree_child_sub nodes p true).trans (Finset.erase_subset _ _)) (Finset.Subset.refl _)
      have haL : ∀ e, (∃ q ∈ subtree nodes (p ++ [false]) \ inner, line q = stepOf (fun _ => t) e (J e).val) →
          ClauseSat a (baseC e) := fun e ⟨q, hq, heq⟩ => ha e ⟨q, hsubL hq, heq⟩
      have haR : ∀ e, (∃ q ∈ subtree nodes (p ++ [true]) \ inner, line q = stepOf (fun _ => t) e (J e).val) →
          ClauseSat a (baseC e) := fun e ⟨q, hq, heq⟩ => ha e ⟨q, hsubR hq, heq⟩
      by_cases htL : IsTaut ((line (p ++ [false])).image (subJ t J))
      · have hRsub := taut_parent_left_sub (subJ t J) (subJ_negLit t J) hRes htL hgood
        have hgoodR : ¬ IsTaut ((line (p ++ [true])).image (subJ t J)) :=
          fun htR => hgood (isTaut_mono hRsub htR)
        rcases ih _ hR_lt (p ++ [true]) hR_in rfl hgoodR a haR with ⟨l, hl, hla⟩
        exact ⟨l, hRsub hl, hla⟩
      · by_cases htR : IsTaut ((line (p ++ [true])).image (subJ t J))
        · have hLsub := taut_parent_right_sub (subJ t J) (subJ_negLit t J) hRes htR hgood
          rcases ih _ hL_lt (p ++ [false]) hL_in rfl htL a haL with ⟨l, hl, hla⟩
          exact ⟨l, hLsub hl, hla⟩
        · have hsatL := ih _ hL_lt (p ++ [false]) hL_in rfl htL a haL
          have hsatR := ih _ hR_lt (p ++ [true]) hR_in rfl htR a haR
          rcases hRes with ⟨v, hvL, hvR, heq⟩
          set l0 := subJ t J (v, true) with hl0_def
          have hneg0 : subJ t J (v, false) = negLit l0 := by
            have h := subJ_negLit t J (v, true)
            simpa [negLit, hl0_def] using h
          by_cases hval : a l0.1 = l0.2
          · rcases hsatR with ⟨x, hx, hxa⟩
            rcases Finset.mem_image.mp hx with ⟨u, huR, rfl⟩
            have hune : u ≠ (v, false) := by
              intro hu
              rw [hu, hneg0] at hxa
              dsimp only [negLit] at hxa
              rw [hval] at hxa
              exact (Bool.not_eq_self _).mp hxa.symm
            refine ⟨subJ t J u, ?_, hxa⟩
            rw [heq]
            exact Finset.mem_image.mpr ⟨u, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hune, huR⟩), rfl⟩
          · rcases hsatL with ⟨x, hx, hxa⟩
            rcases Finset.mem_image.mp hx with ⟨u, huL, rfl⟩
            have hune : u ≠ (v, true) := by
              intro hu
              rw [hu, ← hl0_def] at hxa
              exact hval hxa
            refine ⟨subJ t J u, ?_, hxa⟩
            rw [heq]
            exact Finset.mem_image.mpr ⟨u, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hune, huL⟩), rfl⟩
    · rcases hleaf p hp hpin with ⟨e, j, hj, heq⟩
      have hj_eq : j = (J e).val := by
        by_contra hne
        rw [heq] at hgood
        exact hgood (subJ_stepOf_taut t J e j hj hne)
      subst hj_eq
      rw [heq, subJ_stepOf_eq]
      exact ha e ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hp, List.prefix_refl p⟩, hpin⟩, heq⟩

private lemma tree_goodLeaves_ge_7 (t : ℕ) (J : Fin 6 → Fin t)
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause V)
    (hleaf : ∀ p ∈ nodes, p ∉ inner → line p ∈ famOf (fun _ => t))
    (hinner : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    ∀ k : ℕ, ∀ p ∈ nodes, (subtree nodes p).card = k →
      (line p).image (subJ t J) = ∅ →
      7 ≤ ((subtree nodes p \ inner).filter
        (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)).card := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro p hp hcard hemp
    have hpin : p ∈ inner := by
      by_contra hnot
      rcases hleaf p hp hnot with ⟨e, j, hj, heq⟩
      rw [heq] at hemp
      have hne : (stepOf (fun _ => t) e j).Nonempty := ⟨litOf (fun _ => t) e (j + 1), by simp [stepOf]⟩
      have hne' := hne.image (subJ t J)
      rw [hemp] at hne'
      exact Finset.not_nonempty_empty hne'
    rcases hinner p hpin with ⟨hL_in, hR_in, hRes⟩
    have hL_lt : (subtree nodes (p ++ [false])).card < k := by
      rw [← hcard]; exact subtree_child_card_lt nodes hp false
    have hR_lt : (subtree nodes (p ++ [true])).card < k := by
      rw [← hcard]; exact subtree_child_card_lt nodes hp true
    have hsubL : subtree nodes (p ++ [false]) \ inner ⊆ subtree nodes p \ inner :=
      Finset.sdiff_subset_sdiff ((subtree_child_sub nodes p false).trans (Finset.erase_subset _ _)) (Finset.Subset.refl _)
    have hsubR : subtree nodes (p ++ [true]) \ inner ⊆ subtree nodes p \ inner :=
      Finset.sdiff_subset_sdiff ((subtree_child_sub nodes p true).trans (Finset.erase_subset _ _)) (Finset.Subset.refl _)
    have hngp : ¬ IsTaut ((line p).image (subJ t J)) := by
      rw [hemp]; exact not_isTaut_empty
    by_cases htL : IsTaut ((line (p ++ [false])).image (subJ t J))
    · have hRsub := taut_parent_left_sub (subJ t J) (subJ_negLit t J) hRes htL hngp
      rw [hemp] at hRsub
      have hRemp : (line (p ++ [true])).image (subJ t J) = ∅ := Finset.subset_empty.mp hRsub
      calc 7 ≤ ((subtree nodes (p ++ [true]) \ inner).filter
            (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)).card :=
            ih _ hR_lt (p ++ [true]) hR_in rfl hRemp
        _ ≤ ((subtree nodes p \ inner).filter
            (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ hsubR)
    · by_cases htR : IsTaut ((line (p ++ [true])).image (subJ t J))
      · have hLsub := taut_parent_right_sub (subJ t J) (subJ_negLit t J) hRes htR hngp
        rw [hemp] at hLsub
        have hLemp : (line (p ++ [false])).image (subJ t J) = ∅ := Finset.subset_empty.mp hLsub
        calc 7 ≤ ((subtree nodes (p ++ [false]) \ inner).filter
              (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)).card :=
              ih _ hL_lt (p ++ [false]) hL_in rfl hLemp
          _ ≤ ((subtree nodes p \ inner).filter
              (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)).card :=
              Finset.card_le_card (Finset.filter_subset_filter _ hsubL)
      · rcases hRes with ⟨v, hvL, hvR, heq⟩
        set l0 := subJ t J (v, true) with hl0_def
        have hneg0 : subJ t J (v, false) = negLit l0 := by
          have h := subJ_negLit t J (v, true)
          simpa [negLit, hl0_def] using h
        have hL_eq : (line (p ++ [false])).image (subJ t J) = {l0} := by
          ext x
          simp only [Finset.mem_image, Finset.mem_singleton]
          constructor
          · rintro ⟨u, huL, rfl⟩
            by_cases hu : u = (v, true)
            · rw [hu, hl0_def]
            · exfalso
              have hmem : subJ t J u ∈ (line p).image (subJ t J) := by
                rw [heq]
                exact Finset.mem_image.mpr ⟨u, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hu, huL⟩), rfl⟩
              rw [hemp] at hmem
              exact Finset.notMem_empty _ hmem
          · rintro rfl
            exact ⟨(v, true), hvL, rfl⟩
        have hR_eq : (line (p ++ [true])).image (subJ t J) = {negLit l0} := by
          ext x
          simp only [Finset.mem_image, Finset.mem_singleton]
          constructor
          · rintro ⟨u, huR, rfl⟩
            by_cases hu : u = (v, false)
            · rw [hu, hneg0]
            · exfalso
              have hmem : subJ t J u ∈ (line p).image (subJ t J) := by
                rw [heq]
                exact Finset.mem_image.mpr ⟨u, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hu, huR⟩), rfl⟩
              rw [hemp] at hmem
              exact Finset.notMem_empty _ hmem
          · rintro rfl
            exact ⟨(v, false), hvR, hneg0⟩
        set gL := (subtree nodes (p ++ [false]) \ inner).filter
          (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)
        set gR := (subtree nodes (p ++ [true]) \ inner).filter
          (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)
        set gP := (subtree nodes p \ inner).filter
          (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)
        set SL : Finset (Fin 6) := Finset.univ.filter
          (fun e => ∃ q ∈ subtree nodes (p ++ [false]) \ inner, line q = stepOf (fun _ => t) e (J e).val)
        set SR : Finset (Fin 6) := Finset.univ.filter
          (fun e => ∃ q ∈ subtree nodes (p ++ [true]) \ inner, line q = stepOf (fun _ => t) e (J e).val)
        have hSL_le : SL.card ≤ gL.card := by
          let pick : Fin 6 → List Bool := fun e =>
            if h : ∃ q ∈ subtree nodes (p ++ [false]) \ inner, line q = stepOf (fun _ => t) e (J e).val
            then Classical.choose h else []
          have hinj : Set.InjOn pick SL := by
            intro e₁ he₁ e₂ he₂ heq_p
            have h1 : ∃ q ∈ subtree nodes (p ++ [false]) \ inner, line q = stepOf (fun _ => t) e₁ (J e₁).val :=
              (Finset.mem_filter.mp he₁).2
            have h2 : ∃ q ∈ subtree nodes (p ++ [false]) \ inner, line q = stepOf (fun _ => t) e₂ (J e₂).val :=
              (Finset.mem_filter.mp he₂).2
            dsimp only [pick] at heq_p
            rw [dif_pos h1, dif_pos h2] at heq_p
            have hs1 := (Classical.choose_spec h1).2
            have hs2 := (Classical.choose_spec h2).2
            rw [heq_p] at hs1
            exact (stepOf_inj (fun _ => t) (J e₁).isLt (J e₂).isLt (hs1.symm.trans hs2)).1
          have hmaps : Set.MapsTo pick SL gL := by
            intro e he
            have h1 : ∃ q ∈ subtree nodes (p ++ [false]) \ inner, line q = stepOf (fun _ => t) e (J e).val :=
              (Finset.mem_filter.mp he).2
            dsimp only [pick]
            rw [dif_pos h1]
            exact Finset.mem_filter.mpr ⟨(Classical.choose_spec h1).1, e, (Classical.choose_spec h1).2⟩
          exact Finset.card_le_card_of_injOn pick hmaps hinj
        have hSR_le : SR.card ≤ gR.card := by
          let pick : Fin 6 → List Bool := fun e =>
            if h : ∃ q ∈ subtree nodes (p ++ [true]) \ inner, line q = stepOf (fun _ => t) e (J e).val
            then Classical.choose h else []
          have hinj : Set.InjOn pick SR := by
            intro e₁ he₁ e₂ he₂ heq_p
            have h1 : ∃ q ∈ subtree nodes (p ++ [true]) \ inner, line q = stepOf (fun _ => t) e₁ (J e₁).val :=
              (Finset.mem_filter.mp he₁).2
            have h2 : ∃ q ∈ subtree nodes (p ++ [true]) \ inner, line q = stepOf (fun _ => t) e₂ (J e₂).val :=
              (Finset.mem_filter.mp he₂).2
            dsimp only [pick] at heq_p
            rw [dif_pos h1, dif_pos h2] at heq_p
            have hs1 := (Classical.choose_spec h1).2
            have hs2 := (Classical.choose_spec h2).2
            rw [heq_p] at hs1
            exact (stepOf_inj (fun _ => t) (J e₁).isLt (J e₂).isLt (hs1.symm.trans hs2)).1
          have hmaps : Set.MapsTo pick SR gR := by
            intro e he
            have h1 : ∃ q ∈ subtree nodes (p ++ [true]) \ inner, line q = stepOf (fun _ => t) e (J e).val :=
              (Finset.mem_filter.mp he).2
            dsimp only [pick]
            rw [dif_pos h1]
            exact Finset.mem_filter.mpr ⟨(Classical.choose_spec h1).1, e, (Classical.choose_spec h1).2⟩
          exact Finset.card_le_card_of_injOn pick hmaps hinj
        have hdisjG : Disjoint gL gR := by
          apply Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
          apply Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
          exact subtree_children_disjoint nodes p
        have hG_le : gL.card + gR.card ≤ gP.card := by
          rw [← Finset.card_union_of_disjoint hdisjG]
          exact Finset.card_le_card
            (Finset.union_subset (Finset.filter_subset_filter _ hsubL) (Finset.filter_subset_filter _ hsubR))
        have hSL_ent : ∀ a : Fin 4 → Bool, (∀ e ∈ SL, ClauseSat a (baseC e)) → a l0.1 = l0.2 := by
          intro a ha
          have hsat := tree_sound_usedBase t J nodes inner line hleaf hinner _ (p ++ [false]) hL_in rfl htL a
            (fun e he => ha e (Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩))
          rw [hL_eq] at hsat
          rcases hsat with ⟨l, hl, hla⟩
          rw [Finset.mem_singleton.mp hl] at hla
          exact hla
        have hSR_ent : ∀ a : Fin 4 → Bool, (∀ e ∈ SR, ClauseSat a (baseC e)) → a l0.1 = !l0.2 := by
          intro a ha
          have hsat := tree_sound_usedBase t J nodes inner line hleaf hinner _ (p ++ [true]) hR_in rfl htR a
            (fun e he => ha e (Finset.mem_filter.mpr ⟨Finset.mem_univ e, he⟩))
          rw [hR_eq] at hsat
          rcases hsat with ⟨l, hl, hla⟩
          rw [Finset.mem_singleton.mp hl] at hla
          exact hla
        have h7 := base_two_sides_card_ge_7 hSL_ent hSR_ent
        omega

private lemma tree_lower_bound (t : ℕ) (ht : 0 < t) (N : ℕ)
    (nodes inner : Finset (List Bool)) (line : List Bool → Clause V) (cost : List Bool → ℕ)
    (hroot : [] ∈ nodes) (_hsub : inner ⊆ nodes) (hline0 : line [] = ∅)
    (hsum : (nodes \ inner).sum cost ≤ N)
    (hleaf : ∀ p ∈ nodes, p ∉ inner → line p ∈ famOf (fun _ => t) ∧ cost p = 1)
    (hinner : ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)) :
    7 * t ≤ N := by
  have hleaves_card : (nodes \ inner).card ≤ N := by
    have heq : (nodes \ inner).sum cost = (nodes \ inner).card := by
      calc (nodes \ inner).sum cost = ∑ _p ∈ nodes \ inner, (1 : ℕ) :=
            Finset.sum_congr rfl (fun p hp =>
              (hleaf p (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2).2)
        _ = (nodes \ inner).card := by simp
    omega
  let c : Fin 6 → Fin t → ℕ := fun e j =>
    ((nodes \ inner).filter (fun q => line q = stepOf (fun _ => t) e j.val)).card
  have hne_t : (Finset.univ : Finset (Fin t)).Nonempty :=
    ⟨⟨0, ht⟩, Finset.mem_univ _⟩
  let J : Fin 6 → Fin t := fun e =>
    Classical.choose (Finset.exists_min_image Finset.univ (c e) hne_t)
  have hJ_min : ∀ (e : Fin 6) (j : Fin t), c e (J e) ≤ c e j := by
    intro e j
    exact (Classical.choose_spec (Finset.exists_min_image Finset.univ (c e) hne_t)).2 j (Finset.mem_univ j)
  have hsub0 : subtree nodes [] = nodes := by
    ext q; simp [subtree]
  have h7 := tree_goodLeaves_ge_7 t J nodes inner line (fun p hp hni => (hleaf p hp hni).1) hinner
    (subtree nodes []).card [] hroot rfl (by simp [hline0])
  rw [hsub0] at h7
  have hgood_eq : ((nodes \ inner).filter
      (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val)).card =
      ∑ e : Fin 6, c e (J e) := by
    have hunion : (nodes \ inner).filter (fun q => ∃ e : Fin 6, line q = stepOf (fun _ => t) e (J e).val) =
        Finset.univ.biUnion (fun e : Fin 6 => (nodes \ inner).filter (fun q => line q = stepOf (fun _ => t) e (J e).val)) := by
      ext q; simp
    rw [hunion, Finset.card_biUnion]
    intro e₁ _ e₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro q h1 h2
    have he1 := (Finset.mem_filter.mp h1).2
    have he2 := (Finset.mem_filter.mp h2).2
    exact hne (stepOf_inj (fun _ => t) (J e₁).isLt (J e₂).isLt (he1.symm.trans he2)).1
  rw [hgood_eq] at h7
  have hrow : ∀ e : Fin 6, t * c e (J e) ≤ ∑ j : Fin t, c e j := by
    intro e
    calc t * c e (J e) = ∑ _j : Fin t, c e (J e) := by
          simp [Finset.sum_const]
      _ ≤ ∑ j : Fin t, c e j := Finset.sum_le_sum (fun j _ => hJ_min e j)
  have htot : ∑ e : Fin 6, ∑ j : Fin t, c e j ≤ (nodes \ inner).card := by
    rw [← Finset.sum_product', Finset.univ_product_univ]
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 6 × Fin t)))
        (fun p : Fin 6 × Fin t => (nodes \ inner).filter (fun q => line q = stepOf (fun _ => t) p.1 p.2.val)) := by
      intro p₁ _ p₂ _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro q h1 h2
      have he1 := (Finset.mem_filter.mp h1).2
      have he2 := (Finset.mem_filter.mp h2).2
      have hinj := stepOf_inj (fun _ => t) p₁.2.isLt p₂.2.isLt (he1.symm.trans he2)
      apply hne
      exact Prod.ext hinj.1 (Fin.ext hinj.2)
    have hbi := Finset.card_biUnion hdisj
    dsimp only [c]
    rw [← hbi]
    apply Finset.card_le_card
    intro q hq
    rcases Finset.mem_biUnion.mp hq with ⟨_, _, hqf⟩
    exact (Finset.mem_filter.mp hqf).1
  have hmul : 7 * t ≤ ∑ e : Fin 6, t * c e (J e) := by
    rw [← Finset.mul_sum]
    nlinarith
  have hsum_le : ∑ e : Fin 6, t * c e (J e) ≤ ∑ e : Fin 6, ∑ j : Fin t, c e j :=
    Finset.sum_le_sum (fun e _ => hrow e)
  omega

private def prefC (t : ℕ) (e : Fin 6) (k : ℕ) : Clause V :=
  ({negLit (litOf (fun _ => t) e 0), litOf (fun _ => t) e (k + 1)} : Clause V)

private lemma prefC_zero (t : ℕ) (e : Fin 6) : prefC t e 0 = stepOf (fun _ => t) e 0 := rfl

private lemma prefC_last (t : ℕ) (ht : 0 < t) (e : Fin 6) : prefC t e (t - 1) = baseV e := by
  have h1 : t - 1 + 1 = t := by omega
  simp only [prefC, h1, litOf, if_true, show t ≠ 0 by omega, if_false, baseV, liftClause, baseC,
    liftLit, negLit, Finset.image_insert, Finset.image_singleton]

private lemma prefC_resolvent (t : ℕ) (e : Fin 6) (k : ℕ) (hk : k + 1 < t) :
    IsResolvent (prefC t e k) (stepOf (fun _ => t) e (k + 1)) (prefC t e (k + 1)) := by
  have hlit_mid : litOf (fun _ => t) e (k + 1) = (Sum.inr (e, k + 1), true) := by
    dsimp only [litOf]
    rw [if_neg (by omega), if_neg (by omega)]
  have hne1 : negLit (litOf (fun _ => t) e 0) ≠ (Sum.inr (e, k + 1), true) := by
    simp [litOf, negLit]
  have hne2 : litOf (fun _ => t) e (k + 2) ≠ (Sum.inr (e, k + 1), false) := by
    dsimp only [litOf]
    rw [if_neg (by omega)]
    split_ifs <;> simp
  refine ⟨Sum.inr (e, k + 1), ?_, ?_, ?_⟩
  · simp [prefC, hlit_mid]
  · simp [stepOf, hlit_mid, negLit]
  · ext l
    simp only [prefC, stepOf, hlit_mid, negLit, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · left; exact ⟨hne1, Or.inl rfl⟩
      · right; exact ⟨hne2, Or.inr rfl⟩
    · rintro (⟨h1, rfl | h2⟩ | ⟨h1, h2 | rfl⟩)
      · exact Or.inl rfl
      · exact False.elim (h1 h2)
      · exact False.elim (h1 h2)
      · exact Or.inr rfl

private def chainList (t : ℕ) (e : Fin 6) : ℕ → List (Clause V)
  | 0 => [stepOf (fun _ => t) e 0]
  | k + 1 => prefC t e (k + 1) :: stepOf (fun _ => t) e (k + 1) :: chainList t e k

private lemma chainList_spec (t : ℕ) (e : Fin 6) :
    ∀ k, k < t →
      IsDerivation (famOf (fun _ => t)) (chainList t e k) ∧
      prefC t e k ∈ chainList t e k ∧
      (chainList t e k).length = 2 * k + 1 := by
  intro k
  induction k with
  | zero =>
    intro h0
    refine ⟨IsDerivation.ax IsDerivation.nil ⟨e, 0, h0, rfl⟩, ?_, rfl⟩
    simp [chainList, prefC_zero]
  | succ k ih =>
    intro hk
    rcases ih (by omega) with ⟨hder, hmem, hlen⟩
    have hstep : stepOf (fun _ => t) e (k + 1) ∈ famOf (fun _ => t) := ⟨e, k + 1, hk, rfl⟩
    have hder1 := IsDerivation.ax hder hstep
    have hder2 := IsDerivation.res hder1 (List.mem_cons_of_mem _ hmem) List.mem_cons_self
      (prefC_resolvent t e k hk)
    refine ⟨hder2, List.mem_cons_self, ?_⟩
    simp only [chainList, List.length_cons, hlen]
    omega

private lemma liftClause_resolvent {C D R : Clause (Fin 4)} (h : IsResolvent C D R) :
    IsResolvent (liftClause C) (liftClause D) (liftClause R) := by
  rcases h with ⟨v, hvC, hvD, rfl⟩
  have hinj : Function.Injective liftLit := by
    intro l₁ l₂ h
    rcases l₁ with ⟨x₁, b₁⟩
    rcases l₂ with ⟨x₂, b₂⟩
    simp [liftLit] at h
    exact Prod.ext h.1 h.2
  refine ⟨Sum.inl v, Finset.mem_image.mpr ⟨(v, true), hvC, rfl⟩,
    Finset.mem_image.mpr ⟨(v, false), hvD, rfl⟩, ?_⟩
  simp only [liftClause, Finset.image_union, Finset.image_erase hinj, liftLit]

private lemma base_step_A : IsResolvent (baseC 2) (baseC 1) {(0, true), (3, false)} := by
  refine ⟨2, by decide, by decide, by decide⟩

private lemma base_step_B : IsResolvent (baseC 3) {(0, true), (3, false)} {(0, true)} := by
  refine ⟨3, by decide, by decide, by decide⟩

private lemma base_step_E : IsResolvent (baseC 4) (baseC 1) {(1, true), (3, false)} := by
  refine ⟨2, by decide, by decide, by decide⟩

private lemma base_step_F : IsResolvent (baseC 5) {(1, true), (3, false)} {(1, true)} := by
  refine ⟨3, by decide, by decide, by decide⟩

private lemma base_step_G : IsResolvent {(0, true)} (baseC 0) {(1, false)} := by
  refine ⟨0, by decide, by decide, by decide⟩

private lemma base_step_H : IsResolvent ({(1, true)} : Clause (Fin 4)) {(1, false)} (∅ : Clause (Fin 4)) := by
  refine ⟨1, by decide, by decide, by decide⟩

private lemma shared_upper_bound (t : ℕ) (ht : 0 < t) :
    ∃ π : List (Clause V), IsRefutation (famOf (fun _ => t)) π ∧ π.length = 12 * t := by
  let ch : Fin 6 → List (Clause V) := fun e => chainList t e (t - 1)
  have hch : ∀ e : Fin 6,
      IsDerivation (famOf (fun _ => t)) (ch e) ∧ baseV e ∈ ch e ∧ (ch e).length = 2 * (t - 1) + 1 := by
    intro e
    rcases chainList_spec t e (t - 1) (by omega) with ⟨h1, h2, h3⟩
    rw [prefC_last t ht e] at h2
    exact ⟨h1, h2, h3⟩
  let baseAll := ch 0 ++ ch 1 ++ ch 2 ++ ch 3 ++ ch 4 ++ ch 5
  have hderAll : IsDerivation (famOf (fun _ => t)) baseAll :=
    isDerivation_append
      (isDerivation_append
        (isDerivation_append
          (isDerivation_append
            (isDerivation_append (hch 0).1 (hch 1).1)
            (hch 2).1)
          (hch 3).1)
        (hch 4).1)
      (hch 5).1
  have hlenAll : baseAll.length = 6 * (2 * (t - 1) + 1) := by
    simp only [baseAll, List.length_append, (hch 0).2.2, (hch 1).2.2, (hch 2).2.2, (hch 3).2.2,
      (hch 4).2.2, (hch 5).2.2]
    omega
  have hm0 : baseV 0 ∈ baseAll := by
    simp only [baseAll, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (hch 0).2.1))))
  have hm1 : baseV 1 ∈ baseAll := by
    simp only [baseAll, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (hch 1).2.1))))
  have hm2 : baseV 2 ∈ baseAll := by
    simp only [baseAll, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr (hch 2).2.1)))
  have hm3 : baseV 3 ∈ baseAll := by
    simp only [baseAll, List.mem_append]; exact Or.inl (Or.inl (Or.inr (hch 3).2.1))
  have hm4 : baseV 4 ∈ baseAll := by
    simp only [baseAll, List.mem_append]; exact Or.inl (Or.inr (hch 4).2.1)
  have hm5 : baseV 5 ∈ baseAll := by
    simp only [baseAll, List.mem_append]; exact Or.inr (hch 5).2.1
  let cA := liftClause {(0, true), (3, false)}
  let cB := liftClause {(0, true)}
  let cE := liftClause {(1, true), (3, false)}
  let cF := liftClause {(1, true)}
  let cG := liftClause {(1, false)}
  let cH : Clause V := ∅
  have hA := liftClause_resolvent base_step_A
  have hB := liftClause_resolvent base_step_B
  have hE := liftClause_resolvent base_step_E
  have hF := liftClause_resolvent base_step_F
  have hG := liftClause_resolvent base_step_G
  have hH : IsResolvent cF cG cH := by
    simpa [cF, cG, cH, liftClause] using liftClause_resolvent base_step_H
  have h1 := IsDerivation.res hderAll hm2 hm1 hA
  have h2 := IsDerivation.res h1 (List.mem_cons_of_mem _ hm3) List.mem_cons_self hB
  have h3 := IsDerivation.res h2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm4))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm1)) hE
  have h4 := IsDerivation.res h3
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm5)))
    List.mem_cons_self hF
  have h5 := IsDerivation.res h4
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm0)))) hG
  have h6 := IsDerivation.res h5 (List.mem_cons_of_mem _ List.mem_cons_self) List.mem_cons_self hH
  refine ⟨cH :: cG :: cF :: cE :: cB :: cA :: baseAll, ⟨h6, List.mem_cons_self⟩, ?_⟩
  simp only [List.length_cons, hlenAll]
  omega

private def HasTree (F : Set (Clause V)) (R : Clause V) (k : ℕ) : Prop :=
  ∃ (nodes inner : Finset (List Bool)) (line : List Bool → Clause V),
    [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = R ∧
    (nodes \ inner).card = k ∧
    (∀ p ∈ nodes, p ∉ inner → line p ∈ F) ∧
    (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) ∧
    ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
      IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)

private lemma hasTree_leaf {F : Set (Clause V)} {C : Clause V} (hC : C ∈ F) :
    HasTree F C 1 := by
  refine ⟨{[]}, ∅, fun _ => C, Finset.mem_singleton_self _, Finset.empty_subset _, rfl,
    by simp, ?_, ?_, ?_⟩
  · intro p _ _; exact hC
  · intro p a hmem
    have := Finset.mem_singleton.mp hmem
    exact False.elim (List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil a []) this)
  · intro p hp; exact False.elim (Finset.notMem_empty p hp)

private lemma hasTree_join {F : Set (Clause V)} {C D R : Clause V} {k₁ k₂ : ℕ}
    (h₁ : HasTree F C k₁) (h₂ : HasTree F D k₂) (hRes : IsResolvent C D R) :
    HasTree F R (k₁ + k₂) := by
  rcases h₁ with ⟨n₁, i₁, l₁, hr₁, hsub₁, hline₁, hcard₁, hleaf₁, hpar₁, hin₁⟩
  rcases h₂ with ⟨n₂, i₂, l₂, hr₂, hsub₂, hline₂, hcard₂, hleaf₂, hpar₂, hin₂⟩
  let nodes : Finset (List Bool) :=
    insert [] (n₁.image (false :: ·) ∪ n₂.image (true :: ·))
  let inner : Finset (List Bool) :=
    insert [] (i₁.image (false :: ·) ∪ i₂.image (true :: ·))
  let line : List Bool → Clause V
    | [] => R
    | false :: q => l₁ q
    | true :: q => l₂ q
  have hinjF : Function.Injective (fun q : List Bool => false :: q) := fun _ _ h => (List.cons.inj h).2
  have hinjT : Function.Injective (fun q : List Bool => true :: q) := fun _ _ h => (List.cons.inj h).2
  have hsub : inner ⊆ nodes := by
    intro p hp
    simp only [inner, nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp ⊢
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨q, hsub₁ hq, rfl⟩)
    · exact Or.inr (Or.inr ⟨q, hsub₂ hq, rfl⟩)
  have hsdiff : nodes \ inner =
      (n₁ \ i₁).image (false :: ·) ∪ (n₂ \ i₂).image (true :: ·) := by
    ext p
    simp only [nodes, inner, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image]
    cases p with
    | nil => simp
    | cons b q =>
      cases b
      · constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with hnil | ⟨q', hq', heq⟩ | ⟨q', _, heq⟩
          · exact False.elim (List.cons_ne_nil _ _ hnil)
          · have hqq : q' = q := (List.cons.inj heq).2
            subst hqq
            left
            refine ⟨q', ⟨hq', fun hq'i => h2 (Or.inr (Or.inl ⟨q', hq'i, rfl⟩))⟩, rfl⟩
          · exact False.elim (Bool.false_ne_true (List.cons.inj heq).1.symm)
        · rintro (⟨q', ⟨hq', hni⟩, heq⟩ | ⟨q', _, heq⟩)
          · have hqq : q' = q := (List.cons.inj heq).2
            subst hqq
            refine ⟨Or.inr (Or.inl ⟨q', hq', rfl⟩), ?_⟩
            rintro (hnil | ⟨q'', hq'', heq2⟩ | ⟨q'', _, heq2⟩)
            · exact List.cons_ne_nil _ _ hnil
            · exact hni ((List.cons.inj heq2).2 ▸ hq'')
            · exact Bool.false_ne_true (List.cons.inj heq2).1.symm
          · exact False.elim (Bool.false_ne_true (List.cons.inj heq).1.symm)
      · constructor
        · rintro ⟨h1, h2⟩
          rcases h1 with hnil | ⟨q', _, heq⟩ | ⟨q', hq', heq⟩
          · exact False.elim (List.cons_ne_nil _ _ hnil)
          · exact False.elim (Bool.false_ne_true (List.cons.inj heq).1)
          · have hqq : q' = q := (List.cons.inj heq).2
            subst hqq
            right
            refine ⟨q', ⟨hq', fun hq'i => h2 (Or.inr (Or.inr ⟨q', hq'i, rfl⟩))⟩, rfl⟩
        · rintro (⟨q', _, heq⟩ | ⟨q', ⟨hq', hni⟩, heq⟩)
          · exact False.elim (Bool.false_ne_true (List.cons.inj heq).1)
          · have hqq : q' = q := (List.cons.inj heq).2
            subst hqq
            refine ⟨Or.inr (Or.inr ⟨q', hq', rfl⟩), ?_⟩
            rintro (hnil | ⟨q'', _, heq2⟩ | ⟨q'', hq'', heq2⟩)
            · exact List.cons_ne_nil _ _ hnil
            · exact Bool.false_ne_true (List.cons.inj heq2).1
            · exact hni ((List.cons.inj heq2).2 ▸ hq'')
  have hdisj : Disjoint ((n₁ \ i₁).image (false :: ·)) ((n₂ \ i₂).image (true :: ·)) := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨_, _, heq⟩
    exact Bool.false_ne_true (List.cons.inj heq).1.symm
  have hcard : (nodes \ inner).card = k₁ + k₂ := by
    rw [hsdiff, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hinjF, Finset.card_image_of_injective _ hinjT,
      hcard₁, hcard₂]
  refine ⟨nodes, inner, line, Finset.mem_insert_self _ _, hsub, rfl, hcard, ?_, ?_, ?_⟩
  · intro p hp hni
    have hpm : p ∈ nodes \ inner := Finset.mem_sdiff.mpr ⟨hp, hni⟩
    rw [hsdiff, Finset.mem_union] at hpm
    rcases hpm with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨q, hq, rfl⟩
      rcases Finset.mem_sdiff.mp hq with ⟨hq1, hq2⟩
      exact hleaf₁ q hq1 hq2
    · rcases Finset.mem_image.mp h2 with ⟨q, hq, rfl⟩
      rcases Finset.mem_sdiff.mp hq with ⟨hq1, hq2⟩
      exact hleaf₂ q hq1 hq2
  · intro p a hpa
    cases p with
    | nil => exact Finset.mem_insert_self _ _
    | cons b q =>
      simp only [nodes, Finset.mem_insert, Finset.mem_union, Finset.mem_image, List.cons_append] at hpa
      cases b
      · rcases hpa with hnil | ⟨q', hq', heq⟩ | ⟨q', _, heq⟩
        · exact False.elim (List.cons_ne_nil _ _ hnil)
        · have hqq : q' = q ++ [a] := (List.cons.inj heq).2
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨q, hpar₁ q a (hqq ▸ hq'), rfl⟩))
        · exact False.elim (Bool.false_ne_true (List.cons.inj heq).1.symm)
      · rcases hpa with hnil | ⟨q', _, heq⟩ | ⟨q', hq', heq⟩
        · exact False.elim (List.cons_ne_nil _ _ hnil)
        · exact False.elim (Bool.false_ne_true (List.cons.inj heq).1)
        · have hqq : q' = q ++ [a] := (List.cons.inj heq).2
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨q, hpar₂ q a (hqq ▸ hq'), rfl⟩))
  · intro p hp
    simp only [inner, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hp
    rcases hp with rfl | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨[], hr₁, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨[], hr₂, rfl⟩)), ?_⟩
      simpa [line, hline₁, hline₂] using hRes
    · rcases hin₁ q hq with ⟨h1, h2, h3⟩
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [false], h1, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q ++ [true], h2, rfl⟩)), ?_⟩
      simpa [line] using h3
    · rcases hin₂ q hq with ⟨h1, h2, h3⟩
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [false], h1, rfl⟩)),
        Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q ++ [true], h2, rfl⟩)), ?_⟩
      simpa [line] using h3

private lemma chainTree_spec (t : ℕ) (e : Fin 6) :
    ∀ k, k < t → HasTree (famOf (fun _ => t)) (prefC t e k) (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro h0
    rw [prefC_zero]
    exact hasTree_leaf ⟨e, 0, h0, rfl⟩
  | succ k ih =>
    intro hk
    exact hasTree_join (ih (by omega)) (hasTree_leaf ⟨e, k + 1, hk, rfl⟩)
      (prefC_resolvent t e k hk)

private lemma tree_upper_bound (t : ℕ) (ht : 0 < t) :
    HasTree (famOf (fun _ => t)) ∅ (7 * t) := by
  have hb : ∀ e : Fin 6, HasTree (famOf (fun _ => t)) (baseV e) t := by
    intro e
    have h := chainTree_spec t e (t - 1) (by omega)
    rw [prefC_last t ht e, show t - 1 + 1 = t by omega] at h
    exact h
  have hA := hasTree_join (hb 2) (hb 1) (liftClause_resolvent base_step_A)
  have hB := hasTree_join (hb 3) hA (liftClause_resolvent base_step_B)
  have hE := hasTree_join (hb 4) (hb 1) (liftClause_resolvent base_step_E)
  have hF := hasTree_join (hb 5) hE (liftClause_resolvent base_step_F)
  have hG := hasTree_join hB (hb 0) (liftClause_resolvent base_step_G)
  have hH_res : IsResolvent (liftClause {(1, true)}) (liftClause {(1, false)}) (∅ : Clause V) := by
    simpa [liftClause] using liftClause_resolvent base_step_H
  have hH := hasTree_join hF hG hH_res
  have h7 : t + (t + t) + (t + (t + t) + t) = 7 * t := by omega
  rwa [h7] at hH

end PEqualNP.Outside.L_pcx_287

theorem PEqualNP.Outside.L_pcx_287 :
  ∀ t : ℕ, 0 < t →
    let n := 4
    let m := 6
    let src : Fin m → Fin n × Bool := ![(0,true),(2,true),(0,false),(0,false),(1,false),(1,false)]
    let dst : Fin m → Fin n × Bool := ![(1,false),(3,false),(2,true),(3,true),(2,true),(3,true)]
    let len := fun _ : Fin m => t
    let V := Fin n ⊕ (Fin m × ℕ)
    let lit := fun (e : Fin m) (j : ℕ) =>
      if j = 0 then ((Sum.inl (src e).1 : V), (src e).2)
      else if j = len e then ((Sum.inl (dst e).1 : V), (dst e).2)
      else ((Sum.inr (e,j) : V), true)
    let step := fun (e : Fin m) (j : ℕ) =>
      ({((lit e j).1, !(lit e j).2), lit e (j+1)} : PEqualNP.ProofComplexity.Clause V)
    let big : Set (PEqualNP.ProofComplexity.Clause V) := {C | ∃ e j, j < len e ∧ C = step e j}
    let tree := fun (leaf : PEqualNP.ProofComplexity.Clause V → ℕ → Prop) (K : ℕ) =>
      ∃ (nodes inner : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause V)
        (cost : List Bool → ℕ), [] ∈ nodes ∧ inner ⊆ nodes ∧ line [] = ∅ ∧
        (nodes \ inner).sum cost ≤ K ∧
        (∀ p ∈ nodes, p ∉ inner → leaf (line p) (cost p)) ∧
        (∀ (p : List Bool) (a : Bool), p ++ [a] ∈ nodes → p ∈ inner) ∧
        ∀ p ∈ inner, p ++ [false] ∈ nodes ∧ p ++ [true] ∈ nodes ∧
          PEqualNP.ProofComplexity.IsResolvent (line (p ++ [false])) (line (p ++ [true])) (line p)
    ∀ L N : ℕ,
      ((∃ π, PEqualNP.ProofComplexity.IsRefutation big π ∧ π.length ≤ L) ↔ 12*t ≤ L) ∧
      (tree (fun C k => C ∈ big ∧ k = 1) N ↔ 7*t ≤ N) := by
  intro t ht n m src dst len V lit step big tree L N
  have hbig : big = PEqualNP.Outside.L_pcx_287.famOf (fun _ => t) := rfl
  constructor
  · constructor
    · rintro ⟨π, href, hlen⟩
      rw [hbig] at href
      have h12 := PEqualNP.Outside.L_pcx_287.shared_lower_bound t ht href
      omega
    · intro hL
      rcases PEqualNP.Outside.L_pcx_287.shared_upper_bound t ht with ⟨π, href, hlen⟩
      rw [← hbig] at href
      exact ⟨π, href, by omega⟩
  · constructor
    · rintro ⟨nodes, inner, line, cost, hroot, hsub, hline0, hsum, hleaf, _hpar, hinner⟩
      rw [hbig] at hleaf
      exact PEqualNP.Outside.L_pcx_287.tree_lower_bound t ht N nodes inner line cost
        hroot hsub hline0 hsum hleaf hinner
    · intro hN
      rcases PEqualNP.Outside.L_pcx_287.tree_upper_bound t ht with
        ⟨nodes, inner, line, hroot, hsub, hline0, hcard, hleaf, hpar, hinner⟩
      refine ⟨nodes, inner, line, fun _ => 1, hroot, hsub, hline0, ?_, ?_, hpar, hinner⟩
      · simp only [Finset.sum_const, smul_eq_mul, mul_one, hcard]
        exact hN
      · intro p hp hni
        rw [hbig]
        exact ⟨hleaf p hp hni, rfl⟩
