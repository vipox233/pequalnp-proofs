import Mathlib.Data.Nat.Log
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_373

open PEqualNP.ProofComplexity

section WeakResolution

private def IsWeakStep {V : Type} [DecidableEq V] (F : Set (Clause V))
    (prev : List (Clause V)) (C : Clause V) : Prop :=
  C ∈ F ∨ (∃ A ∈ prev, A ⊆ C) ∨ (∃ A ∈ prev, ∃ B ∈ prev, IsResolvent A B C)

private def IsWeakDeriv {V : Type} [DecidableEq V] (F : Set (Clause V)) :
    List (Clause V) → Prop
  | [] => True
  | C :: rest => IsWeakDeriv F rest ∧ IsWeakStep F rest C

private lemma isWeakStep_mono {V : Type} [DecidableEq V] {F₁ F₂ : Set (Clause V)}
    {p₁ p₂ : List (Clause V)} {C : Clause V}
    (hF : F₁ ⊆ F₂) (hp : ∀ A ∈ p₁, A ∈ p₂) (h : IsWeakStep F₁ p₁ C) :
    IsWeakStep F₂ p₂ C := by
  rcases h with h1 | ⟨A, hA, hsub⟩ | ⟨A, hA, B, hB, hres⟩
  · exact Or.inl (hF h1)
  · exact Or.inr (Or.inl ⟨A, hp A hA, hsub⟩)
  · exact Or.inr (Or.inr ⟨A, hp A hA, B, hp B hB, hres⟩)

private lemma isWeakDeriv_mono {V : Type} [DecidableEq V] {F₁ F₂ : Set (Clause V)}
    {π : List (Clause V)} (hF : F₁ ⊆ F₂) (h : IsWeakDeriv F₁ π) :
    IsWeakDeriv F₂ π := by
  induction π with
  | nil => trivial
  | cons C rest ih =>
    exact ⟨ih h.1, isWeakStep_mono hF (fun _ hA => hA) h.2⟩

private lemma isWeakDeriv_append {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π δ : List (Clause V)} (hπ : IsWeakDeriv F π)
    (hδ : IsWeakDeriv (F ∪ {A | A ∈ π}) δ) :
    IsWeakDeriv F (δ ++ π) := by
  induction δ with
  | nil => exact hπ
  | cons C rest ih =>
    refine ⟨ih hδ.1, ?_⟩
    rcases hδ.2 with hax | ⟨A, hA, hsub⟩ | ⟨A, hA, B, hB, hres⟩
    · rcases hax with hF | hmem
      · exact Or.inl hF
      · exact Or.inr (Or.inl ⟨C, List.mem_append_right rest hmem, Finset.Subset.rfl⟩)
    · exact Or.inr (Or.inl ⟨A, List.mem_append_left π hA, hsub⟩)
    · exact Or.inr (Or.inr ⟨A, List.mem_append_left π hA, B, List.mem_append_left π hB, hres⟩)

private lemma elim_weakening {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsWeakDeriv F π) :
    ∃ π' : List (Clause V), IsDerivation F π' ∧ π'.length ≤ π.length ∧
      (∀ C ∈ π, ∃ D ∈ π', D ⊆ C) ∧ (∀ D ∈ π', ∃ C ∈ π, D ⊆ C) := by
  induction π with
  | nil =>
    exact ⟨[], IsDerivation.nil, le_rfl, fun _ h => absurd h List.not_mem_nil,
      fun _ h => absurd h List.not_mem_nil⟩
  | cons C rest ih =>
    obtain ⟨π', hd', hlen', hcov, hsub⟩ := ih hπ.1
    rcases hπ.2 with hF | ⟨A, hA, hAC⟩ | ⟨A, hA, B, hB, v, hvA, hvB, hC⟩
    · refine ⟨C :: π', IsDerivation.ax hd' hF, Nat.succ_le_succ hlen', ?_, ?_⟩
      · intro X hX
        rcases List.mem_cons.mp hX with hXC | hXr
        · rw [hXC]; exact ⟨C, List.mem_cons_self, Finset.Subset.rfl⟩
        · obtain ⟨D, hD, hDX⟩ := hcov X hXr
          exact ⟨D, List.mem_cons_of_mem C hD, hDX⟩
      · intro D hD
        rcases List.mem_cons.mp hD with hDC | hDr
        · rw [hDC]; exact ⟨C, List.mem_cons_self, Finset.Subset.rfl⟩
        · obtain ⟨X, hX, hDX⟩ := hsub D hDr
          exact ⟨X, List.mem_cons_of_mem C hX, hDX⟩
    · refine ⟨π', hd', Nat.le_succ_of_le hlen', ?_, ?_⟩
      · intro X hX
        rcases List.mem_cons.mp hX with hXC | hXr
        · rw [hXC]
          obtain ⟨D, hD, hDA⟩ := hcov A hA
          exact ⟨D, hD, Finset.Subset.trans hDA hAC⟩
        · exact hcov X hXr
      · intro D hD
        obtain ⟨X, hX, hDX⟩ := hsub D hD
        exact ⟨X, List.mem_cons_of_mem C hX, hDX⟩
    · obtain ⟨A', hA', hAA'⟩ := hcov A hA
      obtain ⟨B', hB', hBB'⟩ := hcov B hB
      by_cases h1 : (v, true) ∈ A'
      · by_cases h2 : (v, false) ∈ B'
        · let R' : Clause V := A'.erase (v, true) ∪ B'.erase (v, false)
          have hR'C : R' ⊆ C := by
            rw [hC]
            exact Finset.union_subset_union (Finset.erase_subset_erase _ hAA')
              (Finset.erase_subset_erase _ hBB')
          refine ⟨R' :: π', IsDerivation.res hd' hA' hB' ⟨v, h1, h2, rfl⟩,
            Nat.succ_le_succ hlen', ?_, ?_⟩
          · intro X hX
            rcases List.mem_cons.mp hX with hXC | hXr
            · rw [hXC]; exact ⟨R', List.mem_cons_self, hR'C⟩
            · obtain ⟨D, hD, hDX⟩ := hcov X hXr
              exact ⟨D, List.mem_cons_of_mem R' hD, hDX⟩
          · intro D hD
            rcases List.mem_cons.mp hD with hDR | hDr
            · rw [hDR]; exact ⟨C, List.mem_cons_self, hR'C⟩
            · obtain ⟨X, hX, hDX⟩ := hsub D hDr
              exact ⟨X, List.mem_cons_of_mem C hX, hDX⟩
        · have hB'C : B' ⊆ C := by
            intro l hl
            rw [hC]
            apply Finset.mem_union_right
            exact Finset.mem_erase.mpr ⟨fun heq => h2 (heq ▸ hl), hBB' hl⟩
          refine ⟨π', hd', Nat.le_succ_of_le hlen', ?_, ?_⟩
          · intro X hX
            rcases List.mem_cons.mp hX with hXC | hXr
            · rw [hXC]; exact ⟨B', hB', hB'C⟩
            · exact hcov X hXr
          · intro D hD
            obtain ⟨X, hX, hDX⟩ := hsub D hD
            exact ⟨X, List.mem_cons_of_mem C hX, hDX⟩
      · have hA'C : A' ⊆ C := by
          intro l hl
          rw [hC]
          apply Finset.mem_union_left
          exact Finset.mem_erase.mpr ⟨fun heq => h1 (heq ▸ hl), hAA' hl⟩
        refine ⟨π', hd', Nat.le_succ_of_le hlen', ?_, ?_⟩
        · intro X hX
          rcases List.mem_cons.mp hX with hXC | hXr
          · rw [hXC]; exact ⟨A', hA', hA'C⟩
          · exact hcov X hXr
        · intro D hD
          obtain ⟨X, hX, hDX⟩ := hsub D hD
          exact ⟨X, List.mem_cons_of_mem C hX, hDX⟩

private def ClauseVarsLt (B : ℕ) (C : Clause ℕ) : Prop :=
  ∀ l ∈ C, l.1 < B

private def mapClause {V : Type} [DecidableEq V] (f : ℕ → V) (C : Clause ℕ) : Clause V :=
  C.image (fun l => (f l.1, l.2))

private lemma mapClause_erase {V : Type} [DecidableEq V] {f : ℕ → V} {B : ℕ}
    (hinj : ∀ a b, a < B → b < B → f a = f b → a = b)
    {C : Clause ℕ} (hC : ClauseVarsLt B C) (v : ℕ) (hv : v < B) (s : Bool) :
    mapClause f (C.erase (v, s)) = (mapClause f C).erase (f v, s) := by
  ext ⟨u, b⟩
  simp only [mapClause, Finset.mem_image, Finset.mem_erase, Prod.mk.injEq, ne_eq]
  constructor
  · rintro ⟨⟨w, s'⟩, ⟨hne, hwC⟩, hfw, hsb⟩
    refine ⟨?_, ⟨w, s'⟩, hwC, hfw, hsb⟩
    rintro ⟨hu, hb⟩
    apply hne
    exact Prod.ext (hinj w v (hC _ hwC) hv (hfw.trans hu)) (hsb.trans hb)
  · rintro ⟨hne, ⟨w, s'⟩, hwC, hfw, hsb⟩
    refine ⟨⟨w, s'⟩, ⟨?_, hwC⟩, hfw, hsb⟩
    intro heq
    rcases Prod.mk.inj heq with ⟨hw, hs⟩
    apply hne
    exact ⟨by rw [← hfw, hw], by rw [← hsb, hs]⟩

private lemma map_isDerivation {V : Type} [DecidableEq V] {F : Set (Clause ℕ)}
    {F' : Set (Clause V)} {f : ℕ → V} {B : ℕ}
    (hinj : ∀ a b, a < B → b < B → f a = f b → a = b)
    (hF : ∀ C ∈ F, ClauseVarsLt B C → mapClause f C ∈ F')
    {π : List (Clause ℕ)} (hπ : IsDerivation F π) (hB : ∀ C ∈ π, ClauseVarsLt B C) :
    IsDerivation F' (π.map (mapClause f)) := by
  induction hπ with
  | nil => exact IsDerivation.nil
  | ax hd hax ih =>
    have hBrest : ∀ D ∈ _, ClauseVarsLt B D := fun D hD => hB D (List.mem_cons_of_mem _ hD)
    have hBC : ClauseVarsLt B _ := hB _ List.mem_cons_self
    exact IsDerivation.ax (ih hBrest) (hF _ hax hBC)
  | @res π C D R hd hC hD hres ih =>
    have hBrest : ∀ X ∈ π, ClauseVarsLt B X := fun X hX => hB X (List.mem_cons_of_mem _ hX)
    have hBC : ClauseVarsLt B C := hBrest C hC
    have hBD : ClauseVarsLt B D := hBrest D hD
    obtain ⟨v, hvC, hvD, hR⟩ := hres
    have hvB : v < B := hBC (v, true) hvC
    refine IsDerivation.res (ih hBrest) (List.mem_map_of_mem hC) (List.mem_map_of_mem hD)
      ⟨f v, ?_, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(v, true), hvC, rfl⟩
    · exact Finset.mem_image.mpr ⟨(v, false), hvD, rfl⟩
    · rw [hR]
      simp only [mapClause, Finset.image_union]
      rw [← mapClause, ← mapClause, mapClause_erase hinj hBC v hvB true,
        mapClause_erase hinj hBD v hvB false]
      rfl

private def Derivable (F : Set (Clause ℕ)) (B W L : ℕ) (S : Set (Clause ℕ)) : Prop :=
  ∃ π : List (Clause ℕ), IsWeakDeriv F π ∧ π.length ≤ L ∧
    (∀ C ∈ π, C.card ≤ W ∧ ClauseVarsLt B C) ∧ ∀ C ∈ S, C ∈ π

private lemma derivable_empty (F : Set (Clause ℕ)) (B W : ℕ) :
    Derivable F B W 0 ∅ :=
  ⟨[], trivial, le_rfl, fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h (Set.notMem_empty _)⟩

private lemma derivable_mono {F₁ F₂ : Set (Clause ℕ)} {B₁ B₂ W₁ W₂ L₁ L₂ : ℕ}
    {S₁ S₂ : Set (Clause ℕ)}
    (h : Derivable F₁ B₁ W₁ L₁ S₁)
    (hF : F₁ ⊆ F₂) (hB : B₁ ≤ B₂) (hW : W₁ ≤ W₂) (hL : L₁ ≤ L₂) (hS : S₂ ⊆ S₁) :
    Derivable F₂ B₂ W₂ L₂ S₂ := by
  obtain ⟨π, hd, hlen, hwb, hcov⟩ := h
  refine ⟨π, isWeakDeriv_mono hF hd, le_trans hlen hL, ?_, fun C hC => hcov C (hS hC)⟩
  intro C hC
  exact ⟨le_trans (hwb C hC).1 hW, fun l hl => lt_of_lt_of_le ((hwb C hC).2 l hl) hB⟩

private lemma derivable_union {F : Set (Clause ℕ)} {B W L₁ L₂ : ℕ} {S₁ S₂ : Set (Clause ℕ)}
    (h₁ : Derivable F B W L₁ S₁) (h₂ : Derivable F B W L₂ S₂) :
    Derivable F B W (L₁ + L₂) (S₁ ∪ S₂) := by
  obtain ⟨π₁, hd₁, hl₁, hwb₁, hc₁⟩ := h₁
  obtain ⟨π₂, hd₂, hl₂, hwb₂, hc₂⟩ := h₂
  refine ⟨π₂ ++ π₁, isWeakDeriv_append hd₁ (isWeakDeriv_mono Set.subset_union_left hd₂), ?_, ?_, ?_⟩
  · rw [List.length_append]; omega
  · intro C hC
    rcases List.mem_append.mp hC with h | h
    · exact hwb₂ C h
    · exact hwb₁ C h
  · intro C hC
    rcases hC with h | h
    · exact List.mem_append_right π₂ (hc₁ C h)
    · exact List.mem_append_left π₁ (hc₂ C h)

private lemma derivable_trans {F : Set (Clause ℕ)} {B W L₁ L₂ : ℕ} {S₁ S₂ : Set (Clause ℕ)}
    (h₁ : Derivable F B W L₁ S₁) (h₂ : Derivable (F ∪ S₁) B W L₂ S₂) :
    Derivable F B W (L₁ + L₂) (S₁ ∪ S₂) := by
  obtain ⟨π₁, hd₁, hl₁, hwb₁, hc₁⟩ := h₁
  obtain ⟨π₂, hd₂, hl₂, hwb₂, hc₂⟩ := h₂
  have hsub : F ∪ S₁ ⊆ F ∪ {A | A ∈ π₁} :=
    Set.union_subset_union_right F (fun A hA => hc₁ A hA)
  refine ⟨π₂ ++ π₁, isWeakDeriv_append hd₁ (isWeakDeriv_mono hsub hd₂), ?_, ?_, ?_⟩
  · rw [List.length_append]; omega
  · intro C hC
    rcases List.mem_append.mp hC with h | h
    · exact hwb₂ C h
    · exact hwb₁ C h
  · intro C hC
    rcases hC with h | h
    · exact List.mem_append_right π₂ (hc₁ C h)
    · exact List.mem_append_left π₁ (hc₂ C h)

private lemma derivable_trans_only {F : Set (Clause ℕ)} {B W L₁ L₂ : ℕ} {S₁ S₂ : Set (Clause ℕ)}
    (h₁ : Derivable F B W L₁ S₁) (h₂ : Derivable (F ∪ S₁) B W L₂ S₂) :
    Derivable F B W (L₁ + L₂) S₂ :=
  derivable_mono (derivable_trans h₁ h₂) Set.Subset.rfl le_rfl le_rfl le_rfl Set.subset_union_right

private lemma derivable_biUnion {ι : Type*} [DecidableEq ι] {F : Set (Clause ℕ)} {B W : ℕ}
    (s : Finset ι) (L : ι → ℕ) (S : ι → Set (Clause ℕ))
    (h : ∀ i ∈ s, Derivable F B W (L i) (S i)) :
    Derivable F B W (∑ i ∈ s, L i) (⋃ i ∈ s, S i) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using derivable_empty F B W
  | @insert a t ha ih =>
    have h1 := h a (Finset.mem_insert_self a t)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hu := derivable_union h1 h2
    rw [Finset.sum_insert ha]
    refine derivable_mono hu Set.Subset.rfl le_rfl le_rfl le_rfl ?_
    intro C hC
    simp only [Set.mem_iUnion, Finset.mem_insert] at hC ⊢
    rcases hC with ⟨i, rfl | hit, hCi⟩
    · exact Or.inl hCi
    · exact Or.inr (Set.mem_biUnion hit hCi)

private lemma derivable_range_chain {F : Set (Clause ℕ)} {B W L₀ Lstep : ℕ}
    (Inv Emit : ℕ → Set (Clause ℕ)) (k : ℕ)
    (h0 : Derivable F B W L₀ (Inv 0))
    (hstep : ∀ i < k, Derivable (F ∪ Inv i) B W Lstep (Inv (i + 1) ∪ Emit i)) :
    Derivable F B W (L₀ + k * Lstep) (Inv k ∪ ⋃ i ∈ Finset.range k, Emit i) := by
  induction k with
  | zero =>
    simpa using derivable_mono h0 Set.Subset.rfl le_rfl le_rfl le_rfl Set.Subset.rfl
  | succ k ih =>
    have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
    have hnext := hstep k (Nat.lt_succ_self k)
    have hnext' : Derivable (F ∪ (Inv k ∪ ⋃ i ∈ Finset.range k, Emit i)) B W Lstep
        (Inv (k + 1) ∪ Emit k) :=
      derivable_mono hnext (Set.union_subset_union_right F Set.subset_union_left)
        le_rfl le_rfl le_rfl Set.Subset.rfl
    have htr := derivable_trans hprev hnext'
    refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl (by rw [Nat.succ_mul]; omega) ?_
    intro C hC
    rcases hC with hInv | hEm
    · exact Or.inr (Or.inl hInv)
    · simp only [Set.mem_iUnion, Finset.mem_range] at hEm
      rcases hEm with ⟨i, hi, hCi⟩
      by_cases hik : i = k
      · subst hik; exact Or.inr (Or.inr hCi)
      · exact Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hCi))

private def NonTaut (C : Clause ℕ) : Prop :=
  ∀ v : ℕ, ¬ ((v, true) ∈ C ∧ (v, false) ∈ C)

private lemma card_le_of_nonTaut {S : Finset ℕ} {C : Clause ℕ}
    (hnt : NonTaut C) (hvars : ∀ l ∈ C, l.1 ∈ S) : C.card ≤ S.card := by
  have hinj : Set.InjOn Prod.fst (C : Set (Literal ℕ)) := by
    rintro ⟨v₁, b₁⟩ h₁ ⟨v₂, b₂⟩ h₂ (rfl : v₁ = v₂)
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd ⟨h₂, h₁⟩ (hnt v₁)
    · exact absurd ⟨h₁, h₂⟩ (hnt v₁)
    · rfl
  have hsub : C.image Prod.fst ⊆ S := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨l, hl, rfl⟩
    exact hvars l hl
  calc C.card = (C.image Prod.fst).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ S.card := Finset.card_le_card hsub

private lemma nonTaut_of_not_clauseSat {x : ℕ → Bool} {C : Clause ℕ}
    (h : ¬ ClauseSat x C) : NonTaut C := by
  intro v ⟨hT, hF⟩
  cases hx : x v
  · exact h ⟨(v, false), hF, hx⟩
  · exact h ⟨(v, true), hT, hx⟩

private lemma derive_semantic_list {F H : Set (Clause ℕ)} {B : ℕ} {S : Finset ℕ}
    (hHF : H ⊆ F) (hSB : ∀ v ∈ S, v < B) (hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S)
    (L : List ℕ) :
    ∀ T : Clause ℕ, NonTaut T → (∀ l ∈ T, l.1 ∈ S) →
      (∀ v ∈ S, (v, true) ∈ T ∨ (v, false) ∈ T ∨ v ∈ L) →
      (∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → ClauseSat x T) →
      Derivable F B S.card (3 * 2 ^ L.length - 1) {T} := by
  induction L with
  | nil =>
    intro T hnt hTS hcov hsem
    let x : ℕ → Bool := fun v => decide ((v, false) ∈ T)
    have hxT : ¬ ClauseSat x T := by
      rintro ⟨⟨v, b⟩, hvT, hxb⟩
      cases b
      · have : (v, false) ∉ T := by simpa [x] using hxb
        exact this hvT
      · have : (v, false) ∈ T := by simpa [x] using hxb
        exact hnt v ⟨hvT, this⟩
    have hex : ∃ C ∈ H, ¬ ClauseSat x C := by
      by_contra hall
      push Not at hall
      exact hxT (hsem x hall)
    obtain ⟨C, hCH, hxC⟩ := hex
    have hCT : C ⊆ T := by
      intro ⟨v, b⟩ hlC
      have hvS : v ∈ S := hHS C hCH (v, b) hlC
      have hxb : x v ≠ b := fun heq => hxC ⟨(v, b), hlC, heq⟩
      cases b
      · have : x v = true := by cases hxv : x v <;> simp_all
        simpa [x] using this
      · have hxf : x v = false := by cases hxv : x v <;> simp_all
        have hnf : (v, false) ∉ T := by simpa [x] using hxf
        rcases hcov v hvS with hT | hF | hnil
        · exact hT
        · exact absurd hF hnf
        · exact absurd hnil List.not_mem_nil
    have hCcard : C.card ≤ S.card := card_le_of_nonTaut (nonTaut_of_not_clauseSat hxC) (hHS C hCH)
    have hTcard : T.card ≤ S.card := card_le_of_nonTaut hnt hTS
    refine ⟨[T, C], ⟨⟨trivial, Or.inl (hHF hCH)⟩, Or.inr (Or.inl ⟨C, List.mem_cons_self, hCT⟩)⟩,
      by simp, ?_, ?_⟩
    · intro D hD
      rcases List.mem_cons.mp hD with hDT | hD'
      · rw [hDT]; exact ⟨hTcard, fun l hl => hSB l.1 (hTS l hl)⟩
      · rcases List.mem_cons.mp hD' with hDC | hnil
        · rw [hDC]; exact ⟨hCcard, fun l hl => hSB l.1 (hHS C hCH l hl)⟩
        · exact absurd hnil List.not_mem_nil
    · intro D hD
      rw [Set.mem_singleton_iff.mp hD]
      exact List.mem_cons_self
  | cons u rest ih =>
    intro T hnt hTS hcov hsem
    have hpow : 3 * 2 ^ rest.length - 1 ≤ 3 * 2 ^ (rest.length + 1) - 1 := by
      have : 2 ^ rest.length ≤ 2 ^ (rest.length + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ _)
      omega
    by_cases hu : (u, true) ∈ T ∨ (u, false) ∈ T ∨ u ∉ S
    · have hcov' : ∀ v ∈ S, (v, true) ∈ T ∨ (v, false) ∈ T ∨ v ∈ rest := by
        intro v hvS
        rcases hcov v hvS with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr (Or.inl h2)
        · rcases List.mem_cons.mp h3 with rfl | hr
          · rcases hu with hT | hF | hnS
            · exact Or.inl hT
            · exact Or.inr (Or.inl hF)
            · exact absurd hvS hnS
          · exact Or.inr (Or.inr hr)
      exact derivable_mono (ih T hnt hTS hcov' hsem) Set.Subset.rfl le_rfl le_rfl hpow Set.Subset.rfl
    · push Not at hu
      obtain ⟨huT, huF, huS⟩ := hu
      let T₁ : Clause ℕ := insert (u, true) T
      let T₂ : Clause ℕ := insert (u, false) T
      have hnt1 : NonTaut T₁ := by
        intro v ⟨h1, h2⟩
        simp only [T₁, Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨rfl, _⟩ | h1 <;> rcases h2 with ⟨_, hff⟩ | h2
        · cases hff
        · exact huF h2
        · cases hff
        · exact hnt v ⟨h1, h2⟩
      have hnt2 : NonTaut T₂ := by
        intro v ⟨h1, h2⟩
        simp only [T₂, Finset.mem_insert, Prod.mk.injEq] at h1 h2
        rcases h1 with ⟨_, hft⟩ | h1 <;> rcases h2 with ⟨rfl, _⟩ | h2
        · cases hft
        · cases hft
        · exact huT h1
        · exact hnt v ⟨h1, h2⟩
      have hT1S : ∀ l ∈ T₁, l.1 ∈ S := by
        intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hlT
        · exact huS
        · exact hTS l hlT
      have hT2S : ∀ l ∈ T₂, l.1 ∈ S := by
        intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hlT
        · exact huS
        · exact hTS l hlT
      have hcov1 : ∀ v ∈ S, (v, true) ∈ T₁ ∨ (v, false) ∈ T₁ ∨ v ∈ rest := by
        intro v hvS
        rcases hcov v hvS with h1 | h2 | h3
        · exact Or.inl (Finset.mem_insert_of_mem h1)
        · exact Or.inr (Or.inl (Finset.mem_insert_of_mem h2))
        · rcases List.mem_cons.mp h3 with rfl | hr
          · exact Or.inl (Finset.mem_insert_self _ _)
          · exact Or.inr (Or.inr hr)
      have hcov2 : ∀ v ∈ S, (v, true) ∈ T₂ ∨ (v, false) ∈ T₂ ∨ v ∈ rest := by
        intro v hvS
        rcases hcov v hvS with h1 | h2 | h3
        · exact Or.inl (Finset.mem_insert_of_mem h1)
        · exact Or.inr (Or.inl (Finset.mem_insert_of_mem h2))
        · rcases List.mem_cons.mp h3 with rfl | hr
          · exact Or.inr (Or.inl (Finset.mem_insert_self _ _))
          · exact Or.inr (Or.inr hr)
      have hsem1 : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → ClauseSat x T₁ := by
        intro x hx
        obtain ⟨l, hl, hxl⟩ := hsem x hx
        exact ⟨l, Finset.mem_insert_of_mem hl, hxl⟩
      have hsem2 : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → ClauseSat x T₂ := by
        intro x hx
        obtain ⟨l, hl, hxl⟩ := hsem x hx
        exact ⟨l, Finset.mem_insert_of_mem hl, hxl⟩
      obtain ⟨π₁, hd₁, hl₁, hwb₁, hc₁⟩ := ih T₁ hnt1 hT1S hcov1 hsem1
      obtain ⟨π₂, hd₂, hl₂, hwb₂, hc₂⟩ := ih T₂ hnt2 hT2S hcov2 hsem2
      have hres : IsResolvent T₁ T₂ T := by
        refine ⟨u, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.erase_insert huT, Finset.erase_insert huF, Finset.union_idempotent]
      have hd12 : IsWeakDeriv F (π₁ ++ π₂) :=
        isWeakDeriv_append hd₂ (isWeakDeriv_mono Set.subset_union_left hd₁)
      have hT1m : T₁ ∈ π₁ ++ π₂ := List.mem_append_left π₂ (hc₁ T₁ rfl)
      have hT2m : T₂ ∈ π₁ ++ π₂ := List.mem_append_right π₁ (hc₂ T₂ rfl)
      have hTcard : T.card ≤ S.card := card_le_of_nonTaut hnt hTS
      refine ⟨T :: (π₁ ++ π₂), ⟨hd12, Or.inr (Or.inr ⟨T₁, hT1m, T₂, hT2m, hres⟩)⟩, ?_, ?_, ?_⟩
      · simp only [List.length_cons, List.length_append]
        have hpos : 1 ≤ 3 * 2 ^ rest.length := by
          have : 1 ≤ 2 ^ rest.length := Nat.one_le_two_pow
          omega
        have hexp : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
          rw [Nat.pow_succ]; omega
        omega
      · intro D hD
        rcases List.mem_cons.mp hD with hDT | hD'
        · rw [hDT]; exact ⟨hTcard, fun l hl => hSB l.1 (hTS l hl)⟩
        · rcases List.mem_append.mp hD' with h1 | h2
          · exact hwb₁ D h1
          · exact hwb₂ D h2
      · intro D hD
        rw [Set.mem_singleton_iff.mp hD]
        exact List.mem_cons_self

private lemma derive_semantic {F H : Set (Clause ℕ)} {B : ℕ} {S : Finset ℕ} {T : Clause ℕ}
    (hHF : H ⊆ F) (hSB : ∀ v ∈ S, v < B) (hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S)
    (hnt : NonTaut T) (hTS : ∀ l ∈ T, l.1 ∈ S)
    (hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → ClauseSat x T) :
    Derivable F B S.card (3 * 2 ^ S.card) {T} := by
  have h := derive_semantic_list hHF hSB hHS S.toList T hnt hTS
    (fun v hv => Or.inr (Or.inr (Finset.mem_toList.mpr hv))) hsem
  refine derivable_mono h Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
  rw [Finset.length_toList]
  exact Nat.sub_le _ _

private def forbidClause (O : Finset ℕ) (α : ℕ → Bool) : Clause ℕ :=
  O.image (fun v => (v, !(α v)))

private def fullCNF (O : Finset ℕ) (P : (ℕ → Bool) → Prop) : Set (Clause ℕ) :=
  {C | ∃ α : ℕ → Bool, ¬ P α ∧ C = forbidClause O α}

private def DependsOn (O : Finset ℕ) (P : (ℕ → Bool) → Prop) : Prop :=
  ∀ x y : ℕ → Bool, (∀ v ∈ O, x v = y v) → (P x ↔ P y)

private lemma forbidClause_nonTaut (O : Finset ℕ) (α : ℕ → Bool) :
    NonTaut (forbidClause O α) := by
  intro v ⟨hT, hF⟩
  rcases Finset.mem_image.mp hT with ⟨w₁, _, h₁⟩
  rcases Finset.mem_image.mp hF with ⟨w₂, _, h₂⟩
  simp only [Prod.mk.injEq] at h₁ h₂
  rcases h₁ with ⟨rfl, hb1⟩
  rcases h₂ with ⟨rfl, hb2⟩
  rw [hb1] at hb2
  cases hb2

private lemma forbidClause_vars (O : Finset ℕ) (α : ℕ → Bool) :
    ∀ l ∈ forbidClause O α, l.1 ∈ O := by
  intro l hl
  rcases Finset.mem_image.mp hl with ⟨v, hv, rfl⟩
  exact hv

private lemma fullCNF_vars (O : Finset ℕ) (P : (ℕ → Bool) → Prop) :
    ∀ C ∈ fullCNF O P, ∀ l ∈ C, l.1 ∈ O := by
  rintro C ⟨α, -, rfl⟩
  exact forbidClause_vars O α

private lemma fullCNF_vars_subset {O S : Finset ℕ} {P : (ℕ → Bool) → Prop} (hOS : O ⊆ S) :
    ∀ C ∈ fullCNF O P, ∀ l ∈ C, l.1 ∈ S :=
  fun C hC l hl => hOS (fullCNF_vars O P C hC l hl)

private lemma forbidClause_sat_iff (O : Finset ℕ) (α x : ℕ → Bool) :
    ClauseSat x (forbidClause O α) ↔ ∃ v ∈ O, x v ≠ α v := by
  constructor
  · rintro ⟨l, hl, hxl⟩
    rcases Finset.mem_image.mp hl with ⟨v, hv, rfl⟩
    refine ⟨v, hv, ?_⟩
    simp only at hxl
    cases h : α v <;> simp_all
  · rintro ⟨v, hv, hne⟩
    refine ⟨(v, !(α v)), Finset.mem_image.mpr ⟨v, hv, rfl⟩, ?_⟩
    cases h1 : x v <;> cases h2 : α v <;> simp_all

private lemma fullCNF_sat_iff {O : Finset ℕ} {P : (ℕ → Bool) → Prop}
    (hdep : DependsOn O P) (x : ℕ → Bool) :
    (∀ C ∈ fullCNF O P, ClauseSat x C) ↔ P x := by
  constructor
  · intro hsat
    by_contra hPx
    have hmem : forbidClause O x ∈ fullCNF O P := ⟨x, hPx, rfl⟩
    obtain ⟨v, _, hne⟩ := (forbidClause_sat_iff O x x).mp (hsat _ hmem)
    exact hne rfl
  · rintro hPx C ⟨α, hPa, rfl⟩
    rw [forbidClause_sat_iff]
    by_contra hall
    push Not at hall
    exact hPa ((hdep x α hall).mp hPx)

private lemma derive_fullCNF {F H : Set (Clause ℕ)} {B : ℕ} {S O : Finset ℕ}
    {P : (ℕ → Bool) → Prop}
    (hHF : H ⊆ F) (hSB : ∀ v ∈ S, v < B) (hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S)
    (hOS : O ⊆ S) (hdep : DependsOn O P)
    (hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → P x) :
    Derivable F B S.card (3 * 2 ^ (O.card + S.card)) (fullCNF O P) := by
  classical
  let extFn : (O → Bool) → (ℕ → Bool) := fun f v => if hv : v ∈ O then f ⟨v, hv⟩ else false
  let bad : Finset (O → Bool) := Finset.univ.filter (fun f => ¬ P (extFn f))
  have hsingle : ∀ f ∈ bad, Derivable F B S.card (3 * 2 ^ S.card) {forbidClause O (extFn f)} := by
    intro f hf
    have hP : ¬ P (extFn f) := (Finset.mem_filter.mp hf).2
    refine derive_semantic hHF hSB hHS (forbidClause_nonTaut O (extFn f))
      (fun l hl => hOS (forbidClause_vars O (extFn f) l hl)) ?_
    intro x hx
    exact (fullCNF_sat_iff hdep x).mpr (hsem x hx) _ ⟨extFn f, hP, rfl⟩
  have hu := derivable_biUnion bad (fun _ => 3 * 2 ^ S.card)
    (fun f => {forbidClause O (extFn f)}) hsingle
  have hlen : ∑ _ ∈ bad, 3 * 2 ^ S.card ≤ 3 * 2 ^ (O.card + S.card) := by
    rw [Finset.sum_const, smul_eq_mul]
    have hbad : bad.card ≤ 2 ^ O.card := by
      calc bad.card ≤ (Finset.univ : Finset (O → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ O.card := by simp
    calc bad.card * (3 * 2 ^ S.card)
        ≤ 2 ^ O.card * (3 * 2 ^ S.card) := Nat.mul_le_mul_right _ hbad
      _ = 3 * 2 ^ (O.card + S.card) := by rw [Nat.pow_add]; ring
  refine derivable_mono hu Set.Subset.rfl le_rfl le_rfl hlen ?_
  rintro C ⟨α, hPa, rfl⟩
  let f : O → Bool := fun v => α v.1
  have heq : ∀ v ∈ O, extFn f v = α v := by
    intro v hv; simp [extFn, f, hv]
  have hfbad : f ∈ bad := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ f, ?_⟩
    intro hPf
    exact hPa ((hdep (extFn f) α heq).mp hPf)
  have hfc : forbidClause O α = forbidClause O (extFn f) := by
    ext ⟨v, s⟩
    simp only [forbidClause, Finset.mem_image, Prod.mk.injEq]
    constructor <;> rintro ⟨w, hw, rfl, rfl⟩ <;> exact ⟨w, hw, rfl, by rw [heq w hw]⟩
  exact Set.mem_biUnion hfbad (by simp [hfc])

end WeakResolution

section NandCircuits

private def ValidCirc (n : ℕ) (G : List (ℕ × ℕ)) : Prop :=
  ∀ i (hi : i < G.length), G[i].1 < n + i ∧ G[i].2 < n + i

private def nandClauses (z a b : ℕ) : Set (Clause ℕ) :=
  {{(z, false), (a, false), (b, false)}, {(z, true), (a, true)}, {(z, true), (b, true)}}

private def HasNand (n : ℕ) (G : List (ℕ × ℕ)) (z a b : ℕ) : Prop :=
  ∃ i : Fin G.length, z = n + i.val ∧ G[i.val] = (a, b)

private def allGateClauses (n : ℕ) (G : List (ℕ × ℕ)) : Set (Clause ℕ) :=
  {D | ∃ i : Fin G.length, D ∈ nandClauses (n + i.val) G[i.val].1 G[i.val].2}

private lemma hasNand_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {z a b : ℕ}
    (hp : G₁ <+: G₂) (h : HasNand n G₁ z a b) : HasNand n G₂ z a b := by
  obtain ⟨⟨i, hi⟩, hz, hgi⟩ := h
  obtain ⟨t, rfl⟩ := hp
  refine ⟨⟨i, Nat.lt_of_lt_of_le hi (by simp)⟩, hz, ?_⟩
  rw [List.getElem_append_left hi, hgi]

private lemma allGateClauses_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} (hp : G₁ <+: G₂) :
    allGateClauses n G₁ ⊆ allGateClauses n G₂ := by
  rintro D ⟨⟨i, hi⟩, hD⟩
  obtain ⟨t, rfl⟩ := hp
  refine ⟨⟨i, Nat.lt_of_lt_of_le hi (by simp)⟩, ?_⟩
  simpa [List.getElem_append_left hi] using hD

private lemma hasNand_clauses_subset {n : ℕ} {G : List (ℕ × ℕ)} {z a b : ℕ}
    (h : HasNand n G z a b) : nandClauses z a b ⊆ allGateClauses n G := by
  obtain ⟨i, rfl, hgi⟩ := h
  intro D hD
  exact ⟨i, by simpa [hgi] using hD⟩

private lemma hasNand_lt {n : ℕ} {G : List (ℕ × ℕ)} {z a b : ℕ}
    (h : HasNand n G z a b) : z < n + G.length := by
  obtain ⟨i, rfl, -⟩ := h
  exact Nat.add_lt_add_left i.isLt n

private lemma nandClauses_vars_subset {z a b : ℕ} {S : Finset ℕ}
    (hz : z ∈ S) (ha : a ∈ S) (hb : b ∈ S) :
    ∀ C ∈ nandClauses z a b, ∀ l ∈ C, l.1 ∈ S := by
  intro C hC l hl
  rcases hC with rfl | rfl | rfl
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl <;> assumption
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> assumption
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> assumption

private lemma nandClauses_sat_iff (z a b : ℕ) (x : ℕ → Bool) :
    (∀ C ∈ nandClauses z a b, ClauseSat x C) ↔ x z = !(x a && x b) := by
  constructor
  · intro h
    have h1 := h _ (Or.inl rfl)
    have h2 := h _ (Or.inr (Or.inl rfl))
    have h3 := h _ (Or.inr (Or.inr rfl))
    simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
      exists_eq_left] at h1 h2 h3
    cases hxz : x z <;> cases hxa : x a <;> cases hxb : x b <;> simp_all
  · intro h C hC
    rcases hC with rfl | rfl | rfl
    · simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
        exists_eq_left]
      cases hxa : x a <;> cases hxb : x b <;> simp_all
    · simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
        exists_eq_left]
      cases hxa : x a <;> simp_all
    · simp only [ClauseSat, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp,
        exists_eq_left]
      cases hxb : x b <;> simp_all

private lemma exists_addGate {n : ℕ} {G : List (ℕ × ℕ)} (a b : ℕ)
    (hV : ValidCirc n G) (ha : a < n + G.length) (hb : b < n + G.length) :
    ∃ (G' : List (ℕ × ℕ)) (w : ℕ),
      G <+: G' ∧ G'.length = G.length + 1 ∧ ValidCirc n G' ∧
      HasNand n G' w a b ∧ w < n + G'.length := by
  refine ⟨G ++ [(a, b)], n + G.length, List.prefix_append G [(a, b)], by simp, ?_, ?_, by simp⟩
  · intro i hi
    rw [List.length_append] at hi
    by_cases hlt : i < G.length
    · rw [List.getElem_append_left hlt]
      exact hV i hlt
    · have heq : i = G.length := by simp at hi; omega
      subst heq
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨ha, hb⟩
  · exact ⟨⟨G.length, by simp⟩, rfl, by simp⟩

private def HasConsts (n : ℕ) (G : List (ℕ × ℕ)) (z0 o1 : ℕ) : Prop :=
  z0 < n + G.length ∧ o1 < n + G.length ∧
    ∃ w nv, w < n ∧ nv < n + G.length ∧
      HasNand n G nv w w ∧ HasNand n G o1 w nv ∧ HasNand n G z0 o1 o1

private lemma hasConsts_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {z0 o1 : ℕ}
    (hp : G₁ <+: G₂) (h : HasConsts n G₁ z0 o1) : HasConsts n G₂ z0 o1 := by
  have hle : G₁.length ≤ G₂.length := hp.length_le
  obtain ⟨hz, ho, w, nv, hw, hnv, h1, h2, h3⟩ := h
  exact ⟨by omega, by omega, w, nv, hw, by omega,
    hasNand_mono hp h1, hasNand_mono hp h2, hasNand_mono hp h3⟩

private lemma exists_addConsts (n : ℕ) (hn : 0 < n) :
    ∃ (G : List (ℕ × ℕ)) (z0 o1 : ℕ),
      G.length = 3 ∧ ValidCirc n G ∧ HasConsts n G z0 o1 := by
  have h0 : ValidCirc n [] := fun i hi => absurd hi (Nat.not_lt_zero i)
  obtain ⟨G1, w1, p1, l1, v1, n1, hw1⟩ := exists_addGate 0 0 h0 (by simp; omega) (by simp; omega)
  simp only [List.length_nil, zero_add] at l1
  obtain ⟨G2, w2, p2, l2, v2, n2, hw2⟩ := exists_addGate 0 w1 v1 (by omega) hw1
  obtain ⟨G3, w3, p3, l3, v3, n3, hw3⟩ := exists_addGate w2 w2 v2 hw2 hw2
  refine ⟨G3, w3, w2, by omega, v3, hw3, by omega, 0, w1, hn, by omega, ?_, ?_, n3⟩
  · exact hasNand_mono (p2.trans p3) n1
  · exact hasNand_mono p3 n2

private lemma derive_consts {n : ℕ} {G : List (ℕ × ℕ)} {z0 o1 : ℕ}
    (hc : HasConsts n G z0 o1) :
    Derivable (allGateClauses n G) (n + G.length) 4 (2 * (3 * 2 ^ 5))
      (fullCNF {z0} (fun x => x z0 = false) ∪ fullCNF {o1} (fun x => x o1 = true)) := by
  obtain ⟨hz, ho, w, nv, hw, hnv, h1, h2, h3⟩ := hc
  let S : Finset ℕ := {w, nv, o1, z0}
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> omega
  have hScard : S.card ≤ 4 := by
    dsimp only [S]
    have := Finset.card_insert_le w {nv, o1, z0}
    have := Finset.card_insert_le nv {o1, z0}
    have := Finset.card_insert_le o1 {z0}
    simp only [Finset.card_singleton] at *
    omega
  let H : Set (Clause ℕ) := nandClauses nv w w ∪ nandClauses o1 w nv ∪ nandClauses z0 o1 o1
  have hHF : H ⊆ allGateClauses n G := by
    intro C hC
    rcases hC with (h | h) | h
    · exact hasNand_clauses_subset h1 h
    · exact hasNand_clauses_subset h2 h
    · exact hasNand_clauses_subset h3 h
  have hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with (h | h) | h
    · exact nandClauses_vars_subset (by simp [S]) (by simp [S]) (by simp [S]) C h l hl
    · exact nandClauses_vars_subset (by simp [S]) (by simp [S]) (by simp [S]) C h l hl
    · exact nandClauses_vars_subset (by simp [S]) (by simp [S]) (by simp [S]) C h l hl
  have hsat : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → x z0 = false ∧ x o1 = true := by
    intro x hx
    have e1 : x nv = !(x w && x w) :=
      (nandClauses_sat_iff nv w w x).mp (fun C hC => hx C (Or.inl (Or.inl hC)))
    have e2 : x o1 = !(x w && x nv) :=
      (nandClauses_sat_iff o1 w nv x).mp (fun C hC => hx C (Or.inl (Or.inr hC)))
    have e3 : x z0 = !(x o1 && x o1) :=
      (nandClauses_sat_iff z0 o1 o1 x).mp (fun C hC => hx C (Or.inr hC))
    cases hxw : x w <;> simp_all
  have d1 := derive_fullCNF (O := {z0}) hHF hSB hHS (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [S, hv])
    (fun x y hxy => by rw [hxy z0 (Finset.mem_singleton_self _)])
    (fun x hx => (hsat x hx).1)
  have d2 := derive_fullCNF (O := {o1}) hHF hSB hHS (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [S, hv])
    (fun x y hxy => by rw [hxy o1 (Finset.mem_singleton_self _)])
    (fun x hx => (hsat x hx).2)
  have hpow : 3 * 2 ^ (1 + S.card) ≤ 3 * 2 ^ 5 :=
    Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega))
  have d1' := derivable_mono d1 Set.Subset.rfl le_rfl hScard (by simpa using hpow) Set.Subset.rfl
  have d2' := derivable_mono d2 Set.Subset.rfl le_rfl hScard (by simpa using hpow) Set.Subset.rfl
  exact derivable_mono (derivable_union d1' d2') Set.Subset.rfl le_rfl le_rfl (by omega) Set.Subset.rfl

private def HasFA (n : ℕ) (G : List (ℕ × ℕ)) (a b cin sum cout : ℕ) : Prop :=
  a < n + G.length ∧ b < n + G.length ∧ cin < n + G.length ∧
    sum < n + G.length ∧ cout < n + G.length ∧
    ∃ t1 t2 t3 x1 t4 t5 t6,
      t1 < n + G.length ∧ t2 < n + G.length ∧ t3 < n + G.length ∧
      x1 < n + G.length ∧ t4 < n + G.length ∧ t5 < n + G.length ∧ t6 < n + G.length ∧
      HasNand n G t1 a b ∧
      HasNand n G t2 a t1 ∧
      HasNand n G t3 b t1 ∧
      HasNand n G x1 t2 t3 ∧
      HasNand n G t4 x1 cin ∧
      HasNand n G t5 x1 t4 ∧
      HasNand n G t6 cin t4 ∧
      HasNand n G sum t5 t6 ∧
      HasNand n G cout t1 t4

private lemma hasFA_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {a b cin sum cout : ℕ}
    (hp : G₁ <+: G₂) (h : HasFA n G₁ a b cin sum cout) :
    HasFA n G₂ a b cin sum cout := by
  have hle : G₁.length ≤ G₂.length := hp.length_le
  obtain ⟨ha, hb, hc, hs, hco, t1, t2, t3, x1, t4, t5, t6,
    ht1, ht2, ht3, hx1, ht4, ht5, ht6, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  exact ⟨by omega, by omega, by omega, by omega, by omega,
    t1, t2, t3, x1, t4, t5, t6,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    hasNand_mono hp g1, hasNand_mono hp g2, hasNand_mono hp g3,
    hasNand_mono hp g4, hasNand_mono hp g5, hasNand_mono hp g6,
    hasNand_mono hp g7, hasNand_mono hp g8, hasNand_mono hp g9⟩

private lemma exists_addFA {n : ℕ} {G : List (ℕ × ℕ)} {a b cin : ℕ}
    (hV : ValidCirc n G) (ha : a < n + G.length) (hb : b < n + G.length) (hc : cin < n + G.length) :
    ∃ (G' : List (ℕ × ℕ)) (sum cout : ℕ),
      G <+: G' ∧ G'.length = G.length + 9 ∧ ValidCirc n G' ∧
      HasFA n G' a b cin sum cout := by
  obtain ⟨G1, w1, p1, l1, v1, n1, hw1⟩ := exists_addGate a b hV ha hb
  obtain ⟨G2, w2, p2, l2, v2, n2, hw2⟩ := exists_addGate a w1 v1 (by omega) hw1
  obtain ⟨G3, w3, p3, l3, v3, n3, hw3⟩ := exists_addGate b w1 v2 (by omega) (by omega)
  obtain ⟨G4, w4, p4, l4, v4, n4, hw4⟩ := exists_addGate w2 w3 v3 (by omega) hw3
  obtain ⟨G5, w5, p5, l5, v5, n5, hw5⟩ := exists_addGate w4 cin v4 hw4 (by omega)
  obtain ⟨G6, w6, p6, l6, v6, n6, hw6⟩ := exists_addGate w4 w5 v5 (by omega) hw5
  obtain ⟨G7, w7, p7, l7, v7, n7, hw7⟩ := exists_addGate cin w5 v6 (by omega) (by omega)
  obtain ⟨G8, w8, p8, l8, v8, n8, hw8⟩ := exists_addGate w6 w7 v7 (by omega) hw7
  obtain ⟨G9, w9, p9, l9, v9, n9, hw9⟩ := exists_addGate w1 w5 v8 (by omega) (by omega)
  refine ⟨G9, w8, w9,
    p1.trans (p2.trans (p3.trans (p4.trans (p5.trans (p6.trans (p7.trans (p8.trans p9))))))),
    by omega, v9,
    by omega, by omega, by omega, by omega, hw9,
    w1, w2, w3, w4, w5, w6, w7,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    hasNand_mono (p2.trans (p3.trans (p4.trans (p5.trans (p6.trans (p7.trans (p8.trans p9))))))) n1,
    hasNand_mono (p3.trans (p4.trans (p5.trans (p6.trans (p7.trans (p8.trans p9)))))) n2,
    hasNand_mono (p4.trans (p5.trans (p6.trans (p7.trans (p8.trans p9))))) n3,
    hasNand_mono (p5.trans (p6.trans (p7.trans (p8.trans p9)))) n4,
    hasNand_mono (p6.trans (p7.trans (p8.trans p9))) n5,
    hasNand_mono (p7.trans (p8.trans p9)) n6,
    hasNand_mono (p8.trans p9) n7,
    hasNand_mono p9 n8,
    n9⟩

private def faPred (a b cin sum cout : ℕ) (x : ℕ → Bool) : Prop :=
  (x a).toNat + (x b).toNat + (x cin).toNat = (x sum).toNat + 2 * (x cout).toNat

private def faCNF (a b cin sum cout : ℕ) : Set (Clause ℕ) :=
  fullCNF {a, b, cin, sum, cout} (faPred a b cin sum cout)

private lemma faPred_dependsOn (a b cin sum cout : ℕ) :
    DependsOn {a, b, cin, sum, cout} (faPred a b cin sum cout) := by
  intro x y hxy
  simp only [faPred, hxy a (by simp), hxy b (by simp), hxy cin (by simp),
    hxy sum (by simp), hxy cout (by simp)]

private lemma fa_wireSet {n : ℕ} {G : List (ℕ × ℕ)} {a b cin sum cout : ℕ}
    (h : HasFA n G a b cin sum cout) :
    ∃ (W : Finset ℕ) (H : Set (Clause ℕ)),
      W.card ≤ 9 ∧ (∀ v ∈ W, v < n + G.length) ∧
      sum ∈ W ∧ cout ∈ W ∧ H ⊆ allGateClauses n G ∧
      (∀ C ∈ H, ∀ l ∈ C, l.1 ∈ ({a, b, cin} ∪ W)) ∧
      (∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → faPred a b cin sum cout x) := by
  obtain ⟨ha, hb, hc, hs, hco, t1, t2, t3, x1, t4, t5, t6,
    ht1, ht2, ht3, hx1, ht4, ht5, ht6, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := h
  let W : Finset ℕ := {t1, t2, t3, x1, t4, t5, t6, sum, cout}
  let H : Set (Clause ℕ) :=
    nandClauses t1 a b ∪ nandClauses t2 a t1 ∪ nandClauses t3 b t1 ∪
    nandClauses x1 t2 t3 ∪ nandClauses t4 x1 cin ∪ nandClauses t5 x1 t4 ∪
    nandClauses t6 cin t4 ∪ nandClauses sum t5 t6 ∪ nandClauses cout t1 t4
  refine ⟨W, H, ?_, ?_, by simp [W], by simp [W], ?_, ?_, ?_⟩
  · dsimp only [W]
    have := Finset.card_insert_le t1 {t2, t3, x1, t4, t5, t6, sum, cout}
    have := Finset.card_insert_le t2 {t3, x1, t4, t5, t6, sum, cout}
    have := Finset.card_insert_le t3 {x1, t4, t5, t6, sum, cout}
    have := Finset.card_insert_le x1 {t4, t5, t6, sum, cout}
    have := Finset.card_insert_le t4 {t5, t6, sum, cout}
    have := Finset.card_insert_le t5 {t6, sum, cout}
    have := Finset.card_insert_le t6 {sum, cout}
    have := Finset.card_insert_le sum {cout}
    simp only [Finset.card_singleton] at *
    omega
  · intro v hv
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro C hC
    rcases hC with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
    · exact hasNand_clauses_subset g1 h
    · exact hasNand_clauses_subset g2 h
    · exact hasNand_clauses_subset g3 h
    · exact hasNand_clauses_subset g4 h
    · exact hasNand_clauses_subset g5 h
    · exact hasNand_clauses_subset g6 h
    · exact hasNand_clauses_subset g7 h
    · exact hasNand_clauses_subset g8 h
    · exact hasNand_clauses_subset g9 h
  · intro C hC l hl
    rcases hC with (((((((h | h) | h) | h) | h) | h) | h) | h) | h
    · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp [W]) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp [W]) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp [W]) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
    · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
  · intro x hx
    have e1 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hC)))))))))
    have e2 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hC)))))))))
    have e3 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hC))))))))
    have e4 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hC)))))))
    have e5 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hC))))))
    have e6 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inr hC)))))
    have e7 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
    have e8 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inr hC)))
    have e9 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inr hC))
    simp only [faPred, e8, e9, e7, e6, e5, e4, e3, e2, e1]
    cases x a <;> cases x b <;> cases x cin <;> rfl

private lemma derive_FA {n : ℕ} {G : List (ℕ × ℕ)} {a b cin sum cout : ℕ}
    (h : HasFA n G a b cin sum cout) :
    Derivable (allGateClauses n G) (n + G.length) 12 (3 * 2 ^ 17) (faCNF a b cin sum cout) := by
  obtain ⟨W, H, hWc, hWB, hsumW, hcoutW, hHF, hHS, hsem⟩ := fa_wireSet h
  let S : Finset ℕ := {a, b, cin} ∪ W
  have hScard : S.card ≤ 12 := by
    have h1 : ({a, b, cin} : Finset ℕ).card ≤ 3 := by
      have := Finset.card_insert_le a {b, cin}
      have := Finset.card_insert_le b {cin}
      simp only [Finset.card_singleton] at *; omega
    exact le_trans (Finset.card_union_le _ _) (by omega)
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    rcases Finset.mem_union.mp hv with h1 | h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl | rfl
      · exact h.1
      · exact h.2.1
      · exact h.2.2.1
    · exact hWB v h2
  have hOcard : ({a, b, cin, sum, cout} : Finset ℕ).card ≤ 5 := by
    have := Finset.card_insert_le a {b, cin, sum, cout}
    have := Finset.card_insert_le b {cin, sum, cout}
    have := Finset.card_insert_le cin {sum, cout}
    have := Finset.card_insert_le sum {cout}
    simp only [Finset.card_singleton] at *; omega
  have hOS : ({a, b, cin, sum, cout} : Finset ℕ) ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _ hsumW
    · exact Finset.mem_union_right _ hcoutW
  have hd := derive_fullCNF hHF hSB hHS hOS (faPred_dependsOn a b cin sum cout) hsem
  exact derivable_mono hd Set.Subset.rfl le_rfl hScard
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega))) Set.Subset.rfl

private def HasRipple (n : ℕ) (G : List (ℕ × ℕ)) (z0 k : ℕ)
    (A B S car : ℕ → ℕ) : Prop :=
  car 0 = z0 ∧
  (∀ i < k, HasFA n G (A i) (B i) (car i) (S i) (car (i + 1))) ∧
  S k = car k

private lemma hasRipple_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {z0 k : ℕ}
    {A B S car : ℕ → ℕ} (hp : G₁ <+: G₂) (h : HasRipple n G₁ z0 k A B S car) :
    HasRipple n G₂ z0 k A B S car :=
  ⟨h.1, fun i hi => hasFA_mono hp (h.2.1 i hi), h.2.2⟩

private lemma exists_addRipple {n : ℕ} {G : List (ℕ × ℕ)} {z0 : ℕ}
    (hV : ValidCirc n G) (hz : z0 < n + G.length) (k : ℕ) (A B : ℕ → ℕ)
    (hA : ∀ i < k, A i < n + G.length) (hB : ∀ i < k, B i < n + G.length) :
    ∃ (G' : List (ℕ × ℕ)) (S car : ℕ → ℕ),
      G <+: G' ∧ G'.length = G.length + 9 * k ∧ ValidCirc n G' ∧
      HasRipple n G' z0 k A B S car ∧
      (∀ i ≤ k, S i < n + G'.length ∧ car i < n + G'.length) := by
  induction k with
  | zero =>
    refine ⟨G, fun _ => z0, fun _ => z0, List.prefix_refl G, by simp, hV,
      ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i), rfl⟩,
      fun _ _ => ⟨hz, hz⟩⟩
  | succ k ih =>
    obtain ⟨G₁, S₁, car₁, hp₁, hl₁, hV₁, hr₁, hlt₁⟩ :=
      ih (fun i hi => hA i (Nat.lt_succ_of_lt hi)) (fun i hi => hB i (Nat.lt_succ_of_lt hi))
    have hA' : A k < n + G₁.length := by have := hA k (Nat.lt_succ_self k); omega
    have hB' : B k < n + G₁.length := by have := hB k (Nat.lt_succ_self k); omega
    have hc' : car₁ k < n + G₁.length := (hlt₁ k le_rfl).2
    obtain ⟨G₂, sumk, coutk, hp₂, hl₂, hV₂, hfa⟩ := exists_addFA hV₁ hA' hB' hc'
    let S₂ : ℕ → ℕ := fun i => if i = k then sumk else if i = k + 1 then coutk else S₁ i
    let car₂ : ℕ → ℕ := fun i => if i = k + 1 then coutk else car₁ i
    refine ⟨G₂, S₂, car₂, hp₁.trans hp₂, by omega, hV₂, ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [car₂, hr₁.1]
    · intro i hi
      by_cases hik : i = k
      · rw [hik]
        have hcar_k : car₂ k = car₁ k := by simp [car₂]
        have hcar_k1 : car₂ (k + 1) = coutk := by simp [car₂]
        have hS_k : S₂ k = sumk := by simp [S₂]
        rw [hcar_k, hcar_k1, hS_k]
        exact hfa
      · have hlt : i < k := by omega
        have hcar_i : car₂ i = car₁ i := by simp [car₂]; omega
        have hcar_i1 : car₂ (i + 1) = car₁ (i + 1) := by simp [car₂]; omega
        have hS_i : S₂ i = S₁ i := by
          have h1 : i ≠ k := by omega
          have h2 : i ≠ k + 1 := by omega
          simp [S₂, h1, h2]
        rw [hcar_i, hcar_i1, hS_i]
        exact hasFA_mono hp₂ (hr₁.2.1 i hlt)
    · simp [S₂, car₂]
    · intro i hi
      by_cases h1 : i = k + 1
      · rw [h1]; simp only [S₂, car₂, Nat.succ_ne_self, ↓reduceIte]
        exact ⟨hfa.2.2.2.2.1, hfa.2.2.2.2.1⟩
      · by_cases h2 : i = k
        · rw [h2]
          have hne : k ≠ k + 1 := Nat.ne_of_lt (Nat.lt_succ_self k)
          simp only [S₂, car₂, ↓reduceIte, hne]
          exact ⟨hfa.2.2.2.1, by have := hp₂.length_le; omega⟩
        · have hle : i ≤ k := by omega
          have hS : S₂ i = S₁ i := by simp [S₂, h2, h1]
          have hC : car₂ i = car₁ i := by simp [car₂, h1]
          rw [hS, hC]
          have := hlt₁ i hle
          have := hp₂.length_le
          omega

private def bitsVal (k : ℕ) (f : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range k, (f i).toNat * 2 ^ i

private lemma bitsVal_succ (k : ℕ) (f : ℕ → Bool) :
    bitsVal (k + 1) f = bitsVal k f + (f k).toNat * 2 ^ k := by
  simp [bitsVal, Finset.sum_range_succ]

private lemma ripple_wireSet {n : ℕ} {G : List (ℕ × ℕ)} {z0 k : ℕ} {A B S car : ℕ → ℕ}
    (hr : HasRipple n G z0 k A B S car) :
    ∃ (W : Finset ℕ) (H : Set (Clause ℕ)),
      W.card ≤ 9 * k ∧ (∀ v ∈ W, v < n + G.length) ∧
      (∀ i ≤ k, S i ∈ insert z0 W) ∧
      H ⊆ allGateClauses n G ∧
      (∀ C ∈ H, ∀ l ∈ C, l.1 ∈ (Finset.range k).image A ∪ (Finset.range k).image B ∪ insert z0 W) ∧
      (∀ x : ℕ → Bool, x z0 = false → (∀ C ∈ H, ClauseSat x C) →
        bitsVal (k + 1) (fun i => x (S i)) =
          bitsVal k (fun i => x (A i)) + bitsVal k (fun i => x (B i))) := by
  have haux : ∀ m ≤ k, ∃ (W : Finset ℕ) (H : Set (Clause ℕ)),
      W.card ≤ 9 * m ∧ (∀ v ∈ W, v < n + G.length) ∧
      (∀ i < m, S i ∈ W) ∧ car m ∈ insert z0 W ∧
      H ⊆ allGateClauses n G ∧
      (∀ C ∈ H, ∀ l ∈ C, l.1 ∈ (Finset.range m).image A ∪ (Finset.range m).image B ∪ insert z0 W) ∧
      (∀ x : ℕ → Bool, x z0 = false → (∀ C ∈ H, ClauseSat x C) →
        bitsVal m (fun i => x (S i)) + (x (car m)).toNat * 2 ^ m =
          bitsVal m (fun i => x (A i)) + bitsVal m (fun i => x (B i))) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨∅, ∅, by simp, fun _ h => absurd h (Finset.notMem_empty _),
        fun i hi => absurd hi (Nat.not_lt_zero i), by simp [hr.1], Set.empty_subset _,
        fun _ h => absurd h (Set.notMem_empty _), ?_⟩
      intro x hx0 _
      simp [bitsVal, hr.1, hx0]
    | succ m ih =>
      intro hmk
      obtain ⟨W₁, H₁, hWc1, hWB1, hSW1, hcm1, hHF1, hHS1, hval1⟩ := ih (Nat.le_of_succ_le hmk)
      obtain ⟨Wf, Hf, hWfc, hWfB, hSmW, hcmW, hHFf, hHSf, hsemf⟩ := fa_wireSet (hr.2.1 m hmk)
      refine ⟨W₁ ∪ Wf, H₁ ∪ Hf, ?_, ?_, ?_, ?_, Set.union_subset hHF1 hHFf, ?_, ?_⟩
      · exact le_trans (Finset.card_union_le _ _) (by omega)
      · intro v hv
        rcases Finset.mem_union.mp hv with h1 | h2
        · exact hWB1 v h1
        · exact hWfB v h2
      · intro i hi
        by_cases him : i = m
        · rw [him]; exact Finset.mem_union_right _ hSmW
        · exact Finset.mem_union_left _ (hSW1 i (by omega))
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hcmW)
      · intro C hC l hl
        rcases hC with h1 | h2
        · have hv := hHS1 C h1 l hl
          simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_insert] at hv ⊢
          rcases hv with (⟨i, hi, hiA⟩ | ⟨i, hi, hiB⟩) | (hlz | hw)
          · exact Or.inl (Or.inl ⟨i, Nat.lt_succ_of_lt hi, hiA⟩)
          · exact Or.inl (Or.inr ⟨i, Nat.lt_succ_of_lt hi, hiB⟩)
          · exact Or.inr (Or.inl hlz)
          · exact Or.inr (Or.inr (Or.inl hw))
        · have hv := hHSf C h2 l hl
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with (hA | hB | hcm) | hwf
          · rw [hA]
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), rfl⟩))
          · rw [hB]
            exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (Nat.lt_succ_self m), rfl⟩))
          · rw [hcm]
            rcases Finset.mem_insert.mp hcm1 with hcz | hcw
            · exact Finset.mem_union_right _ (by rw [hcz]; exact Finset.mem_insert_self _ _)
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ hcw))
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hwf))
      · intro x hx0 hxH
        have h1 := hval1 x hx0 (fun C hC => hxH C (Or.inl hC))
        have hf : (x (A m)).toNat + (x (B m)).toNat + (x (car m)).toNat =
            (x (S m)).toNat + 2 * (x (car (m + 1))).toNat :=
          hsemf x (fun C hC => hxH C (Or.inr hC))
        rw [bitsVal_succ, bitsVal_succ, bitsVal_succ]
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
        rw [hpow]
        have hf' : ((x (A m)).toNat + (x (B m)).toNat + (x (car m)).toNat) * 2 ^ m =
            ((x (S m)).toNat + 2 * (x (car (m + 1))).toNat) * 2 ^ m :=
          congrArg (· * 2 ^ m) hf
        ring_nf at hf' ⊢
        omega
  obtain ⟨W, H, hWc, hWB, hSW, hck, hHF, hHS, hval⟩ := haux k le_rfl
  refine ⟨W, H, hWc, hWB, ?_, hHF, hHS, ?_⟩
  · intro i hi
    by_cases hik : i = k
    · rw [hik, hr.2.2]; exact hck
    · exact Finset.mem_insert_of_mem (hSW i (by omega))
  · intro x hx0 hxH
    rw [bitsVal_succ, hr.2.2]
    exact hval x hx0 hxH

private def cmpBit (isGe target a prev : Bool) : Bool :=
  if isGe then
    if target then a && prev else a || prev
  else
    if target then (!a) || prev else (!a) && prev

private def HasCmpStep (n : ℕ) (G : List (ℕ × ℕ)) (isGe target : Bool)
    (bit prev out : ℕ) : Prop :=
  bit < n + G.length ∧ prev < n + G.length ∧ out < n + G.length ∧
  match isGe, target with
  | true, true => ∃ t, t < n + G.length ∧ HasNand n G t bit prev ∧ HasNand n G out t t
  | true, false => ∃ t1 t2, t1 < n + G.length ∧ t2 < n + G.length ∧
      HasNand n G t1 bit bit ∧ HasNand n G t2 prev prev ∧ HasNand n G out t1 t2
  | false, true => ∃ t, t < n + G.length ∧ HasNand n G t prev prev ∧ HasNand n G out bit t
  | false, false => ∃ t1 t2, t1 < n + G.length ∧ t2 < n + G.length ∧
      HasNand n G t1 bit bit ∧ HasNand n G t2 t1 prev ∧ HasNand n G out t2 t2

private lemma hasCmpStep_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {isGe target : Bool}
    {bit prev out : ℕ} (hp : G₁ <+: G₂) (h : HasCmpStep n G₁ isGe target bit prev out) :
    HasCmpStep n G₂ isGe target bit prev out := by
  have hle : G₁.length ≤ G₂.length := hp.length_le
  cases isGe <;> cases target
  · obtain ⟨h1, h2, h3, t1, t2, ht1, ht2, g1, g2, g3⟩ := h
    exact ⟨by omega, by omega, by omega, t1, t2, by omega, by omega,
      hasNand_mono hp g1, hasNand_mono hp g2, hasNand_mono hp g3⟩
  · obtain ⟨h1, h2, h3, t, ht, g1, g2⟩ := h
    exact ⟨by omega, by omega, by omega, t, by omega, hasNand_mono hp g1, hasNand_mono hp g2⟩
  · obtain ⟨h1, h2, h3, t1, t2, ht1, ht2, g1, g2, g3⟩ := h
    exact ⟨by omega, by omega, by omega, t1, t2, by omega, by omega,
      hasNand_mono hp g1, hasNand_mono hp g2, hasNand_mono hp g3⟩
  · obtain ⟨h1, h2, h3, t, ht, g1, g2⟩ := h
    exact ⟨by omega, by omega, by omega, t, by omega, hasNand_mono hp g1, hasNand_mono hp g2⟩

private lemma exists_addCmpStep {n : ℕ} {G : List (ℕ × ℕ)} (isGe target : Bool)
    {bit prev : ℕ} (hV : ValidCirc n G)
    (hb : bit < n + G.length) (hp : prev < n + G.length) :
    ∃ (G' : List (ℕ × ℕ)) (out : ℕ),
      G <+: G' ∧ G'.length ≤ G.length + 3 ∧ ValidCirc n G' ∧
      HasCmpStep n G' isGe target bit prev out := by
  cases isGe <;> cases target
  · obtain ⟨G1, w1, p1, l1, v1, n1, hw1⟩ := exists_addGate bit bit hV hb hb
    obtain ⟨G2, w2, p2, l2, v2, n2, hw2⟩ := exists_addGate w1 prev v1 hw1 (by omega)
    obtain ⟨G3, w3, p3, l3, v3, n3, hw3⟩ := exists_addGate w2 w2 v2 hw2 hw2
    exact ⟨G3, w3, p1.trans (p2.trans p3), by omega, v3,
      by omega, by omega, hw3, w1, w2, by omega, by omega,
      hasNand_mono (p2.trans p3) n1, hasNand_mono p3 n2, n3⟩
  · obtain ⟨G1, w1, p1, l1, v1, n1, hw1⟩ := exists_addGate prev prev hV hp hp
    obtain ⟨G2, w2, p2, l2, v2, n2, hw2⟩ := exists_addGate bit w1 v1 (by omega) hw1
    exact ⟨G2, w2, p1.trans p2, by omega, v2,
      by omega, by omega, hw2, w1, by omega, hasNand_mono p2 n1, n2⟩
  · obtain ⟨G1, w1, p1, l1, v1, n1, hw1⟩ := exists_addGate bit bit hV hb hb
    obtain ⟨G2, w2, p2, l2, v2, n2, hw2⟩ := exists_addGate prev prev v1 (by omega) (by omega)
    obtain ⟨G3, w3, p3, l3, v3, n3, hw3⟩ := exists_addGate w1 w2 v2 (by omega) hw2
    exact ⟨G3, w3, p1.trans (p2.trans p3), by omega, v3,
      by omega, by omega, hw3, w1, w2, by omega, by omega,
      hasNand_mono (p2.trans p3) n1, hasNand_mono p3 n2, n3⟩
  · obtain ⟨G1, w1, p1, l1, v1, n1, hw1⟩ := exists_addGate bit prev hV hb hp
    obtain ⟨G2, w2, p2, l2, v2, n2, hw2⟩ := exists_addGate w1 w1 v1 hw1 hw1
    exact ⟨G2, w2, p1.trans p2, by omega, v2,
      by omega, by omega, hw2, w1, by omega, hasNand_mono p2 n1, n2⟩

private def cmpStepPred (isGe target : Bool) (bit prev out : ℕ) (x : ℕ → Bool) : Prop :=
  x out = cmpBit isGe target (x bit) (x prev)

private def cmpStepCNF (isGe target : Bool) (bit prev out : ℕ) : Set (Clause ℕ) :=
  fullCNF {bit, prev, out} (cmpStepPred isGe target bit prev out)

private lemma cmpStepPred_dependsOn (isGe target : Bool) (bit prev out : ℕ) :
    DependsOn {bit, prev, out} (cmpStepPred isGe target bit prev out) := by
  intro x y hxy
  simp only [cmpStepPred, hxy bit (by simp), hxy prev (by simp), hxy out (by simp)]

private lemma cmpStep_wireSet {n : ℕ} {G : List (ℕ × ℕ)} {isGe target : Bool}
    {bit prev out : ℕ} (h : HasCmpStep n G isGe target bit prev out) :
    ∃ (W : Finset ℕ) (H : Set (Clause ℕ)),
      W.card ≤ 3 ∧ (∀ v ∈ W, v < n + G.length) ∧ out ∈ W ∧
      H ⊆ allGateClauses n G ∧
      (∀ C ∈ H, ∀ l ∈ C, l.1 ∈ ({bit, prev} ∪ W)) ∧
      (∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → cmpStepPred isGe target bit prev out x) := by
  cases isGe <;> cases target
  · obtain ⟨h1, h2, h3, t1, t2, ht1, ht2, g1, g2, g3⟩ := h
    let W : Finset ℕ := {t1, t2, out}
    let H : Set (Clause ℕ) := nandClauses t1 bit bit ∪ nandClauses t2 t1 prev ∪ nandClauses out t2 t2
    refine ⟨W, H, ?_, ?_, by simp [W], ?_, ?_, ?_⟩
    · dsimp only [W]
      have := Finset.card_insert_le t1 {t2, out}
      have := Finset.card_insert_le t2 {out}
      simp only [Finset.card_singleton] at *; omega
    · intro v hv; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> omega
    · intro C hC; rcases hC with (h | h) | h
      · exact hasNand_clauses_subset g1 h
      · exact hasNand_clauses_subset g2 h
      · exact hasNand_clauses_subset g3 h
    · intro C hC l hl; rcases hC with (h | h) | h
      · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp) C h l hl
      · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp) C h l hl
      · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
    · intro x hx
      have e1 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl hC)))
      have e2 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inr hC)))
      have e3 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inr hC))
      simp only [cmpStepPred, cmpBit, e3, e2, e1]
      cases x bit <;> cases x prev <;> rfl
  · obtain ⟨h1, h2, h3, t, ht, g1, g2⟩ := h
    let W : Finset ℕ := {t, out}
    let H : Set (Clause ℕ) := nandClauses t prev prev ∪ nandClauses out bit t
    refine ⟨W, H, ?_, ?_, by simp [W], ?_, ?_, ?_⟩
    · dsimp only [W]
      have := Finset.card_insert_le t {out}
      simp only [Finset.card_singleton] at *; omega
    · intro v hv; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> omega
    · intro C hC; rcases hC with h | h
      · exact hasNand_clauses_subset g1 h
      · exact hasNand_clauses_subset g2 h
    · intro C hC l hl; rcases hC with h | h
      · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp) C h l hl
      · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp [W]) C h l hl
    · intro x hx
      have e1 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl hC))
      have e2 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inr hC))
      simp only [cmpStepPred, cmpBit, e2, e1]
      cases x bit <;> cases x prev <;> rfl
  · obtain ⟨h1, h2, h3, t1, t2, ht1, ht2, g1, g2, g3⟩ := h
    let W : Finset ℕ := {t1, t2, out}
    let H : Set (Clause ℕ) := nandClauses t1 bit bit ∪ nandClauses t2 prev prev ∪ nandClauses out t1 t2
    refine ⟨W, H, ?_, ?_, by simp [W], ?_, ?_, ?_⟩
    · dsimp only [W]
      have := Finset.card_insert_le t1 {t2, out}
      have := Finset.card_insert_le t2 {out}
      simp only [Finset.card_singleton] at *; omega
    · intro v hv; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl <;> omega
    · intro C hC; rcases hC with (h | h) | h
      · exact hasNand_clauses_subset g1 h
      · exact hasNand_clauses_subset g2 h
      · exact hasNand_clauses_subset g3 h
    · intro C hC l hl; rcases hC with (h | h) | h
      · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp) C h l hl
      · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp) C h l hl
      · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
    · intro x hx
      have e1 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inl hC)))
      have e2 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl (Or.inr hC)))
      have e3 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inr hC))
      simp only [cmpStepPred, cmpBit, e3, e2, e1]
      cases x bit <;> cases x prev <;> rfl
  · obtain ⟨h1, h2, h3, t, ht, g1, g2⟩ := h
    let W : Finset ℕ := {t, out}
    let H : Set (Clause ℕ) := nandClauses t bit prev ∪ nandClauses out t t
    refine ⟨W, H, ?_, ?_, by simp [W], ?_, ?_, ?_⟩
    · dsimp only [W]
      have := Finset.card_insert_le t {out}
      simp only [Finset.card_singleton] at *; omega
    · intro v hv; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> omega
    · intro C hC; rcases hC with h | h
      · exact hasNand_clauses_subset g1 h
      · exact hasNand_clauses_subset g2 h
    · intro C hC l hl; rcases hC with h | h
      · exact nandClauses_vars_subset (by simp [W]) (by simp) (by simp) C h l hl
      · exact nandClauses_vars_subset (by simp [W]) (by simp [W]) (by simp [W]) C h l hl
    · intro x hx
      have e1 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inl hC))
      have e2 := (nandClauses_sat_iff _ _ _ x).mp (fun C hC => hx C (Or.inr hC))
      simp only [cmpStepPred, cmpBit, e2, e1]
      cases x bit <;> cases x prev <;> rfl

private lemma derive_cmpStep {n : ℕ} {G : List (ℕ × ℕ)} {isGe target : Bool}
    {bit prev out : ℕ} (h : HasCmpStep n G isGe target bit prev out) :
    Derivable (allGateClauses n G) (n + G.length) 5 (3 * 2 ^ 8)
      (cmpStepCNF isGe target bit prev out) := by
  obtain ⟨W, H, hWc, hWB, houtW, hHF, hHS, hsem⟩ := cmpStep_wireSet h
  let S : Finset ℕ := {bit, prev} ∪ W
  have hScard : S.card ≤ 5 := by
    have h1 : ({bit, prev} : Finset ℕ).card ≤ 2 := by
      have := Finset.card_insert_le bit {prev}; simp only [Finset.card_singleton] at *; omega
    exact le_trans (Finset.card_union_le _ _) (by omega)
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    rcases Finset.mem_union.mp hv with h1 | h2
    · simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      rcases h1 with rfl | rfl
      · exact h.1
      · exact h.2.1
    · exact hWB v h2
  have hOcard : ({bit, prev, out} : Finset ℕ).card ≤ 3 := by
    have := Finset.card_insert_le bit {prev, out}
    have := Finset.card_insert_le prev {out}
    simp only [Finset.card_singleton] at *; omega
  have hOS : ({bit, prev, out} : Finset ℕ) ⊆ S := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_left _ (by simp)
    · exact Finset.mem_union_right _ houtW
  have hd := derive_fullCNF hHF hSB hHS hOS (cmpStepPred_dependsOn isGe target bit prev out) hsem
  exact derivable_mono hd Set.Subset.rfl le_rfl hScard
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega))) Set.Subset.rfl

private def HasCmp (n : ℕ) (G : List (ℕ × ℕ)) (o1 : ℕ) (isGe : Bool)
    (w K : ℕ) (A st : ℕ → ℕ) : Prop :=
  st 0 = o1 ∧ ∀ i < w, HasCmpStep n G isGe (K.testBit i) (A i) (st i) (st (i + 1))

private lemma hasCmp_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {o1 : ℕ} {isGe : Bool}
    {w K : ℕ} {A st : ℕ → ℕ} (hp : G₁ <+: G₂) (h : HasCmp n G₁ o1 isGe w K A st) :
    HasCmp n G₂ o1 isGe w K A st :=
  ⟨h.1, fun i hi => hasCmpStep_mono hp (h.2 i hi)⟩

private lemma exists_addCmp {n : ℕ} {G : List (ℕ × ℕ)} {o1 : ℕ} (isGe : Bool)
    (hV : ValidCirc n G) (ho : o1 < n + G.length) (w K : ℕ) (A : ℕ → ℕ)
    (hA : ∀ i < w, A i < n + G.length) :
    ∃ (G' : List (ℕ × ℕ)) (st : ℕ → ℕ),
      G <+: G' ∧ G'.length ≤ G.length + 3 * w ∧ ValidCirc n G' ∧
      HasCmp n G' o1 isGe w K A st ∧ (∀ i ≤ w, st i < n + G'.length) := by
  induction w with
  | zero =>
    refine ⟨G, fun _ => o1, List.prefix_refl G, by simp, hV,
      ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩, fun _ _ => ho⟩
  | succ w ih =>
    obtain ⟨G₁, st₁, hp₁, hl₁, hV₁, hc₁, hlt₁⟩ :=
      ih (fun i hi => hA i (Nat.lt_succ_of_lt hi))
    have hAw : A w < n + G₁.length := by have := hA w (Nat.lt_succ_self w); have := hp₁.length_le; omega
    obtain ⟨G₂, outw, hp₂, hl₂, hV₂, hstep⟩ :=
      exists_addCmpStep isGe (K.testBit w) hV₁ hAw (hlt₁ w le_rfl)
    let st₂ : ℕ → ℕ := fun i => if i = w + 1 then outw else st₁ i
    refine ⟨G₂, st₂, hp₁.trans hp₂, by omega, hV₂, ⟨by simp [st₂, hc₁.1], ?_⟩, ?_⟩
    · intro i hi
      by_cases hiw : i = w
      · rw [hiw]
        have h1 : st₂ w = st₁ w := by simp [st₂]
        have h2 : st₂ (w + 1) = outw := by simp [st₂]
        rw [h1, h2]; exact hstep
      · have hlt : i < w := by omega
        have h1 : st₂ i = st₁ i := by simp [st₂]; omega
        have h2 : st₂ (i + 1) = st₁ (i + 1) := by simp [st₂]; omega
        rw [h1, h2]; exact hasCmpStep_mono hp₂ (hc₁.2 i hlt)
    · intro i hi
      by_cases h1 : i = w + 1
      · rw [h1]; simp [st₂, hstep.2.2.1]
      · simp only [st₂, h1, ↓reduceIte]
        have := hlt₁ i (by omega)
        have := hp₂.length_le
        omega

private lemma bitsVal_lt_two_pow (w : ℕ) (f : ℕ → Bool) :
    bitsVal w f < 2 ^ w := by
  induction w with
  | zero => simp [bitsVal]
  | succ w ih =>
    rw [bitsVal_succ, Nat.pow_succ]
    cases f w <;> simp <;> omega

private lemma mod_two_pow_succ (K j : ℕ) :
    K % 2 ^ (j + 1) = K % 2 ^ j + (K.testBit j).toNat * 2 ^ j := by
  have h1 : K % 2 ^ (j + 1) = K % 2 ^ j + (K / 2 ^ j % 2) * 2 ^ j := by
    have hd1 := Nat.div_add_mod K (2 ^ j)
    have hd2 := Nat.div_add_mod (K / 2 ^ j) 2
    have hlt1 : K % 2 ^ j < 2 ^ j := Nat.mod_lt K (Nat.two_pow_pos j)
    have hle2 : K / 2 ^ j % 2 ≤ 1 := by have := Nat.mod_lt (K / 2 ^ j) (by omega : 0 < 2); omega
    have hpow : 2 ^ (j + 1) = 2 ^ j * 2 := Nat.pow_succ 2 j
    have hmul : 2 ^ j * (2 * (K / 2 ^ j / 2) + K / 2 ^ j % 2) = 2 ^ j * (K / 2 ^ j) :=
      congrArg (2 ^ j * ·) hd2
    have hK : K = (K % 2 ^ j + (K / 2 ^ j % 2) * 2 ^ j) + (2 ^ (j + 1)) * (K / 2 ^ j / 2) := by
      rw [hpow]; linarith
    have hrem : K % 2 ^ j + (K / 2 ^ j % 2) * 2 ^ j < 2 ^ (j + 1) := by
      rw [hpow]
      have hmul2 : (K / 2 ^ j % 2) * 2 ^ j ≤ 1 * 2 ^ j := Nat.mul_le_mul_right _ hle2
      omega
    conv_lhs => rw [hK]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem]
  rw [h1, Nat.testBit_eq_decide_div_mod_eq]
  have hm : K / 2 ^ j % 2 = 0 ∨ K / 2 ^ j % 2 = 1 := by omega
  rcases hm with h | h <;> simp [h]

private lemma cmp_wireSet {n : ℕ} {G : List (ℕ × ℕ)} {o1 : ℕ} {isGe : Bool}
    {w K : ℕ} {A st : ℕ → ℕ}
    (hc : HasCmp n G o1 isGe w K A st) :
    ∃ (W : Finset ℕ) (H : Set (Clause ℕ)),
      W.card ≤ 3 * w ∧ (∀ v ∈ W, v < n + G.length) ∧
      st w ∈ insert o1 W ∧ H ⊆ allGateClauses n G ∧
      (∀ C ∈ H, ∀ l ∈ C, l.1 ∈ (Finset.range w).image A ∪ insert o1 W) ∧
      (∀ x : ℕ → Bool, x o1 = true → (∀ C ∈ H, ClauseSat x C) →
        if isGe then (x (st w) = true ↔ K % 2 ^ w ≤ bitsVal w (fun i => x (A i)))
        else (x (st w) = true ↔ bitsVal w (fun i => x (A i)) ≤ K % 2 ^ w)) := by
  induction w with
  | zero =>
    refine ⟨∅, ∅, by simp, fun _ h => absurd h (Finset.notMem_empty _),
      by simp [hc.1], Set.empty_subset _, fun _ h => absurd h (Set.notMem_empty _), ?_⟩
    intro x hx1 _
    cases isGe <;> simp [bitsVal, hc.1, hx1, Nat.mod_one]
  | succ w ih =>
    have hc' : HasCmp n G o1 isGe w K A st := ⟨hc.1, fun i hi => hc.2 i (Nat.lt_succ_of_lt hi)⟩
    obtain ⟨W₁, H₁, hWc1, hWB1, hst1, hHF1, hHS1, hsem1⟩ := ih hc'
    obtain ⟨Ws, Hs, hWsc, hWsB, hstW, hHFs, hHSs, hsems⟩ := cmpStep_wireSet (hc.2 w (Nat.lt_succ_self w))
    refine ⟨W₁ ∪ Ws, H₁ ∪ Hs, le_trans (Finset.card_union_le _ _) (by omega), ?_, ?_,
      Set.union_subset hHF1 hHFs, ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_union.mp hv with h1 | h2
      · exact hWB1 v h1
      · exact hWsB v h2
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hstW)
    · intro C hC l hl
      rcases hC with h1 | h2
      · have hv := hHS1 C h1 l hl
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_insert] at hv ⊢
        rcases hv with ⟨i, hi, hiA⟩ | (hlo | hw)
        · exact Or.inl ⟨i, Nat.lt_succ_of_lt hi, hiA⟩
        · exact Or.inr (Or.inl hlo)
        · exact Or.inr (Or.inr (Or.inl hw))
      · have hv := hHSs C h2 l hl
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with (hA | hst) | hws
        · rw [hA]
          exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨w, Finset.mem_range.mpr (Nat.lt_succ_self w), rfl⟩)
        · rw [hst]
          rcases Finset.mem_insert.mp hst1 with h | h
          · exact Finset.mem_union_right _ (by rw [h]; exact Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ h))
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hws))
    · intro x hx1 hxH
      have hprev := hsem1 x hx1 (fun C hC => hxH C (Or.inl hC))
      have hstep := hsems x (fun C hC => hxH C (Or.inr hC))
      have hblt := bitsVal_lt_two_pow w (fun i => x (A i))
      have hklt : K % 2 ^ w < 2 ^ w := Nat.mod_lt K (Nat.two_pow_pos w)
      rw [bitsVal_succ, mod_two_pow_succ]
      simp only [cmpStepPred, cmpBit] at hstep
      cases isGe
      · simp only [Bool.false_eq_true, ↓reduceIte] at hprev hstep ⊢
        rw [hstep]
        cases htk : K.testBit w <;> cases hxa : x (A w) <;> cases hxp : x (st w) <;>
          simp only [hxp, Bool.false_eq_true, Bool.true_and, Bool.false_and,
            Bool.true_or, Bool.false_or, Bool.not_true, Bool.not_false,
            Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul, add_zero,
            ↓reduceIte, true_iff, false_iff] at hprev ⊢ <;> omega
      · simp only [↓reduceIte] at hprev hstep ⊢
        rw [hstep]
        cases htk : K.testBit w <;> cases hxa : x (A w) <;> cases hxp : x (st w) <;>
          simp only [hxp, Bool.false_eq_true, Bool.true_and, Bool.false_and,
            Bool.true_or, Bool.false_or,
            Bool.toNat_true, Bool.toNat_false, zero_mul, one_mul, add_zero,
            ↓reduceIte, true_iff, false_iff] at hprev ⊢ <;> omega

end NandCircuits

section CounterAndPerm

private def HasCounterTree (n : ℕ) (G : List (ℕ × ℕ)) (z0 d : ℕ)
    (leaves : ℕ → ℕ) (bits car : ℕ → ℕ → ℕ → ℕ) : Prop :=
  (∀ pos < 2 ^ d, bits 0 pos 0 = leaves pos) ∧
  (∀ t < d, ∀ pos < 2 ^ (d - (t + 1)),
    HasRipple n G z0 (t + 1)
      (fun i => bits t (2 * pos) i)
      (fun i => bits t (2 * pos + 1) i)
      (fun i => bits (t + 1) pos i)
      (fun i => car (t + 1) pos i))

private lemma hasCounterTree_mono {n : ℕ} {G₁ G₂ : List (ℕ × ℕ)} {z0 d : ℕ}
    {leaves : ℕ → ℕ} {bits car : ℕ → ℕ → ℕ → ℕ}
    (hp : G₁ <+: G₂) (h : HasCounterTree n G₁ z0 d leaves bits car) :
    HasCounterTree n G₂ z0 d leaves bits car :=
  ⟨h.1, fun t ht pos hpos => hasRipple_mono hp (h.2 t ht pos hpos)⟩

private lemma counterTree_left {n : ℕ} {G : List (ℕ × ℕ)} {z0 d : ℕ}
    {leaves : ℕ → ℕ} {bits car : ℕ → ℕ → ℕ → ℕ}
    (h : HasCounterTree n G z0 (d + 1) leaves bits car) :
    HasCounterTree n G z0 d leaves bits car := by
  refine ⟨fun pos hpos => h.1 pos (lt_of_lt_of_le hpos (Nat.pow_le_pow_right (by omega) (Nat.le_succ d))), ?_⟩
  intro t ht pos hpos
  have hlt : pos < 2 ^ (d + 1 - (t + 1)) :=
    lt_of_lt_of_le hpos (Nat.pow_le_pow_right (by omega) (by omega))
  exact h.2 t (Nat.lt_succ_of_lt ht) pos hlt

private lemma counterTree_right {n : ℕ} {G : List (ℕ × ℕ)} {z0 d : ℕ}
    {leaves : ℕ → ℕ} {bits car : ℕ → ℕ → ℕ → ℕ}
    (h : HasCounterTree n G z0 (d + 1) leaves bits car) :
    HasCounterTree n G z0 d
      (fun p => leaves (2 ^ d + p))
      (fun t p => bits t (2 ^ (d - t) + p))
      (fun t p => car t (2 ^ (d - t) + p)) := by
  refine ⟨?_, ?_⟩
  · intro pos hpos
    have hlt : 2 ^ d + pos < 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
    simpa [Nat.sub_zero] using h.1 (2 ^ d + pos) hlt
  · intro t ht pos hpos
    have hexp1 : d + 1 - (t + 1) = (d - (t + 1)) + 1 := by omega
    have hlt : 2 ^ (d - (t + 1)) + pos < 2 ^ (d + 1 - (t + 1)) := by
      rw [hexp1, Nat.pow_succ]; omega
    have hmul : 2 * (2 ^ (d - (t + 1)) + pos) = 2 ^ (d - t) + 2 * pos := by
      have he : d - t = (d - (t + 1)) + 1 := by omega
      rw [he, Nat.pow_succ]; ring
    have hmul1 : 2 * (2 ^ (d - (t + 1)) + pos) + 1 = 2 ^ (d - t) + (2 * pos + 1) := by omega
    have hr := h.2 t (Nat.lt_succ_of_lt ht) (2 ^ (d - (t + 1)) + pos) hlt
    have e1 : (fun i => bits t (2 * (2 ^ (d - (t + 1)) + pos)) i) = fun i => bits t (2 ^ (d - t) + 2 * pos) i := by
      funext i; rw [hmul]
    have e2 : (fun i => bits t (2 * (2 ^ (d - (t + 1)) + pos) + 1) i) = fun i => bits t (2 ^ (d - t) + (2 * pos + 1)) i := by
      funext i; rw [hmul1]
    rwa [e1, e2] at hr

private lemma counterTree_subtree {n : ℕ} {G : List (ℕ × ℕ)} {z0 r k : ℕ}
    {leaves : ℕ → ℕ} {bits car : ℕ → ℕ → ℕ → ℕ}
    (h : HasCounterTree n G z0 (r + k) leaves bits car) (blk : ℕ) (hblk : blk < 2 ^ r) :
    HasCounterTree n G z0 k
      (fun p => leaves (blk * 2 ^ k + p))
      (fun t p => bits t (blk * 2 ^ (k - t) + p))
      (fun t p => car t (blk * 2 ^ (k - t) + p)) := by
  refine ⟨?_, ?_⟩
  · intro pos hpos
    have hlt : blk * 2 ^ k + pos < 2 ^ (r + k) := by
      rw [Nat.pow_add]
      have hle : blk + 1 ≤ 2 ^ r := hblk
      calc blk * 2 ^ k + pos < blk * 2 ^ k + 2 ^ k := Nat.add_lt_add_left hpos _
        _ = (blk + 1) * 2 ^ k := by ring
        _ ≤ 2 ^ r * 2 ^ k := Nat.mul_le_mul_right _ hle
    simpa [Nat.sub_zero] using h.1 (blk * 2 ^ k + pos) hlt
  · intro t ht pos hpos
    have hexp : r + k - (t + 1) = r + (k - (t + 1)) := by omega
    have hlt : blk * 2 ^ (k - (t + 1)) + pos < 2 ^ (r + k - (t + 1)) := by
      rw [hexp, Nat.pow_add]
      have hle : blk + 1 ≤ 2 ^ r := hblk
      calc blk * 2 ^ (k - (t + 1)) + pos
          < blk * 2 ^ (k - (t + 1)) + 2 ^ (k - (t + 1)) := Nat.add_lt_add_left hpos _
        _ = (blk + 1) * 2 ^ (k - (t + 1)) := by ring
        _ ≤ 2 ^ r * 2 ^ (k - (t + 1)) := Nat.mul_le_mul_right _ hle
    have hmul : 2 * (blk * 2 ^ (k - (t + 1)) + pos) = blk * 2 ^ (k - t) + 2 * pos := by
      have he : k - t = (k - (t + 1)) + 1 := by omega
      rw [he, Nat.pow_succ]; ring
    have hmul1 : 2 * (blk * 2 ^ (k - (t + 1)) + pos) + 1 = blk * 2 ^ (k - t) + (2 * pos + 1) := by omega
    have hr := h.2 t (by omega) (blk * 2 ^ (k - (t + 1)) + pos) hlt
    have e1 : (fun i => bits t (2 * (blk * 2 ^ (k - (t + 1)) + pos)) i) = fun i => bits t (blk * 2 ^ (k - t) + 2 * pos) i := by
      funext i; rw [hmul]
    have e2 : (fun i => bits t (2 * (blk * 2 ^ (k - (t + 1)) + pos) + 1) i) = fun i => bits t (blk * 2 ^ (k - t) + (2 * pos + 1)) i := by
      funext i; rw [hmul1]
    rwa [e1, e2] at hr

private lemma exists_buildCounterTree {n : ℕ} {G : List (ℕ × ℕ)} (z0 : ℕ)
    (hV : ValidCirc n G) (hz : z0 < n + G.length) (d : ℕ) (leaves : ℕ → ℕ)
    (hl : ∀ p < 2 ^ d, leaves p < n + G.length) :
    ∃ (G' : List (ℕ × ℕ)) (bits car : ℕ → ℕ → ℕ → ℕ),
      G <+: G' ∧ G'.length + 9 * (d + 2) = G.length + 18 * 2 ^ d ∧ ValidCirc n G' ∧
      HasCounterTree n G' z0 d leaves bits car ∧
      (∀ t ≤ d, ∀ pos < 2 ^ (d - t), ∀ i ≤ t, bits t pos i < n + G'.length) ∧
      (∀ t, 1 ≤ t → t ≤ d → ∀ pos < 2 ^ (d - t), ∀ i ≤ t, car t pos i < n + G'.length) := by
  induction d generalizing G leaves with
  | zero =>
    refine ⟨G, fun _ _ _ => leaves 0, fun _ _ _ => z0, List.prefix_refl G, by simp, hV,
      ⟨fun pos hpos => by
        have hp0 : pos = 0 := by simp at hpos; omega
        rw [hp0],
       fun t ht => absurd ht (Nat.not_lt_zero t)⟩,
      fun t ht pos _ i _ => hl 0 (by simp),
      fun t h1 h2 => by omega⟩
  | succ d ih =>
    obtain ⟨G₁, bL, cL, p₁, l₁, v₁, ctL, hblL, hclL⟩ :=
      ih hV hz leaves (fun p hp => hl p (lt_of_lt_of_le hp (Nat.pow_le_pow_right (by omega) (Nat.le_succ d))))
    have hz₁ : z0 < n + G₁.length := by have := p₁.length_le; omega
    have hlR : ∀ p < 2 ^ d, leaves (2 ^ d + p) < n + G₁.length := by
      intro p hp
      have hlt : 2 ^ d + p < 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
      have := hl (2 ^ d + p) hlt
      have := p₁.length_le
      omega
    obtain ⟨G₂, bR, cR, p₂, l₂, v₂, ctR, hblR, hclR⟩ := ih v₁ hz₁ (fun p => leaves (2 ^ d + p)) hlR
    have hz₂ : z0 < n + G₂.length := by have := p₂.length_le; omega
    have hAL : ∀ i < d + 1, bL d 0 i < n + G₂.length := by
      intro i hi
      have := hblL d le_rfl 0 (by simp) i (by omega)
      have := p₂.length_le
      omega
    have hBR : ∀ i < d + 1, bR d 0 i < n + G₂.length := by
      intro i hi
      exact hblR d le_rfl 0 (by simp) i (by omega)
    obtain ⟨G₃, Sroot, croot, p₃, l₃, v₃, hrRoot, hltRoot⟩ :=
      exists_addRipple v₂ hz₂ (d + 1) (fun i => bL d 0 i) (fun i => bR d 0 i) hAL hBR
    let bits : ℕ → ℕ → ℕ → ℕ := fun t pos i =>
      if t = d + 1 then Sroot i
      else if pos < 2 ^ (d - t) then bL t pos i
      else bR t (pos - 2 ^ (d - t)) i
    let car : ℕ → ℕ → ℕ → ℕ := fun t pos i =>
      if t = d + 1 then croot i
      else if pos < 2 ^ (d - t) then cL t pos i
      else cR t (pos - 2 ^ (d - t)) i
    have hlen : G₃.length + 9 * (d + 3) = G.length + 18 * 2 ^ (d + 1) := by
      rw [Nat.pow_succ]; omega
    refine ⟨G₃, bits, car, p₁.trans (p₂.trans p₃), hlen, v₃, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro pos hpos
      simp only [bits, Nat.zero_ne_add_one, ↓reduceIte, Nat.sub_zero]
      by_cases hlt : pos < 2 ^ d
      · simp only [hlt, ↓reduceIte]; exact ctL.1 pos hlt
      · simp only [hlt, ↓reduceIte]
        have hsub : pos - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hpos; omega
        rw [ctR.1 (pos - 2 ^ d) hsub]
        dsimp only
        rw [Nat.add_sub_of_le (by omega)]
    · intro t ht pos hpos
      by_cases htd : t = d
      · rw [htd] at hpos ⊢
        have hp0 : pos = 0 := by simp at hpos; omega
        rw [hp0]
        have hL0 : (fun i => bits d (2 * 0) i) = fun i => bL d 0 i := by
          funext i; simp [bits]
        have hR0 : (fun i => bits d (2 * 0 + 1) i) = fun i => bR d 0 i := by
          funext i; simp [bits]
        have hS0 : (fun i => bits (d + 1) 0 i) = Sroot := by
          funext i; simp [bits]
        have hC0 : (fun i => car (d + 1) 0 i) = croot := by
          funext i; simp [car]
        rw [hL0, hR0, hS0, hC0]
        exact hrRoot
      · have htd' : t < d := by omega
        have hne1 : t ≠ d + 1 := by omega
        have hne2 : t + 1 ≠ d + 1 := by omega
        have hpow : 2 ^ (d - t) = 2 * 2 ^ (d - (t + 1)) := by
          have he : d - t = (d - (t + 1)) + 1 := by omega
          rw [he, Nat.pow_succ]; omega
        by_cases hlt : pos < 2 ^ (d - (t + 1))
        · have hlt2 : 2 * pos < 2 ^ (d - t) := by omega
          have hlt21 : 2 * pos + 1 < 2 ^ (d - t) := by omega
          have e1 : (fun i => bits t (2 * pos) i) = fun i => bL t (2 * pos) i := by
            funext i; simp only [bits, hne1, ↓reduceIte, hlt2]
          have e2 : (fun i => bits t (2 * pos + 1) i) = fun i => bL t (2 * pos + 1) i := by
            funext i; simp only [bits, hne1, ↓reduceIte, hlt21]
          have e3 : (fun i => bits (t + 1) pos i) = fun i => bL (t + 1) pos i := by
            funext i; simp only [bits, hne2, ↓reduceIte, hlt]
          have e4 : (fun i => car (t + 1) pos i) = fun i => cL (t + 1) pos i := by
            funext i; simp only [car, hne2, ↓reduceIte, hlt]
          rw [e1, e2, e3, e4]
          exact hasRipple_mono (p₂.trans p₃) (ctL.2 t htd' pos hlt)
        · have hge2 : ¬ (2 * pos < 2 ^ (d - t)) := by omega
          have hge21 : ¬ (2 * pos + 1 < 2 ^ (d - t)) := by omega
          have hsub : pos - 2 ^ (d - (t + 1)) < 2 ^ (d - (t + 1)) := by
            have he : d + 1 - (t + 1) = (d - (t + 1)) + 1 := by omega
            rw [he, Nat.pow_succ] at hpos; omega
          have hsub2 : 2 * pos - 2 ^ (d - t) = 2 * (pos - 2 ^ (d - (t + 1))) := by omega
          have hsub21 : 2 * pos + 1 - 2 ^ (d - t) = 2 * (pos - 2 ^ (d - (t + 1))) + 1 := by omega
          have e1 : (fun i => bits t (2 * pos) i) = fun i => bR t (2 * (pos - 2 ^ (d - (t + 1)))) i := by
            funext i; simp only [bits, hne1, hge2, ↓reduceIte, hsub2]
          have e2 : (fun i => bits t (2 * pos + 1) i) = fun i => bR t (2 * (pos - 2 ^ (d - (t + 1))) + 1) i := by
            funext i; simp only [bits, hne1, hge21, ↓reduceIte, hsub21]
          have e3 : (fun i => bits (t + 1) pos i) = fun i => bR (t + 1) (pos - 2 ^ (d - (t + 1))) i := by
            funext i; simp only [bits, hne2, hlt, ↓reduceIte]
          have e4 : (fun i => car (t + 1) pos i) = fun i => cR (t + 1) (pos - 2 ^ (d - (t + 1))) i := by
            funext i; simp only [car, hne2, hlt, ↓reduceIte]
          rw [e1, e2, e3, e4]
          exact hasRipple_mono p₃ (ctR.2 t htd' (pos - 2 ^ (d - (t + 1))) hsub)
    · intro t ht pos hpos i hi
      by_cases htd : t = d + 1
      · rw [htd]; simp only [bits, ↓reduceIte]; exact (hltRoot i (by omega)).1
      · simp only [bits, htd, ↓reduceIte]
        have htle : t ≤ d := by omega
        by_cases hlt : pos < 2 ^ (d - t)
        · simp only [hlt, ↓reduceIte]
          have := hblL t htle pos hlt i hi
          have := (p₂.trans p₃).length_le
          omega
        · simp only [hlt, ↓reduceIte]
          have hsub : pos - 2 ^ (d - t) < 2 ^ (d - t) := by
            have he : d + 1 - t = (d - t) + 1 := by omega
            rw [he, Nat.pow_succ] at hpos; omega
          have := hblR t htle (pos - 2 ^ (d - t)) hsub i hi
          have := p₃.length_le
          omega
    · intro t ht1 ht2 pos hpos i hi
      by_cases htd : t = d + 1
      · rw [htd]; simp only [car, ↓reduceIte]; exact (hltRoot i (by omega)).2
      · simp only [car, htd, ↓reduceIte]
        have htle : t ≤ d := by omega
        by_cases hlt : pos < 2 ^ (d - t)
        · simp only [hlt, ↓reduceIte]
          have := hclL t ht1 htle pos hlt i hi
          have := (p₂.trans p₃).length_le
          omega
        · simp only [hlt, ↓reduceIte]
          have hsub : pos - 2 ^ (d - t) < 2 ^ (d - t) := by
            have he : d + 1 - t = (d - t) + 1 := by omega
            rw [he, Nat.pow_succ] at hpos; omega
          have := hclR t ht1 htle (pos - 2 ^ (d - t)) hsub i hi
          have := p₃.length_le
          omega

private lemma counterTree_wireSet {n : ℕ} {G : List (ℕ × ℕ)} {z0 d : ℕ}
    {leaves : ℕ → ℕ} {bits car : ℕ → ℕ → ℕ → ℕ}
    (ct : HasCounterTree n G z0 d leaves bits car) :
    ∃ (W : Finset ℕ) (H : Set (Clause ℕ)),
      W.card + 9 * (d + 2) ≤ 18 * 2 ^ d ∧
      (∀ v ∈ W, v < n + G.length) ∧
      (∀ i ≤ d, bits d 0 i ∈ (Finset.range (2 ^ d)).image leaves ∪ insert z0 W) ∧
      H ⊆ allGateClauses n G ∧
      (∀ C ∈ H, ∀ l ∈ C, l.1 ∈ (Finset.range (2 ^ d)).image leaves ∪ insert z0 W) ∧
      (∀ x : ℕ → Bool, x z0 = false → (∀ C ∈ H, ClauseSat x C) →
        bitsVal (d + 1) (fun i => x (bits d 0 i)) =
          ∑ p ∈ Finset.range (2 ^ d), (x (leaves p)).toNat) := by
  induction d generalizing leaves bits car with
  | zero =>
    refine ⟨∅, ∅, by simp, fun _ h => absurd h (Finset.notMem_empty _), ?_, Set.empty_subset _,
      fun _ h => absurd h (Set.notMem_empty _), ?_⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      rw [hi0, ct.1 0 (by simp)]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, by simp, rfl⟩)
    · intro x _ _
      simp [bitsVal, ct.1 0 (by simp)]
  | succ d ih =>
    obtain ⟨WL, HL, hWLc, hWLB, hbL, hHFL, hHSL, hvalL⟩ := ih (counterTree_left ct)
    obtain ⟨WR, HR, hWRc, hWRB, hbR, hHFR, hHSR, hvalR⟩ := ih (counterTree_right ct)
    have hroot : HasRipple n G z0 (d + 1) (fun i => bits d 0 i) (fun i => bits d 1 i)
        (fun i => bits (d + 1) 0 i) (fun i => car (d + 1) 0 i) := by
      simpa using ct.2 d (Nat.lt_succ_self d) 0 (by simp)
    obtain ⟨WM, HM, hWMc, hWMB, hbM, hHFM, hHSM, hvalM⟩ := ripple_wireSet hroot
    let W : Finset ℕ := WL ∪ WR ∪ WM
    let H : Set (Clause ℕ) := HL ∪ HR ∪ HM
    have hLsub : (Finset.range (2 ^ d)).image leaves ⊆ (Finset.range (2 ^ (d + 1))).image leaves := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
      rw [Finset.mem_range] at hp
      exact Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr (by rw [Nat.pow_succ]; omega), rfl⟩
    have hRsub : (Finset.range (2 ^ d)).image (fun p => leaves (2 ^ d + p)) ⊆
        (Finset.range (2 ^ (d + 1))).image leaves := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨p, hp, rfl⟩
      rw [Finset.mem_range] at hp
      exact Finset.mem_image.mpr ⟨2 ^ d + p, Finset.mem_range.mpr (by rw [Nat.pow_succ]; omega), rfl⟩
    have hWcard : W.card + 9 * (d + 3) ≤ 18 * 2 ^ (d + 1) := by
      dsimp only [W]
      have hu1 : (WL ∪ WR ∪ WM).card ≤ WL.card + WR.card + WM.card :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      rw [Nat.pow_succ]; omega
    refine ⟨W, H, hWcard, ?_, ?_, Set.union_subset (Set.union_subset hHFL hHFR) hHFM, ?_, ?_⟩
    · intro v hv
      simp only [W, Finset.mem_union] at hv
      rcases hv with (h | h) | h
      · exact hWLB v h
      · exact hWRB v h
      · exact hWMB v h
    · intro i hi
      have := hbM i hi
      rcases Finset.mem_insert.mp this with hiz | hiW
      · exact Finset.mem_union_right _ (by rw [hiz]; exact Finset.mem_insert_self _ _)
      · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hiW))
    · intro C hC l hl
      rcases hC with (h1 | h2) | h3
      · have hv := hHSL C h1 l hl
        rcases Finset.mem_union.mp hv with hlv | hw
        · exact Finset.mem_union_left _ (hLsub hlv)
        · rcases Finset.mem_insert.mp hw with rfl | hwl
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_union_left _ hwl)))
      · have hv := hHSR C h2 l hl
        rcases Finset.mem_union.mp hv with hlv | hw
        · exact Finset.mem_union_left _ (hRsub hlv)
        · rcases Finset.mem_insert.mp hw with rfl | hwr
          · exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
              (Finset.mem_union_left _ (Finset.mem_union_right _ hwr)))
      · have hv := hHSM C h3 l hl
        rcases Finset.mem_union.mp hv with hAB | hw
        · rcases Finset.mem_union.mp hAB with hA | hB
          · rcases Finset.mem_image.mp hA with ⟨i, hi, hiA⟩
            rw [← hiA]
            rw [Finset.mem_range] at hi
            have hm := hbL i (by omega)
            rcases Finset.mem_union.mp hm with hlv | hwl
            · exact Finset.mem_union_left _ (hLsub hlv)
            · rcases Finset.mem_insert.mp hwl with hiz | hwl'
              · rw [hiz]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
              · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
                  (Finset.mem_union_left _ (Finset.mem_union_left _ hwl')))
          · rcases Finset.mem_image.mp hB with ⟨i, hi, hiB⟩
            rw [← hiB]
            rw [Finset.mem_range] at hi
            have hm := hbR i (by omega)
            simp only [Nat.sub_self, Nat.pow_zero, Nat.add_zero] at hm
            rcases Finset.mem_union.mp hm with hlv | hwr
            · exact Finset.mem_union_left _ (hRsub hlv)
            · rcases Finset.mem_insert.mp hwr with hiz | hwr'
              · rw [hiz]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
              · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem
                  (Finset.mem_union_left _ (Finset.mem_union_right _ hwr')))
        · rcases Finset.mem_insert.mp hw with hiz | hwm
          · rw [hiz]; exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ hwm))
    · intro x hx0 hxH
      have hL := hvalL x hx0 (fun C hC => hxH C (Or.inl (Or.inl hC)))
      have hR := hvalR x hx0 (fun C hC => hxH C (Or.inl (Or.inr hC)))
      simp only [Nat.sub_self, Nat.pow_zero, Nat.add_zero] at hR
      have hM := hvalM x hx0 (fun C hC => hxH C (Or.inr hC))
      rw [hM, hL, hR]
      have hexp : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
      rw [hexp, Finset.sum_range_add]

private lemma iter_conj {X : Type*} {α β : X → X}
    (_hα2 : ∀ x, α (α x) = x) :
    ∀ k x, α ((fun y => β (α y))^[k] x) = (fun y => α (β y))^[k] (α x) := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    simp only [Function.iterate_succ_apply']
    rw [ih]

private lemma iter_cancel {X : Type*} {f g : X → X}
    (hfg : ∀ x, g (f x) = x) :
    ∀ k m x, g^[k] (f^[k + m] x) = f^[m] x := by
  intro k
  induction k with
  | zero => intro m x; simp
  | succ k ih =>
    intro m x
    have h1 : k + 1 + m = k + (m + 1) := by omega
    rw [h1, Function.iterate_succ_apply', ih (m + 1) x, Function.iterate_succ_apply', hfg]

private lemma exists_period {m : ℕ} {f g : Fin m → Fin m}
    (hgf : ∀ x, g (f x) = x) (u : Fin m) :
    ∃ p : ℕ, 0 < p ∧ f^[p] u = u := by
  have hcard : Fintype.card (Fin m) < Fintype.card (Fin (m + 1)) := by simp
  obtain ⟨i, j, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin (m + 1) => f^[k.val] u) hcard
  wlog hlt : i.val < j.val generalizing i j
  · exact this j i hne.symm heq.symm (by omega)
  refine ⟨j.val - i.val, by omega, ?_⟩
  have hsum : i.val + (j.val - i.val) = j.val := by omega
  have h1 := congrArg (g^[i.val]) heq
  rw [← hsum, iter_cancel hgf i.val (j.val - i.val) u] at h1
  have h2 : g^[i.val] (f^[i.val] u) = u := by simpa using iter_cancel hgf i.val 0 u
  rw [h2] at h1
  exact h1.symm

private lemma iter_mod_period {X : Type*} {f : X → X} {u : X} {p : ℕ}
    (hp : 0 < p) (hper : f^[p] u = u) : ∀ k : ℕ, f^[k] u = f^[k % p] u := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hlt : k < p
    · rw [Nat.mod_eq_of_lt hlt]
    · have hge : p ≤ k := by omega
      have h1 : k = (k - p) + p := by omega
      have hmod : k % p = (k - p) % p := by
        conv_lhs => rw [h1]
        rw [Nat.add_mod_right]
      rw [hmod, ← ih (k - p) (by omega)]
      conv_lhs => rw [h1]
      rw [Function.iterate_add_apply, hper]

private lemma two_color_involutions_aux {m : ℕ} (α β : Fin m → Fin m)
    (hα2 : ∀ x, α (α x) = x) (hαn : ∀ x, α x ≠ x)
    (hβ2 : ∀ x, β (β x) = x) (hβn : ∀ x, β x ≠ x) :
    ∀ k (U : Finset (Fin m)), U.card = k →
      (∀ x ∈ U, α x ∈ U) → (∀ x ∈ U, β x ∈ U) →
      ∃ col : Fin m → Bool, ∀ x ∈ U, col (α x) = !(col x) ∧ col (β x) = !(col x) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro U hcard hUα hUβ
    by_cases hne : U.Nonempty
    · obtain ⟨u, huU⟩ := hne
      let γ : Fin m → Fin m := fun y => β (α y)
      let γ' : Fin m → Fin m := fun y => α (β y)
      have hγ'γ : ∀ x, γ' (γ x) = x := fun x => by simp [γ, γ', hβ2, hα2]
      have hγγ' : ∀ x, γ (γ' x) = x := fun x => by simp [γ, γ', hβ2, hα2]
      obtain ⟨p, hp, hper⟩ := exists_period hγ'γ u
      let Aorb : Finset (Fin m) := (Finset.range p).image (fun t => γ^[t] u)
      let Borb : Finset (Fin m) := Aorb.image α
      have hAsub : Aorb ⊆ U := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, -, rfl⟩
        clear hx
        induction t with
        | zero => exact huU
        | succ t iht =>
          rw [Function.iterate_succ_apply']
          exact hUβ _ (hUα _ iht)
      have hBsub : Borb ⊆ U := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        exact hUα y (hAsub hy)
      have hdisj : Disjoint Aorb Borb := by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        rcases Finset.mem_image.mp hxA with ⟨s, -, rfl⟩
        rcases Finset.mem_image.mp hxB with ⟨y, hyA, hxy⟩
        rcases Finset.mem_image.mp hyA with ⟨t, -, rfl⟩
        have hmain : ∀ a b : ℕ, a ≤ b → γ^[b] u ≠ α (γ^[a] u) := by
          intro a b hab heq
          let v := γ^[a] u
          have hv : γ^[b - a] v = α v := by
            change γ^[b - a] (γ^[a] u) = α (γ^[a] u)
            rw [← Function.iterate_add_apply, Nat.sub_add_cancel hab]
            exact heq
          let q := (b - a) / 2
          by_cases hev : (b - a) % 2 = 0
          · have h2q : b - a = q + q := by omega
            have h1 := congrArg (γ'^[q]) hv
            rw [h2q, iter_cancel hγ'γ q q v] at h1
            have h2 := iter_conj (β := β) hα2 q v
            change α (γ^[q] v) = γ'^[q] (α v) at h2
            rw [← h2] at h1
            exact hαn (γ^[q] v) h1.symm
          · have h2q : b - a = q + (q + 1) := by omega
            have h1 := congrArg (γ'^[q]) hv
            rw [h2q, iter_cancel hγ'γ q (q + 1) v] at h1
            have h2 := iter_conj (β := β) hα2 q v
            change α (γ^[q] v) = γ'^[q] (α v) at h2
            rw [← h2, Function.iterate_succ_apply'] at h1
            exact hβn (α (γ^[q] v)) h1
        by_cases hts : t ≤ s
        · exact hmain t s hts hxy.symm
        · have hst : s ≤ t := by omega
          have hxy' : γ^[t] u = α (γ^[s] u) := by rw [← hxy, hα2]
          exact hmain s t hst hxy'
      have hα_AB : ∀ x ∈ Aorb, α x ∈ Borb := fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hα_BA : ∀ x ∈ Borb, α x ∈ Aorb := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rw [hα2]; exact hy
      have hβ_BA : ∀ x ∈ Borb, β x ∈ Aorb := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        rcases Finset.mem_image.mp hy with ⟨t, -, rfl⟩
        have hstep : β (α (γ^[t] u)) = γ^[t + 1] u := (Function.iterate_succ_apply' γ t u).symm
        rw [hstep, iter_mod_period hp hper (t + 1)]
        exact Finset.mem_image.mpr ⟨(t + 1) % p, Finset.mem_range.mpr (Nat.mod_lt _ hp), rfl⟩
      have hβ_AB : ∀ x ∈ Aorb, β x ∈ Borb := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
        rw [Finset.mem_range] at ht
        let t' := if t = 0 then p - 1 else t - 1
        have ht' : t' < p := by dsimp only [t']; split_ifs <;> omega
        have hstep : γ^[t' + 1] u = γ^[t] u := by
          dsimp only [t']
          split_ifs with hz
          · subst hz; rw [Nat.sub_add_cancel hp]; exact hper
          · rw [Nat.sub_add_cancel (by omega)]
        have hβeq : β (γ^[t] u) = α (γ^[t'] u) := by
          rw [← hstep, Function.iterate_succ_apply']
          simp [γ, hβ2]
        rw [hβeq]
        exact Finset.mem_image.mpr ⟨γ^[t'] u, Finset.mem_image.mpr ⟨t', Finset.mem_range.mpr ht', rfl⟩, rfl⟩
      let U' : Finset (Fin m) := U \ (Aorb ∪ Borb)
      have huA : u ∈ Aorb := Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hp, rfl⟩
      have hcard' : U'.card < k := by
        rw [← hcard]
        exact Finset.card_lt_card (Finset.sdiff_ssubset (Finset.union_subset hAsub hBsub)
          ⟨u, Finset.mem_union_left _ huA⟩)
      have hU'α : ∀ x ∈ U', α x ∈ U' := by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨hUα x hx.1, fun hmem => hx.2 ?_⟩
        rcases Finset.mem_union.mp hmem with hA | hB
        · exact Finset.mem_union_right _ (by simpa [hα2] using hα_AB (α x) hA)
        · exact Finset.mem_union_left _ (by simpa [hα2] using hα_BA (α x) hB)
      have hU'β : ∀ x ∈ U', β x ∈ U' := by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨hUβ x hx.1, fun hmem => hx.2 ?_⟩
        rcases Finset.mem_union.mp hmem with hA | hB
        · exact Finset.mem_union_right _ (by simpa [hβ2] using hβ_AB (β x) hA)
        · exact Finset.mem_union_left _ (by simpa [hβ2] using hβ_BA (β x) hB)
      obtain ⟨col', hcol'⟩ := ih U'.card hcard' U' rfl hU'α hU'β
      let col : Fin m → Bool := fun x =>
        if x ∈ Aorb then false else if x ∈ Borb then true else col' x
      refine ⟨col, ?_⟩
      intro x hxU
      by_cases hxA : x ∈ Aorb
      · have hαB : α x ∈ Borb := hα_AB x hxA
        have hβB : β x ∈ Borb := hβ_AB x hxA
        have hαnA : α x ∉ Aorb := Finset.disjoint_right.mp hdisj hαB
        have hβnA : β x ∉ Aorb := Finset.disjoint_right.mp hdisj hβB
        simp [col, hxA, hαB, hβB, hαnA, hβnA]
      · by_cases hxB : x ∈ Borb
        · have hαA : α x ∈ Aorb := hα_BA x hxB
          have hβA : β x ∈ Aorb := hβ_BA x hxB
          simp [col, hxA, hxB, hαA, hβA]
        · have hxU' : x ∈ U' := Finset.mem_sdiff.mpr ⟨hxU, by simp [hxA, hxB]⟩
          have hαU' := hU'α x hxU'
          have hβU' := hU'β x hxU'
          have hαn : α x ∉ Aorb ∧ α x ∉ Borb := by
            have := (Finset.mem_sdiff.mp hαU').2; simp_all
          have hβn' : β x ∉ Aorb ∧ β x ∉ Borb := by
            have := (Finset.mem_sdiff.mp hβU').2; simp_all
          simp only [col, hxA, hxB, hαn.1, hαn.2, hβn'.1, hβn'.2, ↓reduceIte]
          exact hcol' x hxU'
    · refine ⟨fun _ => false, fun x hx => absurd ⟨x, hx⟩ hne⟩

private lemma two_color_involutions {m : ℕ} (α β : Fin m → Fin m)
    (hα2 : ∀ x, α (α x) = x) (hαn : ∀ x, α x ≠ x)
    (hβ2 : ∀ x, β (β x) = x) (hβn : ∀ x, β x ≠ x) :
    ∃ col : Fin m → Bool, ∀ x, col (α x) = !(col x) ∧ col (β x) = !(col x) := by
  obtain ⟨col, hcol⟩ := two_color_involutions_aux α β hα2 hαn hβ2 hβn
    (Finset.univ : Finset (Fin m)).card Finset.univ rfl
    (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
  exact ⟨col, fun x => hcol x (Finset.mem_univ x)⟩

private def flipPair (m : ℕ) (x : Fin (2 * m)) : Fin (2 * m) :=
  ⟨if x.val % 2 = 0 then x.val + 1 else x.val - 1, by have := x.isLt; split_ifs <;> omega⟩

private lemma flipPair_invol (m : ℕ) (x : Fin (2 * m)) : flipPair m (flipPair m x) = x := by
  apply Fin.ext; dsimp only [flipPair]; split_ifs <;> omega

private lemma flipPair_ne (m : ℕ) (x : Fin (2 * m)) : flipPair m x ≠ x := by
  intro h
  have := congrArg Fin.val h
  dsimp only [flipPair] at this
  split_ifs at this <;> omega

private lemma perm_two_color_split {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) :
    ∃ (rowIdx colIdx : Bool → Fin m → Fin (2 * m)) (σc : Bool → Equiv.Perm (Fin m)),
      (∀ k : Fin m,
        ((rowIdx false k).val = 2 * k.val ∧ (rowIdx true k).val = 2 * k.val + 1) ∨
        ((rowIdx false k).val = 2 * k.val + 1 ∧ (rowIdx true k).val = 2 * k.val)) ∧
      (∀ j : Fin m,
        ((colIdx false j).val = 2 * j.val ∧ (colIdx true j).val = 2 * j.val + 1) ∨
        ((colIdx false j).val = 2 * j.val + 1 ∧ (colIdx true j).val = 2 * j.val)) ∧
      (∀ c : Bool, ∀ k : Fin m, σ (rowIdx c k) = colIdx c (σc c k)) := by
  let α : Fin (2 * m) → Fin (2 * m) := flipPair m
  let β : Fin (2 * m) → Fin (2 * m) := fun x => σ.symm (flipPair m (σ x))
  have hβ2 : ∀ x, β (β x) = x := fun x => by simp [β, flipPair_invol]
  have hβn : ∀ x, β x ≠ x := fun x h => flipPair_ne m (σ x) (by
    have := congrArg σ h; simpa [β] using this)
  obtain ⟨col, hcol⟩ := two_color_involutions α β (flipPair_invol m) (flipPair_ne m) hβ2 hβn
  have hpair_col : ∀ k : Fin m,
      col ⟨2 * k.val + 1, by omega⟩ = !(col ⟨2 * k.val, by omega⟩) := by
    intro k
    have hfl : α ⟨2 * k.val, by omega⟩ = ⟨2 * k.val + 1, by omega⟩ := by
      apply Fin.ext; simp [α, flipPair]
    rw [← hfl]
    exact (hcol ⟨2 * k.val, by omega⟩).1
  have hpair_colY : ∀ j : Fin m,
      col (σ.symm ⟨2 * j.val + 1, by omega⟩) = !(col (σ.symm ⟨2 * j.val, by omega⟩)) := by
    intro j
    have hfl : β (σ.symm ⟨2 * j.val, by omega⟩) = σ.symm ⟨2 * j.val + 1, by omega⟩ := by
      dsimp only [β]
      rw [Equiv.apply_symm_apply]
      congr 1
      apply Fin.ext; simp [flipPair]
    rw [← hfl]
    exact (hcol (σ.symm ⟨2 * j.val, by omega⟩)).2
  let rowIdx : Bool → Fin m → Fin (2 * m) := fun c k =>
    if col ⟨2 * k.val, by omega⟩ = c then ⟨2 * k.val, by omega⟩ else ⟨2 * k.val + 1, by omega⟩
  let colIdx : Bool → Fin m → Fin (2 * m) := fun c j =>
    if col (σ.symm ⟨2 * j.val, by omega⟩) = c then ⟨2 * j.val, by omega⟩ else ⟨2 * j.val + 1, by omega⟩
  have hrowCol : ∀ c k, col (rowIdx c k) = c := by
    intro c k
    dsimp only [rowIdx]
    split_ifs with h
    · exact h
    · rw [hpair_col k]; cases c <;> cases h0 : col ⟨2 * k.val, by omega⟩ <;> simp_all
  have hcolCol : ∀ c j, col (σ.symm (colIdx c j)) = c := by
    intro c j
    dsimp only [colIdx]
    split_ifs with h
    · exact h
    · rw [hpair_colY j]; cases c <;> cases h0 : col (σ.symm ⟨2 * j.val, by omega⟩) <;> simp_all
  have hrowUniq : ∀ c (x : Fin (2 * m)), col x = c →
      rowIdx c ⟨x.val / 2, by omega⟩ = x := by
    intro c x hcx
    dsimp only [rowIdx]
    by_cases hev : x.val % 2 = 0
    · have hx : (⟨2 * (x.val / 2), by omega⟩ : Fin (2 * m)) = x := by apply Fin.ext; dsimp; omega
      rw [hx]; simp [hcx]
    · have hx1 : (⟨2 * (x.val / 2) + 1, by omega⟩ : Fin (2 * m)) = x := by apply Fin.ext; dsimp; omega
      have hne : col ⟨2 * (x.val / 2), by omega⟩ ≠ c := by
        have hp := hpair_col ⟨x.val / 2, by omega⟩
        rw [hx1, hcx] at hp
        intro heq; rw [heq] at hp; cases c <;> simp at hp
      simp [hne, hx1]
  have hcolUniq : ∀ c (y : Fin (2 * m)), col (σ.symm y) = c →
      colIdx c ⟨y.val / 2, by omega⟩ = y := by
    intro c y hcy
    dsimp only [colIdx]
    by_cases hev : y.val % 2 = 0
    · have hy : (⟨2 * (y.val / 2), by omega⟩ : Fin (2 * m)) = y := by apply Fin.ext; dsimp; omega
      rw [hy]; simp [hcy]
    · have hy1 : (⟨2 * (y.val / 2) + 1, by omega⟩ : Fin (2 * m)) = y := by apply Fin.ext; dsimp; omega
      have hne : col (σ.symm ⟨2 * (y.val / 2), by omega⟩) ≠ c := by
        have hp := hpair_colY ⟨y.val / 2, by omega⟩
        rw [hy1, hcy] at hp
        intro heq; rw [heq] at hp; cases c <;> simp at hp
      simp [hne, hy1]
  let σc : Bool → Equiv.Perm (Fin m) := fun c =>
    { toFun := fun k => ⟨(σ (rowIdx c k)).val / 2, by omega⟩
      invFun := fun j => ⟨(σ.symm (colIdx c j)).val / 2, by omega⟩
      left_inv := fun k => by
        have h1 : colIdx c ⟨(σ (rowIdx c k)).val / 2, by omega⟩ = σ (rowIdx c k) :=
          hcolUniq c (σ (rowIdx c k)) (by rw [Equiv.symm_apply_apply]; exact hrowCol c k)
        apply Fin.ext
        dsimp only
        rw [h1, Equiv.symm_apply_apply]
        dsimp only [rowIdx]; split_ifs <;> (dsimp only; omega)
      right_inv := fun j => by
        have h1 : rowIdx c ⟨(σ.symm (colIdx c j)).val / 2, by omega⟩ = σ.symm (colIdx c j) :=
          hrowUniq c (σ.symm (colIdx c j)) (hcolCol c j)
        apply Fin.ext
        dsimp only
        rw [h1, Equiv.apply_symm_apply]
        dsimp only [colIdx]; split_ifs <;> (dsimp only; omega) }
  refine ⟨rowIdx, colIdx, σc, ?_, ?_, ?_⟩
  · intro k
    cases h0 : col ⟨2 * k.val, by omega⟩
    · left; simp [rowIdx, h0]
    · right; simp [rowIdx, h0]
  · intro j
    cases h0 : col (σ.symm ⟨2 * j.val, by omega⟩)
    · left; simp [colIdx, h0]
    · right; simp [colIdx, h0]
  · intro c k
    exact (hcolUniq c (σ (rowIdx c k)) (by rw [Equiv.symm_apply_apply]; exact hrowCol c k)).symm

private def BitEqCNF (u v : ℕ) : Set (Clause ℕ) :=
  fullCNF {u, v} (fun x => x u = x v)

private lemma bitEq_dependsOn (u v : ℕ) : DependsOn {u, v} (fun x => x u = x v) := by
  intro x y hxy
  simp only [hxy u (by simp), hxy v (by simp)]

private lemma bitEq_refl (u : ℕ) : BitEqCNF u u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro C ⟨α, hα, -⟩
  exact hα rfl

private def carrySumPred (c1 c2 c3 d1 d2 d3 : ℕ) (x : ℕ → Bool) : Prop :=
  (x c1).toNat + (x c2).toNat + (x c3).toNat =
    (x d1).toNat + (x d2).toNat + (x d3).toNat

private def carrySumCNF (c1 c2 c3 d1 d2 d3 : ℕ) : Set (Clause ℕ) :=
  fullCNF {c1, c2, c3, d1, d2, d3} (carrySumPred c1 c2 c3 d1 d2 d3)

private lemma carrySum_dependsOn (c1 c2 c3 d1 d2 d3 : ℕ) :
    DependsOn {c1, c2, c3, d1, d2, d3} (carrySumPred c1 c2 c3 d1 d2 d3) := by
  intro x y hxy
  simp only [carrySumPred, hxy c1 (by simp), hxy c2 (by simp), hxy c3 (by simp),
    hxy d1 (by simp), hxy d2 (by simp), hxy d3 (by simp)]

private lemma carrySum_refl (z : ℕ) : carrySumCNF z z z z z z = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro C ⟨α, hα, -⟩
  exact hα rfl

private def K_slice : ℕ := 2 ^ 38

private lemma card5_le (a b c d e : ℕ) : ({a, b, c, d, e} : Finset ℕ).card ≤ 5 := by
  have := Finset.card_insert_le a {b, c, d, e}
  have := Finset.card_insert_le b {c, d, e}
  have := Finset.card_insert_le c {d, e}
  have := Finset.card_insert_le d {e}
  simp only [Finset.card_singleton] at *
  omega

private lemma recombine_slice {n : ℕ} {G : List (ℕ × ℕ)}
    {ru bu rw_ bw c1 c2 c3 d1 d2 d3 yu yw xu xw rv bv xv yv c1' c2' c3' d1' d2' d3' : ℕ}
    (hFA1 : HasFA n G ru bu c1 yu c1')
    (hFA2 : HasFA n G rw_ bw c2 yw c2')
    (hFA3 : HasFA n G xu xw c3 xv c3')
    (hFA4 : HasFA n G ru rw_ d1 rv d1')
    (hFA5 : HasFA n G bu bw d2 bv d2')
    (hFA6 : HasFA n G rv bv d3 yv d3') :
    Derivable (allGateClauses n G ∪ BitEqCNF xu yu ∪ BitEqCNF xw yw ∪
        carrySumCNF c1 c2 c3 d1 d2 d3)
      (n + G.length) 30 K_slice
      (carrySumCNF c1' c2' c3' d1' d2' d3' ∪ BitEqCNF xv yv) := by
  let F0 : Set (Clause ℕ) :=
    allGateClauses n G ∪ BitEqCNF xu yu ∪ BitEqCNF xw yw ∪ carrySumCNF c1 c2 c3 d1 d2 d3
  have hsub0 : allGateClauses n G ⊆ F0 := fun C hC => Or.inl (Or.inl (Or.inl hC))
  have dFA1 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF ru bu c1 yu c1') :=
    derivable_mono (derive_FA hFA1) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dFA2 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF rw_ bw c2 yw c2') :=
    derivable_mono (derive_FA hFA2) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dFA3 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF xu xw c3 xv c3') :=
    derivable_mono (derive_FA hFA3) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dFA4 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF ru rw_ d1 rv d1') :=
    derivable_mono (derive_FA hFA4) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dFA5 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF bu bw d2 bv d2') :=
    derivable_mono (derive_FA hFA5) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dFA6 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF rv bv d3 yv d3') :=
    derivable_mono (derive_FA hFA6) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dAll := derivable_union (derivable_union (derivable_union dFA1 dFA2) (derivable_union dFA3 dFA4))
    (derivable_union dFA5 dFA6)
  let H : Set (Clause ℕ) :=
    ((faCNF ru bu c1 yu c1' ∪ faCNF rw_ bw c2 yw c2') ∪ (faCNF xu xw c3 xv c3' ∪ faCNF ru rw_ d1 rv d1')) ∪
    (faCNF bu bw d2 bv d2' ∪ faCNF rv bv d3 yv d3') ∪
    BitEqCNF xu yu ∪ BitEqCNF xw yw ∪ carrySumCNF c1 c2 c3 d1 d2 d3
  let S1 : Finset ℕ := {ru, bu, c1, yu, c1'}
  let S2 : Finset ℕ := {rw_, bw, c2, yw, c2'}
  let S3 : Finset ℕ := {xu, xw, c3, xv, c3'}
  let S4 : Finset ℕ := {ru, rw_, d1, rv, d1'}
  let S5 : Finset ℕ := {bu, bw, d2, bv, d2'}
  let S6 : Finset ℕ := {rv, bv, d3, yv, d3'}
  let S : Finset ℕ := ((S1 ∪ S2) ∪ (S3 ∪ S4)) ∪ (S5 ∪ S6)
  have hS1 : S1 ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
  have hS2 : S2 ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
  have hS3 : S3 ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _ hv))
  have hS4 : S4 ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hv))
  have hS5 : S5 ⊆ S := fun v hv => Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  have hS6 : S6 ⊆ S := fun v hv => Finset.mem_union_right _ (Finset.mem_union_right _ hv)
  have hScard : S.card ≤ 30 := by
    have h1 := card5_le ru bu c1 yu c1'
    have h2 := card5_le rw_ bw c2 yw c2'
    have h3 := card5_le xu xw c3 xv c3'
    have h4 := card5_le ru rw_ d1 rv d1'
    have h5 := card5_le bu bw d2 bv d2'
    have h6 := card5_le rv bv d3 yv d3'
    have hu : S.card ≤ S1.card + S2.card + S3.card + S4.card + S5.card + S6.card := by
      dsimp only [S]
      have := Finset.card_union_le ((S1 ∪ S2) ∪ (S3 ∪ S4)) (S5 ∪ S6)
      have := Finset.card_union_le (S1 ∪ S2) (S3 ∪ S4)
      have := Finset.card_union_le S1 S2
      have := Finset.card_union_le S3 S4
      have := Finset.card_union_le S5 S6
      omega
    dsimp only [S1, S2, S3, S4, S5, S6] at hu
    omega
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    rcases Finset.mem_union.mp hv with h14 | h56
    · rcases Finset.mem_union.mp h14 with h12 | h34
      · rcases Finset.mem_union.mp h12 with h | h
        · simp only [S1, Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hFA1.1
          · exact hFA1.2.1
          · exact hFA1.2.2.1
          · exact hFA1.2.2.2.1
          · exact hFA1.2.2.2.2.1
        · simp only [S2, Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hFA2.1
          · exact hFA2.2.1
          · exact hFA2.2.2.1
          · exact hFA2.2.2.2.1
          · exact hFA2.2.2.2.2.1
      · rcases Finset.mem_union.mp h34 with h | h
        · simp only [S3, Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hFA3.1
          · exact hFA3.2.1
          · exact hFA3.2.2.1
          · exact hFA3.2.2.2.1
          · exact hFA3.2.2.2.2.1
        · simp only [S4, Finset.mem_insert, Finset.mem_singleton] at h
          rcases h with rfl | rfl | rfl | rfl | rfl
          · exact hFA4.1
          · exact hFA4.2.1
          · exact hFA4.2.2.1
          · exact hFA4.2.2.2.1
          · exact hFA4.2.2.2.2.1
    · rcases Finset.mem_union.mp h56 with h | h
      · simp only [S5, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hFA5.1
        · exact hFA5.2.1
        · exact hFA5.2.2.1
        · exact hFA5.2.2.2.1
        · exact hFA5.2.2.2.2.1
      · simp only [S6, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hFA6.1
        · exact hFA6.2.1
        · exact hFA6.2.2.1
        · exact hFA6.2.2.2.1
        · exact hFA6.2.2.2.2.1
  have hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with ((((h | h) | h) | h) | h)
    · rcases h with (h | h) | (h | h)
      · exact fullCNF_vars_subset hS1 C h l hl
      · exact fullCNF_vars_subset hS2 C h l hl
      · exact fullCNF_vars_subset hS3 C h l hl
      · exact fullCNF_vars_subset hS4 C h l hl
    · rcases h with h | h
      · exact fullCNF_vars_subset hS5 C h l hl
      · exact fullCNF_vars_subset hS6 C h l hl
    · exact fullCNF_vars_subset (fun v hv => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hS3 (by simp [S3])
        · exact hS1 (by simp [S1])) C h l hl
    · exact fullCNF_vars_subset (fun v hv => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact hS3 (by simp [S3])
        · exact hS2 (by simp [S2])) C h l hl
    · exact fullCNF_vars_subset (fun v hv => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hS1 (by simp [S1])
        · exact hS2 (by simp [S2])
        · exact hS3 (by simp [S3])
        · exact hS4 (by simp [S4])
        · exact hS5 (by simp [S5])
        · exact hS6 (by simp [S6])) C h l hl
  have hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) →
      carrySumPred c1' c2' c3' d1' d2' d3' x ∧ x xv = x yv := by
    intro x hx
    have e1 : faPred ru bu c1 yu c1' x := (fullCNF_sat_iff (faPred_dependsOn ru bu c1 yu c1') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hC)))))))
    have e2 : faPred rw_ bw c2 yw c2' x := (fullCNF_sat_iff (faPred_dependsOn rw_ bw c2 yw c2') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hC)))))))
    have e3 : faPred xu xw c3 xv c3' x := (fullCNF_sat_iff (faPred_dependsOn xu xw c3 xv c3') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl hC)))))))
    have e4 : faPred ru rw_ d1 rv d1' x := (fullCNF_sat_iff (faPred_dependsOn ru rw_ d1 rv d1') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr hC)))))))
    have e5 : faPred bu bw d2 bv d2' x := (fullCNF_sat_iff (faPred_dependsOn bu bw d2 bv d2') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl hC))))))
    have e6 : faPred rv bv d3 yv d3' x := (fullCNF_sat_iff (faPred_dependsOn rv bv d3 yv d3') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr hC))))))
    have exu : x xu = x yu := (fullCNF_sat_iff (bitEq_dependsOn xu yu) x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
    have exw : x xw = x yw := (fullCNF_sat_iff (bitEq_dependsOn xw yw) x).mp
      (fun C hC => hx C (Or.inl (Or.inr hC)))
    have ecar : carrySumPred c1 c2 c3 d1 d2 d3 x :=
      (fullCNF_sat_iff (carrySum_dependsOn c1 c2 c3 d1 d2 d3) x).mp
        (fun C hC => hx C (Or.inr hC))
    simp only [faPred, carrySumPred, exu, exw] at e1 e2 e3 e4 e5 e6 ecar ⊢
    have hxv_lt : (x xv).toNat ≤ 1 := by cases x xv <;> simp
    have hyv_lt : (x yv).toNat ≤ 1 := by cases x yv <;> simp
    have hbit : (x xv).toNat = (x yv).toNat := by omega
    refine ⟨by omega, ?_⟩
    cases hx1 : x xv <;> cases hy1 : x yv <;> simp_all
  have hHsub : H ⊆ F0 ∪ (((faCNF ru bu c1 yu c1' ∪ faCNF rw_ bw c2 yw c2') ∪
      (faCNF xu xw c3 xv c3' ∪ faCNF ru rw_ d1 rv d1')) ∪
      (faCNF bu bw d2 bv d2' ∪ faCNF rv bv d3 yv d3')) := by
    intro C hC
    rcases hC with ((((h | h) | h) | h) | h)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
  have hO1 : ({c1', c2', c3', d1', d2', d3'} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS1 (by simp [S1])
    · exact hS2 (by simp [S2])
    · exact hS3 (by simp [S3])
    · exact hS4 (by simp [S4])
    · exact hS5 (by simp [S5])
    · exact hS6 (by simp [S6])
  have hO2 : ({xv, yv} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hS3 (by simp [S3])
    · exact hS6 (by simp [S6])
  have hO1c : ({c1', c2', c3', d1', d2', d3'} : Finset ℕ).card ≤ 6 := by
    have := Finset.card_insert_le c1' {c2', c3', d1', d2', d3'}
    have := card5_le c2' c3' d1' d2' d3'
    omega
  have hO2c : ({xv, yv} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le xv {yv}; simp at *; omega
  have dOut1 := derive_fullCNF (O := {c1', c2', c3', d1', d2', d3'}) hHsub hSB hHS hO1
    (carrySum_dependsOn c1' c2' c3' d1' d2' d3') (fun x hx => (hsem x hx).1)
  have dOut2 := derive_fullCNF (O := {xv, yv}) hHsub hSB hHS hO2
    (bitEq_dependsOn xv yv) (fun x hx => (hsem x hx).2)
  have dOut1' := derivable_mono dOut1 Set.Subset.rfl le_rfl hScard
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 36))) Set.Subset.rfl
  have dOut2' := derivable_mono dOut2 Set.Subset.rfl le_rfl hScard
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 32))) Set.Subset.rfl
  have dOut := derivable_union dOut1' dOut2'
  have htr := derivable_trans_only dAll dOut
  refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
  dsimp only [K_slice]
  norm_num

private lemma recombine_top {n : ℕ} {G : List (ℕ × ℕ)}
    {c1 c2 c3 d1 d2 d3 xu xw xv yv c3' d3' : ℕ}
    (hc1 : c1 < n + G.length) (hc2 : c2 < n + G.length)
    (hFA3 : HasFA n G xu xw c3 xv c3')
    (hFA6 : HasFA n G d1 d2 d3 yv d3') :
    Derivable (allGateClauses n G ∪ BitEqCNF xu c1 ∪ BitEqCNF xw c2 ∪
        carrySumCNF c1 c2 c3 d1 d2 d3)
      (n + G.length) 30 K_slice
      (BitEqCNF xv yv ∪ BitEqCNF c3' d3') := by
  let F0 : Set (Clause ℕ) :=
    allGateClauses n G ∪ BitEqCNF xu c1 ∪ BitEqCNF xw c2 ∪ carrySumCNF c1 c2 c3 d1 d2 d3
  have hsub0 : allGateClauses n G ⊆ F0 := fun C hC => Or.inl (Or.inl (Or.inl hC))
  have dFA3 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF xu xw c3 xv c3') :=
    derivable_mono (derive_FA hFA3) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dFA6 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF d1 d2 d3 yv d3') :=
    derivable_mono (derive_FA hFA6) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dAll := derivable_union dFA3 dFA6
  let H : Set (Clause ℕ) :=
    (faCNF xu xw c3 xv c3' ∪ faCNF d1 d2 d3 yv d3') ∪
    BitEqCNF xu c1 ∪ BitEqCNF xw c2 ∪ carrySumCNF c1 c2 c3 d1 d2 d3
  let S : Finset ℕ := {c1, c2, c3, d1, d2, d3, xu, xw, xv, yv, c3', d3'}
  have hScard : S.card ≤ 12 := by
    have : S = ([c1, c2, c3, d1, d2, d3, xu, xw, xv, yv, c3', d3'] : List ℕ).toFinset := by simp [S]
    rw [this]; exact le_trans (List.toFinset_card_le _) (by simp)
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc1
    · exact hc2
    · exact hFA3.2.2.1
    · exact hFA6.1
    · exact hFA6.2.1
    · exact hFA6.2.2.1
    · exact hFA3.1
    · exact hFA3.2.1
    · exact hFA3.2.2.2.1
    · exact hFA6.2.2.2.1
    · exact hFA3.2.2.2.2.1
    · exact hFA6.2.2.2.2.1
  have hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with (((h | h) | h) | h)
    · rcases h with h | h
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [S]) C h l hl
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [S]) C h l hl
  have hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → x xv = x yv ∧ x c3' = x d3' := by
    intro x hx
    have e3 : faPred xu xw c3 xv c3' x := (fullCNF_sat_iff (faPred_dependsOn xu xw c3 xv c3') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl hC)))))
    have e6 : faPred d1 d2 d3 yv d3' x := (fullCNF_sat_iff (faPred_dependsOn d1 d2 d3 yv d3') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inr hC)))))
    have exu : x xu = x c1 := (fullCNF_sat_iff (bitEq_dependsOn xu c1) x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
    have exw : x xw = x c2 := (fullCNF_sat_iff (bitEq_dependsOn xw c2) x).mp
      (fun C hC => hx C (Or.inl (Or.inr hC)))
    have ecar : carrySumPred c1 c2 c3 d1 d2 d3 x := (fullCNF_sat_iff (carrySum_dependsOn c1 c2 c3 d1 d2 d3) x).mp
      (fun C hC => hx C (Or.inr hC))
    simp only [faPred, carrySumPred, exu, exw] at e3 e6 ecar
    have hxv_lt : (x xv).toNat ≤ 1 := by cases x xv <;> simp
    have hyv_lt : (x yv).toNat ≤ 1 := by cases x yv <;> simp
    have hbit1 : (x xv).toNat = (x yv).toNat := by omega
    have hbit2 : (x c3').toNat = (x d3').toNat := by omega
    constructor
    · cases h1 : x xv <;> cases h2 : x yv <;> simp_all
    · cases h1 : x c3' <;> cases h2 : x d3' <;> simp_all
  have hHsub : H ⊆ F0 ∪ (faCNF xu xw c3 xv c3' ∪ faCNF d1 d2 d3 yv d3') := by
    intro C hC
    rcases hC with (((h | h) | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
  have hO1c : ({xv, yv} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le xv {yv}; simp at *; omega
  have hO2c : ({c3', d3'} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le c3' {d3'}; simp at *; omega
  have hO1S : ({xv, yv} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have hO2S : ({c3', d3'} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have dOut1 := derive_fullCNF (O := {xv, yv}) hHsub hSB hHS hO1S
    (bitEq_dependsOn xv yv) (fun x hx => (hsem x hx).1)
  have dOut2 := derive_fullCNF (O := {c3', d3'}) hHsub hSB hHS hO2S
    (bitEq_dependsOn c3' d3') (fun x hx => (hsem x hx).2)
  have dOut1' := derivable_mono dOut1 Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 14))) Set.Subset.rfl
  have dOut2' := derivable_mono dOut2 Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 14))) Set.Subset.rfl
  have htr := derivable_trans_only dAll (derivable_union dOut1' dOut2')
  refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
  dsimp only [K_slice]; norm_num

private lemma recombine_base_pair {n : ℕ} {G : List (ℕ × ℕ)} {a b r1 b1 z0 s1 c1 s2 c2 : ℕ}
    (hmatch : (r1 = a ∧ b1 = b) ∨ (r1 = b ∧ b1 = a))
    (hFA1 : HasFA n G a b z0 s1 c1)
    (hFA2 : HasFA n G r1 b1 z0 s2 c2) :
    Derivable (allGateClauses n G) (n + G.length) 30 K_slice
      (BitEqCNF s1 s2 ∪ BitEqCNF c1 c2) := by
  have d1 := derivable_mono (derive_FA hFA1) Set.Subset.rfl le_rfl (by omega : 12 ≤ 30) le_rfl Set.Subset.rfl
  have d2 := derivable_mono (derive_FA hFA2) Set.Subset.rfl le_rfl (by omega : 12 ≤ 30) le_rfl Set.Subset.rfl
  have dAll := derivable_union d1 d2
  let H : Set (Clause ℕ) := faCNF a b z0 s1 c1 ∪ faCNF r1 b1 z0 s2 c2
  let S : Finset ℕ := {a, b, r1, b1, z0, s1, c1, s2, c2}
  have hScard : S.card ≤ 9 := by
    have : S = ([a, b, r1, b1, z0, s1, c1, s2, c2] : List ℕ).toFinset := by simp [S]
    rw [this]; exact le_trans (List.toFinset_card_le _) (by simp)
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hFA1.1
    · exact hFA1.2.1
    · exact hFA2.1
    · exact hFA2.2.1
    · exact hFA1.2.2.1
    · exact hFA1.2.2.2.1
    · exact hFA1.2.2.2.2.1
    · exact hFA2.2.2.2.1
    · exact hFA2.2.2.2.2.1
  have hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with h | h
    · have hv := fullCNF_vars _ _ C h l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with h1 | h1 | h1 | h1 | h1 <;> simp [S, h1]
    · have hv := fullCNF_vars _ _ C h l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with h1 | h1 | h1 | h1 | h1 <;> simp [S, h1]
  have hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → x s1 = x s2 ∧ x c1 = x c2 := by
    intro x hx
    have e1 : faPred a b z0 s1 c1 x := (fullCNF_sat_iff (faPred_dependsOn a b z0 s1 c1) x).mp
      (fun C hC => hx C (Or.inl hC))
    have e2 : faPred r1 b1 z0 s2 c2 x := (fullCNF_sat_iff (faPred_dependsOn r1 b1 z0 s2 c2) x).mp
      (fun C hC => hx C (Or.inr hC))
    simp only [faPred] at e1 e2
    have hs1 : (x s1).toNat ≤ 1 := by cases x s1 <;> simp
    have hs2 : (x s2).toNat ≤ 1 := by cases x s2 <;> simp
    have hsum : (x s1).toNat + 2 * (x c1).toNat = (x s2).toNat + 2 * (x c2).toNat := by
      rcases hmatch with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    have hbit1 : (x s1).toNat = (x s2).toNat := by omega
    have hbit2 : (x c1).toNat = (x c2).toNat := by omega
    constructor
    · cases h1 : x s1 <;> cases h2 : x s2 <;> simp_all
    · cases h1 : x c1 <;> cases h2 : x c2 <;> simp_all
  have hO1c : ({s1, s2} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le s1 {s2}; simp at *; omega
  have hO2c : ({c1, c2} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le c1 {c2}; simp at *; omega
  have hO1S : ({s1, s2} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have hO2S : ({c1, c2} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have hHsub : H ⊆ allGateClauses n G ∪ H := Set.subset_union_right
  have dOut1 := derive_fullCNF (O := {s1, s2}) hHsub hSB hHS hO1S
    (bitEq_dependsOn s1 s2) (fun x hx => (hsem x hx).1)
  have dOut2 := derive_fullCNF (O := {c1, c2}) hHsub hSB hHS hO2S
    (bitEq_dependsOn c1 c2) (fun x hx => (hsem x hx).2)
  have dOut1' := derivable_mono dOut1 Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 11))) Set.Subset.rfl
  have dOut2' := derivable_mono dOut2 Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 11))) Set.Subset.rfl
  have htr := derivable_trans_only dAll (derivable_union dOut1' dOut2')
  refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
  dsimp only [K_slice]; norm_num

private lemma recombine_tree {n : ℕ} (z0 : ℕ) (d : ℕ) :
    ∀ {G : List (ℕ × ℕ)} {xs rs bs : ℕ → ℕ} {Xbits Xcar Rbits Rcar Bbits Bcar : ℕ → ℕ → ℕ → ℕ},
      ValidCirc n G → z0 < n + G.length →
      HasCounterTree n G z0 (d + 1) xs Xbits Xcar →
      HasCounterTree n G z0 d rs Rbits Rcar →
      HasCounterTree n G z0 d bs Bbits Bcar →
      (∀ t ≤ d, ∀ pos < 2 ^ (d - t), ∀ i ≤ t,
        Rbits t pos i < n + G.length ∧ Bbits t pos i < n + G.length) →
      (∀ pos < 2 ^ d,
        (rs pos = xs (2 * pos) ∧ bs pos = xs (2 * pos + 1)) ∨
        (rs pos = xs (2 * pos + 1) ∧ bs pos = xs (2 * pos))) →
      ∃ (G' : List (ℕ × ℕ)) (Yroot Ycar : ℕ → ℕ),
        G <+: G' ∧ G'.length + 9 * (d + 3) = G.length + 36 * 2 ^ d ∧ ValidCirc n G' ∧
        HasRipple n G' z0 (d + 1) (fun i => Rbits d 0 i) (fun i => Bbits d 0 i) Yroot Ycar ∧
        (∀ i ≤ d + 1, Yroot i < n + G'.length ∧ Ycar i < n + G'.length) ∧
        Derivable (allGateClauses n G') (n + G'.length) 30 (4 * K_slice * 2 ^ d - (d + 3) * K_slice)
          (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 0 i) (Yroot i)) := by
  induction d with
  | zero =>
    intro G xs rs bs Xbits Xcar Rbits Rcar Bbits Bcar hV hz ctX ctR ctB hltRB hmatch
    have hR0 : ∀ i < 1, Rbits 0 0 i < n + G.length := fun i hi => by
      have : i = 0 := by omega
      subst this; exact (hltRB 0 le_rfl 0 (by simp) 0 le_rfl).1
    have hB0 : ∀ i < 1, Bbits 0 0 i < n + G.length := fun i hi => by
      have : i = 0 := by omega
      subst this; exact (hltRB 0 le_rfl 0 (by simp) 0 le_rfl).2
    obtain ⟨G', Yroot, Ycar, hp, hl, hV', hrY, hltY⟩ :=
      exists_addRipple hV hz 1 (fun i => Rbits 0 0 i) (fun i => Bbits 0 0 i) hR0 hB0
    have hrX : HasRipple n G' z0 1 (fun i => Xbits 0 0 i) (fun i => Xbits 0 1 i)
        (fun i => Xbits 1 0 i) (fun i => Xcar 1 0 i) := by
      simpa using hasRipple_mono hp (ctX.2 0 (Nat.zero_lt_one) 0 (by simp))
    have hFA1 : HasFA n G' (xs 0) (xs 1) z0 (Xbits 1 0 0) (Xbits 1 0 1) := by
      have h := hrX.2.1 0 Nat.zero_lt_one
      dsimp only at h
      have h1 : Xcar 1 0 0 = z0 := hrX.1
      have h2 : Xbits 1 0 1 = Xcar 1 0 1 := hrX.2.2
      rw [ctX.1 0 (by simp), ctX.1 1 (by simp), h1, ← h2] at h
      exact h
    have hFA2 : HasFA n G' (rs 0) (bs 0) z0 (Yroot 0) (Yroot 1) := by
      have h := hrY.2.1 0 Nat.zero_lt_one
      dsimp only at h
      rw [ctR.1 0 (by simp), ctB.1 0 (by simp), hrY.1, ← hrY.2.2] at h
      exact h
    have hder := recombine_base_pair (hmatch 0 (by simp)) hFA1 hFA2
    refine ⟨G', Yroot, Ycar, hp, by omega, hV', hrY, hltY, ?_⟩
    refine derivable_mono hder Set.Subset.rfl le_rfl le_rfl (by omega) ?_
    intro C hC
    simp only [Set.mem_iUnion, Finset.mem_range] at hC
    rcases hC with ⟨i, hi, hCi⟩
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · exact Or.inl hCi
    · exact Or.inr hCi
  | succ d ih =>
    intro G xs rs bs Xbits Xcar Rbits Rcar Bbits Bcar hV hz ctX ctR ctB hltRB hmatch
    have hltL : ∀ t ≤ d, ∀ pos < 2 ^ (d - t), ∀ i ≤ t,
        Rbits t pos i < n + G.length ∧ Bbits t pos i < n + G.length :=
      fun t ht pos hpos i hi => hltRB t (Nat.le_succ_of_le ht) pos
        (lt_of_lt_of_le hpos (Nat.pow_le_pow_right (by omega) (by omega))) i hi
    have hmatchL : ∀ pos < 2 ^ d,
        (rs pos = xs (2 * pos) ∧ bs pos = xs (2 * pos + 1)) ∨
        (rs pos = xs (2 * pos + 1) ∧ bs pos = xs (2 * pos)) :=
      fun pos hpos => hmatch pos (lt_of_lt_of_le hpos (Nat.pow_le_pow_right (by omega) (Nat.le_succ d)))
    obtain ⟨G₁, YL, cL, p₁, l₁, v₁, hrYL, hltYL, derL⟩ :=
      ih hV hz (counterTree_left ctX) (counterTree_left ctR) (counterTree_left ctB) hltL hmatchL
    have hz₁ : z0 < n + G₁.length := by have := p₁.length_le; omega
    have hltR : ∀ t ≤ d, ∀ pos < 2 ^ (d - t), ∀ i ≤ t,
        Rbits t (2 ^ (d - t) + pos) i < n + G₁.length ∧
        Bbits t (2 ^ (d - t) + pos) i < n + G₁.length := by
      intro t ht pos hpos i hi
      have hexp : d + 1 - t = (d - t) + 1 := by omega
      have hlt : 2 ^ (d - t) + pos < 2 ^ (d + 1 - t) := by rw [hexp, Nat.pow_succ]; omega
      have h := hltRB t (Nat.le_succ_of_le ht) (2 ^ (d - t) + pos) hlt i hi
      have := p₁.length_le
      exact ⟨by omega, by omega⟩
    have hmatchR : ∀ pos < 2 ^ d,
        (rs (2 ^ d + pos) = xs (2 ^ (d + 1) + 2 * pos) ∧ bs (2 ^ d + pos) = xs (2 ^ (d + 1) + (2 * pos + 1))) ∨
        (rs (2 ^ d + pos) = xs (2 ^ (d + 1) + (2 * pos + 1)) ∧ bs (2 ^ d + pos) = xs (2 ^ (d + 1) + 2 * pos)) := by
      intro pos hpos
      have hlt : 2 ^ d + pos < 2 ^ (d + 1) := by rw [Nat.pow_succ]; omega
      have hm := hmatch (2 ^ d + pos) hlt
      have e1 : 2 * (2 ^ d + pos) = 2 ^ (d + 1) + 2 * pos := by rw [Nat.pow_succ]; ring
      have e2 : 2 * (2 ^ d + pos) + 1 = 2 ^ (d + 1) + (2 * pos + 1) := by omega
      rw [e2, e1] at hm
      exact hm
    obtain ⟨G₂, YR, cR, p₂, l₂, v₂, hrYR, hltYR, derR⟩ :=
      ih v₁ hz₁ (hasCounterTree_mono p₁ (counterTree_right ctX))
        (hasCounterTree_mono p₁ (counterTree_right ctR))
        (hasCounterTree_mono p₁ (counterTree_right ctB)) hltR hmatchR
    have hz₂ : z0 < n + G₂.length := by have := (p₁.trans p₂).length_le; omega
    have hRroot : ∀ i < d + 2, Rbits (d + 1) 0 i < n + G₂.length := by
      intro i hi
      have := (hltRB (d + 1) le_rfl 0 (by simp) i (by omega)).1
      have := (p₁.trans p₂).length_le; omega
    have hBroot : ∀ i < d + 2, Bbits (d + 1) 0 i < n + G₂.length := by
      intro i hi
      have := (hltRB (d + 1) le_rfl 0 (by simp) i (by omega)).2
      have := (p₁.trans p₂).length_le; omega
    obtain ⟨G₃, Yroot, Ycar, p₃, l₃, v₃, hrY, hltY⟩ :=
      exists_addRipple v₂ hz₂ (d + 2) (fun i => Rbits (d + 1) 0 i) (fun i => Bbits (d + 1) 0 i)
        hRroot hBroot
    have p13 : G <+: G₃ := p₁.trans (p₂.trans p₃)
    have p23 : G₁ <+: G₃ := p₂.trans p₃
    have hrYL3 : HasRipple n G₃ z0 (d + 1) (fun i => Rbits d 0 i) (fun i => Bbits d 0 i) YL cL :=
      hasRipple_mono p23 hrYL
    have hrYR3 : HasRipple n G₃ z0 (d + 1) (fun i => Rbits d 1 i) (fun i => Bbits d 1 i) YR cR := by
      have h := hasRipple_mono p₃ hrYR
      simpa only [Nat.sub_self, Nat.pow_zero, Nat.add_zero] using h
    have hrX3 : HasRipple n G₃ z0 (d + 2) (fun i => Xbits (d + 1) 0 i) (fun i => Xbits (d + 1) 1 i)
        (fun i => Xbits (d + 2) 0 i) (fun i => Xcar (d + 2) 0 i) := by
      simpa using hasRipple_mono p13 (ctX.2 (d + 1) (Nat.lt_succ_self _) 0 (by simp))
    have hrR3 : HasRipple n G₃ z0 (d + 1) (fun i => Rbits d 0 i) (fun i => Rbits d 1 i)
        (fun i => Rbits (d + 1) 0 i) (fun i => Rcar (d + 1) 0 i) := by
      simpa using hasRipple_mono p13 (ctR.2 d (Nat.lt_succ_self _) 0 (by simp))
    have hrB3 : HasRipple n G₃ z0 (d + 1) (fun i => Bbits d 0 i) (fun i => Bbits d 1 i)
        (fun i => Bbits (d + 1) 0 i) (fun i => Bcar (d + 1) 0 i) := by
      simpa using hasRipple_mono p13 (ctB.2 d (Nat.lt_succ_self _) 0 (by simp))
    let eqL : Set (Clause ℕ) := ⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 0 i) (YL i)
    let eqR : Set (Clause ℕ) := ⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 1 i) (YR i)
    have derL3 : Derivable (allGateClauses n G₃) (n + G₃.length) 30
        (4 * K_slice * 2 ^ d - (d + 3) * K_slice) eqL :=
      derivable_mono derL (allGateClauses_mono p23) (by have := p23.length_le; omega) le_rfl le_rfl Set.Subset.rfl
    have derR3 : Derivable (allGateClauses n G₃) (n + G₃.length) 30
        (4 * K_slice * 2 ^ d - (d + 3) * K_slice) eqR := by
      have h : Derivable (allGateClauses n G₃) (n + G₃.length) 30
          (4 * K_slice * 2 ^ d - (d + 3) * K_slice)
          (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) (2 ^ (d + 1 - (d + 1)) + 0) i) (YR i)) :=
        derivable_mono derR (allGateClauses_mono p₃) (by have := p₃.length_le; omega) le_rfl le_rfl Set.Subset.rfl
      simpa only [eqR, Nat.sub_self, Nat.pow_zero, Nat.add_zero] using h
    have derLR := derivable_union derL3 derR3
    let F1 : Set (Clause ℕ) := allGateClauses n G₃ ∪ (eqL ∪ eqR)
    let Inv : ℕ → Set (Clause ℕ) := fun i =>
      carrySumCNF (cL i) (cR i) (Xcar (d + 2) 0 i) (Rcar (d + 1) 0 i) (Bcar (d + 1) 0 i) (Ycar i)
    let Emit : ℕ → Set (Clause ℕ) := fun i => BitEqCNF (Xbits (d + 2) 0 i) (Yroot i)
    have hInv0 : Derivable F1 (n + G₃.length) 30 0 (Inv 0) := by
      have h0 : Inv 0 = ∅ := by
        dsimp only [Inv]
        have hx0 : Xcar (d + 2) 0 0 = z0 := hrX3.1
        have hr0 : Rcar (d + 1) 0 0 = z0 := hrR3.1
        have hb0 : Bcar (d + 1) 0 0 = z0 := hrB3.1
        rw [hrYL3.1, hrYR3.1, hx0, hr0, hb0, hrY.1]
        exact carrySum_refl z0
      rw [h0]; exact derivable_empty _ _ _
    have hStep : ∀ i < d + 1, Derivable (F1 ∪ Inv i) (n + G₃.length) 30 K_slice
        (Inv (i + 1) ∪ Emit i) := by
      intro i hi
      have hFsub : allGateClauses n G₃ ∪ BitEqCNF (Xbits (d + 1) 0 i) (YL i) ∪
          BitEqCNF (Xbits (d + 1) 1 i) (YR i) ∪ Inv i ⊆ F1 ∪ Inv i := by
        intro C hC
        rcases hC with ((h | h) | h) | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr (Or.inl (Set.mem_biUnion (Finset.mem_range.mpr (by omega)) h)))
        · exact Or.inl (Or.inr (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (by omega)) h)))
        · exact Or.inr h
      have hs := recombine_slice (hrYL3.2.1 i hi) (hrYR3.2.1 i hi)
        (hrX3.2.1 i (Nat.lt_succ_of_lt hi)) (hrR3.2.1 i hi) (hrB3.2.1 i hi)
        (hrY.2.1 i (Nat.lt_succ_of_lt hi))
      exact derivable_mono hs hFsub le_rfl le_rfl le_rfl Set.Subset.rfl
    have hChain := derivable_range_chain Inv Emit (d + 1) hInv0 hStep
    have hTop : Derivable (F1 ∪ (Inv (d + 1) ∪ ⋃ i ∈ Finset.range (d + 1), Emit i))
        (n + G₃.length) 30 K_slice (Emit (d + 1) ∪ Emit (d + 2)) := by
      have hcLlt : cL (d + 1) < n + G₃.length := by
        have := (hltYL (d + 1) le_rfl).2; have := p23.length_le; omega
      have hcRlt : cR (d + 1) < n + G₃.length := by
        have := (hltYR (d + 1) le_rfl).2; have := p₃.length_le; omega
      have hFA3 : HasFA n G₃ (Xbits (d + 1) 0 (d + 1)) (Xbits (d + 1) 1 (d + 1))
          (Xcar (d + 2) 0 (d + 1)) (Xbits (d + 2) 0 (d + 1)) (Xbits (d + 2) 0 (d + 2)) := by
        have h := hrX3.2.1 (d + 1) (Nat.lt_succ_self _)
        rwa [← hrX3.2.2] at h
      have hFA6 : HasFA n G₃ (Rcar (d + 1) 0 (d + 1)) (Bcar (d + 1) 0 (d + 1))
          (Ycar (d + 1)) (Yroot (d + 1)) (Yroot (d + 2)) := by
        have h := hrY.2.1 (d + 1) (Nat.lt_succ_self _)
        rwa [hrR3.2.2, hrB3.2.2, ← hrY.2.2] at h
      have ht := recombine_top hcLlt hcRlt hFA3 hFA6
      have hFsub : allGateClauses n G₃ ∪ BitEqCNF (Xbits (d + 1) 0 (d + 1)) (cL (d + 1)) ∪
          BitEqCNF (Xbits (d + 1) 1 (d + 1)) (cR (d + 1)) ∪ Inv (d + 1) ⊆
          F1 ∪ (Inv (d + 1) ∪ ⋃ i ∈ Finset.range (d + 1), Emit i) := by
        intro C hC
        rcases hC with ((h | h) | h) | h
        · exact Or.inl (Or.inl h)
        · rw [← hrYL3.2.2] at h
          exact Or.inl (Or.inr (Or.inl (Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self _)) h)))
        · rw [← hrYR3.2.2] at h
          exact Or.inl (Or.inr (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_self _)) h)))
        · exact Or.inr (Or.inl h)
      exact derivable_mono ht hFsub le_rfl le_rfl le_rfl Set.Subset.rfl
    have hComb1 := derivable_trans hChain hTop
    have hComb2 := derivable_trans_only derLR hComb1
    have hglen : G₃.length + 9 * (d + 4) = G.length + 36 * 2 ^ (d + 1) := by
      rw [Nat.pow_succ]; omega
    have hplen : (4 * K_slice * 2 ^ d - (d + 3) * K_slice) +
        (4 * K_slice * 2 ^ d - (d + 3) * K_slice) +
        (0 + (d + 1) * K_slice + K_slice) ≤
        4 * K_slice * 2 ^ (d + 1) - (d + 4) * K_slice := by
      have hge : (d + 3) * K_slice ≤ 4 * K_slice * 2 ^ d := by
        have h2d : d + 3 ≤ 4 * 2 ^ d := by
          clear * -
          induction d with
          | zero => simp
          | succ k ih => rw [Nat.pow_succ]; omega
        calc (d + 3) * K_slice ≤ (4 * 2 ^ d) * K_slice := Nat.mul_le_mul_right _ h2d
          _ = 4 * K_slice * 2 ^ d := by ring
      have hexp : 4 * K_slice * 2 ^ (d + 1) = 4 * K_slice * 2 ^ d + 4 * K_slice * 2 ^ d := by
        rw [Nat.pow_succ]; ring
      have h1 : (d + 1) * K_slice + K_slice = (d + 2) * K_slice := by ring
      have h2 : (d + 3) * K_slice + (d + 3) * K_slice = (d + 2) * K_slice + (d + 4) * K_slice := by ring
      omega
    refine ⟨G₃, Yroot, Ycar, p13, hglen, v₃, hrY, hltY, ?_⟩
    refine derivable_mono hComb2 Set.Subset.rfl le_rfl le_rfl hplen ?_
    intro C hC
    simp only [Set.mem_iUnion, Finset.mem_range] at hC
    rcases hC with ⟨i, hi, hCi⟩
    by_cases h1 : i = d + 2
    · rw [h1] at hCi; exact Or.inr (Or.inr hCi)
    · by_cases h2 : i = d + 1
      · rw [h2] at hCi; exact Or.inr (Or.inl hCi)
      · exact Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hCi))

private def K_cong : ℕ := 2 ^ 20

private lemma adder_congr_step {n : ℕ} {G : List (ℕ × ℕ)}
    {a1 b1 c1 s1 c1' a2 b2 c2 s2 c2' : ℕ}
    (hFA1 : HasFA n G a1 b1 c1 s1 c1')
    (hFA2 : HasFA n G a2 b2 c2 s2 c2') :
    Derivable (allGateClauses n G ∪ BitEqCNF a1 a2 ∪ BitEqCNF b1 b2 ∪ BitEqCNF c1 c2)
      (n + G.length) 30 K_cong
      (BitEqCNF c1' c2' ∪ BitEqCNF s1 s2) := by
  let F0 := allGateClauses n G ∪ BitEqCNF a1 a2 ∪ BitEqCNF b1 b2 ∪ BitEqCNF c1 c2
  have hsub0 : allGateClauses n G ⊆ F0 := fun C hC => Or.inl (Or.inl (Or.inl hC))
  have d1 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF a1 b1 c1 s1 c1') :=
    derivable_mono (derive_FA hFA1) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have d2 : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF a2 b2 c2 s2 c2') :=
    derivable_mono (derive_FA hFA2) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dAll := derivable_union d1 d2
  let H : Set (Clause ℕ) :=
    (faCNF a1 b1 c1 s1 c1' ∪ faCNF a2 b2 c2 s2 c2') ∪ BitEqCNF a1 a2 ∪ BitEqCNF b1 b2 ∪ BitEqCNF c1 c2
  let S : Finset ℕ := {a1, b1, c1, s1, c1', a2, b2, c2, s2, c2'}
  have hScard : S.card ≤ 10 := by
    have : S = ([a1, b1, c1, s1, c1', a2, b2, c2, s2, c2'] : List ℕ).toFinset := by simp [S]
    rw [this]; exact le_trans (List.toFinset_card_le _) (by simp)
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hFA1.1
    · exact hFA1.2.1
    · exact hFA1.2.2.1
    · exact hFA1.2.2.2.1
    · exact hFA1.2.2.2.2.1
    · exact hFA2.1
    · exact hFA2.2.1
    · exact hFA2.2.2.1
    · exact hFA2.2.2.2.1
    · exact hFA2.2.2.2.2.1
  have hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with (((h | h) | h) | h)
    · rcases h with h | h
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [S]) C h l hl
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl | rfl | rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
  have hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → x c1' = x c2' ∧ x s1 = x s2 := by
    intro x hx
    have e1 : faPred a1 b1 c1 s1 c1' x := (fullCNF_sat_iff (faPred_dependsOn a1 b1 c1 s1 c1') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inl hC)))))
    have e2 : faPred a2 b2 c2 s2 c2' x := (fullCNF_sat_iff (faPred_dependsOn a2 b2 c2 s2 c2') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl (Or.inr hC)))))
    have ea : x a1 = x a2 := (fullCNF_sat_iff (bitEq_dependsOn a1 a2) x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
    have eb : x b1 = x b2 := (fullCNF_sat_iff (bitEq_dependsOn b1 b2) x).mp
      (fun C hC => hx C (Or.inl (Or.inr hC)))
    have ec : x c1 = x c2 := (fullCNF_sat_iff (bitEq_dependsOn c1 c2) x).mp
      (fun C hC => hx C (Or.inr hC))
    simp only [faPred, ea, eb, ec] at e1 e2
    have hs1 : (x s1).toNat ≤ 1 := by cases x s1 <;> simp
    have hs2 : (x s2).toNat ≤ 1 := by cases x s2 <;> simp
    have h1 : (x c1').toNat = (x c2').toNat := by omega
    have h2 : (x s1).toNat = (x s2).toNat := by omega
    constructor
    · cases h : x c1' <;> cases h' : x c2' <;> simp_all
    · cases h : x s1 <;> cases h' : x s2 <;> simp_all
  have hHsub : H ⊆ F0 ∪ (faCNF a1 b1 c1 s1 c1' ∪ faCNF a2 b2 c2 s2 c2') := by
    intro C hC
    rcases hC with (((h | h) | h) | h)
    · exact Or.inr h
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
  have hO1c : ({c1', c2'} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le c1' {c2'}; simp at *; omega
  have hO2c : ({s1, s2} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le s1 {s2}; simp at *; omega
  have hO1S : ({c1', c2'} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have hO2S : ({s1, s2} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have dOut1 := derive_fullCNF (O := {c1', c2'}) hHsub hSB hHS hO1S
    (bitEq_dependsOn c1' c2') (fun x hx => (hsem x hx).1)
  have dOut2 := derive_fullCNF (O := {s1, s2}) hHsub hSB hHS hO2S
    (bitEq_dependsOn s1 s2) (fun x hx => (hsem x hx).2)
  have dOut1' := derivable_mono dOut1 Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 12))) Set.Subset.rfl
  have dOut2' := derivable_mono dOut2 Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 12))) Set.Subset.rfl
  have htr := derivable_trans_only dAll (derivable_union dOut1' dOut2')
  refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
  dsimp only [K_cong]; norm_num

private lemma adder_congr {n : ℕ} {G : List (ℕ × ℕ)} {z0 k : ℕ}
    {A1 B1 S1 c1 A2 B2 S2 c2 : ℕ → ℕ}
    (hr1 : HasRipple n G z0 k A1 B1 S1 c1)
    (hr2 : HasRipple n G z0 k A2 B2 S2 c2) :
    Derivable (allGateClauses n G ∪
        (⋃ i ∈ Finset.range k, BitEqCNF (A1 i) (A2 i)) ∪
        (⋃ i ∈ Finset.range k, BitEqCNF (B1 i) (B2 i)))
      (n + G.length) 30 (k * K_cong)
      (⋃ i ∈ Finset.range (k + 1), BitEqCNF (S1 i) (S2 i)) := by
  let F1 := allGateClauses n G ∪
    (⋃ i ∈ Finset.range k, BitEqCNF (A1 i) (A2 i)) ∪
    (⋃ i ∈ Finset.range k, BitEqCNF (B1 i) (B2 i))
  let Inv : ℕ → Set (Clause ℕ) := fun i => BitEqCNF (c1 i) (c2 i)
  let Emit : ℕ → Set (Clause ℕ) := fun i => BitEqCNF (S1 i) (S2 i)
  have h0 : Derivable F1 (n + G.length) 30 0 (Inv 0) := by
    have : Inv 0 = ∅ := by dsimp only [Inv]; rw [hr1.1, hr2.1]; exact bitEq_refl z0
    rw [this]; exact derivable_empty _ _ _
  have hstep : ∀ i < k, Derivable (F1 ∪ Inv i) (n + G.length) 30 K_cong (Inv (i + 1) ∪ Emit i) := by
    intro i hi
    have hs := adder_congr_step (hr1.2.1 i hi) (hr2.2.1 i hi)
    have hFsub : allGateClauses n G ∪ BitEqCNF (A1 i) (A2 i) ∪ BitEqCNF (B1 i) (B2 i) ∪ Inv i ⊆
        F1 ∪ Inv i := by
      intro C hC
      rcases hC with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr hi) h)))
      · exact Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr hi) h))
      · exact Or.inr h
    exact derivable_mono hs hFsub le_rfl le_rfl le_rfl Set.Subset.rfl
  have hch := derivable_range_chain Inv Emit k h0 hstep
  refine derivable_mono hch Set.Subset.rfl le_rfl le_rfl (by omega) ?_
  intro C hC
  simp only [Set.mem_iUnion, Finset.mem_range] at hC
  rcases hC with ⟨i, hi, hCi⟩
  by_cases hik : i = k
  · rw [hik, hr1.2.2, hr2.2.2] at hCi
    exact Or.inl hCi
  · exact Or.inr (Set.mem_biUnion (Finset.mem_range.mpr (by omega)) hCi)

private lemma bitEq_trans3 {B a b c d : ℕ}
    (ha : a < B) (hb : b < B) (hc : c < B) (hd : d < B) :
    Derivable (BitEqCNF a b ∪ BitEqCNF b c ∪ BitEqCNF c d) B 30 (3 * 2 ^ 6) (BitEqCNF a d) := by
  let S : Finset ℕ := {a, b, c, d}
  have hScard : S.card ≤ 4 := by
    have : S = ([a, b, c, d] : List ℕ).toFinset := by simp [S]
    rw [this]; exact le_trans (List.toFinset_card_le _) (by simp)
  have hSB : ∀ v ∈ S, v < B := by
    intro v hv; simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hHS : ∀ C ∈ (BitEqCNF a b ∪ BitEqCNF b c ∪ BitEqCNF c d), ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with (h | h) | h
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
    · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv; rcases hv with rfl | rfl <;> simp [S]) C h l hl
  have hsem : ∀ x : ℕ → Bool,
      (∀ C ∈ (BitEqCNF a b ∪ BitEqCNF b c ∪ BitEqCNF c d), ClauseSat x C) → x a = x d := by
    intro x hx
    have e1 : x a = x b := (fullCNF_sat_iff (bitEq_dependsOn a b) x).mp
      (fun C hC => hx C (Or.inl (Or.inl hC)))
    have e2 : x b = x c := (fullCNF_sat_iff (bitEq_dependsOn b c) x).mp
      (fun C hC => hx C (Or.inl (Or.inr hC)))
    have e3 : x c = x d := (fullCNF_sat_iff (bitEq_dependsOn c d) x).mp
      (fun C hC => hx C (Or.inr hC))
    rw [e1, e2, e3]
  have hOc : ({a, d} : Finset ℕ).card ≤ 2 := by
    have := Finset.card_insert_le a {d}; simp at *; omega
  have hOS : ({a, d} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [S]
  have hder := derive_fullCNF (O := {a, d}) Set.Subset.rfl hSB hHS hOS
    (bitEq_dependsOn a d) hsem
  exact derivable_mono hder Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 6))) Set.Subset.rfl

private def K_eq : ℕ := 8 * K_slice + K_cong + 6 * 2 ^ 6

private lemma prove_perm_equiv {n : ℕ} (z0 : ℕ) (d : ℕ) :
    ∀ {G : List (ℕ × ℕ)} {xs ys : ℕ → ℕ} {Xbits Xcar Ybits Ycar : ℕ → ℕ → ℕ → ℕ}
      (σ : Equiv.Perm (Fin (2 ^ d))),
      ValidCirc n G → z0 < n + G.length →
      (∀ p < 2 ^ d, xs p < n + G.length ∧ ys p < n + G.length) →
      (∀ i : Fin (2 ^ d), xs i.val = ys (σ i).val) →
      HasCounterTree n G z0 d xs Xbits Xcar →
      HasCounterTree n G z0 d ys Ybits Ycar →
      (∀ i ≤ d, Xbits d 0 i < n + G.length ∧ Ybits d 0 i < n + G.length) →
      ∃ G' : List (ℕ × ℕ),
        G <+: G' ∧ G'.length ≤ G.length + 72 * d * 2 ^ d ∧ ValidCirc n G' ∧
        Derivable (allGateClauses n G') (n + G'.length) 30 (K_eq * d * 2 ^ d)
          (⋃ i ∈ Finset.range (d + 1), BitEqCNF (Xbits d 0 i) (Ybits d 0 i)) := by
  induction d with
  | zero =>
    intro G xs ys Xbits Xcar Ybits Ycar σ hV hz hxy hperm ctX ctY hlt
    refine ⟨G, List.prefix_refl G, by simp, hV, ?_⟩
    have h0 : σ ⟨0, by simp⟩ = ⟨0, by simp⟩ := by
      apply Fin.ext; have := (σ ⟨0, by simp⟩).isLt; omega
    have heq : Xbits 0 0 0 = Ybits 0 0 0 := by
      rw [ctX.1 0 (by simp), ctY.1 0 (by simp)]
      have := hperm ⟨0, by simp⟩
      simpa [h0] using this
    have hempty : (⋃ i ∈ Finset.range 1, BitEqCNF (Xbits 0 0 i) (Ybits 0 0 i)) = ∅ := by
      ext C
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, hi, hC⟩
      have hi0 : i = 0 := by omega
      rw [hi0, heq, bitEq_refl] at hC
      exact hC
    rw [hempty]
    exact derivable_empty _ _ _
  | succ d ih =>
    intro G xs ys Xbits Xcar Ybits Ycar σ hV hz hxy hperm ctX ctY hlt
    have hexp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
    let eqFin : Fin (2 ^ (d + 1)) ≃ Fin (2 * 2 ^ d) := finCongr hexp
    let σ' : Equiv.Perm (Fin (2 * 2 ^ d)) := eqFin.symm.trans (σ.trans eqFin)
    obtain ⟨rowIdx, colIdx, σc, hrowP, hcolP, hσc⟩ := perm_two_color_split σ'
    let xR : ℕ → ℕ := fun p => if hp : p < 2 ^ d then xs (rowIdx false ⟨p, hp⟩).val else z0
    let xB : ℕ → ℕ := fun p => if hp : p < 2 ^ d then xs (rowIdx true ⟨p, hp⟩).val else z0
    let yR : ℕ → ℕ := fun p => if hp : p < 2 ^ d then ys (colIdx false ⟨p, hp⟩).val else z0
    let yB : ℕ → ℕ := fun p => if hp : p < 2 ^ d then ys (colIdx true ⟨p, hp⟩).val else z0
    have hxRlt : ∀ p < 2 ^ d, xR p < n + G.length := fun p hp => by
      simp only [xR, hp, ↓reduceDIte]
      exact (hxy _ (by have := (rowIdx false ⟨p, hp⟩).isLt; omega)).1
    have hxBlt : ∀ p < 2 ^ d, xB p < n + G.length := fun p hp => by
      simp only [xB, hp, ↓reduceDIte]
      exact (hxy _ (by have := (rowIdx true ⟨p, hp⟩).isLt; omega)).1
    have hyRlt : ∀ p < 2 ^ d, yR p < n + G.length := fun p hp => by
      simp only [yR, hp, ↓reduceDIte]
      exact (hxy _ (by have := (colIdx false ⟨p, hp⟩).isLt; omega)).2
    have hyBlt : ∀ p < 2 ^ d, yB p < n + G.length := fun p hp => by
      simp only [yB, hp, ↓reduceDIte]
      exact (hxy _ (by have := (colIdx true ⟨p, hp⟩).isLt; omega)).2
    obtain ⟨G1, xRbits, xRcar, p1, l1, v1, ctXR, hblXR, _⟩ := exists_buildCounterTree z0 hV hz d xR hxRlt
    obtain ⟨G2, xBbits, xBcar, p2, l2, v2, ctXB, hblXB, _⟩ :=
      exists_buildCounterTree z0 v1 (by have := p1.length_le; omega) d xB
        (fun p hp => by have := hxBlt p hp; have := p1.length_le; omega)
    obtain ⟨G3, yRbits, yRcar, p3, l3, v3, ctYR, hblYR, _⟩ :=
      exists_buildCounterTree z0 v2 (by have := (p1.trans p2).length_le; omega) d yR
        (fun p hp => by have := hyRlt p hp; have := (p1.trans p2).length_le; omega)
    obtain ⟨G4, yBbits, yBcar, p4, l4, v4, ctYB, hblYB, _⟩ :=
      exists_buildCounterTree z0 v3 (by have := (p1.trans (p2.trans p3)).length_le; omega) d yB
        (fun p hp => by have := hyBlt p hp; have := (p1.trans (p2.trans p3)).length_le; omega)
    have p04 : G <+: G4 := p1.trans (p2.trans (p3.trans p4))
    have p14 : G1 <+: G4 := p2.trans (p3.trans p4)
    have p24 : G2 <+: G4 := p3.trans p4
    have hmatchX : ∀ pos < 2 ^ d,
        (xR pos = xs (2 * pos) ∧ xB pos = xs (2 * pos + 1)) ∨
        (xR pos = xs (2 * pos + 1) ∧ xB pos = xs (2 * pos)) := by
      intro pos hpos
      simp only [xR, xB, hpos, ↓reduceDIte]
      rcases hrowP ⟨pos, hpos⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
      · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
    have hmatchY : ∀ pos < 2 ^ d,
        (yR pos = ys (2 * pos) ∧ yB pos = ys (2 * pos + 1)) ∨
        (yR pos = ys (2 * pos + 1) ∧ yB pos = ys (2 * pos)) := by
      intro pos hpos
      simp only [yR, yB, hpos, ↓reduceDIte]
      rcases hcolP ⟨pos, hpos⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
      · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
    obtain ⟨G5, Yx, YxCar, p5, l5, v5, hrYx, hltYx, derRecX⟩ :=
      recombine_tree z0 d v4 (by have := p04.length_le; omega)
        (hasCounterTree_mono p04 ctX) (hasCounterTree_mono p14 ctXR) (hasCounterTree_mono p24 ctXB)
        (fun t ht pos hpos i hi =>
          ⟨by have := hblXR t ht pos hpos i hi; have := p14.length_le; omega,
           by have := hblXB t ht pos hpos i hi; have := p24.length_le; omega⟩) hmatchX
    obtain ⟨G6, Yy, YyCar, p6, l6, v6, hrYy, hltYy, derRecY⟩ :=
      recombine_tree z0 d v5 (by have := (p04.trans p5).length_le; omega)
        (hasCounterTree_mono (p04.trans p5) ctY) (hasCounterTree_mono (p4.trans p5) ctYR)
        (hasCounterTree_mono p5 ctYB)
        (fun t ht pos hpos i hi =>
          ⟨by have := hblYR t ht pos hpos i hi; have := (p4.trans p5).length_le; omega,
           by have := hblYB t ht pos hpos i hi; have := p5.length_le; omega⟩) hmatchY
    have hpermC : ∀ c : Bool, ∀ i : Fin (2 ^ d),
        xs (rowIdx c i).val = ys (colIdx c (σc c i)).val := by
      intro c i
      have h1 := hσc c i
      have h2 := hperm (eqFin.symm (rowIdx c i))
      have he1 : (eqFin.symm (rowIdx c i)).val = (rowIdx c i).val := rfl
      have he2 : (σ (eqFin.symm (rowIdx c i))).val = (σ' (rowIdx c i)).val := rfl
      rw [he1, he2, h1] at h2
      exact h2
    have hpermR : ∀ i : Fin (2 ^ d), xR i.val = yR (σc false i).val := fun i => by
      simp only [xR, yR, i.isLt, (σc false i).isLt, ↓reduceDIte]
      exact hpermC false i
    have hpermB : ∀ i : Fin (2 ^ d), xB i.val = yB (σc true i).val := fun i => by
      simp only [xB, yB, i.isLt, (σc true i).isLt, ↓reduceDIte]
      exact hpermC true i
    have p06 : G <+: G6 := p04.trans (p5.trans p6)
    have p16 : G1 <+: G6 := p14.trans (p5.trans p6)
    have p26 : G2 <+: G6 := p24.trans (p5.trans p6)
    have p36 : G3 <+: G6 := p4.trans (p5.trans p6)
    have p46 : G4 <+: G6 := p5.trans p6
    obtain ⟨G7, p7, l7, v7, derEqR⟩ := ih (σc false) v6 (by have := p06.length_le; omega)
      (fun p hp => ⟨by have := hxRlt p hp; have := p06.length_le; omega,
                    by have := hyRlt p hp; have := p06.length_le; omega⟩)
      hpermR (hasCounterTree_mono p16 ctXR) (hasCounterTree_mono p36 ctYR)
      (fun i hi => ⟨by have := hblXR d le_rfl 0 (by simp) i hi; have := p16.length_le; omega,
                    by have := hblYR d le_rfl 0 (by simp) i hi; have := p36.length_le; omega⟩)
    obtain ⟨G8, p8, l8, v8, derEqB⟩ := ih (σc true) v7 (by have := (p06.trans p7).length_le; omega)
      (fun p hp => ⟨by have := hxBlt p hp; have := (p06.trans p7).length_le; omega,
                    by have := hyBlt p hp; have := (p06.trans p7).length_le; omega⟩)
      hpermB (hasCounterTree_mono (p26.trans p7) ctXB) (hasCounterTree_mono (p46.trans p7) ctYB)
      (fun i hi => ⟨by have := hblXB d le_rfl 0 (by simp) i hi; have := (p26.trans p7).length_le; omega,
                    by have := hblYB d le_rfl 0 (by simp) i hi; have := (p46.trans p7).length_le; omega⟩)
    have p08 : G <+: G8 := p06.trans (p7.trans p8)
    have p58 : G5 <+: G8 := p6.trans (p7.trans p8)
    have p68 : G6 <+: G8 := p7.trans p8
    have hCong : Derivable (allGateClauses n G8 ∪
        (⋃ i ∈ Finset.range (d + 1), BitEqCNF (xRbits d 0 i) (yRbits d 0 i)) ∪
        (⋃ i ∈ Finset.range (d + 1), BitEqCNF (xBbits d 0 i) (yBbits d 0 i)))
        (n + G8.length) 30 ((d + 1) * K_cong)
        (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Yx i) (Yy i)) :=
      adder_congr (hasRipple_mono p58 hrYx) (hasRipple_mono p68 hrYy)
    have derEqR8 : Derivable (allGateClauses n G8) (n + G8.length) 30 (K_eq * d * 2 ^ d)
        (⋃ i ∈ Finset.range (d + 1), BitEqCNF (xRbits d 0 i) (yRbits d 0 i)) :=
      derivable_mono derEqR (allGateClauses_mono p8) (by have := p8.length_le; omega) le_rfl le_rfl Set.Subset.rfl
    have derEqB8 := derEqB
    have derRB8 := derivable_union derEqR8 derEqB8
    have hCong' : Derivable (allGateClauses n G8 ∪
        ((⋃ i ∈ Finset.range (d + 1), BitEqCNF (xRbits d 0 i) (yRbits d 0 i)) ∪
         (⋃ i ∈ Finset.range (d + 1), BitEqCNF (xBbits d 0 i) (yBbits d 0 i))))
        (n + G8.length) 30 ((d + 1) * K_cong)
        (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Yx i) (Yy i)) :=
      derivable_mono hCong (by intro C hC; rcases hC with (h | h) | h; exact Or.inl h; exact Or.inr (Or.inl h); exact Or.inr (Or.inr h))
        le_rfl le_rfl le_rfl Set.Subset.rfl
    have derYxYy := derivable_trans_only derRB8 hCong'
    have derRecX8 : Derivable (allGateClauses n G8) (n + G8.length) 30
        (4 * K_slice * 2 ^ d - (d + 3) * K_slice)
        (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 0 i) (Yx i)) :=
      derivable_mono derRecX (allGateClauses_mono p58) (by have := p58.length_le; omega) le_rfl le_rfl Set.Subset.rfl
    have derRecY8 : Derivable (allGateClauses n G8) (n + G8.length) 30
        (4 * K_slice * 2 ^ d - (d + 3) * K_slice)
        (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Ybits (d + 1) 0 i) (Yy i)) :=
      derivable_mono derRecY (allGateClauses_mono p68) (by have := p68.length_le; omega) le_rfl le_rfl Set.Subset.rfl
    have derAll3 := derivable_union (derivable_union derRecX8 derYxYy) derRecY8
    let S3 : Set (Clause ℕ) :=
      ((⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 0 i) (Yx i)) ∪
       (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Yx i) (Yy i))) ∪
      (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Ybits (d + 1) 0 i) (Yy i))
    have derTrans : Derivable (allGateClauses n G8 ∪ S3) (n + G8.length) 30 ((d + 2) * (3 * 2 ^ 6))
        (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 0 i) (Ybits (d + 1) 0 i)) := by
      have hbi : Derivable (allGateClauses n G8 ∪ S3) (n + G8.length) 30
          (∑ _ ∈ Finset.range (d + 2), (3 * 2 ^ 6))
          (⋃ i ∈ Finset.range (d + 2), BitEqCNF (Xbits (d + 1) 0 i) (Ybits (d + 1) 0 i)) :=
        derivable_biUnion (Finset.range (d + 2)) (fun _ => 3 * 2 ^ 6)
          (fun i => BitEqCNF (Xbits (d + 1) 0 i) (Ybits (d + 1) 0 i)) (by
            intro i hi
            rw [Finset.mem_range] at hi
            have h1 : Xbits (d + 1) 0 i < n + G8.length := by
              have := (hlt i (by omega)).1; have := p08.length_le; omega
            have h2 : Yx i < n + G8.length := by
              have := (hltYx i (by omega)).1; have := p58.length_le; omega
            have h3 : Yy i < n + G8.length := by
              have := (hltYy i (by omega)).1; have := p68.length_le; omega
            have h4 : Ybits (d + 1) 0 i < n + G8.length := by
              have := (hlt i (by omega)).2; have := p08.length_le; omega
            have ht := bitEq_trans3 h1 h2 h3 h4
            have hsym : BitEqCNF (Yy i) (Ybits (d + 1) 0 i) = BitEqCNF (Ybits (d + 1) 0 i) (Yy i) := by
              ext C; simp only [BitEqCNF, fullCNF, Set.mem_ofPred_eq]
              constructor <;> rintro ⟨α, hα, rfl⟩ <;> refine ⟨α, fun h => hα h.symm, ?_⟩ <;>
                simp only [forbidClause, Finset.pair_comm]
            refine derivable_mono ht ?_ le_rfl le_rfl le_rfl Set.Subset.rfl
            intro C hC
            rcases hC with (h | h) | h
            · exact Or.inr (Or.inl (Or.inl (Set.mem_biUnion (Finset.mem_range.mpr hi) h)))
            · exact Or.inr (Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr hi) h)))
            · rw [hsym] at h
              exact Or.inr (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr hi) h)))
      refine derivable_mono hbi Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
      simp [Finset.sum_const]
    have derFinal := derivable_trans_only derAll3 derTrans
    have hGbound : G8.length ≤ G.length + 72 * (d + 1) * 2 ^ (d + 1) := by
      have h1 : G1.length ≤ G.length + 18 * 2 ^ d := by omega
      have h2 : G2.length ≤ G1.length + 18 * 2 ^ d := by omega
      have h3 : G3.length ≤ G2.length + 18 * 2 ^ d := by omega
      have h4 : G4.length ≤ G3.length + 18 * 2 ^ d := by omega
      have h5 : G5.length ≤ G4.length + 36 * 2 ^ d := by omega
      have h6 : G6.length ≤ G5.length + 36 * 2 ^ d := by omega
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      have halg : 72 * (d + 1) * (2 * 2 ^ d) = 144 * 2 ^ d + 72 * d * 2 ^ d + 72 * d * 2 ^ d := by ring
      rw [hpow, halg]; omega
    have hPbound : (4 * K_slice * 2 ^ d - (d + 3) * K_slice) +
        (K_eq * d * 2 ^ d + K_eq * d * 2 ^ d + (d + 1) * K_cong) +
        (4 * K_slice * 2 ^ d - (d + 3) * K_slice) +
        (d + 2) * (3 * 2 ^ 6) ≤ K_eq * (d + 1) * 2 ^ (d + 1) := by
      have h2d : d + 1 ≤ 2 ^ d := by
        clear * -
        induction d with
        | zero => simp
        | succ k ih => rw [Nat.pow_succ]; omega
      have h2d2 : d + 2 ≤ 2 * 2 ^ d := by omega
      have hcong_le : (d + 1) * K_cong ≤ K_cong * 2 ^ d := by
        calc (d + 1) * K_cong ≤ 2 ^ d * K_cong := Nat.mul_le_mul_right _ h2d
          _ = K_cong * 2 ^ d := by ring
      have htrans_le : (d + 2) * (3 * 2 ^ 6) ≤ (6 * 2 ^ 6) * 2 ^ d := by
        calc (d + 2) * (3 * 2 ^ 6) ≤ (2 * 2 ^ d) * (3 * 2 ^ 6) := Nat.mul_le_mul_right _ h2d2
          _ = (6 * 2 ^ 6) * 2 ^ d := by ring
      have hsub1 : 4 * K_slice * 2 ^ d - (d + 3) * K_slice ≤ 4 * K_slice * 2 ^ d := Nat.sub_le _ _
      have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ]; omega
      have hkeq : K_eq * (d + 1) * (2 * 2 ^ d) =
          K_eq * d * 2 ^ d + K_eq * d * 2 ^ d + 2 * K_eq * 2 ^ d := by ring
      have hkeq2 : (8 * K_slice + K_cong + 6 * 2 ^ 6) * 2 ^ d ≤ 2 * K_eq * 2 ^ d := by
        dsimp only [K_eq]
        have : (8 * K_slice + K_cong + 6 * 2 ^ 6) ≤ 2 * (8 * K_slice + K_cong + 6 * 2 ^ 6) := by omega
        exact Nat.mul_le_mul_right _ this
      rw [hpow, hkeq]
      have hdist : 4 * K_slice * 2 ^ d + 4 * K_slice * 2 ^ d + K_cong * 2 ^ d + (6 * 2 ^ 6) * 2 ^ d =
          (8 * K_slice + K_cong + 6 * 2 ^ 6) * 2 ^ d := by ring
      omega
    exact ⟨G8, p08, hGbound, v8, derivable_mono derFinal Set.Subset.rfl le_rfl le_rfl hPbound Set.Subset.rfl⟩

end CounterAndPerm

section QuotaAndContradiction

private def constCNF (z0 o1 : ℕ) : Set (Clause ℕ) :=
  fullCNF {z0} (fun x => x z0 = false) ∪ fullCNF {o1} (fun x => x o1 = true)

private def unitTrueCNF (u : ℕ) : Set (Clause ℕ) :=
  fullCNF {u} (fun x => x u = true)

private lemma unitTrue_dependsOn (u : ℕ) : DependsOn {u} (fun x => x u = true) :=
  fun x y hxy => by simp only [hxy u (Finset.mem_singleton_self _)]

private def constCarry (K L k : ℕ) : Bool :=
  decide (2 ^ k ≤ K % 2 ^ k + L % 2 ^ k)

private lemma add_mod_two_pow (K L k : ℕ) :
    K % 2 ^ k + L % 2 ^ k = (K + L) % 2 ^ k + (constCarry K L k).toNat * 2 ^ k := by
  have hK : K % 2 ^ k < 2 ^ k := Nat.mod_lt K (Nat.two_pow_pos k)
  have hL : L % 2 ^ k < 2 ^ k := Nat.mod_lt L (Nat.two_pow_pos k)
  have hsum : (K + L) % 2 ^ k = (K % 2 ^ k + L % 2 ^ k) % 2 ^ k := Nat.add_mod K L (2 ^ k)
  rw [hsum]
  dsimp only [constCarry]
  by_cases h : 2 ^ k ≤ K % 2 ^ k + L % 2 ^ k
  · simp only [h, decide_true, Bool.toNat_true, one_mul]
    have hlt : K % 2 ^ k + L % 2 ^ k - 2 ^ k < 2 ^ k := by omega
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt hlt]
    omega
  · simp only [h, decide_false, Bool.toNat_false, zero_mul, add_zero]
    exact (Nat.mod_eq_of_lt (by omega)).symm

private lemma constCarry_step (K L k : ℕ) :
    (K.testBit k).toNat + (L.testBit k).toNat + (constCarry K L k).toNat =
      ((K + L).testBit k).toNat + 2 * (constCarry K L (k + 1)).toNat := by
  have h0 := add_mod_two_pow K L k
  have h1 := add_mod_two_pow K L (k + 1)
  rw [mod_two_pow_succ K k, mod_two_pow_succ L k, mod_two_pow_succ (K + L) k] at h1
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [hpow] at h1
  have hmul : ((K.testBit k).toNat + (L.testBit k).toNat + (constCarry K L k).toNat) * 2 ^ k =
      (((K + L).testBit k).toNat + 2 * (constCarry K L (k + 1)).toNat) * 2 ^ k := by
    linarith
  exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos k) hmul

private lemma constCarry_top {K L w : ℕ} (hK : K < 2 ^ w) (hL : L < 2 ^ w) (hKL : K + L ≤ 2 ^ w) :
    constCarry K L w = (K + L).testBit w := by
  dsimp only [constCarry]
  rw [Nat.mod_eq_of_lt hK, Nat.mod_eq_of_lt hL, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : 2 ^ w ≤ K + L
  · have heq : K + L = 2 ^ w := by omega
    rw [heq, Nat.div_self (Nat.two_pow_pos w)]
    simp
  · have hdiv : (K + L) / 2 ^ w = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv]
    simp [h]

private def boolSign (b : Bool) : ℤ := if b then 0 else -1

private lemma cmpBit_sign (isGe a p s : Bool) :
    let diff : ℤ := if isGe then (a.toNat : ℤ) - (p.toNat : ℤ) else (p.toNat : ℤ) - (a.toNat : ℤ)
    2 * boolSign (cmpBit isGe p a s) ≤ diff + boolSign s ∧
    diff + boolSign s ≤ 2 * boolSign (cmpBit isGe p a s) + 1 := by
  cases isGe <;> cases a <;> cases p <;> cases s <;> decide

private def cmpInvPred (isGe dcar : Bool) (c su sw sv : ℕ) (x : ℕ → Bool) : Prop :=
  let P : ℤ := boolSign (x su) + boolSign (x sw)
  let Q : ℤ := if isGe
    then boolSign (x sv) + ((x c).toNat : ℤ) - (dcar.toNat : ℤ)
    else boolSign (x sv) + (dcar.toNat : ℤ) - ((x c).toNat : ℤ)
  P ≤ Q ∧ Q ≤ P + 1

private def cmpInvCNF (isGe dcar : Bool) (c su sw sv : ℕ) : Set (Clause ℕ) :=
  fullCNF {c, su, sw, sv} (cmpInvPred isGe dcar c su sw sv)

private lemma cmpInv_dependsOn (isGe dcar : Bool) (c su sw sv : ℕ) :
    DependsOn {c, su, sw, sv} (cmpInvPred isGe dcar c su sw sv) := by
  intro x y hxy
  simp only [cmpInvPred, hxy c (by simp), hxy su (by simp), hxy sw (by simp), hxy sv (by simp)]

private lemma cmpInv_step_arith {isGe a b cin s cout p q dcar r dcar' su sw sv : Bool}
    (hadd : a.toNat + b.toNat + cin.toNat = s.toNat + 2 * cout.toNat)
    (hcadd : p.toNat + q.toNat + dcar.toNat = r.toNat + 2 * dcar'.toNat)
    (hinv :
      let P : ℤ := boolSign su + boolSign sw
      let Q : ℤ := if isGe then boolSign sv + (cin.toNat : ℤ) - (dcar.toNat : ℤ)
                   else boolSign sv + (dcar.toNat : ℤ) - (cin.toNat : ℤ)
      P ≤ Q ∧ Q ≤ P + 1) :
    let P' : ℤ := boolSign (cmpBit isGe p a su) + boolSign (cmpBit isGe q b sw)
    let Q' : ℤ := if isGe then boolSign (cmpBit isGe r s sv) + (cout.toNat : ℤ) - (dcar'.toNat : ℤ)
                  else boolSign (cmpBit isGe r s sv) + (dcar'.toNat : ℤ) - (cout.toNat : ℤ)
    P' ≤ Q' ∧ Q' ≤ P' + 1 := by
  have h1 := cmpBit_sign isGe a p su
  have h2 := cmpBit_sign isGe b q sw
  have h3 := cmpBit_sign isGe s r sv
  cases isGe
  · simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2 h3 hinv ⊢
    omega
  · simp only [↓reduceIte] at h1 h2 h3 hinv ⊢
    omega

private lemma cmpInv_top_arith {isGe dcar cout sv : Bool}
    (hinv :
      let Q : ℤ := if isGe then boolSign sv + (cout.toNat : ℤ) - (dcar.toNat : ℤ)
                   else boolSign sv + (dcar.toNat : ℤ) - (cout.toNat : ℤ)
      0 ≤ Q ∧ Q ≤ 1) :
    cmpBit isGe dcar cout sv = true := by
  cases isGe <;> cases dcar <;> cases cout <;> cases sv <;>
    simp only [Bool.false_eq_true, ↓reduceIte, boolSign, cmpBit,
      Bool.toNat_true, Bool.toNat_false, Bool.true_and, Bool.false_and,
      Bool.true_or, Bool.false_or, Bool.not_true, Bool.not_false] at hinv ⊢ <;>
    omega

private def K_qstep : ℕ := 2 ^ 21

private lemma derive_cmpInv_step {n : ℕ} {G : List (ℕ × ℕ)} {isGe p q dcar r dcar' : Bool}
    {a b cin s cout su sw sv su' sw' sv' : ℕ}
    (hcadd : p.toNat + q.toNat + dcar.toNat = r.toNat + 2 * dcar'.toNat)
    (hFA : HasFA n G a b cin s cout)
    (hL : HasCmpStep n G isGe p a su su')
    (hR : HasCmpStep n G isGe q b sw sw')
    (hV : HasCmpStep n G isGe r s sv sv') :
    Derivable (allGateClauses n G ∪ cmpInvCNF isGe dcar cin su sw sv)
      (n + G.length) 30 K_qstep
      (cmpInvCNF isGe dcar' cout su' sw' sv') := by
  let F0 := allGateClauses n G ∪ cmpInvCNF isGe dcar cin su sw sv
  have hsub0 : allGateClauses n G ⊆ F0 := Set.subset_union_left
  have dFA : Derivable F0 (n + G.length) 30 (3 * 2 ^ 17) (faCNF a b cin s cout) :=
    derivable_mono (derive_FA hFA) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dL : Derivable F0 (n + G.length) 30 (3 * 2 ^ 8) (cmpStepCNF isGe p a su su') :=
    derivable_mono (derive_cmpStep hL) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dR : Derivable F0 (n + G.length) 30 (3 * 2 ^ 8) (cmpStepCNF isGe q b sw sw') :=
    derivable_mono (derive_cmpStep hR) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dV : Derivable F0 (n + G.length) 30 (3 * 2 ^ 8) (cmpStepCNF isGe r s sv sv') :=
    derivable_mono (derive_cmpStep hV) hsub0 le_rfl (by omega) le_rfl Set.Subset.rfl
  have dAll := derivable_union (derivable_union dFA dL) (derivable_union dR dV)
  let S1 : Finset ℕ := {a, b, cin, s, cout}
  let S2 : Finset ℕ := {a, su, su'}
  let S3 : Finset ℕ := {b, sw, sw'}
  let S4 : Finset ℕ := {s, sv, sv'}
  let S : Finset ℕ := (S1 ∪ S2) ∪ (S3 ∪ S4)
  have hS1 : S1 ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hS2 : S2 ⊆ S := fun v hv => Finset.mem_union_left _ (Finset.mem_union_right _ hv)
  have hS3 : S3 ⊆ S := fun v hv => Finset.mem_union_right _ (Finset.mem_union_left _ hv)
  have hS4 : S4 ⊆ S := fun v hv => Finset.mem_union_right _ (Finset.mem_union_right _ hv)
  have hScard : S.card ≤ 14 := by
    have h1 : S1.card ≤ 5 := card5_le a b cin s cout
    have h2 : S2.card ≤ 3 := by
      dsimp only [S2]; have := Finset.card_insert_le a {su, su'}; have := Finset.card_insert_le su {su'}
      simp only [Finset.card_singleton] at *; omega
    have h3 : S3.card ≤ 3 := by
      dsimp only [S3]; have := Finset.card_insert_le b {sw, sw'}; have := Finset.card_insert_le sw {sw'}
      simp only [Finset.card_singleton] at *; omega
    have h4 : S4.card ≤ 3 := by
      dsimp only [S4]; have := Finset.card_insert_le s {sv, sv'}; have := Finset.card_insert_le sv {sv'}
      simp only [Finset.card_singleton] at *; omega
    dsimp only [S]
    have := Finset.card_union_le (S1 ∪ S2) (S3 ∪ S4)
    have := Finset.card_union_le S1 S2
    have := Finset.card_union_le S3 S4
    omega
  have hSB : ∀ v ∈ S, v < n + G.length := by
    intro v hv
    rcases Finset.mem_union.mp hv with h12 | h34
    · rcases Finset.mem_union.mp h12 with h | h
      · simp only [S1, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl | rfl | rfl
        · exact hFA.1
        · exact hFA.2.1
        · exact hFA.2.2.1
        · exact hFA.2.2.2.1
        · exact hFA.2.2.2.2.1
      · simp only [S2, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl
        · exact hL.1
        · exact hL.2.1
        · exact hL.2.2.1
    · rcases Finset.mem_union.mp h34 with h | h
      · simp only [S3, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl
        · exact hR.1
        · exact hR.2.1
        · exact hR.2.2.1
      · simp only [S4, Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with rfl | rfl | rfl
        · exact hV.1
        · exact hV.2.1
        · exact hV.2.2.1
  let H : Set (Clause ℕ) :=
    ((faCNF a b cin s cout ∪ cmpStepCNF isGe p a su su') ∪
     (cmpStepCNF isGe q b sw sw' ∪ cmpStepCNF isGe r s sv sv')) ∪
    cmpInvCNF isGe dcar cin su sw sv
  have hHsub : H ⊆ F0 ∪ ((faCNF a b cin s cout ∪ cmpStepCNF isGe p a su su') ∪
      (cmpStepCNF isGe q b sw sw' ∪ cmpStepCNF isGe r s sv sv')) := by
    intro C hC
    rcases hC with h | h
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hHS : ∀ C ∈ H, ∀ l ∈ C, l.1 ∈ S := by
    intro C hC l hl
    rcases hC with ((h | h) | (h | h)) | h
    · exact fullCNF_vars_subset hS1 C h l hl
    · exact fullCNF_vars_subset hS2 C h l hl
    · exact fullCNF_vars_subset hS3 C h l hl
    · exact fullCNF_vars_subset hS4 C h l hl
    · exact fullCNF_vars_subset (fun v hv => by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact hS1 (by simp [S1])
        · exact hS2 (by simp [S2])
        · exact hS3 (by simp [S3])
        · exact hS4 (by simp [S4])) C h l hl
  have hOS : ({cout, su', sw', sv'} : Finset ℕ) ⊆ S := by
    intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hS1 (by simp [S1])
    · exact hS2 (by simp [S2])
    · exact hS3 (by simp [S3])
    · exact hS4 (by simp [S4])
  have hOc : ({cout, su', sw', sv'} : Finset ℕ).card ≤ 4 := by
    have := Finset.card_insert_le cout {su', sw', sv'}
    have := Finset.card_insert_le su' {sw', sv'}
    have := Finset.card_insert_le sw' {sv'}
    simp only [Finset.card_singleton] at *; omega
  have hsem : ∀ x : ℕ → Bool, (∀ C ∈ H, ClauseSat x C) → cmpInvPred isGe dcar' cout su' sw' sv' x := by
    intro x hx
    have eFA : faPred a b cin s cout x := (fullCNF_sat_iff (faPred_dependsOn a b cin s cout) x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inl hC))))
    have eL : cmpStepPred isGe p a su su' x := (fullCNF_sat_iff (cmpStepPred_dependsOn isGe p a su su') x).mp
      (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
    have eR : cmpStepPred isGe q b sw sw' x := (fullCNF_sat_iff (cmpStepPred_dependsOn isGe q b sw sw') x).mp
      (fun C hC => hx C (Or.inl (Or.inr (Or.inl hC))))
    have eV : cmpStepPred isGe r s sv sv' x := (fullCNF_sat_iff (cmpStepPred_dependsOn isGe r s sv sv') x).mp
      (fun C hC => hx C (Or.inl (Or.inr (Or.inr hC))))
    have eI : cmpInvPred isGe dcar cin su sw sv x := (fullCNF_sat_iff (cmpInv_dependsOn isGe dcar cin su sw sv) x).mp
      (fun C hC => hx C (Or.inr hC))
    dsimp only [cmpInvPred, cmpStepPred, faPred] at eFA eL eR eV eI ⊢
    rw [eL, eR, eV]
    exact cmpInv_step_arith eFA hcadd eI
  have dOut := derive_fullCNF (O := {cout, su', sw', sv'}) hHsub hSB hHS hOS
    (cmpInv_dependsOn isGe dcar' cout su' sw' sv') hsem
  have dOut' := derivable_mono dOut Set.Subset.rfl le_rfl (by omega : S.card ≤ 30)
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 18))) Set.Subset.rfl
  have htr := derivable_trans_only dAll dOut'
  refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
  dsimp only [K_qstep]; norm_num

private lemma derive_quota_merge {n : ℕ} {G : List (ℕ × ℕ)} {z0 o1 : ℕ} {isGe : Bool}
    {w K L : ℕ} {A B S car stL stR stV : ℕ → ℕ}
    (hz : z0 < n + G.length) (ho : o1 < n + G.length)
    (hK : K < 2 ^ w) (hL : L < 2 ^ w) (hKL : K + L ≤ 2 ^ w)
    (hr : HasRipple n G z0 w A B S car)
    (hcL : HasCmp n G o1 isGe w K A stL)
    (hcR : HasCmp n G o1 isGe w L B stR)
    (hcV : HasCmp n G o1 isGe (w + 1) (K + L) S stV)
    (hstL : stL w < n + G.length) (hstR : stR w < n + G.length) :
    Derivable (allGateClauses n G ∪ constCNF z0 o1 ∪ unitTrueCNF (stL w) ∪ unitTrueCNF (stR w))
      (n + G.length) 30 ((w + 2) * K_qstep) (unitTrueCNF (stV (w + 1))) := by
  let F0 := allGateClauses n G ∪ constCNF z0 o1 ∪ unitTrueCNF (stL w) ∪ unitTrueCNF (stR w)
  let Inv : ℕ → Set (Clause ℕ) := fun k => cmpInvCNF isGe (constCarry K L k) (car k) (stL k) (stR k) (stV k)
  have hInv0 : Derivable F0 (n + G.length) 30 K_qstep (Inv 0) := by
    let S0 : Finset ℕ := {z0, o1}
    have hS0c : S0.card ≤ 2 := by
      dsimp only [S0]; have := Finset.card_insert_le z0 {o1}; simp only [Finset.card_singleton] at *; omega
    have hS0B : ∀ v ∈ S0, v < n + G.length := by
      intro v hv; simp only [S0, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    have hH0 : constCNF z0 o1 ⊆ F0 := fun C hC => Or.inl (Or.inl (Or.inr hC))
    have hH0S : ∀ C ∈ constCNF z0 o1, ∀ l ∈ C, l.1 ∈ S0 := by
      intro C hC l hl
      rcases hC with h | h
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [S0, hv]) C h l hl
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [S0, hv]) C h l hl
    have hO0S : ({car 0, stL 0, stR 0, stV 0} : Finset ℕ) ⊆ S0 := by
      rw [hr.1, hcL.1, hcR.1, hcV.1]
      intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl <;> simp [S0]
    have hO0c : ({car 0, stL 0, stR 0, stV 0} : Finset ℕ).card ≤ 4 := by
      have := Finset.card_insert_le (car 0) {stL 0, stR 0, stV 0}
      have := Finset.card_insert_le (stL 0) {stR 0, stV 0}
      have := Finset.card_insert_le (stR 0) {stV 0}
      simp only [Finset.card_singleton] at *; omega
    have hsem0 : ∀ x : ℕ → Bool, (∀ C ∈ constCNF z0 o1, ClauseSat x C) →
        cmpInvPred isGe (constCarry K L 0) (car 0) (stL 0) (stR 0) (stV 0) x := by
      intro x hx
      have ez : x z0 = false := (fullCNF_sat_iff (fun a b hab => by rw [hab z0 (by simp)]) x).mp
        (fun C hC => hx C (Or.inl hC))
      have eo : x o1 = true := (fullCNF_sat_iff (fun a b hab => by rw [hab o1 (by simp)]) x).mp
        (fun C hC => hx C (Or.inr hC))
      have hc0 : constCarry K L 0 = false := by simp [constCarry, Nat.mod_one]
      simp only [cmpInvPred, hr.1, hcL.1, hcR.1, hcV.1, ez, eo, hc0, boolSign]
      cases isGe <;> simp
    have hd0 := derive_fullCNF (O := {car 0, stL 0, stR 0, stV 0}) hH0 hS0B hH0S hO0S
      (cmpInv_dependsOn isGe (constCarry K L 0) (car 0) (stL 0) (stR 0) (stV 0)) hsem0
    refine derivable_mono hd0 Set.Subset.rfl le_rfl (by omega) ?_ Set.Subset.rfl
    have h1 : 3 * 2 ^ (({car 0, stL 0, stR 0, stV 0} : Finset ℕ).card + S0.card) ≤ 3 * 2 ^ 6 :=
      Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega))
    dsimp only [K_qstep]; omega
  have hstep : ∀ k < w, Derivable (F0 ∪ Inv k) (n + G.length) 30 K_qstep (Inv (k + 1) ∪ ∅) := by
    intro k hk
    have hs := derive_cmpInv_step (constCarry_step K L k) (hr.2.1 k hk)
      (hcL.2 k hk) (hcR.2 k hk) (hcV.2 k (Nat.lt_succ_of_lt hk))
    have hFsub : allGateClauses n G ∪ Inv k ⊆ F0 ∪ Inv k :=
      Set.union_subset_union_left _ (fun C hC => Or.inl (Or.inl (Or.inl hC)))
    exact derivable_mono hs hFsub le_rfl le_rfl le_rfl (by simp [Inv])
  have hch := derivable_range_chain Inv (fun _ => ∅) w hInv0 hstep
  have hch' : Derivable F0 (n + G.length) 30 (K_qstep + w * K_qstep) (Inv w) :=
    derivable_mono hch Set.Subset.rfl le_rfl le_rfl le_rfl Set.subset_union_left
  have hTop : Derivable (F0 ∪ Inv w) (n + G.length) 30 K_qstep (unitTrueCNF (stV (w + 1))) := by
    have hstepV : HasCmpStep n G isGe ((K + L).testBit w) (car w) (stV w) (stV (w + 1)) := by
      have h := hcV.2 w (Nat.lt_succ_self w)
      rwa [hr.2.2] at h
    have dStep : Derivable (F0 ∪ Inv w) (n + G.length) 30 (3 * 2 ^ 8)
        (cmpStepCNF isGe ((K + L).testBit w) (car w) (stV w) (stV (w + 1))) :=
      derivable_mono (derive_cmpStep hstepV)
        (fun C hC => Or.inl (Or.inl (Or.inl (Or.inl hC)))) le_rfl (by omega) le_rfl Set.Subset.rfl
    let St : Finset ℕ := {car w, stL w, stR w, stV w, stV (w + 1)}
    have hStc : St.card ≤ 5 := card5_le _ _ _ _ _
    have hStB : ∀ v ∈ St, v < n + G.length := by
      intro v hv; simp only [St, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact hstepV.1
      · exact hstL
      · exact hstR
      · exact hstepV.2.1
      · exact hstepV.2.2.1
    let Ht : Set (Clause ℕ) :=
      cmpStepCNF isGe ((K + L).testBit w) (car w) (stV w) (stV (w + 1)) ∪
      Inv w ∪ unitTrueCNF (stL w) ∪ unitTrueCNF (stR w)
    have hHtsub : Ht ⊆ (F0 ∪ Inv w) ∪ cmpStepCNF isGe ((K + L).testBit w) (car w) (stV w) (stV (w + 1)) := by
      intro C hC
      rcases hC with ((h | h) | h) | h
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inl (Or.inl (Or.inr h))
    have hHtS : ∀ C ∈ Ht, ∀ l ∈ C, l.1 ∈ St := by
      intro C hC l hl
      rcases hC with ((h | h) | h) | h
      · exact fullCNF_vars_subset (fun v hv => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl <;> simp [St]) C h l hl
      · exact fullCNF_vars_subset (fun v hv => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl | rfl | rfl <;> simp [St]) C h l hl
      · exact fullCNF_vars_subset (fun v hv => by
          simp only [Finset.mem_singleton] at hv; simp [St, hv]) C h l hl
      · exact fullCNF_vars_subset (fun v hv => by
          simp only [Finset.mem_singleton] at hv; simp [St, hv]) C h l hl
    have hsemT : ∀ x : ℕ → Bool, (∀ C ∈ Ht, ClauseSat x C) → x (stV (w + 1)) = true := by
      intro x hx
      have eSt : x (stV (w + 1)) = cmpBit isGe ((K + L).testBit w) (x (car w)) (x (stV w)) :=
        (fullCNF_sat_iff (cmpStepPred_dependsOn isGe ((K + L).testBit w) (car w) (stV w) (stV (w + 1))) x).mp
          (fun C hC => hx C (Or.inl (Or.inl (Or.inl hC))))
      have eI : cmpInvPred isGe (constCarry K L w) (car w) (stL w) (stR w) (stV w) x :=
        (fullCNF_sat_iff (cmpInv_dependsOn isGe (constCarry K L w) (car w) (stL w) (stR w) (stV w)) x).mp
          (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
      have eL : x (stL w) = true := (fullCNF_sat_iff (unitTrue_dependsOn _) x).mp
        (fun C hC => hx C (Or.inl (Or.inr hC)))
      have eR : x (stR w) = true := (fullCNF_sat_iff (unitTrue_dependsOn _) x).mp
        (fun C hC => hx C (Or.inr hC))
      rw [eSt, ← constCarry_top hK hL hKL]
      dsimp only [cmpInvPred] at eI
      rw [eL, eR] at eI
      simp only [boolSign, ↓reduceIte, add_zero, zero_add] at eI
      exact cmpInv_top_arith eI
    have dOut := derive_fullCNF (O := {stV (w + 1)}) hHtsub hStB hHtS
      (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [St, hv])
      (unitTrue_dependsOn _) hsemT
    have dOut' := derivable_mono dOut Set.Subset.rfl le_rfl (by omega : St.card ≤ 30)
      (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by simp; omega : _ ≤ 6))) Set.Subset.rfl
    have htr := derivable_trans_only dStep dOut'
    refine derivable_mono htr Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
    dsimp only [K_qstep]; norm_num
  have hfin := derivable_trans_only hch' hTop
  exact derivable_mono hfin Set.Subset.rfl le_rfl le_rfl (by ring_nf; exact le_rfl) Set.Subset.rfl

private lemma build_quota_tree {n : ℕ} (baseF : Set (Clause ℕ)) (z0 o1 k_b W_leaf L_leaf : ℕ)
    (isGe : Bool) (hW30 : 30 ≤ W_leaf) (r : ℕ) :
    ∀ {G : List (ℕ × ℕ)} {leaves : ℕ → ℕ} {bits car : ℕ → ℕ → ℕ → ℕ} (q : ℕ → ℕ),
      ValidCirc n G → z0 < n + G.length → o1 < n + G.length →
      HasCounterTree n G z0 (r + k_b) leaves bits car →
      (∀ t ≤ r + k_b, ∀ pos < 2 ^ (r + k_b - t), ∀ i ≤ t, bits t pos i < n + G.length) →
      (∀ blk < 2 ^ r, q blk ≤ 2 ^ k_b) →
      (∀ blk < 2 ^ r, ∀ G1 : List (ℕ × ℕ), G <+: G1 → ∀ st : ℕ → ℕ,
        HasCmp n G1 o1 isGe (k_b + 1) (q blk) (fun i => bits k_b blk i) st →
        Derivable (baseF ∪ allGateClauses n G1 ∪ constCNF z0 o1) (n + G1.length) W_leaf L_leaf
          (unitTrueCNF (st (k_b + 1)))) →
      ∃ (G' : List (ℕ × ℕ)) (stRoot : ℕ → ℕ),
        G <+: G' ∧ G'.length + 3 * (r + k_b + 3) ≤ G.length + 6 * (k_b + 3) * 2 ^ r ∧
        ValidCirc n G' ∧
        HasCmp n G' o1 isGe (r + k_b + 1) (∑ blk ∈ Finset.range (2 ^ r), q blk)
          (fun i => bits (r + k_b) 0 i) stRoot ∧
        (∀ i ≤ r + k_b + 1, stRoot i < n + G'.length) ∧
        Derivable (baseF ∪ allGateClauses n G' ∪ constCNF z0 o1) (n + G'.length) W_leaf
          ((L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r - (r + k_b + 4) * K_qstep)
          (unitTrueCNF (stRoot (r + k_b + 1))) := by
  induction r with
  | zero =>
    intro G leaves bits car q hV hz ho ct hbl hq hLeaf
    have hA : ∀ i < k_b + 1, bits k_b 0 i < n + G.length :=
      fun i hi => hbl k_b (by omega) 0 (by simp) i (by omega)
    obtain ⟨G', st, hp, hl, hV', hcmp, hstlt⟩ := exists_addCmp isGe hV ho (k_b + 1) (q 0)
      (fun i => bits k_b 0 i) hA
    have hder := hLeaf 0 (by simp) G' hp st hcmp
    have hsum : ∑ blk ∈ Finset.range (2 ^ 0), q blk = q 0 := by simp
    refine ⟨G', st, hp, by simp only [pow_zero, mul_one, zero_add]; omega, hV', ?_, ?_, ?_⟩
    · simp only [zero_add, hsum]; exact hcmp
    · intro i hi; exact hstlt i (by omega)
    · simp only [zero_add, pow_zero, mul_one]
      refine derivable_mono hder Set.Subset.rfl le_rfl le_rfl ?_ Set.Subset.rfl
      have hsub : (k_b + 4) * K_qstep ≤ 2 * (k_b + 4) * K_qstep := by
        have h1 : 2 * (k_b + 4) * K_qstep = (k_b + 4) * K_qstep + (k_b + 4) * K_qstep := by ring
        omega
      omega
  | succ r ih =>
    intro G leaves bits car q hV hz ho ct hbl hq hLeaf
    have hsum_eq : r + 1 + k_b = (r + k_b) + 1 := by omega
    have ct' : HasCounterTree n G z0 ((r + k_b) + 1) leaves bits car := hsum_eq ▸ ct
    have hblL : ∀ t ≤ r + k_b, ∀ pos < 2 ^ (r + k_b - t), ∀ i ≤ t, bits t pos i < n + G.length :=
      fun t ht pos hpos i hi => hbl t (by omega) pos
        (lt_of_lt_of_le hpos (Nat.pow_le_pow_right (by omega) (by omega))) i hi
    have hqL : ∀ blk < 2 ^ r, q blk ≤ 2 ^ k_b :=
      fun blk hb => hq blk (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (Nat.le_succ r)))
    have hLeafL : ∀ blk < 2 ^ r, ∀ G1 : List (ℕ × ℕ), G <+: G1 → ∀ st : ℕ → ℕ,
        HasCmp n G1 o1 isGe (k_b + 1) (q blk) (fun i => bits k_b blk i) st →
        Derivable (baseF ∪ allGateClauses n G1 ∪ constCNF z0 o1) (n + G1.length) W_leaf L_leaf
          (unitTrueCNF (st (k_b + 1))) :=
      fun blk hb => hLeaf blk (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) (Nat.le_succ r)))
    obtain ⟨G1, stL, p1, l1, v1, hcL, hstL, derL⟩ :=
      ih q hV hz ho (counterTree_left ct') hblL hqL hLeafL
    have hz1 : z0 < n + G1.length := by have := p1.length_le; omega
    have ho1 : o1 < n + G1.length := by have := p1.length_le; omega
    let qR : ℕ → ℕ := fun blk => q (2 ^ r + blk)
    have hblR : ∀ t ≤ r + k_b, ∀ pos < 2 ^ (r + k_b - t), ∀ i ≤ t,
        bits t (2 ^ (r + k_b - t) + pos) i < n + G1.length := by
      intro t ht pos hpos i hi
      have hexp : r + 1 + k_b - t = (r + k_b - t) + 1 := by omega
      have hlt : 2 ^ (r + k_b - t) + pos < 2 ^ (r + 1 + k_b - t) := by rw [hexp, Nat.pow_succ]; omega
      have := hbl t (by omega) (2 ^ (r + k_b - t) + pos) hlt i hi
      have := p1.length_le; omega
    have hqR : ∀ blk < 2 ^ r, qR blk ≤ 2 ^ k_b := by
      intro blk hb
      exact hq (2 ^ r + blk) (by rw [Nat.pow_succ]; omega)
    have hLeafR : ∀ blk < 2 ^ r, ∀ G2 : List (ℕ × ℕ), G1 <+: G2 → ∀ st : ℕ → ℕ,
        HasCmp n G2 o1 isGe (k_b + 1) (qR blk) (fun i => bits k_b (2 ^ (r + k_b - k_b) + blk) i) st →
        Derivable (baseF ∪ allGateClauses n G2 ∪ constCNF z0 o1) (n + G2.length) W_leaf L_leaf
          (unitTrueCNF (st (k_b + 1))) := by
      intro blk hb G2 p12 st hcmp
      have hsub : r + k_b - k_b = r := by omega
      rw [hsub] at hcmp
      exact hLeaf (2 ^ r + blk) (by rw [Nat.pow_succ]; omega) G2 (p1.trans p12) st hcmp
    obtain ⟨G2, stR, p2, l2, v2, hcR, hstR, derR⟩ :=
      ih qR v1 hz1 ho1 (hasCounterTree_mono p1 (counterTree_right ct')) hblR hqR hLeafR
    have hz2 : z0 < n + G2.length := by have := p2.length_le; omega
    have ho2 : o1 < n + G2.length := by have := p2.length_le; omega
    let KL := ∑ blk ∈ Finset.range (2 ^ r), q blk
    let KR := ∑ blk ∈ Finset.range (2 ^ r), qR blk
    have hsumAll : ∑ blk ∈ Finset.range (2 ^ (r + 1)), q blk = KL + KR := by
      have hexp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by rw [Nat.pow_succ]; omega
      rw [hexp, Finset.sum_range_add]
    have hAroot : ∀ i < r + 1 + k_b + 1, bits (r + 1 + k_b) 0 i < n + G2.length := by
      intro i hi
      have := hbl (r + 1 + k_b) le_rfl 0 (by simp) i (by omega)
      have := (p1.trans p2).length_le; omega
    obtain ⟨G3, stV, p3, l3, v3, hcV, hstV⟩ :=
      exists_addCmp isGe v2 ho2 (r + 1 + k_b + 1) (KL + KR) (fun i => bits (r + 1 + k_b) 0 i) hAroot
    have p03 : G <+: G3 := p1.trans (p2.trans p3)
    have p13 : G1 <+: G3 := p2.trans p3
    have hKLle : KL ≤ 2 ^ (r + k_b) := by
      calc KL ≤ ∑ _ ∈ Finset.range (2 ^ r), 2 ^ k_b :=
            Finset.sum_le_sum (fun blk hb => hqL blk (Finset.mem_range.mp hb))
        _ = 2 ^ r * 2 ^ k_b := by simp
        _ = 2 ^ (r + k_b) := (Nat.pow_add 2 r k_b).symm
    have hKRle : KR ≤ 2 ^ (r + k_b) := by
      calc KR ≤ ∑ _ ∈ Finset.range (2 ^ r), 2 ^ k_b :=
            Finset.sum_le_sum (fun blk hb => hqR blk (Finset.mem_range.mp hb))
        _ = 2 ^ r * 2 ^ k_b := by simp
        _ = 2 ^ (r + k_b) := (Nat.pow_add 2 r k_b).symm
    have hpow_pos : 0 < 2 ^ (r + k_b) := Nat.two_pow_pos _
    have hKLlt : KL < 2 ^ (r + k_b + 1) := by rw [Nat.pow_succ]; omega
    have hKRlt : KR < 2 ^ (r + k_b + 1) := by rw [Nat.pow_succ]; omega
    have hSumLe : KL + KR ≤ 2 ^ (r + k_b + 1) := by rw [Nat.pow_succ]; omega
    have hrRoot : HasRipple n G3 z0 (r + k_b + 1)
        (fun i => bits (r + k_b) 0 i) (fun i => bits (r + k_b) 1 i)
        (fun i => bits (r + 1 + k_b) 0 i) (fun i => car (r + 1 + k_b) 0 i) := by
      have h := hasRipple_mono p03 (ct'.2 (r + k_b) (Nat.lt_succ_self _) 0 (by simp))
      simpa [hsum_eq] using h
    have hcR3 : HasCmp n G3 o1 isGe (r + k_b + 1) KR (fun i => bits (r + k_b) 1 i) stR := by
      have h := hasCmp_mono p3 hcR
      simpa only [Nat.sub_self, Nat.pow_zero, Nat.add_zero] using h
    have hcV3 : HasCmp n G3 o1 isGe ((r + k_b + 1) + 1) (KL + KR) (fun i => bits (r + 1 + k_b) 0 i) stV := by
      have hlen : (r + k_b + 1) + 1 = r + 1 + k_b + 1 := by omega
      rwa [hlen]
    have hMerge := derive_quota_merge (by have := p3.length_le; omega) (by have := p3.length_le; omega)
      hKLlt hKRlt hSumLe hrRoot (hasCmp_mono p13 hcL) hcR3 hcV3
      (by have := hstL (r + k_b + 1) le_rfl; have := p13.length_le; omega)
      (by have := hstR (r + k_b + 1) le_rfl; have := p3.length_le; omega)
    let F3 := baseF ∪ allGateClauses n G3 ∪ constCNF z0 o1
    have derL3 : Derivable F3 (n + G3.length) W_leaf
        ((L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r - (r + k_b + 4) * K_qstep)
        (unitTrueCNF (stL (r + k_b + 1))) :=
      derivable_mono derL
        (fun C hC => by rcases hC with (h | h) | h; exact Or.inl (Or.inl h); exact Or.inl (Or.inr (allGateClauses_mono p13 h)); exact Or.inr h)
        (by have := p13.length_le; omega) le_rfl le_rfl Set.Subset.rfl
    have derR3 : Derivable F3 (n + G3.length) W_leaf
        ((L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r - (r + k_b + 4) * K_qstep)
        (unitTrueCNF (stR (r + k_b + 1))) :=
      derivable_mono derR
        (fun C hC => by rcases hC with (h | h) | h; exact Or.inl (Or.inl h); exact Or.inl (Or.inr (allGateClauses_mono p3 h)); exact Or.inr h)
        (by have := p3.length_le; omega) le_rfl le_rfl Set.Subset.rfl
    have derLR := derivable_union derL3 derR3
    have hMerge' : Derivable (F3 ∪ (unitTrueCNF (stL (r + k_b + 1)) ∪ unitTrueCNF (stR (r + k_b + 1))))
        (n + G3.length) W_leaf ((r + k_b + 1 + 2) * K_qstep) (unitTrueCNF (stV (r + 1 + k_b + 1))) := by
      have heq : (r + k_b + 1) + 1 = r + 1 + k_b + 1 := by omega
      rw [← heq]
      refine derivable_mono hMerge ?_ le_rfl hW30 le_rfl Set.Subset.rfl
      intro C hC
      rcases hC with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have derFinal := derivable_trans_only derLR hMerge'
    have hGbound : G3.length + 3 * (r + 1 + k_b + 3) ≤ G.length + 6 * (k_b + 3) * 2 ^ (r + 1) := by
      have halg : 6 * (k_b + 3) * 2 ^ (r + 1) = 6 * (k_b + 3) * 2 ^ r + 6 * (k_b + 3) * 2 ^ r := by
        rw [Nat.pow_succ]; ring
      omega
    have hPbound : ((L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r - (r + k_b + 4) * K_qstep) +
        ((L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r - (r + k_b + 4) * K_qstep) +
        (r + k_b + 1 + 2) * K_qstep ≤
        (L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ (r + 1) - (r + 1 + k_b + 4) * K_qstep := by
      have hge : (r + k_b + 4) * K_qstep ≤ (L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r := by
        have h2r : r + 1 ≤ 2 ^ r := by
          clear * -
          induction r with
          | zero => simp
          | succ m ihm => rw [Nat.pow_succ]; omega
        have h1 : r + k_b + 4 ≤ (k_b + 4) * 2 ^ r := by
          have : r + k_b + 4 ≤ (k_b + 4) * (r + 1) := by nlinarith
          exact le_trans this (Nat.mul_le_mul_left (k_b + 4) h2r)
        have h2 : (r + k_b + 4) * K_qstep ≤ ((k_b + 4) * 2 ^ r) * K_qstep :=
          Nat.mul_le_mul_right _ h1
        have h3 : ((k_b + 4) * 2 ^ r) * K_qstep = (k_b + 4) * K_qstep * 2 ^ r := by ring
        have h4 : (k_b + 4) * K_qstep ≤ L_leaf + 2 * (k_b + 4) * K_qstep := by
          have : (k_b + 4) * K_qstep ≤ 2 * ((k_b + 4) * K_qstep) := by omega
          have : 2 * ((k_b + 4) * K_qstep) = 2 * (k_b + 4) * K_qstep := by ring
          omega
        calc (r + k_b + 4) * K_qstep ≤ (k_b + 4) * K_qstep * 2 ^ r := by rw [← h3]; exact h2
          _ ≤ (L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r := Nat.mul_le_mul_right _ h4
      have hexp : (L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ (r + 1) =
          (L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r + (L_leaf + 2 * (k_b + 4) * K_qstep) * 2 ^ r := by
        rw [Nat.pow_succ]; ring
      have ha1 : (r + k_b + 4) * K_qstep + (r + k_b + 4) * K_qstep =
          (r + k_b + 1 + 2) * K_qstep + (r + 1 + k_b + 4) * K_qstep := by ring
      omega
    refine ⟨G3, stV, p03, hGbound, v3, ?_, hstV,
      derivable_mono derFinal Set.Subset.rfl le_rfl le_rfl hPbound Set.Subset.rfl⟩
    rwa [hsumAll]

private def contraCNF (LO HI : ℕ) (stS stT : ℕ → ℕ) (k : ℕ) : Set (Clause ℕ) :=
  if HI % 2 ^ k < LO % 2 ^ k then
    fullCNF {stS k, stT k} (fun x => ¬ (x (stS k) = true ∧ x (stT k) = true))
  else ∅

private lemma root_contradiction {n : ℕ} {G : List (ℕ × ℕ)} {o1 w LO HI : ℕ}
    {Sbits Tbits stS stT : ℕ → ℕ}
    (hHL : HI < LO) (hLO : LO < 2 ^ w)
    (hcS : HasCmp n G o1 true w LO Sbits stS)
    (hcT : HasCmp n G o1 false w HI Tbits stT)
    (hstS : ∀ i ≤ w, stS i < n + G.length)
    (hstT : ∀ i ≤ w, stT i < n + G.length) :
    Derivable (allGateClauses n G ∪
        (⋃ i ∈ Finset.range w, BitEqCNF (Sbits i) (Tbits i)) ∪
        unitTrueCNF (stS w) ∪ unitTrueCNF (stT w))
      (n + G.length) 30 ((w + 1) * 2 ^ 13) {∅} := by
  let F0 := allGateClauses n G ∪
    (⋃ i ∈ Finset.range w, BitEqCNF (Sbits i) (Tbits i)) ∪
    unitTrueCNF (stS w) ∪ unitTrueCNF (stT w)
  have h0 : Derivable F0 (n + G.length) 30 0 (contraCNF LO HI stS stT 0) := by
    have : contraCNF LO HI stS stT 0 = ∅ := by simp [contraCNF, Nat.mod_one]
    rw [this]; exact derivable_empty _ _ _
  have hstep : ∀ k < w, Derivable (F0 ∪ contraCNF LO HI stS stT k) (n + G.length) 30 (2 ^ 13)
      (contraCNF LO HI stS stT (k + 1) ∪ ∅) := by
    intro k hk
    by_cases hlt1 : HI % 2 ^ (k + 1) < LO % 2 ^ (k + 1)
    · have hc1 := hcS.2 k hk
      have hc2 := hcT.2 k hk
      have d1 : Derivable (F0 ∪ contraCNF LO HI stS stT k) (n + G.length) 30 (3 * 2 ^ 8)
          (cmpStepCNF true (LO.testBit k) (Sbits k) (stS k) (stS (k + 1))) :=
        derivable_mono (derive_cmpStep hc1)
          (fun C hC => Or.inl (Or.inl (Or.inl (Or.inl hC)))) le_rfl (by omega) le_rfl Set.Subset.rfl
      have d2 : Derivable (F0 ∪ contraCNF LO HI stS stT k) (n + G.length) 30 (3 * 2 ^ 8)
          (cmpStepCNF false (HI.testBit k) (Tbits k) (stT k) (stT (k + 1))) :=
        derivable_mono (derive_cmpStep hc2)
          (fun C hC => Or.inl (Or.inl (Or.inl (Or.inl hC)))) le_rfl (by omega) le_rfl Set.Subset.rfl
      have d12 := derivable_union d1 d2
      let Sc : Finset ℕ := {Sbits k, Tbits k, stS k, stT k, stS (k + 1), stT (k + 1)}
      have hScc : Sc.card ≤ 6 := by
        dsimp only [Sc]
        have := Finset.card_insert_le (Sbits k) {Tbits k, stS k, stT k, stS (k + 1), stT (k + 1)}
        have := card5_le (Tbits k) (stS k) (stT k) (stS (k + 1)) (stT (k + 1))
        omega
      have hScB : ∀ v ∈ Sc, v < n + G.length := by
        intro v hv; simp only [Sc, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hc1.1
        · exact hc2.1
        · exact hc1.2.1
        · exact hc2.2.1
        · exact hc1.2.2.1
        · exact hc2.2.2.1
      let Hc : Set (Clause ℕ) :=
        (cmpStepCNF true (LO.testBit k) (Sbits k) (stS k) (stS (k + 1)) ∪
         cmpStepCNF false (HI.testBit k) (Tbits k) (stT k) (stT (k + 1))) ∪
        BitEqCNF (Sbits k) (Tbits k) ∪ contraCNF LO HI stS stT k
      have hHcsub : Hc ⊆ (F0 ∪ contraCNF LO HI stS stT k) ∪
          (cmpStepCNF true (LO.testBit k) (Sbits k) (stS k) (stS (k + 1)) ∪
           cmpStepCNF false (HI.testBit k) (Tbits k) (stT k) (stT (k + 1))) := by
        intro C hC
        rcases hC with (h | h) | h
        · exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Set.mem_biUnion (Finset.mem_range.mpr hk) h)))))
        · exact Or.inl (Or.inr h)
      have hHcS : ∀ C ∈ Hc, ∀ l ∈ C, l.1 ∈ Sc := by
        intro C hC l hl
        rcases hC with ((h | h) | h) | h
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl <;> simp [Sc]) C h l hl
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl | rfl <;> simp [Sc]) C h l hl
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl <;> simp [Sc]) C h l hl
        · dsimp only [contraCNF] at h
          split_ifs at h with hlt0
          · exact fullCNF_vars_subset (fun v hv => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl <;> simp [Sc]) C h l hl
          · exact absurd h (Set.notMem_empty _)
      have hsem : ∀ x : ℕ → Bool, (∀ C ∈ Hc, ClauseSat x C) →
          ¬ (x (stS (k + 1)) = true ∧ x (stT (k + 1)) = true) := by
        intro x hx ⟨hS1, hT1⟩
        have e1 : x (stS (k + 1)) = cmpBit true (LO.testBit k) (x (Sbits k)) (x (stS k)) :=
          (fullCNF_sat_iff (cmpStepPred_dependsOn true (LO.testBit k) (Sbits k) (stS k) (stS (k + 1))) x).mp
            (fun C hC => hx C (Or.inl (Or.inl (Or.inl hC))))
        have e2 : x (stT (k + 1)) = cmpBit false (HI.testBit k) (x (Tbits k)) (x (stT k)) :=
          (fullCNF_sat_iff (cmpStepPred_dependsOn false (HI.testBit k) (Tbits k) (stT k) (stT (k + 1))) x).mp
            (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
        have eEq : x (Sbits k) = x (Tbits k) :=
          (fullCNF_sat_iff (bitEq_dependsOn (Sbits k) (Tbits k)) x).mp (fun C hC => hx C (Or.inl (Or.inr hC)))
        rw [mod_two_pow_succ HI k, mod_two_pow_succ LO k] at hlt1
        have hHlt : HI % 2 ^ k < 2 ^ k := Nat.mod_lt HI (Nat.two_pow_pos k)
        have hLlt : LO % 2 ^ k < 2 ^ k := Nat.mod_lt LO (Nat.two_pow_pos k)
        cases htbH : HI.testBit k <;> cases htbL : LO.testBit k
        · have hlt0 : HI % 2 ^ k < LO % 2 ^ k := by simp [htbH, htbL] at hlt1; omega
          have ePrev : ¬ (x (stS k) = true ∧ x (stT k) = true) := by
            have hsat : ∀ C ∈ contraCNF LO HI stS stT k, ClauseSat x C :=
              fun C hC => hx C (Or.inr hC)
            simp only [contraCNF, hlt0, ↓reduceIte] at hsat
            exact (fullCNF_sat_iff (fun a b hab => by rw [hab (stS k) (by simp), hab (stT k) (by simp)]) x).mp hsat
          simp only [htbL, htbH, cmpBit, ↓reduceIte, Bool.false_eq_true] at e1 e2
          rw [eEq] at e1
          cases hxb : x (Tbits k) <;> cases hxs : x (stS k) <;> cases hxt : x (stT k) <;> simp_all
        · simp only [htbL, htbH, cmpBit, ↓reduceIte, Bool.false_eq_true] at e1 e2
          rw [eEq] at e1
          cases hxb : x (Tbits k) <;> cases hxs : x (stS k) <;> cases hxt : x (stT k) <;> simp_all
        · simp [htbH, htbL] at hlt1; omega
        · have hlt0 : HI % 2 ^ k < LO % 2 ^ k := by simp [htbH, htbL] at hlt1; omega
          have ePrev : ¬ (x (stS k) = true ∧ x (stT k) = true) := by
            have hsat : ∀ C ∈ contraCNF LO HI stS stT k, ClauseSat x C :=
              fun C hC => hx C (Or.inr hC)
            simp only [contraCNF, hlt0, ↓reduceIte] at hsat
            exact (fullCNF_sat_iff (fun a b hab => by rw [hab (stS k) (by simp), hab (stT k) (by simp)]) x).mp hsat
          simp only [htbL, htbH, cmpBit, ↓reduceIte, Bool.false_eq_true] at e1 e2
          rw [eEq] at e1
          cases hxb : x (Tbits k) <;> cases hxs : x (stS k) <;> cases hxt : x (stT k) <;> simp_all
      have hOc : ({stS (k + 1), stT (k + 1)} : Finset ℕ).card ≤ 2 := by
        have := Finset.card_insert_le (stS (k + 1)) {stT (k + 1)}; simp only [Finset.card_singleton] at *; omega
      have hOS : ({stS (k + 1), stT (k + 1)} : Finset ℕ) ⊆ Sc := by
        intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> simp [Sc]
      have dOut := derive_fullCNF (O := {stS (k + 1), stT (k + 1)}) hHcsub hScB hHcS hOS
        (fun a b hab => by rw [hab (stS (k + 1)) (by simp), hab (stT (k + 1)) (by simp)]) hsem
      have dOut' := derivable_mono dOut Set.Subset.rfl le_rfl (by omega : Sc.card ≤ 30)
        (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by omega : _ ≤ 8))) Set.Subset.rfl
      have htr := derivable_trans_only d12 dOut'
      simp only [contraCNF, hlt1, ↓reduceIte, Set.union_empty]
      exact derivable_mono htr Set.Subset.rfl le_rfl le_rfl (by norm_num) Set.Subset.rfl
    · simp only [contraCNF, hlt1, ↓reduceIte, Set.union_empty]
      exact derivable_mono (derivable_empty _ _ _) Set.Subset.rfl le_rfl le_rfl (by omega) Set.Subset.rfl
  have hch := derivable_range_chain (contraCNF LO HI stS stT) (fun _ => ∅) w h0 hstep
  have hch' : Derivable F0 (n + G.length) 30 (w * 2 ^ 13) (contraCNF LO HI stS stT w) :=
    derivable_mono hch Set.Subset.rfl le_rfl le_rfl (by omega) Set.subset_union_left
  have hltw : HI % 2 ^ w < LO % 2 ^ w := by
    rw [Nat.mod_eq_of_lt (lt_trans hHL hLO), Nat.mod_eq_of_lt hLO]; exact hHL
  have hFinal : Derivable (F0 ∪ contraCNF LO HI stS stT w) (n + G.length) 30 (2 ^ 13) {∅} := by
    let Sf : Finset ℕ := {stS w, stT w}
    have hSfc : Sf.card ≤ 2 := by
      dsimp only [Sf]; have := Finset.card_insert_le (stS w) {stT w}; simp only [Finset.card_singleton] at *; omega
    have hSfB : ∀ v ∈ Sf, v < n + G.length := by
      intro v hv; simp only [Sf, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hstS w le_rfl
      · exact hstT w le_rfl
    let Hf : Set (Clause ℕ) :=
      fullCNF {stS w, stT w} (fun x => ¬ (x (stS w) = true ∧ x (stT w) = true)) ∪
      unitTrueCNF (stS w) ∪ unitTrueCNF (stT w)
    have hHfsub : Hf ⊆ F0 ∪ contraCNF LO HI stS stT w := by
      intro C hC
      rcases hC with (h | h) | h
      · exact Or.inr (by simpa [contraCNF, hltw] using h)
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
    have hHfS : ∀ C ∈ Hf, ∀ l ∈ C, l.1 ∈ Sf := by
      intro C hC l hl
      rcases hC with (h | h) | h
      · exact fullCNF_vars_subset Finset.Subset.rfl C h l hl
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [Sf, hv]) C h l hl
      · exact fullCNF_vars_subset (by intro v hv; simp only [Finset.mem_singleton] at hv; simp [Sf, hv]) C h l hl
    have hsem : ∀ x : ℕ → Bool, (∀ C ∈ Hf, ClauseSat x C) → ClauseSat x ∅ := by
      intro x hx
      have e1 : ¬ (x (stS w) = true ∧ x (stT w) = true) :=
        (fullCNF_sat_iff (fun a b hab => by rw [hab (stS w) (by simp), hab (stT w) (by simp)]) x).mp
          (fun C hC => hx C (Or.inl (Or.inl hC)))
      have e2 : x (stS w) = true := (fullCNF_sat_iff (unitTrue_dependsOn _) x).mp
        (fun C hC => hx C (Or.inl (Or.inr hC)))
      have e3 : x (stT w) = true := (fullCNF_sat_iff (unitTrue_dependsOn _) x).mp
        (fun C hC => hx C (Or.inr hC))
      exact absurd ⟨e2, e3⟩ e1
    have hd := derive_semantic hHfsub hSfB hHfS (fun _ h => absurd h.1 (Finset.notMem_empty _))
      (fun _ h => absurd h (Finset.notMem_empty _)) hsem
    refine derivable_mono hd Set.Subset.rfl le_rfl (by omega) ?_ Set.Subset.rfl
    have : 3 * 2 ^ Sf.card ≤ 3 * 2 ^ 2 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) hSfc)
    omega
  exact derivable_mono (derivable_trans_only hch' hFinal) Set.Subset.rfl le_rfl le_rfl
    (by rw [Nat.succ_mul]) Set.Subset.rfl

end QuotaAndContradiction

section MainAssembly

private def baseNat {n m h : ℕ} (row : Fin n → Fin m) (col : Fin n → Fin h)
    (lo : Fin m → ℕ) (hi : Fin h → ℕ) : Set (Clause ℕ) :=
  {D | (∃ (i : Fin m) (T : Finset (Fin n)),
          T ⊆ Finset.univ.filter (fun e : Fin n => row e = i) ∧
          T.card + lo i = (Finset.univ.filter (fun e : Fin n => row e = i)).card + 1 ∧
          D = T.image (fun e => (e.val, true))) ∨
       (∃ (j : Fin h) (T : Finset (Fin n)),
          T ⊆ Finset.univ.filter (fun e : Fin n => col e = j) ∧
          T.card = hi j + 1 ∧
          D = T.image (fun e => (e.val, false)))}

private lemma row_base_sat_ge {n m h : ℕ} {row : Fin n → Fin m} {col : Fin n → Fin h}
    {lo : Fin m → ℕ} {hi : Fin h → ℕ} (i : Fin m)
    (hlo : lo i ≤ (Finset.univ.filter (fun e : Fin n => row e = i)).card)
    (x : ℕ → Bool)
    (hx : ∀ T : Finset (Fin n),
      T ⊆ Finset.univ.filter (fun e : Fin n => row e = i) →
      T.card + lo i = (Finset.univ.filter (fun e : Fin n => row e = i)).card + 1 →
      ClauseSat x (T.image (fun e => (e.val, true)))) :
    lo i ≤ ∑ e ∈ Finset.univ.filter (fun e : Fin n => row e = i), (x e.val).toNat := by
  let R := Finset.univ.filter (fun e : Fin n => row e = i)
  have hsum : ∑ e ∈ R, (x e.val).toNat = (R.filter (fun e => x e.val = true)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    cases x e.val <;> simp
  rw [hsum]
  by_contra hlt
  push Not at hlt
  let F := R.filter (fun e => x e.val = false)
  have hpart : (R.filter (fun e => x e.val = true)).card + F.card = R.card := by
    have hdisj : Disjoint (R.filter (fun e => x e.val = true)) F := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      rw [h1'] at h2'; cases h2'
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext e
    simp only [F, Finset.mem_union, Finset.mem_filter]
    cases x e.val <;> simp
  have hloR : lo i ≤ R.card := hlo
  have hFge : R.card + 1 - lo i ≤ F.card := by omega
  obtain ⟨T, hTF, hTcard⟩ := Finset.exists_subset_card_eq hFge
  have hTR : T ⊆ R := Finset.Subset.trans hTF (Finset.filter_subset _ _)
  have hTsum : T.card + lo i = R.card + 1 := by omega
  obtain ⟨l, hl, hxl⟩ := hx T hTR hTsum
  rcases Finset.mem_image.mp hl with ⟨e, heT, rfl⟩
  have heF := (Finset.mem_filter.mp (hTF heT)).2
  simp only at hxl
  rw [heF] at hxl
  cases hxl

private lemma col_base_sat_le {n m h : ℕ} {row : Fin n → Fin m} {col : Fin n → Fin h}
    {lo : Fin m → ℕ} {hi : Fin h → ℕ} (j : Fin h)
    (x : ℕ → Bool)
    (hx : ∀ T : Finset (Fin n),
      T ⊆ Finset.univ.filter (fun e : Fin n => col e = j) →
      T.card = hi j + 1 →
      ClauseSat x (T.image (fun e => (e.val, false)))) :
    ∑ e ∈ Finset.univ.filter (fun e : Fin n => col e = j), (x e.val).toNat ≤ hi j := by
  let C := Finset.univ.filter (fun e : Fin n => col e = j)
  have hsum : ∑ e ∈ C, (x e.val).toNat = (C.filter (fun e => x e.val = true)).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    cases x e.val <;> simp
  rw [hsum]
  by_contra hgt
  push Not at hgt
  obtain ⟨T, hTCt, hTcard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hgt)
  have hTC : T ⊆ C := Finset.Subset.trans hTCt (Finset.filter_subset _ _)
  obtain ⟨l, hl, hxl⟩ := hx T hTC hTcard
  rcases Finset.mem_image.mp hl with ⟨e, heT, rfl⟩
  have heT' := (Finset.mem_filter.mp (hTCt heT)).2
  simp only at hxl
  rw [heT'] at hxl
  cases hxl

private def slotAt {n K : ℕ} (slot : Fin K → Option (Fin n)) (z0 u : ℕ) : ℕ :=
  if hu : u < K then match slot ⟨u, hu⟩ with | some e => e.val | none => z0 else z0

private lemma list_sum_map_eq_finset_sum {α : Type*} [DecidableEq α] (F : Finset α) (f : α → ℕ) :
    (F.toList.map f).sum = ∑ e ∈ F, f e := by
  have haux : ∀ (L : List α) (S : Finset α), L.Nodup → (∀ a, a ∈ L ↔ a ∈ S) →
      (L.map f).sum = ∑ e ∈ S, f e := by
    intro L
    induction L with
    | nil =>
      intro S _ hmem
      have hS : S = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun a ha => by
        have := (hmem a).mpr ha; exact List.not_mem_nil this)
      rw [hS]; simp
    | cons a tl ih =>
      intro S hnd hmem
      rw [List.nodup_cons] at hnd
      have haS : a ∈ S := (hmem a).mp List.mem_cons_self
      have hmem' : ∀ b, b ∈ tl ↔ b ∈ S.erase a := by
        intro b
        rw [Finset.mem_erase, ← hmem b, List.mem_cons]
        constructor
        · intro hb; exact ⟨fun hba => hnd.1 (hba ▸ hb), Or.inr hb⟩
        · rintro ⟨hne, rfl | hb⟩
          · exact absurd rfl hne
          · exact hb
      simp only [List.map_cons, List.sum_cons]
      rw [ih (S.erase a) hnd.2 hmem', Finset.add_sum_erase S f haS]
  exact haux F.toList F (Finset.nodup_toList F) (fun a => Finset.mem_toList)

private lemma block_padding_bijection {n m h B M : ℕ} (hB : 0 < B)
    (row : Fin n → Fin m) (col : Fin n → Fin h)
    (hmM : m ≤ M) (hhM : h ≤ M)
    (hrowB : ∀ i : Fin m, (Finset.univ.filter (fun e : Fin n => row e = i)).card ≤ B)
    (hcolB : ∀ j : Fin h, (Finset.univ.filter (fun e : Fin n => col e = j)).card ≤ B) :
    ∃ (rowSlot colSlot : Fin (M * B) → Option (Fin n)) (σ : Equiv.Perm (Fin (M * B))),
      (∀ u : Fin (M * B), rowSlot u = colSlot (σ u)) ∧
      (∀ (blk : ℕ) (hb : blk < m) (x : ℕ → Bool) (z0 : ℕ), x z0 = false →
        ∑ off ∈ Finset.range B, (x (slotAt rowSlot z0 (blk * B + off))).toNat =
          ∑ e ∈ Finset.univ.filter (fun e : Fin n => row e = ⟨blk, hb⟩), (x e.val).toNat) ∧
      (∀ (blk : ℕ) (hb : blk < m) (off : ℕ) (hoff : off < B) (e : Fin n),
        rowSlot ⟨blk * B + off, by
          have h1 : blk + 1 ≤ M := by omega
          calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
            _ = (blk + 1) * B := by ring
            _ ≤ M * B := Nat.mul_le_mul_right B h1⟩ = some e → row e = ⟨blk, hb⟩) ∧
      (∀ (blk : ℕ) (hge : m ≤ blk) (hM : blk < M) (off : ℕ) (hoff : off < B),
        rowSlot ⟨blk * B + off, by
          have h1 : blk + 1 ≤ M := by omega
          calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
            _ = (blk + 1) * B := by ring
            _ ≤ M * B := Nat.mul_le_mul_right B h1⟩ = none) ∧
      (∀ (blk : ℕ) (hb : blk < h) (x : ℕ → Bool) (z0 : ℕ), x z0 = false →
        ∑ off ∈ Finset.range B, (x (slotAt colSlot z0 (blk * B + off))).toNat =
          ∑ e ∈ Finset.univ.filter (fun e : Fin n => col e = ⟨blk, hb⟩), (x e.val).toNat) ∧
      (∀ (blk : ℕ) (hb : blk < h) (off : ℕ) (hoff : off < B) (e : Fin n),
        colSlot ⟨blk * B + off, by
          have h1 : blk + 1 ≤ M := by omega
          calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
            _ = (blk + 1) * B := by ring
            _ ≤ M * B := Nat.mul_le_mul_right B h1⟩ = some e → col e = ⟨blk, hb⟩) ∧
      (∀ (blk : ℕ) (hge : h ≤ blk) (hM : blk < M) (off : ℕ) (hoff : off < B),
        colSlot ⟨blk * B + off, by
          have h1 : blk + 1 ≤ M := by omega
          calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
            _ = (blk + 1) * B := by ring
            _ ≤ M * B := Nat.mul_le_mul_right B h1⟩ = none) := by
  classical
  let mkSlot := fun {k : ℕ} (part : Fin n → Fin k) (u : Fin (M * B)) =>
    if hk : u.val / B < k then
      let L := (Finset.univ.filter (fun e : Fin n => part e = ⟨u.val / B, hk⟩)).toList
      if ho : u.val % B < L.length then some L[u.val % B] else none
    else none
  have hdiv : ∀ blk off, off < B → (blk * B + off) / B = blk ∧ (blk * B + off) % B = off := by
    intro blk off hoff
    constructor
    · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hoff, zero_add]
    · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hoff]
  have hbi : ∀ {k : ℕ} (part : Fin n → Fin k) (_ : k ≤ M)
      (_ : ∀ i : Fin k, (Finset.univ.filter (fun e : Fin n => part e = i)).card ≤ B),
      ∃ eqv : Fin n ≃ {u : Fin (M * B) // (mkSlot part u).isSome = true},
        ∀ e : Fin n, mkSlot part (eqv e).1 = some e := by
    intro k part hkM hpartB
    have hmem_part : ∀ (u : Fin (M * B)) (e : Fin n),
        mkSlot part u = some e → ∃ hk : u.val / B < k, part e = ⟨u.val / B, hk⟩ := by
      intro u e hsome
      dsimp only [mkSlot] at hsome
      split_ifs at hsome with hk ho
      · simp only [Option.some.injEq] at hsome
        have hmem : e ∈ (Finset.univ.filter (fun e' : Fin n => part e' = ⟨u.val / B, hk⟩)).toList := by
          rw [← hsome]; exact List.getElem_mem ho
        rw [Finset.mem_toList, Finset.mem_filter] at hmem
        exact ⟨hk, hmem.2⟩
    have hinj : ∀ (u₁ u₂ : Fin (M * B)) (e : Fin n),
        mkSlot part u₁ = some e → mkSlot part u₂ = some e → u₁ = u₂ := by
      intro u₁ u₂ e h1 h2
      obtain ⟨hk1, hp1⟩ := hmem_part u₁ e h1
      obtain ⟨hk2, hp2⟩ := hmem_part u₂ e h2
      have hdiv_eq : u₁.val / B = u₂.val / B := by
        have := hp1.symm.trans hp2
        exact congrArg Fin.val this
      have hfin_eq : (⟨u₁.val / B, hk1⟩ : Fin k) = ⟨u₂.val / B, hk2⟩ := Fin.ext hdiv_eq
      dsimp only [mkSlot] at h1 h2
      rw [dif_pos hk1] at h1
      rw [dif_pos hk2] at h2
      split_ifs at h1 with ho1
      split_ifs at h2 with ho2
      simp only [Option.some.injEq] at h1 h2
      have ho2' : u₂.val % B < (Finset.univ.filter (fun e' : Fin n => part e' = ⟨u₁.val / B, hk1⟩)).toList.length := by
        simpa only [hfin_eq] using ho2
      have hnodup : ((Finset.univ.filter (fun e' : Fin n => part e' = ⟨u₁.val / B, hk1⟩)).toList).Nodup :=
        Finset.nodup_toList _
      have hmod_eq : u₁.val % B = u₂.val % B := by
        have h2' : (Finset.univ.filter (fun e' : Fin n => part e' = ⟨u₁.val / B, hk1⟩)).toList[u₂.val % B]'ho2' = e := by
          simpa only [hfin_eq] using h2
        exact (List.Nodup.getElem_inj_iff hnodup).mp (h1.trans h2'.symm)
      apply Fin.ext
      have e1 := Nat.div_add_mod u₁.val B
      have e2 := Nat.div_add_mod u₂.val B
      rw [hdiv_eq, hmod_eq] at e1
      omega
    have hsurj : ∀ e : Fin n, ∃ u : Fin (M * B), mkSlot part u = some e := by
      intro e
      let L := (Finset.univ.filter (fun e' : Fin n => part e' = part e)).toList
      have heL : e ∈ L := by rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨Finset.mem_univ _, rfl⟩
      obtain ⟨off, hoff, hget⟩ := List.mem_iff_getElem.mp heL
      have hLlen : L.length ≤ B := by
        rw [Finset.length_toList]; exact hpartB (part e)
      have hoffB : off < B := lt_of_lt_of_le hoff hLlen
      have hblkM : (part e).val + 1 ≤ M := by have := (part e).isLt; omega
      have huLt : (part e).val * B + off < M * B := by
        calc (part e).val * B + off < (part e).val * B + B := Nat.add_lt_add_left hoffB _
          _ = ((part e).val + 1) * B := by ring
          _ ≤ M * B := Nat.mul_le_mul_right B hblkM
      refine ⟨⟨(part e).val * B + off, huLt⟩, ?_⟩
      dsimp only [mkSlot]
      obtain ⟨hd, hm⟩ := hdiv (part e).val off hoffB
      simp only [hd, hm, (part e).isLt, ↓reduceDIte]
      have hfeq : (⟨(part e).val, (part e).isLt⟩ : Fin k) = part e := rfl
      dsimp only [L] at hoff hget
      simp only [hfeq, hoff, ↓reduceDIte, hget]
    let toF : Fin n → {u : Fin (M * B) // (mkSlot part u).isSome = true} := fun e =>
      ⟨Classical.choose (hsurj e), by rw [Classical.choose_spec (hsurj e)]; rfl⟩
    have htoF_spec : ∀ e, mkSlot part (toF e).1 = some e := fun e => Classical.choose_spec (hsurj e)
    have hbij : Function.Bijective toF := by
      constructor
      · intro e₁ e₂ heq
        have h1 := htoF_spec e₁
        have h2 := htoF_spec e₂
        rw [congrArg Subtype.val heq] at h1
        exact Option.some.inj (h1.symm.trans h2)
      · rintro ⟨u, hu⟩
        rcases Option.isSome_iff_exists.mp hu with ⟨e, he⟩
        refine ⟨e, Subtype.ext ?_⟩
        exact hinj _ _ e (htoF_spec e) he
    exact ⟨Equiv.ofBijective toF hbij, fun e => htoF_spec e⟩
  let rowSlot := mkSlot row
  let colSlot := mkSlot col
  obtain ⟨eRow, heRow⟩ := hbi row hmM hrowB
  obtain ⟨eCol, heCol⟩ := hbi col hhM hcolB
  have hcardNone : Fintype.card {u : Fin (M * B) // (rowSlot u).isSome = false} =
      Fintype.card {v : Fin (M * B) // (colSlot v).isSome = false} := by
    have h1 := Fintype.card_subtype_compl (fun u : Fin (M * B) => (rowSlot u).isSome = true)
    have h2 := Fintype.card_subtype_compl (fun v : Fin (M * B) => (colSlot v).isSome = true)
    have h3 : Fintype.card {u : Fin (M * B) // (rowSlot u).isSome = true} =
        Fintype.card {v : Fin (M * B) // (colSlot v).isSome = true} :=
      (Fintype.card_congr eRow).symm.trans (Fintype.card_congr eCol)
    have hr_iff : Fintype.card {u : Fin (M * B) // (rowSlot u).isSome = false} =
        Fintype.card {u : Fin (M * B) // ¬ ((rowSlot u).isSome = true)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun u => by cases (rowSlot u).isSome <;> simp))
    have hc_iff : Fintype.card {v : Fin (M * B) // (colSlot v).isSome = false} =
        Fintype.card {v : Fin (M * B) // ¬ ((colSlot v).isSome = true)} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by cases (colSlot v).isSome <;> simp))
    rw [hr_iff, hc_iff]; omega
  let eNone : {u : Fin (M * B) // (rowSlot u).isSome = false} ≃
      {v : Fin (M * B) // (colSlot v).isSome = false} := Fintype.equivOfCardEq hcardNone
  let eSome : {u : Fin (M * B) // (rowSlot u).isSome = true} ≃
      {v : Fin (M * B) // (colSlot v).isSome = true} := eRow.symm.trans eCol
  let splitR : Fin (M * B) ≃ {u : Fin (M * B) // (rowSlot u).isSome = true} ⊕
      {u : Fin (M * B) // (rowSlot u).isSome = false} :=
    (Equiv.sumCompl (fun u : Fin (M * B) => (rowSlot u).isSome = true)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun u => by cases (rowSlot u).isSome <;> simp)))
  let splitC : Fin (M * B) ≃ {v : Fin (M * B) // (colSlot v).isSome = true} ⊕
      {v : Fin (M * B) // (colSlot v).isSome = false} :=
    (Equiv.sumCompl (fun v : Fin (M * B) => (colSlot v).isSome = true)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun v => by cases (colSlot v).isSome <;> simp)))
  let σ : Equiv.Perm (Fin (M * B)) := splitR.trans ((Equiv.sumCongr eSome eNone).trans splitC.symm)
  have hσ : ∀ u : Fin (M * B), rowSlot u = colSlot (σ u) := by
    intro u
    by_cases hu : (rowSlot u).isSome = true
    · have hsr : splitR u = Sum.inl ⟨u, hu⟩ := by
        rw [Equiv.apply_eq_iff_eq_symm_apply]; rfl
      have hσu : σ u = (eSome ⟨u, hu⟩).1 := by
        dsimp only [σ, Equiv.trans_apply]
        rw [hsr]; rfl
      rw [hσu]
      let e := eRow.symm ⟨u, hu⟩
      have h1 : rowSlot u = some e := by
        have := heRow e
        simpa [e] using this
      have h2 : colSlot (eSome ⟨u, hu⟩).1 = some e := heCol e
      rw [h1, h2]
    · have huf : (rowSlot u).isSome = false := by cases h : (rowSlot u).isSome <;> simp_all
      have hsr : splitR u = Sum.inr ⟨u, huf⟩ := by
        rw [Equiv.apply_eq_iff_eq_symm_apply]; rfl
      have hσu : σ u = (eNone ⟨u, huf⟩).1 := by
        dsimp only [σ, Equiv.trans_apply]
        rw [hsr]; rfl
      rw [hσu]
      have h1 : rowSlot u = none := Option.not_isSome_iff_eq_none.mp hu
      have h2 : colSlot (eNone ⟨u, huf⟩).1 = none := by
        have := (eNone ⟨u, huf⟩).2
        exact Option.not_isSome_iff_eq_none.mp (by rw [this]; simp)
      rw [h1, h2]
  have hsumPart : ∀ {k : ℕ} (part : Fin n → Fin k) (_ : k ≤ M)
      (_ : ∀ i : Fin k, (Finset.univ.filter (fun e : Fin n => part e = i)).card ≤ B)
      (blk : ℕ) (hb : blk < k) (x : ℕ → Bool) (z0 : ℕ), x z0 = false →
      ∑ off ∈ Finset.range B, (x (slotAt (mkSlot part) z0 (blk * B + off))).toNat =
        ∑ e ∈ Finset.univ.filter (fun e : Fin n => part e = ⟨blk, hb⟩), (x e.val).toNat := by
    intro k part hkM hpartB blk hb x z0 hz0
    let F := Finset.univ.filter (fun e : Fin n => part e = ⟨blk, hb⟩)
    let L := F.toList
    have hLlen : L.length ≤ B := by rw [Finset.length_toList]; exact hpartB ⟨blk, hb⟩
    have hsplit : B = L.length + (B - L.length) := by omega
    have h1 : ∑ off ∈ Finset.range B, (x (slotAt (mkSlot part) z0 (blk * B + off))).toNat =
        ∑ off ∈ Finset.range L.length, (L[off]?.elim 0 (fun e => (x e.val).toNat)) := by
      rw [show Finset.range B = Finset.range (L.length + (B - L.length)) from congrArg Finset.range hsplit]
      rw [Finset.sum_range_add]
      have hzero : ∑ i ∈ Finset.range (B - L.length),
          (x (slotAt (mkSlot part) z0 (blk * B + (L.length + i)))).toNat = 0 := by
        refine Finset.sum_eq_zero (fun i hi => ?_)
        rw [Finset.mem_range] at hi
        obtain ⟨hd, hm⟩ := hdiv blk (L.length + i) (by omega)
        have hltMB : blk * B + (L.length + i) < M * B := by
          have h1 : blk + 1 ≤ M := by omega
          have hlt : L.length + i < B := by omega
          calc blk * B + (L.length + i) < blk * B + B := Nat.add_lt_add_left hlt _
            _ = (blk + 1) * B := by ring
            _ ≤ M * B := Nat.mul_le_mul_right B h1
        have hnone : mkSlot part ⟨blk * B + (L.length + i), hltMB⟩ = none := by
          dsimp only [mkSlot]
          simp only [hd, hm, hb, ↓reduceDIte]
          split_ifs with h
          · exfalso; change L.length + i < L.length at h; omega
          · rfl
        simp only [slotAt, hltMB, ↓reduceDIte, hnone, hz0, Bool.toNat_false]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl (fun off hoff => ?_)
      rw [Finset.mem_range] at hoff
      obtain ⟨hd, hm⟩ := hdiv blk off (lt_of_lt_of_le hoff hLlen)
      have hltMB : blk * B + off < M * B := by
        have h1 : blk + 1 ≤ M := by omega
        have hlt : off < B := lt_of_lt_of_le hoff hLlen
        calc blk * B + off < blk * B + B := Nat.add_lt_add_left hlt _
          _ = (blk + 1) * B := by ring
          _ ≤ M * B := Nat.mul_le_mul_right B h1
      have hsome : mkSlot part ⟨blk * B + off, hltMB⟩ = some L[off] := by
        dsimp only [mkSlot]
        simp only [hd, hm, hb, ↓reduceDIte]
        split_ifs with h
        · rfl
        · exfalso; exact h hoff
      simp only [slotAt, hltMB, ↓reduceDIte, hsome, List.getElem?_eq_getElem hoff, Option.elim_some]
    rw [h1]
    have hlist : ∑ off ∈ Finset.range L.length, (L[off]?.elim 0 (fun e => (x e.val).toNat)) =
        (L.map (fun e => (x e.val).toNat)).sum := by
      clear * -
      induction L with
      | nil => simp
      | cons a tl ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        rw [Finset.sum_range_succ']
        simp only [List.getElem?_cons_zero, Option.elim_some, List.getElem?_cons_succ]
        rw [ih, add_comm]
    rw [hlist]
    exact list_sum_map_eq_finset_sum F (fun e => (x e.val).toNat)
  have hblkMem : ∀ {k : ℕ} (part : Fin n → Fin k) (_ : k ≤ M)
      (blk : ℕ) (hb : blk < k) (off : ℕ) (hoff : off < B) (e : Fin n),
      mkSlot part ⟨blk * B + off, by
        have h1 : blk + 1 ≤ M := by omega
        calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
          _ = (blk + 1) * B := by ring
          _ ≤ M * B := Nat.mul_le_mul_right B h1⟩ = some e → part e = ⟨blk, hb⟩ := by
    intro k part hkM blk hb off hoff e hsome
    obtain ⟨hd, hm⟩ := hdiv blk off hoff
    dsimp only [mkSlot] at hsome
    simp only [hd, hm, hb, ↓reduceDIte] at hsome
    split_ifs at hsome with ho
    simp only [Option.some.injEq] at hsome
    have hmem : e ∈ (Finset.univ.filter (fun e' : Fin n => part e' = ⟨blk, hb⟩)).toList := by
      rw [← hsome]; exact List.getElem_mem ho
    rw [Finset.mem_toList, Finset.mem_filter] at hmem
    exact hmem.2
  have hblkNone : ∀ {k : ℕ} (part : Fin n → Fin k)
      (blk : ℕ) (hge : k ≤ blk) (hM : blk < M) (off : ℕ) (hoff : off < B),
      mkSlot part ⟨blk * B + off, by
        have h1 : blk + 1 ≤ M := by omega
        calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
          _ = (blk + 1) * B := by ring
          _ ≤ M * B := Nat.mul_le_mul_right B h1⟩ = none := by
    intro k part blk hge hM off hoff
    obtain ⟨hd, _⟩ := hdiv blk off hoff
    dsimp only [mkSlot]
    have hnot : ¬ (blk < k) := by omega
    simp [hd, hnot]
  exact ⟨rowSlot, colSlot, σ, hσ,
    hsumPart row hmM hrowB, hblkMem row hmM, hblkNone row,
    hsumPart col hhM hcolB, hblkMem col hhM, hblkNone col⟩

private lemma two_pow_clog_le {k : ℕ} (hk : 0 < k) : 2 ^ Nat.clog 2 k ≤ 2 * k := by
  by_cases h1 : k = 1
  · subst h1; simp
  · have hpos : 0 < Nat.clog 2 k := Nat.clog_pos (by omega) (by omega)
    have hlt : 2 ^ (Nat.clog 2 k - 1) < k := by
      by_contra hge
      push Not at hge
      have hle : Nat.clog 2 k ≤ Nat.clog 2 k - 1 :=
        (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).mpr hge
      omega
    have hpow : 2 ^ Nat.clog 2 k = 2 * 2 ^ (Nat.clog 2 k - 1) := by
      have : Nat.clog 2 k = (Nat.clog 2 k - 1) + 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.pow_succ]; omega
    omega

private lemma final_size_bound {k_b B L_leaf C r M D L N s plen : ℕ}
    (hBpos : 0 < B) (hNpos : 1 ≤ N) (hLmul : L = M * B) (hDdef : D = r + k_b)
    (hM_le : M ≤ 2 * N) (hr_le : r ≤ Nat.clog 2 N)
    (hC_ge : 1000 + 2 * B * (k_b + 1) * (72 + K_eq + 2 ^ 14) +
      2 * B * 36 + 4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep) ≤ C)
    (hs_le : s ≤ 3 + 36 * L + 72 * D * L + 12 * (k_b + 3) * M)
    (hπ_le : plen ≤ 2 * (3 * 2 ^ 5) + K_eq * D * L +
      2 * (L_leaf + 2 * (k_b + 4) * K_qstep) * M + (D + 2) * 2 ^ 13) :
    s + plen ≤ C * N * (1 + Nat.clog 2 N) := by
  let Q := N * (1 + Nat.clog 2 N)
  have hL_le : L ≤ 2 * B * N := by
    rw [hLmul]
    calc M * B ≤ (2 * N) * B := Nat.mul_le_mul_right B hM_le
      _ = 2 * B * N := by ring
  have hD1_le : D + 1 ≤ (k_b + 1) * (1 + Nat.clog 2 N) := by
    rw [hDdef]
    have h1 : k_b ≤ k_b * (1 + Nat.clog 2 N) :=
      Nat.le_mul_of_pos_right k_b (Nat.zero_lt_one.trans_le (Nat.le_add_right 1 _))
    have h2 : (k_b + 1) * (1 + Nat.clog 2 N) = k_b * (1 + Nat.clog 2 N) + 1 + Nat.clog 2 N := by ring
    rw [h2]
    calc r + k_b + 1 = k_b + 1 + r := by ring
      _ ≤ k_b * (1 + Nat.clog 2 N) + 1 + Nat.clog 2 N :=
          Nat.add_le_add (Nat.add_le_add_right h1 1) hr_le
  have hD_le : D ≤ (k_b + 1) * (1 + Nat.clog 2 N) := by omega
  have hN_le : N ≤ Q := Nat.le_mul_of_pos_right N (by omega)
  have hQ1 : 1 ≤ Q := le_trans hNpos hN_le
  have hDL_le : D * L ≤ 2 * B * (k_b + 1) * Q := by
    calc D * L ≤ ((k_b + 1) * (1 + Nat.clog 2 N)) * (2 * B * N) :=
          Nat.mul_le_mul hD_le hL_le
      _ = 2 * B * (k_b + 1) * Q := by dsimp only [Q]; ring
  have hD2_le : (D + 2) * 2 ^ 13 ≤ (2 * B * (k_b + 1) * 2 ^ 14) * Q := by
    have hkp : 1 ≤ (k_b + 1) * (1 + Nat.clog 2 N) :=
      Nat.mul_le_mul (by omega : 1 ≤ k_b + 1) (by omega : 1 ≤ 1 + Nat.clog 2 N)
    have hD2 : D + 2 ≤ 2 * ((k_b + 1) * (1 + Nat.clog 2 N)) := by omega
    have h1 : (D + 2) * 2 ^ 13 ≤ (k_b + 1) * (1 + Nat.clog 2 N) * 2 ^ 14 := by
      calc (D + 2) * 2 ^ 13 ≤ (2 * ((k_b + 1) * (1 + Nat.clog 2 N))) * 2 ^ 13 :=
            Nat.mul_le_mul_right _ hD2
        _ = (k_b + 1) * (1 + Nat.clog 2 N) * 2 ^ 14 := by ring
    have hBN : 1 ≤ 2 * B * N := by
      have h1 : 1 ≤ B * N := Nat.mul_le_mul hBpos hNpos
      have h2 : 2 * B * N = 2 * (B * N) := by ring
      omega
    calc (D + 2) * 2 ^ 13 ≤ (k_b + 1) * (1 + Nat.clog 2 N) * 2 ^ 14 := h1
      _ = ((k_b + 1) * (1 + Nat.clog 2 N) * 2 ^ 14) * 1 := by ring
      _ ≤ ((k_b + 1) * (1 + Nat.clog 2 N) * 2 ^ 14) * (2 * B * N) := Nat.mul_le_mul_left _ hBN
      _ = (2 * B * (k_b + 1) * 2 ^ 14) * Q := by dsimp only [Q]; ring
  have hterm1 : 3 + 2 * (3 * 2 ^ 5) ≤ 1000 * Q := by
    calc 3 + 2 * (3 * 2 ^ 5) ≤ 1000 * 1 := by norm_num
      _ ≤ 1000 * Q := Nat.mul_le_mul_left 1000 hQ1
  have hterm2 : 36 * L ≤ (2 * B * 36) * Q := by
    calc 36 * L ≤ 36 * (2 * B * N) := Nat.mul_le_mul_left 36 hL_le
      _ = (2 * B * 36) * N := by ring
      _ ≤ (2 * B * 36) * Q := Nat.mul_le_mul_left _ hN_le
  have hterm3 : (72 + K_eq) * (D * L) ≤ (2 * B * (k_b + 1) * (72 + K_eq)) * Q := by
    calc (72 + K_eq) * (D * L) ≤ (72 + K_eq) * (2 * B * (k_b + 1) * Q) :=
          Nat.mul_le_mul_left _ hDL_le
      _ = (2 * B * (k_b + 1) * (72 + K_eq)) * Q := by ring
  have hterm4 : (12 * (k_b + 3) + 2 * (L_leaf + 2 * (k_b + 4) * K_qstep)) * M ≤
      (4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep)) * Q := by
    calc (12 * (k_b + 3) + 2 * (L_leaf + 2 * (k_b + 4) * K_qstep)) * M
        ≤ (12 * (k_b + 3) + 2 * (L_leaf + 2 * (k_b + 4) * K_qstep)) * (2 * N) :=
          Nat.mul_le_mul_left _ hM_le
      _ = (4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep)) * N := by ring
      _ ≤ (4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep)) * Q :=
          Nat.mul_le_mul_left _ hN_le
  have hmul_assoc : C * N * (1 + Nat.clog 2 N) = C * Q := Nat.mul_assoc _ _ _
  rw [hmul_assoc]
  have hsum_all : (1000 + 2 * B * (k_b + 1) * (72 + K_eq + 2 ^ 14) +
      2 * B * 36 + 4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep)) * Q ≤ C * Q :=
    Nat.mul_le_mul_right Q hC_ge
  have h72 : 72 * D * L + K_eq * D * L = (72 + K_eq) * (D * L) := by ring
  have hMdist : 12 * (k_b + 3) * M + 2 * (L_leaf + 2 * (k_b + 4) * K_qstep) * M =
      (12 * (k_b + 3) + 2 * (L_leaf + 2 * (k_b + 4) * K_qstep)) * M := by ring
  have hsplitC : (1000 + 2 * B * (k_b + 1) * (72 + K_eq + 2 ^ 14) +
      2 * B * 36 + 4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep)) * Q =
      1000 * Q + (2 * B * (k_b + 1) * (72 + K_eq)) * Q + (2 * B * (k_b + 1) * 2 ^ 14) * Q +
      (2 * B * 36) * Q + (4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep)) * Q := by ring
  omega

private lemma main_proof (b : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n m h : ℕ) (row : Fin n → Fin m) (col : Fin n → Fin h)
      (lo : Fin m → ℕ) (hi : Fin h → ℕ),
    let rows := fun i : Fin m => Finset.univ.filter (fun e : Fin n => row e = i)
    let cols := fun j : Fin h => Finset.univ.filter (fun e : Fin n => col e = j)
    (∀ i, lo i ≤ (rows i).card ∧ (rows i).card ≤ b) →
    (∀ j, hi j ≤ (cols j).card ∧ (cols j).card ≤ b) →
    (∑ j : Fin h, hi j) < (∑ i : Fin m, lo i) →
    let N := n + m + h + 1
    ∃ (s : ℕ) (first second : Fin s → Fin n ⊕ Fin s),
      let V := Fin n ⊕ Fin s
      let earlier := fun i : Fin s =>
        Sum.elim (fun _ : Fin n => True) (fun j : Fin s => j.val < i.val)
      let literals := fun (T : Finset (Fin n)) (sign : Bool) =>
        T.image (fun e => ((Sum.inl e : V), sign))
      let base : Set (Clause V) := {D |
        (∃ (i : Fin m) (T : Finset (Fin n)), T ⊆ rows i ∧
          T.card + lo i = (rows i).card + 1 ∧ D = literals T true) ∨
        (∃ (j : Fin h) (T : Finset (Fin n)), T ⊆ cols j ∧
          T.card = hi j + 1 ∧ D = literals T false)}
      let gates : Set (Clause V) := {D |
        ∃ i : Fin s, D = {((Sum.inr i : V), false), (first i, false), (second i, false)} ∨
          D = {((Sum.inr i : V), true), (first i, true)} ∨
          D = {((Sum.inr i : V), true), (second i, true)}}
      (∀ i, earlier i (first i) ∧ earlier i (second i)) ∧
      ∃ π : List (Clause V),
        IsRefutation (base ∪ gates) π ∧
        s + π.length ≤ C * N * (1 + Nat.clog 2 N) ∧ ∀ D ∈ π, D.card ≤ C := by
  let k_b := Nat.clog 2 (max b 1)
  let B := 2 ^ k_b
  let W_leaf := b + 2 + 18 * B + 4 * (k_b + 1) + 30
  let L_leaf := 3 * 2 ^ (1 + W_leaf)
  let C := max W_leaf (1000 + 2 * B * (k_b + 1) * (72 + K_eq + 2 ^ 14) +
    2 * B * 36 + 4 * (6 * (k_b + 3) + L_leaf + 2 * (k_b + 4) * K_qstep))
  refine ⟨C, by dsimp only [C]; omega, ?_⟩
  intro n m h row col lo hi rows cols hrow hcol hquota N
  have hlo_pos : 0 < ∑ i : Fin m, lo i := by omega
  have hex_i : ∃ i : Fin m, 0 < lo i := by
    by_contra hall
    push Not at hall
    have : ∑ i : Fin m, lo i = 0 := Finset.sum_eq_zero (fun i _ => Nat.eq_zero_of_le_zero (hall i))
    omega
  obtain ⟨i0, hi0⟩ := hex_i
  have hri0 : 0 < (rows i0).card := lt_of_lt_of_le hi0 (hrow i0).1
  obtain ⟨e0, _⟩ := Finset.card_pos.mp hri0
  have hn : 0 < n := Nat.pos_of_ne_zero (fun hn0 => by subst hn0; exact Fin.elim0 e0)
  have hm : 0 < m := Nat.pos_of_ne_zero (fun hm0 => by subst hm0; exact Fin.elim0 i0)
  have hh : 0 < h := Nat.pos_of_ne_zero (fun hh0 => by subst hh0; exact Fin.elim0 (col e0))
  have hb_le_B : b ≤ B := le_trans (le_max_left b 1) (Nat.le_pow_clog (by omega) _)
  have hBpos : 0 < B := Nat.two_pow_pos k_b
  let r := Nat.clog 2 (max m h)
  let M := 2 ^ r
  let D := r + k_b
  let L := 2 ^ D
  have hmM : m ≤ M := le_trans (le_max_left m h) (Nat.le_pow_clog (by omega) _)
  have hhM : h ≤ M := le_trans (le_max_right m h) (Nat.le_pow_clog (by omega) _)
  have hLmul : L = M * B := Nat.pow_add 2 r k_b
  obtain ⟨rowSlot, colSlot, σ_mb, hσ_mb, hsumR, hmemR, hnoneR, hsumC, hmemC, hnoneC⟩ :=
    block_padding_bijection hBpos row col hmM hhM
      (fun i => le_trans (hrow i).2 hb_le_B) (fun j => le_trans (hcol j).2 hb_le_B)
  let eqL : Fin L ≃ Fin (M * B) := finCongr hLmul
  let σ : Equiv.Perm (Fin L) := eqL.trans (σ_mb.trans eqL.symm)
  obtain ⟨G0, z0, o1, lG0, vG0, hcG0⟩ := exists_addConsts n hn
  have hz0 : z0 < n + G0.length := hcG0.1
  have ho1 : o1 < n + G0.length := hcG0.2.1
  let rowW : ℕ → ℕ := fun u =>
    if hu : u < L then match rowSlot (eqL ⟨u, hu⟩) with | some e => e.val | none => z0 else z0
  let colW : ℕ → ℕ := fun v =>
    if hv : v < L then match colSlot (eqL ⟨v, hv⟩) with | some e => e.val | none => z0 else z0
  have hrowW_lt : ∀ p < L, rowW p < n + G0.length := by
    intro p hp; simp only [rowW, hp, ↓reduceDIte]
    cases rowSlot (eqL ⟨p, hp⟩) with
    | none => exact hz0
    | some e => exact Nat.lt_of_lt_of_le e.isLt (Nat.le_add_right _ _)
  have hcolW_lt : ∀ p < L, colW p < n + G0.length := by
    intro p hp; simp only [colW, hp, ↓reduceDIte]
    cases colSlot (eqL ⟨p, hp⟩) with
    | none => exact hz0
    | some e => exact Nat.lt_of_lt_of_le e.isLt (Nat.le_add_right _ _)
  have hpermW : ∀ i : Fin L, rowW i.val = colW (σ i).val := by
    intro i
    simp only [rowW, colW, i.isLt, (σ i).isLt, ↓reduceDIte]
    have h1 : eqL (σ i) = σ_mb (eqL i) := by simp [σ]
    rw [h1, ← hσ_mb (eqL i)]
  obtain ⟨G1, Xbits, Xcar, p01, lG1, vG1, ctX, hblX, _⟩ :=
    exists_buildCounterTree z0 vG0 hz0 D rowW hrowW_lt
  obtain ⟨G2, Ybits, Ycar, p12, lG2, vG2, ctY, hblY, _⟩ :=
    exists_buildCounterTree z0 vG1 (by have := p01.length_le; omega) D colW
      (fun p hp => by have := hcolW_lt p hp; have := p01.length_le; omega)
  have p02 : G0 <+: G2 := p01.trans p12
  obtain ⟨G3, p23, lG3, vG3, derPerm⟩ :=
    prove_perm_equiv z0 D σ vG2 (by have := p02.length_le; omega)
      (fun p hp => ⟨by have := hrowW_lt p hp; have := p02.length_le; omega,
                    by have := hcolW_lt p hp; have := p02.length_le; omega⟩)
      hpermW (hasCounterTree_mono p12 ctX) ctY
      (fun i hi => ⟨by have := hblX D le_rfl 0 (by simp) i hi; have := p12.length_le; omega,
                    by have := hblY D le_rfl 0 (by simp) i hi; omega⟩)
  let baseF := baseNat row col lo hi
  let qLo : ℕ → ℕ := fun blk => if hb : blk < m then lo ⟨blk, hb⟩ else 0
  let qHi : ℕ → ℕ := fun blk => if hb : blk < h then hi ⟨blk, hb⟩ else 0
  have hqLo : ∀ blk < M, qLo blk ≤ B := by
    intro blk _; dsimp only [qLo]; split_ifs with hb
    · exact le_trans (hrow ⟨blk, hb⟩).1 (le_trans (hrow ⟨blk, hb⟩).2 hb_le_B)
    · exact Nat.zero_le B
  have hqHi : ∀ blk < M, qHi blk ≤ B := by
    intro blk _; dsimp only [qHi]; split_ifs with hb
    · exact le_trans (hcol ⟨blk, hb⟩).1 (le_trans (hcol ⟨blk, hb⟩).2 hb_le_B)
    · exact Nat.zero_le B
  have hLeafRow : ∀ blk < M, ∀ Gq : List (ℕ × ℕ), G3 <+: Gq → ∀ st : ℕ → ℕ,
      HasCmp n Gq o1 true (k_b + 1) (qLo blk) (fun i => Xbits k_b blk i) st →
      Derivable (baseF ∪ allGateClauses n Gq ∪ constCNF z0 o1) (n + Gq.length) W_leaf L_leaf
        (unitTrueCNF (st (k_b + 1))) := by
    intro blk hblk Gq p3q st hcmp
    have p0q : G0 <+: Gq := p02.trans (p23.trans p3q)
    have p1q : G1 <+: Gq := p12.trans (p23.trans p3q)
    have hsubCT := counterTree_subtree (hasCounterTree_mono p1q ctX) blk hblk
    obtain ⟨Wc, Hc, hWcc, hWcB, hbcW, hHFc, hHSc, hvalc⟩ := counterTree_wireSet hsubCT
    obtain ⟨Wp, Hp, hWpc, hWpB, hstW, hHFp, hHSp, hvalp⟩ := cmp_wireSet hcmp
    have hleafSub : (Finset.range B).image (fun p => rowW (blk * B + p)) ⊆
        (if hb : blk < m then (rows ⟨blk, hb⟩).image Fin.val else ∅) ∪ {z0} := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨off, hoff, rfl⟩
      rw [Finset.mem_range] at hoff
      have hlt : blk * B + off < L := by
        rw [hLmul]
        have h1 : blk + 1 ≤ M := hblk
        calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
          _ = (blk + 1) * B := by ring
          _ ≤ M * B := Nat.mul_le_mul_right B h1
      simp only [rowW, hlt, ↓reduceDIte]
      by_cases hb : blk < m
      · simp only [hb, ↓reduceDIte]
        cases hslot : rowSlot (eqL ⟨blk * B + off, hlt⟩) with
        | none => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        | some e =>
          have hre : row e = ⟨blk, hb⟩ := hmemR blk hb off hoff e (by simpa [eqL] using hslot)
          exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hre⟩, rfl⟩)
      · have hnone : rowSlot (eqL ⟨blk * B + off, hlt⟩) = none :=
          hnoneR blk (by omega) hblk off hoff
        rw [hnone]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    let BaseV : Finset ℕ := if hb : blk < m then (rows ⟨blk, hb⟩).image Fin.val else ∅
    let Sblk : Finset ℕ := BaseV ∪ {z0, o1} ∪ Wc ∪ Wp
    have hBaseVc : BaseV.card ≤ b := by
      dsimp only [BaseV]; split_ifs with hb
      · exact le_trans Finset.card_image_le (hrow ⟨blk, hb⟩).2
      · simp
    have hSblkc : Sblk.card ≤ W_leaf := by
      have hzo : ({z0, o1} : Finset ℕ).card ≤ 2 := by
        have := Finset.card_insert_le z0 {o1}; simp only [Finset.card_singleton] at *; omega
      dsimp only [Sblk]
      have := Finset.card_union_le (BaseV ∪ {z0, o1} ∪ Wc) Wp
      have := Finset.card_union_le (BaseV ∪ {z0, o1}) Wc
      have := Finset.card_union_le BaseV {z0, o1}
      dsimp only [W_leaf, B]
      omega
    have hSblkB : ∀ v ∈ Sblk, v < n + Gq.length := by
      intro v hv
      simp only [Sblk, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with ((hB1 | (rfl | rfl)) | hW1) | hW2
      · dsimp only [BaseV] at hB1; split_ifs at hB1 with hb
        · rcases Finset.mem_image.mp hB1 with ⟨e, -, rfl⟩
          exact Nat.lt_of_lt_of_le e.isLt (Nat.le_add_right _ _)
        · exact absurd hB1 (Finset.notMem_empty _)
      · have := p0q.length_le; omega
      · have := p0q.length_le; omega
      · exact hWcB v hW1
      · exact hWpB v hW2
    let Hbase : Set (Clause ℕ) :=
      if hb : blk < m then
        {D | ∃ T : Finset (Fin n), T ⊆ rows ⟨blk, hb⟩ ∧
          T.card + lo ⟨blk, hb⟩ = (rows ⟨blk, hb⟩).card + 1 ∧
          D = T.image (fun e => (e.val, true))}
      else ∅
    let Hblk : Set (Clause ℕ) := Hbase ∪ Hc ∪ Hp ∪ constCNF z0 o1
    have hHblkSub : Hblk ⊆ baseF ∪ allGateClauses n Gq ∪ constCNF z0 o1 := by
      intro C hC
      rcases hC with ((h1 | h2) | h3) | h4
      · apply Or.inl; apply Or.inl
        dsimp only [Hbase] at h1; split_ifs at h1 with hb
        · rcases h1 with ⟨T, hT1, hT2, hT3⟩
          exact Or.inl ⟨⟨blk, hb⟩, T, hT1, hT2, hT3⟩
        · exact absurd h1 (Set.notMem_empty _)
      · exact Or.inl (Or.inr (hHFc h2))
      · exact Or.inl (Or.inr (hHFp h3))
      · exact Or.inr h4
    have hHblkS : ∀ C ∈ Hblk, ∀ l ∈ C, l.1 ∈ Sblk := by
      intro C hC l hl
      rcases hC with ((h1 | h2) | h3) | h4
      · dsimp only [Hbase] at h1; split_ifs at h1 with hb
        · rcases h1 with ⟨T, hTR, -, rfl⟩
          rcases Finset.mem_image.mp hl with ⟨e, heT, rfl⟩
          apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
          simp only [BaseV, hb, ↓reduceDIte]
          exact Finset.mem_image.mpr ⟨e, hTR heT, rfl⟩
        · exact absurd h1 (Set.notMem_empty _)
      · have hv := hHSc C h2 l hl
        rcases Finset.mem_union.mp hv with hlv | hzw
        · have hv' := hleafSub hlv
          rcases Finset.mem_union.mp hv' with hbv | hz'
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hbv))
          · simp only [Finset.mem_singleton] at hz'
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
        · rcases Finset.mem_insert.mp hzw with hz' | hwc
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hwc)
      · have hv := hHSp C h3 l hl
        rcases Finset.mem_union.mp hv with him | how
        · rcases Finset.mem_image.mp him with ⟨i, hi, hiX⟩
          rw [Finset.mem_range] at hi
          have hmem := hbcW i (by omega)
          simp only [Nat.sub_self, Nat.pow_zero, mul_one, add_zero] at hmem
          rw [← hiX]
          rcases Finset.mem_union.mp hmem with hlv | hzw
          · have hv' := hleafSub hlv
            rcases Finset.mem_union.mp hv' with hbv | hz'
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hbv))
            · simp only [Finset.mem_singleton] at hz'
              exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
          · rcases Finset.mem_insert.mp hzw with hz' | hwc
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hwc)
        · rcases Finset.mem_insert.mp how with ho' | hwp
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [ho'])))
          · exact Finset.mem_union_right _ hwp
      · rcases h4 with hz' | ho'
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_singleton] at hv; simp [Sblk, hv]) C hz' l hl
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_singleton] at hv; simp [Sblk, hv]) C ho' l hl
    have hOutS : ({st (k_b + 1)} : Finset ℕ) ⊆ Sblk := by
      intro v hv; simp only [Finset.mem_singleton] at hv; rw [hv]
      rcases Finset.mem_insert.mp hstW with ho' | hwp
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [ho'])))
      · exact Finset.mem_union_right _ hwp
    have hsem : ∀ x : ℕ → Bool, (∀ C ∈ Hblk, ClauseSat x C) → x (st (k_b + 1)) = true := by
      intro x hx
      have ez : x z0 = false := (fullCNF_sat_iff (fun a b hab => by rw [hab z0 (by simp)]) x).mp
        (fun C hC => hx C (Or.inr (Or.inl hC)))
      have eo : x o1 = true := (fullCNF_sat_iff (fun a b hab => by rw [hab o1 (by simp)]) x).mp
        (fun C hC => hx C (Or.inr (Or.inr hC)))
      have hvc := hvalc x ez (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
      simp only [Nat.sub_self, Nat.pow_zero, mul_one, add_zero] at hvc
      have hvp := hvalp x eo (fun C hC => hx C (Or.inl (Or.inr hC)))
      simp only [↓reduceIte] at hvp
      rw [hvp, hvc]
      have hqlt : qLo blk < 2 ^ (k_b + 1) := by
        have := hqLo blk hblk; rw [Nat.pow_succ]; dsimp only [B] at this; omega
      rw [Nat.mod_eq_of_lt hqlt]
      by_cases hb : blk < m
      · simp only [qLo, hb, ↓reduceDIte]
        have hsum_eq : ∑ p ∈ Finset.range B, (x (rowW (blk * B + p))).toNat =
            ∑ e ∈ rows ⟨blk, hb⟩, (x e.val).toNat := by
          have hs := hsumR blk hb x z0 ez
          rw [← hs]
          refine Finset.sum_congr rfl (fun off hoff => ?_)
          rw [Finset.mem_range] at hoff
          have hlt : blk * B + off < L := by
            rw [hLmul]
            have h1 : blk + 1 ≤ M := hblk
            calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
              _ = (blk + 1) * B := by ring
              _ ≤ M * B := Nat.mul_le_mul_right B h1
          have hltMB : blk * B + off < M * B := hLmul ▸ hlt
          simp only [rowW, slotAt, hlt, hltMB, ↓reduceDIte, eqL]
          rfl
        change lo ⟨blk, hb⟩ ≤ ∑ p ∈ Finset.range B, (x (rowW (blk * B + p))).toNat
        rw [hsum_eq]
        refine row_base_sat_ge (col := col) (hi := hi) ⟨blk, hb⟩ (hrow ⟨blk, hb⟩).1 x ?_
        intro T hT1 hT2
        exact hx _ (Or.inl (Or.inl (Or.inl (by simp only [Hbase, hb, ↓reduceDIte]; exact ⟨T, hT1, hT2, rfl⟩))))
      · simp only [qLo, hb, ↓reduceDIte]
        exact Nat.zero_le _
    have hd := derive_fullCNF (O := {st (k_b + 1)}) hHblkSub hSblkB hHblkS hOutS
      (unitTrue_dependsOn _) hsem
    refine derivable_mono hd Set.Subset.rfl le_rfl hSblkc ?_ Set.Subset.rfl
    dsimp only [L_leaf]
    exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by simp; omega))
  have hLeafCol : ∀ blk < M, ∀ Gq : List (ℕ × ℕ), G3 <+: Gq → ∀ st : ℕ → ℕ,
      HasCmp n Gq o1 false (k_b + 1) (qHi blk) (fun i => Ybits k_b blk i) st →
      Derivable (baseF ∪ allGateClauses n Gq ∪ constCNF z0 o1) (n + Gq.length) W_leaf L_leaf
        (unitTrueCNF (st (k_b + 1))) := by
    intro blk hblk Gq p3q st hcmp
    have p0q : G0 <+: Gq := p02.trans (p23.trans p3q)
    have p2q : G2 <+: Gq := p23.trans p3q
    have hsubCT := counterTree_subtree (hasCounterTree_mono p2q ctY) blk hblk
    obtain ⟨Wc, Hc, hWcc, hWcB, hbcW, hHFc, hHSc, hvalc⟩ := counterTree_wireSet hsubCT
    obtain ⟨Wp, Hp, hWpc, hWpB, hstW, hHFp, hHSp, hvalp⟩ := cmp_wireSet hcmp
    have hleafSub : (Finset.range B).image (fun p => colW (blk * B + p)) ⊆
        (if hb : blk < h then (cols ⟨blk, hb⟩).image Fin.val else ∅) ∪ {z0} := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨off, hoff, rfl⟩
      rw [Finset.mem_range] at hoff
      have hlt : blk * B + off < L := by
        rw [hLmul]
        have h1 : blk + 1 ≤ M := hblk
        calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
          _ = (blk + 1) * B := by ring
          _ ≤ M * B := Nat.mul_le_mul_right B h1
      simp only [colW, hlt, ↓reduceDIte]
      by_cases hb : blk < h
      · simp only [hb, ↓reduceDIte]
        cases hslot : colSlot (eqL ⟨blk * B + off, hlt⟩) with
        | none => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        | some e =>
          have hce : col e = ⟨blk, hb⟩ := hmemC blk hb off hoff e (by simpa [eqL] using hslot)
          exact Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hce⟩, rfl⟩)
      · have hnone : colSlot (eqL ⟨blk * B + off, hlt⟩) = none :=
          hnoneC blk (by omega) hblk off hoff
        rw [hnone]
        exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    let BaseV : Finset ℕ := if hb : blk < h then (cols ⟨blk, hb⟩).image Fin.val else ∅
    let Sblk : Finset ℕ := BaseV ∪ {z0, o1} ∪ Wc ∪ Wp
    have hBaseVc : BaseV.card ≤ b := by
      dsimp only [BaseV]; split_ifs with hb
      · exact le_trans Finset.card_image_le (hcol ⟨blk, hb⟩).2
      · simp
    have hSblkc : Sblk.card ≤ W_leaf := by
      have hzo : ({z0, o1} : Finset ℕ).card ≤ 2 := by
        have := Finset.card_insert_le z0 {o1}; simp only [Finset.card_singleton] at *; omega
      dsimp only [Sblk]
      have := Finset.card_union_le (BaseV ∪ {z0, o1} ∪ Wc) Wp
      have := Finset.card_union_le (BaseV ∪ {z0, o1}) Wc
      have := Finset.card_union_le BaseV {z0, o1}
      dsimp only [W_leaf, B]
      omega
    have hSblkB : ∀ v ∈ Sblk, v < n + Gq.length := by
      intro v hv
      simp only [Sblk, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with ((hB1 | (rfl | rfl)) | hW1) | hW2
      · dsimp only [BaseV] at hB1; split_ifs at hB1 with hb
        · rcases Finset.mem_image.mp hB1 with ⟨e, -, rfl⟩
          exact Nat.lt_of_lt_of_le e.isLt (Nat.le_add_right _ _)
        · exact absurd hB1 (Finset.notMem_empty _)
      · have := p0q.length_le; omega
      · have := p0q.length_le; omega
      · exact hWcB v hW1
      · exact hWpB v hW2
    let Hbase : Set (Clause ℕ) :=
      if hb : blk < h then
        {D | ∃ T : Finset (Fin n), T ⊆ cols ⟨blk, hb⟩ ∧
          T.card = hi ⟨blk, hb⟩ + 1 ∧
          D = T.image (fun e => (e.val, false))}
      else ∅
    let Hblk : Set (Clause ℕ) := Hbase ∪ Hc ∪ Hp ∪ constCNF z0 o1
    have hHblkSub : Hblk ⊆ baseF ∪ allGateClauses n Gq ∪ constCNF z0 o1 := by
      intro C hC
      rcases hC with ((h1 | h2) | h3) | h4
      · apply Or.inl; apply Or.inl
        dsimp only [Hbase] at h1; split_ifs at h1 with hb
        · rcases h1 with ⟨T, hT1, hT2, hT3⟩
          exact Or.inr ⟨⟨blk, hb⟩, T, hT1, hT2, hT3⟩
        · exact absurd h1 (Set.notMem_empty _)
      · exact Or.inl (Or.inr (hHFc h2))
      · exact Or.inl (Or.inr (hHFp h3))
      · exact Or.inr h4
    have hHblkS : ∀ C ∈ Hblk, ∀ l ∈ C, l.1 ∈ Sblk := by
      intro C hC l hl
      rcases hC with ((h1 | h2) | h3) | h4
      · dsimp only [Hbase] at h1; split_ifs at h1 with hb
        · rcases h1 with ⟨T, hTC, -, rfl⟩
          rcases Finset.mem_image.mp hl with ⟨e, heT, rfl⟩
          apply Finset.mem_union_left; apply Finset.mem_union_left; apply Finset.mem_union_left
          simp only [BaseV, hb, ↓reduceDIte]
          exact Finset.mem_image.mpr ⟨e, hTC heT, rfl⟩
        · exact absurd h1 (Set.notMem_empty _)
      · have hv := hHSc C h2 l hl
        rcases Finset.mem_union.mp hv with hlv | hzw
        · have hv' := hleafSub hlv
          rcases Finset.mem_union.mp hv' with hbv | hz'
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hbv))
          · simp only [Finset.mem_singleton] at hz'
            exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
        · rcases Finset.mem_insert.mp hzw with hz' | hwc
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hwc)
      · have hv := hHSp C h3 l hl
        rcases Finset.mem_union.mp hv with him | how
        · rcases Finset.mem_image.mp him with ⟨i, hi, hiY⟩
          rw [Finset.mem_range] at hi
          have hmem := hbcW i (by omega)
          simp only [Nat.sub_self, Nat.pow_zero, mul_one, add_zero] at hmem
          rw [← hiY]
          rcases Finset.mem_union.mp hmem with hlv | hzw
          · have hv' := hleafSub hlv
            rcases Finset.mem_union.mp hv' with hbv | hz'
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hbv))
            · simp only [Finset.mem_singleton] at hz'
              exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
          · rcases Finset.mem_insert.mp hzw with hz' | hwc
            · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [hz'])))
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hwc)
        · rcases Finset.mem_insert.mp how with ho' | hwp
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [ho'])))
          · exact Finset.mem_union_right _ hwp
      · rcases h4 with hz' | ho'
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_singleton] at hv; simp [Sblk, hv]) C hz' l hl
        · exact fullCNF_vars_subset (fun v hv => by
            simp only [Finset.mem_singleton] at hv; simp [Sblk, hv]) C ho' l hl
    have hOutS : ({st (k_b + 1)} : Finset ℕ) ⊆ Sblk := by
      intro v hv; simp only [Finset.mem_singleton] at hv; rw [hv]
      rcases Finset.mem_insert.mp hstW with ho' | hwp
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (by simp [ho'])))
      · exact Finset.mem_union_right _ hwp
    have hsem : ∀ x : ℕ → Bool, (∀ C ∈ Hblk, ClauseSat x C) → x (st (k_b + 1)) = true := by
      intro x hx
      have ez : x z0 = false := (fullCNF_sat_iff (fun a b hab => by rw [hab z0 (by simp)]) x).mp
        (fun C hC => hx C (Or.inr (Or.inl hC)))
      have eo : x o1 = true := (fullCNF_sat_iff (fun a b hab => by rw [hab o1 (by simp)]) x).mp
        (fun C hC => hx C (Or.inr (Or.inr hC)))
      have hvc := hvalc x ez (fun C hC => hx C (Or.inl (Or.inl (Or.inr hC))))
      simp only [Nat.sub_self, Nat.pow_zero, mul_one, add_zero] at hvc
      have hvp := hvalp x eo (fun C hC => hx C (Or.inl (Or.inr hC)))
      simp only [Bool.false_eq_true, ↓reduceIte] at hvp
      rw [hvp, hvc]
      have hqlt : qHi blk < 2 ^ (k_b + 1) := by
        have := hqHi blk hblk; rw [Nat.pow_succ]; dsimp only [B] at this; omega
      rw [Nat.mod_eq_of_lt hqlt]
      by_cases hb : blk < h
      · simp only [qHi, hb, ↓reduceDIte]
        have hsum_eq : ∑ p ∈ Finset.range B, (x (colW (blk * B + p))).toNat =
            ∑ e ∈ cols ⟨blk, hb⟩, (x e.val).toNat := by
          have hs := hsumC blk hb x z0 ez
          rw [← hs]
          refine Finset.sum_congr rfl (fun off hoff => ?_)
          rw [Finset.mem_range] at hoff
          have hlt : blk * B + off < L := by
            rw [hLmul]
            have h1 : blk + 1 ≤ M := hblk
            calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
              _ = (blk + 1) * B := by ring
              _ ≤ M * B := Nat.mul_le_mul_right B h1
          have hltMB : blk * B + off < M * B := hLmul ▸ hlt
          simp only [colW, slotAt, hlt, hltMB, ↓reduceDIte, eqL]
          rfl
        change ∑ p ∈ Finset.range B, (x (colW (blk * B + p))).toNat ≤ hi ⟨blk, hb⟩
        rw [hsum_eq]
        refine col_base_sat_le (row := row) (lo := lo) ⟨blk, hb⟩ x ?_
        intro T hT1 hT2
        exact hx _ (Or.inl (Or.inl (Or.inl (by simp only [Hbase, hb, ↓reduceDIte]; exact ⟨T, hT1, hT2, rfl⟩))))
      · simp only [qHi, hb, ↓reduceDIte]
        have hsum0 : ∑ p ∈ Finset.range B, (x (colW (blk * B + p))).toNat = 0 := by
          refine Finset.sum_eq_zero (fun off hoff => ?_)
          rw [Finset.mem_range] at hoff
          have hlt : blk * B + off < L := by
            rw [hLmul]
            have h1 : blk + 1 ≤ M := hblk
            calc blk * B + off < blk * B + B := Nat.add_lt_add_left hoff _
              _ = (blk + 1) * B := by ring
              _ ≤ M * B := Nat.mul_le_mul_right B h1
          have hnone : colSlot (eqL ⟨blk * B + off, hlt⟩) = none :=
            hnoneC blk (by omega) hblk off hoff
          simp only [colW, hlt, ↓reduceDIte, hnone, ez, Bool.toNat_false]
        exact le_of_eq hsum0
    have hd := derive_fullCNF (O := {st (k_b + 1)}) hHblkSub hSblkB hHblkS hOutS
      (unitTrue_dependsOn _) hsem
    refine derivable_mono hd Set.Subset.rfl le_rfl hSblkc ?_ Set.Subset.rfl
    dsimp only [L_leaf]
    exact Nat.mul_le_mul_left 3 (Nat.pow_le_pow_right (by omega) (by simp; omega))
  have p03 : G0 <+: G3 := p02.trans p23
  have p13 : G1 <+: G3 := p12.trans p23
  obtain ⟨G4, stS, p34, lG4, vG4, hcS, hstS, derRowQ⟩ :=
    build_quota_tree baseF z0 o1 k_b W_leaf L_leaf true (by dsimp only [W_leaf]; omega) r qLo
      vG3 (by have := p03.length_le; omega) (by have := p03.length_le; omega)
      (hasCounterTree_mono p13 ctX)
      (fun t ht pos hpos i hi => by have := hblX t ht pos hpos i hi; have := p13.length_le; omega)
      hqLo hLeafRow
  obtain ⟨G5, stT, p45, lG5, vG5, hcT, hstT, derColQ⟩ :=
    build_quota_tree baseF z0 o1 k_b W_leaf L_leaf false (by dsimp only [W_leaf]; omega) r qHi
      vG4 (by have := (p03.trans p34).length_le; omega) (by have := (p03.trans p34).length_le; omega)
      (hasCounterTree_mono (p23.trans p34) ctY)
      (fun t ht pos hpos i hi => by have := hblY t ht pos hpos i hi; have := (p23.trans p34).length_le; omega)
      hqHi (fun blk hblk Gq p4q => hLeafCol blk hblk Gq (p34.trans p4q))
  have p05 : G0 <+: G5 := p03.trans (p34.trans p45)
  have p35 : G3 <+: G5 := p34.trans p45
  have hLOeq : ∑ blk ∈ Finset.range M, qLo blk = ∑ i : Fin m, lo i := by
    have hsplit : M = m + (M - m) := by omega
    conv_lhs => rw [hsplit]
    rw [Finset.sum_range_add]
    have hz : ∑ i ∈ Finset.range (M - m), qLo (m + i) = 0 :=
      Finset.sum_eq_zero (fun i _ => by dsimp only [qLo]; split_ifs with h1; omega; rfl)
    rw [hz, add_zero]
    rw [← Fin.sum_univ_eq_sum_range (fun i => qLo i)]
    refine Finset.sum_congr rfl (fun i _ => by simp [qLo, i.isLt])
  have hHIeq : ∑ blk ∈ Finset.range M, qHi blk = ∑ j : Fin h, hi j := by
    have hsplit : M = h + (M - h) := by omega
    conv_lhs => rw [hsplit]
    rw [Finset.sum_range_add]
    have hz : ∑ i ∈ Finset.range (M - h), qHi (h + i) = 0 :=
      Finset.sum_eq_zero (fun i _ => by dsimp only [qHi]; split_ifs with h1; omega; rfl)
    rw [hz, add_zero]
    rw [← Fin.sum_univ_eq_sum_range (fun j => qHi j)]
    refine Finset.sum_congr rfl (fun j _ => by simp [qHi, j.isLt])
  have hLOlt : ∑ blk ∈ Finset.range M, qLo blk < 2 ^ (D + 1) := by
    have hle : ∑ blk ∈ Finset.range M, qLo blk ≤ M * B := by
      calc ∑ blk ∈ Finset.range M, qLo blk ≤ ∑ _ ∈ Finset.range M, B :=
            Finset.sum_le_sum (fun blk hb => hqLo blk (Finset.mem_range.mp hb))
        _ = M * B := by simp
    rw [← hLmul] at hle
    rw [Nat.pow_succ]; dsimp only [L] at hle; omega
  have hHL : ∑ blk ∈ Finset.range M, qHi blk < ∑ blk ∈ Finset.range M, qLo blk := by
    rw [hLOeq, hHIeq]; exact hquota
  have hContra := root_contradiction hHL hLOlt (hasCmp_mono p45 hcS) hcT
    (fun i hi => by have := hstS i hi; have := p45.length_le; omega) hstT
  let Fall := baseF ∪ allGateClauses n G5
  have derC : Derivable Fall (n + G5.length) W_leaf (2 * (3 * 2 ^ 5)) (constCNF z0 o1) :=
    derivable_mono (derive_consts (hasConsts_mono p05 hcG0)) Set.subset_union_right le_rfl
      (by dsimp only [W_leaf]; omega) le_rfl Set.Subset.rfl
  have derPerm5 : Derivable (Fall ∪ constCNF z0 o1) (n + G5.length) W_leaf (K_eq * D * L)
      (⋃ i ∈ Finset.range (D + 1), BitEqCNF (Xbits D 0 i) (Ybits D 0 i)) :=
    derivable_mono derPerm
      (fun C hC => Or.inl (Or.inr (allGateClauses_mono p35 hC)))
      (by have := p35.length_le; omega) (by dsimp only [W_leaf]; omega) le_rfl Set.Subset.rfl
  have derRow5 : Derivable (Fall ∪ constCNF z0 o1) (n + G5.length) W_leaf
      ((L_leaf + 2 * (k_b + 4) * K_qstep) * M) (unitTrueCNF (stS (D + 1))) :=
    derivable_mono derRowQ
      (fun C hC => by rcases hC with (h | h) | h; exact Or.inl (Or.inl h); exact Or.inl (Or.inr (allGateClauses_mono p45 h)); exact Or.inr h)
      (by have := p45.length_le; omega) le_rfl (Nat.sub_le _ _) Set.Subset.rfl
  have derCol5 : Derivable (Fall ∪ constCNF z0 o1) (n + G5.length) W_leaf
      ((L_leaf + 2 * (k_b + 4) * K_qstep) * M) (unitTrueCNF (stT (D + 1))) :=
    derivable_mono derColQ Set.Subset.rfl le_rfl le_rfl (Nat.sub_le _ _) Set.Subset.rfl
  have derInputs := derivable_trans_only derC (derivable_union (derivable_union derPerm5 derRow5) derCol5)
  have hContra' : Derivable (Fall ∪
      (((⋃ i ∈ Finset.range (D + 1), BitEqCNF (Xbits D 0 i) (Ybits D 0 i)) ∪
        unitTrueCNF (stS (D + 1))) ∪ unitTrueCNF (stT (D + 1))))
      (n + G5.length) W_leaf ((D + 2) * 2 ^ 13) {∅} :=
    derivable_mono hContra
      (fun C hC => by
        rcases hC with ((h | h) | h) | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inl (Or.inr h))
        · exact Or.inr (Or.inr h))
      le_rfl (by dsimp only [W_leaf]; omega) le_rfl Set.Subset.rfl
  have derBot := derivable_trans_only derInputs hContra'
  obtain ⟨πw, hwd, hπw_len, hπw_wb, hπw_emp⟩ := derBot
  obtain ⟨πnat, hdn, hπn_len, hcov, hsub⟩ := elim_weakening hwd
  have hemp_nat : (∅ : Clause ℕ) ∈ πnat := by
    obtain ⟨E, hE, hEsub⟩ := hcov ∅ (hπw_emp ∅ rfl)
    rwa [Finset.subset_empty.mp hEsub] at hE
  have hπn_wb : ∀ D ∈ πnat, D.card ≤ W_leaf ∧ ClauseVarsLt (n + G5.length) D := by
    intro E hE
    obtain ⟨E', hE', hEE'⟩ := hsub E hE
    have hwb := hπw_wb E' hE'
    exact ⟨le_trans (Finset.card_le_card hEE') hwb.1, fun l hl => hwb.2 l (hEE' hl)⟩
  let s := G5.length
  let toVar : ℕ → Fin n ⊕ Fin s := fun w =>
    if h1 : w < n then Sum.inl ⟨w, h1⟩
    else if h2 : w - n < s then Sum.inr ⟨w - n, h2⟩
    else Sum.inl ⟨0, hn⟩
  have htoVar_inj : ∀ a b, a < n + s → b < n + s → toVar a = toVar b → a = b := by
    intro a b ha hb heq
    dsimp only [toVar] at heq
    by_cases ha1 : a < n
    · by_cases hb1 : b < n
      · simp only [ha1, hb1, ↓reduceDIte] at heq
        exact congrArg Fin.val (Sum.inl.inj heq)
      · have hb2 : b - n < s := by omega
        simp only [ha1, hb1, hb2, ↓reduceDIte] at heq
        cases heq
    · have ha2 : a - n < s := by omega
      by_cases hb1 : b < n
      · simp only [ha1, ha2, hb1, ↓reduceDIte] at heq
        cases heq
      · have hb2 : b - n < s := by omega
        simp only [ha1, ha2, hb1, hb2, ↓reduceDIte] at heq
        have hsub : a - n = b - n := congrArg Fin.val (Sum.inr.inj heq)
        omega
  let first : Fin s → Fin n ⊕ Fin s := fun i => toVar G5[i.val].1
  let second : Fin s → Fin n ⊕ Fin s := fun i => toVar G5[i.val].2
  refine ⟨s, first, second, ?_, ?_⟩
  · intro i
    have hv := vG5 i.val i.isLt
    constructor
    · dsimp only [first, toVar]
      split_ifs with h1 h2
      · trivial
      · dsimp only [Sum.elim]; omega
      · omega
    · dsimp only [second, toVar]
      split_ifs with h1 h2
      · trivial
      · dsimp only [Sum.elim]; omega
      · omega
  · let π : List (Clause (Fin n ⊕ Fin s)) := πnat.map (mapClause toVar)
    have hFmap : ∀ E ∈ Fall, ClauseVarsLt (n + s) E →
        mapClause toVar E ∈
          ({E' | (∃ (i : Fin m) (T : Finset (Fin n)), T ⊆ rows i ∧
              T.card + lo i = (rows i).card + 1 ∧ E' = T.image (fun e => ((Sum.inl e : Fin n ⊕ Fin s), true))) ∨
            (∃ (j : Fin h) (T : Finset (Fin n)), T ⊆ cols j ∧
              T.card = hi j + 1 ∧ E' = T.image (fun e => ((Sum.inl e : Fin n ⊕ Fin s), false)))} ∪
           {E' | ∃ i : Fin s,
              E' = {((Sum.inr i : Fin n ⊕ Fin s), false), (first i, false), (second i, false)} ∨
              E' = {((Sum.inr i : Fin n ⊕ Fin s), true), (first i, true)} ∨
              E' = {((Sum.inr i : Fin n ⊕ Fin s), true), (second i, true)}}) := by
      intro E hE _
      rcases hE with hbase | hgate
      · apply Or.inl
        rcases hbase with ⟨i, T, hT1, hT2, rfl⟩ | ⟨j, T, hT1, hT2, rfl⟩
        · refine Or.inl ⟨i, T, hT1, hT2, ?_⟩
          ext l
          simp only [mapClause, Finset.mem_image]
          constructor
          · rintro ⟨⟨w, b⟩, ⟨e, heT, heq⟩, rfl⟩
            rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact ⟨e, heT, by simp [toVar, e.isLt]⟩
          · rintro ⟨e, heT, rfl⟩
            exact ⟨(e.val, true), ⟨e, heT, rfl⟩, by simp [toVar, e.isLt]⟩
        · refine Or.inr ⟨j, T, hT1, hT2, ?_⟩
          ext l
          simp only [mapClause, Finset.mem_image]
          constructor
          · rintro ⟨⟨w, b⟩, ⟨e, heT, heq⟩, rfl⟩
            rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact ⟨e, heT, by simp [toVar, e.isLt]⟩
          · rintro ⟨e, heT, rfl⟩
            exact ⟨(e.val, false), ⟨e, heT, rfl⟩, by simp [toVar, e.isLt]⟩
      · apply Or.inr
        rcases hgate with ⟨i, hD⟩
        have hzi : toVar (n + i.val) = Sum.inr i := by
          dsimp only [toVar]
          have h1 : ¬ (n + i.val < n) := by omega
          have h2 : n + i.val - n < s := by rw [Nat.add_sub_cancel_left]; exact i.isLt
          simp only [h1, ↓reduceDIte, h2]
          congr 1; apply Fin.ext; simp
        refine ⟨i, ?_⟩
        rcases hD with rfl | rfl | rfl
        · left; simp [mapClause, hzi, first, second]
        · right; left; simp [mapClause, hzi, first]
        · right; right; simp [mapClause, hzi, second]
    have hderiv : IsDerivation _ π :=
      map_isDerivation htoVar_inj hFmap hdn (fun E hE => (hπn_wb E hE).2)
    have hemp : (∅ : Clause (Fin n ⊕ Fin s)) ∈ π := by
      have : mapClause toVar ∅ = ∅ := by simp [mapClause]
      rw [← this]
      exact List.mem_map_of_mem hemp_nat
    refine ⟨π, ⟨hderiv, hemp⟩, ?_, ?_⟩
    · have hM_le : M ≤ 2 * N := by
        have hpos : 0 < max m h := lt_of_lt_of_le hm (le_max_left m h)
        have h1 := two_pow_clog_le hpos
        have h2 : max m h ≤ N := by dsimp only [N]; omega
        dsimp only [M, r]; omega
      have hr_le : r ≤ Nat.clog 2 N :=
        Nat.clog_mono_right 2 (by dsimp only [N]; omega)
      have hs_le : s ≤ 3 + 36 * L + 72 * D * L + 12 * (k_b + 3) * M := by
        have h1 : G1.length ≤ G0.length + 18 * L := by omega
        have h2 : G2.length ≤ G1.length + 18 * L := by omega
        have h3 : G3.length ≤ G2.length + 72 * D * L := lG3
        have h4 : G4.length ≤ G3.length + 6 * (k_b + 3) * M := by dsimp only [M]; omega
        have h5 : G5.length ≤ G4.length + 6 * (k_b + 3) * M := by dsimp only [M]; omega
        have h12 : 12 * (k_b + 3) * M = 6 * (k_b + 3) * M + 6 * (k_b + 3) * M := by ring
        dsimp only [s]; omega
      have hπ_le : π.length ≤ 2 * (3 * 2 ^ 5) + K_eq * D * L +
          2 * (L_leaf + 2 * (k_b + 4) * K_qstep) * M + (D + 2) * 2 ^ 13 := by
        have hlen : π.length = πnat.length := List.length_map _
        rw [hlen]
        have h2M : 2 * (L_leaf + 2 * (k_b + 4) * K_qstep) * M =
            (L_leaf + 2 * (k_b + 4) * K_qstep) * M + (L_leaf + 2 * (k_b + 4) * K_qstep) * M := by ring
        have := le_trans hπn_len hπw_len
        omega
      exact final_size_bound hBpos (by dsimp only [N]; omega) hLmul rfl hM_le hr_le
        (le_max_right _ _) hs_le hπ_le
    · intro E hE
      rcases List.mem_map.mp hE with ⟨E', hE', rfl⟩
      exact le_trans Finset.card_image_le (le_trans (hπn_wb E' hE').1 (le_max_left _ _))

end MainAssembly

end PEqualNP.Outside.L_pcx_373

theorem PEqualNP.Outside.L_pcx_373 : ∀ b : ℕ, ∃ C : ℕ, 0 < C ∧ ∀ (n m h : ℕ) (row : Fin n → Fin m) (col : Fin n → Fin h)
    (lo : Fin m → ℕ) (hi : Fin h → ℕ),
  let rows := fun i : Fin m => Finset.univ.filter (fun e : Fin n => row e = i)
  let cols := fun j : Fin h => Finset.univ.filter (fun e : Fin n => col e = j)
  (∀ i, lo i ≤ (rows i).card ∧ (rows i).card ≤ b) →
  (∀ j, hi j ≤ (cols j).card ∧ (cols j).card ≤ b) →
  (∑ j : Fin h, hi j) < (∑ i : Fin m, lo i) →
  let N := n + m + h + 1
  ∃ (s : ℕ) (first second : Fin s → Fin n ⊕ Fin s),
    let V := Fin n ⊕ Fin s
    let earlier := fun i : Fin s =>
      Sum.elim (fun _ : Fin n => True) (fun j : Fin s => j.val < i.val)
    let literals := fun (T : Finset (Fin n)) (sign : Bool) =>
      T.image (fun e => ((Sum.inl e : V), sign))
    let base : Set (PEqualNP.ProofComplexity.Clause V) := {D |
      (∃ (i : Fin m) (T : Finset (Fin n)), T ⊆ rows i ∧
        T.card + lo i = (rows i).card + 1 ∧ D = literals T true) ∨
      (∃ (j : Fin h) (T : Finset (Fin n)), T ⊆ cols j ∧
        T.card = hi j + 1 ∧ D = literals T false)}
    let gates : Set (PEqualNP.ProofComplexity.Clause V) := {D |
      ∃ i : Fin s, D = {((Sum.inr i : V), false), (first i, false), (second i, false)} ∨
        D = {((Sum.inr i : V), true), (first i, true)} ∨
        D = {((Sum.inr i : V), true), (second i, true)}}
    (∀ i, earlier i (first i) ∧ earlier i (second i)) ∧
    ∃ π : List (PEqualNP.ProofComplexity.Clause V),
      PEqualNP.ProofComplexity.IsRefutation (base ∪ gates) π ∧
      s + π.length ≤ C * N * (1 + Nat.clog 2 N) ∧ ∀ D ∈ π, D.card ≤ C :=
  PEqualNP.Outside.L_pcx_373.main_proof
