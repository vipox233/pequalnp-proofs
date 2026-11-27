import Mathlib
import PEqualNP.Defs

-- Map every line termwise: a term T goes to T.image project; widths can only shrink.
-- Axiom: the target clause line, then one weakening to the image (each literal of D forces
-- a projected literal of C). Cut and and-introduction: the target rule gives a subset of the
-- image (collisions only merge terms), then one subset weakening; weakening maps to weakening.

namespace PEqualNP.Outside.L_pcx_203_aux

open PEqualNP.ProofComplexity

variable {V W : Type} [DecidableEq V] [DecidableEq W]

abbrev img (project : LinEq V → LinEq W) (L : LinKLine V) : LinKLine W :=
  L.image (fun T => T.image project)

theorem width_img (project : LinEq V → LinEq W) {k : ℕ} {L : LinKLine V}
    (h : ∀ T ∈ L, T.card ≤ k) : ∀ T ∈ img project L, T.card ≤ k := by
  intro T hT
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.1 hT
  exact Finset.card_image_le.trans (h S hS)

theorem weak_sub {L M : LinKLine W} (h : L ⊆ M) : IsLinKWeakening L M :=
  fun T hT => Or.inl ⟨T, h hT, fun _ ha => ha⟩

theorem termSat_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) (a : W → Bool)
    (T : LinTerm V) : LinTermSat a (T.image project) ↔ LinTermSat (extend a) T := by
  constructor
  · intro h e he
    exact (hsat a e).1 (h _ (Finset.mem_image_of_mem _ he))
  · intro h q hq
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hq
    exact (hsat a e).2 (h e he)

theorem sat_single (a : V → Bool) (v : V) (s : Bool) :
    LinEqSat a (({v} : Finset V), s) ↔ a v = s := by
  cases h : a v <;> cases s <;> simp [LinEqSat, h, Finset.filter_singleton]

theorem cut_img (project : LinEq V → LinEq W)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e)) {C D R : LinKLine V}
    (h : IsLinKCut C D R) :
    ∃ R', IsLinKCut (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T, hT, hD, rfl⟩ := h
  refine ⟨(img project C).erase (T.image project) ∪ (img project D \
    (T.image project).image (fun e => ({negLinEq e} : LinTerm W))),
    ⟨T.image project, Finset.mem_image_of_mem _ hT, ?_, rfl⟩, ?_⟩
  · intro e he
    obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.1 he
    have h1 : ({negLinEq e0} : LinTerm V).image project = {negLinEq (project e0)} := by
      rw [Finset.image_singleton, hneg]
    rw [← h1]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) (hD e0 he0)
  · intro S hS
    rcases Finset.mem_union.1 hS with h1 | h1
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩))
    · obtain ⟨hS, hn⟩ := Finset.mem_sdiff.1 h1
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      refine Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hU, ?_⟩))
      intro hU'
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 hU'
      apply hn
      refine Finset.mem_image.2 ⟨project e, Finset.mem_image_of_mem _ he, ?_⟩
      rw [Finset.image_singleton, hneg]

theorem and_img (project : LinEq V → LinEq W) {C D R : LinKLine V}
    (h : IsLinKAndIntro C D R) :
    ∃ R', IsLinKAndIntro (img project C) (img project D) R' ∧ R' ⊆ img project R := by
  obtain ⟨T₁, T₂, h1, h2, rfl⟩ := h
  refine ⟨((img project C).erase (T₁.image project) ∪ (img project D).erase (T₂.image project))
    ∪ {T₁.image project ∪ T₂.image project},
    ⟨_, _, Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, rfl⟩, ?_⟩
  intro S hS
  rcases Finset.mem_union.1 hS with hS | hS
  · rcases Finset.mem_union.1 hS with hS | hS
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₁ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
    · obtain ⟨hne, hS⟩ := Finset.mem_erase.1 hS
      obtain ⟨U, hU, rfl⟩ := Finset.mem_image.1 hS
      have hUT : U ≠ T₂ := by rintro rfl; exact hne rfl
      exact Finset.mem_image_of_mem _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hUT, hU⟩)))
  · rw [Finset.mem_singleton.1 hS, ← Finset.image_union]
    exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))

theorem weak_img (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {L M : LinKLine V}
    (h : IsLinKWeakening L M) : IsLinKWeakening (img project L) (img project M) := by
  intro T' hT'
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.1 hT'
  rcases h T hT with ⟨S, hS, hTS⟩ | hq
  · exact Or.inl ⟨S.image project, Finset.mem_image_of_mem _ hS, fun a ha =>
      (termSat_img project extend hsat a S).2 (hTS _ ((termSat_img project extend hsat a T).1 ha))⟩
  · right
    intro a ha
    obtain ⟨q, hq1, hq2⟩ := hq _ ((termSat_img project extend hsat a T).1 ha)
    refine ⟨project q, ?_, (hsat a q).2 hq2⟩
    rw [show ({project q} : LinTerm W) = ({q} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
    exact Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) hq1

theorem ax_weak (project : LinEq V → LinEq W) (extend : (W → Bool) → V → Bool)
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e) {C : Clause V}
    {D : Clause W} (hCD : ∀ a, ClauseSat a D → ClauseSat (extend a) C) :
    IsLinKWeakening (linKOfClause D) (img project (linKOfClause C)) := by
  intro T hT
  right
  intro a ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hT
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hq
  have hla : a l.1 = l.2 := (sat_single a l.1 l.2).1 (ha _ (Finset.mem_singleton_self _))
  obtain ⟨l', hl', h'⟩ := hCD a ⟨l, hl, hla⟩
  refine ⟨project (({l'.1} : Finset V), l'.2), ?_,
    (hsat a _).2 ((sat_single (extend a) l'.1 l'.2).2 h')⟩
  rw [show ({project (({l'.1} : Finset V), l'.2)} : LinTerm W) =
      ({(({l'.1} : Finset V), l'.2)} : LinTerm V).image project from
      (Finset.image_singleton _ _).symm]
  refine Finset.mem_image_of_mem (fun T : LinTerm V => T.image project) ?_
  exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hl')

theorem width_clause {k : ℕ} (hk : 1 ≤ k) (D : Clause W) :
    ∀ T ∈ linKOfClause D, T.card ≤ k := by
  intro T hT
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hT
  rw [Finset.card_singleton]; exact hk

theorem main (k : ℕ) (F : Set (Clause V)) (H : Set (Clause W))
    (extend : (W → Bool) → V → Bool) (project : LinEq V → LinEq W) (hk : 1 ≤ k)
    (hneg : ∀ e, project (negLinEq e) = negLinEq (project e))
    (hsat : ∀ a e, LinEqSat a (project e) ↔ LinEqSat (extend a) e)
    (hax : ∀ C ∈ F, ∃ D ∈ H, ∀ a, ClauseSat a D → ClauseSat (extend a) C)
    (π : List (LinKLine V))
    (h : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) π) :
    ∃ τ : List (LinKLine W),
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' H) τ ∧
      τ.length ≤ 2 * π.length ∧ ∀ L ∈ π, img project L ∈ τ := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | @ax π C _ hC hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨C0, hC0, rfl⟩ := hC
    obtain ⟨D, hD, hCD⟩ := hax C0 hC0
    refine ⟨img project (linKOfClause C0) :: linKOfClause D :: τ,
      .weak (.ax hτ ⟨D, hD, rfl⟩ (width_clause hk D)) (List.mem_cons.2 (Or.inl rfl))
        (ax_weak project extend hsat hCD) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @cut π C D R _ hC hD hcut hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨R', hR', hsub⟩ := cut_img project hneg hcut
    refine ⟨img project R :: R' :: τ,
      .weak (.cut hτ (hm _ hC) (hm _ hD) hR' (fun T hT => width_img project hw T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @andIntro π C D R _ hC hD hand hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    obtain ⟨R', hR', hsub⟩ := and_img project hand
    refine ⟨img project R :: R' :: τ,
      .weak (.andIntro hτ (hm _ hC) (hm _ hD) hR'
        (fun T hT => width_img project hw T (hsub hT)))
        (List.mem_cons.2 (Or.inl rfl)) (weak_sub hsub) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hm L hL))
  | @weak π C D _ hC hW hw ih =>
    obtain ⟨τ, hτ, hl, hm⟩ := ih
    refine ⟨img project D :: τ,
      .weak hτ (hm _ hC) (weak_img project extend hsat hW) (width_img project hw), ?_, ?_⟩
    · simp only [List.length_cons]; omega
    · intro L hL
      rcases List.mem_cons.1 hL with rfl | hL
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (hm L hL)

end PEqualNP.Outside.L_pcx_203_aux

theorem PEqualNP.Outside.L_pcx_203 : ∀ (V W : Type) [DecidableEq V] [DecidableEq W] (k : ℕ)
    (F : Set (PEqualNP.ProofComplexity.Clause V))
    (H : Set (PEqualNP.ProofComplexity.Clause W))
    (extend : (W → Bool) → V → Bool)
    (project : PEqualNP.ProofComplexity.LinEq V → PEqualNP.ProofComplexity.LinEq W),
  1 ≤ k →
  (∀ e, project (PEqualNP.ProofComplexity.negLinEq e) =
    PEqualNP.ProofComplexity.negLinEq (project e)) →
  (∀ a e, PEqualNP.ProofComplexity.LinEqSat a (project e) ↔
    PEqualNP.ProofComplexity.LinEqSat (extend a) e) →
  (∀ C ∈ F, ∃ D ∈ H, ∀ a, PEqualNP.ProofComplexity.ClauseSat a D →
    PEqualNP.ProofComplexity.ClauseSat (extend a) C) →
  ∀ π : List (PEqualNP.ProofComplexity.LinKLine V),
    PEqualNP.ProofComplexity.IsLinKRefutation k F π →
    ∃ τ : List (PEqualNP.ProofComplexity.LinKLine W),
      PEqualNP.ProofComplexity.IsLinKRefutation k H τ ∧ τ.length ≤ 2 * π.length := by
  intro V W _ _ k F H extend project hk hneg hsat hax π hπ
  obtain ⟨τ, hτ, hl, hm⟩ := PEqualNP.Outside.L_pcx_203_aux.main k F H extend project hk hneg
    hsat hax π hπ.1
  have h0 := hm _ hπ.2
  rw [PEqualNP.Outside.L_pcx_203_aux.img, Finset.image_empty] at h0
  exact ⟨τ, ⟨hτ, h0⟩, hl⟩
