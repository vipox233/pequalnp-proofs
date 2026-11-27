import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_325_aux

open PEqualNP.ProofComplexity

abbrev RawT {n : ℕ} (w : Fin n → ℕ) : Type := (i : Fin n) × Fin (w i)
abbrev Fiber {n : ℕ} (w : Fin n → ℕ) (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (z : Fin n × Bool) : Type :=
  {x : Fin (w z.1) → Bool // g z.1 x = z.2}
abbrev Sec {n : ℕ} (w : Fin n → ℕ) (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) : Type :=
  ∀ z : Fin n × Bool, Fiber w g z

def fslots {n : ℕ} (C : Clause (Fin n)) : Finset (Fin n × Bool) :=
  Finset.univ.filter (fun z => (z.1, !z.2) ∈ C)

def blockFn {n : ℕ} (w : Fin n → ℕ) (C : Clause (Fin n)) (x : RawT w → Bool) :
    Clause (RawT w) :=
  ((Finset.univ : Finset (RawT w)).filter (fun j => j.1 ∈ C.image Prod.fst)).image
    (fun j => (j, !(x j)))

def copiesFn {n : ℕ} (w : Fin n → ℕ) (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (C : Clause (Fin n)) : Finset (Clause (RawT w)) :=
  ((Finset.univ : Finset (RawT w → Bool)).filter (fun x =>
    ∀ l ∈ C, g l.1 (fun j => x ⟨l.1, j⟩) ≠ l.2)).image (blockFn w C)

noncomputable def repFn {n : ℕ} (w : Fin n → ℕ) (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (σ : Sec w g) (C : Clause (Fin n)) : Clause (RawT w) :=
  blockFn w C (fun u =>
    if (u.1, false) ∈ C then (σ (u.1, true)).1 u.2
    else (σ (u.1, false)).1 u.2)

lemma bool_ne_iff_eq_not (a b : Bool) : a ≠ b ↔ a = !b := by
  cases a <;> cases b <;> decide

lemma not_taut_unique {n : ℕ} {C : Clause (Fin n)}
    (hnt : ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    {i : Fin n} {b₁ b₂ : Bool} (h1 : (i, b₁) ∈ C) (h2 : (i, b₂) ∈ C) : b₁ = b₂ := by
  cases b₁ <;> cases b₂
  · rfl
  · exact (hnt i ⟨h2, h1⟩).elim
  · exact (hnt i ⟨h1, h2⟩).elim
  · rfl

lemma blockFn_eq_iff {n : ℕ} (w : Fin n → ℕ) (C : Clause (Fin n)) (x y : RawT w → Bool) :
    blockFn w C x = blockFn w C y ↔
      ∀ u : RawT w, u.1 ∈ C.image Prod.fst → x u = y u := by
  constructor
  · intro heq u hu
    have hmem : (u, !(x u)) ∈ blockFn w C y := by
      rw [← heq]
      exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩, rfl⟩
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 hmem
    rcases Prod.mk.inj hv with ⟨rfl, hb⟩
    exact Bool.not_inj hb.symm
  · intro h
    ext p
    simp only [blockFn, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by rw [h u (Finset.mem_image.2 hu)]⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, by rw [h u (Finset.mem_image.2 hu)]⟩

lemma repFn_mem_copies {n : ℕ} (w : Fin n → ℕ) (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    {C : Clause (Fin n)} (hnt : ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) (σ : Sec w g) :
    repFn w g σ C ∈ copiesFn w g C := by
  unfold repFn copiesFn
  refine Finset.mem_image.2 ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro ⟨i, s⟩ hl
  cases s
  · have hfn : (fun j : Fin (w i) =>
        if (i, false) ∈ C then (σ (i, true)).1 j else (σ (i, false)).1 j) = (σ (i, true)).1 := by
      funext j; simp [hl]
    rw [hfn, (σ (i, true)).2]
    intro h; cases h
  · have hnf : (i, false) ∉ C := fun hf => hnt i ⟨hl, hf⟩
    have hfn : (fun j : Fin (w i) =>
        if (i, false) ∈ C then (σ (i, true)).1 j else (σ (i, false)).1 j) = (σ (i, false)).1 := by
      funext j; simp [hnf]
    rw [hfn, (σ (i, false)).2]
    intro h; cases h

lemma repFn_eq_of_agree_fslots {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    {C : Clause (Fin n)} (hnt : ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    {σ₁ σ₂ : Sec w g} (hag : ∀ z ∈ fslots C, σ₁ z = σ₂ z) :
    repFn w g σ₁ C = repFn w g σ₂ C := by
  unfold repFn
  rw [blockFn_eq_iff]
  rintro ⟨i, j⟩ hu
  obtain ⟨⟨i', s⟩, hlC, hi'⟩ := Finset.mem_image.1 hu
  simp only at hi'
  subst hi'
  cases s
  · have hz : (i', true) ∈ fslots C := by simp [fslots, hlC]
    simp only [hlC, ↓reduceIte]
    rw [hag _ hz]
  · have hnf : (i', false) ∉ C := fun hf => hnt i' ⟨hlC, hf⟩
    have hz : (i', false) ∈ fslots C := by simp [fslots, hlC]
    simp only [hnf, ↓reduceIte]
    rw [hag _ hz]

lemma agree_fslots_of_repFn_eq {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    {C : Clause (Fin n)} (hnt : ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    {σ₁ σ₂ : Sec w g} (heq : repFn w g σ₁ C = repFn w g σ₂ C) :
    ∀ z ∈ fslots C, σ₁ z = σ₂ z := by
  unfold repFn at heq
  have hpt := (blockFn_eq_iff w C _ _).1 heq
  intro ⟨i, b⟩ hz
  have hlC : (i, !b) ∈ C := (Finset.mem_filter.1 hz).2
  have hi : i ∈ C.image Prod.fst := Finset.mem_image.2 ⟨(i, !b), hlC, rfl⟩
  apply Subtype.ext
  funext j
  have hj := hpt ⟨i, j⟩ hi
  cases b
  · have hnf : (i, false) ∉ C := fun hf => hnt i ⟨by simpa using hlC, hf⟩
    simpa [hnf] using hj
  · have hf : (i, false) ∈ C := by simpa using hlC
    simpa [hf] using hj

lemma copies_disjoint {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    {C₁ C₂ : Clause (Fin n)}
    (_hnt1 : ∀ i, ¬ ((i, true) ∈ C₁ ∧ (i, false) ∈ C₁))
    (_hnt2 : ∀ i, ¬ ((i, true) ∈ C₂ ∧ (i, false) ∈ C₂))
    (hne : C₁ ≠ C₂) :
    Disjoint (copiesFn w g C₁) (copiesFn w g C₂) := by
  rw [Finset.disjoint_left]
  intro E hE1 hE2
  apply hne
  obtain ⟨x₁, hx₁, rfl⟩ := Finset.mem_image.1 hE1
  obtain ⟨x₂, hx₂, heq⟩ := Finset.mem_image.1 hE2
  have hx1_f := (Finset.mem_filter.1 hx₁).2
  have hx2_f := (Finset.mem_filter.1 hx₂).2
  have hvars : C₁.image Prod.fst = C₂.image Prod.fst := by
    ext i
    constructor
    · intro hi1
      let u : RawT w := ⟨i, ⟨0, hw i⟩⟩
      have hmem : (u, !(x₁ u)) ∈ blockFn w C₂ x₂ := by
        rw [heq]
        exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hi1⟩, rfl⟩
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 hmem
      rcases Prod.mk.inj hveq with ⟨rfl, _⟩
      exact (Finset.mem_filter.1 hv).2
    · intro hi2
      let u : RawT w := ⟨i, ⟨0, hw i⟩⟩
      have hmem : (u, !(x₂ u)) ∈ blockFn w C₁ x₁ := by
        rw [← heq]
        exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hi2⟩, rfl⟩
      obtain ⟨v, hv, hveq⟩ := Finset.mem_image.1 hmem
      rcases Prod.mk.inj hveq with ⟨rfl, _⟩
      exact (Finset.mem_filter.1 hv).2
  have hx_eq : ∀ i ∈ C₁.image Prod.fst, (fun j => x₁ ⟨i, j⟩) = (fun j => x₂ ⟨i, j⟩) := by
    intro i hi
    funext j
    have hmem : (⟨i, j⟩, !(x₁ ⟨i, j⟩)) ∈ blockFn w C₂ x₂ := by
      rw [heq]
      exact Finset.mem_image.2 ⟨⟨i, j⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩
    obtain ⟨v, _, hveq⟩ := Finset.mem_image.1 hmem
    rcases Prod.mk.inj hveq with ⟨rfl, hb⟩
    exact Bool.not_inj hb.symm
  ext ⟨i, s⟩
  constructor
  · intro h1
    have hi1 : i ∈ C₁.image Prod.fst := Finset.mem_image.2 ⟨(i, s), h1, rfl⟩
    have hi2 : i ∈ C₂.image Prod.fst := hvars ▸ hi1
    obtain ⟨⟨i', s'⟩, h2, rfl⟩ := Finset.mem_image.1 hi2
    have hg1 : g i' (fun j => x₁ ⟨i', j⟩) ≠ s := hx1_f (i', s) h1
    have hg2 : g i' (fun j => x₂ ⟨i', j⟩) ≠ s' := hx2_f (i', s') h2
    rw [hx_eq i' hi1] at hg1
    have hs : s = s' := by
      cases hs1 : s <;> cases hs2 : s' <;> cases hgv : g i' (fun j => x₂ ⟨i', j⟩) <;> simp_all
    exact hs ▸ h2
  · intro h2
    have hi2 : i ∈ C₂.image Prod.fst := Finset.mem_image.2 ⟨(i, s), h2, rfl⟩
    have hi1 : i ∈ C₁.image Prod.fst := hvars.symm ▸ hi2
    obtain ⟨⟨i', s'⟩, h1, rfl⟩ := Finset.mem_image.1 hi1
    have hg1 : g i' (fun j => x₁ ⟨i', j⟩) ≠ s' := hx1_f (i', s') h1
    have hg2 : g i' (fun j => x₂ ⟨i', j⟩) ≠ s := hx2_f (i', s) h2
    rw [hx_eq i' hi1] at hg1
    have hs : s = s' := by
      cases hs1 : s <;> cases hs2 : s' <;> cases hgv : g i' (fun j => x₂ ⟨i', j⟩) <;> simp_all
    exact hs ▸ h1

lemma exists_sec_of_mem_copies {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (hg : ∀ i b, ∃ x, g i x = b)
    {C : Clause (Fin n)} (hnt : ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    {E : Clause (RawT w)} (hE : E ∈ copiesFn w g C) :
    ∃ σ : Sec w g, repFn w g σ C = E := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hE
  have hxf := (Finset.mem_filter.1 hx).2
  let σ : Sec w g := fun z =>
    if hz : z ∈ fslots C then
      ⟨fun j => x ⟨z.1, j⟩, by
        have hl : (z.1, !z.2) ∈ C := (Finset.mem_filter.1 hz).2
        have hne := hxf (z.1, !z.2) hl
        cases hz2 : z.2 <;> simp_all⟩
    else
      ⟨Classical.choose (hg z.1 z.2), Classical.choose_spec (hg z.1 z.2)⟩
  refine ⟨σ, ?_⟩
  unfold repFn
  rw [blockFn_eq_iff]
  rintro ⟨i, j⟩ hu
  obtain ⟨⟨i', s⟩, hlC, hi'⟩ := Finset.mem_image.1 hu
  simp only at hi'
  subst hi'
  cases s
  · have hz : (i', true) ∈ fslots C := by simp [fslots, hlC]
    simp only [hlC, ↓reduceIte, σ, hz, ↓reduceDIte]
  · have hnf : (i', false) ∉ C := fun hf => hnt i' ⟨hlC, hf⟩
    have hz : (i', false) ∈ fslots C := by simp [fslots, hlC]
    simp only [hnf, ↓reduceIte, σ, hz, ↓reduceDIte]

lemma sec_fiber_card_mul {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (hg : ∀ i b, ∃ x, g i x = b)
    {C : Clause (Fin n)} (hnt : ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    {E : Clause (RawT w)} (hE : E ∈ copiesFn w g C) :
    ((Finset.univ : Finset (Sec w g)).filter (fun σ => repFn w g σ C = E)).card *
      (copiesFn w g C).card = Fintype.card (Sec w g) := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := exists_sec_of_mem_copies w g hg hnt hE
  let P1 := ∀ z : ↥(fslots C), Fiber w g z.1
  let P2 := ∀ z : {z : Fin n × Bool // z ∉ fslots C}, Fiber w g z.1
  let split : Sec w g ≃ P1 × P2 :=
    { toFun := fun σ => (fun z => σ z.1, fun z => σ z.1)
      invFun := fun p z => if hz : z ∈ fslots C then p.1 ⟨z, hz⟩ else p.2 ⟨z, hz⟩
      left_inv := fun σ => by
        funext z
        by_cases hz : z ∈ fslots C <;> simp [hz]
      right_inv := fun ⟨p1, p2⟩ => by
        ext z
        · simp [z.2]
        · simp [z.2] }
  have hcard_split : Fintype.card (Sec w g) = Fintype.card P1 * Fintype.card P2 := by
    rw [Fintype.card_congr split, Fintype.card_prod]
  let def2 : P2 := fun z => ⟨Classical.choose (hg z.1.1 z.1.2), Classical.choose_spec (hg z.1.1 z.1.2)⟩
  let toCopy : P1 → Clause (RawT w) := fun p1 => repFn w g (split.symm (p1, def2)) C
  have hcopies_eq : copiesFn w g C = Finset.univ.image toCopy := by
    ext E'
    constructor
    · intro hE'
      obtain ⟨σ, rfl⟩ := exists_sec_of_mem_copies w g hg hnt hE'
      refine Finset.mem_image.2 ⟨fun z => σ z.1, Finset.mem_univ _, ?_⟩
      apply repFn_eq_of_agree_fslots w g hnt
      intro z hz
      simp [split, hz]
    · intro hE'
      obtain ⟨p1, _, rfl⟩ := Finset.mem_image.1 hE'
      exact repFn_mem_copies w g hnt _
  have htoCopy_inj : Function.Injective toCopy := by
    intro p1 q1 heq
    have hag := agree_fslots_of_repFn_eq w g hnt heq
    funext ⟨z, hz⟩
    have := hag z hz
    simpa [split, hz] using this
  have hcopies_card : (copiesFn w g C).card = Fintype.card P1 := by
    rw [hcopies_eq, Finset.card_image_of_injective _ htoCopy_inj, Finset.card_univ]
  let filt := (Finset.univ : Finset (Sec w g)).filter (fun σ => repFn w g σ C = E)
  let toSec : P2 → Sec w g := fun p2 => split.symm (fun z => σ₀ z.1, p2)
  have hfilt_eq : filt = Finset.univ.image toSec := by
    ext σ
    simp only [filt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hrep
      have hag := agree_fslots_of_repFn_eq w g hnt (hrep.trans hσ₀.symm)
      refine ⟨fun z => σ z.1, ?_⟩
      funext z
      by_cases hz : z ∈ fslots C
      · simp [toSec, split, hz, (hag z hz).symm]
      · simp [toSec, split, hz]
    · rintro ⟨p2, rfl⟩
      rw [← hσ₀]
      apply repFn_eq_of_agree_fslots w g hnt
      intro z hz
      simp [toSec, split, hz]
  have htoSec_inj : Function.Injective toSec := by
    intro p2 q2 heq
    have h1 := congrArg split heq
    simp only [toSec, Equiv.apply_symm_apply] at h1
    exact (Prod.mk.inj h1).2
  have hfilt_card : filt.card = Fintype.card P2 := by
    rw [hfilt_eq, Finset.card_image_of_injective _ htoSec_inj, Finset.card_univ]
  rw [hfilt_card, hcopies_card, hcard_split, Nat.mul_comm]

lemma sum_outer_eq_card_mul_sec {n : ℕ} (w : Fin n → ℕ) (hw : ∀ i, 0 < w i)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (hg : ∀ i b, ∃ x, g i x = b)
    (F : Finset (Clause (Fin n)))
    (hF : ∀ C ∈ F, ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    (A : Finset (Clause (RawT w))) (hA : A ⊆ F.biUnion (copiesFn w g)) :
    ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copiesFn w g C).card) =
      A.card * Fintype.card (Sec w g) := by
  classical
  have h1 :
      ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copiesFn w g C).card) =
      ∑ C ∈ F, ∑ σ : Sec w g, if repFn w g σ C ∈ A then (copiesFn w g C).card else 0 := by
    calc
      ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copiesFn w g C).card)
          = ∑ σ : Sec w g, ∑ C ∈ F, if repFn w g σ C ∈ A then (copiesFn w g C).card else 0 := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [Finset.sum_filter]
      _ = ∑ C ∈ F, ∑ σ : Sec w g, if repFn w g σ C ∈ A then (copiesFn w g C).card else 0 :=
            Finset.sum_comm
  rw [h1]
  have hinner : ∀ C ∈ F,
      ∑ σ : Sec w g, (if repFn w g σ C ∈ A then (copiesFn w g C).card else 0) =
        (A ∩ copiesFn w g C).card * Fintype.card (Sec w g) := by
    intro C hCF
    have hsplit :
        ∑ σ : Sec w g, (if repFn w g σ C ∈ A then (copiesFn w g C).card else 0) =
        ∑ E ∈ A ∩ copiesFn w g C,
          ((Finset.univ : Finset (Sec w g)).filter (fun σ => repFn w g σ C = E)).card *
            (copiesFn w g C).card := by
      calc
        ∑ σ : Sec w g, (if repFn w g σ C ∈ A then (copiesFn w g C).card else 0)
            = ∑ σ : Sec w g, ∑ E ∈ A ∩ copiesFn w g C,
                if repFn w g σ C = E then (copiesFn w g C).card else 0 := by
              apply Finset.sum_congr rfl
              intro σ _
              by_cases hmem : repFn w g σ C ∈ A
              · have hmem' : repFn w g σ C ∈ A ∩ copiesFn w g C :=
                  Finset.mem_inter.2 ⟨hmem, repFn_mem_copies w g (hF C hCF) σ⟩
                simp [hmem, hmem']
              · have hnot : ∀ E ∈ A ∩ copiesFn w g C, repFn w g σ C ≠ E := fun E hE heq =>
                  hmem (heq ▸ (Finset.mem_inter.1 hE).1)
                simp only [hmem, ↓reduceIte]
                symm
                exact Finset.sum_eq_zero (fun E hE => by simp [hnot E hE])
        _ = ∑ E ∈ A ∩ copiesFn w g C, ∑ σ : Sec w g,
              if repFn w g σ C = E then (copiesFn w g C).card else 0 := Finset.sum_comm
        _ = ∑ E ∈ A ∩ copiesFn w g C,
              ((Finset.univ : Finset (Sec w g)).filter (fun σ => repFn w g σ C = E)).card *
                (copiesFn w g C).card := by
              apply Finset.sum_congr rfl
              intro E _
              rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [hsplit]
    calc
      ∑ E ∈ A ∩ copiesFn w g C,
          ((Finset.univ : Finset (Sec w g)).filter (fun σ => repFn w g σ C = E)).card *
            (copiesFn w g C).card
          = ∑ _E ∈ A ∩ copiesFn w g C, Fintype.card (Sec w g) := by
            apply Finset.sum_congr rfl
            intro E hE
            exact sec_fiber_card_mul w g hg (hF C hCF) (Finset.mem_inter.1 hE).2
      _ = (A ∩ copiesFn w g C).card * Fintype.card (Sec w g) := by
            rw [Finset.sum_const, smul_eq_mul]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  congr 1
  have hpart : F.biUnion (fun C => A ∩ copiesFn w g C) = A := by
    ext E
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨_, _, hEA, _⟩; exact hEA
    · intro hEA
      obtain ⟨C, hCF, hEC⟩ := Finset.mem_biUnion.1 (hA hEA)
      exact ⟨C, hCF, hEA, hEC⟩
  have hcard : A.card = ∑ C ∈ F, (A ∩ copiesFn w g C).card := by
    conv_lhs => rw [← hpart]
    exact Finset.card_biUnion (fun C₁ hC₁ C₂ hC₂ hne =>
      Finset.disjoint_left.2 (fun E h1 h2 =>
        Finset.disjoint_left.1 (copies_disjoint w hw g (hF C₁ hC₁) (hF C₂ hC₂) hne)
          (Finset.mem_inter.1 h1).2 (Finset.mem_inter.1 h2).2))
  exact hcard.symm

lemma bad_sec_of_bad_raw {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool)
    (F : Finset (Clause (Fin n)))
    (hF : ∀ C ∈ F, ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    (A : Finset (Clause (RawT w))) (hA : A ⊆ F.biUnion (copiesFn w g))
    (hbad : ¬ Satisfiable (A : Set (Clause (RawT w)))) (σ : Sec w g) :
    ¬ Satisfiable ((F.filter (fun C => repFn w g σ C ∈ A) : Finset (Clause (Fin n))) :
      Set (Clause (Fin n))) := by
  intro ⟨x, hx⟩
  apply hbad
  let y : RawT w → Bool := fun u => (σ (u.1, x u.1)).1 u.2
  refine ⟨y, fun E hEA => ?_⟩
  have hEA' : E ∈ A := Finset.mem_coe.1 hEA
  obtain ⟨C, hCF, hEC⟩ := Finset.mem_biUnion.1 (hA hEA')
  by_contra hnsat
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hEC
  have hx₀f := (Finset.mem_filter.1 hx₀).2
  have hy_eq : ∀ u : RawT w, u.1 ∈ C.image Prod.fst → y u = x₀ u := by
    intro u hu
    by_contra hne
    apply hnsat
    refine ⟨(u, !(x₀ u)), Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩, rfl⟩, ?_⟩
    cases hyu : y u <;> cases hx0u : x₀ u <;> simp_all
  have hxfals : ∀ l ∈ C, x l.1 ≠ l.2 := by
    intro ⟨i, s⟩ hl
    have hi : i ∈ C.image Prod.fst := Finset.mem_image.2 ⟨(i, s), hl, rfl⟩
    have hgi : g i (fun j => y ⟨i, j⟩) = x i := (σ (i, x i)).2
    have hyeq : (fun j => y ⟨i, j⟩) = (fun j => x₀ ⟨i, j⟩) := funext fun j => hy_eq ⟨i, j⟩ hi
    rw [← hgi, hyeq]
    exact hx₀f (i, s) hl
  have hrep_eq : repFn w g σ C = blockFn w C x₀ := by
    unfold repFn
    rw [blockFn_eq_iff]
    rintro ⟨i, j⟩ hu
    obtain ⟨⟨i', s⟩, hlC, hi'⟩ := Finset.mem_image.1 hu
    simp only at hi'
    subst hi'
    have hxs := hxfals (i', s) hlC
    rw [← hy_eq ⟨i', j⟩ hu]
    dsimp only [y]
    cases s
    · have hxt : x i' = true := by cases hxi : x i' <;> simp_all
      simp only [hlC, ↓reduceIte]
      rw [hxt]
    · have hxf : x i' = false := by cases hxi : x i' <;> simp_all
      have hnf : (i', false) ∉ C := fun hf => hF C hCF i' ⟨hlC, hf⟩
      simp only [hnf, ↓reduceIte]
      rw [hxf]
  have hCmem : C ∈ F.filter (fun C => repFn w g σ C ∈ A) :=
    Finset.mem_filter.2 ⟨hCF, hrep_eq ▸ hEA'⟩
  obtain ⟨l, hlC, hxl⟩ := hx C (Finset.mem_coe.2 hCmem)
  exact hxfals l hlC hxl

lemma bad_raw_of_bad_sec {n : ℕ} (w : Fin n → ℕ)
    (g : (i : Fin n) → (Fin (w i) → Bool) → Bool) (hg : ∀ i b, ∃ x, g i x = b)
    (F : Finset (Clause (Fin n)))
    (hF : ∀ C ∈ F, ∀ i, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    (A : Finset (Clause (RawT w)))
    (hsec : ∀ σ : Sec w g,
      ¬ Satisfiable ((F.filter (fun C => repFn w g σ C ∈ A) : Finset (Clause (Fin n))) :
        Set (Clause (Fin n)))) :
    ¬ Satisfiable (A : Set (Clause (RawT w))) := by
  classical
  intro ⟨y, hy⟩
  let x : Fin n → Bool := fun i => g i (fun j => y ⟨i, j⟩)
  let σ : Sec w g := fun z =>
    if hz : x z.1 = z.2 then ⟨fun j => y ⟨z.1, j⟩, hz⟩
    else ⟨Classical.choose (hg z.1 z.2), Classical.choose_spec (hg z.1 z.2)⟩
  apply hsec σ
  refine ⟨x, fun C hC => ?_⟩
  have hC' := Finset.mem_filter.1 (Finset.mem_coe.1 hC)
  have hCF := hC'.1
  have hrepA := hC'.2
  by_contra hnsat
  have hxfals : ∀ l ∈ C, x l.1 ≠ l.2 := fun l hl hxl => hnsat ⟨l, hl, hxl⟩
  have hrep_eq : repFn w g σ C = blockFn w C y := by
    unfold repFn
    rw [blockFn_eq_iff]
    rintro ⟨i, j⟩ hu
    obtain ⟨⟨i', s⟩, hlC, hi'⟩ := Finset.mem_image.1 hu
    simp only at hi'
    subst hi'
    have hxs := hxfals (i', s) hlC
    cases s
    · have hxt : x i' = true := by cases hxi : x i' <;> simp_all
      simp only [hlC, ↓reduceIte, σ, hxt, ↓reduceDIte]
    · have hxf : x i' = false := by cases hxi : x i' <;> simp_all
      have hnf : (i', false) ∉ C := fun hf => hF C hCF i' ⟨hlC, hf⟩
      simp only [hnf, ↓reduceIte, σ, hxf, ↓reduceDIte]
  obtain ⟨l, hlE, hyl⟩ := hy (repFn w g σ C) (Finset.mem_coe.2 hrepA)
  rw [hrep_eq] at hlE
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 hlE
  simp at hyl

lemma eq_of_update_inv {α β : Type*} [Fintype α] [DecidableEq α] {f : α → Type*}
    (S : Finset α) (φ : (∀ a, f a) → β)
    (hstep : ∀ (σ : ∀ a, f a) (a : α) (v : f a), a ∉ S → φ (Function.update σ a v) = φ σ)
    {σ₁ σ₂ : ∀ a, f a} (hag : ∀ a ∈ S, σ₁ a = σ₂ a) :
    φ σ₁ = φ σ₂ := by
  classical
  have hmain : ∀ (T : Finset α) (σ₁ σ₂ : ∀ a, f a),
      (∀ a ∈ S, σ₁ a = σ₂ a) → (∀ a, σ₁ a ≠ σ₂ a → a ∈ T) → φ σ₁ = φ σ₂ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro σ₁ σ₂ _ hdiff
      have heq : σ₁ = σ₂ := by
        funext a
        by_contra hne
        exact Finset.notMem_empty a (hdiff a hne)
      rw [heq]
    | @insert a₀ T' ha₀ ih =>
      intro σ₁ σ₂ hag' hdiff
      by_cases haS : a₀ ∈ S
      · apply ih σ₁ σ₂ hag'
        intro a hne
        have hmem := hdiff a hne
        rcases Finset.mem_insert.1 hmem with rfl | hT'
        · exact (hne (hag' a haS)).elim
        · exact hT'
      · let σ' := Function.update σ₁ a₀ (σ₂ a₀)
        have h1 : φ σ' = φ σ₁ := hstep σ₁ a₀ (σ₂ a₀) haS
        rw [← h1]
        apply ih σ' σ₂
        · intro a ha
          have hne : a ≠ a₀ := fun e => haS (e ▸ ha)
          simp [σ', Function.update_of_ne hne, hag' a ha]
        · intro a hne
          by_cases ha : a = a₀
          · subst ha; simp [σ'] at hne
          · simp only [σ', Function.update_of_ne ha] at hne
            rcases Finset.mem_insert.1 (hdiff a hne) with rfl | hT'
            · exact (ha rfl).elim
            · exact hT'
  let D : Finset α := Finset.univ.filter (fun a => σ₁ a ≠ σ₂ a)
  exact hmain D σ₁ σ₂ hag (fun a hne => Finset.mem_filter.2 ⟨Finset.mem_univ a, hne⟩)

end PEqualNP.Outside.L_pcx_325_aux

theorem PEqualNP.Outside.L_pcx_325 : (∀ (n : ℕ) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  ∀ g : (i : Fin n) → (Fin (w i) → Bool) → Bool, (∀ i b, ∃ x, g i x = b) →
  let B := PEqualNP.ProofComplexity.Clause (Fin n)
  let Raw := (i : Fin n) × Fin (w i)
  let Axiom := PEqualNP.ProofComplexity.Clause Raw
  let block := fun (C : B) (x : Raw → Bool) =>
    ((Finset.univ : Finset Raw).filter (fun j => j.1 ∈ C.image Prod.fst)).image (fun j => (j, !(x j)))
  let copies := fun (C : B) =>
    ((Finset.univ : Finset (Raw → Bool)).filter (fun x =>
      ∀ l ∈ C, g l.1 (fun j => x ⟨l.1,j⟩) ≠ l.2)).image (block C)
  ∀ F : Finset B, (∀ C ∈ F, ∀ i, ¬ ((i,true) ∈ C ∧ (i,false) ∈ C)) →
    let allAx := F.biUnion copies
    let bad := fun {V : Type} (K : Finset (PEqualNP.ProofComplexity.Clause V)) =>
      ¬ PEqualNP.ProofComplexity.Satisfiable (K : Set (PEqualNP.ProofComplexity.Clause V))
    let outer := fun (K : Finset B) => K.sum (fun C => (copies C).card)
    let bestOuter := fun K => K ⊆ F ∧ bad K ∧ ∀ Q ⊆ F, bad Q → outer K ≤ outer Q
    let bestRaw := fun (A : Finset Axiom) => A ⊆ allAx ∧ bad A ∧ ∀ Q ⊆ allAx, bad Q → A.card ≤ Q.card
    ∀ r : ℕ, 2 ≤ r → ∀ (H : Finset B) (P : Fin r → Finset B),
      (∀ i, (P i).Nonempty ∧ Disjoint H (P i)) →
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) →
      (∀ Q, bestOuter Q ↔ ∃ i, Q = H ∪ P i) →
      let slots := fun i : Fin r => (Finset.univ : Finset (Fin n × Bool)).filter
        (fun z => ∀ C ∈ P i, (z.1, !z.2) ∈ C)
      ∀ I : Finset (Fin n × Bool), (∀ i j, i ≠ j → slots i ∩ slots j = I) →
        let choices := I.prod (fun z =>
          ((Finset.univ : Finset (Fin (w z.1) → Bool)).filter (fun x => g z.1 x = z.2)).card)
        Nat.card {A : Finset Axiom // bestRaw A} = r^choices) := by
  classical
  open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_325_aux in
  intro n w hw g hg B Raw Axiom block copies F hF allAx bad outer bestOuter bestRaw
    r hr H P hP hPdisj hbest slots I hI choices
  have hSec_ne : Nonempty (Sec w g) :=
    ⟨fun z => ⟨Classical.choose (hg z.1 z.2), Classical.choose_spec (hg z.1 z.2)⟩⟩
  have hSec_pos : 0 < Fintype.card (Sec w g) := Fintype.card_pos_iff.2 hSec_ne
  let i0 : Fin r := ⟨0, by omega⟩
  have hbest_i : ∀ i : Fin r, bestOuter (H ∪ P i) := fun i => (hbest (H ∪ P i)).2 ⟨i, rfl⟩
  let M : ℕ := outer (H ∪ P i0)
  have houter_i : ∀ i : Fin r, outer (H ∪ P i) = M := fun i =>
    le_antisymm ((hbest_i i).2.2 _ (hbest_i i0).1 (hbest_i i0).2.1)
      ((hbest_i i0).2.2 _ (hbest_i i).1 (hbest_i i).2.1)
  have hH_sub : H ⊆ F := fun C hC => (hbest_i i0).1 (Finset.mem_union_left _ hC)
  have hP_sub : ∀ i : Fin r, P i ⊆ F := fun i C hC => (hbest_i i).1 (Finset.mem_union_right _ hC)
  have hA0_sub : (H ∪ P i0).biUnion copies ⊆ allAx := by
    intro E hE
    obtain ⟨C, hC, hEC⟩ := Finset.mem_biUnion.1 hE
    exact Finset.mem_biUnion.2 ⟨C, (hbest_i i0).1 hC, hEC⟩
  have hA0_bad : bad ((H ∪ P i0).biUnion copies) := by
    apply bad_raw_of_bad_sec w g hg F hF
    intro σ
    have hsub : H ∪ P i0 ⊆ F.filter (fun C => repFn w g σ C ∈ (H ∪ P i0).biUnion copies) := by
      intro C hC
      refine Finset.mem_filter.2 ⟨(hbest_i i0).1 hC, Finset.mem_biUnion.2 ⟨C, hC, ?_⟩⟩
      exact repFn_mem_copies w g (hF C ((hbest_i i0).1 hC)) σ
    intro ⟨x, hx⟩
    exact (hbest_i i0).2.1 ⟨x, fun C hC => hx C (Finset.mem_coe.2 (hsub (Finset.mem_coe.1 hC)))⟩
  have hA0_card : ((H ∪ P i0).biUnion copies).card = M := by
    rw [Finset.card_biUnion]
    intro C₁ hC₁ C₂ hC₂ hne
    exact copies_disjoint w hw g (hF C₁ ((hbest_i i0).1 hC₁)) (hF C₂ ((hbest_i i0).1 hC₂)) hne
  have hcard_ge_M : ∀ Q : Finset Axiom, Q ⊆ allAx → bad Q → M ≤ Q.card := by
    intro Q hQ hQbad
    have hsum : ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ Q)).sum (fun C => (copies C).card) =
        Q.card * Fintype.card (Sec w g) :=
      sum_outer_eq_card_mul_sec w hw g hg F hF Q hQ
    have hle : ∑ _σ : Sec w g, M ≤
        ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ Q)).sum (fun C => (copies C).card) := by
      apply Finset.sum_le_sum
      intro σ _
      exact (hbest_i i0).2.2 _ (Finset.filter_subset _ F) (bad_sec_of_bad_raw w g F hF Q hQ hQbad σ)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hsum, Nat.mul_comm] at hle
    exact Nat.le_of_mul_le_mul_right hle hSec_pos
  have hbestRaw_iff : ∀ A : Finset Axiom,
      bestRaw A ↔ A ⊆ allAx ∧ ∀ σ : Sec w g, ∃ i : Fin r,
        F.filter (fun C => repFn w g σ C ∈ A) = H ∪ P i := by
    intro A
    constructor
    · rintro ⟨hAsub, hAbad, hAmin⟩
      refine ⟨hAsub, fun σ => ?_⟩
      have hAcard : A.card = M := le_antisymm (hA0_card ▸ hAmin _ hA0_sub hA0_bad)
        (hcard_ge_M A hAsub hAbad)
      have hsum : ∑ τ : Sec w g, (F.filter (fun C => repFn w g τ C ∈ A)).sum (fun C => (copies C).card) =
          A.card * Fintype.card (Sec w g) :=
        sum_outer_eq_card_mul_sec w hw g hg F hF A hAsub
      rw [hAcard] at hsum
      have hge : ∀ τ : Sec w g,
          M ≤ (F.filter (fun C => repFn w g τ C ∈ A)).sum (fun C => (copies C).card) :=
        fun τ => (hbest_i i0).2.2 _ (Finset.filter_subset _ F)
          (bad_sec_of_bad_raw w g F hF A hAsub hAbad τ)
      have heq_all : ∀ τ ∈ (Finset.univ : Finset (Sec w g)),
          (F.filter (fun C => repFn w g τ C ∈ A)).sum (fun C => (copies C).card) = M := by
        have hsum_eq : ∑ τ ∈ (Finset.univ : Finset (Sec w g)),
            (F.filter (fun C => repFn w g τ C ∈ A)).sum (fun C => (copies C).card) =
            ∑ _τ ∈ (Finset.univ : Finset (Sec w g)), M := by
          rw [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
        exact (Finset.sum_eq_sum_iff_of_le (fun τ _ => hge τ)).1 hsum_eq.symm |> fun h τ hτ => (h τ hτ).symm
      have hbo : bestOuter (F.filter (fun C => repFn w g σ C ∈ A)) := by
        refine ⟨Finset.filter_subset _ F, bad_sec_of_bad_raw w g F hF A hAsub hAbad σ, ?_⟩
        intro Q hQF hQbad
        change (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copies C).card) ≤ outer Q
        rw [heq_all σ (Finset.mem_univ σ)]
        exact (hbest_i i0).2.2 Q hQF hQbad
      exact (hbest _).1 hbo
    · rintro ⟨hAsub, hsec⟩
      have hAbad : bad A := by
        apply bad_raw_of_bad_sec w g hg F hF
        intro σ
        obtain ⟨i, hi⟩ := hsec σ
        rw [hi]
        exact (hbest_i i).2.1
      have hAcard : A.card = M := by
        have hsum : ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copies C).card) =
            A.card * Fintype.card (Sec w g) :=
          sum_outer_eq_card_mul_sec w hw g hg F hF A hAsub
        have hconst : ∑ σ : Sec w g,
            (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copies C).card) =
            M * Fintype.card (Sec w g) := by
          calc
            ∑ σ : Sec w g, (F.filter (fun C => repFn w g σ C ∈ A)).sum (fun C => (copies C).card)
                = ∑ _σ : Sec w g, M := by
                  apply Finset.sum_congr rfl
                  intro σ _
                  obtain ⟨i, hi⟩ := hsec σ
                  rw [hi]
                  exact houter_i i
            _ = M * Fintype.card (Sec w g) := by
                  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm]
        rw [hconst] at hsum
        exact Nat.eq_of_mul_eq_mul_right hSec_pos hsum.symm
      exact ⟨hAsub, hAbad, fun Q hQ hQbad => hAcard ▸ hcard_ge_M Q hQ hQbad⟩
  have huniq_i : ∀ {i j : Fin r}, H ∪ P i = H ∪ P j → i = j := by
    intro i j heq
    by_contra hne
    obtain ⟨C, hCi⟩ := (hP i).1
    have hCin : C ∈ H ∪ P j := heq ▸ Finset.mem_union_right H hCi
    rcases Finset.mem_union.1 hCin with hCH | hCj
    · exact Finset.disjoint_left.1 (hP i).2 hCH hCi
    · exact Finset.disjoint_left.1 (hPdisj i j hne) hCi hCj
  have hI_sub_slots : ∀ i : Fin r, I ⊆ slots i := by
    intro i
    let j : Fin r := if i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      by_cases hi0 : i.val = 0
      · simp [j, hi0] at hv
      · simp [j, hi0] at hv
    rw [← hI i j hij]
    exact Finset.inter_subset_left
  have hslots_sub_fslots : ∀ (i : Fin r) (C : B), C ∈ P i → slots i ⊆ fslots C := by
    intro i C hCP z hz
    exact Finset.mem_filter.2 ⟨Finset.mem_univ z, (Finset.mem_filter.1 hz).2 C hCP⟩
  let ITup := ∀ z : ↥I, Fiber w g z.1
  let restr : Sec w g → ITup := fun σ z => σ z.1
  let extI : ITup → Sec w g := fun t z =>
    if hz : z ∈ I then t ⟨z, hz⟩
    else ⟨Classical.choose (hg z.1 z.2), Classical.choose_spec (hg z.1 z.2)⟩
  have hrestr_ext : ∀ t : ITup, restr (extI t) = t := by
    intro t
    funext ⟨z, hz⟩
    simp [restr, extI, hz]
  let fromFn : (ITup → Fin r) → Finset Axiom := fun ψ =>
    allAx.filter (fun E => ∃ C ∈ F, ∃ σ : Sec w g, repFn w g σ C = E ∧ C ∈ H ∪ P (ψ (restr σ)))
  have hfromFn_sec : ∀ (ψ : ITup → Fin r) (σ : Sec w g),
      F.filter (fun C => repFn w g σ C ∈ fromFn ψ) = H ∪ P (ψ (restr σ)) := by
    intro ψ σ
    ext C
    simp only [Finset.mem_filter, fromFn]
    constructor
    · rintro ⟨hCF, _, C', hC'F, σ', hrep', hC'in⟩
      have hCeq : C = C' := by
        by_contra hne
        have h1 := repFn_mem_copies w g (hF C hCF) σ
        have h2 := repFn_mem_copies w g (hF C' hC'F) σ'
        rw [hrep'] at h2
        exact Finset.disjoint_left.1 (copies_disjoint w hw g (hF C hCF) (hF C' hC'F) hne) h1 h2
      subst hCeq
      rcases Finset.mem_union.1 hC'in with hCH | hCP
      · exact Finset.mem_union_left _ hCH
      · have hag := agree_fslots_of_repFn_eq w g (hF C hCF) hrep'.symm
        have hreq : restr σ = restr σ' := by
          funext ⟨z, hz⟩
          exact hag z (hslots_sub_fslots _ C hCP (hI_sub_slots _ hz))
        rw [hreq]
        exact Finset.mem_union_right _ hCP
    · intro hCin
      have hCF : C ∈ F := (hbest_i (ψ (restr σ))).1 hCin
      refine ⟨hCF, Finset.mem_biUnion.2 ⟨C, hCF, repFn_mem_copies w g (hF C hCF) σ⟩,
        C, hCF, σ, rfl, hCin⟩
  have hfromFn_best : ∀ ψ : ITup → Fin r, bestRaw (fromFn ψ) := fun ψ =>
    (hbestRaw_iff (fromFn ψ)).2 ⟨Finset.filter_subset _ allAx, fun σ => ⟨ψ (restr σ), hfromFn_sec ψ σ⟩⟩
  let toFn : {A : Finset Axiom // bestRaw A} → (ITup → Fin r) := fun ⟨A, hA⟩ t =>
    Classical.choose (((hbestRaw_iff A).1 hA).2 (extI t))
  have htoFn_spec : ∀ (A : {A : Finset Axiom // bestRaw A}) (σ : Sec w g),
      F.filter (fun C => repFn w g σ C ∈ A.1) = H ∪ P (toFn A (restr σ)) := by
    rintro ⟨A, hA⟩ σ
    have hA' := (hbestRaw_iff A).1 hA
    let φ : Sec w g → Fin r := fun τ => Classical.choose (hA'.2 τ)
    have hφ_spec : ∀ τ : Sec w g, F.filter (fun C => repFn w g τ C ∈ A) = H ∪ P (φ τ) :=
      fun τ => Classical.choose_spec (hA'.2 τ)
    have hslot_inv : ∀ (i : Fin r) (τ : Sec w g) (z : Fin n × Bool) (v : Fiber w g z),
        z ∉ slots i → (φ (Function.update τ z v) = i ↔ φ τ = i) := by
      intro i τ z v hz
      have hnotall : ¬ ∀ C ∈ P i, (z.1, !z.2) ∈ C := fun hall =>
        hz (Finset.mem_filter.2 ⟨Finset.mem_univ z, hall⟩)
      push Not at hnotall
      obtain ⟨C, hCP, hznC⟩ := hnotall
      have hCF : C ∈ F := hP_sub i hCP
      have hrep_eq : repFn w g (Function.update τ z v) C = repFn w g τ C := by
        apply repFn_eq_of_agree_fslots w g (hF C hCF)
        intro z' hz'
        have hne : z' ≠ z := fun e => hznC (e ▸ (Finset.mem_filter.1 hz').2)
        exact Function.update_of_ne hne v τ
      have hmem_iff : ∀ τ' : Sec w g, C ∈ F.filter (fun D => repFn w g τ' D ∈ A) ↔ φ τ' = i := by
        intro τ'
        rw [hφ_spec τ']
        constructor
        · intro hCin
          rcases Finset.mem_union.1 hCin with hCH | hCφ
          · exact (Finset.disjoint_left.1 (hP i).2 hCH hCP).elim
          · by_contra hne
            exact Finset.disjoint_left.1 (hPdisj _ i hne) hCφ hCP
        · rintro rfl
          exact Finset.mem_union_right H hCP
      rw [← hmem_iff (Function.update τ z v), ← hmem_iff τ]
      simp [hCF, hrep_eq]
    have hI_inv : ∀ (τ : Sec w g) (z : Fin n × Bool) (v : Fiber w g z),
        z ∉ I → φ (Function.update τ z v) = φ τ := by
      intro τ z v hzI
      set i := φ τ
      by_cases hzs : z ∈ slots i
      · by_contra hne
        have hnotj : z ∉ slots (φ (Function.update τ z v)) := by
          intro hzj
          exact hzI (hI i (φ (Function.update τ z v)) (Ne.symm hne) ▸
            Finset.mem_inter.2 ⟨hzs, hzj⟩)
        have hcontra := (hslot_inv (φ (Function.update τ z v)) τ z v hnotj).1 rfl
        exact hne hcontra.symm
      · exact (hslot_inv i τ z v hzs).2 rfl
    have hφ_eq : φ σ = φ (extI (restr σ)) :=
      eq_of_update_inv I φ hI_inv (fun z hz => by simp [extI, restr, hz])
    rw [hφ_spec σ, hφ_eq]
  let equiv : {A : Finset Axiom // bestRaw A} ≃ (ITup → Fin r) :=
    { toFun := toFn
      invFun := fun ψ => ⟨fromFn ψ, hfromFn_best ψ⟩
      left_inv := fun ⟨A, hA⟩ => by
        apply Subtype.ext
        ext E
        have hAsub : A ⊆ allAx := hA.1
        have hFsub : fromFn (toFn ⟨A, hA⟩) ⊆ allAx := Finset.filter_subset _ allAx
        by_cases hEall : E ∈ allAx
        · obtain ⟨C, hCF, hEC⟩ := Finset.mem_biUnion.1 hEall
          obtain ⟨σ, rfl⟩ := exists_sec_of_mem_copies w g hg (hF C hCF) hEC
          have h1 := hfromFn_sec (toFn ⟨A, hA⟩) σ
          have h2 := htoFn_spec ⟨A, hA⟩ σ
          have hCiff : C ∈ F.filter (fun D => repFn w g σ D ∈ fromFn (toFn ⟨A, hA⟩)) ↔
              C ∈ F.filter (fun D => repFn w g σ D ∈ A) := by
            rw [h1, h2]
          simpa [hCF] using hCiff
        · exact ⟨fun h => (hEall (hFsub h)).elim, fun h => (hEall (hAsub h)).elim⟩
      right_inv := fun ψ => by
        funext t
        have h1 := htoFn_spec ⟨fromFn ψ, hfromFn_best ψ⟩ (extI t)
        have h2 := hfromFn_sec ψ (extI t)
        rw [hrestr_ext t] at h1 h2
        exact huniq_i (h1.symm.trans h2) }
  rw [Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
  congr 1
  dsimp only [ITup, choices]
  rw [Fintype.card_pi]
  rw [Finset.prod_coe_sort I (fun z => Fintype.card (Fiber w g z))]
  apply Finset.prod_congr rfl
  intro z _
  exact Fintype.card_subtype (fun x => g z.1 x = z.2)
