import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1150_aux

open Classical Finset

section Graph

variable {n : ℕ} (u v : Fin n → Fin n)

def cut (S : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => decide (u i ∈ S) != decide (v i ∈ S))

theorem mem_cut {S : Finset (Fin n)} {i : Fin n} :
    i ∈ cut u v S ↔ (u i ∈ S ∧ v i ∉ S) ∨ (v i ∈ S ∧ u i ∉ S) := by
  simp only [cut, mem_filter, mem_univ, true_and]
  by_cases hu : u i ∈ S <;> by_cases hv : v i ∈ S <;> simp [hu, hv]

theorem cut_symmDiff (A B : Finset (Fin n)) :
    cut u v (symmDiff A B) = symmDiff (cut u v A) (cut u v B) := by
  ext i
  simp only [mem_symmDiff, mem_cut]
  by_cases ha1 : u i ∈ A <;> by_cases ha2 : v i ∈ A <;>
    by_cases hb1 : u i ∈ B <;> by_cases hb2 : v i ∈ B <;> simp_all

noncomputable def bridges : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => ∃ U : Finset (Fin n), cut u v U = {i})

def edgeAdj (i a b : Fin n) : Prop :=
  (u i = a ∧ v i = b) ∨ (v i = a ∧ u i = b)

inductive Reach (E : Finset (Fin n)) : Fin n → Fin n → Prop
  | refl (a) : Reach E a a
  | step {a b c} : Reach E a b → ∀ i ∈ E, edgeAdj u v i b c → Reach E a c

theorem reach_mono {E₁ E₂ : Finset (Fin n)} (hsub : E₁ ⊆ E₂) {a b : Fin n}
    (h : Reach u v E₁ a b) : Reach u v E₂ a b := by
  induction h with
  | refl => exact .refl a
  | step _ i hi hbc ih => exact .step ih i (hsub hi) hbc

theorem reach_trans {E : Finset (Fin n)} {a b c : Fin n}
    (hab : Reach u v E a b) (hbc : Reach u v E b c) : Reach u v E a c := by
  induction hbc with
  | refl => exact hab
  | step _ i hi hcd ih => exact .step ih i hi hcd

theorem edgeAdj_symm {i a b : Fin n} (h : edgeAdj u v i a b) : edgeAdj u v i b a := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [exact Or.inr ⟨h2, h1⟩; exact Or.inl ⟨h2, h1⟩]

theorem reach_symm {E : Finset (Fin n)} {a b : Fin n}
    (h : Reach u v E a b) : Reach u v E b a := by
  induction h with
  | refl => exact .refl a
  | step _ i hi hbc ih =>
    exact reach_trans u v (.step (.refl _) i hi (edgeAdj_symm u v hbc)) ih

theorem reach_cut {E : Finset (Fin n)} {a b : Fin n} (h : Reach u v E a b)
    (U : Finset (Fin n)) (ha : a ∈ U) (hb : b ∉ U) : ∃ i ∈ E, i ∈ cut u v U := by
  induction h with
  | refl => exact absurd ha hb
  | @step y z _ i hi hyz ih =>
    by_cases hy : y ∈ U
    · refine ⟨i, hi, (mem_cut u v).2 ?_⟩
      rcases hyz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hy, hb⟩
      · exact Or.inr ⟨hy, hb⟩
    · exact ih hy

theorem reach_cut_iff {E : Finset (Fin n)} {a b : Fin n} (h : Reach u v E a b)
    {U : Finset (Fin n)} (hcut : E ∩ cut u v U = ∅) : a ∈ U ↔ b ∈ U := by
  constructor
  · intro ha
    by_contra hb
    obtain ⟨i, hiE, hiCut⟩ := reach_cut u v h U ha hb
    have hm : i ∈ E ∩ cut u v U := mem_inter.2 ⟨hiE, hiCut⟩
    rw [hcut] at hm
    exact notMem_empty i hm
  · intro hb
    by_contra ha
    obtain ⟨i, hiE, hiCut⟩ := reach_cut u v (reach_symm u v h) U hb ha
    have hm : i ∈ E ∩ cut u v U := mem_inter.2 ⟨hiE, hiCut⟩
    rw [hcut] at hm
    exact notMem_empty i hm

theorem connected_univ (hconn : ∀ U : Finset (Fin n), U.Nonempty → U ≠ Finset.univ → (cut u v U).Nonempty)
    (a b : Fin n) : Reach u v Finset.univ a b := by
  by_contra h
  let U : Finset (Fin n) := Finset.univ.filter (fun w => Reach u v Finset.univ a w)
  have ha : a ∈ U := mem_filter.2 ⟨mem_univ a, .refl a⟩
  have hb : b ∉ U := fun hb' => h (mem_filter.1 hb').2
  have hne : U ≠ Finset.univ := fun heq => hb (heq ▸ mem_univ b)
  obtain ⟨i, hi⟩ := hconn U ⟨a, ha⟩ hne
  rcases (mem_cut u v).1 hi with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · exact hv (mem_filter.2 ⟨mem_univ _, .step (mem_filter.1 hu).2 i (mem_univ i) (Or.inl ⟨rfl, rfl⟩)⟩)
  · exact hu (mem_filter.2 ⟨mem_univ _, .step (mem_filter.1 hv).2 i (mem_univ i) (Or.inr ⟨rfl, rfl⟩)⟩)

noncomputable def comp (E : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => Reach u v E a w)

noncomputable def compImg (E : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image (comp u v E)

theorem mem_comp {E : Finset (Fin n)} {a w : Fin n} : w ∈ comp u v E a ↔ Reach u v E a w := by
  simp [comp]

theorem comp_eq_of_reach {E : Finset (Fin n)} {a b : Fin n} (h : Reach u v E a b) :
    comp u v E a = comp u v E b := by
  ext w
  simp only [mem_comp]
  exact ⟨fun haw => reach_trans u v (reach_symm u v h) haw, fun hbw => reach_trans u v h hbw⟩

theorem compImg_empty : (compImg u v ∅).card = n := by
  have himg : compImg u v ∅ = Finset.univ.image (fun a : Fin n => ({a} : Finset (Fin n))) := by
    refine Finset.image_congr fun a _ => ?_
    ext w
    simp only [mem_comp, mem_singleton]
    constructor
    · intro h
      induction h with
      | refl => rfl
      | step _ _ hi _ _ => simp at hi
    · rintro rfl; exact .refl w
  rw [himg, Finset.card_image_of_injective _ (fun a b h => singleton_inj.1 h), Finset.card_univ, Fintype.card_fin]

theorem reach_insert_of_reach {E : Finset (Fin n)} {e : Fin n}
    (h : Reach u v E (u e) (v e)) {a b : Fin n} (hr : Reach u v (insert e E) a b) :
    Reach u v E a b := by
  induction hr with
  | refl => exact .refl a
  | step _ i hi hbc ih =>
    rcases mem_insert.1 hi with rfl | hi'
    · rcases hbc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact reach_trans u v ih h
      · exact reach_trans u v ih (reach_symm u v h)
    · exact .step ih i hi' hbc

theorem reach_insert_union {E : Finset (Fin n)} {e a w : Fin n}
    (h : Reach u v (insert e E) a w) (ha : Reach u v E (u e) a ∨ Reach u v E (v e) a) :
    Reach u v E (u e) w ∨ Reach u v E (v e) w := by
  induction h with
  | refl => exact ha
  | step _ i hi hbc ih =>
    rcases mem_insert.1 hi with rfl | hi'
    · rcases hbc with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (.refl _)
      · exact Or.inl (.refl _)
    · rcases ih with h1 | h1
      · exact Or.inl (.step h1 i hi' hbc)
      · exact Or.inr (.step h1 i hi' hbc)

theorem reach_insert_disj {E : Finset (Fin n)} {e a w : Fin n}
    (hu : ¬ Reach u v E a (u e)) (hv : ¬ Reach u v E a (v e))
    (h : Reach u v (insert e E) a w) : Reach u v E a w := by
  induction h with
  | refl => exact .refl a
  | step _ i hi hbc ih =>
    rcases mem_insert.1 hi with rfl | hi'
    · rcases hbc with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact absurd (h1 ▸ ih) hu
      · exact absurd (h1 ▸ ih) hv
    · exact .step ih i hi' hbc

theorem compImg_insert_card_of_reach {E : Finset (Fin n)} {e : Fin n}
    (h : Reach u v E (u e) (v e)) : compImg u v (insert e E) = compImg u v E := by
  refine Finset.image_congr fun a _ => ?_
  ext w
  simp only [mem_comp]
  exact ⟨reach_insert_of_reach u v h, reach_mono u v (subset_insert e E)⟩

theorem compImg_insert_card_of_not_reach {E : Finset (Fin n)} {e : Fin n}
    (h : ¬ Reach u v E (u e) (v e)) :
    (compImg u v (insert e E)).card + 1 = (compImg u v E).card := by
  let Cu := comp u v E (u e)
  let Cv := comp u v E (v e)
  let Cuv := comp u v (insert e E) (u e)
  have hCu : Cu ∈ compImg u v E := mem_image_of_mem _ (mem_univ _)
  have hCv : Cv ∈ compImg u v E := mem_image_of_mem _ (mem_univ _)
  have hne : Cu ≠ Cv := fun heq => h ((mem_comp u v).1 (show v e ∈ Cu from heq ▸ (mem_comp u v).2 (.refl _)))
  have hCuv_eq : Cuv = Cu ∪ Cv := by
    ext w
    simp only [Cuv, Cu, Cv, mem_union, mem_comp]
    constructor
    · intro hr; exact reach_insert_union u v hr (Or.inl (.refl _))
    · rintro (hr | hr)
      · exact reach_mono u v (subset_insert e E) hr
      · exact .step (.refl _) e (mem_insert_self e E) (Or.inl ⟨rfl, rfl⟩) |>
          fun s => reach_trans u v s (reach_mono u v (subset_insert e E) hr)
  have hCuv_not : Cuv ∉ ((compImg u v E).erase Cu).erase Cv := by
    intro hm
    have hm' := mem_of_mem_erase (mem_of_mem_erase hm)
    rcases mem_image.1 hm' with ⟨w, _, hw⟩
    have h1 : u e ∈ comp u v E w := by rw [hw, hCuv_eq]; exact mem_union_left _ ((mem_comp u v).2 (.refl _))
    have h2 : v e ∈ comp u v E w := by rw [hw, hCuv_eq]; exact mem_union_right _ ((mem_comp u v).2 (.refl _))
    exact h (reach_trans u v (reach_symm u v ((mem_comp u v).1 h1)) ((mem_comp u v).1 h2))
  have himg : compImg u v (insert e E) = insert Cuv (((compImg u v E).erase Cu).erase Cv) := by
    ext S
    simp only [compImg, mem_image, mem_univ, true_and, mem_insert, mem_erase]
    constructor
    · rintro ⟨w, rfl⟩
      by_cases hwu : Reach u v E w (u e)
      · left; exact (comp_eq_of_reach u v (reach_symm u v (reach_mono u v (subset_insert e E) hwu))).symm
      · by_cases hwv : Reach u v E w (v e)
        · left
          have h1 : Reach u v (insert e E) (u e) w :=
            reach_trans u v (.step (.refl _) e (mem_insert_self _ _) (Or.inl ⟨rfl, rfl⟩))
              (reach_symm u v (reach_mono u v (subset_insert e E) hwv))
          exact (comp_eq_of_reach u v h1).symm
        · right
          have hcw : comp u v (insert e E) w = comp u v E w := by
            ext z; simp only [mem_comp]
            exact ⟨reach_insert_disj u v hwu hwv, reach_mono u v (subset_insert e E)⟩
          rw [hcw]
          refine ⟨fun hEq => hwv ?_, fun hEq => hwu ?_, w, rfl⟩
          · have : v e ∈ comp u v E w := hEq ▸ (mem_comp u v).2 (.refl _)
            exact (mem_comp u v).1 this
          · have : u e ∈ comp u v E w := hEq ▸ (mem_comp u v).2 (.refl _)
            exact (mem_comp u v).1 this
    · rintro (rfl | ⟨hSCv, hSCu, w, _, rfl⟩)
      · exact ⟨u e, rfl⟩
      · have hwu : ¬ Reach u v E w (u e) := fun hr => hSCu (comp_eq_of_reach u v hr)
        have hwv : ¬ Reach u v E w (v e) := fun hr => hSCv (comp_eq_of_reach u v hr)
        refine ⟨w, ?_⟩
        ext z; simp only [mem_comp]
        exact ⟨reach_insert_disj u v hwu hwv, reach_mono u v (subset_insert e E)⟩
  rw [himg, Finset.card_insert_of_notMem hCuv_not,
      card_erase_of_mem (mem_erase.2 ⟨hne.symm, hCv⟩), card_erase_of_mem hCu]
  have hge2 : 2 ≤ (compImg u v E).card := by
    have : ({Cu, Cv} : Finset _).card ≤ (compImg u v E).card :=
      card_le_card (insert_subset_iff.2 ⟨hCu, singleton_subset_iff.2 hCv⟩)
    rw [card_pair hne] at this
    exact this
  omega

theorem compImg_card_add_card_ge (E : Finset (Fin n)) :
    n ≤ (compImg u v E).card + E.card := by
  induction E using Finset.induction with
  | empty => simp [compImg_empty]
  | @insert e E he ih =>
    rw [Finset.card_insert_of_notMem he]
    by_cases hr : Reach u v E (u e) (v e)
    · rw [compImg_insert_card_of_reach u v hr]; omega
    · have := compImg_insert_card_of_not_reach u v hr; omega

def Acyclic (E : Finset (Fin n)) : Prop :=
  ∀ e ∈ E, ¬ Reach u v (E.erase e) (u e) (v e)

theorem acyclic_subset {E₁ E₂ : Finset (Fin n)} (hsub : E₁ ⊆ E₂) (ha : Acyclic u v E₂) :
    Acyclic u v E₁ := fun e he hr =>
  ha e (hsub he) (reach_mono u v (erase_subset_erase e hsub) hr)

theorem acyclic_compImg_card {E : Finset (Fin n)} (ha : Acyclic u v E) :
    (compImg u v E).card + E.card = n := by
  induction E using Finset.induction with
  | empty => simp [compImg_empty]
  | @insert e E he ih =>
    have ha' : Acyclic u v E := acyclic_subset u v (subset_insert e E) ha
    have hnr : ¬ Reach u v E (u e) (v e) := by
      have := ha e (mem_insert_self e E)
      rwa [erase_insert he] at this
    have := compImg_insert_card_of_not_reach u v hnr
    rw [Finset.card_insert_of_notMem he]
    have := ih ha'
    omega

theorem acyclic_of_compImg_card {E : Finset (Fin n)}
    (heq : (compImg u v E).card + E.card = n) : Acyclic u v E := by
  intro e he hr
  have h1 : compImg u v E = compImg u v (E.erase e) := by
    have := compImg_insert_card_of_reach u v (E := E.erase e) hr
    rwa [insert_erase he] at this
  have hge := compImg_card_add_card_ge u v (E.erase e)
  rw [← h1, card_erase_of_mem he] at hge
  have hpos : 0 < E.card := card_pos.2 ⟨e, he⟩
  omega

theorem compImg_connected (hn : 0 < n) {E : Finset (Fin n)}
    (hc : ∀ a b : Fin n, Reach u v E a b) : (compImg u v E).card = 1 := by
  let z : Fin n := ⟨0, hn⟩
  have heq : compImg u v E = {Finset.univ} := by
    ext S
    simp only [compImg, mem_image, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      ext w; simp only [mem_comp, mem_univ, iff_true]; exact hc a w
    · rintro rfl
      refine ⟨z, ?_⟩
      ext w; simp only [mem_comp, mem_univ, iff_true]; exact hc z w
  rw [heq, card_singleton]

inductive ReachN (E : Finset (Fin n)) : ℕ → Fin n → Fin n → Prop
  | zero (a) : ReachN E 0 a a
  | head {k a b c} (i : Fin n) (hi : i ∈ E) (hab : edgeAdj u v i a b)
      (hbc : ReachN E k b c) : ReachN E (k + 1) a c

theorem reachN_to_reach {E : Finset (Fin n)} {k : ℕ} {a b : Fin n}
    (h : ReachN u v E k a b) : Reach u v E a b := by
  induction h with
  | zero => exact .refl _
  | head i hi hab _ ih => exact reach_trans u v (.step (.refl _) i hi hab) ih

theorem reach_to_reachN {E : Finset (Fin n)} {a b : Fin n}
    (h : Reach u v E a b) : ∃ k, ReachN u v E k a b := by
  have happend : ∀ {x y z : Fin n} {k : ℕ}, ReachN u v E k x y → ∀ i ∈ E, edgeAdj u v i y z →
      ReachN u v E (k + 1) x z := by
    intro x y z k hxy
    induction hxy with
    | zero => intro i hi hay; exact .head i hi hay (.zero z)
    | head j hj hab _ ih => intro i hi hyz; exact .head j hj hab (ih i hi hyz)
  induction h with
  | refl => exact ⟨0, .zero a⟩
  | step _ i hi hyz ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, happend hk i hi hyz⟩

noncomputable def sideW (T : Finset (Fin n)) (e : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => Reach u v (T.erase e) (u e) w)

theorem mem_sideW {T : Finset (Fin n)} {e w : Fin n} :
    w ∈ sideW u v T e ↔ Reach u v (T.erase e) (u e) w := by simp [sideW]

theorem u_mem_sideW {T : Finset (Fin n)} {e : Fin n} : u e ∈ sideW u v T e :=
  (mem_sideW u v).2 (.refl _)

theorem v_not_mem_sideW {T : Finset (Fin n)} (ha : Acyclic u v T) {e : Fin n} (he : e ∈ T) :
    v e ∉ sideW u v T e := fun h => ha e he ((mem_sideW u v).1 h)

theorem sideW_edge_eq {T : Finset (Fin n)} {e j : Fin n} (hj : j ∈ T.erase e) :
    u j ∈ sideW u v T e ↔ v j ∈ sideW u v T e := by
  simp only [mem_sideW]
  exact ⟨fun h => .step h j hj (Or.inl ⟨rfl, rfl⟩), fun h => .step h j hj (Or.inr ⟨rfl, rfl⟩)⟩

theorem cut_sideW_inter_tree {T : Finset (Fin n)} (ha : Acyclic u v T) {e : Fin n} (he : e ∈ T) :
    T ∩ cut u v (sideW u v T e) = {e} := by
  ext j
  simp only [mem_inter, mem_cut, mem_singleton]
  constructor
  · rintro ⟨hjT, h1 | h1⟩
    · by_contra hne
      have hj : j ∈ T.erase e := mem_erase.2 ⟨hne, hjT⟩
      exact h1.2 ((sideW_edge_eq u v hj).1 h1.1)
    · by_contra hne
      have hj : j ∈ T.erase e := mem_erase.2 ⟨hne, hjT⟩
      exact h1.2 ((sideW_edge_eq u v hj).2 h1.1)
  · rintro rfl
    exact ⟨he, Or.inl ⟨u_mem_sideW u v, v_not_mem_sideW u v ha he⟩⟩

theorem reach_tree_avoid {T : Finset (Fin n)} (hc : ∀ a b, Reach u v T a b)
    {e : Fin n} (w : Fin n) :
    Reach u v (T.erase e) (u e) w ∨ Reach u v (T.erase e) (v e) w := by
  have hreach := hc (u e) w
  induction hreach with
  | refl => exact Or.inl (.refl _)
  | step _ i hi hbc ih =>
    by_cases hie : i = e
    · subst hie
      rcases hbc with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact Or.inr (.refl _)
      · exact Or.inl (.refl _)
    · have hi' : i ∈ T.erase e := mem_erase.2 ⟨hie, hi⟩
      rcases ih with h1 | h1
      · exact Or.inl (.step h1 i hi' hbc)
      · exact Or.inr (.step h1 i hi' hbc)

theorem reachN_side_hit {T : Finset (Fin n)} (ha : Acyclic u v T)
    {e x x' : Fin n} (he : e ∈ T) (hxx' : edgeAdj u v e x x') :
    ∀ {m : ℕ} {a b : Fin n}, ReachN u v T m a b →
      (a ∈ sideW u v T e ↔ x' ∈ sideW u v T e) →
      (b ∈ sideW u v T e ↔ x ∈ sideW u v T e) →
      ∃ m' < m, ReachN u v T m' x b := by
  intro m
  induction m with
  | zero =>
    intro a b hab ha' hb'
    cases hab
    have hsep : x ∈ sideW u v T e ↔ x' ∉ sideW u v T e := by
      rcases hxx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [u_mem_sideW u v, v_not_mem_sideW u v ha he]
      · simp [u_mem_sideW u v, v_not_mem_sideW u v ha he]
    tauto
  | succ m₁ ih =>
    intro a b hab ha' hb'
    cases hab with
    | @head _ _ a₁ _ i hiT haa₁ ha₁b =>
      by_cases hie : i = e
      · subst hie
        have ha₁eq : a₁ = x := by
          rcases hxx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases haa₁ with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact absurd (ha'.1 (h1 ▸ u_mem_sideW u v)) (v_not_mem_sideW u v ha he)
          · exact h2.symm
          · exact h2.symm
          · exact absurd (ha'.2 (u_mem_sideW u v)) (fun hm => v_not_mem_sideW u v ha he (h1 ▸ hm))
        rw [ha₁eq] at ha₁b
        exact ⟨m₁, Nat.lt_succ_self m₁, ha₁b⟩
      · have hi' : i ∈ T.erase e := mem_erase.2 ⟨hie, hiT⟩
        have haa₁_eq : a ∈ sideW u v T e ↔ a₁ ∈ sideW u v T e := by
          rcases haa₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact sideW_edge_eq u v hi'
          · exact (sideW_edge_eq u v hi').symm
        obtain ⟨m', hm', hm'r⟩ := ih ha₁b (haa₁_eq.symm.trans ha') hb'
        exact ⟨m', Nat.lt_trans hm' (Nat.lt_succ_self m₁), hm'r⟩

theorem reachN_exists_edge_step {T : Finset (Fin n)} (ha : Acyclic u v T) :
    ∀ k : ℕ, ∀ x y : Fin n, ReachN u v T k x y → x ≠ y →
      ∃ e ∈ T, ∃ x' : Fin n, ∃ k' < k,
        edgeAdj u v e x x' ∧ (x ∈ sideW u v T e ↔ y ∉ sideW u v T e) ∧ ReachN u v T k' x' y := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro x y hxy hne
    cases k with
    | zero => cases hxy; exact absurd rfl hne
    | succ k' =>
      cases hxy with
      | head e heT hxx' hx'y =>
        rename_i x'
        have hsep_xx' : x ∈ sideW u v T e ↔ x' ∉ sideW u v T e := by
          rcases hxx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [u_mem_sideW u v, v_not_mem_sideW u v ha heT]
        by_cases hxy_sep : x ∈ sideW u v T e ↔ y ∉ sideW u v T e
        · exact ⟨e, heT, x', k', Nat.lt_succ_self k', hxx', hxy_sep, hx'y⟩
        · have hy_same : y ∈ sideW u v T e ↔ x ∈ sideW u v T e := by tauto
          obtain ⟨m', hm', hmr⟩ := reachN_side_hit u v ha heT hxx' hx'y Iff.rfl hy_same
          obtain ⟨e₂, he₂, x₂, k₂, hk₂, hadj₂, hsep₂, hr₂⟩ :=
            ih m' (Nat.lt_trans hm' (Nat.lt_succ_self k')) x y hmr hne
          exact ⟨e₂, he₂, x₂, k₂, Nat.lt_trans hk₂ (Nat.lt_trans hm' (Nat.lt_succ_self k')),
            hadj₂, hsep₂, hr₂⟩

inductive ReachRel (R : Fin n → Fin n → Prop) : Fin n → Fin n → Prop
  | refl (a) : ReachRel R a a
  | step {a b c} : ReachRel R a b → R b c → ReachRel R a c

theorem reachRel_trans {R : Fin n → Fin n → Prop} {a b c : Fin n}
    (hab : ReachRel R a b) (hbc : ReachRel R b c) : ReachRel R a c := by
  induction hbc with
  | refl => exact hab
  | step _ hcd ih => exact .step ih hcd

theorem reach_dir_of_tree {T : Finset (Fin n)} (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (R : Fin n → Fin n → Prop)
    (x y : Fin n)
    (hstep : ∀ e ∈ T, (x ∈ sideW u v T e ↔ y ∉ sideW u v T e) →
      ∀ a b : Fin n, edgeAdj u v e a b → (a ∈ sideW u v T e ↔ x ∈ sideW u v T e) → R a b) :
    ReachRel R x y := by
  obtain ⟨k, hk⟩ := reach_to_reachN u v (hc x y)
  induction k using Nat.strong_induction_on generalizing x hstep with
  | ind k ih =>
    by_cases hxy : x = y
    · subst hxy; exact .refl x
    · obtain ⟨e, heT, x', k', hk', hxx', hsep, hx'y⟩ :=
        reachN_exists_edge_step u v ha k x y hk hxy
      have hRx : R x x' := hstep e heT hsep x x' hxx' Iff.rfl
      have hsub_ih : ReachRel R x' y := by
        refine ih k' hk' x' (fun e' he' hsep' a b hab ha' => ?_) hx'y
        have hne' : e' ≠ e := by
          intro heq; subst heq
          have hx_sep : x ∈ sideW u v T e' ↔ x' ∉ sideW u v T e' := by
            rcases hxx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨fun _ => v_not_mem_sideW u v ha heT, fun _ => u_mem_sideW u v⟩
            · exact ⟨fun h => absurd h (v_not_mem_sideW u v ha heT), fun hn => absurd (u_mem_sideW u v) hn⟩
          by_cases hx : x ∈ sideW u v T e'
          · exact hx_sep.1 hx (hsep'.2 (hsep.1 hx))
          · exact hx (hx_sep.2 (fun hx' => by
              by_cases hy : y ∈ sideW u v T e'
              · exact (hsep'.1 hx') hy
              · exact hx (hsep.2 hy)))
        have he_erase : e ∈ T.erase e' := mem_erase.2 ⟨hne'.symm, heT⟩
        have hxx'_eq : x ∈ sideW u v T e' ↔ x' ∈ sideW u v T e' := by
          rcases hxx' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact sideW_edge_eq u v he_erase
          · exact (sideW_edge_eq u v he_erase).symm
        exact hstep e' he' (hxx'_eq.trans hsep') a b hab (ha'.trans hxx'_eq.symm)
      exact reachRel_trans (.step (.refl x) hRx) hsub_ih

theorem exists_tree (hn : 0 < n)
    (hconn : ∀ U : Finset (Fin n), U.Nonempty → U ≠ Finset.univ → (cut u v U).Nonempty) :
    ∃ T : Finset (Fin n), (∀ a b, Reach u v T a b) ∧ Acyclic u v T ∧ T.card + 1 = n := by
  let S := Finset.univ.powerset.filter (fun F : Finset (Fin n) => ∀ a b : Fin n, Reach u v F a b)
  have hS : Finset.univ ∈ S := mem_filter.2 ⟨mem_powerset.2 (Subset.refl _), connected_univ u v hconn⟩
  obtain ⟨T, hTS, hTmin⟩ := S.exists_min_image Finset.card ⟨Finset.univ, hS⟩
  have hTc : ∀ a b, Reach u v T a b := (mem_filter.1 hTS).2
  have hTa : Acyclic u v T := by
    intro e he hr
    have heS : T.erase e ∈ S := mem_filter.2 ⟨mem_powerset.2 (subset_univ _), fun a b =>
      reach_insert_of_reach u v (E := T.erase e) hr (by rw [insert_erase he]; exact hTc a b)⟩
    have hle := hTmin (T.erase e) heS
    have hlt := card_erase_lt_of_mem he
    omega
  refine ⟨T, hTc, hTa, ?_⟩
  have hcard := acyclic_compImg_card u v hTa
  rw [compImg_connected u v hn hTc] at hcard
  omega

theorem unique_extra_edge {T : Finset (Fin n)} (hcard : T.card + 1 = n) :
    ∃ e₀ : Fin n, e₀ ∉ T ∧ Finset.univ = insert e₀ T := by
  have hc : (Finset.univ \ T).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨e₀, he₀⟩ := card_eq_one.1 hc
  have hm : e₀ ∈ Finset.univ \ T := he₀ ▸ mem_singleton_self e₀
  refine ⟨e₀, (mem_sdiff.1 hm).2, ?_⟩
  ext x
  by_cases hx : x ∈ T
  · simp [hx]
  · have : x ∈ Finset.univ \ T := mem_sdiff.2 ⟨mem_univ x, hx⟩
    rw [he₀, mem_singleton] at this
    simp [this]

noncomputable def cycleEdges (T : Finset (Fin n)) (e₀ : Fin n) : Finset (Fin n) :=
  insert e₀ (T.filter (fun e => decide (u e₀ ∈ sideW u v T e) != decide (v e₀ ∈ sideW u v T e)))

def isCycleVert (C : Finset (Fin n)) (c : Fin n) : Prop :=
  ∃ e ∈ C, c = u e ∨ c = v e

theorem mem_cycleEdges_iff {T : Finset (Fin n)} {e₀ e : Fin n} :
    e ∈ cycleEdges u v T e₀ ↔
      e = e₀ ∨ (e ∈ T ∧ (u e₀ ∈ sideW u v T e ↔ v e₀ ∉ sideW u v T e)) := by
  simp only [cycleEdges, mem_insert, mem_filter]
  constructor
  · rintro (rfl | ⟨he, hdiff⟩)
    · exact Or.inl rfl
    · right; refine ⟨he, ?_⟩
      cases h1 : decide (u e₀ ∈ sideW u v T e) <;> cases h2 : decide (v e₀ ∈ sideW u v T e) <;>
        simp_all
  · rintro (rfl | ⟨he, hsep⟩)
    · exact Or.inl rfl
    · right; refine ⟨he, ?_⟩
      cases h1 : decide (u e₀ ∈ sideW u v T e) <;> cases h2 : decide (v e₀ ∈ sideW u v T e) <;>
        simp_all

theorem cycleEdge_erase_conn {T : Finset (Fin n)} {e₀ : Fin n}
    (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T)
    {e : Fin n} (heC : e ∈ cycleEdges u v T e₀) :
    ∀ a b, Reach u v (Finset.univ.erase e) a b := by
  rcases (mem_cycleEdges_iff u v).1 heC with heq | ⟨heT, hsep⟩
  · subst heq
    have hsub : T ⊆ Finset.univ.erase e := fun j hj =>
      mem_erase.2 ⟨fun h => he₀ (h ▸ hj), mem_univ j⟩
    exact fun a b => reach_mono u v hsub (hc a b)
  · have hsub_mid : T.erase e ⊆ Finset.univ.erase e := by
      intro j hj
      rw [huniv]
      exact mem_erase.2 ⟨(mem_erase.1 hj).1, mem_insert_of_mem (mem_erase.1 hj).2⟩
    have hstep_mid : ∀ a b, Reach u v (T.erase e) a b → Reach u v (Finset.univ.erase e) a b :=
      fun _ _ => reach_mono u v hsub_mid
    have he₀_er : e₀ ∈ Finset.univ.erase e := mem_erase.2 ⟨fun heq => he₀ (heq ▸ heT), mem_univ _⟩
    have huv_er : Reach u v (Finset.univ.erase e) (u e) (v e) := by
      have hs_u : Reach u v (T.erase e) (u e) (u e₀) ∨ Reach u v (T.erase e) (v e) (u e₀) :=
        reach_tree_avoid u v hc (u e₀)
      have hs_v : Reach u v (T.erase e) (u e) (v e₀) ∨ Reach u v (T.erase e) (v e) (v e₀) :=
        reach_tree_avoid u v hc (v e₀)
      have hu_not_v : ¬ Reach u v (T.erase e) (u e) (v e₀) ∨ ¬ Reach u v (T.erase e) (u e) (u e₀) := by
        by_cases h : u e₀ ∈ sideW u v T e
        · left; exact fun hr => (hsep.1 h) ((mem_sideW u v).2 hr)
        · right; exact fun hr => h ((mem_sideW u v).2 hr)
      rcases hu_not_v with hnv | hnu
      · have h1 : Reach u v (T.erase e) (u e) (u e₀) := by
          rcases hs_u with hu | hv
          · exact hu
          · exfalso
            have hu0 : u e₀ ∉ sideW u v T e := fun hu' =>
              ha e heT (reach_trans u v ((mem_sideW u v).1 hu') (reach_symm u v hv))
            have hv0 : v e₀ ∉ sideW u v T e := fun hv' => hnv ((mem_sideW u v).1 hv')
            exact hu0 (hsep.2 hv0)
        have h2 : Reach u v (T.erase e) (v e) (v e₀) := by
          rcases hs_v with hu | hv
          · exact absurd hu hnv
          · exact hv
        exact reach_trans u v (hstep_mid _ _ h1)
          (reach_trans u v (.step (.refl _) e₀ he₀_er (Or.inl ⟨rfl, rfl⟩))
            (reach_symm u v (hstep_mid _ _ h2)))
      · have h2 : Reach u v (T.erase e) (u e) (v e₀) := by
          rcases hs_v with hu | hv
          · exact hu
          · exfalso
            have hv0 : v e₀ ∉ sideW u v T e := fun hv' =>
              ha e heT (reach_trans u v ((mem_sideW u v).1 hv') (reach_symm u v hv))
            have hu0 : u e₀ ∉ sideW u v T e := fun hu' => hnu ((mem_sideW u v).1 hu')
            exact hu0 (hsep.2 hv0)
        have h1 : Reach u v (T.erase e) (v e) (u e₀) := by
          rcases hs_u with hu | hv
          · exact absurd hu hnu
          · exact hv
        exact reach_trans u v (hstep_mid _ _ h2)
          (reach_trans u v (.step (.refl _) e₀ he₀_er (Or.inr ⟨rfl, rfl⟩))
            (reach_symm u v (hstep_mid _ _ h1)))
    intro a b
    have hrT := hc a b
    induction hrT with
    | refl => exact .refl _
    | step _ i hi hxy ih =>
      by_cases hie : i = e
      · subst hie
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact reach_trans u v ih huv_er
        · exact reach_trans u v ih (reach_symm u v huv_er)
      · exact .step ih i (mem_erase.2 ⟨hie, mem_univ i⟩) hxy

theorem cycleEdge_erase_tree (hn : 0 < n) {T : Finset (Fin n)} {e₀ : Fin n}
    (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T)
    {e : Fin n} (heC : e ∈ cycleEdges u v T e₀) :
    (∀ a b, Reach u v (Finset.univ.erase e) a b) ∧ Acyclic u v (Finset.univ.erase e) := by
  have hc' := cycleEdge_erase_conn u v hc ha he₀ huniv heC
  refine ⟨hc', acyclic_of_compImg_card u v ?_⟩
  rw [compImg_connected u v hn hc', card_erase_of_mem (mem_univ e), Finset.card_univ, Fintype.card_fin]
  omega

theorem bridges_eq_sdiff_cycle {T : Finset (Fin n)} {e₀ : Fin n}
    (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T) :
    bridges u v = Finset.univ \ cycleEdges u v T e₀ := by
  ext e
  simp only [bridges, mem_filter, mem_univ, true_and, mem_sdiff]
  constructor
  · rintro ⟨U, hU⟩ heC
    have hconn_er := cycleEdge_erase_conn u v hc ha he₀ huniv heC
    have hcute : e ∈ cut u v U := hU ▸ mem_singleton_self e
    have hreach : ∃ j ∈ Finset.univ.erase e, j ∈ cut u v U := by
      rcases (mem_cut u v).1 hcute with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact reach_cut u v (hconn_er (u e) (v e)) U h1 h2
      · exact reach_cut u v (hconn_er (v e) (u e)) U h1 h2
    obtain ⟨j, hjer, hjU⟩ := hreach
    rw [hU, mem_singleton] at hjU
    exact (mem_erase.1 hjer).1 hjU
  · intro hnotC
    have heT : e ∈ T := by
      have heU : e ∈ insert e₀ T := huniv ▸ mem_univ e
      rcases mem_insert.1 heU with rfl | h
      · exact absurd ((mem_cycleEdges_iff u v).2 (Or.inl rfl)) hnotC
      · exact h
    refine ⟨sideW u v T e, ?_⟩
    ext j
    simp only [mem_singleton]
    constructor
    · intro hj
      have hjU : j = e₀ ∨ j ∈ T := by rw [← mem_insert, ← huniv]; exact mem_univ j
      rcases hjU with rfl | hjT
      · exfalso; apply hnotC; rw [mem_cycleEdges_iff]; right; refine ⟨heT, ?_⟩
        rcases (mem_cut u v).1 hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all
      · have hjinter : j ∈ T ∩ cut u v (sideW u v T e) := mem_inter.2 ⟨hjT, hj⟩
        rw [cut_sideW_inter_tree u v ha heT, mem_singleton] at hjinter
        exact hjinter
    · rintro rfl
      exact (mem_cut u v).2 (Or.inl ⟨u_mem_sideW u v, v_not_mem_sideW u v ha heT⟩)

theorem cut_sideW_cycleEdge {T : Finset (Fin n)} {e₀ : Fin n}
    (ha : Acyclic u v T) (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T)
    {e : Fin n} (heT : e ∈ T) (heC : e ∈ cycleEdges u v T e₀) :
    cut u v (sideW u v T e) = {e₀, e} := by
  have he₀_sep : e₀ ∈ cut u v (sideW u v T e) := by
    rcases (mem_cycleEdges_iff u v).1 heC with rfl | ⟨_, hsep⟩
    · exact absurd heT he₀
    · rw [mem_cut]
      by_cases hu : u e₀ ∈ sideW u v T e
      · exact Or.inl ⟨hu, hsep.1 hu⟩
      · exact Or.inr ⟨by by_contra hv; exact hu (hsep.2 hv), hu⟩
  ext j
  simp only [mem_insert, mem_singleton]
  constructor
  · intro hj
    have hjU : j = e₀ ∨ j ∈ T := by rw [← mem_insert, ← huniv]; exact mem_univ j
    rcases hjU with rfl | hjT
    · exact Or.inl rfl
    · right
      have := cut_sideW_inter_tree u v ha heT
      have hj' : j ∈ T ∩ cut u v (sideW u v T e) := mem_inter.2 ⟨hjT, hj⟩
      rw [this, mem_singleton] at hj'
      exact hj'
  · rintro (rfl | rfl)
    · exact he₀_sep
    · exact (mem_cut u v).2 (Or.inl ⟨u_mem_sideW u v, v_not_mem_sideW u v ha heT⟩)

theorem cut_two_cycleEdges {T : Finset (Fin n)} {e₀ : Fin n}
    (ha : Acyclic u v T) (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T)
    {e₁ e₂ : Fin n} (h₁ : e₁ ∈ cycleEdges u v T e₀) (h₂ : e₂ ∈ cycleEdges u v T e₀)
    (hne : e₁ ≠ e₂) : ∃ U : Finset (Fin n), cut u v U = {e₁, e₂} := by
  have hmemT : ∀ e ∈ cycleEdges u v T e₀, e = e₀ ∨ e ∈ T := by
    intro e he
    have : e ∈ insert e₀ T := huniv ▸ mem_univ e
    exact mem_insert.1 this
  by_cases h10 : e₁ = e₀
  · subst h10
    have he₂T : e₂ ∈ T := (hmemT e₂ h₂).resolve_left hne.symm
    exact ⟨sideW u v T e₂, cut_sideW_cycleEdge u v ha he₀ huniv he₂T h₂⟩
  · by_cases h20 : e₂ = e₀
    · subst h20
      have he₁T : e₁ ∈ T := (hmemT e₁ h₁).resolve_left h10
      refine ⟨sideW u v T e₁, ?_⟩
      rw [cut_sideW_cycleEdge u v ha he₀ huniv he₁T h₁]
      ext j; simp only [mem_insert, mem_singleton]; tauto
    · have he₁T : e₁ ∈ T := (hmemT e₁ h₁).resolve_left h10
      have he₂T : e₂ ∈ T := (hmemT e₂ h₂).resolve_left h20
      refine ⟨symmDiff (sideW u v T e₁) (sideW u v T e₂), ?_⟩
      rw [cut_symmDiff u v, cut_sideW_cycleEdge u v ha he₀ huniv he₁T h₁,
        cut_sideW_cycleEdge u v ha he₀ huniv he₂T h₂]
      ext j
      simp only [mem_symmDiff, mem_insert, mem_singleton]
      by_cases hj0 : j = e₀ <;> by_cases hj1 : j = e₁ <;> by_cases hj2 : j = e₂ <;> simp_all

theorem tree_erase_side_conn {T : Finset (Fin n)} (hc : ∀ a b, Reach u v T a b)
    {e : Fin n} {w : Fin n} (hw : w ∉ sideW u v T e) :
    Reach u v (T.erase e) (v e) w := by
  rcases reach_tree_avoid u v hc w with h1 | h2
  · exact absurd ((mem_sideW u v).2 h1) hw
  · exact h2

theorem reach_avoid_subset_outside {T : Finset (Fin n)} {e e₁ : Fin n}
    (houtside : u e₁ ∉ sideW u v T e ∧ v e₁ ∉ sideW u v T e) :
    ∀ {a b : Fin n}, Reach u v (T.erase e) a b → a ∈ sideW u v T e →
      Reach u v (T.erase e₁) a b := by
  intro a b hr ha
  induction hr with
  | refl => exact .refl a
  | @step y z hxy i hi hyz ih =>
    have hy : y ∈ sideW u v T e := by
      have := (mem_sideW u v).1 ha
      exact (mem_sideW u v).2 (reach_trans u v this hxy)
    have hne : i ≠ e₁ := by
      intro heq; subst heq
      rcases hyz with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact houtside.1 hy
      · exact houtside.2 hy
    exact .step ih i (mem_erase.2 ⟨hne, (mem_erase.1 hi).2⟩) hyz

theorem reach_avoid_subset_inside {T : Finset (Fin n)} {e e₁ : Fin n}
    (hinside : u e₁ ∈ sideW u v T e ∧ v e₁ ∈ sideW u v T e) :
    ∀ {a b : Fin n}, Reach u v (T.erase e) a b → a ∉ sideW u v T e →
      Reach u v (T.erase e₁) a b := by
  intro a b hr ha
  induction hr with
  | refl => exact .refl a
  | @step y z hxy i hi hyz ih =>
    have hy : y ∉ sideW u v T e := by
      intro hy'
      have hyw := (mem_sideW u v).1 hy'
      have hyx := reach_trans u v hyw (reach_symm u v hxy)
      exact ha ((mem_sideW u v).2 hyx)
    have hne : i ≠ e₁ := by
      intro heq; subst heq
      rcases hyz with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hy hinside.1
      · exact hy hinside.2
    exact .step ih i (mem_erase.2 ⟨hne, (mem_erase.1 hi).2⟩) hyz

theorem cycleVert_sideW_bridge {T : Finset (Fin n)} {e₀ : Fin n}
    (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T)
    {e : Fin n} (heB : e ∈ bridges u v) {c : Fin n} (hcC : isCycleVert u v (cycleEdges u v T e₀) c) :
    c ∈ sideW u v T e ↔ u e₀ ∈ sideW u v T e := by
  have hdiff := bridges_eq_sdiff_cycle u v hc ha he₀ huniv
  have heNotC : e ∉ cycleEdges u v T e₀ := by
    rw [hdiff] at heB; exact (mem_sdiff.1 heB).2
  have heT : e ∈ T := by
    have : e ∈ Finset.univ := mem_univ e
    rw [huniv] at this
    rcases mem_insert.1 this with rfl | h
    · exact absurd ((mem_cycleEdges_iff u v).2 (Or.inl rfl)) heNotC
    · exact h
  have he₀_same : u e₀ ∈ sideW u v T e ↔ v e₀ ∈ sideW u v T e := by
    by_contra hsep
    apply heNotC
    rw [mem_cycleEdges_iff]
    right; exact ⟨heT, by tauto⟩
  have hcommon : ∀ e₁ : Fin n, e₁ ∈ cycleEdges u v T e₀ → e₁ ≠ e₀ →
      (u e₁ ∈ sideW u v T e ↔ u e₀ ∈ sideW u v T e) := by
    intro e₁ he₁C hne0
    have he₁_Tsep : e₁ ∈ T ∧ (u e₀ ∈ sideW u v T e₁ ↔ v e₀ ∉ sideW u v T e₁) :=
      ((mem_cycleEdges_iff u v).1 he₁C).resolve_left hne0
    have hsep₁ := he₁_Tsep.2
    have hne : e₁ ≠ e := fun heq => heNotC (heq ▸ he₁C)
    have he₁_eq : u e₁ ∈ sideW u v T e ↔ v e₁ ∈ sideW u v T e :=
      sideW_edge_eq u v (mem_erase.2 ⟨hne, he₁_Tsep.1⟩)
    by_contra hdiff_side
    have hu0_eq : u e₀ ∈ sideW u v T e₁ ↔ v e₀ ∈ sideW u v T e₁ := by
      by_cases hu1 : u e₁ ∈ sideW u v T e
      · have hv1 : v e₁ ∈ sideW u v T e := he₁_eq.1 hu1
        have hu0 : u e₀ ∉ sideW u v T e := fun h => hdiff_side ⟨fun _ => h, fun _ => hu1⟩
        have hv0 : v e₀ ∉ sideW u v T e := fun h => hu0 (he₀_same.2 h)
        have r_u0 := reach_avoid_subset_inside u v ⟨hu1, hv1⟩
          (tree_erase_side_conn u v hc (e := e) hu0) (v_not_mem_sideW u v ha heT)
        have r_v0 := reach_avoid_subset_inside u v ⟨hu1, hv1⟩
          (tree_erase_side_conn u v hc (e := e) hv0) (v_not_mem_sideW u v ha heT)
        simp only [mem_sideW]
        exact ⟨fun h => reach_trans u v (reach_trans u v h (reach_symm u v r_u0)) r_v0,
          fun h => reach_trans u v (reach_trans u v h (reach_symm u v r_v0)) r_u0⟩
      · have hv1 : v e₁ ∉ sideW u v T e := fun h => hu1 (he₁_eq.2 h)
        have hu0 : u e₀ ∈ sideW u v T e := by
          by_contra hn; exact hdiff_side ⟨fun h => absurd h hu1, fun h => absurd h hn⟩
        have hv0 : v e₀ ∈ sideW u v T e := he₀_same.1 hu0
        have r_u0 := reach_avoid_subset_outside u v ⟨hu1, hv1⟩ ((mem_sideW u v).1 hu0) (u_mem_sideW u v)
        have r_v0 := reach_avoid_subset_outside u v ⟨hu1, hv1⟩ ((mem_sideW u v).1 hv0) (u_mem_sideW u v)
        simp only [mem_sideW]
        exact ⟨fun h => reach_trans u v (reach_trans u v h (reach_symm u v r_u0)) r_v0,
          fun h => reach_trans u v (reach_trans u v h (reach_symm u v r_v0)) r_u0⟩
    by_cases h : u e₀ ∈ sideW u v T e₁
    · exact (hsep₁.1 h) (hu0_eq.1 h)
    · exact h (hsep₁.2 (fun hv => h (hu0_eq.2 hv)))
  rcases hcC with ⟨e₁, he₁C, rfl | rfl⟩
  · by_cases h0 : e₁ = e₀
    · subst h0; exact Iff.rfl
    · exact hcommon e₁ he₁C h0
  · by_cases h0 : e₁ = e₀
    · subst h0; exact he₀_same.symm
    · have hne : e₁ ≠ e := fun heq => heNotC (heq ▸ he₁C)
      have he₁T : e₁ ∈ T := (((mem_cycleEdges_iff u v).1 he₁C).resolve_left h0).1
      have he₁_eq : u e₁ ∈ sideW u v T e ↔ v e₁ ∈ sideW u v T e :=
        sideW_edge_eq u v (mem_erase.2 ⟨hne, he₁T⟩)
      exact he₁_eq.symm.trans (hcommon e₁ he₁C h0)

theorem reach_bridges_cycleVert {T : Finset (Fin n)} {e₀ : Fin n}
    (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T) (w : Fin n) :
    ∃ c : Fin n, isCycleVert u v (cycleEdges u v T e₀) c ∧ Reach u v (bridges u v) c w := by
  have hdiff := bridges_eq_sdiff_cycle u v hc ha he₀ huniv
  have h0 : isCycleVert u v (cycleEdges u v T e₀) (u e₀) :=
    ⟨e₀, (mem_cycleEdges_iff u v).2 (Or.inl rfl), Or.inl rfl⟩
  have hr := hc (u e₀) w
  induction hr with
  | refl => exact ⟨u e₀, h0, .refl _⟩
  | @step y z _ i hiT hyz ih =>
    by_cases hiC : i ∈ cycleEdges u v T e₀
    · refine ⟨z, ⟨i, hiC, ?_⟩, .refl z⟩
      rcases hyz with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> [exact Or.inr rfl; exact Or.inl rfl]
    · have hiB : i ∈ bridges u v := by
        rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ i, hiC⟩
      rcases ih with ⟨c, hcC, hcy⟩
      exact ⟨c, hcC, .step hcy i hiB hyz⟩

theorem cycle_connected {T : Finset (Fin n)} {e₀ : Fin n}
    (hc : ∀ a b, Reach u v T a b) (ha : Acyclic u v T)
    (he₀ : e₀ ∉ T) (huniv : Finset.univ = insert e₀ T)
    {c₁ c₂ : Fin n} (hc₁ : isCycleVert u v (cycleEdges u v T e₀) c₁)
    (hc₂ : isCycleVert u v (cycleEdges u v T e₀) c₂) :
    Reach u v (cycleEdges u v T e₀) c₁ c₂ := by
  have hto0 : ∀ c, isCycleVert u v (cycleEdges u v T e₀) c →
      Reach u v (cycleEdges u v T e₀) c (u e₀) := by
    intro c hcC
    have hdiff := bridges_eq_sdiff_cycle u v hc ha he₀ huniv
    let R : Fin n → Fin n → Prop := fun a b => ∃ i ∈ cycleEdges u v T e₀, edgeAdj u v i a b
    have hrr := reach_dir_of_tree u v hc ha R c (u e₀) fun e heT hsep a b hab _ => by
      have heNotB : e ∉ bridges u v := fun heB => by
        have := cycleVert_sideW_bridge u v hc ha he₀ huniv heB hcC
        tauto
      have heC : e ∈ cycleEdges u v T e₀ := by
        by_contra hnot
        exact heNotB (by rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ e, hnot⟩)
      exact ⟨e, heC, hab⟩
    have htoReach : ∀ a b, ReachRel R a b → Reach u v (cycleEdges u v T e₀) a b := by
      intro a b hrr'
      induction hrr' with
      | refl => exact .refl _
      | step _ hstep ih =>
        rcases hstep with ⟨i, hiC, hab⟩
        exact .step ih i hiC hab
    exact htoReach c (u e₀) hrr
  exact reach_trans u v (hto0 c₁ hc₁) (reach_symm u v (hto0 c₂ hc₂))

/-! Direction 1 & Direction 2 -/

def pass (p : Fin n → Bool × Bool) (x : Finset (Fin n)) : Prop :=
  ∀ i : Fin n, (decide (u i ∈ x), decide (v i ∈ x)) ≠ p i

theorem dir_rhs_to_lhs (hn : 0 < n)
    (hconn : ∀ U : Finset (Fin n), U.Nonempty → U ≠ Finset.univ → (cut u v U).Nonempty)
    (S : Finset (Fin n))
    (hrhs : ∀ a ∈ S, ∀ b ∈ S, ∀ U : Finset (Fin n), a ∈ U → b ∉ U → (bridges u v ∩ cut u v U).Nonempty)
    (A B : Finset (Finset (Fin n))) (hsat : ∀ p, (∃ x ∈ A, pass u v p x) ↔ (∃ x ∈ B, pass u v p x))
    (z : Finset (Fin n)) (_ : z ⊆ S) :
    (∃ x ∈ A, x ∩ S = z) ↔ ∃ x ∈ B, x ∩ S = z := by
  suffices hgen : ∀ A' B' : Finset (Finset (Fin n)),
      (∀ p, (∃ x ∈ A', pass u v p x) → (∃ x ∈ B', pass u v p x)) →
      ∀ x₀ ∈ A', x₀ ∩ S = z → ∃ x ∈ B', x ∩ S = z by
    exact ⟨fun ⟨x₀, hx₀A, hx₀z⟩ => hgen A B (fun p h => (hsat p).1 h) x₀ hx₀A hx₀z,
      fun ⟨x₀, hx₀B, hx₀z⟩ => hgen B A (fun p h => (hsat p).2 h) x₀ hx₀B hx₀z⟩
  intro A' B' hAB x₀ hx₀A hx₀z
  by_cases hS : S = ∅
  · subst hS
    let p : Fin n → Bool × Bool := fun i => (!(decide (u i ∈ x₀)), !(decide (v i ∈ x₀)))
    have hp0 : pass u v p x₀ := fun i h => by
      have h1 := congrArg Prod.fst h
      cases hdu : decide (u i ∈ x₀) <;> simp_all [p]
    obtain ⟨x, hxB, _⟩ := hAB p ⟨x₀, hx₀A, hp0⟩
    refine ⟨x, hxB, ?_⟩
    simp [← hx₀z]
  · obtain ⟨s₀, hs₀⟩ := Finset.nonempty_iff_ne_empty.2 hS
    obtain ⟨T, hTc, hTa, hTcard⟩ := exists_tree u v hn hconn
    obtain ⟨e₀, he₀, huniv⟩ := unique_extra_edge hTcard
    have hdiff := bridges_eq_sdiff_cycle u v hTc hTa he₀ huniv
    obtain ⟨r, hrC, hrs₀⟩ := reach_bridges_cycleVert u v hTc hTa he₀ huniv s₀
    have hSb : ∀ s ∈ S, Reach u v (bridges u v) s r := by
      intro s hs
      have hs0s : Reach u v (bridges u v) s₀ s := by
        by_contra hno
        let U := Finset.univ.filter (Reach u v (bridges u v) s₀)
        have hU0 : s₀ ∈ U := mem_filter.2 ⟨mem_univ _, .refl _⟩
        have hUs : s ∉ U := fun h => hno (mem_filter.1 h).2
        obtain ⟨i, hi⟩ := hrhs s₀ hs₀ s hs U hU0 hUs
        rcases mem_inter.1 hi with ⟨hiB, hiCut⟩
        rcases (mem_cut u v).1 hiCut with ⟨huU, hvU⟩ | ⟨hvU, huU⟩
        · exact hvU (mem_filter.2 ⟨mem_univ _, .step (mem_filter.1 huU).2 i hiB (Or.inl ⟨rfl, rfl⟩)⟩)
        · exact huU (mem_filter.2 ⟨mem_univ _, .step (mem_filter.1 hvU).2 i hiB (Or.inr ⟨rfl, rfl⟩)⟩)
      exact reach_trans u v (reach_symm u v hs0s) (reach_symm u v hrs₀)
    let b : Fin n → Bool := fun w => decide (w ∈ x₀)
    let p : Fin n → Bool × Bool := fun i =>
      if i = e₀ then (!(b (u e₀)), !(b (v e₀)))
      else if i ∈ cycleEdges u v T e₀ then
        if r ∈ sideW u v T i then (!(b (u i)), b (v i)) else (b (u i), !(b (v i)))
      else if i ∈ T then
        if r ∈ sideW u v T i then (b (u i), !(b (v i))) else (!(b (u i)), b (v i))
      else (!(b (u i)), !(b (v i)))
    have hp0 : pass u v p x₀ := by
      intro i h
      dsimp only [p] at h
      split_ifs at h with h1 h2 h3 h4 h5
      all_goals
        have h1f := congrArg Prod.fst h
        have h2f := congrArg Prod.snd h
        cases hdu : decide (u i ∈ x₀) <;> cases hdv : decide (v i ∈ x₀) <;> simp_all [b]
    obtain ⟨x, hxB, hpx⟩ := hAB p ⟨x₀, hx₀A, hp0⟩
    have hstep_pass : ∀ i : Fin n, i ∈ T →
        (i ∈ cycleEdges u v T e₀ →
          ∀ a c : Fin n, edgeAdj u v i a c → (a ∈ sideW u v T i ↔ r ∈ sideW u v T i) →
            decide (a ∈ x) = !(b a) → decide (c ∈ x) = !(b c)) ∧
        (i ∈ bridges u v →
          ∀ a c : Fin n, edgeAdj u v i a c → (a ∈ sideW u v T i ↔ r ∉ sideW u v T i) →
            decide (a ∈ x) = !(b a) → decide (c ∈ x) = !(b c)) := by
      intro i hiT
      have hne0 : i ≠ e₀ := fun heq => he₀ (heq ▸ hiT)
      have hpi := hpx i
      dsimp only [p] at hpi
      rw [if_neg hne0] at hpi
      constructor
      · intro hiC a c hac ha ha_bad
        rw [if_pos hiC] at hpi
        rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hrW : r ∈ sideW u v T i := ha.1 (u_mem_sideW u v)
          rw [if_pos hrW] at hpi
          cases hdc : decide (v i ∈ x) <;> cases hdb : b (v i) <;> simp_all [b]
        · have hrnW : r ∉ sideW u v T i := fun hw => v_not_mem_sideW u v hTa hiT (ha.2 hw)
          rw [if_neg hrnW] at hpi
          cases hdc : decide (u i ∈ x) <;> cases hdb : b (u i) <;> simp_all [b]
      · intro hiB a c hac ha ha_bad
        have hnotC : i ∉ cycleEdges u v T e₀ := by
          rw [hdiff] at hiB; exact (mem_sdiff.1 hiB).2
        rw [if_neg hnotC, if_pos hiT] at hpi
        rcases hac with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · have hrnW : r ∉ sideW u v T i := ha.1 (u_mem_sideW u v)
          rw [if_neg hrnW] at hpi
          cases hdc : decide (v i ∈ x) <;> cases hdb : b (v i) <;> simp_all [b]
        · have hrW : r ∈ sideW u v T i := by
            by_contra hnr
            exact v_not_mem_sideW u v hTa hiT (ha.2 hnr)
          rw [if_pos hrW] at hpi
          cases hdc : decide (u i ∈ x) <;> cases hdb : b (u i) <;> simp_all [b]
    let BadR : Fin n → Fin n → Prop := fun a c => decide (a ∈ x) = !(b a) → decide (c ∈ x) = !(b c)
    have himpl_tree : ∀ a₁ a₂ : Fin n, ReachRel BadR a₁ a₂ → BadR a₁ a₂ := by
      intro a₁ a₂ hrr
      induction hrr with
      | refl => exact id
      | step _ hs ih => exact fun ha => hs (ih ha)
    have hbad_r_u0 : decide (r ∈ x) = !(b r) → decide (u e₀ ∈ x) = !(b (u e₀)) := by
      have hrr := reach_dir_of_tree u v hTc hTa BadR r (u e₀) fun i hiT hsep a c hac ha hax => by
        have hiNotB : i ∉ bridges u v := fun hiB => by
          have hcw := cycleVert_sideW_bridge u v hTc hTa he₀ huniv hiB hrC
          by_cases hrW : r ∈ sideW u v T i
          · exact (hsep.1 hrW) (hcw.1 hrW)
          · exact hrW (hsep.2 (fun hu => hrW (hcw.2 hu)))
        have hiC : i ∈ cycleEdges u v T e₀ := by
          by_contra hnot; exact hiNotB (by rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ i, hnot⟩)
        exact (hstep_pass i hiT).1 hiC a c hac ha hax
      exact himpl_tree r (u e₀) hrr
    have hbad_r_v0 : decide (r ∈ x) = !(b r) → decide (v e₀ ∈ x) = !(b (v e₀)) := by
      have hv0C : isCycleVert u v (cycleEdges u v T e₀) (v e₀) :=
        ⟨e₀, (mem_cycleEdges_iff u v).2 (Or.inl rfl), Or.inr rfl⟩
      have hrr := reach_dir_of_tree u v hTc hTa BadR r (v e₀) fun i hiT hsep a c hac ha hax => by
        have hiNotB : i ∉ bridges u v := fun hiB => by
          have h1 := cycleVert_sideW_bridge u v hTc hTa he₀ huniv hiB hrC
          have h2 := cycleVert_sideW_bridge u v hTc hTa he₀ huniv hiB hv0C
          by_cases hrW : r ∈ sideW u v T i
          · exact (hsep.1 hrW) (h2.2 (h1.1 hrW))
          · exact hrW (hsep.2 (fun hv => hrW (h1.2 (h2.1 hv))))
        have hiC : i ∈ cycleEdges u v T e₀ := by
          by_contra hnot; exact hiNotB (by rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ i, hnot⟩)
        exact (hstep_pass i hiT).1 hiC a c hac ha hax
      exact himpl_tree r (v e₀) hrr
    have hr_ok : decide (r ∈ x) = b r := by
      cases hdr : decide (r ∈ x) <;> cases hbr : b r <;> try rfl
      all_goals
        have hbad : decide (r ∈ x) = !(b r) := by simp [hdr, hbr]
        have hu0 := hbad_r_u0 hbad
        have hv0 := hbad_r_v0 hbad
        have hpe0 := hpx e₀
        dsimp only [p] at hpe0
        rw [if_pos rfl] at hpe0
        rw [hu0, hv0] at hpe0
        exact absurd rfl hpe0
    have hs_ok : ∀ s ∈ S, s ∈ x ↔ s ∈ x₀ := by
      intro s hs
      have hbr := hSb s hs
      have hrr := reach_dir_of_tree u v hTc hTa BadR s r fun i hiT hsep a c hac ha hax => by
        have hiB : i ∈ bridges u v := by
          have hex : ∃ j ∈ bridges u v, j ∈ cut u v (sideW u v T i) := by
            by_cases hsW : s ∈ sideW u v T i
            · exact reach_cut u v hbr (sideW u v T i) hsW (hsep.1 hsW)
            · have hrW : r ∈ sideW u v T i := by by_contra hrn; exact hsW (hsep.2 hrn)
              exact reach_cut u v (reach_symm u v hbr) (sideW u v T i) hrW hsW
          obtain ⟨j, hjB, hjCut⟩ := hex
          have hjT : j ∈ T := by
            rw [hdiff] at hjB
            have hj1 := (mem_sdiff.1 hjB).1
            rw [huniv] at hj1
            rcases mem_insert.1 hj1 with rfl | hj'
            · exact absurd ((mem_cycleEdges_iff u v).2 (Or.inl rfl)) (mem_sdiff.1 hjB).2
            · exact hj'
          have hj_eq : j ∈ T ∩ cut u v (sideW u v T i) := mem_inter.2 ⟨hjT, hjCut⟩
          rw [cut_sideW_inter_tree u v hTa hiT, mem_singleton] at hj_eq
          exact hj_eq ▸ hjB
        have hsep' : a ∈ sideW u v T i ↔ r ∉ sideW u v T i := ha.trans hsep
        exact (hstep_pass i hiT).2 hiB a c hac hsep' hax
      have himpl := himpl_tree s r hrr
      cases hdx : decide (s ∈ x) <;> cases hdx0 : decide (s ∈ x₀)
      · exact ⟨fun h => absurd (decide_eq_true h) (by simp [hdx]),
          fun h => absurd (decide_eq_true h) (by simp [hdx0])⟩
      · exfalso
        have hbad : decide (s ∈ x) = !(b s) := by simp [hdx, hdx0, b]
        have := himpl hbad
        rw [hr_ok] at this
        cases b r <;> simp at this
      · exfalso
        have hbad : decide (s ∈ x) = !(b s) := by simp [hdx, hdx0, b]
        have := himpl hbad
        rw [hr_ok] at this
        cases b r <;> simp at this
      · exact ⟨fun _ => decide_eq_true_iff.1 hdx0, fun _ => decide_eq_true_iff.1 hdx⟩
    refine ⟨x, hxB, ?_⟩
    rw [← hx₀z]
    ext s; simp only [mem_inter]
    exact ⟨fun ⟨hx', hs⟩ => ⟨(hs_ok s hs).1 hx', hs⟩, fun ⟨hx0', hs⟩ => ⟨(hs_ok s hs).2 hx0', hs⟩⟩

def StepDir (p' : Fin n → Bool × Bool) (w₁ w₂ : Fin n) : Prop :=
  ∃ i : Fin n, (u i = w₁ ∧ v i = w₂ ∧ p' i = (true, false)) ∨
    (v i = w₁ ∧ u i = w₂ ∧ p' i = (false, true))

theorem reachDir_cut (p' : Fin n → Bool × Bool) {s w : Fin n}
    (h : ReachRel (StepDir u v p') s w) (U : Finset (Fin n)) (hs : s ∈ U) (hw : w ∉ U) :
    ∃ j ∈ cut u v U, (u j ∈ U ∧ v j ∉ U ∧ p' j = (true, false)) ∨
      (v j ∈ U ∧ u j ∉ U ∧ p' j = (false, true)) := by
  induction h with
  | refl => exact absurd hs hw
  | @step y z _ hyz ih =>
    by_cases hy : y ∈ U
    · rcases hyz with ⟨j, ⟨rfl, rfl, hpj⟩ | ⟨rfl, rfl, hpj⟩⟩
      · exact ⟨j, (mem_cut u v).2 (Or.inl ⟨hy, hw⟩), Or.inl ⟨hy, hw, hpj⟩⟩
      · exact ⟨j, (mem_cut u v).2 (Or.inr ⟨hy, hw⟩), Or.inr ⟨hy, hw, hpj⟩⟩
    · exact ih hy

theorem reachDir_cut_out (p' : Fin n → Bool × Bool) {s w : Fin n}
    (h : ReachRel (StepDir u v p') s w) (U : Finset (Fin n)) (hs : s ∉ U) (hw : w ∈ U) :
    ∃ j ∈ cut u v U, (u j ∉ U ∧ v j ∈ U ∧ p' j = (true, false)) ∨
      (v j ∉ U ∧ u j ∈ U ∧ p' j = (false, true)) := by
  induction h with
  | refl => exact absurd hw hs
  | @step y z _ hyz ih =>
    by_cases hy : y ∈ U
    · exact ih hy
    · rcases hyz with ⟨j, ⟨rfl, rfl, hpj⟩ | ⟨rfl, rfl, hpj⟩⟩
      · exact ⟨j, (mem_cut u v).2 (Or.inr ⟨hw, hy⟩), Or.inl ⟨hy, hw, hpj⟩⟩
      · exact ⟨j, (mem_cut u v).2 (Or.inl ⟨hw, hy⟩), Or.inr ⟨hy, hw, hpj⟩⟩

theorem dir_lhs_to_rhs (hn : 0 < n)
    (hconn : ∀ U : Finset (Fin n), U.Nonempty → U ≠ Finset.univ → (cut u v U).Nonempty)
    (S : Finset (Fin n))
    (hlhs : ∀ A B : Finset (Finset (Fin n)),
      (∀ p, (∃ x ∈ A, pass u v p x) ↔ (∃ x ∈ B, pass u v p x)) →
      ∀ z ⊆ S, ((∃ x ∈ A, x ∩ S = z) ↔ ∃ x ∈ B, x ∩ S = z)) :
    ∀ a ∈ S, ∀ b ∈ S, ∀ U : Finset (Fin n), a ∈ U → b ∉ U → (bridges u v ∩ cut u v U).Nonempty := by
  by_contra hnrhs
  push Not at hnrhs
  obtain ⟨a, haS, b, hbS, U₀, haU₀, hbU₀, hEmptyU₀⟩ := hnrhs
  have hnotB : ¬ Reach u v (bridges u v) a b := by
    intro hr
    obtain ⟨i, hiB, hiCut⟩ := reach_cut u v hr U₀ haU₀ hbU₀
    have : i ∈ bridges u v ∩ cut u v U₀ := mem_inter.2 ⟨hiB, hiCut⟩
    rw [hEmptyU₀] at this
    exact notMem_empty i this
  let A : Finset (Finset (Fin n)) := Finset.univ
  let B : Finset (Finset (Fin n)) := Finset.univ.filter (fun x => (x ∩ S).Nonempty)
  have hnotSame : ¬ ∀ p, (∃ x ∈ A, pass u v p x) ↔ (∃ x ∈ B, pass u v p x) := by
    intro hsame
    have hiff := hlhs A B hsame ∅ (empty_subset S)
    have hL : ∃ x ∈ A, x ∩ S = ∅ := ⟨∅, mem_univ _, empty_inter S⟩
    obtain ⟨x, hxB, hxz⟩ := hiff.1 hL
    have hxne : (x ∩ S).Nonempty := (mem_filter.1 hxB).2
    rw [hxz] at hxne
    exact hxne.ne_empty rfl
  have hBsubA : ∀ p, (∃ x ∈ B, pass u v p x) → (∃ x ∈ A, pass u v p x) :=
    fun p ⟨x, _, hp⟩ => ⟨x, mem_univ x, hp⟩
  obtain ⟨p, hnot⟩ := Classical.not_forall.1 hnotSame
  obtain ⟨p, ⟨x₀, _, hpx₀⟩, hnoB⟩ : ∃ p, (∃ x ∈ A, pass u v p x) ∧ ¬ ∃ x ∈ B, pass u v p x := by
    by_cases h1 : ∃ x ∈ A, pass u v p x
    · exact ⟨p, h1, fun h2 => hnot (Iff.intro (fun _ => h2) (fun _ => h1))⟩
    · exact False.elim (hnot (Iff.intro (fun hA => absurd hA h1) (fun hB => absurd (hBsubA p hB) h1)))
  have hx₀S : x₀ ∩ S = ∅ := by
    by_contra hne
    exact hnoB ⟨x₀, mem_filter.2 ⟨mem_univ x₀, nonempty_iff_ne_empty.2 hne⟩, hpx₀⟩
  have ha0 : a ∉ x₀ := fun h => by
    have : a ∈ x₀ ∩ S := mem_inter.2 ⟨h, haS⟩
    rw [hx₀S] at this; exact notMem_empty a this
  have hb0 : b ∉ x₀ := fun h => by
    have : b ∈ x₀ ∩ S := mem_inter.2 ⟨h, hbS⟩
    rw [hx₀S] at this; exact notMem_empty b this
  let p' : Fin n → Bool × Bool := fun i =>
    (xor (p i).1 (decide (u i ∈ x₀)), xor (p i).2 (decide (v i ∈ x₀)))
  have hp'_nz : ∀ i, p' i ≠ (false, false) := fun i heq => by
    apply hpx₀ i
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    apply Prod.ext
    · cases hdu : decide (u i ∈ x₀) <;> cases hp1 : (p i).1 <;> simp_all [p']
    · cases hdv : decide (v i ∈ x₀) <;> cases hp2 : (p i).2 <;> simp_all [p']
  have hpass_shift : ∀ y : Finset (Fin n), pass u v p' y → pass u v p (symmDiff x₀ y) := by
    intro y hy i heq
    apply hy i
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    dsimp only at h1 h2
    have hm1 : decide (u i ∈ symmDiff x₀ y) = xor (decide (u i ∈ y)) (decide (u i ∈ x₀)) := by
      simp only [mem_symmDiff]
      by_cases hx1 : u i ∈ x₀ <;> by_cases hy1 : u i ∈ y <;> simp_all
    have hm2 : decide (v i ∈ symmDiff x₀ y) = xor (decide (v i ∈ y)) (decide (v i ∈ x₀)) := by
      simp only [mem_symmDiff]
      by_cases hx2 : v i ∈ x₀ <;> by_cases hy2 : v i ∈ y <;> simp_all
    rw [hm1] at h1; rw [hm2] at h2
    apply Prod.ext
    · by_cases hx1 : u i ∈ x₀ <;> by_cases hy1 : u i ∈ y <;> cases hp1 : (p i).1 <;> simp_all [p']
    · by_cases hx2 : v i ∈ x₀ <;> by_cases hy2 : v i ∈ y <;> cases hp2 : (p i).2 <;> simp_all [p']
  have hforb_ab : ∀ y : Finset (Fin n), pass u v p' y → a ∉ y ∧ b ∉ y := by
    intro y hy
    have hpy := hpass_shift y hy
    have hy0 : symmDiff x₀ y ∩ S = ∅ := by
      by_contra hne
      exact hnoB ⟨symmDiff x₀ y, mem_filter.2 ⟨mem_univ _, nonempty_iff_ne_empty.2 hne⟩, hpy⟩
    constructor
    · intro ha'
      have : a ∈ symmDiff x₀ y ∩ S := mem_inter.2 ⟨mem_symmDiff.2 (Or.inr ⟨ha', ha0⟩), haS⟩
      rw [hy0] at this; exact notMem_empty a this
    · intro hb'
      have : b ∈ symmDiff x₀ y ∩ S := mem_inter.2 ⟨mem_symmDiff.2 (Or.inr ⟨hb', hb0⟩), hbS⟩
      rw [hy0] at this; exact notMem_empty b this
  let R : Fin n → Finset (Fin n) := fun s => Finset.univ.filter (fun w => ReachRel (StepDir u v p') s w)
  have hmemR : ∀ s w, w ∈ R s ↔ ReachRel (StepDir u v p') s w := fun s w => by simp [R]
  have hs_in_R : ∀ s, s ∈ R s := fun s => (hmemR s s).2 (.refl s)
  have hit_pair : ∀ s ∈ ({a, b} : Finset (Fin n)),
      ∃ i : Fin n, p' i = (true, true) ∧ u i ∈ R s ∧ v i ∈ R s := by
    intro s hs
    have hfail : ¬ pass u v p' (R s) := fun hok => by
      have hab' := hforb_ab (R s) hok
      rcases mem_insert.1 hs with rfl | hb'
      · exact hab'.1 (hs_in_R s)
      · exact hab'.2 (mem_singleton.1 hb' ▸ hs_in_R s)
    unfold pass at hfail
    push Not at hfail
    obtain ⟨i, hi⟩ := hfail
    have hnz := hp'_nz i
    cases hp1 : (p' i).1 <;> cases hp2 : (p' i).2
    · exfalso; exact hnz (Prod.ext hp1 hp2)
    · exfalso
      have hpu : decide (u i ∈ R s) = false := by rw [← hp1]; exact congrArg Prod.fst hi
      have hpv : decide (v i ∈ R s) = true := by rw [← hp2]; exact congrArg Prod.snd hi
      have hvR : v i ∈ R s := decide_eq_true_iff.1 hpv
      have hstep : StepDir u v p' (v i) (u i) := ⟨i, Or.inr ⟨rfl, rfl, Prod.ext hp1 hp2⟩⟩
      have huR : u i ∈ R s := (hmemR s (u i)).2 (.step ((hmemR s (v i)).1 hvR) hstep)
      simp_all
    · exfalso
      have hpu : decide (u i ∈ R s) = true := by rw [← hp1]; exact congrArg Prod.fst hi
      have hpv : decide (v i ∈ R s) = false := by rw [← hp2]; exact congrArg Prod.snd hi
      have huR : u i ∈ R s := decide_eq_true_iff.1 hpu
      have hstep : StepDir u v p' (u i) (v i) := ⟨i, Or.inl ⟨rfl, rfl, Prod.ext hp1 hp2⟩⟩
      have hvR : v i ∈ R s := (hmemR s (v i)).2 (.step ((hmemR s (u i)).1 huR) hstep)
      simp_all
    · refine ⟨i, Prod.ext hp1 hp2, ?_, ?_⟩
      · have hpu : decide (u i ∈ R s) = true := by rw [← hp1]; exact congrArg Prod.fst hi
        exact decide_eq_true_iff.1 hpu
      · have hpv : decide (v i ∈ R s) = true := by rw [← hp2]; exact congrArg Prod.snd hi
        exact decide_eq_true_iff.1 hpv
  obtain ⟨ia, hpia, huia, hvia⟩ := hit_pair a (mem_insert_self a _)
  obtain ⟨ib, hpib, huib, hvib⟩ := hit_pair b (mem_insert_of_mem (mem_singleton_self b))
  obtain ⟨T, hTc, hTa, hTcard⟩ := exists_tree u v hn hconn
  obtain ⟨e₀, he₀, huniv⟩ := unique_extra_edge hTcard
  have hdiff := bridges_eq_sdiff_cycle u v hTc hTa he₀ huniv
  have hnot_bridge : ∀ s i, p' i = (true, true) → u i ∈ R s → v i ∈ R s → i ∉ bridges u v := by
    intro s i hpi hui hvi hiB
    rw [bridges, mem_filter] at hiB
    obtain ⟨U, hU⟩ := hiB.2
    have hiCut : i ∈ cut u v U := hU ▸ mem_singleton_self i
    rcases (mem_cut u v).1 hiCut with ⟨huU, hvU⟩ | ⟨hvU, huU⟩
    · by_cases hsU : s ∈ U
      · obtain ⟨j, hjCut, hdir⟩ := reachDir_cut u v p' ((hmemR s (v i)).1 hvi) U hsU hvU
        rw [hU, mem_singleton] at hjCut; subst hjCut
        rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpi] at hbad <;> exact absurd hbad (by decide)
      · obtain ⟨j, hjCut, hdir⟩ := reachDir_cut_out u v p' ((hmemR s (u i)).1 hui) U hsU huU
        rw [hU, mem_singleton] at hjCut; subst hjCut
        rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpi] at hbad <;> exact absurd hbad (by decide)
    · by_cases hsU : s ∈ U
      · obtain ⟨j, hjCut, hdir⟩ := reachDir_cut u v p' ((hmemR s (u i)).1 hui) U hsU huU
        rw [hU, mem_singleton] at hjCut; subst hjCut
        rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpi] at hbad <;> exact absurd hbad (by decide)
      · obtain ⟨j, hjCut, hdir⟩ := reachDir_cut_out u v p' ((hmemR s (v i)).1 hvi) U hsU hvU
        rw [hU, mem_singleton] at hjCut; subst hjCut
        rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpi] at hbad <;> exact absurd hbad (by decide)
  have hiaC : ia ∈ cycleEdges u v T e₀ := by
    by_contra hnot
    exact hnot_bridge a ia hpia huia hvia (by rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ ia, hnot⟩)
  have hibC : ib ∈ cycleEdges u v T e₀ := by
    by_contra hnot
    exact hnot_bridge b ib hpib huib hvib (by rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ ib, hnot⟩)
  have hia_eq_ib : ia = ib := by
    by_contra hne
    obtain ⟨U, hU⟩ := cut_two_cycleEdges u v hTa he₀ huniv hiaC hibC hne
    have hiaU : ia ∈ cut u v U := hU ▸ mem_insert_self ia {ib}
    have hno_cross : ∀ w, w ∈ R a → (a ∈ U ↔ w ∈ U) := by
      intro w hw
      have hsub : ∀ {x y}, ReachRel (StepDir u v p') x y → x ∈ U → y ∈ U := by
        intro x y hr hx
        by_contra hy
        obtain ⟨j, hjCut, hdir⟩ := reachDir_cut u v p' hr U hx hy
        rw [hU, mem_insert, mem_singleton] at hjCut
        rcases hjCut with rfl | rfl
        · rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpia] at hbad <;> exact absurd hbad (by decide)
        · rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpib] at hbad <;> exact absurd hbad (by decide)
      have hsub2 : ∀ {x y}, ReachRel (StepDir u v p') x y → x ∉ U → y ∉ U := by
        intro x y hr hx hy
        obtain ⟨j, hjCut, hdir⟩ := reachDir_cut_out u v p' hr U hx hy
        rw [hU, mem_insert, mem_singleton] at hjCut
        rcases hjCut with rfl | rfl
        · rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpia] at hbad <;> exact absurd hbad (by decide)
        · rcases hdir with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpib] at hbad <;> exact absurd hbad (by decide)
      exact ⟨fun haU => hsub ((hmemR a w).1 hw) haU, fun hwU => by
        by_contra hanU; exact hsub2 ((hmemR a w).1 hw) hanU hwU⟩
    have h1 := hno_cross (u ia) huia
    have h2 := hno_cross (v ia) hvia
    rcases (mem_cut u v).1 hiaU with ⟨hu1, hv1⟩ | ⟨hv1, hu1⟩
    · exact hv1 (h2.1 (h1.2 hu1))
    · exact hu1 (h1.1 (h2.2 hv1))
  subst hia_eq_ib
  set eStar := ia
  obtain ⟨hTsc, hTsa⟩ := cycleEdge_erase_tree u v hn hTc hTa he₀ huniv hiaC
  let Ts := Finset.univ.erase eStar
  obtain ⟨ca, hcaC, hcaB⟩ := reach_bridges_cycleVert u v hTc hTa he₀ huniv a
  obtain ⟨cb, hcbC, hcbB⟩ := reach_bridges_cycleVert u v hTc hTa he₀ huniv b
  have hcab : ca ≠ cb := fun heq => by
    subst heq
    exact hnotB (reach_trans u v (reach_symm u v hcaB) hcbB)
  obtain ⟨k, hk⟩ := reach_to_reachN u v (hTsc ca cb)
  obtain ⟨e₁, he₁Ts, _, _, _, _, hsep_cab, _⟩ := reachN_exists_edge_step u v hTsa k ca cb hk hcab
  let U₁ := sideW u v Ts e₁
  have he₁_notB : e₁ ∉ bridges u v := by
    intro he₁B
    have he₁B' := he₁B
    rw [bridges, mem_filter] at he₁B
    obtain ⟨W₀, hW₀⟩ := he₁B.2
    have hnot_er : eStar ∉ cut u v W₀ := by
      intro hmem; rw [hW₀, mem_singleton] at hmem
      exact (mem_erase.1 he₁Ts).1 hmem.symm
    have hW₀_cut_er : Ts.erase e₁ ∩ cut u v W₀ = ∅ := by
      ext j; simp only [mem_inter, mem_erase, notMem_empty, iff_false]
      rintro ⟨⟨hj1, _⟩, hjCut⟩
      rw [hW₀, mem_singleton] at hjCut
      exact hj1 hjCut
    have hU₁_eq : ∀ w, w ∈ U₁ ↔ (if u e₁ ∈ W₀ then w ∈ W₀ else w ∉ W₀) := by
      intro w
      by_cases hw : w ∈ U₁
      · have hr : Reach u v (Ts.erase e₁) (u e₁) w := (mem_sideW u v).1 hw
        have heq := reach_cut_iff u v hr hW₀_cut_er
        simp only [hw, true_iff]
        by_cases huW : u e₁ ∈ W₀
        · rw [if_pos huW]; exact heq.1 huW
        · rw [if_neg huW]; exact fun h => huW (heq.2 h)
      · have hr : Reach u v (Ts.erase e₁) (v e₁) w :=
          tree_erase_side_conn u v hTsc (e := e₁) hw
        have heq := reach_cut_iff u v hr hW₀_cut_er
        have he₁_cut : e₁ ∈ cut u v W₀ := hW₀ ▸ mem_singleton_self e₁
        simp only [hw, false_iff]
        rcases (mem_cut u v).1 he₁_cut with ⟨huW, hvW⟩ | ⟨hvW, huW⟩
        · rw [if_pos huW]; exact fun h => hvW (heq.2 h)
        · rw [if_neg huW]; exact fun h => h (heq.1 hvW)
    have he₁_cutU₁ : cut u v U₁ = {e₁} := by
      have hcut_eq : cut u v U₁ = cut u v W₀ := by
        ext j; simp only [mem_cut, hU₁_eq]
        by_cases huW : u e₁ ∈ W₀ <;> by_cases hju : u j ∈ W₀ <;> by_cases hjv : v j ∈ W₀ <;>
          simp [huW, hju, hjv]
      rw [hcut_eq, hW₀]
    have he₁NotC : e₁ ∉ cycleEdges u v T e₀ := by
      rw [hdiff] at he₁B'; exact (mem_sdiff.1 he₁B').2
    have hCcut : cycleEdges u v T e₀ ∩ cut u v U₁ = ∅ := by
      ext j; simp only [mem_inter, he₁_cutU₁, mem_singleton, notMem_empty, iff_false]
      rintro ⟨hjC, rfl⟩
      exact he₁NotC hjC
    have hc_eq := reach_cut_iff u v (cycle_connected u v hTc hTa he₀ huniv hcaC hcbC) hCcut
    by_cases hca : ca ∈ U₁
    · exact (hsep_cab.1 hca) (hc_eq.1 hca)
    · exact hca (hsep_cab.2 (fun hcb => hca (hc_eq.2 hcb)))
  have heStar_cut : eStar ∈ cut u v U₁ := by
    by_contra hnot
    have hU₁_only : cut u v U₁ = {e₁} := by
      ext j
      simp only [mem_singleton]
      constructor
      · intro hj
        have hjU : j = eStar ∨ j ∈ Ts := by
          by_cases hje : j = eStar
          · exact Or.inl hje
          · exact Or.inr (mem_erase.2 ⟨hje, mem_univ j⟩)
        rcases hjU with rfl | hjTs
        · exact absurd hj hnot
        · have hj_er : j ∈ Ts ∩ cut u v U₁ := mem_inter.2 ⟨hjTs, hj⟩
          rw [cut_sideW_inter_tree u v hTsa he₁Ts, mem_singleton] at hj_er
          exact hj_er
      · rintro rfl
        exact (mem_cut u v).2 (Or.inl ⟨u_mem_sideW u v, v_not_mem_sideW u v hTsa he₁Ts⟩)
    exact he₁_notB (mem_filter.2 ⟨mem_univ _, U₁, hU₁_only⟩)
  have hU₁_pair : cut u v U₁ = {e₁, eStar} := by
    ext j
    simp only [mem_insert, mem_singleton]
    constructor
    · intro hj
      by_cases hje : j = eStar
      · exact Or.inr hje
      · left
        have hjTs : j ∈ Ts := mem_erase.2 ⟨hje, mem_univ j⟩
        have := cut_sideW_inter_tree u v hTsa he₁Ts
        have hj' : j ∈ Ts ∩ cut u v U₁ := mem_inter.2 ⟨hjTs, hj⟩
        rw [this, mem_singleton] at hj'
        exact hj'
    · rintro (rfl | rfl)
      · exact (mem_cut u v).2 (Or.inl ⟨u_mem_sideW u v, v_not_mem_sideW u v hTsa he₁Ts⟩)
      · exact heStar_cut
  have he₁C : e₁ ∈ cycleEdges u v T e₀ := by
    by_contra hnot; exact he₁_notB (by rw [hdiff]; exact mem_sdiff.2 ⟨mem_univ e₁, hnot⟩)
  have hBU₁ : bridges u v ∩ cut u v U₁ = ∅ := by
    ext j; simp only [mem_inter, hU₁_pair, mem_insert, mem_singleton, notMem_empty, iff_false]
    rintro ⟨hjB, rfl | rfl⟩
    · exact he₁_notB hjB
    · exact hnot_bridge a eStar hpia huia hvia hjB
  have ha_eq_ca : a ∈ U₁ ↔ ca ∈ U₁ := reach_cut_iff u v (reach_symm u v hcaB) hBU₁
  have hb_eq_cb : b ∈ U₁ ↔ cb ∈ U₁ := reach_cut_iff u v (reach_symm u v hcbB) hBU₁
  have ha_sep_b : a ∈ U₁ ↔ b ∉ U₁ :=
    ⟨fun ha hb => (hsep_cab.1 (ha_eq_ca.1 ha)) (hb_eq_cb.1 hb),
     fun hb => ha_eq_ca.2 (hsep_cab.2 (fun hcb => hb (hb_eq_cb.2 hcb)))⟩
  have hboth_from_in : ∀ {x y : Fin n}, x ∈ U₁ → y ∉ U₁ →
      u eStar ∈ R x → v eStar ∈ R x → u eStar ∈ R y → v eStar ∈ R y → False := by
    intro x y hx hy hux hvx huy hvy
    rcases (mem_cut u v).1 heStar_cut with ⟨hus, hvs⟩ | ⟨hvs, hus⟩
    · obtain ⟨j1, hj1, hdir1⟩ := reachDir_cut u v p' ((hmemR x (v eStar)).1 hvx) U₁ hx hvs
      rw [hU₁_pair, mem_insert, mem_singleton] at hj1
      have hj1_eq : j1 = e₁ := by
        rcases hj1 with rfl | rfl
        · rfl
        · exfalso
          rcases hdir1 with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpia] at hbad <;> exact absurd hbad (by decide)
      subst j1
      obtain ⟨j2, hj2, hdir2⟩ := reachDir_cut_out u v p' ((hmemR y (u eStar)).1 huy) U₁ hy hus
      rw [hU₁_pair, mem_insert, mem_singleton] at hj2
      have hj2_eq : j2 = e₁ := by
        rcases hj2 with rfl | rfl
        · rfl
        · exfalso
          rcases hdir2 with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpia] at hbad <;> exact absurd hbad (by decide)
      subst j2
      rcases hdir1 with ⟨h1u, _, h1p⟩ | ⟨h1v, h1u, h1p⟩ <;>
        rcases hdir2 with ⟨h2u, _, h2p⟩ | ⟨h2v, _, h2p⟩
      · exact absurd h1u h2u
      · rw [h1p] at h2p; exact absurd h2p (by decide)
      · rw [h1p] at h2p; exact absurd h2p (by decide)
      · exact absurd h1v h2v
    · obtain ⟨j1, hj1, hdir1⟩ := reachDir_cut u v p' ((hmemR x (u eStar)).1 hux) U₁ hx hus
      rw [hU₁_pair, mem_insert, mem_singleton] at hj1
      have hj1_eq : j1 = e₁ := by
        rcases hj1 with rfl | rfl
        · rfl
        · exfalso
          rcases hdir1 with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpia] at hbad <;> exact absurd hbad (by decide)
      subst j1
      obtain ⟨j2, hj2, hdir2⟩ := reachDir_cut_out u v p' ((hmemR y (v eStar)).1 hvy) U₁ hy hvs
      rw [hU₁_pair, mem_insert, mem_singleton] at hj2
      have hj2_eq : j2 = e₁ := by
        rcases hj2 with rfl | rfl
        · rfl
        · exfalso
          rcases hdir2 with ⟨_, _, hbad⟩ | ⟨_, _, hbad⟩ <;> rw [hpia] at hbad <;> exact absurd hbad (by decide)
      subst j2
      rcases hdir1 with ⟨h1u, _, h1p⟩ | ⟨h1v, h1u, h1p⟩ <;>
        rcases hdir2 with ⟨h2u, _, h2p⟩ | ⟨h2v, _, h2p⟩
      · exact absurd h1u h2u
      · rw [h1p] at h2p; exact absurd h2p (by decide)
      · rw [h1p] at h2p; exact absurd h2p (by decide)
      · exact absurd h1v h2v
  by_cases haU₁ : a ∈ U₁
  · exact hboth_from_in haU₁ (ha_sep_b.1 haU₁) huia hvia huib hvib
  · exact hboth_from_in (by by_contra hnb; exact haU₁ (ha_sep_b.2 hnb)) haU₁ huib hvib huia hvia

end Graph

end PEqualNP.Outside.L_lib_1150_aux

theorem PEqualNP.Outside.L_lib_1150 :
  ∀ (n m : Nat) (u v : Fin m → Fin n), (∀ i, u i ≠ v i) →
    let Bits := Finset (Fin n)
    let cube := (Finset.univ : Finset Bits)
    let labels := (Finset.univ : Finset (Fin m))
    let cut := fun (S : Bits) => labels.filter
      (fun i => decide (u i ∈ S) != decide (v i ∈ S))
    0 < n → m = n →
    (∀ U ∈ cube, U.Nonempty → U ≠ Finset.univ → (cut U).Nonempty) →
    let bridges := labels.filter (fun i => ∃ U ∈ cube, cut U = {i})
    let Signing := Fin m → Bool × Bool
    let sat := fun (A : Finset Bits) (p : Signing) =>
      ∃ x ∈ A, ∀ i, (decide (u i ∈ x), decide (v i ∈ x)) ≠ p i
    ∀ S : Bits,
      (∀ A B : Finset Bits, (∀ p, (sat A p ↔ sat B p)) →
        ∀ z ⊆ S, ((∃ x ∈ A, x ∩ S = z) ↔ ∃ x ∈ B, x ∩ S = z)) ↔
      ∀ a ∈ S, ∀ b ∈ S, ∀ U ∈ cube, a ∈ U → b ∉ U → (bridges ∩ cut U).Nonempty := by
  intro n m u v huv Bits cube labels cut hn hm hconn bridges Signing sat S
  subst m
  have hconn' : ∀ U : Finset (Fin n), U.Nonempty → U ≠ Finset.univ →
      (PEqualNP.Outside.L_lib_1150_aux.cut u v U).Nonempty :=
    fun U h1 h2 => hconn U (Finset.mem_univ U) h1 h2
  constructor
  · intro hlhs a ha b hb U _ haU hbU
    exact PEqualNP.Outside.L_lib_1150_aux.dir_lhs_to_rhs u v hn hconn' S hlhs a ha b hb U haU hbU
  · intro hrhs A B hsat z hz
    have hrhs' : ∀ a ∈ S, ∀ b ∈ S, ∀ U : Finset (Fin n), a ∈ U → b ∉ U →
        (PEqualNP.Outside.L_lib_1150_aux.bridges u v ∩
          PEqualNP.Outside.L_lib_1150_aux.cut u v U).Nonempty :=
      fun a ha b hb U haU hbU => hrhs a ha b hb U (Finset.mem_univ U) haU hbU
    exact PEqualNP.Outside.L_lib_1150_aux.dir_rhs_to_lhs u v hn hconn' S hrhs' A B hsat z hz
