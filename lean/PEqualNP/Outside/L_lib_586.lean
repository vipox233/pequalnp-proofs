import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_586_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def Adj (E : List (ℕ × ℕ)) (x y : ℕ) : Prop :=
  (x, y) ∈ E ∨ (y, x) ∈ E

private def Reach (E : List (ℕ × ℕ)) (x y : ℕ) : Prop :=
  Relation.ReflTransGen (Adj E) x y

private theorem reach_refl (E : List (ℕ × ℕ)) (x : ℕ) : Reach E x x :=
  Relation.ReflTransGen.refl

private theorem reach_trans {E : List (ℕ × ℕ)} {x y z : ℕ}
    (h1 : Reach E x y) (h2 : Reach E y z) : Reach E x z :=
  Relation.ReflTransGen.trans h1 h2

private theorem reach_symm {E : List (ℕ × ℕ)} {x y : ℕ} (h : Reach E x y) : Reach E y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    exact Relation.ReflTransGen.head (by
      rcases hab with h1 | h2
      · exact Or.inr h1
      · exact Or.inl h2) ih

private theorem reach_mono {E1 E2 : List (ℕ × ℕ)} (hsub : ∀ e, e ∈ E1 → e ∈ E2)
    {x y : ℕ} (h : Reach E1 x y) : Reach E2 x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    apply Relation.ReflTransGen.tail ih
    rcases hab with h1 | h2
    · exact Or.inl (hsub _ h1)
    · exact Or.inr (hsub _ h2)

private theorem reach_iff_of_mem_iff {E1 E2 : List (ℕ × ℕ)} (hiff : ∀ e, e ∈ E1 ↔ e ∈ E2)
    (x y : ℕ) : Reach E1 x y ↔ Reach E2 x y :=
  ⟨reach_mono (fun e he => (hiff e).mp he), reach_mono (fun e he => (hiff e).mpr he)⟩

private noncomputable def comp (V : Finset ℕ) (E : List (ℕ × ℕ)) (x : ℕ) : Finset ℕ := by
  classical
  exact V.filter (fun y => Reach E x y)

private noncomputable def cc (V : Finset ℕ) (E : List (ℕ × ℕ)) : ℕ := by
  classical
  exact (V.image (comp V E)).card

private theorem mem_comp_iff {V : Finset ℕ} {E : List (ℕ × ℕ)} {x y : ℕ} :
    y ∈ comp V E x ↔ y ∈ V ∧ Reach E x y := by
  classical
  simp [comp]

private theorem comp_eq_iff {V : Finset ℕ} {E : List (ℕ × ℕ)} {x y : ℕ}
    (_hx : x ∈ V) (hy : y ∈ V) : comp V E x = comp V E y ↔ Reach E x y := by
  constructor
  · intro heq
    have : y ∈ comp V E x := by rw [heq]; exact mem_comp_iff.mpr ⟨hy, reach_refl E y⟩
    exact (mem_comp_iff.mp this).2
  · intro hxy
    ext z
    simp only [mem_comp_iff]
    exact ⟨fun ⟨hz, hxz⟩ => ⟨hz, reach_trans (reach_symm hxy) hxz⟩,
      fun ⟨hz, hyz⟩ => ⟨hz, reach_trans hxy hyz⟩⟩

private theorem cc_eq_of_mem_iff {V : Finset ℕ} {E1 E2 : List (ℕ × ℕ)}
    (hiff : ∀ e, e ∈ E1 ↔ e ∈ E2) : cc V E1 = cc V E2 := by
  classical
  have hc : comp V E1 = comp V E2 := by
    funext x
    ext y
    simp only [mem_comp_iff, reach_iff_of_mem_iff hiff]
  simp only [cc, hc]

private theorem cc_nil (V : Finset ℕ) : cc V [] = V.card := by
  classical
  have hc : ∀ x ∈ V, comp V [] x = {x} := by
    intro x hx
    ext y
    simp only [mem_comp_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      cases h with
      | refl => rfl
      | tail _ hab => simp [Adj] at hab
    · rintro rfl
      exact ⟨hx, reach_refl [] y⟩
  have heq : V.image (comp V []) = V.image (fun x => ({x} : Finset ℕ)) := by
    ext C
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hc x hx).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, hc x hx⟩
  simp only [cc, heq]
  rw [Finset.card_image_of_injective]
  intro a b h
  exact Finset.singleton_injective h

private theorem reach_cons_iff {E : List (ℕ × ℕ)} {u v x y : ℕ} :
    Reach ((u, v) :: E) x y ↔
      Reach E x y ∨ (Reach E x u ∧ Reach E v y) ∨ (Reach E x v ∧ Reach E u y) := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl (reach_refl E x)
    | @tail b c _ hbc ih =>
      have hstep : Adj E b c ∨ (b = u ∧ c = v) ∨ (b = v ∧ c = u) := by
        rcases hbc with h1 | h2
        · simp only [List.mem_cons, Prod.mk.injEq] at h1
          rcases h1 with ⟨rfl, rfl⟩ | h1'
          · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          · exact Or.inl (Or.inl h1')
        · simp only [List.mem_cons, Prod.mk.injEq] at h2
          rcases h2 with ⟨rfl, rfl⟩ | h2'
          · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          · exact Or.inl (Or.inr h2')
      rcases hstep with hadj | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl (Relation.ReflTransGen.tail h1 hadj)
        · exact Or.inr (Or.inl ⟨h1, Relation.ReflTransGen.tail h2 hadj⟩)
        · exact Or.inr (Or.inr ⟨h1, Relation.ReflTransGen.tail h2 hadj⟩)
      · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inl ⟨h1, reach_refl E c⟩)
        · exact Or.inr (Or.inl ⟨h1, reach_refl E c⟩)
        · exact Or.inl h1
      · rcases ih with h1 | ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inr (Or.inr ⟨h1, reach_refl E c⟩)
        · exact Or.inl h1
        · exact Or.inr (Or.inr ⟨h1, reach_refl E c⟩)
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact reach_mono (fun e he => List.mem_cons_of_mem _ he) h
    · exact reach_trans (reach_mono (fun e he => List.mem_cons_of_mem _ he) h1)
        (Relation.ReflTransGen.head (Or.inl (List.mem_cons_self ..))
          (reach_mono (fun e he => List.mem_cons_of_mem _ he) h2))
    · exact reach_trans (reach_mono (fun e he => List.mem_cons_of_mem _ he) h1)
        (Relation.ReflTransGen.head (Or.inr (List.mem_cons_self ..))
          (reach_mono (fun e he => List.mem_cons_of_mem _ he) h2))

private theorem cc_cons_bounds {V : Finset ℕ} {E : List (ℕ × ℕ)} {u v : ℕ}
    (hu : u ∈ V) (hv : v ∈ V) :
    cc V ((u, v) :: E) ≤ cc V E ∧ cc V E ≤ cc V ((u, v) :: E) + 1 := by
  classical
  by_cases huv : Reach E u v
  · have hiff : ∀ x y, Reach ((u, v) :: E) x y ↔ Reach E x y := by
      intro x y
      rw [reach_cons_iff]
      constructor
      · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact h
        · exact reach_trans (reach_trans h1 huv) h2
        · exact reach_trans (reach_trans h1 (reach_symm huv)) h2
      · exact Or.inl
    have heq : cc V ((u, v) :: E) = cc V E := by
      have hc : comp V ((u, v) :: E) = comp V E := by
        funext x; ext y; simp only [mem_comp_iff, hiff]
      simp only [cc, hc]
    omega
  · let S := V.image (comp V E)
    let S' := V.image (comp V ((u, v) :: E))
    let Cu := comp V E u
    let Cv := comp V E v
    have hCuS : Cu ∈ S := Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hCvS : Cv ∈ S := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hne : Cu ≠ Cv := fun h => huv ((comp_eq_iff hu hv).mp h)
    have hcomp_merge : ∀ x ∈ V,
        (Reach E x u ∨ Reach E x v → comp V ((u, v) :: E) x = Cu ∪ Cv) ∧
        (¬ Reach E x u ∧ ¬ Reach E x v → comp V ((u, v) :: E) x = comp V E x) := by
      intro x hx
      constructor
      · intro hxu
        ext y
        simp only [mem_comp_iff, Finset.mem_union, Cu, Cv, reach_cons_iff]
        constructor
        · rintro ⟨hy, h | ⟨_, h2⟩ | ⟨_, h2⟩⟩
          · rcases hxu with h1 | h1
            · exact Or.inl ⟨hy, reach_trans (reach_symm h1) h⟩
            · exact Or.inr ⟨hy, reach_trans (reach_symm h1) h⟩
          · exact Or.inr ⟨hy, h2⟩
          · exact Or.inl ⟨hy, h2⟩
        · rintro (⟨hy, huy⟩ | ⟨hy, hvy⟩)
          · rcases hxu with h1 | h1
            · exact ⟨hy, Or.inl (reach_trans h1 huy)⟩
            · exact ⟨hy, Or.inr (Or.inr ⟨h1, huy⟩)⟩
          · rcases hxu with h1 | h1
            · exact ⟨hy, Or.inr (Or.inl ⟨h1, hvy⟩)⟩
            · exact ⟨hy, Or.inl (reach_trans h1 hvy)⟩
      · rintro ⟨hnu, hnv⟩
        ext y
        simp only [mem_comp_iff, reach_cons_iff]
        constructor
        · rintro ⟨hy, h | ⟨h1, _⟩ | ⟨h1, _⟩⟩
          · exact ⟨hy, h⟩
          · exact absurd h1 hnu
          · exact absurd h1 hnv
        · rintro ⟨hy, h⟩
          exact ⟨hy, Or.inl h⟩
    have hS'_eq : S' = insert (Cu ∪ Cv) ((S.erase Cu).erase Cv) := by
      ext C
      simp only [S', S, Finset.mem_insert, Finset.mem_erase, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxu : Reach E x u ∨ Reach E x v
        · exact Or.inl ((hcomp_merge x hx).1 hxu)
        · push Not at hxu
          refine Or.inr ⟨?_, ?_, x, hx, ((hcomp_merge x hx).2 hxu).symm⟩
          · rw [(hcomp_merge x hx).2 hxu]
            exact fun h => hxu.2 ((comp_eq_iff hx hv).mp h)
          · rw [(hcomp_merge x hx).2 hxu]
            exact fun h => hxu.1 ((comp_eq_iff hx hu).mp h)
      · rintro (rfl | ⟨hCv', hCu', x, hx, rfl⟩)
        · exact ⟨u, hu, (hcomp_merge u hu).1 (Or.inl (reach_refl E u))⟩
        · have hnu : ¬ Reach E x u := fun h => hCu' ((comp_eq_iff hx hu).mpr h)
          have hnv : ¬ Reach E x v := fun h => hCv' ((comp_eq_iff hx hv).mpr h)
          exact ⟨x, hx, (hcomp_merge x hx).2 ⟨hnu, hnv⟩⟩
    have hnotmem : Cu ∪ Cv ∉ (S.erase Cu).erase Cv := by
      intro hmem
      rcases Finset.mem_erase.mp hmem with ⟨h1, hmem2⟩
      rcases Finset.mem_erase.mp hmem2 with ⟨h2, hmem3⟩
      rcases Finset.mem_image.mp hmem3 with ⟨x, hx, heq⟩
      have huin : u ∈ comp V E x := by
        rw [heq]; exact Finset.mem_union_left _ (mem_comp_iff.mpr ⟨hu, reach_refl E u⟩)
      have hxu : Reach E x u := (mem_comp_iff.mp huin).2
      have hCx : comp V E x = Cu := (comp_eq_iff hx hu).mpr hxu
      rw [hCx] at heq
      exact h2 heq.symm
    have hcard : S'.card + 1 = S.card := by
      rw [hS'_eq, Finset.card_insert_of_notMem hnotmem]
      have hCv_in : Cv ∈ S.erase Cu := Finset.mem_erase.mpr ⟨hne.symm, hCvS⟩
      rw [Finset.card_erase_of_mem hCv_in, Finset.card_erase_of_mem hCuS]
      have hge2 : 2 ≤ S.card := by
        have hsub : ({Cu, Cv} : Finset (Finset ℕ)) ⊆ S := by
          intro c hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc
          rcases hc with rfl | rfl
          · exact hCuS
          · exact hCvS
        have h2 : ({Cu, Cv} : Finset (Finset ℕ)).card = 2 := Finset.card_pair hne
        have := Finset.card_le_card hsub
        omega
      omega
    change S'.card ≤ S.card ∧ S.card ≤ S'.card + 1
    omega

private theorem card_le_edges_add_cc {V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    V.card ≤ E.length + cc V E := by
  induction E with
  | nil => rw [List.length_nil, zero_add, cc_nil]
  | cons e E ih =>
    rcases e with ⟨u, v⟩
    have he : u ∈ V ∧ v ∈ V := hE (u, v) (List.mem_cons_self ..)
    have hrest : ∀ e' ∈ E, e'.1 ∈ V ∧ e'.2 ∈ V := fun e' he' => hE e' (List.mem_cons_of_mem _ he')
    have hih := ih hrest
    have hb := (cc_cons_bounds (E := E) he.1 he.2).2
    simp only [List.length_cons]
    omega

private noncomputable def beta1 (V : Finset ℕ) (E : List (ℕ × ℕ)) : ℕ :=
  E.length + cc V E - V.card

private theorem beta1_add_card {V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hE : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    V.card + beta1 V E = E.length + cc V E := by
  have h := card_le_edges_add_cc hE
  dsimp only [beta1]
  omega

private theorem cc_connected {V : Finset ℕ} {E : List (ℕ × ℕ)} {out : ℕ}
    (hout : out ∈ V) (hconn : ∀ x ∈ V, Reach E out x) : cc V E = 1 := by
  classical
  have heq : V.image (comp V E) = {comp V E out} := by
    ext C
    simp only [Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (comp_eq_iff hx hout).mpr (reach_symm (hconn x hx))
    · rintro rfl
      exact ⟨out, hout, rfl⟩
  simp only [cc, heq, Finset.card_singleton]

private theorem beta1_delete_edge {V : Finset ℕ} {E1 E2 : List (ℕ × ℕ)} {e : ℕ × ℕ}
    (he1 : e.1 ∈ V) (he2 : e.2 ∈ V) :
    beta1 V (E1 ++ E2) ≤ beta1 V (E1 ++ e :: E2) := by
  rcases e with ⟨u, v⟩
  dsimp only at he1 he2
  have hiff : ∀ x, x ∈ (u, v) :: (E1 ++ E2) ↔ x ∈ E1 ++ (u, v) :: E2 := by
    intro x
    simp only [List.mem_cons, List.mem_append]
    tauto
  have hcc : cc V (E1 ++ (u, v) :: E2) = cc V ((u, v) :: (E1 ++ E2)) :=
    (cc_eq_of_mem_iff hiff).symm
  have hb := (cc_cons_bounds (E := E1 ++ E2) he1 he2).2
  dsimp only [beta1]
  rw [hcc]
  simp only [List.length_append, List.length_cons]
  omega

private theorem beta1_sublist {V : Finset ℕ} {E' E : List (ℕ × ℕ)}
    (hsub : E'.Sublist E) (hE : ∀ e ∈ E, e.1 ∈ V ∧ e.2 ∈ V) :
    beta1 V E' ≤ beta1 V E := by
  have hgen : ∀ (P Q R : List (ℕ × ℕ)), P.Sublist Q →
      (∀ e ∈ R ++ Q, e.1 ∈ V ∧ e.2 ∈ V) → beta1 V (R ++ P) ≤ beta1 V (R ++ Q) := by
    intro P Q R hpq
    induction hpq generalizing R with
    | slnil => intro _; exact le_rfl
    | @cons p q x _ ih =>
      intro hRQ
      have hx : x.1 ∈ V ∧ x.2 ∈ V := hRQ x (List.mem_append_right _ (List.mem_cons_self ..))
      have h1 : beta1 V (R ++ p) ≤ beta1 V (R ++ q) :=
        ih R (fun e he => hRQ e (by
          rcases List.mem_append.mp he with h1 | h2
          · exact List.mem_append_left _ h1
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)))
      have h2 : beta1 V (R ++ q) ≤ beta1 V (R ++ x :: q) :=
        beta1_delete_edge hx.1 hx.2
      exact h1.trans h2
    | @cons_cons p q x _ ih =>
      intro hRQ
      have heq1 : R ++ x :: p = (R ++ [x]) ++ p := by simp
      have heq2 : R ++ x :: q = (R ++ [x]) ++ q := by simp
      rw [heq1, heq2]
      exact ih (R ++ [x]) (fun e he => by
        rw [← heq2] at he; exact hRQ e he)
  simpa using hgen E' E [] hsub (by simpa using hE)

private theorem cc_erase_isolated {V : Finset ℕ} {E : List (ℕ × ℕ)} {v : ℕ}
    (hv : v ∈ V) (hiso : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) :
    cc V E = cc (V.erase v) E + 1 := by
  classical
  have hreach_v : ∀ y, Reach E v y ↔ y = v := by
    intro y
    constructor
    · intro h
      induction h with
      | refl => rfl
      | tail _ hab ih =>
        subst ih
        rcases hab with h1 | h2
        · exact absurd rfl (hiso _ h1).1
        · exact absurd rfl (hiso _ h2).2
    · rintro rfl; exact reach_refl E _
  have hcv : comp V E v = {v} := by
    ext y
    simp only [mem_comp_iff, Finset.mem_singleton, hreach_v]
    constructor
    · rintro ⟨_, rfl⟩; rfl
    · intro hy; subst hy; exact ⟨hv, rfl⟩
  have hcx : ∀ x ∈ V.erase v, comp V E x = comp (V.erase v) E x := by
    intro x hx
    have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
    ext y
    simp only [mem_comp_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hy, hxy⟩
      refine ⟨⟨fun hyv => hxv ?_, hy⟩, hxy⟩
      subst hyv
      exact (hreach_v x).mp (reach_symm hxy)
    · rintro ⟨⟨_, hy⟩, hxy⟩
      exact ⟨hy, hxy⟩
  have heq : V.image (comp V E) = insert ({v} : Finset ℕ) ((V.erase v).image (comp (V.erase v) E)) := by
    ext C
    simp only [Finset.mem_image, Finset.mem_insert]
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv; exact Or.inl hcv
      · exact Or.inr ⟨x, Finset.mem_erase.mpr ⟨hxv, hx⟩, (hcx x (Finset.mem_erase.mpr ⟨hxv, hx⟩)).symm⟩
    · rintro (rfl | ⟨x, hx, rfl⟩)
      · exact ⟨v, hv, hcv⟩
      · exact ⟨x, Finset.mem_of_mem_erase hx, hcx x hx⟩
  have hnm : ({v} : Finset ℕ) ∉ (V.erase v).image (comp (V.erase v) E) := by
    intro hm
    rcases Finset.mem_image.mp hm with ⟨x, _, he⟩
    have hv_in : v ∈ comp (V.erase v) E x := by rw [he]; simp
    exact (Finset.mem_erase.mp (mem_comp_iff.mp hv_in).1).1 rfl
  simp only [cc, heq, Finset.card_insert_of_notMem hnm]

private theorem beta1_erase_isolated {V : Finset ℕ} {E : List (ℕ × ℕ)} {v : ℕ}
    (hv : v ∈ V) (hiso : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v) :
    beta1 (V.erase v) E = beta1 V E := by
  dsimp only [beta1]
  rw [cc_erase_isolated hv hiso, Finset.card_erase_of_mem hv]
  have hpos : 1 ≤ V.card := Finset.card_pos.mpr ⟨v, hv⟩
  omega

private theorem beta1_restrict_isolated {R V : Finset ℕ} {E : List (ℕ × ℕ)}
    (hRV : R ⊆ V) (hER : ∀ e ∈ E, e.1 ∈ R ∧ e.2 ∈ R) :
    beta1 R E = beta1 V E := by
  have hgen : ∀ (D : Finset ℕ), Disjoint R D → beta1 R E = beta1 (R ∪ D) E := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro _; simp
    | @insert v D hvD ih =>
      intro hdisj
      have hvR : v ∉ R := fun h => (Finset.disjoint_left.mp hdisj) h (Finset.mem_insert_self _ _)
      have hdisj' : Disjoint R D := Disjoint.mono_right (Finset.subset_insert _ _) hdisj
      have hiso : ∀ e ∈ E, e.1 ≠ v ∧ e.2 ≠ v := fun e he =>
        ⟨fun h => hvR (h ▸ (hER e he).1), fun h => hvR (h ▸ (hER e he).2)⟩
      have hvin : v ∈ R ∪ insert v D := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
      have her : (R ∪ insert v D).erase v = R ∪ D := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro ⟨hne, hR | rfl | hD⟩
          · exact Or.inl hR
          · exact absurd rfl hne
          · exact Or.inr hD
        · rintro (hR | hD)
          · exact ⟨fun h => hvR (h ▸ hR), Or.inl hR⟩
          · exact ⟨fun h => hvD (h ▸ hD), Or.inr (Or.inr hD)⟩
      rw [ih hdisj', ← her, beta1_erase_isolated hvin hiso]
  have hunion : R ∪ (V \ R) = V := Finset.union_sdiff_of_subset hRV
  rw [← hunion]
  exact hgen (V \ R) Finset.disjoint_sdiff

private theorem beta1_contract {V : Finset ℕ} {E1 E2 : List (ℕ × ℕ)} {a v : ℕ}
    (ha : a ∈ V) (hv : v ∈ V) (hav : a ≠ v) :
    let sub : ℕ → ℕ := fun x => if x = v then a else x
    beta1 (V.erase v) ((E1 ++ E2).map (fun e => (sub e.1, sub e.2))) =
      beta1 V (E1 ++ (a, v) :: E2) := by
  classical
  intro sub
  let E := E1 ++ (a, v) :: E2
  let E' := (E1 ++ E2).map (fun e => (sub e.1, sub e.2))
  let V' := V.erase v
  have hsub_mem : ∀ x ∈ V, sub x ∈ V' := by
    intro x hx
    dsimp only [sub, V']
    split_ifs with h
    · exact Finset.mem_erase.mpr ⟨hav, ha⟩
    · exact Finset.mem_erase.mpr ⟨h, hx⟩
  have hsub_self : ∀ x, x ≠ v → sub x = x := fun x hx => by simp [sub, hx]
  have hreach_sub : ∀ x, Reach E x (sub x) := by
    intro x
    dsimp only [sub]
    split_ifs with h
    · subst h
      exact Relation.ReflTransGen.single (Or.inr (List.mem_append_right _ (List.mem_cons_self ..)))
    · exact reach_refl E x
  have hreach_iff : ∀ x y, Reach E' (sub x) (sub y) ↔ Reach E x y := by
    intro x y
    constructor
    · intro h
      have h' : ∀ p q, Reach E' p q → Reach E p q := by
        intro p q hpq
        induction hpq with
        | refl => exact reach_refl E p
        | tail _ hab ih =>
          refine reach_trans ih ?_
          rcases hab with h1 | h2
          · rcases List.mem_map.mp h1 with ⟨⟨r, s⟩, hrs, heq⟩
            rcases Prod.mk.inj heq with ⟨hr, hs⟩
            rw [← hr, ← hs]
            have hrsE : (r, s) ∈ E := by
              rcases List.mem_append.mp hrs with h1' | h2'
              · exact List.mem_append_left _ h1'
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2')
            exact reach_trans (reach_symm (hreach_sub r))
              (reach_trans (Relation.ReflTransGen.single (Or.inl hrsE)) (hreach_sub s))
          · rcases List.mem_map.mp h2 with ⟨⟨r, s⟩, hrs, heq⟩
            rcases Prod.mk.inj heq with ⟨hr, hs⟩
            rw [← hr, ← hs]
            have hrsE : (r, s) ∈ E := by
              rcases List.mem_append.mp hrs with h1' | h2'
              · exact List.mem_append_left _ h1'
              · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2')
            exact reach_trans (reach_symm (hreach_sub s))
              (reach_trans (Relation.ReflTransGen.single (Or.inr hrsE)) (hreach_sub r))
      exact reach_trans (hreach_sub x) (reach_trans (h' _ _ h) (reach_symm (hreach_sub y)))
    · intro h
      induction h with
      | refl => exact reach_refl E' (sub x)
      | @tail p q _ hpq ih =>
        refine reach_trans ih ?_
        have hstep : ∀ r s, (r, s) ∈ E → Reach E' (sub r) (sub s) := by
          intro r s hrs
          rcases List.mem_append.mp hrs with h1 | h2
          · exact Relation.ReflTransGen.single (Or.inl (List.mem_map.mpr ⟨(r, s),
              List.mem_append_left _ h1, rfl⟩))
          · rcases List.mem_cons.mp h2 with heq | h2'
            · rcases Prod.mk.inj heq with ⟨hra, hsv⟩
              rw [hra, hsv]
              have h1' : sub a = a := hsub_self a hav
              have h2' : sub v = a := by simp [sub]
              rw [h1', h2']; exact reach_refl E' a
            · exact Relation.ReflTransGen.single (Or.inl (List.mem_map.mpr ⟨(r, s),
                List.mem_append_right _ h2', rfl⟩))
        rcases hpq with h1 | h2
        · exact hstep p q h1
        · exact reach_symm (hstep q p h2)
  have hcomp_erase : ∀ x ∈ V, (comp V E x).erase v = comp V' E' (sub x) := by
    intro x _
    ext y
    simp only [Finset.mem_erase, mem_comp_iff, V']
    constructor
    · rintro ⟨hyv, hyV, hxy⟩
      refine ⟨⟨hyv, hyV⟩, ?_⟩
      rw [← hsub_self y hyv]
      exact (hreach_iff x y).mpr hxy
    · rintro ⟨⟨hyv, hyV⟩, hxy⟩
      refine ⟨hyv, hyV, (hreach_iff x y).mp ?_⟩
      rwa [hsub_self y hyv]
  let S := V.image (comp V E)
  let S' := V'.image (comp V' E')
  have hS'_eq : S' = S.image (fun C => C.erase v) := by
    ext D
    simp only [S', S, Finset.mem_image]
    constructor
    · rintro ⟨y, hyV', rfl⟩
      have hyV : y ∈ V := Finset.mem_of_mem_erase hyV'
      have hyv : y ≠ v := (Finset.mem_erase.mp hyV').1
      refine ⟨comp V E y, ⟨y, hyV, rfl⟩, ?_⟩
      rw [hcomp_erase y hyV, hsub_self y hyv]
    · rintro ⟨C, ⟨x, hxV, rfl⟩, rfl⟩
      exact ⟨sub x, hsub_mem x hxV, (hcomp_erase x hxV).symm⟩
  have hinj : Set.InjOn (fun C : Finset ℕ => C.erase v) (S : Set (Finset ℕ)) := by
    intro C1 hC1 C2 hC2 heq
    rcases Finset.mem_image.mp hC1 with ⟨x1, hx1, rfl⟩
    rcases Finset.mem_image.mp hC2 with ⟨x2, hx2, rfl⟩
    have hsub1_in : sub x1 ∈ (comp V E x1).erase v := by
      rw [hcomp_erase x1 hx1]
      exact mem_comp_iff.mpr ⟨hsub_mem x1 hx1, reach_refl E' (sub x1)⟩
    dsimp only at heq
    rw [heq, hcomp_erase x2 hx2] at hsub1_in
    have h21 : Reach E x2 x1 := (hreach_iff x2 x1).mp (mem_comp_iff.mp hsub1_in).2
    exact (comp_eq_iff hx1 hx2).mpr (reach_symm h21)
  have hcc_eq : cc V' E' = cc V E := by
    change S'.card = S.card
    rw [hS'_eq, Finset.card_image_of_injOn hinj]
  have hlen : E'.length + 1 = E.length := by
    dsimp only [E', E]
    simp only [List.length_map, List.length_append, List.length_cons]
    omega
  have hVcard : V'.card + 1 = V.card := by
    dsimp only [V']
    rw [Finset.card_erase_of_mem hv]
    have := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  change E'.length + cc V' E' - V'.card = E.length + cc V E - V.card
  rw [hcc_eq]
  omega

private theorem foldl_wires_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
    acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih]
    simp only [List.length_append, List.length_singleton]
    omega

private theorem foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ)
    (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) acc).getD i false =
    acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (t : ℕ)
    (ht : t < gs.length) :
    let final := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) acc
    final.getD (acc.length + t) false =
      gs[t].op.eval (gs[t].inputs.map fun j => if j < acc.length + t then final.getD j false else false) := by
  induction gs generalizing acc t with
  | nil => simp at ht
  | cons g gs ih =>
    dsimp only
    cases t with
    | zero =>
      simp only [List.foldl_cons, add_zero, List.getElem_cons_zero]
      let step := acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]
      have hlen : acc.length < step.length := by
        dsimp only [step]; simp only [List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs step acc.length hlen]
      have hstep_at : step.getD acc.length false =
          g.op.eval (g.inputs.map fun j => acc.getD j false) := by
        simp [step, List.getD_eq_getElem?_getD]
      rw [hstep_at]
      congr 1
      apply List.map_congr_left
      intro j _
      by_cases hj : j < acc.length
      · simp only [hj, ↓reduceIte]
        have hj' : j < step.length := by omega
        rw [foldl_wires_getD_lt gs step j hj']
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
      · have hnone : acc[j]? = none := List.getElem?_eq_none (by omega)
        simp only [hj, ↓reduceIte, List.getD_eq_getElem?_getD, hnone]
        rfl
    | succ t =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      let step := acc ++ [g.op.eval (g.inputs.map fun j => acc.getD j false)]
      have ht' : t < gs.length := by simp at ht; omega
      have hlen : step.length = acc.length + 1 := by
        dsimp only [step]; simp only [List.length_append, List.length_singleton]
      have heq : acc.length + (t + 1) = step.length + t := by omega
      rw [heq]
      exact ih step t ht'

private theorem circuit_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_length C.gates x

private theorem circuit_wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_wires_getD_lt C.gates x i hi

private theorem circuit_wires_getD_gate (C : Circuit) (x : List Bool) (t : ℕ) (ht : t < C.gates.length) :
    (C.wires x).getD (x.length + t) false =
      C.gates[t].op.eval
        (C.gates[t].inputs.map fun j => if j < x.length + t then (C.wires x).getD j false else false) :=
  foldl_wires_getD_gate C.gates x t ht

private inductive NodeOp (k : ℕ)
  | inp (j : Fin k)
  | const (b : Bool)
  | copy (a : ℕ)
  | neg (a : ℕ)
  | bin (isAnd : Bool) (a b : ℕ)

private def nodeChildren {k : ℕ} : NodeOp k → List ℕ
  | NodeOp.inp _ => []
  | NodeOp.const _ => []
  | NodeOp.copy a => [a]
  | NodeOp.neg a => [a]
  | NodeOp.bin _ a b => [a, b]

private def mapNodeOp {k : ℕ} (f : ℕ → ℕ) : NodeOp k → NodeOp k
  | NodeOp.inp j => NodeOp.inp j
  | NodeOp.const b => NodeOp.const b
  | NodeOp.copy a => NodeOp.copy (f a)
  | NodeOp.neg a => NodeOp.neg (f a)
  | NodeOp.bin isAnd a b => NodeOp.bin isAnd (f a) (f b)

private def isNegOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.neg _ => true
  | _ => false

private def isBinOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.bin _ _ _ => true
  | _ => false

private def isInpOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.inp _ => true
  | _ => false

private def isConstOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.const _ => true
  | _ => false

private def isCopyOp {k : ℕ} : NodeOp k → Bool
  | NodeOp.copy _ => true
  | _ => false

private def evalOp {k : ℕ} (val : ℕ → Bool) (y : Fin k → Bool) : NodeOp k → Bool
  | NodeOp.inp j => y j
  | NodeOp.const b => b
  | NodeOp.copy a => val a
  | NodeOp.neg a => !(val a)
  | NodeOp.bin true a b => val a && val b
  | NodeOp.bin false a b => val a || val b

private theorem evalOp_congr {k : ℕ} {val1 val2 : ℕ → Bool} {y : Fin k → Bool} {o : NodeOp k}
    (h : ∀ a ∈ nodeChildren o, val1 a = val2 a) :
    evalOp val1 y o = evalOp val2 y o := by
  cases o with
  | inp _ => rfl
  | const _ => rfl
  | copy a => exact h a (by simp [nodeChildren])
  | neg a => simp only [evalOp, h a (by simp [nodeChildren])]
  | bin isAnd a b =>
    have ha := h a (by simp [nodeChildren])
    have hb := h b (by simp [nodeChildren])
    cases isAnd <;> simp only [evalOp, ha, hb]

private theorem evalOp_mapNodeOp {k : ℕ} {val1 val2 : ℕ → Bool} {y : Fin k → Bool}
    {f : ℕ → ℕ} {o : NodeOp k} (h : ∀ a ∈ nodeChildren o, val1 (f a) = val2 a) :
    evalOp val1 y (mapNodeOp f o) = evalOp val2 y o := by
  cases o with
  | inp _ => rfl
  | const _ => rfl
  | copy a => exact h a (by simp [nodeChildren])
  | neg a => simp only [mapNodeOp, evalOp, h a (by simp [nodeChildren])]
  | bin isAnd a b =>
    have ha := h a (by simp [nodeChildren])
    have hb := h b (by simp [nodeChildren])
    cases isAnd <;> simp only [mapNodeOp, evalOp, ha, hb]

private def evalFuel {k : ℕ} (op : ℕ → NodeOp k) (y : Fin k → Bool) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, v => evalOp (evalFuel op y fuel) y (op v)

private structure ValidDag (k : ℕ) where
  V : Finset ℕ
  op : ℕ → NodeOp k
  out : ℕ
  hout : out ∈ V
  hchild : ∀ v ∈ V, ∀ a ∈ nodeChildren (op v), a ∈ V ∧ a < v
  hinp_inj : ∀ v1 ∈ V, ∀ v2 ∈ V, ∀ j : Fin k,
    op v1 = NodeOp.inp j → op v2 = NodeOp.inp j → v1 = v2

private def evalDag {k : ℕ} (D : ValidDag k) (y : Fin k → Bool) (v : ℕ) : Bool :=
  evalFuel D.op y (v + 1) v

private theorem evalFuel_eq_of_ge {k : ℕ} (D : ValidDag k) (y : Fin k → Bool) :
    ∀ (v : ℕ), v ∈ D.V → ∀ (f : ℕ), v + 1 ≤ f → evalFuel D.op y f v = evalDag D y v := by
  intro v
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro hv f hf
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    dsimp only [evalDag, evalFuel]
    refine evalOp_congr (fun a ha => ?_)
    have hch := D.hchild v hv a ha
    rw [ih a hch.2 hch.1 f' (by omega), ih a hch.2 hch.1 v (by omega)]

private theorem evalDag_unfold {k : ℕ} (D : ValidDag k) (y : Fin k → Bool) {v : ℕ} (hv : v ∈ D.V) :
    evalDag D y v = evalOp (evalDag D y) y (D.op v) := by
  dsimp only [evalDag, evalFuel]
  refine evalOp_congr (fun a ha => ?_)
  have hch := D.hchild v hv a ha
  exact evalFuel_eq_of_ge D y a hch.1 v (by omega)

private def dagEdges {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : List (ℕ × ℕ) :=
  (V.sort (· ≤ ·)).flatMap (fun v => (nodeChildren (op v)).map (fun a => (a, v)))

private theorem dagEdges_allIn {k : ℕ} (D : ValidDag k) :
    ∀ e ∈ dagEdges D.V D.op, e.1 ∈ D.V ∧ e.2 ∈ D.V := by
  intro e he
  rcases List.mem_flatMap.mp he with ⟨v, hv, hev⟩
  have hvV : v ∈ D.V := (Finset.mem_sort (· ≤ ·)).mp hv
  rcases List.mem_map.mp hev with ⟨a, ha, rfl⟩
  exact ⟨(D.hchild v hvV a ha).1, hvV⟩

private theorem dagEdges_length {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) :
    (dagEdges V op).length = ∑ v ∈ V, (nodeChildren (op v)).length := by
  dsimp only [dagEdges]
  rw [List.length_flatMap]
  have hmap : ((V.sort (· ≤ ·)).map (fun v => ((nodeChildren (op v)).map (fun a => (a, v))).length)) =
      (V.sort (· ≤ ·)).map (fun v => (nodeChildren (op v)).length) := by
    apply List.map_congr_left
    intro v _
    exact List.length_map _
  rw [hmap]
  rw [Finset.sum_eq_multiset_sum]
  have hcoe : ((V.sort (· ≤ ·) : List ℕ) : Multiset ℕ) = V.val := Finset.sort_eq (r := (· ≤ ·)) V
  rw [← hcoe, Multiset.map_coe, Multiset.sum_coe]

private def negCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isNegOp (op v))).card

private def binCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isBinOp (op v))).card

private def inpCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isInpOp (op v))).card

private def constCount {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) : ℕ :=
  (V.filter (fun v => isConstOp (op v))).card

private theorem dag_edge_vertex_identity {k : ℕ} (V : Finset ℕ) (op : ℕ → NodeOp k) :
    (dagEdges V op).length + inpCount V op + constCount V op = V.card + binCount V op := by
  rw [dagEdges_length]
  dsimp only [inpCount, constCount, binCount]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  have hcard : V.card = ∑ _ ∈ V, 1 := by simp
  rw [hcard, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  cases op v <;> simp [nodeChildren, isInpOp, isConstOp, isBinOp]

private theorem sublist_of_pairwise_lt {l1 l2 : List ℕ}
    (h1 : l1.Pairwise (· < ·)) (h2 : l2.Pairwise (· < ·))
    (hsub : ∀ x ∈ l1, x ∈ l2) : l1.Sublist l2 := by
  induction l2 generalizing l1 with
  | nil =>
    cases l1 with
    | nil => exact List.Sublist.slnil
    | cons a l1' =>
      exfalso
      exact List.not_mem_nil (hsub a (List.mem_cons_self ..))
  | cons b l2 ih =>
    cases l1 with
    | nil => exact List.nil_sublist _
    | cons a l1' =>
      have ha_in : a ∈ b :: l2 := hsub a (List.mem_cons_self ..)
      have hb_lt : ∀ y ∈ l2, b < y := (List.pairwise_cons.mp h2).1
      have h2' : l2.Pairwise (· < ·) := (List.pairwise_cons.mp h2).2
      have ha_lt : ∀ y ∈ l1', a < y := (List.pairwise_cons.mp h1).1
      have h1' : l1'.Pairwise (· < ·) := (List.pairwise_cons.mp h1).2
      rcases List.mem_cons.mp ha_in with rfl | ha2
      · refine List.Sublist.cons_cons a (ih h1' h2' ?_)
        intro x hx
        have hax : a < x := ha_lt x hx
        rcases List.mem_cons.mp (hsub x (List.mem_cons_of_mem _ hx)) with rfl | hx2
        · omega
        · exact hx2
      · refine List.Sublist.cons b (ih h1 h2' ?_)
        intro x hx
        have hba : b < a := hb_lt a ha2
        rcases List.mem_cons.mp (hsub x hx) with rfl | hx2
        · rcases List.mem_cons.mp hx with rfl | hx1'
          · omega
          · have := ha_lt x hx1'; omega
        · exact hx2

private theorem sort_sublist_of_subset {R V : Finset ℕ} (hRV : R ⊆ V) :
    (R.sort (· ≤ ·)).Sublist (V.sort (· ≤ ·)) := by
  have hp : ∀ S : Finset ℕ, (S.sort (· ≤ ·)).Pairwise (· < ·) := by
    intro S
    have hle := Finset.pairwise_sort S (· ≤ ·)
    have hnd := Finset.sort_nodup (r := (· ≤ ·)) S
    exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
      have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
      have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
      omega)
  refine sublist_of_pairwise_lt (hp R) (hp V) ?_
  intro x hx
  exact (Finset.mem_sort (· ≤ ·)).mpr (hRV ((Finset.mem_sort (· ≤ ·)).mp hx))

private theorem sublist_flatMap {α β : Type} {l1 l2 : List α} (h : l1.Sublist l2) (f : α → List β) :
    (l1.flatMap f).Sublist (l2.flatMap f) := by
  induction h with
  | slnil => exact List.Sublist.slnil
  | cons a _ ih =>
    simp only [List.flatMap_cons]
    exact ih.trans (List.sublist_append_right _ _)
  | cons_cons a _ ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (List.Sublist.refl _) ih

private theorem flatMap_sublist_of_pointwise {α β : Type} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, (f x).Sublist (g x)) : (l.flatMap f).Sublist (l.flatMap g) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact List.Sublist.append (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

private def DirStep {k : ℕ} (D : ValidDag k) (x y : ℕ) : Prop :=
  y ∈ D.V ∧ x ∈ nodeChildren (D.op y)

private def DirReach {k : ℕ} (D : ValidDag k) (x y : ℕ) : Prop :=
  Relation.ReflTransGen (DirStep D) x y

private noncomputable def trimDag {k : ℕ} (D : ValidDag k) : ValidDag k := by
  classical
  let R := D.V.filter (fun x => DirReach D x D.out)
  refine ⟨R, D.op, D.out, ?_, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨D.hout, Relation.ReflTransGen.refl⟩
  · intro v hv a ha
    have hvV : v ∈ D.V := (Finset.mem_filter.mp hv).1
    have hvR : DirReach D v D.out := (Finset.mem_filter.mp hv).2
    have hch := D.hchild v hvV a ha
    refine ⟨Finset.mem_filter.mpr ⟨hch.1, Relation.ReflTransGen.head ⟨hvV, ha⟩ hvR⟩, hch.2⟩
  · intro v1 hv1 v2 hv2 j h1 h2
    exact D.hinp_inj v1 (Finset.mem_filter.mp hv1).1 v2 (Finset.mem_filter.mp hv2).1 j h1 h2

private theorem trimDag_connected {k : ℕ} (D : ValidDag k) :
    cc (trimDag D).V (dagEdges (trimDag D).V (trimDag D).op) = 1 := by
  classical
  refine cc_connected (trimDag D).hout ?_
  intro x hx
  have hdir : DirReach D x D.out := (Finset.mem_filter.mp hx).2
  have hback : ∀ u v, DirReach D u v → v ∈ (trimDag D).V →
      Reach (dagEdges (trimDag D).V (trimDag D).op) v u := by
    intro u v huv
    induction huv with
    | refl => intro _; exact reach_refl _ _
    | @tail b c _ hbc ih =>
      intro hcV
      have hbV : b ∈ (trimDag D).V := ((trimDag D).hchild c hcV b hbc.2).1
      have hedge : (b, c) ∈ dagEdges (trimDag D).V (trimDag D).op := by
        dsimp only [dagEdges]
        refine List.mem_flatMap.mpr ⟨c, (Finset.mem_sort (· ≤ ·)).mpr hcV, ?_⟩
        exact List.mem_map.mpr ⟨b, hbc.2, rfl⟩
      exact Relation.ReflTransGen.head (Or.inr hedge) (ih hbV)
  exact hback x D.out hdir (trimDag D).hout

private theorem trimDag_beta1 {k : ℕ} (D : ValidDag k) :
    beta1 (trimDag D).V (dagEdges (trimDag D).V (trimDag D).op) ≤
      beta1 D.V (dagEdges D.V D.op) := by
  classical
  have hRV : (trimDag D).V ⊆ D.V := Finset.filter_subset _ _
  have hsub : (dagEdges (trimDag D).V (trimDag D).op).Sublist (dagEdges D.V D.op) :=
    sublist_flatMap (sort_sublist_of_subset hRV) _
  have h1 := beta1_restrict_isolated hRV (dagEdges_allIn (trimDag D))
  have h2 := beta1_sublist hsub (dagEdges_allIn D)
  omega

private theorem trimDag_negCount {k : ℕ} (D : ValidDag k) :
    negCount (trimDag D).V (trimDag D).op ≤ negCount D.V D.op := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))

private def IsNormalForm {k : ℕ} (D : ValidDag k) : Prop :=
  (∀ x ∈ D.V, DirReach D x D.out) ∧
  (∀ v ∈ D.V, ¬ isConstOp (D.op v) ∧ ¬ isCopyOp (D.op v))

private theorem reduce_to_normal_form {k : ℕ} (D0 : ValidDag k)
    (hnc : ∃ y1 y2 : Fin k → Bool, evalDag D0 y1 D0.out ≠ evalDag D0 y2 D0.out) :
    ∃ D : ValidDag k,
      IsNormalForm D ∧
      beta1 D.V (dagEdges D.V D.op) ≤ beta1 D0.V (dagEdges D0.V D0.op) ∧
      negCount D.V D.op ≤ negCount D0.V D0.op ∧
      ∀ y : Fin k → Bool, evalDag D y D.out = evalDag D0 y D0.out := by
  classical
  have hmain : ∀ m : ℕ, ∀ D : ValidDag k,
      D.V.card + (dagEdges D.V D.op).length ≤ m →
      (∃ y1 y2 : Fin k → Bool, evalDag D y1 D.out ≠ evalDag D y2 D.out) →
      ∃ D' : ValidDag k,
        IsNormalForm D' ∧
        beta1 D'.V (dagEdges D'.V D'.op) ≤ beta1 D.V (dagEdges D.V D.op) ∧
        negCount D'.V D'.op ≤ negCount D.V D.op ∧
        ∀ y : Fin k → Bool, evalDag D' y D'.out = evalDag D y D.out := by
    intro m
    induction m with
    | zero =>
      intro D hm _
      have := Finset.card_pos.mpr ⟨D.out, D.hout⟩
      omega
    | succ m ih =>
      intro D hm hncD
      by_cases htrim : ∀ x ∈ D.V, DirReach D x D.out
      · by_cases halias : ∃ v ∈ D.V, ∃ a, D.op v = NodeOp.copy a
        · rcases halias with ⟨v, hvV, a, hopv⟩
          have ha := D.hchild v hvV a (by simp [hopv, nodeChildren])
          let sub : ℕ → ℕ := fun x => if x = v then a else x
          let V' := D.V.erase v
          let op' : ℕ → NodeOp k := fun u => mapNodeOp sub (D.op u)
          let out' := sub D.out
          have hsub_lt : ∀ u ∈ V', ∀ c ∈ nodeChildren (op' u), c ∈ V' ∧ c < u := by
            intro u huV' c hc
            have huV : u ∈ D.V := Finset.mem_of_mem_erase huV'
            have hch_map : nodeChildren (op' u) = (nodeChildren (D.op u)).map sub := by
              dsimp only [op']; cases D.op u <;> simp [mapNodeOp, nodeChildren]
            rw [hch_map] at hc
            rcases List.mem_map.mp hc with ⟨c0, hc0, rfl⟩
            have hc0_ok := D.hchild u huV c0 hc0
            dsimp only [sub]
            split_ifs with hcv
            · refine ⟨Finset.mem_erase.mpr ⟨by omega, ha.1⟩, by omega⟩
            · refine ⟨Finset.mem_erase.mpr ⟨hcv, hc0_ok.1⟩, hc0_ok.2⟩
          have hinj' : ∀ v1 ∈ V', ∀ v2 ∈ V', ∀ j : Fin k,
              op' v1 = NodeOp.inp j → op' v2 = NodeOp.inp j → v1 = v2 := by
            intro v1 hv1 v2 hv2 j h1 h2
            have h1' : D.op v1 = NodeOp.inp j := by
              dsimp only [op'] at h1; cases h : D.op v1 <;> simp [h, mapNodeOp] at h1 ⊢; exact h1
            have h2' : D.op v2 = NodeOp.inp j := by
              dsimp only [op'] at h2; cases h : D.op v2 <;> simp [h, mapNodeOp] at h2 ⊢; exact h2
            exact D.hinp_inj v1 (Finset.mem_of_mem_erase hv1) v2 (Finset.mem_of_mem_erase hv2) j h1' h2'
          have hout' : out' ∈ V' := by
            dsimp only [out', sub, V']
            split_ifs with h
            · exact Finset.mem_erase.mpr ⟨by omega, ha.1⟩
            · exact Finset.mem_erase.mpr ⟨h, D.hout⟩
          let D1 : ValidDag k := ⟨V', op', out', hout', hsub_lt, hinj'⟩
          have heval_all : ∀ y : Fin k → Bool, ∀ u ∈ D.V,
              evalDag D1 y (sub u) = evalDag D y u := by
            intro y u
            induction u using Nat.strong_induction_on with
            | ind u ihu =>
              intro huV
              by_cases huv : u = v
              · subst huv
                have hsubv : sub u = a := by simp [sub]
                have hsuba : sub a = a := by
                  dsimp only [sub]; split_ifs <;> omega
                rw [hsubv, evalDag_unfold D y huV, hopv]
                dsimp only [evalOp]
                rw [← ihu a ha.2 ha.1, hsuba]
              · have hsubu : sub u = u := by simp [sub, huv]
                have huV' : u ∈ V' := Finset.mem_erase.mpr ⟨huv, huV⟩
                rw [hsubu, evalDag_unfold D1 y huV', evalDag_unfold D y huV]
                change evalOp (evalDag D1 y) y (mapNodeOp sub (D.op u)) = evalOp (evalDag D y) y (D.op u)
                exact evalOp_mapNodeOp (fun c hc =>
                  ihu c (D.hchild u huV c hc).2 (D.hchild u huV c hc).1)
          have heval1 : ∀ y, evalDag D1 y D1.out = evalDag D y D.out :=
            fun y => heval_all y D.out D.hout
          have hbeta1 : beta1 D1.V (dagEdges D1.V D1.op) = beta1 D.V (dagEdges D.V D.op) := by
            have hv_sort : v ∈ D.V.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hvV
            rcases List.append_of_mem hv_sort with ⟨L1, L2, hL⟩
            have hLnd : (L1 ++ v :: L2).Nodup := by rw [← hL]; exact Finset.sort_nodup _ _
            have hv_not1 : v ∉ L1 := by
              intro h; exact (List.nodup_append.mp hLnd).2.2 v h v (List.mem_cons_self ..) rfl
            have hv_not2 : v ∉ L2 := (List.nodup_cons.mp (List.nodup_append.mp hLnd).2.1).1
            have hsort' : V'.sort (· ≤ ·) = L1 ++ L2 := by
              have hp1 : (V'.sort (· ≤ ·)).Pairwise (· < ·) := by
                have hle := Finset.pairwise_sort V' (· ≤ ·)
                have hnd := Finset.sort_nodup (r := (· ≤ ·)) V'
                exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
                  have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
                  have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
                  omega)
              have hp2 : (L1 ++ L2).Pairwise (· < ·) := by
                have hfull : (D.V.sort (· ≤ ·)).Pairwise (· < ·) := by
                  have hle := Finset.pairwise_sort D.V (· ≤ ·)
                  have hnd := Finset.sort_nodup (r := (· ≤ ·)) D.V
                  exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
                    have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
                    have h2 := List.pairwise_iff_getElem.mp hnd i j hi hj hij
                    omega)
                rw [hL] at hfull
                exact hfull.sublist (List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self _ _))
              have hmem_eq : ∀ x, x ∈ V'.sort (· ≤ ·) ↔ x ∈ L1 ++ L2 := by
                intro x
                rw [Finset.mem_sort, Finset.mem_erase, ← Finset.mem_sort (r := (· ≤ ·)), hL]
                simp only [List.mem_append, List.mem_cons]
                constructor
                · rintro ⟨hne, h1 | rfl | h2⟩
                  · exact Or.inl h1
                  · exact absurd rfl hne
                  · exact Or.inr h2
                · rintro (h1 | h2)
                  · exact ⟨fun h => hv_not1 (h ▸ h1), Or.inl h1⟩
                  · exact ⟨fun h => hv_not2 (h ▸ h2), Or.inr (Or.inr h2)⟩
              exact List.Sublist.antisymm
                (sublist_of_pairwise_lt hp1 hp2 (fun x hx => (hmem_eq x).mp hx))
                (sublist_of_pairwise_lt hp2 hp1 (fun x hx => (hmem_eq x).mpr hx))
            let fD : ℕ → List (ℕ × ℕ) := fun u => (nodeChildren (D.op u)).map (fun c => (c, u))
            let fD1 : ℕ → List (ℕ × ℕ) := fun u => (nodeChildren (op' u)).map (fun c => (c, u))
            have hE_eq : dagEdges D.V D.op = L1.flatMap fD ++ (a, v) :: L2.flatMap fD := by
              dsimp only [dagEdges, fD]
              rw [hL, List.flatMap_append, List.flatMap_cons, hopv]
              simp [nodeChildren]
            have hE1_eq : dagEdges D1.V D1.op =
                (L1.flatMap fD ++ L2.flatMap fD).map (fun e => (sub e.1, sub e.2)) := by
              dsimp only [dagEdges, D1]
              rw [hsort', List.flatMap_append, List.map_append]
              have hcongr : ∀ L : List ℕ, v ∉ L →
                  L.flatMap fD1 = (L.flatMap fD).map (fun e => (sub e.1, sub e.2)) := by
                intro L hnv
                rw [List.map_flatMap]
                apply List.flatMap_congr
                intro u hu
                have huv : u ≠ v := fun h => hnv (h ▸ hu)
                have hsubu : sub u = u := by simp [sub, huv]
                dsimp only [fD1, fD, op']
                cases D.op u <;> simp [mapNodeOp, nodeChildren, hsubu]
              exact congrArg₂ (· ++ ·) (hcongr L1 hv_not1) (hcongr L2 hv_not2)
            rw [hE_eq, hE1_eq]
            exact beta1_contract ha.1 hvV (by omega)
          have hneg1 : negCount D1.V D1.op ≤ negCount D.V D.op := by
            refine Finset.card_le_card ?_
            intro u hu
            rcases Finset.mem_filter.mp hu with ⟨huV', hneg⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase huV', ?_⟩
            dsimp only [D1, op'] at hneg
            cases h : D.op u <;> simp [h, mapNodeOp, isNegOp] at hneg ⊢
          have hmeas : D1.V.card + (dagEdges D1.V D1.op).length ≤ m := by
            have hcard1 : D1.V.card + 1 = D.V.card := by
              dsimp only [D1, V']; rw [Finset.card_erase_of_mem hvV]
              have := Finset.card_pos.mpr ⟨v, hvV⟩; omega
            have hedge1 : (dagEdges D1.V D1.op).length ≤ (dagEdges D.V D.op).length := by
              rw [dagEdges_length, dagEdges_length]
              have hsub_V : D1.V ⊆ D.V := Finset.erase_subset _ _
              refine (Finset.sum_le_sum (fun u _ => ?_)).trans
                (Finset.sum_le_sum_of_subset hsub_V)
              dsimp only [D1, op']
              cases D.op u <;> simp [mapNodeOp, nodeChildren]
            omega
          have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := by
            rcases hncD with ⟨y1, y2, hne⟩
            exact ⟨y1, y2, by rw [heval1 y1, heval1 y2]; exact hne⟩
          rcases ih D1 hmeas hnc1 with ⟨D', hnf, hb', hn', he'⟩
          exact ⟨D', hnf, hb'.trans (le_of_eq hbeta1), hn'.trans hneg1, fun y => (he' y).trans (heval1 y)⟩
        · have hno_alias : ∀ v ∈ D.V, ¬ isCopyOp (D.op v) := by
            intro v hvV hal
            cases hop : D.op v <;> simp [hop, isCopyOp] at hal
            exact halias ⟨v, hvV, _, hop⟩
          by_cases hdup : ∃ v ∈ D.V, ∃ isAnd a, D.op v = NodeOp.bin isAnd a a
          · rcases hdup with ⟨v, hvV, isAnd, a, hopv⟩
            let op' : ℕ → NodeOp k := fun u => if u = v then NodeOp.copy a else D.op u
            have hch' : ∀ u ∈ D.V, ∀ c ∈ nodeChildren (op' u), c ∈ D.V ∧ c < u := by
              intro u hu c hc
              dsimp only [op'] at hc
              split_ifs at hc with huv
              · subst huv
                have hc' : c = a := by simpa [nodeChildren] using hc
                subst hc'
                exact D.hchild u hu c (by simp [hopv, nodeChildren])
              · exact D.hchild u hu c hc
            have hinj' : ∀ v1 ∈ D.V, ∀ v2 ∈ D.V, ∀ j : Fin k,
                op' v1 = NodeOp.inp j → op' v2 = NodeOp.inp j → v1 = v2 := by
              intro v1 hv1 v2 hv2 j h1 h2
              dsimp only [op'] at h1 h2
              by_cases h1v : v1 = v
              · simp only [h1v, ↓reduceIte] at h1; cases h1
              · by_cases h2v : v2 = v
                · simp only [h2v, ↓reduceIte] at h2; cases h2
                · simp only [h1v, h2v, ↓reduceIte] at h1 h2
                  exact D.hinp_inj v1 hv1 v2 hv2 j h1 h2
            let D1 : ValidDag k := ⟨D.V, op', D.out, D.hout, hch', hinj'⟩
            have heval_all : ∀ y u, u ∈ D.V → evalDag D1 y u = evalDag D y u := by
              intro y u
              induction u using Nat.strong_induction_on with
              | ind u ihu =>
                intro huV
                rw [evalDag_unfold D1 y huV, evalDag_unfold D y huV]
                change evalOp (evalDag D1 y) y (op' u) = evalOp (evalDag D y) y (D.op u)
                dsimp only [op']
                split_ifs with huv
                · subst huv
                  have ha := D.hchild u huV a (by simp [hopv, nodeChildren])
                  rw [hopv]
                  simp only [evalOp, ihu a ha.2 ha.1]
                  cases isAnd <;> simp
                · exact evalOp_congr (fun c hc =>
                    ihu c (D.hchild u huV c hc).2 (D.hchild u huV c hc).1)
            have hsubE : (dagEdges D1.V D1.op).Sublist (dagEdges D.V D.op) := by
              dsimp only [dagEdges, D1]
              apply flatMap_sublist_of_pointwise
              intro u _
              dsimp only [op']
              split_ifs with huv
              · subst huv; rw [hopv]; simp [nodeChildren]
              · exact List.Sublist.refl _
            have hbeta1 : beta1 D1.V (dagEdges D1.V D1.op) ≤ beta1 D.V (dagEdges D.V D.op) :=
              beta1_sublist hsubE (dagEdges_allIn D)
            have hneg1 : negCount D1.V D1.op ≤ negCount D.V D.op := by
              refine Finset.card_le_card ?_
              intro u hu
              rcases Finset.mem_filter.mp hu with ⟨huV, hn⟩
              refine Finset.mem_filter.mpr ⟨huV, ?_⟩
              dsimp only [D1, op'] at hn
              split_ifs at hn with huv
              · simp [isNegOp] at hn
              · exact hn
            have hlen_lt : (dagEdges D1.V D1.op).length < (dagEdges D.V D.op).length := by
              rw [dagEdges_length, dagEdges_length]
              refine Finset.sum_lt_sum (fun u _ => ?_) ⟨v, hvV, ?_⟩
              · dsimp only [D1, op']; split_ifs with huv
                · subst huv; rw [hopv]; simp [nodeChildren]
                · exact le_rfl
              · dsimp only [D1, op']; simp [hopv, nodeChildren]
            have hmeas : D1.V.card + (dagEdges D1.V D1.op).length ≤ m := by
              have hVcard : D1.V.card = D.V.card := rfl
              omega
            have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := by
              rcases hncD with ⟨y1, y2, hne⟩
              exact ⟨y1, y2, by rw [heval_all y1 D.out D.hout, heval_all y2 D.out D.hout]; exact hne⟩
            rcases ih D1 hmeas hnc1 with ⟨D', hnf, hb', hn', he'⟩
            exact ⟨D', hnf, hb'.trans hbeta1, hn'.trans hneg1,
              fun y => (he' y).trans (heval_all y D.out D.hout)⟩
          · by_cases hconst : ∃ c ∈ D.V, isConstOp (D.op c)
            · rcases hconst with ⟨c, hcV, hcop⟩
              cases hopc : D.op c with
              | const bval =>
                have hc_ne_out : c ≠ D.out := by
                  intro heq
                  subst heq
                  rcases hncD with ⟨y1, y2, hne⟩
                  rw [evalDag_unfold D y1 hcV, evalDag_unfold D y2 hcV, hopc] at hne
                  exact hne rfl
                have hparent : ∃ v ∈ D.V, c ∈ nodeChildren (D.op v) := by
                  have hrc : DirReach D c D.out := htrim c hcV
                  rcases Relation.ReflTransGen.cases_head hrc with rfl | ⟨w, hcw, _⟩
                  · exact absurd rfl hc_ne_out
                  · exact ⟨w, hcw.1, hcw.2⟩
                rcases hparent with ⟨v, hvV, hcv⟩
                have hred : ∃ newOp : NodeOp k,
                    (nodeChildren newOp).Sublist (nodeChildren (D.op v)) ∧
                    (nodeChildren newOp).length < (nodeChildren (D.op v)).length ∧
                    (isNegOp newOp = true → isNegOp (D.op v) = true) ∧
                    (∀ j, newOp ≠ NodeOp.inp j) ∧
                    ∀ y, evalOp (evalDag D y) y newOp = evalDag D y v := by
                  cases hopv : D.op v with
                  | inp j => simp [hopv, nodeChildren] at hcv
                  | const b => simp [hopv, nodeChildren] at hcv
                  | copy a => exact absurd (by simp [hopv, isCopyOp]) (hno_alias v hvV)
                  | neg a =>
                    have hac : c = a := by simpa [hopv, nodeChildren] using hcv
                    subst hac
                    refine ⟨NodeOp.const (!bval), by simp [nodeChildren], by simp [nodeChildren],
                      by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                    rw [evalDag_unfold D y hvV, hopv]; simp only [evalOp, evalDag_unfold D y hcV, hopc]
                  | bin isAnd a b =>
                    have hab : c = a ∨ c = b := by simpa [hopv, nodeChildren] using hcv
                    rcases hab with rfl | rfl
                    · cases isAnd
                      · cases bval
                        · refine ⟨NodeOp.copy b, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.const true, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                      · cases bval
                        · refine ⟨NodeOp.const false, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.copy b, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                    · cases isAnd
                      · cases bval
                        · refine ⟨NodeOp.copy a, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.const true, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                      · cases bval
                        · refine ⟨NodeOp.const false, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                        · refine ⟨NodeOp.copy a, by simp [nodeChildren], by simp [nodeChildren],
                            by simp [isNegOp], by intro j; simp, fun y => ?_⟩
                          rw [evalDag_unfold D y hvV, hopv]; simp [evalOp, evalDag_unfold D y hcV, hopc]
                rcases hred with ⟨newOp, hsub_ch, hlen_ch, hneg_ch, hnoinp, heval_v⟩
                let op' : ℕ → NodeOp k := fun u => if u = v then newOp else D.op u
                have hch' : ∀ u ∈ D.V, ∀ a ∈ nodeChildren (op' u), a ∈ D.V ∧ a < u := by
                  intro u hu a ha
                  dsimp only [op'] at ha
                  split_ifs at ha with huv
                  · subst huv; exact D.hchild u hu a (hsub_ch.subset ha)
                  · exact D.hchild u hu a ha
                have hinj' : ∀ v1 ∈ D.V, ∀ v2 ∈ D.V, ∀ j : Fin k,
                    op' v1 = NodeOp.inp j → op' v2 = NodeOp.inp j → v1 = v2 := by
                  intro v1 hv1 v2 hv2 j h1 h2
                  dsimp only [op'] at h1 h2
                  by_cases h1v : v1 = v
                  · simp only [h1v, ↓reduceIte] at h1; exact absurd h1 (hnoinp j)
                  · by_cases h2v : v2 = v
                    · simp only [h2v, ↓reduceIte] at h2; exact absurd h2 (hnoinp j)
                    · simp only [h1v, h2v, ↓reduceIte] at h1 h2
                      exact D.hinp_inj v1 hv1 v2 hv2 j h1 h2
                let D1 : ValidDag k := ⟨D.V, op', D.out, D.hout, hch', hinj'⟩
                have heval_all : ∀ y u, u ∈ D.V → evalDag D1 y u = evalDag D y u := by
                  intro y u
                  induction u using Nat.strong_induction_on with
                  | ind u ihu =>
                    intro huV
                    rw [evalDag_unfold D1 y huV]
                    change evalOp (evalDag D1 y) y (op' u) = evalDag D y u
                    dsimp only [op']
                    split_ifs with huv
                    · subst huv
                      rw [← heval_v y]
                      exact evalOp_congr (fun a ha =>
                        ihu a (D.hchild u huV a (hsub_ch.subset ha)).2 (D.hchild u huV a (hsub_ch.subset ha)).1)
                    · rw [evalDag_unfold D y huV]
                      exact evalOp_congr (fun a ha =>
                        ihu a (D.hchild u huV a ha).2 (D.hchild u huV a ha).1)
                have hsubE : (dagEdges D1.V D1.op).Sublist (dagEdges D.V D.op) := by
                  dsimp only [dagEdges, D1]
                  apply flatMap_sublist_of_pointwise
                  intro u _
                  dsimp only [op']
                  split_ifs with huv
                  · subst huv; exact hsub_ch.map _
                  · exact List.Sublist.refl _
                have hbeta1 : beta1 D1.V (dagEdges D1.V D1.op) ≤ beta1 D.V (dagEdges D.V D.op) :=
                  beta1_sublist hsubE (dagEdges_allIn D)
                have hneg1 : negCount D1.V D1.op ≤ negCount D.V D.op := by
                  refine Finset.card_le_card ?_
                  intro u hu
                  rcases Finset.mem_filter.mp hu with ⟨huV, hn⟩
                  refine Finset.mem_filter.mpr ⟨huV, ?_⟩
                  dsimp only [D1, op'] at hn
                  split_ifs at hn with huv
                  · subst huv; exact hneg_ch hn
                  · exact hn
                have hlen_lt : (dagEdges D1.V D1.op).length < (dagEdges D.V D.op).length := by
                  rw [dagEdges_length, dagEdges_length]
                  refine Finset.sum_lt_sum (fun u _ => ?_) ⟨v, hvV, ?_⟩
                  · dsimp only [D1, op']; split_ifs with huv
                    · subst huv; exact le_of_lt hlen_ch
                    · exact le_rfl
                  · dsimp only [D1, op']; simp [hlen_ch]
                have hmeas : D1.V.card + (dagEdges D1.V D1.op).length ≤ m := by
                  have hVcard : D1.V.card = D.V.card := rfl
                  omega
                have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := by
                  rcases hncD with ⟨y1, y2, hne⟩
                  exact ⟨y1, y2, by rw [heval_all y1 D.out D.hout, heval_all y2 D.out D.hout]; exact hne⟩
                rcases ih D1 hmeas hnc1 with ⟨D', hnf, hb', hn', he'⟩
                exact ⟨D', hnf, hb'.trans hbeta1, hn'.trans hneg1,
                  fun y => (he' y).trans (heval_all y D.out D.hout)⟩
              | inp _ => simp [hopc, isConstOp] at hcop
              | copy _ => simp [hopc, isConstOp] at hcop
              | neg _ => simp [hopc, isConstOp] at hcop
              | bin _ _ _ => simp [hopc, isConstOp] at hcop
            · push Not at hconst
              exact ⟨D, ⟨htrim, fun v hv => ⟨by intro h; exact absurd h (by simp [hconst v hv]),
                hno_alias v hv⟩⟩, le_rfl, le_rfl, fun _ => rfl⟩
      · let D1 := trimDag D
        have hlt_card : D1.V.card < D.V.card := by
          push Not at htrim
          rcases htrim with ⟨x, hxV, hxn⟩
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, ?_⟩)
          intro heq
          have hx1 : x ∈ D1.V := by rw [heq]; exact hxV
          exact hxn (Finset.mem_filter.mp hx1).2
        have hle_edges : (dagEdges D1.V D1.op).length ≤ (dagEdges D.V D.op).length :=
          (sublist_flatMap (sort_sublist_of_subset (Finset.filter_subset _ _)) _).length_le
        have hnc1 : ∃ y1 y2, evalDag D1 y1 D1.out ≠ evalDag D1 y2 D1.out := hncD
        rcases ih D1 (by omega) hnc1 with ⟨D', hnf, hb', hn', he'⟩
        exact ⟨D', hnf, hb'.trans (trimDag_beta1 D), hn'.trans (trimDag_negCount D),
          fun y => he' y⟩
  exact hmain (D0.V.card + (dagEdges D0.V D0.op).length) D0 le_rfl hnc

private theorem inv_eq_match (G : Circuit) :
    (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
    (G.gates.filter (fun g => match g.op with | GateOp.not => true | _ => false)).length := by
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> simp

private theorem normal_form_to_circuit {k : ℕ} (D : ValidDag k) (hnf : IsNormalForm D) :
    ∃ G : Circuit,
      FanInTwo G ∧
      (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
        negCount D.V D.op ∧
      G.size - (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
        binCount D.V D.op ∧
      ∀ y : Fin k → Bool, G.eval (List.ofFn y) = evalDag D y D.out := by
  classical
  let Gset := D.V.filter (fun v => !(isInpOp (D.op v)))
  let gl := Gset.sort (· ≤ ·)
  have hgl_nodup : gl.Nodup := Finset.sort_nodup _ _
  have hgl_sorted : gl.Pairwise (· < ·) := by
    have hle : gl.Pairwise (· ≤ ·) := Finset.pairwise_sort Gset (· ≤ ·)
    exact List.pairwise_iff_getElem.mpr (fun i j hi hj hij => by
      have h1 := List.pairwise_iff_getElem.mp hle i j hi hj hij
      have h2 := List.pairwise_iff_getElem.mp hgl_nodup i j hi hj hij
      omega)
  have hgl_mem : ∀ v, v ∈ gl ↔ v ∈ Gset := fun v => Finset.mem_sort (· ≤ ·)
  let idx : ℕ → ℕ := fun v =>
    match D.op v with
    | NodeOp.inp j => j.val
    | _ => k + gl.idxOf v
  let mkGate : ℕ → Gate := fun v =>
    match D.op v with
    | NodeOp.neg a => ⟨GateOp.not, [idx a]⟩
    | NodeOp.bin true a b => ⟨GateOp.and, [idx a, idx b]⟩
    | NodeOp.bin false a b => ⟨GateOp.or, [idx a, idx b]⟩
    | _ => ⟨GateOp.or, []⟩
  let G : Circuit := ⟨gl.map mkGate, idx D.out⟩
  have hfan : FanInTwo G := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨v, _, rfl⟩
    dsimp only [mkGate]
    cases D.op v with
    | inp _ => simp
    | const _ => simp
    | copy _ => simp
    | neg _ => simp
    | bin isAnd _ _ => cases isAnd <;> simp
  have hidx_lt : ∀ v ∈ Gset, ∀ a ∈ nodeChildren (D.op v), idx a < k + gl.idxOf v := by
    intro v hvG a ha
    have hvV : v ∈ D.V := (Finset.mem_filter.mp hvG).1
    have hach := D.hchild v hvV a ha
    have hlt_gl : a ∈ gl → gl.idxOf a < gl.idxOf v := by
      intro haG
      have hvgl : v ∈ gl := (hgl_mem v).mpr hvG
      have hia : gl.idxOf a < gl.length := List.idxOf_lt_length_iff.mpr haG
      have hiv : gl.idxOf v < gl.length := List.idxOf_lt_length_iff.mpr hvgl
      have hgeta : gl[gl.idxOf a]'hia = a := List.getElem_idxOf hia
      have hgetv : gl[gl.idxOf v]'hiv = v := List.getElem_idxOf hiv
      by_contra hge
      rcases eq_or_lt_of_le (Nat.not_lt.mp hge) with heq | hgt
      · have hav : a = v := by rw [← hgeta, ← hgetv]; congr 1; exact heq.symm
        omega
      · have := List.pairwise_iff_getElem.mp hgl_sorted (gl.idxOf v) (gl.idxOf a) hiv hia hgt
        rw [hgetv, hgeta] at this; omega
    dsimp only [idx]
    cases hopa : D.op a with
    | inp j => dsimp only; have := j.isLt; omega
    | const _ => exact absurd (by simp [hopa, isConstOp]) (hnf.2 a hach.1).1
    | copy _ => exact absurd (by simp [hopa, isCopyOp]) (hnf.2 a hach.1).2
    | neg _ =>
      dsimp only
      have haG : a ∈ gl := (hgl_mem a).mpr (Finset.mem_filter.mpr ⟨hach.1, by simp [hopa, isInpOp]⟩)
      have := hlt_gl haG
      omega
    | bin _ _ _ =>
      dsimp only
      have haG : a ∈ gl := (hgl_mem a).mpr (Finset.mem_filter.mpr ⟨hach.1, by simp [hopa, isInpOp]⟩)
      have := hlt_gl haG
      omega
  have hinv_eq : (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length =
      negCount D.V D.op := by
    rw [inv_eq_match]
    dsimp only [G]
    rw [List.filter_map, List.length_map]
    change (gl.filter (fun v => match (mkGate v).op with | GateOp.not => true | _ => false)).length = _
    have hperm : (gl.filter (fun v => match (mkGate v).op with | GateOp.not => true | _ => false)).Perm
        (D.V.filter (fun v => isNegOp (D.op v))).toList := by
      refine List.perm_ext_iff_of_nodup (hgl_nodup.filter _) (Finset.nodup_toList _) |>.mpr ?_
      intro v
      simp only [List.mem_filter, hgl_mem, Finset.mem_toList, Finset.mem_filter, Gset]
      constructor
      · rintro ⟨⟨hvV, _⟩, hnot⟩
        refine ⟨hvV, ?_⟩
        dsimp only [mkGate] at hnot
        cases h : D.op v with
        | neg _ => simp [isNegOp]
        | inp _ => simp [h] at hnot
        | const _ => simp [h] at hnot
        | copy _ => simp [h] at hnot
        | bin b _ _ => cases b <;> simp [h] at hnot
      · rintro ⟨hvV, hneg⟩
        cases h : D.op v with
        | neg _ => exact ⟨⟨hvV, by simp [isInpOp]⟩, by simp [mkGate, h]⟩
        | inp _ => simp [h, isNegOp] at hneg
        | const _ => simp [h, isNegOp] at hneg
        | copy _ => simp [h, isNegOp] at hneg
        | bin _ _ _ => simp [h, isNegOp] at hneg
    rw [hperm.length_eq, Finset.length_toList]
    rfl
  have hGsize : G.size = negCount D.V D.op + binCount D.V D.op := by
    dsimp only [Circuit.size, G]
    rw [List.length_map, Finset.length_sort]
    have hsplit : Gset = D.V.filter (fun v => isNegOp (D.op v)) ∪ D.V.filter (fun v => isBinOp (D.op v)) := by
      ext v
      simp only [Gset, Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hvV, hni⟩
        cases hop : D.op v with
        | inp _ => simp [hop, isInpOp] at hni
        | const _ => exact absurd (by simp [hop, isConstOp]) (hnf.2 v hvV).1
        | copy _ => exact absurd (by simp [hop, isCopyOp]) (hnf.2 v hvV).2
        | neg _ => exact Or.inl ⟨hvV, by simp [isNegOp]⟩
        | bin _ _ _ => exact Or.inr ⟨hvV, by simp [isBinOp]⟩
      · rintro (⟨hvV, hn⟩ | ⟨hvV, hb⟩)
        · cases hop : D.op v <;> simp [hop, isNegOp] at hn; exact ⟨hvV, by simp [isInpOp]⟩
        · cases hop : D.op v <;> simp [hop, isBinOp] at hb; exact ⟨hvV, by simp [isInpOp]⟩
    have hdisj : Disjoint (D.V.filter (fun v => isNegOp (D.op v))) (D.V.filter (fun v => isBinOp (D.op v))) := by
      rw [Finset.disjoint_left]
      intro v h1 h2
      have h1' := (Finset.mem_filter.mp h1).2
      have h2' := (Finset.mem_filter.mp h2).2
      cases hop : D.op v <;> simp [hop, isNegOp, isBinOp] at h1' h2'
    rw [hsplit, Finset.card_union_of_disjoint hdisj]
    rfl
  have heval_G : ∀ y : Fin k → Bool, ∀ v ∈ D.V,
      (G.wires (List.ofFn y)).getD (idx v) false = evalDag D y v := by
    intro y v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hvV
      rw [evalDag_unfold D y hvV]
      cases hopv : D.op v with
      | inp j =>
        have hidxv : idx v = j.val := by simp [idx, hopv]
        rw [hidxv, circuit_wires_getD_input G (List.ofFn y) j.val (by simp)]
        simp [List.getD_eq_getElem?_getD, evalOp]
      | const _ => exact absurd (by simp [hopv, isConstOp]) (hnf.2 v hvV).1
      | copy _ => exact absurd (by simp [hopv, isCopyOp]) (hnf.2 v hvV).2
      | neg a =>
        have hvG : v ∈ Gset := Finset.mem_filter.mpr ⟨hvV, by simp [hopv, isInpOp]⟩
        have hvgl : v ∈ gl := (hgl_mem v).mpr hvG
        have ht : gl.idxOf v < gl.length := List.idxOf_lt_length_iff.mpr hvgl
        have hidxv : idx v = (List.ofFn y).length + gl.idxOf v := by
          simp [idx, hopv]
        rw [hidxv, circuit_wires_getD_gate G (List.ofFn y) (gl.idxOf v) (by simp [G, ht])]
        have hget : G.gates[gl.idxOf v]'(by simp [G, ht]) = mkGate v := by
          dsimp only [G]
          rw [List.getElem_map, List.getElem_idxOf ht]
        rw [hget]
        dsimp only [mkGate]
        rw [hopv]
        have ha := D.hchild v hvV a (by simp [hopv, nodeChildren])
        have halt : idx a < (List.ofFn y).length + gl.idxOf v := by
          simpa using hidx_lt v hvG a (by simp [hopv, nodeChildren])
        simp only [List.map_cons, List.map_nil, halt, ↓reduceIte, GateOp.eval, List.headD_cons, evalOp]
        rw [ih a ha.2 ha.1]
      | bin isAnd a b =>
        have hvG : v ∈ Gset := Finset.mem_filter.mpr ⟨hvV, by simp [hopv, isInpOp]⟩
        have hvgl : v ∈ gl := (hgl_mem v).mpr hvG
        have ht : gl.idxOf v < gl.length := List.idxOf_lt_length_iff.mpr hvgl
        have hidxv : idx v = (List.ofFn y).length + gl.idxOf v := by
          simp [idx, hopv]
        rw [hidxv, circuit_wires_getD_gate G (List.ofFn y) (gl.idxOf v) (by simp [G, ht])]
        have hget : G.gates[gl.idxOf v]'(by simp [G, ht]) = mkGate v := by
          dsimp only [G]
          rw [List.getElem_map, List.getElem_idxOf ht]
        rw [hget]
        dsimp only [mkGate]
        rw [hopv]
        have ha := D.hchild v hvV a (by simp [hopv, nodeChildren])
        have hb := D.hchild v hvV b (by simp [hopv, nodeChildren])
        have halt : idx a < (List.ofFn y).length + gl.idxOf v := by
          simpa using hidx_lt v hvG a (by simp [hopv, nodeChildren])
        have hblt : idx b < (List.ofFn y).length + gl.idxOf v := by
          simpa using hidx_lt v hvG b (by simp [hopv, nodeChildren])
        cases isAnd
        · simp only [List.map_cons, List.map_nil, halt, hblt, ↓reduceIte, GateOp.eval,
            List.any_cons, List.any_nil, id_eq, Bool.or_false, evalOp]
          rw [ih a ha.2 ha.1, ih b hb.2 hb.1]
        · simp only [List.map_cons, List.map_nil, halt, hblt, ↓reduceIte, GateOp.eval,
            List.all_cons, List.all_nil, id_eq, Bool.and_true, evalOp]
          rw [ih a ha.2 ha.1, ih b hb.2 hb.1]
  refine ⟨G, hfan, hinv_eq, by omega, fun y => ?_⟩
  exact heval_G y D.out D.hout

private def gateToNodeOp {k : ℕ} (pos : ℕ) (g : Gate) : NodeOp k :=
  match g.op with
  | GateOp.not =>
    match g.inputs with
    | a :: _ => if a < pos then NodeOp.neg a else NodeOp.const true
    | [] => NodeOp.const true
  | GateOp.and =>
    match g.inputs with
    | [] => NodeOp.const true
    | [a] => if a < pos then NodeOp.copy a else NodeOp.const false
    | [a, b] => if a < pos ∧ b < pos then NodeOp.bin true a b else NodeOp.const false
    | _ => NodeOp.const false
  | GateOp.or =>
    match g.inputs with
    | [] => NodeOp.const false
    | [a] => if a < pos then NodeOp.copy a else NodeOp.const false
    | [a, b] =>
      if a < pos ∧ b < pos then NodeOp.bin false a b
      else if a < pos then NodeOp.copy a
      else if b < pos then NodeOp.copy b
      else NodeOp.const false
    | _ => NodeOp.const false
  | _ => NodeOp.const false

private theorem gateToNodeOp_ne_inp {k : ℕ} (pos : ℕ) (g : Gate) (j : Fin k) :
    gateToNodeOp (k := k) pos g ≠ NodeOp.inp j := by
  rcases g with ⟨gop, gins⟩
  cases gop with
  | not =>
    cases gins with
    | nil => simp [gateToNodeOp]
    | cons a _ => dsimp only [gateToNodeOp]; split_ifs <;> simp
  | and =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp]
    · simp
    · split_ifs <;> simp
    · split_ifs <;> simp
    · simp
  | or =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp]
    · simp
    · split_ifs <;> simp
    · split_ifs <;> simp
    · simp
  | mod _ => simp [gateToNodeOp]
  | maj => simp [gateToNodeOp]

private theorem gateToNodeOp_isNeg {k : ℕ} (pos : ℕ) (g : Gate)
    (h : isNegOp (gateToNodeOp (k := k) pos g) = true) : g.op = GateOp.not := by
  rcases g with ⟨gop, gins⟩
  cases gop with
  | not => rfl
  | and =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp] at h
    · simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · simp [isNegOp] at h
  | or =>
    rcases gins with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> dsimp only [gateToNodeOp] at h
    · simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · split_ifs at h <;> simp [isNegOp] at h
    · simp [isNegOp] at h
  | mod _ => simp [gateToNodeOp, isNegOp] at h
  | maj => simp [gateToNodeOp, isNegOp] at h

private theorem gateToNodeOp_isBin {k : ℕ} (pos : ℕ) (g : Gate)
    (h : isBinOp (gateToNodeOp (k := k) pos g) = true) : g.op ≠ GateOp.not := by
  rcases g with ⟨gop, gins⟩
  intro heq
  subst heq
  cases gins with
  | nil => simp [gateToNodeOp, isBinOp] at h
  | cons a _ => dsimp only [gateToNodeOp] at h; split_ifs at h <;> simp [isBinOp] at h

private theorem gateToNodeOp_children {k : ℕ} (pos : ℕ) (g : Gate) :
    ∀ a ∈ nodeChildren (gateToNodeOp (k := k) pos g), a < pos := by
  rcases g with ⟨gop, gins⟩
  intro a ha
  cases gop with
  | not =>
    cases gins with
    | nil => simp [gateToNodeOp, nodeChildren] at ha
    | cons x xs =>
      dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
  | and =>
    rcases gins with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · simp [gateToNodeOp, nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · simp only [nodeChildren, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> [exact h.1; exact h.2]
      · simp [nodeChildren] at ha
    · simp [gateToNodeOp, nodeChildren] at ha
  | or =>
    rcases gins with _ | ⟨x, _ | ⟨y, _ | _⟩⟩
    · simp [gateToNodeOp, nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
    · dsimp only [gateToNodeOp] at ha
      split_ifs at ha with h1 h2 h3
      · simp only [nodeChildren, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> [exact h1.1; exact h1.2]
      · have hax : a = x := by simpa [nodeChildren] using ha
        omega
      · have hay : a = y := by simpa [nodeChildren] using ha
        omega
      · simp [nodeChildren] at ha
    · simp [gateToNodeOp, nodeChildren] at ha
  | mod _ => simp [gateToNodeOp, nodeChildren] at ha
  | maj => simp [gateToNodeOp, nodeChildren] at ha

private theorem gateToNodeOp_eval {k : ℕ} (pos : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (val : ℕ → Bool) (y : Fin k → Bool) :
    evalOp val y (gateToNodeOp (k := k) pos g) =
    g.op.eval (g.inputs.map (fun j => if j < pos then val j else false)) := by
  rcases g with ⟨gop, gins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · dsimp only [gateToNodeOp]
    rcases gins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp [GateOp.eval, evalOp]
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      split_ifs <;> rfl
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      by_cases ha : a < pos <;> by_cases hb : b < pos <;> simp [ha, hb, evalOp]
    · simp at hlen
  · dsimp only [gateToNodeOp]
    rcases gins with _ | ⟨a, _ | ⟨b, _ | ⟨c, cs⟩⟩⟩
    · simp [GateOp.eval, evalOp]
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      split_ifs <;> rfl
    · simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      by_cases ha : a < pos <;> by_cases hb : b < pos <;> simp [ha, hb, evalOp]
    · simp at hlen
  · dsimp only [gateToNodeOp]
    rcases gins with _ | ⟨a, _⟩
    · simp [GateOp.eval, evalOp]
    · simp only [List.map_cons, GateOp.eval, List.headD_cons]
      split_ifs <;> rfl

private theorem solve_lib_586 (n k : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (wire : Fin k → Fin n) (fixed : Fin n → Bool) (hwinj : Function.Injective wire)
    (hnc : ∃ x y : Fin k → Bool,
      let plug := fun (z : Fin k → Bool) (i : Fin n) =>
        if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ z j = true) else fixed i
      C.eval (List.ofFn (plug x)) ≠ C.eval (List.ofFn (plug y))) :
    let inv := fun (G : Circuit) =>
      (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length
    let binary := fun (G : Circuit) => G.size - inv G
    let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
    let e := ((Finset.univ : Finset (Fin n)).filter (fun i =>
      ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))).card
    let plug := fun (y : Fin k → Bool) (i : Fin n) =>
      if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
    ∃ D : Circuit, FanInTwo D ∧ binary D + e ≤ binary C + k ∧ inv D ≤ inv C ∧
      ∀ y : Fin k → Bool, D.eval (List.ofFn y) = f (plug y) := by
  classical
  dsimp only
  let inv := fun (G : Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : Circuit) => G.size - inv G
  let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
  let Ess := (Finset.univ : Finset (Fin n)).filter (fun i =>
    ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))
  let plug := fun (y : Fin k → Bool) (i : Fin n) =>
    if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    rcases hnc with ⟨x, y, hne⟩
    have hx : C.eval (List.ofFn (plug x)) = false := by
      dsimp only [Circuit.eval]
      have hlen : (C.wires (List.ofFn (plug x))).length = n + C.gates.length := by
        rw [circuit_wires_length, List.length_ofFn]
      have hnone : (C.wires (List.ofFn (plug x)))[C.output]? = none :=
        List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone]
    have hy : C.eval (List.ofFn (plug y)) = false := by
      dsimp only [Circuit.eval]
      have hlen : (C.wires (List.ofFn (plug y))).length = n + C.gates.length := by
        rw [circuit_wires_length, List.length_ofFn]
      have hnone : (C.wires (List.ofFn (plug y)))[C.output]? = none :=
        List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone]
    exact hne (by rw [hx, hy])
  let opRaw : ℕ → NodeOp n := fun v =>
    if hv : v < n then NodeOp.inp ⟨v, hv⟩
    else if hvt : v - n < C.gates.length then gateToNodeOp v (C.gates[v - n]'hvt)
    else NodeOp.const false
  have hch_raw : ∀ v ∈ Finset.range (n + C.gates.length), ∀ a ∈ nodeChildren (opRaw v),
      a ∈ Finset.range (n + C.gates.length) ∧ a < v := by
    intro v hv a ha
    have hvlt := Finset.mem_range.mp hv
    dsimp only [opRaw] at ha
    split_ifs at ha with h1 h2
    · simp [nodeChildren] at ha
    · have halt := gateToNodeOp_children v (C.gates[v - n]'h2) a ha
      exact ⟨Finset.mem_range.mpr (by omega), halt⟩
    · simp [nodeChildren] at ha
  have hinj_raw : ∀ v1 ∈ Finset.range (n + C.gates.length),
      ∀ v2 ∈ Finset.range (n + C.gates.length), ∀ j : Fin n,
      opRaw v1 = NodeOp.inp j → opRaw v2 = NodeOp.inp j → v1 = v2 := by
    intro v1 _ v2 _ j h1 h2
    have hlt_of : ∀ v, opRaw v = NodeOp.inp j → v = j.val := by
      intro v hv
      dsimp only [opRaw] at hv
      by_cases hvn : v < n
      · simp only [hvn, ↓reduceDIte] at hv
        exact congrArg Fin.val (NodeOp.inp.inj hv)
      · simp only [hvn, ↓reduceDIte] at hv
        by_cases hvt : v - n < C.gates.length
        · simp only [hvt, ↓reduceDIte] at hv
          exact absurd hv (gateToNodeOp_ne_inp v _ j)
        · simp only [hvt, ↓reduceDIte] at hv
          cases hv
    exact (hlt_of v1 h1).trans (hlt_of v2 h2).symm
  let Draw : ValidDag n := ⟨Finset.range (n + C.gates.length), opRaw, C.output,
    Finset.mem_range.mpr hout_lt, hch_raw, hinj_raw⟩
  have heval_raw : ∀ x : Fin n → Bool, ∀ v ∈ Draw.V,
      evalDag Draw x v = (C.wires (List.ofFn x)).getD v false := by
    intro x v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hvV
      have hvlt := Finset.mem_range.mp hvV
      rw [evalDag_unfold Draw x hvV]
      change evalOp (evalDag Draw x) x (opRaw v) = _
      dsimp only [opRaw]
      split_ifs with h1 h2
      · rw [circuit_wires_getD_input C (List.ofFn x) v (by simp [h1])]
        simp [List.getD_eq_getElem?_getD, h1, evalOp]
      · have hveq : v = (List.ofFn x).length + (v - n) := by simp; omega
        have hg_mem : C.gates[v - n]'h2 ∈ C.gates := List.getElem_mem h2
        have hfg := hfan _ hg_mem
        have hget := circuit_wires_getD_gate C (List.ofFn x) (v - n) h2
        rw [← hveq] at hget
        rw [hget]
        have hcongr : evalOp (evalDag Draw x) x (gateToNodeOp (k := n) v (C.gates[v - n]'h2)) =
            evalOp (fun a => (C.wires (List.ofFn x)).getD a false) x
              (gateToNodeOp (k := n) v (C.gates[v - n]'h2)) := by
          refine evalOp_congr (fun a ha => ?_)
          have halt := gateToNodeOp_children (k := n) v (C.gates[v - n]'h2) a ha
          exact ih a halt (Finset.mem_range.mpr (by omega))
        rw [hcongr]
        exact gateToNodeOp_eval (k := n) v (C.gates[v - n]'h2) hfg.1 hfg.2
          (fun a => (C.wires (List.ofFn x)).getD a false) x
      · omega
  let Dtrim := trimDag Draw
  have hess_in : ∀ i ∈ Ess, i.val ∈ Dtrim.V := by
    intro i hi
    by_contra hnot
    rcases (Finset.mem_filter.mp hi).2 with ⟨x, hne⟩
    have hsame : ∀ v ∈ Dtrim.V,
        evalDag Dtrim (Function.update x i false) v = evalDag Dtrim (Function.update x i true) v := by
      intro v
      induction v using Nat.strong_induction_on with
      | ind v ih =>
        intro hv
        rw [evalDag_unfold Dtrim _ hv, evalDag_unfold Dtrim _ hv]
        cases hopv : Dtrim.op v with
        | inp j =>
          have hji : j ≠ i := by
            intro heq; subst heq
            have hvlt : v < n + C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hv).1
            have h1 := Draw.hinp_inj v (Finset.mem_range.mpr hvlt) j.val
              (Finset.mem_range.mpr (by omega)) j hopv (by simp [Draw, opRaw, j.isLt])
            rw [h1] at hv; exact hnot hv
          simp [evalOp, Function.update_of_ne hji]
        | const b => rfl
        | copy a =>
          have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
          exact ih a ha.2 ha.1
        | neg a =>
          have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
          simp only [evalOp, ih a ha.2 ha.1]
        | bin isAnd a b =>
          have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
          have hb := Dtrim.hchild v hv b (by simp [hopv, nodeChildren])
          cases isAnd <;> simp only [evalOp, ih a ha.2 ha.1, ih b hb.2 hb.1]
    have h0 := hsame Dtrim.out Dtrim.hout
    change evalDag Draw (Function.update x i false) C.output =
      evalDag Draw (Function.update x i true) C.output at h0
    rw [heval_raw _ C.output Draw.hout, heval_raw _ C.output Draw.hout] at h0
    exact hne h0
  let opPlug : ℕ → NodeOp k := fun v =>
    match Dtrim.op v with
    | NodeOp.inp i =>
      if h : ∃ j : Fin k, wire j = i then NodeOp.inp (Classical.choose h)
      else NodeOp.const (fixed i)
    | NodeOp.const b => NodeOp.const b
    | NodeOp.copy a => NodeOp.copy a
    | NodeOp.neg a => NodeOp.neg a
    | NodeOp.bin isAnd a b => NodeOp.bin isAnd a b
  have hch_eq : ∀ v, nodeChildren (opPlug v) = nodeChildren (Dtrim.op v) := by
    intro v
    dsimp only [opPlug]
    cases Dtrim.op v with
    | inp i => dsimp only; split_ifs <;> rfl
    | const _ => rfl
    | copy _ => rfl
    | neg _ => rfl
    | bin _ _ _ => rfl
  have hinj_plug : ∀ v1 ∈ Dtrim.V, ∀ v2 ∈ Dtrim.V, ∀ j : Fin k,
      opPlug v1 = NodeOp.inp j → opPlug v2 = NodeOp.inp j → v1 = v2 := by
    intro v1 hv1 v2 hv2 j h1 h2
    have hof : ∀ v, opPlug v = NodeOp.inp j → Dtrim.op v = NodeOp.inp (wire j) := by
      intro v hv
      dsimp only [opPlug] at hv
      cases hopv : Dtrim.op v with
      | inp i =>
        rw [hopv] at hv; dsimp only at hv
        by_cases hex : ∃ j0 : Fin k, wire j0 = i
        · simp only [hex, ↓reduceDIte] at hv
          have ej : Classical.choose hex = j := NodeOp.inp.inj hv
          have hi : wire j = i := by rw [← ej]; exact Classical.choose_spec hex
          rw [hi]
        · simp only [hex, ↓reduceDIte] at hv; cases hv
      | const _ => rw [hopv] at hv; cases hv
      | copy _ => rw [hopv] at hv; cases hv
      | neg _ => rw [hopv] at hv; cases hv
      | bin _ _ _ => rw [hopv] at hv; cases hv
    exact Dtrim.hinp_inj v1 hv1 v2 hv2 (wire j) (hof v1 h1) (hof v2 h2)
  let Dplug : ValidDag k := ⟨Dtrim.V, opPlug, Dtrim.out, Dtrim.hout,
    fun v hv a ha => Dtrim.hchild v hv a (by rwa [← hch_eq v]), hinj_plug⟩
  have heval_plug : ∀ y : Fin k → Bool, ∀ v ∈ Dtrim.V,
      evalDag Dplug y v = evalDag Dtrim (plug y) v := by
    intro y v
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro hv
      rw [evalDag_unfold Dplug y hv, evalDag_unfold Dtrim (plug y) hv]
      change evalOp (evalDag Dplug y) y (opPlug v) = evalOp (evalDag Dtrim (plug y)) (plug y) (Dtrim.op v)
      dsimp only [opPlug]
      cases hopv : Dtrim.op v with
      | inp i =>
        dsimp only [evalOp, plug]
        by_cases h1 : ∃ j : Fin k, wire j = i
        · have h2 : i ∈ Finset.univ.image wire := by
            rcases h1 with ⟨j, hj⟩; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
          simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
          have hj := Classical.choose_spec h1
          have hiff : (∃ j, wire j = i ∧ y j = true) ↔ y (Classical.choose h1) = true := by
            constructor
            · rintro ⟨j, hji, hyj⟩
              have : j = Classical.choose h1 := hwinj (hji.trans hj.symm)
              rwa [← this]
            · intro hy; exact ⟨Classical.choose h1, hj, hy⟩
          simp [hiff]
        · have h2 : i ∉ Finset.univ.image wire := by
            intro hm; rcases Finset.mem_image.mp hm with ⟨j, _, hj⟩; exact h1 ⟨j, hj⟩
          simp only [h1, h2, ↓reduceDIte, ↓reduceIte]
      | const b => rfl
      | copy a =>
        have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
        exact ih a ha.2 ha.1
      | neg a =>
        have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
        simp only [evalOp, ih a ha.2 ha.1]
      | bin isAnd a b =>
        have ha := Dtrim.hchild v hv a (by simp [hopv, nodeChildren])
        have hb := Dtrim.hchild v hv b (by simp [hopv, nodeChildren])
        cases isAnd <;> simp only [evalOp, ih a ha.2 ha.1, ih b hb.2 hb.1]
  have heval_plug_out : ∀ y : Fin k → Bool, evalDag Dplug y Dplug.out = f (plug y) := by
    intro y
    rw [heval_plug y Dtrim.out Dtrim.hout]
    change evalDag Draw (plug y) C.output = C.eval (List.ofFn (plug y))
    exact heval_raw (plug y) C.output Draw.hout
  have hnc_plug : ∃ y1 y2, evalDag Dplug y1 Dplug.out ≠ evalDag Dplug y2 Dplug.out := by
    rcases hnc with ⟨y1, y2, hne⟩
    exact ⟨y1, y2, by rw [heval_plug_out y1, heval_plug_out y2]; exact hne⟩
  have hedges_eq : dagEdges Dplug.V Dplug.op = dagEdges Dtrim.V Dtrim.op := by
    dsimp only [dagEdges, Dplug]
    apply List.flatMap_congr
    intro v _
    rw [hch_eq v]
  have hcc_plug : cc Dplug.V (dagEdges Dplug.V Dplug.op) = 1 := by
    rw [hedges_eq]; exact trimDag_connected Draw
  have hneg_plug_le : negCount Dplug.V Dplug.op ≤ inv C := by
    have h1 : negCount Dplug.V Dplug.op ≤ negCount Draw.V Draw.op := by
      refine Finset.card_le_card ?_
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvT, hneg⟩
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hvT).1, ?_⟩
      dsimp only [Dplug, opPlug] at hneg
      cases hop : Dtrim.op v with
      | neg _ => change isNegOp (Dtrim.op v) = true; rw [hop]; rfl
      | inp _ => rw [hop] at hneg; dsimp only at hneg; split_ifs at hneg <;> simp [isNegOp] at hneg
      | const _ => simp [hop, isNegOp] at hneg
      | copy _ => simp [hop, isNegOp] at hneg
      | bin _ _ _ => simp [hop, isNegOp] at hneg
    refine h1.trans ?_
    dsimp only [inv]
    rw [inv_eq_match]
    let S := (Finset.range C.gates.length).filter (fun t =>
      match (C.gates.getD t ⟨GateOp.or, []⟩).op with | GateOp.not => true | _ => false)
    have hsub : (Draw.V.filter (fun v => isNegOp (Draw.op v))) ⊆ S.image (fun t => n + t) := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvR, hneg⟩
      have hvlt := Finset.mem_range.mp hvR
      dsimp only [Draw, opRaw] at hneg
      split_ifs at hneg with h1 h2
      · simp [isNegOp] at hneg
      · refine Finset.mem_image.mpr ⟨v - n, ?_, by omega⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, ?_⟩
        have hgetD : C.gates.getD (v - n) ⟨GateOp.or, []⟩ = C.gates[v - n]'h2 := by
          simp [List.getD_eq_getElem?_getD, h2]
        rw [hgetD, gateToNodeOp_isNeg v _ hneg]
      · simp [isNegOp] at hneg
    have hScard : S.card = (C.gates.filter (fun g => match g.op with | GateOp.not => true | _ => false)).length := by
      clear hsub h1
      let P : Gate → Bool := fun g => match g.op with | GateOp.not => true | _ => false
      have hgen : ∀ (L : List Gate),
          ((Finset.range L.length).filter (fun t => P (L.getD t ⟨GateOp.or, []⟩) = true)).card =
          (L.filter P).length := by
        intro L
        induction L with
        | nil => simp
        | cons g L ih =>
          simp only [List.length_cons, List.filter_cons]
          have hr : Finset.range (L.length + 1) = insert 0 ((Finset.range L.length).image Nat.succ) := by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
            cases x with
            | zero => simp
            | succ x => simp
          rw [hr, Finset.filter_insert]
          have hflt_img : ((Finset.range L.length).image Nat.succ).filter
              (fun t => P ((g :: L).getD t ⟨GateOp.or, []⟩) = true) =
              ((Finset.range L.length).filter
                (fun t => P (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨⟨t, ht, rfl⟩, hp⟩
              exact ⟨t, ⟨ht, by simpa [List.getD_eq_getElem?_getD] using hp⟩, rfl⟩
            · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
              exact ⟨⟨t, ht, rfl⟩, by simpa [List.getD_eq_getElem?_getD] using hp⟩
          have h0_eq : (g :: L).getD 0 ⟨GateOp.or, []⟩ = g := rfl
          rw [h0_eq, hflt_img]
          have h0nm : (0 : ℕ) ∉ ((Finset.range L.length).filter (fun t => P (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            simp
          cases hPg : P g
          · simp only [Bool.false_eq_true, ↓reduceIte, Finset.card_image_of_injective _ Nat.succ_injective, ih]
          · simp only [↓reduceIte, Finset.card_insert_of_notMem h0nm,
              Finset.card_image_of_injective _ Nat.succ_injective, List.length_cons, ih]
      convert hgen C.gates using 2
      ext t; simp [S, P]; intro _; cases (C.gates[t]?.getD ⟨GateOp.or, []⟩).op <;> simp
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq hScard))
  have hbin_plug_le : binCount Dplug.V Dplug.op ≤ binary C := by
    have h1 : binCount Dplug.V Dplug.op ≤ binCount Draw.V Draw.op := by
      refine Finset.card_le_card ?_
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvT, hbin⟩
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hvT).1, ?_⟩
      dsimp only [Dplug, opPlug] at hbin
      cases hop : Dtrim.op v with
      | bin _ _ _ => change isBinOp (Dtrim.op v) = true; rw [hop]; rfl
      | inp _ => rw [hop] at hbin; dsimp only at hbin; split_ifs at hbin <;> simp [isBinOp] at hbin
      | const _ => simp [hop, isBinOp] at hbin
      | copy _ => simp [hop, isBinOp] at hbin
      | neg _ => simp [hop, isBinOp] at hbin
    refine h1.trans ?_
    dsimp only [binary, inv, Circuit.size]
    rw [inv_eq_match]
    let S := (Finset.range C.gates.length).filter (fun t =>
      match (C.gates.getD t ⟨GateOp.or, []⟩).op with | GateOp.not => false | _ => true)
    have hsub : (Draw.V.filter (fun v => isBinOp (Draw.op v))) ⊆ S.image (fun t => n + t) := by
      intro v hv
      rcases Finset.mem_filter.mp hv with ⟨hvR, hbin⟩
      have hvlt := Finset.mem_range.mp hvR
      dsimp only [Draw, opRaw] at hbin
      split_ifs at hbin with h1 h2
      · simp [isBinOp] at hbin
      · refine Finset.mem_image.mpr ⟨v - n, ?_, by omega⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2, ?_⟩
        have hgetD : C.gates.getD (v - n) ⟨GateOp.or, []⟩ = C.gates[v - n]'h2 := by
          simp [List.getD_eq_getElem?_getD, h2]
        rw [hgetD]
        have hne_not := gateToNodeOp_isBin v _ hbin
        cases hop : (C.gates[v - n]'h2).op with
        | not => exact absurd hop hne_not
        | and => rfl
        | or => rfl
        | mod _ => rfl
        | maj => rfl
      · simp [isBinOp] at hbin
    have hScard : S.card = C.gates.length -
        (C.gates.filter (fun g => match g.op with | GateOp.not => true | _ => false)).length := by
      clear hsub h1
      let P : Gate → Bool := fun g => match g.op with | GateOp.not => true | _ => false
      let Q : Gate → Bool := fun g => match g.op with | GateOp.not => false | _ => true
      have hPQ : ∀ g, Q g = !(P g) := fun ⟨gop, _⟩ => by cases gop <;> rfl
      have hgen : ∀ (L : List Gate),
          ((Finset.range L.length).filter (fun t => Q (L.getD t ⟨GateOp.or, []⟩) = true)).card +
          (L.filter P).length = L.length := by
        intro L
        induction L with
        | nil => simp
        | cons g L ih =>
          simp only [List.length_cons, List.filter_cons]
          have hr : Finset.range (L.length + 1) = insert 0 ((Finset.range L.length).image Nat.succ) := by
            ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_image]
            cases x with
            | zero => simp
            | succ x => simp
          rw [hr, Finset.filter_insert]
          have hflt_img : ((Finset.range L.length).image Nat.succ).filter
              (fun t => Q ((g :: L).getD t ⟨GateOp.or, []⟩) = true) =
              ((Finset.range L.length).filter
                (fun t => Q (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_image]
            constructor
            · rintro ⟨⟨t, ht, rfl⟩, hp⟩
              exact ⟨t, ⟨ht, by simpa [List.getD_eq_getElem?_getD] using hp⟩, rfl⟩
            · rintro ⟨t, ⟨ht, hp⟩, rfl⟩
              exact ⟨⟨t, ht, rfl⟩, by simpa [List.getD_eq_getElem?_getD] using hp⟩
          have h0_eq : (g :: L).getD 0 ⟨GateOp.or, []⟩ = g := rfl
          rw [h0_eq, hflt_img, hPQ g]
          have h0nm : (0 : ℕ) ∉ ((Finset.range L.length).filter (fun t => Q (L.getD t ⟨GateOp.or, []⟩) = true)).image Nat.succ := by
            simp
          cases hPg : P g
          · simp only [Bool.false_eq_true, Bool.not_false, ↓reduceIte, Finset.card_insert_of_notMem h0nm,
              Finset.card_image_of_injective _ Nat.succ_injective]
            omega
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Finset.card_image_of_injective _ Nat.succ_injective, List.length_cons]
            omega
      have hsum : S.card +
          (C.gates.filter P).length = C.gates.length := by
        convert hgen C.gates using 3
        ext t; simp [S, Q]; intro _; cases (C.gates[t]?.getD ⟨GateOp.or, []⟩).op <;> simp
      exact Nat.eq_sub_of_add_eq hsum
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (le_of_eq hScard))
  have hess_le_ic : Ess.card ≤ inpCount Dplug.V Dplug.op + constCount Dplug.V Dplug.op := by
    let U := Dplug.V.filter (fun v => isInpOp (Dplug.op v) ∨ isConstOp (Dplug.op v))
    have hUcard : U.card = inpCount Dplug.V Dplug.op + constCount Dplug.V Dplug.op := by
      have hsplit : U = Dplug.V.filter (fun v => isInpOp (Dplug.op v)) ∪
          Dplug.V.filter (fun v => isConstOp (Dplug.op v)) := by
        ext v; simp only [U, Finset.mem_filter, Finset.mem_union]; tauto
      have hdisj : Disjoint (Dplug.V.filter (fun v => isInpOp (Dplug.op v)))
          (Dplug.V.filter (fun v => isConstOp (Dplug.op v))) := by
        rw [Finset.disjoint_left]
        intro v h1 h2
        have h1' := (Finset.mem_filter.mp h1).2
        have h2' := (Finset.mem_filter.mp h2).2
        cases hop : Dplug.op v <;> simp [hop, isInpOp, isConstOp] at h1' h2'
      rw [hsplit, Finset.card_union_of_disjoint hdisj]; rfl
    rw [← hUcard]
    have hsub : Ess.image Fin.val ⊆ U := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      have hiV : i.val ∈ Dplug.V := hess_in i hi
      refine Finset.mem_filter.mpr ⟨hiV, ?_⟩
      dsimp only [Dplug, opPlug]
      have hopi : Dtrim.op i.val = NodeOp.inp i := by
        simp [Dtrim, trimDag, Draw, opRaw, i.isLt]
      rw [hopi]
      dsimp only
      split_ifs <;> simp [isInpOp, isConstOp]
    have hcard_img : (Ess.image Fin.val).card = Ess.card :=
      Finset.card_image_of_injective _ Fin.val_injective
    rw [← hcard_img]
    exact Finset.card_le_card hsub
  have hbeta_plug : beta1 Dplug.V (dagEdges Dplug.V Dplug.op) + Ess.card ≤ binary C + 1 := by
    have h1 := beta1_add_card (dagEdges_allIn Dplug)
    have h2 := dag_edge_vertex_identity Dplug.V Dplug.op
    rw [hcc_plug] at h1
    omega
  rcases reduce_to_normal_form Dplug hnc_plug with ⟨Dnf, hnf, hbeta_nf, hneg_nf, heval_nf⟩
  have hcc_nf : cc Dnf.V (dagEdges Dnf.V Dnf.op) = 1 := by
    have hteq : (trimDag Dnf).V = Dnf.V := by
      ext x; simp only [trimDag, Finset.mem_filter, and_iff_left_iff_imp]; exact hnf.1 x
    have h1 := trimDag_connected Dnf
    change cc (trimDag Dnf).V (dagEdges (trimDag Dnf).V Dnf.op) = 1 at h1
    rwa [hteq] at h1
  have hconst_nf : constCount Dnf.V Dnf.op = 0 := by
    dsimp only [constCount]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv
    exact (hnf.2 v hv).1
  have hinp_nf_le : inpCount Dnf.V Dnf.op ≤ k := by
    let S := Dnf.V.filter (fun v => isInpOp (Dnf.op v))
    let toFin : ℕ → Fin k := fun v =>
      match Dnf.op v with
      | NodeOp.inp j => j
      | _ => ⟨0, by
          by_contra hk0
          have hk_eq : k = 0 := by omega
          subst hk_eq
          rcases hnc_plug with ⟨y1, y2, hne⟩
          have : y1 = y2 := funext (fun i => Fin.elim0 i)
          exact hne (by rw [this])⟩
    have hinj : Set.InjOn toFin (S : Set ℕ) := by
      intro v1 hv1 v2 hv2 heq
      have h1 := Finset.mem_filter.mp hv1
      have h2 := Finset.mem_filter.mp hv2
      cases hop1 : Dnf.op v1 with
      | inp j1 =>
        cases hop2 : Dnf.op v2 with
        | inp j2 =>
          have hj : j1 = j2 := by simpa [toFin, hop1, hop2] using heq
          subst hj
          exact Dnf.hinp_inj v1 h1.1 v2 h2.1 j1 hop1 hop2
        | const _ => simp [hop2, isInpOp] at h2
        | copy _ => simp [hop2, isInpOp] at h2
        | neg _ => simp [hop2, isInpOp] at h2
        | bin _ _ _ => simp [hop2, isInpOp] at h2
      | const _ => simp [hop1, isInpOp] at h1
      | copy _ => simp [hop1, isInpOp] at h1
      | neg _ => simp [hop1, isInpOp] at h1
      | bin _ _ _ => simp [hop1, isInpOp] at h1
    have hcard : S.card = (S.image toFin).card := (Finset.card_image_of_injOn hinj).symm
    calc inpCount Dnf.V Dnf.op = (S.image toFin).card := hcard
      _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_univ _
      _ = k := by simp
  have hbin_nf_eq : binCount Dnf.V Dnf.op + 1 = beta1 Dnf.V (dagEdges Dnf.V Dnf.op) + inpCount Dnf.V Dnf.op := by
    have h1 := beta1_add_card (dagEdges_allIn Dnf)
    have h2 := dag_edge_vertex_identity Dnf.V Dnf.op
    rw [hcc_nf] at h1
    rw [hconst_nf] at h2
    omega
  rcases normal_form_to_circuit Dnf hnf with ⟨G, hGfan, hGinv, hGbin, hGeval⟩
  refine ⟨G, hGfan, ?_, ?_, ?_⟩
  · change G.size - inv G + Ess.card ≤ binary C + k
    dsimp only [inv]
    rw [hGbin]
    omega
  · change inv G ≤ inv C
    dsimp only [inv]
    rw [hGinv]
    exact hneg_nf.trans hneg_plug_le
  · intro y
    rw [hGeval y, heval_nf y, heval_plug_out y]

end PEqualNP.Outside.L_lib_586_aux

theorem PEqualNP.Outside.L_lib_586 : (∀ (n k : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.MetaComplexity.FanInTwo C →
  let inv := fun (G : PEqualNP.CircuitLowerBounds.Circuit) =>
    (G.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not) (Classical.propDecidable _))).length
  let binary := fun (G : PEqualNP.CircuitLowerBounds.Circuit) => G.size - inv G
  let f := fun (x : Fin n → Bool) => C.eval (List.ofFn x)
  let e := ((Finset.univ : Finset (Fin n)).filter (fun i =>
    ∃ x : Fin n → Bool, f (Function.update x i false) ≠ f (Function.update x i true))).card
  ∀ (wire : Fin k → Fin n) (fixed : Fin n → Bool), Function.Injective wire →
    let plug := fun (y : Fin k → Bool) (i : Fin n) =>
      if i ∈ Finset.univ.image wire then decide (∃ j, wire j = i ∧ y j = true) else fixed i
    (∃ x y : Fin k → Bool, f (plug x) ≠ f (plug y)) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧
      binary D + e ≤ binary C + k ∧ inv D ≤ inv C ∧
      ∀ y : Fin k → Bool, D.eval (List.ofFn y) = f (plug y)) := by
  intro n k C hfan inv binary f e wire fixed hwinj plug hnc
  exact PEqualNP.Outside.L_lib_586_aux.solve_lib_586 n k C hfan wire fixed hwinj hnc
