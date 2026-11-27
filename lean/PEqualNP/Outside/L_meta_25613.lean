import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25613_aux

def nbrR {n m : ℕ} (H : Fin n → Fin m → Bool) (a : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun c => H a c = true)

def nbrC {n m : ℕ} (H : Fin n → Fin m → Bool) (c : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun a => H a c = true)

def profR {n m : ℕ} (H : Fin n → Fin m → Bool) (B : Finset (Fin m)) (a : Fin n) : Finset (Fin m) :=
  (Finset.univ \ B).filter (fun c => H a c = true)

def profC {n m : ℕ} (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (c : Fin m) : Finset (Fin n) :=
  (Finset.univ \ R).filter (fun a => H a c = true)

def coreR {n m : ℕ} (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)) : Finset (Fin n) :=
  R.filter (fun a => ∃ c ∈ B, H a c = true)

def coreC {n m : ℕ} (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)) : Finset (Fin m) :=
  B.filter (fun c => ∃ a ∈ R, H a c = true)

structure AdmissibleTrue (d t n m : ℕ) (H : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) : Prop where
  degR : ∀ a, 2 ≤ (nbrR H a).card ∧ (nbrR H a).card ≤ d
  degC : ∀ c, 2 ≤ (nbrC H c).card ∧ (nbrC H c).card ≤ d
  c4R : ∀ a b, a ≠ b → (nbrR H a ∩ nbrR H b).card ≤ 1
  typesR : (R.image (profR H B)).card ≤ t
  typesC : (B.image (profC H R)).card ≤ t
  closure : ∀ a ∈ coreR H R B, ∀ b ∈ coreR H R B,
    ∀ x ∈ coreC H R B, ∀ y ∈ coreC H R B,
      H a x = false → H b x = false → H b y = false → H a y = false

lemma c4C_of_c4R {n m : ℕ} {H : Fin n → Fin m → Bool}
    (hc4 : ∀ a b, a ≠ b → (nbrR H a ∩ nbrR H b).card ≤ 1) :
    ∀ x y, x ≠ y → (nbrC H x ∩ nbrC H y).card ≤ 1 := by
  intro x y hxy
  by_contra hgt
  have h1 : 1 < (nbrC H x ∩ nbrC H y).card := by omega
  rcases Finset.one_lt_card.mp h1 with ⟨a, ha, b, hb, hab⟩
  simp only [Finset.mem_inter, nbrC, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have hsub : ({x, y} : Finset (Fin m)) ⊆ nbrR H a ∩ nbrR H b := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_inter, nbrR, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl
    · exact ⟨ha.1, hb.1⟩
    · exact ⟨ha.2, hb.2⟩
  have h2 : 2 ≤ (nbrR H a ∩ nbrR H b).card := by
    calc 2 = ({x, y} : Finset (Fin m)).card := (Finset.card_pair hxy).symm
      _ ≤ (nbrR H a ∩ nbrR H b).card := Finset.card_le_card hsub
  have hle := hc4 a b hab
  omega

lemma AdmissibleTrue.transpose {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B) :
    AdmissibleTrue d t m n (fun c a => H a c) B R where
  degR := h.degC
  degC := h.degR
  c4R := c4C_of_c4R h.c4R
  typesR := h.typesC
  typesC := h.typesR
  closure := by
    intro x hx y hy a ha b hb hax hbx hby
    exact h.closure b hb a ha y hy x hx hby hbx hax

lemma profR_subset_nbrR {n m : ℕ} (H : Fin n → Fin m → Bool) (B : Finset (Fin m)) (a : Fin n) :
    profR H B a ⊆ nbrR H a := by
  intro c hc
  simp only [profR, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hc ⊢
  exact hc.2

lemma profC_subset_nbrC {n m : ℕ} (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (c : Fin m) :
    profC H R c ⊆ nbrC H c := by
  intro a ha
  simp only [profC, nbrC, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at ha ⊢
  exact ha.2

lemma nbrR_card_split {n m : ℕ} (H : Fin n → Fin m → Bool) (B : Finset (Fin m)) (a : Fin n) :
    (nbrR H a ∩ B).card + (profR H B a).card = (nbrR H a).card := by
  have hdisj : Disjoint (nbrR H a ∩ B) (profR H B a) := by
    rw [Finset.disjoint_left]
    intro c h1 h2
    simp only [Finset.mem_inter, profR, Finset.mem_filter, Finset.mem_sdiff] at h1 h2
    exact h2.1.2 h1.2
  have hunion : (nbrR H a ∩ B) ∪ profR H B a = nbrR H a := by
    ext c
    simp only [Finset.mem_union, Finset.mem_inter, nbrR, profR, Finset.mem_filter,
               Finset.mem_sdiff, Finset.mem_univ, true_and]
    by_cases hc : c ∈ B <;> simp [hc]
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

lemma nbrC_card_split {n m : ℕ} (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (c : Fin m) :
    (nbrC H c ∩ R).card + (profC H R c).card = (nbrC H c).card :=
  nbrR_card_split (fun c a => H a c) R c

lemma card_eq_of_fin_bij {α : Type*} (k : ℕ) (S : Finset α) (f : Fin k → α)
    (hmem : ∀ j : Fin k, f j ∈ S)
    (hinj : ∀ j1 j2 : Fin k, f j1 = f j2 → j1 = j2)
    (hsurj : ∀ a ∈ S, ∃ j : Fin k, f j = a) : S.card = k := by
  rw [← Fintype.card_fin k, ← Finset.card_univ]
  symm
  apply Finset.card_bij (fun j _ => f j)
  · intro j _; exact hmem j
  · intro j1 _ j2 _ h; exact hinj j1 j2 h
  · intro a ha; rcases hsurj a ha with ⟨j, rfl⟩; exact ⟨j, Finset.mem_univ _, rfl⟩

lemma isolates_row_bound {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B) :
    let R1 := coreR H R B
    let R0 := R \ R1
    R0.card + (R1.image (profR H B)).card = (R.image (profR H B)).card ∧
    (R.image (profR H B)).card ≤ t := by
  intro R1 R0
  have hsub : R1 ⊆ R := Finset.filter_subset _ _
  have hunion_R : R0 ∪ R1 = R := Finset.sdiff_union_of_subset hsub
  have himg_union : R.image (profR H B) = R0.image (profR H B) ∪ R1.image (profR H B) := by
    rw [← hunion_R, Finset.image_union]
  have hprof_iso : ∀ a ∈ R0, profR H B a = nbrR H a := by
    intro a ha
    simp only [R0, R1, coreR, Finset.mem_sdiff, Finset.mem_filter] at ha
    have hno : ∀ c ∈ B, H a c ≠ true := by
      intro c hc htrue; exact ha.2 ⟨ha.1, c, hc, htrue⟩
    ext c
    simp only [profR, nbrR, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro h1; exact h1.2
    · intro h1; exact ⟨fun hcB => hno c hcB h1, h1⟩
  have hdisj_img : Disjoint (R0.image (profR H B)) (R1.image (profR H B)) := by
    rw [Finset.disjoint_left]
    intro P hP0 hP1
    rw [Finset.mem_image] at hP0 hP1
    rcases hP0 with ⟨a, ha0, rfl⟩
    rcases hP1 with ⟨b, hb1, hpeq⟩
    have hab : a ≠ b := by
      intro heq; subst heq
      simp only [R0, Finset.mem_sdiff] at ha0
      exact ha0.2 hb1
    have hsub_inter : nbrR H a ⊆ nbrR H a ∩ nbrR H b := by
      rw [Finset.subset_inter_iff]
      refine ⟨Finset.Subset.refl _, ?_⟩
      rw [← hprof_iso a ha0, ← hpeq]
      exact profR_subset_nbrR H B b
    have h2 := (h.degR a).1
    have h1 := h.c4R a b hab
    have hle := Finset.card_le_card hsub_inter
    omega
  have hinj0 : Set.InjOn (profR H B) (R0 : Set (Fin n)) := by
    intro a ha b hb hpeq
    by_contra hab
    have hsub_inter : nbrR H a ⊆ nbrR H a ∩ nbrR H b := by
      rw [Finset.subset_inter_iff]
      refine ⟨Finset.Subset.refl _, ?_⟩
      rw [← hprof_iso a ha, hpeq, hprof_iso b hb]
    have h2 := (h.degR a).1
    have h1 := h.c4R a b hab
    have hle := Finset.card_le_card hsub_inter
    omega
  rw [himg_union, Finset.card_union_of_disjoint hdisj_img, Finset.card_image_of_injOn hinj0]
  exact ⟨rfl, by rw [← Finset.card_image_of_injOn hinj0, ← Finset.card_union_of_disjoint hdisj_img, ← himg_union]; exact h.typesR⟩

lemma core_sum_reduction {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B) :
    let R1 := coreR H R B
    let B1 := coreC H R B
    let tR := (R1.image (profR H B)).card
    let tB := (B1.image (profC H R)).card
    R.card + B.card ≤ 2 * t + (R1.card - tR) + (B1.card - tB) ∧
    tR ≤ R1.card ∧ tB ≤ B1.card ∧ tR ≤ t ∧ tB ≤ t := by
  intro R1 B1 tR tB
  have hR := isolates_row_bound h
  have hB := isolates_row_bound h.transpose
  dsimp only at hR hB
  have hsubR : R1 ⊆ R := Finset.filter_subset _ _
  have hsubB : B1 ⊆ B := Finset.filter_subset _ _
  have hsplitR : (R \ R1).card + R1.card = R.card := Finset.card_sdiff_add_card_eq_card hsubR
  have hsplitB : (B \ B1).card + B1.card = B.card := Finset.card_sdiff_add_card_eq_card hsubB
  have hleR : tR ≤ R1.card := Finset.card_image_le
  have hleB : tB ≤ B1.card := Finset.card_image_le
  have hcore_tr : coreR (fun c a => H a c) B R = B1 := rfl
  have hprof_tr : profR (fun c a => H a c) R = profC H R := rfl
  rw [hcore_tr, hprof_tr] at hB
  change (R \ R1).card + tR = (R.image (profR H B)).card ∧ (R.image (profR H B)).card ≤ t at hR
  change (B \ B1).card + tB = (B.image (profC H R)).card ∧ (B.image (profC H R)).card ≤ t at hB
  exact ⟨by omega, hleR, hleB, by omega, by omega⟩

lemma core_nonempty_iff {n m : ℕ} (H : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (B : Finset (Fin m)) :
    (coreR H R B).Nonempty ↔ (coreC H R B).Nonempty := by
  constructor
  · rintro ⟨a, ha⟩
    simp only [coreR, Finset.mem_filter] at ha
    rcases ha.2 with ⟨c, hc, hac⟩
    exact ⟨c, Finset.mem_filter.mpr ⟨hc, a, ha.1, hac⟩⟩
  · rintro ⟨c, hc⟩
    simp only [coreC, Finset.mem_filter] at hc
    rcases hc.2 with ⟨a, ha, hac⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, c, hc.1, hac⟩⟩

lemma profC_inj_of_unique_row_nbr {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B)
    (S : Finset (Fin m)) (a0 : Fin n) (ha0 : a0 ∈ R)
    (huniq : ∀ x ∈ S, nbrC H x ∩ R = {a0}) :
    Set.InjOn (profC H R) (S : Set (Fin m)) := by
  intro x hx y hy hpeq
  by_contra hxy
  have hpx_pos : 1 ≤ (profC H R x).card := by
    have hsp := nbrC_card_split H R x
    rw [huniq x hx, Finset.card_singleton] at hsp
    have hd := (h.degC x).1
    omega
  rcases Finset.card_pos.mp (by omega : 0 < (profC H R x).card) with ⟨r1, hr1⟩
  have hr1_ne : r1 ≠ a0 := by
    intro heq; subst heq
    simp only [profC, Finset.mem_filter, Finset.mem_sdiff] at hr1
    exact hr1.1.2 ha0
  have hsub : ({a0, r1} : Finset (Fin n)) ⊆ nbrC H x ∩ nbrC H y := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [Finset.mem_inter]
    rcases hz with rfl | rfl
    · have hx0 : z ∈ nbrC H x ∩ R := by rw [huniq x hx]; simp
      have hy0 : z ∈ nbrC H y ∩ R := by rw [huniq y hy]; simp
      exact ⟨(Finset.mem_inter.mp hx0).1, (Finset.mem_inter.mp hy0).1⟩
    · refine ⟨profC_subset_nbrC H R x hr1, ?_⟩
      rw [hpeq] at hr1
      exact profC_subset_nbrC H R y hr1
  have h2 : 2 ≤ (nbrC H x ∩ nbrC H y).card := by
    calc 2 = ({a0, r1} : Finset (Fin n)).card := (Finset.card_pair hr1_ne.symm).symm
      _ ≤ (nbrC H x ∩ nbrC H y).card := Finset.card_le_card hsub
  have h1 := c4C_of_c4R h.c4R x y hxy
  omega

lemma case_coreR_eq_1 {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B)
    (h1 : (coreR H R B).card = 1) :
    ((coreR H R B).card - ((coreR H R B).image (profR H B)).card) +
    ((coreC H R B).card - ((coreC H R B).image (profC H R)).card) = 0 := by
  rcases Finset.card_eq_one.mp h1 with ⟨a0, ha0_eq⟩
  have ha0_R1 : a0 ∈ coreR H R B := by rw [ha0_eq]; simp
  have ha0_R : a0 ∈ R := (Finset.mem_filter.mp ha0_R1).1
  have htR : ((coreR H R B).image (profR H B)).card = 1 := by rw [ha0_eq]; simp
  have huniq : ∀ x ∈ coreC H R B, nbrC H x ∩ R = {a0} := by
    intro x hx
    ext a
    simp only [Finset.mem_inter, nbrC, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton]
    constructor
    · rintro ⟨hax, haR⟩
      have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
      have ha1 : a ∈ coreR H R B := Finset.mem_filter.mpr ⟨haR, x, hxB, hax⟩
      rw [ha0_eq, Finset.mem_singleton] at ha1
      exact ha1
    · rintro rfl
      rcases (Finset.mem_filter.mp hx).2 with ⟨a, haR, hax⟩
      have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
      have ha1 : a ∈ coreR H R B := Finset.mem_filter.mpr ⟨haR, x, hxB, hax⟩
      rw [ha0_eq, Finset.mem_singleton] at ha1
      subst ha1
      exact ⟨hax, ha0_R⟩
  have hinj := profC_inj_of_unique_row_nbr h (coreC H R B) a0 ha0_R huniq
  have htB : ((coreC H R B).image (profC H R)).card = (coreC H R B).card :=
    Finset.card_image_of_injOn hinj
  omega

lemma case_coreR_eq_2 {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B)
    (h2 : (coreR H R B).card = 2) :
    ((coreR H R B).card - ((coreR H R B).image (profR H B)).card) +
    ((coreC H R B).card - ((coreC H R B).image (profC H R)).card) ≤ min d t + 1 := by
  rcases Finset.card_eq_two.mp h2 with ⟨a1, a2, ha12, hR1_eq⟩
  have ha1_R : a1 ∈ R := (Finset.mem_filter.mp (by rw [hR1_eq]; simp : a1 ∈ coreR H R B)).1
  have ha2_R : a2 ∈ R := (Finset.mem_filter.mp (by rw [hR1_eq]; simp : a2 ∈ coreR H R B)).1
  have htR_pos : 1 ≤ ((coreR H R B).image (profR H B)).card := by
    rw [hR1_eq]; exact Finset.card_pos.mpr ⟨profR H B a1, by simp⟩
  let B1 := coreC H R B
  let Pset := B1.image (profC H R)
  let cls : Finset (Fin n) → Finset (Fin m) := fun P => B1.filter (fun x => profC H R x = P)
  have hpart : B1.card = ∑ P ∈ Pset, (cls P).card := by
    have h1 := Finset.card_eq_sum_card_fiberwise (f := profC H R) (s := B1) (t := Pset)
      (fun x hx => Finset.mem_image_of_mem _ hx)
    exact h1
  have hcls_pos : ∀ P ∈ Pset, 1 ≤ (cls P).card := by
    intro P hP
    rcases Finset.mem_image.mp hP with ⟨x, hx, rfl⟩
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hcls_props : ∀ P ∈ Pset, (cls P).card ≤ 2 ∧
      ((cls P).card = 2 → ∃ x ∈ cls P, x ∈ nbrR H a1) := by
    intro P hP
    by_cases hgt1 : 1 < (cls P).card
    · rcases Finset.one_lt_card.mp hgt1 with ⟨x, hx, y, hy, hxy⟩
      have hx_f := Finset.mem_filter.mp hx
      have hy_f := Finset.mem_filter.mp hy
      have hP_nonempty : P.Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty] at hemp
        have hnbr : ∀ z ∈ cls P, a1 ∈ nbrC H z ∧ a2 ∈ nbrC H z := by
          intro z hz
          have hzf := Finset.mem_filter.mp hz
          have hsp := nbrC_card_split H R z
          rw [hzf.2, hemp, Finset.card_empty, Nat.add_zero] at hsp
          have hsub_R1 : nbrC H z ∩ R ⊆ {a1, a2} := by
            intro a ha
            rw [Finset.mem_inter] at ha
            have hzB : z ∈ B := (Finset.mem_filter.mp hzf.1).1
            have ha1 : a ∈ coreR H R B :=
              Finset.mem_filter.mpr ⟨ha.2, z, hzB, (Finset.mem_filter.mp ha.1).2⟩
            rwa [hR1_eq] at ha1
          have hcard2 : 2 ≤ (nbrC H z ∩ R).card := by rw [hsp]; exact (h.degC z).1
          have heq2 : nbrC H z ∩ R = {a1, a2} :=
            Finset.eq_of_subset_of_card_le hsub_R1 (by rw [Finset.card_pair ha12]; exact hcard2)
          have h1m : a1 ∈ nbrC H z ∩ R := by rw [heq2]; simp
          have h2m : a2 ∈ nbrC H z ∩ R := by rw [heq2]; simp
          exact ⟨(Finset.mem_inter.mp h1m).1, (Finset.mem_inter.mp h2m).1⟩
        have hxy_sub : ({x, y} : Finset (Fin m)) ⊆ nbrR H a1 ∩ nbrR H a2 := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          simp only [Finset.mem_inter, nbrR, Finset.mem_filter, Finset.mem_univ, true_and]
          rcases hz with rfl | rfl
          · have h1 := hnbr z hx
            exact ⟨(Finset.mem_filter.mp h1.1).2, (Finset.mem_filter.mp h1.2).2⟩
          · have h2 := hnbr z hy
            exact ⟨(Finset.mem_filter.mp h2.1).2, (Finset.mem_filter.mp h2.2).2⟩
        have hle := h.c4R a1 a2 ha12
        have hge : 2 ≤ (nbrR H a1 ∩ nbrR H a2).card := by
          calc 2 = ({x, y} : Finset (Fin m)).card := (Finset.card_pair hxy).symm
            _ ≤ (nbrR H a1 ∩ nbrR H a2).card := Finset.card_le_card hxy_sub
        omega
      rcases hP_nonempty with ⟨r0, hr0⟩
      have hr0_notR : r0 ∉ R := by
        rw [← hx_f.2] at hr0
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hr0).1).2
      have hdisj_in : ∀ u ∈ cls P, ∀ v ∈ cls P, u ≠ v →
          Disjoint (nbrC H u ∩ R) (nbrC H v ∩ R) := by
        intro u hu v hv huv
        rw [Finset.disjoint_left]
        intro a hau hav
        have ha_ne : a ≠ r0 := fun heq => hr0_notR (heq ▸ (Finset.mem_inter.mp hau).2)
        have huf := Finset.mem_filter.mp hu
        have hvf := Finset.mem_filter.mp hv
        have hr0_u : r0 ∈ nbrC H u := profC_subset_nbrC H R u (huf.2.symm ▸ hr0)
        have hr0_v : r0 ∈ nbrC H v := profC_subset_nbrC H R v (hvf.2.symm ▸ hr0)
        have hsub : ({a, r0} : Finset (Fin n)) ⊆ nbrC H u ∩ nbrC H v := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rw [Finset.mem_inter]
          rcases hz with rfl | rfl
          · exact ⟨(Finset.mem_inter.mp hau).1, (Finset.mem_inter.mp hav).1⟩
          · exact ⟨hr0_u, hr0_v⟩
        have hge : 2 ≤ (nbrC H u ∩ nbrC H v).card := by
          calc 2 = ({a, r0} : Finset (Fin n)).card := (Finset.card_pair ha_ne).symm
            _ ≤ (nbrC H u ∩ nbrC H v).card := Finset.card_le_card hsub
        have hle := c4C_of_c4R h.c4R u v huv
        omega
      have hmem_core : ∀ u ∈ cls P, a1 ∈ nbrC H u ∩ R ∨ a2 ∈ nbrC H u ∩ R := by
        intro u hu
        have huf := Finset.mem_filter.mp hu
        rcases (Finset.mem_filter.mp huf.1).2 with ⟨a, haR, hau⟩
        have huB : u ∈ B := (Finset.mem_filter.mp huf.1).1
        have ha1 : a ∈ coreR H R B := Finset.mem_filter.mpr ⟨haR, u, huB, hau⟩
        rw [hR1_eq, Finset.mem_insert, Finset.mem_singleton] at ha1
        rcases ha1 with rfl | rfl
        · left; exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hau⟩, ha1_R⟩
        · right; exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hau⟩, ha2_R⟩
      have hcard_le2 : (cls P).card ≤ 2 := by
        by_contra hgt2
        have hcard3 : 2 < (cls P).card := by omega
        have hsub_xy : ({x, y} : Finset (Fin m)) ⊆ cls P := by
          intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> assumption
        have hne : ((cls P) \ {x, y}).Nonempty := by
          rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub_xy, Finset.card_pair hxy]
          omega
        rcases hne with ⟨z, hz⟩
        rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hz
        have hzx : z ≠ x := fun heq => hz.2 (Or.inl heq)
        have hzy : z ≠ y := fun heq => hz.2 (Or.inr heq)
        rcases hmem_core x hx with hx1 | hx2 <;>
        rcases hmem_core y hy with hy1 | hy2 <;>
        rcases hmem_core z hz.1 with hz1 | hz2
        · exact Finset.disjoint_left.mp (hdisj_in x hx y hy hxy) hx1 hy1
        · exact Finset.disjoint_left.mp (hdisj_in x hx y hy hxy) hx1 hy1
        · exact Finset.disjoint_left.mp (hdisj_in x hx z hz.1 hzx.symm) hx1 hz1
        · exact Finset.disjoint_left.mp (hdisj_in y hy z hz.1 hzy.symm) hy2 hz2
        · exact Finset.disjoint_left.mp (hdisj_in y hy z hz.1 hzy.symm) hy1 hz1
        · exact Finset.disjoint_left.mp (hdisj_in x hx z hz.1 hzx.symm) hx2 hz2
        · exact Finset.disjoint_left.mp (hdisj_in x hx y hy hxy) hx2 hy2
        · exact Finset.disjoint_left.mp (hdisj_in x hx y hy hxy) hx2 hy2
      refine ⟨hcard_le2, ?_⟩
      intro _
      rcases hmem_core x hx with hx1 | hx2
      · exact ⟨x, hx, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_inter.mp hx1).1).2⟩⟩
      · rcases hmem_core y hy with hy1 | hy2
        · exact ⟨y, hy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_inter.mp hy1).1).2⟩⟩
        · exact False.elim (Finset.disjoint_left.mp (hdisj_in x hx y hy hxy) hx2 hy2)
    · exact ⟨by omega, fun h2' => by omega⟩
  let Dset := Pset.filter (fun P => (cls P).card = 2)
  have hdiff : B1.card - Pset.card = Dset.card := by
    have hsum1 : B1.card = Pset.card + Dset.card := by
      rw [hpart]
      have hterm : ∀ P ∈ Pset, (cls P).card = 1 + if (cls P).card = 2 then 1 else 0 := by
        intro P hP
        have hlo := hcls_pos P hP
        have hhi := (hcls_props P hP).1
        by_cases h2' : (cls P).card = 2
        · simp [h2']
        · simp only [h2', ↓reduceIte]; omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
          Nat.mul_one, ← Finset.card_filter]
    omega
  have hD_le_t : Dset.card ≤ t := by
    have hsub : Dset ⊆ Pset := Finset.filter_subset _ _
    have hleP : Pset.card ≤ (B.image (profC H R)).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    exact Nat.le_trans (Finset.card_le_card hsub) (Nat.le_trans hleP h.typesC)
  have hD_le_d : Dset.card ≤ d := by
    have hpick : ∀ P ∈ Dset, ∃ x ∈ cls P, x ∈ nbrR H a1 := by
      intro P hP
      have hPf := Finset.mem_filter.mp hP
      exact (hcls_props P hPf.1).2 hPf.2
    have hle_nbr : Dset.card ≤ (nbrR H a1).card := by
      have hsub_biUnion : Dset.card ≤ (Dset.biUnion (fun P => cls P ∩ nbrR H a1)).card := by
        rw [Finset.card_biUnion]
        · calc Dset.card = ∑ _P ∈ Dset, 1 := by simp
            _ ≤ ∑ P ∈ Dset, (cls P ∩ nbrR H a1).card := by
                apply Finset.sum_le_sum
                intro P hP
                rcases hpick P hP with ⟨x, hx1, hx2⟩
                exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hx1, hx2⟩⟩
        · intro P1 _ P2 _ hne
          change Disjoint (cls P1 ∩ nbrR H a1) (cls P2 ∩ nbrR H a1)
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          have h1 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx1).1).2
          have h2 := (Finset.mem_filter.mp (Finset.mem_inter.mp hx2).1).2
          exact hne (h1.symm.trans h2)
      have hsub : Dset.biUnion (fun P => cls P ∩ nbrR H a1) ⊆ nbrR H a1 := by
        intro x hx
        rw [Finset.mem_biUnion] at hx
        rcases hx with ⟨_, _, hx'⟩
        exact (Finset.mem_inter.mp hx').2
      exact Nat.le_trans hsub_biUnion (Finset.card_le_card hsub)
    exact Nat.le_trans hle_nbr (h.degR a1).2
  have hmin : Dset.card ≤ min d t := Nat.le_min.mpr ⟨hD_le_d, hD_le_t⟩
  change (coreR H R B).card - ((coreR H R B).image (profR H B)).card + (B1.card - Pset.card) ≤ min d t + 1
  omega

lemma case_large_nondeg2 {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B)
    (hR3 : 3 ≤ (coreR H R B).card) (hB3 : 3 ≤ (coreC H R B).card)
    (a0 : Fin n) (ha0 : a0 ∈ coreR H R B)
    (hnon2 : 2 ≤ ((coreC H R B).filter (fun x => H a0 x = false)).card) :
    ((coreR H R B).card - ((coreR H R B).image (profR H B)).card) +
    ((coreC H R B).card - ((coreC H R B).image (profC H R)).card) ≤ 2 := by
  let R1 := coreR H R B
  let B1 := coreC H R B
  let N0 := B1.filter (fun x => H a0 x = false)
  change 3 ≤ R1.card at hR3
  change 3 ≤ B1.card at hB3
  change 2 ≤ N0.card at hnon2
  rcases Finset.one_lt_card.mp (by omega : 1 < N0.card) with ⟨x1, hx1, x2, hx2, hx12⟩
  have hx1f := Finset.mem_filter.mp hx1
  have hx2f := Finset.mem_filter.mp hx2
  let A := R1.filter (fun a => H a x1 = false)
  have hR1_sdiff_sub : R1 \ A ⊆ nbrC H x1 ∩ nbrC H x2 := by
    intro b hb
    rw [Finset.mem_sdiff] at hb
    have hbx1 : H b x1 = true := by
      cases hval : H b x1
      · exact False.elim (hb.2 (Finset.mem_filter.mpr ⟨hb.1, hval⟩))
      · rfl
    have hbx2 : H b x2 = true := by
      cases hval : H b x2
      · have hfx1 := h.closure b hb.1 a0 ha0 x2 hx2f.1 x1 hx1f.1 hval hx2f.2 hx1f.2
        rw [hbx1] at hfx1; cases hfx1
      · rfl
    exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx2⟩⟩
  have hR1_sdiff_le1 : (R1 \ A).card ≤ 1 :=
    Nat.le_trans (Finset.card_le_card hR1_sdiff_sub) (c4C_of_c4R h.c4R x1 x2 hx12)
  have hR1_sdiff_pos : 1 ≤ (R1 \ A).card := by
    rcases (Finset.mem_filter.mp hx1f.1).2 with ⟨b, hbR, hbx1⟩
    have hx1B : x1 ∈ B := (Finset.mem_filter.mp hx1f.1).1
    have hb1 : b ∈ R1 := Finset.mem_filter.mpr ⟨hbR, x1, hx1B, hbx1⟩
    have hb_notA : b ∉ A := by
      intro hm; have hf := (Finset.mem_filter.mp hm).2; rw [hbx1] at hf; cases hf
    exact Finset.card_pos.mpr ⟨b, Finset.mem_sdiff.mpr ⟨hb1, hb_notA⟩⟩
  have hR1_sdiff_eq1 : (R1 \ A).card = 1 := by omega
  rcases Finset.card_eq_one.mp hR1_sdiff_eq1 with ⟨b0, hb0_eq⟩
  have hb0_R1 : b0 ∈ R1 := (Finset.mem_sdiff.mp (by rw [hb0_eq]; simp : b0 ∈ R1 \ A)).1
  have hb0_R : b0 ∈ R := (Finset.mem_filter.mp hb0_R1).1
  have hA_card : A.card = R1.card - 1 := by
    have hsp : (R1 \ A).card + A.card = R1.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ R1)
    omega
  have hA_ge2 : 2 ≤ A.card := by omega
  have hA_adj_sdiff : ∀ a ∈ A, ∀ z ∈ B1 \ N0, H a z = true := by
    intro a ha z hz
    have haf := Finset.mem_filter.mp ha
    have hzf := Finset.mem_sdiff.mp hz
    have ha0z : H a0 z = true := by
      cases hval : H a0 z
      · exact False.elim (hzf.2 (Finset.mem_filter.mpr ⟨hzf.1, hval⟩))
      · rfl
    cases hval : H a z
    · have hfz := h.closure a0 ha0 a haf.1 x1 hx1f.1 z hzf.1 hx1f.2 haf.2 hval
      rw [ha0z] at hfz; cases hfz
    · rfl
  have hB1_sdiff_le1 : (B1 \ N0).card ≤ 1 := by
    by_contra hgt1
    rcases Finset.one_lt_card.mp (by omega : 1 < (B1 \ N0).card) with ⟨z1, hz1, z2, hz2, hz12⟩
    have hA_sub : A ⊆ nbrC H z1 ∩ nbrC H z2 := by
      intro a ha
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA_adj_sdiff a ha z1 hz1⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA_adj_sdiff a ha z2 hz2⟩⟩
    have hle1 := Nat.le_trans (Finset.card_le_card hA_sub) (c4C_of_c4R h.c4R z1 z2 hz12)
    omega
  have hB1_sdiff_pos : 1 ≤ (B1 \ N0).card := by
    rcases (Finset.mem_filter.mp ha0).2 with ⟨z, hzB, ha0z⟩
    have ha0_R : a0 ∈ R := (Finset.mem_filter.mp ha0).1
    have hz1 : z ∈ B1 := Finset.mem_filter.mpr ⟨hzB, a0, ha0_R, ha0z⟩
    have hz_notN : z ∉ N0 := by
      intro hm; have hf := (Finset.mem_filter.mp hm).2; rw [ha0z] at hf; cases hf
    exact Finset.card_pos.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz1, hz_notN⟩⟩
  have hB1_sdiff_eq1 : (B1 \ N0).card = 1 := by omega
  rcases Finset.card_eq_one.mp hB1_sdiff_eq1 with ⟨z0, hz0_eq⟩
  have hz0_B1 : z0 ∈ B1 := (Finset.mem_sdiff.mp (by rw [hz0_eq]; simp : z0 ∈ B1 \ N0)).1
  have hz0_B : z0 ∈ B := (Finset.mem_filter.mp hz0_B1).1
  have hN0_card : N0.card = B1.card - 1 := by
    have hsp : (B1 \ N0).card + N0.card = B1.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ B1)
    omega
  have huniq_A : ∀ a ∈ A, nbrR H a ∩ B = {z0} := by
    intro a ha
    have haf := Finset.mem_filter.mp ha
    ext z
    simp only [Finset.mem_inter, nbrR, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton]
    constructor
    · rintro ⟨haz, hzB⟩
      have haR : a ∈ R := (Finset.mem_filter.mp haf.1).1
      have hzB1 : z ∈ B1 := Finset.mem_filter.mpr ⟨hzB, a, haR, haz⟩
      have hz_notN : z ∉ N0 := by
        intro hm
        have hmf := Finset.mem_filter.mp hm
        have hfz := h.closure a haf.1 a0 ha0 x1 hx1f.1 z hmf.1 haf.2 hx1f.2 hmf.2
        rw [haz] at hfz; cases hfz
      have hzm : z ∈ B1 \ N0 := Finset.mem_sdiff.mpr ⟨hzB1, hz_notN⟩
      rw [hz0_eq, Finset.mem_singleton] at hzm
      exact hzm
    · rintro rfl
      exact ⟨hA_adj_sdiff a ha z (by rw [hz0_eq]; simp), hz0_B⟩
  have huniq_N0 : ∀ x ∈ N0, nbrC H x ∩ R = {b0} := by
    intro x hx
    have hxf := Finset.mem_filter.mp hx
    ext b
    simp only [Finset.mem_inter, nbrC, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_singleton]
    constructor
    · rintro ⟨hbx, hbR⟩
      have hxB : x ∈ B := (Finset.mem_filter.mp hxf.1).1
      have hbR1 : b ∈ R1 := Finset.mem_filter.mpr ⟨hbR, x, hxB, hbx⟩
      have hb_notA : b ∉ A := by
        intro hm
        have hmf := Finset.mem_filter.mp hm
        have hfx := h.closure b hbR1 a0 ha0 x1 hx1f.1 x hxf.1 hmf.2 hx1f.2 hxf.2
        rw [hbx] at hfx; cases hfx
      have hbm : b ∈ R1 \ A := Finset.mem_sdiff.mpr ⟨hbR1, hb_notA⟩
      rw [hb0_eq, Finset.mem_singleton] at hbm
      exact hbm
    · rintro rfl
      have hb0_notA : b ∉ A := (Finset.mem_sdiff.mp (by rw [hb0_eq]; simp : b ∈ R1 \ A)).2
      have hb0_x1 : H b x1 = true := by
        cases hval : H b x1
        · exact False.elim (hb0_notA (Finset.mem_filter.mpr ⟨hb0_R1, hval⟩))
        · rfl
      have hb0_x : H b x = true := by
        cases hval : H b x
        · have hfx1 := h.closure b hb0_R1 a0 ha0 x hxf.1 x1 hx1f.1 hval hxf.2 hx1f.2
          rw [hb0_x1] at hfx1; cases hfx1
        · rfl
      exact ⟨hb0_x, hb0_R⟩
  have hinjA := profC_inj_of_unique_row_nbr h.transpose A z0 hz0_B huniq_A
  have hinjN0 := profC_inj_of_unique_row_nbr h N0 b0 hb0_R huniq_N0
  have htR_ge : A.card ≤ (R1.image (profR H B)).card := by
    calc A.card = (A.image (profR H B)).card := (Finset.card_image_of_injOn hinjA).symm
      _ ≤ (R1.image (profR H B)).card :=
        Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  have htB_ge : N0.card ≤ (B1.image (profC H R)).card := by
    calc N0.card = (N0.image (profC H R)).card := (Finset.card_image_of_injOn hinjN0).symm
      _ ≤ (B1.image (profC H R)).card :=
        Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  change (R1.card - (R1.image (profR H B)).card) + (B1.card - (B1.image (profC H R)).card) ≤ 2
  omega

lemma case_large_nondeg_le1 {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B)
    (hR3 : 3 ≤ (coreR H R B).card) (hB3 : 3 ≤ (coreC H R B).card)
    (hRle1 : ∀ a ∈ coreR H R B, ((coreC H R B).filter (fun x => H a x = false)).card ≤ 1)
    (hBle1 : ∀ x ∈ coreC H R B, ((coreR H R B).filter (fun a => H a x = false)).card ≤ 1) :
    (coreR H R B).card ≤ 3 ∧ (coreC H R B).card ≤ 3 := by
  let R1 := coreR H R B
  let B1 := coreC H R B
  change 3 ≤ R1.card at hR3
  change 3 ≤ B1.card at hB3
  have hboundR : R1.card ≤ 3 := by
    rcases Finset.one_lt_card.mp (by omega : 1 < B1.card) with ⟨x, hx, y, hy, hxy⟩
    let Nx := R1.filter (fun a => H a x = false)
    let Ny := R1.filter (fun a => H a y = false)
    have hsub : R1 \ (Nx ∪ Ny) ⊆ nbrC H x ∩ nbrC H y := by
      intro a ha
      rw [Finset.mem_sdiff, Finset.mem_union] at ha
      have hax : H a x = true := by
        cases hval : H a x
        · exact False.elim (ha.2 (Or.inl (Finset.mem_filter.mpr ⟨ha.1, hval⟩)))
        · rfl
      have hay : H a y = true := by
        cases hval : H a y
        · exact False.elim (ha.2 (Or.inr (Finset.mem_filter.mpr ⟨ha.1, hval⟩)))
        · rfl
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hay⟩⟩
    have hle1 : (R1 \ (Nx ∪ Ny)).card ≤ 1 :=
      Nat.le_trans (Finset.card_le_card hsub) (c4C_of_c4R h.c4R x y hxy)
    have hun : (Nx ∪ Ny).card ≤ 2 := by
      have h1 := Finset.card_union_le Nx Ny
      have hx1 : Nx.card ≤ 1 := hBle1 x hx
      have hy1 : Ny.card ≤ 1 := hBle1 y hy
      omega
    have hsub_un : Nx ∪ Ny ⊆ R1 :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsp := Finset.card_sdiff_add_card_eq_card hsub_un
    omega
  have hboundB : B1.card ≤ 3 := by
    rcases Finset.one_lt_card.mp (by omega : 1 < R1.card) with ⟨a, ha, b, hb, hab⟩
    let Na := B1.filter (fun x => H a x = false)
    let Nb := B1.filter (fun x => H b x = false)
    have hsub : B1 \ (Na ∪ Nb) ⊆ nbrR H a ∩ nbrR H b := by
      intro x hx
      rw [Finset.mem_sdiff, Finset.mem_union] at hx
      have hax : H a x = true := by
        cases hval : H a x
        · exact False.elim (hx.2 (Or.inl (Finset.mem_filter.mpr ⟨hx.1, hval⟩)))
        · rfl
      have hbx : H b x = true := by
        cases hval : H b x
        · exact False.elim (hx.2 (Or.inr (Finset.mem_filter.mpr ⟨hx.1, hval⟩)))
        · rfl
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hax⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩⟩
    have hle1 : (B1 \ (Na ∪ Nb)).card ≤ 1 :=
      Nat.le_trans (Finset.card_le_card hsub) (h.c4R a b hab)
    have hun : (Na ∪ Nb).card ≤ 2 := by
      have h1 := Finset.card_union_le Na Nb
      have ha1 : Na.card ≤ 1 := hRle1 a ha
      have hb1 : Nb.card ≤ 1 := hRle1 b hb
      omega
    have hsub_un : Na ∪ Nb ⊆ B1 :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsp := Finset.card_sdiff_add_card_eq_card hsub_un
    omega
  exact ⟨hboundR, hboundB⟩

lemma upper_bound_true {d t n m : ℕ} {H : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B) :
    R.card + B.card ≤ 2 * t + max 4 (min d t + 1) := by
  have hred := core_sum_reduction h
  dsimp only at hred
  let R1 := coreR H R B
  let B1 := coreC H R B
  let tR := (R1.image (profR H B)).card
  let tB := (B1.image (profC H R)).card
  have hcore_bound : (R1.card - tR) + (B1.card - tB) ≤ max 4 (min d t + 1) := by
    by_cases hR0 : R1.card = 0
    · have hB0 : B1.card = 0 := by
        rw [Finset.card_eq_zero] at hR0 ⊢
        rw [← Finset.not_nonempty_iff_eq_empty] at hR0 ⊢
        exact fun hne => hR0 ((core_nonempty_iff H R B).mpr hne)
      omega
    · by_cases hR1 : R1.card = 1
      · have h0 : (R1.card - tR) + (B1.card - tB) = 0 := case_coreR_eq_1 h hR1; omega
      · by_cases hB1 : B1.card = 1
        · have h0 : (B1.card - tB) + (R1.card - tR) = 0 := case_coreR_eq_1 h.transpose hB1
          omega
        · by_cases hR2 : R1.card = 2
          · have hle : (R1.card - tR) + (B1.card - tB) ≤ min d t + 1 := case_coreR_eq_2 h hR2
            exact Nat.le_trans hle (Nat.le_max_right _ _)
          · by_cases hB2 : B1.card = 2
            · have hle : (B1.card - tB) + (R1.card - tR) ≤ min d t + 1 := case_coreR_eq_2 h.transpose hB2
              exact Nat.le_trans (by omega : (R1.card - tR) + (B1.card - tB) ≤ min d t + 1)
                (Nat.le_max_right _ _)
            · have hB0 : B1.card ≠ 0 := by
                intro hB0
                rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty] at hB0
                have hRne : R1.Nonempty := Finset.card_pos.mp (by omega)
                exact hB0 ((core_nonempty_iff H R B).mp hRne)
              have hR3 : 3 ≤ R1.card := by omega
              have hB3 : 3 ≤ B1.card := by omega
              by_cases hexR : ∃ a ∈ R1, 2 ≤ (B1.filter (fun x => H a x = false)).card
              · rcases hexR with ⟨a0, ha0, hnon2⟩
                have hle : (R1.card - tR) + (B1.card - tB) ≤ 2 := case_large_nondeg2 h hR3 hB3 a0 ha0 hnon2
                exact Nat.le_trans hle (Nat.le_trans (by omega : 2 ≤ 4) (Nat.le_max_left _ _))
              · by_cases hexB : ∃ x ∈ B1, 2 ≤ (R1.filter (fun a => H a x = false)).card
                · rcases hexB with ⟨x0, hx0, hnon2⟩
                  have hle : (B1.card - tB) + (R1.card - tR) ≤ 2 := case_large_nondeg2 h.transpose hB3 hR3 x0 hx0 hnon2
                  exact Nat.le_trans (by omega : (R1.card - tR) + (B1.card - tB) ≤ 2)
                    (Nat.le_trans (by omega : 2 ≤ 4) (Nat.le_max_left _ _))
                · have hRle1 : ∀ a ∈ R1, (B1.filter (fun x => H a x = false)).card ≤ 1 := by
                    intro a ha; by_contra hgt; exact hexR ⟨a, ha, by omega⟩
                  have hBle1 : ∀ x ∈ B1, (R1.filter (fun a => H a x = false)).card ≤ 1 := by
                    intro x hx; by_contra hgt; exact hexB ⟨x, hx, by omega⟩
                  have h33 : R1.card ≤ 3 ∧ B1.card ≤ 3 := case_large_nondeg_le1 h hR3 hB3 hRle1 hBle1
                  have htR1 : 1 ≤ tR := Finset.card_pos.mpr
                    (Finset.Nonempty.image (Finset.card_pos.mp (by omega)) _)
                  have htB1 : 1 ≤ tB := Finset.card_pos.mpr
                    (Finset.Nonempty.image (Finset.card_pos.mp (by omega)) _)
                  exact Nat.le_trans (by omega : (R1.card - tR) + (B1.card - tB) ≤ 4)
                    (Nat.le_max_left _ _)
  have h1 : R.card + B.card ≤ 2 * t + (R1.card - tR) + (B1.card - tB) := hred.1
  omega

lemma constr_c6 (d t : ℕ) (hd : 2 ≤ d) (ht : 2 ≤ t) :
    ∃ (n m : ℕ) (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)),
      AdmissibleTrue d t n m H R B ∧ R.card + B.card = 2 * t + 4 := by
  let blocks := 2 * t - 1
  let n := 3 * blocks
  let H : Fin n → Fin n → Bool := fun a c => decide (a.val / 3 = c.val / 3 ∧ a.val % 3 ≠ c.val % 3)
  let R : Finset (Fin n) := Finset.univ.filter (fun a =>
    a.val < 3 ∨ (a.val % 3 = 0 ∧ 1 ≤ a.val / 3 ∧ a.val / 3 < t))
  let B : Finset (Fin n) := Finset.univ.filter (fun c =>
    c.val < 3 ∨ (c.val % 3 = 0 ∧ t ≤ c.val / 3))
  have hdegR : ∀ a : Fin n, (nbrR H a).card = 2 := by
    intro a
    let q := a.val / 3
    let r := a.val % 3
    have hq : q < blocks := by dsimp only [q, n] at *; omega
    let c1 : Fin n := ⟨3 * q + (r + 1) % 3, by dsimp only [n]; omega⟩
    let c2 : Fin n := ⟨3 * q + (r + 2) % 3, by dsimp only [n]; omega⟩
    have h12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp only [c1, c2] at this; omega
    have heq : nbrR H a = {c1, c2} := by
      ext c
      simp only [nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
                 Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
      dsimp only [c1, c2, q, r]
      omega
    rw [heq, Finset.card_pair h12]
  have hdegC : ∀ c : Fin n, (nbrC H c).card = 2 := by
    intro c
    have hsym : nbrC H c = nbrR H c := by
      ext a; simp only [nbrC, nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
    rw [hsym]; exact hdegR c
  have hc4 : ∀ a b : Fin n, a ≠ b → (nbrR H a ∩ nbrR H b).card ≤ 1 := by
    intro a b hab
    by_cases hq : a.val / 3 = b.val / 3
    · let q := a.val / 3
      have hq_lt : q < blocks := by dsimp only [q, n] at *; omega
      let c0 : Fin n := ⟨3 * q + (3 - a.val % 3 - b.val % 3), by dsimp only [n]; omega⟩
      have hsub : nbrR H a ∩ nbrR H b ⊆ {c0} := by
        intro c hc
        simp only [Finset.mem_inter, nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and,
                   decide_eq_true_eq] at hc
        rw [Finset.mem_singleton, Fin.ext_iff]
        have hne : a.val ≠ b.val := fun h => hab (Fin.ext h)
        dsimp only [c0, q]; omega
      exact Nat.le_trans (Finset.card_le_card hsub) (by simp)
    · have hemp : nbrR H a ∩ nbrR H b = ∅ := by
        ext c
        simp only [Finset.mem_inter, nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and,
                   decide_eq_true_eq, Finset.notMem_empty, iff_false]
        intro hc; exact hq (hc.1.1.trans hc.2.1.symm)
      rw [hemp]; simp
  have hR_card : R.card = t + 2 := by
    let R_core := Finset.univ.filter (fun a : Fin n => a.val < 3)
    let R_iso := Finset.univ.filter (fun a : Fin n => a.val % 3 = 0 ∧ 1 ≤ a.val / 3 ∧ a.val / 3 < t)
    have hdisj : Disjoint R_core R_iso := by
      rw [Finset.disjoint_left]; intro a h1 h2
      simp only [R_core, R_iso, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    have hun : R_core ∪ R_iso = R := by
      ext a; simp only [R_core, R_iso, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc1 : R_core.card = 3 :=
      card_eq_of_fin_bij 3 R_core (fun j => ⟨j.val, by dsimp only [n, blocks]; omega⟩)
        (fun j => by simp [R_core])
        (fun j1 j2 h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
        (fun a ha => by
          simp only [R_core, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ⟨⟨a.val, ha⟩, Fin.ext rfl⟩)
    have hc2 : R_iso.card = t - 1 :=
      card_eq_of_fin_bij (t - 1) R_iso (fun j => ⟨3 * (j.val + 1), by dsimp only [n, blocks]; omega⟩)
        (fun j => by simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : 3 * (j1.val + 1) = 3 * (j2.val + 1) := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun a ha => by
          simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ⟨⟨a.val / 3 - 1, by omega⟩, Fin.ext (by dsimp only; omega)⟩)
    rw [← hun, Finset.card_union_of_disjoint hdisj, hc1, hc2]; omega
  have hB_card : B.card = t + 2 := by
    let B_core := Finset.univ.filter (fun c : Fin n => c.val < 3)
    let B_iso := Finset.univ.filter (fun c : Fin n => c.val % 3 = 0 ∧ t ≤ c.val / 3)
    have hdisj : Disjoint B_core B_iso := by
      rw [Finset.disjoint_left]; intro c h1 h2
      simp only [B_core, B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    have hun : B_core ∪ B_iso = B := by
      ext c; simp only [B_core, B_iso, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc1 : B_core.card = 3 :=
      card_eq_of_fin_bij 3 B_core (fun j => ⟨j.val, by dsimp only [n, blocks]; omega⟩)
        (fun j => by simp [B_core])
        (fun j1 j2 h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
        (fun c hc => by
          simp only [B_core, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact ⟨⟨c.val, hc⟩, Fin.ext rfl⟩)
    have hc2 : B_iso.card = t - 1 :=
      card_eq_of_fin_bij (t - 1) B_iso (fun j => ⟨3 * (t + j.val), by dsimp only [n, blocks]; omega⟩)
        (fun j => by simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : 3 * (t + j1.val) = 3 * (t + j2.val) := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun c hc => by
          simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have hlt : c.val / 3 < blocks := by dsimp only [n] at *; omega
          exact ⟨⟨c.val / 3 - t, by dsimp only [blocks] at hlt; omega⟩, Fin.ext (by dsimp only; omega)⟩)
    rw [← hun, Finset.card_union_of_disjoint hdisj, hc1, hc2]; omega
  have htypesR : (R.image (profR H B)).card ≤ t := by
    let R_iso := Finset.univ.filter (fun a : Fin n => a.val % 3 = 0 ∧ 1 ≤ a.val / 3 ∧ a.val / 3 < t)
    have hsub : R.image (profR H B) ⊆ insert ∅ (R_iso.image (profR H B)) := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases ha with ha3 | hais
      · rw [Finset.mem_insert]; left
        ext c
        simp only [profR, H, B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
                   decide_eq_true_eq, Finset.notMem_empty, iff_false]
        intro hc; omega
      · rw [Finset.mem_insert]; right
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hais⟩)
    have hle_iso : R_iso.card = t - 1 :=
      card_eq_of_fin_bij (t - 1) R_iso (fun j => ⟨3 * (j.val + 1), by dsimp only [n, blocks]; omega⟩)
        (fun j => by simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : 3 * (j1.val + 1) = 3 * (j2.val + 1) := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun a ha => by
          simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ⟨⟨a.val / 3 - 1, by omega⟩, Fin.ext (by dsimp only; omega)⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (∅ : Finset (Fin n)) (R_iso.image (profR H B))
    have h3 : (R_iso.image (profR H B)).card ≤ R_iso.card := Finset.card_image_le
    omega
  have htypesC : (B.image (profC H R)).card ≤ t := by
    let B_iso := Finset.univ.filter (fun c : Fin n => c.val % 3 = 0 ∧ t ≤ c.val / 3)
    have hsub : B.image (profC H R) ⊆ insert ∅ (B_iso.image (profC H R)) := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rcases hc with hc3 | hcis
      · rw [Finset.mem_insert]; left
        ext a
        simp only [profC, H, R, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
                   decide_eq_true_eq, Finset.notMem_empty, iff_false]
        intro ha; omega
      · rw [Finset.mem_insert]; right
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcis⟩)
    have hle_iso : B_iso.card = t - 1 :=
      card_eq_of_fin_bij (t - 1) B_iso (fun j => ⟨3 * (t + j.val), by dsimp only [n, blocks]; omega⟩)
        (fun j => by simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : 3 * (t + j1.val) = 3 * (t + j2.val) := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun c hc => by
          simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have hlt : c.val / 3 < blocks := by dsimp only [n] at *; omega
          exact ⟨⟨c.val / 3 - t, by dsimp only [blocks] at hlt; omega⟩, Fin.ext (by dsimp only; omega)⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (∅ : Finset (Fin n)) (B_iso.image (profC H R))
    have h3 : (B_iso.image (profC H R)).card ≤ B_iso.card := Finset.card_image_le
    omega
  have hcl : ∀ a ∈ coreR H R B, ∀ b ∈ coreR H R B,
      ∀ x ∈ coreC H R B, ∀ y ∈ coreC H R B,
        H a x = false → H b x = false → H b y = false → H a y = false := by
    intro a ha b hb x hx y hy hax hbx hby
    have hlt3 : ∀ u ∈ coreR H R B, u.val < 3 := by
      intro u hu
      rcases (Finset.mem_filter.mp hu).2 with ⟨c, hcB, huc⟩
      have huR := (Finset.mem_filter.mp hu).1
      simp only [R, B, H, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at huR hcB huc
      omega
    have hlt3C : ∀ v ∈ coreC H R B, v.val < 3 := by
      intro v hv
      rcases (Finset.mem_filter.mp hv).2 with ⟨u, huR, huv⟩
      have hvB := (Finset.mem_filter.mp hv).1
      simp only [R, B, H, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at huR hvB huv
      omega
    have ha3 := hlt3 a ha; have hb3 := hlt3 b hb; have hx3 := hlt3C x hx; have hy3 := hlt3C y hy
    simp only [H, decide_eq_false_iff_not] at hax hbx hby ⊢
    omega
  refine ⟨n, n, H, R, B, ?_, by omega⟩
  exact ⟨fun a => by rw [hdegR a]; exact ⟨by omega, hd⟩,
         fun c => by rw [hdegC c]; exact ⟨by omega, hd⟩,
         hc4, htypesR, htypesC, hcl⟩

lemma constr_stars (d t : ℕ) (hd : 2 ≤ d) (ht : 2 ≤ t) :
    ∃ (n m : ℕ) (H : Fin n → Fin m → Bool) (R : Finset (Fin n)) (B : Finset (Fin m)),
      AdmissibleTrue d t n m H R B ∧ R.card + B.card = 2 * t + min d t + 1 := by
  let s := min d t
  have hs2 : 2 ≤ s := Nat.le_min.mpr ⟨hd, ht⟩
  have hsd : s ≤ d := Nat.min_le_left d t
  have hst : s ≤ t := Nat.min_le_right d t
  let kR := t - 1
  let kB := t - s
  let n0 := 2 + s
  let m0 := 2 * s
  let n := n0 + 3 * (kR + kB)
  let m := m0 + 3 * (kR + kB)
  let H : Fin n → Fin m → Bool := fun a c =>
    if a.val < 2 ∧ c.val < m0 then
      decide (a.val = c.val / s)
    else if 2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0 then
      decide (a.val - 2 = c.val % s)
    else if n0 ≤ a.val ∧ m0 ≤ c.val then
      decide ((a.val - n0) / 3 = (c.val - m0) / 3 ∧ (a.val - n0) % 3 ≠ (c.val - m0) % 3)
    else
      false
  let R : Finset (Fin n) := Finset.univ.filter (fun a =>
    a.val < 2 ∨ (n0 ≤ a.val ∧ (a.val - n0) % 3 = 0 ∧ (a.val - n0) / 3 < kR))
  let B : Finset (Fin m) := Finset.univ.filter (fun c =>
    c.val < m0 ∨ (m0 ≤ c.val ∧ (c.val - m0) % 3 = 0 ∧ kR ≤ (c.val - m0) / 3))
  have hdegR : ∀ a : Fin n, 2 ≤ (nbrR H a).card ∧ (nbrR H a).card ≤ d := by
    intro a
    by_cases ha2 : a.val < 2
    · have hcard : (nbrR H a).card = s :=
        card_eq_of_fin_bij s (nbrR H a)
          (fun j => ⟨a.val * s + j.val, by
            have hj := j.isLt
            have h01 : a.val = 0 ∨ a.val = 1 := by omega
            rcases h01 with h0 | h1
            · dsimp only [m, m0]; rw [h0, Nat.zero_mul, Nat.zero_add]; omega
            · dsimp only [m, m0]; rw [h1, Nat.one_mul]; omega⟩)
          (fun j => by
            simp only [nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and]
            have hltm : a.val * s + j.val < m0 := by
              have hj := j.isLt
              have h01 : a.val = 0 ∨ a.val = 1 := by omega
              rcases h01 with h0 | h1
              · dsimp only [m0]; rw [h0, Nat.zero_mul, Nat.zero_add]; omega
              · dsimp only [m0]; rw [h1, Nat.one_mul]; omega
            have h1 : a.val < 2 ∧ a.val * s + j.val < m0 := ⟨ha2, hltm⟩
            simp only [h1, and_self, ↓reduceIte, decide_eq_true_eq]
            have hdiv : (a.val * s + j.val) / s = a.val := by
              rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
            exact hdiv.symm)
          (fun j1 j2 h => by
            have hv : a.val * s + j1.val = a.val * s + j2.val := congrArg Fin.val h
            exact Fin.ext (by omega))
          (fun c hc => by
            simp only [nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and] at hc
            by_cases hcm : c.val < m0
            · have h1 : a.val < 2 ∧ c.val < m0 := ⟨ha2, hcm⟩
              simp only [h1, and_self, ↓reduceIte, decide_eq_true_eq] at hc
              refine ⟨⟨c.val % s, Nat.mod_lt _ (by omega)⟩, Fin.ext ?_⟩
              dsimp only
              have hdm := Nat.div_add_mod c.val s
              rw [← hc, Nat.mul_comm] at hdm; omega
            · have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
              have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
              have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by dsimp only [n0]; omega
              simp only [h1, h2, h3, ↓reduceIte] at hc; cases hc)
      rw [hcard]; exact ⟨hs2, hsd⟩
    · by_cases han : a.val < n0
      · let j := a.val - 2
        let c1 : Fin m := ⟨j, by dsimp only [m, m0, j, n0] at *; omega⟩
        let c2 : Fin m := ⟨s + j, by dsimp only [m, m0, j, n0] at *; omega⟩
        have h12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp only [c1, c2] at this; omega
        have heq : nbrR H a = {c1, c2} := by
          ext c
          simp only [nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and,
                     Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          by_cases hcm : c.val < m0
          · have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
            have h2 : 2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0 := ⟨by omega, han, hcm⟩
            simp only [h1, ↓reduceIte]
            simp only [h2, and_self, ↓reduceIte, decide_eq_true_eq]
            have hdm := Nat.div_add_mod c.val s
            have hmod := Nat.mod_lt c.val (by omega : 0 < s)
            have hlt2 : c.val / s < 2 := Nat.div_lt_of_lt_mul (by dsimp only [m0] at hcm; omega)
            have hjlt : j < s := by dsimp only [j, n0] at han ⊢; omega
            constructor
            · intro he
              generalize hq : c.val / s = q at hlt2 hdm
              by_cases hd0 : q = 0
              · left; dsimp only [c1, j]; rw [hd0, mul_zero, zero_add] at hdm; omega
              · right; have hd1 : q = 1 := by omega
                dsimp only [c2, j]; rw [hd1, mul_one] at hdm; omega
            · rintro (hc1 | hc2)
              · dsimp only [c1, j] at hc1
                rw [hc1, Nat.mod_eq_of_lt (by dsimp only [j] at hjlt; omega)]
              · dsimp only [c2, j] at hc2
                rw [hc2, Nat.add_mod_left, Nat.mod_eq_of_lt (by dsimp only [j] at hjlt; omega)]
          · have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
            have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
            have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by omega
            simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, false_iff]
            dsimp only [c1, c2, j, m0, n0] at hcm han ⊢; omega
        rw [heq, Finset.card_pair h12]; exact ⟨by omega, hd⟩
      · let q := (a.val - n0) / 3
        let r := (a.val - n0) % 3
        have ha_lt := a.isLt
        have hq : q < kR + kB := by dsimp only [q, n] at ha_lt ⊢; omega
        let c1 : Fin m := ⟨m0 + 3 * q + (r + 1) % 3, by dsimp only [m]; omega⟩
        let c2 : Fin m := ⟨m0 + 3 * q + (r + 2) % 3, by dsimp only [m]; omega⟩
        have h12 : c1 ≠ c2 := by intro h; have := congrArg Fin.val h; dsimp only [c1, c2] at this; omega
        have heq : nbrR H a = {c1, c2} := by
          ext c
          simp only [nbrR, H, Finset.mem_filter, Finset.mem_univ, true_and,
                     Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
          have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by dsimp only [n0] at han; omega
          have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
          by_cases hcm : m0 ≤ c.val
          · have h3 : n0 ≤ a.val ∧ m0 ≤ c.val := ⟨by omega, hcm⟩
            simp only [h1, h2, h3, and_self, ↓reduceIte, decide_eq_true_eq]
            dsimp only [c1, c2, q, r]; omega
          · have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by omega
            simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, false_iff]
            dsimp only [c1, c2, q, r]; omega
        rw [heq, Finset.card_pair h12]; exact ⟨by omega, hd⟩
  have hdegC : ∀ c : Fin m, 2 ≤ (nbrC H c).card ∧ (nbrC H c).card ≤ d := by
    intro c
    by_cases hcm : c.val < m0
    · have hlt2 : c.val / s < 2 := Nat.div_lt_of_lt_mul (by dsimp only [m0] at hcm; omega)
      have hmod := Nat.mod_lt c.val (by omega : 0 < s)
      let a1 : Fin n := ⟨c.val / s, by dsimp only [n, n0]; omega⟩
      let a2 : Fin n := ⟨2 + c.val % s, by dsimp only [n, n0]; omega⟩
      have h12 : a1 ≠ a2 := by
        intro h; have := congrArg Fin.val h
        dsimp only [a1, a2] at this; omega
      have heq : nbrC H c = {a1, a2} := by
        ext a
        simp only [nbrC, H, Finset.mem_filter, Finset.mem_univ, true_and,
                   Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        by_cases ha2 : a.val < 2
        · have h1 : a.val < 2 ∧ c.val < m0 := ⟨ha2, hcm⟩
          simp only [h1, and_self, ↓reduceIte, decide_eq_true_eq]
          dsimp only [a1, a2]; omega
        · by_cases han : a.val < n0
          · have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
            have h2 : 2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0 := ⟨by omega, han, hcm⟩
            simp only [h1, ↓reduceIte]
            simp only [h2, and_self, ↓reduceIte, decide_eq_true_eq]
            dsimp only [a1, a2]; omega
          · have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
            have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
            have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by omega
            simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, false_iff]
            dsimp only [a1, a2, n0] at han ⊢; omega
      rw [heq, Finset.card_pair h12]; exact ⟨by omega, hd⟩
    · let q := (c.val - m0) / 3
      let r := (c.val - m0) % 3
      have hc_lt := c.isLt
      have hq : q < kR + kB := by dsimp only [q, m] at hc_lt ⊢; omega
      let a1 : Fin n := ⟨n0 + 3 * q + (r + 1) % 3, by dsimp only [n]; omega⟩
      let a2 : Fin n := ⟨n0 + 3 * q + (r + 2) % 3, by dsimp only [n]; omega⟩
      have h12 : a1 ≠ a2 := by intro h; have := congrArg Fin.val h; dsimp only [a1, a2] at this; omega
      have heq : nbrC H c = {a1, a2} := by
        ext a
        simp only [nbrC, H, Finset.mem_filter, Finset.mem_univ, true_and,
                   Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
        have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
        have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
        by_cases han : n0 ≤ a.val
        · have h3 : n0 ≤ a.val ∧ m0 ≤ c.val := ⟨han, by omega⟩
          simp only [h1, h2, h3, and_self, ↓reduceIte, decide_eq_true_eq]
          dsimp only [a1, a2, q, r]; omega
        · have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by omega
          simp only [h1, h2, h3, ↓reduceIte, Bool.false_eq_true, false_iff]
          dsimp only [a1, a2, q, r]; omega
      rw [heq, Finset.card_pair h12]; exact ⟨by omega, hd⟩
  have hc4 : ∀ a b : Fin n, a ≠ b → (nbrR H a ∩ nbrR H b).card ≤ 1 := by
    intro a b hab
    by_contra hgt
    rcases Finset.one_lt_card.mp (by omega : 1 < (nbrR H a ∩ nbrR H b).card) with ⟨c1, hc1, c2, hc2, hc12⟩
    simp only [Finset.mem_inter, nbrR, Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
    have hne_ab : a.val ≠ b.val := fun h => hab (Fin.ext h)
    have hne_c : c1.val ≠ c2.val := fun h => hc12 (Fin.ext h)
    have hzone : ∀ (u : Fin n) (c : Fin m), H u c = true →
        (u.val < 2 ∧ c.val < m0 ∧ u.val = c.val / s) ∨
        (2 ≤ u.val ∧ u.val < n0 ∧ c.val < m0 ∧ u.val - 2 = c.val % s) ∨
        (n0 ≤ u.val ∧ m0 ≤ c.val ∧ (u.val - n0) / 3 = (c.val - m0) / 3 ∧
          (u.val - n0) % 3 ≠ (c.val - m0) % 3) := by
      intro u c huc
      dsimp only [H] at huc
      by_cases h1 : u.val < 2 ∧ c.val < m0
      · simp only [h1, and_self, ↓reduceIte, decide_eq_true_eq] at huc; exact Or.inl ⟨h1.1, h1.2, huc⟩
      · simp only [h1, ↓reduceIte] at huc
        by_cases h2 : 2 ≤ u.val ∧ u.val < n0 ∧ c.val < m0
        · simp only [h2, and_self, ↓reduceIte, decide_eq_true_eq] at huc
          exact Or.inr (Or.inl ⟨h2.1, h2.2.1, h2.2.2, huc⟩)
        · simp only [h2, ↓reduceIte] at huc
          by_cases h3 : n0 ≤ u.val ∧ m0 ≤ c.val
          · simp only [h3, and_self, ↓reduceIte, decide_eq_true_eq] at huc
            exact Or.inr (Or.inr ⟨h3.1, h3.2, huc.1, huc.2⟩)
          · simp only [h3, ↓reduceIte] at huc; cases huc
    have ha1 := hzone a c1 hc1.1
    have ha2 := hzone a c2 hc2.1
    have hb1 := hzone b c1 hc1.2
    have hb2 := hzone b c2 hc2.2
    rcases ha1 with ⟨_, _, ha1d⟩ | ⟨_, _, _, ha1m⟩ | ⟨_, _, ha1q, ha1r⟩ <;>
    rcases ha2 with ⟨_, _, ha2d⟩ | ⟨_, _, _, ha2m⟩ | ⟨_, _, ha2q, ha2r⟩ <;>
    rcases hb1 with ⟨_, _, hb1d⟩ | ⟨_, _, _, hb1m⟩ | ⟨_, _, hb1q, hb1r⟩ <;>
    rcases hb2 with ⟨_, _, hb2d⟩ | ⟨_, _, _, hb2m⟩ | ⟨_, _, hb2q, hb2r⟩
    all_goals try (dsimp only [n0, m0] at *; omega)
    · have hdm1 := Nat.div_add_mod c1.val s
      have hdm2 := Nat.div_add_mod c2.val s
      rw [← ha1d] at hdm1; rw [← ha2d] at hdm2; omega
    · have hdm1 := Nat.div_add_mod c1.val s
      have hdm2 := Nat.div_add_mod c2.val s
      rw [← hb1d] at hdm1; rw [← hb2d] at hdm2; omega
  have hR_card : R.card = t + 1 := by
    let R_core := Finset.univ.filter (fun a : Fin n => a.val < 2)
    let R_iso := Finset.univ.filter (fun a : Fin n =>
      n0 ≤ a.val ∧ (a.val - n0) % 3 = 0 ∧ (a.val - n0) / 3 < kR)
    have hdisj : Disjoint R_core R_iso := by
      rw [Finset.disjoint_left]; intro a h1 h2
      simp only [R_core, R_iso, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      dsimp only [n0] at h2; omega
    have hun : R_core ∪ R_iso = R := by
      ext a; simp only [R_core, R_iso, R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc1 : R_core.card = 2 :=
      card_eq_of_fin_bij 2 R_core (fun j => ⟨j.val, by dsimp only [n, n0]; omega⟩)
        (fun j => by simp only [R_core, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => Fin.ext (congrArg (Fin.val : Fin n → ℕ) h))
        (fun a ha => by
          simp only [R_core, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ⟨⟨a.val, ha⟩, Fin.ext rfl⟩)
    have hc2 : R_iso.card = kR :=
      card_eq_of_fin_bij kR R_iso (fun j => ⟨n0 + 3 * j.val, by dsimp only [n]; omega⟩)
        (fun j => by simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : n0 + 3 * j1.val = n0 + 3 * j2.val := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun a ha => by
          simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ⟨⟨(a.val - n0) / 3, ha.2.2⟩, Fin.ext (by dsimp only; omega)⟩)
    rw [← hun, Finset.card_union_of_disjoint hdisj, hc1, hc2]; dsimp only [kR]; omega
  have hB_card : B.card = t + s := by
    let B_core := Finset.univ.filter (fun c : Fin m => c.val < m0)
    let B_iso := Finset.univ.filter (fun c : Fin m =>
      m0 ≤ c.val ∧ (c.val - m0) % 3 = 0 ∧ kR ≤ (c.val - m0) / 3)
    have hdisj : Disjoint B_core B_iso := by
      rw [Finset.disjoint_left]; intro c h1 h2
      simp only [B_core, B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
    have hun : B_core ∪ B_iso = B := by
      ext c; simp only [B_core, B_iso, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have hc1 : B_core.card = m0 :=
      card_eq_of_fin_bij m0 B_core (fun j => ⟨j.val, by dsimp only [m]; omega⟩)
        (fun j => by simp [B_core])
        (fun j1 j2 h => Fin.ext (congrArg (Fin.val : Fin m → ℕ) h))
        (fun c hc => by
          simp only [B_core, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          exact ⟨⟨c.val, hc⟩, Fin.ext rfl⟩)
    have hc2 : B_iso.card = kB :=
      card_eq_of_fin_bij kB B_iso (fun j => ⟨m0 + 3 * (kR + j.val), by dsimp only [m]; omega⟩)
        (fun j => by simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : m0 + 3 * (kR + j1.val) = m0 + 3 * (kR + j2.val) := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun c hc => by
          simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have hc_lt := c.isLt
          have hlt : (c.val - m0) / 3 < kR + kB := by dsimp only [m] at hc_lt; omega
          exact ⟨⟨(c.val - m0) / 3 - kR, by omega⟩, Fin.ext (by dsimp only; omega)⟩)
    rw [← hun, Finset.card_union_of_disjoint hdisj, hc1, hc2]; dsimp only [m0, kB]; omega
  have htypesR : (R.image (profR H B)).card ≤ t := by
    let R_iso := Finset.univ.filter (fun a : Fin n =>
      n0 ≤ a.val ∧ (a.val - n0) % 3 = 0 ∧ (a.val - n0) / 3 < kR)
    have hsub : R.image (profR H B) ⊆ insert ∅ (R_iso.image (profR H B)) := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨a, ha, rfl⟩
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      rcases ha with ha2 | hais
      · rw [Finset.mem_insert]; left
        ext c
        simp only [profR, H, B, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
                   Finset.notMem_empty, iff_false]
        intro hc
        have hcm : ¬ (c.val < m0) := fun hlt => hc.1 (Or.inl hlt)
        have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
        have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
        have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by dsimp only [n0]; omega
        simp only [h1, h2, h3, ↓reduceIte] at hc; cases hc.2
      · rw [Finset.mem_insert]; right
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hais⟩)
    have hle_iso : R_iso.card = kR :=
      card_eq_of_fin_bij kR R_iso (fun j => ⟨n0 + 3 * j.val, by dsimp only [n]; omega⟩)
        (fun j => by simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : n0 + 3 * j1.val = n0 + 3 * j2.val := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun a ha => by
          simp only [R_iso, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ⟨⟨(a.val - n0) / 3, ha.2.2⟩, Fin.ext (by dsimp only; omega)⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le (∅ : Finset (Fin m)) (R_iso.image (profR H B))
    have h3 : (R_iso.image (profR H B)).card ≤ R_iso.card := Finset.card_image_le
    dsimp only [kR] at hle_iso; omega
  have htypesC : (B.image (profC H R)).card ≤ t := by
    let B_iso := Finset.univ.filter (fun c : Fin m =>
      m0 ≤ c.val ∧ (c.val - m0) % 3 = 0 ∧ kR ≤ (c.val - m0) / 3)
    let pairedTypes : Finset (Finset (Fin n)) :=
      (Finset.univ : Finset (Fin s)).image (fun j =>
        ({⟨2 + j.val, by dsimp only [n, n0]; omega⟩} : Finset (Fin n)))
    have hsub : B.image (profC H R) ⊆ pairedTypes ∪ B_iso.image (profC H R) := by
      intro P hP
      rcases Finset.mem_image.mp hP with ⟨c, hc, rfl⟩
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hc
      rcases hc with hcm | hcis
      · rw [Finset.mem_union]; left
        rw [Finset.mem_image]
        refine ⟨⟨c.val % s, Nat.mod_lt _ (by omega)⟩, Finset.mem_univ _, ?_⟩
        ext a
        simp only [profC, H, R, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
                   Finset.mem_singleton, Fin.ext_iff]
        constructor
        · intro heq
          have hmod := Nat.mod_lt c.val (by omega : 0 < s)
          have ha2 : ¬ (a.val < 2) := by omega
          have han : a.val < n0 := by dsimp only [n0]; omega
          have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
          have h2 : 2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0 := ⟨by omega, han, hcm⟩
          refine ⟨by omega, ?_⟩
          simp only [h1, ↓reduceIte]
          simp only [h2, and_self, ↓reduceIte, decide_eq_true_eq]; omega
        · intro ha
          have ha2 : ¬ (a.val < 2) := fun hlt => ha.1 (Or.inl hlt)
          have h1 : ¬ (a.val < 2 ∧ c.val < m0) := by omega
          by_cases han : a.val < n0
          · have h2 : 2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0 := ⟨by omega, han, hcm⟩
            simp only [h1, ↓reduceIte] at ha
            simp only [h2, and_self, ↓reduceIte, decide_eq_true_eq] at ha; omega
          · have h2 : ¬ (2 ≤ a.val ∧ a.val < n0 ∧ c.val < m0) := by omega
            have h3 : ¬ (n0 ≤ a.val ∧ m0 ≤ c.val) := by omega
            simp only [h1, h2, h3, ↓reduceIte] at ha; cases ha.2
      · rw [Finset.mem_union]; right
        exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcis⟩)
    have hle_iso : B_iso.card = kB :=
      card_eq_of_fin_bij kB B_iso (fun j => ⟨m0 + 3 * (kR + j.val), by dsimp only [m]; omega⟩)
        (fun j => by simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
        (fun j1 j2 h => by have hv : m0 + 3 * (kR + j1.val) = m0 + 3 * (kR + j2.val) := congrArg Fin.val h; exact Fin.ext (by omega))
        (fun c hc => by
          simp only [B_iso, Finset.mem_filter, Finset.mem_univ, true_and] at hc
          have hc_lt := c.isLt
          have hlt : (c.val - m0) / 3 < kR + kB := by dsimp only [m] at hc_lt; omega
          exact ⟨⟨(c.val - m0) / 3 - kR, by omega⟩, Fin.ext (by dsimp only; omega)⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le pairedTypes (B_iso.image (profC H R))
    have h3 : pairedTypes.card ≤ s := by
      calc pairedTypes.card ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
        _ = s := by simp
    have h4 : (B_iso.image (profC H R)).card ≤ B_iso.card := Finset.card_image_le
    dsimp only [kB] at hle_iso; omega
  have hcl : ∀ a ∈ coreR H R B, ∀ b ∈ coreR H R B,
      ∀ x ∈ coreC H R B, ∀ y ∈ coreC H R B,
        H a x = false → H b x = false → H b y = false → H a y = false := by
    intro a ha b hb x hx y hy hax hbx hby
    have hlt2 : ∀ u ∈ coreR H R B, u.val < 2 := by
      intro u hu
      rcases (Finset.mem_filter.mp hu).2 with ⟨c, hcB, huc⟩
      have huR := (Finset.mem_filter.mp hu).1
      simp only [R, B, Finset.mem_filter, Finset.mem_univ, true_and] at huR hcB
      rcases huR with hu2 | hu_iso
      · exact hu2
      · exfalso
        dsimp only [H] at huc
        have h1 : ¬ (u.val < 2 ∧ c.val < m0) := by dsimp only [n0] at hu_iso; omega
        have h2 : ¬ (2 ≤ u.val ∧ u.val < n0 ∧ c.val < m0) := by omega
        by_cases hcm : m0 ≤ c.val
        · have h3 : n0 ≤ u.val ∧ m0 ≤ c.val := ⟨hu_iso.1, hcm⟩
          simp only [h1, h2, h3, and_self, ↓reduceIte, decide_eq_true_eq] at huc
          rcases hcB with hc_lt | hc_iso <;> omega
        · have h3 : ¬ (n0 ≤ u.val ∧ m0 ≤ c.val) := by omega
          simp only [h1, h2, h3, ↓reduceIte] at huc; cases huc
    have hltm : ∀ v ∈ coreC H R B, v.val < m0 := by
      intro v hv
      rcases (Finset.mem_filter.mp hv).2 with ⟨u, huR, huv⟩
      have hvB := (Finset.mem_filter.mp hv).1
      have hu1 : u ∈ coreR H R B := Finset.mem_filter.mpr ⟨huR, v, hvB, huv⟩
      have hu2 := hlt2 u hu1
      by_contra hge
      dsimp only [H] at huv
      have h1 : ¬ (u.val < 2 ∧ v.val < m0) := by omega
      have h2 : ¬ (2 ≤ u.val ∧ u.val < n0 ∧ v.val < m0) := by omega
      have h3 : ¬ (n0 ≤ u.val ∧ m0 ≤ v.val) := by dsimp only [n0]; omega
      simp only [h1, h2, h3, ↓reduceIte] at huv; cases huv
    have ha2 := hlt2 a ha; have hb2 := hlt2 b hb; have hxm := hltm x hx; have hym := hltm y hy
    have hxlt2 : x.val / s < 2 := Nat.div_lt_of_lt_mul (by dsimp only [m0] at hxm; omega)
    have hylt2 : y.val / s < 2 := Nat.div_lt_of_lt_mul (by dsimp only [m0] at hym; omega)
    have h1a : a.val < 2 ∧ x.val < m0 := ⟨ha2, hxm⟩
    have h1b : b.val < 2 ∧ x.val < m0 := ⟨hb2, hxm⟩
    have h2a : a.val < 2 ∧ y.val < m0 := ⟨ha2, hym⟩
    have h2b : b.val < 2 ∧ y.val < m0 := ⟨hb2, hym⟩
    dsimp only [H] at hax hbx hby ⊢
    simp only [h1a, and_self, ↓reduceIte, decide_eq_false_iff_not] at hax
    simp only [h1b, and_self, ↓reduceIte, decide_eq_false_iff_not] at hbx
    simp only [h2b, and_self, ↓reduceIte, decide_eq_false_iff_not] at hby
    simp only [h2a, and_self, ↓reduceIte, decide_eq_false_iff_not]
    generalize x.val / s = qx at hxlt2 hax hbx
    generalize y.val / s = qy at hylt2 hby ⊢
    omega
  refine ⟨n, m, H, R, B, ?_, by change R.card + B.card = 2 * t + s + 1; omega⟩
  exact ⟨hdegR, hdegC, hc4, htypesR, htypesC, hcl⟩

lemma to_admissible_true {d t n m : ℕ} {G : Fin n → Fin m → Bool} {edge : Bool}
    {R : Finset (Fin n)} {B : Finset (Fin m)}
    (h1 : ∀ a, 2 ≤ (Finset.univ.filter (fun dest : Fin m => G a dest = edge)).card ∧
               (Finset.univ.filter (fun dest : Fin m => G a dest = edge)).card ≤ d)
    (h2 : ∀ c, 2 ≤ (Finset.univ.filter (fun src : Fin n => G src c = edge)).card ∧
               (Finset.univ.filter (fun src : Fin n => G src c = edge)).card ≤ d)
    (h3 : ∀ a b, a ≠ b →
      ((Finset.univ.filter (fun dest : Fin m => G a dest = edge)) ∩
       (Finset.univ.filter (fun dest : Fin m => G b dest = edge))).card ≤ 1)
    (h4 : (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤ t)
    (h5 : (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤ t)
    (h6 : ∀ a ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ !edge),
          ∀ b ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ !edge),
          ∀ x ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ !edge),
          ∀ y ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ !edge),
            G a x ≠ edge → G b x ≠ edge → G b y ≠ edge → G a y ≠ edge) :
    AdmissibleTrue d t n m (fun a c => decide (G a c = edge)) R B := by
  let H : Fin n → Fin m → Bool := fun a c => decide (G a c = edge)
  have hcard_compR : (R.image (profR H B)).card =
      (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card := by
    cases edge
    · let comp : Finset (Fin m) → Finset (Fin m) := fun S => (Finset.univ \ B) \ S
      have hcomp_eq : R.image (profR H B) =
          (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).image comp := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro a _
        ext c
        simp only [profR, H, comp, Function.comp_apply, Finset.mem_filter, Finset.mem_sdiff,
                   Finset.mem_univ, true_and, decide_eq_true_eq]
        cases G a c <;> simp
      rw [hcomp_eq]
      apply Finset.card_image_of_injOn
      intro S1 hS1 S2 hS2 heq
      rcases Finset.mem_image.mp hS1 with ⟨a1, _, rfl⟩
      rcases Finset.mem_image.mp hS2 with ⟨a2, _, rfl⟩
      ext c
      have hc := Finset.ext_iff.mp heq c
      simp only [comp, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      by_cases hcB : c ∈ B
      · simp [hcB]
      · simp only [hcB, not_false_eq_true, true_and] at hc ⊢
        tauto
    · apply congrArg Finset.card
      apply Finset.image_congr
      intro a _; ext c; simp [profR, H]
  have hcard_compC : (B.image (profC H R)).card =
      (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card := by
    cases edge
    · let comp : Finset (Fin n) → Finset (Fin n) := fun S => (Finset.univ \ R) \ S
      have hcomp_eq : B.image (profC H R) =
          (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).image comp := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro c _
        ext a
        simp only [profC, H, comp, Function.comp_apply, Finset.mem_filter, Finset.mem_sdiff,
                   Finset.mem_univ, true_and, decide_eq_true_eq]
        cases G a c <;> simp
      rw [hcomp_eq]
      apply Finset.card_image_of_injOn
      intro S1 hS1 S2 hS2 heq
      rcases Finset.mem_image.mp hS1 with ⟨c1, _, rfl⟩
      rcases Finset.mem_image.mp hS2 with ⟨c2, _, rfl⟩
      ext a
      have ha := Finset.ext_iff.mp heq a
      simp only [comp, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      by_cases haR : a ∈ R
      · simp [haR]
      · simp only [haR, not_false_eq_true, true_and] at ha ⊢
        tauto
    · apply congrArg Finset.card
      apply Finset.image_congr
      intro c _; ext a; simp [profC, H]
  refine ⟨?_, ?_, ?_, by rw [hcard_compR]; exact h4, by rw [hcard_compC]; exact h5, ?_⟩
  · intro a; simpa [nbrR, H] using h1 a
  · intro c; simpa [nbrC, H] using h2 c
  · intro a b hab; simpa [nbrR, H] using h3 a b hab
  · intro a ha b hb x hx y hy hax hbx hby
    have hcoreR_eq : coreR H R B = R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ !edge) := by
      ext r; simp only [coreR, H, Finset.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨hr, w, hw, heq⟩; refine ⟨hr, w, hw, ?_⟩
        rw [heq]; cases edge <;> decide
      · rintro ⟨hr, w, hw, hne⟩; refine ⟨hr, w, hw, ?_⟩
        cases edge <;> cases hgw : G r w <;> simp [hgw] at hne ⊢
    have hcoreC_eq : coreC H R B = B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ !edge) := by
      ext c; simp only [coreC, H, Finset.mem_filter, decide_eq_true_eq]
      constructor
      · rintro ⟨hc, w, hw, heq⟩; refine ⟨hc, w, hw, ?_⟩
        rw [heq]; cases edge <;> decide
      · rintro ⟨hc, w, hw, hne⟩; refine ⟨hc, w, hw, ?_⟩
        cases edge <;> cases hgw : G w c <;> simp [hgw] at hne ⊢
    rw [hcoreR_eq] at ha hb
    rw [hcoreC_eq] at hx hy
    simp only [decide_eq_false_iff_not] at hax hbx hby ⊢
    exact h6 a ha b hb x hx y hy hax hbx hby

lemma from_admissible_true {d t n m : ℕ} {H : Fin n → Fin m → Bool} (edge : Bool)
    {R : Finset (Fin n)} {B : Finset (Fin m)} (h : AdmissibleTrue d t n m H R B) :
    let G : Fin n → Fin m → Bool := fun a c => if edge then H a c else !(H a c)
    (∀ a, 2 ≤ (Finset.univ.filter (fun dest : Fin m => G a dest = edge)).card ∧
          (Finset.univ.filter (fun dest : Fin m => G a dest = edge)).card ≤ d) ∧
    (∀ c, 2 ≤ (Finset.univ.filter (fun src : Fin n => G src c = edge)).card ∧
          (Finset.univ.filter (fun src : Fin n => G src c = edge)).card ≤ d) ∧
    (∀ a b, a ≠ b →
      ((Finset.univ.filter (fun dest : Fin m => G a dest = edge)) ∩
       (Finset.univ.filter (fun dest : Fin m => G b dest = edge))).card ≤ 1) ∧
    (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤ t ∧
    (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤ t ∧
    (∀ a ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ !edge),
     ∀ b ∈ R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ !edge),
     ∀ x ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ !edge),
     ∀ y ∈ B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ !edge),
       G a x ≠ edge → G b x ≠ edge → G b y ≠ edge → G a y ≠ edge) := by
  intro G
  have hGe : ∀ a c, (G a c = edge) ↔ (H a c = true) := by
    intro a c; dsimp only [G]; cases edge <;> cases H a c <;> simp
  have hGne : ∀ a c, (G a c ≠ !edge) ↔ (H a c = true) := by
    intro a c; dsimp only [G]; cases edge <;> cases H a c <;> simp
  have hcardR : (R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))).card ≤
      (R.image (profR H B)).card := by
    cases edge
    · let comp : Finset (Fin m) → Finset (Fin m) := fun S => (Finset.univ \ B) \ S
      have hcomp_eq : R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true)) =
          (R.image (profR H B)).image comp := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro a _; ext c
        simp only [G, comp, Function.comp_apply, Bool.false_eq_true, ↓reduceIte,
                   Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, profR]
        cases H a c <;> simp
      rw [hcomp_eq]; exact Finset.card_image_le
    · have heq : R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true)) =
          R.image (profR H B) := by
        apply Finset.image_congr; intro a _; ext c; simp [G, profR]
      rw [heq]
  have hcardC : (B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))).card ≤
      (B.image (profC H R)).card := by
    cases edge
    · let comp : Finset (Fin n) → Finset (Fin n) := fun S => (Finset.univ \ R) \ S
      have hcomp_eq : B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true)) =
          (B.image (profC H R)).image comp := by
        rw [Finset.image_image]
        apply Finset.image_congr
        intro c _; ext a
        simp only [G, comp, Function.comp_apply, Bool.false_eq_true, ↓reduceIte,
                   Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, profC]
        cases H a c <;> simp
      rw [hcomp_eq]; exact Finset.card_image_le
    · have heq : B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true)) =
          B.image (profC H R) := by
        apply Finset.image_congr; intro c _; ext a; simp [G, profC]
      rw [heq]
  refine ⟨?_, ?_, ?_, Nat.le_trans hcardR h.typesR, Nat.le_trans hcardC h.typesC, ?_⟩
  · intro a; simpa [nbrR, hGe] using h.degR a
  · intro c; simpa [nbrC, hGe] using h.degC c
  · intro a b hab; simpa [nbrR, hGe] using h.c4R a b hab
  · intro a ha b hb x hx y hy hax hbx hby
    have hcoreR_eq : R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ !edge) = coreR H R B := by
      ext r; simp [coreR, hGne]
    have hcoreC_eq : B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ !edge) = coreC H R B := by
      ext c; simp [coreC, hGne]
    rw [hcoreR_eq] at ha hb; rw [hcoreC_eq] at hx hy
    have hf : ∀ u v, G u v ≠ edge → H u v = false := by
      intro u v hne; cases hv : H u v
      · rfl
      · exact False.elim (hne ((hGe u v).mpr hv))
    have hay := h.closure a ha b hb x hx y hy (hf a x hax) (hf b x hbx) (hf b y hby)
    intro heq
    have htr := (hGe a y).mp heq
    rw [hay] at htr; cases htr

end PEqualNP.Outside.L_meta_25613_aux

theorem PEqualNP.Outside.L_meta_25613 : ∀ (d t : ℕ), 2 ≤ d → 2 ≤ t →
  let cap := 2 * t + max 4 (min d t + 1)
  let admissible := fun (n m : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
      (R : Finset (Fin n)) (B : Finset (Fin m)) =>
    let nbrR := fun (row : Fin n) => Finset.univ.filter (fun dest : Fin m => G row dest = edge)
    let nbrC := fun (col : Fin m) => Finset.univ.filter (fun src : Fin n => G src col = edge)
    let rowTypes := R.image (fun inRow => (Finset.univ \ B).filter (fun outCol => G inRow outCol = true))
    let colTypes := B.image (fun inCol => (Finset.univ \ R).filter (fun outRow => G outRow inCol = true))
    let coreRows := fun (rowPol : Bool) => R.filter (fun keptRow => ∃ w ∈ B, G keptRow w ≠ rowPol)
    let coreCols := fun (colPol : Bool) => B.filter (fun keptCol => ∃ w ∈ R, G w keptCol ≠ colPol)
    (∀ a, 2 ≤ (nbrR a).card ∧ (nbrR a).card ≤ d) ∧
    (∀ c, 2 ≤ (nbrC c).card ∧ (nbrC c).card ≤ d) ∧
    (∀ a b, a ≠ b → ((nbrR a) ∩ (nbrR b)).card ≤ 1) ∧
    rowTypes.card ≤ t ∧ colTypes.card ≤ t ∧
    (∀ a ∈ coreRows (!edge), ∀ b ∈ coreRows (!edge),
      ∀ x ∈ coreCols (!edge), ∀ y ∈ coreCols (!edge),
        G a x ≠ edge → G b x ≠ edge → G b y ≠ edge → G a y ≠ edge)
  (∀ (n m : ℕ) (G : Fin n → Fin m → Bool) (edge : Bool)
      (R : Finset (Fin n)) (B : Finset (Fin m)),
    admissible n m G edge R B → R.card + B.card ≤ cap) ∧
  (∀ edge : Bool, ∃ (n m : ℕ) (G : Fin n → Fin m → Bool)
      (R : Finset (Fin n)) (B : Finset (Fin m)),
    admissible n m G edge R B ∧ R.card + B.card = cap) := by
  intro d t hd ht cap admissible
  constructor
  · intro n m G edge R B hadm
    rcases hadm with ⟨h1, h2, h3, h4, h5, h6⟩
    exact PEqualNP.Outside.L_meta_25613_aux.upper_bound_true
      (PEqualNP.Outside.L_meta_25613_aux.to_admissible_true h1 h2 h3 h4 h5 h6)
  · intro edge
    by_cases hcmp : min d t + 1 ≤ 4
    · rcases PEqualNP.Outside.L_meta_25613_aux.constr_c6 d t hd ht with ⟨n, m, H, R, B, hH, hcard⟩
      refine ⟨n, m, fun a c => if edge then H a c else !(H a c), R, B,
        PEqualNP.Outside.L_meta_25613_aux.from_admissible_true edge hH, ?_⟩
      dsimp only [cap]
      rw [Nat.max_eq_left hcmp]
      exact hcard
    · rcases PEqualNP.Outside.L_meta_25613_aux.constr_stars d t hd ht with ⟨n, m, H, R, B, hH, hcard⟩
      refine ⟨n, m, fun a c => if edge then H a c else !(H a c), R, B,
        PEqualNP.Outside.L_meta_25613_aux.from_admissible_true edge hH, ?_⟩
      dsimp only [cap]
      rw [Nat.max_eq_right (by omega : 4 ≤ min d t + 1)]
      omega
