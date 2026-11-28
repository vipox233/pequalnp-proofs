import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1125_aux

open Classical

section GraphParity

variable {n m : ℕ} (u v : Fin m → Fin n)

noncomputable def isClosedB (allowed : Finset (Fin m)) (C : Finset (Fin n)) : Bool :=
  allowed.toList.all (fun i => decide (u i ∈ C) == decide (v i ∈ C))

lemma isClosedB_iff (allowed : Finset (Fin m)) (C : Finset (Fin n)) :
    isClosedB u v allowed C = true ↔ ∀ i ∈ allowed, (u i ∈ C ↔ v i ∈ C) := by
  unfold isClosedB
  rw [List.all_eq_true]
  simp only [Finset.mem_toList, beq_iff_eq, decide_eq_decide]

noncomputable def comps (allowed : Finset (Fin m)) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun C =>
    C.Nonempty ∧ isClosedB u v allowed C = true ∧
      ∀ D ∈ C.powerset, D.Nonempty → isClosedB u v allowed D = true → D = C)

lemma closed_inter {allowed : Finset (Fin m)} {A B : Finset (Fin n)}
    (hA : isClosedB u v allowed A = true) (hB : isClosedB u v allowed B = true) :
    isClosedB u v allowed (A ∩ B) = true := by
  rw [isClosedB_iff] at hA hB ⊢
  intro i hi
  simp only [Finset.mem_inter]
  exact and_congr (hA i hi) (hB i hi)

lemma closed_sdiff {allowed : Finset (Fin m)} {A B : Finset (Fin n)}
    (hA : isClosedB u v allowed A = true) (hB : isClosedB u v allowed B = true) :
    isClosedB u v allowed (A \ B) = true := by
  rw [isClosedB_iff] at hA hB ⊢
  intro i hi
  simp only [Finset.mem_sdiff]
  exact and_congr (hA i hi) (not_congr (hB i hi))

lemma closed_univ (allowed : Finset (Fin m)) :
    isClosedB u v allowed Finset.univ = true := by
  rw [isClosedB_iff]; intro i _; simp

lemma closed_mono {a1 a2 : Finset (Fin m)} (h : a1 ⊆ a2) {C : Finset (Fin n)}
    (hc : isClosedB u v a2 C = true) : isClosedB u v a1 C = true := by
  rw [isClosedB_iff] at hc ⊢
  intro i hi; exact hc i (h hi)

lemma comps_disjoint {allowed : Finset (Fin m)} {C1 C2 : Finset (Fin n)}
    (h1 : C1 ∈ comps u v allowed) (h2 : C2 ∈ comps u v allowed) (hne : C1 ≠ C2) :
    Disjoint C1 C2 := by
  rw [Finset.disjoint_left]
  intro a ha1 ha2
  simp only [comps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset] at h1 h2
  have hcl : isClosedB u v allowed (C1 ∩ C2) = true := closed_inter u v h1.2.1 h2.2.1
  have hneI : (C1 ∩ C2).Nonempty := ⟨a, Finset.mem_inter.mpr ⟨ha1, ha2⟩⟩
  have e1 := h1.2.2 (C1 ∩ C2) Finset.inter_subset_left hneI hcl
  have e2 := h2.2.2 (C1 ∩ C2) Finset.inter_subset_right hneI hcl
  exact hne (e1.symm.trans e2)

lemma exists_comp_mem (allowed : Finset (Fin m)) (a : Fin n) :
    ∃ C ∈ comps u v allowed, a ∈ C := by
  let S : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun C => a ∈ C ∧ isClosedB u v allowed C = true)
  have hS : S.Nonempty := ⟨Finset.univ, by simp [S, closed_univ]⟩
  obtain ⟨C, hCmem, hCmin⟩ := Finset.exists_min_image S Finset.card hS
  simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hCmem
  refine ⟨C, ?_, hCmem.1⟩
  simp only [comps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
  refine ⟨⟨a, hCmem.1⟩, hCmem.2, fun D hDC hDne hDcl => ?_⟩
  by_cases haD : a ∈ D
  · have hDS : D ∈ S := by simp [S, haD, hDcl]
    have hle := hCmin D hDS
    exact Finset.eq_of_subset_of_card_le hDC hle
  · have hSD : C \ D ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Finset.mem_sdiff.mpr ⟨hCmem.1, haD⟩, closed_sdiff u v hCmem.2 hDcl⟩
    have hle := hCmin (C \ D) hSD
    rcases hDne with ⟨b, hb⟩
    have hlt : (C \ D).card < C.card := Finset.card_lt_card (Finset.sdiff_ssubset hDC ⟨b, hb⟩)
    omega

lemma comp_unique {allowed : Finset (Fin m)} {C1 C2 : Finset (Fin n)} {a : Fin n}
    (h1 : C1 ∈ comps u v allowed) (h2 : C2 ∈ comps u v allowed) (ha1 : a ∈ C1) (ha2 : a ∈ C2) :
    C1 = C2 := by
  by_contra hne
  exact Finset.disjoint_left.mp (comps_disjoint u v h1 h2 hne) ha1 ha2

lemma comp_subset_of_mem {a1 a2 : Finset (Fin m)} (hsub : a1 ⊆ a2)
    {C F : Finset (Fin n)} (hC : C ∈ comps u v a1) (hF : F ∈ comps u v a2)
    {a : Fin n} (haC : a ∈ C) (haF : a ∈ F) : C ⊆ F := by
  simp only [comps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset] at hC hF
  have hF1 : isClosedB u v a1 F = true := closed_mono u v hsub hF.2.1
  have hcl : isClosedB u v a1 (C ∩ F) = true := closed_inter u v hC.2.1 hF1
  have heq := hC.2.2 (C ∩ F) Finset.inter_subset_left ⟨a, Finset.mem_inter.mpr ⟨haC, haF⟩⟩ hcl
  rw [← heq]
  exact Finset.inter_subset_right

def bdy (x : Finset (Fin m)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j =>
    ((x.filter (fun i => u i = j)).card +
     (x.filter (fun i => v i = j)).card) % 2 = 1)

lemma card_symmDiff_mod2 {α : Type*} [DecidableEq α] (A B : Finset α) :
    (symmDiff A B).card % 2 = (A.card + B.card) % 2 := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 : A ∪ B = symmDiff A B ∪ (A ∩ B) := by
    ext x; simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]; tauto
  have h3 : Disjoint (symmDiff A B) (A ∩ B) := by
    rw [Finset.disjoint_left]; intro x; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
  rw [h2, Finset.card_union_of_disjoint h3] at h1
  omega

lemma bdy_empty : bdy u v ∅ = ∅ := by
  ext j; simp [bdy]

lemma bdy_symmDiff (x y : Finset (Fin m)) :
    bdy u v (symmDiff x y) = symmDiff (bdy u v x) (bdy u v y) := by
  ext j
  simp only [bdy, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
  have hf1 : (symmDiff x y).filter (fun i => u i = j) =
      symmDiff (x.filter (fun i => u i = j)) (y.filter (fun i => u i = j)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  have hf2 : (symmDiff x y).filter (fun i => v i = j) =
      symmDiff (x.filter (fun i => v i = j)) (y.filter (fun i => v i = j)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_symmDiff]; tauto
  rw [hf1, hf2]
  have c1 := card_symmDiff_mod2 (x.filter (fun i => u i = j)) (y.filter (fun i => u i = j))
  have c2 := card_symmDiff_mod2 (x.filter (fun i => v i = j)) (y.filter (fun i => v i = j))
  omega

lemma bdy_singleton (i : Fin m) : bdy u v {i} = symmDiff {u i} {v i} := by
  ext j
  simp only [bdy, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff, Finset.mem_singleton]
  have h1 : (({i} : Finset (Fin m)).filter (fun e => u e = j)).card = if u i = j then 1 else 0 := by
    by_cases h : u i = j
    · rw [if_pos h, Finset.filter_singleton, if_pos h, Finset.card_singleton]
    · rw [if_neg h, Finset.filter_singleton, if_neg h, Finset.card_empty]
  have h2 : (({i} : Finset (Fin m)).filter (fun e => v e = j)).card = if v i = j then 1 else 0 := by
    by_cases h : v i = j
    · rw [if_pos h, Finset.filter_singleton, if_pos h, Finset.card_singleton]
    · rw [if_neg h, Finset.filter_singleton, if_neg h, Finset.card_empty]
  rw [h1, h2]
  by_cases hu : u i = j <;> by_cases hv : v i = j <;>
    simp [hu, hv, Ne.symm, Eq.symm]

lemma card_bdy_inter_closed_even {allowed : Finset (Fin m)} {C : Finset (Fin n)}
    (hC : isClosedB u v allowed C = true) {y : Finset (Fin m)} (hy : y ⊆ allowed) :
    (bdy u v y ∩ C).card % 2 = 0 := by
  induction y using Finset.induction_on with
  | empty => simp [bdy_empty]
  | @insert i s hi ih =>
    have hsi : insert i s = symmDiff s {i} := by
      ext e; simp only [Finset.mem_insert, Finset.mem_symmDiff, Finset.mem_singleton]
      constructor
      · rintro (rfl | hs)
        · exact Or.inr ⟨rfl, hi⟩
        · exact Or.inl ⟨hs, fun h => hi (h ▸ hs)⟩
      · rintro (⟨hs, _⟩ | ⟨rfl, _⟩)
        · exact Or.inr hs
        · exact Or.inl rfl
    rw [hsi, bdy_symmDiff]
    have hinter : symmDiff (bdy u v s) (bdy u v {i}) ∩ C =
        symmDiff (bdy u v s ∩ C) (bdy u v {i} ∩ C) := by
      ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto
    rw [hinter, card_symmDiff_mod2]
    have hih := ih (Finset.Subset.trans (Finset.subset_insert i s) hy)
    have hiA : i ∈ allowed := hy (Finset.mem_insert_self i s)
    have huv : u i ∈ C ↔ v i ∈ C := (isClosedB_iff u v allowed C).mp hC i hiA
    have hev : (bdy u v {i} ∩ C).card % 2 = 0 := by
      rw [bdy_singleton]
      by_cases huc : u i ∈ C
      · have hvc : v i ∈ C := huv.mp huc
        by_cases heq : u i = v i
        · simp [heq]
        · have hs : symmDiff {u i} {v i} ∩ C = {u i, v i} := by
            ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
              Finset.mem_insert]
            constructor
            · rintro ⟨(⟨rfl, _⟩ | ⟨rfl, _⟩), _⟩ <;> simp
            · rintro (rfl | rfl)
              · exact ⟨Or.inl ⟨rfl, heq⟩, huc⟩
              · exact ⟨Or.inr ⟨rfl, Ne.symm heq⟩, hvc⟩
          rw [hs, Finset.card_pair heq]
      · have hvc : v i ∉ C := fun h => huc (huv.mpr h)
        have hs : symmDiff {u i} {v i} ∩ C = ∅ := by
          ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
            Finset.notMem_empty, iff_false]
          rintro ⟨(⟨rfl, _⟩ | ⟨rfl, _⟩), hj⟩
          · exact huc hj
          · exact hvc hj
        rw [hs]; simp
    omega

lemma comp_reachable {allowed : Finset (Fin m)} {C : Finset (Fin n)}
    (hC : C ∈ comps u v allowed) {a b : Fin n} (ha : a ∈ C) (hb : b ∈ C) :
    ∃ y ⊆ allowed, bdy u v y = symmDiff {a} {b} := by
  let R : Finset (Fin n) := C.filter (fun x => ∃ y ⊆ allowed, bdy u v y = symmDiff {a} {x})
  have haR : a ∈ R := by
    simp only [R, Finset.mem_filter]
    exact ⟨ha, ∅, Finset.empty_subset _, by simp [bdy_empty]⟩
  have hRsub : R ⊆ C := Finset.filter_subset _ _
  simp only [comps, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset] at hC
  have hRcl : isClosedB u v allowed R = true := by
    rw [isClosedB_iff]
    intro i hi
    have hCuv : u i ∈ C ↔ v i ∈ C := (isClosedB_iff u v allowed C).mp hC.2.1 i hi
    simp only [R, Finset.mem_filter]
    constructor
    · rintro ⟨huC, y, hy, hby⟩
      refine ⟨hCuv.mp huC, symmDiff y {i}, ?_, ?_⟩
      · intro e he
        simp only [Finset.mem_symmDiff, Finset.mem_singleton] at he
        rcases he with ⟨hey, _⟩ | ⟨rfl, _⟩
        · exact hy hey
        · exact hi
      · rw [bdy_symmDiff, hby, bdy_singleton]
        ext j; simp only [Finset.mem_symmDiff, Finset.mem_singleton]; tauto
    · rintro ⟨hvC, y, hy, hby⟩
      refine ⟨hCuv.mpr hvC, symmDiff y {i}, ?_, ?_⟩
      · intro e he
        simp only [Finset.mem_symmDiff, Finset.mem_singleton] at he
        rcases he with ⟨hey, _⟩ | ⟨rfl, _⟩
        · exact hy hey
        · exact hi
      · rw [bdy_symmDiff, hby, bdy_singleton]
        ext j; simp only [Finset.mem_symmDiff, Finset.mem_singleton]; tauto
  have hReq : R = C := hC.2.2 R hRsub ⟨a, haR⟩ hRcl
  have hbR : b ∈ R := hReq ▸ hb
  exact (Finset.mem_filter.mp hbR).2

lemma exists_bdy_iff (allowed : Finset (Fin m)) (e : Finset (Fin n)) :
    (∃ y ⊆ allowed, bdy u v y = e) ↔ ∀ C ∈ comps u v allowed, (e ∩ C).card % 2 = 0 := by
  constructor
  · rintro ⟨y, hy, rfl⟩ C hC
    simp only [comps, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    exact card_bdy_inter_closed_even u v hC.2.1 hy
  · intro heven
    suffices h : ∀ k : ℕ, ∀ e : Finset (Fin n), e.card ≤ k →
        (∀ C ∈ comps u v allowed, (e ∩ C).card % 2 = 0) → ∃ y ⊆ allowed, bdy u v y = e from
      h e.card e le_rfl heven
    intro k
    induction k with
    | zero =>
      intro e he _
      have he0 : e = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero he)
      subst he0; exact ⟨∅, Finset.empty_subset _, bdy_empty u v⟩
    | succ k ih =>
      intro e he hce
      by_cases hemp : e = ∅
      · subst hemp; exact ⟨∅, Finset.empty_subset _, bdy_empty u v⟩
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
        obtain ⟨C, hC, haC⟩ := exists_comp_mem u v allowed a
        have hpos : 0 < (e ∩ C).card := Finset.card_pos.mpr ⟨a, Finset.mem_inter.mpr ⟨ha, haC⟩⟩
        have hevC := hce C hC
        have hge2 : 1 < (e ∩ C).card := by omega
        obtain ⟨b, hbIC, hba⟩ := Finset.exists_mem_ne hge2 a
        have hb : b ∈ e := (Finset.mem_inter.mp hbIC).1
        have hbC : b ∈ C := (Finset.mem_inter.mp hbIC).2
        obtain ⟨y1, hy1, hby1⟩ := comp_reachable u v hC haC hbC
        let e' := (e.erase a).erase b
        have he'_eq : e' = symmDiff e (symmDiff {a} {b}) := by
          ext j
          simp only [e', Finset.mem_erase, Finset.mem_symmDiff, Finset.mem_singleton]
          constructor
          · rintro ⟨hjb, hja, hje⟩
            exact Or.inl ⟨hje, by tauto⟩
          · rintro (⟨hje, hnot⟩ | ⟨(⟨rfl, _⟩ | ⟨rfl, _⟩), hnot⟩)
            · refine ⟨?_, ?_, hje⟩
              · intro h; subst h; exact hnot (Or.inr ⟨rfl, hba⟩)
              · intro h; subst h; exact hnot (Or.inl ⟨rfl, Ne.symm hba⟩)
            · exact False.elim (hnot ha)
            · exact False.elim (hnot hb)
        have hcard' : e'.card ≤ k := by
          have hb_er : b ∈ e.erase a := Finset.mem_erase.mpr ⟨hba, hb⟩
          have h1 : e'.card + 1 = (e.erase a).card := Finset.card_erase_add_one hb_er
          have h2 : (e.erase a).card + 1 = e.card := Finset.card_erase_add_one ha
          omega
        have hce' : ∀ C' ∈ comps u v allowed, (e' ∩ C').card % 2 = 0 := by
          intro C' hC'
          rw [he'_eq]
          have hinter : symmDiff e (symmDiff {a} {b}) ∩ C' =
              symmDiff (e ∩ C') (symmDiff {a} {b} ∩ C') := by
            ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto
          rw [hinter, card_symmDiff_mod2]
          have h1 := hce C' hC'
          have h2 : (symmDiff {a} {b} ∩ C').card % 2 = 0 := by
            by_cases hEq : C' = C
            · rw [hEq]
              have hs : symmDiff {a} {b} ∩ C = {a, b} := by
                ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
                constructor
                · rintro ⟨(⟨rfl, _⟩ | ⟨rfl, _⟩), _⟩ <;> simp
                · rintro (rfl | rfl)
                  · exact ⟨Or.inl ⟨rfl, Ne.symm hba⟩, haC⟩
                  · exact ⟨Or.inr ⟨rfl, hba⟩, hbC⟩
              rw [hs, Finset.card_pair (Ne.symm hba)]
            · have hdisj := comps_disjoint u v hC hC' (Ne.symm hEq)
              have hs : symmDiff {a} {b} ∩ C' = ∅ := by
                ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton,
                  Finset.notMem_empty, iff_false]
                rintro ⟨(⟨rfl, _⟩ | ⟨rfl, _⟩), hj⟩
                · exact Finset.disjoint_left.mp hdisj haC hj
                · exact Finset.disjoint_left.mp hdisj hbC hj
              rw [hs]; simp
          omega
        obtain ⟨y2, hy2, hby2⟩ := ih e' hcard' hce'
        refine ⟨symmDiff y1 y2, ?_, ?_⟩
        · intro x hx
          simp only [Finset.mem_symmDiff] at hx
          rcases hx with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact hy1 h1
          · exact hy2 h2
        · rw [bdy_symmDiff, hby1, hby2, he'_eq]
          ext j
          by_cases hj1 : j ∈ e <;> by_cases hj2 : j ∈ symmDiff ({a} : Finset (Fin n)) {b} <;>
            simp [Finset.mem_symmDiff, hj1, hj2]

lemma part1 (T : Finset (Fin m)) (d : Finset (Fin n)) (z : Finset (Fin m)) (hz : z ⊆ T) :
    z ∈ ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bdy u v x = d)).image (fun x => x ∩ T) ↔
      ∀ C ∈ comps u v (Finset.univ \ T), (d ∩ C).card % 2 = (bdy u v z ∩ C).card % 2 := by
  have hiff1 : z ∈ ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bdy u v x = d)).image (fun x => x ∩ T) ↔
      ∃ y ⊆ Finset.univ \ T, bdy u v y = symmDiff d (bdy u v z) := by
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hbx, hxT⟩
      refine ⟨x \ T, fun i hi => Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩, ?_⟩
      have hxs : x \ T = symmDiff x z := by
        ext i; simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
        rw [← hxT, Finset.mem_inter]
        tauto
      rw [hxs, bdy_symmDiff, hbx]
    · rintro ⟨y, hy, hby⟩
      refine ⟨symmDiff y z, ?_, ?_⟩
      · rw [bdy_symmDiff, hby]
        ext j; simp only [Finset.mem_symmDiff]; tauto
      · ext i
        simp only [Finset.mem_inter, Finset.mem_symmDiff]
        constructor
        · rintro ⟨(⟨hiy, _⟩ | ⟨hiz, _⟩), hiT⟩
          · exact False.elim ((Finset.mem_sdiff.mp (hy hiy)).2 hiT)
          · exact hiz
        · intro hiz
          refine ⟨Or.inr ⟨hiz, fun hiy => (Finset.mem_sdiff.mp (hy hiy)).2 (hz hiz)⟩, hz hiz⟩
  rw [hiff1, exists_bdy_iff u v (Finset.univ \ T) (symmDiff d (bdy u v z))]
  apply forall₂_congr; intro C _
  have hinter : symmDiff d (bdy u v z) ∩ C = symmDiff (d ∩ C) (bdy u v z ∩ C) := by
    ext j; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto
  rw [hinter, card_symmDiff_mod2]
  omega

lemma card_bdy_eq_sum_sub {a1 a2 : Finset (Fin m)} (hsub : a1 ⊆ a2)
    {F : Finset (Fin n)} (hF : F ∈ comps u v a2) (d : Finset (Fin n)) :
    (d ∩ F).card = ∑ C ∈ (comps u v a1).filter (fun C => C ⊆ F), (d ∩ C).card := by
  have hunion : F = ((comps u v a1).filter (fun C => C ⊆ F)).biUnion id := by
    ext a
    simp only [Finset.mem_biUnion, Finset.mem_filter, id_eq]
    constructor
    · intro haF
      obtain ⟨C, hC, haC⟩ := exists_comp_mem u v a1 a
      exact ⟨C, ⟨hC, comp_subset_of_mem u v hsub hC hF haC haF⟩, haC⟩
    · rintro ⟨C, ⟨_, hCF⟩, haC⟩
      exact hCF haC
  have hdF : d ∩ F = ((comps u v a1).filter (fun C => C ⊆ F)).biUnion (fun C => d ∩ C) := by
    conv_lhs => rw [hunion]
    ext a; simp only [Finset.mem_inter, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨had, C, hC, haC⟩; exact ⟨C, hC, had, haC⟩
    · rintro ⟨C, hC, had, haC⟩; exact ⟨had, C, hC, haC⟩
  rw [hdF, Finset.card_biUnion]
  intro C1 hC1 C2 hC2 hne
  have h1 := (Finset.mem_filter.mp hC1).1
  have h2 := (Finset.mem_filter.mp hC2).1
  exact (comps_disjoint u v h1 h2 hne).mono Finset.inter_subset_right Finset.inter_subset_right

lemma support_image_card (T : Finset (Fin m)) :
    let full := comps u v Finset.univ
    let cut := comps u v (Finset.univ \ T)
    let support := fun (d : Finset (Fin n)) =>
      ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => bdy u v x = d)).image (fun x => x ∩ T)
    ((Finset.univ : Finset (Finset (Fin n))).image support).card =
      2 ^ (cut.card - full.card) + (if n = 0 then 0 else 1) := by
  intro full cut support
  have hsubT : Finset.univ \ T ⊆ (Finset.univ : Finset (Fin m)) := Finset.subset_univ _
  let sig (d : Finset (Fin n)) : {C // C ∈ cut} → Bool :=
    fun C => decide ((d ∩ C.val).card % 2 = 1)
  let EvenSig : Finset ({C // C ∈ cut} → Bool) :=
    Finset.univ.filter (fun σ => ∀ F ∈ full,
      ((Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F ∧ σ C = true)).card % 2 = 0)
  have hsig_even_iff : ∀ d : Finset (Fin n),
      sig d ∈ EvenSig ↔ ∀ F ∈ full, (d ∩ F).card % 2 = 0 := by
    intro d
    simp only [EvenSig, Finset.mem_filter, Finset.mem_univ, true_and]
    apply forall₂_congr; intro F hF
    have hsum := card_bdy_eq_sum_sub u v hsubT hF d
    have hmod_sum : (∑ C ∈ cut.filter (fun C => C ⊆ F), (d ∩ C).card) % 2 =
        (∑ C ∈ cut.filter (fun C => C ⊆ F), (d ∩ C).card % 2) % 2 := by
      rw [Finset.sum_nat_mod]
    have hcnt : ∑ C ∈ cut.filter (fun C => C ⊆ F), (d ∩ C).card % 2 =
        ((Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F ∧ sig d C = true)).card := by
      have h1 : ∑ C ∈ cut.filter (fun C => C ⊆ F), (d ∩ C).card % 2 =
          (cut.filter (fun C => C ⊆ F ∧ (d ∩ C).card % 2 = 1)).card := by
        rw [Finset.card_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl; intro C _
        by_cases hCF : C ⊆ F
        · simp only [hCF, ↓reduceIte, true_and]
          have h2 : (d ∩ C).card % 2 < 2 := Nat.mod_lt _ (by omega)
          by_cases hm : (d ∩ C).card % 2 = 1 <;> simp [hm] <;> omega
        · simp [hCF]
      rw [h1]
      refine Finset.card_bij (fun C hC => ⟨C, (Finset.mem_filter.mp hC).1⟩) ?_ ?_ ?_
      · intro C hC
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sig, decide_eq_true_eq] at hC ⊢
        exact hC.2
      · intro C1 _ C2 _ h; exact congrArg Subtype.val h
      · intro C hC
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, sig, decide_eq_true_eq] at hC
        exact ⟨C.val, Finset.mem_filter.mpr ⟨C.property, hC⟩, Subtype.ext rfl⟩
    rw [hsum, hmod_sum, hcnt]
  have hnonempty_iff : ∀ d : Finset (Fin n), (support d).Nonempty ↔ sig d ∈ EvenSig := by
    intro d
    rw [hsig_even_iff]
    constructor
    · rintro ⟨z, hz⟩
      simp only [support, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rcases hz with ⟨x, hbx, _⟩
      exact (exists_bdy_iff u v Finset.univ d).mp ⟨x, Finset.subset_univ _, hbx⟩
    · intro hev
      obtain ⟨x, _, hbx⟩ := (exists_bdy_iff u v Finset.univ d).mpr hev
      exact ⟨x ∩ T, Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbx⟩, rfl⟩⟩
  have hrep_sig : ∀ σ : {C // C ∈ cut} → Bool, ∃ d : Finset (Fin n), sig d = σ := by
    intro σ
    have hne : ∀ C : {C // C ∈ cut}, C.val.Nonempty := fun C =>
      (Finset.mem_filter.mp C.property).2.1
    let pick (C : {C // C ∈ cut}) : Fin n := (hne C).choose
    have hpick_mem : ∀ C : {C // C ∈ cut}, pick C ∈ C.val := fun C => (hne C).choose_spec
    let d : Finset (Fin n) :=
      ((Finset.univ : Finset {C // C ∈ cut}).filter (fun C => σ C = true)).image pick
    refine ⟨d, ?_⟩
    funext C
    have hinter : d ∩ C.val = if σ C = true then {pick C} else ∅ := by
      ext a
      simp only [d, Finset.mem_inter, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with hσ
      · rw [Finset.mem_singleton]
        constructor
        · rintro ⟨⟨C', _, rfl⟩, haC⟩
          have heq := comp_unique u v C'.property C.property (hpick_mem C') haC
          have : C' = C := Subtype.ext heq
          rw [this]
        · rintro rfl; exact ⟨⟨C, hσ, rfl⟩, hpick_mem C⟩
      · simp only [Finset.notMem_empty, iff_false]
        rintro ⟨⟨C', hσ', rfl⟩, haC⟩
        have heq := comp_unique u v C'.property C.property (hpick_mem C') haC
        have : C' = C := Subtype.ext heq
        rw [this] at hσ'; exact hσ hσ'
    simp only [sig, hinter]
    cases hσ : σ C <;> simp
  have hsupp_eq_iff : ∀ d1 d2 : Finset (Fin n),
      sig d1 ∈ EvenSig → sig d2 ∈ EvenSig → (support d1 = support d2 ↔ sig d1 = sig d2) := by
    intro d1 d2 h1 h2
    constructor
    · intro heq
      obtain ⟨z, hz1⟩ := (hnonempty_iff d1).mpr h1
      have hz2 : z ∈ support d2 := heq ▸ hz1
      have hzT : z ⊆ T := by
        simp only [support, Finset.mem_image] at hz1
        rcases hz1 with ⟨x, _, rfl⟩; exact Finset.inter_subset_right
      have hp1 := (part1 u v T d1 z hzT).mp hz1
      have hp2 := (part1 u v T d2 z hzT).mp hz2
      funext C
      have hc1 := hp1 C.val C.property
      have hc2 := hp2 C.val C.property
      simp only [sig]
      rw [hc1, ← hc2]
    · intro hsig
      ext z
      by_cases hzT : z ⊆ T
      · rw [part1 u v T d1 z hzT, part1 u v T d2 z hzT]
        apply forall₂_congr; intro C hC
        have hCeq := congrFun hsig ⟨C, hC⟩
        simp only [sig, decide_eq_decide] at hCeq
        have hm1 : (d1 ∩ C).card % 2 < 2 := Nat.mod_lt _ (by omega)
        have hm2 : (d2 ∩ C).card % 2 < 2 := Nat.mod_lt _ (by omega)
        have heq : (d1 ∩ C).card % 2 = (d2 ∩ C).card % 2 := by
          by_cases h : (d1 ∩ C).card % 2 = 1
          · rw [h, hCeq.mp h]
          · have h0 : (d1 ∩ C).card % 2 = 0 := by omega
            have h0' : (d2 ∩ C).card % 2 = 0 := by
              by_contra hne; have : (d2 ∩ C).card % 2 = 1 := by omega
              exact h (hCeq.mpr this)
            omega
        rw [heq]
      · have hnot : ∀ d, z ∉ support d := by
          intro d hz
          simp only [support, Finset.mem_image] at hz
          rcases hz with ⟨x, _, rfl⟩
          exact hzT Finset.inter_subset_right
        simp [hnot]
  let Simg := (Finset.univ : Finset (Finset (Fin n))).image support
  let Snonempty := Simg.filter Finset.Nonempty
  have hSnonempty_card : Snonempty.card = EvenSig.card := by
    refine Finset.card_bij (fun s hs =>
      let d := (Finset.mem_image.mp (Finset.mem_filter.mp hs).1).choose
      sig d) ?_ ?_ ?_
    · intro s hs
      have hs1 := (Finset.mem_filter.mp hs).1
      have hs2 := (Finset.mem_filter.mp hs).2
      have hspec := (Finset.mem_image.mp hs1).choose_spec.2
      rw [← hnonempty_iff, hspec]
      exact hs2
    · intro s1 hs1 s2 hs2 hsig
      have h1a := (Finset.mem_image.mp (Finset.mem_filter.mp hs1).1).choose_spec.2
      have h2a := (Finset.mem_image.mp (Finset.mem_filter.mp hs2).1).choose_spec.2
      have hev1 : sig _ ∈ EvenSig := (hnonempty_iff _).mp (h1a.symm ▸ (Finset.mem_filter.mp hs1).2)
      have hev2 : sig _ ∈ EvenSig := (hnonempty_iff _).mp (h2a.symm ▸ (Finset.mem_filter.mp hs2).2)
      rw [← h1a, ← h2a]
      exact (hsupp_eq_iff _ _ hev1 hev2).mpr hsig
    · intro σ hσ
      obtain ⟨d, hd⟩ := hrep_sig σ
      have hne : (support d).Nonempty := (hnonempty_iff d).mpr (hd.symm ▸ hσ)
      have hmem : support d ∈ Snonempty :=
        Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩, hne⟩
      refine ⟨support d, hmem, ?_⟩
      have hspec := (Finset.mem_image.mp (Finset.mem_filter.mp hmem).1).choose_spec.2
      have hev1 : sig _ ∈ EvenSig := (hnonempty_iff _).mp (hspec.symm ▸ hne)
      have hev2 : sig d ∈ EvenSig := hd.symm ▸ hσ
      rw [← hd]
      exact (hsupp_eq_iff _ d hev1 hev2).mp hspec
  have hEven_card : EvenSig.card = 2 ^ (cut.card - full.card) := by
    have hsub_ne : ∀ F ∈ full, (cut.filter (fun C => C ⊆ F)).Nonempty := by
      intro F hF
      have hFne : F.Nonempty := (Finset.mem_filter.mp hF).2.1
      obtain ⟨a, haF⟩ := hFne
      obtain ⟨C, hC, haC⟩ := exists_comp_mem u v (Finset.univ \ T) a
      exact ⟨C, Finset.mem_filter.mpr ⟨hC, comp_subset_of_mem u v hsubT hC hF haC haF⟩⟩
    let lead (F : {F // F ∈ full}) : {C // C ∈ cut} :=
      let C := (hsub_ne F.val F.property).choose
      ⟨C, (Finset.mem_filter.mp (hsub_ne F.val F.property).choose_spec).1⟩
    have hlead_sub : ∀ F : {F // F ∈ full}, (lead F).val ⊆ F.val := fun F =>
      (Finset.mem_filter.mp (hsub_ne F.val F.property).choose_spec).2
    have hlead_inj : Function.Injective lead := by
      intro F1 F2 heq
      have hCne : (lead F1).val.Nonempty := (Finset.mem_filter.mp (lead F1).property).2.1
      obtain ⟨a, ha⟩ := hCne
      have ha1 : a ∈ F1.val := hlead_sub F1 ha
      have ha2 : a ∈ F2.val := hlead_sub F2 (heq ▸ ha)
      exact Subtype.ext (comp_unique u v F1.property F2.property ha1 ha2)
    let leads : Finset {C // C ∈ cut} := Finset.univ.image lead
    let free : Finset {C // C ∈ cut} := Finset.univ \ leads
    have hfree_card : free.card = cut.card - full.card := by
      have h1 : leads.card = full.card := by
        rw [Finset.card_image_of_injective _ hlead_inj, Finset.card_univ, Fintype.card_coe]
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_coe, h1]
    have hbij : EvenSig.card = Fintype.card ({C // C ∈ free} → Bool) := by
      let toFree (σ : {C // C ∈ cut} → Bool) : {C // C ∈ free} → Bool := fun C => σ C.val
      have hinj : ∀ σ1 ∈ EvenSig, ∀ σ2 ∈ EvenSig, toFree σ1 = toFree σ2 → σ1 = σ2 := by
        intro σ1 h1 σ2 h2 htf
        funext C
        by_cases hCfree : C ∈ free
        · exact congrFun htf ⟨C, hCfree⟩
        · have hClead : C ∈ leads := by
            simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hCfree
            exact hCfree
          obtain ⟨F, _, rfl⟩ := Finset.mem_image.mp hClead
          simp only [EvenSig, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
          have hf1 := h1 F.val F.property
          have hf2 := h2 F.val F.property
          let rest := (Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F.val ∧ C ≠ lead F)
          have hsame : ∀ C ∈ rest, σ1 C = σ2 C := by
            intro C hCr
            have hneL : C ≠ lead F := (Finset.mem_filter.mp hCr).2.2
            have hsubF : C.val ⊆ F.val := (Finset.mem_filter.mp hCr).2.1
            have hnotL : C ∉ leads := by
              intro hL
              obtain ⟨F', _, hF'⟩ := Finset.mem_image.mp hL
              have hCne : C.val.Nonempty := (Finset.mem_filter.mp C.property).2.1
              obtain ⟨a, ha⟩ := hCne
              have haF : a ∈ F.val := hsubF ha
              have haF' : a ∈ F'.val := hlead_sub F' (hF'.symm ▸ ha)
              have heqF : F' = F := Subtype.ext (comp_unique u v F'.property F.property haF' haF)
              exact hneL (hF'.symm.trans (congrArg lead heqF))
            exact congrFun htf ⟨C, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotL⟩⟩
          have hsplit : ∀ σ : {C // C ∈ cut} → Bool,
              ((Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F.val ∧ σ C = true)).card =
                (if σ (lead F) = true then 1 else 0) + (rest.filter (fun C => σ C = true)).card := by
            intro σ
            have heq : (Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F.val ∧ σ C = true) =
                (if σ (lead F) = true then {lead F} else ∅) ∪ rest.filter (fun C => σ C = true) := by
              ext C; simp only [rest, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
              split_ifs with hL
              · simp only [Finset.mem_singleton]
                constructor
                · rintro ⟨hsub, hσ⟩
                  by_cases h : C = lead F
                  · exact Or.inl h
                  · exact Or.inr ⟨⟨hsub, h⟩, hσ⟩
                · rintro (rfl | ⟨⟨hsub, _⟩, hσ⟩)
                  · exact ⟨hlead_sub F, hL⟩
                  · exact ⟨hsub, hσ⟩
              · simp only [Finset.notMem_empty, false_or]
                constructor
                · rintro ⟨hsub, hσ⟩
                  refine ⟨⟨hsub, ?_⟩, hσ⟩
                  intro h; rw [h] at hσ; exact hL hσ
                · rintro ⟨⟨hsub, _⟩, hσ⟩; exact ⟨hsub, hσ⟩
            rw [heq, Finset.card_union_of_disjoint]
            · split_ifs <;> simp
            · split_ifs
              · rw [Finset.disjoint_singleton_left]
                simp [rest]
              · exact Finset.disjoint_empty_left _
          have hrest_eq : rest.filter (fun C => σ1 C = true) = rest.filter (fun C => σ2 C = true) :=
            Finset.filter_congr (fun C hC => by rw [hsame C hC])
          rw [hsplit σ1] at hf1
          rw [hsplit σ2, ← hrest_eq] at hf2
          cases h1v : σ1 (lead F) <;> cases h2v : σ2 (lead F)
          · rfl
          · simp only [h1v, h2v, Bool.false_eq_true, ↓reduceIte, zero_add] at hf1 hf2; omega
          · simp only [h1v, h2v, Bool.false_eq_true, ↓reduceIte, zero_add] at hf1 hf2; omega
          · rfl
      have hsurj : ∀ τ : {C // C ∈ free} → Bool, ∃ σ ∈ EvenSig, toFree σ = τ := by
        intro τ
        let σ : {C // C ∈ cut} → Bool := fun C =>
          if hC : C ∈ free then τ ⟨C, hC⟩
          else
            let F : {F // F ∈ full} := (Finset.mem_image.mp (by
              simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not] at hC; exact hC)).choose
            decide ((((Finset.univ : Finset {C // C ∈ cut}).filter (fun C' =>
              C'.val ⊆ F.val ∧ C' ≠ C)).filter (fun C' =>
                if h' : C' ∈ free then τ ⟨C', h'⟩ = true else false)).card % 2 = 1)
        refine ⟨σ, ?_, ?_⟩
        · simp only [EvenSig, Finset.mem_filter, Finset.mem_univ, true_and]
          intro F hF
          let Fsub : {F // F ∈ full} := ⟨F, hF⟩
          let rest := (Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F ∧ C ≠ lead Fsub)
          have hrest_free : ∀ C ∈ rest, C ∈ free := by
            intro C hCr
            rw [Finset.mem_sdiff]
            refine ⟨Finset.mem_univ _, fun hL => ?_⟩
            obtain ⟨F', _, hF'⟩ := Finset.mem_image.mp hL
            have hCne : C.val.Nonempty := (Finset.mem_filter.mp C.property).2.1
            obtain ⟨a, ha⟩ := hCne
            have haF : a ∈ F := (Finset.mem_filter.mp hCr).2.1 ha
            have haF' : a ∈ F'.val := hlead_sub F' (hF'.symm ▸ ha)
            have heqF : F' = Fsub := Subtype.ext (comp_unique u v F'.property hF haF' haF)
            exact (Finset.mem_filter.mp hCr).2.2 (hF'.symm.trans (congrArg lead heqF))
          have hnot_free : lead Fsub ∉ free := by
            simp only [free, Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
            exact Finset.mem_image.mpr ⟨Fsub, Finset.mem_univ _, rfl⟩
          have hlead_val : σ (lead Fsub) = decide ((rest.filter (fun C => σ C = true)).card % 2 = 1) := by
            dsimp only [σ]
            rw [dif_neg hnot_free]
            have hmemL : lead Fsub ∈ leads := Finset.mem_image.mpr ⟨Fsub, Finset.mem_univ _, rfl⟩
            have hFchoose : (Finset.mem_image.mp hmemL).choose = Fsub :=
              hlead_inj (Finset.mem_image.mp hmemL).choose_spec.2
            congr 1; congr 1
            have hfeq : (Finset.univ : Finset {C // C ∈ cut}).filter (fun C' =>
                C'.val ⊆ (Finset.mem_image.mp hmemL).choose.val ∧ C' ≠ lead Fsub) = rest := by
              rw [hFchoose]
            rw [hfeq]
            congr 1; congr 1
            apply Finset.filter_congr
            intro C hCr
            have hCf := hrest_free C hCr
            simp only [σ, hCf, ↓reduceDIte]
          have hsplit : ((Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F ∧ σ C = true)).card =
              (if σ (lead Fsub) = true then 1 else 0) + (rest.filter (fun C => σ C = true)).card := by
            have heq : (Finset.univ : Finset {C // C ∈ cut}).filter (fun C => C.val ⊆ F ∧ σ C = true) =
                (if σ (lead Fsub) = true then {lead Fsub} else ∅) ∪ rest.filter (fun C => σ C = true) := by
              ext C; simp only [rest, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
              split_ifs with hL
              · simp only [Finset.mem_singleton]
                constructor
                · rintro ⟨hsub, hσ⟩
                  by_cases h : C = lead Fsub
                  · exact Or.inl h
                  · exact Or.inr ⟨⟨hsub, h⟩, hσ⟩
                · rintro (rfl | ⟨⟨hsub, _⟩, hσ⟩)
                  · exact ⟨hlead_sub Fsub, hL⟩
                  · exact ⟨hsub, hσ⟩
              · simp only [Finset.notMem_empty, false_or]
                constructor
                · rintro ⟨hsub, hσ⟩
                  refine ⟨⟨hsub, ?_⟩, hσ⟩
                  intro h; rw [h] at hσ; exact hL hσ
                · rintro ⟨⟨hsub, _⟩, hσ⟩; exact ⟨hsub, hσ⟩
            rw [heq, Finset.card_union_of_disjoint]
            · split_ifs <;> simp
            · split_ifs
              · rw [Finset.disjoint_singleton_left]; simp [rest]
              · exact Finset.disjoint_empty_left _
          rw [hsplit, hlead_val]
          by_cases hodd : (rest.filter (fun C => σ C = true)).card % 2 = 1 <;> simp [hodd] <;> omega
        · funext C
          simp only [toFree, σ, dif_pos C.property]
      rw [← Finset.card_univ]
      exact Finset.card_bij (fun σ _ => toFree σ) (fun _ _ => Finset.mem_univ _) hinj
        (fun τ _ => by obtain ⟨σ, hσ, htf⟩ := hsurj τ; exact ⟨σ, hσ, htf⟩)
    rw [hbij, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hfree_card]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [↓reduceIte, add_zero]
    have hEq : Simg = Snonempty := by
      apply Finset.Subset.antisymm _ (Finset.filter_subset _ _)
      intro s hs
      rw [Finset.mem_filter]
      refine ⟨hs, ?_⟩
      obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hs
      rw [hnonempty_iff, hsig_even_iff]
      intro F hF
      have hd0 : d = ∅ := Finset.eq_empty_of_isEmpty d
      simp [hd0]
    change Simg.card = _
    rw [hEq, hSnonempty_card, hEven_card]
  · simp only [hn0, ↓reduceIte]
    have hEmptyMem : (∅ : Finset (Finset (Fin m))) ∈ Simg := by
      let v0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn0⟩
      refine Finset.mem_image.mpr ⟨{v0}, Finset.mem_univ _, ?_⟩
      by_contra hne
      have hne' : (support {v0}).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      have hev := (hsig_even_iff {v0}).mp ((hnonempty_iff {v0}).mp hne')
      obtain ⟨F, hF, hv0F⟩ := exists_comp_mem u v Finset.univ v0
      have hFodd := hev F hF
      have hinter : ({v0} : Finset (Fin n)) ∩ F = {v0} := by
        ext a; simp only [Finset.mem_inter, Finset.mem_singleton]
        exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hv0F⟩⟩
      rw [hinter] at hFodd
      simp at hFodd
    have hsplit : Simg = insert ∅ Snonempty := by
      ext s
      simp only [Snonempty, Finset.mem_insert, Finset.mem_filter]
      constructor
      · intro hs
        by_cases h : s = ∅
        · exact Or.inl h
        · exact Or.inr ⟨hs, Finset.nonempty_iff_ne_empty.mpr h⟩
      · rintro (rfl | ⟨hs, _⟩)
        · exact hEmptyMem
        · exact hs
    have hnotmem : (∅ : Finset (Finset (Fin m))) ∉ Snonempty := by
      simp [Snonempty]
    change Simg.card = _
    rw [hsplit, Finset.card_insert_of_notMem hnotmem, hSnonempty_card, hEven_card, Nat.add_comm]

lemma codec_iff (T : Finset (Fin m)) (k : ℕ) :
    let edges := (Finset.univ : Finset (Finset (Fin m)))
    let support := fun (d : Finset (Fin n)) =>
      (edges.filter (fun x => bdy u v x = d)).image (fun x => x ∩ T)
    (∃ (code : Finset (Fin n) → Fin k)
       (answer : Fin k → (Finset (Fin m) → Bool) → Bool),
      ∀ (d : Finset (Fin n)) (test : Finset (Fin m) → Bool),
        answer (code d) test = true ↔
        ∃ x ∈ edges, bdy u v x = d ∧ test (x ∩ T) = true) ↔
      ((Finset.univ : Finset (Finset (Fin n))).image support).card ≤ k := by
  intro edges support
  let Simg := (Finset.univ : Finset (Finset (Fin n))).image support
  have hmem_iff : ∀ (d : Finset (Fin n)) (test : Finset (Fin m) → Bool),
      (∃ x ∈ edges, bdy u v x = d ∧ test (x ∩ T) = true) ↔ ∃ z ∈ support d, test z = true := by
    intro d test
    simp only [support, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, hxe, hbx, ht⟩; exact ⟨x ∩ T, ⟨x, ⟨hxe, hbx⟩, rfl⟩, ht⟩
    · rintro ⟨z, ⟨x, ⟨hxe, hbx⟩, rfl⟩, ht⟩; exact ⟨x, hxe, hbx, ht⟩
  constructor
  · rintro ⟨code, answer, hspec⟩
    have hsep : ∀ d1 d2 : Finset (Fin n), code d1 = code d2 → support d1 = support d2 := by
      intro d1 d2 hcd
      ext z
      let test : Finset (Fin m) → Bool := fun w => decide (w = z)
      have h1 := hspec d1 test
      have h2 := hspec d2 test
      rw [hmem_iff] at h1 h2
      rw [hcd] at h1
      have hiff := h1.symm.trans h2
      simp only [test, decide_eq_true_eq, exists_eq_right] at hiff
      exact hiff
    let f : {s // s ∈ Simg} → Fin k := fun s => code (Finset.mem_image.mp s.property).choose
    have hfinj : Function.Injective f := by
      intro s1 s2 heq
      have h1 := (Finset.mem_image.mp s1.property).choose_spec.2
      have h2 := (Finset.mem_image.mp s2.property).choose_spec.2
      exact Subtype.ext (h1.symm.trans ((hsep _ _ heq).trans h2))
    have hcard := Fintype.card_le_of_injective f hfinj
    simpa [Fintype.card_coe] using hcard
  · intro hle
    let e := Fintype.equivFin {s // s ∈ Simg}
    have hce : Fintype.card {s // s ∈ Simg} ≤ k := by simpa [Fintype.card_coe] using hle
    let code : Finset (Fin n) → Fin k := fun d =>
      Fin.castLE hce (e ⟨support d, Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩⟩)
    let answer : Fin k → (Finset (Fin m) → Bool) → Bool := fun c test =>
      if h : c.val < Fintype.card {s // s ∈ Simg} then
        decide (∃ z ∈ (e.symm ⟨c.val, h⟩).val, test z = true)
      else false
    refine ⟨code, answer, fun d test => ?_⟩
    rw [hmem_iff]
    dsimp only [answer, code]
    simp only [Fin.val_castLE]
    have hlt : (e ⟨support d, Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩⟩).val <
        Fintype.card {s // s ∈ Simg} := (e _).isLt
    simp only [hlt, ↓reduceDIte, decide_eq_true_eq]
    have hfin : (⟨(e ⟨support d, Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩⟩).val, hlt⟩ :
        Fin (Fintype.card {s // s ∈ Simg})) =
        e ⟨support d, Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩⟩ := Fin.ext rfl
    rw [hfin, Equiv.symm_apply_apply]

end GraphParity

end PEqualNP.Outside.L_lib_1125_aux

theorem PEqualNP.Outside.L_lib_1125 : ∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)),
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let edges := (Finset.univ : Finset (Finset (Fin m)))
  let components := fun (allowed : Finset (Fin m)) =>
    let closed := fun (C : Finset (Fin n)) =>
      allowed.toList.all (fun i => decide (u i ∈ C) == decide (v i ∈ C))
    vertices.filter (fun C => C.Nonempty ∧ closed C = true ∧
      ∀ D ∈ C.powerset, D.Nonempty → closed D = true → D = C)
  let full := components Finset.univ
  let cut := components (Finset.univ \ T)
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let support := fun (d : Finset (Fin n)) =>
    (edges.filter (fun x => boundary x = d)).image (fun x => x ∩ T)
  (∀ (d : Finset (Fin n)) (z : Finset (Fin m)), z ⊆ T →
    (z ∈ support d ↔ ∀ C ∈ cut,
      (d ∩ C).card % 2 = (boundary z ∩ C).card % 2)) ∧
  ∀ k : Nat,
    (∃ (code : Finset (Fin n) → Fin k)
       (answer : Fin k → (Finset (Fin m) → Bool) → Bool),
      ∀ (d : Finset (Fin n)) (test : Finset (Fin m) → Bool),
        answer (code d) test = true ↔
        ∃ x ∈ edges, boundary x = d ∧ test (x ∩ T) = true) ↔
      2 ^ (cut.card - full.card) + (if n = 0 then 0 else 1) ≤ k := by
  intro n m u v T
  dsimp only
  refine ⟨fun d z hz => PEqualNP.Outside.L_lib_1125_aux.part1 u v T d z hz, fun k => ?_⟩
  have h1 := PEqualNP.Outside.L_lib_1125_aux.codec_iff u v T k
  have h2 := PEqualNP.Outside.L_lib_1125_aux.support_image_card u v T
  dsimp only at h1 h2
  rw [h2] at h1
  exact h1
