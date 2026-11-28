import Mathlib.Combinatorics.Hall.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Data.Rat.Defs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_430_aux

section Covers

variable {n m r : ℕ} (u v : Fin m → Fin n) (time : Fin n → Fin r)

def adj (q : Fin (r + 1)) (i j : Fin n) : Prop :=
  (time i).val < q.val ∧ q.val ≤ (time j).val ∧
    ∃ e : Fin m, (u e = i ∧ v e = j) ∨ (u e = j ∧ v e = i)

def validM (q : Fin (r + 1)) (M : Finset (Fin n × Fin n)) : Prop :=
  (∀ p ∈ M, adj u v time q p.1 p.2) ∧
  Set.InjOn Prod.fst (↑M : Set (Fin n × Fin n)) ∧
  Set.InjOn Prod.snd (↑M : Set (Fin n × Fin n))

def isCover (q : Fin (r + 1)) (C : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, adj u v time q i j → i ∈ C ∨ j ∈ C

lemma isCover_iff_edge (q : Fin (r + 1)) (C : Finset (Fin n)) :
    isCover u v time q C ↔
      ∀ e : Fin m, decide ((time (u e)).val < q.val) ≠ decide ((time (v e)).val < q.val) →
        u e ∈ C ∨ v e ∈ C := by
  constructor
  · intro hC e hne
    by_cases hu : (time (u e)).val < q.val
    · have hv : ¬ ((time (v e)).val < q.val) := by
        intro hv; apply hne; simp [hu, hv]
      exact hC (u e) (v e) ⟨hu, Nat.le_of_not_lt hv, ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩
    · have hv : (time (v e)).val < q.val := by
        by_contra hv; apply hne; simp [hu, hv]
      exact (hC (v e) (u e) ⟨hv, Nat.le_of_not_lt hu, ⟨e, Or.inr ⟨rfl, rfl⟩⟩⟩).symm
  · intro hC i j ⟨hi, hj, ⟨e, he⟩⟩
    have hlt : decide ((time i).val < q.val) = true := by simp [hi]
    have hge : decide ((time j).val < q.val) = false := by
      simp [Nat.not_lt.mpr hj]
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hC e (by rw [hlt, hge]; decide)
    · exact (hC e (by rw [hlt, hge]; decide)).symm

lemma isCover_univ (q : Fin (r + 1)) : isCover u v time q Finset.univ :=
  fun i _ _ => Or.inl (Finset.mem_univ i)

open Classical in
noncomputable def allCovers (q : Fin (r + 1)) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun C => isCover u v time q C)

lemma allCovers_nonempty (q : Fin (r + 1)) : (allCovers u v time q).Nonempty := by
  classical
  refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, isCover_univ u v time q⟩⟩

open Classical in
noncomputable def minCoverCard (q : Fin (r + 1)) : ℕ :=
  ((allCovers u v time q).image Finset.card).min'
    ((allCovers_nonempty u v time q).image Finset.card)

open Classical in
noncomputable def minCovers (q : Fin (r + 1)) : Finset (Finset (Fin n)) :=
  (allCovers u v time q).filter (fun C => C.card = minCoverCard u v time q)

lemma minCovers_nonempty (q : Fin (r + 1)) : (minCovers u v time q).Nonempty := by
  classical
  have hmem : minCoverCard u v time q ∈ (allCovers u v time q).image Finset.card :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨C, hC, hcard⟩
  exact ⟨C, Finset.mem_filter.mpr ⟨hC, hcard⟩⟩

open Classical in
noncomputable def sep (q : Fin (r + 1)) : Finset (Fin n) :=
  Classical.choose
    (Finset.exists_max_image (minCovers u v time q)
      (fun C => (C.filter (fun i => (time i).val < q.val)).card)
      (minCovers_nonempty u v time q))

lemma sep_mem_minCovers (q : Fin (r + 1)) : sep u v time q ∈ minCovers u v time q := by
  classical
  exact (Classical.choose_spec
    (Finset.exists_max_image (minCovers u v time q)
      (fun C => (C.filter (fun i => (time i).val < q.val)).card)
      (minCovers_nonempty u v time q))).1

lemma sep_isCover (q : Fin (r + 1)) : isCover u v time q (sep u v time q) := by
  classical
  have h := sep_mem_minCovers u v time q
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2

lemma sep_card_eq_min (q : Fin (r + 1)) : (sep u v time q).card = minCoverCard u v time q := by
  classical
  exact (Finset.mem_filter.mp (sep_mem_minCovers u v time q)).2

lemma sep_card_le (q : Fin (r + 1)) {C : Finset (Fin n)} (hC : isCover u v time q C) :
    (sep u v time q).card ≤ C.card := by
  classical
  rw [sep_card_eq_min]
  exact Finset.min'_le _ _
    (Finset.mem_image.mpr ⟨C, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩, rfl⟩)

lemma sep_left_max (q : Fin (r + 1)) {C : Finset (Fin n)}
    (hC : isCover u v time q C) (hcard : C.card = (sep u v time q).card) :
    (C.filter (fun i => (time i).val < q.val)).card ≤
      ((sep u v time q).filter (fun i => (time i).val < q.val)).card := by
  classical
  have hmem : C ∈ minCovers u v time q :=
    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC⟩,
      hcard.trans (sep_card_eq_min u v time q)⟩
  exact (Classical.choose_spec
    (Finset.exists_max_image (minCovers u v time q)
      (fun D => (D.filter (fun i => (time i).val < q.val)).card)
      (minCovers_nonempty u v time q))).2 C hmem

lemma sep_zero : sep u v time 0 = ∅ := by
  have hcov : isCover u v time 0 ∅ := by
    intro i j ⟨hi, _, _⟩
    exact absurd hi (Nat.not_lt_zero _)
  have hle : (sep u v time 0).card ≤ 0 := sep_card_le u v time 0 hcov
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)

lemma sep_last : sep u v time (Fin.last r) = ∅ := by
  have hcov : isCover u v time (Fin.last r) ∅ := by
    intro i j ⟨_, hj, _⟩
    exact absurd (Nat.lt_of_le_of_lt hj (time j).isLt) (Nat.lt_irrefl _)
  have hle : (sep u v time (Fin.last r)).card ≤ 0 := sep_card_le u v time (Fin.last r) hcov
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hle)

lemma sep_konig (q : Fin (r + 1)) :
    ∃ M : Finset (Fin n × Fin n), validM u v time q M ∧ M.card = (sep u v time q).card := by
  classical
  set C := sep u v time q
  have hC : isCover u v time q C := sep_isCover u v time q
  set A : Finset (Fin n) := C.filter (fun i => (time i).val < q.val)
  set B : Finset (Fin n) := C.filter (fun i => q.val ≤ (time i).val)
  have hdisjAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have h1 := (Finset.mem_filter.mp hxA).2
    have h2 := (Finset.mem_filter.mp hxB).2
    omega
  have hunionAB : A ∪ B = C := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases hlt : (time x).val < q.val
      · exact Or.inl ⟨hx, hlt⟩
      · exact Or.inr ⟨hx, Nat.le_of_not_lt hlt⟩
  have hcardAB : A.card + B.card = C.card := by
    rw [← Finset.card_union_of_disjoint hdisjAB, hunionAB]
  let nbrR : A → Finset (Fin n) := fun a =>
    Finset.univ.filter (fun j => j ∉ B ∧ adj u v time q a.1 j)
  have hHallA : ∀ s : Finset A, s.card ≤ (s.biUnion nbrR).card := by
    intro s
    by_contra hlt
    push Not at hlt
    let S : Finset (Fin n) := s.image Subtype.val
    let N : Finset (Fin n) := s.biUnion nbrR
    have hScard : S.card = s.card := Finset.card_image_of_injective s Subtype.val_injective
    have hSsubA : S ⊆ A := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
      exact a.2
    have hSsubC : S ⊆ C := hSsubA.trans (Finset.filter_subset _ C)
    let C' : Finset (Fin n) := (C \ S) ∪ N
    have hC'cov : isCover u v time q C' := by
      intro i j hadj
      by_cases hjB : j ∈ B
      · right
        refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hjB).1, ?_⟩)
        intro hjS
        exact Finset.disjoint_left.mp hdisjAB (hSsubA hjS) hjB
      · have hiC : i ∈ C := by
          rcases hC i j hadj with hi | hj
          · exact hi
          · exact absurd (Finset.mem_filter.mpr ⟨hj, hadj.2.1⟩) hjB
        by_cases hiS : i ∈ S
        · right
          rcases Finset.mem_image.mp hiS with ⟨a, ha, rfl⟩
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjB, hadj⟩⟩)
        · left
          exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hiC, hiS⟩)
    have hle : C.card ≤ C'.card := sep_card_le u v time q hC'cov
    have hcard_le : C'.card ≤ (C \ S).card + (s.biUnion nbrR).card := Finset.card_union_le _ _
    have hsdiff : (C \ S).card = C.card - S.card := Finset.card_sdiff_of_subset hSsubC
    have hSle : S.card ≤ C.card := Finset.card_le_card hSsubC
    omega
  rcases (Finset.all_card_le_biUnion_card_iff_exists_injective nbrR).mp hHallA with ⟨f, hf_inj, hf_mem⟩
  let nbrL : B → Finset (Fin n) := fun b =>
    Finset.univ.filter (fun i => i ∉ A ∧ adj u v time q i b.1)
  have hHallB : ∀ s : Finset B, s.card ≤ (s.biUnion nbrL).card := by
    intro s
    by_contra hlt
    push Not at hlt
    let S : Finset (Fin n) := s.image Subtype.val
    let N : Finset (Fin n) := s.biUnion nbrL
    have hScard : S.card = s.card := Finset.card_image_of_injective s Subtype.val_injective
    have hSsubB : S ⊆ B := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨b, _, rfl⟩
      exact b.2
    have hSsubC : S ⊆ C := hSsubB.trans (Finset.filter_subset _ C)
    let C' : Finset (Fin n) := (C \ S) ∪ N
    have hC'cov : isCover u v time q C' := by
      intro i j hadj
      by_cases hiA : i ∈ A
      · left
        refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hiA).1, ?_⟩)
        intro hiS
        exact Finset.disjoint_left.mp hdisjAB hiA (hSsubB hiS)
      · have hjC : j ∈ C := by
          rcases hC i j hadj with hi | hj
          · exact absurd (Finset.mem_filter.mpr ⟨hi, hadj.1⟩) hiA
          · exact hj
        by_cases hjS : j ∈ S
        · left
          rcases Finset.mem_image.mp hjS with ⟨b, hb, rfl⟩
          exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiA, hadj⟩⟩)
        · right
          exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hjC, hjS⟩)
    have hle : C.card ≤ C'.card := sep_card_le u v time q hC'cov
    have hcard_le : C'.card ≤ (C \ S).card + (s.biUnion nbrL).card := Finset.card_union_le _ _
    have hsdiff : (C \ S).card = C.card - S.card := Finset.card_sdiff_of_subset hSsubC
    have hSle : S.card ≤ C.card := Finset.card_le_card hSsubC
    omega
  rcases (Finset.all_card_le_biUnion_card_iff_exists_injective nbrL).mp hHallB with ⟨g, hg_inj, hg_mem⟩
  let M1 : Finset (Fin n × Fin n) := (Finset.univ : Finset A).image (fun a => (a.1, f a))
  let M2 : Finset (Fin n × Fin n) := (Finset.univ : Finset B).image (fun b => (g b, b.1))
  have hM1_info : ∀ p ∈ M1, p.1 ∈ A ∧ p.2 ∉ B ∧ adj u v time q p.1 p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, _, rfl⟩
    have hfa := (Finset.mem_filter.mp (hf_mem a)).2
    exact ⟨a.2, hfa.1, hfa.2⟩
  have hM2_info : ∀ p ∈ M2, p.1 ∉ A ∧ p.2 ∈ B ∧ adj u v time q p.1 p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨b, _, rfl⟩
    have hgb := (Finset.mem_filter.mp (hg_mem b)).2
    exact ⟨hgb.1, b.2, hgb.2⟩
  have hdisjM : Disjoint M1 M2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    exact (hM2_info p hp2).1 (hM1_info p hp1).1
  refine ⟨M1 ∪ M2, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · exact (hM1_info p hp1).2.2
    · exact (hM2_info p hp2).2.2
  · intro p1 hp1 p2 hp2 hfst
    have hp1' : p1 ∈ M1 ∪ M2 := hp1
    have hp2' : p2 ∈ M1 ∪ M2 := hp2
    rcases Finset.mem_union.mp hp1' with h1 | h1 <;> rcases Finset.mem_union.mp hp2' with h2 | h2
    · rcases Finset.mem_image.mp h1 with ⟨a1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨a2, _, rfl⟩
      have ha : a1 = a2 := Subtype.ext hfst
      subst ha; rfl
    · exfalso; exact (hM2_info p2 h2).1 (hfst ▸ (hM1_info p1 h1).1)
    · exfalso; exact (hM2_info p1 h1).1 (hfst.symm ▸ (hM1_info p2 h2).1)
    · rcases Finset.mem_image.mp h1 with ⟨b1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨b2, _, rfl⟩
      have hb : b1 = b2 := hg_inj hfst
      subst hb; rfl
  · intro p1 hp1 p2 hp2 hsnd
    have hp1' : p1 ∈ M1 ∪ M2 := hp1
    have hp2' : p2 ∈ M1 ∪ M2 := hp2
    rcases Finset.mem_union.mp hp1' with h1 | h1 <;> rcases Finset.mem_union.mp hp2' with h2 | h2
    · rcases Finset.mem_image.mp h1 with ⟨a1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨a2, _, rfl⟩
      have ha : a1 = a2 := hf_inj hsnd
      subst ha; rfl
    · exfalso; exact (hM1_info p1 h1).2.1 (hsnd ▸ (hM2_info p2 h2).2.1)
    · exfalso; exact (hM1_info p2 h2).2.1 (hsnd.symm ▸ (hM2_info p1 h1).2.1)
    · rcases Finset.mem_image.mp h1 with ⟨b1, _, rfl⟩
      rcases Finset.mem_image.mp h2 with ⟨b2, _, rfl⟩
      have hb : b1 = b2 := Subtype.ext hsnd
      subst hb; rfl
  · rw [Finset.card_union_of_disjoint hdisjM]
    have hM1c : M1.card = A.card := by
      rw [Finset.card_image_of_injective _ (fun a1 a2 h => Subtype.ext (congrArg Prod.fst h)),
        Finset.card_univ, Fintype.card_coe]
    have hM2c : M2.card = B.card := by
      rw [Finset.card_image_of_injective _ (fun b1 b2 h => Subtype.ext (congrArg Prod.snd h)),
        Finset.card_univ, Fintype.card_coe]
    rw [hM1c, hM2c, hcardAB]

lemma sep_mono (t : Fin r) (i : Fin n) :
    (i ∈ sep u v time t.castSucc → i ∉ sep u v time t.succ → (time i).val ≤ t.val) ∧
    (i ∉ sep u v time t.castSucc → i ∈ sep u v time t.succ → t.val ≤ (time i).val) := by
  classical
  set C1 := sep u v time t.castSucc
  set C2 := sep u v time t.succ
  have hC1 : isCover u v time t.castSucc C1 := sep_isCover u v time t.castSucc
  have hC2 : isCover u v time t.succ C2 := sep_isCover u v time t.succ
  let L1 : Finset (Fin n) := Finset.univ.filter (fun x => (time x).val < t.val)
  let Bt : Finset (Fin n) := Finset.univ.filter (fun x => (time x).val = t.val)
  let R2 : Finset (Fin n) := Finset.univ.filter (fun x => t.val + 1 ≤ (time x).val)
  have hdisj_LB : Disjoint L1 Bt := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hdisj_LR : Disjoint L1 R2 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hdisj_BR : Disjoint Bt R2 := by
    rw [Finset.disjoint_left]; intro x h1 h2
    have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
  have hpart : ∀ S : Finset (Fin n), S.card = (S ∩ L1).card + (S ∩ Bt).card + (S ∩ R2).card := by
    intro S
    have hdisj1 : Disjoint (S ∩ L1) (S ∩ Bt) :=
      hdisj_LB.mono Finset.inter_subset_right Finset.inter_subset_right
    have hdisj2 : Disjoint ((S ∩ L1) ∪ (S ∩ Bt)) (S ∩ R2) := by
      rw [Finset.disjoint_union_left]
      exact ⟨hdisj_LR.mono Finset.inter_subset_right Finset.inter_subset_right,
        hdisj_BR.mono Finset.inter_subset_right Finset.inter_subset_right⟩
    have hunion : ((S ∩ L1) ∪ (S ∩ Bt)) ∪ (S ∩ R2) = S := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, L1, Bt, R2, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
      · intro hx
        by_cases h1 : (time x).val < t.val
        · exact Or.inl (Or.inl ⟨hx, h1⟩)
        · by_cases h2 : (time x).val = t.val
          · exact Or.inl (Or.inr ⟨hx, h2⟩)
          · exact Or.inr ⟨hx, by omega⟩
    rw [← Finset.card_union_of_disjoint hdisj1, ← Finset.card_union_of_disjoint hdisj2, hunion]
  let D1 : Finset (Fin n) := ((C1 ∩ L1) ∪ (C2 ∩ L1)) ∪ (C1 ∩ Bt) ∪ ((C1 ∩ R2) ∩ (C2 ∩ R2))
  let D2 : Finset (Fin n) := ((C1 ∩ L1) ∩ (C2 ∩ L1)) ∪ (C2 ∩ Bt) ∪ ((C1 ∩ R2) ∪ (C2 ∩ R2))
  have hD1_cov : isCover u v time t.castSucc D1 := by
    intro a b hadj
    have haL1 : a ∈ L1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.1⟩
    have hb_ge : t.val ≤ (time b).val := hadj.2.1
    by_cases hbEq : (time b).val = t.val
    · have hbBt : b ∈ Bt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbEq⟩
      rcases hC1 a b hadj with ha | hb
      · left; exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, haL1⟩)))
      · right; exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hb, hbBt⟩))
    · have hbR2 : b ∈ R2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have ha_lt1 : (time a).val < t.val := hadj.1
      have hadj2 : adj u v time t.succ a b := ⟨by simp [Fin.val_succ]; omega, by simp [Fin.val_succ]; omega, hadj.2.2⟩
      by_cases ha1 : a ∈ C1
      · left; exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha1, haL1⟩)))
      · by_cases ha2 : a ∈ C2
        · left; exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha2, haL1⟩)))
        · have hb1 : b ∈ C1 := (hC1 a b hadj).resolve_left ha1
          have hb2 : b ∈ C2 := (hC2 a b hadj2).resolve_left ha2
          right; exact Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hb1, hbR2⟩, Finset.mem_inter.mpr ⟨hb2, hbR2⟩⟩)
  have hD2_cov : isCover u v time t.succ D2 := by
    intro a b hadj
    have hbR2 : b ∈ R2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.2.1⟩
    have ha_lt : (time a).val < t.val + 1 := hadj.1
    by_cases haEq : (time a).val = t.val
    · have haBt : a ∈ Bt := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haEq⟩
      rcases hC2 a b hadj with ha | hb
      · left; exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨ha, haBt⟩))
      · right; exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_inter.mpr ⟨hb, hbR2⟩))
    · have haL1 : a ∈ L1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hb_ge2 : t.val + 1 ≤ (time b).val := hadj.2.1
      have hadj1 : adj u v time t.castSucc a b := ⟨by simp; omega, by simp; omega, hadj.2.2⟩
      by_cases hb1 : b ∈ C1
      · right; exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨hb1, hbR2⟩))
      · by_cases hb2 : b ∈ C2
        · right; exact Finset.mem_union_right _ (Finset.mem_union_right _
            (Finset.mem_inter.mpr ⟨hb2, hbR2⟩))
        · have ha1 : a ∈ C1 := (hC1 a b hadj1).resolve_right hb1
          have ha2 : a ∈ C2 := (hC2 a b hadj).resolve_right hb2
          left; exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨ha1, haL1⟩, Finset.mem_inter.mpr ⟨ha2, haL1⟩⟩))
  have hD1_L : D1 ∩ L1 = (C1 ∩ L1) ∪ (C2 ∩ L1) := by
    ext x
    simp only [D1, Finset.mem_inter, Finset.mem_union, L1, Bt, R2, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨((⟨h, _⟩ | ⟨h, _⟩) | ⟨_, h2⟩) | ⟨⟨_, h2⟩, _⟩, h1⟩
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
      · omega
      · omega
    · rintro (⟨h, h1⟩ | ⟨h, h1⟩)
      · exact ⟨Or.inl (Or.inl (Or.inl ⟨h, h1⟩)), h1⟩
      · exact ⟨Or.inl (Or.inl (Or.inr ⟨h, h1⟩)), h1⟩
  have hD1_B : D1 ∩ Bt = C1 ∩ Bt := by
    ext x
    simp only [D1, Finset.mem_inter, Finset.mem_union, L1, Bt, R2, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨h, _⟩) | ⟨⟨_, h2⟩, _⟩, h1⟩
      · omega
      · omega
      · exact ⟨h, h1⟩
      · omega
    · rintro ⟨h, h1⟩; exact ⟨Or.inl (Or.inr ⟨h, h1⟩), h1⟩
  have hD1_R : D1 ∩ R2 = (C1 ∩ R2) ∩ (C2 ∩ R2) := by
    ext x
    simp only [D1, Finset.mem_inter, Finset.mem_union, L1, Bt, R2, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨((⟨_, h2⟩ | ⟨_, h2⟩) | ⟨_, h2⟩) | ⟨⟨h1', _⟩, ⟨h2', _⟩⟩, h1⟩
      · omega
      · omega
      · omega
      · exact ⟨⟨h1', h1⟩, ⟨h2', h1⟩⟩
    · rintro ⟨⟨h1', h1⟩, ⟨h2', _⟩⟩; exact ⟨Or.inr ⟨⟨h1', h1⟩, ⟨h2', h1⟩⟩, h1⟩
  have hD2_L : D2 ∩ L1 = (C1 ∩ L1) ∩ (C2 ∩ L1) := by
    ext x
    simp only [D2, Finset.mem_inter, Finset.mem_union, L1, Bt, R2, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨(⟨⟨h1', _⟩, ⟨h2', _⟩⟩ | ⟨_, h2⟩) | (⟨_, h2⟩ | ⟨_, h2⟩), h1⟩
      · exact ⟨⟨h1', h1⟩, ⟨h2', h1⟩⟩
      · omega
      · omega
      · omega
    · rintro ⟨⟨h1', h1⟩, ⟨h2', _⟩⟩; exact ⟨Or.inl (Or.inl ⟨⟨h1', h1⟩, ⟨h2', h1⟩⟩), h1⟩
  have hD2_B : D2 ∩ Bt = C2 ∩ Bt := by
    ext x
    simp only [D2, Finset.mem_inter, Finset.mem_union, L1, Bt, R2, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨(⟨⟨_, h2⟩, _⟩ | ⟨h, _⟩) | (⟨_, h2⟩ | ⟨_, h2⟩), h1⟩
      · omega
      · exact ⟨h, h1⟩
      · omega
      · omega
    · rintro ⟨h, h1⟩; exact ⟨Or.inl (Or.inr ⟨h, h1⟩), h1⟩
  have hD2_R : D2 ∩ R2 = (C1 ∩ R2) ∪ (C2 ∩ R2) := by
    ext x
    simp only [D2, Finset.mem_inter, Finset.mem_union, L1, Bt, R2, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨(⟨⟨_, h2⟩, _⟩ | ⟨_, h2⟩) | (⟨h, _⟩ | ⟨h, _⟩), h1⟩
      · omega
      · omega
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
    · rintro (⟨h, h1⟩ | ⟨h, h1⟩)
      · exact ⟨Or.inr (Or.inl ⟨h, h1⟩), h1⟩
      · exact ⟨Or.inr (Or.inr ⟨h, h1⟩), h1⟩
  have hsum : D1.card + D2.card = C1.card + C2.card := by
    rw [hpart D1, hpart D2, hpart C1, hpart C2, hD1_L, hD1_B, hD1_R, hD2_L, hD2_B, hD2_R]
    have hL := Finset.card_union_add_card_inter (C1 ∩ L1) (C2 ∩ L1)
    have hR := Finset.card_union_add_card_inter (C1 ∩ R2) (C2 ∩ R2)
    omega
  have hC1_le : C1.card ≤ D1.card := sep_card_le u v time t.castSucc hD1_cov
  have hC2_le : C2.card ≤ D2.card := sep_card_le u v time t.succ hD2_cov
  have hD1_eq : D1.card = C1.card := by omega
  have hLmax := sep_left_max u v time t.castSucc hD1_cov hD1_eq
  have hfilter_eq : ∀ S : Finset (Fin n),
      S.filter (fun x => (time x).val < t.castSucc.val) = S ∩ L1 := by
    intro S; ext x; simp [L1]
  rw [hfilter_eq D1, hfilter_eq C1, hD1_L] at hLmax
  have hsubL : C1 ∩ L1 ⊆ (C1 ∩ L1) ∪ (C2 ∩ L1) := Finset.subset_union_left
  have hLeq : (C1 ∩ L1) ∪ (C2 ∩ L1) = C1 ∩ L1 :=
    (Finset.eq_of_subset_of_card_le hsubL hLmax).symm
  have hReq_card : ((C1 ∩ R2) ∩ (C2 ∩ R2)).card = (C1 ∩ R2).card := by
    have h1 := hpart D1
    have h2 := hpart C1
    rw [hD1_L, hD1_B, hD1_R, hLeq] at h1
    omega
  have hReq : (C1 ∩ R2) ∩ (C2 ∩ R2) = C1 ∩ R2 :=
    Finset.eq_of_subset_of_card_le Finset.inter_subset_left (Nat.le_of_eq hReq_card.symm)
  constructor
  · intro hi1 hi2
    by_contra hgt
    have hiR2 : i ∈ R2 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hiIn : i ∈ C1 ∩ R2 := Finset.mem_inter.mpr ⟨hi1, hiR2⟩
    rw [← hReq] at hiIn
    exact hi2 (Finset.mem_inter.mp (Finset.mem_inter.mp hiIn).2).1
  · intro hi1 hi2
    by_contra hlt
    have hiL1 : i ∈ L1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hiIn : i ∈ (C1 ∩ L1) ∪ (C2 ∩ L1) :=
      Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hi2, hiL1⟩)
    rw [hLeq] at hiIn
    exact hi1 (Finset.mem_inter.mp hiIn).1

end Covers

section ReaderConstruction

variable {n m r : ℕ} (u v : Fin m → Fin n) (time : Fin n → Fin r)

def batch (t : Fin r) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => time i = t)

noncomputable def avail (t : Fin r) : Finset (Fin n) :=
  sep u v time t.castSucc ∪ sep u v time t.succ ∪ batch time t

noncomputable def seen (q : Fin (r + 1)) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin n => (time i).val < q.val)) ∪ sep u v time q

lemma seen_zero : seen u v time 0 = ∅ := by
  ext i
  simp [seen, sep_zero]

lemma seen_last : seen u v time (Fin.last r) = Finset.univ := by
  ext i
  simp [seen, (time i).isLt]

lemma seen_mono_step (t : Fin r) : seen u v time t.castSucc ⊆ seen u v time t.succ := by
  intro i hi
  simp only [seen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with hlt | hsep
  · left; simp only [Fin.val_succ]; simp only [Fin.coe_castSucc] at hlt; omega
  · by_cases hsep2 : i ∈ sep u v time t.succ
    · exact Or.inr hsep2
    · left
      have hle := (sep_mono u v time t i).1 hsep hsep2
      simp only [Fin.val_succ]; omega

lemma seen_mono_le {q1 q2 : Fin (r + 1)} (h : q1.val ≤ q2.val) :
    seen u v time q1 ⊆ seen u v time q2 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  induction k generalizing q2 with
  | zero =>
    have heq : q1 = q2 := Fin.ext (by omega)
    subst heq; exact Finset.Subset.rfl
  | succ k ih =>
    have hlt : q1.val + k < r := by omega
    let t : Fin r := ⟨q1.val + k, hlt⟩
    have hq2 : q2 = t.succ := Fin.ext (by simp [t]; omega)
    rw [hq2]
    exact (ih (q2 := t.castSucc) (by simp [t]) (by simp [t])).trans (seen_mono_step u v time t)

lemma avail_subset_seen_succ (t : Fin r) : avail u v time t ⊆ seen u v time t.succ := by
  intro i hi
  simp only [avail, Finset.mem_union] at hi
  rcases hi with (h1 | h2) | h3
  · exact seen_mono_step u v time t (Finset.mem_union_right _ h1)
  · exact Finset.mem_union_right _ h2
  · have ht : time i = t := (Finset.mem_filter.mp h3).2
    refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    simp [ht]

lemma sep_succ_inter_seen_castSucc (t : Fin r) {i : Fin n}
    (h1 : i ∈ sep u v time t.succ) (h2 : i ∈ seen u v time t.castSucc) :
    i ∈ sep u v time t.castSucc := by
  by_contra hnot
  have hge := (sep_mono u v time t i).2 hnot h1
  simp only [seen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.coe_castSucc] at h2
  rcases h2 with hlt | hsep
  · omega
  · exact hnot hsep

lemma edge_visible (e : Fin m) : ∃ t : Fin r, u e ∈ avail u v time t ∧ v e ∈ avail u v time t := by
  have haux : ∀ (a b : Fin n),
      (∃ e' : Fin m, (u e' = a ∧ v e' = b) ∨ (u e' = b ∧ v e' = a)) →
      (time a).val ≤ (time b).val →
      ∃ t : Fin r, a ∈ avail u v time t ∧ b ∈ avail u v time t := by
    intro a b hedge hle
    by_cases heq : time a = time b
    · refine ⟨time a, ?_, ?_⟩
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq.symm⟩)
    · have hlt : (time a).val < (time b).val := lt_of_le_of_ne hle (fun h => heq (Fin.ext h))
      have hcov_step : ∀ (q : Fin (r + 1)), (time a).val < q.val → q.val ≤ (time b).val →
          a ∈ sep u v time q ∨ b ∈ sep u v time q := fun q h1 h2 =>
        sep_isCover u v time q a b ⟨h1, h2, hedge⟩
      by_cases hb1 : b ∈ sep u v time (time a).succ
      · refine ⟨time a, ?_, ?_⟩
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb1)
      · have ha1 : a ∈ sep u v time (time a).succ :=
          (hcov_step (time a).succ (by simp) (by simp; omega)).resolve_right hb1
        by_cases ha2 : a ∈ sep u v time (time b).castSucc
        · refine ⟨time b, ?_, ?_⟩
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ ha2)
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
        · have htb : (time b).val < r := (time b).isLt
          have hfind : ∀ (d : ℕ) (hbd : (time a).val + 1 + d ≤ (time b).val),
              a ∉ sep u v time ⟨(time a).val + 1 + d, by omega⟩ →
              ∃ t : Fin r, (time a).val < t.val ∧ t.val < (time b).val ∧
                a ∈ sep u v time t.castSucc ∧ a ∉ sep u v time t.succ := by
            intro d
            induction d with
            | zero =>
              intro _ hnot
              exact absurd ha1 hnot
            | succ d ih =>
              intro hbd hnot
              let qm : Fin (r + 1) := ⟨(time a).val + 1 + d, by omega⟩
              by_cases hmid : a ∈ sep u v time qm
              · let tm : Fin r := ⟨(time a).val + 1 + d, by omega⟩
                have hq_succ : tm.succ = ⟨(time a).val + 1 + (d + 1), by omega⟩ := Fin.ext (by simp [tm]; omega)
                exact ⟨tm, by simp [tm]; omega, by simp [tm]; omega, hmid, by rw [hq_succ]; exact hnot⟩
              · exact ih (by omega) hmid
          have hq_end : (⟨(time a).val + 1 + ((time b).val - ((time a).val + 1)), by omega⟩ : Fin (r + 1)) =
              (time b).castSucc := Fin.ext (by simp; omega)
          rcases hfind ((time b).val - ((time a).val + 1)) (by omega) (by rw [hq_end]; exact ha2) with
            ⟨t, ht1, ht2, hat1, hat2⟩
          have hbt : b ∈ sep u v time t.succ :=
            (hcov_step t.succ (by simp; omega) (by simp; omega)).resolve_left hat2
          exact ⟨t, Finset.mem_union_left _ (Finset.mem_union_left _ hat1),
            Finset.mem_union_left _ (Finset.mem_union_right _ hbt)⟩
  by_cases hle : (time (u e)).val ≤ (time (v e)).val
  · exact haux (u e) (v e) ⟨e, Or.inl ⟨rfl, rfl⟩⟩ hle
  · rcases haux (v e) (u e) ⟨e, Or.inr ⟨rfl, rfl⟩⟩ (by omega) with ⟨t, hv, hu⟩
    exact ⟨t, hu, hv⟩

noncomputable def owner (e : Fin m) : Fin r :=
  Classical.choose (edge_visible u v time e)

lemma owner_mem (e : Fin m) :
    u e ∈ avail u v time (owner u v time e) ∧ v e ∈ avail u v time (owner u v time e) :=
  Classical.choose_spec (edge_visible u v time e)

noncomputable def edgesBefore (q : Fin (r + 1)) : Finset (Fin m) :=
  Finset.univ.filter (fun e : Fin m => (owner u v time e).val < q.val)

noncomputable def edgesAt (t : Fin r) : Finset (Fin m) :=
  Finset.univ.filter (fun e : Fin m => owner u v time e = t)

lemma edgesBefore_zero : edgesBefore u v time 0 = ∅ := by
  ext e; simp [edgesBefore]

lemma edgesBefore_last : edgesBefore u v time (Fin.last r) = Finset.univ := by
  ext e; simp [edgesBefore, (owner u v time e).isLt]

lemma edgesBefore_succ (t : Fin r) :
    edgesBefore u v time t.succ = edgesBefore u v time t.castSucc ∪ edgesAt u v time t := by
  ext e
  simp only [edgesBefore, edgesAt, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, Fin.val_succ, Fin.coe_castSucc, Fin.ext_iff]
  omega

lemma edgesBefore_disj_edgesAt (t : Fin r) :
    Disjoint (edgesBefore u v time t.castSucc) (edgesAt u v time t) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  have := (Finset.mem_filter.mp h1).2
  have := (Finset.mem_filter.mp h2).2
  simp only [Fin.coe_castSucc] at *
  omega

lemma edgesBefore_endpoints_seen (q : Fin (r + 1)) {e : Fin m} (he : e ∈ edgesBefore u v time q) :
    u e ∈ seen u v time q ∧ v e ∈ seen u v time q := by
  have hlt : (owner u v time e).val < q.val := (Finset.mem_filter.mp he).2
  have hsub : seen u v time (owner u v time e).succ ⊆ seen u v time q :=
    seen_mono_le u v time (by simp; omega)
  have hmem := owner_mem u v time e
  exact ⟨hsub (avail_subset_seen_succ u v time _ hmem.1),
    hsub (avail_subset_seen_succ u v time _ hmem.2)⟩

noncomputable def freeSet (t : Fin r) : Finset (Fin n) :=
  batch time t \ (sep u v time t.castSucc ∪ sep u v time t.succ)

open Classical in
lemma enough_to_reader (w : Fin (r + 1) → ℕ)
    (henough : ∀ (q : Fin (r + 1)) (M : Finset (Fin n × Fin n)), validM u v time q M → 2 ^ M.card ≤ w q) :
    ∃ (start : Fin (w 0)) (last : Fin (w (Fin.last r)))
      (terms : (t : Fin r) → (Fin n → Bool) → Fin (w t.castSucc) → Fin (w t.succ) →
        List (Finset (Fin m × Bool))),
      (∀ t s a b, (terms t s a b).length ≤
        2 ^ ((Finset.univ.filter (fun j : Fin n => time j = t)).card)) ∧
      ∀ (p : Fin n → Bool) (cost : Fin m → Bool → ℕ),
        let total := ∑ x : Fin n → Bool, if (∀ i, p i = true → x i = false) then
          ∏ e : Fin m, cost e (decide (x (u e) ≠ x (v e))) else 0
        ∃ state : (q : Fin (r + 1)) → Fin (w q) → ℕ,
          (∀ j, state 0 j = if j = start then 1 else 0) ∧
          (∀ (t : Fin r) (b : Fin (w t.succ)),
            let s := fun j : Fin n => if time j = t then p j else false
            state t.succ b = ∑ a : Fin (w t.castSucc), state t.castSucc a *
              ((terms t s a b).map (fun M => ∏ h ∈ M, cost h.1 h.2)).sum) ∧
          state (Fin.last r) last = total := by
  have hsep_le : ∀ q : Fin (r + 1), 2 ^ (sep u v time q).card ≤ w q := by
    intro q
    rcases sep_konig u v time q with ⟨M, hM, hcard⟩
    rw [← hcard]
    exact henough q M hM
  have hcard_fun : ∀ q : Fin (r + 1), Fintype.card (sep u v time q → Bool) = 2 ^ (sep u v time q).card := by
    intro q
    simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
  let enc : (q : Fin (r + 1)) → (sep u v time q → Bool) → Fin (w q) := fun q σ =>
    Fin.castLE (hsep_le q) ((Fintype.equivFinOfCardEq (hcard_fun q)) σ)
  have henc_inj : ∀ q : Fin (r + 1), Function.Injective (enc q) := by
    intro q σ1 σ2 h
    have h1 : (Fintype.equivFinOfCardEq (hcard_fun q)) σ1 = (Fintype.equivFinOfCardEq (hcard_fun q)) σ2 :=
      Fin.ext (by simpa [enc] using congrArg Fin.val h)
    exact (Fintype.equivFinOfCardEq (hcard_fun q)).injective h1
  let empty0 : sep u v time 0 → Bool := fun i => False.elim (Finset.notMem_empty i.1 (sep_zero u v time ▸ i.2))
  let emptyR : sep u v time (Fin.last r) → Bool := fun i => False.elim (Finset.notMem_empty i.1 (sep_last u v time ▸ i.2))
  let start : Fin (w 0) := enc 0 empty0
  let last : Fin (w (Fin.last r)) := enc (Fin.last r) emptyR
  let consist : (t : Fin r) → (Fin n → Bool) → (sep u v time t.castSucc → Bool) →
      (sep u v time t.succ → Bool) → Prop := fun t s σ τ =>
    (∀ i (h1 : i ∈ sep u v time t.castSucc) (h2 : i ∈ sep u v time t.succ), σ ⟨i, h1⟩ = τ ⟨i, h2⟩) ∧
    (∀ i (h1 : i ∈ sep u v time t.castSucc), time i = t → s i = true → σ ⟨i, h1⟩ = false) ∧
    (∀ i (h2 : i ∈ sep u v time t.succ), time i = t → s i = true → τ ⟨i, h2⟩ = false)
  let allowedPhi : (t : Fin r) → (Fin n → Bool) → (freeSet u v time t → Bool) → Prop :=
    fun t s φ => ∀ i : freeSet u v time t, s i.1 = true → φ i = false
  let localVal : (t : Fin r) → (sep u v time t.castSucc → Bool) → (sep u v time t.succ → Bool) →
      (freeSet u v time t → Bool) → Fin n → Bool := fun t σ τ φ i =>
    if h1 : i ∈ sep u v time t.castSucc then σ ⟨i, h1⟩
    else if h2 : i ∈ sep u v time t.succ then τ ⟨i, h2⟩
    else if h3 : i ∈ freeSet u v time t then φ ⟨i, h3⟩
    else false
  let monom : (t : Fin r) → (sep u v time t.castSucc → Bool) → (sep u v time t.succ → Bool) →
      (freeSet u v time t → Bool) → Finset (Fin m × Bool) := fun t σ τ φ =>
    (edgesAt u v time t).image (fun e => (e, decide (localVal t σ τ φ (u e) ≠ localVal t σ τ φ (v e))))
  let terms : (t : Fin r) → (Fin n → Bool) → Fin (w t.castSucc) → Fin (w t.succ) →
      List (Finset (Fin m × Bool)) := fun t s a b =>
    if ha : ∃ σ, enc t.castSucc σ = a then
      if hb : ∃ τ, enc t.succ τ = b then
        let σ := Classical.choose ha
        let τ := Classical.choose hb
        if consist t s σ τ then
          ((Finset.univ : Finset (freeSet u v time t → Bool)).filter (fun φ => allowedPhi t s φ)).toList.map
            (fun φ => monom t σ τ φ)
        else []
      else []
    else []
  refine ⟨start, last, terms, ?_, ?_⟩
  · intro t s a b
    dsimp only [terms]
    split_ifs with ha hb hc
    · rw [List.length_map, Finset.length_toList]
      calc ((Finset.univ : Finset (freeSet u v time t → Bool)).filter _).card
          ≤ (Finset.univ : Finset (freeSet u v time t → Bool)).card := Finset.card_filter_le _ _
        _ = 2 ^ (freeSet u v time t).card := by simp [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]
        _ ≤ 2 ^ (batch time t).card := Nat.pow_le_pow_right (by decide) (Finset.card_le_card Finset.sdiff_subset)
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  · intro p cost
    dsimp only
    let validPref : (q : Fin (r + 1)) → (sep u v time q → Bool) → (Fin n → Bool) → Prop :=
      fun q σ x =>
        (∀ i, i ∉ seen u v time q → x i = false) ∧
        (∀ i : sep u v time q, x i.1 = σ i) ∧
        (∀ i, (time i).val < q.val → p i = true → x i = false)
    let state : (q : Fin (r + 1)) → Fin (w q) → ℕ := fun q j =>
      if h : ∃ σ : sep u v time q → Bool, enc q σ = j then
        ∑ x : Fin n → Bool, if validPref q (Classical.choose h) x then
          ∏ e ∈ edgesBefore u v time q, cost e (decide (x (u e) ≠ x (v e))) else 0
      else 0
    have hstate_enc : ∀ (q : Fin (r + 1)) (σ : sep u v time q → Bool),
        state q (enc q σ) = ∑ x : Fin n → Bool, if validPref q σ x then
          ∏ e ∈ edgesBefore u v time q, cost e (decide (x (u e) ≠ x (v e))) else 0 := by
      intro q σ
      have hex : ∃ σ', enc q σ' = enc q σ := ⟨σ, rfl⟩
      simp only [state, hex, ↓reduceDIte]
      have hch : Classical.choose hex = σ := henc_inj q (Classical.choose_spec hex)
      rw [hch]
    refine ⟨state, ?_, ?_, ?_⟩
    · intro j
      by_cases hj : j = start
      · subst hj
        rw [if_pos rfl]
        change state 0 (enc 0 empty0) = 1
        rw [hstate_enc 0 empty0]
        rw [Finset.sum_eq_single (fun _ : Fin n => false)]
        · have hv : validPref 0 empty0 (fun _ => false) := by
            refine ⟨fun _ _ => rfl, fun i => False.elim (Finset.notMem_empty i.1 (sep_zero u v time ▸ i.2)),
              fun _ hlt _ => absurd hlt (Nat.not_lt_zero _)⟩
          simp [hv, edgesBefore_zero]
        · intro x _ hne
          have hnv : ¬ validPref 0 empty0 x := by
            intro hv
            apply hne
            funext i
            exact hv.1 i (by rw [seen_zero]; exact Finset.notMem_empty i)
          simp [hnv]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      · rw [if_neg hj]
        have hno : ¬ ∃ σ : sep u v time 0 → Bool, enc 0 σ = j := by
          rintro ⟨σ, rfl⟩
          apply hj
          have hσ : σ = empty0 := funext fun i => False.elim (Finset.notMem_empty i.1 (sep_zero u v time ▸ i.2))
          rw [hσ]
        simp [state, hno]
    · intro t b
      set s : Fin n → Bool := fun j => if time j = t then p j else false
      by_cases hb : ∃ τ : sep u v time t.succ → Bool, enc t.succ τ = b
      · rcases hb with ⟨τ, rfl⟩
        rw [hstate_enc t.succ τ]
        have hsum_enc' : (∑ a : Fin (w t.castSucc), state t.castSucc a *
            ((terms t s a (enc t.succ τ)).map (fun M => ∏ h ∈ M, cost h.1 h.2)).sum) =
            ∑ σ : sep u v time t.castSucc → Bool, state t.castSucc (enc t.castSucc σ) *
              ((terms t s (enc t.castSucc σ) (enc t.succ τ)).map (fun M => ∏ h ∈ M, cost h.1 h.2)).sum := by
          let img : Finset (Fin (w t.castSucc)) := Finset.univ.image (enc t.castSucc)
          rw [← Finset.sum_subset (Finset.subset_univ img)]
          · rw [Finset.sum_image (fun σ1 _ σ2 _ h => henc_inj t.castSucc h)]
          · intro a _ hnot
            have hno : ¬ ∃ σ, enc t.castSucc σ = a := by
              rintro ⟨σ, rfl⟩; exact hnot (Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩)
            simp [state, hno]
        rw [hsum_enc']
        have hterms_eval : ∀ σ : sep u v time t.castSucc → Bool,
            ((terms t s (enc t.castSucc σ) (enc t.succ τ)).map (fun M => ∏ h ∈ M, cost h.1 h.2)).sum =
            if consist t s σ τ then
              ∑ φ : freeSet u v time t → Bool, if allowedPhi t s φ then
                ∏ e ∈ edgesAt u v time t, cost e (decide (localVal t σ τ φ (u e) ≠ localVal t σ τ φ (v e)))
              else 0
            else 0 := by
          intro σ
          have ha : ∃ σ', enc t.castSucc σ' = enc t.castSucc σ := ⟨σ, rfl⟩
          have hb' : ∃ τ', enc t.succ τ' = enc t.succ τ := ⟨τ, rfl⟩
          have hcha : Classical.choose ha = σ := henc_inj t.castSucc (Classical.choose_spec ha)
          have hchb : Classical.choose hb' = τ := henc_inj t.succ (Classical.choose_spec hb')
          simp only [terms, ha, hb', ↓reduceDIte, hcha, hchb]
          by_cases hc : consist t s σ τ
          · simp only [hc, ↓reduceIte, List.map_map]
            have hlist_sum : ∀ (S : Finset (freeSet u v time t → Bool)) (f : (freeSet u v time t → Bool) → ℕ),
                (S.toList.map f).sum = ∑ φ ∈ S, f φ := fun S f => by
              rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]; rfl
            rw [hlist_sum, Finset.sum_filter]
            refine Finset.sum_congr rfl fun φ _ => ?_
            split_ifs
            · simp only [Function.comp_apply, monom]
              rw [Finset.prod_image (fun e1 _ e2 _ h => congrArg Prod.fst h)]
            · rfl
          · simp [hc]
        simp_rw [hstate_enc t.castSucc, hterms_eval]
        have hprod_expand :
            (∑ σ : sep u v time t.castSucc → Bool,
              (∑ x : Fin n → Bool, if validPref t.castSucc σ x then
                ∏ e ∈ edgesBefore u v time t.castSucc, cost e (decide (x (u e) ≠ x (v e))) else 0) *
              (if consist t s σ τ then
                ∑ φ : freeSet u v time t → Bool, if allowedPhi t s φ then
                  ∏ e ∈ edgesAt u v time t, cost e (decide (localVal t σ τ φ (u e) ≠ localVal t σ τ φ (v e)))
                else 0
              else 0)) =
            ∑ y : (Fin n → Bool) × (freeSet u v time t → Bool),
              let σ : sep u v time t.castSucc → Bool := fun i => y.1 i.1
              if validPref t.castSucc σ y.1 ∧ consist t s σ τ ∧ allowedPhi t s y.2 then
                (∏ e ∈ edgesBefore u v time t.castSucc, cost e (decide (y.1 (u e) ≠ y.1 (v e)))) *
                (∏ e ∈ edgesAt u v time t, cost e (decide (localVal t σ τ y.2 (u e) ≠ localVal t σ τ y.2 (v e))))
              else 0 := by
          rw [Fintype.sum_prod_type]
          trans (∑ x : Fin n → Bool, ∑ σ : sep u v time t.castSucc → Bool,
            (if validPref t.castSucc σ x then
              ∏ e ∈ edgesBefore u v time t.castSucc, cost e (decide (x (u e) ≠ x (v e))) else 0) *
            (if consist t s σ τ then
              ∑ φ : freeSet u v time t → Bool, if allowedPhi t s φ then
                ∏ e ∈ edgesAt u v time t, cost e (decide (localVal t σ τ φ (u e) ≠ localVal t σ τ φ (v e)))
              else 0
            else 0))
          · simp_rw [Finset.sum_mul]
            exact Finset.sum_comm
          · refine Finset.sum_congr rfl fun x _ => ?_
            let σx : sep u v time t.castSucc → Bool := fun i => x i.1
            rw [Finset.sum_eq_single σx]
            · dsimp only
              change ((if validPref t.castSucc σx x then
                  ∏ e ∈ edgesBefore u v time t.castSucc, cost e (decide (x (u e) ≠ x (v e))) else 0) *
                (if consist t s σx τ then
                  ∑ φ : freeSet u v time t → Bool, if allowedPhi t s φ then
                    ∏ e ∈ edgesAt u v time t, cost e (decide (localVal t σx τ φ (u e) ≠ localVal t σx τ φ (v e)))
                  else 0
                else 0)) =
                ∑ φ : freeSet u v time t → Bool,
                  if validPref t.castSucc σx x ∧ consist t s σx τ ∧ allowedPhi t s φ then
                    (∏ e ∈ edgesBefore u v time t.castSucc, cost e (decide (x (u e) ≠ x (v e)))) *
                    (∏ e ∈ edgesAt u v time t, cost e (decide (localVal t σx τ φ (u e) ≠ localVal t σx τ φ (v e))))
                  else 0
              by_cases hvp : validPref t.castSucc σx x
              · by_cases hc : consist t s σx τ
                · simp only [hvp, hc, ↓reduceIte, true_and, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun φ _ => ?_
                  by_cases hφ : allowedPhi t s φ <;> simp [hφ]
                · simp [hvp, hc]
              · simp [hvp]
            · intro σ _ hne
              have hnv : ¬ validPref t.castSucc σ x := by
                intro hv; apply hne; funext i; exact (hv.2.1 i).symm
              simp [hnv]
            · intro hnot; exact absurd (Finset.mem_univ _) hnot
        rw [hprod_expand]
        let S1 : Finset (Fin n → Bool) := Finset.univ.filter (fun x => validPref t.succ τ x)
        let S2 : Finset ((Fin n → Bool) × (freeSet u v time t → Bool)) :=
          Finset.univ.filter (fun y =>
            let σ : sep u v time t.castSucc → Bool := fun i => y.1 i.1
            validPref t.castSucc σ y.1 ∧ consist t s σ τ ∧ allowedPhi t s y.2)
        rw [← Finset.sum_filter, ← Finset.sum_filter]
        let fwd : (Fin n → Bool) → (Fin n → Bool) × (freeSet u v time t → Bool) := fun x =>
          (fun i => if i ∈ seen u v time t.castSucc then x i else false, fun i => x i.1)
        let bwd : (Fin n → Bool) × (freeSet u v time t → Bool) → (Fin n → Bool) := fun y i =>
          if i ∈ seen u v time t.castSucc then y.1 i
          else if h2 : i ∈ sep u v time t.succ then τ ⟨i, h2⟩
          else if h3 : i ∈ freeSet u v time t then y.2 ⟨i, h3⟩
          else false
        refine Finset.sum_nbij' fwd bwd ?_ ?_ ?_ ?_ ?_
        · intro x hx
          have hv : validPref t.succ τ x := (Finset.mem_filter.mp hx).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
          · refine ⟨fun i hi => by simp [fwd, hi], fun i => by
              have hmem : i.1 ∈ seen u v time t.castSucc := Finset.mem_union_right _ i.2
              simp [fwd, hmem], fun i hlt hp => by
              have hmem : i ∈ seen u v time t.castSucc :=
                Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
              simp only [fwd, hmem, ↓reduceIte]
              exact hv.2.2 i (by simp only [Fin.val_succ]; simp only [Fin.coe_castSucc] at hlt; omega) hp⟩
          · refine ⟨fun i h1 h2 => ?_, fun i h1 ht hs => ?_, fun i h2 ht hs => ?_⟩
            · have hmem : i ∈ seen u v time t.castSucc := Finset.mem_union_right _ h1
              simp only [fwd, hmem, ↓reduceIte]
              exact hv.2.1 ⟨i, h2⟩
            · have hmem : i ∈ seen u v time t.castSucc := Finset.mem_union_right _ h1
              simp only [fwd, hmem, ↓reduceIte]
              have hp : p i = true := by simpa [s, ht] using hs
              exact hv.2.2 i (by simp [ht]) hp
            · have hp : p i = true := by simpa [s, ht] using hs
              rw [← hv.2.1 ⟨i, h2⟩]
              exact hv.2.2 i (by simp [ht]) hp
          · intro i hs
            have ht : time i.1 = t := (Finset.mem_filter.mp (Finset.mem_sdiff.mp i.2).1).2
            have hp : p i.1 = true := by simpa [s, ht] using hs
            exact hv.2.2 i.1 (by simp [ht]) hp
        · intro y hy
          rcases (Finset.mem_filter.mp hy).2 with ⟨hv, hc, hφ⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
          · intro i hnot
            have hn1 : i ∉ seen u v time t.castSucc := fun h => hnot (seen_mono_step u v time t h)
            have hn2 : i ∉ sep u v time t.succ := fun h => hnot (Finset.mem_union_right _ h)
            have hn3 : i ∉ freeSet u v time t := by
              intro h
              have ht : time i = t := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
              exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [ht]⟩))
            simp [bwd, hn1, hn2, hn3]
          · intro i
            by_cases h1 : i.1 ∈ seen u v time t.castSucc
            · have hsep1 : i.1 ∈ sep u v time t.castSucc :=
                sep_succ_inter_seen_castSucc u v time t i.2 h1
              simp only [bwd, h1, ↓reduceIte]
              exact hc.1 i.1 hsep1 i.2
            · simp [bwd, h1, i.2]
          · intro i hlt hp
            simp only [Fin.val_succ] at hlt
            by_cases hlt' : (time i).val < t.val
            · have h1 : i ∈ seen u v time t.castSucc :=
                Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩)
              simp only [bwd, h1, ↓reduceIte]
              exact hv.2.2 i hlt' hp
            · have ht : time i = t := Fin.ext (by omega)
              have hs : s i = true := by simp [s, ht, hp]
              by_cases h1 : i ∈ seen u v time t.castSucc
              · have hsep1 : i ∈ sep u v time t.castSucc := by
                  simp only [seen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
                    true_and, Fin.coe_castSucc] at h1
                  exact h1.resolve_left hlt'
                simp only [bwd, h1, ↓reduceIte]
                exact hc.2.1 i hsep1 ht hs
              · by_cases h2 : i ∈ sep u v time t.succ
                · simp only [bwd, h1, h2, ↓reduceDIte, ↓reduceIte]
                  exact hc.2.2 i h2 ht hs
                · have h3 : i ∈ freeSet u v time t := by
                    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
                    simp only [Finset.mem_union, not_or]
                    exact ⟨fun h => h1 (Finset.mem_union_right _ h), h2⟩
                  simp only [bwd, h1, h2, h3, ↓reduceDIte, ↓reduceIte]
                  exact hφ ⟨i, h3⟩ hs
        · intro x hx
          have hv : validPref t.succ τ x := (Finset.mem_filter.mp hx).2
          funext i
          by_cases h1 : i ∈ seen u v time t.castSucc
          · simp [bwd, fwd, h1]
          · by_cases h2 : i ∈ sep u v time t.succ
            · simp only [bwd, fwd, h1, h2, ↓reduceDIte, ↓reduceIte]
              exact (hv.2.1 ⟨i, h2⟩).symm
            · by_cases h3 : i ∈ freeSet u v time t
              · simp [bwd, fwd, h1, h2, h3]
              · simp only [bwd, fwd, h1, h2, h3, ↓reduceDIte, ↓reduceIte]
                have hnot : i ∉ seen u v time t.succ := by
                  intro hmem
                  simp only [seen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
                    true_and, Fin.val_succ] at hmem
                  have hlt := hmem.resolve_right h2
                  have hge : ¬ ((time i).val < t.val) := fun h =>
                    h1 (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
                  have ht : time i = t := Fin.ext (by omega)
                  apply h3
                  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
                  simp only [Finset.mem_union, not_or]
                  exact ⟨fun h => h1 (Finset.mem_union_right _ h), h2⟩
                exact (hv.1 i hnot).symm
        · intro y hy
          rcases (Finset.mem_filter.mp hy).2 with ⟨hv, hc, hφ⟩
          refine Prod.ext ?_ ?_
          · funext i
            by_cases h1 : i ∈ seen u v time t.castSucc
            · simp [fwd, bwd, h1]
            · simp only [fwd, bwd, h1, ↓reduceIte]
              exact (hv.1 i h1).symm
          · funext i
            have hn1 : i.1 ∉ seen u v time t.castSucc := by
              have hmem := Finset.mem_sdiff.mp i.2
              have ht : time i.1 = t := (Finset.mem_filter.mp hmem.1).2
              have hnotu := hmem.2
              simp only [Finset.mem_union, not_or] at hnotu
              simp only [seen, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
                Fin.coe_castSucc, ht, lt_self_iff_false, false_or]
              exact hnotu.1
            have hn2 : i.1 ∉ sep u v time t.succ := by
              have hnotu := (Finset.mem_sdiff.mp i.2).2
              simp only [Finset.mem_union, not_or] at hnotu
              exact hnotu.2
            simp [fwd, bwd, hn1, hn2, i.2]
        · intro x hx
          have hv : validPref t.succ τ x := (Finset.mem_filter.mp hx).2
          rw [edgesBefore_succ, Finset.prod_union (edgesBefore_disj_edgesAt u v time t)]
          congr 1
          · refine Finset.prod_congr rfl fun e he => ?_
            have hseen := edgesBefore_endpoints_seen u v time t.castSucc he
            simp [fwd, hseen.1, hseen.2]
          · refine Finset.prod_congr rfl fun e he => ?_
            have ho : owner u v time e = t := (Finset.mem_filter.mp he).2
            have hav := owner_mem u v time e
            rw [ho] at hav
            have hloc : ∀ z, z ∈ avail u v time t →
                localVal t (fun i => (fwd x).1 i.1) τ (fwd x).2 z = x z := by
              intro z hz
              by_cases h1 : z ∈ sep u v time t.castSucc
              · have hs1 : z ∈ seen u v time t.castSucc := Finset.mem_union_right _ h1
                simp [localVal, fwd, h1, hs1]
              · by_cases h2 : z ∈ sep u v time t.succ
                · simp only [localVal, h1, h2, ↓reduceDIte]
                  exact (hv.2.1 ⟨z, h2⟩).symm
                · have h3 : z ∈ freeSet u v time t := by
                    simp only [avail, Finset.mem_union] at hz
                    have hbt : z ∈ batch time t := by
                      rcases hz with (h | h) | h
                      · exact absurd h h1
                      · exact absurd h h2
                      · exact h
                    exact Finset.mem_sdiff.mpr ⟨hbt, by simp [h1, h2]⟩
                  simp [localVal, fwd, h1, h2, h3]
            rw [hloc (u e) hav.1, hloc (v e) hav.2]
      · simp only [state, hb, ↓reduceDIte]
        symm
        refine Finset.sum_eq_zero fun a _ => ?_
        simp [terms, hb]
    · change state (Fin.last r) (enc (Fin.last r) emptyR) = _
      rw [hstate_enc (Fin.last r) emptyR]
      refine Finset.sum_congr rfl fun x _ => ?_
      have hiff : validPref (Fin.last r) emptyR x ↔ ∀ i : Fin n, p i = true → x i = false := by
        constructor
        · intro hv i hp; exact hv.2.2 i (time i).isLt hp
        · intro hx
          refine ⟨fun i hi => absurd (Finset.mem_univ i) (seen_last u v time ▸ hi),
            fun i => False.elim (Finset.notMem_empty i.1 (sep_last u v time ▸ i.2)), fun i _ hp => hx i hp⟩
      by_cases hx : ∀ i : Fin n, p i = true → x i = false
      · have hv : validPref (Fin.last r) emptyR x := hiff.mpr hx
        rw [if_pos hv, if_pos hx, edgesBefore_last]
      · have hnv : ¬ validPref (Fin.last r) emptyR x := fun hv => hx (hiff.mp hv)
        rw [if_neg hnv, if_neg hx]

end ReaderConstruction

section LowerBound

open Classical in
lemma reader_to_enough {n m r : ℕ} (u v : Fin m → Fin n) (time : Fin n → Fin r)
    (w : Fin (r + 1) → ℕ)
    (start : Fin (w 0)) (last : Fin (w (Fin.last r)))
    (terms : (t : Fin r) → (Fin n → Bool) → Fin (w t.castSucc) → Fin (w t.succ) →
      List (Finset (Fin m × Bool)))
    (hrun : ∀ (p : Fin n → Bool) (cost : Fin m → Bool → ℕ),
      let total := ∑ x : Fin n → Bool, if (∀ i, p i = true → x i = false) then
        ∏ e : Fin m, cost e (decide (x (u e) ≠ x (v e))) else 0
      ∃ state : (q : Fin (r + 1)) → Fin (w q) → ℕ,
        (∀ j, state 0 j = if j = start then 1 else 0) ∧
        (∀ (t : Fin r) (b : Fin (w t.succ)),
          let s := fun j : Fin n => if time j = t then p j else false
          state t.succ b = ∑ a : Fin (w t.castSucc), state t.castSucc a *
            ((terms t s a b).map (fun M => ∏ h ∈ M, cost h.1 h.2)).sum) ∧
        state (Fin.last r) last = total) :
    ∀ (q : Fin (r + 1)) (M : Finset (Fin n × Fin n)), validM u v time q M → 2 ^ M.card ≤ w q := by
  intro q M hM
  set k := M.card
  let eM : Fin k ≃ M := (Fintype.equivFinOfCardEq (Fintype.card_coe M)).symm
  let aL : Fin k → Fin n := fun j => (eM j).1.1
  let bR : Fin k → Fin n := fun j => (eM j).1.2
  have haL_lt : ∀ j : Fin k, (time (aL j)).val < q.val := fun j => (hM.1 (eM j).1 (eM j).2).1
  have hbR_ge : ∀ j : Fin k, q.val ≤ (time (bR j)).val := fun j => (hM.1 (eM j).1 (eM j).2).2.1
  have haL_inj : Function.Injective aL := fun j1 j2 h =>
    eM.injective (Subtype.ext (hM.2.1 (eM j1).2 (eM j2).2 h))
  have hbR_inj : Function.Injective bR := fun j1 j2 h =>
    eM.injective (Subtype.ext (hM.2.2 (eM j1).2 (eM j2).2 h))
  have hdisj_ab : ∀ j1 j2 : Fin k, aL j1 ≠ bR j2 := by
    intro j1 j2 h
    have h1 := haL_lt j1
    have h2 := hbR_ge j2
    rw [h] at h1
    omega
  let edgeM : Fin k → Fin m := fun j => Classical.choose (hM.1 (eM j).1 (eM j).2).2.2
  have hedgeM_spec : ∀ j : Fin k,
      (u (edgeM j) = aL j ∧ v (edgeM j) = bR j) ∨ (u (edgeM j) = bR j ∧ v (edgeM j) = aL j) :=
    fun j => Classical.choose_spec (hM.1 (eM j).1 (eM j).2).2.2
  let costM : Fin m → Bool → ℕ := fun e b =>
    if ∃ j : Fin k, edgeM j = e then (if b = false then 1 else 0) else 1
  let pOf : (Fin k → Bool) → (Fin k → Bool) → (Fin n → Bool) := fun α β i =>
    if h1 : ∃ j : Fin k, aL j = i then α (Classical.choose h1)
    else if h2 : ∃ j : Fin k, bR j = i then β (Classical.choose h2)
    else true
  have hpOf_a : ∀ α β (j : Fin k), pOf α β (aL j) = α j := by
    intro α β j
    have hex : ∃ j', aL j' = aL j := ⟨j, rfl⟩
    simp only [pOf, hex, ↓reduceDIte]
    rw [haL_inj (Classical.choose_spec hex)]
  have hpOf_b : ∀ α β (j : Fin k), pOf α β (bR j) = β j := by
    intro α β j
    have hna : ¬ ∃ j', aL j' = bR j := by rintro ⟨j', hj'⟩; exact hdisj_ab j' j hj'
    have hex : ∃ j', bR j' = bR j := ⟨j, rfl⟩
    simp only [pOf, hna, hex, ↓reduceDIte]
    rw [hbR_inj (Classical.choose_spec hex)]
  have hpOf_other : ∀ α β (i : Fin n), (∀ j, aL j ≠ i) → (∀ j, bR j ≠ i) → pOf α β i = true := by
    intro α β i hna hnb
    have h1 : ¬ ∃ j, aL j = i := by rintro ⟨j, hj⟩; exact hna j hj
    have h2 : ¬ ∃ j, bR j = i := by rintro ⟨j, hj⟩; exact hnb j hj
    simp [pOf, h1, h2]
  have htotal_val : ∀ α β : Fin k → Bool,
      (∑ x : Fin n → Bool, if (∀ i, pOf α β i = true → x i = false) then
        ∏ e : Fin m, costM e (decide (x (u e) ≠ x (v e))) else 0) =
      ∏ j : Fin k, if α j = false ∧ β j = false then 2 else 1 := by
    intro α β
    have hprod_eval : ∀ x : Fin n → Bool,
        (∏ e : Fin m, costM e (decide (x (u e) ≠ x (v e)))) =
        if (∀ j : Fin k, x (aL j) = x (bR j)) then 1 else 0 := by
      intro x
      by_cases hmatch : ∀ j : Fin k, x (aL j) = x (bR j)
      · rw [if_pos hmatch]
        refine Finset.prod_eq_one fun e _ => ?_
        dsimp only [costM]
        split_ifs with he hd
        · rfl
        · exfalso
          rcases he with ⟨j, rfl⟩
          have hxj := hmatch j
          rcases hedgeM_spec j with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · rw [hu, hv, hxj] at hd; simp at hd
          · rw [hu, hv, hxj] at hd; simp at hd
        · rfl
      · rw [if_neg hmatch]
        push Not at hmatch
        rcases hmatch with ⟨j, hj⟩
        refine Finset.prod_eq_zero (Finset.mem_univ (edgeM j)) ?_
        have hex : ∃ j', edgeM j' = edgeM j := ⟨j, rfl⟩
        have hne : decide (x (u (edgeM j)) ≠ x (v (edgeM j))) = true := by
          rcases hedgeM_spec j with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · rw [hu, hv]; simp [hj]
          · rw [hu, hv]; simp [Ne.symm hj]
        simp [costM, hex, hne]
    simp_rw [hprod_eval]
    have hsum_eq : (∑ x : Fin n → Bool,
        if (∀ i, pOf α β i = true → x i = false) then
          (if (∀ j : Fin k, x (aL j) = x (bR j)) then 1 else 0)
        else 0) =
        ∑ y : Fin k → Bool,
          if (∀ j : Fin k, (α j = true → y j = false) ∧ (β j = true → y j = false)) then 1 else 0 := by
      let S1 := (Finset.univ : Finset (Fin n → Bool)).filter
        (fun x => (∀ i, pOf α β i = true → x i = false) ∧ (∀ j : Fin k, x (aL j) = x (bR j)))
      let S2 := (Finset.univ : Finset (Fin k → Bool)).filter
        (fun y => ∀ j : Fin k, (α j = true → y j = false) ∧ (β j = true → y j = false))
      trans S1.card
      · rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun x _ => by split_ifs <;> simp_all
      · trans S2.card
        · refine Finset.card_bij' (fun x _ => fun j => x (aL j))
            (fun y _ => fun i =>
              if h1 : ∃ j, aL j = i then y (Classical.choose h1)
              else if h2 : ∃ j, bR j = i then y (Classical.choose h2)
              else false) ?_ ?_ ?_ ?_
          · intro x hx
            rcases (Finset.mem_filter.mp hx).2 with ⟨hp, hmatch⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ⟨?_, ?_⟩⟩
            · intro hα; dsimp only; exact hp (aL j) (by rw [hpOf_a, hα])
            · intro hβ; dsimp only; rw [hmatch j]; exact hp (bR j) (by rw [hpOf_b, hβ])
          · intro y hy
            have hy' := (Finset.mem_filter.mp hy).2
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩
            · intro i hpi
              by_cases h1 : ∃ j, aL j = i
              · rcases h1 with ⟨j, rfl⟩
                have hex : ∃ j', aL j' = aL j := ⟨j, rfl⟩
                simp only [hex, ↓reduceDIte]
                rw [haL_inj (Classical.choose_spec hex)]
                exact (hy' j).1 (by rwa [hpOf_a] at hpi)
              · by_cases h2 : ∃ j, bR j = i
                · rcases h2 with ⟨j, rfl⟩
                  have hex : ∃ j', bR j' = bR j := ⟨j, rfl⟩
                  simp only [h1, hex, ↓reduceDIte]
                  rw [hbR_inj (Classical.choose_spec hex)]
                  exact (hy' j).2 (by rwa [hpOf_b] at hpi)
                · simp [h1, h2]
            · intro j
              have h1 : ∃ j', aL j' = aL j := ⟨j, rfl⟩
              have hna : ¬ ∃ j', aL j' = bR j := by rintro ⟨j', hj'⟩; exact hdisj_ab j' j hj'
              have h2 : ∃ j', bR j' = bR j := ⟨j, rfl⟩
              simp only [h1, hna, h2, ↓reduceDIte]
              rw [haL_inj (Classical.choose_spec h1), hbR_inj (Classical.choose_spec h2)]
          · intro x hx
            rcases (Finset.mem_filter.mp hx).2 with ⟨hp, hmatch⟩
            funext i
            by_cases h1 : ∃ j, aL j = i
            · rcases h1 with ⟨j, rfl⟩
              have hex : ∃ j', aL j' = aL j := ⟨j, rfl⟩
              simp only [hex, ↓reduceDIte]
              rw [haL_inj (Classical.choose_spec hex)]
            · by_cases h2 : ∃ j, bR j = i
              · rcases h2 with ⟨j, rfl⟩
                have hex : ∃ j', bR j' = bR j := ⟨j, rfl⟩
                simp only [h1, hex, ↓reduceDIte]
                rw [hbR_inj (Classical.choose_spec hex), hmatch j]
              · simp only [h1, h2, ↓reduceDIte]
                have hna : ∀ j, aL j ≠ i := fun j hj => h1 ⟨j, hj⟩
                have hnb : ∀ j, bR j ≠ i := fun j hj => h2 ⟨j, hj⟩
                exact (hp i (hpOf_other α β i hna hnb)).symm
          · intro y _
            funext j
            have h1 : ∃ j', aL j' = aL j := ⟨j, rfl⟩
            simp only [h1, ↓reduceDIte]
            rw [haL_inj (Classical.choose_spec h1)]
        · rw [Finset.card_filter]
    rw [hsum_eq]
    have hprod_sum : (∏ j : Fin k, if α j = false ∧ β j = false then (2 : ℕ) else 1) =
        ∏ j : Fin k, ∑ b : Bool, if (α j = true → b = false) ∧ (β j = true → b = false) then 1 else 0 := by
      refine Finset.prod_congr rfl fun j _ => ?_
      cases α j <;> cases β j <;> decide
    rw [hprod_sum, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : ∀ j : Fin k, (α j = true → y j = false) ∧ (β j = true → y j = false)
    · rw [if_pos hy]; symm; exact Finset.prod_eq_one fun j _ => if_pos (hy j)
    · rw [if_neg hy]
      have hex : ∃ j : Fin k, ¬ ((α j = true → y j = false) ∧ (β j = true → y j = false)) := by
        by_contra hall
        apply hy
        intro j
        by_contra hj
        exact hall ⟨j, hj⟩
      rcases hex with ⟨j, hj⟩
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  let stepW : (t : Fin r) → (Fin n → Bool) → Fin (w t.castSucc) → Fin (w t.succ) → ℚ :=
    fun t s a b => (((terms t s a b).map (fun S => ∏ h ∈ S, costM h.1 h.2)).sum : ℚ)
  let sL : (Fin k → Bool) → (t : Fin r) → Fin n → Bool :=
    fun α t j => if time j = t then pOf α (fun _ => true) j else false
  let sR : (Fin k → Bool) → (t : Fin r) → Fin n → Bool :=
    fun β t j => if time j = t then pOf (fun _ => true) β j else false
  have hsL_eq : ∀ α β (t : Fin r), t.val < q.val →
      (fun j : Fin n => if time j = t then pOf α β j else false) = sL α t := by
    intro α β t ht
    funext j
    by_cases hj : time j = t
    · simp only [sL, hj, ↓reduceIte]
      have hnb : ∀ l : Fin k, bR l ≠ j := by
        intro l hl
        have hge := hbR_ge l
        rw [hl, hj] at hge
        omega
      by_cases h1 : ∃ l, aL l = j
      · rcases h1 with ⟨l, rfl⟩; rw [hpOf_a α β l, hpOf_a α (fun _ => true) l]
      · have hna : ∀ l, aL l ≠ j := fun l hl => h1 ⟨l, hl⟩
        rw [hpOf_other α β j hna hnb, hpOf_other α (fun _ => true) j hna hnb]
    · simp [sL, hj]
  have hsR_eq : ∀ α β (t : Fin r), q.val ≤ t.val →
      (fun j : Fin n => if time j = t then pOf α β j else false) = sR β t := by
    intro α β t ht
    funext j
    by_cases hj : time j = t
    · simp only [sR, hj, ↓reduceIte]
      have hna : ∀ l : Fin k, aL l ≠ j := by
        intro l hl
        have hlt := haL_lt l
        rw [hl, hj] at hlt
        omega
      by_cases h2 : ∃ l, bR l = j
      · rcases h2 with ⟨l, rfl⟩; rw [hpOf_b α β l, hpOf_b (fun _ => true) β l]
      · have hnb : ∀ l, bR l ≠ j := fun l hl => h2 ⟨l, hl⟩
        rw [hpOf_other α β j hna hnb, hpOf_other (fun _ => true) β j hna hnb]
    · simp [sR, hj]
  let fwdVec : (d : ℕ) → (hd : d ≤ r) → (Fin k → Bool) → Fin (w ⟨d, Nat.lt_succ_of_le hd⟩) → ℚ :=
    fun d => Nat.rec
      (fun _ _ j => if j = start then (1 : ℚ) else 0)
      (fun d ih hd α b =>
        ∑ a : Fin (w ⟨d, Nat.lt_succ_of_le (Nat.le_of_succ_le hd)⟩),
          ih (Nat.le_of_succ_le hd) α a * stepW ⟨d, hd⟩ (sL α ⟨d, hd⟩) a b)
      d
  let bwdVec : (d : ℕ) → (hd : d ≤ r) → (Fin k → Bool) → Fin (w ⟨r - d, by omega⟩) → ℚ :=
    fun d => Nat.rec
      (fun _ _ a => if a = last then (1 : ℚ) else 0)
      (fun d ih hd β a =>
        ∑ b : Fin (w ⟨r - d, by omega⟩),
          stepW ⟨r - (d + 1), by omega⟩ (sR β ⟨r - (d + 1), by omega⟩) a
            (Fin.cast (by congr 1; ext; dsimp; omega) b) *
          ih (Nat.le_of_succ_le hd) β b)
      d
  let Lmat : Matrix (Fin k → Bool) (Fin (w q)) ℚ :=
    fun α a => fwdVec q.val (Nat.le_of_lt_succ q.isLt) α a
  let Rmat : Matrix (Fin (w q)) (Fin k → Bool) ℚ :=
    fun a β => bwdVec (r - q.val) (Nat.sub_le r q.val) β
      (Fin.cast (by congr 1; ext; dsimp; omega) a)
  let Hmat : Matrix (Fin k → Bool) (Fin k → Bool) ℚ :=
    fun α β => ∏ j : Fin k, if α j = false ∧ β j = false then (2 : ℚ) else 1
  have hLR : Lmat * Rmat = Hmat := by
    ext α β
    rcases hrun (pOf α β) costM with ⟨state, hst0, hstep, hlast⟩
    have hst_cast_fn : ∀ (q1 q2 : Fin (r + 1)) (h : q1 = q2) (x : Fin (w q1)),
        state q1 x = state q2 (Fin.cast (by rw [h]) x) := by
      rintro q1 _ rfl x; rfl
    have hfwd_eq : ∀ (d : ℕ) (hd : d ≤ q.val) (a : Fin (w ⟨d, by omega⟩)),
        (state ⟨d, by omega⟩ a : ℚ) = fwdVec d (by omega) α a := by
      intro d
      induction d with
      | zero =>
        intro hd a
        change (state 0 a : ℚ) = if a = start then (1 : ℚ) else 0
        rw [hst0 a]
        split_ifs <;> first | exact Nat.cast_one | exact Nat.cast_zero | contradiction
      | succ d ih =>
        intro hd a
        let t : Fin r := ⟨d, by omega⟩
        have hst := hstep t a
        dsimp only at hst
        have hcast : (state ⟨d + 1, by omega⟩ a : ℚ) =
            ∑ x : Fin (w t.castSucc), (state t.castSucc x : ℚ) *
              stepW t (fun j => if time j = t then pOf α β j else false) x a := by
          change (state t.succ a : ℚ) = _
          rw [hst, Nat.cast_sum]
          refine Finset.sum_congr rfl fun x _ => by rw [Nat.cast_mul]
        rw [hcast, hsL_eq α β t (by simp [t]; omega)]
        change (∑ x : Fin (w ⟨d, by omega⟩), (state ⟨d, by omega⟩ x : ℚ) *
            stepW ⟨d, by omega⟩ (sL α ⟨d, by omega⟩) x a) =
          ∑ x : Fin (w ⟨d, by omega⟩), fwdVec d (by omega) α x *
            stepW ⟨d, by omega⟩ (sL α ⟨d, by omega⟩) x a
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [ih (by omega) x]
    have hbwd_eq : ∀ (d : ℕ) (hd : d ≤ r - q.val),
        (∑ a : Fin (w ⟨r - d, by omega⟩),
          (state ⟨r - d, by omega⟩ a : ℚ) * bwdVec d (by omega) β a) =
        (state (Fin.last r) last : ℚ) := by
      intro d
      induction d with
      | zero =>
        intro hd
        change (∑ a : Fin (w (Fin.last r)), (state (Fin.last r) a : ℚ) *
            (if a = last then (1 : ℚ) else 0)) = (state (Fin.last r) last : ℚ)
        rw [Finset.sum_eq_single last]
        · simp
        · intro a _ hne; simp [hne]
        · intro hnot; exact absurd (Finset.mem_univ _) hnot
      | succ d ih =>
        intro hd
        let t : Fin r := ⟨r - (d + 1), by omega⟩
        have ht_ge : q.val ≤ t.val := by simp [t]; omega
        have ht_succ : t.succ = ⟨r - d, by omega⟩ := Fin.ext (by simp [t]; omega)
        have hstep_q : ∀ b : Fin (w ⟨r - d, by omega⟩),
            (state ⟨r - d, by omega⟩ b : ℚ) =
            ∑ a : Fin (w t.castSucc), (state t.castSucc a : ℚ) *
              stepW t (sR β t) a (Fin.cast (by rw [ht_succ]) b) := by
          intro b
          have hb_eq := hstep t (Fin.cast (by rw [ht_succ]) b)
          dsimp only at hb_eq
          have hst_c : state ⟨r - d, by omega⟩ b = state t.succ (Fin.cast (by rw [ht_succ]) b) :=
            hst_cast_fn ⟨r - d, by omega⟩ t.succ ht_succ.symm b
          rw [hst_c, hb_eq, Nat.cast_sum]
          refine Finset.sum_congr rfl fun a _ => by
            rw [Nat.cast_mul, hsR_eq α β t ht_ge]
        rw [← ih (by omega)]
        simp_rw [hstep_q, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hstep_bwd : bwdVec (d + 1) (by omega) β a =
            ∑ b : Fin (w ⟨r - d, by omega⟩),
              stepW t (sR β t) a (Fin.cast (by rw [ht_succ]) b) * bwdVec d (by omega) β b := rfl
        rw [hstep_bwd, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        change (state t.castSucc a : ℚ) * (stepW t (sR β t) a (Fin.cast (by rw [ht_succ]) b) *
            bwdVec d (by omega) β b) =
          (state t.castSucc a : ℚ) * stepW t (sR β t) a (Fin.cast (by rw [ht_succ]) b) *
            bwdVec d (by omega) β b
        rw [mul_assoc]
    rw [Matrix.mul_apply]
    have hq_sub : (⟨r - (r - q.val), by omega⟩ : Fin (r + 1)) = q := Fin.ext (by simp; omega)
    have h1 : (∑ a : Fin (w q), Lmat α a * Rmat a β) =
        ∑ a : Fin (w ⟨r - (r - q.val), by omega⟩),
          (state ⟨r - (r - q.val), by omega⟩ a : ℚ) * bwdVec (r - q.val) (Nat.sub_le r q.val) β a := by
      have hL_eq : ∀ a : Fin (w q), Lmat α a = (state q a : ℚ) := fun a =>
        (hfwd_eq q.val (le_refl _) a).symm
      simp_rw [hL_eq]
      refine Finset.sum_equiv (finCongr (congrArg w hq_sub.symm)) (fun _ => by simp) ?_
      intro a _
      dsimp only [Rmat, finCongr]
      congr 1
      exact congrArg (fun z : ℕ => (z : ℚ)) (hst_cast_fn q ⟨r - (r - q.val), by omega⟩ hq_sub.symm a)
    rw [h1, hbwd_eq (r - q.val) (le_refl _), hlast]
    dsimp only [Hmat]
    rw [htotal_val α β, Nat.cast_prod]
    refine Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
  let Kmat : Matrix (Fin k → Bool) (Fin k → Bool) ℚ :=
    fun β γ => ∏ j : Fin k,
      if β j = false ∧ γ j = false then (1 : ℚ)
      else if β j = true ∧ γ j = true then 2 else -1
  have hHK : Hmat * Kmat = 1 := by
    ext α γ
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hmul : (∑ β : Fin k → Bool, Hmat α β * Kmat β γ) =
        ∑ β : Fin k → Bool, ∏ j : Fin k,
          ((if α j = false ∧ β j = false then (2 : ℚ) else 1) *
           (if β j = false ∧ γ j = false then (1 : ℚ)
            else if β j = true ∧ γ j = true then 2 else -1)) := by
      refine Finset.sum_congr rfl fun β _ => (Finset.prod_mul_distrib).symm
    have hps := Fintype.prod_sum (fun j b =>
      (if α j = false ∧ b = false then (2 : ℚ) else 1) *
      (if b = false ∧ γ j = false then (1 : ℚ)
       else if b = true ∧ γ j = true then 2 else -1))
    rw [hmul, ← hps]
    have hfactor : ∀ j : Fin k,
        (∑ b : Bool,
          (if α j = false ∧ b = false then (2 : ℚ) else 1) *
          (if b = false ∧ γ j = false then (1 : ℚ)
           else if b = true ∧ γ j = true then 2 else -1)) =
        if α j = γ j then 1 else 0 := by
      intro j
      cases α j <;> cases γ j <;> simp <;> norm_num
    simp_rw [hfactor]
    by_cases heq : α = γ
    · subst heq; simp
    · rw [if_neg heq]
      have hex : ∃ j : Fin k, α j ≠ γ j := by
        by_contra hall; push Not at hall; exact heq (funext hall)
      rcases hex with ⟨j, hj⟩
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  have hsurj : Function.Surjective (Matrix.mulVecLin Lmat) := by
    intro y
    refine ⟨Matrix.mulVecLin (Rmat * Kmat) y, ?_⟩
    change Matrix.mulVec Lmat (Matrix.mulVec (Rmat * Kmat) y) = y
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hLR, hHK, Matrix.one_mulVec]
  have hfin : Module.finrank ℚ ((Fin k → Bool) → ℚ) ≤ Module.finrank ℚ (Fin (w q) → ℚ) :=
    LinearMap.finrank_le_finrank_of_surjective hsurj
  simpa [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool] using hfin

end LowerBound

end PEqualNP.Outside.L_pcx_430_aux

theorem PEqualNP.Outside.L_pcx_430 : ∀ (n m r : ℕ) (u v : Fin m → Fin n) (time : Fin n → Fin r) (w : Fin (r+1) → ℕ),
  let I := Fin n
  let P := I → Bool
  let valid := fun (q : Fin (r+1)) (M : Finset (I × I)) =>
    (∀ p ∈ M, (time p.1).val < q.val ∧ q.val ≤ (time p.2).val ∧ ∃ e : Fin m,
      (u e = p.1 ∧ v e = p.2) ∨ (u e = p.2 ∧ v e = p.1)) ∧
    Set.InjOn Prod.fst (↑M : Set (I × I)) ∧ Set.InjOn Prod.snd (↑M : Set (I × I))
  let enough := ∀ (q : Fin (r+1)) (M : Finset (I × I)), valid q M → 2^M.card ≤ w q
  let reader := ∃ (start : Fin (w 0)) (last : Fin (w (Fin.last r)))
      (terms : (t : Fin r) → P → Fin (w t.castSucc) → Fin (w t.succ) →
        List (Finset (Fin m × Bool))),
    (∀ t s a b, (terms t s a b).length ≤
      2^((Finset.univ.filter (fun j : I => time j = t)).card)) ∧
    ∀ (p : P) (cost : Fin m → Bool → ℕ),
      let total := ∑ x : P, if (∀ i, p i = true → x i = false) then
        ∏ e : Fin m, cost e (decide (x (u e) ≠ x (v e))) else 0
      ∃ state : (q : Fin (r+1)) → Fin (w q) → ℕ,
        (∀ j, state 0 j = if j = start then 1 else 0) ∧
        (∀ (t : Fin r) (b : Fin (w t.succ)),
          let s := fun j : I => if time j = t then p j else false
          state t.succ b = ∑ a : Fin (w t.castSucc), state t.castSucc a *
            ((terms t s a b).map (fun M =>
              ∏ h ∈ M, cost h.1 h.2)).sum) ∧ state (Fin.last r) last = total
  (reader ↔ enough) ∧ (enough → ∃ sep : Fin (r+1) → Finset I,
    (∀ q, 2^(sep q).card ≤ w q ∧
      (∃ M : Finset (I × I), valid q M ∧ M.card = (sep q).card) ∧
      ∀ e : Fin m, decide ((time (u e)).val < q.val) ≠ decide ((time (v e)).val < q.val) →
        u e ∈ sep q ∨ v e ∈ sep q) ∧
    (∀ (t : Fin r) (i : I),
      (i ∈ sep t.castSucc → i ∉ sep t.succ → (time i).val ≤ t.val) ∧
      (i ∉ sep t.castSucc → i ∈ sep t.succ → t.val ≤ (time i).val))) := by
  intro n m r u v time w I P valid enough reader
  constructor
  · constructor
    · rintro ⟨start, last, terms, _, hrun⟩
      exact PEqualNP.Outside.L_pcx_430_aux.reader_to_enough u v time w start last terms hrun
    · intro henough
      exact PEqualNP.Outside.L_pcx_430_aux.enough_to_reader u v time w henough
  · intro henough
    refine ⟨PEqualNP.Outside.L_pcx_430_aux.sep u v time, ?_, ?_⟩
    · intro q
      rcases PEqualNP.Outside.L_pcx_430_aux.sep_konig u v time q with ⟨M, hM, hcard⟩
      refine ⟨by rw [← hcard]; exact henough q M hM, ⟨M, hM, hcard⟩, ?_⟩
      exact (PEqualNP.Outside.L_pcx_430_aux.isCover_iff_edge u v time q _).mp
        (PEqualNP.Outside.L_pcx_430_aux.sep_isCover u v time q)
    · exact PEqualNP.Outside.L_pcx_430_aux.sep_mono u v time
