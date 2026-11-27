import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_277_aux

open PEqualNP.ProofComplexity
open Classical

abbrev Raw (m n : ℕ) := Fin m × Fin n
abbrev Cl (m n h : ℕ) := Clause (Sum (Raw m n) (Fin h))
abbrev Hid (h : ℕ) := Clause (Fin h)

def Consistent {h : ℕ} (U : Finset (Hid h)) : Prop :=
  ∃ z : Fin h → Bool, Satisfies z (↑U : Set _)

def RawSat {m n h : ℕ} (x : Raw m n → Bool) (C : Cl m n h) : Prop :=
  ∃ (p : Raw m n) (b : Bool), (Sum.inl p, b) ∈ C ∧ x p = b

noncomputable def hidPart {m n h : ℕ} (C : Cl m n h) : Hid h :=
  Finset.univ.filter (fun l : Fin h × Bool => (Sum.inr l.1, l.2) ∈ C)

noncomputable def posBlocks {m n h : ℕ} (C : Cl m n h) : Finset (Fin m) :=
  Finset.univ.filter (fun j : Fin m => ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C)

lemma mem_hidPart {m n h : ℕ} {C : Cl m n h} {l : Fin h × Bool} :
    l ∈ hidPart C ↔ (Sum.inr l.1, l.2) ∈ C := by
  simp [hidPart]

lemma mem_posBlocks {m n h : ℕ} {C : Cl m n h} {j : Fin m} :
    j ∈ posBlocks C ↔ ∃ i : Fin n, (Sum.inl (j, i), true) ∈ C := by
  simp [posBlocks]

lemma sum_union_le_nat {α : Type*} [DecidableEq α]
    (s t : Finset α) (w : α → ℕ) :
    ∑ x ∈ s ∪ t, w x ≤ (∑ x ∈ s, w x) + ∑ x ∈ t, w x := by
  have h1 : s ∪ t = s ∪ (t \ s) := by
    ext x
    simp
  rw [h1, Finset.sum_union Finset.disjoint_sdiff]
  have h2 : ∑ x ∈ t \ s, w x ≤ ∑ x ∈ t, w x :=
    Finset.sum_le_sum_of_subset Finset.sdiff_subset
  omega

lemma sum_image_le_nat {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) (w : β → ℕ) :
    ∑ y ∈ s.image f, w y ≤ ∑ x ∈ s, w (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.image_insert, Finset.sum_insert ha]
    by_cases hmem : f a ∈ s.image f
    · rw [Finset.insert_eq_of_mem hmem]
      omega
    · rw [Finset.sum_insert hmem]
      omega

lemma sum_biUnion_le_nat {α β : Type*} [DecidableEq β]
    (s : Finset α) (t : α → Finset β) (w : β → ℕ) :
    ∑ y ∈ s.biUnion t, w y ≤ ∑ x ∈ s, ∑ y ∈ t x, w y := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (sum_union_le_nat (t a) (s.biUnion t) w) (Nat.add_le_add_left ih _)

lemma exists_cover_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (U : Finset α) (g : α → ℕ) :
    ∀ S : Finset β, ∑ a ∈ U, g a = S.card →
      ∃ B : α → Finset β,
        (∀ a ∈ U, B a ⊆ S) ∧
        (∀ a ∈ U, (B a).card = g a) ∧
        (∀ j ∈ S, ∃ a ∈ U, j ∈ B a) := by
  induction U using Finset.induction_on with
  | empty =>
    intro S hS
    simp only [Finset.sum_empty] at hS
    have hSe : S = ∅ := Finset.card_eq_zero.mp hS.symm
    refine ⟨fun _ => ∅, ?_, ?_, ?_⟩
    · intro a ha; simp at ha
    · intro a ha; simp at ha
    · intro j hj; rw [hSe] at hj; simp at hj
  | insert a s ha ih =>
    intro S hS
    rw [Finset.sum_insert ha] at hS
    have hle : g a ≤ S.card := by omega
    obtain ⟨A, hAS, hAcard⟩ := Finset.exists_subset_card_eq hle
    have hcard_un : (S \ A).card + A.card = S.card := by
      have hdisj : Disjoint (S \ A) A := Finset.sdiff_disjoint
      have hun : (S \ A) ∪ A = S := Finset.sdiff_union_of_subset hAS
      have hc := Finset.card_union_of_disjoint hdisj
      rw [hun] at hc
      exact hc.symm
    have hrem : ∑ x ∈ s, g x = (S \ A).card := by omega
    obtain ⟨B', hB'sub, hB'card, hB'cov⟩ := ih (S \ A) hrem
    refine ⟨fun x => if x = a then A else B' x, ?_, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAS]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact Finset.Subset.trans (hB'sub x hxs) Finset.sdiff_subset
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · simp [hAcard]
      · have hne : x ≠ a := fun h => ha (h ▸ hxs)
        simp only [hne, ↓reduceIte]
        exact hB'card x hxs
    · intro j hj
      by_cases hjA : j ∈ A
      · exact ⟨a, Finset.mem_insert_self a s, by simp [hjA]⟩
      · have hjs : j ∈ S \ A := Finset.mem_sdiff.mpr ⟨hj, hjA⟩
        obtain ⟨x, hxs, hjx⟩ := hB'cov j hjs
        have hne : x ≠ a := fun h => ha (h ▸ hxs)
        exact ⟨x, Finset.mem_insert_of_mem hxs, by simp [hne, hjx]⟩

noncomputable def mkClause {m n h : ℕ} (H : Hid h) (B : Finset (Fin m)) (f : ↥B → Fin n) : Cl m n h :=
  H.image (fun l => (Sum.inr l.1, l.2)) ∪
  (Finset.univ : Finset ↥B).image (fun j => (Sum.inl (j.1, f j), true))

lemma mkClause_card {m n h : ℕ} (H : Hid h) (B : Finset (Fin m)) (f : ↥B → Fin n) :
    (mkClause H B f).card = H.card + B.card := by
  have hdisj : Disjoint (H.image (fun l : Fin h × Bool => (Sum.inr l.1, l.2)))
      ((Finset.univ : Finset ↥B).image (fun j => (Sum.inl (j.1, f j), true))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rcases Finset.mem_image.mp hx1 with ⟨l, _, rfl⟩
    rcases Finset.mem_image.mp hx2 with ⟨j, _, hEq⟩
    cases hEq
  rw [mkClause, Finset.card_union_of_disjoint hdisj]
  have hinj1 : Function.Injective (fun l : Fin h × Bool => ((Sum.inr l.1 : Sum (Raw m n) (Fin h)), l.2)) := by
    intro l1 l2 hEq
    rcases l1 with ⟨v1, b1⟩
    rcases l2 with ⟨v2, b2⟩
    injection hEq with hv hb
    injection hv with hv'
    subst hv'
    subst hb
    rfl
  have hinj2 : Function.Injective (fun j : ↥B => ((Sum.inl (j.1, f j) : Sum (Raw m n) (Fin h)), true)) := by
    intro j1 j2 hEq
    injection hEq with hv _
    injection hv with hp
    have hj : j1.1 = j2.1 := congrArg Prod.fst hp
    exact Subtype.ext hj
  rw [Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2]
  simp

lemma backward_dir {n m h W K : ℕ} (price : ℕ → ℕ)
    (U : Finset (Hid h)) (g : Hid h → ℕ)
    (hunsat : ¬ Consistent U)
    (hmin : ∀ H ∈ U, Consistent (U.erase H))
    (hsum : ∑ H ∈ U, g H = m)
    (hW : ∀ H ∈ U, H.card + g H ≤ W)
    (hK : ∑ H ∈ U, n ^ (g H) * price (H.card + g H) ≤ K) :
    ∃ F : Finset (Cl m n h),
      (∀ x : Raw m n → Bool,
        (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
          ∃ z : Fin h → Bool, Satisfies (Sum.elim x z) (↑F : Set _)) ∧
      (∀ C ∈ F, C.card ≤ W) ∧
      (∑ C ∈ F, price C.card) ≤ K := by
  have hcardU : (Finset.univ : Finset (Fin m)).card = m := Fintype.card_fin m
  obtain ⟨B, _, hBcard, hBcov⟩ :=
    exists_cover_card U g (Finset.univ : Finset (Fin m)) (by rw [hsum, hcardU])
  let F : Finset (Cl m n h) :=
    U.biUnion (fun H => (Finset.univ : Finset (↥(B H) → Fin n)).image (mkClause H (B H)))
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x
    constructor
    · rintro ⟨j0, hj0⟩
      obtain ⟨H0, hH0U, hj0B⟩ := hBcov j0 (Finset.mem_univ j0)
      obtain ⟨z, hz⟩ := hmin H0 hH0U
      refine ⟨z, ?_⟩
      intro C hC
      have hCF : C ∈ F := Finset.mem_coe.mp hC
      rcases Finset.mem_biUnion.mp hCF with ⟨H, hHU, hCH⟩
      rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
      by_cases hEq : H = H0
      · subst hEq
        refine ⟨(Sum.inl (j0, f ⟨j0, hj0B⟩), true), ?_, ?_⟩
        · rw [mkClause]
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨⟨j0, hj0B⟩, Finset.mem_univ _, rfl⟩
        · simpa [Sum.elim] using hj0 (f ⟨j0, hj0B⟩)
      · have hHer : H ∈ (↑(U.erase H0) : Set _) :=
          Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hEq, hHU⟩)
        obtain ⟨l, hlH, hlz⟩ := hz H hHer
        refine ⟨(Sum.inr l.1, l.2), ?_, ?_⟩
        · rw [mkClause]
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr ⟨l, hlH, rfl⟩
        · simpa [Sum.elim] using hlz
    · rintro ⟨z, hz⟩
      by_contra hno
      push Not at hno
      have hbad : ∃ H0 ∈ U, ¬ ClauseSat z H0 := by
        by_contra hall
        push Not at hall
        apply hunsat
        exact ⟨z, fun H hH => hall H (Finset.mem_coe.mp hH)⟩
      obtain ⟨H0, hH0U, hH0nsat⟩ := hbad
      have hpick : ∀ j : ↥(B H0), ∃ i : Fin n, x (j.1, i) = false := by
        intro j
        obtain ⟨i, hi⟩ := hno j.1
        cases hx : x (j.1, i)
        · exact ⟨i, hx⟩
        · exact False.elim (hi hx)
      let f : ↥(B H0) → Fin n := fun j => Classical.choose (hpick j)
      have hf : ∀ j : ↥(B H0), x (j.1, f j) = false :=
        fun j => Classical.choose_spec (hpick j)
      have hmem : mkClause H0 (B H0) f ∈ (↑F : Set _) := by
        rw [Finset.mem_coe]
        exact Finset.mem_biUnion.mpr ⟨H0, hH0U, Finset.mem_image.mpr ⟨f, Finset.mem_univ _, rfl⟩⟩
      obtain ⟨l, hlC, hlsat⟩ := hz (mkClause H0 (B H0) f) hmem
      rw [mkClause] at hlC
      rcases Finset.mem_union.mp hlC with hl1 | hl2
      · rcases Finset.mem_image.mp hl1 with ⟨lh, hlh, rfl⟩
        apply hH0nsat
        exact ⟨lh, hlh, by simpa [Sum.elim] using hlsat⟩
      · rcases Finset.mem_image.mp hl2 with ⟨j, _, rfl⟩
        have hxtrue : x (j.1, f j) = true := by simpa [Sum.elim] using hlsat
        rw [hf j] at hxtrue
        cases hxtrue
  · intro C hC
    rcases Finset.mem_biUnion.mp hC with ⟨H, hHU, hCH⟩
    rcases Finset.mem_image.mp hCH with ⟨f, _, rfl⟩
    rw [mkClause_card, hBcard H hHU]
    exact hW H hHU
  · calc
      ∑ C ∈ F, price C.card
        ≤ ∑ H ∈ U, ∑ C ∈ (Finset.univ : Finset (↥(B H) → Fin n)).image (mkClause H (B H)),
            price C.card := sum_biUnion_le_nat U _ (fun C : Cl m n h => price C.card)
      _ ≤ ∑ H ∈ U, ∑ f : ↥(B H) → Fin n, price (mkClause H (B H) f).card := by
          apply Finset.sum_le_sum
          intro H _
          exact sum_image_le_nat Finset.univ (mkClause H (B H)) (fun C : Cl m n h => price C.card)
      _ = ∑ H ∈ U, n ^ (g H) * price (H.card + g H) := by
          apply Finset.sum_congr rfl
          intro H hHU
          have hconst : ∀ f : ↥(B H) → Fin n,
              price (mkClause H (B H) f).card = price (H.card + g H) := by
            intro f
            rw [mkClause_card, hBcard H hHU]
          simp_rw [hconst]
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
            Fintype.card_fin, Fintype.card_coe, hBcard H hHU]
      _ ≤ K := hK

lemma exists_minimal_unsat {h : ℕ} :
    ∀ k : ℕ, ∀ U0 : Finset (Hid h), U0.card ≤ k → ¬ Consistent U0 →
      ∃ U ⊆ U0, ¬ Consistent U ∧ ∀ H ∈ U, Consistent (U.erase H) := by
  intro k
  induction k with
  | zero =>
    intro U0 hcard hunsat
    have hU0 : U0 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exfalso
    apply hunsat
    refine ⟨fun _ => false, ?_⟩
    intro H hH
    rw [hU0] at hH
    simp at hH
  | succ k ih =>
    intro U0 hcard hunsat
    by_cases hmin : ∀ H ∈ U0, Consistent (U0.erase H)
    · exact ⟨U0, Finset.Subset.refl _, hunsat, hmin⟩
    · push Not at hmin
      obtain ⟨H, hHU0, her⟩ := hmin
      have hlt : (U0.erase H).card < U0.card := Finset.card_erase_lt_of_mem hHU0
      have hle : (U0.erase H).card ≤ k := by omega
      obtain ⟨U, hUsub, hUunsat, hUmin⟩ := ih (U0.erase H) hle her
      exact ⟨U, Finset.Subset.trans hUsub (Finset.erase_subset H U0), hUunsat, hUmin⟩

def xAssign {m n : ℕ} (α : Fin m → Fin n) : Raw m n → Bool :=
  fun p => decide (p.2 ≠ α p.1)

def xFlip {m n : ℕ} (α : Fin m → Fin n) (j0 : Fin m) : Raw m n → Bool :=
  fun p => if p.1 = j0 then true else xAssign α p

lemma xAssign_eq_false {m n : ℕ} (α : Fin m → Fin n) (j : Fin m) (i : Fin n) :
    xAssign α (j, i) = false ↔ i = α j := by
  simp [xAssign]

lemma xAssign_eq_true {m n : ℕ} (α : Fin m → Fin n) (j : Fin m) (i : Fin n) :
    xAssign α (j, i) = true ↔ i ≠ α j := by
  simp [xAssign]

lemma rawSat_xFlip_of_not_xAssign {m n h : ℕ} (α : Fin m → Fin n) (j0 : Fin m)
    {C : Cl m n h} (hnot : ¬ RawSat (xAssign α) C) (hsat : RawSat (xFlip α j0) C) :
    (Sum.inl (j0, α j0), true) ∈ C := by
  obtain ⟨⟨j, i⟩, b, hmem, heq⟩ := hsat
  by_cases hj : j = j0
  · subst hj
    have hb : b = true := by
      simp [xFlip] at heq
      exact heq
    subst hb
    have hi : i = α j := by
      by_contra hne
      apply hnot
      refine ⟨(j, i), true, hmem, ?_⟩
      exact (xAssign_eq_true α j i).mpr hne
    subst hi
    exact hmem
  · exfalso
    apply hnot
    refine ⟨(j, i), b, hmem, ?_⟩
    simpa [xFlip, hj] using heq

lemma card_filter_not_rawSat_le {m n h : ℕ} (C : Cl m n h) :
    (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card ≤
      n ^ (m - (posBlocks C).card) := by
  let P := posBlocks C
  let S := Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)
  let T : Finset (↥(Pᶜ) → Fin n) := Finset.univ
  have hinj : Set.InjOn (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1) (↑S : Set _) := by
    intro α1 h1 α2 h2 hfun
    have h1' : ¬ RawSat (xAssign α1) C := (Finset.mem_filter.mp h1).2
    have h2' : ¬ RawSat (xAssign α2) C := (Finset.mem_filter.mp h2).2
    funext j
    by_cases hj : j ∈ P
    · obtain ⟨i, hi⟩ := mem_posBlocks.mp hj
      have h1i : α1 j = i := by
        by_contra hne
        apply h1'
        exact ⟨(j, i), true, hi, (xAssign_eq_true α1 j i).mpr (Ne.symm hne)⟩
      have h2i : α2 j = i := by
        by_contra hne
        apply h2'
        exact ⟨(j, i), true, hi, (xAssign_eq_true α2 j i).mpr (Ne.symm hne)⟩
      rw [h1i, h2i]
    · have hjc : j ∈ Pᶜ := Finset.mem_compl.mpr hj
      exact congrFun hfun ⟨j, hjc⟩
  have hmaps : Set.MapsTo (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1)
      (↑S : Set _) (↑T : Set _) := by
    intro α _
    exact Finset.mem_coe.mpr (Finset.mem_univ _)
  have hle := Finset.card_le_card_of_injOn
    (fun (α : Fin m → Fin n) (j : ↥(Pᶜ)) => α j.1) hmaps hinj
  have hTcard : T.card = n ^ (Pᶜ).card := by
    change (Finset.univ : Finset (↥(Pᶜ) → Fin n)).card = n ^ (Pᶜ).card
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  have hPcompl : (Pᶜ).card = m - P.card := by
    have hsum : (Pᶜ).card + P.card = m := by
      have hd : Disjoint (Pᶜ) P := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_compl.mp hx1) hx2
      have hu : Pᶜ ∪ P = Finset.univ := by
        ext x
        by_cases hx : x ∈ P
        · simp [hx]
        · simp [hx]
      have hc := Finset.card_union_of_disjoint hd
      rw [hu, Finset.card_univ, Fintype.card_fin] at hc
      exact hc.symm
    omega
  rw [hTcard, hPcompl] at hle
  exact hle

lemma card_hid_add_pos_le {m n h : ℕ}
    (α : Fin m → Fin n) (C : Cl m n h) (B : Finset (Fin m))
    (hB : ∀ j ∈ B, (Sum.inl (j, α j), true) ∈ C) :
    (hidPart C).card + B.card ≤ C.card := by
  let A1 : Cl m n h := (hidPart C).image (fun l => (Sum.inr l.1, l.2))
  let A2 : Cl m n h := B.image (fun j => (Sum.inl (j, α j), true))
  have hsub : A1 ∪ A2 ⊆ C := by
    intro x hx
    rcases Finset.mem_union.mp hx with h1 | h2
    · rcases Finset.mem_image.mp h1 with ⟨l, hl, rfl⟩
      exact mem_hidPart.mp hl
    · rcases Finset.mem_image.mp h2 with ⟨j, hj, rfl⟩
      exact hB j hj
  have hdisj : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]
    intro x h1 h2
    rcases Finset.mem_image.mp h1 with ⟨l, _, rfl⟩
    rcases Finset.mem_image.mp h2 with ⟨j, _, hEq⟩
    cases hEq
  have hinj1 : Function.Injective (fun l : Fin h × Bool => ((Sum.inr l.1 : Sum (Raw m n) (Fin h)), l.2)) := by
    intro l1 l2 hEq
    rcases l1 with ⟨v1, b1⟩
    rcases l2 with ⟨v2, b2⟩
    injection hEq with hv hb
    injection hv with hv'
    subst hv'
    subst hb
    rfl
  have hinj2 : Function.Injective (fun j : Fin m => ((Sum.inl (j, α j) : Sum (Raw m n) (Fin h)), true)) := by
    intro j1 j2 hEq
    injection hEq with hv _
    injection hv with hp
    exact congrArg Prod.fst hp
  have hc1 : A1.card = (hidPart C).card := Finset.card_image_of_injective _ hinj1
  have hc2 : A2.card = B.card := Finset.card_image_of_injective _ hinj2
  have hcu : (A1 ∪ A2).card = A1.card + A2.card := Finset.card_union_of_disjoint hdisj
  have hle : (A1 ∪ A2).card ≤ C.card := Finset.card_le_card hsub
  omega

lemma exists_alpha_data {n m h W : ℕ} (hn : 0 < n) (price : ℕ → ℕ)
    (hmono : ∀ lo hi, lo ≤ hi → price lo ≤ price hi)
    (F : Finset (Cl m n h))
    (henc : ∀ x : Raw m n → Bool,
      (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
        ∃ z : Fin h → Bool, Satisfies (Sum.elim x z) (↑F : Set _))
    (hW : ∀ C ∈ F, C.card ≤ W)
    (α : Fin m → Fin n) :
    ∃ (U : Finset (Hid h)) (g : Hid h → ℕ),
      ¬ Consistent U ∧
      (∀ H ∈ U, Consistent (U.erase H)) ∧
      (∑ H ∈ U, g H) = m ∧
      (∀ H ∈ U, H.card + g H ≤ W) ∧
      (∑ H ∈ U, n ^ (g H) * price (H.card + g H)) ≤
        ∑ C ∈ F.filter (fun C => ¬ RawSat (xAssign α) C),
          n ^ (posBlocks C).card * price C.card := by
  let Fα : Finset (Cl m n h) := F.filter (fun C => ¬ RawSat (xAssign α) C)
  let Uα : Finset (Hid h) := Fα.image hidPart
  have hUα_unsat : ¬ Consistent Uα := by
    rintro ⟨z, hz⟩
    have hsatF : Satisfies (Sum.elim (xAssign α) z) (↑F : Set _) := by
      intro C hC
      have hCF : C ∈ F := Finset.mem_coe.mp hC
      by_cases hraw : RawSat (xAssign α) C
      · obtain ⟨p, b, hmem, heq⟩ := hraw
        exact ⟨(Sum.inl p, b), hmem, by simpa [Sum.elim] using heq⟩
      · have hCFα : C ∈ Fα := Finset.mem_filter.mpr ⟨hCF, hraw⟩
        have hHU : hidPart C ∈ (↑Uα : Set _) :=
          Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨C, hCFα, rfl⟩)
        obtain ⟨l, hl, hzl⟩ := hz (hidPart C) hHU
        exact ⟨(Sum.inr l.1, l.2), mem_hidPart.mp hl, by simpa [Sum.elim] using hzl⟩
    have hyes : ∃ j : Fin m, ∀ i : Fin n, xAssign α (j, i) = true :=
      (henc (xAssign α)).mpr ⟨z, hsatF⟩
    obtain ⟨j, hj⟩ := hyes
    have htrue := hj (α j)
    have hfalse : xAssign α (j, α j) = false := (xAssign_eq_false α j (α j)).mpr rfl
    rw [hfalse] at htrue
    cases htrue
  obtain ⟨U, hUsub, hUunsat, hUmin⟩ :=
    exists_minimal_unsat Uα.card Uα (le_refl _) hUα_unsat
  have hphi_ex : ∀ j : Fin m, ∃ H ∈ U, ∀ C ∈ Fα, hidPart C = H → (Sum.inl (j, α j), true) ∈ C := by
    intro j
    have hyes : ∃ j' : Fin m, ∀ i : Fin n, xFlip α j (j', i) = true :=
      ⟨j, fun i => by simp [xFlip]⟩
    obtain ⟨z, hz⟩ := (henc (xFlip α j)).mp hyes
    have hbad : ∃ H ∈ U, ¬ ClauseSat z H := by
      by_contra hall
      push Not at hall
      exact hUunsat ⟨z, fun H hH => hall H (Finset.mem_coe.mp hH)⟩
    obtain ⟨H, hHU, hHnsat⟩ := hbad
    refine ⟨H, hHU, ?_⟩
    intro C hCFα hhid
    have hCF : C ∈ (↑F : Set _) := Finset.mem_coe.mpr (Finset.mem_filter.mp hCFα).1
    have hnot : ¬ RawSat (xAssign α) C := (Finset.mem_filter.mp hCFα).2
    obtain ⟨l, hlC, hlsat⟩ := hz C hCF
    rcases l with ⟨v, b⟩
    rcases v with p | hv
    · have hrawflip : RawSat (xFlip α j) C := ⟨p, b, hlC, by simpa [Sum.elim] using hlsat⟩
      exact rawSat_xFlip_of_not_xAssign α j hnot hrawflip
    · exfalso
      apply hHnsat
      have hlH : (hv, b) ∈ H := by
        rw [← hhid]
        exact mem_hidPart.mpr hlC
      exact ⟨(hv, b), hlH, by simpa [Sum.elim] using hlsat⟩
  let φ : Fin m → Hid h := fun j => Classical.choose (hphi_ex j)
  have hφU : ∀ j : Fin m, φ j ∈ U := fun j => (Classical.choose_spec (hphi_ex j)).1
  have hφC : ∀ (j : Fin m) (C : Cl m n h), C ∈ Fα → hidPart C = φ j →
      (Sum.inl (j, α j), true) ∈ C :=
    fun j => (Classical.choose_spec (hphi_ex j)).2
  let g : Hid h → ℕ := fun H => (Finset.univ.filter (fun j : Fin m => φ j = H)).card
  have hgsum : ∑ H ∈ U, g H = m := by
    have h1 : ∑ H ∈ U, (Finset.univ.filter (fun j : Fin m => φ j = H)).card =
        (Finset.univ : Finset (Fin m)).card := by
      have hcard_eq : ∀ H : Hid h,
          (Finset.univ.filter (fun j : Fin m => φ j = H)).card =
          ∑ j : Fin m, if φ j = H then 1 else 0 := by
        intro H
        simp [Finset.sum_boole]
      simp_rw [hcard_eq]
      rw [Finset.sum_comm]
      have hinner : ∀ j : Fin m, (∑ H ∈ U, if φ j = H then 1 else 0) = 1 := by
        intro j
        rw [Finset.sum_ite_eq U (φ j) (fun _ => 1)]
        simp [hφU j]
      simp_rw [hinner]
      simp
    rw [h1, Finset.card_univ, Fintype.card_fin]
  have hpick_ex : ∀ H ∈ U, ∃ C ∈ Fα, hidPart C = H := by
    intro H hHU
    exact Finset.mem_image.mp (hUsub hHU)
  let pickC : Hid h → Cl m n h := fun H =>
    if hHU : H ∈ U then Classical.choose (hpick_ex H hHU) else ∅
  have hpick_mem : ∀ H ∈ U, pickC H ∈ Fα := by
    intro H hHU
    simp only [pickC, hHU, ↓reduceDIte]
    exact (Classical.choose_spec (hpick_ex H hHU)).1
  have hpick_hid : ∀ H ∈ U, hidPart (pickC H) = H := by
    intro H hHU
    simp only [pickC, hHU, ↓reduceDIte]
    exact (Classical.choose_spec (hpick_ex H hHU)).2
  have hcard_le : ∀ H ∈ U, H.card + g H ≤ (pickC H).card := by
    intro H hHU
    have hB : ∀ j ∈ Finset.univ.filter (fun j : Fin m => φ j = H),
        (Sum.inl (j, α j), true) ∈ pickC H := by
      intro j hj
      have hjEq : φ j = H := (Finset.mem_filter.mp hj).2
      exact hφC j (pickC H) (hpick_mem H hHU) (by rw [hpick_hid H hHU, hjEq])
    have hle := card_hid_add_pos_le α (pickC H)
      (Finset.univ.filter (fun j : Fin m => φ j = H)) hB
    rw [hpick_hid H hHU] at hle
    exact hle
  have hg_le_pos : ∀ H ∈ U, g H ≤ (posBlocks (pickC H)).card := by
    intro H hHU
    apply Finset.card_le_card
    intro j hj
    have hjEq : φ j = H := (Finset.mem_filter.mp hj).2
    apply mem_posBlocks.mpr
    refine ⟨α j, ?_⟩
    exact hφC j (pickC H) (hpick_mem H hHU) (by rw [hpick_hid H hHU, hjEq])
  refine ⟨U, g, hUunsat, hUmin, hgsum, ?_, ?_⟩
  · intro H hHU
    exact le_trans (hcard_le H hHU) (hW (pickC H) (Finset.mem_filter.mp (hpick_mem H hHU)).1)
  · have hterm : ∀ H ∈ U,
        n ^ (g H) * price (H.card + g H) ≤
          n ^ (posBlocks (pickC H)).card * price (pickC H).card := by
      intro H hHU
      apply Nat.mul_le_mul
      · exact Nat.pow_le_pow_right hn (hg_le_pos H hHU)
      · exact hmono _ _ (hcard_le H hHU)
    have h1 : ∑ H ∈ U, n ^ (g H) * price (H.card + g H) ≤
        ∑ H ∈ U, n ^ (posBlocks (pickC H)).card * price (pickC H).card :=
      Finset.sum_le_sum hterm
    have hinj : Set.InjOn pickC (↑U : Set _) := by
      intro H1 h1 H2 h2 hEq
      have h1' : H1 ∈ U := Finset.mem_coe.mp h1
      have h2' : H2 ∈ U := Finset.mem_coe.mp h2
      rw [← hpick_hid H1 h1', ← hpick_hid H2 h2', hEq]
    have h2 : ∑ H ∈ U, n ^ (posBlocks (pickC H)).card * price (pickC H).card =
        ∑ C ∈ U.image pickC, n ^ (posBlocks C).card * price C.card := by
      symm
      exact Finset.sum_image hinj
    have hsub : U.image pickC ⊆ Fα := by
      intro C hC
      rcases Finset.mem_image.mp hC with ⟨H, hHU, rfl⟩
      exact hpick_mem H hHU
    have h3 : ∑ C ∈ U.image pickC, n ^ (posBlocks C).card * price C.card ≤
        ∑ C ∈ Fα, n ^ (posBlocks C).card * price C.card :=
      Finset.sum_le_sum_of_subset hsub
    exact le_trans h1 (by rw [h2]; exact h3)

lemma forward_dir {n m h W K : ℕ} (hn : 0 < n) (price : ℕ → ℕ)
    (hmono : ∀ lo hi, lo ≤ hi → price lo ≤ price hi)
    (F : Finset (Cl m n h))
    (henc : ∀ x : Raw m n → Bool,
      (∃ j : Fin m, ∀ i : Fin n, x (j, i) = true) ↔
        ∃ z : Fin h → Bool, Satisfies (Sum.elim x z) (↑F : Set _))
    (hW : ∀ C ∈ F, C.card ≤ W)
    (hK : ∑ C ∈ F, price C.card ≤ K) :
    ∃ (U : Finset (Hid h)) (g : Hid h → ℕ),
      ¬ Consistent U ∧
      (∀ H ∈ U, Consistent (U.erase H)) ∧
      (∑ H ∈ U, g H) = m ∧
      (∀ H ∈ U, H.card + g H ≤ W) ∧
      (∑ H ∈ U, n ^ (g H) * price (H.card + g H)) ≤ K := by
  let w : Cl m n h → ℕ := fun C => n ^ (posBlocks C).card * price C.card
  let score : (Fin m → Fin n) → ℕ := fun α =>
    ∑ C ∈ F.filter (fun C => ¬ RawSat (xAssign α) C), w C
  have hsum_le : ∑ α : Fin m → Fin n, score α ≤ n ^ m * K := by
    have hrewrite : ∑ α : Fin m → Fin n, score α =
        ∑ C ∈ F, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C := by
      have h1 : ∀ α : Fin m → Fin n,
          score α = ∑ C ∈ F, if ¬ RawSat (xAssign α) C then w C else 0 := by
        intro α
        simp [score, Finset.sum_filter]
      simp_rw [h1]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro C _
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    rw [hrewrite]
    have hterm : ∀ C ∈ F,
        (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C ≤
          n ^ m * price C.card := by
      intro C _
      have hcard := card_filter_not_rawSat_le C
      have hp_le : (posBlocks C).card ≤ m := by
        calc
          (posBlocks C).card ≤ (Finset.univ : Finset (Fin m)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = m := by simp
      calc
        (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C
          ≤ n ^ (m - (posBlocks C).card) * (n ^ (posBlocks C).card * price C.card) :=
            Nat.mul_le_mul_right (w C) hcard
        _ = (n ^ (m - (posBlocks C).card) * n ^ (posBlocks C).card) * price C.card := by
            rw [Nat.mul_assoc]
        _ = n ^ m * price C.card := by
            rw [← Nat.pow_add, Nat.sub_add_cancel hp_le]
    calc
      ∑ C ∈ F, (Finset.univ.filter (fun α : Fin m → Fin n => ¬ RawSat (xAssign α) C)).card * w C
        ≤ ∑ C ∈ F, n ^ m * price C.card := Finset.sum_le_sum hterm
      _ = n ^ m * ∑ C ∈ F, price C.card := by rw [← Finset.mul_sum]
      _ ≤ n ^ m * K := Nat.mul_le_mul_left (n ^ m) hK
  have hex : ∃ α : Fin m → Fin n, score α ≤ K := by
    by_contra hall
    push Not at hall
    have hgt : n ^ m * (K + 1) ≤ ∑ α : Fin m → Fin n, score α := by
      have h1 : ∑ _α : Fin m → Fin n, (K + 1) ≤ ∑ α : Fin m → Fin n, score α :=
        Finset.sum_le_sum (fun α _ => hall α)
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin] at h1
      exact h1
    have hpos : 0 < n ^ m := Nat.pow_pos hn
    have hstrict : n ^ m * K < n ^ m * (K + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    omega
  obtain ⟨α, hα⟩ := hex
  obtain ⟨U, g, hunsat, hmin, hsum, hWU, hcost⟩ :=
    exists_alpha_data hn price hmono F henc hW α
  exact ⟨U, g, hunsat, hmin, hsum, hWU, le_trans hcost hα⟩

end PEqualNP.Outside.L_pcx_277_aux

theorem PEqualNP.Outside.L_pcx_277 :
∀ (n m hiddenCount W K : ℕ), 0 < n → 0 < m → ∀ price : ℕ → ℕ, (∀ lo hi, lo ≤ hi → price lo ≤ price hi) →
  let Raw := Fin m × Fin n
  let Cl := PEqualNP.ProofComplexity.Clause (Sum Raw (Fin hiddenCount))
  let Hidden := PEqualNP.ProofComplexity.Clause (Fin hiddenCount)
  let enc := fun F : Finset Cl => ∀ x : Raw → Bool,
    (∃ j : Fin m, ∀ i : Fin n, x (j,i) = true) ↔
      ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim x z) (↑F : Set _)
  let consistent := fun U : Finset Hidden =>
    ∃ z : Fin hiddenCount → Bool, PEqualNP.ProofComplexity.Satisfies z (↑U : Set _)
  (∃ F : Finset Cl, enc F ∧ (∀ C ∈ F, C.card ≤ W) ∧
    (∑ C ∈ F, price C.card) ≤ K) ↔
  ∃ (U : Finset Hidden) (g : Hidden → ℕ),
    ¬ consistent U ∧ (∀ H ∈ U, consistent (U.erase H)) ∧
    (∑ H ∈ U, g H) = m ∧ (∀ H ∈ U, H.card + g H ≤ W) ∧
    (∑ H ∈ U, n^(g H) * price (H.card + g H)) ≤ K := by
  intro n m hiddenCount W K hn _hm price hmono
  dsimp only
  constructor
  · rintro ⟨F, henc, hW, hK⟩
    exact PEqualNP.Outside.L_pcx_277_aux.forward_dir hn price hmono F henc hW hK
  · rintro ⟨U, g, hunsat, hmin, hsum, hW, hK⟩
    exact PEqualNP.Outside.L_pcx_277_aux.backward_dir price U g hunsat hmin hsum hW hK
