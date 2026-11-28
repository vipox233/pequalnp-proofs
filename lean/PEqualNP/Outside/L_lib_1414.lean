import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1414

section
variable [DecidableEq ℕ]

def W {m : ℕ} (A : Fin m → Finset ℕ) (s e : ℕ) (i : Fin m) : Finset ℕ :=
  A i ∪ Finset.Ico s (s + (2*e+1) * i.val)

def Sub {m : ℕ} (W : Fin m → Finset ℕ) (e k : ℕ) (f : Fin k → Fin m) : Prop :=
  ∃ Y : Fin k → Finset ℕ, (∀ i j, i ≤ j → Y i ⊆ Y j) ∧
    ∀ i, ((W (f i)) \ Y i).card ≤ e ∧ (Y i \ W (f i)).card ≤ e

def Anch {m : ℕ} (A : Fin (m+2) → Finset ℕ) (s e : ℕ) : Prop :=
  2*e ≤ s ∧ (∀ i, A i ⊆ Finset.range s) ∧ A 0 = Finset.range (2*e) ∧ A (Fin.last (m+1)) = ∅

theorem keyA {m : ℕ} (A : Fin m → Finset ℕ) (s e k : ℕ) (f : Fin k → Fin m) (hf : Monotone f)
    (T : Finset ℕ) (h : ∀ j, (A (f j) \ T).card ≤ e ∧ (T \ A (f j)).card ≤ e) :
    Sub (W A s e) e k f := by
  refine ⟨fun j => T ∪ Finset.Ico s (s + (2*e+1) * (f j).val), ?_, ?_⟩
  · intro i j hij
    apply Finset.union_subset_union_right
    apply Finset.Ico_subset_Ico_right
    have : (f i).val ≤ (f j).val := hf hij
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ this) _
  · intro j
    refine ⟨le_trans (Finset.card_le_card ?_) (h j).1, le_trans (Finset.card_le_card ?_) (h j).2⟩
    · intro x; simp only [W, Finset.mem_sdiff, Finset.mem_union]; tauto
    · intro x; simp only [W, Finset.mem_sdiff, Finset.mem_union]; tauto

theorem keyB {m : ℕ} (A : Fin (m+2) → Finset ℕ) (s e : ℕ) (hA : Anch A s e) (k : ℕ)
    (f : Fin k → Fin (m+2)) (hf : StrictMono f) (j0 j1 : Fin k) (h0 : f j0 = 0)
    (h1 : f j1 = Fin.last (m+1)) (hs : Sub (W A s e) e k f) :
    ∃ T ∈ Finset.powersetCard e (Finset.range (2*e)),
      ∀ j, (A (f j) \ T).card ≤ e ∧ (T \ A (f j)).card ≤ e := by
  obtain ⟨hes, hAs, hA0, hAl⟩ := hA
  obtain ⟨Y, hinc, hnear⟩ := hs
  have hj1 : ∀ j, j ≤ j1 := fun j => hf.le_iff_le.mp (by rw [h1]; exact Fin.le_last _)
  have hj0 : ∀ j, j0 ≤ j := fun j => hf.le_iff_le.mp (by rw [h0]; exact Fin.zero_le _)
  obtain ⟨T, hT⟩ : ∃ T, T = Y j0 ∩ Finset.range (2*e) := ⟨_, rfl⟩
  have hTcard : e ≤ T.card := by
    have h := (hnear j0).1
    have hW : W A s e (f j0) = Finset.range (2*e) := by
      simp [W, h0, hA0]
    rw [hW] at h
    have := Finset.card_sdiff_add_card_inter (Finset.range (2*e)) (Y j0)
    rw [Finset.card_range, Finset.inter_comm, ← hT] at this
    omega
  have hle : ∀ j, (Y j ∩ Finset.range s).card ≤ e := by
    intro j
    refine le_trans (Finset.card_le_card ?_) (hnear j1).2
    intro x hx
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_sdiff]
    refine ⟨hinc j j1 (hj1 j) hx.1, ?_⟩
    rw [h1]
    intro hmem
    simp only [W, hAl, Finset.empty_union, Finset.mem_Ico] at hmem
    have := Finset.mem_range.mp hx.2
    omega
  have hsub : ∀ j, T ⊆ Y j ∩ Finset.range s := by
    intro j x hx
    rw [hT, Finset.mem_inter] at hx
    rw [Finset.mem_inter]
    refine ⟨hinc j0 j (hj0 j) hx.1, ?_⟩
    have := Finset.mem_range.mp hx.2
    exact Finset.mem_range.mpr (by omega)
  have heq : ∀ j, Y j ∩ Finset.range s = T := fun j =>
    (Finset.eq_of_subset_of_card_le (hsub j) (le_trans (hle j) hTcard)).symm
  have hTc : T.card = e := le_antisymm (by rw [← heq j0]; exact hle j0) hTcard
  refine ⟨T, Finset.mem_powersetCard.mpr ⟨by rw [hT]; exact Finset.inter_subset_right, hTc⟩,
    fun j => ⟨?_, ?_⟩⟩
  · refine le_trans (Finset.card_le_card ?_) (hnear j).1
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    refine ⟨by simp [W, hx.1], fun hxY => hx.2 ?_⟩
    rw [← heq j, Finset.mem_inter]
    exact ⟨hxY, hAs _ hx.1⟩
  · refine le_trans (Finset.card_le_card ?_) (hnear j).2
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    have hx1 := hx.1
    rw [hT, Finset.mem_inter, Finset.mem_range] at hx1
    refine ⟨(Finset.mem_inter.mp (hsub j hx.1)).1, ?_⟩
    intro hmem
    simp only [W, Finset.mem_union, Finset.mem_Ico] at hmem
    rcases hmem with h | h
    · exact hx.2 h
    · omega

theorem conj1 (e s m : ℕ) (A : Fin (m+2) → Finset ℕ) (hA : Anch A s e) :
    Sub (W A s e) e (m+2) id ↔ ∀ k ≤ Nat.choose (2*e) e + 2, ∀ f : Fin k → Fin (m+2),
      StrictMono f → Sub (W A s e) e k f := by
  constructor
  · rintro ⟨Y, hinc, hnear⟩ k _ f hf
    exact ⟨fun i => Y (f i), fun i j hij => hinc _ _ (hf.monotone hij), fun i => hnear (f i)⟩
  · intro H
    by_contra hno
    have hbad : ∀ T : Finset ℕ, ∃ i : Fin (m+2),
        ¬((A i \ T).card ≤ e ∧ (T \ A i).card ≤ e) := by
      intro T
      by_contra hc
      have hc' : ∀ i : Fin (m+2), (A i \ T).card ≤ e ∧ (T \ A i).card ≤ e := by
        intro i
        by_contra h
        exact hc ⟨i, h⟩
      exact hno (keyA A s e (m+2) id monotone_id T (fun j => hc' j))
    choose g hg using hbad
    let P := Finset.powersetCard e (Finset.range (2*e))
    let S : Finset (Fin (m+2)) := insert 0 (insert (Fin.last (m+1)) (P.image g))
    have hcard : S.card ≤ Nat.choose (2*e) e + 2 := by
      have h1 := Finset.card_insert_le (0 : Fin (m+2)) (insert (Fin.last (m+1)) (P.image g))
      have h2 := Finset.card_insert_le (Fin.last (m+1)) (P.image g)
      have h3 : (P.image g).card ≤ P.card := Finset.card_image_le
      have h4 : P.card = Nat.choose (2*e) e := by simp [P]
      show (insert 0 (insert (Fin.last (m+1)) (P.image g))).card ≤ _
      omega
    have hf := (S.orderEmbOfFin rfl).strictMono
    have hr : Set.range (S.orderEmbOfFin rfl) = ↑S := Finset.range_orderEmbOfFin S rfl
    have hmem : ∀ i ∈ S, ∃ j, S.orderEmbOfFin rfl j = i := by
      intro i hi
      have : i ∈ Set.range (S.orderEmbOfFin rfl) := by rw [hr]; exact hi
      exact this
    obtain ⟨j0, h0⟩ := hmem 0 (by simp [S])
    obtain ⟨j1, h1⟩ := hmem (Fin.last (m+1)) (by simp [S])
    obtain ⟨T, hT, hnear⟩ := keyB A s e hA S.card _ hf j0 j1 h0 h1 (H S.card hcard _ hf)
    obtain ⟨j, hj⟩ := hmem (g T) (by
      simp only [S, Finset.mem_insert, Finset.mem_image]
      exact Or.inr (Or.inr ⟨T, hT, rfl⟩))
    exact hg T (hj ▸ hnear j)

theorem conj2 (e : ℕ) (he : 0 < e) :
    ∃ A : Fin (Nat.choose (2*e) e + 2) → Finset ℕ, Anch A (2*e+1) e ∧
      (∀ i j, i < j → 2*e < (W A (2*e+1) e j \ W A (2*e+1) e i).card) ∧
      ¬ Sub (W A (2*e+1) e) e (Nat.choose (2*e) e + 2) id ∧
      ∀ k < Nat.choose (2*e) e + 2, ∀ f : Fin k → Fin (Nat.choose (2*e) e + 2), StrictMono f →
        Sub (W A (2*e+1) e) e k f := by
  obtain ⟨K, hK⟩ : ∃ K, K = Nat.choose (2*e) e := ⟨_, rfl⟩
  rw [← hK]
  let P := Finset.powersetCard e (Finset.range (2*e))
  have hPc : P.card = K := by simp [P, hK]
  let t : ℕ → Finset ℕ := fun j =>
    if h : j < P.card then ((P.equivFin.symm ⟨j, h⟩ : P) : Finset ℕ) else ∅
  have ht1 : ∀ j < K, t j ∈ P := by
    intro j hj
    have h : j < P.card := by omega
    simp only [t, dif_pos h]
    exact (P.equivFin.symm ⟨j, h⟩).2
  have ht2 : ∀ T ∈ P, ∃ j < K, t j = T := by
    intro T hT
    refine ⟨(P.equivFin ⟨T, hT⟩).val, by have := (P.equivFin ⟨T, hT⟩).isLt; omega, ?_⟩
    simp [t]
  have ht3 : ∀ j j', j < K → j' < K → t j = t j' → j = j' := by
    intro j j' hj hj' h
    have h1 : j < P.card := by omega
    have h2 : j' < P.card := by omega
    simp only [t, dif_pos h1, dif_pos h2] at h
    have := P.equivFin.symm.injective (Subtype.ext h)
    simpa using this
  have F1 : ∀ T ∈ P, (((Finset.range (2*e) \ T) ∪ {2*e}) \ T).card = e + 1 := by
    intro T hT
    obtain ⟨hTs, hTc⟩ := Finset.mem_powersetCard.mp hT
    have h2 : 2*e ∉ T := fun h => by have := Finset.mem_range.mp (hTs h); omega
    have : ((Finset.range (2*e) \ T) ∪ {2*e}) \ T = insert (2*e) (Finset.range (2*e) \ T) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert,
        Finset.mem_range]
      constructor
      · rintro ⟨h | h, _⟩ <;> tauto
      · rintro (h | h)
        · subst h; exact ⟨Or.inr rfl, h2⟩
        · exact ⟨Or.inl h, h.2⟩
    rw [this, Finset.card_insert_of_notMem (by simp)]
    have := Finset.card_sdiff_add_card_eq_card hTs
    rw [Finset.card_range] at this
    omega
  have F2 : ∀ T ∈ P, ∀ T' ∈ P, T' ≠ T →
      (((Finset.range (2*e) \ T) ∪ {2*e}) \ T').card ≤ e ∧
      (T' \ ((Finset.range (2*e) \ T) ∪ {2*e})).card ≤ e := by
    intro T hT T' hT' hne
    obtain ⟨hTs, hTc⟩ := Finset.mem_powersetCard.mp hT
    obtain ⟨hTs', hTc'⟩ := Finset.mem_powersetCard.mp hT'
    constructor
    · have hU : e + 1 ≤ (T ∪ T').card := by
        by_contra hc
        have h1 : T = T ∪ T' :=
          Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
        have h2 : T' = T ∪ T' :=
          Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
        exact hne (h2.trans h1.symm)
      have hUs : T ∪ T' ⊆ Finset.range (2*e) := Finset.union_subset hTs hTs'
      have h3 := Finset.card_sdiff_add_card_eq_card hUs
      rw [Finset.card_range] at h3
      have h4 : ((Finset.range (2*e) \ T) ∪ {2*e}) \ T' ⊆
          insert (2*e) (Finset.range (2*e) \ (T ∪ T')) := by
        intro x
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert,
          Finset.mem_range]
        tauto
      have h5 := Finset.card_le_card h4
      have h6 := Finset.card_insert_le (2*e) (Finset.range (2*e) \ (T ∪ T'))
      omega
    · exact le_trans (Finset.card_le_card Finset.sdiff_subset) hTc'.le
  let A : Fin (K+2) → Finset ℕ := fun i =>
    if i.val = 0 then Finset.range (2*e) else if i.val = K+1 then ∅
    else (Finset.range (2*e) \ t (i.val - 1)) ∪ {2*e}
  have hA0 : ∀ i : Fin (K+2), i.val = 0 → A i = Finset.range (2*e) := fun i h => by
    simp only [A, if_pos h]
  have hAl : ∀ i : Fin (K+2), i.val = K+1 → A i = ∅ := fun i h => by
    have h' : i.val ≠ 0 := by omega
    simp only [A, if_neg h', if_pos h]
  have hAm : ∀ i : Fin (K+2), i.val ≠ 0 → i.val ≠ K+1 →
      A i = (Finset.range (2*e) \ t (i.val - 1)) ∪ {2*e} := fun i h h' => by
    simp only [A, if_neg h, if_neg h']
  have hsubA : ∀ i, A i ⊆ Finset.range (2*e+1) := by
    intro i
    by_cases h0 : i.val = 0
    · rw [hA0 i h0]; exact Finset.range_subset_range.mpr (by omega)
    · by_cases hl : i.val = K+1
      · rw [hAl i hl]; exact Finset.empty_subset _
      · rw [hAm i h0 hl]
        intro x
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, Finset.mem_range]
        omega
  have hAnch : Anch A (2*e+1) e :=
    ⟨by omega, hsubA, hA0 0 (by simp), hAl (Fin.last (K+1)) (by simp)⟩
  refine ⟨A, hAnch, ?_, ?_, ?_⟩
  · intro i j hij
    have hsubset : Finset.Ico (2*e+1 + (2*e+1)*i.val) (2*e+1 + (2*e+1)*j.val) ⊆
        W A (2*e+1) e j \ W A (2*e+1) e i := by
      intro x hx
      rw [Finset.mem_Ico] at hx
      simp only [W, Finset.mem_sdiff, Finset.mem_union, Finset.mem_Ico]
      refine ⟨Or.inr ⟨by omega, hx.2⟩, ?_⟩
      rintro (h | h)
      · have := Finset.mem_range.mp (hsubA i h); omega
      · omega
    have := Finset.card_le_card hsubset
    rw [Nat.card_Ico] at this
    have h1 : (2*e+1)*(i.val+1) ≤ (2*e+1)*j.val := Nat.mul_le_mul_left _ hij
    have h2 : (2*e+1)*(i.val+1) = (2*e+1)*i.val + (2*e+1) := by ring
    omega
  · intro hs
    obtain ⟨T, hT, hnear⟩ := keyB A (2*e+1) e hAnch (K+2) id strictMono_id 0 (Fin.last (K+1))
      rfl rfl hs
    obtain ⟨j, hj, rfl⟩ := ht2 T hT
    have hA' : A ⟨j+1, by omega⟩ = (Finset.range (2*e) \ t j) ∪ {2*e} := by
      have := hAm ⟨j+1, by omega⟩ (by simp) (by simp; omega)
      simpa using this
    have h := (hnear ⟨j+1, by omega⟩).1
    change (A ⟨j+1, _⟩ \ t j).card ≤ e at h
    rw [hA', F1 _ hT] at h
    omega
  · intro k hk f hf
    have hns : ∃ i, ∀ j, f j ≠ i := by
      by_contra hc
      have hsurj : Function.Surjective f := by
        intro i
        by_contra h
        exact hc ⟨i, fun j hj => h ⟨j, hj⟩⟩
      have := Fintype.card_le_of_surjective f hsurj
      simp at this
      omega
    obtain ⟨i, hi⟩ := hns
    by_cases hi0 : i.val = 0
    · apply keyA A _ e k f hf.monotone {2*e}
      intro j
      have hj0 : (f j).val ≠ 0 := fun h => hi j (Fin.ext (by omega))
      by_cases hjl : (f j).val = K+1
      · rw [hAl _ hjl]
        constructor <;> simp <;> omega
      · rw [hAm _ hj0 hjl]
        have hjK : (f j).val - 1 < K := by have := (f j).isLt; omega
        obtain ⟨hTs, hTc⟩ := Finset.mem_powersetCard.mp (ht1 _ hjK)
        constructor
        · refine le_trans (Finset.card_le_card
            (?_ : _ ⊆ Finset.range (2*e) \ t ((f j).val - 1))) ?_
          · intro x
            simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
            tauto
          · have := Finset.card_sdiff_add_card_eq_card hTs
            rw [Finset.card_range] at this
            omega
        · have : ({2*e} : Finset ℕ) \ (Finset.range (2*e) \ t ((f j).val - 1) ∪ {2*e}) = ∅ :=
            Finset.sdiff_eq_empty_iff_subset.mpr Finset.subset_union_right
          rw [this]; simp
    · by_cases hil : i.val = K+1
      · apply keyA A _ e k f hf.monotone (Finset.range (2*e+1))
        intro j
        have hjl : (f j).val ≠ K+1 := fun h => hi j (Fin.ext (by omega))
        have h1 : A (f j) \ Finset.range (2*e+1) = ∅ :=
          Finset.sdiff_eq_empty_iff_subset.mpr (hsubA _)
        rw [h1]
        refine ⟨by simp, ?_⟩
        by_cases hj0 : (f j).val = 0
        · rw [hA0 _ hj0]
          have : Finset.range (2*e+1) \ Finset.range (2*e) ⊆ {2*e} := by
            intro x
            simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]
            omega
          have := Finset.card_le_card this
          rw [Finset.card_singleton] at this
          omega
        · rw [hAm _ hj0 hjl]
          have hjK : (f j).val - 1 < K := by have := (f j).isLt; omega
          obtain ⟨hTs, hTc⟩ := Finset.mem_powersetCard.mp (ht1 _ hjK)
          refine le_trans (Finset.card_le_card (?_ : _ ⊆ t ((f j).val - 1))) hTc.le
          intro x
          simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, Finset.mem_range]
          rintro ⟨h1, h2⟩
          by_contra h3
          have h4 : x ≠ 2*e := fun h => h2 (Or.inr h)
          exact h2 (Or.inl ⟨by omega, h3⟩)
      · have hiK : i.val - 1 < K := by have := i.isLt; omega
        have hTi := ht1 _ hiK
        obtain ⟨hTs, hTc⟩ := Finset.mem_powersetCard.mp hTi
        apply keyA A _ e k f hf.monotone (t (i.val - 1))
        intro j
        by_cases hj0 : (f j).val = 0
        · rw [hA0 _ hj0]
          have := Finset.card_sdiff_add_card_eq_card hTs
          rw [Finset.card_range] at this
          refine ⟨by omega, ?_⟩
          rw [Finset.sdiff_eq_empty_iff_subset.mpr hTs]; simp
        · by_cases hjl : (f j).val = K+1
          · rw [hAl _ hjl]
            exact ⟨by simp, by simp [hTc]⟩
          · rw [hAm _ hj0 hjl]
            have hjK : (f j).val - 1 < K := by have := (f j).isLt; omega
            have hne : t (i.val - 1) ≠ t ((f j).val - 1) := by
              intro h
              have := ht3 _ _ hiK hjK h
              exact hi j (Fin.ext (by omega))
            exact F2 _ (ht1 _ hjK) _ hTi hne

end

end PEqualNP.Outside.L_lib_1414

theorem PEqualNP.Outside.L_lib_1414 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let tag := fun (s w j : Nat) => Finset.Ico s (s+w*j)
let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
let inc := fun {m : Nat} (Y : Fin m → Finset Nat) => ∀ i j, i ≤ j → Y i ⊆ Y j
let subseq := fun {m : Nat} (W : Fin m → Finset Nat) (e k : Nat) (f : Fin k → Fin m) =>
  ∃ Y : Fin k → Finset Nat, inc Y ∧ ∀ i, near e e (W (f i)) (Y i)
let framed := fun {m : Nat} (A : Fin m → Finset Nat) (s e : Nat) (i : Fin m) =>
  A i ∪ tag s (2*e+1) i.val
let anchored := fun {m : Nat} (A : Fin (m+2) → Finset Nat) (s e : Nat) =>
  2*e ≤ s ∧ (∀ i, A i ⊆ Finset.range s) ∧ A 0 = Finset.range (2*e) ∧ A (Fin.last (m+1)) = ∅
(∀ (e s m : Nat) (A : Fin (m+2) → Finset Nat), anchored A s e →
  let W := framed A s e
  (subseq W e (m+2) id ↔ ∀ k ≤ Nat.choose (2*e) e+2, ∀ f : Fin k → Fin (m+2),
    StrictMono f → subseq W e k f)) ∧
∀ e : Nat, 0 < e → let K := Nat.choose (2*e) e
  ∃ A : Fin (K+2) → Finset Nat, anchored A (2*e+1) e ∧
    let W := framed A (2*e+1) e
    (∀ i j, i < j → 2*e < (W j \ W i).card) ∧ ¬subseq W e (K+2) id ∧
      ∀ k < K+2, ∀ f : Fin k → Fin (K+2), StrictMono f → subseq W e k f) := by
  intro tag near inc subseq framed anchored
  refine ⟨fun e s m A hA => ?_, fun e he => ?_⟩
  · have h := @PEqualNP.Outside.L_lib_1414.conj1 (fun a b => Classical.propDecidable (a = b)) e s m A hA
    exact h
  · have h := @PEqualNP.Outside.L_lib_1414.conj2 (fun a b => Classical.propDecidable (a = b)) e he
    exact h
