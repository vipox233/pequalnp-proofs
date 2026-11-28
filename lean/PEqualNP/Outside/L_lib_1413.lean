import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_1413 : (letI : ∀ P : Prop, Decidable P := Classical.propDecidable
let tag := fun (s w j : Nat) => Finset.Ico s (s+w*j)
let near := fun (a f : Nat) (W Y : Finset Nat) => (W \ Y).card ≤ a ∧ (Y \ W).card ≤ f
let inc := fun {m : Nat} (Y : Fin m → Finset Nat) => ∀ i j, i ≤ j → Y i ⊆ Y j
∀ (n k m : Nat) (E : Fin m → Finset Nat) (d : Fin m → Nat), k ≤ n →
  (∀ j, E j ⊆ Finset.range n ∧ d j ≤ k) →
  let a := n-k
  let s := 2*n+1
  let raw := fun (j : Fin (m+2)) =>
    if j.val=0 then Finset.range n else if h : j.val-1 < m then
      let i : Fin m := ⟨j.val-1,h⟩
      E i ∪ Finset.Ico n (n+(a+d i-(E i).card))
    else ∅
  let W := fun j : Fin (m+2) => raw j ∪ tag s (n+1) j.val
  let good := fun T : Finset Nat => T ⊆ Finset.range n ∧ T.card=k ∧ ∀ i, d i ≤ (T ∩ E i).card
  let fit := fun Y : Fin (m+2) → Finset Nat => inc Y ∧ ∀ j, near a k (W j) (Y j)
  (∀ i j, i < j → n < (W j \ W i).card) ∧
  (∀ Y, fit Y → ∃ T, good T ∧ ∀ j, Y j ∩ Finset.range s = T) ∧
  ∀ T, good T → fit (fun j => T ∪ tag s (n+1) j.val)) := by
  generalize (fun a b : ℕ => Classical.propDecidable (a = b)) = inst
  intro tag near inc n k m E d hkn hE a s raw W good fit
  have hraw0 : ∀ j : Fin (m+2), j.val = 0 → raw j = Finset.range n := by
    intro j hj
    simp only [raw]
    rw [if_pos hj]
  have hrawS : ∀ (j : Fin (m+2)) (h : j.val - 1 < m), j.val ≠ 0 →
      raw j = E ⟨j.val-1,h⟩ ∪ Finset.Ico n (n + (a + d ⟨j.val-1,h⟩ - (E ⟨j.val-1,h⟩).card)) := by
    intro j h hj
    simp only [raw]
    rw [if_neg hj, dif_pos h]
  have hrawL : ∀ j : Fin (m+2), j.val ≠ 0 → ¬ (j.val - 1 < m) → raw j = ∅ := by
    intro j hj h
    simp only [raw]
    rw [if_neg hj, dif_neg h]
  have hraw_lt : ∀ (j : Fin (m+2)) x, x ∈ raw j → x < s := by
    intro j x hx
    by_cases hj : j.val = 0
    · rw [hraw0 j hj] at hx
      simp only [Finset.mem_range] at hx
      omega
    · by_cases h : j.val - 1 < m
      · rw [hrawS j h hj] at hx
        have h1 := (hE ⟨j.val-1,h⟩).1
        have h2 := (hE ⟨j.val-1,h⟩).2
        simp only [Finset.mem_union, Finset.mem_Ico] at hx
        rcases hx with hx | hx
        · have := Finset.mem_range.1 (h1 hx)
          omega
        · omega
      · rw [hrawL j hj h] at hx
        simp at hx
  have htag : ∀ j x, x ∈ tag s (n+1) j ↔ s ≤ x ∧ x < s + (n+1)*j := by
    intro j x
    simp only [tag, Finset.mem_Ico]
  have hW : ∀ j x, x ∈ W j ↔ x ∈ raw j ∨ x ∈ tag s (n+1) j.val := by
    intro j x
    simp only [W, Finset.mem_union]
  have hmul : ∀ i j : ℕ, i ≤ j → (n+1)*i ≤ (n+1)*j := fun i j h => Nat.mul_le_mul_left _ h
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    have hij' : i.val + 1 ≤ j.val := hij
    have h1 := hmul _ _ hij'
    have h2 : (n+1)*(i.val+1) = (n+1)*i.val + (n+1) := by ring
    have hsub : Finset.Ico (s + (n+1)*i.val) (s + (n+1)*j.val) ⊆ W j \ W i := by
      intro x hx
      simp only [Finset.mem_Ico] at hx
      rw [Finset.mem_sdiff, hW, hW, htag, htag]
      refine ⟨Or.inr ⟨by omega, hx.2⟩, ?_⟩
      rintro (h | h)
      · have := hraw_lt i x h
        omega
      · omega
    have hc := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hc
    omega
  · rintro Y ⟨hinc, hnear⟩
    have hinc' : ∀ i j : Fin (m+2), i ≤ j → Y i ⊆ Y j := hinc
    have hnear' : ∀ j : Fin (m+2), (W j \ Y j).card ≤ a ∧ (Y j \ W j).card ≤ k := hnear
    let j0 : Fin (m+2) := ⟨0, by omega⟩
    let jl : Fin (m+2) := ⟨m+1, by omega⟩
    have hTn : Y j0 ∩ Finset.range n ⊆ Finset.range n := Finset.inter_subset_right
    have hTge : k ≤ (Y j0 ∩ Finset.range n).card := by
      have h0 := (hnear' j0).1
      have hsub : Finset.range n \ Y j0 ⊆ W j0 \ Y j0 := by
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        refine ⟨?_, hx.2⟩
        rw [hW, hraw0 j0 rfl]
        exact Or.inl hx.1
      have hc := Finset.card_le_card hsub
      have h3 := Finset.card_sdiff_add_card_inter (Finset.range n) (Y j0)
      rw [Finset.card_range, Finset.inter_comm] at h3
      omega
    have hrl : raw jl = ∅ := hrawL jl (by simp [jl]) (by simp [jl])
    have hTsub : Y j0 ∩ Finset.range n ⊆ Y jl \ W jl := by
      intro x hx
      rw [Finset.mem_inter, Finset.mem_range] at hx
      rw [Finset.mem_sdiff, hW, htag, hrl]
      refine ⟨hinc' j0 jl (Fin.zero_le _) hx.1, ?_⟩
      rintro (h | h)
      · simp at h
      · omega
    have hTeq : Y j0 ∩ Finset.range n = Y jl \ W jl :=
      Finset.eq_of_subset_of_card_le hTsub (le_trans (hnear' jl).2 hTge)
    have hTk : (Y j0 ∩ Finset.range n).card = k :=
      le_antisymm (le_trans (Finset.card_le_card hTsub) (hnear' jl).2) hTge
    have hY : ∀ j : Fin (m+2), Y j ∩ Finset.range s = Y j0 ∩ Finset.range n := by
      intro j
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter, Finset.mem_range] at hx
        rw [hTeq, Finset.mem_sdiff, hW, htag, hrl]
        refine ⟨hinc' j jl (Fin.le_last _) hx.1, ?_⟩
        rintro (h | h)
        · simp at h
        · omega
      · intro hx
        rw [Finset.mem_inter, Finset.mem_range] at hx ⊢
        exact ⟨hinc' j0 j (Fin.zero_le _) hx.1, by omega⟩
    refine ⟨Y j0 ∩ Finset.range n, ⟨hTn, hTk, ?_⟩, hY⟩
    intro i
    let j : Fin (m+2) := ⟨i.val+1, by omega⟩
    have hjm : j.val - 1 < m := by simp [j]
    have hrj := hrawS j hjm (by simp [j])
    have hi : (⟨j.val-1, hjm⟩ : Fin m) = i := by
      apply Fin.ext
      simp [j]
    rw [hi] at hrj
    have hsub : (E i \ (Y j0 ∩ Finset.range n)) ∪ Finset.Ico n (n + (a + d i - (E i).card)) ⊆ W j \ Y j := by
      intro x hx
      rw [Finset.mem_sdiff, hW, hrj]
      rw [Finset.mem_union, Finset.mem_sdiff] at hx
      have hxs : x < s := by
        apply hraw_lt j
        rw [hrj, Finset.mem_union]
        rcases hx with hx | hx
        · exact Or.inl hx.1
        · exact Or.inr hx
      have hnT : x ∉ Y j0 ∩ Finset.range n := by
        rcases hx with hx | hx
        · exact hx.2
        · intro h
          have := Finset.mem_range.1 (hTn h)
          rw [Finset.mem_Ico] at hx
          omega
      refine ⟨Or.inl ?_, ?_⟩
      · rw [Finset.mem_union]
        rcases hx with hx | hx
        · exact Or.inl hx.1
        · exact Or.inr hx
      · intro hxY
        apply hnT
        rw [← hY j, Finset.mem_inter, Finset.mem_range]
        exact ⟨hxY, hxs⟩
    have hdisj : Disjoint (E i \ (Y j0 ∩ Finset.range n)) (Finset.Ico n (n + (a + d i - (E i).card))) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      have := Finset.mem_range.1 ((hE i).1 (Finset.mem_sdiff.1 hx).1)
      rw [Finset.mem_Ico] at hx2
      omega
    have hc := le_trans (Finset.card_le_card hsub) (hnear' j).1
    rw [Finset.card_union_of_disjoint hdisj, Nat.card_Ico] at hc
    have h3 := Finset.card_sdiff_add_card_inter (E i) (Y j0 ∩ Finset.range n)
    rw [Finset.inter_comm (E i) _] at h3
    omega
  · rintro T ⟨hTn, hTk, hTd⟩
    have hTlt : ∀ x ∈ T, x < n := fun x hx => Finset.mem_range.1 (hTn hx)
    have hcomp : (Finset.range n \ T).card = a := by
      have h3 := Finset.card_sdiff_add_card_inter (Finset.range n) T
      rw [Finset.card_range, Finset.inter_eq_right.2 hTn] at h3
      omega
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hij' : i.val ≤ j.val := hij
      have h1 := hmul _ _ hij'
      intro x hx
      simp only [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl hx
      · rw [htag] at hx ⊢
        exact Or.inr ⟨hx.1, by omega⟩
    · intro j
      change (W j \ (T ∪ tag s (n+1) j.val)).card ≤ a ∧ ((T ∪ tag s (n+1) j.val) \ W j).card ≤ k
      have hs1 : W j \ (T ∪ tag s (n+1) j.val) ⊆ raw j \ T := by
        intro x hx
        rw [Finset.mem_sdiff, hW, Finset.mem_union] at hx
        rw [Finset.mem_sdiff]
        rcases hx with ⟨h1 | h1, h2⟩
        · exact ⟨h1, fun h => h2 (Or.inl h)⟩
        · exact absurd (Or.inr h1) h2
      have hs2 : (T ∪ tag s (n+1) j.val) \ W j ⊆ T := by
        intro x hx
        rw [Finset.mem_sdiff, hW, Finset.mem_union] at hx
        rcases hx with ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd (Or.inr h1) h2
      refine ⟨le_trans (Finset.card_le_card hs1) ?_, ?_⟩
      · by_cases hj : j.val = 0
        · rw [hraw0 j hj, hcomp]
        · by_cases h : j.val - 1 < m
          · rw [hrawS j h hj]
            have hEn := (hE ⟨j.val-1,h⟩).1
            have hd := hTd ⟨j.val-1,h⟩
            have hs3 : (E ⟨j.val-1,h⟩ ∪ Finset.Ico n (n + (a + d ⟨j.val-1,h⟩ - (E ⟨j.val-1,h⟩).card))) \ T ⊆
                (E ⟨j.val-1,h⟩ \ T) ∪ Finset.Ico n (n + (a + d ⟨j.val-1,h⟩ - (E ⟨j.val-1,h⟩).card)) := by
              intro x hx
              simp only [Finset.mem_sdiff, Finset.mem_union] at hx ⊢
              tauto
            have hc := le_trans (Finset.card_le_card hs3) (Finset.card_union_le _ _)
            rw [Nat.card_Ico] at hc
            have h3 := Finset.card_sdiff_add_card_inter (E ⟨j.val-1,h⟩) T
            rw [Finset.inter_comm] at h3
            have h4 : (E ⟨j.val-1,h⟩ \ T).card ≤ (Finset.range n \ T).card :=
              Finset.card_le_card (Finset.sdiff_subset_sdiff hEn (le_refl _))
            omega
          · rw [hrawL j hj h]
            simp
      · have := Finset.card_le_card hs2
        omega
