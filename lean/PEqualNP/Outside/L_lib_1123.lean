import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1123_aux

open Finset

theorem charsum {ι α : Type*} [DecidableEq ι] [DecidableEq α] (R : Finset ι)
    (blk : ι → Finset α) (s : ι → Bool) (X : Finset α) :
    (2:ℤ) ^ R.card * ((X.powerset.filter (fun T =>
        ∀ r ∈ R, decide ((T ∩ blk r).card % 2 = 1) = s r)).card : ℤ) =
      2 ^ X.card * ∑ D ∈ R.powerset.filter (fun D =>
        ∀ x ∈ X, (D.filter (fun r => x ∈ blk r)).card % 2 = 0),
          ∏ r ∈ D, (if s r then (-1:ℤ) else 1) := by
  have ind : ∀ (T : Finset α) (r : ι),
      (if decide ((T ∩ blk r).card % 2 = 1) = s r then (2:ℤ) else 0) =
        1 + (if s r then (-1:ℤ) else 1) * (-1) ^ (T ∩ blk r).card := by
    intro T r
    rcases Nat.even_or_odd (T ∩ blk r).card with h | h
    · have h2 : (T ∩ blk r).card % 2 = 0 := Nat.even_iff.1 h
      rw [h.neg_one_pow]; cases s r <;> simp [h2]
    · have h2 : (T ∩ blk r).card % 2 = 1 := Nat.odd_iff.1 h
      rw [h.neg_one_pow]; cases s r <;> simp [h2]
  have hpow : ∀ (T : Finset α) (r : ι),
      ((-1:ℤ)) ^ (T ∩ blk r).card = ∏ x ∈ T, (if x ∈ blk r then (-1:ℤ) else 1) := by
    intro T r
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
      Finset.filter_mem_eq_inter]
  have inner : ∀ D : Finset ι,
      ∑ T ∈ X.powerset, ∏ r ∈ D, ((-1:ℤ)) ^ (T ∩ blk r).card =
        if ∀ x ∈ X, (D.filter (fun r => x ∈ blk r)).card % 2 = 0 then 2 ^ X.card else 0 := by
    intro D
    have h1 : ∀ T ∈ X.powerset, ∏ r ∈ D, ((-1:ℤ)) ^ (T ∩ blk r).card =
        ∏ x ∈ T, ((-1:ℤ)) ^ (D.filter (fun r => x ∈ blk r)).card := by
      intro T _
      simp_rw [hpow]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [Finset.sum_congr rfl h1, ← Finset.prod_one_add]
    have h2 : ∀ x ∈ X, (1 + ((-1:ℤ)) ^ (D.filter (fun r => x ∈ blk r)).card) =
        if (D.filter (fun r => x ∈ blk r)).card % 2 = 0 then 2 else 0 := by
      intro x _
      rcases Nat.even_or_odd (D.filter (fun r => x ∈ blk r)).card with h | h
      · rw [h.neg_one_pow, if_pos (Nat.even_iff.1 h)]; norm_num
      · rw [h.neg_one_pow, if_neg (by rw [Nat.odd_iff.1 h]; norm_num)]; norm_num
    rw [Finset.prod_congr rfl h2, Finset.prod_ite_zero, Finset.prod_const]
  calc (2:ℤ) ^ R.card * ((X.powerset.filter (fun T =>
        ∀ r ∈ R, decide ((T ∩ blk r).card % 2 = 1) = s r)).card : ℤ)
      = ∑ T ∈ X.powerset, ∏ r ∈ R,
          (if decide ((T ∩ blk r).card % 2 = 1) = s r then (2:ℤ) else 0) := by
        simp_rw [Finset.prod_ite_zero, Finset.prod_const]
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => ?_
        split_ifs <;> simp
    _ = ∑ T ∈ X.powerset, ∑ D ∈ R.powerset,
          ∏ r ∈ D, ((if s r then (-1:ℤ) else 1) * (-1) ^ (T ∩ blk r).card) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp_rw [ind]
        rw [Finset.prod_one_add]
    _ = ∑ D ∈ R.powerset, (∏ r ∈ D, (if s r then (-1:ℤ) else 1)) *
          ∑ T ∈ X.powerset, ∏ r ∈ D, ((-1:ℤ)) ^ (T ∩ blk r).card := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun D _ => ?_
        simp_rw [Finset.prod_mul_distrib]
        rw [Finset.mul_sum]
    _ = _ := by
        simp_rw [inner]
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun D _ => ?_
        split_ifs <;> ring

theorem trace {n : ℕ} (H : Finset (Finset (Fin n))) (h0 : (∅ : Finset (Fin n)) ∉ H)
    (h1 : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B)
    (s : Finset (Fin n) → Bool) (X T : Finset (Fin n)) (hT : T ⊆ X) :
    (∃ y ∈ (Finset.univ : Finset (Finset (Fin n))), y ∩ X = T ∧
        ∀ B ∈ H, decide ((y ∩ B).card % 2 = 1) = s B) ↔
      ∀ B ∈ H, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = s B := by
  classical
  constructor
  · rintro ⟨y, -, rfl, hy⟩ B hB hBX
    rw [← hy B hB, Finset.inter_assoc, Finset.inter_eq_right.2 hBX]
  · intro h
    have uniq : ∀ B ∈ H, ∀ B' ∈ H, ∀ i, i ∈ B → i ∈ B' → B = B' :=
      fun B hB B' hB' i hi hi' => (h1 i).unique ⟨hB, hi⟩ ⟨hB', hi'⟩
    set E : Finset (Fin n) → Finset (Fin n) := fun B =>
      if hne : (B \ X).Nonempty then {(B \ X).min' hne} else ∅ with hE
    have hEsub : ∀ B, E B ⊆ B \ X := by
      intro B; simp only [hE]; split_ifs with hne
      · exact Finset.singleton_subset_iff.2 (Finset.min'_mem _ hne)
      · exact Finset.empty_subset _
    have hEcard : ∀ B, ¬ B ⊆ X → (E B).card = 1 := by
      intro B hB
      have hne : (B \ X).Nonempty := by rwa [Finset.sdiff_nonempty]
      simp only [hE, dif_pos hne, Finset.card_singleton]
    let bad : Finset (Fin n) → Prop := fun B =>
      ¬ B ⊆ X ∧ decide ((T ∩ B).card % 2 = 1) ≠ s B
    let y : Finset (Fin n) := Finset.univ.filter (fun i => i ∈ T ∨ ∃ B ∈ H, bad B ∧ i ∈ E B)
    refine ⟨y, Finset.mem_univ _, ?_, ?_⟩
    · ext i
      simp only [y, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hi | ⟨B, -, -, hiE⟩, hiX⟩
        · exact hi
        · exact absurd hiX (Finset.mem_sdiff.1 (hEsub B hiE)).2
      · intro hi; exact ⟨Or.inl hi, hT hi⟩
    · intro B hB
      have hyB : y ∩ B = (T ∩ B) ∪ (if bad B then E B else ∅) := by
        ext i
        simp only [y, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_union]
        constructor
        · rintro ⟨hi | ⟨B', hB', hbad, hiE⟩, hiB⟩
          · exact Or.inl ⟨hi, hiB⟩
          · have hBB : B' = B := uniq B' hB' B hB i (Finset.mem_sdiff.1 (hEsub B' hiE)).1 hiB
            rw [hBB] at hbad hiE
            right; rw [if_pos hbad]; exact hiE
        · rintro (⟨hi, hiB⟩ | hi)
          · exact ⟨Or.inl hi, hiB⟩
          · by_cases hbad : bad B
            · rw [if_pos hbad] at hi
              exact ⟨Or.inr ⟨B, hB, hbad, hi⟩, (Finset.mem_sdiff.1 (hEsub B hi)).1⟩
            · rw [if_neg hbad] at hi; exact absurd hi (Finset.notMem_empty _)
      have hdisj : Disjoint (T ∩ B) (if bad B then E B else ∅) := by
        rw [Finset.disjoint_left]; intro i hi hi2
        by_cases hbad : bad B
        · rw [if_pos hbad] at hi2
          exact (Finset.mem_sdiff.1 (hEsub B hi2)).2 (hT (Finset.mem_inter.1 hi).1)
        · rw [if_neg hbad] at hi2; exact absurd hi2 (Finset.notMem_empty _)
      rw [hyB, Finset.card_union_of_disjoint hdisj]
      by_cases hbad : bad B
      · rw [if_pos hbad, hEcard B hbad.1]
        have h2 := hbad.2
        rcases Nat.mod_two_eq_zero_or_one (T ∩ B).card with hk | hk
        · have hk' : ((T ∩ B).card + 1) % 2 = 1 := by omega
          rw [hk] at h2; rw [hk']; revert h2; cases s B <;> simp
        · have hk' : ((T ∩ B).card + 1) % 2 = 0 := by omega
          rw [hk] at h2; rw [hk']; revert h2; cases s B <;> simp
      · rw [if_neg hbad, Finset.card_empty, add_zero]
        by_cases hBX : B ⊆ X
        · exact h B hB hBX
        · by_contra hne; exact hbad ⟨hBX, hne⟩

def partsF {n : ℕ} (P Q : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun C => C.Nonempty ∧
    (∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C) ∧
    ∀ D ∈ C.powerset, D.Nonempty → (∀ B ∈ P ∪ Q, Disjoint D B ∨ B ⊆ D) → D = C)

theorem cl_inter {n : ℕ} {P Q : Finset (Finset (Fin n))} {C1 C2 : Finset (Fin n)}
    (h1 : ∀ B ∈ P ∪ Q, Disjoint C1 B ∨ B ⊆ C1) (h2 : ∀ B ∈ P ∪ Q, Disjoint C2 B ∨ B ⊆ C2) :
    ∀ B ∈ P ∪ Q, Disjoint (C1 ∩ C2) B ∨ B ⊆ C1 ∩ C2 := by
  intro B hB
  rcases h1 B hB with d | s1
  · left; exact Finset.disjoint_of_subset_left Finset.inter_subset_left d
  · rcases h2 B hB with d | s2
    · left; exact Finset.disjoint_of_subset_left Finset.inter_subset_right d
    · right; exact Finset.subset_inter s1 s2

theorem cl_sdiff {n : ℕ} {P Q : Finset (Finset (Fin n))} {C1 C2 : Finset (Fin n)}
    (h1 : ∀ B ∈ P ∪ Q, Disjoint C1 B ∨ B ⊆ C1) (h2 : ∀ B ∈ P ∪ Q, Disjoint C2 B ∨ B ⊆ C2) :
    ∀ B ∈ P ∪ Q, Disjoint (C1 \ C2) B ∨ B ⊆ C1 \ C2 := by
  intro B hB
  rcases h1 B hB with d | s1
  · left; exact Finset.disjoint_of_subset_left Finset.sdiff_subset d
  · rcases h2 B hB with d | s2
    · right; exact Finset.subset_sdiff.2 ⟨s1, d.symm⟩
    · left; exact Finset.disjoint_of_subset_right s2 Finset.sdiff_disjoint

theorem part_exists {n : ℕ} (P Q : Finset (Finset (Fin n))) (i : Fin n) :
    ∃ C ∈ partsF P Q, i ∈ C := by
  classical
  let Ci : Finset (Fin n) := Finset.univ.filter
    (fun j => ∀ C : Finset (Fin n), (∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C) → i ∈ C → j ∈ C)
  have hmem : ∀ j, j ∈ Ci ↔
      ∀ C : Finset (Fin n), (∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C) → i ∈ C → j ∈ C := by
    intro j; simp [Ci]
  have hi : i ∈ Ci := (hmem i).2 fun C _ h => h
  have hcl : ∀ B ∈ P ∪ Q, Disjoint Ci B ∨ B ⊆ Ci := by
    intro B hB
    by_cases hsub : B ⊆ Ci
    · exact Or.inr hsub
    · left
      obtain ⟨j, hjB, hj⟩ := Finset.not_subset.1 hsub
      rw [hmem] at hj; push_neg at hj
      obtain ⟨C, hC, hiC, hjC⟩ := hj
      have hd : Disjoint C B := (hC B hB).resolve_right fun hs => hjC (hs hjB)
      exact Finset.disjoint_of_subset_left (fun k hk => (hmem k).1 hk C hC hiC) hd
  refine ⟨Ci, ?_, hi⟩
  simp only [partsF, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨i, hi⟩, hcl, ?_⟩
  intro D hD hDne hDcl
  have hDsub := Finset.mem_powerset.1 hD
  by_cases hiD : i ∈ D
  · exact Finset.Subset.antisymm hDsub fun j hj => (hmem j).1 hj D hDcl hiD
  · exfalso
    obtain ⟨j, hj⟩ := hDne
    have := (hmem j).1 (hDsub hj) (Ci \ D) (cl_sdiff hcl hDcl) (Finset.mem_sdiff.2 ⟨hi, hiD⟩)
    exact (Finset.mem_sdiff.1 this).2 hj

theorem cl_part_sub {n : ℕ} {P Q : Finset (Finset (Fin n))} {U C : Finset (Fin n)}
    (hU : ∀ B ∈ P ∪ Q, Disjoint U B ∨ B ⊆ U) (hC : C ∈ partsF P Q) {x : Fin n}
    (hxC : x ∈ C) (hxU : x ∈ U) : C ⊆ U := by
  simp only [partsF, Finset.mem_filter, Finset.mem_univ, true_and] at hC
  have := hC.2.2 (C ∩ U) (Finset.mem_powerset.2 Finset.inter_subset_left)
    ⟨x, Finset.mem_inter.2 ⟨hxC, hxU⟩⟩ (cl_inter hC.2.1 hU)
  exact Finset.inter_eq_left.1 this

theorem part_cl {n : ℕ} {P Q : Finset (Finset (Fin n))} {C : Finset (Fin n)}
    (hC : C ∈ partsF P Q) : ∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C := by
  simp only [partsF, Finset.mem_filter, Finset.mem_univ, true_and] at hC
  exact hC.2.1

theorem part_eq {n : ℕ} {P Q : Finset (Finset (Fin n))} {C C' : Finset (Fin n)}
    (hC : C ∈ partsF P Q) (hC' : C' ∈ partsF P Q) {x : Fin n}
    (hxC : x ∈ C) (hxC' : x ∈ C') : C = C' :=
  Finset.Subset.antisymm (cl_part_sub (part_cl hC') hC hxC hxC')
    (cl_part_sub (part_cl hC) hC' hxC' hxC)

theorem blk_sub {n : ℕ} {P Q : Finset (Finset (Fin n))} {C B : Finset (Fin n)}
    (hC : C ∈ partsF P Q) (hB : B ∈ P ∪ Q) {x : Fin n} (hxB : x ∈ B) (hxC : x ∈ C) : B ⊆ C :=
  (part_cl hC B hB).resolve_left fun d => Finset.disjoint_left.1 d hxC hxB

theorem cnt {n : ℕ} (H : Finset (Finset (Fin n)))
    (h1 : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B)
    (S : Finset (Finset (Fin n))) (hS : S ⊆ H) (x : Fin n) :
    (S.filter (fun B => x ∈ B)).card = if ∃ B ∈ S, x ∈ B then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨B, hB, hx⟩ := h
    rw [Finset.card_eq_one]; refine ⟨B, ?_⟩
    ext B'; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hB', hx'⟩; exact (h1 x).unique ⟨hS hB', hx'⟩ ⟨hS hB, hx⟩
    · rintro rfl; exact ⟨hB, hx⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro B hB hx; exact h ⟨B, hB, hx⟩

theorem depcount {n : ℕ} (P Q : Finset (Finset (Fin n)))
    (hP : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ P ∧ i ∈ B)
    (hQ : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ Q ∧ i ∈ B)
    (DP DQ : Finset (Finset (Fin n))) (hDP : DP ⊆ P) (hDQ : DQ ⊆ Q) (x : Fin n) :
    ((DP.disjSum DQ).filter (fun r => x ∈ Sum.elim id id r)).card =
      (if ∃ B ∈ DP, x ∈ B then 1 else 0) + (if ∃ B ∈ DQ, x ∈ B then 1 else 0) := by
  have h : (DP.disjSum DQ).filter (fun r => x ∈ Sum.elim id id r) =
      (DP.filter (fun B => x ∈ B)).disjSum (DQ.filter (fun B => x ∈ B)) := by
    ext r; cases r <;> simp
  rw [h, Finset.card_disjSum, cnt P hP DP hDP x, cnt Q hQ DQ hDQ x]

theorem cov {n : ℕ} {P Q : Finset (Finset (Fin n))} (H : Finset (Finset (Fin n)))
    (h1 : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B) (hH : H ⊆ P ∪ Q)
    (I : Finset (Finset (Fin n))) (hI : I ⊆ partsF P Q) (x : Fin n) :
    (∃ B ∈ H.filter (fun B => ∃ C ∈ I, B ⊆ C), x ∈ B) ↔ ∃ C ∈ I, x ∈ C := by
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨-, C, hC, hBC⟩ := Finset.mem_filter.1 hB
    exact ⟨C, hC, hBC hx⟩
  · rintro ⟨C, hC, hx⟩
    obtain ⟨B, ⟨hB, hxB⟩, -⟩ := h1 x
    exact ⟨B, Finset.mem_filter.2 ⟨hB, C, hC, blk_sub (hI hC) (hH hB) hxB hx⟩, hxB⟩

theorem sgn {n : ℕ} {P Q : Finset (Finset (Fin n))} (H : Finset (Finset (Fin n)))
    (h0 : (∅ : Finset (Fin n)) ∉ H)
    (I : Finset (Finset (Fin n))) (hI : I ⊆ partsF P Q) (s : Finset (Fin n) → Bool) :
    ∏ B ∈ H.filter (fun B => ∃ C ∈ I, B ⊆ C), (if s B then (-1:ℤ) else 1) =
      ∏ C ∈ I, (-1:ℤ) ^ ((H.filter (fun B => B ⊆ C)).filter (fun B => s B = true)).card := by
  have hb : H.filter (fun B => ∃ C ∈ I, B ⊆ C) =
      I.biUnion (fun C => H.filter (fun B => B ⊆ C)) := by
    ext B; simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hB, C, hC, hBC⟩; exact ⟨C, hC, hB, hBC⟩
    · rintro ⟨C, hC, hB, hBC⟩; exact ⟨hB, C, hC, hBC⟩
  rw [hb, Finset.prod_biUnion]
  · refine Finset.prod_congr rfl fun C _ => ?_
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  · intro C hC C' hC' hne
    change Disjoint (H.filter _) (H.filter _)
    rw [Finset.disjoint_left]; intro B hB hB'
    obtain ⟨hBH, hBC⟩ := Finset.mem_filter.1 hB
    obtain ⟨-, hBC'⟩ := Finset.mem_filter.1 hB'
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ hBH))
    exact hne (part_eq (hI (Finset.mem_coe.1 hC)) (hI (Finset.mem_coe.1 hC')) (hBC hx) (hBC' hx))

theorem inj_side {n : ℕ} {P Q : Finset (Finset (Fin n))} (H : Finset (Finset (Fin n)))
    (h1 : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B) (hH : H ⊆ P ∪ Q)
    (I I' : Finset (Finset (Fin n))) (hI : I ⊆ partsF P Q) (hI' : I' ⊆ partsF P Q)
    (hsub : ∀ B, B ∈ H.filter (fun B => ∃ C ∈ I, B ⊆ C) →
      B ∈ H.filter (fun B => ∃ C ∈ I', B ⊆ C)) : I ⊆ I' := by
  intro C hC
  have hCp := hI hC
  have hne : C.Nonempty := by
    have h := hCp
    simp only [partsF, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact h.1
  obtain ⟨x, hx⟩ := hne
  obtain ⟨B, hB, hxB⟩ := (cov H h1 hH I hI x).2 ⟨C, hC, hx⟩
  obtain ⟨-, C', hC', hBC'⟩ := Finset.mem_filter.1 (hsub B hB)
  rw [part_eq hCp (hI' hC') hx (hBC' hxB)]; exact hC'

theorem recover {n : ℕ} (P Q : Finset (Finset (Fin n))) (H : Finset (Finset (Fin n)))
    (h0 : (∅ : Finset (Fin n)) ∉ H)
    (h1 : ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B) (hH : H ⊆ P ∪ Q)
    (DH : Finset (Finset (Fin n))) (hDH : DH ⊆ H) (U : Finset (Fin n))
    (hU : ∀ B ∈ P ∪ Q, Disjoint U B ∨ B ⊆ U) (hUmem : ∀ x, x ∈ U ↔ ∃ B ∈ DH, x ∈ B) :
    H.filter (fun B => ∃ C ∈ (partsF P Q).filter (fun C => C ⊆ U), B ⊆ C) = DH := by
  ext B; simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hB, C, ⟨hC, hCU⟩, hBC⟩
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ hB))
    obtain ⟨B', hB', hxB'⟩ := (hUmem x).1 (hCU (hBC hx))
    rw [(h1 x).unique ⟨hB, hx⟩ ⟨hDH hB', hxB'⟩]; exact hB'
  · intro hB
    have hBH := hDH hB
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 (fun h => h0 (h ▸ hBH))
    obtain ⟨C, hC, hxC⟩ := part_exists P Q x
    have hxU : x ∈ U := (hUmem x).2 ⟨B, hB, hx⟩
    exact ⟨hBH, C, ⟨hC, cl_part_sub hU hC hxC hxU⟩, blk_sub hC (hH hBH) hx hxC⟩

theorem depsum {n : ℕ} (P Q : Finset (Finset (Fin n)))
    (hP : (∅ : Finset (Fin n)) ∉ P ∧ ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ P ∧ i ∈ B)
    (hQ : (∅ : Finset (Fin n)) ∉ Q ∧ ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ Q ∧ i ∈ B)
    (a b : Finset (Fin n) → Bool) (X : Finset (Fin n)) :
    ∑ D ∈ ((P.filter (fun B => B ⊆ X)).disjSum (Q.filter (fun B => B ⊆ X))).powerset.filter
        (fun D => ∀ x ∈ X, (D.filter (fun r => x ∈ Sum.elim id id r)).card % 2 = 0),
        ∏ r ∈ D, (if Sum.elim a b r then (-1:ℤ) else 1) =
      ∏ C ∈ (partsF P Q).filter (fun C => C ⊆ X),
        (1 + (-1:ℤ) ^ (((P.filter (fun B => B ⊆ C)).filter (fun B => a B = true)).card +
          ((Q.filter (fun B => B ⊆ C)).filter (fun B => b B = true)).card)) := by
  classical
  rw [Finset.prod_one_add]; symm
  have hPsub : P ⊆ P ∪ Q := Finset.subset_union_left
  have hQsub : Q ⊆ P ∪ Q := Finset.subset_union_right
  have hint : ∀ I ∈ ((partsF P Q).filter (fun C => C ⊆ X)).powerset, I ⊆ partsF P Q :=
    fun I hI C hC => (Finset.mem_filter.1 (Finset.mem_powerset.1 hI hC)).1
  refine Finset.sum_bij (fun I _ => (P.filter (fun B => ∃ C ∈ I, B ⊆ C)).disjSum
    (Q.filter (fun B => ∃ C ∈ I, B ⊆ C))) ?_ ?_ ?_ ?_
  · intro I hI
    have hIp := hint I hI
    have hIX : ∀ C ∈ I, C ⊆ X := fun C hC =>
      (Finset.mem_filter.1 (Finset.mem_powerset.1 hI hC)).2
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨?_, ?_⟩
    · apply Finset.disjSum_mono
      · intro B hB
        obtain ⟨hBP, C, hC, hBC⟩ := Finset.mem_filter.1 hB
        exact Finset.mem_filter.2 ⟨hBP, hBC.trans (hIX C hC)⟩
      · intro B hB
        obtain ⟨hBP, C, hC, hBC⟩ := Finset.mem_filter.1 hB
        exact Finset.mem_filter.2 ⟨hBP, hBC.trans (hIX C hC)⟩
    · intro x _
      have hc := depcount P Q hP.2 hQ.2 (P.filter (fun B => ∃ C ∈ I, B ⊆ C))
        (Q.filter (fun B => ∃ C ∈ I, B ⊆ C)) (Finset.filter_subset _ _)
        (Finset.filter_subset _ _) x
      have e1 := cov P hP.2 hPsub I hIp x
      have e2 := cov Q hQ.2 hQsub I hIp x
      by_cases h : ∃ C ∈ I, x ∈ C
      · rw [if_pos (e1.2 h), if_pos (e2.2 h)] at hc
        rw [hc]
      · rw [if_neg (fun h' => h (e1.1 h')), if_neg (fun h' => h (e2.1 h'))] at hc
        rw [hc]
  · intro I hI I' hI' heq
    have hP' : ∀ B, B ∈ P.filter (fun B => ∃ C ∈ I, B ⊆ C) ↔
        B ∈ P.filter (fun B => ∃ C ∈ I', B ⊆ C) := by
      intro B
      rw [← Finset.inl_mem_disjSum (t := Q.filter (fun B => ∃ C ∈ I, B ⊆ C)), heq,
        Finset.inl_mem_disjSum]
    exact Finset.Subset.antisymm
      (inj_side P hP.2 hPsub I I' (hint I hI) (hint I' hI') fun B => (hP' B).1)
      (inj_side P hP.2 hPsub I' I (hint I' hI') (hint I hI) fun B => (hP' B).2)
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_powerset] at hD
    obtain ⟨hDR, hdep⟩ := hD
    have hDL : D.toLeft ⊆ P.filter (fun B => B ⊆ X) := fun B hB =>
      Finset.inl_mem_disjSum.1 (hDR (Finset.mem_toLeft.1 hB))
    have hDRt : D.toRight ⊆ Q.filter (fun B => B ⊆ X) := fun B hB =>
      Finset.inr_mem_disjSum.1 (hDR (Finset.mem_toRight.1 hB))
    have hDeq : D.toLeft.disjSum D.toRight = D := Finset.toLeft_disjSum_toRight
    have hmem : ∀ x, (∃ B ∈ D.toLeft, x ∈ B) ↔ (∃ B ∈ D.toRight, x ∈ B) := by
      intro x
      by_cases hx : x ∈ X
      · have h := hdep x hx
        have hc := depcount P Q hP.2 hQ.2 D.toLeft D.toRight
          (hDL.trans (Finset.filter_subset _ _)) (hDRt.trans (Finset.filter_subset _ _)) x
        rw [hDeq] at hc
        rw [hc] at h
        by_cases h1 : ∃ B ∈ D.toLeft, x ∈ B <;> by_cases h2 : ∃ B ∈ D.toRight, x ∈ B
        · exact ⟨fun _ => h2, fun _ => h1⟩
        · rw [if_pos h1, if_neg h2] at h; exact absurd h (by norm_num)
        · rw [if_neg h1, if_pos h2] at h; exact absurd h (by norm_num)
        · exact ⟨fun h' => absurd h' h1, fun h' => absurd h' h2⟩
      · constructor
        · rintro ⟨B, hB, hxB⟩; exact absurd ((Finset.mem_filter.1 (hDL hB)).2 hxB) hx
        · rintro ⟨B, hB, hxB⟩; exact absurd ((Finset.mem_filter.1 (hDRt hB)).2 hxB) hx
    let U : Finset (Fin n) := Finset.univ.filter (fun x => ∃ B ∈ D.toLeft, x ∈ B)
    have hUP : ∀ x, x ∈ U ↔ ∃ B ∈ D.toLeft, x ∈ B := by intro x; simp [U]
    have hUQ : ∀ x, x ∈ U ↔ ∃ B ∈ D.toRight, x ∈ B := fun x => (hUP x).trans (hmem x)
    have hUcl : ∀ B ∈ P ∪ Q, Disjoint U B ∨ B ⊆ U := by
      intro B hB
      by_cases hd : Disjoint U B
      · exact Or.inl hd
      · right
        rw [Finset.not_disjoint_iff] at hd
        obtain ⟨x, hxU, hxB⟩ := hd
        rcases Finset.mem_union.1 hB with hBP | hBQ
        · obtain ⟨B', hB', hxB'⟩ := (hUP x).1 hxU
          have hBB : B = B' := (hP.2 x).unique ⟨hBP, hxB⟩
            ⟨(Finset.mem_filter.1 (hDL hB')).1, hxB'⟩
          intro y hy; exact (hUP y).2 ⟨B', hB', hBB ▸ hy⟩
        · obtain ⟨B', hB', hxB'⟩ := (hUQ x).1 hxU
          have hBB : B = B' := (hQ.2 x).unique ⟨hBQ, hxB⟩
            ⟨(Finset.mem_filter.1 (hDRt hB')).1, hxB'⟩
          intro y hy; exact (hUQ y).2 ⟨B', hB', hBB ▸ hy⟩
    have hUX : U ⊆ X := by
      intro x hx
      obtain ⟨B, hB, hxB⟩ := (hUP x).1 hx
      exact (Finset.mem_filter.1 (hDL hB)).2 hxB
    refine ⟨(partsF P Q).filter (fun C => C ⊆ U), ?_, ?_⟩
    · rw [Finset.mem_powerset]; intro C hC
      obtain ⟨hCp, hCU⟩ := Finset.mem_filter.1 hC
      exact Finset.mem_filter.2 ⟨hCp, hCU.trans hUX⟩
    · rw [recover P Q P hP.1 hP.2 hPsub D.toLeft (hDL.trans (Finset.filter_subset _ _)) U hUcl hUP,
        recover P Q Q hQ.1 hQ.2 hQsub D.toRight (hDRt.trans (Finset.filter_subset _ _)) U hUcl hUQ,
        hDeq]
  · intro I hI
    have hIp := hint I hI
    rw [Finset.prod_disjSum]
    change _ = (∏ B ∈ P.filter (fun B => ∃ C ∈ I, B ⊆ C), (if a B then (-1:ℤ) else 1)) *
      (∏ B ∈ Q.filter (fun B => ∃ C ∈ I, B ⊆ C), (if b B then (-1:ℤ) else 1))
    rw [sgn P hP.1 I hIp a, sgn Q hQ.1 I hIp b, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun C _ => ?_
    rw [pow_add]

theorem final {n : ℕ} (P Q : Finset (Finset (Fin n)))
    (hP : (∅ : Finset (Fin n)) ∉ P ∧ ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ P ∧ i ∈ B)
    (hQ : (∅ : Finset (Fin n)) ∉ Q ∧ ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ Q ∧ i ∈ B)
    (a b : Finset (Fin n) → Bool) (X : Finset (Fin n)) :
    (X.powerset.filter (fun T =>
        (∀ B ∈ P, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = a B) ∧
        (∀ B ∈ Q, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = b B))).card =
      if ∀ C ∈ (partsF P Q).filter (fun C => C ⊆ X),
          (((P.filter (fun B => B ⊆ C)).filter (fun B => a B = true)).card +
            ((Q.filter (fun B => B ⊆ C)).filter (fun B => b B = true)).card) % 2 = 0 then
        2 ^ (X.card + ((partsF P Q).filter (fun C => C ⊆ X)).card -
          ((P.filter (fun B => B ⊆ X)).card + (Q.filter (fun B => B ⊆ X)).card))
      else 0 := by
  have key := (charsum ((P.filter (fun B => B ⊆ X)).disjSum (Q.filter (fun B => B ⊆ X)))
    (Sum.elim id id) (Sum.elim a b) X).trans
      (congrArg (fun z : ℤ => 2 ^ X.card * z) (by convert depsum P Q hP hQ a b X))
  rw [Finset.card_disjSum] at key
  replace key : (2:ℤ) ^ ((P.filter (fun B => B ⊆ X)).card + (Q.filter (fun B => B ⊆ X)).card) *
      ((X.powerset.filter (fun T =>
        (∀ B ∈ P, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = a B) ∧
        (∀ B ∈ Q, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = b B))).card : ℤ) =
      2 ^ X.card * ∏ C ∈ (partsF P Q).filter (fun C => C ⊆ X),
        (1 + (-1:ℤ) ^ (((P.filter (fun B => B ⊆ C)).filter (fun B => a B = true)).card +
          ((Q.filter (fun B => B ⊆ C)).filter (fun B => b B = true)).card)) := by
    refine Eq.trans ?_ key
    congr 2
    refine Finset.card_bij (fun T _ => T) (fun T hT => ?_) (fun _ _ _ _ h => h)
      (fun T hT => ⟨T, ?_, rfl⟩)
    · simp only [Finset.mem_filter] at hT ⊢
      refine ⟨hT.1, ?_⟩
      obtain ⟨h1, h2⟩ := hT.2
      intro r hr
      rcases r with B | B
      · simp only [Finset.inl_mem_disjSum, Finset.mem_filter] at hr
        exact h1 B hr.1 hr.2
      · simp only [Finset.inr_mem_disjSum, Finset.mem_filter] at hr
        exact h2 B hr.1 hr.2
    · simp only [Finset.mem_filter] at hT ⊢
      refine ⟨hT.1, ?_⟩
      have h := hT.2
      exact ⟨fun B hB hBX => h (Sum.inl B) (by simp [hB, hBX]),
        fun B hB hBX => h (Sum.inr B) (by simp [hB, hBX])⟩
  split_ifs with hev
  · rw [Finset.prod_congr rfl (fun C hC => by
      rw [(Nat.even_iff.2 (hev C hC)).neg_one_pow]), Finset.prod_const] at key
    norm_num at key
    have key' : 2 ^ ((P.filter (fun B => B ⊆ X)).card + (Q.filter (fun B => B ⊆ X)).card) *
        (X.powerset.filter (fun T =>
        (∀ B ∈ P, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = a B) ∧
        (∀ B ∈ Q, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = b B))).card =
        2 ^ (X.card + ((partsF P Q).filter (fun C => C ⊆ X)).card) := by
      rw [← pow_add] at key; exact_mod_cast key
    obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (Dvd.intro_left _ key')
    rw [hcj, ← pow_add] at key'
    have := Nat.pow_right_injective (le_refl 2) key'
    rw [hcj]; congr 1; omega
  · push_neg at hev
    obtain ⟨C, hC, hodd⟩ := hev
    have hz : (1 + (-1:ℤ) ^ (((P.filter (fun B => B ⊆ C)).filter (fun B => a B = true)).card +
          ((Q.filter (fun B => B ⊆ C)).filter (fun B => b B = true)).card)) = 0 := by
      rw [(Nat.odd_iff.2 (by omega)).neg_one_pow]; norm_num
    rw [Finset.prod_eq_zero hC hz, mul_zero] at key
    have := mul_eq_zero.1 key
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact_mod_cast h

end PEqualNP.Outside.L_lib_1123_aux

theorem PEqualNP.Outside.L_lib_1123 : ∀ (n : Nat) (P Q : Finset (Finset (Fin n))),
  (∀ H ∈ [P, Q], (∅ : Finset (Fin n)) ∉ H ∧
    ∀ i : Fin n, ∃! B : Finset (Fin n), B ∈ H ∧ i ∈ B) →
  let spaces := (Finset.univ : Finset (Finset (Fin n)))
  let closed := fun (C : Finset (Fin n)) =>
    ∀ B ∈ P ∪ Q, Disjoint C B ∨ B ⊆ C
  let parts := spaces.filter (fun C => C.Nonempty ∧ closed C ∧
    ∀ D ∈ C.powerset, D.Nonempty → closed D → D = C)
  let hits := fun (H : Finset (Finset (Fin n))) (s : Finset (Fin n) → Bool)
      (y : Finset (Fin n)) => ∀ B ∈ H, decide ((y ∩ B).card % 2 = 1) = s B
  let count := fun (a b : Finset (Fin n) → Bool) (X : Finset (Fin n)) =>
    (X.powerset.filter (fun T =>
      (∃ y ∈ spaces, y ∩ X = T ∧ hits P a y) ∧
      (∃ z ∈ spaces, z ∩ X = T ∧ hits Q b z))).card

  ∀ (a b : Finset (Fin n) → Bool) (X : Finset (Fin n)),
    let inside := fun (H : Finset (Finset (Fin n))) (C : Finset (Fin n)) =>
      H.filter (fun B => B ⊆ C)
    let intact := inside parts X
    let pos := fun (H : Finset (Finset (Fin n))) (s : Finset (Fin n) → Bool)
        (C : Finset (Fin n)) => ((inside H C).filter (fun B => s B = true)).card
    count a b X =
      if ∀ C ∈ intact, (pos P a C + pos Q b C) % 2 = 0 then
        2 ^ (X.card + intact.card - ((inside P X).card + (inside Q X).card))
      else 0 := by
  intro n P Q hPQ
  have hP := hPQ P (by simp)
  have hQ := hPQ Q (by simp)
  intro spaces closed parts hits count a b X inside intact pos
  have hcount : count a b X = (X.powerset.filter (fun T =>
        (∀ B ∈ P, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = a B) ∧
        (∀ B ∈ Q, B ⊆ X → decide ((T ∩ B).card % 2 = 1) = b B))).card := by
    show (Finset.filter _ _).card = _
    congr 1
    refine Finset.filter_congr fun T hT => ?_
    have hTX := Finset.mem_powerset.1 hT
    exact and_congr
      (PEqualNP.Outside.L_lib_1123_aux.trace P hP.1 hP.2 a X T hTX)
      (PEqualNP.Outside.L_lib_1123_aux.trace Q hQ.1 hQ.2 b X T hTX)
  rw [hcount]
  exact PEqualNP.Outside.L_lib_1123_aux.final P Q hP hQ a b X
