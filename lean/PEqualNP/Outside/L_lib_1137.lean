import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Ring.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1137

open symmDiff

private def chi {α : Type*} [DecidableEq α] (A B : Finset α) : ℤ :=
  ∏ a ∈ A, if a ∈ B then (-1 : ℤ) else 1

private lemma chi_eq_neg_one_pow {α : Type*} [DecidableEq α] (A B : Finset α) :
    chi A B = (-1 : ℤ) ^ (A ∩ B).card := by
  unfold chi
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun a => a ∈ B)]
  have h1 : (∏ x ∈ A.filter (fun a => a ∈ B), if x ∈ B then (-1 : ℤ) else 1) =
      (-1 : ℤ) ^ (A ∩ B).card := by
    have hfilt : A.filter (fun a => a ∈ B) = A ∩ B := by
      ext x; simp
    rw [hfilt]
    calc (∏ x ∈ A ∩ B, if x ∈ B then (-1 : ℤ) else 1)
        = ∏ _x ∈ A ∩ B, (-1 : ℤ) := by
            apply Finset.prod_congr rfl
            intro x hx; simp [(Finset.mem_inter.mp hx).2]
      _ = (-1 : ℤ) ^ (A ∩ B).card := by simp
  have h2 : (∏ x ∈ A.filter (fun a => ¬ a ∈ B), if x ∈ B then (-1 : ℤ) else 1) = 1 := by
    apply Finset.prod_eq_one
    intro x hx
    simp [(Finset.mem_filter.mp hx).2]
  rw [h1, h2, mul_one]

private lemma chi_comm {α : Type*} [DecidableEq α] (A B : Finset α) :
    chi A B = chi B A := by
  rw [chi_eq_neg_one_pow, chi_eq_neg_one_pow, Finset.inter_comm]

private lemma chi_eq_ite_mod {α : Type*} [DecidableEq α] (A B : Finset α) :
    chi A B = if (A ∩ B).card % 2 = 1 then -1 else 1 := by
  rw [chi_eq_neg_one_pow]
  rcases Nat.even_or_odd (A ∩ B).card with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    have hmod : (k + k) % 2 ≠ 1 := by omega
    rw [if_neg hmod]
    simp [← two_mul, pow_mul]
  · rw [hk]
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    simp [hmod, pow_add, pow_mul]

private lemma chi_symmDiff_right {α : Type*} [DecidableEq α] (A B C : Finset α) :
    chi A (B ∆ C) = chi A B * chi A C := by
  unfold chi
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro a _
  by_cases hb : a ∈ B <;> by_cases hc : a ∈ C <;> simp [Finset.mem_symmDiff, hb, hc]

private lemma chi_symmDiff_left {α : Type*} [DecidableEq α] (A B C : Finset α) :
    chi (A ∆ B) C = chi A C * chi B C := by
  rw [chi_comm, chi_symmDiff_right, chi_comm A C, chi_comm B C]

private lemma chi_union_right {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hBC : Disjoint B C) : chi A (B ∪ C) = chi A B * chi A C := by
  have : B ∪ C = B ∆ C := by
    ext x
    simp only [Finset.mem_union, Finset.mem_symmDiff]
    have hnd := Finset.disjoint_left.mp hBC
    tauto
  rw [this, chi_symmDiff_right]

private lemma chi_inter_right_of_subset {α : Type*} [DecidableEq α] {A B S : Finset α}
    (hAS : A ⊆ S) : chi A (B ∩ S) = chi A B := by
  unfold chi
  apply Finset.prod_congr rfl
  intro a ha
  simp [hAS ha]

private lemma sum_chi_powerset {α : Type*} [DecidableEq α] (S A : Finset α) (hAS : A ⊆ S) :
    ∑ B ∈ S.powerset, chi A B = if A = ∅ then (2 : ℤ) ^ S.card else 0 := by
  by_cases hA : A = ∅
  · subst hA
    simp [chi, Finset.card_powerset]
  · simp only [hA, ite_false]
    rcases Finset.nonempty_iff_ne_empty.mpr hA with ⟨a, ha⟩
    have haS : a ∈ S := hAS ha
    let f : Finset α → Finset α := fun B => B ∆ {a}
    have hf_mem : ∀ B ∈ S.powerset, f B ∈ S.powerset := by
      intro B hB
      rw [Finset.mem_powerset] at hB ⊢
      intro x hx
      rw [Finset.mem_symmDiff] at hx
      rcases hx with ⟨hxB, _⟩ | ⟨hxa, _⟩
      · exact hB hxB
      · rw [Finset.mem_singleton.mp hxa]; exact haS
    have hf_inv : ∀ B ∈ S.powerset, f (f B) = B := by
      intro B _
      dsimp [f]
      rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
    have hneg : ∀ B ∈ S.powerset, chi A (f B) = -chi A B := by
      intro B _
      rw [chi_symmDiff_right]
      have : chi A {a} = -1 := by
        rw [chi_eq_neg_one_pow]
        have : A ∩ {a} = {a} := by
          ext x; simp [ha]
        rw [this]; simp
      rw [this]; ring
    have hsum : ∑ B ∈ S.powerset, chi A (f B) = ∑ B ∈ S.powerset, chi A B := by
      refine Finset.sum_bij (fun B _ => f B) hf_mem ?_ ?_ ?_
      · intro B₁ h₁ B₂ h₂ heq
        have := congrArg f heq
        rwa [hf_inv B₁ h₁, hf_inv B₂ h₂] at this
      · intro B hB
        exact ⟨f B, hf_mem B hB, hf_inv B hB⟩
      · intro _ _; rfl
    have hsum2 : ∑ B ∈ S.powerset, chi A (f B) = -(∑ B ∈ S.powerset, chi A B) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl hneg
    omega

private lemma sum_chi_univ {α : Type*} [DecidableEq α] [Fintype α] (A : Finset α) :
    ∑ B : Finset α, chi A B = if A = ∅ then (2 : ℤ) ^ Fintype.card α else 0 := by
  have h1 : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    ext s; simp
  rw [h1, sum_chi_powerset _ _ (Finset.subset_univ A), Finset.card_univ]

private lemma chi_syn_eq_chi_word {m r : Nat} (rows : Fin r → Finset (Fin m))
    (U : Finset (Fin r)) (x : Finset (Fin m)) :
    let syn := fun (x : Finset (Fin m)) =>
      (Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)
    let word := fun (U : Finset (Fin r)) =>
      (Finset.univ : Finset (Fin m)).filter
        (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)
    chi U (syn x) = chi (word U) x := by
  intro syn word
  have hL : chi U (syn x) = ∏ i ∈ U, ∏ j ∈ x, if j ∈ rows i then (-1 : ℤ) else 1 := by
    unfold chi
    apply Finset.prod_congr rfl
    intro i _
    have hmem : i ∈ syn x ↔ ((rows i) ∩ x).card % 2 = 1 := by simp [syn]
    by_cases h : ((rows i) ∩ x).card % 2 = 1
    · have hc : chi (rows i) x = -1 := by rw [chi_eq_ite_mod, if_pos h]
      calc (if i ∈ syn x then (-1 : ℤ) else 1)
          = -1 := if_pos (hmem.mpr h)
        _ = chi (rows i) x := hc.symm
        _ = chi x (rows i) := chi_comm _ _
        _ = _ := rfl
    · have hc : chi (rows i) x = 1 := by rw [chi_eq_ite_mod, if_neg h]
      calc (if i ∈ syn x then (-1 : ℤ) else 1)
          = 1 := if_neg (fun hm => h (hmem.mp hm))
        _ = chi (rows i) x := hc.symm
        _ = chi x (rows i) := chi_comm _ _
        _ = _ := rfl
  have hR : chi (word U) x = ∏ j ∈ x, ∏ i ∈ U, if j ∈ rows i then (-1 : ℤ) else 1 := by
    rw [chi_comm]
    unfold chi
    apply Finset.prod_congr rfl
    intro j _
    have hmem : j ∈ word U ↔ (U.filter (fun i => j ∈ rows i)).card % 2 = 1 := by simp [word]
    have hprod : (∏ i ∈ U, if j ∈ rows i then (-1 : ℤ) else 1) =
        (-1 : ℤ) ^ (U.filter (fun i => j ∈ rows i)).card := by
      rw [← Finset.prod_filter_mul_prod_filter_not U (fun i => j ∈ rows i)]
      have ha : (∏ i ∈ U.filter (fun i => j ∈ rows i), if j ∈ rows i then (-1 : ℤ) else 1) =
          (-1 : ℤ) ^ (U.filter (fun i => j ∈ rows i)).card := by
        calc _ = ∏ _i ∈ U.filter (fun i => j ∈ rows i), (-1 : ℤ) := by
                apply Finset.prod_congr rfl; intro i hi; simp [(Finset.mem_filter.mp hi).2]
          _ = _ := by simp
      have hb : (∏ i ∈ U.filter (fun i => ¬ j ∈ rows i), if j ∈ rows i then (-1 : ℤ) else 1) = 1 := by
        apply Finset.prod_eq_one; intro i hi; simp [(Finset.mem_filter.mp hi).2]
      rw [ha, hb, mul_one]
    rw [hprod]
    rcases Nat.even_or_odd (U.filter (fun i => j ∈ rows i)).card with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hmod : (U.filter (fun i => j ∈ rows i)).card % 2 ≠ 1 := by omega
      rw [if_neg (fun hm => hmod (hmem.mp hm)), hk]
      simp [← two_mul, pow_mul]
    · have hmod : (U.filter (fun i => j ∈ rows i)).card % 2 = 1 := by omega
      rw [if_pos (hmem.mpr hmod), hk]
      simp [pow_add, pow_mul]
  rw [hL, hR, Finset.prod_comm]

private lemma fourier_pin {m r : Nat} (rows : Fin r → Finset (Fin m))
    (s : Finset (Fin r)) (S B : Finset (Fin m)) (hBS : B ⊆ S) :
    let syn := fun (x : Finset (Fin m)) =>
      (Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)
    let word := fun (U : Finset (Fin r)) =>
      (Finset.univ : Finset (Fin m)).filter
        (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)
    ((2 : ℤ) ^ r * (2 : ℤ) ^ S.card) *
      (((Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = s ∧ x ∩ S = B)).card : ℤ) =
    (2 : ℤ) ^ m *
      ∑ U ∈ (Finset.univ : Finset (Finset (Fin r))).filter (fun U => word U ⊆ S),
        chi U s * chi (word U) B := by
  intro syn word
  have hLHS : ((2 : ℤ) ^ r * (2 : ℤ) ^ S.card) *
      (((Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = s ∧ x ∩ S = B)).card : ℤ) =
      ∑ x : Finset (Fin m),
        (∑ U : Finset (Fin r), chi U (syn x ∆ s)) *
        (∑ W ∈ S.powerset, chi W ((x ∩ S) ∆ B)) := by
    have hterm : ∀ x : Finset (Fin m),
        (∑ U : Finset (Fin r), chi U (syn x ∆ s)) *
        (∑ W ∈ S.powerset, chi W ((x ∩ S) ∆ B)) =
        if syn x = s ∧ x ∩ S = B then (2 : ℤ) ^ r * (2 : ℤ) ^ S.card else 0 := by
      intro x
      have h1 : ∑ U : Finset (Fin r), chi U (syn x ∆ s) =
          if syn x = s then (2 : ℤ) ^ r else 0 := by
        have : ∑ U : Finset (Fin r), chi U (syn x ∆ s) =
            ∑ U : Finset (Fin r), chi (syn x ∆ s) U :=
          Finset.sum_congr rfl (fun U _ => chi_comm U _)
        rw [this, sum_chi_univ, Fintype.card_fin]
        by_cases h : syn x = s
        · subst h; simp
        · have hne : syn x ∆ s ≠ ∅ := by
            intro he; exact h (symmDiff_eq_bot.mp he)
          simp [h, hne]
      have h2 : ∑ W ∈ S.powerset, chi W ((x ∩ S) ∆ B) =
          if x ∩ S = B then (2 : ℤ) ^ S.card else 0 := by
        have hsub : (x ∩ S) ∆ B ⊆ S := by
          intro j hj
          rw [Finset.mem_symmDiff] at hj
          rcases hj with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact (Finset.mem_inter.mp h1).2
          · exact hBS h2
        have : ∑ W ∈ S.powerset, chi W ((x ∩ S) ∆ B) =
            ∑ W ∈ S.powerset, chi ((x ∩ S) ∆ B) W :=
          Finset.sum_congr rfl (fun W _ => chi_comm W _)
        rw [this, sum_chi_powerset S _ hsub]
        by_cases h : x ∩ S = B
        · rw [h]; simp
        · have hne : (x ∩ S) ∆ B ≠ ∅ := by
            intro he; exact h (symmDiff_eq_bot.mp he)
          simp [h, hne]
      rw [h1, h2]
      by_cases hs : syn x = s <;> by_cases hb : x ∩ S = B <;> simp [hs, hb]
    calc _ = ∑ _x ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = s ∧ x ∩ S = B),
              ((2 : ℤ) ^ r * (2 : ℤ) ^ S.card) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ x : Finset (Fin m),
            if syn x = s ∧ x ∩ S = B then (2 : ℤ) ^ r * (2 : ℤ) ^ S.card else 0 := by
              rw [Finset.sum_filter]
      _ = _ := Finset.sum_congr rfl (fun x _ => (hterm x).symm)
  rw [hLHS]

  have hexp : ∀ x : Finset (Fin m),
      (∑ U : Finset (Fin r), chi U (syn x ∆ s)) *
      (∑ W ∈ S.powerset, chi W ((x ∩ S) ∆ B)) =
      ∑ U : Finset (Fin r), ∑ W ∈ S.powerset,
        chi U s * chi W B * chi (word U ∆ W) x := by
    intro x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro W hW
    have hWS : W ⊆ S := Finset.mem_powerset.mp hW
    rw [chi_symmDiff_right, chi_symmDiff_right, chi_syn_eq_chi_word rows U x,
        chi_inter_right_of_subset hWS, chi_symmDiff_left]
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : ∑ U : Finset (Fin r), ∑ x : Finset (Fin m), ∑ W ∈ S.powerset,
      chi U s * chi W B * chi (word U ∆ W) x =
      ∑ U : Finset (Fin r), ∑ W ∈ S.powerset,
        chi U s * chi W B * (∑ x : Finset (Fin m), chi (word U ∆ W) x) := by
    apply Finset.sum_congr rfl
    intro U _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro W _
    rw [← Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ U : Finset (Fin r),
      ∑ W ∈ S.powerset, chi U s * chi W B * (∑ x : Finset (Fin m), chi (word U ∆ W) x) =
      if word U ⊆ S then (2 : ℤ) ^ m * (chi U s * chi (word U) B) else 0 := by
    intro U
    have hsumx : ∀ W, ∑ x : Finset (Fin m), chi (word U ∆ W) x =
        if word U = W then (2 : ℤ) ^ m else 0 := by
      intro W
      rw [sum_chi_univ, Fintype.card_fin]
      by_cases h : word U = W
      · subst h; simp
      · have hne : word U ∆ W ≠ ∅ := fun he => h (symmDiff_eq_bot.mp he)
        simp [h, hne]
    simp_rw [hsumx]
    by_cases hU : word U ⊆ S
    · rw [if_pos hU]
      rw [Finset.sum_eq_single (word U)]
      · simp [mul_comm]
      · intro W _ hW
        have hne : word U ≠ W := Ne.symm hW
        simp [hne]
      · intro hnot
        exact absurd (Finset.mem_powerset.mpr hU) hnot
    · rw [if_neg hU]
      apply Finset.sum_eq_zero
      intro W hW
      have hne : word U ≠ W := fun he => hU (he ▸ Finset.mem_powerset.mp hW)
      simp [hne]
  simp_rw [hinner]
  rw [← Finset.sum_filter, ← Finset.mul_sum]

private lemma pin_eq_of_sig_eq {m r : Nat} (rows : Fin r → Finset (Fin m))
    (T : Finset (Fin m)) (k : Nat)
    {d₁ d₂ e₁ e₂ : Finset (Fin r)}
    (hd₁e₁ : Disjoint d₁ e₁) (hd₂e₂ : Disjoint d₂ e₂)
    (hsigd :
      ((Finset.univ : Finset (Finset (Fin r))).filter (fun U =>
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ T ∧
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)).card ≤ k)).filter
        (fun U => (U ∩ d₁).card % 2 = 1) =
      ((Finset.univ : Finset (Finset (Fin r))).filter (fun U =>
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ T ∧
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)).card ≤ k)).filter
        (fun U => (U ∩ d₂).card % 2 = 1))
    (hsige :
      ((Finset.univ : Finset (Finset (Fin r))).filter (fun U =>
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ T ∧
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)).card ≤ k)).filter
        (fun U => (U ∩ e₁).card % 2 = 1) =
      ((Finset.univ : Finset (Finset (Fin r))).filter (fun U =>
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ T ∧
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)).card ≤ k)).filter
        (fun U => (U ∩ e₂).card % 2 = 1))
    (S B : Finset (Fin m)) (hST : S ⊆ T) (hSk : S.card ≤ k) (hBS : B ⊆ S) :
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun x =>
      ((Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)) = d₁ ∪ e₁ ∧
      x ∩ S = B)).card =
    ((Finset.univ : Finset (Finset (Fin m))).filter (fun x =>
      ((Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)) = d₂ ∪ e₂ ∧
      x ∩ S = B)).card := by
  have h1 := fourier_pin rows (d₁ ∪ e₁) S B hBS
  have h2 := fourier_pin rows (d₂ ∪ e₂) S B hBS
  have hsum :
      ∑ U ∈ (Finset.univ : Finset (Finset (Fin r))).filter (fun U =>
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ S),
        chi U (d₁ ∪ e₁) * chi ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) B =
      ∑ U ∈ (Finset.univ : Finset (Finset (Fin r))).filter (fun U =>
        ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ S),
        chi U (d₂ ∪ e₂) * chi ((Finset.univ : Finset (Fin m)).filter
          (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) B := by
    apply Finset.sum_congr rfl
    intro U hU
    have hUS : ((Finset.univ : Finset (Fin m)).filter
        (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ S := (Finset.mem_filter.mp hU).2
    have hUT : ((Finset.univ : Finset (Fin m)).filter
        (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ T := hUS.trans hST
    have hUk : ((Finset.univ : Finset (Fin m)).filter
        (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)).card ≤ k :=
      (Finset.card_le_card hUS).trans hSk
    have hd_iff : (U ∩ d₁).card % 2 = 1 ↔ (U ∩ d₂).card % 2 = 1 := by
      have := Finset.ext_iff.mp hsigd U
      simpa [Finset.mem_filter, hUT, hUk] using this
    have he_iff : (U ∩ e₁).card % 2 = 1 ↔ (U ∩ e₂).card % 2 = 1 := by
      have := Finset.ext_iff.mp hsige U
      simpa [Finset.mem_filter, hUT, hUk] using this
    rw [chi_union_right hd₁e₁, chi_union_right hd₂e₂,
        chi_eq_ite_mod U d₁, chi_eq_ite_mod U d₂,
        chi_eq_ite_mod U e₁, chi_eq_ite_mod U e₂]
    simp [hd_iff, he_iff]
  have hEq : ((2 : ℤ) ^ r * (2 : ℤ) ^ S.card) *
      (((Finset.univ : Finset (Finset (Fin m))).filter (fun x =>
        ((Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)) = d₁ ∪ e₁ ∧
        x ∩ S = B)).card : ℤ) =
      ((2 : ℤ) ^ r * (2 : ℤ) ^ S.card) *
      (((Finset.univ : Finset (Finset (Fin m))).filter (fun x =>
        ((Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)) = d₂ ∪ e₂ ∧
        x ∩ S = B)).card : ℤ) := by
    dsimp only at h1 h2
    rw [h1, h2, hsum]
  have hpos : ((2 : ℤ) ^ r * (2 : ℤ) ^ S.card) ≠ 0 := by positivity
  exact Nat.cast_injective (mul_left_cancel₀ hpos hEq)

private lemma prod_one_sub_indicator {α : Type*} [DecidableEq α] [Fintype α]
    (P : α → Prop) [DecidablePred P] :
    (∏ i : α, (1 - if P i then (1 : ℤ) else 0)) =
      ∑ J : Finset α, (-1 : ℤ) ^ J.card * if ∀ i ∈ J, P i then (1 : ℤ) else 0 := by
  have h1 : ∀ i : α, (1 - if P i then (1 : ℤ) else 0) = (if P i then (-1 : ℤ) else 0) + (1 : ℤ) := by
    intro i; by_cases h : P i <;> simp [h]
  simp_rw [h1]
  rw [Finset.prod_add]
  have hpow : (Finset.univ : Finset α).powerset = Finset.univ := by ext s; simp
  rw [hpow]
  apply Finset.sum_congr rfl
  intro J _
  simp only [Finset.prod_const_one, mul_one]
  by_cases hJ : ∀ i ∈ J, P i
  · rw [if_pos hJ, mul_one]
    calc (∏ i ∈ J, if P i then (-1 : ℤ) else 0)
        = ∏ _i ∈ J, (-1 : ℤ) := Finset.prod_congr rfl (fun i hi => by simp [hJ i hi])
      _ = (-1 : ℤ) ^ J.card := by simp
  · rw [if_neg hJ, mul_zero]
    have hex : ∃ i ∈ J, ¬ P i := by
      by_contra h
      exact hJ (fun i hi => by by_contra hp; exact h ⟨i, hi, hp⟩)
    rcases hex with ⟨i, hi, hni⟩
    exact Finset.prod_eq_zero hi (by simp [hni])

private lemma sep_of_disjoint_diff {m r : Nat} (rows : Fin r → Finset (Fin m))
    (T : Finset (Fin m)) (t w : Nat) (hw : 0 < w) (counting : Bool)
    {d₁ d₂ e : Finset (Fin r)} (x₁ : Finset (Fin m))
    (hx₁ : ((Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x₁).card % 2 = 1)) = d₁ ∪ e)
    (hdisj₁ : Disjoint d₁ e) (hdisj₂ : Disjoint d₂ e)
    (U : Finset (Fin r))
    (hUT : ((Finset.univ : Finset (Fin m)).filter
      (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)) ⊆ T)
    (hUk : ((Finset.univ : Finset (Fin m)).filter
      (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)).card ≤ if counting then t * w else t)
    (hpar : (U ∩ d₁).card % 2 ≠ (U ∩ d₂).card % 2) :
    let syn := fun (x : Finset (Fin m)) =>
      (Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)
    let Clause := Finset (Fin m × Bool)
    let valid := fun (F : Finset Clause) => F.card ≤ t ∧
      ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T
    let mass := fun (d e : Finset (Fin r)) (F : Finset Clause) =>
      ((Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = d ∪ e ∧
        ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).card
    ∃ F, valid F ∧
      (if counting then mass d₁ e F else min 1 (mass d₁ e F)) ≠
      (if counting then mass d₂ e F else min 1 (mass d₂ e F)) := by
  intro syn Clause valid mass
  let W := (Finset.univ : Finset (Fin m)).filter
    (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)
  have hno2 : ∀ x : Finset (Fin m), syn x = d₂ ∪ e → x ∩ W ≠ x₁ ∩ W := by
    intro x hxs hxw
    have hchi1 : chi U (d₁ ∪ e) = chi W x₁ := by
      rw [← hx₁]
      exact chi_syn_eq_chi_word rows U x₁
    have hchi2 : chi U (d₂ ∪ e) = chi W x := by
      rw [← hxs]
      exact chi_syn_eq_chi_word rows U x
    have hW : chi W x = chi W x₁ := by
      calc chi W x = chi W (x ∩ W) := (chi_inter_right_of_subset (Finset.Subset.refl W)).symm
        _ = chi W (x₁ ∩ W) := by rw [hxw]
        _ = chi W x₁ := chi_inter_right_of_subset (Finset.Subset.refl W)
    have hEq : chi U d₁ * chi U e = chi U d₂ * chi U e := by
      rw [← chi_union_right hdisj₁, ← chi_union_right hdisj₂, hchi1, hchi2, hW]
    have hne0 : chi U e ≠ 0 := by
      rw [chi_eq_ite_mod]; split <;> decide
    have hdEq : chi U d₁ = chi U d₂ := mul_right_cancel₀ hne0 hEq
    rw [chi_eq_ite_mod, chi_eq_ite_mod] at hdEq
    have h1 : (U ∩ d₁).card % 2 < 2 := Nat.mod_lt _ (by omega)
    have h2 : (U ∩ d₂).card % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases hp1 : (U ∩ d₁).card % 2 = 1 <;> by_cases hp2 : (U ∩ d₂).card % 2 = 1
    · exact hpar (by omega)
    · simp [hp1, hp2] at hdEq
    · simp [hp1, hp2] at hdEq
    · exact hpar (by omega)
  cases counting with
  | false =>
    simp only [Bool.false_eq_true, ite_false] at hUk ⊢
    let F : Finset Clause := W.image (fun j => {(j, decide (j ∈ x₁))})
    refine ⟨F, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.card_image_le.trans hUk
    · intro C hC
      rcases Finset.mem_image.mp hC with ⟨j, hj, rfl⟩
      refine ⟨by rw [Finset.card_singleton]; omega, ?_⟩
      intro l hl
      rw [Finset.mem_singleton.mp hl]
      exact hUT hj
    · have hpos1 : 0 < mass d₁ e F := by
        apply Finset.card_pos.mpr
        refine ⟨x₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₁, ?_⟩⟩
        intro C hC
        rcases Finset.mem_image.mp hC with ⟨j, _, rfl⟩
        exact ⟨(j, decide (j ∈ x₁)), Finset.mem_singleton_self _, rfl⟩
      have hzero2 : mass d₂ e F = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro x _ ⟨hxs, hsat⟩
        apply hno2 x hxs
        ext j
        simp only [Finset.mem_inter]
        constructor
        · rintro ⟨hjx, hjW⟩
          refine ⟨?_, hjW⟩
          have hC : ({(j, decide (j ∈ x₁))} : Clause) ∈ F :=
            Finset.mem_image.mpr ⟨j, hjW, rfl⟩
          rcases hsat _ hC with ⟨l, hl, hle⟩
          rw [Finset.mem_singleton.mp hl] at hle
          simp only [hjx, decide_true] at hle
          exact of_decide_eq_true hle.symm
        · rintro ⟨hjx1, hjW⟩
          refine ⟨?_, hjW⟩
          have hC : ({(j, decide (j ∈ x₁))} : Clause) ∈ F :=
            Finset.mem_image.mpr ⟨j, hjW, rfl⟩
          rcases hsat _ hC with ⟨l, hl, hle⟩
          rw [Finset.mem_singleton.mp hl] at hle
          simp only [hjx1, decide_true] at hle
          exact of_decide_eq_true hle
      rw [hzero2]
      omega
  | true =>
    simp only [ite_true] at hUk ⊢
    let L := W.toList
    have hLlen : L.length ≤ t * w := by simpa [L] using hUk
    let B : Fin t → Finset (Fin m) := fun i => ((L.drop (i.val * w)).take w).toFinset
    have hBsub : ∀ i : Fin t, B i ⊆ W := by
      intro i j hj
      have hjL : j ∈ L := List.mem_of_mem_drop (List.mem_of_mem_take (List.mem_toFinset.mp hj))
      exact Finset.mem_toList.mp hjL
    have hBcard : ∀ i : Fin t, (B i).card ≤ w := by
      intro i
      exact (List.toFinset_card_le _).trans (List.length_take_le _ _)
    have hBcov : ∀ j ∈ W, ∃ i : Fin t, j ∈ B i := by
      intro j hj
      have hjL : j ∈ L := Finset.mem_toList.mpr hj
      rcases List.getElem_of_mem hjL with ⟨idx, hidx, hget⟩
      have hdiv : idx / w < t := by
        have hlt : idx < t * w := lt_of_lt_of_le hidx hLlen
        exact (Nat.div_lt_iff_lt_mul hw).mpr hlt
      refine ⟨⟨idx / w, hdiv⟩, List.mem_toFinset.mpr ?_⟩
      have hmod : idx % w < w := Nat.mod_lt idx hw
      have hidx_eq : idx = (idx / w) * w + idx % w := by
        have := Nat.div_add_mod idx w
        rw [mul_comm] at this
        omega
      have hlen_drop : idx % w < (L.drop ((idx / w) * w)).length := by
        rw [List.length_drop]; omega
      have hlen_take : idx % w < ((L.drop ((idx / w) * w)).take w).length := by
        rw [List.length_take]; omega
      rw [← hget]
      have hget' : ((L.drop ((idx / w) * w)).take w)[idx % w]'hlen_take = L[idx]'hidx := by
        rw [List.getElem_take, List.getElem_drop]
        congr 1; omega
      rw [← hget']
      exact List.getElem_mem hlen_take
    let C : Fin t → Clause := fun i => (B i).image (fun j => (j, !(decide (j ∈ x₁))))
    have hCsat : ∀ (x : Finset (Fin m)) (i : Fin t),
        (∃ l ∈ C i, decide (l.1 ∈ x) = l.2) ↔ x ∩ B i ≠ x₁ ∩ B i := by
      intro x i
      constructor
      · rintro ⟨l, hl, hle⟩ heq
        rcases Finset.mem_image.mp hl with ⟨j, hjB, rfl⟩
        have hmem := Finset.ext_iff.mp heq j
        simp only [Finset.mem_inter, hjB, and_true] at hmem
        by_cases hjx : j ∈ x
        · have hjx1 : j ∈ x₁ := hmem.mp hjx
          simp [hjx, hjx1] at hle
        · have hjx1 : j ∉ x₁ := fun h => hjx (hmem.mpr h)
          simp [hjx, hjx1] at hle
      · intro hne
        have hex : ∃ j ∈ B i, ¬ (j ∈ x ↔ j ∈ x₁) := by
          by_contra hall
          apply hne
          ext j
          simp only [Finset.mem_inter]
          by_cases hjB : j ∈ B i
          · have : j ∈ x ↔ j ∈ x₁ := by
              by_contra h; exact hall ⟨j, hjB, h⟩
            simp [hjB, this]
          · simp [hjB]
        rcases hex with ⟨j, hjB, hdiff⟩
        refine ⟨(j, !(decide (j ∈ x₁))), Finset.mem_image.mpr ⟨j, hjB, rfl⟩, ?_⟩
        by_cases hjx : j ∈ x <;> by_cases hjx1 : j ∈ x₁ <;> simp_all
    let FJ : Finset (Fin t) → Finset Clause := fun J => J.image C
    have hFJ_valid : ∀ J : Finset (Fin t), valid (FJ J) := by
      intro J
      refine ⟨Finset.card_image_le.trans (by simpa using Finset.card_le_univ J), ?_⟩
      intro cl hcl
      rcases Finset.mem_image.mp hcl with ⟨i, _, rfl⟩
      refine ⟨Finset.card_image_le.trans (hBcard i), ?_⟩
      intro l hl
      rcases Finset.mem_image.mp hl with ⟨j, hjB, rfl⟩
      exact hUT (hBsub i hjB)
    have hie : ∀ d : Finset (Fin r),
        (((Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = d ∪ e ∧ x ∩ W = x₁ ∩ W)).card : ℤ) =
        ∑ J : Finset (Fin t), (-1 : ℤ) ^ J.card * (mass d e (FJ J) : ℤ) := by
      intro d
      have hpoint : ∀ x : Finset (Fin m),
          (if x ∩ W = x₁ ∩ W then (1 : ℤ) else 0) =
          ∑ J : Finset (Fin t), (-1 : ℤ) ^ J.card *
            if ∀ cl ∈ FJ J, ∃ l ∈ cl, decide (l.1 ∈ x) = l.2 then (1 : ℤ) else 0 := by
        intro x
        have heq_iff : x ∩ W = x₁ ∩ W ↔ ∀ i : Fin t, ¬ (x ∩ B i ≠ x₁ ∩ B i) := by
          constructor
          · intro h i hne
            apply hne
            ext j
            simp only [Finset.mem_inter]
            by_cases hjB : j ∈ B i
            · have := Finset.ext_iff.mp h j
              simp only [Finset.mem_inter, hBsub i hjB, and_true] at this
              simp [hjB, this]
            · simp [hjB]
          · intro h
            ext j
            simp only [Finset.mem_inter]
            by_cases hjW : j ∈ W
            · rcases hBcov j hjW with ⟨i, hi⟩
              have hi' : x ∩ B i = x₁ ∩ B i := not_not.mp (h i)
              have := Finset.ext_iff.mp hi' j
              simp only [Finset.mem_inter, hi, and_true] at this
              simp [hjW, this]
            · simp [hjW]
        have hprod : (if x ∩ W = x₁ ∩ W then (1 : ℤ) else 0) =
            ∏ i : Fin t, (1 - if x ∩ B i ≠ x₁ ∩ B i then (1 : ℤ) else 0) := by
          by_cases h : x ∩ W = x₁ ∩ W
          · rw [if_pos h]
            symm
            apply Finset.prod_eq_one
            intro i _
            have := heq_iff.mp h i
            simp [this]
          · rw [if_neg h]
            have hex : ∃ i : Fin t, x ∩ B i ≠ x₁ ∩ B i := by
              by_contra hall
              exact h (heq_iff.mpr (fun i hi => hall ⟨i, hi⟩))
            rcases hex with ⟨i, hi⟩
            symm
            exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
        rw [hprod, prod_one_sub_indicator]
        apply Finset.sum_congr rfl
        intro J _
        congr 1
        have hsat_iff : (∀ i ∈ J, x ∩ B i ≠ x₁ ∩ B i) ↔
            (∀ cl ∈ FJ J, ∃ l ∈ cl, decide (l.1 ∈ x) = l.2) := by
          constructor
          · intro h cl hcl
            rcases Finset.mem_image.mp hcl with ⟨i, hi, rfl⟩
            exact (hCsat x i).mpr (h i hi)
          · intro h i hi
            exact (hCsat x i).mp (h (C i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
        by_cases hJ : ∀ i ∈ J, x ∩ B i ≠ x₁ ∩ B i
        · rw [if_pos hJ, if_pos (hsat_iff.mp hJ)]
        · rw [if_neg hJ, if_neg (fun h => hJ (hsat_iff.mpr h))]
      calc (((Finset.univ : Finset (Finset (Fin m))).filter
              (fun x => syn x = d ∪ e ∧ x ∩ W = x₁ ∩ W)).card : ℤ)
          = ∑ x ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = d ∪ e),
              if x ∩ W = x₁ ∩ W then (1 : ℤ) else 0 := by
              rw [Finset.sum_boole]
              congr 2; ext x; simp [Finset.mem_filter]
        _ = ∑ x ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = d ∪ e),
              ∑ J : Finset (Fin t), (-1 : ℤ) ^ J.card *
                if ∀ cl ∈ FJ J, ∃ l ∈ cl, decide (l.1 ∈ x) = l.2 then (1 : ℤ) else 0 :=
              Finset.sum_congr rfl (fun x _ => hpoint x)
        _ = ∑ J : Finset (Fin t),
              ∑ x ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun x => syn x = d ∪ e),
                (-1 : ℤ) ^ J.card *
                  if ∀ cl ∈ FJ J, ∃ l ∈ cl, decide (l.1 ∈ x) = l.2 then (1 : ℤ) else 0 :=
              Finset.sum_comm
        _ = ∑ J : Finset (Fin t), (-1 : ℤ) ^ J.card * (mass d e (FJ J) : ℤ) := by
              apply Finset.sum_congr rfl
              intro J _
              rw [← Finset.mul_sum, Finset.sum_boole]
              congr 3; ext x; simp [Finset.mem_filter]
    by_contra hall
    have hEq_all : ∀ J : Finset (Fin t), mass d₁ e (FJ J) = mass d₂ e (FJ J) := by
      intro J
      by_contra hne
      exact hall ⟨FJ J, hFJ_valid J, hne⟩
    have hpin_eq :
        (((Finset.univ : Finset (Finset (Fin m))).filter
          (fun x => syn x = d₁ ∪ e ∧ x ∩ W = x₁ ∩ W)).card : ℤ) =
        (((Finset.univ : Finset (Finset (Fin m))).filter
          (fun x => syn x = d₂ ∪ e ∧ x ∩ W = x₁ ∩ W)).card : ℤ) := by
      rw [hie d₁, hie d₂]
      apply Finset.sum_congr rfl
      intro J _; rw [hEq_all J]
    have hpos1 : 0 < ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => syn x = d₁ ∪ e ∧ x ∩ W = x₁ ∩ W)).card :=
      Finset.card_pos.mpr ⟨x₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₁, rfl⟩⟩
    have hzero2 : ((Finset.univ : Finset (Finset (Fin m))).filter
        (fun x => syn x = d₂ ∪ e ∧ x ∩ W = x₁ ∩ W)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x _ ⟨hxs, hxw⟩
      exact hno2 x hxs hxw
    rw [hzero2] at hpin_eq
    omega

theorem main_proof : (∀ (m r : Nat) (rows : Fin r → Finset (Fin m)) (I : Finset (Fin r))
    (T : Finset (Fin m)) (t w : Nat), 0 < w →
  let xs := (Finset.univ : Finset (Finset (Fin m)))
  let ys := (Finset.univ : Finset (Finset (Fin r)))
  let parity := fun (U d : Finset (Fin r)) => (U ∩ d).card % 2
  let syn := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)
  let word := fun (U : Finset (Fin r)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)
  let lefts := xs.image (fun x => syn x ∩ I)
  let rights := xs.image (fun x => syn x \ I)
  let Clause := Finset (Fin m × Bool)
  let valid := fun (F : Finset Clause) => F.card ≤ t ∧
    ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T
  let mass := fun (d e : Finset (Fin r)) (F : Finset Clause) =>
    (xs.filter (fun x => syn x = d ∪ e ∧
      ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).card
  ∀ (counting : Bool) (a b : Nat),
    let k := if counting then t * w else t
    let probes := ys.filter (fun U => word U ⊆ T ∧ (word U).card ≤ k)
    let sig := fun (d : Finset (Fin r)) => probes.filter (fun U => parity U d = 1)
    (∃ (L : Finset (Fin r) → Fin a) (R : Finset (Fin r) → Fin b)
       (decode : Fin a → Fin b → Finset Clause → Nat),
      ∀ d ∈ lefts, ∀ e ∈ rights, ∀ F, valid F →
        decode (L d) (R e) F = if counting then mass d e F else min 1 (mass d e F)) ↔
      (lefts.image sig).card ≤ a ∧ (rights.image sig).card ≤ b) := by
  intro m r rows I T t w hw xs ys parity syn word lefts rights Clause valid mass counting a b k probes sig
  have hdisj_lr : ∀ d ∈ lefts, ∀ e ∈ rights, Disjoint d e := by
    intro d hd e he
    rcases Finset.mem_image.mp hd with ⟨x, _, rfl⟩
    rcases Finset.mem_image.mp he with ⟨y, _, rfl⟩
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    exact (Finset.mem_sdiff.mp hi2).2 (Finset.mem_inter.mp hi1).2
  constructor
  ·
    rintro ⟨L, R, decode, hdec⟩
    constructor
    ·
      have hinj : ∀ d₁ ∈ lefts, ∀ d₂ ∈ lefts, L d₁ = L d₂ → sig d₁ = sig d₂ := by
        intro d₁ hd₁ d₂ hd₂ hL
        by_contra hsig
        have hex : ∃ U ∈ probes, parity U d₁ ≠ parity U d₂ := by
          by_contra hall
          apply hsig
          ext U
          simp only [sig, Finset.mem_filter]
          constructor <;> rintro ⟨hUp, hp⟩ <;> refine ⟨hUp, ?_⟩
          · have : parity U d₁ = parity U d₂ := by
              by_contra h; exact hall ⟨U, hUp, h⟩
            omega
          · have : parity U d₁ = parity U d₂ := by
              by_contra h; exact hall ⟨U, hUp, h⟩
            omega
        rcases hex with ⟨U, hUp, hpar⟩
        rcases Finset.mem_filter.mp hUp with ⟨_, hUT, hUk⟩
        rcases Finset.mem_image.mp hd₁ with ⟨x₁, _, hx₁eq⟩
        let e := syn x₁ \ I
        have he : e ∈ rights := Finset.mem_image.mpr ⟨x₁, Finset.mem_univ _, rfl⟩
        have hx₁ : syn x₁ = d₁ ∪ e := by
          rw [← hx₁eq]; ext i; simp only [e, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          by_cases hi : i ∈ I <;> simp [hi]
        have hsep := sep_of_disjoint_diff rows T t w hw counting x₁ hx₁
          (hdisj_lr d₁ hd₁ e he) (hdisj_lr d₂ hd₂ e he) U hUT hUk hpar
        rcases hsep with ⟨F, hFv, hne⟩
        have h1 := hdec d₁ hd₁ e he F hFv
        have h2 := hdec d₂ hd₂ e he F hFv
        rw [hL] at h1
        exact hne (h1.symm.trans h2)

      let f : {s // s ∈ lefts.image sig} → Fin a := fun s =>
        L (Classical.choose (Finset.mem_image.mp s.2))
      have hf_inj : Function.Injective f := by
        rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ hEq
        have h1 := Classical.choose_spec (Finset.mem_image.mp hs₁)
        have h2 := Classical.choose_spec (Finset.mem_image.mp hs₂)
        have hsEq := hinj _ h1.1 _ h2.1 hEq
        apply Subtype.ext
        dsimp only
        rw [← h1.2, ← h2.2, hsEq]
      calc (lefts.image sig).card
          = Fintype.card {s // s ∈ lefts.image sig} := (Fintype.card_coe _).symm
        _ ≤ Fintype.card (Fin a) := Fintype.card_le_of_injective f hf_inj
        _ = a := Fintype.card_fin a
    ·
      have hinj : ∀ e₁ ∈ rights, ∀ e₂ ∈ rights, R e₁ = R e₂ → sig e₁ = sig e₂ := by
        intro e₁ he₁ e₂ he₂ hR
        by_contra hsig
        have hex : ∃ U ∈ probes, parity U e₁ ≠ parity U e₂ := by
          by_contra hall
          apply hsig
          ext U
          simp only [sig, Finset.mem_filter]
          constructor <;> rintro ⟨hUp, hp⟩ <;> refine ⟨hUp, ?_⟩
          · have : parity U e₁ = parity U e₂ := by
              by_contra h; exact hall ⟨U, hUp, h⟩
            omega
          · have : parity U e₁ = parity U e₂ := by
              by_contra h; exact hall ⟨U, hUp, h⟩
            omega
        rcases hex with ⟨U, hUp, hpar⟩
        rcases Finset.mem_filter.mp hUp with ⟨_, hUT, hUk⟩
        rcases Finset.mem_image.mp he₁ with ⟨x₁, _, hx₁eq⟩
        let d := syn x₁ ∩ I
        have hd : d ∈ lefts := Finset.mem_image.mpr ⟨x₁, Finset.mem_univ _, rfl⟩
        have hx₁ : syn x₁ = e₁ ∪ d := by
          rw [← hx₁eq]; ext i; simp only [d, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
          by_cases hi : i ∈ I <;> simp [hi]
        have hsep := sep_of_disjoint_diff rows T t w hw counting x₁ hx₁
          (hdisj_lr d hd e₁ he₁).symm (hdisj_lr d hd e₂ he₂).symm U hUT hUk hpar
        rcases hsep with ⟨F, hFv, hne⟩
        have h1 := hdec d hd e₁ he₁ F hFv
        have h2 := hdec d hd e₂ he₂ F hFv
        rw [hR] at h1
        have hcomm1 : mass d e₁ F = (xs.filter (fun x => syn x = e₁ ∪ d ∧
            ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).card := by
          dsimp only [mass]; rw [Finset.union_comm d e₁]
        have hcomm2 : mass d e₂ F = (xs.filter (fun x => syn x = e₂ ∪ d ∧
            ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).card := by
          dsimp only [mass]; rw [Finset.union_comm d e₂]
        rw [hcomm1] at h1
        rw [hcomm2] at h2
        exact hne (h1.symm.trans h2)
      let f : {s // s ∈ rights.image sig} → Fin b := fun s =>
        R (Classical.choose (Finset.mem_image.mp s.2))
      have hf_inj : Function.Injective f := by
        rintro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ hEq
        have h1 := Classical.choose_spec (Finset.mem_image.mp hs₁)
        have h2 := Classical.choose_spec (Finset.mem_image.mp hs₂)
        have hsEq := hinj _ h1.1 _ h2.1 hEq
        apply Subtype.ext
        dsimp only
        rw [← h1.2, ← h2.2, hsEq]
      calc (rights.image sig).card
          = Fintype.card {s // s ∈ rights.image sig} := (Fintype.card_coe _).symm
        _ ≤ Fintype.card (Fin b) := Fintype.card_le_of_injective f hf_inj
        _ = b := Fintype.card_fin b
  ·
    rintro ⟨ha, hb⟩
    have hLne : (lefts.image sig).Nonempty :=
      ⟨sig (syn ∅ ∩ I), Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨∅, Finset.mem_univ _, rfl⟩, rfl⟩⟩
    have hRne : (rights.image sig).Nonempty :=
      ⟨sig (syn ∅ \ I), Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨∅, Finset.mem_univ _, rfl⟩, rfl⟩⟩
    have ha_pos : 0 < a := lt_of_lt_of_le (Finset.card_pos.mpr hLne) ha
    have hb_pos : 0 < b := lt_of_lt_of_le (Finset.card_pos.mpr hRne) hb
    let eL := (lefts.image sig).equivFin
    let eR := (rights.image sig).equivFin
    let L : Finset (Fin r) → Fin a := fun d =>
      if h : sig d ∈ lefts.image sig then Fin.castLE ha (eL ⟨sig d, h⟩) else ⟨0, ha_pos⟩
    let R : Finset (Fin r) → Fin b := fun e =>
      if h : sig e ∈ rights.image sig then Fin.castLE hb (eR ⟨sig e, h⟩) else ⟨0, hb_pos⟩
    have hL_inj : ∀ d₁ ∈ lefts, ∀ d₂ ∈ lefts, L d₁ = L d₂ → sig d₁ = sig d₂ := by
      intro d₁ hd₁ d₂ hd₂ hEq
      have h1 : sig d₁ ∈ lefts.image sig := Finset.mem_image.mpr ⟨d₁, hd₁, rfl⟩
      have h2 : sig d₂ ∈ lefts.image sig := Finset.mem_image.mpr ⟨d₂, hd₂, rfl⟩
      simp only [L, h1, h2, dite_true] at hEq
      have hfin := Fin.castLE_injective ha hEq
      exact congrArg Subtype.val (eL.injective hfin)
    have hR_inj : ∀ e₁ ∈ rights, ∀ e₂ ∈ rights, R e₁ = R e₂ → sig e₁ = sig e₂ := by
      intro e₁ he₁ e₂ he₂ hEq
      have h1 : sig e₁ ∈ rights.image sig := Finset.mem_image.mpr ⟨e₁, he₁, rfl⟩
      have h2 : sig e₂ ∈ rights.image sig := Finset.mem_image.mpr ⟨e₂, he₂, rfl⟩
      simp only [R, h1, h2, dite_true] at hEq
      have hfin := Fin.castLE_injective hb hEq
      exact congrArg Subtype.val (eR.injective hfin)
    have hmass_eq : ∀ d₁ ∈ lefts, ∀ d₂ ∈ lefts, ∀ e₁ ∈ rights, ∀ e₂ ∈ rights,
        sig d₁ = sig d₂ → sig e₁ = sig e₂ → ∀ F, valid F →
        (if counting then mass d₁ e₁ F else min 1 (mass d₁ e₁ F)) =
        (if counting then mass d₂ e₂ F else min 1 (mass d₂ e₂ F)) := by
      intro d₁ hd₁ d₂ hd₂ e₁ he₁ e₂ he₂ hsd hse F hFv
      have hpin := pin_eq_of_sig_eq rows T k (hdisj_lr d₁ hd₁ e₁ he₁) (hdisj_lr d₂ hd₂ e₂ he₂) hsd hse
      cases counting with
      | true =>
        simp only [ite_true]
        let S : Finset (Fin m) := F.biUnion (fun C => C.image Prod.fst)
        have hST : S ⊆ T := by
          intro j hj
          rcases Finset.mem_biUnion.mp hj with ⟨C, hCF, hjC⟩
          rcases Finset.mem_image.mp hjC with ⟨l, hlC, rfl⟩
          exact (hFv.2 C hCF).2 l hlC
        have hSk : S.card ≤ k := by
          change S.card ≤ t * w
          calc S.card
              ≤ ∑ C ∈ F, (C.image Prod.fst).card := Finset.card_biUnion_le
            _ ≤ ∑ _C ∈ F, w := Finset.sum_le_sum (fun C hC => Finset.card_image_le.trans (hFv.2 C hC).1)
            _ = F.card * w := by simp
            _ ≤ t * w := Nat.mul_le_mul_right w hFv.1
        have hpart : ∀ d e : Finset (Fin r),
            mass d e F = ∑ B ∈ S.powerset.filter (fun B => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ B) = l.2),
              (xs.filter (fun x => syn x = d ∪ e ∧ x ∩ S = B)).card := by
          intro d e
          have hmap : ∀ x ∈ xs.filter (fun x => syn x = d ∪ e ∧
                ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2),
              x ∩ S ∈ S.powerset.filter (fun B => ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ B) = l.2) := by
            intro x hx
            rcases Finset.mem_filter.mp hx with ⟨_, _, hsat⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
            intro C hCF
            rcases hsat C hCF with ⟨l, hlC, hle⟩
            have hlS : l.1 ∈ S :=
              Finset.mem_biUnion.mpr ⟨C, hCF, Finset.mem_image.mpr ⟨l, hlC, rfl⟩⟩
            exact ⟨l, hlC, by simpa [Finset.mem_inter, hlS] using hle⟩
          dsimp only [mass]
          rw [Finset.card_eq_sum_card_fiberwise hmap]
          apply Finset.sum_congr rfl
          intro B hB
          rcases Finset.mem_filter.mp hB with ⟨_, hBsat⟩
          congr 1; ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hx, hsyn, _⟩, hxB⟩
            exact ⟨hx, hsyn, hxB⟩
          · rintro ⟨hx, hsyn, hxB⟩
            refine ⟨⟨hx, hsyn, ?_⟩, hxB⟩
            intro C hCF
            rcases hBsat C hCF with ⟨l, hlC, hle⟩
            have hlS : l.1 ∈ S :=
              Finset.mem_biUnion.mpr ⟨C, hCF, Finset.mem_image.mpr ⟨l, hlC, rfl⟩⟩
            have : l.1 ∈ x ↔ l.1 ∈ B := by
              rw [← hxB]; simp [Finset.mem_inter, hlS]
            exact ⟨l, hlC, by simpa [this] using hle⟩
        rw [hpart d₁ e₁, hpart d₂ e₂]
        apply Finset.sum_congr rfl
        intro B hB
        exact hpin S B hST hSk (Finset.mem_powerset.mp (Finset.mem_filter.mp hB).1)
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        have hpos_iff : ∀ (d₁' d₂' e₁' e₂' : Finset (Fin r)),
            (∀ S B, S ⊆ T → S.card ≤ k → B ⊆ S →
              (xs.filter (fun x => syn x = d₁' ∪ e₁' ∧ x ∩ S = B)).card =
              (xs.filter (fun x => syn x = d₂' ∪ e₂' ∧ x ∩ S = B)).card) →
            0 < mass d₁' e₁' F → 0 < mass d₂' e₂' F := by
          intro d₁' d₂' e₁' e₂' hpin' hpos
          rcases Finset.card_pos.mp hpos with ⟨x, hx⟩
          rcases Finset.mem_filter.mp hx with ⟨_, hsyn, hsat⟩
          let pickLit : {C // C ∈ F} → Fin m × Bool := fun C => Classical.choose (hsat C.1 C.2)
          let S : Finset (Fin m) := F.attach.image (fun C => (pickLit C).1)
          have hST : S ⊆ T := by
            intro j hj
            rcases Finset.mem_image.mp hj with ⟨C, _, rfl⟩
            have hspec := Classical.choose_spec (hsat C.1 C.2)
            exact (hFv.2 C.1 C.2).2 _ hspec.1
          have hSk : S.card ≤ k := by
            change S.card ≤ t
            exact Finset.card_image_le.trans (by simpa using hFv.1)
          have hposS : 0 < (xs.filter (fun y => syn y = d₁' ∪ e₁' ∧ y ∩ S = x ∩ S)).card :=
            Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsyn, rfl⟩⟩
          rw [hpin' S (x ∩ S) hST hSk Finset.inter_subset_right] at hposS
          rcases Finset.card_pos.mp hposS with ⟨y, hy⟩
          rcases Finset.mem_filter.mp hy with ⟨_, hysyn, hyS⟩
          apply Finset.card_pos.mpr
          refine ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hysyn, ?_⟩⟩
          intro C hCF
          have hspec := Classical.choose_spec (hsat C hCF)
          let l := pickLit ⟨C, hCF⟩
          have hlS : l.1 ∈ S := Finset.mem_image.mpr ⟨⟨C, hCF⟩, Finset.mem_attach _ _, rfl⟩
          have hmem : l.1 ∈ y ↔ l.1 ∈ x := by
            have := Finset.ext_iff.mp hyS l.1
            simpa [Finset.mem_inter, hlS] using this
          exact ⟨l, hspec.1, by simpa [hmem] using hspec.2⟩
        have h12 := hpos_iff d₁ d₂ e₁ e₂ hpin
        have h21 := hpos_iff d₂ d₁ e₂ e₁ (fun S B h1 h2 h3 => (hpin S B h1 h2 h3).symm)
        by_cases h1 : 0 < mass d₁ e₁ F
        · have h2 := h12 h1; omega
        · have h2 : ¬ 0 < mass d₂ e₂ F := fun h => h1 (h21 h); omega
    classical
    let decode : Fin a → Fin b → Finset Clause → Nat := fun u v F =>
      if h : ∃ d ∈ lefts, ∃ e ∈ rights, L d = u ∧ R e = v then
        let d := Classical.choose h
        let e := Classical.choose (Classical.choose_spec h).2
        if counting then mass d e F else min 1 (mass d e F)
      else 0
    refine ⟨L, R, decode, ?_⟩
    intro d hd e he F hFv
    have hex : ∃ d' ∈ lefts, ∃ e' ∈ rights, L d' = L d ∧ R e' = R e :=
      ⟨d, hd, e, he, rfl, rfl⟩
    simp only [decode, hex, dite_true]
    have hd' := (Classical.choose_spec hex).1
    have he'_spec := Classical.choose_spec (Classical.choose_spec hex).2
    have he' := he'_spec.1
    have hL' := he'_spec.2.1
    have hR' := he'_spec.2.2
    exact hmass_eq _ hd' d hd _ he' e he (hL_inj _ hd' d hd hL') (hR_inj _ he' e he hR') F hFv

end PEqualNP.Outside.L_lib_1137

theorem PEqualNP.Outside.L_lib_1137 : (∀ (m r : Nat) (rows : Fin r → Finset (Fin m)) (I : Finset (Fin r))
    (T : Finset (Fin m)) (t w : Nat), 0 < w →
  let xs := (Finset.univ : Finset (Finset (Fin m)))
  let ys := (Finset.univ : Finset (Finset (Fin r)))
  let parity := fun (U d : Finset (Fin r)) => (U ∩ d).card % 2
  let syn := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin r)).filter (fun i => ((rows i) ∩ x).card % 2 = 1)
  let word := fun (U : Finset (Fin r)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun j => (U.filter (fun i => j ∈ rows i)).card % 2 = 1)
  let lefts := xs.image (fun x => syn x ∩ I)
  let rights := xs.image (fun x => syn x \ I)
  let Clause := Finset (Fin m × Bool)
  let valid := fun (F : Finset Clause) => F.card ≤ t ∧
    ∀ C ∈ F, C.card ≤ w ∧ ∀ l ∈ C, l.1 ∈ T
  let mass := fun (d e : Finset (Fin r)) (F : Finset Clause) =>
    (xs.filter (fun x => syn x = d ∪ e ∧
      ∀ C ∈ F, ∃ l ∈ C, decide (l.1 ∈ x) = l.2)).card
  ∀ (counting : Bool) (a b : Nat),
    let k := if counting then t * w else t
    let probes := ys.filter (fun U => word U ⊆ T ∧ (word U).card ≤ k)
    let sig := fun (d : Finset (Fin r)) => probes.filter (fun U => parity U d = 1)
    (∃ (L : Finset (Fin r) → Fin a) (R : Finset (Fin r) → Fin b)
       (decode : Fin a → Fin b → Finset Clause → Nat),
      ∀ d ∈ lefts, ∀ e ∈ rights, ∀ F, valid F →
        decode (L d) (R e) F = if counting then mass d e F else min 1 (mass d e F)) ↔
      (lefts.image sig).card ≤ a ∧ (rights.image sig).card ≤ b) := by
  exact PEqualNP.Outside.L_lib_1137.main_proof
