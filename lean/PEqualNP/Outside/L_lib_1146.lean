import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1146

open symmDiff
open scoped Classical

private def chi {α : Type*} [DecidableEq α] (A B : Finset α) : ℤ :=
  ∏ a ∈ A, if a ∈ B then (-1 : ℤ) else 1

private lemma chi_eq_neg_one_pow {α : Type*} [DecidableEq α] (A B : Finset α) :
    chi A B = (-1 : ℤ) ^ (A ∩ B).card := by
  unfold chi
  rw [← Finset.prod_filter_mul_prod_filter_not A (fun a => a ∈ B)]
  have h1 : (∏ x ∈ A.filter (fun a => a ∈ B), if x ∈ B then (-1 : ℤ) else 1) =
      (-1 : ℤ) ^ (A ∩ B).card := by
    have hfilt : A.filter (fun a => a ∈ B) = A ∩ B := by ext x; simp
    rw [hfilt]
    calc (∏ x ∈ A ∩ B, if x ∈ B then (-1 : ℤ) else 1)
        = ∏ _x ∈ A ∩ B, (-1 : ℤ) := Finset.prod_congr rfl (fun x hx => by simp [(Finset.mem_inter.mp hx).2])
      _ = (-1 : ℤ) ^ (A ∩ B).card := by simp
  have h2 : (∏ x ∈ A.filter (fun a => ¬ a ∈ B), if x ∈ B then (-1 : ℤ) else 1) = 1 :=
    Finset.prod_eq_one (fun x hx => by simp [(Finset.mem_filter.mp hx).2])
  rw [h1, h2, mul_one]

private lemma chi_comm {α : Type*} [DecidableEq α] (A B : Finset α) : chi A B = chi B A := by
  rw [chi_eq_neg_one_pow, chi_eq_neg_one_pow, Finset.inter_comm]

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

private lemma chi_inter_right_of_subset {α : Type*} [DecidableEq α] {A B S : Finset α}
    (hAS : A ⊆ S) : chi A (B ∩ S) = chi A B := by
  unfold chi
  exact Finset.prod_congr rfl (fun a ha => by simp [hAS ha])

private lemma sum_chi_powerset {α : Type*} [DecidableEq α] (S A : Finset α) (hAS : A ⊆ S) :
    ∑ B ∈ S.powerset, chi A B = if A = ∅ then (2 : ℤ) ^ S.card else 0 := by
  by_cases hA : A = ∅
  · subst hA; simp [chi, Finset.card_powerset]
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
      intro B _; dsimp [f]; rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]
    have hneg : ∀ B ∈ S.powerset, chi A (f B) = -chi A B := by
      intro B _
      rw [chi_symmDiff_right]
      have : chi A {a} = -1 := by
        rw [chi_eq_neg_one_pow]
        have : A ∩ {a} = {a} := by ext x; simp [ha]
        rw [this]; simp
      rw [this]; ring
    have hsum : ∑ B ∈ S.powerset, chi A (f B) = ∑ B ∈ S.powerset, chi A B := by
      refine Finset.sum_bij (fun B _ => f B) hf_mem ?_ ?_ ?_
      · intro B₁ h₁ B₂ h₂ heq
        have := congrArg f heq
        rwa [hf_inv B₁ h₁, hf_inv B₂ h₂] at this
      · intro B hB; exact ⟨f B, hf_mem B hB, hf_inv B hB⟩
      · intro _ _; rfl
    have hsum2 : ∑ B ∈ S.powerset, chi A (f B) = -(∑ B ∈ S.powerset, chi A B) := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl hneg
    omega

private lemma sum_chi_univ {α : Type*} [DecidableEq α] [Fintype α] (A : Finset α) :
    ∑ B : Finset α, chi A B = if A = ∅ then (2 : ℤ) ^ Fintype.card α else 0 := by
  have h1 : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by ext s; simp
  rw [h1, sum_chi_powerset _ _ (Finset.subset_univ A), Finset.card_univ]

private lemma gcd_two_pow_sub_one (a b : Nat) :
    Nat.gcd (2 ^ a - 1) (2 ^ b - 1) = 2 ^ (Nat.gcd a b) - 1 := by
  induction a, b using Nat.gcd.induction with
  | H0 b => simp
  | H1 a b ha ih =>
    rw [Nat.gcd_comm (2 ^ a - 1), Nat.gcd_comm a b]
    have hmod : (2 ^ b - 1) % (2 ^ a - 1) = 2 ^ (b % a) - 1 := by
      have hdiv : b = a * (b / a) + b % a := (Nat.div_add_mod b a).symm
      have hdvd : (2 ^ a - 1) ∣ (2 ^ (a * (b / a)) - 1) := by
        have h1 : ∀ k : Nat, (2 ^ a - 1) ∣ (2 ^ (a * k) - 1) := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
            have hge1 : 1 ≤ 2 ^ (a * k) := Nat.one_le_two_pow
            have hge2 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
            have hge3 : 1 ≤ 2 ^ a * 2 ^ (a * k) := Nat.mul_pos (by omega) (by omega)
            have heq : 2 ^ (a * (k + 1)) - 1 = 2 ^ a * (2 ^ (a * k) - 1) + (2 ^ a - 1) := by
              rw [Nat.mul_succ, pow_add, mul_comm (2 ^ (a * k)) (2 ^ a)]
              zify [hge1, hge2, hge3]
              ring
            rw [heq]
            exact dvd_add (dvd_mul_of_dvd_right ihk _) (dvd_refl _)
        exact h1 (b / a)
      rcases hdvd with ⟨q, hq⟩
      have hlt : 2 ^ (b % a) - 1 < 2 ^ a - 1 := by
        have hba : b % a < a := Nat.mod_lt b ha
        have hp : 2 ^ (b % a) < 2 ^ a := Nat.pow_lt_pow_right (by omega) hba
        have h1 : 1 ≤ 2 ^ (b % a) := Nat.one_le_two_pow
        omega
      have heq : 2 ^ b - 1 = (2 ^ a - 1) * (q * 2 ^ (b % a)) + (2 ^ (b % a) - 1) := by
        have h1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
        have h2 : 1 ≤ 2 ^ (b % a) := Nat.one_le_two_pow
        have h3 : 1 ≤ 2 ^ (a * (b / a)) := Nat.one_le_two_pow
        have h4 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
        have hq' : (2 ^ (a * (b / a)) : ℤ) - 1 = ((2 ^ a : ℤ) - 1) * (q : ℤ) := by
          zify [h3, h4] at hq; exact hq
        zify [h1, h2, h4]
        calc (2 : ℤ) ^ b - 1 = (2 : ℤ) ^ (a * (b / a) + b % a) - 1 := by rw [← hdiv]
          _ = (2 : ℤ) ^ (a * (b / a)) * (2 : ℤ) ^ (b % a) - 1 := by rw [pow_add]
          _ = ((2 : ℤ) ^ (a * (b / a)) - 1) * (2 : ℤ) ^ (b % a) + ((2 : ℤ) ^ (b % a) - 1) := by ring
          _ = ((2 : ℤ) ^ a - 1) * (q * (2 : ℤ) ^ (b % a)) + ((2 : ℤ) ^ (b % a) - 1) := by rw [hq']; ring
      rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    calc (2 ^ b - 1).gcd (2 ^ a - 1)
        = ((2 ^ b - 1) % (2 ^ a - 1)).gcd (2 ^ a - 1) := by rw [Nat.gcd_comm (2 ^ b - 1), Nat.gcd_rec]
      _ = (2 ^ (b % a) - 1).gcd (2 ^ a - 1) := by rw [hmod]
      _ = 2 ^ (b % a).gcd a - 1 := ih
      _ = 2 ^ b.gcd a - 1 := by rw [Nat.gcd_comm b a, ← Nat.gcd_rec]

private lemma odd_two_pow_sub_one {a : Nat} (ha : 0 < a) : (2 ^ a - 1) % 2 = 1 := by
  have h2 : 2 ∣ 2 ^ a := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  rcases h2 with ⟨k, hk⟩
  omega

private lemma coprime_two_pow_odd {k m : Nat} (hm : m % 2 = 1) : Nat.Coprime (2 ^ k) m := by
  apply Nat.Coprime.pow_left
  exact Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hm)

private lemma finset_gcd_two_pow_sub_one {α : Type*} [DecidableEq α] (J : Finset α) (f : α → Nat) :
    J.gcd (fun i => 2 ^ f i - 1) = 2 ^ (J.gcd f) - 1 := by
  induction J using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.gcd_insert, Finset.gcd_insert, ih]
    exact gcd_two_pow_sub_one (f a) (s.gcd f)

private lemma prod_filter_choices {n t : Nat} (scope : Fin t → Finset (Fin n))
    (g : ∀ i : Fin t, Finset (Fin n) → ℤ) :
    let choices := (Finset.univ : Finset (Fin t → Finset (Fin n))).filter (fun R => ∀ i, R i ⊆ scope i)
    ∑ p ∈ choices, ∏ i : Fin t, g i (p i) =
      ∏ i : Fin t, ∑ q ∈ (scope i).powerset, g i q := by
  intro choices
  have hch : choices = Fintype.piFinset (fun i => (scope i).powerset) := by
    ext p; simp [choices, Fintype.mem_piFinset]
  rw [hch]
  symm
  exact Finset.prod_univ_sum (fun i => (scope i).powerset) g

private lemma local_point_indicator {n t : Nat} (scope : Fin t → Finset (Fin n))
    (hcov : ∀ j : Fin n, ∃ i, j ∈ scope i) (z x : Finset (Fin n)) :
    let choices := (Finset.univ : Finset (Fin t → Finset (Fin n))).filter (fun R => ∀ i, R i ⊆ scope i)
    let passes := fun (x : Finset (Fin n)) (p : Fin t → Finset (Fin n)) =>
      (Finset.univ : Finset (Fin t)).toList.all (fun i => decide (x ∩ scope i ≠ p i))
    let c : (Fin t → Finset (Fin n)) → ℤ := fun p =>
      ∏ i : Fin t, if p i = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1
    ∑ p ∈ choices.filter (fun p => passes x p = true), c p =
      if x = z then ∏ i : Fin t, ((2 : ℤ) ^ (scope i).card - 1) else 0 := by
  intro choices passes c
  have hpass : ∀ p, passes x p = true ↔ ∀ i : Fin t, x ∩ scope i ≠ p i := by
    intro p; simp [passes]
  have hsum : ∑ p ∈ choices.filter (fun p => passes x p = true), c p =
      ∑ p ∈ choices, ∏ i : Fin t,
        (if x ∩ scope i ≠ p i then (if p i = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : passes x p = true
    · rw [if_pos hp]
      have hall := (hpass p).mp hp
      exact Finset.prod_congr rfl (fun i _ => by simp [hall i])
    · rw [if_neg hp]
      have hex : ∃ i : Fin t, ¬ x ∩ scope i ≠ p i := by
        by_contra h
        exact hp ((hpass p).mpr (fun i hi => h ⟨i, fun h' => h' hi⟩))
      rcases hex with ⟨i, hi⟩
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [hsum]
  dsimp only [choices]
  rw [prod_filter_choices scope (fun i q =>
    if x ∩ scope i ≠ q then (if q = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) else 0)]
  have hloc : ∀ i : Fin t,
      ∑ q ∈ (scope i).powerset,
        (if x ∩ scope i ≠ q then (if q = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) else 0) =
      if x ∩ scope i = z ∩ scope i then ((2 : ℤ) ^ (scope i).card - 1) else 0 := by
    intro i
    have hx_mem : x ∩ scope i ∈ (scope i).powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
    have hz_mem : z ∩ scope i ∈ (scope i).powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
    by_cases hxz : x ∩ scope i = z ∩ scope i
    · rw [if_pos hxz]
      calc ∑ q ∈ (scope i).powerset,
            (if x ∩ scope i ≠ q then (if q = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) else 0)
          = ∑ q ∈ (scope i).powerset.erase (x ∩ scope i), (1 : ℤ) := by
              rw [← Finset.add_sum_erase _ _ hx_mem]
              simp only [ne_eq, not_true_eq_false, ite_false, zero_add]
              apply Finset.sum_congr rfl
              intro q hq
              have hne : x ∩ scope i ≠ q := (Finset.mem_erase.mp hq).1.symm
              have hnez : q ≠ z ∩ scope i := by rw [← hxz]; exact hne.symm
              simp [hne, hnez]
        _ = (((scope i).powerset.erase (x ∩ scope i)).card : ℤ) := by simp
        _ = (2 : ℤ) ^ (scope i).card - 1 := by
              rw [Finset.card_erase_of_mem hx_mem, Finset.card_powerset]
              have h1 : 1 ≤ 2 ^ (scope i).card := Nat.one_le_two_pow
              zify [h1]
    · rw [if_neg hxz]
      rw [← Finset.add_sum_erase _ _ hx_mem]
      simp only [ne_eq, not_true_eq_false, ite_false, zero_add]
      have hz_mem' : z ∩ scope i ∈ (scope i).powerset.erase (x ∩ scope i) :=
        Finset.mem_erase.mpr ⟨Ne.symm hxz, hz_mem⟩
      rw [← Finset.add_sum_erase _ _ hz_mem']
      have hterm1 : (if x ∩ scope i ≠ z ∩ scope i then
          (if z ∩ scope i = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) else 0) =
          -((2 : ℤ) ^ (scope i).card - 2) := by simp [hxz]
      rw [hterm1]
      have hrest : ∑ q ∈ ((scope i).powerset.erase (x ∩ scope i)).erase (z ∩ scope i),
          (if x ∩ scope i ≠ q then (if q = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) else 0) =
          (((scope i).powerset.erase (x ∩ scope i)).erase (z ∩ scope i)).card := by
        calc _ = ∑ _q ∈ ((scope i).powerset.erase (x ∩ scope i)).erase (z ∩ scope i), (1 : ℤ) := by
                apply Finset.sum_congr rfl
                intro q hq
                have hq1 : q ≠ z ∩ scope i := (Finset.mem_erase.mp hq).1
                have hq2 : q ≠ x ∩ scope i := (Finset.mem_erase.mp (Finset.mem_erase.mp hq).2).1
                simp [hq1, hq2.symm]
          _ = _ := by simp
      rw [hrest, Finset.card_erase_of_mem hz_mem', Finset.card_erase_of_mem hx_mem, Finset.card_powerset]
      have hcard2 : 2 ≤ 2 ^ (scope i).card := by
        have hpos : 0 < (scope i).card := by

          by_contra h0
          have hemp : scope i = ∅ := Finset.card_eq_zero.mp (by omega)
          exact hxz (by simp [hemp])
        exact Nat.le_self_pow (by omega) 2
      have hcard1 : 1 ≤ 2 ^ (scope i).card - 1 := by omega
      have hcard0 : 1 ≤ 2 ^ (scope i).card := by omega
      zify [hcard2, hcard1, hcard0]
      ring
  simp_rw [hloc]
  by_cases hxz : x = z
  · subst hxz
    simp only [ite_true]
  · rw [if_neg hxz]
    have hex : ∃ i : Fin t, x ∩ scope i ≠ z ∩ scope i := by
      have hexj : ∃ j : Fin n, ¬ (j ∈ x ↔ j ∈ z) := by
        by_contra hall
        apply hxz; ext j
        by_contra h; exact hall ⟨j, h⟩
      rcases hexj with ⟨j, hj⟩
      rcases hcov j with ⟨i, hij⟩
      refine ⟨i, fun hEq => hj ?_⟩
      have := Finset.ext_iff.mp hEq j
      simpa [Finset.mem_inter, hij] using this
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private def xorAll {n t : Nat} (M : Fin t → Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun j => ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 = 1)

private lemma chi_xorAll {n t : Nat} (M : Fin t → Finset (Fin n)) (x : Finset (Fin n)) :
    ∏ i : Fin t, chi (M i) x = chi (xorAll M) x := by
  have hL : ∏ i : Fin t, chi (M i) x = ∏ i : Fin t, ∏ j ∈ x, if j ∈ M i then (-1 : ℤ) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    rw [chi_comm]; rfl
  have hR : chi (xorAll M) x = ∏ j ∈ x, ∏ i : Fin t, if j ∈ M i then (-1 : ℤ) else 1 := by
    rw [chi_comm]
    unfold chi
    apply Finset.prod_congr rfl
    intro j _
    have hmem : j ∈ xorAll M ↔ ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 = 1 := by
      simp [xorAll]
    have hprod : (∏ i : Fin t, if j ∈ M i then (-1 : ℤ) else 1) =
        (-1 : ℤ) ^ ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => j ∈ M i)]
      have ha : (∏ i ∈ Finset.univ.filter (fun i => j ∈ M i), if j ∈ M i then (-1 : ℤ) else 1) =
          (-1 : ℤ) ^ ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card := by
        calc _ = ∏ _i ∈ Finset.univ.filter (fun i => j ∈ M i), (-1 : ℤ) :=
                Finset.prod_congr rfl (fun i hi => by simp [(Finset.mem_filter.mp hi).2])
          _ = _ := by simp
      have hb : (∏ i ∈ Finset.univ.filter (fun i => ¬ j ∈ M i), if j ∈ M i then (-1 : ℤ) else 1) = 1 :=
        Finset.prod_eq_one (fun i hi => by simp [(Finset.mem_filter.mp hi).2])
      rw [ha, hb, mul_one]
    rw [hprod]
    rcases Nat.even_or_odd ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hmod : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 ≠ 1 := by omega
      rw [if_neg (fun hm => hmod (hmem.mp hm)), hk]
      simp [← two_mul, pow_mul]
    · have hmod : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 = 1 := by omega
      rw [if_pos (hmem.mpr hmod), hk]
      simp [pow_add, pow_mul]
  rw [hL, hR, Finset.prod_comm]

private lemma walsh_signing {n t : Nat} (scope : Fin t → Finset (Fin n))
    (M : Fin t → Finset (Fin n)) (hM : ∀ i, M i ⊆ scope i) (x : Finset (Fin n)) :
    let choices := (Finset.univ : Finset (Fin t → Finset (Fin n))).filter (fun R => ∀ i, R i ⊆ scope i)
    let passes := fun (x : Finset (Fin n)) (p : Fin t → Finset (Fin n)) =>
      (Finset.univ : Finset (Fin t)).toList.all (fun i => decide (x ∩ scope i ≠ p i))
    ∑ p ∈ choices.filter (fun p => passes x p = true), (∏ i : Fin t, chi (M i) (p i)) =
      (∏ i : Fin t, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1) * chi (xorAll M) x := by
  intro choices passes
  have hpass : ∀ p, passes x p = true ↔ ∀ i : Fin t, x ∩ scope i ≠ p i := by
    intro p; simp [passes]
  have hsum : ∑ p ∈ choices.filter (fun p => passes x p = true), (∏ i : Fin t, chi (M i) (p i)) =
      ∑ p ∈ choices, ∏ i : Fin t, (if x ∩ scope i ≠ p i then chi (M i) (p i) else 0) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : passes x p = true
    · rw [if_pos hp]
      have hall := (hpass p).mp hp
      exact Finset.prod_congr rfl (fun i _ => by simp [hall i])
    · rw [if_neg hp]
      have hex : ∃ i : Fin t, ¬ x ∩ scope i ≠ p i := by
        by_contra h
        exact hp ((hpass p).mpr (fun i hi => h ⟨i, fun h' => h' hi⟩))
      rcases hex with ⟨i, hi⟩
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  rw [hsum]
  dsimp only [choices]
  rw [prod_filter_choices scope (fun i q => if x ∩ scope i ≠ q then chi (M i) q else 0)]
  have hloc : ∀ i : Fin t,
      ∑ q ∈ (scope i).powerset, (if x ∩ scope i ≠ q then chi (M i) q else 0) =
      (if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1) * chi (M i) x := by
    intro i
    have hx_mem : x ∩ scope i ∈ (scope i).powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
    have hfull := sum_chi_powerset (scope i) (M i) (hM i)
    have hsub : ∑ q ∈ (scope i).powerset, (if x ∩ scope i ≠ q then chi (M i) q else 0) =
        (∑ q ∈ (scope i).powerset, chi (M i) q) - chi (M i) (x ∩ scope i) := by
      rw [← Finset.add_sum_erase _ _ hx_mem, ← Finset.add_sum_erase _ _ hx_mem]
      simp only [ne_eq, not_true_eq_false, ite_false, zero_add]
      have hrest : ∑ q ∈ (scope i).powerset.erase (x ∩ scope i),
          (if x ∩ scope i ≠ q then chi (M i) q else 0) =
          ∑ q ∈ (scope i).powerset.erase (x ∩ scope i), chi (M i) q := by
        apply Finset.sum_congr rfl
        intro q hq; simp [(Finset.mem_erase.mp hq).1.symm]
      rw [hrest]; ring
    rw [hsub, hfull, chi_inter_right_of_subset (hM i)]
    by_cases hMi : M i = ∅
    · rw [hMi]; simp [chi]
    · simp [hMi]
  simp_rw [hloc]
  rw [Finset.prod_mul_distrib, chi_xorAll]

private def rowAdj {n t : Nat} (scope : Fin t → Finset (Fin n)) (i h : Fin t) : Prop :=
  (scope i ∩ scope h).Nonempty

private def rowReach {n t : Nat} (scope : Fin t → Finset (Fin n)) : Nat → Fin t → Fin t → Prop
  | 0, i, h => i = h
  | k + 1, i, h => rowReach scope k i h ∨ ∃ u, rowReach scope k i u ∧ rowAdj scope u h

private lemma rowReach_refl {n t : Nat} (scope : Fin t → Finset (Fin n)) (k : Nat) (i : Fin t) :
    rowReach scope k i i := by
  induction k with
  | zero => rfl
  | succ k ih => exact Or.inl ih

private lemma rowReach_mono {n t : Nat} (scope : Fin t → Finset (Fin n)) {k₁ k₂ : Nat}
    (hk : k₁ ≤ k₂) {i h : Fin t} (hr : rowReach scope k₁ i h) : rowReach scope k₂ i h := by
  induction hk with
  | refl => exact hr
  | step _ ih => exact Or.inl ih

private lemma rowReach_trans {n t : Nat} (scope : Fin t → Finset (Fin n)) {k₁ k₂ : Nat} {i u h : Fin t}
    (h1 : rowReach scope k₁ i u) (h2 : rowReach scope k₂ u h) : rowReach scope (k₁ + k₂) i h := by
  induction k₂ generalizing h with
  | zero => subst h2; simpa using h1
  | succ k₂ ih =>
    rcases h2 with h2 | ⟨v, hv, hadj⟩
    · exact Or.inl (ih h2)
    · exact Or.inr ⟨v, ih hv, hadj⟩

private lemma rowReach_symm {n t : Nat} (scope : Fin t → Finset (Fin n)) {k : Nat} {i h : Fin t}
    (hr : rowReach scope k i h) : rowReach scope k h i := by
  induction k generalizing i h with
  | zero => exact hr.symm
  | succ k ih =>
    rcases hr with hr | ⟨u, hu, hadj⟩
    · exact Or.inl (ih hr)
    · have h1 : rowReach scope 1 h u :=
        Or.inr ⟨h, rfl, by simpa [rowAdj, Finset.inter_comm] using hadj⟩
      have h2 : rowReach scope k u i := ih hu
      have h3 := rowReach_trans scope h1 h2
      simpa [Nat.add_comm] using h3

private lemma rowReach_bound {n t : Nat} (scope : Fin t → Finset (Fin n)) {k : Nat} {i h : Fin t}
    (hr : rowReach scope k i h) : rowReach scope t i h := by

  suffices ∀ m, (∃ k ≤ m, rowReach scope k i h) → rowReach scope t i h from
    this k ⟨k, le_refl k, hr⟩
  intro m hm
  classical
  let k0 := Nat.find (show ∃ k, rowReach scope k i h from ⟨hm.choose, hm.choose_spec.2⟩)
  have hk0 : rowReach scope k0 i h := Nat.find_spec (show ∃ k, rowReach scope k i h from ⟨hm.choose, hm.choose_spec.2⟩)
  have hmin : ∀ k' < k0, ¬ rowReach scope k' i h := fun k' hk' =>
    Nat.find_min (show ∃ k, rowReach scope k i h from ⟨hm.choose, hm.choose_spec.2⟩) hk'
  suffices hle : k0 ≤ t from rowReach_mono scope hle hk0
  by_contra hgt
  push Not at hgt

  have hpath : ∀ r ≤ k0, ∃ u : Fin t, rowReach scope r i u ∧ rowReach scope (k0 - r) u h := by
    intro r hr_le
    induction r with
    | zero => exact ⟨i, rfl, by simpa using hk0⟩
    | succ r ihr =>
      rcases ihr (by omega) with ⟨u, hu1, hu2⟩
      have hpos : 0 < k0 - r := by omega
      have hsplit : k0 - r = (k0 - (r + 1)) + 1 := by omega
      rw [hsplit] at hu2

      have hu2' := rowReach_symm scope hu2
      rcases hu2' with hu2' | ⟨v, hv, hadj⟩
      · exfalso
        have := rowReach_trans scope hu1 (rowReach_symm scope hu2')
        exact hmin (r + (k0 - (r + 1))) (by omega) this
      · refine ⟨v, Or.inr ⟨u, hu1, by simpa [rowAdj, Finset.inter_comm] using hadj⟩,
          rowReach_symm scope hv⟩
  let f : Fin (k0 + 1) → Fin t := fun r => Classical.choose (hpath r.val (by omega))
  have hf_spec : ∀ r : Fin (k0 + 1), rowReach scope r.val i (f r) ∧ rowReach scope (k0 - r.val) (f r) h :=
    fun r => Classical.choose_spec (hpath r.val (by omega))
  have hcard : Fintype.card (Fin t) < Fintype.card (Fin (k0 + 1)) := by simp; omega
  rcases Fintype.exists_ne_map_eq_of_card_lt f hcard with ⟨r₁, r₂, hne, hfeq⟩
  have hlt : r₁.val < r₂.val ∨ r₂.val < r₁.val := by
    have : r₁.val ≠ r₂.val := fun h => hne (Fin.ext h)
    omega
  rcases hlt with hlt | hlt
  · have h1 := (hf_spec r₁).1
    have h2 := (hf_spec r₂).2
    rw [← hfeq] at h2
    exact hmin (r₁.val + (k0 - r₂.val)) (by omega) (rowReach_trans scope h1 h2)
  · have h1 := (hf_spec r₂).1
    have h2 := (hf_spec r₁).2
    rw [hfeq] at h2
    exact hmin (r₂.val + (k0 - r₁.val)) (by omega) (rowReach_trans scope h1 h2)

private lemma closed_iff {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t)) :
    (J.toList.all (fun i => (Finset.univ : Finset (Fin t)).toList.all
      (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))) = true ↔
      ∀ i ∈ J, ∀ h : Fin t, rowAdj scope i h → h ∈ J := by
  simp only [List.all_eq_true, Finset.mem_toList, Finset.mem_univ, true_implies,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, rowAdj]
  constructor
  · intro H i hi h hadj
    rcases H i hi h with hno | hmem
    · exact absurd hadj hno
    · exact hmem
  · intro H i hi h
    by_cases hadj : (scope i ∩ scope h).Nonempty
    · exact Or.inr (H i hi h hadj)
    · exact Or.inl hadj

private lemma mem_components_iff {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t)) :
    let rows := (Finset.univ : Finset (Fin t))
    let closed := fun (J : Finset (Fin t)) => J.toList.all (fun i => rows.toList.all
      (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))
    let components := rows.powerset.filter (fun J => J.Nonempty ∧ closed J = true ∧
      ∀ K ∈ J.powerset, K.Nonempty → closed K = true → K = J)
    J ∈ components ↔
      ∃ i : Fin t, J = (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i h) := by
  classical
  intro rows closed components
  let comp : Fin t → Finset (Fin t) := fun i =>
    (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i h)
  have hcomp_closed : ∀ i : Fin t, closed (comp i) = true := by
    intro i
    rw [closed_iff]
    intro u hu h hadj
    have hu' : rowReach scope t i u := (Finset.mem_filter.mp hu).2
    have hreach : rowReach scope (t + 1) i h := Or.inr ⟨u, hu', hadj⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_bound scope hreach⟩
  have hcomp_eq : ∀ i u : Fin t, u ∈ comp i → comp u = comp i := by
    intro i u hu
    have hiu : rowReach scope t i u := (Finset.mem_filter.mp hu).2
    ext h
    simp only [comp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro huh; exact rowReach_bound scope (rowReach_trans scope hiu huh)
    · intro hih; exact rowReach_bound scope (rowReach_trans scope (rowReach_symm scope hiu) hih)
  have hclosed_reach : ∀ {K : Finset (Fin t)}, closed K = true →
      ∀ {u h : Fin t}, u ∈ K → ∀ k, rowReach scope k u h → h ∈ K := by
    intro K hK u h hu k hr
    have hK' := (closed_iff scope K).mp hK
    induction k generalizing h with
    | zero => subst hr; exact hu
    | succ k ih =>
      rcases hr with hr | ⟨v, hv, hadj⟩
      · exact ih hr
      · exact hK' v (ih hv) h hadj
  constructor
  · intro hJ
    simp only [components, Finset.mem_filter, Finset.mem_powerset] at hJ
    rcases hJ with ⟨_, ⟨i, hi⟩, hJcl, hJmin⟩
    refine ⟨i, (hJmin (comp i) ?_ ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_refl scope t i⟩⟩ (hcomp_closed i)).symm⟩
    intro h hh
    exact hclosed_reach hJcl hi t (Finset.mem_filter.mp hh).2
  · rintro ⟨i, rfl⟩
    simp only [components, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_refl scope t i⟩⟩,
      hcomp_closed i, ?_⟩
    intro K hKsub ⟨u, hu⟩ hKcl
    have hucomp : u ∈ comp i := hKsub hu
    apply Finset.Subset.antisymm hKsub
    intro h hh
    have hh' : h ∈ comp u := by rwa [hcomp_eq i u hucomp]
    exact hclosed_reach hKcl hu t (Finset.mem_filter.mp hh').2

private def bipAdj {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t))
    (skip : Option (Fin t × Fin n)) : Sum (Fin t) (Fin n) → Sum (Fin t) (Fin n) → Prop
  | Sum.inl i, Sum.inr j => i ∈ J ∧ j ∈ scope i ∧ skip ≠ some (i, j)
  | Sum.inr j, Sum.inl i => i ∈ J ∧ j ∈ scope i ∧ skip ≠ some (i, j)
  | _, _ => False

private def bipReach {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t))
    (skip : Option (Fin t × Fin n)) : Nat → Sum (Fin t) (Fin n) → Sum (Fin t) (Fin n) → Prop
  | 0, u, v => u = v
  | k + 1, u, v => bipReach scope J skip k u v ∨ ∃ w, bipReach scope J skip k u w ∧ bipAdj scope J skip w v

private lemma bipReach_trans {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t))
    (skip : Option (Fin t × Fin n)) {k₁ k₂ : Nat} {u w v : Sum (Fin t) (Fin n)}
    (h1 : bipReach scope J skip k₁ u w) (h2 : bipReach scope J skip k₂ w v) :
    bipReach scope J skip (k₁ + k₂) u v := by
  induction k₂ generalizing v with
  | zero => subst h2; simpa using h1
  | succ k₂ ih =>
    rcases h2 with h2 | ⟨z, hz, hadj⟩
    · exact Or.inl (ih h2)
    · exact Or.inr ⟨z, ih hz, hadj⟩

private lemma bipAdj_symm {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t))
    (skip : Option (Fin t × Fin n)) {u v : Sum (Fin t) (Fin n)}
    (h : bipAdj scope J skip u v) : bipAdj scope J skip v u := by
  cases u <;> cases v <;> simpa [bipAdj] using h

private lemma bipReach_symm {n t : Nat} (scope : Fin t → Finset (Fin n)) (J : Finset (Fin t))
    (skip : Option (Fin t × Fin n)) {k : Nat} {u v : Sum (Fin t) (Fin n)}
    (h : bipReach scope J skip k u v) : bipReach scope J skip k v u := by
  induction k generalizing u v with
  | zero => exact h.symm
  | succ k ih =>
    rcases h with h | ⟨w, hw, hadj⟩
    · exact Or.inl (ih h)
    · have h1 : bipReach scope J skip 1 v w := Or.inr ⟨v, rfl, bipAdj_symm scope J skip hadj⟩
      simpa [Nat.add_comm] using bipReach_trans scope J skip h1 (ih hw)

private lemma bipReach_none_of_comp {n t : Nat} (scope : Fin t → Finset (Fin n))
    {i₀ : Fin t} :
    let J := (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i₀ h)
    ∀ v : Sum (Fin t) (Fin n),
      (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
      ∃ k, bipReach scope J none k (Sum.inl i₀) v := by
  intro J
  have hrow : ∀ k (h : Fin t), rowReach scope k i₀ h →
      ∃ m, bipReach scope J none m (Sum.inl i₀) (Sum.inl h) := by
    intro k
    induction k with
    | zero => intro h hh; subst hh; exact ⟨0, rfl⟩
    | succ k ih =>
      intro h hh
      rcases hh with hh | ⟨u, hu, j, hj⟩
      · exact ih h hh
      · rcases ih u hu with ⟨m, hm⟩
        have huJ : u ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_bound scope hu⟩
        have hhJ : h ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          rowReach_bound scope (show rowReach scope (k + 1) i₀ h from Or.inr ⟨u, hu, ⟨j, hj⟩⟩)⟩
        have hju : j ∈ scope u := (Finset.mem_inter.mp hj).1
        have hjh : j ∈ scope h := (Finset.mem_inter.mp hj).2
        refine ⟨m + 2, ?_⟩
        exact Or.inr ⟨Sum.inr j, Or.inr ⟨Sum.inl u, hm, ⟨huJ, hju, by simp⟩⟩, ⟨hhJ, hjh, by simp⟩⟩
  intro v hv
  cases v with
  | inl i => exact hrow t i (Finset.mem_filter.mp hv).2
  | inr j =>
    rcases Finset.mem_biUnion.mp hv with ⟨i, hiJ, hji⟩
    rcases hrow t i (Finset.mem_filter.mp hiJ).2 with ⟨m, hm⟩
    exact ⟨m + 1, Or.inr ⟨Sum.inl i, hm, ⟨hiJ, hji, by simp⟩⟩⟩

private lemma bfs_parent_edges {n t : Nat} (scope : Fin t → Finset (Fin n))
    (J : Finset (Fin t)) (skip : Option (Fin t × Fin n)) (root : Sum (Fin t) (Fin n))
    (hconn : ∀ v : Sum (Fin t) (Fin n),
      (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
      ∃ k, bipReach scope J skip k root v) :
    ∃ d : Sum (Fin t) (Fin n) → Nat,
      d root = 0 ∧
      (∀ v, (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
        v ≠ root → ∃ u, bipAdj scope J skip u v ∧ d u < d v) ∧
      (∀ u v, bipAdj scope J skip u v →
        (match u with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
        d v ≤ d u + 1) := by
  classical
  let inV : Sum (Fin t) (Fin n) → Prop := fun v =>
    match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope
  let d : Sum (Fin t) (Fin n) → Nat := fun v =>
    if h : inV v then Nat.find (hconn v h) else 0
  have hd_spec : ∀ v (hv : inV v), bipReach scope J skip (d v) root v := by
    intro v hv; simp only [d, hv, dite_true]; exact Nat.find_spec (hconn v hv)
  have hd_min : ∀ v (hv : inV v) k, bipReach scope J skip k root v → d v ≤ k := by
    intro v hv k hk; simp only [d, hv, dite_true]; exact Nat.find_min' (hconn v hv) hk
  refine ⟨d, ?_, ?_, ?_⟩
  · by_cases hr : inV root
    · have h0 := hd_min root hr 0 rfl; omega
    · simp [d, hr]
  · intro v hv hne
    have hreach := hd_spec v hv
    cases hk : d v with
    | zero =>
      rw [hk] at hreach
      exact absurd hreach.symm hne
    | succ k =>
      rw [hk] at hreach
      rcases hreach with hprev | ⟨u, hu, hadj⟩
      · have := hd_min v hv k hprev; omega
      · have huV : inV u := by
          cases u <;> cases v <;> simp only [bipAdj] at hadj
          · exact hadj.1
          · exact Finset.mem_biUnion.mpr ⟨_, hadj.1, hadj.2.1⟩
        have hdu : d u ≤ k := hd_min u huV k hu
        exact ⟨u, hadj, by omega⟩
  · intro u v hadj huV
    have hvV : inV v := by
      cases u <;> cases v <;> simp only [bipAdj] at hadj
      · exact Finset.mem_biUnion.mpr ⟨_, hadj.1, hadj.2.1⟩
      · exact hadj.1
    exact hd_min v hvV (d u + 1) (Or.inr ⟨u, hd_spec u huV, hadj⟩)

private lemma tree_all_demanding_forces_empty {n t : Nat} (scope : Fin t → Finset (Fin n))
    (J : Finset (Fin t))
    (hJclosed : ∀ i ∈ J, ∀ h : Fin t, rowAdj scope i h → h ∈ J)
    (htree : J.sum (fun i => (scope i).card) + 1 = J.card + (J.biUnion scope).card)
    (T : Finset (Fin n))
    (hT : T ∩ J.biUnion scope =
      ((Finset.univ : Finset (Fin n)).filter (fun j => ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 = 0)) ∩
        J.biUnion scope)
    (M : Fin t → Finset (Fin n)) (hMsub : ∀ i, M i ⊆ scope i) (hMxor : xorAll M = T) :
    ∃ i ∈ J, M i = ∅ := by
  by_contra hall
  push Not at hall
  have hkept : J.card ≤ ∑ i ∈ J, (M i).card := by
    calc J.card = ∑ _i ∈ J, 1 := by simp
      _ ≤ ∑ i ∈ J, (M i).card := Finset.sum_le_sum (fun i hi =>
          Nat.succ_le_of_lt (Finset.card_pos.mpr (hall i hi)))
  have hdel_site : ∀ j ∈ J.biUnion scope, ∃ i ∈ J, j ∈ scope i \ M i := by
    intro j hj
    have hscope_in_J : ∀ i : Fin t, j ∈ scope i → i ∈ J := by
      intro i hji
      rcases Finset.mem_biUnion.mp hj with ⟨i0, hi0J, hji0⟩
      exact hJclosed i0 hi0J i ⟨j, Finset.mem_inter.mpr ⟨hji0, hji⟩⟩
    have hM_eq_sc : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 ≠
        ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 := by
      have h1 := Finset.ext_iff.mp hT j
      simp only [Finset.mem_inter, hj, and_true, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      have h2 : j ∈ T ↔ ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 = 1 := by
        rw [← hMxor]; simp [xorAll]
      have hiff : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 = 1 ↔
          ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 = 0 := h2.symm.trans h1
      have ha : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i)).card % 2 < 2 := Nat.mod_lt _ (by omega)
      have hb : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 < 2 := Nat.mod_lt _ (by omega)
      omega
    have hne : (Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i) ≠
        (Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i) := fun hEq => hM_eq_sc (by rw [hEq])
    have hsub : (Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i) ⊆
        (Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i) := by
      intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hMsub i hi
    have hssub : (Finset.univ : Finset (Fin t)).filter (fun i => j ∈ M i) ⊂
        (Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
    rcases Finset.exists_of_ssubset hssub with ⟨i, hi_sc, hi_notM⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_sc hi_notM
    exact ⟨i, hscope_in_J i hi_sc, Finset.mem_sdiff.mpr ⟨hi_sc, hi_notM⟩⟩
  have hdel : (J.biUnion scope).card ≤ ∑ i ∈ J, (scope i \ M i).card := by
    have hswap : ∑ i ∈ J, (scope i \ M i).card =
        ∑ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i \ M i)).card := by
      have h1 : ∀ i ∈ J, (scope i \ M i).card =
          ∑ j ∈ J.biUnion scope, if j ∈ scope i \ M i then 1 else 0 := by
        intro i hi
        rw [Finset.sum_boole, Nat.cast_id]
        congr 1; ext j
        simp only [Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, h1⟩, h1, h2⟩
        · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_boole, Nat.cast_id]
    rw [hswap]
    calc (J.biUnion scope).card = ∑ _j ∈ J.biUnion scope, 1 := by simp
      _ ≤ ∑ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i \ M i)).card :=
        Finset.sum_le_sum (fun j hj => by
          rcases hdel_site j hj with ⟨i, hi, hji⟩
          exact Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hji⟩⟩))
  have htot : ∑ i ∈ J, (scope i).card = ∑ i ∈ J, (M i).card + ∑ i ∈ J, (scope i \ M i).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hMsub i)]
    have := Finset.card_le_card (hMsub i)
    omega
  omega

private lemma tree_empty_single {n t : Nat} (scope : Fin t → Finset (Fin n))
    (i₀ : Fin t) :
    let J := (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i₀ h)
    J.sum (fun i => (scope i).card) + 1 = J.card + (J.biUnion scope).card →
    ∃ M : Fin t → Finset (Fin n),
      (∀ i ∈ J, M i ⊆ scope i) ∧
      M i₀ = ∅ ∧
      (∀ i ∈ J, i ≠ i₀ → (M i).Nonempty) ∧
      (∀ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i \ M i)).card = 1) := by
  intro J htree
  have hi₀J : i₀ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_refl scope t i₀⟩
  rcases bfs_parent_edges scope J none (Sum.inl i₀) (bipReach_none_of_comp scope) with ⟨d, hd0, hpar, _⟩
  let M : Fin t → Finset (Fin n) := fun i =>
    (scope i).filter (fun j => d (Sum.inr j) < d (Sum.inl i))

  have hrow_ge : ∀ i ∈ J.erase i₀, 1 ≤ (M i).card := by
    intro i hi
    have ⟨hne, hiJ⟩ := Finset.mem_erase.mp hi
    rcases hpar (Sum.inl i) hiJ (fun h => hne (Sum.inl.inj h)) with ⟨u, hadj, hdu⟩
    cases u with
    | inl _ => exact absurd hadj id
    | inr j =>
      exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hadj.2.1, hdu⟩⟩
  have hsite_ge : ∀ j ∈ J.biUnion scope,
      1 ≤ (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card := by
    intro j hj
    rcases hpar (Sum.inr j) hj (by simp) with ⟨u, hadj, hdu⟩
    cases u with
    | inr _ => exact absurd hadj id
    | inl i =>
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hadj.1, hadj.2.1, hdu⟩⟩

  have hsum_le : (∑ i ∈ J.erase i₀, (M i).card) +
      (∑ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card) ≤
      ∑ i ∈ J, (scope i).card := by
    have hswap : ∑ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card =
        ∑ i ∈ J, ((scope i).filter (fun j => d (Sum.inl i) < d (Sum.inr j))).card := by
      have h1 : ∀ j ∈ J.biUnion scope,
          (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card =
          ∑ i ∈ J, if j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j) then 1 else 0 := by
        intro j _; rw [Finset.sum_boole, Nat.cast_id]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_boole, Nat.cast_id]
      congr 1; ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, h1⟩, h1, h2⟩
    have hMi0 : (M i₀).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _; rw [hd0]; omega
    have hMsum : ∑ i ∈ J.erase i₀, (M i).card = ∑ i ∈ J, (M i).card := by
      rw [← Finset.add_sum_erase _ _ hi₀J, hMi0, zero_add]
    rw [hswap, hMsum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hdisj : Disjoint (M i) ((scope i).filter (fun j => d (Sum.inl i) < d (Sum.inr j))) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      have h1 := (Finset.mem_filter.mp hj1).2
      have h2 := (Finset.mem_filter.mp hj2).2
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))

  have hlow1 : J.card - 1 ≤ ∑ i ∈ J.erase i₀, (M i).card := by
    calc J.card - 1 = (J.erase i₀).card := (Finset.card_erase_of_mem hi₀J).symm
      _ = ∑ _i ∈ J.erase i₀, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hrow_ge
  have hlow2 : (J.biUnion scope).card ≤
      ∑ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card := by
    calc (J.biUnion scope).card = ∑ _j ∈ J.biUnion scope, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum hsite_ge
  have hJpos : 1 ≤ J.card := Finset.card_pos.mpr ⟨i₀, hi₀J⟩
  have hsum_eq : ∑ j ∈ J.biUnion scope,
      (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card =
      (J.biUnion scope).card := by omega
  have hsum_lt_eq : ∑ i ∈ J, ((M i).card + ((scope i).filter (fun j => d (Sum.inl i) < d (Sum.inr j))).card) =
      ∑ i ∈ J, (scope i).card := by
    have hMi0 : (M i₀).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro j _; rw [hd0]; omega
    have hMsum : ∑ i ∈ J.erase i₀, (M i).card = ∑ i ∈ J, (M i).card := by
      rw [← Finset.add_sum_erase _ _ hi₀J, hMi0, zero_add]
    have hswap : ∑ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card =
        ∑ i ∈ J, ((scope i).filter (fun j => d (Sum.inl i) < d (Sum.inr j))).card := by
      have h1 : ∀ j ∈ J.biUnion scope,
          (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card =
          ∑ i ∈ J, if j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j) then 1 else 0 := by
        intro j _; rw [Finset.sum_boole, Nat.cast_id]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi; rw [Finset.sum_boole, Nat.cast_id]; congr 1; ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Finset.mem_biUnion.mpr ⟨i, hi, h1⟩, h1, h2⟩
    rw [Finset.sum_add_distrib, ← hMsum, ← hswap]; omega

  have hno_eq : ∀ i ∈ J, ∀ j ∈ scope i, d (Sum.inl i) ≠ d (Sum.inr j) := by
    intro i hi j hj hdeq
    have hlt_i : (M i).card + ((scope i).filter (fun j' => d (Sum.inl i) < d (Sum.inr j'))).card < (scope i).card := by
      have hdisj : Disjoint (M i) ((scope i).filter (fun j' => d (Sum.inl i) < d (Sum.inr j'))) := by
        rw [Finset.disjoint_left]; intro j' h1 h2
        have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
      rw [← Finset.card_union_of_disjoint hdisj]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))]
      refine ⟨j, hj, ?_⟩
      simp only [Finset.mem_union, M, Finset.mem_filter, not_or, not_and]
      exact ⟨fun _ => by omega, fun _ => by omega⟩
    have hle_all : ∀ i' ∈ J, (M i').card + ((scope i').filter (fun j' => d (Sum.inl i') < d (Sum.inr j'))).card ≤ (scope i').card := by
      intro i' _
      have hdisj : Disjoint (M i') ((scope i').filter (fun j' => d (Sum.inl i') < d (Sum.inr j'))) := by
        rw [Finset.disjoint_left]; intro j' h1 h2
        have := (Finset.mem_filter.mp h1).2; have := (Finset.mem_filter.mp h2).2; omega
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have hstrict := Finset.sum_lt_sum hle_all ⟨i, hi, hlt_i⟩
    omega
  have hsite_eq1 : ∀ j ∈ J.biUnion scope,
      (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card = 1 := by
    intro j hj
    by_contra hne1
    have hgt1 : 1 < (J.filter (fun i => j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j))).card := by
      have := hsite_ge j hj; omega
    have hstrict := Finset.sum_lt_sum hsite_ge ⟨j, hj, hgt1⟩
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hstrict
    omega
  refine ⟨M, fun i _ => Finset.filter_subset _ _, ?_, ?_, ?_⟩
  · rw [Finset.filter_eq_empty_iff]; intro j _; rw [hd0]; omega
  · intro i hi hne
    exact Finset.card_pos.mp (hrow_ge i (Finset.mem_erase.mpr ⟨hne, hi⟩))
  · intro j hj
    rw [← hsite_eq1 j hj]
    congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, M]
    constructor
    · rintro ⟨hiJ, hjsc, hnotM⟩
      refine ⟨hiJ, hjsc, ?_⟩
      have hne := hno_eq i hiJ j hjsc
      have : ¬ d (Sum.inr j) < d (Sum.inl i) := fun h => hnotM ⟨hjsc, h⟩
      omega
    · rintro ⟨hiJ, hjsc, hlt⟩
      exact ⟨hiJ, hjsc, fun h => by omega⟩

private lemma non_tree_or_non_demanding_all_nonempty {n t : Nat} (scope : Fin t → Finset (Fin n))
    (hnonempty : ∀ i, (scope i).Nonempty) (i₀ : Fin t) (dem : Fin n → Prop) [DecidablePred dem] :
    let J := (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i₀ h)
    ((∃ j₀ ∈ J.biUnion scope, ¬ dem j₀) ∨
      J.sum (fun i => (scope i).card) + 1 ≠ J.card + (J.biUnion scope).card) →
    ∃ M : Fin t → Finset (Fin n),
      (∀ i ∈ J, M i ⊆ scope i ∧ (M i).Nonempty) ∧
      (∀ j ∈ J.biUnion scope, (J.filter (fun i => j ∈ scope i \ M i)).card = if dem j then 1 else 0) := by
  classical
  intro J hcond
  have hconn_from : ∀ root : Sum (Fin t) (Fin n),
      (match root with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
      ∀ v, (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
      ∃ k, bipReach scope J none k root v := by
    intro root hroot v hv
    rcases bipReach_none_of_comp scope root hroot with ⟨k1, hk1⟩
    rcases bipReach_none_of_comp scope v hv with ⟨k2, hk2⟩
    exact ⟨k1 + k2, bipReach_trans scope J none (bipReach_symm scope J none hk1) hk2⟩
  rcases hcond with ⟨j₀, hj₀, hndem⟩ | hnot_tree
  ·
    rcases bfs_parent_edges scope J none (Sum.inr j₀) (hconn_from (Sum.inr j₀) hj₀) with ⟨d, hd0, hpar, _⟩
    have hq_ex : ∀ j ∈ J.biUnion scope, j ≠ j₀ → ∃ i ∈ J, j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j) := by
      intro j hj hne
      rcases hpar (Sum.inr j) hj (fun h => hne (Sum.inr.inj h)) with ⟨u, hadj, hdu⟩
      cases u with
      | inr _ => exact absurd hadj id
      | inl i => exact ⟨i, hadj.1, hadj.2.1, hdu⟩
    let q : Fin n → Option (Fin t) := fun j =>
      if h : j ∈ J.biUnion scope ∧ j ≠ j₀ ∧ dem j then
        some (Classical.choose (hq_ex j h.1 h.2.1))
      else none
    let M : Fin t → Finset (Fin n) := fun i =>
      (scope i).filter (fun j => q j ≠ some i)
    refine ⟨M, ?_, ?_⟩
    · intro i hi
      refine ⟨Finset.filter_subset _ _, ?_⟩
      rcases hpar (Sum.inl i) hi (by simp) with ⟨u, hadj, hdu⟩
      cases u with
      | inl _ => exact absurd hadj id
      | inr j =>
        refine ⟨j, Finset.mem_filter.mpr ⟨hadj.2.1, ?_⟩⟩
        intro hqi
        simp only [q] at hqi
        split at hqi
        · rename_i hcondj
          have hspec := Classical.choose_spec (hq_ex j hcondj.1 hcondj.2.1)
          have heq : Classical.choose (hq_ex j hcondj.1 hcondj.2.1) = i := Option.some.inj hqi
          rw [heq] at hspec
          omega
        · cases hqi
    · intro j hj
      by_cases hdj : dem j
      · rw [if_pos hdj]
        have hnej : j ≠ j₀ := fun he => hndem (he ▸ hdj)
        have hcondj : j ∈ J.biUnion scope ∧ j ≠ j₀ ∧ dem j := ⟨hj, hnej, hdj⟩
        let i1 := Classical.choose (hq_ex j hj hnej)
        have hi1 := Classical.choose_spec (hq_ex j hj hnej)
        have hfilt : J.filter (fun i => j ∈ scope i \ M i) = {i1} := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_sdiff, M, Finset.mem_singleton, not_and, not_not]
          constructor
          · rintro ⟨_, hjsc, hqi⟩
            have h := hqi hjsc
            dsimp only [q] at h
            rw [dif_pos hcondj] at h
            exact (Option.some.inj h).symm
          · rintro rfl
            refine ⟨hi1.1, hi1.2.1, fun _ => ?_⟩
            dsimp only [q]
            rw [dif_pos hcondj]
        rw [hfilt]; simp
      · rw [if_neg hdj]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        simp only [Finset.mem_sdiff, M, Finset.mem_filter, not_and, not_not]
        intro hjsc hqi
        have h := hqi hjsc
        dsimp only [q] at h
        rw [dif_neg (fun hc => hdj hc.2.2)] at h
        cases h
  ·
    have hi₀J : i₀ ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_refl scope t i₀⟩
    rcases hnonempty i₀ with ⟨j₀, hj₀i⟩
    have hj₀ : j₀ ∈ J.biUnion scope := Finset.mem_biUnion.mpr ⟨i₀, hi₀J, hj₀i⟩
    rcases bfs_parent_edges scope J none (Sum.inr j₀) (hconn_from (Sum.inr j₀) hj₀) with ⟨d, hd0, hpar, _⟩

    have hp_ex : ∀ i ∈ J, ∃ j ∈ scope i, d (Sum.inr j) < d (Sum.inl i) := by
      intro i hi
      rcases hpar (Sum.inl i) hi (by simp) with ⟨u, hadj, hdu⟩
      cases u with
      | inl _ => exact absurd hadj id
      | inr j => exact ⟨j, hadj.2.1, hdu⟩
    have hq_ex : ∀ j ∈ J.biUnion scope, j ≠ j₀ → ∃ i ∈ J, j ∈ scope i ∧ d (Sum.inl i) < d (Sum.inr j) := by
      intro j hj hne
      rcases hpar (Sum.inr j) hj (fun h => hne (Sum.inr.inj h)) with ⟨u, hadj, hdu⟩
      cases u with
      | inr _ => exact absurd hadj id
      | inl i => exact ⟨i, hadj.1, hadj.2.1, hdu⟩
    let p : Fin t → Fin n := fun i => if h : i ∈ J then Classical.choose (hp_ex i h) else j₀
    let q : Fin n → Fin t := fun j => if h : j ∈ J.biUnion scope ∧ j ≠ j₀ then Classical.choose (hq_ex j h.1 h.2) else i₀
    let E : Finset (Fin t × Fin n) := J.biUnion (fun i => (scope i).image (fun j => (i, j)))
    let K : Finset (Fin t × Fin n) := J.image (fun i => (i, p i))
    let Q : Finset (Fin t × Fin n) := ((J.biUnion scope).erase j₀).image (fun j => (q j, j))
    have hEcard : E.card = J.sum (fun i => (scope i).card) := by
      have hdisj : (J : Set (Fin t)).PairwiseDisjoint (fun i => (scope i).image (fun j => (i, j))) := by
        intro i₁ _ i₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro e he1 he2
        rcases Finset.mem_image.mp he1 with ⟨_, _, rfl⟩
        rcases Finset.mem_image.mp he2 with ⟨_, _, heq⟩
        exact hne (Prod.mk.inj heq).1.symm
      rw [Finset.card_biUnion hdisj]
      apply Finset.sum_congr rfl
      intro i _; exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
    have hKsub : K ⊆ E := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
      have hspec := Classical.choose_spec (hp_ex i hi)
      exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨p i, by simpa [p, hi] using hspec.1, rfl⟩⟩
    have hQsub : Q ⊆ E := by
      intro e he
      rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
      have ⟨hnej, hjU⟩ := Finset.mem_erase.mp hj
      have hspec := Classical.choose_spec (hq_ex j hjU hnej)
      have hcond : j ∈ J.biUnion scope ∧ j ≠ j₀ := ⟨hjU, hnej⟩
      have h1 : q j ∈ J := by dsimp only [q]; rw [dif_pos hcond]; exact hspec.1
      have h2 : j ∈ scope (q j) := by dsimp only [q]; rw [dif_pos hcond]; exact hspec.2.1
      exact Finset.mem_biUnion.mpr ⟨q j, h1, Finset.mem_image.mpr ⟨j, h2, rfl⟩⟩
    have hKQ_disj : Disjoint K Q := by
      rw [Finset.disjoint_left]
      intro e heK heQ
      rcases Finset.mem_image.mp heK with ⟨i, hi, rfl⟩
      rcases Finset.mem_image.mp heQ with ⟨j, hj, hEq⟩
      have ⟨hnej, hjU⟩ := Finset.mem_erase.mp hj
      have h1 : i = q j := (Prod.mk.inj hEq).1.symm
      have h2 : p i = j := (Prod.mk.inj hEq).2.symm
      have hcond : j ∈ J.biUnion scope ∧ j ≠ j₀ := ⟨hjU, hnej⟩
      have hd1 : d (Sum.inr (p i)) < d (Sum.inl i) := by simpa [p, hi] using (Classical.choose_spec (hp_ex i hi)).2
      have hd2 : d (Sum.inl (q j)) < d (Sum.inr j) := by dsimp only [q]; rw [dif_pos hcond]; exact (Classical.choose_spec (hq_ex j hjU hnej)).2.2
      rw [h2, h1] at hd1; omega
    have hKcard : K.card = J.card := Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
    have hQcard : Q.card = (J.biUnion scope).card - 1 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_erase_of_mem hj₀]
    have hKQ_card : (K ∪ Q).card = J.card + (J.biUnion scope).card - 1 := by
      rw [Finset.card_union_of_disjoint hKQ_disj, hKcard, hQcard]
      have hpos : 1 ≤ (J.biUnion scope).card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
      omega
    have hE_gt : (K ∪ Q).card < E.card := by
      have hle : (K ∪ Q).card ≤ E.card := Finset.card_le_card (Finset.union_subset hKsub hQsub)
      have hpos : 1 ≤ (J.biUnion scope).card := Finset.card_pos.mpr ⟨j₀, hj₀⟩
      rw [hEcard, hKQ_card] at hle ⊢
      omega
    have hssub : K ∪ Q ⊂ E := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.union_subset hKsub hQsub, fun hEq => by rw [hEq] at hE_gt; omega⟩
    rcases Finset.exists_of_ssubset hssub with ⟨⟨iStar, jStar⟩, hEstar, hnotKQ⟩
    rcases Finset.mem_biUnion.mp hEstar with ⟨i', hi'J, hj'img⟩
    rcases Finset.mem_image.mp hj'img with ⟨j', hj'sc, hpair⟩
    have hiStarJ : iStar ∈ J := (Prod.mk.inj hpair).1 ▸ hi'J
    have hjStar_sc : jStar ∈ scope iStar := by
      have h1 : i' = iStar := (Prod.mk.inj hpair).1
      have h2 : j' = jStar := (Prod.mk.inj hpair).2
      subst h1; subst h2; exact hj'sc
    have hjStarU : jStar ∈ J.biUnion scope := Finset.mem_biUnion.mpr ⟨iStar, hiStarJ, hjStar_sc⟩

    have hreach_skip_j0 : ∀ v : Sum (Fin t) (Fin n),
        (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
        ∃ k, bipReach scope J (some (iStar, jStar)) k (Sum.inr j₀) v := by
      suffices ∀ m v, (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
          d v = m → ∃ k, bipReach scope J (some (iStar, jStar)) k (Sum.inr j₀) v from
        fun v hv => this (d v) v hv rfl
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro v hv hdv
        cases v with
        | inl i =>
          have hspec := Classical.choose_spec (hp_ex i hv)
          have hpi_sc : p i ∈ scope i := by simpa [p, hv] using hspec.1
          have hpi_d : d (Sum.inr (p i)) < m := by rw [← hdv]; simpa [p, hv] using hspec.2
          have hpiU : p i ∈ J.biUnion scope := Finset.mem_biUnion.mpr ⟨i, hv, hpi_sc⟩
          rcases ih (d (Sum.inr (p i))) hpi_d (Sum.inr (p i)) hpiU rfl with ⟨k, hk⟩
          have hne_star : some (iStar, jStar) ≠ some (i, p i) := by
            intro heq
            have hp_eq := Option.some.inj heq
            exact hnotKQ (Finset.mem_union_left _ (hp_eq ▸ Finset.mem_image.mpr ⟨i, hv, rfl⟩))
          exact ⟨k + 1, Or.inr ⟨Sum.inr (p i), hk, ⟨hv, hpi_sc, hne_star⟩⟩⟩
        | inr j =>
          by_cases hj : j = j₀
          · subst hj; exact ⟨0, rfl⟩
          · have hspec := Classical.choose_spec (hq_ex j hv hj)
            have hcond : j ∈ J.biUnion scope ∧ j ≠ j₀ := ⟨hv, hj⟩
            have hqjJ : q j ∈ J := by dsimp only [q]; rw [dif_pos hcond]; exact hspec.1
            have hqj_sc : j ∈ scope (q j) := by dsimp only [q]; rw [dif_pos hcond]; exact hspec.2.1
            have hqj_d : d (Sum.inl (q j)) < m := by rw [← hdv]; dsimp only [q]; rw [dif_pos hcond]; exact hspec.2.2
            rcases ih (d (Sum.inl (q j))) hqj_d (Sum.inl (q j)) hqjJ rfl with ⟨k, hk⟩
            have hne_star : some (iStar, jStar) ≠ some (q j, j) := by
              intro heq
              have hq_eq := Option.some.inj heq
              exact hnotKQ (Finset.mem_union_right _
                (hq_eq ▸ Finset.mem_image.mpr ⟨j, Finset.mem_erase.mpr ⟨hj, hv⟩, rfl⟩))
            exact ⟨k + 1, Or.inr ⟨Sum.inl (q j), hk, ⟨hqjJ, hqj_sc, hne_star⟩⟩⟩
    have hconn_star : ∀ v : Sum (Fin t) (Fin n),
        (match v with | Sum.inl i => i ∈ J | Sum.inr j => j ∈ J.biUnion scope) →
        ∃ k, bipReach scope J (some (iStar, jStar)) k (Sum.inr jStar) v := by
      intro v hv
      rcases hreach_skip_j0 (Sum.inr jStar) hjStarU with ⟨k1, hk1⟩
      rcases hreach_skip_j0 v hv with ⟨k2, hk2⟩
      exact ⟨k1 + k2, bipReach_trans scope J (some (iStar, jStar))
        (bipReach_symm scope J (some (iStar, jStar)) hk1) hk2⟩

    rcases bfs_parent_edges scope J (some (iStar, jStar)) (Sum.inr jStar) hconn_star with ⟨d', _, hpar', _⟩
    have hq'_ex : ∀ j ∈ J.biUnion scope, j ≠ jStar →
        ∃ i ∈ J, j ∈ scope i ∧ some (iStar, jStar) ≠ some (i, j) ∧ d' (Sum.inl i) < d' (Sum.inr j) := by
      intro j hj hne
      rcases hpar' (Sum.inr j) hj (fun h => hne (Sum.inr.inj h)) with ⟨u, hadj, hdu⟩
      cases u with
      | inr _ => exact absurd hadj id
      | inl i => exact ⟨i, hadj.1, hadj.2.1, hadj.2.2, hdu⟩
    let q' : Fin n → Option (Fin t) := fun j =>
      if h : j ∈ J.biUnion scope ∧ dem j then
        if hne : j = jStar then some iStar
        else some (Classical.choose (hq'_ex j h.1 hne))
      else none
    let M : Fin t → Finset (Fin n) := fun i =>
      (scope i).filter (fun j => q' j ≠ some i)
    refine ⟨M, ?_, ?_⟩
    · intro i hi
      refine ⟨Finset.filter_subset _ _, ?_⟩
      rcases hpar' (Sum.inl i) hi (by simp) with ⟨u, hadj, hdu⟩
      cases u with
      | inl _ => exact absurd hadj id
      | inr j =>
        refine ⟨j, Finset.mem_filter.mpr ⟨hadj.2.1, ?_⟩⟩
        intro hqi
        simp only [q'] at hqi
        split at hqi
        · rename_i hcondj
          split at hqi
          · rename_i heqj
            subst heqj
            have heqi : iStar = i := Option.some.inj hqi
            subst heqi
            exact hadj.2.2 rfl
          · rename_i hnej
            have hspec := Classical.choose_spec (hq'_ex j hcondj.1 hnej)
            have heq : Classical.choose (hq'_ex j hcondj.1 hnej) = i := Option.some.inj hqi
            rw [heq] at hspec
            omega
        · cases hqi
    · intro j hj
      by_cases hdj : dem j
      · rw [if_pos hdj]
        have hcondj : j ∈ J.biUnion scope ∧ dem j := ⟨hj, hdj⟩
        by_cases hjs : j = jStar
        · subst hjs
          have hfilt : J.filter (fun i => j ∈ scope i \ M i) = {iStar} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_sdiff, M, Finset.mem_singleton, not_and, not_not]
            constructor
            · rintro ⟨_, hjsc, hqi⟩
              have h := hqi hjsc
              dsimp only [q'] at h
              rw [dif_pos hcondj, dif_pos rfl] at h
              exact (Option.some.inj h).symm
            · rintro rfl
              refine ⟨hiStarJ, hjStar_sc, fun _ => ?_⟩
              dsimp only [q']
              rw [dif_pos hcondj, dif_pos rfl]
          rw [hfilt]; simp
        · let i1 := Classical.choose (hq'_ex j hj hjs)
          have hi1 := Classical.choose_spec (hq'_ex j hj hjs)
          have hfilt : J.filter (fun i => j ∈ scope i \ M i) = {i1} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_sdiff, M, Finset.mem_singleton, not_and, not_not]
            constructor
            · rintro ⟨_, hjsc, hqi⟩
              have h := hqi hjsc
              dsimp only [q'] at h
              rw [dif_pos hcondj, dif_neg hjs] at h
              exact (Option.some.inj h).symm
            · rintro rfl
              refine ⟨hi1.1, hi1.2.1, fun _ => ?_⟩
              dsimp only [q']
              rw [dif_pos hcondj, dif_neg hjs]
          rw [hfilt]; simp
      · rw [if_neg hdj]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _
        simp only [Finset.mem_sdiff, M, Finset.mem_filter, not_and, not_not]
        intro hjsc hqi
        have h := hqi hjsc
        dsimp only [q'] at h
        rw [dif_neg (fun hc => hdj hc.2)] at h
        cases h

private def multOf {n t : Nat} (scope : Fin t → Finset (Fin n)) (M : Fin t → Finset (Fin n)) : ℤ :=
  ∏ i : Fin t, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1

private lemma odd_prod_nat {α : Type*} (s : Finset α) (f : α → Nat) (hf : ∀ a ∈ s, f a % 2 = 1) :
    (∏ a ∈ s, f a) % 2 = 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Nat.mul_mod]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    rw [h1, h2]

private lemma int_dvd_of_coprime_mul {a b : Nat} {x : ℤ} (hcop : Nat.Coprime a b)
    (h : (a : ℤ) ∣ (b : ℤ) * x) : (a : ℤ) ∣ x := by
  have hbez : (1 : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b := by
    have := Nat.gcd_eq_gcd_ab a b
    rw [hcop.gcd_eq_one] at this; exact this
  have hx : x = (a : ℤ) * (Nat.gcdA a b * x) + Nat.gcdB a b * ((b : ℤ) * x) := by
    calc x = 1 * x := (one_mul x).symm
      _ = ((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b) * x := by rw [← hbez]
      _ = (a : ℤ) * (Nat.gcdA a b * x) + Nat.gcdB a b * ((b : ℤ) * x) := by ring
  rw [hx]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right h _)

private lemma bezout_finset_gcd {α : Type*} [DecidableEq α] (s : Finset α) (f : α → Nat) :
    ∃ coeff : α → ℤ, ∑ a ∈ s, coeff a * (f a : ℤ) = ((s.gcd f : Nat) : ℤ) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp⟩
  | insert a s ha ih =>
    rcases ih with ⟨c, hc⟩
    let u := Nat.gcdA (f a) (s.gcd f)
    let v := Nat.gcdB (f a) (s.gcd f)
    have hbez : ((Nat.gcd (f a) (s.gcd f) : Nat) : ℤ) = (f a : ℤ) * u + ((s.gcd f : Nat) : ℤ) * v :=
      Nat.gcd_eq_gcd_ab (f a) (s.gcd f)
    refine ⟨fun x => if x = a then u else v * c x, ?_⟩
    rw [Finset.sum_insert ha]
    simp only [ite_true]
    have hrest : ∑ x ∈ s, (if x = a then u else v * c x) * (f x : ℤ) =
        v * ∑ x ∈ s, c x * (f x : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      have hne : x ≠ a := fun h => ha (h ▸ hx)
      simp [hne, mul_assoc]
    rw [hrest, hc, Finset.gcd_insert]
    change u * (f a : ℤ) + v * ((s.gcd f : Nat) : ℤ) = ((Nat.gcd (f a) (s.gcd f) : Nat) : ℤ)
    rw [hbez]; ring

private lemma divisor_dvd_and_comb {n t : Nat} (scope : Fin t → Finset (Fin n))
    (hnonempty : ∀ i, (scope i).Nonempty) (hcov : ∀ j : Fin n, ∃ i, j ∈ scope i)
    (T : Finset (Fin n)) :
    let rows := (Finset.univ : Finset (Fin t))
    let sites := (Finset.univ : Finset (Fin n))
    let closed := fun (J : Finset (Fin t)) => J.toList.all (fun i => rows.toList.all
      (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))
    let components := rows.powerset.filter (fun J => J.Nonempty ∧ closed J = true ∧
      ∀ K ∈ J.powerset, K.Nonempty → closed K = true → K = J)
    let support := fun (J : Finset (Fin t)) => J.biUnion scope
    let trees := components.filter (fun J =>
      J.sum (fun i => (scope i).card) + 1 = J.card + (support J).card)
    let widthGCD := fun (J : Finset (Fin t)) => J.gcd (fun i => (scope i).card)
    let exceptional := sites.filter (fun j => (rows.filter (fun i => j ∈ scope i)).card % 2 = 0)
    let divisor := (trees.filter (fun J => T ∩ support J = exceptional ∩ support J)).prod
      (fun J => (2 ^ widthGCD J - 1 : Nat))
    let choices := (Finset.univ : Finset (Fin t → Finset (Fin n))).filter (fun R => ∀ i, R i ⊆ scope i)
    (divisor % 2 = 1) ∧
    (∀ M ∈ choices, xorAll M = T → (divisor : ℤ) ∣ multOf scope M) ∧
    (∃ α : (Fin t → Finset (Fin n)) → ℤ,
      ∑ M ∈ choices.filter (fun M => xorAll M = T), α M * multOf scope M = (divisor : ℤ)) := by
  intro rows sites closed components support trees widthGCD exceptional divisor choices

  have hcomp_disj : (components : Set (Finset (Fin t))).PairwiseDisjoint id := by
    intro J₁ hJ₁ J₂ hJ₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro i hi1 hi2
    rcases (mem_components_iff scope J₁).mp hJ₁ with ⟨i₁, rfl⟩
    rcases (mem_components_iff scope J₂).mp hJ₂ with ⟨i₂, rfl⟩
    have h1 : rowReach scope t i₁ i := (Finset.mem_filter.mp hi1).2
    have h2 : rowReach scope t i₂ i := (Finset.mem_filter.mp hi2).2
    apply hne
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h1h
      exact rowReach_bound scope (rowReach_trans scope h2 (rowReach_trans scope (rowReach_symm scope h1) h1h))
    · intro h2h
      exact rowReach_bound scope (rowReach_trans scope h1 (rowReach_trans scope (rowReach_symm scope h2) h2h))
  have hcomp_cov : components.biUnion id = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    refine ⟨(Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i h),
      (mem_components_iff scope _).mpr ⟨i, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_refl scope t i⟩⟩
  have hsupp_disj : ∀ J₁ ∈ components, ∀ J₂ ∈ components, J₁ ≠ J₂ → Disjoint (support J₁) (support J₂) := by
    intro J₁ hJ₁ J₂ hJ₂ hne
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    rcases Finset.mem_biUnion.mp hj1 with ⟨i₁, hi1, hji1⟩
    rcases Finset.mem_biUnion.mp hj2 with ⟨i₂, hi2, hji2⟩
    have hJ1cl := (closed_iff scope J₁).mp (Finset.mem_filter.mp hJ₁).2.2.1
    have hi2_in_J1 : i₂ ∈ J₁ := hJ1cl i₁ hi1 i₂ ⟨j, Finset.mem_inter.mpr ⟨hji1, hji2⟩⟩
    exact Finset.disjoint_left.mp (hcomp_disj hJ₁ hJ₂ hne) hi2_in_J1 hi2

  have hdiv_odd : divisor % 2 = 1 := by
    apply odd_prod_nat
    intro J hJ
    have hJcomp : J ∈ components := (Finset.mem_filter.mp (Finset.mem_filter.mp hJ).1).1
    have hJne : J.Nonempty := (Finset.mem_filter.mp hJcomp).2.1
    have hgcd_pos : 0 < widthGCD J := by
      rcases hJne with ⟨i, hi⟩
      by_contra h0
      have hgcd0 : widthGCD J = 0 := by omega
      have hdvd : widthGCD J ∣ (scope i).card := Finset.gcd_dvd hi
      rw [hgcd0, zero_dvd_iff] at hdvd
      exact Finset.card_ne_zero.mpr (hnonempty i) hdvd
    exact odd_two_pow_sub_one hgcd_pos

  have hdiv_dvd : ∀ M ∈ choices, xorAll M = T → (divisor : ℤ) ∣ multOf scope M := by
    intro M hM hMxor
    have hMsub : ∀ i, M i ⊆ scope i := (Finset.mem_filter.mp hM).2
    have hprod_split : multOf scope M =
        ∏ J ∈ components, ∏ i ∈ J, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1 := by
      unfold multOf
      rw [← hcomp_cov, Finset.prod_biUnion hcomp_disj]
      rfl
    rw [hprod_split]
    let badTrees := trees.filter (fun J => T ∩ support J = exceptional ∩ support J)
    have hsub_comp : badTrees ⊆ components :=
      (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    rw [← Finset.prod_sdiff hsub_comp]
    apply dvd_mul_of_dvd_right
    rw [Nat.cast_prod]
    apply Finset.prod_dvd_prod_of_dvd
    intro J hJ
    have hJtree := (Finset.mem_filter.mp hJ).1
    have hJT := (Finset.mem_filter.mp hJ).2
    have hJcomp := (Finset.mem_filter.mp hJtree).1
    have hJtr_eq := (Finset.mem_filter.mp hJtree).2
    have hJcl := (closed_iff scope J).mp (Finset.mem_filter.mp hJcomp).2.2.1
    rcases tree_all_demanding_forces_empty scope J hJcl hJtr_eq T hJT M hMsub hMxor with ⟨i₀, hi₀J, hMi₀⟩
    have hdvd_nat : 2 ^ widthGCD J - 1 ∣ 2 ^ (scope i₀).card - 1 := by
      have hg : widthGCD J ∣ (scope i₀).card := Finset.gcd_dvd hi₀J
      have h1 : Nat.gcd (2 ^ widthGCD J - 1) (2 ^ (scope i₀).card - 1) = 2 ^ widthGCD J - 1 := by
        rw [gcd_two_pow_sub_one, Nat.gcd_eq_left hg]
      rw [← h1]
      exact Nat.gcd_dvd_right _ _
    have hdvd_int : ((2 ^ widthGCD J - 1 : Nat) : ℤ) ∣ ((2 : ℤ) ^ (scope i₀).card - 1) := by
      have hge1 : 1 ≤ 2 ^ (scope i₀).card := Nat.one_le_two_pow
      have hcast : ((2 ^ (scope i₀).card - 1 : Nat) : ℤ) = (2 : ℤ) ^ (scope i₀).card - 1 := by
        zify [hge1]
      rw [← hcast]
      exact Int.ofNat_dvd.mpr hdvd_nat
    rw [← Finset.mul_prod_erase J _ hi₀J, if_pos hMi₀]
    exact dvd_mul_of_dvd_left hdvd_int _

  have hloc_comb : ∀ J ∈ components,
      ∃ (S_J : Finset (Fin t → Finset (Fin n))) (w_J : (Fin t → Finset (Fin n)) → ℤ),
        (∀ M ∈ S_J, (∀ i ∈ J, M i ⊆ scope i) ∧
          (∀ j ∈ support J, (J.filter (fun i => j ∈ scope i \ M i)).card % 2 =
            if (j ∈ T ↔ j ∈ exceptional) then 1 else 0)) ∧
        ∑ M ∈ S_J, w_J M * (∏ i ∈ J, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1) =
          if J ∈ trees ∧ T ∩ support J = exceptional ∩ support J then ((2 ^ widthGCD J - 1 : Nat) : ℤ) else 1 := by
    intro J hJ
    rcases (mem_components_iff scope J).mp hJ with ⟨i₀, rfl⟩
    let J' := (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i₀ h)
    by_cases hbad : J' ∈ trees ∧ T ∩ support J' = exceptional ∩ support J'
    · rw [if_pos hbad]
      have htr : J'.sum (fun i => (scope i).card) + 1 = J'.card + (J'.biUnion scope).card :=
        (Finset.mem_filter.mp hbad.1).2

      have hex_i : ∀ i ∈ J', ∃ M : Fin t → Finset (Fin n),
          (∀ u ∈ J', M u ⊆ scope u) ∧ M i = ∅ ∧ (∀ u ∈ J', u ≠ i → (M u).Nonempty) ∧
          (∀ j ∈ support J', (J'.filter (fun u => j ∈ scope u \ M u)).card = 1) := by
        intro i hi
        have hJeq : (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i h) = J' := by
          ext h
          simp only [J', Finset.mem_filter, Finset.mem_univ, true_and]
          have hi' : rowReach scope t i₀ i := (Finset.mem_filter.mp hi).2
          constructor
          · intro hih; exact rowReach_bound scope (rowReach_trans scope hi' hih)
          · intro hi0h; exact rowReach_bound scope (rowReach_trans scope (rowReach_symm scope hi') hi0h)
        have htr' := htr
        rw [← hJeq] at htr'
        rcases tree_empty_single scope i htr' with ⟨M, h1, h2, h3, h4⟩
        rw [hJeq] at h1 h3 h4
        exact ⟨M, h1, h2, h3, h4⟩
      let Mof : Fin t → (Fin t → Finset (Fin n)) := fun i =>
        if h : i ∈ J' then Classical.choose (hex_i i h) else fun _ => ∅

      have hmult_i : ∀ i ∈ J',
          ∃ sgn : ℤ, (sgn = 1 ∨ sgn = -1) ∧
            sgn * (∏ u ∈ J', if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1) =
              ((2 ^ (scope i).card - 1 : Nat) : ℤ) := by
        intro i hi
        have hspec := Classical.choose_spec (hex_i i hi)
        have hMi : Mof i i = ∅ := by dsimp only [Mof]; rw [dif_pos hi]; exact hspec.2.1
        have hMne : ∀ u ∈ J'.erase i, Mof i u ≠ ∅ := by
          intro u hu
          have ⟨hne, huJ⟩ := Finset.mem_erase.mp hu
          dsimp only [Mof]; rw [dif_pos hi]
          exact Finset.nonempty_iff_ne_empty.mp (hspec.2.2.1 u huJ hne)
        have hprod : ∏ u ∈ J', (if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1) =
            ((2 : ℤ) ^ (scope i).card - 1) * (-1 : ℤ) ^ (J'.erase i).card := by
          rw [← Finset.mul_prod_erase J' _ hi, if_pos hMi]
          congr 1
          calc ∏ u ∈ J'.erase i, (if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1)
              = ∏ _u ∈ J'.erase i, (-1 : ℤ) := Finset.prod_congr rfl (fun u hu => by simp [hMne u hu])
            _ = (-1 : ℤ) ^ (J'.erase i).card := by simp
        refine ⟨(-1 : ℤ) ^ (J'.erase i).card, ?_, ?_⟩
        · rcases Nat.even_or_odd (J'.erase i).card with ⟨k, hk⟩ | ⟨k, hk⟩
          · left; rw [hk]; simp [← two_mul, pow_mul]
          · right; rw [hk]; simp [pow_add, pow_mul]
        · rw [hprod]
          have hsq : (-1 : ℤ) ^ (J'.erase i).card * (-1 : ℤ) ^ (J'.erase i).card = 1 := by
            rw [← mul_pow]; simp
          have hge1 : 1 ≤ 2 ^ (scope i).card := Nat.one_le_two_pow
          have hcast : ((2 ^ (scope i).card - 1 : Nat) : ℤ) = (2 : ℤ) ^ (scope i).card - 1 := by zify [hge1]
          rw [hcast]
          calc (-1 : ℤ) ^ (J'.erase i).card * (((2 : ℤ) ^ (scope i).card - 1) * (-1 : ℤ) ^ (J'.erase i).card)
              = ((2 : ℤ) ^ (scope i).card - 1) * ((-1 : ℤ) ^ (J'.erase i).card * (-1 : ℤ) ^ (J'.erase i).card) := by ring
            _ = (2 : ℤ) ^ (scope i).card - 1 := by rw [hsq, mul_one]

      rcases bezout_finset_gcd J' (fun i => 2 ^ (scope i).card - 1) with ⟨c, hc⟩
      rw [finset_gcd_two_pow_sub_one] at hc
      let S_J := J'.image Mof
      let w_J : (Fin t → Finset (Fin n)) → ℤ := fun M =>
        ∑ i ∈ J'.filter (fun i => Mof i = M), c i * (-1 : ℤ) ^ (J'.erase i).card
      refine ⟨S_J, w_J, ?_, ?_⟩
      · intro M hM
        rcases Finset.mem_image.mp hM with ⟨i, hi, rfl⟩
        have hspec := Classical.choose_spec (hex_i i hi)
        refine ⟨by intro u hu; dsimp only [Mof]; rw [dif_pos hi]; exact hspec.1 u hu, ?_⟩
        intro j hj
        have hMeq : Mof i = Classical.choose (hex_i i hi) := by dsimp only [Mof]; rw [dif_pos hi]
        have h1 : (J'.filter (fun u => j ∈ scope u \ Mof i u)).card = 1 := by
          simpa [hMeq] using hspec.2.2.2 j hj
        have hdem : j ∈ T ↔ j ∈ exceptional := by
          have hj' : j ∈ support J' := hj
          have := Finset.ext_iff.mp hbad.2 j
          simp only [Finset.mem_inter, hj', and_true] at this
          exact this
        rw [h1, if_pos hdem]
      · have hsum_re : ∑ M ∈ S_J, w_J M * (∏ u ∈ J', if M u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1) =
            ∑ i ∈ J', c i * ((-1 : ℤ) ^ (J'.erase i).card *
              (∏ u ∈ J', if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1)) := by
          have h1 : ∀ M ∈ S_J, w_J M * (∏ u ∈ J', if M u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1) =
              ∑ i ∈ J'.filter (fun i => Mof i = M),
                c i * ((-1 : ℤ) ^ (J'.erase i).card *
                  (∏ u ∈ J', if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1)) := by
            intro M _
            dsimp only [w_J]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i hi
            have hMi := (Finset.mem_filter.mp hi).2
            rw [hMi]; ring
          rw [Finset.sum_congr rfl h1]
          rw [← Finset.sum_fiberwise_of_maps_to (g := Mof) (t := S_J) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)]
        rw [hsum_re, ← hc]
        apply Finset.sum_congr rfl
        intro i hi
        rcases hmult_i i hi with ⟨sgn, _, hsgn⟩

        have hspec := Classical.choose_spec (hex_i i hi)
        have hMi : Mof i i = ∅ := by dsimp only [Mof]; rw [dif_pos hi]; exact hspec.2.1
        have hMne : ∀ u ∈ J'.erase i, Mof i u ≠ ∅ := by
          intro u hu
          have ⟨hne, huJ⟩ := Finset.mem_erase.mp hu
          dsimp only [Mof]; rw [dif_pos hi]
          exact Finset.nonempty_iff_ne_empty.mp (hspec.2.2.1 u huJ hne)
        have hprod : ∏ u ∈ J', (if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1) =
            ((2 : ℤ) ^ (scope i).card - 1) * (-1 : ℤ) ^ (J'.erase i).card := by
          rw [← Finset.mul_prod_erase J' _ hi, if_pos hMi]
          congr 1
          calc ∏ u ∈ J'.erase i, (if Mof i u = ∅ then ((2 : ℤ) ^ (scope u).card - 1) else -1)
              = ∏ _u ∈ J'.erase i, (-1 : ℤ) := Finset.prod_congr rfl (fun u hu => by simp [hMne u hu])
            _ = (-1 : ℤ) ^ (J'.erase i).card := by simp
        have hsq : (-1 : ℤ) ^ (J'.erase i).card * (-1 : ℤ) ^ (J'.erase i).card = 1 := by
          rw [← mul_pow]; simp
        have hge1 : 1 ≤ 2 ^ (scope i).card := Nat.one_le_two_pow
        have hcast : ((2 ^ (scope i).card - 1 : Nat) : ℤ) = (2 : ℤ) ^ (scope i).card - 1 := by zify [hge1]
        rw [hprod, hcast]
        calc c i * ((-1 : ℤ) ^ (J'.erase i).card * (((2 : ℤ) ^ (scope i).card - 1) * (-1 : ℤ) ^ (J'.erase i).card))
            = c i * (((2 : ℤ) ^ (scope i).card - 1) * ((-1 : ℤ) ^ (J'.erase i).card * (-1 : ℤ) ^ (J'.erase i).card)) := by ring
          _ = c i * ((2 : ℤ) ^ (scope i).card - 1) := by rw [hsq, mul_one]
    ·
      rw [if_neg hbad]
      let dem : Fin n → Prop := fun j => j ∈ T ↔ j ∈ exceptional
      have hcond : (∃ j₀ ∈ J'.biUnion scope, ¬ dem j₀) ∨
          J'.sum (fun i => (scope i).card) + 1 ≠ J'.card + (J'.biUnion scope).card := by
        by_cases htr : J'.sum (fun i => (scope i).card) + 1 = J'.card + (J'.biUnion scope).card
        · left
          have hJ'tree : J' ∈ trees := Finset.mem_filter.mpr ⟨hJ, htr⟩
          have hTne : T ∩ support J' ≠ exceptional ∩ support J' := fun hEq => hbad ⟨hJ'tree, hEq⟩
          by_contra hall
          push Not at hall
          apply hTne
          ext j
          simp only [Finset.mem_inter]
          by_cases hj : j ∈ support J'
          · have hdj : j ∈ T ↔ j ∈ exceptional := hall j hj
            tauto
          · simp [hj]
        · exact Or.inr htr
      rcases non_tree_or_non_demanding_all_nonempty scope hnonempty i₀ dem hcond with ⟨M, hM, hdel⟩
      refine ⟨{M}, fun _ => (-1 : ℤ) ^ J'.card, ?_, ?_⟩
      · intro M' hM'
        rw [Finset.mem_singleton.mp hM']
        refine ⟨fun i hi => (hM i hi).1, ?_⟩
        intro j hj
        rw [hdel j hj]
        by_cases hd : dem j <;> simp [hd, dem]
      · simp only [Finset.sum_singleton]
        have hprod : ∏ i ∈ J', (if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1) =
            (-1 : ℤ) ^ J'.card := by
          calc _ = ∏ _i ∈ J', (-1 : ℤ) := Finset.prod_congr rfl (fun i hi => by
                  simp [Finset.nonempty_iff_ne_empty.mp (hM i hi).2])
            _ = _ := by simp
        rw [hprod, ← mul_pow]; simp

  let S_of : Finset (Fin t) → Finset (Fin t → Finset (Fin n)) := fun J =>
    if h : J ∈ components then Classical.choose (hloc_comb J h) else ∅
  let w_of : Finset (Fin t) → (Fin t → Finset (Fin n)) → ℤ := fun J =>
    if h : J ∈ components then Classical.choose (Classical.choose_spec (hloc_comb J h)) else fun _ => 0
  have hloc_spec : ∀ J (hJ : J ∈ components),
      (∀ M ∈ S_of J, (∀ i ∈ J, M i ⊆ scope i) ∧
        (∀ j ∈ support J, (J.filter (fun i => j ∈ scope i \ M i)).card % 2 =
          if (j ∈ T ↔ j ∈ exceptional) then 1 else 0)) ∧
      ∑ M ∈ S_of J, w_of J M * (∏ i ∈ J, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1) =
        if J ∈ trees ∧ T ∩ support J = exceptional ∩ support J then ((2 ^ widthGCD J - 1 : Nat) : ℤ) else 1 := by
    intro J hJ
    dsimp only [S_of, w_of]
    rw [dif_pos hJ, dif_pos hJ]
    exact Classical.choose_spec (Classical.choose_spec (hloc_comb J hJ))

  let compOf : Fin t → Finset (Fin t) := fun i =>
    (Finset.univ : Finset (Fin t)).filter (fun h => rowReach scope t i h)
  have hcompOf_mem : ∀ i : Fin t, compOf i ∈ components := fun i =>
    (mem_components_iff scope _).mpr ⟨i, rfl⟩
  have hcompOf_self : ∀ i : Fin t, i ∈ compOf i := fun i =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rowReach_refl scope t i⟩
  have hcompOf_eq : ∀ {J : Finset (Fin t)}, J ∈ components → ∀ i ∈ J, compOf i = J := by
    intro J hJ i hi
    have h1 := hcompOf_mem i
    by_contra hne
    exact Finset.disjoint_left.mp (hcomp_disj h1 hJ hne) (hcompOf_self i) hi
  let PiSet := Finset.pi components (fun J => S_of J)
  let glue : (∀ J ∈ components, Fin t → Finset (Fin n)) → (Fin t → Finset (Fin n)) := fun F i =>
    F (compOf i) (hcompOf_mem i) i
  have hglue_mem : ∀ F ∈ PiSet, glue F ∈ choices.filter (fun M => xorAll M = T) := by
    intro F hF
    have hF' := Finset.mem_pi.mp hF
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · intro i
      exact (hloc_spec (compOf i) (hcompOf_mem i)).1 (F (compOf i) (hcompOf_mem i)) (hF' _ (hcompOf_mem i)) |>.1 i (hcompOf_self i)
    · ext j
      simp only [xorAll, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hcov j with ⟨i0, hi0j⟩
      let J := compOf i0
      have hJ : J ∈ components := hcompOf_mem i0
      have hjJ : j ∈ support J := Finset.mem_biUnion.mpr ⟨i0, hcompOf_self i0, hi0j⟩
      have hsc_in_J : ∀ i : Fin t, j ∈ scope i → i ∈ J := by
        intro i hji
        have hJcl := (closed_iff scope J).mp (Finset.mem_filter.mp hJ).2.2.1
        exact hJcl i0 (hcompOf_self i0) i ⟨j, Finset.mem_inter.mpr ⟨hi0j, hji⟩⟩
      have hMsub_i : ∀ i : Fin t, glue F i ⊆ scope i := fun i =>
        (hloc_spec (compOf i) (hcompOf_mem i)).1 _ (hF' _ (hcompOf_mem i)) |>.1 i (hcompOf_self i)
      have hdel_eq : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card =
          ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ glue F i)).card +
          (J.filter (fun i => j ∈ scope i \ F J hJ i)).card := by
        have hdisj : Disjoint ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ glue F i))
            (J.filter (fun i => j ∈ scope i \ F J hJ i)) := by
          rw [Finset.disjoint_left]
          intro i hi1 hi2
          have h1 := (Finset.mem_filter.mp hi1).2
          have h2 := Finset.mem_filter.mp hi2
          have hci : compOf i = J := hcompOf_eq hJ i h2.1
          have hgi : glue F i = F J hJ i := by
            have hdep : ∀ (J' : Finset (Fin t)) (hJ' : J' ∈ components), J' = J → F J' hJ' i = F J hJ i := by
              rintro _ _ rfl; rfl
            exact hdep (compOf i) (hcompOf_mem i) hci
          rw [hgi] at h1
          exact (Finset.mem_sdiff.mp h2.2).2 h1
        rw [← Finset.card_union_of_disjoint hdisj]
        congr 1; ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        constructor
        · intro hji
          have hiJ : i ∈ J := hsc_in_J i hji
          have hci : compOf i = J := hcompOf_eq hJ i hiJ
          have hgi : glue F i = F J hJ i := by
            have hdep : ∀ (J' : Finset (Fin t)) (hJ' : J' ∈ components), J' = J → F J' hJ' i = F J hJ i := by
              rintro _ _ rfl; rfl
            exact hdep (compOf i) (hcompOf_mem i) hci
          by_cases hm : j ∈ glue F i
          · exact Or.inl hm
          · rw [hgi] at hm
            exact Or.inr ⟨hiJ, hji, hm⟩
        · rintro (hm | ⟨_, hji, _⟩)
          · exact hMsub_i i hm
          · exact hji
      have hdel_mod := (hloc_spec J hJ).1 (F J hJ) (hF' J hJ) |>.2 j hjJ
      have hex_iff : j ∈ exceptional ↔ ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 = 0 := by
        simp [exceptional, sites, rows]
      by_cases hjT : j ∈ T <;> by_cases hjex : j ∈ exceptional
      · simp only [hjT, hjex, iff_self, ite_true] at hdel_mod
        rw [hex_iff] at hjex
        simp only [hjT, iff_true]; omega
      · simp only [hjT, hjex, iff_false, not_true_eq_false, ite_false] at hdel_mod
        rw [hex_iff] at hjex
        have hlt : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 < 2 := Nat.mod_lt _ (by omega)
        simp only [hjT, iff_true]; omega
      · simp only [hjT, hjex, false_iff, not_true_eq_false, ite_false] at hdel_mod
        rw [hex_iff] at hjex
        simp only [hjT, iff_false]; omega
      · simp only [hjT, hjex, iff_self, ite_true] at hdel_mod
        rw [hex_iff] at hjex
        have hlt : ((Finset.univ : Finset (Fin t)).filter (fun i => j ∈ scope i)).card % 2 < 2 := Nat.mod_lt _ (by omega)
        simp only [hjT, iff_false]; omega

  let α : (Fin t → Finset (Fin n)) → ℤ := fun M =>
    ∑ F ∈ PiSet.filter (fun F => glue F = M), ∏ J ∈ components.attach, w_of J.1 (F J.1 J.2)
  refine ⟨hdiv_odd, hdiv_dvd, ⟨α, ?_⟩⟩
  have hsum_glue :
      ∑ M ∈ choices.filter (fun M => xorAll M = T), α M * multOf scope M =
      ∑ F ∈ PiSet, (∏ J ∈ components.attach, w_of J.1 (F J.1 J.2)) * multOf scope (glue F) := by
    have h1 : ∀ M ∈ choices.filter (fun M => xorAll M = T),
        α M * multOf scope M =
        ∑ F ∈ PiSet.filter (fun F => glue F = M),
          (∏ J ∈ components.attach, w_of J.1 (F J.1 J.2)) * multOf scope (glue F) := by
      intro M _
      dsimp only [α]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro F hF
      rw [(Finset.mem_filter.mp hF).2]
    rw [Finset.sum_congr rfl h1]
    rw [← Finset.sum_fiberwise_of_maps_to (g := glue) (t := choices.filter (fun M => xorAll M = T)) hglue_mem]
  rw [hsum_glue]
  have hterm : ∀ F ∈ PiSet,
      (∏ J ∈ components.attach, w_of J.1 (F J.1 J.2)) * multOf scope (glue F) =
      ∏ J ∈ components.attach,
        (w_of J.1 (F J.1 J.2) * (∏ i ∈ J.1, if F J.1 J.2 i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1)) := by
    intro F _
    have hms : multOf scope (glue F) =
        ∏ J ∈ components.attach, ∏ i ∈ J.1, if F J.1 J.2 i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1 := by
      unfold multOf
      rw [← hcomp_cov, Finset.prod_biUnion hcomp_disj, ← Finset.prod_attach]
      apply Finset.prod_congr rfl
      intro J _
      apply Finset.prod_congr rfl
      intro i hi
      have hci : compOf i = J.1 := hcompOf_eq J.2 i hi
      have hgi : glue F i = F J.1 J.2 i := by
        have hdep : ∀ (J' : Finset (Fin t)) (hJ' : J' ∈ components), J' = J.1 → F J' hJ' i = F J.1 J.2 i := by
          rintro _ _ rfl; rfl
        exact hdep (compOf i) (hcompOf_mem i) hci
      rw [hgi]
    rw [hms, Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl hterm]
  have hprod_sum :
      ∑ F ∈ PiSet, ∏ J ∈ components.attach,
        (w_of J.1 (F J.1 J.2) * (∏ i ∈ J.1, if F J.1 J.2 i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1)) =
      ∏ J ∈ components, ∑ M ∈ S_of J,
        (w_of J M * (∏ i ∈ J, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1)) := by
    exact (Finset.prod_sum components S_of (fun J M =>
      w_of J M * (∏ i ∈ J, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1))).symm
  rw [hprod_sum]
  have hprod_eval :
      ∏ J ∈ components, ∑ M ∈ S_of J,
        (w_of J M * (∏ i ∈ J, if M i = ∅ then ((2 : ℤ) ^ (scope i).card - 1) else -1)) =
      ∏ J ∈ components,
        if J ∈ trees ∧ T ∩ support J = exceptional ∩ support J then ((2 ^ widthGCD J - 1 : Nat) : ℤ) else 1 := by
    exact Finset.prod_congr rfl (fun J hJ => (hloc_spec J hJ).2)
  rw [hprod_eval, ← Finset.prod_filter]
  have hfilt_eq : components.filter (fun J => J ∈ trees ∧ T ∩ support J = exceptional ∩ support J) =
      trees.filter (fun J => T ∩ support J = exceptional ∩ support J) := by
    ext J
    simp only [Finset.mem_filter, trees]
    tauto
  rw [hfilt_eq, Nat.cast_prod]

private def splitTwo (m : Nat) : Nat × Nat :=
  if h : 0 < m ∧ m % 2 = 0 then
    let p := splitTwo (m / 2)
    (p.1 + 1, p.2)
  else (0, m)
termination_by m

private lemma splitTwo_spec : ∀ m : Nat, 0 < m →
    m = 2 ^ (splitTwo m).1 * (splitTwo m).2 ∧ (splitTwo m).2 % 2 = 1 ∧ 0 < (splitTwo m).2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    intro hm
    rw [splitTwo]
    by_cases h2 : m % 2 = 0
    · have hcond : 0 < m ∧ m % 2 = 0 := ⟨hm, h2⟩
      rw [dif_pos hcond]
      have hlt : m / 2 < m := Nat.div_lt_self hm (by omega)
      have hpos : 0 < m / 2 := by omega
      have ⟨heq, hodd, hpos'⟩ := ih (m / 2) hlt hpos
      refine ⟨?_, hodd, hpos'⟩
      dsimp only
      rw [pow_succ, mul_assoc, mul_comm 2, ← mul_assoc]
      omega
    · rw [dif_neg (fun hc => h2 hc.2)]
      exact ⟨by simp, by omega, hm⟩

private lemma card_mul_zero_mod {m a : Nat} (hm : 0 < m) :
    ((Finset.univ : Finset (Fin m)).filter (fun y => (a * y.val) % m = 0)).card = Nat.gcd m a := by
  let g := Nat.gcd m a
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left a hm
  have hg_dvd_m : g ∣ m := Nat.gcd_dvd_left m a
  have hg_dvd_a : g ∣ a := Nat.gcd_dvd_right m a
  let q := m / g
  have hmq : g * q = m := Nat.mul_div_cancel' hg_dvd_m
  have hcop : Nat.Coprime q (a / g) := by
    have := Nat.coprime_div_gcd_div_gcd hg_pos
    simpa [q, g] using this
  have hiff : ∀ y : Fin m, (a * y.val) % m = 0 ↔ q ∣ y.val := by
    intro y
    rw [← Nat.dvd_iff_mod_eq_zero]
    have ha_eq : g * (a / g) = a := Nat.mul_div_cancel' hg_dvd_a
    constructor
    · intro h
      have h1 : g * q ∣ g * ((a / g) * y.val) := by
        rw [hmq, ← mul_assoc, ha_eq]; exact h
      have h2 : q ∣ (a / g) * y.val := (mul_dvd_mul_iff_left (by omega : g ≠ 0)).mp h1
      exact hcop.dvd_of_dvd_mul_left h2
    · rintro ⟨k, hk⟩
      have h1 : g * q ∣ g * (a / g) * y.val := by
        rw [hk]; exact ⟨(a / g) * k, by ring⟩
      rwa [hmq, ha_eq] at h1
  have hq_pos : 0 < q := Nat.div_pos (Nat.le_of_dvd hm hg_dvd_m) hg_pos
  have hbij : ((Finset.univ : Finset (Fin m)).filter (fun y => (a * y.val) % m = 0)) =
      (Finset.univ : Finset (Fin g)).image (fun k => ⟨k.val * q, by
        have hk : k.val < g := k.isLt
        calc k.val * q < g * q := Nat.mul_lt_mul_of_pos_right hk hq_pos
          _ = m := hmq⟩) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hiff]
    constructor
    · rintro ⟨k, hk⟩
      have hklt : k < g := by
        have hlt : q * k < g * q := by rw [← hk, hmq]; exact y.isLt
        rw [mul_comm] at hlt
        exact lt_of_mul_lt_mul_right hlt (Nat.zero_le q)
      refine ⟨⟨k, hklt⟩, Fin.ext (by dsimp only; rw [hk, mul_comm])⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k.val, by dsimp only; rw [mul_comm]⟩
  rw [hbij, Finset.card_image_of_injective]
  · simp [g]
  · intro k₁ k₂ hEq
    have hv := congrArg Fin.val hEq
    dsimp only at hv
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hq_pos hv)

theorem main_proof : (∀ (n t : Nat) (scope : Fin t → Finset (Fin n)),
  (∀ i, (scope i).Nonempty) → (∀ j : Fin n, ∃ i, j ∈ scope i) →
  let Bits := Finset (Fin n)
  let sites := (Finset.univ : Finset (Fin n))
  let rows := (Finset.univ : Finset (Fin t))
  let choices := (Finset.univ : Finset (Fin t → Bits)).filter
    (fun R => ∀ i, R i ⊆ scope i)
  let closed := fun (J : Finset (Fin t)) => J.toList.all (fun i => rows.toList.all
    (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))
  let components := rows.powerset.filter (fun J => J.Nonempty ∧ closed J = true ∧
    ∀ K ∈ J.powerset, K.Nonempty → closed K = true → K = J)
  let support := fun (J : Finset (Fin t)) => J.biUnion scope
  let trees := components.filter (fun J =>
    J.sum (fun i => (scope i).card) + 1 = J.card + (support J).card)
  let widthGCD := fun (J : Finset (Fin t)) => J.gcd (fun i => (scope i).card)
  let exceptional := sites.filter (fun j => (rows.filter (fun i => j ∈ scope i)).card % 2 = 0)
  let divisor := fun (T : Bits) => (trees.filter
    (fun J => T ∩ support J = exceptional ∩ support J)).prod
    (fun J => (2 ^ widthGCD J - 1 : Nat))
  let cube := (Finset.univ : Finset Bits)
  let passes := fun (x : Bits) (p : Fin t → Bits) => rows.toList.all (fun i => decide (x ∩ scope i ≠ p i))
  let coeff := fun (f : Bits → Int) (T : Bits) =>
    cube.sum (fun x => (-1 : Int) ^ (x ∩ T).card * f x)
  (∀ f : Bits → Int,
    (∃ c : (Fin t → Bits) → Int, ∀ x, (choices.filter (fun p => passes x p = true)).sum c = f x) ↔
      ∀ T : Bits, (divisor T : Int) ∣ coeff f T) ∧
  (∀ m : Nat, 0 < m →
    ((Finset.univ : Finset (Bits → Fin m)).filter (fun d =>
      ∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum
        (fun x => (d x).val)) % m = 0)).card =
      cube.prod (fun T => Nat.gcd m (divisor T)))) := by
  intro n t scope hnonempty hcov Bits sites rows choices closed components support trees widthGCD
    exceptional divisor cube passes coeff

  let M_odd : Nat := ∏ i : Fin t, (2 ^ (scope i).card - 1)
  have hModd_odd : M_odd % 2 = 1 :=
    odd_prod_nat Finset.univ _ (fun i _ => odd_two_pow_sub_one (Finset.card_pos.mpr (hnonempty i)))
  have hModd_cast : (M_odd : ℤ) = ∏ i : Fin t, ((2 : ℤ) ^ (scope i).card - 1) := by
    dsimp only [M_odd]
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    have hge1 : 1 ≤ 2 ^ (scope i).card := Nat.one_le_two_pow
    zify [hge1]
  let Q_two : Nat := ∏ i : Fin t, 2 ^ (scope i).card
  have hQ_pow : Q_two = 2 ^ (∑ i : Fin t, (scope i).card) := by
    dsimp only [Q_two]; rw [Finset.prod_pow_eq_pow_sum]

  have hwalsh_choices : ∀ (c : (Fin t → Bits) → ℤ) (p : Fin t → Bits), p ∈ choices →
      (Q_two : ℤ) * c p =
      ∑ M ∈ choices, (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * (∏ i : Fin t, chi (M i) (p i)) := by
    intro c p hp
    have hp_sub : ∀ i, p i ⊆ scope i := (Finset.mem_filter.mp hp).2
    have hswap : ∑ M ∈ choices, (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * (∏ i : Fin t, chi (M i) (p i)) =
        ∑ q ∈ choices, c q * ∑ M ∈ choices, ∏ i : Fin t, chi (M i) (q i ∆ p i) := by
      have h1 : ∀ M ∈ choices,
          (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * (∏ i : Fin t, chi (M i) (p i)) =
          ∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i ∆ p i) := by
        intro M _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q _
        rw [mul_assoc, ← Finset.prod_mul_distrib]
        congr 1
        exact Finset.prod_congr rfl (fun i _ => (chi_symmDiff_right (M i) (q i) (p i)).symm)
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun q _ => (Finset.mul_sum _ _ _).symm)
    rw [hswap]
    have hinner : ∀ q ∈ choices,
        ∑ M ∈ choices, ∏ i : Fin t, chi (M i) (q i ∆ p i) =
        if q = p then (Q_two : ℤ) else 0 := by
      intro q hq
      have hq_sub : ∀ i, q i ⊆ scope i := (Finset.mem_filter.mp hq).2
      dsimp only [choices]
      rw [prod_filter_choices scope (fun i M_i => chi M_i (q i ∆ p i))]
      have hloc : ∀ i : Fin t,
          ∑ M_i ∈ (scope i).powerset, chi M_i (q i ∆ p i) =
          if q i = p i then (2 : ℤ) ^ (scope i).card else 0 := by
        intro i
        have hsub : q i ∆ p i ⊆ scope i := by
          intro j hj; rw [Finset.mem_symmDiff] at hj
          rcases hj with ⟨h1, _⟩ | ⟨h2, _⟩
          · exact hq_sub i h1
          · exact hp_sub i h2
        have hcomm : ∑ M_i ∈ (scope i).powerset, chi M_i (q i ∆ p i) =
            ∑ M_i ∈ (scope i).powerset, chi (q i ∆ p i) M_i :=
          Finset.sum_congr rfl (fun M_i _ => chi_comm M_i _)
        rw [hcomm, sum_chi_powerset (scope i) _ hsub]
        by_cases heq : q i = p i
        · rw [heq, symmDiff_self, Finset.bot_eq_empty]; simp
        · have hne : q i ∆ p i ≠ ∅ := fun h => heq (symmDiff_eq_bot.mp h)
          simp [heq, hne]
      simp_rw [hloc]
      by_cases hqp : q = p
      · subst hqp; simp only [ite_true]; push_cast [Q_two]; rfl
      · rw [if_neg hqp]
        have hex : ∃ i : Fin t, q i ≠ p i := by
          by_contra hall; apply hqp; funext i; by_contra h; exact hall ⟨i, h⟩
        rcases hex with ⟨i, hi⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [Finset.sum_congr rfl (fun q hq => by rw [hinner q hq])]
    rw [Finset.sum_eq_single p]
    · simp [mul_comm]
    · intro q _ hne; simp [hne]
    · intro hnot; exact absurd hp hnot

  have hwalsh_cube : ∀ (f : Bits → ℤ) (x : Bits),
      (2 : ℤ) ^ n * f x = ∑ T : Bits, coeff f T * chi T x := by
    intro f x
    have hcoeff : ∀ T : Bits, coeff f T = ∑ y : Bits, chi T y * f y := by
      intro T
      apply Finset.sum_congr rfl
      intro y _
      rw [chi_eq_neg_one_pow, Finset.inter_comm]
    simp_rw [hcoeff]
    have hswap : ∑ T : Bits, (∑ y : Bits, chi T y * f y) * chi T x =
        ∑ y : Bits, f y * ∑ T : Bits, chi (y ∆ x) T := by
      have h1 : ∀ T : Bits, (∑ y : Bits, chi T y * f y) * chi T x =
          ∑ y : Bits, f y * chi (y ∆ x) T := by
        intro T
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y _
        rw [chi_comm (y ∆ x) T, chi_symmDiff_right]
        ring
      simp_rw [h1]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun y _ => (Finset.mul_sum _ _ _).symm)
    rw [hswap]
    have hinner : ∀ y : Bits, ∑ T : Bits, chi (y ∆ x) T = if y = x then (2 : ℤ) ^ n else 0 := by
      intro y
      rw [sum_chi_univ, Fintype.card_fin]
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne : y ∆ x ≠ ∅ := fun h => hyx (symmDiff_eq_bot.mp h)
        simp [hyx, hne]
    simp_rw [hinner]
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro y _ hne; simp [hne]
    · intro hnot; exact absurd (Finset.mem_univ x) hnot
  constructor
  ·
    intro f
    constructor
    ·
      rintro ⟨c, hc⟩ T
      have hspecT := divisor_dvd_and_comb scope hnonempty hcov T
      have hQ_coeff : (Q_two : ℤ) * coeff f T =
          (2 : ℤ) ^ n * ∑ M ∈ choices.filter (fun M => xorAll M = T),
            (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * multOf scope M := by
        have hstep1 : (Q_two : ℤ) * coeff f T =
            ∑ x : Bits, chi T x * ∑ p ∈ choices.filter (fun p => passes x p = true), ((Q_two : ℤ) * c p) := by
          dsimp only [coeff]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [← hc x, chi_eq_neg_one_pow, Finset.inter_comm]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _; ring
        rw [hstep1]
        have hstep2 : ∀ x : Bits,
            ∑ p ∈ choices.filter (fun p => passes x p = true), ((Q_two : ℤ) * c p) =
            ∑ M ∈ choices, (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) *
              (multOf scope M * chi (xorAll M) x) := by
          intro x
          have hsub : ∑ p ∈ choices.filter (fun p => passes x p = true), ((Q_two : ℤ) * c p) =
              ∑ p ∈ choices.filter (fun p => passes x p = true),
                ∑ M ∈ choices, (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * (∏ i : Fin t, chi (M i) (p i)) :=
            Finset.sum_congr rfl (fun p hp => hwalsh_choices c p (Finset.mem_filter.mp hp).1)
          rw [hsub, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro M hM
          rw [← Finset.mul_sum]
          congr 1
          exact walsh_signing scope M (Finset.mem_filter.mp hM).2 x
        simp_rw [hstep2]
        have hswap : ∑ x : Bits, chi T x * ∑ M ∈ choices,
              (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * (multOf scope M * chi (xorAll M) x) =
            ∑ M ∈ choices, (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * multOf scope M *
              ∑ x : Bits, chi (T ∆ xorAll M) x := by
          have h1 : ∀ x : Bits,
              chi T x * ∑ M ∈ choices,
                (∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * (multOf scope M * chi (xorAll M) x) =
              ∑ M ∈ choices,
                ((∑ q ∈ choices, c q * ∏ i : Fin t, chi (M i) (q i)) * multOf scope M) * chi (T ∆ xorAll M) x := by
            intro x
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro M _
            rw [chi_symmDiff_left]; ring
          simp_rw [h1]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl (fun M _ => (Finset.mul_sum _ _ _).symm)
        rw [hswap]
        have hinner : ∀ M ∈ choices, ∑ x : Bits, chi (T ∆ xorAll M) x =
            if xorAll M = T then (2 : ℤ) ^ n else 0 := by
          intro M _
          rw [sum_chi_univ, Fintype.card_fin]
          by_cases hM : xorAll M = T
          · rw [hM]; simp
          · have hne : T ∆ xorAll M ≠ ∅ := fun h => hM (symmDiff_eq_bot.mp h).symm
            simp [hM, hne]
        rw [Finset.sum_congr rfl (fun M hM => by rw [hinner M hM])]
        rw [Finset.mul_sum]
        conv_rhs => rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro M _
        by_cases hM : xorAll M = T <;> simp [hM, mul_comm]
      have hdvd_Q : (divisor T : ℤ) ∣ (Q_two : ℤ) * coeff f T := by
        rw [hQ_coeff]
        apply dvd_mul_of_dvd_right
        apply Finset.dvd_sum
        intro M hM
        have ⟨hMch, hMxor⟩ := Finset.mem_filter.mp hM
        exact dvd_mul_of_dvd_right (hspecT.2.1 M hMch hMxor) _
      have hcop : Nat.Coprime (divisor T) Q_two := by
        rw [hQ_pow]; exact (coprime_two_pow_odd hspecT.1).symm
      exact int_dvd_of_coprime_mul hcop hdvd_Q
    ·
      intro hdvd

      have hex_T : ∀ T : Bits, ∃ cT : (Fin t → Bits) → ℤ,
          ∀ x : Bits, (choices.filter (fun p => passes x p = true)).sum cT = coeff f T * chi T x := by
        intro T
        rcases (divisor_dvd_and_comb scope hnonempty hcov T).2.2 with ⟨α, hα⟩
        rcases hdvd T with ⟨kT, hkT⟩
        refine ⟨fun p => kT * ∑ M ∈ choices.filter (fun M => xorAll M = T), α M * (∏ i : Fin t, chi (M i) (p i)), ?_⟩
        intro x
        rw [← Finset.mul_sum, Finset.sum_comm]
        have hinner : ∑ M ∈ choices.filter (fun M => xorAll M = T),
            ∑ p ∈ choices.filter (fun p => passes x p = true), α M * (∏ i : Fin t, chi (M i) (p i)) =
            (divisor T : ℤ) * chi T x := by
          have h1 : ∀ M ∈ choices.filter (fun M => xorAll M = T),
              ∑ p ∈ choices.filter (fun p => passes x p = true), α M * (∏ i : Fin t, chi (M i) (p i)) =
              (α M * multOf scope M) * chi T x := by
            intro M hM
            have ⟨hMch, hMxor⟩ := Finset.mem_filter.mp hM
            rw [← Finset.mul_sum, walsh_signing scope M (Finset.mem_filter.mp hMch).2 x, hMxor]
            unfold multOf; ring
          rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, hα]
        rw [hinner, hkT]; ring
      let cEven : (Fin t → Bits) → ℤ := fun p => ∑ T : Bits, Classical.choose (hex_T T) p
      have hcEven : ∀ x : Bits, (choices.filter (fun p => passes x p = true)).sum cEven = (2 : ℤ) ^ n * f x := by
        intro x
        dsimp only [cEven]
        rw [Finset.sum_comm]
        have h1 : ∀ T : Bits, (choices.filter (fun p => passes x p = true)).sum (Classical.choose (hex_T T)) =
            coeff f T * chi T x := fun T => Classical.choose_spec (hex_T T) x
        rw [Finset.sum_congr rfl (fun T _ => h1 T), ← hwalsh_cube f x]

      let cOdd : (Fin t → Bits) → ℤ := fun p =>
        ∑ z : Bits, f z * ∏ i : Fin t, if p i = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1
      have hcOdd : ∀ x : Bits, (choices.filter (fun p => passes x p = true)).sum cOdd = (M_odd : ℤ) * f x := by
        intro x
        dsimp only [cOdd]
        rw [Finset.sum_comm]
        have h1 : ∀ z : Bits,
            ∑ p ∈ choices.filter (fun p => passes x p = true),
              f z * ∏ i : Fin t, (if p i = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1) =
            if x = z then f z * (M_odd : ℤ) else 0 := by
          intro z
          rw [← Finset.mul_sum, local_point_indicator scope hcov z x, ← hModd_cast]
          by_cases hxz : x = z <;> simp [hxz]
        simp_rw [h1]
        rw [Finset.sum_eq_single x]
        · simp [mul_comm]
        · intro z _ hne; simp [Ne.symm hne]
        · intro hnot; exact absurd (Finset.mem_univ x) hnot

      have hcop : Nat.Coprime (2 ^ n) M_odd := coprime_two_pow_odd hModd_odd
      have hbez : (1 : ℤ) = ((2 ^ n : Nat) : ℤ) * Nat.gcdA (2 ^ n) M_odd + (M_odd : ℤ) * Nat.gcdB (2 ^ n) M_odd := by
        have := Nat.gcd_eq_gcd_ab (2 ^ n) M_odd
        rw [hcop.gcd_eq_one] at this; exact this
      let u := Nat.gcdA (2 ^ n) M_odd
      let v := Nat.gcdB (2 ^ n) M_odd
      refine ⟨fun p => u * cEven p + v * cOdd p, ?_⟩
      intro x
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcEven x, hcOdd x]
      have hbez' : u * (2 : ℤ) ^ n + v * (M_odd : ℤ) = 1 := by
        push_cast at hbez; linarith
      calc u * ((2 : ℤ) ^ n * f x) + v * ((M_odd : ℤ) * f x)
          = (u * (2 : ℤ) ^ n + v * (M_odd : ℤ)) * f x := by ring
        _ = f x := by rw [hbez', one_mul]
  ·
    intro m hm
    let countMod : (k : Nat) → Nat := fun k =>
      ((Finset.univ : Finset (Bits → Fin k)).filter (fun d =>
        ∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum
          (fun x => (d x).val)) % k = 0)).card

    have hcrt : ∀ m₁ m₂ : Nat, 0 < m₁ → 0 < m₂ → Nat.Coprime m₁ m₂ →
        countMod (m₁ * m₂) = countMod m₁ * countMod m₂ := by
      intro m₁ m₂ hm₁ hm₂ hcop
      have hprod_card : countMod m₁ * countMod m₂ =
          (((Finset.univ : Finset (Bits → Fin m₁)).filter (fun d =>
              ∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val)) % m₁ = 0)) ×ˢ
           ((Finset.univ : Finset (Bits → Fin m₂)).filter (fun d =>
              ∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val)) % m₂ = 0))).card :=
        (Finset.card_product _ _).symm
      rw [hprod_card]
      let toPair : (Bits → Fin (m₁ * m₂)) → (Bits → Fin m₁) × (Bits → Fin m₂) := fun d =>
        (fun x => ⟨(d x).val % m₁, Nat.mod_lt _ hm₁⟩, fun x => ⟨(d x).val % m₂, Nat.mod_lt _ hm₂⟩)

      let eCRT : ZMod (m₁ * m₂) ≃+* ZMod m₁ × ZMod m₂ := ZMod.chineseRemainder hcop
      haveI : NeZero m₁ := ⟨by omega⟩
      haveI : NeZero m₂ := ⟨by omega⟩
      haveI : NeZero (m₁ * m₂) := ⟨by positivity⟩
      let fromPair : (Bits → Fin m₁) × (Bits → Fin m₂) → (Bits → Fin (m₁ * m₂)) := fun P x =>
        ⟨(eCRT.symm ((P.1 x).val, (P.2 x).val)).val, ZMod.val_lt _⟩
      have hmod_sum : ∀ (k : Nat) (f : Bits → Nat) (S : Finset Bits),
          (S.sum (fun x => f x % k)) % k = (S.sum f) % k := by
        intro k f S
        induction S using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mod, Nat.mod_mod, ih, ← Nat.add_mod]
      refine Finset.card_bij (fun d _ => toPair d) ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        · intro p hp
          have h := hd p hp
          rw [hmod_sum]
          exact Nat.dvd_iff_mod_eq_zero.mp (dvd_trans (dvd_mul_right m₁ m₂) (Nat.dvd_iff_mod_eq_zero.mpr h))
        · intro p hp
          have h := hd p hp
          rw [hmod_sum]
          exact Nat.dvd_iff_mod_eq_zero.mp (dvd_trans (dvd_mul_left m₂ m₁) (Nat.dvd_iff_mod_eq_zero.mpr h))
      · intro d₁ _ d₂ _ hEq
        funext x
        have h1 : (d₁ x).val % m₁ = (d₂ x).val % m₁ := congrArg (fun P => (P.1 x).val) hEq
        have h2 : (d₁ x).val % m₂ = (d₂ x).val % m₂ := congrArg (fun P => (P.2 x).val) hEq
        have hz1 : ((d₁ x).val : ZMod m₁) = ((d₂ x).val : ZMod m₁) := by
          rw [ZMod.natCast_eq_natCast_iff]; exact h1
        have hz2 : ((d₁ x).val : ZMod m₂) = ((d₂ x).val : ZMod m₂) := by
          rw [ZMod.natCast_eq_natCast_iff]; exact h2
        have hze : eCRT ((d₁ x).val : ZMod (m₁ * m₂)) = eCRT ((d₂ x).val : ZMod (m₁ * m₂)) := by
          ext <;> simp [eCRT, hz1, hz2]
        have hzm : ((d₁ x).val : ZMod (m₁ * m₂)) = ((d₂ x).val : ZMod (m₁ * m₂)) := eCRT.injective hze
        have hmod : (d₁ x).val % (m₁ * m₂) = (d₂ x).val % (m₁ * m₂) :=
          (ZMod.natCast_eq_natCast_iff _ _ _).mp hzm
        rw [Nat.mod_eq_of_lt (d₁ x).isLt, Nat.mod_eq_of_lt (d₂ x).isLt] at hmod
        exact Fin.ext hmod
      · intro P hP
        rcases Finset.mem_product.mp hP with ⟨hP1, hP2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP1 hP2
        have hcoord : ∀ x : Bits, (fromPair P x).val % m₁ = (P.1 x).val ∧
            (fromPair P x).val % m₂ = (P.2 x).val := by
          intro x
          let z := eCRT.symm ((P.1 x).val, (P.2 x).val)
          have heq_pair := eCRT.apply_symm_apply (((P.1 x).val : ZMod m₁), ((P.2 x).val : ZMod m₂))
          have hmap : eCRT z = ((z.val : ZMod m₁), (z.val : ZMod m₂)) := by
            have h := map_natCast eCRT z.val
            rwa [ZMod.natCast_zmod_val] at h
          have hz1 : (z.val : ZMod m₁) = ((P.1 x).val : ZMod m₁) :=
            (congrArg Prod.fst hmap).symm.trans (congrArg Prod.fst heq_pair)
          have hz2 : (z.val : ZMod m₂) = ((P.2 x).val : ZMod m₂) :=
            (congrArg Prod.snd hmap).symm.trans (congrArg Prod.snd heq_pair)
          have hm1' : z.val % m₁ = (P.1 x).val % m₁ := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz1
          have hm2' : z.val % m₂ = (P.2 x).val % m₂ := (ZMod.natCast_eq_natCast_iff _ _ _).mp hz2
          rw [Nat.mod_eq_of_lt (P.1 x).isLt] at hm1'
          rw [Nat.mod_eq_of_lt (P.2 x).isLt] at hm2'
          exact ⟨hm1', hm2'⟩
        refine ⟨fromPair P, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
        · intro p hp
          have hd1 : m₁ ∣ (cube.filter (fun x => passes x p = true)).sum (fun x => (fromPair P x).val) := by
            rw [Nat.dvd_iff_mod_eq_zero, ← hmod_sum]
            simpa [fun x => (hcoord x).1] using hP1 p hp
          have hd2 : m₂ ∣ (cube.filter (fun x => passes x p = true)).sum (fun x => (fromPair P x).val) := by
            rw [Nat.dvd_iff_mod_eq_zero, ← hmod_sum]
            simpa [fun x => (hcoord x).2] using hP2 p hp
          exact Nat.dvd_iff_mod_eq_zero.mp (hcop.mul_dvd_of_dvd_of_dvd hd1 hd2)
        · ext x
          · exact (hcoord x).1
          · exact (hcoord x).2

    have hpow2 : ∀ a : Nat, countMod (2 ^ a) = 1 := by
      intro a
      have hpos : 0 < 2 ^ a := Nat.two_pow_pos a
      have hset : ((Finset.univ : Finset (Bits → Fin (2 ^ a))).filter (fun d =>
          ∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val)) % 2 ^ a = 0)) =
          {fun _ => ⟨0, hpos⟩} := by
        ext d
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hd
          funext z
          let c_z : (Fin t → Bits) → ℤ := fun p =>
            ∏ i : Fin t, if p i = z ∩ scope i then -((2 : ℤ) ^ (scope i).card - 2) else 1
          have hdiv_z : ((2 ^ a : Nat) : ℤ) ∣ (M_odd : ℤ) * ((d z).val : ℤ) := by
            have hsum_eq : ∑ p ∈ choices, c_z p *
                (((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val) : Nat) : ℤ) =
                (M_odd : ℤ) * ((d z).val : ℤ) := by
              have h1 : ∑ p ∈ choices, c_z p *
                  (((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val) : Nat) : ℤ) =
                  ∑ x : Bits, ((d x).val : ℤ) * ∑ p ∈ choices.filter (fun p => passes x p = true), c_z p := by
                have ha : ∀ p ∈ choices,
                    c_z p * (((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val) : Nat) : ℤ) =
                    ∑ x : Bits, if passes x p = true then c_z p * ((d x).val : ℤ) else 0 := by
                  intro p _
                  rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_filter]
                rw [Finset.sum_congr rfl ha, Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro x _
                conv_rhs => rw [Finset.sum_filter, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p _; by_cases hp : passes x p = true <;> simp [hp, mul_comm]
              rw [h1]
              have h2 : ∀ x : Bits,
                  ((d x).val : ℤ) * ∑ p ∈ choices.filter (fun p => passes x p = true), c_z p =
                  if x = z then ((d x).val : ℤ) * (M_odd : ℤ) else 0 := by
                intro x
                rw [local_point_indicator scope hcov z x, ← hModd_cast]
                by_cases hxz : x = z <;> simp [hxz]
              simp_rw [h2]
              rw [Finset.sum_eq_single z]
              · simp [mul_comm]
              · intro x _ hne; simp [hne]
              · intro hnot; exact absurd (Finset.mem_univ z) hnot
            rw [← hsum_eq]
            apply Finset.dvd_sum
            intro p hp
            exact dvd_mul_of_dvd_right (Int.ofNat_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr (hd p hp))) _
          have hcop : Nat.Coprime (2 ^ a) M_odd := coprime_two_pow_odd hModd_odd
          have hdiv_d : ((2 ^ a : Nat) : ℤ) ∣ ((d z).val : ℤ) :=
            int_dvd_of_coprime_mul hcop hdiv_z
          have hdiv_nat : 2 ^ a ∣ (d z).val := Int.ofNat_dvd.mp hdiv_d
          have h0 : (d z).val = 0 := Nat.eq_zero_of_dvd_of_lt hdiv_nat (d z).isLt
          exact Fin.ext h0
        · rintro rfl p _; simp
      dsimp only [countMod]
      rw [hset]; simp

    have hodd_case : ∀ k : Nat, 0 < k → k % 2 = 1 →
        countMod k = cube.prod (fun T => Nat.gcd k (divisor T)) := by
      intro k hk_pos hk_odd
      haveI : NeZero k := ⟨by omega⟩

      let W : (Bits → ZMod k) → (Bits → ZMod k) := fun d T =>
        ∑ x : Bits, (chi T x : ZMod k) * d x
      have h2_unit : IsUnit ((2 : ZMod k)) := by
        have h : IsUnit ((2 : Nat) : ZMod k) :=
          (ZMod.isUnit_iff_coprime 2 k).mpr (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hk_odd))
        simpa using h
      have h2n_unit : IsUnit ((2 : ZMod k) ^ n) := h2_unit.pow n
      have hQ_unit : IsUnit ((Q_two : ZMod k)) := by
        rw [hQ_pow, Nat.cast_pow, Nat.cast_ofNat]; exact h2_unit.pow _
      have hWW : ∀ d : Bits → ZMod k, ∀ x : Bits, W (W d) x = (2 : ZMod k) ^ n * d x := by
        intro d x
        dsimp only [W]
        have hswap : ∑ T : Bits, (chi x T : ZMod k) * ∑ y : Bits, (chi T y : ZMod k) * d y =
            ∑ y : Bits, d y * ((∑ T : Bits, chi (y ∆ x) T : ℤ) : ZMod k) := by
          have h1 : ∀ T : Bits, (chi x T : ZMod k) * ∑ y : Bits, (chi T y : ZMod k) * d y =
              ∑ y : Bits, d y * (chi (y ∆ x) T : ZMod k) := by
            intro T
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            rw [chi_comm (y ∆ x) T, chi_symmDiff_right, chi_comm x T, Int.cast_mul]
            ring
          simp_rw [h1]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Int.cast_sum, Finset.mul_sum]
        rw [hswap]
        have hinner : ∀ y : Bits, ((∑ T : Bits, chi (y ∆ x) T : ℤ) : ZMod k) =
            if y = x then (2 : ZMod k) ^ n else 0 := by
          intro y
          rw [sum_chi_univ, Fintype.card_fin]
          by_cases hyx : y = x
          · subst hyx; simp
          · have hne : y ∆ x ≠ ∅ := fun h => hyx (symmDiff_eq_bot.mp h)
            simp [hyx, hne]
        simp_rw [hinner]
        rw [Finset.sum_eq_single x]
        · simp [mul_comm]
        · intro y _ hne; simp [hne]
        · intro hnot; exact absurd (Finset.mem_univ x) hnot
      have hW_bij : Function.Bijective W := by
        refine ⟨?_, ?_⟩
        · intro d₁ d₂ hEq
          funext x
          have h := congrFun (congrArg W hEq) x
          rw [hWW d₁ x, hWW d₂ x] at h
          exact h2n_unit.mul_left_cancel h
        · intro g
          rcases h2n_unit with ⟨u, hu⟩
          refine ⟨fun x => (u⁻¹ : (ZMod k)ˣ) * W g x, ?_⟩
          funext T
          have hlin : W (fun x => (u⁻¹ : (ZMod k)ˣ) * W g x) T = (u⁻¹ : (ZMod k)ˣ) * W (W g) T := by
            dsimp only [W]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro x _; ring
          rw [hlin, hWW g T, ← hu, ← mul_assoc, Units.inv_mul, one_mul]

      have hcond_iff : ∀ d : Bits → ZMod k,
          (∀ p ∈ choices, ∑ x ∈ cube.filter (fun x => passes x p = true), d x = 0) ↔
          (∀ T : Bits, (divisor T : ZMod k) * W d T = 0) := by
        intro d
        have hstep1 : (∀ p ∈ choices, ∑ x ∈ cube.filter (fun x => passes x p = true), d x = 0) ↔
            (∀ M ∈ choices, (multOf scope M : ZMod k) * W d (xorAll M) = 0) := by
          have hmul : ∀ M ∈ choices,
              ∑ p ∈ choices, (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                (∑ x ∈ cube.filter (fun x => passes x p = true), d x) =
              (multOf scope M : ZMod k) * W d (xorAll M) := by
            intro M hM
            have h1 : ∑ p ∈ choices, (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                (∑ x ∈ cube.filter (fun x => passes x p = true), d x) =
                ∑ x : Bits, d x * ((∑ p ∈ choices.filter (fun p => passes x p = true),
                  ∏ i : Fin t, chi (M i) (p i) : ℤ) : ZMod k) := by
              have ha : ∀ p ∈ choices,
                  (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                    (∑ x ∈ cube.filter (fun x => passes x p = true), d x) =
                  ∑ x : Bits, if passes x p = true then (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) * d x else 0 := by
                intro p _; rw [Finset.mul_sum, Finset.sum_filter]
              rw [Finset.sum_congr rfl ha, Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro x _
              rw [Int.cast_sum]
              conv_rhs => rw [Finset.sum_filter, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              by_cases hp : passes x p = true <;> simp [hp, Int.cast_prod, mul_comm]
            rw [h1]
            dsimp only [W]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            rw [walsh_signing scope M (Finset.mem_filter.mp hM).2 x, Int.cast_mul]
            unfold multOf; ring
          constructor
          · intro h M hM
            rw [← hmul M hM]
            exact Finset.sum_eq_zero (fun p hp => by rw [h p hp, mul_zero])
          · intro h p hp
            let A : (Fin t → Bits) → ZMod k := fun q => ∑ x ∈ cube.filter (fun x => passes x q = true), d x

            have hinv : (Q_two : ZMod k) * A p =
                ∑ M ∈ choices, (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                  (∑ q ∈ choices, (∏ i : Fin t, (chi (M i) (q i) : ZMod k)) * A q) := by
              have hswap : ∑ M ∈ choices, (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                  (∑ q ∈ choices, (∏ i : Fin t, (chi (M i) (q i) : ZMod k)) * A q) =
                  ∑ q ∈ choices, A q * ((∑ M ∈ choices, ∏ i : Fin t, chi (M i) (q i ∆ p i) : ℤ) : ZMod k) := by
                have h1 : ∀ M ∈ choices,
                    (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                      (∑ q ∈ choices, (∏ i : Fin t, (chi (M i) (q i) : ZMod k)) * A q) =
                    ∑ q ∈ choices, A q * ((∏ i : Fin t, chi (M i) (q i ∆ p i) : ℤ) : ZMod k) := by
                  intro M _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro q _
                  rw [Int.cast_prod]
                  have hp_eq : (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) *
                      (∏ i : Fin t, (chi (M i) (q i) : ZMod k)) =
                      ∏ i : Fin t, (chi (M i) (q i ∆ p i) : ZMod k) := by
                    rw [← Finset.prod_mul_distrib]
                    apply Finset.prod_congr rfl
                    intro i _; rw [chi_symmDiff_right, Int.cast_mul, mul_comm]
                  calc (∏ i : Fin t, (chi (M i) (p i) : ZMod k)) * ((∏ i : Fin t, (chi (M i) (q i) : ZMod k)) * A q)
                      = A q * ((∏ i : Fin t, (chi (M i) (p i) : ZMod k)) * (∏ i : Fin t, (chi (M i) (q i) : ZMod k))) := by ring
                    _ = A q * ∏ i : Fin t, (chi (M i) (q i ∆ p i) : ZMod k) := by rw [hp_eq]
                rw [Finset.sum_congr rfl h1, Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro q _
                rw [Int.cast_sum, Finset.mul_sum]
              rw [hswap]
              have hp_sub : ∀ i, p i ⊆ scope i := (Finset.mem_filter.mp hp).2
              have hinner : ∀ q ∈ choices,
                  ((∑ M ∈ choices, ∏ i : Fin t, chi (M i) (q i ∆ p i) : ℤ) : ZMod k) =
                  if q = p then (Q_two : ZMod k) else 0 := by
                intro q hq
                have hq_sub : ∀ i, q i ⊆ scope i := (Finset.mem_filter.mp hq).2
                have hz : ∑ M ∈ choices, ∏ i : Fin t, chi (M i) (q i ∆ p i) =
                    if q = p then (Q_two : ℤ) else 0 := by
                  dsimp only [choices]
                  rw [prod_filter_choices scope (fun i M_i => chi M_i (q i ∆ p i))]
                  have hloc : ∀ i : Fin t,
                      ∑ M_i ∈ (scope i).powerset, chi M_i (q i ∆ p i) =
                      if q i = p i then (2 : ℤ) ^ (scope i).card else 0 := by
                    intro i
                    have hsub : q i ∆ p i ⊆ scope i := by
                      intro j hj; rw [Finset.mem_symmDiff] at hj
                      rcases hj with ⟨h1, _⟩ | ⟨h2, _⟩
                      · exact hq_sub i h1
                      · exact hp_sub i h2
                    have hcomm : ∑ M_i ∈ (scope i).powerset, chi M_i (q i ∆ p i) =
                        ∑ M_i ∈ (scope i).powerset, chi (q i ∆ p i) M_i :=
                      Finset.sum_congr rfl (fun M_i _ => chi_comm M_i _)
                    rw [hcomm, sum_chi_powerset (scope i) _ hsub]
                    by_cases heq : q i = p i
                    · rw [heq, symmDiff_self, Finset.bot_eq_empty]; simp
                    · have hne : q i ∆ p i ≠ ∅ := fun h => heq (symmDiff_eq_bot.mp h)
                      simp [heq, hne]
                  simp_rw [hloc]
                  by_cases hqp : q = p
                  · subst hqp; simp only [ite_true]; push_cast [Q_two]; rfl
                  · rw [if_neg hqp]
                    have hex : ∃ i : Fin t, q i ≠ p i := by
                      by_contra hall; apply hqp; funext i; by_contra h; exact hall ⟨i, h⟩
                    rcases hex with ⟨i, hi⟩
                    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
                rw [hz]
                by_cases hqp : q = p <;> simp [hqp]
              rw [Finset.sum_congr rfl (fun q hq => by rw [hinner q hq])]
              rw [Finset.sum_eq_single p]
              · simp [mul_comm]
              · intro q _ hne; simp [hne]
              · intro hnot; exact absurd hp hnot
            have h0 : (Q_two : ZMod k) * A p = 0 := by
              rw [hinv]
              apply Finset.sum_eq_zero
              intro M hM
              rw [hmul M hM, h M hM, mul_zero]
            exact hQ_unit.mul_left_cancel (by simpa using h0)
        rw [hstep1]
        constructor
        · intro h M_T
          rcases (divisor_dvd_and_comb scope hnonempty hcov M_T).2.2 with ⟨α, hα⟩
          have hsum : ∑ M ∈ choices.filter (fun M => xorAll M = M_T),
              (α M : ZMod k) * ((multOf scope M : ZMod k) * W d (xorAll M)) =
              (divisor M_T : ZMod k) * W d M_T := by
            have h1 : ∑ M ∈ choices.filter (fun M => xorAll M = M_T),
                (α M : ZMod k) * ((multOf scope M : ZMod k) * W d (xorAll M)) =
                ((∑ M ∈ choices.filter (fun M => xorAll M = M_T), α M * multOf scope M : ℤ) : ZMod k) * W d M_T := by
              rw [Int.cast_sum, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro M hM
              rw [(Finset.mem_filter.mp hM).2, Int.cast_mul]; ring
            rw [h1, hα, Int.cast_natCast]
          rw [← hsum]
          apply Finset.sum_eq_zero
          intro M hM
          rw [h M (Finset.mem_filter.mp hM).1, mul_zero]
        · intro h M hM
          rcases (divisor_dvd_and_comb scope hnonempty hcov (xorAll M)).2.1 M hM rfl with ⟨q, hq⟩
          rw [hq, Int.cast_mul, Int.cast_natCast]
          calc ((divisor (xorAll M) : ZMod k) * (q : ZMod k)) * W d (xorAll M)
              = (q : ZMod k) * ((divisor (xorAll M) : ZMod k) * W d (xorAll M)) := by ring
            _ = 0 := by rw [h (xorAll M), mul_zero]

      let toZ : (Bits → Fin k) → (Bits → ZMod k) := fun d x => ((d x).val : ZMod k)
      have htoZ_bij : Function.Bijective toZ := by
        refine ⟨?_, ?_⟩
        · intro d₁ d₂ hEq
          funext x
          have h : (d₁ x).val % k = (d₂ x).val % k :=
            (ZMod.natCast_eq_natCast_iff _ _ _).mp (congrFun hEq x)
          rw [Nat.mod_eq_of_lt (d₁ x).isLt, Nat.mod_eq_of_lt (d₂ x).isLt] at h
          exact Fin.ext h
        · intro g
          refine ⟨fun x => ⟨(g x).val, ZMod.val_lt _⟩, ?_⟩
          funext x; simp [toZ]
      have htoZ_cond : ∀ d : Bits → Fin k,
          (∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum (fun x => (d x).val)) % k = 0) ↔
          (∀ p ∈ choices, ∑ x ∈ cube.filter (fun x => passes x p = true), toZ d x = 0) := by
        intro d
        apply forall₂_congr
        intro p _
        rw [← Nat.cast_sum]
        exact (ZMod.natCast_eq_zero_iff _ _).trans Nat.dvd_iff_mod_eq_zero |>.symm

      let target : Bits → Finset (Fin k) := fun T =>
        (Finset.univ : Finset (Fin k)).filter (fun y => (divisor T * y.val) % k = 0)
      have hcard_target : (Fintype.piFinset target).card = cube.prod (fun T => Nat.gcd k (divisor T)) := by
        rw [Fintype.card_piFinset]
        exact Finset.prod_congr rfl (fun T _ => card_mul_zero_mod hk_pos)
      rw [← hcard_target]
      let phi : (Bits → Fin k) → (Bits → Fin k) := fun d T => ⟨(W (toZ d) T).val, ZMod.val_lt _⟩
      have hphi_bij : Function.Bijective phi := by
        have h1 : Function.Bijective (W ∘ toZ) := hW_bij.comp htoZ_bij
        refine ⟨?_, ?_⟩
        · intro d₁ d₂ hEq
          apply h1.1
          funext T
          have hv := congrArg Fin.val (congrFun hEq T)
          exact ZMod.val_injective k hv
        · intro g
          rcases h1.2 (fun T => ((g T).val : ZMod k)) with ⟨d, hd⟩
          refine ⟨d, ?_⟩
          funext T
          have hT : W (toZ d) T = ((g T).val : ZMod k) := congrFun hd T
          have hv : (W (toZ d) T).val = (g T).val := by
            rw [hT, ZMod.val_natCast, Nat.mod_eq_of_lt (g T).isLt]
          exact Fin.ext hv
      refine Finset.card_bij (fun d _ => phi d) ?_ ?_ ?_
      · intro d hd
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
        have hdZ := (hcond_iff (toZ d)).mp ((htoZ_cond d).mp hd)
        rw [Fintype.mem_piFinset]
        intro T
        simp only [target, Finset.mem_filter, Finset.mem_univ, true_and, phi]
        have hT := hdZ T
        have hcast : ((divisor T * (W (toZ d) T).val : Nat) : ZMod k) = 0 := by
          rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact hT
        exact Nat.dvd_iff_mod_eq_zero.mp ((ZMod.natCast_eq_zero_iff _ _).mp hcast)
      · intro d₁ _ d₂ _ hEq; exact hphi_bij.1 hEq
      · intro g hg
        rw [Fintype.mem_piFinset] at hg
        rcases hphi_bij.2 g with ⟨d, rfl⟩
        refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        rw [htoZ_cond d, hcond_iff (toZ d)]
        intro T
        have hT := (Finset.mem_filter.mp (hg T)).2
        have hcast : ((divisor T * (W (toZ d) T).val : Nat) : ZMod k) = 0 :=
          (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_iff_mod_eq_zero.mpr hT)
        simpa [Nat.cast_mul, ZMod.natCast_zmod_val] using hcast

    have ⟨hm_eq, hk_odd, hk_pos⟩ := splitTwo_spec m hm
    let a := (splitTwo m).1
    let k := (splitTwo m).2
    have hcop : Nat.Coprime (2 ^ a) k := coprime_two_pow_odd hk_odd
    change countMod m = cube.prod (fun T => Nat.gcd m (divisor T))
    rw [hm_eq, hcrt (2 ^ a) k (Nat.two_pow_pos a) hk_pos hcop, hpow2 a, one_mul, hodd_case k hk_pos hk_odd]
    apply Finset.prod_congr rfl
    intro T _
    have hdiv_odd := (divisor_dvd_and_comb scope hnonempty hcov T).1
    have hcop_T : Nat.Coprime (2 ^ a) (divisor T) := coprime_two_pow_odd hdiv_odd
    exact (hcop_T.gcd_mul_left_cancel k).symm

end PEqualNP.Outside.L_lib_1146

theorem PEqualNP.Outside.L_lib_1146 : (∀ (n t : Nat) (scope : Fin t → Finset (Fin n)),
  (∀ i, (scope i).Nonempty) → (∀ j : Fin n, ∃ i, j ∈ scope i) →
  let Bits := Finset (Fin n)
  let sites := (Finset.univ : Finset (Fin n))
  let rows := (Finset.univ : Finset (Fin t))
  let choices := (Finset.univ : Finset (Fin t → Bits)).filter
    (fun R => ∀ i, R i ⊆ scope i)
  let closed := fun (J : Finset (Fin t)) => J.toList.all (fun i => rows.toList.all
    (fun h => !(decide (scope i ∩ scope h).Nonempty) || decide (h ∈ J)))
  let components := rows.powerset.filter (fun J => J.Nonempty ∧ closed J = true ∧
    ∀ K ∈ J.powerset, K.Nonempty → closed K = true → K = J)
  let support := fun (J : Finset (Fin t)) => J.biUnion scope
  let trees := components.filter (fun J =>
    J.sum (fun i => (scope i).card) + 1 = J.card + (support J).card)
  let widthGCD := fun (J : Finset (Fin t)) => J.gcd (fun i => (scope i).card)
  let exceptional := sites.filter (fun j => (rows.filter (fun i => j ∈ scope i)).card % 2 = 0)
  let divisor := fun (T : Bits) => (trees.filter
    (fun J => T ∩ support J = exceptional ∩ support J)).prod
    (fun J => (2 ^ widthGCD J - 1 : Nat))
  let cube := (Finset.univ : Finset Bits)
  let passes := fun (x : Bits) (p : Fin t → Bits) => rows.toList.all (fun i => decide (x ∩ scope i ≠ p i))
  let coeff := fun (f : Bits → Int) (T : Bits) =>
    cube.sum (fun x => (-1 : Int) ^ (x ∩ T).card * f x)
  (∀ f : Bits → Int,
    (∃ c : (Fin t → Bits) → Int, ∀ x, (choices.filter (fun p => passes x p = true)).sum c = f x) ↔
      ∀ T : Bits, (divisor T : Int) ∣ coeff f T) ∧
  (∀ m : Nat, 0 < m →
    ((Finset.univ : Finset (Bits → Fin m)).filter (fun d =>
      ∀ p ∈ choices, ((cube.filter (fun x => passes x p = true)).sum
        (fun x => (d x).val)) % m = 0)).card =
      cube.prod (fun T => Nat.gcd m (divisor T)))) := by
  exact PEqualNP.Outside.L_lib_1146.main_proof
