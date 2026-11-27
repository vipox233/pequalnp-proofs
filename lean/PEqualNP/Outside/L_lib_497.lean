import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_497

open MvPolynomial PEqualNP.ProofComplexity

theorem degX {ι : Type} (n : ℕ) (T : Finset ι) (f : ι → Fin n) :
    (∏ i ∈ T, (X (f i) : MvPolynomial (Fin n) (ZMod 2))).totalDegree ≤ T.card := by
  refine (totalDegree_finsetProd T _).trans ?_
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i _
  rw [totalDegree_X]

theorem degLit (n : ℕ) (l : Fin n × Bool) :
    (if l.2 = true then 1 + X l.1 else X l.1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 1 := by
  split_ifs
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    exact max_le (Nat.zero_le 1) (le_refl 1)
  · rw [totalDegree_X]

theorem degClause (n : ℕ) (C : Clause (Fin n)) : (clausePoly C).totalDegree ≤ C.card := by
  unfold clausePoly
  refine (totalDegree_finsetProd C _).trans ?_
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun l _ => degLit n l)

theorem split (n : ℕ) (C : Clause (Fin n)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), (q = 0 ∨ q.totalDegree < C.card) ∧
      clausePoly C = (∏ l ∈ C, X l.1) + q := by
  unfold clausePoly
  induction C using Finset.induction_on with
  | empty => exact ⟨0, Or.inl rfl, by simp⟩
  | insert a S ha ih =>
    obtain ⟨q, hq, he⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, he, Finset.card_insert_of_notMem ha]
    have hM : (∏ l ∈ S, (X l.1 : MvPolynomial (Fin n) (ZMod 2))).totalDegree ≤ S.card :=
      degX n S Prod.fst
    have hX : (X a.1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree = 1 := totalDegree_X _
    have hmul := totalDegree_mul (X a.1 : MvPolynomial (Fin n) (ZMod 2)) q
    have hq1 : q.totalDegree ≤ S.card := by
      rcases hq with h | h
      · rw [h, totalDegree_zero]; exact Nat.zero_le _
      · omega
    have hq2 : (X a.1 * q).totalDegree ≤ S.card := by
      rcases hq with h | h
      · rw [h, mul_zero, totalDegree_zero]; exact Nat.zero_le _
      · omega
    by_cases hs : a.2 = true
    · simp only [hs, ↓reduceIte]
      refine ⟨(∏ l ∈ S, X l.1) + q + X a.1 * q, Or.inr ?_, by ring⟩
      have h1 := totalDegree_add ((∏ l ∈ S, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) + q) (X a.1 * q)
      have h2 := totalDegree_add (∏ l ∈ S, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) q
      have h3 := max_le hM hq1
      have h4 := max_le (h2.trans h3) hq2
      exact Nat.lt_succ_of_le (h1.trans h4)
    · have hb : a.2 = false := by simpa using hs
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      refine ⟨X a.1 * q, ?_, by ring⟩
      rcases hq with h | h
      · left; rw [h, mul_zero]
      · right; omega

theorem mulT (n : ℕ) (F : Set (MvPolynomial (Fin n) (ZMod 2))) (B : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : PCDerivable F B p) (T : Finset (Fin n))
    (hdeg : ∀ T' : Finset (Fin n), T' ⊆ T → ((∏ j ∈ T', X j) * p).totalDegree ≤ B) :
    PCDerivable F B ((∏ j ∈ T, X j) * p) := by
  induction T using Finset.induction_on with
  | empty => simpa using hp
  | insert a S ha ih =>
    have h1 := ih (fun T' hT' => hdeg T' (hT'.trans (Finset.subset_insert a S)))
    have h2 := hdeg (insert a S) (Finset.Subset.refl _)
    rw [Finset.prod_insert ha, mul_assoc] at h2 ⊢
    exact PCDerivable.mulX a h1 h2

theorem main (n : ℕ) (F : Set (Clause (Fin n))) (S : Finset (Fin n)) (C : Clause (Fin n))
    (hS : S.Nonempty) (hsub : (C.image Prod.fst) ⊆ S)
    (hcons : ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    (hd : PCDerivable (cnfSystem F) S.card (clausePoly C)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), q.totalDegree < S.card ∧
      PCDerivable (cnfSystem F) S.card ((∏ i ∈ S, MvPolynomial.X i) + q) := by
  have hinj : ∀ x ∈ C, ∀ y ∈ C, x.1 = y.1 → x = y := by
    rintro ⟨i, b⟩ hl ⟨j, c⟩ hl' hij
    simp only at hij
    subst hij
    by_contra hne
    apply hcons i
    cases b <;> cases c <;> simp_all
  have hinj' : Set.InjOn Prod.fst (C : Set (Fin n × Bool)) :=
    fun x hx y hy h => hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) h
  have hcard : (C.image Prod.fst).card = C.card := Finset.card_image_of_injOn hinj'
  have hTc : (S \ C.image Prod.fst).card + C.card = S.card := by
    rw [← hcard]; exact Finset.card_sdiff_add_card_eq_card hsub
  have hder := mulT n (cnfSystem F) S.card (clausePoly C) hd (S \ C.image Prod.fst) (by
    intro T' hT'
    refine (totalDegree_mul _ _).trans ?_
    have h1 := degX n T' id
    have h2 := degClause n C
    have h3 := Finset.card_le_card hT'
    simp only [id] at h1
    omega)
  obtain ⟨q, hq, he⟩ := split n C
  have hprod : (∏ l ∈ C, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) =
      ∏ i ∈ C.image Prod.fst, X i := (Finset.prod_image hinj).symm
  have hS' : (∏ j ∈ S \ C.image Prod.fst, (X j : MvPolynomial (Fin n) (ZMod 2))) *
      ∏ i ∈ C.image Prod.fst, X i = ∏ i ∈ S, X i := Finset.prod_sdiff hsub
  refine ⟨(∏ j ∈ S \ C.image Prod.fst, X j) * q, ?_, ?_⟩
  · rcases hq with h | h
    · rw [h, mul_zero, totalDegree_zero]; exact Finset.card_pos.mpr hS
    · have h1 := degX n (S \ C.image Prod.fst) id
      have h2 := totalDegree_mul (∏ j ∈ S \ C.image Prod.fst, (X j : MvPolynomial (Fin n) (ZMod 2))) q
      simp only [id] at h1
      omega
  · have hfin : (∏ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod 2))) +
        (∏ j ∈ S \ C.image Prod.fst, X j) * q =
        (∏ j ∈ S \ C.image Prod.fst, X j) * clausePoly C := by
      rw [he, hprod, mul_add, hS']
    rw [hfin]; exact hder

end PEqualNP.Outside.L_lib_497

theorem PEqualNP.Outside.L_lib_497 : ∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (S : Finset (Fin n)) (C : PEqualNP.ProofComplexity.Clause (Fin n)),
  S.Nonempty → (C.image Prod.fst) ⊆ S →
  (∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) →
  PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card (PEqualNP.ProofComplexity.clausePoly C) →
  ∃ q : MvPolynomial (Fin n) (ZMod 2), q.totalDegree < S.card ∧
    PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) S.card ((∏ i ∈ S, MvPolynomial.X i) + q) := by
  intro n F S C hS hsub hcons hd
  exact PEqualNP.Outside.L_lib_497.main n F S C hS hsub hcons hd
