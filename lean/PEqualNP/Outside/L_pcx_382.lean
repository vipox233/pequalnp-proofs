import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.BoolVanish

namespace PEqualNP.Outside.L_pcx_382

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

private theorem degree_line {V : Type} {A : Set (Poly V)} {d : ℕ} {p : Poly V}
    (h : PCDerivable A d p) : p.totalDegree ≤ d := by
  induction h with
  | ax _ h => exact h
  | zero => simp
  | add _ _ ih₁ ih₂ => exact (totalDegree_add _ _).trans (max_le ih₁ ih₂)
  | mulX _ _ h _ => exact h

private theorem degree_product {V ι : Type} (S : Finset ι) (p : ι → Poly V) :
    (∏ i ∈ S, p i).totalDegree ≤ ∑ i ∈ S, (p i).totalDegree := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

private theorem with_factor {V : Type} {A F : Set (Poly V)} {d B : ℕ}
    (q : Poly V) (hq : q.totalDegree + d ≤ B)
    (base : ∀ p ∈ A, p.totalDegree ≤ d → PCDerivable F B (q * p))
    {p : Poly V} (h : PCDerivable A d p) : PCDerivable F B (q * p) := by
  induction h with
  | ax hp hd => exact base _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable F B 0)
  | add _ _ ih₁ ih₂ =>
    rw [mul_add]
    exact .add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [mul_left_comm q (X j)]
    apply PCDerivable.mulX j ih
    rw [← mul_left_comm q (X j)]
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add_left hd _).trans hq)

private theorem derive_products {V : Type} {F : Set (Poly V)} {B : ℕ} :
    ∀ (t : ℕ) (A : Fin t → Set (Poly V)) (D : Fin t → ℕ) (q : Poly V)
      (p : Fin t → Poly V), (∀ i, PCDerivable (A i) (D i) (p i)) →
      q.totalDegree + (∑ i, D i) ≤ B →
      (∀ f : Fin t → Poly V, (∀ i, f i ∈ A i ∧ (f i).totalDegree ≤ D i) →
        PCDerivable F B (q * ∏ i, f i)) →
      PCDerivable F B (q * ∏ i, p i) := by
  intro t
  induction t with
  | zero =>
    intro A D q p _ _ base
    exact base p (fun i => Fin.elim0 i)
  | succ t ih =>
    intro A D q p deriv hp base
    rw [Fin.sum_univ_succ] at hp
    let r : Poly V := ∏ i : Fin t, p i.succ
    have r_bound : r.totalDegree ≤ ∑ i : Fin t, D i.succ :=
      (degree_product Finset.univ (fun i : Fin t => p i.succ)).trans
        (Finset.sum_le_sum fun i _ => degree_line (deriv i.succ))
    have qr_bound : (q*r).totalDegree + D 0 ≤ B := by
      have h := totalDegree_mul q r
      omega
    rw [Fin.prod_univ_succ, ← mul_assoc]
    change PCDerivable F B ((q * p 0) * r)
    rw [mul_right_comm]
    apply with_factor (q*r) qr_bound _ (deriv 0)
    intro a ha da
    have qa_bound : (q*a).totalDegree + (∑ i : Fin t, D i.succ) ≤ B := by
      have h := totalDegree_mul q a
      omega
    have suffix := ih (fun i => A i.succ) (fun i => D i.succ) (q*a)
      (fun i => p i.succ) (fun i => deriv i.succ) qa_bound (by
        intro f hf
        let full : Fin (t+1) → Poly V := Fin.cons a f
        have hfull (j : Fin (t+1)) : full j ∈ A j ∧ (full j).totalDegree ≤ D j := by
          refine Fin.cases ?_ (fun i => ?_) j
          · simpa [full] using And.intro ha da
          · simpa [full] using hf i
        simpa only [full, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← mul_assoc]
          using base full hfull)
    simpa only [r, mul_right_comm q a] using suffix

theorem combine {V : Type} (F : Set (Poly V)) (t : ℕ)
    (E : Fin t → Set (Poly V)) (D : Fin t → ℕ)
    (boolean : ∀ v : V, X v * X v + X v ∈ F)
    (cover : ∀ x : V → ZMod 2, ∃ j : Fin t, ∀ e ∈ E j, eval x e = 0)
    (branches : ∀ j, PCRefutable (F ∪ E j) (D j)) : PCRefutable F (∑ j, D j) := by
  classical
  let B := ∑ j, D j
  have base (p : Fin t → Poly V) (hp : ∀ j, p j ∈ F ∪ E j ∧ (p j).totalDegree ≤ D j) :
      PCDerivable F B (1 * ∏ j, p j) := by
    rw [one_mul]
    by_cases hasBase : ∃ i, p i ∈ F
    · obtain ⟨i, hi⟩ := hasBase
      let r := Finset.univ.erase i
      have hsum : (∑ j ∈ r, D j) + D i = B :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i)
      let q := ∏ j ∈ r, p j
      have hq : q.totalDegree ≤ ∑ j ∈ r, D j := (degree_product r p).trans
        (Finset.sum_le_sum fun j _ => (hp j).2)
      have derived : PCDerivable F (D i) (p i) := .ax hi (hp i).2
      have step := pcDerivable_mul_left derived q
      have hstep : PCDerivable F B (q * p i) :=
        pcDerivable_mono step (max_le (by omega) (by have := (hp i).2; omega)) (fun _ h => h)
      rwa [Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at hstep
    · apply BoolVanish.vanish_derivable V F B _ boolean
      · exact (degree_product Finset.univ p).trans (Finset.sum_le_sum fun j _ => (hp j).2)
      · intro x
        obtain ⟨i, hi⟩ := cover x
        have hmem : p i ∈ E i := ((hp i).1).resolve_left (fun h => hasBase ⟨i,h⟩)
        rw [map_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ i) (hi _ hmem)
  have h := derive_products t (fun j => F ∪ E j) D (1 : Poly V) (fun _ => 1)
    branches (by simp [B]) base
  simpa [PCRefutable, B] using h

end PEqualNP.Outside.L_pcx_382

theorem PEqualNP.Outside.L_pcx_382 :
    ∀ (V : Type) (F : Set (MvPolynomial V (ZMod 2))) (t : ℕ)
      (E : Fin t → Set (MvPolynomial V (ZMod 2))) (D : Fin t → ℕ),
      (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
      (∀ x : V → ZMod 2, ∃ j : Fin t, ∀ e ∈ E j, MvPolynomial.eval x e = 0) →
      (∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ E j) (D j)) →
      PEqualNP.ProofComplexity.PCRefutable F (∑ j, D j) := by
  intro V F t E D boolean cover branches
  exact PEqualNP.Outside.L_pcx_382.combine F t E D boolean cover branches
