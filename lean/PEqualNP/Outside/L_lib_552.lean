import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_552_aux

open MvPolynomial in
theorem main (q h : ℕ) (c : (Fin h → Fin q) → ℚ) (S : Finset ℚ)
    (hS : S.Nonempty) (hc : ∃ w, c w ≠ 0) :
    ((Finset.univ : Finset (Fin h → Fin q → ↥S)).filter (fun z =>
      ∑ w : Fin h → Fin q, c w * ∏ i : Fin h, (z i (w i)).val = 0)).card * S.card
      ≤ h * (Finset.univ : Finset (Fin h → Fin q → ↥S)).card := by
  classical
  obtain ⟨w0, hw0⟩ := hc
  let e : Fin h × Fin q ≃ Fin (h * q) := finProdFinEquiv
  let m : (Fin h → Fin q) → (Fin (h * q) →₀ ℕ) :=
    fun w => ∑ i : Fin h, Finsupp.single (e (i, w i)) 1
  let p : MvPolynomial (Fin (h * q)) ℚ := ∑ w : Fin h → Fin q, monomial (m w) (c w)
  have key : ∀ (w : Fin h → Fin q) (i : Fin h) (a : Fin q),
      m w (e (i, a)) = if w i = a then 1 else 0 := by
    intro w i a
    simp only [m, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply,
      e.injective.eq_iff, Prod.mk.injEq]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have hminj : Function.Injective m := by
    intro w w' hww
    funext i
    have h1 := key w i (w i)
    have h2 := key w' i (w i)
    rw [hww] at h1
    rw [h1] at h2
    simp at h2
    exact h2.symm
  have hp : p ≠ 0 := by
    intro hp0
    have h1 : p.coeff (m w0) = c w0 := by
      simp only [p, coeff_sum, coeff_monomial]
      rw [Finset.sum_eq_single w0]
      · simp
      · intro w _ hw; rw [if_neg (fun h => hw (hminj h))]
      · simp
    rw [hp0] at h1; simp at h1; exact hw0 h1.symm
  have hdeg : p.totalDegree ≤ h := by
    apply totalDegree_finsetSum_le
    intro w _
    refine (totalDegree_monomial_le _ _).trans ?_
    simp only [m]
    rw [← Finsupp.sum_finsetSum_index (by simp) (by simp)]
    simp [Finsupp.sum_single_index]
  have heval : ∀ f : Fin (h * q) → ℚ,
      eval f p = ∑ w : Fin h → Fin q, c w * ∏ i : Fin h, f (e (i, w i)) := by
    intro f
    simp only [p, map_sum, eval_monomial]
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    simp only [m]
    rw [← Finsupp.prod_finsetSum_index (by simp) (by intros; simp [pow_add])]
    simp [Finsupp.prod_single_index]
  have hSZ := schwartz_zippel_totalDegree hp S
  have hcard : ((Finset.univ : Finset (Fin h → Fin q → ↥S)).filter (fun z =>
      ∑ w : Fin h → Fin q, c w * ∏ i : Fin h, (z i (w i)).val = 0)).card ≤
      (Finset.filter (fun f => eval f p = 0)
        (Fintype.piFinset fun _ : Fin (h * q) => S)).card := by
    apply Finset.card_le_card_of_injOn
      (fun z k => ((z (e.symm k).1 (e.symm k).2 : ↥S) : ℚ))
    · intro z hz
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
        true_and, Fintype.mem_piFinset] at hz ⊢
      refine ⟨fun k => (z _ _).2, ?_⟩
      rw [heval]; simpa using hz
    · intro z _ z' _ hzz
      funext i a
      have := congrFun hzz (e (i, a))
      simp at this
      exact this
  have hA : (Finset.univ : Finset (Fin h → Fin q → ↥S)).card = S.card ^ (h * q) := by
    simp [Finset.card_univ, pow_mul']
  have hpos : (0 : NNRat) < S.card := by exact_mod_cast hS.card_pos
  have h2 := hSZ.trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hdeg) hpos.le)
  rw [div_le_div_iff₀ (by positivity) hpos] at h2
  rw [hA]
  refine (Nat.mul_le_mul_right _ hcard).trans ?_
  exact_mod_cast h2

end PEqualNP.Outside.L_lib_552_aux

theorem PEqualNP.Outside.L_lib_552 : (∀ (q h : ℕ) (c : (Fin h → Fin q) → ℚ) (S : Finset ℚ),
  S.Nonempty → (∃ w, c w ≠ 0) →
  let assignments := (Finset.univ : Finset (Fin h → Fin q → ↥S))
  let val := fun z : Fin h → Fin q → ↥S =>
    ∑ w : Fin h → Fin q, c w * ∏ i : Fin h, (z i (w i)).val
  (assignments.filter (fun z => val z = 0)).card * S.card ≤ h * assignments.card) := by
  intro q h c S hS hc assignments val
  exact PEqualNP.Outside.L_lib_552_aux.main q h c S hS hc
