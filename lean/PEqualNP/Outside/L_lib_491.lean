import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_491

open MvPolynomial PEqualNP.ProofComplexity

/-- The Boolean axioms `X i * X i + X i`. -/
def BA (n : ℕ) : Set (MvPolynomial (Fin n) (ZMod 2)) :=
  {q | ∃ i : Fin n, q = X i * X i + X i}

theorem zmod2_sq_add : ∀ x : ZMod 2, x * x + x = 0 := by
  decide

theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by
  decide

/-- Every derivable polynomial vanishes at every point. -/
theorem eval_derivable {n d : ℕ} {p : MvPolynomial (Fin n) (ZMod 2)}
    (h : PCDerivable (BA n) d p) (v : Fin n → ZMod 2) : eval v p = 0 := by
  induction h with
  | ax hp hdeg =>
    obtain ⟨i, rfl⟩ := hp
    simp only [map_add, map_mul, eval_X]
    exact zmod2_sq_add (v i)
  | zero => exact map_zero _
  | add hp hq ihp ihq => rw [map_add, ihp, ihq, add_zero]
  | mulX j hp hdeg ih => rw [map_mul, ih, mul_zero]

/-- The sum of the exponents of a monomial. -/
def deg {n : ℕ} (s : Fin n →₀ ℕ) : ℕ := s.sum fun _ e => e

theorem deg_add {n : ℕ} (s t : Fin n →₀ ℕ) : deg (s + t) = deg s + deg t := by
  unfold deg
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem deg_single {n : ℕ} (i : Fin n) (e : ℕ) : deg (Finsupp.single i e) = e := by
  unfold deg
  exact Finsupp.sum_single_index rfl

theorem deg_zero {n : ℕ} : deg (0 : Fin n →₀ ℕ) = 0 := by
  unfold deg
  exact Finsupp.sum_zero_index

theorem split_single {n : ℕ} (t : Fin n →₀ ℕ) (j : Fin n) (e : ℕ) (h : e ≤ t j) :
    t = (t - Finsupp.single j e) + Finsupp.single j e := by
  ext i
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs with hji
  · subst hji
    omega
  · omega

/-- A monomial multiple of a derivable polynomial is derivable when the degree allows it. -/
theorem mul_monomial {n d : ℕ} {a : MvPolynomial (Fin n) (ZMod 2)}
    (ha : PCDerivable (BA n) d a) :
    ∀ (k : ℕ) (t : Fin n →₀ ℕ), deg t = k → a.totalDegree + k ≤ d →
      PCDerivable (BA n) d (monomial t 1 * a) := by
  intro k
  induction k with
  | zero =>
    intro t ht _
    by_cases h0 : t = 0
    · subst h0
      simpa using ha
    · exfalso
      obtain ⟨j, hj⟩ := DFunLike.ne_iff.mp h0
      have hj' : t j ≠ 0 := by simpa using hj
      have hsplit := congrArg deg (split_single t j 1 (Nat.one_le_iff_ne_zero.mpr hj'))
      rw [deg_add, deg_single] at hsplit
      omega
  | succ k ih =>
    intro t ht hd
    by_cases h0 : t = 0
    · subst h0
      simpa using ha
    · obtain ⟨j, hj⟩ := DFunLike.ne_iff.mp h0
      have hj' : t j ≠ 0 := by simpa using hj
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + Finsupp.single j 1 :=
        ⟨_, split_single t j 1 (Nat.one_le_iff_ne_zero.mpr hj')⟩
      rw [deg_add, deg_single] at ht
      have ih' := ih t' (by omega) (by omega)
      have hmul : monomial (t' + Finsupp.single j 1) (1 : ZMod 2) * a =
          X j * (monomial t' 1 * a) := by
        rw [monomial_add_single, pow_one]
        ring
      rw [hmul]
      refine PCDerivable.mulX j ih' ?_
      have h1 : (X j * (monomial t' (1 : ZMod 2) * a)).totalDegree ≤
          (X j : MvPolynomial (Fin n) (ZMod 2)).totalDegree +
            (monomial t' (1 : ZMod 2) * a).totalDegree := totalDegree_mul _ _
      have h2 : (monomial t' (1 : ZMod 2) * a).totalDegree ≤
          (monomial t' (1 : ZMod 2)).totalDegree + a.totalDegree := totalDegree_mul _ _
      have h3 : (monomial t' (1 : ZMod 2)).totalDegree ≤ deg t' := totalDegree_monomial_le t' 1
      have h4 : (X j : MvPolynomial (Fin n) (ZMod 2)).totalDegree = 1 := totalDegree_X j
      omega

theorem axiom_degree {n : ℕ} (i : Fin n) :
    (X i * X i + X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 2 := by
  have h1 : (X i * X i + X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
      max (X i * X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree
        (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree := totalDegree_add _ _
  have h2 : (X i * X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤
      (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree +
        (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree := totalDegree_mul _ _
  have h4 : (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree = 1 := totalDegree_X i
  have h5 := max_le (h2.trans (by rw [h4])) (show (X i : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 2 by
    rw [h4]; exact Nat.le_succ 1)
  exact h1.trans h5

/-- A monomial of degree at most `d` has a multilinear representative, reached in degree `d`. -/
theorem monomial_norm {n d : ℕ} : ∀ (k : ℕ) (s : Fin n →₀ ℕ), deg s = k → k ≤ d →
    ∃ q : MvPolynomial (Fin n) (ZMod 2), (∀ i, q.degreeOf i ≤ 1) ∧
      PCDerivable (BA n) d (monomial s 1 + q) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro s hs hk
    by_cases hml : ∀ i, s i ≤ 1
    · refine ⟨monomial s 1, fun i => ?_, ?_⟩
      · rw [degreeOf_monomial_eq s i one_ne_zero]
        exact hml i
      · rw [CharTwo.add_self_eq_zero]
        exact PCDerivable.zero
    · obtain ⟨i, hi⟩ := not_forall.mp hml
      obtain ⟨t, rfl⟩ : ∃ t, s = t + Finsupp.single i 2 :=
        ⟨_, split_single s i 2 (by omega)⟩
      rw [deg_add, deg_single] at hs
      have hsmall : deg (t + Finsupp.single i 1) = k - 1 := by
        rw [deg_add, deg_single]
        omega
      obtain ⟨q, hq1, hq2⟩ := ih (k - 1) (by omega) (t + Finsupp.single i 1) hsmall (by omega)
      refine ⟨q, hq1, ?_⟩
      have hax : PCDerivable (BA n) d (X i * X i + X i : MvPolynomial (Fin n) (ZMod 2)) :=
        PCDerivable.ax ⟨i, rfl⟩ ((axiom_degree i).trans (by omega))
      have hmul := mul_monomial hax (deg t) t rfl (by
        have := axiom_degree i
        omega)
      have e2 : monomial (t + Finsupp.single i 2) (1 : ZMod 2) = monomial t 1 * (X i * X i) := by
        rw [monomial_add_single]
        ring
      have e1 : monomial (t + Finsupp.single i 1) (1 : ZMod 2) = monomial t 1 * X i := by
        rw [monomial_add_single, pow_one]
      have key : monomial (t + Finsupp.single i 2) (1 : ZMod 2) + q =
          monomial t 1 * (X i * X i + X i) + (monomial (t + Finsupp.single i 1) 1 + q) := by
        rw [e2, e1]
        have hz := CharTwo.add_self_eq_zero (monomial t (1 : ZMod 2) * X i)
        linear_combination (-1 : MvPolynomial (Fin n) (ZMod 2)) * hz
      rw [key]
      exact PCDerivable.add hmul hq2

/-- Every polynomial has a multilinear representative, reached in its own degree. -/
theorem exists_norm {n : ℕ} (p : MvPolynomial (Fin n) (ZMod 2)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), (∀ i, q.degreeOf i ≤ 1) ∧
      PCDerivable (BA n) p.totalDegree (p + q) := by
  have hzero : ∃ q : MvPolynomial (Fin n) (ZMod 2), (∀ i, q.degreeOf i ≤ 1) ∧
      PCDerivable (BA n) p.totalDegree (0 + q) := by
    refine ⟨0, fun i => ?_, ?_⟩
    · rw [degreeOf_zero]
      exact Nat.zero_le 1
    · rw [add_zero]
      exact PCDerivable.zero
  have hsum : ∀ (S : Finset (Fin n →₀ ℕ)), (∀ s ∈ S, deg s ≤ p.totalDegree) →
      ∃ q : MvPolynomial (Fin n) (ZMod 2), (∀ i, q.degreeOf i ≤ 1) ∧
        PCDerivable (BA n) p.totalDegree ((∑ s ∈ S, monomial s (p.coeff s)) + q) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      rw [Finset.sum_empty]
      exact hzero
    · intro a S ha ih hS
      obtain ⟨q1, hq1, hd1⟩ := ih (fun s hs => hS s (Finset.mem_insert_of_mem hs))
      have hadeg := hS a (Finset.mem_insert_self a S)
      obtain ⟨q2, hq2, hd2⟩ : ∃ q : MvPolynomial (Fin n) (ZMod 2), (∀ i, q.degreeOf i ≤ 1) ∧
          PCDerivable (BA n) p.totalDegree (monomial a (p.coeff a) + q) := by
        rcases zmod2_cases (p.coeff a) with h0 | h1
        · rw [h0, monomial_zero]
          exact hzero
        · rw [h1]
          exact monomial_norm (deg a) a rfl hadeg
      refine ⟨q2 + q1, fun i => ?_, ?_⟩
      · exact (degreeOf_add_le i q2 q1).trans (max_le (hq2 i) (hq1 i))
      · rw [Finset.sum_insert ha]
        have hre : monomial a (p.coeff a) + ∑ s ∈ S, monomial s (p.coeff s) + (q2 + q1) =
            (monomial a (p.coeff a) + q2) + (∑ s ∈ S, monomial s (p.coeff s) + q1) := by
          ring
        rw [hre]
        exact PCDerivable.add hd2 hd1
  obtain ⟨q, hq, hd⟩ := hsum p.support (fun s hs => le_totalDegree hs)
  rw [support_sum_monomial_coeff] at hd
  exact ⟨q, hq, hd⟩

theorem multilinear_mem {n : ℕ} {q : MvPolynomial (Fin n) (ZMod 2)}
    (hq : ∀ i, q.degreeOf i ≤ 1) : q ∈ restrictDegree (Fin n) (ZMod 2) 1 := by
  rw [mem_restrictDegree]
  intro s hs i
  exact (monomial_le_degreeOf i hs).trans (hq i)

theorem main (n : ℕ) (p : MvPolynomial (Fin n) (ZMod 2)) :
    ∃! q : MvPolynomial (Fin n) (ZMod 2), (∀ i : Fin n, q.degreeOf i ≤ 1) ∧
      PCDerivable (BA n) p.totalDegree (p + q) := by
  obtain ⟨q, hq, hd⟩ := exists_norm p
  refine ⟨q, ⟨hq, hd⟩, ?_⟩
  rintro q' ⟨hq', hd'⟩
  have hsum : PCDerivable (BA n) p.totalDegree (q' + q) := by
    have hre : q' + q = (p + q') + (p + q) := by
      have hz := CharTwo.add_self_eq_zero p
      linear_combination (-1 : MvPolynomial (Fin n) (ZMod 2)) * hz
    rw [hre]
    exact PCDerivable.add hd' hd
  have hcard : Fintype.card (ZMod 2) - 1 = 1 := by
    rw [ZMod.card]
  have hmem : q' + q ∈ restrictDegree (Fin n) (ZMod 2) (Fintype.card (ZMod 2) - 1) := by
    rw [hcard]
    exact multilinear_mem (fun i => (degreeOf_add_le i q' q).trans (max_le (hq' i) (hq i)))
  have hzero : q' + q = 0 :=
    eq_zero_of_eval_eq_zero (Fin n) (ZMod 2) (q' + q) (fun v => eval_derivable hsum v) hmem
  exact CharTwo.add_eq_zero.mp hzero

end PEqualNP.Outside.L_lib_491

theorem PEqualNP.Outside.L_lib_491 : ∀ (n : ℕ), let P := MvPolynomial (Fin n) (ZMod 2)
  let B := {q : P | ∃ i : Fin n, q = MvPolynomial.X i * MvPolynomial.X i + MvPolynomial.X i}
  ∀ p : P, ∃! q : P, (∀ i : Fin n, q.degreeOf i ≤ 1) ∧
    PEqualNP.ProofComplexity.PCDerivable B p.totalDegree (p + q) := by
  intro n P B p
  exact PEqualNP.Outside.L_lib_491.main n p
