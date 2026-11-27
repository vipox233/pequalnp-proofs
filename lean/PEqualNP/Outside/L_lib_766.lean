import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_766

open MvPolynomial

private abbrev F := ZMod 2

private abbrev Poly (n : ℕ) := MvPolynomial (Fin n) F

private noncomputable def base {n : ℕ} (p : Poly (n+1)) : Poly n :=
  (finSuccEquiv F n p).coeff 0

private noncomputable def difference {n : ℕ} (p : Poly (n+1)) : Poly n :=
  ∑ j ∈ Finset.range (finSuccEquiv F n p).natDegree, (finSuccEquiv F n p).coeff (j+1)

private theorem base_degree {n d : ℕ} (p : Poly (n+1)) (hp : p.totalDegree ≤ d) :
    (base p).totalDegree ≤ d := by
  by_cases h : base p = 0
  · simp [h]
  · have := totalDegree_coeff_finSuccEquiv_add_le p 0 h
    exact (by simpa only [base, Nat.add_zero] using this : (base p).totalDegree ≤ _).trans hp

private theorem diff_degree {n d : ℕ} (p : Poly (n+1)) (hp : p.totalDegree ≤ d+1) :
    (difference p).totalDegree ≤ d := by
  apply totalDegree_finsetSum_le
  intro j _
  by_cases h : (finSuccEquiv F n p).coeff (j+1) = 0
  · simp [h]
  · have := totalDegree_coeff_finSuccEquiv_add_le p (j+1) h
    omega

private theorem eval_base {n : ℕ} (p : Poly (n+1)) (x : Fin n → F) :
    eval (Fin.cons 0 x) p = eval x (base p) := by
  rw [eval_eq_eval_mv_eval', ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
  rfl

private theorem eval_one_slice {n : ℕ} (p : Poly (n+1)) (x : Fin n → F) :
    eval (Fin.cons 1 x) p = eval x (base p) + eval x (difference p) := by
  rw [eval_eq_eval_mv_eval', Polynomial.eval_one_map, ← map_add]
  congr 1
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp only [one_pow, mul_one, base, difference, add_comm]

private noncomputable def supportAt {n : ℕ} (p : Poly n) : Finset (Fin n → F) := by
  classical
  exact Finset.univ.filter (fun x => eval x p ≠ 0)

private theorem mem_supportAt {n : ℕ} (p : Poly n) (x : Fin n → F) :
    x ∈ supportAt p ↔ eval x p ≠ 0 := by
  classical
  simp [supportAt]

private theorem split_count (n : ℕ) (P : (Fin (n+1) → F) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      (Finset.univ.filter (fun x : Fin n → F => P (Fin.cons 0 x))).card +
      (Finset.univ.filter (fun x : Fin n → F => P (Fin.cons 1 x))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  let f := fun z : Fin (n+1) → F => if P z then (1 : ℕ) else 0
  change (∑ z, f z) = (∑ x : Fin n → F, f (Fin.cons 0 x)) + (∑ x : Fin n → F, f (Fin.cons 1 x))
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => F)).sum_comp f, Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply]
  rw [show (Finset.univ : Finset F) = {0,1} by decide +kernel]
  simp

private theorem constant_count {n : ℕ} (p : Poly n) (hp : p.totalDegree = 0)
    (hne : ∃ x : Fin n → F, eval x p ≠ 0) : (supportAt p).card = 2^n := by
  classical
  have heq := totalDegree_eq_zero_iff_eq_C.mp hp
  obtain ⟨x,hx⟩ := hne
  have hc : p.coeff 0 ≠ 0 := by
    rwa [heq, eval_C] at hx
  have hs : supportAt p = Finset.univ := by
    ext x
    simp only [mem_supportAt, Finset.mem_univ, iff_true]
    rw [heq, eval_C]
    exact hc
  rw [hs]
  simp

private theorem estimate (n : ℕ) : ∀ (d : ℕ) (p : Poly n), p.totalDegree ≤ d →
    (∃ x : Fin n → F, eval x p ≠ 0) → 2^n ≤ 2^d * (supportAt p).card := by
  classical
  induction n with
  | zero =>
    intro d p _ hp
    obtain ⟨x,hx⟩ := hp
    have pos := Finset.card_pos.mpr ⟨x, (mem_supportAt p x).mpr hx⟩
    exact Nat.mul_pos (by positivity) pos
  | succ n ih =>
    intro d p hp hne
    cases d with
    | zero => rw [constant_count p (Nat.eq_zero_of_le_zero hp) hne, pow_zero, one_mul]
    | succ d =>
      let q := base p
      let r := difference p
      let count0 := Finset.univ.filter (fun x : Fin n → F => eval (Fin.cons 0 x) p ≠ 0)
      let count1 := Finset.univ.filter (fun x : Fin n → F => eval (Fin.cons 1 x) p ≠ 0)
      have hf : (supportAt p).card = count0.card + count1.card := split_count n _
      have h0 : count0 = supportAt q := by
        ext x
        simp [count0, mem_supportAt, q, eval_base]
      by_cases hr : ∃ x : Fin n → F, eval x r ≠ 0
      · have hb := ih d r (diff_degree p hp) hr
        have diff_support : supportAt r ⊆ count0 ∪ count1 := by
          intro x hx
          have hxr := (mem_supportAt r x).mp hx
          by_contra miss
          have hleft : eval (Fin.cons 0 x) p = 0 := by
            by_contra notZero
            exact miss (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,notZero⟩))
          have hright : eval (Fin.cons 1 x) p = 0 := by
            by_contra notZero
            exact miss (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,notZero⟩))
          rw [eval_base] at hleft
          rw [eval_one_slice, hleft, zero_add] at hright
          exact hxr hright
        have hc : (supportAt r).card ≤ (supportAt p).card := by
          rw [hf]
          exact (Finset.card_le_card diff_support).trans (Finset.card_union_le _ _)
        calc
          2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
          _ ≤ 2 * (2 ^ d * (supportAt p).card) :=
            Nat.mul_le_mul_left 2 (hb.trans (Nat.mul_le_mul_left _ hc))
          _ = 2 ^ (d + 1) * (supportAt p).card := by rw [pow_succ]; ring
      · have zero_r (x : Fin n → F) : eval x r = 0 := not_ne_iff.mp (not_exists.mp hr x)
        have h1 : count1 = supportAt q := by
          ext x
          simp only [count1, Finset.mem_filter_univ, mem_supportAt, eval_one_slice]
          change eval x q + eval x r ≠ 0 ↔ eval x q ≠ 0
          rw [zero_r, add_zero]
        obtain ⟨x,hx⟩ := hne
        let z := Fin.tail x
        have hhead : x 0 = 0 ∨ x 0 = 1 := by
          have hz : ∀ b : F, b = 0 ∨ b = 1 := by decide +kernel
          exact hz (x 0)
        have hqn : eval z q ≠ 0 := by
          have he : Fin.cons (x 0) z = x := Fin.cons_self_tail x
          rw [← he] at hx
          rcases hhead with hh | hh
          · simpa only [hh, eval_base] using hx
          · simpa only [hh, eval_one_slice, show eval z (difference p) = 0 from zero_r z, add_zero] using hx
        have hb := ih (d+1) q (base_degree p hp) ⟨z,hqn⟩
        rw [hf, h0, h1, pow_succ, Nat.mul_add]
        omega

end PEqualNP.Outside.L_lib_766

theorem PEqualNP.Outside.L_lib_766 :
    ∀ (n d : ℕ) (p : MvPolynomial (Fin n) (ZMod 2)), p.totalDegree ≤ d →
      (∃ x : Fin n → ZMod 2, MvPolynomial.eval x p ≠ 0) →
      2 ^ n ≤ 2 ^ d * (Finset.univ.filter (fun x : Fin n → ZMod 2 => MvPolynomial.eval x p ≠ 0)).card := by
  exact PEqualNP.Outside.L_lib_766.estimate
