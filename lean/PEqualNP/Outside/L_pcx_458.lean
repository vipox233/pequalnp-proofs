import PEqualNP.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_pcx_458_aux

open MvPolynomial Finset

private abbrev K := ZMod 2

private lemma z2_cases (x : K) : x = 0 ∨ x = 1 := by
  revert x
  decide

private lemma z2_add_self (x : K) : x + x = 0 := by
  revert x
  decide

private lemma z2_mul_self (x : K) : x * x = x := by
  revert x
  decide

private lemma z2_pow_pos {x : K} {n : ℕ} (hn : 0 < n) : x ^ n = x := by
  rcases z2_cases x with rfl | rfl
  · exact zero_pow hn.ne'
  · exact one_pow n

private lemma z2_eq_one_of_one_add_eq_zero {x : K} (h : 1 + x = 0) : x = 1 := by
  rcases z2_cases x with rfl | rfl
  · exact absurd h (by decide)
  · rfl

private lemma z2_add_one_eq_iff {x y : K} : x + 1 = y ↔ x = y + 1 := by
  revert x y
  decide

private lemma prod_one_add {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → K) :
    ∏ i : ι, (1 + y i) = ∑ T : Finset ι, ∏ i ∈ T, y i := by
  have h1 : (∏ i : ι, (1 + y i)) = ∏ i ∈ (Finset.univ : Finset ι), (y i + 1) := by
    refine Finset.prod_congr rfl fun i _ => add_comm 1 (y i)
  rw [h1, Finset.prod_add_one, Finset.powerset_univ]

private lemma fits_to_select {m d : ℕ} {p q : Fin m → ℕ}
    (hfits : ∀ T : Finset (Fin m), T.Nonempty → ∃ S ⊆ T, S.Nonempty ∧
      (∑ i ∈ S, p i) + (∑ i ∈ T \ S, q i) ≤ d)
    (W : Type) (c e : Fin m → MvPolynomial W K)
    (hce : ∀ i, (c i).totalDegree ≤ p i ∧ (e i).totalDegree ≤ q i) :
    ∃ s : MvPolynomial W K, s.totalDegree ≤ d ∧
      ∀ x : W → K, (∃ u : K, ∀ i, eval x (c i) = u * eval x (e i)) →
        ∀ i, eval x (c i) = eval x s * eval x (e i) := by
  classical
  let NE : Finset (Finset (Fin m)) := Finset.univ.erase ∅
  let term : Finset (Fin m) → MvPolynomial W K := fun T =>
    if hT : T.Nonempty then
      let S := (hfits T hT).choose
      (∏ i ∈ S, c i) * (∏ i ∈ T \ S, e i)
    else 0
  refine ⟨∑ T ∈ NE, term T, ?_, ?_⟩
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro T hT
    have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT)
    simp only [term, hne, ↓reduceDIte]
    set S := (hfits T hne).choose
    have hS := (hfits T hne).choose_spec
    calc ((∏ i ∈ S, c i) * (∏ i ∈ T \ S, e i)).totalDegree
        ≤ (∏ i ∈ S, c i).totalDegree + (∏ i ∈ T \ S, e i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
      _ ≤ (∑ i ∈ S, (c i).totalDegree) + (∑ i ∈ T \ S, (e i).totalDegree) :=
          Nat.add_le_add (MvPolynomial.totalDegree_finsetProd _ _)
            (MvPolynomial.totalDegree_finsetProd _ _)
      _ ≤ (∑ i ∈ S, p i) + (∑ i ∈ T \ S, q i) :=
          Nat.add_le_add (Finset.sum_le_sum fun i _ => (hce i).1)
            (Finset.sum_le_sum fun i _ => (hce i).2)
      _ ≤ d := hS.2.2
  · intro x ⟨u, hu⟩ i₀
    rcases z2_cases (eval x (e i₀)) with he0 | he1
    · rw [hu i₀, he0, mul_zero, mul_zero]
    · have heval : eval x (∑ T ∈ NE, term T) = u * ∑ T ∈ NE, ∏ i ∈ T, eval x (e i) := by
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun T hT => ?_
        have hne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hT)
        simp only [term, hne, ↓reduceDIte, map_mul, map_prod]
        set S := (hfits T hne).choose
        have hS := (hfits T hne).choose_spec
        have h1 : (∏ i ∈ S, eval x (c i)) = u * ∏ i ∈ S, eval x (e i) := by
          calc ∏ i ∈ S, eval x (c i)
              = ∏ i ∈ S, (u * eval x (e i)) := Finset.prod_congr rfl fun i _ => hu i
            _ = (∏ _i ∈ S, u) * (∏ i ∈ S, eval x (e i)) := Finset.prod_mul_distrib
            _ = u ^ S.card * (∏ i ∈ S, eval x (e i)) := by rw [Finset.prod_const]
            _ = u * (∏ i ∈ S, eval x (e i)) := by rw [z2_pow_pos hS.2.1.card_pos]
        rw [h1, mul_assoc, mul_comm (∏ i ∈ S, eval x (e i)), Finset.prod_sdiff hS.1]
      have hsum0 : 1 + ∑ T ∈ NE, ∏ i ∈ T, eval x (e i) = 0 := by
        have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Finset (Fin m)))
          (fun T => ∏ i ∈ T, eval x (e i)) (Finset.mem_univ ∅)
        simp only [Finset.prod_empty] at hsplit
        change 1 + ∑ T ∈ NE, ∏ i ∈ T, eval x (e i) = 0
        rw [hsplit, ← prod_one_add]
        refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        rw [he1]
        exact z2_add_self 1
      have hsum1 : ∑ T ∈ NE, ∏ i ∈ T, eval x (e i) = 1 :=
        z2_eq_one_of_one_add_eq_zero hsum0
      rw [hu i₀, heval, hsum1, mul_one]

private abbrev VType (m : ℕ) (p q : Fin m → ℕ) :=
  (Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))

private noncomputable def coeffs {V : Type} [DecidableEq V]
    (s : MvPolynomial V K) (U : Finset V) : K :=
  ∑ μ ∈ s.support.filter (fun μ => μ.support = U), s.coeff μ

private lemma coeff_degree {V : Type} [DecidableEq V] {s : MvPolynomial V K} {d : ℕ}
    (hs : s.totalDegree ≤ d) {U : Finset V} (hne : coeffs s U ≠ 0) : U.card ≤ d := by
  have hne_f : (s.support.filter (fun μ => μ.support = U)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    exact hne (by simp [coeffs, h])
  rcases hne_f with ⟨μ, hμ⟩
  rw [Finset.mem_filter] at hμ
  have hle : U.card ≤ μ.sum (fun _ e => e) := by
    rw [← hμ.2, Finsupp.sum]
    calc μ.support.card = ∑ _v ∈ μ.support, 1 := by simp
      _ ≤ ∑ v ∈ μ.support, μ v :=
        Finset.sum_le_sum fun v hv => Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
  exact le_trans hle (le_trans (MvPolynomial.le_totalDegree hμ.1) hs)

private lemma eval_eq_sum_coeffs {V : Type} [Fintype V] [DecidableEq V]
    (s : MvPolynomial V K) (x : V → K) :
    eval x s = ∑ U : Finset V, coeffs s U * ∏ v ∈ U, x v := by
  conv_lhs => rw [s.as_sum]
  rw [map_sum]
  have hmon : ∀ μ ∈ s.support, eval x (monomial μ (s.coeff μ)) =
      s.coeff μ * ∏ v ∈ μ.support, x v := by
    intro μ _
    rw [MvPolynomial.eval_monomial, Finsupp.prod]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    exact z2_pow_pos (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv))
  rw [Finset.sum_congr rfl hmon]
  calc ∑ μ ∈ s.support, s.coeff μ * ∏ v ∈ μ.support, x v
      = ∑ μ ∈ s.support, ∑ U : Finset V,
          if μ.support = U then s.coeff μ * ∏ v ∈ U, x v else 0 := by
        refine Finset.sum_congr rfl fun μ _ => ?_
        simp
    _ = ∑ U : Finset V, ∑ μ ∈ s.support,
          if μ.support = U then s.coeff μ * ∏ v ∈ U, x v else 0 :=
        Finset.sum_comm
    _ = ∑ U : Finset V, coeffs s U * ∏ v ∈ U, x v := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [coeffs, Finset.sum_mul, Finset.sum_filter]

private def BFib (k : ℕ) (γ : K) : Finset (Fin k → K) :=
  Finset.univ.filter (fun z : Fin k → K => (∏ j : Fin k, z j) = γ)

private lemma prod_eq_one_iff {k : ℕ} (z : Fin k → K) :
    (∏ j : Fin k, z j) = 1 ↔ z = fun _ => 1 := by
  constructor
  · intro h
    funext j
    rcases z2_cases (z j) with hj | hj
    · exfalso
      have h0 : (∏ i : Fin k, z i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
      rw [h0] at h
      exact zero_ne_one h
    · exact hj
  · rintro rfl
    simp

private lemma sum_cube_prod {k : ℕ} (W : Finset (Fin k)) :
    (∑ z : Fin k → K, ∏ j ∈ W, z j) = if W = Finset.univ then 1 else 0 := by
  have h1 : (∑ z : Fin k → K, ∏ j ∈ W, z j) =
      ∑ z ∈ Fintype.piFinset (fun _ : Fin k => (Finset.univ : Finset K)),
        ∏ j : Fin k, (if j ∈ W then z j else 1) := by
    rw [Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h1, ← Finset.prod_univ_sum (t := fun _ : Fin k => (Finset.univ : Finset K))
    (f := fun j b => if j ∈ W then b else (1 : K))]
  have h2 : ∀ j : Fin k,
      (∑ b : K, if j ∈ W then b else (1 : K)) = if j ∈ W then 1 else 0 := by
    intro j
    by_cases hj : j ∈ W <;> simp [hj] <;> decide
  simp_rw [h2]
  by_cases hW : W = Finset.univ
  · subst hW
    simp
  · simp only [hW, ↓reduceIte]
    have hex : ∃ j : Fin k, j ∉ W := by
      by_contra hall
      push_neg at hall
      apply hW
      ext j
      simp [hall j]
    rcases hex with ⟨j, hj⟩
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])

private lemma block_fiber_sum {k : ℕ} (W : Finset (Fin k)) (γ : K) :
    (∑ z ∈ BFib k γ, ∏ j ∈ W, z j) = if W = Finset.univ then γ else 1 := by
  rcases z2_cases γ with rfl | rfl
  · have hBF0 : BFib k 0 = Finset.univ.erase (fun _ => 1) := by
      ext z
      simp only [BFib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      rcases z2_cases (∏ j : Fin k, z j) with h0 | h1
      · constructor
        · intro _
          refine ⟨?_, trivial⟩
          intro hz
          rw [← prod_eq_one_iff] at hz
          rw [h0] at hz
          exact zero_ne_one hz
        · intro _
          exact h0
      · constructor
        · intro h0
          rw [h1] at h0
          exact absurd h0 one_ne_zero
        · intro ⟨hne, _⟩
          exact absurd ((prod_eq_one_iff z).mp h1) hne
    rw [hBF0]
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin k → K))
      (fun z => ∏ j ∈ W, z j) (Finset.mem_univ (fun _ => 1))
    simp only [Finset.prod_const_one] at hsplit
    rw [sum_cube_prod W, add_comm] at hsplit
    have hres := z2_add_one_eq_iff.mp hsplit
    rw [hres]
    by_cases hW : W = Finset.univ <;> simp [hW] <;> decide
  · have hBF1 : BFib k 1 = {fun _ => 1} := by
      ext z
      simp only [BFib, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact prod_eq_one_iff z
    rw [hBF1]
    simp

private def eV {m : ℕ} {p q : Fin m → ℕ} :
    ((∀ i : Fin m, Fin (p i) → K) × (∀ i : Fin m, Fin (q i) → K)) ≃ (VType m p q → K) where
  toFun ab := Sum.elim (fun x => ab.1 x.1 x.2) (fun y => ab.2 y.1 y.2)
  invFun f := (fun i j => f (Sum.inl ⟨i, j⟩), fun i j => f (Sum.inr ⟨i, j⟩))
  left_inv ab := by
    rcases ab with ⟨a, b⟩
    rfl
  right_inv f := by
    funext v
    rcases v with ⟨i, j⟩ | ⟨i, j⟩ <;> rfl

private def Fiber {m : ℕ} {p q : Fin m → ℕ} (α β : Fin m → K) : Finset (VType m p q → K) :=
  ((Fintype.piFinset fun i : Fin m => BFib (p i) (α i)) ×ˢ
   (Fintype.piFinset fun i : Fin m => BFib (q i) (β i))).map eV.toEmbedding

private def UA {m : ℕ} {p q : Fin m → ℕ} (U : Finset (VType m p q)) (i : Fin m) :
    Finset (Fin (p i)) :=
  Finset.univ.filter (fun j => (Sum.inl ⟨i, j⟩ : VType m p q) ∈ U)

private def UB {m : ℕ} {p q : Fin m → ℕ} (U : Finset (VType m p q)) (i : Fin m) :
    Finset (Fin (q i)) :=
  Finset.univ.filter (fun j => (Sum.inr ⟨i, j⟩ : VType m p q) ∈ U)

private def S_full {m : ℕ} {p q : Fin m → ℕ} (U : Finset (VType m p q)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => UA U i = Finset.univ)

private def R_full {m : ℕ} {p q : Fin m → ℕ} (U : Finset (VType m p q)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => UB U i = Finset.univ)

private lemma prod_eV {m : ℕ} {p q : Fin m → ℕ} (U : Finset (VType m p q))
    (xA : ∀ i : Fin m, Fin (p i) → K) (xB : ∀ i : Fin m, Fin (q i) → K) :
    (∏ v ∈ U, eV (xA, xB) v) =
      (∏ i : Fin m, ∏ j ∈ UA U i, xA i j) * (∏ i : Fin m, ∏ j ∈ UB U i, xB i j) := by
  have hL : (∏ v ∈ U, eV (xA, xB) v) =
      ∏ v : VType m p q, if v ∈ U then eV (xA, xB) v else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hL, Fintype.prod_sum_type, Fintype.prod_sigma, Fintype.prod_sigma]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    rfl

private lemma sum_Fiber_prod {m : ℕ} {p q : Fin m → ℕ} (α β : Fin m → K)
    (U : Finset (VType m p q)) :
    (∑ x ∈ Fiber α β, ∏ v ∈ U, x v) =
      (∏ i ∈ S_full U, α i) * (∏ i ∈ R_full U, β i) := by
  rw [Fiber, Finset.sum_map]
  simp only [Equiv.toEmbedding_apply]
  rw [Finset.sum_product]
  simp_rw [prod_eV]
  rw [← Finset.sum_mul_sum]
  rw [← Finset.prod_univ_sum (t := fun i : Fin m => BFib (p i) (α i))
      (f := fun (i : Fin m) (z : Fin (p i) → K) => ∏ j ∈ UA U i, z j),
    ← Finset.prod_univ_sum (t := fun i : Fin m => BFib (q i) (β i))
      (f := fun (i : Fin m) (z : Fin (q i) → K) => ∏ j ∈ UB U i, z j)]
  simp_rw [block_fiber_sum]
  congr 1
  · rw [← Finset.prod_filter]
    rfl
  · rw [← Finset.prod_filter]
    rfl

private lemma card_Fiber_z2 {m : ℕ} {p q : Fin m → ℕ} (hpq : ∀ i, 0 < p i ∧ 0 < q i)
    (α β : Fin m → K) : ((Fiber (p := p) (q := q) α β).card : K) = 1 := by
  have h := sum_Fiber_prod (p := p) (q := q) α β ∅
  simp only [Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hS : S_full (p := p) (q := q) ∅ = ∅ := by
    ext i
    simp only [S_full, UA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    intro heq
    have h0 : (⟨0, (hpq i).1⟩ : Fin (p i)) ∈ (Finset.univ : Finset (Fin (p i))) :=
      Finset.mem_univ _
    rw [← heq] at h0
    simp at h0
  have hR : R_full (p := p) (q := q) ∅ = ∅ := by
    ext i
    simp only [R_full, UB, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
      iff_false]
    intro heq
    have h0 : (⟨0, (hpq i).2⟩ : Fin (q i)) ∈ (Finset.univ : Finset (Fin (q i))) :=
      Finset.mem_univ _
    rw [← heq] at h0
    simp at h0
  rw [hS, hR] at h
  simpa using h

private lemma eval_a_of_mem_Fiber {m : ℕ} {p q : Fin m → ℕ} {α β : Fin m → K}
    {x : VType m p q → K} (hx : x ∈ Fiber α β) (i : Fin m) :
    eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) = α i := by
  rw [Fiber, Finset.mem_map] at hx
  rcases hx with ⟨⟨xA, xB⟩, hmem, rfl⟩
  rw [Finset.mem_product] at hmem
  have hA := (Fintype.mem_piFinset.mp hmem.1) i
  rw [BFib, Finset.mem_filter] at hA
  simp only [map_prod, eval_X, Equiv.toEmbedding_apply, eV, Equiv.coe_fn_mk, Sum.elim_inl]
  exact hA.2

private lemma eval_b_of_mem_Fiber {m : ℕ} {p q : Fin m → ℕ} {α β : Fin m → K}
    {x : VType m p q → K} (hx : x ∈ Fiber α β) (i : Fin m) :
    eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩)) = β i := by
  rw [Fiber, Finset.mem_map] at hx
  rcases hx with ⟨⟨xA, xB⟩, hmem, rfl⟩
  rw [Finset.mem_product] at hmem
  have hB := (Fintype.mem_piFinset.mp hmem.2) i
  rw [BFib, Finset.mem_filter] at hB
  simp only [map_prod, eval_X, Equiv.toEmbedding_apply, eV, Equiv.coe_fn_mk, Sum.elim_inr]
  exact hB.2

private noncomputable def F_macro {m : ℕ} {p q : Fin m → ℕ}
    (s : MvPolynomial (VType m p q) K) (α β : Fin m → K) : K :=
  ∑ x ∈ Fiber α β, eval x s

private lemma F_macro_eq {m : ℕ} {p q : Fin m → ℕ}
    (s : MvPolynomial (VType m p q) K) (α β : Fin m → K) :
    F_macro s α β = ∑ U : Finset (VType m p q),
      coeffs s U * ((∏ i ∈ S_full U, α i) * (∏ i ∈ R_full U, β i)) := by
  unfold F_macro
  simp_rw [eval_eq_sum_coeffs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [← Finset.mul_sum, sum_Fiber_prod]

private def SubCube {m : ℕ} (T₀ : Finset (Fin m)) : Finset (Fin m → K) :=
  Fintype.piFinset (fun i : Fin m => if i ∈ T₀ then (Finset.univ : Finset K) else {0})

private lemma sum_SubCube_indicator {m : ℕ} {T₀ : Finset (Fin m)} (hT₀ : T₀.Nonempty) :
    (∑ β ∈ SubCube T₀, if β = 0 then (0 : K) else 1) = 1 := by
  have h0mem : (0 : Fin m → K) ∈ SubCube T₀ := by
    rw [SubCube, Fintype.mem_piFinset]
    intro i
    by_cases hi : i ∈ T₀ <;> simp [hi]
  have hsplit := Finset.add_sum_erase (SubCube T₀) (fun β => if β = 0 then (0 : K) else 1) h0mem
  rw [← hsplit]
  simp only [↓reduceIte, zero_add]
  have hones : (∑ β ∈ (SubCube T₀).erase 0, if β = 0 then (0 : K) else 1) =
      (((SubCube T₀).erase 0).card : K) := by
    calc (∑ β ∈ (SubCube T₀).erase 0, if β = 0 then (0 : K) else 1)
        = ∑ _β ∈ (SubCube T₀).erase 0, (1 : K) :=
          Finset.sum_congr rfl fun β hβ => by simp [Finset.ne_of_mem_erase hβ]
      _ = (((SubCube T₀).erase 0).card : K) := by simp
  rw [hones]
  have hcard_eq : (SubCube T₀).card = 2 ^ T₀.card := by
    rw [SubCube, Fintype.card_piFinset]
    have hfac : ∀ i : Fin m,
        (if i ∈ T₀ then (Finset.univ : Finset K) else {0}).card = if i ∈ T₀ then 2 else 1 := by
      intro i
      by_cases hi : i ∈ T₀ <;> simp [hi]
    simp_rw [hfac]
    rw [← Finset.prod_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const]
  have hcard_zero : ((SubCube T₀).card : K) = 0 := by
    rw [hcard_eq, Nat.cast_pow]
    have h2 : ((2 : ℕ) : K) = 0 := by decide
    rw [h2, zero_pow hT₀.card_pos.ne']
  have hadd1 := Finset.card_erase_add_one h0mem
  have hcast : (((SubCube T₀).erase 0).card : K) + 1 = 0 := by
    have hc : (((SubCube T₀).erase 0).card + 1 : ℕ) = (SubCube T₀).card := hadd1
    rw [← Nat.cast_one, ← Nat.cast_add, hc, hcard_zero]
  rw [add_comm] at hcast
  exact z2_eq_one_of_one_add_eq_zero hcast

private lemma prod_mul_prod_z2 {m : ℕ} (S R : Finset (Fin m)) (β : Fin m → K) :
    (∏ i ∈ S, β i) * (∏ i ∈ R, β i) = ∏ i ∈ S ∪ R, β i := by
  have hS : (∏ i ∈ S, β i) = ∏ i : Fin m, if i ∈ S then β i else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hR : (∏ i ∈ R, β i) = ∏ i : Fin m, if i ∈ R then β i else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  have hU : (∏ i ∈ S ∪ R, β i) = ∏ i : Fin m, if i ∈ S ∪ R then β i else 1 := by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hS, hR, hU, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ R <;> simp [h1, h2, z2_mul_self]

private lemma sum_SubCube_prod {m : ℕ} (T₀ T' : Finset (Fin m)) :
    (∑ β ∈ SubCube T₀, ∏ i ∈ T', β i) = if T' = T₀ then 1 else 0 := by
  have h1 : (∑ β ∈ SubCube T₀, ∏ i ∈ T', β i) =
      ∑ β ∈ SubCube T₀, ∏ i : Fin m, if i ∈ T' then β i else 1 := by
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h1, SubCube, ← Finset.prod_univ_sum
    (t := fun i : Fin m => if i ∈ T₀ then (Finset.univ : Finset K) else {0})
    (f := fun i b => if i ∈ T' then b else (1 : K))]
  have hfac : ∀ i : Fin m,
      (∑ b ∈ (if i ∈ T₀ then (Finset.univ : Finset K) else {0}),
        if i ∈ T' then b else (1 : K)) =
      if (i ∈ T₀ ↔ i ∈ T') then 1 else 0 := by
    intro i
    by_cases h0 : i ∈ T₀ <;> by_cases h' : i ∈ T' <;> simp [h0, h'] <;> decide
  simp_rw [hfac]
  by_cases hEq : T' = T₀
  · subst hEq
    simp
  · simp only [hEq, ↓reduceIte]
    have hex : ∃ i : Fin m, ¬ (i ∈ T₀ ↔ i ∈ T') := by
      by_contra hall
      push_neg at hall
      apply hEq
      ext i
      exact (hall i).symm
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

private lemma select_to_fits {m d : ℕ} {p q : Fin m → ℕ} (hpq : ∀ i, 0 < p i ∧ 0 < q i)
    (hsel : ∃ s : MvPolynomial (VType m p q) K, s.totalDegree ≤ d ∧
      ∀ x : VType m p q → K,
        (∃ u : K, ∀ i,
          eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) =
            u * eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩))) →
        ∀ i,
          eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) =
            eval x s * eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩))) :
    ∀ T : Finset (Fin m), T.Nonempty → ∃ S ⊆ T, S.Nonempty ∧
      (∑ i ∈ S, p i) + (∑ i ∈ T \ S, q i) ≤ d := by
  rcases hsel with ⟨s, hs_deg, hs_sel⟩
  have hslice : ∀ β : Fin m → K,
      F_macro s β β + F_macro s 0 β = if β = 0 then 0 else 1 := by
    intro β
    by_cases hβ : β = 0
    · simp only [hβ, ↓reduceIte]
      exact z2_add_self _
    · simp only [hβ, ↓reduceIte]
      have hex : ∃ i₀ : Fin m, β i₀ ≠ 0 := by
        by_contra hall
        push_neg at hall
        apply hβ
        funext i
        exact hall i
      rcases hex with ⟨i₀, hi₀⟩
      have hβ1 : β i₀ = 1 := (z2_cases (β i₀)).resolve_left hi₀
      have hF1 : F_macro s β β = 1 := by
        unfold F_macro
        have hpt : ∀ x ∈ Fiber (p := p) (q := q) β β, eval x s = 1 := by
          intro x hx
          have hfeas : ∃ u : K, ∀ i,
              eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) =
                u * eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩)) := by
            refine ⟨1, fun i => ?_⟩
            rw [eval_a_of_mem_Fiber hx i, eval_b_of_mem_Fiber hx i, one_mul]
          have hhi := hs_sel x hfeas i₀
          rw [eval_a_of_mem_Fiber hx i₀, eval_b_of_mem_Fiber hx i₀, hβ1, mul_one] at hhi
          exact hhi.symm
        rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
        exact card_Fiber_z2 hpq β β
      have hF0 : F_macro s 0 β = 0 := by
        unfold F_macro
        have hpt : ∀ x ∈ Fiber (p := p) (q := q) 0 β, eval x s = 0 := by
          intro x hx
          have hfeas : ∃ u : K, ∀ i,
              eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) =
                u * eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩)) := by
            refine ⟨0, fun i => ?_⟩
            rw [eval_a_of_mem_Fiber hx i, eval_b_of_mem_Fiber hx i, zero_mul]
            rfl
          have hhi := hs_sel x hfeas i₀
          rw [eval_a_of_mem_Fiber hx i₀, eval_b_of_mem_Fiber hx i₀, hβ1, mul_one] at hhi
          exact hhi.symm
        rw [Finset.sum_congr rfl hpt, Finset.sum_const_zero]
      rw [hF1, hF0, add_zero]
  intro T₀ hT₀
  have hsum_eq1 : (∑ U : Finset (VType m p q), coeffs s U *
      ∑ β ∈ SubCube T₀,
        ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
          (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))) = 1 := by
    have hL : (∑ β ∈ SubCube T₀, (F_macro s β β + F_macro s 0 β)) = 1 := by
      rw [Finset.sum_congr rfl fun β _ => hslice β]
      exact sum_SubCube_indicator hT₀
    rw [← hL]
    simp_rw [F_macro_eq]
    calc ∑ U : Finset (VType m p q), coeffs s U *
          ∑ β ∈ SubCube T₀,
            ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
              (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))
        = ∑ U : Finset (VType m p q), ∑ β ∈ SubCube T₀,
            (coeffs s U * ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i)) +
              coeffs s U * ((∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))) := by
          refine Finset.sum_congr rfl fun U _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => mul_add _ _ _
      _ = ∑ β ∈ SubCube T₀, ∑ U : Finset (VType m p q),
            (coeffs s U * ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i)) +
              coeffs s U * ((∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))) :=
          Finset.sum_comm
      _ = ∑ β ∈ SubCube T₀,
            ((∑ U : Finset (VType m p q),
                coeffs s U * ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i))) +
              (∑ U : Finset (VType m p q),
                coeffs s U * ((∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i)))) := by
          refine Finset.sum_congr rfl fun β _ => Finset.sum_add_distrib
  have hexU : ∃ U : Finset (VType m p q),
      coeffs s U *
        ∑ β ∈ SubCube T₀,
          ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
            (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i)) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : (∑ U : Finset (VType m p q), coeffs s U *
        ∑ β ∈ SubCube T₀,
          ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
            (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))) = 0 :=
      Finset.sum_eq_zero fun U _ => hall U
    rw [hsum_eq1] at h0
    exact one_ne_zero h0
  rcases hexU with ⟨U, hUne⟩
  have hcoeff_ne : coeffs s U ≠ 0 := left_ne_zero_of_mul hUne
  have hinner_ne : (∑ β ∈ SubCube T₀,
      ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
        (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))) ≠ 0 :=
    right_ne_zero_of_mul hUne
  have hUdeg : U.card ≤ d := coeff_degree hs_deg hcoeff_ne
  have hSne : (S_full U).Nonempty := by
    by_contra hSe
    rw [Finset.not_nonempty_iff_eq_empty] at hSe
    apply hinner_ne
    refine Finset.sum_eq_zero fun β _ => ?_
    rw [hSe, Finset.prod_empty, Finset.prod_empty, one_mul]
    exact z2_add_self _
  have hzeroS : (∏ _i ∈ S_full U, (0 : K)) = 0 := by
    rcases hSne with ⟨i, hi⟩
    exact Finset.prod_eq_zero hi rfl
  have hinner_simp : (∑ β ∈ SubCube T₀,
      ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
        (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i))) =
      if S_full U ∪ R_full U = T₀ then 1 else 0 := by
    have h1 : ∀ β ∈ SubCube T₀,
        ((∏ i ∈ S_full U, β i) * (∏ i ∈ R_full U, β i) +
          (∏ i ∈ S_full U, (0 : K)) * (∏ i ∈ R_full U, β i)) =
        ∏ i ∈ S_full U ∪ R_full U, β i := by
      intro β _
      rw [hzeroS, zero_mul, add_zero, prod_mul_prod_z2]
    rw [Finset.sum_congr rfl h1]
    exact sum_SubCube_prod T₀ (S_full U ∪ R_full U)
  have hunion : S_full U ∪ R_full U = T₀ := by
    by_contra hneq
    rw [hinner_simp] at hinner_ne
    simp only [hneq, ↓reduceIte] at hinner_ne
    exact hinner_ne rfl
  refine ⟨S_full U, ?_, hSne, ?_⟩
  · rw [← hunion]
    exact Finset.subset_union_left
  · have hdiff_sub : T₀ \ S_full U ⊆ R_full U := by
      intro i hi
      rw [Finset.mem_sdiff, ← hunion, Finset.mem_union] at hi
      exact hi.1.resolve_left hi.2
    let A_sub : Finset (VType m p q) :=
      (S_full U).biUnion (fun i => Finset.univ.image (fun j : Fin (p i) => Sum.inl ⟨i, j⟩))
    let B_sub : Finset (VType m p q) :=
      (T₀ \ S_full U).biUnion (fun i => Finset.univ.image (fun j : Fin (q i) => Sum.inr ⟨i, j⟩))
    have hA_sub : A_sub ⊆ U := by
      intro v hv
      simp only [A_sub, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨i, hiS, j, rfl⟩
      rw [S_full, Finset.mem_filter] at hiS
      have hj : j ∈ UA U i := by
        rw [hiS.2]
        exact Finset.mem_univ j
      rw [UA, Finset.mem_filter] at hj
      exact hj.2
    have hB_sub : B_sub ⊆ U := by
      intro v hv
      simp only [B_sub, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨i, hiB, j, rfl⟩
      have hiR := hdiff_sub hiB
      rw [R_full, Finset.mem_filter] at hiR
      have hj : j ∈ UB U i := by
        rw [hiR.2]
        exact Finset.mem_univ j
      rw [UB, Finset.mem_filter] at hj
      exact hj.2
    have hdisj : Disjoint A_sub B_sub := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      simp only [A_sub, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hvA
      simp only [B_sub, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ, true_and] at hvB
      rcases hvA with ⟨_, _, _, rfl⟩
      rcases hvB with ⟨_, _, _, hEq⟩
      exact Sum.inr_ne_inl hEq
    have hA_card : A_sub.card = ∑ i ∈ S_full U, p i := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.card_image_of_injective]
        · exact Finset.card_fin (p i)
        · intro j₁ j₂ hEq
          have hs := Sum.inl.inj hEq
          exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      · intro i₁ _ i₂ _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv1 hv2
        rcases hv1 with ⟨j₁, rfl⟩
        rcases hv2 with ⟨j₂, hEq⟩
        exact hne (Sigma.mk.inj_iff.mp (Sum.inl.inj hEq)).1.symm
    have hB_card : B_sub.card = ∑ i ∈ T₀ \ S_full U, q i := by
      rw [Finset.card_biUnion]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.card_image_of_injective]
        · exact Finset.card_fin (q i)
        · intro j₁ j₂ hEq
          have hs := Sum.inr.inj hEq
          exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      · intro i₁ _ i₂ _ hne
        simp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv1 hv2
        rcases hv1 with ⟨j₁, rfl⟩
        rcases hv2 with ⟨j₂, hEq⟩
        exact hne (Sigma.mk.inj_iff.mp (Sum.inr.inj hEq)).1.symm
    calc (∑ i ∈ S_full U, p i) + (∑ i ∈ T₀ \ S_full U, q i)
        = A_sub.card + B_sub.card := by rw [hA_card, hB_card]
      _ = (A_sub ∪ B_sub).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ U.card := Finset.card_le_card (Finset.union_subset hA_sub hB_sub)
      _ ≤ d := hUdeg

end PEqualNP.Outside.L_pcx_458_aux

theorem PEqualNP.Outside.L_pcx_458 : (∀ m d : ℕ, ∀ p q : Fin m → ℕ, (∀ i, 0 < p i ∧ 0 < q i) →
  let K := ZMod 2
  let I := Fin m
  let fits := ∀ T : Finset I, T.Nonempty → ∃ S ⊆ T, S.Nonempty ∧
    (∑ i ∈ S, p i) + (∑ i ∈ T \ S, q i) ≤ d
  let select := fun (V : Type) (a b : I → MvPolynomial V K) =>
    ∃ s : MvPolynomial V K, s.totalDegree ≤ d ∧
      ∀ x : V → K, (∃ u : K, ∀ i, MvPolynomial.eval x (a i) = u * MvPolynomial.eval x (b i)) →
        ∀ i, MvPolynomial.eval x (a i) = MvPolynomial.eval x s * MvPolynomial.eval x (b i)
  let V := (Σ i : I, Fin (p i)) ⊕ (Σ i : I, Fin (q i))
  let a : I → MvPolynomial V K := fun i => ∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i,j⟩)
  let b : I → MvPolynomial V K := fun i => ∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i,j⟩)
  (select V a b ↔ fits) ∧
    ((∀ (W : Type) [Fintype W] (c e : I → MvPolynomial W K),
      (∀ i, (c i).totalDegree ≤ p i ∧ (e i).totalDegree ≤ q i) → select W c e) ↔ fits)) := by
  intro m d p q hpq
  dsimp only
  have h_fits_univ :
      (∀ T : Finset (Fin m), T.Nonempty → ∃ S ⊆ T, S.Nonempty ∧
        (∑ i ∈ S, p i) + (∑ i ∈ T \ S, q i) ≤ d) →
      ∀ (W : Type) [Fintype W] (c e : Fin m → MvPolynomial W (ZMod 2)),
        (∀ i, (c i).totalDegree ≤ p i ∧ (e i).totalDegree ≤ q i) →
        ∃ s : MvPolynomial W (ZMod 2), s.totalDegree ≤ d ∧
          ∀ x : W → ZMod 2,
            (∃ u : ZMod 2, ∀ i, MvPolynomial.eval x (c i) = u * MvPolynomial.eval x (e i)) →
            ∀ i, MvPolynomial.eval x (c i) = MvPolynomial.eval x s * MvPolynomial.eval x (e i) := by
    intro hfits W _ c e hce
    exact PEqualNP.Outside.L_pcx_458_aux.fits_to_select hfits W c e hce
  have h_univ_spec :
      (∀ (W : Type) [Fintype W] (c e : Fin m → MvPolynomial W (ZMod 2)),
        (∀ i, (c i).totalDegree ≤ p i ∧ (e i).totalDegree ≤ q i) →
        ∃ s : MvPolynomial W (ZMod 2), s.totalDegree ≤ d ∧
          ∀ x : W → ZMod 2,
            (∃ u : ZMod 2, ∀ i, MvPolynomial.eval x (c i) = u * MvPolynomial.eval x (e i)) →
            ∀ i, MvPolynomial.eval x (c i) = MvPolynomial.eval x s * MvPolynomial.eval x (e i)) →
      ∃ s : MvPolynomial ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))) (ZMod 2),
        s.totalDegree ≤ d ∧
        ∀ x : ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))) → ZMod 2,
          (∃ u : ZMod 2, ∀ i,
            MvPolynomial.eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) =
              u * MvPolynomial.eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩))) →
          ∀ i,
            MvPolynomial.eval x (∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩)) =
              MvPolynomial.eval x s *
                MvPolynomial.eval x (∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩)) := by
    intro huniv
    refine huniv ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i)))
      (fun i => ∏ j : Fin (p i), MvPolynomial.X (Sum.inl ⟨i, j⟩))
      (fun i => ∏ j : Fin (q i), MvPolynomial.X (Sum.inr ⟨i, j⟩)) ?_
    intro i
    constructor
    · calc (∏ j : Fin (p i), (MvPolynomial.X (Sum.inl ⟨i, j⟩) :
            MvPolynomial ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))) (ZMod 2))).totalDegree
          ≤ ∑ j : Fin (p i), (MvPolynomial.X (Sum.inl ⟨i, j⟩) :
            MvPolynomial ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))) (ZMod 2)).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ = ∑ _j : Fin (p i), 1 :=
            Finset.sum_congr rfl fun j _ => MvPolynomial.totalDegree_X _
        _ = p i := by simp
    · calc (∏ j : Fin (q i), (MvPolynomial.X (Sum.inr ⟨i, j⟩) :
            MvPolynomial ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))) (ZMod 2))).totalDegree
          ≤ ∑ j : Fin (q i), (MvPolynomial.X (Sum.inr ⟨i, j⟩) :
            MvPolynomial ((Σ i : Fin m, Fin (p i)) ⊕ (Σ i : Fin m, Fin (q i))) (ZMod 2)).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ = ∑ _j : Fin (q i), 1 :=
            Finset.sum_congr rfl fun j _ => MvPolynomial.totalDegree_X _
        _ = q i := by simp
  have h_spec_fits := PEqualNP.Outside.L_pcx_458_aux.select_to_fits (d := d) hpq
  exact ⟨⟨h_spec_fits, fun h => h_univ_spec (h_fits_univ h)⟩,
    ⟨fun h => h_spec_fits (h_univ_spec h), h_fits_univ⟩⟩
