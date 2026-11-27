import Mathlib

namespace PEqualNP.Outside.L_lib_604_aux

theorem fred (m n : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod 2)) (b : Fin m → ZMod 2)
    (h : ¬ ∃ x : Fin n → ZMod 2, A.mulVec x = b) :
    ∃ y : Fin m → ZMod 2, A.vecMul y = 0 ∧ dotProduct y b = 1 := by
  have hb : b ∉ LinearMap.range A.mulVecLin := by
    rintro ⟨x, hx⟩
    exact h ⟨x, by simpa using hx⟩
  obtain ⟨f, hfb, hf⟩ := Submodule.exists_le_ker_of_notMem hb
  have key : ∀ v : Fin m → ZMod 2, dotProduct (fun i => f (Pi.single i 1)) v = f v := by
    intro v
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    unfold dotProduct
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hs : (Pi.single i (v i) : Fin m → ZMod 2) = v i • Pi.single i (1 : ZMod 2) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [hs, map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
  · funext j
    have h1 : A.vecMul (fun i => f (Pi.single i 1)) j = f (fun i => A i j) := key (fun i => A i j)
    have hmem : (fun i => A i j) ∈ LinearMap.range A.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      funext i
      simp
    rw [h1]
    simpa using hf hmem
  · rw [key]
    exact (show ∀ a : ZMod 2, a ≠ 0 → a = 1 by decide) _ hfb

theorem z01 (t : ZMod 2) : t = 0 ∨ t = 1 := by
  revert t; decide

theorem cert_of {m n : ℕ} (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2) (R : Finset (Fin m))
    (h : ¬ ∃ x : Fin n → ZMod 2, ∀ e ∈ R, (∑ j, row e j * x j) = rhs e) :
    ∃ S ⊆ R, (∀ j : Fin n, S.sum (fun e => row e j) = 0) ∧ S.sum rhs = 1 := by
  classical
  let A : Matrix (Fin m) (Fin n) (ZMod 2) := Matrix.of fun e j => if e ∈ R then row e j else 0
  let b : Fin m → ZMod 2 := fun e => if e ∈ R then rhs e else 0
  have hA : ¬ ∃ x : Fin n → ZMod 2, A.mulVec x = b := by
    rintro ⟨x, hx⟩
    apply h
    refine ⟨x, fun e he => ?_⟩
    have := congrFun hx e
    simp only [A, b, Matrix.mulVec, dotProduct, Matrix.of_apply, if_pos he] at this
    exact this
  obtain ⟨y, hy, hyb⟩ := fred m n A b hA
  have conv : ∀ f : Fin m → ZMod 2, (R.filter (fun e => y e = 1)).sum f =
      ∑ e, y e * (if e ∈ R then f e else 0) := by
    intro f
    rw [Finset.sum_filter]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun e => e ∈ R)]
    have h2 : ∑ e ∈ Finset.univ.filter (fun e => e ∉ R), y e * (if e ∈ R then f e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      simp only [Finset.mem_filter] at he
      simp [he.2]
    rw [h2, add_zero, Finset.filter_mem_eq_inter, Finset.univ_inter]
    apply Finset.sum_congr rfl
    intro e he
    rw [if_pos he]
    rcases z01 (y e) with h0 | h1
    · simp [h0]
    · simp [h1]
  refine ⟨R.filter (fun e => y e = 1), Finset.filter_subset _ _, fun j => ?_, ?_⟩
  · rw [conv]
    have := congrFun hy j
    simp only [Matrix.vecMul, dotProduct, A, Matrix.of_apply, Pi.zero_apply] at this
    exact this
  · rw [conv]
    simpa [dotProduct, b] using hyb

theorem sum_symm {m : ℕ} (f : Fin m → ZMod 2) (S T : Finset (Fin m)) :
    (symmDiff S T).sum f = S.sum f + T.sum f := by
  classical
  have h : ∀ X : Finset (Fin m), X.sum f = ∑ e, (if e ∈ X then f e else 0) := by
    intro X
    rw [← Finset.sum_filter]
    congr 1
    ext
    simp
  rw [h, h S, h T, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  by_cases hs : e ∈ S <;> by_cases ht : e ∈ T <;> simp [Finset.mem_symmDiff, hs, ht, hz]

theorem main {n m : ℕ} (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2)
    (hinc : ¬ ∃ x : Fin n → ZMod 2, ∀ e ∈ (Finset.univ : Finset (Fin m)), (∑ j, row e j * x j) = rhs e)
    (hdel : ∀ e : Fin m, ¬ ∃ x : Fin n → ZMod 2, ∀ e' ∈ Finset.univ.erase e,
      (∑ j, row e' j * x j) = rhs e') :
    let W := Finset.univ.filter (fun indices : Finset (Fin m) =>
      (∀ j : Fin n, indices.sum (fun e => row e j) = 0) ∧ indices.sum rhs = 1)
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  classical
  intro W
  have memW : ∀ D, D ∈ W ↔ (∀ j : Fin n, D.sum (fun e => row e j) = 0) ∧ D.sum rhs = 1 := by
    intro D
    simp [W]
  have hne : W.Nonempty := by
    obtain ⟨S, _, hS⟩ := cert_of row rhs Finset.univ hinc
    exact ⟨S, (memW S).2 hS⟩
  have half : ∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card := by
    intro e he
    obtain ⟨S1, hS1, heS1⟩ := Finset.mem_biUnion.1 he
    obtain ⟨S0, hS0sub, hS0⟩ := cert_of row rhs (Finset.univ.erase e) (hdel e)
    have heS0 : e ∉ S0 := fun h => by simpa using hS0sub h
    have hS1' := (memW S1).1 hS1
    set T := symmDiff S0 S1 with hT
    have heT : e ∈ T := by
      rw [hT, Finset.mem_symmDiff]
      exact Or.inr ⟨heS1, heS0⟩
    have hphi : ∀ D ∈ W, symmDiff D T ∈ W := by
      intro D hD
      have hD' := (memW D).1 hD
      rw [memW]
      constructor
      · intro j
        rw [sum_symm, hT, sum_symm, hD'.1 j, hS0.1 j, hS1'.1 j]
        decide
      · rw [sum_symm, hT, sum_symm, hD'.2, hS0.2, hS1'.2]
        decide
    have hcard : (W.filter (fun subset => e ∈ subset)).card =
        (W.filter (fun subset => ¬ e ∈ subset)).card := by
      apply Finset.card_nbij' (fun D => symmDiff D T) (fun D => symmDiff D T)
      · intro D hD
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hD ⊢
        refine ⟨hphi D hD.1, ?_⟩
        rw [Finset.mem_symmDiff]
        tauto
      · intro D hD
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at hD ⊢
        refine ⟨hphi D hD.1, ?_⟩
        rw [Finset.mem_symmDiff]
        tauto
      · intro D _
        exact symmDiff_symmDiff_cancel_right T D
      · intro D _
        exact symmDiff_symmDiff_cancel_right T D
    have := Finset.card_filter_add_card_filter_not (s := W) (fun subset => e ∈ subset)
    omega
  refine ⟨hne, half, fun w => ?_⟩
  set U := W.biUnion id with hU
  have hsub : ∀ D ∈ W, D ⊆ U := fun D hD x hx => Finset.mem_biUnion.2 ⟨D, hD, hx⟩
  have hdouble : W.sum (fun support => support.sum w) =
      U.sum (fun e => w e * (W.filter (fun subset => e ∈ subset)).card) := by
    calc W.sum (fun support => support.sum w)
        = W.sum (fun D => U.sum (fun e => if e ∈ D then w e else 0)) := by
          apply Finset.sum_congr rfl
          intro D hD
          rw [← Finset.sum_filter]
          congr 1
          ext x
          simp only [Finset.mem_filter]
          exact ⟨fun h => ⟨hsub D hD h, h⟩, fun h => h.2⟩
      _ = U.sum (fun e => W.sum (fun D => if e ∈ D then w e else 0)) := Finset.sum_comm
      _ = U.sum (fun e => w e * (W.filter (fun subset => e ∈ subset)).card) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_comm]
  have htot : 2*W.sum (fun support => support.sum w) = W.card * U.sum w := by
    rw [hdouble, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [← half e he]
    ring
  refine ⟨htot, ?_⟩
  by_contra hcon
  push Not at hcon
  have hlt := Finset.sum_lt_sum_of_nonempty hne hcon
  rw [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hlt
  omega

end PEqualNP.Outside.L_lib_604_aux

theorem PEqualNP.Outside.L_lib_604 : ∀ (n m : ℕ) (row : Fin m → Fin n → ZMod 2) (rhs : Fin m → ZMod 2),
  let ok := fun (rows : Finset (Fin m)) => ∃ x : Fin n → ZMod 2,
    ∀ e ∈ rows, (∑ j, row e j * x j) = rhs e
  let W := Finset.univ.filter (fun indices : Finset (Fin m) =>
    (∀ j : Fin n, indices.sum (fun e => row e j) = 0) ∧ indices.sum rhs = 1)
  ¬ ok Finset.univ → (∀ e : Fin m, ¬ ok (Finset.univ.erase e)) →
    W.Nonempty ∧
    (∀ e ∈ W.biUnion id, 2*(W.filter (fun subset => e ∈ subset)).card = W.card) ∧
    ∀ w : Fin m → ℕ,
      2*W.sum (fun support => support.sum w) = W.card * (W.biUnion id).sum w ∧
      ∃ D ∈ W, 2*D.sum w ≤ (W.biUnion id).sum w := by
  intro n m row rhs ok W hinc hdel
  exact PEqualNP.Outside.L_lib_604_aux.main row rhs hinc hdel
