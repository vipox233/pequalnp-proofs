import Mathlib

namespace PEqualNP.Outside.L_lib_556_aux

theorem absl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Submodule ℝ E)
    [FiniteDimensional ℝ K] (n : ℕ) (N : ℝ) (h a : Fin n → E) (ha : ∀ j, a j ∈ K)
    (hframe : ∀ e : E, ∑ j, (inner ℝ (h j) e) ^ 2 ≤ N * ‖e‖ ^ 2) :
    (∑ j, inner ℝ (h j) (a j)) ^ 2 ≤ N * (Module.finrank ℝ K) * ∑ j, ‖a j‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ K
  have hexp : ∀ j, inner ℝ (h j) (a j) =
      ∑ k, inner ℝ (b k) (⟨a j, ha j⟩ : K) * inner ℝ (h j) ((b k : K) : E) := by
    intro j
    have e1 := b.sum_repr' (⟨a j, ha j⟩ : K)
    have e2 : a j = ∑ k, inner ℝ (b k) (⟨a j, ha j⟩ : K) • ((b k : K) : E) := by
      have := congrArg (fun z : K => (z : E)) e1
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm
    conv_lhs => rw [e2]
    rw [inner_sum]
    simp only [inner_smul_right]
  rw [Finset.sum_congr rfl (fun j _ => hexp j)]
  rw [← Fintype.sum_prod_type' (f := fun j k => inner ℝ (b k) (⟨a j, ha j⟩ : K) *
    inner ℝ (h j) ((b k : K) : E))]
  refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) ?_
  have hA : ∑ p : Fin n × Fin (Module.finrank ℝ K), (inner ℝ (b p.2) (⟨a p.1, ha p.1⟩ : K)) ^ 2 =
      ∑ j, ‖a j‖ ^ 2 := by
    rw [Fintype.sum_prod_type' (f := fun j k => (inner ℝ (b k) (⟨a j, ha j⟩ : K)) ^ 2)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := b.sum_sq_norm_inner_right (⟨a j, ha j⟩ : K)
    simp only [Real.norm_eq_abs, sq_abs] at this
    rw [this]
    rfl
  have hB : ∑ p : Fin n × Fin (Module.finrank ℝ K), (inner ℝ (h p.1) ((b p.2 : K) : E)) ^ 2 ≤
      N * (Module.finrank ℝ K) := by
    rw [Fintype.sum_prod_type_right' (f := fun j k => (inner ℝ (h j) ((b k : K) : E)) ^ 2)]
    calc ∑ k, ∑ j, (inner ℝ (h j) ((b k : K) : E)) ^ 2 ≤ ∑ k : Fin (Module.finrank ℝ K), N := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          have := hframe ((b k : K) : E)
          have hn : ‖((b k : K) : E)‖ = 1 := by
            exact b.orthonormal.1 k
          rw [hn] at this
          simpa using this
      _ = N * (Module.finrank ℝ K) := by simp [mul_comm]
  rw [hA]
  have h0 : 0 ≤ ∑ j, ‖a j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  nlinarith

theorem frame (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (horth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) (x : Fin n → ℝ) :
    ∑ j, (∑ i, x i * H i j) ^ 2 = n * ∑ i, x i ^ 2 := by
  simp only [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  have : ∀ i' : Fin n, ∑ j, x i * H i j * (x i' * H i' j) = x i * x i' * (if i = i' then (n : ℝ) else 0) := by
    intro i'
    rw [← horth i i', Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [Finset.sum_congr rfl (fun i' _ => this i')]
  simp
  ring

theorem main (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ)
    (horth : ∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, ∑ j, H i j * A i j)^2 ≤ (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (LinearMap.range A.mulVecLin).map e.toLinearMap
  have hK : Module.finrank ℝ K = A.rank := by
    unfold Matrix.rank
    exact LinearEquiv.finrank_map_eq e _
  let ca : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  let ch : Fin n → EuclideanSpace ℝ (Fin n) := fun j => WithLp.toLp 2 (fun i => H i j)
  have ha : ∀ j, ca j ∈ K := by
    intro j
    refine Submodule.mem_map.mpr ⟨A.mulVec (Pi.single j 1), ⟨Pi.single j 1, rfl⟩, ?_⟩
    simp only [ca]
    rw [Matrix.mulVec_single_one]
    rfl
  have hfr : ∀ v : EuclideanSpace ℝ (Fin n), ∑ j, (inner ℝ (ch j) v) ^ 2 ≤ (n : ℝ) * ‖v‖ ^ 2 := by
    intro v
    have h1 : ∀ j, inner ℝ (ch j) v = ∑ i, (WithLp.ofLp v) i * H i j := by
      intro j
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [ch, dotProduct]
    simp only [h1]
    rw [frame n H horth, EuclideanSpace.norm_sq_eq]
    simp
  have := absl K n (n : ℝ) ch ca ha hfr
  rw [hK] at this
  have hl : ∑ i, ∑ j, H i j * A i j = ∑ j, inner ℝ (ch j) (ca j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [ch, ca, dotProduct, mul_comm]
  have hr : ∑ i, ∑ j, (A i j) ^ 2 = ∑ j, ‖ca j‖ ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [EuclideanSpace.norm_sq_eq]
    simp [ca]
  rw [hl, hr]
  exact this

end PEqualNP.Outside.L_lib_556_aux

theorem PEqualNP.Outside.L_lib_556 : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ), 0 < n →
  (∀ i j, H i j = 1 ∨ H i j = -1) →
  (∀ i j, (∑ c, H i c * H j c) = if i = j then (n : ℝ) else 0) →
  ∀ A : Matrix (Fin n) (Fin n) ℝ,
    (∑ i, ∑ j, H i j * A i j)^2 ≤
      (n : ℝ) * (A.rank : ℝ) * (∑ i, ∑ j, (A i j)^2) := by
  intro n H _ _ horth A
  exact PEqualNP.Outside.L_lib_556_aux.main n H horth A
