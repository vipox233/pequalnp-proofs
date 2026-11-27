import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_762 : (∀ (F : Type) [Field F] (n m r : ℕ) (A : Matrix (Fin n) (Fin m) F),
  A.rank ≤ r ↔
    ∃ (u : Fin r → Fin n → F) (v : Fin r → Fin m → F), ∀ i j, A i j = ∑ k, u k i * v k j) := by
  intro F _ n m r A
  constructor
  · intro h
    let s := LinearMap.range A.mulVecLin
    have hd : Module.finrank F s = A.rank := rfl
    let b := Module.finBasis F s
    have col : ∀ j, (fun i => A i j) ∈ s := fun j =>
      ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec_single]⟩
    let c : Fin m → s := fun j => ⟨_, col j⟩
    refine ⟨fun k i => if hk : (k : ℕ) < Module.finrank F s then (b ⟨k, hk⟩ : Fin n → F) i else 0,
      fun k j => if hk : (k : ℕ) < Module.finrank F s then b.repr (c j) ⟨k, hk⟩ else 0, ?_⟩
    intro i j
    have e := congrArg (fun x : s => (x : Fin n → F) i) (b.sum_repr (c j))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at e
    let f : ℕ → F := fun k => if hk : k < Module.finrank F s then
      (b ⟨k, hk⟩ : Fin n → F) i * b.repr (c j) ⟨k, hk⟩ else 0
    have lhs : A i j = ∑ k ∈ Finset.range (Module.finrank F s), f k := by
      change (c j : Fin n → F) i = _
      rw [← e, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [f, k.isLt, dite_true, Fin.eta]
      ring
    have rhs : (∑ k : Fin r, (if hk : (k : ℕ) < Module.finrank F s then
        (b ⟨k, hk⟩ : Fin n → F) i else 0) *
        (if hk : (k : ℕ) < Module.finrank F s then b.repr (c j) ⟨k, hk⟩ else 0)) =
        ∑ k ∈ Finset.range r, f k := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [f]
      split_ifs <;> simp
    rw [rhs, lhs]
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · intro k _ hk
      simp only [Finset.mem_range] at hk
      simp [f, hk]
  · rintro ⟨u, v, huv⟩
    let U : Matrix (Fin n) (Fin r) F := Matrix.of fun i k => u k i
    let V : Matrix (Fin r) (Fin m) F := Matrix.of fun k j => v k j
    have hA : A = U * V := by
      ext i j
      rw [huv i j, Matrix.mul_apply]
      rfl
    rw [hA]
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_width U)
