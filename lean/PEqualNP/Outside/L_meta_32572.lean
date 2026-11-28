import PEqualNP.Defs
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Module.Submodule.Equiv

namespace PEqualNP.Outside.L_meta_32572

open Matrix
open PEqualNP.CircuitLowerBounds PEqualNP.Represents
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open scoped BigOperators Matrix

private abbrev F := ZMod 2
private abbrev Idx (r m : ℕ) := Fin r ⊕ (Fin m ⊕ Fin r)

private def Alt {ι : Type*} (X : Matrix ι ι F) : Prop :=
  X.transpose = X ∧ ∀ i, X i i = 0

private lemma z2_add_self (a : F) : a + a = 0 := by fin_cases a <;> rfl
private lemma z2_sq (a : F) : a * a = a := by fin_cases a <;> rfl
private lemma z2_two : (2 : F) = 0 := rfl

private lemma z2_eq_zero_or_one (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma z2_add_eq_zero_iff (a b : F) : a + b = 0 ↔ a = b := by
  revert a b; decide

private lemma z2_ite_eq (x : F) : (if x = 1 then (1 : F) else 0) = x := by
  fin_cases x <;> rfl

private lemma z2_ite_mul (c a : F) : (if c = 1 then a else 0) = c * a := by
  fin_cases c <;> fin_cases a <;> rfl

private lemma mat_add_self {α β : Type*} (A : Matrix α β F) : A + A = 0 := by
  ext i j; exact z2_add_self (A i j)

private lemma mat_add_eq_zero_iff {α β : Type*} (A B : Matrix α β F) : A + B = 0 ↔ A = B := by
  constructor
  · intro h; ext i j
    exact (z2_add_eq_zero_iff _ _).mp (congrFun (congrFun h i) j)
  · rintro rfl; exact mat_add_self A

private lemma vec_add_self {α : Type*} (v : α → F) : v + v = 0 := by
  ext i; exact z2_add_self (v i)

private lemma vec_add_eq_zero_iff {α : Type*} (u v : α → F) : u + v = 0 ↔ u = v := by
  constructor
  · intro h; ext i; exact (z2_add_eq_zero_iff _ _).mp (congrFun h i)
  · rintro rfl; exact vec_add_self u

private lemma alt_entry_symm {ι : Type*} {H : Matrix ι ι F} (hH : Alt H) (i j : ι) :
    H i j = H j i := congrFun (congrFun hH.1 j) i

private lemma alt_zero {ι : Type*} : Alt (0 : Matrix ι ι F) :=
  ⟨by ext i j; rfl, fun _ => rfl⟩

private lemma alt_add {ι : Type*} {A B : Matrix ι ι F} (hA : Alt A) (hB : Alt B) :
    Alt (A + B) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Matrix.transpose_add, hA.1, hB.1]
  · change A i i + B i i = 0; rw [hA.2 i, hB.2 i, add_zero]

private lemma alt_smul {ι : Type*} (c : F) {A : Matrix ι ι F} (hA : Alt A) :
    Alt (c • A) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Matrix.transpose_smul, hA.1]
  · change c * A i i = 0; rw [hA.2 i, mul_zero]

private lemma symm_zero_diag_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (M : ι → ι → F) (hdiag : ∀ i, M i i = 0) (hsymm : ∀ i j, M i j = M j i) :
    ∑ i ∈ s, ∑ j ∈ s, M i j = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hinner : ∀ i ∈ s, ∑ j ∈ insert a s, M i j = M i a + ∑ j ∈ s, M i j := by
      intro i _
      rw [Finset.sum_insert ha]
    rw [Finset.sum_insert ha, Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ih, hdiag a,
      zero_add, add_zero]
    have hswap : ∑ i ∈ s, M i a = ∑ j ∈ s, M a j :=
      Finset.sum_congr rfl fun i _ => hsymm i a
    rw [hswap]
    exact z2_add_self _

private lemma congr_alt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix κ ι F) {H : Matrix ι ι F} (hH : Alt H) : Alt (P * H * P.transpose) := by
  classical
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.1, Matrix.mul_assoc]
  · intro k
    have hmul : (P * H * P.transpose) k k = ∑ i : ι, ∑ j : ι, P k i * H i j * P k j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hmul]
    refine symm_zero_diag_sum Finset.univ (fun i j => P k i * H i j * P k j) ?_ ?_
    · intro i
      simp [hH.2 i]
    · intro i j
      rw [alt_entry_symm hH i j]
      ring

private lemma congr_rank {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix κ ι F) (Q : Matrix ι κ F) (h : Q * P = 1) (H : Matrix ι ι F) :
    (P * H * P.transpose).rank = H.rank := by
  have ht : P.transpose * Q.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose h
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  · have hi : Q * (P * H * P.transpose) * Q.transpose = H := by
      rw [← Matrix.mul_assoc Q (P * H), ← Matrix.mul_assoc Q P, h, Matrix.one_mul,
        Matrix.mul_assoc H, ht, Matrix.mul_one]
    calc
      H.rank = (Q * (P * H * P.transpose) * Q.transpose).rank := congrArg Matrix.rank hi.symm
      _ ≤ (P * H * P.transpose).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

private def matrixCongr {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (P : Matrix κ ι F) (Q : Matrix ι κ F) (h : Q * P = 1) (g : P * Q = 1) :
    Matrix ι ι F ≃ₗ[F] Matrix κ κ F where
  toFun H := P * H * P.transpose
  invFun H := Q * H * Q.transpose
  left_inv H := by
    change Q * (P * H * P.transpose) * Q.transpose = H
    have ht : P.transpose * Q.transpose = 1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose h
    rw [← Matrix.mul_assoc Q (P * H), ← Matrix.mul_assoc Q P, h, Matrix.one_mul,
      Matrix.mul_assoc H, ht, Matrix.mul_one]
  right_inv H := by
    change P * (Q * H * Q.transpose) * P.transpose = H
    have ht : Q.transpose * P.transpose = 1 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose g
    rw [← Matrix.mul_assoc P (Q * H), ← Matrix.mul_assoc P Q, g, Matrix.one_mul,
      Matrix.mul_assoc H, ht, Matrix.mul_one]
  map_add' H J := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c H := by simp [Matrix.mul_smul, Matrix.smul_mul]

private def Nmat (r m : ℕ) : Matrix (Idx r m) (Idx r m) F
  | Sum.inl i, Sum.inr (Sum.inr j) => if i = j then 1 else 0
  | _, _ => 0

private def Cmat {r m : ℕ} (B : Matrix (Fin r) (Fin m) F)
    (K : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin m ⊕ Fin r) F :=
  fun i j => Sum.elim (B i) (K i) j

private lemma image_left {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F)
    (i : Idx r m) (j : Idx r m) :
    (Nmat r m * H) i j = Sum.elim (fun k => H (Sum.inr (Sum.inr k)) j) (fun _ => 0) i := by
  rcases i with i | (i | i) <;>
    simp [Nmat, Matrix.mul_apply, Fintype.sum_sum_type, ite_mul]

private lemma image_right {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F)
    (i : Idx r m) (j : Idx r m) :
    (H * (Nmat r m).transpose) i j =
      Sum.elim (fun k => H i (Sum.inr (Sum.inr k))) (fun _ => 0) j := by
  rcases j with j | (j | j) <;>
    simp [Nmat, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, mul_ite]

private lemma image_expand {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F) :
    (1 + Nmat r m) * H * (1 + Nmat r m).transpose + H =
      Nmat r m * H + H * (Nmat r m).transpose + Nmat r m * H * (Nmat r m).transpose := by
  have hh : H + H = 0 := mat_add_self H
  calc
    _ = H + H + (Nmat r m * H + H * (Nmat r m).transpose + Nmat r m * H * (Nmat r m).transpose) := by
      simp only [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, one_mul, mul_one]
      abel
    _ = _ := by rw [hh, zero_add]

private lemma image_calc {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F) (h : Alt H) :
    (1 + Nmat r m) * H * (1 + Nmat r m).transpose + H =
      Matrix.fromBlocks
        (fun i j => H (Sum.inr (Sum.inr i)) (Sum.inl j) +
          H (Sum.inl i) (Sum.inr (Sum.inr j)) + H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)))
        (Cmat (fun i j => H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)))
          (fun i j => H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j))))
        (Cmat (fun i j => H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inl j)))
          (fun i j => H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j)))).transpose 0 := by
  rw [image_expand]
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [Matrix.add_apply, Matrix.transpose_apply, Matrix.fromBlocks,
      image_right, image_left, Cmat, alt_entry_symm h]

private def imageLift {r m : ℕ} (Q : Matrix (Fin r) (Fin r) F)
    (B : Matrix (Fin r) (Fin m) F) (K : Matrix (Fin r) (Fin r) F) :
    Matrix (Idx r m) (Idx r m) F
  | Sum.inr (Sum.inr i), Sum.inl j => Q i j
  | Sum.inl i, Sum.inr (Sum.inr j) => Q j i
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inl j) => B i j
  | Sum.inr (Sum.inl i), Sum.inr (Sum.inr j) => B j i
  | Sum.inr (Sum.inr i), Sum.inr (Sum.inr j) => K i j
  | _, _ => 0

private lemma imageBlocks {r m : ℕ} (X : Matrix (Idx r m) (Idx r m) F) :
    (∃ H, Alt H ∧ X = (1 + Nmat r m) * H * (1 + Nmat r m).transpose + H) ↔
      ∃ (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin m) F)
        (K : Matrix (Fin r) (Fin r) F),
        Alt A ∧ Alt K ∧ X = Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0 := by
  constructor
  · rintro ⟨H, hH, hX⟩
    refine ⟨_, _, _, ?_, ?_, hX.trans (image_calc H hH)⟩
    · constructor
      · ext i j
        change H (Sum.inr (Sum.inr j)) (Sum.inl i) + H (Sum.inl j) (Sum.inr (Sum.inr i)) +
          H (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr i)) =
          H (Sum.inr (Sum.inr i)) (Sum.inl j) + H (Sum.inl i) (Sum.inr (Sum.inr j)) +
          H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr j))
        rw [alt_entry_symm hH (Sum.inr (Sum.inr j)) (Sum.inl i),
          alt_entry_symm hH (Sum.inl j) (Sum.inr (Sum.inr i)),
          alt_entry_symm hH (Sum.inr (Sum.inr j)) (Sum.inr (Sum.inr i))]
        ac_rfl
      · intro i
        change H (Sum.inr (Sum.inr i)) (Sum.inl i) + H (Sum.inl i) (Sum.inr (Sum.inr i)) +
          H (Sum.inr (Sum.inr i)) (Sum.inr (Sum.inr i)) = 0
        rw [alt_entry_symm hH (Sum.inl i) (Sum.inr (Sum.inr i)), z2_add_self, hH.2, zero_add]
    · exact ⟨by ext i j; exact alt_entry_symm hH _ _, fun i => hH.2 _⟩
  · rintro ⟨A, B, K, hA, hK, hX⟩
    let Q : Matrix (Fin r) (Fin r) F := fun i j => if i < j then A i j + K i j else 0
    have hQ (i j : Fin r) : Q i j + Q j i = A i j + K i j := by
      rcases lt_trichotomy i j with h | rfl | h
      · simp [Q, h, not_lt_of_ge h.le]
      · simp [Q, hA.2, hK.2]
      · simp [Q, h, not_lt_of_ge h.le, alt_entry_symm hA j i, alt_entry_symm hK j i]
    have hLift : Alt (imageLift Q B K) := by
      constructor
      · ext i j
        rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
          simp [Matrix.transpose_apply, imageLift, alt_entry_symm hK]
      · intro i
        rcases i with i | (i | i) <;> simp [imageLift, hK.2]
    refine ⟨imageLift Q B K, hLift, ?_⟩
    rw [hX, image_calc _ hLift]
    change Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0 =
      Matrix.fromBlocks (fun i j => Q i j + Q j i + K i j) (Cmat B K) (Cmat B K).transpose 0
    have hTop : (fun i j => Q i j + Q j i + K i j) = A := by
      ext i j
      rw [hQ, add_assoc, z2_add_self, add_zero]
    rw [hTop]

private lemma squareZero_normalize {d r : ℕ} (D : Matrix (Fin d) (Fin d) F)
    (hD : D * D = 0) (hr : D.rank = r) :
    ∃ (m : ℕ) (P : Matrix (Fin d) (Idx r m) F)
      (Q : Matrix (Idx r m) (Fin d) F),
      d = r + m + r ∧ P * Q = 1 ∧ Q * P = 1 ∧ Q * D * P = Nmat r m := by
  let V := Fin d → F
  let b₀ : Module.Basis (Fin d) F V := Pi.basisFun F (Fin d)
  let f : V →ₗ[F] V := Matrix.toLin b₀ b₀ D
  let K := LinearMap.ker f
  let R := LinearMap.range f
  have hRK : R ≤ K := by
    apply LinearMap.range_le_ker_iff.mpr
    change (Matrix.toLin b₀ b₀ D).comp (Matrix.toLin b₀ b₀ D) = 0
    rw [← Matrix.toLin_mul b₀ b₀ b₀, hD, map_zero]
  let A := R.comap K.subtype
  obtain ⟨B, hAB⟩ := A.exists_isCompl
  obtain ⟨C, hKC⟩ := K.exists_isCompl
  let eA : A ≃ₗ[F] R := Submodule.comap_equiv_self_of_inj_of_le
    Subtype.val_injective (by simpa only [Submodule.range_subtype] using hRK)
  let eC : C ≃ₗ[F] R := (K.quotientEquivOfIsCompl C hKC).symm.trans f.quotKerEquivRange
  let m := Module.finrank F B
  let a : Module.Basis (Fin r) F R :=
    Module.finBasisOfFinrankEq F R ((D.rank_eq_finrank_range_toLin b₀ b₀).symm.trans hr)
  letI : Module.Finite F K := inferInstance
  letI : Module.Free F B := Module.Free.of_divisionRing F B
  let bB : Module.Basis (Fin m) F B := Module.finBasis F B
  let b : Module.Basis (Idx r m) F V :=
    (((((a.map eA.symm).prod bB).map (A.prodEquivOfIsCompl B hAB)).prod
      (a.map eC.symm)).map (K.prodEquivOfIsCompl C hKC)).reindex (Equiv.sumAssoc _ _ _)
  have hA (i : Fin r) : b (Sum.inl i) = (a i : V) := by
    calc
      b (Sum.inl i) = (((eA.symm (a i) : A) : K) : V) := by
        simp [b, Module.Basis.reindex_apply, Function.comp_apply]
      _ = (a i : V) := congrArg (fun x : R => (x : V)) (eA.apply_symm_apply (a i))
  have hB (i : Fin m) : b (Sum.inr (Sum.inl i)) = ((bB i : K) : V) := by
    simp [b, Module.Basis.reindex_apply, Function.comp_apply]
  have hC (i : Fin r) : b (Sum.inr (Sum.inr i)) = (eC.symm (a i) : V) := by
    simp [b, Module.Basis.reindex_apply, Function.comp_apply]
  have heC (x : C) : (eC x : V) = f (x : V) := by
    change (f.quotKerEquivRange (Submodule.Quotient.mk (x : V)) : V) = f (x : V)
    exact f.quotKerEquivRange_apply_mk (x : V)
  have h₁ (i : Fin r) : f (b (Sum.inl i)) = 0 := by
    rw [hA]
    exact LinearMap.mem_ker.mp (hRK (a i).property)
  have h₂ (i : Fin m) : f (b (Sum.inr (Sum.inl i))) = 0 := by
    rw [hB]
    exact LinearMap.mem_ker.mp ((bB i : K).property)
  have h₃ (i : Fin r) : f (b (Sum.inr (Sum.inr i))) = b (Sum.inl i) := by
    rw [hC, hA, ← heC, LinearEquiv.apply_symm_apply]
  have hd : d = r + m + r := by
    simpa [V, Fintype.card_sum, Nat.add_assoc, Module.finrank_fintype_fun_eq_card] using
      Module.finrank_eq_card_basis b
  refine ⟨m, b₀.toMatrix b, b.toMatrix b₀, hd, b₀.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip b₀, ?_⟩
  calc
    b.toMatrix b₀ * D * b₀.toMatrix b =
        b.toMatrix b₀ * LinearMap.toMatrix b₀ b₀ f * b₀.toMatrix b :=
      congrArg (fun T : Matrix (Fin d) (Fin d) F => b.toMatrix b₀ * T * b₀.toMatrix b)
        (LinearMap.toMatrix_toLin b₀ b₀ D).symm
    _ = LinearMap.toMatrix b b f :=
      basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b₀ b b₀ f
    _ = Nmat r m := by
      apply Matrix.ext
      intro i j
      rcases i with i | i | i <;> rcases j with j | j | j <;>
        simp [LinearMap.toMatrix_apply, h₁, h₂, h₃, Nmat, Finsupp.single_apply, eq_comm]

private lemma invol_sub_square {d : ℕ} (U : Matrix (Fin d) (Fin d) F) (hU : U * U = 1) :
    (U - 1) * (U - 1) = 0 := by
  have hn : -(1 : Matrix (Fin d) (Fin d) F) = 1 := by
    ext i j
    change -((1 : Matrix (Fin d) (Fin d) F) i j) = _
    have h := z2_add_self ((1 : Matrix (Fin d) (Fin d) F) i j)
    exact add_eq_zero_iff_neg_eq.1 h
  rw [sub_eq_add_neg U, hn, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hU, add_comm (1 : Matrix (Fin d) (Fin d) F) U]
  ext i j
  exact z2_add_self _

private def imageSet {ι : Type*} [Fintype ι] (U : Matrix ι ι F) : Set (Matrix ι ι F) :=
  {X | ∃ H, Alt H ∧ X = U * H * U.transpose + H}

private lemma image_transport_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι ι F)
    (P : Matrix ι κ F) (Q : Matrix κ ι F) (hp : P * Q = 1) (hq : Q * P = 1)
    (H : Matrix ι ι F) :
    matrixCongr Q P hp hq (U * H * U.transpose + H) =
      (Q * U * P) * matrixCongr Q P hp hq H * (Q * U * P).transpose + matrixCongr Q P hp hq H := by
  have ht : Q.transpose * P.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hp
  change Q * (U * H * U.transpose + H) * Q.transpose =
    (Q * U * P) * (Q * H * Q.transpose) * (Q * U * P).transpose + Q * H * Q.transpose
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P Q, hp, Matrix.one_mul,
    ← Matrix.mul_assoc Q.transpose P.transpose, ht, Matrix.one_mul]

private lemma image_transport {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι ι F)
    (P : Matrix ι κ F) (Q : Matrix κ ι F) (hp : P * Q = 1) (hq : Q * P = 1) :
    matrixCongr Q P hp hq '' imageSet U = imageSet (Q * U * P) := by
  let e := matrixCongr Q P hp hq
  ext X
  change X ∈ e '' imageSet U ↔ X ∈ imageSet (Q * U * P)
  constructor
  · rintro ⟨Y, ⟨H, hH, rfl⟩, rfl⟩
    exact ⟨e H, congr_alt Q hH, image_transport_eq U P Q hp hq H⟩
  · rintro ⟨J, hJ, rfl⟩
    let H := e.symm J
    have he : e H = J := e.apply_symm_apply J
    refine ⟨U * H * U.transpose + H, ⟨H, congr_alt P hJ, rfl⟩, ?_⟩
    rw [image_transport_eq U P Q hp hq H, he]

private lemma rankBlockLower {r m : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (C : Matrix (Fin r) (Fin m ⊕ Fin r) F) :
    2 * C.rank ≤ (fromBlocks A C C.transpose 0).rank := by
  classical
  let X : Matrix (Idx r m) (Idx r m) F := fromBlocks A C C.transpose 0
  change 2 * C.rank ≤ X.rank
  let L := LinearMap.range X.mulVecLin
  let R := LinearMap.range C.transpose.mulVecLin
  let U := LinearMap.range C.mulVecLin
  have hX (x : Idx r m → F) :
      X.mulVecLin x = Sum.elim (A *ᵥ (x ∘ Sum.inl) + C *ᵥ (x ∘ Sum.inr))
        (C.transpose *ᵥ (x ∘ Sum.inl)) := by
    simp [X, Matrix.mulVecLin_apply, fromBlocks_mulVec]
  let p : L →ₗ[F] (Fin m ⊕ Fin r → F) :=
    (LinearMap.funLeft F F Sum.inr).domRestrict L
  let φ : L →ₗ[F] R := p.codRestrict R (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    refine ⟨x ∘ Sum.inl, ?_⟩
    funext j
    change (C.transpose *ᵥ (x ∘ Sum.inl)) j = X.mulVecLin x (Sum.inr j)
    rw [hX] <;> rfl)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    let z : Idx r m → F := Sum.elim x 0
    refine ⟨⟨X.mulVecLin z, LinearMap.mem_range_self _ z⟩, ?_⟩
    apply Subtype.ext
    funext j
    change X.mulVecLin z (Sum.inr j) = (C.transpose *ᵥ x) j
    rw [hX] <;> rfl
  let e : (Fin r → F) →ₗ[F] (Idx r m → F) :=
    { toFun := fun x => Sum.elim x 0
      map_add' := fun x y => by funext j; cases j <;> simp
      map_smul' := fun s x => by funext j; cases j <;> simp }
  let e' : U →ₗ[F] L := (e.domRestrict U).codRestrict L (by
    rintro ⟨y, ⟨x, rfl⟩⟩
    let z : Idx r m → F := Sum.elim 0 x
    refine ⟨z, ?_⟩
    change X.mulVecLin z = Sum.elim (C *ᵥ x) 0
    rw [hX]
    have hz : z ∘ Sum.inl = 0 := rfl
    have hz' : z ∘ Sum.inr = x := rfl
    simp [hz, hz'])
  let ι : U →ₗ[F] LinearMap.ker φ := e'.codRestrict _ (by
    intro u
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    rfl)
  have hι : Function.Injective ι := by
    intro u v h
    apply Subtype.ext
    funext j
    exact congrArg (fun y : LinearMap.ker φ => y.1.1 (Sum.inl j)) h
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at hrn
  change C.transpose.rank + Module.finrank F (LinearMap.ker φ) = X.rank at hrn
  rw [rank_transpose] at hrn
  have hl := LinearMap.finrank_le_finrank_of_injective hι
  change C.rank ≤ Module.finrank F (LinearMap.ker φ) at hl
  omega

private def pairMat3 (a : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F
  | 0, 1 => a 0
  | 1, 0 => a 0
  | 0, 2 => a 1
  | 2, 0 => a 1
  | 1, 2 => a 2
  | 2, 1 => a 2
  | _, _ => 0

private def pairMat3Lin : (Fin 3 → F) →ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun := pairMat3
  map_add' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMat3]
  map_smul' c a := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMat3]

private lemma pairMat3_alt (a : Fin 3 → F) : Alt (pairMat3 a) := by
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;> rfl

private lemma pairMat3_inj : Function.Injective pairMat3Lin := by
  intro a b h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 1) 2

private lemma pairMat3_surj {A : Matrix (Fin 3) (Fin 3) F} (hA : Alt A) :
    ∃ a : Fin 3 → F, pairMat3 a = A := by
  refine ⟨![A 0 1, A 0 2, A 1 2], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · exact (hA.2 0).symm
  · rfl
  · rfl
  · exact alt_entry_symm hA 0 1
  · exact (hA.2 1).symm
  · rfl
  · exact alt_entry_symm hA 0 2
  · exact alt_entry_symm hA 1 2
  · exact (hA.2 2).symm

private def Palt : Submodule F (Matrix (Fin 3) (Fin 3) F) :=
  LinearMap.range pairMat3Lin

private lemma mem_Palt_iff (K : Matrix (Fin 3) (Fin 3) F) : K ∈ Palt ↔ Alt K := by
  constructor
  · rintro ⟨a, rfl⟩
    exact pairMat3_alt a
  · intro hK
    exact pairMat3_surj hK

private lemma finrank_Palt : Module.finrank F Palt = 3 := by
  unfold Palt
  rw [LinearMap.finrank_range_of_inj pairMat3_inj, Module.finrank_pi, Fintype.card_fin]

private abbrev WideCoord3 (m : ℕ) := Fin 3 ⊕ (Fin 3 × Fin m) ⊕ Fin 3

private def wideMap3 (m : ℕ) : (WideCoord3 m → F) →ₗ[F] Matrix (Idx 3 m) (Idx 3 m) F where
  toFun a :=
    let A := pairMat3 (fun q => a (Sum.inl q))
    let B : Matrix (Fin 3) (Fin m) F := fun i j => a (Sum.inr (Sum.inl (i, j)))
    let K := pairMat3 (fun q => a (Sum.inr (Sum.inr q)))
    Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0
  map_add' a b := by
    ext (i | (i | i)) (j | (j | j))
    · fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, pairMat3]
    · simp [Matrix.fromBlocks, Cmat]
    · fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Cmat, pairMat3]
    · simp [Matrix.fromBlocks, Cmat, Matrix.transpose_apply]
    · simp [Matrix.fromBlocks]
    · simp [Matrix.fromBlocks]
    · fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Cmat, Matrix.transpose_apply, pairMat3]
    · simp [Matrix.fromBlocks]
    · simp [Matrix.fromBlocks]
  map_smul' c a := by
    ext (i | (i | i)) (j | (j | j))
    · fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, pairMat3]
    · simp [Matrix.fromBlocks, Cmat]
    · fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Cmat, pairMat3]
    · simp [Matrix.fromBlocks, Cmat, Matrix.transpose_apply]
    · simp [Matrix.fromBlocks]
    · simp [Matrix.fromBlocks]
    · fin_cases i <;> fin_cases j <;> simp [Matrix.fromBlocks, Cmat, Matrix.transpose_apply, pairMat3]
    · simp [Matrix.fromBlocks]
    · simp [Matrix.fromBlocks]

private lemma wideMap3_inj (m : ℕ) : Function.Injective (wideMap3 m) := by
  intro a b h
  have hA : pairMat3Lin (fun q => a (Sum.inl q)) = pairMat3Lin (fun q => b (Sum.inl q)) := by
    ext i j
    exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  have hK : pairMat3Lin (fun q => a (Sum.inr (Sum.inr q))) =
      pairMat3Lin (fun q => b (Sum.inr (Sum.inr q))) := by
    ext i j
    exact congrFun (congrFun h (Sum.inl i)) (Sum.inr (Sum.inr j))
  funext x
  rcases x with q | (⟨i, j⟩ | q)
  · exact congrFun (pairMat3_inj hA) q
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inr (Sum.inl j))
  · exact congrFun (pairMat3_inj hK) q

private def Wfull (m : ℕ) : Submodule F (Matrix (Idx 3 m) (Idx 3 m) F) :=
  LinearMap.range (wideMap3 m)

private lemma mem_Wfull_iff {m : ℕ} (X : Matrix (Idx 3 m) (Idx 3 m) F) :
    X ∈ Wfull m ↔
      ∃ (A : Matrix (Fin 3) (Fin 3) F) (B : Matrix (Fin 3) (Fin m) F)
        (K : Matrix (Fin 3) (Fin 3) F),
        Alt A ∧ Alt K ∧ X = Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, _, _, pairMat3_alt _, pairMat3_alt _, rfl⟩
  · rintro ⟨A, B, K, hA, hK, rfl⟩
    obtain ⟨a, rfl⟩ := pairMat3_surj hA
    obtain ⟨k, rfl⟩ := pairMat3_surj hK
    exact ⟨Sum.elim a (Sum.elim (fun p : Fin 3 × Fin m => B p.1 p.2) k), rfl⟩

private lemma finrank_Wfull (m : ℕ) : Module.finrank F (Wfull m) = 3 * m + 6 := by
  unfold Wfull
  rw [LinearMap.finrank_range_of_inj (wideMap3_inj m), Module.finrank_pi]
  simp only [WideCoord3, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

private lemma finrank_sup_le' {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (U W : Submodule F V) :
    Module.finrank F (U ⊔ W : Submodule F V) ≤ Module.finrank F U + Module.finrank F W := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U W
  omega

private lemma eq_of_le_of_finrank_ge' {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {U W : Submodule F V} (hle : U ≤ W) (hge : Module.finrank F W ≤ Module.finrank F U) :
    U = W :=
  Submodule.eq_of_le_of_finrank_eq hle (le_antisymm (Submodule.finrank_mono hle) hge)

private def WSub {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F)) :
    Submodule F (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
  { carrier := {X | ∃ A K : Matrix (Fin n) (Fin n) F,
      Alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)}
    zero_mem' := ⟨0, 0, alt_zero, P.zero_mem, by ext i j; cases i <;> cases j <;> rfl⟩
    smul_mem' := by
      rintro c _ ⟨A, K, hA, hK, rfl⟩
      refine ⟨c • A, c • K, alt_smul c hA, P.smul_mem c hK, ?_⟩
      rw [Matrix.fromBlocks_smul, smul_zero]
    , add_mem' := by
      rintro _ _ ⟨A₁, K₁, hA₁, hK₁, rfl⟩ ⟨A₂, K₂, hA₂, hK₂, rfl⟩
      refine ⟨A₁ + A₂, K₁ + K₂, alt_add hA₁ hA₂, P.add_mem hK₁ hK₂, ?_⟩
      rw [Matrix.fromBlocks_add, add_zero] }

private def crossLin (n : ℕ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F →ₗ[F] Matrix (Fin n) (Fin n) F where
  toFun X i j := X (Sum.inl i) (Sum.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma crossLin_fromBlocks {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) :
    crossLin n (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)) = K := by
  ext i j; rfl

private noncomputable def colSp {α β : Type*} [Fintype β] (A : Matrix α β F) : Submodule F (α → F) :=
  LinearMap.range A.mulVecLin

private lemma rank_eq_finrank_colSp {α β : Type*} [Fintype β] (A : Matrix α β F) :
    A.rank = Module.finrank F (colSp A) := rfl

private lemma colSp_add_le {α β : Type*} [Fintype β] (A B : Matrix α β F) :
    colSp (A + B) ≤ colSp A ⊔ colSp B := by
  rintro y ⟨x, rfl⟩
  change (A + B) *ᵥ x ∈ colSp A ⊔ colSp B
  rw [Matrix.add_mulVec]
  exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩

private lemma rank_add_le {α β : Type*} [Fintype α] [Fintype β] (A B : Matrix α β F) :
    (A + B).rank ≤ A.rank + B.rank := by
  rw [rank_eq_finrank_colSp, rank_eq_finrank_colSp, rank_eq_finrank_colSp]
  exact (Submodule.finrank_mono (colSp_add_le A B)).trans (finrank_sup_le' _ _)

private lemma colSp_add_eq_sup_of_rank_eq {α β : Type*} [Fintype α] [Fintype β] (A B : Matrix α β F)
    (h : (A + B).rank = A.rank + B.rank) :
    colSp (A + B) = colSp A ⊔ colSp B := by
  apply eq_of_le_of_finrank_ge' (colSp_add_le A B)
  have h1 : Module.finrank F (colSp A ⊔ colSp B : Submodule F (α → F)) ≤ A.rank + B.rank :=
    finrank_sup_le' (colSp A) (colSp B)
  rw [rank_eq_finrank_colSp] at h
  omega

private def piBot (n : ℕ) : (Fin n ⊕ Fin n → F) →ₗ[F] (Fin n → F) where
  toFun v := v ∘ Sum.inr
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def injTop (n : ℕ) : (Fin n → F) →ₗ[F] (Fin n ⊕ Fin n → F) where
  toFun u := Sum.elim u 0
  map_add' u v := by ext i; cases i <;> simp
  map_smul' c u := by ext i; cases i <;> simp

private lemma injTop_injective (n : ℕ) : Function.Injective (injTop n) := by
  intro u v h
  ext i
  exact congrFun h (Sum.inl i)

private lemma fromBlocks_mulVec_inl {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) (v : Fin n ⊕ Fin n → F)
    (i : Fin n) :
    (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F) *ᵥ v) (Sum.inl i) =
      (A *ᵥ (v ∘ Sum.inl)) i + (K *ᵥ (v ∘ Sum.inr)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private lemma fromBlocks_mulVec_inr {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) (v : Fin n ⊕ Fin n → F)
    (i : Fin n) :
    (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F) *ᵥ v) (Sum.inr i) =
      (K *ᵥ (v ∘ Sum.inl)) i := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

private lemma map_piBot_colSp_fromBlocks {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) :
    (colSp (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F))).map (piBot n) = colSp K := by
  ext y
  simp only [Submodule.mem_map, colSp, LinearMap.mem_range, Matrix.mulVecLin_apply]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨v ∘ Sum.inl, ?_⟩
    ext i
    exact (fromBlocks_mulVec_inr A K v i).symm
  · rintro ⟨u, rfl⟩
    refine ⟨Matrix.fromBlocks A K K 0 *ᵥ Sum.elim u 0, ⟨Sum.elim u 0, rfl⟩, ?_⟩
    ext i
    exact fromBlocks_mulVec_inr A K (Sum.elim u 0) i

private lemma two_mul_rank_le_rank_fromBlocks {n : ℕ} (A K : Matrix (Fin n) (Fin n) F) :
    2 * K.rank ≤ (Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)).rank := by
  set X := Matrix.fromBlocks A K K (0 : Matrix (Fin n) (Fin n) F)
  let φ : colSp X →ₗ[F] (Fin n → F) := (piBot n).domRestrict (colSp X)
  have hrm := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : LinearMap.range φ = colSp K := by
    rw [← map_piBot_colSp_fromBlocks A K]
    ext y
    simp only [φ, LinearMap.mem_range, LinearMap.domRestrict_apply, Subtype.exists, exists_prop,
      Submodule.mem_map]
    rfl
  have hr : Module.finrank F (LinearMap.range φ) = K.rank := by
    rw [hrange, rank_eq_finrank_colSp]
  have hmem : ∀ y ∈ colSp K, injTop n y ∈ colSp X := by
    rintro y ⟨u, rfl⟩
    refine ⟨Sum.elim 0 u, ?_⟩
    ext i
    cases i with
    | inl i =>
      change (X *ᵥ Sum.elim 0 u) (Sum.inl i) = (K *ᵥ u) i
      rw [fromBlocks_mulVec_inl]
      have h0 : Sum.elim (0 : Fin n → F) u ∘ Sum.inl = 0 := rfl
      have h1 : Sum.elim (0 : Fin n → F) u ∘ Sum.inr = u := rfl
      rw [h0, h1, Matrix.mulVec_zero, Pi.zero_apply, zero_add]
    | inr i =>
      change (X *ᵥ Sum.elim 0 u) (Sum.inr i) = 0
      rw [fromBlocks_mulVec_inr]
      have h0 : Sum.elim (0 : Fin n → F) u ∘ Sum.inl = 0 := rfl
      rw [h0, Matrix.mulVec_zero, Pi.zero_apply]
  let ψ : colSp K →ₗ[F] LinearMap.ker φ :=
    { toFun := fun y => ⟨⟨injTop n y.1, hmem y.1 y.2⟩, by
        change piBot n (injTop n y.1) = 0
        ext i; rfl⟩
      map_add' := fun x y => by ext i; cases i <;> simp [injTop]
      map_smul' := fun c x => by ext i; cases i <;> simp [injTop] }
  have hψinj : Function.Injective ψ := by
    intro x y h
    apply Subtype.ext
    apply injTop_injective n
    exact congrArg (fun z => z.1.1) h
  have hk : K.rank ≤ Module.finrank F (LinearMap.ker φ) := by
    rw [rank_eq_finrank_colSp]
    exact LinearMap.finrank_le_finrank_of_injective hψinj
  change 2 * K.rank ≤ Module.finrank F (colSp X)
  omega

private lemma rank_ne_zero_of_ne_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) F} (hK : K ≠ 0) :
    K.rank ≠ 0 := by
  intro hr
  apply hK
  have hbot : colSp K = ⊥ := Submodule.finrank_eq_zero.mp hr
  ext i j
  have hcol : K *ᵥ Pi.single j (1 : F) ∈ colSp K := ⟨Pi.single j 1, rfl⟩
  rw [hbot, Submodule.mem_bot] at hcol
  have hi := congrFun hcol i
  simpa [Matrix.mulVec_single] using hi

private lemma rank_ne_one_of_alt {n : ℕ} {K : Matrix (Fin n) (Fin n) F} (hK : Alt K) :
    K.rank ≠ 1 := by
  intro hr
  have hne : colSp K ≠ ⊥ := by
    intro hb
    rw [rank_eq_finrank_colSp, hb, finrank_bot] at hr
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : Submodule.span F {u} = colSp K := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa using hu)
    · rw [finrank_span_singleton hu0, ← rank_eq_finrank_colSp, hr]
  have hcol : ∀ j : Fin n, ∃ c : F, ∀ i : Fin n, K i j = c * u i := by
    intro j
    have hm : K *ᵥ Pi.single j (1 : F) ∈ Submodule.span F {u} := by
      rw [hsp]; exact ⟨Pi.single j 1, rfl⟩
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨c, fun i => ?_⟩
    have hi := congrFun hc i
    simpa [Matrix.mulVec_single, mul_comm] using hi.symm
  choose c hc using hcol
  have hK0 : K ≠ 0 := by
    intro h0; rw [h0, Matrix.rank_zero] at hr; omega
  have hex : ∃ i₀ j₀ : Fin n, K i₀ j₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hK0 (Matrix.ext hall)
  obtain ⟨i₀, j₀, hij⟩ := hex
  have h1 : c j₀ * u i₀ ≠ 0 := by rwa [← hc j₀ i₀]
  have hui : u i₀ = 1 := by
    rcases z2_eq_zero_or_one (u i₀) with h | h
    · exfalso; apply h1; simp [h]
    · exact h
  have hsym : K j₀ i₀ = K i₀ j₀ := congrFun (congrFun hK.1 i₀) j₀
  have h2 : c i₀ * u j₀ ≠ 0 := by rwa [← hc i₀ j₀, hsym]
  have hci : c i₀ = 1 := by
    rcases z2_eq_zero_or_one (c i₀) with h | h
    · exfalso; apply h2; simp [h]
    · exact h
  have hdiag : K i₀ i₀ = 0 := hK.2 i₀
  rw [hc i₀ i₀, hci, hui, mul_one] at hdiag
  exact one_ne_zero hdiag

private lemma two_le_rank_of_alt_ne_zero {n : ℕ} {K : Matrix (Fin n) (Fin n) F}
    (hK : Alt K) (hne : K ≠ 0) : 2 ≤ K.rank := by
  have h0 := rank_ne_zero_of_ne_zero hne
  have h1 := rank_ne_one_of_alt hK
  omega

private def wedge {n : ℕ} (u v : Fin n → F) : Matrix (Fin n) (Fin n) F :=
  fun i j => u i * v j + v i * u j

private lemma wedge_mulVec {n : ℕ} (u v x : Fin n → F) :
    wedge u v *ᵥ x = (dotProduct v x) • u + (dotProduct u x) • v := by
  ext i
  simp only [Matrix.mulVec, dotProduct, wedge, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma wedge_add_right {n : ℕ} (w a b : Fin n → F) :
    wedge w a + wedge w b = wedge w (a + b) := by
  ext i j
  simp only [Matrix.add_apply, wedge, Pi.add_apply]
  ring

private lemma exists_det_one_of_pair {n : ℕ} {u v : Fin n → F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∃ i₁ i₂ : Fin n, u i₁ * v i₂ + v i₁ * u i₂ = 1 := by
  have hexu : ∃ i₁, u i₁ ≠ 0 := by
    by_contra h; push Not at h; exact hu (funext h)
  obtain ⟨i₁, hi₁⟩ := hexu
  have hui₁ : u i₁ = 1 := (z2_eq_zero_or_one (u i₁)).resolve_left hi₁
  rcases z2_eq_zero_or_one (v i₁) with hvi₁ | hvi₁
  · have hexv : ∃ i₂, v i₂ ≠ 0 := by
      by_contra h; push Not at h; exact hv (funext h)
    obtain ⟨i₂, hi₂⟩ := hexv
    have hvi₂ : v i₂ = 1 := (z2_eq_zero_or_one (v i₂)).resolve_left hi₂
    exact ⟨i₁, i₂, by rw [hui₁, hvi₂, hvi₁]; simp⟩
  · have hexne : ∃ i₂, u i₂ ≠ v i₂ := by
      by_contra h; push Not at h; exact huv (funext h)
    obtain ⟨i₂, hi₂⟩ := hexne
    refine ⟨i₁, i₂, ?_⟩
    rw [hui₁, hvi₁, one_mul, one_mul]
    rcases z2_eq_zero_or_one (u i₂) with h1 | h1 <;>
    rcases z2_eq_zero_or_one (v i₂) with h2 | h2 <;>
    simp_all

private lemma colSp_wedge {n : ℕ} {u v : Fin n → F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    colSp (wedge u v) = Submodule.span F ({u, v} : Set (Fin n → F)) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    change wedge u v *ᵥ x ∈ _
    rw [wedge_mulVec]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · obtain ⟨i₁, i₂, hdet⟩ := exists_det_one_of_pair hu hv huv
    rw [Submodule.span_le]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with hyu | hyv
    · rw [hyu]
      refine ⟨u i₂ • Pi.single i₁ 1 + u i₁ • Pi.single i₂ 1, ?_⟩
      change wedge u v *ᵥ _ = u
      rw [wedge_mulVec]
      have hdu : dotProduct u (u i₂ • Pi.single i₁ (1 : F) + u i₁ • Pi.single i₂ 1) = 0 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        rw [mul_comm (u i₂) (u i₁)]
        exact z2_add_self _
      have hdv : dotProduct v (u i₂ • Pi.single i₁ (1 : F) + u i₁ • Pi.single i₂ 1) = 1 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        calc u i₂ * v i₁ + u i₁ * v i₂ = u i₁ * v i₂ + v i₁ * u i₂ := by ring
          _ = 1 := hdet
      rw [hdu, hdv, zero_smul, one_smul, add_zero]
    · rw [Set.mem_singleton_iff.mp hyv]
      refine ⟨v i₂ • Pi.single i₁ 1 + v i₁ • Pi.single i₂ 1, ?_⟩
      change wedge u v *ᵥ _ = v
      rw [wedge_mulVec]
      have hdv : dotProduct v (v i₂ • Pi.single i₁ (1 : F) + v i₁ • Pi.single i₂ 1) = 0 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        rw [mul_comm (v i₂) (v i₁)]
        exact z2_add_self _
      have hdu : dotProduct u (v i₂ • Pi.single i₁ (1 : F) + v i₁ • Pi.single i₂ 1) = 1 := by
        simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_single, mul_one]
        calc v i₂ * u i₁ + v i₁ * u i₂ = u i₁ * v i₂ + v i₁ * u i₂ := by ring
          _ = 1 := hdet
      rw [hdu, hdv, zero_smul, one_smul, zero_add]

private lemma eq_wedge_of_alt_colSp {n : ℕ} {K : Matrix (Fin n) (Fin n) F}
    (hK : Alt K) (hKne : K ≠ 0) {u v : Fin n → F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    (hsp : colSp K = Submodule.span F ({u, v} : Set (Fin n → F))) :
    K = wedge u v := by
  obtain ⟨i₁, i₂, hdet⟩ := exists_det_one_of_pair hu hv huv
  have hcol : ∀ j : Fin n, ∃ a b : F, ∀ i : Fin n, K i j = u i * a + v i * b := by
    intro j
    have hm : K *ᵥ Pi.single j (1 : F) ∈ Submodule.span F ({u, v} : Set (Fin n → F)) := by
      rw [← hsp]; exact ⟨Pi.single j 1, rfl⟩
    rw [Submodule.mem_span_pair] at hm
    obtain ⟨a, b, hab⟩ := hm
    refine ⟨a, b, fun i => ?_⟩
    have hi := congrFun hab i
    simpa [Matrix.mulVec_single, mul_comm] using hi.symm
  choose a b hab using hcol
  have ha_eq : ∀ j : Fin n, a j = v i₂ * K i₁ j + v i₁ * K i₂ j := by
    intro j
    rw [hab j i₁, hab j i₂]
    calc a j = (u i₁ * v i₂ + v i₁ * u i₂) * a j + (v i₂ * v i₁ + v i₁ * v i₂) * b j := by
          rw [hdet, one_mul, mul_comm (v i₂) (v i₁), z2_add_self, zero_mul, add_zero]
      _ = v i₂ * (u i₁ * a j + v i₁ * b j) + v i₁ * (u i₂ * a j + v i₂ * b j) := by ring
  have hb_eq : ∀ j : Fin n, b j = u i₂ * K i₁ j + u i₁ * K i₂ j := by
    intro j
    rw [hab j i₁, hab j i₂]
    calc b j = (u i₂ * u i₁ + u i₁ * u i₂) * a j + (u i₁ * v i₂ + v i₁ * u i₂) * b j := by
          rw [hdet, one_mul, mul_comm (u i₂) (u i₁), z2_add_self, zero_mul, zero_add]
      _ = u i₂ * (u i₁ * a j + v i₁ * b j) + u i₁ * (u i₂ * a j + v i₂ * b j) := by ring
  have hsym : ∀ i j : Fin n, K i j = K j i := fun i j =>
    congrFun (congrFun hK.1 j) i
  let α : F := v i₂ * a i₁ + v i₁ * a i₂
  let β : F := v i₂ * b i₁ + v i₁ * b i₂
  let γ : F := u i₂ * a i₁ + u i₁ * a i₂
  let δ : F := u i₂ * b i₁ + u i₁ * b i₂
  have ha_lin : ∀ j, a j = α * u j + β * v j := by
    intro j
    rw [ha_eq j, hsym i₁ j, hsym i₂ j, hab i₁ j, hab i₂ j]
    dsimp [α, β]; ring
  have hb_lin : ∀ j, b j = γ * u j + δ * v j := by
    intro j
    rw [hb_eq j, hsym i₁ j, hsym i₂ j, hab i₁ j, hab i₂ j]
    dsimp [γ, δ]; ring
  have hKform : ∀ i j, K i j = α * (u i * u j) + β * (u i * v j) +
      γ * (v i * u j) + δ * (v i * v j) := by
    intro i j
    rw [hab j i, ha_lin j, hb_lin j]
    ring
  have hβγ : β = γ := by
    have hs := hsym i₁ i₂
    rw [hKform i₁ i₂, hKform i₂ i₁] at hs
    have h0 : (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂) = 0 := by
      have hz := (z2_add_eq_zero_iff _ _).mpr hs
      calc (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂)
          = (α * (u i₁ * u i₂) + β * (u i₁ * v i₂) + γ * (v i₁ * u i₂) + δ * (v i₁ * v i₂)) +
            (α * (u i₂ * u i₁) + β * (u i₂ * v i₁) + γ * (v i₂ * u i₁) + δ * (v i₂ * v i₁)) := by
              have h1 : α * (u i₁ * u i₂) + α * (u i₂ * u i₁) = 0 := by
                rw [mul_comm (u i₂) (u i₁)]; exact z2_add_self _
              have h2 : δ * (v i₁ * v i₂) + δ * (v i₂ * v i₁) = 0 := by
                rw [mul_comm (v i₂) (v i₁)]; exact z2_add_self _
              calc (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂)
                  = (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂) + 0 + 0 := by simp
                _ = (β + γ) * (u i₁ * v i₂ + v i₁ * u i₂) +
                    (α * (u i₁ * u i₂) + α * (u i₂ * u i₁)) +
                    (δ * (v i₁ * v i₂) + δ * (v i₂ * v i₁)) := by rw [h1, h2]
                _ = _ := by ring
        _ = 0 := hz
    rw [hdet, mul_one] at h0
    exact (z2_add_eq_zero_iff β γ).mp h0
  have hdiag : ∀ i, α * u i + δ * v i = 0 := by
    intro i
    have hd := hK.2 i
    rw [hKform i i, hβγ, z2_sq (u i), z2_sq (v i)] at hd
    have hmid : γ * (u i * v i) + γ * (v i * u i) = 0 := by
      rw [mul_comm (v i) (u i)]; exact z2_add_self _
    calc α * u i + δ * v i
        = α * u i + (γ * (u i * v i) + γ * (v i * u i)) + δ * v i := by rw [hmid, add_zero]
      _ = α * u i + γ * (u i * v i) + γ * (v i * u i) + δ * v i := by ring
      _ = 0 := hd
  have hα : α = 0 := by
    calc α = α * (u i₁ * v i₂ + v i₁ * u i₂) + δ * 0 := by
          rw [hdet, mul_one, mul_zero, add_zero]
      _ = α * (u i₁ * v i₂ + v i₁ * u i₂) + δ * (v i₂ * v i₁ + v i₁ * v i₂) := by
          rw [mul_comm (v i₂) (v i₁), z2_add_self]
      _ = v i₂ * (α * u i₁ + δ * v i₁) + v i₁ * (α * u i₂ + δ * v i₂) := by ring
      _ = 0 := by rw [hdiag i₁, hdiag i₂]; simp
  have hδ : δ = 0 := by
    calc δ = δ * (u i₁ * v i₂ + v i₁ * u i₂) + α * 0 := by
          rw [hdet, mul_one, mul_zero, add_zero]
      _ = δ * (u i₁ * v i₂ + v i₁ * u i₂) + α * (u i₂ * u i₁ + u i₁ * u i₂) := by
          rw [mul_comm (u i₂) (u i₁), z2_add_self]
      _ = u i₂ * (α * u i₁ + δ * v i₁) + u i₁ * (α * u i₂ + δ * v i₂) := by ring
      _ = 0 := by rw [hdiag i₁, hdiag i₂]; simp
  have hKβ : ∀ i j, K i j = β * (u i * v j + v i * u j) := by
    intro i j
    rw [hKform i j, hα, hδ, ← hβγ]
    ring
  have hβ : β = 1 := by
    rcases z2_eq_zero_or_one β with h0 | h1
    · exfalso; apply hKne
      ext i j; rw [hKβ i j, h0, zero_mul]; rfl
    · exact h1
  ext i j
  rw [hKβ i j, hβ, one_mul]
  rfl

private lemma rank_wedge_add_of_disjoint {n : ℕ} {u₁ v₁ u₂ v₂ : Fin n → F}
    (hu₁ : u₁ ≠ 0) (hv₁ : v₁ ≠ 0) (huv₁ : u₁ ≠ v₁)
    (hu₂ : u₂ ≠ 0) (hv₂ : v₂ ≠ 0) (huv₂ : u₂ ≠ v₂)
    (hdisj : Submodule.span F ({u₁, v₁} : Set (Fin n → F)) ⊓
      Submodule.span F ({u₂, v₂} : Set (Fin n → F)) = ⊥) :
    (wedge u₁ v₁ + wedge u₂ v₂).rank = 4 := by
  let vecs : Fin 4 → (Fin n → F) := ![u₁, v₁, u₂, v₂]
  have hli : LinearIndependent F vecs := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (g 0 • u₁ + g 1 • v₁) + (g 2 • u₂ + g 3 • v₂) = 0 := by
      have h4 : ∑ i : Fin 4, g i • vecs i =
          g 0 • u₁ + g 1 • v₁ + (g 2 • u₂ + g 3 • v₂) := by
        rw [Fin.sum_univ_four]
        simp only [vecs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        abel
      rwa [← h4]
    have hmem1 : g 0 • u₁ + g 1 • v₁ ∈ Submodule.span F ({u₁, v₁} : Set (Fin n → F)) :=
      Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have hmem2 : g 2 • u₂ + g 3 • v₂ ∈ Submodule.span F ({u₂, v₂} : Set (Fin n → F)) :=
      Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have heq : g 0 • u₁ + g 1 • v₁ = g 2 • u₂ + g 3 • v₂ :=
      (vec_add_eq_zero_iff _ _).mp hsum
    have hbot : g 0 • u₁ + g 1 • v₁ ∈ (⊥ : Submodule F (Fin n → F)) := by
      rw [← hdisj]
      exact ⟨hmem1, heq ▸ hmem2⟩
    rw [Submodule.mem_bot] at hbot
    have hbot2 : g 2 • u₂ + g 3 • v₂ = 0 := heq ▸ hbot
    have h01 : g 0 = 0 ∧ g 1 = 0 := by
      rcases z2_eq_zero_or_one (g 0) with h0 | h0 <;>
      rcases z2_eq_zero_or_one (g 1) with h1 | h1
      · exact ⟨h0, h1⟩
      · rw [h0, h1, zero_smul, one_smul, zero_add] at hbot; exact absurd hbot hv₁
      · rw [h0, h1, one_smul, zero_smul, add_zero] at hbot; exact absurd hbot hu₁
      · rw [h0, h1, one_smul, one_smul] at hbot
        exact absurd ((vec_add_eq_zero_iff u₁ v₁).mp hbot) huv₁
    have h23 : g 2 = 0 ∧ g 3 = 0 := by
      rcases z2_eq_zero_or_one (g 2) with h2 | h2 <;>
      rcases z2_eq_zero_or_one (g 3) with h3 | h3
      · exact ⟨h2, h3⟩
      · rw [h2, h3, zero_smul, one_smul, zero_add] at hbot2; exact absurd hbot2 hv₂
      · rw [h2, h3, one_smul, zero_smul, add_zero] at hbot2; exact absurd hbot2 hu₂
      · rw [h2, h3, one_smul, one_smul] at hbot2
        exact absurd ((vec_add_eq_zero_iff u₂ v₂).mp hbot2) huv₂
    intro i
    fin_cases i
    · exact h01.1
    · exact h01.2
    · exact h23.1
    · exact h23.2
  let B : Matrix (Fin 4) (Fin n) F := fun k j => vecs k j
  have hBT : Bᵀ.rank = 4 := by
    rw [rank_eq_finrank_colSp]
    have hrg : colSp Bᵀ = Submodule.span F (Set.range vecs) := by
      ext y
      simp only [colSp, LinearMap.mem_range, Matrix.mulVecLin_apply,
        ← Fintype.range_linearCombination]
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        ext i
        simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.mulVec, dotProduct, B]
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
      · rintro ⟨x, rfl⟩
        refine ⟨x, ?_⟩
        ext i
        simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Matrix.mulVec, dotProduct, B]
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
    rw [hrg, finrank_span_eq_card hli, Fintype.card_fin]
  have hBr : B.rank = 4 := by
    rw [← Matrix.rank_transpose, hBT]
  have hker : LinearMap.ker (wedge u₁ v₁ + wedge u₂ v₂).mulVecLin = LinearMap.ker B.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.add_mulVec, wedge_mulVec]
    constructor
    · intro hx
      let c : Fin 4 → F := ![dotProduct v₁ x, dotProduct u₁ x, dotProduct v₂ x, dotProduct u₂ x]
      have hsum : ∑ i : Fin 4, c i • vecs i = 0 := by
        rw [Fin.sum_univ_four]
        simp only [c, vecs, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
        simpa [add_assoc] using hx
      have hc0 := (Fintype.linearIndependent_iff.mp hli) c hsum
      ext k
      change dotProduct (vecs k) x = 0
      fin_cases k
      · exact hc0 1
      · exact hc0 0
      · exact hc0 3
      · exact hc0 2
    · intro hx
      have h0 : dotProduct u₁ x = 0 := congrFun hx 0
      have h1 : dotProduct v₁ x = 0 := congrFun hx 1
      have h2 : dotProduct u₂ x = 0 := congrFun hx 2
      have h3 : dotProduct v₂ x = 0 := congrFun hx 3
      rw [h0, h1, h2, h3]
      simp
  have h1 := LinearMap.finrank_range_add_finrank_ker (wedge u₁ v₁ + wedge u₂ v₂).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [hker] at h1
  change (wedge u₁ v₁ + wedge u₂ v₂).rank + _ = _ at h1
  change B.rank + _ = _ at h2
  omega

private lemma exists_pair_of_finrank_two {n : ℕ} {V : Submodule F (Fin n → F)}
    (hV : Module.finrank F V = 2) :
    ∃ u v : Fin n → F, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧
      V = Submodule.span F ({u, v} : Set (Fin n → F)) := by
  have hne : V ≠ ⊥ := by
    intro hb; rw [hb, finrank_bot] at hV; omega
  obtain ⟨u, huV, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hlt : Submodule.span F {u} < V := by
    refine lt_of_le_of_ne (Submodule.span_le.mpr (by simpa using huV)) ?_
    intro heq
    have h1 : Module.finrank F (Submodule.span F {u}) = 1 := finrank_span_singleton hu0
    rw [heq, hV] at h1
    omega
  obtain ⟨v, hvV, hvnot⟩ := IsConcreteLE.exists_of_lt hlt
  have hv0 : v ≠ 0 := fun h => hvnot (h ▸ Submodule.zero_mem _)
  have huv : u ≠ v := fun h => hvnot (h ▸ Submodule.subset_span (Set.mem_singleton u))
  have hsub : Submodule.span F ({u, v} : Set (Fin n → F)) ≤ V :=
    Submodule.span_le.mpr (by intro x hx; rcases hx with rfl | rfl <;> assumption)
  have hlt2 : Submodule.span F {u} < Submodule.span F ({u, v} : Set (Fin n → F)) := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp))) ?_
    intro heq
    exact hvnot (heq ▸ Submodule.subset_span (by simp))
  have hfr1 : Module.finrank F (Submodule.span F {u}) <
      Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) :=
    Submodule.finrank_lt_finrank_of_lt hlt2
  have hfr2 : Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) ≤
      Module.finrank F V :=
    Submodule.finrank_mono hsub
  have hfr_eq : Module.finrank F (Submodule.span F ({u, v} : Set (Fin n → F))) = 2 := by
    rw [finrank_span_singleton hu0] at hfr1; omega
  exact ⟨u, v, hu0, hv0, huv, (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfr_eq, hV])).symm⟩

private lemma exists_extend_of_finrank_two {n : ℕ} {V : Submodule F (Fin n → F)}
    (hV : Module.finrank F V = 2) {w : Fin n → F} (hwV : w ∈ V) (hw0 : w ≠ 0) :
    ∃ a : Fin n → F, a ∈ V ∧ a ∉ Submodule.span F {w} ∧ a ≠ 0 ∧ w ≠ a ∧
      V = Submodule.span F ({w, a} : Set (Fin n → F)) := by
  have hlt : Submodule.span F {w} < V := by
    refine lt_of_le_of_ne (Submodule.span_le.mpr (by simpa using hwV)) ?_
    intro heq
    have h1 : Module.finrank F (Submodule.span F {w}) = 1 := finrank_span_singleton hw0
    rw [heq, hV] at h1
    omega
  obtain ⟨a, haV, hanot⟩ := IsConcreteLE.exists_of_lt hlt
  have ha0 : a ≠ 0 := fun h => hanot (h ▸ Submodule.zero_mem _)
  have hwa : w ≠ a := fun h => hanot (h ▸ Submodule.subset_span (Set.mem_singleton w))
  have hsub : Submodule.span F ({w, a} : Set (Fin n → F)) ≤ V :=
    Submodule.span_le.mpr (by intro x hx; rcases hx with rfl | rfl <;> assumption)
  have hlt2 : Submodule.span F {w} < Submodule.span F ({w, a} : Set (Fin n → F)) := by
    refine lt_of_le_of_ne (Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp))) ?_
    intro heq
    exact hanot (heq ▸ Submodule.subset_span (by simp))
  have hfr1 : Module.finrank F (Submodule.span F {w}) <
      Module.finrank F (Submodule.span F ({w, a} : Set (Fin n → F))) :=
    Submodule.finrank_lt_finrank_of_lt hlt2
  have hfr2 : Module.finrank F (Submodule.span F ({w, a} : Set (Fin n → F))) ≤
      Module.finrank F V :=
    Submodule.finrank_mono hsub
  have hfr_eq : Module.finrank F (Submodule.span F ({w, a} : Set (Fin n → F))) = 2 := by
    rw [finrank_span_singleton hw0] at hfr1; omega
  exact ⟨a, haV, hanot, ha0, hwa, (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfr_eq, hV])).symm⟩

private lemma part1 {n : ℕ} (P : Submodule F (Matrix (Fin n) (Fin n) F))
    (hP : ∀ K ∈ P, Alt K)
    (R : Fin 3 → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hRk : ∀ i, (R i).rank ≤ 2)
    (hRW : ∀ i j, R i + R j ∈ WSub P) :
    ∃ i j : Fin 3, i ≠ j ∧ crossLin n (R i) = crossLin n (R j) := by
  by_contra hcontra
  push Not at hcontra
  have hpair : ∀ i j : Fin 3, i ≠ j →
      let K := crossLin n (R i) + crossLin n (R j)
      Alt K ∧ K ≠ 0 ∧ K.rank = 2 ∧
        colSp K = (colSp (R i)).map (piBot n) ⊔ (colSp (R j)).map (piBot n) := by
    intro i j hij
    obtain ⟨A, K, hA, hKP, hEq⟩ := hRW i j
    have hKeq : K = crossLin n (R i) + crossLin n (R j) := by
      have hc := congrArg (crossLin n) hEq
      rw [map_add, crossLin_fromBlocks] at hc
      exact hc.symm
    subst hKeq
    have hKne : crossLin n (R i) + crossLin n (R j) ≠ 0 := by
      intro h0
      exact hcontra i j hij ((mat_add_eq_zero_iff _ _).mp h0)
    have hKalt : Alt (crossLin n (R i) + crossLin n (R j)) := hP _ hKP
    have hKge : 2 ≤ (crossLin n (R i) + crossLin n (R j)).rank :=
      two_le_rank_of_alt_ne_zero hKalt hKne
    have hblk : 2 * (crossLin n (R i) + crossLin n (R j)).rank ≤ (R i + R j).rank := by
      rw [hEq]; exact two_mul_rank_le_rank_fromBlocks A _
    have hadd : (R i + R j).rank ≤ (R i).rank + (R j).rank := rank_add_le (R i) (R j)
    have hri := hRk i
    have hrj := hRk j
    have hKr : (crossLin n (R i) + crossLin n (R j)).rank = 2 := by omega
    have hsumr : (R i + R j).rank = (R i).rank + (R j).rank := by omega
    have hsup := colSp_add_eq_sup_of_rank_eq (R i) (R j) hsumr
    have hmap : colSp (crossLin n (R i) + crossLin n (R j)) =
        (colSp (R i)).map (piBot n) ⊔ (colSp (R j)).map (piBot n) := by
      rw [← map_piBot_colSp_fromBlocks A (crossLin n (R i) + crossLin n (R j)),
        ← hEq, hsup, Submodule.map_sup]
    exact ⟨hKalt, hKne, hKr, hmap⟩
  obtain ⟨hAlt01, hNe01, hRk01, hMap01⟩ := hpair 0 1 (by decide)
  obtain ⟨hAlt02, hNe02, hRk02, hMap02⟩ := hpair 0 2 (by decide)
  obtain ⟨hAlt12, hNe12, hRk12, hMap12⟩ := hpair 1 2 (by decide)
  set K01 := crossLin n (R 0) + crossLin n (R 1)
  set K02 := crossLin n (R 0) + crossLin n (R 2)
  set K12 := crossLin n (R 1) + crossLin n (R 2)
  have hK12eq : K12 = K01 + K02 := by
    ext i j
    change crossLin n (R 1) i j + crossLin n (R 2) i j =
      (crossLin n (R 0) i j + crossLin n (R 1) i j) +
      (crossLin n (R 0) i j + crossLin n (R 2) i j)
    have h00 := z2_add_self (crossLin n (R 0) i j)
    calc crossLin n (R 1) i j + crossLin n (R 2) i j
        = 0 + crossLin n (R 1) i j + crossLin n (R 2) i j := by rw [zero_add]
      _ = (crossLin n (R 0) i j + crossLin n (R 0) i j) +
          crossLin n (R 1) i j + crossLin n (R 2) i j := by rw [h00]
      _ = _ := by ring
  let V01 := colSp K01
  let V02 := colSp K02
  let V12 := colSp K12
  have hfr01 : Module.finrank F V01 = 2 := hRk01
  have hfr02 : Module.finrank F V02 = 2 := hRk02
  have hVne : V01 ≠ V02 := by
    intro heq
    obtain ⟨u, v, hu, hv, huv, hsp⟩ := exists_pair_of_finrank_two hfr01
    have h1 : K01 = wedge u v := eq_wedge_of_alt_colSp hAlt01 hNe01 hu hv huv hsp
    have h2 : K02 = wedge u v := eq_wedge_of_alt_colSp hAlt02 hNe02 hu hv huv (heq.symm.trans hsp)
    have h0 : K12 = 0 := by rw [hK12eq, h1, h2, mat_add_self]
    exact hNe12 h0
  have hVinf : V01 ⊓ V02 ≠ ⊥ := by
    intro hdisj
    obtain ⟨u₁, v₁, hu₁, hv₁, huv₁, hsp₁⟩ := exists_pair_of_finrank_two hfr01
    obtain ⟨u₂, v₂, hu₂, hv₂, huv₂, hsp₂⟩ := exists_pair_of_finrank_two hfr02
    have h1 : K01 = wedge u₁ v₁ := eq_wedge_of_alt_colSp hAlt01 hNe01 hu₁ hv₁ huv₁ hsp₁
    have h2 : K02 = wedge u₂ v₂ := eq_wedge_of_alt_colSp hAlt02 hNe02 hu₂ hv₂ huv₂ hsp₂
    have hr4 : K12.rank = 4 := by
      rw [hK12eq, h1, h2]
      exact rank_wedge_add_of_disjoint hu₁ hv₁ huv₁ hu₂ hv₂ huv₂
        (by rw [← hsp₁, ← hsp₂]; exact hdisj)
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVinf
  obtain ⟨a, haV01, hanot, ha0, hwa, hsp01⟩ := exists_extend_of_finrank_two hfr01 hw.1 hw0
  obtain ⟨b, hbV02, hbnot, hb0, hwb, hsp02⟩ := exists_extend_of_finrank_two hfr02 hw.2 hw0
  have hbnot01 : b ∉ V01 := by
    intro hb1
    have hsub : V02 ≤ V01 := by
      rw [hsp02, Submodule.span_le]
      intro x hx; rcases hx with rfl | rfl
      · exact hw.1
      · exact hb1
    exact hVne (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hfr02, hfr01])).symm
  have hK01w : K01 = wedge w a := eq_wedge_of_alt_colSp hAlt01 hNe01 hw0 ha0 hwa hsp01
  have hK02w : K02 = wedge w b := eq_wedge_of_alt_colSp hAlt02 hNe02 hw0 hb0 hwb hsp02
  have hK12w : K12 = wedge w (a + b) := by rw [hK12eq, hK01w, hK02w, wedge_add_right]
  have hab0 : a + b ≠ 0 := by
    intro h0
    have heq : a = b := (vec_add_eq_zero_iff a b).mp h0
    exact hbnot01 (heq ▸ haV01)
  have hwab : w ≠ a + b := by
    intro h0
    have hb_eq : b = w + a := by
      ext i
      have hi : w i = a i + b i := congrFun h0 i
      have h1 := z2_add_self (a i)
      calc b i = 0 + b i := by rw [zero_add]
        _ = (a i + a i) + b i := by rw [h1]
        _ = (a i + b i) + a i := by ring
        _ = w i + a i := by rw [← hi]
    exact hbnot01 (hb_eq ▸ V01.add_mem hw.1 haV01)
  have hsp12 : V12 = Submodule.span F ({w, a + b} : Set (Fin n → F)) := by
    change colSp K12 = _
    rw [hK12w]
    exact colSp_wedge hw0 hab0 hwab
  have hinf01_02 : V01 ⊓ V02 ≤ Submodule.span F {w} := by
    intro z hz
    have hz2 : z ∈ Submodule.span F ({w, b} : Set (Fin n → F)) := hsp02 ▸ hz.2
    rw [Submodule.mem_span_pair] at hz2
    obtain ⟨c₁, c₂, hcz⟩ := hz2
    rcases z2_eq_zero_or_one c₂ with hc2 | hc2
    · rw [hc2, zero_smul, add_zero] at hcz
      rw [← hcz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
    · exfalso; apply hbnot01
      rw [hc2, one_smul] at hcz
      have hbeq : b = z + c₁ • w := by
        ext i
        have hi : c₁ * w i + b i = z i := congrFun hcz i
        have hs := z2_add_self (c₁ * w i)
        calc b i = 0 + b i := by rw [zero_add]
          _ = (c₁ * w i + c₁ * w i) + b i := by rw [hs]
          _ = (c₁ * w i + b i) + c₁ * w i := by ring
          _ = z i + c₁ * w i := by rw [hi]
      rw [hbeq]
      exact V01.add_mem hz.1 (V01.smul_mem c₁ hw.1)
  have hinf01_12 : V01 ⊓ V12 ≤ Submodule.span F {w} := by
    intro z hz
    have hz2 : z ∈ Submodule.span F ({w, a + b} : Set (Fin n → F)) := hsp12 ▸ hz.2
    rw [Submodule.mem_span_pair] at hz2
    obtain ⟨c₁, c₂, hcz⟩ := hz2
    rcases z2_eq_zero_or_one c₂ with hc2 | hc2
    · rw [hc2, zero_smul, add_zero] at hcz
      rw [← hcz]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton w))
    · exfalso; apply hbnot01
      rw [hc2, one_smul] at hcz
      have hbeq : b = z + c₁ • w + a := by
        ext i
        have hi : c₁ * w i + (a i + b i) = z i := congrFun hcz i
        have hs1 := z2_add_self (c₁ * w i)
        have hs2 := z2_add_self (a i)
        calc b i = 0 + 0 + b i := by simp
          _ = (c₁ * w i + c₁ * w i) + (a i + a i) + b i := by rw [hs1, hs2]
          _ = (c₁ * w i + (a i + b i)) + c₁ * w i + a i := by ring
          _ = z i + c₁ * w i + a i := by rw [hi]
      rw [hbeq]
      exact V01.add_mem (V01.add_mem hz.1 (V01.smul_mem c₁ hw.1)) haV01
  set U0 := (colSp (R 0)).map (piBot n)
  set U1 := (colSp (R 1)).map (piBot n)
  have hU0 : U0 ≤ Submodule.span F {w} := by
    refine le_trans ?_ hinf01_02
    exact le_inf
      (by rw [show V01 = U0 ⊔ U1 from hMap01]; exact le_sup_left)
      (by rw [show V02 = U0 ⊔ (colSp (R 2)).map (piBot n) from hMap02]; exact le_sup_left)
  have hU1 : U1 ≤ Submodule.span F {w} := by
    refine le_trans ?_ hinf01_12
    exact le_inf
      (by rw [show V01 = U0 ⊔ U1 from hMap01]; exact le_sup_right)
      (by rw [show V12 = U1 ⊔ (colSp (R 2)).map (piBot n) from hMap12]; exact le_sup_left)
  have hV01_le : V01 ≤ Submodule.span F {w} := by
    rw [show V01 = U0 ⊔ U1 from hMap01]
    exact sup_le hU0 hU1
  have hfr := Submodule.finrank_mono hV01_le
  rw [finrank_span_singleton hw0] at hfr
  change K01.rank ≤ 1 at hfr
  omega

private lemma pow_mono_sub {a b : ℕ} (h : a ≤ b) : b - a + 2 ^ (a + 1) ≤ 2 ^ (b + 1) := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    have hpow : 2 ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
    omega

private lemma finrank_fun_F {ι : Type*} [Fintype ι] :
    Module.finrank F (ι → F) = Fintype.card ι := by
  simp

private def emb33 (m : ℕ) : Fin 3 ⊕ Fin 3 → Idx 3 m
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr (Sum.inr j)

private def crossK (m : ℕ) :
    Matrix (Idx 3 m) (Idx 3 m) F →ₗ[F] Matrix (Fin 3) (Fin 3) F where
  toFun X i j := X (Sum.inl i) (Sum.inr (Sum.inr j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma submatrix_emb33_mem_WSub {m : ℕ} {X : Matrix (Idx 3 m) (Idx 3 m) F}
    (hX : X ∈ Wfull m) : X.submatrix (emb33 m) (emb33 m) ∈ WSub Palt := by
  obtain ⟨A, B, K, hA, hK, rfl⟩ := (mem_Wfull_iff X).mp hX
  refine ⟨A, K, hA, (mem_Palt_iff K).mpr hK, ?_⟩
  ext (i | i) (j | j)
  · rfl
  · rfl
  · change (Cmat B K).transpose (Sum.inr i) j = K i j
    exact alt_entry_symm hK j i
  · rfl

private lemma crossK_eq_zero_of_mem_Wfull_rank_le_two {m : ℕ}
    {X : Matrix (Idx 3 m) (Idx 3 m) F} (hXW : X ∈ Wfull m) (hXr : X.rank ≤ 2) :
    crossK m X = 0 := by
  obtain ⟨A, B, K, hA, hK, rfl⟩ := (mem_Wfull_iff X).mp hXW
  have hc : crossK m (Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0) = K := by
    ext i j; rfl
  rw [hc]
  by_contra hKne
  have h1 := two_le_rank_of_alt_ne_zero hK hKne
  have hStrip : K.rank ≤ (Cmat B K).rank := (Cmat B K).rank_submatrix_le id Sum.inr
  have hBlock := rankBlockLower A (Cmat B K)
  omega

private lemma part1_full {m : ℕ}
    (R3 : Fin 3 → Matrix (Idx 3 m) (Idx 3 m) F)
    (hRk : ∀ a, (R3 a).rank ≤ 2)
    (hRW : ∀ a b, R3 a + R3 b ∈ Wfull m) :
    ∃ a b : Fin 3, a ≠ b ∧ crossK m (R3 a) = crossK m (R3 b) := by
  let R' : Fin 3 → Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F :=
    fun a => (R3 a).submatrix (emb33 m) (emb33 m)
  have hR'k : ∀ a, (R' a).rank ≤ 2 := fun a =>
    ((R3 a).rank_submatrix_le (emb33 m) (emb33 m)).trans (hRk a)
  have hR'W : ∀ a b, R' a + R' b ∈ WSub Palt := fun a b => by
    have heq : R' a + R' b = (R3 a + R3 b).submatrix (emb33 m) (emb33 m) := rfl
    rw [heq]
    exact submatrix_emb33_mem_WSub (hRW a b)
  obtain ⟨a, b, hab, hceq⟩ := part1 Palt (fun K hK => (mem_Palt_iff K).mp hK) R' hR'k hR'W
  exact ⟨a, b, hab, hceq⟩

set_option maxHeartbeats 800000 in
private lemma part2_full {m t : ℕ}
    (R : Fin t → Matrix (Idx 3 m) (Idx 3 m) F)
    (hRk : ∀ i, (R i).rank ≤ 2)
    (hWS : Wfull m ≤ Submodule.span F (Set.range R)) :
    let D := Module.finrank F (Wfull m)
    D ≤ t ∧ 3 + (t - D) + 2 ≤ 2 ^ ((t - D) + 1) := by
  classical
  set W := Wfull m
  set S := Submodule.span F (Set.range R)
  set D := Module.finrank F W
  have hS_le : Module.finrank F S ≤ t := by
    have hrg : LinearMap.range (Fintype.linearCombination F R) = S :=
      Fintype.range_linearCombination F R
    rw [← hrg]
    have h1 := LinearMap.finrank_range_le (Fintype.linearCombination F R)
    rw [finrank_fun_F, Fintype.card_fin] at h1
    exact h1
  have hDt : D ≤ t := (Submodule.finrank_mono hWS).trans hS_le
  refine ⟨hDt, ?_⟩
  set Q := S.map W.mkQ
  set s := Module.finrank F Q
  have hs_le : s ≤ t - D := by
    let qS : S →ₗ[F] (Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) := W.mkQ.domRestrict S
    have hrm := LinearMap.finrank_range_add_finrank_ker qS
    have hrg : LinearMap.range qS = Q := by
      ext y; simp [qS, Q, Submodule.mem_map]
    have hker : Module.finrank F (LinearMap.ker qS) = D := by
      let e : W →ₗ[F] LinearMap.ker qS :=
        { toFun := fun x => ⟨⟨x.1, hWS x.2⟩, by
            change W.mkQ x.1 = 0
            exact (Submodule.Quotient.mk_eq_zero W).mpr x.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      have he_bij : Function.Bijective e := by
        constructor
        · intro x y h; exact Subtype.ext (congrArg (fun z => z.1.1) h)
        · rintro ⟨⟨x, hxS⟩, hxk⟩
          have hxW : x ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hxk
          exact ⟨⟨x, hxW⟩, rfl⟩
      exact (LinearEquiv.ofBijective e he_bij).finrank_eq.symm
    rw [hrg, hker] at hrm
    omega
  let qR : Fin t → (Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) := fun i => W.mkQ (R i)
  have hqR_mem : ∀ i, qR i ∈ Q := fun i =>
    ⟨R i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  let Cplus : Finset (Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) :=
    (Finset.univ.image qR).erase 0
  set mc := Cplus.card
  have hm_bound : mc + 1 ≤ 2 ^ s := by
    have h0not : (0 : Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) ∉ Cplus :=
      Finset.notMem_erase _ _
    let C0 := insert (0 : Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) Cplus
    have hC0_card : C0.card = mc + 1 := Finset.card_insert_of_notMem h0not
    have hC0_mem : ∀ c ∈ C0, c ∈ Q := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc'
      · exact Q.zero_mem
      · have hci := Finset.mem_of_mem_erase hc'
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hci
        exact hqR_mem i
    have hcard_le : C0.card ≤ Fintype.card Q := by
      let f : C0 → Q := fun c => ⟨c.1, hC0_mem c.1 c.2⟩
      have hfinj : Function.Injective f := fun a b h =>
        Subtype.ext (congrArg (fun z : Q => z.1) h)
      simpa [Fintype.card_coe] using Fintype.card_le_of_injective f hfinj
    have hQcard : Fintype.card Q = 2 ^ s := by
      have h := Module.card_eq_pow_finrank (K := F) (V := Q)
      rw [ZMod.card] at h
      exact h
    omega
  have hrep_ex : ∀ c : Cplus, ∃ i : Fin t, qR i = c.1 := by
    intro c
    have hc := Finset.mem_of_mem_erase c.2
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    exact ⟨i, hi⟩
  choose rep hrep using hrep_ex
  have hd_ex : ∀ c : Cplus, ∃ d : Matrix (Fin 3) (Fin 3) F,
      ∀ i : Fin t, qR i = c.1 →
        crossK m (R i) + crossK m (R (rep c)) ∈ Submodule.span F {d} := by
    intro c
    by_cases hall : ∀ i : Fin t, qR i = c.1 → crossK m (R i) = crossK m (R (rep c))
    · refine ⟨0, fun i hi => ?_⟩
      rw [hall i hi, mat_add_self]
      exact Submodule.zero_mem _
    · push Not at hall
      obtain ⟨i₁, hi₁, hne₁⟩ := hall
      refine ⟨crossK m (R i₁) + crossK m (R (rep c)), fun i hi => ?_⟩
      let R3 : Fin 3 → Matrix (Idx 3 m) (Idx 3 m) F := ![R (rep c), R i₁, R i]
      have hR3k : ∀ a : Fin 3, (R3 a).rank ≤ 2 := by
        intro a; fin_cases a <;> exact hRk _
      have hR3q : ∀ a : Fin 3, W.mkQ (R3 a) = c.1 := by
        intro a; fin_cases a
        · exact hrep c
        · exact hi₁
        · exact hi
      have hR3W : ∀ a b : Fin 3, R3 a + R3 b ∈ W := by
        intro a b
        rw [← Submodule.Quotient.mk_eq_zero W]
        change W.mkQ (R3 a + R3 b) = 0
        rw [map_add, hR3q a, hR3q b]
        have : c.1 + c.1 = (1 + 1 : F) • c.1 := by rw [add_smul, one_smul]
        rw [this]
        have h11 : (1 + 1 : F) = 0 := rfl
        rw [h11, zero_smul]
      obtain ⟨a, b, hab, hceq⟩ := part1_full R3 hR3k hR3W
      have hcases : crossK m (R i) = crossK m (R (rep c)) ∨
          crossK m (R i) = crossK m (R i₁) := by
        fin_cases a <;> fin_cases b <;> simp_all [R3]
      rcases hcases with heq | heq
      · rw [heq, mat_add_self]; exact Submodule.zero_mem _
      · rw [heq]; exact Submodule.subset_span (Set.mem_singleton _)
  choose d hd using hd_ex
  let Φ : (Cplus → F) →ₗ[F] Q :=
    { toFun := fun lam => ⟨∑ c : Cplus, lam c • c.1, by
        apply Q.sum_mem
        intro c _
        have hc := Finset.mem_of_mem_erase c.2
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
        exact Q.smul_mem _ (hi ▸ hqR_mem i)⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change ∑ c : Cplus, (x c + y c) • c.1 =
          (∑ c : Cplus, x c • c.1) + ∑ c : Cplus, y c • c.1
        simp only [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        apply Subtype.ext
        change ∑ c : Cplus, (r * x c) • c.1 = r • ∑ c : Cplus, x c • c.1
        simp only [mul_smul, Finset.smul_sum] }
  let Ψ : (Cplus → F) →ₗ[F] Matrix (Fin 3) (Fin 3) F :=
    { toFun := fun lam => ∑ c : Cplus, lam c • crossK m (R (rep c))
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r x => by simp [mul_smul, Finset.smul_sum] }
  have hΦ_surj : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hyQ⟩ _
    obtain ⟨x, hxS, rfl⟩ := hyQ
    have hxrg : x ∈ LinearMap.range (Fintype.linearCombination F R) := by
      rwa [Fintype.range_linearCombination]
    obtain ⟨α, rfl⟩ := hxrg
    let lam : Cplus → F := fun c => ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i
    refine ⟨lam, ?_⟩
    apply Subtype.ext
    change ∑ c : Cplus, lam c • c.1 = W.mkQ (∑ i : Fin t, α i • R i)
    rw [map_sum]
    simp only [map_smul]
    change ∑ c : Cplus, (∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i) • c.1 =
      ∑ i : Fin t, α i • qR i
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
      (f := fun i => α i • qR i) (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
    rw [← hfib]
    have hsum_er : ∑ c ∈ Finset.univ.image qR, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i =
        ∑ c ∈ Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i := by
      by_cases h0 : (0 : Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) ∈ Finset.univ.image qR
      · rw [← Finset.add_sum_erase _ _ h0]
        have hz : ∑ i ∈ Finset.univ.filter (fun i => qR i = 0), α i • qR i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          rw [(Finset.mem_filter.mp hi).2, smul_zero]
        rw [hz, zero_add]
      · have hCeq : Cplus = Finset.univ.image qR := Finset.erase_eq_of_notMem h0
        rw [hCeq]
    rw [hsum_er, ← Finset.sum_coe_sort Cplus]
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  have hkerΦ : Module.finrank F (LinearMap.ker Φ) + s = mc := by
    have hrm := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hΦ_surj, finrank_top, finrank_fun_F, Fintype.card_coe] at hrm
    change s + Module.finrank F (LinearMap.ker Φ) = mc at hrm
    omega
  let L₁ : Submodule F (Matrix (Fin 3) (Fin 3) F) := (LinearMap.ker Φ).map Ψ
  let L₂ : Submodule F (Matrix (Fin 3) (Fin 3) F) := Submodule.span F (Set.range d)
  have hP_le : Palt ≤ L₁ ⊔ L₂ := by
    intro K hKP
    let X : Matrix (Idx 3 m) (Idx 3 m) F :=
      Matrix.fromBlocks 0 (Cmat (0 : Matrix (Fin 3) (Fin m) F) K)
        (Cmat (0 : Matrix (Fin 3) (Fin m) F) K).transpose 0
    have hXW : X ∈ W := (mem_Wfull_iff X).mpr ⟨0, 0, K, alt_zero, (mem_Palt_iff K).mp hKP, rfl⟩
    have hXS : X ∈ LinearMap.range (Fintype.linearCombination F R) := by
      rw [Fintype.range_linearCombination]; exact hWS hXW
    obtain ⟨α, hα⟩ := hXS
    have hXsum : X = ∑ i : Fin t, α i • R i := hα.symm
    let lam : Cplus → F := fun c => ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i
    have hlam_ker : lam ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change ∑ c : Cplus, lam c • c.1 = 0
      have hW0 : W.mkQ X = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hXW
      rw [hXsum, map_sum] at hW0
      simp only [map_smul] at hW0
      change ∑ i : Fin t, α i • qR i = 0 at hW0
      rw [← hW0]
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
        (f := fun i => α i • qR i) (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
      rw [← hfib]
      have hsum_er : ∑ c ∈ Finset.univ.image qR, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i =
          ∑ c ∈ Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • qR i := by
        by_cases h0 : (0 : Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) ∈ Finset.univ.image qR
        · rw [← Finset.add_sum_erase _ _ h0]
          have hz : ∑ i ∈ Finset.univ.filter (fun i => qR i = 0), α i • qR i = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            rw [(Finset.mem_filter.mp hi).2, smul_zero]
          rw [hz, zero_add]
        · have hCeq : Cplus = Finset.univ.image qR := Finset.erase_eq_of_notMem h0
          rw [hCeq]
      rw [hsum_er, ← Finset.sum_coe_sort Cplus]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    have hK_eq : K = Ψ lam +
        ∑ c : Cplus, ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1),
          α i • (crossK m (R i) + crossK m (R (rep c))) := by
      have hKc : K = ∑ i : Fin t, α i • crossK m (R i) := by
        have hc := congrArg (crossK m) hXsum
        have hcx : crossK m X = K := by ext i j; rfl
        rw [hcx, map_sum] at hc
        simpa only [map_smul] using hc
      rw [hKc]
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := (Finset.univ : Finset (Fin t))) (t := Finset.univ.image qR) (g := qR)
        (f := fun i => α i • crossK m (R i))
        (fun i _ => Finset.mem_image_of_mem qR (Finset.mem_univ i))
      rw [← hfib]
      have hsum_er : ∑ c ∈ Finset.univ.image qR,
            ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • crossK m (R i) =
          ∑ c ∈ Cplus,
            ∑ i ∈ Finset.univ.filter (fun i => qR i = c), α i • crossK m (R i) := by
        by_cases h0 : (0 : Matrix (Idx 3 m) (Idx 3 m) F ⧸ W) ∈ Finset.univ.image qR
        · rw [← Finset.add_sum_erase _ _ h0]
          have hz : ∑ i ∈ Finset.univ.filter (fun i => qR i = 0), α i • crossK m (R i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have hi0 : W.mkQ (R i) = 0 := (Finset.mem_filter.mp hi).2
            have hiW : R i ∈ W := (Submodule.Quotient.mk_eq_zero W).mp hi0
            rw [crossK_eq_zero_of_mem_Wfull_rank_le_two hiW (hRk i), smul_zero]
          rw [hz, zero_add]
        · have hCeq : Cplus = Finset.univ.image qR := Finset.erase_eq_of_notMem h0
          rw [hCeq]
      rw [hsum_er, ← Finset.sum_coe_sort Cplus]
      change _ = (∑ c : Cplus, lam c • crossK m (R (rep c))) + _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      change ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i • crossK m (R i) =
        (∑ i ∈ Finset.univ.filter (fun i => qR i = c.1), α i) • crossK m (R (rep c)) +
        ∑ i ∈ Finset.univ.filter (fun i => qR i = c.1),
          α i • (crossK m (R i) + crossK m (R (rep c)))
      rw [Finset.sum_smul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ext a b
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have hs := z2_add_self (α i * crossK m (R (rep c)) a b)
      calc α i * crossK m (R i) a b
          = 0 + α i * crossK m (R i) a b := by rw [zero_add]
        _ = (α i * crossK m (R (rep c)) a b + α i * crossK m (R (rep c)) a b) +
            α i * crossK m (R i) a b := by rw [hs]
        _ = _ := by ring
    rw [hK_eq]
    apply Submodule.add_mem_sup
    · exact ⟨lam, hlam_ker, rfl⟩
    · apply L₂.sum_mem
      intro c _
      apply L₂.sum_mem
      intro i hi
      apply L₂.smul_mem
      have hmem := hd c i (Finset.mem_filter.mp hi).2
      have hsub : Submodule.span F {d c} ≤ L₂ :=
        Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨c, rfl⟩)
      exact hsub hmem
  have hL1 : Module.finrank F L₁ ≤ Module.finrank F (LinearMap.ker Φ) :=
    Submodule.finrank_map_le Ψ (LinearMap.ker Φ)
  have hL2 : Module.finrank F L₂ ≤ mc := by
    have hrg : LinearMap.range (Fintype.linearCombination F d) = L₂ :=
      Fintype.range_linearCombination F d
    rw [← hrg]
    have h1 := LinearMap.finrank_range_le (Fintype.linearCombination F d)
    rw [finrank_fun_F, Fintype.card_coe] at h1
    exact h1
  have hp_le : 3 ≤ Module.finrank F L₁ + Module.finrank F L₂ := by
    have h1 : Module.finrank F Palt ≤ Module.finrank F L₁ + Module.finrank F L₂ :=
      (Submodule.finrank_mono hP_le).trans (finrank_sup_le' L₁ L₂)
    have h2 : Module.finrank F Palt = 3 := finrank_Palt
    omega
  have hpow_s : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
  have hps : 3 + s + 2 ≤ 2 ^ (s + 1) := by omega
  have hmono := pow_mono_sub hs_le
  omega

private def b2z (b : Bool) : F := if b then 1 else 0

private lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> simp [b2z] at h <;> rfl

private lemma b2z_decide_ne_zero (a : F) : b2z (decide (a ≠ 0)) = a := by
  fin_cases a <;> rfl

private def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

private def depthsOf (w : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
    (List.replicate w 0)

private def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private lemma wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  unfold wiresOf
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

private lemma depthsOf_length (w : ℕ) (gs : List Gate) :
    (depthsOf w gs).length = w + gs.length := by
  unfold depthsOf
  have aux : ∀ (ds : List ℕ) (gs : List Gate),
      (gs.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]) ds).length =
      ds.length + gs.length := by
    intro ds gs
    induction gs generalizing ds with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  rw [aux, List.length_replicate]

private lemma wiresOf_append (x : List Bool) (gs1 gs2 : List Gate) :
    wiresOf x (gs1 ++ gs2) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (wiresOf x gs1) := by
  unfold wiresOf
  rw [List.foldl_append]

private lemma depthsOf_append (w : ℕ) (gs1 gs2 : List Gate) :
    depthsOf w (gs1 ++ gs2) =
      gs2.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat])
        (depthsOf w gs1) := by
  unfold depthsOf
  rw [List.foldl_append]

private lemma foldl_append_init {α β : Type*} (f : List α → β → α) (l : List β) (init : List α) :
    ∃ ext : List α, l.foldl (fun acc b => acc ++ [f acc b]) init = init ++ ext := by
  induction l generalizing init with
  | nil => exact ⟨[], by simp⟩
  | cons b l ih =>
    rw [List.foldl_cons]
    obtain ⟨ext, hext⟩ := ih (init ++ [f init b])
    exact ⟨f init b :: ext, by rw [hext]; simp⟩

private lemma wiresOf_append_getD_lt (x : List Bool) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < x.length + gs1.length) :
    (wiresOf x (gs1 ++ gs2)).getD k false = (wiresOf x gs1).getD k false := by
  rw [wiresOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_init
    (fun (w : List Bool) (g : Gate) => g.op.eval (g.inputs.map fun i => w.getD i false))
    gs2 (wiresOf x gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [wiresOf_length]; exact hk)]

private lemma depthsOf_append_getD_lt (w : ℕ) (gs1 gs2 : List Gate) {k : ℕ}
    (hk : k < w + gs1.length) :
    (depthsOf w (gs1 ++ gs2)).getD k 0 = (depthsOf w gs1).getD k 0 := by
  rw [depthsOf_append]
  obtain ⟨ext, hext⟩ := foldl_append_init
    (fun (ds : List ℕ) (g : Gate) =>
      (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat)
    gs2 (depthsOf w gs1)
  rw [hext, List.getD_append _ _ _ _ (by rw [depthsOf_length]; exact hk)]

private lemma wiresOf_getD_input (x : List Bool) (gs : List Gate) {k : ℕ} (hk : k < x.length) :
    (wiresOf x gs).getD k false = x.getD k false := by
  have h := wiresOf_append_getD_lt x [] gs (by simpa using hk)
  simpa [wiresOf] using h

private lemma depthsOf_getD_input (w : ℕ) (gs : List Gate) {k : ℕ} (hk : k < w) :
    (depthsOf w gs).getD k 0 = 0 := by
  have h := depthsOf_append_getD_lt w [] gs (by simpa using hk)
  simp only [List.nil_append] at h
  rw [h]
  unfold depthsOf
  simp only [List.foldl_nil]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_replicate]

private lemma wiresOf_getD_gate (x : List Bool) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < x.length + idx) :
    (wiresOf x gs).getD (x.length + idx) false =
      (gs[idx]).op.eval ((gs[idx]).inputs.map fun a => (wiresOf x gs).getD a false) := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
  have hlw : (wiresOf x (gs.take idx)).length = x.length + idx := by
    rw [wiresOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hlw, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro a ha
  have halt : a < x.length + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [wiresOf_append_getD_lt x (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [wiresOf_append_getD_lt x (gs.take idx) [gs[idx]] halt]

private lemma depthsOf_getD_gate (w : ℕ) (gs : List Gate) {idx : ℕ} (hidx : idx < gs.length)
    (hrb : ∀ a ∈ (gs[idx]).inputs, a < w + idx) :
    (depthsOf w gs).getD (w + idx) 0 =
      ((gs[idx]).inputs.map (fun a => (depthsOf w gs).getD a 0)).foldr max 0 +
        (nlGate (gs[idx])).toNat := by
  have hsplit : gs = (gs.take idx ++ [gs[idx]]) ++ gs.drop (idx + 1) := by
    rw [List.take_append_getElem, List.take_append_drop]
  have hlen1 : (gs.take idx).length = idx := List.length_take_of_le (Nat.le_of_lt hidx)
  have hlen2 : (gs.take idx ++ [gs[idx]]).length = idx + 1 := by
    rw [List.length_append, hlen1]
    rfl
  conv_lhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
  have hld : (depthsOf w (gs.take idx)).length = w + idx := by
    rw [depthsOf_length, hlen1]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp only [hld, Nat.sub_self, List.getD_cons_zero]
  congr 2
  apply List.map_congr_left
  intro a ha
  have halt : a < w + (gs.take idx).length := by rw [hlen1]; exact hrb a ha
  conv_rhs => rw [hsplit]
  rw [depthsOf_append_getD_lt w (gs.take idx ++ [gs[idx]]) (gs.drop (idx + 1)) (by omega)]
  rw [depthsOf_append_getD_lt w (gs.take idx) [gs[idx]] halt]

private lemma oneEach_length {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by
  simp [oneEach]

private lemma oneEach_getD_left {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk : k < n) :
    (oneEach i j).getD k false = decide (k = i.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp [hk])]
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]
  simp [Fin.ext_iff]

private lemma oneEach_getD_right {n m : ℕ} (i : Fin n) (j : Fin m) {k : ℕ} (hk1 : n ≤ k)
    (hk2 : k < n + m) :
    (oneEach i j).getD k false = decide (k - n = j.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp [hk1])]
  simp only [List.length_ofFn]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  simp [Fin.ext_iff]

private lemma anf_one (f : Bool → Bool) (x : Bool) :
    b2z (f x) = b2z (f false) + (b2z (f false) + b2z (f true)) * b2z x := by
  cases x <;> cases h0 : f false <;> cases h1 : f true <;> decide

private lemma anf_two (f : Bool → Bool → Bool) (x y : Bool) :
    b2z (f x y) =
      b2z (f false false) +
      (b2z (f false false) + b2z (f true false)) * b2z x +
      (b2z (f false false) + b2z (f false true)) * b2z y +
      b2z (xor (xor (f false false) (f false true)) (xor (f true false) (f true true))) *
        (b2z x * b2z y) := by
  cases x <;> cases y <;>
    cases h00 : f false false <;> cases h01 : f false true <;>
    cases h10 : f true false <;> cases h11 : f true true <;> decide

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m) (h : Fin n → Fin m → F) :
    Matrix (Fin n) (Fin m) F :=
  fun i j => h i j + h i v + h u j + h u v

private lemma anchor_const {n m : ℕ} (u : Fin n) (v : Fin m) (c : F) :
    anchor u v (fun _ _ => c) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  simp [z2_add_self]

private lemma anchor_split {n m : ℕ} (u : Fin n) (v : Fin m) (r : Fin n → F) (s : Fin m → F) :
    anchor u v (fun i j => r i + s j) = 0 := by
  ext i j
  simp only [anchor, Matrix.zero_apply]
  have h : (r i + s j) + (r i + s v) + (r u + s j) + (r u + s v) =
      (r i + r i) + (r u + r u) + (s j + s j) + (s v + s v) := by ring
  simp [h, z2_add_self]

private lemma anchor_add {n m : ℕ} (u : Fin n) (v : Fin m) (h1 h2 : Fin n → Fin m → F) :
    anchor u v (fun i j => h1 i j + h2 i j) = anchor u v h1 + anchor u v h2 := by
  ext i j
  simp only [anchor, Matrix.add_apply]
  ring

private lemma anchor_smul {n m : ℕ} (u : Fin n) (v : Fin m) (c : F) (h : Fin n → Fin m → F) :
    anchor u v (fun i j => c * h i j) = c • anchor u v h := by
  ext i j
  simp only [anchor, Matrix.smul_apply, smul_eq_mul]
  ring

private lemma anchor_prod_split {n m : ℕ} (u : Fin n) (v : Fin m)
    (r1 r2 : Fin n → F) (s1 s2 : Fin m → F) :
    anchor u v (fun i j => (r1 i + s1 j) * (r2 i + s2 j)) =
      Matrix.vecMulVec (fun i => r1 i + r1 u) (fun j => s2 j + s2 v) +
      Matrix.vecMulVec (fun i => r2 i + r2 u) (fun j => s1 j + s1 v) := by
  ext i j
  simp only [anchor, Matrix.add_apply, Matrix.vecMulVec_apply]
  have h : ((r1 i + s1 j) * (r2 i + s2 j) + (r1 i + s1 v) * (r2 i + s2 v) +
      (r1 u + s1 j) * (r2 u + s2 j) + (r1 u + s1 v) * (r2 u + s2 v)) +
      ((r1 i + r1 u) * (s2 j + s2 v) + (r2 i + r2 u) * (s1 j + s1 v)) =
      (2 : F) * (r1 i * r2 i + r1 u * r2 u + s1 j * s2 j + s1 v * s2 v +
        r1 i * s2 j + r1 i * s2 v + r1 u * s2 j + r1 u * s2 v +
        r2 i * s1 j + r2 i * s1 v + r2 u * s1 j + r2 u * s1 v) := by ring
  rw [z2_two, zero_mul] at h
  exact (z2_add_eq_zero_iff _ _).mp h

private lemma rank_of_factor {n m K : ℕ} (P : Matrix (Fin n) (Fin K) F)
    (Q : Matrix (Fin K) (Fin m) F) : (P * Q).rank ≤ K := by
  calc (P * Q).rank ≤ P.rank := Matrix.rank_mul_le_left P Q
    _ = Module.finrank F (LinearMap.range P.mulVecLin) := rfl
    _ ≤ Module.finrank F (Fin K → F) := LinearMap.finrank_range_le P.mulVecLin
    _ = K := Module.finrank_fin_fun F

private lemma card_filter_fin_eq_countP {α : Type*} (l : List α) (p : α → Bool) :
    (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card = l.countP p := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.countP_cons]
    have hsplit : (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun idx : Fin l.length => p l[idx.val] = true)).card := by
      have hsum : ∀ (S : Finset (Fin (l.length + 1))), S.card =
          (if (0 : Fin (l.length + 1)) ∈ S then 1 else 0) +
          (Finset.univ.filter (fun idx : Fin l.length => idx.succ ∈ S)).card := by
        intro S
        have h1 : S.card = ∑ x : Fin (l.length + 1), if x ∈ S then 1 else 0 := by
          simp
        rw [h1, Fin.sum_univ_succ]
        congr 1
        simp
      have h2 := hsum (Finset.univ.filter (fun idx : Fin (a :: l).length => p (a :: l)[idx.val] = true))
      simpa using h2
    rw [hsplit, ih]
    cases p a <;> simp [Nat.add_comm]

private def tableOf {d : ℕ} (H : Matrix (Fin d) (Fin d) F) (x y : Fin (d + 1)) : Bool :=
  Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x

private lemma tableOf_anchor_succ {d : ℕ} (Y : Matrix (Fin d) (Fin d) F) :
    (anchor (0 : Fin (d + 1)) (0 : Fin (d + 1)) (fun x y => b2z (tableOf Y x y))).submatrix
      Fin.succ Fin.succ = Y := by
  ext i j
  simp only [Matrix.submatrix_apply, anchor, tableOf, Fin.cases_zero, Fin.cases_succ,
    b2z_decide_ne_zero]
  have hbf : b2z false = 0 := rfl
  rw [hbf]
  simp

set_option maxHeartbeats 800000 in
private lemma extract_rank2_gens {d t : ℕ} (C : Circuit)
    (hrb : ReadsBack ((d + 1) + (d + 1)) C)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcnt : C.gates.countP nlGate ≤ t) :
    ∃ G : Fin t → Matrix (Fin d) (Fin d) F,
      (∀ l, (G l).rank ≤ 2) ∧
      ∀ (Y : Matrix (Fin d) (Fin d) F) (w : ℕ),
        (depthsOf ((d + 1) + (d + 1)) C.gates).getD w 0 ≤ 1 →
        Represents (tableOf Y) ⟨C.gates, w⟩ →
        Y ∈ Submodule.span F (Set.range G) := by
  classical
  let n := d + 1
  let val : ℕ → Fin n → Fin n → F :=
    fun k i j => b2z ((wiresOf (oneEach i j) C.gates).getD k false)
  let dep : ℕ → ℕ := fun k => (depthsOf (n + n) C.gates).getD k 0
  have hrb' : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      ∀ a ∈ (C.gates[idx]).inputs, a < n + n + idx := by
    intro idx hidx a ha
    have h := hrb idx hidx a
    unfold gateAt at h
    rw [List.getD_eq_getElem _ _ hidx] at h
    exact h ha
  have hval_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length) (i j : Fin n),
      val (n + n + idx) i j =
        b2z ((C.gates[idx]).op.eval ((C.gates[idx]).inputs.map fun a =>
          (wiresOf (oneEach i j) C.gates).getD a false)) := by
    intro idx hidx i j
    unfold val
    have h := wiresOf_getD_gate (oneEach i j) C.gates hidx (by
      intro a ha
      rw [oneEach_length]
      exact hrb' idx hidx a ha)
    rw [oneEach_length] at h
    rw [h]
  have hdep_gate : ∀ (idx : ℕ) (hidx : idx < C.gates.length),
      dep (n + n + idx) =
        ((C.gates[idx]).inputs.map (fun a => dep a)).foldr max 0 +
          (nlGate (C.gates[idx])).toNat := by
    intro idx hidx
    exact depthsOf_getD_gate (n + n) C.gates hidx (hrb' idx hidx)
  have hsplit_zero : ∀ k : ℕ, dep k = 0 →
      ∃ (r s : Fin n → F), ∀ i j, val k i j = r i + s j := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hk1 : k < n + n
      · by_cases hk0 : k < n
        · refine ⟨fun i => b2z (decide (k = i.val)), fun _ => 0, fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_left i j hk0, add_zero]
        · refine ⟨fun _ => 0, fun j => b2z (decide (k - n = j.val)), fun i j => ?_⟩
          unfold val
          rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; exact hk1),
            oneEach_getD_right i j (by omega) hk1, zero_add]
      · by_cases hk2 : k < n + n + C.gates.length
        · let idx := k - (n + n)
          have hidx : idx < C.gates.length := by omega
          have hkeq : k = n + n + idx := by omega
          rw [hkeq] at hdk ⊢
          let g := C.gates[idx]
          have hdg := hdep_gate idx hidx
          change dep (n + n + idx) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
          rw [hdk] at hdg
          have hnl : nlGate g = false := by
            have h0 : (nlGate g).toNat = 0 := by omega
            cases h : nlGate g
            · rfl
            · rw [h] at h0
              simp at h0
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem hidx)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => b2z (g.op.eval []), fun _ => 0, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_nil, add_zero]
          | [a] =>
            have ha_lt : a < n + n + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have ha_d : dep a = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun i => c0 + c1 * r1 i, fun j => c1 * s1 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_nil]
            have hanf := anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            change b2z (g.op.eval [_]) = c0 + c1 * val a i j at hanf
            rw [hanf, h1 i j]
            ring
          | [a, b] =>
            have ha_lt : a < n + n + idx := hrb' idx hidx a (by rw [hg_in]; simp)
            have hb_lt : b < n + n + idx := hrb' idx hidx b (by rw [hg_in]; simp)
            have hab_d : dep a = 0 ∧ dep b = 0 := by
              change 0 = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨r1, s1, h1⟩ := ih a (by omega) hab_d.1
            obtain ⟨r2, s2, h2⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnl
              rw [hg_in] at hnl
              simpa using hnl
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun i => c0 + c1 * r1 i + c2 * r2 i, fun j => c1 * s1 j + c2 * s2 j, fun i j => ?_⟩
            rw [hval_gate idx hidx i j]
            change b2z (g.op.eval (g.inputs.map _)) = _
            rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
            have hanf := anf_two (fun x y => g.op.eval [x, y])
              ((wiresOf (oneEach i j) C.gates).getD a false)
              ((wiresOf (oneEach i j) C.gates).getD b false)
            rw [hxor] at hanf
            have hbf : b2z false = 0 := rfl
            change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
            rw [hbf, zero_mul, add_zero] at hanf
            rw [hanf, h1 i j, h2 i j]
            ring
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
        · refine ⟨fun _ => 0, fun _ => 0, fun i j => ?_⟩
          unfold val
          have hge : (wiresOf (oneEach i j) C.gates).length ≤ k := by
            rw [wiresOf_length, oneEach_length]
            omega
          rw [List.getD_eq_default _ _ hge]
          simp [b2z]
  let NL : Finset (Fin C.gates.length) :=
    Finset.univ.filter (fun idx => nlGate (C.gates[idx.val]) = true ∧ dep (n + n + idx.val) ≤ 1)
  have hNL_card : NL.card ≤ t := by
    calc NL.card
        ≤ (Finset.univ.filter (fun idx : Fin C.gates.length => nlGate (C.gates[idx.val]) = true)).card :=
          Finset.card_le_card (fun idx hidx => Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp hidx).2.1⟩)
      _ = C.gates.countP nlGate := card_filter_fin_eq_countP C.gates nlGate
      _ ≤ t := hcnt
  have hNL_outer : ∀ idx ∈ NL,
      ∃ (r1 r2 s1 s2 : Fin n → F),
        anchor (0 : Fin n) (0 : Fin n) (val (n + n + idx.val)) =
          Matrix.vecMulVec r1 s1 + Matrix.vecMulVec r2 s2 := by
    intro idx hidx_mem
    have hnl : nlGate (C.gates[idx.val]) = true := (Finset.mem_filter.mp hidx_mem).2.1
    have hdg1 : dep (n + n + idx.val) ≤ 1 := (Finset.mem_filter.mp hidx_mem).2.2
    let g := C.gates[idx.val]
    have hlen2 : g.inputs.length = 2 := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      simpa using hnl.1
    obtain ⟨a, b, hab⟩ : ∃ a b, g.inputs = [a, b] := by
      match h : g.inputs with
      | [a, b] => exact ⟨a, b, rfl⟩
      | [] => rw [h] at hlen2; simp at hlen2
      | [_] => rw [h] at hlen2; simp at hlen2
      | _ :: _ :: _ :: _ => rw [h] at hlen2; simp at hlen2
    have hdg := hdep_gate idx.val idx.isLt
    change dep (n + n + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
    rw [hab, hnl] at hdg
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, Bool.toNat_true] at hdg
    have hda : dep a = 0 := by omega
    have hdb : dep b = 0 := by omega
    obtain ⟨r1, s1, h1⟩ := hsplit_zero a hda
    obtain ⟨r2, s2, h2⟩ := hsplit_zero b hdb
    have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      unfold nlGate at hnl
      rw [Bool.and_eq_true] at hnl
      exact hnl.2
    let c0 := b2z (g.op.eval [false, false])
    let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
    let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
    have hfun : val (n + n + idx.val) = fun i j =>
        (c0 + c1 * r1 i + c2 * r2 i + (c1 * s1 j + c2 * s2 j)) +
        (r1 i + s1 j) * (r2 i + s2 j) := by
      funext i j
      rw [hval_gate idx.val idx.isLt i j]
      change b2z (g.op.eval (g.inputs.map _)) = _
      rw [hab, List.map_cons, List.map_cons, List.map_nil]
      have hanf := anf_two (fun x y => g.op.eval [x, y])
        ((wiresOf (oneEach i j) C.gates).getD a false)
        ((wiresOf (oneEach i j) C.gates).getD b false)
      rw [hxor] at hanf
      have hbt : b2z true = 1 := rfl
      change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z true * (val a i j * val b i j) at hanf
      rw [hbt, one_mul] at hanf
      rw [hanf, h1 i j, h2 i j]
      ring
    refine ⟨fun i => r1 i + r1 0, fun i => r2 i + r2 0, fun j => s2 j + s2 0, fun j => s1 j + s1 0, ?_⟩
    rw [hfun, anchor_add, anchor_split, zero_add, anchor_prod_split]
  have hspan : ∀ k : ℕ, dep k ≤ 1 →
      ∃ coeff : Fin C.gates.length → F,
        anchor (0 : Fin n) (0 : Fin n) (val k) =
          ∑ idx ∈ NL, coeff idx • anchor (0 : Fin n) (0 : Fin n) (val (n + n + idx.val)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hdk
      by_cases hdk0 : dep k = 0
      · obtain ⟨r, s, hrs⟩ := hsplit_zero k hdk0
        refine ⟨fun _ => 0, ?_⟩
        have hfun : val k = fun i j => r i + s j := by funext i j; exact hrs i j
        rw [hfun, anchor_split]
        simp
      · have hk1 : n + n ≤ k := by
          by_contra hlt
          have := depthsOf_getD_input (n + n) C.gates (by omega : k < n + n)
          exact hdk0 this
        have hk2 : k < n + n + C.gates.length := by
          by_contra hge
          have hlen_d : (depthsOf (n + n) C.gates).length ≤ k := by
            rw [depthsOf_length]
            omega
          exact hdk0 (List.getD_eq_default _ _ hlen_d)
        let idx : Fin C.gates.length := ⟨k - (n + n), by omega⟩
        have hkeq : k = n + n + idx.val := by simp [idx]; omega
        rw [hkeq] at hdk ⊢
        let g := C.gates[idx.val]
        by_cases hnl : nlGate g = true
        · have hmem : idx ∈ NL := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnl, hdk⟩
          refine ⟨fun idx' => if idx' = idx then 1 else 0, ?_⟩
          rw [Finset.sum_eq_single idx]
          · simp
          · intro idx' _ hne
            simp [hne]
          · intro h
            exact absurd hmem h
        · have hnlf : nlGate g = false := by cases h : nlGate g <;> simp_all
          have hdg := hdep_gate idx.val idx.isLt
          have hgl : g.inputs.length ≤ 2 := hlen g (List.getElem_mem idx.isLt)
          match hg_in : g.inputs with
          | [] =>
            refine ⟨fun _ => 0, ?_⟩
            have hfun : val (n + n + idx.val) = fun _ _ => b2z (g.op.eval []) := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_nil]
            rw [hfun, anchor_const]
            simp
          | [a] =>
            have ha_lt : a < n + n + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have ha_d : dep a ≤ 1 := by
              change dep (n + n + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) ha_d
            let c0 := b2z (g.op.eval [false])
            let c1 := b2z (g.op.eval [false]) + b2z (g.op.eval [true])
            refine ⟨fun idx' => c1 * ca idx', ?_⟩
            have hfun : val (n + n + idx.val) = fun i j => c0 + c1 * val a i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_nil]
              exact anf_one (fun x => g.op.eval [x]) ((wiresOf (oneEach i j) C.gates).getD a false)
            rw [hfun, anchor_add, anchor_const, zero_add, anchor_smul, hca, Finset.smul_sum]
            refine Finset.sum_congr rfl fun idx' _ => by rw [smul_smul]
          | [a, b] =>
            have ha_lt : a < n + n + idx.val := hrb' idx.val idx.isLt a (by rw [hg_in]; simp)
            have hb_lt : b < n + n + idx.val := hrb' idx.val idx.isLt b (by rw [hg_in]; simp)
            have hab_d : dep a ≤ 1 ∧ dep b ≤ 1 := by
              change dep (n + n + idx.val) = (g.inputs.map dep).foldr max 0 + (nlGate g).toNat at hdg
              rw [hg_in] at hdg
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil] at hdg
              omega
            obtain ⟨ca, hca⟩ := ih a (by omega) hab_d.1
            obtain ⟨cb, hcb⟩ := ih b (by omega) hab_d.2
            have hxor : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
              unfold nlGate at hnlf
              rw [hg_in] at hnlf
              simpa using hnlf
            let c0 := b2z (g.op.eval [false, false])
            let c1 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [true, false])
            let c2 := b2z (g.op.eval [false, false]) + b2z (g.op.eval [false, true])
            refine ⟨fun idx' => c1 * ca idx' + c2 * cb idx', ?_⟩
            have hfun : val (n + n + idx.val) = fun i j => (c0 + c1 * val a i j) + c2 * val b i j := by
              funext i j
              rw [hval_gate idx.val idx.isLt i j]
              change b2z (g.op.eval (g.inputs.map _)) = _
              rw [hg_in, List.map_cons, List.map_cons, List.map_nil]
              have hanf := anf_two (fun x y => g.op.eval [x, y])
                ((wiresOf (oneEach i j) C.gates).getD a false)
                ((wiresOf (oneEach i j) C.gates).getD b false)
              rw [hxor] at hanf
              have hbf : b2z false = 0 := rfl
              change b2z (g.op.eval [_, _]) = c0 + c1 * val a i j + c2 * val b i j + b2z false * _ at hanf
              rw [hbf, zero_mul, add_zero] at hanf
              exact hanf
            rw [hfun, anchor_add, anchor_add, anchor_const, zero_add, anchor_smul, anchor_smul,
              hca, hcb, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun idx' _ => by
              rw [smul_smul, smul_smul, ← add_smul]
          | _ :: _ :: _ :: _ =>
            rw [hg_in] at hgl
            simp at hgl
  let G0 : Fin C.gates.length → Matrix (Fin d) (Fin d) F :=
    fun idx => (anchor (0 : Fin n) (0 : Fin n) (val (n + n + idx.val))).submatrix Fin.succ Fin.succ
  have hG0_rk : ∀ idx ∈ NL, (G0 idx).rank ≤ 2 := by
    intro idx hidx
    obtain ⟨r1, r2, s1, s2, houter⟩ := hNL_outer idx hidx
    let P2 : Matrix (Fin d) (Fin 2) F := fun i k => if k = 0 then r1 i.succ else r2 i.succ
    let Q2 : Matrix (Fin 2) (Fin d) F := fun k j => if k = 0 then s1 j.succ else s2 j.succ
    have hfac : G0 idx = P2 * Q2 := by
      ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_two]
      change (anchor (0 : Fin n) (0 : Fin n) (val (n + n + idx.val))) i.succ j.succ =
        P2 i 0 * Q2 0 j + P2 i 1 * Q2 1 j
      rw [houter]
      simp [Matrix.vecMulVec_apply, P2, Q2, show (1 : Fin 2) ≠ 0 by decide]
    rw [hfac]
    exact rank_of_factor P2 Q2
  obtain ⟨eNL⟩ : Nonempty (Fin NL.card ≃ NL) :=
    ⟨(Fintype.equivFinOfCardEq (Fintype.card_coe NL)).symm⟩
  let G : Fin t → Matrix (Fin d) (Fin d) F :=
    fun l => if hl : l.val < NL.card then G0 (eNL ⟨l.val, hl⟩).val else 0
  refine ⟨G, ?_, ?_⟩
  · intro l
    dsimp [G]
    split
    · rename_i hl
      exact hG0_rk (eNL ⟨l.val, hl⟩).val (eNL ⟨l.val, hl⟩).property
    · rw [Matrix.rank_zero]
      exact Nat.zero_le 2
  · intro Y w hd1 hrep
    obtain ⟨coeff, hcoeff⟩ := hspan w hd1
    have hveq : val w = fun x y => b2z (tableOf Y x y) := by
      funext x y
      unfold val
      rw [← hrep x y]
      rfl
    have hYeq : Y = ∑ idx ∈ NL, coeff idx • G0 idx := by
      rw [← tableOf_anchor_succ Y, ← hveq, hcoeff]
      ext i j
      simp [G0, Matrix.sum_apply]
    rw [hYeq]
    refine Submodule.sum_mem _ fun idx hidx => Submodule.smul_mem _ _ ?_
    let k : Fin NL.card := eNL.symm ⟨idx, hidx⟩
    let l : Fin t := ⟨k.val, lt_of_lt_of_le k.isLt hNL_card⟩
    refine Submodule.subset_span ⟨l, ?_⟩
    have hl : l.val < NL.card := k.isLt
    simp only [G, dif_pos hl]
    have hkl : (⟨l.val, hl⟩ : Fin NL.card) = k := Fin.ext rfl
    have heq : (eNL k).val = idx := congrArg Subtype.val (eNL.apply_symm_apply ⟨idx, hidx⟩)
    rw [hkl, heq]

private def Valid (n m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.inputs.length ≤ 2) ∧ ReadsBack (n + m) ⟨gs, 0⟩

private lemma valid_nil (n m : ℕ) : Valid n m [] := by
  exact ⟨by simp, by simp [ReadsBack]⟩

private lemma valid_snoc {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hbound : ∀ a ∈ g.inputs, a < n + m + gs.length) :
    Valid n m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with h | h
    · exact hv.1 g' h
    · rw [List.mem_singleton.mp h]
      exact hlen
  · intro j hj a ha
    change j < (gs ++ [g]).length at hj
    change a ∈ ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).inputs at ha
    by_cases hj' : j < gs.length
    · rw [List.getD_append _ _ _ _ hj'] at ha
      exact hv.2 j hj' a ha
    · have heq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      rw [List.getD_append_right _ _ _ _ le_rfl] at ha
      simp only [Nat.sub_self, List.getD_cons_zero] at ha
      exact hbound a ha

private lemma nlGate_or_nil : nlGate ⟨GateOp.or, []⟩ = false := rfl
private lemma nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := rfl
private lemma nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := rfl
private lemma nlGate_and (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := rfl

private def pushFalse (gs : List Gate) : List Gate := gs ++ [⟨GateOp.or, []⟩]

private def pushXor (n m : ℕ) (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [n + m + gs.length]⟩]

private def pushAnd (gs : List Gate) (a b : ℕ) : List Gate :=
  gs ++ [⟨GateOp.and, [a, b]⟩]

private lemma pushFalse_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) :
    let gs' := pushFalse gs
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 = 0 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) = 0) := by
  refine ⟨valid_snoc hv _ (by simp) (by simp), by simp [pushFalse], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushFalse, List.countP_append, nlGate_or_nil]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushFalse
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, nlGate_or_nil]
  · intro i j
    unfold pushFalse
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hl, GateOp.eval, b2z]

private lemma pushXor_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushXor n m gs a b
    let w := n + m + gs.length + 1
    Valid n m gs' ∧ gs'.length = gs.length + 2 ∧
    gs'.countP nlGate = gs.countP nlGate ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) +
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  let g1 : Gate := ⟨GateOp.mod 2, [a, b]⟩
  let g2 : Gate := ⟨GateOp.not, [n + m + gs.length]⟩
  have hsplit : pushXor n m gs a b = (gs ++ [g1]) ++ [g2] := by
    simp [pushXor, g1, g2]
  have hv1 : Valid n m (gs ++ [g1]) := valid_snoc hv g1 (by simp [g1]) (by
    intro x hx; simp only [g1, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption)
  have hv2 : Valid n m ((gs ++ [g1]) ++ [g2]) := valid_snoc hv1 g2 (by simp [g2]) (by
    intro x hx; simp only [g2, List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx; simp)
  refine ⟨hsplit ▸ hv2, by simp [pushXor], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushXor, List.countP_append, nlGate_mod2, nlGate_not]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · rw [hsplit, depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (depthsOf (n + m) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [depthsOf_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_not, Bool.toNat_false, add_zero, Nat.max_zero]
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_mod2, Bool.toNat_false, add_zero, Nat.max_zero]
  · intro i j
    rw [hsplit, wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl1 : (wiresOf (oneEach i j) (gs ++ [g1])).length = n + m + gs.length + 1 := by
      rw [wiresOf_length, oneEach_length]; simp; omega
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl1, Nat.sub_self, List.getD_cons_zero, g2, List.map_cons, List.map_nil]
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, g1, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

private lemma pushAnd_spec {n m : ℕ} {gs : List Gate} (hv : Valid n m gs) {a b : ℕ}
    (ha : a < n + m + gs.length) (hb : b < n + m + gs.length) :
    let gs' := pushAnd gs a b
    let w := n + m + gs.length
    Valid n m gs' ∧ gs'.length = gs.length + 1 ∧
    gs'.countP nlGate = gs.countP nlGate + 1 ∧
    (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
    (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
      (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
    (depthsOf (n + m) gs').getD w 0 =
      max ((depthsOf (n + m) gs).getD a 0) ((depthsOf (n + m) gs).getD b 0) + 1 ∧
    (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD w false) =
      b2z ((wiresOf (oneEach i j) gs).getD a false) *
      b2z ((wiresOf (oneEach i j) gs).getD b false)) := by
  refine ⟨valid_snoc hv _ (by simp) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption), by simp [pushAnd], ?_, ?_, ?_, ?_, ?_⟩
  · simp [pushAnd, List.countP_append, nlGate_and]
  · intro k hk
    exact depthsOf_append_getD_lt (n + m) gs _ hk
  · intro i j k hk
    exact wiresOf_append_getD_lt (oneEach i j) gs _ (by rw [oneEach_length]; exact hk)
  · unfold pushAnd
    rw [depthsOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (depthsOf (n + m) gs).length = n + m + gs.length := depthsOf_length (n + m) gs
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, nlGate_and, Bool.toNat_true, Nat.max_zero]
  · intro i j
    unfold pushAnd
    rw [wiresOf_append, List.foldl_cons, List.foldl_nil]
    have hl0 : (wiresOf (oneEach i j) gs).length = n + m + gs.length := by
      rw [wiresOf_length, oneEach_length]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp only [hl0, Nat.sub_self, List.getD_cons_zero, List.map_cons, List.map_nil]
    generalize (wiresOf (oneEach i j) gs).getD a false = va
    generalize (wiresOf (oneEach i j) gs).getD b false = vb
    cases va <;> cases vb <;> decide

private lemma build_xor_list {n m : ℕ} (D : ℕ) (ws : List ℕ) (gs : List Gate) (hv : Valid n m gs)
    (hb : ∀ w ∈ ws, w < n + m + gs.length)
    (hd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ D) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ D ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum) := by
  induction ws generalizing gs with
  | nil =>
    obtain ⟨hv', hlen', hcnt', hdp', hwp', hdout, hwout⟩ := pushFalse_spec hv
    exact ⟨pushFalse gs, n + m + gs.length, hv', by omega, by omega, hcnt', hdp', hwp',
      by omega, fun i j => by simpa using hwout i j⟩
  | cons w ws ih =>
    have hw_lt : w < n + m + gs.length := hb w List.mem_cons_self
    have hw_d : (depthsOf (n + m) gs).getD w 0 ≤ D := hd w List.mem_cons_self
    obtain ⟨gs1, out1, hv1, hle1, hout1, hcnt1, hdp1, hwp1, hd1, hw1⟩ :=
      ih gs hv (fun a ha => hb a (List.mem_cons_of_mem w ha))
        (fun a ha => hd a (List.mem_cons_of_mem w ha))
    obtain ⟨hv2, hlen2, hcnt2, hdp2, hwp2, hd2, hw2⟩ :=
      pushXor_spec hv1 (by omega : w < n + m + gs1.length) hout1
    refine ⟨pushXor n m gs1 w out1, n + m + gs1.length + 1, hv2, by omega, by omega,
      by omega, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hdp2 k (by omega), hdp1 k hk]
    · intro i j k hk
      rw [hwp2 i j k (by omega), hwp1 i j k hk]
    · rw [hd2, hdp1 w hw_lt]
      exact max_le hw_d hd1
    · intro i j
      rw [hw2 i j, hwp1 i j w hw_lt, hw1 i j]
      simp

private lemma build_row_fn {n m : ℕ} (f : Fin n → F) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = f i) := by
  let ws : List ℕ := ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map Fin.val
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin n, if f k = 1 then (if k = i then (1 : F) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange n).filter (fun k : Fin n => decide (f k = 1))).map
          (fun k : Fin n => if k = i then (1 : F) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega), oneEach_getD_left i j k.isLt]
      by_cases hki : k = i
      · subst hki; simp [b2z]
      · have hne : k.val ≠ i.val := fun e => hki (Fin.ext e)
        simp [b2z, hki, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin n)),
        ((l.filter (fun k => decide (f k = 1))).map (fun k => if k = i then (1 : F) else 0)).sum =
        (l.map (fun k => if f k = 1 then (if k = i then (1 : F) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hfa : f a = 1 <;> simp [hfa, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true]
    exact z2_ite_eq (f i)
  · intro k _ hki
    simp [hki]
  · intro h
    exact absurd (Finset.mem_univ i) h

private lemma build_col_fn {n m : ℕ} (g : Fin m → F) (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 = 0 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) = g j) := by
  let ws : List ℕ :=
    ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map (fun k => n + k.val)
  have hwb : ∀ w ∈ ws, w < n + m + gs.length := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    omega
  have hwd : ∀ w ∈ ws, (depthsOf (n + m) gs).getD w 0 ≤ 0 := by
    intro w hw
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hw
    rw [depthsOf_getD_input (n + m) gs (by omega)]
  obtain ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', hdout', hwout'⟩ :=
    build_xor_list 0 ws gs hv hwb hwd
  refine ⟨gs', out, hv', hle', hout', hcnt', hdp', hwp', by omega, fun i j => ?_⟩
  rw [hwout' i j]
  have hsum : (ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false))).sum =
      ∑ k : Fin m, if g k = 1 then (if k = j then (1 : F) else 0) else 0 := by
    have hmap : ws.map (fun w => b2z ((wiresOf (oneEach i j) gs).getD w false)) =
        ((List.finRange m).filter (fun k : Fin m => decide (g k = 1))).map
          (fun k : Fin m => if k = j then (1 : F) else 0) := by
      unfold ws
      rw [List.map_map]
      apply List.map_congr_left
      intro k _
      simp only [Function.comp_apply]
      rw [wiresOf_getD_input _ _ (by rw [oneEach_length]; omega),
        oneEach_getD_right i j (by omega) (by omega)]
      simp only [Nat.add_sub_cancel_left]
      by_cases hkj : k = j
      · subst hkj; simp [b2z]
      · have hne : k.val ≠ j.val := fun e => hkj (Fin.ext e)
        simp [b2z, hkj, hne]
    rw [hmap]
    have hfilt : ∀ (l : List (Fin m)),
        ((l.filter (fun k => decide (g k = 1))).map (fun k => if k = j then (1 : F) else 0)).sum =
        (l.map (fun k => if g k = 1 then (if k = j then (1 : F) else 0) else 0)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons a l ihl =>
        rw [List.filter_cons]
        by_cases hga : g a = 1 <;> simp [hga, ihl]
    rw [hfilt]
    rw [← Fin.sum_univ_def]
  rw [hsum]
  rw [Finset.sum_eq_single j]
  · simp only [ite_true]
    exact z2_ite_eq (g j)
  · intro k _ hkj
    simp [hkj]
  · intro h
    exact absurd (Finset.mem_univ j) h

private lemma build_pair_and {n m : ℕ} (a b : Fin n → F) (c d : Fin m → F)
    (gs : List Gate) (hv : Valid n m gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n m gs' ∧ gs.length ≤ gs'.length ∧ out < n + m + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate + 1 ∧
      (∀ k < n + m + gs.length, (depthsOf (n + m) gs').getD k 0 = (depthsOf (n + m) gs).getD k 0) ∧
      (∀ (i : Fin n) (j : Fin m), ∀ k < n + m + gs.length,
        (wiresOf (oneEach i j) gs').getD k false = (wiresOf (oneEach i j) gs).getD k false) ∧
      (depthsOf (n + m) gs').getD out 0 ≤ 1 ∧
      (∀ (i : Fin n) (j : Fin m), b2z ((wiresOf (oneEach i j) gs').getD out false) =
        (a i + d j) * (b i + c j)) := by
  obtain ⟨gs1, wa, hv1, hl1, hwa, hc1, hd1, hw1, hda, hfa⟩ := build_row_fn a gs hv
  obtain ⟨gs2, wd, hv2, hl2, hwd, hc2, hd2, hw2, hdd, hfd⟩ := build_col_fn d gs1 hv1
  obtain ⟨hv3, hl3, hc3, hd3, hw3, hdL, hwL⟩ :=
    pushXor_spec hv2 (by omega : wa < n + m + gs2.length) hwd
  set gs3 := pushXor n m gs2 wa wd
  let wL := n + m + gs2.length + 1
  obtain ⟨gs4, wb, hv4, hl4, hwb, hc4, hd4, hw4, hdb, hfb⟩ := build_row_fn b gs3 hv3
  obtain ⟨gs5, wc, hv5, hl5, hwc, hc5, hd5, hw5, hdc, hfc⟩ := build_col_fn c gs4 hv4
  obtain ⟨hv6, hl6, hc6, hd6, hw6, hdR, hwR⟩ :=
    pushXor_spec hv5 (by omega : wb < n + m + gs5.length) hwc
  set gs6 := pushXor n m gs5 wb wc
  let wR := n + m + gs5.length + 1
  obtain ⟨hv7, hl7, hc7, hd7, hw7, hdP, hwP⟩ :=
    pushAnd_spec hv6 (by omega : wL < n + m + gs6.length) (by omega : wR < n + m + gs6.length)
  set gs7 := pushAnd gs6 wL wR
  let out := n + m + gs6.length
  refine ⟨gs7, out, hv7, by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [hd7 k (by omega), hd6 k (by omega), hd5 k (by omega), hd4 k (by omega),
      hd3 k (by omega), hd2 k (by omega), hd1 k hk]
  · intro i j k hk
    rw [hw7 i j k (by omega), hw6 i j k (by omega), hw5 i j k (by omega), hw4 i j k (by omega),
      hw3 i j k (by omega), hw2 i j k (by omega), hw1 i j k hk]
  · rw [hdP]
    have hL0 : (depthsOf (n + m) gs6).getD wL 0 = 0 := by
      rw [hd6 wL (by omega), hd5 wL (by omega), hd4 wL (by omega), hdL, hd2 wa hwa, hda, hdd]
      simp
    have hR0 : (depthsOf (n + m) gs6).getD wR 0 = 0 := by
      rw [hdR, hd5 wb hwb, hdb, hdc]
      simp
    rw [hL0, hR0]
    simp
  · intro i j
    rw [hwP i j]
    have hLv : b2z ((wiresOf (oneEach i j) gs6).getD wL false) = a i + d j := by
      rw [hw6 i j wL (by omega), hw5 i j wL (by omega), hw4 i j wL (by omega),
        hwL i j, hw2 i j wa hwa, hfa i j, hfd i j]
    have hRv : b2z ((wiresOf (oneEach i j) gs6).getD wR false) = b i + c j := by
      rw [hwR i j, hw5 i j wb hwb, hfb i j, hfc i j]
    rw [hLv, hRv]

private lemma build_sym_prod {n : ℕ} (p q : Fin n → F) (gs : List Gate) (hv : Valid n n gs) :
    ∃ (gs' : List Gate) (out : ℕ),
      Valid n n gs' ∧ gs.length ≤ gs'.length ∧ out < n + n + gs'.length ∧
      gs'.countP nlGate = gs.countP nlGate + 1 ∧
      (∀ k < n + n + gs.length, (depthsOf (n + n) gs').getD k 0 = (depthsOf (n + n) gs).getD k 0) ∧
      (∀ (x y : Fin n), ∀ k < n + n + gs.length,
        (wiresOf (oneEach x y) gs').getD k false = (wiresOf (oneEach x y) gs).getD k false) ∧
      (depthsOf (n + n) gs').getD out 0 ≤ 1 ∧
      (∀ (x y : Fin n), b2z ((wiresOf (oneEach x y) gs').getD out false) =
        p x * q y + q x * p y) := by
  obtain ⟨gs1, w1, hv1, hl1, hw1, hc1, hd1, hwp1, hdw1, hfv1⟩ :=
    build_pair_and p q q p gs hv
  obtain ⟨gs2, w2, hv2, hl2, hw2, hc2, hd2, hwp2, hdw2, hfv2⟩ :=
    build_row_fn (fun x => p x * q x) gs1 hv1
  obtain ⟨gs3, w3, hv3, hl3, hw3, hc3, hd3, hwp3, hdw3, hfv3⟩ :=
    build_col_fn (fun y => p y * q y) gs2 hv2
  obtain ⟨gs4, out, hv4, hl4, hout, hc4, hd4, hwp4, hdout, hwout⟩ :=
    build_xor_list 1 [w1, w2, w3] gs3 hv3
      (by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> omega)
      (by
        intro w hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · rw [hd3 w (by omega), hd2 w hw1]; exact hdw1
        · rw [hd3 w hw2, hdw2]; omega
        · rw [hdw3]; omega)
  refine ⟨gs4, out, hv4, by omega, hout, by omega, ?_, ?_, hdout, ?_⟩
  · intro k hk
    rw [hd4 k (by omega), hd3 k (by omega), hd2 k (by omega), hd1 k hk]
  · intro x y k hk
    rw [hwp4 x y k (by omega), hwp3 x y k (by omega), hwp2 x y k (by omega), hwp1 x y k hk]
  · intro x y
    rw [hwout x y]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hwp3 x y w1 (by omega), hwp2 x y w1 hw1, hfv1 x y,
      hwp3 x y w2 hw2, hfv2 x y, hfv3 x y]
    have h2 : (p x + p y) * (q x + q y) + (p x * q x + p y * q y) =
        p x * q y + q x * p y + (2 : F) * (p x * q x + p y * q y) := by ring
    rw [h2, z2_two, zero_mul, add_zero]

private lemma build_gen_bank {n : ℕ} (k : ℕ) (p q : Fin k → Fin n → F)
    (gs : List Gate) (hv : Valid n n gs) :
    ∃ (gs' : List Gate) (genW : Fin k → ℕ),
      Valid n n gs' ∧ gs.length ≤ gs'.length ∧
      (∀ s : Fin k, genW s < n + n + gs'.length) ∧
      (∀ s : Fin k, (depthsOf (n + n) gs').getD (genW s) 0 ≤ 1) ∧
      gs'.countP nlGate = gs.countP nlGate + k ∧
      (∀ r < n + n + gs.length, (depthsOf (n + n) gs').getD r 0 = (depthsOf (n + n) gs).getD r 0) ∧
      (∀ (x y : Fin n), ∀ r < n + n + gs.length,
        (wiresOf (oneEach x y) gs').getD r false = (wiresOf (oneEach x y) gs).getD r false) ∧
      (∀ (s : Fin k) (x y : Fin n),
        b2z ((wiresOf (oneEach x y) gs').getD (genW s) false) = p s x * q s y + q s x * p s y) := by
  induction k generalizing gs with
  | zero =>
    exact ⟨gs, Fin.elim0, hv, le_rfl, fun s => Fin.elim0 s, fun s => Fin.elim0 s,
      by simp, fun _ _ => rfl, fun _ _ _ _ => rfl, fun s => Fin.elim0 s⟩
  | succ k ih =>
    obtain ⟨gs1, w0, hv1, hl1, hw0, hc1, hd1, hwp1, hdw0, hfv0⟩ :=
      build_sym_prod (p 0) (q 0) gs hv
    obtain ⟨gs2, genW', hv2, hl2, hgenb, hgend, hc2, hd2, hwp2, hfv2⟩ :=
      ih (fun s => p s.succ) (fun s => q s.succ) gs1 hv1
    refine ⟨gs2, Fin.cases w0 genW', hv2, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro s
      refine Fin.cases ?_ ?_ s
      · simp; omega
      · intro s'; exact hgenb s'
    · intro s
      refine Fin.cases ?_ ?_ s
      · simp only [Fin.cases_zero]
        rw [hd2 w0 hw0]
        exact hdw0
      · intro s'; exact hgend s'
    · intro r hr
      rw [hd2 r (by omega), hd1 r hr]
    · intro x y r hr
      rw [hwp2 x y r (by omega), hwp1 x y r hr]
    · intro s x y
      refine Fin.cases ?_ ?_ s
      · simp only [Fin.cases_zero]
        rw [hwp2 x y w0 hw0]
        exact hfv0 x y
      · intro s'; exact hfv2 s' x y

private lemma list_filter_sum_fin {k : ℕ} (c : Fin k → F) (f : Fin k → F) :
    (((List.finRange k).filter (fun s => decide (c s = 1))).map f).sum =
      ∑ s : Fin k, c s * f s := by
  have hfilt : ∀ (l : List (Fin k)),
      ((l.filter (fun s => decide (c s = 1))).map f).sum =
      (l.map (fun s => if c s = 1 then f s else 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ihl =>
      rw [List.filter_cons]
      by_cases hca : c a = 1 <;> simp [hca, ihl]
  rw [hfilt, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun s _ => z2_ite_mul (c s) (f s)

private lemma build_combo_bank {n k N : ℕ} (genW : Fin k → ℕ)
    (coeffs : Fin N → Fin k → F) (gs : List Gate) (hv : Valid n n gs)
    (hb : ∀ s : Fin k, genW s < n + n + gs.length)
    (hd : ∀ s : Fin k, (depthsOf (n + n) gs).getD (genW s) 0 ≤ 1) :
    ∃ (gs' : List Gate) (outW : Fin N → ℕ),
      Valid n n gs' ∧ gs.length ≤ gs'.length ∧
      (∀ u : Fin N, outW u < n + n + gs'.length) ∧
      (∀ u : Fin N, (depthsOf (n + n) gs').getD (outW u) 0 ≤ 1) ∧
      gs'.countP nlGate = gs.countP nlGate ∧
      (∀ r < n + n + gs.length, (depthsOf (n + n) gs').getD r 0 = (depthsOf (n + n) gs).getD r 0) ∧
      (∀ (x y : Fin n), ∀ r < n + n + gs.length,
        (wiresOf (oneEach x y) gs').getD r false = (wiresOf (oneEach x y) gs).getD r false) ∧
      (∀ (u : Fin N) (x y : Fin n),
        b2z ((wiresOf (oneEach x y) gs').getD (outW u) false) =
          ∑ s : Fin k, coeffs u s * b2z ((wiresOf (oneEach x y) gs).getD (genW s) false)) := by
  induction N generalizing gs with
  | zero =>
    exact ⟨gs, Fin.elim0, hv, le_rfl, fun u => Fin.elim0 u, fun u => Fin.elim0 u,
      rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, fun u => Fin.elim0 u⟩
  | succ N ih =>
    let ws0 : List ℕ :=
      ((List.finRange k).filter (fun s => decide (coeffs 0 s = 1))).map genW
    have hwb0 : ∀ w ∈ ws0, w < n + n + gs.length := by
      intro w hw
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hw
      exact hb s
    have hwd0 : ∀ w ∈ ws0, (depthsOf (n + n) gs).getD w 0 ≤ 1 := by
      intro w hw
      obtain ⟨s, _, rfl⟩ := List.mem_map.mp hw
      exact hd s
    obtain ⟨gs1, w0, hv1, hl1, hw0, hc1, hd1, hwp1, hdw0, hwv0⟩ :=
      build_xor_list 1 ws0 gs hv hwb0 hwd0
    obtain ⟨gs2, outW', hv2, hl2, houtb, houtd, hc2, hd2, hwp2, hfv2⟩ :=
      ih (fun u => coeffs u.succ) gs1 hv1
        (fun s => lt_of_lt_of_le (hb s) (by omega))
        (fun s => by rw [hd1 (genW s) (hb s)]; exact hd s)
    refine ⟨gs2, Fin.cases w0 outW', hv2, by omega, ?_, ?_, by omega, ?_, ?_, ?_⟩
    · intro u
      refine Fin.cases ?_ ?_ u
      · simp; omega
      · intro u'; exact houtb u'
    · intro u
      refine Fin.cases ?_ ?_ u
      · simp only [Fin.cases_zero]
        rw [hd2 w0 hw0]
        exact hdw0
      · intro u'; exact houtd u'
    · intro r hr
      rw [hd2 r (by omega), hd1 r hr]
    · intro x y r hr
      rw [hwp2 x y r (by omega), hwp1 x y r hr]
    · intro u x y
      refine Fin.cases ?_ ?_ u
      · simp only [Fin.cases_zero]
        rw [hwp2 x y w0 hw0, hwv0 x y]
        unfold ws0
        rw [List.map_map]
        exact list_filter_sum_fin (coeffs 0)
          (fun s => b2z ((wiresOf (oneEach x y) gs).getD (genW s) false))
      · intro u'
        simp only [Fin.cases_succ]
        rw [hfv2 u' x y]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hwp1 x y (genW s) (hb s)]

private def e3 (i : Fin 3) : Fin 3 → F := Pi.single i 1

private def inlVec {m : ℕ} (u : Fin 3 → F) : Idx 3 m → F :=
  Sum.elim u 0

private def midVec {m : ℕ} (j : Fin m) : Idx 3 m → F :=
  Sum.elim 0 (Sum.elim (Pi.single j 1) 0)

private def inrVec {m : ℕ} (v : Fin 3 → F) : Idx 3 m → F :=
  Sum.elim 0 (Sum.elim 0 v)

private def symMat {ι : Type*} (u v : ι → F) : Matrix ι ι F :=
  fun x y => u x * v y + v x * u y

private lemma congr_symMat {ι κ : Type*} [Fintype ι]
    (P : Matrix κ ι F) (u v : ι → F) (i j : κ) :
    (P * symMat u v * P.transpose) i j =
      (P *ᵥ u) i * (P *ᵥ v) j + (P *ᵥ v) i * (P *ᵥ u) j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, symMat, Matrix.mulVec, dotProduct]
  simp_rw [mul_add, Finset.sum_add_distrib, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

private def uA : Fin 3 → (Fin 3 → F)
  | 0 => e3 0
  | 1 => e3 0
  | 2 => e3 1

private def vA : Fin 3 → (Fin 3 → F)
  | 0 => e3 1
  | 1 => e3 2
  | 2 => e3 2

private def coeffA (A : Matrix (Fin 3) (Fin 3) F) : Fin 3 → F
  | 0 => A 0 1
  | 1 => A 0 2
  | 2 => A 1 2

private def u5 : Fin 5 → (Fin 3 → F)
  | 0 => e3 0
  | 1 => e3 1
  | 2 => e3 0 + e3 2
  | 3 => e3 2
  | 4 => e3 1 + e3 2

private def v5 : Fin 5 → (Fin 3 → F)
  | 0 => e3 1
  | 1 => e3 0
  | 2 => e3 1 + e3 2
  | 3 => e3 0 + e3 1 + e3 2
  | 4 => e3 0 + e3 2

private def coeffK (K : Matrix (Fin 3) (Fin 3) F) : Fin 5 → F
  | 0 => K 0 1 + K 0 2
  | 1 => K 0 1 + K 1 2
  | 2 => K 0 2
  | 3 => K 0 2 + K 1 2
  | 4 => K 1 2

private lemma sum_A_decomp (A : Matrix (Fin 3) (Fin 3) F) (hA : Alt A) (i j : Fin 3) :
    ∑ k : Fin 3, coeffA A k * (uA k i * vA k j + vA k i * uA k j) = A i j := by
  rw [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [coeffA, uA, vA, e3, Pi.single_apply, hA.2] <;>
    exact alt_entry_symm hA _ _

private lemma sum_K_decomp (K : Matrix (Fin 3) (Fin 3) F) (hK : Alt K) (i j : Fin 3) :
    ∑ k : Fin 5, coeffK K k * (u5 k i * v5 k j) = K i j := by
  have h01 : K 1 0 = K 0 1 := alt_entry_symm hK 1 0
  have h02 : K 2 0 = K 0 2 := alt_entry_symm hK 2 0
  have h12 : K 2 1 = K 1 2 := alt_entry_symm hK 2 1
  have hd0 : K 0 0 = 0 := hK.2 0
  have hd1 : K 1 1 = 0 := hK.2 1
  have hd2 : K 2 2 = 0 := hK.2 2
  rw [Fin.sum_univ_five]
  fin_cases i <;> fin_cases j <;>
    simp [coeffK, u5, v5, e3, Pi.single_apply, hd0, hd1, hd2, h01, h02, h12] <;>
    (generalize K 0 1 = a; generalize K 0 2 = b; generalize K 1 2 = c; revert a b c; decide)

private abbrev GenIdx (m : ℕ) := Fin 3 ⊕ (Fin 3 × Fin m) ⊕ Fin 5

private lemma card_genIdx (m : ℕ) : Fintype.card (GenIdx m) = 3 * m + 8 := by
  simp only [GenIdx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  omega

private def genAlpha {m : ℕ} : GenIdx m → (Idx 3 m → F)
  | Sum.inl k => inlVec (uA k)
  | Sum.inr (Sum.inl p) => inlVec (e3 p.1)
  | Sum.inr (Sum.inr k) => inlVec (u5 k)

private def genBeta {m : ℕ} : GenIdx m → (Idx 3 m → F)
  | Sum.inl k => inlVec (vA k)
  | Sum.inr (Sum.inl p) => midVec p.2
  | Sum.inr (Sum.inr k) => inrVec (v5 k)

private def genCoeff {m : ℕ} (X : Matrix (Idx 3 m) (Idx 3 m) F) : GenIdx m → F
  | Sum.inl k => coeffA (fun i j => X (Sum.inl i) (Sum.inl j)) k
  | Sum.inr (Sum.inl p) => X (Sum.inl p.1) (Sum.inr (Sum.inl p.2))
  | Sum.inr (Sum.inr k) => coeffK (fun i j => X (Sum.inl i) (Sum.inr (Sum.inr j))) k

private lemma wfull_gen_decomp {m : ℕ} {X : Matrix (Idx 3 m) (Idx 3 m) F} (hX : X ∈ Wfull m) :
    X = ∑ g : GenIdx m, genCoeff X g • symMat (genAlpha g) (genBeta g) := by
  obtain ⟨A, B, K, hA, hK, rfl⟩ := (mem_Wfull_iff X).mp hX
  have hAblk : (fun i j => Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0
      (Sum.inl i) (Sum.inl j)) = A := rfl
  have hBblk : ∀ i j, Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0
      (Sum.inl i) (Sum.inr (Sum.inl j)) = B i j := fun _ _ => rfl
  have hKblk : (fun i j => Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0
      (Sum.inl i) (Sum.inr (Sum.inr j))) = K := rfl
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fintype.sum_sum_type,
    genCoeff, genAlpha, genBeta, hAblk, hBblk, hKblk]
  rcases x with i | (i | i) <;> rcases y with j | (j | j)
  · have h1 : ∑ p : Fin 3 × Fin m, B p.1 p.2 * symMat (inlVec (m := m) (e3 p.1)) (midVec p.2)
        (Sum.inl i) (Sum.inl j) = 0 := by
      simp [symMat, inlVec, midVec]
    have h2 : ∑ k : Fin 5, coeffK K k * symMat (inlVec (m := m) (u5 k)) (inrVec (m := m) (v5 k))
        (Sum.inl i) (Sum.inl j) = 0 := by
      simp [symMat, inlVec, inrVec]
    rw [h1, h2, add_zero, add_zero]
    simp only [Matrix.fromBlocks, symMat, inlVec, Sum.elim_inl]
    exact (sum_A_decomp A hA i j).symm
  · have h0 : ∑ k : Fin 3, coeffA A k * symMat (inlVec (m := m) (uA k)) (inlVec (m := m) (vA k))
        (Sum.inl i) (Sum.inr (Sum.inl j)) = 0 := by
      simp [symMat, inlVec]
    have h2 : ∑ k : Fin 5, coeffK K k * symMat (inlVec (m := m) (u5 k)) (inrVec (m := m) (v5 k))
        (Sum.inl i) (Sum.inr (Sum.inl j)) = 0 := by
      simp [symMat, inlVec, inrVec]
    rw [h0, h2, zero_add, add_zero]
    simp only [Matrix.fromBlocks, Cmat, symMat, inlVec, midVec, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, add_zero]
    rw [Finset.sum_eq_single (i, j)]
    · simp [Matrix.fromBlocks, Cmat, e3, Pi.single_apply]
    · intro p _ hp
      by_cases h1 : p.1 = i
      · have h2 : p.2 ≠ j := fun e => hp (Prod.ext h1 e)
        simp [e3, Pi.single_apply, h2, Ne.symm h2]
      · simp [e3, Pi.single_apply, h1, Ne.symm h1]
    · intro h; exact absurd (Finset.mem_univ (i, j)) h
  · have h0 : ∑ k : Fin 3, coeffA A k * symMat (inlVec (m := m) (uA k)) (inlVec (m := m) (vA k))
        (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
      simp [symMat, inlVec]
    have h1 : ∑ p : Fin 3 × Fin m, B p.1 p.2 * symMat (inlVec (m := m) (e3 p.1)) (midVec p.2)
        (Sum.inl i) (Sum.inr (Sum.inr j)) = 0 := by
      simp [symMat, inlVec, midVec]
    rw [h0, h1, zero_add, zero_add]
    simp only [Matrix.fromBlocks, Cmat, symMat, inlVec, inrVec, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, add_zero]
    exact (sum_K_decomp K hK i j).symm
  · have h0 : ∑ k : Fin 3, coeffA A k * symMat (inlVec (m := m) (uA k)) (inlVec (m := m) (vA k))
        (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := by
      simp [symMat, inlVec]
    have h2 : ∑ k : Fin 5, coeffK K k * symMat (inlVec (m := m) (u5 k)) (inrVec (m := m) (v5 k))
        (Sum.inr (Sum.inl i)) (Sum.inl j) = 0 := by
      simp [symMat, inlVec, inrVec]
    rw [h0, h2, zero_add, add_zero]
    simp only [Matrix.fromBlocks, Cmat, Matrix.transpose_apply, symMat, inlVec, midVec,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, zero_add]
    rw [Finset.sum_eq_single (j, i)]
    · simp [Matrix.fromBlocks, Cmat, Matrix.transpose_apply, e3, Pi.single_apply]
    · intro p _ hp
      by_cases h1 : p.1 = j
      · have h2 : p.2 ≠ i := fun e => hp (Prod.ext h1 e)
        simp [e3, Pi.single_apply, h2, Ne.symm h2]
      · simp [e3, Pi.single_apply, h1, Ne.symm h1]
    · intro h; exact absurd (Finset.mem_univ (j, i)) h
  · simp [Matrix.fromBlocks, symMat, inlVec, midVec, inrVec]
  · simp [Matrix.fromBlocks, symMat, inlVec, midVec, inrVec]
  · have h0 : ∑ k : Fin 3, coeffA A k * symMat (inlVec (m := m) (uA k)) (inlVec (m := m) (vA k))
        (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
      simp [symMat, inlVec]
    have h1 : ∑ p : Fin 3 × Fin m, B p.1 p.2 * symMat (inlVec (m := m) (e3 p.1)) (midVec p.2)
        (Sum.inr (Sum.inr i)) (Sum.inl j) = 0 := by
      simp [symMat, inlVec, midVec]
    rw [h0, h1, zero_add, zero_add]
    simp only [Matrix.fromBlocks, Cmat, Matrix.transpose_apply, symMat, inlVec, inrVec,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul, zero_add]
    have hcomm : ∑ k : Fin 5, coeffK K k * (v5 k i * u5 k j) =
        ∑ k : Fin 5, coeffK K k * (u5 k j * v5 k i) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hcomm]
    exact (sum_K_decomp K hK j i).symm
  · simp [Matrix.fromBlocks, symMat, inlVec, midVec, inrVec]
  · simp [Matrix.fromBlocks, symMat, inlVec, midVec, inrVec]

private def padZero {d : ℕ} (w : Fin d → F) : Fin (d + 1) → F :=
  Fin.cases 0 w

private lemma upper_bank {d m : ℕ} (U : Matrix (Fin d) (Fin d) F)
    (P : Matrix (Fin d) (Idx 3 m) F) (Q : Matrix (Idx 3 m) (Fin d) F)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) (hV : Q * U * P = 1 + Nmat 3 m) :
    ∃ (C : Circuit) (tap : Matrix (Fin d) (Fin d) F → ℕ),
      ReadsBack ((d + 1) + (d + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ 3 * m + 8 ∧
      ∀ H : Matrix (Fin d) (Fin d) F, Alt H →
        (depthsOf ((d + 1) + (d + 1)) C.gates).getD (tap H) 0 ≤ 1 ∧
        Represents (tableOf (U * H * U.transpose + H)) ⟨C.gates, tap H⟩ := by
  classical
  let k := 3 * m + 8
  let eG : Fin k ≃ GenIdx m := (Fintype.equivFinOfCardEq (card_genIdx m)).symm
  let p : Fin k → Fin (d + 1) → F := fun s => padZero (P *ᵥ genAlpha (eG s))
  let q : Fin k → Fin (d + 1) → F := fun s => padZero (P *ᵥ genBeta (eG s))
  obtain ⟨gs1, genW, hv1, hl1, hgb1, hgd1, hc1, _, _, hgv1⟩ :=
    build_gen_bank k p q [] (valid_nil (d + 1) (d + 1))
  let N := Fintype.card (Fin k → F)
  let eC : Fin N ≃ (Fin k → F) := (Fintype.equivFin (Fin k → F)).symm
  obtain ⟨gs2, outW, hv2, hl2, houtb, houtd, hc2, hd2, hwp2, hfv2⟩ :=
    build_combo_bank genW (fun u => eC u) gs1 hv1 hgb1 hgd1
  let tap : Matrix (Fin d) (Fin d) F → ℕ := fun H =>
    let X := Q * (U * H * U.transpose + H) * Q.transpose
    outW (eC.symm (fun s => genCoeff X (eG s)))
  refine ⟨⟨gs2, 0⟩, tap, hv2.2, hv2.1, ?_, ?_⟩
  · change gs2.countP nlGate ≤ k
    simp only [List.countP_nil, zero_add] at hc1
    omega
  · intro H hH
    let Y := U * H * U.transpose + H
    let X := Q * Y * Q.transpose
    let c : Fin k → F := fun s => genCoeff X (eG s)
    let u : Fin N := eC.symm c
    have htap : tap H = outW u := rfl
    refine ⟨htap ▸ houtd u, ?_⟩
    have hXin : X ∈ Wfull m := by
      have hXimg : X ∈ imageSet (1 + Nmat 3 m) := by
        rw [← hV, ← image_transport U P Q hPQ hQP]
        exact ⟨Y, ⟨H, hH, rfl⟩, rfl⟩
      exact (mem_Wfull_iff X).mpr ((imageBlocks X).mp hXimg)
    have hYeq : P * X * P.transpose = Y :=
      (matrixCongr Q P hPQ hQP).left_inv Y
    have hXsum : X = ∑ s : Fin k, c s • symMat (genAlpha (eG s)) (genBeta (eG s)) := by
      rw [wfull_gen_decomp hXin]
      exact (Equiv.sum_comp eG (fun g => genCoeff X g • symMat (genAlpha g) (genBeta g))).symm
    intro x y
    apply b2z_inj
    change b2z ((wiresOf (oneEach x y) gs2).getD (outW u) false) = b2z (tableOf Y x y)
    rw [hfv2 u x y]
    have heCu : eC u = c := eC.apply_symm_apply c
    rw [heCu]
    have hval : ∑ s : Fin k, c s * b2z ((wiresOf (oneEach x y) gs1).getD (genW s) false) =
        ∑ s : Fin k, c s * (p s x * q s y + q s x * p s y) :=
      Finset.sum_congr rfl fun s _ => by rw [hgv1 s x y]
    rw [hval]
    refine Fin.cases ?_ ?_ x
    · simp only [p, q, padZero, Fin.cases_zero, zero_mul, mul_zero, add_zero, Finset.sum_const_zero]
      rfl
    · intro i
      refine Fin.cases ?_ ?_ y
      · simp only [p, q, padZero, Fin.cases_zero, Fin.cases_succ, mul_zero, add_zero,
          Finset.sum_const_zero]
        rfl
      · intro j
        simp only [p, q, padZero, Fin.cases_succ, tableOf, b2z_decide_ne_zero]
        rw [← hYeq, hXsum, Matrix.mul_sum, Matrix.sum_mul]
        simp only [Matrix.sum_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
          smul_eq_mul]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [congr_symMat P (genAlpha (eG s)) (genBeta (eG s)) i j]

private lemma main_iff (d : ℕ) (U : Matrix (Fin d) (Fin d) F) (hU : U * U = 1)
    (hr : (U - 1).rank = 3) (t : ℕ) :
    (∃ (C : Circuit) (tap : Matrix (Fin d) (Fin d) F → ℕ),
      ReadsBack ((d + 1) + (d + 1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nlGate ≤ t ∧
      ∀ H : Matrix (Fin d) (Fin d) F, Alt H →
        (depthsOf ((d + 1) + (d + 1)) C.gates).getD (tap H) 0 ≤ 1 ∧
        Represents (tableOf (U * H * U.transpose + H)) ⟨C.gates, tap H⟩) ↔
    3 * (d - 3 - 1) + 2 ≤ t := by
  obtain ⟨m, P, Q, hd, hPQ, hQP, hN⟩ :=
    squareZero_normalize (U - 1) (invol_sub_square U hU) hr
  have hV : Q * U * P = 1 + Nmat 3 m := by
    have hU' : U = (U - 1) + 1 := (sub_add_cancel U 1).symm
    calc
      Q * U * P = Q * ((U - 1) + 1) * P := congrArg (fun X => Q * X * P) hU'
      _ = 1 + Nmat 3 m := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hN, hQP, add_comm]
  have hD : 3 * (d - 3 - 1) = 3 * m + 6 := by omega
  rw [hD]
  constructor
  · rintro ⟨C, tap, hrb, hlen, hcnt, htap⟩
    obtain ⟨G, hGrk, hGspan⟩ := extract_rank2_gens C hrb hlen hcnt
    let e := matrixCongr Q P hPQ hQP
    let R : Fin t → Matrix (Idx 3 m) (Idx 3 m) F := fun l => e (G l)
    have hRrk : ∀ l, (R l).rank ≤ 2 := fun l => by
      change (Q * G l * Q.transpose).rank ≤ 2
      rw [congr_rank Q P hPQ]
      exact hGrk l
    have hWS : Wfull m ≤ Submodule.span F (Set.range R) := by
      intro X hX
      have hXimg : X ∈ imageSet (Q * U * P) := by
        rw [hV]
        exact (imageBlocks X).mpr ((mem_Wfull_iff X).mp hX)
      rw [← image_transport U P Q hPQ hQP] at hXimg
      obtain ⟨Y, ⟨H, hH, rfl⟩, rfl⟩ := hXimg
      obtain ⟨hd1, hrep⟩ := htap H hH
      have hYspan : U * H * U.transpose + H ∈ Submodule.span F (Set.range G) :=
        hGspan (U * H * U.transpose + H) (tap H) hd1 hrep
      have hmap : e (U * H * U.transpose + H) ∈
          (Submodule.span F (Set.range G)).map e.toLinearMap :=
        Submodule.mem_map_of_mem hYspan
      rw [Submodule.map_span] at hmap
      have hrange : e.toLinearMap '' Set.range G = Set.range R := by
        ext Z
        simp [R]
      rwa [hrange] at hmap
    obtain ⟨hDt, hpow⟩ := part2_full R hRrk hWS
    rw [finrank_Wfull m] at hDt hpow
    by_cases h0 : t - (3 * m + 6) = 0
    · rw [h0] at hpow
      omega
    · by_cases h1 : t - (3 * m + 6) = 1
      · rw [h1] at hpow
        omega
      · omega
  · intro ht
    obtain ⟨C, tap, hrb, hlen, hcnt, htap⟩ := upper_bank U P Q hPQ hQP hV
    exact ⟨C, tap, hrb, hlen, le_trans hcnt ht, htap⟩

end PEqualNP.Outside.L_meta_32572

theorem PEqualNP.Outside.L_meta_32572 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
  let Mat := Matrix (Fin d) (Fin d) F
  let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
  let r := (U-1).rank
  let table := fun (H : Mat) (x y : Fin (d+1)) =>
    Fin.cases false (fun i => Fin.cases false (fun j => decide (H i j ≠ 0)) y) x
  let D := r*(d-r-1)
  let bank := fun (t : ℕ) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Mat → ℕ),
      PEqualNP.MetaComplexity.NestedCover.ReadsBack ((d+1)+(d+1)) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ H : Mat, alt H →
        (depths ((d+1)+(d+1)) C).getD (tap H) 0 ≤ 1 ∧
        PEqualNP.Represents.Represents (table (U*H*U.transpose + H)) ⟨C.gates, tap H⟩
  r = 3 → ∀ t : ℕ, bank t ↔ D+2 ≤ t) := by
  dsimp only
  intro d U hU hr t
  rw [hr]
  exact PEqualNP.Outside.L_meta_32572.main_iff d U hU hr t
