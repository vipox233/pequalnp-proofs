import Mathlib

open Matrix
open scoped BigOperators

namespace PEqualNP.Outside.L_lib_923

private abbrev F := ZMod 2
private abbrev Idx (r m : ℕ) := Fin r ⊕ (Fin m ⊕ Fin r)

private def Alt {ι : Type*} (X : Matrix ι ι F) : Prop :=
  X.transpose = X ∧ ∀ i, X i i = 0

private lemma char2_add_self (a : F) : a + a = 0 := by
  rw [← two_mul, show (2 : F) = 0 by decide, zero_mul]

private lemma alt_entry_symm {ι : Type*} {H : Matrix ι ι F} (hH : Alt H) (i j : ι) :
    H i j = H j i := congrFun (congrFun hH.1 j) i

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
    exact char2_add_self _

private lemma alt_bilin_zero {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι F} (hH : Alt H)
    (x : ι → F) : H.toBilin' x x = 0 := by
  classical
  rw [Matrix.toBilin'_apply]
  refine symm_zero_diag_sum Finset.univ (fun i j => x i * H i j * x j) ?_ ?_
  · intro i
    simp [hH.2 i]
  · intro i j
    rw [alt_entry_symm hH i j]
    ring

private lemma congr_alt {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : Matrix κ ι F) {H : Matrix ι ι F} (hH : Alt H) : Alt (P * H * P.transpose) := by
  classical
  constructor
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hH.1, Matrix.mul_assoc]
  · intro i
    rw [← Matrix.toBilin'_single (P * H * P.transpose) i i]
    have h := Matrix.toBilin'_comp H P.transpose P.transpose
    rw [Matrix.transpose_transpose] at h
    rw [← h]
    exact alt_bilin_zero hH _

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
private def N (r m : ℕ) : Matrix (Idx r m) (Idx r m) F
  | Sum.inl i, Sum.inr (Sum.inr j) => if i = j then 1 else 0
  | _, _ => 0

private def Cmat {r m : ℕ} (B : Matrix (Fin r) (Fin m) F)
    (K : Matrix (Fin r) (Fin r) F) : Matrix (Fin r) (Fin m ⊕ Fin r) F :=
  fun i j => Sum.elim (B i) (K i) j

private theorem image_left {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F)
    (i : Idx r m) (j : Idx r m) :
    (N r m * H) i j = Sum.elim (fun k => H (Sum.inr (Sum.inr k)) j) (fun _ => 0) i := by
  rcases i with i | (i | i) <;>
    simp [N, Matrix.mul_apply, Fintype.sum_sum_type, ite_mul]

private theorem image_right {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F)
    (i : Idx r m) (j : Idx r m) :
    (H * (N r m).transpose) i j =
      Sum.elim (fun k => H i (Sum.inr (Sum.inr k))) (fun _ => 0) j := by
  rcases j with j | (j | j) <;>
    simp [N, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_sum_type, mul_ite]

private theorem image_expand {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F) :
    (1 + N r m) * H * (1 + N r m).transpose + H =
      N r m * H + H * (N r m).transpose + N r m * H * (N r m).transpose := by
  have hh : H + H = 0 := by
    ext i j
    exact char2_add_self (H i j)
  calc
    _ = H + H + (N r m * H + H * (N r m).transpose + N r m * H * (N r m).transpose) := by
      simp only [Matrix.transpose_add, Matrix.transpose_one, add_mul, mul_add, one_mul, mul_one]
      abel
    _ = _ := by rw [hh, zero_add]

private theorem image_calc {r m : ℕ} (H : Matrix (Idx r m) (Idx r m) F) (h : Alt H) :
    (1 + N r m) * H * (1 + N r m).transpose + H =
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

private theorem imageBlocks {r m : ℕ} (X : Matrix (Idx r m) (Idx r m) F) :
    (∃ H, Alt H ∧ X = (1 + N r m) * H * (1 + N r m).transpose + H) ↔
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
        rw [alt_entry_symm hH (Sum.inl i) (Sum.inr (Sum.inr i)), char2_add_self, hH.2, zero_add]
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
      change Q i j + Q j i + K i j = A i j
      rw [hQ, add_assoc, char2_add_self, add_zero]
    rw [hTop]
private theorem squareZero_normalize {d : ℕ} (D : Matrix (Fin d) (Fin d) F)
    (hD : D * D = 0) :
    ∃ (m : ℕ) (P : Matrix (Fin d) (Idx D.rank m) F)
      (Q : Matrix (Idx D.rank m) (Fin d) F),
      d = D.rank + m + D.rank ∧ P * Q = 1 ∧ Q * P = 1 ∧ Q * D * P = N D.rank m := by
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
  let a : Module.Basis (Fin D.rank) F R :=
    Module.finBasisOfFinrankEq F R (D.rank_eq_finrank_range_toLin b₀ b₀).symm
  letI : Module.Finite F K := inferInstance
  letI : Module.Free F B := Module.Free.of_divisionRing F B
  let bB : Module.Basis (Fin m) F B := Module.finBasis F B
  let b : Module.Basis (Idx D.rank m) F V :=
    (((((a.map eA.symm).prod bB).map (A.prodEquivOfIsCompl B hAB)).prod
      (a.map eC.symm)).map (K.prodEquivOfIsCompl C hKC)).reindex (Equiv.sumAssoc _ _ _)
  have hA (i : Fin D.rank) : b (Sum.inl i) = (a i : V) := by
    calc
      b (Sum.inl i) = (((eA.symm (a i) : A) : K) : V) := by
        simp [b, Module.Basis.reindex_apply, Function.comp_apply]
      _ = (a i : V) := congrArg (fun x : R => (x : V)) (eA.apply_symm_apply (a i))
  have hB (i : Fin m) : b (Sum.inr (Sum.inl i)) = ((bB i : K) : V) := by
    simp [b, Module.Basis.reindex_apply, Function.comp_apply]
  have hC (i : Fin D.rank) : b (Sum.inr (Sum.inr i)) = (eC.symm (a i) : V) := by
    simp [b, Module.Basis.reindex_apply, Function.comp_apply]
  have heC (x : C) : (eC x : V) = f (x : V) := by
    change (f.quotKerEquivRange (Submodule.Quotient.mk (x : V)) : V) = f (x : V)
    exact f.quotKerEquivRange_apply_mk (x : V)
  have h₁ (i : Fin D.rank) : f (b (Sum.inl i)) = 0 := by
    rw [hA]
    exact LinearMap.mem_ker.mp (hRK (a i).property)
  have h₂ (i : Fin m) : f (b (Sum.inr (Sum.inl i))) = 0 := by
    rw [hB]
    exact LinearMap.mem_ker.mp ((bB i : K).property)
  have h₃ (i : Fin D.rank) : f (b (Sum.inr (Sum.inr i))) = b (Sum.inl i) := by
    rw [hC, hA, ← heC, LinearEquiv.apply_symm_apply]
  have hd : d = D.rank + m + D.rank := by
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
    _ = N D.rank m := by
      apply Matrix.ext
      intro i j
      rcases i with i | i | i <;> rcases j with j | j | j <;>
        simp [LinearMap.toMatrix_apply, h₁, h₂, h₃, N, Finsupp.single_apply, eq_comm]
private lemma blockAlt {r m : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (C : Matrix (Fin r) (Fin m ⊕ Fin r) F) (hA : Alt A) :
    Alt (fromBlocks A C C.transpose 0) := by
  refine ⟨?_, ?_⟩
  · rw [fromBlocks_transpose, hA.1, transpose_transpose, transpose_zero]
  · rintro (i | i)
    · exact hA.2 i
    · rfl

private lemma rankBlockBoundsAux {r m : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (C : Matrix (Fin r) (Fin m ⊕ Fin r) F) :
    let X := fromBlocks A C C.transpose 0
    2 * C.rank ≤ X.rank ∧ X.rank ≤ r + C.rank ∧ (A = 0 → X.rank = 2 * C.rank) := by
  classical
  let X : Matrix (Idx r m) (Idx r m) F := fromBlocks A C C.transpose 0
  change 2 * C.rank ≤ X.rank ∧ X.rank ≤ r + C.rank ∧ (A = 0 → X.rank = 2 * C.rank)
  let L := LinearMap.range X.mulVecLin
  let R := LinearMap.range C.transpose.mulVecLin
  let U := LinearMap.range C.mulVecLin
  have hX (x : Idx r m → F) :
      X.mulVecLin x = Sum.elim (A *ᵥ (x ∘ Sum.inl) + C *ᵥ (x ∘ Sum.inr))
        (C.transpose *ᵥ (x ∘ Sum.inl)) := by
    simp [X, Matrix.mulVecLin_apply, fromBlocks_mulVec]
  let p : L →ₗ[F] (Fin m ⊕ Fin r → F) :=
    (LinearMap.funLeft F F Sum.inr).domRestrict L
  let q : L →ₗ[F] (Fin r → F) :=
    (LinearMap.funLeft F F Sum.inl).domRestrict L
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
      map_add' := fun x y => by
        funext j
        cases j <;> simp
      map_smul' := fun s x => by
        funext j
        cases j <;> simp }
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
  have hq : Function.Injective (q.domRestrict (LinearMap.ker φ)) := by
    intro u v h
    have hu := congrArg Subtype.val (LinearMap.mem_ker.mp u.2)
    have hv := congrArg Subtype.val (LinearMap.mem_ker.mp v.2)
    change (fun j => u.1.1 (Sum.inr j)) = 0 at hu
    change (fun j => v.1.1 (Sum.inr j)) = 0 at hv
    apply Subtype.ext
    apply Subtype.ext
    funext j
    cases j with
    | inl j => exact congrFun h j
    | inr j => exact (congrFun hu j).trans ((congrFun hv j).symm)
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.mpr hφ, finrank_top] at hrn
  change C.transpose.rank + Module.finrank F (LinearMap.ker φ) = X.rank at hrn
  rw [rank_transpose] at hrn
  have hl := LinearMap.finrank_le_finrank_of_injective hι
  change C.rank ≤ Module.finrank F (LinearMap.ker φ) at hl
  have hu := LinearMap.finrank_le_finrank_of_injective hq
  rw [Module.finrank_pi, Fintype.card_fin] at hu
  refine ⟨by omega, by omega, fun hA => ?_⟩
  have hsurj : Function.Surjective ι := by
    intro y
    have hy := congrArg Subtype.val (LinearMap.mem_ker.mp y.2)
    change (fun j => y.1.1 (Sum.inr j)) = 0 at hy
    obtain ⟨x, hx⟩ := y.1.2
    have hx' := (hX x).symm.trans hx
    rw [hA, zero_mulVec, zero_add] at hx'
    refine ⟨⟨C.mulVecLin (x ∘ Sum.inr), LinearMap.mem_range_self _ _⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    funext j
    cases j with
    | inl j => exact congrFun hx' (Sum.inl j)
    | inr j => exact (congrFun hy j).symm
  have he := LinearMap.finrank_le_finrank_of_surjective hsurj
  change Module.finrank F (LinearMap.ker φ) ≤ C.rank at he
  omega

private lemma rankBlockBounds {r m : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (C : Matrix (Fin r) (Fin m ⊕ Fin r) F) :
    2 * C.rank ≤ (fromBlocks A C C.transpose 0).rank ∧
      (fromBlocks A C C.transpose 0).rank ≤ r + C.rank :=
  ⟨(rankBlockBoundsAux A C).1, (rankBlockBoundsAux A C).2.1⟩

private lemma rankBlockZero {r m : ℕ} (C : Matrix (Fin r) (Fin m ⊕ Fin r) F) :
    (fromBlocks (0 : Matrix (Fin r) (Fin r) F) C C.transpose 0).rank = 2 * C.rank :=
  (rankBlockBoundsAux 0 C).2.2 rfl

private lemma strip_attainment (r m : ℕ) :
    ∃ (B : Matrix (Fin r) (Fin m) F) (K : Matrix (Fin r) (Fin r) F),
      Alt K ∧ (Cmat B K).rank = if m = 0 ∧ Odd r then r - 1 else r := by
  classical
  let n := 2 * (r / 2)
  let w := if m = 0 then n else r
  have hn : n ≤ r := by dsimp [n]; omega
  have hw : w ≤ r := by dsimp [w]; split <;> omega
  have hw' : w = if m = 0 ∧ Odd r then r - 1 else r := by
    by_cases hm : m = 0
    · simp only [w, hm, if_true, true_and]
      simp only [Nat.odd_iff]
      split <;> dsimp [n] <;> omega
    · simp [w, hm]
  let adj (i j : ℕ) : Prop :=
    (i % 2 = 0 ∧ j = i + 1) ∨ (j % 2 = 0 ∧ i = j + 1)
  let K : Matrix (Fin r) (Fin r) F := of fun i j => if adj i.val j.val then 1 else 0
  let B : Matrix (Fin r) (Fin m) F := of fun i j => if i.val = n ∧ j.val = 0 then 1 else 0
  refine ⟨B, K, ⟨?_, ?_⟩, ?_⟩
  · ext i j
    change (if adj j.val i.val then (1 : F) else 0) = if adj i.val j.val then 1 else 0
    simp only [show adj j.val i.val ↔ adj i.val j.val from or_comm]
  · intro i
    have h : ¬adj i.val i.val := by dsimp [adj]; omega
    change (if adj i.val i.val then (1 : F) else 0) = 0
    rw [if_neg h]
  rw [← hw']
  let f : Fin w → Fin r := Fin.castLE hw
  let partner (j : ℕ) := if j % 2 = 0 then j + 1 else j - 1
  have hpartner (j : Fin w) (hj : j.val < n) : partner j.val < r := by
    dsimp [partner]
    have hn' : n % 2 = 0 := by dsimp [n]; omega
    split <;> omega
  have htail (j : Fin w) (hj : ¬ j.val < n) : 0 < m ∧ j.val = n := by
    have hlt := j.isLt
    have hle := lt_of_lt_of_le hlt hw
    have hm : m ≠ 0 := by
      intro hm
      exact hj (by simpa [w, hm] using hlt)
    dsimp [n] at hj ⊢
    omega
  let g (j : Fin w) : Fin m ⊕ Fin r :=
    if hj : j.val < n then Sum.inr ⟨partner j.val, hpartner j hj⟩
    else Sum.inl ⟨0, (htail j hj).1⟩
  have hs : (Cmat B K).submatrix f g = 1 := by
    ext i j
    rw [Matrix.one_apply, Matrix.submatrix_apply]
    by_cases hj : j.val < n
    · have hh : adj i.val (partner j.val) ↔ i = j := by
        rw [← Fin.val_inj]
        dsimp [partner, adj]
        split <;> omega
      simp only [g, dif_pos hj]
      change (if adj i.val (partner j.val) then (1 : F) else 0) = if i = j then 1 else 0
      simp only [hh]
    · have hh : i.val = n ↔ i = j := by
        rw [← Fin.val_inj, (htail j hj).2]
      simp only [g, dif_neg hj]
      change (if i.val = n ∧ (0 : ℕ) = 0 then (1 : F) else 0) = if i = j then 1 else 0
      simp only [eq_self, and_true, hh]
  have hl := (Cmat B K).rank_submatrix_le f g
  rw [hs, rank_one, Fintype.card_fin] at hl
  refine le_antisymm ?_ hl
  by_cases hm : m = 0
  · let b : Fin n ↪ Fin r := Fin.castLEEmb hn
    let s : Finset (Fin r) := Finset.univ.map b
    have hs' : s.card = w := by simp [s, w, hm]
    rw [← hs']
    apply rank_le_card_of_support_subset
    intro i hi
    have hi' : i.val < n := by
      by_contra h
      apply hi
      funext j
      rcases j with j | j
      · have hj : j.val < m := j.isLt
        omega
      · have hnot : ¬adj i.val j.val := by
          have hiR := i.isLt
          have hjR := j.isLt
          dsimp only [adj, n] at h ⊢
          omega
        change (if adj i.val j.val then (1 : F) else 0) = 0
        rw [if_neg hnot]
    exact Finset.mem_map.mpr ⟨⟨i.val, hi'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · simpa [w, hm] using (Cmat B K).rank_le_card_height

-- Adapted from L_meta_25745.lean at 0b87cb0f3d060d4c5d18a2ed94686ba356a8aabb.
private lemma rankFOneOfNonzero {a : F} (h : a ≠ 0) : a = 1 := by
  revert a h
  decide

private lemma rankFEqOfAddEqZero {a b : F} (h : a + b = 0) : a = b := by
  revert a b h
  decide

private def rankRad {ι : Type*}
    (B : (ι → F) →ₗ[F] (ι → F) →ₗ[F] F) (U : Submodule F (ι → F)) : Submodule F (ι → F) :=
  { carrier := {u | u ∈ U ∧ ∀ v ∈ U, B u v = 0}, add_mem' := by
      intro a b ha hb
      refine ⟨U.add_mem ha.1 hb.1, fun v hv => ?_⟩
      rw [map_add, LinearMap.add_apply, ha.2 v hv, hb.2 v hv, add_zero]
    zero_mem' := ⟨U.zero_mem, fun _ _ => by simp⟩
    smul_mem' := by
      intro s a ha
      refine ⟨U.smul_mem s ha.1, fun v hv => ?_⟩
      rw [map_smul, LinearMap.smul_apply, ha.2 v hv, smul_zero] }

private lemma rankEvenCodimRad {ι : Type*} [Fintype ι]
    (B : (ι → F) →ₗ[F] (ι → F) →ₗ[F] F)
    (halt : ∀ v, B v v = 0) (hsymm : ∀ u v, B u v = B v u)
    (W : Submodule F (ι → F)) :
    Even (Module.finrank F W - Module.finrank F (rankRad B W)) := by
  classical
  let radOf := rankRad B
  have hstrong : ∀ k : ℕ, ∀ U : Submodule F (ι → F),
      Module.finrank F U = k →
      Even (Module.finrank F U - Module.finrank F (radOf U)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro U hk
      by_cases htriv : ∀ u ∈ U, ∀ v ∈ U, B u v = 0
      · have heq : radOf U = U := by
          ext u
          exact ⟨fun h => h.1, fun hu => ⟨hu, htriv u hu⟩⟩
        rw [heq, Nat.sub_self]
        exact ⟨0, rfl⟩
      · push Not at htriv
        obtain ⟨u, huU, v, hvU, huv_ne⟩ := htriv
        have huv : B u v = 1 := rankFOneOfNonzero huv_ne
        have hvu : B v u = 1 := by rw [hsymm, huv]
        let φ : U →ₗ[F] (F × F) :=
          { toFun := fun w => (B u w.1, B v w.1)
            map_add' := fun a b => by
              apply Prod.ext <;> simp only [Submodule.coe_add, map_add, Prod.fst_add, Prod.snd_add]
            map_smul' := fun s a => by
              apply Prod.ext <;> simp only [SetLike.val_smul, map_smul, Prod.smul_fst,
                Prod.smul_snd, RingHom.id_apply] }
        have hφ_surj : Function.Surjective φ := by
          intro ⟨a, b⟩
          refine ⟨a • ⟨v, hvU⟩ + b • ⟨u, huU⟩, ?_⟩
          apply Prod.ext
          · change B u (a • v + b • u) = a
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, huv, halt u,
              mul_one, mul_zero, add_zero]
          · change B v (a • v + b • u) = b
            rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, hvu, halt v,
              mul_zero, mul_one, zero_add]
        have hrange_φ : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
        have hrank_φ : Module.finrank F (LinearMap.range φ) = 2 := by
          rw [hrange_φ, finrank_top, Module.finrank_prod, Module.finrank_self]
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        rw [hrank_φ] at hrn
        let U' : Submodule F (ι → F) :=
          { carrier := {w | w ∈ U ∧ B u w = 0 ∧ B v w = 0}, add_mem' := by
              intro a b ha hb
              refine ⟨U.add_mem ha.1 hb.1, ?_, ?_⟩
              · rw [map_add, ha.2.1, hb.2.1, add_zero]
              · rw [map_add, ha.2.2, hb.2.2, add_zero]
            zero_mem' := ⟨U.zero_mem, by simp, by simp⟩
            smul_mem' := by
              intro s a ha
              refine ⟨U.smul_mem s ha.1, ?_, ?_⟩
              · rw [map_smul, ha.2.1, smul_zero]
              · rw [map_smul, ha.2.2, smul_zero] }
        let eker : LinearMap.ker φ ≃ₗ[F] U' :=
          { toFun := fun w => ⟨w.1.1, w.1.2, by
              have hw : φ w.1 = 0 := w.2
              exact ⟨congrArg Prod.fst hw, congrArg Prod.snd hw⟩⟩
            invFun := fun w => ⟨⟨w.1, w.2.1⟩, by
              change φ ⟨w.1, w.2.1⟩ = 0
              exact Prod.ext w.2.2.1 w.2.2.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        have hdimU' : Module.finrank F U' = Module.finrank F (LinearMap.ker φ) :=
          eker.finrank_eq.symm
        have hrad_eq : radOf U' = radOf U := by
          ext x
          constructor
          · intro hx
            refine ⟨hx.1.1, fun w hw => ?_⟩
            let w' := w + B u w • v + B v w • u
            have hw'U : w' ∈ U :=
              U.add_mem (U.add_mem hw (U.smul_mem _ hvU)) (U.smul_mem _ huU)
            have hBuw' : B u w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                huv, halt u, mul_one, mul_zero, add_zero]
              exact char2_add_self _
            have hBvw' : B v w' = 0 := by
              dsimp only [w']
              rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
                hvu, halt v, mul_one, mul_zero, add_zero]
              exact char2_add_self _
            have hBxw' : B x w' = 0 := hx.2 w' ⟨hw'U, hBuw', hBvw'⟩
            have hBxu : B x u = 0 := by rw [hsymm]; exact hx.1.2.1
            have hBxv : B x v = 0 := by rw [hsymm]; exact hx.1.2.2
            dsimp only [w'] at hBxw'
            rw [map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
              hBxv, hBxu, mul_zero, mul_zero, add_zero, add_zero] at hBxw'
            exact hBxw'
          · intro hx
            refine ⟨⟨hx.1, ?_, ?_⟩, fun w hw => hx.2 w hw.1⟩
            · rw [hsymm]; exact hx.2 u huU
            · rw [hsymm]; exact hx.2 v hvU
        have hle_rad : Module.finrank F (radOf U') ≤ Module.finrank F U' :=
          Submodule.finrank_mono (fun _ hx => hx.1)
        have hU'_lt : Module.finrank F U' < k := by omega
        have hev' := ih (Module.finrank F U') hU'_lt U' rfl
        rw [hrad_eq] at hev' hle_rad
        rcases hev' with ⟨t, ht⟩
        refine ⟨t + 1, ?_⟩
        omega
  exact hstrong (Module.finrank F W) W rfl

private lemma rankEvenRangeAlt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → F) →ₗ[F] (ι → F)) (halt : ∀ v, dotProduct v (A v) = 0) :
    Even (Module.finrank F (LinearMap.range A)) := by
  have hsymm : ∀ u v, dotProduct u (A v) = dotProduct v (A u) := by
    intro u v
    have h := halt (u + v)
    rw [map_add, add_dotProduct, dotProduct_add, dotProduct_add, halt u, halt v,
      zero_add, add_zero] at h
    exact rankFEqOfAddEqZero h
  let B : (ι → F) →ₗ[F] (ι → F) →ₗ[F] F :=
    { toFun := fun u =>
        { toFun := fun v => dotProduct u (A v)
          map_add' := fun v₁ v₂ => by rw [map_add, dotProduct_add]
          map_smul' := fun s v => by rw [map_smul, dotProduct_smul, RingHom.id_apply] }
      map_add' := fun u₁ u₂ => by
        apply LinearMap.ext; intro v; exact add_dotProduct u₁ u₂ (A v)
      map_smul' := fun s u => by
        apply LinearMap.ext; intro v; exact smul_dotProduct s u (A v) }
  have hrad : rankRad B ⊤ = LinearMap.ker A := by
    ext u
    change (u ∈ (⊤ : Submodule F (ι → F)) ∧
      ∀ v ∈ (⊤ : Submodule F (ι → F)), dotProduct u (A v) = 0) ↔ A u = 0
    constructor
    · intro h
      funext a
      have ha := h.2 (Pi.single a 1) Submodule.mem_top
      rw [hsymm, single_dotProduct, one_mul] at ha
      exact ha
    · intro h
      refine ⟨Submodule.mem_top, fun v _ => ?_⟩
      rw [hsymm, h, dotProduct_zero]
  have hev := rankEvenCodimRad B halt hsymm ⊤
  rw [hrad, finrank_top] at hev
  have hrn := LinearMap.finrank_range_add_finrank_ker A
  have hsub : Module.finrank F (ι → F) - Module.finrank F (LinearMap.ker A) =
      Module.finrank F (LinearMap.range A) := by omega
  rwa [hsub] at hev

private lemma altRankEven {ι : Type*} [Fintype ι] {H : Matrix ι ι F} (hH : Alt H) :
    Even H.rank := by
  classical
  change Even (Module.finrank F (LinearMap.range H.mulVecLin))
  apply rankEvenRangeAlt H.mulVecLin
  intro x
  simpa only [Matrix.toBilin'_apply', Matrix.mulVecLin_apply] using alt_bilin_zero hH x

private lemma altRankTwo {ι : Type*} [Fintype ι] {K : Matrix ι ι F}
    (hK : Alt K) (hne : K ≠ 0) : 2 ≤ K.rank := by
  classical
  have hex : ∃ i j, K i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    ext i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hex
  have hij' : K i j = 1 := rankFOneOfNonzero hij
  have hji' : K j i = 1 :=
    (congrArg (fun M : Matrix ι ι F => M i j) hK.1).trans hij'
  let e (t : Fin 2) : ι := if t = 0 then i else j
  have hdet : (K.submatrix e e).det ≠ 0 := by
    rw [det_fin_two]
    simp [e, hK.2, hij', hji', show (1 : Fin 2) ≠ 0 by decide]
  have hr := K.rank_submatrix_le e e
  rwa [rank_of_det_ne_zero hdet, Fintype.card_fin] at hr

private lemma altRankLt {r : ℕ} {K : Matrix (Fin r) (Fin r) F} (hK : Alt K) (hr : Odd r) :
    K.rank < r := by
  have hle : K.rank ≤ r := by simpa using K.rank_le_card_height
  apply lt_of_le_of_ne hle
  intro he
  have hv := altRankEven hK
  rw [he, Nat.even_iff] at hv
  have ho := Nat.odd_iff.mp hr
  omega

private abbrev PairCoord (r : ℕ) := {s : Finset (Fin r) // s.card = 2}
private abbrev NarrowCoord (r m : ℕ) := PairCoord r ⊕ (Fin r × Fin m)
private abbrev WideCoord (r m : ℕ) := NarrowCoord r m ⊕ PairCoord r

private lemma card_pairCoord (r : ℕ) : Fintype.card (PairCoord r) = r.choose 2 := by
  rw [Fintype.card_of_subtype (p := fun s : Finset (Fin r) => s.card = 2)
    ((Finset.univ : Finset (Fin r)).powersetCard 2)
    (fun s => by simp [Finset.mem_powersetCard])]
  simp [Finset.card_powersetCard]

private def coordPair {r : ℕ} (i j : Fin r) (h : i ≠ j) : PairCoord r :=
  ⟨{i, j}, Finset.card_pair h⟩

private def pairMat {r : ℕ} (a : PairCoord r → F) : Matrix (Fin r) (Fin r) F :=
  fun i j => if h : i ≠ j then a (coordPair i j h) else 0

private lemma pairMat_alt {r : ℕ} (a : PairCoord r → F) : Alt (pairMat a) := by
  constructor
  · ext i j
    change pairMat a j i = pairMat a i j
    by_cases h : i = j
    · subst j; rfl
    · have he : coordPair j i (Ne.symm h) = coordPair i j h :=
        Subtype.ext (Finset.pair_comm _ _)
      simp only [pairMat, dif_pos h, dif_pos (Ne.symm h), he]
  · intro i
    simp [pairMat]

private lemma pairMat_inj {r : ℕ} : Function.Injective (@pairMat r) := by
  intro a b h
  funext q
  obtain ⟨i, j, hij, hq⟩ := Finset.card_eq_two.1 q.2
  have he : q = coordPair i j hij := Subtype.ext hq
  have hab := congrFun (congrFun h i) j
  simpa [he, pairMat, hij] using hab

private lemma pairMat_surj {r : ℕ} {A : Matrix (Fin r) (Fin r) F} (hA : Alt A) :
    ∃ a, pairMat a = A := by
  classical
  have hrep (q : PairCoord r) : ∃ x y, x ≠ y ∧ q.1 = {x, y} := Finset.card_eq_two.1 q.2
  choose x y hxy hq using hrep
  refine ⟨fun q => A (x q) (y q), ?_⟩
  ext i j
  change pairMat (fun q => A (x q) (y q)) i j = A i j
  by_cases hij : i = j
  · subst j
    simpa [pairMat] using (hA.2 i).symm
  · let q := coordPair i j hij
    rw [pairMat, dif_pos hij]
    change A (x q) (y q) = A i j
    have hAq : ({i, j} : Finset (Fin r)) = {x q, y q} := hq q
    have hi : i = x q ∨ i = y q := by
      have hm : i ∈ ({x q, y q} : Finset (Fin r)) := by rw [← hAq]; simp
      simpa using hm
    have hj : j = x q ∨ j = y q := by
      have hm : j ∈ ({x q, y q} : Finset (Fin r)) := by rw [← hAq]; simp
      simpa using hm
    rcases hi with hx | hx <;> rcases hj with hy | hy
    · exact (hij (hx.trans hy.symm)).elim
    · rw [← hx, ← hy]
    · rw [← hy, ← hx]; exact alt_entry_symm hA _ _
    · exact (hij (hx.trans hy.symm)).elim

private def wideMap (r m : ℕ) : (WideCoord r m → F) →ₗ[F] Matrix (Idx r m) (Idx r m) F where
  toFun a :=
    let A := pairMat (fun q => a (Sum.inl (Sum.inl q)))
    let B : Matrix (Fin r) (Fin m) F := fun i j => a (Sum.inl (Sum.inr (i,j)))
    let K := pairMat (fun q => a (Sum.inr q))
    Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0
  map_add' a b := by
    ext (i | (i | i)) (j | (j | j)) <;>
      simp [Matrix.fromBlocks, Cmat, pairMat, Matrix.transpose_apply] <;>
      split <;> rfl
  map_smul' c a := by
    ext (i | (i | i)) (j | (j | j)) <;>
      simp [Matrix.fromBlocks, Cmat, pairMat, Matrix.transpose_apply]

private lemma wideMap_inj (r m : ℕ) : Function.Injective (wideMap r m) := by
  intro a b h
  have hA : pairMat (fun q => a (Sum.inl (Sum.inl q))) =
      pairMat (fun q => b (Sum.inl (Sum.inl q))) := by
    ext i j
    exact congrFun (congrFun h (Sum.inl i)) (Sum.inl j)
  have hK : pairMat (fun q => a (Sum.inr q)) = pairMat (fun q => b (Sum.inr q)) := by
    ext i j
    exact congrFun (congrFun h (Sum.inl i)) (Sum.inr (Sum.inr j))
  funext x
  rcases x with (q | ⟨i,j⟩) | q
  · exact congrFun (pairMat_inj hA) q
  · exact congrFun (congrFun h (Sum.inl i)) (Sum.inr (Sum.inl j))
  · exact congrFun (pairMat_inj hK) q

private def extendZero (r m : ℕ) : (NarrowCoord r m → F) →ₗ[F] (WideCoord r m → F) where
  toFun a := Sum.elim a 0
  map_add' a b := by funext x; cases x <;> simp
  map_smul' c a := by funext x; cases x <;> simp

private def narrowMap (r m : ℕ) : (NarrowCoord r m → F) →ₗ[F] Matrix (Idx r m) (Idx r m) F :=
  (wideMap r m).comp (extendZero r m)

private lemma narrowMap_inj (r m : ℕ) : Function.Injective (narrowMap r m) := by
  intro a b h
  have he := wideMap_inj r m h
  funext x
  exact congrFun he (Sum.inl x)

private lemma pairMat_zero (r : ℕ) : pairMat (0 : PairCoord r → F) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [pairMat, h]

private lemma wide_range {r m : ℕ} (X : Matrix (Idx r m) (Idx r m) F) :
    X ∈ LinearMap.range (wideMap r m) ↔
      ∃ (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin m) F)
        (K : Matrix (Fin r) (Fin r) F), Alt A ∧ Alt K ∧
          X = Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, _, _, pairMat_alt _, pairMat_alt _, rfl⟩
  · rintro ⟨A, B, K, hA, hK, rfl⟩
    obtain ⟨a, rfl⟩ := pairMat_surj hA
    obtain ⟨k, rfl⟩ := pairMat_surj hK
    exact ⟨Sum.elim (Sum.elim a (fun p : Fin r × Fin m => B p.1 p.2)) k, rfl⟩

private lemma narrow_apply {r m : ℕ} (a : NarrowCoord r m → F) :
    narrowMap r m a =
      let A := pairMat (fun q => a (Sum.inl q))
      let B : Matrix (Fin r) (Fin m) F := fun i j => a (Sum.inr (i,j))
      Matrix.fromBlocks A (Cmat B 0) (Cmat B 0).transpose 0 := by
  let A := pairMat (fun q => a (Sum.inl q))
  let B : Matrix (Fin r) (Fin m) F := fun i j => a (Sum.inr (i,j))
  let K := pairMat (0 : PairCoord r → F)
  change Matrix.fromBlocks A (Cmat B K) (Cmat B K).transpose 0 =
    Matrix.fromBlocks A (Cmat B 0) (Cmat B 0).transpose 0
  simp only [K, pairMat_zero]

private lemma narrow_range {r m : ℕ} (X : Matrix (Idx r m) (Idx r m) F) :
    X ∈ LinearMap.range (narrowMap r m) ↔
      ∃ (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin m) F), Alt A ∧
        X = Matrix.fromBlocks A (Cmat B 0) (Cmat B 0).transpose 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, (fun i j => a (Sum.inr (i,j))), pairMat_alt (fun q => a (Sum.inl q)), narrow_apply a⟩
  · rintro ⟨A,B,hA,rfl⟩
    obtain ⟨a,rfl⟩ := pairMat_surj hA
    exact ⟨Sum.elim a (fun p : Fin r × Fin m => B p.1 p.2), narrow_apply _⟩

private lemma narrow_single_rank {r m : ℕ} (x : NarrowCoord r m) :
    (narrowMap r m (Pi.single x 1)).rank ≤ 2 := by
  classical
  let X := narrowMap r m (Pi.single x 1)
  cases x with
  | inl q =>
    let s := q.1.map (Function.Embedding.inl : Fin r ↪ Idx r m)
    have hs : s.card = 2 := by simp [s, q.2]
    suffices h : X.rank ≤ s.card by simpa only [hs] using h
    apply Matrix.rank_le_card_of_support_subset X s
    rw [Function.support_subset_iff']
    intro i hi
    funext j
    change X i j = 0
    cases i with
    | inl i =>
      have hni : i ∉ q.1 := fun h => hi (Finset.mem_map.2 ⟨i, h, rfl⟩)
      cases j with
      | inl j =>
        change pairMat (fun p => (Pi.single (Sum.inl q : NarrowCoord r m) 1 :
          NarrowCoord r m → F) (Sum.inl p)) i j = 0
        by_cases hij : i = j
        · simp [pairMat, hij]
        · have hpq : coordPair i j hij ≠ q := by
            intro hp
            apply hni
            rw [← hp]
            simp [coordPair]
          simp [pairMat, hij, Pi.single_apply, hpq, Ne.symm hpq]
      | inr j =>
        cases j <;> simp [X, narrowMap, wideMap, extendZero, Matrix.fromBlocks, Cmat,
          Pi.single_apply, pairMat]
    | inr i =>
      rcases i with i | i <;> rcases j with j | (j | j) <;>
        simp [X, narrowMap, wideMap, extendZero, Matrix.fromBlocks, Cmat, Pi.single_apply, pairMat]
  | inr p =>
    rcases p with ⟨u,v⟩
    let s : Finset (Idx r m) := {Sum.inl u, Sum.inr (Sum.inl v)}
    have hs : s.card = 2 := Finset.card_pair (by simp)
    suffices h : X.rank ≤ s.card by simpa only [hs] using h
    apply Matrix.rank_le_card_of_support_subset X s
    rw [Function.support_subset_iff']
    intro i hi
    funext j
    change X i j = 0
    rcases i with i | (i | i)
    · have hn : i ≠ u := by
        intro he
        subst i
        exact hi (by simp [s])
      rcases j with j | (j | j) <;>
        simp [X, narrowMap, wideMap, extendZero, Matrix.fromBlocks, Cmat, Pi.single_apply,
          pairMat, hn, Ne.symm hn, Prod.mk.injEq]
    · have hn : i ≠ v := by
        intro he
        subst i
        exact hi (by simp [s])
      rcases j with j | (j | j) <;>
        simp [X, narrowMap, wideMap, extendZero, Matrix.fromBlocks, Cmat, Pi.single_apply,
          pairMat, hn, Ne.symm hn, Prod.mk.injEq]
    · rcases j with j | (j | j) <;>
        simp [X, narrowMap, wideMap, extendZero, Matrix.fromBlocks, Cmat, Pi.single_apply, pairMat]

private lemma wide_dim (r m : ℕ) :
    Module.finrank F (LinearMap.range (wideMap r m)) = r.choose 2 + r*m + r.choose 2 := by
  rw [LinearMap.finrank_range_of_inj (wideMap_inj r m), Module.finrank_pi]
  simp [WideCoord, NarrowCoord, card_pairCoord]

private lemma narrow_dim (r m : ℕ) :
    Module.finrank F (LinearMap.range (narrowMap r m)) = r.choose 2 + r*m := by
  rw [LinearMap.finrank_range_of_inj (narrowMap_inj r m), Module.finrank_pi]
  simp [NarrowCoord, card_pairCoord]

private lemma narrow_span {r m : ℕ} (S : Set (Matrix (Idx r m) (Idx r m) F))
    (hrange : ∀ X, X ∈ S ↔ X ∈ LinearMap.range (wideMap r m))
    (hsmall : ∀ X ∈ S, X.rank ≤ 2 → X ∈ LinearMap.range (narrowMap r m)) :
    Submodule.span F {X | X ∈ S ∧ X.rank ≤ 2} = LinearMap.range (narrowMap r m) := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.2 (fun X h => hsmall X h.1 h.2)
  · rintro X ⟨a, rfl⟩
    rw [← Finset.univ_sum_single a, map_sum]
    refine Submodule.sum_mem _ fun x _ => ?_
    have he : Pi.single x (a x) = a x • (Pi.single x 1 : NarrowCoord r m → F) := by
      ext i
      by_cases h : i = x <;> simp [Pi.single_apply, h]
    rw [he, map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨?_, narrow_single_rank x⟩)
    exact (hrange _).2 ⟨extendZero r m (Pi.single x 1), rfl⟩

private def imageSet {ι : Type*} [Fintype ι] (U : Matrix ι ι F) : Set (Matrix ι ι F) :=
  {X | ∃ H, Alt H ∧ X = U * H * U.transpose + H}

private def smallSet {ι : Type*} [Fintype ι] (S : Set (Matrix ι ι F)) : Set (Matrix ι ι F) :=
  {X | X ∈ S ∧ X.rank ≤ 2}

private lemma strip_rank_empty {r : ℕ} (B : Matrix (Fin r) (Fin 0) F)
    (K : Matrix (Fin r) (Fin r) F) : (Cmat B K).rank = K.rank := by
  let e : Fin 0 ⊕ Fin r ≃ Fin r := Equiv.emptySum _ _
  have he : Cmat B K = K.submatrix (Equiv.refl (Fin r)) e := by
    ext i (j | j)
    · exact Fin.elim0 j
    · rfl
  rw [he, Matrix.rank_submatrix]

private lemma canonical {r m : ℕ} :
    let S := imageSet (1 + N r m)
    let w := if m = 0 ∧ Odd r then r-1 else r
    Module.finrank F (Submodule.span F S) = r.choose 2 + r*m + r.choose 2 ∧
    Module.finrank F (Submodule.span F (smallSet S)) = r.choose 2 + r*m ∧
    (∀ X ∈ S, X.rank ≤ 2*w) ∧ ∃ X ∈ S, X.rank = 2*w := by
  intro S w
  have hRange (X) : X ∈ S ↔ X ∈ LinearMap.range (wideMap r m) :=
    (imageBlocks X).trans (wide_range X).symm
  have hSp : Submodule.span F S = LinearMap.range (wideMap r m) := by
    have hset : S = (LinearMap.range (wideMap r m) : Set _) := Set.ext hRange
    rw [hset, Submodule.span_eq]
  have hsmall (X) (hX : X ∈ S) (hq : X.rank ≤ 2) :
      X ∈ LinearMap.range (narrowMap r m) := by
    obtain ⟨A,B,K,hA,hK,rfl⟩ := (imageBlocks X).1 hX
    have hz : K = 0 := by
      by_contra hk
      have h₂ := altRankTwo hK hk
      have hStrip := (Cmat B K).rank_submatrix_le id Sum.inr
      change K.rank ≤ (Cmat B K).rank at hStrip
      have hBlock := (rankBlockBounds A (Cmat B K)).1
      omega
    subst K
    exact (narrow_range _).2 ⟨A,B,hA,rfl⟩
  have hN : Submodule.span F (smallSet S) = LinearMap.range (narrowMap r m) :=
    narrow_span S hRange hsmall
  rw [hSp, hN, wide_dim, narrow_dim]
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro X hX
    obtain ⟨A,B,K,hA,hK,rfl⟩ := (imageBlocks X).1 hX
    have hblock := (rankBlockBounds A (Cmat B K)).2
    dsimp only [w]
    split
    · rename_i he
      obtain ⟨hm, ho⟩ := he
      subst m
      rw [strip_rank_empty] at hblock
      have hlt := altRankLt hK ho
      have hev := altRankEven (blockAlt A (Cmat B K) hA)
      rw [Nat.even_iff] at hev
      omega
    · have hwidth : (Cmat B K).rank ≤ r := by simpa using (Cmat B K).rank_le_card_height
      omega
  · obtain ⟨B,K,hK,hC⟩ := strip_attainment r m
    let A : Matrix (Fin r) (Fin r) F := 0
    let C := Cmat B K
    have hAw : Alt A := ⟨Matrix.transpose_zero, fun _ => rfl⟩
    refine ⟨Matrix.fromBlocks A C C.transpose 0,
      (imageBlocks _).2 ⟨A,B,K,hAw,hK,rfl⟩, ?_⟩
    rw [rankBlockZero C]
    exact congrArg (2 * ·) hC

private lemma image_transport_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι ι F)
    (P : Matrix ι κ F) (Q : Matrix κ ι F) (hp : P * Q = 1) (hq : Q * P = 1)
    (H : Matrix ι ι F) :
    matrixCongr Q P hp hq (U*H*U.transpose + H) =
      (Q*U*P) * matrixCongr Q P hp hq H * (Q*U*P).transpose + matrixCongr Q P hp hq H := by
  have ht : Q.transpose * P.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using congrArg Matrix.transpose hp
  change Q * (U*H*U.transpose + H) * Q.transpose =
    (Q*U*P) * (Q*H*Q.transpose) * (Q*U*P).transpose + Q*H*Q.transpose
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
  · rintro ⟨J,hJ,rfl⟩
    let H := e.symm J
    have he : e H = J := e.apply_symm_apply J
    refine ⟨U*H*U.transpose + H, ⟨H, congr_alt P hJ, rfl⟩, ?_⟩
    rw [image_transport_eq U P Q hp hq H, he]

private lemma rank_image_set {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (U : Matrix ι ι F)
    (P : Matrix ι κ F) (Q : Matrix κ ι F) (hp : P * Q = 1) (hq : Q * P = 1) :
    matrixCongr Q P hp hq '' smallSet (imageSet U) = smallSet (imageSet (Q * U * P)) := by
  let e := matrixCongr Q P hp hq
  have hs := image_transport U P Q hp hq
  ext X
  change X ∈ e '' smallSet (imageSet U) ↔ X ∈ smallSet (imageSet (Q * U * P))
  constructor
  · rintro ⟨Y, ⟨hY, hρ⟩, rfl⟩
    exact ⟨hs ▸ ⟨Y,hY,rfl⟩, (congr_rank Q P hp Y).symm ▸ hρ⟩
  · rintro ⟨hX, hρ⟩
    obtain ⟨Y,hY,rfl⟩ : X ∈ e '' imageSet U := hs.symm ▸ hX
    exact ⟨Y,⟨hY,(congr_rank Q P hp Y) ▸ hρ⟩,rfl⟩

private lemma span_dim_image {V W : Type*} [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] (e : V ≃ₗ[F] W) (S : Set V) :
    Module.finrank F (Submodule.span F S) = Module.finrank F (Submodule.span F (e '' S)) := by
  change Module.finrank F (Submodule.span F S) =
    Module.finrank F (Submodule.span F (e.toLinearMap '' S))
  rw [← Submodule.map_span e.toLinearMap S]
  exact (Submodule.equivMapOfInjective e.toLinearMap e.injective _).finrank_eq

private lemma rank_dim_arith {d r m : ℕ} (hd : d = r+m+r) :
    r.choose 2 + r*m + r.choose 2 = r*(d-r-1) := by
  have he := Nat.even_iff.mp (Nat.even_mul_pred_self r)
  rw [Nat.choose_two_right]
  calc
    _ = r*(r-1)+r*m := by omega
    _ = r*((r-1)+m) := by rw [Nat.mul_add]
    _ = _ := by
      cases r with
      | zero => simp
      | succ r => congr 1 <;> omega

private lemma invol_sub_square {d : ℕ} (U : Matrix (Fin d) (Fin d) F) (hU : U * U = 1) :
    (U - 1) * (U - 1) = 0 := by
  have hn : -(1 : Matrix (Fin d) (Fin d) F) = 1 := by
    ext i j
    change -((1 : Matrix (Fin d) (Fin d) F) i j) = _
    have h := char2_add_self ((1 : Matrix (Fin d) (Fin d) F) i j)
    exact add_eq_zero_iff_neg_eq.1 h
  rw [sub_eq_add_neg U, hn, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hU, add_comm (1 : Matrix (Fin d) (Fin d) F) U]
  ext i j
  exact char2_add_self _

end PEqualNP.Outside.L_lib_923

open PEqualNP.Outside.L_lib_923

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_lib_923 :
    let F := ZMod 2
    ∀ (d : ℕ) (U : Matrix (Fin d) (Fin d) F), U*U = 1 →
      let Mat := Matrix (Fin d) (Fin d) F
      let alt := fun (H : Mat) => H.transpose = H ∧ ∀ i, H i i = 0
      let r := (U-1).rank
      let S : Set Mat := {X | ∃ H : Mat, alt H ∧ X = U*H*U.transpose + H}
      let W := Submodule.span F S
      let L := Submodule.span F {X : Mat | X ∈ S ∧ X.rank ≤ 2}
      let w := if d = 2*r ∧ r % 2 = 1 then r-1 else r
      Module.finrank F W = r*(d-r-1) ∧
        Module.finrank F L + Nat.choose r 2 = Module.finrank F W ∧
        (∀ X ∈ S, X.rank ≤ 2*w) ∧ (∃ X ∈ S, X.rank = 2*w) := by
  intro F d U hU Mat alt r S W L w
  obtain ⟨m,P,Q,hd,hPQ,hQP,hN⟩ := squareZero_normalize (U - 1) (invol_sub_square U hU)
  have hV : Q * U * P = 1 + N r m := by
    have hU' : U = (U - 1) + 1 := (sub_add_cancel U 1).symm
    calc
      Q * U * P = Q * ((U-1)+1) * P := congrArg (fun X : Mat => Q * X * P) hU'
      _ = 1 + N r m := by rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hN, hQP, add_comm]
  have hw : w = if m = 0 ∧ Odd r then r-1 else r := by
    have hd' : d = r+m+r := hd
    have hh : d = 2*r ↔ m = 0 := by omega
    change (if d = 2*r ∧ r % 2 = 1 then r-1 else r) = _
    have hh' : (d = 2*r ∧ r % 2 = 1) ↔ (m = 0 ∧ Odd r) := and_congr hh Nat.odd_iff.symm
    by_cases h : d = 2*r ∧ r % 2 = 1
    · simp [h, hh'.1 h]
    · have h' : ¬ (m = 0 ∧ Odd r) := fun hn => h (hh'.2 hn)
      simp [h, h']
  let e := matrixCongr Q P hPQ hQP
  have hS : e '' S = imageSet (1 + N r m) := (image_transport U P Q hPQ hQP).trans (congrArg imageSet hV)
  have hL : e '' smallSet S = smallSet (imageSet (1 + N r m)) :=
    (rank_image_set U P Q hPQ hQP).trans (congrArg (fun V => smallSet (imageSet V)) hV)
  obtain ⟨hW', hL', hu, he⟩ := canonical (r := r) (m := m)
  have hW : Module.finrank F W = r.choose 2 + r*m + r.choose 2 := by
    change Module.finrank F (Submodule.span F S) = _
    rw [span_dim_image e S, hS]
    exact hW'
  have hLdim : Module.finrank F L = r.choose 2 + r*m := by
    change Module.finrank F (Submodule.span F (smallSet S)) = _
    rw [span_dim_image e (smallSet S), hL]
    exact hL'
  refine ⟨hW.trans (rank_dim_arith hd), by rw [hLdim,hW], ?_, ?_⟩
  · intro X hX
    have hX' : e X ∈ imageSet (1 + N r m) := hS ▸ ⟨X,hX,rfl⟩
    rw [← congr_rank Q P hPQ X, hw]
    exact hu _ hX'
  · obtain ⟨Y,hY,hRank⟩ := he
    obtain ⟨X,hX,rfl⟩ : Y ∈ e '' S := hS.symm ▸ hY
    exact ⟨X,hX,by rw [← congr_rank Q P hPQ X, hw]; exact hRank⟩
