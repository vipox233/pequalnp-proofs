import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Matrix

namespace PEqualNP.Outside.L_lib_986_aux

abbrev F := ZMod 2

variable {n : ℕ}

abbrev V (n : ℕ) := Fin n → F
abbrev JV (n : ℕ) := Fin n ⊕ Fin n → F
abbrev Big (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) F

def Alt (A : Mat n) : Prop := A.transpose = A ∧ ∀ i, A i i = 0

def Wsp (P : Submodule F (Mat n)) : Submodule F (Big n) :=
  Submodule.span F {X : Big n | ∃ A K : Mat n, Alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : Mat n)}

def Hsp (P : Submodule F (Mat n)) : Submodule F (V n) :=
  Submodule.span F {v : Fin n → F | ∃ K ∈ P, ∃ j : Fin n, v = fun i => K i j}

def Gset (E : Submodule F (JV n)) : Set (Big n) :=
  {X : Big n | (∀ j, (fun i => X i j) ∈ E) ∧ (∀ i, (fun j => X i j) ∈ E)}

def freeSp (E : Submodule F (JV n)) : Submodule F (Big n) := Submodule.span F (Gset E)

theorem two_zero (a : F) : a + a = 0 := CharTwo.add_self_eq_zero a

theorem se_dot (a b c d : V n) :
    (Sum.elim a b : JV n) ⬝ᵥ (Sum.elim c d : JV n) = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem fb_mulVec (A B C D : Mat n) (c d : V n) :
    Matrix.fromBlocks A B C D *ᵥ (Sum.elim c d : JV n) =
      Sum.elim (A *ᵥ c + B *ᵥ d) (C *ᵥ c + D *ᵥ d) := by
  rw [Matrix.fromBlocks_mulVec]
  rfl

theorem sym_swap (K : Mat n) (hK : K.transpose = K) (u w : V n) :
    u ⬝ᵥ (K *ᵥ w) = w ⬝ᵥ (K *ᵥ u) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hK, dotProduct_comm]

theorem alt_quad (A : Mat n) (hA : Alt A) (y : V n) : y ⬝ᵥ (A *ᵥ y) = 0 := by
  classical
  let B : Mat n := Matrix.of fun i j => if i < j then A i j else 0
  have hAB : A = B + B.transpose := by
    ext i j
    simp only [B, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
    · subst h; simp [hA.2 i]
    · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
      have := congrFun (congrFun hA.1 i) j
      simpa [Matrix.transpose_apply] using this.symm
  have e : y ⬝ᵥ (B.transpose *ᵥ y) = y ⬝ᵥ (B *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [hAB, Matrix.add_mulVec, dotProduct_add, e, two_zero]

def bil (u w : JV n) : Big n →ₗ[F] F where
  toFun X := u ⬝ᵥ (X *ᵥ w)
  map_add' X Y := by simp [Matrix.add_mulVec, dotProduct_add]
  map_smul' c X := by simp [Matrix.smul_mulVec, dotProduct_smul]

theorem bil_apply (u w : JV n) (X : Big n) : bil u w X = u ⬝ᵥ (X *ᵥ w) := rfl

theorem Gset_right {E : Submodule F (JV n)} {X : Big n} (hX : X ∈ Gset E) (u w : JV n)
    (hw : ∀ e ∈ E, w ⬝ᵥ e = 0) : bil u w X = 0 := by
  have : X *ᵥ w = 0 := by
    funext i
    have h := hw _ (hX.2 i)
    simp only [Matrix.mulVec, Pi.zero_apply]
    rw [dotProduct_comm]
    exact h
  rw [bil_apply, this, dotProduct_zero]

theorem Gset_left {E : Submodule F (JV n)} {X : Big n} (hX : X ∈ Gset E) (u w : JV n)
    (hu : ∀ e ∈ E, u ⬝ᵥ e = 0) : bil u w X = 0 := by
  have : u ᵥ* X = 0 := by
    funext j
    have h := hu _ (hX.1 j)
    simp only [Matrix.vecMul, Pi.zero_apply]
    exact h
  rw [bil_apply, Matrix.dotProduct_mulVec, this, zero_dotProduct]

theorem vanish_L (P : Submodule F (Mat n)) (E : Submodule F (JV n)) (ℓ : Big n →ₗ[F] F)
    (hW : ∀ A K : Mat n, Alt A → K ∈ P → ℓ (Matrix.fromBlocks A K K 0) = 0)
    (hG : ∀ X ∈ Gset E, ℓ X = 0) : ∀ X ∈ Wsp P ⊔ freeSp E, ℓ X = 0 := by
  have h : Wsp P ⊔ freeSp E ≤ LinearMap.ker ℓ := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro X ⟨A, K, hA, hK, rfl⟩
      exact hW A K hA hK
    · apply Submodule.span_le.mpr
      intro X hX
      exact hG X hX
  intro X hX
  exact h hX

theorem rank4_mat (a b c d e f : F) :
    (!![a, b, c, 1; d, e, 1, 0; f, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) F).rank = 4 := by
  have h2 : (2 : F) = 0 := by decide
  let M : Matrix (Fin 4) (Fin 4) F := !![a, b, c, 1; d, e, 1, 0; f, 1, 0, 0; 1, 0, 0, 0]
  let N : Matrix (Fin 4) (Fin 4) F := !![0, 0, 0, 1; 0, 0, 1, f; 0, 1, e, d + e * f;
    1, c, b + c * e, a + b * f + c * (d + e * f)]
  have hMN : M * N = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, N, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring_nf <;> simp [h2]
  have hNM : N * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, N, Matrix.mul_apply, Fin.sum_univ_four] <;>
      ring_nf <;> simp [h2]
  have hu : IsUnit M := ⟨⟨M, N, hMN, hNM⟩, rfl⟩
  show M.rank = 4
  rw [Matrix.rank_of_isUnit M hu]
  simp

theorem rank_four (X : Big n) (a0 a1 a2 a3 : JV n)
    (h03 : a0 ⬝ᵥ (X *ᵥ a3) = 1)
    (h30 : a3 ⬝ᵥ (X *ᵥ a0) = 1) (h12 : a1 ⬝ᵥ (X *ᵥ a2) = 1) (h21 : a2 ⬝ᵥ (X *ᵥ a1) = 1)
    (h13 : a1 ⬝ᵥ (X *ᵥ a3) = 0) (h31 : a3 ⬝ᵥ (X *ᵥ a1) = 0) (h22 : a2 ⬝ᵥ (X *ᵥ a2) = 0)
    (h23 : a2 ⬝ᵥ (X *ᵥ a3) = 0) (h32 : a3 ⬝ᵥ (X *ᵥ a2) = 0) (h33 : a3 ⬝ᵥ (X *ᵥ a3) = 0) :
    4 ≤ X.rank := by
  let vec : Fin 4 → JV n := ![a0, a1, a2, a3]
  let Vm : Matrix (Fin n ⊕ Fin n) (Fin 4) F := Matrix.of fun j a => vec a j
  let M : Matrix (Fin 4) (Fin 4) F := Vm.transpose * X * Vm
  have hM : ∀ a b, M a b = vec a ⬝ᵥ (X *ᵥ vec b) := by
    intro a b
    simp only [M, Vm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have Meq : M = !![M 0 0, M 0 1, M 0 2, 1; M 1 0, M 1 1, 1, 0; M 2 0, 1, 0, 0; 1, 0, 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hM, vec, h03, h30, h12, h21, h13, h31, h22, h23, h32, h33]
  have hr : M.rank = 4 := by
    rw [Meq]
    exact rank4_mat _ _ _ _ _ _
  have le1 : M.rank ≤ X.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  omega

theorem factor {E : Submodule F (JV n)} (ρ : E →ₗ[F] V n) (f : E →ₗ[F] F)
    (h : LinearMap.ker ρ ≤ LinearMap.ker f) : ∃ g : V n →ₗ[F] F, ∀ e, g (ρ e) = f e := by
  obtain ⟨ι, hι⟩ := LinearMap.exists_leftInverse_of_injective ((LinearMap.ker ρ).liftQ ρ le_rfl)
    (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  refine ⟨((LinearMap.ker ρ).liftQ f h).comp ι, fun e => ?_⟩
  have e1 : ρ e = (LinearMap.ker ρ).liftQ ρ le_rfl (Submodule.Quotient.mk e) := rfl
  rw [LinearMap.comp_apply, e1, ← LinearMap.comp_apply ι, hι, LinearMap.id_apply]
  rfl

theorem dual_dot (φ : V n →ₗ[F] F) (v : V n) :
    φ v = v ⬝ᵥ (fun i => φ (fun j => if i = j then 1 else 0)) := by
  rw [LinearMap.pi_apply_eq_sum_univ φ v]
  simp [dotProduct, smul_eq_mul]

def itL : V n →ₗ[F] JV n where
  toFun t := Sum.elim t 0
  map_add' a b := by funext j; cases j <;> simp
  map_smul' c a := by funext j; cases j <;> simp

def pbL : JV n →ₗ[F] V n := LinearMap.funLeft F F Sum.inr

theorem pbL_apply (e : JV n) (i : Fin n) : pbL e i = e (Sum.inr i) := rfl

theorem split_vec (e : JV n) : e = Sum.elim (fun i => e (Sum.inl i)) (fun i => e (Sum.inr i)) := by
  funext j; cases j <;> rfl

theorem dir1 (P : Submodule F (Mat n)) (hP : ∀ K ∈ P, Alt K) (E : Submodule F (JV n))
    (hL : Wsp P ⊔ freeSp E =
      Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2}) :
    Module.finrank F (Hsp P) ≤ Module.finrank F E := by
  classical
  let T0 : Submodule F (V n) := E.comap itL
  let B : Submodule F (V n) := E.map pbL
  let U : Submodule F (V n) := T0 ⊔ B

  let ρ : E →ₗ[F] V n := pbL.comp E.subtype
  have rn := LinearMap.finrank_range_add_finrank_ker ρ
  have hrange : LinearMap.range ρ = B := by
    ext v
    simp [B, ρ]
  have hB : Module.finrank F B ≤ Module.finrank F (LinearMap.range ρ) := by
    rw [hrange]
  have hT : Module.finrank F T0 ≤ Module.finrank F (LinearMap.ker ρ) := by
    let σ : T0 →ₗ[F] LinearMap.ker ρ :=
      LinearMap.codRestrict (LinearMap.ker ρ)
        (LinearMap.codRestrict E (itL.comp T0.subtype) (fun t => t.2))
        (fun t => by
          rw [LinearMap.mem_ker]
          funext i
          rfl)
    apply LinearMap.finrank_le_finrank_of_injective (f := σ)
    intro s t hst
    apply Subtype.ext
    have h1 := congrArg (fun z : LinearMap.ker ρ => ((z : E) : JV n)) hst
    funext i
    have := congrFun h1 (Sum.inl i)
    exact this
  have hU : Module.finrank F ↥(T0 ⊔ B) ≤ Module.finrank F E := by
    have := Submodule.finrank_add_le_finrank_add_finrank T0 B
    omega
  refine le_trans ?_ hU
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro v ⟨K, hK, j, rfl⟩
  show (fun i => K i j) ∈ U
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set y : V n := fun i => φ (fun j => if i = j then 1 else 0) with hy
  have hφy : ∀ v, φ v = v ⬝ᵥ y := fun v => dual_dot φ v
  have perpB : ∀ e ∈ E, (fun i => e (Sum.inr i)) ⬝ᵥ y = 0 := by
    intro e he
    rw [← hφy]
    exact hφ _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem he))
  have perpT : ∀ t : V n, itL t ∈ E → t ⬝ᵥ y = 0 := by
    intro t ht
    rw [← hφy]
    exact hφ _ (Submodule.mem_sup_left ht)

  let fL : E →ₗ[F] F :=
    { toFun := fun e => (fun i => (e : JV n) (Sum.inl i)) ⬝ᵥ y
      map_add' := fun a b => by
        show (fun i => a.1 (Sum.inl i) + b.1 (Sum.inl i)) ⬝ᵥ y = _
        rw [show (fun i => a.1 (Sum.inl i) + b.1 (Sum.inl i)) =
          (fun i => a.1 (Sum.inl i)) + (fun i => b.1 (Sum.inl i)) from rfl, add_dotProduct]
      map_smul' := fun c a => by
        show (fun i => c * a.1 (Sum.inl i)) ⬝ᵥ y = c • _
        rw [show (fun i => c * a.1 (Sum.inl i)) = c • (fun i => a.1 (Sum.inl i)) from rfl,
          smul_dotProduct] }
  have hker : LinearMap.ker ρ ≤ LinearMap.ker fL := by
    intro e he
    rw [LinearMap.mem_ker] at he ⊢
    have hb : ∀ i, (e : JV n) (Sum.inr i) = 0 := fun i => congrFun he i
    have hmem : itL (fun i => (e : JV n) (Sum.inl i)) ∈ E := by
      have : itL (fun i => (e : JV n) (Sum.inl i)) = (e : JV n) := by
        funext j
        cases j with
        | inl i => rfl
        | inr i => exact (hb i).symm
      rw [this]
      exact e.2
    exact perpT _ hmem
  obtain ⟨g, hg⟩ := factor ρ fL hker
  set z : V n := fun i => g (fun j => if i = j then 1 else 0) with hz
  have hgz : ∀ v, g v = v ⬝ᵥ z := fun v => dual_dot g v
  have zprop : ∀ e ∈ E, (fun i => e (Sum.inr i)) ⬝ᵥ z = (fun i => e (Sum.inl i)) ⬝ᵥ y := by
    intro e he
    rw [← hgz]
    exact hg ⟨e, he⟩
  let yt : JV n := Sum.elim y z
  let yb : JV n := Sum.elim 0 y
  have perp_yt : ∀ e ∈ E, yt ⬝ᵥ e = 0 := by
    intro e he
    rw [split_vec e, se_dot, dotProduct_comm y, dotProduct_comm z, zprop e he, two_zero]
  have perp_yb : ∀ e ∈ E, yb ⬝ᵥ e = 0 := by
    intro e he
    rw [split_vec e, se_dot, zero_dotProduct, zero_add, dotProduct_comm]
    exact perpB e he

  have keyx : ∀ x : V n, x ⬝ᵥ (K *ᵥ y) = 0 := by
    intro x
    let xt : JV n := Sum.elim x 0
    let xb : JV n := Sum.elim 0 x

    have gen : ∀ (u w u' w' : JV n),
        (∀ A K' : Mat n, Alt A → K' ∈ P →
          bil u w (Matrix.fromBlocks A K' K' 0) = bil u' w' (Matrix.fromBlocks A K' K' 0)) →
        (∀ X ∈ Gset E, bil u w X = bil u' w' X) →
        ∀ X ∈ Wsp P ⊔ freeSp E, bil u w X = bil u' w' X := by
      intro u w u' w' h1 h2 X hX
      have := vanish_L P E (bil u w - bil u' w')
        (fun A K' hA hK' => by rw [LinearMap.sub_apply, sub_eq_zero]; exact h1 A K' hA hK')
        (fun X hX => by rw [LinearMap.sub_apply, sub_eq_zero]; exact h2 X hX) X hX
      rwa [LinearMap.sub_apply, sub_eq_zero] at this
    have gen0 : ∀ (u w : JV n),
        (∀ A K' : Mat n, Alt A → K' ∈ P → bil u w (Matrix.fromBlocks A K' K' 0) = 0) →
        (∀ X ∈ Gset E, bil u w X = 0) →
        ∀ X ∈ Wsp P ⊔ freeSp E, bil u w X = 0 :=
      fun u w h1 h2 X hX => vanish_L P E (bil u w) h1 h2 X hX
    have Gyt_r : ∀ u, ∀ X ∈ Gset E, bil u yt X = 0 := fun u X hX => Gset_right hX u yt perp_yt
    have Gyb_r : ∀ u, ∀ X ∈ Gset E, bil u yb X = 0 := fun u X hX => Gset_right hX u yb perp_yb
    have Gyt_l : ∀ w, ∀ X ∈ Gset E, bil yt w X = 0 := fun w X hX => Gset_left hX yt w perp_yt
    have Gyb_l : ∀ w, ∀ X ∈ Gset E, bil yb w X = 0 := fun w X hX => Gset_left hX yb w perp_yb
    have F30 := gen yb xt xt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yb, xt, fb_mulVec, se_dot, Matrix.mulVec_zero, zero_dotProduct,
          dotProduct_zero, add_zero, zero_add]
        exact sym_swap K' (hP K' hK').1 y x)
      (fun X hX => by rw [Gyb_l _ X hX, Gyb_r _ X hX])
    have F12 := gen xb yt xt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yb, xt, xb, yt, fb_mulVec, se_dot, Matrix.mulVec_zero,
          zero_dotProduct, dotProduct_zero, add_zero, zero_add, Matrix.zero_mulVec])
      (fun X hX => by rw [Gyt_r _ X hX, Gyb_r _ X hX])
    have F21 := gen yt xb xt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yb, xt, xb, yt, fb_mulVec, se_dot, Matrix.mulVec_zero,
          zero_dotProduct, dotProduct_zero, add_zero, zero_add, Matrix.zero_mulVec]
        exact sym_swap K' (hP K' hK').1 y x)
      (fun X hX => by rw [Gyt_l _ X hX, Gyb_r _ X hX])
    have F13 := gen0 xb yb
      (fun A K' hA hK' => by
        simp [bil_apply, yb, xb, fb_mulVec, se_dot])
      (fun X hX => Gyb_r _ X hX)
    have F31 := gen0 yb xb
      (fun A K' hA hK' => by
        simp [bil_apply, yb, xb, fb_mulVec, se_dot])
      (fun X hX => Gyb_l _ X hX)
    have F22 := gen0 yt yt
      (fun A K' hA hK' => by
        simp only [bil_apply, yt, fb_mulVec, se_dot, Matrix.zero_mulVec, add_zero,
          dotProduct_add, alt_quad A hA y, zero_add]
        rw [sym_swap K' (hP K' hK').1 z y, two_zero])
      (fun X hX => Gyt_r _ X hX)
    have F23 := gen0 yt yb
      (fun A K' hA hK' => by
        simp only [bil_apply, yt, yb, fb_mulVec, se_dot, Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, dotProduct_add, dotProduct_zero]
        exact alt_quad K' (hP K' hK') y)
      (fun X hX => Gyb_r _ X hX)
    have F32 := gen0 yb yt
      (fun A K' hA hK' => by
        simp only [bil_apply, yt, yb, fb_mulVec, se_dot, Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero, zero_add, dotProduct_add, dotProduct_zero, zero_dotProduct]
        exact alt_quad K' (hP K' hK') y)
      (fun X hX => Gyb_l _ X hX)
    have F33 := gen0 yb yb
      (fun A K' hA hK' => by
        simp [bil_apply, yb, fb_mulVec, se_dot])
      (fun X hX => Gyb_r _ X hX)

    have hS : ∀ X ∈ {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2}, bil xt yb X = 0 := by
      rintro X ⟨hXL, hr⟩
      by_contra hne
      have h1 : bil xt yb X = 1 := by
        revert hne
        generalize bil xt yb X = c
        revert c; decide
      have := rank_four X xt xb yt yb h1
        (by rw [← bil_apply, F30 X hXL]; exact h1)
        (by rw [← bil_apply, F12 X hXL]; exact h1)
        (by rw [← bil_apply, F21 X hXL]; exact h1)
        (F13 X hXL) (F31 X hXL) (F22 X hXL) (F23 X hXL) (F32 X hXL) (F33 X hXL)
      omega
    have hspan : Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2} ≤
        LinearMap.ker (bil xt yb) := Submodule.span_le.mpr hS
    have X0mem : Matrix.fromBlocks (0 : Mat n) K K 0 ∈ Wsp P ⊔ freeSp E := by
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨0, K, ⟨by simp, fun i => rfl⟩, hK, rfl⟩
    rw [hL] at X0mem
    have := hspan X0mem
    rw [LinearMap.mem_ker, bil_apply] at this
    simpa [xt, yb, fb_mulVec, se_dot] using this
  have Ky : K *ᵥ y = 0 := by
    funext i
    have := keyx (Pi.single i 1)
    rwa [single_dotProduct, one_mul] at this
  rw [hφy]
  have hsym := (hP K hK).1
  have : (fun i => K i j) ⬝ᵥ y = (K *ᵥ y) j := by
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    have := congrFun (congrFun hsym j) i
    simp only [Matrix.transpose_apply] at this
    rw [this]
  rw [this, Ky]
  rfl

def Lt (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) F := Matrix.of fun j i => if j = Sum.inl i then 1 else 0

def Lb (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) F := Matrix.of fun j i => if j = Sum.inr i then 1 else 0

theorem rank_sandwich {m : Type} [Fintype m] [DecidableEq m] (Pm : Matrix m (Fin n) F) (K : Mat n)
    (Q : Matrix (Fin n) m F) : (Pm * K * Q).rank ≤ K.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem fb_tl (K : Mat n) : Matrix.fromBlocks K 0 0 0 = Lt n * K * (Lt n).transpose := by
  ext (i | i) (j | j) <;> simp [Lt, Matrix.mul_apply, Fintype.sum_sum_type]

theorem fb_br (K : Mat n) : Matrix.fromBlocks 0 0 0 K = Lb n * K * (Lb n).transpose := by
  ext (i | i) (j | j) <;> simp [Lb, Matrix.mul_apply, Fintype.sum_sum_type]

def Ls (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n) F :=
  Matrix.of fun j i => if j = Sum.inl i ∨ j = Sum.inr i then 1 else 0

theorem fb_all (K : Mat n) :
    Matrix.fromBlocks K K K K = Ls n * K * (Ls n).transpose := by
  ext (i | i) (j | j) <;> simp [Ls, Matrix.mul_apply, Fintype.sum_sum_type]

theorem rank_two_sum (u v u' v' : V n) :
    (Matrix.vecMulVec u v + Matrix.vecMulVec u' v').rank ≤ 2 := by
  let U : Matrix (Fin n) (Fin 2) F := Matrix.of fun a t => ![u a, u' a] t
  let R : Matrix (Fin 2) (Fin n) F := Matrix.of fun t b => ![v b, v' b] t
  have e : Matrix.vecMulVec u v + Matrix.vecMulVec u' v' = U * R := by
    ext a b
    simp [U, R, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMulVec_apply]
  rw [e]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width U

def ibL : V n →ₗ[F] JV n where
  toFun t := Sum.elim 0 t
  map_add' a b := by funext j; cases j <;> simp
  map_smul' c a := by funext j; cases j <;> simp

theorem dir2 (P : Submodule F (Mat n)) (hP : ∀ K ∈ P, Alt K)
    (hspan : P = Submodule.span F {K : Mat n | K ∈ P ∧ K.rank ≤ 2}) :
    Wsp P ⊔ freeSp ((Hsp P).map ibL) =
      Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp ((Hsp P).map ibL) ∧ X.rank ≤ 2} := by
  classical
  set E := (Hsp P).map ibL with hEdef
  set L := Wsp P ⊔ freeSp E with hLdef
  set S := {X : Big n | X ∈ L ∧ X.rank ≤ 2} with hSdef
  have inS : ∀ X, X ∈ L → X.rank ≤ 2 → X ∈ Submodule.span F S :=
    fun X h r => Submodule.subset_span ⟨h, r⟩
  have Wmem : ∀ A K : Mat n, Alt A → K ∈ P → Matrix.fromBlocks A K K 0 ∈ L :=
    fun A K hA hK => Submodule.mem_sup_left (Submodule.subset_span ⟨A, K, hA, hK, rfl⟩)
  have alt_tl : ∀ A : Mat n, Alt A → Matrix.fromBlocks A 0 0 0 ∈ L :=
    fun A hA => Wmem A 0 hA P.zero_mem

  have tl_mem : ∀ A : Mat n, Alt A → Matrix.fromBlocks A 0 0 0 ∈ Submodule.span F S := by
    intro A hA
    let e : Fin n → V n := fun i => Pi.single i 1
    let r : Fin n → V n := fun i j => if i < j then A i j else 0
    let C : Fin n → Mat n := fun i => Matrix.vecMulVec (e i) (r i) + Matrix.vecMulVec (r i) (e i)
    have s1 : ∀ a b, (∑ i, Matrix.vecMulVec (e i) (r i)) a b = r a b := by
      intro a b
      rw [Matrix.sum_apply, Finset.sum_eq_single a]
      · simp [e, Matrix.vecMulVec_apply]
      · intro i _ hi
        simp [e, Matrix.vecMulVec_apply, Pi.single_apply, Ne.symm hi]
      · simp
    have s2 : ∀ a b, (∑ i, Matrix.vecMulVec (r i) (e i)) a b = r b a := by
      intro a b
      rw [Matrix.sum_apply, Finset.sum_eq_single b]
      · simp [e, Matrix.vecMulVec_apply]
      · intro i _ hi
        simp [e, Matrix.vecMulVec_apply, Pi.single_apply, Ne.symm hi]
      · simp
    have hA_eq : A = ∑ i, C i := by
      ext a b
      rw [show (∑ i, C i) = (∑ i, Matrix.vecMulVec (e i) (r i)) +
        ∑ i, Matrix.vecMulVec (r i) (e i) from Finset.sum_add_distrib, Matrix.add_apply, s1, s2]
      simp only [r]
      rcases lt_trichotomy a b with h | h | h
      · rw [if_pos h, if_neg (not_lt.mpr h.le), add_zero]
      · subst h; simp [hA.2 a]
      · rw [if_neg (not_lt.mpr h.le), if_pos h, zero_add]
        have := congrFun (congrFun hA.1 a) b
        simpa [Matrix.transpose_apply] using this.symm
    have Calt : ∀ i, Alt (C i) := by
      intro i
      refine ⟨?_, ?_⟩
      · ext a b
        simp only [C, Matrix.transpose_apply, Matrix.add_apply, Matrix.vecMulVec_apply]
        ring
      · intro a
        simp only [C, Matrix.add_apply, Matrix.vecMulVec_apply]
        rw [mul_comm (r i a), two_zero]
    rw [hA_eq, fb_tl, Matrix.mul_sum, Matrix.sum_mul]
    apply Submodule.sum_mem
    intro i _
    apply inS
    · rw [← fb_tl]; exact alt_tl _ (Calt i)
    · exact (rank_sandwich _ _ _).trans (rank_two_sum _ _ _ _)

  let Φ : Mat n →ₗ[F] Big n :=
    { toFun := fun K => Matrix.fromBlocks 0 K K 0
      map_add' := fun a b => by simp [Matrix.fromBlocks_add]
      map_smul' := fun c a => by simp [Matrix.fromBlocks_smul] }
  have off_gen : ∀ K : Mat n, K ∈ P → K.rank ≤ 2 → Φ K ∈ Submodule.span F S := by
    intro K hK hr
    have hKa := hP K hK
    have m1 : Matrix.fromBlocks K 0 0 0 ∈ L := alt_tl K hKa
    have m2 : Matrix.fromBlocks 0 0 0 K ∈ L := by
      apply Submodule.mem_sup_right
      apply Submodule.subset_span
      have colmem : ∀ j, (fun i => K i j) ∈ Hsp P :=
        fun j => Submodule.subset_span ⟨K, hK, j, rfl⟩
      refine ⟨?_, ?_⟩
      · intro j
        cases j with
        | inl j =>
          have : (fun i => (Matrix.fromBlocks (0 : Mat n) 0 0 K) i (Sum.inl j)) = 0 := by
            funext i; cases i <;> rfl
          rw [this]; exact E.zero_mem
        | inr j =>
          have : (fun i => (Matrix.fromBlocks (0 : Mat n) 0 0 K) i (Sum.inr j)) =
              ibL (fun i => K i j) := by
            funext i; cases i <;> rfl
          rw [this]; exact Submodule.mem_map_of_mem (colmem j)
      · intro i
        cases i with
        | inl i =>
          have : (fun j => (Matrix.fromBlocks (0 : Mat n) 0 0 K) (Sum.inl i) j) = 0 := by
            funext j; cases j <;> rfl
          rw [this]; exact E.zero_mem
        | inr i =>
          have : (fun j => (Matrix.fromBlocks (0 : Mat n) 0 0 K) (Sum.inr i) j) =
              ibL (fun j => K j i) := by
            funext j
            cases j with
            | inl j => rfl
            | inr j =>
              have := congrFun (congrFun hKa.1 i) j
              simpa [Matrix.transpose_apply, ibL] using this.symm
          rw [this]; exact Submodule.mem_map_of_mem (colmem i)
    have m0 : Φ K ∈ L := Wmem 0 K ⟨by simp, fun i => rfl⟩ hK
    have e3 : Matrix.fromBlocks K K K K =
        Φ K + Matrix.fromBlocks K 0 0 0 + Matrix.fromBlocks 0 0 0 K := by
      ext (i | i) (j | j) <;> simp [Φ]
    have e4 : Φ K = Matrix.fromBlocks K K K K + Matrix.fromBlocks K 0 0 0 +
        Matrix.fromBlocks 0 0 0 K := by
      ext (i | i) (j | j) <;> simp [Φ, two_zero]
    have m3 : Matrix.fromBlocks K K K K ∈ L := by
      rw [e3]; exact L.add_mem (L.add_mem m0 m1) m2
    rw [e4]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact inS _ m3 (by rw [fb_all]; exact (rank_sandwich _ _ _).trans hr)
    · exact inS _ m1 (by rw [fb_tl]; exact (rank_sandwich _ _ _).trans hr)
    · exact inS _ m2 (by rw [fb_br]; exact (rank_sandwich _ _ _).trans hr)
  have off_mem : ∀ K : Mat n, K ∈ P → Φ K ∈ Submodule.span F S := by
    intro K hK
    have hle : Submodule.span F {K : Mat n | K ∈ P ∧ K.rank ≤ 2} ≤
        (Submodule.span F S).comap Φ := by
      apply Submodule.span_le.mpr
      rintro K' ⟨hK', hr⟩
      exact off_gen K' hK' hr
    have hK' : K ∈ Submodule.span F {K : Mat n | K ∈ P ∧ K.rank ≤ 2} := by
      rw [← hspan]; exact hK
    exact hle hK'
  have hWle : Wsp P ≤ Submodule.span F S := by
    apply Submodule.span_le.mpr
    rintro X ⟨A, K, hA, hK, rfl⟩
    have e : Matrix.fromBlocks A K K 0 = Matrix.fromBlocks A 0 0 0 + Φ K := by
      ext (i | i) (j | j) <;> simp [Φ]
    rw [e]
    exact Submodule.add_mem _ (tl_mem A hA) (off_mem K hK)
  have hFle : freeSp E ≤ Submodule.span F S := by
    apply Submodule.span_le.mpr
    intro X hX
    obtain ⟨q, hq⟩ := E.exists_isCompl
    let π := E.projection q hq
    let ev : Fin n ⊕ Fin n → JV n := fun j k => if j = k then 1 else 0
    have hX_eq : X = ∑ j, Matrix.vecMulVec (fun i => X i j) (π (ev j)) := by
      ext i k
      have hrow : π (fun j => X i j) = (fun j => X i j) :=
        Submodule.projection_apply_left hq ⟨_, hX.2 i⟩
      have hsum : π (fun j => X i j) = ∑ j, X i j • π (ev j) := by
        conv_lhs => rw [pi_eq_sum_univ (fun j => X i j)]
        rw [map_sum]
        simp only [map_smul]
        rfl
      have := congrFun (hrow.symm.trans hsum) k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.sum_apply]
      simp only [Matrix.vecMulVec_apply]
      exact this
    rw [hX_eq]
    apply Submodule.sum_mem
    intro j _
    have hu : (fun i => X i j) ∈ E := hX.1 j
    have hv : π (ev j) ∈ E := Submodule.projection_apply_mem hq _
    have hG : Matrix.vecMulVec (fun i => X i j) (π (ev j)) ∈ Gset E := by
      refine ⟨fun k => ?_, fun i => ?_⟩
      · have : (fun i => Matrix.vecMulVec (fun i => X i j) (π (ev j)) i k) =
            (π (ev j) k) • (fun i => X i j) := by
          funext i; simp [Matrix.vecMulVec_apply, mul_comm]
        rw [this]; exact E.smul_mem _ hu
      · have : (fun k => Matrix.vecMulVec (fun i => X i j) (π (ev j)) i k) =
            (X i j) • π (ev j) := by
          funext k; simp [Matrix.vecMulVec_apply]
        rw [this]; exact E.smul_mem _ hv
    exact inS _ (Submodule.mem_sup_right (Submodule.subset_span hG))
      ((Matrix.rank_vecMulVec_le _ _).trans (by norm_num))
  apply le_antisymm
  · exact sup_le hWle hFle
  · exact Submodule.span_le.mpr (fun X hX => hX.1)

def Fits (P : Submodule F (Mat n)) (b : ℕ) : Prop :=
  ∃ E : Submodule F (JV n), Module.finrank F E ≤ b ∧
    (Wsp P ⊔ freeSp E = Submodule.span F {X : Big n | X ∈ Wsp P ⊔ freeSp E ∧ X.rank ≤ 2})

theorem mainM (P : Submodule F (Mat n)) (hP : ∀ K ∈ P, Alt K) :
    (∀ b : ℕ, Fits P b → Module.finrank F (Hsp P) ≤ b) ∧
    (P = Submodule.span F {K : Mat n | K ∈ P ∧ K.rank ≤ 2} →
      ∀ b : ℕ, Fits P b ↔ Module.finrank F (Hsp P) ≤ b) := by
  have one : ∀ b : ℕ, Fits P b → Module.finrank F (Hsp P) ≤ b := by
    rintro b ⟨E, hE, hL⟩
    exact (dir1 P hP E hL).trans hE
  refine ⟨one, fun hspan b => ⟨one b, fun hb => ?_⟩⟩
  exact ⟨(Hsp P).map ibL, (Submodule.finrank_map_le _ _).trans hb, dir2 P hP hspan⟩

end PEqualNP.Outside.L_lib_986_aux

theorem PEqualNP.Outside.L_lib_986 : (let F := ZMod 2
∀ (n : ℕ) (P : Submodule F (Matrix (Fin n) (Fin n) F)),
  let M := Matrix (Fin n) (Fin n) F
  let J := Fin n ⊕ Fin n
  let Big := Matrix J J F
  let alt := fun (A : M) => A.transpose = A ∧ ∀ i, A i i = 0
  let W := Submodule.span F {X : Big | ∃ A K : M,
    alt A ∧ K ∈ P ∧ X = Matrix.fromBlocks A K K (0 : M)}
  let H := Submodule.span F {v : Fin n → F | ∃ K ∈ P, ∃ j : Fin n, v = fun i => K i j}
  let fits := fun b : ℕ =>
    ∃ E : Submodule F (J → F), Module.finrank F E ≤ b ∧
      let free := Submodule.span F {X : Big |
        (∀ j, (fun i => X i j) ∈ E) ∧ (∀ i, (fun j => X i j) ∈ E)}
      let L := W ⊔ free
      L = Submodule.span F {X : Big | X ∈ L ∧ X.rank ≤ 2}
  (∀ K ∈ P, alt K) →
    (∀ b : ℕ, fits b → Module.finrank F H ≤ b) ∧
    (P = Submodule.span F {K : M | K ∈ P ∧ K.rank ≤ 2} →
      ∀ b : ℕ, fits b ↔ Module.finrank F H ≤ b)) := by
  intro F n P M J Big alt W H fits hP
  exact PEqualNP.Outside.L_lib_986_aux.mainM P hP
