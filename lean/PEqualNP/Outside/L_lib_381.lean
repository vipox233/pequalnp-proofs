import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic
import PEqualNP.Defs

-- L-lib-381: with P the matrix of blocks p, J = [A | P], so col J = col A + col P. The admissible
-- masks are W = comap P (col A), the kernel of P followed by the quotient by col A; rank-nullity
-- gives dim W = s - d. A fiber minus one of its points lies in the dot-product coannihilator of W,
-- of dimension s - dim W <= d.

namespace PEqualNP.Outside.L_lib_381_aux

theorem finrank_map_mkQ {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (U Q : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (Q.map U.mkQ) + Module.finrank (ZMod 2) U =
      Module.finrank (ZMod 2) ↥(U ⊔ Q) := by
  have h1 : Q.map U.mkQ = (U ⊔ Q).map U.mkQ := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]
  have hr : LinearMap.range (U.mkQ.domRestrict (U ⊔ Q)) = (U ⊔ Q).map U.mkQ :=
    LinearMap.range_domRestrict _ _
  have hk : LinearMap.ker (U.mkQ.domRestrict (U ⊔ Q)) = U.comap (U ⊔ Q).subtype := by
    rw [LinearMap.ker_domRestrict, Submodule.ker_mkQ]
  have hrn := LinearMap.finrank_range_add_finrank_ker (U.mkQ.domRestrict (U ⊔ Q))
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe le_sup_left).finrank_eq, ← h1] at hrn
  exact hrn

end PEqualNP.Outside.L_lib_381_aux

open PEqualNP.Outside.L_lib_381_aux in
theorem PEqualNP.Outside.L_lib_381 :
    ∀ (n s m : ℕ) (Y : Fin n → (Fin s → ZMod 2) → Fin m),
      let A : Matrix (Fin n × (Fin s → ZMod 2)) (Fin m) (ZMod 2) :=
        fun e y => (if Y e.1 e.2 = y then 1 else 0) +
                   (if Y e.1 0 = y then 1 else 0)
      let J : Matrix (Fin n × (Fin s → ZMod 2)) (Fin m ⊕ Fin s) (ZMod 2) :=
        fun entry => Sum.elim (A entry) entry.2
      let d := J.rank - A.rank
      Nat.card {a : Fin s → ZMod 2 //
        ∃ label : Fin m → ZMod 2, ∀ z p,
          label (Y z p) + label (Y z 0) = ∑ j, a j * p j} = 2 ^ (s - d) ∧
      ∀ (z : Fin n) (y : Fin m),
        Nat.card {p : Fin s → ZMod 2 // Y z p = y} ≤ 2 ^ d := by
  classical
  intro n s m Y A J d
  let P : Matrix (Fin n × (Fin s → ZMod 2)) (Fin s) (ZMod 2) := fun e j => e.2 j
  have hJ : J = Matrix.fromCols A P := by
    ext e j
    cases j <;> rfl
  let U := LinearMap.range A.mulVecLin
  let Q := LinearMap.range P.mulVecLin
  have hJU : LinearMap.range J.mulVecLin = U ⊔ Q := by
    rw [hJ]
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
      exact Submodule.add_mem_sup (LinearMap.mem_range.2 ⟨_, rfl⟩) (LinearMap.mem_range.2 ⟨_, rfl⟩)
    · refine sup_le ?_ ?_
      · rintro y ⟨v, rfl⟩
        refine LinearMap.mem_range.2 ⟨Sum.elim v 0, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, add_zero]
        rfl
      · rintro y ⟨v, rfl⟩
        refine LinearMap.mem_range.2 ⟨Sum.elim 0 v, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, zero_add]
        rfl
  have hrA : A.rank = Module.finrank (ZMod 2) U := rfl
  have hrJ : J.rank = Module.finrank (ZMod 2) ↥(U ⊔ Q) := by
    show Module.finrank _ (LinearMap.range J.mulVecLin) = _
    rw [hJU]
  let W := Submodule.comap P.mulVecLin U
  have hAv : ∀ (label : Fin m → ZMod 2) (e : Fin n × (Fin s → ZMod 2)),
      Matrix.mulVec A label e = label (Y e.1 e.2) + label (Y e.1 0) := by
    intro label e
    simp [Matrix.mulVec, dotProduct, A, add_mul, Finset.sum_add_distrib]
  have hPv : ∀ (a : Fin s → ZMod 2) (e : Fin n × (Fin s → ZMod 2)),
      Matrix.mulVec P a e = ∑ j, a j * e.2 j := by
    intro a e
    simp [Matrix.mulVec, dotProduct, P, mul_comm]
  have memW : ∀ a, a ∈ W ↔ ∃ label : Fin m → ZMod 2, ∀ z p,
      label (Y z p) + label (Y z 0) = ∑ j, a j * p j := by
    intro a
    simp only [W, U, Submodule.mem_comap, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨label, h⟩
      refine ⟨label, fun z p => ?_⟩
      have h1 := congrFun h (z, p)
      rw [hAv, hPv] at h1
      exact h1
    · rintro ⟨label, h⟩
      refine ⟨label, funext fun e => ?_⟩
      rw [hAv, hPv]
      exact h e.1 e.2
  let g := U.mkQ ∘ₗ P.mulVecLin
  have hker : LinearMap.ker g = W := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hran : LinearMap.range g = Q.map U.mkQ := LinearMap.range_comp _ _
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hker, hran, Module.finrank_fin_fun] at hrn
  have hmk := finrank_map_mkQ U Q
  have hWd : Module.finrank (ZMod 2) W = s - d := by
    show _ = s - (J.rank - A.rank)
    rw [hrJ, hrA]
    omega
  have hcard : ∀ (X : Submodule (ZMod 2) (Fin s → ZMod 2)),
      Nat.card X = 2 ^ Module.finrank (ZMod 2) X := by
    intro X
    rw [Nat.card_eq_fintype_card (α := ↥X), Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥X),
      ZMod.card]
  constructor
  · rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (memW a).symm)), ← hWd]
    exact hcard W
  · intro z y
    by_cases hne : ∃ p0, Y z p0 = y
    · obtain ⟨p0, hp0⟩ := hne
      let D := ((dotProductEquiv (ZMod 2) (Fin s)) :
        (Fin s → ZMod 2) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin s → ZMod 2))
      let C := (W.map D).dualCoannihilator
      have hW' : Module.finrank (ZMod 2) (W.map D) = Module.finrank (ZMod 2) W :=
        LinearEquiv.finrank_map_eq _ W
      have hC := Subspace.finrank_add_finrank_dualCoannihilator_eq (W.map D)
      rw [Module.finrank_fin_fun, hW'] at hC
      have hC' : Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) C = s := hC
      rw [hWd] at hC'
      have hmem : ∀ p : {p // Y z p = y}, p.1 - p0 ∈ C := by
        rintro ⟨p, hp⟩
        rw [Submodule.mem_dualCoannihilator]
        intro φ hφ
        obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hφ
        obtain ⟨label, hl⟩ := (memW a).1 ha
        have e1 := hl z p
        have e2 := hl z p0
        rw [hp] at e1
        rw [hp0] at e2
        show dotProduct a (p - p0) = 0
        rw [dotProduct_sub]
        simp only [dotProduct]
        rw [← e1, ← e2, sub_self]
      have hinj : Function.Injective (fun p : {p // Y z p = y} => (⟨p.1 - p0, hmem p⟩ : C)) := by
        intro p q h
        apply Subtype.ext
        have h1 := congrArg Subtype.val h
        simpa using h1
      calc Nat.card {p // Y z p = y} ≤ Nat.card C := Nat.card_le_card_of_injective _ hinj
        _ = 2 ^ Module.finrank (ZMod 2) C := hcard C
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by clear_value d; omega)
    · have : IsEmpty {p // Y z p = y} := ⟨fun ⟨p, hp⟩ => hne ⟨p, hp⟩⟩
      rw [Nat.card_of_isEmpty]
      exact Nat.zero_le _
