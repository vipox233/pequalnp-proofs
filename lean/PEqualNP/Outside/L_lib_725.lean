import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_725

open Finset

theorem key (m : ℕ) (S : Finset (Fin m → ZMod 2)) :
    (univ.filter (fun w : Fin m → ZMod 2 => ∀ v ∈ S, dotProduct w v = 0)).card =
      2 ^ (m - Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2) (S : Set (Fin m → ZMod 2)))) := by
  classical
  let M : Matrix S (Fin m) (ZMod 2) := fun s => (s : Fin m → ZMod 2)
  have hrank : M.rank = Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) (S : Set (Fin m → ZMod 2))) := by
    have hr : Set.range M.row = (S : Set (Fin m → ZMod 2)) := by
      ext v
      simp [M, Matrix.row]
    rw [Matrix.rank_eq_finrank_span_row, hr]
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fin_fun] at hrn
  have hcard : Fintype.card (LinearMap.ker M.mulVecLin) =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have e : (univ.filter (fun w : Fin m → ZMod 2 => ∀ v ∈ S, dotProduct w v = 0)).card =
      Fintype.card (LinearMap.ker M.mulVecLin) := by
    rw [← Fintype.card_subtype]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro w
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff]
    simp only [Matrix.mulVec, Pi.zero_apply]
    constructor
    · intro h s
      rw [dotProduct_comm]
      exact h s.1 s.2
    · intro h v hv
      rw [dotProduct_comm]
      exact h ⟨v, hv⟩
  rw [e, hcard, ← hrank]
  unfold Matrix.rank
  congr 1
  omega

theorem lemX {R : Type} [CommRing R] (k : ℕ) (h : Fin k → Prop) [DecidablePred h] (X : R) :
    X ^ (univ.filter h).card = ∑ A ∈ (univ : Finset (Fin k)).powerset,
      X ^ (k - A.card) * (1 - X) ^ A.card * (if ∀ i ∈ A, ¬ h i then 1 else 0) := by
  classical
  have h1 : X ^ (univ.filter h).card = ∏ i, ((1 - X) * (if ¬ h i then 1 else 0) + X) := by
    rw [← Finset.prod_const, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : h i <;> simp [hi]
  rw [h1, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole, Finset.prod_const,
    Finset.card_univ_sdiff, Fintype.card_fin]
  ring

theorem lemY {R : Type} [CommRing R] (k : ℕ) (h : Fin k → Prop) [DecidablePred h] (Y : R) :
    Y ^ (univ.filter h).card = ∑ B ∈ (univ : Finset (Fin k)).powerset,
      (Y - 1) ^ B.card * (if ∀ i ∈ B, h i then 1 else 0) := by
  classical
  have h1 : Y ^ (univ.filter h).card = ∏ i, ((Y - 1) * (if h i then 1 else 0) + 1) := by
    rw [← Finset.prod_const, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : h i <;> simp [hi]
  rw [h1, Finset.prod_add]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_boole, Finset.prod_const_one]
  ring

end PEqualNP.Outside.L_lib_725

theorem PEqualNP.Outside.L_lib_725 : (∀ (n names negatives positives : Nat),
  let V := Fin n → ZMod 2
  let W := Fin (n+1) → ZMod 2
  let E := Fin names × V
  let lift := fun p : E => Fin.cons (1 : ZMod 2) p.2
  ∀ (bad : Fin negatives → Finset E) (good : Fin positives → Finset E),
    let hit := fun (coeff : Fin names → W) (cell : Finset E) =>
      (cell.filter (fun p => dotProduct (coeff p.1) (lift p) ≠ 0)).Nonempty
    let rank := fun (pool : Finset E) (y : Fin names) =>
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
        (((pool.filter (fun p => p.1 = y)).image lift : Finset W) : Set W))
    let X : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 0
    let Y : MvPolynomial (Fin 2) ℤ := MvPolynomial.X 1
    (∑ coeff : Fin names → W,
      (X ^ (Finset.univ.filter (fun i => hit coeff (bad i))).card *
       Y ^ (Finset.univ.filter (fun j => ¬hit coeff (good j))).card)) =
    ∑ A ∈ (Finset.univ : Finset (Fin negatives)).powerset,
    ∑ B ∈ (Finset.univ : Finset (Fin positives)).powerset,
      let pool := A.biUnion bad ∪ B.biUnion good
      X ^ (negatives - A.card) * (1-X) ^ A.card * (Y-1) ^ B.card *
        (2 : MvPolynomial (Fin 2) ℤ) ^ (∑ y : Fin names, (n+1 - rank pool y))) := by
  intro n names negatives positives V W E lift bad good hit rank X Y
  have hhit : ∀ coeff cell, ¬ hit coeff cell ↔
      ∀ p ∈ cell, dotProduct (coeff p.1) (lift p) = 0 := by
    intro coeff cell
    simp only [hit, Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff, not_not]
  have hcoeff : ∀ coeff : Fin names → W,
      X ^ (Finset.univ.filter (fun i => hit coeff (bad i))).card *
       Y ^ (Finset.univ.filter (fun j => ¬hit coeff (good j))).card =
      ∑ A ∈ (Finset.univ : Finset (Fin negatives)).powerset,
      ∑ B ∈ (Finset.univ : Finset (Fin positives)).powerset,
        X ^ (negatives - A.card) * (1-X) ^ A.card * (Y-1) ^ B.card *
        (if ∀ p ∈ A.biUnion bad ∪ B.biUnion good,
          dotProduct (coeff p.1) (lift p) = 0 then 1 else 0) := by
    intro coeff
    rw [PEqualNP.Outside.L_lib_725.lemX, PEqualNP.Outside.L_lib_725.lemY, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro A _
    apply Finset.sum_congr rfl
    intro B _
    have hc : (∀ p ∈ A.biUnion bad ∪ B.biUnion good,
          dotProduct (coeff p.1) (lift p) = 0) ↔
        (∀ i ∈ A, ¬ hit coeff (bad i)) ∧ (∀ j ∈ B, ¬ hit coeff (good j)) := by
      simp only [hhit, Finset.mem_union, Finset.mem_biUnion]
      constructor
      · intro h
        exact ⟨fun i hi p hp => h p (Or.inl ⟨i, hi, hp⟩),
          fun j hj p hp => h p (Or.inr ⟨j, hj, hp⟩)⟩
      · rintro ⟨h1, h2⟩ p (⟨i, hi, hp⟩ | ⟨j, hj, hp⟩)
        exacts [h1 i hi p hp, h2 j hj p hp]
    rw [if_congr hc rfl rfl]
    by_cases h1 : ∀ i ∈ A, ¬ hit coeff (bad i) <;>
      by_cases h2 : ∀ j ∈ B, ¬ hit coeff (good j)
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
      ring
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]
      ring
    · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]
      ring
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]
      ring
  have hcount : ∀ pool : Finset E, ∑ coeff : Fin names → W,
      (if ∀ p ∈ pool, dotProduct (coeff p.1) (lift p) = 0
        then (1 : MvPolynomial (Fin 2) ℤ) else 0) =
      (2 : MvPolynomial (Fin 2) ℤ) ^ (∑ y : Fin names, (n+1 - rank pool y)) := by
    intro pool
    have h1 : ∀ coeff : Fin names → W,
        (if ∀ p ∈ pool, dotProduct (coeff p.1) (lift p) = 0
          then (1 : MvPolynomial (Fin 2) ℤ) else 0) =
        ∏ y, (if ∀ v ∈ (pool.filter (fun p => p.1 = y)).image lift,
          dotProduct (coeff y) v = 0 then 1 else 0) := by
      intro coeff
      by_cases hc : ∀ p ∈ pool, dotProduct (coeff p.1) (lift p) = 0
      · rw [if_pos hc]
        symm
        apply Finset.prod_eq_one
        intro y _
        rw [if_pos]
        intro v hv
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
        rw [Finset.mem_filter] at hp
        rw [← hp.2]
        exact hc p hp.1
      · rw [if_neg hc]
        symm
        push_neg at hc
        obtain ⟨p, hp, hne⟩ := hc
        apply Finset.prod_eq_zero (Finset.mem_univ p.1)
        rw [if_neg]
        intro h
        exact hne (h (lift p)
          (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩, rfl⟩))
    have hp := Finset.prod_univ_sum (fun _ : Fin names => (Finset.univ : Finset W))
      (fun y w => (if ∀ v ∈ (pool.filter (fun p => p.1 = y)).image lift,
        dotProduct w v = 0 then (1 : MvPolynomial (Fin 2) ℤ) else 0))
    rw [Fintype.piFinset_univ] at hp
    rw [Finset.sum_congr rfl (fun c _ => h1 c), ← hp, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro y _
    rw [Finset.sum_boole, PEqualNP.Outside.L_lib_725.key]
    simp [rank]
    convert rfl
  rw [Finset.sum_congr rfl (fun coeff _ => hcoeff coeff), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  rw [← Finset.mul_sum, hcount]
