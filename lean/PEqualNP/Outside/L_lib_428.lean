import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_428

open Module

theorem forward (n d : ℕ) (hn : 2 ≤ n) (A B : Fin d → Finset (Fin n))
    (h : ∀ i j : Fin n,
      (Finset.univ.filter (fun t : Fin d => i ∈ A t ∧ j ∈ B t)).card
        = (if i = j then 0 else 1)) : n ≤ d := by
  classical
  set M : Matrix (Fin n) (Fin n) ℚ := fun i j => if i = j then 0 else 1 with hM
  set u : Fin d → (Fin n → ℚ) := fun t i => if i ∈ A t then 1 else 0 with hu
  set v : Fin d → (Fin n → ℚ) := fun t j => if j ∈ B t then 1 else 0 with hv
  have hsum : M = ∑ t, Matrix.of (fun i j => u t i * v t j) := by
    ext i j
    simp only [hM, Matrix.sum_apply, Matrix.of_apply]
    have hcard : (∑ t, u t i * v t j)
        = ((Finset.univ.filter (fun t => i ∈ A t ∧ j ∈ B t)).card : ℚ) := by
      rw [Finset.card_filter]
      push_cast
      refine Finset.sum_congr rfl ?_
      intro t _
      by_cases h1 : i ∈ A t <;> by_cases h2 : j ∈ B t <;> simp [hu, hv, h1, h2]
    rw [hcard, h i j]
    split_ifs <;> norm_num
  have happ : ∀ x : Fin n → ℚ, M.mulVec x = ∑ t, (∑ j, v t j * x j) • u t := by
    intro x
    funext i
    rw [hsum, Matrix.sum_mulVec]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl ?_
    intro t _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have hrange : LinearMap.range M.mulVecLin ≤ Submodule.span ℚ (Set.range u) := by
    rintro _ ⟨x, rfl⟩
    rw [Matrix.mulVecLin_apply, happ x]
    exact Submodule.sum_mem _ (fun t _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩))
  have hinj : Function.Injective M.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    set S : ℚ := ∑ j : Fin n, x j with hSdef
    have hxi : ∀ i : Fin n, x i = S := by
      intro i
      have hi : (M.mulVec x) i = 0 := by
        have h' := congrFun hx i
        simpa [Matrix.mulVecLin_apply] using h' 
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.of_apply] at hi
      have h1 : (∑ j : Fin n, (if i = j then (0:ℚ) else 1) * x j) = S - x i := by
        have hstep : (∑ j : Fin n, (if i = j then (0:ℚ) else 1) * x j)
            = ∑ j ∈ Finset.univ.erase i, x j := by
          rw [← Finset.sum_erase_add _ (fun j => (if i = j then (0:ℚ) else 1) * x j) (Finset.mem_univ i)]
          simp only [ite_true, mul_zero, zero_mul, add_zero]
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hji : j ≠ i := Finset.ne_of_mem_erase hj
          have hij : i ≠ j := fun h' => hji h'.symm
          simp [hij]
        rw [hstep, Finset.sum_erase_eq_sub (Finset.mem_univ i), hSdef]
      rw [h1] at hi
      linarith
    have hsum2 : (∑ i : Fin n, x i) = (n : ℚ) * S := by
      calc ∑ i : Fin n, x i = ∑ i : Fin n, S := Finset.sum_congr rfl (fun i _ => hxi i)
        _ = (n : ℚ) * S := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hSeq : S = (n : ℚ) * S := by rw [hSdef]; exact hsum2
    have hzero : S = 0 := by
      have h' : ((n : ℚ) - 1) * S = 0 := by linarith
      have hn1 : ((n : ℚ) - 1) ≠ 0 := by
        have h2 : (2:ℚ) ≤ n := by exact_mod_cast hn
        linarith
      exact (mul_eq_zero.mp h').resolve_left hn1
    funext i
    rw [hxi i, hzero]
    rfl
  have hrankM : finrank ℚ (LinearMap.range M.mulVecLin) = n := by
    have hker : LinearMap.ker M.mulVecLin = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [hker, finrank_bot, add_zero] at h
    rw [h]
    simp
  have hrankle : finrank ℚ (LinearMap.range M.mulVecLin) ≤ d := by
    have h1 : finrank ℚ (LinearMap.range M.mulVecLin)
        ≤ finrank ℚ (Submodule.span ℚ (Set.range u)) := Submodule.finrank_mono hrange
    have h2 : finrank ℚ (Submodule.span ℚ (Set.range u)) ≤ d := by
      have hle := finrank_span_le_card (R := ℚ) (Set.range u)
      have hcard : (Set.range u).toFinset.card ≤ d := by
        have himg : (Set.range u).toFinset = Finset.univ.image u := by
          ext x
          simp [Set.mem_toFinset, Set.mem_range, Finset.mem_image, eq_comm]
        rw [himg]
        simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d))) (f := u)
      linarith
    linarith
  linarith


theorem reverse (n d : ℕ) (hnd : n ≤ d) :
    ∃ A B : Fin d → Finset (Fin n),
      ∀ i j : Fin n,
        (Finset.univ.filter (fun t : Fin d => i ∈ A t ∧ j ∈ B t)).card
          = (if i = j then 0 else 1) := by
  classical
  let A : Fin d → Finset (Fin n) := fun t => if h : t.val < n then {⟨t.val, h⟩} else ∅
  let B : Fin d → Finset (Fin n) := fun t => if h : t.val < n then Finset.univ.erase ⟨t.val, h⟩ else ∅
  refine ⟨A, B, ?_⟩
  intro i j
  have hi_lt_d : i.val < d := lt_of_lt_of_le i.isLt hnd
  let t0 : Fin d := ⟨i.val, hi_lt_d⟩
  have ht0val : t0.val = i.val := rfl
  have hmem : ∀ t : Fin d, (i ∈ A t ∧ j ∈ B t) ↔ (t = t0 ∧ j ≠ i) := by
    intro t
    constructor
    · rintro ⟨hA, hB⟩
      by_cases ht : t.val < n
      · simp only [A, dif_pos ht, Finset.mem_singleton] at hA
        have ht_eq : t = t0 := Fin.ext (by rw [← ht0val]; exact (congrArg Fin.val hA).symm)
        have hB' : j ≠ i := by
          simp only [B, dif_pos ht, Finset.mem_erase, Finset.mem_univ, and_true] at hB
          rwa [← hA] at hB
        exact ⟨ht_eq, hB'⟩
      · simp only [A, dif_neg ht] at hA
        exact absurd hA (by simp)
    · rintro ⟨rfl, hji⟩
      have ht : t0.val < n := by rw [ht0val]; exact i.isLt
      refine ⟨?_, ?_⟩
      · simp only [A, dif_pos ht, Finset.mem_singleton]
        exact (Fin.ext (by rw [ht0val])).symm
      · simp only [B, dif_pos ht, Finset.mem_erase, Finset.mem_univ, and_true]
        intro h
        exact hji (h.trans (Fin.ext (by rw [ht0val])))
  have hfilter : (Finset.univ.filter (fun t : Fin d => i ∈ A t ∧ j ∈ B t))
      = if j = i then ∅ else {t0} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hmem t]
    by_cases hji : j = i
    · rw [if_pos hji]; simp [hji]
    · rw [if_neg hji]; simp [hji]
  rw [hfilter]
  by_cases hji : j = i
  · rw [if_pos hji]; simp [hji, eq_comm]
  · rw [if_neg hji]
    have hne : i ≠ j := fun h => hji h.symm
    simp [hne]

theorem main (n d : ℕ) (hn : 2 ≤ n) :
    ((∃ A B : Fin d → Finset (Fin n),
      ∀ i j : Fin n, (Finset.univ.filter
        (fun t : Fin d => i ∈ A t ∧ j ∈ B t)).card = (if i = j then 0 else 1)) ↔ n ≤ d) := by
  constructor
  · rintro ⟨A, B, h⟩
    exact forward n d hn A B h
  · intro h
    exact reverse n d h


end PEqualNP.Outside.L_lib_428

theorem PEqualNP.Outside.L_lib_428 : (∀ n d : ℕ, 2 ≤ n →
  ((∃ A B : Fin d → Finset (Fin n),
    ∀ i j : Fin n, (Finset.univ.filter
      (fun t : Fin d => i ∈ A t ∧ j ∈ B t)).card = (if i = j then 0 else 1)) ↔ n ≤ d)) :=
  PEqualNP.Outside.L_lib_428.main
