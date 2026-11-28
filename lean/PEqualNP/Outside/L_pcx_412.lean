import PEqualNP.Defs
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_412

namespace ExpBase

open PEqualNP.Expanders

def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)

theorem permGraph_leftDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    LeftDegLe (permGraph σ) b := by
  intro i
  have hsub : (permGraph σ i).map Fin.castSuccEmb ⊆ Finset.univ.image (fun k => σ k i) := by
    intro x hx
    simp only [Finset.mem_map, permGraph, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.coe_castSuccEmb] at hx
    obtain ⟨j, ⟨k, hk⟩, rfl⟩ := hx
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩
  calc (permGraph σ i).card = ((permGraph σ i).map Fin.castSuccEmb).card := (Finset.card_map _).symm
    _ ≤ (Finset.univ.image (fun k => σ k i)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp

theorem permGraph_rightDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    RightDegLe (permGraph σ) b := by
  intro j
  have hsub : rightNbrs (permGraph σ) j ⊆
      Finset.univ.image (fun k => (σ k).symm j.castSucc) := by
    intro i hi
    simp only [rightNbrs, permGraph, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨k, hk⟩ := hi
    exact Finset.mem_image.2 ⟨k, Finset.mem_univ _, by rw [← hk]; simp⟩
  calc (rightNbrs (permGraph σ) j).card
      ≤ (Finset.univ.image (fun k => (σ k).symm j.castSucc)).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin b)).card := Finset.card_image_le
    _ = b := by simp

theorem permGraph_trap {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1)))
    (hT : 5 * T.card ≤ n + 1)
    (hbad : (uniqueNbrs (permGraph σ) T).card < 2 * T.card) :
    ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y := by
  set G := permGraph σ with hG
  set N := T.biUnion G with hN
  set U := uniqueNbrs G T with hU
  have he : ∑ i ∈ T, (G i).card = ∑ j ∈ N, (T.filter (fun i => j ∈ G i)).card := by
    have h1 : ∀ i ∈ T, (G i).card = ∑ j ∈ N, if j ∈ G i then 1 else 0 := by
      intro i hi
      rw [← Finset.card_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter, hN, Finset.mem_biUnion]
      exact ⟨fun h => ⟨⟨i, hi, h⟩, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  have hle8 : ∑ i ∈ T, (G i).card ≤ 8 * T.card := by
    have := Finset.sum_le_card_nsmul T (fun i => (G i).card) 8
      (fun i _ => permGraph_leftDegLe σ i)
    simpa [mul_comm] using this
  have hpt : ∀ j ∈ N, 2 ≤ (T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0 := by
    intro j hj
    have hpos : 0 < (T.filter (fun i => j ∈ G i)).card := by
      rw [hN, Finset.mem_biUnion] at hj
      obtain ⟨i, hi, hji⟩ := hj
      exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, hji⟩⟩
    by_cases h1 : (T.filter (fun i => j ∈ G i)).card = 1
    · have : j ∈ U := by
        simp only [hU, uniqueNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h1
      simp [this, h1]
    · split_ifs <;> omega
  have hsum : 2 * N.card ≤ ∑ i ∈ T, (G i).card + U.card := by
    have h2 : ∑ j ∈ N, 2 ≤ ∑ j ∈ N,
        ((T.filter (fun i => j ∈ G i)).card + if j ∈ U then 1 else 0) :=
      Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, ← Finset.card_filter, ← he] at h2
    have h3 : (N.filter (fun j => j ∈ U)).card ≤ U.card :=
      Finset.card_le_card (fun j hj => (Finset.mem_filter.1 hj).2)
    simp only [Finset.sum_const, smul_eq_mul] at h2
    omega
  have hNc : N.card + 1 ≤ 5 * T.card := by omega
  set Y0 := N.map Fin.castSuccEmb ∪ {Fin.last n} with hY0
  have hY0c : Y0.card ≤ 5 * T.card := by
    calc Y0.card ≤ (N.map Fin.castSuccEmb).card + ({Fin.last n} : Finset _).card :=
          Finset.card_union_le _ _
      _ = N.card + 1 := by simp
      _ ≤ 5 * T.card := hNc
  obtain ⟨Y, hY0Y, hYc⟩ := Finset.exists_superset_card_eq hY0c (by simpa using hT)
  refine ⟨Y, hYc, fun k x hx => hY0Y ?_⟩
  induction h : σ k x using Fin.lastCases with
  | last => simp [hY0]
  | cast j =>
    have hj : j ∈ N := by
      rw [hN, Finset.mem_biUnion]
      refine ⟨x, hx, ?_⟩
      simp only [hG, permGraph, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨k, h⟩
    simp only [hY0, Finset.mem_union, Finset.mem_map, Fin.coe_castSuccEmb]
    exact Or.inl ⟨j, hj, rfl⟩

theorem permCount :
    ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
      (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
        Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial := by
  intro α _ _ T Y
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y) with hS
  let f : Equiv.Perm α → (T → α) := fun σ x => σ x
  let t : Finset (T → α) :=
    Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ Y)
  have hmaps : ∀ σ ∈ S, f σ ∈ t := by
    intro σ hσ
    simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, fun x => hσ x.1 x.2⟩
    intro a b hab
    exact Subtype.ext (σ.injective hab)
  have ht : t.card ≤ Y.card.descFactorial T.card := by
    have hinj : Function.Injective
        (fun g : t => (⟨fun x => ⟨g.1 x, ((Finset.mem_filter.mp g.2).2.2 x)⟩,
          fun a b hab => (Finset.mem_filter.mp g.2).2.1 (congrArg Subtype.val hab)⟩ : T ↪ Y)) := by
      intro g h hgh
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq] at this
    simpa using this
  have hfib : ∀ g ∈ t, (S.filter (fun σ => f σ = g)).card ≤ (Fintype.card α - T.card).factorial := by
    intro g _
    rcases Finset.eq_empty_or_nonempty (S.filter (fun σ => f σ = g)) with h | ⟨σ₀, hσ₀⟩
    · rw [h]; simp
    have hσ₀g : f σ₀ = g := (Finset.mem_filter.mp hσ₀).2
    let P := {τ : Equiv.Perm α // ∀ a, ¬ (a ∉ T) → τ a = a}
    have hcardP : Fintype.card P = (Fintype.card α - T.card).factorial := by
      rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ T)),
        Fintype.card_perm]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    let F : {σ // σ ∈ S.filter (fun σ => f σ = g)} → P := fun σ =>
      ⟨σ₀⁻¹ * σ.1, by
        intro a ha
        have ha' : a ∈ T := not_not.mp ha
        have h1 : f σ.1 = g := (Finset.mem_filter.mp σ.2).2
        have h2 : σ.1 a = σ₀ a := by
          have e := congrFun (h1.trans hσ₀g.symm) ⟨a, ha'⟩
          simpa [f] using e
        simp [Equiv.Perm.mul_apply, h2]⟩
    have hF : Function.Injective F := by
      intro a b hab
      apply Subtype.ext
      have := congrArg Subtype.val hab
      simpa [F] using this
    have := Fintype.card_le_of_injective F hF
    rw [hcardP, Fintype.card_coe] at this
    exact this
  have := Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  calc S.card ≤ (Fintype.card α - T.card).factorial * t.card := this
    _ ≤ (Fintype.card α - T.card).factorial * Y.card.descFactorial T.card :=
        Nat.mul_le_mul_left _ ht
    _ = _ := Nat.mul_comm _ _

lemma arith_choose_le (N r : ℕ) (hr : 0 < r) : (N.choose r : ℝ) ≤ (3 * N / r) ^ r := by
  have h1 : (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := Nat.choose_le_pow_div r N
  have h2 : (r : ℝ) ^ r / r.factorial ≤ Real.exp r :=
    Real.pow_div_factorial_le_exp (r : ℝ) (by positivity) r
  have h3 : Real.exp r ≤ 3 ^ r := by
    have : Real.exp (r : ℝ) = Real.exp 1 ^ r := by rw [← Real.exp_nat_mul]; simp
    rw [this]
    gcongr
    linarith [Real.exp_one_lt_d9]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hf : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hrr : (0 : ℝ) < (r : ℝ) ^ r := by positivity
  calc (N.choose r : ℝ) ≤ (N : ℝ) ^ r / r.factorial := h1
    _ = (N : ℝ) ^ r / (r : ℝ) ^ r * ((r : ℝ) ^ r / r.factorial) := by field_simp
    _ ≤ (N : ℝ) ^ r / (r : ℝ) ^ r * 3 ^ r := by gcongr; exact h2.trans h3
    _ = (3 * N / r) ^ r := by rw [div_pow, mul_pow]; ring

lemma arith_ratio_le (N t : ℕ) (ht : 1 ≤ t) (hN : 2 * t ≤ N) :
    ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ) ≤ (10 * t / N) ^ t := by
  have hnum : ((5 * t).descFactorial t : ℝ) ≤ ((5 * t : ℕ) : ℝ) ^ t := by
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hden0 : ((N + 1 - t : ℕ) : ℝ) ^ t ≤ (N.descFactorial t : ℝ) := by
    exact_mod_cast Nat.pow_sub_le_descFactorial N t
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hsub : (N : ℝ) / 2 ≤ ((N + 1 - t : ℕ) : ℝ) := by
    have hle : t ≤ N + 1 := by omega
    rw [Nat.cast_sub hle]
    have : (2 * t : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    linarith
  have hden : ((N : ℝ) / 2) ^ t ≤ (N.descFactorial t : ℝ) :=
    (pow_le_pow_left₀ (by positivity) hsub t).trans hden0
  calc ((5 * t).descFactorial t : ℝ) / (N.descFactorial t : ℝ)
      ≤ ((5 * t : ℕ) : ℝ) ^ t / ((N : ℝ) / 2) ^ t :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = (10 * t / N) ^ t := by
        rw [← div_pow]
        congr 1
        push_cast
        field_simp
        ring

lemma arith_term_le (n t : ℕ) (ht : 1 ≤ t) (hts : t * 100000 ≤ n) :
    ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 ≤
      (1 / 4 : ℝ) ^ t := by
  have htpos : (0 : ℝ) < t := by
    have : 0 < t := by omega
    exact_mod_cast this
  have hN : ((n + 1 : ℕ) : ℝ) ≥ 100000 * t := by
    have : t * 100000 ≤ n + 1 := by omega
    have h : ((t * 100000 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h ⊢
    linarith
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 := arith_choose_le (n + 1) t (by omega)
  have h2 := arith_choose_le (n + 1) (5 * t) (by omega)
  have h3 := arith_ratio_le (n + 1) t ht (by omega)
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hratio0 : (0 : ℝ) ≤ ((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ) := by
    positivity
  have h5 : ((5 * t : ℕ) : ℝ) = 5 * (t : ℝ) := by push_cast; ring
  rw [h5] at h2
  have hbase : (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 = 23328000 * t ^ 2 / N ^ 2 := by
    field_simp
    ring
  have hq : (23328000 : ℝ) * t ^ 2 / N ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq0 : (0 : ℝ) ≤ (3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8 := by positivity
  calc ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ (3 * N / t) ^ t * (3 * N / (5 * t)) ^ (5 * t) * ((10 * t / N) ^ t) ^ 8 := by
        gcongr
    _ = ((3 * N / t) * (3 * N / (5 * t)) ^ 5 * (10 * t / N) ^ 8) ^ t := by
        rw [pow_mul (3 * N / (5 * t)) 5 t, ← pow_mul (10 * t / N) t 8, mul_comm t 8,
          pow_mul (10 * t / N) 8 t, mul_pow, mul_pow]
    _ ≤ (1 / 4 : ℝ) ^ t := by
        rw [hbase] at hq0 ⊢
        exact pow_le_pow_left₀ hq0 hq t

theorem arith_bound (n : ℕ) :
    ∑ t ∈ Finset.Icc 1 (n / 100000),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1 := by
  calc ∑ t ∈ Finset.Icc 1 (n / 100000),
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8
      ≤ ∑ t ∈ Finset.Icc 1 (n / 100000), (1 / 4 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Icc] at ht
        exact arith_term_le n t ht.1 ((Nat.le_div_iff_mul_le (by norm_num)).1 ht.2)
    _ = ∑ t ∈ Finset.Ico 1 (n / 100000 + 1), (1 / 4 : ℝ) ^ t := by
        rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ (1 / 4 : ℝ) ^ 1 / (1 - 1 / 4) := geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    _ < 1 := by norm_num

theorem exists_expander (n : ℕ) :
    ∃ G : BipGraph (n + 1) n,
      LeftDegLe G 8 ∧ RightDegLe G 8 ∧ IsBdryExpander G (n / 100000) 2 := by
  classical
  have hs1 := arith_bound n
  have hsn : 5 * (n / 100000) ≤ n := by omega
  set s := n / 100000 with hs
  suffices h : ∃ σ : Fin 8 → Equiv.Perm (Fin (n + 1)), IsBdryExpander (permGraph σ) s 2 by
    obtain ⟨σ, hσ⟩ := h
    exact ⟨permGraph σ, permGraph_leftDegLe σ, permGraph_rightDegLe σ, hσ⟩
  by_contra hno
  push Not at hno
  let A : Finset (Fin (n + 1)) → Finset (Fin (n + 1)) → Finset (Equiv.Perm (Fin (n + 1))) :=
    fun T Y => Finset.univ.filter (fun τ => ∀ x ∈ T, τ x ∈ Y)
  let U : Finset (Fin 8 → Equiv.Perm (Fin (n + 1))) :=
    (Finset.Icc 1 s).biUnion (fun t =>
      (Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun T =>
        (Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1)))).biUnion (fun Y =>
          Fintype.piFinset (fun _ : Fin 8 => A T Y))))
  have hsub : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))) ⊆ U := by
    intro σ _
    have hbad := hno σ
    unfold IsBdryExpander at hbad
    push Not at hbad
    obtain ⟨T, hTs, hTlt⟩ := hbad
    have ht1 : 1 ≤ T.card := by
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · rw [h0] at hTlt; omega
      · exact h0
    obtain ⟨Y, hYc, hY⟩ := permGraph_trap σ T (by omega) hTlt
    simp only [U, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_powersetCard,
      Fintype.mem_piFinset]
    refine ⟨T.card, ⟨ht1, hTs⟩, T, ⟨Finset.subset_univ _, rfl⟩, Y,
      ⟨Finset.subset_univ _, hYc⟩, ?_⟩
    intro k
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun x hx => hY k x hx
  have hAcard : ∀ t, ∀ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
      ∀ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
      (A T Y).card ≤ (5 * t).descFactorial t * (n + 1 - t).factorial := by
    intro t T hT' Y hY'
    rw [Finset.mem_powersetCard] at hT' hY'
    have h := permCount (Fin (n + 1)) T Y
    rw [hT'.2, hY'.2, Fintype.card_fin] at h
    convert h
  have hUcard : U.card ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t * ((n + 1).choose (5 * t) *
      ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) := by
    refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun t _ => ?_)
    refine (Finset.card_biUnion_le).trans ?_
    calc _ ≤ ∑ T ∈ Finset.powersetCard t (Finset.univ : Finset (Fin (n + 1))),
          (n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
          apply Finset.sum_le_sum
          intro T hT'
          refine (Finset.card_biUnion_le).trans ?_
          calc _ ≤ ∑ Y ∈ Finset.powersetCard (5 * t) (Finset.univ : Finset (Fin (n + 1))),
                ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8 := by
                apply Finset.sum_le_sum
                intro Y hY'
                rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
                exact Nat.pow_le_pow_left (hAcard t T hT' Y hY') 8
            _ = _ := by
                rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
                  Fintype.card_fin, smul_eq_mul]
      _ = _ := by
          rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
  have hcardΩ : (Finset.univ : Finset (Fin 8 → Equiv.Perm (Fin (n + 1)))).card =
      ((n + 1).factorial) ^ 8 := by
    rw [Finset.card_univ, Fintype.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fintype.card_perm, Fintype.card_fin]
  have hle : ((n + 1).factorial) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s, (n + 1).choose t *
      ((n + 1).choose (5 * t) * ((5 * t).descFactorial t * (n + 1 - t).factorial) ^ 8) :=
    hcardΩ ▸ (Finset.card_le_card hsub).trans hUcard
  have hleR : (((n + 1).factorial : ℕ) : ℝ) ^ 8 ≤ ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) := by
    exact_mod_cast hle
  have hid : ∑ t ∈ Finset.Icc 1 s,
      ((n + 1).choose t : ℝ) * (((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) * ((n + 1 - t).factorial : ℝ)) ^ 8) =
      (((n + 1).factorial : ℕ) : ℝ) ^ 8 * ∑ t ∈ Finset.Icc 1 s,
        ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
          (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have htn : t ≤ n + 1 := by omega
    have hEF : ((n + 1 - t).factorial : ℝ) * ((n + 1).descFactorial t : ℝ) =
        (((n + 1).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_mul_descFactorial htn
    have hE : ((n + 1).descFactorial t : ℝ) ≠ 0 := by
      have : (n + 1).descFactorial t ≠ 0 := by
        rw [Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
      exact_mod_cast this
    rw [← hEF]
    field_simp
  have hpos : (0 : ℝ) < (((n + 1).factorial : ℕ) : ℝ) ^ 8 := by
    have := Nat.factorial_pos (n + 1)
    positivity
  have hlt := mul_lt_mul_of_pos_left hs1 hpos
  rw [hid] at hleR
  linarith

end ExpBase

namespace FunPHPBase

open MvPolynomial PEqualNP.Expanders PEqualNP.ProofComplexity

section EchelonSec

variable {σ : Type} [Countable σ]

noncomputable def monoKey (a : σ →₀ ℕ) : ℕ ×ₗ ℕ :=
  toLex (a.degree, Classical.choose (Countable.exists_injective_nat (σ →₀ ℕ)) a)

def MonoLt (b a : σ →₀ ℕ) : Prop := monoKey b < monoKey a

theorem monoKey_injective : Function.Injective (monoKey (σ := σ)) := by
  intro a b h
  have h2 := congrArg (fun x => (ofLex x).2) h
  simp only [monoKey, ofLex_toLex] at h2
  exact Classical.choose_spec (Countable.exists_injective_nat (σ →₀ ℕ)) h2

theorem monoLt_of_degree_lt {a b : σ →₀ ℕ} (h : b.degree < a.degree) : MonoLt b a := by
  unfold MonoLt monoKey
  exact Prod.Lex.toLex_lt_toLex.2 (Or.inl h)

theorem degree_le_of_monoLt {a b : σ →₀ ℕ} (h : MonoLt b a) : b.degree ≤ a.degree := by
  unfold MonoLt monoKey at h
  rcases Prod.Lex.toLex_lt_toLex.1 h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

theorem monoLt_wellFounded : WellFounded (MonoLt (σ := σ)) :=
  InvImage.wf monoKey wellFounded_lt

theorem monoLt_trans {a b c : σ →₀ ℕ} (h1 : MonoLt a b) (h2 : MonoLt b c) : MonoLt a c :=
  lt_trans (α := ℕ ×ₗ ℕ) h1 h2

def IsStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (a : σ →₀ ℕ) : Prop :=
  monomial a (1 : ZMod 2) ∉ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a}

noncomputable def echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictSupport (ZMod 2) {a | IsStd U a}

omit [Countable σ] in
theorem echelon_restrictSupport_le {s : Set (σ →₀ ℕ)}
    {P : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    (h : ∀ b ∈ s, monomial b (1 : ZMod 2) ∈ P) : restrictSupport (ZMod 2) s ≤ P := by
  rw [restrictSupport_eq_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, hb, rfl⟩
  exact h b hb

theorem echelon_disjoint (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    Disjoint (echelonStd U) U := by
  classical
  rw [Submodule.disjoint_def]
  intro h hS hU
  by_contra hne
  have hsupp : h.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image h.support monoKey hsupp
  have hstd : IsStd U a := ((mem_restrictSupport_iff (R := ZMod 2)).1 hS) ha
  apply hstd
  have key : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  have hc : h.coeff a = 1 := key _ (mem_support_iff.1 ha)
  have hw : h - monomial a 1 ∈ restrictSupport (ZMod 2) {b | MonoLt b a} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    have hb' : (h - monomial a 1).coeff b ≠ 0 := mem_support_iff.1 hb
    rw [coeff_sub, coeff_monomial] at hb'
    by_cases hab : a = b
    · subst hab
      simp [hc] at hb'
    · rw [if_neg hab, sub_zero] at hb'
      have hbS : b ∈ h.support := mem_support_iff.2 hb'
      exact lt_of_le_of_ne (hmax b hbS) (fun e => hab (monoKey_injective e).symm)
  have heq : monomial a (1 : ZMod 2) = h - (h - monomial a 1) := (sub_sub_cancel _ _).symm
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hU) (Submodule.mem_sup_right hw)

theorem echelon_monomial_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) :
    monomial a (1 : ZMod 2) ∈
      U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
  induction a using (monoLt_wellFounded (σ := σ)).induction
  rename_i a ih
  by_cases hs : IsStd U a
  · apply Submodule.mem_sup_right
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl hs)
    · exact (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  · have hmem : monomial a (1 : ZMod 2) ∈ U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} :=
      Classical.byContradiction fun h => hs h
    have hle : U ⊔ restrictSupport (ZMod 2) {b | MonoLt b a} ≤
        U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a}) := by
      refine sup_le le_sup_left ?_
      refine echelon_restrictSupport_le ?_
      intro b hb
      refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
        (ih b hb)
      intro c hc
      rcases hc with rfl | hc
      · exact Or.inr hb
      · exact Or.inr (monoLt_trans hc hb)
    exact hle hmem

theorem echelon_le_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s) :
    restrictSupport (ZMod 2) s ≤ U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) s) := by
  refine echelon_restrictSupport_le ?_
  intro a ha
  refine (sup_le_sup_left (inf_le_inf_left _ (restrictSupport_mono (R := ZMod 2) ?_)) U)
    (echelon_monomial_mem U a)
  intro b hb
  rcases hb with hb | hb
  · rw [hb]; exact ha
  · exact hs a ha b hb

theorem echelon_isCompl (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    IsCompl (echelonStd U) U := by
  refine ⟨echelon_disjoint U, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro f _
  have hf : f ∈ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ)) := by
    rw [mem_restrictSupport_iff]
    exact Set.subset_univ _
  have h := echelon_le_of_downClosed U (s := Set.univ) (fun _ _ _ _ => trivial) hf
  have hle : U ⊔ (echelonStd U ⊓ restrictSupport (ZMod 2) (Set.univ : Set (σ →₀ ℕ))) ≤
      echelonStd U ⊔ U :=
    sup_le le_sup_right (inf_le_left.trans le_sup_left)
  exact hle h

noncomputable def nf (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) :
    MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2) :=
  Submodule.projection (echelonStd U) U (echelon_isCompl U)

theorem nf_mem_echelonStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f ∈ echelonStd U :=
  Submodule.projection_apply_mem (echelon_isCompl U) f

theorem nf_sub_mem (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : f - nf U f ∈ U :=
  Submodule.sub_projection_mem (echelon_isCompl U) f

theorem nf_support_isStd (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : ∀ a ∈ (nf U f).support, IsStd U a :=
  fun _ ha => ((mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_echelonStd U f)) ha

theorem nf_unique (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {f g : MvPolynomial σ (ZMod 2)} (hg : ∀ a ∈ g.support, IsStd U a) (hfg : f - g ∈ U) :
    nf U f = g := by
  have hgS : g ∈ echelonStd U := (mem_restrictSupport_iff (R := ZMod 2)).2 fun a ha => hg a ha
  have h1 : nf U f - g ∈ echelonStd U := Submodule.sub_mem _ (nf_mem_echelonStd U f) hgS
  have h2 : nf U f - g ∈ U := by
    have h3 := Submodule.sub_mem _ hfg (nf_sub_mem U f)
    rwa [sub_sub_sub_cancel_left] at h3
  exact sub_eq_zero.1 ((Submodule.disjoint_def.1 (echelon_disjoint U)) _ h1 h2)

theorem nf_eq_zero_iff (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : nf U f = 0 ↔ f ∈ U := by
  constructor
  · intro h
    have h3 := nf_sub_mem U f
    rwa [h, sub_zero] at h3
  · intro h
    exact nf_unique U (by simp) (by rwa [sub_zero])

theorem nf_mem_of_downClosed (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    {s : Set (σ →₀ ℕ)} (hs : ∀ a ∈ s, ∀ b, MonoLt b a → b ∈ s)
    {f : MvPolynomial σ (ZMod 2)} (hf : f ∈ restrictSupport (ZMod 2) s) :
    nf U f ∈ restrictSupport (ZMod 2) s := by
  obtain ⟨u, hu, g, hg, hug⟩ := Submodule.mem_sup.1 (echelon_le_of_downClosed U hs hf)
  have hgs := Submodule.mem_inf.1 hg
  have hnf : nf U f = g := by
    refine nf_unique U (fun c hc => (mem_restrictSupport_iff (R := ZMod 2)).1 hgs.1 hc) ?_
    rw [← hug, add_sub_cancel_right]
    exact hu
  rw [hnf]
  exact hgs.2

omit [Countable σ] in
theorem echelon_sum_eq_degree (b : σ →₀ ℕ) : (b.sum fun _ e => e) = b.degree := by
  rw [Finsupp.degree_apply]
  rfl

theorem totalDegree_nf_le (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (f : MvPolynomial σ (ZMod 2)) : (nf U f).totalDegree ≤ f.totalDegree := by
  have hd : ∀ c ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree}, ∀ b, MonoLt b c →
      b ∈ {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} :=
    fun _ hc _ hb => le_trans (degree_le_of_monoLt hb) hc
  have hf : f ∈ restrictSupport (ZMod 2) {b : σ →₀ ℕ | b.degree ≤ f.totalDegree} := by
    rw [mem_restrictSupport_iff]
    intro b hb
    exact (echelon_sum_eq_degree b).symm.trans_le (le_totalDegree hb)
  have hg := (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hf)
  unfold totalDegree
  exact Finset.sup_le fun b hb => (echelon_sum_eq_degree b).trans_le (hg hb)

end EchelonSec

theorem not_pcRefutable_of_pseudoReduction {σ : Type}
    {F : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (R : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] MvPolynomial σ (ZMod 2))
    (hax : ∀ f ∈ F, f.totalDegree ≤ D → R f = 0)
    (hmul : ∀ (v : σ) (a : σ →₀ ℕ), a.degree + 1 ≤ D →
      R (X v * monomial a 1) = R (X v * R (monomial a 1)))
    (hone : R 1 ≠ 0) :
    ¬ PCRefutable F D := by
  have hsum : ∀ (v : σ) (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ a ∈ s, a.degree + 1 ≤ D) →
      R (X v * ∑ a ∈ s, c a • monomial a 1) =
        R (X v * R (∑ a ∈ s, c a • monomial a 1)) := by
    intro v s c hs
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul]
    exact Finset.sum_congr rfl fun a ha => by rw [hmul v a (hs a ha)]
  have key : ∀ {p : MvPolynomial σ (ZMod 2)}, PCDerivable F D p → R p = 0 := by
    intro p h
    induction h with
    | ax hp hdeg => exact hax _ hp hdeg
    | zero => exact map_zero R
    | add _ _ ih1 ih2 => rw [map_add, ih1, ih2, add_zero]
    | @mulX j p _ hdeg ih =>
      by_cases hp0 : p = 0
      · rw [hp0, mul_zero, map_zero]
      · have hdeg' : p.totalDegree + 1 ≤ D := by
          rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X] at hdeg
          omega
        have hp : p = ∑ a ∈ p.support, p.coeff a • monomial a (1 : ZMod 2) := by
          conv_lhs => rw [p.as_sum]
          exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
        have hs : ∀ a ∈ p.support, a.degree + 1 ≤ D := by
          intro a ha
          have h1 : a.degree ≤ p.totalDegree := le_totalDegree ha
          omega
        have h2 := hsum j p.support (fun a => p.coeff a) hs
        rw [← hp, ih, mul_zero, map_zero] at h2
        exact h2
  intro href
  exact hone (key href)

theorem monomial_one_mul_X {σ : Type} (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]

theorem totalDegree_monomial_one {σ : Type} (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

section GraphSec

variable {m N : ℕ} (G : BipGraph m N)

def ContainedIn (s : ℕ) (H : Finset (Fin N)) (T : Finset (Fin m)) : Prop :=
  T.card ≤ s ∧ uniqueNbrs G T ⊆ H

open Classical in
noncomputable def supp (s : ℕ) (H : Finset (Fin N)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∃ T, i ∈ T ∧ ContainedIn G s H T)

open Classical in
lemma mem_supp {s : ℕ} {H : Finset (Fin N)} {i : Fin m} :
    i ∈ supp G s H ↔ ∃ T, i ∈ T ∧ ContainedIn G s H T := by
  simp [supp]

def SuppClosed (s : ℕ) (K : Finset (Fin N)) (S : Finset (Fin m)) : Prop :=
  ∀ T : Finset (Fin m), S ⊂ T → T.card ≤ s → ¬ uniqueNbrs G T ⊆ K ∪ S.biUnion G

lemma mem_uniqueNbrs {T : Finset (Fin m)} {j : Fin N} :
    j ∈ uniqueNbrs G T ↔ (T.filter (fun i => j ∈ G i)).card = 1 := by
  simp [uniqueNbrs]

theorem uniqueNbrs_union_subset (A B : Finset (Fin m)) :
    uniqueNbrs G (A ∪ B) ⊆ uniqueNbrs G A ∪ uniqueNbrs G B := by
  intro j hj
  rw [mem_uniqueNbrs, Finset.filter_union] at hj
  rw [Finset.mem_union, mem_uniqueNbrs, mem_uniqueNbrs]
  by_cases hA : (A.filter (fun i => j ∈ G i)).card = 0
  · right
    rw [Finset.card_eq_zero] at hA
    rw [hA, Finset.empty_union] at hj
    exact hj
  · left
    have h1 : (A.filter (fun i => j ∈ G i)).card ≤ 1 :=
      hj ▸ Finset.card_le_card Finset.subset_union_left
    omega

lemma two_mul_card_le_of_containedIn {s : ℕ} (hG : IsBdryExpander G s 2)
    {H : Finset (Fin N)} {T : Finset (Fin m)} (hT : ContainedIn G s H T) :
    2 * T.card ≤ H.card :=
  (hG T hT.1).trans (Finset.card_le_card hT.2)

lemma containedIn_union {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) {A B : Finset (Fin m)} (hA : ContainedIn G s H A)
    (hB : ContainedIn G s H B) : ContainedIn G s H (A ∪ B) := by
  refine ⟨?_, ?_⟩
  · have h1 := two_mul_card_le_of_containedIn G hG hA
    have h2 := two_mul_card_le_of_containedIn G hG hB
    have h3 := Finset.card_union_le A B
    omega
  · exact (uniqueNbrs_union_subset G A B).trans (Finset.union_subset hA.2 hB.2)

lemma containedIn_empty (s : ℕ) (H : Finset (Fin N)) :
    ContainedIn G s H (∅ : Finset (Fin m)) := by
  refine ⟨by simp, ?_⟩
  intro j hj
  simp [uniqueNbrs] at hj

theorem supp_containedIn {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : ContainedIn G s H (supp G s H) := by
  have key : ∀ U : Finset (Fin m), U ⊆ supp G s H →
      ∃ T, U ⊆ T ∧ T ⊆ supp G s H ∧ ContainedIn G s H T := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨∅, Finset.empty_subset _, Finset.empty_subset _, containedIn_empty G s H⟩
    | insert i U _ ih =>
      intro hU
      obtain ⟨T, hUT, hTS, hT⟩ := ih ((Finset.subset_insert i U).trans hU)
      have hi : i ∈ supp G s H := hU (Finset.mem_insert_self i U)
      obtain ⟨Ti, hiTi, hTi⟩ := (mem_supp G).mp hi
      have hTiS : Ti ⊆ supp G s H := fun k hk =>
        (mem_supp G).mpr ⟨Ti, hk, hTi⟩
      refine ⟨Ti ∪ T, ?_, Finset.union_subset hTiS hTS, containedIn_union G hG hH hTi hT⟩
      exact Finset.insert_subset (Finset.mem_union_left _ hiTi)
        (hUT.trans Finset.subset_union_right)
  obtain ⟨T, h1, h2, hT⟩ := key (supp G s H) (Finset.Subset.refl _)
  rw [← Finset.Subset.antisymm h2 h1]
  exact hT

theorem two_mul_card_supp_le {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : 2 * (supp G s H).card ≤ H.card :=
  two_mul_card_le_of_containedIn G hG (supp_containedIn G hG hH)

lemma mem_uniqueNbrs_of_subset {S T : Finset (Fin m)} (hST : S ⊆ T) {j : Fin N}
    (hj : j ∈ uniqueNbrs G T) (hjS : j ∈ S.biUnion G) : j ∈ uniqueNbrs G S := by
  rw [mem_uniqueNbrs] at hj ⊢
  obtain ⟨i, hiS, hji⟩ := Finset.mem_biUnion.mp hjS
  have h1 : (S.filter (fun i => j ∈ G i)).card ≤ 1 :=
    hj ▸ Finset.card_le_card (Finset.filter_subset_filter _ hST)
  have h2 : 0 < (S.filter (fun i => j ∈ G i)).card :=
    Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hiS, hji⟩⟩
  omega

theorem suppClosed_supp {s : ℕ} (hG : IsBdryExpander G s 2) {H : Finset (Fin N)}
    (hH : H.card ≤ s) : SuppClosed G s H (supp G s H) := by
  intro T hST hT hsub
  have hS := supp_containedIn G hG hH
  have hTH : uniqueNbrs G T ⊆ H := by
    intro j hj
    rcases Finset.mem_union.mp (hsub hj) with h | h
    · exact h
    · exact hS.2 (mem_uniqueNbrs_of_subset G hST.subset hj h)
  have hTS : T ⊆ supp G s H := fun k hk =>
    (mem_supp G).mpr ⟨T, hk, hT, hTH⟩
  exact (Finset.not_subset.mp hST.2).elim fun k ⟨hkT, hkS⟩ => hkS (hTS hkT)

theorem SuppClosed.mono {s : ℕ} {K K' : Finset (Fin N)} {S : Finset (Fin m)}
    (h : SuppClosed G s K S) (hK : K' ⊆ K ∪ S.biUnion G) : SuppClosed G s K' S := by
  intro T hST hT hsub
  apply h T hST hT
  intro j hj
  rcases Finset.mem_union.mp (hsub hj) with h1 | h1
  · exact hK h1
  · exact Finset.mem_union_right _ h1

theorem SuppClosed.peel {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (h : SuppClosed G s K S) (hST : S ⊂ T) (hT : T.card ≤ s) :
    ∃ p ∈ T, p ∉ S ∧ ∃ j ∈ G p, j ∉ K ∧ j ∉ (T.erase p).biUnion G := by
  obtain ⟨j, hj, hjK⟩ := Finset.not_subset.mp (h T hST hT)
  rw [Finset.mem_union, not_or] at hjK
  obtain ⟨hjK, hjS⟩ := hjK
  rw [mem_uniqueNbrs, Finset.card_eq_one] at hj
  obtain ⟨p, hp⟩ := hj
  have hpmem : p ∈ T.filter (fun i => j ∈ G i) := hp ▸ Finset.mem_singleton_self p
  obtain ⟨hpT, hjp⟩ := Finset.mem_filter.mp hpmem
  refine ⟨p, hpT, ?_, j, hjp, hjK, ?_⟩
  · intro hpS
    exact hjS (Finset.mem_biUnion.mpr ⟨p, hpS, hjp⟩)
  · intro hj'
    obtain ⟨q, hq, hjq⟩ := Finset.mem_biUnion.mp hj'
    obtain ⟨hqp, hqT⟩ := Finset.mem_erase.mp hq
    have : q ∈ T.filter (fun i => j ∈ G i) := Finset.mem_filter.mpr ⟨hqT, hjq⟩
    rw [hp, Finset.mem_singleton] at this
    exact hqp this

lemma uniqueNbrs_singleton (i : Fin m) : uniqueNbrs G {i} = G i := by
  ext j
  rw [mem_uniqueNbrs]
  by_cases hj : j ∈ G i
  · simp [Finset.filter_singleton, hj]
  · simp [Finset.filter_singleton, hj]

theorem mem_supp_self {s : ℕ} (hs : 1 ≤ s) (i : Fin m) {H : Finset (Fin N)}
    (hi : G i ⊆ H) : i ∈ supp G s H :=
  (mem_supp G).mpr ⟨{i}, Finset.mem_singleton_self i,
    by simpa using hs, by rw [uniqueNbrs_singleton]; exact hi⟩

def localSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  (∀ e e' : GEdge G, e.1.2 = e'.1.2 → e.1.1 ≠ e'.1.1 → α e * α e' = 0) ∧
  ∀ i ∈ S, ∃ e : GEdge G, e.1.1 = i ∧ α e = 1

noncomputable def locIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : localSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_locIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ locIdeal G S ↔ ∀ α, localSat G S α → eval α f = 0 := by
  simp only [locIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

def monoHoles (a : GEdge G →₀ ℕ) : Finset (Fin N) := a.support.image (fun e => e.1.2)

def pigeonClause (i : Fin m) : Clause (GEdge G) :=
  Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

theorem bool_mem_locIdeal (S : Finset (Fin m)) (v : GEdge G) :
    X v * X v + X v ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α _
  have h : ∀ x : ZMod 2, x * x + x = 0 := by decide
  simpa using h (α v)

theorem hole_mem_locIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.2 = e'.1.2) (h2 : e.1.1 ≠ e'.1.1) : X e * X e' ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  simpa using hα.1 e e' h1 h2

theorem pigeon_mem_locIdeal {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) :
    clausePoly (pigeonClause G i) ∈ locIdeal G S := by
  rw [mem_locIdeal]
  intro α hα
  obtain ⟨e, he, hαe⟩ := hα.2 i hi
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [clausePoly, map_prod]
  refine Finset.prod_eq_zero (i := ((e, true) : Literal (GEdge G))) ?_ ?_
  · simp [pigeonClause, he]
  · simp [hαe, h2]

theorem localSat_clausePoly_pigeonClause (i : Fin m) :
    clausePoly (pigeonClause G i)
      = ∏ l ∈ pigeonClause G i, (1 + X l.1 : MvPolynomial (GEdge G) (ZMod 2)) := by
  rw [clausePoly]
  refine Finset.prod_congr rfl fun l hl => ?_
  have hl2 : l.2 = true := (Finset.mem_filter.mp hl).2.2
  simp only [hl2, ite_true]

theorem localSat_card_pigeonClause (i : Fin m) : (pigeonClause G i).card = (G i).card := by
  refine Finset.card_bij (fun l _ => l.1.1.2) ?_ ?_ ?_
  · intro l hl
    have h := (Finset.mem_filter.mp hl).2.1
    have := l.1.2
    rwa [h] at this
  · rintro ⟨⟨⟨p, j⟩, hpj⟩, b⟩ hl ⟨⟨⟨p', j'⟩, hpj'⟩, b'⟩ hl' hjj
    have h := (Finset.mem_filter.mp hl).2
    have h' := (Finset.mem_filter.mp hl').2
    simp only at h h' hjj
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := h'
    subst hjj
    rfl
  · intro j hj
    exact ⟨((⟨(i, j), hj⟩ : GEdge G), true), by simp [pigeonClause], rfl⟩

theorem totalDegree_pigeonClause (i : Fin m) :
    (clausePoly (pigeonClause G i)).totalDegree = (G i).card := by
  classical
  have hdeg : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 1 := by
    intro v
    rw [totalDegree_add_eq_right_of_totalDegree_lt
      (by rw [totalDegree_one, totalDegree_X]; exact Nat.zero_lt_one), totalDegree_X]
  have hne : ∀ v : GEdge G, (1 + X v : MvPolynomial (GEdge G) (ZMod 2)) ≠ 0 := by
    intro v h0
    have := hdeg v
    rw [h0, totalDegree_zero] at this
    exact Nat.zero_ne_one this
  rw [localSat_clausePoly_pigeonClause, ← localSat_card_pigeonClause]
  generalize pigeonClause G i = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
      totalDegree_mul_of_isDomain (hne _) (Finset.prod_ne_zero_iff.mpr fun l _ => hne _),
      ih, hdeg, add_comm]

theorem cnfSystem_graphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (graphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    ∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · refine Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩)
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp

theorem localNF_eval_bind₁ {σ : Type} (α : σ → ZMod 2) (φ : σ → MvPolynomial σ (ZMod 2))
    (f : MvPolynomial σ (ZMod 2)) :
    eval α (bind₁ φ f) = eval (fun e => eval α (φ e)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p e hp => rw [map_mul, map_mul, map_mul, hp, bind₁_X_right, eval_X]

theorem localNF_map_eq_sum (L : MvPolynomial (GEdge G) (ZMod 2) →ₐ[ZMod 2]
    MvPolynomial (GEdge G) (ZMod 2)) (w : MvPolynomial (GEdge G) (ZMod 2)) :
    L w = ∑ c ∈ w.support, L (monomial c (w.coeff c)) := by
  conv_lhs => rw [← support_sum_monomial_coeff w]
  rw [map_sum]

noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)

theorem localNF_drop_eq_or_degree_lt (j : Fin N) (c : GEdge G →₀ ℕ) :
    localNF_drop G j c = c ∨ (localNF_drop G j c).degree < c.degree := by
  have hsplit : localNF_drop G j c + c.filter (fun e => ¬ e.1.2 ≠ j) = c :=
    Finsupp.filter_add_filter_not c _
  by_cases h0 : c.filter (fun e => ¬ e.1.2 ≠ j) = 0
  · left
    rw [h0, add_zero] at hsplit
    exact hsplit
  · right
    have hdeg : (localNF_drop G j c).degree + (c.filter (fun e => ¬ e.1.2 ≠ j)).degree
        = c.degree := by
      rw [← map_add, hsplit]
    have hpos : 0 < (c.filter (fun e => ¬ e.1.2 ≠ j)).degree :=
      Nat.pos_of_ne_zero fun h => h0 ((Finsupp.degree_eq_zero_iff _).mp h)
    omega

def funLocalSat (S : Finset (Fin m)) (α : GEdge G → ZMod 2) : Prop :=
  localSat G S α ∧
  ∀ e e' : GEdge G, e.1.1 = e'.1.1 → e.1.2 ≠ e'.1.2 → α e * α e' = 0

noncomputable def funLocIdeal (S : Finset (Fin m)) :
    Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)) :=
  ⨅ (α : GEdge G → ZMod 2) (_ : funLocalSat G S α),
    LinearMap.ker (MvPolynomial.aeval (R := ZMod 2) α).toLinearMap

theorem mem_funLocIdeal {S : Finset (Fin m)} {f : MvPolynomial (GEdge G) (ZMod 2)} :
    f ∈ funLocIdeal G S ↔ ∀ α, funLocalSat G S α → eval α f = 0 := by
  simp only [funLocIdeal, Submodule.mem_iInf, LinearMap.mem_ker, AlgHom.toLinearMap_apply]
  rfl

theorem locIdeal_le_funLocIdeal (S : Finset (Fin m)) : locIdeal G S ≤ funLocIdeal G S := by
  intro f hf
  rw [mem_locIdeal] at hf
  rw [mem_funLocIdeal]
  exact fun α hα => hf α hα.1

theorem funLocIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') :
    funLocIdeal G S ≤ funLocIdeal G S' := by
  intro f hf
  rw [mem_funLocIdeal] at hf ⊢
  exact fun α hα => hf α ⟨⟨hα.1.1, fun i hi => hα.1.2 i (h hi)⟩, hα.2⟩

theorem X_mul_mem_funLocIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    X v * f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]

theorem fun_mem_funLocIdeal (S : Finset (Fin m)) {e e' : GEdge G}
    (h1 : e.1.1 = e'.1.1) (h2 : e.1.2 ≠ e'.1.2) : X e * X e' ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal]
  intro α hα
  simpa using hα.2 e e' h1 h2

theorem one_not_mem_funLocIdeal_empty :
    (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ funLocIdeal G ∅ := by
  rw [mem_funLocIdeal]
  intro h
  have h0 := h (fun _ => 0)
    ⟨⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩, fun _ _ _ _ => mul_zero _⟩
  rw [map_one] at h0
  exact one_ne_zero h0

def monoPigeons (a : GEdge G →₀ ℕ) : Finset (Fin m) := a.support.image (fun e => e.1.1)

def monoNbrs (a : GEdge G →₀ ℕ) : Finset (Fin N) := (monoPigeons G a).biUnion G

theorem card_monoNbrs_le {d : ℕ} (hd : LeftDegLe G d) (a : GEdge G →₀ ℕ) :
    (monoNbrs G a).card ≤ d * a.degree := by
  have h1 : (monoNbrs G a).card ≤ (monoPigeons G a).card * d :=
    Finset.card_biUnion_le_card_mul _ _ _ fun i _ => hd i
  have h2 : (monoPigeons G a).card ≤ a.degree := by
    refine Finset.card_image_le.trans ?_
    rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
  calc (monoNbrs G a).card ≤ (monoPigeons G a).card * d := h1
    _ ≤ a.degree * d := Nat.mul_le_mul_right d h2
    _ = d * a.degree := Nat.mul_comm _ _

theorem monoNbrs_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoNbrs G (a + Finsupp.single v 1) = monoNbrs G a ∪ G v.1.1 := by
  ext j
  simp only [monoNbrs, monoPigeons, Finset.mem_biUnion, Finset.mem_image, Finset.mem_union,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  constructor
  · rintro ⟨i, ⟨e, he, rfl⟩, hj⟩
    by_cases hev : e = v
    · exact Or.inr (hev ▸ hj)
    · refine Or.inl ⟨e.1.1, ⟨e, ?_, rfl⟩, hj⟩
      rwa [Finsupp.single_apply, ite_eq_right (Ne.symm hev), add_zero] at he
  · rintro (⟨i, ⟨e, he, rfl⟩, hj⟩ | hj)
    · exact ⟨e.1.1, ⟨e, fun h0 => he (Nat.eq_zero_of_add_eq_zero_right h0), rfl⟩, hj⟩
    · exact ⟨v.1.1, ⟨v, by rw [Finsupp.single_eq_same]; omega, rfl⟩, hj⟩

theorem monoNbrs_subset_of_monoPigeons {a b : GEdge G →₀ ℕ} {S : Finset (Fin m)}
    (h : monoPigeons G b ⊆ monoPigeons G a ∪ S) :
    monoNbrs G b ⊆ monoNbrs G a ∪ S.biUnion G := by
  intro j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  rcases Finset.mem_union.mp (h hi) with h' | h'
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, h', hji⟩)

theorem monoNbrs_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoNbrs G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨i', hi', hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi'
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  rwa [h] at hji

theorem cnfSystem_funGraphPHP_cases {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) :
    (∃ v, f = X v * X v + X v) ∨ (∃ i, f = clausePoly (pigeonClause G i)) ∨
    (∃ e e' : GEdge G, e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ f = X e * X e') ∨
    ∃ e e' : GEdge G, e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ f = X e * X e' := by
  rcases hf with ⟨v, rfl⟩ | ⟨C, hC, rfl⟩
  · exact Or.inl ⟨v, rfl⟩
  · rcases hC with hC | ⟨e, e', h1, h2, rfl⟩
    · rcases cnfSystem_graphPHP_cases G (Or.inr ⟨C, hC, rfl⟩) with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · refine Or.inr (Or.inr (Or.inr ⟨e, e', h1, h2, ?_⟩))
      have hne : ((e, false) : Literal (GEdge G)) ≠ (e', false) := by
        intro h
        exact h2 (by rw [(Prod.mk.inj h).1])
      rw [clausePoly, Finset.prod_pair hne]
      simp

noncomputable def funNF_zeroOut (Q : Finset (Fin m)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 ∈ Q then X e else 0

theorem funNF_zeroOut_monomial (Q : Finset (Fin m)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (funNF_zeroOut G Q) (monomial b c)
      = if monoPigeons G b ⊆ Q then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, funNF_zeroOut G Q e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [funNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxQ⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [funNF_zeroOut, ite_eq_right hxQ, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem funNF_zeroOut_mem {S Q : Finset (Fin m)} (hQ : S ⊆ Q)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ funLocIdeal G S) :
    bind₁ (funNF_zeroOut G Q) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have key : ∀ e e' : GEdge G, α e * α e' = 0 →
      eval α (funNF_zeroOut G Q e) * eval α (funNF_zeroOut G Q e') = 0 := by
    intro e e' h0
    by_cases h : e.1.1 ∈ Q
    · by_cases h' : e'.1.1 ∈ Q
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact h0
      · rw [funNF_zeroOut, funNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [funNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    exact key e e' (hα.1.1 e e' h1 h2)
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.1.2 i hi
    have hmem : e.1.1 ∈ Q := by
      rw [he]
      exact hQ hi
    refine ⟨e, he, ?_⟩
    show eval α (funNF_zeroOut G Q e) = 1
    rw [funNF_zeroOut, ite_eq_left hmem, eval_X, h1]
  · intro e e' h1 h2
    exact key e e' (hα.2 e e' h1 h2)

theorem funNF_zeroOut_eq (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (funNF_zeroOut G Q) r
      = ∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => funNF_zeroOut_monomial G Q b _

theorem funNF_support_sum_filter (Q : Finset (Fin m)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoPigeons G b ⊆ Q),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoPigeons G b ⊆ Q) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc

theorem nf_funLocIdeal_pigeons (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support,
      monoPigeons G b ⊆ monoPigeons G a ∪ S := by
  have hsub := funNF_support_sum_filter G (monoPigeons G a ∪ S)
    (nf (funLocIdeal G S) (monomial a 1))
  have heq : nf (funLocIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
          (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
          monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (funLocIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (funLocIdeal G S) (monomial a 1) b
        (Finset.mem_filter.mp (hsub hb)).1
    · have h := funNF_zeroOut_mem G (S := S) (Q := monoPigeons G a ∪ S)
        Finset.subset_union_right (nf_sub_mem (funLocIdeal G S) (monomial a 1))
      rw [map_sub, funNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        funNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (funLocIdeal G S) (monomial a 1)).support.filter
      (fun b => monoPigeons G b ⊆ monoPigeons G a ∪ S),
      monomial b ((nf (funLocIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2

noncomputable def funNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else X e)

theorem funNF_override_monomial_of_notMem {p : Fin m} {j : Fin N} {b : GEdge G →₀ ℕ}
    (hp : p ∉ monoPigeons G b) (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (funNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, funNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne1 : e.1.1 ≠ p := fun h => hp (h ▸ Finset.mem_image_of_mem _ he)
    have hne2 : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [funNF_override, ite_eq_right hne1, ite_eq_right hne2]
  rw [hprod, monomial_eq]
  rfl

theorem funNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hp : p ∉ S)
    (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ funLocIdeal G (insert p S)) :
    bind₁ (funNF_override G p j) f ∈ funLocIdeal G S := by
  rw [mem_funLocIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  have hval : ∀ e : GEdge G, eval α (funNF_override G p j e)
      = if e.1.1 = p then (if e.1.2 = j then 1 else 0) else (if e.1.2 = j then 0 else α e) := by
    intro e
    rw [funNF_override]
    split_ifs <;> simp
  refine hf _ ⟨⟨?_, ?_⟩, ?_⟩
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hj1 : e.1.2 = j
    · have hj2 : e'.1.2 = j := h1.symm.trans hj1
      by_cases hp1 : e.1.1 = p
      · have hp2 : ¬ e'.1.1 = p := fun h3 => h2 (hp1.trans h3.symm)
        rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
    · have hj2 : ¬ e'.1.2 = j := fun h3 => hj1 (h1.trans h3)
      by_cases hp1 : e.1.1 = p
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
      · by_cases hp2 : e'.1.1 = p
        · rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.1.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (funNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [hval, ite_eq_left rfl, ite_eq_left rfl]
    · obtain ⟨e, he, h1⟩ := hα.1.2 i h
      have hne1 : ¬ e.1.1 = p := by
        intro h3
        rw [he] at h3
        exact hp (h3 ▸ h)
      have hne2 : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (funNF_override G p j e) = 1
      rw [hval, ite_eq_right hne1, ite_eq_right hne2, h1]
  · intro e e' h1 h2
    show eval α (funNF_override G p j e) * eval α (funNF_override G p j e') = 0
    by_cases hp1 : e.1.1 = p
    · have hp2 : e'.1.1 = p := h1.symm.trans hp1
      by_cases hj1 : e.1.2 = j
      · have hj2 : ¬ e'.1.2 = j := fun h3 => h2 (hj1.trans h3.symm)
        rw [hval e', ite_eq_left hp2, ite_eq_right hj2, mul_zero]
      · rw [hval e, ite_eq_left hp1, ite_eq_right hj1, zero_mul]
    · have hp2 : ¬ e'.1.1 = p := fun h3 => hp1 (h1.trans h3)
      by_cases hj1 : e.1.2 = j
      · rw [hval e, ite_eq_right hp1, ite_eq_left hj1, zero_mul]
      · by_cases hj2 : e'.1.2 = j
        · rw [hval e', ite_eq_right hp2, ite_eq_left hj2, mul_zero]
        · rw [hval e, hval e', ite_eq_right hp1, ite_eq_right hj1, ite_eq_right hp2,
            ite_eq_right hj2]
          exact hα.2 e e' h1 h2

theorem funNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (funNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (funNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, (e.1.1 = p ∧ ¬ e.1.2 = j) ∨ (¬ e.1.1 = p ∧ e.1.2 = j)
  · obtain ⟨e, he, h⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [funNF_override, ite_eq_left h1, ite_eq_right h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
    · rw [funNF_override, ite_eq_right h1, ite_eq_left h2,
        zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz1 : ∀ e ∈ c.support, e.1.1 = p → e.1.2 = j := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inl ⟨h, h2⟩⟩
    have hz2 : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, Or.inr ⟨h2, h⟩⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), funNF_override, ite_eq_left (hz2 e he h),
        ite_eq_left h, one_pow]
    · have hne : ¬ e.1.1 = p := fun h3 => h (hz1 e he h3)
      rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        funNF_override, ite_eq_right hne, ite_eq_right h]

theorem funNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (funNF_override G p j) w
      ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b} := by
  rw [localNF_map_eq_sum]
  refine Submodule.sum_mem _ fun c hc => ?_
  have hcb : MonoLt c b :=
    (show (↑w.support : Set (GEdge G →₀ ℕ)) ⊆ {d | MonoLt d b} from hw) (Finset.mem_coe.mpr hc)
  have hsm : monomial c (w.coeff c)
      = w.coeff c • (monomial c 1 : MvPolynomial (GEdge G) (ZMod 2)) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rcases funNF_override_monomial_one G p j c with h | h
  · rw [h]
    exact Submodule.zero_mem _
  · rw [h]
    refine (show (↑(monomial (localNF_drop G j c) (1 : ZMod 2)).support : Set (GEdge G →₀ ℕ))
      ⊆ {d | MonoLt d b} from ?_)
    intro d hd
    have hd' : d = localNF_drop G j c :=
      Finset.mem_singleton.mp (support_monomial_subset (Finset.mem_coe.mp hd))
    rw [hd']
    show MonoLt (localNF_drop G j c) b
    rcases localNF_drop_eq_or_degree_lt G j c with h' | h'
    · rw [h']
      exact hcb
    · exact monoLt_of_degree_lt (lt_of_lt_of_le h' (degree_le_of_monoLt hcb))

theorem nf_funLocIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoNbrs G a) :
    nf (funLocIdeal G (insert p S)) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  refine nf_unique (funLocIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (funLocIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hloc := nf_funLocIdeal_pigeons G S a b hb
    have hbp : p ∉ monoPigeons G b := by
      intro h
      rcases Finset.mem_union.mp (hloc h) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨p, h', hj⟩)
      · exact hp h'
    have hbj : j ∉ monoHoles G b := by
      intro h
      obtain ⟨e, he, hej⟩ := Finset.mem_image.mp h
      have hje : j ∈ G e.1.1 := by
        rw [← hej]
        exact e.2
      rcases Finset.mem_union.mp (hloc (Finset.mem_image_of_mem _ he)) with h' | h'
      · exact ha (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
      · exact hjS (Finset.mem_biUnion.mpr ⟨e.1.1, h', hje⟩)
    have himg := congrArg (bind₁ (funNF_override G p j)) huw
    rw [map_add, funNF_override_monomial_of_notMem G hbp hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (funNF_override_mem G hp hj hjS hu)
      (funNF_override_mem_restrictSupport G p j hw)
  · exact funLocIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (funLocIdeal G S) (monomial a 1))

theorem nf_funLocIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoNbrs G a ⊆ K) :
    nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (funLocIdeal G T) (monomial a 1) = nf (funLocIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_funLocIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

noncomputable def funPseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1))

theorem funPseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (funLocIdeal G (supp G s (monoNbrs G a))) (monomial a 1)) a
  simpa only [funPseudoR, coe_basisMonomials] using h

theorem monoNbrs_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, G e.1.1 ⊆ K) : ∀ a ∈ f.support, monoNbrs G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨i, hi, hji⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩) hji

theorem funPseudoR_monomial_eq_nf {s B : ℕ} (hG : IsBdryExpander G s 2) (hB : B ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ B) {a : GEdge G →₀ ℕ}
    (ha : (monoNbrs G a).card ≤ B)
    (haK : monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s (monomial a 1) = nf (funLocIdeal G (supp G s K)) (monomial a 1) := by
  rw [funPseudoR_monomial]
  have hH : (monoNbrs G a).card ≤ s := ha.trans hB
  have hKs : K.card ≤ s := hK.trans hB
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoNbrs G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoNbrs G a)) (supp G s K)
    omega
  have e1 := nf_funLocIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoNbrs G a))
  have e2 := nf_funLocIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoNbrs G a))
  exact e1.symm.trans e2

theorem funPseudoR_eq_nf_of_monomials {s : ℕ}
    (U : Submodule (ZMod 2) (MvPolynomial (GEdge G) (ZMod 2)))
    {f : MvPolynomial (GEdge G) (ZMod 2)}
    (h : ∀ a ∈ f.support, funPseudoR G s (monomial a 1) = nf U (monomial a 1)) :
    funPseudoR G s f = nf U f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (funPseudoR G s), e (nf U)]
  exact Finset.sum_congr rfl fun a ha => by rw [h a ha]

theorem funPseudoR_eq_nf {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) {K : Finset (Fin N)} (hK : K.card ≤ d * D)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K ∪ (supp G s K).biUnion G) :
    funPseudoR G s f = nf (funLocIdeal G (supp G s K)) f :=
  funPseudoR_eq_nf_of_monomials G _ fun a ha =>
    funPseudoR_monomial_eq_nf G hG hB hK
      ((card_monoNbrs_le G hd a).trans
        (Nat.mul_le_mul_left d ((le_totalDegree ha).trans hf))) (hfK a ha)

theorem funPseudoR_mul {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hB : d * D ≤ s) (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    funPseudoR G s (X v * monomial a 1)
      = funPseudoR G s (X v * funPseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoNbrs G (a + Finsupp.single v 1)).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hKa : (monoNbrs G a).card ≤ d * D :=
    (card_monoNbrs_le G hd _).trans (Nat.mul_le_mul_left d (by omega))
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoNbrs G a ⊆ monoNbrs G (a + Finsupp.single v 1) := by
    rw [monoNbrs_add_single]
    exact Finset.subset_union_left
  have e1 : funPseudoR G s (monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1)))) (monomial a 1) :=
    funPseudoR_monomial_eq_nf G hG hB hK0 hKa (haK0.trans Finset.subset_union_left)
  have e2 : funPseudoR G s (X v * monomial a 1)
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact funPseudoR_monomial_eq_nf G hG hB hK0 hK0 Finset.subset_union_left
  have hq : (nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : funPseudoR G s
        (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1))
      = nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine funPseudoR_eq_nf G hG hd hB hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := monoNbrs_subset_of_monoPigeons G (nf_funLocIdeal_pigeons G _ a c hc)
      rw [addRightEmbedding_apply, monoNbrs_add_single]
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
      · refine Finset.mem_union_left _ ?_
        rw [monoNbrs_add_single]
        exact Finset.mem_union_right _ hj
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))))
          (monomial a 1)
      ∈ funLocIdeal G (supp G s (monoNbrs G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_funLocIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0

theorem funPseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hfK : ∀ a ∈ f.support, monoNbrs G a ⊆ K)
    (hmem : f ∈ funLocIdeal G (supp G s K)) : funPseudoR G s f = 0 := by
  rw [funPseudoR_eq_nf_of_monomials G (funLocIdeal G (supp G s K)) fun a ha =>
    funPseudoR_monomial_eq_nf G hG le_rfl hK ((Finset.card_le_card (hfK a ha)).trans hK)
      ((hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

theorem totalDegree_X_mul_X (e e' : GEdge G) :
    (X e * X e' : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
  have h : (X e * X e' : MvPolynomial (GEdge G) (ZMod 2))
      = monomial (Finsupp.single e 1 + Finsupp.single e' 1) 1 := by
    have hX : (X e : MvPolynomial (GEdge G) (ZMod 2)) = monomial (Finsupp.single e 1) 1 := rfl
    rw [hX, monomial_one_mul_X]
  rw [h, totalDegree_monomial_one, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem funPseudoR_axiom {s d D : ℕ} (hG : IsBdryExpander G s 2) (hd : LeftDegLe G d)
    (hs : 1 ≤ s) (hB : d * D ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ cnfSystem (funGraphPHP G)) (hdeg : f.totalDegree ≤ D) : funPseudoR G s f = 0 := by
  have hcard : ∀ i, 1 ≤ D → (G i).card ≤ d * D := fun i hD =>
    (hd i).trans (Nat.le_mul_of_pos_right d hD)
  rcases cnfSystem_funGraphPHP_cases G hf with
    ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · have h2 : (X v * X v + X v : MvPolynomial (GEdge G) (ZMod 2)).totalDegree = 2 := by
      rw [totalDegree_add_eq_left_of_totalDegree_lt, totalDegree_X_mul_X]
      rw [totalDegree_X_mul_X, totalDegree_X]
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G v.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (bool_mem_locIdeal G _ v))
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
  · have hi : (G i).card ≤ D := by
      rw [← totalDegree_pigeonClause G i]
      exact hdeg
    have hi' : (G i).card ≤ s := by
      rcases Nat.eq_zero_or_pos D with h0 | h0
      · omega
      · exact (hcard i h0).trans hB
    exact funPseudoR_eq_zero_of_mem G hG (K := G i) hi' (monoNbrs_pigeonClause G i)
      (locIdeal_le_funLocIdeal G _
        (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _))))
  · rw [totalDegree_X_mul_X] at hdeg
    have hK : (G e.1.1 ∪ G e'.1.1).card ≤ s := by
      have h3 := Finset.card_union_le (G e.1.1) (G e'.1.1)
      have h4 := hd e.1.1
      have h5 := hd e'.1.1
      have h6 : d * 2 ≤ d * D := Nat.mul_le_mul_left d hdeg
      omega
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1 ∪ G e'.1.1) hK
      (monoNbrs_subset_of_vars G ?_)
      (locIdeal_le_funLocIdeal G _ (hole_mem_locIdeal G _ h1 h2))
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_left
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.subset_union_right
  · rw [totalDegree_X_mul_X] at hdeg
    refine funPseudoR_eq_zero_of_mem G hG (K := G e.1.1) ((hcard _ (by omega)).trans hB)
      (monoNbrs_subset_of_vars G ?_) (fun_mem_funLocIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]

theorem funPseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : funPseudoR G s 1 ≠ 0 := by
  have hm : monoNbrs G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoNbrs monoPigeons
    rw [Finsupp.support_zero, Finset.image_empty, Finset.biUnion_empty]
  have h0 : supp G s (monoNbrs G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : funPseudoR G s 1 = nf (funLocIdeal G ∅) 1 := by
    have h := funPseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_funLocIdeal_empty G ((nf_eq_zero_iff _ _).mp h)

theorem funGraphPHP_no_pc_refutation {s d D : ℕ} (hG : IsBdryExpander G s 2)
    (hd : LeftDegLe G d) (hs : 1 ≤ s) (hB : d * D ≤ s) :
    ¬ PCRefutable (cnfSystem (funGraphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (funPseudoR G s)
    (fun _ hf hdeg => funPseudoR_axiom G hG hd hs hB hf hdeg)
    (fun v a ha => funPseudoR_mul G hG hd hB v a ha)
    (funPseudoR_one G hG)

end GraphSec

end FunPHPBase

namespace Tool411

open MvPolynomial PEqualNP.ProofComplexity

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

theorem pcDerivable_mono {σ : Type} {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

theorem pcDerivable_monomial_mul {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

theorem pcDerivable_sum {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem pcDerivable_mul_left {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

theorem degree_product {V ι : Type} (S : Finset ι) (p : ι → Poly V) :
    (∏ i ∈ S, p i).totalDegree ≤ ∑ i ∈ S, (p i).totalDegree := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

theorem with_factor {V : Type} {A F : Set (Poly V)} {d B : ℕ}
    (q : Poly V) (hq : q.totalDegree + d ≤ B)
    (base : ∀ p ∈ A, p.totalDegree ≤ d → PCDerivable F B (q * p))
    {p : Poly V} (h : PCDerivable A d p) : PCDerivable F B (q * p) := by
  induction h with
  | ax hp hd => exact base _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable F B 0)
  | add _ _ ih₁ ih₂ =>
    rw [mul_add]
    exact .add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [mul_left_comm q (X j)]
    apply PCDerivable.mulX j ih
    rw [← mul_left_comm q (X j)]
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add_left hd _).trans hq)

private theorem pcDerivable_eval_eq_zero {σ : Type} {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

private noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

private noncomputable def mlin {σ : Type} (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

private theorem mlin_apply {σ : Type} (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

private theorem boolDerivable_monomial {σ : Type} (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this

private theorem eq_zero_of_multilinear {σ : Type} (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]

theorem vanish_derivable (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ)
    (p : MvPolynomial σ (ZMod 2))
    (hF : ∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hd : p.totalDegree ≤ d) (hvan : ∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) :
    PCDerivable F d p := by
  classical
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v

def face {V : Type} [Fintype V] [DecidableEq V] (U : Finset V) (seed : V → ZMod 2) :
    Finset (V → ZMod 2) := Finset.univ.filter fun y => ∀ v ∉ U, y v = seed v

def faceMonomial {V : Type} (S : Finset V) (y : V → ZMod 2) : ZMod 2 := ∏ v ∈ S, y v

def faceEval {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → ZMod 2)
    (y : V → ZMod 2) : ZMod 2 := ∑ S : Finset V, coeff S * faceMonomial S y

private theorem binary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide +kernel

private theorem face_prod {V : Type} [Fintype V] [DecidableEq V]
    (U S : Finset V) (seed : V → ZMod 2) :
    (∑ y ∈ face U seed, faceMonomial S y) =
      ∏ v : V, ∑ a ∈ (if v ∈ U then Finset.univ else {seed v}), if v ∈ S then a else 1 := by
  let allowed (v : V) : Finset (ZMod 2) := if v ∈ U then Finset.univ else {seed v}
  have hf : face U seed = Fintype.piFinset allowed := by
    ext y
    simp only [face, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hy v
      by_cases hv : v ∈ U
      · simp [allowed, hv]
      · simp [allowed, hv, hy v hv]
    · intro hy v hv
      simpa [allowed, hv] using hy v
  rw [hf, Finset.prod_univ_sum]
  simp [faceMonomial, allowed]

private theorem face_vanishes {V : Type} [Fintype V] [DecidableEq V]
    (U S : Finset V) (seed : V → ZMod 2) (h : ¬ U ⊆ S) :
    (∑ y ∈ face U seed, faceMonomial S y) = 0 := by
  obtain ⟨v, hv, hs⟩ := Finset.not_subset.mp h
  rw [face_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  have ht : (∑ _ : ZMod 2, (1 : ZMod 2)) = 0 := by decide +kernel
  simpa [hv, hs] using ht

private theorem face_top {V : Type} [Fintype V] [DecidableEq V]
    (U : Finset V) (seed : V → ZMod 2) : (∑ y ∈ face U seed, faceMonomial U y) = 1 := by
  rw [face_prod]
  apply Finset.prod_eq_one
  intro v _
  by_cases hv : v ∈ U
  · have ht : (∑ a : ZMod 2, a) = 1 := by decide +kernel
    simpa [hv] using ht
  · simp [hv]

private theorem face_sum {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → ZMod 2)
    (U : Finset V) (hU : coeff U ≠ 0) (hmax : ∀ S, coeff S ≠ 0 → S.card ≤ U.card)
    (seed : V → ZMod 2) : (∑ y ∈ face U seed, faceEval coeff y) = 1 := by
  unfold faceEval
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single U]
  · rw [face_top, (binary _).resolve_left hU, mul_one]
  · intro S _ hSU
    by_cases hc : coeff S = 0
    · rw [hc, zero_mul]
    · have sub : ¬ U ⊆ S := fun hs => hSU (Finset.eq_of_subset_of_card_le hs (hmax S hc)).symm
      rw [face_vanishes U S seed sub, mul_zero]
  · simp

private theorem odd_of_face_sum {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → ZMod 2)
    (U : Finset V) (seed : V → ZMod 2) (h : (∑ y ∈ face U seed, faceEval coeff y) = 1) :
    Odd (((face U seed).filter fun y => faceEval coeff y = 1).card) := by
  have heq : (((face U seed).filter fun y => faceEval coeff y = 1).card : ZMod 2) =
      ∑ y ∈ face U seed, faceEval coeff y := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    rcases binary (faceEval coeff y) with he | he <;> simp [he]
  exact ZMod.natCast_eq_one_iff_odd.mp (heq.trans h)

theorem odd_face {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → ZMod 2)
    (h : ∃ S, coeff S ≠ 0) : ∃ U, coeff U ≠ 0 ∧
      (∀ S, coeff S ≠ 0 → S.card ≤ U.card) ∧
      ∀ seed, Odd (((face U seed).filter fun y => faceEval coeff y = 1).card) := by
  let support := Finset.univ.filter fun S => coeff S ≠ 0
  have nonempty : support.Nonempty := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, by simp [support, hS]⟩
  obtain ⟨U, hU, hmax⟩ := Finset.exists_max_image support Finset.card nonempty
  have hn : coeff U ≠ 0 := by simpa [support] using hU
  have hb (S : Finset V) (hS : coeff S ≠ 0) : S.card ≤ U.card :=
    hmax S (by simp [support, hS])
  exact ⟨U, hn, hb, fun seed => odd_of_face_sum coeff U seed (face_sum coeff U hn hb seed)⟩

private theorem substitution_degree {σ τ : Type} (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)

theorem affine_pullback {V : Type} [Fintype V] [DecidableEq V] (q : MvPolynomial V (ZMod 2))
    (L : (V → ZMod 2) ≃ₗ[ZMod 2] (V → ZMod 2)) (a : V → ZMod 2) :
    ∃ p : MvPolynomial V (ZMod 2), p.totalDegree ≤ q.totalDegree ∧
      ∀ y : V → ZMod 2, MvPolynomial.eval y p = MvPolynomial.eval (a + L y) q := by
  let b := Pi.basisFun (ZMod 2) V
  let φ := fun v : V => C (a v) + ∑ u : V, C (L (b u) v) * X u
  have hφ (v : V) : (φ v).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    rw [totalDegree_C, zero_max]
    refine totalDegree_finsetSum_le fun u _ => ?_
    exact (totalDegree_mul _ _).trans (by simp)
  refine ⟨bind₁ φ q, by simpa only [one_mul] using substitution_degree φ hφ q, ?_⟩
  intro y
  have sy (v : V) : ∑ u : V, L (b u) v * y u = L y v := by
    have h := congrFun (congrArg L (b.sum_equivFun y)) v
    simpa [map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, Pi.basisFun_equivFun,
      mul_comm] using h
  have ey (v : V) : MvPolynomial.eval y (φ v) = (a + L y) v := by
    simp [φ, map_sum, sy]
  change aeval y (bind₁ φ q) = aeval (a + L y) q
  have he : (fun v => aeval y (φ v)) = a + L y := funext ey
  rw [aeval_bind₁, he]

noncomputable def coeffs {V : Type} [DecidableEq V] (p : MvPolynomial V (ZMod 2))
    (S : Finset V) : ZMod 2 :=
  ∑ a ∈ p.support.filter (fun a => a.support = S), p.coeff a

theorem coeff_degree {V : Type} [DecidableEq V] (p : MvPolynomial V (ZMod 2)) {S : Finset V}
    (hne : coeffs p S ≠ 0) : S.card ≤ p.totalDegree := by
  have hraw : (p.support.filter (fun a => a.support = S)).Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    apply hne
    rw [coeffs, he, Finset.sum_empty]
  obtain ⟨a, ha⟩ := hraw
  obtain ⟨hin, hS⟩ := Finset.mem_filter.mp ha
  rw [← hS]
  calc
    a.support.card = ∑ i ∈ a.support, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ a.support, a i := Finset.sum_le_sum fun i hi =>
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    _ ≤ p.totalDegree := le_totalDegree hin

private theorem pow_eq_self {x : ZMod 2} {n : ℕ} (hn : n ≠ 0) : x ^ n = x := by
  rcases binary x with rfl | rfl
  · exact zero_pow hn
  · exact one_pow n

theorem eval_coeffs {V : Type} [Fintype V] [DecidableEq V] (p : MvPolynomial V (ZMod 2))
    (x : V → ZMod 2) : faceEval (coeffs p) x = MvPolynomial.eval x p := by
  classical
  unfold faceEval coeffs
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ S : Finset V, ∑ a ∈ p.support.filter (fun a => a.support = S),
        p.coeff a * faceMonomial a.support x := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a ∈ p.support, p.coeff a * faceMonomial a.support x :=
      Finset.sum_fiberwise p.support Finsupp.support _
    _ = _ := by
      conv_rhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [eval_monomial]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (pow_eq_self (Finsupp.mem_support_iff.mp hi)).symm

theorem odd_affine_face {V : Type} [Fintype V] [DecidableEq V]
    (q : MvPolynomial V (ZMod 2)) (hv : ∃ v : V → ZMod 2, eval v q ≠ 0)
    (L : (V → ZMod 2) ≃ₗ[ZMod 2] (V → ZMod 2)) (z : V → ZMod 2) :
    ∃ U : Finset V, U.card ≤ q.totalDegree ∧
      ∀ x : V → ZMod 2, Odd ((Finset.univ.filter (fun y : V → ZMod 2 =>
        (∀ v, v ∉ U → y v = x v) ∧ eval (z + L y) q = 1)).card) := by
  obtain ⟨v, hv⟩ := hv
  obtain ⟨r, hd, eval_r⟩ := affine_pullback q L z
  have nonzero : ∃ S, coeffs r S ≠ 0 := by
    by_contra h
    let y := L.symm (v - z)
    have hy : z + L y = v := by
      rw [show L y = v - z from L.apply_symm_apply _, add_comm, sub_add_cancel]
    have zero (S : Finset V) : coeffs r S = 0 :=
      not_ne_iff.mp (not_exists.mp h S)
    have h0 : faceEval (coeffs r) y = 0 := by simp [faceEval, zero]
    rw [eval_coeffs, eval_r, hy] at h0
    exact hv h0
  obtain ⟨U, hU, _, hOdd⟩ := odd_face (coeffs r) nonzero
  refine ⟨U, (coeff_degree r hU).trans hd, ?_⟩
  intro x
  simpa only [face, Finset.filter_filter, eval_coeffs, eval_r] using hOdd x

end Tool411

namespace Half1

open MvPolynomial PEqualNP.ProofComplexity Tool411

theorem resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool} {C₁ C₂ R : Clause V}
    (hres : IsResolvent C₁ C₂ R) (h1 : ClauseSat a C₁) (h2 : ClauseSat a C₂) :
    ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := hres
  obtain ⟨l₁, hl₁, ha₁⟩ := h1
  obtain ⟨l₂, hl₂, ha₂⟩ := h2
  cases hv : a v
  · refine ⟨l₁, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hl₁⟩), ha₁⟩
    intro heq
    rw [heq] at ha₁
    simp [hv] at ha₁
  · refine ⟨l₂, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl₂⟩), ha₂⟩
    intro heq
    rw [heq] at ha₂
    simp [hv] at ha₂

theorem zmod2_id_four {V : Type} (p₁ p₂ pR : Poly V) :
    (1 + p₁) * (1 + p₂) * pR + p₁ * pR + p₂ * pR + p₁ * (p₂ * pR) = pR := by
  have h2 : ∀ z : Poly V, z + z = 0 := by
    intro z
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hexp : (1 + p₁) * (1 + p₂) * pR + p₁ * pR + p₂ * pR + p₁ * (p₂ * pR) =
      pR + (p₁ * pR + p₁ * pR) + (p₂ * pR + p₂ * pR) + (p₁ * (p₂ * pR) + p₁ * (p₂ * pR)) := by
    ring
  rw [hexp, h2, h2, h2, add_zero, add_zero, add_zero]

theorem sharp_product_induction {V : Type} (F : Set (Poly V)) :
    ∀ (m : ℕ) (E : Fin m → Set (Poly V)) (cm : Fin m → ℕ) (B_tot D_PC : ℕ)
      (_hEdeg : ∀ j, ∀ e ∈ E j, e.totalDegree ≤ cm j)
      (_hRef : ∀ j, PCRefutable (F ∪ E j) (3 * cm j))
      (_hD : 3 * B_tot ≤ D_PC)
      (q₀ : Poly V)
      (_hq : q₀.totalDegree + ∑ j, cm j ≤ B_tot)
      (_hbase : ∀ e : Fin m → Poly V, (∀ j, e j ∈ E j) →
        PCDerivable F D_PC (q₀ * ∏ j, e j)),
      PCDerivable F D_PC q₀ := by
  intro m
  induction m with
  | zero =>
    intro E cm B_tot D_PC _ _ _ q₀ _ hbase
    simpa using hbase Fin.elim0 (fun j => Fin.elim0 j)
  | succ m ih =>
    intro E cm B_tot D_PC hEdeg hRef hD q₀ hq hbase
    rw [Fin.sum_univ_succ] at hq
    have hq0 : q₀.totalDegree + 3 * cm 0 ≤ D_PC := by omega
    have hstep := with_factor q₀ hq0 (F := F) (by
      intro a ha ha_deg
      rcases ha with haF | haE
      · have hd1 := pcDerivable_mul_left (PCDerivable.ax haF ha_deg) q₀
        exact pcDerivable_mono hd1 (max_le (by omega) (by omega)) subset_rfl
      · have ha_c : a.totalDegree ≤ cm 0 := hEdeg 0 a haE
        have hqa : (q₀ * a).totalDegree + ∑ i : Fin m, cm i.succ ≤ B_tot := by
          have := totalDegree_mul q₀ a
          omega
        exact ih (fun i => E i.succ) (fun i => cm i.succ) B_tot D_PC
          (fun i => hEdeg i.succ) (fun i => hRef i.succ) hD (q₀ * a) hqa (by
            intro e he
            let full : Fin (m + 1) → Poly V := Fin.cons a e
            have hfull : ∀ j : Fin (m + 1), full j ∈ E j := by
              intro j
              refine Fin.cases ?_ (fun i => ?_) j
              · simpa [full] using haE
              · simpa [full] using he i
            simpa only [full, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← mul_assoc]
              using hbase full hfull)) (hRef 0)
    simpa only [mul_one] using hstep

def badMenu {V : Type} {t a h : ℕ} (menu : Fin t → Fin h → Bool)
    (j : Fin t) (cl : Clause ((V ⊕ Fin a) ⊕ Fin h)) : Prop :=
  ∃ i : Fin h, ((Sum.inr i : (V ⊕ Fin a) ⊕ Fin h), menu j i) ∈ cl

noncomputable def litPolyW {V : Type} {t a h : ℕ}
    (P : Fin t → Fin a → Poly V) (j : Fin t)
    (l : Literal ((V ⊕ Fin a) ⊕ Fin h)) : Poly V :=
  match l with
  | (Sum.inl (Sum.inl v), b) => if b = true then 1 + X v else X v
  | (Sum.inl (Sum.inr i), b) => if b = true then 1 + P j i else P j i
  | (Sum.inr _, _) => 1

noncomputable def linePoly {V : Type} {t a h : ℕ}
    (P : Fin t → Fin a → Poly V) (menu : Fin t → Fin h → Bool)
    (j : Fin t) (cl : Clause ((V ⊕ Fin a) ⊕ Fin h)) : Poly V := by
  classical
  exact if badMenu menu j cl then 0 else
    ∏ l ∈ cl.filter (fun l => l.1.isLeft), litPolyW P j l

theorem litPolyW_deg {V : Type} {t a h : ℕ} {d : Fin t → ℕ}
    (P : Fin t → Fin a → Poly V)
    (hd : ∀ j, 1 ≤ d j) (hP : ∀ j i, (P j i).totalDegree ≤ 1 * d j)
    (j : Fin t) (l : Literal ((V ⊕ Fin a) ⊕ Fin h)) :
    (litPolyW P j l).totalDegree ≤ d j := by
  rcases l with ⟨(v | i) | g, b⟩
  · simp only [litPolyW]
    split_ifs
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_one]; exact Nat.zero_le _
      · rw [totalDegree_X]; exact hd j
    · rw [totalDegree_X]; exact hd j
  · simp only [litPolyW]
    have hPi : (P j i).totalDegree ≤ d j := by simpa using hP j i
    split_ifs
    · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_one]; exact Nat.zero_le _
      · exact hPi
    · exact hPi
  · simp [litPolyW]

theorem eval_litPolyW_left {V : Type} {t a h : ℕ}
    (P : Fin t → Fin a → Poly V) (menu : Fin t → Fin h → Bool)
    (x : V → ZMod 2) (j : Fin t) (l : Literal ((V ⊕ Fin a) ⊕ Fin h))
    (hl : l.1.isLeft = true) :
    eval x (litPolyW P j l) =
      if (Sum.elim (Sum.elim (fun v => decide (x v = 1))
        (fun i => decide (eval x (P j i) = 1))) (menu j)) l.1 = l.2 then 0 else 1 := by
  rcases l with ⟨(v | i) | g, b⟩
  · simp only [litPolyW, Sum.elim_inl]
    have hx : x v = 0 ∨ x v = 1 := by
      generalize x v = c; revert c; decide
    cases b <;> rcases hx with h0 | h0 <;> simp [h0]
    · decide
  · simp only [litPolyW, Sum.elim_inl, Sum.elim_inr]
    have hx : eval x (P j i) = 0 ∨ eval x (P j i) = 1 := by
      generalize eval x (P j i) = c; revert c; decide
    cases b <;> rcases hx with h0 | h0 <;> simp [h0]
    · decide
  · simp at hl

open Classical in
theorem eval_linePoly {V : Type} {t a h : ℕ}
    (P : Fin t → Fin a → Poly V) (menu : Fin t → Fin h → Bool)
    (x : V → ZMod 2) (j : Fin t) (cl : Clause ((V ⊕ Fin a) ⊕ Fin h)) :
    eval x (linePoly P menu j cl) =
      if ClauseSat (Sum.elim (Sum.elim (fun v => decide (x v = 1))
        (fun i => decide (eval x (P j i) = 1))) (menu j)) cl then 0 else 1 := by
  classical
  let r := Sum.elim (Sum.elim (fun v => decide (x v = 1))
    (fun i => decide (eval x (P j i) = 1))) (menu j)
  show eval x (linePoly P menu j cl) = if ClauseSat r cl then 0 else 1
  unfold linePoly
  by_cases hbad : badMenu menu j cl
  · rw [if_pos hbad, map_zero]
    obtain ⟨i, hi⟩ := hbad
    have hsat : ClauseSat r cl := ⟨(Sum.inr i, menu j i), hi, rfl⟩
    rw [if_pos hsat]
  · rw [if_neg hbad, map_prod]
    by_cases hsat : ClauseSat r cl
    · rw [if_pos hsat]
      obtain ⟨l, hl, hlv⟩ := hsat
      have hleft : l.1.isLeft = true := by
        rcases l with ⟨(v | i) | g, b⟩
        · rfl
        · rfl
        · exfalso
          simp only [r, Sum.elim_inr] at hlv
          exact hbad ⟨g, hlv ▸ hl⟩
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hl, hleft⟩) ?_
      rw [eval_litPolyW_left P menu x j l hleft]
      exact if_pos hlv
    · rw [if_neg hsat]
      refine Finset.prod_eq_one fun l hl => ?_
      obtain ⟨hlc, hleft⟩ := Finset.mem_filter.mp hl
      rw [eval_litPolyW_left P menu x j l hleft]
      have hne : r l.1 ≠ l.2 := fun heq => hsat ⟨l, hlc, heq⟩
      exact if_neg hne

theorem linePoly_lift {V : Type} [DecidableEq V] {t a h : ℕ}
    (P : Fin t → Fin a → Poly V) (menu : Fin t → Fin h → Bool)
    (j : Fin t) (C₀ : Clause V) :
    linePoly P menu j (C₀.image (fun l => ((Sum.inl (Sum.inl l.1) : (V ⊕ Fin a) ⊕ Fin h), l.2))) =
      clausePoly C₀ := by
  classical
  let f : Literal V → Literal ((V ⊕ Fin a) ⊕ Fin h) :=
    fun l => ((Sum.inl (Sum.inl l.1) : (V ⊕ Fin a) ⊕ Fin h), l.2)
  have hnbad : ¬ badMenu menu j (C₀.image f) := by
    rintro ⟨i, hi⟩
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hi
    simp [f] at hl
  have hfilt : (C₀.image f).filter (fun l => l.1.isLeft) = C₀.image f := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_image, and_iff_left_iff_imp]
    rintro ⟨l₀, _, rfl⟩
    rfl
  unfold linePoly
  rw [if_neg hnbad, hfilt, Finset.prod_image]
  · unfold clausePoly
    refine Finset.prod_congr rfl fun l _ => ?_
    simp [f, litPolyW]
  · intro x _ y _ hxy
    simp only [f, Prod.mk.injEq, Sum.inl.injEq] at hxy
    exact Prod.ext hxy.1 hxy.2

theorem linePoly_empty {V : Type} {t a h : ℕ}
    (P : Fin t → Fin a → Poly V) (menu : Fin t → Fin h → Bool) (j : Fin t) :
    linePoly P menu j ∅ = 1 := by
  classical
  have hnbad : ¬ badMenu menu j (∅ : Clause ((V ⊕ Fin a) ⊕ Fin h)) := by
    rintro ⟨i, hi⟩
    simp at hi
  unfold linePoly
  rw [if_neg hnbad]
  simp

theorem half1_main {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (Clause V)) (t : ℕ) (d w : Fin t → ℕ)
    (hdw : ∀ j, 1 ≤ d j ∧ 1 ≤ w j)
    (hHard : ¬ PCRefutable (cnfSystem F) (3 * ∑ j, d j * w j))
    (a h : ℕ) (P : Fin t → Fin a → Poly V)
    (menu : Fin t → Fin h → Bool)
    (extra : Set (Clause ((V ⊕ Fin a) ⊕ Fin h)))
    (π : List (Clause ((V ⊕ Fin a) ⊕ Fin h)))
    (hPdeg : ∀ j i, (P j i).totalDegree ≤ 1 * d j)
    (hRef : IsRefutation
      (Set.image (fun cl : Clause V =>
        cl.image (fun l => ((Sum.inl (Sum.inl l.1) : (V ⊕ Fin a) ⊕ Fin h), l.2))) F ∪ extra) π)
    (hWidth : ∀ j cl, cl ∈ π →
      (∃ i : Fin h, ((Sum.inr i : (V ⊕ Fin a) ⊕ Fin h), menu j i) ∈ cl) ∨
      (cl.filter (fun l => l.1.isLeft)).card ≤ 1 * w j) :
    ∃ cl : Fin t → Clause ((V ⊕ Fin a) ⊕ Fin h),
      (∀ j, cl j ∈ extra ∧ cl j ∈ π) ∧
      ∀ (L : (V → ZMod 2) ≃ₗ[ZMod 2] (V → ZMod 2)) (z : V → ZMod 2),
        ∃ U : Finset V, U.card ≤ ∑ j, d j * w j ∧
          ∀ x : V → ZMod 2, Odd ((Finset.univ.filter (fun y : V → ZMod 2 =>
            @decide ((∀ v, v ∉ U → y v = x v) ∧ ∀ j,
              ¬ ClauseSat (Sum.elim (Sum.elim (fun v => decide ((z + L y) v = 1))
                (fun i => decide (eval (z + L y) (P j i) = 1))) (menu j)) (cl j))
              (Classical.propDecidable _))).card) := by
  classical
  let W := (V ⊕ Fin a) ⊕ Fin h
  let lift : Clause V → Clause W :=
    fun cl => cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W), l.2))
  let c : Fin t → ℕ := fun j => d j * w j
  let B : ℕ := ∑ j, c j
  let E_poly : Fin t → Set (Poly V) :=
    fun j => {p | ∃ cl, cl ∈ extra ∧ cl ∈ π ∧ p = linePoly P menu j cl}
  have hlineDeg : ∀ j cl, cl ∈ π → (linePoly P menu j cl).totalDegree ≤ c j := by
    intro j cl hcl
    unfold linePoly
    by_cases hbad : badMenu menu j cl
    · rw [if_pos hbad, totalDegree_zero]
      exact Nat.zero_le _
    · rw [if_neg hbad]
      have hw : (cl.filter (fun l => l.1.isLeft)).card ≤ w j := by
        rcases hWidth j cl hcl with h1 | h2
        · exact absurd h1 hbad
        · simpa using h2
      calc (∏ l ∈ cl.filter (fun l => l.1.isLeft), litPolyW P j l).totalDegree
          ≤ ∑ l ∈ cl.filter (fun l => l.1.isLeft), (litPolyW P j l).totalDegree :=
            degree_product _ _
        _ ≤ ∑ _l ∈ cl.filter (fun l => l.1.isLeft), d j :=
            Finset.sum_le_sum fun l _ => litPolyW_deg P (fun k => (hdw k).1) hPdeg j l
        _ = (cl.filter (fun l => l.1.isLeft)).card * d j := by simp
        _ ≤ w j * d j := Nat.mul_le_mul_right _ hw
        _ = c j := Nat.mul_comm _ _
  have hEdeg : ∀ j, ∀ e ∈ E_poly j, e.totalDegree ≤ c j := by
    rintro j e ⟨cl, _, hclπ, rfl⟩
    exact hlineDeg j cl hclπ
  have hBranch : ∀ j, PCRefutable (cnfSystem F ∪ E_poly j) (3 * c j) := by
    intro j
    have hreplay : ∀ π' : List (Clause W), IsDerivation (Set.image lift F ∪ extra) π' →
        (∀ cl ∈ π', cl ∈ π) →
        ∀ cl ∈ π', PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j) (linePoly P menu j cl) := by
      intro π' hder
      induction hder with
      | nil =>
        intro _ cl hcl
        simp at hcl
      | ax _ hC ih =>
        intro hsub cl hcl
        rcases List.mem_cons.mp hcl with rfl | hcl0
        · have hCπ : cl ∈ π := hsub cl (List.mem_cons_self ..)
          have hdegC : (linePoly P menu j cl).totalDegree ≤ 3 * c j :=
            (hlineDeg j cl hCπ).trans (by omega)
          rcases hC with ⟨C₀, hC₀F, rfl⟩ | hCex
          · refine PCDerivable.ax (Or.inl ?_) hdegC
            rw [linePoly_lift]
            exact Or.inr ⟨C₀, hC₀F, rfl⟩
          · exact PCDerivable.ax (Or.inr ⟨cl, hCex, hCπ, rfl⟩) hdegC
        · exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) cl hcl0
      | res hder0 h1 h2 hres ih =>
        rename_i π₀ C₁ C₂ ClR
        intro hsub cl hcl
        rcases List.mem_cons.mp hcl with heq | hcl0
        · rw [heq]
          have hsub0 : ∀ x ∈ π₀, x ∈ π := fun x hx => hsub x (List.mem_cons_of_mem _ hx)
          have hp1 : PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j) (linePoly P menu j C₁) :=
            ih hsub0 C₁ h1
          have hp2 : PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j) (linePoly P menu j C₂) :=
            ih hsub0 C₂ h2
          set p₁ := linePoly P menu j C₁
          set p₂ := linePoly P menu j C₂
          set pR := linePoly P menu j ClR
          have hd1 : p₁.totalDegree ≤ c j := hlineDeg j C₁ (hsub0 C₁ h1)
          have hd2 : p₂.totalDegree ≤ c j := hlineDeg j C₂ (hsub0 C₂ h2)
          have hdR : pR.totalDegree ≤ c j := hlineDeg j ClR (hsub ClR (List.mem_cons_self ..))
          have h1p1 : (1 + p₁).totalDegree ≤ c j :=
            (totalDegree_add _ _).trans (max_le (by simp) hd1)
          have h1p2 : (1 + p₂).totalDegree ≤ c j :=
            (totalDegree_add _ _).trans (max_le (by simp) hd2)
          have hvan_deg : ((1 + p₁) * (1 + p₂) * pR).totalDegree ≤ 3 * c j := by
            have ha1 := totalDegree_mul ((1 + p₁) * (1 + p₂)) pR
            have ha2 := totalDegree_mul (1 + p₁) (1 + p₂)
            omega
          have hvan_zero : ∀ x : V → ZMod 2, eval x ((1 + p₁) * (1 + p₂) * pR) = 0 := by
            intro x
            simp only [map_mul, map_add, map_one, p₁, p₂, pR, eval_linePoly]
            by_cases hs1 : ClauseSat (Sum.elim (Sum.elim (fun v => decide (x v = 1))
                (fun i => decide (eval x (P j i) = 1))) (menu j)) C₁
            · by_cases hs2 : ClauseSat (Sum.elim (Sum.elim (fun v => decide (x v = 1))
                  (fun i => decide (eval x (P j i) = 1))) (menu j)) C₂
              · have hsR := resolvent_sound hres hs1 hs2
                simp [hs1, hs2, hsR]
              · have h20 : (1 : ZMod 2) + 1 = 0 := by decide
                simp [hs1, hs2, h20]
            · have h20 : (1 : ZMod 2) + 1 = 0 := by decide
              simp [hs1, h20]
          have hvan : PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j)
              ((1 + p₁) * (1 + p₂) * pR) :=
            vanish_derivable V (cnfSystem F ∪ E_poly j) (3 * c j) _
              (fun v => Or.inl (Or.inl ⟨v, rfl⟩)) hvan_deg hvan_zero
          have h1R : PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j) (p₁ * pR) := by
            have := pcDerivable_mul_left hp1 pR
            rw [mul_comm pR p₁] at this
            exact pcDerivable_mono this (max_le le_rfl (by omega)) subset_rfl
          have h2R : PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j) (p₂ * pR) := by
            have := pcDerivable_mul_left hp2 pR
            rw [mul_comm pR p₂] at this
            exact pcDerivable_mono this (max_le le_rfl (by omega)) subset_rfl
          have h12R : PCDerivable (cnfSystem F ∪ E_poly j) (3 * c j) (p₁ * (p₂ * pR)) := by
            have := pcDerivable_mul_left hp1 (p₂ * pR)
            rw [mul_comm (p₂ * pR) p₁] at this
            have hd2R := totalDegree_mul p₂ pR
            exact pcDerivable_mono this (max_le le_rfl (by omega)) subset_rfl
          have hsum := PCDerivable.add (PCDerivable.add (PCDerivable.add hvan h1R) h2R) h12R
          rwa [zmod2_id_four] at hsum
        · exact ih (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) cl hcl0
    have h1 := hreplay π hRef.1 (fun _ hx => hx) ∅ hRef.2
    rwa [linePoly_empty] at h1
  have hex : ∃ e : Fin t → Poly V, (∀ j, e j ∈ E_poly j) ∧
      ¬ PCDerivable (cnfSystem F) (3 * B) (∏ j, e j) := by
    by_contra hno
    apply hHard
    refine sharp_product_induction (cnfSystem F) t E_poly c B (3 * B) hEdeg hBranch le_rfl 1
      (by simp [B]) ?_
    intro e he
    rw [one_mul]
    by_contra hbad
    exact hno ⟨e, he, hbad⟩
  obtain ⟨e, he, hnotD⟩ := hex
  have hchoose : ∀ j, ∃ cl, cl ∈ extra ∧ cl ∈ π ∧ e j = linePoly P menu j cl := fun j => he j
  let cl : Fin t → Clause W := fun j => Classical.choose (hchoose j)
  have hcl : ∀ j, cl j ∈ extra ∧ cl j ∈ π ∧ e j = linePoly P menu j (cl j) :=
    fun j => Classical.choose_spec (hchoose j)
  let q_prod : Poly V := ∏ j, linePoly P menu j (cl j)
  have hq_eq : q_prod = ∏ j, e j :=
    Finset.prod_congr rfl fun j _ => (hcl j).2.2.symm
  have hq_deg : q_prod.totalDegree ≤ B :=
    (degree_product Finset.univ _).trans (Finset.sum_le_sum fun j _ => hlineDeg j (cl j) (hcl j).2.1)
  have hq_nonzero : ∃ v : V → ZMod 2, eval v q_prod ≠ 0 := by
    by_contra hno
    apply hnotD
    rw [← hq_eq]
    refine vanish_derivable V (cnfSystem F) (3 * B) q_prod
      (fun v => Or.inl ⟨v, rfl⟩) (hq_deg.trans (by omega)) ?_
    intro x
    exact not_ne_iff.mp (not_exists.mp hno x)
  refine ⟨cl, fun j => ⟨(hcl j).1, (hcl j).2.1⟩, ?_⟩
  intro L z
  obtain ⟨U, hU, hOdd⟩ := odd_affine_face q_prod hq_nonzero L z
  refine ⟨U, hU.trans hq_deg, ?_⟩
  intro x
  have hcard_eq : (Finset.univ.filter (fun y : V → ZMod 2 =>
        @decide ((∀ v, v ∉ U → y v = x v) ∧ ∀ j,
          ¬ ClauseSat (Sum.elim (Sum.elim (fun v => decide ((z + L y) v = 1))
            (fun i => decide (eval (z + L y) (P j i) = 1))) (menu j)) (cl j))
          (Classical.propDecidable _))).card =
      (Finset.univ.filter (fun y : V → ZMod 2 =>
        (∀ v, v ∉ U → y v = x v) ∧ eval (z + L y) q_prod = 1)).card := by
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    refine and_congr_right fun _ => ?_
    simp only [q_prod, map_prod, eval_linePoly]
    constructor
    · intro hall
      refine Finset.prod_eq_one fun j _ => ?_
      rw [if_neg (hall j)]
    · intro hprod j hsat
      have h0 : (∏ k : Fin t, if ClauseSat (Sum.elim (Sum.elim (fun v => decide ((z + L y) v = 1))
          (fun i => decide (eval (z + L y) (P k i) = 1))) (menu k)) (cl k) then (0 : ZMod 2) else 1)
          = 0 := Finset.prod_eq_zero (Finset.mem_univ j) (if_pos hsat)
      rw [h0] at hprod
      exact zero_ne_one hprod
  rw [hcard_eq]
  exact hOdd x

end Half1

namespace Half2

open MvPolynomial PEqualNP.Expanders PEqualNP.ProofComplexity Tool411

section MainCase

variable {n : ℕ} (G : BipGraph (n + 1) n)
variable (t : ℕ) (d w : Fin t → ℕ)

def cum (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin t => j.val < k), d j * w j

lemma cum_zero : cum t d w 0 = 0 := by
  simp [cum]

lemma cum_top : cum t d w t = ∑ j : Fin t, d j * w j := by
  unfold cum
  congr 1
  ext j
  simp [j.isLt]

lemma cum_succ (j : Fin t) : cum t d w (j.val + 1) = cum t d w j.val + d j * w j := by
  unfold cum
  have heq : Finset.univ.filter (fun j' : Fin t => j'.val < j.val + 1) =
      insert j (Finset.univ.filter (fun j' : Fin t => j'.val < j.val)) := by
    ext j'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : j ∉ Finset.univ.filter (fun j' : Fin t => j'.val < j.val) := by
    simp
  rw [heq, Finset.sum_insert hnot, add_comm]

lemma cum_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : cum t d w k₁ ≤ cum t d w k₂ := by
  unfold cum
  refine Finset.sum_le_sum_of_subset ?_
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  omega

lemma exists_bin_of_lt_cum {k m : ℕ} (hk : k ≤ t) (hm : m < cum t d w k) :
    ∃ j : Fin t, j.val < k ∧ cum t d w j.val ≤ m ∧ m < cum t d w (j.val + 1) := by
  induction k with
  | zero =>
    rw [cum_zero] at hm
    omega
  | succ k ih =>
    have hkt : k < t := by omega
    let jk : Fin t := ⟨k, hkt⟩
    by_cases hmk : m < cum t d w k
    · obtain ⟨j, hjlt, hj1, hj2⟩ := ih (by omega) hmk
      exact ⟨j, by omega, hj1, hj2⟩
    · refine ⟨jk, by simp [jk], by simp only [jk]; omega, ?_⟩
      simpa [jk] using hm

lemma bin_unique {j₁ j₂ : Fin t} {m : ℕ}
    (h1a : cum t d w j₁.val ≤ m) (h1b : m < cum t d w (j₁.val + 1))
    (h2a : cum t d w j₂.val ≤ m) (h2b : m < cum t d w (j₂.val + 1)) : j₁ = j₂ := by
  by_contra hne
  have hne' : j₁.val ≠ j₂.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · have := cum_mono t d w (k₁ := j₁.val + 1) (k₂ := j₂.val) (by omega)
    omega
  · have := cum_mono t d w (k₁ := j₂.val + 1) (k₂ := j₁.val) (by omega)
    omega

theorem half2_main
    (hLeft8 : LeftDegLe G 8)
    (hNonempty : ∀ i : Fin (n + 1), (G i).Nonempty)
    (hdw : ∀ j, 1 ≤ d j ∧ 1 ≤ w j)
    (ht : 0 < t) :
    let V := GEdge G
    let X := V → ZMod 2
    let F := funGraphPHP G
    let B := ∑ j, d j * w j
    let q := min n B
    let W := fun (a h : ℕ) => (V ⊕ Fin a) ⊕ Fin h
    let run := fun (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
        (menu : Fin t → Fin h → Bool) (x : X) (j : Fin t) =>
      Sum.elim (Sum.elim (fun v => decide (x v = 1))
        (fun i => decide (MvPolynomial.eval x (P j i) = 1))) (menu j)
    let proof := fun (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
        (menu : Fin t → Fin h → Bool) (extra : Set (Clause (W a h)))
        (π : List (Clause (W a h))) (scale : ℕ) =>
      let lift := fun cl : Clause V =>
        cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W a h), l.2))
      (∀ j i, (P j i).totalDegree ≤ scale * d j) ∧
      IsRefutation (Set.image lift F ∪ extra) π ∧
      ∀ j cl, cl ∈ π → (∃ i : Fin h, ((Sum.inr i : W a h), menu j i) ∈ cl) ∨
        (cl.filter (fun l => l.1.isLeft)).card ≤ scale * w j
    ∃ (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
        (menu : Fin t → Fin h → Bool) (extra : Finset (Clause (W a h)))
        (π : List (Clause (W a h))) (J : Finset (Fin (n + 1))),
      proof a h P menu (↑extra) π 2400000 ∧ J.card = q ∧
      a + h + extra.card + π.length ≤ 2400000 * (q + t + 1) ∧
      ∀ x : X, (∀ j, ¬ Satisfies (run a h P menu x j) (↑extra)) ↔
        ∀ i ∈ J, ∃ e : V, e.val.1 = i ∧ x e = 1 := by
  classical
  dsimp only
  let V := GEdge G
  let X := V → ZMod 2
  let F := funGraphPHP G
  let B := ∑ j, d j * w j
  let q := min n B
  let W := (V ⊕ Fin q) ⊕ Fin t
  let C : ℕ := 2400000
  have hqn : q ≤ n := Nat.min_le_left n B
  have hqB : q ≤ B := Nat.min_le_right n B
  let pigeon : Fin q → Fin (n + 1) := fun p => ⟨p.val, by omega⟩
  have hpigeon_inj : Function.Injective pigeon := by
    intro p₁ p₂ h
    exact Fin.ext (congrArg (Fin.val (n := n + 1)) h)
  let J : Finset (Fin (n + 1)) := Finset.univ.image pigeon
  have hJcard : J.card = q := by
    rw [Finset.card_image_of_injective _ hpigeon_inj, Finset.card_univ, Fintype.card_fin]
  have hbin_ex : ∀ p : Fin q,
      ∃ j : Fin t, cum t d w j.val ≤ p.val ∧ p.val < cum t d w (j.val + 1) := by
    intro p
    have hlt : p.val < cum t d w t := by rw [cum_top]; omega
    obtain ⟨j, _, h1, h2⟩ := exists_bin_of_lt_cum t d w le_rfl hlt
    exact ⟨j, h1, h2⟩
  let binOf : Fin q → Fin t := fun p => Classical.choose (hbin_ex p)
  have hbin_spec : ∀ p : Fin q,
      cum t d w (binOf p).val ≤ p.val ∧ p.val < cum t d w ((binOf p).val + 1) :=
    fun p => Classical.choose_spec (hbin_ex p)
  have hbin_eq : ∀ (p : Fin q) (j : Fin t),
      cum t d w j.val ≤ p.val → p.val < cum t d w (j.val + 1) → binOf p = j :=
    fun p j h1 h2 => bin_unique t d w (hbin_spec p).1 (hbin_spec p).2 h1 h2
  let locIdx : Fin q → ℕ := fun p => p.val - cum t d w (binOf p).val
  let batchIdx : Fin q → ℕ := fun p => locIdx p / d (binOf p)
  let posInBatch : Fin q → ℕ := fun p => locIdx p % d (binOf p)
  have hloc_lt : ∀ p : Fin q, locIdx p < d (binOf p) * w (binOf p) := by
    intro p
    have hs := hbin_spec p
    have hsc := cum_succ t d w (binOf p)
    dsimp only [locIdx]
    omega
  have hbatch_lt : ∀ p : Fin q, batchIdx p < w (binOf p) := by
    intro p
    exact Nat.div_lt_of_lt_mul (hloc_lt p)
  have hpos_lt : ∀ p : Fin q, posInBatch p < d (binOf p) := by
    intro p
    exact Nat.mod_lt _ (by have := (hdw (binOf p)).1; omega)
  have hp_decomp : ∀ p : Fin q,
      p.val = cum t d w (binOf p).val + batchIdx p * d (binOf p) + posInBatch p := by
    intro p
    have hdm := Nat.div_add_mod (locIdx p) (d (binOf p))
    have hs := (hbin_spec p).1
    have hmul : d (binOf p) * batchIdx p = batchIdx p * d (binOf p) := Nat.mul_comm _ _
    dsimp only [batchIdx, posInBatch, locIdx] at hdm hmul ⊢
    omega
  have hprev_props : ∀ (p : Fin q) (hpos : 0 < posInBatch p),
      let prevP : Fin q := ⟨p.val - 1, by omega⟩
      binOf prevP = binOf p ∧ batchIdx prevP = batchIdx p ∧ posInBatch prevP = posInBatch p - 1 := by
    intro p hpos
    dsimp only
    let prevP : Fin q := ⟨p.val - 1, by omega⟩
    have hpd := hp_decomp p
    have hs := hbin_spec p
    have hbin_prev : binOf prevP = binOf p := by
      refine hbin_eq prevP (binOf p) ?_ ?_
      · show cum t d w (binOf p).val ≤ p.val - 1
        omega
      · show p.val - 1 < cum t d w ((binOf p).val + 1)
        omega
    have hloc_prev : locIdx prevP = batchIdx p * d (binOf p) + (posInBatch p - 1) := by
      simp only [locIdx, hbin_prev, prevP]
      omega
    have hplt := hpos_lt p
    have hdpos : 0 < d (binOf p) := by have := (hdw (binOf p)).1; omega
    have hdiv : (batchIdx p * d (binOf p) + (posInBatch p - 1)) / d (binOf p) = batchIdx p := by
      rw [Nat.mul_comm, Nat.mul_add_div hdpos, Nat.div_eq_of_lt (by omega), add_zero]
    have hmod : (batchIdx p * d (binOf p) + (posInBatch p - 1)) % d (binOf p) = posInBatch p - 1 := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    refine ⟨hbin_prev, ?_, ?_⟩
    · show locIdx prevP / d (binOf prevP) = batchIdx p
      rw [hbin_prev, hloc_prev, hdiv]
    · show locIdx prevP % d (binOf prevP) = posInBatch p - 1
      rw [hbin_prev, hloc_prev, hmod]
  let chainSet : Fin q → Finset (Fin q) := fun p =>
    Finset.univ.filter (fun p' : Fin q => binOf p' = binOf p ∧ batchIdx p' = batchIdx p ∧ p'.val ≤ p.val)
  have hchain_card : ∀ p : Fin q, (chainSet p).card ≤ d (binOf p) := by
    intro p
    have hinj : Set.InjOn posInBatch (↑(chainSet p) : Set (Fin q)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      obtain ⟨hb1, hba1, _⟩ := (Finset.mem_filter.mp hp₁).2
      obtain ⟨hb2, hba2, _⟩ := (Finset.mem_filter.mp hp₂).2
      have h1 := hp_decomp p₁
      have h2 := hp_decomp p₂
      rw [hb1, hba1] at h1
      rw [hb2, hba2] at h2
      exact Fin.ext (by omega)
    have hsub : (chainSet p).image posInBatch ⊆ Finset.range (d (binOf p)) := by
      intro k hk
      obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hb, _, _⟩ := (Finset.mem_filter.mp hp').2
      rw [Finset.mem_range, ← hb]
      exact hpos_lt p'
    calc (chainSet p).card = ((chainSet p).image posInBatch).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (d (binOf p))).card := Finset.card_le_card hsub
      _ = d (binOf p) := Finset.card_range _
  have hchain_zero : ∀ p : Fin q, posInBatch p = 0 → chainSet p = {p} := by
    intro p hpos0
    ext p'
    simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, hba, hle⟩
      have h1 := hp_decomp p
      have h2 := hp_decomp p'
      rw [hb, hba] at h2
      exact Fin.ext (by omega)
    · rintro rfl
      exact ⟨rfl, rfl, le_rfl⟩
  have hchain_pos : ∀ (p : Fin q) (hpos : 0 < posInBatch p),
      chainSet p = insert p (chainSet ⟨p.val - 1, by omega⟩) := by
    intro p hpos
    have hpr := hprev_props p hpos
    ext p'
    simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      hpr.1, hpr.2.1]
    constructor
    · rintro ⟨hb, hba, hle⟩
      by_cases heq : p' = p
      · exact Or.inl heq
      · right
        have hlt : p'.val < p.val := lt_of_le_of_ne hle (fun h => heq (Fin.ext h))
        exact ⟨hb, hba, by omega⟩
    · rintro (rfl | ⟨hb, hba, hle⟩)
      · exact ⟨rfl, rfl, le_rfl⟩
      · exact ⟨hb, hba, by omega⟩
  let isTop : Fin q → Prop := fun p =>
    ∀ p' : Fin q, binOf p' = binOf p → batchIdx p' = batchIdx p → p'.val ≤ p.val
  let tops : Fin t → Finset (Fin q) := fun g =>
    Finset.univ.filter (fun p : Fin q => binOf p = g ∧ isTop p)
  have htops_card : ∀ g : Fin t, (tops g).card ≤ w g := by
    intro g
    have hinj : Set.InjOn batchIdx (↑(tops g) : Set (Fin q)) := by
      intro p₁ hp₁ p₂ hp₂ heq
      obtain ⟨hb1, ht1⟩ := (Finset.mem_filter.mp hp₁).2
      obtain ⟨hb2, ht2⟩ := (Finset.mem_filter.mp hp₂).2
      have hle1 : p₂.val ≤ p₁.val := ht1 p₂ (hb2.trans hb1.symm) heq.symm
      have hle2 : p₁.val ≤ p₂.val := ht2 p₁ (hb1.trans hb2.symm) heq
      exact Fin.ext (by omega)
    have hsub : (tops g).image batchIdx ⊆ Finset.range (w g) := by
      intro k hk
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨hb, _⟩ := (Finset.mem_filter.mp hp).2
      rw [Finset.mem_range, ← hb]
      exact hbatch_lt p
    calc (tops g).card = ((tops g).image batchIdx).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (w g)).card := Finset.card_le_card hsub
      _ = w g := Finset.card_range _
  have htops_sum_card : ∑ g : Fin t, (tops g).card ≤ q := by
    have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin t))) tops := by
      intro g₁ _ g₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact hne ((Finset.mem_filter.mp hp1).2.1.symm.trans (Finset.mem_filter.mp hp2).2.1)
    rw [← Finset.card_biUnion hdisj]
    calc (Finset.univ.biUnion tops).card ≤ (Finset.univ : Finset (Fin q)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = q := by simp
  have htops_cover : ∀ p' : Fin q, ∃ p ∈ tops (binOf p'), p' ∈ chainSet p := by
    intro p'
    let S := Finset.univ.filter (fun p : Fin q => binOf p = binOf p' ∧ batchIdx p = batchIdx p')
    have hSne : S.Nonempty := ⟨p', by simp [S]⟩
    obtain ⟨p, hpS, hpmax⟩ := Finset.exists_max_image S Fin.val hSne
    obtain ⟨hbp, hbap⟩ := (Finset.mem_filter.mp hpS).2
    refine ⟨p, ?_, ?_⟩
    · simp only [tops, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hbp, fun r hr1 hr2 => ?_⟩
      exact hpmax r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr1.trans hbp, hr2.trans hbap⟩)
    · simp only [chainSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hbp.symm, hbap.symm, hpmax p' (by simp [S])⟩
  let edgesOf : Fin (n + 1) → Finset V := fun i => Finset.univ.filter (fun e : V => e.val.1 = i)
  have hedges_card : ∀ i : Fin (n + 1), (edgesOf i).card = (G i).card := by
    intro i
    refine Finset.card_bij (fun e _ => e.val.2) ?_ ?_ ?_
    · intro e he
      have h1 : e.val.1 = i := (Finset.mem_filter.mp he).2
      have h2 := e.2
      rwa [h1] at h2
    · intro e₁ he₁ e₂ he₂ h2
      have h1a : e₁.val.1 = i := (Finset.mem_filter.mp he₁).2
      have h1b : e₂.val.1 = i := (Finset.mem_filter.mp he₂).2
      exact Subtype.ext (Prod.ext (h1a.trans h1b.symm) h2)
    · intro j hj
      exact ⟨⟨(i, j), hj⟩, by simp [edgesOf], rfl⟩
  have hedges_ne : ∀ i : Fin (n + 1), (edgesOf i).Nonempty := by
    intro i
    obtain ⟨j, hj⟩ := hNonempty i
    exact ⟨⟨(i, j), hj⟩, by simp [edgesOf]⟩
  have hedges_le8 : ∀ i : Fin (n + 1), (edgesOf i).card ≤ 8 := by
    intro i
    rw [hedges_card]
    exact hLeft8 i
  let violPoly : Fin (n + 1) → Poly V := fun i => ∏ e ∈ edgesOf i, (1 + MvPolynomial.X e)
  have hviol_deg : ∀ i : Fin (n + 1), (violPoly i).totalDegree ≤ 8 := by
    intro i
    calc (violPoly i).totalDegree
        ≤ ∑ e ∈ edgesOf i, (1 + MvPolynomial.X e : Poly V).totalDegree := degree_product _ _
      _ ≤ ∑ _e ∈ edgesOf i, 1 := Finset.sum_le_sum fun e _ =>
          (totalDegree_add _ _).trans (max_le (by simp) (by simp))
      _ = (edgesOf i).card := by simp
      _ ≤ 8 := hedges_le8 i
  have hviol_eval : ∀ (x : X) (i : Fin (n + 1)),
      eval x (violPoly i) = if (∀ e : V, e.val.1 = i → x e = 0) then 1 else 0 := by
    intro x i
    simp only [violPoly, map_prod, map_add, map_one, eval_X]
    by_cases hall : ∀ e : V, e.val.1 = i → x e = 0
    · rw [if_pos hall]
      refine Finset.prod_eq_one fun e he => ?_
      rw [hall e (Finset.mem_filter.mp he).2, add_zero]
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨e, he1, he0⟩ := hall
      have he1' : x e = 1 := by
        generalize x e = c at he0; revert he0; revert c; decide
      refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he1⟩) ?_
      rw [he1']; decide
  let P : Fin t → Fin q → Poly V := fun j p =>
    if j = binOf p then 1 + ∏ p' ∈ chainSet p, (1 + violPoly (pigeon p')) else 0
  let menu : Fin t → Fin t → Bool := fun j g => decide (j ≠ g)
  have hPdeg : ∀ j p, (P j p).totalDegree ≤ C * d j := by
    intro j p
    simp only [P]
    split_ifs with hj
    · subst hj
      refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
      calc (∏ p' ∈ chainSet p, (1 + violPoly (pigeon p'))).totalDegree
          ≤ ∑ p' ∈ chainSet p, (1 + violPoly (pigeon p')).totalDegree := degree_product _ _
        _ ≤ ∑ _p' ∈ chainSet p, 8 := Finset.sum_le_sum fun p' _ =>
            (totalDegree_add _ _).trans (max_le (by simp) (hviol_deg (pigeon p')))
        _ = (chainSet p).card * 8 := by simp
        _ ≤ d (binOf p) * 8 := Nat.mul_le_mul_right 8 (hchain_card p)
        _ ≤ C * d (binOf p) := by dsimp only [C]; omega
    · simp
  have hPeval : ∀ (x : X) (p : Fin q),
      decide (eval x (P (binOf p) p) = 1) = true ↔
        ∃ p' ∈ chainSet p, ∀ e : V, e.val.1 = pigeon p' → x e = 0 := by
    intro x p
    rw [decide_eq_true_eq]
    simp only [P, if_pos rfl, map_add, map_one, map_prod, hviol_eval]
    by_cases hex : ∃ p' ∈ chainSet p, ∀ e : V, e.val.1 = pigeon p' → x e = 0
    · constructor
      · intro _; exact hex
      · intro _
        obtain ⟨p', hp', h0⟩ := hex
        have hprod0 : (∏ r ∈ chainSet p,
            ((1 : ZMod 2) + if ∀ e : V, e.val.1 = pigeon r → x e = 0 then 1 else 0)) = 0 := by
          refine Finset.prod_eq_zero hp' ?_
          rw [if_pos h0]; decide
        rw [hprod0, add_zero]
    · constructor
      · intro h1
        have hprod1 : (∏ r ∈ chainSet p,
            ((1 : ZMod 2) + if ∀ e : V, e.val.1 = pigeon r → x e = 0 then 1 else 0)) = 1 := by
          refine Finset.prod_eq_one fun r hr => ?_
          have hnr : ¬ ∀ e : V, e.val.1 = pigeon r → x e = 0 := fun h => hex ⟨r, hr, h⟩
          rw [if_neg hnr, add_zero]
        rw [hprod1] at h1
        have h20 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h20] at h1
        exact absurd h1 zero_ne_one
      · intro h; exact absurd h hex
  let vLit : V → Bool → Literal W := fun e b => (Sum.inl (Sum.inl e), b)
  let zLit : Fin q → Bool → Literal W := fun p b => (Sum.inl (Sum.inr p), b)
  let gLit : Fin t → Bool → Literal W := fun g b => (Sum.inr g, b)
  let baseClause : Fin q → Clause W := fun p =>
    if hpos : 0 < posInBatch p then
      {gLit (binOf p) true, zLit p false, zLit ⟨p.val - 1, by omega⟩ true}
    else
      {gLit (binOf p) true, zLit p false}
  let stepClause : Fin q → V → Clause W := fun p e => insert (vLit e false) (baseClause p)
  let stepClauses : Finset (Clause W) :=
    Finset.univ.biUnion (fun p : Fin q => (edgesOf (pigeon p)).image (fun e => stepClause p e))
  let activeClause : Fin t → Clause W := fun g =>
    insert (gLit g true) ((tops g).image (fun p => zLit p true))
  let activeClauses : Finset (Clause W) := Finset.univ.image activeClause
  let allNegGuards : Clause W := Finset.univ.image (fun g : Fin t => gLit g false)
  let extra : Finset (Clause W) := stepClauses ∪ activeClauses ∪ {allNegGuards}
  have hextra_card : extra.card ≤ 8 * q + t + 1 := by
    have hs1 : stepClauses.card ≤ 8 * q := by
      calc stepClauses.card
          ≤ ∑ p : Fin q, ((edgesOf (pigeon p)).image (fun e => stepClause p e)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ p : Fin q, (edgesOf (pigeon p)).card :=
            Finset.sum_le_sum fun p _ => Finset.card_image_le
        _ ≤ ∑ _p : Fin q, 8 := Finset.sum_le_sum fun p _ => hedges_le8 (pigeon p)
        _ = q * 8 := by simp
        _ = 8 * q := Nat.mul_comm _ _
    have hs2 : activeClauses.card ≤ t := by
      calc activeClauses.card ≤ (Finset.univ : Finset (Fin t)).card := Finset.card_image_le
        _ = t := by simp
    have hs3 : (stepClauses ∪ activeClauses).card ≤ stepClauses.card + activeClauses.card :=
      Finset.card_union_le _ _
    have hs4 : extra.card ≤ (stepClauses ∪ activeClauses).card + ({allNegGuards} : Finset _).card :=
      Finset.card_union_le _ _
    simp only [Finset.card_singleton] at hs4
    omega
  let lift : Clause V → Clause W :=
    fun cl => cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W), l.2))
  let F_tot : Set (Clause W) := Set.image lift F ∪ (↑extra : Set (Clause W))
  let GoodLine : Clause W → Prop := fun cl =>
    ∀ j : Fin t, (∃ i : Fin t, gLit i (menu j i) ∈ cl) ∨
      (cl.filter (fun l => l.1.isLeft)).card ≤ C * w j
  have hGood_of_card : ∀ cl : Clause W, cl.card ≤ 12 → GoodLine cl := by
    intro cl hcl j
    right
    have h1 : (cl.filter (fun l => l.1.isLeft)).card ≤ cl.card := Finset.card_filter_le _ _
    have hwj := (hdw j).2
    dsimp only [C]
    omega
  have hGood_of_guard : ∀ (g : Fin t) (cl : Clause W),
      gLit g true ∈ cl → (cl.filter (fun l => l.1.isLeft)).card ≤ C * w g → GoodLine cl := by
    intro g cl hg hcard j
    by_cases hj : j = g
    · subst hj
      exact Or.inr hcard
    · left
      refine ⟨g, ?_⟩
      simpa [menu, hj] using hg
  have hlift_pigeon : ∀ i : Fin (n + 1), (edgesOf i).image (fun e => vLit e true) ∈ F_tot := by
    intro i
    left
    refine ⟨Finset.univ.filter (fun l : Literal V => l.1.1.1 = i ∧ l.2 = true),
      Or.inl (Or.inl ⟨i, rfl⟩), ?_⟩
    ext l
    simp only [lift, edgesOf, vLit, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨e, b⟩, ⟨he, rfl⟩, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨(e, true), ⟨he, rfl⟩, rfl⟩
  have hpeel_v : ∀ (Base : Clause W) (hBv : ∀ e b, vLit e b ∉ Base) (hBc : Base.card ≤ 3)
      (S : Finset V) (hS8 : S.card ≤ 8) (hSb : ∀ e ∈ S, insert (vLit e false) Base ∈ F_tot)
      (T : Finset V) (hTS : T ⊆ S)
      (π₀ : List (Clause W)) (hD0 : IsDerivation F_tot π₀) (hG0 : ∀ cl ∈ π₀, GoodLine cl)
      (hIn : T.image (fun e => vLit e true) ∪ Base ∈ π₀),
      ∃ π₁ : List (Clause W), IsDerivation F_tot π₁ ∧ (∀ cl ∈ π₀, cl ∈ π₁) ∧
        (∀ cl ∈ π₁, GoodLine cl) ∧ Base ∈ π₁ ∧ π₁.length ≤ π₀.length + 2 * T.card := by
    intro Base hBv hBc S hS8 hSb T
    induction T using Finset.induction_on with
    | empty =>
      intro _ π₀ hD0 hG0 hIn
      refine ⟨π₀, hD0, fun _ h => h, hG0, ?_, by simp⟩
      simpa using hIn
    | insert e T he ih =>
      intro hTS π₀ hD0 hG0 hIn
      have heS : e ∈ S := hTS (Finset.mem_insert_self e T)
      let axCl := insert (vLit e false) Base
      have hax : axCl ∈ F_tot := hSb e heS
      let prevCl := (insert e T).image (fun e' => vLit e' true) ∪ Base
      let nextCl := T.image (fun e' => vLit e' true) ∪ Base
      have hres : IsResolvent prevCl axCl nextCl := by
        refine ⟨Sum.inl (Sum.inl e), ?_, Finset.mem_insert_self _ _, ?_⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_insert_self e T))
        · have hnotT : vLit e true ∉ T.image (fun e' => vLit e' true) := by
            intro hm
            obtain ⟨e', he', heq⟩ := Finset.mem_image.mp hm
            cases heq
            exact he he'
          have he1 : prevCl.erase (vLit e true) = T.image (fun e' => vLit e' true) ∪ Base := by
            ext l
            simp only [prevCl, Finset.mem_erase, Finset.mem_union, Finset.mem_image,
              Finset.mem_insert]
            constructor
            · rintro ⟨hne, ⟨e', rfl | he', rfl⟩ | hlB⟩
              · exact absurd rfl hne
              · exact Or.inl ⟨e', he', rfl⟩
              · exact Or.inr hlB
            · rintro (⟨e', he', rfl⟩ | hlB)
              · refine ⟨fun h => hnotT (h ▸ Finset.mem_image_of_mem _ he'), Or.inl ⟨e', Or.inr he', rfl⟩⟩
              · exact ⟨fun h => hBv e true (h ▸ hlB), Or.inr hlB⟩
          have he2 : axCl.erase (vLit e false) = Base :=
            Finset.erase_insert (hBv e false)
          rw [he1, he2, Finset.union_assoc, Finset.union_idempotent]
      let π' := nextCl :: axCl :: π₀
      have hD' : IsDerivation F_tot π' :=
        IsDerivation.res (IsDerivation.ax hD0 hax)
          (List.mem_cons_of_mem _ hIn) (List.mem_cons_self ..) hres
      have hG_ax : GoodLine axCl := hGood_of_card axCl (by
        dsimp only [axCl]
        have := Finset.card_insert_le (vLit e false) Base; omega)
      have hG_next : GoodLine nextCl := hGood_of_card nextCl (by
        dsimp only [nextCl]
        have h1 := Finset.card_union_le (T.image (fun e' => vLit e' true)) Base
        have h2 : (T.image (fun e' => vLit e' true)).card ≤ T.card := Finset.card_image_le
        have h3 : T.card ≤ S.card := Finset.card_le_card ((Finset.subset_insert e T).trans hTS)
        omega)
      have hG' : ∀ cl ∈ π', GoodLine cl := by
        intro cl hcl
        rcases List.mem_cons.mp hcl with rfl | hcl
        · exact hG_next
        · rcases List.mem_cons.mp hcl with rfl | hcl
          · exact hG_ax
          · exact hG0 cl hcl
      obtain ⟨π₁, hD1, hsub1, hG1, hBase1, hlen1⟩ :=
        ih ((Finset.subset_insert e T).trans hTS) π' hD' hG' (List.mem_cons_self ..)
      refine ⟨π₁, hD1, fun cl hcl => hsub1 cl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hcl)),
        hG1, hBase1, ?_⟩
      rw [Finset.card_insert_of_notMem he]
      simp only [π', List.length_cons] at hlen1
      omega
  have hresolve_edges : ∀ (Base : Clause W) (hBv : ∀ e b, vLit e b ∉ Base) (hBc : Base.card ≤ 3)
      (S : Finset V) (hSne : S.Nonempty) (hS8 : S.card ≤ 8)
      (hSpos : S.image (fun e => vLit e true) ∈ F_tot)
      (hSb : ∀ e ∈ S, insert (vLit e false) Base ∈ F_tot)
      (π₀ : List (Clause W)) (hD0 : IsDerivation F_tot π₀) (hG0 : ∀ cl ∈ π₀, GoodLine cl),
      ∃ π₁ : List (Clause W), IsDerivation F_tot π₁ ∧ (∀ cl ∈ π₀, cl ∈ π₁) ∧
        (∀ cl ∈ π₁, GoodLine cl) ∧ Base ∈ π₁ ∧ π₁.length ≤ π₀.length + 17 := by
    intro Base hBv hBc S hSne hS8 hSpos hSb π₀ hD0 hG0
    obtain ⟨e₀, he₀⟩ := hSne
    let posCl := S.image (fun e => vLit e true)
    let axCl := insert (vLit e₀ false) Base
    let midCl := (S.erase e₀).image (fun e => vLit e true) ∪ Base
    have hres0 : IsResolvent posCl axCl midCl := by
      refine ⟨Sum.inl (Sum.inl e₀), Finset.mem_image_of_mem _ he₀, Finset.mem_insert_self _ _, ?_⟩
      have he1 : posCl.erase (vLit e₀ true) = (S.erase e₀).image (fun e => vLit e true) := by
        ext l
        simp only [posCl, Finset.mem_erase, Finset.mem_image]
        constructor
        · rintro ⟨hne, e, heS, rfl⟩
          exact ⟨e, ⟨fun h => hne (by rw [h]), heS⟩, rfl⟩
        · rintro ⟨e, ⟨hne, heS⟩, rfl⟩
          refine ⟨fun h => ?_, e, heS, rfl⟩
          cases h
          exact hne rfl
      have he2 : axCl.erase (vLit e₀ false) = Base := Finset.erase_insert (hBv e₀ false)
      rw [he1, he2]
    let π' := midCl :: axCl :: posCl :: π₀
    have hD' : IsDerivation F_tot π' :=
      IsDerivation.res (IsDerivation.ax (IsDerivation.ax hD0 hSpos) (hSb e₀ he₀))
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (List.mem_cons_self ..) hres0
    have hG' : ∀ cl ∈ π', GoodLine cl := by
      intro cl hcl
      rcases List.mem_cons.mp hcl with rfl | hcl
      · exact hGood_of_card midCl (by
          dsimp only [midCl]
          have h1 := Finset.card_union_le ((S.erase e₀).image (fun e => vLit e true)) Base
          have h2 : ((S.erase e₀).image (fun e => vLit e true)).card ≤ (S.erase e₀).card :=
            Finset.card_image_le
          have h3 : (S.erase e₀).card ≤ S.card := Finset.card_erase_le
          omega)
      · rcases List.mem_cons.mp hcl with rfl | hcl
        · exact hGood_of_card axCl (by
            dsimp only [axCl]
            have := Finset.card_insert_le (vLit e₀ false) Base; omega)
        · rcases List.mem_cons.mp hcl with rfl | hcl
          · exact hGood_of_card posCl (by
              have h2 : posCl.card ≤ S.card := Finset.card_image_le; omega)
          · exact hG0 cl hcl
    obtain ⟨π₁, hD1, hsub1, hG1, hBase1, hlen1⟩ :=
      hpeel_v Base hBv hBc S hS8 hSb (S.erase e₀) (Finset.erase_subset e₀ S) π' hD' hG'
        (List.mem_cons_self ..)
    refine ⟨π₁, hD1, fun cl hcl =>
        hsub1 cl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hcl))),
      hG1, hBase1, ?_⟩
    have hc : (S.erase e₀).card = S.card - 1 := Finset.card_erase_of_mem he₀
    have hSpos' : 1 ≤ S.card := Finset.one_le_card.mpr ⟨e₀, he₀⟩
    simp only [π', List.length_cons] at hlen1
    omega
  have hbase_mem_Ftot : ∀ (p : Fin q) (e : V), e ∈ edgesOf (pigeon p) →
      insert (vLit e false) (baseClause p) ∈ F_tot := by
    intro p e he
    right
    simp only [Finset.mem_coe, extra, Finset.mem_union, stepClauses, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_image]
    exact Or.inl (Or.inl ⟨p, e, he, rfl⟩)
  have hbase_no_v : ∀ (p : Fin q) (e : V) (b : Bool), vLit e b ∉ baseClause p := by
    intro p e b hm
    simp only [baseClause] at hm
    split_ifs at hm
    · simp only [Finset.mem_insert, Finset.mem_singleton, vLit, gLit, zLit] at hm
      rcases hm with h | h | h <;> cases h
    · simp only [Finset.mem_insert, Finset.mem_singleton, vLit, gLit, zLit] at hm
      rcases hm with h | h <;> cases h
  have hbase_card : ∀ p : Fin q, (baseClause p).card ≤ 3 := by
    intro p
    simp only [baseClause]
    split_ifs
    · calc ({gLit (binOf p) true, zLit p false, zLit ⟨p.val - 1, by omega⟩ true} : Clause W).card
          ≤ 1 + ({zLit p false, zLit ⟨p.val - 1, by omega⟩ true} : Clause W).card := by
            simpa [Nat.add_comm] using Finset.card_insert_le (gLit (binOf p) true) _
        _ ≤ 1 + (1 + ({zLit ⟨p.val - 1, by omega⟩ true} : Clause W).card) := by
            have := Finset.card_insert_le (zLit p false) {zLit ⟨p.val - 1, by omega⟩ true}; omega
        _ = 3 := by simp
    · have := Finset.card_insert_le (gLit (binOf p) true) {zLit p false}
      simp only [Finset.card_singleton] at this
      omega
  have hderive_z : ∀ k : ℕ, k ≤ q →
      ∃ π : List (Clause W), IsDerivation F_tot π ∧ (∀ cl ∈ π, GoodLine cl) ∧
        (∀ p : Fin q, p.val < k → ({gLit (binOf p) true, zLit p false} : Clause W) ∈ π) ∧
        π.length ≤ 18 * k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨[], IsDerivation.nil, fun _ h => by simp at h, fun _ h => by omega, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨π₀, hD0, hG0, hZ0, hlen0⟩ := ih (by omega)
      let p : Fin q := ⟨k, hk⟩
      obtain ⟨π₁, hD1, hsub1, hG1, hBase1, hlen1⟩ :=
        hresolve_edges (baseClause p) (hbase_no_v p) (hbase_card p)
          (edgesOf (pigeon p)) (hedges_ne (pigeon p)) (hedges_le8 (pigeon p))
          (hlift_pigeon (pigeon p)) (hbase_mem_Ftot p) π₀ hD0 hG0
      by_cases hpos : 0 < posInBatch p
      · have hpr := hprev_props p hpos
        let prevP : Fin q := ⟨p.val - 1, by omega⟩
        have hpd := hp_decomp p
        have hpk : p.val = k := rfl
        have hprev_lt : prevP.val < k := by
          show k - 1 < k
          omega
        have hprev_in : ({gLit (binOf p) true, zLit prevP false} : Clause W) ∈ π₁ := by
          have := hZ0 prevP hprev_lt
          rw [hpr.1] at this
          exact hsub1 _ this
        have hbase_eq : baseClause p = {gLit (binOf p) true, zLit p false, zLit prevP true} := by
          simp only [baseClause, dif_pos hpos, prevP]
        have hne_prev : prevP ≠ p := by
          intro h
          have hv : prevP.val = p.val := congrArg Fin.val h
          simp only [prevP] at hv
          omega
        let target : Clause W := {gLit (binOf p) true, zLit p false}
        have hres_z : IsResolvent (baseClause p) {gLit (binOf p) true, zLit prevP false} target := by
          refine ⟨Sum.inl (Sum.inr prevP), ?_, ?_, ?_⟩
          · rw [hbase_eq]; simp [zLit]
          · simp [zLit]
          · rw [hbase_eq]
            symm
            ext l
            simp only [target, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
              Finset.mem_singleton, gLit, zLit]
            constructor
            · rintro (⟨hne, rfl | rfl | rfl⟩ | ⟨hne, rfl | rfl⟩)
              · exact Or.inl rfl
              · exact Or.inr rfl
              · exact absurd rfl hne
              · exact Or.inl rfl
              · exact absurd rfl hne
            · rintro (rfl | rfl)
              · left; exact ⟨by simp, Or.inl rfl⟩
              · left
                refine ⟨?_, Or.inr (Or.inl rfl)⟩
                intro heq
                exact Bool.false_ne_true (congrArg Prod.snd heq)
        let π₂ := target :: π₁
        have hD2 : IsDerivation F_tot π₂ :=
          IsDerivation.res hD1 hBase1 hprev_in hres_z
        have hG2 : ∀ cl ∈ π₂, GoodLine cl := by
          intro cl hcl
          rcases List.mem_cons.mp hcl with rfl | hcl
          · exact hGood_of_card target (by
              dsimp only [target]
              have := Finset.card_insert_le (gLit (binOf p) true) {zLit p false}
              simp only [Finset.card_singleton] at this; omega)
          · exact hG1 cl hcl
        refine ⟨π₂, hD2, hG2, ?_, ?_⟩
        · intro r hr
          by_cases hrk : r.val = k
          · have hrp : r = p := Fin.ext hrk
            subst hrp
            exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (hsub1 _ (hZ0 r (by omega)))
        · simp only [π₂, List.length_cons]
          omega
      · have hbase_eq : baseClause p = {gLit (binOf p) true, zLit p false} := by
          simp only [baseClause, dif_neg hpos]
        refine ⟨π₁, hD1, hG1, ?_, by omega⟩
        intro r hr
        by_cases hrk : r.val = k
        · have hrp : r = p := Fin.ext hrk
          subst hrp
          rwa [hbase_eq] at hBase1
        · exact hsub1 _ (hZ0 r (by omega))
  obtain ⟨π_z, hDz, hGz, hZz, hlenz⟩ := hderive_z q le_rfl
  have hpeel_z : ∀ (g : Fin t) (T : Finset (Fin q)) (hT : T ⊆ tops g)
      (π₀ : List (Clause W)) (hD0 : IsDerivation F_tot π₀) (hG0 : ∀ cl ∈ π₀, GoodLine cl)
      (hZ : ∀ p : Fin q, ({gLit (binOf p) true, zLit p false} : Clause W) ∈ π₀)
      (hIn : insert (gLit g true) (T.image (fun p => zLit p true)) ∈ π₀),
      ∃ π₁ : List (Clause W), IsDerivation F_tot π₁ ∧ (∀ cl ∈ π₀, cl ∈ π₁) ∧
        (∀ cl ∈ π₁, GoodLine cl) ∧ ({gLit g true} : Clause W) ∈ π₁ ∧
        π₁.length ≤ π₀.length + T.card := by
    intro g T
    induction T using Finset.induction_on with
    | empty =>
      intro _ π₀ hD0 hG0 _ hIn
      refine ⟨π₀, hD0, fun _ h => h, hG0, ?_, by simp⟩
      simpa using hIn
    | insert p T hp ih =>
      intro hT π₀ hD0 hG0 hZ hIn
      have hp_top : p ∈ tops g := hT (Finset.mem_insert_self p T)
      have hbin_p : binOf p = g := (Finset.mem_filter.mp hp_top).2.1
      have hZp : ({gLit g true, zLit p false} : Clause W) ∈ π₀ := by
        simpa [hbin_p] using hZ p
      let prevCl := insert (gLit g true) ((insert p T).image (fun r => zLit r true))
      let nextCl := insert (gLit g true) (T.image (fun r => zLit r true))
      have hres : IsResolvent prevCl {gLit g true, zLit p false} nextCl := by
        refine ⟨Sum.inl (Sum.inr p), ?_, by simp [zLit], ?_⟩
        · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_insert_self p T))
        · symm
          ext l
          simp only [prevCl, nextCl, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton, Finset.mem_image, gLit, zLit]
          constructor
          · rintro (⟨hne, rfl | ⟨r, rfl | hrT, rfl⟩⟩ | ⟨hne, rfl | rfl⟩)
            · exact Or.inl rfl
            · exact absurd rfl hne
            · exact Or.inr ⟨r, hrT, rfl⟩
            · exact Or.inl rfl
            · exact absurd rfl hne
          · rintro (rfl | ⟨r, hrT, rfl⟩)
            · left; exact ⟨by simp, Or.inl rfl⟩
            · left
              refine ⟨?_, Or.inr ⟨r, Or.inr hrT, rfl⟩⟩
              intro heq
              cases heq
              exact hp hrT
      let π' := nextCl :: π₀
      have hD' : IsDerivation F_tot π' := IsDerivation.res hD0 hIn hZp hres
      have hG_next : GoodLine nextCl := by
        refine hGood_of_guard g nextCl (Finset.mem_insert_self _ _) ?_
        have hsub_f : nextCl.filter (fun l => l.1.isLeft) ⊆ T.image (fun r => zLit r true) := by
          intro l hl
          obtain ⟨hln, hleft⟩ := Finset.mem_filter.mp hl
          rcases Finset.mem_insert.mp hln with rfl | hln'
          · simp [gLit] at hleft
          · exact hln'
        calc (nextCl.filter (fun l => l.1.isLeft)).card
            ≤ (T.image (fun r => zLit r true)).card := Finset.card_le_card hsub_f
          _ ≤ T.card := Finset.card_image_le
          _ ≤ (tops g).card := Finset.card_le_card ((Finset.subset_insert p T).trans hT)
          _ ≤ w g := htops_card g
          _ ≤ C * w g := Nat.le_mul_of_pos_left _ (by dsimp only [C]; omega)
      have hG' : ∀ cl ∈ π', GoodLine cl := by
        intro cl hcl
        rcases List.mem_cons.mp hcl with rfl | hcl
        · exact hG_next
        · exact hG0 cl hcl
      obtain ⟨π₁, hD1, hsub1, hG1, hEnd1, hlen1⟩ :=
        ih ((Finset.subset_insert p T).trans hT) π' hD' hG'
          (fun r => List.mem_cons_of_mem _ (hZ r)) (List.mem_cons_self ..)
      refine ⟨π₁, hD1, fun cl hcl => hsub1 cl (List.mem_cons_of_mem _ hcl), hG1, hEnd1, ?_⟩
      rw [Finset.card_insert_of_notMem hp]
      simp only [π', List.length_cons] at hlen1
      omega
  have hderive_guards : ∀ k : ℕ, k ≤ t →
      ∃ π : List (Clause W), IsDerivation F_tot π ∧ (∀ cl ∈ π_z, cl ∈ π) ∧
        (∀ cl ∈ π, GoodLine cl) ∧
        (∀ g : Fin t, g.val < k → ({gLit g true} : Clause W) ∈ π) ∧
        π.length ≤ π_z.length + k + ∑ g ∈ Finset.univ.filter (fun g : Fin t => g.val < k), (tops g).card := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨π_z, hDz, fun _ h => h, hGz, fun _ h => by omega, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨π₀, hD0, hsub0, hG0, hU0, hlen0⟩ := ih (by omega)
      let g : Fin t := ⟨k, hk⟩
      have hact_F : activeClause g ∈ F_tot := by
        right
        simp only [Finset.mem_coe, extra, Finset.mem_union, activeClauses, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨g, rfl⟩)
      let π' := activeClause g :: π₀
      have hD' : IsDerivation F_tot π' := IsDerivation.ax hD0 hact_F
      have hG_act : GoodLine (activeClause g) := by
        refine hGood_of_guard g (activeClause g) (Finset.mem_insert_self _ _) ?_
        have hsub_f : (activeClause g).filter (fun l => l.1.isLeft) ⊆
            (tops g).image (fun r => zLit r true) := by
          intro l hl
          obtain ⟨hln, hleft⟩ := Finset.mem_filter.mp hl
          rcases Finset.mem_insert.mp hln with rfl | hln'
          · simp [gLit] at hleft
          · exact hln'
        calc ((activeClause g).filter (fun l => l.1.isLeft)).card
            ≤ ((tops g).image (fun r => zLit r true)).card := Finset.card_le_card hsub_f
          _ ≤ (tops g).card := Finset.card_image_le
          _ ≤ w g := htops_card g
          _ ≤ C * w g := Nat.le_mul_of_pos_left _ (by dsimp only [C]; omega)
      have hG' : ∀ cl ∈ π', GoodLine cl := by
        intro cl hcl
        rcases List.mem_cons.mp hcl with rfl | hcl
        · exact hG_act
        · exact hG0 cl hcl
      obtain ⟨π₁, hD1, hsub1, hG1, hUnit1, hlen1⟩ :=
        hpeel_z g (tops g) (Finset.Subset.refl _) π' hD' hG'
          (fun p => List.mem_cons_of_mem _ (hsub0 _ (hZz p p.isLt))) (List.mem_cons_self ..)
      refine ⟨π₁, hD1, fun cl hcl => hsub1 cl (List.mem_cons_of_mem _ (hsub0 cl hcl)), hG1, ?_, ?_⟩
      · intro g' hg'
        by_cases hgk : g'.val = k
        · have : g' = g := Fin.ext hgk
          subst this
          exact hUnit1
        · exact hsub1 _ (List.mem_cons_of_mem _ (hU0 g' (by omega)))
      · have hfilt_eq : Finset.univ.filter (fun g' : Fin t => g'.val < k + 1) =
            insert g (Finset.univ.filter (fun g' : Fin t => g'.val < k)) := by
          ext g'
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, g]
          omega
        have hnotg : g ∉ Finset.univ.filter (fun g' : Fin t => g'.val < k) := by simp [g]
        rw [hfilt_eq, Finset.sum_insert hnotg]
        simp only [π', List.length_cons] at hlen1
        omega
  obtain ⟨π_g, hDg, _, hGg, hUg, hleng⟩ := hderive_guards t le_rfl
  have hleng' : π_g.length ≤ 18 * q + t + q := by
    have hfilt_univ : Finset.univ.filter (fun g : Fin t => g.val < t) = Finset.univ := by
      ext g; simp [g.isLt]
    rw [hfilt_univ] at hleng
    omega
  have hpeel_g : ∀ (T : Finset (Fin t)) (π₀ : List (Clause W)),
      IsDerivation F_tot π₀ → (∀ cl ∈ π₀, GoodLine cl) →
      (∀ g : Fin t, ({gLit g true} : Clause W) ∈ π₀) →
      T.image (fun g => gLit g false) ∈ π₀ →
      ∃ π₁ : List (Clause W), IsDerivation F_tot π₁ ∧ (∀ cl ∈ π₁, GoodLine cl) ∧
        (∅ : Clause W) ∈ π₁ ∧ π₁.length ≤ π₀.length + T.card := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro π₀ hD0 hG0 _ hIn
      refine ⟨π₀, hD0, hG0, ?_, by simp⟩
      simpa using hIn
    | insert g T hg ih =>
      intro π₀ hD0 hG0 hU hIn
      let prevCl := (insert g T).image (fun g' => gLit g' false)
      let nextCl := T.image (fun g' => gLit g' false)
      have hres : IsResolvent {gLit g true} prevCl nextCl := by
        refine ⟨Sum.inr g, Finset.mem_singleton_self _,
          Finset.mem_image_of_mem _ (Finset.mem_insert_self g T), ?_⟩
        symm
        ext l
        simp only [prevCl, nextCl, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton,
          Finset.mem_image, Finset.mem_insert, gLit]
        constructor
        · rintro (⟨hne, rfl⟩ | ⟨hne, g', rfl | hg'T, rfl⟩)
          · exact absurd rfl hne
          · exact absurd rfl hne
          · exact ⟨g', hg'T, rfl⟩
        · rintro ⟨g', hg'T, rfl⟩
          right
          refine ⟨?_, g', Or.inr hg'T, rfl⟩
          intro heq
          cases heq
          exact hg hg'T
      let π' := nextCl :: π₀
      have hD' : IsDerivation F_tot π' := IsDerivation.res hD0 (hU g) hIn hres
      have hG_next : GoodLine nextCl := by
        intro j
        right
        have hemp : nextCl.filter (fun l => l.1.isLeft) = ∅ := by
          ext l
          simp only [nextCl, Finset.mem_filter, Finset.mem_image, Finset.notMem_empty, iff_false,
            not_and]
          rintro ⟨g', _, rfl⟩
          simp [gLit]
        rw [hemp, Finset.card_empty]
        exact Nat.zero_le _
      have hG' : ∀ cl ∈ π', GoodLine cl := by
        intro cl hcl
        rcases List.mem_cons.mp hcl with rfl | hcl
        · exact hG_next
        · exact hG0 cl hcl
      obtain ⟨π₁, hD1, hG1, hemp1, hlen1⟩ :=
        ih π' hD' hG' (fun g' => List.mem_cons_of_mem _ (hU g')) (List.mem_cons_self ..)
      refine ⟨π₁, hD1, hG1, hemp1, ?_⟩
      rw [Finset.card_insert_of_notMem hg]
      simp only [π', List.length_cons] at hlen1
      omega
  have hallNeg_F : allNegGuards ∈ F_tot := by
    right
    simp only [Finset.mem_coe, extra, Finset.mem_union, Finset.mem_singleton]
    exact Or.inr trivial
  let π_start := allNegGuards :: π_g
  have hD_start : IsDerivation F_tot π_start := IsDerivation.ax hDg hallNeg_F
  have hG_start : ∀ cl ∈ π_start, GoodLine cl := by
    intro cl hcl
    rcases List.mem_cons.mp hcl with rfl | hcl
    · intro j
      right
      have hemp : allNegGuards.filter (fun l => l.1.isLeft) = ∅ := by
        ext l
        simp only [allNegGuards, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and]
        rintro ⟨g', rfl⟩
        simp [gLit]
      rw [hemp, Finset.card_empty]
      exact Nat.zero_le _
    · exact hGg cl hcl
  obtain ⟨π, hDπ, hGπ, hempπ, hlenπ⟩ :=
    hpeel_g Finset.univ π_start hD_start hG_start
      (fun g => List.mem_cons_of_mem _ (hUg g g.isLt)) (List.mem_cons_self ..)
  have hπ_len : π.length ≤ 19 * q + 2 * t + 1 := by
    simp only [π_start, List.length_cons, Finset.card_univ, Fintype.card_fin] at hlenπ
    omega
  refine ⟨q, t, P, menu, extra, π, J, ?_, hJcard, ?_, ?_⟩
  · refine ⟨hPdeg, ⟨hDπ, hempπ⟩, ?_⟩
    intro j cl hcl
    exact hGπ cl hcl j
  · omega
  · intro x
    let runX : Fin t → W → Bool := fun j =>
      Sum.elim (Sum.elim (fun v => decide (x v = 1))
        (fun i => decide (eval x (P j i) = 1))) (menu j)
    have hsat_equiv : ∀ j : Fin t,
        Satisfies (runX j) (↑extra) ↔ ClauseSat (runX j) (activeClause j) := by
      intro j
      constructor
      · intro hsat
        refine hsat (activeClause j) ?_
        simp only [Finset.mem_coe, extra, Finset.mem_union, activeClauses, Finset.mem_image,
          Finset.mem_univ, true_and]
        exact Or.inl (Or.inr ⟨j, rfl⟩)
      · intro hact cl hcl
        simp only [Finset.mem_coe, extra, Finset.mem_union, Finset.mem_singleton, stepClauses,
          activeClauses, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hcl
        rcases hcl with (⟨p, e, he, rfl⟩ | ⟨g, rfl⟩) | rfl
        · by_cases hbg : binOf p = j
          · subst hbg
            by_cases hpos : 0 < posInBatch p
            · let prevP : Fin q := ⟨p.val - 1, by omega⟩
              have hpr := hprev_props p hpos
              by_cases hzp : decide (eval x (P (binOf p) p) = 1) = false
              · refine ⟨zLit p false, ?_, hzp⟩
                simp only [stepClause, baseClause, dif_pos hpos]
                exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
              · have hzp_t : decide (eval x (P (binOf p) p) = 1) = true :=
                  Bool.eq_true_of_not_eq_false hzp
                by_cases hzpr : decide (eval x (P (binOf p) prevP) = 1) = true
                · refine ⟨zLit prevP true, ?_, hzpr⟩
                  simp only [stepClause, baseClause, dif_pos hpos]
                  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
                · have hzpr_f : ¬ (decide (eval x (P (binOf prevP) prevP) = 1) = true) := by
                    rw [hpr.1]; exact hzpr
                  obtain ⟨p', hp'c, hp'0⟩ := (hPeval x p).mp hzp_t
                  rw [hchain_pos p hpos] at hp'c
                  rcases Finset.mem_insert.mp hp'c with rfl | hp'prev
                  · have hxe0 : x e = 0 := hp'0 e (Finset.mem_filter.mp he).2
                    refine ⟨vLit e false, Finset.mem_insert_self _ _, ?_⟩
                    show decide (x e = 1) = false
                    rw [hxe0]
                    decide
                  · exact absurd ((hPeval x prevP).mpr ⟨p', hp'prev, hp'0⟩) hzpr_f
            · by_cases hzp : decide (eval x (P (binOf p) p) = 1) = false
              · refine ⟨zLit p false, ?_, hzp⟩
                simp only [stepClause, baseClause, dite_eq_right_iff.mpr (fun h => absurd h hpos)]
                exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
              · have hzp_t : decide (eval x (P (binOf p) p) = 1) = true :=
                  Bool.eq_true_of_not_eq_false hzp
                obtain ⟨p', hp'c, hp'0⟩ := (hPeval x p).mp hzp_t
                have hpos0 : posInBatch p = 0 := by omega
                rw [hchain_zero p hpos0, Finset.mem_singleton] at hp'c
                subst hp'c
                have hxe0 : x e = 0 := hp'0 e (Finset.mem_filter.mp he).2
                refine ⟨vLit e false, Finset.mem_insert_self _ _, ?_⟩
                show decide (x e = 1) = false
                rw [hxe0]
                decide
          · refine ⟨gLit (binOf p) true, ?_, ?_⟩
            · simp only [stepClause, baseClause]
              split_ifs
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
              · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
            · show decide (j ≠ binOf p) = true
              exact decide_eq_true (Ne.symm hbg)
        · by_cases hgj : g = j
          · subst hgj; exact hact
          · refine ⟨gLit g true, Finset.mem_insert_self _ _, ?_⟩
            show decide (j ≠ g) = true
            exact decide_eq_true (Ne.symm hgj)
        · refine ⟨gLit j false, Finset.mem_image_of_mem _ (Finset.mem_univ j), ?_⟩
          show decide (j ≠ j) = false
          exact decide_eq_false (not_not.mpr rfl)
    have hact_equiv : ∀ j : Fin t,
        ClauseSat (runX j) (activeClause j) ↔
          ∃ p' : Fin q, binOf p' = j ∧ ∀ e : V, e.val.1 = pigeon p' → x e = 0 := by
      intro j
      constructor
      · rintro ⟨l, hl, hlv⟩
        rcases Finset.mem_insert.mp hl with rfl | hl'
        · change decide (j ≠ j) = true at hlv
          exact absurd (of_decide_eq_true hlv) (not_not.mpr rfl)
        · obtain ⟨p, hp_top, rfl⟩ := Finset.mem_image.mp hl'
          have hbin_p : binOf p = j := (Finset.mem_filter.mp hp_top).2.1
          have hpt : decide (eval x (P (binOf p) p) = 1) = true := by
            change decide (eval x (P j p) = 1) = true at hlv
            rwa [hbin_p]
          obtain ⟨p', hp'c, hp'0⟩ := (hPeval x p).mp hpt
          have hbin_p' : binOf p' = j := (Finset.mem_filter.mp hp'c).2.1.trans hbin_p
          exact ⟨p', hbin_p', hp'0⟩
      · rintro ⟨p', hbin_p', hp'0⟩
        obtain ⟨p, hp_top, hp'c⟩ := htops_cover p'
        rw [hbin_p'] at hp_top
        have hbin_p : binOf p = j := (Finset.mem_filter.mp hp_top).2.1
        have hpt : decide (eval x (P (binOf p) p) = 1) = true :=
          (hPeval x p).mpr ⟨p', hp'c, hp'0⟩
        refine ⟨zLit p true, Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp_top), ?_⟩
        show decide (eval x (P j p) = 1) = true
        rwa [← hbin_p]
    constructor
    · intro hno i hi
      obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hi
      have hna : ¬ ClauseSat (runX (binOf p')) (activeClause (binOf p')) := by
        rw [← hsat_equiv (binOf p')]
        exact hno (binOf p')
      have hnex : ¬ ∀ e : V, e.val.1 = pigeon p' → x e = 0 := fun h0 =>
        hna ((hact_equiv (binOf p')).mpr ⟨p', rfl, h0⟩)
      push Not at hnex
      obtain ⟨e, he1, he0⟩ := hnex
      have he1' : x e = 1 := by
        generalize x e = c at he0; revert he0; revert c; decide
      exact ⟨e, he1, he1'⟩
    · intro hall j hsat
      rw [hsat_equiv j, hact_equiv j] at hsat
      obtain ⟨p', _, hp'0⟩ := hsat
      obtain ⟨e, he1, hxe1⟩ := hall (pigeon p') (Finset.mem_image_of_mem _ (Finset.mem_univ p'))
      have hxe0 := hp'0 e he1
      rw [hxe0] at hxe1
      exact zero_ne_one hxe1

end MainCase

end Half2

end PEqualNP.Outside.L_pcx_412

theorem PEqualNP.Outside.L_pcx_412 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    (∀ i : Fin (n+1), (G i).Nonempty) ∧
    let V := PEqualNP.Expanders.GEdge G
    let X := V → ZMod 2
    let F := PEqualNP.Expanders.funGraphPHP G
    ∀ (t : ℕ) (d w : Fin t → ℕ), (∀ j, 1 ≤ d j ∧ 1 ≤ w j) →
      let B := ∑ j, d j * w j
      let q := min n B
      let W := fun (a h : ℕ) => (V ⊕ Fin a) ⊕ Fin h
      let run := fun (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
          (menu : Fin t → Fin h → Bool) (x : X) (j : Fin t) =>
        Sum.elim (Sum.elim (fun v => decide (x v = 1))
          (fun i => decide (MvPolynomial.eval x (P j i) = 1))) (menu j)
      let proof := fun (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
          (menu : Fin t → Fin h → Bool) (extra : Set (PEqualNP.ProofComplexity.Clause (W a h)))
          (π : List (PEqualNP.ProofComplexity.Clause (W a h))) (scale : ℕ) =>
        let lift := fun cl : PEqualNP.ProofComplexity.Clause V =>
          cl.image (fun l => ((Sum.inl (Sum.inl l.1) : W a h), l.2))
        (∀ j i, (P j i).totalDegree ≤ scale*d j) ∧
        PEqualNP.ProofComplexity.IsRefutation (Set.image lift F ∪ extra) π ∧
        ∀ j cl, cl ∈ π → (∃ i : Fin h, ((Sum.inr i : W a h), menu j i) ∈ cl) ∨
          (cl.filter (fun l => l.1.isLeft)).card ≤ scale*w j
      (C*B < n → ∀ (a h : ℕ) P menu extra π, proof a h P menu extra π 1 →
        ∃ cl : Fin t → PEqualNP.ProofComplexity.Clause (W a h),
          (∀ j, cl j ∈ extra ∧ cl j ∈ π) ∧
          ∀ (L : X ≃ₗ[ZMod 2] X) (z : X), ∃ U : Finset V, U.card ≤ B ∧
            ∀ x : X, Odd ((Finset.univ.filter (fun y : X =>
              @decide ((∀ v, v ∉ U → y v = x v) ∧ ∀ j,
                ¬ PEqualNP.ProofComplexity.ClauseSat (run a h P menu (z + L y) j) (cl j))
                (Classical.propDecidable _))).card)) ∧
      ∃ (a h : ℕ) (P : Fin t → Fin a → MvPolynomial V (ZMod 2))
          (menu : Fin t → Fin h → Bool) (extra : Finset (PEqualNP.ProofComplexity.Clause (W a h)))
          (π : List (PEqualNP.ProofComplexity.Clause (W a h))) (J : Finset (Fin (n+1))),
        proof a h P menu (↑extra) π C ∧ J.card = q ∧
        a + h + extra.card + π.length ≤ C*(q+t+1) ∧
        ∀ x : X, (∀ j, ¬ PEqualNP.ProofComplexity.Satisfies (run a h P menu x j) (↑extra)) ↔
          ∀ i ∈ J, ∃ e : V, e.val.1 = i ∧ x e = 1) := by
  refine ⟨2400000, 100000, by omega, ?_⟩
  intro n hn
  obtain ⟨G, hLeft8, hRight8, hExp⟩ := PEqualNP.Outside.L_pcx_412.ExpBase.exists_expander n
  have hs1 : 1 ≤ n / 100000 := by omega
  have hNonempty : ∀ i : Fin (n + 1), (G i).Nonempty := by
    intro i
    have h2 : 2 * ({i} : Finset (Fin (n + 1))).card ≤
        (PEqualNP.Expanders.uniqueNbrs G {i}).card := hExp {i} (by simpa using hs1)
    rw [Finset.card_singleton] at h2
    have hne : (PEqualNP.Expanders.uniqueNbrs G {i}).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hne
    rw [PEqualNP.Expanders.uniqueNbrs, Finset.mem_filter] at hj
    have hpos : 0 < (({i} : Finset (Fin (n + 1))).filter (fun i' => j ∈ G i')).card := by
      omega
    obtain ⟨i', hi'⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter, Finset.mem_singleton] at hi'
    exact ⟨j, hi'.1 ▸ hi'.2⟩
  refine ⟨G, fun i => (hLeft8 i).trans (by omega), fun j => (hRight8 j).trans (by omega),
    hNonempty, ?_⟩
  dsimp only
  intro t d w hdw
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · constructor
    · intro _ a h P menu extra π _
      refine ⟨Fin.elim0, fun j => Fin.elim0 j, ?_⟩
      intro L z
      refine ⟨∅, by simp, ?_⟩
      intro x
      have hfilt : Finset.univ.filter (fun y : PEqualNP.Expanders.GEdge G → ZMod 2 =>
          @decide ((∀ v, v ∉ (∅ : Finset (PEqualNP.Expanders.GEdge G)) → y v = x v) ∧ ∀ j : Fin 0,
            ¬ PEqualNP.ProofComplexity.ClauseSat
              (Sum.elim (Sum.elim (fun v => decide ((z + L y) v = 1))
                (fun i => decide (MvPolynomial.eval (z + L y) (P j i) = 1))) (menu j))
              (Fin.elim0 j))
            (Classical.propDecidable _)) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq,
          Finset.notMem_empty, not_false_eq_true, forall_const, Finset.mem_singleton]
        constructor
        · intro hy
          exact funext hy.1
        · rintro rfl
          exact ⟨fun _ => rfl, fun j => Fin.elim0 j⟩
      rw [hfilt, Finset.card_singleton]
      exact odd_one
    · refine ⟨0, 0, Fin.elim0, Fin.elim0, ({∅} : Finset _), [∅], ∅, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun j => Fin.elim0 j, ⟨?_, List.mem_singleton_self ∅⟩, fun j => Fin.elim0 j⟩
        exact PEqualNP.ProofComplexity.IsDerivation.ax
          PEqualNP.ProofComplexity.IsDerivation.nil (Or.inr (by simp))
      · simp
      · simp
      · intro x
        simp
  · constructor
    · intro hCB a h P menu extra π hproof
      have hHard : ¬ PEqualNP.ProofComplexity.PCRefutable
          (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G))
          (3 * ∑ j, d j * w j) :=
        PEqualNP.Outside.L_pcx_412.FunPHPBase.funGraphPHP_no_pc_refutation G hExp hLeft8 hs1
          (by omega)
      exact PEqualNP.Outside.L_pcx_412.Half1.half1_main (PEqualNP.Expanders.funGraphPHP G)
        t d w hdw hHard a h P menu extra π hproof.1 hproof.2.1 hproof.2.2
    · exact PEqualNP.Outside.L_pcx_412.Half2.half2_main G t d w hLeft8 hNonempty hdw ht
