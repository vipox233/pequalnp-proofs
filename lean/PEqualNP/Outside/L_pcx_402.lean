import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open PEqualNP.Expanders


def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)


def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial


def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open PEqualNP.Expanders

theorem permGraph_leftDegLe {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) :
    PEqualNP.Expanders.LeftDegLe (permGraph σ) b := by
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
    PEqualNP.Expanders.RightDegLe (permGraph σ) b := by
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
    (hbad : (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card) :
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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open Finset

theorem permCount : PermCountStmt := by
  intro α _ _ T Y
  classical
  set S := Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y) with hS
  let f : Equiv.Perm α → (T → α) := fun σ x => σ x
  let t : Finset (T → α) :=
    Finset.univ.filter (fun g => Function.Injective g ∧ ∀ x, g x ∈ Y)
  have hmaps : ∀ σ ∈ S, f σ ∈ t := by
    intro σ hσ
    simp only [hS, mem_filter, mem_univ, true_and] at hσ
    simp only [t, mem_filter, mem_univ, true_and]
    refine ⟨?_, fun x => hσ x.1 x.2⟩
    intro a b hab
    exact Subtype.ext (σ.injective hab)
  
  have ht : t.card ≤ Y.card.descFactorial T.card := by
    have hinj : Function.Injective
        (fun g : t => (⟨fun x => ⟨g.1 x, ((mem_filter.mp g.2).2.2 x)⟩,
          fun a b hab => (mem_filter.mp g.2).2.1 (congrArg Subtype.val hab)⟩ : T ↪ Y)) := by
      intro g h hgh
      apply Subtype.ext
      funext x
      exact congrArg Subtype.val (DFunLike.congr_fun hgh x)
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_embedding_eq] at this
    simpa using this
  
  have hfib : ∀ g ∈ t, Finset.card {σ ∈ S | f σ = g} ≤ (Fintype.card α - T.card).factorial := by
    intro g _
    rcases Finset.eq_empty_or_nonempty {σ ∈ S | f σ = g} with h | ⟨σ₀, hσ₀⟩
    · rw [h]; simp
    have hσ₀g : f σ₀ = g := (mem_filter.mp hσ₀).2
    let P := {τ : Equiv.Perm α // ∀ a, ¬ (a ∉ T) → τ a = a}
    have hcardP : Fintype.card P = (Fintype.card α - T.card).factorial := by
      rw [← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a => a ∉ T)),
        Fintype.card_perm]
      congr 1
      rw [Fintype.card_subtype_compl, Fintype.card_coe]
    let F : {σ // σ ∈ ({σ ∈ S | f σ = g} : Finset _)} → P := fun σ =>
      ⟨σ₀⁻¹ * σ.1, by
        intro a ha
        have ha' : a ∈ T := not_not.mp ha
        have h1 : f σ.1 = g := (mem_filter.mp σ.2).2
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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open Finset


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


theorem arith : ArithStmt := by
  refine ⟨100000, 0, by norm_num, fun n _ => ?_⟩
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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open PEqualNP.Expanders

theorem expander_of_parts (hP : PermCountStmt) (hA : ArithStmt)
    (hL : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.LeftDegLe (permGraph σ) b)
    (hR : ∀ {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))),
      PEqualNP.Expanders.RightDegLe (permGraph σ) b)
    (hT : ∀ {n : ℕ} (σ : Fin 8 → Equiv.Perm (Fin (n + 1))) (T : Finset (Fin (n + 1))),
      5 * T.card ≤ n + 1 →
      (PEqualNP.Expanders.uniqueNbrs (permGraph σ) T).card < 2 * T.card →
      ∃ Y : Finset (Fin (n + 1)), Y.card = 5 * T.card ∧ ∀ k, ∀ x ∈ T, σ k x ∈ Y) :
    ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n,
        PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧
        PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 := by
  classical
  obtain ⟨s₀, n₀, h5, hsum⟩ := hA
  refine ⟨8, s₀, n₀, by omega, ?_⟩
  intro n hn
  have hs1 := hsum n hn
  have hsn : 5 * (n / s₀) ≤ n := by
    have h1 := Nat.div_mul_le_self n s₀
    have h2 : 5 * (n / s₀) ≤ n / s₀ * s₀ := by
      rw [Nat.mul_comm]; exact Nat.mul_le_mul_left (n / s₀) h5
    omega
  set s := n / s₀ with hs
  suffices h : ∃ σ : Fin 8 → Equiv.Perm (Fin (n + 1)), IsBdryExpander (permGraph σ) s 2 by
    obtain ⟨σ, hσ⟩ := h
    exact ⟨permGraph σ, hL σ, hR σ, hσ⟩
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
    obtain ⟨Y, hYc, hY⟩ := hT σ T (by omega) hTlt
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
    have h := hP (Fin (n + 1)) T Y
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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core
open PEqualNP.ProofComplexity PEqualNP


theorem L043 : ∃ (b s₀ n₀ : ℕ), 0 < s₀ ∧ ∀ n : ℕ, n₀ ≤ n → ∃ G : PEqualNP.Expanders.BipGraph (n + 1) n, PEqualNP.Expanders.LeftDegLe G b ∧ PEqualNP.Expanders.RightDegLe G b ∧ PEqualNP.Expanders.IsBdryExpander G (n / s₀) 2 :=
  Helpers.expander_of_parts Helpers.permCount Helpers.arith
    (fun σ => Helpers.permGraph_leftDegLe σ) (fun σ => Helpers.permGraph_rightDegLe σ)
    (fun σ T hT hbad => Helpers.permGraph_trap σ T hT hbad)

end PEqualNP.Outside.L_pcx_402_aux.Core

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial

variable {σ τ : Type}


theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)


theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
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


theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))


theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
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


theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]


theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this


theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
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


theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this


theorem bitPHPSystem_injective {m l : ℕ} (a : Fin m × Fin l → ZMod 2)
    (ha : ∀ f ∈ bitPHPSystem m l, eval a f = 0) :
    Function.Injective (fun (i : Fin m) (t : Fin l) => a (i, t)) := by
  intro i i' hii
  by_contra hne
  have h := ha _ (Or.inr ⟨i, i', hne, rfl⟩)
  rw [map_prod] at h
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h
  have hEq : a (i, t) = a (i', t) := congrFun hii t
  simp only [map_add, map_one, eval_X, hEq] at ht
  generalize a (i', t) = c at ht
  revert ht; revert c; decide


theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial


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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial



section Static

variable {σ : Type}


noncomputable def staticSpan (F : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2)
    {q | ∃ (a : σ →₀ ℕ) (f : MvPolynomial σ (ZMod 2)),
      f ∈ F ∧ (monomial a 1 * f).totalDegree ≤ k ∧ q = monomial a 1 * f}

theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]


theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl


theorem X_mul_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} (j : σ)
    {g : MvPolynomial σ (ZMod 2)} (hg : g ∈ staticSpan F k) :
    X j * g ∈ staticSpan F (k + 1) := by
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    have heq : X j * (monomial a 1 * f) =
        monomial (a + Finsupp.single j 1) (1 : ZMod 2) * f := by
      rw [← monomial_one_mul_X]
      ring
    refine Submodule.subset_span ⟨a + Finsupp.single j 1, f, hf, ?_, heq⟩
    rw [← heq]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx


theorem pcDerivable_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) : p ∈ staticSpan F B := by
  induction h with
  | @ax p hp hdeg =>
    exact Submodule.subset_span ⟨0, p, hp, by simpa using hdeg, by simp⟩
  | zero => exact Submodule.zero_mem _
  | add _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simp
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    exact X_mul_mem_staticSpan j (hint k (Nat.lt_succ_self k) p ih (by omega))


theorem one_mem_staticSpan_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    (h : (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F B) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F 0 := by
  induction B with
  | zero => exact h
  | succ k ih =>
    exact ih (fun k' hk' => hint k' (by omega)) (hint k (by omega) 1 h (by simp))


theorem dual_eq_of_monomial_eq {k : ℕ}
    (f g : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h : ∀ a : σ →₀ ℕ, a.degree ≤ k → f (monomial a 1) = g (monomial a 1))
    (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ k) : f p = g p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hm : monomial a (p.coeff a) = p.coeff a • monomial a (1 : ZMod 2) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, h a ((le_totalDegree ha).trans hp)]

theorem support_add_single_one [DecidableEq σ] (a : σ →₀ ℕ) (v : σ) :
    (a + Finsupp.single v 1).support = insert v a.support := by
  ext u
  by_cases h : v = u
  · subst h
    simp
  · simp [Ne.symm h]

theorem card_support_le_degree (a : σ →₀ ℕ) : a.support.card ≤ a.degree := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)

end Static



section Matching

variable {m N : ℕ}


def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b


def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)


def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T

theorem isPartialMatching_empty : IsPartialMatching (∅ : Finset (Fin m × Fin N)) := by
  intro a ha
  simp at ha

theorem IsPartialMatching.mono {S T : Finset (Fin m × Fin N)} (hT : IsPartialMatching T)
    (hST : S ⊆ T) : IsPartialMatching S :=
  fun a ha b hb h => hT a (hST ha) b (hST hb) h


theorem isPartialMatching_insert_iff {S : Finset (Fin m × Fin N)} (hS : IsPartialMatching S)
    {i : Fin m} (hrow : ∀ a ∈ S, a.1 ≠ i) (j : Fin N) :
    IsPartialMatching (insert (i, j) S) ↔ ∀ a ∈ S, a.2 ≠ j := by
  constructor
  · intro h a ha haj
    have := h a (Finset.mem_insert_of_mem ha) (i, j) (Finset.mem_insert_self _ _) (Or.inr haj)
    exact hrow a ha (by rw [this])
  · intro hcol a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
    · rfl
    · rcases hab with h | h
      · exact absurd h.symm (hrow b hb')
      · exact absurd h.symm (hcol b hb')
    · rcases hab with h | h
      · exact absurd h (hrow a ha')
      · exact absurd h (hcol a ha')
    · exact hS a ha' b hb' hab


theorem not_isPartialMatching_insert {S : Finset (Fin m × Fin N)} {i : Fin m} {j j0 : Fin N}
    (h0 : (i, j0) ∈ S) (hj : j ≠ j0) : ¬ IsPartialMatching (insert (i, j) S) := by
  intro h
  have := h (i, j) (Finset.mem_insert_self _ _) (i, j0) (Finset.mem_insert_of_mem h0)
    (Or.inl rfl)
  exact hj (congrArg Prod.snd this)

open Classical in

noncomputable def momentWeight (z : Finset (Fin m × Fin N) → ZMod 2)
    (S : Finset (Fin m × Fin N)) : ZMod 2 :=
  if IsPartialMatching S then z S else 0

theorem momentWeight_of_not {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : ¬ IsPartialMatching S) : momentWeight z S = 0 :=
  ite_eq_right h

theorem momentWeight_of_matching {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : IsPartialMatching S) : momentWeight z S = z S :=
  ite_eq_left h


theorem momentWeight_row_sum {z : Finset (Fin m × Fin N) → ZMod 2} {k : ℕ}
    (hz : MomentConsistent m N k z) (S : Finset (Fin m × Fin N))
    (hS : IsPartialMatching S → S.card < k) (i : Fin m) :
    ∑ j : Fin N, momentWeight z (insert (i, j) S) = momentWeight z S := by
  by_cases hM : IsPartialMatching S
  · by_cases hrow : ∀ a ∈ S, a.1 ≠ i
    · rw [momentWeight_of_matching hM, hz S hM (hS hM) i hrow, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : ∀ a ∈ S, a.2 ≠ j
      · rw [ite_eq_left hc,
          momentWeight_of_matching ((isPartialMatching_insert_iff hM hrow j).mpr hc)]
      · rw [ite_eq_right hc, momentWeight_of_not
          (fun h => hc ((isPartialMatching_insert_iff hM hrow j).mp h))]
    · push Not at hrow
      obtain ⟨⟨i', j0⟩, ha, hi⟩ := hrow
      simp only at hi
      subst hi
      rw [Finset.sum_eq_single j0]
      · rw [Finset.insert_eq_of_mem ha]
      · intro j _ hj
        exact momentWeight_of_not (not_isPartialMatching_insert ha hj)
      · intro h
        exact absurd (Finset.mem_univ _) h
  · rw [momentWeight_of_not hM]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact momentWeight_of_not fun h => hM (h.mono (Finset.subset_insert _ _))




noncomputable def momentFunctional (z : Finset (Fin m × Fin N) → ZMod 2) :
    MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (basisMonomials (Fin m × Fin N) (ZMod 2)).constr (ZMod 2)
    fun a => momentWeight z a.support

theorem momentFunctional_monomial (z : Finset (Fin m × Fin N) → ZMod 2)
    (a : Fin m × Fin N →₀ ℕ) :
    momentFunctional z (monomial a 1) = momentWeight z a.support := by
  have h := (basisMonomials (Fin m × Fin N) (ZMod 2)).constr_basis (ZMod 2)
    (fun a => momentWeight z a.support) a
  rw [coe_basisMonomials] at h
  exact h


theorem rowAxiom_totalDegree_le (i : Fin m) :
    ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [totalDegree_X]

theorem one_le_rowAxiom_totalDegree (hN : 1 ≤ N) (i : Fin m) :
    1 ≤ ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree := by
  by_contra hlt
  have h0 : ((∑ j : Fin N, X (i, j)) + 1 :
      MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have e0 := congrArg (eval (fun _ : Fin m × Fin N => (0 : ZMod 2))) h0
  have e1 := congrArg
    (eval (fun v : Fin m × Fin N => if v = (i, (⟨0, hN⟩ : Fin N)) then (1 : ZMod 2) else 0)) h0
  simp only [map_add, map_sum, eval_X, map_one, eval_C, Finset.sum_const_zero, zero_add] at e0 e1
  rw [← e0] at e1
  simp [Prod.mk.injEq] at e1

theorem monomial_one_mul_rowAxiom (a : Fin m × Fin N →₀ ℕ) (i : Fin m) :
    monomial a (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) =
      (∑ j : Fin N, monomial (a + Finsupp.single (i, j) 1) 1) + monomial a 1 := by
  rw [mul_add, mul_one, Finset.mul_sum]
  simp only [monomial_one_mul_X]


theorem momentFunctional_staticSpan (hN : 1 ≤ N) {z : Finset (Fin m × Fin N) → ZMod 2}
    {k : ℕ} (hz : MomentConsistent m N k z) {p : MvPolynomial (Fin m × Fin N) (ZMod 2)}
    (hp : p ∈ staticSpan (funPHPSystem m N) k) : momentFunctional z p = 0 := by
  induction hp using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    rcases hf with ⟨v, rfl⟩ | ⟨i, j, j', hne, rfl⟩ | ⟨i, i', j, hne, rfl⟩ | ⟨i, rfl⟩
    · rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, map_add,
        momentFunctional_monomial, momentFunctional_monomial, support_add_single_one,
        support_add_single_one, Finset.insert_idem v a.support]
      exact CharTwo.add_self_eq_zero _
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i, j')
        (Finset.mem_insert_self _ _) (Or.inl rfl)
      exact congrArg Prod.snd this
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i', j)
        (Finset.mem_insert_self _ _) (Or.inr rfl)
      exact congrArg Prod.fst this
    · have hrow := one_le_rowAxiom_totalDegree (m := m) hN i
      have hne0 :
          ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) ≠ 0 := by
        intro h0
        rw [h0, totalDegree_zero] at hrow
        omega
      have hmon : monomial a (1 : ZMod 2) ≠ 0 := by
        rw [Ne, monomial_eq_zero]
        exact one_ne_zero
      rw [totalDegree_mul_of_isDomain hmon hne0, totalDegree_monomial_one] at hdeg
      have hcard := card_support_le_degree a
      rw [monomial_one_mul_rowAxiom, map_add, map_sum, momentFunctional_monomial]
      simp only [momentFunctional_monomial, support_add_single_one]
      rw [momentWeight_row_sum hz a.support (fun _ => by omega) i]
      exact CharTwo.add_self_eq_zero _




noncomputable def indMon (T : Finset (Fin m × Fin N)) : Fin m × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v ∈ T then 1 else 0

theorem indMon_apply (T : Finset (Fin m × Fin N)) (v : Fin m × Fin N) :
    indMon T v = if v ∈ T then 1 else 0 := rfl

theorem indMon_support (T : Finset (Fin m × Fin N)) : (indMon T).support = T := by
  ext v
  simp [indMon_apply]

theorem indMon_degree (T : Finset (Fin m × Fin N)) : (indMon T).degree = T.card := by
  rw [Finsupp.degree_eq_sum]
  simp [indMon_apply]

theorem indMon_insert {T : Finset (Fin m × Fin N)} {v : Fin m × Fin N} (hv : v ∉ T) :
    indMon (insert v T) = indMon T + Finsupp.single v 1 := by
  ext u
  by_cases h : u = v
  · subst h
    simp [indMon_apply, hv]
  · simp [indMon_apply, h]

theorem eq_indMon_support {a : Fin m × Fin N →₀ ℕ} (h : ∀ v, a v ≤ 1) :
    a = indMon a.support := by
  ext v
  have := h v
  by_cases h0 : a v = 0
  · simp [indMon_apply, h0]
  · simp [indMon_apply, h0]
    omega


theorem dual_monomial_eq_indMon {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    ∀ (n : ℕ) (a : Fin m × Fin N →₀ ℕ), a.degree = n → a.degree ≤ k →
      φ (monomial a 1) = φ (monomial (indMon a.support) 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a han hak
    by_cases h : ∀ v, a v ≤ 1
    · rw [← eq_indMon_support h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    have hle : Finsupp.single v 2 ≤ a := by
      intro u
      by_cases huv : v = u
      · subst huv
        rw [Finsupp.single_eq_same]
        omega
      · simp [huv]
    obtain ⟨b, hb⟩ : ∃ b, a = b + Finsupp.single v 2 :=
      ⟨a - Finsupp.single v 2, (tsub_add_cancel_of_le hle).symm⟩
    set c := b + Finsupp.single v 1 with hc
    have hac : a = c + Finsupp.single v 1 := by
      rw [hb, hc, add_assoc, ← Finsupp.single_add]
    have hdeg : a.degree = c.degree + 1 := by
      rw [hac, map_add, Finsupp.degree_single]
    have hq : monomial b (1 : ZMod 2) * (X v * X v + X v) = monomial a 1 + monomial c 1 := by
      rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, ← hc, ← hac]
    have hmem : monomial a (1 : ZMod 2) + monomial c 1 ∈ staticSpan (funPHPSystem m N) k := by
      refine Submodule.subset_span ⟨b, _, Or.inl ⟨v, rfl⟩, ?_, hq.symm⟩
      rw [hq]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_monomial_one]
        exact hak
      · rw [totalDegree_monomial_one]
        omega
    have h0 := hφ _ hmem
    rw [map_add, CharTwo.add_eq_zero] at h0
    have hsupp : a.support = c.support := by
      rw [hac, support_add_single_one, Finset.insert_eq_of_mem]
      rw [Finsupp.mem_support_iff, hc]
      simp
    rw [h0, hsupp]
    exact ih c.degree (by omega) c rfl (by omega)


theorem dual_monomial_eq_zero {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (a : Fin m × Fin N →₀ ℕ) (hak : a.degree ≤ k) (hM : ¬ IsPartialMatching a.support) :
    φ (monomial a 1) = 0 := by
  unfold IsPartialMatching at hM
  push Not at hM
  obtain ⟨u, hu, v, hv, huv, hne⟩ := hM
  have hle : Finsupp.single u 1 + Finsupp.single v 1 ≤ a := by
    intro w
    have h1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
    have h2 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    by_cases hwu : u = w
    · subst hwu
      simpa [Finsupp.single_apply, Ne.symm hne] using h1
    · by_cases hwv : v = w
      · subst hwv
        simpa [Finsupp.single_apply, hne] using h2
      · simp [hwu, hwv]
  obtain ⟨b, hb⟩ : ∃ b, a = b + (Finsupp.single u 1 + Finsupp.single v 1) :=
    ⟨a - (Finsupp.single u 1 + Finsupp.single v 1), (tsub_add_cancel_of_le hle).symm⟩
  have hq : monomial b (1 : ZMod 2) * (X u * X v) = monomial a 1 := by
    rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, hb, add_assoc]
  have hF : (X u * X v : MvPolynomial (Fin m × Fin N) (ZMod 2)) ∈ funPHPSystem m N := by
    obtain ⟨i, j⟩ := u
    obtain ⟨i', j'⟩ := v
    rcases huv with h | h
    · simp only at h
      subst h
      exact Or.inr (Or.inl ⟨i, j, j', fun h => hne (by rw [h]), rfl⟩)
    · simp only at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨i, i', j, fun h => hne (by rw [h]), rfl⟩))
  refine hφ _ (Submodule.subset_span ⟨b, _, hF, ?_, hq.symm⟩)
  rw [hq, totalDegree_monomial_one]
  exact hak


theorem momentConsistent_of_dual {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    MomentConsistent m N k fun T => φ (monomial (indMon T) 1) := by
  intro T hT hcard i hrow
  have hnot : ∀ j : Fin N, (i, j) ∉ T := fun j hj => hrow _ hj rfl
  have hmem : monomial (indMon T) (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) ∈
      staticSpan (funPHPSystem m N) k := by
    refine Submodule.subset_span ⟨indMon T, _, Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)), ?_, rfl⟩
    refine (totalDegree_mul _ _).trans ?_
    have h1 := rowAxiom_totalDegree_le (N := N) i
    rw [totalDegree_monomial_one, indMon_degree]
    omega
  have h0 := hφ _ hmem
  rw [monomial_one_mul_rowAxiom, map_add, CharTwo.add_eq_zero, map_sum] at h0
  show φ (monomial (indMon T) 1) = _
  rw [← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← indMon_insert (hnot j)]
  by_cases hc : ∀ a ∈ T, a.2 ≠ j
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    refine dual_monomial_eq_zero hφ _ ?_ ?_
    · rw [indMon_degree, Finset.card_insert_of_notMem (hnot j)]
      omega
    · rw [indMon_support]
      exact fun h => hc ((isPartialMatching_insert_iff hT hrow j).mp h)


theorem dual_eq_momentFunctional {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2)) (hp : p.totalDegree ≤ k) :
    φ p = momentFunctional (fun T => φ (monomial (indMon T) 1)) p := by
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hp
  rw [momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM]
    exact dual_monomial_eq_indMon hφ _ a rfl ha
  · rw [momentWeight_of_not hM]
    exact dual_monomial_eq_zero hφ a ha hM




theorem staticSpan_funPHP_inter (hN : 1 ≤ N) {k : ℕ} (hext : MomentExt m N k)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2))
    (hp : p ∈ staticSpan (funPHPSystem m N) (k + 1)) (hdeg : p.totalDegree ≤ k) :
    p ∈ staticSpan (funPHPSystem m N) k := by
  by_contra hnot
  obtain ⟨φ, hφp, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0 := by
    intro q hq
    have : φ q ∈ (staticSpan (funPHPSystem m N) k).map φ := Submodule.mem_map_of_mem hq
    rw [hmap] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨z', hz', hagree⟩ := hext _ (momentConsistent_of_dual hφ)
  apply hφp
  rw [dual_eq_momentFunctional hφ p hdeg, ← momentFunctional_staticSpan hN hz' hp]
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hdeg
  rw [momentFunctional_monomial, momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM, momentWeight_of_matching hM]
    exact (hagree _ hM ((card_support_le_degree a).trans ha)).symm
  · rw [momentWeight_of_not hM, momentWeight_of_not hM]


theorem no_pc_refutation_of_momentExt :
    ∀ m N B : ℕ, 1 ≤ N → (∀ k < B, MomentExt m N k) →
      ¬ PCRefutable (funPHPSystem m N) B := by
  intro m N B hN hext href
  have hint : ∀ k < B, ∀ p, p ∈ staticSpan (funPHPSystem m N) (k + 1) → p.totalDegree ≤ k →
      p ∈ staticSpan (funPHPSystem m N) k :=
    fun k hk p => staticSpan_funPHP_inter hN (hext k hk) p
  have h0 := one_mem_staticSpan_zero hint (pcDerivable_mem_staticSpan hint href)
  have hz : MomentConsistent m N 0 fun _ => 1 := by
    intro T _ hcard
    omega
  have hval := momentFunctional_staticSpan hN hz h0
  have h1 : (1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) = monomial 0 1 := rfl
  rw [h1, momentFunctional_monomial, Finsupp.support_zero,
    momentWeight_of_matching isPartialMatching_empty] at hval
  exact one_ne_zero hval




theorem momentExt_zero (m N : ℕ) (hN : 1 ≤ N) : MomentExt m N 0 := by
  intro z _
  refine ⟨fun T => if T = ∅ then z ∅ else
    if ∃ i : Fin m, T = {(i, (⟨0, hN⟩ : Fin N))} then z ∅ else 0, ?_, ?_⟩
  · intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      ite_true, insert_empty_eq, Finset.singleton_ne_empty, ite_false]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [ite_eq_left ⟨i, rfl⟩]
    · intro j _ hj
      refine ite_eq_right ?_
      rintro ⟨i', h⟩
      rw [Finset.singleton_inj] at h
      exact hj (congrArg Prod.snd h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro T _ hcard
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp


theorem not_momentExt_zero_of_no_holes (m : ℕ) (hm : 1 ≤ m) : ¬ MomentExt m 0 0 := by
  intro h
  obtain ⟨z', hz', hagree⟩ := h (fun _ => 1) (fun T _ hcard => by omega)
  have h1 := hz' ∅ isPartialMatching_empty (by simp) ⟨0, hm⟩ (by simp)
  rw [hagree ∅ isPartialMatching_empty (by simp)] at h1
  simp at h1


theorem not_momentExt_two_one_one : ¬ MomentExt 2 1 1 := by
  intro h
  have hz : MomentConsistent 2 1 1 fun _ => 1 := by
    intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp
  obtain ⟨z', hz', hagree⟩ := h _ hz
  have hM : IsPartialMatching ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)) := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  have h1 := hz' {((0 : Fin 2), (0 : Fin 1))} hM (by simp) 1 (by simp)
  rw [hagree _ hM (by simp)] at h1
  have hempty : (Finset.univ.filter fun j : Fin 1 =>
      ∀ a ∈ ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)), a.2 ≠ j) = ∅ := by
    decide
  rw [hempty, Finset.sum_empty] at h1
  exact one_ne_zero h1

end Matching

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial

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

theorem nf_monomial_support (U : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (a : σ →₀ ℕ) : ∀ b ∈ (nf U (monomial a 1)).support, b = a ∨ MonoLt b a := by
  have hd : ∀ c ∈ {b | b = a ∨ MonoLt b a}, ∀ b, MonoLt b c → b ∈ {b | b = a ∨ MonoLt b a} := by
    intro c hc b hb
    rcases hc with hc | hc
    · rw [hc] at hb
      exact Or.inr hb
    · exact Or.inr (monoLt_trans hb hc)
  have hm : monomial a (1 : ZMod 2) ∈ restrictSupport (ZMod 2) {b | b = a ∨ MonoLt b a} :=
    (monomial_mem_restrictSupport (R := ZMod 2)).2 (Or.inl (Or.inl rfl))
  intro b hb
  exact (mem_restrictSupport_iff (R := ZMod 2)).1 (nf_mem_of_downClosed U hd hm) hb

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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open PEqualNP.Expanders

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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)


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

theorem locIdeal_mono {S S' : Finset (Fin m)} (h : S ⊆ S') : locIdeal G S ≤ locIdeal G S' := by
  intro f hf
  rw [mem_locIdeal] at hf ⊢
  exact fun α hα => hf α ⟨hα.1, fun i hi => hα.2 i (h hi)⟩

theorem X_mul_mem_locIdeal {S : Finset (Fin m)} (v : GEdge G)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) : X v * f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [map_mul, hf α hα, mul_zero]

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

theorem one_not_mem_locIdeal_empty : (1 : MvPolynomial (GEdge G) (ZMod 2)) ∉ locIdeal G ∅ := by
  rw [mem_locIdeal]
  intro h
  have h0 := h (fun _ => 0) ⟨fun _ _ _ _ => mul_zero _, fun i hi => absurd hi (by simp)⟩
  rw [map_one] at h0
  exact one_ne_zero h0

theorem card_monoHoles_le (a : GEdge G →₀ ℕ) : (monoHoles G a).card ≤ a.degree := by
  refine Finset.card_image_le.trans ?_
  rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)


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

theorem monoHoles_pigeonClause (i : Fin m) :
    ∀ a ∈ (clausePoly (pigeonClause G i)).support, monoHoles G a ⊆ G i := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  have hv : e ∈ (clausePoly (pigeonClause G i)).vars :=
    (mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩
  rw [localSat_clausePoly_pigeonClause] at hv
  obtain ⟨l, hl, hel⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
  have hel' := vars_add_subset _ _ hel
  rw [vars_one, vars_X, Finset.empty_union, Finset.mem_singleton] at hel'
  have h := (Finset.mem_filter.mp hl).2.1
  subst hel'
  have := l.1.2
  rwa [h] at this

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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)


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




noncomputable def localNF_zeroOut (K : Finset (Fin N)) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 ∈ K then X e else 0

theorem localNF_zeroOut_monomial (K : Finset (Fin N)) (b : GEdge G →₀ ℕ) (c : ZMod 2) :
    bind₁ (localNF_zeroOut G K) (monomial b c)
      = if monoHoles G b ⊆ K then monomial b c else 0 := by
  rw [bind₁_monomial]
  split_ifs with h
  · have hprod : ∏ e ∈ b.support, localNF_zeroOut G K e ^ b e
        = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
      refine Finset.prod_congr rfl fun e he => ?_
      rw [localNF_zeroOut, ite_eq_left (h (Finset.mem_image_of_mem _ he))]
    rw [hprod, monomial_eq]
    rfl
  · obtain ⟨x, hx, hxK⟩ := Finset.not_subset.mp h
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.prod_eq_zero he, mul_zero]
    rw [localNF_zeroOut, ite_eq_right hxK, zero_pow (Finsupp.mem_support_iff.mp he)]

theorem localNF_zeroOut_mem {S : Finset (Fin m)} {K : Finset (Fin N)} (hK : S.biUnion G ⊆ K)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ locIdeal G S) :
    bind₁ (localNF_zeroOut G K) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_zeroOut G K e) * eval α (localNF_zeroOut G K e') = 0
    by_cases h : e.1.2 ∈ K
    · by_cases h' : e'.1.2 ∈ K
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_left h, ite_eq_left h', eval_X, eval_X]
        exact hα.1 e e' h1 h2
      · rw [localNF_zeroOut, localNF_zeroOut, ite_eq_right h', map_zero, mul_zero]
    · rw [localNF_zeroOut, ite_eq_right h, map_zero, zero_mul]
  · intro i hi
    obtain ⟨e, he, h1⟩ := hα.2 i hi
    have hmem : e.1.2 ∈ K := by
      refine hK (Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩)
      rw [← he]
      exact e.2
    refine ⟨e, he, ?_⟩
    show eval α (localNF_zeroOut G K e) = 1
    rw [localNF_zeroOut, ite_eq_left hmem, eval_X, h1]

theorem localNF_zeroOut_eq (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    bind₁ (localNF_zeroOut G K) r
      = ∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K), monomial b (r.coeff b) := by
  rw [localNF_map_eq_sum, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => localNF_zeroOut_monomial G K b _

theorem localNF_support_sum_filter (K : Finset (Fin N)) (r : MvPolynomial (GEdge G) (ZMod 2)) :
    (∑ b ∈ r.support.filter (fun b => monoHoles G b ⊆ K),
        monomial b (r.coeff b)).support
      ⊆ r.support.filter (fun b => monoHoles G b ⊆ K) := by
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Finset.mem_biUnion.mp (support_sum hb)
  have hbc' := Finset.mem_singleton.mp (support_monomial_subset hbc)
  rw [hbc']
  exact hc


theorem nf_locIdeal_holes (S : Finset (Fin m)) (a : GEdge G →₀ ℕ) :
    ∀ b ∈ (nf (locIdeal G S) (monomial a 1)).support,
      monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G := by
  have hsub := localNF_support_sum_filter G (monoHoles G a ∪ S.biUnion G)
    (nf (locIdeal G S) (monomial a 1))
  have heq : nf (locIdeal G S) (monomial a 1)
      = ∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
          (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
          monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b) := by
    refine nf_unique (locIdeal G S) ?_ ?_
    · intro b hb
      exact nf_support_isStd (locIdeal G S) (monomial a 1) b (Finset.mem_filter.mp (hsub hb)).1
    · have h := localNF_zeroOut_mem G (S := S) (K := monoHoles G a ∪ S.biUnion G)
        Finset.subset_union_right (nf_sub_mem (locIdeal G S) (monomial a 1))
      rw [map_sub, localNF_zeroOut_monomial, ite_eq_left Finset.subset_union_left,
        localNF_zeroOut_eq] at h
      exact h
  intro b hb
  have hb' : b ∈ (∑ b ∈ (nf (locIdeal G S) (monomial a 1)).support.filter
      (fun b => monoHoles G b ⊆ monoHoles G a ∪ S.biUnion G),
      monomial b ((nf (locIdeal G S) (monomial a 1)).coeff b)).support := by
    rw [← heq]
    exact hb
  exact (Finset.mem_filter.mp (hsub hb')).2




noncomputable def localNF_override (p : Fin m) (j : Fin N) (e : GEdge G) :
    MvPolynomial (GEdge G) (ZMod 2) :=
  if e.1.2 = j then (if e.1.1 = p then 1 else 0) else X e


noncomputable def localNF_drop (j : Fin N) (c : GEdge G →₀ ℕ) : GEdge G →₀ ℕ :=
  c.filter (fun e => e.1.2 ≠ j)

theorem localNF_override_monomial_of_notMem (p : Fin m) {j : Fin N} {b : GEdge G →₀ ℕ}
    (hb : j ∉ monoHoles G b) (c : ZMod 2) :
    bind₁ (localNF_override G p j) (monomial b c) = monomial b c := by
  rw [bind₁_monomial]
  have hprod : ∏ e ∈ b.support, localNF_override G p j e ^ b e
      = ∏ e ∈ b.support, (X e : MvPolynomial (GEdge G) (ZMod 2)) ^ b e := by
    refine Finset.prod_congr rfl fun e he => ?_
    have hne : e.1.2 ≠ j := fun h => hb (h ▸ Finset.mem_image_of_mem _ he)
    rw [localNF_override, ite_eq_right hne]
  rw [hprod, monomial_eq]
  rfl

theorem localNF_override_mem {S : Finset (Fin m)} {p : Fin m} {j : Fin N} (hj : j ∈ G p)
    (hjS : j ∉ S.biUnion G) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f ∈ locIdeal G (insert p S)) :
    bind₁ (localNF_override G p j) f ∈ locIdeal G S := by
  rw [mem_locIdeal] at hf ⊢
  intro α hα
  rw [localNF_eval_bind₁]
  refine hf _ ⟨?_, ?_⟩
  · intro e e' h1 h2
    show eval α (localNF_override G p j e) * eval α (localNF_override G p j e') = 0
    by_cases h : e.1.2 = j
    · have h' : e'.1.2 = j := h1 ▸ h
      by_cases hp : e.1.1 = p
      · have hp' : ¬ e'.1.1 = p := fun h3 => h2 (hp.trans h3.symm)
        rw [localNF_override, localNF_override, ite_eq_left h', ite_eq_right hp', map_zero,
          mul_zero]
      · rw [localNF_override, ite_eq_left h, ite_eq_right hp, map_zero, zero_mul]
    · have h' : ¬ e'.1.2 = j := fun h3 => h (h1.trans h3)
      rw [localNF_override, localNF_override, ite_eq_right h, ite_eq_right h', eval_X, eval_X]
      exact hα.1 e e' h1 h2
  · intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · refine ⟨⟨(p, j), hj⟩, h.symm, ?_⟩
      show eval α (localNF_override G p j ⟨(p, j), hj⟩) = 1
      rw [localNF_override, ite_eq_left rfl, ite_eq_left rfl, map_one]
    · obtain ⟨e, he, h1⟩ := hα.2 i h
      have hne : ¬ e.1.2 = j := by
        intro h3
        refine hjS (Finset.mem_biUnion.mpr ⟨i, h, ?_⟩)
        rw [← he, ← h3]
        exact e.2
      refine ⟨e, he, ?_⟩
      show eval α (localNF_override G p j e) = 1
      rw [localNF_override, ite_eq_right hne, eval_X, h1]


theorem localNF_override_monomial_one (p : Fin m) (j : Fin N) (c : GEdge G →₀ ℕ) :
    bind₁ (localNF_override G p j) (monomial c 1) = 0 ∨
      bind₁ (localNF_override G p j) (monomial c 1) = monomial (localNF_drop G j c) 1 := by
  rw [bind₁_monomial, C_1, one_mul]
  by_cases hz : ∃ e ∈ c.support, e.1.2 = j ∧ ¬ e.1.1 = p
  · obtain ⟨e, he, h1, h2⟩ := hz
    left
    refine Finset.prod_eq_zero he ?_
    rw [localNF_override, ite_eq_left h1, ite_eq_right h2, zero_pow (Finsupp.mem_support_iff.mp he)]
  · right
    have hz' : ∀ e ∈ c.support, e.1.2 = j → e.1.1 = p := fun e he h =>
      by_contra fun h2 => hz ⟨e, he, h, h2⟩
    rw [monomial_eq, C_1, one_mul, Finsupp.prod, localNF_drop, Finsupp.support_filter,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun e he => ?_
    by_cases h : e.1.2 = j
    · rw [ite_eq_right (not_not.mpr h), localNF_override, ite_eq_left h,
        ite_eq_left (hz' e he h), one_pow]
    · rw [ite_eq_left h, Finsupp.filter_apply_pos (p := fun e : GEdge G => e.1.2 ≠ j) (f := c) h,
        localNF_override, ite_eq_right h]


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


theorem localNF_override_mem_restrictSupport (p : Fin m) (j : Fin N) {b : GEdge G →₀ ℕ}
    {w : MvPolynomial (GEdge G) (ZMod 2)}
    (hw : w ∈ restrictSupport (ZMod 2) {d : GEdge G →₀ ℕ | MonoLt d b}) :
    bind₁ (localNF_override G p j) w
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
  rcases localNF_override_monomial_one G p j c with h | h
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


theorem nf_locIdeal_insert {S : Finset (Fin m)} {p : Fin m} {j : Fin N}
    (hp : p ∉ S) (hj : j ∈ G p) (hjS : j ∉ S.biUnion G) {a : GEdge G →₀ ℕ}
    (ha : j ∉ monoHoles G a) :
    nf (locIdeal G (insert p S)) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have _ := hp
  refine nf_unique (locIdeal G (insert p S)) ?_ ?_
  · intro b hb hmem
    have hstd := nf_support_isStd (locIdeal G S) (monomial a 1) b hb
    refine hstd ?_
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hmem
    have hbj : j ∉ monoHoles G b := by
      intro h
      rcases Finset.mem_union.mp (nf_locIdeal_holes G S a b hb h) with h' | h'
      · exact ha h'
      · exact hjS h'
    have himg := congrArg (bind₁ (localNF_override G p j)) huw
    rw [map_add, localNF_override_monomial_of_notMem G p hbj] at himg
    rw [← himg]
    exact Submodule.add_mem_sup (localNF_override_mem G hj hjS hu)
      (localNF_override_mem_restrictSupport G p j hw)
  · exact locIdeal_mono G (Finset.subset_insert p S)
      (nf_sub_mem (locIdeal G S) (monomial a 1))


theorem nf_locIdeal_ext {s : ℕ} {K : Finset (Fin N)} {S T : Finset (Fin m)}
    (hcl : SuppClosed G s K S) (hST : S ⊆ T) (hT : T.card ≤ s)
    {a : GEdge G →₀ ℕ} (ha : monoHoles G a ⊆ K) :
    nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
  have key : ∀ n : ℕ, ∀ T : Finset (Fin m), S ⊆ T → T.card ≤ s → T.card = n →
      nf (locIdeal G T) (monomial a 1) = nf (locIdeal G S) (monomial a 1) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hST hT hn
      by_cases hTS : T = S
      · rw [hTS]
      · have hlt : S ⊂ T := hST.ssubset_of_ne (Ne.symm hTS)
        obtain ⟨p, hpT, hpS, j, hj, hjK, hjT⟩ := SuppClosed.peel (G := G) hcl hlt hT
        have h1 := nf_locIdeal_insert G (S := T.erase p) (p := p) (j := j) (by simp) hj hjT
          (a := a) (fun h => hjK (ha h))
        rw [Finset.insert_erase hpT] at h1
        rw [h1]
        refine ih (T.erase p).card ?_ (T.erase p) ?_ ?_ rfl
        · rw [← hn]
          exact Finset.card_erase_lt_of_mem hpT
        · exact Finset.subset_erase.mpr ⟨hST, hpS⟩
        · exact (Finset.card_erase_le).trans hT
  exact key T.card T hST hT rfl

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)


noncomputable def pseudoR (s : ℕ) :
    MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2) :=
  (basisMonomials (GEdge G) (ZMod 2)).constr (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1))

theorem pseudoR_monomial (s : ℕ) (a : GEdge G →₀ ℕ) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1) := by
  have h := Module.Basis.constr_basis (basisMonomials (GEdge G) (ZMod 2)) (ZMod 2)
    (fun a => nf (locIdeal G (supp G s (monoHoles G a))) (monomial a 1)) a
  simpa only [pseudoR, coe_basisMonomials] using h


theorem monoHoles_add_single (a : GEdge G →₀ ℕ) (v : GEdge G) :
    monoHoles G (a + Finsupp.single v 1) = insert v.1.2 (monoHoles G a) := by
  unfold monoHoles
  rw [support_add_single_one, Finset.image_insert]


theorem monoHoles_subset_of_vars {f : MvPolynomial (GEdge G) (ZMod 2)} {K : Finset (Fin N)}
    (h : ∀ e ∈ f.vars, e.1.2 ∈ K) : ∀ a ∈ f.support, monoHoles G a ⊆ K := by
  classical
  intro a ha j hj
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
  exact h e ((mem_vars_iff_mem_support e).mpr ⟨a, ha, he⟩)


theorem pseudoR_monomial_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {a : GEdge G →₀ ℕ} (ha : a.degree ≤ D)
    (haK : monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s (monomial a 1) = nf (locIdeal G (supp G s K)) (monomial a 1) := by
  rw [pseudoR_monomial]
  have h3 := card_monoHoles_le G a
  have hH : (monoHoles G a).card ≤ s := h3.trans (ha.trans hD)
  have hKs : K.card ≤ s := hK.trans hD
  have h1 := two_mul_card_supp_le G hG hH
  have h2 := two_mul_card_supp_le G hG hKs
  have hT : (supp G s (monoHoles G a) ∪ supp G s K).card ≤ s := by
    have := Finset.card_union_le (supp G s (monoHoles G a)) (supp G s K)
    omega
  have e1 := nf_locIdeal_ext G (suppClosed_supp G hG hH) Finset.subset_union_left hT
    (subset_refl (monoHoles G a))
  have e2 := nf_locIdeal_ext G (SuppClosed.mono G (suppClosed_supp G hG hKs) haK)
    Finset.subset_union_right hT (subset_refl (monoHoles G a))
  exact e1.symm.trans e2

theorem pseudoR_eq_nf {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    {K : Finset (Fin N)} (hK : K.card ≤ D) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ D)
    (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K ∪ (supp G s K).biUnion G) :
    pseudoR G s f = nf (locIdeal G (supp G s K)) f := by
  have hf' : f = ∑ a ∈ f.support, f.coeff a • monomial a (1 : ZMod 2) := by
    conv_lhs => rw [f.as_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [smul_monomial, smul_eq_mul, mul_one]
  have e : ∀ L : MvPolynomial (GEdge G) (ZMod 2) →ₗ[ZMod 2] MvPolynomial (GEdge G) (ZMod 2),
      L f = ∑ a ∈ f.support, f.coeff a • L (monomial a 1) := by
    intro L
    conv_lhs => rw [hf']
    simp only [map_sum, map_smul]
  rw [e (pseudoR G s), e (nf (locIdeal G (supp G s K)))]
  exact Finset.sum_congr rfl fun a ha => by
    rw [pseudoR_monomial_eq_nf G hG hD hK ((le_totalDegree ha).trans hf) (hfK a ha)]

theorem pseudoR_mul {s D : ℕ} (hG : IsBdryExpander G s 2) (hD : D ≤ s)
    (v : GEdge G) (a : GEdge G →₀ ℕ) (ha : a.degree + 1 ≤ D) :
    pseudoR G s (X v * monomial a 1) = pseudoR G s (X v * pseudoR G s (monomial a 1)) := by
  have hdeg : (a + Finsupp.single v 1).degree = a.degree + 1 := by
    rw [map_add, Finsupp.degree_single]
  have hK0 : (monoHoles G (a + Finsupp.single v 1)).card ≤ D :=
    (card_monoHoles_le G _).trans (by omega)
  have hmono : X v * monomial a (1 : ZMod 2) = monomial (a + Finsupp.single v 1) 1 := by
    rw [mul_comm, monomial_one_mul_X]
  have haK0 : monoHoles G a ⊆ monoHoles G (a + Finsupp.single v 1) := by
    rw [monoHoles_add_single]
    exact Finset.subset_insert _ _
  have e1 : pseudoR G s (monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1) :=
    pseudoR_monomial_eq_nf G hG hD hK0 (by omega) (haK0.trans Finset.subset_union_left)
  have e2 : pseudoR G s (X v * monomial a 1)
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * monomial a 1) := by
    rw [hmono]
    exact pseudoR_monomial_eq_nf G hG hD hK0 (by omega) Finset.subset_union_left
  have hq : (nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
      (monomial a 1)).totalDegree ≤ a.degree :=
    (totalDegree_nf_le _ _).trans (totalDegree_monomial_one a).le
  have e3 : pseudoR G s (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
        (monomial a 1))
      = nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
          (X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))))
            (monomial a 1)) := by
    refine pseudoR_eq_nf G hG hD hK0 ?_ ?_
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega
    · intro b hb
      rw [mul_comm, support_mul_X] at hb
      obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hb
      have hc' := nf_locIdeal_holes G _ a c hc
      rw [addRightEmbedding_apply, monoHoles_add_single]
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · refine Finset.mem_union_left _ ?_
        rw [monoHoles_add_single]
        exact Finset.mem_insert_self _ _
      · rcases Finset.mem_union.mp (hc' hj) with h | h
        · exact Finset.mem_union_left _ (haK0 h)
        · exact Finset.mem_union_right _ h
  rw [e1, e2, e3]
  have hmem : X v * monomial a 1
      - X v * nf (locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1)))) (monomial a 1)
      ∈ locIdeal G (supp G s (monoHoles G (a + Finsupp.single v 1))) := by
    rw [← mul_sub]
    exact X_mul_mem_locIdeal G v (nf_sub_mem _ _)
  have h0 := (nf_eq_zero_iff _ _).mpr hmem
  rw [map_sub, sub_eq_zero] at h0
  exact h0


theorem pseudoR_eq_zero_of_mem {s : ℕ} (hG : IsBdryExpander G s 2)
    {K : Finset (Fin N)} (hK : K.card ≤ s) {f : MvPolynomial (GEdge G) (ZMod 2)}
    (hf : f.totalDegree ≤ s) (hfK : ∀ a ∈ f.support, monoHoles G a ⊆ K)
    (hmem : f ∈ locIdeal G (supp G s K)) : pseudoR G s f = 0 := by
  rw [pseudoR_eq_nf G hG le_rfl hK hf (fun a ha => (hfK a ha).trans Finset.subset_union_left)]
  exact (nf_eq_zero_iff _ _).mpr hmem

theorem pseudoR_axiom {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s) (hD : D ≤ s)
    {f : MvPolynomial (GEdge G) (ZMod 2)} (hf : f ∈ cnfSystem (graphPHP G))
    (hdeg : f.totalDegree ≤ D) : pseudoR G s f = 0 := by
  rcases cnfSystem_graphPHP_cases G hf with ⟨v, rfl⟩ | ⟨i, rfl⟩ | ⟨e, e', h1, h2, rfl⟩
  · refine pseudoR_eq_zero_of_mem G hG (K := {v.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (bool_mem_locIdeal G _ v)
    intro u hu
    rcases Finset.mem_union.mp (vars_add_subset _ _ hu) with h | h
    · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h <;>
      · rw [vars_X, Finset.mem_singleton] at h
        rw [h]
        exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
  · refine pseudoR_eq_zero_of_mem G hG (K := G i) ?_ (hdeg.trans hD)
      (monoHoles_pigeonClause G i)
      (pigeon_mem_locIdeal G (mem_supp_self G hs i (subset_refl _)))
    rw [← totalDegree_pigeonClause G i]
    exact hdeg.trans hD
  · refine pseudoR_eq_zero_of_mem G hG (K := {e.1.2}) (by simpa using hs) (hdeg.trans hD)
      (monoHoles_subset_of_vars G ?_) (hole_mem_locIdeal G _ h1 h2)
    intro u hu
    rcases Finset.mem_union.mp (vars_mul _ _ hu) with h | h
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_singleton_self _
    · rw [vars_X, Finset.mem_singleton] at h
      rw [h, ← h1]
      exact Finset.mem_singleton_self _

theorem pseudoR_one {s : ℕ} (hG : IsBdryExpander G s 2) : pseudoR G s 1 ≠ 0 := by
  have hm : monoHoles G (0 : GEdge G →₀ ℕ) = ∅ := by
    unfold monoHoles
    rw [Finsupp.support_zero, Finset.image_empty]
  have h0 : supp G s (monoHoles G (0 : GEdge G →₀ ℕ)) = ∅ := by
    rw [hm]
    have h := two_mul_card_supp_le G hG (H := ∅) (Nat.zero_le s)
    rw [Finset.card_empty] at h
    exact Finset.card_eq_zero.mp (by omega)
  have h1 : pseudoR G s 1 = nf (locIdeal G ∅) 1 := by
    have h := pseudoR_monomial G s 0
    rw [h0] at h
    exact h
  rw [h1]
  exact fun h => one_not_mem_locIdeal_empty G ((nf_eq_zero_iff _ _).mp h)

theorem graphPHP_no_pc_refutation {s D : ℕ} (hG : IsBdryExpander G s 2) (hs : 1 ≤ s)
    (hD : D ≤ s) : ¬ PCRefutable (cnfSystem (graphPHP G)) D :=
  not_pcRefutable_of_pseudoReduction (pseudoR G s)
    (fun _ hf hdeg => pseudoR_axiom G hG hs hD hf hdeg)
    (fun v a ha => pseudoR_mul G hG hD v a ha)
    (pseudoR_one G hG)

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)


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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)




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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core.Helpers
open PEqualNP.ProofComplexity PEqualNP

open MvPolynomial
open PEqualNP.Expanders

variable {m N : ℕ} (G : BipGraph m N)


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

end PEqualNP.Outside.L_pcx_402_aux.Core.Helpers

namespace PEqualNP.Outside.L_pcx_402_aux.Core
open PEqualNP.ProofComplexity PEqualNP


theorem L049 : ∀ (m N : ℕ) (G : PEqualNP.Expanders.BipGraph m N) (s d D : ℕ), PEqualNP.Expanders.IsBdryExpander G s 2 → PEqualNP.Expanders.LeftDegLe G d → 1 ≤ s → d * D ≤ s → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem (PEqualNP.Expanders.funGraphPHP G)) D :=
  fun _ _ G _ _ _ hG hd hs hB => Helpers.funGraphPHP_no_pc_refutation G hG hd hs hB

end PEqualNP.Outside.L_pcx_402_aux.Core

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.ProofComplexity PEqualNP.Expanders
theorem card_gedge_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    Fintype.card (GEdge G) ≤ m * b := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      ((Finset.univ.filter (fun e : Fin m × Fin N => e.2 ∈ G e.1)).filter
        (fun e => e.1 = i)).card ≤ b := by
    intro i _
    refine le_trans (Finset.card_le_card_of_injOn Prod.snd ?_ ?_) (hb i)
    · intro e he
      have he' := Finset.mem_filter.mp (Finset.mem_coe.mp he)
      have h1 := (Finset.mem_filter.mp he'.1).2
      rw [he'.2] at h1
      exact Finset.mem_coe.mpr h1
    · intro e he e' he' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp he)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp he')).2
      exact Prod.ext (h1.trans h2.symm) h
  calc _ ≤ ∑ _i : Fin m, b := Finset.sum_le_sum hfib
    _ = m * b := by simp


theorem graphPHP_width {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hb : LeftDegLe G b) :
    ∀ C ∈ graphPHP G, C.card ≤ max b 2 := by
  classical
  intro C hC
  rcases hC with ⟨i, rfl⟩ | ⟨e, e', -, -, rfl⟩
  · refine le_trans (le_trans
      (Finset.card_le_card_of_injOn (fun l : Literal (GEdge G) => l.1.1.2) ?_ ?_) (hb i))
      (le_max_left _ _)
    · intro l hl
      have hl' := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h1 : l.1.1.2 ∈ G l.1.1.1 := l.1.2
      rw [hl'.1] at h1
      exact Finset.mem_coe.mpr h1
    · intro l hl l' hl' h
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hl')).2
      exact Prod.ext (Subtype.ext (Prod.ext (h1.1.trans h2.1.symm) h)) (h1.2.trans h2.2.symm)
  · exact le_trans Finset.card_le_two (le_max_right _ _)


theorem graphPHP_unsat {m N : ℕ} (G : BipGraph m N) (h : N < m) :
    ¬ Satisfiable (graphPHP G) := by
  classical
  rintro ⟨a, ha⟩
  have hp : ∀ i : Fin m, ∃ e : GEdge G, e.1.1 = i ∧ a e = true := by
    intro i
    obtain ⟨l, hl, hal⟩ := ha _ (Or.inl ⟨i, rfl⟩)
    have h2 := (Finset.mem_filter.mp hl).2
    exact ⟨l.1, h2.1, by rw [hal, h2.2]⟩
  choose g hg1 hg2 using hp
  obtain ⟨i, i', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i => (g i).1.2)
    (by simpa using h)
  obtain ⟨l, hl, hal⟩ := ha _ (Or.inr ⟨g i, g i', heq, by rw [hg1, hg1]; exact hne, rfl⟩)
  rcases Finset.mem_insert.mp hl with rfl | hl
  · simp [hg2] at hal
  · rw [Finset.mem_singleton] at hl
    subst hl
    simp [hg2] at hal


theorem card_pairs_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hR : RightDegLe G b) :
    ((Finset.univ : Finset (GEdge G × GEdge G)).filter (fun p => p.1.1.2 = p.2.1.2)).card
      ≤ Fintype.card (GEdge G) * b := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  have hfib : ∀ e ∈ (Finset.univ : Finset (GEdge G)),
      (((Finset.univ : Finset (GEdge G × GEdge G)).filter
        (fun p => p.1.1.2 = p.2.1.2)).filter (fun p => p.1 = e)).card ≤ b := by
    intro e _
    refine le_trans (Finset.card_le_card_of_injOn (t := rightNbrs G e.1.2)
      (fun p : GEdge G × GEdge G => p.2.1.1) ?_ ?_) (hR e.1.2)
    · intro p hp
      have hp' := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have h1 := (Finset.mem_filter.mp hp'.1).2
      have h2 : p.2.1.2 ∈ G p.2.1.1 := p.2.2
      rw [← h1, hp'.2] at h2
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩)
    · intro p hp p' hp' h
      have hq := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hp')
      have h1 := (Finset.mem_filter.mp hq.1).2
      have h1' := (Finset.mem_filter.mp hq'.1).2
      have e1 : p.1 = p'.1 := hq.2.trans hq'.2.symm
      have e2 : p.2.1.2 = p'.2.1.2 := by rw [← h1, ← h1', e1]
      exact Prod.ext e1 (Subtype.ext (Prod.ext h e2))
  calc _ ≤ ∑ _e : GEdge G, b := Finset.sum_le_sum hfib
    _ = Fintype.card (GEdge G) * b := by simp


theorem card_graphPHP_le {m N : ℕ} (G : BipGraph m N) (b : ℕ) (hL : LeftDegLe G b)
    (hR : RightDegLe G b) [Fintype ↥(graphPHP G)] :
    Fintype.card ↥(graphPHP G) ≤ m + m * b * b := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (GEdge G × GEdge G),
      S = Finset.univ.filter (fun p => p.1.1.2 = p.2.1.2) := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Finset (Clause (GEdge G)),
      T = (Finset.univ : Finset (Fin m)).image
          (fun i => Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true))
        ∪ S.image (fun p => {(p.1, false), (p.2, false)}) := ⟨_, rfl⟩
  have hsub : ∀ C, C ∈ graphPHP G → C ∈ T := by
    rintro C (⟨i, rfl⟩ | ⟨e, e', h, -, rfl⟩)
    · rw [hT]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · rw [hT]
      refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(e, e'), ?_, rfl⟩)
      rw [hS]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
  have hinj : Function.Injective
      (fun x : ↥(graphPHP G) => (⟨x.1, hsub x.1 x.2⟩ : {C // C ∈ T})) :=
    fun x y h => Subtype.ext (congrArg (fun z : {C // C ∈ T} => z.1) h)
  have hSc : S.card ≤ m * b * b := by
    rw [hS]
    exact le_trans (card_pairs_le G b hR)
      (Nat.mul_le_mul_right _ (card_gedge_le G b hL))
  have hTc : T.card ≤ m + S.card := by
    rw [hT]
    refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add ?_ Finset.card_image_le)
    refine le_trans Finset.card_image_le ?_
    simp
  calc Fintype.card ↥(graphPHP G) ≤ Fintype.card {C // C ∈ T} :=
        Fintype.card_le_of_injective _ hinj
    _ = T.card := Fintype.card_coe T
    _ ≤ m + S.card := hTc
    _ ≤ m + m * b * b := Nat.add_le_add_left hSc _


end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
abbrev F2 := ZMod 2
abbrev Bits (b : ℕ) := Fin b → F2

lemma flat_kernel {b : ℕ} {X : Type} [AddCommGroup X] [Module F2 X] [FiniteDimensional F2 X]
    (S : Finset (Bits b)) (msg : X → Bits b) (inside : ∀ x, msg x ∈ S)
    (K : Submodule F2 X) (A : K →ₗ[F2] Bits b)
    (shift : ∀ (x : X) (u : K), msg (x + u.val) = msg x + A u) :
    ∃ W : Submodule F2 X,
      Module.finrank F2 (X ⧸ W) ≤ Module.finrank F2 (X ⧸ K) +
        sSup {k : ℕ | ∃ (U : Submodule F2 (Bits b)) (y : Bits b),
        Module.finrank F2 U = k ∧ ∀ u ∈ U, y + u ∈ S} ∧
      ∀ (x : X) (v : W), msg (x + v.val) = msg x := by
  let W := (LinearMap.ker A).map K.subtype
  refine ⟨W, ?_, ?_⟩
  · have hbounded : BddAbove {k : ℕ | ∃ (U : Submodule F2 (Bits b)) (y : Bits b),
          Module.finrank F2 U = k ∧ ∀ u ∈ U, y + u ∈ S} := by
      refine ⟨Module.finrank F2 (Bits b), ?_⟩
      rintro i ⟨U,y,rfl,_⟩
      exact U.finrank_le
    have hrange : Module.finrank F2 (LinearMap.range A) ≤ sSup {k : ℕ |
        ∃ (U : Submodule F2 (Bits b)) (y : Bits b), Module.finrank F2 U = k ∧
          ∀ u ∈ U, y + u ∈ S} := by
      apply le_csSup hbounded
      refine ⟨LinearMap.range A,msg 0,rfl,?_⟩
      rintro _ ⟨v,rfl⟩
      rw [← shift]
      exact inside _
    have hr := A.finrank_range_add_finrank_ker
    have hd := W.finrank_quotient_add_finrank
    have hd' := K.finrank_quotient_add_finrank
    have he : Module.finrank F2 W = Module.finrank F2 (LinearMap.ker A) :=
      (Submodule.equivMapOfInjective K.subtype K.subtype_injective _).finrank_eq.symm
    omega
  · intro x v
    obtain ⟨u,hu,hv⟩ := v.property
    change (u : X) = v.val at hv
    rw [← hv, shift, LinearMap.mem_ker.mp hu, add_zero]

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.CircuitLowerBounds
abbrev F := ZMod 2
variable {X : Type} [AddCommGroup X] [Module F X] [FiniteDimensional F X]

def z (b : Bool) : F := b.toNat
lemma z_inj : Function.Injective z := by decide
lemma z_xor (a b : Bool) : z (xor a b) = z a + z b := by revert a b; decide
lemma z_not (a : Bool) : z (!a) = 1 + z a := by revert a; decide

def Dir (K : Submodule F X) (f : X → Bool) : Prop :=
  ∃ a : X →ₗ[F] F, ∀ (x u : X), u ∈ K → z (f (x+u)) = z (f x) + a u

lemma dconst (K : Submodule F X) (b : Bool) : Dir K (fun _ => b) :=
  ⟨0,fun _ _ _ => by simp⟩
lemma dmono {K W : Submodule F X} {f : X → Bool} (h : Dir K f) (hw : W ≤ K) : Dir W f :=
  ⟨h.choose,fun x u hu => h.choose_spec x u (hw hu)⟩
lemma dxor {K : Submodule F X} {f g : X → Bool} (h : Dir K f) (h' : Dir K g) :
    Dir K (fun x => xor (f x) (g x)) := by
  obtain ⟨a,ha⟩ := h
  obtain ⟨b,hb⟩ := h'
  refine ⟨a+b, fun x u hu => ?_⟩
  simp only [z_xor,ha _ _ hu,hb _ _ hu,LinearMap.add_apply]
  abel
lemma dnot {K : Submodule F X} {f : X → Bool} (h : Dir K f) :
    Dir K (fun x => !(f x)) := by
  obtain ⟨a,ha⟩ := h
  exact ⟨a,fun x u hu => by simp [z_not,ha _ _ hu, add_assoc]⟩

lemma freeze_two {K : Submodule F X} {f g : X → Bool} (hf : Dir K f) (hg : Dir K g)
    (op : Bool → Bool → Bool) : ∃ W ≤ K,
    Module.finrank F (X ⧸ W) ≤ Module.finrank F (X ⧸ K) + 2 ∧ Dir W (fun x => op (f x) (g x)) := by
  obtain ⟨a,ha⟩ := hf
  obtain ⟨b,hb⟩ := hg
  let L := (a.prod b).domRestrict K
  let W := (LinearMap.ker L).map K.subtype
  have sub : W ≤ K := by rintro _ ⟨v,hv,rfl⟩; exact v.property
  refine ⟨W,sub,?_,0,?_⟩
  · have hd := L.finrank_range_add_finrank_ker
    have he : Module.finrank F W = Module.finrank F (LinearMap.ker L) :=
      (Submodule.equivMapOfInjective K.subtype K.subtype_injective _).finrank_eq.symm
    have h1 := K.finrank_quotient_add_finrank
    have h2 := W.finrank_quotient_add_finrank
    have h3 := (LinearMap.range L).finrank_le
    have : Module.finrank F (F × F) = 2 := by simp [Module.finrank_prod]
    omega
  · rintro x _ ⟨u,hu,rfl⟩
    have h0 : (a u.val,b u.val) = (0,0) := LinearMap.mem_ker.mp hu
    have h1 := ha x u.val u.property
    have h2 := hb x u.val u.property
    rw [show a u.val = 0 from congrArg Prod.fst h0, add_zero] at h1
    rw [show b u.val = 0 from congrArg Prod.snd h0, add_zero] at h2
    simp [z_inj h1,z_inj h2]

def rd (w : List (X → Bool)) (i : ℕ) := w.getD i (fun _ => false)
lemma read_ok {K : Submodule F X} {w : List (X → Bool)} (h : ∀ f ∈ w, Dir K f) (i : ℕ) :
    Dir K (rd w i) := by
  by_cases hi : i < w.length
  · rw [rd, List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [rd, List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    exact dconst _ _

lemma mod_ok {K : Submodule F X} (l : List (X → Bool)) (h : ∀ f ∈ l, Dir K f) :
    Dir K (fun x => GateOp.eval (.mod 2) (l.map (fun f => f x))) := by
  induction l with
  | nil => exact dconst _ true
  | cons f l ih =>
    convert dxor (h f (by simp)) (ih (fun g hg => h g (by simp [hg]))) using 1
    funext x
    cases e : f x <;> simp [GateOp.eval,e]
    generalize (List.map (fun f : X → Bool => f x) l).count true = m
    by_cases hm : m % 2 = 0 <;> simp [hm] <;> omega

noncomputable def charged (g : Gate) : Bool :=
  @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)
def OK (g : Gate) := ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)
def form (w : List (X → Bool)) (g : Gate) := fun x : X => g.op.eval (g.inputs.map (fun i => rd w i x))
def wireForms (gs : List Gate) (w : List (X → Bool)) :=
  gs.foldl (fun v g => v ++ [form v g]) w

lemma gate_dir {K : Submodule F X} (g : Gate) (ok : OK g) (w : List (X → Bool))
    (hw : ∀ f ∈ w, Dir K f) : ∃ W ≤ K,
      Module.finrank F (X ⧸ W) ≤ Module.finrank F (X ⧸ K) + (if charged g then 2 else 0) ∧
      Dir W (form w g) := by
  change ∃ W ≤ K, _ ∧ Dir W (fun x => g.op.eval (g.inputs.map (fun i => rd w i x)))
  rcases ok with ⟨hop,hlen⟩ | hmod | ⟨hnot,hlen⟩
  · obtain ⟨i,j,hij⟩ : ∃ i j, g.inputs = [i,j] := by
      generalize g.inputs = l at hlen ⊢
      obtain _ | ⟨i,l⟩ := l <;> simp_all
      obtain _ | ⟨j,l⟩ := l <;> simp_all
    simpa [form,hij,charged,hop] using freeze_two (read_ok hw i) (read_ok hw j)
      (fun a b => g.op.eval [a,b])
  · refine ⟨K,le_refl _,by simp [charged,hmod],?_⟩
    simpa [form,hmod,List.map_map,Function.comp_def] using
      mod_ok (g.inputs.map (rd w)) (by
        intro f hf
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
        exact read_ok hw i)
  · obtain ⟨i,hi⟩ : ∃ i, g.inputs = [i] := by
      generalize g.inputs = l at hlen ⊢
      obtain _ | ⟨i,l⟩ := l <;> simp_all
    refine ⟨K,le_refl _,by simp [charged,hnot],?_⟩
    simpa [form,hi,hnot,GateOp.eval] using dnot (read_ok hw i)

lemma circuit_dir (gs : List Gate) (ok : ∀ g ∈ gs, OK g) (K : Submodule F X)
    (w : List (X → Bool)) (hw : ∀ f ∈ w, Dir K f) :
    ∃ W : Submodule F X,
      Module.finrank F (X ⧸ W) ≤ Module.finrank F (X ⧸ K) + 2*gs.countP charged ∧
      ∀ f ∈ wireForms gs w, Dir W f := by
  induction gs generalizing w K with
  | nil => exact ⟨K,by simp,hw⟩
  | cons g gs ih =>
    obtain ⟨K',hle,hr,hg⟩ := gate_dir g (ok _ (by simp)) w hw
    obtain ⟨W,hW,hw'⟩ := ih (fun a ha => ok a (by simp [ha])) K' (w ++ [form w g]) (by
      intro f hf
      rcases List.mem_append.mp hf with h | h
      · exact dmono (hw _ h) hle
      · simpa [List.mem_singleton.mp h] using hg)
    refine ⟨W,?_,hw'⟩
    cases h : charged g <;> simp [List.countP_cons,h] at hr ⊢ <;> omega

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open MvPolynomial
abbrev R := ZMod 2
variable {V : Type} [Fintype V]
noncomputable def linpoly (f : (V → R) →ₗ[R] R) : MvPolynomial V R :=
  ∑ v, C (f (Pi.basisFun R V v)) * X v

lemma linpoly_deg (f : (V → R) →ₗ[R] R) : (linpoly f).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro v _
  exact (totalDegree_mul _ _).trans (by simp)

lemma linpoly_eval (f : (V → R) →ₗ[R] R) (x : V → R) : eval x (linpoly f) = f x := by
  classical
  have h := congrArg f ((Pi.basisFun R V).sum_repr x)
  simpa [linpoly,map_sum,map_smul,smul_eq_mul,Pi.basisFun_repr,mul_comm] using h

noncomputable def testpoly {d : ℕ} (l : Fin d → (V → R) →ₗ[R] R)
    (y : Fin d → R) : MvPolynomial V R :=
  ∏ i, (1+C (y i)+linpoly (l i))

lemma testpoly_deg {d : ℕ} (l : Fin d → (V → R) →ₗ[R] R) (y : Fin d → R) :
    (testpoly l y).totalDegree ≤ d := by
  apply (totalDegree_finsetProd _ _).trans
  calc _ ≤ ∑ _ : Fin d, 1 := Finset.sum_le_sum fun i _ =>
         (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (by simp)) (linpoly_deg _))
       _ = _ := by simp

lemma testpoly_eval {d : ℕ} (l : Fin d → (V → R) →ₗ[R] R) (y : Fin d → R) (x : V → R) :
    eval x (testpoly l y) = if y = (fun i => l i x) then 1 else 0 := by
  classical
  simp only [testpoly,map_prod,map_add,map_one,eval_C,linpoly_eval]
  have val : ∀ a b : R, 1+a+b = if a = b then 1 else 0 := by decide
  by_cases h : y = fun i => l i x
  · rw [if_pos h]
    exact Finset.prod_eq_one (fun i _ => by rw [val,congrFun h i,if_pos rfl])
  · rw [if_neg h]
    obtain ⟨j,hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [val,if_neg hj])

lemma quotient_indicators (W : Submodule R (V → R)) :
    let d := Module.finrank R ((V → R) ⧸ W)
    ∃ (p : (Fin d → R) → MvPolynomial V R) (rep : (Fin d → R) → (V → R)),
      (∀ y, (p y).totalDegree ≤ d) ∧
      (∀ x : V → R, ∑ y, eval x (p y) = 1) ∧
      ∀ y (x : V → R), eval x (p y) ≠ 0 → x - rep y ∈ W := by
  classical
  intro d
  let B := Module.finBasis R ((V → R) ⧸ W)
  let l := fun i : Fin d => (B.coord i).comp W.mkQ
  let rep := fun y : Fin d → R => (W.mkQ_surjective (B.equivFun.symm y)).choose
  refine ⟨testpoly l,rep,testpoly_deg l,?_,?_⟩
  · intro x
    simp [testpoly_eval]
  · intro y x hx
    rw [testpoly_eval] at hx
    have hy : y = fun i => l i x := by split at hx <;> simp_all
    apply (Submodule.Quotient.eq W).mp
    change W.mkQ x = W.mkQ (rep y)
    rw [(W.mkQ_surjective _).choose_spec]
    apply B.equivFun.injective
    rw [B.equivFun.apply_symm_apply,hy]
    rfl

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open MvPolynomial PEqualNP.ProofComplexity
variable {σ τ : Type}


theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)


theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
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


theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))


theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
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
theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]


noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v


noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

theorem boolDerivable_monomial (d : ℕ) :
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


theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
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

theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
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
theorem z2_lit : ∀ (b : Bool) (z : ZMod 2),
    (if b = true then 1 + z else z) = if decide (z = 1) = b then 0 else 1 := by decide

open Classical in

theorem eval_clausePoly {σ : Type} (x : σ → ZMod 2) (C : Clause σ) :
    eval x (clausePoly C) = if ClauseSat (fun v => decide (x v = 1)) C then 0 else 1 := by
  unfold clausePoly
  rw [map_prod]
  have hf : ∀ l ∈ C, eval x (if l.2 = true then 1 + X l.1 else X l.1) =
      if decide (x l.1 = 1) = l.2 then 0 else 1 := by
    intro l _
    rw [apply_ite (eval x), map_add, map_one, eval_X]
    exact z2_lit l.2 (x l.1)
  rw [Finset.prod_congr rfl hf]
  by_cases h : ClauseSat (fun v => decide (x v = 1)) C
  · rw [if_pos h]
    obtain ⟨l, hl, hs⟩ := h
    exact Finset.prod_eq_zero hl (if_pos hs)
  · rw [if_neg h]
    exact Finset.prod_eq_one fun l hl => if_neg fun hs => h ⟨l, hl, hs⟩


abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

lemma twice_zero {V : Type} (p : Poly V) : p+p=0 := by
  rw [← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul]

lemma clause_degree {V : Type} (c : Clause V) : (clausePoly c).totalDegree ≤ c.card := by
  classical
  unfold clausePoly
  refine (totalDegree_finsetProd _ _).trans ?_
  calc _ ≤ ∑ _ ∈ c, 1 := Finset.sum_le_sum (fun l _ => by
         split_ifs
         · exact (totalDegree_add _ _).trans (by simp)
         · simp)
       _ = _ := by simp

lemma leaf_indicator {V : Type} (F : Set (Clause V)) (w B : ℕ)
    (l : List (Clause V)) (p : Poly V)
    (valid : ∀ c ∈ l, c ∈ F ∧ c.card ≤ w)
    (deg : p.totalDegree + w*l.length ≤ B)
    (hit : ∀ x : V → ZMod 2, eval x p ≠ 0 → ∃ c ∈ l, ¬ ClauseSat (fun v => decide (x v = 1)) c) :
    PCDerivable (cnfSystem F) B p := by
  classical
  induction l generalizing p with
  | nil =>
    apply vanish_derivable
    · exact fun v => Or.inl ⟨v,rfl⟩
    · simpa using deg
    · intro x
      by_contra h
      simpa using hit x h
  | cons c l ih =>
    obtain ⟨hc, hw⟩ := valid c List.mem_cons_self
    have hd := (clause_degree c).trans hw
    have hd' : (1 + clausePoly c).totalDegree ≤ w :=
      (totalDegree_add _ _).trans (max_le (by simp) hd)
    have hh : p.totalDegree + w + w*l.length ≤ B := by
      simpa [List.length_cons, Nat.mul_add, Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using deg
    have h1 := ih (p * (1 + clausePoly c))
      (fun a ha => valid a (List.mem_cons_of_mem _ ha))
      ((Nat.add_le_add_right ((totalDegree_mul _ _).trans (Nat.add_le_add_left hd' _)) _).trans hh) (by
        intro x hx
        rw [map_mul, map_add, map_one] at hx
        obtain ⟨a, ha, hab⟩ := hit x (left_ne_zero_of_mul hx)
        rcases List.mem_cons.mp ha with rfl | ha
        · rw [eval_clausePoly, if_neg hab] at hx
          simp [show (1 + 1 : ZMod 2) = 0 from rfl] at hx
        · exact ⟨a, ha, hab⟩)
    have h2 : PCDerivable (cnfSystem F) B (clausePoly c) :=
      .ax (Or.inr ⟨c,hc,rfl⟩) (by omega)
    have h3 := pcDerivable_mono (pcDerivable_mul_left h2 p)
      (max_le (le_refl B) (by omega)) (Set.Subset.refl _)
    have h4 := h1.add h3
    simpa [mul_add, add_assoc, twice_zero] using h4

lemma glue_indicators {V I : Type} [Fintype I] (F : Set (Clause V)) (w r k : ℕ)
    (p : I → Poly V) (l : I → List (Clause V))
    (valid : ∀ i, ∀ c ∈ l i, c ∈ F ∧ c.card ≤ w)
    (bound : ∀ i, (p i).totalDegree ≤ r ∧ (l i).length ≤ k)
    (partition : ∀ x : V → ZMod 2, ∑ i, eval x (p i) = 1)
    (hit : ∀ i (x : V → ZMod 2), eval x (p i) ≠ 0 →
      ∃ c ∈ l i, ¬ ClauseSat (fun v => decide (x v = 1)) c) :
    PCRefutable (cnfSystem F) (r+w*k) := by
  classical
  have h1 := pcDerivable_sum Finset.univ p (fun i _ => leaf_indicator F w (r+w*k)
    (l i) (p i) (valid i) (Nat.add_le_add (bound i).1 (Nat.mul_le_mul_left _ (bound i).2)) (hit i))
  have hd : (∑ i, p i).totalDegree ≤ r := by
    apply totalDegree_finsetSum_le
    exact fun i _ => (bound i).1
  have h2 : PCDerivable (cnfSystem F) (r+w*k) (1+∑ i, p i) := by
    apply vanish_derivable
    · exact fun v => Or.inl ⟨v,rfl⟩
    · exact (totalDegree_add _ _).trans (max_le (by simp) (by omega))
    · intro x
      rw [map_add, map_one, map_sum, partition]
      decide
  simpa [PCRefutable, add_assoc, twice_zero] using h2.add h1

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.Expanders PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds
open Finset

abbrev pigeon {m n : ℕ} (G : BipGraph m n) (i : Fin m) : Clause (GEdge G) :=
  univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)

lemma small_match {m n s : ℕ} (G : BipGraph m n) (hexp : IsBdryExpander G s 2)
    (P : Finset (Fin m)) (hP : P.card ≤ s) :
    ∃ f : P → Fin n, Function.Injective f ∧ ∀ i : P, f i ∈ G i.val := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp
  intro t
  let A := t.map (Function.Embedding.subtype (· ∈ P))
  have hA : A.card = t.card := card_map _
  have hAs : A.card ≤ s := hA.le.trans ((t.card_le_univ.trans (by simp)).trans hP)
  have hsub : uniqueNbrs G A ⊆ t.biUnion (fun i : P => G i) := by
    intro j hj
    have h1 := (mem_filter.mp hj).2
    obtain ⟨i, hi⟩ := card_pos.mp (show 0 < (A.filter (fun i => j ∈ G i)).card by omega)
    obtain ⟨hiA,hjG⟩ := mem_filter.mp hi
    obtain ⟨v,hv,rfl⟩ := mem_map.mp hiA
    exact mem_biUnion.mpr ⟨v,hv,hjG⟩
  have := card_le_card hsub
  have := hexp A hAs
  omega

lemma small_sat {n s : ℕ} (G : BipGraph (n+1) n) (hexp : IsBdryExpander G s 2)
    (L : Finset (Clause (GEdge G))) (hL : ∀ c ∈ L, c ∈ funGraphPHP G)
    (hs : L.card ≤ s) : ∃ x, ∀ c ∈ L, ClauseSat x c := by
  classical
  let rep (c : Clause (GEdge G)) : Fin (n+1) :=
    if h : ∃ i, c = pigeon G i then h.choose else 0
  let P := L.image rep
  obtain ⟨f, hf, hmem⟩ := small_match G hexp P (card_image_le.trans hs)
  let x (e : GEdge G) := decide (∃ i : P, i.val = e.val.1 ∧ f i = e.val.2)
  refine ⟨x, fun c hc => ?_⟩
  by_cases h : ∃ i, c = pigeon G i
  · have hrep : c = pigeon G (rep c) := by simpa [rep, h] using h.choose_spec
    let i : P := ⟨rep c, mem_image_of_mem _ hc⟩
    let e : GEdge G := ⟨⟨rep c, f i⟩, hmem i⟩
    exact ⟨(e,true), hrep ▸ mem_filter.mpr ⟨mem_univ _, rfl, rfl⟩,
      decide_eq_true ⟨i, rfl, rfl⟩⟩
  · have pair_sat (a b : GEdge G)
        (inc : (a.val.2 = b.val.2 ∧ a.val.1 ≠ b.val.1) ∨
               (a.val.1 = b.val.1 ∧ a.val.2 ≠ b.val.2)) :
        ClauseSat x {(a,false),(b,false)} := by
      by_cases ha : x a = true
      · have hb : x b = false := by
          cases hxb : x b
          · rfl
          · obtain ⟨u, h1,h2⟩ := of_decide_eq_true ha
            obtain ⟨v, h3,h4⟩ := of_decide_eq_true hxb
            rcases inc with h' | h'
            · exact False.elim (h'.2 (h1.symm.trans ((congrArg Subtype.val (hf (h2.trans (h'.1.trans h4.symm)))).trans h3)))
            · exact False.elim (h'.2 (h2.symm.trans ((congrArg f (Subtype.ext (h1.trans (h'.1.trans h3.symm)))).trans h4)))
        exact ⟨(b,false),by simp,hb⟩
      · exact ⟨(a,false),by simp,by simpa using ha⟩
    rcases hL c hc with (hpos | ⟨a,b,h1,h2,rfl⟩) | ⟨a,b,h1,h2,rfl⟩
    · exact (h hpos).elim
    · exact pair_sat a b (Or.inl ⟨h1,h2⟩)
    · exact pair_sat a b (Or.inr ⟨h1,h2⟩)

lemma total_capacity {n s : ℕ} (G : BipGraph (n+1) n) (hexp : IsBdryExpander G s 2)
    {Y : Type} [DecidableEq Y] (S : Finset Y) (cap : Y → ℕ)
    (out : Y → Finset (Clause (GEdge G)))
    (valid : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ c ∈ out y, c ∈ funGraphPHP G)
    (cover : ∀ x, ∃ y ∈ S, ∃ c ∈ out y, ¬ ClauseSat x c) :
    s < ∑ y ∈ S, cap y := by
  classical
  by_contra! hs
  let L := S.biUnion out
  have hL : ∀ c ∈ L, c ∈ funGraphPHP G := by
    intro c hc
    obtain ⟨y,hy,hc⟩ := mem_biUnion.mp hc
    exact (valid y hy).2 c hc
  have hc : L.card ≤ s := (card_biUnion_le.trans (sum_le_sum (fun y hy => (valid y hy).1))).trans hs
  obtain ⟨x,hx⟩ := small_sat G hexp L hL hc
  obtain ⟨y,hy,c,hc,hbad⟩ := cover x
  exact hbad (hx c (mem_biUnion.mpr ⟨y,hy,hc⟩))

end PEqualNP.Outside.L_pcx_402_aux
namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.CircuitLowerBounds PEqualNP.ProofComplexity

lemma wire_eval {X : Type} (gs : List Gate) (w : List (X → Bool)) (x : X) :
    (wireForms gs w).map (fun f => f x) =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))])
        (w.map (fun f => f x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wireForms gs (w ++ [form w g])).map _ = _
    rw [ih]
    simp only [List.map_append, List.map_cons,List.map_nil,List.foldl_cons,form]
    congr 2
    simp only [rd, List.getD_map w (fun _ => false) (fun f => f x)]

def bitof (a : F) : Bool := decide (a=1)
lemma z_bitof (a : F) : z (bitof a) = a := by revert a; decide

abbrev inp {V : Type} [Fintype V] (o : Fin (Fintype.card V) ≃ V) : List ((V → F) → Bool) :=
  [fun _ => false, fun _ => true] ++ List.ofFn (fun i => fun x => bitof (x (o i)))

lemma inp_ok {V : Type} [Fintype V] (o : Fin (Fintype.card V) ≃ V) :
    ∀ f ∈ inp o, Dir ⊤ f := by
  intro f hf
  rcases List.mem_append.mp hf with h | h
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl <;> apply dconst
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
    exact ⟨LinearMap.proj (o i),fun x u _ => by simp [z_bitof]⟩

def msgZ {V : Type} [Fintype V] (o : Fin (Fintype.card V) ≃ V) (H : Circuit) {b : ℕ}
    (pick : Fin b → ℕ) (x : V → F) (i : Fin b) : F :=
  z ((H.wires ([false,true] ++ List.ofFn (fun j => bitof (x (o j))))).getD (pick i) false)

lemma msg_eq {V : Type} [Fintype V] (o : Fin (Fintype.card V) ≃ V) (H : Circuit) {b : ℕ}
    (pick : Fin b → ℕ) (x : V → F) (i : Fin b) :
    msgZ o H pick x i = z (rd (wireForms H.gates (inp o)) (pick i) x) := by
  unfold msgZ
  rw [← show (wireForms H.gates (inp o)).map (fun f => f x) = H.wires
    ([false,true] ++ List.ofFn (fun j => bitof (x (o j)))) by
      rw [wire_eval]
      simp [Circuit.wires,inp,List.map_ofFn,Function.comp_def]]
  rw [List.getD_map (wireForms H.gates (inp o)) (fun _ => false) (fun f => f x)]
  rfl

noncomputable abbrev flatRank {b : ℕ} (S : Finset (Bits b)) :=
  sSup {k : ℕ | ∃ (U : Submodule F (Bits b)) (y : Bits b),
      Module.finrank F U = k ∧ ∀ u ∈ U, y + u ∈ S}

lemma lower_pc {V : Type} [Fintype V] [DecidableEq V] (o : Fin (Fintype.card V) ≃ V)
    (Fml : Set (Clause V)) (w : ℕ) (width : ∀ c ∈ Fml, c.card ≤ w)
    (H : Circuit) {b : ℕ} (pick : Fin b → ℕ) (ok : ∀ g ∈ H.gates, OK g)
    (S : Finset (Bits b)) (cap : Bits b → ℕ) (out : Bits b → Finset (Clause V))
    (valid : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ c ∈ out y, c ∈ Fml)
    (hit : ∀ x : V → F, msgZ o H pick x ∈ S ∧ ∃ c ∈ out (msgZ o H pick x),
       ¬ ClauseSat (fun v => bitof (x v)) c) :
    PCRefutable (cnfSystem Fml) (2*H.gates.countP charged + flatRank S + w*S.sup cap) := by
  classical
  obtain ⟨K,hk,hf⟩ := circuit_dir H.gates ok ⊤ (inp o) (inp_ok o)
  have hk' : Module.finrank F ((V → F) ⧸ K) ≤ 2*H.gates.countP charged := by
    have htop := (⊤ : Submodule F (V → F)).finrank_quotient_add_finrank
    rw [finrank_top] at htop
    omega
  let l := fun i => (read_ok hf (pick i)).choose
  let A := (LinearMap.pi l).domRestrict K
  have shift (x : V → F) (u : K) : msgZ o H pick (x+u.val) = msgZ o H pick x + A u := by
    funext i
    simp only [Pi.add_apply,msg_eq]
    exact (read_ok hf (pick i)).choose_spec x u.val u.property
  obtain ⟨W,hd,hinv⟩ := flat_kernel S _ (fun x => (hit x).1) K A shift
  obtain ⟨p,rep,hdeg,hpart,hrep⟩ := quotient_indicators W
  let m := fun y => msgZ o H pick (rep y)
  apply glue_indicators Fml w (2*H.gates.countP charged + flatRank S) (S.sup cap) p
    (fun y => (out (m y)).toList)
  · intro y c hc
    have h := (valid _ (hit (rep y)).1).2 c (Finset.mem_toList.mp hc)
    exact ⟨h,width c h⟩
  · intro y
    exact ⟨(hdeg y).trans (hd.trans (Nat.add_le_add_right hk' _)),
      (Finset.length_toList _).le.trans ((valid _ (hit (rep y)).1).1.trans (Finset.le_sup (f:=cap) (hit (rep y)).1))⟩
  · exact hpart
  · intro y x hx
    let v : W := ⟨x-rep y,hrep y x hx⟩
    have he : msgZ o H pick x = m y := by
      simpa [v,m,add_sub_cancel] using hinv (rep y) v
    obtain ⟨c,hc,hc'⟩ := (hit x).2
    exact ⟨c, Finset.mem_toList.mpr (he ▸ hc),hc'⟩

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.CircuitLowerBounds PEqualNP.ProofComplexity
variable {X : Type}
abbrev Wires (X : Type) := List (X → Bool)

def Back : ℕ → List Gate → Prop
  | _,[] => True
  | n,g::gs => (∀ i ∈ g.inputs, i < n) ∧ Back (n+1) gs

lemma back_append {n : ℕ} {gs hs : List Gate} (h : Back n gs) (h' : Back (n+gs.length) hs) :
    Back n (gs++hs) := by
  induction gs generalizing n with
  | nil => simpa using h'
  | cons g gs ih =>
    exact ⟨h.1, ih h.2 (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h')⟩

lemma back_reads {n : ℕ} {gs : List Gate} (h : Back n gs) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n ⟨gs,0⟩ := by
  intro j hj i hi
  induction gs generalizing n j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simpa using h.1 i (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi)
    | succ j => exact (ih h.2 j (by simpa using hj) (by simpa [PEqualNP.MetaComplexity.NestedCover.gateAt] using hi)).trans_le (by omega)

lemma forms_length (gs : List Gate) (w : Wires X) :
    (wireForms gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wireForms]
  | cons g gs ih =>
    change (wireForms gs (w ++ [form w g])).length = _
    rw [ih]; simp; omega

lemma forms_subset (gs : List Gate) (w : Wires X) : w ⊆ wireForms gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    exact List.Subset.trans (List.subset_append_left ..) (ih (w ++ [form w g]))

def Run (w : Wires X) (t : ℕ) (v : Wires X) : Prop := ∃ gs : List Gate,
  Back w.length gs ∧ (∀ g ∈ gs, OK g) ∧ gs.countP charged ≤ t ∧ wireForms gs w = v

lemma Run.keep (w : Wires X) : Run w 0 w := ⟨[], trivial,by simp,by simp,rfl⟩
lemma Run.subset {w v : Wires X} {t} (h : Run w t v) : w ⊆ v := by
  obtain ⟨gs,_,_,_,rfl⟩ := h
  exact forms_subset gs w
lemma Run.weaken {w v : Wires X} {t u : ℕ} (h : Run w t v) (ht : t ≤ u) : Run w u v := by
  obtain ⟨gs,hb,ho,hc,he⟩ := h
  exact ⟨gs,hb,ho,hc.trans ht,he⟩
lemma Run.seq {w v w' : Wires X} {t u} (h : Run w t v) (h' : Run v u w') :
    Run w (t+u) w' := by
  obtain ⟨gs,hb,ho,hc,rfl⟩ := h
  obtain ⟨hs,hb',ho',hc',rfl⟩ := h'
  refine ⟨gs++hs,back_append hb (by rwa [forms_length] at hb'),?_,?_,?_⟩
  · intro g hg
    exact (List.mem_append.mp hg).elim (ho g) (ho' g)
  · rw [List.countP_append]; omega
  · simp [wireForms,List.foldl_append]

open Classical in
lemma make (w : Wires X) (fs : Wires X) (op : GateOp) (mem : fs ⊆ w)
    (ok : ((op = .and ∨ op = .or) ∧ fs.length = 2) ∨ op = .mod 2 ∨ (op = .not ∧ fs.length = 1)) :
    let f := fun x => op.eval (fs.map (fun a => a x))
    Run w (if op = .and ∨ op = .or then 1 else 0) (w++[f]) := by
  classical
  intro f
  let g : Gate := ⟨op,fs.map w.idxOf⟩
  refine ⟨[g],⟨?_,trivial⟩,?_,?_,?_⟩
  · rintro i hi
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hi
    exact List.idxOf_lt_length_of_mem (mem ha)
  · simpa [OK,g] using ok
  · simp [charged,g]
  · change w ++ [form w g] = w ++ [f]
    congr 2
    funext x
    apply congrArg op.eval
    simp only [g,List.map_map]
    apply List.map_congr_left
    intro a ha
    have hm := mem ha
    change w.getD _ _ x = a x
    rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hm), List.getElem_idxOf]

lemma build_not (w : Wires X) (a : X → Bool) (ha : a ∈ w) :
    ∃ v, Run w 0 v ∧ (fun x => !(a x)) ∈ v := by
  have h := make w [a] .not (by simpa using ha) (by simp)
  exact ⟨_,by simpa [GateOp.eval] using h, List.mem_append_right _ (by simp)⟩

lemma build_and (w : Wires X) (a b : X → Bool) (ha : a ∈ w) (hb : b ∈ w) :
    ∃ v, Run w 1 v ∧ (fun x => a x && b x) ∈ v := by
  have h := make w [a,b] .and (by simp [ha,hb]) (by simp)
  exact ⟨_,by simpa [GateOp.eval] using h, List.mem_append_right _ (by simp)⟩

def parity {X : Type} (l : Wires X) (x : X) : Bool := l.foldr (fun f r => xor (f x) r) false
lemma parity_mod (l : Wires X) (x : X) :
    GateOp.eval (.mod 2) (l.map (fun f => f x)) = !parity l x := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    change _ = !(xor (f x) (parity l x))
    cases e : f x <;> simp [GateOp.eval,e] at ih ⊢ <;> try assumption
    generalize (List.map (fun f : X → Bool => f x) l).count true = m at ih ⊢
    cases hp : parity l x <;> simp [hp] at ih ⊢ <;> omega

lemma build_parity (w : Wires X) (l : Wires X) (hm : l ⊆ w) :
    ∃ v, Run w 0 v ∧ parity l ∈ v := by
  let f := fun x => GateOp.eval (.mod 2) (l.map (fun a => a x))
  have h : Run w 0 (w++[f]) := by simpa [f] using make w l (.mod 2) hm (by simp)
  obtain ⟨v,hv,hnot⟩ := build_not (w++[f]) f (by simp)
  refine ⟨v,h.seq hv,?_⟩
  simpa only [f,parity_mod,Bool.not_not] using hnot

lemma build_all {ι : Type} (w : Wires X) (s : List ι) (f : ι → X → Bool)
    (able : ∀ i ∈ s, ∀ v : Wires X, w ⊆ v → ∃ v', Run v 0 v' ∧ f i ∈ v') :
    ∃ v, Run w 0 v ∧ ∀ i ∈ s, f i ∈ v := by
  induction s generalizing w with
  | nil => exact ⟨_,Run.keep _,by simp⟩
  | cons i s ih =>
    obtain ⟨v,hv,hi⟩ := able i (by simp) w (by rfl)
    obtain ⟨v',hv',hs⟩ := ih v (fun j hj u hu => able j (by simp [hj]) u (List.Subset.trans hv.subset hu))
    exact ⟨v',hv.seq hv',fun j hj => (List.mem_cons.mp hj).elim (fun e => e.symm ▸ hv'.subset hi) (hs j)⟩

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.CircuitLowerBounds PEqualNP.ProofComplexity

variable {V : Type} [Fintype V] [DecidableEq V]
noncomputable abbrev Base (V : Type) [Fintype V] : Wires (V → Bool) :=
  [fun _ => false,fun _ => true] ++ List.ofFn (fun i : Fin (Fintype.card V) => fun x => x ((Fintype.equivFin V).symm i))

lemma raw_mem (v : V) : (fun x => x v) ∈ Base V := by
  apply List.mem_append_right
  apply List.mem_ofFn.mpr
  exact ⟨Fintype.equivFin V v,by simp⟩
lemma base_const (b : Bool) : (fun _ => b) ∈ Base V := by cases b <;> simp [Base]

noncomputable def Works (Fml : Set (Clause V)) (b T : ℕ) (S : Finset (Bits b)) (cap : Bits b → ℕ) : Prop :=
  ∃ (H : Circuit) (pick : Fin b → Fin (2+Fintype.card V+H.size)) (out : Bits b → Finset (Clause V)),
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+Fintype.card V) H ∧
    (∀ g ∈ H.gates, OK g) ∧ H.gates.countP charged ≤ T ∧
    (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ c ∈ out y, c ∈ Fml) ∧
    ∀ x : V → Bool,
      let ws := H.wires ([false,true] ++ List.ofFn (fun j : Fin (Fintype.card V) => x ((Fintype.equivFin V).symm j)))
      let y := fun j : Fin b => z (ws.getD (pick j).val false)
      y ∈ S ∧ ∃ c ∈ out y, ¬ ClauseSat x c

lemma realize (Fml : Set (Clause V)) {b T : ℕ} (S : Finset (Bits b)) (cap : Bits b → ℕ)
    (msg : (V → Bool) → Bits b) (out : Bits b → Finset (Clause V))
    (outok : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ c ∈ out y, c ∈ Fml)
    (hit : ∀ x, msg x ∈ S ∧ ∃ c ∈ out (msg x), ¬ ClauseSat x c)
    (v : Wires (V → Bool)) (run : Run (Base V) T v)
    (present : ∀ j : Fin b, (fun x => bitof (msg x j)) ∈ v) : Works Fml b T S cap := by
  classical
  obtain ⟨gs,hb,ho,hc,rfl⟩ := run
  let v := wireForms gs (Base V)
  let H : Circuit := ⟨gs,0⟩
  have hlen : v.length = 2 + Fintype.card V + H.size := by simp [v,forms_length,Base,H,Circuit.size,Nat.add_comm] <;> omega
  let pick := fun j => v.idxOf (fun x => bitof (msg x j))
  have hlt j : pick j < v.length := List.idxOf_lt_length_of_mem (present j)
  refine ⟨H,fun j => ⟨pick j, hlen ▸ hlt j⟩,out,?_,ho,hc,outok,?_⟩
  · have hh : (Base V).length = 2+Fintype.card V := by simp [Base]; omega
    rw [hh] at hb
    exact back_reads hb
  · intro x
    have he : v.map (fun f => f x) = H.wires ([false,true] ++ List.ofFn (fun j : Fin (Fintype.card V) =>
        x ((Fintype.equivFin V).symm j))) := by
      rw [wire_eval]
      simp [H,Circuit.wires,Base,List.map_ofFn,Function.comp_def]
    have hj (j : Fin b) : z ((v.map (fun f => f x)).getD (pick j) false) = msg x j := by
      rw [List.getD_map v (fun _ => false) (fun f => f x), List.getD_eq_getElem _ _ (hlt j)]
      change z ((v[v.idxOf (fun x => bitof (msg x j))]'(hlt j)) x) = _
      rw [List.getElem_idxOf,z_bitof]
    simpa only [← he, hj] using hit x

lemma big_list {b T : ℕ} (S : Finset (Bits b)) (cap : Bits b → ℕ) (a : Bits b)
    (ha : a ∈ S) (Fml : Set (Clause V)) (L : Finset (Clause V))
    (hcard : L.card ≤ cap a) (hF : ∀ c ∈ L, c ∈ Fml) (bad : ∀ x, ∃ c ∈ L, ¬ ClauseSat x c) :
    Works Fml b T S cap := by
  classical
  apply realize Fml S cap (fun _ => a) (fun y => if y=a then L else ∅)
  · intro y hy
    by_cases he : y = a
    · simpa [he] using And.intro hcard hF
    · simp [he]
  · exact fun x => ⟨ha,by simpa using bad x⟩
  · exact (Run.keep (Base V)).weaken (Nat.zero_le _)
  · exact fun j => base_const _

lemma parity_z {X : Type} (l : Wires X) (x : X) : z (parity l x) = (l.map (fun f => z (f x))).sum := by
  induction l with
  | nil => rfl
  | cons f l ih => simpa [parity,z_xor] using congrArg (fun q => z (f x)+q) ih

lemma build_affine (w : Wires (V → Bool)) (hw : Base V ⊆ w) (a : F) (l : (V → F) →ₗ[F] F) :
    ∃ w', Run w 0 w' ∧ (fun x => bitof (a + l (fun i => z (x i)))) ∈ w' := by
  classical
  let coef := fun i : V => l ((Pi.basisFun F V) i)
  let coeffun := fun i : V => if coef i = 0 then (fun _ : V → Bool => false) else (fun x => x i)
  let fs : Wires (V → Bool) := (fun _ => bitof a) :: Finset.univ.toList.map coeffun
  have hm : fs ⊆ w := by
    intro f hf
    rcases List.mem_cons.mp hf with rfl | ht
    · exact hw (base_const _)
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
      by_cases h : coef i = 0
      · simpa [coeffun,h] using hw (base_const false)
      · simpa [coeffun,h] using hw (raw_mem i)
  obtain ⟨v,hr,hp⟩ := build_parity w fs hm
  refine ⟨v,hr,?_⟩
  have he : parity fs = (fun x => bitof (a + l (fun i => z (x i)))) := by
    funext x
    apply z_inj
    rw [z_bitof,parity_z]
    have hcoef (i : V) : z (coeffun i x) = z (x i) * coef i := by
      have h01 : ∀ c : F, c = 0 ∨ c = 1 := by decide
      rcases h01 (coef i) with hi | hi <;> simp [coeffun,hi,z]
    have hrepr := congrArg l ((Pi.basisFun F V).sum_repr (fun i => z (x i)))
    simp only [map_sum,map_smul,Pi.basisFun_repr,smul_eq_mul] at hrepr
    simpa [fs,List.map_map,Function.comp_def,hcoef,z_bitof,coef] using congrArg (a+·) hrepr
  exact he ▸ hp

lemma large_flat {b T : ℕ} (S : Finset (Bits b)) (cap : Bits b → ℕ)
    (hne : S.Nonempty) (pos : ∀ y ∈ S, 1 ≤ cap y) (hflat : Fintype.card V ≤ flatRank S)
    (Fml : Set (Clause V)) (bad : ∀ x : V → Bool, ∃ c ∈ Fml, ¬ ClauseSat x c) :
    Works Fml b T S cap := by
  classical
  obtain ⟨a0,ha0⟩ := hne
  obtain ⟨U,a,hU,ha⟩ : ∃ (U : Submodule F (Bits b)) (a : Bits b), Module.finrank F U = flatRank S ∧
      ∀ u ∈ U, a+u ∈ S := by
    apply Nat.sSup_mem (s := {k : ℕ | ∃ (U : Submodule F (Bits b)) (y : Bits b), Module.finrank F U = k ∧ ∀ u ∈ U, y+u ∈ S})
    · exact ⟨0,⊥,a0,by simp,fun u hu => by simpa [show u = 0 from hu] using ha0⟩
    · refine ⟨Module.finrank F (Bits b),?_⟩
      rintro k ⟨U,a,rfl,_⟩
      exact U.finrank_le
  obtain ⟨lin,hlin⟩ : ∃ l : (V → F) →ₗ[F] U, Function.Injective l :=
    finrank_le_iff_exists_linearMap.mp (by simpa [hU,Module.finrank_pi] using hflat)
  let msg := fun x : V → Bool => a + (lin (fun i => z (x i))).val
  have hin : ∀ x, msg x ∈ S := fun x => ha _ (lin _).property
  have hi : Function.Injective msg := by
    intro x x' he
    have h' : lin (fun i => z (x i)) = lin (fun i => z (x' i)) := Subtype.ext (add_left_cancel he)
    exact funext fun i => z_inj (congrFun (hlin h') i)
  let inv := Function.invFun msg
  let out : Bits b → Finset (Clause V) := fun y => {(bad (inv y)).choose}
  obtain ⟨v,hr,hv⟩ := build_all (Base V) (List.finRange b) (fun j x => bitof (msg x j)) (by
    intro j _ w hw
    exact build_affine w hw (a j) ((LinearMap.proj j).comp (U.subtype.comp lin)))
  apply realize Fml S cap msg out
  · intro y hy
    simpa [out] using And.intro (pos y hy) (bad (inv y)).choose_spec.1
  · intro x
    refine ⟨hin x,(bad x).choose,?_,(bad x).choose_spec.2⟩
    simp [out,inv,Function.leftInverse_invFun hi x]
  · exact hr.weaken (by omega)
  · exact fun j => hv j (by simp)

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]
open Classical in
noncomputable def badbit (c : Clause V) (x : V → Bool) := decide (¬ ClauseSat x c)

lemma build_bad (w : Wires (V → Bool)) (hw : Base V ⊆ w) (c : Clause V) :
    ∃ v, Run w c.card v ∧ badbit c ∈ v := by
  classical
  induction c using Finset.induction_on generalizing w with
  | empty =>
    refine ⟨w, Run.keep w,?_⟩
    have h : badbit (∅ : Clause V) = fun _ => true := by funext x; simp [badbit,ClauseSat]
    rw [h]; exact hw (base_const true)
  | insert l c hl ih =>
    obtain ⟨v,hv,hc⟩ := ih w hw
    let f := fun x : V → Bool => decide (x l.1 ≠ l.2)
    have haveLit : ∃ v', Run v 0 v' ∧ f ∈ v' := by
      have raw := hv.subset (hw (raw_mem l.1))
      cases he : l.2 with
      | false =>
        exact ⟨v, Run.keep _,by simpa [f,he] using raw⟩
      | true =>
        simpa [f,he] using build_not v (fun x => x l.1) raw
    obtain ⟨v',hv',hf⟩ := haveLit
    obtain ⟨v'',hv'',hf'⟩ := build_and v' f (badbit c) hf (hv'.subset hc)
    refine ⟨v'',by simpa [Finset.card_insert_of_notMem hl] using (hv.seq hv').seq hv'',?_⟩
    have he : badbit (insert l c) = (fun x => f x && badbit c x) := by
      funext x
      simp [badbit,f,ClauseSat,not_or]
    exact he ▸ hf'

noncomputable def firstBad (cs : List (Clause V)) (x : V → Bool) := cs.find? (fun c => badbit c x)
noncomputable def flag (cs : List (Clause V)) (p : (V → Bool) → Bool) (c : Clause V) :=
  fun x => p x && decide (firstBad cs x = some c)

lemma flags (w : Wires (V → Bool)) (hw : Base V ⊆ w) (cs : List (Clause V))
    (nodup : cs.Nodup) (d : ℕ) (width : ∀ c ∈ cs, c.card ≤ d)
    (p : (V → Bool) → Bool) (hp : p ∈ w) :
    ∃ v, Run w ((d+2)*cs.length) v ∧ ∀ c ∈ cs, flag cs p c ∈ v := by
  classical
  induction cs generalizing p w with
  | nil => exact ⟨w,Run.keep _,by simp⟩
  | cons c cs ih =>
    obtain ⟨hn,hn'⟩ := List.nodup_cons.mp nodup
    obtain ⟨v,hv,hb⟩ := build_bad w hw c
    obtain ⟨u,hu,hfire⟩ := build_and v p (badbit c) (hv.subset hp) hb
    obtain ⟨z,hz,hnc⟩ := build_not u (badbit c) (hu.subset hb)
    obtain ⟨t,ht,htail⟩ := build_and z p (fun x => !(badbit c x)) (hz.subset (hu.subset (hv.subset hp))) hnc
    let tailp := fun x => p x && !(badbit c x)
    have run := ((hv.seq hu).seq hz).seq ht
    obtain ⟨v',hr,hf⟩ := ih t (List.Subset.trans hw run.subset) hn' (fun a ha => width a (by simp [ha])) tailp htail
    refine ⟨v',(run.seq hr).weaken ?_,?_⟩
    · have := width c List.mem_cons_self
      simp only [List.length_cons,Nat.mul_succ]; omega
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · have eq : flag (a::cs) p a = (fun x => p x && badbit a x) := by
          funext x
          have hnmem : firstBad cs x ≠ some a := fun h => hn (List.mem_of_find?_eq_some h)
          cases e : badbit a x <;> simp [flag,firstBad,List.find?_cons,e,firstBad] at hnmem ⊢ <;> simp_all
        exact eq ▸ hr.subset (ht.subset (hz.subset hfire))
      · have ne : c ≠ a := fun h => hn (h ▸ ha)
        have eq : flag (c::cs) p a = flag cs tailp a := by
          funext x
          cases e : badbit c x <;> simp [flag,firstBad,List.find?_cons,e,tailp,ne] <;> rfl
        exact eq ▸ hf _ ha

lemma slots {A Y : Type} [DecidableEq A] [DecidableEq Y] (L : Finset A) (S : Finset Y) (cap : Y → ℕ)
    (h : L.card ≤ ∑ y ∈ S, cap y) : ∃ assign : L → S,
       ∀ y : S, (Finset.univ.filter (fun c : L => assign c = y)).card ≤ cap y := by
  classical
  let Slots := (y : S) × Fin (cap y)
  have hc : Fintype.card L ≤ Fintype.card Slots := by
    simpa [Slots,Fintype.card_sigma,Finset.sum_attach] using h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun c => (f c).1,fun y => ?_⟩
  let ts := Finset.univ.filter (fun c : L => (f c).1 = y)
  let k (c : ts) : Fin (cap y) := (f c.val).2.cast (congrArg cap (congrArg Subtype.val (Finset.mem_filter.mp c.property).2))
  have hi : Function.Injective k := by
    intro c d he
    apply Subtype.ext
    apply f.injective
    apply Sigma.ext ((Finset.mem_filter.mp c.property).2.trans (Finset.mem_filter.mp d.property).2.symm)
    apply (Fin.heq_ext_iff _).mpr
    · exact congrArg Fin.val he
    · exact congrArg (fun q : S => cap q) ((Finset.mem_filter.mp c.property).2.trans (Finset.mem_filter.mp d.property).2.symm)
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective k hi

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.ProofComplexity
variable {V : Type} [Fintype V] [DecidableEq V]

lemma large_T {b T : ℕ} (S : Finset (Bits b)) (cap : Bits b → ℕ)
    (Fml : Set (Clause V)) (L : Finset (Clause V)) (valid : ∀ c ∈ L, c ∈ Fml)
    (bad : ∀ x, ∃ c ∈ L, ¬ ClauseSat x c) (d : ℕ) (width : ∀ c ∈ L, c.card ≤ d)
    (hcost : (d+2)*L.card ≤ T) (hslots : L.card ≤ ∑ y ∈ S, cap y) : Works Fml b T S cap := by
  classical
  obtain ⟨lab,hcap⟩ := slots L S cap hslots
  have pick (x : V → Bool) : ∃ c : L, firstBad L.toList x = some c.val := by
    obtain ⟨c,hc,hbad⟩ := bad x
    cases e : firstBad L.toList x with
    | none =>
      have hn := List.find?_eq_none.mp e c (Finset.mem_toList.mpr hc)
      simp [badbit,hbad] at hn
    | some r => exact ⟨⟨r,Finset.mem_toList.mp (List.mem_of_find?_eq_some e)⟩,rfl⟩
  let win := fun x => (pick x).choose
  have first (x) : firstBad L.toList x = some (win x).val := (pick x).choose_spec
  let msg := fun x => (lab (win x)).val
  let out := fun y => (Finset.univ.filter (fun c : L => (lab c).val = y)).image Subtype.val
  have outok : ∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ c ∈ out y, c ∈ Fml := by
    intro y hy
    constructor
    · apply Finset.card_image_le.trans
      simpa only [Subtype.ext_iff] using hcap ⟨y,hy⟩
    · rintro c hc
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
      exact valid _ z.property
  have hit (x) : msg x ∈ S ∧ ∃ c ∈ out (msg x), ¬ ClauseSat x c := by
    refine ⟨(lab (win x)).property,(win x).val,
      Finset.mem_image.mpr ⟨win x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩,?_⟩
    have h : badbit (win x).val x = true := List.find?_some (p := fun c => badbit c x) (first x)
    exact of_decide_eq_true h
  obtain ⟨v,hr,hf⟩ := flags (Base V) (by rfl) L.toList L.nodup_toList d
    (fun c hc => width c (Finset.mem_toList.mp hc)) (fun _ => true) (base_const true)
  obtain ⟨u,hu,hbit⟩ := build_all v (List.finRange b) (fun j x => bitof (msg x j)) (by
    intro j _ w hw
    let wire := fun c : L => if (lab c).val j = 1 then flag L.toList (fun _ => true) c.val
       else (fun _ : V → Bool => false)
    have hwire (c : L) : wire c ∈ w := by
      dsimp only [wire]
      split
      · exact hw (hf _ (Finset.mem_toList.mpr c.property))
      · exact hw (hr.subset (base_const false))
    let fs := (Finset.univ : Finset L).toList.map wire
    obtain ⟨u,h,hm⟩ := build_parity w fs (by
      intro f hf
      obtain ⟨c,_,rfl⟩ := List.mem_map.mp hf
      exact hwire c)
    refine ⟨u,h,?_⟩
    have he : parity fs = fun x => bitof (msg x j) := by
      funext x
      apply z_inj
      rw [z_bitof,parity_z]
      have hv (c : L) : z (wire c x) = if c = win x then (lab c).val j else 0 := by
        have h01 : ∀ r : F, r = 0 ∨ r = 1 := by decide
        by_cases hc : c = win x
        · subst c
          rcases h01 ((lab (win x)).val j) with hl | hl <;> simp [wire,hl,flag,first,z]
        · have hv : (win x).val ≠ c.val := fun he => hc (Subtype.ext he.symm)
          rcases h01 ((lab c).val j) with hl | hl <;> simp [wire,hl,flag,first,hc,hv,z]
      simpa [fs,List.map_map,Function.comp_def,hv,msg] 
    exact he ▸ hm)
  apply realize Fml S cap msg out outok hit u ((hr.seq hu).weaken (by simpa using hcost))
  exact fun j => hbit j (by simp)

end PEqualNP.Outside.L_pcx_402_aux

namespace PEqualNP.Outside.L_pcx_402_aux
open PEqualNP.Expanders PEqualNP.ProofComplexity

lemma fun_width {m n d : ℕ} (G : BipGraph m n) (hL : LeftDegLe G d) :
    ∀ c ∈ funGraphPHP G, c.card ≤ max d 2 := by
  rintro c (hc | ⟨a,b,_,_,rfl⟩)
  · exact graphPHP_width G d hL c hc
  · exact (Finset.card_insert_le _ _).trans (by simp)

lemma lower_bound {n s d C b T : ℕ} (hs : 0 < s) (hn : s ≤ n)
    (hC : s ≤ C) (hC' : s*d*(max d 2) ≤ C)
    (G : BipGraph (n+1) n) (hl : LeftDegLe G d) (exp : IsBdryExpander G (n/s) 2)
    (S : Finset (Bits b)) (cap : Bits b → ℕ) (hw : Works (funGraphPHP G) b T S cap) :
    n ≤ C * min (∑ y ∈ S, cap y) (T + S.sup cap + flatRank S) := by
  classical
  obtain ⟨H,pick,out,_,ok,hcost,hvalid,hit⟩ := hw
  let o := (Fintype.equivFin (GEdge G)).symm
  have sumlt := total_capacity G exp S cap out hvalid (by
    intro x
    exact ⟨_,(hit x).1,(hit x).2⟩)
  have pc := lower_pc o (funGraphPHP G) (max d 2) (fun_width G hl) H
    (fun j => (pick j).val) ok S cap out hvalid (fun x => hit (fun i => bitof (x i)))
  let k := H.gates.countP charged
  let w := max d 2
  have powlt : n/s < d*(2*k+flatRank S+w*S.sup cap) := by
    by_contra! h
    exact Core.L049 _ _ G _ d _ exp hl (Nat.div_pos hn hs) h pc
  rw [mul_min]
  apply le_min
  · calc n ≤ (∑ y ∈ S, cap y)*s := ((Nat.div_lt_iff_lt_mul hs).mp sumlt).le
         _ ≤ C*(∑ y ∈ S, cap y) := by rw [Nat.mul_comm]; gcongr
  · have h2 : 2 ≤ w := le_max_right _ _
    have h1 : 1 ≤ w := by omega
    have hD : 2*k+flatRank S+w*S.sup cap ≤ w*(T+S.sup cap+flatRank S) := by
      have hh : 2*k ≤ w*T := Nat.mul_le_mul h2 hcost
      have hf := Nat.mul_le_mul_right (flatRank S) h1
      simp only [Nat.one_mul] at hf
      rw [Nat.mul_add,Nat.mul_add]
      omega
    calc n ≤ (d*(2*k+flatRank S+w*S.sup cap))*s := ((Nat.div_lt_iff_lt_mul hs).mp powlt).le
         _ ≤ (d*(w*(T+S.sup cap+flatRank S)))*s := by gcongr
         _ = (s*d*w)*(T+S.sup cap+flatRank S) := by ring
         _ ≤ _ := Nat.mul_le_mul_right _ hC'

lemma upper_bound {n d C b T : ℕ} (hn : 1 ≤ n)
    (hC : 3*(max d 2 + 2)*(2*(d+1)*(d+1)) ≤ C) (G : BipGraph (n+1) n)
    (hl : LeftDegLe G d) (hr : RightDegLe G d)
    (S : Finset (Bits b)) (cap : Bits b → ℕ) (hne : S.Nonempty) (pos : ∀ y ∈ S, 1 ≤ cap y)
    (budget : C*n ≤ min (∑ y ∈ S, cap y) (T + S.sup cap + flatRank S)) :
    Works (funGraphPHP G) b T S cap := by
  classical
  let B := 2*(d+1)*(d+1)
  let w := max d 2
  let K := (w+2)*B
  have hK : 3*K ≤ C := by simpa [K,w,B,Nat.mul_assoc] using hC
  have hBK : B ≤ K := by
    calc B = 1*B := by omega
         _ ≤ (w+2)*B := Nat.mul_le_mul_right _ (by omega)
  let L := (graphPHP G).toFinset
  have valid : ∀ c ∈ L, c ∈ funGraphPHP G := fun _ hc => Or.inl (Set.mem_toFinset.mp hc)
  have bad (x : GEdge G → Bool) : ∃ c ∈ L, ¬ ClauseSat x c := by
    by_contra! h
    exact graphPHP_unsat G (by omega) ⟨x,fun c hc => h c (Set.mem_toFinset.mpr hc)⟩
  have hcard : L.card ≤ B*n := by
    have hc := card_graphPHP_le G d hl hr
    have he : L.card = Fintype.card (graphPHP G) := Set.toFinset_card _
    have hn2 : n+1 ≤ 2*n := by omega
    calc L.card ≤ (n+1)+(n+1)*d*d := he.le.trans hc
         _ ≤ (2*n)+(2*n)*d*d := by gcongr
         _ ≤ B*n := by dsimp [B]; ring_nf; omega
  have he : Fintype.card (GEdge G) ≤ B*n := by
    calc Fintype.card (GEdge G) ≤ (n+1)*d := card_gedge_le G d hl
         _ ≤ (2*n)*d := Nat.mul_le_mul_right _ (by omega)
         _ ≤ B*n := by dsimp [B]; ring_nf; omega
  have hslots : L.card ≤ ∑ y ∈ S, cap y := hcard.trans ((Nat.mul_le_mul_right n (by omega : B ≤ C)).trans (le_min_iff.mp budget).1)
  by_cases ht : (w+2)*L.card ≤ T
  · exact large_T S cap _ L valid bad w (fun c hc => fun_width G hl c (valid c hc)) ht hslots
  by_cases hcap : L.card ≤ S.sup cap
  · obtain ⟨a,ha,heq⟩ := S.exists_mem_eq_sup hne cap
    exact big_list S cap a ha _ L (heq ▸ hcap) valid bad
  by_cases hflat : Fintype.card (GEdge G) ≤ flatRank S
  · exact large_flat S cap hne pos hflat _ (fun x => by
      obtain ⟨c,hc,hb⟩ := bad x
      exact ⟨c,valid c hc,hb⟩)
  have ht' : T < K*n := (Nat.lt_of_not_ge ht).trans_le (by
    calc (w+2)*L.card ≤ (w+2)*(B*n) := Nat.mul_le_mul_left _ hcard
         _ = K*n := by simp [K,Nat.mul_assoc])
  have hBK' := Nat.mul_le_mul_right n hBK
  have hbig : 3*(K*n) ≤ T + S.sup cap + flatRank S := by
    rw [← Nat.mul_assoc]
    exact (Nat.mul_le_mul_right _ hK).trans (le_min_iff.mp budget).2
  omega

end PEqualNP.Outside.L_pcx_402_aux

open PEqualNP.Outside.L_pcx_402_aux

theorem PEqualNP.Outside.L_pcx_402 : (∃ C n₀ : ℕ, 2 ≤ C ∧ ∀ n : ℕ, n₀ ≤ n →
  ∃ G : PEqualNP.Expanders.BipGraph (n+1) n,
    PEqualNP.Expanders.LeftDegLe G C ∧ PEqualNP.Expanders.RightDegLe G C ∧
    let V := PEqualNP.Expanders.GEdge G
    let e := Fintype.card V
    let F := PEqualNP.Expanders.funGraphPHP G
    ∀ (b T : ℕ) (S : Finset (Fin b → ZMod 2)) (cap : (Fin b → ZMod 2) → ℕ),
      S.Nonempty → (∀ y ∈ S, 1 ≤ cap y) →
      let Y := Fin b → ZMod 2
      let flat := sSup {k : ℕ | ∃ (U : Submodule (ZMod 2) Y) (y : Y),
        Module.finrank (ZMod 2) U = k ∧ ∀ u ∈ U, y + u ∈ S}
      let budget := min (∑ y ∈ S, cap y) (T + S.sup cap + flat)
      let works := ∃ (H : PEqualNP.CircuitLowerBounds.Circuit)
          (pick : Fin b → Fin (2+e+H.size)) (out : Y → Finset (PEqualNP.ProofComplexity.Clause V)),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+e) H ∧
        (∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
          g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) ∧
        H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)) ≤ T ∧
        (∀ y ∈ S, (out y).card ≤ cap y ∧ ∀ cl ∈ out y, cl ∈ F) ∧
        ∀ x : V → Bool,
          let ws := H.wires ([false,true] ++ List.ofFn (fun j : Fin e => x ((Fintype.equivFin V).symm j)))
          let y := fun j : Fin b => ((ws.getD (pick j).val false).toNat : ZMod 2)
          y ∈ S ∧ ∃ cl ∈ out y, ¬ PEqualNP.ProofComplexity.ClauseSat x cl
      (works → n ≤ C*budget) ∧ (C*n ≤ budget → works)) := by
  classical
  obtain ⟨d,s,n₀,hs,hex⟩ := Core.L043
  let C := 2 + d + s + s*d*(max d 2) + 3*(max d 2 + 2)*(2*(d+1)*(d+1))
  refine ⟨C,max n₀ s,by dsimp [C]; omega,?_⟩
  intro n hn
  obtain ⟨hn0,hns⟩ := max_le_iff.mp hn
  obtain ⟨G,hl,hr,exp⟩ := hex n hn0
  have hd : d ≤ C := by dsimp [C]; omega
  refine ⟨G, fun i => (hl i).trans hd, fun j => (hr j).trans hd,?_⟩
  intro V e Fml b T S cap hne pos Y flat budget works
  exact ⟨lower_bound hs hns (by dsimp [C]; omega) (by dsimp [C]; omega) G hl exp S cap,
    upper_bound (by omega) (by dsimp [C]; omega) G hl hr S cap hne pos⟩
