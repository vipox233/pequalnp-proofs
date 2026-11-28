import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_296_aux

open Finset Polynomial Module

private def quadEquiv (q : ℕ) : (Fin q × Fin q × Fin q × Fin q) ≃ (Fin 4 → Fin q) :=
  ⟨fun e => ![e.1, e.2.1, e.2.2.1, e.2.2.2],
    fun c => (c 0, c 1, c 2, c 3),
    fun _ => rfl, fun c => by ext i; fin_cases i <;> rfl⟩

private lemma quadEquiv_injective {q : ℕ} (a b c d : Fin q) :
    Function.Injective (quadEquiv q (a, b, c, d)) ↔
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  refine ⟨fun hinj => ?_, fun ⟨hab, hac, had, hbc, hbd, hcd⟩ i j heq => ?_⟩
  · have dist (i j : Fin 4) (hne : i ≠ j := by decide) :
        quadEquiv q (a, b, c, d) i ≠ quadEquiv q (a, b, c, d) j := fun h => hne (hinj h)
    exact ⟨dist 0 1, dist 0 2, dist 0 3, dist 1 2, dist 1 3, dist 2 3⟩
  · change ![a, b, c, d] i = ![a, b, c, d] j at heq
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]

private lemma sum_injections_q {q : ℕ} (term : (Fin 4 → Fin q) → ℂ) :
    (∑ f : Fin 4 ↪ Fin q, term f) =
      ∑ a : Fin q, ∑ b ∈ univ.erase a,
        ∑ c ∈ (univ.erase a).erase b,
          ∑ d ∈ ((univ.erase a).erase b).erase c,
            term ![a, b, c, d] := by
  classical
  have h1 : (∑ f : Fin 4 ↪ Fin q, term f) =
      ∑ a : Fin q, ∑ b : Fin q, ∑ c : Fin q, ∑ d : Fin q,
        if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then
          term ![a, b, c, d] else 0 := by
    calc
      _ = ∑ col : Fin 4 → Fin q, if Function.Injective col then term col else 0 := by
        rw [← (Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin q)).sum_comp,
          ← sum_filter (p := Function.Injective)]
        exact (sum_subtype _ (fun _ => by simp) term).symm
      _ = _ := by
        rw [← (quadEquiv q).sum_comp]
        simp only [Fintype.sum_prod_type, quadEquiv_injective]
        rfl
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hb : ∀ b : Fin q,
      (∑ c : Fin q, ∑ d : Fin q,
        if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then term ![a, b, c, d] else 0) =
      if b ∈ univ.erase a then
        ∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c, term ![a, b, c, d]
      else 0 := by
    intro b
    by_cases hba : b = a
    · subst hba
      simp
    · rw [if_pos (mem_erase.mpr ⟨hba, mem_univ _⟩)]
      have hc : ∀ c : Fin q,
          (∑ d : Fin q,
            if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then term ![a, b, c, d] else 0) =
          if c ∈ (univ.erase a).erase b then
            ∑ d ∈ ((univ.erase a).erase b).erase c, term ![a, b, c, d]
          else 0 := by
        intro c
        by_cases hca : c = a
        · subst hca; simp
        · by_cases hcb : c = b
          · subst hcb; simp
          · rw [if_pos (mem_erase.mpr ⟨hcb, mem_erase.mpr ⟨hca, mem_univ _⟩⟩)]
            have hd : ∀ d : Fin q,
                (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then term ![a, b, c, d] else 0) =
                if d ∈ ((univ.erase a).erase b).erase c then term ![a, b, c, d] else 0 := by
              intro d
              have hiff : (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) ↔
                  d ∈ ((univ.erase a).erase b).erase c := by
                simp only [mem_erase, mem_univ, and_true]
                tauto
              exact if_congr hiff rfl rfl
            simp_rw [hd, Finset.sum_ite_mem, Finset.univ_inter]
      simp_rw [hc, Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [hb, Finset.sum_ite_mem, Finset.univ_inter]

private lemma sum_finset_erase_swap {α : Type*} [DecidableEq α] (S : Finset α) (F : α → α → ℂ) :
    (∑ a ∈ S, ∑ b ∈ S.erase a, F a b) = ∑ a ∈ S, ∑ b ∈ S.erase a, F b a := by
  have hrew : ∀ G : α → α → ℂ,
      (∑ a ∈ S, ∑ b ∈ S.erase a, G a b) = ∑ a ∈ S, ∑ b ∈ S, if b ≠ a then G a b else 0 := by
    intro G
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_filter]
    congr 1
    ext b
    simp [Finset.mem_erase, and_comm]
  rw [hrew F, hrew (fun a b => F b a), Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · subst h; simp
  · rw [if_pos (Ne.symm h), if_pos h]

private lemma sum_pair_prod {α : Type*} [DecidableEq α] (S : Finset α) (g : α → ℂ) :
    (∑ a ∈ S, ∑ b ∈ S.erase a, g a * g b) = (∑ a ∈ S, g a) ^ 2 - ∑ a ∈ S, (g a) ^ 2 := by
  have h1 : ∀ a ∈ S, (∑ b ∈ S.erase a, g a * g b) = g a * ((∑ b ∈ S, g b) - g a) := by
    intro a ha
    rw [← Finset.mul_sum, Finset.sum_erase_eq_sub ha]
  rw [Finset.sum_congr rfl h1]
  have h2 : ∀ a ∈ S, g a * ((∑ b ∈ S, g b) - g a) = g a * (∑ b ∈ S, g b) - (g a) ^ 2 := by
    intro a _; ring
  rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, ← Finset.sum_mul, pow_two]

private lemma permanent_expand_q {q : ℕ} (hq : 4 ≤ q) (x y : Fin q → ℂ)
    (hx : (∑ j, x j) = 0) (hy : (∑ j, y j) = 0) (hy2 : (∑ j, (y j) ^ 2) = 0) (t : ℂ) :
    let rows : Fin 4 → Fin q → ℂ := ![x, -x, t • y, -(t • y)]
    (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
      (Fintype.card (Fin 4 ↪ Fin q) : ℂ) +
      ((q : ℂ) - 2) * ((q : ℂ) - 3) * (∑ j, (x j) ^ 2) +
      t ^ 2 * (2 * (∑ j, x j * y j) ^ 2 - 6 * (∑ j, (x j) ^ 2 * (y j) ^ 2)) := by
  classical
  dsimp only
  rw [sum_injections_q (fun col => ∏ i : Fin 4,
    (1 + (![x, -x, t • y, -(t • y)] : Fin 4 → Fin q → ℂ) i (col i)))]
  have hcard_sum : (Fintype.card (Fin 4 ↪ Fin q) : ℂ) =
      ∑ a : Fin q, ∑ b ∈ univ.erase a,
        ∑ c ∈ (univ.erase a).erase b,
          ∑ d ∈ ((univ.erase a).erase b).erase c, (1 : ℂ) := by
    have h := sum_injections_q (q := q) (fun _ => (1 : ℂ))
    simpa using h
  have hprod_eval : ∀ a b c d : Fin q,
      (∏ i : Fin 4, (1 + (![x, -x, t • y, -(t • y)] : Fin 4 → Fin q → ℂ) i (![a, b, c, d] i))) =
      (1 + x a) * (1 - x b) * ((1 : ℂ) + t * (y c - y d) - t ^ 2 * (y c * y d)) := by
    intro a b c d
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Pi.neg_apply, Pi.smul_apply,
      smul_eq_mul]
    ring
  simp_rw [hprod_eval]
  have hinner : ∀ a : Fin q, ∀ b ∈ univ.erase a,
      (∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c,
        (1 + x a) * (1 - x b) * ((1 : ℂ) + t * (y c - y d) - t ^ 2 * (y c * y d))) =
      (1 + x a) * (1 - x b) *
        ((∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c, (1 : ℂ)) -
          t ^ 2 * (2 * (y a) ^ 2 + 2 * (y b) ^ 2 + 2 * y a * y b)) := by
    intro a b hb
    set S := (univ.erase a).erase b
    have hba : b ≠ a := (mem_erase.mp hb).1
    have hpull : ∀ c ∈ S,
        (∑ d ∈ S.erase c, (1 + x a) * (1 - x b) * ((1 : ℂ) + t * (y c - y d) - t ^ 2 * (y c * y d))) =
        (1 + x a) * (1 - x b) * ∑ d ∈ S.erase c, ((1 : ℂ) + t * (y c - y d) - t ^ 2 * (y c * y d)) :=
      fun c _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl hpull, ← Finset.mul_sum]
    congr 1
    have hsplit : (∑ c ∈ S, ∑ d ∈ S.erase c, ((1 : ℂ) + t * (y c - y d) - t ^ 2 * (y c * y d))) =
        (∑ c ∈ S, ∑ d ∈ S.erase c, (1 : ℂ)) +
        t * (∑ c ∈ S, ∑ d ∈ S.erase c, (y c - y d)) -
        t ^ 2 * (∑ c ∈ S, ∑ d ∈ S.erase c, y c * y d) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    rw [hsplit]
    have hodd : (∑ c ∈ S, ∑ d ∈ S.erase c, (y c - y d)) = 0 := by
      simp_rw [Finset.sum_sub_distrib]
      have hsw := sum_finset_erase_swap S (fun c d => y c)
      rw [hsw, sub_self]
    have hSy : (∑ c ∈ S, y c) = -(y a + y b) := by
      have h1 : (∑ c ∈ univ.erase a, y c) = -y a := by
        rw [Finset.sum_erase_eq_sub (mem_univ a), hy, zero_sub]
      rw [show S = (univ.erase a).erase b from rfl, Finset.sum_erase_eq_sub hb, h1]
      ring
    have hSy2 : (∑ c ∈ S, (y c) ^ 2) = -((y a) ^ 2 + (y b) ^ 2) := by
      have h1 : (∑ c ∈ univ.erase a, (y c) ^ 2) = -(y a) ^ 2 := by
        rw [Finset.sum_erase_eq_sub (mem_univ a), hy2, zero_sub]
      rw [show S = (univ.erase a).erase b from rfl, Finset.sum_erase_eq_sub hb, h1]
      ring
    have hSyy : (∑ c ∈ S, ∑ d ∈ S.erase c, y c * y d) =
        2 * (y a) ^ 2 + 2 * (y b) ^ 2 + 2 * y a * y b := by
      rw [sum_pair_prod S y, hSy, hSy2]
      ring
    rw [hodd, hSyy]
    ring
  have hstep1 :
      (∑ a : Fin q, ∑ b ∈ univ.erase a,
        ∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c,
          (1 + x a) * (1 - x b) * ((1 : ℂ) + t * (y c - y d) - t ^ 2 * (y c * y d))) =
      ∑ a : Fin q, ∑ b ∈ univ.erase a,
        (1 + x a) * (1 - x b) *
          ((∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c, (1 : ℂ)) -
            t ^ 2 * (2 * (y a) ^ 2 + 2 * (y b) ^ 2 + 2 * y a * y b)) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => hinner a b hb
  rw [hstep1]
  have hconst_ab : ∀ a : Fin q, ∀ b ∈ univ.erase a,
      (∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c, (1 : ℂ)) =
      ((q : ℂ) - 2) * ((q : ℂ) - 3) := by
    intro a b hb
    set S := (univ.erase a).erase b
    have hScard : S.card = q - 2 := by
      rw [show S = (univ.erase a).erase b from rfl, Finset.card_erase_of_mem hb,
        Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin]
      omega
    have hinner1 : ∀ c ∈ S, (∑ d ∈ S.erase c, (1 : ℂ)) = (q : ℂ) - 3 := by
      intro c hc
      rw [Finset.sum_const, Finset.card_erase_of_mem hc, hScard, nsmul_eq_mul, mul_one]
      have hcast : ((q - 2 - 1 : ℕ) : ℂ) = (q : ℂ) - 3 := by
        rw [show q - 2 - 1 = q - 3 by omega, Nat.cast_sub (by omega : 3 ≤ q)]
        norm_num
      exact hcast
    rw [Finset.sum_congr rfl hinner1, Finset.sum_const, hScard, nsmul_eq_mul]
    have hcast2 : ((q - 2 : ℕ) : ℂ) = (q : ℂ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ q)]
      norm_num
    rw [hcast2]
  set H : Fin q → Fin q → ℂ := fun a b =>
    ((q : ℂ) - 2) * ((q : ℂ) - 3) - t ^ 2 * (2 * (y a) ^ 2 + 2 * (y b) ^ 2 + 2 * y a * y b)
  have hHsym : ∀ a b : Fin q, H a b = H b a := by
    intro a b; simp only [H]; ring
  have hstep2 :
      (∑ a : Fin q, ∑ b ∈ univ.erase a,
        (1 + x a) * (1 - x b) *
          ((∑ c ∈ (univ.erase a).erase b, ∑ d ∈ ((univ.erase a).erase b).erase c, (1 : ℂ)) -
            t ^ 2 * (2 * (y a) ^ 2 + 2 * (y b) ^ 2 + 2 * y a * y b))) =
      ∑ a : Fin q, ∑ b ∈ univ.erase a, (1 + (x a - x b) - x a * x b) * H a b := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
    rw [hconst_ab a b hb]
    simp only [H]
    ring
  rw [hstep2]
  have hsplit2 :
      (∑ a : Fin q, ∑ b ∈ univ.erase a, (1 + (x a - x b) - x a * x b) * H a b) =
      (∑ a : Fin q, ∑ b ∈ univ.erase a, H a b) +
      (∑ a : Fin q, ∑ b ∈ univ.erase a, (x a - x b) * H a b) -
      (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * H a b) := by
    have hpt : ∀ a b : Fin q, (1 + (x a - x b) - x a * x b) * H a b =
        H a b + (x a - x b) * H a b - x a * x b * H a b := fun _ _ => by ring
    simp_rw [hpt, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit2]
  have hodd_ab : (∑ a : Fin q, ∑ b ∈ univ.erase a, (x a - x b) * H a b) = 0 := by
    have hpt : ∀ a b : Fin q, (x a - x b) * H a b = x a * H a b - x b * H a b := fun _ _ => by ring
    simp_rw [hpt, Finset.sum_sub_distrib]
    have hsw := sum_finset_erase_swap (univ : Finset (Fin q)) (fun a b => x a * H a b)
    have hsw' : (∑ a : Fin q, ∑ b ∈ univ.erase a, x b * H b a) =
        ∑ a : Fin q, ∑ b ∈ univ.erase a, x b * H a b :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hHsym b a]
    rw [hsw, hsw', sub_self]
  have hterm1 : (∑ a : Fin q, ∑ b ∈ univ.erase a, H a b) =
      (Fintype.card (Fin 4 ↪ Fin q) : ℂ) := by
    have h0 : (∑ a : Fin q, ∑ b ∈ univ.erase a, ((q : ℂ) - 2) * ((q : ℂ) - 3)) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ) := by
      rw [hcard_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => (hconst_ab a b hb).symm
    have hya : (∑ a : Fin q, ∑ b ∈ univ.erase a, (y a) ^ 2) = 0 := by
      have : ∀ a : Fin q, (∑ b ∈ univ.erase a, (y a) ^ 2) = ((q - 1 : ℕ) : ℂ) * (y a) ^ 2 := by
        intro a
        rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
      simp_rw [this, ← Finset.mul_sum, hy2, mul_zero]
    have hyb : (∑ a : Fin q, ∑ b ∈ univ.erase a, (y b) ^ 2) = 0 := by
      rw [← sum_finset_erase_swap (univ : Finset (Fin q)) (fun a b => (y a) ^ 2)]
      exact hya
    have hyab : (∑ a : Fin q, ∑ b ∈ univ.erase a, y a * y b) = 0 := by
      rw [sum_pair_prod univ y, hy, hy2]; ring
    have hHexp : (∑ a : Fin q, ∑ b ∈ univ.erase a, H a b) =
        (∑ a : Fin q, ∑ b ∈ univ.erase a, ((q : ℂ) - 2) * ((q : ℂ) - 3)) -
        t ^ 2 * (2 * (∑ a : Fin q, ∑ b ∈ univ.erase a, (y a) ^ 2) +
                 2 * (∑ a : Fin q, ∑ b ∈ univ.erase a, (y b) ^ 2) +
                 2 * (∑ a : Fin q, ∑ b ∈ univ.erase a, y a * y b)) := by
      simp only [H, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [hHexp, h0, hya, hyb, hyab]; ring
  have hterm3 : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * H a b) =
      -((q : ℂ) - 2) * ((q : ℂ) - 3) * (∑ j, (x j) ^ 2) -
      t ^ 2 * (2 * (∑ j, x j * y j) ^ 2 - 6 * (∑ j, (x j) ^ 2 * (y j) ^ 2)) := by
    have hxx : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b) = -(∑ j, (x j) ^ 2) := by
      rw [sum_pair_prod univ x, hx]; ring
    have hxxy_a : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y a) ^ 2) =
        -(∑ j, (x j) ^ 2 * (y j) ^ 2) := by
      have h1 : ∀ a : Fin q, (∑ b ∈ univ.erase a, x a * x b * (y a) ^ 2) =
          -(x a) ^ 2 * (y a) ^ 2 := by
        intro a
        have hpt : ∀ b : Fin q, x a * x b * (y a) ^ 2 = (x a * (y a) ^ 2) * x b := fun _ => by ring
        simp_rw [hpt, ← Finset.mul_sum, Finset.sum_erase_eq_sub (mem_univ a), hx]
        ring
      simp_rw [h1, neg_mul, Finset.sum_neg_distrib]
    have hxxy_b : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y b) ^ 2) =
        -(∑ j, (x j) ^ 2 * (y j) ^ 2) := by
      have hsw := sum_finset_erase_swap (univ : Finset (Fin q)) (fun a b => x a * x b * (y a) ^ 2)
      have hcon : (∑ a : Fin q, ∑ b ∈ univ.erase a, x b * x a * (y b) ^ 2) =
          ∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y b) ^ 2 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [← hcon, ← hsw, hxxy_a]
    have hxyxy : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y a * y b)) =
        (∑ j, x j * y j) ^ 2 - ∑ j, (x j) ^ 2 * (y j) ^ 2 := by
      have hcon : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y a * y b)) =
          ∑ a : Fin q, ∑ b ∈ univ.erase a, (x a * y a) * (x b * y b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      rw [hcon, sum_pair_prod univ (fun i => x i * y i)]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have h3exp : (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * H a b) =
        ((q : ℂ) - 2) * ((q : ℂ) - 3) * (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b) -
        t ^ 2 * (2 * (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y a) ^ 2) +
                 2 * (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y b) ^ 2) +
                 2 * (∑ a : Fin q, ∑ b ∈ univ.erase a, x a * x b * (y a * y b))) := by
      have hpt : ∀ a b : Fin q, x a * x b * H a b =
          ((q : ℂ) - 2) * ((q : ℂ) - 3) * (x a * x b) -
          t ^ 2 * (2 * (x a * x b * (y a) ^ 2) + 2 * (x a * x b * (y b) ^ 2) +
                   2 * (x a * x b * (y a * y b))) := by
        intro a b; simp only [H]; ring
      simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h3exp, hxx, hxxy_a, hxxy_b, hxyxy]
    ring
  rw [hterm1, hodd_ab, hterm3]
  ring

private lemma permanent_iff_q {q : ℕ} (hq : 4 ≤ q) (x y : Fin q → ℂ)
    (hx : (∑ j, x j) = 0) (hy : (∑ j, y j) = 0) (hy2 : (∑ j, (y j) ^ 2) = 0) :
    (∀ t : ℂ, let rows : Fin 4 → Fin q → ℂ := ![x, -x, t • y, -(t • y)]
      (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
        (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) ↔
      (∑ j, (x j) ^ 2) = 0 ∧ 3 * (∑ j, (x j) ^ 2 * (y j) ^ 2) = (∑ j, x j * y j) ^ 2 := by
  have hcne : ((q : ℂ) - 2) * ((q : ℂ) - 3) ≠ 0 := by
    have h2 : (q : ℂ) - 2 ≠ 0 := by
      intro h
      have : (q : ℂ) = (2 : ℕ) := by push_cast; linear_combination h
      have : q = 2 := Nat.cast_injective this
      omega
    have h3 : (q : ℂ) - 3 ≠ 0 := by
      intro h
      have : (q : ℂ) = (3 : ℕ) := by push_cast; linear_combination h
      have : q = 3 := Nat.cast_injective this
      omega
    exact mul_ne_zero h2 h3
  constructor
  · intro hlevel
    have h0 := (permanent_expand_q hq x y hx hy hy2 0).symm.trans (hlevel 0)
    have h1 := (permanent_expand_q hq x y hx hy hy2 1).symm.trans (hlevel 1)
    have hqx0 : ((q : ℂ) - 2) * ((q : ℂ) - 3) * (∑ j, (x j) ^ 2) = 0 := by
      linear_combination h0
    have hqx : (∑ j, (x j) ^ 2) = 0 := (mul_eq_zero.mp hqx0).resolve_left hcne
    exact ⟨hqx, by linear_combination (h0 - h1) / 2⟩
  · rintro ⟨hqx, hxy⟩ t
    refine (permanent_expand_q hq x y hx hy hy2 t).trans ?_
    rw [hqx, ← hxy]
    ring

private lemma charpoly_factor {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (operator : Module.End ℂ V) (space : Submodule ℂ V)
    (stable : space ≤ space.comap operator) :
    operator.charpoly = (operator.restrict stable).charpoly *
      (space.mapQ space operator stable).charpoly := by
  apply Polynomial.funext
  intro value
  simp only [eval_mul, LinearMap.eval_charpoly]
  let shift := algebraMap ℂ (Module.End ℂ V) value - operator
  have hshift : space ≤ space.comap shift := fun vector hvector => by
    change value • vector - operator vector ∈ space
    exact space.sub_mem (space.smul_mem _ hvector) (stable hvector)
  have hrest : shift.restrict hshift = algebraMap ℂ (Module.End ℂ space) value -
      operator.restrict stable := by
    ext vector : 1
    apply Subtype.ext
    rfl
  have hquot : space.mapQ space shift hshift =
      algebraMap ℂ (Module.End ℂ (V ⧸ space)) value - space.mapQ space operator stable := by
    apply LinearMap.ext
    intro vector
    obtain ⟨source, rfl⟩ := space.mkQ_surjective vector
    change space.mkQ (value • source - operator source) =
      value • space.mkQ source - space.mkQ (operator source)
    rw [map_sub, map_smul]
  exact (LinearMap.det_eq_det_mul_det space shift hshift).trans (by rw [hrest, hquot])

private lemma charpoly_dual {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (operator : Module.End ℂ V) :
    operator.dualMap.charpoly = operator.charpoly := by
  apply Polynomial.funext
  intro value
  rw [LinearMap.eval_charpoly, LinearMap.eval_charpoly,
    ← LinearMap.det_dualMap (algebraMap ℂ (Module.End ℂ V) value - operator)]
  congr 1
  ext vector source : 2
  simp [LinearMap.dualMap_apply]

private lemma orthogonal_stable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (form : LinearMap.BilinForm ℂ V) (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    (space : Submodule ℂ V) (stable : space ≤ space.comap operator) :
    form.orthogonal space ≤ (form.orthogonal space).comap operator := by
  intro vector hvector
  change operator vector ∈ form.orthogonal space
  intro source hsource
  rw [← adjoint]
  exact hvector (operator source) (stable hsource)

private lemma charpoly_orthogonal_quotient {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (form : LinearMap.BilinForm ℂ V)
    (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    (space : Submodule ℂ V) (stable : space ≤ space.comap operator) :
    ((form.orthogonal space).mapQ (form.orthogonal space) operator
      (orthogonal_stable form operator adjoint space stable)).charpoly =
        (operator.restrict stable).charpoly := by
  let orth := form.orthogonal space
  let pairing : V →ₗ[ℂ] Module.Dual ℂ space := space.dualRestrict.comp form
  have hsurj : Function.Surjective pairing :=
    Subspace.dualRestrict_surjective.comp (form.toDual nondegenerate).surjective
  have hker : orth = LinearMap.ker pairing := by
    ext vector
    rw [LinearMap.mem_ker]
    exact ⟨fun h => LinearMap.ext fun source =>
        (symmetric.eq vector source).trans (h source source.property),
      fun h source hsource =>
        (symmetric.eq source vector).trans (LinearMap.congr_fun h ⟨source, hsource⟩)⟩
  let quotientEquiv : (V ⧸ orth) ≃ₗ[ℂ] Module.Dual ℂ space :=
    (Submodule.quotEquivOfEq orth (LinearMap.ker pairing) hker).trans
      (pairing.quotKerEquivOfSurjective hsurj)
  have hpair (vector : V) : quotientEquiv (orth.mkQ vector) = pairing vector := by
    simp [quotientEquiv, Submodule.mkQ_apply]
  let quotientOperator := orth.mapQ orth operator
    (orthogonal_stable form operator adjoint space stable)
  have hconj : quotientEquiv.conj quotientOperator = (operator.restrict stable).dualMap := by
    ext function source : 2
    obtain ⟨vector, rfl⟩ := quotientEquiv.surjective function
    obtain ⟨vector, rfl⟩ := orth.mkQ_surjective vector
    change quotientEquiv (quotientOperator (quotientEquiv.symm (quotientEquiv (orth.mkQ vector))))
      source = _
    rw [quotientEquiv.symm_apply_apply]
    change quotientEquiv (orth.mkQ (operator vector)) source = _
    rw [hpair, hpair]
    exact adjoint vector source
  exact (quotientEquiv.charpoly_conj quotientOperator).symm.trans
    ((congrArg LinearMap.charpoly hconj).trans (charpoly_dual _))

private lemma stable_line {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Module.End ℂ V) {vector : V} {value : ℂ} (heig : operator vector = value • vector) :
    (ℂ ∙ vector) ≤ (ℂ ∙ vector).comap operator := by
  intro source hsource
  obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp hsource
  change operator (scalar • vector) ∈ ℂ ∙ vector
  rw [map_smul, heig, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private lemma scalar_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (value : ℂ) : (algebraMap ℂ (Module.End ℂ V) value).charpoly =
      (X - C value) ^ finrank ℂ V := by
  apply Polynomial.funext
  intro point
  rw [LinearMap.eval_charpoly, ← map_sub, Algebra.algebraMap_eq_smul_one, LinearMap.det_smul]
  simp

private lemma line_charpoly {V : Type*} [AddCommGroup V] [Module ℂ V]
    (operator : Module.End ℂ V) {vector : V} (hnz : vector ≠ 0) {value : ℂ}
    (heig : operator vector = value • vector) :
    (operator.restrict (stable_line operator heig)).charpoly = X - C value := by
  have hscalar : operator.restrict (stable_line operator heig) =
      algebraMap ℂ (Module.End ℂ (ℂ ∙ vector)) value := by
    apply LinearMap.ext
    rintro ⟨source, hsource⟩
    obtain ⟨scalar, rfl⟩ := Submodule.mem_span_singleton.mp hsource
    apply Subtype.ext
    change operator (scalar • vector) = value • (scalar • vector)
    rw [map_smul, heig, smul_smul, smul_smul, mul_comm]
  rw [hscalar, scalar_charpoly, finrank_span_singleton hnz, pow_one]

private lemma linear_factor_of_square {value : ℂ} {root other : ℂ[X]}
    (hf : root ^ 2 = (X - C value) * other) :
    ∃ factor : ℂ[X], root = (X - C value) * factor ∧
      other = (X - C value) * factor ^ 2 := by
  have hzero := congrArg (Polynomial.eval value) hf
  have heval : root.eval value = 0 := by
    simp only [eval_pow, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
      pow_eq_zero_iff (by decide : 2 ≠ 0)] at hzero
    exact hzero
  obtain ⟨factor, hfactor⟩ := (dvd_iff_isRoot.mpr heval : X - C value ∣ root)
  refine ⟨factor, hfactor, ?_⟩
  apply mul_left_cancel₀ (X_sub_C_ne_zero value)
  calc
    _ = root ^ 2 := hf.symm
    _ = _ := by rw [hfactor]; ring

private lemma isotropic_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [Nontrivial V] (form : LinearMap.BilinForm ℂ V)
    (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    {root : ℂ[X]} (hsquare : operator.charpoly = root ^ 2) :
    ∃ value : ℂ, ∃ vector : V, vector ≠ 0 ∧ operator vector = value • vector ∧ form vector vector = 0 := by
  obtain ⟨value, hvalue⟩ := operator.exists_eigenvalue
  obtain ⟨vector, hvector, hnz⟩ := hvalue.exists_hasEigenvector
  have heig := Module.End.mem_eigenspace_iff.mp hvector
  by_cases hnorm : form vector vector = 0
  · exact ⟨value, vector, hnz, heig, hnorm⟩
  let line := ℂ ∙ vector
  let orth := form.orthogonal line
  have hline := stable_line operator heig
  have horth := orthogonal_stable form operator adjoint line hline
  let restricted : Module.End ℂ orth := operator.restrict (p := orth) (q := orth) horth
  have hfactor : root ^ 2 = (X - C value) * restricted.charpoly := by
    rw [← hsquare, charpoly_factor operator orth horth,
      charpoly_orthogonal_quotient form symmetric nondegenerate operator adjoint line hline,
      line_charpoly operator hnz heig, mul_comm]
  obtain ⟨factor, _, hfactor⟩ := linear_factor_of_square hfactor
  have hvalue' : restricted.HasEigenvalue value := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, hfactor]
    simp [Polynomial.IsRoot]
  obtain ⟨other, hother, hothernz⟩ := hvalue'.exists_hasEigenvector
  have hothereig : operator (other : V) = value • (other : V) :=
    congrArg Subtype.val (Module.End.mem_eigenspace_iff.mp hother)
  have horthog : form vector (other : V) = 0 := other.property vector (Submodule.mem_span_singleton_self _)
  obtain ⟨coef, hcoef⟩ := IsAlgClosed.exists_pow_nat_eq
    (-(form (other : V) (other : V)) / form vector vector) (by decide : 0 < 2)
  refine ⟨value, coef • vector + (other : V), ?_, ?_, ?_⟩
  · intro hzero
    have hcoefzero : coef * form vector vector = 0 := by
      simpa [map_add, map_smul, horthog] using congrArg (form vector) hzero
    have hcz := (mul_eq_zero.mp hcoefzero).resolve_right hnorm
    apply hothernz
    apply Subtype.ext
    simpa [hcz] using hzero
  · simp only [map_add, map_smul, heig, hothereig, smul_add, smul_smul]
    rw [mul_comm coef value]
  · have horthog' : form (other : V) vector = 0 := (symmetric.eq _ _).trans horthog
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      horthog, horthog', mul_zero, add_zero, zero_add]
    have hc := (eq_div_iff hnorm).mp hcoef
    linear_combination hc

private lemma square_of_half_isotropic {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {k : ℕ} (dimension : finrank ℂ V = 2 * k)
    (form : LinearMap.BilinForm ℂ V) (symmetric : form.IsSymm) (nondegenerate : form.Nondegenerate)
    (operator : Module.End ℂ V)
    (adjoint : ∀ left right, form (operator left) right = form left (operator right))
    (space : Submodule ℂ V) (rank : finrank ℂ space = k)
    (isotropic : space ≤ form.orthogonal space) (stable : space ≤ space.comap operator) :
    ∃ root : ℂ[X], operator.charpoly = root ^ 2 := by
  have horth : form.orthogonal space = space := by
    symm
    apply Submodule.eq_of_le_of_finrank_le isotropic
    rw [form.finrank_orthogonal nondegenerate, dimension, rank]
    omega
  have hstable := orthogonal_stable form operator adjoint space stable
  have hquot := charpoly_orthogonal_quotient form symmetric nondegenerate operator adjoint space stable
  have hfact := charpoly_factor operator (form.orthogonal space) hstable
  rw [hquot] at hfact
  have hrest : (operator.restrict hstable).charpoly = (operator.restrict stable).charpoly := by
    have same (other : Submodule ℂ V) (hother : other ≤ other.comap operator) (heq : other = space) :
        (operator.restrict hother).charpoly = (operator.restrict stable).charpoly := by
      subst other
      rfl
    exact same _ hstable horth
  exact ⟨_, by rw [hfact, hrest, pow_two]⟩

private lemma half_isotropic_of_square : ∀ (k : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V],
    finrank ℂ V = 2 * k →
    ∀ (form : LinearMap.BilinForm ℂ V), form.IsSymm → form.Nondegenerate →
    ∀ (operator : Module.End ℂ V),
    (∀ left right, form (operator left) right = form left (operator right)) →
    ∀ {root : ℂ[X]}, operator.charpoly = root ^ 2 →
    ∃ K : Submodule ℂ V, finrank ℂ K = k ∧ K ≤ form.orthogonal K ∧ K ≤ K.comap operator
  | 0, V, _, _, _, _, _, _, _, _, _, _, _ =>
      ⟨⊥, finrank_bot ℂ V, by simp, by simp⟩
  | k + 1, V, _, _, _, dimension, form, symmetric, nondegenerate, operator, adjoint, root, hsquare => by
      let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      obtain ⟨value, vector, hnz, heig, hiso⟩ :=
        isotropic_eigenvector form symmetric nondegenerate operator adjoint hsquare
      let line := ℂ ∙ vector
      let orth := form.orthogonal line
      let hline := stable_line operator heig
      let horth := orthogonal_stable form operator adjoint line hline
      have hsub : line ≤ orth := by
        intro left hleft right hright
        obtain ⟨scalarLeft, rfl⟩ := Submodule.mem_span_singleton.mp hleft
        obtain ⟨scalarRight, rfl⟩ := Submodule.mem_span_singleton.mp hright
        simp [hiso]
      let line' := line.comap orth.subtype
      let restrictOp := operator.restrict (p := orth) (q := orth) horth
      have hline' : line' ≤ line'.comap restrictOp := fun elem helem => hline helem
      let quotientOp := line'.mapQ line' restrictOp hline'
      have hlineRank : finrank ℂ line' = 1 :=
        (Submodule.comapSubtypeEquivOfLe hsub).finrank_eq.trans (finrank_span_singleton hnz)
      have hOrthRank : finrank ℂ orth = 2 * k + 1 := by
        change finrank ℂ (form.orthogonal line) = 2 * k + 1
        rw [form.finrank_orthogonal nondegenerate, dimension, finrank_span_singleton hnz]
        omega
      have hQuotientRank : finrank ℂ (orth ⧸ line') = 2 * k := by
        have hd := line'.finrank_quotient_add_finrank
        rw [hlineRank, hOrthRank] at hd
        omega
      have hlineChar : (restrictOp.restrict hline').charpoly = X - C value := by
        have hscalar : restrictOp.restrict hline' = algebraMap ℂ (Module.End ℂ line') value := by
          apply LinearMap.ext
          rintro ⟨⟨source, hsource⟩, hsource'⟩
          obtain ⟨coef, heq⟩ := Submodule.mem_span_singleton.mp (show source ∈ line from hsource')
          apply Subtype.ext
          apply Subtype.ext
          change operator source = value • source
          rw [← heq, map_smul, heig, smul_smul, smul_smul, mul_comm]
        rw [hscalar, scalar_charpoly, hlineRank, pow_one]
      have hfactor : root ^ 2 = (X - C value) ^ 2 * quotientOp.charpoly := by
        have hquot := charpoly_orthogonal_quotient form symmetric nondegenerate operator adjoint line hline
        have houter := charpoly_factor operator orth horth
        have hinner := charpoly_factor restrictOp line' hline'
        rw [← hsquare, houter, hquot, line_charpoly operator hnz heig, hinner, hlineChar]
        change ((X - C value) * quotientOp.charpoly) * (X - C value) = _
        ring
      obtain ⟨quotientRoot, _, hroot⟩ := linear_factor_of_square (value := value)
        (other := (X - C value) * quotientOp.charpoly) (by rw [hfactor, pow_two, mul_assoc])
      have hsquareQuotient : quotientOp.charpoly = quotientRoot ^ 2 :=
        mul_left_cancel₀ (X_sub_C_ne_zero value) hroot
      let restrictForm := form.restrict orth
      have hrad : line' ≤ restrictForm.ker := by
        intro left hleft
        apply LinearMap.mem_ker.mpr
        apply LinearMap.ext
        intro right
        exact right.property left hleft
      have hrad' : line' ≤ restrictForm.flip.ker := by
        intro left hleft
        apply LinearMap.mem_ker.mpr
        apply LinearMap.ext
        intro right
        exact (symmetric.eq right left).trans (right.property left hleft)
      let quotientForm : LinearMap.BilinForm ℂ (orth ⧸ line') :=
        restrictForm.liftQ₂ line' line' hrad hrad'
      have hsymm : quotientForm.IsSymm := by
        constructor
        intro left right
        obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
        obtain ⟨right, rfl⟩ := line'.mkQ_surjective right
        exact symmetric.eq left right
      have hnondeg : quotientForm.Nondegenerate :=
        hsymm.isRefl.nondegenerate_iff_separatingLeft.mpr (by
          intro left hleft
          obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
          apply (Submodule.Quotient.mk_eq_zero line').mpr
          change (left : V) ∈ line
          rw [← form.orthogonal_orthogonal nondegenerate symmetric.isRefl line]
          intro source hsource
          exact (symmetric.eq source left).trans (hleft (line'.mkQ ⟨source, hsource⟩)))
      have hadjoint : ∀ left right, quotientForm (quotientOp left) right =
          quotientForm left (quotientOp right) := by
        intro left right
        obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
        obtain ⟨right, rfl⟩ := line'.mkQ_surjective right
        exact adjoint left right
      obtain ⟨K', hK'rank, hK'iso, hK'stab⟩ :=
        half_isotropic_of_square k hQuotientRank quotientForm hsymm hnondeg
          quotientOp hadjoint hsquareQuotient
      let lifted := K'.comap line'.mkQ
      let projected : lifted →ₗ[ℂ] K' := LinearMap.codRestrict K'
        (line'.mkQ.comp lifted.subtype) (fun elem => elem.property)
      have hsurj : Function.Surjective projected := by
        rintro ⟨elem, helem⟩
        obtain ⟨source, rfl⟩ := line'.mkQ_surjective elem
        exact ⟨⟨source, helem⟩, rfl⟩
      have hcontained : line' ≤ lifted := by
        intro elem helem
        change line'.mkQ elem ∈ K'
        have hzero : line'.mkQ elem = 0 := (Submodule.Quotient.mk_eq_zero line').mpr helem
        simp [hzero]
      have hker : LinearMap.ker projected = line'.comap lifted.subtype := by
        ext elem
        rw [LinearMap.mem_ker, Subtype.ext_iff]
        exact Submodule.Quotient.mk_eq_zero line'
      have hliftRank : finrank ℂ lifted = k + 1 := by
        rw [← LinearMap.finrank_range_add_finrank_ker projected,
          LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
          (Submodule.comapSubtypeEquivOfLe hcontained).finrank_eq, hlineRank, hK'rank]
      refine ⟨lifted.map orth.subtype, (Submodule.finrank_map_subtype_eq _ _).trans hliftRank, ?_, ?_⟩
      · rintro left ⟨left, hleft, rfl⟩ right ⟨right, hright, rfl⟩
        change quotientForm (line'.mkQ right) (line'.mkQ left) = 0
        exact hK'iso hleft (line'.mkQ right) hright
      · rintro elem ⟨elem, helem, rfl⟩
        refine ⟨restrictOp elem, ?_, rfl⟩
        change quotientOp (line'.mkQ elem) ∈ K'
        exact hK'stab helem

private lemma eval_finset_sum' {α : Type*} (s : Finset α) (f : α → ℂ[X]) (x : ℂ) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma coeff_finset_sum' {α : Type*} (s : Finset α) (f : α → ℂ[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private lemma lagrange_moment_zero {m : ℕ} (hm : 2 ≤ m) (μ : Fin m → ℂ)
    (hinj : Function.Injective μ) (p : ℕ) (hp : p + 1 < m) :
    (∑ j : Fin m, (∏ i ∈ Finset.univ.erase j, (μ j - μ i))⁻¹ * (μ j) ^ p) = 0 := by
  let w : Fin m → ℂ := fun j => (∏ i ∈ Finset.univ.erase j, (μ j - μ i))⁻¹
  let L : Fin m → ℂ[X] := fun j => ∏ i ∈ Finset.univ.erase j, (X - C (μ i))
  have hLmonic : ∀ j : Fin m, (L j).Monic := fun j =>
    Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (μ i))
  have hLdeg : ∀ j : Fin m, (L j).natDegree = m - 1 := by
    intro j
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C (μ i))]
    simp [Finset.card_erase_of_mem (mem_univ j)]
  have hLeval_self : ∀ j : Fin m, (L j).eval (μ j) = ∏ i ∈ Finset.univ.erase j, (μ j - μ i) := by
    intro j
    simp [L, Polynomial.eval_prod]
  have hLeval_ne : ∀ j t : Fin m, t ≠ j → (L j).eval (μ t) = 0 := by
    intro j t hne
    simp only [L, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    exact Finset.prod_eq_zero (mem_erase.mpr ⟨hne, mem_univ t⟩) (sub_self _)
  have hprod_ne : ∀ j : Fin m, (∏ i ∈ Finset.univ.erase j, (μ j - μ i)) ≠ 0 := by
    intro j
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    exact sub_ne_zero.mpr (hinj.ne (mem_erase.mp hi).1.symm)
  let F : ℂ[X] := X ^ p - ∑ j : Fin m, C (w j * (μ j) ^ p) * L j
  have hFeval : ∀ t : Fin m, F.eval (μ t) = 0 := by
    intro t
    simp only [F, eval_sub, eval_pow, eval_X, eval_finset_sum', eval_mul, eval_C]
    rw [Finset.sum_eq_single t]
    · rw [hLeval_self t]
      have hinv : w t * (∏ i ∈ Finset.univ.erase t, (μ t - μ i)) = 1 :=
        inv_mul_cancel₀ (hprod_ne t)
      linear_combination -(μ t) ^ p * hinv
    · intro j _ hne
      rw [hLeval_ne j t hne.symm, mul_zero]
    · intro h; exact absurd (mem_univ t) h
  have hFdeg : F.natDegree ≤ m - 1 := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (Polynomial.natDegree_X_pow_le p) (by omega)
    · refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_le]
      refine ⟨by omega, fun j _ => ?_⟩
      exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by rw [hLdeg j])
  have hFzero : F = 0 := by
    by_contra hne
    have hsub : Finset.univ.image μ ⊆ F.roots.toFinset := by
      intro z hz
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hFeval t
    have hcard : m ≤ F.natDegree := calc
      m = (Finset.univ.image μ).card := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      _ ≤ F.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ F.roots.card := Multiset.toFinset_card_le _
      _ ≤ F.natDegree := Polynomial.card_roots' F
    omega
  have hcoeff := congrArg (fun P : ℂ[X] => P.coeff (m - 1)) hFzero
  simp only [F, coeff_sub, coeff_zero, coeff_X_pow, coeff_finset_sum', coeff_C_mul] at hcoeff
  rw [if_neg (by omega : m - 1 ≠ p), zero_sub, neg_eq_zero] at hcoeff
  have hlead : ∀ j : Fin m, (L j).coeff (m - 1) = 1 := by
    intro j
    rw [← hLdeg j, ← Polynomial.leadingCoeff, (hLmonic j).leadingCoeff]
  simpa [w, hlead] using hcoeff

private lemma orthonormal_eigenbasis_of_no_iso : ∀ (d : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V],
    finrank ℂ V = d →
    ∀ (form : LinearMap.BilinForm ℂ V), form.IsSymm → form.Nondegenerate →
    ∀ (operator : Module.End ℂ V),
    (∀ left right, form (operator left) right = form left (operator right)) →
    (∀ (μ : ℂ) (v : V), v ≠ 0 → operator v = μ • v → form v v ≠ 0) →
    ∃ (e : Fin d → V) (μ : Fin d → ℂ),
      Function.Injective μ ∧
      (∀ i, operator (e i) = μ i • e i) ∧
      (∀ i j, form (e i) (e j) = if i = j then 1 else 0)
  | 0, V, _, _, _, _, _, _, _, _, _, _ =>
      ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | d + 1, V, _, _, _, hdim, form, symmetric, nondegenerate, operator, adjoint, hno => by
      let : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
      obtain ⟨μ0, hμ0⟩ := operator.exists_eigenvalue
      obtain ⟨v0, hv0, hv0nz⟩ := hμ0.exists_hasEigenvector
      have hv0eig : operator v0 = μ0 • v0 := Module.End.mem_eigenspace_iff.mp hv0
      have hvv : form v0 v0 ≠ 0 := hno μ0 v0 hv0nz hv0eig
      obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (form v0 v0)⁻¹ (by decide : 0 < 2)
      let e0 : V := s • v0
      have he0eig : operator e0 = μ0 • e0 := by
        simp only [e0, map_smul, hv0eig, smul_smul, mul_comm]
      have he0norm : form e0 e0 = 1 := by
        simp only [e0, map_smul, LinearMap.smul_apply, smul_eq_mul]
        calc
          s * (s * form v0 v0) = s ^ 2 * form v0 v0 := by ring
          _ = (form v0 v0)⁻¹ * form v0 v0 := by rw [hs]
          _ = 1 := inv_mul_cancel₀ hvv
      have he0nz : e0 ≠ 0 := by
        intro h
        rw [h] at he0norm
        simp at he0norm
      let line := ℂ ∙ e0
      let W := form.orthogonal line
      have hline := stable_line operator he0eig
      have hWstab := orthogonal_stable form operator adjoint line hline
      have hWdim : finrank ℂ W = d := by
        change finrank ℂ (form.orthogonal line) = d
        rw [form.finrank_orthogonal nondegenerate, hdim, finrank_span_singleton he0nz]
        omega
      let formW := form.restrict W
      have hWsymm : formW.IsSymm := ⟨fun x y => symmetric.eq x y⟩
      have hWnondeg : formW.Nondegenerate :=
        hWsymm.isRefl.nondegenerate_iff_separatingLeft.mpr (by
          intro w hw
          apply Subtype.ext
          apply (symmetric.isRefl.nondegenerate_iff_separatingLeft.mp nondegenerate) (w : V)
          intro z
          let z' : V := z - form e0 z • e0
          have hz' : z' ∈ W := by
            intro u hu
            obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
            simp only [z', map_sub, map_smul, LinearMap.smul_apply,
              smul_eq_mul, he0norm, mul_one]
            ring
          have hwe0 : form (w : V) e0 = 0 :=
            (symmetric.eq (w : V) e0).trans (w.property e0 (Submodule.mem_span_singleton_self _))
          have hwz' : form (w : V) z' = 0 := hw ⟨z', hz'⟩
          have hz_eq : z = form e0 z • e0 + z' := by simp [z']
          rw [hz_eq, map_add, map_smul, hwe0, hwz', smul_zero, add_zero])
      let opW : Module.End ℂ W := operator.restrict (p := W) (q := W) hWstab
      have hWadj : ∀ x y : W, formW (opW x) y = formW x (opW y) := fun x y => adjoint x y
      have hWno : ∀ (μ : ℂ) (w : W), w ≠ 0 → opW w = μ • w → formW w w ≠ 0 := by
        intro μ w hwnz hweig
        exact hno μ (w : V) (fun h => hwnz (Subtype.ext h)) (congrArg Subtype.val hweig)
      obtain ⟨e', μ', _, he'eig, he'form⟩ :=
        orthonormal_eigenbasis_of_no_iso d hWdim formW hWsymm hWnondeg opW hWadj hWno
      let e : Fin (d + 1) → V := Fin.cons e0 (fun i => (e' i : V))
      let μ : Fin (d + 1) → ℂ := Fin.cons μ0 μ'
      have heig : ∀ i, operator (e i) = μ i • e i := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact he0eig
        · intro j; exact congrArg Subtype.val (he'eig j)
      have hform : ∀ i j, form (e i) (e j) = if i = j then 1 else 0 := by
        intro i j
        refine Fin.cases ?_ ?_ i <;> refine Fin.cases ?_ ?_ j
        · simp [e, he0norm]
        · intro k
          simp only [e, Fin.cons_zero, Fin.cons_succ]
          rw [if_neg (Fin.succ_ne_zero k).symm]
          exact (e' k).property e0 (Submodule.mem_span_singleton_self _)
        · intro k
          simp only [e, Fin.cons_zero, Fin.cons_succ, Fin.succ_ne_zero, ite_false]
          exact (symmetric.eq _ _).trans ((e' k).property e0 (Submodule.mem_span_singleton_self _))
        · intro k l
          simp only [e, Fin.cons_succ, Fin.succ_inj]
          exact he'form l k
      have hinj : Function.Injective μ := by
        intro i j hij
        by_contra hne
        let v : V := e i + Complex.I • e j
        have hvnz : v ≠ 0 := by
          intro hv
          have h1 := congrArg (form (e i)) hv
          simp only [v, map_add, map_smul, map_zero, hform i i, hform i j, ite_true,
            if_neg hne, smul_zero, add_zero] at h1
          exact one_ne_zero h1
        have hveig : operator v = μ i • v := by
          simp only [v, map_add, map_smul, heig i, heig j, hij, smul_add, smul_smul, mul_comm]
        have hviso : form v v = 0 := by
          simp only [v, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            hform i i, hform j j, hform i j, hform j i, ite_true, if_neg hne, if_neg (Ne.symm hne)]
          have hI : Complex.I ^ 2 = -1 := Complex.I_sq
          linear_combination hI
        exact hno (μ i) v hvnz hveig hviso
      exact ⟨e, μ, hinj, heig, hform⟩

private lemma sim_isotropic_of_lt : ∀ (k : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V],
    2 * k + 1 ≤ finrank ℂ V →
    ∀ (form : LinearMap.BilinForm ℂ V), form.IsSymm → form.Nondegenerate →
    ∀ (operator : Module.End ℂ V),
    (∀ left right, form (operator left) right = form left (operator right)) →
    ∃ K : Submodule ℂ V, finrank ℂ K = k ∧
      K ≤ form.orthogonal K ∧ ∀ x ∈ K, form (operator x) x = 0
  | 0, V, _, _, _, _, _, _, _, _, _ =>
      ⟨⊥, finrank_bot ℂ V, by simp, by simp⟩
  | k + 1, V, _, _, _, hle, form, symmetric, nondegenerate, operator, adjoint => by
      by_cases hiso : ∃ (value : ℂ) (vector : V), vector ≠ 0 ∧
          operator vector = value • vector ∧ form vector vector = 0
      · obtain ⟨value, vector, hnz, heig, hv_iso⟩ := hiso
        let line := ℂ ∙ vector
        let orth := form.orthogonal line
        let hline := stable_line operator heig
        let horth := orthogonal_stable form operator adjoint line hline
        have hsub : line ≤ orth := by
          intro left hleft right hright
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hleft
          obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hright
          simp [hv_iso]
        let line' := line.comap orth.subtype
        let restrictOp := operator.restrict (p := orth) (q := orth) horth
        have hline' : line' ≤ line'.comap restrictOp := fun elem helem => hline helem
        let quotientOp := line'.mapQ line' restrictOp hline'
        have hlineRank : finrank ℂ line' = 1 :=
          (Submodule.comapSubtypeEquivOfLe hsub).finrank_eq.trans (finrank_span_singleton hnz)
        have hOrthRank : finrank ℂ orth = finrank ℂ V - 1 := by
          change finrank ℂ (form.orthogonal line) = finrank ℂ V - 1
          rw [form.finrank_orthogonal nondegenerate, finrank_span_singleton hnz]
        have hQuotientRank : 2 * k + 1 ≤ finrank ℂ (orth ⧸ line') := by
          have hd := line'.finrank_quotient_add_finrank
          rw [hlineRank, hOrthRank] at hd
          omega
        let restrictForm := form.restrict orth
        have hrad : line' ≤ restrictForm.ker := by
          intro left hleft
          apply LinearMap.mem_ker.mpr
          apply LinearMap.ext
          intro right
          exact right.property left hleft
        have hrad' : line' ≤ restrictForm.flip.ker := by
          intro left hleft
          apply LinearMap.mem_ker.mpr
          apply LinearMap.ext
          intro right
          exact (symmetric.eq right left).trans (right.property left hleft)
        let quotientForm : LinearMap.BilinForm ℂ (orth ⧸ line') :=
          restrictForm.liftQ₂ line' line' hrad hrad'
        have hsymm : quotientForm.IsSymm := by
          constructor
          intro left right
          obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
          obtain ⟨right, rfl⟩ := line'.mkQ_surjective right
          exact symmetric.eq left right
        have hnondeg : quotientForm.Nondegenerate :=
          hsymm.isRefl.nondegenerate_iff_separatingLeft.mpr (by
            intro left hleft
            obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
            apply (Submodule.Quotient.mk_eq_zero line').mpr
            change (left : V) ∈ line
            rw [← form.orthogonal_orthogonal nondegenerate symmetric.isRefl line]
            intro source hsource
            exact (symmetric.eq source left).trans (hleft (line'.mkQ ⟨source, hsource⟩)))
        have hadjoint : ∀ left right, quotientForm (quotientOp left) right =
            quotientForm left (quotientOp right) := by
          intro left right
          obtain ⟨left, rfl⟩ := line'.mkQ_surjective left
          obtain ⟨right, rfl⟩ := line'.mkQ_surjective right
          exact adjoint left right
        obtain ⟨K', hK'rank, hK'iso, hK'op⟩ :=
          sim_isotropic_of_lt k hQuotientRank quotientForm hsymm hnondeg quotientOp hadjoint
        let lifted := K'.comap line'.mkQ
        let projected : lifted →ₗ[ℂ] K' := LinearMap.codRestrict K'
          (line'.mkQ.comp lifted.subtype) (fun elem => elem.property)
        have hsurj : Function.Surjective projected := by
          rintro ⟨elem, helem⟩
          obtain ⟨source, rfl⟩ := line'.mkQ_surjective elem
          exact ⟨⟨source, helem⟩, rfl⟩
        have hcontained : line' ≤ lifted := by
          intro elem helem
          change line'.mkQ elem ∈ K'
          have hzero : line'.mkQ elem = 0 := (Submodule.Quotient.mk_eq_zero line').mpr helem
          simp [hzero]
        have hker : LinearMap.ker projected = line'.comap lifted.subtype := by
          ext elem
          rw [LinearMap.mem_ker, Subtype.ext_iff]
          exact Submodule.Quotient.mk_eq_zero line'
        have hliftRank : finrank ℂ lifted = k + 1 := by
          rw [← LinearMap.finrank_range_add_finrank_ker projected,
            LinearMap.range_eq_top.mpr hsurj, finrank_top, hker,
            (Submodule.comapSubtypeEquivOfLe hcontained).finrank_eq, hlineRank, hK'rank]
        refine ⟨lifted.map orth.subtype, (Submodule.finrank_map_subtype_eq _ _).trans hliftRank, ?_, ?_⟩
        · rintro left ⟨left, hleft, rfl⟩ right ⟨right, hright, rfl⟩
          change quotientForm (line'.mkQ right) (line'.mkQ left) = 0
          exact hK'iso hleft (line'.mkQ right) hright
        · rintro elem ⟨elem, helem, rfl⟩
          change quotientForm (quotientOp (line'.mkQ elem)) (line'.mkQ elem) = 0
          exact hK'op (line'.mkQ elem) helem
      · have hno : ∀ (μ : ℂ) (v : V), v ≠ 0 → operator v = μ • v → form v v ≠ 0 := by
          intro μ v hvnz hveig hviso
          exact hiso ⟨μ, v, hvnz, hveig, hviso⟩
        obtain ⟨e, μ, hinj, heig, hform⟩ :=
          orthonormal_eigenbasis_of_no_iso (finrank ℂ V) rfl form symmetric nondegenerate
            operator adjoint hno
        let m : ℕ := 2 * (k + 1) + 1
        let emb : Fin m → Fin (finrank ℂ V) := Fin.castLE hle
        have hemb_inj : Function.Injective emb := fun a b hab =>
          Fin.ext (by simpa [emb] using congrArg Fin.val hab)
        let μ' : Fin m → ℂ := fun j => μ (emb j)
        have hμ'_inj : Function.Injective μ' := hinj.comp hemb_inj
        let w : Fin m → ℂ := fun j => (∏ i ∈ Finset.univ.erase j, (μ' j - μ' i))⁻¹
        have hw_ne : ∀ j : Fin m, w j ≠ 0 := by
          intro j
          apply inv_ne_zero
          rw [Finset.prod_ne_zero_iff]
          intro i hi
          exact sub_ne_zero.mpr (hμ'_inj.ne (mem_erase.mp hi).1.symm)
        have hsqrt : ∀ j : Fin m, ∃ c : ℂ, c ^ 2 = w j :=
          fun j => IsAlgClosed.exists_pow_nat_eq (w j) (by decide : 0 < 2)
        let c : Fin m → ℂ := fun j => Classical.choose (hsqrt j)
        have hc2 : ∀ j : Fin m, (c j) ^ 2 = w j := fun j => Classical.choose_spec (hsqrt j)
        have hc_ne : ∀ j : Fin m, c j ≠ 0 := by
          intro j h0
          have := hc2 j
          rw [h0] at this
          exact hw_ne j (by simpa using this.symm)
        let u : Fin (k + 1) → V := fun r => ∑ j : Fin m, (c j * (μ' j) ^ (r : ℕ)) • e (emb j)
        have hform_e : ∀ j l : Fin m, form (e (emb j)) (e (emb l)) = if j = l then 1 else 0 := by
          intro j l
          rw [hform (emb j) (emb l)]
          by_cases h : j = l
          · subst h; simp
          · rw [if_neg (hemb_inj.ne h), if_neg h]
        have hform_eu : ∀ (s : Fin (k + 1)) (j : Fin m),
            form (e (emb j)) (u s) = c j * (μ' j) ^ (s : ℕ) := by
          intro s j
          simp only [u, map_sum, map_smul, smul_eq_mul, hform_e]
          rw [Finset.sum_eq_single j]
          · simp
          · intro l _ hne; rw [if_neg hne.symm, mul_zero]
          · intro h; exact absurd (mem_univ j) h
        have hform_u : ∀ r s : Fin (k + 1), form (u r) (u s) = 0 := by
          intro r s
          conv_lhs => rw [show u r = ∑ j : Fin m, (c j * (μ' j) ^ (r : ℕ)) • e (emb j) from rfl]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            hform_eu]
          have h2 : (∑ j : Fin m, c j * (μ' j) ^ (r : ℕ) * (c j * (μ' j) ^ (s : ℕ))) =
              ∑ j : Fin m, w j * (μ' j) ^ ((r : ℕ) + (s : ℕ)) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hc2 j, pow_add]
            ring
          rw [h2]
          exact lagrange_moment_zero (by omega : 2 ≤ m) μ' hμ'_inj ((r : ℕ) + (s : ℕ))
            (by have := r.isLt; have := s.isLt; omega)
        have hform_Tu : ∀ r s : Fin (k + 1), form (operator (u r)) (u s) = 0 := by
          intro r s
          have hTu : operator (u r) = ∑ j : Fin m, (c j * (μ' j) ^ ((r : ℕ) + 1)) • e (emb j) := by
            simp only [u, map_sum, map_smul, heig]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_smul, pow_succ]
            congr 1
            ring
          rw [hTu]
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            hform_eu]
          have h2 : (∑ j : Fin m, c j * (μ' j) ^ ((r : ℕ) + 1) * (c j * (μ' j) ^ (s : ℕ))) =
              ∑ j : Fin m, w j * (μ' j) ^ ((r : ℕ) + (s : ℕ) + 1) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hc2 j, pow_add, pow_add, pow_one]
            ring
          rw [h2]
          exact lagrange_moment_zero (by omega : 2 ≤ m) μ' hμ'_inj ((r : ℕ) + (s : ℕ) + 1)
            (by have := r.isLt; have := s.isLt; omega)
        have hli : LinearIndependent ℂ u := by
          rw [Fintype.linearIndependent_iff]
          intro α hα
          let P : ℂ[X] := ∑ r : Fin (k + 1), C (α r) * X ^ (r : ℕ)
          have hPeval : ∀ j : Fin m, P.eval (μ' j) = 0 := by
            intro j
            have h0 := congrArg (form (e (emb j))) hα
            simp only [map_sum, map_smul, map_zero, smul_eq_mul, hform_eu] at h0
            have h2 : (∑ r : Fin (k + 1), α r * (c j * (μ' j) ^ (r : ℕ))) =
                c j * P.eval (μ' j) := by
              simp only [P, eval_finset_sum', eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
              refine Finset.sum_congr rfl fun r _ => by ring
            rw [h2] at h0
            exact (mul_eq_zero.mp h0).resolve_left (hc_ne j)
          have hPdeg : P.natDegree ≤ k := by
            refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
            rw [Finset.fold_max_le]
            refine ⟨by omega, fun r _ => ?_⟩
            exact le_trans (Polynomial.natDegree_C_mul_le _ _)
              (le_trans (Polynomial.natDegree_X_pow_le _) (by have := r.isLt; omega))
          have hPzero : P = 0 := by
            by_contra hne
            have hsub : Finset.univ.image μ' ⊆ P.roots.toFinset := by
              intro z hz
              obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
              rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
              exact hPeval j
            have hcard : m ≤ P.natDegree := calc
              m = (Finset.univ.image μ').card := by
                rw [Finset.card_image_of_injective _ hμ'_inj, Finset.card_univ, Fintype.card_fin]
              _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
              _ ≤ P.roots.card := Multiset.toFinset_card_le _
              _ ≤ P.natDegree := Polynomial.card_roots' P
            omega
          intro r
          have hcoeff := congrArg (fun Q : ℂ[X] => Q.coeff (r : ℕ)) hPzero
          simp only [P, coeff_finset_sum', coeff_C_mul, coeff_X_pow, coeff_zero] at hcoeff
          rw [Finset.sum_eq_single r] at hcoeff
          · simpa using hcoeff
          · intro s _ hne
            rw [if_neg (by intro heq; exact hne (Fin.ext heq.symm)), mul_zero]
          · intro h; exact absurd (mem_univ r) h
        let K := Submodule.span ℂ (Set.range u)
        refine ⟨K, ?_, ?_, ?_⟩
        · rw [finrank_span_eq_card hli, Fintype.card_fin]
        · intro x hx y hy
          obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
          obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hy
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            hform_u, mul_zero, Finset.sum_const_zero]
        · intro x hx
          obtain ⟨α, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
          simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
            hform_Tu, mul_zero, Finset.sum_const_zero]

private noncomputable def dotFormQ (q : ℕ) : LinearMap.BilinForm ℂ (Fin q → ℂ) :=
  dotProductBilin ℂ ℂ

private noncomputable def columnSumQ (q : ℕ) : (Fin q → ℂ) →ₗ[ℂ] ℂ :=
  dotFormQ q (fun _ => 1)

private noncomputable abbrev CenterQ (q : ℕ) := (columnSumQ q).ker

private lemma mem_centerQ {q : ℕ} (v : Fin q → ℂ) : v ∈ CenterQ q ↔ (∑ j, v j) = 0 := by
  change (∑ j, (1 : ℂ) * v j) = 0 ↔ _
  simp

private lemma centerQ_finrank {q : ℕ} (hq : 4 ≤ q) : finrank ℂ (CenterQ q) = q - 1 := by
  have hsurj : Function.Surjective (columnSumQ q) := by
    intro c
    let i0 : Fin q := ⟨0, by omega⟩
    refine ⟨Pi.single i0 c, ?_⟩
    change (∑ j : Fin q, (1 : ℂ) * (Pi.single i0 c : Fin q → ℂ) j) = c
    simp [Pi.single_apply]
  have hr := LinearMap.finrank_range_add_finrank_ker (columnSumQ q)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hr
  dsimp only [CenterQ]
  omega

private noncomputable def centerFormQ (q : ℕ) : LinearMap.BilinForm ℂ (CenterQ q) :=
  (dotFormQ q).restrict (CenterQ q)

private lemma centerFormQ_apply {q : ℕ} (x y : CenterQ q) :
    centerFormQ q x y = ∑ j, (x : Fin q → ℂ) j * (y : Fin q → ℂ) j := rfl

private lemma centerFormQ_symm (q : ℕ) : (centerFormQ q).IsSymm :=
  ⟨fun x y => by simp only [centerFormQ_apply, mul_comm]⟩

private lemma centerFormQ_nondeg {q : ℕ} (hq : 4 ≤ q) : (centerFormQ q).Nondegenerate :=
  (centerFormQ_symm q).isRefl.nondegenerate_iff_separatingLeft.mpr (by
    intro v hv
    let i0 : Fin q := ⟨0, by omega⟩
    have heq : ∀ j : Fin q, (v : Fin q → ℂ) j = (v : Fin q → ℂ) i0 := by
      intro j
      let u : Fin q → ℂ := Pi.single j 1 - Pi.single i0 1
      have hu : u ∈ CenterQ q := by
        rw [mem_centerQ]
        simp [u, Finset.sum_sub_distrib, Pi.single_apply]
      have h0 := hv ⟨u, hu⟩
      rw [centerFormQ_apply] at h0
      have hcalc : (∑ l : Fin q, (v : Fin q → ℂ) l * u l) =
          (v : Fin q → ℂ) j - (v : Fin q → ℂ) i0 := by
        simp [u, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
      rw [hcalc] at h0
      exact sub_eq_zero.mp h0
    have hsum : (∑ j : Fin q, (v : Fin q → ℂ) j) = 0 := (mem_centerQ _).mp v.property
    simp_rw [heq] at hsum
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hvi0 : (v : Fin q → ℂ) i0 = 0 := (mul_eq_zero.mp hsum).resolve_left hqne
    apply Subtype.ext
    funext j
    exact (heq j).trans hvi0)

private lemma main_296 :
    ∀ (q : ℕ), 4 ≤ q → ∀ (y : Fin q → ℂ),
      (∑ j, y j) = 0 → (∑ j, (y j) ^ 2) = 0 →
      let P : Matrix (Fin q) (Fin q) ℂ :=
        fun i j => (if i = j then 1 else 0) - 1 / (q : ℂ)
      let A : Matrix (Fin q) (Fin q) ℂ :=
        fun i j => (if i = j then (y i) ^ 2 else 0) - y i * y j / 3
      ∀ k : ℕ,
        (∃ K : Submodule ℂ (Fin q → ℂ), Module.finrank ℂ K = k ∧
          ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ,
            let rows : Fin 4 → Fin q → ℂ := ![x, -x, t • y, -(t • y)]
            (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
              (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) ↔
          2 * k + 2 ≤ q ∨ (2 * k + 1 = q ∧
            ∃ f : Polynomial ℂ, (P * A * P).charpoly = Polynomial.X * f ^ 2) := by
  intro q hq y hy hy2 P A k
  have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hP_apply : ∀ (v : Fin q → ℂ) (i : Fin q),
      P.mulVecLin v i = v i - (∑ j, v j) / (q : ℂ) := by
    intro v i
    change (∑ j : Fin q, ((if i = j then (1 : ℂ) else 0) - 1 / (q : ℂ)) * v j) = _
    simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, mem_univ, ite_true, ← Finset.mul_sum]
    ring
  have hP_mem : ∀ v : Fin q → ℂ, P.mulVecLin v ∈ CenterQ q := by
    intro v
    rw [mem_centerQ]
    simp_rw [hP_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hqne]
    ring
  have hP_center : ∀ v : CenterQ q, P.mulVecLin (v : Fin q → ℂ) = v := by
    intro v
    ext i
    rw [hP_apply, (mem_centerQ _).mp v.property, zero_div, sub_zero]
  have hA_apply : ∀ (v : Fin q → ℂ) (i : Fin q),
      A.mulVecLin v i = (y i) ^ 2 * v i - y i * (∑ j, y j * v j) / 3 := by
    intro v i
    change (∑ j : Fin q, ((if i = j then (y i) ^ 2 else 0) - y i * y j / 3) * v j) = _
    simp_rw [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, mem_univ, ite_true]
    have h2 : (∑ j : Fin q, y i * y j / 3 * v j) = y i * (∑ j : Fin q, y j * v j) / 3 := by
      have hpt : ∀ j : Fin q, y i * y j / 3 * v j = (y i / 3) * (y j * v j) := fun _ => by ring
      simp_rw [hpt, ← Finset.mul_sum]
      ring
    rw [h2]
  let Tfull : Module.End ℂ (Fin q → ℂ) := (P * A * P).mulVecLin
  have hTfull_apply : ∀ v : Fin q → ℂ, Tfull v = P.mulVecLin (A.mulVecLin (P.mulVecLin v)) := by
    intro v
    simp only [Tfull, Matrix.mulVecLin_mul, LinearMap.comp_apply]
  have hCenter_stab : CenterQ q ≤ (CenterQ q).comap Tfull := fun v _ => by
    change Tfull v ∈ CenterQ q
    rw [hTfull_apply]
    exact hP_mem _
  let Top : Module.End ℂ (CenterQ q) := Tfull.restrict hCenter_stab
  have hTop_form : ∀ u v : CenterQ q,
      centerFormQ q (Top u) v =
        (∑ j, (y j) ^ 2 * (u : Fin q → ℂ) j * (v : Fin q → ℂ) j) -
        (∑ j, y j * (u : Fin q → ℂ) j) * (∑ j, y j * (v : Fin q → ℂ) j) / 3 := by
    intro u v
    rw [centerFormQ_apply]
    have hval : ∀ i : Fin q, (Top u : Fin q → ℂ) i =
        A.mulVecLin (u : Fin q → ℂ) i - (∑ j, A.mulVecLin (u : Fin q → ℂ) j) / (q : ℂ) := by
      intro i
      change Tfull (u : Fin q → ℂ) i = _
      rw [hTfull_apply, hP_center u, hP_apply]
    simp_rw [hval, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
      (mem_centerQ _).mp v.property, mul_zero, sub_zero, hA_apply]
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    have h2 : (∑ i : Fin q, y i * (∑ j : Fin q, y j * (u : Fin q → ℂ) j) / 3 * (v : Fin q → ℂ) i) =
        (∑ j : Fin q, y j * (u : Fin q → ℂ) j) * (∑ i : Fin q, y i * (v : Fin q → ℂ) i) / 3 := by
      have hpt : ∀ i : Fin q,
          y i * (∑ j : Fin q, y j * (u : Fin q → ℂ) j) / 3 * (v : Fin q → ℂ) i =
          ((∑ j : Fin q, y j * (u : Fin q → ℂ) j) / 3) * (y i * (v : Fin q → ℂ) i) := fun _ => by ring
      simp_rw [hpt, ← Finset.mul_sum]
      ring
    rw [h2]
  have hTop_adj : ∀ u v : CenterQ q, centerFormQ q (Top u) v = centerFormQ q u (Top v) := by
    intro u v
    rw [(centerFormQ_symm q).eq u (Top v), hTop_form, hTop_form]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have hchar_rel : (P * A * P).charpoly = Polynomial.X * Top.charpoly := by
    rw [← Matrix.charpoly_mulVecLin (P * A * P)]
    change Tfull.charpoly = Polynomial.X * Top.charpoly
    rw [charpoly_factor Tfull (CenterQ q) hCenter_stab]
    have hqdim : finrank ℂ ((Fin q → ℂ) ⧸ CenterQ q) = 1 := by
      have hd := (CenterQ q).finrank_quotient_add_finrank
      rw [centerQ_finrank hq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
      omega
    have hqzero : (CenterQ q).mapQ (CenterQ q) Tfull hCenter_stab =
        algebraMap ℂ (Module.End ℂ ((Fin q → ℂ) ⧸ CenterQ q)) 0 := by
      apply LinearMap.ext
      intro z
      obtain ⟨v, rfl⟩ := (CenterQ q).mkQ_surjective z
      rw [map_zero, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero (CenterQ q)).mpr (by rw [hTfull_apply]; exact hP_mem _)
    rw [hqzero, scalar_charpoly, hqdim, pow_one, map_zero, sub_zero, mul_comm]
  have hlevel_iff : ∀ u : CenterQ q,
      (∀ t : ℂ, let rows : Fin 4 → Fin q → ℂ := ![(u : Fin q → ℂ), -(u : Fin q → ℂ), t • y, -(t • y)]
        (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
          (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) ↔
        centerFormQ q u u = 0 ∧ centerFormQ q (Top u) u = 0 := by
    intro u
    rw [permanent_iff_q hq _ y ((mem_centerQ _).mp u.property) hy hy2, centerFormQ_apply, hTop_form]
    have h1 : (∑ j, (u : Fin q → ℂ) j * (u : Fin q → ℂ) j) = ∑ j, ((u : Fin q → ℂ) j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => by ring
    have h2 : (∑ j, (y j) ^ 2 * (u : Fin q → ℂ) j * (u : Fin q → ℂ) j) =
        ∑ j, ((u : Fin q → ℂ) j) ^ 2 * (y j) ^ 2 :=
      Finset.sum_congr rfl fun j _ => by ring
    have h3 : (∑ j, y j * (u : Fin q → ℂ) j) = ∑ j, (u : Fin q → ℂ) j * y j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [h1, h2, h3]
    constructor
    · rintro ⟨ha, hb⟩; exact ⟨ha, by linear_combination hb / 3⟩
    · rintro ⟨ha, hb⟩; exact ⟨ha, by linear_combination 3 * hb⟩
  constructor
  · rintro ⟨K, hKrank, hK⟩
    have hKsub : K ≤ CenterQ q := fun x hx => (mem_centerQ x).mpr (hK x hx).1
    let K' := K.comap (CenterQ q).subtype
    have hK'rank : finrank ℂ K' = k :=
      (Submodule.comapSubtypeEquivOfLe hKsub).finrank_eq.trans hKrank
    have hK'lev : ∀ u ∈ K', centerFormQ q u u = 0 ∧ centerFormQ q (Top u) u = 0 := fun u hu =>
      (hlevel_iff u).mp (hK u hu).2
    have hK'iso : K' ≤ (centerFormQ q).orthogonal K' := by
      intro u hu v hv
      have hsum := (hK'lev (v + u) (K'.add_mem hv hu)).1
      simp only [map_add, LinearMap.add_apply, (centerFormQ_symm q).eq u v] at hsum
      linear_combination (hsum - (hK'lev v hv).1 - (hK'lev u hu).1) / 2
    have hdim_le : 2 * k + 1 ≤ q := by
      have hle1 : finrank ℂ K' ≤ finrank ℂ ((centerFormQ q).orthogonal K') :=
        Submodule.finrank_mono hK'iso
      rw [(centerFormQ q).finrank_orthogonal (centerFormQ_nondeg hq), centerQ_finrank hq,
        hK'rank] at hle1
      omega
    by_cases hlt : 2 * k + 2 ≤ q
    · exact Or.inl hlt
    · right
      have heq : 2 * k + 1 = q := by omega
      refine ⟨heq, ?_⟩
      have hCdim : finrank ℂ (CenterQ q) = 2 * k := by rw [centerQ_finrank hq]; omega
      have hself : (centerFormQ q).orthogonal K' = K' := by
        symm
        apply Submodule.eq_of_le_of_finrank_le hK'iso
        rw [(centerFormQ q).finrank_orthogonal (centerFormQ_nondeg hq), hCdim, hK'rank]
        omega
      have hK'stab : K' ≤ K'.comap Top := by
        intro u hu
        change Top u ∈ K'
        rw [← hself]
        intro v hv
        have hsum := (hK'lev (v + u) (K'.add_mem hv hu)).2
        have hsym : centerFormQ q (Top u) v = centerFormQ q (Top v) u :=
          ((centerFormQ_symm q).eq _ _).trans (hTop_adj v u).symm
        simp only [map_add, LinearMap.add_apply, hsym] at hsum
        rw [← hTop_adj]
        linear_combination (hsum - (hK'lev v hv).2 - (hK'lev u hu).2) / 2
      obtain ⟨f, hf⟩ := square_of_half_isotropic hCdim (centerFormQ q) (centerFormQ_symm q)
        (centerFormQ_nondeg hq) Top hTop_adj K' hK'rank hK'iso hK'stab
      exact ⟨f, by rw [hchar_rel, hf]⟩
  · rintro (hlt | ⟨heq, f, hf⟩)
    · have hdim : 2 * k + 1 ≤ finrank ℂ (CenterQ q) := by rw [centerQ_finrank hq]; omega
      obtain ⟨K', hK'rank, hK'iso, hK'op⟩ :=
        sim_isotropic_of_lt k hdim (centerFormQ q) (centerFormQ_symm q) (centerFormQ_nondeg hq)
          Top hTop_adj
      refine ⟨K'.map (CenterQ q).subtype, (Submodule.finrank_map_subtype_eq _ _).trans hK'rank, ?_⟩
      rintro x ⟨u, hu, rfl⟩
      exact ⟨(mem_centerQ _).mp u.property,
        (hlevel_iff u).mpr ⟨hK'iso hu u hu, hK'op u hu⟩⟩
    · have hCdim : finrank ℂ (CenterQ q) = 2 * k := by rw [centerQ_finrank hq]; omega
      have hsq : Top.charpoly = f ^ 2 := by
        rw [hchar_rel] at hf
        exact mul_left_cancel₀ Polynomial.X_ne_zero hf
      obtain ⟨K', hK'rank, hK'iso, hK'stab⟩ :=
        half_isotropic_of_square k hCdim (centerFormQ q) (centerFormQ_symm q)
          (centerFormQ_nondeg hq) Top hTop_adj hsq
      refine ⟨K'.map (CenterQ q).subtype, (Submodule.finrank_map_subtype_eq _ _).trans hK'rank, ?_⟩
      rintro x ⟨u, hu, rfl⟩
      exact ⟨(mem_centerQ _).mp u.property,
        (hlevel_iff u).mpr ⟨hK'iso hu u hu, hK'iso hu (Top u) (hK'stab hu)⟩⟩

end PEqualNP.Outside.L_gct_296_aux

theorem PEqualNP.Outside.L_gct_296 : ∀ (q : ℕ), 4 ≤ q → ∀ (y : Fin q → ℂ),
  (∑ j, y j) = 0 → (∑ j, (y j)^2) = 0 →
  let P : Matrix (Fin q) (Fin q) ℂ :=
    fun i j => (if i = j then 1 else 0) - 1 / (q : ℂ)
  let A : Matrix (Fin q) (Fin q) ℂ :=
    fun i j => (if i = j then (y i)^2 else 0) - y i * y j / 3
  ∀ k : ℕ,
    (∃ K : Submodule ℂ (Fin q → ℂ), Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ,
        let rows : Fin 4 → Fin q → ℂ := ![x, -x, t • y, -(t • y)]
        (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
          (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) ↔
      2*k + 2 ≤ q ∨ (2*k + 1 = q ∧
        ∃ f : Polynomial ℂ, (P * A * P).charpoly = Polynomial.X * f^2) :=
  PEqualNP.Outside.L_gct_296_aux.main_296
