import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_297

lemma sum_emb4 {q : ℕ} (F : Fin q → Fin q → Fin q → Fin q → ℂ) :
    (∑ f : Fin 4 ↪ Fin q, F (f 0) (f 1) (f 2) (f 3)) =
      ∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        ∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
          ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c, F a b c d := by
  let S : Finset (Fin q × Fin q × Fin q × Fin q) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2.1 ∧ p.1 ≠ p.2.2.2 ∧
      p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2)
  have h1 : (∑ f : Fin 4 ↪ Fin q, F (f 0) (f 1) (f 2) (f 3)) =
      ∑ p ∈ S, F p.1 p.2.1 p.2.2.1 p.2.2.2 := by
    refine Finset.sum_bij (fun f _ => (f 0, f 1, f 2, f 3)) ?_ ?_ ?_ ?_
    · intro f _
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => by have := f.injective h; omega,
        fun h => by have := f.injective h; omega,
        fun h => by have := f.injective h; omega,
        fun h => by have := f.injective h; omega,
        fun h => by have := f.injective h; omega,
        fun h => by have := f.injective h; omega⟩
    · intro f1 _ f2 _ h
      ext i
      have h0 : f1 0 = f2 0 := congrArg Prod.fst h
      have h1' : f1 1 = f2 1 := congrArg (fun p => p.2.1) h
      have h2 : f1 2 = f2 2 := congrArg (fun p => p.2.2.1) h
      have h3 : f1 3 = f2 3 := congrArg (fun p => p.2.2.2) h
      fin_cases i <;> simp_all
    · intro ⟨a, b, c, d⟩ hp
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      refine ⟨⟨![a, b, c, d], fun i j hij => ?_⟩, Finset.mem_univ _, rfl⟩
      fin_cases i <;> fin_cases j <;> simp_all
    · intro _ _; rfl
  rw [h1]
  have h2 : (∑ p ∈ S, F p.1 p.2.1 p.2.2.1 p.2.2.2) =
      ∑ a : Fin q, ∑ b : Fin q, ∑ c : Fin q, ∑ d : Fin q,
        if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F a b c d else 0 := by
    rw [Finset.sum_filter]
    simp only [Fintype.sum_prod_type]
  rw [h2]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hf1 : Finset.univ.filter (fun b : Fin q => b ≠ a) = Finset.univ.erase a := by ext x; simp
  calc ∑ b : Fin q, ∑ c : Fin q, ∑ d : Fin q,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F a b c d else 0)
      = ∑ b ∈ Finset.univ.erase a, ∑ c : Fin q, ∑ d : Fin q,
          (if a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then F a b c d else 0) := by
        rw [← hf1, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hab : b = a
        · subst hab; simp
        · simp [hab, Ne.symm hab]
    _ = ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b, ∑ d : Fin q,
          (if a ≠ d ∧ b ≠ d ∧ c ≠ d then F a b c d else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        have hf2 : Finset.univ.filter (fun c : Fin q => a ≠ c ∧ b ≠ c) = (Finset.univ.erase a).erase b := by
          ext x; simp [ne_comm, and_comm]
        rw [← hf2, Finset.sum_filter]
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases hca : a ≠ c ∧ b ≠ c
        · simp [hca.1, hca.2]
        · rw [if_neg hca]
          apply Finset.sum_eq_zero; intro d _
          rw [if_neg]; intro h; exact hca ⟨h.1, h.2.2.1⟩
    _ = ∑ b ∈ Finset.univ.erase a, ∑ c ∈ (Finset.univ.erase a).erase b,
          ∑ d ∈ ((Finset.univ.erase a).erase b).erase c, F a b c d := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        have hf3 : Finset.univ.filter (fun d : Fin q => a ≠ d ∧ b ≠ d ∧ c ≠ d) =
            ((Finset.univ.erase a).erase b).erase c := by
          ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_comm]; tauto
        rw [← hf3, Finset.sum_filter]

lemma card_emb4_cast {q : ℕ} (hq : 5 ≤ q) :
    (Fintype.card (Fin 4 ↪ Fin q) : ℂ) = (q : ℂ) * ((q : ℂ) - 1) * ((q : ℂ) - 2) * ((q : ℂ) - 3) := by
  have h1 : Fintype.card (Fin 4 ↪ Fin q) = q * (q - 1) * (q - 2) * (q - 3) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin, Nat.descFactorial_succ,
      Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_zero]
    simp only [Nat.sub_zero]; ring
  rw [h1]
  have hq1 : (1 : ℕ) ≤ q := by omega
  have hq2 : (2 : ℕ) ≤ q := by omega
  have hq3 : (3 : ℕ) ≤ q := by omega
  push_cast [Nat.cast_sub hq1, Nat.cast_sub hq2, Nat.cast_sub hq3]
  ring

lemma sum_erase_zero {q : ℕ} (v : Fin q → ℂ) (hv : ∑ j : Fin q, v j = 0) (a : Fin q) :
    ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a, v b = -v a := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ a), hv, zero_sub]

lemma sum_erase2_zero {q : ℕ} (v : Fin q → ℂ) (hv : ∑ j : Fin q, v j = 0) {a b : Fin q} (hba : b ≠ a) :
    ∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b, v c = -(v a + v b) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_erase.2 ⟨hba, Finset.mem_univ b⟩), sum_erase_zero v hv a]
  ring

lemma sum_erase3_zero {q : ℕ} (v : Fin q → ℂ) (hv : ∑ j : Fin q, v j = 0)
    {a b c : Fin q} (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c, v d = -(v a + v b + v c) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_erase.2 ⟨hcb, Finset.mem_erase.2 ⟨hca, Finset.mem_univ c⟩⟩),
    sum_erase2_zero v hv hba]
  ring

lemma card_erase1 {q : ℕ} (a : Fin q) :
    (((Finset.univ : Finset (Fin q)).erase a).card : ℂ) = (q : ℂ) - 1 := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (Fin.pos a).ne'
  rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_fin, Nat.cast_sub hq]; simp

lemma card_erase2 {q : ℕ} (hq : 2 ≤ q) {a b : Fin q} (hba : b ≠ a) :
    ((((Finset.univ : Finset (Fin q)).erase a).erase b).card : ℂ) = (q : ℂ) - 2 := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hba, Finset.mem_univ b⟩),
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_fin]
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q - 1 := by omega
  rw [Nat.cast_sub h2, Nat.cast_sub h1]; push_cast; ring

lemma card_erase3 {q : ℕ} (hq : 3 ≤ q) {a b c : Fin q} (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    (((((Finset.univ : Finset (Fin q)).erase a).erase b).erase c).card : ℂ) = (q : ℂ) - 3 := by
  rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hcb, Finset.mem_erase.2 ⟨hca, Finset.mem_univ c⟩⟩),
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hba, Finset.mem_univ b⟩),
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_fin]
  have h1 : 1 ≤ q := by omega
  have h2 : 1 ≤ q - 1 := by omega
  have h3 : 1 ≤ q - 1 - 1 := by omega
  rw [Nat.cast_sub h3, Nat.cast_sub h2, Nat.cast_sub h1]; push_cast; ring

noncomputable def permSum {q : ℕ} (x y : Fin q → ℂ) (t : ℂ) : ℂ :=
  ∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4,
    (1 + (![x, -x, t • y, -(t • y)] : Fin 4 → Fin q → ℂ) i (f i))

lemma permSum_expand {q : ℕ} (x y : Fin q → ℂ) (t : ℂ) :
    permSum x y t =
      ∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        ∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
          ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c,
            (1 + x a) * (1 - x b) * (1 + t * y c) * (1 - t * y d) := by
  unfold permSum
  have h1 : (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4,
      (1 + (![x, -x, t • y, -(t • y)] : Fin 4 → Fin q → ℂ) i (f i))) =
      ∑ f : Fin 4 ↪ Fin q, (1 + x (f 0)) * (1 - x (f 1)) * (1 + t * y (f 2)) * (1 - t * y (f 3)) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    simp [Fin.prod_univ_four, sub_eq_add_neg, mul_assoc]
  rw [h1, sum_emb4 (fun a b c d => (1 + x a) * (1 - x b) * (1 + t * y c) * (1 - t * y d))]

lemma permSum_at_zero {q : ℕ} (hq : 5 ≤ q) {x y : Fin q → ℂ} (hx : ∑ j, x j = 0) :
    permSum x y 0 = (Fintype.card (Fin 4 ↪ Fin q) : ℂ) +
      ((q : ℂ) - 2) * ((q : ℂ) - 3) * (∑ j, (x j) ^ 2) := by
  rw [permSum_expand, card_emb4_cast hq]
  have hstep : ∀ a : Fin q, ∀ b ∈ (Finset.univ : Finset (Fin q)).erase a,
      (∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
        ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c,
          (1 + x a) * (1 - x b) * (1 + 0 * y c) * (1 - 0 * y d)) =
      ((q : ℂ) - 2) * ((q : ℂ) - 3) * ((1 + x a) * (1 - x b)) := by
    intro a b hb
    have hba : b ≠ a := (Finset.mem_erase.1 hb).1
    have hc : ∀ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
        (∑ _d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c,
          (1 + x a) * (1 - x b) * (1 + 0 * y c) * (1 - 0 * y _d)) =
        ((q : ℂ) - 3) * ((1 + x a) * (1 - x b)) := by
      intro c hc
      have hcb : c ≠ b := (Finset.mem_erase.1 hc).1
      have hca : c ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
      simp only [zero_mul, add_zero, sub_zero, mul_one, Finset.sum_const, nsmul_eq_mul,
        card_erase3 (by omega) hba hca hcb]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, card_erase2 (by omega) hba]
    ring
  calc (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        ∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
          ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c,
            (1 + x a) * (1 - x b) * (1 + 0 * y c) * (1 - 0 * y d))
      = ∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
          ((q : ℂ) - 2) * ((q : ℂ) - 3) * ((1 + x a) * (1 - x b)) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => hstep a b hb
    _ = ((q : ℂ) - 2) * ((q : ℂ) - 3) * ∑ a : Fin q, (1 + x a) * ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a, (1 - x b) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = ((q : ℂ) - 2) * ((q : ℂ) - 3) * ∑ a : Fin q, (1 + x a) * (((q : ℂ) - 1) + x a) := by
        congr 1; refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, card_erase1 a, sum_erase_zero x hx a]
        ring
    _ = (q : ℂ) * ((q : ℂ) - 1) * ((q : ℂ) - 2) * ((q : ℂ) - 3) +
          ((q : ℂ) - 2) * ((q : ℂ) - 3) * ∑ j : Fin q, (x j) ^ 2 := by
        have hsum : ∑ a : Fin q, (1 + x a) * (((q : ℂ) - 1) + x a) =
            (q : ℂ) * ((q : ℂ) - 1) + ∑ a : Fin q, (x a) ^ 2 := by
          have hex : ∀ a : Fin q, (1 + x a) * (((q : ℂ) - 1) + x a) =
              ((q : ℂ) - 1) + (q : ℂ) * x a + (x a) ^ 2 := fun a => by ring
          simp_rw [hex, Finset.sum_add_distrib, ← Finset.mul_sum, hx, mul_zero, add_zero,
            Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        rw [hsum]; ring

lemma permSum_iso {q : ℕ} (hq : 5 ≤ q) {x y : Fin q → ℂ}
    (hx : ∑ j, x j = 0) (hx2 : ∑ j, (x j) ^ 2 = 0)
    (hy : ∑ j, y j = 0) (hy2 : ∑ j, (y j) ^ 2 = 0) (t : ℂ) :
    permSum x y t = (Fintype.card (Fin 4 ↪ Fin q) : ℂ) +
      t ^ 2 * (2 * (∑ j, x j * y j) ^ 2 - 6 * (∑ j, (x j) ^ 2 * (y j) ^ 2)) := by
  rw [permSum_expand, card_emb4_cast hq]
  have hinner : ∀ a : Fin q, ∀ b ∈ (Finset.univ : Finset (Fin q)).erase a,
      (∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
        ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c,
          (1 + t * y c) * (1 - t * y d)) =
      ((q : ℂ) - 2) * ((q : ℂ) - 3) - 2 * t ^ 2 * ((y a) ^ 2 + y a * y b + (y b) ^ 2) := by
    intro a b hb
    have hba : b ≠ a := (Finset.mem_erase.1 hb).1
    have hd : ∀ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
        (∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c, (1 + t * y c) * (1 - t * y d)) =
        (1 + t * y c) * (((q : ℂ) - 3) + t * (y a + y b + y c)) := by
      intro c hc
      have hcb : c ≠ b := (Finset.mem_erase.1 hc).1
      have hca : c ≠ a := (Finset.mem_erase.1 (Finset.mem_erase.1 hc).2).1
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
        card_erase3 (by omega) hba hca hcb, ← Finset.mul_sum, sum_erase3_zero y hy hba hca hcb]
      ring
    rw [Finset.sum_congr rfl hd]
    have hex : ∀ c : Fin q, (1 + t * y c) * (((q : ℂ) - 3) + t * (y a + y b + y c)) =
        (((q : ℂ) - 3) + t * (y a + y b)) + (t * ((q : ℂ) - 2) + t ^ 2 * (y a + y b)) * y c + t ^ 2 * (y c) ^ 2 :=
      fun c => by ring
    simp_rw [hex, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      card_erase2 (by omega) hba, sum_erase2_zero y hy hba, sum_erase2_zero (fun j => (y j) ^ 2) hy2 hba]
    ring
  have h1 : (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
      ∑ c ∈ ((Finset.univ : Finset (Fin q)).erase a).erase b,
        ∑ d ∈ (((Finset.univ : Finset (Fin q)).erase a).erase b).erase c,
          (1 + x a) * (1 - x b) * (1 + t * y c) * (1 - t * y d)) =
      ∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        (1 + x a) * (1 - x b) * (((q : ℂ) - 2) * ((q : ℂ) - 3) - 2 * t ^ 2 * ((y a) ^ 2 + y a * y b + (y b) ^ 2)) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
    rw [← hinner a b hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => by ring
  rw [h1]
  have hsplit : ∀ a b : Fin q,
      (1 + x a) * (1 - x b) * (((q : ℂ) - 2) * ((q : ℂ) - 3) - 2 * t ^ 2 * ((y a) ^ 2 + y a * y b + (y b) ^ 2)) =
      ((q : ℂ) - 2) * ((q : ℂ) - 3) * ((1 + x a) * (1 - x b)) -
      2 * t ^ 2 * ((1 + x a) * (1 - x b) * ((y a) ^ 2 + y a * y b + (y b) ^ 2)) := fun _ _ => by ring
  simp_rw [hsplit, Finset.sum_sub_distrib]
  have hconst : (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
      ((q : ℂ) - 2) * ((q : ℂ) - 3) * ((1 + x a) * (1 - x b))) =
      (q : ℂ) * ((q : ℂ) - 1) * ((q : ℂ) - 2) * ((q : ℂ) - 3) := by
    have hpull : (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        ((q : ℂ) - 2) * ((q : ℂ) - 3) * ((1 + x a) * (1 - x b))) =
        ((q : ℂ) - 2) * ((q : ℂ) - 3) * ∑ a : Fin q, (1 + x a) * ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a, (1 - x b) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hpull]
    have hb : ∀ a : Fin q, (1 + x a) * ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a, (1 - x b) =
        ((q : ℂ) - 1) + (q : ℂ) * x a + (x a) ^ 2 := by
      intro a
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, card_erase1 a, sum_erase_zero x hx a]
      ring
    simp_rw [hb, Finset.sum_add_distrib, ← Finset.mul_sum, hx, hx2, mul_zero, add_zero,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  have hquad : (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
      (1 + x a) * (1 - x b) * ((y a) ^ 2 + y a * y b + (y b) ^ 2)) =
      3 * (∑ j : Fin q, (x j) ^ 2 * (y j) ^ 2) - (∑ j : Fin q, x j * y j) ^ 2 := by
    have hterm : ∀ a : Fin q, (∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        (1 + x a) * (1 - x b) * ((y a) ^ 2 + y a * y b + (y b) ^ 2)) =
        (1 + x a) * (((q : ℂ) - 3) * (y a) ^ 2 + (x a * (y a) ^ 2 - y a * (∑ j, x j * y j) + x a * (y a) ^ 2 - (∑ j, x j * (y j) ^ 2) + x a * (y a) ^ 2)) := by
      intro a
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      have hex : ∀ b : Fin q, (1 - x b) * ((y a) ^ 2 + y a * y b + (y b) ^ 2) =
          ((y a) ^ 2 + y a * y b + (y b) ^ 2) - ((y a) ^ 2 * x b + y a * (x b * y b) + x b * (y b) ^ 2) :=
        fun b => by ring
      simp_rw [hex, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, card_erase1 a,
        sum_erase_zero y hy a, sum_erase_zero (fun j => (y j) ^ 2) hy2 a, sum_erase_zero x hx a,
        Finset.sum_erase_eq_sub (Finset.mem_univ a)]
      ring
    simp_rw [hterm]
    have hex2 : ∀ a : Fin q,
        (1 + x a) * (((q : ℂ) - 3) * (y a) ^ 2 + (x a * (y a) ^ 2 - y a * (∑ j, x j * y j) + x a * (y a) ^ 2 - (∑ j, x j * (y j) ^ 2) + x a * (y a) ^ 2)) =
        ((q : ℂ) - 3) * (y a) ^ 2 + ((q : ℂ) - 3) * (x a * (y a) ^ 2) + 3 * (x a * (y a) ^ 2) + 3 * ((x a) ^ 2 * (y a) ^ 2) -
        (∑ j, x j * y j) * y a - (∑ j, x j * y j) * (x a * y a) - (∑ j, x j * (y j) ^ 2) - (∑ j, x j * (y j) ^ 2) * x a :=
      fun a => by ring
    simp_rw [hex2, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      hy, hy2, hx, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  rw [hconst]
  have hpull2 : (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
      2 * t ^ 2 * ((1 + x a) * (1 - x b) * ((y a) ^ 2 + y a * y b + (y b) ^ 2))) =
      2 * t ^ 2 * (∑ a : Fin q, ∑ b ∈ (Finset.univ : Finset (Fin q)).erase a,
        (1 + x a) * (1 - x b) * ((y a) ^ 2 + y a * y b + (y b) ^ 2)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  rw [hpull2, hquad]
  ring

lemma permSum_iff {q : ℕ} (hq : 5 ≤ q) {x y : Fin q → ℂ}
    (hx : ∑ j, x j = 0) (hy : ∑ j, y j = 0) (hy2 : ∑ j, (y j) ^ 2 = 0) :
    (∀ t : ℂ, permSum x y t = (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) ↔
      (∑ j, (x j) ^ 2 = 0 ∧ (∑ j, (x j) ^ 2 * (y j) ^ 2) - (1 / 3 : ℂ) * (∑ j, x j * y j) ^ 2 = 0) := by
  constructor
  · intro h
    have h0 := h 0
    rw [permSum_at_zero hq hx] at h0
    have hq2 : ((q : ℂ) - 2) ≠ 0 := by
      have : (2 : ℂ) ≠ (q : ℂ) := by exact_mod_cast (by omega : 2 ≠ q)
      exact sub_ne_zero.2 this.symm
    have hq3 : ((q : ℂ) - 3) ≠ 0 := by
      have : (3 : ℂ) ≠ (q : ℂ) := by exact_mod_cast (by omega : 3 ≠ q)
      exact sub_ne_zero.2 this.symm
    have hx2 : ∑ j, (x j) ^ 2 = 0 := by
      have hmul : ((q : ℂ) - 2) * ((q : ℂ) - 3) * (∑ j, (x j) ^ 2) = 0 := by linear_combination h0
      exact (mul_eq_zero.1 hmul).resolve_left (mul_ne_zero hq2 hq3)
    refine ⟨hx2, ?_⟩
    have h1 := h 1
    rw [permSum_iso hq hx hx2 hy hy2 1] at h1
    linear_combination -h1 / 6
  · rintro ⟨hx2, hB⟩ t
    rw [permSum_iso hq hx hx2 hy hy2 t]
    linear_combination -6 * t ^ 2 * hB

def H0 (q : ℕ) : Submodule ℂ (Fin q → ℂ) :=
  { carrier := {x | ∑ j : Fin q, x j = 0}, add_mem' := fun {x y} hx hy => by
      show ∑ j : Fin q, (x j + y j) = 0
      rw [Finset.sum_add_distrib, hx, hy, add_zero]
    zero_mem' := by simp
    smul_mem' := fun c {x} hx => by
      show ∑ j : Fin q, c * x j = 0
      rw [← Finset.mul_sum, hx, mul_zero] }

lemma finrank_H0 {q : ℕ} (hq : 1 ≤ q) : Module.finrank ℂ (H0 q) = q - 1 := by
  let φ : (Fin q → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∑ j, x j
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [← Finset.mul_sum] }
  have hker : LinearMap.ker φ = H0 q := rfl
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨Pi.single ⟨0, hq⟩ c, ?_⟩
    simp [φ, Pi.single_apply]
  have hr := LinearMap.finrank_range_add_finrank_ker φ
  rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hker, Module.finrank_fin_fun] at hr
  omega

def dot {q : ℕ} (u v : Fin q → ℂ) : ℂ := ∑ j, u j * v j

def formA (q : ℕ) : LinearMap.BilinForm ℂ (H0 q) :=
  LinearMap.mk₂ ℂ (fun u v => dot u.1 v.1)
    (fun u1 u2 v => by simp [dot, add_mul, Finset.sum_add_distrib])
    (fun c u v => by simp [dot, mul_assoc, ← Finset.mul_sum])
    (fun u v1 v2 => by simp [dot, mul_add, Finset.sum_add_distrib])
    (fun c u v => by simp [dot, mul_left_comm, ← Finset.mul_sum])

lemma formA_symm {q : ℕ} (u v : H0 q) : formA q u v = formA q v u := by
  simp only [formA, LinearMap.mk₂_apply, dot]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma formA_nondeg {q : ℕ} (hq : 1 ≤ q) {u : H0 q} (h : ∀ v : H0 q, formA q u v = 0) : u = 0 := by
  apply Subtype.ext
  funext j
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  let v : H0 q := ⟨fun k => (if k = j then (1 : ℂ) else 0) - (q : ℂ)⁻¹, by
    change ∑ k : Fin q, ((if k = j then (1 : ℂ) else 0) - (q : ℂ)⁻¹) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ j), Finset.sum_const,
      Finset.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hq0, sub_self]⟩
  have hv := h v
  simp only [formA, LinearMap.mk₂_apply, dot, v, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', if_pos (Finset.mem_univ j), ← Finset.sum_mul] at hv
  have hu : ∑ k : Fin q, u.1 k = 0 := u.2
  rw [hu, zero_mul, sub_zero] at hv
  exact hv

noncomputable def opT {q : ℕ} (hq : 1 ≤ q) (y : Fin q → ℂ) : H0 q →ₗ[ℂ] H0 q where
  toFun u :=
    let raw : Fin q → ℂ := fun j => (y j) ^ 2 * u.1 j - (1 / 3 : ℂ) * dot y u.1 * y j
    let avg : ℂ := (q : ℂ)⁻¹ * ∑ k, raw k
    ⟨fun j => raw j - avg, by
      have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
      change ∑ j : Fin q, (raw j - avg) = 0
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      simp only [avg]
      field_simp [hq0]; ring⟩
  map_add' u v := by
    apply Subtype.ext; funext j
    simp only [Submodule.coe_add, Pi.add_apply, dot]
    have hdot : (∑ i : Fin q, y i * (u.1 i + v.1 i)) = (∑ i, y i * u.1 i) + (∑ i, y i * v.1 i) := by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hdot]
    have hraw : (∑ k : Fin q, ((y k) ^ 2 * (u.1 k + v.1 k) - (1 / 3 : ℂ) * ((∑ i, y i * u.1 i) + ∑ i, y i * v.1 i) * y k)) =
        (∑ k : Fin q, ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k)) +
        (∑ k : Fin q, ((y k) ^ 2 * v.1 k - (1 / 3 : ℂ) * (∑ i, y i * v.1 i) * y k)) := by
      calc (∑ k : Fin q, ((y k) ^ 2 * (u.1 k + v.1 k) - (1 / 3 : ℂ) * ((∑ i, y i * u.1 i) + ∑ i, y i * v.1 i) * y k))
          = ∑ k : Fin q, (((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k) +
              ((y k) ^ 2 * v.1 k - (1 / 3 : ℂ) * (∑ i, y i * v.1 i) * y k)) :=
            Finset.sum_congr rfl fun k _ => by ring
        _ = (∑ k : Fin q, ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k)) +
            (∑ k : Fin q, ((y k) ^ 2 * v.1 k - (1 / 3 : ℂ) * (∑ i, y i * v.1 i) * y k)) :=
            Finset.sum_add_distrib
    rw [hraw]; ring
  map_smul' c u := by
    apply Subtype.ext; funext j
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dot]
    have hdot : (∑ i : Fin q, y i * (c * u.1 i)) = c * ∑ i, y i * u.1 i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    simp_rw [hdot]
    have hraw : (∑ k : Fin q, ((y k) ^ 2 * (c * u.1 k) - (1 / 3 : ℂ) * (c * ∑ i, y i * u.1 i) * y k)) =
        c * ∑ k : Fin q, ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k) := by
      calc (∑ k : Fin q, ((y k) ^ 2 * (c * u.1 k) - (1 / 3 : ℂ) * (c * ∑ i, y i * u.1 i) * y k))
          = ∑ k : Fin q, (c * ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k)) :=
            Finset.sum_congr rfl fun k _ => by ring
        _ = c * ∑ k : Fin q, ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k) :=
            (Finset.mul_sum _ _ _).symm
    rw [hraw]; ring

lemma formA_opT {q : ℕ} (hq : 1 ≤ q) (y : Fin q → ℂ) (u v : H0 q) :
    formA q (opT hq y u) v =
      (∑ j, (y j) ^ 2 * u.1 j * v.1 j) - (1 / 3 : ℂ) * dot y u.1 * dot y v.1 := by
  simp only [formA, LinearMap.mk₂_apply, opT, LinearMap.coe_mk, AddHom.coe_mk, dot]
  have hex : ∀ j : Fin q,
      (((y j) ^ 2 * u.1 j - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y j) -
        (q : ℂ)⁻¹ * ∑ k, ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k)) * v.1 j =
      (y j) ^ 2 * u.1 j * v.1 j - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * (y j * v.1 j) -
        ((q : ℂ)⁻¹ * ∑ k, ((y k) ^ 2 * u.1 k - (1 / 3 : ℂ) * (∑ i, y i * u.1 i) * y k)) * v.1 j :=
    fun j => by ring
  simp_rw [hex, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hv : ∑ j : Fin q, v.1 j = 0 := v.2
  rw [hv, mul_zero, sub_zero]

lemma opT_selfAdj {q : ℕ} (hq : 1 ≤ q) (y : Fin q → ℂ) (u v : H0 q) :
    formA q (opT hq y u) v = formA q u (opT hq y v) := by
  rw [formA_opT, formA_symm, formA_opT]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => by ring
  · ring

lemma sq_rt_exists (z : ℂ) : ∃ a : ℂ, a ^ 2 = z := by
  have h := IsAlgClosed.exists_root (Polynomial.X ^ 2 - Polynomial.C z) (by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num : 0 < 2)]; decide)
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    sub_eq_zero] at ha
  exact ha

lemma exists_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hpos : 0 < Module.finrank ℂ V) (T : V →ₗ[ℂ] V) :
    ∃ (μ : ℂ) (v : V), v ≠ 0 ∧ T v = μ • v := by
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
  exact ⟨μ, v, hv.2, Module.End.mem_eigenspace_iff.1 hv.1⟩

lemma lagrange_moment_zero {m : ℕ} (lam : Fin m → ℂ) (hinj : Function.Injective lam)
    (p : ℕ) (hp : p + 1 < m) :
    ∑ j : Fin m, (lam j) ^ p * (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (lam j - lam r))⁻¹ = 0 := by
  let P : Polynomial ℂ := Lagrange.interpolate Finset.univ lam (fun j => (lam j) ^ p)
  have hXP : P = Polynomial.X ^ p := by
    have hD_deg : (P - Polynomial.X ^ p).natDegree < m := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
      rw [max_lt_iff]
      constructor
      · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
        have hsup : Finset.univ.sup (fun j : Fin m =>
            (Polynomial.C ((lam j) ^ p) * Lagrange.basis Finset.univ lam j).natDegree) < m := by
          rw [Finset.sup_lt_iff (by omega : 0 < m)]
          intro j _
          refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
          have hnd : (Lagrange.basis Finset.univ lam j).natDegree = m - 1 := by
            simp only [Lagrange.basis, Lagrange.basisDivisor]
            have hprod : (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j,
                Polynomial.C (lam j - lam r)⁻¹ * (Polynomial.X - Polynomial.C (lam r))).natDegree = m - 1 := by
              rw [Finset.prod_mul_distrib, ← map_prod]
              have hcne : (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (lam j - lam r)⁻¹) ≠ 0 := by
                rw [Finset.prod_ne_zero_iff]
                intro r hr
                exact inv_ne_zero (sub_ne_zero.2 fun h => (Finset.mem_erase.1 hr).1 (hinj h.symm))
              rw [Polynomial.natDegree_C_mul hcne,
                Polynomial.natDegree_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C _]
              simp [Finset.card_erase_of_mem (Finset.mem_univ j)]
            exact hprod
          omega
        exact hsup
      · rw [Polynomial.natDegree_X_pow]; omega
    by_contra hne
    have hD_ne : P - Polynomial.X ^ p ≠ 0 := sub_ne_zero.2 hne
    have hroots : ∀ j : Fin m, (P - Polynomial.X ^ p).eval (lam j) = 0 := by
      intro j
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Lagrange.eval_interpolate_at_node (fun j => (lam j) ^ p) (fun _ _ _ _ h => hinj h) (Finset.mem_univ j),
        sub_self]
    have hsub : (Finset.univ.image lam).val ≤ (P - Polynomial.X ^ p).roots := by
      rw [Multiset.le_iff_subset (Finset.nodup _)]
      intro x hx
      simp only [Finset.mem_val, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := hx
      exact (Polynomial.mem_roots hD_ne).2 (hroots j)
    have hcard := Multiset.card_le_card hsub
    rw [Finset.card_val, Finset.card_image_of_injective _ hinj, Finset.card_fin] at hcard
    have hbound := Polynomial.card_roots' (P - Polynomial.X ^ p)
    omega
  have hdeg : P.natDegree < m - 1 := by
    rw [hXP, Polynomial.natDegree_X_pow]; omega
  have hcoeff : P.coeff (m - 1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
  have hP_coeff : P.coeff (m - 1) =
      ∑ j : Fin m, (lam j) ^ p * (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (lam j - lam r))⁻¹ := by
    have hsum : P.coeff (m - 1) = ∑ j : Fin m, (Polynomial.C ((lam j) ^ p) * Lagrange.basis Finset.univ lam j).coeff (m - 1) := by
      simpa [P, Lagrange.interpolate] using map_sum (Polynomial.lcoeff ℂ (m - 1))
        (fun j : Fin m => Polynomial.C ((lam j) ^ p) * Lagrange.basis Finset.univ lam j) Finset.univ
    rw [hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.coeff_C_mul]
    congr 1
    have hprod : (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j,
        Polynomial.C (lam j - lam r)⁻¹ * (Polynomial.X - Polynomial.C (lam r))).coeff (m - 1) =
        ∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (lam j - lam r)⁻¹ := by
      rw [Finset.prod_mul_distrib, ← map_prod, Polynomial.coeff_C_mul]
      have hmonic : (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (Polynomial.X - Polynomial.C (lam r))).Monic :=
        Polynomial.monic_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C _
      have hnd : (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (Polynomial.X - Polynomial.C (lam r))).natDegree = m - 1 := by
        rw [Polynomial.natDegree_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C _]
        simp [Finset.card_erase_of_mem (Finset.mem_univ j)]
      rw [← hnd, hmonic.coeff_natDegree, mul_one]
    have hcoeff_eq : (Lagrange.basis Finset.univ lam j).coeff (m - 1) =
        (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j,
          Polynomial.C (lam j - lam r)⁻¹ * (Polynomial.X - Polynomial.C (lam r))).coeff (m - 1) := by
      congr 1
    rw [hcoeff_eq, hprod, ← Finset.prod_inv_distrib]
  rw [← hP_coeff, hcoeff]

lemma exists_ortho_eigenbasis : ∀ (d : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    Module.finrank ℂ V = d →
    ∀ (A : LinearMap.BilinForm ℂ V) (T : V →ₗ[ℂ] V),
      (∀ u v, A u v = A v u) →
      (∀ u, (∀ v, A u v = 0) → u = 0) →
      (∀ u v, A (T u) v = A u (T v)) →
      (∀ e : V, e ≠ 0 → (∃ μ : ℂ, T e = μ • e) → A e e ≠ 0) →
      ∃ (e : Fin d → V) (lam : Fin d → ℂ),
        (∀ i, T (e i) = lam i • e i) ∧
        (∀ i j, A (e i) (e j) = if i = j then 1 else 0) := by
  intro d
  induction d with
  | zero =>
    intro V _ _ _ _ _ _ _ _ _ _
    exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ d ih =>
    intro V _ _ _ hd A T hsym hnondeg hsa hnoiso
    obtain ⟨μ, v0, hv0, hTv0⟩ := exists_eigenvector (by omega : 0 < Module.finrank ℂ V) T
    have hAv0 : A v0 v0 ≠ 0 := hnoiso v0 hv0 ⟨μ, hTv0⟩
    obtain ⟨s, hs⟩ := sq_rt_exists (A v0 v0)
    have hs0 : s ≠ 0 := fun h => hAv0 (by rw [← hs, h]; simp)
    let e0 : V := s⁻¹ • v0
    have he0_eig : T e0 = μ • e0 := by simp only [e0, map_smul, hTv0]; rw [smul_comm]
    have he0_A : A e0 e0 = 1 := by
      simp only [e0, map_smul, LinearMap.smul_apply, smul_eq_mul]
      rw [← hs]; field_simp [hs0]
    let W : Submodule ℂ V := LinearMap.ker (A e0)
    have hW_dim : Module.finrank ℂ W = d := by
      have hsurj : Function.Surjective (A e0) := by
        intro c; refine ⟨c • e0, by simp [map_smul, he0_A]⟩
      have hr := LinearMap.finrank_range_add_finrank_ker (A e0)
      rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self, hd] at hr
      dsimp only [W]; omega
    have hTW : ∀ w : W, T w.1 ∈ W := by
      intro w
      change A e0 (T w.1) = 0
      rw [← hsa, he0_eig, map_smul, LinearMap.smul_apply, smul_eq_mul]
      have hw : A e0 w.1 = 0 := w.2
      rw [hw, mul_zero]
    let AW : LinearMap.BilinForm ℂ W :=
      LinearMap.mk₂ ℂ (fun u v => A u.1 v.1)
        (fun u1 u2 v => by simp) (fun c u v => by simp)
        (fun u v1 v2 => by simp) (fun c u v => by simp)
    let TW : W →ₗ[ℂ] W :=
      { toFun := fun w => ⟨T w.1, hTW w⟩
        map_add' := fun u v => by apply Subtype.ext; simp
        map_smul' := fun c u => by apply Subtype.ext; simp }
    have hAW_nondeg : ∀ u : W, (∀ v : W, AW u v = 0) → u = 0 := by
      intro u hu
      apply Subtype.ext
      apply hnondeg u.1
      intro x
      let w : W := ⟨x - (A e0 x) • e0, by
        change A e0 (x - (A e0 x) • e0) = 0
        simp [map_sub, map_smul, he0_A]⟩
      have h1 := hu w
      simp only [AW, LinearMap.mk₂_apply, w, map_sub, map_smul, smul_eq_mul] at h1
      have hu0 : A u.1 e0 = 0 := by rw [hsym]; exact u.2
      rw [hu0, mul_zero, sub_zero] at h1
      exact h1
    have hnoisoW : ∀ e : W, e ≠ 0 → (∃ μ' : ℂ, TW e = μ' • e) → AW e e ≠ 0 := by
      intro e he ⟨μ', hμ'⟩
      exact hnoiso e.1 (fun h => he (Subtype.ext h)) ⟨μ', congrArg Subtype.val hμ'⟩
    obtain ⟨e', lam', he'_eig, he'_A⟩ := ih hW_dim AW TW
      (fun u v => hsym u.1 v.1) hAW_nondeg (fun u v => hsa u.1 v.1) hnoisoW
    refine ⟨Fin.cons e0 (fun i => (e' i).1), Fin.cons μ lam', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact he0_eig
      · intro j; exact congrArg Subtype.val (he'_eig j)
    · intro i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simpa using he0_A
        · simp [(Fin.succ_ne_zero j').symm, (e' j').2]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · rw [hsym]; simp [Fin.succ_ne_zero i', (e' i').2]
        · have h := he'_A i' j'
          simpa [AW, LinearMap.mk₂_apply, Fin.succ_inj] using h

lemma exists_iso_subspace : ∀ (k : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : LinearMap.BilinForm ℂ V) (T : V →ₗ[ℂ] V),
    (∀ u v, A u v = A v u) →
    (∀ u, (∀ v, A u v = 0) → u = 0) →
    (∀ u v, A (T u) v = A u (T v)) →
    2 * k + 1 ≤ Module.finrank ℂ V →
    ∃ K : Submodule ℂ V, Module.finrank ℂ K = k ∧
      ∀ u ∈ K, ∀ v ∈ K, A u v = 0 ∧ A (T u) v = 0 := by
  intro k
  induction k with
  | zero =>
    intro V _ _ _ A T _ _ _ _
    exact ⟨⊥, finrank_bot ℂ V, fun u hu v _ => by rw [(Submodule.mem_bot ℂ).1 hu]; simp⟩
  | succ k ih =>
    intro V _ _ _ A T hsym hnondeg hsa hdim
    by_cases hiso : ∃ e : V, e ≠ 0 ∧ (∃ μ : ℂ, T e = μ • e) ∧ A e e = 0
    · obtain ⟨e, he0, ⟨μ, hTe⟩, hAee⟩ := hiso
      let W : Submodule ℂ V := LinearMap.ker (A e)
      have heW : e ∈ W := hAee
      have hW_dim : Module.finrank ℂ W = Module.finrank ℂ V - 1 := by
        have hsurj : Function.Surjective (A e) := by
          have hne : A e ≠ 0 := fun h => he0 (hnondeg e fun v => LinearMap.ext_iff.1 h v)
          obtain ⟨x0, hx0⟩ : ∃ x0, A e x0 ≠ 0 := by
            by_contra hall; push Not at hall; exact hne (LinearMap.ext hall)
          intro c; exact ⟨(c * (A e x0)⁻¹) • x0, by simp [map_smul, hx0]⟩
        have hr := LinearMap.finrank_range_add_finrank_ker (A e)
        rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at hr
        dsimp only [W]; omega
      let L : Submodule ℂ W := Submodule.span ℂ {⟨e, heW⟩}
      have hL_dim : Module.finrank ℂ L = 1 :=
        finrank_span_singleton (K := ℂ) (fun h => he0 (congrArg Subtype.val h))
      let Q := W ⧸ L
      have hQ_dim : Module.finrank ℂ Q = Module.finrank ℂ V - 2 := by
        have hr := Submodule.finrank_quotient_add_finrank L
        rw [hL_dim, hW_dim] at hr; dsimp only [Q]; omega
      have hAL : ∀ u : W, u ∈ L → ∀ v : W, A u.1 v.1 = 0 := by
        intro u hu v
        rw [Submodule.mem_span_singleton] at hu
        obtain ⟨c, rfl⟩ := hu
        simp only [SetLike.val_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
        have hv : A e v.1 = 0 := v.2
        rw [hv, mul_zero]
      have hTW : ∀ w : W, T w.1 ∈ W := by
        intro w
        change A e (T w.1) = 0
        rw [← hsa, hTe, map_smul, LinearMap.smul_apply, smul_eq_mul]
        have hw : A e w.1 = 0 := w.2
        rw [hw, mul_zero]
      let TW : W →ₗ[ℂ] W :=
        { toFun := fun w => ⟨T w.1, hTW w⟩
          map_add' := fun u v => by apply Subtype.ext; simp
          map_smul' := fun c u => by apply Subtype.ext; simp }
      have hTL : ∀ u : W, u ∈ L → TW u ∈ L := by
        intro u hu
        rw [Submodule.mem_span_singleton] at hu ⊢
        obtain ⟨c, rfl⟩ := hu
        refine ⟨c * μ, ?_⟩
        apply Subtype.ext
        simp [TW, map_smul, hTe, mul_smul]
      let TQ : Q →ₗ[ℂ] Q := Submodule.mapQ L L TW (fun u hu => hTL u hu)
      let AQ_left : W →ₗ[ℂ] (Q →ₗ[ℂ] ℂ) :=
        { toFun := fun u => Submodule.liftQ L ((A u.1).comp W.subtype) (fun v hv => by
            simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.coe_subtype]
            rw [hsym]; exact hAL v hv u)
          map_add' := fun u1 u2 => by
            ext v; simp
          map_smul' := fun c u => by
            ext v; simp }
      let AQ : LinearMap.BilinForm ℂ Q :=
        Submodule.liftQ L AQ_left (fun u hu => by
          rw [LinearMap.mem_ker]
          ext v
          exact hAL u hu v)
      have hAQ_mk : ∀ u v : W, AQ (Submodule.Quotient.mk u) (Submodule.Quotient.mk v) = A u.1 v.1 :=
        fun _ _ => rfl
      have hTQ_mk : ∀ u : W, TQ (Submodule.Quotient.mk u) = Submodule.Quotient.mk (TW u) :=
        fun _ => rfl
      have hAQ_symm : ∀ x y : Q, AQ x y = AQ y x := by
        intro x y
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective L x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L y
        exact hsym u.1 v.1
      have hAQ_sa : ∀ x y : Q, AQ (TQ x) y = AQ x (TQ y) := by
        intro x y
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective L x
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective L y
        exact hsa u.1 v.1
      have hAQ_nondeg : ∀ x : Q, (∀ y : Q, AQ x y = 0) → x = 0 := by
        intro x hx
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective L x
        rw [Submodule.Quotient.mk_eq_zero]
        have hu_ker : W ≤ LinearMap.ker (A u.1) := by
          intro v hv
          exact hx (Submodule.Quotient.mk ⟨v, hv⟩)
        have hker_dim : Module.finrank ℂ (LinearMap.ker (A u.1)) ≤ Module.finrank ℂ V - 1 ∨ u.1 = 0 := by
          by_cases hu0 : u.1 = 0
          · exact Or.inr hu0
          · left
            have hne : A u.1 ≠ 0 := fun h => hu0 (hnondeg u.1 fun v => LinearMap.ext_iff.1 h v)
            obtain ⟨x0, hx0⟩ : ∃ x0, A u.1 x0 ≠ 0 := by
              by_contra hall; push Not at hall; exact hne (LinearMap.ext hall)
            have hsurj : Function.Surjective (A u.1) := fun c => ⟨(c * (A u.1 x0)⁻¹) • x0, by simp [map_smul, hx0]⟩
            have hr := LinearMap.finrank_range_add_finrank_ker (A u.1)
            rw [LinearMap.range_eq_top.2 hsurj, finrank_top, Module.finrank_self] at hr
            omega
        rcases hker_dim with hle | hu0
        · have hkeq : W = LinearMap.ker (A u.1) :=
            Submodule.eq_of_le_of_finrank_eq hu_ker (le_antisymm (Submodule.finrank_mono hu_ker) (hW_dim ▸ hle))
          have hne : A e ≠ 0 := fun h => he0 (hnondeg e fun v => LinearMap.ext_iff.1 h v)
          obtain ⟨x0, hx0⟩ : ∃ x0, A e x0 ≠ 0 := by
            by_contra hall; push Not at hall; exact hne (LinearMap.ext hall)
          let c : ℂ := A u.1 x0 * (A e x0)⁻¹
          have huc : u.1 = c • e := by
            apply hnondeg (u.1 - c • e) |> fun h => sub_eq_zero.1 (h _)
            intro v
            let w : V := v - (A e v * (A e x0)⁻¹) • x0
            have hw : w ∈ W := by
              change A e w = 0
              simp only [w, map_sub, map_smul, smul_eq_mul]
              field_simp [hx0]; ring
            have huw : A u.1 w = 0 := by rw [hkeq] at hw; exact hw
            simp only [w, map_sub, map_smul, smul_eq_mul] at huw
            simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
            have h1 : A u.1 v = A e v * (A e x0)⁻¹ * A u.1 x0 := by linear_combination huw
            rw [h1]; simp only [c]; ring
          rw [Submodule.mem_span_singleton]
          exact ⟨c, Subtype.ext huc.symm⟩
        · have : u = 0 := Subtype.ext hu0
          rw [this]; exact Submodule.zero_mem L
      obtain ⟨KQ, hKQ_dim, hKQ_iso⟩ := ih AQ TQ hAQ_symm hAQ_nondeg hAQ_sa (by omega)
      let KW : Submodule ℂ W := KQ.comap L.mkQ
      let K : Submodule ℂ V := KW.map W.subtype
      have hK_dim : Module.finrank ℂ K = k + 1 := by
        have h1 : Module.finrank ℂ K = Module.finrank ℂ KW :=
          Submodule.finrank_map_subtype_eq W KW
        have h2 : Module.finrank ℂ KW = Module.finrank ℂ KQ + Module.finrank ℂ L := by
          have hr := LinearMap.finrank_range_add_finrank_ker (L.mkQ.domRestrict KW)
          have hrg : LinearMap.range (L.mkQ.domRestrict KW) = KQ := by
            ext q; constructor
            · rintro ⟨⟨w, hw⟩, rfl⟩; exact hw
            · intro hq
              obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective L q
              exact ⟨⟨w, hq⟩, rfl⟩
          have hkr : Module.finrank ℂ (LinearMap.ker (L.mkQ.domRestrict KW)) = Module.finrank ℂ L := by
            have hle : L ≤ KW := by
              intro w hw; change L.mkQ w ∈ KQ
              rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L).2 hw]; exact Submodule.zero_mem KQ
            let e_ker : L ≃ₗ[ℂ] LinearMap.ker (L.mkQ.domRestrict KW) :=
              { toFun := fun x => ⟨⟨x.1, hle x.2⟩, by
                  change L.mkQ x.1 = 0; exact (Submodule.Quotient.mk_eq_zero L).2 x.2⟩
                invFun := fun y => ⟨y.1.1, (Submodule.Quotient.mk_eq_zero L).1 y.2⟩
                left_inv := fun _ => rfl
                right_inv := fun _ => rfl
                map_add' := fun _ _ => rfl
                map_smul' := fun _ _ => rfl }
            exact e_ker.finrank_eq.symm
          rw [hrg, hkr] at hr; exact hr.symm
        rw [h1, h2, hKQ_dim, hL_dim]
      refine ⟨K, hK_dim, ?_⟩
      rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      have h := hKQ_iso (L.mkQ u) hu (L.mkQ v) hv
      exact h
    · push Not at hiso
      obtain ⟨e, lam, he_eig, he_A⟩ := exists_ortho_eigenbasis (Module.finrank ℂ V) rfl A T hsym hnondeg hsa hiso
      have hlam_inj : Function.Injective lam := by
        intro i j hij
        by_contra hne
        let v : V := e i + Complex.I • e j
        have hv0 : v ≠ 0 := by
          intro hz
          have h1 := congrArg (A (e i)) hz
          simp only [v, map_add, map_smul, smul_eq_mul, he_A, ite_true, if_neg hne, mul_zero, add_zero, map_zero] at h1
          exact one_ne_zero h1
        have hv_eig : T v = lam i • v := by
          simp only [v, map_add, map_smul, he_eig, hij, smul_add]
          congr 1; rw [smul_comm]
        have hv_iso : A v v = 0 := by
          simp only [v, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
            he_A, ite_true, if_neg hne, if_neg (Ne.symm hne)]
          have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
          linear_combination hI
        exact hiso v hv0 ⟨lam i, hv_eig⟩ hv_iso
      let m := 2 * (k + 1) + 1
      have hm_le : m ≤ Module.finrank ℂ V := hdim
      let emb : Fin m ↪ Fin (Module.finrank ℂ V) := Fin.castLEEmb hm_le
      let lam' : Fin m → ℂ := fun j => lam (emb j)
      have hlam'_inj : Function.Injective lam' := hlam_inj.comp emb.injective
      let z : Fin m → ℂ := fun j => (∏ r ∈ (Finset.univ : Finset (Fin m)).erase j, (lam' j - lam' r))⁻¹
      have hz_ne : ∀ j : Fin m, z j ≠ 0 := by
        intro j
        apply inv_ne_zero
        rw [Finset.prod_ne_zero_iff]
        intro r hr
        exact sub_ne_zero.2 fun h => (Finset.mem_erase.1 hr).1 (hlam'_inj h.symm)
      have ha_ex : ∀ j : Fin m, ∃ a : ℂ, a ^ 2 = z j := fun j => sq_rt_exists (z j)
      choose a ha using ha_ex
      have ha_ne : ∀ j : Fin m, a j ≠ 0 := fun j h => hz_ne j (by rw [← ha j, h]; simp)
      let w : Fin (k + 1) → V := fun s => ∑ j : Fin m, ((lam' j) ^ s.val * a j) • e (emb j)
      have hw_li : LinearIndependent ℂ w := by
        rw [Fintype.linearIndependent_iff]
        intro c hc
        let P : Polynomial ℂ := ∑ s : Fin (k + 1), Polynomial.C (c s) * Polynomial.X ^ s.val
        have hP_roots : ∀ j : Fin m, P.eval (lam' j) = 0 := by
          intro j
          have hA := congrArg (A (e (emb j))) hc
          simp only [w, map_sum, map_smul, smul_eq_mul, map_zero] at hA
          have hinner : ∀ s : Fin (k + 1),
              (∑ j' : Fin m, (lam' j') ^ s.val * a j' * A (e (emb j)) (e (emb j'))) = (lam' j) ^ s.val * a j := by
            intro s
            have : ∀ j' : Fin m, (lam' j') ^ s.val * a j' * A (e (emb j)) (e (emb j')) =
                if j' = j then (lam' j) ^ s.val * a j else 0 := by
              intro j'
              rw [he_A]
              by_cases hjj : j' = j
              · subst hjj; simp
              · have hne : emb j ≠ emb j' := fun h => hjj (emb.injective h.symm)
                simp [hjj, hne]
            simp [this]
          simp_rw [hinner] at hA
          have hmul : (∑ s : Fin (k + 1), c s * (lam' j) ^ s.val) * a j = 0 := by
            rw [Finset.sum_mul]
            convert hA using 1
            exact Finset.sum_congr rfl fun s _ => by ring
          have h0 := (mul_eq_zero.1 hmul).resolve_right (ha_ne j)
          have hev : P.eval (lam' j) = ∑ s : Fin (k + 1), c s * (lam' j) ^ s.val := by
            rw [← Polynomial.coe_evalRingHom]
            simp only [P, map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
              Polynomial.eval_C, Polynomial.eval_X]
          rw [hev]; exact h0
        have hP_zero : P = 0 := by
          by_contra hPne
          have hdeg : P.natDegree < m := by
            have hle : P.natDegree ≤ k := by
              refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
              refine Finset.sup_le fun s _ => ?_
              refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
              rw [Polynomial.natDegree_X_pow]; omega
            omega
          have hcard_roots : m ≤ P.roots.card := by
            have hsub : (Finset.univ.image lam').val ≤ P.roots := by
              rw [Multiset.le_iff_subset (Finset.nodup _)]
              intro x hx
              simp only [Finset.mem_val, Finset.mem_image, Finset.mem_univ, true_and] at hx
              obtain ⟨j, rfl⟩ := hx
              exact (Polynomial.mem_roots hPne).2 (hP_roots j)
            have h1 := Multiset.card_le_card hsub
            rw [Finset.card_val, Finset.card_image_of_injective _ hlam'_inj, Finset.card_fin] at h1
            exact h1
          have hbound := Polynomial.card_roots' P
          omega
        intro s
        have hcs := congrArg (fun p : Polynomial ℂ => p.coeff s.val) hP_zero
        have hsumc : P.coeff s.val = ∑ s' : Fin (k + 1), c s' * (if s.val = s'.val then (1 : ℂ) else 0) := by
          simpa [P, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using
            map_sum (Polynomial.lcoeff ℂ s.val)
              (fun s' : Fin (k + 1) => Polynomial.C (c s') * Polynomial.X ^ s'.val) Finset.univ
        rw [hsumc, Polynomial.coeff_zero] at hcs
        have : ∀ s' : Fin (k + 1), c s' * (if s.val = s'.val then (1 : ℂ) else 0) = if s' = s then c s else 0 := by
          intro s'
          by_cases h : s' = s
          · subst h; simp
          · have hv : s.val ≠ s'.val := fun hv => h (Fin.ext hv.symm)
            simp [h, hv]
        simp [this] at hcs
        exact hcs
      have hw_iso : ∀ r s : Fin (k + 1), A (w r) (w s) = 0 ∧ A (T (w r)) (w s) = 0 := by
        intro r s
        have hcalc : ∀ (p : ℕ) (f : Fin m → ℂ),
            (∀ j, f j = (lam' j) ^ p * a j) →
            A (∑ j : Fin m, f j • e (emb j)) (w s) = ∑ j : Fin m, (lam' j) ^ (p + s.val) * z j := by
          intro p f hf
          simp only [w, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          have hinner : ∑ x : Fin m, f x * A (e (emb x)) (e (emb j)) = f j := by
            have hterm : ∀ x : Fin m, f x * A (e (emb x)) (e (emb j)) =
                if x = j then f j else 0 := by
              intro x
              rw [he_A]
              by_cases hxj : x = j
              · subst hxj; simp
              · have hne : emb x ≠ emb j := fun h => hxj (emb.injective h)
                simp [hxj, hne]
            simp [hterm]
          rw [hinner, hf j, ← ha j, pow_add]; ring
        have hA_rs : A (w r) (w s) = 0 := by
          rw [hcalc r.val _ (fun _ => rfl)]
          exact lagrange_moment_zero lam' hlam'_inj (r.val + s.val) (by dsimp only [m]; omega)
        have hT_wr : T (w r) = ∑ j : Fin m, ((lam' j) ^ (r.val + 1) * a j) • e (emb j) := by
          simp only [w, map_sum, map_smul, he_eig]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [smul_smul]; congr 1; rw [pow_succ]; ring
        have hB_rs : A (T (w r)) (w s) = 0 := by
          rw [hT_wr, hcalc (r.val + 1) _ (fun _ => rfl)]
          exact lagrange_moment_zero lam' hlam'_inj (r.val + 1 + s.val) (by dsimp only [m]; omega)
        exact ⟨hA_rs, hB_rs⟩
      refine ⟨Submodule.span ℂ (Set.range w), ?_, ?_⟩
      · rw [finrank_span_eq_card hw_li, Fintype.card_fin]
      · intro u hu v hv
        rw [Submodule.mem_span_range_iff_exists_fun] at hu hv
        obtain ⟨cu, rfl⟩ := hu
        obtain ⟨cv, rfl⟩ := hv
        constructor
        · simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun r _ => ?_
          rw [mul_eq_zero]; right; refine Finset.sum_eq_zero fun s _ => ?_
          rw [(hw_iso s r).1, mul_zero]
        · simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
          refine Finset.sum_eq_zero fun r _ => ?_
          rw [mul_eq_zero]; right; refine Finset.sum_eq_zero fun s _ => ?_
          rw [(hw_iso s r).2, mul_zero]

lemma charpoly_eq_sq_of_lagrangian {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : LinearMap.BilinForm ℂ V) (T : V →ₗ[ℂ] V)
    (hsym : ∀ u v, A u v = A v u)
    (hnondeg : ∀ u, (∀ v, A u v = 0) → u = 0)
    (hsa : ∀ u v, A (T u) v = A u (T v))
    (K : Submodule ℂ V) (hk : 2 * Module.finrank ℂ K = Module.finrank ℂ V)
    (hK_iso : ∀ u ∈ K, ∀ v ∈ K, A u v = 0 ∧ A (T u) v = 0) :
    ∃ g : Polynomial ℂ, T.charpoly = g ^ 2 := by
  let k := Module.finrank ℂ K
  let bK := Module.finBasis ℂ K
  let b : Fin k → V := fun i => (bK i).1
  have hK_orth_eq : ∀ x : V, (∀ u ∈ K, A x u = 0) → x ∈ K := by
    intro x hx
    let Kperp : Submodule ℂ V :=
      { carrier := {w | ∀ u ∈ K, A w u = 0}, add_mem' := fun {w1 w2} h1 h2 u hu => by simp [h1 u hu, h2 u hu]
        zero_mem' := fun u _ => by simp
        smul_mem' := fun c {w} hw u hu => by simp [hw u hu] }
    have hle : K ≤ Kperp := fun u hu v hv => (hK_iso u hu v hv).1
    let Φ : V →ₗ[ℂ] (Fin k → ℂ) :=
      { toFun := fun w i => A w (b i)
        map_add' := fun w1 w2 => by funext i; simp
        map_smul' := fun c w => by funext i; simp }
    have hker : LinearMap.ker Φ = Kperp := by
      ext w; constructor
      · intro hw u hu
        have hrep := (bK.sum_repr ⟨u, hu⟩).symm
        have hu_eq : u = ∑ i : Fin k, bK.repr ⟨u, hu⟩ i • b i := by
          have := congrArg Subtype.val hrep; rw [Submodule.coe_sum] at this; exact this
        rw [hu_eq, map_sum]
        apply Finset.sum_eq_zero; intro i _
        rw [map_smul, smul_eq_mul]
        have hi : A w (b i) = 0 := congrFun hw i
        rw [hi, mul_zero]
      · intro hw; funext i; exact hw (b i) (bK i).2
    have hΦ_surj : Function.Surjective Φ := by
      intro y
      obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
      let fK : K →ₗ[ℂ] ℂ := bK.constr ℂ y
      let fV : V →ₗ[ℂ] ℂ := fK.comp ((LinearMap.fst ℂ K K').comp (Submodule.prodEquivOfIsCompl K K' hK').symm.toLinearMap)
      have hfV : ∀ i : Fin k, fV (b i) = y i := by
        intro i
        have h1 : (Submodule.prodEquivOfIsCompl K K' hK').symm (b i) = (bK i, 0) := by
          apply (Submodule.prodEquivOfIsCompl K K' hK').injective
          rw [LinearEquiv.apply_symm_apply]
          change (bK i).1 = (bK i).1 + (0 : K').1
          simp
        change fK (LinearMap.fst ℂ K K' ((Submodule.prodEquivOfIsCompl K K' hK').symm (b i))) = y i
        rw [h1]
        simp [fK]
      let Ψ : V →ₗ[ℂ] Module.Dual ℂ V := A
      have hΨ_inj : Function.Injective Ψ := by
        rw [injective_iff_map_eq_zero]
        intro u hu; exact hnondeg u fun v => LinearMap.ext_iff.1 hu v
      have hΨ_surj : Function.Surjective Ψ := by
        have hr := LinearMap.finrank_range_add_finrank_ker Ψ
        rw [LinearMap.ker_eq_bot.2 hΨ_inj, finrank_bot, add_zero] at hr
        have htop : LinearMap.range Ψ = ⊤ :=
          Submodule.eq_top_of_finrank_eq (hr.trans Subspace.dual_finrank_eq.symm)
        intro f; have : f ∈ LinearMap.range Ψ := by rw [htop]; trivial
        exact this
      obtain ⟨w, hw⟩ := hΨ_surj fV
      refine ⟨w, ?_⟩
      funext i
      change A w (b i) = y i
      rw [show A w (b i) = Ψ w (b i) from rfl, hw, hfV i]
    have hr := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.2 hΦ_surj, finrank_top, Module.finrank_fin_fun, hker] at hr
    have hKp_dim : Module.finrank ℂ Kperp = k := by dsimp only [k] at *; omega
    have hkeq : K = Kperp := Submodule.eq_of_le_of_finrank_eq hle hKp_dim.symm
    exact hkeq ▸ hx
  have hTK : ∀ u ∈ K, T u ∈ K := fun u hu => hK_orth_eq (T u) fun v hv => (hK_iso u hu v hv).2
  by_cases hk0 : k = 0
  · have hV0 : Module.finrank ℂ V = 0 := by dsimp only [k] at hk0; omega
    have htop : (⊤ : Submodule ℂ V) = ⊥ := Submodule.finrank_eq_zero.1 (by rw [finrank_top, hV0])
    haveI : Subsingleton V := ⟨fun x y => by
      have hx : x = 0 := (Submodule.mem_bot ℂ).1 (htop ▸ Submodule.mem_top)
      have hy : y = 0 := (Submodule.mem_bot ℂ).1 (htop ▸ Submodule.mem_top)
      rw [hx, hy]⟩
    refine ⟨1, ?_⟩
    have h1 : T.charpoly = 1 := by
      let B0 : Module.Basis (Fin 0) ℂ V := Module.Basis.empty V
      rw [← LinearMap.charpoly_toMatrix T B0]
      simp [Matrix.charpoly]
    rw [h1, one_pow]
  haveI : Nonempty (Fin k ⊕ Fin k) := ⟨Sum.inl ⟨0, Nat.pos_of_ne_zero hk0⟩⟩
  let Φ : V →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun w i => A (b i) w
      map_add' := fun w1 w2 => by funext i; simp
      map_smul' := fun c w => by funext i; simp }
  have hΦ_ker : LinearMap.ker Φ = K := by
    ext w; constructor
    · intro hw
      apply hK_orth_eq w
      intro u hu
      have hrep := (bK.sum_repr ⟨u, hu⟩).symm
      have hu_eq : u = ∑ i : Fin k, bK.repr ⟨u, hu⟩ i • b i := by
        have := congrArg Subtype.val hrep; rw [Submodule.coe_sum] at this; exact this
      rw [hu_eq, map_sum]
      apply Finset.sum_eq_zero; intro i _
      rw [map_smul, smul_eq_mul, hsym]
      have hi : A (b i) w = 0 := congrFun hw i
      rw [hi, mul_zero]
    · intro hw; funext i; exact (hK_iso (b i) (bK i).2 w hw).1
  have hΦ_surj : Function.Surjective Φ := by
    have hr := LinearMap.finrank_range_add_finrank_ker Φ
    rw [hΦ_ker] at hr
    have hrg : Module.finrank ℂ (LinearMap.range Φ) = Module.finrank ℂ (Fin k → ℂ) := by
      rw [Module.finrank_fin_fun]; omega
    have htop : LinearMap.range Φ = ⊤ := Submodule.eq_top_of_finrank_eq hrg
    intro y; have : y ∈ LinearMap.range Φ := by rw [htop]; trivial
    exact this
  have hc_ex : ∀ j : Fin k, ∃ c : V, Φ c = Pi.single j 1 := fun j => hΦ_surj (Pi.single j 1)
  choose c hc using hc_ex
  let bc : Fin k ⊕ Fin k → V := Sum.elim b c
  have hbc_li : LinearIndependent ℂ bc := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg_c : ∀ j : Fin k, g (Sum.inr j) = 0 := by
      intro j
      have hA := congrArg (A (b j)) hg
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_add, map_sum, map_smul,
        smul_eq_mul, map_zero, bc] at hA
      have h1 : ∀ i : Fin k, A (b j) (b i) = 0 := fun i => (hK_iso (b j) (bK j).2 (b i) (bK i).2).1
      have h2 : ∀ i : Fin k, A (b j) (c i) = if j = i then 1 else 0 := fun i => by
        have := congrFun (hc i) j; simpa [Φ, Pi.single_apply] using this
      simp [h1, h2] at hA
      exact hA
    have hg_b : ∑ i : Fin k, g (Sum.inl i) • b i = 0 := by
      simpa [Fintype.sum_sum_type, bc, hg_c] using hg
    have hg_b0 : ∀ i : Fin k, g (Sum.inl i) = 0 := by
      have hli_b : LinearIndependent ℂ b := bK.linearIndependent.map' K.subtype (Submodule.ker_subtype K)
      exact Fintype.linearIndependent_iff.1 hli_b (fun i => g (Sum.inl i)) hg_b
    intro s; rcases s with i | j
    · exact hg_b0 i
    · exact hg_c j
  have hbc_card : Fintype.card (Fin k ⊕ Fin k) = Module.finrank ℂ V := by
    simp [Fintype.card_sum]; omega
  let B : Module.Basis (Fin k ⊕ Fin k) ℂ V := basisOfLinearIndependentOfCardEqFinrank hbc_li hbc_card
  let M := LinearMap.toMatrix B B T
  have hB_inl : ∀ r : Fin k, B (Sum.inl r) = b r := fun r => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank, bc]
  have hB_inr : ∀ r : Fin k, B (Sum.inr r) = c r := fun r => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank, bc]
  have hM_bl : ∀ i j : Fin k, M (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have hTj_eq : T (B (Sum.inl j)) = ∑ s : Fin k ⊕ Fin k, M s (Sum.inl j) • B s := by
      simpa [M, LinearMap.toMatrix_apply] using (B.sum_repr (T (B (Sum.inl j)))).symm
    have hA := congrArg (A (b i)) hTj_eq
    simp only [Fintype.sum_sum_type, hB_inl, hB_inr, map_add, map_sum, map_smul, smul_eq_mul] at hA
    have h1 : ∀ r : Fin k, A (b i) (b r) = 0 := fun r => (hK_iso (b i) (bK i).2 (b r) (bK r).2).1
    have h2 : ∀ r : Fin k, A (b i) (c r) = if i = r then 1 else 0 := fun r => by
      have := congrFun (hc r) i; simpa [Φ, Pi.single_apply] using this
    have h0 : A (b i) (T (b j)) = 0 := by rw [hsym]; exact (hK_iso (b j) (bK j).2 (b i) (bK i).2).2
    simp [h1, h2, h0] at hA
    exact hA.symm
  have hM_br : ∀ i j : Fin k, M (Sum.inr i) (Sum.inr j) = M (Sum.inl j) (Sum.inl i) := by
    intro i j
    have h1 : ∀ r : Fin k, A (b i) (b r) = 0 := fun r => (hK_iso (b i) (bK i).2 (b r) (bK r).2).1
    have h2 : ∀ r s : Fin k, A (b r) (c s) = if r = s then 1 else 0 := fun r s => by
      have := congrFun (hc s) r; simpa [Φ, Pi.single_apply] using this
    have hL : A (b i) (T (c j)) = M (Sum.inr i) (Sum.inr j) := by
      have hTj_eq : T (c j) = ∑ s : Fin k ⊕ Fin k, M s (Sum.inr j) • B s := by
        rw [← hB_inr j]; simpa [M, LinearMap.toMatrix_apply] using (B.sum_repr (T (B (Sum.inr j)))).symm
      rw [hTj_eq]; simp [Fintype.sum_sum_type, hB_inl, hB_inr, h1, h2]
    have hR : A (T (b i)) (c j) = M (Sum.inl j) (Sum.inl i) := by
      have hTi_eq : T (b i) = ∑ s : Fin k ⊕ Fin k, M s (Sum.inl i) • B s := by
        rw [← hB_inl i]; simpa [M, LinearMap.toMatrix_apply] using (B.sum_repr (T (B (Sum.inl i)))).symm
      rw [hTi_eq]
      simp only [Fintype.sum_sum_type, hB_inl, hB_inr, map_add, map_sum, map_smul, LinearMap.add_apply,
        LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hM_bl, zero_mul, Finset.sum_const_zero, add_zero]
      simp [h2]
    rw [← hL, ← hR, hsa]
  let P : Matrix (Fin k) (Fin k) ℂ := fun i j => M (Sum.inl i) (Sum.inl j)
  let R : Matrix (Fin k) (Fin k) ℂ := fun i j => M (Sum.inl i) (Sum.inr j)
  have hM_eq : M = Matrix.fromBlocks P R 0 P.transpose := by
    ext s t
    rcases s with i | i <;> rcases t with j | j
    · rfl
    · rfl
    · exact hM_bl i j
    · exact hM_br i j
  refine ⟨P.charpoly, ?_⟩
  rw [← LinearMap.charpoly_toMatrix T B, show LinearMap.toMatrix B B T = M from rfl, hM_eq,
    Matrix.charpoly_fromBlocks_zero₂₁, Matrix.charpoly_transpose, sq]

lemma det_fin_four {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * A 2 2 * A 3 3 - A 1 1 * A 2 3 * A 3 2 - A 1 2 * A 2 1 * A 3 3 +
               A 1 2 * A 2 3 * A 3 1 + A 1 3 * A 2 1 * A 3 2 - A 1 3 * A 2 2 * A 3 1) -
      A 0 1 * (A 1 0 * A 2 2 * A 3 3 - A 1 0 * A 2 3 * A 3 2 - A 1 2 * A 2 0 * A 3 3 +
               A 1 2 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 2 - A 1 3 * A 2 2 * A 3 0) +
      A 0 2 * (A 1 0 * A 2 1 * A 3 3 - A 1 0 * A 2 3 * A 3 1 - A 1 1 * A 2 0 * A 3 3 +
               A 1 1 * A 2 3 * A 3 0 + A 1 3 * A 2 0 * A 3 1 - A 1 3 * A 2 1 * A 3 0) -
      A 0 3 * (A 1 0 * A 2 1 * A 3 2 - A 1 0 * A 2 2 * A 3 1 - A 1 1 * A 2 0 * A 3 2 +
               A 1 1 * A 2 2 * A 3 0 + A 1 2 * A 2 0 * A 3 1 - A 1 2 * A 2 1 * A 3 0) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.submatrix_apply, Matrix.det_fin_three, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Fin.succAbove, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, pow_two]
  norm_num [Fin.lt_iff_val_lt_val]
  ring

lemma det_tr_active4 (q : ℂ) (hq : q ≠ 0) (y0 y1 y2 y3 : ℂ)
    (h1 : y0 + y1 + y2 + y3 = 0) (h2 : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 0) :
    let y : Fin 4 → ℂ := ![y0, y1, y2, y3]
    let M : Matrix (Fin 4) (Fin 4) ℂ :=
      fun i j => (if i = j then (y j) ^ 2 else 0) - (1 / 3 : ℂ) * y i * y j - q⁻¹ * (y j) ^ 2
    let e : ℂ := y0 * y1 * y2 * y3
    M.trace = 0 ∧
    (M * M).trace = -4 * ((1 / 3 : ℂ) - 2 * q⁻¹) * e ∧
    M.det = -((q - 4) / (3 * q)) * e ^ 2 := by
  intro y M e
  have htr : M.trace = 0 := by
    simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_four, M, y, ite_true, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (2 / 3 - q⁻¹) * h2
  have htr2 : (M * M).trace = -4 * ((1 / 3 : ℂ) - 2 * q⁻¹) * e := by
    rw [Matrix.trace, Fin.sum_univ_four]
    simp only [Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
    simp only [M, y, e, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons]
    norm_num
    have hp4 : y0 ^ 4 + y1 ^ 4 + y2 ^ 4 + y3 ^ 4 = -4 * (y0 * y1 * y2 * y3) := by
      have he2 : y0 * y1 + y0 * y2 + y0 * y3 + y1 * y2 + y1 * y3 + y2 * y3 = 0 := by
        linear_combination ((y0 + y1 + y2 + y3) * h1 - h2) / 2
      have hsym : y0 ^ 4 + y1 ^ 4 + y2 ^ 4 + y3 ^ 4 + 4 * (y0 * y1 * y2 * y3) =
          (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) ^ 2 -
          2 * (y0 * y1 + y0 * y2 + y0 * y3 + y1 * y2 + y1 * y3 + y2 * y3) ^ 2 +
          4 * (y0 + y1 + y2 + y3) * (y0 * y1 * y2 + y0 * y1 * y3 + y0 * y2 * y3 + y1 * y2 * y3) := by ring
      linear_combination hsym + (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) * h2 -
        2 * (y0 * y1 + y0 * y2 + y0 * y3 + y1 * y2 + y1 * y3 + y2 * y3) * he2 +
        4 * (y0 * y1 * y2 + y0 * y1 * y3 + y0 * y2 * y3 + y1 * y2 * y3) * h1
    linear_combination (1 / 3 - 2 * q⁻¹) * hp4 +
      (1 / 9 + q⁻¹ ^ 2) * (y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2) * h2 +
      (2 / 3 * q⁻¹ * (y0 ^ 3 + y1 ^ 3 + y2 ^ 3 + y3 ^ 3)) * h1
  have hdet : M.det = -((q - 4) / (3 * q)) * e ^ 2 := by
    let P : Matrix (Fin 4) (Fin 4) ℂ := fun i j => (if i = j then 1 else 0) - q⁻¹
    let B : Matrix (Fin 4) (Fin 4) ℂ := fun i j => (if i = j then (y j) ^ 2 else 0) - (1 / 3 : ℂ) * y i * y j
    have hM_PB : M = P * B := by
      ext i j
      have hBsum : ∑ k : Fin 4, B k j = (y j) ^ 2 := by
        simp only [B, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        have hys : ∑ k : Fin 4, (1 / 3 : ℂ) * y k * y j = 0 := by
          have : ∀ k : Fin 4, (1 / 3 : ℂ) * y k * y j = ((1 / 3 : ℂ) * y j) * y k := fun _ => by ring
          simp_rw [this, ← Finset.mul_sum, Fin.sum_univ_four, y]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          rw [h1, mul_zero]
        rw [hys, sub_zero]
      have hPB : (P * B) i j = B i j - q⁻¹ * ∑ k : Fin 4, B k j := by
        rw [Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_four]
        simp only [P]
        fin_cases i <;> norm_num <;> ring
      rw [hPB, hBsum]
    have hP_det : P.det = (q - 4) / q := by
      rw [det_fin_four]
      simp only [P]
      norm_num
      field_simp [hq]; ring
    have hB_det : B.det = -(1 / 3 : ℂ) * e ^ 2 := by
      rw [det_fin_four]
      simp only [B, y, e]
      norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      ring
    rw [hM_PB, Matrix.det_mul, hP_det, hB_det]
    field_simp [hq]
  exact ⟨htr, htr2, hdet⟩

lemma charpoly_fin4_not_sq {q : ℕ} (hq : 5 ≤ q) (y0 y1 y2 y3 : ℂ)
    (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) (hy2 : y2 ≠ 0) (hy3 : y3 ≠ 0)
    (h1 : y0 + y1 + y2 + y3 = 0) (h2 : y0 ^ 2 + y1 ^ 2 + y2 ^ 2 + y3 ^ 2 = 0) :
    let y : Fin 4 → ℂ := ![y0, y1, y2, y3]
    let M : Matrix (Fin 4) (Fin 4) ℂ :=
      fun i j => (if i = j then (y j) ^ 2 else 0) - (1 / 3 : ℂ) * y i * y j - (q : ℂ)⁻¹ * (y j) ^ 2
    ¬ ∃ g : Polynomial ℂ, M.charpoly = g ^ 2 := by
  intro y M ⟨g, hg⟩
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  obtain ⟨htr, htr2, hdet⟩ := det_tr_active4 (q : ℂ) hq0 y0 y1 y2 y3 h1 h2
  have hg_deg : g.natDegree = 2 := by
    have hM_deg : M.charpoly.natDegree = 4 := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    have hsq_deg : (g ^ 2).natDegree = 2 * g.natDegree := Polynomial.natDegree_pow g 2
    rw [hg, hsq_deg] at hM_deg; omega
  have hg_lead : g.leadingCoeff ^ 2 = 1 := by
    have hmon := M.charpoly_monic
    rw [hg] at hmon
    simpa [Polynomial.Monic, Polynomial.leadingCoeff_pow] using hmon
  let c0 := g.coeff 0; let c1 := g.coeff 1; let c2 := g.coeff 2
  have hg_eq : g = Polynomial.C c2 * Polynomial.X ^ 2 + Polynomial.C c1 * Polynomial.X + Polynomial.C c0 := by
    ext d
    rcases lt_or_ge d 3 with hd | hd
    · interval_cases d <;> simp [c0, c1, c2, Polynomial.coeff_X_pow]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < d)]
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C,
        show d ≠ 2 by omega, show 1 ≠ d by omega, show d ≠ 0 by omega]
  have hc2_sq : c2 ^ 2 = 1 := by
    have : c2 = g.leadingCoeff := by simp [c2, Polynomial.leadingCoeff, hg_deg]
    rw [this]; exact hg_lead
  have hc3 : M.charpoly.coeff 3 = 2 * c2 * c1 := by
    rw [hg, hg_eq, sq]
    simp [Polynomial.coeff_add, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    ring
  have hc2_coeff : M.charpoly.coeff 2 = 2 * c2 * c0 + c1 ^ 2 := by
    rw [hg, hg_eq, sq]
    simp [Polynomial.coeff_add, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    ring
  have hc0_coeff : M.charpoly.coeff 0 = c0 ^ 2 := by
    rw [hg, hg_eq, sq]
    simp [Polynomial.coeff_add, Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    ring
  have hM_c3 : M.charpoly.coeff 3 = -M.trace := by
    have hdet_eq : M.charpoly = (Matrix.scalar (Fin 4) Polynomial.X - M.map Polynomial.C).det := rfl
    rw [hdet_eq, det_fin_four]
    simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply,
      Matrix.trace, Matrix.diag, Fin.sum_univ_four]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_succ, Polynomial.coeff_X, Polynomial.coeff_C]
    ring
  have hM_c0 : M.charpoly.coeff 0 = M.det := by
    have hdet_eq : M.charpoly = (Matrix.scalar (Fin 4) Polynomial.X - M.map Polynomial.C).det := rfl
    rw [hdet_eq, det_fin_four, det_fin_four]
    simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_succ, Polynomial.coeff_X, Polynomial.coeff_C]
    ring
  have hM_c2 : M.charpoly.coeff 2 = (M.trace ^ 2 - (M * M).trace) / 2 := by
    have hdet_eq : M.charpoly = (Matrix.scalar (Fin 4) Polynomial.X - M.map Polynomial.C).det := rfl
    rw [hdet_eq, det_fin_four]
    simp only [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
    norm_num [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_neg, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_succ, Polynomial.coeff_X, Polynomial.coeff_C]
    ring
  have hc1_zero : c1 = 0 := by
    rw [hM_c3, htr, neg_zero] at hc3
    have hc2_ne : c2 ≠ 0 := fun h => by rw [h] at hc2_sq; norm_num at hc2_sq
    have : c2 * c1 = 0 := by linear_combination -hc3 / 2
    exact (mul_eq_zero.1 this).resolve_left hc2_ne
  have he_ne : y0 * y1 * y2 * y3 ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hy0 hy1) hy2) hy3
  have hc0_val : 2 * c2 * c0 = 2 * ((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) * (y0 * y1 * y2 * y3) := by
    rw [hc1_zero] at hc2_coeff
    rw [hM_c2, htr, htr2] at hc2_coeff
    linear_combination -hc2_coeff
  have hsq_eq : c0 ^ 2 = ((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) ^ 2 * (y0 * y1 * y2 * y3) ^ 2 := by
    have h1' : (c2 * c0) ^ 2 = (((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) * (y0 * y1 * y2 * y3)) ^ 2 := by
      have : c2 * c0 = ((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) * (y0 * y1 * y2 * y3) := by linear_combination hc0_val / 2
      rw [this]
    rw [mul_pow, hc2_sq, one_mul, mul_pow] at h1'
    exact h1'
  rw [hM_c0, hdet] at hc0_coeff
  have hcontra : -(((q : ℂ) - 4) / (3 * (q : ℂ))) * (y0 * y1 * y2 * y3) ^ 2 =
      ((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) ^ 2 * (y0 * y1 * y2 * y3) ^ 2 :=
    hc0_coeff.trans hsq_eq
  have hfrac : -(((q : ℂ) - 4) / (3 * (q : ℂ))) = ((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) ^ 2 :=
    mul_right_cancel₀ (pow_ne_zero 2 he_ne) hcontra
  have hq3 : ((q : ℂ) - 3) ^ 2 = 0 := by
    have hmul : 9 * (q : ℂ) ^ 2 * (-(((q : ℂ) - 4) / (3 * (q : ℂ)))) =
        9 * (q : ℂ) ^ 2 * (((1 / 3 : ℂ) - 2 * (q : ℂ)⁻¹) ^ 2) := congrArg (9 * (q : ℂ) ^ 2 * ·) hfrac
    field_simp [hq0] at hmul
    linear_combination -hmul / 4
  have hq_eq : (q : ℂ) = 3 := sub_eq_zero.1 (sq_eq_zero_iff.1 hq3)
  have hq_nat : q = 3 := by exact_mod_cast hq_eq
  omega

lemma forward_dir {q : ℕ} (hq : 5 ≤ q) (y : Fin q → ℂ)
    (hy1 : ∑ j, y j = 0) (hy2 : ∑ j, (y j) ^ 2 = 0)
    (hcard : ((Finset.univ : Finset (Fin q)).filter (fun j => y j ≠ 0)).card = 4)
    (k : ℕ) (K : Submodule ℂ (Fin q → ℂ)) (hK_dim : Module.finrank ℂ K = k)
    (hK_ok : ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ, permSum x y t = (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) :
    2 * k + 2 ≤ q := by
  have hq1 : 1 ≤ q := by omega
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hK_le : K ≤ H0 q := fun x hx => (hK_ok x hx).1
  let K0 : Submodule ℂ (H0 q) := K.comap (H0 q).subtype
  have hK0_dim : Module.finrank ℂ K0 = k := by
    have hmap : K0.map (H0 q).subtype = K :=
      Submodule.map_comap_eq_self (by rw [Submodule.range_subtype]; exact hK_le)
    rw [← hK_dim, ← hmap, Submodule.finrank_map_subtype_eq]
  have hK0_iso : ∀ u ∈ K0, ∀ v ∈ K0, formA q u v = 0 ∧ formA q (opT hq1 y u) v = 0 := by
    have hdiag : ∀ u ∈ K0, formA q u u = 0 ∧ formA q (opT hq1 y u) u = 0 := by
      intro u hu
      have h := (permSum_iff hq u.2 hy1 hy2).1 (hK_ok u.1 hu).2
      refine ⟨?_, ?_⟩
      · simpa [formA, LinearMap.mk₂_apply, dot, sq] using h.1
      · rw [formA_opT]; simpa [dot, sq, mul_assoc, mul_comm, mul_left_comm] using h.2
    intro u hu v hv
    have huv := hdiag (u + v) (Submodule.add_mem K0 hu hv)
    have hu0 := hdiag u hu
    have hv0 := hdiag v hv
    refine ⟨?_, ?_⟩
    · have h1 : formA q (u + v) (u + v) = formA q u u + 2 * formA q u v + formA q v v := by
        simp only [map_add, LinearMap.add_apply]; rw [formA_symm v u]; ring
      rw [huv.1, hu0.1, hv0.1] at h1; linear_combination -h1 / 2
    · have h1 : formA q (opT hq1 y (u + v)) (u + v) =
          formA q (opT hq1 y u) u + 2 * formA q (opT hq1 y u) v + formA q (opT hq1 y v) v := by
        simp only [map_add, LinearMap.add_apply]; rw [opT_selfAdj hq1 y v u, formA_symm v]; ring
      rw [huv.2, hu0.2, hv0.2] at h1; linear_combination -h1 / 2
  have h2k_le : 2 * k ≤ q - 1 := by
    have : Module.Free ℂ K0 := Module.Free.of_divisionRing ℂ K0
    let bK0 := Module.finBasis ℂ K0
    let Φ : H0 q →ₗ[ℂ] (Fin (Module.finrank ℂ K0) → ℂ) :=
      { toFun := fun w i => formA q w (bK0 i).1
        map_add' := fun w1 w2 => by funext i; simp
        map_smul' := fun c w => by funext i; simp }
    have hle : K0 ≤ LinearMap.ker Φ := fun u hu => by
      rw [LinearMap.mem_ker]; funext i; exact (hK0_iso u hu (bK0 i).1 (bK0 i).2).1
    have hΦ_surj : Function.Surjective Φ := by
      intro z
      obtain ⟨K0', hK0'⟩ := Submodule.exists_isCompl K0
      let fK : K0 →ₗ[ℂ] ℂ := bK0.constr ℂ z
      let fV : H0 q →ₗ[ℂ] ℂ := fK.comp ((LinearMap.fst ℂ K0 K0').comp (Submodule.prodEquivOfIsCompl K0 K0' hK0').symm.toLinearMap)
      have hfV : ∀ i : Fin (Module.finrank ℂ K0), fV (bK0 i).1 = z i := by
        intro i
        have h1 : (Submodule.prodEquivOfIsCompl K0 K0' hK0').symm (bK0 i).1 = (bK0 i, 0) := by
          apply (Submodule.prodEquivOfIsCompl K0 K0' hK0').injective
          rw [LinearEquiv.apply_symm_apply]
          change (bK0 i).1 = (bK0 i).1 + (0 : K0').1
          simp
        change fK (LinearMap.fst ℂ K0 K0' ((Submodule.prodEquivOfIsCompl K0 K0' hK0').symm (bK0 i).1)) = z i
        rw [h1]
        simp [fK]
      let Ψ : H0 q →ₗ[ℂ] Module.Dual ℂ (H0 q) := formA q
      have hΨ_inj : Function.Injective Ψ := by
        rw [injective_iff_map_eq_zero]
        intro u hu; exact formA_nondeg hq1 fun v => LinearMap.ext_iff.1 hu v
      have hΨ_surj : Function.Surjective Ψ := by
        have hr := LinearMap.finrank_range_add_finrank_ker Ψ
        rw [LinearMap.ker_eq_bot.2 hΨ_inj, finrank_bot, add_zero] at hr
        have htop : LinearMap.range Ψ = ⊤ :=
          Submodule.eq_top_of_finrank_eq (hr.trans Subspace.dual_finrank_eq.symm)
        intro f; have : f ∈ LinearMap.range Ψ := by rw [htop]; trivial
        exact this
      obtain ⟨w, hw⟩ := hΨ_surj fV
      refine ⟨w, ?_⟩
      funext i
      change formA q w (bK0 i).1 = z i
      rw [show formA q w (bK0 i).1 = Ψ w (bK0 i).1 from rfl, hw, hfV i]
    have hr := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.2 hΦ_surj, finrank_top, Module.finrank_fin_fun, finrank_H0 hq1] at hr
    have hker_ge : k ≤ Module.finrank ℂ (LinearMap.ker Φ) := by
      rw [← hK0_dim]; exact Submodule.finrank_mono hle
    omega
  by_contra hgt
  have h2k_eq : 2 * k = q - 1 := by omega
  obtain ⟨gAll, hgAll⟩ := charpoly_eq_sq_of_lagrangian (formA q) (opT hq1 y)
    formA_symm (fun _ => formA_nondeg hq1) (opT_selfAdj hq1 y) K0 (by rw [hK0_dim, finrank_H0 hq1, h2k_eq]) hK0_iso

  let S := (Finset.univ : Finset (Fin q)).filter (fun j => y j ≠ 0)
  have hScard : S.card = 4 := hcard
  let eS : Fin 4 ≃ {j : Fin q // j ∈ S} := (S.equivFin.trans (finCongr hScard)).symm
  let idx : Fin 4 → Fin q := fun i => (eS i).1
  have hidx_inj : Function.Injective idx := fun i j h => eS.injective (Subtype.ext h)
  have hidx_mem : ∀ i : Fin 4, y (idx i) ≠ 0 := fun i => (Finset.mem_filter.1 (eS i).2).2
  have hidx_out : ∀ j : Fin q, (∀ i : Fin 4, j ≠ idx i) → y j = 0 := by
    intro j hj
    by_contra hne
    have hmem : j ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ j, hne⟩
    exact hj (eS.symm ⟨j, hmem⟩) (by simp [idx])
  have hy_sum4 : y (idx 0) + y (idx 1) + y (idx 2) + y (idx 3) = 0 := by
    have hS_eq : S = Finset.univ.image idx := by
      ext j; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hj; exact ⟨eS.symm ⟨j, hj⟩, by simp [idx]⟩
      · rintro ⟨i, rfl⟩; exact (eS i).2
    have hsum : ∑ j ∈ S, y j = 0 := by
      rw [← hy1]
      refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_
      simp [S] at hj; exact hj
    rw [hS_eq, Finset.sum_image (fun i _ j _ h => hidx_inj h), Fin.sum_univ_four] at hsum
    exact hsum
  have hy2_sum4 : y (idx 0) ^ 2 + y (idx 1) ^ 2 + y (idx 2) ^ 2 + y (idx 3) ^ 2 = 0 := by
    have hS_eq : S = Finset.univ.image idx := by
      ext j; simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · intro hj; exact ⟨eS.symm ⟨j, hj⟩, by simp [idx]⟩
      · rintro ⟨i, rfl⟩; exact (eS i).2
    have hsum : ∑ j ∈ S, (y j) ^ 2 = 0 := by
      rw [← hy2]
      refine Finset.sum_subset (Finset.subset_univ S) fun j _ hj => ?_
      have : y j = 0 := by simp [S] at hj; exact hj
      simp [this]
    rw [hS_eq, Finset.sum_image (fun i _ j _ h => hidx_inj h), Fin.sum_univ_four] at hsum
    exact hsum

  let vAct : Fin 4 → H0 q := fun i =>
    ⟨fun j => (if j = idx i then (1 : ℂ) else 0) - (q : ℂ)⁻¹, by
      change ∑ j : Fin q, ((if j = idx i then (1 : ℂ) else 0) - (q : ℂ)⁻¹) = 0
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), Finset.sum_const,
        Finset.card_fin, nsmul_eq_mul, mul_inv_cancel₀ hq0, sub_self]⟩
  let W_inact : Submodule ℂ (H0 q) :=
    { carrier := {u | ∀ i : Fin 4, u.1 (idx i) = 0}, add_mem' := fun {u v} hu hv i => by simp [hu i, hv i]
      zero_mem' := fun _ => rfl
      smul_mem' := fun c {u} hu i => by simp [hu i] }
  let W_act : Submodule ℂ (H0 q) := Submodule.span ℂ (Set.range vAct)
  have hWinact_T : ∀ u : H0 q, u ∈ W_inact → opT hq1 y u = 0 := by
    intro u hu
    apply Subtype.ext; funext j
    have hyu : ∀ r : Fin q, y r * u.1 r = 0 := by
      intro r
      by_cases hr : r ∈ S
      · have : r = idx (eS.symm ⟨r, hr⟩) := by simp [idx]
        rw [this, hu, mul_zero]
      · have : y r = 0 := by simpa [S] using hr
        rw [this, zero_mul]
    have hdot0 : dot y u.1 = 0 := Finset.sum_eq_zero fun r _ => hyu r
    have hraw0 : ∀ r : Fin q, (y r) ^ 2 * u.1 r - (1 / 3 : ℂ) * dot y u.1 * y r = 0 := by
      intro r; rw [hdot0, mul_zero, zero_mul, sub_zero, sq, mul_assoc, hyu r, mul_zero]
    simp only [opT, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_zero, Pi.zero_apply, hraw0,
      Finset.sum_const_zero, mul_zero, sub_self]
  let M : Matrix (Fin 4) (Fin 4) ℂ :=
    fun i j => (if i = j then (y (idx j)) ^ 2 else 0) - (1 / 3 : ℂ) * y (idx i) * y (idx j) - (q : ℂ)⁻¹ * (y (idx i)) ^ 2
  have hWact_T : ∀ j : Fin 4, opT hq1 y (vAct j) = ∑ i : Fin 4, M i j • vAct i := by
    intro j
    apply Subtype.ext; funext r
    have hdot_vj : dot y (vAct j).1 = y (idx j) := by
      simp only [dot, vAct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul, hy1, zero_mul, sub_zero]
    have hraw_sum : ∑ l : Fin q, ((y l) ^ 2 * (vAct j).1 l - (1 / 3 : ℂ) * dot y (vAct j).1 * y l) =
        (y (idx j)) ^ 2 := by
      simp only [hdot_vj, vAct, Finset.sum_sub_distrib, ← Finset.mul_sum, hy1, mul_zero, sub_zero,
        mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        ← Finset.sum_mul, hy2, zero_mul]
    have hM_sum : ∑ i : Fin 4, M i j = (y (idx j)) ^ 2 := by
      simp only [M, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      have h0 : ∑ i : Fin 4, (1 / 3 : ℂ) * y (idx i) * y (idx j) = 0 := by
        have : ∀ i : Fin 4, (1 / 3 : ℂ) * y (idx i) * y (idx j) = ((1 / 3 : ℂ) * y (idx j)) * y (idx i) := fun _ => by ring
        simp_rw [this, ← Finset.mul_sum, Fin.sum_univ_four, hy_sum4, mul_zero]
      have h2 : ∑ i : Fin 4, (q : ℂ)⁻¹ * (y (idx i)) ^ 2 = 0 := by
        rw [← Finset.mul_sum, Fin.sum_univ_four, hy2_sum4, mul_zero]
      rw [h0, h2, sub_zero, sub_zero]
    change ((y r) ^ 2 * (vAct j).1 r - (1 / 3 : ℂ) * dot y (vAct j).1 * y r) -
        (q : ℂ)⁻¹ * (∑ l : Fin q, ((y l) ^ 2 * (vAct j).1 l - (1 / 3 : ℂ) * dot y (vAct j).1 * y l)) =
        (∑ i : Fin 4, M i j • vAct i).1 r
    rw [hraw_sum, hdot_vj]
    simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      vAct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ← Finset.sum_mul, hM_sum]
    by_cases hr : ∃ i : Fin 4, r = idx i
    · obtain ⟨i, rfl⟩ := hr
      have hite : ∑ i' : Fin 4, (if idx i = idx i' then M i' j else 0) = M i j := by
        have : ∀ i' : Fin 4, (if idx i = idx i' then M i' j else 0) = if i' = i then M i j else 0 := by
          intro i'
          by_cases h : i' = i
          · subst h; simp
          · have hne : idx i ≠ idx i' := fun heq => h (hidx_inj heq.symm)
            simp [h, hne]
        simp [this]
      rw [hite]
      by_cases hij : i = j
      · subst hij; simp only [M, ite_true]; ring
      · have hne : idx i ≠ idx j := fun heq => hij (hidx_inj heq)
        simp only [M, ite_eq_right hij, ite_eq_right hne]; ring
    · push Not at hr
      have hyr : y r = 0 := hidx_out r hr
      have hite2 : ∑ i' : Fin 4, (if r = idx i' then M i' j else 0) = 0 :=
        Finset.sum_eq_zero fun i' _ => if_neg (hr i')
      rw [hyr, hite2]
      simp only [zero_pow (by norm_num : 2 ≠ 0), ite_self, zero_mul, mul_zero, sub_zero, zero_sub]
      ring

  have hvAct_li : LinearIndependent ℂ vAct := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h_not_in : ∃ r : Fin q, ∀ i : Fin 4, r ≠ idx i := by
      have hne : S ≠ Finset.univ := by
        intro heq; have := congrArg Finset.card heq; rw [hScard, Finset.card_fin] at this; omega
      obtain ⟨r, hr⟩ : ∃ r : Fin q, r ∉ S := by
        by_contra hall; push Not at hall; exact hne (Finset.eq_univ_iff_forall.2 hall)
      exact ⟨r, fun i hi => hr (hi ▸ (eS i).2)⟩
    obtain ⟨r, hr⟩ := h_not_in
    have hsum0 : ∑ i : Fin 4, c i = 0 := by
      have h := congrFun (congrArg Subtype.val hc) r
      simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Submodule.coe_zero, Pi.zero_apply, vAct, hr, ite_false, zero_sub, mul_neg, Finset.sum_neg_distrib,
        ← Finset.sum_mul, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_right (inv_ne_zero hq0)
    intro i
    have h := congrFun (congrArg Subtype.val hc) (idx i)
    simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Submodule.coe_zero, Pi.zero_apply, vAct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      ← Finset.sum_mul, hsum0, zero_mul, sub_zero] at h
    have hite : ∑ i' : Fin 4, (if idx i = idx i' then c i' else 0) = c i := by
      have : ∀ i' : Fin 4, (if idx i = idx i' then c i' else 0) = if i' = i then c i else 0 := by
        intro i'; by_cases he : i' = i
        · subst he; simp
        · have hne : idx i ≠ idx i' := fun heq => he (hidx_inj heq.symm)
          simp [he, hne]
      simp [this]
    rw [hite] at h; exact h
  have hcompl : IsCompl W_act W_inact := by
    rw [isCompl_iff]
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro u ⟨hu1, hu2⟩
      change u ∈ Submodule.span ℂ (Set.range vAct) at hu1
      rw [Submodule.mem_span_range_iff_exists_fun] at hu1
      obtain ⟨c, rfl⟩ := hu1
      have hsum4 : ∀ i : Fin 4, c i = (q : ℂ)⁻¹ * ∑ j : Fin 4, c j := by
        intro i
        have hi := hu2 i
        simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          vAct, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, ← Finset.sum_mul] at hi
        have hite : ∑ i' : Fin 4, (if idx i = idx i' then c i' else 0) = c i := by
          have : ∀ i' : Fin 4, (if idx i = idx i' then c i' else 0) = if i' = i then c i else 0 := by
            intro i'; by_cases he : i' = i
            · subst he; simp
            · have hne : idx i ≠ idx i' := fun heq => he (hidx_inj heq.symm)
              simp [he, hne]
          simp [this]
        rw [hite] at hi; linear_combination hi
      have hsum0 : ∑ i : Fin 4, c i = 0 := by
        have h := Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hsum4 i
        simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h
        have hq4 : (q : ℂ) - 4 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by omega : q ≠ 4))
        have h' : (q : ℂ) * (∑ i : Fin 4, c i) = 4 * (∑ i : Fin 4, c i) := by
          have hcast : (∑ i : Fin 4, c i) = 4 * ((q : ℂ)⁻¹ * ∑ j : Fin 4, c j) := by simpa using h
          calc (q : ℂ) * (∑ i : Fin 4, c i)
              = (q : ℂ) * (4 * ((q : ℂ)⁻¹ * ∑ j : Fin 4, c j)) := by rw [← hcast]
            _ = 4 * ∑ j : Fin 4, c j := by field_simp [hq0]
        have hmul : ((q : ℂ) - 4) * (∑ i : Fin 4, c i) = 0 := by linear_combination h'
        exact (mul_eq_zero.1 hmul).resolve_left hq4
      have hc0 : ∀ i : Fin 4, c i = 0 := fun i => by rw [hsum4 i, hsum0, mul_zero]
      simp [hc0]
    · rw [codisjoint_iff, eq_top_iff]
      intro u _
      let s := ∑ i : Fin 4, u.1 (idx i)
      let c : Fin 4 → ℂ := fun i => u.1 (idx i) + ((q : ℂ) - 4)⁻¹ * s
      have hq4 : (q : ℂ) - 4 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by omega : q ≠ 4))
      have hc_sum : ∑ i : Fin 4, c i = (q : ℂ) * ((q : ℂ) - 4)⁻¹ * s := by
        simp only [c, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        dsimp only [s]
        field_simp [hq4]; ring
      let u1 : H0 q := ∑ i : Fin 4, c i • vAct i
      have hu1 : u1 ∈ W_act := Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hu2 : u - u1 ∈ W_inact := by
        intro i
        simp only [Submodule.coe_sub, Pi.sub_apply, u1, Submodule.coe_sum, SetLike.val_smul,
          Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vAct, mul_sub, Finset.sum_sub_distrib,
          mul_ite, mul_one, mul_zero, ← Finset.sum_mul, hc_sum]
        have hite : ∑ i' : Fin 4, (if idx i = idx i' then c i' else 0) = c i := by
          have : ∀ i' : Fin 4, (if idx i = idx i' then c i' else 0) = if i' = i then c i else 0 := by
            intro i'; by_cases he : i' = i
            · subst he; simp
            · have hne : idx i ≠ idx i' := fun heq => he (hidx_inj heq.symm)
              simp [he, hne]
          simp [this]
        rw [hite]; simp only [c]; field_simp [hq0, hq4]; ring
      have heq : u = u1 + (u - u1) := by abel
      rw [heq]; exact Submodule.add_mem_sup hu1 hu2
  let m := Module.finrank ℂ W_inact
  have hm_eq : m = q - 5 := by
    have hact_dim : Module.finrank ℂ W_act = 4 := by rw [finrank_span_eq_card hvAct_li, Fintype.card_fin]
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq W_act W_inact
    rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot, finrank_H0 hq1, hact_dim] at hsum
    dsimp only [m]; omega
  haveI : Module.Free ℂ W_inact := Module.Free.of_divisionRing ℂ W_inact
  let bIn := Module.finBasis ℂ W_inact
  let bAll : Fin 4 ⊕ Fin m → H0 q := Sum.elim vAct (fun i => (bIn i).1)
  have hbAll_li : LinearIndependent ℂ bAll := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : (∑ i : Fin 4, c (Sum.inl i) • vAct i) + (∑ j : Fin m, c (Sum.inr j) • (bIn j).1) = 0 := by
      simpa [Fintype.sum_sum_type, bAll] using hc
    have hm1 : (∑ i : Fin 4, c (Sum.inl i) • vAct i) ∈ W_act :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hm2 : (∑ j : Fin m, c (Sum.inr j) • (bIn j).1) ∈ W_inact :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bIn j).2
    have hneg : (∑ i : Fin 4, c (Sum.inl i) • vAct i) = -(∑ j : Fin m, c (Sum.inr j) • (bIn j).1) :=
      eq_neg_of_add_eq_zero_left h1
    have hzero1 : ∑ i : Fin 4, c (Sum.inl i) • vAct i = 0 := by
      have hmem : (∑ i : Fin 4, c (Sum.inl i) • vAct i) ∈ W_act ⊓ W_inact :=
        ⟨hm1, hneg ▸ Submodule.neg_mem _ hm2⟩
      rw [hcompl.inf_eq_bot, Submodule.mem_bot] at hmem; exact hmem
    have hzero2 : ∑ j : Fin m, c (Sum.inr j) • (bIn j).1 = 0 := by rw [hzero1, zero_add] at h1; exact h1
    have hc1 := Fintype.linearIndependent_iff.1 hvAct_li (fun i => c (Sum.inl i)) hzero1
    have hzero2_sub : ∑ j : Fin m, c (Sum.inr j) • bIn j = 0 :=
      Subtype.ext (by simpa [Submodule.coe_sum] using hzero2)
    have hc2 : ∀ j : Fin m, c (Sum.inr j) = 0 := fun j => by
      have h := congrArg (fun v => (bIn.repr.toLinearMap v) j) hzero2_sub
      rw [map_zero, map_sum] at h
      simp [Finsupp.single_apply] at h
      exact h
    intro s; rcases s with i | j; exact hc1 i; exact hc2 j
  have hbAll_card : Fintype.card (Fin 4 ⊕ Fin m) = Module.finrank ℂ (H0 q) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, hm_eq, finrank_H0 hq1]; omega
  let BAll : Module.Basis (Fin 4 ⊕ Fin m) ℂ (H0 q) := basisOfLinearIndependentOfCardEqFinrank hbAll_li hbAll_card
  have hT_mat : LinearMap.toMatrix BAll BAll (opT hq1 y) = Matrix.fromBlocks M 0 0 0 := by
    ext s t
    have hB_inl : ∀ i : Fin 4, BAll (Sum.inl i) = vAct i := fun _ => by
      simp [BAll, coe_basisOfLinearIndependentOfCardEqFinrank, bAll]
    have hB_inr : ∀ j : Fin m, BAll (Sum.inr j) = (bIn j).1 := fun _ => by
      simp [BAll, coe_basisOfLinearIndependentOfCardEqFinrank, bAll]
    rcases t with j | j
    · have hrep : BAll.repr (opT hq1 y (BAll (Sum.inl j))) =
          Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => M i j) 0) := by
        apply BAll.repr.symm.injective
        rw [LinearEquiv.symm_apply_apply, hB_inl j, hWact_T j, Module.Basis.repr_symm_apply,
          Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ (fun i a => a • BAll i) (fun i => zero_smul ℂ (BAll i))]
        simp [Fintype.sum_sum_type, hB_inl, hB_inr]
      rw [LinearMap.toMatrix_apply, hrep]
      rcases s with i | i <;> simp
    · have h0 : opT hq1 y (BAll (Sum.inr j)) = 0 := by rw [hB_inr j]; exact hWinact_T _ (bIn j).2
      rw [LinearMap.toMatrix_apply, h0, map_zero]
      rcases s with i | i <;> simp
  have hcp : (opT hq1 y).charpoly = M.charpoly * Polynomial.X ^ m := by
    rw [← LinearMap.charpoly_toMatrix (opT hq1 y) BAll, hT_mat, Matrix.charpoly_fromBlocks_zero₂₁]
    congr 1
    simp [Matrix.charpoly, Matrix.det_diagonal]
  rw [hcp] at hgAll

  have hm_even : ∃ r : ℕ, m = 2 * r := ⟨k - 2, by omega⟩
  obtain ⟨r, hr⟩ := hm_even
  rw [hr] at hgAll
  have hX_div : Polynomial.X ^ r ∣ gAll := by
    have h1 : Polynomial.X ^ (2 * r) ∣ gAll ^ 2 := by
      rw [← hgAll]; exact dvd_mul_left _ _
    have hgen : ∀ (n : ℕ) (p : Polynomial ℂ), Polynomial.X ^ (2 * n) ∣ p ^ 2 → Polynomial.X ^ n ∣ p := by
      intro n
      induction n with
      | zero => intro p _; simp
      | succ n ihn =>
        intro p hp
        have hX2 : Polynomial.X ∣ p ^ 2 := dvd_trans ⟨Polynomial.X ^ (2 * n + 1), by ring⟩ hp
        have hcoeff0 : p.coeff 0 = 0 := by
          have h0 : (p ^ 2).coeff 0 = 0 := Polynomial.X_dvd_iff.1 hX2
          rw [sq, Polynomial.mul_coeff_zero] at h0
          exact mul_self_eq_zero.1 h0
        obtain ⟨p', rfl⟩ := Polynomial.X_dvd_iff.2 hcoeff0
        have hp' : Polynomial.X ^ (2 * n) ∣ p' ^ 2 := by
          obtain ⟨q', hq'⟩ := hp
          refine ⟨q', ?_⟩
          have h2 : Polynomial.X ^ 2 * p' ^ 2 = Polynomial.X ^ 2 * (Polynomial.X ^ (2 * n) * q') := by
            calc Polynomial.X ^ 2 * p' ^ 2 = (Polynomial.X * p') ^ 2 := by ring
              _ = Polynomial.X ^ (2 * (n + 1)) * q' := hq'
              _ = Polynomial.X ^ 2 * (Polynomial.X ^ (2 * n) * q') := by ring
          exact mul_left_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) h2
        obtain ⟨u', hu'⟩ := ihn p' hp'
        refine ⟨u', ?_⟩
        rw [hu']; ring
    exact hgen r gAll h1
  obtain ⟨g, rfl⟩ := hX_div
  have hM_sq : M.transpose.charpoly = g ^ 2 := by
    have h1 : M.charpoly * Polynomial.X ^ (2 * r) = g ^ 2 * Polynomial.X ^ (2 * r) := by
      rw [hgAll]; ring
    have h2 : M.charpoly = g ^ 2 := mul_right_cancel₀ (pow_ne_zero (2 * r) Polynomial.X_ne_zero) h1
    rw [Matrix.charpoly_transpose]; exact h2
  have hMt_eq : M.transpose =
      fun i j => (if i = j then (![y (idx 0), y (idx 1), y (idx 2), y (idx 3)] j) ^ 2 else 0) -
        (1 / 3 : ℂ) * ![y (idx 0), y (idx 1), y (idx 2), y (idx 3)] i * ![y (idx 0), y (idx 1), y (idx 2), y (idx 3)] j -
        (q : ℂ)⁻¹ * (![y (idx 0), y (idx 1), y (idx 2), y (idx 3)] j) ^ 2 := by
    ext i j
    rw [Matrix.transpose_apply]
    simp only [M]
    fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> ring
  rw [hMt_eq] at hM_sq
  exact charpoly_fin4_not_sq hq (y (idx 0)) (y (idx 1)) (y (idx 2)) (y (idx 3))
    (hidx_mem 0) (hidx_mem 1) (hidx_mem 2) (hidx_mem 3) hy_sum4 hy2_sum4 ⟨g, hM_sq⟩

lemma backward_dir {q : ℕ} (hq : 5 ≤ q) (y : Fin q → ℂ)
    (hy1 : ∑ j, y j = 0) (hy2 : ∑ j, (y j) ^ 2 = 0)
    (k : ℕ) (hk : 2 * k + 2 ≤ q) :
    ∃ K : Submodule ℂ (Fin q → ℂ), Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ, permSum x y t = (Fintype.card (Fin 4 ↪ Fin q) : ℂ) := by
  have hq1 : 1 ≤ q := by omega
  obtain ⟨K0, hK0_dim, hK0_iso⟩ := exists_iso_subspace k (formA q) (opT hq1 y)
    formA_symm (fun _ => formA_nondeg hq1) (opT_selfAdj hq1 y) (by rw [finrank_H0 hq1]; omega)
  let K : Submodule ℂ (Fin q → ℂ) := K0.map (H0 q).subtype
  refine ⟨K, ?_, ?_⟩
  · rw [Submodule.finrank_map_subtype_eq, hK0_dim]
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, ?_⟩
    change ∀ t : ℂ, permSum u.1 y t = (Fintype.card (Fin 4 ↪ Fin q) : ℂ)
    rw [permSum_iff hq u.2 hy1 hy2]
    have h := hK0_iso u hu u hu
    refine ⟨?_, ?_⟩
    · simpa [formA, LinearMap.mk₂_apply, dot, sq] using h.1
    · rw [formA_opT] at h; simpa [dot, sq, mul_assoc, mul_comm, mul_left_comm] using h.2

end PEqualNP.Outside.L_gct_297

theorem PEqualNP.Outside.L_gct_297 : (∀ (q : ℕ), 5 ≤ q → ∀ (y : Fin q → ℂ),
  (∑ j, y j) = 0 → (∑ j, (y j)^2) = 0 →
  ((Finset.univ : Finset (Fin q)).filter (fun j => y j ≠ 0)).card = 4 →
  ∀ k : ℕ,
    (∃ K : Submodule ℂ (Fin q → ℂ), Module.finrank ℂ K = k ∧
      ∀ x ∈ K, (∑ j, x j) = 0 ∧ ∀ t : ℂ,
        let rows : Fin 4 → Fin q → ℂ := ![x, -x, t • y, -(t • y)]
        (∑ f : Fin 4 ↪ Fin q, ∏ i : Fin 4, (1 + rows i (f i))) =
          (Fintype.card (Fin 4 ↪ Fin q) : ℂ)) ↔ 2*k + 2 ≤ q) := by
  intro q hq y hy1 hy2 hcard k
  constructor
  · rintro ⟨K, hK_dim, hK_ok⟩
    exact PEqualNP.Outside.L_gct_297.forward_dir hq y hy1 hy2 hcard k K hK_dim hK_ok
  · intro hk
    exact PEqualNP.Outside.L_gct_297.backward_dir hq y hy1 hy2 k hk
