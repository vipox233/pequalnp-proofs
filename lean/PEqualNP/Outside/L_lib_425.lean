import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_425

def sg (b : ZMod 2) : ℤ := if b = 0 then 1 else -1

lemma sg_add (u v : ZMod 2) : sg (u + v) = sg u * sg v := by
  fin_cases u <;> fin_cases v <;> decide

lemma sg_self (u : ZMod 2) : sg u * sg u = 1 := by
  fin_cases u <;> decide

lemma sg_one : sg 1 = -1 := by decide

lemma two_self {k : ℕ} (v : Fin k → ZMod 2) : v + v = 0 :=
  funext fun i => by simp [CharTwo.add_self_eq_zero (v i)]

lemma neg_self {k : ℕ} (v : Fin k → ZMod 2) : -v = v :=
  funext fun i => by simp [ZMod.neg_eq_self_mod_two (v i)]

lemma card_cube (k : ℕ) : (Fintype.card (Fin k → ZMod 2) : ℤ) = 2 ^ k := by
  simp [ZMod.card]

lemma orth {k : ℕ} (v : Fin k → ZMod 2) :
    ∑ a : Fin k → ZMod 2, sg (dotProduct a v) = if v = 0 then 2 ^ k else 0 := by
  split_ifs with hv
  · subst hv
    simp only [dotProduct_zero]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
    simp [sg]
  · obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hvi : v i = 1 := by
      rcases (show ∀ t : ZMod 2, t = 0 ∨ t = 1 by decide) (v i) with h | h
      · exact absurd h hi
      · exact h
    have key : ∑ a : Fin k → ZMod 2, sg (dotProduct a v)
        = -∑ a : Fin k → ZMod 2, sg (dotProduct a v) := by
      calc ∑ a : Fin k → ZMod 2, sg (dotProduct a v)
          = ∑ a : Fin k → ZMod 2, sg (dotProduct (a + Pi.single i 1) v) := by
            rw [← Equiv.sum_comp (Equiv.addRight (Pi.single i (1 : ZMod 2)))]
            rfl
        _ = ∑ a : Fin k → ZMod 2, -sg (dotProduct a v) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [add_dotProduct, single_dotProduct, hvi, one_mul, sg_add, sg_one]
            ring
        _ = -∑ a : Fin k → ZMod 2, sg (dotProduct a v) := Finset.sum_neg_distrib _
    linarith

lemma orth2 {k : ℕ} (u v : Fin k → ZMod 2) :
    ∑ a : Fin k → ZMod 2, sg (dotProduct a u) * sg (dotProduct a v)
      = if u = v then 2 ^ k else 0 := by
  simp_rw [← sg_add, ← dotProduct_add]
  rw [orth]
  have key : (u + v = 0) ↔ (u = v) := by rw [add_eq_zero_iff_eq_neg, neg_self]
  exact if_congr key rfl rfl

lemma parseval {n m : ℕ} (H : (Fin n → ZMod 2) × (Fin m → ZMod 2) → ℤ) :
    ∑ a : Fin n → ZMod 2, ∑ b : Fin m → ZMod 2,
      (∑ p, H p * (sg (dotProduct a p.1) * sg (dotProduct b p.2))) ^ 2
      = 2 ^ n * 2 ^ m * ∑ p, H p ^ 2 := by
  have step : ∀ a b, (∑ p, H p * (sg (dotProduct a p.1) * sg (dotProduct b p.2))) ^ 2
      = ∑ p, ∑ q, H p * H q * ((sg (dotProduct a p.1) * sg (dotProduct a q.1)) *
          (sg (dotProduct b p.2) * sg (dotProduct b q.2))) := by
    intro a b
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [step]
  calc _ = ∑ a : Fin n → ZMod 2, ∑ p, ∑ q, ∑ b : Fin m → ZMod 2,
        H p * H q * ((sg (dotProduct a p.1) * sg (dotProduct a q.1)) *
          (sg (dotProduct b p.2) * sg (dotProduct b q.2))) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ a : Fin n → ZMod 2, ∑ b : Fin m → ZMod 2,
        H p * H q * ((sg (dotProduct a p.1) * sg (dotProduct a q.1)) *
          (sg (dotProduct b p.2) * sg (dotProduct b q.2))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, H p * H q * (if p = q then 2 ^ n * 2 ^ m else 0) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        simp_rw [← Finset.mul_sum]
        rw [← Finset.sum_mul, orth2, orth2]
        by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]
    _ = 2 ^ n * 2 ^ m * ∑ p, H p ^ 2 := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring

def delta {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (p : (Fin n → ZMod 2) × (Fin m → ZMod 2)) : ℤ :=
  ((Finset.univ.filter (fun x : Fin n → ZMod 2 => F (x + p.1) + F x = p.2)).card : ℤ)

lemma T_sq {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (a : Fin n → ZMod 2) (b : Fin m → ZMod 2) :
    (∑ x, sg (dotProduct a x + dotProduct b (F x))) ^ 2
      = ∑ p, delta F p * (sg (dotProduct a p.1) * sg (dotProduct b p.2)) := by
  rw [sq, Finset.sum_mul_sum]
  have h1 : ∀ x : Fin n → ZMod 2, ∑ y, sg (dotProduct a x + dotProduct b (F x)) *
      sg (dotProduct a y + dotProduct b (F y))
      = ∑ d, sg (dotProduct a d) * sg (dotProduct b (F (x + d) + F x)) := by
    intro x
    rw [← Equiv.sum_comp (Equiv.addLeft x)]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [Equiv.coe_addLeft, sg_add, dotProduct_add]
    linear_combination (sg (dotProduct a d) * sg (dotProduct b (F (x + d))) *
      sg (dotProduct b (F x))) * sg_self (dotProduct a x)
  simp_rw [h1]
  rw [Fintype.sum_prod_type]
  simp only [delta, Finset.natCast_card_filter, Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]
  simp

lemma moment_eq {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    ∑ a : Fin n → ZMod 2, ∑ b : Fin m → ZMod 2,
      (∑ x, sg (dotProduct a x + dotProduct b (F x))) ^ 4
      = 2 ^ n * 2 ^ m * ∑ p, delta F p ^ 2 := by
  rw [← parseval]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← T_sq]
  ring

lemma delta_zero {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (e : Fin m → ZMod 2) :
    delta F (0, e) = if e = 0 then 2 ^ n else 0 := by
  simp only [delta, add_zero, two_self]
  split_ifs with he
  · subst he
    rw [Finset.filter_true_of_mem (fun _ _ => rfl), Finset.card_univ]
    exact card_cube n
  · rw [Finset.filter_false_of_mem (fun _ _ h => he h.symm)]
    simp

lemma delta_row {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (d : Fin n → ZMod 2) :
    ∑ e, delta F (d, e) = 2 ^ n := by
  simp only [delta, Finset.natCast_card_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube, mul_one]

lemma delta_even {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (d : Fin n → ZMod 2)
    (hd : d ≠ 0) (e : Fin m → ZMod 2) :
    Even (Finset.univ.filter (fun x : Fin n → ZMod 2 => F (x + d) + F x = e)).card := by
  rw [← ZMod.natCast_eq_zero_iff_even, ← nsmul_one, ← Finset.sum_const]
  refine Finset.sum_involution (fun x _ => x + d) (fun _ _ => by decide) ?_ ?_ ?_
  · intro x _ _ h
    apply hd
    simpa using h
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [add_assoc, two_self, add_zero, add_comm, hx]
  · intro x _
    rw [add_assoc, two_self, add_zero]

lemma delta_nonneg {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) (p) :
    0 ≤ delta F p := by
  unfold delta
  positivity

lemma term_facts (k : ℕ) (hk : Even k) :
    0 ≤ (k : ℤ) * ((k : ℤ) - 2) ∧ ((k : ℤ) * ((k : ℤ) - 2) = 0 ↔ k ≤ 2) := by
  obtain ⟨j, rfl⟩ := hk
  push_cast
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with h | h
    · subst h; simp
    · have : (1 : ℤ) ≤ j := by exact_mod_cast h
      nlinarith
  · constructor
    · intro h
      have h' : (j : ℤ) * ((j : ℤ) - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp h' with h0 | h0
      · have : j = 0 := by exact_mod_cast h0
        omega
      · have : (j : ℤ) = 1 := by linarith
        have : j = 1 := by exact_mod_cast this
        omega
    · intro h
      have : j ≤ 1 := by omega
      interval_cases j <;> simp

lemma sum_sq {n m : ℕ} (F : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    ∑ p, delta F p ^ 2 = 3 * (2 ^ n) ^ 2 - 2 * 2 ^ n +
      ∑ d ∈ Finset.univ.erase 0, ∑ e, delta F (d, e) * (delta F (d, e) - 2) := by
  rw [Fintype.sum_prod_type]
  have hrow : ∀ d : Fin n → ZMod 2, ∑ e, delta F (d, e) ^ 2
      = ∑ e, delta F (d, e) * (delta F (d, e) - 2) + 2 * 2 ^ n := by
    intro d
    rw [← delta_row F d, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  simp_rw [hrow]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ 0)]
  have h0 : ∑ e, delta F (0, e) * (delta F (0, e) - 2) = 2 ^ n * (2 ^ n - 2) := by
    simp_rw [delta_zero]
    calc _ = ∑ e : Fin m → ZMod 2, if e = 0 then (2 : ℤ) ^ n * (2 ^ n - 2) else 0 := by
          refine Finset.sum_congr rfl fun e _ => ?_
          split_ifs <;> simp
      _ = _ := by simp
  rw [h0]
  ring

end PEqualNP.Outside.L_lib_425

theorem PEqualNP.Outside.L_lib_425 : (∀ n m : ℕ,
  let X := Fin n → ZMod 2
  let Y := Fin m → ZMod 2
  let s := fun (bit : ZMod 2) => if bit = 0 then (1 : ℤ) else -1
  ∀ F : X → Y,
    let N := (2:ℤ)^n
    let M := (2:ℤ)^m
    let moment := ∑ a : X, ∑ b : Y, (∑ x : X, s (dotProduct a x + dotProduct b (F x)))^4
    let bound := N*M*(3*N^2-2*N)
    bound ≤ moment ∧ (moment = bound ↔
      ∀ d : X, d ≠ 0 → ∀ e : Y, (Finset.univ.filter (fun x : X => F (x+d)+F x = e)).card ≤ 2)) := by
  intro n m X Y s F N M moment bound
  open PEqualNP.Outside.L_lib_425 in
  have key : moment = 2 ^ n * 2 ^ m * ((3 * (2 ^ n) ^ 2 - 2 * 2 ^ n) +
      ∑ d ∈ Finset.univ.erase 0, ∑ e, delta F (d, e) * (delta F (d, e) - 2)) := by
    rw [← sum_sq]
    exact moment_eq F
  open PEqualNP.Outside.L_lib_425 in
  have hterm : ∀ d ∈ (Finset.univ.erase (0 : Fin n → ZMod 2)), ∀ e : Fin m → ZMod 2,
      0 ≤ delta F (d, e) * (delta F (d, e) - 2) ∧
      (delta F (d, e) * (delta F (d, e) - 2) = 0 ↔
        (Finset.univ.filter (fun x : Fin n → ZMod 2 => F (x + d) + F x = e)).card ≤ 2) := by
    intro d hd e
    exact term_facts _ (delta_even F d (Finset.ne_of_mem_erase hd) e)
  open PEqualNP.Outside.L_lib_425 in
  have hR : 0 ≤ ∑ d ∈ Finset.univ.erase 0, ∑ e, delta F (d, e) * (delta F (d, e) - 2) :=
    Finset.sum_nonneg fun d hd => Finset.sum_nonneg fun e _ => (hterm d hd e).1
  have hNM : (0 : ℤ) < 2 ^ n * 2 ^ m := by positivity
  have hb : bound = 2 ^ n * 2 ^ m * (3 * (2 ^ n) ^ 2 - 2 * 2 ^ n) := rfl
  rw [key, hb]
  refine ⟨by nlinarith, ?_⟩
  open PEqualNP.Outside.L_lib_425 in
  constructor
  · intro h
    have h0 : ∑ d ∈ Finset.univ.erase 0, ∑ e, delta F (d, e) * (delta F (d, e) - 2) = 0 := by
      have := mul_left_cancel₀ hNM.ne' h
      linarith
    intro d hd e
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun d hd => Finset.sum_nonneg fun e _ => (hterm d hd e).1)] at h0
    have hdm : d ∈ Finset.univ.erase 0 := Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩
    have h1 := h0 d hdm
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun e _ => (hterm d hdm e).1)] at h1
    exact ((hterm d hdm e).2).mp (h1 e (Finset.mem_univ _))
  · intro h
    have h0 : ∑ d ∈ Finset.univ.erase 0, ∑ e, delta F (d, e) * (delta F (d, e) - 2) = 0 := by
      refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun e _ => ?_
      exact ((hterm d hd e).2).mpr (h d (Finset.ne_of_mem_erase hd) e)
    rw [h0, add_zero]
