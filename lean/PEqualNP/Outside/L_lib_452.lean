import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_452_aux

open Finset

def sg (b : Bool) : ℤ := if b then -1 else 1

theorem sum_sg_pow (k : ℕ) : (∑ b : Bool, sg b ^ k) = if Even k then 2 else 0 := by
  rw [Fintype.sum_bool]
  rcases Nat.even_or_odd k with h | h
  · simp [sg, h.neg_one_pow, h]
  · simp [sg, h.neg_one_pow, Nat.not_even_iff_odd.mpr h]

def mult {m : ℕ} (f : Fin m → Fin m) (r : Fin m) : ℕ := (univ.filter (fun c => f c = r)).card

theorem sum_mult {m : ℕ} (f : Fin m → Fin m) : ∑ r, mult f r = m := by
  unfold mult
  rw [← card_eq_sum_card_fiberwise (f := f) (s := univ) (t := univ) (fun _ _ => mem_univ _)]
  simp

theorem bij_iff {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) :
    Function.Bijective f ↔ ∀ t : Fin n, Odd (mult f t.succ) := by
  constructor
  · intro hf t
    have : mult f t.succ = 1 := by
      unfold mult
      rw [card_eq_one]
      obtain ⟨c, hc⟩ := hf.2 t.succ
      refine ⟨c, ?_⟩
      ext c'
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro h
        exact hf.1 (h.trans hc.symm)
      · rintro rfl
        exact hc
    rw [this]
    exact odd_one
  · intro h
    have hs := sum_mult f
    rw [Fin.sum_univ_succ] at hs
    have hge : ∀ t : Fin n, 1 ≤ mult f t.succ := fun t => (h t).pos
    have hone : ∀ t : Fin n, mult f t.succ = 1 := by
      intro t
      by_contra hne
      have h3 : 3 ≤ mult f t.succ := by
        obtain ⟨k, hk⟩ := h t
        omega
      have hsplit := add_sum_erase univ (fun t' : Fin n => mult f t'.succ) (mem_univ t)
      have hle : ∑ x ∈ univ.erase t, (1 : ℕ) ≤ ∑ x ∈ univ.erase t, mult f x.succ :=
        sum_le_sum (fun x _ => hge x)
      rw [sum_const, card_erase_of_mem (mem_univ t), card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one] at hle
      have hn : 1 ≤ n := by
        have := t.isLt
        omega
      omega
    have h0 : mult f 0 = 1 := by
      have : ∑ t : Fin n, mult f t.succ = n := by simp [hone]
      omega
    have hsurj : Function.Surjective f := by
      intro r
      have hr : mult f r = 1 := by
        cases r using Fin.cases with
        | zero => exact h0
        | succ t => exact hone t
      unfold mult at hr
      obtain ⟨c, hc⟩ := card_eq_one.mp hr
      have : c ∈ univ.filter (fun c => f c = r) := by
        rw [hc]
        exact mem_singleton_self c
      exact ⟨c, (mem_filter.mp this).2⟩
    exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

def dl {n : ℕ} (e : Fin n → Bool) : Fin (n + 1) → ℤ := Fin.cons 1 (fun i => sg (e i))

theorem inner_eq {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (e : Fin n → Bool) :
    ∏ col : Fin (n + 1), (M 0 col + ∑ i : Fin n, sg (e i) * M i.succ col) =
      ∑ f : Fin (n + 1) → Fin (n + 1),
        (∏ t : Fin n, sg (e t) ^ mult f t.succ) * ∏ col, M (f col) col := by
  have h1 : ∀ col, M 0 col + ∑ i : Fin n, sg (e i) * M i.succ col =
      ∑ r : Fin (n + 1), dl e r * M r col := by
    intro col
    rw [Fin.sum_univ_succ]
    simp [dl]
  simp_rw [h1]
  rw [Fintype.prod_sum]
  refine sum_congr rfl (fun f _ => ?_)
  rw [prod_mul_distrib]
  congr 1
  rw [← prod_fiberwise univ f (fun col => dl e (f col))]
  have h2 : ∀ r : Fin (n + 1), ∏ col ∈ univ.filter (fun col => f col = r), dl e (f col) =
      dl e r ^ mult f r := by
    intro r
    rw [prod_congr rfl (fun col hc => by rw [(mem_filter.mp hc).2]), prod_const]
    rfl
  simp_rw [h2]
  rw [Fin.prod_univ_succ]
  simp [dl]

theorem glynn {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :
    (2 : ℤ) ^ n * M.permanent =
      ∑ e : Fin n → Bool, (∏ t : Fin n, sg (e t)) *
        ∏ col : Fin (n + 1), (M 0 col + ∑ i : Fin n, sg (e i) * M i.succ col) := by
  classical
  simp_rw [inner_eq, mul_sum]
  rw [sum_comm]
  have h3 : ∀ f : Fin (n + 1) → Fin (n + 1),
      ∑ e : Fin n → Bool, (∏ t : Fin n, sg (e t)) *
        ((∏ t : Fin n, sg (e t) ^ mult f t.succ) * ∏ col, M (f col) col) =
      (if Function.Bijective f then (2 : ℤ) ^ n else 0) * ∏ col, M (f col) col := by
    intro f
    simp_rw [← mul_assoc, ← prod_mul_distrib, ← sum_mul]
    congr 1
    have h4 : ∀ e : Fin n → Bool, ∏ t : Fin n, sg (e t) * sg (e t) ^ mult f t.succ =
        ∏ t : Fin n, sg (e t) ^ (mult f t.succ + 1) := by
      intro e
      refine prod_congr rfl (fun t _ => ?_)
      ring
    simp_rw [h4]
    have h5 : ∑ e : Fin n → Bool, ∏ t : Fin n, sg (e t) ^ (mult f t.succ + 1) =
        ∏ t : Fin n, ∑ b : Bool, sg b ^ (mult f t.succ + 1) :=
      (Fintype.prod_sum (fun (t : Fin n) (b : Bool) => sg b ^ (mult f t.succ + 1))).symm
    rw [h5]
    simp_rw [sum_sg_pow]
    by_cases hb : Function.Bijective f
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
      have hodd := (bij_iff f).mp hb
      rw [prod_congr rfl (fun t _ => ite_eq_left_of_eq_true _ _ (eq_true (Nat.even_add_one.mpr
        (Nat.not_even_iff_odd.mpr (hodd t)))))]
      simp
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
      have : ¬ ∀ t : Fin n, Odd (mult f t.succ) := fun h => hb ((bij_iff f).mpr h)
      obtain ⟨t, ht⟩ := not_forall.mp this
      apply prod_eq_zero (mem_univ t)
      have hev : ¬ Even (mult f t.succ + 1) := by
        rw [Nat.even_add_one, not_not]
        exact Nat.not_odd_iff_even.mp ht
      exact ite_eq_right_of_eq_false _ _ (eq_false hev)
  simp_rw [h3]
  rw [Matrix.permanent, mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter]
  have hmap : (univ : Finset (Equiv.Perm (Fin (n + 1)))).map
      ⟨fun σ : Equiv.Perm (Fin (n + 1)) => (σ : Fin (n + 1) → Fin (n + 1)), DFunLike.coe_injective⟩ = univ.filter (fun f => Function.Bijective f) := by
    ext f
    simp only [mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk, mem_filter]
    constructor
    · rintro ⟨σ, rfl⟩
      exact σ.bijective
    · intro hf
      exact ⟨Equiv.ofBijective f hf, rfl⟩
  rw [← hmap, sum_map]
  rfl

end PEqualNP.Outside.L_lib_452_aux

theorem PEqualNP.Outside.L_lib_452 : ∀ (n : ℕ) (M : Matrix (Fin (n+1)) (Fin (n+1)) ℤ),
  let sign := fun (b : Bool) => if b then (-1 : ℤ) else 1
  (2 : ℤ)^n * M.permanent =
    ∑ e : Fin n → Bool,
      (∏ t : Fin n, sign (e t)) *
        ∏ col : Fin (n+1), (M 0 col + ∑ i : Fin n, sign (e i) * M i.succ col) := by
  intro n M sign
  exact PEqualNP.Outside.L_lib_452_aux.glynn M
