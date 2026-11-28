import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_983_aux

open Finset Matrix Equiv

section RealBounds

lemma factorial_le_pow_div_exp : ∀ d : ℕ,
    (d.factorial : ℝ) ≤ ((d + 1 : ℝ) ^ (d + 1)) / Real.exp (d : ℝ)
  | 0 => by simp
  | d + 1 => by
    have ih := factorial_le_pow_div_exp d
    have hd1 : (0 : ℝ) < (d + 1 : ℝ) := by positivity
    have hd2 : (0 : ℝ) < (d + 2 : ℝ) := by positivity
    have hexp_d : (0 : ℝ) < Real.exp (d : ℝ) := Real.exp_pos _
    have hexp_1 : (0 : ℝ) < Real.exp 1 := Real.exp_pos _
    have hstep1 : ((d + 1 : ℝ) / (d + 2 : ℝ)) ≤ Real.exp (-(1 / (d + 2 : ℝ))) := by
      have h := Real.add_one_le_exp (-(1 / (d + 2 : ℝ)))
      have heq : -(1 / (d + 2 : ℝ)) + 1 = (d + 1 : ℝ) / (d + 2 : ℝ) := by
        field_simp [hd2.ne']
        ring
      rwa [heq] at h
    have hpow : ((d + 1 : ℝ) / (d + 2 : ℝ)) ^ (d + 2) ≤ Real.exp (-1) := by
      calc ((d + 1 : ℝ) / (d + 2 : ℝ)) ^ (d + 2)
          ≤ (Real.exp (-(1 / (d + 2 : ℝ)))) ^ (d + 2) :=
            pow_le_pow_left₀ (by positivity) hstep1 (d + 2)
        _ = Real.exp ((d + 2 : ℕ) * (-(1 / (d + 2 : ℝ)))) := (Real.exp_nat_mul _ _).symm
        _ = Real.exp (-1) := by
            congr 1
            push_cast
            field_simp [hd2.ne']
    have hkey : Real.exp 1 * (d + 1 : ℝ) ^ (d + 2) ≤ (d + 2 : ℝ) ^ (d + 2) := by
      rw [div_pow, div_le_iff₀ (by positivity)] at hpow
      have hmul := mul_le_mul_of_nonneg_left hpow hexp_1.le
      have hcancel : Real.exp 1 * (Real.exp (-1) * (d + 2 : ℝ) ^ (d + 2)) = (d + 2 : ℝ) ^ (d + 2) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      linarith
    have hcast1 : (((d + 1).factorial : ℕ) : ℝ) = (d + 1 : ℝ) * (d.factorial : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hcast2 : (((d + 1 : ℕ) + 1 : ℝ)) = (d + 2 : ℝ) := by push_cast; ring
    have hcast3 : ((d + 1 : ℕ) : ℝ) = (d : ℝ) + 1 := by push_cast; ring
    rw [hcast1, hcast2, hcast3, Real.exp_add]
    calc (d + 1 : ℝ) * (d.factorial : ℝ)
        ≤ (d + 1 : ℝ) * (((d + 1 : ℝ) ^ (d + 1)) / Real.exp (d : ℝ)) :=
          mul_le_mul_of_nonneg_left ih hd1.le
      _ = ((d + 1 : ℝ) ^ (d + 2)) / Real.exp (d : ℝ) := by
          rw [← mul_div_assoc, ← pow_succ']
      _ = (Real.exp 1 * (d + 1 : ℝ) ^ (d + 2)) / (Real.exp (d : ℝ) * Real.exp 1) := by
          field_simp [hexp_d.ne', hexp_1.ne']
      _ ≤ ((d + 2 : ℝ) ^ (d + 2)) / (Real.exp (d : ℝ) * Real.exp 1) :=
          div_le_div_of_nonneg_right hkey (by positivity)

lemma one_add_quad_le_pow (δ : ℝ) (hδ : 0 ≤ δ) : ∀ n : ℕ,
    1 + (n : ℝ) * δ + (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2 ≤ (1 + δ) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := one_add_quad_le_pow δ hδ n
    have hnn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by
      cases n with
      | zero => simp
      | succ k =>
        push_cast
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        nlinarith
    have h1 : (1 + δ) * (1 + (n : ℝ) * δ + (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2) ≤ (1 + δ) ^ (n + 1) := by
      have hpos : (0 : ℝ) ≤ 1 + δ := by linarith
      calc (1 + δ) * (1 + (n : ℝ) * δ + (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2)
          ≤ (1 + δ) * (1 + δ) ^ n := mul_le_mul_of_nonneg_left ih hpos
        _ = (1 + δ) ^ (n + 1) := (pow_succ' (1 + δ) n).symm
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 3 := by positivity
    nlinarith

lemma exists_prime_rate_gap (r₀ : ℝ) (hr₀_pos : 0 < r₀) (hr₀_lt : r₀ < Real.exp 1) :
    ∃ q : ℕ, Nat.Prime q ∧ r₀ ^ (q + 1) * ((q + 1).factorial : ℝ) ≤ (q : ℝ) ^ (q + 1) := by
  let δ : ℝ := Real.exp 1 / r₀ - 1
  have hδ : 0 < δ := by
    dsimp only [δ]
    rw [sub_pos, one_lt_div hr₀_pos]
    exact hr₀_lt
  let N : ℕ := max 2 (Nat.ceil (12 * Real.exp 2 / δ ^ 2) + 4)
  obtain ⟨q, hqN, hqprime⟩ := Nat.exists_infinite_primes N
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hqN
  have hqR : 12 * Real.exp 2 / δ ^ 2 ≤ (q : ℝ) := by
    have h1 : Nat.ceil (12 * Real.exp 2 / δ ^ 2) ≤ q := by
      have := le_trans (le_max_right _ _) hqN
      omega
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.2 h1)
  have hq_pos : (0 : ℝ) < (q : ℝ) := by positivity
  have hq2_R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hpow2 : ((q + 2 : ℝ) / (q : ℝ)) ^ q ≤ Real.exp 2 := by
    have h1 : (q + 2 : ℝ) / (q : ℝ) ≤ Real.exp (2 / (q : ℝ)) := by
      have h := Real.add_one_le_exp (2 / (q : ℝ))
      have heq : 2 / (q : ℝ) + 1 = (q + 2 : ℝ) / (q : ℝ) := by
        field_simp [hq_pos.ne']
        ring
      rwa [heq] at h
    calc ((q + 2 : ℝ) / (q : ℝ)) ^ q
        ≤ (Real.exp (2 / (q : ℝ))) ^ q := pow_le_pow_left₀ (by positivity) h1 q
      _ = Real.exp ((q : ℕ) * (2 / (q : ℝ))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp 2 := by congr 1; field_simp [hq_pos.ne']
  have hratio_le : (q + 2 : ℝ) / (q : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hq_pos]
    linarith
  have hlhs : (q + 2 : ℝ) * ((q + 2 : ℝ) / (q : ℝ)) ^ (q + 1) ≤ 3 * Real.exp 2 * (q + 2 : ℝ) := by
    rw [pow_succ']
    have hmul : ((q + 2 : ℝ) / (q : ℝ)) * ((q + 2 : ℝ) / (q : ℝ)) ^ q ≤ 3 * Real.exp 2 :=
      mul_le_mul hratio_le hpow2 (by positivity) (by norm_num)
    have hmul2 := mul_le_mul_of_nonneg_left hmul (by positivity : (0 : ℝ) ≤ (q + 2 : ℝ))
    linarith
  have hrhs : 3 * Real.exp 2 * (q + 2 : ℝ) ≤ (Real.exp 1 / r₀) ^ (q + 1) := by
    have h1 := one_add_quad_le_pow δ hδ.le (q + 1)
    have h1add : 1 + δ = Real.exp 1 / r₀ := by dsimp only [δ]; ring
    rw [h1add] at h1
    have hqcast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; ring
    rw [hqcast] at h1
    have hquad : 3 * Real.exp 2 * (q + 2 : ℝ) ≤ ((q : ℝ) + 1) * ((q : ℝ) + 1 - 1) / 2 * δ ^ 2 := by
      have hqδ : 12 * Real.exp 2 ≤ (q : ℝ) * δ ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at hqR
        exact hqR
      have hexp2_pos : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
      have hq_add : (q + 2 : ℝ) ≤ 2 * ((q : ℝ) + 1) := by linarith
      have h2 : 3 * Real.exp 2 * (q + 2 : ℝ) ≤ 6 * Real.exp 2 * ((q : ℝ) + 1) := by nlinarith
      have h3 : 6 * Real.exp 2 * ((q : ℝ) + 1) ≤ ((q : ℝ) + 1) * (q : ℝ) / 2 * δ ^ 2 := by nlinarith
      nlinarith
    have hnonneg : (0 : ℝ) ≤ 1 + ((q : ℝ) + 1) * δ := by positivity
    linarith
  have hmain : (q + 2 : ℝ) * ((q + 2 : ℝ) / (q : ℝ)) ^ (q + 1) ≤ (Real.exp 1 / r₀) ^ (q + 1) :=
    le_trans hlhs hrhs
  have hfact := factorial_le_pow_div_exp (q + 1)
  have hfact' : ((q + 1).factorial : ℝ) ≤ ((q + 2 : ℝ) ^ (q + 2)) / Real.exp ((q + 1 : ℕ) : ℝ) := by
    convert hfact using 2
    congr 1
    push_cast; ring
  refine ⟨q, hqprime, ?_⟩
  have hexp_eq : (Real.exp 1) ^ (q + 1) = Real.exp ((q + 1 : ℕ) : ℝ) := by
    rw [← Real.exp_nat_mul, mul_one]
  have hrearr : r₀ ^ (q + 1) * (((q + 2 : ℝ) ^ (q + 2)) / Real.exp ((q + 1 : ℕ) : ℝ)) ≤ (q : ℝ) ^ (q + 1) := by
    rw [div_pow, div_pow, hexp_eq] at hmain
    have hmul := mul_le_mul_of_nonneg_right hmain (by positivity : (0 : ℝ) ≤ r₀ ^ (q + 1) * (q : ℝ) ^ (q + 1))
    have hL : (q + 2 : ℝ) * ((q + 2 : ℝ) ^ (q + 1) / (q : ℝ) ^ (q + 1)) * (r₀ ^ (q + 1) * (q : ℝ) ^ (q + 1)) =
        r₀ ^ (q + 1) * (q + 2 : ℝ) ^ (q + 2) := by
      have hqn : (q : ℝ) ^ (q + 1) ≠ 0 := by positivity
      field_simp [hqn]
      ring
    have hR : Real.exp ((q + 1 : ℕ) : ℝ) / r₀ ^ (q + 1) * (r₀ ^ (q + 1) * (q : ℝ) ^ (q + 1)) =
        Real.exp ((q + 1 : ℕ) : ℝ) * (q : ℝ) ^ (q + 1) := by
      have hrn : r₀ ^ (q + 1) ≠ 0 := by positivity
      field_simp [hrn]
    rw [hL, hR] at hmul
    rw [mul_div_assoc', div_le_iff₀ (Real.exp_pos _)]
    linarith
  exact le_trans (mul_le_mul_of_nonneg_left hfact' (by positivity)) hrearr

end RealBounds

section Bregman

lemma sum_mul_log_div_le {α : Type*} [DecidableEq α] (T : Finset α) (f : α → ℝ)
    (hT : T.Nonempty) (hf : ∀ x ∈ T, 0 < f x) :
    ∑ x ∈ T, f x * Real.log ((∑ y ∈ T, f y) / f x) ≤
      (∑ y ∈ T, f y) * Real.log (T.card : ℝ) := by
  set A := ∑ y ∈ T, f y
  have hA : 0 < A := sum_pos hf hT
  have hTpos : (0 : ℝ) < (T.card : ℝ) := by exact_mod_cast hT.card_pos
  have hpt : ∀ x ∈ T, f x * Real.log (A / f x) - f x * Real.log (T.card : ℝ) ≤
      A / (T.card : ℝ) - f x := by
    intro x hx
    have hfx := hf x hx
    have hpos : 0 < A / ((T.card : ℝ) * f x) := div_pos hA (mul_pos hTpos hfx)
    have hlog_eq : Real.log (A / ((T.card : ℝ) * f x)) =
        Real.log (A / f x) - Real.log (T.card : ℝ) := by
      rw [show A / ((T.card : ℝ) * f x) = (A / f x) / (T.card : ℝ) by ring]
      exact Real.log_div (div_pos hA hfx).ne' hTpos.ne'
    have hle := Real.log_le_sub_one_of_pos hpos
    rw [hlog_eq] at hle
    have hmul := mul_le_mul_of_nonneg_left hle hfx.le
    have hr : f x * (A / ((T.card : ℝ) * f x) - 1) = A / (T.card : ℝ) - f x := by
      field_simp [hfx.ne', hTpos.ne']
    linarith
  have hsum := sum_le_sum hpt
  rw [sum_sub_distrib, ← sum_mul, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
  have hcancel : (T.card : ℝ) * (A / (T.card : ℝ)) = A := mul_div_cancel₀ A hTpos.ne'
  rw [hcancel, sub_self] at hsum
  linarith

lemma sum_log_rank_eq_log_factorial {α : Type*} [DecidableEq α] :
    ∀ (k : ℕ) (U : Finset α) (g : α → ℕ),
      U.card = k → Set.InjOn g (U : Set α) →
      ∑ v ∈ U, Real.log ((U.filter (fun u => g v ≤ g u)).card : ℝ) = Real.log (k.factorial : ℝ)
  | 0, U, _, hcard, _ => by
    rw [card_eq_zero.1 hcard]
    simp
  | k + 1, U, g, hcard, hinj => by
    have hUne : U.Nonempty := card_pos.1 (by omega)
    obtain ⟨v0, hv0, hmin⟩ := Finset.exists_min_image U g hUne
    rw [← add_sum_erase U _ hv0]
    have hflt0 : U.filter (fun u => g v0 ≤ g u) = U := by
      ext u
      simp only [mem_filter, and_iff_left_iff_imp]
      exact fun hu => hmin u hu
    rw [hflt0, hcard]
    have herase_card : (U.erase v0).card = k := by
      rw [card_erase_of_mem hv0, hcard]; simp
    have herase_inj : Set.InjOn g ((U.erase v0 : Finset α) : Set α) :=
      hinj.mono (by simp [erase_subset])
    have hcongr : ∑ v ∈ U.erase v0, Real.log ((U.filter (fun u => g v ≤ g u)).card : ℝ) =
        ∑ v ∈ U.erase v0, Real.log (((U.erase v0).filter (fun u => g v ≤ g u)).card : ℝ) := by
      refine sum_congr rfl fun v hv => ?_
      have hvU : v ∈ U := mem_of_mem_erase hv
      have hvne : v ≠ v0 := ne_of_mem_erase hv
      have hgne : g v ≠ g v0 := fun heq => hvne (hinj hvU hv0 heq)
      have hglt : g v0 < g v := lt_of_le_of_ne (hmin v hvU) (Ne.symm hgne)
      congr 3
      ext u
      simp only [mem_filter, mem_erase]
      constructor
      · rintro ⟨huU, hle⟩
        refine ⟨⟨fun hu0 => ?_, huU⟩, hle⟩
        subst hu0
        omega
      · rintro ⟨⟨_, huU⟩, hle⟩
        exact ⟨huU, hle⟩
    rw [hcongr, sum_log_rank_eq_log_factorial k (U.erase v0) g herase_card herase_inj]
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

noncomputable def bregAvail {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (τ σ : Equiv.Perm (Fin m)) (i : Fin m) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin m)).filter
    (fun j => A i j = 1 ∧ (τ.symm i).val ≤ (τ.symm (σ.symm j)).val)).card

lemma bregman_step_tau {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (S : Finset (Equiv.Perm (Fin m)))
    (hS : ∀ σ ∈ S, ∀ i : Fin m, A i (σ i) = 1)
    (τ : Equiv.Perm (Fin m)) :
    (S.card : ℝ) * Real.log (S.card : ℝ) ≤
      ∑ σ ∈ S, ∑ i : Fin m, Real.log (bregAvail A τ σ i : ℝ) := by
  classical
  let pref : ℕ → Equiv.Perm (Fin m) → Finset (Equiv.Perm (Fin m)) :=
    fun k σ => S.filter (fun σ' => ∀ l : Fin m, l.val < k → σ' (τ l) = σ (τ l))
  have htele : ∀ σ ∈ S,
      Real.log (S.card : ℝ) =
        ∑ k : Fin m, Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ)) := by
    intro σ hσ
    have hpos_k : ∀ k : ℕ, (0 : ℝ) < ((pref k σ).card : ℝ) := fun k =>
      Nat.cast_pos.2 (card_pos.2 ⟨σ, mem_filter.2 ⟨hσ, fun _ _ => rfl⟩⟩)
    have hdiv : ∀ k : Fin m,
        Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ)) =
          Real.log ((pref k.val σ).card : ℝ) - Real.log ((pref (k.val + 1) σ).card : ℝ) :=
      fun k => Real.log_div (hpos_k k.val).ne' (hpos_k (k.val + 1)).ne'
    simp_rw [hdiv]
    rw [Fin.sum_univ_eq_sum_range (fun k => Real.log ((pref k σ).card : ℝ) -
      Real.log ((pref (k + 1) σ).card : ℝ)) m]
    have hsum_tele : ∀ n : ℕ,
        ∑ k ∈ Finset.range n, (Real.log ((pref k σ).card : ℝ) -
          Real.log ((pref (k + 1) σ).card : ℝ)) =
        Real.log ((pref 0 σ).card : ℝ) - Real.log ((pref n σ).card : ℝ) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; ring
    rw [hsum_tele m]
    have h0 : pref 0 σ = S := by ext σ'; simp [pref]
    have hm : pref m σ = {σ} := by
      ext σ'
      simp only [pref, mem_filter, mem_singleton]
      constructor
      · rintro ⟨_, heq⟩
        apply Equiv.ext
        intro i
        have := heq (τ.symm i) (τ.symm i).isLt
        simpa using this
      · rintro rfl; exact ⟨hσ, fun _ _ => rfl⟩
    rw [h0, hm, card_singleton, Nat.cast_one, Real.log_one, sub_zero]
  have hlhs : (S.card : ℝ) * Real.log (S.card : ℝ) =
      ∑ k : Fin m, ∑ σ ∈ S,
        Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ)) := by
    rw [sum_comm]
    calc (S.card : ℝ) * Real.log (S.card : ℝ)
        = ∑ _σ ∈ S, Real.log (S.card : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ = ∑ σ ∈ S, ∑ k : Fin m,
            Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ)) :=
          sum_congr rfl fun σ hσ => htele σ hσ
  have hrhs : ∑ σ ∈ S, ∑ i : Fin m, Real.log (bregAvail A τ σ i : ℝ) =
      ∑ k : Fin m, ∑ σ ∈ S, Real.log (bregAvail A τ σ (τ k) : ℝ) := by
    have h1 : ∑ σ ∈ S, ∑ i : Fin m, Real.log (bregAvail A τ σ i : ℝ) =
        ∑ σ ∈ S, ∑ k : Fin m, Real.log (bregAvail A τ σ (τ k) : ℝ) :=
      sum_congr rfl fun σ _ => (Equiv.sum_comp τ (fun i => Real.log (bregAvail A τ σ i : ℝ))).symm
    rw [h1, sum_comm]
  rw [hlhs, hrhs]
  refine sum_le_sum fun k _ => ?_
  let key : Equiv.Perm (Fin m) → (Fin m → Option (Fin m)) :=
    fun σ l => if l.val < k.val then some (σ (τ l)) else none
  have hkey_eq : ∀ σ1 σ2, key σ1 = key σ2 ↔ ∀ l : Fin m, l.val < k.val → σ1 (τ l) = σ2 (τ l) := by
    intro σ1 σ2
    constructor
    · intro h l hl
      have := congrFun h l
      simp only [key, if_pos hl, Option.some.injEq] at this
      exact this
    · intro h
      funext l
      dsimp only [key]
      split_ifs with hl
      · exact congrArg some (h l hl)
      · rfl
  rw [← sum_fiberwise_of_maps_to (g := key) (t := S.image key) (fun σ hσ => mem_image_of_mem key hσ),
    ← sum_fiberwise_of_maps_to (g := key) (t := S.image key) (fun σ hσ => mem_image_of_mem key hσ)]
  refine sum_le_sum fun c hc => ?_
  set E := S.filter (fun σ => key σ = c)
  obtain ⟨σ0, hσ0S, rfl⟩ := mem_image.1 hc
  have hE_eq : ∀ σ ∈ E, pref k.val σ = E := by
    intro σ hσ
    have hσkey : key σ = key σ0 := (mem_filter.1 hσ).2
    ext σ'
    simp only [pref, E, mem_filter]
    constructor
    · rintro ⟨hσ'S, h⟩
      exact ⟨hσ'S, ((hkey_eq σ' σ).2 h).trans hσkey⟩
    · rintro ⟨hσ'S, h⟩
      exact ⟨hσ'S, (hkey_eq σ' σ).1 (h.trans hσkey.symm)⟩
  have havail_const : ∀ σ ∈ E, bregAvail A τ σ (τ k) = bregAvail A τ σ0 (τ k) := by
    intro σ hσ
    have hσkey : ∀ l : Fin m, l.val < k.val → σ (τ l) = σ0 (τ l) :=
      (hkey_eq σ σ0).1 (mem_filter.1 hσ).2
    unfold bregAvail
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and, Equiv.symm_apply_apply]
    have hiff : ∀ (π : Equiv.Perm (Fin m)),
        k.val ≤ (τ.symm (π.symm j)).val ↔ ∀ l : Fin m, l.val < k.val → π (τ l) ≠ j := by
      intro π
      constructor
      · intro hle l hl heq
        have : π.symm j = τ l := by rw [← heq, Equiv.symm_apply_apply]
        rw [this, Equiv.symm_apply_apply] at hle
        omega
      · intro h
        by_contra hlt
        push_neg at hlt
        exact h (τ.symm (π.symm j)) hlt (by simp)
    rw [hiff σ, hiff σ0]
    refine and_congr_right fun _ => ⟨fun h l hl => ?_, fun h l hl => ?_⟩
    · rw [← hσkey l hl]; exact h l hl
    · rw [hσkey l hl]; exact h l hl
  set Y := E.image (fun σ => σ (τ k))
  have hY_sub : Y ⊆ Finset.univ.filter (fun j =>
      A (τ k) j = 1 ∧ (τ.symm (τ k)).val ≤ (τ.symm (σ0.symm j)).val) := by
    intro j hj
    obtain ⟨σ, hσE, rfl⟩ := mem_image.1 hj
    have hσS : σ ∈ S := (mem_filter.1 hσE).1
    have hσkey : ∀ l : Fin m, l.val < k.val → σ (τ l) = σ0 (τ l) :=
      (hkey_eq σ σ0).1 (mem_filter.1 hσE).2
    refine mem_filter.2 ⟨mem_univ _, hS σ hσS (τ k), ?_⟩
    rw [Equiv.symm_apply_apply]
    by_contra hlt
    push_neg at hlt
    set l := τ.symm (σ0.symm (σ (τ k)))
    have hl_eq : σ0 (τ l) = σ (τ k) := by simp [l]
    have hkl : σ (τ l) = σ (τ k) := (hσkey l hlt).trans hl_eq
    have hlt_eq : l = k := τ.injective (σ.injective hkl)
    rw [hlt_eq] at hlt
    exact lt_irrefl _ hlt
  have hY_le : Y.card ≤ bregAvail A τ σ0 (τ k) := by
    unfold bregAvail; exact card_le_card hY_sub
  have hY_ne : Y.Nonempty := ⟨σ0 (τ k), mem_image_of_mem _ (mem_filter.2 ⟨hσ0S, rfl⟩)⟩
  have hpart : ∑ σ ∈ E, Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ)) =
      ∑ y ∈ Y, ((E.filter (fun σ => σ (τ k) = y)).card : ℝ) *
        Real.log ((E.card : ℝ) / ((E.filter (fun σ => σ (τ k) = y)).card : ℝ)) := by
    rw [← sum_fiberwise_of_maps_to (g := fun σ => σ (τ k)) (t := Y) (fun σ hσ => mem_image_of_mem _ hσ)]
    refine sum_congr rfl fun y hy => ?_
    have hinner : ∀ σ ∈ E.filter (fun σ => σ (τ k) = y),
        pref (k.val + 1) σ = E.filter (fun σ' => σ' (τ k) = y) := by
      intro σ hσ
      have ⟨hσE, hσy⟩ := mem_filter.1 hσ
      ext σ'
      simp only [pref, E, mem_filter]
      constructor
      · rintro ⟨hσ'S, hall⟩
        have hk_lt : k.val < k.val + 1 := Nat.lt_succ_self _
        have h1 : key σ' = key σ0 :=
          ((hkey_eq σ' σ).2 fun l hl => hall l (by omega)).trans (mem_filter.1 hσE).2
        exact ⟨⟨hσ'S, h1⟩, (hall k hk_lt).trans hσy⟩
      · rintro ⟨⟨hσ'S, h1⟩, h2⟩
        refine ⟨hσ'S, fun l hl => ?_⟩
        by_cases hlk : l.val < k.val
        · exact (hkey_eq σ' σ).1 (h1.trans (mem_filter.1 hσE).2.symm) l hlk
        · have hle : l = k := Fin.ext (by omega)
          subst hle
          exact h2.trans hσy.symm
    calc ∑ σ ∈ E.filter (fun σ => σ (τ k) = y),
          Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ))
        = ∑ _σ ∈ E.filter (fun σ => σ (τ k) = y),
            Real.log ((E.card : ℝ) / ((E.filter (fun σ' => σ' (τ k) = y)).card : ℝ)) :=
          sum_congr rfl fun σ hσ => by rw [hE_eq σ (mem_filter.1 hσ).1, hinner σ hσ]
      _ = ((E.filter (fun σ => σ (τ k) = y)).card : ℝ) *
            Real.log ((E.card : ℝ) / ((E.filter (fun σ' => σ' (τ k) = y)).card : ℝ)) := by
          rw [sum_const, nsmul_eq_mul]
  have hsum_E : ∑ y ∈ Y, ((E.filter (fun σ => σ (τ k) = y)).card : ℝ) = (E.card : ℝ) := by
    have hnat : ∑ y ∈ Y, (E.filter (fun σ => σ (τ k) = y)).card = E.card := by
      have hf := Finset.sum_fiberwise_of_maps_to (s := E) (t := Y) (g := fun σ => σ (τ k))
        (f := fun _ => (1 : ℕ)) (fun σ hσ => mem_image_of_mem _ hσ)
      simpa only [sum_const, smul_eq_mul, mul_one] using hf
    exact_mod_cast hnat
  have hf_pos : ∀ y ∈ Y, (0 : ℝ) < ((E.filter (fun σ => σ (τ k) = y)).card : ℝ) := by
    intro y hy
    obtain ⟨σ, hσE, rfl⟩ := mem_image.1 hy
    exact Nat.cast_pos.2 (card_pos.2 ⟨σ, mem_filter.2 ⟨hσE, rfl⟩⟩)
  let fY : Fin m → ℝ := fun y => ((E.filter (fun σ => σ (τ k) = y)).card : ℝ)
  have hjensen := sum_mul_log_div_le Y fY hY_ne hf_pos
  change ∑ y ∈ Y, fY y * Real.log ((∑ y' ∈ Y, fY y') / fY y) ≤ (∑ y' ∈ Y, fY y') * Real.log (Y.card : ℝ) at hjensen
  have hsum_fY : ∑ y' ∈ Y, fY y' = (E.card : ℝ) := hsum_E
  rw [hsum_fY] at hjensen
  have hlog_le : Real.log (Y.card : ℝ) ≤ Real.log (bregAvail A τ σ0 (τ k) : ℝ) :=
    Real.log_le_log (Nat.cast_pos.2 hY_ne.card_pos) (Nat.cast_le.2 hY_le)
  calc ∑ σ ∈ E, Real.log (((pref k.val σ).card : ℝ) / ((pref (k.val + 1) σ).card : ℝ))
      ≤ (E.card : ℝ) * Real.log (Y.card : ℝ) := by rw [hpart]; exact hjensen
    _ ≤ (E.card : ℝ) * Real.log (bregAvail A τ σ0 (τ k) : ℝ) :=
        mul_le_mul_of_nonneg_left hlog_le (Nat.cast_nonneg _)
    _ = ∑ _σ ∈ E, Real.log (bregAvail A τ σ0 (τ k) : ℝ) := by rw [sum_const, nsmul_eq_mul]
    _ = ∑ σ ∈ E, Real.log (bregAvail A τ σ (τ k) : ℝ) :=
        sum_congr rfl fun σ hσ => by rw [havail_const σ hσ]

lemma bregman_avg_tau {m d : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (hrow : ∀ i, ((Finset.univ : Finset (Fin m)).filter (fun j => A i j = 1)).card = d)
    (σ : Equiv.Perm (Fin m)) (i : Fin m) (hAi : A i (σ i) = 1) :
    (d : ℝ) * ∑ τ : Equiv.Perm (Fin m), Real.log (bregAvail A τ σ i : ℝ) =
      (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * Real.log (d.factorial : ℝ) := by
  classical
  let U : Finset (Fin m) := Finset.univ.filter (fun u => A i (σ u) = 1)
  have hU_card : U.card = d := by
    have hbij : U.card = ((Finset.univ : Finset (Fin m)).filter (fun j => A i j = 1)).card := by
      refine card_bij (fun u _ => σ u) ?_ ?_ ?_
      · intro u hu; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hu).2⟩
      · intro u1 _ u2 _ h; exact σ.injective h
      · intro j hj
        refine ⟨σ.symm j, mem_filter.2 ⟨mem_univ _, ?_⟩, Equiv.apply_symm_apply σ j⟩
        simpa using (mem_filter.1 hj).2
    exact hbij.trans (hrow i)
  have hiU : i ∈ U := mem_filter.2 ⟨mem_univ _, hAi⟩
  let rnk : Equiv.Perm (Fin m) → Fin m → ℕ :=
    fun τ v => (U.filter (fun u => (τ.symm v).val ≤ (τ.symm u).val)).card
  have havail_eq : ∀ τ : Equiv.Perm (Fin m), bregAvail A τ σ i = rnk τ i := by
    intro τ
    unfold bregAvail
    refine card_bij (fun j _ => σ.symm j) ?_ ?_ ?_
    · intro j hj
      have ⟨_, hA, hle⟩ := mem_filter.1 hj
      exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, by simpa using hA⟩, hle⟩
    · intro j1 _ j2 _ h; exact σ.symm.injective h
    · intro u hu
      have ⟨huU, hle⟩ := mem_filter.1 hu
      refine ⟨σ u, mem_filter.2 ⟨mem_univ _, (mem_filter.1 huU).2, ?_⟩, Equiv.symm_apply_apply σ u⟩
      simpa using hle
  have hswap_rnk : ∀ (v : Fin m) (hv : v ∈ U) (τ : Equiv.Perm (Fin m)),
      rnk (Equiv.swap i v * τ) i = rnk τ v := by
    intro v hv τ
    have hsymm_mul : ∀ x : Fin m, (Equiv.swap i v * τ).symm x = τ.symm (Equiv.swap i v x) := fun x => by
      apply (Equiv.swap i v * τ).injective
      simp [Equiv.Perm.mul_apply]
    refine card_bij (fun u _ => Equiv.swap i v u) ?_ ?_ ?_
    · intro u hu
      have ⟨huU, hle⟩ := mem_filter.1 hu
      have hmemU : Equiv.swap i v u ∈ U := by
        by_cases hui : u = i
        · subst hui; simp [hv]
        · by_cases huv : u = v
          · subst huv; simp [hiU]
          · rw [Equiv.swap_apply_of_ne_of_ne hui huv]; exact huU
      refine mem_filter.2 ⟨hmemU, ?_⟩
      rwa [hsymm_mul i, hsymm_mul u, Equiv.swap_apply_left] at hle
    · intro u1 _ u2 _ h; exact (Equiv.swap i v).injective h
    · intro w hw
      have ⟨hwU, hle⟩ := mem_filter.1 hw
      have hmemU : Equiv.swap i v w ∈ U := by
        by_cases hwi : w = i
        · subst hwi; simp [hv]
        · by_cases hwv : w = v
          · subst hwv; simp [hiU]
          · rw [Equiv.swap_apply_of_ne_of_ne hwi hwv]; exact hwU
      refine ⟨Equiv.swap i v w, mem_filter.2 ⟨hmemU, ?_⟩, Equiv.swap_apply_self i v w⟩
      rw [hsymm_mul i, hsymm_mul (Equiv.swap i v w), Equiv.swap_apply_left, Equiv.swap_apply_self]
      exact hle
  calc (d : ℝ) * ∑ τ : Equiv.Perm (Fin m), Real.log (bregAvail A τ σ i : ℝ)
      = ∑ _v ∈ U, ∑ τ : Equiv.Perm (Fin m), Real.log (rnk τ i : ℝ) := by
        rw [sum_const, nsmul_eq_mul, hU_card]
        congr 1
        exact sum_congr rfl fun τ _ => by rw [havail_eq τ]
    _ = ∑ v ∈ U, ∑ τ : Equiv.Perm (Fin m), Real.log (rnk (Equiv.swap i v * τ) i : ℝ) := by
        refine sum_congr rfl fun v _ => ?_
        exact (Equiv.sum_comp (Equiv.mulLeft (Equiv.swap i v)) (fun τ => Real.log (rnk τ i : ℝ))).symm
    _ = ∑ v ∈ U, ∑ τ : Equiv.Perm (Fin m), Real.log (rnk τ v : ℝ) := by
        refine sum_congr rfl fun v hv => sum_congr rfl fun τ _ => by rw [hswap_rnk v hv τ]
    _ = ∑ τ : Equiv.Perm (Fin m), ∑ v ∈ U, Real.log (rnk τ v : ℝ) := sum_comm
    _ = ∑ _τ : Equiv.Perm (Fin m), Real.log (d.factorial : ℝ) := by
        refine sum_congr rfl fun τ _ => ?_
        exact sum_log_rank_eq_log_factorial d U (fun u => (τ.symm u).val) hU_card
          (fun u1 _ u2 _ h => τ.symm.injective (Fin.ext h))
    _ = (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * Real.log (d.factorial : ℝ) := by
        rw [sum_const, card_univ, nsmul_eq_mul]

lemma bregman_regular {m d : ℕ} (hd : 0 < d) (A : Matrix (Fin m) (Fin m) ℝ)
    (hbin : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hrow : ∀ i, ((Finset.univ : Finset (Fin m)).filter (fun j => A i j = 1)).card = d) :
    A.permanent ^ d ≤ (d.factorial : ℝ) ^ m := by
  classical
  let S : Finset (Equiv.Perm (Fin m)) := Finset.univ.filter (fun σ => ∀ i, A i (σ i) = 1)
  have hperm_eq : A.permanent = (S.card : ℝ) := by
    rw [← Matrix.permanent_transpose, Matrix.permanent]
    have hterm : ∀ σ : Equiv.Perm (Fin m),
        (∏ i : Fin m, Aᵀ (σ i) i) = if σ ∈ S then (1 : ℝ) else 0 := by
      intro σ
      by_cases hσ : σ ∈ S
      · rw [if_pos hσ]
        exact prod_eq_one fun i _ => (mem_filter.1 hσ).2 i
      · rw [if_neg hσ]
        have hnot : ¬ ∀ i, A i (σ i) = 1 := fun h => hσ (mem_filter.2 ⟨mem_univ _, h⟩)
        push_neg at hnot
        obtain ⟨i, hi⟩ := hnot
        have h0 : A i (σ i) = 0 := (hbin i (σ i)).resolve_right hi
        exact prod_eq_zero (mem_univ i) h0
    simp_rw [hterm]
    simp
  rw [hperm_eq]
  by_cases hS0 : S.card = 0
  · rw [hS0, Nat.cast_zero, zero_pow hd.ne']
    positivity
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hS0)
  have hS_ok : ∀ σ ∈ S, ∀ i : Fin m, A i (σ i) = 1 := fun σ hσ => (mem_filter.1 hσ).2
  have hsum_all := sum_le_sum fun τ (_ : τ ∈ (Finset.univ : Finset (Equiv.Perm (Fin m)))) =>
    bregman_step_tau A S hS_ok τ
  rw [sum_const, card_univ, nsmul_eq_mul] at hsum_all
  have hrhs_eq : (d : ℝ) * ∑ τ : Equiv.Perm (Fin m), ∑ σ ∈ S, ∑ i : Fin m, Real.log (bregAvail A τ σ i : ℝ) =
      (S.card : ℝ) * (m : ℝ) * (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * Real.log (d.factorial : ℝ) := by
    rw [mul_sum]
    calc ∑ τ : Equiv.Perm (Fin m), (d : ℝ) * ∑ σ ∈ S, ∑ i : Fin m, Real.log (bregAvail A τ σ i : ℝ)
        = ∑ σ ∈ S, ∑ i : Fin m, (d : ℝ) * ∑ τ : Equiv.Perm (Fin m), Real.log (bregAvail A τ σ i : ℝ) := by
          simp_rw [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun σ _ => sum_comm
      _ = ∑ _σ ∈ S, ∑ _i : Fin m,
            (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * Real.log (d.factorial : ℝ) :=
          sum_congr rfl fun σ hσ => sum_congr rfl fun i _ => bregman_avg_tau A hrow σ i (hS_ok σ hσ i)
      _ = (S.card : ℝ) * (m : ℝ) * (Fintype.card (Equiv.Perm (Fin m)) : ℝ) * Real.log (d.factorial : ℝ) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hPperm : (0 : ℝ) < (Fintype.card (Equiv.Perm (Fin m)) : ℝ) :=
    Nat.cast_pos.2 Fintype.card_pos
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.2 hd
  have hmul_d := mul_le_mul_of_nonneg_left hsum_all hd_pos.le
  rw [hrhs_eq] at hmul_d
  have hlog_pow : Real.log ((S.card : ℝ) ^ d) ≤ Real.log ((d.factorial : ℝ) ^ m) := by
    rw [Real.log_pow, Real.log_pow]
    nlinarith [mul_pos hSpos hPperm]
  have h1 := Real.exp_le_exp.2 hlog_pow
  rwa [Real.exp_log (pow_pos hSpos d), Real.exp_log (by positivity)] at h1

end Bregman

section ProjPlane

abbrev Pt (q : ℕ) := Unit ⊕ ZMod q ⊕ (ZMod q × ZMod q)

def vec (q : ℕ) : Pt q → Fin 3 → ZMod q
  | Sum.inl () => ![0, 0, 1]
  | Sum.inr (Sum.inl a) => ![0, 1, a]
  | Sum.inr (Sum.inr (a, b)) => ![1, a, b]

def dot3 {q : ℕ} (u v : Fin 3 → ZMod q) : ZMod q :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

lemma vec_ne_zero (q : ℕ) [Fact (Nat.Prime q)] (x : Pt q) : vec q x ≠ 0 := by
  cases x with
  | inl u =>
    cases u
    intro h
    have := congrFun h 2
    simp [vec] at this
  | inr y =>
    cases y with
    | inl a =>
      intro h
      have := congrFun h 1
      simp [vec] at this
    | inr ab =>
      intro h
      have := congrFun h 0
      simp [vec] at this

lemma vec_scale_unique (q : ℕ) [Fact (Nat.Prime q)] {c : ZMod q} {x y : Pt q}
    (hc : c ≠ 0) (h : c • vec q x = vec q y) : c = 1 ∧ x = y := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  cases x with
  | inl ux =>
    cases ux
    cases y with
    | inl uy =>
      cases uy
      simp [vec] at h2
      exact ⟨h2, rfl⟩
    | inr y =>
      cases y with
      | inl a => simp [vec] at h1
      | inr ab => simp [vec] at h0
  | inr x =>
    cases x with
    | inl ax =>
      cases y with
      | inl uy =>
        cases uy
        simp [vec] at h1
        exact absurd h1 hc
      | inr y =>
        cases y with
        | inl ay =>
          simp [vec] at h1 h2
          subst h1
          simp at h2
          exact ⟨rfl, by rw [h2]⟩
        | inr ab => simp [vec] at h0
    | inr abx =>
      rcases abx with ⟨a, b⟩
      cases y with
      | inl uy =>
        cases uy
        simp [vec] at h0
        exact absurd h0 hc
      | inr y =>
        cases y with
        | inl ay =>
          simp [vec] at h0
          exact absurd h0 hc
        | inr aby =>
          rcases aby with ⟨a', b'⟩
          simp [vec] at h0 h1 h2
          subst h0
          simp at h1 h2
          exact ⟨rfl, by rw [h1, h2]⟩

lemma exists_rep (q : ℕ) [Fact (Nat.Prime q)] {v : Fin 3 → ZMod q} (hv : v ≠ 0) :
    ∃ (c : ZMod q) (x : Pt q), c ≠ 0 ∧ v = c • vec q x := by
  by_cases h0 : v 0 ≠ 0
  · refine ⟨v 0, Sum.inr (Sum.inr ((v 0)⁻¹ * v 1, (v 0)⁻¹ * v 2)), h0, ?_⟩
    funext i
    fin_cases i <;> simp [vec, ← mul_assoc, mul_inv_cancel₀ h0]
  · push_neg at h0
    by_cases h1 : v 1 ≠ 0
    · refine ⟨v 1, Sum.inr (Sum.inl ((v 1)⁻¹ * v 2)), h1, ?_⟩
      funext i
      fin_cases i <;> simp [vec, h0, ← mul_assoc, mul_inv_cancel₀ h1]
    · push_neg at h1
      have h2 : v 2 ≠ 0 := by
        intro h2
        apply hv
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      refine ⟨v 2, Sum.inl (), h2, ?_⟩
      funext i
      fin_cases i <;> simp [vec, h0, h1]

lemma card_orth_one (q : ℕ) [Fact (Nat.Prime q)] (v : Fin 3 → ZMod q) (hv : v ≠ 0) :
    ((Finset.univ : Finset (Pt q)).filter (fun y => dot3 v (vec q y) = 0)).card = q + 1 := by
  classical
  let W0 : Finset (Fin 3 → ZMod q) := Finset.univ.filter (fun w => dot3 v w = 0)
  have hW0_card : W0.card = q * q := by
    have hbij : ∀ (i0 i1 i2 : Fin 3), v i0 ≠ 0 → i0 ≠ i1 → i0 ≠ i2 → i1 ≠ i2 →
        (∀ w : Fin 3 → ZMod q, dot3 v w = v i0 * w i0 + v i1 * w i1 + v i2 * w i2) →
        W0.card = q * q := by
      intro i0 i1 i2 hvi0 h01 h02 h12 hdot
      have hcard_pair : (Finset.univ : Finset (ZMod q × ZMod q)).card = q * q := by
        simp [ZMod.card]
      rw [← hcard_pair]
      refine card_bij (fun w _ => (w i1, w i2)) ?_ ?_ ?_
      · intro _ _; exact mem_univ _
      · intro w1 hw1 w2 hw2 heq
        have h1 : w1 i1 = w2 i1 := congrArg Prod.fst heq
        have h2 : w1 i2 = w2 i2 := congrArg Prod.snd heq
        have hd1 := (mem_filter.1 hw1).2
        have hd2 := (mem_filter.1 hw2).2
        rw [hdot w1] at hd1
        rw [hdot w2, ← h1, ← h2] at hd2
        have h0 : w1 i0 = w2 i0 := by
          have : v i0 * w1 i0 = v i0 * w2 i0 := by linear_combination hd1 - hd2
          exact mul_left_cancel₀ hvi0 this
        funext i
        have hall : i = i0 ∨ i = i1 ∨ i = i2 := by
          fin_cases i0 <;> fin_cases i1 <;> fin_cases i2 <;> fin_cases i <;>
            simp_all
        rcases hall with rfl | rfl | rfl <;> assumption
      · intro ab _
        rcases ab with ⟨a, b⟩
        let w : Fin 3 → ZMod q := fun i =>
          if i = i1 then a else if i = i2 then b else -(v i0)⁻¹ * (v i1 * a + v i2 * b)
        have hw1 : w i1 = a := by simp [w]
        have hw2 : w i2 = b := by simp [w, h12.symm]
        have hw0 : w i0 = -(v i0)⁻¹ * (v i1 * a + v i2 * b) := by simp [w, h01, h02]
        refine ⟨w, mem_filter.2 ⟨mem_univ _, ?_⟩, Prod.ext hw1 hw2⟩
        rw [hdot w, hw0, hw1, hw2]
        have : v i0 * (-(v i0)⁻¹ * (v i1 * a + v i2 * b)) = -(v i1 * a + v i2 * b) := by
          rw [← mul_assoc, mul_neg, mul_inv_cancel₀ hvi0, neg_one_mul]
        rw [this]
        ring
    by_cases h0 : v 0 ≠ 0
    · exact hbij 0 1 2 h0 (by decide) (by decide) (by decide) (fun _ => rfl)
    · push_neg at h0
      by_cases h1 : v 1 ≠ 0
      · exact hbij 1 0 2 h1 (by decide) (by decide) (by decide) (fun w => by unfold dot3; ring)
      · push_neg at h1
        have h2 : v 2 ≠ 0 := by
          intro h2; apply hv; funext i; fin_cases i <;> simp [h0, h1, h2]
        exact hbij 2 0 1 h2 (by decide) (by decide) (by decide) (fun w => by unfold dot3; ring)
  let Wnz := W0.erase 0
  have h0_mem : (0 : Fin 3 → ZMod q) ∈ W0 := mem_filter.2 ⟨mem_univ _, by simp [dot3]⟩
  have hWnz_card : Wnz.card = q * q - 1 := by
    rw [card_erase_of_mem h0_mem, hW0_card]
  let Orth := (Finset.univ : Finset (Pt q)).filter (fun y => dot3 v (vec q y) = 0)
  let Units := (Finset.univ : Finset (ZMod q)).erase 0
  have hUnits_card : Units.card = q - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  have hWnz_eq : Wnz.card = Units.card * Orth.card := by
    rw [← card_product]
    refine card_bij (fun w hw => ?_) ?_ ?_ ?_
    · exact ((exists_rep q (ne_of_mem_erase hw)).choose,
        (exists_rep q (ne_of_mem_erase hw)).choose_spec.choose)
    · intro w hw
      have hspec := (exists_rep q (ne_of_mem_erase hw)).choose_spec.choose_spec
      refine mem_product.2 ⟨mem_erase.2 ⟨hspec.1, mem_univ _⟩, mem_filter.2 ⟨mem_univ _, ?_⟩⟩
      have hd : dot3 v w = 0 := (mem_filter.1 (mem_of_mem_erase hw)).2
      rw [hspec.2] at hd
      have hdot_smul : dot3 v ((exists_rep q (ne_of_mem_erase hw)).choose •
          vec q (exists_rep q (ne_of_mem_erase hw)).choose_spec.choose) =
          (exists_rep q (ne_of_mem_erase hw)).choose *
          dot3 v (vec q (exists_rep q (ne_of_mem_erase hw)).choose_spec.choose) := by
        simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring
      rw [hdot_smul] at hd
      exact (mul_eq_zero.1 hd).resolve_left hspec.1
    · intro w1 hw1 w2 hw2 heq
      set c1 := (exists_rep q (ne_of_mem_erase hw1)).choose
      set x1 := (exists_rep q (ne_of_mem_erase hw1)).choose_spec.choose
      set c2 := (exists_rep q (ne_of_mem_erase hw2)).choose
      set x2 := (exists_rep q (ne_of_mem_erase hw2)).choose_spec.choose
      have h1 : w1 = c1 • vec q x1 := (exists_rep q (ne_of_mem_erase hw1)).choose_spec.choose_spec.2
      have h2 : w2 = c2 • vec q x2 := (exists_rep q (ne_of_mem_erase hw2)).choose_spec.choose_spec.2
      have hc : c1 = c2 := congrArg Prod.fst heq
      have hx : x1 = x2 := congrArg Prod.snd heq
      rw [h1, h2, hc, hx]
    · intro cy hcy
      rcases cy with ⟨c, y⟩
      have ⟨hc, hy⟩ := mem_product.1 hcy
      have hc0 : c ≠ 0 := ne_of_mem_erase hc
      have hy0 : dot3 v (vec q y) = 0 := (mem_filter.1 hy).2
      have hwnz : c • vec q y ∈ Wnz := by
        refine mem_erase.2 ⟨fun h0 => vec_ne_zero q y ((smul_eq_zero.1 h0).resolve_left hc0),
          mem_filter.2 ⟨mem_univ _, ?_⟩⟩
        have : dot3 v (c • vec q y) = c * dot3 v (vec q y) := by
          simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring
        rw [this, hy0, mul_zero]
      refine ⟨c • vec q y, hwnz, ?_⟩
      have hspec := (exists_rep q (ne_of_mem_erase hwnz)).choose_spec.choose_spec
      have heq : (c⁻¹ * (exists_rep q (ne_of_mem_erase hwnz)).choose) •
          vec q (exists_rep q (ne_of_mem_erase hwnz)).choose_spec.choose = vec q y := by
        rw [mul_smul, ← hspec.2, inv_smul_smul₀ hc0]
      have ⟨hcu, hxy⟩ := vec_scale_unique q (mul_ne_zero (inv_ne_zero hc0) hspec.1) heq
      have hc_eq : (exists_rep q (ne_of_mem_erase hwnz)).choose = c := by
        have := congrArg (fun z => c * z) hcu
        simpa [← mul_assoc, mul_inv_cancel₀ hc0] using this
      exact Prod.ext hc_eq hxy
  rw [hWnz_card, hUnits_card] at hWnz_eq
  have hq2 : 2 ≤ q := (Fact.out : Nat.Prime q).two_le
  have hfactor : q * q - 1 = (q - 1) * (q + 1) := by
    zify [show 1 ≤ q * q by nlinarith, show 1 ≤ q by omega]
    ring
  rw [hfactor] at hWnz_eq
  exact (Nat.mul_left_cancel (by omega : 0 < q - 1) hWnz_eq).symm

lemma card_orth_two (q : ℕ) [Fact (Nat.Prime q)] (x1 x2 : Pt q) (hne : x1 ≠ x2) :
    ((Finset.univ : Finset (Pt q)).filter
      (fun y => dot3 (vec q x1) (vec q y) = 0 ∧ dot3 (vec q x2) (vec q y) = 0)).card = 1 := by
  classical
  let u := vec q x1
  let v := vec q x2
  let w0 : Fin 3 → ZMod q :=
    ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]
  have hw0_u : dot3 u w0 = 0 := by simp [dot3, w0]; ring
  have hw0_v : dot3 v w0 = 0 := by simp [dot3, w0]; ring
  have hw0_ne : w0 ≠ 0 := by
    intro h0
    have e0 : u 1 * v 2 = u 2 * v 1 := sub_eq_zero.1 (congrFun h0 0)
    have e1 : u 2 * v 0 = u 0 * v 2 := sub_eq_zero.1 (congrFun h0 1)
    have e2 : u 0 * v 1 = u 1 * v 0 := sub_eq_zero.1 (congrFun h0 2)
    have hscale : ∃ c : ZMod q, c ≠ 0 ∧ c • u = v := by
      by_cases hu0 : u 0 ≠ 0
      · have hv0 : v 0 ≠ 0 := by
          intro hv0
          have hv1 : v 1 = 0 := by
            rw [hv0, mul_zero] at e2; exact (mul_eq_zero.1 e2).resolve_left hu0
          have hv2 : v 2 = 0 := by
            rw [hv0, mul_zero] at e1; exact (mul_eq_zero.1 e1.symm).resolve_left hu0
          apply vec_ne_zero q x2
          funext i; fin_cases i <;> simp [v, hv0, hv1, hv2]
        refine ⟨v 0 * (u 0)⁻¹, mul_ne_zero hv0 (inv_ne_zero hu0), ?_⟩
        funext i
        fin_cases i
        · simp [mul_assoc, inv_mul_cancel₀ hu0]
        · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
          have : u 0 * (v 0 * (u 0)⁻¹ * u 1) = u 0 * v 1 := by
            calc u 0 * (v 0 * (u 0)⁻¹ * u 1) = (u 0 * (u 0)⁻¹) * (u 1 * v 0) := by ring
              _ = u 1 * v 0 := by rw [mul_inv_cancel₀ hu0, one_mul]
              _ = u 0 * v 1 := e2.symm
          exact mul_left_cancel₀ hu0 this
        · simp only [Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
          have : u 0 * (v 0 * (u 0)⁻¹ * u 2) = u 0 * v 2 := by
            calc u 0 * (v 0 * (u 0)⁻¹ * u 2) = (u 0 * (u 0)⁻¹) * (u 2 * v 0) := by ring
              _ = u 2 * v 0 := by rw [mul_inv_cancel₀ hu0, one_mul]
              _ = u 0 * v 2 := e1
          exact mul_left_cancel₀ hu0 this
      · push_neg at hu0
        by_cases hu1 : u 1 ≠ 0
        · have hv0 : v 0 = 0 := by
            rw [hu0, zero_mul] at e2; exact (mul_eq_zero.1 e2.symm).resolve_left hu1
          have hv1 : v 1 ≠ 0 := by
            intro hv1
            have hv2 : v 2 = 0 := by
              rw [hv1, mul_zero] at e0; exact (mul_eq_zero.1 e0).resolve_left hu1
            apply vec_ne_zero q x2
            funext i; fin_cases i <;> simp [v, hv0, hv1, hv2]
          refine ⟨v 1 * (u 1)⁻¹, mul_ne_zero hv1 (inv_ne_zero hu1), ?_⟩
          funext i
          fin_cases i
          · simp [hu0, hv0]
          · simp [mul_assoc, inv_mul_cancel₀ hu1]
          · simp only [Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
            have : u 1 * (v 1 * (u 1)⁻¹ * u 2) = u 1 * v 2 := by
              calc u 1 * (v 1 * (u 1)⁻¹ * u 2) = (u 1 * (u 1)⁻¹) * (u 2 * v 1) := by ring
                _ = u 2 * v 1 := by rw [mul_inv_cancel₀ hu1, one_mul]
                _ = u 1 * v 2 := e0.symm
            exact mul_left_cancel₀ hu1 this
        · push_neg at hu1
          have hu2 : u 2 ≠ 0 := by
            intro hu2; apply vec_ne_zero q x1; funext i; fin_cases i <;> simp [u, hu0, hu1, hu2]
          have hv0 : v 0 = 0 := by
            rw [hu0, zero_mul] at e1; exact (mul_eq_zero.1 e1).resolve_left hu2
          have hv1 : v 1 = 0 := by
            rw [hu1, zero_mul] at e0; exact (mul_eq_zero.1 e0.symm).resolve_left hu2
          have hv2 : v 2 ≠ 0 := by
            intro hv2; apply vec_ne_zero q x2; funext i; fin_cases i <;> simp [v, hv0, hv1, hv2]
          refine ⟨v 2 * (u 2)⁻¹, mul_ne_zero hv2 (inv_ne_zero hu2), ?_⟩
          funext i
          fin_cases i
          · simp [hu0, hv0]
          · simp [hu1, hv1]
          · simp [mul_assoc, inv_mul_cancel₀ hu2]
    obtain ⟨c, hc, hcu⟩ := hscale
    exact hne (vec_scale_unique q hc hcu).2
  obtain ⟨c0, y0, hc0, hw0_eq⟩ := exists_rep q hw0_ne
  have hy0_mem : dot3 u (vec q y0) = 0 ∧ dot3 v (vec q y0) = 0 := by
    have hdot_smul : ∀ (a : Fin 3 → ZMod q), dot3 a (c0 • vec q y0) = c0 * dot3 a (vec q y0) := by
      intro a; simp only [dot3, Pi.smul_apply, smul_eq_mul]; ring
    rw [hw0_eq, hdot_smul] at hw0_u hw0_v
    exact ⟨(mul_eq_zero.1 hw0_u).resolve_left hc0, (mul_eq_zero.1 hw0_v).resolve_left hc0⟩
  have hsing : (Finset.univ : Finset (Pt q)).filter
      (fun y => dot3 u (vec q y) = 0 ∧ dot3 v (vec q y) = 0) = {y0} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hyu, hyv⟩
      set w := vec q y
      have hcross0 : w0 0 * w 1 = w 0 * w0 1 ∧ w0 0 * w 2 = w 0 * w0 2 := by
        constructor
        · dsimp only [w0, dot3] at hyu hyv ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          linear_combination v 2 * hyu - u 2 * hyv
        · dsimp only [w0, dot3] at hyu hyv ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          linear_combination (-v 1) * hyu + u 1 * hyv
      have hcross1 : w0 1 * w 0 = w 1 * w0 0 ∧ w0 1 * w 2 = w 1 * w0 2 := by
        constructor
        · rw [mul_comm (w0 1), mul_comm (w 1)]; exact hcross0.1.symm
        · dsimp only [w0, dot3] at hyu hyv ⊢
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
          linear_combination v 0 * hyu - u 0 * hyv
      have hcross2 : w0 2 * w 0 = w 2 * w0 0 ∧ w0 2 * w 1 = w 2 * w0 1 := by
        constructor
        · rw [mul_comm (w0 2), mul_comm (w 2)]; exact hcross0.2.symm
        · rw [mul_comm (w0 2), mul_comm (w 2)]; exact hcross1.2.symm
      have hmul_w : ∃ t : ZMod q, w = t • w0 := by
        by_cases h0 : w0 0 ≠ 0
        · refine ⟨w 0 * (w0 0)⁻¹, ?_⟩
          funext i; fin_cases i
          · simp [mul_assoc, inv_mul_cancel₀ h0]
          · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
            exact mul_left_cancel₀ h0 (by
              calc w0 0 * w 1 = w 0 * w0 1 := hcross0.1
                _ = w0 0 * (w 0 * (w0 0)⁻¹ * w0 1) := by
                    rw [show w0 0 * (w 0 * (w0 0)⁻¹ * w0 1) = (w0 0 * (w0 0)⁻¹) * (w 0 * w0 1) by ring,
                      mul_inv_cancel₀ h0, one_mul])
          · simp only [Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
            exact mul_left_cancel₀ h0 (by
              calc w0 0 * w 2 = w 0 * w0 2 := hcross0.2
                _ = w0 0 * (w 0 * (w0 0)⁻¹ * w0 2) := by
                    rw [show w0 0 * (w 0 * (w0 0)⁻¹ * w0 2) = (w0 0 * (w0 0)⁻¹) * (w 0 * w0 2) by ring,
                      mul_inv_cancel₀ h0, one_mul])
        · push_neg at h0
          by_cases h1 : w0 1 ≠ 0
          · refine ⟨w 1 * (w0 1)⁻¹, ?_⟩
            funext i; fin_cases i
            · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
              exact mul_left_cancel₀ h1 (by
                calc w0 1 * w 0 = w 1 * w0 0 := hcross1.1
                  _ = w0 1 * (w 1 * (w0 1)⁻¹ * w0 0) := by
                      rw [show w0 1 * (w 1 * (w0 1)⁻¹ * w0 0) = (w0 1 * (w0 1)⁻¹) * (w 1 * w0 0) by ring,
                        mul_inv_cancel₀ h1, one_mul])
            · simp [mul_assoc, inv_mul_cancel₀ h1]
            · simp only [Pi.smul_apply, smul_eq_mul, Fin.reduceFinMk]
              exact mul_left_cancel₀ h1 (by
                calc w0 1 * w 2 = w 1 * w0 2 := hcross1.2
                  _ = w0 1 * (w 1 * (w0 1)⁻¹ * w0 2) := by
                      rw [show w0 1 * (w 1 * (w0 1)⁻¹ * w0 2) = (w0 1 * (w0 1)⁻¹) * (w 1 * w0 2) by ring,
                        mul_inv_cancel₀ h1, one_mul])
          · push_neg at h1
            have h2 : w0 2 ≠ 0 := by
              intro h2; apply hw0_ne; funext i; fin_cases i <;> simp [h0, h1, h2]
            refine ⟨w 2 * (w0 2)⁻¹, ?_⟩
            funext i; fin_cases i
            · simp only [Pi.smul_apply, smul_eq_mul, Fin.zero_eta]
              exact mul_left_cancel₀ h2 (by
                calc w0 2 * w 0 = w 2 * w0 0 := hcross2.1
                  _ = w0 2 * (w 2 * (w0 2)⁻¹ * w0 0) := by
                      rw [show w0 2 * (w 2 * (w0 2)⁻¹ * w0 0) = (w0 2 * (w0 2)⁻¹) * (w 2 * w0 0) by ring,
                        mul_inv_cancel₀ h2, one_mul])
            · simp only [Pi.smul_apply, smul_eq_mul, Fin.mk_one]
              exact mul_left_cancel₀ h2 (by
                calc w0 2 * w 1 = w 2 * w0 1 := hcross2.2
                  _ = w0 2 * (w 2 * (w0 2)⁻¹ * w0 1) := by
                      rw [show w0 2 * (w 2 * (w0 2)⁻¹ * w0 1) = (w0 2 * (w0 2)⁻¹) * (w 2 * w0 1) by ring,
                        mul_inv_cancel₀ h2, one_mul])
            · simp [mul_assoc, inv_mul_cancel₀ h2]
      obtain ⟨t, ht⟩ := hmul_w
      have ht0 : t ≠ 0 := by
        intro htz; rw [htz, zero_smul] at ht; exact vec_ne_zero q y ht
      rw [hw0_eq, smul_smul] at ht
      exact (vec_scale_unique q (mul_ne_zero ht0 hc0) ht.symm).2.symm
    · rintro rfl; exact hy0_mem
  rw [hsing, card_singleton]

noncomputable def projMat (q : ℕ) : Matrix (Pt q) (Pt q) ℝ :=
  fun x y => if dot3 (vec q x) (vec q y) = 0 then 1 else 0

lemma projMat_det_sq (q : ℕ) [Fact (Nat.Prime q)] :
    (projMat q).det ^ 2 = ((q + 1 : ℝ) ^ 2) * (q : ℝ) ^ (Fintype.card (Pt q) - 1) := by
  classical
  have hsymm : (projMat q)ᵀ = projMat q := by
    ext x y
    simp only [Matrix.transpose_apply, projMat]
    have : dot3 (vec q y) (vec q x) = dot3 (vec q x) (vec q y) := by unfold dot3; ring
    rw [this]
  have hgram : projMat q * (projMat q)ᵀ =
      (q : ℝ) • (1 : Matrix (Pt q) (Pt q) ℝ) + Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext x1 x2
    rw [hsymm, Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply]
    have hsum : ∑ y : Pt q, projMat q x1 y * projMat q y x2 =
        (((Finset.univ : Finset (Pt q)).filter
          (fun y => dot3 (vec q x1) (vec q y) = 0 ∧ dot3 (vec q x2) (vec q y) = 0)).card : ℝ) := by
      rw [← sum_boole]
      refine sum_congr rfl fun y _ => ?_
      simp only [projMat]
      have hcomm : dot3 (vec q y) (vec q x2) = dot3 (vec q x2) (vec q y) := by unfold dot3; ring
      rw [hcomm]
      by_cases h1 : dot3 (vec q x1) (vec q y) = 0 <;> by_cases h2 : dot3 (vec q x2) (vec q y) = 0 <;>
        simp [h1, h2]
    rw [hsum]
    by_cases heq : x1 = x2
    · subst heq
      have hflt : (Finset.univ : Finset (Pt q)).filter
          (fun y => dot3 (vec q x1) (vec q y) = 0 ∧ dot3 (vec q x1) (vec q y) = 0) =
          (Finset.univ : Finset (Pt q)).filter (fun y => dot3 (vec q x1) (vec q y) = 0) := by
        ext y; simp
      rw [hflt, card_orth_one q (vec q x1) (vec_ne_zero q x1)]
      simp [smul_eq_mul]
    · rw [card_orth_two q x1 x2 heq]
      simp [heq]
  have hcard : Fintype.card (Pt q) = 1 + q + q * q := by
    simp [Pt, ZMod.card, add_assoc]
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 (Fact.out : Nat.Prime q).pos
  let A : Matrix (Pt q) (Fin 1) ℝ := Matrix.of (fun _ _ => (q : ℝ)⁻¹)
  let B : Matrix (Fin 1) (Pt q) ℝ := Matrix.of (fun _ _ => 1)
  have hfact : projMat q * (projMat q)ᵀ = (q : ℝ) • (1 + A * B) := by
    rw [hgram]
    ext x y
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      Matrix.mul_apply, A, B, Fintype.sum_unique, smul_eq_mul, mul_one, mul_add]
    rw [mul_inv_cancel₀ hqpos.ne']
  have hdet_sq : (projMat q).det ^ 2 = (projMat q * (projMat q)ᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_transpose, sq]
  rw [hdet_sq, hfact, Matrix.det_smul, Matrix.det_one_add_mul_comm]
  have h1BA : (1 + B * A).det = ((q + 1 : ℝ) ^ 2) / (q : ℝ) := by
    rw [Matrix.det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, A, B, Matrix.of_apply,
      one_mul, sum_const, card_univ, nsmul_eq_mul, hcard]
    push_cast
    field_simp [hqpos.ne']
    ring
  rw [h1BA]
  have hm1 : 1 ≤ Fintype.card (Pt q) := by omega
  have hpow : (q : ℝ) ^ Fintype.card (Pt q) = (q : ℝ) * (q : ℝ) ^ (Fintype.card (Pt q) - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hm1, pow_succ']
  rw [hpow]
  field_simp [hqpos.ne']

lemma projMat_exists (q : ℕ) [Fact (Nat.Prime q)] :
    let m := q ^ 2 + q + 1
    ∃ M : Matrix (Fin m) (Fin m) ℝ,
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧
      (∀ i, ((Finset.univ : Finset (Fin m)).filter (fun j => M i j = 1)).card = q + 1) ∧
      (∀ j, ((Finset.univ : Finset (Fin m)).filter (fun i => M i j = 1)).card = q + 1) ∧
      0 < M.permanent ∧
      (q : ℝ) ^ m ≤ M.det ^ 2 ∧
      M.permanent ^ (q + 1) ≤ ((q + 1).factorial : ℝ) ^ m := by
  classical
  intro m
  have hcard : Fintype.card (Pt q) = m := by
    simp [Pt, ZMod.card, m, sq]; ring
  let e : Fin m ≃ Pt q := (Fintype.equivFinOfCardEq hcard).symm
  let M : Matrix (Fin m) (Fin m) ℝ := (projMat q).submatrix e e
  have hbin : ∀ i j, M i j = 0 ∨ M i j = 1 := by
    intro i j
    simp only [M, Matrix.submatrix_apply, projMat]
    split_ifs <;> simp
  have hrow : ∀ i, ((Finset.univ : Finset (Fin m)).filter (fun j => M i j = 1)).card = q + 1 := by
    intro i
    have hbij : ((Finset.univ : Finset (Fin m)).filter (fun j => M i j = 1)).card =
        ((Finset.univ : Finset (Pt q)).filter (fun y => dot3 (vec q (e i)) (vec q y) = 0)).card := by
      refine card_bij (fun j _ => e j) ?_ ?_ ?_
      · intro j hj
        have h1 := (mem_filter.1 hj).2
        simp only [M, Matrix.submatrix_apply, projMat] at h1
        refine mem_filter.2 ⟨mem_univ _, ?_⟩
        by_contra hne
        simp [hne] at h1
      · intro j1 _ j2 _ h; exact e.injective h
      · intro y hy
        refine ⟨e.symm y, mem_filter.2 ⟨mem_univ _, ?_⟩, e.apply_symm_apply y⟩
        simp [M, projMat, (mem_filter.1 hy).2]
    exact hbij.trans (card_orth_one q (vec q (e i)) (vec_ne_zero q (e i)))
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    simp only [M, Matrix.submatrix_apply, projMat]
    have : dot3 (vec q (e i)) (vec q (e j)) = dot3 (vec q (e j)) (vec q (e i)) := by unfold dot3; ring
    rw [this]
  have hcol : ∀ j, ((Finset.univ : Finset (Fin m)).filter (fun i => M i j = 1)).card = q + 1 := by
    intro j
    simpa only [hsymm] using hrow j
  have hdet_eq : M.det ^ 2 = ((q + 1 : ℝ) ^ 2) * (q : ℝ) ^ (m - 1) := by
    have hd : M.det = (projMat q).det := Matrix.det_submatrix_equiv_self e (projMat q)
    rw [hd, projMat_det_sq q, hcard]
  have hqpos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.2 (Fact.out : Nat.Prime q).pos
  have hdet_ge : (q : ℝ) ^ m ≤ M.det ^ 2 := by
    rw [hdet_eq]
    have hm1 : 1 ≤ m := by omega
    have hpow : (q : ℝ) ^ m = (q : ℝ) * (q : ℝ) ^ (m - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm1, pow_succ']
    rw [hpow]
    have hqle : (q : ℝ) ≤ (q + 1 : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hqle (by positivity)
  have hperm_pos : 0 < M.permanent := by
    have hdet_ne : M.det ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by norm_num)] at hdet_ge
      linarith [pow_pos hqpos m]
    have hex : ∃ σ : Equiv.Perm (Fin m), ∏ i, M (σ i) i ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hdet_ne
      rw [Matrix.det_apply]
      exact sum_eq_zero fun σ _ => by simp [hall σ]
    obtain ⟨σ0, hσ0⟩ := hex
    have hterm_nonneg : ∀ σ : Equiv.Perm (Fin m), 0 ≤ ∏ i, M (σ i) i := fun σ =>
      prod_nonneg fun i _ => by rcases hbin (σ i) i with h | h <;> linarith
    have hterm_pos : 0 < ∏ i, M (σ0 i) i := by
      have : ∏ i, M (σ0 i) i = 1 := prod_eq_one fun i _ => by
        rcases hbin (σ0 i) i with h | h
        · exact absurd (prod_eq_zero (f := fun j => M (σ0 j) j) (mem_univ i) h) hσ0
        · exact h
      linarith
    rw [Matrix.permanent]
    exact lt_of_lt_of_le hterm_pos (single_le_sum (fun σ _ => hterm_nonneg σ) (mem_univ σ0))
  have hbreg := bregman_regular (Nat.succ_pos q) M hbin hrow
  exact ⟨M, hbin, hrow, hcol, hperm_pos, hdet_ge, hbreg⟩

end ProjPlane

section BlockAndSign

lemma permanent_submatrix_equiv_self {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (M : Matrix β β ℝ) :
    (M.submatrix e e).permanent = M.permanent := by
  classical
  rw [Matrix.permanent, Matrix.permanent]
  let conj : Equiv.Perm α ≃ Equiv.Perm β :=
    { toFun := fun σ => e.symm.trans (σ.trans e)
      invFun := fun τ => e.trans (τ.trans e.symm)
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext y; simp }
  refine Fintype.sum_equiv conj _ _ fun σ => ?_
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [conj]

lemma permanent_fromBlocks_zero {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix α α ℝ) (D : Matrix β β ℝ) :
    (Matrix.fromBlocks A 0 0 D).permanent = A.permanent * D.permanent := by
  classical
  rw [Matrix.permanent, Matrix.permanent, Matrix.permanent, sum_mul]
  simp_rw [mul_sum]
  rw [← sum_product']
  let embed : Equiv.Perm α × Equiv.Perm β ↪ Equiv.Perm (α ⊕ β) :=
    ⟨fun p => Equiv.sumCongr p.1 p.2, by
      rintro ⟨σ1, τ1⟩ ⟨σ2, τ2⟩ h
      exact Prod.ext
        (Equiv.ext fun a => by simpa using Equiv.congr_fun h (Sum.inl a))
        (Equiv.ext fun b => by simpa using Equiv.congr_fun h (Sum.inr b))⟩
  have hzero : ∀ π : Equiv.Perm (α ⊕ β),
      π ∉ Finset.univ.map embed → ∏ x : α ⊕ β, Matrix.fromBlocks A 0 0 D (π x) x = 0 := by
    intro π hnot
    by_cases hL : ∀ a : α, ∃ a' : α, π (Sum.inl a) = Sum.inl a'
    · by_cases hR : ∀ b : β, ∃ b' : β, π (Sum.inr b) = Sum.inr b'
      · exfalso
        apply hnot
        choose f hf using hL
        choose g hg using hR
        have hfinj : Function.Injective f := fun a1 a2 h => by
          have : π (Sum.inl a1) = π (Sum.inl a2) := by rw [hf a1, hf a2, h]
          exact Sum.inl.inj (π.injective this)
        have hginj : Function.Injective g := fun b1 b2 h => by
          have : π (Sum.inr b1) = π (Sum.inr b2) := by rw [hg b1, hg b2, h]
          exact Sum.inr.inj (π.injective this)
        let σ : Equiv.Perm α := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj)
        let τ : Equiv.Perm β := Equiv.ofBijective g (Finite.injective_iff_bijective.1 hginj)
        refine mem_map.2 ⟨(σ, τ), mem_univ _, ?_⟩
        ext x
        cases x with
        | inl a => exact (hf a).symm
        | inr b => exact (hg b).symm
      · push_neg at hR
        obtain ⟨b, hb⟩ := hR
        cases hπb : π (Sum.inr b) with
        | inl a => exact prod_eq_zero (mem_univ (Sum.inr b)) (by simp [hπb])
        | inr b' => exact absurd hπb (hb b')
    · push_neg at hL
      obtain ⟨a, ha⟩ := hL
      cases hπa : π (Sum.inl a) with
      | inl a' => exact absurd hπa (ha a')
      | inr b => exact prod_eq_zero (mem_univ (Sum.inl a)) (by simp [hπa])
  rw [← sum_subset (subset_univ (Finset.univ.map embed)) (fun π _ h => hzero π h)]
  rw [sum_map]
  refine sum_congr rfl fun p _ => ?_
  rcases p with ⟨σ, τ⟩
  rw [Fintype.prod_sum_type]
  rfl

lemma permanent_blockDiagonal_const {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    ∀ k : ℕ, (Matrix.blockDiagonal (fun _ : Fin k => M)).permanent = M.permanent ^ k
  | 0 => by
    have : IsEmpty (Fin m × Fin 0) := inferInstance
    rw [Matrix.permanent_isEmpty, pow_zero]
  | k + 1 => by
    let e : (Fin m × Fin k) ⊕ Fin m ≃ Fin m × Fin (k + 1) :=
      { toFun := Sum.elim (fun p => (p.1, p.2.castSucc)) (fun a => (a, Fin.last k))
        invFun := fun p => if h : p.2.val < k then Sum.inl (p.1, ⟨p.2.val, h⟩) else Sum.inr p.1
        left_inv := fun x => by
          cases x with
          | inl p => simp [p.2.isLt]
          | inr a => simp
        right_inv := fun p => by
          rcases p with ⟨a, j⟩
          by_cases hj : j.val < k
          · simp [hj]
          · have hlast : j = Fin.last k := Fin.ext (by have := j.isLt; simp [Fin.last]; omega)
            subst hlast
            simp }
    have hsub : (Matrix.blockDiagonal (fun _ : Fin (k + 1) => M)).submatrix e e =
        Matrix.fromBlocks (Matrix.blockDiagonal (fun _ : Fin k => M)) 0 0 M := by
      ext x y
      cases x with
      | inl p =>
        cases y with
        | inl q => simp [e, Matrix.blockDiagonal_apply, Fin.castSucc_inj]
        | inr b => simp [e, Matrix.blockDiagonal_apply, Fin.castSucc_ne_last]
      | inr a =>
        cases y with
        | inl q => simp [e, Matrix.blockDiagonal_apply, (Fin.castSucc_ne_last q.2).symm]
        | inr b => simp [e, Matrix.blockDiagonal_apply]
    rw [← permanent_submatrix_equiv_self e, hsub, permanent_fromBlocks_zero,
      permanent_blockDiagonal_const M k, pow_succ]

lemma extract_sign_blocks {n m : ℕ} (hm : 0 < m) (s : Fin n × Fin n → Bool) :
    ∀ (k : ℕ) (R C : Finset (Fin n)),
      R.card = C.card → m * 2 ^ m + m * k ≤ R.card →
      ∃ (u v : Fin k × Fin m ↪ Fin n),
        (∀ x, u x ∈ R) ∧ (∀ x, v x ∈ C) ∧
        ∀ (t : Fin k) (a1 a2 b : Fin m), s (u (t, a1), v (t, b)) = s (u (t, a2), v (t, b))
  | 0, R, C, _, _ => by
    refine ⟨⟨fun x => x.1.elim0, fun x => x.1.elim0⟩, ⟨fun x => x.1.elim0, fun x => x.1.elim0⟩,
      fun x => x.1.elim0, fun x => x.1.elim0, fun t => t.elim0⟩
  | k + 1, R, C, hRC, hle => by
    classical
    have hmC : m ≤ C.card := by
      have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
      nlinarith
    obtain ⟨C0, hC0sub, hC0card⟩ := Finset.exists_subset_card_eq hmC
    let eC : Fin m ≃ {x // x ∈ C0} := (Fintype.equivFinOfCardEq (by simp [hC0card])).symm
    let pat : Fin n → (Fin m → Bool) := fun r b => s (r, (eC b).1)
    have hfib_ex : ∃ f : Fin m → Bool, m ≤ (R.filter (fun r => pat r = f)).card := by
      by_contra hall
      push_neg at hall
      have hsum : R.card = ∑ f : Fin m → Bool, (R.filter (fun r => pat r = f)).card := by
        conv_lhs => rw [card_eq_sum_ones]
        rw [← sum_fiberwise_of_maps_to (g := pat) (t := Finset.univ)
          (fun _ _ => mem_univ _)]
        exact sum_congr rfl fun f _ => by simp
      have hlt : ∑ f : Fin m → Bool, (R.filter (fun r => pat r = f)).card <
          ∑ _f : Fin m → Bool, m :=
        sum_lt_sum_of_nonempty univ_nonempty fun f _ => hall f
      simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        smul_eq_mul] at hlt
      rw [← hsum, mul_comm (2 ^ m) m] at hlt
      omega
    obtain ⟨f, hf⟩ := hfib_ex
    obtain ⟨R0, hR0sub, hR0card⟩ := Finset.exists_subset_card_eq hf
    have hR0R : R0 ⊆ R := hR0sub.trans (filter_subset _ _)
    let eR : Fin m ≃ {x // x ∈ R0} := (Fintype.equivFinOfCardEq (by simp [hR0card])).symm
    have hRdiff : (R \ R0).card = R.card - m := by
      rw [card_sdiff_of_subset hR0R, hR0card]
    have hCdiff : (C \ C0).card = C.card - m := by
      rw [card_sdiff_of_subset hC0sub, hC0card]
    have hle' : m * 2 ^ m + m * k ≤ (R \ R0).card := by
      rw [hRdiff]; rw [Nat.mul_succ] at hle; omega
    obtain ⟨u', v', hu'R, hv'C, hsign'⟩ :=
      extract_sign_blocks hm s k (R \ R0) (C \ C0) (by omega) hle'
    let uFun : Fin (k + 1) × Fin m → Fin n := fun p =>
      if h : p.1.val < k then u' (⟨p.1.val, h⟩, p.2) else (eR p.2).1
    let vFun : Fin (k + 1) × Fin m → Fin n := fun p =>
      if h : p.1.val < k then v' (⟨p.1.val, h⟩, p.2) else (eC p.2).1
    have huInj : Function.Injective uFun := by
      rintro ⟨t1, a1⟩ ⟨t2, a2⟩ heq
      dsimp only [uFun] at heq
      by_cases h1 : t1.val < k <;> by_cases h2 : t2.val < k
      · simp only [dif_pos h1, dif_pos h2] at heq
        have hp := u'.injective heq
        exact Prod.ext (Fin.ext (congrArg (fun p : Fin k × Fin m => p.1.val) hp))
          (congrArg (fun p : Fin k × Fin m => p.2) hp)
      · simp only [dif_pos h1, dif_neg h2] at heq
        have hmem1 := hu'R (⟨t1.val, h1⟩, a1)
        rw [heq] at hmem1
        exact absurd (eR a2).2 (mem_sdiff.1 hmem1).2
      · simp only [dif_neg h1, dif_pos h2] at heq
        have hmem2 := hu'R (⟨t2.val, h2⟩, a2)
        rw [← heq] at hmem2
        exact absurd (eR a1).2 (mem_sdiff.1 hmem2).2
      · simp only [dif_neg h1, dif_neg h2] at heq
        have ha := eR.injective (Subtype.ext heq)
        exact Prod.ext (Fin.ext (by change t1.val = t2.val; have ht1 := t1.isLt; have ht2 := t2.isLt; omega)) ha
    have hvInj : Function.Injective vFun := by
      rintro ⟨t1, b1⟩ ⟨t2, b2⟩ heq
      dsimp only [vFun] at heq
      by_cases h1 : t1.val < k <;> by_cases h2 : t2.val < k
      · simp only [dif_pos h1, dif_pos h2] at heq
        have hp := v'.injective heq
        exact Prod.ext (Fin.ext (congrArg (fun p : Fin k × Fin m => p.1.val) hp))
          (congrArg (fun p : Fin k × Fin m => p.2) hp)
      · simp only [dif_pos h1, dif_neg h2] at heq
        have hmem1 := hv'C (⟨t1.val, h1⟩, b1)
        rw [heq] at hmem1
        exact absurd (eC b2).2 (mem_sdiff.1 hmem1).2
      · simp only [dif_neg h1, dif_pos h2] at heq
        have hmem2 := hv'C (⟨t2.val, h2⟩, b2)
        rw [← heq] at hmem2
        exact absurd (eC b1).2 (mem_sdiff.1 hmem2).2
      · simp only [dif_neg h1, dif_neg h2] at heq
        have hb := eC.injective (Subtype.ext heq)
        exact Prod.ext (Fin.ext (by change t1.val = t2.val; have ht1 := t1.isLt; have ht2 := t2.isLt; omega)) hb
    refine ⟨⟨uFun, huInj⟩, ⟨vFun, hvInj⟩, ?_, ?_, ?_⟩
    · rintro ⟨t, a⟩
      change uFun (t, a) ∈ R
      dsimp only [uFun]
      split_ifs with ht
      · exact (mem_sdiff.1 (hu'R (⟨t.val, ht⟩, a))).1
      · exact hR0R (eR a).2
    · rintro ⟨t, b⟩
      change vFun (t, b) ∈ C
      dsimp only [vFun]
      split_ifs with ht
      · exact (mem_sdiff.1 (hv'C (⟨t.val, ht⟩, b))).1
      · exact hC0sub (eC b).2
    · intro t a1 a2 b
      change s (uFun (t, a1), vFun (t, b)) = s (uFun (t, a2), vFun (t, b))
      dsimp only [uFun, vFun]
      split_ifs with ht
      · exact hsign' ⟨t.val, ht⟩ a1 a2 b
      · have h1 := (mem_filter.1 (hR0sub (eR a1).2)).2
        have h2 := (mem_filter.1 (hR0sub (eR a2).2)).2
        exact (congrFun h1 b).trans (congrFun h2 b).symm

lemma extend_embedding_to_perm {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) (S : Finset α)
    (f : {x // x ∈ S} ↪ β) :
    ∃ π : α ≃ β, ∀ (x : α) (hx : x ∈ S), π x = f ⟨x, hx⟩ := by
  classical
  let T : Finset β := S.attach.map f
  have hTcard : T.card = S.card := by
    rw [card_map, card_attach]
  have hcomp_card : (Finset.univ \ S).card = (Finset.univ \ T).card := by
    rw [card_sdiff_of_subset (subset_univ _), card_sdiff_of_subset (subset_univ _),
      card_univ, card_univ, Fintype.card_congr e, hTcard]
  let eRest : {x // x ∈ (Finset.univ \ S)} ≃ {y // y ∈ (Finset.univ \ T)} :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, Fintype.card_congr e, hTcard])
  let πFun : α → β := fun x =>
    if hx : x ∈ S then f ⟨x, hx⟩
    else (eRest ⟨x, mem_sdiff.2 ⟨mem_univ _, hx⟩⟩).1
  have hπInj : Function.Injective πFun := by
    intro x1 x2 heq
    dsimp only [πFun] at heq
    by_cases h1 : x1 ∈ S <;> by_cases h2 : x2 ∈ S
    · simp only [dif_pos h1, dif_pos h2] at heq
      exact congrArg Subtype.val (f.injective heq)
    · simp only [dif_pos h1, dif_neg h2] at heq
      have hmemT : f ⟨x1, h1⟩ ∈ T := mem_map.2 ⟨⟨x1, h1⟩, mem_attach _ _, rfl⟩
      rw [heq] at hmemT
      exact absurd hmemT (mem_sdiff.1 (eRest _).2).2
    · simp only [dif_neg h1, dif_pos h2] at heq
      have hmemT : f ⟨x2, h2⟩ ∈ T := mem_map.2 ⟨⟨x2, h2⟩, mem_attach _ _, rfl⟩
      rw [← heq] at hmemT
      exact absurd hmemT (mem_sdiff.1 (eRest _).2).2
    · simp only [dif_neg h1, dif_neg h2] at heq
      exact congrArg Subtype.val (eRest.injective (Subtype.ext heq))
  have hπBij : Function.Bijective πFun := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hπInj, Fintype.card_congr e⟩
  refine ⟨Equiv.ofBijective πFun hπBij, fun x hx => ?_⟩
  simp [πFun, hx]

end BlockAndSign

lemma main_983 : (∀ rate : ℝ, 1 < rate → rate < Real.exp 1 →
    ∃ d : ℕ, 0 < d ∧ ∀ p : ℕ, 2 ≤ p → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      let I := Fin n
      ∃ B : Matrix I I ℝ, (∀ i j, B i j = 0 ∨ B i j = 1) ∧ 0 < B.permanent ∧
        (∀ i, ((Finset.univ : Finset I).filter (fun j => B i j = 1)).card ≤ d) ∧
        (∀ j, ((Finset.univ : Finset I).filter (fun i => B i j = 1)).card ≤ d) ∧
        ∀ (t : ℕ) (s : Fin t → I × I → Bool) (w : Fin t → ℝ),
          (∀ h, 0 ≤ w h) →
          (∀ A : Matrix I I ℝ,
            (A = 1 ∨ ∃ u v : Equiv.Perm I, ∀ i j, A i j = B (u i) (v j)) →
            let est := ∑ h : Fin t, w h * (Matrix.det (fun i j =>
              if s h (i, j) then -A i j else A i j : Matrix I I ℝ)) ^ 2
            ((p : ℝ) - 1) * A.permanent ≤ (p : ℝ) * est ∧
              (p : ℝ) * est ≤ ((p : ℝ) + 1) * A.permanent) →
          rate ^ n ≤ (((Finset.univ : Finset (Fin t)).filter (fun h => w h ≠ 0)).card : ℝ)) := by
  classical
  intro rate hrate1 hrateE
  let r0 : ℝ := (rate + Real.exp 1) / 2
  have hr0_gt : rate < r0 := by dsimp only [r0]; linarith
  have hr0_lt : r0 < Real.exp 1 := by dsimp only [r0]; linarith
  have hr0_pos : 0 < r0 := by linarith
  obtain ⟨q, hqprime, hqgap⟩ := exists_prime_rate_gap r0 hr0_pos hr0_lt
  haveI : Fact (Nat.Prime q) := ⟨hqprime⟩
  let d : ℕ := q + 1
  let m : ℕ := q ^ 2 + q + 1
  have hm_pos : 0 < m := by omega
  obtain ⟨M, hMbin, hMrow, hMcol, hMperm_pos, hMdet_ge, hMbreg⟩ := projMat_exists q
  have hMratio : r0 ^ m * M.permanent ≤ M.det ^ 2 := by
    have h1 : (r0 ^ m * M.permanent) ^ d ≤ (M.det ^ 2) ^ d := by
      calc (r0 ^ m * M.permanent) ^ d
          = (r0 ^ d) ^ m * M.permanent ^ d := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m d]
        _ ≤ (r0 ^ d) ^ m * ((d.factorial : ℝ) ^ m) :=
            mul_le_mul_of_nonneg_left hMbreg (by positivity)
        _ = (r0 ^ d * (d.factorial : ℝ)) ^ m := (mul_pow _ _ _).symm
        _ ≤ ((q : ℝ) ^ d) ^ m := pow_le_pow_left₀ (by positivity) hqgap m
        _ = ((q : ℝ) ^ m) ^ d := by rw [← pow_mul, ← pow_mul, mul_comm d m]
        _ ≤ (M.det ^ 2) ^ d := pow_le_pow_left₀ (by positivity) hMdet_ge d
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (Nat.succ_ne_zero q)).1 h1
  have hMdet_pos : 0 < M.det ^ 2 := lt_of_lt_of_le (by positivity) hMratio
  refine ⟨d, Nat.succ_pos q, fun p hp => ?_⟩
  let C : ℕ := m * 2 ^ m + m
  let δ : ℝ := r0 / rate - 1
  have hδ : 0 < δ := by
    dsimp only [δ]
    rw [sub_pos, one_lt_div (by linarith)]
    exact hr0_gt
  let target : ℝ := ((p : ℝ) + 1) / ((p : ℝ) - 1) * r0 ^ C
  let n0 : ℕ := max (m * 2 ^ m) (Nat.ceil (target / δ) + 1)
  refine ⟨n0, fun n hn => ?_⟩
  intro I
  have hn_base : m * 2 ^ m ≤ n := le_trans (le_max_left _ _) hn
  let k : ℕ := (n - m * 2 ^ m) / m
  have hkm_le : m * 2 ^ m + m * k ≤ n := by
    have hdiv := Nat.mul_div_le (n - m * 2 ^ m) m
    dsimp only [k]
    omega
  have hmk_le_n : k * m ≤ n := by rw [mul_comm]; omega
  have hmk_ge : n ≤ k * m + C := by
    have hmod := Nat.div_add_mod (n - m * 2 ^ m) m
    have hlt := Nat.mod_lt (n - m * 2 ^ m) hm_pos
    dsimp only [k, C]
    rw [mul_comm ((n - m * 2 ^ m) / m) m]
    omega
  let Idx := (Fin m × Fin k) ⊕ Fin (n - k * m)
  have hIdx_card : Fintype.card Idx = n := by
    simp only [Idx, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [mul_comm m k]
    omega
  let e : I ≃ Idx := (Fintype.equivFinOfCardEq hIdx_card).symm
  let B0 : Matrix Idx Idx ℝ := Matrix.fromBlocks (Matrix.blockDiagonal (fun _ : Fin k => M)) 0 0 1
  let B : Matrix I I ℝ := B0.submatrix e e
  have hBbin : ∀ i j, B i j = 0 ∨ B i j = 1 := by
    intro i j
    simp only [B, Matrix.submatrix_apply, B0]
    cases e i with
    | inl p1 =>
      cases e j with
      | inl p2 =>
        simp only [Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply]
        split_ifs
        · exact hMbin p1.1 p2.1
        · left; rfl
      | inr r2 => left; simp
    | inr r1 =>
      cases e j with
      | inl p2 => left; simp
      | inr r2 =>
        simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
        split_ifs <;> simp
  have hBperm : B.permanent = M.permanent ^ k := by
    rw [permanent_submatrix_equiv_self e B0]
    dsimp only [B0]
    rw [permanent_fromBlocks_zero, permanent_blockDiagonal_const M k, Matrix.permanent_one, mul_one]
  have hBdet : B.det = M.det ^ k := by
    rw [Matrix.det_submatrix_equiv_self e B0]
    dsimp only [B0]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_blockDiagonal, Matrix.det_one, mul_one,
      prod_const, card_univ, Fintype.card_fin]
  have hBperm_pos : 0 < B.permanent := by rw [hBperm]; exact pow_pos hMperm_pos k
  have hBrow : ∀ i : I, ((Finset.univ : Finset I).filter (fun j => B i j = 1)).card ≤ d := by
    intro i
    cases hi : e i with
    | inl p1 =>
      have hcard_eq : ((Finset.univ : Finset I).filter (fun j => B i j = 1)).card =
          ((Finset.univ : Finset (Fin m)).filter (fun b => M p1.1 b = 1)).card := by
        refine card_bij (fun j hj => ?_) ?_ ?_ ?_
        · exact match e j with | Sum.inl p2 => p2.1 | Sum.inr _ => ⟨0, hm_pos⟩
        · intro j hj
          have h1 := (mem_filter.1 hj).2
          simp only [B, Matrix.submatrix_apply, B0, hi] at h1
          cases hj2 : e j with
          | inl p2 =>
            simp only [hj2, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply] at h1
            split_ifs at h1 with heq
            · exact mem_filter.2 ⟨mem_univ _, h1⟩
            · norm_num at h1
          | inr r2 => simp [hj2] at h1
        · intro j1 hj1 j2 hj2 heq
          have h1 := (mem_filter.1 hj1).2
          have h2 := (mem_filter.1 hj2).2
          simp only [B, Matrix.submatrix_apply, B0, hi] at h1 h2
          cases he1 : e j1 with
          | inr _ => simp [he1] at h1
          | inl p1' =>
            cases he2 : e j2 with
            | inr _ => simp [he2] at h2
            | inl p2' =>
              simp only [he1, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply] at h1
              simp only [he2, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply] at h2
              have ht1 : p1.2 = p1'.2 := by by_contra hne; simp [hne] at h1
              have ht2 : p1.2 = p2'.2 := by by_contra hne; simp [hne] at h2
              simp only [he1, he2] at heq
              apply e.injective
              rw [he1, he2]
              exact congrArg Sum.inl (Prod.ext heq (ht1.symm.trans ht2))
        · intro b hb
          refine ⟨e.symm (Sum.inl (b, p1.2)), mem_filter.2 ⟨mem_univ _, ?_⟩, by simp⟩
          simp [B, B0, hi, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply, (mem_filter.1 hb).2]
      rw [hcard_eq, hMrow p1.1]
    | inr r1 =>
      have hsing : (Finset.univ : Finset I).filter (fun j => B i j = 1) = {e.symm (Sum.inr r1)} := by
        ext j
        simp only [mem_filter, mem_univ, true_and, mem_singleton, B, Matrix.submatrix_apply, B0, hi]
        cases hj : e j with
        | inl p2 =>
          simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_ne_one, false_iff]
          intro h; have := congrArg e h; simp [hj] at this
        | inr r2 =>
          simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
          constructor
          · intro h
            by_cases hrr : r1 = r2
            · subst hrr; exact e.injective (by simp [hj])
            · simp [hrr] at h
          · rintro rfl
            have : r2 = r1 := Sum.inr.inj (hj.symm.trans (e.apply_symm_apply _))
            simp [this]
      rw [hsing, card_singleton]
      omega
  have hBcol : ∀ j : I, ((Finset.univ : Finset I).filter (fun i => B i j = 1)).card ≤ d := by
    intro j
    cases hj : e j with
    | inl p2 =>
      have hcard_eq : ((Finset.univ : Finset I).filter (fun i => B i j = 1)).card =
          ((Finset.univ : Finset (Fin m)).filter (fun a => M a p2.1 = 1)).card := by
        refine card_bij (fun i hi => ?_) ?_ ?_ ?_
        · exact match e i with | Sum.inl p1 => p1.1 | Sum.inr _ => ⟨0, hm_pos⟩
        · intro i hi
          have h1 := (mem_filter.1 hi).2
          simp only [B, Matrix.submatrix_apply, B0, hj] at h1
          cases hi1 : e i with
          | inl p1 =>
            simp only [hi1, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply] at h1
            split_ifs at h1 with heq
            · exact mem_filter.2 ⟨mem_univ _, h1⟩
            · norm_num at h1
          | inr r1 => simp [hi1] at h1
        · intro i1 hi1 i2 hi2 heq
          have h1 := (mem_filter.1 hi1).2
          have h2 := (mem_filter.1 hi2).2
          simp only [B, Matrix.submatrix_apply, B0, hj] at h1 h2
          cases he1 : e i1 with
          | inr _ => simp [he1] at h1
          | inl p1' =>
            cases he2 : e i2 with
            | inr _ => simp [he2] at h2
            | inl p2' =>
              simp only [he1, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply] at h1
              simp only [he2, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply] at h2
              have ht1 : p1'.2 = p2.2 := by by_contra hne; simp [hne] at h1
              have ht2 : p2'.2 = p2.2 := by by_contra hne; simp [hne] at h2
              simp only [he1, he2] at heq
              apply e.injective
              rw [he1, he2]
              exact congrArg Sum.inl (Prod.ext heq (ht1.trans ht2.symm))
        · intro a ha
          refine ⟨e.symm (Sum.inl (a, p2.2)), mem_filter.2 ⟨mem_univ _, ?_⟩, by simp⟩
          simp [B, B0, hj, Matrix.fromBlocks_apply₁₁, Matrix.blockDiagonal_apply, (mem_filter.1 ha).2]
      rw [hcard_eq, hMcol p2.1]
    | inr r2 =>
      have hsing : (Finset.univ : Finset I).filter (fun i => B i j = 1) = {e.symm (Sum.inr r2)} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton, B, Matrix.submatrix_apply, B0, hj]
        cases hi : e i with
        | inl p1 =>
          simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, zero_ne_one, false_iff]
          intro h; have := congrArg e h; simp [hi] at this
        | inr r1 =>
          simp only [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
          constructor
          · intro h
            by_cases hrr : r1 = r2
            · subst hrr; exact e.injective (by simp [hi])
            · simp [hrr] at h
          · rintro rfl
            have : r1 = r2 := Sum.inr.inj (hi.symm.trans (e.apply_symm_apply _))
            simp [this]
      rw [hsing, card_singleton]
      omega
  refine ⟨B, hBbin, hBperm_pos, hBrow, hBcol, fun t s w hw hacc => ?_⟩
  have hp_pos : (0 : ℝ) < (p : ℝ) := by positivity
  have hp_sub : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have hsum_w_lb : ((p : ℝ) - 1) / (p : ℝ) ≤ ∑ h : Fin t, w h := by
    have h1 := (hacc 1 (Or.inl rfl)).1
    rw [Matrix.permanent_one, mul_one] at h1
    have hdet1 : ∀ h : Fin t,
        (Matrix.det (fun i j => if s h (i, j) then -(1 : Matrix I I ℝ) i j else (1 : Matrix I I ℝ) i j)) ^ 2 = 1 := by
      intro h
      let diagSign : I → ℝ := fun i => if s h (i, i) then -1 else 1
      have hmat : (fun i j => if s h (i, j) then -(1 : Matrix I I ℝ) i j else (1 : Matrix I I ℝ) i j) =
          Matrix.diagonal diagSign := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [diagSign]
        · simp [hij]
      rw [hmat, Matrix.det_diagonal, ← prod_pow]
      exact prod_eq_one fun i _ => by dsimp only [diagSign]; split_ifs <;> norm_num
    have hest : ∑ h : Fin t, w h * (Matrix.det (fun i j =>
        if s h (i, j) then -(1 : Matrix I I ℝ) i j else (1 : Matrix I I ℝ) i j)) ^ 2 =
        ∑ h : Fin t, w h := by
      refine sum_congr rfl fun h _ => by rw [hdet1 h, mul_one]
    rw [hest] at h1
    rw [div_le_iff₀ hp_pos]
    linarith
  have hw_ub : ∀ h : Fin t, w h ≤ ((p : ℝ) + 1) / (p : ℝ) * (M.permanent / M.det ^ 2) ^ k := by
    intro h
    obtain ⟨uEmb, vEmb, _, _, hsign⟩ :=
      extract_sign_blocks hm_pos (s h) k Finset.univ Finset.univ rfl (by simp [hkm_le])
    let Sblk : Finset Idx := (Finset.univ : Finset (Fin m × Fin k)).image Sum.inl
    let uSub : {x : Idx // x ∈ Sblk} ↪ I :=
      ⟨fun x =>
        match hx : x.1 with
        | Sum.inl p => uEmb (p.2, p.1)
        | Sum.inr _ => False.elim (by
            have hmem := x.2
            rw [hx] at hmem
            simp [Sblk] at hmem),
       by
        rintro ⟨x1, hx1⟩ ⟨x2, hx2⟩ heq
        cases x1 with
        | inr _ => simp [Sblk] at hx1
        | inl p1 =>
          cases x2 with
          | inr _ => simp [Sblk] at hx2
          | inl p2 =>
            dsimp only at heq
            have hp := uEmb.injective heq
            exact Subtype.ext (congrArg Sum.inl (Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)))⟩
    let vSub : {x : Idx // x ∈ Sblk} ↪ I :=
      ⟨fun x =>
        match hx : x.1 with
        | Sum.inl p => vEmb (p.2, p.1)
        | Sum.inr _ => False.elim (by
            have hmem := x.2
            rw [hx] at hmem
            simp [Sblk] at hmem),
       by
        rintro ⟨x1, hx1⟩ ⟨x2, hx2⟩ heq
        cases x1 with
        | inr _ => simp [Sblk] at hx1
        | inl p1 =>
          cases x2 with
          | inr _ => simp [Sblk] at hx2
          | inl p2 =>
            dsimp only at heq
            have hp := vEmb.injective heq
            exact Subtype.ext (congrArg Sum.inl (Prod.ext (congrArg Prod.snd hp) (congrArg Prod.fst hp)))⟩
    obtain ⟨πU, hπU⟩ := extend_embedding_to_perm e.symm Sblk uSub
    obtain ⟨πV, hπV⟩ := extend_embedding_to_perm e.symm Sblk vSub
    let u' : Equiv.Perm I := e.trans πU
    let v' : Equiv.Perm I := e.trans πV
    let u : Equiv.Perm I := u'.symm
    let v : Equiv.Perm I := v'.symm
    let A : Matrix I I ℝ := fun i j => B (u i) (v j)
    have hA_perm : A.permanent = B.permanent := by
      have hA_sub : A = (B.submatrix u id).submatrix id v := by ext i j; rfl
      rw [hA_sub, Matrix.permanent_permute_rows, Matrix.permanent_permute_cols]
    let SA : Matrix I I ℝ := fun i j => if s h (i, j) then -A i j else A i j
    let α : I → ℝ := fun y =>
      match e y with
      | Sum.inl p => if s h (u' (e.symm (Sum.inl (⟨0, hm_pos⟩, p.2))), v' y) then -1 else 1
      | Sum.inr _ => if s h (u' y, v' y) then -1 else 1
    have hSA_sub : SA.submatrix u' v' = B * Matrix.diagonal α := by
      ext x y
      change (if s h (u' x, v' y) then -B (u (u' x)) (v (v' y)) else B (u (u' x)) (v (v' y))) =
        (B * Matrix.diagonal α) x y
      simp only [u, v, Equiv.symm_apply_apply, Matrix.mul_diagonal]
      have hBxy : B x y = B0 (e x) (e y) := rfl
      cases hex : e x with
      | inl px =>
        cases hey : e y with
        | inl py =>
          by_cases hblk : px.2 = py.2
          · have hux : u' x = uEmb (px.2, px.1) := by
              change πU (e x) = uEmb (px.2, px.1)
              rw [hex, hπU _ (mem_image_of_mem _ (mem_univ _))]
              rfl
            have hu0 : u' (e.symm (Sum.inl (⟨0, hm_pos⟩, py.2))) = uEmb (py.2, ⟨0, hm_pos⟩) := by
              change πU (e (e.symm (Sum.inl (⟨0, hm_pos⟩, py.2)))) = _
              rw [Equiv.apply_symm_apply, hπU _ (mem_image_of_mem _ (mem_univ _))]
              rfl
            have hvy : v' y = vEmb (py.2, py.1) := by
              change πV (e y) = vEmb (py.2, py.1)
              rw [hey, hπV _ (mem_image_of_mem _ (mem_univ _))]
              rfl
            have hs_eq : s h (u' x, v' y) =
                s h (u' (e.symm (Sum.inl (⟨0, hm_pos⟩, py.2))), v' y) := by
              rw [hux, hu0, hvy, hblk]
              exact hsign py.2 px.1 ⟨0, hm_pos⟩ py.1
            simp only [α, hey, hs_eq]
            split_ifs <;> ring
          · have h0 : B x y = 0 := by simp [B, B0, hex, hey, Matrix.blockDiagonal_apply, hblk]
            rw [h0]; simp
        | inr ry =>
          have h0 : B x y = 0 := by simp [B, B0, hex, hey]
          rw [h0]; simp
      | inr rx =>
        cases hey : e y with
        | inl py =>
          have h0 : B x y = 0 := by simp [B, B0, hex, hey]
          rw [h0]; simp
        | inr ry =>
          by_cases hrr : rx = ry
          · have hxy : x = y := e.injective (by rw [hex, hey, hrr])
            subst hxy
            simp only [α, hey]
            split_ifs <;> ring
          · have h0 : B x y = 0 := by simp [B, B0, hex, hey, hrr]
            rw [h0]; simp
    have hdet_sq : SA.det ^ 2 = (M.det ^ 2) ^ k := by
      have h1 : (SA.submatrix u' v').det =
          (Equiv.Perm.sign u' : ℝ) * (Equiv.Perm.sign v' : ℝ) * SA.det := by
        have hsub2 : SA.submatrix u' v' = (SA.submatrix u' id).submatrix id v' := by ext i j; rfl
        rw [hsub2, Matrix.det_permute', Matrix.det_permute, mul_assoc]
        ring
      have h2 : (SA.submatrix u' v').det ^ 2 = SA.det ^ 2 := by
        rw [h1, mul_pow, mul_pow]
        have hu1 : ((Equiv.Perm.sign u' : ℤ) : ℝ) ^ 2 = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign u') with h | h <;> simp [h]
        have hv1 : ((Equiv.Perm.sign v' : ℤ) : ℝ) ^ 2 = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign v') with h | h <;> simp [h]
        rw [hu1, hv1, one_mul, one_mul]
      have h3 : (B * Matrix.diagonal α).det ^ 2 = B.det ^ 2 := by
        rw [Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← prod_pow]
        have hα1 : ∏ y : I, α y ^ 2 = 1 := prod_eq_one fun y _ => by
          cases hy : e y <;> simp only [α, hy] <;> split_ifs <;> norm_num
        rw [hα1, mul_one]
      rw [← h2, hSA_sub, h3, hBdet, ← pow_mul, mul_comm k 2, pow_mul]
    have haccA := (hacc A (Or.inr ⟨u, v, fun _ _ => rfl⟩)).2
    have hterm_le : w h * SA.det ^ 2 ≤
        ∑ h' : Fin t, w h' * (Matrix.det (fun i j =>
          if s h' (i, j) then -A i j else A i j : Matrix I I ℝ)) ^ 2 :=
      single_le_sum (fun h' _ => mul_nonneg (hw h') (sq_nonneg _)) (mem_univ h)
    have hmul_p := mul_le_mul_of_nonneg_left hterm_le hp_pos.le
    have hcomb : (p : ℝ) * (w h * (M.det ^ 2) ^ k) ≤ ((p : ℝ) + 1) * M.permanent ^ k := by
      rw [← hdet_sq]
      rw [hA_perm, hBperm] at haccA
      exact le_trans hmul_p haccA
    rw [div_pow, mul_div_assoc', le_div_iff₀ (pow_pos hMdet_pos k)]
    rw [div_mul_eq_mul_div, le_div_iff₀ hp_pos]
    linarith
  let Snz := (Finset.univ : Finset (Fin t)).filter (fun h => w h ≠ 0)
  have hsum_nz : ∑ h : Fin t, w h = ∑ h ∈ Snz, w h := by
    symm
    refine sum_subset (subset_univ Snz) fun h _ hnot => ?_
    simp only [Snz, mem_filter, mem_univ, true_and, not_not] at hnot
    exact hnot
  have hsum_ub : ∑ h ∈ Snz, w h ≤ (Snz.card : ℝ) * (((p : ℝ) + 1) / (p : ℝ) * (M.permanent / M.det ^ 2) ^ k) := by
    calc ∑ h ∈ Snz, w h
        ≤ ∑ _h ∈ Snz, (((p : ℝ) + 1) / (p : ℝ) * (M.permanent / M.det ^ 2) ^ k) :=
          sum_le_sum fun h _ => hw_ub h
      _ = (Snz.card : ℝ) * (((p : ℝ) + 1) / (p : ℝ) * (M.permanent / M.det ^ 2) ^ k) := by
          rw [sum_const, nsmul_eq_mul]
  have hcomb1 : ((p : ℝ) - 1) / (p : ℝ) ≤
      (Snz.card : ℝ) * (((p : ℝ) + 1) / (p : ℝ) * (M.permanent / M.det ^ 2) ^ k) :=
    le_trans hsum_w_lb (hsum_nz ▸ hsum_ub)
  have hratio_pow : (M.permanent / M.det ^ 2) ^ k ≤ (1 / r0 ^ m) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    rw [div_le_div_iff₀ hMdet_pos (pow_pos hr0_pos m), one_mul, mul_comm]
    exact hMratio
  have hcomb2 : ((p : ℝ) - 1) / (p : ℝ) ≤
      (Snz.card : ℝ) * (((p : ℝ) + 1) / (p : ℝ) * (1 / r0 ^ (k * m))) := by
    have hpow_eq : (1 / r0 ^ m) ^ k = 1 / r0 ^ (k * m) := by
      rw [div_pow, one_pow, ← pow_mul, mul_comm]
    rw [← hpow_eq]
    exact le_trans hcomb1 (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hratio_pow (by positivity)) (Nat.cast_nonneg _))
  have hSnz_ge : ((p : ℝ) - 1) / ((p : ℝ) + 1) * r0 ^ (k * m) ≤ (Snz.card : ℝ) := by
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have hmul := mul_le_mul_of_nonneg_right hcomb2 (by positivity : (0 : ℝ) ≤ (p : ℝ) / ((p : ℝ) + 1) * r0 ^ (k * m))
    have hL : ((p : ℝ) - 1) / (p : ℝ) * ((p : ℝ) / ((p : ℝ) + 1) * r0 ^ (k * m)) =
        ((p : ℝ) - 1) / ((p : ℝ) + 1) * r0 ^ (k * m) := by
      field_simp [hp_pos.ne', hp1.ne']
    have hR : (Snz.card : ℝ) * (((p : ℝ) + 1) / (p : ℝ) * (1 / r0 ^ (k * m))) *
        ((p : ℝ) / ((p : ℝ) + 1) * r0 ^ (k * m)) = (Snz.card : ℝ) := by
      have hrn : r0 ^ (k * m) ≠ 0 := (pow_pos hr0_pos _).ne'
      field_simp [hp_pos.ne', hp1.ne', hrn]
    linarith
  have hrate_pow_le : rate ^ n ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) * r0 ^ (k * m) := by
    have hr0_ge_one : 1 ≤ r0 := by linarith
    have hr0_pow : r0 ^ n ≤ r0 ^ (k * m) * r0 ^ C := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hr0_ge_one hmk_ge
    have hbern : target ≤ (r0 / rate) ^ n := by
      have h1 := one_add_quad_le_pow δ hδ.le n
      have h1add : 1 + δ = r0 / rate := by dsimp only [δ]; ring
      rw [h1add] at h1
      have hnn : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * δ ^ 2 := by
        cases n with
        | zero => simp
        | succ j =>
          push_cast
          have hsub : (j : ℝ) + 1 - 1 = (j : ℝ) := by ring
          rw [hsub]
          positivity
      have hn_ceil : target / δ ≤ (n : ℝ) := by
        have h2 : Nat.ceil (target / δ) ≤ n := by
          have := le_trans (le_max_right _ _) hn
          omega
        exact le_trans (Nat.le_ceil _) (Nat.cast_le.2 h2)
      have hnδ : target ≤ (n : ℝ) * δ := by
        rw [div_le_iff₀ hδ] at hn_ceil
        exact hn_ceil
      linarith
    have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    rw [div_pow, le_div_iff₀ (pow_pos (by linarith : (0 : ℝ) < rate) n)] at hbern
    have hmul := mul_le_mul_of_nonneg_left (le_trans hbern hr0_pow)
      (by positivity : (0 : ℝ) ≤ ((p : ℝ) - 1) / (((p : ℝ) + 1) * r0 ^ C))
    have hL : ((p : ℝ) - 1) / (((p : ℝ) + 1) * r0 ^ C) * (target * rate ^ n) = rate ^ n := by
      dsimp only [target]
      have hrC : r0 ^ C ≠ 0 := (pow_pos hr0_pos C).ne'
      field_simp [hp_sub.ne', hp1.ne', hrC]
    have hR : ((p : ℝ) - 1) / (((p : ℝ) + 1) * r0 ^ C) * (r0 ^ (k * m) * r0 ^ C) =
        ((p : ℝ) - 1) / ((p : ℝ) + 1) * r0 ^ (k * m) := by
      have hrC : r0 ^ C ≠ 0 := (pow_pos hr0_pos C).ne'
      field_simp [hp1.ne', hrC]
    linarith
  exact le_trans hrate_pow_le hSnz_ge

end PEqualNP.Outside.L_lib_983_aux

theorem PEqualNP.Outside.L_lib_983 : (∀ rate : ℝ, 1 < rate → rate < Real.exp 1 →
  ∃ d : ℕ, 0 < d ∧ ∀ p : ℕ, 2 ≤ p → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    let I := Fin n
    ∃ B : Matrix I I ℝ, (∀ i j, B i j = 0 ∨ B i j = 1) ∧ 0 < B.permanent ∧
      (∀ i, ((Finset.univ : Finset I).filter (fun j => B i j = 1)).card ≤ d) ∧
      (∀ j, ((Finset.univ : Finset I).filter (fun i => B i j = 1)).card ≤ d) ∧
      ∀ (t : ℕ) (s : Fin t → I × I → Bool) (w : Fin t → ℝ),
        (∀ h, 0 ≤ w h) →
        (∀ A : Matrix I I ℝ,
          (A = 1 ∨ ∃ u v : Equiv.Perm I, ∀ i j, A i j = B (u i) (v j)) →
          let est := ∑ h : Fin t, w h * (Matrix.det (fun i j =>
            if s h (i,j) then -A i j else A i j : Matrix I I ℝ))^2
          ((p : ℝ)-1)*A.permanent ≤ (p : ℝ)*est ∧
            (p : ℝ)*est ≤ ((p : ℝ)+1)*A.permanent) →
        rate^n ≤ (((Finset.univ : Finset (Fin t)).filter (fun h => w h ≠ 0)).card : ℝ)) :=
  PEqualNP.Outside.L_lib_983_aux.main_983
