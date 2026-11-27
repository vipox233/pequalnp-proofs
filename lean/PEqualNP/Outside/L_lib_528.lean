import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_528_aux

def enc : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, a => enc k (a / 2) ++ [a % 2 == 1]

def dec (l : List Bool) : ℕ := l.foldl (fun acc b => 2 * acc + b.toNat) 0

theorem dec_append_single (l : List Bool) (b : Bool) : dec (l ++ [b]) = 2 * dec l + b.toNat := by
  simp [dec, List.foldl_append]

theorem enc_length (k a : ℕ) : (enc k a).length = k := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih => simp [enc, ih]

theorem dec_enc (k a : ℕ) : dec (enc k a) = a % 2 ^ k := by
  induction k generalizing a with
  | zero => simp [enc, dec, Nat.mod_one]
  | succ k ih =>
    rw [enc, dec_append_single, ih, pow_succ, mul_comm (2 ^ k) 2, Nat.mod_mul]
    have h : (a % 2 == 1).toNat = a % 2 := by
      rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
    rw [h]; ring

theorem enc_add (l d a : ℕ) : enc (l + d) a = enc l (a / 2 ^ d) ++ enc d a := by
  induction d generalizing a with
  | zero => simp [enc]
  | succ d ih =>
    rw [← Nat.add_assoc, enc, ih, enc, List.append_assoc, Nat.div_div_eq_div_mul, pow_succ,
      mul_comm (2 ^ d) 2]

theorem exists_pow (x : ℝ) (hx : 1 ≤ x) : ∃ n : ℕ, x ≤ 2 ^ n ∧ (2 : ℝ) ^ n < 2 * x := by
  classical
  have h : ∃ n : ℕ, x ≤ 2 ^ n :=
    (pow_unbounded_of_one_lt x one_lt_two).imp fun _ h => h.le
  refine ⟨Nat.find h, Nat.find_spec h, ?_⟩
  rcases hn : Nat.find h with _ | k
  · simp; linarith
  · have := Nat.find_min h (show k < Nat.find h by omega)
    push Not at this
    rw [pow_succ]; linarith

section converse

variable {m : ℕ} (l : Fin m → ℕ)

def before (i : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => l k < l i ∨ (l k = l i ∧ k < i))

def val (i : Fin m) : ℕ := ∑ k ∈ before l i, 2 ^ (l i - l k)

theorem mem_before {i k : Fin m} : k ∈ before l i ↔ (l k < l i ∨ (l k = l i ∧ k < i)) := by
  simp [before]

theorem le_of_mem_before {i k : Fin m} (h : k ∈ before l i) : l k ≤ l i := by
  rcases (mem_before l).1 h with h | h <;> omega

theorem not_mem_before_self (i : Fin m) : i ∉ before l i := by
  simp [before]

theorem mul_val_succ (i : Fin m) (M : ℕ) (hM : l i ≤ M) :
    2 ^ (M - l i) * (val l i + 1) = ∑ k ∈ insert i (before l i), 2 ^ (M - l k) := by
  rw [Finset.sum_insert (not_mem_before_self l i), val, mul_add, mul_one,
    Finset.mul_sum, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have := le_of_mem_before l hk
  rw [← pow_add]; congr 1; omega

theorem step {i j : Fin m} (h : j ∈ before l i) :
    2 ^ (l i - l j) * (val l j + 1) ≤ val l i := by
  rw [mul_val_succ l j (l i) (le_of_mem_before l h), val]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  rw [Finset.mem_insert] at hk
  rcases hk with rfl | hk
  · exact h
  · rw [mem_before] at h hk ⊢
    rw [Fin.lt_def] at h hk ⊢
    omega

theorem val_lt (N : ℕ) (hN : ∀ i, l i ≤ N) (hK : ∑ i, 2 ^ (N - l i) ≤ 2 ^ N) (i : Fin m) :
    val l i < 2 ^ l i := by
  have h1 := mul_val_succ l i N (hN i)
  have h2 : ∑ k ∈ insert i (before l i), 2 ^ (N - l k) ≤ ∑ k, 2 ^ (N - l k) :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have h3 : 2 ^ N = 2 ^ (N - l i) * 2 ^ l i := by
    rw [← pow_add]; congr 1; have := hN i; omega
  have : 2 ^ (N - l i) * (val l i + 1) ≤ 2 ^ (N - l i) * 2 ^ l i := by omega
  have := Nat.le_of_mul_le_mul_left this (by positivity)
  omega

theorem kraft_converse (N : ℕ) (hN : ∀ i, l i ≤ N) (hK : ∑ i, 2 ^ (N - l i) ≤ 2 ^ N) :
    ∃ c : Fin m → List Bool, (∀ i, (c i).length = l i) ∧
      ∀ i j, (∃ t : List Bool, c j = c i ++ t) → i = j := by
  refine ⟨fun i => enc (l i) (val l i), fun i => enc_length _ _, ?_⟩
  rintro i j ⟨t, ht⟩
  have hlen := congrArg List.length ht
  simp only [List.length_append, enc_length] at hlen
  obtain ⟨d, hd⟩ : ∃ d, l j = l i + d := ⟨t.length, hlen⟩
  simp only at ht
  rw [hd, enc_add] at ht
  have h := (List.append_inj ht (by simp [enc_length])).1
  have h' := congrArg dec h
  rw [dec_enc, dec_enc] at h'
  have hvi := val_lt l N hN hK i
  have hvj := val_lt l N hN hK j
  have hq : val l j / 2 ^ d < 2 ^ l i := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, ← hd]; exact hvj
  rw [Nat.mod_eq_of_lt hvi, Nat.mod_eq_of_lt hq] at h'
  by_contra hij
  have htri : i ∈ before l j ∨ j ∈ before l i := by
    rw [mem_before, mem_before]
    rcases lt_trichotomy i j with h | h | h
    · omega
    · exact absurd h hij
    · omega
  rcases htri with h1 | h1
  · have := step l h1
    rw [hd, Nat.add_sub_cancel_left] at this
    have : val l i + 1 ≤ val l j / 2 ^ d := by
      rw [Nat.le_div_iff_mul_le (by positivity), mul_comm]; exact this
    omega
  · have := step l h1
    have hl := le_of_mem_before l h1
    have hd0 : d = 0 := by omega
    subst hd0
    simp only [Nat.add_zero, pow_zero, Nat.div_one] at hd h'
    rw [hd, Nat.sub_self, pow_zero, one_mul] at this
    omega

end converse

end PEqualNP.Outside.L_lib_528_aux

open PEqualNP.Outside.L_lib_528_aux

theorem PEqualNP.Outside.L_lib_528 : (∀ (m : ℕ) (p : Fin m → ℝ),
  (∀ i, 0 < p i) → (∑ i, p i) = 1 →
  let prefixCode := fun (code : Fin m → List Bool) =>
    ∀ i j, (∃ tail : List Bool, code j = code i ++ tail) → i = j
  let S := ∑ i, Real.sqrt (p i)
  let cost := fun (c : Fin m → List Bool) => ∑ i, p i * (2:ℝ)^(c i).length
  (∀ c, prefixCode c → S^2 ≤ cost c) ∧ ∃ c, prefixCode c ∧ cost c < 2*S^2) := by
  intro m p hp hsum prefixCode S cost
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp at hsum
    · exact h
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hsq : ∀ i, 0 < Real.sqrt (p i) := fun i => Real.sqrt_pos.2 (hp i)
  have hS : 0 < S := Finset.sum_pos (fun i _ => hsq i) hne
  constructor
  · intro c hc
    have hinj : Function.Injective c := fun i j h => hc i j ⟨[], by simp [h]⟩
    have hpf : InformationTheory.IsPrefixFree
        ((Finset.univ.image c : Finset (List Bool)) : Set (List Bool)) := by
      intro x hx y hy hxy
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      obtain ⟨t, ht⟩ := hxy
      rw [hc i j ⟨t, ht.symm⟩]
    have kraft := InformationTheory.IsPrefixFree.finsetSum_one_div_card_pow_length_le_one hpf
    rw [Finset.sum_image (fun i _ j _ h => hinj h)] at kraft
    have kraft' : ∑ i, ((2:ℝ) ^ (c i).length)⁻¹ ≤ 1 := by
      simpa [one_div, inv_pow] using kraft
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Real.sqrt (p i) * Real.sqrt ((2:ℝ) ^ (c i).length))
      (fun i => (Real.sqrt ((2:ℝ) ^ (c i).length))⁻¹)
    have e1 : ∑ i, Real.sqrt (p i) * Real.sqrt ((2:ℝ) ^ (c i).length) *
        (Real.sqrt ((2:ℝ) ^ (c i).length))⁻¹ = S := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : 0 < Real.sqrt ((2:ℝ) ^ (c i).length) := Real.sqrt_pos.2 (by positivity)
      field_simp
    have e2 : ∑ i, (Real.sqrt (p i) * Real.sqrt ((2:ℝ) ^ (c i).length)) ^ 2 = cost c := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_pow, Real.sq_sqrt (hp i).le, Real.sq_sqrt (by positivity)]
    have e3 : ∑ i, ((Real.sqrt ((2:ℝ) ^ (c i).length))⁻¹) ^ 2 =
        ∑ i, ((2:ℝ) ^ (c i).length)⁻¹ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    rw [e1, e2, e3] at cs
    have hcost : 0 ≤ cost c := Finset.sum_nonneg fun i _ => by have := hp i; positivity
    nlinarith
  · have hx : ∀ i, 1 ≤ S / Real.sqrt (p i) := fun i => by
      rw [le_div_iff₀ (hsq i), one_mul]
      exact Finset.single_le_sum (fun j _ => (hsq j).le) (Finset.mem_univ i)
    choose l hl1 hl2 using fun i => exists_pow _ (hx i)
    set N := ∑ i, l i with hNdef
    have hN : ∀ i, l i ≤ N := fun i =>
      Finset.single_le_sum (fun j _ => Nat.zero_le (l j)) (Finset.mem_univ i)
    have hinv : ∀ i, ((2:ℝ) ^ l i)⁻¹ ≤ Real.sqrt (p i) / S := fun i => by
      have h := inv_anti₀ (div_pos hS (hsq i)) (hl1 i)
      rwa [inv_div] at h
    have hK : ∑ i, 2 ^ (N - l i) ≤ 2 ^ N := by
      have : ((∑ i, 2 ^ (N - l i) : ℕ) : ℝ) ≤ ((2 ^ N : ℕ) : ℝ) := by
        push_cast
        have e : ∀ i, (2:ℝ) ^ (N - l i) = 2 ^ N * ((2:ℝ) ^ l i)⁻¹ := fun i => by
          rw [pow_sub₀ _ two_ne_zero (hN i)]
        simp_rw [e]
        rw [← Finset.mul_sum]
        have h1 : ∑ i, ((2:ℝ) ^ l i)⁻¹ ≤ 1 := by
          calc ∑ i, ((2:ℝ) ^ l i)⁻¹ ≤ ∑ i, Real.sqrt (p i) / S := Finset.sum_le_sum fun i _ => hinv i
            _ = 1 := by rw [← Finset.sum_div]; exact div_self hS.ne'
        have : (0:ℝ) < 2 ^ N := by positivity
        nlinarith
      exact_mod_cast this
    obtain ⟨c, hcl, hcp⟩ := kraft_converse l N hN hK
    refine ⟨c, hcp, ?_⟩
    show ∑ i, p i * (2:ℝ) ^ (c i).length < 2 * S ^ 2
    have hterm : ∀ i, p i * (2:ℝ) ^ (c i).length < 2 * S * Real.sqrt (p i) := fun i => by
      rw [hcl i]
      have h1 : p i * (2:ℝ) ^ l i < p i * (2 * (S / Real.sqrt (p i))) :=
        mul_lt_mul_of_pos_left (hl2 i) (hp i)
      have h2 : p i * (2 * (S / Real.sqrt (p i))) = 2 * S * Real.sqrt (p i) := by
        rw [show p i * (2 * (S / Real.sqrt (p i))) = 2 * S * (p i / Real.sqrt (p i)) by ring,
          Real.div_sqrt]
      linarith
    calc ∑ i, p i * (2:ℝ) ^ (c i).length < ∑ i, 2 * S * Real.sqrt (p i) :=
          Finset.sum_lt_sum_of_nonempty hne fun i _ => hterm i
      _ = 2 * S ^ 2 := by rw [← Finset.mul_sum]; ring
