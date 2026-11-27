import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_463

theorem digits_inj (b : ℕ) (hb : 1 < b) : ∀ (n : ℕ) (c d : Fin n → ℕ), (∀ j, c j < b) → (∀ j, d j < b) →
    ∑ j, c j * b ^ j.val = ∑ j, d j * b ^ j.val → c = d := by
  intro n
  induction n with
  | zero => intro c d _ _ _; funext j; exact j.elim0
  | succ n ih =>
    intro c d hc hd h
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at h
    have e : ∀ f : Fin (n+1) → ℕ, ∑ j : Fin n, f j.succ * b ^ (j.succ).val = b * ∑ j : Fin n, f j.succ * b ^ j.val := by
      intro f
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [pow_succ]; ring
    rw [e c, e d] at h
    simp only [Fin.val_zero, pow_zero, mul_one] at h
    have h0 : c 0 = d 0 := by
      have := congrArg (· % b) h
      simp only [Nat.add_mul_mod_self_left] at this
      rwa [Nat.mod_eq_of_lt (hc 0), Nat.mod_eq_of_lt (hd 0)] at this
    rw [h0] at h
    have h1 := Nat.add_left_cancel h
    have h2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
    have := ih (fun j => c j.succ) (fun j => d j.succ) (fun j => hc _) (fun j => hd _) h2
    funext j
    refine Fin.cases h0 (fun k => ?_) j
    exact congrFun this k

end PEqualNP.Outside.L_lib_463

theorem PEqualNP.Outside.L_lib_463 : ∀ (n m : ℕ) (A : Fin m → Finset (Fin n)),
  let b := m + 2
  (∃ S : Finset (Fin m), ∀ j : Fin n, ∃! i : Fin m, i ∈ S ∧ j ∈ A i) ↔
  ∃ S : Finset (Fin m), (∑ i ∈ S, ∑ j ∈ A i, b ^ j.val) = ∑ j : Fin n, b ^ j.val := by
  intro n m A b
  have hsum : ∀ S : Finset (Fin m), ∑ i ∈ S, ∑ j ∈ A i, b ^ j.val =
      ∑ j : Fin n, (S.filter (fun i => j ∈ A i)).card * b ^ j.val := by
    intro S
    have h1 : ∀ i ∈ S, ∑ j ∈ A i, b ^ j.val = ∑ j : Fin n, (if j ∈ A i then b ^ j.val else 0) := by
      intro i _
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have hall : ∑ j : Fin n, b ^ j.val = ∑ j : Fin n, 1 * b ^ j.val := by simp
  constructor
  · rintro ⟨S, hS⟩
    refine ⟨S, ?_⟩
    rw [hsum, hall]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    obtain ⟨a, ⟨haS, haj⟩, hu⟩ := hS j
    apply Finset.card_eq_one.2
    refine ⟨a, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hx; exact hu x hx
    · rintro rfl; exact ⟨haS, haj⟩
  · rintro ⟨S, hS⟩
    rw [hsum, hall] at hS
    have hlt : ∀ j : Fin n, (S.filter (fun i => j ∈ A i)).card < b := fun j => by
      have := Finset.card_filter_le S (fun i => j ∈ A i)
      have := Finset.card_le_univ S
      simp at this ⊢
      omega
    have := PEqualNP.Outside.L_lib_463.digits_inj b (by omega) n _ _ hlt (fun _ => by omega) hS
    refine ⟨S, fun j => ?_⟩
    have hj : (S.filter (fun i => j ∈ A i)).card = 1 := congrFun this j
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hj
    have hamem : a ∈ S.filter (fun i => j ∈ A i) := by rw [ha]; simp
    refine ⟨a, Finset.mem_filter.1 hamem, ?_⟩
    rintro x hx
    have : x ∈ S.filter (fun i => j ∈ A i) := Finset.mem_filter.2 hx
    rw [ha] at this
    simpa using this
