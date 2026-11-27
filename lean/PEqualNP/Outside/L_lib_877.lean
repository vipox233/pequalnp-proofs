import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_877_aux

open Finset

variable {k q : ℕ}

def valid (M : Finset (Finset (Fin k))) : Prop :=
  (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)

def err (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (M : Finset (Finset (Fin k))) : ℕ :=
  (Finset.univ.filter (fun t : Fin q => (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card

def signed (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (S : Finset (Finset (Fin k))) : ℤ :=
  ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
  ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)

theorem valid_mono {M S : Finset (Finset (Fin k))} (hM : valid M) (hS : S ⊆ M) : valid S :=
  ⟨fun e he => hM.1 e (hS he), fun e he g hg hne => hM.2 e (hS he) g (hS hg) hne⟩

theorem key {α : Type*} [DecidableEq α] (M A : Finset α) :
    ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : ℤ) ^ S.card * (if S ⊆ A then 1 else 0) =
      (if M ∩ A = ∅ then 1 else 0) - 1 := by
  have h1 : ∑ S ∈ M.powerset, (-1 : ℤ) ^ S.card * (if S ⊆ A then 1 else 0) =
      if M ∩ A = ∅ then 1 else 0 := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    have : M.powerset.filter (fun S => S ⊆ A) = (M ∩ A).powerset := by
      ext S; simp [Finset.subset_inter_iff]
    rw [this, Finset.sum_powerset_neg_one_pow_card]
  have h2 := Finset.sum_filter_add_sum_filter_not M.powerset (fun T => T.Nonempty)
    (fun S => (-1 : ℤ) ^ S.card * (if S ⊆ A then 1 else 0))
  have h3 : M.powerset.filter (fun T => ¬ T.Nonempty) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h3, Finset.sum_singleton] at h2
  simp only [Finset.card_empty, pow_zero, Finset.empty_subset, ite_true, mul_one] at h2
  linarith

def sig (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (S : Finset (Finset (Fin k))) (t : Fin q) : ℤ :=
  (if fixed t = false ∧ S ⊆ D t ∧ target t = true then 1 else 0) -
  (if fixed t = false ∧ S ⊆ D t ∧ target t = false then 1 else 0)

def ind (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (M : Finset (Finset (Fin k))) (t : Fin q) : ℤ :=
  if (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t then 1 else 0

theorem err_eq (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (M : Finset (Finset (Fin k))) : (err D fixed target M : ℤ) = ∑ t, ind D fixed target M t := by
  rw [err, Finset.card_filter]; push_cast; rfl

theorem signed_eq (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (S : Finset (Finset (Fin k))) : signed D fixed target S = ∑ t, sig D fixed target S t := by
  rw [signed, Finset.card_filter, Finset.card_filter]; push_cast
  rw [← Finset.sum_sub_distrib]; rfl

theorem ind_point (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (M : Finset (Finset (Fin k))) (t : Fin q) :
    ind D fixed target M t = ind D fixed target ∅ t +
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : ℤ) ^ S.card * sig D fixed target S t := by
  have hk := key M (D t)
  have hne : (M ∩ D t).Nonempty ↔ ¬ (M ∩ D t = ∅) := by
    rw [Finset.nonempty_iff_ne_empty]
  cases hf : fixed t <;> cases ht : target t
  ·
    have : ∀ S : Finset (Finset (Fin k)), sig D fixed target S t = - (if S ⊆ D t then 1 else 0) := by
      intro S; simp [sig, hf, ht]
    simp only [this, mul_neg, Finset.sum_neg_distrib, hk]
    by_cases he : M ∩ D t = ∅
    · simp [ind, hf, ht, he]
    · have : (M ∩ D t).Nonempty := hne.2 he
      simp [ind, hf, ht, he, this]
  ·
    have : ∀ S : Finset (Finset (Fin k)), sig D fixed target S t = (if S ⊆ D t then 1 else 0) := by
      intro S; simp [sig, hf, ht]
    simp only [this, hk]
    by_cases he : M ∩ D t = ∅
    · simp [ind, hf, ht, he]
    · have : (M ∩ D t).Nonempty := hne.2 he
      simp [ind, hf, ht, he, this]
  · have : ∀ S : Finset (Finset (Fin k)), sig D fixed target S t = 0 := by
      intro S; simp [sig, hf]
    simp [this, ind, hf, ht]
  · have : ∀ S : Finset (Finset (Fin k)), sig D fixed target S t = 0 := by
      intro S; simp [sig, hf]
    simp [this, ind, hf, ht]

theorem part1 (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (M : Finset (Finset (Fin k))) :
    (err D fixed target M : Int) = (err D fixed target ∅ : Int) +
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : Int) ^ S.card * signed D fixed target S := by
  rw [err_eq, err_eq]
  simp only [signed_eq, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  exact ind_point D fixed target M t

def coef (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (S : Finset (Finset (Fin k))) : ℤ :=
  if S = ∅ then (err D fixed target ∅ : ℤ) else (-1 : ℤ) ^ S.card * signed D fixed target S

theorem err_coef (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool)
    (M : Finset (Finset (Fin k))) :
    (err D fixed target M : ℤ) = ∑ S ∈ M.powerset, coef D fixed target S := by
  rw [part1, ← Finset.sum_filter_add_sum_filter_not M.powerset (fun T => T.Nonempty)]
  have h3 : M.powerset.filter (fun T => ¬ T.Nonempty) = {∅} := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.not_nonempty_iff_eq_empty,
      Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨Finset.empty_subset _, rfl⟩
  rw [h3, Finset.sum_singleton]
  have : ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), coef D fixed target S =
      ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : Int) ^ S.card * signed D fixed target S := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [Finset.mem_filter] at hS
    simp [coef, Finset.nonempty_iff_ne_empty.1 hS.2]
  rw [this]; simp [coef]; ring

theorem uniq (δ : Finset (Finset (Fin k)) → ℤ)
    (h : ∀ M, valid M → ∑ S ∈ M.powerset, δ S = 0) : ∀ M, valid M → δ M = 0 := by
  intro M
  induction M using Finset.strongInduction with
  | H M ih =>
    intro hM
    have hs := h M hM
    rw [Finset.sum_eq_single M] at hs
    · exact hs
    · intro S hS hSM
      have hsub : S ⊂ M := Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1 hS, hSM⟩
      exact ih S hsub (valid_mono hM hsub.subset)
    · intro hn; exact absurd (Finset.mem_powerset.2 (subset_refl M)) hn

theorem part2 (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool) (d : ℕ) :
    ((∃ h : Finset (Finset (Fin k)) → Int, ∀ M, valid M →
      (err D fixed target M : Int) = ∑ S ∈ M.powerset.filter (fun T => T.card ≤ d), h S) ↔
      ∀ S, valid S → d < S.card → signed D fixed target S = 0) := by
  constructor
  · rintro ⟨h, hh⟩ S hS hd
    let h' : Finset (Finset (Fin k)) → ℤ := fun S => if S.card ≤ d then h S else 0
    have hzero := uniq (fun S => coef D fixed target S - h' S) (by
      intro M hM
      rw [Finset.sum_sub_distrib, ← err_coef, hh M hM, Finset.sum_filter]
      simp [h']) S hS
    have hS0 : S ≠ ∅ := by
      intro he; rw [he, Finset.card_empty] at hd; omega
    simp only [coef, hS0, ite_false, h', show ¬ S.card ≤ d by omega, sub_zero] at hzero
    rcases mul_eq_zero.1 hzero with hp | hp
    · exact absurd hp (pow_ne_zero _ (by norm_num))
    · exact hp
  · intro hz
    refine ⟨coef D fixed target, fun M hM => ?_⟩
    rw [err_coef]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro S hS hSn
    rw [Finset.mem_filter, not_and, not_le] at hSn
    have hd := hSn hS
    have hS0 : S ≠ ∅ := by
      intro he; rw [he, Finset.card_empty] at hd; omega
    simp [coef, hS0, hz S (valid_mono hM (Finset.mem_powerset.1 hS)) hd]

end PEqualNP.Outside.L_lib_877_aux

theorem PEqualNP.Outside.L_lib_877 : (∀ (k q : Nat) (D : Fin q → Finset (Finset (Fin k))) (fixed target : Fin q → Bool),
  let valid := fun (M : Finset (Finset (Fin k))) =>
    (∀ e ∈ M, e.card = 2) ∧ (∀ e ∈ M, ∀ g ∈ M, e ≠ g → Disjoint e g)
  let err := fun (M : Finset (Finset (Fin k))) =>
    (Finset.univ.filter (fun t : Fin q =>
      (fixed t || decide ((M ∩ D t).Nonempty)) ≠ target t)).card
  let signed := fun (S : Finset (Finset (Fin k))) =>
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = true)).card : Int) -
    ((Finset.univ.filter (fun t : Fin q => fixed t = false ∧ S ⊆ D t ∧ target t = false)).card : Int)
  (∀ M, valid M → (err M : Int) = (err ∅ : Int) +
    ∑ S ∈ M.powerset.filter (fun T => T.Nonempty), (-1 : Int)^S.card * signed S) ∧
  ∀ d : Nat, ((∃ h : Finset (Finset (Fin k)) → Int, ∀ M, valid M →
    (err M : Int) = ∑ S ∈ M.powerset.filter (fun T => T.card ≤ d), h S) ↔
    ∀ S, valid S → d < S.card → signed S = 0)) := by
  intro k q D fixed target
  exact ⟨fun M _ => L_lib_877_aux.part1 D fixed target M,
    fun d => L_lib_877_aux.part2 D fixed target d⟩
