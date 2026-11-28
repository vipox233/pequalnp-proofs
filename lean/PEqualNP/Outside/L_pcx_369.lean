import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_369
open Classical

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Cons {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) : Prop :=
  ∀ (j : Fin p.length), q (List.take (↑j) p) x = p.get j

lemma fw_cons_iff {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V) :
    Cons q p x ↔ ∀ (j : ℕ) (h : j < p.length), q (p.take j) x = p[j] := by
  constructor
  · intro h j hj
    exact h ⟨j, hj⟩
  · intro h j
    exact h j.1 j.2

lemma fw_cons_ext {V : Type} (q : List Bool → V → Bool) (p : List Bool) (x : V)
    (h : Cons q p x) : Cons q (p ++ [q p x]) x := by
  rw [fw_cons_iff] at h ⊢
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h1 | h1
  · rw [List.take_append_of_le_length h1.le, List.getElem_append_left h1]
    exact h j h1
  · subst h1
    simp

lemma fw_reach_aux {V : Type} (N J : Finset (List Bool)) (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) (d : ℕ) :
    ∃ p ∈ N, Cons q p x ∧ (p ∉ J ∨ d ≤ p.length) := by
  induction d with
  | zero => exact ⟨[], hS.1, fun j => j.elim0, Or.inr (Nat.zero_le _)⟩
  | succ d ih =>
    obtain ⟨p, hp, hc, h⟩ := ih
    by_cases hJ : p ∈ J
    · refine ⟨p ++ [q p x], ?_, fw_cons_ext q p x hc, Or.inr ?_⟩
      · have h2 := hS.2.2.2 p hJ
        cases q p x
        · exact h2.1
        · exact h2.2
      · have h3 : d ≤ p.length := h.resolve_left (not_not.mpr hJ)
        rw [List.length_append, List.length_singleton]
        omega
    · exact ⟨p, hp, hc, Or.inl hJ⟩

lemma fw_reach {V : Type} (N J : Finset (List Bool)) (hS : Shape N J)
    (q : List Bool → V → Bool) (x : V) : ∃ p ∈ N \ J, Cons q p x := by
  obtain ⟨p, hp, hc, h⟩ := fw_reach_aux N J hS q x (N.sup List.length + 1)
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hp, ?_⟩, hc⟩
  rcases h with h | h
  · exact h
  · have h1 := Finset.le_sup (f := List.length) hp
    omega

lemma fw_internal (N J : Finset (List Bool)) (hS : Shape N J) (p s : List Bool)
    (hs : s ≠ []) (h : p ++ s ∈ N) : p ∈ J := by
  induction s using List.reverseRecOn with
  | nil => exact absurd rfl hs
  | append_singleton s b ih =>
    rw [← List.append_assoc] at h
    have h1 := hS.2.2.1 _ b h
    by_cases hs1 : s = []
    · subst hs1
      simpa using h1
    · exact ih hs1 (hS.2.1 h1)

def sg (u : ZMod 2) : ℤ := if u = 0 then 1 else -1

theorem sg_add (u v : ZMod 2) : sg (u + v) = sg u * sg v := by
  fin_cases u <;> fin_cases v <;> decide

theorem sg_sub (u v : ZMod 2) : sg (u - v) = sg u * sg v := by
  fin_cases u <;> fin_cases v <;> decide

theorem sg_abs (u : ZMod 2) : |sg u| = 1 := by
  fin_cases u <;> decide

theorem sg_mul_eq (u v : ZMod 2) : sg u * sg v = if u = v then 1 else -1 := by
  fin_cases u <;> fin_cases v <;> decide

theorem z2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  fin_cases u
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem add_self_z2 {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (f : M) : f + f = 0 := by
  rw [← two_smul (ZMod 2) f]
  have h : (2 : ZMod 2) = 0 := rfl
  rw [h, zero_smul]

theorem charW {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) (V →ₗ[ZMod 2] ZMod 2)) (Wf : Finset (V →ₗ[ZMod 2] ZMod 2))
    (hW : ∀ φ, φ ∈ Wf ↔ φ ∈ W) (w : V) :
    ∑ φ ∈ Wf, sg (φ w) = if ∀ φ ∈ W, φ w = 0 then (Wf.card : ℤ) else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro φ hφ
    simp [h φ ((hW φ).1 hφ), sg]
  · push Not at h
    obtain ⟨φ0, h0, h1⟩ := h
    have h1' : φ0 w = 1 := (z2_cases (φ0 w)).resolve_left h1
    have key : ∑ φ ∈ Wf, sg (φ w) = - ∑ φ ∈ Wf, sg (φ w) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_nbij' (fun φ => φ + φ0) (fun φ => φ + φ0)
      · intro φ hφ
        simp only [hW] at hφ ⊢
        exact W.add_mem hφ h0
      · intro φ hφ
        simp only [hW] at hφ ⊢
        exact W.add_mem hφ h0
      · intro φ _
        simp [add_assoc, add_self_z2]
      · intro φ _
        simp [add_assoc, add_self_z2]
      · intro φ _
        simp only [LinearMap.add_apply, sg_add, h1']
        have : sg 1 = -1 := rfl
        rw [this]
        ring
    linarith

theorem charV {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (φ : V →ₗ[ZMod 2] ZMod 2) :
    ∑ z : V, sg (φ z) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
  split_ifs with h
  · subst h
    simp [sg]
  · have : ∃ v, φ v ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (LinearMap.ext hc)
    obtain ⟨v, hv⟩ := this
    have hv' : φ v = 1 := (z2_cases (φ v)).resolve_left hv
    have key : ∑ z : V, sg (φ z) = - ∑ z : V, sg (φ z) := by
      rw [← Finset.sum_neg_distrib]
      apply Fintype.sum_equiv (Equiv.addRight v)
      intro z
      simp only [Equiv.coe_addRight, map_add, sg_add, hv']
      have : sg 1 = -1 := rfl
      rw [this]
      ring
    linarith

theorem cellCard {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (W : Submodule (ZMod 2) (V →ₗ[ZMod 2] ZMod 2)) (Wf : Finset (V →ₗ[ZMod 2] ZMod 2))
    (hW : ∀ φ, φ ∈ Wf ↔ φ ∈ W) (z0 : V) :
    Wf.card * (Finset.univ.filter (fun z : V => ∀ φ ∈ W, φ z = φ z0)).card = Fintype.card V := by
  have e1 : ∑ z : V, ∑ φ ∈ Wf, sg (φ (z - z0)) =
      ((Wf.card * (Finset.univ.filter (fun z : V => ∀ φ ∈ W, φ z = φ z0)).card : ℕ) : ℤ) := by
    have hc : ∀ z, (∀ φ ∈ W, φ (z - z0) = 0) ↔ (∀ φ ∈ W, φ z = φ z0) := by
      intro z
      simp [map_sub, sub_eq_zero]
    simp only [charW W Wf hW, hc]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul]
    push_cast
    ring
  have e2 : ∑ z : V, ∑ φ ∈ Wf, sg (φ (z - z0)) = (Fintype.card V : ℤ) := by
    rw [Finset.sum_comm]
    have : ∀ φ ∈ Wf, ∑ z : V, sg (φ (z - z0)) = if φ = 0 then (Fintype.card V : ℤ) else 0 := by
      intro φ _
      simp only [map_sub, sg_sub]
      rw [← Finset.sum_mul, charV]
      split_ifs with h
      · subst h; simp [sg]
      · simp
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    have h0 : (0 : V →ₗ[ZMod 2] ZMod 2) ∈ Wf := (hW 0).2 W.zero_mem
    simp [h0]
  exact_mod_cast e1.symm.trans e2

theorem indic {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (W : Submodule (ZMod 2) (V →ₗ[ZMod 2] ZMod 2)) (Wf : Finset (V →ₗ[ZMod 2] ZMod 2))
    (hW : ∀ φ, φ ∈ Wf ↔ φ ∈ W) (z0 z : V) :
    (Wf.card : ℤ) * (if ∀ φ ∈ W, φ z = φ z0 then 1 else 0) = ∑ φ ∈ Wf, sg (φ z - φ z0) := by
  have h := charW W Wf hW (z - z0)
  simp only [map_sub] at h
  rw [h]
  have hc : (∀ φ ∈ W, φ z - φ z0 = 0) ↔ (∀ φ ∈ W, φ z = φ z0) := by
    simp [sub_eq_zero]
  by_cases h2 : ∀ φ ∈ W, φ z = φ z0
  · rw [if_pos h2, if_pos (hc.2 h2)]; ring
  · rw [if_neg h2, if_neg (fun h3 => h2 (hc.1 h3))]; ring

theorem compNe {X : Type} [AddCommGroup X] [Module (ZMod 2) X]
    (W : Submodule (ZMod 2) (ZMod 2 × X →ₗ[ZMod 2] ZMod 2))
    (hf : LinearMap.fst (ZMod 2) (ZMod 2) X ∉ W) (φ : ZMod 2 × X →ₗ[ZMod 2] ZMod 2)
    (hφ : φ ∈ W) (h0 : φ ≠ 0) : φ.comp (LinearMap.inr (ZMod 2) (ZMod 2) X) ≠ 0 := by
  intro hc
  have hx : ∀ x : X, φ (0, x) = 0 := fun x => by
    have := LinearMap.congr_fun hc x
    simpa using this
  have hsplit : ∀ c : ZMod 2, ∀ x : X, φ (c, x) = c * φ (1, 0) := by
    intro c x
    have e : ((c, x) : ZMod 2 × X) = c • ((1 : ZMod 2), (0 : X)) + ((0 : ZMod 2), x) := by
      ext <;> simp
    rw [e, map_add, map_smul, hx, smul_eq_mul, add_zero]
  rcases z2_cases (φ (1, 0)) with h1 | h1
  · apply h0
    apply LinearMap.ext
    rintro ⟨c, x⟩
    rw [hsplit, h1, mul_zero]
    rfl
  · apply hf
    have : φ = LinearMap.fst (ZMod 2) (ZMod 2) X := by
      apply LinearMap.ext
      rintro ⟨c, x⟩
      rw [hsplit, h1, mul_one]
      rfl
    rw [← this]
    exact hφ

theorem termBound {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X]
    (π : X ≃ X) (B : ℕ)
    (hB : ∀ a b : X →ₗ[ZMod 2] ZMod 2, a ≠ 0 → b ≠ 0 →
      (∑ x : X, if a x = b (π x) then (1 : ℤ) else -1).natAbs ≤ B)
    (W : Submodule (ZMod 2) (ZMod 2 × X →ₗ[ZMod 2] ZMod 2))
    (hf : LinearMap.fst (ZMod 2) (ZMod 2) X ∉ W) (z0 : ZMod 2 × X)
    (φ ψ : ZMod 2 × X →ₗ[ZMod 2] ZMod 2) (hφ : φ ∈ W) (hψ : ψ ∈ W) :
    ∑ a : X, sg (φ (0, a) - φ z0) * sg (ψ (1, π a) - ψ z0) ≤
      (if φ = 0 then (if ψ = 0 then (Fintype.card X : ℤ) else 0) else (if ψ = 0 then 0 else (B : ℤ))) := by
  set α := φ.comp (LinearMap.inr (ZMod 2) (ZMod 2) X) with hα
  set β := ψ.comp (LinearMap.inr (ZMod 2) (ZMod 2) X) with hβ
  have e1 : ∀ a : X, φ (0, a) = α a := fun a => rfl
  have e2 : ∀ a : X, ψ (1, π a) = ψ (1, 0) + β (π a) := by
    intro a
    have : ((1 : ZMod 2), π a) = ((1 : ZMod 2), (0 : X)) + ((0 : ZMod 2), π a) := by ext <;> simp
    rw [this, map_add]
    rfl
  have hs : ∑ a : X, sg (φ (0, a) - φ z0) * sg (ψ (1, π a) - ψ z0) =
      (sg (φ z0) * sg (ψ z0) * sg (ψ (1, 0))) * ∑ a : X, sg (α a) * sg (β (π a)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [e1, e2, sg_sub, sg_sub, sg_add]
    ring
  have hle : ∑ a : X, sg (φ (0, a) - φ z0) * sg (ψ (1, π a) - ψ z0) ≤
      |∑ a : X, sg (α a) * sg (β (π a))| := by
    rw [hs]
    calc _ ≤ |(sg (φ z0) * sg (ψ z0) * sg (ψ (1, 0))) * ∑ a : X, sg (α a) * sg (β (π a))| := le_abs_self _
      _ = _ := by rw [abs_mul, abs_mul, abs_mul, sg_abs, sg_abs, sg_abs]; ring
  refine le_trans hle ?_
  have sumB : ∀ γ : X →ₗ[ZMod 2] ZMod 2, γ ≠ 0 → ∑ x : X, sg (γ x) = 0 := by
    intro γ hγ
    rw [charV, if_neg hγ]
  by_cases h1 : φ = 0
  · have hα0 : α = 0 := by rw [hα, h1]; rfl
    rw [if_pos h1]
    by_cases h2 : ψ = 0
    · have hβ0 : β = 0 := by rw [hβ, h2]; rfl
      rw [if_pos h2, hα0, hβ0]
      simp [sg]
    · rw [if_neg h2, hα0]
      have hb := compNe W hf ψ hψ h2
      simp only [LinearMap.zero_apply]
      have : sg 0 = 1 := rfl
      simp only [this, one_mul]
      rw [Equiv.sum_comp π (fun x => sg (β x)), sumB β hb]
      simp
  · rw [if_neg h1]
    have ha := compNe W hf φ hφ h1
    by_cases h2 : ψ = 0
    · have hβ0 : β = 0 := by rw [hβ, h2]; rfl
      rw [if_pos h2, hβ0]
      simp only [LinearMap.zero_apply]
      have : sg 0 = 1 := rfl
      simp only [this, mul_one]
      rw [sumB α ha]
      simp
    · rw [if_neg h2]
      have hb := compNe W hf ψ hψ h2
      have := hB α β ha hb
      simp only [sg_mul_eq]
      rw [← Int.natCast_natAbs]
      exact_mod_cast this

theorem sumOff {X : Type} [AddCommGroup X] [Module (ZMod 2) X] (Wf : Finset (ZMod 2 × X →ₗ[ZMod 2] ZMod 2)) (h0 : (0 : ZMod 2 × X →ₗ[ZMod 2] ZMod 2) ∈ Wf) (c : ℤ) :
    ∑ ψ ∈ Wf, (if ψ = 0 then (0 : ℤ) else c) = ((Wf.card : ℤ) - 1) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem h0, nsmul_eq_mul]
  have : 1 ≤ Wf.card := Finset.card_pos.mpr ⟨0, h0⟩
  push_cast [this]
  ring

theorem sumBnd {X : Type} [AddCommGroup X] [Module (ZMod 2) X] (Wf : Finset (ZMod 2 × X →ₗ[ZMod 2] ZMod 2)) (h0 : (0 : ZMod 2 × X →ₗ[ZMod 2] ZMod 2) ∈ Wf) (K c : ℤ) :
    ∑ φ ∈ Wf, ∑ ψ ∈ Wf, (if φ = 0 then (if ψ = 0 then K else 0) else (if ψ = 0 then 0 else c)) =
      K + ((Wf.card : ℤ) - 1) ^ 2 * c := by
  have inner : ∀ φ ∈ Wf, ∑ ψ ∈ Wf, (if φ = 0 then (if ψ = 0 then K else 0) else (if ψ = 0 then 0 else c))
      = (if φ = 0 then K else 0) + (if φ = 0 then (0 : ℤ) else ((Wf.card : ℤ) - 1) * c) := by
    intro φ _
    by_cases hφ : φ = 0
    · simp only [hφ, if_true]
      rw [Finset.sum_ite_eq' Wf 0 (fun _ => K), if_pos h0]
      ring
    · simp only [hφ, if_false]
      rw [sumOff Wf h0 c]
      ring
  rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, Finset.sum_ite_eq' Wf 0 (fun _ => K), if_pos h0,
    sumOff Wf h0]
  ring

theorem cellBound {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X]
    (π : X ≃ X) (B : ℕ)
    (hB : ∀ a b : X →ₗ[ZMod 2] ZMod 2, a ≠ 0 → b ≠ 0 →
      (∑ x : X, if a x = b (π x) then (1 : ℤ) else -1).natAbs ≤ B)
    (W : Submodule (ZMod 2) (ZMod 2 × X →ₗ[ZMod 2] ZMod 2)) (Wf : Finset (ZMod 2 × X →ₗ[ZMod 2] ZMod 2))
    (hW : ∀ φ, φ ∈ Wf ↔ φ ∈ W) (z0 : ZMod 2 × X) :
    (Wf.card : ℤ) ^ 2 * ((Finset.univ.filter (fun a : X => (∀ φ ∈ W, φ (0, a) = φ z0) ∧
      (∀ φ ∈ W, φ (1, π a) = φ z0))).card : ℤ) ≤ Fintype.card X + ((Wf.card : ℤ) - 1) ^ 2 * B := by
  have h0 : (0 : ZMod 2 × X →ₗ[ZMod 2] ZMod 2) ∈ Wf := (hW 0).2 W.zero_mem
  by_cases hf : LinearMap.fst (ZMod 2) (ZMod 2) X ∈ W
  · have : Finset.univ.filter (fun a : X => (∀ φ ∈ W, φ (0, a) = φ z0) ∧
        (∀ φ ∈ W, φ (1, π a) = φ z0)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      rintro a _ ⟨h1, h2⟩
      have e1 := h1 _ hf
      have e2 := h2 _ hf
      simp only [LinearMap.fst_apply] at e1 e2
      rw [← e1] at e2
      exact absurd e2 (by decide)
    rw [this]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero]
    positivity
  · have hc : ((Finset.univ.filter (fun a : X => (∀ φ ∈ W, φ (0, a) = φ z0) ∧
        (∀ φ ∈ W, φ (1, π a) = φ z0))).card : ℤ) = ∑ a : X,
        (if ∀ φ ∈ W, φ (0, a) = φ z0 then (1 : ℤ) else 0) *
        (if ∀ φ ∈ W, φ (1, π a) = φ z0 then (1 : ℤ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp_all
    rw [hc, Finset.mul_sum]
    have step : ∀ a : X, (Wf.card : ℤ) ^ 2 * ((if ∀ φ ∈ W, φ (0, a) = φ z0 then (1 : ℤ) else 0) *
        (if ∀ φ ∈ W, φ (1, π a) = φ z0 then (1 : ℤ) else 0)) =
        ∑ φ ∈ Wf, ∑ ψ ∈ Wf, sg (φ (0, a) - φ z0) * sg (ψ (1, π a) - ψ z0) := by
      intro a
      rw [← Finset.sum_mul_sum, ← indic W Wf hW z0 (0, a), ← indic W Wf hW z0 (1, π a)]
      ring
    rw [Finset.sum_congr rfl (fun a _ => step a), Finset.sum_comm]
    have swap : ∀ φ ∈ Wf, ∑ a : X, ∑ ψ ∈ Wf, sg (φ (0, a) - φ z0) * sg (ψ (1, π a) - ψ z0) =
        ∑ ψ ∈ Wf, ∑ a : X, sg (φ (0, a) - φ z0) * sg (ψ (1, π a) - ψ z0) :=
      fun φ _ => Finset.sum_comm
    rw [Finset.sum_congr rfl swap]
    refine le_trans (Finset.sum_le_sum (fun φ hφ => Finset.sum_le_sum (fun ψ hψ =>
      termBound π B hB W hf z0 φ ψ ((hW φ).1 hφ) ((hW ψ).1 hψ)))) (le_of_eq ?_)
    convert sumBnd Wf h0 (Fintype.card X : ℤ) (B : ℤ) using 8

theorem finD {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X] :
    Finite (ZMod 2 × X →ₗ[ZMod 2] ZMod 2) :=
  Finite.of_injective (fun f : ZMod 2 × X →ₗ[ZMod 2] ZMod 2 => (f : ZMod 2 × X → ZMod 2))
    DFunLike.coe_injective

def gens {D : Type} (f : ℕ → D) (j : ℕ) : Set D := {φ | ∃ i < j, f i = φ}

theorem gens_succ {D : Type} (f : ℕ → D) (j : ℕ) : gens f (j + 1) = insert (f j) (gens f j) := by
  ext φ
  simp only [gens, Set.mem_setOf_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact Or.inr ⟨i, h, rfl⟩
    · exact Or.inl (by rw [h])
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨j, Nat.lt_succ_self j, rfl⟩
    · exact ⟨i, by omega, rfl⟩

theorem gens_zero {D : Type} (f : ℕ → D) : gens f 0 = ∅ := by
  ext φ
  simp [gens]

theorem rk_succ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite (V →ₗ[ZMod 2] ZMod 2)]
    (f : ℕ → (V →ₗ[ZMod 2] ZMod 2)) (j : ℕ) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (gens f (j + 1))) ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (gens f j)) + 1 := by
  rw [gens_succ, Submodule.span_insert]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (ZMod 2 ∙ f j) (Submodule.span (ZMod 2) (gens f j))
  have h1 : Module.finrank (ZMod 2) (ZMod 2 ∙ f j) ≤ 1 := by
    have := finrank_span_le_card (R := ZMod 2) ({f j} : Set (V →ₗ[ZMod 2] ZMod 2))
    simpa using this
  omega

theorem span_iff {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (S : Set (V →ₗ[ZMod 2] ZMod 2))
    (z z0 : V) : (∀ φ ∈ Submodule.span (ZMod 2) S, φ z = φ z0) ↔ ∀ φ ∈ S, φ z = φ z0 := by
  constructor
  · intro h φ hφ
    exact h φ (Submodule.subset_span hφ)
  · intro h φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]

theorem dec_iff (u v b : ZMod 2) : decide (u = b) = decide (v = b) ↔ u = v := by
  revert u v b
  decide

theorem take_take_lt (p : List Bool) (i j : ℕ) (h : i ≤ j) : (p.take j).take i = p.take i := by
  rw [List.take_take]
  congr 1
  omega

theorem getD_take_lt (p : List Bool) (i j : ℕ) (h : i < j) :
    (p.take j).getD i false = p.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  rw [if_pos h]

theorem prefix_mem (N J : Finset (List Bool)) (hS : Shape N J)
    (p : List Bool) (hp : p ∈ N) (j : ℕ) (hj : j < p.length) : p.take j ∈ J := by
  apply fw_internal N J hS (p.take j) (p.drop j)
  · intro h
    have := congrArg List.length h
    simp at this
    omega
  · rw [List.take_append_drop]
    exact hp

theorem prefix_memN (N J : Finset (List Bool)) (hS : Shape N J)
    (p : List Bool) (hp : p ∈ N) (j : ℕ) (hj : j ≤ p.length) : p.take j ∈ N := by
  rcases Nat.lt_or_ge j p.length with h | h
  · exact hS.2.1 (prefix_mem N J hS p hp j h)
  · rw [List.take_of_length_le h]
    exact hp

def cellS {V : Type} (q : List Bool → V → Bool) (r : List Bool) (z : V) : Prop :=
  ∀ i < r.length, q (r.take i) z = r.getD i false

def WL {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (lf : List Bool → (V →ₗ[ZMod 2] ZMod 2))
    (r : List Bool) : Submodule (ZMod 2) (V →ₗ[ZMod 2] ZMod 2) :=
  Submodule.span (ZMod 2) (gens (fun i => lf (r.take i)) r.length)

theorem cellEq {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (J : Finset (List Bool))
    (q : List Bool → V → Bool) (lf : List Bool → (V →ₗ[ZMod 2] ZMod 2)) (bf : List Bool → ZMod 2)
    (hlf : ∀ p ∈ J, q p = fun x => decide (lf p x = bf p)) (r : List Bool)
    (hr : ∀ i < r.length, r.take i ∈ J) (z0 z : V) (h0 : cellS q r z0) :
    cellS q r z ↔ ∀ φ ∈ WL lf r, φ z = φ z0 := by
  rw [WL, span_iff]
  constructor
  · rintro hz φ ⟨i, hi, rfl⟩
    have a := hz i hi
    have b := h0 i hi
    rw [hlf _ (hr i hi)] at a b
    exact (dec_iff _ _ _).1 (a.trans b.symm)
  · intro h i hi
    have b := h0 i hi
    rw [hlf _ (hr i hi)] at b ⊢
    rw [← b]
    exact (dec_iff _ _ _).2 (h _ ⟨i, hi, rfl⟩)

theorem cons_cell {V : Type} (q : List Bool → V → Bool) (p : List Bool) (z : V) (h : Cons q p z)
    (j : ℕ) (hj : j ≤ p.length) : cellS q (p.take j) z := by
  intro i hi
  rw [List.length_take, min_eq_left hj] at hi
  rw [take_take_lt p i j hi.le, getD_take_lt p i j hi]
  rw [fw_cons_iff] at h
  rw [h i (by omega), List.getD_eq_getElem]

theorem cell_cons {V : Type} (q : List Bool → V → Bool) (p : List Bool) (z : V) (h : cellS q p z) :
    Cons q p z := by
  rw [fw_cons_iff]
  intro j hj
  rw [h j hj, List.getD_eq_getElem]

theorem WL_take {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (lf : List Bool → (V →ₗ[ZMod 2] ZMod 2))
    (p : List Bool) (j : ℕ) (hj : j ≤ p.length) :
    WL lf (p.take j) = Submodule.span (ZMod 2) (gens (fun i => lf (p.take i)) j) := by
  unfold WL
  congr 1
  ext φ
  simp only [gens, Set.mem_setOf_eq, List.length_take, min_eq_left hj]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [take_take_lt p i j hi.le]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by rw [take_take_lt p i j hi.le]⟩

theorem take_succ_getD (l : List Bool) (k : ℕ) (hk : k < l.length) :
    l.take (k + 1) = l.take k ++ [l.getD k false] := by
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]
  rfl

theorem prefix_agree {V : Type} (q : List Bool → V → Bool) (r r' : List Bool) (z : V)
    (h : cellS q r z) (h' : cellS q r' z) (hle : r.length ≤ r'.length) : r = r'.take r.length := by
  have key : ∀ k ≤ r.length, r.take k = r'.take k := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      rw [take_succ_getD r k (by omega), take_succ_getD r' k (by omega), ih']
      have e1 := h k (by omega)
      have e2 := h' k (by omega)
      rw [← e1, ← e2, ih']
  have := key r.length le_rfl
  rw [List.take_length] at this
  exact this

theorem cardW {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype (V →ₗ[ZMod 2] ZMod 2)]
    (W : Submodule (ZMod 2) (V →ₗ[ZMod 2] ZMod 2)) :
    (Finset.univ.filter (fun φ => φ ∈ W)).card = 2 ^ Module.finrank (ZMod 2) W := by
  have : Finite W := inferInstance
  rw [← Fintype.card_subtype, Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem cellCardL {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X] (m : ℕ)
    (hX : Fintype.card X = 2 ^ m) [Fintype (ZMod 2 × X →ₗ[ZMod 2] ZMod 2)]
    (J : Finset (List Bool))
    (q : List Bool → ZMod 2 × X → Bool) (lf : List Bool → (ZMod 2 × X →ₗ[ZMod 2] ZMod 2))
    (bf : List Bool → ZMod 2)
    (hlf : ∀ p ∈ J, q p = fun x => decide (lf p x = bf p)) (r : List Bool)
    (hr : ∀ i < r.length, r.take i ∈ J) (z0 : ZMod 2 × X) (h0 : cellS q r z0) :
    2 ^ Module.finrank (ZMod 2) (WL lf r) * (Finset.univ.filter (fun z => cellS q r z)).card =
      2 ^ (m + 1) := by
  have h := cellCard (WL lf r) (Finset.univ.filter (fun φ => φ ∈ WL lf r)) (by simp) z0
  rw [cardW] at h
  have e : Finset.univ.filter (fun z => cellS q r z) =
      Finset.univ.filter (fun z : ZMod 2 × X => ∀ φ ∈ WL lf r, φ z = φ z0) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact cellEq J q lf bf hlf r hr z0 z h0
  rw [e]
  convert h using 1
  · first
    | rfl
    | (congr 2; ext; simp)
    | convert rfl
  · rw [Fintype.card_prod, ZMod.card, hX, pow_succ]
    ring

theorem okLeaf {X : Type} (π : X ≃ X) (o : X) (z : ZMod 2 × X)
    (h : if z.1 = 0 then z.2 = o else z.2 = π o) : z = (0, o) ∨ z = (1, π o) := by
  obtain ⟨c, x⟩ := z
  rcases z2_cases c with hc | hc
  · subst hc
    simp only [if_true] at h
    left
    rw [h]
  · subst hc
    have : ¬ ((1 : ZMod 2) = 0) := by decide
    simp only [this, if_false] at h
    right
    rw [h]

theorem core {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X] (m B : ℕ)
    (hX : Fintype.card X = 2 ^ m) (π : X ≃ X)
    (hB : ∀ a b : X →ₗ[ZMod 2] ZMod 2, a ≠ 0 → b ≠ 0 →
      (∑ x : X, if a x = b (π x) then (1 : ℤ) else -1).natAbs ≤ B)
    (N J : Finset (List Bool)) (q : List Bool → ZMod 2 × X → Bool) (out : List Bool → X)
    (hS : Shape N J)
    (hq : ∀ p ∈ J, ∃ (l : ZMod 2 × X →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), q p = fun x => decide (l x = b))
    (hok : ∀ p ∈ N \ J, ∀ z : ZMod 2 × X, Cons q p z →
      (if z.1 = 0 then z.2 = out p else z.2 = π (out p)))
    (t : ℕ) (ht : t ≤ m) :
    2 ^ t * 2 ^ (m + 1) ≤ 2 ^ t * (N \ J).card + 2 ^ m + B * (2 ^ t - 1) ^ 2 := by
  classical
  haveI hFin := finD (X := X)
  letI : Fintype (ZMod 2 × X →ₗ[ZMod 2] ZMod 2) := Fintype.ofFinite _
  have hq' : ∀ p, ∃ (l : ZMod 2 × X →ₗ[ZMod 2] ZMod 2) (b : ZMod 2),
      p ∈ J → q p = fun x => decide (l x = b) := by
    intro p
    by_cases hp : p ∈ J
    · obtain ⟨l, b, h⟩ := hq p hp
      exact ⟨l, b, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hp⟩
  choose lf bf hlf using hq'
  have hreach := fun z => fw_reach N J hS q z
  choose ℓ hℓN hℓC using hreach
  have hcardV : Fintype.card (ZMod 2 × X) = 2 ^ (m + 1) := by
    rw [Fintype.card_prod, ZMod.card, hX, pow_succ]
    ring
  have leafOk : ∀ p ∈ N \ J, ∀ z, Cons q p z → z = (0, out p) ∨ z = (1, π (out p)) :=
    fun p hp z hz => okLeaf π (out p) z (hok p hp z hz)
  set S := Finset.univ.filter (fun a : X => ℓ (0, a) = ℓ (1, π a)) with hSdef

  have part1 : 2 ^ (m + 1) ≤ (N \ J).card + S.card := by
    set T := S.image (fun a => ((1 : ZMod 2), π a)) with hT
    have hTle : T.card ≤ S.card := Finset.card_image_le
    have hinj : (Finset.univ \ T).card ≤ (N \ J).card := by
      apply Finset.card_le_card_of_injOn ℓ
      · intro z _
        exact hℓN z
      · intro z hz w hw hzw
        simp only [Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ, true_and,
          Finset.mem_coe] at hz hw
        have hz2 := leafOk (ℓ z) (hℓN z) z (hℓC z)
        have hw2 := leafOk (ℓ z) (hℓN z) w (hzw ▸ hℓC w)
        have bad : ∀ a : X, ℓ (0, a) = ℓ (1, π a) → ((1 : ZMod 2), π a) ∈ T := by
          intro a ha
          rw [hT]
          exact Finset.mem_image.mpr ⟨a, by rw [hSdef]; simp [ha], rfl⟩
        rcases hz2 with h1 | h1 <;> rcases hw2 with h2 | h2
        · rw [h1, h2]
        · exfalso; apply hw; rw [h2]; apply bad
          rw [← h1, ← h2]; exact hzw
        · exfalso; apply hz; rw [h1]; apply bad
          rw [← h1, ← h2]; exact hzw.symm
        · rw [h1, h2]
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
    rw [Finset.card_univ, hcardV] at this
    omega

  let rk : List Bool → ℕ → ℕ := fun p j =>
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (gens (fun i => lf (p.take i)) j))
  have prefJ : ∀ r ∈ N, ∀ i < r.length, r.take i ∈ J := fun r hr i hi => prefix_mem N J hS r hr i hi
  have leafRk : ∀ z, m ≤ rk (ℓ z) (ℓ z).length := by
    intro z
    set p := ℓ z
    have hpN : p ∈ N := (Finset.mem_sdiff.mp (hℓN z)).1
    have hcz : cellS q p z := by
      have := cons_cell q p z (hℓC z) p.length le_rfl
      rwa [List.take_length] at this
    have hc := cellCardL m hX J q lf bf hlf p (prefJ p hpN) z hcz
    have hsub : Finset.univ.filter (fun w => cellS q p w) ⊆ {(0, out p), (1, π (out p))} := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rcases leafOk p (hℓN z) w (cell_cons q p w hw) with h | h <;> simp [h]
    have h2 : (Finset.univ.filter (fun w => cellS q p w)).card ≤ 2 :=
      (Finset.card_le_card hsub).trans Finset.card_le_two
    have h3 : 2 ^ (m + 1) ≤ 2 ^ (rk p p.length + 1) := by
      rw [← hc, pow_succ]
      exact Nat.mul_le_mul_left _ h2
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
    omega
  have ex : ∀ a : X, ∃ j, t ≤ rk (ℓ (0, a)) j := fun a => ⟨_, ht.trans (leafRk _)⟩
  let jA : X → ℕ := fun a => Nat.find (ex a)
  have jA_le : ∀ a, jA a ≤ (ℓ (0, a)).length := fun a => Nat.find_min' (ex a) (ht.trans (leafRk _))
  have rkA : ∀ a, rk (ℓ (0, a)) (jA a) = t := by
    intro a
    have hge : t ≤ rk (ℓ (0, a)) (jA a) := Nat.find_spec (ex a)
    apply le_antisymm _ hge
    by_cases h0 : jA a = 0
    · have : rk (ℓ (0, a)) (jA a) = 0 := by
        show Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (gens _ (jA a))) = 0
        rw [h0, gens_zero, Submodule.span_empty, finrank_bot]
      exact this.le.trans (Nat.zero_le t)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      have hlt : ¬ t ≤ rk (ℓ (0, a)) k := Nat.find_min (ex a) (by have hk' : Nat.find (ex a) = k.succ := hk; rw [hk']; exact Nat.lt_succ_self k)
      have hs := rk_succ (fun i => lf ((ℓ (0, a)).take i)) k
      show Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (gens _ (jA a))) ≤ t
      rw [hk]
      have : rk (ℓ (0, a)) k < t := by omega
      exact le_trans hs (Nat.succ_le_of_lt this)
  let rA : X → List Bool := fun a => (ℓ (0, a)).take (jA a)
  have rA_len : ∀ a, (rA a).length = jA a := fun a => by
    simp only [rA, List.length_take]
    exact min_eq_left (jA_le a)
  have rA_N : ∀ a, rA a ∈ N := fun a =>
    prefix_memN N J hS _ (Finset.mem_sdiff.mp (hℓN _)).1 _ (jA_le a)
  have rA_rk : ∀ a, Module.finrank (ZMod 2) (WL lf (rA a)) = t := by
    intro a
    simp only [rA]
    rw [WL_take lf _ _ (jA_le a)]
    exact rkA a
  have rA_cell0 : ∀ a, cellS q (rA a) (0, a) := fun a => cons_cell q _ _ (hℓC _) _ (jA_le a)
  have rA_cell1 : ∀ a ∈ S, cellS q (rA a) (1, π a) := by
    intro a ha
    have ha' : ℓ (0, a) = ℓ (1, π a) := by rw [hSdef] at ha; simpa using ha
    have := hℓC (1, π a)
    rw [← ha'] at this
    exact cons_cell q _ _ this _ (jA_le a)
  have disj : ∀ a a' : X, ∀ z, cellS q (rA a) z → cellS q (rA a') z → rA a = rA a' := by
    have half : ∀ a a' : X, ∀ z, cellS q (rA a) z → cellS q (rA a') z → jA a ≤ jA a' →
        rA a = rA a' := by
      intro a a' z h h' hle
      have e := prefix_agree q (rA a) (rA a') z h h' (by rw [rA_len, rA_len]; exact hle)
      rw [rA_len] at e
      have e2 : rA a = (ℓ (0, a')).take (jA a) := by
        rw [e]
        simp only [rA]
        exact take_take_lt _ _ _ hle
      have hrk : t ≤ rk (ℓ (0, a')) (jA a) := by
        have := rA_rk a
        rw [e2, WL_take lf _ _ (hle.trans (jA_le a'))] at this
        exact this.symm.le
      have hle2 : jA a' ≤ jA a := Nat.find_min' (ex a') hrk
      have heq : jA a = jA a' := le_antisymm hle hle2
      rw [e2, heq]
    intro a a' z h h'
    rcases le_total (jA a) (jA a') with hle | hle
    · exact half a a' z h h' hle
    · exact (half a' a z h' h hle).symm
  set R := S.image rA with hR
  have cellR : ∀ r ∈ R, ∃ a, rA a = r := by
    intro r hr
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨a, rfl⟩
  have Rcard : R.card ≤ 2 ^ t := by
    have hc : ∀ r ∈ R, 2 ^ t * (Finset.univ.filter (fun z => cellS q r z)).card = 2 ^ (m + 1) := by
      intro r hr
      obtain ⟨a, rfl⟩ := cellR r hr
      have := cellCardL m hX J q lf bf hlf (rA a) (prefJ _ (rA_N a)) (0, a) (rA_cell0 a)
      rwa [rA_rk a] at this
    have hpd : (R : Set (List Bool)).PairwiseDisjoint (fun r => Finset.univ.filter (fun z => cellS q r z)) := by
      intro r hr r' hr' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro z hz hz'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
      obtain ⟨a, rfl⟩ := cellR r hr
      obtain ⟨a', rfl⟩ := cellR r' hr'
      exact hne (disj a a' z hz hz')
    have hU := Finset.card_biUnion hpd
    have hle : (R.biUnion (fun r => Finset.univ.filter (fun z => cellS q r z))).card ≤ 2 ^ (m + 1) := by
      rw [← hcardV]
      exact Finset.card_le_univ _
    rw [hU] at hle
    have h2 : 2 ^ t * ∑ r ∈ R, (Finset.univ.filter (fun z => cellS q r z)).card = R.card * 2 ^ (m + 1) := by
      rw [Finset.mul_sum, Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul]
    have h3 : R.card * 2 ^ (m + 1) ≤ 2 ^ t * 2 ^ (m + 1) := by
      rw [← h2]
      exact Nat.mul_le_mul_left _ hle
    exact Nat.le_of_mul_le_mul_right h3 (by positivity)

  let cnt : List Bool → ℕ := fun r =>
    (Finset.univ.filter (fun a : X => cellS q r (0, a) ∧ cellS q r (1, π a))).card
  have cntB : ∀ r ∈ R, ((2 : ℤ) ^ t) ^ 2 * (cnt r : ℤ) ≤ 2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B := by
    intro r hr
    obtain ⟨a, rfl⟩ := cellR r hr
    have h := cellBound π B hB (WL lf (rA a)) (Finset.univ.filter (fun φ => φ ∈ WL lf (rA a)))
      (by simp) (0, a)
    rw [cardW, rA_rk a, hX] at h
    have e : Finset.univ.filter (fun b : X => cellS q (rA a) (0, b) ∧ cellS q (rA a) (1, π b)) =
        Finset.univ.filter (fun b : X => (∀ φ ∈ WL lf (rA a), φ (0, b) = φ (0, a)) ∧
          (∀ φ ∈ WL lf (rA a), φ (1, π b) = φ (0, a))) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [cellEq J q lf bf hlf (rA a) (prefJ _ (rA_N a)) (0, a) (0, b) (rA_cell0 a),
        cellEq J q lf bf hlf (rA a) (prefJ _ (rA_N a)) (0, a) (1, π b) (rA_cell0 a)]
    have : (cnt (rA a) : ℤ) = ((Finset.univ.filter (fun b : X => (∀ φ ∈ WL lf (rA a), φ (0, b) = φ (0, a)) ∧
          (∀ φ ∈ WL lf (rA a), φ (1, π b) = φ (0, a)))).card : ℤ) := by
      simp only [cnt]
      rw [e]
    rw [this]
    push_cast at h
    convert h using 2
    all_goals first
      | rfl
      | (congr 2; ext; simp)
      | convert rfl
  have Sle : S.card ≤ ∑ r ∈ R, cnt r := by
    rw [Finset.card_eq_sum_card_image rA S]
    apply Finset.sum_le_sum
    intro r _
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← ha.2]
    exact ⟨rA_cell0 a, rA_cell1 a ha.1⟩
  have part2 : (2 : ℤ) ^ t * S.card ≤ 2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B := by
    have h1 : ((2 : ℤ) ^ t) ^ 2 * S.card ≤ ∑ r ∈ R, ((2 : ℤ) ^ t) ^ 2 * (cnt r : ℤ) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Sle
    have h2 : ∑ r ∈ R, ((2 : ℤ) ^ t) ^ 2 * (cnt r : ℤ) ≤ R.card * (2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B) := by
      calc _ ≤ ∑ r ∈ R, (2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B) := Finset.sum_le_sum cntB
        _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
    have hQ : (0 : ℤ) ≤ 2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B := by positivity
    have h3 : (R.card : ℤ) * (2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B) ≤ 2 ^ t * (2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B) := by
      apply mul_le_mul_of_nonneg_right _ hQ
      exact_mod_cast Rcard
    have h4 : (2 : ℤ) ^ t * ((2 : ℤ) ^ t * S.card) ≤ 2 ^ t * (2 ^ m + ((2 : ℤ) ^ t - 1) ^ 2 * B) := by
      nlinarith
    exact le_of_mul_le_mul_left h4 (by positivity)
  have h1t : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have key : ((2 ^ t * 2 ^ (m + 1) : ℕ) : ℤ) ≤ ((2 ^ t * (N \ J).card + 2 ^ m + B * (2 ^ t - 1) ^ 2 : ℕ) : ℤ) := by
    push_cast [h1t]
    have p1 : ((2 : ℤ) ^ (m + 1)) ≤ (N \ J).card + S.card := by exact_mod_cast part1
    nlinarith
  exact_mod_cast key

end PEqualNP.Outside.L_pcx_369

theorem PEqualNP.Outside.L_pcx_369 : (let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (X : Type) [AddCommGroup X] [Module (ZMod 2) X] [Fintype X]
      (m B : ℕ), Fintype.card X = 2^m →
    ∀ π : X ≃ X,
      (∀ a b : X →ₗ[ZMod 2] ZMod 2, a ≠ 0 → b ≠ 0 →
        (∑ x : X, if a x = b (π x) then (1 : ℤ) else -1).natAbs ≤ B) →
      ∀ (N J : Finset (List Bool)) (q : List Bool → (ZMod 2 × X) → Bool)
        (out : List Bool → X),
        cert (queries (ZMod 2 × X))
          (fun z a => if z.1 = 0 then z.2 = a else z.2 = π a) N J q out →
        ∀ t : ℕ, t ≤ m →
          2^t * 2^(m+1) ≤ 2^t * (N \ J).card + 2^m + B*(2^t-1)^2) := by
  intro shape queries cert X _ _ _ m B hX π hB N J q out hc t ht
  obtain ⟨hs, hq, hok⟩ := hc
  exact PEqualNP.Outside.L_pcx_369.core m B hX π hB N J q out hs hq
    (fun p hp z hz => hok p hp z hz) t ht
