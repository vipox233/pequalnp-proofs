import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33662_aux
namespace RectangleLibrary

open scoped BigOperators

lemma perm_map_two {N : ℕ} (a b c d : Fin N) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ σ : Equiv.Perm (Fin N), σ a = c ∧ σ b = d := by
  let σ₁ : Equiv.Perm (Fin N) := Equiv.swap a c
  have h1 : σ₁ a = c := Equiv.swap_apply_left a c
  let b' : Fin N := σ₁ b
  have hb' : b' ≠ c := by
    intro h
    exact hab (σ₁.injective (h1.trans h.symm))
  let σ₂ : Equiv.Perm (Fin N) := Equiv.swap b' d
  refine ⟨σ₁.trans σ₂, ?_, ?_⟩
  · simp only [Equiv.trans_apply, h1]
    exact Equiv.swap_apply_of_ne_of_ne hb'.symm hcd
  · simp only [Equiv.trans_apply]
    exact Equiv.swap_apply_left b' d

lemma circulant_reg {N t : ℕ} (ht : t < N) :
    let T0 : Fin N → Fin N → Bool := fun a b => decide ((b.val + N - a.val) % N < t)
    (∀ x, (Finset.univ.filter (fun y => T0 x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T0 x y)).card = t) := by
  intro T0
  have hN : 0 < N := by omega
  constructor
  · intro x
    let f : Fin t → Fin N := fun k => ⟨(x.val + k.val) % N, Nat.mod_lt _ hN⟩
    have hf_inj : Function.Injective f := by
      intro k₁ k₂ h
      have hv := congrArg Fin.val h
      simp only [f] at hv
      have h1 := k₁.isLt
      have h2 := k₂.isLt
      have hx := x.isLt
      apply Fin.ext
      by_cases hlt1 : x.val + k₁.val < N <;> by_cases hlt2 : x.val + k₂.val < N
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    have hfilt : Finset.univ.filter (fun y => T0 x y) = Finset.univ.image f := by
      ext y
      simp only [T0, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_image]
      constructor
      · intro hy
        let k : Fin t := ⟨(y.val + N - x.val) % N, hy⟩
        refine ⟨k, ?_⟩
        apply Fin.ext
        simp only [f, k]
        have hx := x.isLt
        have hylt := y.isLt
        by_cases hxy : x.val ≤ y.val
        · have hsub : (y.val + N - x.val) % N = y.val - x.val := by
            have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub]
          have h2 : x.val + (y.val - x.val) = y.val := by omega
          rw [h2, Nat.mod_eq_of_lt hylt]
        · have hsub : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
          rw [hsub]
          have h2 : x.val + (y.val + N - x.val) = y.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hylt]
      · rintro ⟨k, rfl⟩
        have hx := x.isLt
        have hk := k.isLt
        simp only [f]
        by_cases hlt : x.val + k.val < N
        · rw [Nat.mod_eq_of_lt hlt]
          have h1 : x.val + k.val + N - x.val = k.val + N := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          exact hk
        · have hmod : (x.val + k.val) % N = x.val + k.val - N := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have h1 : x.val + k.val - N + N - x.val = k.val := by omega
          rw [h1, Nat.mod_eq_of_lt (by omega)]
          exact hk
    rw [hfilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  · intro y
    let f : Fin t → Fin N := fun k => ⟨(y.val + N - k.val) % N, Nat.mod_lt _ hN⟩
    have hf_inj : Function.Injective f := by
      intro k₁ k₂ h
      have hv := congrArg Fin.val h
      simp only [f] at hv
      have h1 := k₁.isLt
      have h2 := k₂.isLt
      have hy := y.isLt
      apply Fin.ext
      by_cases hlt1 : k₁.val ≤ y.val <;> by_cases hlt2 : k₂.val ≤ y.val
      · have e1 : y.val + N - k₁.val = (y.val - k₁.val) + N := by omega
        have e2 : y.val + N - k₂.val = (y.val - k₂.val) + N := by omega
        rw [e1, e2, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e1 : y.val + N - k₁.val = (y.val - k₁.val) + N := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e2 : y.val + N - k₂.val = (y.val - k₂.val) + N := by omega
        rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    have hfilt : Finset.univ.filter (fun x => T0 x y) = Finset.univ.image f := by
      ext x
      simp only [T0, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_image]
      constructor
      · intro hx
        let k : Fin t := ⟨(y.val + N - x.val) % N, hx⟩
        refine ⟨k, ?_⟩
        apply Fin.ext
        simp only [f, k]
        have hxlt := x.isLt
        have hylt := y.isLt
        by_cases hxy : x.val ≤ y.val
        · have hsub : (y.val + N - x.val) % N = y.val - x.val := by
            have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub]
          have h2 : y.val + N - (y.val - x.val) = x.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hxlt]
        · have hsub : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
          rw [hsub]
          have h2 : y.val + N - (y.val + N - x.val) = x.val := by omega
          rw [h2, Nat.mod_eq_of_lt hxlt]
      · rintro ⟨k, rfl⟩
        have hy := y.isLt
        have hk := k.isLt
        simp only [f]
        by_cases hle : k.val ≤ y.val
        · have hmod : (y.val + N - k.val) % N = y.val - k.val := by
            have e1 : y.val + N - k.val = (y.val - k.val) + N := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have h2 : y.val + N - (y.val - k.val) = k.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          exact hk
        · have hmod : (y.val + N - k.val) % N = y.val + N - k.val := Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          have h2 : y.val + N - (y.val + N - k.val) = k.val := by omega
          rw [h2, Nat.mod_eq_of_lt (by omega)]
          exact hk
    rw [hfilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

lemma flat_four_corner {N t : ℕ} (ht0 : 0 < t) (htN : t < N)
    (C : Fin N → Fin N → ℕ)
    (hflat : ∀ T U : Fin N → Fin N → Bool,
      ((∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
       (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)) →
      ((∀ x, (Finset.univ.filter (fun y => U x y)).card = t) ∧
       (∀ y, (Finset.univ.filter (fun x => U x y)).card = t)) →
      (∑ x, ∑ y, if T x y then C x y else 0) = (∑ x, ∑ y, if U x y then C x y else 0))
    (u v x y : Fin N) :
    C u v + C x y = C u y + C x v := by
  by_cases hux : u = x
  · subst hux; ring
  by_cases hvy : v = y
  · subst hvy; ring
  have hN2 : 2 ≤ N := by omega
  let i0 : Fin N := ⟨0, by omega⟩
  let i1 : Fin N := ⟨1, by omega⟩
  let it : Fin N := ⟨t, htN⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  have h0t : i0 ≠ it := by intro h; have := congrArg Fin.val h; simp [i0, it] at this; omega
  rcases perm_map_two u x i0 i1 hux h01 with ⟨σ, hσu, hσx⟩
  rcases perm_map_two v y i0 it hvy h0t with ⟨τ, hτv, hτy⟩
  let T0 : Fin N → Fin N → Bool := fun a b => decide ((b.val + N - a.val) % N < t)
  let T : Fin N → Fin N → Bool := fun a b => T0 (σ a) (τ b)
  have hT0_reg := circulant_reg htN
  have hT_reg : (∀ a, (Finset.univ.filter (fun b => T a b)).card = t) ∧
      (∀ b, (Finset.univ.filter (fun a => T a b)).card = t) := by
    constructor
    · intro a
      have h1 : Finset.univ.filter (fun b => T a b) =
          (Finset.univ.filter (fun b => T0 (σ a) b)).image τ.symm := by
        ext b
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun h => ⟨τ b, h, τ.symm_apply_apply b⟩, fun ⟨c, hc, hcb⟩ => hcb ▸ by simpa using hc⟩
      rw [h1, Finset.card_image_of_injective _ τ.symm.injective]
      exact hT0_reg.1 (σ a)
    · intro b
      have h1 : Finset.univ.filter (fun a => T a b) =
          (Finset.univ.filter (fun a => T0 a (τ b))).image σ.symm := by
        ext a
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        exact ⟨fun h => ⟨σ a, h, σ.symm_apply_apply a⟩, fun ⟨c, hc, hca⟩ => hca ▸ by simpa using hc⟩
      rw [h1, Finset.card_image_of_injective _ σ.symm.injective]
      exact hT0_reg.2 (τ b)
  have hTuv : T u v = true := by
    simp only [T, T0, hσu, hτv, i0, decide_eq_true_eq]
    rw [zero_add, Nat.sub_zero, Nat.mod_self]; exact ht0
  have hTxy : T x y = true := by
    simp only [T, T0, hσx, hτy, i1, it, decide_eq_true_eq]
    have h1 : t + N - 1 = (t - 1) + N := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
  have hTuy : T u y = false := by
    simp only [T, T0, hσu, hτy, i0, it, decide_eq_false_iff_not, not_lt]
    rw [Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt htN]
  have hTxv : T x v = false := by
    simp only [T, T0, hσx, hτv, i1, i0, decide_eq_false_iff_not, not_lt]
    rw [zero_add, Nat.mod_eq_of_lt (by omega)]; omega
  let U : Fin N → Fin N → Bool := fun a b =>
    if (a = u ∧ b = v) ∨ (a = x ∧ b = y) then false
    else if (a = u ∧ b = y) ∨ (a = x ∧ b = v) then true
    else T a b
  have hU_reg : (∀ a, (Finset.univ.filter (fun b => U a b)).card = t) ∧
      (∀ b, (Finset.univ.filter (fun a => U a b)).card = t) := by
    constructor
    · intro a
      by_cases hau : a = u
      · rw [hau]
        have heq : Finset.univ.filter (fun b => U u b) =
            insert y ((Finset.univ.filter (fun b => T u b)).erase v) := by
          ext b
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
          by_cases hbv : b = v
          · rw [hbv]; simp [hvy]
          · by_cases hby : b = y
            · rw [hby]; simp [hux, Ne.symm hvy]
            · simp [hbv, hby]
        have hv_mem : v ∈ Finset.univ.filter (fun b => T u b) := by simp [hTuv]
        have hy_not : y ∉ (Finset.univ.filter (fun b => T u b)).erase v := by
          simp [hTuy]
        rw [heq, Finset.card_insert_of_notMem hy_not, Finset.card_erase_of_mem hv_mem, hT_reg.1 u]
        omega
      · by_cases hax : a = x
        · rw [hax]
          have heq : Finset.univ.filter (fun b => U x b) =
              insert v ((Finset.univ.filter (fun b => T x b)).erase y) := by
            ext b
            simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
            by_cases hby : b = y
            · rw [hby]; simp [Ne.symm hvy]
            · by_cases hbv : b = v
              · rw [hbv]; simp [Ne.symm hux, hvy]
              · simp [hbv, hby]
          have hy_mem : y ∈ Finset.univ.filter (fun b => T x b) := by simp [hTxy]
          have hv_not : v ∉ (Finset.univ.filter (fun b => T x b)).erase y := by
            simp [hTxv]
          rw [heq, Finset.card_insert_of_notMem hv_not, Finset.card_erase_of_mem hy_mem, hT_reg.1 x]
          omega
        · have heq : Finset.univ.filter (fun b => U a b) = Finset.univ.filter (fun b => T a b) := by
            ext b; simp [U, hau, hax]
          rw [heq, hT_reg.1 a]
    · intro b
      by_cases hbv : b = v
      · rw [hbv]
        have heq : Finset.univ.filter (fun a => U a v) =
            insert x ((Finset.univ.filter (fun a => T a v)).erase u) := by
          ext a
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
          by_cases hau : a = u
          · rw [hau]; simp [hux]
          · by_cases hax : a = x
            · rw [hax]; simp [hvy, Ne.symm hux]
            · simp [hau, hax]
        have hu_mem : u ∈ Finset.univ.filter (fun a => T a v) := by simp [hTuv]
        have hx_not : x ∉ (Finset.univ.filter (fun a => T a v)).erase u := by
          simp [hTxv]
        rw [heq, Finset.card_insert_of_notMem hx_not, Finset.card_erase_of_mem hu_mem, hT_reg.2 v]
        omega
      · by_cases hby : b = y
        · rw [hby]
          have heq : Finset.univ.filter (fun a => U a y) =
              insert u ((Finset.univ.filter (fun a => T a y)).erase x) := by
            ext a
            simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_erase]
            by_cases hax : a = x
            · rw [hax]; simp [Ne.symm hux]
            · by_cases hau : a = u
              · rw [hau]; simp [Ne.symm hvy, hux]
              · simp [hau, hax]
          have hx_mem : x ∈ Finset.univ.filter (fun a => T a y) := by simp [hTxy]
          have hu_not : u ∉ (Finset.univ.filter (fun a => T a y)).erase x := by
            simp [hTuy]
          rw [heq, Finset.card_insert_of_notMem hu_not, Finset.card_erase_of_mem hx_mem, hT_reg.2 y]
          omega
        · have heq : Finset.univ.filter (fun a => U a b) = Finset.univ.filter (fun a => T a b) := by
            ext a; simp [U, hbv, hby]
          rw [heq, hT_reg.2 b]
  have heq_cost := hflat T U hT_reg hU_reg
  have hrow_diff : ∀ a : Fin N,
      (∑ b : Fin N, if T a b then C a b else 0) + (if a = u then C u y else if a = x then C x v else 0) =
      (∑ b : Fin N, if U a b then C a b else 0) + (if a = u then C u v else if a = x then C x y else 0) := by
    intro a
    by_cases hau : a = u
    · rw [hau]
      have h1 : (∑ b : Fin N, if T u b then C u b else 0) =
          C u v + ∑ b ∈ (Finset.univ.erase v).erase y, if T u b then C u b else 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hvy, Finset.mem_univ y⟩)]
        simp [hTuv, hTuy]
      have h2 : (∑ b : Fin N, if U u b then C u b else 0) =
          C u y + ∑ b ∈ (Finset.univ.erase v).erase y, if T u b then C u b else 0 := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
          ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hvy, Finset.mem_univ y⟩)]
        have hUuv : U u v = false := by simp [U]
        have hUuy : U u y = true := by simp [U, Ne.symm hvy, hux]
        rw [hUuv, hUuy]
        simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
        congr 1
        refine Finset.sum_congr rfl (fun b hb => ?_)
        have hby : b ≠ y := (Finset.mem_erase.mp hb).1
        have hbv : b ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
        simp [U, hbv, hby, hux]
      rw [h1, h2]
      simp only [↓reduceIte]
      ring
    · by_cases hax : a = x
      · rw [hax]
        have h1 : (∑ b : Fin N, if T x b then C x b else 0) =
            C x y + ∑ b ∈ (Finset.univ.erase v).erase y, if T x b then C x b else 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hvy, Finset.mem_univ y⟩)]
          simp [hTxv, hTxy]
        have h2 : (∑ b : Fin N, if U x b then C x b else 0) =
            C x v + ∑ b ∈ (Finset.univ.erase v).erase y, if T x b then C x b else 0 := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v),
            ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hvy, Finset.mem_univ y⟩)]
          have hUxv : U x v = true := by simp [U, Ne.symm hux, hvy]
          have hUxy : U x y = false := by simp [U]
          rw [hUxv, hUxy]
          simp only [↓reduceIte, Bool.false_eq_true, zero_add]
          congr 1
          refine Finset.sum_congr rfl (fun b hb => ?_)
          have hby : b ≠ y := (Finset.mem_erase.mp hb).1
          have hbv : b ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1
          simp [U, hbv, hby, Ne.symm hux]
        rw [h1, h2]
        simp only [Ne.symm hux, ↓reduceIte]
        ring
      · have hsame : (∑ b : Fin N, if U a b then C a b else 0) = ∑ b : Fin N, if T a b then C a b else 0 :=
          Finset.sum_congr rfl (fun b _ => by simp [U, hau, hax])
        rw [hsame]
        simp [hau, hax]
  have hsum := Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hrow_diff a)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, heq_cost] at hsum
  have hL : (∑ a : Fin N, if a = u then C u y else if a = x then C x v else 0) = C u y + C x v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hux, Finset.mem_univ x⟩)]
    have h0 : ∑ a ∈ (Finset.univ.erase u).erase x, (if a = u then C u y else if a = x then C x v else 0) = 0 :=
      Finset.sum_eq_zero (fun a ha => by
        have hax : a ≠ x := (Finset.mem_erase.mp ha).1
        have hau : a ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
        simp [hau, hax])
    rw [h0]; simp [Ne.symm hux]
  have hR : (∑ a : Fin N, if a = u then C u v else if a = x then C x y else 0) = C u v + C x y := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hux, Finset.mem_univ x⟩)]
    have h0 : ∑ a ∈ (Finset.univ.erase u).erase x, (if a = u then C u v else if a = x then C x y else 0) = 0 :=
      Finset.sum_eq_zero (fun a ha => by
        have hax : a ≠ x := (Finset.mem_erase.mp ha).1
        have hau : a ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
        simp [hau, hax])
    rw [h0]; simp [Ne.symm hux]
  rw [hL, hR] at hsum
  omega

lemma cyclic_block_feasible {N t r s : ℕ} (hr0 : 0 < r) (hrN : r ≤ N) (hsN : s ≤ N) :
    let d := N / Nat.gcd N r
    ∃ R S : Fin d → Finset (Fin N),
      (∀ i, (R i).card = r ∧ (S i).card = s) ∧
      ∀ T U : Fin N → Fin N → Bool,
        ((∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
         (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)) →
        ((∀ x, (Finset.univ.filter (fun y => U x y)).card = t) ∧
         (∀ y, (Finset.univ.filter (fun x => U x y)).card = t)) →
        (∑ x, ∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0) =
        (∑ x, ∑ y, if U x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0) := by
  intro d
  have hN : 0 < N := by omega
  let g := Nat.gcd N r
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left r hN
  have hgN : g ∣ N := Nat.gcd_dvd_left N r
  have hgr : g ∣ r := Nat.gcd_dvd_right N r
  have hdg : d * g = N := Nat.div_mul_cancel hgN
  let S0 : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => y.val < s)
  have hS0_card : S0.card = s := by
    let emb : Fin s → Fin N := fun j => ⟨j.val, by omega⟩
    have heq : S0 = Finset.univ.image emb := by
      ext y
      simp only [S0, emb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun hy => ⟨⟨y.val, hy⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.isLt⟩
    have hemb_inj : Function.Injective emb := fun j₁ j₂ h =>
      Fin.ext (by simpa [emb] using congrArg Fin.val h)
    rw [heq, Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fin]
  let R : Fin d → Finset (Fin N) := fun i =>
    (Finset.univ : Finset (Fin r)).image (fun k => ⟨(i.val * g + k.val) % N, Nat.mod_lt _ hN⟩)
  let S : Fin d → Finset (Fin N) := fun _ => S0
  have hR_card : ∀ i : Fin d, (R i).card = r := by
    intro i
    have hinj : Function.Injective (fun k : Fin r => (⟨(i.val * g + k.val) % N, Nat.mod_lt _ hN⟩ : Fin N)) := by
      intro k₁ k₂ h
      have hv := congrArg Fin.val h
      simp only at hv
      have h1 := k₁.isLt
      have h2 := k₂.isLt
      have hi : i.val * g < N := by
        have hle : (i.val + 1) * g ≤ d * g := Nat.mul_le_mul_right g i.isLt
        rw [add_mul, one_mul, hdg] at hle; omega
      apply Fin.ext
      by_cases hlt1 : i.val * g + k₁.val < N <;> by_cases hlt2 : i.val * g + k₂.val < N
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hR_cov : ∀ x : Fin N, (Finset.univ.filter (fun i : Fin d => x ∈ R i)).card = r / g := by
    intro x
    let rg := r / g
    have hrg : rg * g = r := Nat.div_mul_cancel hgr
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hdg; omega)
    let f : Fin rg → Fin d := fun q =>
      ⟨((x.val / g + d - q.val) % d), Nat.mod_lt _ hd_pos⟩
    have hrg_le : rg ≤ d := by
      have : rg * g ≤ d * g := by rw [hrg, hdg]; exact hrN
      exact Nat.le_of_mul_le_mul_right this hg_pos
    have hxq_lt : x.val / g < d := Nat.div_lt_of_lt_mul (by rw [mul_comm, hdg]; exact x.isLt)
    have hf_inj : Function.Injective f := by
      intro q₁ q₂ h
      have hv := congrArg Fin.val h
      simp only [f] at hv
      have h1 : q₁.val < d := lt_of_lt_of_le q₁.isLt hrg_le
      have h2 : q₂.val < d := lt_of_lt_of_le q₂.isLt hrg_le
      apply Fin.ext
      by_cases hle1 : q₁.val ≤ x.val / g <;> by_cases hle2 : q₂.val ≤ x.val / g
      · have e1 : x.val / g + d - q₁.val = (x.val / g - q₁.val) + d := by omega
        have e2 : x.val / g + d - q₂.val = (x.val / g - q₂.val) + d := by omega
        rw [e1, e2, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e1 : x.val / g + d - q₁.val = (x.val / g - q₁.val) + d := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e2 : x.val / g + d - q₂.val = (x.val / g - q₂.val) + d := by omega
        rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have hm1 : (x.val / g + d - q₁.val) % d = x.val / g + d - q₁.val := Nat.mod_eq_of_lt (by omega)
        have hm2 : (x.val / g + d - q₂.val) % d = x.val / g + d - q₂.val := Nat.mod_eq_of_lt (by omega)
        rw [hm1, hm2] at hv
        have hle1' : q₁.val ≤ x.val / g + d := le_trans (le_of_lt h1) (Nat.le_add_left d _)
        have hle2' : q₂.val ≤ x.val / g + d := le_trans (le_of_lt h2) (Nat.le_add_left d _)
        have h1eq : (x.val / g + d - q₁.val) + q₁.val = (x.val / g + d - q₂.val) + q₂.val := by
          rw [Nat.sub_add_cancel hle1', Nat.sub_add_cancel hle2']
        rw [hv] at h1eq
        exact Nat.add_left_cancel h1eq
    have hfilt : Finset.univ.filter (fun i : Fin d => x ∈ R i) = Finset.univ.image f := by
      ext i
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨k, hk⟩
        have hv := congrArg Fin.val hk
        simp only at hv
        have hrem : k.val % g = x.val % g := by
          have h1 := congrArg (· % g) hv
          simp only [Nat.mod_mod_of_dvd _ hgN, Nat.mul_comm i.val g, Nat.mul_add_mod] at h1
          exact h1
        have hkdiv_lt : k.val / g < rg := Nat.div_lt_of_lt_mul (by rw [mul_comm, hrg]; exact k.isLt)
        refine ⟨⟨k.val / g, hkdiv_lt⟩, ?_⟩
        apply Fin.ext
        simp only [f]
        have hkm : k.val = k.val / g * g + k.val % g := by have := Nat.div_add_mod k.val g; linarith
        have hxm : x.val = x.val / g * g + x.val % g := by have := Nat.div_add_mod x.val g; linarith
        have hsum_eq : (i.val + k.val / g) % d = x.val / g := by
          have hmul : ((i.val + k.val / g) * g + x.val % g) % N = x.val := by
            have heq : (i.val + k.val / g) * g + x.val % g = i.val * g + k.val := by
              conv_rhs => rw [hkm, hrem]
              ring
            rw [heq, hv]
          have hdiv_mod : ((i.val + k.val / g) * g + x.val % g) % (d * g) =
              ((i.val + k.val / g) % d) * g + x.val % g := by
            have hmod_lt : ((i.val + k.val / g) % d) * g + x.val % g < d * g := by
              have h1 : ((i.val + k.val / g) % d + 1) * g ≤ d * g :=
                Nat.mul_le_mul_right g (Nat.mod_lt _ hd_pos)
              have h2 : x.val % g < g := Nat.mod_lt _ hg_pos
              rw [add_mul, one_mul] at h1; omega
            have hdecomp : (i.val + k.val / g) * g + x.val % g =
                (d * g) * ((i.val + k.val / g) / d) + (((i.val + k.val / g) % d) * g + x.val % g) := by
              have := Nat.div_add_mod (i.val + k.val / g) d
              nlinarith
            conv_lhs => rw [hdecomp]
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod_lt]
          have hmul' : ((i.val + k.val / g) * g + x.val % g) % (d * g) = x.val := by
            rwa [hdg]
          rw [hdiv_mod] at hmul'
          conv_rhs at hmul' => rw [hxm]
          have hcancel : ((i.val + k.val / g) % d) * g = (x.val / g) * g := by omega
          exact Nat.eq_of_mul_eq_mul_right hg_pos hcancel
        have hilt := i.isLt
        have hklt : k.val / g < d := lt_of_lt_of_le hkdiv_lt hrg_le
        by_cases hsum_lt : i.val + k.val / g < d
        · rw [Nat.mod_eq_of_lt hsum_lt] at hsum_eq
          have h1 : x.val / g + d - k.val / g = i.val + d := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hilt]
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hsum_eq
          have h1 : x.val / g + d - k.val / g = i.val := by omega
          rw [h1, Nat.mod_eq_of_lt hilt]
      · rintro ⟨q, rfl⟩
        have hqlt : q.val < d := lt_of_lt_of_le q.isLt hrg_le
        have hk_lt : q.val * g + x.val % g < r := by
          have h1 : (q.val + 1) * g ≤ rg * g := Nat.mul_le_mul_right g q.isLt
          have h2 : x.val % g < g := Nat.mod_lt _ hg_pos
          rw [add_mul, one_mul, hrg] at h1; omega
        refine ⟨⟨q.val * g + x.val % g, hk_lt⟩, ?_⟩
        apply Fin.ext
        simp only [f]
        have hxm : x.val = x.val / g * g + x.val % g := by have := Nat.div_add_mod x.val g; linarith
        by_cases hle : q.val ≤ x.val / g
        · have hmod : (x.val / g + d - q.val) % d = x.val / g - q.val := by
            have e1 : x.val / g + d - q.val = (x.val / g - q.val) + d := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have h2 : (x.val / g - q.val) * g + (q.val * g + x.val % g) = x.val := by
            have : (x.val / g - q.val) * g + q.val * g = (x.val / g) * g := by
              rw [← add_mul, Nat.sub_add_cancel hle]
            omega
          rw [h2, Nat.mod_eq_of_lt x.isLt]
        · have hmod : (x.val / g + d - q.val) % d = x.val / g + d - q.val :=
            Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          have h2 : (x.val / g + d - q.val) * g + (q.val * g + x.val % g) = x.val + N := by
            have : (x.val / g + d - q.val) * g + q.val * g = (x.val / g + d) * g := by
              rw [← add_mul, Nat.sub_add_cancel (le_trans (le_of_lt hqlt) (Nat.le_add_left d _))]
            rw [add_mul, hdg] at this
            omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
    rw [hfilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  refine ⟨R, S, fun i => ⟨hR_card i, hS0_card⟩, ?_⟩
  have hcost_const : ∀ T : Fin N → Fin N → Bool,
      ((∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
       (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)) →
      (∑ x, ∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0) =
      t * s * (r / g) := by
    intro T hT
    have hentry : ∀ x y : Fin N,
        (Finset.univ.filter (fun i : Fin d => x ∈ R i ∧ y ∈ S i)).card =
        if y ∈ S0 then r / g else 0 := by
      intro x y
      by_cases hy : y ∈ S0
      · simp only [S, hy, and_true, ↓reduceIte, hR_cov x]
      · simp only [S, hy, and_false, Finset.filter_false, Finset.card_empty, ↓reduceIte]
    simp_rw [hentry]
    rw [Finset.sum_comm]
    have hinner : ∀ y : Fin N,
        (∑ x : Fin N, if T x y then (if y ∈ S0 then r / g else 0) else 0) =
        if y ∈ S0 then t * (r / g) else 0 := by
      intro y
      by_cases hy : y ∈ S0
      · simp only [hy, ↓reduceIte]
        rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hT.2 y]
      · simp [hy]
    rw [Finset.sum_congr rfl (fun y _ => hinner y), ← Finset.sum_filter, Finset.sum_const,
      smul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter, hS0_card]
    ring
  intro T U hT hU
  rw [hcost_const T hT, hcost_const U hU]

lemma frobenius_coprime {a b M : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hM : (a - 1) * (b - 1) ≤ M) :
    ∃ x y : ℕ, M = x * a + y * b := by
  let f : Fin a → Fin a := fun y => ⟨(y.val * b) % a, Nat.mod_lt _ ha⟩
  have hf_inj : Function.Injective f := by
    intro y₁ y₂ h
    have hv := congrArg Fin.val h
    simp only [f] at hv
    have hmod : y₁.val * b ≡ y₂.val * b [MOD a] := hv
    have hcancel : y₁.val ≡ y₂.val [MOD a] :=
      Nat.ModEq.cancel_right_of_coprime hcop hmod
    apply Fin.ext
    rw [Nat.ModEq, Nat.mod_eq_of_lt y₁.isLt, Nat.mod_eq_of_lt y₂.isLt] at hcancel
    exact hcancel
  have hf_surj : Function.Surjective f := Finite.injective_iff_surjective.mp hf_inj
  rcases hf_surj ⟨M % a, Nat.mod_lt _ ha⟩ with ⟨y, hy⟩
  have hymod : (y.val * b) % a = M % a := congrArg Fin.val hy
  have hyle : y.val ≤ a - 1 := by have := y.isLt; omega
  have hyb_le : y.val * b ≤ M := by
    have hup : y.val * b ≤ (a - 1) * b := Nat.mul_le_mul_right b hyle
    have hdiff : (a - 1) * b = (a - 1) * (b - 1) + (a - 1) := by
      have : b = (b - 1) + 1 := by omega
      conv_lhs => rw [this, mul_add, mul_one]
    have hlt_Ma : y.val * b < M + a := by omega
    by_contra hgt
    have hMlt : M < y.val * b := by omega
    have hsub_pos : 0 < y.val * b - M := by omega
    have hsub_lt : y.val * b - M < a := by omega
    have hdvd : a ∣ y.val * b - M := by
      rw [Nat.dvd_iff_mod_eq_zero]
      have h1 := Nat.div_add_mod (y.val * b) a
      have h2 := Nat.div_add_mod M a
      have h3 : y.val * b - M = a * (y.val * b / a - M / a) := by
        have hq : M / a ≤ y.val * b / a := Nat.div_le_div_right (le_of_lt hMlt)
        rw [Nat.mul_sub_left_distrib]
        omega
      rw [h3, Nat.mul_mod_right]
    have := Nat.le_of_dvd hsub_pos hdvd
    omega
  have hdvd : a ∣ M - y.val * b := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have h1 := Nat.div_add_mod M a
    have h2 := Nat.div_add_mod (y.val * b) a
    have hq : y.val * b / a ≤ M / a := Nat.div_le_div_right hyb_le
    have h3 : M - y.val * b = a * (M / a - y.val * b / a) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    rw [h3, Nat.mul_mod_right]
  rcases hdvd with ⟨x, hx⟩
  refine ⟨x, y.val, ?_⟩
  calc
    M = M - y.val * b + y.val * b := (Nat.sub_add_cancel hyb_le).symm
    _ = a * x + y.val * b := by rw [hx]
    _ = x * a + y.val * b := by ring

end RectangleLibrary

theorem rectangle_classification :
  ∀ (N t r s : ℕ), 0 < t → t < N → 0 < r → r ≤ N → 0 < s → s ≤ N →
  let X := Fin N
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let dims := fun (R S : Finset X) =>
    (R.card = r ∧ S.card = s) ∨ (R.card = s ∧ S.card = r)
  let B := fun (M : ℕ) (R S : Fin M → Finset X) (x y : X) =>
    (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card
  let cost := fun (C : X → X → ℕ) (T : X → X → Bool) => ∑ x, ∑ y, if T x y then C x y else 0
  let flat := fun C => ∀ T U, reg T → reg U → cost C T = cost C U
  let feasible := fun (M : ℕ) => ∃ R S, (∀ i, dims (R i) (S i)) ∧ flat (B M R S)
  let d := N / Nat.gcd N r
  let e := N / Nat.gcd N s
  let c := Nat.gcd d e
  let generated := fun M : ℕ => ∃ a b : ℕ, M = a*d+b*e
  let threshold := c*(d/c-1)*(e/c-1)
  (∀ (M : ℕ) (R S : Fin M → Finset X), (∀ i, dims (R i) (S i)) → flat (B M R S) →
    ∀ x y : X, M*r*s+N*N*B M R S x y = N*((∑ z, B M R S x z)+(∑ z, B M R S z y))) ∧
  ∀ M : ℕ, (generated M → feasible M) ∧ (feasible M → c ∣ M) ∧
    (threshold ≤ M → (feasible M ↔ c ∣ M)) ∧
    (r ∣ N → s ∣ N → (feasible M ↔ generated M)) := by
  intro N t r s ht0 htN hr0 hrN hs0 hsN X reg dims B cost flat feasible d e c generated threshold
  have hN : 0 < N := by omega
  have hsum_total : ∀ (M : ℕ) (R S : Fin M → Finset X), (∀ i, dims (R i) (S i)) →
      (∑ u : X, ∑ v : X, B M R S u v) = M * r * s := by
    intro M R S hdims
    have hB : ∀ u v : X, B M R S u v = ∑ i : Fin M, if u ∈ R i ∧ v ∈ S i then 1 else 0 := by
      intro u v; simp [B]
    simp_rw [hB]
    have hsw : (∑ u : X, ∑ v : X, ∑ i : Fin M, if u ∈ R i ∧ v ∈ S i then 1 else 0) =
        ∑ i : Fin M, ∑ u : X, ∑ v : X, if u ∈ R i ∧ v ∈ S i then 1 else 0 := by
      calc
        (∑ u : X, ∑ v : X, ∑ i : Fin M, if u ∈ R i ∧ v ∈ S i then 1 else 0) =
            ∑ u : X, ∑ i : Fin M, ∑ v : X, if u ∈ R i ∧ v ∈ S i then 1 else 0 :=
          Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
        _ = ∑ i : Fin M, ∑ u : X, ∑ v : X, if u ∈ R i ∧ v ∈ S i then 1 else 0 := Finset.sum_comm
    rw [hsw]
    have hterm : ∀ i : Fin M,
        (∑ u : X, ∑ v : X, if u ∈ R i ∧ v ∈ S i then 1 else 0) = r * s := by
      intro i
      have h1 : ∀ u : X, (∑ v : X, if u ∈ R i ∧ v ∈ S i then 1 else 0) =
          if u ∈ R i then (S i).card else 0 := by
        intro u
        by_cases hu : u ∈ R i
        · simp [hu]
        · simp [hu]
      rw [Finset.sum_congr rfl (fun u _ => h1 u)]
      simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul]
      rcases hdims i with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]
      · rw [h1, h2, mul_comm]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_assoc]
  have hpart1 : ∀ (M : ℕ) (R S : Fin M → Finset X), (∀ i, dims (R i) (S i)) → flat (B M R S) →
      ∀ x y : X, M * r * s + N * N * B M R S x y = N * ((∑ z, B M R S x z) + (∑ z, B M R S z y)) := by
    intro M R S hdims hfl x y
    have h4 : ∀ u v : X, B M R S u v + B M R S x y = B M R S u y + B M R S x v :=
      fun u v => RectangleLibrary.flat_four_corner ht0 htN (B M R S) hfl u v x y
    have hsum := Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun v (_ : v ∈ Finset.univ) => h4 u v))
    simp only [X, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum, hsum_total M R S hdims] at hsum
    linarith
  have hfeas0 : feasible 0 := by
    refine ⟨Fin.elim0, Fin.elim0, fun i => Fin.elim0 i, ?_⟩
    intro T U _ _
    simp [cost, B]
  have hfeas_add : ∀ M₁ M₂, feasible M₁ → feasible M₂ → feasible (M₁ + M₂) := by
    rintro M₁ M₂ ⟨R₁, S₁, hd₁, hf₁⟩ ⟨R₂, S₂, hd₂, hf₂⟩
    let R : Fin (M₁ + M₂) → Finset X := Fin.addCases R₁ R₂
    let S : Fin (M₁ + M₂) → Finset X := Fin.addCases S₁ S₂
    have hdims : ∀ i, dims (R i) (S i) := by
      intro i
      refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
      · simpa [R, S] using hd₁ i₁
      · simpa [R, S] using hd₂ i₂
    have hB_add : ∀ x y : X, B (M₁ + M₂) R S x y = B M₁ R₁ S₁ x y + B M₂ R₂ S₂ x y := by
      intro x y
      simp only [B, Finset.card_filter]
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl (fun i _ => by simp [R, S])
      · refine Finset.sum_congr rfl (fun i _ => by simp [R, S])
    refine ⟨R, S, hdims, ?_⟩
    intro T U hT hU
    have hcost_add : ∀ W : X → X → Bool,
        cost (B (M₁ + M₂) R S) W = cost (B M₁ R₁ S₁) W + cost (B M₂ R₂ S₂) W := by
      intro W
      simp only [cost, hB_add]
      have hite : ∀ x y : X, (if W x y then B M₁ R₁ S₁ x y + B M₂ R₂ S₂ x y else 0) =
          (if W x y then B M₁ R₁ S₁ x y else 0) + (if W x y then B M₂ R₂ S₂ x y else 0) := by
        intro x y; split_ifs <;> simp
      simp_rw [hite, Finset.sum_add_distrib]
    rw [hcost_add T, hcost_add U, hf₁ T U hT hU, hf₂ T U hT hU]
  have hfeas_d : feasible d := by
    rcases RectangleLibrary.cyclic_block_feasible (t := t) hr0 hrN hsN with ⟨R, S, hd, hfl⟩
    exact ⟨R, S, fun i => Or.inl (hd i), hfl⟩
  have hfeas_e : feasible e := by
    rcases RectangleLibrary.cyclic_block_feasible (t := t) hs0 hsN hrN with ⟨R, S, hd, hfl⟩
    exact ⟨R, S, fun i => Or.inr (hd i), hfl⟩
  have hgen_feas : ∀ M, generated M → feasible M := by
    rintro M ⟨a, b, rfl⟩
    have hmul : ∀ (k L : ℕ), feasible L → feasible (k * L) := by
      intro k L hL
      induction k with
      | zero => simpa using hfeas0
      | succ k ih =>
        rw [Nat.succ_mul]
        exact hfeas_add (k * L) L ih hL
    exact hfeas_add (a * d) (b * e) (hmul a d hfeas_d) (hmul b e hfeas_e)
  have hfeas_dvd : ∀ M, feasible M → c ∣ M := by
    rintro M ⟨R, S, hdims, hfl⟩
    let x0 : X := ⟨0, hN⟩
    have hid := hpart1 M R S hdims hfl x0 x0
    have hdvd_row : ∀ x : X, Nat.gcd r s ∣ ∑ z : X, B M R S x z := by
      intro x
      have hsum : (∑ z : X, B M R S x z) = ∑ i : Fin M, if x ∈ R i then (S i).card else 0 := by
        have hB : ∀ z : X, B M R S x z = ∑ i : Fin M, if x ∈ R i ∧ z ∈ S i then 1 else 0 :=
          fun z => by simp [B]
        simp_rw [hB]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hx : x ∈ R i
        · simp [hx]
        · simp [hx]
      rw [hsum]
      refine Finset.dvd_sum (fun i _ => ?_)
      split_ifs
      · rcases hdims i with ⟨_, h2⟩ | ⟨_, h2⟩
        · rw [h2]; exact Nat.gcd_dvd_right r s
        · rw [h2]; exact Nat.gcd_dvd_left r s
      · exact dvd_zero _
    have hdvd_col : ∀ y : X, Nat.gcd r s ∣ ∑ z : X, B M R S z y := by
      intro y
      have hsum : (∑ z : X, B M R S z y) = ∑ i : Fin M, if y ∈ S i then (R i).card else 0 := by
        have hB : ∀ z : X, B M R S z y = ∑ i : Fin M, if z ∈ R i ∧ y ∈ S i then 1 else 0 :=
          fun z => by simp [B]
        simp_rw [hB]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hy : y ∈ S i
        · simp [hy]
        · simp [hy]
      rw [hsum]
      refine Finset.dvd_sum (fun i _ => ?_)
      split_ifs
      · rcases hdims i with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1]; exact Nat.gcd_dvd_left r s
        · rw [h1]; exact Nat.gcd_dvd_right r s
      · exact dvd_zero _
    let g1 := Nat.gcd N r
    let g2 := Nat.gcd N s
    let g := Nat.gcd g1 g2
    have hg_N : g ∣ N := (Nat.gcd_dvd_left g1 g2).trans (Nat.gcd_dvd_left N r)
    have hg_rs : g ∣ Nat.gcd r s :=
      Nat.dvd_gcd ((Nat.gcd_dvd_left g1 g2).trans (Nat.gcd_dvd_right N r))
        ((Nat.gcd_dvd_right g1 g2).trans (Nat.gcd_dvd_right N s))
    have hNg_dvd_R : N * g ∣ N * ((∑ z, B M R S x0 z) + (∑ z, B M R S z x0)) :=
      Nat.mul_dvd_mul_left N (hg_rs.trans (dvd_add (hdvd_row x0) (hdvd_col x0)))
    have hNg_dvd_B : N * g ∣ N * N * B M R S x0 x0 := by
      have h1 : N * g ∣ N * N := Nat.mul_dvd_mul_left N hg_N
      exact h1.trans (dvd_mul_right _ _)
    have hNg_dvd_Mrs : N * g ∣ M * r * s := by
      have hsub : M * r * s = N * ((∑ z, B M R S x0 z) + (∑ z, B M R S z x0)) - N * N * B M R S x0 x0 := by omega
      rw [hsub]
      exact Nat.dvd_sub hNg_dvd_R hNg_dvd_B
    have hg1_pos : 0 < g1 := Nat.gcd_pos_of_pos_left r hN
    have hg2_pos : 0 < g2 := Nat.gcd_pos_of_pos_left s hN
    have hdg1 : d * g1 = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N r)
    have heg2 : e * g2 = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N s)
    have hcg_dvd : c * (g1 * g2) ∣ N * g := by
      have h1 : N * g = Nat.gcd (N * g1) (N * g2) := (Nat.gcd_mul_left N g1 g2).symm
      rw [h1]
      refine Nat.dvd_gcd ?_ ?_
      · have heq : N * g1 = e * (g1 * g2) := by rw [← heg2]; ring
        rw [heq]; exact Nat.mul_dvd_mul_right (Nat.gcd_dvd_right d e) _
      · have heq : N * g2 = d * (g1 * g2) := by rw [← hdg1]; ring
        rw [heq]; exact Nat.mul_dvd_mul_right (Nat.gcd_dvd_left d e) _
    let r' := r / g1
    let s' := s / g2
    have hr' : r' * g1 = r := Nat.div_mul_cancel (Nat.gcd_dvd_right N r)
    have hs' : s' * g2 = s := Nat.div_mul_cancel (Nat.gcd_dvd_right N s)
    have hcop_r : Nat.Coprime c r' :=
      (Nat.coprime_div_gcd_div_gcd hg1_pos).coprime_dvd_left (Nat.gcd_dvd_left d e)
    have hcop_s : Nat.Coprime c s' :=
      (Nat.coprime_div_gcd_div_gcd hg2_pos).coprime_dvd_left (Nat.gcd_dvd_right d e)
    have hcop_rs : Nat.Coprime c (r' * s') := hcop_r.mul_right hcop_s
    have hMrs_eq : M * r * s = (M * (r' * s')) * (g1 * g2) := by
      rw [← hr', ← hs']; ring
    have hdvd_mul : c * (g1 * g2) ∣ (M * (r' * s')) * (g1 * g2) :=
      hcg_dvd.trans (hMrs_eq ▸ hNg_dvd_Mrs)
    have hdvd_c : c ∣ M * (r' * s') :=
      (Nat.mul_dvd_mul_iff_right (Nat.mul_pos hg1_pos hg2_pos)).mp hdvd_mul
    exact hcop_rs.dvd_of_dvd_mul_right hdvd_c
  have hthr_gen : ∀ M, threshold ≤ M → c ∣ M → generated M := by
    intro M hthr hdvd
    have hd_pos : 0 < d := by
      have h1 : d * Nat.gcd N r = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N r)
      exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at h1; omega)
    have he_pos : 0 < e := by
      have h1 : e * Nat.gcd N s = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N s)
      exact Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at h1; omega)
    have hc_pos : 0 < c := Nat.gcd_pos_of_pos_left e hd_pos
    have hd'c : d / c * c = d := Nat.div_mul_cancel (Nat.gcd_dvd_left d e)
    have he'c : e / c * c = e := Nat.div_mul_cancel (Nat.gcd_dvd_right d e)
    have hd'_pos : 0 < d / c := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hd'c; omega)
    have he'_pos : 0 < e / c := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at he'c; omega)
    have hcop : Nat.Coprime (d / c) (e / c) := Nat.coprime_div_gcd_div_gcd hc_pos
    rcases hdvd with ⟨M', rfl⟩
    have hM'_ge : (d / c - 1) * (e / c - 1) ≤ M' := by
      have h1 : c * ((d / c - 1) * (e / c - 1)) ≤ c * M' := by
        simpa [threshold, mul_assoc] using hthr
      exact Nat.le_of_mul_le_mul_left h1 hc_pos
    rcases RectangleLibrary.frobenius_coprime hd'_pos he'_pos hcop hM'_ge with ⟨a, b, hM'⟩
    refine ⟨a, b, ?_⟩
    rw [hM', mul_add]
    have h1 : c * (a * (d / c)) = a * d := by
      calc c * (a * (d / c)) = a * (d / c * c) := by ring
        _ = a * d := by rw [hd'c]
    have h2 : c * (b * (e / c)) = b * e := by
      calc c * (b * (e / c)) = b * (e / c * c) := by ring
        _ = b * e := by rw [he'c]
    rw [h1, h2]
  refine ⟨hpart1, fun M => ⟨hgen_feas M, hfeas_dvd M, ?_, ?_⟩⟩
  · intro hthr
    exact ⟨hfeas_dvd M, fun hdvd => hgen_feas M (hthr_gen M hthr hdvd)⟩
  · intro hr_dvd hs_dvd
    refine ⟨fun hfeas => ?_, hgen_feas M⟩
    rcases hfeas with ⟨R, S, hdims, hfl⟩
    have hd_mul : d * r = N := by
      have hg : Nat.gcd N r = r := Nat.gcd_eq_right hr_dvd
      have h1 : d * Nat.gcd N r = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N r)
      rwa [hg] at h1
    have he_mul : e * s = N := by
      have hg : Nat.gcd N s = s := Nat.gcd_eq_right hs_dvd
      have h1 : e * Nat.gcd N s = N := Nat.div_mul_cancel (Nat.gcd_dvd_left N s)
      rwa [hg] at h1
    by_cases hzero : ∃ x y : X, B M R S x y = 0
    · rcases hzero with ⟨x, y, hxy⟩
      have hid := hpart1 M R S hdims hfl x y
      rw [hxy, mul_zero, add_zero] at hid
      let P1 := (Finset.univ : Finset (Fin M)).filter (fun i => x ∈ R i ∧ (R i).card = r ∧ (S i).card = s)
      let Q1 := (Finset.univ : Finset (Fin M)).filter (fun i => x ∈ R i ∧ ¬ ((R i).card = r ∧ (S i).card = s))
      have hrow_eq : (∑ z : X, B M R S x z) = P1.card * s + Q1.card * r := by
        have hsum : (∑ z : X, B M R S x z) = ∑ i : Fin M, if x ∈ R i then (S i).card else 0 := by
          have hB : ∀ z : X, B M R S x z = ∑ i : Fin M, if x ∈ R i ∧ z ∈ S i then 1 else 0 :=
            fun z => by simp [B]
          simp_rw [hB]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hx : x ∈ R i <;> simp [hx]
        rw [hsum, ← Finset.sum_filter]
        have hpart := (Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun i : Fin M => x ∈ R i))
          (fun i => (R i).card = r ∧ (S i).card = s) (fun i => (S i).card)).symm
        rw [hpart]
        have hP1 : (Finset.univ.filter (fun i : Fin M => x ∈ R i)).filter (fun i => (R i).card = r ∧ (S i).card = s) = P1 := by
          ext i; simp [P1]
        have hQ1 : (Finset.univ.filter (fun i : Fin M => x ∈ R i)).filter (fun i => ¬ ((R i).card = r ∧ (S i).card = s)) = Q1 := by
          ext i; simp [Q1]
        rw [hP1, hQ1]
        have h1 : (∑ i ∈ P1, (S i).card) = P1.card * s := by
          rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2.2.2), Finset.sum_const, smul_eq_mul]
        have h2 : (∑ i ∈ Q1, (S i).card) = Q1.card * r := by
          have hS : ∀ i ∈ Q1, (S i).card = r := by
            intro i hi
            have hnot := (Finset.mem_filter.mp hi).2.2
            rcases hdims i with h | ⟨_, h2⟩
            · exact (hnot h).elim
            · exact h2
          rw [Finset.sum_congr rfl hS, Finset.sum_const, smul_eq_mul]
        rw [h1, h2]
      let P2 := (Finset.univ : Finset (Fin M)).filter (fun i => y ∈ S i ∧ (R i).card = r ∧ (S i).card = s)
      let Q2 := (Finset.univ : Finset (Fin M)).filter (fun i => y ∈ S i ∧ ¬ ((R i).card = r ∧ (S i).card = s))
      have hcol_eq : (∑ z : X, B M R S z y) = P2.card * r + Q2.card * s := by
        have hsum : (∑ z : X, B M R S z y) = ∑ i : Fin M, if y ∈ S i then (R i).card else 0 := by
          have hB : ∀ z : X, B M R S z y = ∑ i : Fin M, if z ∈ R i ∧ y ∈ S i then 1 else 0 :=
            fun z => by simp [B]
          simp_rw [hB]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hy : y ∈ S i <;> simp [hy]
        rw [hsum, ← Finset.sum_filter]
        have hpart := (Finset.sum_filter_add_sum_filter_not
          (Finset.univ.filter (fun i : Fin M => y ∈ S i))
          (fun i => (R i).card = r ∧ (S i).card = s) (fun i => (R i).card)).symm
        rw [hpart]
        have hP2 : (Finset.univ.filter (fun i : Fin M => y ∈ S i)).filter (fun i => (R i).card = r ∧ (S i).card = s) = P2 := by
          ext i; simp [P2]
        have hQ2 : (Finset.univ.filter (fun i : Fin M => y ∈ S i)).filter (fun i => ¬ ((R i).card = r ∧ (S i).card = s)) = Q2 := by
          ext i; simp [Q2]
        rw [hP2, hQ2]
        have h1 : (∑ i ∈ P2, (R i).card) = P2.card * r := by
          rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2.2.1), Finset.sum_const, smul_eq_mul]
        have h2 : (∑ i ∈ Q2, (R i).card) = Q2.card * s := by
          have hR : ∀ i ∈ Q2, (R i).card = s := by
            intro i hi
            have hnot := (Finset.mem_filter.mp hi).2.2
            rcases hdims i with h | ⟨h1, _⟩
            · exact (hnot h).elim
            · exact h1
          rw [Finset.sum_congr rfl hR, Finset.sum_const, smul_eq_mul]
        rw [h1, h2]
      rw [hrow_eq, hcol_eq] at hid
      refine ⟨P1.card + Q2.card, Q1.card + P2.card, ?_⟩
      have hmul_eq : M * (r * s) = ((P1.card + Q2.card) * d + (Q1.card + P2.card) * e) * (r * s) := by
        calc
          M * (r * s) = M * r * s := by ring
          _ = N * (P1.card * s + Q1.card * r + (P2.card * r + Q2.card * s)) := hid
          _ = (P1.card + Q2.card) * N * s + (Q1.card + P2.card) * N * r := by ring
          _ = (P1.card + Q2.card) * (d * r) * s + (Q1.card + P2.card) * (e * s) * r := by rw [hd_mul, he_mul]
          _ = ((P1.card + Q2.card) * d + (Q1.card + P2.card) * e) * (r * s) := by ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hr0 hs0) hmul_eq
    · push Not at hzero
      have hge1 : ∀ x y : X, 1 ≤ B M R S x y := fun x y => Nat.pos_of_ne_zero (hzero x y)
      have hN2_le : N * N ≤ M * r * s := by
        rw [← hsum_total M R S hdims]
        calc
          N * N = ∑ _u : X, ∑ _v : X, 1 := by simp [X]
          _ ≤ ∑ u : X, ∑ v : X, B M R S u v :=
              Finset.sum_le_sum (fun u _ => Finset.sum_le_sum (fun v _ => hge1 u v))
      have hde_le : d * e ≤ M := by
        have h1 : (d * e) * (r * s) ≤ M * (r * s) := by
          calc
            (d * e) * (r * s) = (d * r) * (e * s) := by ring
            _ = N * N := by rw [hd_mul, he_mul]
            _ ≤ M * r * s := hN2_le
            _ = M * (r * s) := by ring
        exact Nat.le_of_mul_le_mul_right h1 (Nat.mul_pos hr0 hs0)
      have hthr_le : threshold ≤ M := by
        have h1 : c * (d / c - 1) * (e / c - 1) ≤ c * (d / c) * (e / c) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left c (Nat.sub_le _ _)) (Nat.sub_le _ _)
        have h2 : c * (d / c) = d := Nat.mul_div_cancel' (Nat.gcd_dvd_left d e)
        have h3 : e / c ≤ e := Nat.div_le_self e c
        have h4 : c * (d / c) * (e / c) ≤ d * e := by rw [h2]; exact Nat.mul_le_mul_left d h3
        exact le_trans h1 (le_trans h4 hde_le)
      exact hthr_gen M hthr_le (hfeas_dvd M ⟨R, S, hdims, hfl⟩)

namespace Fixed33662
open RectangleLibrary
theorem divides {N M t s : ℕ} (ht0 : 0<t) (htN : t<N)
    (P : Finset (Fin N)) (proper : P.card<N) (nonempty : P.Nonempty)
    (Q : Fin M → Finset (Fin N)) (sizes : ∀ i, (Q i).card=s)
    (flat : ∀ T U : Fin N → Fin N → Bool,
      ((∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
       (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)) →
      ((∀ x, (Finset.univ.filter (fun y => U x y)).card = t) ∧
       (∀ y, (Finset.univ.filter (fun x => U x y)).card = t)) →
      (∑ x, ∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ P ∧ y ∈ Q i)).card else 0) =
      (∑ x, ∑ y, if U x y then (Finset.univ.filter (fun i => x ∈ P ∧ y ∈ Q i)).card else 0)) :
    N / Nat.gcd N s ∣ M := by
  classical
  let B := fun (x y : Fin N) => (Finset.univ.filter (fun i => x ∈ P ∧ y ∈ Q i)).card
  let k := fun (y : Fin N) => (Finset.univ.filter (fun i => y ∈ Q i)).card
  obtain ⟨u,hu⟩ := nonempty
  obtain ⟨x,_,hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show P.card < (Finset.univ : Finset (Fin N)).card by simpa using proper)
  have constant (v : Fin N) : k v = k u := by
    have h := flat_four_corner ht0 htN B flat u v x u
    simpa [B,k,hu,hx] using h
  have sumk : (∑ y, k y) = M*s := by
    have cnt (y : Fin N) : k y = ∑ i : Fin M, (if y ∈ Q i then 1 else 0 : ℕ) := by
      simp [k,Finset.sum_boole]
    simp_rw [cnt]
    rw [Finset.sum_comm]
    simp [Finset.sum_boole,sizes]
  have raw : N ∣ M*s := by
    refine ⟨k u,?_⟩
    simpa [constant] using sumk.symm
  let g := Nat.gcd N s
  have gpos : 0<g := Nat.gcd_pos_of_pos_left _ (by omega)
  have hh : (N/g)*g ∣ (M*(s/g))*g := by
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left N s),Nat.mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_right N s)]
    exact raw
  exact (Nat.coprime_div_gcd_div_gcd gpos).dvd_of_dvd_mul_right
    ((Nat.mul_dvd_mul_iff_right gpos).mp hh)
end Fixed33662

namespace ShapeLibrary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def isNotOp : GateOp → Bool
  | .not => true
  | _ => false

lemma isNotOp_eq_true_iff (op : GateOp) : isNotOp op = true ↔ op = .not := by
  cases op <;> simp [isNotOp]

def legalC (N h : ℕ) (C : Circuit) : Prop :=
  ReadsBack (N + N + h) C ∧ C.output < N + N + h + C.size ∧
  ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
    (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))

def inpVec {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) : List Bool :=
  oneEach x y ++ List.ofFn w

def tableC (N h : ℕ) (C : Circuit) (w : Fin h → Bool) (x y : Fin N) : Bool :=
  C.eval (inpVec w x y)

def areaC {N : ℕ} (H : Fin N → Fin N → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true)).card

def lineUnionC (N h : ℕ) (C : Circuit) (R S : Finset (Fin N)) : Prop :=
  ∀ (w : Fin h → Bool) (x y : Fin N), tableC N h C w x y = decide (x ∈ R ∨ y ∈ S)

lemma inpVec_length {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) :
    (inpVec w x y).length = N + N + h := by
  simp [inpVec, oneEach, Nat.add_assoc]

lemma foldl_wires_length (gs : List Gate) (init : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).length =
      init.length + gs.length := by
  induction gs generalizing init with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_prefix (gs : List Gate) (init : List Bool) (k : ℕ) (hk : k < init.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD k false =
      init.getD k false := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hk' : k < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
      simp; omega
    rw [ih _ hk', List.getD_eq_getElem _ _ hk', List.getElem_append_left hk, List.getD_eq_getElem _ _ hk]

lemma foldl_wires_getD_gate (gs : List Gate) (init : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨.or, []⟩).inputs, i < init.length + k) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD (init.length + j) false =
      (gs.getD j ⟨.or, []⟩).op.eval
        ((gs.getD j ⟨.or, []⟩).inputs.map fun i =>
          (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init).getD i false) := by
  induction gs generalizing init j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, add_zero, List.getD_cons_zero]
      have hlen : init.length < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
        simp
      rw [foldl_wires_getD_prefix gs _ init.length hlen]
      rw [List.getD_eq_getElem _ _ hlen, List.getElem_append_right le_rfl]
      simp only [Nat.sub_self, List.getElem_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hilt : i < init.length := by
        have := hback 0 (by simp) i (by simpa using hi)
        omega
      have hilt' : i < (init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]).length := by
        simp; omega
      rw [foldl_wires_getD_prefix gs _ i hilt', List.getD_eq_getElem _ _ hilt',
        List.getElem_append_left hilt, List.getD_eq_getElem _ _ hilt]
    | succ j =>
      simp only [List.foldl_cons, List.getD_cons_succ]
      let init' := init ++ [g.op.eval (g.inputs.map fun i => init.getD i false)]
      have hlen' : init'.length = init.length + 1 := by simp [init']
      have hidx : init.length + (j + 1) = init'.length + j := by omega
      rw [hidx]
      have hj' : j < gs.length := by simp at hj; omega
      have hback' : ∀ k < gs.length, ∀ i ∈ (gs.getD k ⟨.or, []⟩).inputs, i < init'.length + k := by
        intro k hk i hi
        have := hback (k + 1) (by simp; omega) i (by simpa using hi)
        omega
      exact ih init' j hj' hback'

def wireVal (C : Circuit) (inp : List Bool) (w : ℕ) : Bool :=
  (C.wires inp).getD w false

lemma wireVal_input {n : ℕ} (C : Circuit) (inp : List Bool) (hinp : inp.length = n)
    (w : ℕ) (hw : w < n) :
    wireVal C inp w = inp.getD w false := by
  unfold wireVal Circuit.wires
  exact foldl_wires_getD_prefix C.gates inp w (by omega)

lemma wireVal_gate {n : ℕ} (C : Circuit) (hread : ReadsBack n C) (inp : List Bool) (hinp : inp.length = n)
    (w : ℕ) (hw1 : n ≤ w) (hw2 : w - n < C.gates.length) :
    wireVal C inp w = (gateAt C (w - n)).op.eval ((gateAt C (w - n)).inputs.map (wireVal C inp)) := by
  have heq : w = inp.length + (w - n) := by omega
  unfold wireVal Circuit.wires
  conv_lhs => rw [heq]
  have hback : ∀ k < C.gates.length, ∀ i ∈ (C.gates.getD k ⟨.or, []⟩).inputs, i < inp.length + k := by
    intro k hk i hi; rw [hinp]; exact hread k hk i hi
  exact foldl_wires_getD_gate C.gates inp (w - n) hw2 hback

lemma inpVec_getD_row {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) (i : ℕ) (hi : i < N) :
    (inpVec w x y).getD i false = decide (⟨i, hi⟩ = x) := by
  unfold inpVec oneEach
  have hlen : i < ((List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))) ++ List.ofFn w).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : i < (List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))).length := by
    simp; omega
  rw [List.getElem_append_left h1]
  have h2 : i < (List.ofFn (fun k : Fin N => decide (k = x))).length := by simp; omega
  rw [List.getElem_append_left h2, List.getElem_ofFn]

lemma inpVec_getD_col {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) (i : ℕ) (hi1 : N ≤ i) (hi2 : i < N + N) :
    (inpVec w x y).getD i false = decide (⟨i - N, by omega⟩ = y) := by
  unfold inpVec oneEach
  have hlen : i < ((List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))) ++ List.ofFn w).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : i < (List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))).length := by
    simp; omega
  rw [List.getElem_append_left h1]
  have h2 : (List.ofFn (fun k : Fin N => decide (k = x))).length ≤ i := by simp; omega
  rw [List.getElem_append_right h2]
  simp only [List.length_ofFn, List.getElem_ofFn]

lemma inpVec_getD_seed {N h : ℕ} (w : Fin h → Bool) (x y : Fin N) (i : ℕ)
    (hi1 : N + N ≤ i) (hi2 : i < N + N + h) :
    (inpVec w x y).getD i false = w ⟨i - (N + N), by omega⟩ := by
  unfold inpVec oneEach
  have hlen : i < ((List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))) ++ List.ofFn w).length := by
    simp; omega
  rw [List.getD_eq_getElem _ _ hlen]
  have h1 : (List.ofFn (fun k : Fin N => decide (k = x)) ++ List.ofFn (fun k : Fin N => decide (k = y))).length ≤ i := by
    simp; omega
  rw [List.getElem_append_right h1]
  simp only [List.length_append, List.length_ofFn, List.getElem_ofFn]

def reachWires (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  if _ : n ≤ w ∧ w - n < C.gates.length then
    insert w (((gateAt C (w - n)).inputs.filter (· < w)).attach.foldr
      (fun u acc => reachWires n C u.1 ∪ acc) ∅)
  else {w}
termination_by w
decreasing_by
  have hu := (List.mem_filter.mp u.2).2
  exact of_decide_eq_true hu

lemma self_mem_reachWires (n : ℕ) (C : Circuit) (w : ℕ) : w ∈ reachWires n C w := by
  rw [reachWires]
  split_ifs
  · exact Finset.mem_insert_self w _
  · exact Finset.mem_singleton_self w

lemma mem_foldr_union {α : Type*} [DecidableEq α] (l : List α) (f : α → Finset ℕ) (x : ℕ) :
    x ∈ l.foldr (fun a acc => f a ∪ acc) ∅ ↔ ∃ a ∈ l, x ∈ f a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, Finset.mem_union, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hxb⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hxb⟩
    · rintro ⟨b, rfl | hb, hxb⟩
      · exact Or.inl hxb
      · exact Or.inr ⟨b, hb, hxb⟩

lemma mem_reachWires_iff {n : ℕ} {C : Circuit} (hread : ReadsBack n C) (w v : ℕ) :
    v ∈ reachWires n C w ↔
      v = w ∨ (n ≤ w ∧ w - n < C.gates.length ∧ ∃ u ∈ (gateAt C (w - n)).inputs, v ∈ reachWires n C u) := by
  rw [reachWires]
  split_ifs with hw
  · rw [Finset.mem_insert, mem_foldr_union]
    constructor
    · rintro (rfl | ⟨⟨u, hu⟩, _, hvu⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hw.1, hw.2, u, (List.mem_filter.mp hu).1, hvu⟩
    · rintro (rfl | ⟨_, _, u, hu, hvu⟩)
      · exact Or.inl rfl
      · have hult : u < w := by
          have := hread (w - n) hw.2 u hu; omega
        have huf : u ∈ (gateAt C (w - n)).inputs.filter (· < w) :=
          List.mem_filter.mpr ⟨hu, decide_eq_true hult⟩
        exact Or.inr ⟨⟨u, huf⟩, List.mem_attach _ _, hvu⟩
  · simp only [Finset.mem_singleton, iff_self_or]
    rintro ⟨h1, h2, _⟩; exact (hw ⟨h1, h2⟩).elim

lemma le_of_mem_reachWires {n : ℕ} {C : Circuit} (hread : ReadsBack n C) :
    ∀ (w v : ℕ), v ∈ reachWires n C w → v ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro v hv
    rw [mem_reachWires_iff hread] at hv
    rcases hv with rfl | ⟨hw1, hw2, u, hu, hvu⟩
    · exact le_rfl
    · have hult : u < w := by have := hread (w - n) hw2 u hu; omega
      exact le_trans (ih u hult v hvu) (le_of_lt hult)

lemma reachWires_subset_of_mem {n : ℕ} {C : Circuit} (hread : ReadsBack n C) :
    ∀ (w u : ℕ), u ∈ reachWires n C w → reachWires n C u ⊆ reachWires n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro u hu
    rw [mem_reachWires_iff hread] at hu
    rcases hu with rfl | ⟨hw1, hw2, a, ha, hua⟩
    · exact Finset.Subset.refl _
    · have halt : a < w := by have := hread (w - n) hw2 a ha; omega
      have hsub1 : reachWires n C u ⊆ reachWires n C a := ih a halt u hua
      intro v hv
      rw [mem_reachWires_iff hread]
      exact Or.inr ⟨hw1, hw2, a, ha, hsub1 hv⟩

lemma reachWires_lt_bound {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    ∀ v ∈ reachWires n C w, v < n + C.gates.length := by
  intro v hv
  exact lt_of_le_of_lt (le_of_mem_reachWires hread w v hv) hw

lemma wireVal_congr_on_reach {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (inp₁ inp₂ : List Bool) (h1 : inp₁.length = n) (h2 : inp₂.length = n) :
    ∀ (w : ℕ), w < n + C.gates.length →
      (∀ v ∈ reachWires n C w, v < n → inp₁.getD v false = inp₂.getD v false) →
      wireVal C inp₁ w = wireVal C inp₂ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hagree
    by_cases hlt : w < n
    · rw [wireVal_input C inp₁ h1 w hlt, wireVal_input C inp₂ h2 w hlt]
      exact hagree w (self_mem_reachWires n C w) hlt
    · have hw1 : n ≤ w := Nat.le_of_not_lt hlt
      have hw2 : w - n < C.gates.length := by omega
      rw [wireVal_gate C hread inp₁ h1 w hw1 hw2, wireVal_gate C hread inp₂ h2 w hw1 hw2]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hult : u < w := by have := hread (w - n) hw2 u hu; omega
      have husub : reachWires n C u ⊆ reachWires n C w :=
        reachWires_subset_of_mem hread w u
          ((mem_reachWires_iff hread w u).mpr (Or.inr ⟨hw1, hw2, u, hu, self_mem_reachWires n C u⟩))
      exact ih u hult (by omega) (fun v hv hvn => hagree v (husub hv) hvn)

lemma gateOp_and_mono (l₁ l₂ : List Bool) (h : List.Forall₂ (fun a b => a = true → b = true) l₁ l₂) :
    GateOp.eval .and l₁ = true → GateOp.eval .and l₂ = true := by
  induction h with
  | nil => intro _; rfl
  | cons hab _ ih =>
    simp only [GateOp.eval, List.all_cons, id_eq, Bool.and_eq_true]
    intro ⟨ha, hl⟩
    exact ⟨hab ha, ih hl⟩

lemma gateOp_or_mono (l₁ l₂ : List Bool) (h : List.Forall₂ (fun a b => a = true → b = true) l₁ l₂) :
    GateOp.eval .or l₁ = true → GateOp.eval .or l₂ = true := by
  induction h with
  | nil => intro h; cases h
  | cons hab _ ih =>
    simp only [GateOp.eval, List.any_cons, id_eq, Bool.or_eq_true]
    rintro (ha | hl)
    · exact Or.inl (hab ha)
    · exact Or.inr (ih hl)

lemma wireVal_mono_on_reach {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (inp₁ inp₂ : List Bool) (h1 : inp₁.length = n) (h2 : inp₂.length = n) :
    ∀ (w : ℕ), w < n + C.gates.length →
      (∀ u ∈ reachWires n C w, n ≤ u → (gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or) →
      (∀ v ∈ reachWires n C w, v < n → inp₁.getD v false = true → inp₂.getD v false = true) →
      wireVal C inp₁ w = true → wireVal C inp₂ w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmon hle hval
    by_cases hlt : w < n
    · rw [wireVal_input C inp₁ h1 w hlt] at hval
      rw [wireVal_input C inp₂ h2 w hlt]
      exact hle w (self_mem_reachWires n C w) hlt hval
    · have hw1 : n ≤ w := Nat.le_of_not_lt hlt
      have hw2 : w - n < C.gates.length := by omega
      rw [wireVal_gate C hread inp₁ h1 w hw1 hw2] at hval
      rw [wireVal_gate C hread inp₂ h2 w hw1 hw2]
      have hpair : List.Forall₂ (fun a b => a = true → b = true)
          ((gateAt C (w - n)).inputs.map (wireVal C inp₁))
          ((gateAt C (w - n)).inputs.map (wireVal C inp₂)) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
        intro u hu
        have hult : u < w := by have := hread (w - n) hw2 u hu; omega
        have husub : reachWires n C u ⊆ reachWires n C w :=
          reachWires_subset_of_mem hread w u
            ((mem_reachWires_iff hread w u).mpr (Or.inr ⟨hw1, hw2, u, hu, self_mem_reachWires n C u⟩))
        exact ih u hult (by omega) (fun z hz hzn => hmon z (husub hz) hzn)
          (fun v hv hvn => hle v (husub hv) hvn)
      rcases hmon w (self_mem_reachWires n C w) hw1 with hop | hop
      · rw [hop] at hval ⊢; exact gateOp_and_mono _ _ hpair hval
      · rw [hop] at hval ⊢; exact gateOp_or_mono _ _ hpair hval

lemma wireVal_false_of_all_false {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (inp : List Bool) (hinp : inp.length = n) :
    ∀ (w : ℕ), w < n + C.gates.length →
      (∀ u ∈ reachWires n C w, n ≤ u →
        ((gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or) ∧
        (gateAt C (u - n)).inputs ≠ []) →
      (∀ v ∈ reachWires n C w, v < n → inp.getD v false = false) →
      wireVal C inp w = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hmon hzero
    by_cases hlt : w < n
    · rw [wireVal_input C inp hinp w hlt]
      exact hzero w (self_mem_reachWires n C w) hlt
    · have hw1 : n ≤ w := Nat.le_of_not_lt hlt
      have hw2 : w - n < C.gates.length := by omega
      rw [wireVal_gate C hread inp hinp w hw1 hw2]
      have hgate := hmon w (self_mem_reachWires n C w) hw1
      have hmap : ∀ u ∈ (gateAt C (w - n)).inputs, wireVal C inp u = false := by
        intro u hu
        have hult : u < w := by have := hread (w - n) hw2 u hu; omega
        have husub : reachWires n C u ⊆ reachWires n C w :=
          reachWires_subset_of_mem hread w u
            ((mem_reachWires_iff hread w u).mpr (Or.inr ⟨hw1, hw2, u, hu, self_mem_reachWires n C u⟩))
        exact ih u hult (by omega) (fun z hz hzn => hmon z (husub hz) hzn)
          (fun v hv hvn => hzero v (husub hv) hvn)
      rcases hgate with ⟨hop | hop, hne⟩
      · rw [hop]
        cases hins : (gateAt C (w - n)).inputs with
        | nil => exact (hne hins).elim
        | cons a rest =>
          have ha : wireVal C inp a = false := hmap a (by rw [hins]; exact List.mem_cons_self)
          simp [GateOp.eval, ha]
      · rw [hop]
        simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq]
        rintro b ⟨u, hu, rfl⟩
        simp [hmap u hu]

def readsW (n : ℕ) (C : Circuit) (G : Finset ℕ) (v : ℕ) : ℕ :=
  ∑ u ∈ G, (gateAt C (u - n)).inputs.count v

lemma readsW_pos_of_mem_ne {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (v : ℕ) (hv : v ∈ reachWires n C w) (hne : v ≠ w) :
    1 ≤ readsW n C ((reachWires n C w).filter (n ≤ ·)) v := by
  have hex : ∀ (z : ℕ), v ∈ reachWires n C z → v ≠ z →
      ∃ u ∈ (reachWires n C z).filter (n ≤ ·), v ∈ (gateAt C (u - n)).inputs := by
    intro z
    induction z using Nat.strong_induction_on with
    | ind z ih =>
      intro hvz hvnz
      rw [mem_reachWires_iff hread] at hvz
      rcases hvz with rfl | ⟨hz1, hz2, a, ha, hva⟩
      · exact (hvnz rfl).elim
      · by_cases hva_eq : v = a
        · subst hva_eq
          exact ⟨z, Finset.mem_filter.mpr ⟨self_mem_reachWires n C z, hz1⟩, ha⟩
        · have halt : a < z := by have := hread (z - n) hz2 a ha; omega
          obtain ⟨u, hu, hvu⟩ := ih a halt hva hva_eq
          have hasub : reachWires n C a ⊆ reachWires n C z :=
            reachWires_subset_of_mem hread z a
              ((mem_reachWires_iff hread z a).mpr (Or.inr ⟨hz1, hz2, a, ha, self_mem_reachWires n C a⟩))
          exact ⟨u, Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩, hvu⟩
  obtain ⟨u, hu, hvu⟩ := hex w hv hne
  have h1 : 1 ≤ (gateAt C (u - n)).inputs.count v := List.count_pos_iff.mpr hvu
  have h2 : (gateAt C (u - n)).inputs.count v ≤ readsW n C ((reachWires n C w).filter (n ≤ ·)) v :=
    Finset.single_le_sum (f := fun z => (gateAt C (z - n)).inputs.count v) (fun _ _ => Nat.zero_le _) hu
  omega

lemma list_length_eq_sum_count {α : Type*} [DecidableEq α] (l : List α) (S : Finset α)
    (hsub : ∀ x ∈ l, x ∈ S) :
    l.length = ∑ x ∈ S, l.count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : a ∈ S := hsub a List.mem_cons_self
    have hl : ∀ x ∈ l, x ∈ S := fun x hx => hsub x (List.mem_cons_of_mem a hx)
    rw [List.length_cons, ih hl]
    have hsplit : ∀ x ∈ S, (a :: l).count x = l.count x + (if x = a then 1 else 0) := by
      intro x _
      rw [List.count_cons]
      by_cases hxa : x = a
      · subst hxa; simp
      · have hax : a ≠ x := Ne.symm hxa; simp [hxa, hax]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq' S a, if_pos ha]

lemma sum_inputs_eq_sum_reads {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    let V := reachWires n C w
    let G := V.filter (n ≤ ·)
    ∑ u ∈ G, (gateAt C (u - n)).inputs.length = ∑ v ∈ V.erase w, readsW n C G v := by
  intro V G
  have hlen : ∀ u ∈ G, (gateAt C (u - n)).inputs.length =
      ∑ v ∈ V.erase w, (gateAt C (u - n)).inputs.count v := by
    intro u hu
    apply list_length_eq_sum_count
    intro v hv
    have huV : u ∈ V := (Finset.mem_filter.mp hu).1
    have hun : n ≤ u := (Finset.mem_filter.mp hu).2
    have hult : u - n < C.gates.length := by
      have := le_of_mem_reachWires hread w u huV; omega
    have hvlt : v < u := by have := hread (u - n) hult v hv; omega
    have hule : u ≤ w := le_of_mem_reachWires hread w u huV
    have hvne : v ≠ w := by omega
    have hvV : v ∈ V := by
      have hsub := reachWires_subset_of_mem hread w u huV
      exact hsub ((mem_reachWires_iff hread u v).mpr (Or.inr ⟨hun, hult, v, hv, self_mem_reachWires n C v⟩))
    exact Finset.mem_erase.mpr ⟨hvne, hvV⟩
  rw [Finset.sum_congr rfl hlen, Finset.sum_comm]
  rfl

lemma accounting_ineq {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (hleg : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1)))
    (w : ℕ) (hw : w < n + C.gates.length) :
    let V := reachWires n C w
    let G := V.filter (n ≤ ·)
    let I := V.filter (· < n)
    let n0 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 0)).card
    let n1 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false)).card
    let nnot := (G.filter (fun u => isNotOp (gateAt C (u - n)).op = true)).card
    I.card + 2 * n0 + n1 + nnot ≤ G.card + 1 ∧
      (I.card + 2 * n0 + n1 + nnot = G.card + 1 →
        ∀ v ∈ V.erase w, readsW n C G v = 1) := by
  intro V G I n0 n1 nnot
  have hVpart : V.card = G.card + I.card := by
    have hdisj : Disjoint G I := by
      rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
    have hunion : G ∪ I = V := by
      ext x; simp only [G, I, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx; by_cases h : n ≤ x
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by omega⟩
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hgate_mem : ∀ u ∈ G, gateAt C (u - n) ∈ C.gates := by
    intro u hu
    have huV := (Finset.mem_filter.mp hu).1
    have hun := (Finset.mem_filter.mp hu).2
    have hult : u - n < C.gates.length := by
      have := le_of_mem_reachWires hread w u huV; omega
    unfold gateAt
    rw [List.getD_eq_getElem _ _ hult]
    exact List.getElem_mem hult
  have hslot_formula : ∑ u ∈ G, (gateAt C (u - n)).inputs.length + 2 * n0 + n1 + nnot = 2 * G.card := by
    have hpt : ∀ u ∈ G,
        (gateAt C (u - n)).inputs.length +
        (if (gateAt C (u - n)).inputs.length = 0 then 2 else 0) +
        (if (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false then 1 else 0) +
        (if isNotOp (gateAt C (u - n)).op = true then 1 else 0) = 2 := by
      intro u hu
      rcases hleg _ (hgate_mem u hu) with ⟨hlen, hop | hop | ⟨hop, h1⟩⟩
      · have : (gateAt C (u - n)).inputs.length = 0 ∨ (gateAt C (u - n)).inputs.length = 1 ∨
            (gateAt C (u - n)).inputs.length = 2 := by omega
        rcases this with h | h | h <;> simp [h, hop, isNotOp]
      · have : (gateAt C (u - n)).inputs.length = 0 ∨ (gateAt C (u - n)).inputs.length = 1 ∨
            (gateAt C (u - n)).inputs.length = 2 := by omega
        rcases this with h | h | h <;> simp [h, hop, isNotOp]
      · simp [hop, h1, isNotOp]
    have hsum := Finset.sum_congr rfl hpt
    simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Finset.sum_ite,
      Finset.sum_const_zero, add_zero] at hsum
    have h2 : (G.filter (fun u => (gateAt C (u - n)).inputs.length = 0)).card * 2 = 2 * n0 := by
      simp [n0]; ring
    have h1 : (G.filter (fun u => (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false)).card * 1 = n1 := by
      simp [n1]
    have hnot : (G.filter (fun u => isNotOp (gateAt C (u - n)).op = true)).card * 1 = nnot := by
      simp [nnot]
    have hG2 : G.card * 2 = 2 * G.card := by ring
    omega
  have hsum_eq : ∑ u ∈ G, (gateAt C (u - n)).inputs.length = ∑ v ∈ V.erase w, readsW n C G v :=
    sum_inputs_eq_sum_reads hread w hw
  have hge1 : ∀ v ∈ V.erase w, 1 ≤ readsW n C G v := by
    intro v hv
    exact readsW_pos_of_mem_ne hread w v (Finset.mem_erase.mp hv).2 (Finset.mem_erase.mp hv).1
  have hsum_ge : (V.erase w).card ≤ ∑ v ∈ V.erase w, readsW n C G v := by
    calc (V.erase w).card = ∑ _v ∈ V.erase w, 1 := by simp
      _ ≤ ∑ v ∈ V.erase w, readsW n C G v := Finset.sum_le_sum hge1
  have herase : (V.erase w).card + 1 = V.card := by
    have := Finset.card_erase_add_one (self_mem_reachWires n C w)
    exact this
  constructor
  · omega
  · intro heq v hv
    have hsum_tight : ∑ x ∈ V.erase w, readsW n C G x = ∑ _x ∈ V.erase w, 1 := by
      simp only [Finset.sum_const, smul_eq_mul, mul_one]; omega
    by_contra hne
    have hgt : 2 ≤ readsW n C G v := by have := hge1 v hv; omega
    have hstrict : ∑ _x ∈ V.erase w, 1 < ∑ x ∈ V.erase w, readsW n C G x :=
      Finset.sum_lt_sum hge1 ⟨v, hv, by omega⟩
    omega

lemma disjoint_children_of_reads_one {n : ℕ} {C : Circuit} (hread : ReadsBack n C)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hreads : ∀ v ∈ (reachWires n C w).erase w, readsW n C ((reachWires n C w).filter (n ≤ ·)) v = 1)
    (u a b : ℕ) (hu : u ∈ (reachWires n C w).filter (n ≤ ·))
    (hins : (gateAt C (u - n)).inputs = [a, b]) :
    Disjoint (reachWires n C a) (reachWires n C b) := by
  let V := reachWires n C w
  let G := V.filter (n ≤ ·)
  have huV : u ∈ V := (Finset.mem_filter.mp hu).1
  have hun : n ≤ u := (Finset.mem_filter.mp hu).2
  have hult : u - n < C.gates.length := by
    have := le_of_mem_reachWires hread w u huV; omega
  have ha_in : a ∈ (gateAt C (u - n)).inputs := by rw [hins]; exact List.mem_cons_self
  have hb_in : b ∈ (gateAt C (u - n)).inputs := by rw [hins]; exact List.mem_cons_of_mem a List.mem_cons_self
  have halt : a < u := by have := hread (u - n) hult a ha_in; omega
  have hblt : b < u := by have := hread (u - n) hult b hb_in; omega
  have hule : u ≤ w := le_of_mem_reachWires hread w u huV
  have hasub : reachWires n C a ⊆ V :=
    reachWires_subset_of_mem hread w a
      (reachWires_subset_of_mem hread w u huV
        ((mem_reachWires_iff hread u a).mpr (Or.inr ⟨hun, hult, a, ha_in, self_mem_reachWires n C a⟩)))
  have hbsub : reachWires n C b ⊆ V :=
    reachWires_subset_of_mem hread w b
      (reachWires_subset_of_mem hread w u huV
        ((mem_reachWires_iff hread u b).mpr (Or.inr ⟨hun, hult, b, hb_in, self_mem_reachWires n C b⟩)))
  have hab : a ≠ b := by
    intro heq; subst heq
    have ha_er : a ∈ V.erase w := Finset.mem_erase.mpr ⟨by omega, hasub (self_mem_reachWires n C a)⟩
    have h1 : readsW n C G a = 1 := hreads a ha_er
    have h2 : (gateAt C (u - n)).inputs.count a ≤ readsW n C G a :=
      Finset.single_le_sum (f := fun z => (gateAt C (z - n)).inputs.count a) (fun _ _ => Nat.zero_le _) hu
    rw [hins] at h2
    simp at h2; omega
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hne
  have hne' : (reachWires n C a ∩ reachWires n C b).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨m, hm_mem, hm_max⟩ : ∃ m ∈ reachWires n C a ∩ reachWires n C b,
      ∀ z ∈ reachWires n C a ∩ reachWires n C b, z ≤ m :=
    ⟨(reachWires n C a ∩ reachWires n C b).max' hne', Finset.max'_mem _ hne',
      fun z hz => Finset.le_max' _ z hz⟩
  have hma : m ∈ reachWires n C a := (Finset.mem_inter.mp hm_mem).1
  have hmb : m ∈ reachWires n C b := (Finset.mem_inter.mp hm_mem).2
  have hm_er : m ∈ V.erase w := by
    have hmle : m ≤ a := le_of_mem_reachWires hread a m hma
    exact Finset.mem_erase.mpr ⟨by omega, hasub hma⟩
  have hrm : readsW n C G m = 1 := hreads m hm_er
  have hfind : ∀ (r : ℕ), m ∈ reachWires n C r → m ≠ r →
      ∃ p ∈ (reachWires n C r).filter (n ≤ ·), m ∈ (gateAt C (p - n)).inputs := by
    intro r hmr hmne
    have hpos := readsW_pos_of_mem_ne hread r m hmr hmne
    by_contra hnone; push Not at hnone
    have hz : readsW n C ((reachWires n C r).filter (n ≤ ·)) m = 0 := by
      unfold readsW
      apply Finset.sum_eq_zero; intro p hp
      exact List.count_eq_zero.mpr (hnone p hp)
    omega
  by_cases hma_eq : m = a
  · subst hma_eq
    have hmb_ne : m ≠ b := hab
    obtain ⟨p, hp, hmp⟩ := hfind b hmb hmb_ne
    have hpG : p ∈ G := Finset.mem_filter.mpr ⟨hbsub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
    have hpu : p ≠ u := by
      have := le_of_mem_reachWires hread b p (Finset.mem_filter.mp hp).1; omega
    have h2 : (gateAt C (u - n)).inputs.count m + (gateAt C (p - n)).inputs.count m ≤ readsW n C G m := by
      have hpair : {u, p} ⊆ G := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      have hle := Finset.sum_le_sum_of_subset (f := fun z => (gateAt C (z - n)).inputs.count m) hpair
      rw [Finset.sum_pair hpu.symm] at hle
      exact hle
    have hc1 : 1 ≤ (gateAt C (u - n)).inputs.count m := List.count_pos_iff.mpr ha_in
    have hc2 : 1 ≤ (gateAt C (p - n)).inputs.count m := List.count_pos_iff.mpr hmp
    omega
  · by_cases hmb_eq : m = b
    · subst hmb_eq
      obtain ⟨p, hp, hmp⟩ := hfind a hma hma_eq
      have hpG : p ∈ G := Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2⟩
      have hpu : p ≠ u := by
        have := le_of_mem_reachWires hread a p (Finset.mem_filter.mp hp).1; omega
      have h2 : (gateAt C (u - n)).inputs.count m + (gateAt C (p - n)).inputs.count m ≤ readsW n C G m := by
        have hpair : {u, p} ⊆ G := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
        have hle := Finset.sum_le_sum_of_subset (f := fun z => (gateAt C (z - n)).inputs.count m) hpair
        rw [Finset.sum_pair hpu.symm] at hle
        exact hle
      have hc1 : 1 ≤ (gateAt C (u - n)).inputs.count m := List.count_pos_iff.mpr hb_in
      have hc2 : 1 ≤ (gateAt C (p - n)).inputs.count m := List.count_pos_iff.mpr hmp
      omega
    · obtain ⟨p1, hp1, hmp1⟩ := hfind a hma hma_eq
      obtain ⟨p2, hp2, hmp2⟩ := hfind b hmb hmb_eq
      by_cases hp12 : p1 = p2
      · subst hp12
        have hp_inter : p1 ∈ reachWires n C a ∩ reachWires n C b :=
          Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hp1).1, (Finset.mem_filter.mp hp2).1⟩
        have hle_max : p1 ≤ m := hm_max p1 hp_inter
        have hp1n : n ≤ p1 := (Finset.mem_filter.mp hp1).2
        have hp1lt : p1 - n < C.gates.length := by
          have := le_of_mem_reachWires hread a p1 (Finset.mem_filter.mp hp1).1; omega
        have hmlt : m < p1 := by have := hread (p1 - n) hp1lt m hmp1; omega
        omega
      · have hp1G : p1 ∈ G := Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hp1).1, (Finset.mem_filter.mp hp1).2⟩
        have hp2G : p2 ∈ G := Finset.mem_filter.mpr ⟨hbsub (Finset.mem_filter.mp hp2).1, (Finset.mem_filter.mp hp2).2⟩
        have h2 : (gateAt C (p1 - n)).inputs.count m + (gateAt C (p2 - n)).inputs.count m ≤ readsW n C G m := by
          have hpair : {p1, p2} ⊆ G := by intro z hz; simp at hz; rcases hz with rfl | rfl <;> assumption
          have hle := Finset.sum_le_sum_of_subset (f := fun z => (gateAt C (z - n)).inputs.count m) hpair
          rw [Finset.sum_pair hp12] at hle
          exact hle
        have hc1 : 1 ≤ (gateAt C (p1 - n)).inputs.count m := List.count_pos_iff.mpr hmp1
        have hc2 : 1 ≤ (gateAt C (p2 - n)).inputs.count m := List.count_pos_iff.mpr hmp2
        omega

lemma area_le_of_subset {N : ℕ} (H₁ H₂ : Fin N → Fin N → Bool)
    (h : ∀ x y, H₁ x y = true → H₂ x y = true) :
    areaC H₁ ≤ areaC H₂ := by
  apply Finset.card_le_card
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  exact ⟨Finset.mem_univ z, h z.1 z.2 hz.2⟩

lemma area_or_le {N : ℕ} (H₁ H₂ : Fin N → Fin N → Bool) :
    areaC (fun x y => H₁ x y || H₂ x y) ≤ areaC H₁ + areaC H₂ := by
  have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (H₁ z.1 z.2 || H₂ z.1 z.2) = true) ⊆
      (Finset.univ.filter (fun z => H₁ z.1 z.2 = true)) ∪ (Finset.univ.filter (fun z => H₂ z.1 z.2 = true)) := by
    intro z hz
    rw [Finset.mem_filter, Bool.or_eq_true] at hz
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hz.2 with h1 | h2
    · exact Or.inl ⟨Finset.mem_univ z, h1⟩
    · exact Or.inr ⟨Finset.mem_univ z, h2⟩
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

lemma area_ge_of_unnamed_true {N : ℕ} (H : Fin N → Fin N → Bool) (R S : Finset (Fin N))
    (h : ∀ x y, x ∉ R → y ∉ S → H x y = true) :
    (N - R.card) * (N - S.card) ≤ areaC H := by
  have hsub : Rᶜ ×ˢ Sᶜ ⊆ (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true) := by
    intro z hz
    rcases Finset.mem_product.mp hz with ⟨hx, hy⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ z, h z.1 z.2 (Finset.mem_compl.mp hx) (Finset.mem_compl.mp hy)⟩
  have hcard : (Rᶜ ×ˢ Sᶜ).card = (N - R.card) * (N - S.card) := by
    rw [Finset.card_product, Finset.card_compl, Finset.card_compl, Fintype.card_fin]
  rw [← hcard]
  exact Finset.card_le_card hsub

lemma area_le_of_lines {N : ℕ} (H : Fin N → Fin N → Bool) (R S : Finset (Fin N))
    (h : ∀ x y, H x y = true → x ∈ R ∨ y ∈ S) :
    areaC H ≤ (R.card + S.card) * N := by
  have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => H z.1 z.2 = true) ⊆
      (R ×ˢ (Finset.univ : Finset (Fin N))) ∪ ((Finset.univ : Finset (Fin N)) ×ˢ S) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [Finset.mem_union, Finset.mem_product, Finset.mem_product]
    rcases h z.1 z.2 hz.2 with hr | hs
    · exact Or.inl ⟨hr, Finset.mem_univ z.2⟩
    · exact Or.inr ⟨Finset.mem_univ z.1, hs⟩
  have hle := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin] at hle
  have hrw : R.card * N + N * S.card = (R.card + S.card) * N := by ring
  rw [hrw] at hle; exact hle

lemma mul_compl_ge {N r s : ℕ} (hrs : r + s ≤ N) :
    N * (N - (r + s)) ≤ (N - r) * (N - s) := by
  let a := N - (r + s)
  have hN : N = a + r + s := by omega
  have hr : N - r = a + s := by omega
  have hs : N - s = a + r := by omega
  rw [hr, hs]
  have heq : (a + s) * (a + r) = (a + r + s) * a + r * s := by ring
  rw [heq, ← hN]
  exact Nat.le_add_right _ _

inductive BTree (N h : ℕ) where
  | row (x : Fin N)
  | col (y : Fin N)
  | seed (j : Fin h)
  | not (t : BTree N h)
  | and (t₁ t₂ : BTree N h)
  | or (t₁ t₂ : BTree N h)

def BTree.evalRaw {N h : ℕ} : BTree N h → (Fin N → Bool) → (Fin N → Bool) → (Fin h → Bool) → Bool
  | .row x, rx, _, _ => rx x
  | .col y, _, cy, _ => cy y
  | .seed j, _, _, w => w j
  | .not t, rx, cy, w => !(t.evalRaw rx cy w)
  | .and t₁ t₂, rx, cy, w => t₁.evalRaw rx cy w && t₂.evalRaw rx cy w
  | .or t₁ t₂, rx, cy, w => t₁.evalRaw rx cy w || t₂.evalRaw rx cy w

def BTree.eval {N h : ℕ} (t : BTree N h) (w : Fin h → Bool) (x y : Fin N) : Bool :=
  t.evalRaw (fun i => decide (i = x)) (fun j => decide (j = y)) w

def BTree.rows {N h : ℕ} : BTree N h → Finset (Fin N)
  | .row x => {x}
  | .col _ => ∅
  | .seed _ => ∅
  | .not t => t.rows
  | .and t₁ t₂ => t₁.rows ∪ t₂.rows
  | .or t₁ t₂ => t₁.rows ∪ t₂.rows

def BTree.cols {N h : ℕ} : BTree N h → Finset (Fin N)
  | .row _ => ∅
  | .col y => {y}
  | .seed _ => ∅
  | .not t => t.cols
  | .and t₁ t₂ => t₁.cols ∪ t₂.cols
  | .or t₁ t₂ => t₁.cols ∪ t₂.cols

def BTree.seeds {N h : ℕ} : BTree N h → Finset (Fin h)
  | .row _ => ∅
  | .col _ => ∅
  | .seed j => {j}
  | .not t => t.seeds
  | .and t₁ t₂ => t₁.seeds ∪ t₂.seeds
  | .or t₁ t₂ => t₁.seeds ∪ t₂.seeds

def BTree.notCount {N h : ℕ} : BTree N h → ℕ
  | .row _ => 0
  | .col _ => 0
  | .seed _ => 0
  | .not t => t.notCount + 1
  | .and t₁ t₂ => t₁.notCount + t₂.notCount
  | .or t₁ t₂ => t₁.notCount + t₂.notCount

def BTree.andCount {N h : ℕ} : BTree N h → ℕ
  | .row _ => 0
  | .col _ => 0
  | .seed _ => 0
  | .not t => t.andCount
  | .and t₁ t₂ => t₁.andCount + t₂.andCount + 1
  | .or t₁ t₂ => t₁.andCount + t₂.andCount

def BTree.lineCount {N h : ℕ} (t : BTree N h) : ℕ :=
  t.rows.card + t.cols.card

def BTree.ReadOnce {N h : ℕ} : BTree N h → Prop
  | .row _ => True
  | .col _ => True
  | .seed _ => True
  | .not t => t.ReadOnce
  | .and t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧
      Disjoint t₁.rows t₂.rows ∧ Disjoint t₁.cols t₂.cols ∧ Disjoint t₁.seeds t₂.seeds
  | .or t₁ t₂ => t₁.ReadOnce ∧ t₂.ReadOnce ∧
      Disjoint t₁.rows t₂.rows ∧ Disjoint t₁.cols t₂.cols ∧ Disjoint t₁.seeds t₂.seeds

lemma BTree.nonempty_leaves {N h : ℕ} (t : BTree N h) :
    t.rows.Nonempty ∨ t.cols.Nonempty ∨ t.seeds.Nonempty := by
  induction t with
  | row x => exact Or.inl ⟨x, Finset.mem_singleton_self x⟩
  | col y => exact Or.inr (Or.inl ⟨y, Finset.mem_singleton_self y⟩)
  | seed j => exact Or.inr (Or.inr ⟨j, Finset.mem_singleton_self j⟩)
  | not t ih => exact ih
  | and t₁ _ ih₁ _ =>
    rcases ih₁ with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨x, Finset.mem_union_left _ hx⟩
    · exact Or.inr (Or.inl ⟨y, Finset.mem_union_left _ hy⟩)
    · exact Or.inr (Or.inr ⟨j, Finset.mem_union_left _ hj⟩)
  | or t₁ _ ih₁ _ =>
    rcases ih₁ with ⟨x, hx⟩ | ⟨y, hy⟩ | ⟨j, hj⟩
    · exact Or.inl ⟨x, Finset.mem_union_left _ hx⟩
    · exact Or.inr (Or.inl ⟨y, Finset.mem_union_left _ hy⟩)
    · exact Or.inr (Or.inr ⟨j, Finset.mem_union_left _ hj⟩)

lemma BTree.evalRaw_congr {N h : ℕ} (t : BTree N h)
    (rx₁ rx₂ cy₁ cy₂ : Fin N → Bool) (w₁ w₂ : Fin h → Bool)
    (hr : ∀ x ∈ t.rows, rx₁ x = rx₂ x)
    (hc : ∀ y ∈ t.cols, cy₁ y = cy₂ y)
    (hs : ∀ j ∈ t.seeds, w₁ j = w₂ j) :
    t.evalRaw rx₁ cy₁ w₁ = t.evalRaw rx₂ cy₂ w₂ := by
  induction t with
  | row x => exact hr x (Finset.mem_singleton_self x)
  | col y => exact hc y (Finset.mem_singleton_self y)
  | seed j => exact hs j (Finset.mem_singleton_self j)
  | not t ih =>
    simp only [BTree.evalRaw, ih hr hc hs]
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.evalRaw]
    rw [ih₁ (fun x hx => hr x (Finset.mem_union_left _ hx))
            (fun y hy => hc y (Finset.mem_union_left _ hy))
            (fun j hj => hs j (Finset.mem_union_left _ hj)),
        ih₂ (fun x hx => hr x (Finset.mem_union_right _ hx))
            (fun y hy => hc y (Finset.mem_union_right _ hy))
            (fun j hj => hs j (Finset.mem_union_right _ hj))]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.evalRaw]
    rw [ih₁ (fun x hx => hr x (Finset.mem_union_left _ hx))
            (fun y hy => hc y (Finset.mem_union_left _ hy))
            (fun j hj => hs j (Finset.mem_union_left _ hj)),
        ih₂ (fun x hx => hr x (Finset.mem_union_right _ hx))
            (fun y hy => hc y (Finset.mem_union_right _ hy))
            (fun j hj => hs j (Finset.mem_union_right _ hj))]

lemma BTree.evalRaw_mono {N h : ℕ} (t : BTree N h) (hnot : t.notCount = 0)
    (rx₁ rx₂ cy₁ cy₂ : Fin N → Bool) (w₁ w₂ : Fin h → Bool)
    (hr : ∀ x, rx₁ x = true → rx₂ x = true)
    (hc : ∀ y, cy₁ y = true → cy₂ y = true)
    (hs : ∀ j, w₁ j = true → w₂ j = true) :
    t.evalRaw rx₁ cy₁ w₁ = true → t.evalRaw rx₂ cy₂ w₂ = true := by
  induction t with
  | row x => exact hr x
  | col y => exact hc y
  | seed j => exact hs j
  | not _ _ => simp [BTree.notCount] at hnot
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw, Bool.and_eq_true]
    intro ⟨h1, h2⟩
    exact ⟨ih₁ (by omega) h1, ih₂ (by omega) h2⟩
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw, Bool.or_eq_true]
    rintro (h1 | h2)
    · exact Or.inl (ih₁ (by omega) h1)
    · exact Or.inr (ih₂ (by omega) h2)

lemma BTree.evalRaw_zero_false {N h : ℕ} (t : BTree N h) (hnot : t.notCount = 0)
    (w : Fin h → Bool) (hw : ∀ j ∈ t.seeds, w j = false) :
    t.evalRaw (fun _ => false) (fun _ => false) w = false := by
  induction t with
  | row _ => rfl
  | col _ => rfl
  | seed j => exact hw j (Finset.mem_singleton_self j)
  | not _ _ => simp [BTree.notCount] at hnot
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw,
      ih₁ (by omega) (fun j hj => hw j (Finset.mem_union_left _ hj)),
      ih₂ (by omega) (fun j hj => hw j (Finset.mem_union_right _ hj)), Bool.and_self]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.evalRaw,
      ih₁ (by omega) (fun j hj => hw j (Finset.mem_union_left _ hj)),
      ih₂ (by omega) (fun j hj => hw j (Finset.mem_union_right _ hj)), Bool.or_self]

lemma BTree.eval_eq_seed_of_only_seed {N h : ℕ} (t : BTree N h)
    (hnot : t.notCount = 0) (hr : t.rows = ∅) (hc : t.cols = ∅)
    (j : Fin h) (hs : ∀ k ∈ t.seeds, k = j) :
    ∀ (w : Fin h → Bool) (x y : Fin N), t.eval w x y = w j := by
  intro w x y
  induction t with
  | row x' => simp [BTree.rows] at hr
  | col y' => simp [BTree.cols] at hc
  | seed k =>
    have hk : k = j := hs k (Finset.mem_singleton_self k)
    subst hk; rfl
  | not _ _ => simp [BTree.notCount] at hnot
  | and t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.rows, Finset.union_eq_empty] at hr
    simp only [BTree.cols, Finset.union_eq_empty] at hc
    simp only [BTree.eval, BTree.evalRaw]
    have h1 := ih₁ (by omega) hr.1 hc.1 (fun k hk => hs k (Finset.mem_union_left _ hk))
    have h2 := ih₂ (by omega) hr.2 hc.2 (fun k hk => hs k (Finset.mem_union_right _ hk))
    simp only [BTree.eval] at h1 h2
    rw [h1, h2, Bool.and_self]
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.rows, Finset.union_eq_empty] at hr
    simp only [BTree.cols, Finset.union_eq_empty] at hc
    simp only [BTree.eval, BTree.evalRaw]
    have h1 := ih₁ (by omega) hr.1 hc.1 (fun k hk => hs k (Finset.mem_union_left _ hk))
    have h2 := ih₂ (by omega) hr.2 hc.2 (fun k hk => hs k (Finset.mem_union_right _ hk))
    simp only [BTree.eval] at h1 h2
    rw [h1, h2, Bool.or_self]

lemma BTree.eval_of_no_not_no_and {N h : ℕ} (t : BTree N h)
    (hnot : t.notCount = 0) (hand : t.andCount = 0) (hseed : t.seeds = ∅) :
    ∀ (w : Fin h → Bool) (x y : Fin N), t.eval w x y = decide (x ∈ t.rows ∨ y ∈ t.cols) := by
  intro w x y
  induction t with
  | row x' => simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | col y' => simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | seed j => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and _ _ _ _ => simp [BTree.andCount] at hand
  | or t₁ t₂ ih₁ ih₂ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.andCount] at hand
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    have h1 := ih₁ (by omega) (by omega) hseed.1
    have h2 := ih₂ (by omega) (by omega) hseed.2
    simp only [BTree.eval, BTree.evalRaw] at h1 h2 ⊢
    rw [h1, h2]
    simp only [BTree.rows, BTree.cols, Finset.mem_union]
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto

lemma BTree.tree_not_one_decr {N h : ℕ} (t : BTree N h) (w : Fin h → Bool)
    (hro : t.ReadOnce) (hseed : t.seeds = ∅) (hnot : t.notCount = 1) :
    (∃ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w = true →
      t.evalRaw (fun _ => false) (fun _ => false) w = true) ∨
    (∃ y ∈ t.cols, t.evalRaw (fun _ => false) (fun j => decide (j = y)) w = true →
      t.evalRaw (fun _ => false) (fun _ => false) w = true) := by
  induction t with
  | row _ => simp [BTree.notCount] at hnot
  | col _ => simp [BTree.notCount] at hnot
  | seed _ => simp [BTree.notCount] at hnot
  | not u _ =>
    simp only [BTree.notCount] at hnot
    have hu0 : u.notCount = 0 := by omega
    have hne : u.rows.Nonempty ∨ u.cols.Nonempty := by
      rcases u.nonempty_leaves with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [show u.seeds = ∅ from hseed] at h3; exact (Finset.not_nonempty_empty h3).elim
    rcases hne with ⟨x, hx⟩ | ⟨y, hy⟩
    · left; refine ⟨x, hx, fun h => ?_⟩
      simp only [BTree.evalRaw, Bool.not_eq_true'] at h ⊢
      by_contra hne0
      have huT : u.evalRaw (fun _ => false) (fun _ => false) w = true := by
        cases hval : u.evalRaw (fun _ => false) (fun _ => false) w
        · exact (hne0 hval).elim
        · rfl
      have hmon := u.evalRaw_mono hu0 (fun _ => false) (fun i => decide (i = x))
        (fun _ => false) (fun _ => false) w w (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => h) huT
      rw [hmon] at h; cases h
    · right; refine ⟨y, hy, fun h => ?_⟩
      simp only [BTree.evalRaw, Bool.not_eq_true'] at h ⊢
      by_contra hne0
      have huT : u.evalRaw (fun _ => false) (fun _ => false) w = true := by
        cases hval : u.evalRaw (fun _ => false) (fun _ => false) w
        · exact (hne0 hval).elim
        · rfl
      have hmon := u.evalRaw_mono hu0 (fun _ => false) (fun _ => false)
        (fun _ => false) (fun j => decide (j = y)) w w (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => h) huT
      rw [hmon] at h; cases h
  | and u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    by_cases hu1 : u.notCount = 1
    · rcases ihu hrou hseed.1 hu1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_left _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
        have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnv (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        exact ⟨hdec h.1, hv_eq ▸ h.2⟩
      · right; refine ⟨y, Finset.mem_union_left _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
        have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynv (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        exact ⟨hdec h.1, hv_eq ▸ h.2⟩
    · have hv1 : v.notCount = 1 := by omega
      rcases ihv hrov hseed.2 hv1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_right _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
        have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnu (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        exact ⟨hu_eq ▸ h.1, hdec h.2⟩
      · right; refine ⟨y, Finset.mem_union_right _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.and_eq_true] at h ⊢
        have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
        have hu_eq : u.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynu (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        exact ⟨hu_eq ▸ h.1, hdec h.2⟩
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    by_cases hu1 : u.notCount = 1
    · rcases ihu hrou hseed.1 hu1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_left _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
        have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnv (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hdec h1)
        · exact Or.inr (hv_eq ▸ h2)
      · right; refine ⟨y, Finset.mem_union_left _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
        have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            v.evalRaw (fun _ => false) (fun _ => false) w :=
          v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynv (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hdec h1)
        · exact Or.inr (hv_eq ▸ h2)
    · have hv1 : v.notCount = 1 := by omega
      rcases ihv hrov hseed.2 hv1 with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · left; refine ⟨x, Finset.mem_union_right _ hx, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
        have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnu (heq ▸ hi)
            simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hu_eq ▸ h1)
        · exact Or.inr (hdec h2)
      · right; refine ⟨y, Finset.mem_union_right _ hy, fun h => ?_⟩
        simp only [BTree.evalRaw, Bool.or_eq_true] at h ⊢
        have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
        have hu_eq : u.evalRaw (fun _ => false) (fun j => decide (j = y)) w =
            u.evalRaw (fun _ => false) (fun _ => false) w :=
          u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
            have : j ≠ y := fun heq => hynu (heq ▸ hj)
            simp [this]) (fun _ _ => rfl)
        rcases h with h1 | h2
        · exact Or.inl (hu_eq ▸ h1)
        · exact Or.inr (hdec h2)

lemma BTree.tree_seedless_tight {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅)
    (hrow : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true)
    (hcol : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true) :
    ∀ (w : Fin h → Bool) (x y : Fin N), t.eval w x y = decide (x ∈ t.rows ∨ y ∈ t.cols) := by
  induction t with
  | row x' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | col y' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, Finset.notMem_empty, Finset.mem_singleton, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | seed _ => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    exfalso
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨_, _, hdisjR, hdisjC, _⟩
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun j hj => by rw [hseed.2] at hj; exact (Finset.notMem_empty j hj).elim)
    have hune : u.rows.Nonempty ∨ u.cols.Nonempty := by
      rcases u.nonempty_leaves with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [hseed.1] at h3; exact (Finset.not_nonempty_empty h3).elim
    rcases hune with ⟨x, hx⟩ | ⟨y, hy⟩
    · have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ =
          v.evalRaw (fun _ => false) (fun _ => false) w₀ :=
        v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)
      rw [hv_eq, hv0] at h1; cases h1.2
    · have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ =
          v.evalRaw (fun _ => false) (fun _ => false) w₀ :=
        v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
          have : j ≠ y := fun heq => hynv (heq ▸ hj); simp [this]) (fun _ _ => rfl)
      rw [hv_eq, hv0] at h1; cases h1.2
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      u.evalRaw_zero_false (by omega) w₀ (fun j hj => by rw [hseed.1] at hj; exact (Finset.notMem_empty j hj).elim)
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun j hj => by rw [hseed.2] at hj; exact (Finset.notMem_empty j hj).elim)
    have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
          have : j ≠ y := fun heq => hynv (heq ▸ hj); simp [this]) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun j hj => by
          have : j ≠ y := fun heq => hynu (heq ▸ hj); simp [this]) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have h1 := ihu hrou (by omega) hseed.1 hru hcu
    have h2 := ihv hrov (by omega) hseed.2 hrv hcv
    intro w x y
    simp only [BTree.eval, BTree.evalRaw] at h1 h2 ⊢
    rw [h1 w x y, h2 w x y]
    simp only [BTree.rows, BTree.cols, Finset.mem_union]
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]; tauto

lemma BTree.tree_seed_false {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool) (j₀ : Fin h)
    (hro : t.ReadOnce) (hnot : t.notCount = 0)
    (hseed : ∀ k ∈ t.seeds, k = j₀) (hw₀ : w₀ j₀ = false)
    (hrow : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true)
    (hcol : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true) :
    ∀ (w : Fin h → Bool) (x y : Fin N),
      t.eval w x y = decide ((j₀ ∈ t.seeds ∧ w j₀ = true) ∨ x ∈ t.rows ∨ y ∈ t.cols) := by
  induction t with
  | row x' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, BTree.seeds,
      Finset.notMem_empty, Finset.mem_singleton, false_and, false_or, or_false]; exact decide_eq_decide.mpr eq_comm
  | col y' => intro w x y; simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, BTree.seeds,
      Finset.notMem_empty, Finset.mem_singleton, false_and, false_or]; exact decide_eq_decide.mpr eq_comm
  | seed k =>
    have hk : k = j₀ := hseed k (Finset.mem_singleton_self k)
    subst hk
    intro w x y; simp [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, BTree.seeds]
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    exfalso
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨_, _, hdisjR, hdisjC, hdisjS⟩
    have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      u.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_left _ hk)]; exact hw₀)
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_right _ hk)]; exact hw₀)
    have hex : (u.rows.Nonempty ∨ u.cols.Nonempty) ∨ (v.rows.Nonempty ∨ v.cols.Nonempty) := by
      rcases u.nonempty_leaves with h1 | h2 | ⟨k1, hk1⟩
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h2)
      · rcases v.nonempty_leaves with h1 | h2 | ⟨k2, hk2⟩
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h2)
        · have heq1 : k1 = j₀ := hseed k1 (Finset.mem_union_left _ hk1)
          have heq2 : k2 = j₀ := hseed k2 (Finset.mem_union_right _ hk2)
          subst heq1; subst heq2
          exact (Finset.disjoint_left.mp hdisjS hk1 hk2).elim
    rcases hex with (⟨x, hx⟩ | ⟨y, hy⟩) | (⟨x, hx⟩ | ⟨y, hy⟩)
    · have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; cases h1.2
    · have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; cases h1.2
    · have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; cases h1.1
    · have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.and_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; cases h1.1
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      u.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_left _ hk)]; exact hw₀)
    have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
      v.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hseed k (Finset.mem_union_right _ hk)]; exact hw₀)
    have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hv0
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hu0
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have h1 := ihu hrou (by omega) (fun k hk => hseed k (Finset.mem_union_left _ hk)) hru hcu
    have h2 := ihv hrov (by omega) (fun k hk => hseed k (Finset.mem_union_right _ hk)) hrv hcv
    intro w x y
    simp only [BTree.eval, BTree.evalRaw] at h1 h2 ⊢
    rw [h1 w x y, h2 w x y]
    simp only [BTree.rows, BTree.cols, BTree.seeds, Finset.mem_union]
    rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ((⟨h1, h2⟩ | h1 | h1) | (⟨h1, h2⟩ | h1 | h1))
      · exact Or.inl ⟨Or.inl h1, h2⟩
      · exact Or.inr (Or.inl (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inl ⟨Or.inr h1, h2⟩
      · exact Or.inr (Or.inl (Or.inr h1))
      · exact Or.inr (Or.inr (Or.inr h1))
    · rintro (⟨h1 | h1, h2⟩ | (h1 | h1) | (h1 | h1))
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inl (Or.inr (Or.inr h1))
      · exact Or.inr (Or.inr (Or.inr h1))

lemma BTree.tree_seed_true {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool) (j₀ : Fin h)
    (hro : t.ReadOnce) (hnot : t.notCount = 0)
    (hseed : t.seeds = {j₀}) (hw₀ : w₀ j₀ = true)
    (hzero : t.evalRaw (fun _ => false) (fun _ => false) w₀ = false)
    (hrow : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true)
    (hcol : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true) :
    ∃ B D : Finset (Fin N), B ⊆ t.rows ∧ D ⊆ t.cols ∧ (B ≠ t.rows ∨ D ≠ t.cols) ∧
      ∀ (w : Fin h → Bool) (x y : Fin N),
        t.eval w x y = decide (x ∈ B ∨ y ∈ D ∨ (w j₀ = true ∧ (x ∈ t.rows ∨ y ∈ t.cols))) := by
  induction t with
  | row _ => simp [BTree.seeds] at hseed
  | col _ => simp [BTree.seeds] at hseed
  | seed k =>
    have hk : k = j₀ := by
      have : k ∈ ({j₀} : Finset (Fin h)) := hseed ▸ Finset.mem_singleton_self k
      exact Finset.mem_singleton.mp this
    subst hk
    simp [BTree.evalRaw, hw₀] at hzero
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, hdisjS⟩
    have hsplit : (u.seeds = {j₀} ∧ v.seeds = ∅) ∨ (u.seeds = ∅ ∧ v.seeds = {j₀}) := by
      have hj : j₀ ∈ u.seeds ∪ v.seeds := by
        change j₀ ∈ (BTree.and u v).seeds; rw [hseed]; exact Finset.mem_singleton_self j₀
      rcases Finset.mem_union.mp hj with hju | hjv
      · left
        have hsubU : u.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_left _ hk
        have hU : u.seeds = {j₀} := Finset.Subset.antisymm hsubU (Finset.singleton_subset_iff.mpr hju)
        have hV : v.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_right _ hk)
          subst hk0; exact Finset.disjoint_left.mp hdisjS hju hk
        exact ⟨hU, hV⟩
      · right
        have hsubV : v.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_right _ hk
        have hV : v.seeds = {j₀} := Finset.Subset.antisymm hsubV (Finset.singleton_subset_iff.mpr hjv)
        have hU : u.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_left _ hk)
          subst hk0; exact Finset.disjoint_right.mp hdisjS hjv hk
        exact ⟨hU, hV⟩
    rcases hsplit with ⟨hU, hV⟩ | ⟨hU, hV⟩
    · have hv0 : v.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
        v.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hV] at hk; exact (Finset.notMem_empty k hk).elim)
      have hur : u.rows = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
        have h1 := hrow x (Finset.mem_union_left _ hx)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
        have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
          (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hv0
        rw [hv_eq] at h1; cases h1.2
      have huc : u.cols = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro y hy
        have h1 := hcol y (Finset.mem_union_left _ hy)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
        have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
          (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
            have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hv0
        rw [hv_eq] at h1; cases h1.2
      have huev := u.eval_eq_seed_of_only_seed (by omega) hur huc j₀ (fun k hk => by rw [hU] at hk; exact Finset.mem_singleton.mp hk)
      have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := fun x hx =>
        (Bool.and_eq_true _ _ |>.mp (hrow x (Finset.mem_union_right _ hx))).2
      have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := fun y hy =>
        (Bool.and_eq_true _ _ |>.mp (hcol y (Finset.mem_union_right _ hy))).2
      have hvev := v.tree_seedless_tight w₀ hrov (by omega) hV hrv hcv
      have hvne : v.rows.Nonempty ∨ v.cols.Nonempty := by
        rcases v.nonempty_leaves with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · rw [hV] at h3; exact (Finset.not_nonempty_empty h3).elim
      refine ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
      · simp only [BTree.rows, BTree.cols, hur, huc, Finset.empty_union]
        rcases hvne with h1 | h2
        · exact Or.inl (Finset.nonempty_iff_ne_empty.mp h1).symm
        · exact Or.inr (Finset.nonempty_iff_ne_empty.mp h2).symm
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, hur, huc, Finset.empty_union,
          Finset.notMem_empty, false_or] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]
    · have hu0 : u.evalRaw (fun _ => false) (fun _ => false) w₀ = false :=
        u.evalRaw_zero_false (by omega) w₀ (fun k hk => by rw [hU] at hk; exact (Finset.notMem_empty k hk).elim)
      have hvr : v.rows = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro x hx
        have h1 := hrow x (Finset.mem_union_right _ hx)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
        have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
          (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
            have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hu0
        rw [hu_eq] at h1; cases h1.1
      have hvc : v.cols = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro y hy
        have h1 := hcol y (Finset.mem_union_right _ hy)
        simp only [BTree.evalRaw, Bool.and_eq_true] at h1
        have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
        have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
          (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
            have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hu0
        rw [hu_eq] at h1; cases h1.1
      have hvev := v.eval_eq_seed_of_only_seed (by omega) hvr hvc j₀ (fun k hk => by rw [hV] at hk; exact Finset.mem_singleton.mp hk)
      have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := fun x hx =>
        (Bool.and_eq_true _ _ |>.mp (hrow x (Finset.mem_union_left _ hx))).1
      have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := fun y hy =>
        (Bool.and_eq_true _ _ |>.mp (hcol y (Finset.mem_union_left _ hy))).1
      have huev := u.tree_seedless_tight w₀ hrou (by omega) hU hru hcu
      have hune : u.rows.Nonempty ∨ u.cols.Nonempty := by
        rcases u.nonempty_leaves with h1 | h2 | h3
        · exact Or.inl h1
        · exact Or.inr h2
        · rw [hU] at h3; exact (Finset.not_nonempty_empty h3).elim
      refine ⟨∅, ∅, Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
      · simp only [BTree.rows, BTree.cols, hvr, hvc, Finset.union_empty]
        rcases hune with h1 | h2
        · exact Or.inl (Finset.nonempty_iff_ne_empty.mp h1).symm
        · exact Or.inr (Finset.nonempty_iff_ne_empty.mp h2).symm
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw, BTree.rows, BTree.cols, hvr, hvc, Finset.union_empty,
          Finset.notMem_empty, false_or] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; tauto
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, hdisjS⟩
    simp only [BTree.evalRaw, Bool.or_eq_false_iff] at hzero
    have hsplit : (u.seeds = {j₀} ∧ v.seeds = ∅) ∨ (u.seeds = ∅ ∧ v.seeds = {j₀}) := by
      have hj : j₀ ∈ u.seeds ∪ v.seeds := by
        change j₀ ∈ (BTree.or u v).seeds; rw [hseed]; exact Finset.mem_singleton_self j₀
      rcases Finset.mem_union.mp hj with hju | hjv
      · left
        have hsubU : u.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_left _ hk
        have hU : u.seeds = {j₀} := Finset.Subset.antisymm hsubU (Finset.singleton_subset_iff.mpr hju)
        have hV : v.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_right _ hk)
          subst hk0; exact Finset.disjoint_left.mp hdisjS hju hk
        exact ⟨hU, hV⟩
      · right
        have hsubV : v.seeds ⊆ {j₀} := by intro k hk; rw [← hseed]; exact Finset.mem_union_right _ hk
        have hV : v.seeds = {j₀} := Finset.Subset.antisymm hsubV (Finset.singleton_subset_iff.mpr hjv)
        have hU : u.seeds = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]; intro k hk
          have hk0 : k = j₀ := Finset.mem_singleton.mp (hseed ▸ Finset.mem_union_left _ hk)
          subst hk0; exact Finset.disjoint_right.mp hdisjS hjv hk
        exact ⟨hU, hV⟩
    have hru : ∀ x ∈ u.rows, u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_left _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnv : x ∉ v.rows := Finset.disjoint_left.mp hdisjR hx
      have hv_eq : v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnv (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hzero.2
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hcu : ∀ y ∈ u.cols, u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_left _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynv : y ∉ v.cols := Finset.disjoint_left.mp hdisjC hy
      have hv_eq : v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (v.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynv (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hzero.2
      rw [hv_eq] at h1; exact h1.resolve_right (by decide)
    have hrv : ∀ x ∈ v.rows, v.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
      intro x hx
      have h1 := hrow x (Finset.mem_union_right _ hx)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hxnu : x ∉ u.rows := Finset.disjoint_right.mp hdisjR hx
      have hu_eq : u.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun i hi => by
          have : i ≠ x := fun heq => hxnu (heq ▸ hi); simp [this]) (fun _ _ => rfl) (fun _ _ => rfl)).trans hzero.1
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    have hcv : ∀ y ∈ v.cols, v.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
      intro y hy
      have h1 := hcol y (Finset.mem_union_right _ hy)
      simp only [BTree.evalRaw, Bool.or_eq_true] at h1
      have hynu : y ∉ u.cols := Finset.disjoint_right.mp hdisjC hy
      have hu_eq : u.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = false :=
        (u.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl) (fun k hk => by
          have : k ≠ y := fun heq => hynu (heq ▸ hk); simp [this]) (fun _ _ => rfl)).trans hzero.1
      rw [hu_eq] at h1; exact h1.resolve_left (by decide)
    rcases hsplit with ⟨hU, hV⟩ | ⟨hU, hV⟩
    · obtain ⟨B₁, D₁, hB₁, hD₁, hne₁, huev⟩ := ihu hrou (by omega) hU hzero.1 hru hcu
      have hvev := v.tree_seedless_tight w₀ hrov (by omega) hV hrv hcv
      refine ⟨B₁ ∪ v.rows, D₁ ∪ v.cols, Finset.union_subset_union_left hB₁,
        Finset.union_subset_union_left hD₁, ?_, ?_⟩
      · rcases hne₁ with hBne | hDne
        · left; intro heq; apply hBne; apply Finset.Subset.antisymm hB₁
          intro x hx
          have hxm : x ∈ B₁ ∪ v.rows := heq ▸ Finset.mem_union_left _ hx
          exact (Finset.mem_union.mp hxm).resolve_right (Finset.disjoint_left.mp hdisjR hx)
        · right; intro heq; apply hDne; apply Finset.Subset.antisymm hD₁
          intro y hy
          have hym : y ∈ D₁ ∪ v.cols := heq ▸ Finset.mem_union_left _ hy
          exact (Finset.mem_union.mp hym).resolve_right (Finset.disjoint_left.mp hdisjC hy)
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        simp only [BTree.rows, BTree.cols, Finset.mem_union]
        rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h1 | h1 | ⟨hw, h1 | h1⟩) | (h1 | h1))
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl (Or.inl h1))
          · exact Or.inr (Or.inr ⟨hw, Or.inl (Or.inl h1)⟩)
          · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inl h1)⟩)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inl (Or.inr h1))
        · rintro ((h1 | h1) | (h1 | h1) | ⟨hw, (h1 | h1) | (h1 | h1)⟩)
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl (Or.inr (Or.inl h1))
          · exact Or.inr (Or.inr h1)
          · exact Or.inl (Or.inr (Or.inr ⟨hw, Or.inl h1⟩))
          · exact Or.inr (Or.inl h1)
          · exact Or.inl (Or.inr (Or.inr ⟨hw, Or.inr h1⟩))
          · exact Or.inr (Or.inr h1)
    · obtain ⟨B₁, D₁, hB₁, hD₁, hne₁, hvev⟩ := ihv hrov (by omega) hV hzero.2 hrv hcv
      have huev := u.tree_seedless_tight w₀ hrou (by omega) hU hru hcu
      refine ⟨u.rows ∪ B₁, u.cols ∪ D₁, Finset.union_subset_union_right hB₁,
        Finset.union_subset_union_right hD₁, ?_, ?_⟩
      · rcases hne₁ with hBne | hDne
        · left; intro heq; apply hBne; apply Finset.Subset.antisymm hB₁
          intro x hx
          have hxm : x ∈ u.rows ∪ B₁ := heq ▸ Finset.mem_union_right _ hx
          exact (Finset.mem_union.mp hxm).resolve_left (Finset.disjoint_right.mp hdisjR hx)
        · right; intro heq; apply hDne; apply Finset.Subset.antisymm hD₁
          intro y hy
          have hym : y ∈ u.cols ∪ D₁ := heq ▸ Finset.mem_union_right _ hy
          exact (Finset.mem_union.mp hym).resolve_left (Finset.disjoint_right.mp hdisjC hy)
      · intro w x y
        simp only [BTree.eval, BTree.evalRaw] at huev hvev ⊢
        rw [huev w x y, hvev w x y]
        simp only [BTree.rows, BTree.cols, Finset.mem_union]
        rw [Bool.eq_iff_iff]; simp only [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h1 | h1) | (h1 | h1 | ⟨hw, h1 | h1⟩))
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl (Or.inl h1))
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inl (Or.inr h1))
          · exact Or.inr (Or.inr ⟨hw, Or.inl (Or.inr h1)⟩)
          · exact Or.inr (Or.inr ⟨hw, Or.inr (Or.inr h1)⟩)
        · rintro ((h1 | h1) | (h1 | h1) | ⟨hw, (h1 | h1) | (h1 | h1)⟩)
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inl h1)
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inr (Or.inl h1))
          · exact Or.inl (Or.inl h1)
          · exact Or.inr (Or.inr (Or.inr ⟨hw, Or.inl h1⟩))
          · exact Or.inl (Or.inr h1)
          · exact Or.inr (Or.inr (Or.inr ⟨hw, Or.inr h1⟩))

def BTree.hasBigAnd {N h : ℕ} : BTree N h → Prop
  | .row _ => False
  | .col _ => False
  | .seed _ => False
  | .not t => t.hasBigAnd
  | .and u v => (2 ≤ u.lineCount ∨ 2 ≤ v.lineCount) ∨ u.hasBigAnd ∨ v.hasBigAnd
  | .or u v => u.hasBigAnd ∨ v.hasBigAnd

lemma BTree.area_le_lineCount {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hnot : t.notCount = 0) (hseed : t.seeds = ∅) :
    areaC (t.eval w₀) ≤ t.lineCount * N := by
  apply area_le_of_lines (t.eval w₀) t.rows t.cols
  intro x y hxy
  by_contra hneither; push Not at hneither
  have heq : t.eval w₀ x y = t.evalRaw (fun _ => false) (fun _ => false) w₀ :=
    t.evalRaw_congr _ _ _ _ _ _
      (fun i hi => by have : i ≠ x := fun h => hneither.1 (h ▸ hi); simp [this])
      (fun j hj => by have : j ≠ y := fun h => hneither.2 (h ▸ hj); simp [this])
      (fun _ _ => rfl)
  rw [heq, t.evalRaw_zero_false hnot w₀ (fun j hj => by rw [hseed] at hj; exact (Finset.notMem_empty j hj).elim)] at hxy
  cases hxy

lemma BTree.lineCount_pos {N h : ℕ} (t : BTree N h) (hseed : t.seeds = ∅) :
    1 ≤ t.lineCount := by
  rcases t.nonempty_leaves with h1 | h2 | h3
  · have := Finset.card_pos.mpr h1; unfold BTree.lineCount; omega
  · have := Finset.card_pos.mpr h2; unfold BTree.lineCount; omega
  · rw [hseed] at h3; exact (Finset.not_nonempty_empty h3).elim

lemma BTree.lineCount_and {N h : ℕ} (u v : BTree N h)
    (hR : Disjoint u.rows v.rows) (hC : Disjoint u.cols v.cols) :
    (BTree.and u v).lineCount = u.lineCount + v.lineCount := by
  simp only [BTree.lineCount, BTree.rows, BTree.cols,
    Finset.card_union_of_disjoint hR, Finset.card_union_of_disjoint hC]
  omega

lemma BTree.lineCount_or {N h : ℕ} (u v : BTree N h)
    (hR : Disjoint u.rows v.rows) (hC : Disjoint u.cols v.cols) :
    (BTree.or u v).lineCount = u.lineCount + v.lineCount := by
  simp only [BTree.lineCount, BTree.rows, BTree.cols,
    Finset.card_union_of_disjoint hR, Finset.card_union_of_disjoint hC]
  omega

lemma BTree.area_le_of_hasBigAnd {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅) (hbig : t.hasBigAnd) :
    areaC (t.eval w₀) + 2 * N ≤ t.lineCount * N := by
  induction t with
  | row _ => exact hbig.elim
  | col _ => exact hbig.elim
  | seed _ => exact hbig.elim
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hlc := BTree.lineCount_and u v hdisjR hdisjC
    have hleU : areaC ((BTree.and u v).eval w₀) ≤ areaC (u.eval w₀) :=
      area_le_of_subset _ _ (fun x y h => (Bool.and_eq_true _ _ |>.mp h).1)
    have hleV : areaC ((BTree.and u v).eval w₀) ≤ areaC (v.eval w₀) :=
      area_le_of_subset _ _ (fun x y h => (Bool.and_eq_true _ _ |>.mp h).2)
    have hU := u.area_le_lineCount w₀ (by omega) hseed.1
    have hV := v.area_le_lineCount w₀ (by omega) hseed.2
    rw [hlc, Nat.add_mul]
    rcases hbig with (h2u | h2v) | hbu | hbv
    · have : 2 * N ≤ u.lineCount * N := Nat.mul_le_mul_right N h2u
      omega
    · have : 2 * N ≤ v.lineCount * N := Nat.mul_le_mul_right N h2v
      omega
    · have := ihu hrou (by omega) hseed.1 hbu; omega
    · have := ihv hrov (by omega) hseed.2 hbv; omega
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hlc := BTree.lineCount_or u v hdisjR hdisjC
    have hor : areaC ((BTree.or u v).eval w₀) ≤ areaC (u.eval w₀) + areaC (v.eval w₀) :=
      area_or_le (u.eval w₀) (v.eval w₀)
    have hU := u.area_le_lineCount w₀ (by omega) hseed.1
    have hV := v.area_le_lineCount w₀ (by omega) hseed.2
    rw [hlc, Nat.add_mul]
    rcases hbig with hbu | hbv
    · have := ihu hrou (by omega) hseed.1 hbu; omega
    · have := ihv hrov (by omega) hseed.2 hbv; omega

lemma BTree.single_leaf_form {N h : ℕ} (t : BTree N h)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅) (hlc : t.lineCount = 1) :
    t.andCount = 0 ∧
    ((∃ x : Fin N, t.rows = {x} ∧ t.cols = ∅ ∧ ∀ w a b, t.eval w a b = decide (a = x)) ∨
     (∃ y : Fin N, t.rows = ∅ ∧ t.cols = {y} ∧ ∀ w a b, t.eval w a b = decide (b = y))) := by
  induction t with
  | row x =>
    refine ⟨rfl, Or.inl ⟨x, rfl, rfl, fun _ a _ => by simp only [BTree.eval, BTree.evalRaw]; exact decide_eq_decide.mpr eq_comm⟩⟩
  | col y =>
    refine ⟨rfl, Or.inr ⟨y, rfl, rfl, fun _ _ b => by simp only [BTree.eval, BTree.evalRaw]; exact decide_eq_decide.mpr eq_comm⟩⟩
  | seed _ => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    exfalso
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨_, _, hdisjR, hdisjC, _⟩
    have h1 := u.lineCount_pos hseed.1
    have h2 := v.lineCount_pos hseed.2
    have hlc' := BTree.lineCount_and u v hdisjR hdisjC
    omega
  | or u v _ _ =>
    exfalso
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨_, _, hdisjR, hdisjC, _⟩
    have h1 := u.lineCount_pos hseed.1
    have h2 := v.lineCount_pos hseed.2
    have hlc' := BTree.lineCount_or u v hdisjR hdisjC
    omega

lemma BTree.area_le_of_no_bigAnd {N h : ℕ} (t : BTree N h) (w₀ : Fin h → Bool)
    (hro : t.ReadOnce) (hnot : t.notCount = 0) (hseed : t.seeds = ∅) (hnbig : ¬ t.hasBigAnd) :
    areaC (t.eval w₀) + 2 * t.andCount * N ≤ t.lineCount * N + t.andCount := by
  induction t with
  | row x =>
    have hle := (BTree.row x : BTree N h).area_le_lineCount w₀ rfl rfl
    simp only [BTree.andCount, Nat.mul_zero, Nat.zero_mul, add_zero]
    exact hle
  | col y =>
    have hle := (BTree.col y : BTree N h).area_le_lineCount w₀ rfl rfl
    simp only [BTree.andCount, Nat.mul_zero, Nat.zero_mul, add_zero]
    exact hle
  | seed _ => simp [BTree.seeds] at hseed
  | not _ _ => simp [BTree.notCount] at hnot
  | and u v _ _ =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    simp only [BTree.hasBigAnd, not_or] at hnbig
    have hu1 : u.lineCount = 1 := by have := u.lineCount_pos hseed.1; omega
    have hv1 : v.lineCount = 1 := by have := v.lineCount_pos hseed.2; omega
    obtain ⟨hua, huf⟩ := u.single_leaf_form hrou (by omega) hseed.1 hu1
    obtain ⟨hva, hvf⟩ := v.single_leaf_form hrov (by omega) hseed.2 hv1
    have hlc : (BTree.and u v).lineCount = 2 := by
      rw [BTree.lineCount_and u v hdisjR hdisjC, hu1, hv1]
    have hac : (BTree.and u v).andCount = 1 := by simp [BTree.andCount, hua, hva]
    have harea1 : areaC ((BTree.and u v).eval w₀) ≤ 1 := by
      rcases huf with ⟨x₁, hru, _, huev⟩ | ⟨y₁, _, hcu, huev⟩ <;>
      rcases hvf with ⟨x₂, hrv, _, hvev⟩ | ⟨y₂, _, hcv, hvev⟩
      · have hne : x₁ ≠ x₂ := by
          intro h; subst h; exact Finset.disjoint_left.mp hdisjR (hru ▸ Finset.mem_singleton_self x₁) (hrv ▸ Finset.mem_singleton_self x₁)
        have h0 : areaC ((BTree.and u v).eval w₀) = 0 := by
          unfold areaC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro ⟨a, b⟩ _
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true, not_and]
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval] at h1 h2
          rw [h1, h2]; simp only [decide_eq_true_eq]
          intro ha1 ha2; exact hne (ha1.symm.trans ha2)
        omega
      · have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (BTree.and u v).eval w₀ z.1 z.2 = true) ⊆ {(x₁, y₂)} := by
          intro ⟨a, b⟩ hz
          rw [Finset.mem_filter] at hz
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true] at h1 h2 hz
          rw [h1, h2] at hz
          simp only [decide_eq_true_eq] at hz
          rw [Finset.mem_singleton]; exact Prod.ext hz.2.1 hz.2.2
        exact le_trans (Finset.card_le_card hsub) (by simp)
      · have hsub : (Finset.univ : Finset (Fin N × Fin N)).filter (fun z => (BTree.and u v).eval w₀ z.1 z.2 = true) ⊆ {(x₂, y₁)} := by
          intro ⟨a, b⟩ hz
          rw [Finset.mem_filter] at hz
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true] at h1 h2 hz
          rw [h1, h2] at hz
          simp only [decide_eq_true_eq] at hz
          rw [Finset.mem_singleton]; exact Prod.ext hz.2.2 hz.2.1
        exact le_trans (Finset.card_le_card hsub) (by simp)
      · have hne : y₁ ≠ y₂ := by
          intro h; subst h; exact Finset.disjoint_left.mp hdisjC (hcu ▸ Finset.mem_singleton_self y₁) (hcv ▸ Finset.mem_singleton_self y₁)
        have h0 : areaC ((BTree.and u v).eval w₀) = 0 := by
          unfold areaC
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro ⟨a, b⟩ _
          simp only [BTree.eval, BTree.evalRaw, Bool.and_eq_true, not_and]
          have h1 := huev w₀ a b; have h2 := hvev w₀ a b
          simp only [BTree.eval] at h1 h2
          rw [h1, h2]; simp only [decide_eq_true_eq]
          intro hb1 hb2; exact hne (hb1.symm.trans hb2)
        omega
    rw [hlc, hac]; omega
  | or u v ihu ihv =>
    simp only [BTree.notCount] at hnot
    simp only [BTree.seeds, Finset.union_eq_empty] at hseed
    simp only [BTree.hasBigAnd, not_or] at hnbig
    rcases hro with ⟨hrou, hrov, hdisjR, hdisjC, _⟩
    have hu := ihu hrou (by omega) hseed.1 hnbig.1
    have hv := ihv hrov (by omega) hseed.2 hnbig.2
    have hor : areaC ((BTree.or u v).eval w₀) ≤ areaC (u.eval w₀) + areaC (v.eval w₀) :=
      area_or_le (u.eval w₀) (v.eval w₀)
    have hlc := BTree.lineCount_or u v hdisjR hdisjC
    have hac : (BTree.or u v).andCount = u.andCount + v.andCount := rfl
    rw [hlc, hac]
    have h1 : 2 * (u.andCount + v.andCount) * N = 2 * u.andCount * N + 2 * v.andCount * N := by ring
    have h2 : (u.lineCount + v.lineCount) * N = u.lineCount * N + v.lineCount * N := by ring
    omega

def unfoldTree {N h : ℕ} (hN : 0 < N) (C : Circuit) (w : ℕ) : BTree N h :=
  if _ : N + N + h ≤ w ∧ w - (N + N + h) < C.gates.length then
    let g := gateAt C (w - (N + N + h))
    match g.op, g.inputs with
    | .not, [a] => if _ : a < w then .not (unfoldTree hN C a) else .row ⟨0, hN⟩
    | .and, [a, b] => if _ : a < w ∧ b < w then .and (unfoldTree hN C a) (unfoldTree hN C b) else .row ⟨0, hN⟩
    | .or, [a, b] => if _ : a < w ∧ b < w then .or (unfoldTree hN C a) (unfoldTree hN C b) else .row ⟨0, hN⟩
    | _, [a] => if _ : a < w then unfoldTree hN C a else .row ⟨0, hN⟩
    | _, _ => .row ⟨0, hN⟩
  else if hw1 : w < N then .row ⟨w, hw1⟩
  else if hw2 : w < N + N then .col ⟨w - N, by omega⟩
  else if hw3 : w < N + N + h then .seed ⟨w - (N + N), by omega⟩
  else .row ⟨0, hN⟩
termination_by w

lemma unfoldTree_props {N h : ℕ} (hN : 0 < N) (C : Circuit)
    (hread : ReadsBack (N + N + h) C)
    (hleg : ∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .and ∨ gate.op = .or ∨ (gate.op = .not ∧ gate.inputs.length = 1))) :
    ∀ (w : ℕ), w < N + N + h + C.gates.length →
      (∀ u ∈ reachWires (N + N + h) C w, N + N + h ≤ u → (gateAt C (u - (N + N + h))).inputs ≠ []) →
      (∀ v ∈ (reachWires (N + N + h) C w).erase w,
        readsW (N + N + h) C ((reachWires (N + N + h) C w).filter (N + N + h ≤ ·)) v = 1) →
      let t := unfoldTree (h := h) hN C w
      (∀ wd x y, t.eval wd x y = wireVal C (inpVec wd x y) w) ∧
      (∀ x : Fin N, x ∈ t.rows ↔ x.val ∈ reachWires (N + N + h) C w) ∧
      (∀ y : Fin N, y ∈ t.cols ↔ N + y.val ∈ reachWires (N + N + h) C w) ∧
      (∀ j : Fin h, j ∈ t.seeds ↔ N + N + j.val ∈ reachWires (N + N + h) C w) ∧
      t.ReadOnce ∧
      t.notCount = ((reachWires (N + N + h) C w).filter
        (fun u => N + N + h ≤ u ∧ isNotOp (gateAt C (u - (N + N + h))).op = true)).card := by
  set n := N + N + h
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne0 hreads
    have hreads_child : ∀ a, a ∈ reachWires n C w →
        ∀ v ∈ (reachWires n C a).erase a,
          readsW n C ((reachWires n C a).filter (n ≤ ·)) v = 1 := by
      intro a ha v hv
      have hasub := reachWires_subset_of_mem hread w a ha
      have hv_ne_a : v ≠ a := (Finset.mem_erase.mp hv).1
      have hv_in_a : v ∈ reachWires n C a := (Finset.mem_erase.mp hv).2
      have hge1 := readsW_pos_of_mem_ne hread a v hv_in_a hv_ne_a
      have hvlt : v < a := lt_of_le_of_ne (le_of_mem_reachWires hread a v hv_in_a) hv_ne_a
      have hale : a ≤ w := le_of_mem_reachWires hread w a ha
      have hv_er_w : v ∈ (reachWires n C w).erase w := Finset.mem_erase.mpr ⟨by omega, hasub hv_in_a⟩
      have hle1 : readsW n C ((reachWires n C a).filter (n ≤ ·)) v ≤
          readsW n C ((reachWires n C w).filter (n ≤ ·)) v := by
        apply Finset.sum_le_sum_of_subset
        intro u hu
        exact Finset.mem_filter.mpr ⟨hasub (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
      have h1 := hreads v hv_er_w
      omega
    by_cases hge : n ≤ w
    · have hw2 : w - n < C.gates.length := by omega
      have hmemC : gateAt C (w - n) ∈ C.gates := by
        unfold gateAt; rw [List.getD_eq_getElem _ _ hw2]; exact List.getElem_mem hw2
      rcases hleg _ hmemC with ⟨hlen, hop⟩
      have hne_w : (gateAt C (w - n)).inputs ≠ [] := hne0 w (self_mem_reachWires n C w) hge
      have hnot_filter : ∀ (a : ℕ) (ha : a ∈ (gateAt C (w - n)).inputs),
          a ∈ reachWires n C w ∧ a < w := by
        intro a ha
        have halt : a < w := by have := hread (w - n) hw2 a ha; omega
        have ham : a ∈ reachWires n C w :=
          (mem_reachWires_iff hread w a).mpr (Or.inr ⟨hge, hw2, a, ha, self_mem_reachWires n C a⟩)
        exact ⟨ham, halt⟩
      cases hins : (gateAt C (w - n)).inputs with
      | nil => exact (hne_w hins).elim
      | cons a rest =>
        cases rest with
        | nil =>
          have ha_in : a ∈ (gateAt C (w - n)).inputs := by rw [hins]; exact List.mem_cons_self
          obtain ⟨ha_mem, halt⟩ := hnot_filter a ha_in
          have hasub := reachWires_subset_of_mem hread w a ha_mem
          have hreach_eq : reachWires n C w = insert w (reachWires n C a) := by
            ext v; rw [mem_reachWires_iff hread, Finset.mem_insert]
            constructor
            · rintro (rfl | ⟨_, _, u, hu, hvu⟩)
              · exact Or.inl rfl
              · rw [hins, List.mem_singleton] at hu; subst hu; exact Or.inr hvu
            · rintro (rfl | hva)
              · exact Or.inl rfl
              · exact Or.inr ⟨hge, hw2, a, ha_in, hva⟩
          have hw_not_a : w ∉ reachWires n C a := by
            intro hm; have := le_of_mem_reachWires hread a w hm; omega
          obtain ⟨heva, hrowa, hcola, hseeda, hroa, hnota⟩ :=
            ih a halt (by omega) (fun u hu hun => hne0 u (hasub hu) hun) (hreads_child a ha_mem)
          rcases hop with hop_eq | hop_eq | ⟨hop_eq, _⟩
          · have htree : unfoldTree (h := h) hN C w = unfoldTree (h := h) hN C a := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, hroa, ?_⟩
            · rw [heva wd x y, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · rw [hrowa x, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · rw [hcola y, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · rw [hseeda j, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · rw [hnota, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              simp [hnf]
          · have htree : unfoldTree (h := h) hN C w = unfoldTree (h := h) hN C a := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, hroa, ?_⟩
            · rw [heva wd x y, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · rw [hrowa x, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · rw [hcola y, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · rw [hseeda j, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · rw [hnota, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              simp [hnf]
          · have htree : unfoldTree (h := h) hN C w = .not (unfoldTree (h := h) hN C a) := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, hroa, ?_⟩
            · simp only [BTree.eval, BTree.evalRaw]
              have h1 := heva wd x y; simp only [BTree.eval] at h1
              rw [h1, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · simp only [BTree.rows]; rw [hrowa x, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · simp only [BTree.cols]; rw [hcola y, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · simp only [BTree.seeds]; rw [hseeda j, hreach_eq, Finset.mem_insert]; constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · simp only [BTree.notCount]
              have hnot_w : n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true := ⟨hge, by rw [hop_eq]; rfl⟩
              rw [hnota, hreach_eq, Finset.filter_insert, if_pos hnot_w, Finset.card_insert_of_notMem]
              intro hm; exact hw_not_a (Finset.mem_filter.mp hm).1
        | cons b rest' =>
          have hnil : rest' = [] := List.length_eq_zero_iff.mp (by rw [hins] at hlen; simp only [List.length_cons] at hlen; omega)
          subst hnil
          have ha_in : a ∈ (gateAt C (w - n)).inputs := by rw [hins]; exact List.mem_cons_self
          have hb_in : b ∈ (gateAt C (w - n)).inputs := by rw [hins]; exact List.mem_cons_of_mem a List.mem_cons_self
          obtain ⟨ha_mem, halt⟩ := hnot_filter a ha_in
          obtain ⟨hb_mem, hblt⟩ := hnot_filter b hb_in
          have hasub := reachWires_subset_of_mem hread w a ha_mem
          have hbsub := reachWires_subset_of_mem hread w b hb_mem
          have hdisj : Disjoint (reachWires n C a) (reachWires n C b) :=
            disjoint_children_of_reads_one hread w hw hreads w a b
              (Finset.mem_filter.mpr ⟨self_mem_reachWires n C w, hge⟩) hins
          have hreach_eq : reachWires n C w = insert w (reachWires n C a ∪ reachWires n C b) := by
            ext v; rw [mem_reachWires_iff hread, Finset.mem_insert, Finset.mem_union]
            constructor
            · rintro (rfl | ⟨_, _, u, hu, hvu⟩)
              · exact Or.inl rfl
              · rw [hins] at hu; simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
                rcases hu with rfl | rfl
                · exact Or.inr (Or.inl hvu)
                · exact Or.inr (Or.inr hvu)
            · rintro (rfl | hva | hvb)
              · exact Or.inl rfl
              · exact Or.inr ⟨hge, hw2, a, ha_in, hva⟩
              · exact Or.inr ⟨hge, hw2, b, hb_in, hvb⟩
          obtain ⟨heva, hrowa, hcola, hseeda, hroa, hnota⟩ :=
            ih a halt (by omega) (fun u hu hun => hne0 u (hasub hu) hun) (hreads_child a ha_mem)
          obtain ⟨hevb, hrowb, hcolb, hseedb, hrob, hnotb⟩ :=
            ih b hblt (by omega) (fun u hu hun => hne0 u (hbsub hu) hun) (hreads_child b hb_mem)
          have hdisjR : Disjoint (unfoldTree (h := h) hN C a).rows (unfoldTree (h := h) hN C b).rows := by
            rw [Finset.disjoint_left]; intro x hx1 hx2
            exact Finset.disjoint_left.mp hdisj ((hrowa x).mp hx1) ((hrowb x).mp hx2)
          have hdisjC : Disjoint (unfoldTree (h := h) hN C a).cols (unfoldTree (h := h) hN C b).cols := by
            rw [Finset.disjoint_left]; intro y hy1 hy2
            exact Finset.disjoint_left.mp hdisj ((hcola y).mp hy1) ((hcolb y).mp hy2)
          have hdisjS : Disjoint (unfoldTree (h := h) hN C a).seeds (unfoldTree (h := h) hN C b).seeds := by
            rw [Finset.disjoint_left]; intro j hj1 hj2
            exact Finset.disjoint_left.mp hdisj ((hseeda j).mp hj1) ((hseedb j).mp hj2)
          rcases hop with hop_eq | hop_eq | ⟨_, h1⟩
          · have htree : unfoldTree (h := h) hN C w = .and (unfoldTree (h := h) hN C a) (unfoldTree (h := h) hN C b) := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt, hblt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, ⟨hroa, hrob, hdisjR, hdisjC, hdisjS⟩, ?_⟩
            · simp only [BTree.eval, BTree.evalRaw]
              have h1 := heva wd x y; have h2 := hevb wd x y
              simp only [BTree.eval] at h1 h2
              rw [h1, h2, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · simp only [BTree.rows, Finset.mem_union]; rw [hrowa x, hrowb x, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · simp only [BTree.cols, Finset.mem_union]; rw [hcola y, hcolb y, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · simp only [BTree.seeds, Finset.mem_union]; rw [hseeda j, hseedb j, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · simp only [BTree.notCount]
              rw [hnota, hnotb, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              rw [if_neg hnf, Finset.filter_union, Finset.card_union_of_disjoint]
              exact Finset.disjoint_filter_filter hdisj
          · have htree : unfoldTree (h := h) hN C w = .or (unfoldTree (h := h) hN C a) (unfoldTree (h := h) hN C b) := by
              rw [unfoldTree]; simp only [show N + N + h ≤ w from hge, show w - (N + N + h) < C.gates.length from hw2, and_self, dite_true, show (gateAt C (w - (N + N + h))).op = _ from hop_eq, show (gateAt C (w - (N + N + h))).inputs = _ from hins, halt, hblt]
            dsimp only; rw [htree]
            refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, ⟨hroa, hrob, hdisjR, hdisjC, hdisjS⟩, ?_⟩
            · simp only [BTree.eval, BTree.evalRaw]
              have h1 := heva wd x y; have h2 := hevb wd x y
              simp only [BTree.eval] at h1 h2
              rw [h1, h2, wireVal_gate C hread _ (inpVec_length wd x y) w hge hw2, hop_eq, hins]
              simp [GateOp.eval]
            · simp only [BTree.rows, Finset.mem_union]; rw [hrowa x, hrowb x, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hx)
                · have := x.isLt; omega
                · exact hx
            · simp only [BTree.cols, Finset.mem_union]; rw [hcola y, hcolb y, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hy)
                · have := y.isLt; omega
                · exact hy
            · simp only [BTree.seeds, Finset.mem_union]; rw [hseeda j, hseedb j, hreach_eq, Finset.mem_insert, Finset.mem_union]
              constructor
              · exact Or.inr
              · rintro (heq | hj)
                · have := j.isLt; omega
                · exact hj
            · simp only [BTree.notCount]
              rw [hnota, hnotb, hreach_eq, Finset.filter_insert]
              have hnf : ¬ (n ≤ w ∧ isNotOp (gateAt C (w - n)).op = true) := by rw [hop_eq]; simp [isNotOp]
              rw [if_neg hnf, Finset.filter_union, Finset.card_union_of_disjoint]
              exact Finset.disjoint_filter_filter hdisj
          · rw [hins] at h1; simp at h1
    · have hlt : w < n := Nat.lt_of_not_ge hge
      have hreach_sing : reachWires n C w = {w} := by
        rw [reachWires]; simp [hge]
      have hnot_zero : ((reachWires n C w).filter
          (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true)).card = 0 := by
        rw [hreach_sing, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro u hu; rw [Finset.mem_singleton.mp hu]; omega
      by_cases hw1 : w < N
      · have htree : unfoldTree (h := h) hN C w = .row ⟨w, hw1⟩ := by
          rw [unfoldTree]; simp [show ¬ (N + N + h ≤ w) from hge, hw1]
        dsimp only; rw [htree]
        refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, trivial, ?_⟩
        · rw [wireVal_input C _ (inpVec_length wd x y) w hlt, inpVec_getD_row wd x y w hw1]
          rfl
        · simp only [BTree.rows, Finset.mem_singleton, hreach_sing]
          exact ⟨fun hx => congrArg Fin.val hx, fun hx => Fin.ext hx⟩
        · simp only [BTree.cols, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
        · simp only [BTree.seeds, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
        · simp [BTree.notCount, hnot_zero]
      · by_cases hw2 : w < N + N
        · have htree : unfoldTree (h := h) hN C w = .col ⟨w - N, by omega⟩ := by
            rw [unfoldTree]; simp [show ¬ (N + N + h ≤ w) from hge, hw1, hw2]
          dsimp only; rw [htree]
          refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, trivial, ?_⟩
          · rw [wireVal_input C _ (inpVec_length wd x y) w hlt, inpVec_getD_col wd x y w (by omega) hw2]
            rfl
          · simp only [BTree.rows, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp only [BTree.cols, Finset.mem_singleton, hreach_sing, Fin.ext_iff]; omega
          · simp only [BTree.seeds, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp [BTree.notCount, hnot_zero]
        · have htree : unfoldTree (h := h) hN C w = .seed ⟨w - (N + N), by omega⟩ := by
            rw [unfoldTree]; simp [show ¬ (N + N + h ≤ w) from hge, hw1, hw2, show w < N + N + h from hlt]
          dsimp only; rw [htree]
          refine ⟨fun wd x y => ?_, fun x => ?_, fun y => ?_, fun j => ?_, trivial, ?_⟩
          · rw [wireVal_input C _ (inpVec_length wd x y) w hlt, inpVec_getD_seed wd x y w (by omega) hlt]
            rfl
          · simp only [BTree.rows, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp only [BTree.cols, Finset.notMem_empty, hreach_sing, Finset.mem_singleton, false_iff]; omega
          · simp only [BTree.seeds, Finset.mem_singleton, hreach_sing, Fin.ext_iff]; omega
          · simp [BTree.notCount, hnot_zero]

lemma part1_classification (N g : ℕ) (hg : 0 < g) (hgN : g + 1 < N)
    (h : ℕ) (C : Circuit) (hleg : legalC N h C) (hsize : C.size ≤ g)
    (w₀ : Fin h → Bool)
    (hlo : (g - 1) * N + 1 < areaC (tableC N h C w₀))
    (hhi : areaC (tableC N h C w₀) < N * (N - g)) :
    (∃ R S : Finset (Fin N), g ≤ R.card + S.card ∧ R.card + S.card ≤ g + 1 ∧ lineUnionC N h C R S) ∨
    ∃ (R S : Finset (Fin N)) (j : Fin h), R.card + S.card = g ∧
      ((w₀ j = false ∧ ∀ (w : Fin h → Bool) (x y : Fin N),
        tableC N h C w x y = decide (w j = true ∨ x ∈ R ∨ y ∈ S)) ∨
       (w₀ j = true ∧ ∃ B D : Finset (Fin N), B ⊆ R ∧ D ⊆ S ∧ (B ≠ R ∨ D ≠ S) ∧
        ∀ (w : Fin h → Bool) (x y : Fin N), tableC N h C w x y =
          decide (x ∈ B ∨ y ∈ D ∨ (w j = true ∧ (x ∈ R ∨ y ∈ S))))) := by
  let n := N + N + h
  have hN : 0 < N := by omega
  rcases hleg with ⟨hread, hout, hgates⟩
  have hout' : C.output < n + C.gates.length := hout
  let V := reachWires n C C.output
  let G := V.filter (n ≤ ·)
  let I := V.filter (· < n)
  let n0 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 0)).card
  let n1 := (G.filter (fun u => (gateAt C (u - n)).inputs.length = 1 ∧ isNotOp (gateAt C (u - n)).op = false)).card
  let nnot := (G.filter (fun u => isNotOp (gateAt C (u - n)).op = true)).card
  have hG_le : G.card ≤ g := by
    have hsub : G ⊆ (Finset.range C.gates.length).image (fun k => n + k) := by
      intro u hu
      have huV := (Finset.mem_filter.mp hu).1
      have hun := (Finset.mem_filter.mp hu).2
      have hult : u - n < C.gates.length := by
        have := le_of_mem_reachWires hread C.output u huV; omega
      exact Finset.mem_image.mpr ⟨u - n, Finset.mem_range.mpr hult, by omega⟩
    have hle := le_trans (Finset.card_le_card hsub) Finset.card_image_le
    rw [Finset.card_range] at hle
    exact le_trans hle hsize
  obtain ⟨hacc0, hacc_tight0⟩ := accounting_ineq hread hgates C.output hout'
  have hacc : I.card + 2 * n0 + n1 + nnot ≤ G.card + 1 := hacc0
  have hacc_tight : I.card + 2 * n0 + n1 + nnot = G.card + 1 →
      ∀ v ∈ V.erase C.output, readsW n C G v = 1 := hacc_tight0
  let R₀ : Finset (Fin N) := Finset.univ.filter (fun x => x.val ∈ V)
  let S₀ : Finset (Fin N) := Finset.univ.filter (fun y => N + y.val ∈ V)
  let J₀ : Finset (Fin h) := Finset.univ.filter (fun j => N + N + j.val ∈ V)
  have hI_card : I.card = R₀.card + S₀.card + J₀.card := by
    let IR := I.filter (· < N)
    let IS := I.filter (fun v => N ≤ v ∧ v < N + N)
    let IJ := I.filter (fun v => N + N ≤ v)
    have hRcard : IR.card = R₀.card := by
      apply Finset.card_bij (fun v hv => ⟨v, (Finset.mem_filter.mp hv).2⟩)
      · intro v hv
        have hvI := (Finset.mem_filter.mp hv).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hvI).1⟩
      · intro a _ b _ hab; exact congrArg Fin.val hab
      · intro x hx
        refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hx).2, by omega⟩, x.isLt⟩, rfl⟩
    have hScard : IS.card = S₀.card := by
      apply Finset.card_bij (fun v hv => ⟨v - N, by have := (Finset.mem_filter.mp hv).2; omega⟩)
      · intro v hv
        have hvI := (Finset.mem_filter.mp hv).1
        have hv2 := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have heq : N + (v - N) = v := by omega
        rw [heq]; exact (Finset.mem_filter.mp hvI).1
      · intro a ha b hb hab
        have ha2 := (Finset.mem_filter.mp ha).2
        have hb2 := (Finset.mem_filter.mp hb).2
        have := congrArg Fin.val hab; dsimp at this; omega
      · intro y hy
        refine ⟨N + y.val, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hy).2, by omega⟩, by omega⟩, Fin.ext (by simp)⟩
    have hJcard : IJ.card = J₀.card := by
      apply Finset.card_bij (fun v hv => ⟨v - (N + N), by
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
        have h2 := (Finset.mem_filter.mp hv).2; omega⟩)
      · intro v hv
        have hvI := (Finset.mem_filter.mp hv).1
        have hv2 := (Finset.mem_filter.mp hv).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have heq : N + N + (v - (N + N)) = v := by omega
        rw [heq]; exact (Finset.mem_filter.mp hvI).1
      · intro a ha b hb hab
        have ha2 := (Finset.mem_filter.mp ha).2
        have hb2 := (Finset.mem_filter.mp hb).2
        have := congrArg Fin.val hab; dsimp at this; omega
      · intro j hj
        refine ⟨N + N + j.val, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hj).2, by omega⟩, by omega⟩, Fin.ext (by simp)⟩
    have hunion : I = IR ∪ IS ∪ IJ := by
      ext v; simp only [IR, IS, IJ, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hv
        by_cases h1 : v < N
        · exact Or.inl (Or.inl ⟨hv, h1⟩)
        · by_cases h2 : v < N + N
          · exact Or.inl (Or.inr ⟨hv, by omega, h2⟩)
          · exact Or.inr ⟨hv, by omega⟩
      · rintro ((⟨hv, _⟩ | ⟨hv, _⟩) | ⟨hv, _⟩) <;> exact hv
    have hd1 : Disjoint IR IS := by rw [Finset.disjoint_filter]; intro x _ h1 h2; omega
    have hd2 : Disjoint (IR ∪ IS) IJ := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      simp only [IR, IS, IJ, Finset.mem_union, Finset.mem_filter] at hx1 hx2
      omega
    rw [hunion, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
      hRcard, hScard, hJcard]
  have hL_le : R₀.card + S₀.card + J₀.card + 2 * n0 + n1 + nnot ≤ g + 1 := by omega
  have hR_lt : R₀.card < N := by omega
  have hS_lt : S₀.card < N := by omega
  obtain ⟨x_un, hx_un⟩ : ∃ x : Fin N, x ∉ R₀ := by
    by_contra hnone; push Not at hnone
    have : R₀ = Finset.univ := Finset.eq_univ_iff_forall.mpr hnone
    rw [this, Finset.card_univ, Fintype.card_fin] at hR_lt; omega
  obtain ⟨y_un, hy_un⟩ : ∃ y : Fin N, y ∉ S₀ := by
    by_contra hnone; push Not at hnone
    have : S₀ = Finset.univ := Finset.eq_univ_iff_forall.mpr hnone
    rw [this, Finset.card_univ, Fintype.card_fin] at hS_lt; omega
  have hunnamed_const : ∀ x y : Fin N, x ∉ R₀ → y ∉ S₀ →
      tableC N h C w₀ x y = tableC N h C w₀ x_un y_un := by
    intro x y hx hy
    apply wireVal_congr_on_reach hread _ _ (inpVec_length w₀ x y) (inpVec_length w₀ x_un y_un) C.output hout'
    intro v hv hvn
    by_cases hv1 : v < N
    · rw [inpVec_getD_row w₀ x y v hv1, inpVec_getD_row w₀ x_un y_un v hv1]
      have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      have h1 : (⟨v, hv1⟩ : Fin N) ≠ x := fun h => hx (h ▸ hvR)
      have h2 : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
      simp [h1, h2]
    · by_cases hv2 : v < N + N
      · rw [inpVec_getD_col w₀ x y v (by omega) hv2, inpVec_getD_col w₀ x_un y_un v (by omega) hv2]
        have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have : N + (v - N) = v := by omega
          rw [this]; exact hv
        have h1 : (⟨v - N, by omega⟩ : Fin N) ≠ y := fun h => hy (h ▸ hvS)
        have h2 : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
        simp [h1, h2]
      · rw [inpVec_getD_seed w₀ x y v (by omega) hvn, inpVec_getD_seed w₀ x_un y_un v (by omega) hvn]
  have hb0_false : tableC N h C w₀ x_un y_un = false := by
    by_contra hb0
    have hb0T : tableC N h C w₀ x_un y_un = true := by
      cases hv : tableC N h C w₀ x_un y_un
      · exact (hb0 hv).elim
      · rfl
    by_cases hLg : R₀.card + S₀.card ≤ g
    · have h1 := area_ge_of_unnamed_true (tableC N h C w₀) R₀ S₀
        (fun x y hx hy => (hunnamed_const x y hx hy).trans hb0T)
      have h2 := mul_compl_ge (N := N) (r := R₀.card) (s := S₀.card) (by omega)
      have h3 : N * (N - g) ≤ N * (N - (R₀.card + S₀.card)) := Nat.mul_le_mul_left N (by omega)
      omega
    · have hL_eq : R₀.card + S₀.card = g + 1 := by omega
      have hJ0 : J₀.card = 0 := by omega
      have hn0_0 : n0 = 0 := by omega
      have hnnot_0 : nnot = 0 := by omega
      have hmon : ∀ u ∈ V, n ≤ u →
          ((gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or) ∧
          (gateAt C (u - n)).inputs ≠ [] := by
        intro u hu hun
        have huG : u ∈ G := Finset.mem_filter.mpr ⟨hu, hun⟩
        have hult : u - n < C.gates.length := by
          have := le_of_mem_reachWires hread C.output u hu; omega
        have hmemC : gateAt C (u - n) ∈ C.gates := by
          unfold gateAt; rw [List.getD_eq_getElem _ _ hult]; exact List.getElem_mem hult
        have hnot_ne : (gateAt C (u - n)).op ≠ .not := by
          intro hEq
          have hmem : u ∈ G.filter (fun z => isNotOp (gateAt C (z - n)).op = true) :=
            Finset.mem_filter.mpr ⟨huG, by rw [hEq]; rfl⟩
          have hpos : 0 < nnot := Finset.card_pos.mpr ⟨u, hmem⟩
          omega
        have hlen_ne : (gateAt C (u - n)).inputs ≠ [] := by
          intro hEq
          have hmem : u ∈ G.filter (fun z => (gateAt C (z - n)).inputs.length = 0) :=
            Finset.mem_filter.mpr ⟨huG, by simp [hEq]⟩
          have hpos : 0 < n0 := Finset.card_pos.mpr ⟨u, hmem⟩
          omega
        rcases (hgates _ hmemC).2 with h1 | h2 | ⟨h3, _⟩
        · exact ⟨Or.inl h1, hlen_ne⟩
        · exact ⟨Or.inr h2, hlen_ne⟩
        · exact (hnot_ne h3).elim
      have hzero : ∀ v ∈ V, v < n → (inpVec w₀ x_un y_un).getD v false = false := by
        intro v hv hvn
        by_cases hv1 : v < N
        · rw [inpVec_getD_row w₀ x_un y_un v hv1]
          have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
          have : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
          simp [this]
        · by_cases hv2 : v < N + N
          · rw [inpVec_getD_col w₀ x_un y_un v (by omega) hv2]
            have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have : N + (v - N) = v := by omega
              rw [this]; exact hv
            have : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
            simp [this]
          · exfalso
            have hvJ : ⟨v - (N + N), by omega⟩ ∈ J₀ := by
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have : N + N + (v - (N + N)) = v := by omega
              rw [this]; exact hv
            have hpos : 0 < J₀.card := Finset.card_pos.mpr ⟨_, hvJ⟩
            omega
      have hf := wireVal_false_of_all_false hread _ (inpVec_length w₀ x_un y_un) C.output hout' hmon hzero
      change wireVal C (inpVec w₀ x_un y_un) C.output = true at hb0T
      rw [hf] at hb0T; cases hb0T
  have hlines_cov : ∀ x y : Fin N, tableC N h C w₀ x y = true → x ∈ R₀ ∨ y ∈ S₀ := by
    intro x y hxy
    by_contra hneither; push Not at hneither
    rw [hunnamed_const x y hneither.1 hneither.2, hb0_false] at hxy
    cases hxy
  have harea_ub := area_le_of_lines (tableC N h C w₀) R₀ S₀ hlines_cov
  have hL_ge : g ≤ R₀.card + S₀.card := by
    by_contra hlt
    have hle : R₀.card + S₀.card ≤ g - 1 := by omega
    have hmul : (R₀.card + S₀.card) * N ≤ (g - 1) * N := Nat.mul_le_mul_right N hle
    omega
  have hne0_of_n0 : n0 = 0 → ∀ u ∈ V, n ≤ u → (gateAt C (u - n)).inputs ≠ [] := by
    intro hn0 u hu hun hnil
    have hmem : u ∈ G.filter (fun z => (gateAt C (z - n)).inputs.length = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hu, hun⟩, by simp [hnil]⟩
    have := Finset.card_pos.mpr ⟨u, hmem⟩
    omega
  by_cases hL_eq : R₀.card + S₀.card = g
  · have hn0_0 : n0 = 0 := by omega
    have hsing_row : ∀ x ∈ R₀, tableC N h C w₀ x y_un = true := by
      intro x hx
      by_contra hnotT
      have hxf : tableC N h C w₀ x y_un = false := by
        cases hv : tableC N h C w₀ x y_un
        · rfl
        · exact (hnotT hv).elim
      have hcov' : ∀ a b : Fin N, tableC N h C w₀ a b = true → a ∈ R₀.erase x ∨ b ∈ S₀ := by
        intro a b hab
        rcases hlines_cov a b hab with haR | hbS
        · by_cases hax : a = x
          · subst hax
            by_cases hbS' : b ∈ S₀
            · exact Or.inr hbS'
            · exfalso
              have heq : tableC N h C w₀ a b = tableC N h C w₀ a y_un := by
                apply wireVal_congr_on_reach hread _ _ (inpVec_length w₀ a b) (inpVec_length w₀ a y_un) C.output hout'
                intro v hv hvn
                by_cases hv1 : v < N
                · rw [inpVec_getD_row w₀ a b v hv1, inpVec_getD_row w₀ a y_un v hv1]
                · by_cases hv2 : v < N + N
                  · rw [inpVec_getD_col w₀ a b v (by omega) hv2, inpVec_getD_col w₀ a y_un v (by omega) hv2]
                    have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
                      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                      have : N + (v - N) = v := by omega
                      rw [this]; exact hv
                    have h1 : (⟨v - N, by omega⟩ : Fin N) ≠ b := fun h => hbS' (h ▸ hvS)
                    have h2 : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
                    simp [h1, h2]
                  · rw [inpVec_getD_seed w₀ a b v (by omega) hvn, inpVec_getD_seed w₀ a y_un v (by omega) hvn]
              rw [heq, hxf] at hab; cases hab
          · exact Or.inl (Finset.mem_erase.mpr ⟨hax, haR⟩)
        · exact Or.inr hbS
      have hub := area_le_of_lines (tableC N h C w₀) (R₀.erase x) S₀ hcov'
      have her := Finset.card_erase_add_one hx
      have heq_card : (R₀.erase x).card + S₀.card = g - 1 := by omega
      rw [heq_card] at hub; omega
    have hsing_col : ∀ y ∈ S₀, tableC N h C w₀ x_un y = true := by
      intro y hy
      by_contra hnotT
      have hyf : tableC N h C w₀ x_un y = false := by
        cases hv : tableC N h C w₀ x_un y
        · rfl
        · exact (hnotT hv).elim
      have hcov' : ∀ a b : Fin N, tableC N h C w₀ a b = true → a ∈ R₀ ∨ b ∈ S₀.erase y := by
        intro a b hab
        rcases hlines_cov a b hab with haR | hbS
        · exact Or.inl haR
        · by_cases hby : b = y
          · subst hby
            by_cases haR' : a ∈ R₀
            · exact Or.inl haR'
            · exfalso
              have heq : tableC N h C w₀ a b = tableC N h C w₀ x_un b := by
                apply wireVal_congr_on_reach hread _ _ (inpVec_length w₀ a b) (inpVec_length w₀ x_un b) C.output hout'
                intro v hv hvn
                by_cases hv1 : v < N
                · rw [inpVec_getD_row w₀ a b v hv1, inpVec_getD_row w₀ x_un b v hv1]
                  have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
                  have h1 : (⟨v, hv1⟩ : Fin N) ≠ a := fun h => haR' (h ▸ hvR)
                  have h2 : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
                  simp [h1, h2]
                · by_cases hv2 : v < N + N
                  · rw [inpVec_getD_col w₀ a b v (by omega) hv2, inpVec_getD_col w₀ x_un b v (by omega) hv2]
                  · rw [inpVec_getD_seed w₀ a b v (by omega) hvn, inpVec_getD_seed w₀ x_un b v (by omega) hvn]
              rw [heq, hyf] at hab; cases hab
          · exact Or.inr (Finset.mem_erase.mpr ⟨hby, hbS⟩)
      have hub := area_le_of_lines (tableC N h C w₀) R₀ (S₀.erase y) hcov'
      have her := Finset.card_erase_add_one hy
      have heq_card : R₀.card + (S₀.erase y).card = g - 1 := by omega
      rw [heq_card] at hub; omega
    by_cases hnot_pos : nnot = 1
    · exfalso
      have hJ0 : J₀.card = 0 := by omega
      have htight : I.card + 2 * n0 + n1 + nnot = G.card + 1 := by omega
      have hreads := hacc_tight htight
      obtain ⟨hev, hrows, hcols, hseeds, hro, hnotc⟩ :=
        unfoldTree_props hN C hread hgates C.output hout' (hne0_of_n0 hn0_0) hreads
      let t := unfoldTree (h := h) hN C C.output
      have ht_rows : t.rows = R₀ := by
        ext x; rw [hrows x]; simp [R₀, V, n]
      have ht_cols : t.cols = S₀ := by
        ext y; rw [hcols y]; simp [S₀, V, n]
      have ht_seeds : t.seeds = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]; intro j hj
        have : j ∈ J₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hseeds j).mp hj⟩
        have := Finset.card_pos.mpr ⟨j, this⟩; omega
      have ht_not : t.notCount = 1 := by
        rw [hnotc]
        have heq : V.filter (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true) =
            G.filter (fun u => isNotOp (gateAt C (u - n)).op = true) := by
          ext u; simp [G, Finset.mem_filter, and_assoc]
        rw [heq]; exact hnot_pos
      have ht0 : t.evalRaw (fun _ => false) (fun _ => false) w₀ = false := by
        have h1 : t.eval w₀ x_un y_un = false := (hev w₀ x_un y_un).trans hb0_false
        trans (t.eval w₀ x_un y_un)
        · unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _
            (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
            (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
            (fun _ _ => rfl)
        · exact h1
      rcases t.tree_not_one_decr w₀ hro ht_seeds ht_not with ⟨x, hx, hdec⟩ | ⟨y, hy, hdec⟩
      · have hxR : x ∈ R₀ := ht_rows ▸ hx
        have h1 : t.eval w₀ x y_un = true := (hev w₀ x y_un).trans (hsing_row x hxR)
        have h2 : t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl)
            (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
            (fun _ _ => rfl)
        have h3 := hdec h2; rw [ht0] at h3; cases h3
      · have hyS : y ∈ S₀ := ht_cols ▸ hy
        have h1 : t.eval w₀ x_un y = true := (hev w₀ x_un y).trans (hsing_col y hyS)
        have h2 : t.evalRaw (fun _ => false) (fun j => decide (j = y)) w₀ = true := by
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _
            (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
            (fun _ _ => rfl) (fun _ _ => rfl)
        have h3 := hdec h2; rw [ht0] at h3; cases h3
    · have hnnot_0 : nnot = 0 := by omega
      by_cases hJ_pos : J₀.card = 1
      · right
        obtain ⟨j₀, hj₀_eq⟩ := Finset.card_eq_one.mp hJ_pos
        have htight : I.card + 2 * n0 + n1 + nnot = G.card + 1 := by omega
        have hreads := hacc_tight htight
        obtain ⟨hev, hrows, hcols, hseeds, hro, hnotc⟩ :=
          unfoldTree_props hN C hread hgates C.output hout' (hne0_of_n0 hn0_0) hreads
        let t := unfoldTree (h := h) hN C C.output
        have ht_rows : t.rows = R₀ := by ext x; rw [hrows x]; simp [R₀, V, n]
        have ht_cols : t.cols = S₀ := by ext y; rw [hcols y]; simp [S₀, V, n]
        have ht_seeds : t.seeds = {j₀} := by
          rw [← hj₀_eq]; ext j; rw [hseeds j]; simp [J₀, V, n]
        have ht_not : t.notCount = 0 := by
          rw [hnotc]
          have heq : V.filter (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true) =
              G.filter (fun u => isNotOp (gateAt C (u - n)).op = true) := by
            ext u; simp [G, Finset.mem_filter, and_assoc]
          rw [heq]; exact hnnot_0
        have ht0 : t.evalRaw (fun _ => false) (fun _ => false) w₀ = false := by
          have h1 : t.eval w₀ x_un y_un = false := (hev w₀ x_un y_un).trans hb0_false
          trans (t.eval w₀ x_un y_un)
          · unfold BTree.eval
            exact t.evalRaw_congr _ _ _ _ _ _
              (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
              (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
              (fun _ _ => rfl)
          · exact h1
        have hrow_t : ∀ x ∈ t.rows, t.evalRaw (fun i => decide (i = x)) (fun _ => false) w₀ = true := by
          intro x hx
          have h1 : t.eval w₀ x y_un = true := (hev w₀ x y_un).trans (hsing_row x (ht_rows ▸ hx))
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _ (fun _ _ => rfl)
            (fun j hj => by rw [ht_cols] at hj; have : j ≠ y_un := fun h => hy_un (h ▸ hj); simp [this])
            (fun _ _ => rfl)
        have hcol_t : ∀ y ∈ t.cols, t.evalRaw (fun _ => false) (fun k => decide (k = y)) w₀ = true := by
          intro y hy
          have h1 : t.eval w₀ x_un y = true := (hev w₀ x_un y).trans (hsing_col y (ht_cols ▸ hy))
          rw [← h1]; unfold BTree.eval
          exact t.evalRaw_congr _ _ _ _ _ _
            (fun i hi => by rw [ht_rows] at hi; have : i ≠ x_un := fun h => hx_un (h ▸ hi); simp [this])
            (fun _ _ => rfl) (fun _ _ => rfl)
        refine ⟨R₀, S₀, j₀, hL_eq, ?_⟩
        cases hwj : w₀ j₀
        · left
          refine ⟨rfl, fun w x y => ?_⟩
          change wireVal C (inpVec w x y) C.output = _
          rw [← hev w x y]
          have hres := t.tree_seed_false w₀ j₀ hro ht_not (fun k hk => by rw [ht_seeds] at hk; exact Finset.mem_singleton.mp hk)
            hwj hrow_t hcol_t w x y
          rw [ht_rows, ht_cols, ht_seeds] at hres
          simpa using hres
        · right
          obtain ⟨B, D, hB, hD, hne, hres⟩ :=
            t.tree_seed_true w₀ j₀ hro ht_not ht_seeds hwj ht0 hrow_t hcol_t
          rw [ht_rows] at hB hne hres; rw [ht_cols] at hD hne hres
          exact ⟨rfl, B, D, hB, hD, hne, fun w x y => (hev w x y).symm.trans (hres w x y)⟩
      · left
        have hJ0 : J₀.card = 0 := by omega
        have hmon : ∀ u ∈ V, n ≤ u → (gateAt C (u - n)).op = .and ∨ (gateAt C (u - n)).op = .or := by
          intro u hu hun
          have huG : u ∈ G := Finset.mem_filter.mpr ⟨hu, hun⟩
          have hult : u - n < C.gates.length := by
            have := le_of_mem_reachWires hread C.output u hu; omega
          have hmemC : gateAt C (u - n) ∈ C.gates := by
            unfold gateAt; rw [List.getD_eq_getElem _ _ hult]; exact List.getElem_mem hult
          rcases (hgates _ hmemC).2 with h1 | h2 | ⟨h3, _⟩
          · exact Or.inl h1
          · exact Or.inr h2
          · exfalso
            have hmem : u ∈ G.filter (fun z => isNotOp (gateAt C (z - n)).op = true) := Finset.mem_filter.mpr ⟨huG, by rw [h3]; rfl⟩
            have := Finset.card_pos.mpr ⟨u, hmem⟩; omega
        refine ⟨R₀, S₀, by omega, by omega, fun w x y => ?_⟩
        have hindep : tableC N h C w x y = tableC N h C w₀ x y := by
          apply wireVal_congr_on_reach hread _ _ (inpVec_length w x y) (inpVec_length w₀ x y) C.output hout'
          intro v hv hvn
          by_cases hv1 : v < N
          · rw [inpVec_getD_row w x y v hv1, inpVec_getD_row w₀ x y v hv1]
          · by_cases hv2 : v < N + N
            · rw [inpVec_getD_col w x y v (by omega) hv2, inpVec_getD_col w₀ x y v (by omega) hv2]
            · exfalso
              have hvJ : ⟨v - (N + N), by omega⟩ ∈ J₀ := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                have : N + N + (v - (N + N)) = v := by omega
                rw [this]; exact hv
              have := Finset.card_pos.mpr ⟨_, hvJ⟩; omega
        rw [hindep]
        by_cases hmem : x ∈ R₀ ∨ y ∈ S₀
        · simp only [hmem, decide_true]
          rcases hmem with hxR | hyS
          · apply wireVal_mono_on_reach hread (inpVec w₀ x y_un) (inpVec w₀ x y)
              (inpVec_length w₀ x y_un) (inpVec_length w₀ x y) C.output hout' hmon _ (hsing_row x hxR)
            intro v hv hvn hvt
            by_cases hv1 : v < N
            · rw [inpVec_getD_row w₀ x y_un v hv1] at hvt
              rw [inpVec_getD_row w₀ x y v hv1]; exact hvt
            · by_cases hv2 : v < N + N
              · rw [inpVec_getD_col w₀ x y_un v (by omega) hv2] at hvt
                have hvS : ⟨v - N, by omega⟩ ∈ S₀ := by
                  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                  have : N + (v - N) = v := by omega
                  rw [this]; exact hv
                have : (⟨v - N, by omega⟩ : Fin N) ≠ y_un := fun h => hy_un (h ▸ hvS)
                simp [this] at hvt
              · rw [inpVec_getD_seed w₀ x y_un v (by omega) hvn] at hvt
                rw [inpVec_getD_seed w₀ x y v (by omega) hvn]; exact hvt
          · apply wireVal_mono_on_reach hread (inpVec w₀ x_un y) (inpVec w₀ x y)
              (inpVec_length w₀ x_un y) (inpVec_length w₀ x y) C.output hout' hmon _ (hsing_col y hyS)
            intro v hv hvn hvt
            by_cases hv1 : v < N
            · rw [inpVec_getD_row w₀ x_un y v hv1] at hvt
              have hvR : ⟨v, hv1⟩ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
              have : (⟨v, hv1⟩ : Fin N) ≠ x_un := fun h => hx_un (h ▸ hvR)
              simp [this] at hvt
            · by_cases hv2 : v < N + N
              · rw [inpVec_getD_col w₀ x_un y v (by omega) hv2] at hvt
                rw [inpVec_getD_col w₀ x y v (by omega) hv2]; exact hvt
              · rw [inpVec_getD_seed w₀ x_un y v (by omega) hvn] at hvt
                rw [inpVec_getD_seed w₀ x y v (by omega) hvn]; exact hvt
        · push Not at hmem
          simp only [hmem.1, hmem.2, or_self, decide_false]
          exact (hunnamed_const x y hmem.1 hmem.2).trans hb0_false
  · left
    have hL_eq1 : R₀.card + S₀.card = g + 1 := by omega
    have hJ0 : J₀.card = 0 := by omega
    have hn0_0 : n0 = 0 := by omega
    have hnnot_0 : nnot = 0 := by omega
    have htight : I.card + 2 * n0 + n1 + nnot = G.card + 1 := by omega
    have hreads := hacc_tight htight
    obtain ⟨hev, hrows, hcols, hseeds, hro, hnotc⟩ :=
      unfoldTree_props hN C hread hgates C.output hout' (hne0_of_n0 hn0_0) hreads
    let t := unfoldTree (h := h) hN C C.output
    have ht_rows : t.rows = R₀ := by ext x; rw [hrows x]; simp [R₀, V, n]
    have ht_cols : t.cols = S₀ := by ext y; rw [hcols y]; simp [S₀, V, n]
    have ht_seeds : t.seeds = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]; intro j hj
      have : j ∈ J₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hseeds j).mp hj⟩
      have := Finset.card_pos.mpr ⟨j, this⟩; omega
    have ht_not : t.notCount = 0 := by
      rw [hnotc]
      have heq : V.filter (fun u => n ≤ u ∧ isNotOp (gateAt C (u - n)).op = true) =
          G.filter (fun u => isNotOp (gateAt C (u - n)).op = true) := by
        ext u; simp [G, Finset.mem_filter, and_assoc]
      rw [heq]; exact hnnot_0
    have harea_eq : areaC (t.eval w₀) = areaC (tableC N h C w₀) := by
      congr 1; funext x y; exact hev w₀ x y
    have hlc_t : t.lineCount = g + 1 := by
      unfold BTree.lineCount; rw [ht_rows, ht_cols]; exact hL_eq1
    have hand_zero : t.andCount = 0 := by
      by_contra hne
      have hm : 1 ≤ t.andCount := by omega
      by_cases hbig : t.hasBigAnd
      · have hle := t.area_le_of_hasBigAnd w₀ hro ht_not ht_seeds hbig
        rw [harea_eq, hlc_t] at hle
        have hg_mul : (g - 1) * N + 2 * N = (g + 1) * N := by
          have : g - 1 + 2 = g + 1 := by omega
          rw [← Nat.add_mul, this]
        omega
      · have hle := t.area_le_of_no_bigAnd w₀ hro ht_not ht_seeds hbig
        rw [harea_eq, hlc_t] at hle
        have hstep : 2 * N + (t.andCount - 1) ≤ 2 * t.andCount * N := by
          have h1 : 2 * t.andCount * N = 2 * N + 2 * (t.andCount - 1) * N := by
            have : t.andCount = 1 + (t.andCount - 1) := by omega
            conv_lhs => rw [this]
            ring
          have h2 : t.andCount - 1 ≤ 2 * (t.andCount - 1) * N := by
            calc t.andCount - 1 = (t.andCount - 1) * 1 := by ring
              _ ≤ (t.andCount - 1) * (2 * N) := Nat.mul_le_mul_left _ (by omega)
              _ = 2 * (t.andCount - 1) * N := by ring
          omega
        have hg_mul : (g - 1) * N + 2 * N = (g + 1) * N := by
          have : g - 1 + 2 = g + 1 := by omega
          rw [← Nat.add_mul, this]
        omega
    refine ⟨R₀, S₀, by omega, by omega, fun w x y => ?_⟩
    change wireVal C (inpVec w x y) C.output = _
    rw [← hev w x y, t.eval_of_no_not_no_and ht_not hand_zero ht_seeds w x y, ht_rows, ht_cols]

end ShapeLibrary
namespace Saturated33662
open ShapeLibrary PEqualNP.CircuitLowerBounds PEqualNP.Represents
theorem area_union {N : ℕ} (R S : Finset (Fin N)) :
    areaC (fun x y => decide (x ∈ R ∨ y ∈ S)) + R.card*S.card = (R.card+S.card)*N := by
  classical
  let U : Finset (Fin N) := Finset.univ
  have eq : (Finset.univ.filter fun z : Fin N × Fin N => decide (z.1 ∈ R ∨ z.2 ∈ S) = true) =
      (R ×ˢ U) ∪ (U ×ˢ S) := by ext z; simp [U]
  have inter : (R ×ˢ U) ∩ (U ×ˢ S) = R ×ˢ S := by ext z; simp [U]
  have h := Finset.card_union_add_card_inter (R ×ˢ U) (U ×ˢ S)
  rw [inter] at h
  unfold areaC
  rw [eq]
  simpa [U, Finset.card_product, Nat.add_mul, Nat.mul_add, Nat.mul_comm] using h

theorem roots (a b r s : ℕ) (hs : a+b=r+s) (hp : a*b=r*s) :
    (a=r ∧ b=s) ∨ (a=s ∧ b=r) := by
  have hs' : (a:ℤ)+b=r+s := by exact_mod_cast hs
  have hp' : (a:ℤ)*b=r*s := by exact_mod_cast hp
  have he : ((a:ℤ)-r)*(a-s)=0 := by
    nlinarith only [hp',congrArg (fun z : ℤ => (a:ℤ)*z) hs']
  rcases mul_eq_zero.mp he with h | h
  · left; omega
  · right; omega

theorem saturated {N g r s : ℕ} (hr : 0<r) (hrs : r≤s) (hgs : r+s=g+1)
    (hrN : r*s<N) (hN : 2*g+1<N) (C : Circuit) (leg : legalC N 0 C) (small : C.size≤g)
    (sat : areaC (fun x y : Fin N => C.eval (oneEach x y)) = (g+1)*N-r*s) :
    ∃ R S : Finset (Fin N), ((R.card=r ∧ S.card=s) ∨ (R.card=s ∧ S.card=r)) ∧
      ∀ x y : Fin N, C.eval (oneEach x y) = decide (x ∈ R ∨ y ∈ S) := by
  let w : Fin 0 → Bool := Fin.elim0
  have tab : tableC N 0 C w = fun x y : Fin N => C.eval (oneEach x y) := by
    funext x y; simp [tableC,inpVec,w]
  have gpos : 0<g := by omega
  have lower : (g-1)*N+1 < (g+1)*N-r*s := by
    have hx : g-1+1=g := by omega
    have hm := congrArg (fun z : ℕ => z*N) hx
    simp only [Nat.add_mul,one_mul] at hm ⊢
    omega
  have upper : (g+1)*N-r*s < N*(N-g) := by
    have h := Nat.mul_lt_mul_of_pos_left (by omega : g+1 < N-g) (by omega : 0<N)
    rw [Nat.mul_comm (g+1) N]; omega
  obtain ⟨R,S,hlo,hhi,form⟩ | ⟨_,_,j,_⟩ := part1_classification N g gpos (by omega) 0 C leg small w
    (by rwa [tab,sat]) (by rwa [tab,sat])
  · have htab : (fun x y : Fin N => C.eval (oneEach x y)) =
        (fun x y => decide (x ∈ R ∨ y ∈ S)) := by
      rw [← tab]; funext x y; exact form w x y
    have card := area_union R S
    rw [← htab,sat] at card
    have hsum : R.card+S.card=g+1 := by
      by_contra hn
      have hm := Nat.mul_le_mul_right N (by omega : R.card+S.card ≤ g)
      rw [Nat.add_mul,one_mul] at card
      omega
    rw [hsum] at card
    refine ⟨R,S,roots _ _ _ _ (by omega) ?_,fun x y => congrFun (congrFun htab x) y⟩
    rw [Nat.add_mul,one_mul] at card
    omega
  · exact Fin.elim0 j

end Saturated33662

namespace Average33662
open scoped BigOperators

theorem forced_area {I K : Type*} [Fintype I] [Fintype K]
    (area : I → ℤ) (loss : I → K → ℤ) (A base delta : ℤ)
    (positive : 0 < delta) (bound : ∀ i, area i ≤ A)
    (averaged : ∀ i, ∑ k, loss i k = base - delta * area i)
    (budget : (∑ k, ∑ i, loss i k) ≤ ∑ _i : I, (base-delta*A)) :
    ∀ i, area i = A := by
  classical
  rw [Finset.sum_comm] at budget
  simp_rw [averaged] at budget
  have allge : ∀ i : I, base - delta * A ≤ base - delta * area i := by
    intro i
    have := mul_le_mul_of_nonneg_left (bound i) positive.le
    omega
  intro i
  by_contra h
  have lt : area i < A := lt_of_le_of_ne (bound i) h
  have hmul := mul_lt_mul_of_pos_left lt positive
  have bad : (∑ _i : I, (base-delta*A)) < ∑ j : I, (base-delta*area j) :=
    Finset.sum_lt_sum (fun j _ => allge j) ⟨i,Finset.mem_univ i,by omega⟩
  exact (not_lt_of_ge budget) bad

theorem bit_loss (p t : Bool) : ((if p ≠ t then 1 else 0) : ℤ) =
    (if p then 1 else 0) + (if t then 1 else 0) -
      2*(if p && t then 1 else 0) := by cases p <;> cases t <;> decide

theorem tally {K : Type*} [Fintype K] (p : Bool) (targets : K → Bool) (t : ℤ)
    (support : (∑ k, (if targets k then 1 else 0 : ℤ)) = t) :
    (∑ k, (if p ≠ targets k then 1 else 0 : ℤ)) =
       t - (2*t-(Fintype.card K : ℤ))*(if p then 1 else 0) := by
  classical
  simp_rw [bit_loss,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  cases p <;> simp [support] <;> ring

def reg {N : ℕ} (t : ℕ) (T : Fin N → Fin N → Bool) :=
  (∀ x, (Finset.univ.filter (fun y => T x y)).card=t) ∧
  (∀ y, (Finset.univ.filter (fun x => T x y)).card=t)

def hits {Z : Type*} [Fintype Z] (p : Z → Bool) : ℕ :=
  (Finset.univ.filter (fun z => p z)).card

theorem sum_hits {Z : Type*} [Fintype Z] (p : Z → Bool) :
    (∑ z, (if p z then 1 else 0 : ℤ)) = (hits p : ℤ) := by
  simp [hits, Finset.sum_boole]

def shift {N : ℕ} [NeZero N] (T : Fin N → Fin N → Bool) (k x y : Fin N) := T (x+k) y

theorem shifted_column {N : ℕ} [NeZero N] (T : Fin N → Fin N → Bool) (y k : Fin N) :
    hits (fun x => shift T k x y) = hits (fun x => T x y) := by
  have h : (∑ x, (if T (x+k) y then 1 else 0 : ℤ)) = ∑ x, (if T x y then 1 else 0 : ℤ) :=
    Fintype.sum_equiv (Equiv.addRight k) _ _ (fun _ => rfl)
  exact_mod_cast (show (hits (fun x => shift T k x y) : ℤ) = hits (fun x => T x y) by
    simpa only [← sum_hits,shift] using h)

theorem reg_shift {N t : ℕ} [NeZero N] (T : Fin N → Fin N → Bool) (h : reg t T) (k : Fin N) :
    reg t (shift T k) := by
  refine ⟨fun x => h.1 (x+k),fun y => ?_⟩
  exact (shifted_column T y k).trans (h.2 y)

theorem avg_shift {N t : ℕ} [NeZero N] (T H : Fin N → Fin N → Bool) (h : reg t T) :
    (∑ k : Fin N, ((hits fun z : Fin N × Fin N => decide (H z.1 z.2 ≠ shift T k z.1 z.2)) : ℤ)) =
      (N : ℤ)*(N : ℤ)*t - (2*(t : ℤ)-N)*(hits fun z : Fin N × Fin N => H z.1 z.2) := by
  have support (x y : Fin N) : (∑ k : Fin N, (if shift T k x y then 1 else 0 : ℤ)) = t := by
    calc
      _ = ∑ k, (if T k y then 1 else 0 : ℤ) :=
        Fintype.sum_equiv (Equiv.addLeft x) _ _ (fun _ => rfl)
      _ = _ := by rw [sum_hits]; exact_mod_cast h.2 y
  simp_rw [← sum_hits, decide_eq_true_eq]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z : Fin N × Fin N, ((t:ℤ) - (2*(t:ℤ)-N)*(if H z.1 z.2 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro z _
      simpa only [Fintype.card_fin] using tally (H z.1 z.2) (fun k : Fin N => shift T k z.1 z.2) t (support z.1 z.2)
    _ = _ := by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]

theorem tight_budget {N M t A : ℕ} [NeZero N] (hNt : N<2*t)
    (D : Fin M → Fin N → Fin N → Bool)
    (cap : ∀ i, hits (fun z : Fin N × Fin N => D i z.1 z.2) ≤ A)
    (T : Fin N → Fin N → Bool) (hr : reg t T)
    (budget : ∀ U : Fin N → Fin N → Bool, reg t U →
      (N : ℤ) * (∑ i, ((hits fun z : Fin N × Fin N => decide (D i z.1 z.2 ≠ U z.1 z.2)) : ℤ)) ≤
        (M : ℤ) * ((N:ℤ)*N*t-(2*(t:ℤ)-N)*A)) :
    (∀ i, hits (fun z : Fin N × Fin N => D i z.1 z.2) = A) ∧
    (N : ℤ) * (∑ i, ((hits fun z : Fin N × Fin N => decide (D i z.1 z.2 ≠ T z.1 z.2)) : ℤ)) =
        (M : ℤ) * ((N:ℤ)*N*t-(2*(t:ℤ)-N)*A) := by
  let base := (N:ℤ)*N*t
  let delta := 2*(t:ℤ)-N
  let bench := base-delta*A
  let area (i : Fin M) : ℤ := hits (fun z : Fin N × Fin N => D i z.1 z.2)
  let L (i : Fin M) (k : Fin N) : ℤ := hits (fun z : Fin N × Fin N => decide (D i z.1 z.2 ≠ shift T k z.1 z.2))
  have hpos : (0:ℤ)<N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have deltaPos : 0<delta := by dsimp [delta]; omega
  have hcap (i) : area i ≤ A := by dsimp [area]; exact_mod_cast cap i
  have avg (i) : ∑ k, L i k = base-delta*area i := avg_shift T (D i) hr
  have b (k) : (N:ℤ)*(∑ i, L i k) ≤ (M:ℤ)*bench := budget _ (reg_shift T hr k)
  have bs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => b k)
  simp only [← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at bs
  have small : (∑ k, ∑ i, L i k) ≤ (M:ℤ)*bench := by
    by_contra! bad
    nlinarith only [bs,mul_pos hpos (sub_pos.mpr bad)]
  have rhs : (∑ _i : Fin M, bench) = (M:ℤ)*bench := by simp
  have same := forced_area area L (A:ℤ) base delta deltaPos hcap avg (rhs.symm ▸ small)
  refine ⟨fun i => (Int.ofNat_inj).mp (same i), ?_⟩
  have eqsum : (∑ k, ∑ i, L i k) = (M:ℤ)*bench := by
    rw [Finset.sum_comm]
    simpa only [avg,same] using rhs
  have eq : (∑ k, (N:ℤ)*(∑ i, L i k)) = ∑ _k : Fin N, (M:ℤ)*bench := by
    simp only [← Finset.mul_sum,eqsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have every := (Finset.sum_eq_sum_iff_of_le (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) => b k)).mp eq
  simpa [L,shift,bench,base,delta] using every 0 (Finset.mem_univ _)
end Average33662

namespace ExactShape33662
open PEqualNP.CircuitLowerBounds PEqualNP.Represents Average33662

lemma circulant_reg {N t : ℕ} (ht : t < N) :
    let T0 : Fin N → Fin N → Bool := fun a b => decide ((b.val + N - a.val) % N < t)
    (∀ x, (Finset.univ.filter (fun y => T0 x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T0 x y)).card = t) := by
  intro T0
  have hN : 0 < N := by omega
  constructor
  · intro x
    let f : Fin t → Fin N := fun k => ⟨(x.val + k.val) % N, Nat.mod_lt _ hN⟩
    have hf_inj : Function.Injective f := by
      intro k₁ k₂ h
      have hv := congrArg Fin.val h
      simp only [f] at hv
      have h1 := k₁.isLt
      have h2 := k₂.isLt
      have hx := x.isLt
      apply Fin.ext
      by_cases hlt1 : x.val + k₁.val < N <;> by_cases hlt2 : x.val + k₂.val < N
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    have hfilt : Finset.univ.filter (fun y => T0 x y) = Finset.univ.image f := by
      ext y
      simp only [T0, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_image]
      constructor
      · intro hy
        let k : Fin t := ⟨(y.val + N - x.val) % N, hy⟩
        refine ⟨k, ?_⟩
        apply Fin.ext
        simp only [f, k]
        have hx := x.isLt
        have hylt := y.isLt
        by_cases hxy : x.val ≤ y.val
        · have hsub : (y.val + N - x.val) % N = y.val - x.val := by
            have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub]
          have h2 : x.val + (y.val - x.val) = y.val := by omega
          rw [h2, Nat.mod_eq_of_lt hylt]
        · have hsub : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
          rw [hsub]
          have h2 : x.val + (y.val + N - x.val) = y.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hylt]
      · rintro ⟨k, rfl⟩
        have hx := x.isLt
        have hk := k.isLt
        simp only [f]
        by_cases hlt : x.val + k.val < N
        · rw [Nat.mod_eq_of_lt hlt]
          have h1 : x.val + k.val + N - x.val = k.val + N := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          exact hk
        · have hmod : (x.val + k.val) % N = x.val + k.val - N := by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have h1 : x.val + k.val - N + N - x.val = k.val := by omega
          rw [h1, Nat.mod_eq_of_lt (by omega)]
          exact hk
    rw [hfilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  · intro y
    let f : Fin t → Fin N := fun k => ⟨(y.val + N - k.val) % N, Nat.mod_lt _ hN⟩
    have hf_inj : Function.Injective f := by
      intro k₁ k₂ h
      have hv := congrArg Fin.val h
      simp only [f] at hv
      have h1 := k₁.isLt
      have h2 := k₂.isLt
      have hy := y.isLt
      apply Fin.ext
      by_cases hlt1 : k₁.val ≤ y.val <;> by_cases hlt2 : k₂.val ≤ y.val
      · have e1 : y.val + N - k₁.val = (y.val - k₁.val) + N := by omega
        have e2 : y.val + N - k₂.val = (y.val - k₂.val) + N := by omega
        rw [e1, e2, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e1 : y.val + N - k₁.val = (y.val - k₁.val) + N := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e2 : y.val + N - k₂.val = (y.val - k₂.val) + N := by omega
        rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    have hfilt : Finset.univ.filter (fun x => T0 x y) = Finset.univ.image f := by
      ext x
      simp only [T0, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_image]
      constructor
      · intro hx
        let k : Fin t := ⟨(y.val + N - x.val) % N, hx⟩
        refine ⟨k, ?_⟩
        apply Fin.ext
        simp only [f, k]
        have hxlt := x.isLt
        have hylt := y.isLt
        by_cases hxy : x.val ≤ y.val
        · have hsub : (y.val + N - x.val) % N = y.val - x.val := by
            have h1 : y.val + N - x.val = (y.val - x.val) + N := by omega
            rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hsub]
          have h2 : y.val + N - (y.val - x.val) = x.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hxlt]
        · have hsub : (y.val + N - x.val) % N = y.val + N - x.val := Nat.mod_eq_of_lt (by omega)
          rw [hsub]
          have h2 : y.val + N - (y.val + N - x.val) = x.val := by omega
          rw [h2, Nat.mod_eq_of_lt hxlt]
      · rintro ⟨k, rfl⟩
        have hy := y.isLt
        have hk := k.isLt
        simp only [f]
        by_cases hle : k.val ≤ y.val
        · have hmod : (y.val + N - k.val) % N = y.val - k.val := by
            have e1 : y.val + N - k.val = (y.val - k.val) + N := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have h2 : y.val + N - (y.val - k.val) = k.val + N := by omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          exact hk
        · have hmod : (y.val + N - k.val) % N = y.val + N - k.val := Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          have h2 : y.val + N - (y.val + N - k.val) = k.val := by omega
          rw [h2, Nat.mod_eq_of_lt (by omega)]
          exact hk
    rw [hfilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]

theorem all_shapes {N M g r s t : ℕ} (hr : 0<r) (hrs : r≤s) (hgs : r+s=g+1)
    (hprod : r*s<N) (hNg : 2*g+1<N) (hNt : N<2*t) (ht : t<N)
    (D : Fin M → Circuit)
    (fits : ∀ i, PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) (D i) ∧
      (D i).output < N+N+(D i).size ∧ (∀ gate ∈ (D i).gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      (D i).size ≤ g ∧ (hits fun z : Fin N × Fin N => (D i).eval (oneEach z.1 z.2)) ≤ (g+1)*N-r*s)
    (good : ∀ T : Fin N → Fin N → Bool, reg t T →
      N*(∑ i, hits fun z : Fin N × Fin N => decide ((D i).eval (oneEach z.1 z.2) ≠ T z.1 z.2)) ≤
      M*(N*(N*t)-(2*t-N)*((g+1)*N-r*s))) :
    ∀ i, ∃ R S : Finset (Fin N), ((R.card=r ∧ S.card=s) ∨ (R.card=s ∧ S.card=r)) ∧
      ∀ x y : Fin N, (D i).eval (oneEach x y)=decide (x ∈ R ∨ y ∈ S) := by
  letI : NeZero N := ⟨by omega⟩
  let A := (g+1)*N-r*s
  let H (i : Fin M) (x y : Fin N) := (D i).eval (oneEach x y)
  have ha : A ≤ N*N := le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_right N (by omega))
  have hbench : (2*t-N)*A ≤ N*(N*t) := calc
    _ ≤ t*(N*N) := Nat.mul_le_mul (by omega) ha
    _ = _ := by ring
  let T : Fin N → Fin N → Bool := fun x y => decide ((y.val+N-x.val)%N<t)
  have hT : reg t T := circulant_reg ht
  have b (U : Fin N → Fin N → Bool) (hU : reg t U) :
      (N : ℤ) * (∑ i, ((hits fun z : Fin N × Fin N => decide (H i z.1 z.2 ≠ U z.1 z.2)) : ℤ)) ≤
        (M : ℤ) * ((N:ℤ)*N*t-(2*(t:ℤ)-N)*A) := by
    have h := (Int.ofNat_le).mpr (good U hU)
    change ((N * (∑ i, hits fun z : Fin N × Fin N => decide (H i z.1 z.2 ≠ U z.1 z.2)) : ℕ) : ℤ) ≤
      ((M*(N*(N*t)-(2*t-N)*A) : ℕ) : ℤ) at h
    simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_sub hbench,Nat.cast_sub (by omega : N≤2*t),
      Nat.cast_ofNat,mul_assoc] using h
  have uniform := (tight_budget hNt H (fun i => (fits i).2.2.2.2) T hT b).1
  intro i
  obtain ⟨rb,out,ops,size,_⟩ := fits i
  apply Saturated33662.saturated hr hrs hgs hprod hNg (D i) _ size (uniform i)
  refine ⟨rb,out,fun gate hg => ?_⟩
  have h := ops gate hg
  exact ⟨h.1,by rcases h.2 with o|a|n; exact Or.inr (Or.inl o); exact Or.inl a; exact Or.inr (Or.inr n)⟩
end ExactShape33662

namespace Average33662
def total {N M : ℕ} (D : Fin M → Fin N → Fin N → Bool) (T : Fin N → Fin N → Bool) : ℕ :=
  ∑ i, hits (fun z : Fin N × Fin N => decide (D i z.1 z.2 ≠ T z.1 z.2))

theorem uniform_iff {N M t A : ℕ} [NeZero N] (hNt : N<2*t) (ht : t<N) (hA : A≤N*N)
    (D : Fin M → Fin N → Fin N → Bool)
    (full : ∀ i, hits (fun z : Fin N × Fin N => D i z.1 z.2)=A) :
    (∀ T, reg t T → N*total D T ≤ M*(N*(N*t)-(2*t-N)*A)) ↔
      ∀ T U, reg t T → reg t U → total D T = total D U := by
  let B := (N:ℤ)*N*t-(2*(t:ℤ)-N)*A
  have bpos : (2*t-N)*A ≤ N*(N*t) := calc
    _ ≤ t*(N*N) := Nat.mul_le_mul (by omega) hA
    _ = _ := by ring
  have bc : ((N*(N*t)-(2*t-N)*A : ℕ) : ℤ) = B := by
    simp only [B,Nat.cast_sub bpos,Nat.cast_mul,Nat.cast_sub (by omega : N≤2*t),Nat.cast_ofNat,mul_assoc]
  let Z := fun T : Fin N → Fin N → Bool => (total D T : ℤ)
  have cast (T) : Z T = ∑ i, ((hits fun z : Fin N × Fin N => decide (D i z.1 z.2 ≠ T z.1 z.2)) : ℤ) := by
    simp [Z,total]
  have order (T) : N*total D T ≤ M*(N*(N*t)-(2*t-N)*A) ↔ (N:ℤ)*Z T ≤ (M:ℤ)*B := by
    change _ ↔ (N:ℤ)*(total D T : ℤ) ≤ (M:ℤ)*B
    rw [← bc]; norm_cast
  constructor
  · intro budget
    have zbound (T) (hT : reg t T) := (order T).mp (budget T hT)
    have equal (T) (hT : reg t T) : (N:ℤ)*Z T = (M:ℤ)*B := by
      rw [cast]
      apply (tight_budget hNt D (fun i => (full i).le) T hT ?_).2
      intro U hU
      simpa only [← cast] using zbound U hU
    intro T U hT hU
    have h := (equal T hT).trans (equal U hU).symm
    have hn : (N:ℤ)≠0 := by exact_mod_cast NeZero.ne N
    exact Int.ofNat_inj.mp (mul_left_cancel₀ hn h)
  · intro constant T hT
    apply (order T).mpr
    have same (k : Fin N) : Z (shift T k) = Z T := by
      exact congrArg (fun n : ℕ => (n:ℤ)) (constant _ _ (reg_shift T hT k) hT)
    have running : (∑ k : Fin N, Z (shift T k)) = (M:ℤ)*B := by
      simp_rw [cast]
      rw [Finset.sum_comm]
      have h (i) := avg_shift T (D i) hT
      simp_rw [h, full]
      simp [B,mul_sub]
    simpa only [same,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using running.le
end Average33662

namespace Overlap33662
def w (b : Bool) : ℕ := if b then 1 else 0

theorem pointwise : ∀ p q t : Bool,
    w (decide ((p || q) ≠ t)) + 2*(w (p && t)+w (q && t)) =
    w (p || q) + w t + 2*w (p && q && t) := by decide

private theorem sum_w {X : Type*} [Fintype X] (v : X → Bool) :
    (∑ x, w (v x)) = (Finset.univ.filter (fun x => v x)).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rfl

theorem identity {X : Type*} [Fintype X] [DecidableEq X] (P Q : Finset X)
    (T : X → X → Bool) (t : ℕ)
    (row : ∀ x, (Finset.univ.filter (fun y => T x y)).card = t)
    (col : ∀ y, (Finset.univ.filter (fun x => T x y)).card = t) :
    let L := fun x y => decide (x ∈ P ∨ y ∈ Q)
    (∑ x, ∑ y, w (decide (L x y ≠ T x y))) + 2*((P.card+Q.card)*t) =
      (∑ x, ∑ y, w (L x y)) + Fintype.card X*t +
      2*(∑ x, ∑ y, w (decide (x ∈ P) && decide (y ∈ Q) && T x y)) := by
  classical
  dsimp only
  have sumrows : (∑ x, ∑ y, w (decide (x ∈ P) && T x y)) = P.card*t := by
    calc
      _ = ∑ x, if x ∈ P then t else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases h : x ∈ P
        · simp [h,sum_w,row]
        · simp [h,w]
      _ = _ := by simp
  have sumcols : (∑ x, ∑ y, w (decide (y ∈ Q) && T x y)) = Q.card*t := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ y, if y ∈ Q then t else 0 := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases h : y ∈ Q
        · simp [h,sum_w,col]
        · simp [h,w]
      _ = _ := by simp
  have total : (∑ x, ∑ y, w (T x y)) = Fintype.card X * t := by
    simp_rw [sum_w,row]
    simp
  have summed := Finset.sum_congr (rfl : (Finset.univ : Finset X) = Finset.univ) (fun x _ =>
    Finset.sum_congr (rfl : (Finset.univ : Finset X) = Finset.univ) (fun y _ =>
      pointwise (decide (x ∈ P)) (decide (y ∈ Q)) (T x y)))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, sumrows, sumcols, total,
    Nat.add_mul, Bool.decide_or] using summed

theorem aggregate {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (R S : I → Finset X) (T : X → X → Bool) (t : ℕ)
    (row : ∀ x, (Finset.univ.filter (fun y => T x y)).card=t)
    (col : ∀ y, (Finset.univ.filter (fun x => T x y)).card=t) :
    let H := fun i (z : X × X) => decide (z.1 ∈ R i ∨ z.2 ∈ S i)
    let cost := ∑ x, ∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0
    (∑ i, (Finset.univ.filter (fun z : X × X => H i z ≠ T z.1 z.2)).card) +
      ∑ i, 2*(((R i).card+(S i).card)*t) =
      (∑ i, (Finset.univ.filter (fun z : X × X => H i z)).card) +
      Fintype.card I*(Fintype.card X*t) + 2*cost := by
  classical
  dsimp only
  have h := Finset.sum_congr (rfl : (Finset.univ : Finset I) = Finset.univ)
    (fun i _ => identity (R i) (S i) T t row col)
  have layer (x y : X) : (∑ i, w (decide (x ∈ R i) && decide (y ∈ S i) && T x y)) =
      if T x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0 := by
    cases h : T x y <;> simp [w,h,Finset.sum_boole]
  have sums : (∑ i, ∑ x, ∑ y, w (decide (x ∈ R i) && decide (y ∈ S i) && T x y)) =
      ∑ x, ∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => layer x y)
  have grid (p : X × X → Bool) :
      (∑ x, ∑ y, w (p (x,y))) = (Finset.univ.filter (fun z => p z)).card := by
    exact (Fintype.sum_prod_type (fun z : X × X => w (p z))).symm.trans (sum_w p)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,sums,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  have loss (i) : (∑ x, ∑ y, w (decide (decide (x ∈ R i ∨ y ∈ S i) ≠ T x y))) =
     (Finset.univ.filter (fun z : X × X => decide (z.1 ∈ R i ∨ z.2 ∈ S i) ≠ T z.1 z.2)).card := by
    simpa only [decide_eq_true_eq] using grid (fun z => decide (decide (z.1 ∈ R i ∨ z.2 ∈ S i) ≠ T z.1 z.2))
  have area (i) := grid (fun z => decide (z.1 ∈ R i ∨ z.2 ∈ S i))
  simp only [loss,area] at h
  rw [Nat.mul_left_comm (Fintype.card I) (Fintype.card X) t]
  simpa only [← Finset.mul_sum, Nat.cast_id] using h

theorem comparison {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I]
    (R S : I → Finset X) (T U : X → X → Bool) (t : ℕ)
    (rT : ∀ x, (Finset.univ.filter (fun y => T x y)).card=t)
    (cT : ∀ y, (Finset.univ.filter (fun x => T x y)).card=t)
    (rU : ∀ x, (Finset.univ.filter (fun y => U x y)).card=t)
    (cU : ∀ y, (Finset.univ.filter (fun x => U x y)).card=t) :
    let H := fun i (z : X × X) => decide (z.1 ∈ R i ∨ z.2 ∈ S i)
    let loss := fun V : X → X → Bool => ∑ i, (Finset.univ.filter (fun z : X × X => H i z ≠ V z.1 z.2)).card
    let cost := fun V : X → X → Bool => ∑ x, ∑ y, if V x y then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0
    loss T = loss U ↔ cost T = cost U := by
  have a := aggregate R S T t rT cT
  have b := aggregate R S U t rU cU
  dsimp only at a b ⊢
  omega
end Overlap33662
namespace Decoder33662
open PEqualNP.CircuitLowerBounds PEqualNP.Represents Average33662

def tab {N : ℕ} (C : Circuit) (x y : Fin N) := C.eval (oneEach x y)
def area (N g r s : ℕ) := (g+1)*N-r*s
def dims {N : ℕ} (r s : ℕ) (P Q : Finset (Fin N)) :=
  (P.card=r ∧ Q.card=s) ∨ (P.card=s ∧ Q.card=r)
def shape {N : ℕ} (C : Circuit) (P Q : Finset (Fin N)) :=
  ∀ x y, tab C x y = decide (x ∈ P ∨ y ∈ Q)
def fit {N : ℕ} (g A : ℕ) (C : Circuit) := PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧
  C.output<N+N+C.size ∧ (∀ gate∈C.gates, gate.inputs.length≤2 ∧
    (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length=1))) ∧ C.size≤g ∧
  hits (fun z : Fin N × Fin N => tab C z.1 z.2) ≤ A
def budget {N M : ℕ} (t A : ℕ) (D : Fin M → Circuit) :=
  ∀ T, reg t T → N*total (fun i => @tab N (D i)) T ≤ M*(N*(N*t)-(2*t-N)*A)
def good {N M : ℕ} (g t A : ℕ) (D : Fin M → Circuit) :=
  (∀ i, @fit N g A (D i)) ∧ @budget N M t A D
def flat {N M : ℕ} (t : ℕ) (R S : Fin M → Finset (Fin N)) :=
  let cost := fun V : Fin N → Fin N → Bool => ∑ x, ∑ y, if V x y then
    (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0
  ∀ T U, reg t T → reg t U → cost T = cost U

theorem exact_area {N g r s : ℕ} (hs : r+s=g+1) (C : Circuit) (P Q : Finset (Fin N))
    (dim : dims r s P Q) (form : shape C P Q) :
    hits (fun z : Fin N × Fin N => tab C z.1 z.2) = area N g r s := by
  have eq := Saturated33662.area_union P Q
  have htab : @tab N C = fun x y => decide (x∈P ∨ y∈Q) := funext fun x => funext (form x)
  rw [htab]
  change ShapeLibrary.areaC (fun x y : Fin N => decide (x∈P ∨ y∈Q)) = (g+1)*N-r*s
  rcases dim with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · rw [hp,hq,hs] at eq
    omega
  · rw [hp,hq,Nat.add_comm s r,hs,Nat.mul_comm s r] at eq
    omega

theorem shape_budget {N M g t r s : ℕ} [NeZero N] (hs : r+s=g+1) (hg : g+1≤N)
    (hNt : N<2*t) (ht : t<N) (D : Fin M → Circuit) (R S : Fin M → Finset (Fin N))
    (dim : ∀ i, dims r s (R i) (S i)) (forms : ∀ i, shape (D i) (R i) (S i)) :
    @budget N M t (area N g r s) D ↔ flat t R S := by
  have ha : area N g r s ≤ N*N := le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_right N hg)
  unfold budget
  rw [uniform_iff hNt ht ha _ (fun i => exact_area hs (D i) _ _ (dim i) (forms i))]
  have eq (T U : Fin N → Fin N → Bool) (a : reg t T) (b : reg t U) :=
    Overlap33662.comparison R S T U t a.1 a.2 b.1 b.2
  have htab (i) : @tab N (D i) = fun x y => decide (x∈R i ∨ y∈S i) :=
    funext fun x => funext (forms i x)
  simp only [total, hits, htab, decide_eq_true_eq]
  constructor
  · intro h T U a b
    exact (eq T U a b).mp (h T U a b)
  · intro h T U a b
    exact (eq T U a b).mpr (h T U a b)

theorem good_rectangles {N M g t r s : ℕ} (hr : 0<r) (hrs : r≤s) (hs : r+s=g+1)
    (hprod : r*s<N) (hNg : 2*g+1<N) (hNt : N<2*t) (ht : t<N) (D : Fin M → Circuit)
    (hD : @good N M g t (area N g r s) D) :
    ∃ R S : Fin M → Finset (Fin N), (∀ i, dims r s (R i) (S i)) ∧
      (∀ i, shape (D i) (R i) (S i)) ∧ flat t R S := by
  letI : NeZero N := ⟨by omega⟩
  have h := ExactShape33662.all_shapes hr hrs hs hprod hNg hNt ht D hD.1 hD.2
  choose R S dim form using h
  exact ⟨R,S,dim,form,(shape_budget hs (by omega) hNt ht D R S dim form).mp hD.2⟩
end Decoder33662

namespace EvaluationLibrary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

end EvaluationLibrary

namespace Construct33662
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents EvaluationLibrary PEqualNP.MetaComplexity.NestedCover
private theorem oneEach_len {n m : ℕ} (i : Fin n) (j : Fin m) :
    (oneEach i j).length = n + m := by simp [oneEach]

private theorem oneEach_read {n m : ℕ} (i : Fin n) (j : Fin m) (k : ℕ) :
    (oneEach i j).getD k false = decide (k = i.val ∨ k = n + j.val) := by
  by_cases hkn : k < n
  · rw [oneEach, getD_app_lt _ _ _ (by simpa using hkn), ofFn_getD _ _ hkn]
    have hne : k ≠ n + j.val := by omega
    simp [hne, Fin.ext_iff]
  · rw [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simpa using (show n ≤ k by omega))]
    simp only [List.length_ofFn]
    rw [← List.getD_eq_getElem?_getD]
    have hne : k ≠ i.val := by omega
    by_cases h : k - n < m
    · rw [ofFn_getD _ _ h]
      simp only [Fin.ext_iff, hne, false_or]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      omega
    · rw [ofFn_getD_ge _ _ (by omega)]
      simp only [hne, false_or]
      symm
      apply decide_eq_false
      omega

private def wire (k : ℕ) : Circuit := ⟨[], k⟩

private def addGate (N : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a,b]⟩], N+C.size⟩

private theorem wire_size (k : ℕ) : (wire k).size = 0 := rfl

private theorem wire_mono (k : ℕ) : Monotone2 (wire k) := by simp [wire, Monotone2]

private theorem wire_read (k : ℕ) (x : List Bool) : val (wire k) x k = x.getD k false := rfl

private theorem add_size (N : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate N C op a b).size = C.size+1 := by simp [addGate, Circuit.size]

private theorem add_mono {N : ℕ} {C : Circuit} (a b : ℕ) (h : Monotone2 C) (op : GateOp)
    (ho : op = .and ∨ op = .or) : Monotone2 (addGate N C op a b) := by
  intro g hg
  simp only [addGate, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact h g hg
  · simpa using ho

private theorem add_read {N : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool)
    (hx : x.length = N) :
    val (addGate N C op a b) x (N+C.size) = op.eval [val C x a, val C x b] := by
  have hidx : N+C.size = x.length+C.gates.length := by rw [hx]; rfl
  change (W (C.gates ++ [⟨op, [a,b]⟩]) x).getD (N+C.size) false = _
  rw [hidx, W_snoc_getD, if_pos rfl]
  rfl

private theorem add_preserve {N : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ) (x : List Bool)
    (hx : x.length = N) (u : ℕ) (hu : u < N+C.size) :
    val (addGate N C op a b) x u = val C x u := by
  change (W (C.gates ++ [⟨op, [a,b]⟩]) x).getD u false = _
  rw [W_snoc_getD, ite_eq_right (by change u ≠ x.length + C.size; omega)]
  rfl

private def orStep (N : ℕ) (C : Circuit) (u : ℕ) : Circuit := addGate N C .or C.output u

private def orFrom (N : ℕ) (C : Circuit) (k : ℕ) (l : List ℕ) : Circuit :=
  l.foldl (orStep N) { C with output := k }

private theorem orFrom_size (N : ℕ) (C : Circuit) (k : ℕ) (l : List ℕ) :
    (orFrom N C k l).size = C.size + l.length := by
  induction l generalizing C k with
  | nil => simp [orFrom, Circuit.size]
  | cons u l ih =>
    change (orFrom N (orStep N { C with output := k } u) (N+C.size) l).size = _
    rw [ih, orStep, add_size]
    simp only [List.length_cons]
    change C.size + 1 + l.length = _
    omega

private theorem orFrom_mono {N : ℕ} {C : Circuit} (k : ℕ) (l : List ℕ) (h : Monotone2 C) :
    Monotone2 (orFrom N C k l) := by
  induction l generalizing C k with
  | nil => exact h
  | cons u l ih =>
    change Monotone2 (orFrom N (orStep N { C with output := k } u) (N+C.size) l)
    exact ih _ (add_mono _ _ h _ (Or.inr rfl))

private theorem orFrom_preserve {N : ℕ} (C : Circuit) (k : ℕ) (l : List ℕ) (x : List Bool)
    (hx : x.length = N) (u : ℕ) (hu : u < N+C.size) : val (orFrom N C k l) x u = val C x u := by
  induction l generalizing C k with
  | nil => rfl
  | cons v l ih =>
    change val (orFrom N (orStep N { C with output := k } v) (N+C.size) l) x u = _
    rw [ih _ _ (by rw [orStep, add_size]; change u < N+(C.size+1); omega)]
    exact add_preserve _ _ _ _ _ hx _ hu

private theorem orFrom_bound {N : ℕ} (C : Circuit) (k : ℕ) (l : List ℕ) (hk : k < N+C.size) :
    (orFrom N C k l).output < N+(orFrom N C k l).size := by
  induction l generalizing C k with
  | nil => exact hk
  | cons v l ih =>
    change (orFrom N (orStep N { C with output := k } v) (N+C.size) l).output < _
    apply ih
    rw [orStep, add_size]
    change N+C.size < N+(C.size+1)
    omega

private theorem orFrom_read {N : ℕ} (C : Circuit) (k : ℕ) (l : List ℕ) (x : List Bool)
    (hx : x.length = N) (hl : ∀ u ∈ l, u < N) :
    (orFrom N C k l).eval x = (val C x k || l.any (fun u => x.getD u false)) := by
  induction l generalizing C k with
  | nil => simp [orFrom, eval_eq_val]; rfl
  | cons v l ih =>
    change (orFrom N (orStep N { C with output := k } v) (N+C.size) l).eval x = _
    rw [ih _ _ (fun u hu => hl u (by simp [hu]))]
    have he := (add_read ({ C with output := k }) .or k v x hx).trans (eval_or2 _ _)
    change val (orStep N { C with output := k } v) x (N+C.size) =
      ((val C x k) || (val C x v)) at he
    rw [he, val_input hx (hl v (by simp))]
    exact Bool.or_assoc _ _ _

private def group (N : ℕ) (C : Circuit) (l : List ℕ) : Circuit :=
  orFrom N C (l.headD 0) l.tail

private theorem group_size (N : ℕ) (C : Circuit) (l : List ℕ) :
    (group N C l).size = C.size + (l.length-1) := by simp [group, orFrom_size]

private theorem group_mono {N : ℕ} {C : Circuit} (l : List ℕ) (hC : Monotone2 C) :
    Monotone2 (group N C l) := orFrom_mono _ _ hC

private theorem group_preserve {N : ℕ} (C : Circuit) (l : List ℕ) (x : List Bool)
    (hx : x.length = N) (u : ℕ) (hu : u < N+C.size) : val (group N C l) x u = val C x u :=
  orFrom_preserve C _ _ x hx u hu

private theorem group_valid {N : ℕ} (C : Circuit) (l : List ℕ) (hn : l ≠ [])
    (hl : ∀ k ∈ l, k < N) : (group N C l).output < N+(group N C l).size := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons v l =>
    apply orFrom_bound
    change v < N+C.size
    have := hl v (by simp)
    omega

private theorem group_eval {N : ℕ} (C : Circuit) (l : List ℕ) (hn : l ≠ [])
    (hl : ∀ k ∈ l, k < N) (x : List Bool) (hx : x.length = N) :
    (group N C l).eval x = l.any (fun k => x.getD k false) := by
  cases l with
  | nil => exact (hn rfl).elim
  | cons v l =>
    change (orFrom N C v l).eval x = _
    rw [orFrom_read C v l x hx (fun k hk => hl k (by simp [hk])), val_input hx (hl v (by simp))]
    rfl

private noncomputable def names {d : ℕ} (offset : ℕ) (S : Finset (Fin d)) : List ℕ :=
  S.toList.map fun i => offset+i.val

private theorem names_len {d : ℕ} (offset : ℕ) (S : Finset (Fin d)) :
    (names offset S).length = S.card := by simp [names]

private theorem names_ne {d : ℕ} (offset : ℕ) {S : Finset (Fin d)} (h : S.Nonempty) : names offset S ≠ [] := by
  intro he
  have h1 := names_len offset S
  rw [he] at h1
  exact (Nat.ne_of_gt (Finset.card_pos.mpr h)) h1.symm

private theorem names_bound {d : ℕ} (offset : ℕ) (S : Finset (Fin d)) (k : ℕ) (hk : k ∈ names offset S) :
    k < offset+d := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
  have := i.isLt
  omega

private theorem names_rows {n m p q : ℕ} (S : Finset (Fin n)) (i : Fin (n+p)) (j : Fin (m+q)) :
    (names 0 S).any (fun k => (oneEach i j).getD k false) =
      decide (∃ a ∈ S, a.val = i.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, names, List.mem_map, Finset.mem_toList, oneEach_read, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hh⟩
    refine ⟨a, ha, ?_⟩
    have := a.isLt
    omega
  · rintro ⟨a, ha, h⟩
    exact ⟨0+a.val, ⟨a, ha, rfl⟩, Or.inl (by simpa using h)⟩

private theorem names_cols {n m p q : ℕ} (S : Finset (Fin m)) (i : Fin (n+p)) (j : Fin (m+q)) :
    (names (n+p) S).any (fun k => (oneEach i j).getD k false) =
      decide (∃ a ∈ S, a.val = j.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, names, List.mem_map, Finset.mem_toList, oneEach_read, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, hh⟩
    refine ⟨a, ha, ?_⟩
    have := i.isLt
    omega
  · rintro ⟨a, ha, h⟩
    exact ⟨n+p+a.val, ⟨a, ha, rfl⟩, Or.inr (by rw [h])⟩

private theorem append_or_reads {n : ℕ} (C : Circuit) (a b : ℕ) (h : ReadsBack n C)
    (ha : a<n+C.size) (hb : b<n+C.size) : ReadsBack n (addGate n C .or a b) := by
  intro j hj i hi
  by_cases old : j<C.gates.length
  · have eq : gateAt (addGate n C .or a b) j = gateAt C j := by
      simp [gateAt,addGate,List.getD_eq_getElem?_getD,List.getElem?_append_left old]
    rw [eq] at hi
    exact h j old i hi
  · have eqj : j=C.gates.length := by
      change j<(C.gates++[_]).length at hj
      simp at hj; omega
    subst j
    simp [gateAt,addGate,List.getD_eq_getElem?_getD] at hi
    rcases hi with rfl|rfl <;> assumption

private theorem earlier {n : ℕ} (C : Circuit) (a : ℕ) (l : List ℕ) (h : ReadsBack n C)
    (ha : a<n+C.size) (hl : ∀ j∈l, j<n) : ReadsBack n (orFrom n C a l) := by
  induction l generalizing C a with
  | nil => exact h
  | cons b l ih =>
    change ReadsBack n (orFrom n (orStep n {C with output:=a} b) (n+C.size) l)
    apply ih
    · exact append_or_reads {C with output := a} a b h ha (by have := hl b (by simp); change b<n+C.size; omega)
    · rw [orStep,add_size]; change n+C.size<n+(C.size+1); omega
    · exact fun j hj => hl j (by simp [hj])

theorem construct {N : ℕ} (P Q : Finset (Fin N)) (hp : P.Nonempty) :
    ∃ C : Circuit, ReadsBack (N+N) C ∧ C.output<N+N+C.size ∧ Monotone2 C ∧
      C.size=P.card+Q.card-1 ∧
      ∀ x y : Fin N, C.eval (oneEach x y)=decide (x ∈ P ∨ y ∈ Q) := by
  let l := names 0 P ++ names N Q
  have llen : l.length=P.card+Q.card := by simp [l,names_len]
  have pos := Finset.card_pos.mpr hp
  have hn : l≠[] := by intro he; rw [he] at llen; simp at llen; omega
  have hl (k) (hk : k∈l) : k<N+N := by
    rcases List.mem_append.mp hk with hk|hk
    · have := names_bound 0 P k hk; omega
    · exact names_bound N Q k hk
  let C := group (N+N) (wire 0) l
  refine ⟨C, ?_, group_valid _ _ hn hl,group_mono _ (wire_mono 0), ?_, ?_⟩
  · apply earlier
    · intro j hj; exact False.elim (Nat.not_lt_zero _ hj)
    · have := hl (l.headD 0) (by cases h : l with | nil => contradiction | cons a as => simp)
      simpa [wire_size] using this
    · intro j hj
      exact hl j (List.mem_of_mem_tail hj)
  · simp [C,group_size,wire_size,llen]
  · intro x y
    rw [show C=group (N+N) (wire 0) l from rfl,group_eval _ _ hn hl _ (oneEach_len x y)]
    rw [show l=names 0 P ++ names N Q from rfl,List.any_append]
    have row := @names_rows N N 0 0 P x y
    have col := @names_cols N N 0 0 Q x y
    simp only [Nat.add_zero] at col
    rw [row,col]
    apply Bool.eq_iff_iff.mpr
    simp [← Fin.ext_iff]
end Construct33662

namespace FixedBlocks33662
open scoped BigOperators

theorem block {N r s : ℕ} (hr0 : 0 < r) (hrN : r ≤ N) (hsN : s ≤ N) :
    let d := N/Nat.gcd N r
    ∃ (P : Finset (Fin N)) (R : Fin d → Finset (Fin N)), P.card=s ∧
      (∀ i, (R i).card=r) ∧ ∀ x, (Finset.univ.filter (fun i => x ∈ R i)).card = r/Nat.gcd N r := by
  intro d
  have hN : 0 < N := by omega
  let g := Nat.gcd N r
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left r hN
  have hgN : g ∣ N := Nat.gcd_dvd_left N r
  have hgr : g ∣ r := Nat.gcd_dvd_right N r
  have hdg : d * g = N := Nat.div_mul_cancel hgN
  let S0 : Finset (Fin N) := Finset.univ.filter (fun y : Fin N => y.val < s)
  have hS0_card : S0.card = s := by
    let emb : Fin s → Fin N := fun j => ⟨j.val, by omega⟩
    have heq : S0 = Finset.univ.image emb := by
      ext y
      simp only [S0, emb, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨fun hy => ⟨⟨y.val, hy⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.isLt⟩
    have hemb_inj : Function.Injective emb := fun j₁ j₂ h =>
      Fin.ext (by simpa [emb] using congrArg Fin.val h)
    rw [heq, Finset.card_image_of_injective _ hemb_inj, Finset.card_univ, Fintype.card_fin]
  let R : Fin d → Finset (Fin N) := fun i =>
    (Finset.univ : Finset (Fin r)).image (fun k => ⟨(i.val * g + k.val) % N, Nat.mod_lt _ hN⟩)
  have hR_card : ∀ i : Fin d, (R i).card = r := by
    intro i
    have hinj : Function.Injective (fun k : Fin r => (⟨(i.val * g + k.val) % N, Nat.mod_lt _ hN⟩ : Fin N)) := by
      intro k₁ k₂ h
      have hv := congrArg Fin.val h
      simp only at hv
      have h1 := k₁.isLt
      have h2 := k₂.isLt
      have hi : i.val * g < N := by
        have hle : (i.val + 1) * g ≤ d * g := Nat.mul_le_mul_right g i.isLt
        rw [add_mul, one_mul, hdg] at hle; omega
      apply Fin.ext
      by_cases hlt1 : i.val * g + k₁.val < N <;> by_cases hlt2 : i.val * g + k₂.val < N
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hlt2] at hv; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hR_cov : ∀ x : Fin N, (Finset.univ.filter (fun i : Fin d => x ∈ R i)).card = r / g := by
    intro x
    let rg := r / g
    have hrg : rg * g = r := Nat.div_mul_cancel hgr
    have hd_pos : 0 < d := Nat.pos_of_ne_zero (fun h0 => by rw [h0, zero_mul] at hdg; omega)
    let f : Fin rg → Fin d := fun q =>
      ⟨((x.val / g + d - q.val) % d), Nat.mod_lt _ hd_pos⟩
    have hrg_le : rg ≤ d := by
      have : rg * g ≤ d * g := by rw [hrg, hdg]; exact hrN
      exact Nat.le_of_mul_le_mul_right this hg_pos
    have hxq_lt : x.val / g < d := Nat.div_lt_of_lt_mul (by rw [mul_comm, hdg]; exact x.isLt)
    have hf_inj : Function.Injective f := by
      intro q₁ q₂ h
      have hv := congrArg Fin.val h
      simp only [f] at hv
      have h1 : q₁.val < d := lt_of_lt_of_le q₁.isLt hrg_le
      have h2 : q₂.val < d := lt_of_lt_of_le q₂.isLt hrg_le
      apply Fin.ext
      by_cases hle1 : q₁.val ≤ x.val / g <;> by_cases hle2 : q₂.val ≤ x.val / g
      · have e1 : x.val / g + d - q₁.val = (x.val / g - q₁.val) + d := by omega
        have e2 : x.val / g + d - q₂.val = (x.val / g - q₂.val) + d := by omega
        rw [e1, e2, Nat.add_mod_right, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e1 : x.val / g + d - q₁.val = (x.val / g - q₁.val) + d := by omega
        rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have e2 : x.val / g + d - q₂.val = (x.val / g - q₂.val) + d := by omega
        rw [e2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega
      · have hm1 : (x.val / g + d - q₁.val) % d = x.val / g + d - q₁.val := Nat.mod_eq_of_lt (by omega)
        have hm2 : (x.val / g + d - q₂.val) % d = x.val / g + d - q₂.val := Nat.mod_eq_of_lt (by omega)
        rw [hm1, hm2] at hv
        have hle1' : q₁.val ≤ x.val / g + d := le_trans (le_of_lt h1) (Nat.le_add_left d _)
        have hle2' : q₂.val ≤ x.val / g + d := le_trans (le_of_lt h2) (Nat.le_add_left d _)
        have h1eq : (x.val / g + d - q₁.val) + q₁.val = (x.val / g + d - q₂.val) + q₂.val := by
          rw [Nat.sub_add_cancel hle1', Nat.sub_add_cancel hle2']
        rw [hv] at h1eq
        exact Nat.add_left_cancel h1eq
    have hfilt : Finset.univ.filter (fun i : Fin d => x ∈ R i) = Finset.univ.image f := by
      ext i
      simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨k, hk⟩
        have hv := congrArg Fin.val hk
        simp only at hv
        have hrem : k.val % g = x.val % g := by
          have h1 := congrArg (· % g) hv
          simp only [Nat.mod_mod_of_dvd _ hgN, Nat.mul_comm i.val g, Nat.mul_add_mod] at h1
          exact h1
        have hkdiv_lt : k.val / g < rg := Nat.div_lt_of_lt_mul (by rw [mul_comm, hrg]; exact k.isLt)
        refine ⟨⟨k.val / g, hkdiv_lt⟩, ?_⟩
        apply Fin.ext
        simp only [f]
        have hkm : k.val = k.val / g * g + k.val % g := by have := Nat.div_add_mod k.val g; linarith
        have hxm : x.val = x.val / g * g + x.val % g := by have := Nat.div_add_mod x.val g; linarith
        have hsum_eq : (i.val + k.val / g) % d = x.val / g := by
          have hmul : ((i.val + k.val / g) * g + x.val % g) % N = x.val := by
            have heq : (i.val + k.val / g) * g + x.val % g = i.val * g + k.val := by
              conv_rhs => rw [hkm, hrem]
              ring
            rw [heq, hv]
          have hdiv_mod : ((i.val + k.val / g) * g + x.val % g) % (d * g) =
              ((i.val + k.val / g) % d) * g + x.val % g := by
            have hmod_lt : ((i.val + k.val / g) % d) * g + x.val % g < d * g := by
              have h1 : ((i.val + k.val / g) % d + 1) * g ≤ d * g :=
                Nat.mul_le_mul_right g (Nat.mod_lt _ hd_pos)
              have h2 : x.val % g < g := Nat.mod_lt _ hg_pos
              rw [add_mul, one_mul] at h1; omega
            have hdecomp : (i.val + k.val / g) * g + x.val % g =
                (d * g) * ((i.val + k.val / g) / d) + (((i.val + k.val / g) % d) * g + x.val % g) := by
              have := Nat.div_add_mod (i.val + k.val / g) d
              nlinarith
            conv_lhs => rw [hdecomp]
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hmod_lt]
          have hmul' : ((i.val + k.val / g) * g + x.val % g) % (d * g) = x.val := by
            rwa [hdg]
          rw [hdiv_mod] at hmul'
          conv_rhs at hmul' => rw [hxm]
          have hcancel : ((i.val + k.val / g) % d) * g = (x.val / g) * g := by omega
          exact Nat.eq_of_mul_eq_mul_right hg_pos hcancel
        have hilt := i.isLt
        have hklt : k.val / g < d := lt_of_lt_of_le hkdiv_lt hrg_le
        by_cases hsum_lt : i.val + k.val / g < d
        · rw [Nat.mod_eq_of_lt hsum_lt] at hsum_eq
          have h1 : x.val / g + d - k.val / g = i.val + d := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hilt]
        · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hsum_eq
          have h1 : x.val / g + d - k.val / g = i.val := by omega
          rw [h1, Nat.mod_eq_of_lt hilt]
      · rintro ⟨q, rfl⟩
        have hqlt : q.val < d := lt_of_lt_of_le q.isLt hrg_le
        have hk_lt : q.val * g + x.val % g < r := by
          have h1 : (q.val + 1) * g ≤ rg * g := Nat.mul_le_mul_right g q.isLt
          have h2 : x.val % g < g := Nat.mod_lt _ hg_pos
          rw [add_mul, one_mul, hrg] at h1; omega
        refine ⟨⟨q.val * g + x.val % g, hk_lt⟩, ?_⟩
        apply Fin.ext
        simp only [f]
        have hxm : x.val = x.val / g * g + x.val % g := by have := Nat.div_add_mod x.val g; linarith
        by_cases hle : q.val ≤ x.val / g
        · have hmod : (x.val / g + d - q.val) % d = x.val / g - q.val := by
            have e1 : x.val / g + d - q.val = (x.val / g - q.val) + d := by omega
            rw [e1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          rw [hmod]
          have h2 : (x.val / g - q.val) * g + (q.val * g + x.val % g) = x.val := by
            have : (x.val / g - q.val) * g + q.val * g = (x.val / g) * g := by
              rw [← add_mul, Nat.sub_add_cancel hle]
            omega
          rw [h2, Nat.mod_eq_of_lt x.isLt]
        · have hmod : (x.val / g + d - q.val) % d = x.val / g + d - q.val :=
            Nat.mod_eq_of_lt (by omega)
          rw [hmod]
          have h2 : (x.val / g + d - q.val) * g + (q.val * g + x.val % g) = x.val + N := by
            have : (x.val / g + d - q.val) * g + q.val * g = (x.val / g + d) * g := by
              rw [← add_mul, Nat.sub_add_cancel (le_trans (le_of_lt hqlt) (Nat.le_add_left d _))]
            rw [add_mul, hdg] at this
            omega
          rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
    rw [hfilt, Finset.card_image_of_injective _ hf_inj, Finset.card_univ, Fintype.card_fin]
  exact ⟨S0,R,hS0_card,hR_card,hR_cov⟩

theorem multiple {N r s M : ℕ} (hr0 : 0<r) (hrN : r≤N) (hsN : s≤N) (hd : N/Nat.gcd N r ∣ M) :
    ∃ (P : Finset (Fin N)) (Q : Fin M → Finset (Fin N)) (c : ℕ), P.card=s ∧
      (∀ i, (Q i).card=r) ∧ ∀ x, (Finset.univ.filter (fun i => x ∈ Q i)).card=c := by
  classical
  obtain ⟨P,R,hp,hr,cov⟩ := block hr0 hrN hsN
  obtain ⟨k,rfl⟩ := hd
  let d := N / Nat.gcd N r
  let e : Fin (d*k) ≃ Fin d × Fin k := finProdFinEquiv.symm
  refine ⟨P, fun i => R (e i).1, (r/Nat.gcd N r)*k,hp,fun _ => hr _,?_⟩
  intro x
  calc
    _ = ∑ i : Fin (d*k), (if x ∈ R (e i).1 then 1 else 0 : ℕ) := by simp <;> rfl
    _ = ∑ z : Fin d × Fin k, (if x ∈ R z.1 then 1 else 0 : ℕ) :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = (∑ j : Fin d, (if x ∈ R j then 1 else 0 : ℕ))*k := by
      rw [Fintype.sum_prod_type,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : x ∈ R j <;> simp [hj]
    _ = _ := by
      congr 1
      simpa using (cov x)

theorem constant_cost {N M t c : ℕ} (P : Finset (Fin N)) (Q : Fin M → Finset (Fin N))
    (uniform : ∀ y, (Finset.univ.filter (fun i => y ∈ Q i)).card=c)
    (T : Fin N → Fin N → Bool) (row : ∀ x, (Finset.univ.filter (fun y => T x y)).card=t) :
    (∑ x, ∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ P ∧ y ∈ Q i)).card else 0) =
    P.card*(t*c) := by
  classical
  have inner (x : Fin N) : (∑ y, if T x y then (Finset.univ.filter (fun i => x ∈ P ∧ y ∈ Q i)).card else 0) =
      if x ∈ P then t*c else 0 := by
    by_cases h : x ∈ P
    · simp only [h,true_and,uniform,if_true]
      rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,row]
      rfl
    · simp [h]
  simp_rw [inner]
  rw [← Finset.sum_filter, Finset.sum_const,nsmul_eq_mul]
  simp
end FixedBlocks33662

namespace Fair33662

theorem power_feasible (A : ℕ → Prop) (c T : ℕ)
    (necessary : ∀ n, 0<n → A n → c ∣ n)
    (large : ∀ n, 0<n → T ≤ n → c ∣ n → A n) :
    (∃ h : ℕ, A (2^h)) ↔ ∃ j : ℕ, c = 2^j := by
  constructor
  · rintro ⟨h,hh⟩
    obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (necessary _ (by positivity) hh)
    exact ⟨j,hj⟩
  · rintro ⟨j,rfl⟩
    refine ⟨j+T,large _ (by positivity) ?_ ?_⟩
    · exact le_trans (by omega : T ≤ j+T) (Nat.lt_two_pow_self (n := j+T)).le
    · rw [pow_add]
      exact dvd_mul_right _ _

theorem coins (k h : ℕ) :
    (∃ a b : ℕ, 2^h = a*(5*2^k) + b*(3*2^k)) ↔ k+3 ≤ h := by
  constructor
  · rintro ⟨a,b,hab⟩
    have hf : 2^h = 2^k*(5*a+3*b) := by simpa only [hab] using (show a*(5*2^k)+b*(3*2^k) = 2^k*(5*a+3*b) by ring)
    have hd : (2:ℕ)^k ∣ 2^h := ⟨_,hf⟩
    have hle : k ≤ h := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2:ℕ))).1 hd
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add] at hf
    have he := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < (2:ℕ)^k) hf
    by_contra hbad
    have hn : n ≤ 2 := by omega
    interval_cases n <;> norm_num at he <;> omega
  · intro hh
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hh
    refine ⟨2^m,2^m,?_⟩
    rw [pow_add, pow_add]
    ring

theorem fixed_impossible (k h : ℕ) :
    ¬ ((5*2^k ∣ (2:ℕ)^h) ∨ (3*2^k ∣ (2:ℕ)^h)) := by
  rintro (h5 | h3)
  · have hdiv : 5 ∣ (2:ℕ)^h := dvd_trans (dvd_mul_right _ _) h5
    have hp : Nat.Prime 5 := by decide
    exact (by decide : ¬ 5 ∣ (2:ℕ)) (hp.dvd_of_dvd_pow hdiv)
  · have hdiv : 3 ∣ (2:ℕ)^h := dvd_trans (dvd_mul_right _ _) h3
    have hp : Nat.Prime 3 := by decide
    exact (by decide : ¬ 3 ∣ (2:ℕ)) (hp.dvd_of_dvd_pow hdiv)
end Fair33662

namespace Fair33662
 theorem from_classification : ∀ (N g t r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N →
  2*g+1 < N → N < 2*t → t < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let A := (g+1)*N-r*s
  let fits := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
    C.size ≤ g ∧ ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card ≤ A
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let loss := fun (C : Circ) (T : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
  let bench := N*(N*t)-(2*t-N)*A
  let good := fun (M : ℕ) (D : Fin M → Circ) =>
    (∀ i, fits (D i)) ∧ ∀ T, reg T → N*(∑ i, loss (D i) T) ≤ M*bench
  let available := fun M : ℕ => ∃ D, good M D
  let fixed := fun (M : ℕ) (D : Fin M → Circ) =>
    ∃ (swap : Bool) (P : Finset X) (Q : Fin M → Finset X),
      ((P.card = r ∧ ∀ i, (Q i).card = s) ∨ (P.card = s ∧ ∀ i, (Q i).card = r)) ∧
      ∀ (i : Fin M) (x y : X), (if swap then tab (D i) y x else tab (D i) x y) =
        decide (x ∈ P ∨ y ∈ Q i)
  let d := N / Nat.gcd N r
  let e := N / Nat.gcd N s
  let c := Nat.gcd d e
  (∀ M : ℕ, 0 < M →
    ((∃ D, good M D ∧ fixed M D) ↔ d ∣ M ∨ e ∣ M) ∧
    (available M → c ∣ M) ∧
    (c*(d/c-1)*(e/c-1) ≤ M → (available M ↔ c ∣ M)) ∧
    (r ∣ N → s ∣ N → (available M ↔ ∃ a b : ℕ, M = a*d+b*e))) →
  (∀ M : ℕ, 0 < M →
    ((∃ D, good M D ∧ fixed M D) ↔ d ∣ M ∨ e ∣ M) ∧
    (available M → c ∣ M) ∧
    (c*(d/c-1)*(e/c-1) ≤ M → (available M ↔ c ∣ M)) ∧
    (r ∣ N → s ∣ N → (available M ↔ ∃ a b : ℕ, M = a*d+b*e))) ∧
  ((∃ h : ℕ, available (2^h)) ↔ ∃ j : ℕ, c = 2^j) ∧
  ∀ k : ℕ, 0 < k → N = 15*2^k → r = 3 → s = 5 →
    ∀ h : ℕ, (available (2^h) ↔ k+3 ≤ h) ∧
      ∀ D : Fin (2^h) → Circ, good (2^h) D → ¬ fixed (2^h) D := by

  intro N g t r s hr hrs hsum hprod hN ht hsmall
  dsimp only
  intro H
  refine ⟨H, ?_, ?_⟩
  ·
    let X := Fin N
    let Circ := PEqualNP.CircuitLowerBounds.Circuit
    let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
    let A := (g+1)*N-r*s
    let fits := fun (C : Circ) =>
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
      (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
        (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
      C.size ≤ g ∧ ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card ≤ A
    let reg := fun (T : X → X → Bool) =>
      (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
      (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
    let loss := fun (C : Circ) (T : X → X → Bool) =>
      ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
    let bench := N*(N*t)-(2*t-N)*A
    let good := fun (M : ℕ) (D : Fin M → Circ) =>
      (∀ i, fits (D i)) ∧ ∀ T, reg T → N*(∑ i, loss (D i) T) ≤ M*bench
    let available := fun M : ℕ => ∃ D, good M D
    let fixed := fun (M : ℕ) (D : Fin M → Circ) =>
      ∃ (swap : Bool) (P : Finset X) (Q : Fin M → Finset X),
        ((P.card = r ∧ ∀ i, (Q i).card = s) ∨ (P.card = s ∧ ∀ i, (Q i).card = r)) ∧
        ∀ (i : Fin M) (x y : X), (if swap then tab (D i) y x else tab (D i) x y) =
          decide (x ∈ P ∨ y ∈ Q i)
    let d := N / Nat.gcd N r
    let e := N / Nat.gcd N s
    let c := Nat.gcd d e
    apply Fair33662.power_feasible available c (T := (N / N.gcd r).gcd (N / N.gcd s) *
        (N / N.gcd r / (N / N.gcd r).gcd (N / N.gcd s) - 1) *
        (N / N.gcd s / (N / N.gcd r).gcd (N / N.gcd s) - 1))
    · exact fun n hn => (H n hn).2.1
    · exact fun n hn hlim hc => ((H n hn).2.2.1 hlim).2 hc
  · intro k hk hN15 h3 h5 h
    subst N
    subst r
    subst s
    let q := 2^k
    have h3div : 3 ∣ 15*2^k := ⟨5*2^k, by ring⟩
    have h5div : 5 ∣ 15*2^k := ⟨3*2^k, by ring⟩
    have hd : (15*2^k) / Nat.gcd (15*2^k) 3 = 5*2^k := by
      rw [Nat.gcd_eq_right h3div]
      exact Nat.div_eq_of_eq_mul_left (by decide) (by ring)
    have he : (15*2^k) / Nat.gcd (15*2^k) 5 = 3*2^k := by
      rw [Nat.gcd_eq_right h5div]
      exact Nat.div_eq_of_eq_mul_left (by decide) (by ring)
    have cls := H (2^h) (by positivity)
    rw [hd,he] at cls
    refine ⟨(cls.2.2.2 h3div h5div).trans (Fair33662.coins k h), ?_⟩
    intro D good fixed
    exact Fair33662.fixed_impossible k h (cls.1.mp ⟨D,good,fixed⟩)

end Fair33662

namespace Finish33662
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Decoder33662 Average33662

def feasible {N M : ℕ} (t r s : ℕ) := ∃ R S : Fin M → Finset (Fin N),
  (∀ i, dims r s (R i) (S i)) ∧ flat t R S
def fixed {N M : ℕ} (r s : ℕ) (D : Fin M → Circuit) :=
  ∃ (swap : Bool) (P : Finset (Fin N)) (Q : Fin M → Finset (Fin N)),
    ((P.card = r ∧ ∀ i, (Q i).card = s) ∨ (P.card = s ∧ ∀ i, (Q i).card = r)) ∧
    ∀ (i : Fin M) (x y : Fin N), (if swap then tab (D i) y x else tab (D i) x y) =
      decide (x ∈ P ∨ y ∈ Q i)

theorem realize {N M g t r s : ℕ} [NeZero N] (hr : 0<r) (hrs : r≤s)
    (hs : r+s=g+1) (hg : g+1≤N) (ht : N<2*t) (htN : t<N)
    (R S : Fin M → Finset (Fin N)) (dim : ∀ i, dims r s (R i) (S i)) (fl : flat t R S) :
    ∃ D : Fin M → Circuit, @good N M g t (area N g r s) D ∧ ∀ i, shape (D i) (R i) (S i) := by
  have nr (i) : (R i).Nonempty := by
    apply Finset.card_pos.mp
    rcases dim i with h|h <;> omega
  choose D reads valid mono sz form using fun i => Construct33662.construct (R i) (S i) (nr i)
  refine ⟨D, ⟨?_,(shape_budget hs hg ht htN D R S dim form).2 fl⟩,form⟩
  intro i
  refine ⟨reads i, valid i, ?_, ?_, (exact_area hs (D i) _ _ (dim i) (form i)).le⟩
  · intro v hv
    obtain ⟨h,hf⟩ := mono i v hv
    have e : v.op = GateOp.and ∨ v.op = GateOp.or := h
    exact ⟨hf,e.elim (fun a => Or.inr (Or.inl a)) Or.inl⟩
  · have z := sz i
    rcases dim i with ⟨a,b⟩|⟨a,b⟩ <;> omega

theorem transpose_flat {N M t : ℕ} {R S : Fin M → Finset (Fin N)} (h : flat t R S) :
    flat t S R := by
  intro T U a b
  have e (V : Fin N → Fin N → Bool) :
      (∑ x, ∑ y, if V x y then (Finset.univ.filter (fun i => x ∈ S i ∧ y ∈ R i)).card else 0) =
      ∑ x, ∑ y, if V y x then (Finset.univ.filter (fun i => x ∈ R i ∧ y ∈ S i)).card else 0 := by
    rw [Finset.sum_comm]
    simp only [and_comm]
  exact (e T).trans ((h (fun x y => T y x) (fun x y => U y x) ⟨a.2,a.1⟩ ⟨b.2,b.1⟩).trans (e U).symm)

theorem from_fixed_rows {N M g t r s : ℕ} [NeZero N] (hs : r+s=g+1)
    (hg : g+1≤N) (ht : N<2*t) (htN : t<N) (D : Fin M → Circuit)
    (h : @good N M g t (area N g r s) D) (P : Finset (Fin N)) (Q : Fin M → Finset (Fin N))
    (dim : ∀ i, dims r s P (Q i)) (swap : Bool)
    (form : ∀ i x y, (if swap then tab (D i) y x else tab (D i) x y) = decide (x∈P ∨ y∈Q i)) :
    flat t (fun _ : Fin M => P) Q := by
  cases swap with
  | false => exact (shape_budget hs hg ht htN D _ Q dim form).1 h.2
  | true =>
    apply transpose_flat (R := Q) (S := fun _ => P)
    have dm (i) : dims r s (Q i) P := by
      rcases dim i with ⟨a,b⟩|⟨a,b⟩
      · exact Or.inr ⟨b,a⟩
      · exact Or.inl ⟨b,a⟩
    apply (shape_budget hs hg ht htN D Q _ dm _).1 h.2
    intro i x y
    simpa [or_comm] using form i y x

theorem fixed_iff {N M g t r s : ℕ} [NeZero N] (hr : 0<r) (hrs : r≤s)
    (hs : r+s=g+1) (hNg : 2*g+1<N) (ht : N<2*t) (htN : t<N) :
    (∃ D : Fin M → Circuit, @good N M g t (area N g r s) D ∧ @fixed N M r s D) ↔
      N/Nat.gcd N r ∣ M ∨ N/Nat.gcd N s ∣ M := by
  have hg : g+1≤N := by omega
  have ht0 : 0<t := by omega
  have rsN : r<N ∧ s<N := by omega
  constructor
  · rintro ⟨D,h,sw,P,Q,dim,form⟩
    have dm (i) : dims r s P (Q i) := dim.elim (fun a => Or.inl ⟨a.1,a.2 i⟩) (fun a => Or.inr ⟨a.1,a.2 i⟩)
    have fl := from_fixed_rows hs hg ht htN D h P Q dm sw form
    rcases dim with ⟨a,b⟩|⟨a,b⟩
    · exact Or.inr (Fixed33662.divides ht0 htN P (by omega) (Finset.card_pos.mp (by omega)) Q b fl)
    · exact Or.inl (Fixed33662.divides ht0 htN P (by omega) (Finset.card_pos.mp (by omega)) Q b fl)
  · intro div
    have mk (k l : ℕ) (hk : 0<k) (hkN : k≤N) (hlN : l≤N) (d : N/Nat.gcd N k ∣ M)
        (sizes : l=r ∧ k=s ∨ l=s ∧ k=r) :
        ∃ D : Fin M → Circuit, @good N M g t (area N g r s) D ∧ @fixed N M r s D := by
      obtain ⟨P,Q,c,a,b,counts⟩ := FixedBlocks33662.multiple hk hkN hlN d
      have both : (P.card=r ∧ ∀ i, (Q i).card=s) ∨ (P.card=s ∧ ∀ i, (Q i).card=r) :=
        sizes.elim (fun v => Or.inl ⟨a.trans v.1,fun i => (b i).trans v.2⟩)
                   (fun v => Or.inr ⟨a.trans v.1,fun i => (b i).trans v.2⟩)
      have dm (i) : dims r s P (Q i) := both.elim (fun v => Or.inl ⟨v.1,v.2 i⟩) (fun v => Or.inr ⟨v.1,v.2 i⟩)
      have fl : flat t (fun _ : Fin M => P) Q := by
        intro T U ht hu
        exact (FixedBlocks33662.constant_cost P Q counts T ht.1).trans (FixedBlocks33662.constant_cost P Q counts U hu.1).symm
      obtain ⟨D,hD,f⟩ := realize hr hrs hs hg ht htN _ Q dm fl
      exact ⟨D,hD,false,P,Q,both,f⟩
    rcases div with d|d
    · exact mk r s hr rsN.1.le rsN.2.le d (Or.inr ⟨rfl,rfl⟩)
    · exact mk s r (by omega) rsN.2.le rsN.1.le d (Or.inl ⟨rfl,rfl⟩)
end Finish33662

theorem result : ∀ (N g t r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N →
  2*g+1 < N → N < 2*t → t < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let A := (g+1)*N-r*s
  let fits := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
    C.size ≤ g ∧ ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card ≤ A
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let loss := fun (C : Circ) (T : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
  let bench := N*(N*t)-(2*t-N)*A
  let good := fun (M : ℕ) (D : Fin M → Circ) =>
    (∀ i, fits (D i)) ∧ ∀ T, reg T → N*(∑ i, loss (D i) T) ≤ M*bench
  let available := fun M : ℕ => ∃ D, good M D
  let fixed := fun (M : ℕ) (D : Fin M → Circ) =>
    ∃ (swap : Bool) (P : Finset X) (Q : Fin M → Finset X),
      ((P.card = r ∧ ∀ i, (Q i).card = s) ∨ (P.card = s ∧ ∀ i, (Q i).card = r)) ∧
      ∀ (i : Fin M) (x y : X), (if swap then tab (D i) y x else tab (D i) x y) =
        decide (x ∈ P ∨ y ∈ Q i)
  let d := N / Nat.gcd N r
  let e := N / Nat.gcd N s
  let c := Nat.gcd d e
  (∀ M : ℕ, 0 < M →
    ((∃ D, good M D ∧ fixed M D) ↔ d ∣ M ∨ e ∣ M) ∧
    (available M → c ∣ M) ∧
    (c*(d/c-1)*(e/c-1) ≤ M → (available M ↔ c ∣ M)) ∧
    (r ∣ N → s ∣ N → (available M ↔ ∃ a b : ℕ, M = a*d+b*e))) ∧
  ((∃ h : ℕ, available (2^h)) ↔ ∃ j : ℕ, c = 2^j) ∧
  ∀ k : ℕ, 0 < k → N = 15*2^k → r = 3 → s = 5 →
    ∀ h : ℕ, (available (2^h) ↔ k+3 ≤ h) ∧
      ∀ D : Fin (2^h) → Circ, good (2^h) D → ¬ fixed (2^h) D := by
  intro N g t r s hr hrs hs hp hn ht htN
  apply Fair33662.from_classification N g t r s hr hrs hs hp hn ht htN
  letI : NeZero N := ⟨by omega⟩
  intro M hM
  have avail : (∃ D : Fin M → PEqualNP.CircuitLowerBounds.Circuit,
      @Decoder33662.good N M g t (Decoder33662.area N g r s) D) ↔ @Finish33662.feasible N M t r s := by
    constructor
    · rintro ⟨D,hD⟩
      obtain ⟨R,S,dim,_,fl⟩ := Decoder33662.good_rectangles hr hrs hs hp hn ht htN D hD
      exact ⟨R,S,dim,fl⟩
    · rintro ⟨R,S,dim,fl⟩
      obtain ⟨D,hD,_⟩ := Finish33662.realize hr hrs hs (by omega) ht htN R S dim fl
      exact ⟨D,hD⟩
  have casesM := (rectangle_classification N t r s (by omega) htN hr (by omega) (by omega) (by omega)).2 M
  exact ⟨Finish33662.fixed_iff hr hrs hs hn ht htN,
    fun a => casesM.2.1 (avail.1 a),
    fun atLeast => avail.trans (casesM.2.2.1 atLeast),
    fun rd sd => avail.trans (casesM.2.2.2 rd sd)⟩

end PEqualNP.Outside.L_meta_33662_aux

theorem PEqualNP.Outside.L_meta_33662 : ∀ (N g t r s : ℕ), 0 < r → r ≤ s → r+s = g+1 → r*s < N →
  2*g+1 < N → N < 2*t → t < N →
  let X := Fin N
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let tab := fun (C : Circ) (x y : X) => C.eval (PEqualNP.Represents.oneEach x y)
  let A := (g+1)*N-r*s
  let fits := fun (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N+N) C ∧ C.output < N+N+C.size ∧
    (∀ gate ∈ C.gates, gate.inputs.length ≤ 2 ∧
      (gate.op = .or ∨ gate.op = .and ∨ (gate.op = .not ∧ gate.inputs.length = 1))) ∧
    C.size ≤ g ∧ ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2)).card ≤ A
  let reg := fun (T : X → X → Bool) =>
    (∀ x, (Finset.univ.filter (fun y => T x y)).card = t) ∧
    (∀ y, (Finset.univ.filter (fun x => T x y)).card = t)
  let loss := fun (C : Circ) (T : X → X → Bool) =>
    ((Finset.univ : Finset (X × X)).filter (fun z => tab C z.1 z.2 ≠ T z.1 z.2)).card
  let bench := N*(N*t)-(2*t-N)*A
  let good := fun (M : ℕ) (D : Fin M → Circ) =>
    (∀ i, fits (D i)) ∧ ∀ T, reg T → N*(∑ i, loss (D i) T) ≤ M*bench
  let available := fun M : ℕ => ∃ D, good M D
  let fixed := fun (M : ℕ) (D : Fin M → Circ) =>
    ∃ (swap : Bool) (P : Finset X) (Q : Fin M → Finset X),
      ((P.card = r ∧ ∀ i, (Q i).card = s) ∨ (P.card = s ∧ ∀ i, (Q i).card = r)) ∧
      ∀ (i : Fin M) (x y : X), (if swap then tab (D i) y x else tab (D i) x y) =
        decide (x ∈ P ∨ y ∈ Q i)
  let d := N / Nat.gcd N r
  let e := N / Nat.gcd N s
  let c := Nat.gcd d e
  (∀ M : ℕ, 0 < M →
    ((∃ D, good M D ∧ fixed M D) ↔ d ∣ M ∨ e ∣ M) ∧
    (available M → c ∣ M) ∧
    (c*(d/c-1)*(e/c-1) ≤ M → (available M ↔ c ∣ M)) ∧
    (r ∣ N → s ∣ N → (available M ↔ ∃ a b : ℕ, M = a*d+b*e))) ∧
  ((∃ h : ℕ, available (2^h)) ↔ ∃ j : ℕ, c = 2^j) ∧
  ∀ k : ℕ, 0 < k → N = 15*2^k → r = 3 → s = 5 →
    ∀ h : ℕ, (available (2^h) ↔ k+3 ≤ h) ∧
      ∀ D : Fin (2^h) → Circ, good (2^h) D → ¬ fixed (2^h) D := PEqualNP.Outside.L_meta_33662_aux.result
