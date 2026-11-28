import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1052_aux

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

end PEqualNP.Outside.L_lib_1052_aux

theorem PEqualNP.Outside.L_lib_1052 :
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
      fun u v => PEqualNP.Outside.L_lib_1052_aux.flat_four_corner ht0 htN (B M R S) hfl u v x y
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
    rcases PEqualNP.Outside.L_lib_1052_aux.cyclic_block_feasible (t := t) hr0 hrN hsN with ⟨R, S, hd, hfl⟩
    exact ⟨R, S, fun i => Or.inl (hd i), hfl⟩
  have hfeas_e : feasible e := by
    rcases PEqualNP.Outside.L_lib_1052_aux.cyclic_block_feasible (t := t) hs0 hsN hrN with ⟨R, S, hd, hfl⟩
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
    rcases PEqualNP.Outside.L_lib_1052_aux.frobenius_coprime hd'_pos he'_pos hcop hM'_ge with ⟨a, b, hM'⟩
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
