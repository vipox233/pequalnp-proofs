import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1039

open Finset Classical

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

section forms

variable {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]

theorem exists_one (f : X →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) : ∃ e, f e = 1 := by
  by_contra h
  push Not at h
  apply hf
  refine LinearMap.ext fun x => ?_
  rcases z2 (f x) with h1 | h1
  · rw [h1, LinearMap.zero_apply]
  · exact absurd h1 (h x)

theorem sep (f g : X →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (hfg : f ≠ g) :
    ∃ e, f e = 1 ∧ g e = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ g w := by
    by_contra h
    push Not at h
    exact hfg (LinearMap.ext h)
  rcases z2 (f w) with h1 | h1 <;> rcases z2 (g w) with h2 | h2
  · rw [h1, h2] at hw; exact absurd rfl hw
  · obtain ⟨e, he⟩ := exists_one f hf
    rcases z2 (g e) with h3 | h3
    · exact ⟨e, he, h3⟩
    · refine ⟨e + w, ?_, ?_⟩
      · rw [map_add, he, h1]; decide
      · rw [map_add, h3, h2]; decide
  · exact ⟨w, h1, h2⟩
  · rw [h1, h2] at hw; exact absurd rfl hw

theorem half_le (f : X →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (P : X → Prop)
    (hP : ∀ y, P y → f y = 0) : 2 * Nat.card {y // P y} ≤ Nat.card X := by
  obtain ⟨e, he⟩ := exists_one f hf
  have hinj : Function.Injective (fun p : {y // P y} × ZMod 2 => p.1.1 + p.2 • e) := by
    rintro ⟨⟨y, hy⟩, s⟩ ⟨⟨y', hy'⟩, s'⟩ h
    simp only at h
    have hs : s = s' := by
      have := congrArg f h
      simpa [map_add, map_smul, hP y hy, hP y' hy', he] using this
    subst hs
    have : y = y' := by simpa using h
    subst this
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_zmod] at this
  linarith

theorem quarter_le (f g : X →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f ≠ g)
    (P : X → Prop) (hP : ∀ y, P y → f y = 0 ∧ g y = 0) :
    4 * Nat.card {y // P y} ≤ Nat.card X := by
  obtain ⟨e1, h11, h12⟩ := sep f g hf hfg
  obtain ⟨e2, h22, h21⟩ := sep g f hg (Ne.symm hfg)
  have hinj : Function.Injective
      (fun p : {y // P y} × ZMod 2 × ZMod 2 => p.1.1 + p.2.1 • e1 + p.2.2 • e2) := by
    rintro ⟨⟨y, hy⟩, s, t⟩ ⟨⟨y', hy'⟩, s', t'⟩ h
    simp only at h
    have hs : s = s' := by
      have := congrArg f h
      simpa [map_add, map_smul, (hP y hy).1, (hP y' hy').1, h11, h21] using this
    have ht : t = t' := by
      have := congrArg g h
      simpa [map_add, map_smul, (hP y hy).2, (hP y' hy').2, h12, h22] using this
    subst hs ht
    have : y = y' := by simpa using h
    subst this
    rfl
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod] at this
  linarith

theorem quarter_ge (f g : X →ₗ[ZMod 2] ZMod 2) (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f ≠ g) :
    Nat.card X ≤ 4 * Nat.card {x // f x = 1 ∧ g x = 1} := by
  obtain ⟨e1, h11, h12⟩ := sep f g hf hfg
  obtain ⟨e2, h22, h21⟩ := sep g f hg (Ne.symm hfg)
  have hsurj : Function.Surjective
      (fun p : {x // f x = 1 ∧ g x = 1} × ZMod 2 × ZMod 2 =>
        p.1.1 + p.2.1 • e1 + p.2.2 • e2) := by
    intro w
    refine ⟨⟨⟨w - (f w - 1) • e1 - (g w - 1) • e2, ?_, ?_⟩, f w - 1, g w - 1⟩, ?_⟩
    · simp only [map_sub, map_smul, h11, h21, smul_eq_mul]; ring
    · simp only [map_sub, map_smul, h12, h22, smul_eq_mul]; ring
    · simp only; abel
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_prod, Nat.card_zmod] at this
  linarith

theorem half_ge (f : X →ₗ[ZMod 2] ZMod 2) :
    Nat.card X ≤ 2 * Nat.card {x // f x = 0} := by
  by_cases hf : f = 0
  · have hsurj : Function.Surjective (fun p : {x // f x = 0} × ZMod 2 => p.1.1) := by
      intro w
      exact ⟨⟨⟨w, by rw [hf, LinearMap.zero_apply]⟩, 0⟩, rfl⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, Nat.card_zmod] at this
    linarith
  · obtain ⟨e, he⟩ := exists_one f hf
    have hsurj : Function.Surjective
        (fun p : {x // f x = 0} × ZMod 2 => p.1.1 + p.2 • e) := by
      intro w
      refine ⟨⟨⟨w - f w • e, ?_⟩, f w⟩, ?_⟩
      · simp only [map_sub, map_smul, he, smul_eq_mul, mul_one, sub_self]
      · simp only; abel
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [Nat.card_prod, Nat.card_zmod] at this
    linarith

end forms

section counts

variable {X Y : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Fintype X]
  [AddCommGroup Y] [Module (ZMod 2) Y] [Fintype Y] {m : ℕ}

def Zr (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) (x : X) (y : Y) :
    Prop := ∀ i, a i x * b i y = 0

theorem card_rows (P : X → Y → Prop) :
    Nat.card {w : X × Y // P w.1 w.2} = ∑ x, Nat.card {y // P x y} := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype P), Nat.card_sigma]

theorem card_sub (Q : X → Prop) [DecidablePred Q] : Nat.card {x // Q x} = ∑ x, if Q x then 1 else 0 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem nz_both {p q : ZMod 2} (h : p * q ≠ 0) : p = 1 ∧ q = 1 := by
  rcases z2 p with h1 | h1 <;> rcases z2 q with h2 | h2 <;> subst h1 <;> subst h2 <;>
    simp_all

theorem card_le_all (P : Y → Prop) : Nat.card {y // P y} ≤ Nat.card Y :=
  Nat.card_le_card_of_injective _ Subtype.val_injective

theorem row_up (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) (x : X) :
    2 * Nat.card {y // Zr a b x y} ≤
      Nat.card Y + Nat.card Y * (if ∀ y, Zr a b x y then 1 else 0) := by
  split_ifs with hQ
  · have := card_le_all (Zr a b x); linarith
  · push Not at hQ
    obtain ⟨y0, hy0⟩ := hQ
    simp only [Zr, not_forall] at hy0
    obtain ⟨i, hi⟩ := hy0
    obtain ⟨hax, hby⟩ := nz_both hi
    have hb : b i ≠ 0 := by
      intro h; rw [h, LinearMap.zero_apply] at hby; exact zero_ne_one hby
    have := half_le (b i) hb (Zr a b x) (fun y hy => by
      have := hy i; rwa [hax, one_mul] at this)
    linarith

theorem sum_aux (Q : X → Prop) [DecidablePred Q] (v : ℕ) :
    ∑ x, (v + v * (if Q x then 1 else 0)) = Nat.card X * v + Nat.card {x // Q x} * v := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← card_sub, Finset.sum_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]
  ring

theorem upper (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) :
    2 * Nat.card {w : X × Y // Zr a b w.1 w.2} ≤
      Nat.card X * Nat.card Y + Nat.card {x // ∀ y, Zr a b x y} * Nat.card Y := by
  rw [card_rows, Finset.mul_sum, ← sum_aux]
  exact Finset.sum_le_sum fun x _ => row_up a b x

theorem lower (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2)
    (h : Nat.card Y ≤ 2 * Nat.card {y // ∀ x, Zr a b x y}) :
    Nat.card X * Nat.card Y + Nat.card {x // ∀ y, Zr a b x y} * Nat.card Y ≤
      2 * Nat.card {w : X × Y // Zr a b w.1 w.2} := by
  rw [card_rows, Finset.mul_sum, ← sum_aux]
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with hQ
  · have : Nat.card {y // Zr a b x y} = Nat.card Y :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hQ)
    rw [this]; linarith
  · have : Nat.card {y // ∀ x, Zr a b x y} ≤ Nat.card {y // Zr a b x y} :=
      Nat.card_le_card_of_injective (fun y => (⟨y.1, y.2 x⟩ : {y // Zr a b x y}))
        (fun p q hpq => Subtype.ext (Subtype.mk.inj hpq))
    linarith

theorem gap (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) (i k : Fin m)
    (hai : a i ≠ 0) (hak : a k ≠ 0) (ha : a i ≠ a k) (hbi : b i ≠ 0) (hbk : b k ≠ 0)
    (hb : b i ≠ b k) :
    16 * Nat.card {w : X × Y // Zr a b w.1 w.2} + Nat.card X * Nat.card Y ≤
      8 * (Nat.card X * Nat.card Y + Nat.card {x // ∀ y, Zr a b x y} * Nat.card Y) := by
  have hrow : ∀ x, 4 * Nat.card {y // Zr a b x y} +
      Nat.card Y * (if a i x = 1 ∧ a k x = 1 then 1 else 0) ≤
      2 * (Nat.card Y + Nat.card Y * (if ∀ y, Zr a b x y then 1 else 0)) := by
    intro x
    have h0 := row_up a b x
    split_ifs with h1 h2
    · have := quarter_le (b i) (b k) hbi hbk hb (Zr a b x) (fun y hy => by
        have hi := hy i; have hk := hy k
        rw [h1.1, one_mul] at hi; rw [h1.2, one_mul] at hk
        exact ⟨hi, hk⟩)
      linarith
    · have := quarter_le (b i) (b k) hbi hbk hb (Zr a b x) (fun y hy => by
        have hi := hy i; have hk := hy k
        rw [h1.1, one_mul] at hi; rw [h1.2, one_mul] at hk
        exact ⟨hi, hk⟩)
      linarith
    · rename_i h2; rw [if_pos h2] at h0; linarith
    · rename_i h2; rw [if_neg h2] at h0; linarith
  have hs := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset X)) => hrow x
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← card_sub, sum_aux, ← card_rows] at hs
  have hq := quarter_ge (a i) (a k) hai hak ha
  have hqv := Nat.mul_le_mul_right (Nat.card Y) hq
  nlinarith

theorem thin_of (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2)
    (hno : ¬ ∃ i k, a i ≠ 0 ∧ a k ≠ 0 ∧ a i ≠ a k ∧ b i ≠ 0 ∧ b k ≠ 0 ∧ b i ≠ b k) :
    Nat.card X ≤ 2 * Nat.card {x // ∀ y, Zr a b x y} ∨
      Nat.card Y ≤ 2 * Nat.card {y // ∀ x, Zr a b x y} := by
  push Not at hno
  have zr : ∀ i x y, (a i ≠ 0 ∧ b i ≠ 0 → a i x * b i y = 0) → a i x * b i y = 0 := by
    intro i x y h
    by_cases h1 : a i = 0
    · rw [h1, LinearMap.zero_apply, zero_mul]
    by_cases h2 : b i = 0
    · rw [h2, LinearMap.zero_apply, mul_zero]
    exact h ⟨h1, h2⟩
  by_cases hA : ∀ i j, a i ≠ 0 ∧ b i ≠ 0 → a j ≠ 0 ∧ b j ≠ 0 → a i = a j
  · left
    obtain ⟨α, hα⟩ : ∃ α : X →ₗ[ZMod 2] ZMod 2, ∀ i, a i ≠ 0 ∧ b i ≠ 0 → a i = α := by
      by_cases hex : ∃ i, a i ≠ 0 ∧ b i ≠ 0
      · obtain ⟨i0, h0⟩ := hex
        exact ⟨a i0, fun i hi => hA i i0 hi h0⟩
      · push Not at hex
        exact ⟨0, fun i hi => absurd (hex i hi.1) hi.2⟩
    have h1 := half_ge α
    have h2 : Nat.card {x // α x = 0} ≤ Nat.card {x // ∀ y, Zr a b x y} :=
      Nat.card_le_card_of_injective
        (fun x => (⟨x.1, fun y i => zr i x.1 y (fun hi => by
          rw [hα i hi, x.2, zero_mul])⟩ : {x // ∀ y, Zr a b x y}))
        (fun p q hpq => Subtype.ext (Subtype.mk.inj hpq))
    linarith
  · right
    push Not at hA
    obtain ⟨i, j, hi, hj, hij⟩ := hA
    have hbij : b i = b j := hno i j hi.1 hj.1 hij hi.2 hj.2
    have hβ : ∀ k, a k ≠ 0 ∧ b k ≠ 0 → b k = b i := by
      intro k hk
      by_cases hki : a k = a i
      · rw [hbij]
        exact hno k j hk.1 hj.1 (by rw [hki]; exact hij) hk.2 hj.2
      · exact hno k i hk.1 hi.1 hki hk.2 hi.2
    have h1 := half_ge (b i)
    have h2 : Nat.card {y // b i y = 0} ≤ Nat.card {y // ∀ x, Zr a b x y} :=
      Nat.card_le_card_of_injective
        (fun y => (⟨y.1, fun x k => zr k x y.1 (fun hk => by
          rw [hβ k hk, y.2, mul_zero])⟩ : {y // ∀ x, Zr a b x y}))
        (fun p q hpq => Subtype.ext (Subtype.mk.inj hpq))
    linarith

theorem swap_z (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) :
    Nat.card {w : Y × X // Zr b a w.1 w.2} = Nat.card {w : X × Y // Zr a b w.1 w.2} :=
  Nat.card_congr ((Equiv.prodComm Y X).subtypeEquiv (fun w => by
    simp only [Zr, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]))

theorem swap_l (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) :
    Nat.card {y // ∀ x, Zr b a y x} = Nat.card {y // ∀ x, Zr a b x y} :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun y => by simp only [Zr, mul_comm]))

theorem swap_r (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) :
    Nat.card {x // ∀ y, Zr b a y x} = Nat.card {x // ∀ y, Zr a b x y} :=
  Nat.card_congr (Equiv.subtypeEquivRight (fun x => by simp only [Zr, mul_comm]))

theorem main_gen (a : Fin m → X →ₗ[ZMod 2] ZMod 2) (b : Fin m → Y →ₗ[ZMod 2] ZMod 2) :
    let u := Nat.card X
    let v := Nat.card Y
    let left := Nat.card {x : X // ∀ y, Zr a b x y}
    let right := Nat.card {y : Y // ∀ x, Zr a b x y}
    let z := Nat.card {w : X × Y // Zr a b w.1 w.2}
    let bound := u*v + min (left*v) (u*right)
    let thin := (u ≤ 2*left ∨ v ≤ 2*right)
    2*z ≤ bound ∧ (2*z = bound ↔ thin) ∧ (¬ thin → 16*z + u*v ≤ 8*bound) := by
  intro u v left right z bound thin
  have hU1 : 2 * z ≤ u * v + left * v := upper a b
  have hU2 : 2 * z ≤ u * v + u * right := by
    have := upper b a
    rw [swap_z, swap_l] at this
    linarith [mul_comm u v, mul_comm u right]
  have hu : 0 < u := Nat.card_pos
  have hv : 0 < v := Nat.card_pos
  have huv : 0 < u * v := Nat.mul_pos hu hv
  have h1 : 2 * z ≤ bound := by
    rcases le_total (left * v) (u * right) with h | h
    · show 2 * z ≤ u * v + min (left * v) (u * right)
      rw [min_eq_left h]; exact hU1
    · show 2 * z ≤ u * v + min (left * v) (u * right)
      rw [min_eq_right h]; exact hU2
  have h3 : ¬ thin → 16 * z + u * v ≤ 8 * bound := by
    intro hth
    have hpair : ∃ i k, a i ≠ 0 ∧ a k ≠ 0 ∧ a i ≠ a k ∧ b i ≠ 0 ∧ b k ≠ 0 ∧ b i ≠ b k := by
      by_contra hno
      exact hth (thin_of a b hno)
    obtain ⟨i, k, hai, hak, ha, hbi, hbk, hb⟩ := hpair
    have g1 : 16 * z + u * v ≤ 8 * (u * v + left * v) := gap a b i k hai hak ha hbi hbk hb
    have g2 : 16 * z + u * v ≤ 8 * (u * v + u * right) := by
      have := gap b a i k hbi hbk hb hai hak ha
      rw [swap_z, swap_l] at this
      linarith [mul_comm u v, mul_comm u right]
    show 16 * z + u * v ≤ 8 * (u * v + min (left * v) (u * right))
    rcases le_total (left * v) (u * right) with h | h
    · rw [min_eq_left h]; exact g1
    · rw [min_eq_right h]; exact g2
  refine ⟨h1, ⟨fun heq => ?_, fun hth => ?_⟩, h3⟩
  · by_contra hth
    have := h3 hth
    omega
  · apply le_antisymm h1
    show u * v + min (left * v) (u * right) ≤ 2 * z
    rcases hth with h | h
    · have := lower b a (by rw [swap_r]; exact h)
      rw [swap_z, swap_l] at this
      have hm := min_le_right (left * v) (u * right)
      linarith [mul_comm u v, mul_comm u right]
    · have := lower a b h
      have hm := min_le_left (left * v) (u * right)
      linarith

end counts

end PEqualNP.Outside.L_lib_1039

open PEqualNP.Outside.L_lib_1039 in
theorem PEqualNP.Outside.L_lib_1039 : ∀ l r m : ℕ,
  let F := ZMod 2
  let X := Fin l → F
  let Y := Fin r → F
  ∀ (a : Fin m → X →ₗ[F] F) (b : Fin m → Y →ₗ[F] F),
    let zero := fun (x : X) (y : Y) => ∀ i, a i x * b i y = 0
    let u := Nat.card X
    let v := Nat.card Y
    let left := Nat.card {x : X // ∀ y, zero x y}
    let right := Nat.card {y : Y // ∀ x, zero x y}
    let z := Nat.card {w : X × Y // zero w.1 w.2}
    let bound := u*v + min (left*v) (u*right)
    let thin := (u ≤ 2*left ∨ v ≤ 2*right)
    2*z ≤ bound ∧ (2*z = bound ↔ thin) ∧ (¬ thin → 16*z + u*v ≤ 8*bound) := by
  intro l r m F X Y a b
  exact main_gen a b
