import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_671_aux
open Finset

def bitf {w : ℕ} (xf : ((Fin w → ZMod 2) × ZMod 2) → (Fin w → ZMod 2))
    (nb : ((Fin w → ZMod 2) × ZMod 2) → ZMod 2) (u : Fin w → ZMod 2)
    (j : ((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)) : ZMod 2 :=
  j.2.elim (nb j.1) (fun i => (xf j.1 + u) i)

lemma sum_zero {w : ℕ} (i : Fin w) (F : (Fin w → ZMod 2) → ZMod 2)
    (hF : ∀ u, F (u + Pi.single i 1) = F u) : ∑ u, F u = 0 := by
  refine Finset.sum_involution (fun u _ => u + Pi.single i 1) ?_ ?_ ?_ ?_
  · intro u _; rw [hF]; exact CharTwo.add_self_eq_zero _
  · intro u _ _ h
    have := congrFun h i
    simp at this
  · intro u _; exact Finset.mem_univ _
  · intro u _; ext j; simp [add_assoc, CharTwo.add_self_eq_zero]

lemma mono {w : ℕ} (xf : ((Fin w → ZMod 2) × ZMod 2) → (Fin w → ZMod 2))
    (S : Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w))) (hS : S.card ≤ w)
    (nb nb' : ((Fin w → ZMod 2) × ZMod 2) → ZMod 2) :
    ∑ u, ∏ j ∈ S, bitf xf nb u j = ∑ u, ∏ j ∈ S, bitf xf nb' u j := by
  by_cases h : ∃ j ∈ S, j.2 = none
  · obtain ⟨j0, hj0, hn⟩ := h
    have hi : ∃ i : Fin w, ∀ j ∈ S, j.2 ≠ some i := by
      by_contra hc
      push Not at hc
      choose f hf hf2 using hc
      have h1 : (Finset.univ : Finset (Fin w)).card ≤ (S.erase j0).card := by
        apply Finset.card_le_card_of_injOn f
        · intro i _
          simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
          refine ⟨hf i, ?_⟩
          intro e
          have := hf2 i
          rw [e, hn] at this
          exact absurd this (by simp)
        · intro i _ i' _ e
          have := hf2 i
          rw [e, hf2 i'] at this
          exact (Option.some.inj this).symm
      have h2 := Finset.card_erase_lt_of_mem hj0
      simp at h1
      omega
    obtain ⟨i, hi⟩ := hi
    have z : ∀ nb : ((Fin w → ZMod 2) × ZMod 2) → ZMod 2,
        ∑ u, ∏ j ∈ S, bitf xf nb u j = 0 := by
      intro nb
      apply sum_zero i
      intro u
      apply Finset.prod_congr rfl
      rintro ⟨a, o⟩ hj
      cases o with
      | none => rfl
      | some k =>
        have hne : k ≠ i := fun e => hi _ hj (by rw [e])
        simp [bitf, Pi.single_apply, hne]
    rw [z, z]
  · push Not at h
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.prod_congr rfl
    rintro ⟨a, o⟩ hj
    cases o with
    | none => exact absurd rfl (h _ hj)
    | some k => rfl

lemma sum_target {w : ℕ} (x : Fin w → ZMod 2) :
    ∑ u : Fin w → ZMod 2, ∏ i, (x + u) i = 1 := by
  show ∑ u, (fun u : Fin w → ZMod 2 => ∏ i, u i) (Equiv.addLeft x u) = 1
  rw [Equiv.sum_comp (Equiv.addLeft x) (fun u => ∏ i, u i)]
  have := Finset.prod_univ_sum (fun _ : Fin w => (Finset.univ : Finset (ZMod 2))) (fun _ k => k)
  simp only [Fintype.piFinset_univ] at this
  rw [← this]
  have h2 : ∑ k : ZMod 2, k = 1 := by decide
  simp [h2]

lemma cardGood {w : ℕ} (M : Finset (Fin w → ZMod 2)) (t : (Fin w → ZMod 2) → ZMod 2) :
    ((Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)).filter
      (fun b => ∀ x ∈ M, b x = t x)).card = 2 ^ (2 ^ w - M.card) := by
  have : ((Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)).filter
      (fun b => ∀ x ∈ M, b x = t x))
      = Fintype.piFinset (fun x => if x ∈ M then {t x} else Finset.univ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h x
      split_ifs with hx
      · simp [h x hx]
      · simp
    · intro h x hx
      have := h x
      simpa [hx] using this
  rw [this, Fintype.card_piFinset]
  simp [apply_ite Finset.card, Finset.prod_ite, Finset.filter_not, Finset.card_sdiff]

lemma lower {w : ℕ} (p : Equiv.Perm ((Fin w → ZMod 2) × ZMod 2))
    (c : ((Fin w → ZMod 2) × ZMod 2) →
      Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)) → ZMod 2)
    (A : Finset ((Fin w → ZMod 2) × ZMod 2)) :
    2 ^ (2 ^ w) - 2 ^ (2 ^ w - (A.image (fun a => (p a).1)).card) ≤
    ((Finset.univ : Finset ((Fin w → ZMod 2) × ((Fin w → ZMod 2) → ZMod 2))).filter (fun t =>
      ∃ a ∈ A,
        (∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
            (fun S => S.card ≤ w),
          c a S * ∏ j ∈ S, bitf (fun a => (p a).1) (fun a => (p a).2 + t.2 (p a).1) t.1 j)
        ≠ ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i)).card := by
  classical
  set T := ((Finset.univ : Finset ((Fin w → ZMod 2) × ((Fin w → ZMod 2) → ZMod 2))).filter (fun t =>
      ∃ a ∈ A,
        (∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
            (fun S => S.card ≤ w),
          c a S * ∏ j ∈ S, bitf (fun a => (p a).1) (fun a => (p a).2 + t.2 (p a).1) t.1 j)
        ≠ ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i)) with hT
  let G : ((Fin w → ZMod 2) × ZMod 2) → (((Fin w → ZMod 2) × ZMod 2) → ZMod 2) → ZMod 2 :=
    fun a nb => ∑ u : Fin w → ZMod 2,
      ∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
            (fun S => S.card ≤ w),
          c a S * ∏ j ∈ S, bitf (fun a => (p a).1) nb u j
  have hG : ∀ a nb nb', G a nb = G a nb' := by
    intro a nb nb'
    show (∑ u : Fin w → ZMod 2, ∑ S ∈ _, _) = ∑ u : Fin w → ZMod 2, ∑ S ∈ _, _
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ)]
    apply Finset.sum_congr rfl
    intro S hS
    rw [← Finset.mul_sum, ← Finset.mul_sum, mono _ S (Finset.mem_filter.1 hS).2 nb nb']
  let C : ((Fin w → ZMod 2) × ZMod 2) → ZMod 2 := fun a => G a (fun _ => 0)
  have key : ∀ b : (Fin w → ZMod 2) → ZMod 2, (∀ u, (u, b) ∉ T) →
      ∀ a ∈ A, b (p a).1 = (p a).2 + C a := by
    intro b hb a ha
    have h1 : G a (fun a => (p a).2 + b (p a).1) =
        ∑ u : Fin w → ZMod 2, ((p a).2 + b (p a).1) * ∏ i : Fin w, ((p a).1 + u) i := by
      apply Finset.sum_congr rfl
      intro u _
      have := hb u
      rw [hT] at this
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and, not_not] at this
      exact this a ha
    rw [← Finset.mul_sum, sum_target, mul_one, hG a _ (fun _ => 0)] at h1
    show _ = _ + G a (fun _ => 0)
    rw [h1, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  set Bs := (Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)).filter
    (fun b => ¬ ∀ a ∈ A, b (p a).1 = (p a).2 + C a) with hBs
  set Gs := (Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)).filter
    (fun b => ∀ a ∈ A, b (p a).1 = (p a).2 + C a) with hGs
  have h1 : Bs.card ≤ T.card := by
    refine (Finset.card_le_card ?_).trans (Finset.card_image_le (f := Prod.snd))
    intro b hb
    by_contra hn
    rw [hBs, Finset.mem_filter] at hb
    apply hb.2
    apply key b
    intro u hu
    exact hn (Finset.mem_image.2 ⟨(u, b), hu, rfl⟩)
  have h2 : Gs.card + Bs.card = 2 ^ (2 ^ w) := by
    rw [hGs, hBs, Finset.card_filter_add_card_filter_not]
    simp
  have h3 : Gs.card ≤ 2 ^ (2 ^ w - (A.image (fun a => (p a).1)).card) := by
    by_cases he : Gs = ∅
    · rw [he]; simp
    · obtain ⟨b0, hb0⟩ := Finset.nonempty_iff_ne_empty.2 he
      rw [← cardGood (A.image (fun a => (p a).1)) b0]
      apply Finset.card_le_card
      intro b hb
      rw [hGs, Finset.mem_filter] at hb hb0
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      show b (p a).1 = b0 (p a).1
      rw [hb.2 a ha, hb0.2 a ha]
  generalize (2 : ℕ) ^ (2 ^ w) = N at *
  generalize (2 : ℕ) ^ (_ : ℕ) = P at *
  omega

def cdef {w : ℕ} (x : Fin w → ZMod 2) (y : ZMod 2) (a : (Fin w → ZMod 2) × ZMod 2)
    (S : Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w))) : ZMod 2 :=
  (∑ T : Finset (Fin w), if S = T.image (fun i => (a, some i))
      then y * ∏ i ∈ Finset.univ \ T, (1 + x i) else 0) +
  (∑ T : Finset (Fin w), if S = insert (a, none) (T.image (fun i => (a, some i)))
      then (if T = Finset.univ then 0 else ∏ i ∈ Finset.univ \ T, (1 + x i)) else 0)

lemma expand {w : ℕ} {I : Type*} [DecidableEq I] (F : Finset (Finset I))
    (ι : Finset (Fin w) → Finset I) (v : Finset (Fin w) → ZMod 2) (m : Finset I → ZMod 2)
    (h : ∀ T, v T ≠ 0 → ι T ∈ F) :
    ∑ S ∈ F, (∑ T : Finset (Fin w), if S = ι T then v T else 0) * m S
      = ∑ T : Finset (Fin w), v T * m (ι T) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · have : v T = 0 := by
      by_contra hv
      exact hm (h T hv)
    rw [this, zero_mul]

lemma sharp_eval {w : ℕ} (xf : ((Fin w → ZMod 2) × ZMod 2) → (Fin w → ZMod 2))
    (nb : ((Fin w → ZMod 2) × ZMod 2) → ZMod 2) (u : Fin w → ZMod 2)
    (a : (Fin w → ZMod 2) × ZMod 2) (ya : ZMod 2) :
    ∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
        (fun S => S.card ≤ w), cdef (xf a) ya a S * ∏ j ∈ S, bitf xf nb u j
      = (ya + nb a) * ∏ i : Fin w, (1 + u i) + nb a * ∏ i : Fin w, (xf a + u) i := by
  have hinj : Function.Injective
      (fun i : Fin w => (((a, some i)) : ((Fin w → ZMod 2) × ZMod 2) × Option (Fin w))) := by
    intro i i' e
    simpa using e
  have hm1 : ∀ T : Finset (Fin w), ∏ j ∈ T.image (fun i => (a, some i)), bitf xf nb u j
      = ∏ i ∈ T, (xf a + u) i := by
    intro T
    rw [Finset.prod_image (fun i _ i' _ e => hinj e)]
    rfl
  have hm2 : ∀ T : Finset (Fin w),
      ∏ j ∈ insert (a, none) (T.image (fun i => (a, some i))), bitf xf nb u j
      = nb a * ∏ i ∈ T, (xf a + u) i := by
    intro T
    rw [Finset.prod_insert (by simp), hm1]
    rfl
  have hexp : ∏ i : Fin w, (1 + u i)
      = ∑ T : Finset (Fin w), (∏ i ∈ T, (xf a + u) i) * ∏ i ∈ Finset.univ \ T, (1 + xf a i) := by
    have := Finset.prod_add (fun i => (xf a + u) i) (fun i => 1 + xf a i) (Finset.univ : Finset (Fin w))
    rw [Finset.powerset_univ] at this
    rw [← this]
    apply Finset.prod_congr rfl
    intro i _
    simp only [Pi.add_apply]
    have := CharTwo.add_self_eq_zero (xf a i)
    linear_combination -this
  unfold cdef
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [expand _ (fun T => T.image (fun i => (a, some i))) _ (fun S => ∏ j ∈ S, bitf xf nb u j),
    expand _ (fun T => insert (a, none) (T.image (fun i => (a, some i)))) _
      (fun S => ∏ j ∈ S, bitf xf nb u j)]
  · simp_rw [hm1, hm2]
    have h3 : ∀ T : Finset (Fin w),
        (if T = Finset.univ then 0 else ∏ i ∈ Finset.univ \ T, (1 + xf a i)) *
          (nb a * ∏ i ∈ T, (xf a + u) i)
        = nb a * ((∏ i ∈ T, (xf a + u) i) * ∏ i ∈ Finset.univ \ T, (1 + xf a i))
          - (if T = Finset.univ then
              nb a * ((∏ i ∈ T, (xf a + u) i) * ∏ i ∈ Finset.univ \ T, (1 + xf a i)) else 0) := by
      intro T
      split_ifs <;> ring
    simp_rw [h3]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', ← Finset.mul_sum, ← hexp]
    simp only [Finset.mem_univ, ite_true, sdiff_self, Finset.bot_eq_empty, Finset.prod_empty, mul_one]
    have h4 : ∑ T : Finset (Fin w), ya * ((∏ i ∈ Finset.univ \ T, (1 + xf a i)) * ∏ i ∈ T, (xf a + u) i)
        = ya * ∏ i : Fin w, (1 + u i) := by
      rw [hexp, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      ring
    simp only [mul_assoc]
    rw [h4, CharTwo.sub_eq_add]
    ring
  · intro T hT
    have hne : T ≠ Finset.univ := by
      intro e
      simp [e] at hT
    have hlt : T.card < w := by
      have := Finset.card_lt_card (Finset.ssubset_univ_iff.2 hne)
      simpa using this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ hinj]
    omega
  · intro T _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [Finset.card_image_of_injective _ hinj]
    simpa using Finset.card_le_univ T

lemma sharp {w : ℕ} (p : Equiv.Perm ((Fin w → ZMod 2) × ZMod 2)) :
    ∃ c : ((Fin w → ZMod 2) × ZMod 2) →
      Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)) → ZMod 2,
    ∀ A : Finset ((Fin w → ZMod 2) × ZMod 2),
    ((Finset.univ : Finset ((Fin w → ZMod 2) × ((Fin w → ZMod 2) → ZMod 2))).filter (fun t =>
      ∃ a ∈ A,
        (∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
            (fun S => S.card ≤ w),
          c a S * ∏ j ∈ S, bitf (fun a => (p a).1) (fun a => (p a).2 + t.2 (p a).1) t.1 j)
        ≠ ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i)).card
      = 2 ^ (2 ^ w) - 2 ^ (2 ^ w - (A.image (fun a => (p a).1)).card) := by
  refine ⟨fun a S => cdef (p a).1 (p a).2 a S, fun A => ?_⟩
  have hper : ∀ (t : (Fin w → ZMod 2) × ((Fin w → ZMod 2) → ZMod 2))
      (a : (Fin w → ZMod 2) × ZMod 2),
      ((∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
            (fun S => S.card ≤ w),
          cdef (p a).1 (p a).2 a S *
            ∏ j ∈ S, bitf (fun a => (p a).1) (fun a => (p a).2 + t.2 (p a).1) t.1 j)
        ≠ ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i)
      ↔ (t.2 (p a).1 ≠ 0 ∧ t.1 = 0) := by
    intro t a
    have := sharp_eval (fun a => (p a).1) (fun a => (p a).2 + t.2 (p a).1) t.1 a (p a).2
    beta_reduce at this
    rw [this]
    have e : ((p a).2 + ((p a).2 + t.2 (p a).1)) * ∏ i : Fin w, (1 + t.1 i)
        + ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i
        = ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i
          + t.2 (p a).1 * ∏ i : Fin w, (1 + t.1 i) := by
      have := CharTwo.add_self_eq_zero (p a).2
      linear_combination (∏ i : Fin w, (1 + t.1 i)) * this
    rw [e]
    have hz : ∀ v : ZMod 2, 1 + v ≠ 0 ↔ v = 0 := by decide
    simp only [ne_eq, add_eq_left, mul_eq_zero, not_or, Finset.prod_eq_zero_iff, Finset.mem_univ,
      true_and, not_exists]
    apply and_congr Iff.rfl
    constructor
    · intro h; ext i; exact (hz _).1 (h i)
    · intro h i; exact (hz _).2 (by rw [h]; rfl)
  have hset : ((Finset.univ : Finset ((Fin w → ZMod 2) × ((Fin w → ZMod 2) → ZMod 2))).filter (fun t =>
      ∃ a ∈ A,
        (∑ S ∈ (Finset.univ : Finset (Finset (((Fin w → ZMod 2) × ZMod 2) × Option (Fin w)))).filter
            (fun S => S.card ≤ w),
          cdef (p a).1 (p a).2 a S *
            ∏ j ∈ S, bitf (fun a => (p a).1) (fun a => (p a).2 + t.2 (p a).1) t.1 j)
        ≠ ((p a).2 + t.2 (p a).1) * ∏ i : Fin w, ((p a).1 + t.1) i))
      = ((Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)).filter
          (fun b => ¬ ∀ x ∈ A.image (fun a => (p a).1), b x = (fun _ => 0) x)).image
          (fun b => ((0 : Fin w → ZMod 2), b)) := by
    ext ⟨u, b⟩
    simp only [hper]
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, a, ha, hne, h0⟩
      simp only at h0 hne
      subst h0
      exact ⟨b, Finset.mem_filter.2 ⟨Finset.mem_univ _,
        fun h => hne (h _ (Finset.mem_image_of_mem _ ha))⟩, rfl⟩
    · rintro ⟨b', hb', e⟩
      cases e
      refine ⟨Finset.mem_univ _, ?_⟩
      by_contra hc
      apply (Finset.mem_filter.1 hb').2
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      by_contra hne
      exact hc ⟨a, ha, hne, rfl⟩
  rw [hset, Finset.card_image_of_injective _ (fun b b' e => (Prod.mk.inj e).2)]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)))
    (fun b => ∀ x ∈ A.image (fun a => (p a).1), b x = (fun _ => (0 : ZMod 2)) x)
  rw [cardGood] at h2
  have h3 : (Finset.univ : Finset ((Fin w → ZMod 2) → ZMod 2)).card = 2 ^ (2 ^ w) := by simp
  omega

end PEqualNP.Outside.L_lib_671_aux

theorem PEqualNP.Outside.L_lib_671 : ∀ w : ℕ,
  let K := ZMod 2
  let X := Fin w → K
  let V := X × K
  let I := V × Option (Fin w)
  let s := 2^w
  let coeff := V → Finset I → K
  ∀ p : Equiv.Perm V,
    let raw := fun (u : X) (b : X → K) (a : V) =>
      ((p a).1 + u, (p a).2 + b (p a).1)
    let bad := fun (c : coeff) (A : Finset V) =>
      ((Finset.univ : Finset (X × (X → K))).filter (fun t =>
        let z := raw t.1 t.2
        let bit := fun j : I => j.2.elim (z j.1).2 (fun i => (z j.1).1 i)
        ∃ a ∈ A,
          (∑ S ∈ (Finset.univ : Finset (Finset I)).filter (fun S => S.card ≤ w),
            c a S * ∏ j ∈ S, bit j) ≠ (z a).2 * ∏ i : Fin w, (z a).1 i)).card
    let bound := fun (A : Finset V) =>
      2^s - 2^(s - (A.image (fun a => (p a).1)).card)
    (∀ (c : coeff) (A : Finset V), bound A ≤ bad c A) ∧
      ∃ c : coeff, ∀ A : Finset V, bad c A = bound A := by
  intro w K X V I s coeff p raw bad bound
  refine ⟨fun c A => PEqualNP.Outside.L_lib_671_aux.lower p c A,
    PEqualNP.Outside.L_lib_671_aux.sharp p⟩
