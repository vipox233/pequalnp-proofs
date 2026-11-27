import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_442_aux

lemma sq_sum_le_card_mul_sum_sq {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ a ∈ s, f a) ^ 2 ≤ s.card * ∑ a ∈ s, (f a) ^ 2 := by
  have hnonneg : (0 : ℤ) ≤ ∑ a ∈ s, ∑ b ∈ s, ((f a : ℤ) - (f b : ℤ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hexp :
      (∑ a ∈ s, ∑ b ∈ s, ((f a : ℤ) - (f b : ℤ)) ^ 2) =
        2 * (s.card : ℤ) * (∑ a ∈ s, (f a : ℤ) ^ 2) - 2 * (∑ a ∈ s, (f a : ℤ)) ^ 2 := by
    have h1 : ∀ a : α,
        (∑ b ∈ s, ((f a : ℤ) - (f b : ℤ)) ^ 2) =
          (s.card : ℤ) * (f a : ℤ) ^ 2 - 2 * (f a : ℤ) * (∑ b ∈ s, (f b : ℤ)) +
            ∑ b ∈ s, (f b : ℤ) ^ 2 := by
      intro a
      calc
        (∑ b ∈ s, ((f a : ℤ) - (f b : ℤ)) ^ 2)
            = ∑ b ∈ s, ((f a : ℤ) ^ 2 - 2 * (f a : ℤ) * (f b : ℤ) + (f b : ℤ) ^ 2) := by
              refine Finset.sum_congr rfl (fun b _ => by ring)
        _ = (∑ _b ∈ s, (f a : ℤ) ^ 2) - (∑ b ∈ s, 2 * (f a : ℤ) * (f b : ℤ)) +
              ∑ b ∈ s, (f b : ℤ) ^ 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = (s.card : ℤ) * (f a : ℤ) ^ 2 - 2 * (f a : ℤ) * (∑ b ∈ s, (f b : ℤ)) +
              ∑ b ∈ s, (f b : ℤ) ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    calc
      (∑ a ∈ s, ∑ b ∈ s, ((f a : ℤ) - (f b : ℤ)) ^ 2)
          = ∑ a ∈ s, ((s.card : ℤ) * (f a : ℤ) ^ 2 - 2 * (f a : ℤ) * (∑ b ∈ s, (f b : ℤ)) +
              ∑ b ∈ s, (f b : ℤ) ^ 2) := Finset.sum_congr rfl (fun a _ => h1 a)
      _ = (∑ a ∈ s, (s.card : ℤ) * (f a : ℤ) ^ 2) -
            (∑ a ∈ s, 2 * (f a : ℤ) * (∑ b ∈ s, (f b : ℤ))) +
            ∑ _a ∈ s, ∑ b ∈ s, (f b : ℤ) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (s.card : ℤ) * (∑ a ∈ s, (f a : ℤ) ^ 2) -
            (2 * (∑ a ∈ s, (f a : ℤ)) * (∑ b ∈ s, (f b : ℤ))) +
            (s.card : ℤ) * (∑ b ∈ s, (f b : ℤ) ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
            have hmid :
                (∑ a ∈ s, 2 * (f a : ℤ) * (∑ b ∈ s, (f b : ℤ))) =
                  2 * (∑ a ∈ s, (f a : ℤ)) * (∑ b ∈ s, (f b : ℤ)) := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
            rw [hmid]
      _ = 2 * (s.card : ℤ) * (∑ a ∈ s, (f a : ℤ) ^ 2) - 2 * (∑ a ∈ s, (f a : ℤ)) ^ 2 := by
            ring
  have hint : (∑ a ∈ s, (f a : ℤ)) ^ 2 ≤ (s.card : ℤ) * (∑ a ∈ s, (f a : ℤ) ^ 2) := by
    linarith
  exact_mod_cast hint

lemma sum_X_eq {u d q : ℕ} (S : Finset (Fin u)) (h : Fin d → Fin u → Fin q) (target : Fin q) :
    (∑ s : Fin d, (S.filter (fun x => h s x = target)).card) =
      ∑ x ∈ S, (Finset.univ.filter (fun s : Fin d => h s x = target)).card := by
  calc
    (∑ s : Fin d, (S.filter (fun x => h s x = target)).card)
        = ∑ s : Fin d, ∑ x ∈ S, (if h s x = target then 1 else 0) := by
          refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [Finset.card_filter]
    _ = ∑ x ∈ S, ∑ s : Fin d, (if h s x = target then 1 else 0) := Finset.sum_comm
    _ = ∑ x ∈ S, (Finset.univ.filter (fun s : Fin d => h s x = target)).card := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [Finset.card_filter]

lemma sum_X_sq_eq {u d q : ℕ} (S : Finset (Fin u)) (h : Fin d → Fin u → Fin q) (target : Fin q) :
    (∑ s : Fin d, ((S.filter (fun x => h s x = target)).card) ^ 2) =
      (∑ x ∈ S, (Finset.univ.filter (fun s : Fin d => h s x = target)).card) +
        ∑ x ∈ S, ∑ z ∈ S.erase x,
          (Finset.univ.filter (fun s : Fin d => h s x = target ∧ h s z = target)).card := by
  have hterm : ∀ s : Fin d,
      ((S.filter (fun x => h s x = target)).card) ^ 2 =
        (∑ x ∈ S, (if h s x = target then 1 else 0)) +
          ∑ x ∈ S, ∑ z ∈ S.erase x, (if h s x = target ∧ h s z = target then 1 else 0) := by
    intro s
    have hsq : ((S.filter (fun x => h s x = target)).card) ^ 2 =
        ∑ x ∈ S, ∑ z ∈ S, (if h s x = target ∧ h s z = target then 1 else 0) := by
      rw [sq, Finset.card_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      by_cases hx : h s x = target <;> by_cases hz : h s z = target <;> simp [hx, hz]
    rw [hsq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [← Finset.add_sum_erase S (fun z => if h s x = target ∧ h s z = target then 1 else 0) hx]
    simp
  calc
    (∑ s : Fin d, ((S.filter (fun x => h s x = target)).card) ^ 2)
        = ∑ s : Fin d, ((∑ x ∈ S, (if h s x = target then 1 else 0)) +
            ∑ x ∈ S, ∑ z ∈ S.erase x, (if h s x = target ∧ h s z = target then 1 else 0)) :=
          Finset.sum_congr rfl (fun s _ => hterm s)
    _ = (∑ s : Fin d, ∑ x ∈ S, (if h s x = target then 1 else 0)) +
          ∑ s : Fin d, ∑ x ∈ S, ∑ z ∈ S.erase x,
            (if h s x = target ∧ h s z = target then 1 else 0) := Finset.sum_add_distrib
    _ = (∑ x ∈ S, (Finset.univ.filter (fun s : Fin d => h s x = target)).card) +
          ∑ x ∈ S, ∑ z ∈ S.erase x,
            (Finset.univ.filter (fun s : Fin d => h s x = target ∧ h s z = target)).card := by
          congr 1
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.card_filter]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun x _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun z _ => ?_)
            rw [Finset.card_filter]

theorem main (u d q : ℕ) (S : Finset (Fin u)) (h : Fin d → Fin u → Fin q) (hq : 0 < q)
    (h1 : ∀ (x : Fin u) (a : Fin q), q * (Finset.univ.filter (fun s : Fin d => h s x = a)).card = d)
    (h2 : ∀ (x z : Fin u), x ≠ z → ∀ a b : Fin q,
      q ^ 2 * (Finset.univ.filter (fun s : Fin d => h s x = a ∧ h s z = b)).card = d)
    (target : Fin q) :
    let occupied := (Finset.univ.filter (fun s : Fin d => ∃ x ∈ S, h s x = target)).card
    d * S.card ≤ occupied * (q + S.card - 1) ∧ q * occupied ≤ d * S.card := by
  intro occupied
  set O : Finset (Fin d) := Finset.univ.filter (fun s : Fin d => ∃ x ∈ S, h s x = target)
  set X : Fin d → ℕ := fun s => (S.filter (fun x => h s x = target)).card
  have hfirst : q * ∑ s : Fin d, X s = d * S.card := by
    rw [sum_X_eq, Finset.mul_sum]
    calc
      (∑ x ∈ S, q * (Finset.univ.filter (fun s : Fin d => h s x = target)).card)
          = ∑ _x ∈ S, d := Finset.sum_congr rfl (fun x _ => h1 x target)
      _ = S.card * d := by rw [Finset.sum_const, smul_eq_mul]
      _ = d * S.card := Nat.mul_comm _ _
  have hupper : q * occupied ≤ d * S.card := by
    have hO_le : O.card ≤ ∑ s : Fin d, X s := by
      calc
        O.card = ∑ _s ∈ O, 1 := by simp
        _ ≤ ∑ s ∈ O, X s := by
          refine Finset.sum_le_sum (fun s hs => ?_)
          have hs' : ∃ x ∈ S, h s x = target := (Finset.mem_filter.mp hs).2
          rcases hs' with ⟨x, hxS, hxe⟩
          exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, hxe⟩⟩
        _ ≤ ∑ s : Fin d, X s :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    calc
      q * occupied = q * O.card := rfl
      _ ≤ q * ∑ s : Fin d, X s := Nat.mul_le_mul_left q hO_le
      _ = d * S.card := hfirst
  refine ⟨?_, hupper⟩
  by_cases hM : S.card = 0
  · simp [hM]
  by_cases hd : d = 0
  · simp [hd]
  have hMpos : 0 < S.card := Nat.pos_of_ne_zero hM
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hsumO : ∑ s : Fin d, X s = ∑ s ∈ O, X s := by
    symm
    refine Finset.sum_subset (Finset.subset_univ O) (fun s _ hsO => ?_)
    have hne : ¬ ∃ x ∈ S, h s x = target := by
      intro hex
      exact hsO (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hex⟩)
    exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun x hx hxe => hne ⟨x, hx, hxe⟩))
  have hsumO2 : ∑ s : Fin d, (X s) ^ 2 = ∑ s ∈ O, (X s) ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ O) (fun s _ hsO => ?_)
    have hne : ¬ ∃ x ∈ S, h s x = target := by
      intro hex
      exact hsO (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hex⟩)
    have hX0 : X s = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr (fun x hx hxe => hne ⟨x, hx, hxe⟩))
    simp [hX0]
  have hsecond : q ^ 2 * ∑ s : Fin d, (X s) ^ 2 = d * S.card * (q + S.card - 1) := by
    rw [sum_X_sq_eq, Nat.mul_add]
    have hdiag :
        q ^ 2 * (∑ x ∈ S, (Finset.univ.filter (fun s : Fin d => h s x = target)).card) =
          d * S.card * q := by
      rw [sq, Nat.mul_assoc, ← sum_X_eq, hfirst]
      ring
    have hoff :
        q ^ 2 * (∑ x ∈ S, ∑ z ∈ S.erase x,
          (Finset.univ.filter (fun s : Fin d => h s x = target ∧ h s z = target)).card) =
          d * S.card * (S.card - 1) := by
      rw [Finset.mul_sum]
      calc
        (∑ x ∈ S, q ^ 2 * ∑ z ∈ S.erase x,
            (Finset.univ.filter (fun s : Fin d => h s x = target ∧ h s z = target)).card)
            = ∑ x ∈ S, ∑ z ∈ S.erase x,
                q ^ 2 * (Finset.univ.filter (fun s : Fin d => h s x = target ∧ h s z = target)).card := by
              refine Finset.sum_congr rfl (fun x _ => Finset.mul_sum _ _ _)
        _ = ∑ x ∈ S, ∑ _z ∈ S.erase x, d := by
              refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun z hz => ?_))
              exact h2 x z (Ne.symm (Finset.ne_of_mem_erase hz)) target target
        _ = ∑ x ∈ S, (S.card - 1) * d := by
              refine Finset.sum_congr rfl (fun x hx => ?_)
              rw [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx]
        _ = S.card * ((S.card - 1) * d) := by rw [Finset.sum_const, smul_eq_mul]
        _ = d * S.card * (S.card - 1) := by ring
    rw [hdiag, hoff, ← Nat.mul_add]
    congr 1
    omega
  have hcs : (∑ s : Fin d, X s) ^ 2 ≤ occupied * ∑ s : Fin d, (X s) ^ 2 := by
    rw [hsumO, hsumO2]
    exact sq_sum_le_card_mul_sum_sq O X
  have hmul : (d * S.card) ^ 2 ≤ d * S.card * (occupied * (q + S.card - 1)) := by
    have h1' : q ^ 2 * (∑ s : Fin d, X s) ^ 2 ≤ q ^ 2 * (occupied * ∑ s : Fin d, (X s) ^ 2) :=
      Nat.mul_le_mul_left (q ^ 2) hcs
    have hlhs : q ^ 2 * (∑ s : Fin d, X s) ^ 2 = (d * S.card) ^ 2 := by
      rw [← mul_pow, hfirst]
    have hrhs : q ^ 2 * (occupied * ∑ s : Fin d, (X s) ^ 2) =
        d * S.card * (occupied * (q + S.card - 1)) := by
      calc
        q ^ 2 * (occupied * ∑ s : Fin d, (X s) ^ 2)
            = occupied * (q ^ 2 * ∑ s : Fin d, (X s) ^ 2) := by ring
        _ = occupied * (d * S.card * (q + S.card - 1)) := by rw [hsecond]
        _ = d * S.card * (occupied * (q + S.card - 1)) := by ring
    rw [hlhs, hrhs] at h1'
    exact h1'
  have hpos : 0 < d * S.card := Nat.mul_pos hdpos hMpos
  rw [sq] at hmul
  exact Nat.le_of_mul_le_mul_left hmul hpos

end PEqualNP.Outside.L_lib_442_aux

theorem PEqualNP.Outside.L_lib_442 :
    ∀ (u d q : Nat) (S : Finset (Fin u)) (h : Fin d → Fin u → Fin q), 0 < q →
      (∀ (x : Fin u) (a : Fin q), q * (Finset.univ.filter (fun s : Fin d => h s x = a)).card = d) →
      (∀ (x z : Fin u), x ≠ z → ∀ a b : Fin q,
        q^2 * (Finset.univ.filter (fun s : Fin d => h s x = a ∧ h s z = b)).card = d) →
      ∀ target : Fin q,
        let occupied := (Finset.univ.filter (fun s : Fin d => ∃ x ∈ S, h s x = target)).card
        d*S.card ≤ occupied*(q+S.card-1) ∧ q*occupied ≤ d*S.card :=
  PEqualNP.Outside.L_lib_442_aux.main
