import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_713

def sg (b : Bool) : ℤ := if b then -1 else 1

lemma sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma four_ind (a b h p q : Bool) :
    4 * (if (Bool.xor a h = p ∧ Bool.xor b h = q) then (1:ℤ) else 0) =
      1 + sg p * (sg a * sg h) + sg q * (sg b * sg h) + sg p * sg q * (sg a * sg b) := by
  cases a <;> cases b <;> cases h <;> cases p <;> cases q <;> simp [sg]

lemma prod_ind (a b : Bool) : sg a * sg b = 1 - 2 * (if a ≠ b then (1:ℤ) else 0) := by
  cases a <;> cases b <;> simp [sg]

lemma orth {m : ℕ} (f g : Fin m → Bool)
    (h : 2 * ((Finset.univ : Finset (Fin m)).filter (fun x => f x ≠ g x)).card = m) :
    ∑ x, sg (f x) * sg (g x) = 0 := by
  simp only [prod_ind, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [← Finset.natCast_card_filter]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have : (2 * ((Finset.univ : Finset (Fin m)).filter (fun x => f x ≠ g x)).card : ℤ) = m := by
    exact_mod_cast h
  linarith

lemma pair_count {m : ℕ} (f g H : Fin m → Bool) (p q : Bool)
    (h0 : ∑ x, sg (f x) * sg (g x) = 0) :
    4 * (((Finset.univ : Finset (Fin m)).filter (fun x =>
        Bool.xor (f x) (H x) = p ∧ Bool.xor (g x) (H x) = q)).card : ℤ) =
      m + sg p * ∑ x, sg (f x) * sg (H x) + sg q * ∑ x, sg (g x) * sg (H x) := by
  rw [Finset.natCast_card_filter, Finset.mul_sum]
  simp only [four_ind, Finset.sum_add_distrib, ← Finset.mul_sum, h0]
  simp

lemma bessel {ι : Type} {m : ℕ} (W : Finset ι) (g : ι → Fin m → Bool) (H : Fin m → Bool)
    (horth : ∀ u ∈ W, ∀ v ∈ W, u ≠ v → ∑ x, sg (g u x) * sg (g v x) = 0) :
    ∑ w ∈ W, (∑ x, sg (g w x) * sg (H x))^2 ≤ (m:ℤ)^2 := by
  set c : ι → ℤ := fun w => ∑ x, sg (g w x) * sg (H x) with hc
  set S := ∑ w ∈ W, c w ^ 2 with hS
  change S ≤ _
  set B : Fin m → ℤ := fun x => ∑ w ∈ W, c w * sg (g w x) with hB
  have hAB : ∑ x, sg (H x) * B x = S := by
    simp only [hB, Finset.mul_sum, hS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [sq, hc]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  have hself : ∀ w, ∑ x, sg (g w x) * sg (g w x) = (m:ℤ) := by
    intro w; simp [sg_sq]
  have hBB : ∑ x, B x * B x = (m:ℤ) * S := by
    have : ∀ x, B x * B x = ∑ w ∈ W, ∑ w' ∈ W, c w * c w' * (sg (g w x) * sg (g w' x)) := by
      intro x; simp only [hB, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun w _ => Finset.sum_congr rfl (fun w' _ => ?_)); ring
    simp only [this]
    rw [Finset.sum_comm]
    have : ∀ w ∈ W, ∑ x, ∑ w' ∈ W, c w * c w' * (sg (g w x) * sg (g w' x)) = (m:ℤ) * c w ^ 2 := by
      intro w hw
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum]
      rw [Finset.sum_eq_single w]
      · rw [hself]; ring
      · intro w' hw' hne; rw [horth w hw w' hw' (Ne.symm hne)]; ring
      · intro h; exact absurd hw h
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  have h0 : 0 ≤ ∑ x, ((m:ℤ) * sg (H x) - B x)^2 := Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hexp : ∑ x, ((m:ℤ) * sg (H x) - B x)^2 =
      (m:ℤ)^2 * ∑ x, sg (H x) * sg (H x) - 2 * m * ∑ x, sg (H x) * B x + ∑ x, B x * B x := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_); ring
  have hHH : ∑ x, sg (H x) * sg (H x) = (m:ℤ) := by simp [sg_sq]
  rw [hexp, hHH, hAB, hBB] at h0
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have : S = 0 := by
      simp [hS, hc]
    simp [this]
  · have hm' : (0:ℤ) < m := by exact_mod_cast hm
    nlinarith

end PEqualNP.Outside.L_lib_713


theorem PEqualNP.Outside.L_lib_713 : ∀ (n m l : ℕ) (F : Fin n → Fin m → Bool),
  (∀ u v : Fin n, u ≠ v →
    2*((Finset.univ : Finset (Fin m)).filter (fun x => F u x ≠ F v x)).card = m) →
  ∀ (name : Fin l × Bool ↪ Fin n) (H : Fin m → Bool) (p q : Fin l → Bool),
    let e := ∑ i : Fin l, ((Finset.univ : Finset (Fin m)).filter (fun x =>
      Bool.xor (F (name (i,false)) x) (H x) = p i ∧
      Bool.xor (F (name (i,true)) x) (H x) = q i)).card
    (4*(e : ℤ) - (m : ℤ)*(l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 ∧
      m*l ≤ 2*m + 8*e := by
  intro n m l F horth name H p q e
  open PEqualNP.Outside.L_lib_713 in
  have key : 4 * (e : ℤ) - (m : ℤ) * (l : ℤ) =
      ∑ k : Fin l × Bool, (if k.2 then sg (q k.1) else sg (p k.1)) *
        ∑ x, sg (F (name k) x) * sg (H x) := by
    have he : (e : ℤ) = ∑ i : Fin l, (((Finset.univ : Finset (Fin m)).filter (fun x =>
        Bool.xor (F (name (i,false)) x) (H x) = p i ∧
        Bool.xor (F (name (i,true)) x) (H x) = q i)).card : ℤ) := by
      simp [e]
    rw [he, Finset.mul_sum]
    have hpair : ∀ i : Fin l, 4 * (((Finset.univ : Finset (Fin m)).filter (fun x =>
        Bool.xor (F (name (i,false)) x) (H x) = p i ∧
        Bool.xor (F (name (i,true)) x) (H x) = q i)).card : ℤ) =
        m + sg (p i) * ∑ x, sg (F (name (i,false)) x) * sg (H x)
          + sg (q i) * ∑ x, sg (F (name (i,true)) x) * sg (H x) := by
      intro i
      apply pair_count
      apply orth
      apply horth
      intro h; have := name.injective h; simp at this
    simp only [hpair, Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_bool]
    simp
    ring
  open PEqualNP.Outside.L_lib_713 in
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin l × Bool))
    (fun k => (if k.2 then sg (q k.1) else sg (p k.1)))
    (fun k => ∑ x, sg (F (name k) x) * sg (H x))
  open PEqualNP.Outside.L_lib_713 in
  have ht : ∑ k : Fin l × Bool, (if k.2 then sg (q k.1) else sg (p k.1))^2 = 2 * (l:ℤ) := by
    have : ∀ k : Fin l × Bool, (if k.2 then sg (q k.1) else sg (p k.1))^2 = 1 := by
      intro k; split_ifs <;> simp [sq, sg_sq]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, mul_one]
    push_cast; ring
  open PEqualNP.Outside.L_lib_713 in
  have hB : ∑ k : Fin l × Bool, (∑ x, sg (F (name k) x) * sg (H x))^2 ≤ (m:ℤ)^2 := by
    have := bessel (Finset.univ.map name) F H (by
      intro u _ v _ huv
      exact orth _ _ (horth u v huv))
    simpa [Finset.sum_map] using this
  have h1 : (4 * (e : ℤ) - (m : ℤ) * (l : ℤ))^2 ≤ 2*(l : ℤ)*(m : ℤ)^2 := by
    rw [key]
    calc _ ≤ _ := hCS
      _ ≤ 2 * (l:ℤ) * (m:ℤ)^2 := by
        rw [ht]
        apply mul_le_mul_of_nonneg_left hB
        positivity
  refine ⟨h1, ?_⟩
  rcases le_or_gt (m*l) (2*m+8*e) with hle | hlt
  · exact hle
  exfalso
  have hlt' : (2 * (m:ℤ) + 8 * e) < (m:ℤ) * l := by exact_mod_cast hlt
  nlinarith [sq_nonneg ((m:ℤ) * ((l:ℤ) - 2)), sq_nonneg ((m:ℤ) * ((l:ℤ) + 2) + 2 * (4 * (e:ℤ) - m * l))]
