import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_837

open Finset

noncomputable def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_eq (a b : Bool) : (if a = b then (1:ℝ) else -1) = sg a * sg b := by
  cases a <;> cases b <;> simp [sg]

theorem sg_sq (a : Bool) : sg a * sg a = 1 := by cases a <;> simp [sg]

theorem sum_prod {m : ℕ} {q : Fin m → ℕ} (h : (i : Fin m) → Fin (q i) → ℝ) :
    ∑ x : ((i : Fin m) → Fin (q i)), ∏ i, h i (x i) = ∏ i, ∑ u, h i u :=
  (Fintype.prod_sum h).symm

theorem prod_ind {m : ℕ} {q : Fin m → ℕ} (c : Fin m → ℝ) (y z : (i : Fin m) → Fin (q i)) :
    ∏ i, (if y i = z i then c i else 0) = if y = z then ∏ i, c i else 0 := by
  by_cases h : y = z
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ z i := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem energy_gen {m : ℕ} {q : Fin m → ℕ} (h : (i : Fin m) → Fin (q i) → Fin (q i) → ℝ)
    (c : Fin m → ℝ) (hg : ∀ i v w, ∑ u, h i u v * h i u w = if v = w then c i else 0)
    (u : ((i : Fin m) → Fin (q i)) → ℝ) :
    ∑ x : ((i : Fin m) → Fin (q i)), (∑ y, (∏ i, h i (x i) (y i)) * u y) ^ 2
      = (∏ i, c i) * ∑ y, (u y) ^ 2 := by
  have e1 : ∀ x : ((i : Fin m) → Fin (q i)), (∑ y, (∏ i, h i (x i) (y i)) * u y) ^ 2
      = ∑ y, ∑ z, (∏ i, (h i (x i) (y i) * h i (x i) (z i))) * (u y * u z) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [e1]
  calc ∑ x : ((i : Fin m) → Fin (q i)), ∑ y, ∑ z,
        (∏ i, (h i (x i) (y i) * h i (x i) (z i))) * (u y * u z)
      = ∑ y : ((i : Fin m) → Fin (q i)), ∑ z : ((i : Fin m) → Fin (q i)),
          (∑ x : ((i : Fin m) → Fin (q i)), ∏ i, (h i (x i) (y i) * h i (x i) (z i)))
            * (u y * u z) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ y : ((i : Fin m) → Fin (q i)), ∑ z : ((i : Fin m) → Fin (q i)),
          (if y = z then ∏ i, c i else 0) * (u y * u z) := by
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
        have := sum_prod (q := q) (fun i a => h i a (y i) * h i a (z i))
        rw [this]
        simp_rw [hg]
        rw [prod_ind]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp [ite_mul, sq]

theorem gram (q : ℕ) (π : Equiv.Perm (Fin q)) (v w : Fin q) :
    ∑ u, ((if π u = v then ((q:ℝ)-2) else 2) * (if π u = v then (-1:ℝ) else 1)) *
      ((if π u = w then ((q:ℝ)-2) else 2) * (if π u = w then (-1:ℝ) else 1))
      = if v = w then (q:ℝ) ^ 2 else 0 := by
  have key : ∀ u t, ((if π u = t then ((q:ℝ)-2) else 2) * (if π u = t then (-1:ℝ) else 1))
      = 2 - (q:ℝ) * (if u = π.symm t then 1 else 0) := by
    intro u t
    by_cases h : π u = t
    · have h' : u = π.symm t := by rw [← h]; simp
      rw [if_pos h, if_pos h, if_pos h']
      ring
    · have h' : u ≠ π.symm t := by
        intro e
        apply h
        rw [e]
        simp
      rw [if_neg h, if_neg h, if_neg h']
      ring
  simp_rw [key]
  have e : ∀ u, (2 - (q:ℝ) * (if u = π.symm v then 1 else 0)) *
      (2 - (q:ℝ) * (if u = π.symm w then 1 else 0))
      = 4 - 2 * q * (if u = π.symm v then 1 else 0) - 2 * q * (if u = π.symm w then 1 else 0)
        + q ^ 2 * (if u = π.symm v then (if π.symm v = π.symm w then 1 else 0) else 0) := by
    intro u
    by_cases h1 : u = π.symm v
    · subst h1
      split_ifs <;> ring
    · rw [if_neg h1, if_neg h1]
      ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, nsmul_eq_mul]
  by_cases h : v = w
  · subst h
    simp only [if_true]
    ring
  · have : π.symm v ≠ π.symm w := fun e => h (π.symm.injective e)
    rw [if_neg this, if_neg h]
    ring

theorem row_sum (q : ℕ) (π : Equiv.Perm (Fin q)) (u : Fin q) :
    ∑ v, (if π u = v then ((q:ℝ)-2) else 2) = 3 * (q:ℝ) - 4 := by
  have e : ∀ v, (if π u = v then ((q:ℝ)-2) else 2) = 2 + (if π u = v then ((q:ℝ)-4) else 0) := by
    intro v
    split_ifs <;> ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, if_true,
    nsmul_eq_mul]
  ring

theorem col_sum (q : ℕ) (π : Equiv.Perm (Fin q)) (v : Fin q) :
    ∑ u, (if π u = v then ((q:ℝ)-2) else 2) = 3 * (q:ℝ) - 4 := by
  have e : ∀ u, (if π u = v then ((q:ℝ)-2) else 2)
      = 2 + (if u = π.symm v then ((q:ℝ)-4) else 0) := by
    intro u
    by_cases h : π u = v
    · rw [if_pos h, if_pos (by rw [← h]; simp)]
      ring
    · rw [if_neg h, if_neg (by intro e; apply h; rw [e]; simp)]
      ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, if_true,
    nsmul_eq_mul]
  ring

noncomputable def cc (q : ℕ) : Option (Fin q) → ℝ
  | none => ((q:ℝ) - 2) / q
  | some _ => 2

noncomputable def ff (q : ℕ) : Option (Fin q) → Fin q → ℝ
  | none, _ => 1
  | some k, u => (1:ℝ) / q - (if u = k then 1 else 0)

noncomputable def gg (q : ℕ) (π : Equiv.Perm (Fin q)) : Option (Fin q) → Fin q → ℝ
  | none, _ => 1
  | some k, v => (if v = π k then 1 else 0) - (1:ℝ) / q

noncomputable def nn (q : ℕ) : Option (Fin q) → ℝ
  | none => q
  | some _ => 1 - 1 / (q:ℝ)

theorem sum_perm_ind (q : ℕ) (π : Equiv.Perm (Fin q)) (v : Fin q) :
    ∑ k, (if v = π k then (1:ℝ) else 0) = 1 := by
  have := Equiv.sum_comp π (fun t => if v = t then (1:ℝ) else 0)
  rw [this]
  simp

theorem decomp (q : ℕ) (hq : 3 ≤ q) (π : Equiv.Perm (Fin q)) (u v : Fin q) :
    ∑ k, cc q k * ff q k u * gg q π k v = if π u = v then (-1:ℝ) else 1 := by
  have hq0 : (q:ℝ) ≠ 0 := by
    have : (3:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [Fintype.sum_option]
  simp only [cc, ff, gg]
  have e : ∀ k : Fin q, 2 * ((1:ℝ) / q - (if u = k then 1 else 0)) *
      ((if v = π k then 1 else 0) - (1:ℝ) / q)
      = (2 / q) * (if v = π k then 1 else 0) - 2 / q ^ 2 + (2 / q) * (if u = k then 1 else 0)
        - 2 * (if u = k then (if v = π u then 1 else 0) else 0) := by
    intro k
    by_cases h1 : u = k
    · subst h1
      split_ifs <;> field_simp <;> ring
    · rw [if_neg h1, if_neg h1]
      split_ifs <;> field_simp <;> ring
  simp_rw [e]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, sum_perm_ind, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_ite_eq, Finset.mem_univ, if_true, nsmul_eq_mul]
  by_cases h : π u = v
  · rw [if_pos h, if_pos h.symm]
    field_simp
    ring
  · rw [if_neg h, if_neg (fun e => h e.symm)]
    field_simp
    ring

theorem norm_f (q : ℕ) (hq : 3 ≤ q) (k : Option (Fin q)) :
    ∑ u, (ff q k u) ^ 2 = nn q k := by
  have hq0 : (q:ℝ) ≠ 0 := by
    have : (3:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  cases k with
  | none => simp [ff, nn]
  | some k =>
    simp only [ff, nn]
    have e : ∀ u : Fin q, ((1:ℝ) / q - (if u = k then 1 else 0)) ^ 2
        = 1 / (q:ℝ) ^ 2 + (if u = k then 1 - 2 / (q:ℝ) else 0) := by
      intro u
      split_ifs <;> field_simp <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, if_true,
      nsmul_eq_mul]
    field_simp
    ring

theorem norm_g (q : ℕ) (hq : 3 ≤ q) (π : Equiv.Perm (Fin q)) (k : Option (Fin q)) :
    ∑ v, (gg q π k v) ^ 2 = nn q k := by
  have hq0 : (q:ℝ) ≠ 0 := by
    have : (3:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  cases k with
  | none => simp [gg, nn]
  | some k =>
    simp only [gg, nn]
    have e : ∀ v : Fin q, ((if v = π k then 1 else 0) - (1:ℝ) / q) ^ 2
        = 1 / (q:ℝ) ^ 2 + (if v = π k then 1 - 2 / (q:ℝ) else 0) := by
      intro v
      split_ifs <;> field_simp <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ, if_true,
      nsmul_eq_mul]
    field_simp
    ring

theorem weight (q : ℕ) (hq : 3 ≤ q) :
    ∑ k, cc q k * nn q k = 3 * (q:ℝ) - 4 := by
  have hq0 : (q:ℝ) ≠ 0 := by
    have : (3:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [Fintype.sum_option]
  simp only [cc, nn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem cc_nonneg (q : ℕ) (hq : 3 ≤ q) (k : Option (Fin q)) : 0 ≤ cc q k := by
  have : (3:ℝ) ≤ q := by exact_mod_cast hq
  cases k with
  | none =>
    simp only [cc]
    apply div_nonneg <;> linarith
  | some _ => simp only [cc]; norm_num

theorem cs_bound {W : Type} [Fintype W] (X : W → W → ℝ) (b n : ℝ) (hb : 0 ≤ b) (hn : 0 ≤ n)
    (hE : ∀ v : W → ℝ, ∑ x, (∑ y, X x y * v y) ^ 2 ≤ b ^ 2 * ∑ y, (v y) ^ 2)
    (F G : W → ℝ) (hF : ∑ x, (F x) ^ 2 = n) (hG : ∑ y, (G y) ^ 2 = n) :
    ∑ x, ∑ y, X x y * (F x * G y) ≤ b * n := by
  have h1 : ∑ x, ∑ y, X x y * (F x * G y) = ∑ x, F x * (∑ y, X x y * G y) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [h1]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ F (fun x => ∑ y, X x y * G y)
  have h3 := hE G
  rw [hF] at h2
  rw [hG] at h3
  have h4 : (∑ x, F x * (∑ y, X x y * G y)) ^ 2 ≤ (b * n) ^ 2 := by
    calc _ ≤ n * ∑ x, (∑ y, X x y * G y) ^ 2 := h2
      _ ≤ n * (b ^ 2 * n) := mul_le_mul_of_nonneg_left h3 hn
      _ = (b * n) ^ 2 := by ring
  have h5 : 0 ≤ b * n := mul_nonneg hb hn
  nlinarith [h4, h5]

theorem lower {m : ℕ} {q : Fin m → ℕ} (hq : ∀ i, 3 ≤ q i)
    (π : (i : Fin m) → Equiv.Perm (Fin (q i)))
    (l r : ((i : Fin m) → Fin (q i)) → Bool)
    (law : ((i : Fin m) → Fin (q i)) → ((i : Fin m) → Fin (q i)) → ℝ)
    (hsum : ∑ x, ∑ y, law x y = 1) (b : ℝ) (hb : 0 ≤ b)
    (hE : ∀ v : ((i : Fin m) → Fin (q i)) → ℝ, ∑ x, (∑ y, law x y *
      ((if l x = r y then (1:ℝ) else -1) * ∏ i, (if π i (x i) = y i then (-1:ℝ) else 1))
        * v y) ^ 2 ≤ b ^ 2 * ∑ y, (v y) ^ 2) :
    1 ≤ b * ∏ i, (3 * (q i : ℝ) - 4) := by
  set S : ((i : Fin m) → Fin (q i)) → ((i : Fin m) → Fin (q i)) → ℝ := fun x y =>
    (if l x = r y then (1:ℝ) else -1) * ∏ i, (if π i (x i) = y i then (-1:ℝ) else 1) with hSdef
  set F : ((i : Fin m) → Option (Fin (q i))) → ((i : Fin m) → Fin (q i)) → ℝ := fun κ x =>
    sg (l x) * ∏ i, ff (q i) (κ i) (x i) with hFdef
  set G : ((i : Fin m) → Option (Fin (q i))) → ((i : Fin m) → Fin (q i)) → ℝ := fun κ y =>
    sg (r y) * ∏ i, gg (q i) (π i) (κ i) (y i) with hGdef
  set C : ((i : Fin m) → Option (Fin (q i))) → ℝ := fun κ => ∏ i, cc (q i) (κ i) with hCdef
  have hSS : ∀ x y, S x y * S x y = 1 := by
    intro x y
    simp only [hSdef, sg_eq]
    have : ∀ i, (if π i (x i) = y i then (-1:ℝ) else 1) * (if π i (x i) = y i then (-1:ℝ) else 1)
        = 1 := by
      intro i
      split_ifs <;> norm_num
    rw [show ∀ a b c : ℝ, a * b * c * (a * b * c) = (a * a) * (b * b) * (c * c) from
      fun _ _ _ => by ring, sg_sq, sg_sq, ← Finset.prod_mul_distrib]
    simp [this]
  have hdec : ∀ x y, S x y = ∑ κ, C κ * (F κ x * G κ y) := by
    intro x y
    simp only [hSdef, hFdef, hGdef, hCdef, sg_eq]
    have e1 : ∀ i, (if π i (x i) = y i then (-1:ℝ) else 1)
        = ∑ k, cc (q i) k * ff (q i) k (x i) * gg (q i) (π i) k (y i) := fun i =>
      (decomp (q i) (hq i) (π i) (x i) (y i)).symm
    simp_rw [e1]
    rw [Fintype.prod_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    ring
  have hFn : ∀ κ, ∑ x, (F κ x) ^ 2 = ∏ i, nn (q i) (κ i) := by
    intro κ
    have e : ∀ x : ((i : Fin m) → Fin (q i)), (F κ x) ^ 2 = ∏ i, (ff (q i) (κ i) (x i)) ^ 2 := by
      intro x
      simp only [hFdef]
      rw [mul_pow, ← Finset.prod_pow, sq (sg (l x)), sg_sq, one_mul]
    simp_rw [e]
    have := sum_prod (q := q) (fun i a => (ff (q i) (κ i) a) ^ 2)
    rw [this]
    exact Finset.prod_congr rfl fun i _ => norm_f (q i) (hq i) (κ i)
  have hGn : ∀ κ, ∑ y, (G κ y) ^ 2 = ∏ i, nn (q i) (κ i) := by
    intro κ
    have e : ∀ y : ((i : Fin m) → Fin (q i)), (G κ y) ^ 2
        = ∏ i, (gg (q i) (π i) (κ i) (y i)) ^ 2 := by
      intro y
      simp only [hGdef]
      rw [mul_pow, ← Finset.prod_pow, sq (sg (r y)), sg_sq, one_mul]
    simp_rw [e]
    have := sum_prod (q := q) (fun i a => (gg (q i) (π i) (κ i) a) ^ 2)
    rw [this]
    exact Finset.prod_congr rfl fun i _ => norm_g (q i) (hq i) (π i) (κ i)
  have hnn : ∀ κ : ((i : Fin m) → Option (Fin (q i))), 0 ≤ ∏ i, nn (q i) (κ i) := by
    intro κ
    rw [← hFn κ]
    exact Finset.sum_nonneg fun x _ => sq_nonneg _
  have hE' : ∀ v : ((i : Fin m) → Fin (q i)) → ℝ,
      ∑ x, (∑ y, (law x y * S x y) * v y) ^ 2 ≤ b ^ 2 * ∑ y, (v y) ^ 2 := hE
  calc (1:ℝ) = ∑ x, ∑ y, law x y := hsum.symm
    _ = ∑ x, ∑ y, (law x y * S x y) * S x y := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        rw [mul_assoc, hSS, mul_one]
    _ = ∑ κ, C κ * ∑ x, ∑ y, (law x y * S x y) * (F κ x * G κ y) := by
        have h3 : ∀ x y, (law x y * S x y) * S x y
            = ∑ κ, C κ * ((law x y * S x y) * (F κ x * G κ y)) := by
          intro x y
          have e := hdec x y
          calc (law x y * S x y) * S x y
              = (law x y * S x y) * ∑ κ, C κ * (F κ x * G κ y) := by rw [← e]
            _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun κ _ => ?_
              ring
        simp_rw [h3]
        simp_rw [Finset.mul_sum]
        symm
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ κ, C κ * (b * ∏ i, nn (q i) (κ i)) := by
        refine Finset.sum_le_sum fun κ _ => ?_
        apply mul_le_mul_of_nonneg_left
        · exact cs_bound (fun x y => law x y * S x y) b _ hb (hnn κ) hE' (F κ) (G κ)
            (hFn κ) (hGn κ)
        · exact Finset.prod_nonneg fun i _ => cc_nonneg (q i) (hq i) (κ i)
    _ = b * ∑ κ : ((i : Fin m) → Option (Fin (q i))), ∏ i, (cc (q i) (κ i) * nn (q i) (κ i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        simp only [hCdef]
        rw [Finset.prod_mul_distrib]
        ring
    _ = b * ∏ i, (3 * (q i : ℝ) - 4) := by
        have := Fintype.prod_sum (fun i (k : Option (Fin (q i))) => cc (q i) k * nn (q i) k)
        rw [← this]
        congr 1
        exact Finset.prod_congr rfl fun i _ => weight (q i) (hq i)

end PEqualNP.Outside.L_lib_837

open PEqualNP.Outside.L_lib_837 in
theorem PEqualNP.Outside.L_lib_837 : ∀ (m : Nat) (q : Fin m → Nat), (∀ i, 3 ≤ q i) →
  let W := (i : Fin m) → Fin (q i)
  let N := ∏ i : Fin m, q i
  let D := ∏ i : Fin m, (3*q i-4)
  ∀ (matchAt : (i : Fin m) → Equiv.Perm (Fin (q i))) (l r : W → Bool),
    let same := fun (x y : W) (i : Fin m) => matchAt i (x i) = y i
    let sign := fun x y : W =>
      (if l x = r y then (1 : ℝ) else -1) *
        ∏ i : Fin m, (if same x y i then (-1 : ℝ) else 1)
    let witness := fun x y : W =>
      (∏ i : Fin m, (if same x y i then ((q i : ℝ)-2) else 2)) / ((N : ℝ)*D)
    let energy := fun (law : W → W → ℝ) (v : W → ℝ) =>
      ∑ x : W, (∑ y : W, law x y * sign x y * v y)^2
    let prob := fun law : W → W → ℝ =>
      (∀ x y, 0 ≤ law x y) ∧ (∑ x : W, ∑ y : W, law x y) = 1
    (prob witness ∧ (∀ x : W, (∑ y : W, witness x y) = 1/(N : ℝ)) ∧
      (∀ y : W, (∑ x : W, witness x y) = 1/(N : ℝ)) ∧
      (∀ v : W → ℝ, (D : ℝ)^2 * energy witness v = ∑ y : W, (v y)^2)) ∧
    ∀ b : ℝ, 0 ≤ b →
      Iff (∃ law, prob law ∧ ∀ v : W → ℝ, energy law v ≤ b^2 * ∑ y : W, (v y)^2)
        (1 ≤ b * (D : ℝ)) := by
  intro m q hq W N D matchAt l r same sign witness energy prob
  have hq3 : ∀ i, (3:ℝ) ≤ q i := fun i => by exact_mod_cast hq i
  have hN : (N:ℝ) = ∏ i, (q i : ℝ) := by
    simp only [N]
    push_cast
    rfl
  have hD : (D:ℝ) = ∏ i, (3 * (q i : ℝ) - 4) := by
    simp only [D]
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (by have := hq i; omega)]
    push_cast
    ring
  have hNpos : 0 < (N:ℝ) := by
    rw [hN]
    exact Finset.prod_pos fun i _ => by linarith [hq3 i]
  have hDpos : 0 < (D:ℝ) := by
    rw [hD]
    exact Finset.prod_pos fun i _ => by linarith [hq3 i]
  have hrow : ∀ x : W, (∑ y : W, witness x y) = 1 / (N:ℝ) := by
    intro x
    show ∑ y : W, (∏ i : Fin m, (if matchAt i (x i) = y i then ((q i : ℝ)-2) else 2))
      / ((N : ℝ) * D) = 1 / (N:ℝ)
    rw [← Finset.sum_div,
      sum_prod (q := q) (fun i v => if matchAt i (x i) = v then ((q i : ℝ)-2) else 2)]
    simp only [row_sum]
    rw [← hD]
    field_simp
  have hcol : ∀ y : W, (∑ x : W, witness x y) = 1 / (N:ℝ) := by
    intro y
    show ∑ x : W, (∏ i : Fin m, (if matchAt i (x i) = y i then ((q i : ℝ)-2) else 2))
      / ((N : ℝ) * D) = 1 / (N:ℝ)
    rw [← Finset.sum_div,
      sum_prod (q := q) (fun i u => if matchAt i u = y i then ((q i : ℝ)-2) else 2)]
    simp only [col_sum]
    rw [← hD]
    field_simp
  have hcard : (Fintype.card W : ℝ) = N := by
    have : Fintype.card ((i : Fin m) → Fin (q i)) = ∏ i : Fin m, q i := by
      simp [Fintype.card_pi]
    exact_mod_cast this
  have hprob : prob witness := by
    refine ⟨fun x y => ?_, ?_⟩
    · show 0 ≤ (∏ i : Fin m, (if matchAt i (x i) = y i then ((q i : ℝ)-2) else 2))
        / ((N : ℝ) * D)
      apply div_nonneg
      · exact Finset.prod_nonneg fun i _ => by split_ifs <;> linarith [hq3 i]
      · positivity
    · simp only [hrow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hcard]
      field_simp
  have hen : ∀ v : W → ℝ, energy witness v = (∑ y : W, (v y) ^ 2) / (D:ℝ) ^ 2 := by
    intro v
    have e1 : ∀ x y : W, witness x y * sign x y * v y = (sg (l x) / ((N:ℝ) * D)) *
        ((∏ i, ((if matchAt i (x i) = y i then ((q i:ℝ)-2) else 2) *
          (if matchAt i (x i) = y i then (-1:ℝ) else 1))) * (sg (r y) * v y)) := by
      intro x y
      show (∏ i : Fin m, (if matchAt i (x i) = y i then ((q i : ℝ)-2) else 2)) / ((N : ℝ) * D)
        * ((if l x = r y then (1 : ℝ) else -1) *
          ∏ i : Fin m, (if matchAt i (x i) = y i then (-1 : ℝ) else 1)) * v y = _
      rw [sg_eq, Finset.prod_mul_distrib]
      ring
    have hg := energy_gen (q := q) (fun i a b => (if matchAt i a = b then ((q i:ℝ)-2) else 2) *
      (if matchAt i a = b then (-1:ℝ) else 1)) (fun i => (q i:ℝ) ^ 2)
      (fun i v w => gram (q i) (matchAt i) v w) (fun y => sg (r y) * v y)
    show ∑ x : W, (∑ y : W, witness x y * sign x y * v y) ^ 2 = _
    calc ∑ x : W, (∑ y : W, witness x y * sign x y * v y) ^ 2
        = ∑ x : W, (1 / ((N:ℝ) * D)) ^ 2 * (∑ y : W,
            (∏ i, ((if matchAt i (x i) = y i then ((q i:ℝ)-2) else 2) *
              (if matchAt i (x i) = y i then (-1:ℝ) else 1))) * (sg (r y) * v y)) ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp_rw [e1]
          rw [← Finset.mul_sum, mul_pow, div_pow, sq (sg (l x)), sg_sq]
          ring
      _ = (1 / ((N:ℝ) * D)) ^ 2 * ((∏ i, (q i:ℝ) ^ 2) * ∑ y : W, (sg (r y) * v y) ^ 2) := by
          rw [← Finset.mul_sum, hg]
      _ = _ := by
          have : ∀ y : W, (sg (r y) * v y) ^ 2 = (v y) ^ 2 := fun y => by
            rw [mul_pow, sq (sg (r y)), sg_sq, one_mul]
          simp only [this]
          rw [Finset.prod_pow, ← hN]
          field_simp
  refine ⟨⟨hprob, hrow, hcol, fun v => ?_⟩, fun b hb => ⟨?_, ?_⟩⟩
  · rw [hen v]
    field_simp
  · rintro ⟨law, ⟨_, hsum⟩, hE⟩
    rw [hD]
    exact lower hq matchAt l r law hsum b hb hE
  · intro h
    refine ⟨witness, hprob, fun v => ?_⟩
    rw [hen v]
    have hS : 0 ≤ ∑ y : W, (v y) ^ 2 := Finset.sum_nonneg fun y _ => sq_nonneg _
    have h2 : 1 ≤ (b * D) ^ 2 := by nlinarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hS]
