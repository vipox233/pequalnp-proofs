import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25547

theorem L_meta_25547_aux_term (E d G c : ℕ) (h : G ≤ d + E) :
    2 ^ (E - (G - d)) * (15 ^ d * 16 ^ (G + c)) ≤ 2 ^ E * 16 ^ d * (15 ^ G * 16 ^ c) := by
  rcases le_or_gt G d with hGd | hGd
  · obtain ⟨m, rfl⟩ : ∃ m, d = G + m := ⟨d - G, by omega⟩
    rw [Nat.sub_eq_zero_of_le hGd, Nat.sub_zero]
    have hm : 15 ^ m ≤ 16 ^ m := Nat.pow_le_pow_left (by norm_num) m
    calc 2 ^ E * (15 ^ (G + m) * 16 ^ (G + c))
        = (2 ^ E * 15 ^ G * 16 ^ G * 16 ^ c) * 15 ^ m := by ring
      _ ≤ (2 ^ E * 15 ^ G * 16 ^ G * 16 ^ c) * 16 ^ m := Nat.mul_le_mul_left _ hm
      _ = 2 ^ E * 16 ^ (G + m) * (15 ^ G * 16 ^ c) := by ring
  · obtain ⟨e, rfl⟩ : ∃ e, G = d + e := ⟨G - d, by omega⟩
    obtain ⟨F, rfl⟩ : ∃ F, E = F + e := ⟨E - e, by omega⟩
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel]
    have he : 16 ^ e ≤ 2 ^ e * 15 ^ e := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) e
    calc 2 ^ F * (15 ^ d * 16 ^ (d + e + c))
        = (2 ^ F * 15 ^ d * 16 ^ d * 16 ^ c) * 16 ^ e := by ring
      _ ≤ (2 ^ F * 15 ^ d * 16 ^ d * 16 ^ c) * (2 ^ e * 15 ^ e) := Nat.mul_le_mul_left _ he
      _ = 2 ^ (F + e) * 16 ^ d * (15 ^ (d + e) * 16 ^ c) := by ring

theorem L_meta_25547_aux_prod (g : Fin 16 → ℕ) {n : ℕ} (h : Fin n → Fin 16) :
    ∏ i, 15 ^ (g (h i)) * 16 ^ (3 - g (h i)) =
      15 ^ (∑ i, g (h i)) * 16 ^ (∑ i, (3 - g (h i))) := by
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem L_meta_25547_aux_sum3 (g : Fin 16 → ℕ) (hg : ∀ a, g a ≤ 3) {n : ℕ}
    (h : Fin n → Fin 16) : ∑ i, g (h i) + ∑ i, (3 - g (h i)) = 3 * n := by
  rw [← Finset.sum_add_distrib,
    Finset.sum_congr rfl (fun i _ => Nat.add_sub_of_le (hg (h i)))]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

theorem L_meta_25547_aux_pow63 (s : ℕ) : 2 ^ (s / 64) * 63 ^ s ≤ 64 ^ s := by
  have hs := (Nat.div_add_mod s 64).symm
  generalize s / 64 = q at hs ⊢
  generalize s % 64 = r at hs
  subst hs
  calc 2 ^ q * 63 ^ (64 * q + r) = (2 * 63 ^ 64) ^ q * 63 ^ r := by
        rw [mul_pow, pow_add, pow_mul, mul_assoc]
    _ ≤ (64 ^ 64) ^ q * 64 ^ r :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) q) (Nat.pow_le_pow_left (by norm_num) r)
    _ = 64 ^ (64 * q + r) := by rw [pow_add, pow_mul]

theorem L_meta_25547_aux_gen (a b s : ℕ) (h1 : 64 * a ≤ 63 * b) :
    2 ^ (s / 64) * a ^ s ≤ b ^ s := by
  have h2 := Nat.pow_le_pow_left h1 s
  have h3 := L_meta_25547_aux_pow63 s
  rw [mul_pow, mul_pow] at h2
  have h63 : 0 < 63 ^ s := by positivity
  apply Nat.le_of_mul_le_mul_left _ h63
  calc 63 ^ s * (2 ^ (s / 64) * a ^ s) = (2 ^ (s / 64) * 63 ^ s) * a ^ s := by ring
    _ ≤ 64 ^ s * a ^ s := Nat.mul_le_mul_right _ h3
    _ ≤ 63 ^ s * b ^ s := h2

theorem L_meta_25547_aux_num :
    64 * (2 ^ 159 * 16 ^ 33 * 61279 ^ 32) ≤ 63 * (2 ^ 287 * 15 ^ 33 * 16 ^ 96) := by
  decide +kernel

theorem L_meta_25547_aux_core (s : ℕ) :
    2 ^ (s / 64) * (2 ^ (159 * s) * 16 ^ (33 * s) * 61279 ^ (32 * s)) ≤
      2 ^ (287 * s) * (15 ^ (33 * s) * 16 ^ (96 * s)) := by
  have ha : 2 ^ (159 * s) * 16 ^ (33 * s) * 61279 ^ (32 * s) =
      (2 ^ 159 * 16 ^ 33 * 61279 ^ 32) ^ s := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
  have hb : 2 ^ (287 * s) * (15 ^ (33 * s) * 16 ^ (96 * s)) =
      (2 ^ 287 * 15 ^ 33 * 16 ^ 96) ^ s := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_assoc]
  rw [ha, hb]
  exact L_meta_25547_aux_gen _ _ s L_meta_25547_aux_num

theorem L_meta_25547_aux_part1 (g : Fin 16 → ℕ) (hg : ∀ a, g a ≤ 3)
    (hw : ∑ a, 15 ^ (g a) * 16 ^ (3 - g a) = 61279) (s : ℕ) (hs : 0 < s) :
    ∑ h : Fin (32 * s) → Fin 16,
        2 ^ (287 * s + 22 - 4 * (32 * s) - ((∑ i, g (h i)) - 33 * s)) ≤
      2 ^ (287 * s + 22 - s / 64) := by
  have hE : 287 * s + 22 - 4 * (32 * s) = 22 + 159 * s := by omega
  rw [hE]
  have hC : 0 < 15 ^ (33 * s) * 16 ^ (3 * (32 * s)) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hC
  have hA : ∀ h : Fin (32 * s) → Fin 16,
      2 ^ (22 + 159 * s - ((∑ i, g (h i)) - 33 * s)) * (15 ^ (33 * s) * 16 ^ (3 * (32 * s))) ≤
        2 ^ (22 + 159 * s) * 16 ^ (33 * s) * ∏ i, 15 ^ (g (h i)) * 16 ^ (3 - g (h i)) := by
    intro h
    have h3 := L_meta_25547_aux_sum3 g hg h
    rw [L_meta_25547_aux_prod g h, ← h3]
    exact L_meta_25547_aux_term _ _ _ _ (by omega)
  have hB : (∑ h : Fin (32 * s) → Fin 16, 2 ^ (22 + 159 * s - ((∑ i, g (h i)) - 33 * s))) *
      (15 ^ (33 * s) * 16 ^ (3 * (32 * s))) ≤
        2 ^ (22 + 159 * s) * 16 ^ (33 * s) * 61279 ^ (32 * s) := by
    rw [Finset.sum_mul]
    calc _ ≤ ∑ h : Fin (32 * s) → Fin 16,
          2 ^ (22 + 159 * s) * 16 ^ (33 * s) * ∏ i, 15 ^ (g (h i)) * 16 ^ (3 - g (h i)) :=
          Finset.sum_le_sum (fun h _ => hA h)
      _ = 2 ^ (22 + 159 * s) * 16 ^ (33 * s) * 61279 ^ (32 * s) := by
          rw [← Finset.mul_sum, ← hw, Fintype.sum_pow]
  refine le_trans hB ?_
  have core := L_meta_25547_aux_core s
  have hq : s / 64 ≤ s := Nat.div_le_self _ _
  generalize s / 64 = q at core hq ⊢
  obtain ⟨t, ht⟩ : ∃ t, 287 * s = q + t := ⟨287 * s - q, by omega⟩
  rw [show 287 * s + 22 - q = 22 + t by omega]
  rw [ht, pow_add] at core
  have hq0 : 0 < 2 ^ q := by positivity
  apply Nat.le_of_mul_le_mul_left _ hq0
  calc 2 ^ q * (2 ^ (22 + 159 * s) * 16 ^ (33 * s) * 61279 ^ (32 * s))
      = 2 ^ 22 * (2 ^ q * (2 ^ (159 * s) * 16 ^ (33 * s) * 61279 ^ (32 * s))) := by ring
    _ ≤ 2 ^ 22 * (2 ^ q * 2 ^ t * (15 ^ (33 * s) * 16 ^ (96 * s))) := Nat.mul_le_mul_left _ core
    _ = 2 ^ q * (2 ^ (22 + t) * (15 ^ (33 * s) * 16 ^ (3 * (32 * s)))) := by ring

theorem L_meta_25547_aux_sumG (g : Fin 16 → ℕ) :
    ∀ n : ℕ, 16 * ∑ h : Fin n → Fin 16, ∑ i, g (h i) = n * 16 ^ n * ∑ a, g a
  | 0 => by simp
  | n + 1 => by
    have ih := L_meta_25547_aux_sumG g n
    rw [← (Fin.consEquiv fun _ => Fin 16).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ (n := n), Fin.cons_zero, Fin.cons_succ,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Fintype.card_fun]
    rw [← Finset.mul_sum]
    generalize (∑ a, g a) = S at ih ⊢
    generalize (∑ h : Fin n → Fin 16, ∑ i, g (h i)) = X at ih ⊢
    rw [pow_succ]
    nlinarith [ih]

theorem L_meta_25547_aux_part2 (g : Fin 16 → ℕ) (hsum : ∑ a, g a = 17) (n k d : ℕ)
    (hk : 4 * n ≤ k) (hd : 17 * n / 16 ≤ d) :
    2 ^ k ≤ 16 * (d + 1) * ∑ h : Fin n → Fin 16, 2 ^ (k - 4 * n - ((∑ i, g (h i)) - d)) := by
  set E := k - 4 * n with hE
  have hkE : k = 4 * n + E := by omega
  set A := (Finset.univ.filter (fun h : Fin n → Fin 16 => ∑ i, g (h i) ≤ d)).card with hAdef
  set B := (Finset.univ.filter (fun h : Fin n → Fin 16 => ¬ (∑ i, g (h i) ≤ d))).card
    with hBdef
  have hAB : A + B = 16 ^ n := by
    rw [hAdef, hBdef, Finset.card_filter_add_card_filter_not]
    simp
  have hslots : A * 2 ^ E ≤ ∑ h : Fin n → Fin 16, 2 ^ (E - ((∑ i, g (h i)) - d)) := by
    calc A * 2 ^ E
        = ∑ h ∈ Finset.univ.filter (fun h : Fin n → Fin 16 => ∑ i, g (h i) ≤ d), 2 ^ E := by
          rw [Finset.sum_const, smul_eq_mul, hAdef]
      _ = ∑ h ∈ Finset.univ.filter (fun h : Fin n → Fin 16 => ∑ i, g (h i) ≤ d),
            2 ^ (E - ((∑ i, g (h i)) - d)) :=
          Finset.sum_congr rfl (fun h hh => by
            rw [Finset.mem_filter] at hh
            simp [Nat.sub_eq_zero_of_le hh.2])
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hmarkov : (d + 1) * B ≤ ∑ h : Fin n → Fin 16, ∑ i, g (h i) := by
    calc (d + 1) * B
        = ∑ h ∈ Finset.univ.filter (fun h : Fin n → Fin 16 => ¬ (∑ i, g (h i) ≤ d)), (d + 1) := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm, hBdef]
      _ ≤ ∑ h ∈ Finset.univ.filter (fun h : Fin n → Fin 16 => ¬ (∑ i, g (h i) ≤ d)),
            ∑ i, g (h i) :=
          Finset.sum_le_sum (fun h hh => by
            rw [Finset.mem_filter] at hh
            omega)
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hG := L_meta_25547_aux_sumG g n
  rw [hsum] at hG
  have h17 : 17 * n + 1 ≤ 16 * (d + 1) := by omega
  have h1 : 16 * (d + 1) * B ≤ n * 16 ^ n * 17 := by
    rw [← hG, mul_assoc]
    exact Nat.mul_le_mul_left _ hmarkov
  have h2 : (17 * n + 1) * 16 ^ n ≤ 16 * (d + 1) * 16 ^ n := Nat.mul_le_mul_right _ h17
  have h3 : 16 * (d + 1) * 16 ^ n = 16 * (d + 1) * A + 16 * (d + 1) * B := by
    rw [← hAB]; ring
  have key : 16 ^ n ≤ 16 * (d + 1) * A := by
    nlinarith [h1, h2, h3]
  calc 2 ^ k = 16 ^ n * 2 ^ E := by
        rw [hkE, pow_add, pow_mul]; norm_num
    _ ≤ 16 * (d + 1) * A * 2 ^ E := Nat.mul_le_mul_right _ key
    _ = 16 * (d + 1) * (A * 2 ^ E) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hslots

end PEqualNP.Outside.L_meta_25547

theorem PEqualNP.Outside.L_meta_25547 : (let gain := fun (a : Fin 16) =>
  if a.val < 4 then 0 else if a.val < 12 then 1 else if a.val < 15 then 2 else 3
let slots := fun (n k d : Nat) =>
  ∑ history : Fin n → Fin 16,
    (2 : Nat) ^ (k - 4 * n - ((∑ i : Fin n, gain (history i)) - d))
(∀ scale : Nat, 0 < scale →
  slots (32 * scale) (287 * scale + 22) (33 * scale) ≤
    2 ^ (287 * scale + 22 - scale / 64)) ∧
(∀ (n k d : Nat), 4 * n ≤ k → 17 * n / 16 ≤ d →
  2 ^ k ≤ 16 * (d + 1) * slots n k d)) := by
  intro gain slots
  refine ⟨fun s hs => ?_, fun n k d hk hd => ?_⟩
  · exact PEqualNP.Outside.L_meta_25547.L_meta_25547_aux_part1 gain (by decide) (by decide) s hs
  · exact PEqualNP.Outside.L_meta_25547.L_meta_25547_aux_part2 gain (by decide) n k d hk hd
