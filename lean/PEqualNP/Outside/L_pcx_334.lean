import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_334_aux

open Finset

section Sampling

lemma sum_sq_sample {α : Type} [Fintype α] (Z : α → ℤ) (hZ : ∑ i, Z i = 0) : ∀ m : ℕ,
    (Fintype.card α : ℤ) * ∑ s : Fin m → α, (∑ l, Z (s l)) ^ 2 =
      m * (Fintype.card α : ℤ) ^ m * ∑ i, Z i ^ 2
  | 0 => by simp
  | m + 1 => by
    rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, add_sq,
      sum_add_distrib, ← mul_sum, ← sum_mul, sum_const,
      card_univ, Fintype.card_fun, Fintype.card_fin, hZ, nsmul_eq_mul]
    have ih := sum_sq_sample Z hZ m
    push_cast
    linear_combination (Fintype.card α : ℤ) * ih

lemma cheb_half (c s g : ℕ) (P : Fin c → Prop) [DecidablePred P] (hc : 0 < c) (hs : 0 < s)
    (hsg : 16 * c ^ 2 ≤ s * g ^ 2) :
    16 * (univ.filter (fun f : Fin s → Fin c => ((s : ℤ) * g) ^ 2 ≤
      (2 * ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * (univ.filter P).card)) ^ 2)).card
      ≤ c ^ s := by
  set D := (univ.filter P).card
  set Z : Fin c → ℤ := fun i => c * (if P i then 1 else 0) - D
  have hsum : ∀ {k : ℕ} (f : Fin k → Fin c), ∑ l, Z (f l) =
      c * (univ.filter (fun l => P (f l))).card - k * D := by
    intro k f
    simp only [Z, sum_sub_distrib, ← mul_sum, sum_boole, sum_const,
      card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hZ : ∑ i, Z i = 0 := by
    have := hsum (id : Fin c → Fin c)
    simp only [id] at this
    rw [this]; ring
  have hZ2 : ∑ i, Z i ^ 2 = c * D * (c - D) := by
    have : ∀ i, Z i ^ 2 = ((c : ℤ) ^ 2 - 2 * c * D) * (if P i then 1 else 0) + (D : ℤ) ^ 2 := by
      intro i; simp only [Z]; split_ifs <;> ring
    simp only [this, sum_add_distrib, ← mul_sum, sum_boole,
      sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hid := sum_sq_sample Z hZ s
  simp only [Fintype.card_fin, hsum] at hid
  rw [hZ2] at hid
  set bad := univ.filter (fun f : Fin s → Fin c => ((s : ℤ) * g) ^ 2 ≤
      (2 * ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D)) ^ 2)
  have hmk : (bad.card : ℤ) * ((s : ℤ) * g) ^ 2 ≤
      4 * ∑ f : Fin s → Fin c, ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D) ^ 2 := by
    calc (bad.card : ℤ) * ((s : ℤ) * g) ^ 2 = bad.card • (((s : ℤ) * g) ^ 2) := by
          rw [nsmul_eq_mul]
      _ ≤ ∑ f ∈ bad, (2 * ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D)) ^ 2 :=
          card_nsmul_le_sum _ _ _ (fun f hf => (mem_filter.1 hf).2)
      _ ≤ ∑ f : Fin s → Fin c,
            (2 * ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D)) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
      _ = 4 * ∑ f : Fin s → Fin c,
            ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D) ^ 2 := by
          rw [mul_sum]; refine sum_congr rfl fun _ _ => by ring
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc
  have hsg' : (16 : ℤ) * c ^ 2 ≤ s * g ^ 2 := by exact_mod_cast hsg
  have h4 : 4 * (D : ℤ) * (c - D) ≤ (c : ℤ) ^ 2 := by nlinarith [sq_nonneg ((c : ℤ) - 2 * D)]
  have e1 : (c : ℤ) * (bad.card * ((s : ℤ) * g) ^ 2) ≤ 4 * (s * c ^ s * (c * D * (c - D))) := by
    have := mul_le_mul_of_nonneg_left hmk hcz.le
    calc (c : ℤ) * (bad.card * ((s : ℤ) * g) ^ 2)
        ≤ c * (4 * ∑ f : Fin s → Fin c,
            ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D) ^ 2) := this
      _ = 4 * (c * ∑ f : Fin s → Fin c,
            ((c : ℤ) * (univ.filter (fun l => P (f l))).card - s * D) ^ 2) := by ring
      _ = 4 * (s * c ^ s * (c * D * (c - D))) := by rw [hid]
  have e2 : (c : ℤ) * bad.card * s * (16 * c ^ 2) ≤ (c : ℤ) * bad.card * s * (s * g ^ 2) :=
    mul_le_mul_of_nonneg_left hsg' (by positivity)
  have e3 : (s : ℤ) * c ^ s * c * (4 * D * (c - D)) ≤ (s : ℤ) * c ^ s * c * c ^ 2 :=
    mul_le_mul_of_nonneg_left h4 (by positivity)
  have key : (16 : ℤ) * bad.card * (s * c ^ 2 * c) ≤ (c : ℤ) ^ s * (s * c ^ 2 * c) := by
    nlinarith
  have : (16 : ℤ) * bad.card ≤ (c : ℤ) ^ s :=
    le_of_mul_le_mul_right key (by positivity)
  exact_mod_cast this

lemma amp_majority {α : Type} [Fintype α] [DecidableEq α] (B : Finset α) (H : ℕ)
    (hB : 16 * B.card ≤ Fintype.card α) :
    4 ^ H * (univ.filter (fun f : Fin (2 * H) → α =>
      H ≤ (univ.filter (fun t => f t ∈ B)).card)).card ≤ (Fintype.card α) ^ (2 * H) := by
  classical
  set N := Fintype.card α
  set S := univ.filter (fun f : Fin (2 * H) → α =>
    H ≤ (univ.filter (fun t => f t ∈ B)).card)
  have hsub : S ⊆ (powersetCard H (univ : Finset (Fin (2 * H)))).biUnion (fun U =>
      Fintype.piFinset (fun t : Fin (2 * H) => if t ∈ U then B else univ)) := by
    intro f hf
    have hcard : H ≤ (univ.filter (fun t => f t ∈ B)).card := (mem_filter.1 hf).2
    obtain ⟨U, hUsub, hUcard⟩ := exists_subset_card_eq hcard
    refine mem_biUnion.2 ⟨U, mem_powersetCard.2 ⟨subset_univ _, hUcard⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro t
    by_cases ht : t ∈ U
    · rw [if_pos ht]; exact (mem_filter.1 (hUsub ht)).2
    · rw [if_neg ht]; exact mem_univ _
  have hpi : ∀ U ∈ powersetCard H (univ : Finset (Fin (2 * H))),
      (Fintype.piFinset (fun t : Fin (2 * H) => if t ∈ U then B else univ)).card =
        B.card ^ H * N ^ H := by
    intro U hU
    have hUc : U.card = H := (mem_powersetCard.1 hU).2
    rw [Fintype.card_piFinset, ← prod_filter_mul_prod_filter_not univ (fun t => t ∈ U)]
    have h1 : ∏ t ∈ univ.filter (fun t => t ∈ U), (if t ∈ U then B else univ).card =
        B.card ^ H := by
      have hf : univ.filter (fun t => t ∈ U) = U := by ext t; simp
      rw [hf, prod_congr rfl (fun t ht => by rw [if_pos ht]), prod_const, hUc]
    have h2 : ∏ t ∈ univ.filter (fun t => t ∉ U), (if t ∈ U then B else univ).card =
        N ^ H := by
      have hf : (univ.filter (fun t => t ∉ U)).card = H := by
        have := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * H)))) (fun t => t ∈ U)
        have hf1 : univ.filter (fun t => t ∈ U) = U := by ext t; simp
        rw [hf1, hUc, card_univ, Fintype.card_fin] at this
        omega
      rw [prod_congr rfl (fun t ht => by rw [if_neg (mem_filter.1 ht).2]), prod_const,
        card_univ, hf]
    rw [h1, h2]
  have hle : S.card ≤ (powersetCard H (univ : Finset (Fin (2 * H)))).card * (B.card ^ H * N ^ H) := by
    calc S.card ≤ ∑ U ∈ powersetCard H (univ : Finset (Fin (2 * H))),
            (Fintype.piFinset (fun t : Fin (2 * H) => if t ∈ U then B else univ)).card :=
          (card_le_card hsub).trans card_biUnion_le
      _ = ∑ _U ∈ powersetCard H (univ : Finset (Fin (2 * H))), (B.card ^ H * N ^ H) :=
          sum_congr rfl hpi
      _ = _ := by rw [sum_const, smul_eq_mul]
  have hpc : (powersetCard H (univ : Finset (Fin (2 * H)))).card ≤ 4 ^ H := by
    calc (powersetCard H (univ : Finset (Fin (2 * H)))).card
        ≤ (powerset (univ : Finset (Fin (2 * H)))).card :=
          card_le_card (fun U hU => mem_powerset.2 (mem_powersetCard.1 hU).1)
      _ = 2 ^ (2 * H) := by rw [card_powerset, card_univ, Fintype.card_fin]
      _ = 4 ^ H := by rw [pow_mul]; norm_num
  calc 4 ^ H * S.card
      ≤ 4 ^ H * (4 ^ H * (B.card ^ H * N ^ H)) :=
        Nat.mul_le_mul_left _ (hle.trans (Nat.mul_le_mul_right _ hpc))
    _ = (16 * B.card) ^ H * N ^ H := by
        rw [mul_pow, ← mul_assoc, ← mul_pow]; ring_nf
    _ ≤ N ^ H * N ^ H := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hB H)
    _ = N ^ (2 * H) := by rw [← pow_add, two_mul]

end Sampling

section UpperBound

set_option maxHeartbeats 800000 in
lemma upper_bound : ∀ (n r g : ℕ), 0 < g →
    ∀ M : Fin r → Equiv.Perm (Fin n),
      let V := Bool × Fin n
      ∀ S : Finset V,
        let A := {v : V // v ∈ S} → Bool
        let B := {v : V // v ∉ S} → Bool
        let cross := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
          ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))).card
        let cost := fun b : ℕ => ∃ R : ℕ, 0 < R ∧
          ∃ (send : Fin R → A → Fin (2 ^ b)) (recv : Fin R → Fin (2 ^ b) → B → Bool),
            ∀ (a : A) (z : B),
              let x := fun v : V => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
              let D := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
                x (false, i) ≠ x (true, M j i))).card
              let yes := ∀ j : Fin r, 15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n
              let no := ∃ j : Fin r, 32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j
              let good := fun seed : Fin R => (yes → recv seed (send seed a) z = true) ∧
                (no → recv seed (send seed a) z = false)
              2 * R ≤ 3 * (Finset.univ.filter (fun seed : Fin R => good seed)).card
        ∃ b : ℕ, cost b ∧ b ≤ 64 * (r * (1 + Nat.clog 2 (n / g + 1)) +
          ∑ j : Fin r, min (cross j)
            ((1 + (cross j) * (cross j) / (g * g)) * (1 + Nat.clog 2 (r + 1)))) := by
  classical
  intro n r g hg M V S A B cross cost
  by_cases hr0 : r = 0
  · subst hr0
    refine ⟨0, ⟨1, one_pos, fun _ _ => 0, fun _ _ _ => true, fun a z => ?_⟩, Nat.zero_le _⟩
    dsimp only
    rw [filter_true_of_mem fun _ _ => ⟨fun _ => rfl, fun ⟨j, _⟩ => Fin.elim0 j⟩]
    simp
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
  by_cases hng : n < 32 * g
  · refine ⟨0, ⟨1, one_pos, fun _ _ => 0, fun _ _ _ => false, fun a z => ?_⟩, Nat.zero_le _⟩
    dsimp only
    have hflt : (univ.filter (fun _seed : Fin 1 =>
        ((∀ j : Fin r, 15 * n + 32 * g ≤ 32 * (univ.filter (fun i : Fin n =>
          (if h : (false, i) ∈ S then a ⟨(false, i), h⟩ else z ⟨(false, i), h⟩) ≠
          (if h : (true, M j i) ∈ S then a ⟨(true, M j i), h⟩ else z ⟨(true, M j i), h⟩))).card ∧
          32 * (univ.filter (fun i : Fin n =>
          (if h : (false, i) ∈ S then a ⟨(false, i), h⟩ else z ⟨(false, i), h⟩) ≠
          (if h : (true, M j i) ∈ S then a ⟨(true, M j i), h⟩ else z ⟨(true, M j i), h⟩))).card + 32 * g ≤ 17 * n) →
          false = true) ∧
        ((∃ j : Fin r, 32 * (univ.filter (fun i : Fin n =>
          (if h : (false, i) ∈ S then a ⟨(false, i), h⟩ else z ⟨(false, i), h⟩) ≠
          (if h : (true, M j i) ∈ S then a ⟨(true, M j i), h⟩ else z ⟨(true, M j i), h⟩))).card + 32 * g ≤ 15 * n ∨
          17 * n + 32 * g ≤ 32 * (univ.filter (fun i : Fin n =>
          (if h : (false, i) ∈ S then a ⟨(false, i), h⟩ else z ⟨(false, i), h⟩) ≠
          (if h : (true, M j i) ∈ S then a ⟨(true, M j i), h⟩ else z ⟨(true, M j i), h⟩))).card) →
          false = false))) = univ :=
      filter_true_of_mem fun _ _ => ⟨fun hy => by have := hy ⟨0, hrpos⟩; omega, fun _ => rfl⟩
    rw [hflt]
    simp
  have hn32 : 32 * g ≤ n := le_of_not_gt hng
  let w : ℕ := max 1 (g / 4)
  have hwpos : 0 < w := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hw_err : ∀ d : ℕ, 4 * (d % w) < g := by
    intro d
    by_cases hg8 : g < 8
    · have hw1 : w = 1 := by simp only [w]; omega
      rw [hw1, Nat.mod_one]; omega
    · have hw4 : w = g / 4 := by simp only [w]; omega
      have hlt : d % w < w := Nat.mod_lt d hwpos
      omega
  have hw_quo : ∀ d : ℕ, d ≤ n → d / w < 8 * (n / g + 1) := by
    intro d hd
    have hlt_ng : n < g * (n / g + 1) := by
      rw [mul_add, mul_one]; exact Nat.lt_mul_div_succ n hg
    by_cases hg4 : g < 4
    · have hw1 : w = 1 := by simp only [w]; omega
      rw [hw1, Nat.div_one]
      have : g * (n / g + 1) ≤ 3 * (n / g + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    · have hw4 : w = g / 4 := by simp only [w]; omega
      have hg7 : g ≤ 7 * w := by omega
      have hmul : w * (d / w) < w * (8 * (n / g + 1)) := by
        calc w * (d / w) ≤ d := Nat.mul_div_le d w
          _ ≤ n := hd
          _ < g * (n / g + 1) := hlt_ng
          _ ≤ (7 * w) * (n / g + 1) := Nat.mul_le_mul_right _ hg7
          _ < w * (8 * (n / g + 1)) := by nlinarith
      exact Nat.lt_of_mul_lt_mul_left hmul
  let bCnt : ℕ := 3 + Nat.clog 2 (n / g + 1)
  have hbCnt : 8 * (n / g + 1) ≤ 2 ^ bCnt := by
    have := Nat.le_pow_clog one_lt_two (n / g + 1)
    calc 8 * (n / g + 1) ≤ 8 * 2 ^ Nat.clog 2 (n / g + 1) := Nat.mul_le_mul_left 8 this
      _ = 2 ^ (3 + Nat.clog 2 (n / g + 1)) := by rw [pow_add]; norm_num
  let H : ℕ := Nat.clog 2 (r + 1) + 2
  let T : ℕ := 2 * H
  let E : Fin r → Finset (Fin n) := fun j =>
    univ.filter (fun i : Fin n => ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))
  have hEcard : ∀ j, (E j).card = cross j := fun _ => rfl
  let sLen : Fin r → ℕ := fun j => 16 * (1 + cross j * cross j / (g * g))
  have hsPos : ∀ j, 0 < sLen j := fun j => by dsimp only [sLen]; positivity
  have hsBound : ∀ j, 16 * (cross j) ^ 2 ≤ sLen j * g ^ 2 := by
    intro j
    have hlt : cross j * cross j < (cross j * cross j / (g * g) + 1) * (g * g) := by
      rw [add_mul, one_mul, mul_comm _ (g * g)]
      exact Nat.lt_mul_div_succ (cross j * cross j) (Nat.mul_pos hg hg)
    have : 16 * (cross j) ^ 2 ≤ 16 * ((1 + cross j * cross j / (g * g)) * (g * g)) := by
      rw [sq]; nlinarith
    simpa only [sLen, sq, mul_assoc] using this
  let isExact : Fin r → Prop := fun j => cross j ≤ sLen j * T
  let bBit : Fin r → ℕ := fun j => min (cross j) (sLen j * T)
  let b : ℕ := ∑ j : Fin r, (bCnt + bBit j)
  have hb_le : b ≤ 64 * (r * (1 + Nat.clog 2 (n / g + 1)) +
      ∑ j : Fin r, min (cross j)
        ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1)))) := by
    have h1 : ∀ j : Fin r, bCnt ≤ 64 * (1 + Nat.clog 2 (n / g + 1)) := fun j => by
      dsimp only [bCnt]; omega
    have h2 : ∀ j : Fin r, bBit j ≤ 64 * min (cross j)
        ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1))) := by
      intro j
      dsimp only [bBit, sLen, T, H]
      have hTle : 16 * (1 + cross j * cross j / (g * g)) * (2 * (Nat.clog 2 (r + 1) + 2)) ≤
          64 * ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1))) := by
        have : 2 * (Nat.clog 2 (r + 1) + 2) ≤ 4 * (1 + Nat.clog 2 (r + 1)) := by omega
        calc 16 * (1 + cross j * cross j / (g * g)) * (2 * (Nat.clog 2 (r + 1) + 2))
            ≤ 16 * (1 + cross j * cross j / (g * g)) * (4 * (1 + Nat.clog 2 (r + 1))) :=
              Nat.mul_le_mul_left _ this
          _ = 64 * ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1))) := by ring
      rcases le_total (cross j) ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1))) with hle | hle
      · rw [min_eq_left hle]; exact (min_le_left _ _).trans (by omega)
      · rw [min_eq_right hle]; exact (min_le_right _ _).trans hTle
    calc b = ∑ j : Fin r, bCnt + ∑ j : Fin r, bBit j := sum_add_distrib
      _ ≤ ∑ _j : Fin r, (64 * (1 + Nat.clog 2 (n / g + 1))) +
            ∑ j : Fin r, (64 * min (cross j)
              ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1)))) :=
          Nat.add_le_add (sum_le_sum fun j _ => h1 j) (sum_le_sum fun j _ => h2 j)
      _ = 64 * (r * (1 + Nat.clog 2 (n / g + 1)) +
            ∑ j : Fin r, min (cross j)
              ((1 + cross j * cross j / (g * g)) * (1 + Nat.clog 2 (r + 1)))) := by
          rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, ← mul_sum]; ring
  let SeedComp : Fin r → Type := fun j =>
    if isExact j then Fin 1 else Fin T → Fin (sLen j) → Fin (cross j)
  letI : ∀ j, Fintype (SeedComp j) := fun j => by
    dsimp only [SeedComp]; split_ifs <;> infer_instance
  letI : ∀ j, Nonempty (SeedComp j) := fun j => by
    dsimp only [SeedComp]
    split_ifs with h
    · exact ⟨0⟩
    · have hcpos : 0 < cross j := by
        have : 0 < sLen j * T := Nat.mul_pos (hsPos j) (by dsimp only [T, H]; omega)
        dsimp only [isExact] at h; omega
      exact ⟨fun _ _ => ⟨0, hcpos⟩⟩
  let SeedType := ∀ j : Fin r, SeedComp j
  let R : ℕ := Fintype.card SeedType
  have hRpos : 0 < R := Fintype.card_pos
  let eSeed : Fin R ≃ SeedType := (Fintype.equivFin SeedType).symm
  let MsgComp : Fin r → Type := fun j => Fin (2 ^ bCnt) × (Fin (bBit j) → Bool)
  let MsgType := ∀ j : Fin r, MsgComp j
  have hMsgCard : Fintype.card MsgType = 2 ^ b := by
    calc Fintype.card MsgType = ∏ j : Fin r, Fintype.card (MsgComp j) := Fintype.card_pi
      _ = ∏ j : Fin r, 2 ^ (bCnt + bBit j) := prod_congr rfl fun j _ => by
          simp only [MsgComp, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
            Fintype.card_bool, pow_add]
      _ = 2 ^ b := by rw [prod_pow_eq_pow_sum]
  let eMsg : MsgType ≃ Fin (2 ^ b) := Fintype.equivFinOfCardEq hMsgCard
  let eE : ∀ j : Fin r, Fin (cross j) ≃ {i : Fin n // i ∈ E j} := fun j =>
    ((E j).equivFin.trans (Equiv.cast (by rw [hEcard j]))).symm
  let aEnd : ∀ (j : Fin r) (i : {i : Fin n // i ∈ E j}), {v : V // v ∈ S} := fun j i =>
    if h : (false, i.1) ∈ S then ⟨(false, i.1), h⟩
    else ⟨(true, M j i.1), by
      have hi := (mem_filter.1 i.2).2
      tauto⟩
  let bEnd : ∀ (j : Fin r) (i : {i : Fin n // i ∈ E j}), {v : V // v ∉ S} := fun j i =>
    if h : (false, i.1) ∈ S then ⟨(true, M j i.1), by
      have hi := (mem_filter.1 i.2).2
      tauto⟩
    else ⟨(false, i.1), h⟩
  have hEndXor : ∀ (a : A) (z : B) (j : Fin r) (i : {i : Fin n // i ∈ E j}),
      let x := fun v : V => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
      (x (false, i.1) ≠ x (true, M j i.1)) ↔ (a (aEnd j i) ≠ z (bEnd j i)) := by
    intro a z j i x
    dsimp only [aEnd, bEnd, x]
    have hi := (mem_filter.1 i.2).2
    by_cases h : (false, i.1) ∈ S
    · have h2 : (true, M j i.1) ∉ S := by tauto
      simp only [dif_pos h, dif_neg h2]
    · have h2 : (true, M j i.1) ∈ S := by tauto
      simp only [dif_neg h, dif_pos h2]; exact ne_comm
  let dA : A → Fin r → ℕ := fun a j =>
    (univ.filter (fun i : Fin n =>
      ∃ (h1 : (false, i) ∈ S) (h2 : (true, M j i) ∈ S),
        a ⟨(false, i), h1⟩ ≠ a ⟨(true, M j i), h2⟩)).card
  let dB : B → Fin r → ℕ := fun z j =>
    (univ.filter (fun i : Fin n =>
      ∃ (h1 : (false, i) ∉ S) (h2 : (true, M j i) ∉ S),
        z ⟨(false, i), h1⟩ ≠ z ⟨(true, M j i), h2⟩)).card
  have hdA_le : ∀ a j, dA a j ≤ n := fun a j => (card_filter_le _ _).trans (by simp)
  have hD_split : ∀ (a : A) (z : B) (j : Fin r),
      let x := fun v : V => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
      (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card =
        dA a j + dB z j + (univ.filter (fun k : Fin (cross j) =>
          a (aEnd j (eE j k)) ≠ z (bEnd j (eE j k)))).card := by
    intro a z j x
    set P : Fin n → Prop := fun i => x (false, i) ≠ x (true, M j i)
    set SA := univ.filter (fun i : Fin n => (false, i) ∈ S ∧ (true, M j i) ∈ S)
    set SB := univ.filter (fun i : Fin n => (false, i) ∉ S ∧ (true, M j i) ∉ S)
    have hdisjAB : Disjoint (SA.filter P) (SB.filter P) :=
      disjoint_filter_filter (disjoint_filter.2 fun i _ h1 h2 => h2.1 h1.1)
    have hdisjABE : Disjoint (SA.filter P ∪ SB.filter P) ((E j).filter P) := by
      refine disjoint_union_left.2 ⟨?_, ?_⟩
      · exact disjoint_filter_filter (disjoint_filter.2 fun i _ h1 h2 => h2 (by tauto))
      · exact disjoint_filter_filter (disjoint_filter.2 fun i _ h1 h2 => h2 (by tauto))
    have hunion : univ.filter P = (SA.filter P ∪ SB.filter P) ∪ (E j).filter P := by
      ext i
      simp only [mem_union, mem_filter, mem_univ, true_and, SA, SB, E]
      tauto
    have hcA : (SA.filter P).card = dA a j := by
      congr 1; ext i
      simp only [mem_filter, mem_univ, true_and, SA, P, x]
      constructor
      · rintro ⟨⟨h1, h2⟩, hne⟩; simp only [dif_pos h1, dif_pos h2] at hne; exact ⟨h1, h2, hne⟩
      · rintro ⟨h1, h2, hne⟩; simp only [dif_pos h1, dif_pos h2]; exact ⟨⟨h1, h2⟩, hne⟩
    have hcB : (SB.filter P).card = dB z j := by
      congr 1; ext i
      simp only [mem_filter, mem_univ, true_and, SB, P, x]
      constructor
      · rintro ⟨⟨h1, h2⟩, hne⟩; simp only [dif_neg h1, dif_neg h2] at hne; exact ⟨h1, h2, hne⟩
      · rintro ⟨h1, h2, hne⟩; simp only [dif_neg h1, dif_neg h2]; exact ⟨⟨h1, h2⟩, hne⟩
    have hcE : ((E j).filter P).card = (univ.filter (fun k : Fin (cross j) =>
        a (aEnd j (eE j k)) ≠ z (bEnd j (eE j k)))).card := by
      refine card_bij (fun i hi => (eE j).symm ⟨i, (mem_filter.1 hi).1⟩) ?_ ?_ ?_
      · intro i hi
        simp only [mem_filter, mem_univ, true_and, Equiv.apply_symm_apply]
        exact (hEndXor a z j ⟨i, (mem_filter.1 hi).1⟩).1 (mem_filter.1 hi).2
      · intro i1 h1 i2 h2 heq
        have := congrArg Subtype.val ((eE j).symm.injective heq)
        exact this
      · intro k hk
        refine ⟨(eE j k).1, mem_filter.2 ⟨(eE j k).2, (hEndXor a z j (eE j k)).2 (mem_filter.1 hk).2⟩, ?_⟩
        simp
    rw [hunion, card_union_of_disjoint hdisjABE, card_union_of_disjoint hdisjAB, hcA, hcB, hcE]
  let sendRaw : SeedType → A → MsgType := fun sd a j =>
    (⟨dA a j / w, lt_of_lt_of_le (hw_quo (dA a j) (hdA_le a j)) hbCnt⟩,
     if h : isExact j then
       fun idx => a (aEnd j (eE j ⟨idx.val, lt_of_lt_of_le idx.isLt (min_le_left _ _)⟩))
     else
       let f : Fin T → Fin (sLen j) → Fin (cross j) := cast (by dsimp only [SeedComp]; rw [if_neg h]) (sd j)
       fun idx =>
         have hlt : idx.val < sLen j * T := lt_of_lt_of_le idx.isLt (min_le_right _ _)
         let t : Fin T := ⟨idx.val / sLen j, Nat.div_lt_of_lt_mul hlt⟩
         let l : Fin (sLen j) := ⟨idx.val % sLen j, Nat.mod_lt _ (hsPos j)⟩
         a (aEnd j (eE j (f t l))))
  let recvRaw : SeedType → MsgType → B → Bool := fun sd msg z =>
    decide (∀ j : Fin r,
      let qj := (msg j).1.val
      let bits := (msg j).2
      if h : isExact j then
        let cE := (univ.filter (fun k : Fin (cross j) =>
          bits ⟨k.val, lt_of_lt_of_le k.isLt (by dsimp only [bBit]; rw [min_eq_left h])⟩ ≠
            z (bEnd j (eE j k)))).card
        let est := w * qj + dB z j + cE
        15 * n ≤ 32 * est ∧ 32 * est ≤ 17 * n
      else
        let f : Fin T → Fin (sLen j) → Fin (cross j) := cast (by dsimp only [SeedComp]; rw [if_neg h]) (sd j)
        let okBlocks := (univ.filter (fun t : Fin T =>
          let cnt := (univ.filter (fun l : Fin (sLen j) =>
            let pos := t.val * sLen j + l.val
            have hpos : pos < bBit j := by
              have h1 : pos < sLen j * T := by
                dsimp only [pos]
                have ht : t.val + 1 ≤ T := t.isLt
                have hl : l.val < sLen j := l.isLt
                calc t.val * sLen j + l.val < t.val * sLen j + sLen j := Nat.add_lt_add_left hl _
                  _ = (t.val + 1) * sLen j := by ring
                  _ ≤ T * sLen j := Nat.mul_le_mul_right _ ht
                  _ = sLen j * T := mul_comm _ _
              dsimp only [bBit]; rw [min_eq_right (le_of_not_ge h)]; exact h1
            bits ⟨pos, hpos⟩ ≠ z (bEnd j (eE j (f t l))))).card
          let est2 := 2 * sLen j * (w * qj + dB z j) + 2 * cross j * cnt
          15 * sLen j * n ≤ 16 * est2 ∧ 16 * est2 ≤ 17 * sLen j * n)).card
        H < okBlocks)
  refine ⟨b, ⟨R, hRpos, fun seed a => eMsg (sendRaw (eSeed seed) a),
    fun seed m z => recvRaw (eSeed seed) (eMsg.symm m) z, fun a z => ?_⟩, hb_le⟩
  dsimp only
  set x := fun v : V => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
  set D := fun j : Fin r => (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card
  set yes := ∀ j : Fin r, 15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n
  set no := ∃ j : Fin r, 32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j
  let BadComp : ∀ j : Fin r, Finset (SeedComp j) := fun j =>
    if h : isExact j then ∅
    else
      let eC : SeedComp j ≃ (Fin T → Fin (sLen j) → Fin (cross j)) :=
        Equiv.cast (by dsimp only [SeedComp]; rw [if_neg h])
      let B1 : Finset (Fin (sLen j) → Fin (cross j)) :=
        univ.filter (fun f => ((sLen j : ℤ) * g) ^ 2 ≤
          (2 * ((cross j : ℤ) * (univ.filter (fun l =>
            a (aEnd j (eE j (f l))) ≠ z (bEnd j (eE j (f l))))).card -
            sLen j * (univ.filter (fun k =>
              a (aEnd j (eE j k)) ≠ z (bEnd j (eE j k)))).card)) ^ 2)
      univ.filter (fun sdj => H ≤ (univ.filter (fun t : Fin T => eC sdj t ∈ B1)).card)
  have hBadCard : ∀ j : Fin r, 4 ^ H * (BadComp j).card ≤ Fintype.card (SeedComp j) := by
    intro j
    dsimp only [BadComp]
    split_ifs with h
    · simp
    · let eC : SeedComp j ≃ (Fin T → Fin (sLen j) → Fin (cross j)) :=
        Equiv.cast (by dsimp only [SeedComp]; rw [if_neg h])
      let B1 : Finset (Fin (sLen j) → Fin (cross j)) :=
        univ.filter (fun f => ((sLen j : ℤ) * g) ^ 2 ≤
          (2 * ((cross j : ℤ) * (univ.filter (fun l =>
            a (aEnd j (eE j (f l))) ≠ z (bEnd j (eE j (f l))))).card -
            sLen j * (univ.filter (fun k =>
              a (aEnd j (eE j k)) ≠ z (bEnd j (eE j k)))).card)) ^ 2)
      have hcpos : 0 < cross j := by
        have : 0 < sLen j * T := Nat.mul_pos (hsPos j) (by dsimp only [T, H]; omega)
        dsimp only [isExact] at h; omega
      have hB1 : 16 * B1.card ≤ Fintype.card (Fin (sLen j) → Fin (cross j)) := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
        exact cheb_half (cross j) (sLen j) g
          (fun k => a (aEnd j (eE j k)) ≠ z (bEnd j (eE j k))) hcpos (hsPos j) (hsBound j)
      have hamp := amp_majority B1 H hB1
      have hcard_eq : (univ.filter (fun sdj : SeedComp j =>
          H ≤ (univ.filter (fun t : Fin T => eC sdj t ∈ B1)).card)).card =
          (univ.filter (fun f : Fin (2 * H) → (Fin (sLen j) → Fin (cross j)) =>
            H ≤ (univ.filter (fun t => f t ∈ B1)).card)).card := by
        refine card_bij (fun sdj _ => eC sdj) ?_ ?_ ?_
        · intro sdj hsdj; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hsdj).2⟩
        · intro s1 _ s2 _ h12; exact eC.injective h12
        · intro f hf
          exact ⟨eC.symm f, mem_filter.2 ⟨mem_univ _, by simpa using (mem_filter.1 hf).2⟩, by simp⟩
      have hcard_tot : Fintype.card (SeedComp j) =
          (Fintype.card (Fin (sLen j) → Fin (cross j))) ^ (2 * H) := by
        calc Fintype.card (SeedComp j)
            = Fintype.card (Fin T → Fin (sLen j) → Fin (cross j)) := Fintype.card_congr eC
          _ = (Fintype.card (Fin (sLen j) → Fin (cross j))) ^ T := by
              rw [Fintype.card_fun, Fintype.card_fin]
      rw [hcard_eq, hcard_tot]
      exact hamp
  let BadAll : Finset SeedType := univ.filter (fun sd => ∃ j : Fin r, sd j ∈ BadComp j)
  have hBadAll : 4 ^ H * BadAll.card ≤ r * R := by
    let slice : Fin r → Finset SeedType := fun j =>
      Fintype.piFinset (fun l : Fin r => if l = j then BadComp l else univ)
    have hsub : BadAll ⊆ univ.biUnion slice := by
      intro sd hsd
      obtain ⟨j, hj⟩ := (mem_filter.1 hsd).2
      refine mem_biUnion.2 ⟨j, mem_univ _, Fintype.mem_piFinset.2 fun l => ?_⟩
      by_cases hlj : l = j
      · subst hlj; simpa using hj
      · simp [hlj]
    have hterm : ∀ j : Fin r, 4 ^ H * (slice j).card ≤ R := by
      intro j
      dsimp only [slice]
      rw [Fintype.card_piFinset, ← mul_prod_erase univ
        (fun l : Fin r => (if l = j then BadComp l else univ).card) (mem_univ j)]
      have h1 : (if j = j then BadComp j else univ).card = (BadComp j).card := by simp
      have h2 : ∏ l ∈ univ.erase j, (if l = j then BadComp l else univ).card =
          ∏ l ∈ univ.erase j, Fintype.card (SeedComp l) :=
        prod_congr rfl fun l hl => by
          rw [if_neg (ne_of_mem_erase hl), card_univ]
      rw [h1, h2, ← mul_assoc]
      calc 4 ^ H * (BadComp j).card * ∏ l ∈ univ.erase j, Fintype.card (SeedComp l)
          ≤ Fintype.card (SeedComp j) * ∏ l ∈ univ.erase j, Fintype.card (SeedComp l) :=
            Nat.mul_le_mul_right _ (hBadCard j)
        _ = ∏ l : Fin r, Fintype.card (SeedComp l) :=
            mul_prod_erase univ (fun l : Fin r => Fintype.card (SeedComp l)) (mem_univ j)
        _ = R := by simp only [R, SeedType, Fintype.card_pi]
    calc 4 ^ H * BadAll.card
        ≤ 4 ^ H * ∑ j : Fin r, (slice j).card :=
          Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
      _ = ∑ j : Fin r, 4 ^ H * (slice j).card := by rw [mul_sum]
      _ ≤ ∑ _j : Fin r, R := sum_le_sum fun j _ => hterm j
      _ = r * R := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have h4H : 4 * r ≤ 4 ^ H := by
    have hcl := Nat.le_pow_clog one_lt_two (r + 1)
    have : 4 ^ H = 16 * (2 ^ Nat.clog 2 (r + 1)) ^ 2 := by
      dsimp only [H]; rw [pow_add, show (4 : ℕ) ^ 2 = 16 by norm_num,
        show (4 : ℕ) ^ Nat.clog 2 (r + 1) = (2 ^ Nat.clog 2 (r + 1)) ^ 2 by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      ring
    nlinarith
  have hBadLe : 4 * BadAll.card ≤ R := by
    have h1 : 4 * r * BadAll.card ≤ r * R := (Nat.mul_le_mul_right _ h4H).trans hBadAll
    have h2 : r * (4 * BadAll.card) = 4 * r * BadAll.card := by ring
    exact Nat.le_of_mul_le_mul_left (h2.symm ▸ h1) hrpos
  have hGoodSpec : ∀ sd : SeedType, sd ∉ BadAll →
      (yes → recvRaw sd (sendRaw sd a) z = true) ∧
      (no → recvRaw sd (sendRaw sd a) z = false) := by
    intro sd hsd
    have hnotBad : ∀ j : Fin r, sd j ∉ BadComp j := fun j hj =>
      hsd (mem_filter.2 ⟨mem_univ _, ⟨j, hj⟩⟩)
    have hjSpec : ∀ j : Fin r,
        let qj := (sendRaw sd a j).1.val
        let bits := (sendRaw sd a j).2
        let ok : Prop :=
          if h : isExact j then
            let cE := (univ.filter (fun k : Fin (cross j) =>
              bits ⟨k.val, lt_of_lt_of_le k.isLt (by dsimp only [bBit]; rw [min_eq_left h])⟩ ≠
                z (bEnd j (eE j k)))).card
            let est := w * qj + dB z j + cE
            15 * n ≤ 32 * est ∧ 32 * est ≤ 17 * n
          else
            let f : Fin T → Fin (sLen j) → Fin (cross j) :=
              cast (by dsimp only [SeedComp]; rw [if_neg h]) (sd j)
            let okBlocks := (univ.filter (fun t : Fin T =>
              let cnt := (univ.filter (fun l : Fin (sLen j) =>
                let pos := t.val * sLen j + l.val
                have hpos : pos < bBit j := by
                  have h1 : pos < sLen j * T := by
                    dsimp only [pos]
                    have ht : t.val + 1 ≤ T := t.isLt
                    have hl : l.val < sLen j := l.isLt
                    calc t.val * sLen j + l.val < t.val * sLen j + sLen j := Nat.add_lt_add_left hl _
                      _ = (t.val + 1) * sLen j := by ring
                      _ ≤ T * sLen j := Nat.mul_le_mul_right _ ht
                      _ = sLen j * T := mul_comm _ _
                  dsimp only [bBit]; rw [min_eq_right (le_of_not_ge h)]; exact h1
                bits ⟨pos, hpos⟩ ≠ z (bEnd j (eE j (f t l))))).card
              let est2 := 2 * sLen j * (w * qj + dB z j) + 2 * cross j * cnt
              15 * sLen j * n ≤ 16 * est2 ∧ 16 * est2 ≤ 17 * sLen j * n)).card
            H < okBlocks
        ((15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n) → ok) ∧
        ((32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j) → ¬ ok) := by
      intro j
      dsimp only
      have hrem : 4 * (dA a j % w) < g := hw_err (dA a j)
      have hdiv : w * (dA a j / w) + dA a j % w = dA a j := Nat.div_add_mod (dA a j) w
      have hDs := hD_split a z j
      let dE := (univ.filter (fun k : Fin (cross j) =>
        a (aEnd j (eE j k)) ≠ z (bEnd j (eE j k)))).card
      by_cases h : isExact j
      · rw [dif_pos h]
        have hcE : (univ.filter (fun k : Fin (cross j) =>
            (sendRaw sd a j).2 ⟨k.val, lt_of_lt_of_le k.isLt (by dsimp only [bBit]; rw [min_eq_left h])⟩ ≠
              z (bEnd j (eE j k)))).card = dE := by
          congr 1; ext k
          simp only [mem_filter, mem_univ, true_and, sendRaw, dif_pos h]
        rw [hcE]
        change ((15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n) →
            15 * n ≤ 32 * (w * (dA a j / w) + dB z j + dE) ∧
            32 * (w * (dA a j / w) + dB z j + dE) ≤ 17 * n) ∧
          ((32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j) →
            ¬ (15 * n ≤ 32 * (w * (dA a j / w) + dB z j + dE) ∧
              32 * (w * (dA a j / w) + dB z j + dE) ≤ 17 * n))
        have hDj : D j = dA a j + dB z j + dE := hDs
        constructor <;> omega
      · rw [dif_neg h]
        set f : Fin T → Fin (sLen j) → Fin (cross j) :=
          cast (by dsimp only [SeedComp]; rw [if_neg h]) (sd j)
        have hnb := hnotBad j
        simp only [BadComp, dif_neg h, mem_filter, mem_univ, true_and, not_le] at hnb
        set goodT := univ.filter (fun t : Fin T =>
          ¬ (((sLen j : ℤ) * g) ^ 2 ≤
            (2 * ((cross j : ℤ) * (univ.filter (fun l =>
              a (aEnd j (eE j (f t l))) ≠ z (bEnd j (eE j (f t l))))).card -
              sLen j * dE)) ^ 2))
        have hgoodT : H < goodT.card := by
          have hsumT := card_filter_add_card_filter_not (s := (univ : Finset (Fin T)))
            (fun t => ((sLen j : ℤ) * g) ^ 2 ≤
              (2 * ((cross j : ℤ) * (univ.filter (fun l =>
                a (aEnd j (eE j (f t l))) ≠ z (bEnd j (eE j (f t l))))).card -
                sLen j * dE)) ^ 2)
          rw [card_univ, Fintype.card_fin] at hsumT
          have hbadLt : (univ.filter (fun t : Fin T =>
              ((sLen j : ℤ) * g) ^ 2 ≤
                (2 * ((cross j : ℤ) * (univ.filter (fun l =>
                  a (aEnd j (eE j (f t l))) ≠ z (bEnd j (eE j (f t l))))).card -
                  sLen j * dE)) ^ 2)).card < H := by
            refine lt_of_eq_of_lt ?_ hnb
            congr 1
          have hsumT' : (univ.filter (fun t : Fin T =>
              ((sLen j : ℤ) * g) ^ 2 ≤
                (2 * ((cross j : ℤ) * (univ.filter (fun l =>
                  a (aEnd j (eE j (f t l))) ≠ z (bEnd j (eE j (f t l))))).card -
                  sLen j * dE)) ^ 2)).card + goodT.card = 2 * H := hsumT
          omega
        have hcnt_eq : ∀ t : Fin T,
            (univ.filter (fun l : Fin (sLen j) =>
              let pos := t.val * sLen j + l.val
              have hpos : pos < bBit j := by
                have h1 : pos < sLen j * T := by
                  dsimp only [pos]
                  have ht : t.val + 1 ≤ T := t.isLt
                  have hl : l.val < sLen j := l.isLt
                  calc t.val * sLen j + l.val < t.val * sLen j + sLen j := Nat.add_lt_add_left hl _
                    _ = (t.val + 1) * sLen j := by ring
                    _ ≤ T * sLen j := Nat.mul_le_mul_right _ ht
                    _ = sLen j * T := mul_comm _ _
                dsimp only [bBit]; rw [min_eq_right (le_of_not_ge h)]; exact h1
              (sendRaw sd a j).2 ⟨pos, hpos⟩ ≠ z (bEnd j (eE j (f t l))))).card =
            (univ.filter (fun l : Fin (sLen j) =>
              a (aEnd j (eE j (f t l))) ≠ z (bEnd j (eE j (f t l))))).card := by
          intro t
          congr 1; ext l
          simp only [mem_filter, mem_univ, true_and, sendRaw, dif_neg h]
          have hdiv_t : (t.val * sLen j + l.val) / sLen j = t.val := by
            rw [mul_comm, Nat.mul_add_div (hsPos j), Nat.div_eq_of_lt l.isLt, add_zero]
          have hmod_l : (t.val * sLen j + l.val) % sLen j = l.val := by
            rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt l.isLt]
          have hft : ∀ hlt, (⟨(t.val * sLen j + l.val) / sLen j, hlt⟩ : Fin T) = t :=
            fun _ => Fin.ext hdiv_t
          have hfl : ∀ hlt, (⟨(t.val * sLen j + l.val) % sLen j, hlt⟩ : Fin (sLen j)) = l :=
            fun _ => Fin.ext hmod_l
          simp only [hft, hfl, f]
        have hblock_acc : ∀ t ∈ goodT,
            let cnt := (univ.filter (fun l : Fin (sLen j) =>
              a (aEnd j (eE j (f t l))) ≠ z (bEnd j (eE j (f t l))))).card
            let est2 := 2 * sLen j * (w * (dA a j / w) + dB z j) + 2 * cross j * cnt
            ((15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n) →
              15 * sLen j * n ≤ 16 * est2 ∧ 16 * est2 ≤ 17 * sLen j * n) ∧
            ((32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j) →
              ¬ (15 * sLen j * n ≤ 16 * est2 ∧ 16 * est2 ≤ 17 * sLen j * n)) := by
          intro t ht
          have hlt := not_le.1 (mem_filter.1 ht).2
          have habs := abs_lt.1 (abs_lt_of_sq_lt_sq hlt (by positivity))
          have hDj : D j = dA a j + dB z j + dE := hDs
          set quo := dA a j / w
          set rem := dA a j % w
          have hs_nn : (0 : ℤ) ≤ sLen j := by positivity
          have hremZ : 4 * (rem : ℤ) ≤ g := by exact_mod_cast hrem.le
          have hremS : 4 * ((sLen j : ℤ) * (rem : ℤ)) ≤ (sLen j : ℤ) * g := by
            have := mul_le_mul_of_nonneg_left hremZ hs_nn
            linarith
          have hrem_nn : (0 : ℤ) ≤ (sLen j : ℤ) * (rem : ℤ) := by positivity
          dsimp only
          zify at hdiv hDj ⊢
          have hdivS : (sLen j : ℤ) * (w : ℤ) * (quo : ℤ) + (sLen j : ℤ) * (rem : ℤ) =
              (sLen j : ℤ) * dA a j := by
            linear_combination (sLen j : ℤ) * hdiv
          have hDjS : (sLen j : ℤ) * D j =
              (sLen j : ℤ) * dA a j + (sLen j : ℤ) * dB z j + (sLen j : ℤ) * dE := by
            linear_combination (sLen j : ℤ) * hDj
          constructor
          · intro ⟨hy1, hy2⟩
            have hy1S := mul_le_mul_of_nonneg_left hy1 hs_nn
            have hy2S := mul_le_mul_of_nonneg_left hy2 hs_nn
            constructor <;> linarith
          · rintro (hn1 | hn2) ⟨ha1, ha2⟩
            · have hn1S := mul_le_mul_of_nonneg_left hn1 hs_nn
              linarith
            · have hn2S := mul_le_mul_of_nonneg_left hn2 hs_nn
              linarith
        constructor
        · intro hy
          refine lt_of_lt_of_le hgoodT (card_le_card fun t ht => ?_)
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          rw [hcnt_eq t]
          exact (hblock_acc t ht).1 hy
        · intro hno
          let okSet : Finset (Fin T) := univ.filter (fun t : Fin T =>
              let cnt := (univ.filter (fun l : Fin (sLen j) =>
                let pos := t.val * sLen j + l.val
                have hpos : pos < bBit j := by
                  have h1 : pos < sLen j * T := by
                    dsimp only [pos]
                    have ht : t.val + 1 ≤ T := t.isLt
                    have hl : l.val < sLen j := l.isLt
                    calc t.val * sLen j + l.val < t.val * sLen j + sLen j := Nat.add_lt_add_left hl _
                      _ = (t.val + 1) * sLen j := by ring
                      _ ≤ T * sLen j := Nat.mul_le_mul_right _ ht
                      _ = sLen j * T := mul_comm _ _
                  dsimp only [bBit]; rw [min_eq_right (le_of_not_ge h)]; exact h1
                (sendRaw sd a j).2 ⟨pos, hpos⟩ ≠ z (bEnd j (eE j (f t l))))).card
              let est2 := 2 * sLen j * (w * (sendRaw sd a j).1.val + dB z j) + 2 * cross j * cnt
              15 * sLen j * n ≤ 16 * est2 ∧ 16 * est2 ≤ 17 * sLen j * n)
          have hdisj : Disjoint okSet goodT := by
            rw [disjoint_left]
            intro t ht1 ht2
            have h1 := (mem_filter.1 ht1).2
            rw [hcnt_eq t] at h1
            exact (hblock_acc t ht2).2 hno h1
          have hsum : (okSet ∪ goodT).card = okSet.card + goodT.card :=
            card_union_of_disjoint hdisj
          have hleT : (okSet ∪ goodT).card ≤ 2 * H :=
            (card_le_univ (okSet ∪ goodT)).trans (by simp [T])
          change ¬ (H < okSet.card)
          omega
    constructor
    · intro hy
      dsimp only [recvRaw]
      rw [decide_eq_true_iff]
      intro j
      exact (hjSpec j).1 (hy j)
    · intro ⟨j, hj⟩
      dsimp only [recvRaw]
      rw [decide_eq_false_iff_not]
      intro hall
      exact (hjSpec j).2 hj (hall j)
  have hgoodCount : R - BadAll.card ≤
      (univ.filter (fun seed : Fin R =>
        (yes → recvRaw (eSeed seed) (eMsg.symm (eMsg (sendRaw (eSeed seed) a))) z = true) ∧
        (no → recvRaw (eSeed seed) (eMsg.symm (eMsg (sendRaw (eSeed seed) a))) z = false))).card := by
    have hcomp : (univ \ BadAll).card = R - BadAll.card := by
      rw [card_sdiff, inter_univ, card_univ]
    rw [← hcomp]
    refine card_le_card_of_injOn eSeed.symm (fun sd hsd => ?_) eSeed.symm.injective.injOn
    rw [mem_coe, mem_sdiff] at hsd
    rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact hGoodSpec sd hsd.2
  change 2 * R ≤ 3 * (univ.filter (fun seed : Fin R =>
    (yes → recvRaw (eSeed seed) (eMsg.symm (eMsg (sendRaw (eSeed seed) a))) z = true) ∧
    (no → recvRaw (eSeed seed) (eMsg.symm (eMsg (sendRaw (eSeed seed) a))) z = false))).card
  omega

end UpperBound

section HammingBall

lemma hamming_ball_pow5 (N r : ℕ) (hr : 5 * r ≤ 2 * N) :
    ((univ.filter (fun x : Fin N → Bool =>
      (univ.filter (fun i => x i = true)).card ≤ r)).card) ^ 5 * 108 ^ N ≤ 3125 ^ N := by
  classical
  set B := univ.filter (fun x : Fin N → Bool =>
    (univ.filter (fun i => x i = true)).card ≤ r)
  have hwt : ∀ x : Fin N → Bool,
      2 ^ (univ.filter (fun i => x i = true)).card *
        3 ^ (N - (univ.filter (fun i => x i = true)).card) =
      ∏ i : Fin N, (if x i = true then (2 : ℕ) else 3) := by
    intro x
    rw [← prod_filter_mul_prod_filter_not univ (fun i => x i = true)]
    have h1 : ∏ i ∈ univ.filter (fun i => x i = true), (if x i = true then (2 : ℕ) else 3) =
        2 ^ (univ.filter (fun i => x i = true)).card := by
      rw [prod_congr rfl (fun i hi => by rw [if_pos (mem_filter.1 hi).2]), prod_const]
    have h2 : ∏ i ∈ univ.filter (fun i => ¬ x i = true), (if x i = true then (2 : ℕ) else 3) =
        3 ^ (N - (univ.filter (fun i => x i = true)).card) := by
      have hc := card_filter_add_card_filter_not (s := (univ : Finset (Fin N))) (fun i => x i = true)
      rw [card_univ, Fintype.card_fin] at hc
      have hsub : (univ.filter (fun i => ¬ x i = true)).card =
          N - (univ.filter (fun i => x i = true)).card := by omega
      rw [prod_congr rfl (fun i hi => by rw [if_neg (mem_filter.1 hi).2]), prod_const, hsub]
    rw [h1, h2]
  have hsum5 : ∑ x : Fin N → Bool, ∏ i : Fin N, (if x i = true then (2 : ℕ) else 3) = 5 ^ N := by
    have h := (Fintype.prod_sum (fun (_ : Fin N) (b : Bool) => if b = true then (2 : ℕ) else 3)).symm
    have hRHS : ∏ _i : Fin N, ∑ b : Bool, (if b = true then (2 : ℕ) else 3) = 5 ^ N := by
      rw [prod_const, card_univ, Fintype.card_fin]
      have : (∑ b : Bool, (if b = true then (2 : ℕ) else 3)) = 5 := by decide
      rw [this]
    simpa [hRHS] using h
  have hBsum : B.card * (2 ^ r * 3 ^ (N - r)) ≤ 5 ^ N := by
    have hterm : ∀ x ∈ B, 2 ^ r * 3 ^ (N - r) ≤
        ∏ i : Fin N, (if x i = true then (2 : ℕ) else 3) := by
      intro x hx
      rw [← hwt x]
      set k := (univ.filter (fun i => x i = true)).card
      have hkr : k ≤ r := (mem_filter.1 hx).2
      have hkN : k ≤ N := (card_filter_le _ _).trans (by simp)
      have hrN : r ≤ N := by omega
      have h1 : 2 ^ r = 2 ^ k * 2 ^ (r - k) := by rw [← pow_add, Nat.add_sub_of_le hkr]
      have h2 : 3 ^ (N - k) = 3 ^ (N - r) * 3 ^ (r - k) := by
        rw [← pow_add, show N - r + (r - k) = N - k by omega]
      rw [h1, h2]
      have h23 : 2 ^ (r - k) ≤ 3 ^ (r - k) := Nat.pow_le_pow_left (by omega) _
      calc 2 ^ k * 2 ^ (r - k) * 3 ^ (N - r) = 2 ^ k * 3 ^ (N - r) * 2 ^ (r - k) := by ring
        _ ≤ 2 ^ k * 3 ^ (N - r) * 3 ^ (r - k) := Nat.mul_le_mul_left _ h23
        _ = 2 ^ k * (3 ^ (N - r) * 3 ^ (r - k)) := by ring
    calc B.card * (2 ^ r * 3 ^ (N - r)) = B.card • (2 ^ r * 3 ^ (N - r)) := by rw [smul_eq_mul]
      _ ≤ ∑ x ∈ B, ∏ i : Fin N, (if x i = true then (2 : ℕ) else 3) :=
          card_nsmul_le_sum B _ _ hterm
      _ ≤ ∑ x : Fin N → Bool, ∏ i : Fin N, (if x i = true then (2 : ℕ) else 3) :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
      _ = 5 ^ N := hsum5
  have h5 := Nat.pow_le_pow_left hBsum 5
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at h5
  have h108 : 108 ^ N ≤ 2 ^ (r * 5) * 3 ^ ((N - r) * 5) := by
    have hrN : r ≤ N := by omega
    have hsplit1 : 2 ^ (2 * N) = 2 ^ (r * 5) * 2 ^ (2 * N - r * 5) := by
      rw [← pow_add, Nat.add_sub_of_le (by omega)]
    have hsplit2 : 3 ^ ((N - r) * 5) = 3 ^ (3 * N) * 3 ^ (2 * N - r * 5) := by
      rw [← pow_add, show 3 * N + (2 * N - r * 5) = (N - r) * 5 by omega]
    have h23 : 2 ^ (2 * N - r * 5) ≤ 3 ^ (2 * N - r * 5) := Nat.pow_le_pow_left (by omega) _
    calc 108 ^ N = (2 ^ 2 * 3 ^ 3) ^ N := by norm_num
      _ = 2 ^ (2 * N) * 3 ^ (3 * N) := by rw [mul_pow, ← pow_mul, ← pow_mul]
      _ = 2 ^ (r * 5) * 3 ^ (3 * N) * 2 ^ (2 * N - r * 5) := by rw [hsplit1]; ring
      _ ≤ 2 ^ (r * 5) * 3 ^ (3 * N) * 3 ^ (2 * N - r * 5) := Nat.mul_le_mul_left _ h23
      _ = 2 ^ (r * 5) * 3 ^ ((N - r) * 5) := by rw [hsplit2]; ring
  calc B.card ^ 5 * 108 ^ N
      ≤ B.card ^ 5 * (2 ^ (r * 5) * 3 ^ ((N - r) * 5)) := Nat.mul_le_mul_left _ h108
    _ ≤ 5 ^ (N * 5) := h5
    _ = 3125 ^ N := by rw [mul_comm, pow_mul]; norm_num

lemma lb_from_bijective_decoder {N b : ℕ} (hN : 0 < N)
    (send : (Fin N → Bool) → Fin (2 ^ b))
    (errMap : Fin (2 ^ b) → (Fin N → Bool) → (Fin N → Bool))
    (hbij : ∀ m : Fin (2 ^ b), Function.Injective (errMap m))
    (hacc : 5 * (univ.filter (fun p : (Fin N → Bool) × Fin N =>
      errMap (send p.1) p.1 p.2 = true)).card ≤ 2 * (2 ^ N * N) - 2 ^ N * N / 50) :
    N ≤ 50 * b + 500 := by
  classical
  by_cases hsmall : N < 50
  · omega
  set r := (2 * N) / 5
  have hr : 5 * r ≤ 2 * N := Nat.mul_div_le (2 * N) 5
  set GoodU := univ.filter (fun u : Fin N → Bool =>
    (univ.filter (fun i : Fin N => errMap (send u) u i = true)).card ≤ r)
  have hGoodU : 2 ^ N ≤ 200 * GoodU.card := by
    set BadU := univ.filter (fun u : Fin N → Bool =>
      r < (univ.filter (fun i : Fin N => errMap (send u) u i = true)).card)
    have hsum_err : (univ.filter (fun p : (Fin N → Bool) × Fin N =>
        errMap (send p.1) p.1 p.2 = true)).card =
        ∑ u : Fin N → Bool, (univ.filter (fun i : Fin N => errMap (send u) u i = true)).card := by
      rw [← card_sigma]
      refine card_bij (fun p _ => ⟨p.1, p.2⟩) ?_ ?_ ?_
      · intro p hp; simp only [mem_sigma, mem_univ, mem_filter, true_and] at hp ⊢; exact hp
      · intro p1 _ p2 _ h; exact Prod.ext (congrArg Sigma.fst h) (by cases p1; cases p2; simp_all)
      · intro s hs; simp only [mem_sigma, mem_univ, mem_filter, true_and] at hs
        exact ⟨(s.1, s.2), mem_filter.2 ⟨mem_univ _, hs⟩, rfl⟩
    have hBadMul : BadU.card * (r + 1) ≤ ∑ u : Fin N → Bool,
        (univ.filter (fun i : Fin N => errMap (send u) u i = true)).card := by
      calc BadU.card * (r + 1) = BadU.card • (r + 1) := by rw [smul_eq_mul]
        _ ≤ ∑ u ∈ BadU, (univ.filter (fun i : Fin N => errMap (send u) u i = true)).card :=
            card_nsmul_le_sum _ _ _ (fun u hu => (mem_filter.1 hu).2)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)
    have h5r : 2 * N < 5 * (r + 1) := by
      have := Nat.lt_mul_div_succ (2 * N) (by norm_num : 0 < 5)
      omega
    have hpart : GoodU.card + BadU.card = 2 ^ N := by
      have := card_filter_add_card_filter_not (s := (univ : Finset (Fin N → Bool)))
        (fun u => (univ.filter (fun i : Fin N => errMap (send u) u i = true)).card ≤ r)
      simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, not_le] at this
      exact this
    have h1 : BadU.card * (2 * N) ≤ 5 * (BadU.card * (r + 1)) := by
      calc BadU.card * (2 * N) ≤ BadU.card * (5 * (r + 1)) := Nat.mul_le_mul_left _ h5r.le
        _ = 5 * (BadU.card * (r + 1)) := by ring
    have h2 : BadU.card * (2 * N) ≤ 2 * (2 ^ N * N) - 2 ^ N * N / 50 := by
      rw [hsum_err] at hacc
      exact h1.trans ((Nat.mul_le_mul_left 5 hBadMul).trans hacc)
    have hdiv : 2 ^ N * N ≤ 50 * (2 ^ N * N / 50) + 49 := by
      have := Nat.div_add_mod (2 ^ N * N) 50
      have := Nat.mod_lt (2 ^ N * N) (by norm_num : 0 < 50)
      omega
    have : 50 * (BadU.card * (2 * N)) ≤ 99 * (2 ^ N * N) + 49 := by omega
    have hbad100 : 200 * BadU.card * N ≤ 198 * 2 ^ N * N + 98 := by linarith
    have h2N : 2 ^ 50 ≤ 2 ^ N := Nat.pow_le_pow_right two_pos (by omega)
    have h98 : 98 ≤ 2 ^ N * N := by
      have : 100 ≤ 2 ^ 50 := by norm_num
      nlinarith
    have hbad200N : (200 * BadU.card) * N ≤ (199 * 2 ^ N) * N := by linarith
    have hbad200 : 200 * BadU.card ≤ 199 * 2 ^ N := Nat.le_of_mul_le_mul_right hbad200N hN
    omega
  set Ball := univ.filter (fun x : Fin N → Bool =>
    (univ.filter (fun i : Fin N => x i = true)).card ≤ r)
  have hcover : GoodU.card ≤ 2 ^ b * Ball.card := by
    have hsub : GoodU ⊆ univ.biUnion (fun m : Fin (2 ^ b) =>
        GoodU.filter (fun u => send u = m)) := by
      intro u hu; exact mem_biUnion.2 ⟨send u, mem_univ _, mem_filter.2 ⟨hu, rfl⟩⟩
    have hfiber : ∀ m : Fin (2 ^ b), (GoodU.filter (fun u => send u = m)).card ≤ Ball.card := by
      intro m
      refine card_le_card_of_injOn (errMap m) (fun u hu => ?_) (fun u1 _ u2 _ h => hbij m h)
      rw [mem_coe, mem_filter] at hu
      rw [mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hgu := (mem_filter.1 hu.1).2
      rwa [hu.2] at hgu
    calc GoodU.card ≤ ∑ m : Fin (2 ^ b), (GoodU.filter (fun u => send u = m)).card :=
          (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ _m : Fin (2 ^ b), Ball.card := sum_le_sum fun m _ => hfiber m
      _ = 2 ^ b * Ball.card := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  have hBall := hamming_ball_pow5 N r hr
  have hcomb : 2 ^ (5 * N) * 108 ^ N ≤ 200 ^ 5 * 2 ^ (5 * b) * 3125 ^ N := by
    have h1 : 2 ^ N ≤ 200 * 2 ^ b * Ball.card := by
      calc 2 ^ N ≤ 200 * GoodU.card := hGoodU
        _ ≤ 200 * (2 ^ b * Ball.card) := Nat.mul_le_mul_left 200 hcover
        _ = 200 * 2 ^ b * Ball.card := by ring
    have h5 := Nat.pow_le_pow_left h1 5
    rw [← pow_mul, mul_comm N 5, mul_pow, mul_pow, ← pow_mul, mul_comm b 5] at h5
    calc 2 ^ (5 * N) * 108 ^ N
        ≤ 200 ^ 5 * 2 ^ (5 * b) * Ball.card ^ 5 * 108 ^ N := Nat.mul_le_mul_right _ h5
      _ = 200 ^ 5 * 2 ^ (5 * b) * (Ball.card ^ 5 * 108 ^ N) := by ring
      _ ≤ 200 ^ 5 * 2 ^ (5 * b) * 3125 ^ N := Nat.mul_le_mul_left _ hBall
  have h3456 : 3456 ^ N ≤ 200 ^ 5 * 2 ^ (5 * b) * 3125 ^ N := by
    have : 2 ^ (5 * N) * 108 ^ N = 3456 ^ N := by
      rw [pow_mul, ← mul_pow]; norm_num
    rwa [← this]
  have hstep : 2 * 3125 ^ 8 ≤ 3456 ^ 8 := by norm_num
  by_contra hlt
  push_neg at hlt
  have hq : 8 * (5 * b + 40) ≤ N := by omega
  have hpow1 : 2 ^ (5 * b + 40) * 3125 ^ (8 * (5 * b + 40)) ≤ 3456 ^ (8 * (5 * b + 40)) := by
    calc 2 ^ (5 * b + 40) * 3125 ^ (8 * (5 * b + 40))
        = (2 * 3125 ^ 8) ^ (5 * b + 40) := by rw [mul_pow, ← pow_mul]
      _ ≤ (3456 ^ 8) ^ (5 * b + 40) := Nat.pow_le_pow_left hstep _
      _ = 3456 ^ (8 * (5 * b + 40)) := by rw [← pow_mul]
  have hpow2 : 3125 ^ (N - 8 * (5 * b + 40)) ≤ 3456 ^ (N - 8 * (5 * b + 40)) :=
    Nat.pow_le_pow_left (by norm_num) _
  have hbig : 2 ^ (5 * b + 40) * 3125 ^ N ≤ 3456 ^ N := by
    calc 2 ^ (5 * b + 40) * 3125 ^ N
        = (2 ^ (5 * b + 40) * 3125 ^ (8 * (5 * b + 40))) * 3125 ^ (N - 8 * (5 * b + 40)) := by
          rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hq]
      _ ≤ 3456 ^ (8 * (5 * b + 40)) * 3456 ^ (N - 8 * (5 * b + 40)) :=
          Nat.mul_le_mul hpow1 hpow2
      _ = 3456 ^ N := by rw [← pow_add, Nat.add_sub_of_le hq]
  have hstrict : 200 ^ 5 * 2 ^ (5 * b) < 2 ^ (5 * b + 40) := by
    rw [pow_add, mul_comm (2 ^ (5 * b)) (2 ^ 40)]
    have : 200 ^ 5 < 2 ^ 40 := by norm_num
    exact Nat.mul_lt_mul_of_pos_right this (Nat.pow_pos two_pos)
  have hstrict2 : 200 ^ 5 * 2 ^ (5 * b) * 3125 ^ N < 2 ^ (5 * b + 40) * 3125 ^ N :=
    Nat.mul_lt_mul_of_pos_right hstrict (Nat.pow_pos (by norm_num))
  omega

lemma index_lb {N b R : ℕ} (hN : 0 < N) (hR : 0 < R)
    (send : Fin R → (Fin N → Bool) → Fin (2 ^ b))
    (recv : Fin R → Fin (2 ^ b) → Fin N → Bool)
    (hgood : ∀ (u : Fin N → Bool) (i : Fin N),
      19 * R ≤ 30 * (univ.filter (fun s : Fin R => recv s (send s u) i = u i)).card) :
    N ≤ 50 * b + 500 := by
  classical
  have hbad_pt : ∀ (u : Fin N → Bool) (i : Fin N),
      30 * (univ.filter (fun s : Fin R => recv s (send s u) i ≠ u i)).card ≤ 11 * R := by
    intro u i
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin R)))
      (fun s => recv s (send s u) i = u i)
    rw [card_univ, Fintype.card_fin] at hsum
    have hneq : (univ.filter (fun s : Fin R => ¬ recv s (send s u) i = u i)).card =
        (univ.filter (fun s : Fin R => recv s (send s u) i ≠ u i)).card := rfl
    rw [hneq] at hsum
    have := hgood u i
    omega
  have htot : 30 * ∑ s : Fin R, (univ.filter (fun p : (Fin N → Bool) × Fin N =>
      recv s (send s p.1) p.2 ≠ p.1 p.2)).card ≤ 11 * R * (2 ^ N * N) := by
    have hswap : ∑ s : Fin R, (univ.filter (fun p : (Fin N → Bool) × Fin N =>
        recv s (send s p.1) p.2 ≠ p.1 p.2)).card =
        ∑ p : (Fin N → Bool) × Fin N, (univ.filter (fun s : Fin R =>
          recv s (send s p.1) p.2 ≠ p.1 p.2)).card := by
      simp only [card_filter]; exact sum_comm
    rw [hswap, mul_sum]
    calc ∑ p : (Fin N → Bool) × Fin N,
            30 * (univ.filter (fun s : Fin R => recv s (send s p.1) p.2 ≠ p.1 p.2)).card
        ≤ ∑ _p : (Fin N → Bool) × Fin N, (11 * R) := sum_le_sum fun p _ => hbad_pt p.1 p.2
      _ = (2 ^ N * N) * (11 * R) := by
          rw [sum_const, smul_eq_mul, card_univ, Fintype.card_prod, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin]
      _ = 11 * R * (2 ^ N * N) := by ring
  have hex : ∃ s : Fin R, 30 * (univ.filter (fun p : (Fin N → Bool) × Fin N =>
      recv s (send s p.1) p.2 ≠ p.1 p.2)).card ≤ 11 * (2 ^ N * N) := by
    by_contra hall
    push_neg at hall
    have hsum_gt : R * (11 * (2 ^ N * N)) < ∑ s : Fin R,
        30 * (univ.filter (fun p : (Fin N → Bool) × Fin N =>
          recv s (send s p.1) p.2 ≠ p.1 p.2)).card := by
      calc R * (11 * (2 ^ N * N)) = ∑ _s : Fin R, (11 * (2 ^ N * N)) := by
            rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        _ < ∑ s : Fin R, 30 * (univ.filter (fun p : (Fin N → Bool) × Fin N =>
              recv s (send s p.1) p.2 ≠ p.1 p.2)).card :=
            sum_lt_sum_of_nonempty (univ_nonempty_iff.2 ⟨⟨0, hR⟩⟩) fun s _ => hall s
    rw [← mul_sum] at hsum_gt
    linarith
  obtain ⟨s, hs⟩ := hex
  refine lb_from_bijective_decoder hN (send s) (fun m u i => decide (recv s m i ≠ u i)) ?_ ?_
  · intro m u1 u2 h
    funext i
    have hi := congrFun h i
    cases h1 : u1 i <;> cases h2 : u2 i <;> cases hr : recv s m i <;> simp_all
  · have heq : (univ.filter (fun p : (Fin N → Bool) × Fin N =>
        decide (recv s (send s p.1) p.2 ≠ p.1 p.2) = true)).card =
        (univ.filter (fun p : (Fin N → Bool) × Fin N =>
          recv s (send s p.1) p.2 ≠ p.1 p.2)).card := by
      simp only [decide_eq_true_eq]
    rw [heq]
    omega

def bitsToNat {d : ℕ} (x : Fin d → Bool) : ℕ :=
  ∑ i : Fin d, if x i = true then 2 ^ (d - 1 - i.val) else 0

lemma bitsToNat_lt {d : ℕ} (x : Fin d → Bool) : bitsToNat x < 2 ^ d := by
  induction d with
  | zero => simp [bitsToNat]
  | succ d ih =>
    unfold bitsToNat
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ]
    have hsub : ∀ j : Fin d, d - (j.val + 1) = d - 1 - j.val := fun j => by omega
    simp only [hsub]
    have htail : bitsToNat (fun i : Fin d => x i.succ) < 2 ^ d := ih _
    unfold bitsToNat at htail
    dsimp only at htail
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [pow_succ]; ring
    split_ifs <;> omega

lemma gt_probe_iff {d : ℕ} (x : Fin d → Bool) (i : Fin d) :
    let y : Fin d → Bool := fun j => if j.val < i.val then x j else if j = i then false else true
    (bitsToNat y < bitsToNat x) ↔ x i = true := by
  intro y
  have hsplit : ∀ (z : Fin d → Bool),
      bitsToNat z =
        (∑ j ∈ univ.filter (fun j : Fin d => j.val < i.val),
          if z j = true then 2 ^ (d - 1 - j.val) else 0) +
        (if z i = true then 2 ^ (d - 1 - i.val) else 0) +
        (∑ j ∈ univ.filter (fun j : Fin d => i.val < j.val),
          if z j = true then 2 ^ (d - 1 - j.val) else 0) := by
    intro z
    unfold bitsToNat
    rw [← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val < i.val)]
    have hrest : univ.filter (fun j : Fin d => ¬ j.val < i.val) =
        insert i (univ.filter (fun j : Fin d => i.val < j.val)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.ext_iff]
      omega
    rw [hrest, sum_insert (by simp), add_assoc]
  have hpre : (∑ j ∈ univ.filter (fun j : Fin d => j.val < i.val),
      if y j = true then 2 ^ (d - 1 - j.val) else 0) =
      (∑ j ∈ univ.filter (fun j : Fin d => j.val < i.val),
      if x j = true then 2 ^ (d - 1 - j.val) else 0) :=
    sum_congr rfl fun j hj => by
      have hyj : y j = x j := by dsimp only [y]; rw [if_pos (mem_filter.1 hj).2]
      rw [hyj]
  have htail_y : (∑ j ∈ univ.filter (fun j : Fin d => i.val < j.val),
      if y j = true then 2 ^ (d - 1 - j.val) else 0) = 2 ^ (d - 1 - i.val) - 1 := by
    have hy1 : ∀ j ∈ univ.filter (fun j : Fin d => i.val < j.val),
        (if y j = true then 2 ^ (d - 1 - j.val) else 0) = 2 ^ (d - 1 - j.val) := by
      intro j hj
      have hij : i.val < j.val := (mem_filter.1 hj).2
      have hne : j ≠ i := fun h => by subst h; omega
      have hnot : ¬ j.val < i.val := by omega
      have hyj : y j = true := by dsimp only [y]; rw [if_neg hnot, if_neg hne]
      rw [hyj]; simp
    rw [sum_congr rfl hy1]
    have hbij : ∑ j ∈ univ.filter (fun j : Fin d => i.val < j.val), 2 ^ (d - 1 - j.val) =
        ∑ k ∈ range (d - 1 - i.val), 2 ^ k := by
      have hi := i.isLt
      refine sum_bij (fun j _ => d - 1 - j.val) ?_ ?_ ?_ ?_
      · intro j hj; rw [mem_range]; have := (mem_filter.1 hj).2; have := j.isLt; omega
      · intro j1 h1 j2 h2 heq
        have := j1.isLt; have := j2.isLt; exact Fin.ext (by omega)
      · intro k hk
        rw [mem_range] at hk
        refine ⟨⟨d - 1 - k, by omega⟩, mem_filter.2 ⟨mem_univ _, show i.val < d - 1 - k by omega⟩, by show d - 1 - (d - 1 - k) = k; omega⟩
      · intro _ _; rfl
    rw [hbij]
    have hgeom : ∀ m : ℕ, ∑ k ∈ range m, 2 ^ k = 2 ^ m - 1 := by
      intro m; induction m with
      | zero => simp
      | succ m ih =>
        rw [sum_range_succ, ih, pow_succ]
        have : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ two_pos
        omega
    exact hgeom (d - 1 - i.val)
  have htail_x : (∑ j ∈ univ.filter (fun j : Fin d => i.val < j.val),
      if x j = true then 2 ^ (d - 1 - j.val) else 0) ≤ 2 ^ (d - 1 - i.val) - 1 := by
    rw [← htail_y]
    refine sum_le_sum fun j hj => ?_
    have hij : i.val < j.val := (mem_filter.1 hj).2
    have hne : j ≠ i := fun h => by subst h; omega
    have hnot : ¬ j.val < i.val := by omega
    have hyj : y j = true := by dsimp only [y]; rw [if_neg hnot, if_neg hne]
    rw [hyj]; simp only [↓reduceIte]
    split_ifs
    · exact le_rfl
    · exact Nat.zero_le _
  have hyi : y i = false := by simp [y]
  rw [hsplit y, hsplit x, hpre, htail_y, hyi]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  have hpos : 1 ≤ 2 ^ (d - 1 - i.val) := Nat.one_le_pow _ _ two_pos
  cases hxi : x i
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, iff_false, not_lt]; omega
  · simp only [↓reduceIte, iff_true]; omega

lemma gt_lb {d b R : ℕ} (hd : 0 < d) (hR : 0 < R)
    (send : Fin R → Fin (2 ^ d) → Fin (2 ^ b))
    (recv : Fin R → Fin (2 ^ b) → Fin (2 ^ d) → Bool)
    (hgood : ∀ (X Y : Fin (2 ^ d)),
      2 * R ≤ 3 * (univ.filter (fun s : Fin R =>
        (Y.val < X.val → recv s (send s X) Y = true) ∧
        (X.val ≤ Y.val → recv s (send s X) Y = false))).card) :
    d ≤ 50 * b + 500 := by
  classical
  let probe : (Fin d → Bool) → Fin d → Fin (2 ^ d) := fun x i =>
    ⟨bitsToNat (fun j => if j.val < i.val then x j else if j = i then false else true),
      bitsToNat_lt _⟩
  let toNum : (Fin d → Bool) → Fin (2 ^ d) := fun x => ⟨bitsToNat x, bitsToNat_lt x⟩
  have hbad_pt : ∀ (x : Fin d → Bool) (i : Fin d),
      3 * (univ.filter (fun s : Fin R =>
        recv s (send s (toNum x)) (probe x i) ≠ x i)).card ≤ R := by
    intro x i
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin R)))
      (fun s => recv s (send s (toNum x)) (probe x i) = x i)
    rw [card_univ, Fintype.card_fin] at hsum
    have hle : (univ.filter (fun s : Fin R =>
        ((probe x i).val < (toNum x).val → recv s (send s (toNum x)) (probe x i) = true) ∧
        ((toNum x).val ≤ (probe x i).val → recv s (send s (toNum x)) (probe x i) = false))).card ≤
        (univ.filter (fun s : Fin R =>
          recv s (send s (toNum x)) (probe x i) = x i)).card := by
      refine card_le_card fun s hs => ?_
      have ⟨h1, h2⟩ := (mem_filter.1 hs).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      have hiff := gt_probe_iff x i
      cases hxi : x i
      · exact h2 (le_of_not_gt fun hlt => by have := hiff.1 hlt; rw [hxi] at this; exact Bool.noConfusion this)
      · exact h1 (hiff.2 hxi)
    have hneq : (univ.filter (fun s : Fin R => ¬ recv s (send s (toNum x)) (probe x i) = x i)).card =
        (univ.filter (fun s : Fin R => recv s (send s (toNum x)) (probe x i) ≠ x i)).card := rfl
    rw [hneq] at hsum
    have := hgood (toNum x) (probe x i)
    omega
  have htot : 3 * ∑ s : Fin R, (univ.filter (fun p : (Fin d → Bool) × Fin d =>
      recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card ≤ R * (2 ^ d * d) := by
    have hswap : ∑ s : Fin R, (univ.filter (fun p : (Fin d → Bool) × Fin d =>
        recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card =
        ∑ p : (Fin d → Bool) × Fin d, (univ.filter (fun s : Fin R =>
          recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card := by
      simp only [card_filter]; exact sum_comm
    rw [hswap, mul_sum]
    calc ∑ p : (Fin d → Bool) × Fin d,
            3 * (univ.filter (fun s : Fin R =>
              recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card
        ≤ ∑ _p : (Fin d → Bool) × Fin d, R := sum_le_sum fun p _ => hbad_pt p.1 p.2
      _ = (2 ^ d * d) * R := by
          rw [sum_const, smul_eq_mul, card_univ, Fintype.card_prod, Fintype.card_fun,
            Fintype.card_bool, Fintype.card_fin]
      _ = R * (2 ^ d * d) := by ring
  have hex : ∃ s : Fin R, 3 * (univ.filter (fun p : (Fin d → Bool) × Fin d =>
      recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card ≤ 2 ^ d * d := by
    by_contra hall
    push_neg at hall
    have hsum_gt : R * (2 ^ d * d) < ∑ s : Fin R,
        3 * (univ.filter (fun p : (Fin d → Bool) × Fin d =>
          recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card := by
      calc R * (2 ^ d * d) = ∑ _s : Fin R, (2 ^ d * d) := by
            rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
        _ < ∑ s : Fin R, 3 * (univ.filter (fun p : (Fin d → Bool) × Fin d =>
              recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card :=
            sum_lt_sum_of_nonempty (univ_nonempty_iff.2 ⟨⟨0, hR⟩⟩) fun s _ => hall s
    rw [← mul_sum] at hsum_gt
    linarith
  obtain ⟨s, hs⟩ := hex
  refine lb_from_bijective_decoder hd (fun x => send s (toNum x))
    (fun m x i => decide (recv s m (probe x i) ≠ x i)) ?_ ?_
  · intro m x1 x2 heq
    funext i
    induction hi : i.val using Nat.strong_induction_on generalizing i with
    | ind k ih =>
      have hprobe : probe x1 i = probe x2 i := by
        dsimp only [probe]
        congr 1; congr 1; funext j
        split_ifs with hlt
        · exact ih j.val (by omega) j rfl
        · rfl
        · rfl
      have hi_eq := congrFun heq i
      dsimp only at hi_eq
      rw [hprobe] at hi_eq
      cases h1 : x1 i <;> cases h2 : x2 i <;> cases hr : recv s m (probe x2 i) <;> simp_all
  · have heq : (univ.filter (fun p : (Fin d → Bool) × Fin d =>
        decide (recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2) = true)).card =
        (univ.filter (fun p : (Fin d → Bool) × Fin d =>
          recv s (send s (toNum p.1)) (probe p.1 p.2) ≠ p.1 p.2)).card := by
      simp only [decide_eq_true_eq]
    rw [heq]
    omega

end HammingBall

section Pinning

def bSign (b : Bool) : ℤ := if b = true then 1 else -1

lemma bSign_mul_self (b : Bool) : bSign b * bSign b = 1 := by cases b <;> decide

lemma bSign_not (b : Bool) : bSign (!b) = - bSign b := by cases b <;> decide

lemma bSign_eq_iff (b1 b2 : Bool) :
    bSign b1 * bSign b2 = if b1 = b2 then 1 else -1 := by cases b1 <;> cases b2 <;> decide

lemma sum_four_signs_zero {n : ℕ} (i j k l : Fin n) (u : Fin n)
    (hu : (u = i ∧ u ≠ j ∧ u ≠ k ∧ u ≠ l) ∨
          (u ≠ i ∧ u = j ∧ u ≠ k ∧ u ≠ l)) :
    ∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ j) * bSign (σ k) * bSign (σ l) = 0 := by
  classical
  let flip : (Fin n → Bool) → (Fin n → Bool) := fun σ => Function.update σ u (!(σ u))
  have hinv : Function.Involutive flip := by
    intro σ; funext v
    by_cases hv : v = u
    · subst hv; simp [flip]
    · simp [flip, hv]
  have hneg : ∀ σ : Fin n → Bool,
      bSign (flip σ i) * bSign (flip σ j) * bSign (flip σ k) * bSign (flip σ l) =
      -(bSign (σ i) * bSign (σ j) * bSign (σ k) * bSign (σ l)) := by
    intro σ
    rcases hu with ⟨rfl, h2, h3, h4⟩ | ⟨h1, rfl, h3, h4⟩
    · simp only [flip, Function.update_self, Function.update_of_ne h2.symm,
        Function.update_of_ne h3.symm, Function.update_of_ne h4.symm, bSign_not]
      ring
    · simp only [flip, Function.update_self, Function.update_of_ne h1.symm,
        Function.update_of_ne h3.symm, Function.update_of_ne h4.symm, bSign_not]
      ring
  have hsum : ∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ j) * bSign (σ k) * bSign (σ l) =
      ∑ σ : Fin n → Bool,
        bSign (flip σ i) * bSign (flip σ j) * bSign (flip σ k) * bSign (flip σ l) := by
    refine sum_bij (fun σ _ => flip σ) (fun _ _ => mem_univ _)
      (fun _ _ _ _ h => hinv.injective h) (fun σ _ => ⟨flip σ, mem_univ _, hinv σ⟩) (fun σ _ => by simp only [hinv σ])
  have hsum2 : ∑ σ : Fin n → Bool,
      bSign (flip σ i) * bSign (flip σ j) * bSign (flip σ k) * bSign (flip σ l) =
      -(∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ j) * bSign (σ k) * bSign (σ l)) := by
    simp only [hneg, sum_neg_distrib]
  linarith

lemma second_moment_perm {n : ℕ} (π : Equiv.Perm (Fin n)) (G : Finset (Fin n))
    (hnoFix : ∀ i ∈ G, π i ≠ i) (ε : Fin n → ℤ) (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∑ σ : Fin n → Bool, (∑ i ∈ G, ε i * (bSign (σ i) * bSign (σ (π i)))) ^ 2 ≤
      2 * (G.card : ℤ) * 2 ^ n := by
  classical
  have hexp : ∑ σ : Fin n → Bool, (∑ i ∈ G, ε i * (bSign (σ i) * bSign (σ (π i)))) ^ 2 =
      ∑ i ∈ G, ∑ k ∈ G, (ε i * ε k) *
        ∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)) := by
    simp only [sq, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    refine sum_congr rfl fun σ _ => by ring
  rw [hexp]
  have hinner : ∀ i ∈ G, ∑ k ∈ G, (ε i * ε k) *
      ∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)) ≤
      2 * (2 : ℤ) ^ n := by
    intro i hi
    have hterm_zero : ∀ k ∈ G, k ≠ i → k ≠ π i →
        (ε i * ε k) * ∑ σ : Fin n → Bool,
          bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)) = 0 := by
      intro k hk hki hkpi
      have hne1 : π i ≠ i := hnoFix i hi
      by_cases h1 : i ≠ π k
      · rw [sum_four_signs_zero i (π i) k (π k) i (Or.inl ⟨rfl, hne1.symm, hki.symm, h1⟩), mul_zero]
      · push_neg at h1
        have h2 : π i ≠ π k := fun h => hne1 (h.trans h1.symm)
        rw [sum_four_signs_zero i (π i) k (π k) (π i) (Or.inr ⟨hne1, rfl, hkpi.symm, h2⟩), mul_zero]
    have hterm_le : ∀ k : Fin n,
        (ε i * ε k) * ∑ σ : Fin n → Bool,
          bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)) ≤ (2 : ℤ) ^ n := by
      intro k
      have habs : ∀ σ : Fin n → Bool,
          (ε i * ε k) * (bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k))) ≤ 1 := by
        intro σ
        rcases hε i with h1 | h1 <;> rcases hε k with h2 | h2 <;>
          cases σ i <;> cases σ (π i) <;> cases σ k <;> cases σ (π k) <;>
          simp [h1, h2, bSign]
      rw [mul_sum]
      calc ∑ σ : Fin n → Bool,
              (ε i * ε k) * (bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)))
          ≤ ∑ _σ : Fin n → Bool, (1 : ℤ) := sum_le_sum fun σ _ => habs σ
        _ = (2 : ℤ) ^ n := by
            rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
            simp
    have hsub : ∑ k ∈ G, (ε i * ε k) *
        ∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)) =
        ∑ k ∈ G ∩ ({i, π i} : Finset (Fin n)), (ε i * ε k) *
          ∑ σ : Fin n → Bool, bSign (σ i) * bSign (σ (π i)) * bSign (σ k) * bSign (σ (π k)) := by
      refine (sum_subset inter_subset_left fun k hkG hkNot => ?_).symm
      have hk2 : k ∉ ({i, π i} : Finset (Fin n)) := fun h => hkNot (mem_inter.2 ⟨hkG, h⟩)
      simp only [mem_insert, mem_singleton, not_or] at hk2
      exact hterm_zero k hkG hk2.1 hk2.2
    rw [hsub]
    calc ∑ k ∈ G ∩ ({i, π i} : Finset (Fin n)), _
        ≤ ∑ _k ∈ G ∩ ({i, π i} : Finset (Fin n)), (2 : ℤ) ^ n := sum_le_sum fun k _ => hterm_le k
      _ = ((G ∩ ({i, π i} : Finset (Fin n))).card : ℤ) * (2 : ℤ) ^ n := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * (2 : ℤ) ^ n := by
          have hc : (G ∩ ({i, π i} : Finset (Fin n))).card ≤ 2 :=
            (card_le_card inter_subset_right).trans (card_le_two)
          have hcz : ((G ∩ ({i, π i} : Finset (Fin n))).card : ℤ) ≤ 2 := by exact_mod_cast hc
          exact mul_le_mul_of_nonneg_right hcz (by positivity)
  calc ∑ i ∈ G, ∑ k ∈ G, _
      ≤ ∑ _i ∈ G, (2 * (2 : ℤ) ^ n) := sum_le_sum hinner
    _ = 2 * (G.card : ℤ) * 2 ^ n := by rw [sum_const, nsmul_eq_mul]; ring

lemma pinning_lemma {n r g : ℕ} (hr : 0 < r) (hnr : 8192 * r < n) (hg : 128 * g ≤ n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hov : ∀ j l : Fin r, j ≠ l →
      128 * (univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (j0 : Fin r) (R0 : Finset (Fin n)) (hR0 : 256 * R0.card ≤ n)
    (target : ℕ) (htarget : target ≤ n - R0.card) :
    ∃ x0 : Bool × Fin n → Bool,
      ((univ \ R0).filter (fun i : Fin n => x0 (false, i) ≠ x0 (true, M j0 i))).card = target ∧
      ∀ (l : Fin r), l ≠ j0 → ∀ x : Bool × Fin n → Bool,
        (∀ i : Fin n, i ∉ R0 → x (false, i) = x0 (false, i) ∧ x (true, M j0 i) = x0 (true, M j0 i)) →
        let Dl := (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M l i))).card
        15 * n + 32 * g ≤ 32 * Dl ∧ 32 * Dl + 32 * g ≤ 17 * n := by
  classical
  have hUcard : (univ \ R0).card = n - R0.card := by
    rw [card_sdiff, inter_univ, card_univ, Fintype.card_fin]
  obtain ⟨Etar, hEsub, hEcard⟩ := exists_subset_card_eq (hUcard ▸ htarget)
  let ε : Fin n → ℤ := fun i => if i ∈ Etar then -1 else 1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by dsimp only [ε]; split_ifs <;> simp
  let mkX : (Fin n → Bool) → (Bool × Fin n → Bool) := fun σ v =>
    if v.1 = false then σ v.2
    else
      let i := (M j0).symm v.2
      if i ∈ Etar then !(σ i) else σ i
  have hmkX_false : ∀ σ i, mkX σ (false, i) = σ i := fun σ i => by simp [mkX]
  have hmkX_true : ∀ σ i, mkX σ (true, M j0 i) = if i ∈ Etar then !(σ i) else σ i := fun σ i => by
    simp [mkX]
  have hmkX_tar : ∀ σ,
      ((univ \ R0).filter (fun i : Fin n => mkX σ (false, i) ≠ mkX σ (true, M j0 i))).card = target := by
    intro σ
    have heq : (univ \ R0).filter (fun i : Fin n => mkX σ (false, i) ≠ mkX σ (true, M j0 i)) = Etar := by
      ext i
      simp only [mem_filter, hmkX_false, hmkX_true]
      by_cases hi : i ∈ Etar
      · simp [hi, hEsub hi]
      · simp [hi]
    rw [heq, hEcard]
  let BadL : Fin r → Finset (Fin n) := fun l =>
    univ.filter (fun i : Fin n => i ∈ R0 ∨ (M j0).symm (M l i) ∈ R0 ∨ M l i = M j0 i)
  let GoodL : Fin r → Finset (Fin n) := fun l => univ \ BadL l
  have hBadL_card : ∀ l : Fin r, l ≠ j0 → 64 * (BadL l).card ≤ n := by
    intro l hlj
    set π := (M l).trans (M j0).symm
    have hsub : BadL l ⊆ R0 ∪ (univ.filter (fun i => π i ∈ R0) ∪
        univ.filter (fun i => M j0 i = M l i)) := by
      intro i hi
      simp only [BadL, mem_filter, mem_univ, true_and] at hi
      simp only [mem_union, mem_filter, mem_univ, true_and]
      rcases hi with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (Or.inl (by simpa [π] using h2))
      · exact Or.inr (Or.inr h3.symm)
    have hc2 : (univ.filter (fun i : Fin n => π i ∈ R0)).card = R0.card := by
      refine card_bij (fun i _ => π i) (fun _ hi => (mem_filter.1 hi).2)
        (fun _ _ _ _ h => π.injective h)
        (fun j hj => ⟨π.symm j, mem_filter.2 ⟨mem_univ _, by simpa⟩, by simp⟩)
    have hle : (BadL l).card ≤ R0.card + R0.card + (univ.filter (fun i : Fin n => M j0 i = M l i)).card := by
      calc (BadL l).card ≤ R0.card + (univ.filter (fun i => π i ∈ R0) ∪
              univ.filter (fun i => M j0 i = M l i)).card :=
            (card_le_card hsub).trans (card_union_le _ _)
        _ ≤ R0.card + ((univ.filter (fun i => π i ∈ R0)).card +
              (univ.filter (fun i => M j0 i = M l i)).card) :=
            Nat.add_le_add_left (card_union_le _ _) _
        _ = R0.card + R0.card + (univ.filter (fun i : Fin n => M j0 i = M l i)).card := by
            rw [hc2]; ring
    have hovl := hov j0 l hlj.symm
    omega
  let Y : Fin r → (Fin n → Bool) → ℤ := fun l σ =>
    let π := (M l).trans (M j0).symm
    ∑ i ∈ GoodL l, ε (π i) * (bSign (σ i) * bSign (σ (π i)))
  let Fail : Fin r → Finset (Fin n → Bool) := fun l =>
    univ.filter (fun σ : Fin n → Bool => (n : ℤ) ^ 2 ≤ (32 * Y l σ) ^ 2)
  have hFail : ∀ l : Fin r, l ≠ j0 → (Fail l).card * n ≤ 2048 * 2 ^ n := by
    intro l hlj
    let π := (M l).trans (M j0).symm
    have hnoFix : ∀ i ∈ GoodL l, π i ≠ i := by
      intro i hi hfix
      have hnb := (mem_sdiff.1 hi).2
      apply hnb
      refine mem_filter.2 ⟨mem_univ _, Or.inr (Or.inr ?_)⟩
      have := congrArg (M j0) hfix
      simpa [π] using this
    have hmom := second_moment_perm π (GoodL l) hnoFix (fun i => ε (π i)) (fun i => hε (π i))
    have hGcard : (GoodL l).card ≤ n := (card_le_univ _).trans (by simp)
    have hmk : ((Fail l).card : ℤ) * (n : ℤ) ^ 2 ≤ 1024 * (2 * (n : ℤ) * 2 ^ n) := by
      calc ((Fail l).card : ℤ) * (n : ℤ) ^ 2 = (Fail l).card • ((n : ℤ) ^ 2) := by
            rw [nsmul_eq_mul]
        _ ≤ ∑ σ ∈ Fail l, (32 * Y l σ) ^ 2 :=
            card_nsmul_le_sum _ _ _ (fun σ hσ => (mem_filter.1 hσ).2)
        _ ≤ ∑ σ : Fin n → Bool, (32 * Y l σ) ^ 2 :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
        _ = 1024 * ∑ σ : Fin n → Bool, (Y l σ) ^ 2 := by
            rw [mul_sum]; refine sum_congr rfl fun _ _ => by ring
        _ ≤ 1024 * (2 * ((GoodL l).card : ℤ) * 2 ^ n) :=
            mul_le_mul_of_nonneg_left hmom (by norm_num)
        _ ≤ 1024 * (2 * (n : ℤ) * 2 ^ n) := by
            have hGz : ((GoodL l).card : ℤ) ≤ n := by exact_mod_cast hGcard
            have h2pos : (0 : ℤ) ≤ 2 ^ n := by positivity
            nlinarith
    have hnpos : (0 : ℤ) < n := by omega
    have hmul : ((Fail l).card : ℤ) * n * n ≤ (2048 * 2 ^ n) * n := by linarith
    have := le_of_mul_le_mul_right hmul hnpos
    exact_mod_cast this
  have hsumFail : ((univ.erase j0).biUnion Fail).card < 2 ^ n := by
    have h1 : ((univ.erase j0).biUnion Fail).card * n ≤ r * (2048 * 2 ^ n) := by
      calc ((univ.erase j0).biUnion Fail).card * n
          ≤ (∑ l ∈ univ.erase j0, (Fail l).card) * n := Nat.mul_le_mul_right n card_biUnion_le
        _ = ∑ l ∈ univ.erase j0, (Fail l).card * n := sum_mul _ _ _
        _ ≤ ∑ _l ∈ univ.erase j0, (2048 * 2 ^ n) :=
            sum_le_sum fun l hl => hFail l (ne_of_mem_erase hl)
        _ = (univ.erase j0).card * (2048 * 2 ^ n) := by rw [sum_const, smul_eq_mul]
        _ ≤ r * (2048 * 2 ^ n) := Nat.mul_le_mul_right _
            ((card_le_univ _).trans (by simp))
    have hlt : ((univ.erase j0).biUnion Fail).card * n < 2 ^ n * n := by
      have : r * (2048 * 2 ^ n) < 2 ^ n * n := by
        have h2pos : 0 < 2 ^ n := Nat.pow_pos two_pos
        nlinarith
      exact lt_of_le_of_lt h1 this
    exact Nat.lt_of_mul_lt_mul_right hlt
  have hex : ∃ σ : Fin n → Bool, σ ∉ (univ.erase j0).biUnion Fail := by
    by_contra hall
    push_neg at hall
    have : 2 ^ n ≤ ((univ.erase j0).biUnion Fail).card := by
      calc 2 ^ n = (univ : Finset (Fin n → Bool)).card := by
            rw [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
        _ ≤ ((univ.erase j0).biUnion Fail).card := card_le_card fun σ _ => hall σ
    omega
  obtain ⟨σ, hσ⟩ := hex
  refine ⟨mkX σ, hmkX_tar σ, fun l hlj x hx => ?_⟩
  have hσ_ok : ¬ ((n : ℤ) ^ 2 ≤ (32 * Y l σ) ^ 2) := by
    intro hbad
    exact hσ (mem_biUnion.2 ⟨l, mem_erase.2 ⟨hlj, mem_univ _⟩, mem_filter.2 ⟨mem_univ _, hbad⟩⟩)
  have hYabs := abs_lt.1 (abs_lt_of_sq_lt_sq (not_le.1 hσ_ok) (by omega))
  set Dl := (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M l i))).card
  have hD_sign : (n : ℤ) - 2 * Dl =
      ∑ i : Fin n, bSign (x (false, i)) * bSign (x (true, M l i)) := by
    have hterm : ∀ i : Fin n,
        bSign (x (false, i)) * bSign (x (true, M l i)) =
        1 - 2 * (if x (false, i) ≠ x (true, M l i) then (1 : ℤ) else 0) := by
      intro i; cases x (false, i) <;> cases x (true, M l i) <;> decide
    simp only [hterm, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, ← mul_sum, sum_boole]
    rfl
  have hgood_eq : ∀ i ∈ GoodL l,
      bSign (x (false, i)) * bSign (x (true, M l i)) =
      ε ((M j0).symm (M l i)) * (bSign (σ i) * bSign (σ ((M j0).symm (M l i)))) := by
    intro i hi
    have hnb := (mem_sdiff.1 hi).2
    simp only [BadL, mem_filter, mem_univ, true_and, not_or] at hnb
    have h1 := (hx i hnb.1).1
    have h2 := (hx ((M j0).symm (M l i)) hnb.2.1).2
    simp only [Equiv.apply_symm_apply] at h2
    rw [h1, h2, hmkX_false]
    have h3 := hmkX_true σ ((M j0).symm (M l i))
    simp only [Equiv.apply_symm_apply] at h3
    rw [h3]
    dsimp only [ε]
    split_ifs <;> simp [bSign_not] <;> ring
  have hsplit : ∑ i : Fin n, bSign (x (false, i)) * bSign (x (true, M l i)) =
      Y l σ + ∑ i ∈ BadL l, bSign (x (false, i)) * bSign (x (true, M l i)) := by
    rw [← sum_sdiff (subset_univ (BadL l))]
    congr 1
    exact sum_congr rfl fun i hi => hgood_eq i hi
  have hbad_ub : ∑ i ∈ BadL l, bSign (x (false, i)) * bSign (x (true, M l i)) ≤ (BadL l).card := by
    calc ∑ i ∈ BadL l, bSign (x (false, i)) * bSign (x (true, M l i))
        ≤ ∑ _i ∈ BadL l, (1 : ℤ) := sum_le_sum fun i _ => by
          cases x (false, i) <;> cases x (true, M l i) <;> decide
      _ = (BadL l).card := by simp
  have hbad_lb : -((BadL l).card : ℤ) ≤ ∑ i ∈ BadL l, bSign (x (false, i)) * bSign (x (true, M l i)) := by
    calc -((BadL l).card : ℤ) = ∑ _i ∈ BadL l, (-1 : ℤ) := by simp
      _ ≤ ∑ i ∈ BadL l, bSign (x (false, i)) * bSign (x (true, M l i)) := sum_le_sum fun i _ => by
          cases x (false, i) <;> cases x (true, M l i) <;> decide
  have hB64 := hBadL_card l hlj
  zify at hB64 hg ⊢
  constructor <;> linarith

end Pinning

section SplitPairLB

lemma choose_mid_sq (k : ℕ) : 4 ^ (2 * k) ≤ (4 * k + 1) * (Nat.choose (2 * k) k) ^ 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hrec : (k + 1) * Nat.choose (2 * (k + 1)) (k + 1) =
        2 * (2 * k + 1) * Nat.choose (2 * k) k := by
      have h1 : (k + 1) * Nat.choose (2 * k + 2) (k + 1) =
          (2 * k + 2) * Nat.choose (2 * k + 1) k := by
        have := Nat.add_one_mul_choose_eq (2 * k + 1) k
        linarith
      have h2 : Nat.choose (2 * k + 1) k * (k + 1) =
          (2 * k + 1) * Nat.choose (2 * k) k := by
        have hsym := Nat.choose_symm (show k ≤ 2 * k + 1 by omega)
        have hsub : 2 * k + 1 - k = k + 1 := by omega
        rw [hsub] at hsym
        have h3 := Nat.add_one_mul_choose_eq (2 * k) k
        rw [hsym] at h3
        linarith
      have hmul : (k + 1) * ((k + 1) * Nat.choose (2 * k + 2) (k + 1)) =
          (k + 1) * (2 * (2 * k + 1) * Nat.choose (2 * k) k) := by
        calc (k + 1) * ((k + 1) * Nat.choose (2 * k + 2) (k + 1))
            = (k + 1) * ((2 * k + 2) * Nat.choose (2 * k + 1) k) := by rw [h1]
          _ = 2 * (k + 1) * (Nat.choose (2 * k + 1) k * (k + 1)) := by ring
          _ = 2 * (k + 1) * ((2 * k + 1) * Nat.choose (2 * k) k) := by rw [h2]
          _ = (k + 1) * (2 * (2 * k + 1) * Nat.choose (2 * k) k) := by ring
      exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hmul
    have hpoly : 4 * (4 * k + 1) * (k + 1) ^ 2 ≤ (4 * (k + 1) + 1) * (2 * k + 1) ^ 2 := by
      nlinarith
    have hsq : ((k + 1) * Nat.choose (2 * (k + 1)) (k + 1)) ^ 2 =
        (2 * (2 * k + 1) * Nat.choose (2 * k) k) ^ 2 := congrArg (· ^ 2) hrec
    have key : (k + 1) ^ 2 * 4 ^ (2 * (k + 1)) ≤
        (k + 1) ^ 2 * ((4 * (k + 1) + 1) * (Nat.choose (2 * (k + 1)) (k + 1)) ^ 2) := by
      calc (k + 1) ^ 2 * 4 ^ (2 * (k + 1))
          = 16 * (k + 1) ^ 2 * 4 ^ (2 * k) := by rw [mul_add, pow_add]; ring
        _ ≤ 16 * (k + 1) ^ 2 * ((4 * k + 1) * (Nat.choose (2 * k) k) ^ 2) :=
            Nat.mul_le_mul_left _ ih
        _ = 4 * (4 * (4 * k + 1) * (k + 1) ^ 2) * (Nat.choose (2 * k) k) ^ 2 := by ring
        _ ≤ 4 * ((4 * (k + 1) + 1) * (2 * k + 1) ^ 2) * (Nat.choose (2 * k) k) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hpoly)
        _ = (4 * (k + 1) + 1) * (2 * (2 * k + 1) * Nat.choose (2 * k) k) ^ 2 := by ring
        _ = (4 * (k + 1) + 1) * ((k + 1) * Nat.choose (2 * (k + 1)) (k + 1)) ^ 2 := by rw [← hsq]
        _ = (k + 1) ^ 2 * ((4 * (k + 1) + 1) * (Nat.choose (2 * (k + 1)) (k + 1)) ^ 2) := by ring
    exact Nat.le_of_mul_le_mul_left key (Nat.pow_pos (Nat.succ_pos k))

def majBit {k : ℕ} (u c : Fin (2 * k + 1) → Bool) : Bool :=
  decide (k < (univ.filter (fun j => u j = c j)).card)

lemma jks_single_col_sum {k : ℕ} (u : Fin (2 * k + 1) → Bool) (idx : Fin (2 * k + 1)) :
    ∑ c : Fin (2 * k + 1) → Bool, (if majBit u c = c idx then (1 : ℤ) else -1) =
      bSign (u idx) * (2 * Nat.choose (2 * k) k) := by
  classical
  let e : (Fin (2 * k + 1) → Bool) ≃ (Fin (2 * k + 1) → Bool) :=
    { toFun := fun c j => (u j == c j)
      invFun := fun d j => (u j == d j)
      left_inv := fun c => by funext j; dsimp only; cases u j <;> cases c j <;> decide
      right_inv := fun d => by funext j; dsimp only; cases u j <;> cases d j <;> decide }
  rw [← Equiv.sum_comp e.symm]
  have he_symm : ∀ d j, e.symm d j = (u j == d j) := fun _ _ => rfl
  have hterm : ∀ d : Fin (2 * k + 1) → Bool,
      (if majBit u (e.symm d) = e.symm d idx then (1 : ℤ) else -1) =
      bSign (u idx) * (if decide (k < (univ.filter (fun j => d j = true)).card) = d idx then 1 else -1) := by
    intro d
    have hwt : (univ.filter (fun j => u j = e.symm d j)).card =
        (univ.filter (fun j => d j = true)).card := by
      congr 1; ext j
      simp only [mem_filter, mem_univ, true_and, he_symm]
      cases u j <;> cases d j <;> decide
    unfold majBit
    rw [hwt, he_symm]
    dsimp only [bSign]
    cases u idx <;> cases d idx <;>
      cases decide (k < (univ.filter (fun j => d j = true)).card) <;> decide
  simp only [hterm, ← mul_sum]
  congr 1
  let eSplit : (Fin (2 * k + 1) → Bool) ≃ Bool × ({j : Fin (2 * k + 1) // j ≠ idx} → Bool) :=
    { toFun := fun d => (d idx, fun j => d j.1)
      invFun := fun p j => if h : j = idx then p.1 else p.2 ⟨j, h⟩
      left_inv := fun d => by
        funext j
        dsimp only
        by_cases h : j = idx
        · rw [dif_pos h, h]
        · rw [dif_neg h]
      right_inv := fun ⟨b, f⟩ => by
        ext
        · simp
        · rename_i j; simp [j.2] }
  rw [← Equiv.sum_comp eSplit.symm, Fintype.sum_prod_type_right]
  have hinner : ∀ f : {j : Fin (2 * k + 1) // j ≠ idx} → Bool,
      ∑ b : Bool, (if decide (k < (univ.filter (fun j => eSplit.symm (b, f) j = true)).card) =
          eSplit.symm (b, f) idx then (1 : ℤ) else -1) =
      if (univ.filter (fun j : {j : Fin (2 * k + 1) // j ≠ idx} => f j = true)).card = k
      then 2 else 0 := by
    intro f
    set w := (univ.filter (fun j : {j : Fin (2 * k + 1) // j ≠ idx} => f j = true)).card
    have hwt_b : ∀ b : Bool,
        (univ.filter (fun j : Fin (2 * k + 1) => eSplit.symm (b, f) j = true)).card =
        w + (if b = true then 1 else 0) := by
      intro b
      have hpart : univ.filter (fun j : Fin (2 * k + 1) => eSplit.symm (b, f) j = true) =
          (univ.filter (fun j : Fin (2 * k + 1) => j ≠ idx ∧ eSplit.symm (b, f) j = true)) ∪
          (if b = true then {idx} else ∅) := by
        ext j
        by_cases hj : j = idx
        · subst hj; cases b <;> simp [eSplit]
        · cases b <;> simp [eSplit, hj]
      have hdisj : Disjoint (univ.filter (fun j : Fin (2 * k + 1) => j ≠ idx ∧ eSplit.symm (b, f) j = true))
          (if b = true then {idx} else ∅) := by
        cases b <;> simp [disjoint_singleton_right]
      have hc1 : (univ.filter (fun j : Fin (2 * k + 1) => j ≠ idx ∧ eSplit.symm (b, f) j = true)).card = w := by
        have heS : ∀ j, eSplit.symm (b, f) j = if h : j = idx then b else f ⟨j, h⟩ := fun _ => rfl
        refine card_bij (fun j hj => ⟨j, (mem_filter.1 hj).2.1⟩) ?_ ?_ ?_
        · intro j hj
          have ⟨hne, htr⟩ := (mem_filter.1 hj).2
          rw [heS, dif_neg hne] at htr
          exact mem_filter.2 ⟨mem_univ _, htr⟩
        · intro j1 _ j2 _ h; exact congrArg Subtype.val h
        · intro j hj
          refine ⟨j.1, mem_filter.2 ⟨mem_univ _, j.2, ?_⟩, rfl⟩
          rw [heS, dif_neg j.2]
          exact (mem_filter.1 hj).2
      rw [hpart, card_union_of_disjoint hdisj, hc1]
      cases b <;> simp
    have hidx : ∀ b : Bool, eSplit.symm (b, f) idx = b := fun b => by simp [eSplit]
    simp only [Fintype.sum_bool, hwt_b, hidx, ↓reduceIte, Bool.false_eq_true, add_zero]
    by_cases hw : w = k
    · rw [hw]; simp
    · by_cases hlt : w < k
      · have h1 : decide (k < w + 1) = false := decide_eq_false (by omega)
        have h2 : decide (k < w) = false := decide_eq_false (by omega)
        rw [h1, h2, if_neg hw]
        decide
      · have h1 : decide (k < w + 1) = true := decide_eq_true (by omega)
        have h2 : decide (k < w) = true := decide_eq_true (by omega)
        rw [h1, h2, if_neg hw]
        decide
  simp only [hinner]
  have hcard_rest : Fintype.card {j : Fin (2 * k + 1) // j ≠ idx} = 2 * k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]; omega
  let eRest : {j : Fin (2 * k + 1) // j ≠ idx} ≃ Fin (2 * k) :=
    Fintype.equivFinOfCardEq hcard_rest
  have hcount : (univ.filter (fun f : {j : Fin (2 * k + 1) // j ≠ idx} → Bool =>
      (univ.filter (fun j => f j = true)).card = k)).card = Nat.choose (2 * k) k := by
    have hbij : (univ.filter (fun f : {j : Fin (2 * k + 1) // j ≠ idx} → Bool =>
        (univ.filter (fun j => f j = true)).card = k)).card =
        (powersetCard k (univ : Finset (Fin (2 * k)))).card := by
      refine card_bij (fun f _ => (univ.filter (fun j => f j = true)).image eRest) ?_ ?_ ?_
      · intro f hf
        rw [mem_powersetCard]
        refine ⟨subset_univ _, ?_⟩
        rw [card_image_of_injective _ eRest.injective]
        exact (mem_filter.1 hf).2
      · intro f1 _ f2 _ heq
        funext j
        have hiff : eRest j ∈ (univ.filter (fun j => f1 j = true)).image eRest ↔
            eRest j ∈ (univ.filter (fun j => f2 j = true)).image eRest := by rw [heq]
        simp only [mem_image, mem_filter, mem_univ, true_and, eRest.injective.eq_iff, exists_eq_right] at hiff
        exact Bool.eq_iff_iff.2 hiff
      · intro U hU
        let f : {j : Fin (2 * k + 1) // j ≠ idx} → Bool := fun j => decide (eRest j ∈ U)
        refine ⟨f, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
        · have : (univ.filter (fun j => f j = true)).image eRest = U := by
            ext a; simp only [mem_image, mem_filter, mem_univ, true_and, f, decide_eq_true_eq]
            exact ⟨fun ⟨j, hj, heq⟩ => heq ▸ hj, fun ha => ⟨eRest.symm a, by simpa using ha, by simp⟩⟩
          rw [← card_image_of_injective _ eRest.injective, this]
          exact (mem_powersetCard.1 hU).2
        · ext a; simp only [mem_image, mem_filter, mem_univ, true_and, f, decide_eq_true_eq]
          exact ⟨fun ⟨j, hj, heq⟩ => heq ▸ hj, fun ha => ⟨eRest.symm a, by simpa using ha, by simp⟩⟩
    rw [hbij, card_powersetCard, card_univ, Fintype.card_fin]
  have hsum_ite : (∑ f : {j : Fin (2 * k + 1) // j ≠ idx} → Bool,
      if (univ.filter (fun j => f j = true)).card = k then (2 : ℤ) else 0) =
      2 * (univ.filter (fun f : {j : Fin (2 * k + 1) // j ≠ idx} → Bool =>
        (univ.filter (fun j => f j = true)).card = k)).card := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, mul_comm]
  rw [hsum_ite, hcount]

lemma jks_columns_cheb {k q g : ℕ} (hq : 0 < q) (hg : 0 < g)
    (hgap : 4000 * (4 * k + 1) * (q + g * g) ≤ q * q)
    (u : Fin (2 * k + 1) → Bool) (idx : Fin (2 * k + 1)) :
    let Col := Fin (2 * k + 1) → Bool
    let Z : Col → ℤ := fun c => if majBit u c = c idx then 1 else -1
    let goodCol := univ.filter (fun C : Fin q → Col =>
      if u idx = true then (4 * g + 4 : ℤ) ≤ ∑ t : Fin q, Z (C t)
      else ∑ t : Fin q, Z (C t) ≤ -((4 * g + 4 : ℤ)))
    143 * (Fintype.card Col) ^ q ≤ 144 * goodCol.card := by
  classical
  intro Col Z goodCol
  set Nc := Fintype.card Col
  have hNc : Nc = 2 * 4 ^ k := by
    simp only [Nc, Col, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [pow_succ, pow_mul]; ring
  have hNc_pos : 0 < Nc := by rw [hNc]; positivity
  set μ : ℤ := ∑ c : Col, Z c
  have hμ_eq : μ = bSign (u idx) * (2 * Nat.choose (2 * k) k) := jks_single_col_sum u idx
  set W : Col → ℤ := fun c => Nc * Z c - μ
  have hWsum : ∑ c : Col, W c = 0 := by
    simp only [W, sum_sub_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
    ring
  have hW2 : ∑ c : Col, W c ^ 2 ≤ (Nc : ℤ) ^ 3 := by
    have hZ2 : ∑ c : Col, Z c ^ 2 = Nc := by
      have : ∀ c : Col, Z c ^ 2 = 1 := fun c => by dsimp only [Z]; split_ifs <;> norm_num
      simp only [this, sum_const, card_univ, nsmul_eq_mul, mul_one, Nc]
    have hcalc : ∑ c : Col, W c ^ 2 = (Nc : ℤ) ^ 2 * ∑ c : Col, Z c ^ 2 - Nc * μ ^ 2 := by
      have hexp : ∀ c : Col, W c ^ 2 = (Nc : ℤ) ^ 2 * Z c ^ 2 - 2 * Nc * μ * Z c + μ ^ 2 :=
        fun c => by dsimp only [W]; ring
      simp only [hexp, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
        nsmul_eq_mul]
      ring
    rw [hcalc, hZ2]
    nlinarith [sq_nonneg μ]
  have hid := sum_sq_sample W hWsum q
  have hsumW : ∀ C : Fin q → Col, ∑ t : Fin q, W (C t) = Nc * (∑ t : Fin q, Z (C t)) - q * μ := by
    intro C
    simp only [W, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp only [hsumW] at hid
  set Bad := univ.filter (fun C : Fin q → Col =>
    ¬ (if u idx = true then (4 * g + 4 : ℤ) ≤ ∑ t : Fin q, Z (C t)
       else ∑ t : Fin q, Z (C t) ≤ -((4 * g + 4 : ℤ))))
  have hmargin_and_nn : 144 * (q : ℤ) * (Nc : ℤ) ^ 2 ≤
      (q * (2 * (Nat.choose (2 * k) k : ℤ)) - Nc * (4 * g + 4 : ℤ)) ^ 2 ∧
      0 ≤ q * (2 * (Nat.choose (2 * k) k : ℤ)) - Nc * (4 * g + 4 : ℤ) := by
    have hch := choose_mid_sq k
    have hchZ : (4 : ℤ) ^ (2 * k) ≤ (4 * k + 1) * (Nat.choose (2 * k) k : ℤ) ^ 2 := by
      exact_mod_cast hch
    have hgapZ : (4000 : ℤ) * (4 * k + 1) * (q + g * g) ≤ q * q := by exact_mod_cast hgap
    have hNcZ : (Nc : ℤ) = 2 * (4 : ℤ) ^ k := by exact_mod_cast hNc
    have hqP : 4000 * ((q : ℤ) + g * g) * (Nc : ℤ) ^ 2 ≤
        (q * (2 * (Nat.choose (2 * k) k : ℤ))) ^ 2 := by
      have h1 : (4 * k + 1 : ℤ) * (4000 * ((q : ℤ) + g * g) * (Nc : ℤ) ^ 2) ≤
          (4 * k + 1 : ℤ) * (q * (2 * (Nat.choose (2 * k) k : ℤ))) ^ 2 := by
        have hNc2 : (Nc : ℤ) ^ 2 = 4 * (4 : ℤ) ^ (2 * k) := by
          rw [hNcZ, mul_pow, ← pow_mul, mul_comm k 2]; ring
        rw [hNc2]
        have h2 : (4000 * (4 * k + 1 : ℤ) * (q + g * g)) * (4 * (4 : ℤ) ^ (2 * k)) ≤
            (q * q) * (4 * (4 * k + 1) * (Nat.choose (2 * k) k : ℤ) ^ 2) :=
          mul_le_mul hgapZ (by linarith) (by positivity) (by positivity)
        linarith
      exact le_of_mul_le_mul_left h1 (by positivity)
    set A : ℤ := q * (2 * (Nat.choose (2 * k) k : ℤ))
    set B : ℤ := Nc * (4 * g + 4 : ℤ)
    have hA_nn : 0 ≤ A := by positivity
    have hB_nn : 0 ≤ B := by positivity
    have h8g : (4 * g + 4 : ℤ) ≤ 8 * g := by omega
    have hB2 : 4 * B ^ 2 ≤ A ^ 2 := by
      have h1 : (4 * g + 4 : ℤ) ^ 2 ≤ 64 * (g * g) := by nlinarith
      have h2 : 4 * B ^ 2 = 4 * (Nc : ℤ) ^ 2 * (4 * g + 4 : ℤ) ^ 2 := by dsimp only [B]; ring
      have h3 : 4 * (Nc : ℤ) ^ 2 * (4 * g + 4 : ℤ) ^ 2 ≤ 4 * (Nc : ℤ) ^ 2 * (64 * (g * g)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 : 256 * ((g : ℤ) * g) ≤ 4000 * ((q : ℤ) + g * g) := by nlinarith [sq_nonneg (g : ℤ)]
      have h5 : 256 * ((g : ℤ) * g) * (Nc : ℤ) ^ 2 ≤ 4000 * ((q : ℤ) + g * g) * (Nc : ℤ) ^ 2 :=
        mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
      linarith
    have h2B_le_A : 2 * B ≤ A := by nlinarith
    have h4diff : A ^ 2 ≤ 4 * (A - B) ^ 2 := by nlinarith
    have h4000a : 576 * (q : ℤ) ≤ 4000 * ((q : ℤ) + g * g) := by nlinarith [sq_nonneg (g : ℤ)]
    have h4000 : 576 * (q : ℤ) * (Nc : ℤ) ^ 2 ≤ 4000 * ((q : ℤ) + g * g) * (Nc : ℤ) ^ 2 :=
      mul_le_mul_of_nonneg_right h4000a (sq_nonneg _)
    exact ⟨by linarith, by linarith⟩
  obtain ⟨hmargin, hnn⟩ := hmargin_and_nn
  have hbad_dev : ∀ C ∈ Bad,
      144 * (q : ℤ) * (Nc : ℤ) ^ 2 ≤ (Nc * (∑ t : Fin q, Z (C t)) - q * μ) ^ 2 := by
    intro C hC
    have hnot := (mem_filter.1 hC).2
    have hNcZ : (0 : ℤ) ≤ Nc := by positivity
    cases hu : u idx
    · simp only [hu, Bool.false_eq_true, ↓reduceIte, not_le] at hnot
      rw [hμ_eq, hu]
      simp only [bSign, Bool.false_eq_true, ↓reduceIte]
      have hle : q * (2 * (Nat.choose (2 * k) k : ℤ)) - Nc * (4 * g + 4 : ℤ) ≤
          Nc * (∑ t : Fin q, Z (C t)) - q * (-1 * (2 * (Nat.choose (2 * k) k : ℤ))) := by
        have h1 : Nc * (-((4 * g + 4 : ℤ))) ≤ Nc * (∑ t : Fin q, Z (C t)) :=
          mul_le_mul_of_nonneg_left hnot.le hNcZ
        linarith
      have hsq : (q * (2 * (Nat.choose (2 * k) k : ℤ)) - Nc * (4 * g + 4 : ℤ)) ^ 2 ≤
          (Nc * (∑ t : Fin q, Z (C t)) - q * (-1 * (2 * (Nat.choose (2 * k) k : ℤ)))) ^ 2 := by
        simpa only [sq] using mul_le_mul hle hle hnn (hnn.trans hle)
      exact hmargin.trans hsq
    · simp only [hu, ↓reduceIte, not_le] at hnot
      rw [hμ_eq, hu]
      simp only [bSign, ↓reduceIte, one_mul]
      have hle : q * (2 * (Nat.choose (2 * k) k : ℤ)) - Nc * (4 * g + 4 : ℤ) ≤
          -(Nc * (∑ t : Fin q, Z (C t)) - q * (2 * (Nat.choose (2 * k) k : ℤ))) := by
        have h1 : Nc * (∑ t : Fin q, Z (C t)) ≤ Nc * (4 * g + 4 : ℤ) :=
          mul_le_mul_of_nonneg_left hnot.le hNcZ
        linarith
      have hsq : (q * (2 * (Nat.choose (2 * k) k : ℤ)) - Nc * (4 * g + 4 : ℤ)) ^ 2 ≤
          (Nc * (∑ t : Fin q, Z (C t)) - q * (2 * (Nat.choose (2 * k) k : ℤ))) ^ 2 := by
        have h1 := mul_le_mul hle hle hnn (hnn.trans hle)
        rw [← sq, ← sq, neg_sq] at h1
        exact h1
      exact hmargin.trans hsq
  have hmk : (Bad.card : ℤ) * (144 * q * (Nc : ℤ) ^ 2) ≤
      ∑ C : Fin q → Col, (Nc * (∑ t : Fin q, Z (C t)) - q * μ) ^ 2 := by
    calc (Bad.card : ℤ) * (144 * q * (Nc : ℤ) ^ 2) =
          Bad.card • (144 * q * (Nc : ℤ) ^ 2) := by rw [nsmul_eq_mul]
      _ ≤ ∑ C ∈ Bad, (Nc * (∑ t : Fin q, Z (C t)) - q * μ) ^ 2 :=
          card_nsmul_le_sum _ _ _ hbad_dev
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
  have hmul : (144 * (Bad.card : ℤ)) * (q * (Nc : ℤ) ^ 3) ≤
      ((Nc : ℤ) ^ q) * (q * (Nc : ℤ) ^ 3) := by
    have h1 := mul_le_mul_of_nonneg_left hmk (by positivity : (0 : ℤ) ≤ Nc)
    rw [hid] at h1
    have h2 : (q : ℤ) * (Nc : ℤ) ^ q * ∑ c : Col, W c ^ 2 ≤ (q : ℤ) * (Nc : ℤ) ^ q * (Nc : ℤ) ^ 3 :=
      mul_le_mul_of_nonneg_left hW2 (by positivity)
    linarith
  have hBad144 : 144 * Bad.card ≤ Nc ^ q := by
    have : (144 : ℤ) * Bad.card ≤ (Nc : ℤ) ^ q :=
      le_of_mul_le_mul_right hmul (by positivity)
    exact_mod_cast this
  have hpart := card_filter_add_card_filter_not (s := (univ : Finset (Fin q → Col)))
    (fun C : Fin q → Col =>
      if u idx = true then (4 * g + 4 : ℤ) ≤ ∑ t : Fin q, Z (C t)
      else ∑ t : Fin q, Z (C t) ≤ -((4 * g + 4 : ℤ)))
  rw [card_univ, Fintype.card_fun, Fintype.card_fin] at hpart
  have hpart' : goodCol.card + Bad.card = Nc ^ q := hpart
  change 143 * Nc ^ q ≤ 144 * goodCol.card
  omega

set_option maxHeartbeats 800000 in
lemma split_pair_lb {n r g b : ℕ} (hg : 0 < g) (hKg : 16384 * g ≤ n)
    (hr : 0 < r) (hnr : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hov : ∀ j l : Fin r, j ≠ l →
      128 * (univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (S : Finset (Bool × Fin n))
    (hbPos : 1 ≤ b)
    (hcost : ∃ R : ℕ, 0 < R ∧
      ∃ (send : Fin R → ({v : Bool × Fin n // v ∈ S} → Bool) → Fin (2 ^ b))
        (recv : Fin R → Fin (2 ^ b) → ({v : Bool × Fin n // v ∉ S} → Bool) → Bool),
        ∀ (a : {v : Bool × Fin n // v ∈ S} → Bool) (z : {v : Bool × Fin n // v ∉ S} → Bool),
          let x := fun v : Bool × Fin n => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
          let D := fun j : Fin r => (univ.filter (fun i : Fin n =>
            x (false, i) ≠ x (true, M j i))).card
          let yes := ∀ j : Fin r, 15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n
          let no := ∃ j : Fin r, 32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j
          let good := fun seed : Fin R => (yes → recv seed (send seed a) z = true) ∧
            (no → recv seed (send seed a) z = false)
          2 * R ≤ 3 * (univ.filter (fun seed : Fin R => good seed)).card) :
    let cross := fun j : Fin r => (univ.filter (fun i : Fin n =>
      ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))).card
    let m := univ.sup cross
    m * m ≤ 10 ^ 13 * b * max m (g * g) := by
  classical
  intro cross m
  obtain ⟨j0, -, hj0_max⟩ := exists_max_image (univ : Finset (Fin r)) cross
    (univ_nonempty_iff.2 ⟨⟨0, hr⟩⟩)
  have hm_eq : m = cross j0 := by
    apply le_antisymm
    · exact Finset.sup_le fun j hj => hj0_max j hj
    · exact le_sup (f := cross) (mem_univ j0)
  by_cases hm0 : m = 0
  · rw [hm0]; simp
  set q := min m (n / 256)
  have hn_gt : 8192 < n := by
    have : 8192 ≤ 8192 * r := Nat.le_mul_of_pos_right 8192 hr
    omega
  have hq_pos : 0 < q := by dsimp only [q]; omega
  have hq_256 : 256 * q ≤ n := by
    have : q ≤ n / 256 := min_le_right _ _
    have := Nat.mul_div_le n 256
    omega
  have hm_le_512q : m ≤ 512 * q := by
    rcases le_total m (n / 256) with hle | hle
    · rw [show q = m from min_eq_left hle]; omega
    · rw [show q = n / 256 from min_eq_right hle]
      have hm_le_n : m ≤ n := by
        rw [hm_eq]; exact (card_filter_le _ _).trans (by simp)
      omega
  by_cases hsmall : q * q < 100000 * max q (g * g)
  · have hq_le_m : q ≤ m := min_le_left _ _
    have hmax_le : max q (g * g) ≤ max m (g * g) := max_le_max hq_le_m le_rfl
    have hm2 : m * m ≤ 512 * 512 * (q * q) := by
      calc m * m ≤ (512 * q) * (512 * q) := Nat.mul_le_mul hm_le_512q hm_le_512q
        _ = 512 * 512 * (q * q) := by ring
    have h1 : 512 * 512 * (q * q) ≤ 512 * 512 * (100000 * max m (g * g)) := by
      have : q * q ≤ 100000 * max m (g * g) := hsmall.le.trans (Nat.mul_le_mul_left _ hmax_le)
      exact Nat.mul_le_mul_left _ this
    have hconst : 512 * 512 * 100000 ≤ 10 ^ 13 := by norm_num
    calc m * m ≤ 512 * 512 * (100000 * max m (g * g)) := hm2.trans h1
      _ = (512 * 512 * 100000) * max m (g * g) := by ring
      _ ≤ 10 ^ 13 * max m (g * g) := Nat.mul_le_mul_right _ hconst
      _ ≤ 10 ^ 13 * b * max m (g * g) := by nlinarith
  have hbig : 100000 * max q (g * g) ≤ q * q := le_of_not_gt hsmall
  set E0 := univ.filter (fun i : Fin n => ¬ ((false, i) ∈ S ↔ (true, M j0 i) ∈ S))
  have hq_le_E0 : q ≤ E0.card := by
    have : E0.card = m := hm_eq.symm
    rw [this]; exact min_le_left _ _
  obtain ⟨R0, hR0_sub, hR0_card⟩ := exists_subset_card_eq hq_le_E0
  set target := (15 * n) / 32 - q / 2
  have htar_le : target ≤ n - R0.card := by rw [hR0_card]; dsimp only [target]; omega
  obtain ⟨x0, hx0_tar, hx0_pin⟩ := pinning_lemma (g := g) hr hnr (by omega) M hov j0 R0
    (by rw [hR0_card]; exact hq_256) target htar_le
  set k := q * q / (20000 * (q + g * g))
  have hqg_pos : 0 < q + g * g := by positivity
  have hk_ge2 : 2 ≤ k := by
    have hsum : q + g * g ≤ 2 * max q (g * g) := by omega
    have hmul : 2 * (20000 * (q + g * g)) ≤ q * q := by nlinarith
    exact (Nat.le_div_iff_mul_le (by positivity)).2 hmul
  have hgap : 4000 * (4 * k + 1) * (q + g * g) ≤ q * q := by
    have hdiv : 20000 * (q + g * g) * k ≤ q * q := Nat.mul_div_le _ _
    have h45 : 4 * k + 1 ≤ 5 * k := by omega
    nlinarith
  set N := 2 * k + 1
  have hN_pos : 0 < N := by omega
  have hq2_le_N : q * q ≤ 40000 * N * max q (g * g) := by
    have hlt : q * q < (20000 * (q + g * g)) * (k + 1) :=
      Nat.lt_mul_div_succ (q * q) (by positivity)
    have hsum : q + g * g ≤ 2 * max q (g * g) := by omega
    have hkN : k + 1 ≤ N := by dsimp only [N]; omega
    nlinarith
  obtain ⟨R, hRpos, send, recv, hproto⟩ := hcost
  let eR0 : Fin q ≃ {i : Fin n // i ∈ R0} :=
    ((R0.equivFin).trans (Equiv.cast (by rw [hR0_card]))).symm
  let Col := Fin N → Bool
  let Seed2 := Fin R × (Fin q → Col)
  let R2 := Fintype.card Seed2
  have hR2pos : 0 < R2 := by
    have : 0 < Fintype.card (Fin q → Col) := Fintype.card_pos
    simp only [R2, Seed2, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hRpos this
  let eSeed2 : Fin R2 ≃ Seed2 := (Fintype.equivFin Seed2).symm
  let aOf : (Fin q → Col) → (Fin N → Bool) → ({v : Bool × Fin n // v ∈ S} → Bool) :=
    fun C u v =>
      if h : ∃ t : Fin q, v.1 = (false, (eR0 t).1) ∨ v.1 = (true, M j0 (eR0 t).1) then
        majBit u (C h.choose)
      else x0 v.1
  let zOf : (Fin q → Col) → Fin N → ({v : Bool × Fin n // v ∉ S} → Bool) :=
    fun C idx v =>
      if h : ∃ t : Fin q, v.1 = (false, (eR0 t).1) ∨ v.1 = (true, M j0 (eR0 t).1) then
        C h.choose idx
      else x0 v.1
  let sendIdx : Fin R2 → (Fin N → Bool) → Fin (2 ^ b) := fun s u =>
    let p := eSeed2 s
    send p.1 (aOf p.2 u)
  let recvIdx : Fin R2 → Fin (2 ^ b) → Fin N → Bool := fun s m idx =>
    let p := eSeed2 s
    !(recv p.1 m (zOf p.2 idx))
  have hidx_good : ∀ (u : Fin N → Bool) (idx : Fin N),
      19 * R2 ≤ 30 * (univ.filter (fun s : Fin R2 =>
        recvIdx s (sendIdx s u) idx = u idx)).card := by
    intro u idx
    set Z : Col → ℤ := fun c => if majBit u c = c idx then 1 else -1
    set goodCol := univ.filter (fun C : Fin q → Col =>
      if u idx = true then (4 * g + 4 : ℤ) ≤ ∑ t : Fin q, Z (C t)
      else ∑ t : Fin q, Z (C t) ≤ -((4 * g + 4 : ℤ)))
    have hcheb := jks_columns_cheb hq_pos hg hgap u idx
    have huniq : ∀ (t1 t2 : Fin q),
        ((false, (eR0 t1).1) = (false, (eR0 t2).1) ∨ (false, (eR0 t1).1) = (true, M j0 (eR0 t2).1)) →
        t1 = t2 := by
      intro t1 t2 h
      rcases h with h1 | h2
      · have := congrArg Prod.snd h1
        exact eR0.injective (Subtype.ext this)
      · simp at h2
    have huniqT : ∀ (t1 t2 : Fin q),
        ((true, M j0 (eR0 t1).1) = (false, (eR0 t2).1) ∨
          (true, M j0 (eR0 t1).1) = (true, M j0 (eR0 t2).1)) →
        t1 = t2 := by
      intro t1 t2 h
      rcases h with h1 | h2
      · simp at h1
      · have := (M j0).injective (congrArg Prod.snd h2)
        exact eR0.injective (Subtype.ext this)
    have hpair_good : ∀ C ∈ goodCol,
        2 * R ≤ 3 * (univ.filter (fun sd : Fin R =>
          (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card := by
      intro C hC
      set x := fun v : Bool × Fin n => if h : v ∈ S then aOf C u ⟨v, h⟩ else zOf C idx ⟨v, h⟩
      have hout : ∀ i : Fin n, i ∉ R0 →
          x (false, i) = x0 (false, i) ∧ x (true, M j0 i) = x0 (true, M j0 i) := by
        intro i hi
        have hnotF : ¬ ∃ t : Fin q, (false, i) = (false, (eR0 t).1) ∨
            (false, i) = (true, M j0 (eR0 t).1) := by
          rintro ⟨t, h1 | h2⟩
          · have h' := (Prod.mk.inj h1).2; exact hi (h' ▸ (eR0 t).2)
          · simp at h2
        have hnotT : ¬ ∃ t : Fin q, (true, M j0 i) = (false, (eR0 t).1) ∨
            (true, M j0 i) = (true, M j0 (eR0 t).1) := by
          rintro ⟨t, h1 | h2⟩
          · simp at h1
          · have h' := (M j0).injective (Prod.mk.inj h2).2; exact hi (h' ▸ (eR0 t).2)
        constructor
        · by_cases hv : (false, i) ∈ S
          · dsimp only [x]; rw [dif_pos hv]; dsimp only [aOf]; rw [dif_neg hnotF]
          · dsimp only [x]; rw [dif_neg hv]; dsimp only [zOf]; rw [dif_neg hnotF]
        · by_cases hv : (true, M j0 i) ∈ S
          · dsimp only [x]; rw [dif_pos hv]; dsimp only [aOf]; rw [dif_neg hnotT]
          · dsimp only [x]; rw [dif_neg hv]; dsimp only [zOf]; rw [dif_neg hnotT]
      have hpin := fun l hlj => hx0_pin l hlj x hout
      have hin : ∀ t : Fin q,
          (x (false, (eR0 t).1) ≠ x (true, M j0 (eR0 t).1)) ↔ (majBit u (C t) ≠ C t idx) := by
        intro t
        have hmemE : (eR0 t).1 ∈ E0 := hR0_sub (eR0 t).2
        have hsplit := (mem_filter.1 hmemE).2
        have hexF : ∃ t' : Fin q, (false, (eR0 t).1) = (false, (eR0 t').1) ∨
            (false, (eR0 t).1) = (true, M j0 (eR0 t').1) := ⟨t, Or.inl rfl⟩
        have hexT : ∃ t' : Fin q, (true, M j0 (eR0 t).1) = (false, (eR0 t').1) ∨
            (true, M j0 (eR0 t).1) = (true, M j0 (eR0 t').1) := ⟨t, Or.inr rfl⟩
        have hcF : hexF.choose = t := (huniq t hexF.choose hexF.choose_spec).symm
        have hcT : hexT.choose = t := (huniqT t hexT.choose hexT.choose_spec).symm
        by_cases hF : (false, (eR0 t).1) ∈ S
        · have hT : (true, M j0 (eR0 t).1) ∉ S := fun hT => hsplit ⟨fun _ => hT, fun _ => hF⟩
          have h1 : x (false, (eR0 t).1) = majBit u (C t) := by
            dsimp only [x]; rw [dif_pos hF]; dsimp only [aOf]; rw [dif_pos hexF, hcF]
          have h2 : x (true, M j0 (eR0 t).1) = C t idx := by
            dsimp only [x]; rw [dif_neg hT]; dsimp only [zOf]; rw [dif_pos hexT, hcT]
          rw [h1, h2]
        · have hT : (true, M j0 (eR0 t).1) ∈ S := by
            by_contra hT; exact hsplit ⟨fun h => absurd h hF, fun h => absurd h hT⟩
          have h1 : x (false, (eR0 t).1) = C t idx := by
            dsimp only [x]; rw [dif_neg hF]; dsimp only [zOf]; rw [dif_pos hexF, hcF]
          have h2 : x (true, M j0 (eR0 t).1) = majBit u (C t) := by
            dsimp only [x]; rw [dif_pos hT]; dsimp only [aOf]; rw [dif_pos hexT, hcT]
          rw [h1, h2]; exact ne_comm
      set Dj0 := (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card
      set DR0 := (univ.filter (fun t : Fin q => majBit u (C t) ≠ C t idx)).card
      have hDj0 : Dj0 = target + DR0 := by
        have hpart : univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)) =
            ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) ∪
            (R0.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) := by
          ext i; simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and]; tauto
        have hdisj : Disjoint
            ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)))
            (R0.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) :=
          disjoint_filter_filter disjoint_sdiff_self_left
        have h1 : ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card = target := by
          rw [← hx0_tar]
          congr 1; ext i
          simp only [mem_filter, mem_sdiff, mem_univ, true_and]
          by_cases hi : i ∈ R0
          · simp [hi]
          · simp only [hi, not_false_eq_true, true_and, (hout i hi).1, (hout i hi).2]
        have h2 : (R0.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card = DR0 := by
          refine card_bij (fun i hi => eR0.symm ⟨i, (mem_filter.1 hi).1⟩) ?_ ?_ ?_
          · intro i hi
            have hne := (mem_filter.1 hi).2
            rw [mem_filter]
            refine ⟨mem_univ _, ?_⟩
            have h1 := (hin (eR0.symm ⟨i, (mem_filter.1 hi).1⟩)).1
            simp only [Equiv.apply_symm_apply] at h1
            exact h1 hne
          · intro i1 _ i2 _ h; exact congrArg Subtype.val (eR0.symm.injective h)
          · intro t ht
            exact ⟨(eR0 t).1, mem_filter.2 ⟨(eR0 t).2, (hin t).2 (mem_filter.1 ht).2⟩, by simp⟩
        calc Dj0 = (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card := rfl
          _ = (((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) ∪
              (R0.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)))).card := congrArg card hpart
          _ = ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card +
              (R0.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card :=
              card_union_of_disjoint hdisj
          _ = target + DR0 := by rw [h1, h2]
      have hDR0_Z : (q : ℤ) - 2 * DR0 = ∑ t : Fin q, Z (C t) := by
        have hterm : ∀ t : Fin q, Z (C t) = 1 - 2 * (if majBit u (C t) ≠ C t idx then (1 : ℤ) else 0) := by
          intro t; dsimp only [Z]
          by_cases h : majBit u (C t) = C t idx <;> simp [h]
        simp only [hterm, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one, ← mul_sum, sum_boole]
        rfl
      have hCprop := (mem_filter.1 hC).2
      have hpr := hproto (aOf C u) (zOf C idx)
      dsimp only at hpr
      cases hu : u idx
      · simp only [hu, Bool.false_eq_true, ↓reduceIte] at hCprop
        have hyes : ∀ j : Fin r,
            15 * n + 32 * g ≤ 32 * (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card ∧
            32 * (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card + 32 * g ≤ 17 * n := by
          intro j
          by_cases hj : j = j0
          · subst hj
            change 15 * n + 32 * g ≤ 32 * Dj0 ∧ 32 * Dj0 + 32 * g ≤ 17 * n
            have hDR0_le : DR0 ≤ q := (card_filter_le _ _).trans (by simp)
            have htar_def : target = (15 * n) / 32 - q / 2 := rfl
            zify at hDj0 htar_def hq_256 hKg hn_gt hDR0_le ⊢
            constructor <;> omega
          · exact hpin j hj
        refine hpr.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
        have hsd1 := (mem_filter.1 hsd).2.1 hyes
        simp only [mem_filter, mem_univ, true_and, hsd1, Bool.not_true, hu]
      · simp only [hu, ↓reduceIte] at hCprop
        have hno : ∃ j : Fin r,
            32 * (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card + 32 * g ≤ 15 * n ∨
            17 * n + 32 * g ≤ 32 * (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card := by
          refine ⟨j0, Or.inl ?_⟩
          change 32 * Dj0 + 32 * g ≤ 15 * n
          have htar_def : target = (15 * n) / 32 - q / 2 := rfl
          zify at hDj0 htar_def hq_256 hKg hn_gt ⊢
          omega
        refine hpr.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
        have hsd2 := (mem_filter.1 hsd).2.2 hno
        simp only [mem_filter, mem_univ, true_and, hsd2, Bool.not_false, hu]
    have hcount_prod : (univ.filter (fun s : Fin R2 => recvIdx s (sendIdx s u) idx = u idx)).card =
        ∑ C : Fin q → Col, (univ.filter (fun sd : Fin R =>
          (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card := by
      have h1 : (univ.filter (fun s : Fin R2 => recvIdx s (sendIdx s u) idx = u idx)).card =
          (univ.filter (fun p : Seed2 =>
            (!(recv p.1 (send p.1 (aOf p.2 u)) (zOf p.2 idx))) = u idx)).card := by
        refine card_bij (fun s _ => eSeed2 s) ?_ ?_ ?_
        · intro s hs; exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hs).2⟩
        · intro s1 _ s2 _ h; exact eSeed2.injective h
        · intro p hp
          refine ⟨eSeed2.symm p, mem_filter.2 ⟨mem_univ _, ?_⟩, by simp⟩
          dsimp only [recvIdx, sendIdx]
          simpa only [Equiv.apply_symm_apply] using (mem_filter.1 hp).2
      rw [h1]
      simp only [card_filter]
      rw [Fintype.sum_prod_type_right]
    rw [hcount_prod]
    have hsum_ge : 2 * R * goodCol.card ≤
        3 * ∑ C : Fin q → Col, (univ.filter (fun sd : Fin R =>
          (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card := by
      calc 2 * R * goodCol.card = ∑ _C ∈ goodCol, (2 * R) := by
            rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ C ∈ goodCol, 3 * (univ.filter (fun sd : Fin R =>
              (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card :=
            sum_le_sum fun C hC => hpair_good C hC
        _ = 3 * ∑ C ∈ goodCol, (univ.filter (fun sd : Fin R =>
              (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card := by rw [← mul_sum]
        _ ≤ 3 * ∑ C : Fin q → Col, (univ.filter (fun sd : Fin R =>
              (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card :=
            Nat.mul_le_mul_left 3 (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _))
    have hR2_eq : R2 = R * (Fintype.card Col) ^ q := by
      simp only [R2, Seed2, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    rw [hR2_eq]
    set S_tot := ∑ C : Fin q → Col, (univ.filter (fun sd : Fin R =>
      (!(recv sd (send sd (aOf C u)) (zOf C idx))) = u idx)).card
    have hmul1 : 2 * R * (143 * (Fintype.card Col) ^ q) ≤ 2 * R * (144 * goodCol.card) :=
      Nat.mul_le_mul_left (2 * R) hcheb
    have hmul2 : 144 * (2 * R * goodCol.card) ≤ 144 * (3 * S_tot) :=
      Nat.mul_le_mul_left 144 hsum_ge
    have h286 : 286 * (R * (Fintype.card Col) ^ q) ≤ 432 * S_tot :=
      calc 286 * (R * (Fintype.card Col) ^ q)
          = 2 * R * (143 * (Fintype.card Col) ^ q) := by ring
        _ ≤ 2 * R * (144 * goodCol.card) := hmul1
        _ = 144 * (2 * R * goodCol.card) := by ring
        _ ≤ 144 * (3 * S_tot) := hmul2
        _ = 432 * S_tot := by ring
    omega
  have hN_le : N ≤ 50 * b + 500 := index_lb hN_pos hR2pos sendIdx recvIdx hidx_good
  have hN_le_b : N ≤ 550 * b := by omega
  have hq_le_m : q ≤ m := min_le_left _ _
  have hmax_le : max q (g * g) ≤ max m (g * g) := max_le_max hq_le_m le_rfl
  have hm2 : m * m ≤ 512 * 512 * (q * q) := by
    calc m * m ≤ (512 * q) * (512 * q) := Nat.mul_le_mul hm_le_512q hm_le_512q
      _ = 512 * 512 * (q * q) := by ring
  have hq2_b : q * q ≤ 40000 * (550 * b) * max m (g * g) := by
    calc q * q ≤ 40000 * N * max q (g * g) := hq2_le_N
      _ ≤ 40000 * (550 * b) * max m (g * g) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 40000 hN_le_b) hmax_le
  have hconst : 512 * 512 * (40000 * 550) ≤ 10 ^ 13 := by norm_num
  calc m * m ≤ 512 * 512 * (40000 * (550 * b) * max m (g * g)) :=
        hm2.trans (Nat.mul_le_mul_left _ hq2_b)
    _ = (512 * 512 * (40000 * 550)) * b * max m (g * g) := by ring
    _ ≤ 10 ^ 13 * b * max m (g * g) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hconst)

end SplitPairLB

section CompletePairLB

lemma b_pos_of_large_cross {n r g b : ℕ} (hg : 0 < g) (hKg : 16384 * g ≤ n)
    (hr : 0 < r) (hnr : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hov : ∀ j l : Fin r, j ≠ l →
      128 * (univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (S : Finset (Bool × Fin n))
    (hcross : n ≤ 4 * (univ.filter (fun i : Fin n =>
      ¬ ((false, i) ∈ S ↔ (true, M ⟨0, hr⟩ i) ∈ S))).card)
    (hcost : ∃ R : ℕ, 0 < R ∧
      ∃ (send : Fin R → ({v : Bool × Fin n // v ∈ S} → Bool) → Fin (2 ^ b))
        (recv : Fin R → Fin (2 ^ b) → ({v : Bool × Fin n // v ∉ S} → Bool) → Bool),
        ∀ (a : {v : Bool × Fin n // v ∈ S} → Bool) (z : {v : Bool × Fin n // v ∉ S} → Bool),
          let x := fun v : Bool × Fin n => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
          let D := fun j : Fin r => (univ.filter (fun i : Fin n =>
            x (false, i) ≠ x (true, M j i))).card
          let yes := ∀ j : Fin r, 15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n
          let no := ∃ j : Fin r, 32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j
          let good := fun seed : Fin R => (yes → recv seed (send seed a) z = true) ∧
            (no → recv seed (send seed a) z = false)
          2 * R ≤ 3 * (univ.filter (fun seed : Fin R => good seed)).card) :
    1 ≤ b := by
  classical
  by_contra hb0
  have hbe : b = 0 := by omega
  subst hbe
  obtain ⟨R, hRpos, send, recv, hproto⟩ := hcost
  let j0 : Fin r := ⟨0, hr⟩
  set E0 := univ.filter (fun i : Fin n => ¬ ((false, i) ∈ S ↔ (true, M j0 i) ∈ S))
  have hn_gt : 8192 < n := by
    have : 8192 ≤ 8192 * r := Nat.le_mul_of_pos_right 8192 hr
    omega
  set q := n / 256
  have hq_le : q ≤ E0.card := by omega
  obtain ⟨R0, hR0_sub, hR0_card⟩ := exists_subset_card_eq hq_le
  set target := (15 * n) / 32 - 2 * g
  have htar_le : target ≤ n - R0.card := by rw [hR0_card]; dsimp only [target, q]; omega
  obtain ⟨x0, hx0_tar, hx0_pin⟩ := pinning_lemma (g := g) hr hnr (by omega) M hov j0 R0
    (by rw [hR0_card]; dsimp only [q]; exact Nat.mul_div_le n 256) target htar_le
  let z0 : {v : Bool × Fin n // v ∉ S} → Bool := fun v => x0 v.1
  let isR0End : Bool × Fin n → Prop := fun v =>
    ∃ i ∈ R0, v = (false, i) ∨ v = (true, M j0 i)
  let a0 : {v : Bool × Fin n // v ∈ S} → Bool := fun v =>
    if h : ∃ i ∈ R0, v.1 = (false, i) ∨ v.1 = (true, M j0 i) then
      let i := h.choose
      if v.1 = (false, i) then x0 (true, M j0 i) else x0 (false, i)
    else x0 v.1
  let a1 : {v : Bool × Fin n // v ∈ S} → Bool := fun v =>
    if h : ∃ i ∈ R0, v.1 = (false, i) ∨ v.1 = (true, M j0 i) then
      !(a0 v)
    else x0 v.1
  have hmatch0 : ∀ i ∈ R0,
      (if h : (false, i) ∈ S then a0 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) =
      (if h : (true, M j0 i) ∈ S then a0 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩) := by
    intro i hi
    have hsp := (mem_filter.1 (hR0_sub hi)).2
    have hexF : ∃ i' ∈ R0, (false, i) = (false, i') ∨ (false, i) = (true, M j0 i') :=
      ⟨i, hi, Or.inl rfl⟩
    have hexT : ∃ i' ∈ R0, (true, M j0 i) = (false, i') ∨ (true, M j0 i) = (true, M j0 i') :=
      ⟨i, hi, Or.inr rfl⟩
    have hcF : hexF.choose = i := by
      rcases hexF.choose_spec.2 with h1 | h2
      · exact (congrArg Prod.snd h1).symm
      · simp at h2
    have hcT : hexT.choose = i := by
      rcases hexT.choose_spec.2 with h1 | h2
      · simp at h1
      · exact ((M j0).injective (congrArg Prod.snd h2)).symm
    by_cases hF : (false, i) ∈ S
    · have hT : (true, M j0 i) ∉ S := by tauto
      simp only [dif_pos hF, dif_neg hT, a0, z0, dif_pos hexF, hcF, ↓reduceIte]
    · have hT : (true, M j0 i) ∈ S := by tauto
      have hne : (true, M j0 i) ≠ (false, i) := by simp
      simp only [dif_neg hF, dif_pos hT, a0, z0, dif_pos hexT, hcT, if_neg hne]
  have hmatch1 : ∀ i ∈ R0,
      (if h : (false, i) ∈ S then a1 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
      (if h : (true, M j0 i) ∈ S then a1 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩) := by
    intro i hi
    have hsp := (mem_filter.1 (hR0_sub hi)).2
    have hexF : ∃ i' ∈ R0, (false, i) = (false, i') ∨ (false, i) = (true, M j0 i') :=
      ⟨i, hi, Or.inl rfl⟩
    have hexT : ∃ i' ∈ R0, (true, M j0 i) = (false, i') ∨ (true, M j0 i) = (true, M j0 i') :=
      ⟨i, hi, Or.inr rfl⟩
    have hm := hmatch0 i hi
    by_cases hF : (false, i) ∈ S
    · have hT : (true, M j0 i) ∉ S := by tauto
      simp only [dif_pos hF, dif_neg hT] at hm ⊢
      simp only [a1, dif_pos hexF, hm]; cases z0 ⟨(true, M j0 i), hT⟩ <;> decide
    · have hT : (true, M j0 i) ∈ S := by tauto
      simp only [dif_neg hF, dif_pos hT] at hm ⊢
      simp only [a1, dif_pos hexT, ← hm]; cases z0 ⟨(false, i), hF⟩ <;> decide
  have hout0 : ∀ i : Fin n, i ∉ R0 →
      (if h : (false, i) ∈ S then a0 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) = x0 (false, i) ∧
      (if h : (true, M j0 i) ∈ S then a0 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩) = x0 (true, M j0 i) := by
    intro i hi
    have hnotF : ¬ ∃ i' ∈ R0, (false, i) = (false, i') ∨ (false, i) = (true, M j0 i') := by
      rintro ⟨i', hi', h1 | h2⟩
      · exact hi ((Prod.mk.inj h1).2 ▸ hi')
      · simp at h2
    have hnotT : ¬ ∃ i' ∈ R0, (true, M j0 i) = (false, i') ∨ (true, M j0 i) = (true, M j0 i') := by
      rintro ⟨i', hi', h1 | h2⟩
      · simp at h1
      · exact hi (((M j0).injective (Prod.mk.inj h2).2) ▸ hi')
    constructor
    · by_cases hv : (false, i) ∈ S
      · rw [dif_pos hv]; dsimp only [a0]; rw [dif_neg hnotF]
      · rw [dif_neg hv]
    · by_cases hv : (true, M j0 i) ∈ S
      · rw [dif_pos hv]; dsimp only [a0]; rw [dif_neg hnotT]
      · rw [dif_neg hv]
  have hout1 : ∀ i : Fin n, i ∉ R0 →
      (if h : (false, i) ∈ S then a1 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) = x0 (false, i) ∧
      (if h : (true, M j0 i) ∈ S then a1 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩) = x0 (true, M j0 i) := by
    intro i hi
    have hnotF : ¬ ∃ i' ∈ R0, (false, i) = (false, i') ∨ (false, i) = (true, M j0 i') := by
      rintro ⟨i', hi', h1 | h2⟩
      · exact hi ((Prod.mk.inj h1).2 ▸ hi')
      · simp at h2
    have hnotT : ¬ ∃ i' ∈ R0, (true, M j0 i) = (false, i') ∨ (true, M j0 i) = (true, M j0 i') := by
      rintro ⟨i', hi', h1 | h2⟩
      · simp at h1
      · exact hi (((M j0).injective (Prod.mk.inj h2).2) ▸ hi')
    constructor
    · by_cases hv : (false, i) ∈ S
      · rw [dif_pos hv]; dsimp only [a1]; rw [dif_neg hnotF]
      · rw [dif_neg hv]
    · by_cases hv : (true, M j0 i) ∈ S
      · rw [dif_pos hv]; dsimp only [a1]; rw [dif_neg hnotT]
      · rw [dif_neg hv]
  have hD0 : (univ.filter (fun i : Fin n =>
      (if h : (false, i) ∈ S then a0 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
      (if h : (true, M j0 i) ∈ S then a0 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩))).card = target := by
    rw [← hx0_tar]
    congr 1; ext i
    by_cases hi : i ∈ R0
    · simp [hi, hmatch0 i hi]
    · simp [hi, (hout0 i hi).1, (hout0 i hi).2]
  have hD1 : (univ.filter (fun i : Fin n =>
      (if h : (false, i) ∈ S then a1 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
      (if h : (true, M j0 i) ∈ S then a1 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩))).card = target + q := by
    have hpart : univ.filter (fun i : Fin n =>
        (if h : (false, i) ∈ S then a1 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
        (if h : (true, M j0 i) ∈ S then a1 ⟨(true, M j0 i), h⟩ else z0 ⟨(true, M j0 i), h⟩)) =
        ((univ \ R0).filter (fun i : Fin n => x0 (false, i) ≠ x0 (true, M j0 i))) ∪ R0 := by
      ext i
      by_cases hi : i ∈ R0
      · simp [hi, hmatch1 i hi]
      · simp [hi, (hout1 i hi).1, (hout1 i hi).2]
    rw [hpart, card_union_of_disjoint (disjoint_sdiff_self_left.mono_left (filter_subset _ _)),
      hx0_tar, hR0_card]
  have hp0 := hproto a0 z0
  have hp1 := hproto a1 z0
  dsimp only at hp0 hp1
  have hno0 : ∃ j : Fin r,
      32 * (univ.filter (fun i : Fin n =>
        (if h : (false, i) ∈ S then a0 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
        (if h : (true, M j i) ∈ S then a0 ⟨(true, M j i), h⟩ else z0 ⟨(true, M j i), h⟩))).card + 32 * g ≤ 15 * n ∨
      17 * n + 32 * g ≤ 32 * (univ.filter (fun i : Fin n =>
        (if h : (false, i) ∈ S then a0 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
        (if h : (true, M j i) ∈ S then a0 ⟨(true, M j i), h⟩ else z0 ⟨(true, M j i), h⟩))).card := by
    refine ⟨j0, Or.inl ?_⟩
    rw [hD0]; dsimp only [target]; omega
  have hyes1 : ∀ j : Fin r,
      15 * n + 32 * g ≤ 32 * (univ.filter (fun i : Fin n =>
        (if h : (false, i) ∈ S then a1 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
        (if h : (true, M j i) ∈ S then a1 ⟨(true, M j i), h⟩ else z0 ⟨(true, M j i), h⟩))).card ∧
      32 * (univ.filter (fun i : Fin n =>
        (if h : (false, i) ∈ S then a1 ⟨(false, i), h⟩ else z0 ⟨(false, i), h⟩) ≠
        (if h : (true, M j i) ∈ S then a1 ⟨(true, M j i), h⟩ else z0 ⟨(true, M j i), h⟩))).card + 32 * g ≤ 17 * n := by
    intro j
    by_cases hj : j = j0
    · subst hj; rw [hD1]; dsimp only [target, q]; omega
    · exact hx0_pin j hj (fun v => if h : v ∈ S then a1 ⟨v, h⟩ else z0 ⟨v, h⟩) hout1
  have hdisj : Disjoint
      (univ.filter (fun sd : Fin R => recv sd 0 z0 = false))
      (univ.filter (fun sd : Fin R => recv sd 0 z0 = true)) :=
    disjoint_filter.2 fun sd _ h1 h2 => by rw [h1] at h2; exact Bool.noConfusion h2
  have hle0 : 2 * R ≤ 3 * (univ.filter (fun sd : Fin R => recv sd 0 z0 = false)).card := by
    refine hp0.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
    have h := (mem_filter.1 hsd).2.2 hno0
    have h0 : send sd a0 = 0 := Fin.ext (by have := (send sd a0).isLt; omega)
    rw [h0] at h
    exact mem_filter.2 ⟨mem_univ _, h⟩
  have hle1 : 2 * R ≤ 3 * (univ.filter (fun sd : Fin R => recv sd 0 z0 = true)).card := by
    refine hp1.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
    have h := (mem_filter.1 hsd).2.1 hyes1
    have h0 : send sd a1 = 0 := Fin.ext (by have := (send sd a1).isLt; omega)
    rw [h0] at h
    exact mem_filter.2 ⟨mem_univ _, h⟩
  have hsum : (univ.filter (fun sd : Fin R => recv sd 0 z0 = false)).card +
      (univ.filter (fun sd : Fin R => recv sd 0 z0 = true)).card ≤ R := by
    rw [← card_union_of_disjoint hdisj]
    exact (card_le_univ _).trans (by simp)
  omega

lemma gt_reduction_small_cross {n r g b : ℕ} (hg : 0 < g) (hKg : 16384 * g ≤ n)
    (hr : 0 < r) (hnr : 8192 * r < n)
    (M : Fin r → Equiv.Perm (Fin n))
    (hov : ∀ j l : Fin r, j ≠ l →
      128 * (univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n)
    (S : Finset (Bool × Fin n))
    (hS1 : n ≤ 2 * S.card) (hS2 : 2 * S.card ≤ 3 * n)
    (hcross : 4 * (univ.filter (fun i : Fin n =>
      ¬ ((false, i) ∈ S ↔ (true, M ⟨0, hr⟩ i) ∈ S))).card < n)
    (hcost : ∃ R : ℕ, 0 < R ∧
      ∃ (send : Fin R → ({v : Bool × Fin n // v ∈ S} → Bool) → Fin (2 ^ b))
        (recv : Fin R → Fin (2 ^ b) → ({v : Bool × Fin n // v ∉ S} → Bool) → Bool),
        ∀ (a : {v : Bool × Fin n // v ∈ S} → Bool) (z : {v : Bool × Fin n // v ∉ S} → Bool),
          let x := fun v : Bool × Fin n => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
          let D := fun j : Fin r => (univ.filter (fun i : Fin n =>
            x (false, i) ≠ x (true, M j i))).card
          let yes := ∀ j : Fin r, 15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n
          let no := ∃ j : Fin r, 32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j
          let good := fun seed : Fin R => (yes → recv seed (send seed a) z = true) ∧
            (no → recv seed (send seed a) z = false)
          2 * R ≤ 3 * (univ.filter (fun seed : Fin R => good seed)).card) :
    Nat.clog 2 (n / g + 1) ≤ 10 ^ 5 * b := by
  classical
  let j0 : Fin r := ⟨0, hr⟩
  set A0 := univ.filter (fun i : Fin n => (false, i) ∈ S ∧ (true, M j0 i) ∈ S)
  set B0 := univ.filter (fun i : Fin n => (false, i) ∉ S ∧ (true, M j0 i) ∉ S)
  set E0 := univ.filter (fun i : Fin n => ¬ ((false, i) ∈ S ↔ (true, M j0 i) ∈ S))
  have hS_cnt : 2 * A0.card + E0.card = S.card := by
    have hbij : S.card = (univ.filter (fun i : Fin n => (false, i) ∈ S)).card +
        (univ.filter (fun i : Fin n => (true, M j0 i) ∈ S)).card := by
      have hsplit : S = S.filter (fun v => v.1 = false) ∪ S.filter (fun v => v.1 = true) := by
        ext ⟨b, i⟩; cases b <;> simp
      have hdisj : Disjoint (S.filter (fun v => v.1 = false)) (S.filter (fun v => v.1 = true)) :=
        disjoint_filter.2 fun v _ h1 h2 => by rw [h1] at h2; exact Bool.noConfusion h2
      have h1 : (S.filter (fun v => v.1 = false)).card =
          (univ.filter (fun i : Fin n => (false, i) ∈ S)).card := by
        refine card_bij (fun v _ => v.2) ?_ ?_ ?_
        · intro ⟨b, i⟩ hv; obtain ⟨hv1, rfl⟩ := mem_filter.1 hv; exact mem_filter.2 ⟨mem_univ _, hv1⟩
        · intro ⟨b1, i1⟩ h1 ⟨b2, i2⟩ h2 h
          obtain ⟨_, rfl⟩ := mem_filter.1 h1; obtain ⟨_, rfl⟩ := mem_filter.1 h2; exact Prod.ext rfl h
        · intro i hi; exact ⟨(false, i), mem_filter.2 ⟨(mem_filter.1 hi).2, rfl⟩, rfl⟩
      have h2 : (S.filter (fun v => v.1 = true)).card =
          (univ.filter (fun i : Fin n => (true, M j0 i) ∈ S)).card := by
        refine card_bij (fun v _ => (M j0).symm v.2) ?_ ?_ ?_
        · intro ⟨b, i⟩ hv; obtain ⟨hv1, rfl⟩ := mem_filter.1 hv
          exact mem_filter.2 ⟨mem_univ _, by simpa using hv1⟩
        · intro ⟨b1, i1⟩ h1 ⟨b2, i2⟩ h2 h
          obtain ⟨_, rfl⟩ := mem_filter.1 h1; obtain ⟨_, rfl⟩ := mem_filter.1 h2
          exact Prod.ext rfl ((M j0).symm.injective h)
        · intro i hi; exact ⟨(true, M j0 i), mem_filter.2 ⟨(mem_filter.1 hi).2, rfl⟩, by simp⟩
      calc S.card = (S.filter (fun v => v.1 = false) ∪ S.filter (fun v => v.1 = true)).card :=
            congrArg card hsplit
        _ = (S.filter (fun v => v.1 = false)).card + (S.filter (fun v => v.1 = true)).card :=
            card_union_of_disjoint hdisj
        _ = _ := by rw [h1, h2]
    rw [hbij]
    have hsum_id : ∀ i : Fin n,
        (if (false, i) ∈ S then 1 else 0) + (if (true, M j0 i) ∈ S then 1 else 0) =
        2 * (if (false, i) ∈ S ∧ (true, M j0 i) ∈ S then 1 else 0) +
        (if ¬ ((false, i) ∈ S ↔ (true, M j0 i) ∈ S) then 1 else 0) := by
      intro i
      by_cases h1 : (false, i) ∈ S <;> by_cases h2 : (true, M j0 i) ∈ S <;> simp [h1, h2]
    have hsum := sum_congr (s₁ := (univ : Finset (Fin n))) rfl fun i _ => hsum_id i
    simp only [sum_add_distrib, ← mul_sum, sum_boole, Nat.cast_id] at hsum
    exact hsum.symm
  have hpart_n : A0.card + B0.card + E0.card = n := by
    have hsum_id : ∀ i : Fin n,
        (if (false, i) ∈ S ∧ (true, M j0 i) ∈ S then 1 else 0) +
        (if (false, i) ∉ S ∧ (true, M j0 i) ∉ S then 1 else 0) +
        (if ¬ ((false, i) ∈ S ↔ (true, M j0 i) ∈ S) then 1 else 0) = 1 := by
      intro i
      by_cases h1 : (false, i) ∈ S <;> by_cases h2 : (true, M j0 i) ∈ S <;> simp [h1, h2]
    have hsum := sum_congr (s₁ := (univ : Finset (Fin n))) rfl fun i _ => hsum_id i
    simp only [sum_add_distrib, sum_boole, Nat.cast_id, sum_const, card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum
    exact hsum
  have hA0_ge : n ≤ 8 * A0.card := by omega
  have hB0_ge : n ≤ 8 * B0.card := by omega
  set L := n / 512
  have hL_leA : L ≤ A0.card := by omega
  have hL_leB : L ≤ B0.card := by omega
  obtain ⟨RA, hRA_sub, hRA_card⟩ := exists_subset_card_eq hL_leA
  obtain ⟨RB, hRB_sub, hRB_card⟩ := exists_subset_card_eq hL_leB
  have hdisjAB : Disjoint RA RB := by
    rw [disjoint_left]
    intro i hiA hiB
    exact (mem_filter.1 (hRB_sub hiB)).2.1 (mem_filter.1 (hRA_sub hiA)).2.1
  set R0 := RA ∪ RB
  have hR0_card : R0.card = 2 * L := by
    rw [card_union_of_disjoint hdisjAB, hRA_card, hRB_card]; ring
  have hR0_256 : 256 * R0.card ≤ n := by rw [hR0_card]; dsimp only [L]; omega
  set step := 4 * g + 4
  have hstep_pos : 0 < step := by omega
  set Mnum := L / step
  have hMnum_ge : 2 ≤ Mnum := by
    have hstep_le : step ≤ 8 * g := by omega
    have hL_ge : 2 * (8 * g) ≤ L := by dsimp only [L]; omega
    exact (Nat.le_div_iff_mul_le hstep_pos).2 (by nlinarith)
  set d := Nat.log 2 Mnum
  have hd_pos : 0 < d := by
    have : 1 ≤ Nat.log 2 Mnum := Nat.le_log_of_pow_le one_lt_two (by simpa using hMnum_ge)
    omega
  have h2d_le_M : 2 ^ d ≤ Mnum := Nat.pow_log_le_self 2 (by omega)
  have hstep_2d : step * 2 ^ d ≤ L := by
    calc step * 2 ^ d ≤ step * Mnum := Nat.mul_le_mul_left step h2d_le_M
      _ ≤ L := Nat.mul_div_le L step
  have hclog_le_d : Nat.clog 2 (n / g + 1) ≤ 20 * d := by
    have hM_lt : L < step * (Mnum + 1) := Nat.lt_mul_div_succ L hstep_pos
    have h2d1 : Mnum < 2 ^ (d + 1) := Nat.lt_pow_succ_log_self one_lt_two Mnum
    have hstep_le : step ≤ 8 * g := by omega
    have hn_le : n ≤ 512 * L + 511 := by
      have := Nat.div_add_mod n 512
      have := Nat.mod_lt n (by norm_num : 0 < 512)
      omega
    have hng_le : n / g + 1 ≤ 2 ^ (d + 14) := by
      have h1 : g * (n / g) ≤ n := Nat.mul_div_le n g
      have h2 : Mnum + 1 ≤ 2 ^ (d + 1) := h2d1
      have h3 : L < 8 * g * 2 ^ (d + 1) :=
        lt_of_lt_of_le hM_lt (Nat.mul_le_mul hstep_le h2)
      have h4 : n < 512 * (8 * g * 2 ^ (d + 1)) + 512 := by omega
      have h5 : g * (n / g) < g * (4096 * 2 ^ (d + 1) + 512) := by
        calc g * (n / g) ≤ n := h1
          _ < 512 * (8 * g * 2 ^ (d + 1)) + 512 := h4
          _ ≤ 512 * (8 * g * 2 ^ (d + 1)) + 512 * g := by omega
          _ = g * (4096 * 2 ^ (d + 1) + 512) := by ring
      have h6 : n / g < 4096 * 2 ^ (d + 1) + 512 := Nat.lt_of_mul_lt_mul_left h5
      have h7 : 2 ^ (d + 14) = 8192 * 2 ^ (d + 1) := by rw [show d + 14 = d + 1 + 13 by omega, pow_add]; ring
      have h8 : 1 ≤ 2 ^ (d + 1) := Nat.one_le_pow _ _ two_pos
      omega
    have hcl := Nat.clog_le_of_le_pow hng_le
    omega
  set target := (15 * n) / 32 - 2 * g - step * (2 ^ d - 1)
  have htar_le : target ≤ n - R0.card := by rw [hR0_card]; omega
  obtain ⟨x0, hx0_tar, hx0_pin⟩ := pinning_lemma (g := g) hr hnr (by omega) M hov j0 R0 hR0_256 target htar_le
  have htar_sub : step * (2 ^ d - 1) + 2 * g ≤ (15 * n) / 32 := by
    have : step * (2 ^ d - 1) ≤ L := (Nat.mul_le_mul_left step (Nat.sub_le _ _)).trans hstep_2d
    dsimp only [L] at this; omega
  let eRA : Fin L ≃ {i : Fin n // i ∈ RA} :=
    ((RA.equivFin).trans (Equiv.cast (by rw [hRA_card]))).symm
  let eRB : Fin L ≃ {i : Fin n // i ∈ RB} :=
    ((RB.equivFin).trans (Equiv.cast (by rw [hRB_card]))).symm
  let aOf : Fin (2 ^ d) → ({v : Bool × Fin n // v ∈ S} → Bool) := fun X v =>
    if h : ∃ t : Fin L, v.1 = (false, (eRA t).1) then
      decide (h.choose.val < step * X.val)
    else if h2 : ∃ t : Fin L, v.1 = (true, M j0 (eRA t).1) then
      false
    else x0 v.1
  let zOf : Fin (2 ^ d) → ({v : Bool × Fin n // v ∉ S} → Bool) := fun Y v =>
    if h : ∃ t : Fin L, v.1 = (false, (eRB t).1) then
      decide (h.choose.val < step * (2 ^ d - 1 - Y.val))
    else if h2 : ∃ t : Fin L, v.1 = (true, M j0 (eRB t).1) then
      false
    else x0 v.1
  obtain ⟨R, hRpos, send, recv, hproto⟩ := hcost
  have hGT : ∀ (X Y : Fin (2 ^ d)),
      2 * R ≤ 3 * (univ.filter (fun sd : Fin R =>
        (Y.val < X.val → recv sd (send sd (aOf X)) (zOf Y) = true) ∧
        (X.val ≤ Y.val → recv sd (send sd (aOf X)) (zOf Y) = false))).card := by
    intro X Y
    set x := fun v : Bool × Fin n => if h : v ∈ S then aOf X ⟨v, h⟩ else zOf Y ⟨v, h⟩
    have hout : ∀ i : Fin n, i ∉ R0 →
        x (false, i) = x0 (false, i) ∧ x (true, M j0 i) = x0 (true, M j0 i) := by
      intro i hi
      have hniA : i ∉ RA := fun h => hi (mem_union_left _ h)
      have hniB : i ∉ RB := fun h => hi (mem_union_right _ h)
      have h1 : ¬ ∃ t : Fin L, (false, i) = (false, (eRA t).1) := by
        rintro ⟨t, he⟩; exact hniA ((Prod.mk.inj he).2 ▸ (eRA t).2)
      have h2 : ¬ ∃ t : Fin L, (false, i) = (true, M j0 (eRA t).1) := by rintro ⟨_, he⟩; simp at he
      have h3 : ¬ ∃ t : Fin L, (false, i) = (false, (eRB t).1) := by
        rintro ⟨t, he⟩; exact hniB ((Prod.mk.inj he).2 ▸ (eRB t).2)
      have h4 : ¬ ∃ t : Fin L, (false, i) = (true, M j0 (eRB t).1) := by rintro ⟨_, he⟩; simp at he
      have h5 : ¬ ∃ t : Fin L, (true, M j0 i) = (false, (eRA t).1) := by rintro ⟨_, he⟩; simp at he
      have h6 : ¬ ∃ t : Fin L, (true, M j0 i) = (true, M j0 (eRA t).1) := by
        rintro ⟨t, he⟩; exact hniA (((M j0).injective (Prod.mk.inj he).2) ▸ (eRA t).2)
      have h7 : ¬ ∃ t : Fin L, (true, M j0 i) = (false, (eRB t).1) := by rintro ⟨_, he⟩; simp at he
      have h8 : ¬ ∃ t : Fin L, (true, M j0 i) = (true, M j0 (eRB t).1) := by
        rintro ⟨t, he⟩; exact hniB (((M j0).injective (Prod.mk.inj he).2) ▸ (eRB t).2)
      constructor
      · by_cases hv : (false, i) ∈ S
        · dsimp only [x]; rw [dif_pos hv]; dsimp only [aOf]; rw [dif_neg h1, dif_neg h2]
        · dsimp only [x]; rw [dif_neg hv]; dsimp only [zOf]; rw [dif_neg h3, dif_neg h4]
      · by_cases hv : (true, M j0 i) ∈ S
        · dsimp only [x]; rw [dif_pos hv]; dsimp only [aOf]; rw [dif_neg h5, dif_neg h6]
        · dsimp only [x]; rw [dif_neg hv]; dsimp only [zOf]; rw [dif_neg h7, dif_neg h8]
    have hRA_cnt : (RA.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
        step * X.val := by
      have hbij : (RA.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
          (univ.filter (fun t : Fin L => t.val < step * X.val)).card := by
        refine card_bij (fun i hi => eRA.symm ⟨i, (mem_filter.1 hi).1⟩) ?_ ?_ ?_
        · intro i hi
          have hiA := (mem_filter.1 hi).1
          have hmemA := (mem_filter.1 (hRA_sub hiA)).2
          have hne := (mem_filter.1 hi).2
          set t := eRA.symm ⟨i, hiA⟩
          have ht_eq : (eRA t).1 = i := by simp [t]
          have hex1 : ∃ t' : Fin L, (false, i) = (false, (eRA t').1) := ⟨t, by rw [ht_eq]⟩
          have hch1 : hex1.choose = t := eRA.injective (Subtype.ext ((congrArg Prod.snd hex1.choose_spec).symm.trans ht_eq.symm))
          have hno1 : ¬ ∃ t' : Fin L, (true, M j0 i) = (false, (eRA t').1) := by rintro ⟨_, h⟩; simp at h
          have hex2 : ∃ t' : Fin L, (true, M j0 i) = (true, M j0 (eRA t').1) := ⟨t, by rw [ht_eq]⟩
          simp only [x, dif_pos hmemA.1, dif_pos hmemA.2, aOf, dif_pos hex1, dif_neg hno1,
            dif_pos hex2, hch1] at hne
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          by_contra hlt
          simp [hlt] at hne
        · intro i1 _ i2 _ h; exact congrArg Subtype.val (eRA.symm.injective h)
        · intro t ht
          have hmemA := (mem_filter.1 (hRA_sub (eRA t).2)).2
          have hex1 : ∃ t' : Fin L, (false, (eRA t).1) = (false, (eRA t').1) := ⟨t, rfl⟩
          have hch1 : hex1.choose = t := eRA.injective (Subtype.ext (congrArg Prod.snd hex1.choose_spec).symm)
          have hno1 : ¬ ∃ t' : Fin L, (true, M j0 (eRA t).1) = (false, (eRA t').1) := by rintro ⟨_, h⟩; simp at h
          have hex2 : ∃ t' : Fin L, (true, M j0 (eRA t).1) = (true, M j0 (eRA t').1) := ⟨t, rfl⟩
          refine ⟨(eRA t).1, mem_filter.2 ⟨(eRA t).2, ?_⟩, by simp⟩
          simp only [x, dif_pos hmemA.1, dif_pos hmemA.2, aOf, dif_pos hex1, dif_neg hno1,
            dif_pos hex2, hch1, decide_eq_true (mem_filter.1 ht).2]
          decide
      rw [hbij]
      have hleL : step * X.val ≤ L :=
        (Nat.mul_le_mul_left step X.isLt.le).trans hstep_2d
      have hcard_lt : (univ.filter (fun t : Fin L => t.val < step * X.val)).card = step * X.val := by
        have : (univ.filter (fun t : Fin L => t.val < step * X.val)).card = (range (step * X.val)).card := by
          refine card_bij (fun t _ => t.val) (fun t ht => mem_range.2 (mem_filter.1 ht).2)
            (fun _ _ _ _ h => Fin.ext h)
            (fun k hk => ⟨⟨k, lt_of_lt_of_le (mem_range.1 hk) hleL⟩,
              mem_filter.2 ⟨mem_univ _, mem_range.1 hk⟩, rfl⟩)
        rw [this, card_range]
      exact hcard_lt
    have hRB_cnt : (RB.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
        step * (2 ^ d - 1 - Y.val) := by
      have hbij : (RB.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
          (univ.filter (fun t : Fin L => t.val < step * (2 ^ d - 1 - Y.val))).card := by
        refine card_bij (fun i hi => eRB.symm ⟨i, (mem_filter.1 hi).1⟩) ?_ ?_ ?_
        · intro i hi
          have hiB := (mem_filter.1 hi).1
          have hmemB := (mem_filter.1 (hRB_sub hiB)).2
          have hne := (mem_filter.1 hi).2
          set t := eRB.symm ⟨i, hiB⟩
          have ht_eq : (eRB t).1 = i := by simp [t]
          have hex1 : ∃ t' : Fin L, (false, i) = (false, (eRB t').1) := ⟨t, by rw [ht_eq]⟩
          have hch1 : hex1.choose = t := eRB.injective (Subtype.ext ((congrArg Prod.snd hex1.choose_spec).symm.trans ht_eq.symm))
          have hno1 : ¬ ∃ t' : Fin L, (true, M j0 i) = (false, (eRB t').1) := by rintro ⟨_, h⟩; simp at h
          have hex2 : ∃ t' : Fin L, (true, M j0 i) = (true, M j0 (eRB t').1) := ⟨t, by rw [ht_eq]⟩
          simp only [x, dif_neg hmemB.1, dif_neg hmemB.2, zOf, dif_pos hex1, dif_neg hno1,
            dif_pos hex2, hch1] at hne
          rw [mem_filter]
          refine ⟨mem_univ _, ?_⟩
          by_contra hlt
          simp [hlt] at hne
        · intro i1 _ i2 _ h; exact congrArg Subtype.val (eRB.symm.injective h)
        · intro t ht
          have hmemB := (mem_filter.1 (hRB_sub (eRB t).2)).2
          have hex1 : ∃ t' : Fin L, (false, (eRB t).1) = (false, (eRB t').1) := ⟨t, rfl⟩
          have hch1 : hex1.choose = t := eRB.injective (Subtype.ext (congrArg Prod.snd hex1.choose_spec).symm)
          have hno1 : ¬ ∃ t' : Fin L, (true, M j0 (eRB t).1) = (false, (eRB t').1) := by rintro ⟨_, h⟩; simp at h
          have hex2 : ∃ t' : Fin L, (true, M j0 (eRB t).1) = (true, M j0 (eRB t').1) := ⟨t, rfl⟩
          refine ⟨(eRB t).1, mem_filter.2 ⟨(eRB t).2, ?_⟩, by simp⟩
          simp only [x, dif_neg hmemB.1, dif_neg hmemB.2, zOf, dif_pos hex1, dif_neg hno1,
            dif_pos hex2, hch1, decide_eq_true (mem_filter.1 ht).2]
          decide
      rw [hbij]
      have hleL : step * (2 ^ d - 1 - Y.val) ≤ L :=
        (Nat.mul_le_mul_left step (by omega)).trans hstep_2d
      have : (univ.filter (fun t : Fin L => t.val < step * (2 ^ d - 1 - Y.val))).card =
          (range (step * (2 ^ d - 1 - Y.val))).card := by
        refine card_bij (fun t _ => t.val) (fun t ht => mem_range.2 (mem_filter.1 ht).2)
          (fun _ _ _ _ h => Fin.ext h)
          (fun k hk => ⟨⟨k, lt_of_lt_of_le (mem_range.1 hk) hleL⟩,
            mem_filter.2 ⟨mem_univ _, mem_range.1 hk⟩, rfl⟩)
      rw [this, card_range]
    have hDj0 : (univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card =
        target + step * X.val + step * (2 ^ d - 1 - Y.val) := by
      have hpart : univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)) =
          ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) ∪
          (RA.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)) ∪
           RB.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) := by
        ext i; simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and, R0]; tauto
      have hdisj1 : Disjoint
          ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)))
          (RA.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i)) ∪
           RB.filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))) := by
        refine disjoint_union_right.2 ⟨?_, ?_⟩
        · exact disjoint_filter_filter (disjoint_sdiff_self_left.mono_right subset_union_left)
        · exact disjoint_filter_filter (disjoint_sdiff_self_left.mono_right subset_union_right)
      have hU : ((univ \ R0).filter (fun i : Fin n => x (false, i) ≠ x (true, M j0 i))).card = target := by
        rw [← hx0_tar]
        congr 1; ext i
        by_cases hi : i ∈ R0
        · simp [hi]
        · simp [hi, (hout i hi).1, (hout i hi).2]
      rw [hpart, card_union_of_disjoint hdisj1,
        card_union_of_disjoint (disjoint_filter_filter hdisjAB), hU, hRA_cnt, hRB_cnt, add_assoc]
    have hpr := hproto (aOf X) (zOf Y)
    dsimp only at hpr
    refine hpr.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
    have ⟨h1, h2⟩ := (mem_filter.1 hsd).2
    refine mem_filter.2 ⟨mem_univ _, fun hlt => h1 ?_, fun hle => h2 ?_⟩
    · intro j
      by_cases hj : j = j0
      · subst hj
        rw [hDj0]
        have hstep_sum : step * X.val + step * (2 ^ d - 1 - Y.val) =
            step * (2 ^ d - 1 + X.val - Y.val) := by
          rw [← mul_add]; congr 1; have := Y.isLt; omega
        have hgt_sum : step * (2 ^ d - 1) + step ≤ step * X.val + step * (2 ^ d - 1 - Y.val) := by
          rw [hstep_sum]
          have hmul1 : step * (2 ^ d - 1) + step = step * (2 ^ d - 1 + 1) := by ring
          rw [hmul1]
          exact Nat.mul_le_mul_left step (by have := Y.isLt; omega)
        have hle_2L : step * X.val + step * (2 ^ d - 1 - Y.val) ≤ 2 * L := by
          have h1L : step * X.val ≤ L := (Nat.mul_le_mul_left step X.isLt.le).trans hstep_2d
          have h2L : step * (2 ^ d - 1 - Y.val) ≤ L :=
            (Nat.mul_le_mul_left step (by omega)).trans hstep_2d
          omega
        dsimp only [target, step, L] at htar_sub hgt_sum hle_2L ⊢
        omega
      · exact hx0_pin j hj x hout
    · refine ⟨j0, Or.inl ?_⟩
      rw [hDj0]
      have hle_sum : step * X.val + step * (2 ^ d - 1 - Y.val) ≤ step * (2 ^ d - 1) := by
        rw [← mul_add]
        exact Nat.mul_le_mul_left step (by have := Y.isLt; omega)
      dsimp only [target] at htar_sub ⊢
      omega
  have hd_le := gt_lb hd_pos hRpos (fun s X => send s (aOf X)) (fun s m Y => recv s m (zOf Y)) hGT
  by_cases hb0 : b = 0
  · subst hb0
    have htriv : Nat.clog 2 (n / g + 1) ≤ 10 ^ 5 * 0 := by
      have hgt0 := hGT ⟨0, Nat.pow_pos two_pos⟩ ⟨0, Nat.pow_pos two_pos⟩
      have hgt1 := hGT ⟨1, by have : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2; omega⟩
        ⟨0, Nat.pow_pos two_pos⟩
      have hdisj : Disjoint
          (univ.filter (fun sd : Fin R => recv sd 0 (zOf ⟨0, Nat.pow_pos two_pos⟩) = false))
          (univ.filter (fun sd : Fin R => recv sd 0 (zOf ⟨0, Nat.pow_pos two_pos⟩) = true)) :=
        disjoint_filter.2 fun sd _ h1 h2 => by rw [h1] at h2; exact Bool.noConfusion h2
      have h0 : 2 * R ≤ 3 * (univ.filter (fun sd : Fin R =>
          recv sd 0 (zOf ⟨0, Nat.pow_pos two_pos⟩) = false)).card := by
        refine hgt0.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
        have h := (mem_filter.1 hsd).2.2 le_rfl
        have hs0 : send sd (aOf ⟨0, Nat.pow_pos two_pos⟩) = 0 := Fin.ext (by have := (send sd (aOf ⟨0, Nat.pow_pos two_pos⟩)).isLt; omega)
        rw [hs0] at h
        exact mem_filter.2 ⟨mem_univ _, h⟩
      have h1 : 2 * R ≤ 3 * (univ.filter (fun sd : Fin R =>
          recv sd 0 (zOf ⟨0, Nat.pow_pos two_pos⟩) = true)).card := by
        refine hgt1.trans (Nat.mul_le_mul_left 3 (card_le_card fun sd hsd => ?_))
        have h := (mem_filter.1 hsd).2.1 zero_lt_one
        have hs0 : send sd (aOf ⟨1, by have : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2; omega⟩) = 0 :=
          Fin.ext (by have := (send sd (aOf ⟨1, by have : 2 ≤ 2 ^ d := Nat.le_self_pow (by omega) 2; omega⟩)).isLt; omega)
        rw [hs0] at h
        exact mem_filter.2 ⟨mem_univ _, h⟩
      have hsum : (univ.filter (fun sd : Fin R =>
          recv sd 0 (zOf ⟨0, Nat.pow_pos two_pos⟩) = false)).card +
          (univ.filter (fun sd : Fin R =>
            recv sd 0 (zOf ⟨0, Nat.pow_pos two_pos⟩) = true)).card ≤ R := by
        rw [← card_union_of_disjoint hdisj]
        exact (card_le_univ _).trans (by simp)
      omega
    exact htriv
  omega

end CompletePairLB

lemma main_334 : (∃ C K : ℕ, 0 < C ∧ 0 < K ∧ ∀ (n r g : ℕ), 0 < g →
    ∀ M : Fin r → Equiv.Perm (Fin n),
      let V := Bool × Fin n
      ∀ S : Finset V,
        let A := {v : V // v ∈ S} → Bool
        let B := {v : V // v ∉ S} → Bool
        let cross := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
          ¬ ((false, i) ∈ S ↔ (true, M j i) ∈ S))).card
        let cost := fun b : ℕ => ∃ R : ℕ, 0 < R ∧
          ∃ (send : Fin R → A → Fin (2 ^ b)) (recv : Fin R → Fin (2 ^ b) → B → Bool),
            ∀ (a : A) (z : B),
              let x := fun v : V => if h : v ∈ S then a ⟨v, h⟩ else z ⟨v, h⟩
              let D := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
                x (false, i) ≠ x (true, M j i))).card
              let yes := ∀ j : Fin r, 15 * n + 32 * g ≤ 32 * D j ∧ 32 * D j + 32 * g ≤ 17 * n
              let no := ∃ j : Fin r, 32 * D j + 32 * g ≤ 15 * n ∨ 17 * n + 32 * g ≤ 32 * D j
              let good := fun seed : Fin R => (yes → recv seed (send seed a) z = true) ∧
                (no → recv seed (send seed a) z = false)
              2 * R ≤ 3 * (Finset.univ.filter (fun seed : Fin R => good seed)).card
        (∃ b : ℕ, cost b ∧ b ≤ C * (r * (1 + Nat.clog 2 (n / g + 1)) +
          ∑ j : Fin r, min (cross j)
            ((1 + (cross j) * (cross j) / (g * g)) * (1 + Nat.clog 2 (r + 1))))) ∧
        (K * g ≤ n → 0 < r → 8192 * r < n →
          (∀ j l : Fin r, j ≠ l →
            128 * (Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
          n ≤ 2 * S.card → 2 * S.card ≤ 3 * n →
          let m := Finset.univ.sup cross
          ∀ b : ℕ, cost b → Nat.clog 2 (n / g + 1) ≤ C * b ∧ m * m ≤ C * b * max m (g * g))) := by
  refine ⟨10 ^ 16, 16384, by norm_num, by norm_num, ?_⟩
  intro n r g hg M V S A B cross cost
  constructor
  · obtain ⟨b, hcb, hble⟩ := upper_bound n r g hg M S
    refine ⟨b, hcb, hble.trans (Nat.mul_le_mul_right _ (by norm_num))⟩
  · intro hKg hr hnr hov hS1 hS2 m b hcb
    by_cases hcr : n ≤ 4 * cross ⟨0, hr⟩
    · have hbPos : 1 ≤ b := b_pos_of_large_cross hg hKg hr hnr M hov S hcr hcb
      have hm2 : m * m ≤ 10 ^ 13 * b * max m (g * g) :=
        split_pair_lb hg hKg hr hnr M hov S hbPos hcb
      have hm_ge : n ≤ 4 * m := hcr.trans (Nat.mul_le_mul_left 4 (le_sup (f := cross) (mem_univ (⟨0, hr⟩ : Fin r))))
      have hclog_le : Nat.clog 2 (n / g + 1) ≤ 10 ^ 16 * b := by
        have hcl_lin : Nat.clog 2 (n / g + 1) ≤ n / g + 1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
        have hng_pos : 1 ≤ n / g := (Nat.le_div_iff_mul_le hg).2 (by omega)
        have hcl_2ng : Nat.clog 2 (n / g + 1) ≤ 2 * (n / g) := by omega
        rcases le_total m (g * g) with hle | hle
        · rw [max_eq_right hle] at hm2
          have h1 : (n / g) * (n / g) * (g * g) ≤ n * n := by
            have := Nat.div_mul_le_self n g
            calc (n / g) * (n / g) * (g * g) = (n / g * g) * (n / g * g) := by ring
              _ ≤ n * n := Nat.mul_le_mul this this
          have h2 : n * n ≤ 16 * (m * m) := by
            calc n * n ≤ (4 * m) * (4 * m) := Nat.mul_le_mul hm_ge hm_ge
              _ = 16 * (m * m) := by ring
          have h3 : (n / g) * (n / g) * (g * g) ≤ (16 * 10 ^ 13 * b) * (g * g) := by
            calc (n / g) * (n / g) * (g * g) ≤ 16 * (m * m) := h1.trans h2
              _ ≤ 16 * (10 ^ 13 * b * (g * g)) := Nat.mul_le_mul_left 16 hm2
              _ = (16 * 10 ^ 13 * b) * (g * g) := by ring
          have h4 : (n / g) * (n / g) ≤ 16 * 10 ^ 13 * b :=
            Nat.le_of_mul_le_mul_right h3 (Nat.mul_pos hg hg)
          have h5 : n / g ≤ (n / g) * (n / g) := Nat.le_mul_self (n / g)
          omega
        · rw [max_eq_left hle] at hm2
          have hm_pos : 0 < m := by omega
          have hm_le_b : m ≤ 10 ^ 13 * b :=
            Nat.le_of_mul_le_mul_right hm2 hm_pos
          have hng_le_n : n / g ≤ n := Nat.div_le_self n g
          omega
      exact ⟨hclog_le, hm2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))⟩
    · have hcr_lt : 4 * cross ⟨0, hr⟩ < n := lt_of_not_ge hcr
      have hclog : Nat.clog 2 (n / g + 1) ≤ 10 ^ 5 * b :=
        gt_reduction_small_cross hg hKg hr hnr M hov S hS1 hS2 hcr_lt hcb
      have hbPos : 1 ≤ b := by
        have hcl_ge : 1 ≤ Nat.clog 2 (n / g + 1) := by
          have : 1 < n / g + 1 := by
            have : 1 ≤ n / g := (Nat.le_div_iff_mul_le hg).2 (by omega)
            omega
          exact Nat.clog_pos one_lt_two this
        omega
      have hm2 : m * m ≤ 10 ^ 13 * b * max m (g * g) :=
        split_pair_lb hg hKg hr hnr M hov S hbPos hcb
      exact ⟨hclog.trans (Nat.mul_le_mul_right _ (by norm_num)),
        hm2.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))⟩

end PEqualNP.Outside.L_pcx_334_aux

theorem PEqualNP.Outside.L_pcx_334 : (∃ C K : ℕ, 0 < C ∧ 0 < K ∧ ∀ (n r g : ℕ), 0 < g →
  ∀ M : Fin r → Equiv.Perm (Fin n),
    let V := Bool × Fin n
    ∀ S : Finset V,
      let A := {v : V // v ∈ S} → Bool
      let B := {v : V // v ∉ S} → Bool
      let cross := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
        ¬ ((false,i) ∈ S ↔ (true,M j i) ∈ S))).card
      let cost := fun b : ℕ => ∃ R : ℕ, 0 < R ∧
        ∃ (send : Fin R → A → Fin (2^b)) (recv : Fin R → Fin (2^b) → B → Bool),
          ∀ (a : A) (z : B),
            let x := fun v : V => if h : v ∈ S then a ⟨v,h⟩ else z ⟨v,h⟩
            let D := fun j : Fin r => (Finset.univ.filter (fun i : Fin n =>
              x (false,i) ≠ x (true,M j i))).card
            let yes := ∀ j : Fin r, 15*n + 32*g ≤ 32*D j ∧ 32*D j + 32*g ≤ 17*n
            let no := ∃ j : Fin r, 32*D j + 32*g ≤ 15*n ∨ 17*n + 32*g ≤ 32*D j
            let good := fun seed : Fin R => (yes → recv seed (send seed a) z = true) ∧
              (no → recv seed (send seed a) z = false)
            2*R ≤ 3*(Finset.univ.filter (fun seed : Fin R => good seed)).card
      (∃ b : ℕ, cost b ∧ b ≤ C * (r*(1+Nat.clog 2 (n/g+1)) +
        ∑ j : Fin r, min (cross j)
          ((1+(cross j)*(cross j)/(g*g)) * (1+Nat.clog 2 (r+1))))) ∧
      (K*g ≤ n → 0 < r → 8192*r < n →
        (∀ j l : Fin r, j ≠ l →
          128*(Finset.univ.filter (fun i : Fin n => M j i = M l i)).card ≤ n) →
        n ≤ 2*S.card → 2*S.card ≤ 3*n →
        let m := Finset.univ.sup cross
        ∀ b : ℕ, cost b → Nat.clog 2 (n/g+1) ≤ C*b ∧ m*m ≤ C*b*max m (g*g))) :=
  PEqualNP.Outside.L_pcx_334_aux.main_334
