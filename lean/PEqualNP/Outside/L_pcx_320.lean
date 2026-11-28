import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_320
open Finset
def splitCount {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j : Fin 3)
    (S : Finset (Bool × Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, M j i) ∉ S))).card
def agreeCount {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j j' : Fin 3) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => M j i = M j' i)).card
abbrev acc {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (x : Bool × Fin n → Bool) : Prop :=
  ∀ j : Fin 3,
    16 * Nat.dist (2 * (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card) n ≤ n
def cutSet {n : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) : Finset (Bool × Fin n) :=
  (Finset.univ.filter (fun j : Fin (2*n) => j.val < n)).image order
abbrev ans {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (init : Fin R → Fin s)
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (out : Fin R → Fin s → Bool)
    (r : Fin R) (x : Bool × Fin n → Bool) : Bool :=
  out r ((List.finRange p).foldl (fun st pass =>
    (List.finRange (2*n)).foldl (fun z j => step r pass j z (x (order j))) st) (init r))
def inter {m : ℕ} (a b : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun k : Fin m => a k = true ∧ b k = true)).card
noncomputable def js {O : Type} [Fintype O] (P Q : O → ℝ) : ℝ :=
  ∑ o, (P o * Real.log (2 * P o / (P o + Q o)) + Q o * Real.log (2 * Q o / (P o + Q o))) / 2
noncomputable def condLaw {m : ℕ} {O : Type} [DecidableEq O]
    (g : (Fin m → Bool) → O) (i : Fin m) (c : Bool) (o : O) : ℝ :=
  ((Finset.univ.filter (fun z : Fin m → Bool => z i = c ∧ g z = o)).card : ℝ) / 2 ^ (m - 1)
theorem p1_pow_bound (m : ℕ) (hm : 9 ≤ m) : 40 * (m + 1) ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ]; omega
theorem p1_succ_le (n : ℕ) (hn : 360 ≤ n) : n + 1 ≤ 2 ^ (n / 40) := by
  have h := p1_pow_bound (n / 40) (by omega)
  omega
theorem p1_choose_mul (n d : ℕ) (hd : d ≤ n) : n.choose d * 16 ^ (n - d) ≤ 17 ^ n := by
  have h : (17:ℕ) ^ n = ∑ m ∈ Finset.range (n + 1), 1 ^ m * 16 ^ (n - m) * n.choose m :=
    (add_pow (1:ℕ) 16 n)
  rw [h]
  have hmem : d ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  calc n.choose d * 16 ^ (n - d) = 1 ^ d * 16 ^ (n - d) * n.choose d := by ring
    _ ≤ ∑ m ∈ Finset.range (n + 1), 1 ^ m * 16 ^ (n - m) * n.choose m :=
        Finset.single_le_sum (f := fun m => 1 ^ m * 16 ^ (n - m) * n.choose m)
          (fun i _ => Nat.zero_le _) hmem
theorem p1_choose_pow8 (n d : ℕ) (hd : d ≤ n) : (n.choose d) ^ 8 ≤ 2 ^ (n + 32 * d) := by
  have h1 := p1_choose_mul n d hd
  have h2 : (n.choose d * 16 ^ (n - d)) ^ 8 ≤ (17 ^ n) ^ 8 := Nat.pow_le_pow_left h1 8
  have h3 : (17 ^ n) ^ 8 ≤ 2 ^ (33 * n) := by
    rw [← pow_mul, mul_comm, pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) n
  have h4 : (n.choose d * 16 ^ (n - d)) ^ 8 = (n.choose d) ^ 8 * 2 ^ (32 * (n - d)) := by
    rw [mul_pow, ← pow_mul, show (16:ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    congr 2
    ring
  have h5 : (2:ℕ) ^ (33 * n) = 2 ^ (n + 32 * d) * 2 ^ (32 * (n - d)) := by
    rw [← pow_add]
    congr 1
    omega
  have h6 : (n.choose d) ^ 8 * 2 ^ (32 * (n - d)) ≤ 2 ^ (n + 32 * d) * 2 ^ (32 * (n - d)) := by
    rw [← h4, ← h5]
    exact le_trans h2 h3
  exact Nat.le_of_mul_le_mul_right h6 (by positivity)
theorem p1_vand (k t x : ℕ) : k.choose x * t.choose x ≤ (k + t).choose (k + t - 2 * x) := by
  rcases Nat.lt_or_ge k x with hk | hk
  · rw [Nat.choose_eq_zero_of_lt hk]; simp
  rcases Nat.lt_or_ge t x with ht | ht
  · rw [Nat.choose_eq_zero_of_lt ht]; simp
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ht
  have e1 : (x + a).choose x = (x + a).choose a := Nat.choose_symm_add
  have e2 : (x + b).choose x = (x + b).choose b := Nat.choose_symm_add
  have e3 : x + a + (x + b) - 2 * x = a + b := by omega
  rw [e1, e2, e3, Nat.add_choose_eq (x + a) (x + b) (a + b)]
  exact Finset.single_le_sum
    (f := fun ij : ℕ × ℕ => (x + a).choose ij.1 * (x + b).choose ij.2)
    (fun _ _ => Nat.zero_le _) (a := (a, b)) (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)
theorem p1_central (x n : ℕ) (h : 2 * x ≤ n) : 4 ^ x ≤ (2 * x + 1) * n.choose x := by
  calc 4 ^ x ≤ (2 * x + 1) * (2 * x).choose x := by
        rw [← Nat.centralBinom_eq_two_mul_choose]
        exact Nat.four_pow_le_two_mul_add_one_mul_centralBinom x
    _ ≤ (2 * x + 1) * n.choose x := Nat.mul_le_mul_left _ (Nat.choose_le_choose x h)
theorem p1_final (n B F : ℕ) (hn : 1000 ≤ n) (hF : 0 < F)
    (h : 4 ^ (39 * n / 80 + 1) * B ≤
      (2 * (39 * n / 80 + 1) + 1) * n.choose (n - 2 * (39 * n / 80 + 1)) * F) :
    2 * 4 ^ n * B ^ 3 < F ^ 3 := by
  set x := 39 * n / 80 + 1 with hx
  set d := n - 2 * x with hd
  have hdn : d ≤ n := by omega
  have h2x : 2 * x + d = n := by omega
  have h40 : 40 * d < n := by omega
  have hc8 := p1_choose_pow8 n d hdn
  have hs := p1_succ_le n (by omega)
  have h4 : (4:ℕ) = 2 ^ 2 := by norm_num
  have hA : (2 * x + 1) ^ 24 ≤ 2 ^ (24 * (n / 40)) := by
    rw [pow_mul']
    exact Nat.pow_le_pow_left (by omega) 24
  have hB : (n.choose d) ^ 24 ≤ 2 ^ (3 * (n + 32 * d)) := by
    rw [show (n.choose d) ^ 24 = ((n.choose d) ^ 8) ^ 3 by rw [← pow_mul], pow_mul']
    exact Nat.pow_le_pow_left hc8 3
  have hkey : (2 * 4 ^ n * ((2 * x + 1) * n.choose d) ^ 3) ^ 8 < ((4 ^ x) ^ 3) ^ 8 := by
    have e1 : (2 * 4 ^ n * ((2 * x + 1) * n.choose d) ^ 3) ^ 8
        = 2 ^ 8 * (4 ^ n) ^ 8 * ((2 * x + 1) ^ 24 * (n.choose d) ^ 24) := by ring
    have e3 : ((4:ℕ) ^ n) ^ 8 = 2 ^ (16 * n) := by
      rw [← pow_mul, h4, ← pow_mul]
      congr 1
      ring
    have e2 : (((4:ℕ) ^ x) ^ 3) ^ 8 = 2 ^ (48 * x) := by
      rw [← pow_mul, ← pow_mul, h4, ← pow_mul]
      congr 1
      ring
    rw [e1, e3, e2]
    calc 2 ^ 8 * 2 ^ (16 * n) * ((2 * x + 1) ^ 24 * (n.choose d) ^ 24)
        ≤ 2 ^ 8 * 2 ^ (16 * n) * (2 ^ (24 * (n / 40)) * 2 ^ (3 * (n + 32 * d))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hA hB)
      _ = 2 ^ (8 + 16 * n + (24 * (n / 40) + 3 * (n + 32 * d))) := by
          rw [← pow_add, ← pow_add, ← pow_add]
      _ < 2 ^ (48 * x) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt : 2 * 4 ^ n * ((2 * x + 1) * n.choose d) ^ 3 < (4 ^ x) ^ 3 :=
    lt_of_pow_lt_pow_left₀ 8 (Nat.zero_le _) hkey
  have hpos : 0 < (4 ^ x) ^ 3 := by positivity
  have hF3 : 0 < F ^ 3 := by positivity
  apply Nat.lt_of_mul_lt_mul_left (a := (4 ^ x) ^ 3)
  calc (4 ^ x) ^ 3 * (2 * 4 ^ n * B ^ 3) = 2 * 4 ^ n * (4 ^ x * B) ^ 3 := by ring
    _ ≤ 2 * 4 ^ n * ((2 * x + 1) * n.choose d * F) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3)
    _ = (2 * 4 ^ n * ((2 * x + 1) * n.choose d) ^ 3) * F ^ 3 := by ring
    _ < (4 ^ x) ^ 3 * F ^ 3 := Nat.mul_lt_mul_of_pos_right hlt hF3
theorem p1_perm_le {n : ℕ} (W U T : Finset (Fin n)) (h : U.card = W.card) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ W, σ i ∈ T)).card ≤
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ U, σ i ∈ T)).card := by
  have hc : Fintype.card {x // x ∈ U} = Fintype.card {x // x ∈ W} := by
    simp only [Fintype.card_coe, h]
  let e : {x // x ∈ U} ≃ {x // x ∈ W} := Fintype.equivOfCardEq hc
  let ρ : Equiv.Perm (Fin n) := e.extendSubtype
  have hρ : ∀ i ∈ U, ρ i ∈ W := fun i hi => Equiv.extendSubtype_mem e i hi
  apply Finset.card_le_card_of_injOn (fun σ => σ * ρ)
  · intro σ hσ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    intro i hi
    rw [Equiv.Perm.mul_apply]
    exact hσ _ (hρ i hi)
  · intro σ _ τ _ hστ
    exact mul_right_cancel hστ
theorem p1_card_perm_pre {n : ℕ} (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) :
    (Finset.univ.filter (fun i : Fin n => σ i ∈ T)).card = T.card := by
  apply Finset.card_bij (fun i _ => σ i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi
  · intro i _ j _ hij
    exact σ.injective hij
  · intro t ht
    refine ⟨σ.symm t, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
      exact ht
    · simp
theorem p1_sum_perm {n : ℕ} (w : ℕ) (T : Finset (Fin n)) :
    ∑ U ∈ Finset.powersetCard w (Finset.univ : Finset (Fin n)),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ U, σ i ∈ T)).card =
    n.factorial * T.card.choose w := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ σ : Equiv.Perm (Fin n),
      ∑ U ∈ Finset.powersetCard w (Finset.univ : Finset (Fin n)),
        (if ∀ i ∈ U, σ i ∈ T then 1 else 0) = T.card.choose w := by
    intro σ
    rw [← Finset.card_filter]
    have hset : (Finset.powersetCard w (Finset.univ : Finset (Fin n))).filter
        (fun U => ∀ i ∈ U, σ i ∈ T) =
        Finset.powersetCard w (Finset.univ.filter (fun i : Fin n => σ i ∈ T)) := by
      ext U
      simp only [Finset.mem_filter, Finset.mem_powersetCard, true_and,
        Finset.subset_iff, Finset.mem_univ]
      tauto
    rw [hset, Finset.card_powersetCard, p1_card_perm_pre]
  rw [Finset.sum_congr rfl (fun σ _ => key σ)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
theorem p1_count {n : ℕ} (W T : Finset (Fin n)) :
    n.choose W.card * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => ∀ i ∈ W, σ i ∈ T)).card ≤
    n.factorial * T.card.choose W.card := by
  rw [← p1_sum_perm W.card T]
  have hcard : (Finset.powersetCard W.card (Finset.univ : Finset (Fin n))).card = n.choose W.card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hcard, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro U hU
  rw [Finset.mem_powersetCard] at hU
  exact p1_perm_le W U T hU.2
theorem p1_card_split {n : ℕ} (S : Finset (Bool × Fin n)) :
    (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card +
    (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card = S.card := by
  have h1 : S.card = ∑ v : Bool × Fin n, if v ∈ S then 1 else 0 := by
    simp
  rw [h1, Fintype.sum_prod_type, Fintype.sum_bool, Finset.card_filter, Finset.card_filter]
  ring
theorem p1_bad_large {n : ℕ} (S : Finset (Bool × Fin n))
    (hkt : (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card +
      (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card = n)
    (σ : Equiv.Perm (Fin n))
    (hbad : n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card) :
    39 * n / 80 + 1 ≤
      (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S ∧ (true, σ i) ∈ S)).card := by
  have hPQ := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)) (fun i => (true, σ i) ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter] at hPQ
  have hQP := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i : Fin n => (true, σ i) ∈ S)) (fun i => (false, i) ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter] at hQP
  have hEP := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S)))
    (fun i => (false, i) ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter] at hEP
  have hQ : (Finset.univ.filter (fun i : Fin n => (true, σ i) ∈ S)).card =
      (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card := by
    have := p1_card_perm_pre σ (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S))
    rw [← this]
    congr 1
    ext i
    simp
  have e1 : (Finset.univ.filter (fun i : Fin n => (true, σ i) ∈ S ∧ (false, i) ∈ S)) =
      (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S ∧ (true, σ i) ∈ S)) := by
    apply Finset.filter_congr
    intro i _
    exact and_comm
  have e2 : (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S) ∧ (false, i) ∈ S)) =
      (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S ∧ ¬ (true, σ i) ∈ S)) := by
    apply Finset.filter_congr
    intro i _
    tauto
  have e3 : (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S) ∧ ¬ (false, i) ∈ S)) =
      (Finset.univ.filter (fun i : Fin n => (true, σ i) ∈ S ∧ ¬ (false, i) ∈ S)) := by
    apply Finset.filter_congr
    intro i _
    tauto
  rw [e1] at hQP
  rw [e2, e3] at hEP
  omega
theorem p1_bad_count (n : ℕ) (S : Finset (Bool × Fin n))
    (hkt : (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card +
      (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card = n) :
    n.choose (39 * n / 80 + 1) * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)).card ≤
    (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card.choose (39 * n / 80 + 1) *
      (n.factorial *
        (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card.choose (39 * n / 80 + 1)) := by
  have hsub : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)) ⊆
      (Finset.powersetCard (39 * n / 80 + 1) (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S))).biUnion
        (fun W => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
          ∀ i ∈ W, σ i ∈ Finset.univ.filter (fun j : Fin n => (true, j) ∈ S))) := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    have hl := p1_bad_large S hkt σ hσ.2
    obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hl
    rw [Finset.mem_biUnion]
    refine ⟨W, ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      refine ⟨?_, hWcard⟩
      intro i hi
      have hi2 := hWsub hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi2 ⊢
      exact hi2.1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      have hi2 := hWsub hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi2
      exact hi2.2
  calc n.choose (39 * n / 80 + 1) * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)).card
      ≤ n.choose (39 * n / 80 + 1) * ∑ W ∈ Finset.powersetCard (39 * n / 80 + 1)
          (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)),
          (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            ∀ i ∈ W, σ i ∈ Finset.univ.filter (fun j : Fin n => (true, j) ∈ S))).card :=
        Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le)
    _ = ∑ W ∈ Finset.powersetCard (39 * n / 80 + 1)
          (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)),
          n.choose (39 * n / 80 + 1) * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
            ∀ i ∈ W, σ i ∈ Finset.univ.filter (fun j : Fin n => (true, j) ∈ S))).card := by
        rw [Finset.mul_sum]
    _ ≤ ∑ W ∈ Finset.powersetCard (39 * n / 80 + 1)
          (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)),
          n.factorial *
            (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card.choose (39 * n / 80 + 1) := by
        apply Finset.sum_le_sum
        intro W hW
        rw [Finset.mem_powersetCard] at hW
        have hW2 := p1_count W (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S))
        rw [hW.2] at hW2
        exact hW2
    _ = (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card.choose (39 * n / 80 + 1) *
          (n.factorial *
            (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card.choose (39 * n / 80 + 1)) := by
        rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
theorem A1_perS (n : ℕ) (hn : 1000 ≤ n) (S : Finset (Bool × Fin n)) (hS : S.card = n) :
    2 * 4 ^ n * ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)).card) ^ 3
      < (n.factorial) ^ 3 := by
  have hkt := p1_card_split S
  rw [hS] at hkt
  have hcount := p1_bad_count n S hkt
  apply p1_final n _ n.factorial hn (Nat.factorial_pos n)
  have h2x : 2 * (39 * n / 80 + 1) ≤ n := by omega
  have hv := p1_vand (Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card
    (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card (39 * n / 80 + 1)
  rw [hkt] at hv
  have hc := p1_central (39 * n / 80 + 1) n h2x
  calc 4 ^ (39 * n / 80 + 1) * (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)).card
      ≤ (2 * (39 * n / 80 + 1) + 1) * n.choose (39 * n / 80 + 1) *
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)).card :=
        Nat.mul_le_mul_right _ hc
    _ = (2 * (39 * n / 80 + 1) + 1) * (n.choose (39 * n / 80 + 1) *
        (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        n > 40 * (Finset.univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)).card) := by
        ring
    _ ≤ (2 * (39 * n / 80 + 1) + 1) *
        ((Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card.choose (39 * n / 80 + 1) *
        (n.factorial *
          (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card.choose (39 * n / 80 + 1))) :=
        Nat.mul_le_mul_left _ hcount
    _ = (2 * (39 * n / 80 + 1) + 1) *
        ((Finset.univ.filter (fun i : Fin n => (false, i) ∈ S)).card.choose (39 * n / 80 + 1) *
          (Finset.univ.filter (fun j : Fin n => (true, j) ∈ S)).card.choose (39 * n / 80 + 1)) *
        n.factorial := by
        ring
    _ ≤ (2 * (39 * n / 80 + 1) + 1) * n.choose (n - 2 * (39 * n / 80 + 1)) * n.factorial :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hv)
theorem p2_fixA_card {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)).card = (n - A.card).factorial := by
  have h1 : (univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)).card
      = Fintype.card {f : Equiv.Perm (Fin n) // ∀ a, ¬ (a ∉ A) → f a = a} := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro ρ _
    simp only [not_not]
  rw [h1, ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ∉ A)),
    Fintype.card_perm]
  congr 1
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
theorem p2_fix_le (n k : ℕ) (hk : k ≤ n) :
    (univ.filter (fun ρ : Equiv.Perm (Fin n) =>
      k ≤ (univ.filter (fun i => ρ i = i)).card)).card * k.factorial ≤ n.factorial := by
  have hsub : univ.filter (fun ρ : Equiv.Perm (Fin n) => k ≤ (univ.filter (fun i => ρ i = i)).card)
      ⊆ (powersetCard k (univ : Finset (Fin n))).biUnion
        (fun A => univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)) := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq hρ.2
    rw [Finset.mem_biUnion]
    refine ⟨A, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
    have := hA ha
    rw [Finset.mem_filter] at this
    exact this.2
  have h2 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h3 : ∑ A ∈ powersetCard k (univ : Finset (Fin n)),
      (univ.filter (fun ρ : Equiv.Perm (Fin n) => ∀ a ∈ A, ρ a = a)).card
      = n.choose k * (n - k).factorial := by
    rw [Finset.sum_congr rfl (fun A hA => by rw [p2_fixA_card, (Finset.mem_powersetCard.mp hA).2])]
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [h3] at h2
  calc _ ≤ n.choose k * (n - k).factorial * k.factorial := Nat.mul_le_mul_right _ h2
    _ = n.factorial := by
      rw [mul_assoc, mul_comm (n-k).factorial, ← mul_assoc]
      exact Nat.choose_mul_factorial_mul_factorial hk
theorem p2_pairs_le (n : ℕ) :
    (univ.filter (fun q : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
      n < 8 * (univ.filter (fun i : Fin n => q.1 i = q.2 i)).card)).card
    ≤ n.factorial * (univ.filter (fun ρ : Equiv.Perm (Fin n) =>
      n < 8 * (univ.filter (fun i : Fin n => ρ i = i)).card)).card := by
  have hu : n.factorial = (univ : Finset (Equiv.Perm (Fin n))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hu, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun q => (q.1, q.1⁻¹ * q.2))
  · intro q hq
    simp only [Finset.mem_coe, Finset.mem_product,
      Finset.mem_univ, true_and, Finset.mem_filter] at hq ⊢
    have : (univ.filter (fun i : Fin n => (q.1⁻¹ * q.2) i = i))
        = univ.filter (fun i : Fin n => q.1 i = q.2 i) := by
      apply Finset.filter_congr
      intro i _
      rw [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq, eq_comm]
    rw [this]
    exact hq
  · intro q1 _ q2 _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    ext1
    · exact h1
    · rw [h1] at h2
      exact mul_left_cancel h2
theorem A2_agree (n : ℕ) (hn : 1000 ≤ n) :
    6 * (Finset.univ.filter (fun q : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
      n < 8 * (Finset.univ.filter (fun i : Fin n => q.1 i = q.2 i)).card)).card
      < (n.factorial) ^ 2 := by
  have h1 := p2_pairs_le n
  have h2 := p2_fix_le n (n / 8 + 1) (by omega)
  have hset : (univ.filter (fun ρ : Equiv.Perm (Fin n) =>
      n < 8 * (univ.filter (fun i : Fin n => ρ i = i)).card))
      = univ.filter (fun ρ : Equiv.Perm (Fin n) =>
        n / 8 + 1 ≤ (univ.filter (fun i : Fin n => ρ i = i)).card) := by
    apply Finset.filter_congr
    intro ρ _
    omega
  rw [← hset] at h2
  have h4 : (4:ℕ).factorial ≤ (n / 8 + 1).factorial := Nat.factorial_le (by omega)
  have h5 : (4:ℕ).factorial = 24 := by decide
  have hpos : 0 < n.factorial := Nat.factorial_pos n
  generalize (univ.filter (fun ρ : Equiv.Perm (Fin n) =>
      n < 8 * (univ.filter (fun i : Fin n => ρ i = i)).card)).card = F at h1 h2
  generalize (Finset.univ.filter (fun q : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
      n < 8 * (Finset.univ.filter (fun i : Fin n => q.1 i = q.2 i)).card)).card = Q at h1 ⊢
  have h6 : 24 * F ≤ n.factorial := by
    calc 24 * F ≤ (n/8+1).factorial * F := by rw [← h5]; exact Nat.mul_le_mul_right _ h4
      _ = F * (n/8+1).factorial := mul_comm _ _
      _ ≤ n.factorial := h2
  have h7 : 6 * F < n.factorial := by omega
  calc 6 * Q ≤ 6 * (n.factorial * F) := Nat.mul_le_mul_left _ h1
    _ = n.factorial * (6 * F) := by ring
    _ < n.factorial * n.factorial := (Nat.mul_lt_mul_left hpos).mpr h7
    _ = n.factorial ^ 2 := by ring
def p2_E (n : ℕ) (j k : Fin 3) : Finset (Fin 3 → Equiv.Perm (Fin n)) :=
  univ.filter (fun M : Fin 3 → Equiv.Perm (Fin n) => n < 8 * agreeCount M j k)
def p2_bad (n : ℕ) (S : Finset (Bool × Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  univ.filter (fun σ : Equiv.Perm (Fin n) =>
    n > 40 * (univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, σ i) ∉ S))).card)
def p2_B1 (n : ℕ) : Finset (Fin 3 → Equiv.Perm (Fin n)) :=
  (powersetCard n (univ : Finset (Bool × Fin n))).biUnion
    (fun S => Fintype.piFinset (fun _ : Fin 3 => p2_bad n S))
def p2_B2 (n : ℕ) : Finset (Fin 3 → Equiv.Perm (Fin n)) :=
  p2_E n 0 1 ∪ p2_E n 0 2 ∪ p2_E n 1 2
theorem p2_agree_symm {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j j' : Fin 3) :
    agreeCount M j j' = agreeCount M j' j := by
  unfold agreeCount
  congr 1
  apply Finset.filter_congr
  intro i _
  exact eq_comm
theorem p2_fin3 : ∀ i j k l : Fin 3, j ≠ k → j ≠ l → k ≠ l → i = j ∨ i = k ∨ i = l := by
  decide
theorem p2_fin3_pairs : ∀ j j' : Fin 3, j ≠ j' →
    (j = 0 ∧ j' = 1) ∨ (j = 1 ∧ j' = 0) ∨ (j = 0 ∧ j' = 2) ∨ (j = 2 ∧ j' = 0) ∨
    (j = 1 ∧ j' = 2) ∨ (j = 2 ∧ j' = 1) := by
  decide
theorem p2_E_card {n : ℕ} (j k l : Fin 3) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    (p2_E n j k).card ≤ (univ.filter (fun q : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
      n < 8 * (univ.filter (fun i : Fin n => q.1 i = q.2 i)).card)).card * n.factorial := by
  have hu : n.factorial = (univ : Finset (Equiv.Perm (Fin n))).card := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [hu, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun M => ((M j, M k), M l))
  · intro M hM
    simp only [p2_E, Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_filter, true_and] at hM ⊢
    exact hM
  · intro M1 _ M2 _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    funext i
    rcases p2_fin3 i j k l hjk hjl hkl with hi | hi | hi
    · rw [hi]
      exact h1
    · rw [hi]
      exact h2
    · rw [hi]
      exact h3
theorem p2_B1_bound {n : ℕ} (hn : 1000 ≤ n) : 2 * (p2_B1 n).card ≤ n.factorial ^ 3 := by
  have h1 : (p2_B1 n).card ≤
      ∑ S ∈ powersetCard n (univ : Finset (Bool × Fin n)), (p2_bad n S).card ^ 3 := by
    refine Finset.card_biUnion_le.trans (le_of_eq ?_)
    apply Finset.sum_congr rfl
    intro S _
    rw [Fintype.card_piFinset_const]
  have h2 : ∀ S ∈ powersetCard n (univ : Finset (Bool × Fin n)),
      2 * 4 ^ n * (p2_bad n S).card ^ 3 ≤ n.factorial ^ 3 := by
    intro S hS
    exact (A1_perS n hn S (Finset.mem_powersetCard.mp hS).2).le
  have h3 : 2 * 4 ^ n * (p2_B1 n).card ≤ 4 ^ n * n.factorial ^ 3 := by
    calc 2 * 4 ^ n * (p2_B1 n).card
        ≤ 2 * 4 ^ n * ∑ S ∈ powersetCard n (univ : Finset (Bool × Fin n)),
          (p2_bad n S).card ^ 3 := Nat.mul_le_mul_left _ h1
      _ = ∑ S ∈ powersetCard n (univ : Finset (Bool × Fin n)),
          2 * 4 ^ n * (p2_bad n S).card ^ 3 := by rw [Finset.mul_sum]
      _ ≤ ∑ S ∈ powersetCard n (univ : Finset (Bool × Fin n)), n.factorial ^ 3 :=
          Finset.sum_le_sum h2
      _ = (2 * n).choose n * n.factorial ^ 3 := by
          rw [Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]
          simp
      _ ≤ 4 ^ n * n.factorial ^ 3 := by
          apply Nat.mul_le_mul_right
          calc (2 * n).choose n ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
            _ = 4 ^ n := by rw [pow_mul]; norm_num
  have h4 : 0 < 4 ^ n := by positivity
  have h5 : 4 ^ n * (2 * (p2_B1 n).card) ≤ 4 ^ n * n.factorial ^ 3 := by
    calc 4 ^ n * (2 * (p2_B1 n).card) = 2 * 4 ^ n * (p2_B1 n).card := by ring
      _ ≤ _ := h3
  exact Nat.le_of_mul_le_mul_left h5 h4
theorem p2_B2_bound {n : ℕ} (hn : 1000 ≤ n) : 2 * (p2_B2 n).card < n.factorial ^ 3 := by
  have e1 := p2_E_card (n := n) 0 1 2 (by decide) (by decide) (by decide)
  have e2 := p2_E_card (n := n) 0 2 1 (by decide) (by decide) (by decide)
  have e3 := p2_E_card (n := n) 1 2 0 (by decide) (by decide) (by decide)
  have hA2 := A2_agree n hn
  have hc : (p2_B2 n).card ≤ (p2_E n 0 1).card + (p2_E n 0 2).card + (p2_E n 1 2).card := by
    unfold p2_B2
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hpos : 0 < n.factorial := Nat.factorial_pos n
  generalize (univ.filter (fun q : Equiv.Perm (Fin n) × Equiv.Perm (Fin n) =>
      n < 8 * (univ.filter (fun i : Fin n => q.1 i = q.2 i)).card)).card = Q at e1 e2 e3 hA2
  generalize n.factorial = F at e1 e2 e3 hA2 hpos ⊢
  have h1 : 2 * (p2_B2 n).card ≤ 6 * Q * F := by linarith
  have h2 : 6 * Q * F < F ^ 2 * F := Nat.mul_lt_mul_of_pos_right hA2 hpos
  calc 2 * (p2_B2 n).card ≤ 6 * Q * F := h1
    _ < F ^ 2 * F := h2
    _ = F ^ 3 := by ring
theorem A_good_perms : ∃ NA : ℕ, ∀ n : ℕ, NA ≤ n → ∃ M : Fin 3 → Equiv.Perm (Fin n),
    (∀ S : Finset (Bool × Fin n), S.card = n → ∃ j : Fin 3, n ≤ 40 * splitCount M j S) ∧
    (∀ j j' : Fin 3, j ≠ j' → 8 * agreeCount M j j' ≤ n) := by
  refine ⟨1000, fun n hn => ?_⟩
  have hcu : (univ : Finset (Fin 3 → Equiv.Perm (Fin n))).card = n.factorial ^ 3 := by
    simp [Fintype.card_perm]
  have hlt : (p2_B1 n ∪ p2_B2 n).card < (univ : Finset (Fin 3 → Equiv.Perm (Fin n))).card := by
    rw [hcu]
    have h1 := Finset.card_union_le (p2_B1 n) (p2_B2 n)
    have h2 := p2_B1_bound hn
    have h3 := p2_B2_bound hn
    generalize n.factorial ^ 3 = T at h2 h3 ⊢
    omega
  obtain ⟨M, -, hM⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨M, ?_, ?_⟩
  · intro S hS
    by_contra hcon
    apply hM
    apply Finset.mem_union_left
    unfold p2_B1
    rw [Finset.mem_biUnion]
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hS⟩, ?_⟩
    rw [Fintype.mem_piFinset]
    intro j
    unfold p2_bad
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, not_le.mp (fun h => hcon ⟨j, h⟩)⟩
  · intro j j' hjj'
    by_contra hcon0
    have hcon := not_le.mp hcon0
    apply hM
    apply Finset.mem_union_right
    have hs := p2_agree_symm M j j'
    simp only [p2_B2, p2_E, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases p2_fin3_pairs j j' hjj' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl (Or.inl hcon)
    · rw [hs] at hcon
      exact Or.inl (Or.inl hcon)
    · exact Or.inl (Or.inr hcon)
    · rw [hs] at hcon
      exact Or.inl (Or.inr hcon)
    · exact Or.inr hcon
    · rw [hs] at hcon
      exact Or.inr hcon
theorem C_cut_card {n : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) : (cutSet order).card = n := by
  unfold cutSet
  rw [Finset.card_image_of_injective _ order.injective, Fin.card_filter_val_lt]
  omega
theorem D_numeric (n p s : ℕ) (hn : 256 ≤ n) (hp : 0 < p)
    (h : ((n / 256 : ℕ) : ℝ) ≤ 160 * Real.log (Fintype.card (Fin p → Fin s × Fin s))) :
    n ≤ 60000 * p * Nat.clog 2 s := by
  have hcard : Fintype.card (Fin p → Fin s × Fin s) = (s * s) ^ p := by
    simp [Fintype.card_prod, Fintype.card_fin]
  rw [hcard] at h
  push_cast at h
  rw [Real.log_pow] at h
  have hN : 1 ≤ n / 256 := by omega
  have hNr : (1:ℝ) ≤ ((n / 256 : ℕ) : ℝ) := by exact_mod_cast hN
  rcases Nat.lt_or_ge s 2 with hs | hs
  · have h0 : Real.log ((s:ℝ) * s) = 0 := by
      interval_cases s <;> simp
    rw [h0] at h
    linarith
  · have hc : s ≤ 2 ^ Nat.clog 2 s := Nat.le_pow_clog (by norm_num) s
    have hlogs : Real.log s ≤ Nat.clog 2 s * Real.log 2 := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast hc
    have hl2 := Real.log_two_lt_d9
    have hs0 : (0:ℝ) < s := by positivity
    have hlogss : Real.log ((s:ℝ) * s) = 2 * Real.log s := by
      rw [Real.log_mul hs0.ne' hs0.ne']; ring
    rw [hlogss] at h
    have hcpos : 0 < Nat.clog 2 s := Nat.clog_pos (by norm_num) (by omega)
    have hcr : (0:ℝ) ≤ (Nat.clog 2 s : ℝ) := by positivity
    have hpr : (0:ℝ) ≤ (p : ℝ) := by positivity
    have hlogs2 : Real.log s ≤ Nat.clog 2 s * (7 / 10) := by nlinarith
    have key : ((n / 256 : ℕ) : ℝ) ≤ ((224 * (p * Nat.clog 2 s) : ℕ) : ℝ) := by
      push_cast
      nlinarith
    have key2 : n / 256 ≤ 224 * (p * Nat.clog 2 s) := by exact_mod_cast key
    have hX : 1 ≤ p * Nat.clog 2 s := Nat.one_le_iff_ne_zero.mpr (by positivity)
    rw [mul_assoc]
    generalize p * Nat.clog 2 s = X at key2 hX ⊢
    omega
noncomputable def p3_r {m : ℕ} {O : Type} [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (o : O) (c : Bool) : ℝ :=
  2 * condLaw g i c o / (condLaw g i false o + condLaw g i true o)
theorem p3_cl_nonneg {m : ℕ} {O : Type} [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (c : Bool) (o : O) : 0 ≤ condLaw g i c o := by
  unfold condLaw
  positivity
theorem p3_r_nonneg {m : ℕ} {O : Type} [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (o : O) (c : Bool) : 0 ≤ p3_r g i o c := by
  unfold p3_r
  exact div_nonneg (mul_nonneg (by norm_num) (p3_cl_nonneg g i c o))
    (add_nonneg (p3_cl_nonneg g i false o) (p3_cl_nonneg g i true o))
theorem p3_r_sum {m : ℕ} {O : Type} [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (o : O) : ∑ c : Bool, p3_r g i o c ≤ 2 := by
  rw [Fintype.sum_bool]
  unfold p3_r
  have h2 := p3_cl_nonneg g i false o
  have h3 := p3_cl_nonneg g i true o
  rcases eq_or_lt_of_le (add_nonneg h2 h3) with h | h
  · rw [← h, div_zero, div_zero]
    norm_num
  · rw [← add_div, div_le_iff₀ h]
    linarith
theorem p3_cl_pos {m : ℕ} {O : Type} [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (z : Fin m → Bool) : 0 < condLaw g i (z i) (g z) := by
  unfold condLaw
  apply div_pos _ (by positivity)
  exact_mod_cast Finset.card_pos.mpr ⟨z, by simp⟩
theorem p3_r_pos {m : ℕ} {O : Type} [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (z : Fin m → Bool) : 0 < p3_r g i (g z) (z i) := by
  unfold p3_r
  have h1 := p3_cl_pos g i z
  have h2 := p3_cl_nonneg g i false (g z)
  have h3 := p3_cl_nonneg g i true (g z)
  have hden : 0 < condLaw g i false (g z) + condLaw g i true (g z) := by
    cases hz : z i
    · rw [hz] at h1
      linarith
    · rw [hz] at h1
      linarith
  exact div_pos (mul_pos two_pos h1) hden
theorem p3_fiber {m : ℕ} {O : Type} [Fintype O] [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) (F : Bool → O → ℝ) :
    ∑ z, F (z i) (g z) = ∑ o,
      (((Finset.univ.filter (fun z : Fin m → Bool => z i = false ∧ g z = o)).card : ℝ) * F false o
      + ((Finset.univ.filter (fun z : Fin m → Bool => z i = true ∧ g z = o)).card : ℝ) * F true o) := by
  have h : ∀ z : Fin m → Bool, F (z i) (g z) = ∑ o, ((if z i = false ∧ g z = o then F false o else 0)
      + (if z i = true ∧ g z = o then F true o else 0)) := by
    intro z
    rw [Finset.sum_add_distrib]
    cases hz : z i <;> simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl (fun z _ => h z), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
theorem p3_js {m : ℕ} {O : Type} [Fintype O] [DecidableEq O] (g : (Fin m → Bool) → O)
    (i : Fin m) :
    js (condLaw g i false) (condLaw g i true) = (∑ z, Real.log (p3_r g i (g z) (z i))) / 2 ^ m := by
  have e1 : js (condLaw g i false) (condLaw g i true) = ∑ o, (condLaw g i false o *
      Real.log (p3_r g i o false) + condLaw g i true o * Real.log (p3_r g i o true)) / 2 := rfl
  have hf : ∑ z, Real.log (p3_r g i (g z) (z i)) = ∑ o,
      (((Finset.univ.filter (fun z : Fin m → Bool => z i = false ∧ g z = o)).card : ℝ) *
        Real.log (p3_r g i o false)
      + ((Finset.univ.filter (fun z : Fin m → Bool => z i = true ∧ g z = o)).card : ℝ) *
        Real.log (p3_r g i o true)) := p3_fiber g i (fun c o => Real.log (p3_r g i o c))
  rw [e1, hf, Finset.sum_div]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  generalize Real.log (p3_r g i o false) = A
  generalize Real.log (p3_r g i o true) = B
  have hm : (2:ℝ) ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    have := i.2
    omega
  rw [hm]
  unfold condLaw
  have h' : (2:ℝ) ^ (m - 1) ≠ 0 := by positivity
  field_simp
theorem p3_prodsum {m : ℕ} {O : Type} [Fintype O] [DecidableEq O] (g : (Fin m → Bool) → O) :
    ∑ z : Fin m → Bool, ∏ i, p3_r g i (g z) (z i) ≤ 2 ^ m * Fintype.card O := by
  calc ∑ z : Fin m → Bool, ∏ i, p3_r g i (g z) (z i)
      ≤ ∑ z : Fin m → Bool, ∑ o, ∏ i, p3_r g i o (z i) := by
        apply Finset.sum_le_sum
        intro z _
        exact Finset.single_le_sum (f := fun o => ∏ i, p3_r g i o (z i))
          (fun o _ => Finset.prod_nonneg (fun i _ => p3_r_nonneg g i o (z i)))
          (Finset.mem_univ (g z))
    _ = ∑ o, ∑ z : Fin m → Bool, ∏ i, p3_r g i o (z i) := Finset.sum_comm
    _ = ∑ o, ∏ i, ∑ c, p3_r g i o c := by
        refine Finset.sum_congr rfl (fun o _ => ?_)
        exact (Fintype.prod_sum (fun i c => p3_r g i o c)).symm
    _ ≤ ∑ _o : O, (2:ℝ) ^ m := by
        apply Finset.sum_le_sum
        intro o _
        calc ∏ i, ∑ c, p3_r g i o c ≤ ∏ _i : Fin m, (2:ℝ) :=
              Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun c _ => p3_r_nonneg g i o c))
                (fun i _ => p3_r_sum g i o)
          _ = 2 ^ m := by simp
    _ = 2 ^ m * Fintype.card O := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
theorem B1_info {m : ℕ} {O : Type} [Fintype O] [DecidableEq O] (g : (Fin m → Bool) → O) :
    ∑ i : Fin m, js (condLaw g i false) (condLaw g i true) ≤ Real.log (Fintype.card O) := by
  have hK : (0:ℝ) < Fintype.card O :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨g (fun _ => false)⟩)
  have h2m : (0:ℝ) < 2 ^ m := by positivity
  have hX : ∀ z : Fin m → Bool, 0 < ∏ i, p3_r g i (g z) (z i) :=
    fun z => Finset.prod_pos (fun i _ => p3_r_pos g i z)
  have e1 : ∑ i : Fin m, js (condLaw g i false) (condLaw g i true) =
      (∑ z : Fin m → Bool, Real.log (∏ i, p3_r g i (g z) (z i))) / 2 ^ m := by
    simp only [p3_js]
    rw [← Finset.sum_div, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Real.log_prod (fun i _ => (p3_r_pos g i z).ne')]
  rw [e1, div_le_iff₀ h2m]
  have hb : ∀ z : Fin m → Bool, Real.log (∏ i, p3_r g i (g z) (z i)) ≤
      Real.log (Fintype.card O) + (∏ i, p3_r g i (g z) (z i)) / Fintype.card O - 1 := by
    intro z
    have h := Real.log_le_sub_one_of_pos (div_pos (hX z) hK)
    rw [Real.log_div (hX z).ne' hK.ne'] at h
    linarith
  have hS := p3_prodsum g
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (Fin m → Bool))) => hb z)
  have hR : ∑ z : Fin m → Bool, (Real.log (Fintype.card O) +
      (∏ i, p3_r g i (g z) (z i)) / Fintype.card O - 1) =
      2 ^ m * Real.log (Fintype.card O) +
      (∑ z : Fin m → Bool, ∏ i, p3_r g i (g z) (z i)) / Fintype.card O - 2 ^ m := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]
    simp
  rw [hR] at hsum
  have hd : (∑ z : Fin m → Bool, ∏ i, p3_r g i (g z) (z i)) / Fintype.card O ≤ 2 ^ m := by
    rw [div_le_iff₀ hK]
    linarith
  linarith
lemma p4_L0u (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    2 * (u ^ 2 - u * v) ≤ u ^ 2 * Real.log ((u / v) ^ 2) := by
  rw [Real.log_pow]
  push_cast
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
  rw [inv_div] at hlog
  have e : u ^ 2 * (1 - v / u) = u ^ 2 - u * v := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ u ^ 2)]
lemma p4_L0 (p t : ℝ) (hp : 0 ≤ p) (hpt : p ≤ t) :
    2 * (p - √p * √(t / 2)) ≤ p * Real.log (2 * p / t) := by
  rcases hp.eq_or_lt with h | h
  · subst h
    simp
  · have ht : 0 < t := lt_of_lt_of_le h hpt
    have hu0 : 0 < √p := Real.sqrt_pos.mpr h
    have hv0 : 0 < √(t / 2) := Real.sqrt_pos.mpr (by linarith)
    have hu2 : √p ^ 2 = p := Real.sq_sqrt hp
    have hv2 : √(t / 2) ^ 2 = t / 2 := Real.sq_sqrt (by linarith)
    have h2 : 2 * p / t = (√p / √(t / 2)) ^ 2 := by
      rw [div_pow, hu2, hv2]
      field_simp
    have := p4_L0u (√p) (√(t / 2)) hu0 hv0
    rw [hu2, ← h2] at this
    exact this
lemma p4_L1 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (√a - √b) ^ 2 / 4 ≤
      (a * Real.log (2 * a / (a + b)) + b * Real.log (2 * b / (a + b))) / 2 := by
  have h1 := p4_L0 a (a + b) ha (by linarith)
  have h2 := p4_L0 b (a + b) hb (by linarith)
  have hu := Real.sq_sqrt ha
  have hw := Real.sq_sqrt hb
  have hv := Real.sq_sqrt (show 0 ≤ (a + b) / 2 by linarith)
  nlinarith [sq_nonneg (√a + √b - 2 * √((a + b) / 2))]
lemma p4_L2 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hcp : a * d = b * c) :
    (b + c) / 8 - √a * √d / 4 ≤
      (a * Real.log (2 * a / (a + b)) + b * Real.log (2 * b / (a + b))) / 2 +
      (a * Real.log (2 * a / (a + c)) + c * Real.log (2 * c / (a + c))) / 2 := by
  have h1 := p4_L1 a b ha hb
  have h2 := p4_L1 a c ha hc
  have hbc : √b * √c = √a * √d := by
    rw [← Real.sqrt_mul hb, ← Real.sqrt_mul ha, hcp]
  have hb2 := Real.sq_sqrt hb
  have hc2 := Real.sq_sqrt hc
  nlinarith [sq_nonneg (2 * √a - √b - √c)]
lemma p4_amgm1 (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    √a * √d ≤ (7 / 5 * a + 5 / 7 * d) / 2 := by
  nlinarith [sq_nonneg (7 * √a - 5 * √d), Real.sq_sqrt ha, Real.sq_sqrt hd]
lemma p4_amgm2 (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    √a * √d ≤ (5 / 7 * a + 7 / 5 * d) / 2 := by
  nlinarith [sq_nonneg (5 * √a - 7 * √d), Real.sq_sqrt ha, Real.sq_sqrt hd]
theorem B2_hellinger {O : Type} [Fintype O] (P00 P10 P01 P11 : O → ℝ)
    (h00 : ∀ o, 0 ≤ P00 o) (h10 : ∀ o, 0 ≤ P10 o) (h01 : ∀ o, 0 ≤ P01 o) (h11 : ∀ o, 0 ≤ P11 o)
    (s00 : ∑ o, P00 o = 1) (s10 : ∑ o, P10 o = 1) (s01 : ∑ o, P01 o = 1) (s11 : ∑ o, P11 o = 1)
    (hcp : ∀ o, P00 o * P11 o = P10 o * P01 o)
    (E : O → Prop) [DecidablePred E]
    (hE0 : 3 * ∑ o ∈ Finset.univ.filter E, P00 o ≤ 1)
    (hE1 : 2 ≤ 3 * ∑ o ∈ Finset.univ.filter E, P11 o) :
    1 / 80 ≤ js P00 P10 + js P00 P01 := by
  have S1 : ∑ o, ((P10 o + P01 o) / 8 - √(P00 o) * √(P11 o) / 4) ≤ js P00 P10 + js P00 P01 := by
    unfold js
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun o _ => p4_L2 _ _ _ _ (h00 o) (h10 o) (h01 o) (hcp o))
  have S2 : ∑ o, √(P00 o) * √(P11 o) ≤ ∑ o, (if E o then (7 / 5 * P00 o + 5 / 7 * P11 o) / 2
      else (5 / 7 * P00 o + 7 / 5 * P11 o) / 2) := by
    apply Finset.sum_le_sum
    intro o _
    split_ifs
    · exact p4_amgm1 _ _ (h00 o) (h11 o)
    · exact p4_amgm2 _ _ (h00 o) (h11 o)
  have S4 : ∑ o, ((P10 o + P01 o) / 8 - √(P00 o) * √(P11 o) / 4) =
      (1 + 1) / 8 - (∑ o, √(P00 o) * √(P11 o)) / 4 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib, s10, s01]
  have eA := Finset.sum_filter_add_sum_filter_not Finset.univ E P00
  have eD := Finset.sum_filter_add_sum_filter_not Finset.univ E P11
  rw [s00] at eA
  rw [s11] at eD
  rw [Finset.sum_ite] at S2
  simp only [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum] at S2
  linarith
def p4_sw {m : ℕ} (d : Fin m → Bool) (x y : Fin m → Bool) : Fin m → Bool :=
  fun k => if d k = true then x k else y k
lemma p4_sw_inv {m : ℕ} (d : Fin m → Bool) (x y : Fin m → Bool) :
    p4_sw d (p4_sw d x y) (p4_sw d y x) = x := by
  funext k
  unfold p4_sw
  by_cases h : d k = true <;> simp [h]
lemma p4_sw_t {m : ℕ} (d : Fin m → Bool) (x y : Fin m → Bool) :
    ∀ k, d k = true → p4_sw d x y k = x k := by
  intro k hk
  simp [p4_sw, hk]
lemma p4_sw_f {m : ℕ} (d : Fin m → Bool) (x y : Fin m → Bool) :
    ∀ k, d k = false → p4_sw d x y k = y k := by
  intro k hk
  simp [p4_sw, hk]
theorem B3a_cutpaste {m : ℕ} {T : Type} [DecidableEq T]
    (τ : (Fin m → Bool) → (Fin m → Bool) → T)
    (hrect : ∀ a a' b b', τ a b = τ a' b' → τ a b' = τ a b)
    (d : Fin m → Bool) (α β : Bool → (Fin m → Bool) → (Fin m → Bool))
    (hα : ∀ u z z', (∀ k, d k = true → z k = z' k) → α u z = α u z')
    (hβ : ∀ v z z', (∀ k, d k = false → z k = z' k) → β v z = β v z') (t : T) :
    (Finset.univ.filter (fun z => τ (α false z) (β false z) = t)).card *
      (Finset.univ.filter (fun z => τ (α true z) (β true z) = t)).card =
    (Finset.univ.filter (fun z => τ (α true z) (β false z) = t)).card *
      (Finset.univ.filter (fun z => τ (α false z) (β true z) = t)).card := by
  have hA : ∀ u x y, α u (p4_sw d x y) = α u x := fun u x y => hα u _ _ (p4_sw_t d x y)
  have hB : ∀ v x y, β v (p4_sw d x y) = β v y := fun v x y => hβ v _ _ (p4_sw_f d x y)
  rw [← Finset.card_product, ← Finset.card_product]
  refine Finset.card_bij' (fun q _ => (p4_sw d q.2 q.1, p4_sw d q.1 q.2))
    (fun q _ => (p4_sw d q.2 q.1, p4_sw d q.1 q.2)) ?_ ?_ ?_ ?_
  · rintro ⟨z, z'⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [hA, hB, hA, hB]
    refine ⟨?_, ?_⟩
    · rw [hrect (α true z') (α false z) (β true z') (β false z) (hq.2.trans hq.1.symm), hq.2]
    · rw [hrect (α false z) (α true z') (β false z) (β true z') (hq.1.trans hq.2.symm), hq.1]
  · rintro ⟨w, w'⟩ hq
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    rw [hA, hB, hA, hB]
    refine ⟨?_, ?_⟩
    · rw [hrect (α false w') (α true w) (β true w') (β false w) (hq.2.trans hq.1.symm), hq.2]
    · rw [hrect (α true w) (α false w') (β false w) (β true w') (hq.1.trans hq.2.symm), hq.1]
  · rintro ⟨z, z'⟩ _
    simp only [p4_sw_inv]
  · rintro ⟨w, w'⟩ _
    simp only [p4_sw_inv]
def p4_A {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n))
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R) (q : Fin p)
    (x : Bool × Fin n → Bool) (st : Fin s) : Fin s :=
  ((List.finRange (2*n)).take n).foldl (fun z j => step r q j z (x (order j))) st
def p4_B {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n))
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R) (q : Fin p)
    (x : Bool × Fin n → Bool) (st : Fin s) : Fin s :=
  ((List.finRange (2*n)).drop n).foldl (fun z j => step r q j z (x (order j))) st
def p4_pre {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (init : Fin R → Fin s)
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R)
    (x : Bool × Fin n → Bool) (k : ℕ) : Fin s :=
  ((List.finRange p).take k).foldl (fun st q =>
    (List.finRange (2*n)).foldl (fun z j => step r q j z (x (order j))) st) (init r)
def p4_tau {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (init : Fin R → Fin s)
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R)
    (x : Bool × Fin n → Bool) (q : Fin p) : Fin s × Fin s :=
  (p4_A order step r q x (p4_pre order init step r x q.val),
    p4_B order step r q x (p4_A order step r q x (p4_pre order init step r x q.val)))
lemma p4_pass {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n))
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R) (q : Fin p)
    (x : Bool × Fin n → Bool) (st : Fin s) :
    (List.finRange (2*n)).foldl (fun z j => step r q j z (x (order j))) st =
      p4_B order step r q x (p4_A order step r q x st) := by
  unfold p4_A p4_B
  rw [← List.foldl_append, List.take_append_drop]
lemma p4_pre_zero {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (init : Fin R → Fin s)
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R)
    (x : Bool × Fin n → Bool) : p4_pre order init step r x 0 = init r := by
  simp [p4_pre]
lemma p4_pre_succ {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (init : Fin R → Fin s)
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R)
    (x : Bool × Fin n → Bool) (k : ℕ) (hk : k < p) :
    p4_pre order init step r x (k+1) =
      p4_B order step r ⟨k, hk⟩ x (p4_A order step r ⟨k, hk⟩ x (p4_pre order init step r x k)) := by
  have h1 : (List.finRange p)[k]? = some ⟨k, hk⟩ := by
    rw [List.getElem?_eq_getElem (by simpa using hk)]
    simp
  unfold p4_pre
  rw [List.take_add_one, List.foldl_append, h1]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
  exact p4_pass order step r ⟨k, hk⟩ x _
lemma p4_pre_full {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (init : Fin R → Fin s)
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R)
    (x : Bool × Fin n → Bool) :
    p4_pre order init step r x p = (List.finRange p).foldl (fun st q =>
      (List.finRange (2*n)).foldl (fun z j => step r q j z (x (order j))) st) (init r) := by
  unfold p4_pre
  rw [List.take_of_length_le (by simp)]
lemma p4_mem_take {n : ℕ} (j : Fin (2*n)) (h : j ∈ (List.finRange (2*n)).take n) :
    j.val < n := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp at hi ⊢
  omega
lemma p4_mem_drop {n : ℕ} (j : Fin (2*n)) (h : j ∈ (List.finRange (2*n)).drop n) :
    n ≤ j.val := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  simp
lemma p4_cut_in {n : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (j : Fin (2*n)) (h : j.val < n) :
    order j ∈ cutSet order := by
  unfold cutSet
  exact Finset.mem_image_of_mem _ (by simp [h])
lemma p4_cut_out {n : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n)) (j : Fin (2*n)) (h : n ≤ j.val) :
    order j ∉ cutSet order := by
  unfold cutSet
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
  intro j' hj' he
  have := order.injective he
  subst this
  omega
lemma p4_A_mix {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n))
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R) (q : Fin p)
    (x y : Bool × Fin n → Bool) (st : Fin s) :
    p4_A order step r q (fun v => if v ∈ cutSet order then x v else y v) st =
      p4_A order step r q x st := by
  unfold p4_A
  apply List.foldl_ext
  intro a j hj
  simp only [ite_eq_left (p4_cut_in order j (p4_mem_take j hj))]
lemma p4_B_mix {n p s R : ℕ} (order : Fin (2*n) ≃ (Bool × Fin n))
    (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s) (r : Fin R) (q : Fin p)
    (x y : Bool × Fin n → Bool) (st : Fin s) :
    p4_B order step r q (fun v => if v ∈ cutSet order then x v else y v) st =
      p4_B order step r q y st := by
  unfold p4_B
  apply List.foldl_ext
  intro a j hj
  simp only [ite_eq_right (p4_cut_out order j (p4_mem_drop j hj))]
theorem C_transcript {n p s R : ℕ} (hp : 0 < p) (order : Fin (2*n) ≃ (Bool × Fin n))
    (init : Fin R → Fin s) (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s)
    (out : Fin R → Fin s → Bool) :
    ∃ (τ : Fin R → (Bool × Fin n → Bool) → (Fin p → Fin s × Fin s))
      (o : Fin R → (Fin p → Fin s × Fin s) → Bool),
      (∀ r x, ans order init step out r x = o r (τ r x)) ∧
      (∀ r x y, τ r x = τ r y →
        τ r (fun v => if v ∈ cutSet order then x v else y v) = τ r x) := by
  refine ⟨fun r x => p4_tau order init step r x, fun r T => out r (T ⟨p - 1, by omega⟩).2, ?_, ?_⟩
  · intro r x
    have h := p4_pre_succ order init step r x (p - 1) (by omega)
    have hp1 : p - 1 + 1 = p := by omega
    rw [hp1, p4_pre_full] at h
    show out r _ = out r _
    rw [h]
    rfl
  · intro r x y hxy
    have hpre : ∀ k, k ≤ p → p4_pre order init step r
        (fun v => if v ∈ cutSet order then x v else y v) k = p4_pre order init step r x k := by
      intro k
      induction k with
      | zero => intro _; rw [p4_pre_zero, p4_pre_zero]
      | succ k ih =>
        intro hk
        have hk' : k < p := by omega
        have hq := congrFun hxy ⟨k, hk'⟩
        simp only [p4_tau, Prod.mk.injEq] at hq
        rw [p4_pre_succ _ _ _ _ _ k hk', p4_pre_succ _ _ _ _ _ k hk', ih (by omega), p4_A_mix,
          p4_B_mix, hq.2, hq.1]
    show p4_tau order init step r _ = p4_tau order init step r x
    funext q
    have hq := congrFun hxy q
    simp only [p4_tau, Prod.mk.injEq] at hq ⊢
    rw [hpre q.val (le_of_lt q.isLt), p4_A_mix, p4_B_mix]
    exact ⟨rfl, by rw [hq.2, hq.1]⟩
def p5_flip {m : ℕ} (i : Fin m) (z : Fin m → Bool) : Fin m → Bool :=
  fun k => if k = i then !z k else z k
theorem p5_flip_flip {m : ℕ} (i : Fin m) (z : Fin m → Bool) : p5_flip i (p5_flip i z) = z := by
  funext k
  unfold p5_flip
  by_cases h : k = i <;> simp [h]
theorem p5_flip_bij {m : ℕ} (i : Fin m) : Function.Bijective (p5_flip i) :=
  Function.Involutive.bijective (p5_flip_flip i)
theorem p5_half {m : ℕ} (i : Fin m) (c : Bool) (Q : (Fin m → Bool) → Prop) [DecidablePred Q]
    (hQ : ∀ z, Q (p5_flip i z) ↔ Q z) :
    2 * (univ.filter (fun z => z i = c ∧ Q z)).card = (univ.filter Q).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := univ.filter Q)
    (fun z : Fin m → Bool => z i = c)
  rw [Finset.filter_filter, Finset.filter_filter] at h1
  have h2 : (univ.filter (fun z => Q z ∧ z i = c)).card =
      (univ.filter (fun z => Q z ∧ ¬ z i = c)).card := by
    apply Finset.card_nbij' (p5_flip i) (p5_flip i)
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      refine ⟨(hQ z).2 hz.1, ?_⟩
      simp only [p5_flip, hz.2]
      cases c <;> simp
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hz ⊢
      refine ⟨(hQ z).2 hz.1, ?_⟩
      simp only [p5_flip]
      cases c <;> cases hzi : z i <;> simp_all
    · intro z _
      exact p5_flip_flip i z
    · intro z _
      exact p5_flip_flip i z
  have h3 : (univ.filter (fun z => z i = c ∧ Q z)) = (univ.filter (fun z => Q z ∧ z i = c)) := by
    apply Finset.filter_congr
    intro z _
    exact And.comm
  rw [h3]
  omega
theorem p5_js_div {O : Type} [Fintype O] (P Q : O → ℝ) (c : ℝ) (hc : c ≠ 0) :
    js (fun x => P x / c) (fun x => Q x / c) = js P Q / c := by
  unfold js
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  have e1 : 2 * (P x / c) / (P x / c + Q x / c) = 2 * P x / (P x + Q x) := by
    rw [← add_div, mul_div_assoc', div_div_div_cancel_right₀ hc]
  have e2 : 2 * (Q x / c) / (P x / c + Q x / c) = 2 * Q x / (P x + Q x) := by
    rw [← add_div, mul_div_assoc', div_div_div_cancel_right₀ hc]
  rw [e1, e2]
  ring
theorem p5_js_prod {A B : Type} [Fintype A] [Fintype B] (F G : A × B → ℝ) :
    js F G = ∑ a, js (fun b => F (a, b)) (fun b => G (a, b)) := by
  unfold js
  rw [Fintype.sum_prod_type]
theorem p5_dc {A Rr T : Type} [Fintype A] [Fintype Rr] [Fintype T] [DecidableEq T]
    (F : Rr → A → T) (E : Rr → T → Prop) [∀ r t, Decidable (E r t)] :
    ∑ p ∈ univ.filter (fun p : Rr × T => E p.1 p.2), (univ.filter (fun z => F p.1 z = p.2)).card =
    ∑ z, (univ.filter (fun r => E r (F r z))).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [← Finset.card_filter, ← Finset.card_filter]
  apply Finset.card_nbij' (fun p => p.1) (fun r => (r, F r z))
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hp ⊢
    rw [hp.2]
    exact hp.1
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hr ⊢
    refine ⟨hr, ?_⟩
    trivial
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hp
    ext
    · rfl
    · exact hp.2
  · intro r _
    rfl
theorem p5_fiber {A T : Type} [Fintype A] [Fintype T] [DecidableEq T] (f : A → T) :
    ∑ t, (univ.filter (fun z => f z = t)).card = Fintype.card A := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (by intro x _; simp)).symm
def p5_al {m : ℕ} (i : Fin m) (d : Fin m → Bool) (u : Bool) (z : Fin m → Bool) : Fin m → Bool :=
  fun k => if k = i then u else (z k && d k)
def p5_be {m : ℕ} (i : Fin m) (d : Fin m → Bool) (v : Bool) (z : Fin m → Bool) : Fin m → Bool :=
  fun k => if k = i then v else (z k && !d k)
noncomputable def p5_L {m R : ℕ} {T : Type} [DecidableEq T]
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T)
    (i : Fin m) (d : Fin m → Bool) (u v : Bool) (p : Fin R × T) : ℝ :=
  ((univ.filter (fun z => τ p.1 (p5_al i d u z) (p5_be i d v z) = p.2)).card : ℝ) / 2 ^ m / R
theorem p5_al_flip {m : ℕ} (i : Fin m) (d : Fin m → Bool) :
    p5_al i (p5_flip i d) = p5_al i d := by
  funext u z k
  unfold p5_al p5_flip
  by_cases hk : k = i <;> simp [hk]
theorem p5_be_flip {m : ℕ} (i : Fin m) (d : Fin m → Bool) :
    p5_be i (p5_flip i d) = p5_be i d := by
  funext u z k
  unfold p5_be p5_flip
  by_cases hk : k = i <;> simp [hk]
theorem p5_al_zflip {m : ℕ} (i : Fin m) (d : Fin m → Bool) (u : Bool) (z : Fin m → Bool) :
    p5_al i d u (p5_flip i z) = p5_al i d u z := by
  funext k
  unfold p5_al p5_flip
  by_cases hk : k = i <;> simp [hk]
theorem p5_be_zflip {m : ℕ} (i : Fin m) (d : Fin m → Bool) (v : Bool) (z : Fin m → Bool) :
    p5_be i d v (p5_flip i z) = p5_be i d v z := by
  funext k
  unfold p5_be p5_flip
  by_cases hk : k = i <;> simp [hk]
theorem p5_L_flip {m R : ℕ} {T : Type} [DecidableEq T]
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (i : Fin m) (d : Fin m → Bool) :
    p5_L τ i (p5_flip i d) = p5_L τ i d := by
  funext u v p
  simp only [p5_L, p5_al_flip, p5_be_flip]
theorem p5_condLaw {m R : ℕ} {T : Type} [DecidableEq T]
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T)
    (i : Fin m) (d : Fin m → Bool) (r : Fin R) (c : Bool) (t : T) :
    condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i c t =
      ((univ.filter (fun z => τ r (p5_al i d (c && d i) z) (p5_be i d (c && !d i) z) = t)).card
        : ℝ) / 2 ^ m := by
  unfold condLaw
  have hm : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
    have h : m = (m - 1) + 1 := by have := i.2; omega
    conv_lhs => rw [h]
    rw [pow_succ]
    ring
  have key : ∀ z : Fin m → Bool, z i = c →
      (fun k => z k && d k) = p5_al i d (c && d i) z ∧
        (fun k => z k && !d k) = p5_be i d (c && !d i) z := by
    intro z hz
    constructor
    · funext k
      unfold p5_al
      by_cases hk : k = i
      · subst hk
        simp [hz]
      · simp [hk]
    · funext k
      unfold p5_be
      by_cases hk : k = i
      · subst hk
        simp [hz]
      · simp [hk]
  have h1 : univ.filter (fun z : Fin m → Bool =>
        z i = c ∧ τ r (fun k => z k && d k) (fun k => z k && !d k) = t) =
      univ.filter (fun z => z i = c ∧ τ r (p5_al i d (c && d i) z) (p5_be i d (c && !d i) z) = t) := by
    apply Finset.filter_congr
    intro z _
    constructor
    · rintro ⟨hz, h⟩
      obtain ⟨ea, eb⟩ := key z hz
      exact ⟨hz, by rw [← ea, ← eb]; exact h⟩
    · rintro ⟨hz, h⟩
      obtain ⟨ea, eb⟩ := key z hz
      exact ⟨hz, by rw [ea, eb]; exact h⟩
  rw [h1]
  have h2 := p5_half i c
    (fun z => τ r (p5_al i d (c && d i) z) (p5_be i d (c && !d i) z) = t) (by
      intro z
      rw [p5_al_zflip, p5_be_zflip])
  rw [← h2, hm]
  push_cast
  rw [mul_div_mul_left _ _ (two_ne_zero)]
theorem p5_G {m R : ℕ} {T : Type} [Fintype T] [DecidableEq T] (hR : 0 < R)
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (i : Fin m) (d : Fin m → Bool) :
    ∑ r, js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
      (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) =
    R * js (p5_L τ i d false false) (p5_L τ i d (d i) (!d i)) := by
  rw [p5_js_prod]
  have hRne : (R : ℝ) ≠ 0 := by positivity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hP : (fun t => p5_L τ i d false false (r, t)) = fun t =>
      condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false t / R := by
    funext t
    rw [p5_condLaw]
    simp only [p5_L, Bool.false_and]
  have hQ : (fun t => p5_L τ i d (d i) (!d i) (r, t)) = fun t =>
      condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true t / R := by
    funext t
    rw [p5_condLaw]
    simp only [p5_L, Bool.true_and]
  rw [hP, hQ, p5_js_div _ _ _ hRne]
  field_simp
theorem p5_L_nonneg {m R : ℕ} {T : Type} [DecidableEq T]
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (i : Fin m) (d : Fin m → Bool) (u v : Bool)
    (p : Fin R × T) : 0 ≤ p5_L τ i d u v p := by
  unfold p5_L
  positivity
theorem p5_L_sum {m R : ℕ} {T : Type} [Fintype T] [DecidableEq T] (hR : 0 < R)
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (i : Fin m) (d : Fin m → Bool) (u v : Bool) :
    ∑ p, p5_L τ i d u v p = 1 := by
  unfold p5_L
  rw [Fintype.sum_prod_type]
  have hRne : (R : ℝ) ≠ 0 := by positivity
  have h : ∀ r : Fin R, ∑ t, ((univ.filter (fun z =>
      τ (r, t).1 (p5_al i d u z) (p5_be i d v z) = (r, t).2)).card : ℝ) / 2 ^ m / R = 1 / R := by
    intro r
    rw [← Finset.sum_div, ← Finset.sum_div, ← Nat.cast_sum,
      p5_fiber (fun z => τ r (p5_al i d u z) (p5_be i d v z))]
    simp
  rw [Finset.sum_congr rfl (fun r _ => h r)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
theorem p5_inter_le {m : ℕ} (i : Fin m) (d : Fin m → Bool) (u v : Bool) (z : Fin m → Bool) :
    inter (p5_al i d u z) (p5_be i d v z) ≤ 1 := by
  unfold inter
  have hs : univ.filter (fun k : Fin m => p5_al i d u z k = true ∧ p5_be i d v z k = true) ⊆
      {i} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [Finset.mem_singleton]
    by_contra hki
    simp only [p5_al, p5_be, hki, ite_false] at hk
    cases hd : d k <;> simp_all
  calc _ ≤ ({i} : Finset (Fin m)).card := Finset.card_le_card hs
    _ = 1 := Finset.card_singleton i
theorem p5_exists_iff {m : ℕ} (i : Fin m) (d : Fin m → Bool) (u v : Bool) (z : Fin m → Bool) :
    (∃ k, p5_al i d u z k = true ∧ p5_be i d v z k = true) ↔ (u = true ∧ v = true) := by
  constructor
  · rintro ⟨k, h1, h2⟩
    by_cases hki : k = i
    · subst hki
      simp only [p5_al, p5_be, ite_true] at h1 h2
      exact ⟨h1, h2⟩
    · simp only [p5_al, p5_be, hki, ite_false] at h1 h2
      cases hd : d k <;> simp_all
  · rintro ⟨hu, hv⟩
    exact ⟨i, by simp [p5_al, hu], by simp [p5_be, hv]⟩
theorem p5_bound0 {m R : ℕ} {T : Type}
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (o : Fin R → T → Bool)
    (hcorr : ∀ a b : Fin m → Bool, inter a b ≤ 1 →
      2 * R ≤ 3 * (Finset.univ.filter (fun r : Fin R =>
        (o r (τ r a b) = true ↔ ∃ k, a k = true ∧ b k = true))).card)
    (i : Fin m) (d : Fin m → Bool) (z : Fin m → Bool) :
    3 * (univ.filter (fun r => o r (τ r (p5_al i d false z) (p5_be i d false z)) = true)).card
      ≤ R := by
  have h := hcorr (p5_al i d false z) (p5_be i d false z) (p5_inter_le i d false false z)
  have e : univ.filter (fun r : Fin R => (o r (τ r (p5_al i d false z) (p5_be i d false z)) = true ↔
      ∃ k, p5_al i d false z k = true ∧ p5_be i d false z k = true)) =
      univ.filter (fun r => ¬ o r (τ r (p5_al i d false z) (p5_be i d false z)) = true) := by
    apply Finset.filter_congr
    intro r _
    rw [p5_exists_iff]
    simp
  rw [e] at h
  have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin R)))
    (fun r => o r (τ r (p5_al i d false z) (p5_be i d false z)) = true)
  rw [Finset.card_univ, Fintype.card_fin] at h2
  omega
theorem p5_bound1 {m R : ℕ} {T : Type}
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (o : Fin R → T → Bool)
    (hcorr : ∀ a b : Fin m → Bool, inter a b ≤ 1 →
      2 * R ≤ 3 * (Finset.univ.filter (fun r : Fin R =>
        (o r (τ r a b) = true ↔ ∃ k, a k = true ∧ b k = true))).card)
    (i : Fin m) (d : Fin m → Bool) (z : Fin m → Bool) :
    2 * R ≤
      3 * (univ.filter (fun r => o r (τ r (p5_al i d true z) (p5_be i d true z)) = true)).card := by
  have h := hcorr (p5_al i d true z) (p5_be i d true z) (p5_inter_le i d true true z)
  have e : univ.filter (fun r : Fin R => (o r (τ r (p5_al i d true z) (p5_be i d true z)) = true ↔
      ∃ k, p5_al i d true z k = true ∧ p5_be i d true z k = true)) =
      univ.filter (fun r => o r (τ r (p5_al i d true z) (p5_be i d true z)) = true) := by
    apply Finset.filter_congr
    intro r _
    rw [p5_exists_iff]
    simp
  rw [e] at h
  exact h
theorem p5_pair {m R : ℕ} {T : Type} [Fintype T] [DecidableEq T] (hR : 0 < R)
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (o : Fin R → T → Bool)
    (hrect : ∀ r a a' b b', τ r a b = τ r a' b' → τ r a b' = τ r a b)
    (hcorr : ∀ a b : Fin m → Bool, inter a b ≤ 1 →
      2 * R ≤ 3 * (Finset.univ.filter (fun r : Fin R =>
        (o r (τ r a b) = true ↔ ∃ k, a k = true ∧ b k = true))).card)
    (i : Fin m) (d : Fin m → Bool) :
    1 / 80 ≤ js (p5_L τ i d false false) (p5_L τ i d true false) +
      js (p5_L τ i d false false) (p5_L τ i d false true) := by
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  refine B2_hellinger _ _ _ (p5_L τ i d true true) (p5_L_nonneg τ i d false false)
    (p5_L_nonneg τ i d true false) (p5_L_nonneg τ i d false true) (p5_L_nonneg τ i d true true)
    (p5_L_sum hR τ i d false false) (p5_L_sum hR τ i d true false)
    (p5_L_sum hR τ i d false true) (p5_L_sum hR τ i d true true) ?_
    (fun p : Fin R × T => o p.1 p.2 = true) ?_ ?_
  · intro p
    have hα : ∀ (u : Bool) (z z' : Fin m → Bool), (∀ k, d k = true → z k = z' k) →
        p5_al i d u z = p5_al i d u z' := by
      intro u z z' h
      funext k
      unfold p5_al
      by_cases hk : k = i
      · simp [hk]
      · cases hd : d k
        · simp [hk]
        · simp [hk, h k hd]
    have hβ : ∀ (v : Bool) (z z' : Fin m → Bool), (∀ k, d k = false → z k = z' k) →
        p5_be i d v z = p5_be i d v z' := by
      intro v z z' h
      funext k
      unfold p5_be
      by_cases hk : k = i
      · simp [hk]
      · cases hd : d k
        · simp [hk, h k hd]
        · simp [hk]
    have h := B3a_cutpaste (τ p.1) (hrect p.1) d (p5_al i d) (p5_be i d) hα hβ p.2
    have h' : ((univ.filter (fun z => τ p.1 (p5_al i d false z) (p5_be i d false z) = p.2)).card
        : ℝ) * ((univ.filter (fun z => τ p.1 (p5_al i d true z) (p5_be i d true z) = p.2)).card
        : ℝ) =
        ((univ.filter (fun z => τ p.1 (p5_al i d true z) (p5_be i d false z) = p.2)).card : ℝ) *
        ((univ.filter (fun z => τ p.1 (p5_al i d false z) (p5_be i d true z) = p.2)).card
        : ℝ) := by
      exact_mod_cast h
    unfold p5_L
    rw [div_div, div_div, div_div, div_div, div_mul_div_comm, div_mul_div_comm, h']
  · have hN : 3 * ∑ p ∈ univ.filter (fun p : Fin R × T => o p.1 p.2 = true),
        (univ.filter (fun z => τ p.1 (p5_al i d false z) (p5_be i d false z) = p.2)).card ≤
        2 ^ m * R := by
      rw [p5_dc (fun r z => τ r (p5_al i d false z) (p5_be i d false z))
        (fun r t => o r t = true), Finset.mul_sum]
      calc _ ≤ ∑ z : Fin m → Bool, R :=
            Finset.sum_le_sum (fun z _ => p5_bound0 τ o hcorr i d z)
        _ = 2 ^ m * R := by
          rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
    unfold p5_L
    rw [← Finset.sum_div, ← Finset.sum_div, ← Nat.cast_sum, div_div, mul_div_assoc',
      div_le_one (by positivity)]
    exact_mod_cast hN
  · have hN : 2 * (2 ^ m * R) ≤ 3 * ∑ p ∈ univ.filter (fun p : Fin R × T => o p.1 p.2 = true),
        (univ.filter (fun z => τ p.1 (p5_al i d true z) (p5_be i d true z) = p.2)).card := by
      rw [p5_dc (fun r z => τ r (p5_al i d true z) (p5_be i d true z))
        (fun r t => o r t = true), Finset.mul_sum]
      calc 2 * (2 ^ m * R) = ∑ z : Fin m → Bool, 2 * R := by
            rw [Finset.sum_const, Finset.card_univ, hcard, smul_eq_mul]
            ring
        _ ≤ _ := Finset.sum_le_sum (fun z _ => p5_bound1 τ o hcorr i d z)
    unfold p5_L
    rw [← Finset.sum_div, ← Finset.sum_div, ← Nat.cast_sum, div_div, mul_div_assoc',
      le_div_iff₀ (by positivity)]
    exact_mod_cast hN
theorem p5_sumd {m R : ℕ} {T : Type} [Fintype T] [DecidableEq T] (hR : 0 < R)
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (o : Fin R → T → Bool)
    (hrect : ∀ r a a' b b', τ r a b = τ r a' b' → τ r a b' = τ r a b)
    (hcorr : ∀ a b : Fin m → Bool, inter a b ≤ 1 →
      2 * R ≤ 3 * (Finset.univ.filter (fun r : Fin R =>
        (o r (τ r a b) = true ↔ ∃ k, a k = true ∧ b k = true))).card)
    (i : Fin m) :
    (2 : ℝ) ^ m * R / 160 ≤ ∑ d : Fin m → Bool, ∑ r,
      js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
        (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) := by
  set G : (Fin m → Bool) → ℝ := fun d => ∑ r,
      js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
        (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) with hG
  have hGd : ∀ d, G d = R * js (p5_L τ i d false false) (p5_L τ i d (d i) (!d i)) :=
    fun d => p5_G hR τ i d
  have hsum : ∑ d, G d = ∑ d, G (p5_flip i d) :=
    (Fintype.sum_bijective (p5_flip i) (p5_flip_bij i) (fun d => G (p5_flip i d)) G
      (fun _ => rfl)).symm
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have hpair : ∀ d, (R : ℝ) / 80 ≤ G d + G (p5_flip i d) := by
    intro d
    rw [hGd d, hGd (p5_flip i d), p5_L_flip]
    have hfi : p5_flip i d i = !d i := by simp [p5_flip]
    rw [hfi, Bool.not_not]
    have h := p5_pair hR τ o hrect hcorr i d
    cases hdi : d i
    · simp only [Bool.not_false]
      nlinarith
    · simp only [Bool.not_true]
      nlinarith
  have h2 : (2 : ℝ) * ∑ d, G d = ∑ d, (G d + G (p5_flip i d)) := by
    rw [Finset.sum_add_distrib, ← hsum]
    ring
  have h3 : ∑ d : Fin m → Bool, (R : ℝ) / 80 ≤ ∑ d, (G d + G (p5_flip i d)) :=
    Finset.sum_le_sum (fun d _ => hpair d)
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul] at h3
  push_cast at h3
  linarith
theorem B_core (m R : ℕ) (T : Type) [Fintype T] (hR : 0 < R)
    (τ : Fin R → (Fin m → Bool) → (Fin m → Bool) → T) (o : Fin R → T → Bool)
    (hrect : ∀ r a a' b b', τ r a b = τ r a' b' → τ r a b' = τ r a b)
    (hcorr : ∀ a b : Fin m → Bool, inter a b ≤ 1 →
      2 * R ≤ 3 * (Finset.univ.filter (fun r : Fin R =>
        (o r (τ r a b) = true ↔ ∃ k, a k = true ∧ b k = true))).card) :
    (m : ℝ) ≤ 160 * Real.log (Fintype.card T) := by
  classical
  have hRpos : (0 : ℝ) < R := by exact_mod_cast hR
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hcard : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  have hup : ∑ d : Fin m → Bool, ∑ r : Fin R, ∑ i : Fin m,
      js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
        (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) ≤
      2 ^ m * R * Real.log (Fintype.card T) := by
    calc _ ≤ ∑ d : Fin m → Bool, ∑ r : Fin R, Real.log (Fintype.card T) :=
          Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun r _ => B1_info _))
      _ = 2 ^ m * R * Real.log (Fintype.card T) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, hcard,
            Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
          push_cast
          ring
  have hswap : ∑ d : Fin m → Bool, ∑ r : Fin R, ∑ i : Fin m,
      js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
        (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) =
      ∑ i : Fin m, ∑ d : Fin m → Bool, ∑ r : Fin R,
      js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
        (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) := by
    calc _ = ∑ d : Fin m → Bool, ∑ i : Fin m, ∑ r : Fin R,
              js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
                (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) :=
          Finset.sum_congr rfl (fun d _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hlow : ∑ i : Fin m, (2 : ℝ) ^ m * R / 160 ≤ ∑ i : Fin m, ∑ d : Fin m → Bool, ∑ r : Fin R,
      js (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i false)
        (condLaw (fun z => τ r (fun k => z k && d k) (fun k => z k && !d k)) i true) :=
    Finset.sum_le_sum (fun i _ => p5_sumd hR τ o hrect hcorr i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlow
  have hfin : (m : ℝ) * (2 ^ m * R / 160) ≤ 2 ^ m * R * Real.log (Fintype.card T) := by
    linarith
  have hpos : (0 : ℝ) < 2 ^ m * R := by positivity
  nlinarith
def p6_conf {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (t : Fin n) : Finset (Fin n) :=
  insert t ((univ.erase j0).image (fun j => M j ((M j0).symm t)) ∪
    (univ.erase j0).image (fun j => M j0 ((M j).symm t)))
theorem p6_conf_card {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (t : Fin n) :
    (p6_conf M j0 t).card ≤ 5 := by
  unfold p6_conf
  refine (card_insert_le _ _).trans ?_
  have h1 := card_union_le ((univ.erase j0).image (fun j => M j ((M j0).symm t)))
    ((univ.erase j0).image (fun j => M j0 ((M j).symm t)))
  have h2 : ((univ.erase j0).image (fun j => M j ((M j0).symm t))).card ≤ 2 :=
    card_image_le.trans (by simp)
  have h3 : ((univ.erase j0).image (fun j => M j0 ((M j).symm t))).card ≤ 2 :=
    card_image_le.trans (by simp)
  omega
def p6_bad {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (G : Finset (Fin n)) :
    Finset (Fin n) :=
  (univ.biUnion fun j => G.image (M j)) ∪
    ((univ.erase j0).biUnion fun j => (univ.filter (fun i => M j0 i = M j i)).image (M j0))
theorem p6_bad_card {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3)
    (hagree : ∀ j j' : Fin 3, j ≠ j' → 8 * agreeCount M j j' ≤ n) (G : Finset (Fin n)) :
    4 * (p6_bad M j0 G).card ≤ 12 * G.card + n := by
  unfold p6_bad
  have h1 : (univ.biUnion fun j => G.image (M j)).card ≤ 3 * G.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ j : Fin 3, (G.image (M j)).card ≤ ∑ _j : Fin 3, G.card :=
          sum_le_sum (fun j _ => card_image_le)
      _ = 3 * G.card := by simp
  have h2 : 8 * ((univ.erase j0).biUnion fun j =>
      (univ.filter (fun i => M j0 i = M j i)).image (M j0)).card ≤ 2 * n := by
    have h3 := card_biUnion_le (s := univ.erase j0)
      (t := fun j => (univ.filter (fun i => M j0 i = M j i)).image (M j0))
    have h4 : ∑ j ∈ univ.erase j0, ((univ.filter (fun i => M j0 i = M j i)).image (M j0)).card ≤
        ∑ j ∈ univ.erase j0, agreeCount M j0 j :=
      sum_le_sum (fun j _ => card_image_le)
    have h5 : 8 * ∑ j ∈ univ.erase j0, agreeCount M j0 j ≤ 2 * n := by
      rw [mul_sum]
      calc ∑ j ∈ univ.erase j0, 8 * agreeCount M j0 j ≤ ∑ _j ∈ univ.erase j0, n :=
            sum_le_sum (fun j hj => hagree j0 j (ne_of_mem_erase hj).symm)
        _ = 2 * n := by simp
    omega
  have h6 := card_union_le (univ.biUnion fun j => G.image (M j))
    ((univ.erase j0).biUnion fun j => (univ.filter (fun i => M j0 i = M j i)).image (M j0))
  omega
theorem p6_not_bad {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (G : Finset (Fin n))
    (t : Fin n) (ht : t ∉ p6_bad M j0 G) :
    (∀ j : Fin 3, (M j).symm t ∉ G) ∧ (∀ j : Fin 3, j ≠ j0 → (M j0).symm t ≠ (M j).symm t) := by
  unfold p6_bad at ht
  constructor
  · intro j hj
    apply ht
    apply mem_union_left
    rw [mem_biUnion]
    exact ⟨j, mem_univ _, mem_image.2 ⟨_, hj, by simp⟩⟩
  · intro j hj heq
    apply ht
    apply mem_union_right
    rw [mem_biUnion]
    refine ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩,
      mem_image.2 ⟨(M j0).symm t, mem_filter.2 ⟨mem_univ _, ?_⟩, by simp⟩⟩
    rw [Equiv.apply_symm_apply, heq, Equiv.apply_symm_apply]
theorem p6_greedy_aux {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (B : Finset (Fin n)) :
    ∀ k : ℕ, B.card + 5 * k ≤ n → ∃ H : Finset (Fin n), H.card = k ∧ (∀ t ∈ H, t ∉ B) ∧
      (∀ t ∈ H, ∀ t' ∈ H, t ≠ t' → ∀ j : Fin 3, j ≠ j0 → (M j0).symm t ≠ (M j).symm t') := by
  intro k
  induction k with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨H, hHc, hHB, hHp⟩ := ih (by omega)
    have hFc : (B ∪ H.biUnion (p6_conf M j0)).card < (univ : Finset (Fin n)).card := by
      have h1 := card_union_le B (H.biUnion (p6_conf M j0))
      have h2 : (H.biUnion (p6_conf M j0)).card ≤ 5 * k := by
        refine card_biUnion_le.trans ?_
        calc ∑ t ∈ H, (p6_conf M j0 t).card ≤ ∑ _t ∈ H, 5 :=
              sum_le_sum (fun t _ => p6_conf_card M j0 t)
          _ = 5 * k := by rw [sum_const, hHc, smul_eq_mul, mul_comm]
      rw [card_univ, Fintype.card_fin]
      omega
    obtain ⟨t, -, htF⟩ := exists_mem_notMem_of_card_lt_card hFc
    have htH : t ∉ H := fun h =>
      htF (mem_union_right _ (mem_biUnion.2 ⟨t, h, by unfold p6_conf; exact mem_insert_self _ _⟩))
    have htB : t ∉ B := fun h => htF (mem_union_left _ h)
    refine ⟨insert t H, by rw [card_insert_of_notMem htH, hHc], ?_, ?_⟩
    · intro t1 ht1
      rcases mem_insert.1 ht1 with h1 | h1
      · rw [h1]; exact htB
      · exact hHB t1 h1
    · intro t1 ht1 t2 ht2 hne j hj heq
      rcases mem_insert.1 ht1 with h1 | h1 <;> rcases mem_insert.1 ht2 with h2 | h2
      · exact hne (h1.trans h2.symm)
      · rw [h1] at heq
        apply htF
        apply mem_union_right
        refine mem_biUnion.2 ⟨t2, h2, ?_⟩
        unfold p6_conf
        refine mem_insert_of_mem (mem_union_right _
          (mem_image.2 ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩, ?_⟩))
        show M j0 ((M j).symm t2) = t
        rw [← heq, Equiv.apply_symm_apply]
      · rw [h2] at heq
        apply htF
        apply mem_union_right
        refine mem_biUnion.2 ⟨t1, h1, ?_⟩
        unfold p6_conf
        refine mem_insert_of_mem (mem_union_left _
          (mem_image.2 ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩, ?_⟩))
        show M j ((M j0).symm t1) = t
        rw [heq, Equiv.apply_symm_apply]
      · exact hHp t1 h1 t2 h2 hne j hj heq
theorem C_greedy (n : ℕ) (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3)
    (hagree : ∀ j j' : Fin 3, j ≠ j' → 8 * agreeCount M j j' ≤ n)
    (G : Finset (Fin n)) (h : ℕ) (hsize : 20 * h + 12 * G.card ≤ 3 * n) :
    ∃ H : Finset (Fin n), H.card = h ∧
      (∀ t ∈ H, ∀ j : Fin 3, (M j).symm t ∉ G) ∧
      (∀ t ∈ H, ∀ t' ∈ H, ∀ j : Fin 3, j ≠ j0 → (M j0).symm t ≠ (M j).symm t') := by
  have hB := p6_bad_card M j0 hagree G
  obtain ⟨H, hHc, hHB, hHp⟩ := p6_greedy_aux M j0 (p6_bad M j0 G) h (by omega)
  refine ⟨H, hHc, fun t ht => (p6_not_bad M j0 G t (hHB t ht)).1, ?_⟩
  intro t ht t' ht' j hj
  by_cases htt : t = t'
  · rw [← htt]
    exact (p6_not_bad M j0 G t (hHB t ht)).2 j hj
  · exact hHp t ht t' ht' htt j hj
def p6_u (l : Fin 3) (a : Bool) : Bool := if l = 0 then !a else if l = 1 then a else false
def p6_w (l : Fin 3) (b : Bool) : Bool := if l = 0 then false else if l = 1 then b else !b
theorem p6_gadget_pt (x y : Bool) :
    (∑ l : Fin 3, if p6_u l x ≠ p6_w l y then 1 else 0) +
      2 * (if x = true ∧ y = true then 1 else 0) = 2 := by
  rw [Fin.sum_univ_three]
  cases x <;> cases y <;> decide
theorem p6_gadget_count {m : ℕ} (a b : Fin m → Bool) :
    (univ.filter (fun c : Fin m × Fin 3 => p6_u c.2 (a c.1) ≠ p6_w c.2 (b c.1))).card
      + 2 * inter a b = 2 * m := by
  unfold inter
  rw [card_filter, card_filter, Fintype.sum_prod_type, mul_sum, ← sum_add_distrib]
  rw [sum_const_nat (fun k _ => p6_gadget_pt (a k) (b k))]
  simp [mul_comm]
def p6_idx {n : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (v : Bool × Fin n) : Fin n :=
  if v.1 then (M j0).symm v.2 else v.2
def p6_enc {n m : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3) (S : Finset (Bool × Fin n))
    (G Q H : Finset (Fin n)) (κ : Fin n → Fin m × Fin 3) (a b : Fin m → Bool)
    (v : Bool × Fin n) : Bool :=
  if p6_idx M j0 v ∈ G then
    (if v ∈ S then p6_u (κ (p6_idx M j0 v)).2 (a (κ (p6_idx M j0 v)).1)
      else p6_w (κ (p6_idx M j0 v)).2 (b (κ (p6_idx M j0 v)).1))
  else (if v.1 then decide (v.2 ∈ H) else decide (v.2 ∈ Q))
theorem p6_enc_f_out {n m : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3)
    (S : Finset (Bool × Fin n)) (G Q H : Finset (Fin n)) (κ : Fin n → Fin m × Fin 3)
    (a b : Fin m → Bool) (i : Fin n) (hi : i ∉ G) :
    p6_enc M j0 S G Q H κ a b (false, i) = decide (i ∈ Q) := by
  simp [p6_enc, p6_idx, hi]
theorem p6_enc_t_out {n m : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3)
    (S : Finset (Bool × Fin n)) (G Q H : Finset (Fin n)) (κ : Fin n → Fin m × Fin 3)
    (a b : Fin m → Bool) (t : Fin n) (ht : (M j0).symm t ∉ G) :
    p6_enc M j0 S G Q H κ a b (true, t) = decide (t ∈ H) := by
  simp [p6_enc, p6_idx, ht]
theorem p6_enc_gad {n m : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3)
    (S : Finset (Bool × Fin n)) (G Q H : Finset (Fin n)) (κ : Fin n → Fin m × Fin 3)
    (a b : Fin m → Bool) (i : Fin n) (hi : i ∈ G)
    (hsplit : (false, i) ∈ S ↔ (true, M j0 i) ∉ S) :
    (p6_enc M j0 S G Q H κ a b (false, i) ≠ p6_enc M j0 S G Q H κ a b (true, M j0 i)) ↔
      p6_u (κ i).2 (a (κ i).1) ≠ p6_w (κ i).2 (b (κ i).1) := by
  by_cases h1 : (false, i) ∈ S
  · have h2 : (true, M j0 i) ∉ S := hsplit.1 h1
    simp [p6_enc, p6_idx, hi, h1, h2]
  · have h2 : (true, M j0 i) ∈ S := by
      by_contra h2
      exact h1 (hsplit.2 h2)
    simp only [p6_enc, p6_idx, hi, h1, h2, Equiv.symm_apply_apply, ite_true, ite_false,
      Bool.false_eq_true]
    exact ne_comm
theorem p6_card_le_of_agree {n : ℕ} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (F : Finset (Fin n)) (h : ∀ i, i ∉ F → (p i ↔ q i)) :
    (univ.filter p).card ≤ (univ.filter q).card + F.card := by
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro i hi
  rw [mem_union]
  by_cases hiF : i ∈ F
  · exact Or.inr hiF
  · exact Or.inl (mem_filter.2 ⟨mem_univ _, (h i hiF).1 (mem_filter.1 hi).2⟩)
theorem p6_card_preim {n : ℕ} (σ : Fin n ≃ Fin n) (H : Finset (Fin n)) :
    (univ.filter (fun i => σ i ∈ H)).card = H.card := by
  rw [card_filter, Equiv.sum_comp σ (fun t => if t ∈ H then 1 else 0), ← card_filter,
    filter_mem_eq_inter, univ_inter]
theorem p6_D0 {n m : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 : Fin 3)
    (S : Finset (Bool × Fin n)) (G Q H : Finset (Fin n)) (κ : Fin n → Fin m × Fin 3)
    (φ : Fin m × Fin 3 → Fin n) (hφ : Function.Injective φ) (hG : G = univ.image φ)
    (hκ : ∀ c, κ (φ c) = c)
    (hGP : ∀ i ∈ G, ((false, i) ∈ S ↔ (true, M j0 i) ∉ S))
    (hQG : ∀ i ∈ Q, i ∉ G) (hHG : ∀ t ∈ H, (M j0).symm t ∉ G)
    (hHQ : ∀ t ∈ H, (M j0).symm t ∉ Q) (a b : Fin m → Bool) :
    (univ.filter (fun i => p6_enc M j0 S G Q H κ a b (false, i) ≠
      p6_enc M j0 S G Q H κ a b (true, M j0 i))).card + 2 * inter a b =
      2 * m + Q.card + H.card := by
  have hset : univ.filter (fun i => p6_enc M j0 S G Q H κ a b (false, i) ≠
      p6_enc M j0 S G Q H κ a b (true, M j0 i)) =
      (univ.filter (fun c : Fin m × Fin 3 => p6_u c.2 (a c.1) ≠ p6_w c.2 (b c.1))).image φ ∪
      (Q ∪ H.image (M j0).symm) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_union, mem_image]
    by_cases hi : i ∈ G
    · have hi' := hi
      rw [hG, mem_image] at hi'
      obtain ⟨c, -, rfl⟩ := hi'
      rw [p6_enc_gad M j0 S G Q H κ a b (φ c) hi (hGP _ hi), hκ c]
      constructor
      · intro h
        exact Or.inl ⟨c, h, rfl⟩
      · rintro (⟨c', hc', he⟩ | hQ | ⟨t, ht, he⟩)
        · rw [hφ he] at hc'
          exact hc'
        · exact absurd hi (hQG _ hQ)
        · rw [← he] at hi
          exact absurd hi (hHG t ht)
    · rw [p6_enc_f_out M j0 S G Q H κ a b i hi,
        p6_enc_t_out M j0 S G Q H κ a b (M j0 i) (by simpa using hi)]
      constructor
      · intro h
        by_cases hq : i ∈ Q
        · exact Or.inr (Or.inl hq)
        · right
          right
          refine ⟨M j0 i, ?_, by simp⟩
          by_contra hh
          simp [hq, hh] at h
      · rintro (⟨c', -, he⟩ | hQ | ⟨t, ht, he⟩)
        · exact absurd (hG ▸ mem_image.2 ⟨c', mem_univ _, he⟩) hi
        · have : M j0 i ∉ H := fun hh => hHQ _ hh (by simpa using hQ)
          simp [hQ, this]
        · have hq : i ∉ Q := fun hq => hHQ t ht (he ▸ hq)
          have : M j0 i ∈ H := by
            rw [← he]
            simpa using ht
          simp [hq, this]
  have hd1 : Disjoint Q (H.image (M j0).symm) := by
    rw [disjoint_left]
    intro i hq hi
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hi
    exact hHQ t ht hq
  have hd2 : Disjoint
      ((univ.filter (fun c : Fin m × Fin 3 => p6_u c.2 (a c.1) ≠ p6_w c.2 (b c.1))).image φ)
      (Q ∪ H.image (M j0).symm) := by
    rw [disjoint_left]
    intro i h1 h2
    obtain ⟨c, -, rfl⟩ := mem_image.1 h1
    have hc : φ c ∈ G := by
      rw [hG]
      exact mem_image_of_mem _ (mem_univ _)
    rcases mem_union.1 h2 with h2 | h2
    · exact hQG _ h2 hc
    · obtain ⟨t, ht, he⟩ := mem_image.1 h2
      rw [← he] at hc
      exact hHG t ht hc
  rw [hset, card_union_of_disjoint hd2, card_union_of_disjoint hd1, card_image_of_injective _ hφ,
    card_image_of_injective _ (M j0).symm.injective]
  have := p6_gadget_count a b
  omega
theorem p6_Dj {n m : ℕ} (M : Fin 3 → Equiv.Perm (Fin n)) (j0 j : Fin 3)
    (S : Finset (Bool × Fin n)) (G Q H : Finset (Fin n)) (κ : Fin n → Fin m × Fin 3)
    (a b : Fin m → Bool) (hHQ : ∀ t ∈ H, (M j).symm t ∈ Q) :
    (univ.filter (fun i => p6_enc M j0 S G Q H κ a b (false, i) ≠
      p6_enc M j0 S G Q H κ a b (true, M j i))).card + H.card ≤ Q.card + 2 * G.card ∧
    Q.card ≤ (univ.filter (fun i => p6_enc M j0 S G Q H κ a b (false, i) ≠
      p6_enc M j0 S G Q H κ a b (true, M j i))).card + H.card + 2 * G.card := by
  have hF : (G ∪ univ.filter (fun i => (M j0).symm (M j i) ∈ G)).card ≤ 2 * G.card := by
    have h1 := card_union_le G (univ.filter (fun i => (M j0).symm (M j i) ∈ G))
    have h2 : (univ.filter (fun i => (M j0).symm (M j i) ∈ G)).card = G.card :=
      p6_card_preim ((M j).trans (M j0).symm) G
    omega
  have hy : (univ.filter (fun i => decide (i ∈ Q) ≠ decide (M j i ∈ H))).card + H.card =
      Q.card := by
    have hd : Disjoint (univ.filter (fun i => decide (i ∈ Q) ≠ decide (M j i ∈ H)))
        (univ.filter (fun i => M j i ∈ H)) := by
      rw [disjoint_left]
      intro i h1 h2
      simp only [mem_filter, mem_univ, true_and] at h1 h2
      have hq : i ∈ Q := by simpa using hHQ _ h2
      simp [hq, h2] at h1
    rw [← p6_card_preim (M j) H, ← card_union_of_disjoint hd]
    congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and]
    constructor
    · rintro (h | h)
      · by_contra hq
        have : M j i ∈ H := by simpa [hq] using h
        exact hq (by simpa using hHQ _ this)
      · simpa using hHQ _ h
    · intro hq
      by_cases hh : M j i ∈ H
      · exact Or.inr hh
      · left
        simp [hq, hh]
  have hagr : ∀ i, i ∉ G ∪ univ.filter (fun i => (M j0).symm (M j i) ∈ G) →
      ((p6_enc M j0 S G Q H κ a b (false, i) ≠ p6_enc M j0 S G Q H κ a b (true, M j i)) ↔
        (decide (i ∈ Q) ≠ decide (M j i ∈ H))) := by
    intro i hi
    simp only [mem_union, mem_filter, mem_univ, true_and, not_or] at hi
    rw [p6_enc_f_out M j0 S G Q H κ a b i hi.1, p6_enc_t_out M j0 S G Q H κ a b (M j i) hi.2]
  have h1 := p6_card_le_of_agree _ _ _ hagr
  have h2 := p6_card_le_of_agree _ _ _ (fun i hi => (hagr i hi).symm)
  omega
theorem C_embed (n : ℕ) (hn : 4096 ≤ n) (M : Fin 3 → Equiv.Perm (Fin n))
    (hagree : ∀ j j' : Fin 3, j ≠ j' → 8 * agreeCount M j j' ≤ n)
    (S : Finset (Bool × Fin n)) (j0 : Fin 3) (hj0 : n ≤ 40 * splitCount M j0 S) :
    ∃ e : (Fin (n/256) → Bool) → (Fin (n/256) → Bool) → (Bool × Fin n → Bool),
      (∀ a b b' v, v ∈ S → e a b v = e a b' v) ∧
      (∀ a a' b v, v ∉ S → e a b v = e a' b v) ∧
      (∀ a b, inter a b ≤ 1 → (acc M (e a b) ↔ ∃ k, a k = true ∧ b k = true)) := by
  have hP : n ≤ 40 * (univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, M j0 i) ∉ S))).card :=
    hj0
  obtain ⟨emb⟩ : Nonempty (Fin (n/256) × Fin 3 ↪
      {i // i ∈ univ.filter (fun i : Fin n => ((false, i) ∈ S ↔ (true, M j0 i) ∉ S))}) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe]
    omega
  have hφ : Function.Injective (fun c => (emb c).1) := fun c c' h => emb.injective (Subtype.ext h)
  have hφP : ∀ c, ((false, (emb c).1) ∈ S ↔ (true, M j0 (emb c).1) ∉ S) :=
    fun c => (mem_filter.1 (emb c).2).2
  have : Nonempty (Fin (n/256) × Fin 3) := ⟨(⟨0, by omega⟩, 0)⟩
  have hκ : ∀ c, Function.invFun (fun c => (emb c).1) ((emb c).1) = c :=
    Function.leftInverse_invFun hφ
  have hGc : (univ.image (fun c => (emb c).1)).card = 3 * (n/256) := by
    rw [card_image_of_injective _ hφ, card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, mul_comm]
  have hGP : ∀ i ∈ univ.image (fun c => (emb c).1), ((false, i) ∈ S ↔ (true, M j0 i) ∉ S) := by
    intro i hi
    obtain ⟨c, -, rfl⟩ := mem_image.1 hi
    exact hφP c
  obtain ⟨H, hHc, hHG, hHconf⟩ := C_greedy n M j0 hagree (univ.image (fun c => (emb c).1))
    (2 * (n/256) + 1) (by rw [hGc]; omega)
  have hP1R : (univ.erase j0).biUnion (fun j => H.image (M j).symm) ⊆
      univ \ (univ.image (fun c => (emb c).1) ∪ H.image (M j0).symm) := by
    intro i hi
    obtain ⟨j, hj, hi⟩ := mem_biUnion.1 hi
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hi
    rw [mem_sdiff]
    refine ⟨mem_univ _, ?_⟩
    rw [mem_union, not_or]
    refine ⟨hHG t ht j, ?_⟩
    intro h'
    obtain ⟨t', ht', he⟩ := mem_image.1 h'
    exact hHconf t' ht' t ht j (ne_of_mem_erase hj) he
  have hP1c : ((univ.erase j0).biUnion (fun j => H.image (M j).symm)).card ≤ 2 * H.card := by
    refine card_biUnion_le.trans ?_
    calc ∑ j ∈ univ.erase j0, (H.image (M j).symm).card ≤ ∑ _j ∈ univ.erase j0, H.card :=
          sum_le_sum (fun j _ => card_image_le)
      _ = 2 * H.card := by simp
  have hRc : n ≤ (univ \ (univ.image (fun c => (emb c).1) ∪ H.image (M j0).symm)).card +
      (univ.image (fun c => (emb c).1)).card + H.card := by
    rw [card_univ_sdiff, Fintype.card_fin]
    have h2 := card_union_le (univ.image (fun c => (emb c).1)) (H.image (M j0).symm)
    have h3 : (H.image (M j0).symm).card ≤ H.card := card_image_le
    omega
  obtain ⟨Q, hP1Q, hQR, hQc⟩ := exists_subsuperset_card_eq hP1R
    (n := 17 * n / 32 + 1 - 4 * (n / 256)) (by omega) (by omega)
  have hQG : ∀ i ∈ Q, i ∉ univ.image (fun c => (emb c).1) := by
    intro i hi hG
    have := hQR hi
    rw [mem_sdiff, mem_union, not_or] at this
    exact this.2.1 hG
  have hHQ0 : ∀ t ∈ H, (M j0).symm t ∉ Q := by
    intro t ht hq
    have := hQR hq
    rw [mem_sdiff, mem_union, not_or] at this
    exact this.2.2 (mem_image_of_mem _ ht)
  have hHQj : ∀ j, j ≠ j0 → ∀ t ∈ H, (M j).symm t ∈ Q := by
    intro j hj t ht
    exact hP1Q (mem_biUnion.2 ⟨j, mem_erase.2 ⟨hj, mem_univ _⟩, mem_image_of_mem _ ht⟩)
  refine ⟨fun a b => p6_enc M j0 S (univ.image (fun c => (emb c).1)) Q H
    (Function.invFun (fun c => (emb c).1)) a b, ?_, ?_, ?_⟩
  · intro a b b' v hv
    simp only [p6_enc, hv, ite_true]
  · intro a a' b v hv
    simp only [p6_enc, hv, ite_false]
  · intro a b hab
    beta_reduce
    have h0 := p6_D0 M j0 S (univ.image (fun c => (emb c).1)) Q H
      (Function.invFun (fun c => (emb c).1)) (fun c => (emb c).1) hφ rfl hκ hGP hQG
      (fun t ht => hHG t ht j0) hHQ0 a b
    have hint : (∃ k, a k = true ∧ b k = true) ↔ 0 < inter a b := by
      unfold inter
      rw [card_pos, filter_nonempty_iff]
      simp
    rw [hint]
    constructor
    · intro hacc
      have h1 := hacc j0
      unfold Nat.dist at h1
      omega
    · intro hk j
      unfold Nat.dist
      by_cases hj : j = j0
      · rw [hj]
        omega
      · have h2 := p6_Dj M j0 j S (univ.image (fun c => (emb c).1)) Q H
          (Function.invFun (fun c => (emb c).1)) a b (hHQj j hj)
        omega
theorem main_assembly : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ M : Fin 3 → Equiv.Perm (Fin n),
    ∀ (order : Fin (2*n) ≃ (Bool × Fin n)) (p s R : ℕ), 0 < p → 0 < R →
      ∀ (init : Fin R → Fin s) (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s)
        (out : Fin R → Fin s → Bool),
        (∀ x : Bool × Fin n → Bool, 2*R ≤ 3*(Finset.univ.filter (fun r : Fin R =>
          (ans order init step out r x = true ↔ acc M x))).card) →
        n ≤ 60000*p*Nat.clog 2 s := by
  obtain ⟨NA, hA⟩ := A_good_perms
  refine ⟨max NA 4096, ?_⟩
  intro n hn
  obtain ⟨M, hMs, hMa⟩ := hA n (le_trans (le_max_left _ _) hn)
  refine ⟨M, ?_⟩
  intro order p s R hp hR init step out hcorr
  have hn4 : 4096 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨j0, hj0⟩ := hMs (cutSet order) (C_cut_card order)
  obtain ⟨e, heA, heB, heacc⟩ := C_embed n hn4 M hMa (cutSet order) j0 hj0
  obtain ⟨τ, o, hans, hrect⟩ := C_transcript hp order init step out
  have key := B_core (n/256) R (Fin p → Fin s × Fin s) hR (fun r a b => τ r (e a b)) o ?_ ?_
  · exact D_numeric n p s (by omega) hp key
  · intro r a a' b b' h
    have hmix : (fun v => if v ∈ cutSet order then e a b v else e a' b' v) = e a b' := by
      funext v
      by_cases hv : v ∈ cutSet order
      · simp only [hv, ↓reduceIte]
        exact heA a b b' v hv
      · simp only [hv, ↓reduceIte]
        exact heB a' a b' v hv
    have h2 := hrect r (e a b) (e a' b') h
    rw [hmix] at h2
    exact h2
  · intro a b hab
    have hc := hcorr (e a b)
    have hset : (Finset.univ.filter (fun r : Fin R =>
        (ans order init step out r (e a b) = true ↔ acc M (e a b)))) =
        (Finset.univ.filter (fun r : Fin R =>
        (o r (τ r (e a b)) = true ↔ ∃ k, a k = true ∧ b k = true))) := by
      apply Finset.filter_congr
      intro r _
      rw [hans r (e a b), heacc a b hab]
    rw [hset] at hc
    exact hc
end PEqualNP.Outside.L_pcx_320
theorem PEqualNP.Outside.L_pcx_320 : ∃ C N : ℕ, 0 < C ∧ ∀ n : ℕ, N ≤ n →
  let V := Bool × Fin n
  let X := V → Bool
  ∃ M : Fin 3 → Equiv.Perm (Fin n),
    let accepts := fun x : X => ∀ j : Fin 3,
      let D := (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
      16 * Nat.dist (2*D) n ≤ n
    ∀ (order : Fin (2*n) ≃ V) (p s R : ℕ), 0 < p → 0 < R →
      ∀ (init : Fin R → Fin s)
        (step : Fin R → Fin p → Fin (2*n) → Fin s → Bool → Fin s)
        (out : Fin R → Fin s → Bool),
        let answer := fun (r : Fin R) (x : X) =>
          out r ((List.finRange p).foldl (fun st pass =>
            (List.finRange (2*n)).foldl (fun z j => step r pass j z (x (order j))) st) (init r))
        (∀ x : X, 2*R ≤ 3*(Finset.univ.filter (fun r : Fin R =>
          (answer r x = true ↔ accepts x))).card) →
        n ≤ C*p*Nat.clog 2 s := by
  obtain ⟨N, h⟩ := PEqualNP.Outside.L_pcx_320.main_assembly
  exact ⟨60000, N, by norm_num, fun n hn => h n hn⟩
