import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_pcx_300_aux

private def sgn (b : Bool) : Int := if b then -1 else 1

private lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by
  cases b <;> decide

private lemma sgn_xor (a b : Bool) : sgn (xor a b) = sgn a * sgn b := by
  cases a <;> cases b <;> decide

private lemma sgn_ne_eq (a b : Bool) : (if a ≠ b then (1 : Int) else -1) = -(sgn a * sgn b) := by
  cases a <;> cases b <;> decide

private lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> decide

private lemma sum_prod4_zero {n : Nat} (u1 u2 v1 v2 : Fin n)
    (hvu1 : v1 ≠ u1) (hvu2 : v1 ≠ u2) (hvv2 : v1 ≠ v2) :
    (∑ a : Fin n → Bool, sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) = 0 := by
  let flip : (Fin n → Bool) → (Fin n → Bool) := fun a i => if i = v1 then !a i else a i
  have hinv : ∀ a, flip (flip a) = a := by
    intro a; funext i
    dsimp only [flip]
    by_cases hi : i = v1
    · simp [hi]
    · simp [hi]
  have hbij : Function.Bijective flip :=
    ⟨fun a b h => by have := congrArg flip h; rwa [hinv, hinv] at this, fun a => ⟨flip a, hinv a⟩⟩
  have hneg : ∀ a : Fin n → Bool,
      sgn (flip a u1) * sgn (flip a u2) * sgn (flip a v1) * sgn (flip a v2) =
      -(sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) := by
    intro a
    dsimp only [flip]
    have h1 : u1 ≠ v1 := Ne.symm hvu1
    have h2 : u2 ≠ v1 := Ne.symm hvu2
    have h3 : v2 ≠ v1 := Ne.symm hvv2
    simp only [h1, h2, h3, ↓reduceIte, sgn_not]
    ring
  have hsum_eq : (∑ a : Fin n → Bool, sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) =
      ∑ a : Fin n → Bool, sgn (flip a u1) * sgn (flip a u2) * sgn (flip a v1) * sgn (flip a v2) := by
    symm
    exact Fintype.sum_bijective flip hbij _ _ (fun _ => rfl)
  have hsum_neg : (∑ a : Fin n → Bool, sgn (flip a u1) * sgn (flip a u2) * sgn (flip a v1) * sgn (flip a v2)) =
      -(∑ a : Fin n → Bool, sgn (a u1) * sgn (a u2) * sgn (a v1) * sgn (a v2)) := by
    simp only [hneg, Finset.sum_neg_distrib]
  linarith

private lemma second_moment_perm {n : Nat} (π : Equiv.Perm (Fin n)) (mask : Fin n → Bool) :
    let Move := Finset.univ.filter (fun i : Fin n => π i ≠ i)
    (∑ a : Fin n → Bool, (∑ i ∈ Move, -(sgn (mask (π i)) * sgn (a i) * sgn (a (π i)))) ^ 2) ≤
      (2 * n : Int) * (2 ^ n : Int) := by
  intro Move
  have hexp : ∀ a : Fin n → Bool,
      (∑ i ∈ Move, -(sgn (mask (π i)) * sgn (a i) * sgn (a (π i)))) ^ 2 =
      ∑ u ∈ Move, ∑ v ∈ Move,
        (sgn (mask (π u)) * sgn (mask (π v))) * (sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) := by
    intro a
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  simp_rw [hexp]
  rw [Finset.sum_comm]
  have hswap : (∑ u ∈ Move, ∑ a : Fin n → Bool, ∑ v ∈ Move,
      (sgn (mask (π u)) * sgn (mask (π v))) * (sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))) =
      ∑ u ∈ Move, ∑ v ∈ Move,
        (sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ u ∈ Move,
      (∑ v ∈ Move, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))) ≤
      2 * (2 ^ n : Int) := by
    intro u hu
    let S2 : Finset (Fin n) := Move.filter (fun v => v = u ∨ v = π u)
    have hrest : ∑ v ∈ Move, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) =
        ∑ v ∈ S2, (sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun v hv hvnot => ?_
      have hne : ¬(v = u ∨ v = π u) := by
        intro h; exact hvnot (Finset.mem_filter.mpr ⟨hv, h⟩)
      have hvu : v ≠ u := fun h => hne (Or.inl h)
      have hvpu : v ≠ π u := fun h => hne (Or.inr h)
      have hvpv : v ≠ π v := Ne.symm (Finset.mem_filter.mp hv).2
      rw [sum_prod4_zero u (π u) v (π v) hvu hvpu hvpv, mul_zero]
    rw [hrest]
    have hterm : ∀ v ∈ S2, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))) ≤ (2 ^ n : Int) := by
      intro v _
      have habs : |(sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))| ≤ (2 ^ n : Int) := by
        rw [abs_mul, abs_mul, abs_sgn, abs_sgn, mul_one, one_mul]
        calc |∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))|
            ≤ ∑ a : Fin n → Bool, |sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v))| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ _a : Fin n → Bool, (1 : Int) := by
              refine Finset.sum_congr rfl fun a _ => ?_
              simp only [abs_mul, abs_sgn, mul_one]
          _ = (2 ^ n : Int) := by
              simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]
      exact le_trans (le_abs_self _) habs
    have hS2_card : S2.card ≤ 2 := by
      have hsub : S2 ⊆ ({u, π u} : Finset (Fin n)) := by
        intro v hv
        rcases (Finset.mem_filter.mp hv).2 with rfl | rfl <;> simp
      calc S2.card ≤ ({u, π u} : Finset (Fin n)).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    calc ∑ v ∈ S2, (sgn (mask (π u)) * sgn (mask (π v))) *
          (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))
        ≤ ∑ _v ∈ S2, (2 ^ n : Int) := Finset.sum_le_sum hterm
      _ = (S2.card : Int) * (2 ^ n : Int) := by simp
      _ ≤ 2 * (2 ^ n : Int) := by
          have h2p : (0 : Int) ≤ (2 ^ n : Int) := by positivity
          have hc : (S2.card : Int) ≤ 2 := by exact_mod_cast hS2_card
          nlinarith
  have hM_card : Move.card ≤ n := by
    have := Finset.card_le_univ Move
    simpa [Fintype.card_fin] using this
  calc ∑ u ∈ Move, ∑ v ∈ Move, (sgn (mask (π u)) * sgn (mask (π v))) *
        (∑ a : Fin n → Bool, sgn (a u) * sgn (a (π u)) * sgn (a v) * sgn (a (π v)))
      ≤ ∑ _u ∈ Move, (2 * (2 ^ n : Int)) := Finset.sum_le_sum hinner
    _ = (Move.card : Int) * (2 * (2 ^ n : Int)) := by simp
    _ ≤ (n : Int) * (2 * (2 ^ n : Int)) := by
        have h2p : (0 : Int) ≤ 2 * (2 ^ n : Int) := by positivity
        have hc : (Move.card : Int) ≤ (n : Int) := by exact_mod_cast hM_card
        nlinarith
    _ = (2 * n : Int) * (2 ^ n : Int) := by ring

private lemma nat_dist_eq_abs_int (a b : Nat) : (Nat.dist a b : Int) = |(a : Int) - (b : Int)| := by
  rw [Nat.dist]
  by_cases h : a ≤ b
  · have h1 : a - b = 0 := Nat.sub_eq_zero_of_le h
    rw [h1, zero_add, Int.ofNat_sub h, abs_of_nonpos (by omega)]
    ring
  · have h2 : b - a = 0 := Nat.sub_eq_zero_of_le (by omega)
    rw [h2, add_zero, Int.ofNat_sub (by omega), abs_of_nonneg (by omega)]

private lemma card_filter_imbalance {n : Nat} (p : Fin n → Bool) :
    (2 * (Finset.univ.filter (fun i : Fin n => p i = true)).card : Int) - (n : Int) =
      ∑ i : Fin n, if p i = true then (1 : Int) else -1 := by
  let P := Finset.univ.filter (fun i : Fin n => p i = true)
  let Q := Finset.univ.filter (fun i : Fin n => p i ≠ true)
  have hsplit : (∑ i : Fin n, if p i = true then (1 : Int) else -1) =
      (∑ i ∈ P, if p i = true then (1 : Int) else -1) + (∑ i ∈ Q, if p i = true then (1 : Int) else -1) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => p i = true)]
  have hP : (∑ i ∈ P, if p i = true then (1 : Int) else -1) = (P.card : Int) := by
    calc (∑ i ∈ P, if p i = true then (1 : Int) else -1)
        = ∑ _i ∈ P, (1 : Int) := Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      _ = (P.card : Int) := by simp
  have hQ : (∑ i ∈ Q, if p i = true then (1 : Int) else -1) = -(Q.card : Int) := by
    calc (∑ i ∈ Q, if p i = true then (1 : Int) else -1)
        = ∑ _i ∈ Q, (-1 : Int) := Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
      _ = -(Q.card : Int) := by simp
  have hcard : P.card + Q.card = n := by
    have hdisj : Disjoint P Q := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hunion : P ∪ Q = Finset.univ := by
      ext i
      simp only [P, Q, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro (em (p i = true))
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
  rw [hsplit, hP, hQ]
  change (2 * (P.card : Int)) - (n : Int) = (P.card : Int) + -(Q.card : Int)
  omega

private lemma card_filter_diff_le {n : Nat} (p q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (B : Finset (Fin n)) (hagree : ∀ i : Fin n, i ∉ B → (p i ↔ q i)) :
    ((Finset.univ.filter p).card : Int) - ((Finset.univ.filter q).card : Int) ≤ (B.card : Int) ∧
    ((Finset.univ.filter q).card : Int) - ((Finset.univ.filter p).card : Int) ≤ (B.card : Int) := by
  have hsub1 : Finset.univ.filter p ⊆ Finset.univ.filter q ∪ B := by
    intro i hi
    by_cases hB : i ∈ B
    · exact Finset.mem_union_right _ hB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hagree i hB).mp (Finset.mem_filter.mp hi).2⟩)
  have hsub2 : Finset.univ.filter q ⊆ Finset.univ.filter p ∪ B := by
    intro i hi
    by_cases hB : i ∈ B
    · exact Finset.mem_union_right _ hB
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, (hagree i hB).mpr (Finset.mem_filter.mp hi).2⟩)
  have h1 : (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card + B.card :=
    le_trans (Finset.card_le_card hsub1) (Finset.card_union_le _ _)
  have h2 : (Finset.univ.filter q).card ≤ (Finset.univ.filter p).card + B.card :=
    le_trans (Finset.card_le_card hsub2) (Finset.card_union_le _ _)
  omega

private lemma main_300 (n r : Nat) (M : Fin r → Equiv.Perm (Fin n)) (target : Fin r) (T : Finset (Fin n))
    (hrn : 8192 * r < n) (hTn : 128 * T.card ≤ n)
    (hfix : ∀ j : Fin r, j ≠ target →
      128 * (Finset.univ.filter (fun i : Fin n => M j i = M target i)).card ≤ n) :
    let V := Bool × Fin n
    let dist := fun (x : V → Bool) (j : Fin r) =>
      (Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M j i))).card
    let central := fun D : Nat => 16 * Nat.dist (2 * D) n ≤ n
    ∃ base : V → Bool, ∀ x : V → Bool,
      (∀ i : Fin n, i ∉ T →
        x (false, i) = base (false, i) ∧ x (true, M target i) = base (true, M target i)) →
      dist x target = 17 * n / 32 + (T.filter (fun i => x (false, i) ≠ x (true, M target i))).card ∧
      (∀ j : Fin r, j ≠ target → central (dist x j)) ∧
      ((∀ j : Fin r, central (dist x j)) ↔ ∀ i ∈ T, x (false, i) = x (true, M target i)) := by
  intro V dist central
  have hr_pos : 0 < r := Nat.pos_of_ne_zero (fun h0 => by have := target.isLt; omega)
  have hn_big : 8192 < n := by omega
  have hTc_card : 17 * n / 32 ≤ (Finset.univ \ T).card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq hTc_card
  let mask : Fin n → Bool := fun i => decide (i ∈ S)
  let π : Fin r → Equiv.Perm (Fin n) := fun j => (M j).trans (M target).symm
  let Move : Fin r → Finset (Fin n) := fun j => Finset.univ.filter (fun i : Fin n => π j i ≠ i)
  let Y : Fin r → (Fin n → Bool) → Int := fun j a =>
    ∑ i ∈ Move j, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))
  let Others : Finset (Fin r) := Finset.univ.erase target
  have hsum_all : (∑ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2) ≤
      (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int)) := by
    rw [Finset.sum_comm]
    calc ∑ j ∈ Others, ∑ a : Fin n → Bool, (Y j a) ^ 2
        ≤ ∑ _j ∈ Others, ((2 * n : Int) * (2 ^ n : Int)) :=
          Finset.sum_le_sum fun j _ => second_moment_perm (π j) mask
      _ = (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int)) := by simp
  have hO_card : Others.card < r := by
    have h1 : Others.card = r - 1 := by
      simp [Others, Finset.card_erase_of_mem (Finset.mem_univ target), Fintype.card_fin]
    omega
  have hex_a : ∃ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2 ≤ (2 * r * n : Int) := by
    by_contra hnone
    push Not at hnone
    have hgt : (2 ^ n : Int) * ((2 * r * n : Int)) < ∑ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2 := by
      have hcard_a : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
        simp [Fintype.card_pi, Fintype.card_bool, Fintype.card_fin]
      calc (2 ^ n : Int) * (2 * r * n : Int)
          = ∑ _a : Fin n → Bool, (2 * r * n : Int) := by simp [hcard_a]
        _ < ∑ a : Fin n → Bool, ∑ j ∈ Others, (Y j a) ^ 2 :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun a _ => hnone a
    have hle2 : (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int)) ≤ (2 ^ n : Int) * (2 * r * n : Int) := by
      have hO : (Others.card : Int) ≤ (r : Int) := by exact_mod_cast le_of_lt hO_card
      have h2np : (0 : Int) ≤ (2 * n : Int) * (2 ^ n : Int) := by positivity
      calc (Others.card : Int) * ((2 * n : Int) * (2 ^ n : Int))
          ≤ (r : Int) * ((2 * n : Int) * (2 ^ n : Int)) := mul_le_mul_of_nonneg_right hO h2np
        _ = (2 ^ n : Int) * (2 * r * n : Int) := by ring
    linarith
  rcases hex_a with ⟨a, ha_bound⟩
  let base : V → Bool := fun p =>
    match p with
    | (false, i) => a i
    | (true, k) => xor (a ((M target).symm k)) (mask ((M target).symm k))
  refine ⟨base, fun x hagree => ?_⟩
  have hdist_target : dist x target = 17 * n / 32 + (T.filter (fun i => x (false, i) ≠ x (true, M target i))).card := by
    let F := Finset.univ.filter (fun i : Fin n => x (false, i) ≠ x (true, M target i))
    let FT := T.filter (fun i : Fin n => x (false, i) ≠ x (true, M target i))
    have hF_eq : F = S ∪ FT := by
      ext i
      simp only [F, FT, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      by_cases hiT : i ∈ T
      · have hiS : i ∉ S := fun h => (Finset.mem_sdiff.mp (hS_sub h)).2 hiT
        simp [hiT, hiS]
      · rcases hagree i hiT with ⟨h1, h2⟩
        have hbase_ne : (base (false, i) ≠ base (true, M target i)) ↔ i ∈ S := by
          dsimp only [base, mask]
          simp only [Equiv.symm_apply_apply]
          cases a i <;> by_cases hS : i ∈ S <;> simp [hS]
        rw [h1, h2, hbase_ne]
        simp [hiT]
    have hdisj : Disjoint S FT := by
      rw [Finset.disjoint_left]
      intro i hiS hiFT
      exact (Finset.mem_sdiff.mp (hS_sub hiS)).2 (Finset.mem_filter.mp hiFT).1
    change F.card = 17 * n / 32 + FT.card
    rw [hF_eq, Finset.card_union_of_disjoint hdisj, hS_card]
  have hother : ∀ j : Fin r, j ≠ target → central (dist x j) := by
    intro j hj
    have hjO : j ∈ Others := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hY_sq : (Y j a) ^ 2 ≤ (2 * r * n : Int) := by
      have hsingle : (Y j a) ^ 2 ≤ ∑ j' ∈ Others, (Y j' a) ^ 2 :=
        Finset.single_le_sum (fun j' _ => sq_nonneg (Y j' a)) hjO
      exact le_trans hsingle ha_bound
    have h64Y : 64 * |Y j a| < (n : Int) := by
      have hsq_lt : (64 * |Y j a|) ^ 2 < (n : Int) ^ 2 := by
        have h1 : (64 * |Y j a|) ^ 2 = 4096 * (Y j a) ^ 2 := by rw [mul_pow, sq_abs]; ring
        have h2 : (8192 * r : Int) < (n : Int) := by exact_mod_cast hrn
        have hn0 : (0 : Int) < (n : Int) := by omega
        nlinarith
      nlinarith [abs_nonneg (Y j a)]
    let Fix := Finset.univ.filter (fun i : Fin n => M j i = M target i)
    have hFix_eq : Fix = Finset.univ.filter (fun i : Fin n => ¬(π j i ≠ i)) := by
      ext i
      simp only [Fix, π, Finset.mem_filter, Finset.mem_univ, true_and, not_not, Equiv.trans_apply]
      constructor
      · intro h; rw [h, Equiv.symm_apply_apply]
      · intro h; have := congrArg (M target) h; simpa using this
    have hbase_imb : |(2 * dist base j : Int) - (n : Int)| ≤ (Fix.card : Int) + |Y j a| := by
      have hcard_eq : (2 * dist base j : Int) - (n : Int) =
          ∑ i : Fin n, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i))) := by
        have h1 := card_filter_imbalance (fun i : Fin n => decide (base (false, i) ≠ base (true, M j i)))
        have hf : Finset.univ.filter (fun i : Fin n => decide (base (false, i) ≠ base (true, M j i)) = true) =
            Finset.univ.filter (fun i : Fin n => base (false, i) ≠ base (true, M j i)) := by
          ext i; simp
        rw [hf] at h1
        change (2 * (Finset.univ.filter (fun i : Fin n => base (false, i) ≠ base (true, M j i))).card : Int) - (n : Int) = _
        rw [h1]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [decide_eq_true_eq, sgn_ne_eq]
        dsimp only [base, π]
        simp only [Equiv.trans_apply, sgn_xor]
        ring
      rw [hcard_eq]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin n => π j i ≠ i)]
      have hM_def : (∑ i ∈ Finset.univ.filter (fun i : Fin n => π j i ≠ i),
          -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))) = Y j a := rfl
      rw [hM_def, ← hFix_eq]
      have hF_abs : |∑ i ∈ Fix, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))| ≤ (Fix.card : Int) := by
        calc |∑ i ∈ Fix, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))|
            ≤ ∑ i ∈ Fix, |-(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i)))| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ _i ∈ Fix, (1 : Int) := Finset.sum_congr rfl fun i _ => by simp [abs_neg, abs_mul, abs_sgn]
          _ = (Fix.card : Int) := by simp
      have htri := abs_add_le (Y j a) (∑ i ∈ Fix, -(sgn (mask (π j i)) * sgn (a i) * sgn (a (π j i))))
      linarith
    let B : Finset (Fin n) := T ∪ T.map (π j).symm.toEmbedding
    have hB_card : B.card ≤ 2 * T.card := by
      calc B.card ≤ T.card + (T.map (π j).symm.toEmbedding).card := Finset.card_union_le _ _
        _ = T.card + T.card := by rw [Finset.card_map]
        _ = 2 * T.card := by omega
    have hdiff := card_filter_diff_le
      (fun i : Fin n => x (false, i) ≠ x (true, M j i))
      (fun i : Fin n => base (false, i) ≠ base (true, M j i)) B (by
        intro i hiB
        have hiT : i ∉ T := fun h => hiB (Finset.mem_union_left _ h)
        have hpiT : π j i ∉ T := by
          intro h
          apply hiB
          apply Finset.mem_union_right
          rw [Finset.mem_map]
          exact ⟨π j i, h, by simp⟩
        have h1 : x (false, i) = base (false, i) := (hagree i hiT).1
        have h2 : x (true, M j i) = base (true, M j i) := by
          have h2' := (hagree (π j i) hpiT).2
          have hMpi : M target (π j i) = M j i := by simp [π]
          rwa [hMpi] at h2'
        rw [h1, h2])
    have hdist_diff : |(dist x j : Int) - (dist base j : Int)| ≤ (2 * T.card : Int) := by
      have hB_I : (B.card : Int) ≤ (2 * T.card : Int) := by exact_mod_cast hB_card
      rw [abs_le]
      exact ⟨by linarith [hdiff.2], by linarith [hdiff.1]⟩
    have hx_imb : |(2 * dist x j : Int) - (n : Int)| ≤ (Fix.card : Int) + |Y j a| + (4 * T.card : Int) := by
      have hsplit : (2 * dist x j : Int) - (n : Int) =
          ((2 * dist base j : Int) - (n : Int)) + 2 * ((dist x j : Int) - (dist base j : Int)) := by ring
      rw [hsplit]
      calc |((2 * dist base j : Int) - (n : Int)) + 2 * ((dist x j : Int) - (dist base j : Int))|
          ≤ |(2 * dist base j : Int) - (n : Int)| + |2 * ((dist x j : Int) - (dist base j : Int))| := abs_add_le _ _
        _ = |(2 * dist base j : Int) - (n : Int)| + 2 * |(dist x j : Int) - (dist base j : Int)| := by
            rw [abs_mul, abs_of_pos (by decide : (0 : Int) < 2)]
        _ ≤ ((Fix.card : Int) + |Y j a|) + 2 * (2 * T.card : Int) := by linarith
        _ = (Fix.card : Int) + |Y j a| + (4 * T.card : Int) := by ring
    have hFix_le : 128 * (Fix.card : Int) ≤ (n : Int) := by exact_mod_cast hfix j hj
    have hT_le : 128 * (T.card : Int) ≤ (n : Int) := by exact_mod_cast hTn
    have hcent_I : (16 * Nat.dist (2 * dist x j) n : Int) ≤ (n : Int) := by
      rw [nat_dist_eq_abs_int]
      push_cast
      linarith
    exact_mod_cast hcent_I
  refine ⟨hdist_target, hother, ?_⟩
  constructor
  · intro hall i hiT
    have hct : central (dist x target) := hall target
    rw [hdist_target] at hct
    dsimp only [central] at hct
    set d := (T.filter (fun i => x (false, i) ≠ x (true, M target i))).card
    have hd0 : d = 0 := by
      by_contra hne
      have hd1 : 1 ≤ d := by omega
      have hge : n ≤ 2 * (17 * n / 32 + d) := by omega
      have hdist_val : Nat.dist (2 * (17 * n / 32 + d)) n = 2 * (17 * n / 32 + d) - n := by
        rw [Nat.dist, Nat.sub_eq_zero_of_le hge, add_zero]
      rw [hdist_val] at hct
      omega
    by_contra hne_i
    have hmem : i ∈ T.filter (fun i => x (false, i) ≠ x (true, M target i)) :=
      Finset.mem_filter.mpr ⟨hiT, hne_i⟩
    have hpos : 0 < d := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  · intro heq j
    by_cases hj : j = target
    · subst hj
      rw [hdist_target]
      have hd0 : (T.filter (fun i => x (false, i) ≠ x (true, M j i))).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hiT hne
        exact hne (heq i hiT)
      rw [hd0, add_zero]
      dsimp only [central]
      have hge : n ≤ 2 * (17 * n / 32) := by omega
      have hdist_val : Nat.dist (2 * (17 * n / 32)) n = 2 * (17 * n / 32) - n := by
        rw [Nat.dist, Nat.sub_eq_zero_of_le hge, add_zero]
      rw [hdist_val]
      omega
    · exact hother j hj

end PEqualNP.Outside.L_pcx_300_aux

theorem PEqualNP.Outside.L_pcx_300 :
∀ (n r : ℕ) (M : Fin r → Equiv.Perm (Fin n)) (target : Fin r) (T : Finset (Fin n)),
  let V := Bool × Fin n
  let dist := fun (x : V → Bool) (j : Fin r) =>
    (Finset.univ.filter (fun i : Fin n => x (false,i) ≠ x (true,M j i))).card
  let central := fun D : ℕ => 16 * Nat.dist (2*D) n ≤ n
  8192*r < n → 128*T.card ≤ n →
  (∀ j : Fin r, j ≠ target →
    128*(Finset.univ.filter (fun i : Fin n => M j i = M target i)).card ≤ n) →
  ∃ base : V → Bool, ∀ x : V → Bool,
    (∀ i : Fin n, i ∉ T →
      x (false,i) = base (false,i) ∧ x (true,M target i) = base (true,M target i)) →
    dist x target = 17*n/32 + (T.filter (fun i => x (false,i) ≠ x (true,M target i))).card ∧
    (∀ j : Fin r, j ≠ target → central (dist x j)) ∧
    ((∀ j : Fin r, central (dist x j)) ↔ ∀ i ∈ T, x (false,i) = x (true,M target i)) := by
  intro n r M target T V dist central hrn hTn hfix
  exact PEqualNP.Outside.L_pcx_300_aux.main_300 n r M target T hrn hTn hfix
