import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_pcx_301_aux

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


abbrev V (n : Nat) := Bool × Fin n
def cross {n : Nat} (P : Equiv.Perm (Fin n)) (S : Finset (V n)) :=
  Finset.univ.filter (fun i : Fin n => ¬ ((false,i)∈S ↔ (true,P i)∈S))
def agrees {n : Nat} (P Q : Equiv.Perm (Fin n)) := Finset.univ.filter (fun i => P i=Q i)
def accept {n : Nat} (M : Fin 3 → Equiv.Perm (Fin n)) (S : Finset (V n)) (x z : V n→Bool) :=
  let w := fun v => if v ∈ S then x v else z v
  ∀ j : Fin 3, 16*Nat.dist (2*(Finset.univ.filter (fun i : Fin n => w (false,i)≠w (true,M j i))).card) n ≤ n

theorem cut_result {n : Nat} (M : Fin 3→Equiv.Perm (Fin n)) (S : Finset (V n))
    (big : 8192*3<n) (over : ∀ j l : Fin 3,j≠l → 128*(agrees (M j) (M l)).card≤n)
    (splitAll : ∃ t : Fin 3,n/16384≤(cross (M t) S).card) :
    (∃ L R : Fin (2^(n/16384)) → V n→Bool,
      ∀ i j,accept M S (L i) (R j) ↔ i=j) ∧
    ∀ (u : Nat) (left right : Fin u→(V n→Bool)→Prop),
      (∀ x z, accept M S x z ↔ ∃ i,left i x ∧ right i z) → 2^(n/16384)≤u := by
  classical
  obtain ⟨t,ht⟩ := splitAll
  obtain ⟨T,hsub,hcard⟩ := Finset.exists_subset_card_eq ht
  obtain ⟨base,hbase⟩ := main_300 n 3 M t T big (by omega) (fun j h => over j t h)
  let read : (T→Bool) → V n→Bool := fun f v =>
    let i := if v.1 then (M t).symm v.2 else v.2
    if h : i∈T then f ⟨i,h⟩ else base v
  have hit (f g : T→Bool) : accept M S (read f) (read g) ↔ f=g := by
    let w := fun v : V n => if v∈S then read f v else read g v
    have frozen (i : Fin n) (hi : i∉T) : w (false,i)=base (false,i) ∧ w (true,M t i)=base (true,M t i) := by
      simp [w,read,hi]
    change (∀ j : Fin 3, 16 * Nat.dist (2*(Finset.univ.filter (fun i : Fin n => w (false,i) ≠ w (true,M j i))).card) n ≤ n) ↔ _
    rw [(hbase w frozen).2.2]
    have branch (i : T) : w (false,i.val)=w (true,M t i.val) ↔ f i=g i := by
      have hx := (Finset.mem_filter.mp (hsub i.property)).2
      by_cases ha : (false,i.val)∈S
      · have hb : (true,M t i.val)∉S := fun h => hx ⟨fun _ => h,fun _ => ha⟩
        simp [w,read,ha,hb,i.property]
      · have hb : (true,M t i.val)∈S := by by_contra h; exact hx ⟨fun e => (ha e).elim,fun e => (h e).elim⟩
        simpa [w,read,ha,hb,i.property] using
          (show g i=f i ↔ f i=g i from ⟨Eq.symm,Eq.symm⟩)
    constructor
    · intro h; funext i; exact (branch i).mp (h i.val i.property)
    · rintro rfl i hi; exact (branch ⟨i,hi⟩).mpr rfl
  have size : Fintype.card (T→Bool)=2^(n/16384) := by simp [hcard]
  let e : Fin (2^(n/16384)) ≃ (T→Bool) := Fintype.equivOfCardEq (by simpa using size.symm)
  have hh (i j) : accept M S (read (e i)) (read (e j)) ↔ i=j := (hit _ _).trans e.injective.eq_iff
  refine ⟨⟨fun i => read (e i),fun i => read (e i),hh⟩,?_⟩
  intro u left right cov
  have hdiag (i) := (cov _ _).mp ((hh i i).mpr rfl)
  choose cell hl hr using hdiag
  have inj : Function.Injective cell := by
    intro i j hij
    exact (hh i j).mp ((cov _ _).mpr ⟨cell i,hl i,hij ▸ hr j⟩)
  simpa using Fintype.card_le_of_injective cell inj
private def mateOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (j : Fin r) (v : V n) : V n :=
  if v.1 then (false, (M j).symm v.2) else (true, M j v.2)

private def borderOf {n r : ℕ} (M : Fin r → Equiv.Perm (Fin n)) (S : Finset (V n)) : Finset (V n) :=
  S.filter (fun v => ∃ j : Fin r, mateOf M j v ∉ S)

private def ballCard (n r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (r + 1), Nat.choose n j

private theorem pow_101_le (n : ℕ) : 101 ^ n ≤ 2 ^ (n / 50 + 1) * 100 ^ n := by
  have h50 : (101 : ℕ) ^ 50 ≤ 2 * 100 ^ 50 := by norm_num
  have hdiv : n = 50 * (n / 50) + n % 50 := (Nat.div_add_mod n 50).symm
  have hmod : n % 50 < 50 := Nat.mod_lt n (by omega)
  have hpart1 : 101 ^ (50 * (n / 50)) ≤ 2 ^ (n / 50) * 100 ^ (50 * (n / 50)) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left h50 _
  have hpart2 : 101 ^ (n % 50) ≤ 2 * 100 ^ (n % 50) := by
    have hmul : 101 ^ (n % 50) * 100 ^ (50 - n % 50) ≤ 2 * 100 ^ 50 := by
      calc 101 ^ (n % 50) * 100 ^ (50 - n % 50)
          ≤ 101 ^ (n % 50) * 101 ^ (50 - n % 50) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
        _ = 101 ^ 50 := by rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmod)]
        _ ≤ 2 * 100 ^ 50 := h50
    have h50eq : 100 ^ 50 = 100 ^ (n % 50) * 100 ^ (50 - n % 50) := by
      rw [← pow_add, Nat.add_sub_of_le (le_of_lt hmod)]
    rw [h50eq, ← mul_assoc] at hmul
    exact Nat.le_of_mul_le_mul_right hmul (Nat.pow_pos (by omega))
  conv_lhs => rw [hdiv, pow_add]
  calc 101 ^ (50 * (n / 50)) * 101 ^ (n % 50)
      ≤ (2 ^ (n / 50) * 100 ^ (50 * (n / 50))) * (2 * 100 ^ (n % 50)) :=
        Nat.mul_le_mul hpart1 hpart2
    _ = 2 ^ (n / 50 + 1) * (100 ^ (50 * (n / 50)) * 100 ^ (n % 50)) := by rw [pow_succ]; ring
    _ = 2 ^ (n / 50 + 1) * 100 ^ n := by rw [← pow_add, ← hdiv]

private theorem ballCard_le_pow2 {n r : ℕ} (hr : r ≤ n) :
    ballCard n r ≤ 2 ^ (n / 50 + 1 + 7 * r) := by
  have hbinom : 100 ^ (n - r) * ballCard n r ≤ 101 ^ n := by
    have hexp : (100 + 1 : ℕ) ^ n = ∑ j ∈ Finset.range (n + 1), 100 ^ (n - j) * Nat.choose n j := by
      have h1 := add_pow (1 : ℕ) 100 n
      rw [show (100 + 1 : ℕ) = 1 + 100 from rfl, h1]
      refine Finset.sum_congr rfl fun j _ => by simp only [one_pow, one_mul, Nat.cast_id]
    have hsub : Finset.range (r + 1) ⊆ Finset.range (n + 1) := Finset.range_mono (by omega)
    calc 100 ^ (n - r) * ballCard n r
        = ∑ j ∈ Finset.range (r + 1), 100 ^ (n - r) * Nat.choose n j := by
          unfold ballCard; rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (r + 1), 100 ^ (n - j) * Nat.choose n j := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_range] at hj
          exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ ∑ j ∈ Finset.range (n + 1), 100 ^ (n - j) * Nat.choose n j :=
          Finset.sum_le_sum_of_subset hsub
      _ = 101 ^ n := hexp.symm
  have h101 := pow_101_le n
  have hsplit : 100 ^ n = 100 ^ (n - r) * 100 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  have h100r : 100 ^ r ≤ 2 ^ (7 * r) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num : 100 ≤ 2 ^ 7) r
  have hmul : 100 ^ (n - r) * ballCard n r ≤ 100 ^ (n - r) * 2 ^ (n / 50 + 1 + 7 * r) := by
    calc 100 ^ (n - r) * ballCard n r
        ≤ 101 ^ n := hbinom
      _ ≤ 2 ^ (n / 50 + 1) * 100 ^ n := h101
      _ = 100 ^ (n - r) * (2 ^ (n / 50 + 1) * 100 ^ r) := by rw [hsplit]; ring
      _ ≤ 100 ^ (n - r) * (2 ^ (n / 50 + 1) * 2 ^ (7 * r)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h100r)
      _ = 100 ^ (n - r) * 2 ^ (n / 50 + 1 + 7 * r) := by rw [← pow_add]
  exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega))

private theorem perm_image_fiber_card {n : ℕ} (A Y : Finset (Fin n)) (hcard : A.card = Y.card) :
    Nat.choose n A.card *
      ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card =
      Fintype.card (Equiv.Perm (Fin n)) := by
  let fib (Z : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π : Equiv.Perm (Fin n) => A.image π = Z)
  have hfib_eq : ∀ Z : Finset (Fin n), Z.card = A.card → (fib Z).card = (fib Y).card := by
    intro Z hZ
    have hZY : Z.card = Y.card := hZ.trans hcard
    have hc_eq : ((Finset.univ : Finset (Fin n)) \ Z).card = ((Finset.univ : Finset (Fin n)) \ Y).card := by
      rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_univ, Finset.inter_univ, hZY]
    let e1 : ↥Z ≃ ↥Y := Fintype.equivOfCardEq (by simp [hZY])
    let e2 : ↥((Finset.univ : Finset (Fin n)) \ Z) ≃ ↥((Finset.univ : Finset (Fin n)) \ Y) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe]; exact hc_eq)
    let τ : Equiv.Perm (Fin n) := {
      toFun := fun x => if hx : x ∈ Z then (e1 ⟨x, hx⟩).val else (e2 ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩).val
      invFun := fun y => if hy : y ∈ Y then (e1.symm ⟨y, hy⟩).val else (e2.symm ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩).val
      left_inv := fun x => by
        dsimp only
        by_cases hx : x ∈ Z
        · rw [dif_pos hx, dif_pos (e1 ⟨x, hx⟩).property]
          exact congrArg Subtype.val (e1.symm_apply_apply ⟨x, hx⟩)
        · have hx' : x ∈ (Finset.univ : Finset (Fin n)) \ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
          have hny : (e2 ⟨x, hx'⟩).val ∉ Y := (Finset.mem_sdiff.mp (e2 ⟨x, hx'⟩).property).2
          rw [dif_neg hx, dif_neg hny]
          exact congrArg Subtype.val (e2.symm_apply_apply ⟨x, hx'⟩)
      right_inv := fun y => by
        dsimp only
        by_cases hy : y ∈ Y
        · rw [dif_pos hy, dif_pos (e1.symm ⟨y, hy⟩).property]
          exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
        · have hy' : y ∈ (Finset.univ : Finset (Fin n)) \ Y := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩
          have hnz : (e2.symm ⟨y, hy'⟩).val ∉ Z := (Finset.mem_sdiff.mp (e2.symm ⟨y, hy'⟩).property).2
          rw [dif_neg hy, dif_neg hnz]
          exact congrArg Subtype.val (e2.apply_symm_apply ⟨y, hy'⟩)
    }
    have hτZ : Z.image τ = Y := by
      ext y
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (if hx' : x ∈ Z then (e1 ⟨x, hx'⟩).val else _) ∈ Y
        rw [dif_pos hx]
        exact (e1 ⟨x, hx⟩).property
      · intro hy
        refine ⟨(e1.symm ⟨y, hy⟩).val, (e1.symm ⟨y, hy⟩).property, ?_⟩
        change (if hx' : (e1.symm ⟨y, hy⟩).val ∈ Z then (e1 ⟨_, hx'⟩).val else _) = y
        rw [dif_pos (e1.symm ⟨y, hy⟩).property]
        exact congrArg Subtype.val (e1.apply_symm_apply ⟨y, hy⟩)
    refine Finset.card_bij (fun π _ => π.trans τ) ?_ ?_ ?_
    · intro π hπ
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      have himg : A.image (π.trans τ) = (A.image π).image τ := by
        ext y; simp [Equiv.trans_apply]
      rw [himg, hπ, hτZ]
    · intro π1 _ π2 _ heq
      apply Equiv.ext
      intro x
      exact τ.injective (by simpa [Equiv.trans_apply] using Equiv.ext_iff.mp heq x)
    · intro π hπ
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
      refine ⟨π.trans τ.symm, ?_, by ext x; simp⟩
      simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
      have himg : A.image (π.trans τ.symm) = (A.image π).image τ.symm := by
        ext x; simp [Equiv.trans_apply]
      rw [himg, hπ, ← hτZ]
      ext x; simp
  have hpart : (Finset.univ : Finset (Equiv.Perm (Fin n))) =
      (Finset.powersetCard A.card (Finset.univ : Finset (Fin n))).biUnion fib := by
    ext π
    simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_powersetCard, Finset.subset_univ,
      true_and, fib, Finset.mem_filter, true_iff]
    exact ⟨A.image π, Finset.card_image_of_injective A π.injective, rfl⟩
  have hdisj : ((Finset.powersetCard A.card (Finset.univ : Finset (Fin n))) : Set (Finset (Fin n))).PairwiseDisjoint fib := by
    intro Z1 _ Z2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro π h1 h2
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (h1.symm.trans h2)
  have htot := congrArg Finset.card hpart
  rw [Finset.card_univ, Finset.card_biUnion hdisj] at htot
  have hsum_eq : ∑ Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Z).card =
      Nat.choose n A.card * (fib Y).card := by
    calc ∑ Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Z).card
        = ∑ _Z ∈ Finset.powersetCard A.card (Finset.univ : Finset (Fin n)), (fib Y).card :=
          Finset.sum_congr rfl fun Z hZ => hfib_eq Z (Finset.mem_powersetCard.mp hZ).2
      _ = (Finset.powersetCard A.card (Finset.univ : Finset (Fin n))).card * (fib Y).card := by simp
      _ = Nat.choose n A.card * (fib Y).card := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [← hsum_eq, ← htot]

private theorem card_finset_card_le {n r : ℕ} :
    ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ r)).card ≤ ballCard n r := by
  have hsub : (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ r) ⊆
      (Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n))) := by
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Finset.subset_univ] at hT ⊢
    exact ⟨T.card, by omega, rfl⟩
  calc _ ≤ ((Finset.range (r + 1)).biUnion (fun j => Finset.powersetCard j (Finset.univ : Finset (Fin n)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (r + 1), (Finset.powersetCard j (Finset.univ : Finset (Fin n))).card :=
        Finset.card_biUnion_le
    _ = ballCard n r := by
        unfold ballCard
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma choose_lower (n k : Nat) (hk : k≤n) :
    2^min k (n-k) ≤ n.choose k := by
  induction n generalizing k with
  | zero =>
    have eq : k=0 := by omega
    subst k
    decide
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      by_cases edge : n=k
      · subst k; simp
      · have h₁ := ih k (by omega)
        have h₂ := ih (k+1) (by omega)
        have step₁ : min (k+1) (n+1-(k+1)) - 1 ≤ min k (n-k) := by omega
        have step₂ : min (k+1) (n+1-(k+1)) - 1 ≤ min (k+1) (n-(k+1)) := by omega
        let d := min (k+1) (n+1-(k+1))-1
        have eq : min (k+1) (n+1-(k+1)) = d+1 := by dsimp [d]; omega
        have x : 2^d ≤ n.choose k := (Nat.pow_le_pow_right (by decide) step₁).trans h₁
        have y : 2^d ≤ n.choose (k+1) := (Nat.pow_le_pow_right (by decide) step₂).trans h₂
        rw [eq,pow_succ,Nat.choose_succ_succ]
        change 2^d * 2 ≤ n.choose k + n.choose (k+1)
        omega

private def badOverlap {n : Nat} (Q : Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun P : Equiv.Perm (Fin n) => n<128*(agrees P Q).card)

private theorem overlap_bound {n : Nat} (hn : 512≤n) (Q : Equiv.Perm (Fin n)) :
    4*(badOverlap Q).card ≤ Fintype.card (Equiv.Perm (Fin n)) := by
  classical
  let F := Fintype.card (Equiv.Perm (Fin n))
  let row (i : Fin n) := Finset.univ.filter (fun π : Equiv.Perm (Fin n) => π i=Q i)
  have point (i : Fin n) : n*(row i).card=F := by
    have h := perm_image_fiber_card ({i} : Finset (Fin n)) {Q i} (by simp)
    simpa [row,F] using h
  have transposed : ∑ P : Equiv.Perm (Fin n), (agrees P Q).card = ∑ i : Fin n,(row i).card := by
    simp only [agrees,row,Finset.card_filter]
    rw [Finset.sum_comm]
  have count : ∑ P : Equiv.Perm (Fin n),(agrees P Q).card = F := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0<n)
    rw [transposed,Finset.mul_sum]
    simp only [point,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  calc
    4*(badOverlap Q).card = ∑ _P ∈ badOverlap Q, 4 := by simp [Nat.mul_comm]
    _ ≤ ∑ P ∈ badOverlap Q,(agrees P Q).card := by
      apply Finset.sum_le_sum
      intro P h
      have := (Finset.mem_filter.mp h).2
      omega
    _ ≤ ∑ P : Equiv.Perm (Fin n),(agrees P Q).card := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := count
private theorem expansion_triple :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ M : Fin 3 → Equiv.Perm (Fin n),
      (∀ j l : Fin 3,j≠l → 128*(agrees (M j) (M l)).card≤n) ∧
      ∀ S : Finset (V n), n ≤ 2*S.card → 2*S.card≤3*n → n/5000 ≤ (borderOf M S).card := by
  refine ⟨500000, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hn32 : 32 ≤ n := by omega
  let M0 : Equiv.Perm (Fin n) := Equiv.refl (Fin n)
  let M1 : Equiv.Perm (Fin n) := {
    toFun := fun i => ⟨(i.val + 1) % n, Nat.mod_lt _ hn0⟩
    invFun := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ hn0⟩
    left_inv := fun i => by
      apply Fin.ext; dsimp only
      have hi := i.isLt
      by_cases h : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt h]
        have : i.val + 1 + n - 1 = n + i.val := by omega
        rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt hi]
      · have heq : i.val + 1 = n := by omega
        rw [heq, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]; omega
    right_inv := fun i => by
      apply Fin.ext; dsimp only
      have hi := i.isLt
      by_cases h0 : i.val = 0
      · have hm : (i.val + n - 1) % n = n - 1 := by
          rw [h0, zero_add, Nat.mod_eq_of_lt (by omega)]
        rw [hm, h0]
        have : n - 1 + 1 = n := by omega
        rw [this, Nat.mod_self]
      · have hm : (i.val + n - 1) % n = i.val - 1 := by
          have h1 : i.val + n - 1 = n + (i.val - 1) := by omega
          rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hm]
        have : i.val - 1 + 1 = i.val := by omega
        rw [this, Nat.mod_eq_of_lt hi]
  }
  let Mof : Equiv.Perm (Fin n) → (Fin 3 → Equiv.Perm (Fin n)) := fun π j =>
    match j with
    | ⟨0, _⟩ => M0
    | ⟨1, _⟩ => M1
    | ⟨2, _⟩ => π
  set b := n / 5000
  have hb_ge : 100 ≤ b := by omega

  let transOf (A : Finset (Fin n)) : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => decide (i ∈ A) ≠ decide (M1 i ∈ A))
  let candA : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun A => (transOf A).card ≤ 2 * b ∧ n / 8 ≤ A.card ∧ A.card + n/8 ≤ n)
  let candB (A : Finset (Fin n)) : Finset (Finset (Fin n)) :=
    Finset.univ.filter (fun B => (symmDiff A B).card ≤ b)
  let candPairs : Finset (Finset (Fin n) × Finset (Fin n)) :=
    candA.biUnion (fun A => (candB A).map ⟨fun B => (A, B), fun _ _ h => (Prod.mk.inj h).2⟩)
  let badFor (AB : Finset (Fin n) × Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π => (symmDiff (AB.1.image π) AB.2).card ≤ b)
  let badPerms : Finset (Equiv.Perm (Fin n)) := candPairs.biUnion badFor

  have hcandA_card : candA.card ≤ 2 * ballCard n (2 * b) := by
    let encA : Finset (Fin n) → Bool × Finset (Fin n) := fun A => (decide ((⟨0, hn0⟩ : Fin n) ∈ A), transOf A)
    have hencA_inj : Function.Injective encA := by
      intro A1 A2 heq
      have h0 : decide ((⟨0, hn0⟩ : Fin n) ∈ A1) = decide ((⟨0, hn0⟩ : Fin n) ∈ A2) := congrArg Prod.fst heq
      have hT : transOf A1 = transOf A2 := congrArg Prod.snd heq
      have hall : ∀ k (hk : k < n), decide ((⟨k, hk⟩ : Fin n) ∈ A1) = decide ((⟨k, hk⟩ : Fin n) ∈ A2) := by
        intro k
        induction k with
        | zero => intro _; exact h0
        | succ k' ih =>
          intro hk
          have hprev := ih (by omega)
          have hstep := Finset.ext_iff.mp hT ⟨k', by omega⟩
          simp only [transOf, Finset.mem_filter, Finset.mem_univ, true_and] at hstep
          have hM1 : M1 ⟨k', by omega⟩ = ⟨k' + 1, hk⟩ := by
            apply Fin.ext; dsimp only [M1]; exact Nat.mod_eq_of_lt hk
          rw [hM1, hprev] at hstep
          cases h1 : decide ((⟨k' + 1, hk⟩ : Fin n) ∈ A1) <;>
            cases h2 : decide ((⟨k' + 1, hk⟩ : Fin n) ∈ A2) <;>
            cases h3 : decide ((⟨k', by omega⟩ : Fin n) ∈ A2) <;> simp_all
      ext i
      have hi := hall i.val i.isLt
      simpa using hi
    let target := (Finset.univ : Finset Bool) ×ˢ
      ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ 2 * b))
    have hsub : candA.image encA ⊆ target := by
      intro p hp
      rw [Finset.mem_image] at hp
      obtain ⟨A, hA, rfl⟩ := hp
      simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
      simp only [target, encA, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
      exact hA.1
    calc candA.card = (candA.image encA).card := (Finset.card_image_of_injective candA hencA_inj).symm
      _ ≤ target.card := Finset.card_le_card hsub
      _ = 2 * ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ 2 * b)).card := by
          simp [target, Finset.card_product]
      _ ≤ 2 * ballCard n (2 * b) := Nat.mul_le_mul_left 2 card_finset_card_le

  have hcandB_card : ∀ A : Finset (Fin n), (candB A).card ≤ ballCard n b := by
    intro A
    have hinj : Function.Injective (fun B : Finset (Fin n) => symmDiff A B) := by
      intro B1 B2 heq
      have h1 := congrArg (symmDiff A) heq
      rwa [symmDiff_symmDiff_cancel_left, symmDiff_symmDiff_cancel_left] at h1
    have hsub : (candB A).image (fun B => symmDiff A B) ⊆
        (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b) := by
      intro T hT
      rw [Finset.mem_image] at hT
      obtain ⟨B, hB, rfl⟩ := hT
      simp only [candB, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
      exact hB
    calc (candB A).card = ((candB A).image (fun B => symmDiff A B)).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b)).card :=
          Finset.card_le_card hsub
      _ ≤ ballCard n b := card_finset_card_le

  have hbadFor_bound : ∀ AB ∈ candPairs,
      2 ^ (n/8) * (badFor AB).card ≤
        (n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by
    intro AB hAB
    simp only [candPairs, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk] at hAB
    obtain ⟨A, hA, B, _, rfl⟩ := hAB
    simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and] at hA
    let candY := Finset.univ.filter (fun Y : Finset (Fin n) => Y.card = A.card ∧ (symmDiff Y B).card ≤ b)
    have hY_card : candY.card ≤ ballCard n b := by
      have hinj : Function.Injective (fun Y : Finset (Fin n) => symmDiff Y B) := by
        intro Y1 Y2 heq
        have h1 := congrArg (fun Z => symmDiff Z B) heq
        rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at h1
      have hsub : candY.image (fun Y => symmDiff Y B) ⊆
          (Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b) := by
        intro T hT
        rw [Finset.mem_image] at hT
        obtain ⟨Y, hY, rfl⟩ := hT
        simp only [candY, Finset.mem_filter, Finset.mem_univ, true_and] at hY ⊢
        exact hY.2
      calc candY.card = (candY.image (fun Y => symmDiff Y B)).card :=
            (Finset.card_image_of_injective _ hinj).symm
        _ ≤ ((Finset.univ : Finset (Finset (Fin n))).filter (fun T => T.card ≤ b)).card :=
            Finset.card_le_card hsub
        _ ≤ ballCard n b := card_finset_card_le
    have hbad_sub : badFor (A, B) ⊆
        candY.biUnion (fun Y => (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)) := by
      intro π hπ
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, candY] at hπ ⊢
      exact ⟨A.image π, ⟨Finset.card_image_of_injective A π.injective, hπ⟩, rfl⟩
    have hchoose_mul : Nat.choose n A.card * (badFor (A, B)).card ≤
        ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by
      calc Nat.choose n A.card * (badFor (A, B)).card
          ≤ Nat.choose n A.card * (∑ Y ∈ candY, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card) :=
            Nat.mul_le_mul_left (Nat.choose n A.card) (le_trans (Finset.card_le_card hbad_sub) Finset.card_biUnion_le)
        _ = ∑ Y ∈ candY, Nat.choose n A.card * ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π : Equiv.Perm (Fin n) => A.image π = Y)).card := by
            rw [Finset.mul_sum]
        _ = ∑ _Y ∈ candY, Fintype.card (Equiv.Perm (Fin n)) := by
            refine Finset.sum_congr rfl fun Y hY => ?_
            exact perm_image_fiber_card A Y (Finset.mem_filter.mp hY).2.1.symm
        _ = candY.card * Fintype.card (Equiv.Perm (Fin n)) := by simp
        _ ≤ ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := Nat.mul_le_mul_right _ hY_card
    have choose := choose_lower n A.card (by have := Finset.card_le_univ A; simpa using this)
    have h₁ : 2^(n/8) ≤ Nat.choose n A.card := (Nat.pow_le_pow_right (by decide) (by omega)).trans choose
    have hmid : 2^(n/8) ≤ (n+1)*2^b*Nat.choose n A.card :=
      h₁.trans (Nat.le_mul_of_pos_left _ (by positivity))
    calc 2 ^ (n/8) * (badFor (A, B)).card
        ≤ ((n + 1) * 2 ^ b * Nat.choose n A.card) * (badFor (A, B)).card :=
          Nat.mul_le_mul_right _ hmid
      _ = (n + 1) * 2 ^ b * (Nat.choose n A.card * (badFor (A, B)).card) := by ring
      _ ≤ (n + 1) * 2 ^ b * (ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Nat.mul_le_mul_left _ hchoose_mul
      _ = (n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n)) := by ring

  have hpairs_card : candPairs.card ≤ 2 * ballCard n (2 * b) * ballCard n b := by
    calc candPairs.card
        ≤ ∑ A ∈ candA, ((candB A).map ⟨fun B => (A, B), fun _ _ h => (Prod.mk.inj h).2⟩).card :=
          Finset.card_biUnion_le
      _ = ∑ A ∈ candA, (candB A).card := Finset.sum_congr rfl fun A _ => Finset.card_map _
      _ ≤ ∑ _A ∈ candA, ballCard n b := Finset.sum_le_sum fun A _ => hcandB_card A
      _ = candA.card * ballCard n b := by simp
      _ ≤ (2 * ballCard n (2 * b)) * ballCard n b := Nat.mul_le_mul_right _ hcandA_card
  have htot_bad : 2 ^ (n/8) * badPerms.card ≤
      2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b *
        Fintype.card (Equiv.Perm (Fin n)) := by
    calc 2 ^ (n/8) * badPerms.card
        ≤ 2 ^ (n/8) * (∑ AB ∈ candPairs, (badFor AB).card) :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ AB ∈ candPairs, 2 ^ (n/8) * (badFor AB).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _AB ∈ candPairs, ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Finset.sum_le_sum hbadFor_bound
      _ = candPairs.card * ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) := by simp
      _ ≤ (2 * ballCard n (2 * b) * ballCard n b) *
            ((n + 1) * 2 ^ b * ballCard n b * Fintype.card (Equiv.Perm (Fin n))) :=
          Nat.mul_le_mul_right _ hpairs_card
      _ = 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b *
            Fintype.card (Equiv.Perm (Fin n)) := by ring

  have hcoef_lt : 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b < 2 ^ (n/8 - 2) := by
    have hb1 := ballCard_le_pow2 (n := n) (r := 2 * b) (by omega)
    have hb2 := ballCard_le_pow2 (n := n) (r := b) (by omega)
    have hn1_lt : n + 1 < 2 ^ (n / 50) := by
      have hk_ge : 10000 ≤ n / 50 := by omega
      have hlin : ∀ m : ℕ, 10 ≤ m → 60 * m < 2 ^ m := by
        intro m hm
        induction m with
        | zero => omega
        | succ m' ih =>
          by_cases h10 : m' < 10
          · have : m' = 9 := by omega
            subst this; norm_num
          · have hprev := ih (by omega)
            rw [pow_succ]; omega
      have h1 := hlin (n / 50) (by omega)
      omega
    have hexp_le : 1 + n / 50 + b + (n / 50 + 1 + 7 * (2 * b)) + (n / 50 + 1 + 7 * b) + (n / 50 + 1 + 7 * b) ≤ n/8 - 2 := by
      omega
    calc 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b
        < 2 * 2 ^ (n / 50) * 2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
            2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) := by
          have hpos1 : 0 < 2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
              2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) := by positivity
          have hstep1 : 2 * (n + 1) * 2 ^ b * ballCard n (2 * b) * ballCard n b * ballCard n b ≤
              2 * (n + 1) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) := by
            have hm1 : ballCard n (2 * b) * ballCard n b ≤
                2 ^ (n / 50 + 1 + 7 * (2 * b)) * 2 ^ (n / 50 + 1 + 7 * b) := Nat.mul_le_mul hb1 hb2
            have hm2 : ballCard n (2 * b) * ballCard n b * ballCard n b ≤
                2 ^ (n / 50 + 1 + 7 * (2 * b)) * 2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b) :=
              Nat.mul_le_mul hm1 hb2
            have hm3 := Nat.mul_le_mul_left (2 * (n + 1) * 2 ^ b) hm2
            linarith
          have hstep2 : 2 * (n + 1) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) <
              2 * 2 ^ (n / 50) * (2 ^ b * 2 ^ (n / 50 + 1 + 7 * (2 * b)) *
                2 ^ (n / 50 + 1 + 7 * b) * 2 ^ (n / 50 + 1 + 7 * b)) :=
            Nat.mul_lt_mul_of_pos_right (by omega) hpos1
          linarith
      _ = 2 ^ (1 + n / 50 + b + (n / 50 + 1 + 7 * (2 * b)) + (n / 50 + 1 + 7 * b) + (n / 50 + 1 + 7 * b)) := by
          simp only [pow_add, pow_one]
      _ ≤ 2 ^ (n/8 - 2) := Nat.pow_le_pow_right (by omega) hexp_le
  let U := Fintype.card (Equiv.Perm (Fin n))
  have hbadSmall : 4*badPerms.card < U := by
    have positive : 0 < U := Fintype.card_pos
    have aux := lt_of_le_of_lt htot_bad (Nat.mul_lt_mul_of_pos_right hcoef_lt positive)
    have hp : 2^(n/8) = 2^(n/8-2)*4 := by
      conv_lhs => rw [show n/8=n/8-2+2 by omega,pow_add]
      rfl
    rw [hp, Nat.mul_assoc] at aux
    exact Nat.lt_of_mul_lt_mul_left aux
  have overlap0 := overlap_bound (by omega : 512≤n) M0
  have overlap1 := overlap_bound (by omega : 512≤n) M1
  let avoid := badPerms ∪ (badOverlap M0 ∪ badOverlap M1)
  have rare : avoid.card<U := by
    have a := Finset.card_union_le badPerms (badOverlap M0 ∪ badOverlap M1)
    have b' := Finset.card_union_le (badOverlap M0) (badOverlap M1)
    change _ ≤ U at overlap0 overlap1
    change (badPerms ∪ (badOverlap M0 ∪ badOverlap M1)).card<U
    omega
  have good : ∃ π : Equiv.Perm (Fin n), π ∉ avoid := by
    by_contra hall
    push_neg at hall
    have eh : avoid = Finset.univ := by ext π; simp [hall π]
    rw [eh,Finset.card_univ] at rare
    exact lt_irrefl _ rare
  obtain ⟨π,hπ⟩ := good
  have hπ_good : π∉badPerms := fun e => hπ (Finset.mem_union_left _ e)
  have zo : 128*(agrees π M0).card≤n := by
    by_contra no
    exact hπ (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)))
  have oo : 128*(agrees π M1).card≤n := by
    by_contra no
    exact hπ (Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)))
  have nofixed (i : Fin n) : M0 i ≠ M1 i := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=(i.val+1)%n at hv
    have := i.isLt
    by_cases hs : i.val+1<n
    · rw [Nat.mod_eq_of_lt hs] at hv; omega
    · rw [show i.val+1=n by omega,Nat.mod_self] at hv; omega
  have z1 : (agrees M0 M1)=∅ := by ext i; simp [agrees,nofixed]
  have comm (P Q : Equiv.Perm (Fin n)) : agrees P Q=agrees Q P := by ext i; simp [agrees,eq_comm]
  refine ⟨Mof π,?_,?_⟩
  · intro j l ne
    fin_cases j <;> fin_cases l <;> first
      | exact (ne rfl).elim
      | exact zo
      | exact oo
      | change 128*(agrees M0 M1).card≤n; simp [z1]
      | change 128*(agrees M1 M0).card≤n; rw [comm M1 M0,z1]; simp
      | change 128*(agrees M0 π).card≤n; rwa [comm M0 π]
      | change 128*(agrees M1 π).card≤n; rwa [comm M1 π]
  intro S hSlow hShigh
  have hborder_ge : b ≤ (borderOf (Mof π) S).card := by
    by_contra hlt
    have hle : (borderOf (Mof π) S).card ≤ b := by omega
    let A : Finset (Fin n) := Finset.univ.filter (fun i => (false, i) ∈ S)
    let B : Finset (Fin n) := Finset.univ.filter (fun i => (true, i) ∈ S)
    have hAB_sum : A.card + B.card = S.card := by
      have hpart : S = A.image (fun i => (false, i)) ∪ B.image (fun i => (true, i)) := by
        ext ⟨flag, i⟩
        cases flag <;> simp [A, B]
      have hdisj : Disjoint (A.image (fun i => (false, i))) (B.image (fun i => (true, i))) := by
        rw [Finset.disjoint_left]; intro v h1 h2
        simp only [Finset.mem_image] at h1 h2
        obtain ⟨_, _, rfl⟩ := h1; obtain ⟨_, _, heq⟩ := h2
        exact Bool.false_ne_true.symm (Prod.mk.inj heq).1
      have hc := congrArg Finset.card hpart
      rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective A (fun _ _ h => (Prod.mk.inj h).2),
          Finset.card_image_of_injective B (fun _ _ h => (Prod.mk.inj h).2)] at hc
      exact hc.symm

    have hsymAB : (symmDiff A B).card ≤ (borderOf (Mof π) S).card := by
      let f : Fin n → V n := fun i => if i ∈ A then (false, i) else (true, i)
      have hinj : Set.InjOn f ↑(symmDiff A B) := by
        intro i1 _ i2 _ heq
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · exact (Prod.mk.inj heq).2
        · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
        · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
        · exact (Prod.mk.inj heq).2
      have hsub : (symmDiff A B).image f ⊆ borderOf (Mof π) S := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨i, hi, rfl⟩ := hv
        rw [Finset.mem_symmDiff] at hi
        simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [borderOf, Finset.mem_filter]
        rcases hi with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · simp only [f, A, Finset.mem_filter, Finset.mem_univ, true_and, if_pos h1]
          exact ⟨h1, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, h2]⟩
        · simp only [f, A, Finset.mem_filter, Finset.mem_univ, true_and, if_neg h1]
          exact ⟨h2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, h1]⟩
      calc (symmDiff A B).card = ((symmDiff A B).image f).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub

    have hsymPi : (symmDiff (A.image π) B).card ≤ (borderOf (Mof π) S).card := by
      let f : Fin n → V n := fun y => if y ∈ A.image π then (false, π.symm y) else (true, y)
      have hinj : Set.InjOn f ↑(symmDiff (A.image π) B) := by
        intro y1 _ y2 _ heq
        dsimp only [f] at heq
        split_ifs at heq with h1 h2 h2
        · exact π.symm.injective (Prod.mk.inj heq).2
        · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
        · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
        · exact (Prod.mk.inj heq).2
      have hsub : (symmDiff (A.image π) B).image f ⊆ borderOf (Mof π) S := by
        intro v hv
        rw [Finset.mem_image] at hv
        obtain ⟨y, hy, rfl⟩ := hv
        rw [Finset.mem_symmDiff] at hy
        simp only [borderOf, Finset.mem_filter]
        rcases hy with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · simp only [f, if_pos h1]
          rw [Finset.mem_image] at h1
          obtain ⟨i, hiA, rfl⟩ := h1
          simp only [Equiv.symm_apply_apply]
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hiA h2
          exact ⟨hiA, ⟨2, by omega⟩, by simp [mateOf, Mof, h2]⟩
        · simp only [f, if_neg h1]
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h2
          have hnotA : (false, π.symm y) ∉ S := fun hmem => h1 (Finset.mem_image.mpr
            ⟨π.symm y, by simp [A, hmem], by simp⟩)
          exact ⟨h2, ⟨2, by omega⟩, by simp [mateOf, Mof, hnotA]⟩
      calc (symmDiff (A.image π) B).card = ((symmDiff (A.image π) B).image f).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub

    have htrans_le : (transOf A).card ≤ 2 * (borderOf (Mof π) S).card := by
      let T1 := (transOf A).filter (fun i => (false, i) ∈ borderOf (Mof π) S)
      let T2 := (transOf A).filter (fun i => (false, M1 i) ∈ borderOf (Mof π) S ∨ (true, M1 i) ∈ borderOf (Mof π) S)
      have hcov : transOf A ⊆ T1 ∪ T2 := by
        intro i hi
        simp only [transOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [T1, T2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, transOf]
        by_cases hA1 : i ∈ A
        · have hA2 : M1 i ∉ A := by intro h; simp [hA1, h] at hi
          have hS1 : (false, i) ∈ S := (Finset.mem_filter.mp hA1).2
          have hS2 : (false, M1 i) ∉ S := fun h => hA2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          by_cases hB2 : (true, M1 i) ∈ S
          · right; refine ⟨hi, Or.inr ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hB2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, hS2]⟩
          · left; refine ⟨hi, ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hS1, ⟨1, by omega⟩, by simp [mateOf, Mof, hB2]⟩
        · have hA2 : M1 i ∈ A := by by_contra h; simp [hA1, h] at hi
          have hS1 : (false, i) ∉ S := fun h => hA1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have hS2 : (false, M1 i) ∈ S := (Finset.mem_filter.mp hA2).2
          by_cases hB2 : (true, M1 i) ∈ S
          · right; refine ⟨hi, Or.inr ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hB2, ⟨1, by omega⟩, by simp [mateOf, Mof, hS1]⟩
          · right; refine ⟨hi, Or.inl ?_⟩
            simp only [borderOf, Finset.mem_filter]
            exact ⟨hS2, ⟨0, by omega⟩, by simp [mateOf, Mof, M0, hB2]⟩
      have hT1_le : T1.card ≤ (borderOf (Mof π) S).card := by
        have hsub : T1.image (fun i => ((false, i) : V n)) ⊆ borderOf (Mof π) S := by
          intro v hv; rw [Finset.mem_image] at hv; obtain ⟨i, hi, rfl⟩ := hv
          exact (Finset.mem_filter.mp hi).2
        calc T1.card = (T1.image (fun i => ((false, i) : V n))).card :=
              (Finset.card_image_of_injective T1 (fun _ _ h => (Prod.mk.inj h).2)).symm
          _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub
      have hT2_le : T2.card ≤ (borderOf (Mof π) S).card := by
        let g : Fin n → V n := fun i => if (false, M1 i) ∈ borderOf (Mof π) S then (false, M1 i) else (true, M1 i)
        have hinj : Function.Injective g := by
          intro i1 i2 heq
          dsimp only [g] at heq
          split_ifs at heq with h1 h2 h2
          · exact M1.injective (Prod.mk.inj heq).2
          · exact False.elim (Bool.false_ne_true (Prod.mk.inj heq).1)
          · exact False.elim (Bool.false_ne_true.symm (Prod.mk.inj heq).1)
          · exact M1.injective (Prod.mk.inj heq).2
        have hsub : T2.image g ⊆ borderOf (Mof π) S := by
          intro v hv; rw [Finset.mem_image] at hv; obtain ⟨i, hi, rfl⟩ := hv
          have hmem := (Finset.mem_filter.mp hi).2
          dsimp only [g]
          split_ifs with h1
          · exact h1
          · exact hmem.resolve_left h1
        calc T2.card = (T2.image g).card := (Finset.card_image_of_injective T2 hinj).symm
          _ ≤ (borderOf (Mof π) S).card := Finset.card_le_card hsub
      calc (transOf A).card ≤ (T1 ∪ T2).card := Finset.card_le_card hcov
        _ ≤ T1.card + T2.card := Finset.card_union_le T1 T2
        _ ≤ 2 * (borderOf (Mof π) S).card := by omega

    have hdiff_cards : A.card ≤ B.card + (symmDiff A B).card ∧ B.card ≤ A.card + (symmDiff A B).card := by
      have h1 : A ⊆ B ∪ symmDiff A B := by
        intro x hx; rw [Finset.mem_union, Finset.mem_symmDiff]
        by_cases hB : x ∈ B <;> simp [hx, hB]
      have h2 : B ⊆ A ∪ symmDiff A B := by
        intro x hx; rw [Finset.mem_union, Finset.mem_symmDiff]
        by_cases hA : x ∈ A <;> simp [hx, hA]
      exact ⟨le_trans (Finset.card_le_card h1) (Finset.card_union_le _ _),
        le_trans (Finset.card_le_card h2) (Finset.card_union_le _ _)⟩
    have hA_cand : A ∈ candA := by
      simp only [candA, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hB_cand : B ∈ candB A := by
      simp only [candB, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hAB_mem : (A, B) ∈ candPairs := by
      simp only [candPairs, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk]
      exact ⟨A, hA_cand, B, hB_cand, rfl⟩
    have hπ_bad : π ∈ badPerms := by
      simp only [badPerms, Finset.mem_biUnion]
      refine ⟨(A, B), hAB_mem, ?_⟩
      simp only [badFor, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    exact hπ_good hπ_bad
  exact hborder_ge
private lemma one_split {n : Nat} (M : Fin 3→Equiv.Perm (Fin n)) (S : Finset (V n))
    (h : n/5000 ≤ (borderOf M S).card) : ∃ j,n/16384 ≤ (cross (M j) S).card := by
  classical
  let f (j : Fin 3) (i : Fin n) : V n := if (false,i) ∈ S then (false,i) else (true,M j i)
  have inc : borderOf M S ⊆ Finset.univ.biUnion (fun j : Fin 3 => (cross (M j) S).image (f j)) := by
    rintro ⟨side,i⟩ hv
    obtain ⟨inside,j,outside⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_biUnion.mpr
    refine ⟨j,Finset.mem_univ _,?_⟩
    cases side with
    | false =>
      change (true,M j i)∉S at outside
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun e => outside (e.mp inside)⟩,
        by simp [f,inside]⟩
    | true =>
      change (false,(M j).symm i)∉S at outside
      apply Finset.mem_image.mpr
      refine ⟨(M j).symm i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,by simp [f,outside]⟩
      intro e
      exact outside (e.mpr (by simpa using inside))
  have bound : (borderOf M S).card ≤ ∑ j : Fin 3,(cross (M j) S).card :=
    (Finset.card_le_card inc).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun _ _ => Finset.card_image_le)))
  by_contra nope
  push_neg at nope
  have h0 := nope (0 : Fin 3)
  have h1 := nope (1 : Fin 3)
  have h2 := nope (2 : Fin 3)
  rw [Fin.sum_univ_three] at bound
  omega

end PEqualNP.Outside.L_pcx_301_aux

theorem PEqualNP.Outside.L_pcx_301 : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
  let V := Bool × Fin n
  let X := V → Bool
  let q := 2^(n/16384)
  ∃ M : Fin 3 → Equiv.Perm (Fin n), ∀ S : Finset V,
    n ≤ 2*S.card → 2*S.card ≤ 3*n →
    let accept := fun (x z : X) =>
      let w := fun v : V => if v ∈ S then x v else z v
      ∀ j : Fin 3,
        let D := (Finset.univ.filter (fun i : Fin n => w (false,i) ≠ w (true,M j i))).card
        16 * Nat.dist (2*D) n ≤ n
    (∃ L R : Fin q → X, ∀ i j : Fin q, (accept (L i) (R j) ↔ i = j)) ∧
    ∀ (u : ℕ) (left right : Fin u → X → Prop),
      (∀ x z : X, (accept x z ↔ ∃ t : Fin u, left t x ∧ right t z)) → q ≤ u := by
  obtain ⟨N,hex⟩ := PEqualNP.Outside.L_pcx_301_aux.expansion_triple
  refine ⟨max N 500000,?_⟩
  intro n hn V X q
  obtain ⟨M,ho,hs⟩ := hex n (by omega)
  refine ⟨M,?_⟩
  intro S h₁ h₂ accept
  exact PEqualNP.Outside.L_pcx_301_aux.cut_result M S (by omega) ho
    (PEqualNP.Outside.L_pcx_301_aux.one_split M S (hs S h₁ h₂))
