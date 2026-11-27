import PEqualNP.Defs
import Mathlib.Data.Nat.Dist

namespace PEqualNP.Outside.L_lib_654_aux

def wt {n : ℕ} (v : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => v j = true)).card

lemma le_of_pow_le_pow {a b k : ℕ} (hk : k ≠ 0) (h : a ^ k ≤ b ^ k) : a ≤ b := by
  by_contra hlt
  push Not at hlt
  exact absurd (Nat.pow_lt_pow_left hlt hk) (not_lt.mpr h)

lemma num_lift (A B : ℕ) (h1 : 106 * A ≤ 100 * B) (h2 : 2 * 100 ^ 16 ≤ 106 ^ 16) :
    2 * A ^ 16 ≤ B ^ 16 := by
  have h1p : 106 ^ 16 * A ^ 16 ≤ 100 ^ 16 * B ^ 16 := by
    rw [← mul_pow, ← mul_pow]
    exact Nat.pow_le_pow_left h1 16
  have h2p : 2 * 100 ^ 16 * A ^ 16 ≤ 106 ^ 16 * A ^ 16 :=
    Nat.mul_le_mul_right _ h2
  have h3 : 100 ^ 16 * (2 * A ^ 16) ≤ 100 ^ 16 * B ^ 16 := by
    calc 100 ^ 16 * (2 * A ^ 16) = 2 * 100 ^ 16 * A ^ 16 := by ring
      _ ≤ 106 ^ 16 * A ^ 16 := h2p
      _ ≤ 100 ^ 16 * B ^ 16 := h1p
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

lemma chernoff_abstract (u n A B : ℕ) (hA : 0 < A)
    (h32 : u ^ 32 * B ^ n ≤ (2 ^ 32 * A) ^ n)
    (hnum : 2 * A ^ 16 ≤ B ^ 16) :
    u * 2 ^ (n / 512) ≤ 2 ^ n := by
  have h16 : (u ^ 32 * B ^ n) ^ 16 ≤ ((2 ^ 32 * A) ^ n) ^ 16 :=
    Nat.pow_le_pow_left h32 16
  have hLHS : (u ^ 32 * B ^ n) ^ 16 = u ^ 512 * (B ^ 16) ^ n := by
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n 16]
  have hRHS : ((2 ^ 32 * A) ^ n) ^ 16 = 2 ^ (512 * n) * (A ^ 16) ^ n := by
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm n 16]
    have hexp : 32 * (16 * n) = 512 * n := by ring
    rw [hexp]
  rw [hLHS, hRHS] at h16
  have hnum_n : 2 ^ n * (A ^ 16) ^ n ≤ (B ^ 16) ^ n := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hnum n
  have hcomb : u ^ 512 * 2 ^ n * (A ^ 16) ^ n ≤ 2 ^ (512 * n) * (A ^ 16) ^ n := by
    calc u ^ 512 * 2 ^ n * (A ^ 16) ^ n
        = u ^ 512 * (2 ^ n * (A ^ 16) ^ n) := mul_assoc _ _ _
      _ ≤ u ^ 512 * (B ^ 16) ^ n := Nat.mul_le_mul_left _ hnum_n
      _ ≤ 2 ^ (512 * n) * (A ^ 16) ^ n := h16
  have hstep3 : u ^ 512 * 2 ^ n ≤ 2 ^ (512 * n) :=
    Nat.le_of_mul_le_mul_right hcomb (by positivity)
  have hfinal : (u * 2 ^ (n / 512)) ^ 512 ≤ (2 ^ n) ^ 512 := by
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have hdiv : n / 512 * 512 ≤ n := Nat.div_mul_le_self n 512
    calc u ^ 512 * 2 ^ (n / 512 * 512)
        ≤ u ^ 512 * 2 ^ n := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hdiv)
      _ ≤ 2 ^ (512 * n) := hstep3
      _ = 2 ^ (n * 512) := by rw [mul_comm]
  exact le_of_pow_le_pow (by norm_num) hfinal

lemma sum_pow_wt (n a b : ℕ) :
    ∑ v : Fin n → Bool, a ^ wt v * b ^ (n - wt v) = (a + b) ^ n := by
  have h1 :
      ∑ v : Fin n → Bool, a ^ wt v * b ^ (n - wt v) =
        ∑ v : Fin n → Bool, ∏ j : Fin n, if v j = true then a else b := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    let s := Finset.univ.filter (fun j : Fin n => v j = true)
    have hcomp : (Finset.univ.filter (fun j : Fin n => v j ≠ true)).card = n - wt v := by
      have htot : s.card + (Finset.univ.filter (fun j : Fin n => v j ≠ true)).card = n := by
        rw [← Finset.card_union_of_disjoint]
        · have hun : s ∪ Finset.univ.filter (fun j : Fin n => v j ≠ true) = Finset.univ := by
            ext j
            simp only [s, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            exact em _
          rw [hun, Finset.card_univ, Fintype.card_fin]
        · rw [Finset.disjoint_left]
          intro j h1 h2
          exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      dsimp only [s, wt] at htot ⊢
      omega
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hcomp]
    rfl
  rw [h1]
  have h2 := (Fintype.prod_sum (fun (_ : Fin n) (c : Bool) => if c = true then a else b)).symm
  rw [h2]
  have hinner : ∑ c : Bool, (if c = true then a else b) = a + b := by
    have hb : (Finset.univ : Finset Bool) = {true, false} := by decide
    rw [hb, Finset.sum_pair (by decide)]
    simp
  simp_rw [hinner]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma tails_card_bound (n : ℕ) :
    let X := Fin n → Bool
    let central := fun d : ℕ => 16 * Nat.dist (2 * d) n ≤ n
    let tails := (Finset.univ : Finset X).filter (fun v => ¬ central (wt v))
    tails.card * 2 ^ (n / 512) ≤ 2 ^ (n + 1) := by
  dsimp only
  let X := Fin n → Bool
  let upper : Finset X := Finset.univ.filter (fun v => 17 * n < 32 * wt v)
  let lower : Finset X := Finset.univ.filter (fun v => 32 * wt v < 15 * n)
  have hsub :
      (Finset.univ : Finset X).filter (fun v => ¬ 16 * Nat.dist (2 * wt v) n ≤ n) ⊆
        upper ∪ lower := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, upper, lower] at hv ⊢
    by_cases hge : n ≤ 2 * wt v
    · left
      have hd : Nat.dist (2 * wt v) n = 2 * wt v - n := by
        rw [Nat.dist_eq_sub_of_le_right hge]
      rw [hd] at hv
      omega
    · right
      have hle : 2 * wt v ≤ n := by omega
      have hd : Nat.dist (2 * wt v) n = n - 2 * wt v := by
        rw [Nat.dist_eq_sub_of_le hle]
      rw [hd] at hv
      omega
  have hsymm : lower.card = upper.card := by
    refine Finset.card_bij (fun v _ j => !(v j)) ?_ ?_ ?_
    · intro v hv
      simp only [lower, upper, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      have hwt : wt (fun j => !(v j)) + wt v = n := by
        unfold wt
        dsimp only
        rw [← Finset.card_union_of_disjoint]
        · have hun :
              Finset.univ.filter (fun j : Fin n => (!v j) = true) ∪
              Finset.univ.filter (fun j : Fin n => v j = true) = Finset.univ := by
            ext j
            cases v j <;> simp
          rw [hun, Finset.card_univ, Fintype.card_fin]
        · rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [Finset.mem_filter] at h1 h2
          rw [h2.2] at h1
          exact Bool.noConfusion h1.2
      omega
    · intro v1 _ v2 _ h
      funext j
      have := congrFun h j
      cases h1 : v1 j <;> cases h2 : v2 j <;> simp_all
    · intro v hv
      simp only [upper, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hwt : wt (fun j => !(v j)) + wt v = n := by
        unfold wt
        dsimp only
        rw [← Finset.card_union_of_disjoint]
        · have hun :
              Finset.univ.filter (fun j : Fin n => (!v j) = true) ∪
              Finset.univ.filter (fun j : Fin n => v j = true) = Finset.univ := by
            ext j
            cases v j <;> simp
          rw [hun, Finset.card_univ, Fintype.card_fin]
        · rw [Finset.disjoint_left]
          intro j h1 h2
          simp only [Finset.mem_filter] at h1 h2
          rw [h2.2] at h1
          exact Bool.noConfusion h1.2
      refine ⟨fun j => !(v j), ?_, by funext j; simp⟩
      simp only [lower, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
  have htails_le :
      ((Finset.univ : Finset X).filter (fun v => ¬ 16 * Nat.dist (2 * wt v) n ≤ n)).card ≤
        2 * upper.card := by
    calc ((Finset.univ : Finset X).filter (fun v => ¬ 16 * Nat.dist (2 * wt v) n ≤ n)).card
        ≤ (upper ∪ lower).card := Finset.card_le_card hsub
      _ ≤ upper.card + lower.card := Finset.card_union_le _ _
      _ = 2 * upper.card := by rw [hsymm, two_mul]
  suffices hup : upper.card * 2 ^ (n / 512) ≤ 2 ^ n by
    calc ((Finset.univ : Finset X).filter (fun v => ¬ 16 * Nat.dist (2 * wt v) n ≤ n)).card * 2 ^ (n / 512)
        ≤ (2 * upper.card) * 2 ^ (n / 512) := Nat.mul_le_mul_right _ htails_le
      _ = 2 * (upper.card * 2 ^ (n / 512)) := by ring
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 hup
      _ = 2 ^ (n + 1) := by rw [pow_succ, mul_comm]
  by_cases hemp : upper = ∅
  · rw [hemp]
    simp
  · have hne : upper.Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨vmin, hvmin, hmin⟩ := Finset.exists_min_image upper (fun v => 17 ^ wt v * 15 ^ (n - wt v)) hne
    have hsum_le : upper.card * (17 ^ wt vmin * 15 ^ (n - wt vmin)) ≤ 32 ^ n := by
      calc upper.card * (17 ^ wt vmin * 15 ^ (n - wt vmin))
          = ∑ _v ∈ upper, (17 ^ wt vmin * 15 ^ (n - wt vmin)) := by
              rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ v ∈ upper, (17 ^ wt v * 15 ^ (n - wt v)) := Finset.sum_le_sum hmin
        _ ≤ ∑ v : X, (17 ^ wt v * 15 ^ (n - wt v)) :=
              Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
        _ = (17 + 15) ^ n := sum_pow_wt n 17 15
        _ = 32 ^ n := by norm_num
    have hwt_min : 17 * n ≤ 32 * wt vmin := by
      have h := (Finset.mem_filter.mp hvmin).2
      omega
    have hwt_le_n : wt vmin ≤ n := by
      simpa [wt] using Finset.card_le_univ (Finset.univ.filter (fun j : Fin n => vmin j = true))
    have hpow32 : 17 ^ (17 * n) * 15 ^ (15 * n) ≤ (17 ^ wt vmin * 15 ^ (n - wt vmin)) ^ 32 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
      have hd : 32 * wt vmin = 17 * n + (32 * wt vmin - 17 * n) := by omega
      have hd2 : 15 * n = (n - wt vmin) * 32 + (32 * wt vmin - 17 * n) := by omega
      have hmul_comm1 : wt vmin * 32 = 32 * wt vmin := mul_comm _ _
      rw [hmul_comm1, hd, pow_add]
      conv_lhs => rw [hd2, pow_add]
      have h15_17 : 15 ^ (32 * wt vmin - 17 * n) ≤ 17 ^ (32 * wt vmin - 17 * n) :=
        Nat.pow_le_pow_left (by norm_num) _
      calc 17 ^ (17 * n) * (15 ^ ((n - wt vmin) * 32) * 15 ^ (32 * wt vmin - 17 * n))
          = (17 ^ (17 * n) * 15 ^ ((n - wt vmin) * 32)) * 15 ^ (32 * wt vmin - 17 * n) := by ring
        _ ≤ (17 ^ (17 * n) * 15 ^ ((n - wt vmin) * 32)) * 17 ^ (32 * wt vmin - 17 * n) :=
            Nat.mul_le_mul_left _ h15_17
        _ = 17 ^ (17 * n) * 17 ^ (32 * wt vmin - 17 * n) * 15 ^ ((n - wt vmin) * 32) := by ring
    have hnum1 : 106 * 16 ^ 32 ≤ 100 * (17 ^ 17 * 15 ^ 15) := by norm_num
    have hnum2 : 2 * 100 ^ 16 ≤ 106 ^ 16 := by norm_num
    have hnum := num_lift (16 ^ 32) (17 ^ 17 * 15 ^ 15) hnum1 hnum2
    have h32 : upper.card ^ 32 * (17 ^ 17 * 15 ^ 15) ^ n ≤ (2 ^ 32 * 16 ^ 32) ^ n := by
      have hB : (17 ^ 17 * 15 ^ 15) ^ n = 17 ^ (17 * n) * 15 ^ (15 * n) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
      have h32eq : (32 ^ n) ^ 32 = (2 ^ 32 * 16 ^ 32) ^ n := by
        rw [← mul_pow]
        have h216 : (2 * 16 : ℕ) = 32 := by norm_num
        rw [h216, ← pow_mul, ← pow_mul, mul_comm]
      rw [hB, ← h32eq]
      calc upper.card ^ 32 * (17 ^ (17 * n) * 15 ^ (15 * n))
          ≤ upper.card ^ 32 * (17 ^ wt vmin * 15 ^ (n - wt vmin)) ^ 32 :=
            Nat.mul_le_mul_left _ hpow32
        _ = (upper.card * (17 ^ wt vmin * 15 ^ (n - wt vmin))) ^ 32 := (mul_pow _ _ _).symm
        _ ≤ (32 ^ n) ^ 32 := Nat.pow_le_pow_left hsum_le 32
    exact chernoff_abstract upper.card n (16 ^ 32) (17 ^ 17 * 15 ^ 15) (by positivity) h32 hnum

lemma ball_card_lt (n : ℕ) :
    let X := Fin n → Bool
    let f := 1 + (3 * n + 7) / 8
    ((Finset.univ : Finset X).filter (fun v => v ≠ (fun _ => false) ∧ wt v ≤ n / 16)).card < 2 ^ f := by
  dsimp only
  let X := Fin n → Bool
  let B0 : Finset X := Finset.univ.filter (fun v => wt v ≤ n / 16)
  let B : Finset X := Finset.univ.filter (fun v => v ≠ (fun _ => false) ∧ wt v ≤ n / 16)
  have hzero_mem : (fun _ : Fin n => false) ∈ B0 := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp [wt]
  have hB_lt_B0 : B.card < B0.card := by
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [B, B0, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact hv.2
    · intro heq
      have hmem : (fun _ : Fin n => false) ∈ B := heq ▸ hzero_mem
      simp only [B, Finset.mem_filter] at hmem
      exact hmem.2.1 rfl
  suffices hB0 : B0.card ≤ 2 ^ (1 + (3 * n + 7) / 8) by
    change B.card < 2 ^ (1 + (3 * n + 7) / 8)
    omega
  have hne : B0.Nonempty := ⟨fun _ => false, hzero_mem⟩
  obtain ⟨vmin, hvmin, hmin⟩ := Finset.exists_min_image B0 (fun v => 16 ^ (n - wt v)) hne
  have hsum_le : B0.card * 16 ^ (n - wt vmin) ≤ 17 ^ n := by
    calc B0.card * 16 ^ (n - wt vmin)
        = ∑ _v ∈ B0, 16 ^ (n - wt vmin) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ B0, 16 ^ (n - wt v) := Finset.sum_le_sum hmin
      _ ≤ ∑ v : X, (1 ^ wt v * 16 ^ (n - wt v)) := by
            simp only [one_pow, one_mul]
            exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
      _ = (1 + 16) ^ n := sum_pow_wt n 1 16
      _ = 17 ^ n := by norm_num
  have hwt_min : wt vmin ≤ n / 16 := (Finset.mem_filter.mp hvmin).2
  have h15 : 15 * n ≤ (n - wt vmin) * 16 := by omega
  have hnum : 17 ^ 16 ≤ 2 ^ 6 * 16 ^ 15 := by norm_num
  have h16 : B0.card ^ 16 * 16 ^ (15 * n) ≤ 2 ^ (6 * n) * 16 ^ (15 * n) := by
    calc B0.card ^ 16 * 16 ^ (15 * n)
        ≤ B0.card ^ 16 * 16 ^ ((n - wt vmin) * 16) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h15)
      _ = (B0.card * 16 ^ (n - wt vmin)) ^ 16 := by rw [mul_pow, ← pow_mul]
      _ ≤ (17 ^ n) ^ 16 := Nat.pow_le_pow_left hsum_le 16
      _ = (17 ^ 16) ^ n := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ 6 * 16 ^ 15) ^ n := Nat.pow_le_pow_left hnum n
      _ = 2 ^ (6 * n) * 16 ^ (15 * n) := by rw [mul_pow, ← pow_mul, ← pow_mul]
  have h16' : B0.card ^ 16 ≤ (2 ^ (1 + (3 * n + 7) / 8)) ^ 16 := by
    have hcancel := Nat.le_of_mul_le_mul_right h16 (by positivity)
    rw [← pow_mul]
    have hexp : 6 * n ≤ (1 + (3 * n + 7) / 8) * 16 := by omega
    exact le_trans hcancel (Nat.pow_le_pow_right (by norm_num) hexp)
  exact le_of_pow_le_pow (by norm_num) h16'

lemma card_matrices_annihilating {n f : ℕ} (w : Fin n → ZMod 2) (hw : w ≠ 0) :
    ((Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))).filter
      (fun M => M.mulVec w = 0)).card * 2 ^ f =
      Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) := by
  have hex : ∃ j0 : Fin n, w j0 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hw (funext hall)
  obtain ⟨j0, hj0⟩ := hex
  have hwj0 : w j0 = 1 := by
    generalize w j0 = z at hj0 ⊢
    fin_cases z
    · exact absurd rfl hj0
    · rfl
  let Other := Matrix (Fin f) { j : Fin n // j ≠ j0 } (ZMod 2)
  let e : Matrix (Fin f) (Fin n) (ZMod 2) ≃ Other × (Fin f → ZMod 2) :=
    { toFun := fun M => (fun i j => M i j.1, M.mulVec w)
      invFun := fun p i j =>
        if h : j = j0 then
          p.2 i - ∑ k : { k : Fin n // k ≠ j0 }, p.1 i k * w k.1
        else p.1 i ⟨j, h⟩
      left_inv := fun M => by
        ext i j
        by_cases h : j = j0
        · subst j
          simp only [↓reduceDIte, Matrix.mulVec, dotProduct]
          have hsum :
              ∑ k : Fin n, M i k * w k =
                M i j0 + ∑ k : { k : Fin n // k ≠ j0 }, M i k.1 * w k.1 := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hwj0, mul_one]
            congr 1
            refine Finset.sum_bij (fun k hk => ⟨k, Finset.ne_of_mem_erase hk⟩)
              (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
            · intro k1 _ k2 _ h
              exact congrArg Subtype.val h
            · intro k _
              exact ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩, rfl⟩
          rw [hsum]
          ring
        · simp [h]
      right_inv := fun p => by
        refine Prod.ext (by ext i j; simp [j.2]) ?_
        ext i
        simp only [Matrix.mulVec, dotProduct]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j0), hwj0, mul_one]
        simp only [↓reduceDIte]
        have hsum :
            ∑ k ∈ Finset.univ.erase j0,
              (if h : k = j0 then p.2 i - ∑ k : { k : Fin n // k ≠ j0 }, p.1 i k * w k.1
                else p.1 i ⟨k, h⟩) * w k =
            ∑ k : { k : Fin n // k ≠ j0 }, p.1 i k * w k.1 := by
          refine Finset.sum_bij (fun k hk => ⟨k, Finset.ne_of_mem_erase hk⟩)
            (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
          · intro k1 _ k2 _ h
            exact congrArg Subtype.val h
          · intro k _
            exact ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩, rfl⟩
          · intro k hk
            have hne : k ≠ j0 := Finset.ne_of_mem_erase hk
            simp [hne]
        rw [hsum]
        ring }
  have hfib :
      ((Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))).filter
        (fun M => M.mulVec w = 0)).card = Fintype.card Other := by
    trans (Finset.univ : Finset Other).card
    · refine Finset.card_bij (t := (Finset.univ : Finset Other))
        (fun M _ => (e M).1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro M1 hM1 M2 hM2 heq
        have h1 : (e M1).2 = 0 := (Finset.mem_filter.mp hM1).2
        have h2 : (e M2).2 = 0 := (Finset.mem_filter.mp hM2).2
        exact e.injective (Prod.ext heq (h1.trans h2.symm))
      · intro A _
        refine ⟨e.symm (A, 0), ?_, by simp⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := congrArg Prod.snd (e.apply_symm_apply (A, 0))
        exact this
    · simp
  rw [hfib]
  have hcard := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin] at hcard
  exact hcard.symm

lemma exists_detecting_linear {n f : ℕ} (S : Finset (Fin n → ZMod 2))
    (h0 : ∀ w ∈ S, w ≠ 0) (hcard : S.card < 2 ^ f) :
    ∃ H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2),
      ∀ w ∈ S, H w ≠ 0 := by
  let Bad : Finset (Matrix (Fin f) (Fin n) (ZMod 2)) :=
    Finset.univ.filter (fun M => ∃ w ∈ S, M.mulVec w = 0)
  have hBad_sub : Bad ⊆ S.biUnion (fun w =>
      (Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))).filter (fun M => M.mulVec w = 0)) := by
    intro M hM
    simp only [Bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hM ⊢
    exact hM
  have hBad_mul :
      Bad.card * 2 ^ f ≤ S.card * Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) := by
    calc Bad.card * 2 ^ f
        ≤ (S.biUnion (fun w =>
            (Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))).filter
              (fun M => M.mulVec w = 0))).card * 2 ^ f :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hBad_sub)
      _ ≤ (∑ w ∈ S, ((Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))).filter
            (fun M => M.mulVec w = 0)).card) * 2 ^ f :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ w ∈ S, ((Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))).filter
            (fun M => M.mulVec w = 0)).card * 2 ^ f := Finset.sum_mul _ _ _
      _ = ∑ _w ∈ S, Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) :=
          Finset.sum_congr rfl (fun w hw => card_matrices_annihilating w (h0 w hw))
      _ = S.card * Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) := by
          rw [Finset.sum_const, smul_eq_mul]
  have htot_pos : 0 < Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) := by
    have : Nonempty (Matrix (Fin f) (Fin n) (ZMod 2)) := ⟨0⟩
    exact Fintype.card_pos
  have hlt : Bad.card < Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) := by
    have hmul : Bad.card * 2 ^ f < Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) * 2 ^ f := by
      calc Bad.card * 2 ^ f
          ≤ S.card * Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) := hBad_mul
        _ < 2 ^ f * Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) :=
            Nat.mul_lt_mul_of_pos_right hcard htot_pos
        _ = Fintype.card (Matrix (Fin f) (Fin n) (ZMod 2)) * 2 ^ f := mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hmul
  have hex : ∃ M : Matrix (Fin f) (Fin n) (ZMod 2), M ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Matrix (Fin f) (Fin n) (ZMod 2))) ⊆ Bad := fun M _ => hall M
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    omega
  obtain ⟨M, hM⟩ := hex
  refine ⟨Matrix.mulVecLin M, fun w hw => ?_⟩
  intro hzero
  exact hM (Finset.mem_filter.mpr ⟨Finset.mem_univ M, w, hw, hzero⟩)

lemma wt_cross_add {n : ℕ} (p1 p2 q1 q2 : Fin n → Bool)
    (hsum : ∀ j, (p1 j).toNat + (p2 j).toNat = (q1 j).toNat + (q2 j).toNat) :
    wt (fun j => xor (p1 j) (q2 j)) + wt (fun j => xor (p1 j) (q1 j)) =
      wt (fun j => xor (p1 j) (p2 j)) := by
  have hwt_sum : ∀ v : Fin n → Bool, wt v = ∑ j : Fin n, (v j).toNat := by
    intro v
    unfold wt
    have h1 : (Finset.univ.filter (fun j : Fin n => v j = true)).card =
        ∑ j : Fin n, if v j = true then 1 else 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [h1]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    cases v j <;> rfl
  rw [hwt_sum, hwt_sum, hwt_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hj := hsum j
  cases h1 : p1 j <;> cases h2 : p2 j <;> cases h3 : q1 j <;> cases h4 : q2 j <;>
    simp_all

end PEqualNP.Outside.L_lib_654_aux

theorem PEqualNP.Outside.L_lib_654 : (∀ n : ℕ,
  let X := Fin n → Bool
  let wt := fun v : X => (Finset.univ.filter (fun j : Fin n => v j = true)).card
  let diff := fun (x y : X) (j : Fin n) => xor (x j) (y j)
  let central := fun d : ℕ => 16 * Nat.dist (2*d) n ≤ n
  let tails := Finset.univ.filter (fun v : X => ¬central (wt v))
  let f := 1+(3*n+7)/8
  let vec := fun (x : X) (j : Fin n) => if x j then (1 : ZMod 2) else 0
  tails.card * 2^(n/512) ≤ 2^(n+1) ∧
    ∃ H : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin f → ZMod 2),
      (∀ x y : X, x ≠ y → wt (diff x y) ≤ n/16 → H (vec x) ≠ H (vec y)) ∧
      ∀ p q : X × X, p ≠ q → central (wt (diff p.1 p.2)) → central (wt (diff q.1 q.2)) →
        (∀ j, (p.1 j).toNat + (p.2 j).toNat = (q.1 j).toNat + (q.2 j).toNat) →
        H (vec p.1) = H (vec q.1) →
        ¬central (wt (diff p.1 q.2)) ∧ ¬central (wt (diff q.1 p.2))) := by
  intro n
  dsimp only
  refine ⟨PEqualNP.Outside.L_lib_654_aux.tails_card_bound n, ?_⟩
  let X := Fin n → Bool
  let diff : X → X → X := fun x y j => xor (x j) (y j)
  let f := 1 + (3 * n + 7) / 8
  let vec : X → (Fin n → ZMod 2) := fun x j => if x j then (1 : ZMod 2) else 0
  let B : Finset X := Finset.univ.filter (fun v => v ≠ (fun _ => false) ∧ PEqualNP.Outside.L_lib_654_aux.wt v ≤ n / 16)
  let S : Finset (Fin n → ZMod 2) := B.image vec
  have hvec_inj : Function.Injective vec := by
    intro x y hxy
    funext j
    have hj := congrFun hxy j
    cases hx : x j <;> cases hy : y j <;> simp_all [vec]
  have hS_ne0 : ∀ w ∈ S, w ≠ 0 := by
    intro w hw hzero
    obtain ⟨v, hvB, rfl⟩ := Finset.mem_image.mp hw
    have hvne : v ≠ (fun _ => false) := (Finset.mem_filter.mp hvB).2.1
    apply hvne
    apply hvec_inj
    rw [hzero]
    funext j
    simp [vec]
  have hS_card : S.card < 2 ^ f := by
    rw [Finset.card_image_of_injective _ hvec_inj]
    exact PEqualNP.Outside.L_lib_654_aux.ball_card_lt n
  obtain ⟨H, hH⟩ := PEqualNP.Outside.L_lib_654_aux.exists_detecting_linear S hS_ne0 hS_card
  have hvec_diff : ∀ x y : X, vec x - vec y = vec (diff x y) := by
    have hbit : ∀ a b : Bool,
        (if a = true then (1 : ZMod 2) else 0) - (if b = true then (1 : ZMod 2) else 0) =
          if xor a b = true then (1 : ZMod 2) else 0 := by
      intro a b
      cases a <;> cases b <;> decide
    intro x y
    funext j
    exact hbit (x j) (y j)
  have hdet : ∀ x y : X, x ≠ y → PEqualNP.Outside.L_lib_654_aux.wt (diff x y) ≤ n / 16 →
      H (vec x) ≠ H (vec y) := by
    intro x y hxy hwt hHeq
    have hdiff_ne : diff x y ≠ (fun _ => false) := by
      intro h0
      apply hxy
      funext j
      have hj := congrFun h0 j
      cases hx : x j <;> cases hy : y j <;> simp_all [diff]
    have hmem : vec (diff x y) ∈ S :=
      Finset.mem_image.mpr ⟨diff x y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdiff_ne, hwt⟩, rfl⟩
    have hzero : H (vec (diff x y)) = 0 := by
      rw [← hvec_diff x y, map_sub, hHeq, sub_self]
    exact hH _ hmem hzero
  refine ⟨H, hdet, fun p q hpq hcp hcq hsum hHpq => ?_⟩
  have hp1q1 : p.1 ≠ q.1 := by
    intro heq
    apply hpq
    refine Prod.ext heq ?_
    funext j
    have hj := hsum j
    rw [heq] at hj
    cases h1 : p.2 j <;> cases h2 : q.2 j <;> simp_all
  have hwt_gt : n / 16 < PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.1) := by
    by_contra hle
    push Not at hle
    exact hdet p.1 q.1 hp1q1 hle hHpq
  have h16gt : n < 16 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.1) := by omega
  have hcross1 : PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.2) +
      PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.1) =
      PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 p.2) :=
    PEqualNP.Outside.L_lib_654_aux.wt_cross_add p.1 p.2 q.1 q.2 hsum
  have hcross2 : PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2) +
      PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.1) =
      PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2) :=
    PEqualNP.Outside.L_lib_654_aux.wt_cross_add q.1 q.2 p.1 p.2 (fun j => (hsum j).symm)
  have h32p : 32 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 p.2) ≤ 17 * n := by
    by_cases hge : n ≤ 2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 p.2)
    · have hd : Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 p.2)) n =
          2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 p.2) - n :=
        Nat.dist_eq_sub_of_le_right hge
      change 16 * Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 p.2)) n ≤ n at hcp
      rw [hd] at hcp
      omega
    · omega
  have h32q : 32 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2) ≤ 17 * n := by
    by_cases hge : n ≤ 2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2)
    · have hd : Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2)) n =
          2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2) - n :=
        Nat.dist_eq_sub_of_le_right hge
      change 16 * Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2)) n ≤ n at hcq
      rw [hd] at hcq
      omega
    · omega
  have hsymm_pq : PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.1) =
      PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.1) := by
    unfold PEqualNP.Outside.L_lib_654_aux.wt diff
    congr 1
    ext j
    simp [Bool.xor_comm]
  constructor
  · intro hc
    have hlt15 : 32 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.2) < 15 * n := by omega
    have hle : 2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.2) ≤ n := by omega
    have hd : Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.2)) n =
        n - 2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.2) :=
      Nat.dist_eq_sub_of_le hle
    change 16 * Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff p.1 q.2)) n ≤ n at hc
    rw [hd] at hc
    omega
  · intro hc
    have hlt15 : 32 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2) < 15 * n := by
      change PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2) +
        PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.1) =
        PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 q.2) at hcross2
      omega
    have hle : 2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2) ≤ n := by omega
    have hd : Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2)) n =
        n - 2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2) :=
      Nat.dist_eq_sub_of_le hle
    change 16 * Nat.dist (2 * PEqualNP.Outside.L_lib_654_aux.wt (diff q.1 p.2)) n ≤ n at hc
    rw [hd] at hc
    omega
