import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_lib_390

namespace PEqualNP.Outside.L_clb_066_aux

-- Counting and AM-GM adapted from L_clb_069.lean at pin
-- 15f75666520387a9be8e84b0d8a24fc98ba6da1d. The decoder now sees
-- strictly earlier ranks; the score vectors are still injective per message.
private lemma sum_two_pow_matches (b : ℕ) (y : Fin b → Bool) :
    ∑ x : Fin b → Bool, (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = y i)).card) =
      (3 : ℝ) ^ b := by
  have hterm : ∀ x : Fin b → Bool,
      (2 : ℝ) ^ ((Finset.univ.filter (fun i : Fin b => x i = y i)).card) =
        ∏ i : Fin b, (if x i = y i then (2 : ℝ) else 1) := by
    intro x
    simp [Finset.prod_ite]
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun i c => if c = y i then (2 : ℝ) else 1)]
  have h1 : ∀ i : Fin b, (∑ c : Bool, if c = y i then (2 : ℝ) else 1) = 3 := by
    intro i; cases y i <;> norm_num
  simp_rw [h1]
  simp

private lemma amgm_bound (b coins S : ℕ) (hcoins : 0 < coins)
    (enc : Fin coins → (Fin b → Bool) → Fin S)
    (dec : Fin coins → Fin S → (Fin b → Bool) → Fin b → Bool)
    (rank : Fin b → ℕ)
    (hprefix : ∀ tape s x y i, (∀ j, rank j < rank i → x j = y j) →
      dec tape s x i = dec tape s y i)
    (hacc : ∀ (x : Fin b → Bool) (i : Fin b),
      2 * coins ≤ 3 * (Finset.univ.filter (fun tape : Fin coins =>
        dec tape (enc tape x) x i = x i)).card) :
    2 ^ b ≤ S ^ 15 := by
  have hsum_all : 2 * coins * (b * 2 ^ b) ≤
      3 * ∑ tape : Fin coins, ∑ x : Fin b → Bool,
        (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) x i = x i)).card := by
    have h1 : ∑ x : Fin b → Bool, ∑ i : Fin b, 2 * coins ≤
        ∑ x : Fin b → Bool, ∑ i : Fin b,
          3 * (Finset.univ.filter (fun tape : Fin coins =>
            dec tape (enc tape x) x i = x i)).card :=
      Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun i _ => hacc x i))
    have hlhs : (∑ _x : Fin b → Bool, ∑ _i : Fin b, 2 * coins) = 2 * coins * (b * 2 ^ b) := by
      simp [Finset.sum_const, smul_eq_mul]; ring
    rw [hlhs] at h1
    refine le_trans h1 ?_
    simp_rw [← Finset.mul_sum]
    apply Nat.mul_le_mul_left 3
    have hcard : ∀ (x : Fin b → Bool) (i : Fin b),
        (Finset.univ.filter (fun tape : Fin coins => dec tape (enc tape x) x i = x i)).card =
          ∑ tape : Fin coins, if dec tape (enc tape x) x i = x i then 1 else 0 := by
      intro x i; rw [Finset.card_filter]
    simp_rw [hcard]
    have hswap : (∑ x : Fin b → Bool, ∑ i : Fin b, ∑ tape : Fin coins,
        if dec tape (enc tape x) x i = x i then 1 else 0) =
      ∑ tape : Fin coins, ∑ x : Fin b → Bool, ∑ i : Fin b,
        if dec tape (enc tape x) x i = x i then 1 else 0 := by
      trans (∑ x : Fin b → Bool, ∑ tape : Fin coins, ∑ i : Fin b,
        if dec tape (enc tape x) x i = x i then 1 else 0)
      · apply Finset.sum_congr rfl; intro x _; exact Finset.sum_comm
      · exact Finset.sum_comm
    rw [hswap]
    apply le_of_eq
    apply Finset.sum_congr rfl; intro tape _
    apply Finset.sum_congr rfl; intro x _
    rw [Finset.card_filter]
  have hex_tape : ∃ tape : Fin coins,
      2 * b * 2 ^ b ≤ 3 * ∑ x : Fin b → Bool,
        (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) x i = x i)).card := by
    by_contra hnone
    push Not at hnone
    have hlt : ∑ tape : Fin coins,
        3 * ∑ x : Fin b → Bool,
          (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) x i = x i)).card <
        ∑ _tape : Fin coins, 2 * b * 2 ^ b := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨⟨0, hcoins⟩, Finset.mem_univ _⟩
      · intro tape _; exact hnone tape
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hlt
    have : coins * (2 * b * 2 ^ b) = 2 * coins * (b * 2 ^ b) := by ring
    omega
  obtain ⟨tape, htape⟩ := hex_tape
  let m : (Fin b → Bool) → ℕ := fun x =>
    (Finset.univ.filter (fun i : Fin b => x i = dec tape (enc tape x) x i)).card
  have hm_eq : ∀ x, m x =
      (Finset.univ.filter (fun i : Fin b => dec tape (enc tape x) x i = x i)).card := by
    intro x; dsimp [m]; congr 1; ext i; simp [eq_comm]
  have hsum_m : 2 * b * 2 ^ b ≤ 3 * ∑ x : Fin b → Bool, m x := by
    simpa [hm_eq] using htape
  have hupper : ∑ x : Fin b → Bool, (2 : ℝ) ^ (m x) ≤ (S : ℝ) * (3 : ℝ) ^ b := by
    have h1 : ∑ x : Fin b → Bool, (2 : ℝ) ^ (m x) =
        ∑ s : Fin S, ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s),
          (2 : ℝ) ^ (m x) := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := enc tape) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
    rw [h1]
    have h2 : ∀ s : Fin S,
        ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s), (2 : ℝ) ^ (m x) ≤
          (3 : ℝ) ^ b := by
      intro s
      let score (x : Fin b → Bool) (i : Fin b) := decide (x i = dec tape s x i)
      have hinj : Function.Injective score := by
        intro x y hxy
        funext i
        have agree : ∀ n (j : Fin b), rank j = n → x j = y j := by
          intro n
          induction n using Nat.strong_induction_on with
          | ind n ih =>
            intro j hj
            have hp := hprefix tape s x y j (fun k hk => ih (rank k) (hj ▸ hk) k rfl)
            have hs : decide (x j = dec tape s x j) = decide (y j = dec tape s y j) :=
              congrFun hxy j
            rw [hp] at hs
            have cancel (u v q : Bool) :
                decide (u = q) = decide (v = q) → u = v := by
              cases u <;> cases v <;> cases q <;> decide
            exact cancel _ _ _ hs
        exact agree (rank i) i rfl
      let F := Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s)
      let weight (v : Fin b → Bool) := (2 : ℝ) ^ ((Finset.univ.filter
        (fun i : Fin b => v i = (fun _ : Fin b => true) i)).card)
      change ∑ x ∈ F, (2 : ℝ) ^ (m x) ≤ (3 : ℝ) ^ b
      calc
        ∑ x ∈ F, (2 : ℝ) ^ (m x) = ∑ x ∈ F, weight (score x) := by
          apply Finset.sum_congr rfl
          intro x hx
          have he : enc tape x = s := (Finset.mem_filter.mp hx).2
          simp [m, he, score, weight]
        _ = ∑ v ∈ F.image score, weight v := by
          rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
        _ ≤ ∑ v : Fin b → Bool, weight v :=
          Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
        _ = (3 : ℝ) ^ b := sum_two_pow_matches b (fun _ => true)
    calc ∑ s : Fin S, ∑ x ∈ Finset.univ.filter (fun x : Fin b → Bool => enc tape x = s),
            (2 : ℝ) ^ (m x)
        ≤ ∑ _s : Fin S, (3 : ℝ) ^ b := Finset.sum_le_sum (fun s _ => h2 s)
      _ = (S : ℝ) * (3 : ℝ) ^ b := by simp
  have h2b_pos : (0 : ℝ) < (2 : ℝ) ^ b := by positivity
  have hw_sum : ∑ _x : Fin b → Bool, (1 : ℝ) / (2 : ℝ) ^ b = 1 := by
    rw [Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (Fin b → Bool) = 2 ^ b := by simp
    rw [hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin b → Bool))
    (fun _ => (1 : ℝ) / (2 : ℝ) ^ b) (fun x => (2 : ℝ) ^ (m x))
    (fun _ _ => by positivity) hw_sum (fun _ _ => by positivity)
  have hlhs_gm : ∏ x : Fin b → Bool, ((2 : ℝ) ^ (m x)) ^ ((1 : ℝ) / (2 : ℝ) ^ b) =
      (2 : ℝ) ^ ((∑ x : Fin b → Bool, (m x : ℝ)) / (2 : ℝ) ^ b) := by
    have h1 : ∀ x : Fin b → Bool,
        ((2 : ℝ) ^ (m x)) ^ ((1 : ℝ) / (2 : ℝ) ^ b) =
          (2 : ℝ) ^ ((m x : ℝ) / (2 : ℝ) ^ b) := by
      intro x
      rw [← Real.rpow_natCast (2 : ℝ) (m x), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      ring_nf
    simp_rw [h1]
    rw [← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2), ← Finset.sum_div]
  rw [hlhs_gm] at hamgm
  have hrhs_am : ∑ x : Fin b → Bool, (1 : ℝ) / (2 : ℝ) ^ b * (2 : ℝ) ^ (m x) ≤
      (S : ℝ) * (3 : ℝ) ^ b / (2 : ℝ) ^ b := by
    rw [← Finset.mul_sum, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hupper (le_of_lt h2b_pos)
  have hexp_ge : (2 : ℝ) * (b : ℝ) / 3 ≤ (∑ x : Fin b → Bool, (m x : ℝ)) / (2 : ℝ) ^ b := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 3) h2b_pos]
    have hcast : (2 * b * 2 ^ b : ℝ) ≤ 3 * ∑ x : Fin b → Bool, (m x : ℝ) := by
      exact_mod_cast hsum_m
    linarith
  have h2_le : (2 : ℝ) ^ ((2 : ℝ) * (b : ℝ) / 3) ≤ (S : ℝ) * (3 : ℝ) ^ b / (2 : ℝ) ^ b :=
    le_trans (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_ge)
      (le_trans hamgm hrhs_am)
  have hcube : ((2 : ℝ) ^ ((2 : ℝ) * (b : ℝ) / 3)) ^ (3 : ℕ) ≤
      ((S : ℝ) * (3 : ℝ) ^ b / (2 : ℝ) ^ b) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) h2_le 3
  have hcube_lhs : ((2 : ℝ) ^ ((2 : ℝ) * (b : ℝ) / 3)) ^ (3 : ℕ) = (4 : ℝ) ^ b := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have : (2 : ℝ) * (b : ℝ) / 3 * (3 : ℕ) = (2 * b : ℕ) := by push_cast; ring
    rw [this, Real.rpow_natCast, pow_mul]
    norm_num
  rw [hcube_lhs, div_pow, mul_pow, le_div_iff₀ (by positivity : (0 : ℝ) < ((2 : ℝ) ^ b) ^ 3)] at hcube
  have h32 : (32 : ℝ) ^ b ≤ (27 : ℝ) ^ b * (S : ℝ) ^ 3 := by
    have h1 : (4 : ℝ) ^ b * ((2 : ℝ) ^ b) ^ 3 = (32 : ℝ) ^ b := by
      rw [← pow_mul, mul_comm b 3, pow_mul, ← mul_pow]
      norm_num
    have h2 : ((3 : ℝ) ^ b) ^ 3 = (27 : ℝ) ^ b := by
      rw [← pow_mul, mul_comm b 3, pow_mul]
      norm_num
    rw [h1, h2] at hcube
    linarith
  have h5 : ((32 : ℝ) ^ b) ^ 5 ≤ ((27 : ℝ) ^ b * (S : ℝ) ^ 3) ^ 5 :=
    pow_le_pow_left₀ (by positivity) h32 5
  have h5_lhs : (2 : ℝ) ^ b * ((27 : ℝ) ^ b) ^ 5 ≤ ((32 : ℝ) ^ b) ^ 5 := by
    have h1 : (2 : ℝ) ^ b * ((27 : ℝ) ^ b) ^ 5 = ((2 : ℝ) * 27 ^ 5) ^ b := by
      rw [← pow_mul, mul_comm b 5, pow_mul, ← mul_pow]
    have h2 : ((32 : ℝ) ^ b) ^ 5 = ((32 : ℝ) ^ 5) ^ b := by
      rw [← pow_mul, mul_comm b 5, pow_mul]
    rw [h1, h2]
    apply pow_le_pow_left₀ (by positivity)
    norm_num
  have h5_rhs : ((27 : ℝ) ^ b * (S : ℝ) ^ 3) ^ 5 = ((27 : ℝ) ^ b) ^ 5 * (S : ℝ) ^ 15 := by
    rw [mul_pow, ← pow_mul (S : ℝ) 3 5]
  have hfinal_r : (2 : ℝ) ^ b ≤ (S : ℝ) ^ 15 := by
    have hpos27 : (0 : ℝ) < ((27 : ℝ) ^ b) ^ 5 := by positivity
    nlinarith
  exact_mod_cast hfinal_r

end PEqualNP.Outside.L_clb_066_aux

open PEqualNP.Outside.L_clb_066_aux in
theorem PEqualNP.Outside.L_clb_066 :
∀ (d L coins S : ℕ),
  let w := d + 1
  let State := Fin w → Bool
  let Tail := Fin d → Bool
  let Pat := Fin (w + 1) → Bool
  let Part := fun k : ℕ => Fin k → Pat → Bool
  let Config := Fin L → Tail → Bool
  let first := fun (c : Config) (h : Fin L) (p : Pat) =>
    decide (p (Fin.last w) = xor (p 0) (c h (fun b => p b.succ.castSucc)))
  let last := fun (a : State) (k : Fin w) (r : Fin w) (p : Pat) =>
    decide (p (Fin.last w) = a r ∧ (r.val = 0 → p k.castSucc = true))
  let ok := fun (P : Part L) (Q : Part w) (x : Fin (L + d + 1) → Bool) =>
    (∀ row : Fin L, P row (fun j => x (Fin.ofNat (L + d + 1) (row.val + j.val))) = true) ∧
    ∀ r : Fin w, Q r (fun j => x (Fin.ofNat (L + d + 1) (L + r.val + j.val))) = true
  0 < coins →
    ∀ (send : Fin coins → Part L → Fin S) (finish : Fin coins → Fin S → Part w → Bool),
      (∀ (c : Config) (a : State) (k : Fin w),
        2 * coins ≤ 3 * ((Finset.univ : Finset (Fin coins)).filter (fun tape =>
          (finish tape (send tape (first c)) (last a k) = true ↔
            ∃ x, ok (first c) (last a k) x))).card) →
      2 ^ (min L w * 2 ^ d) ≤ S ^ 15 := by
  classical
  intro d L coins S w State Tail Pat Part Config first last ok hcoins send finish hprot
  obtain ⟨select, hprefix, hquery⟩ := PEqualNP.Outside.L_lib_390 d L
  let m := min L w
  let b := m * 2 ^ d
  let Index := Fin m × Tail
  have hcard : Fintype.card Index = b := by simp [Index, Tail, b]
  let e : Index ≃ Fin b := Fintype.equivFinOfCardEq hcard
  let row (i : Fin m) : Fin L := ⟨L - m + i.val, by
    have hi := i.isLt
    have hm : m ≤ L := min_le_left _ _
    omega⟩
  let offset (h : Fin L) (hh : L - m ≤ h.val) : Fin m := ⟨h.val - (L - m), by
    have hi := h.isLt
    have hm : m ≤ L := min_le_left _ _
    omega⟩
  let cfg (x : Fin b → Bool) : Config := fun h z =>
    if hh : L - m ≤ h.val then x (e (offset h hh, z)) else false
  have cfg_row (x : Fin b → Bool) (i : Fin m) (z : Tail) :
      cfg x (row i) z = x (e (i, z)) := by
    have hh : L - m ≤ (row i).val := by dsimp [row]; omega
    have he : offset (row i) hh = i := by apply Fin.ext; dsimp [offset, row]; omega
    simp only [cfg, dite_eq_left hh, he]
  let rank (i : Fin b) := (e.symm i).1.val
  let enc (t : Fin coins) (x : Fin b → Bool) := send t (first (cfg x))
  let dec (t : Fin coins) (s : Fin S) (x : Fin b → Bool) (i : Fin b) :=
    let h := row (e.symm i).1
    let z := (e.symm i).2
    finish t s (last (select (cfg x) h z) (Fin.ofNat w (w - (L - h.val))))
  change 2 ^ b ≤ S ^ 15
  apply amgm_bound b coins S hcoins enc dec rank
  · intro t s x y i agree
    dsimp only [dec]
    congr 2
    apply hprefix
    intro h hh
    funext z
    by_cases hactive : L - m ≤ h.val
    · let j := e (offset h hactive, z)
      have hj : rank j < rank i := by
        have he : e.symm j = (offset h hactive, z) := e.symm_apply_apply _
        dsimp only [rank]
        rw [he]
        change h.val - (L - m) < (e.symm i).1.val
        change h.val < L - m + (e.symm i).1.val at hh
        omega
      simp only [cfg, dite_eq_left hactive]
      exact agree j hj
    · simp only [cfg, dite_eq_right hactive]
  · intro x i
    let h := row (e.symm i).1
    let z := (e.symm i).2
    let a := select (cfg x) h z
    let k := Fin.ofNat w (w - (L - h.val))
    have near : L ≤ h.val + w := by
      have hm : m ≤ w := min_le_right _ _
      dsimp [h, row]
      omega
    have hc : cfg x h z = x i := by
      rw [cfg_row]
      exact congrArg x (e.apply_symm_apply i)
    have hc' := hquery (cfg x) h z near
    change (Finset.univ.filter (ok (first (cfg x)) (last a k))).card =
      (if cfg x h z = true then 1 else 0) at hc'
    have hyes : (∃ y, ok (first (cfg x)) (last a k) y) ↔ x i = true := by
      rw [hc] at hc'
      constructor
      · rintro ⟨y, hy⟩
        have hp := Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
        by_contra hn
        rw [hc', ite_eq_right hn] at hp
        omega
      · intro hy
        rw [ite_eq_left hy] at hc'
        obtain ⟨y, hy'⟩ := Finset.card_pos.mp (show 0 < _ from hc' ▸ Nat.zero_lt_one)
        exact ⟨y, (Finset.mem_filter.mp hy').2⟩
    have hb (u v : Bool) : ((u = true ↔ v = true) ↔ u = v) := by
      cases u <;> cases v <;> decide
    simpa only [enc, dec, ← show row (e.symm i).1 = h from rfl,
      ← show (e.symm i).2 = z from rfl, hyes, hb] using hprot (cfg x) a k
