import Mathlib.Data.Nat.Dist
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1038_aux

open Finset

theorem dist_eq_natAbs (a b : ℕ) : (Nat.dist a b : ℤ) = |(a : ℤ) - (b : ℤ)| := by
  unfold Nat.dist
  by_cases h : a ≤ b
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by omega)]
    ring
  · rw [Nat.sub_eq_zero_of_le (by omega : b ≤ a), add_zero, Nat.cast_sub (by omega),
      abs_of_nonneg (by omega)]

theorem second_moment_exists {t : ℕ} (S : Finset (Fin t))
    (w : {p : Fin t × Fin t // p.1 < p.2} → ℕ) :
    let E := {p : Fin t × Fin t // p.1 < p.2}
    let ES := (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)
    ∃ σ : Fin t → Bool,
      (∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (w e : ℤ) else -(w e : ℤ))) ^ 2 ≤
        ∑ e ∈ ES, (w e : ℤ) ^ 2 := by
  intro E ES
  let f : (Fin t → Bool) → ℤ := fun σ =>
    ∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (w e : ℤ) else -(w e : ℤ))
  have hsum_sq : ∑ σ : Fin t → Bool, (f σ) ^ 2 =
      (2 ^ t : ℤ) * ∑ e ∈ ES, (w e : ℤ) ^ 2 := by
    have hexp : ∀ σ : Fin t → Bool, (f σ) ^ 2 =
        ∑ e1 ∈ ES, ∑ e2 ∈ ES,
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ)) := by
      intro σ
      rw [sq, sum_mul]
      apply sum_congr rfl
      intro e1 _
      rw [mul_sum]
    simp_rw [hexp]
    rw [sum_comm]
    have hswap : ∀ e1 ∈ ES,
        (∑ σ : Fin t → Bool, ∑ e2 ∈ ES,
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ))) =
        ∑ e2 ∈ ES, ∑ σ : Fin t → Bool,
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ)) :=
      fun e1 _ => sum_comm
    rw [sum_congr rfl hswap, mul_sum]
    apply sum_congr rfl
    intro e1 he1
    rw [sum_eq_single e1]
    · have hdiag : ∀ σ : Fin t → Bool,
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) = (w e1 : ℤ) ^ 2 := by
        intro σ
        split_ifs <;> ring
      simp_rw [hdiag, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    · intro e2 _ hne
      have hex : ∃ u : Fin t,
          (u = e1.val.1 ∨ u = e1.val.2) ∧ u ≠ e2.val.1 ∧ u ≠ e2.val.2 ∨
          (u = e2.val.1 ∨ u = e2.val.2) ∧ u ≠ e1.val.1 ∧ u ≠ e1.val.2 := by
        by_contra hall
        push_neg at hall
        have h1 : e1.val.1 = e2.val.1 ∨ e1.val.1 = e2.val.2 := by
          by_contra hc
          push_neg at hc
          exact hc.2 ((hall e1.val.1).1 (Or.inl rfl) hc.1)
        have h2 : e1.val.2 = e2.val.1 ∨ e1.val.2 = e2.val.2 := by
          by_contra hc
          push_neg at hc
          exact hc.2 ((hall e1.val.2).1 (Or.inr rfl) hc.1)
        have hlt1 : e1.val.1 < e1.val.2 := e1.property
        have hlt2 : e2.val.1 < e2.val.2 := e2.property
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.trans h2.symm) (ne_of_lt hlt1)
        · exact hne (Subtype.ext (Prod.ext h1.symm h2.symm))
        · exact absurd (lt_trans (h2 ▸ hlt1) (h1 ▸ hlt2)) (lt_irrefl _)
        · exact absurd (h1.trans h2.symm) (ne_of_lt hlt1)
      obtain ⟨u, hu⟩ := hex
      let flip : (Fin t → Bool) ≃ (Fin t → Bool) :=
        { toFun := fun σ v => if v = u then !(σ v) else σ v
          invFun := fun σ v => if v = u then !(σ v) else σ v
          left_inv := fun σ => by ext v; by_cases h : v = u <;> simp [h]
          right_inv := fun σ => by ext v; by_cases h : v = u <;> simp [h] }
      have hneg : ∀ σ : Fin t → Bool,
          (if flip σ e1.val.1 = flip σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if flip σ e2.val.1 = flip σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ)) =
          -((if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
            (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ))) := by
        intro σ
        have hlt1 : e1.val.1 ≠ e1.val.2 := ne_of_lt e1.property
        have hlt2 : e2.val.1 ≠ e2.val.2 := ne_of_lt e2.property
        rcases hu with ⟨h1 | h1, h2a, h2b⟩ | ⟨h2 | h2, h1a, h1b⟩
        · have h1b : e1.val.2 ≠ u := fun h => hlt1 (h1.symm.trans h.symm)
          simp only [flip, Equiv.coe_fn_mk, h1.symm, ↓reduceIte, h1b, h2a.symm, h2b.symm]
          cases σ u <;> cases σ e1.val.2 <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
        · have h1a : e1.val.1 ≠ u := fun h => hlt1 (h.trans h1)
          simp only [flip, Equiv.coe_fn_mk, h1.symm, ↓reduceIte, h1a, h2a.symm, h2b.symm]
          cases σ u <;> cases σ e1.val.1 <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
        · have h2b : e2.val.2 ≠ u := fun h => hlt2 (h2.symm.trans h.symm)
          simp only [flip, Equiv.coe_fn_mk, h2.symm, ↓reduceIte, h2b, h1a.symm, h1b.symm]
          cases σ u <;> cases σ e2.val.2 <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
        · have h2a : e2.val.1 ≠ u := fun h => hlt2 (h.trans h2)
          simp only [flip, Equiv.coe_fn_mk, h2.symm, ↓reduceIte, h2a, h1a.symm, h1b.symm]
          cases σ u <;> cases σ e2.val.1 <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte] <;> ring
      have hsame : (∑ σ : Fin t → Bool,
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ))) =
          -(∑ σ : Fin t → Bool,
          (if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
          (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ))) := by
        calc _ = ∑ σ : Fin t → Bool,
              (if flip σ e1.val.1 = flip σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
              (if flip σ e2.val.1 = flip σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ)) :=
              (Fintype.sum_equiv flip _ _ (fun _ => rfl)).symm
          _ = ∑ σ : Fin t → Bool,
              -((if σ e1.val.1 = σ e1.val.2 then (w e1 : ℤ) else -(w e1 : ℤ)) *
                (if σ e2.val.1 = σ e2.val.2 then (w e2 : ℤ) else -(w e2 : ℤ))) :=
              sum_congr rfl (fun σ _ => hneg σ)
          _ = _ := by rw [Finset.sum_neg_distrib]
      linarith
    · intro h
      exact absurd he1 h
  by_contra hall
  push_neg at hall
  have hgt : (2 ^ t : ℤ) * ∑ e ∈ ES, (w e : ℤ) ^ 2 < ∑ σ : Fin t → Bool, (f σ) ^ 2 := by
    have hcard : (Finset.univ : Finset (Fin t → Bool)).card = 2 ^ t := by
      simp [Fintype.card_fun]
    have hne : (Finset.univ : Finset (Fin t → Bool)).Nonempty := ⟨fun _ => false, mem_univ _⟩
    calc (2 ^ t : ℤ) * ∑ e ∈ ES, (w e : ℤ) ^ 2
        = ∑ _σ : Fin t → Bool, ∑ e ∈ ES, (w e : ℤ) ^ 2 := by
          rw [sum_const, hcard, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ < ∑ σ : Fin t → Bool, (f σ) ^ 2 :=
          Finset.sum_lt_sum_of_nonempty hne (fun σ _ => hall σ)
  linarith

lemma arith_bound (m1 m2 MS total b : ℕ) (Δ : ℤ)
    (hsum : m1 + m2 = MS)
    (hdiff : (m1 : ℤ) - (m2 : ℤ) = Δ)
    (hgap : (2 * (total : ℤ) - 3 * (MS : ℤ)) ^ 2 ≤ 36 * (total : ℤ) * (b : ℤ))
    (hΔ : Δ ^ 2 ≤ (total : ℤ) * (b : ℤ)) :
    (Nat.dist (3 * m1) total) ^ 2 ≤ 64 * total * b ∧
    (Nat.dist (3 * m2) total) ^ 2 ≤ 64 * total * b := by
  have hs : (m1 : ℤ) + (m2 : ℤ) = (MS : ℤ) := by exact_mod_cast hsum
  have h1Z : ((Nat.dist (3 * m1) total : ℤ) ^ 2) ≤ 64 * (total : ℤ) * (b : ℤ) := by
    rw [dist_eq_natAbs, sq_abs]
    push_cast
    have h4 : 4 * (3 * (m1 : ℤ) - (total : ℤ)) ^ 2 =
        ((3 * (MS : ℤ) - 2 * (total : ℤ)) + 3 * Δ) ^ 2 := by
      have : 2 * (3 * (m1 : ℤ) - (total : ℤ)) = (3 * (MS : ℤ) - 2 * (total : ℤ)) + 3 * Δ := by
        linarith
      nlinarith
    nlinarith [sq_nonneg ((3 * (MS : ℤ) - 2 * (total : ℤ)) - 3 * Δ)]
  have h2Z : ((Nat.dist (3 * m2) total : ℤ) ^ 2) ≤ 64 * (total : ℤ) * (b : ℤ) := by
    rw [dist_eq_natAbs, sq_abs]
    push_cast
    have h4 : 4 * (3 * (m2 : ℤ) - (total : ℤ)) ^ 2 =
        ((3 * (MS : ℤ) - 2 * (total : ℤ)) - 3 * Δ) ^ 2 := by
      have : 2 * (3 * (m2 : ℤ) - (total : ℤ)) = (3 * (MS : ℤ) - 2 * (total : ℤ)) - 3 * Δ := by
        linarith
      nlinarith
    nlinarith [sq_nonneg ((3 * (MS : ℤ) - 2 * (total : ℤ)) + 3 * Δ)]
  exact ⟨by exact_mod_cast h1Z, by exact_mod_cast h2Z⟩

theorem part1 (t b z : ℕ) (hz : z ≤ b) (w : {p : Fin t × Fin t // p.1 < p.2} → ℕ)
    (hw : ∀ e, w e ≤ b) :
    let V := Fin t
    let E := {p : V × V // p.1 < p.2}
    let total := z + ∑ e : E, w e
    ∃ s : V → Fin 3,
      let reply := fun e : E =>
        if s e.val.1 = 0 ∨ s e.val.2 = 0 then (0 : Fin 3)
        else if s e.val.1 = s e.val.2 then 1 else 2
      ∀ j : Fin 3,
        let mass := (if j = 0 then z else 0) + ∑ e : E, (if reply e = j then w e else 0)
        (Nat.dist (3 * mass) total) ^ 2 ≤ 64 * total * b := by
  intro V E total
  set D : ℕ := ∑ e : E, w e
  by_cases hsmall : 3 * D < 2 * total
  · refine ⟨fun _ => 0, fun j => ?_⟩
    dsimp only
    have htot : total ≤ 3 * b := by omega
    fin_cases j <;> dsimp only
    · have hmass : (if (0 : Fin 3) = 0 then z else 0) +
          ∑ e : E, (if (if (0 : Fin 3) = 0 ∨ (0 : Fin 3) = 0 then (0 : Fin 3) else if (0 : Fin 3) = 0 then 1 else 2) = 0 then w e else 0) = total := by
        simp [total]
      change (Nat.dist (3 * ((if (0 : Fin 3) = 0 then z else 0) +
          ∑ e : E, (if (if (0 : Fin 3) = 0 ∨ (0 : Fin 3) = 0 then (0 : Fin 3) else if (0 : Fin 3) = 0 then 1 else 2) = 0 then w e else 0))) total) ^ 2 ≤ 64 * total * b
      rw [hmass]
      have hd : Nat.dist (3 * total) total = 2 * total := by
        unfold Nat.dist
        omega
      rw [hd]
      nlinarith
    · have hmass : (if (1 : Fin 3) = 0 then z else 0) +
          ∑ e : E, (if (if (0 : Fin 3) = 0 ∨ (0 : Fin 3) = 0 then (0 : Fin 3) else if (0 : Fin 3) = 0 then 1 else 2) = 1 then w e else 0) = 0 := by
        simp
      change (Nat.dist (3 * ((if (1 : Fin 3) = 0 then z else 0) +
          ∑ e : E, (if (if (0 : Fin 3) = 0 ∨ (0 : Fin 3) = 0 then (0 : Fin 3) else if (0 : Fin 3) = 0 then 1 else 2) = 1 then w e else 0))) total) ^ 2 ≤ 64 * total * b
      rw [hmass]
      have hd : Nat.dist (3 * 0) total = total := by
        unfold Nat.dist
        omega
      rw [hd]
      nlinarith
    · have hmass : (if (2 : Fin 3) = 0 then z else 0) +
          ∑ e : E, (if (if (0 : Fin 3) = 0 ∨ (0 : Fin 3) = 0 then (0 : Fin 3) else if (0 : Fin 3) = 0 then 1 else 2) = 2 then w e else 0) = 0 := by
        simp
      change (Nat.dist (3 * ((if (2 : Fin 3) = 0 then z else 0) +
          ∑ e : E, (if (if (0 : Fin 3) = 0 ∨ (0 : Fin 3) = 0 then (0 : Fin 3) else if (0 : Fin 3) = 0 then 1 else 2) = 2 then w e else 0))) total) ^ 2 ≤ 64 * total * b
      rw [hmass]
      have hd : Nat.dist (3 * 0) total = total := by
        unfold Nat.dist
        omega
      rw [hd]
      nlinarith
  · have hbig : 2 * total ≤ 3 * D := by omega
    let deg : V → ℕ := fun v =>
      ∑ e ∈ (Finset.univ : Finset E).filter (fun e => e.val.1 = v ∨ e.val.2 = v), w e
    have hsum_deg : ∑ v : V, deg v = 2 * D := by
      have h1 : ∀ v : V, deg v =
          ∑ e : E, ((if e.val.1 = v then w e else 0) + (if e.val.2 = v then w e else 0)) := by
        intro v
        symm
        rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset E)
          (fun e => e.val.1 = v ∨ e.val.2 = v)]
        have hz2 : ∑ e ∈ (Finset.univ : Finset E).filter (fun e => ¬(e.val.1 = v ∨ e.val.2 = v)),
            ((if e.val.1 = v then w e else 0) + (if e.val.2 = v then w e else 0)) = 0 := by
          apply sum_eq_zero
          intro e he
          have h := (mem_filter.mp he).2
          push_neg at h
          simp [h.1, h.2]
        rw [hz2, add_zero]
        apply sum_congr rfl
        intro e he
        have hlt : e.val.1 ≠ e.val.2 := ne_of_lt e.property
        rcases (mem_filter.mp he).2 with h1 | h2
        · have h2' : e.val.2 ≠ v := fun h => hlt (h1.trans h.symm)
          simp [h1, h2']
        · have h1' : e.val.1 ≠ v := fun h => hlt (h.trans h2.symm)
          simp [h1', h2]
      simp_rw [h1]
      rw [sum_comm]
      have heach : ∀ e : E, ∑ v : V,
          ((if e.val.1 = v then w e else 0) + (if e.val.2 = v then w e else 0)) = 2 * w e := by
        intro e
        rw [sum_add_distrib, sum_eq_single e.val.1 (fun v _ hv => by simp [hv.symm]) (fun h => absurd (mem_univ _) h),
          sum_eq_single e.val.2 (fun v _ hv => by simp [hv.symm]) (fun h => absurd (mem_univ _) h)]
        simp; ring
      simp_rw [heach, ← mul_sum]
      rfl
    let M : Finset V → ℕ := fun S =>
      ∑ e ∈ (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S), w e
    let H : Finset V := Finset.univ.filter (fun v => 4 * D * b < (deg v) ^ 2)
    have hMH : 2 * M H ≤ D := by
      by_cases hH : H.Nonempty
      · obtain ⟨vmin, hvmin_mem, hvmin_le⟩ := Finset.exists_min_image H deg hH
        have hdeg_gt : 4 * D * b < (deg vmin) ^ 2 := (mem_filter.mp hvmin_mem).2
        have hH_sum : H.card * deg vmin ≤ 2 * D := by
          calc H.card * deg vmin = ∑ _v ∈ H, deg vmin := by rw [sum_const, smul_eq_mul]
            _ ≤ ∑ v ∈ H, deg v := sum_le_sum (fun v hv => hvmin_le v hv)
            _ ≤ ∑ v : V, deg v := sum_le_sum_of_subset (subset_univ H)
            _ = 2 * D := hsum_deg
        have hH2b : H.card ^ 2 * b ≤ D := by
          by_cases hD0 : D = 0
          · rw [hD0] at hsum_deg hdeg_gt
            have hle : ∑ v ∈ H, deg v ≤ 0 := by
              calc ∑ v ∈ H, deg v ≤ ∑ v : V, deg v := sum_le_sum_of_subset (subset_univ H)
                _ = 2 * 0 := hsum_deg
                _ = 0 := rfl
            have : deg vmin = 0 := by
              have := single_le_sum (f := deg) (fun _ _ => Nat.zero_le _) hvmin_mem
              omega
            rw [this] at hdeg_gt
            omega
          · have hsq : H.card ^ 2 * (4 * D * b) ≤ (2 * D) ^ 2 := by
              calc H.card ^ 2 * (4 * D * b) ≤ H.card ^ 2 * (deg vmin) ^ 2 :=
                    Nat.mul_le_mul_left _ (le_of_lt hdeg_gt)
                _ = (H.card * deg vmin) ^ 2 := by ring
                _ ≤ (2 * D) ^ 2 := Nat.pow_le_pow_left hH_sum 2
            have hpos : 0 < 4 * D := by omega
            have hmul : H.card ^ 2 * b * (4 * D) ≤ D * (4 * D) := by linarith
            exact Nat.le_of_mul_le_mul_right hmul hpos
        have hMH_le : 2 * M H ≤ H.card ^ 2 * b := by
          have hcard_E : ((Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H)).card * 2 ≤
              H.card ^ 2 := by
            let f : E → V × V := fun e => e.val
            let s1 := ((Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H)).image (fun e => (e.val.1, e.val.2))
            let s2 := ((Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H)).image (fun e => (e.val.2, e.val.1))
            have hdisj : Disjoint s1 s2 := by
              rw [Finset.disjoint_left]
              intro p hp1 hp2
              obtain ⟨e1, _, rfl⟩ := mem_image.mp hp1
              obtain ⟨e2, _, h2⟩ := mem_image.mp hp2
              rw [Prod.mk.injEq] at h2
              exact absurd (lt_trans (h2.1 ▸ e2.property) (h2.2 ▸ e1.property)) (lt_irrefl _)
            have hsub : s1 ∪ s2 ⊆ H ×ˢ H := by
              intro p hp
              rcases mem_union.mp hp with hp1 | hp2
              · obtain ⟨e, he, rfl⟩ := mem_image.mp hp1
                exact mem_product.mpr (mem_filter.mp he).2
              · obtain ⟨e, he, rfl⟩ := mem_image.mp hp2
                exact mem_product.mpr ⟨(mem_filter.mp he).2.2, (mem_filter.mp he).2.1⟩
            have hc1 : s1.card = ((Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H)).card := by
              apply card_image_of_injective
              intro e1 e2 heq
              exact Subtype.ext heq
            have hc2 : s2.card = ((Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H)).card := by
              apply card_image_of_injective
              intro e1 e2 heq
              rw [Prod.mk.injEq] at heq
              exact Subtype.ext (Prod.ext heq.2 heq.1)
            have hle := card_le_card hsub
            rw [card_union_of_disjoint hdisj, hc1, hc2, card_product] at hle
            nlinarith
          calc 2 * M H = 2 * ∑ e ∈ (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H), w e := rfl
            _ ≤ 2 * ∑ _e ∈ (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H), b :=
                Nat.mul_le_mul_left 2 (sum_le_sum (fun e _ => hw e))
            _ = ((Finset.univ : Finset E).filter (fun e => e.val.1 ∈ H ∧ e.val.2 ∈ H)).card * 2 * b := by
                rw [sum_const, smul_eq_mul]; ring
            _ ≤ H.card ^ 2 * b := Nat.mul_le_mul_right b hcard_E
        exact hMH_le.trans hH2b
      · rw [Finset.not_nonempty_iff_eq_empty] at hH
        have hM0 : M H = 0 := by simp [M, hH]
        omega
    have hstep : ∀ (S : Finset V) (v : V), M (insert v S) ≤ M S + deg v := by
      intro S v
      let A1 := (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ insert v S ∧ e.val.2 ∈ insert v S)
      let A2 := (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)
      let A3 := (Finset.univ : Finset E).filter (fun e => e.val.1 = v ∨ e.val.2 = v)
      have hsub : A1 ⊆ A2 ∪ A3 := by
        intro e he
        have h := (mem_filter.mp he).2
        simp only [mem_insert] at h
        rw [mem_union, mem_filter, mem_filter]
        rcases h.1 with h1 | h1
        · exact Or.inr ⟨mem_univ _, Or.inl h1⟩
        · rcases h.2 with h2 | h2
          · exact Or.inr ⟨mem_univ _, Or.inr h2⟩
          · exact Or.inl ⟨mem_univ _, h1, h2⟩
      calc M (insert v S) = ∑ e ∈ A1, w e := rfl
        _ ≤ ∑ e ∈ A2 ∪ A3, w e := sum_le_sum_of_subset hsub
        _ ≤ ∑ e ∈ A2, w e + ∑ e ∈ A3, w e := by
            have := Finset.sum_union_inter (s₁ := A2) (s₂ := A3) (f := w)
            omega
        _ = M S + deg v := rfl
    have hexS : ∃ S : Finset V, 3 * M S ≤ 2 * total ∧ (2 * total - 3 * M S) ^ 2 ≤ 36 * total * b := by
      have hwalk : ∀ (R : Finset V) (S : Finset V),
          3 * M S ≤ 2 * total → 2 * total ≤ 3 * M (S ∪ R) →
          (∀ v ∈ R, (deg v) ^ 2 ≤ 4 * D * b) →
          ∃ S' : Finset V, 3 * M S' ≤ 2 * total ∧ (2 * total - 3 * M S') ^ 2 ≤ 36 * total * b := by
        intro R
        induction R using Finset.induction_on with
        | empty =>
          intro S h1 h2 _
          rw [union_empty] at h2
          exact ⟨S, h1, by
            have h0 : 2 * total - 3 * M S = 0 := by omega
            rw [h0]
            simp⟩
        | insert v R hv ih =>
          intro S h1 h2 hdegR
          by_cases hmid : 3 * M (insert v S) ≤ 2 * total
          · have h2' : 2 * total ≤ 3 * M (insert v S ∪ R) := by
              have : insert v S ∪ R = S ∪ insert v R := by
                ext x
                simp only [mem_union, mem_insert]
                tauto
              rwa [this]
            exact ih (insert v S) hmid h2' (fun u hu => hdegR u (mem_insert_of_mem hu))
          · refine ⟨S, h1, ?_⟩
            have hst := hstep S v
            have hdv : (deg v) ^ 2 ≤ 4 * D * b := hdegR v (mem_insert_self v R)
            have hgap : 2 * total - 3 * M S ≤ 3 * deg v := by omega
            have hDle : D ≤ total := by omega
            calc (2 * total - 3 * M S) ^ 2 ≤ (3 * deg v) ^ 2 := Nat.pow_le_pow_left hgap 2
              _ = 9 * (deg v) ^ 2 := by ring
              _ ≤ 9 * (4 * D * b) := Nat.mul_le_mul_left 9 hdv
              _ = 36 * D * b := by ring
              _ ≤ 36 * total * b := Nat.mul_le_mul_right b (Nat.mul_le_mul_left 36 hDle)
      refine hwalk Hᶜ H (by omega) ?_ (fun v hv => ?_)
      · have : H ∪ Hᶜ = Finset.univ := union_compl H
        rw [this]
        have hMuniv : M Finset.univ = D := by simp [M, D]
        rw [hMuniv]
        exact hbig
      · have hnot : v ∉ H := mem_compl.mp hv
        simp only [H, mem_filter, mem_univ, true_and, not_lt] at hnot
        exact hnot
    obtain ⟨S, hMS_le, hMS_gap⟩ := hexS
    obtain ⟨σ, hσ⟩ := second_moment_exists S w
    let s : V → Fin 3 := fun v => if v ∈ S then (if σ v then 1 else 2) else 0
    refine ⟨s, fun j => ?_⟩
    dsimp only
    let reply : E → Fin 3 := fun e =>
      if s e.val.1 = 0 ∨ s e.val.2 = 0 then (0 : Fin 3)
      else if s e.val.1 = s e.val.2 then 1 else 2
    let ES := (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)
    have hrep0 : ∀ e : E, reply e = 0 ↔ ¬(e.val.1 ∈ S ∧ e.val.2 ∈ S) := by
      intro e
      simp only [reply, s]
      by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S
      · simp only [h1, h2, ↓reduceIte, and_self, not_true_eq_false]
        cases σ e.val.1 <;> cases σ e.val.2 <;> decide
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    have hrep1 : ∀ e : E, reply e = 1 ↔ (e.val.1 ∈ S ∧ e.val.2 ∈ S ∧ σ e.val.1 = σ e.val.2) := by
      intro e
      simp only [reply, s]
      by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S
      · simp only [h1, h2, ↓reduceIte, true_and]
        cases σ e.val.1 <;> cases σ e.val.2 <;> decide
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    have hrep2 : ∀ e : E, reply e = 2 ↔ (e.val.1 ∈ S ∧ e.val.2 ∈ S ∧ σ e.val.1 ≠ σ e.val.2) := by
      intro e
      simp only [reply, s]
      by_cases h1 : e.val.1 ∈ S <;> by_cases h2 : e.val.2 ∈ S
      · simp only [h1, h2, ↓reduceIte, true_and]
        cases σ e.val.1 <;> cases σ e.val.2 <;> decide
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    have hm0 : (∑ e : E, if reply e = 0 then w e else 0) + M S = D := by
      simp only [M, ← sum_filter]
      change (∑ e ∈ (Finset.univ : Finset E).filter (fun e => reply e = 0), w e) +
          (∑ e ∈ (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S), w e) =
          ∑ e : E, w e
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset E)
        (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)]
      rw [add_comm]
      congr 1
      congr 1
      ext e
      simp only [mem_filter, mem_univ, true_and, hrep0]
    have hm12_sum : (∑ e : E, if reply e = 1 then w e else 0) +
        (∑ e : E, if reply e = 2 then w e else 0) = M S := by
      simp only [M, ← sum_filter]
      rw [← Finset.sum_filter_add_sum_filter_not ES (fun e => σ e.val.1 = σ e.val.2)]
      congr 1
      · congr 1
        ext e
        simp only [ES, mem_filter, mem_univ, true_and, hrep1]
        exact and_assoc.symm
      · congr 1
        ext e
        simp only [ES, mem_filter, mem_univ, true_and, hrep2]
        exact and_assoc.symm
    have hm12_diff : ((∑ e : E, if reply e = 1 then w e else 0 : ℕ) : ℤ) -
        ((∑ e : E, if reply e = 2 then w e else 0 : ℕ) : ℤ) =
        ∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (w e : ℤ) else -(w e : ℤ)) := by
      have h1 : ((∑ e : E, if reply e = 1 then w e else 0 : ℕ) : ℤ) =
          ∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (w e : ℤ) else 0) := by
        rw [← sum_filter, Nat.cast_sum, ← sum_filter]
        congr 1
        ext e
        simp only [ES, mem_filter, mem_univ, true_and, hrep1]
        exact and_assoc.symm
      have h2 : ((∑ e : E, if reply e = 2 then w e else 0 : ℕ) : ℤ) =
          ∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then 0 else (w e : ℤ)) := by
        have hswap : ∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (0 : ℤ) else (w e : ℤ)) =
            ∑ e ∈ ES, (if ¬(σ e.val.1 = σ e.val.2) then (w e : ℤ) else 0) := by
          apply sum_congr rfl
          intro e _
          by_cases h : σ e.val.1 = σ e.val.2 <;> simp [h]
        rw [hswap, ← sum_filter, Nat.cast_sum, ← sum_filter]
        congr 1
        ext e
        simp only [ES, mem_filter, mem_univ, true_and, hrep2]
        exact and_assoc.symm
      rw [h1, h2, ← sum_sub_distrib]
      apply sum_congr rfl
      intro e _
      split_ifs <;> ring
    have hDelta_sq : (∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (w e : ℤ) else -(w e : ℤ))) ^ 2 ≤
        (total : ℤ) * (b : ℤ) := by
      refine hσ.trans ?_
      have h1 : ∑ e ∈ ES, (w e : ℤ) ^ 2 ≤ ∑ e ∈ ES, (w e : ℤ) * (b : ℤ) :=
        sum_le_sum (fun e _ => by
          have := hw e
          rw [sq]
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity))
      refine h1.trans ?_
      rw [← sum_mul]
      have h2 : ∑ e ∈ ES, (w e : ℤ) ≤ (total : ℤ) := by
        have hMle : M S ≤ D := by
          simp only [M, D]
          exact sum_le_sum_of_subset (subset_univ _)
        have : M S ≤ total := by omega
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have hgapZ : (2 * (total : ℤ) - 3 * (M S : ℤ)) ^ 2 ≤ 36 * (total : ℤ) * (b : ℤ) := by
      have : ((2 * total - 3 * M S : ℕ) : ℤ) = 2 * (total : ℤ) - 3 * (M S : ℤ) := by omega
      rw [← this]
      exact_mod_cast hMS_gap
    have h12 := arith_bound
      (∑ e : E, if reply e = 1 then w e else 0)
      (∑ e : E, if reply e = 2 then w e else 0)
      (M S) total b
      (∑ e ∈ ES, (if σ e.val.1 = σ e.val.2 then (w e : ℤ) else -(w e : ℤ)))
      hm12_sum hm12_diff hgapZ hDelta_sq
    fin_cases j <;> dsimp only
    · change (Nat.dist (3 * ((if (0 : Fin 3) = 0 then z else 0) +
          ∑ e : E, if reply e = 0 then w e else 0)) total) ^ 2 ≤ 64 * total * b
      have hmass0 : (if (0 : Fin 3) = 0 then z else 0) +
          (∑ e : E, if reply e = 0 then w e else 0) = total - M S := by
        simp only [↓reduceIte]
        omega
      rw [hmass0]
      have hdist0 : Nat.dist (3 * (total - M S)) total = 2 * total - 3 * M S := by
        unfold Nat.dist
        have hMle : M S ≤ total := by omega
        omega
      rw [hdist0]
      exact hMS_gap.trans (Nat.mul_le_mul_right b (Nat.mul_le_mul_right total (by decide)))
    · change (Nat.dist (3 * ((if (1 : Fin 3) = 0 then z else 0) +
          ∑ e : E, if reply e = 1 then w e else 0)) total) ^ 2 ≤ 64 * total * b
      have hif : (if (1 : Fin 3) = 0 then z else 0) +
          (∑ e : E, if reply e = 1 then w e else 0) = ∑ e : E, if reply e = 1 then w e else 0 := by simp
      rw [hif]
      exact h12.1
    · change (Nat.dist (3 * ((if (2 : Fin 3) = 0 then z else 0) +
          ∑ e : E, if reply e = 2 then w e else 0)) total) ^ 2 ≤ 64 * total * b
      have hif : (if (2 : Fin 3) = 0 then z else 0) +
          (∑ e : E, if reply e = 2 then w e else 0) = ∑ e : E, if reply e = 2 then w e else 0 := by simp
      rw [hif]
      exact h12.2

theorem card_pairs_lt (t : ℕ) (S : Finset (Fin t)) :
    ((Finset.univ : Finset {p : Fin t × Fin t // p.1 < p.2}).filter
      (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)).card = S.card.choose 2 := by
  have h1 : 2 * ((Finset.univ : Finset {p : Fin t × Fin t // p.1 < p.2}).filter
      (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)).card = S.card * (S.card - 1) := by
    let E := {p : Fin t × Fin t // p.1 < p.2}
    let A := (Finset.univ : Finset E).filter (fun e => e.val.1 ∈ S ∧ e.val.2 ∈ S)
    let s1 := A.image (fun e => (e.val.1, e.val.2))
    let s2 := A.image (fun e => (e.val.2, e.val.1))
    have hdisj : Disjoint s1 s2 := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨e1, _, rfl⟩ := mem_image.mp hp1
      obtain ⟨e2, _, h2⟩ := mem_image.mp hp2
      rw [Prod.mk.injEq] at h2
      exact absurd (lt_trans (h2.1 ▸ e2.property) (h2.2 ▸ e1.property)) (lt_irrefl _)
    have hunion : s1 ∪ s2 = S.offDiag := by
      ext p
      simp only [s1, s2, A, mem_union, mem_image, mem_filter, mem_univ, true_and, mem_offDiag]
      constructor
      · rintro (⟨e, ⟨h1, h2⟩, rfl⟩ | ⟨e, ⟨h1, h2⟩, rfl⟩)
        · exact ⟨h1, h2, ne_of_lt e.property⟩
        · exact ⟨h2, h1, ne_of_gt e.property⟩
      · rintro ⟨h1, h2, hne⟩
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact Or.inl ⟨⟨p, hlt⟩, ⟨h1, h2⟩, rfl⟩
        · exact Or.inr ⟨⟨(p.2, p.1), hgt⟩, ⟨h2, h1⟩, rfl⟩
    have hc1 : s1.card = A.card := card_image_of_injective _ (fun _ _ h => Subtype.ext h)
    have hc2 : s2.card = A.card := card_image_of_injective _ (fun _ _ h => by
      rw [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.2 h.1))
    have hoff := congrArg Finset.card hunion
    have hoff_card : S.offDiag.card + S.card = S.card * S.card := by
      have hsplit := Finset.card_filter_add_card_filter_not (s := S ×ˢ S) (fun p => p.1 ≠ p.2)
      have h1 : ((S ×ˢ S).filter (fun p => p.1 ≠ p.2)) = S.offDiag := by
        ext p; simp [mem_offDiag, and_assoc]
      have h2 : ((S ×ˢ S).filter (fun p => ¬p.1 ≠ p.2)).card = S.card := by
        have heq : (S ×ˢ S).filter (fun p => ¬p.1 ≠ p.2) = S.image (fun v => (v, v)) := by
          ext p
          simp only [mem_filter, mem_product, not_not, mem_image]
          constructor
          · rintro ⟨⟨h1, _⟩, he⟩
            exact ⟨p.1, h1, Prod.ext rfl he⟩
          · rintro ⟨v, hv, rfl⟩
            exact ⟨⟨hv, hv⟩, rfl⟩
        rw [heq, card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
      rw [h1, h2, card_product] at hsplit
      exact hsplit
    rw [card_union_of_disjoint hdisj, hc1, hc2] at hoff
    have hmul : S.card * S.card - S.card = S.card * (S.card - 1) := by
      cases S.card with
      | zero => simp
      | succ n => simp [Nat.mul_succ, Nat.succ_mul]
    change 2 * A.card = S.card * (S.card - 1)
    omega
  rw [Nat.choose_two_right]
  omega

theorem part2 (t₀ : ℕ) (ht₀ : 16 ≤ t₀) :
    ∃ t : ℕ, (t = t₀ ∨ t = t₀ + 1) ∧
      ∀ s : Fin t → Fin 3,
        let E := {p : Fin t × Fin t // p.1 < p.2}
        let neutral := ((Finset.univ : Finset E).filter (fun e =>
          s e.val.1 = 0 ∨ s e.val.2 = 0)).card
        t ≤ 10 * Nat.dist (3 * neutral) (t.choose 2) := by
  by_contra hall
  push_neg at hall
  obtain ⟨s0, hs0⟩ := hall t₀ (Or.inl rfl)
  obtain ⟨s1, hs1⟩ := hall (t₀ + 1) (Or.inr rfl)
  dsimp only at hs0 hs1
  rw [not_le] at hs0 hs1
  have hneut : ∀ (t : ℕ) (s : Fin t → Fin 3),
      let E := {p : Fin t × Fin t // p.1 < p.2}
      let S := (Finset.univ : Finset (Fin t)).filter (fun v => s v ≠ 0)
      ((Finset.univ : Finset E).filter (fun e => s e.val.1 = 0 ∨ s e.val.2 = 0)).card +
        S.card.choose 2 = t.choose 2 := by
    intro t s E S
    have htot : (Finset.univ : Finset E).card = t.choose 2 := by
      have h := card_pairs_lt t Finset.univ
      simpa using h
    have hact : ((Finset.univ : Finset E).filter (fun e => ¬(s e.val.1 = 0 ∨ s e.val.2 = 0))).card =
        S.card.choose 2 := by
      rw [← card_pairs_lt t S]
      congr 1
      ext e
      simp [S, not_or]
    rw [← hact, Finset.card_filter_add_card_filter_not, htot]
  set j0 := ((Finset.univ : Finset (Fin t₀)).filter (fun v => s0 v ≠ 0)).card
  set j1 := ((Finset.univ : Finset (Fin (t₀ + 1))).filter (fun v => s1 v ≠ 0)).card
  have hn0 := hneut t₀ s0
  have hn1 := hneut (t₀ + 1) s1
  have hd0 : 5 * |(3 : ℤ) * (j0 : ℤ) * ((j0 : ℤ) - 1) - 2 * (t₀ : ℤ) * ((t₀ : ℤ) - 1)| < (t₀ : ℤ) := by
    have h20 : 2 * (t₀.choose 2) = t₀ * (t₀ - 1) := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self t₀).two_dvd]
    have h2j0 : 2 * (j0.choose 2) = j0 * (j0 - 1) := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self j0).two_dvd]
    have hdistZ : (Nat.dist (3 * ((Finset.univ : Finset {p : Fin t₀ × Fin t₀ // p.1 < p.2}).filter
        (fun e => s0 e.val.1 = 0 ∨ s0 e.val.2 = 0)).card) (t₀.choose 2) : ℤ) =
        |(3 : ℤ) * (j0.choose 2 : ℤ) - 2 * (t₀.choose 2 : ℤ)| := by
      rw [dist_eq_natAbs]
      push_cast
      have : (3 : ℤ) * (((Finset.univ : Finset {p : Fin t₀ × Fin t₀ // p.1 < p.2}).filter
          (fun e => s0 e.val.1 = 0 ∨ s0 e.val.2 = 0)).card : ℤ) - (t₀.choose 2 : ℤ) =
          -((3 : ℤ) * (j0.choose 2 : ℤ) - 2 * (t₀.choose 2 : ℤ)) := by
        have hn0Z : (((Finset.univ : Finset {p : Fin t₀ × Fin t₀ // p.1 < p.2}).filter
            (fun e => s0 e.val.1 = 0 ∨ s0 e.val.2 = 0)).card : ℤ) + (j0.choose 2 : ℤ) = (t₀.choose 2 : ℤ) := by
          exact_mod_cast hn0
        linarith
      rw [this, abs_neg]
    have hltZ : 10 * |(3 : ℤ) * (j0.choose 2 : ℤ) - 2 * (t₀.choose 2 : ℤ)| < (t₀ : ℤ) := by
      rw [← hdistZ]
      exact_mod_cast hs0
    have heq2 : (3 : ℤ) * (j0 : ℤ) * ((j0 : ℤ) - 1) - 2 * (t₀ : ℤ) * ((t₀ : ℤ) - 1) =
        2 * ((3 : ℤ) * (j0.choose 2 : ℤ) - 2 * (t₀.choose 2 : ℤ)) := by
      have ha : (2 : ℤ) * (t₀.choose 2 : ℤ) = (t₀ : ℤ) * ((t₀ : ℤ) - 1) := by
        have : (t₀ * (t₀ - 1) : ℕ) = 2 * t₀.choose 2 := h20.symm
        have h1 : ((t₀ * (t₀ - 1) : ℕ) : ℤ) = (t₀ : ℤ) * ((t₀ : ℤ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_sub (by omega)]; simp
        rw [← h1, this]; push_cast; ring
      have hb : (2 : ℤ) * (j0.choose 2 : ℤ) = (j0 : ℤ) * ((j0 : ℤ) - 1) := by
        cases hj0 : j0 with
        | zero => simp
        | succ k =>
          rw [hj0] at h2j0
          have : ((k + 1) * k : ℕ) = 2 * (k + 1).choose 2 := h2j0.symm
          have h1 : (((k + 1) * k : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) - 1) := by
            push_cast; ring
          rw [← h1, this]; push_cast; ring
      linarith
    rw [heq2, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2)]
    linarith
  have hd1 : 5 * |(3 : ℤ) * (j1 : ℤ) * ((j1 : ℤ) - 1) - 2 * ((t₀ : ℤ) + 1) * (t₀ : ℤ)| < (t₀ : ℤ) + 1 := by
    have h21 : 2 * ((t₀ + 1).choose 2) = (t₀ + 1) * t₀ := by
      rw [Nat.choose_two_right,
        Nat.mul_div_cancel' (Nat.even_mul_pred_self (t₀ + 1)).two_dvd, Nat.add_sub_cancel]
    have h2j1 : 2 * (j1.choose 2) = j1 * (j1 - 1) := by
      rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self j1).two_dvd]
    have hdistZ : (Nat.dist (3 * ((Finset.univ : Finset {p : Fin (t₀ + 1) × Fin (t₀ + 1) // p.1 < p.2}).filter
        (fun e => s1 e.val.1 = 0 ∨ s1 e.val.2 = 0)).card) ((t₀ + 1).choose 2) : ℤ) =
        |(3 : ℤ) * (j1.choose 2 : ℤ) - 2 * ((t₀ + 1).choose 2 : ℤ)| := by
      rw [dist_eq_natAbs]
      push_cast
      have : (3 : ℤ) * (((Finset.univ : Finset {p : Fin (t₀ + 1) × Fin (t₀ + 1) // p.1 < p.2}).filter
          (fun e => s1 e.val.1 = 0 ∨ s1 e.val.2 = 0)).card : ℤ) - ((t₀ + 1).choose 2 : ℤ) =
          -((3 : ℤ) * (j1.choose 2 : ℤ) - 2 * ((t₀ + 1).choose 2 : ℤ)) := by
        have hn1Z : (((Finset.univ : Finset {p : Fin (t₀ + 1) × Fin (t₀ + 1) // p.1 < p.2}).filter
            (fun e => s1 e.val.1 = 0 ∨ s1 e.val.2 = 0)).card : ℤ) + (j1.choose 2 : ℤ) = ((t₀ + 1).choose 2 : ℤ) := by
          exact_mod_cast hn1
        linarith
      rw [this, abs_neg]
    have hltZ : 10 * |(3 : ℤ) * (j1.choose 2 : ℤ) - 2 * ((t₀ + 1).choose 2 : ℤ)| < (t₀ : ℤ) + 1 := by
      rw [← hdistZ]
      exact_mod_cast hs1
    have heq2 : (3 : ℤ) * (j1 : ℤ) * ((j1 : ℤ) - 1) - 2 * ((t₀ : ℤ) + 1) * (t₀ : ℤ) =
        2 * ((3 : ℤ) * (j1.choose 2 : ℤ) - 2 * ((t₀ + 1).choose 2 : ℤ)) := by
      have ha : (2 : ℤ) * ((t₀ + 1).choose 2 : ℤ) = ((t₀ : ℤ) + 1) * (t₀ : ℤ) := by
        have : ((t₀ + 1) * t₀ : ℕ) = 2 * (t₀ + 1).choose 2 := h21.symm
        have h1 : (((t₀ + 1) * t₀ : ℕ) : ℤ) = ((t₀ : ℤ) + 1) * (t₀ : ℤ) := by push_cast; ring
        rw [← h1, this]; push_cast; ring
      have hb : (2 : ℤ) * (j1.choose 2 : ℤ) = (j1 : ℤ) * ((j1 : ℤ) - 1) := by
        cases hj1 : j1 with
        | zero => simp
        | succ k =>
          rw [hj1] at h2j1
          have : ((k + 1) * k : ℕ) = 2 * (k + 1).choose 2 := h2j1.symm
          have h1 : (((k + 1) * k : ℕ) : ℤ) = ((k + 1 : ℕ) : ℤ) * (((k + 1 : ℕ) : ℤ) - 1) := by
            push_cast; ring
          rw [← h1, this]; push_cast; ring
      linarith
    rw [heq2, abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 2)]
    linarith
  have hd0_lo : -(t₀ : ℤ) < 5 * (3 * (j0 : ℤ) * ((j0 : ℤ) - 1) - 2 * (t₀ : ℤ) * ((t₀ : ℤ) - 1)) := by
    linarith [neg_abs_le (3 * (j0 : ℤ) * ((j0 : ℤ) - 1) - 2 * (t₀ : ℤ) * ((t₀ : ℤ) - 1))]
  have hd0_hi : 5 * (3 * (j0 : ℤ) * ((j0 : ℤ) - 1) - 2 * (t₀ : ℤ) * ((t₀ : ℤ) - 1)) < (t₀ : ℤ) := by
    linarith [le_abs_self (3 * (j0 : ℤ) * ((j0 : ℤ) - 1) - 2 * (t₀ : ℤ) * ((t₀ : ℤ) - 1))]
  have hd1_lo : -((t₀ : ℤ) + 1) < 5 * (3 * (j1 : ℤ) * ((j1 : ℤ) - 1) - 2 * ((t₀ : ℤ) + 1) * (t₀ : ℤ)) := by
    linarith [neg_abs_le (3 * (j1 : ℤ) * ((j1 : ℤ) - 1) - 2 * ((t₀ : ℤ) + 1) * (t₀ : ℤ))]
  have hd1_hi : 5 * (3 * (j1 : ℤ) * ((j1 : ℤ) - 1) - 2 * ((t₀ : ℤ) + 1) * (t₀ : ℤ)) < (t₀ : ℤ) + 1 := by
    linarith [le_abs_self (3 * (j1 : ℤ) * ((j1 : ℤ) - 1) - 2 * ((t₀ : ℤ) + 1) * (t₀ : ℤ))]
  have htZ : (16 : ℤ) ≤ (t₀ : ℤ) := by exact_mod_cast ht₀
  have hj0_gt : 3 * (t₀ : ℤ) < 4 * (j0 : ℤ) := by
    by_contra hle
    push_neg at hle
    nlinarith
  have hj_lt : (j0 : ℤ) < (j1 : ℤ) := by
    by_contra hle
    push_neg at hle
    have hmono : (j1 : ℤ) * ((j1 : ℤ) - 1) ≤ (j0 : ℤ) * ((j0 : ℤ) - 1) := by
      have hj1_nn : (0 : ℤ) ≤ (j1 : ℤ) := by positivity
      nlinarith
    nlinarith
  have hj_step : (j0 : ℤ) + 1 ≤ (j1 : ℤ) := by omega
  have hjump : 6 * (j0 : ℤ) ≤ 3 * (j1 : ℤ) * ((j1 : ℤ) - 1) - 3 * (j0 : ℤ) * ((j0 : ℤ) - 1) := by
    have hj0_nn : (0 : ℤ) ≤ (j0 : ℤ) := by positivity
    nlinarith
  nlinarith

end PEqualNP.Outside.L_lib_1038_aux

theorem PEqualNP.Outside.L_lib_1038 : (∀ (t b z : ℕ), z ≤ b →
  let V := Fin t
  let E := {p : V × V // p.1 < p.2}
  ∀ w : E → ℕ, (∀ e, w e ≤ b) →
    let total := z + ∑ e : E, w e
    ∃ s : V → Fin 3,
      let reply := fun e : E =>
        if s e.val.1 = 0 ∨ s e.val.2 = 0 then (0 : Fin 3)
        else if s e.val.1 = s e.val.2 then 1 else 2
      ∀ j : Fin 3,
        let mass := (if j = 0 then z else 0) + ∑ e : E, (if reply e = j then w e else 0)
        (Nat.dist (3*mass) total)^2 ≤ 64*total*b) ∧
(∀ t₀ : ℕ, 16 ≤ t₀ → ∃ t : ℕ, (t = t₀ ∨ t = t₀+1) ∧
  ∀ s : Fin t → Fin 3,
    let E := {p : Fin t × Fin t // p.1 < p.2}
    let neutral := ((Finset.univ : Finset E).filter (fun e =>
      s e.val.1 = 0 ∨ s e.val.2 = 0)).card
    t ≤ 10 * Nat.dist (3*neutral) (t.choose 2)) :=
  ⟨PEqualNP.Outside.L_lib_1038_aux.part1, PEqualNP.Outside.L_lib_1038_aux.part2⟩
