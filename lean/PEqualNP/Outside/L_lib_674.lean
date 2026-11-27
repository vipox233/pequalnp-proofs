import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_674

open scoped BigOperators

private lemma star_inj {b : ℕ} :
    Function.Injective (fun (p : Fin b → Option Bool) (x : Bool × (Fin b → Bool)) =>
      decide (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i))) := by
  intro p₁ p₂ h
  funext i₀
  by_contra hne
  have aux : ∀ (q₁ q₂ : Fin b → Option Bool) (c : Bool),
      (fun x : Bool × (Fin b → Bool) =>
        decide (x.1 = true ∨ ∀ i : Fin b, q₁ i = none ∨ q₁ i = some (x.2 i))) =
      (fun x : Bool × (Fin b → Bool) =>
        decide (x.1 = true ∨ ∀ i : Fin b, q₂ i = none ∨ q₂ i = some (x.2 i))) →
      q₁ i₀ = some c → q₂ i₀ ≠ some c → False := by
    intro q₁ q₂ c heq h1 h2
    let y : Fin b → Bool := fun i => if i = i₀ then !c else (q₂ i).getD false
    have hq2 : ∀ i : Fin b, q₂ i = none ∨ q₂ i = some (y i) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        cases hq : q₂ i with
        | none => left; rfl
        | some d =>
          right
          have hdc : d ≠ c := fun hdc => h2 (by simp [hq, hdc])
          have : d = !c := by cases c <;> cases d <;> simp_all
          simp [y, this]
      · cases hq : q₂ i with
        | none => left; rfl
        | some d => right; simp [y, hi, hq]
    have ht2 : (fun x : Bool × (Fin b → Bool) =>
        decide (x.1 = true ∨ ∀ i : Fin b, q₂ i = none ∨ q₂ i = some (x.2 i))) (false, y) = true := by
      simp [hq2]
    have ht1 : (fun x : Bool × (Fin b → Bool) =>
        decide (x.1 = true ∨ ∀ i : Fin b, q₁ i = none ∨ q₁ i = some (x.2 i))) (false, y) = true := by
      rw [heq]; exact ht2
    simp only [decide_eq_true_eq, Bool.false_eq_true, false_or] at ht1
    rcases ht1 i₀ with hnone | hsome
    · rw [h1] at hnone; cases hnone
    · rw [h1] at hsome
      have : c = y i₀ := Option.some.inj hsome
      simp [y] at this
  cases hp1 : p₁ i₀ with
  | none =>
    cases hp2 : p₂ i₀ with
    | none => exact hne (hp1.trans hp2.symm)
    | some c => exact aux p₂ p₁ c h.symm hp2 (by simp [hp1])
  | some c =>
    exact aux p₁ p₂ c h hp1 (by rw [hp1] at hne; exact Ne.symm hne)

private lemma count_star_diff_le {b r : ℕ} (x : Bool × (Fin b → Bool)) :
    ((Finset.univ : Finset (Fin b → Option Bool)).filter (fun p =>
      (Finset.univ.filter (fun i : Fin b => (p i).isSome = true)).card = r ∧
      decide (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i)) ≠ x.1)).card
      ≤ Nat.choose b r := by
  let fam := (Finset.univ : Finset (Fin b → Option Bool)).filter (fun p =>
    (Finset.univ.filter (fun i : Fin b => (p i).isSome = true)).card = r)
  let A := fam.filter (fun p =>
    decide (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i)) ≠ x.1)
  have hA_eq : (Finset.univ : Finset (Fin b → Option Bool)).filter (fun p =>
      (Finset.univ.filter (fun i : Fin b => (p i).isSome = true)).card = r ∧
      decide (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i)) ≠ x.1) = A := by
    ext p; simp [A, fam]
  rw [hA_eq]
  cases hx1 : x.1
  · let supp : (Fin b → Option Bool) → Finset (Fin b) :=
      fun p => Finset.univ.filter (fun i : Fin b => (p i).isSome = true)
    have hcard : A.card ≤ ((Finset.univ : Finset (Fin b)).powersetCard r).card := by
      apply Finset.card_le_card_of_injOn supp
      · intro p hp
        have hp_fam := (Finset.mem_filter.mp hp).1
        have hp_r := (Finset.mem_filter.mp hp_fam).2
        exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hp_r⟩
      · intro p₁ hp₁ p₂ hp₂ hsupp
        have hsat₁ : ∀ i, p₁ i = none ∨ p₁ i = some (x.2 i) := by
          have h := (Finset.mem_filter.mp hp₁).2
          simp only [hx1, ne_eq, decide_eq_true_eq, Bool.false_eq_true, false_or,
            Bool.not_eq_false] at h
          exact h
        have hsat₂ : ∀ i, p₂ i = none ∨ p₂ i = some (x.2 i) := by
          have h := (Finset.mem_filter.mp hp₂).2
          simp only [hx1, ne_eq, decide_eq_true_eq, Bool.false_eq_true, false_or,
            Bool.not_eq_false] at h
          exact h
        funext i
        have hi : i ∈ supp p₁ ↔ i ∈ supp p₂ := by rw [hsupp]
        simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        by_cases hs1 : (p₁ i).isSome = true
        · have hs2 : (p₂ i).isSome = true := hi.mp hs1
          rcases hsat₁ i with h1 | h1
          · simp [h1] at hs1
          · rcases hsat₂ i with h2 | h2
            · simp [h2] at hs2
            · exact h1.trans h2.symm
        · have hs2 : (p₂ i).isSome ≠ true := fun h => hs1 (hi.mpr h)
          cases hp1i : p₁ i <;> cases hp2i : p₂ i <;> simp_all
    simpa [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] using hcard
  · have hA_empty : A = ∅ := by
      ext p
      simp [A, hx1]
    simp [hA_empty]

private lemma sum_bool_pow {q v : ℕ} :
    ∑ g : Fin q → Bool, v ^ (q - (Finset.univ.filter (fun j : Fin q => g j = true)).card) =
      (v + 1) ^ q := by
  have h1 : (v + 1) ^ q = ∏ _j : Fin q, (v + 1) := by simp
  rw [h1, Finset.prod_add (fun _ : Fin q => v) (fun _ : Fin q => 1) Finset.univ]
  simp only [Finset.prod_const, one_pow, mul_one]
  symm
  refine Finset.sum_bij (fun g _ => Finset.univ.filter (fun j : Fin q => g j = false)) ?_ ?_ ?_ ?_ |>.symm
  · intro g _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
  · intro g₁ _ g₂ _ h
    funext j
    have hj : j ∈ Finset.univ.filter (fun j : Fin q => g₁ j = false) ↔
        j ∈ Finset.univ.filter (fun j : Fin q => g₂ j = false) := by rw [h]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    cases hg1 : g₁ j <;> cases hg2 : g₂ j <;> simp_all
  · intro s _
    refine ⟨fun j => !(decide (j ∈ s)), Finset.mem_univ _, ?_⟩
    ext j; simp
  · intro g _
    congr 1
    have hsplit : (Finset.univ.filter (fun j : Fin q => g j = false)).card +
        (Finset.univ.filter (fun j : Fin q => g j = true)).card = q := by
      have hunion : Finset.univ.filter (fun j : Fin q => g j = false) ∪
          Finset.univ.filter (fun j : Fin q => g j = true) = Finset.univ := by
        ext j; cases g j <;> simp
      have hdisj : Disjoint (Finset.univ.filter (fun j : Fin q => g j = false))
          (Finset.univ.filter (fun j : Fin q => g j = true)) := by
        rw [Finset.disjoint_left]
        intro j h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        rw [h1] at h2; cases h2
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega

private lemma am_gm_nat {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    s.card ^ s.card * ∏ i ∈ s, f i ≤ (∑ i ∈ s, f i) ^ s.card := by
  by_cases hs : s.Nonempty
  · have hpos : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
    have hle : (∏ i ∈ s, (f i : ℝ) ^ ((s.card : ℝ)⁻¹)) ≤
        ∑ i ∈ s, (s.card : ℝ)⁻¹ * (f i : ℝ) := by
      apply Real.geom_mean_le_arith_mean_weighted s (fun _ => (s.card : ℝ)⁻¹) (fun i => (f i : ℝ))
      · intro _ _; positivity
      · simp [Finset.sum_const, nsmul_eq_mul, hpos.ne']
      · intro _ _; positivity
    have hprod_gen : ∀ (r : ℝ) (t : Finset ι), (∏ i ∈ t, (f i : ℝ) ^ r) =
        (∏ i ∈ t, (f i : ℝ)) ^ r := by
      intro r t
      induction t using Finset.induction with
      | empty => simp
      | @insert a t ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, Real.mul_rpow (by positivity) (by positivity), ih]
    have hprod := hprod_gen ((s.card : ℝ)⁻¹) s
    rw [hprod, ← Finset.mul_sum] at hle
    have hpow := pow_le_pow_left₀ (by positivity) hle s.card
    rw [← Real.rpow_natCast ((∏ i ∈ s, (f i : ℝ)) ^ ((s.card : ℝ)⁻¹)) s.card,
        ← Real.rpow_mul (by positivity), inv_mul_cancel₀ hpos.ne', Real.rpow_one,
        mul_pow, inv_pow] at hpow
    have hpow2 : ((s.card : ℝ) ^ s.card) * (∏ i ∈ s, (f i : ℝ)) ≤
        (∑ i ∈ s, (f i : ℝ)) ^ s.card := by
      have hsc : (0 : ℝ) < (s.card : ℝ) ^ s.card := pow_pos hpos _
      rw [mul_comm]
      have := mul_le_mul_of_nonneg_right hpow hsc.le
      calc (∏ i ∈ s, (f i : ℝ)) * (s.card : ℝ) ^ s.card
          ≤ (((s.card : ℝ) ^ s.card)⁻¹ * (∑ i ∈ s, (f i : ℝ)) ^ s.card) * (s.card : ℝ) ^ s.card := by
            simpa [inv_pow] using this
        _ = (∑ i ∈ s, (f i : ℝ)) ^ s.card := by
            rw [mul_comm (((s.card : ℝ) ^ s.card)⁻¹), mul_assoc, inv_mul_cancel₀ hsc.ne', mul_one]
    exact_mod_cast hpow2
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp

private lemma pow_one_add_le_four {K : ℕ} (hK : 0 < K) :
    (K + 1) ^ K ≤ 4 * K ^ K := by
  have hKr : (0 : ℚ) < K := Nat.cast_pos.mpr hK
  have hbin : ((K + 1 : ℚ) / K) ^ K =
      ∑ j ∈ Finset.range (K + 1), (Nat.choose K j : ℚ) / (K : ℚ) ^ j := by
    have : ((K + 1 : ℚ) / K) = 1 / (K : ℚ) + 1 := by field_simp; ring
    rw [this, add_pow]
    apply Finset.sum_congr rfl
    intro j _
    simp [div_eq_mul_inv, inv_pow, mul_comm]
  have hfac : ∀ m : ℕ, 2 ^ (m - 1) ≤ Nat.factorial m := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      cases k with
      | zero => simp
      | succ l =>
        rw [Nat.factorial_succ]
        calc 2 ^ (l + 1) = 2 * 2 ^ l := by ring
          _ ≤ (l + 2) * Nat.factorial (l + 1) := Nat.mul_le_mul (by omega) ih
  have hterm : ∀ j ∈ Finset.range (K + 1),
      (Nat.choose K j : ℚ) / (K : ℚ) ^ j ≤ if j = 0 then 1 else (1 / 2 : ℚ) ^ (j - 1) := by
    intro j _
    by_cases hj : j = 0
    · subst hj; simp
    · simp only [hj, ↓reduceIte]
      have h1 : Nat.choose K j * Nat.factorial j ≤ K ^ j := by
        rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
        exact Nat.descFactorial_le_pow K j
      have h2 : Nat.choose K j * 2 ^ (j - 1) ≤ K ^ j :=
        (Nat.mul_le_mul_left (Nat.choose K j) (hfac j)).trans h1
      have h3 : (Nat.choose K j : ℚ) * 2 ^ (j - 1) ≤ (K : ℚ) ^ j := by
        exact_mod_cast h2
      rw [div_le_iff₀ (pow_pos hKr j), one_div, inv_pow,
          mul_comm ((2 ^ (j - 1) : ℚ)⁻¹), ← div_eq_mul_inv,
          le_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) (j - 1))]
      simpa [mul_comm] using h3
  have hsum : ((K + 1 : ℚ) / K) ^ K ≤
      1 + ∑ j ∈ Finset.range K, (1 / 2 : ℚ) ^ j := by
    calc ((K + 1 : ℚ) / K) ^ K
        = ∑ j ∈ Finset.range (K + 1), (Nat.choose K j : ℚ) / (K : ℚ) ^ j := hbin
      _ ≤ ∑ j ∈ Finset.range (K + 1), (if j = 0 then (1 : ℚ) else (1 / 2 : ℚ) ^ (j - 1)) :=
          Finset.sum_le_sum hterm
      _ = 1 + ∑ j ∈ Finset.range K, (1 / 2 : ℚ) ^ j := by
          rw [Finset.sum_range_succ']
          simp [add_comm]
  have hg : ∀ n : ℕ, (∑ m ∈ Finset.range n, (1 / 2 : ℚ) ^ m) = 2 - 2 * (1 / 2 : ℚ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hgeom : ∑ j ∈ Finset.range K, (1 / 2 : ℚ) ^ j ≤ 2 := by
    rw [hg K]
    have : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ K := by positivity
    linarith
  have hq : ((K + 1 : ℚ) / K) ^ K ≤ 4 := by linarith
  rw [div_pow, div_le_iff₀ (pow_pos hKr K)] at hq
  exact_mod_cast hq

end PEqualNP.Outside.L_lib_674

theorem PEqualNP.Outside.L_lib_674 : (∀ (b r : ℕ), 0 < r → r ≤ b →
  let W := Bool × (Fin b → Bool)
  let P := Fin b → Option Bool
  let fam := (Finset.univ : Finset P).filter (fun v =>
    (Finset.univ.filter (fun i : Fin b => (v i).isSome = true)).card = r)
  let star := fun (p : P) (x : W) => decide
    (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i))
  let N := Nat.choose b r
  let K := 2 ^ r
  ∀ (M q : ℕ), 0 < M →
    ∀ (ask : Fin M → Fin q → W) (report : Fin M → (Fin q → Bool) → Option (W → Bool)),
      let H := ∑ p ∈ fam, (Finset.univ.filter (fun seed : Fin M =>
        report seed (fun j => star p (ask seed j)) = some (star p))).card
      (∀ v : ℕ, 0 < v →
        H ^ H * v ^ (q * H) ≤
          M ^ H * (v + 1) ^ (q * H) * v ^ (M * q * N)) ∧
      (3 * M * (K * N) ≤ 4 * H →
        (2 ^ (r - 1) * N) ^ (3 * K) ≤ 2 ^ ((4 * r + 6) * q))) := by
  intro b r hr hrb W P fam star N K M q hM ask report H
  let S : Finset (P × Fin M) := (fam ×ˢ Finset.univ).filter (fun x =>
    report x.2 (fun j => star x.1 (ask x.2 j)) = some (star x.1))
  have hS_card : S.card = H := by
    simp only [S, H, Finset.card_filter]
    rw [Finset.sum_product]
  let diff : P → Fin M → ℕ := fun p seed =>
    (Finset.univ.filter (fun j : Fin q => star p (ask seed j) ≠ (ask seed j).1)).card
  let E : ℕ := ∑ x ∈ S, diff x.1 x.2
  have hE_le : E ≤ M * q * N := by
    calc E = ∑ x ∈ S, diff x.1 x.2 := rfl
      _ ≤ ∑ x ∈ fam ×ˢ (Finset.univ : Finset (Fin M)), diff x.1 x.2 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ p ∈ fam, ∑ seed : Fin M, diff p seed := Finset.sum_product _ _ _
      _ = ∑ seed : Fin M, ∑ p ∈ fam, diff p seed := Finset.sum_comm
      _ = ∑ seed : Fin M, ∑ j : Fin q,
            ((fam.filter (fun p => star p (ask seed j) ≠ (ask seed j).1)).card) := by
          apply Finset.sum_congr rfl
          intro seed _
          simp only [diff, Finset.card_filter]
          rw [Finset.sum_comm]
      _ ≤ ∑ seed : Fin M, ∑ j : Fin q, N := by
          apply Finset.sum_le_sum; intro seed _
          apply Finset.sum_le_sum; intro j _
          have hsub : fam.filter (fun p => star p (ask seed j) ≠ (ask seed j).1) =
              (Finset.univ : Finset P).filter (fun p =>
                (Finset.univ.filter (fun i : Fin b => (p i).isSome = true)).card = r ∧
                decide ((ask seed j).1 = true ∨
                  ∀ i : Fin b, p i = none ∨ p i = some ((ask seed j).2 i)) ≠ (ask seed j).1) := by
            ext p; simp [fam, star]
          rw [hsub]
          exact PEqualNP.Outside.L_lib_674.count_star_diff_le (ask seed j)
      _ = M * q * N := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_assoc]
  have hE_le_qH : E ≤ q * H := by
    calc E = ∑ x ∈ S, diff x.1 x.2 := rfl
      _ ≤ ∑ _x ∈ S, q := by
          apply Finset.sum_le_sum; intro x _
          simpa [Finset.card_univ, Fintype.card_fin] using
            Finset.card_filter_le (Finset.univ : Finset (Fin q)) _
      _ = q * H := by simp [Finset.sum_const, hS_card, mul_comm]
  have hpart1 : ∀ v : ℕ, 0 < v →
      H ^ H * v ^ (q * H) ≤ M ^ H * (v + 1) ^ (q * H) * v ^ (M * q * N) := by
    intro v hv
    have hsum_le : ∑ x ∈ S, v ^ (q - diff x.1 x.2) ≤ M * (v + 1) ^ q := by
      have hpart : ∑ x ∈ S, v ^ (q - diff x.1 x.2) =
          ∑ seed : Fin M, ∑ x ∈ S.filter (fun x => x.2 = seed), v ^ (q - diff x.1 x.2) := by
        rw [← Finset.sum_fiberwise S (fun x => x.2) (fun x => v ^ (q - diff x.1 x.2))]
      rw [hpart]
      calc ∑ seed : Fin M, ∑ x ∈ S.filter (fun x => x.2 = seed), v ^ (q - diff x.1 x.2)
          ≤ ∑ _seed : Fin M, (v + 1) ^ q := by
            apply Finset.sum_le_sum; intro seed _
            let f : (P × Fin M) → (Fin q → Bool) :=
              fun x j => xor (star x.1 (ask seed j)) (ask seed j).1
            have hinj : ∀ x₁ ∈ S.filter (fun x => x.2 = seed),
                ∀ x₂ ∈ S.filter (fun x => x.2 = seed), f x₁ = f x₂ → x₁ = x₂ := by
              intro x₁ hx₁ x₂ hx₂ hf
              simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
                and_true] at hx₁ hx₂
              have hs1 : x₁.2 = seed := hx₁.2
              have hs2 : x₂.2 = seed := hx₂.2
              have hans : (fun j => star x₁.1 (ask seed j)) =
                  (fun j => star x₂.1 (ask seed j)) := by
                funext j
                have hj := congr_fun hf j
                simp only [f] at hj
                cases h1 : star x₁.1 (ask seed j) <;> cases h2 : star x₂.1 (ask seed j) <;>
                  cases ha : (ask seed j).1 <;> simp_all
              have hrep1 := hx₁.1.2
              have hrep2 := hx₂.1.2
              rw [hs1] at hrep1
              rw [hs2, ← hans] at hrep2
              have hst : star x₁.1 = star x₂.1 := Option.some.inj (hrep1.symm.trans hrep2)
              have hp : x₁.1 = x₂.1 := PEqualNP.Outside.L_lib_674.star_inj hst
              exact Prod.ext hp (hs1.trans hs2.symm)
            have hle_sum : ∑ x ∈ S.filter (fun x => x.2 = seed), v ^ (q - diff x.1 x.2) ≤
                ∑ g : Fin q → Bool, v ^ (q - (Finset.univ.filter (fun j : Fin q => g j = true)).card) := by
              apply Finset.sum_le_sum_of_injOn f
              · exact hinj
              · simp
              · intro x hx
                simp only [Finset.mem_filter] at hx
                have hcard_eq : (Finset.univ.filter (fun j : Fin q => f x j = true)).card =
                    diff x.1 x.2 := by
                  rw [hx.2]
                  apply congrArg Finset.card
                  ext j
                  simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
                  cases star x.1 (ask seed j) <;> cases (ask seed j).1 <;> simp
                rw [hcard_eq]
              · intro _ _ _; exact Nat.zero_le _
            exact hle_sum.trans_eq PEqualNP.Outside.L_lib_674.sum_bool_pow
        _ = M * (v + 1) ^ q := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have ham := PEqualNP.Outside.L_lib_674.am_gm_nat S (fun x => v ^ (q - diff x.1 x.2))
    rw [hS_card] at ham
    have hprod_eq : ∏ x ∈ S, v ^ (q - diff x.1 x.2) = v ^ (q * H - E) := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      have hsub : ∀ x ∈ S, diff x.1 x.2 ≤ q := fun x _ => by
        simpa [Finset.card_univ, Fintype.card_fin] using
          Finset.card_filter_le (Finset.univ : Finset (Fin q)) _
      have : ∑ x ∈ S, (q - diff x.1 x.2) + ∑ x ∈ S, diff x.1 x.2 = ∑ _x ∈ S, q := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x hx
        exact Nat.sub_add_cancel (hsub x hx)
      simp only [Finset.sum_const, nsmul_eq_mul, hS_card] at this
      symm
      apply Nat.sub_eq_of_eq_add
      calc q * H = H * q := mul_comm _ _
        _ = ∑ x ∈ S, (q - diff x.1 x.2) + ∑ x ∈ S, diff x.1 x.2 := this.symm
    rw [hprod_eq] at ham
    have hpow_sum : (∑ x ∈ S, v ^ (q - diff x.1 x.2)) ^ H ≤ (M * (v + 1) ^ q) ^ H :=
      Nat.pow_le_pow_left hsum_le H
    have hmain : H ^ H * v ^ (q * H - E) ≤ M ^ H * (v + 1) ^ (q * H) := by
      calc H ^ H * v ^ (q * H - E) ≤ (∑ x ∈ S, v ^ (q - diff x.1 x.2)) ^ H := ham
        _ ≤ (M * (v + 1) ^ q) ^ H := hpow_sum
        _ = M ^ H * (v + 1) ^ (q * H) := by rw [mul_pow, ← pow_mul]
    have hv_pow : v ^ E ≤ v ^ (M * q * N) := Nat.pow_le_pow_right hv hE_le
    calc H ^ H * v ^ (q * H)
        = H ^ H * v ^ (q * H - E + E) := by rw [Nat.sub_add_cancel hE_le_qH]
      _ = H ^ H * v ^ (q * H - E) * v ^ E := by rw [pow_add, mul_assoc]
      _ ≤ (M ^ H * (v + 1) ^ (q * H)) * v ^ E := Nat.mul_le_mul_right _ hmain
      _ ≤ M ^ H * (v + 1) ^ (q * H) * v ^ (M * q * N) := Nat.mul_le_mul_left _ hv_pow
  refine ⟨hpart1, ?_⟩
  intro h3
  have hKpos : 0 < K := by positivity
  have hNpos : 0 < N := Nat.choose_pos hrb
  have hHpos : 0 < H := by
    have : 0 < 3 * M * (K * N) := by positivity
    omega
  have h1 := hpart1 K hKpos
  have hA_le : 2 ^ (r - 1) * N * M ≤ H := by
    have hpow : 4 * 2 ^ (r - 1) ≤ 3 * K := by
      have hk : K = 2 * 2 ^ (r - 1) := by
        dsimp [K]
        conv_lhs => rw [show r = (r - 1) + 1 by omega, pow_succ']
      omega
    have hmul : 4 * (2 ^ (r - 1) * N * M) ≤ 3 * M * (K * N) := by
      calc 4 * (2 ^ (r - 1) * N * M) = M * N * (4 * 2 ^ (r - 1)) := by ring
        _ ≤ M * N * (3 * K) := Nat.mul_le_mul_left _ hpow
        _ = 3 * M * (K * N) := by ring
    omega
  have hAH : (2 ^ (r - 1) * N) ^ H * M ^ H ≤ H ^ H := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left hA_le H
  have hstep1 : (2 ^ (r - 1) * N) ^ H * K ^ (q * H) ≤ (K + 1) ^ (q * H) * K ^ (M * q * N) := by
    have hMpos : 0 < M ^ H := pow_pos hM H
    have hmul : M ^ H * ((2 ^ (r - 1) * N) ^ H * K ^ (q * H)) ≤
        M ^ H * ((K + 1) ^ (q * H) * K ^ (M * q * N)) := by
      calc M ^ H * ((2 ^ (r - 1) * N) ^ H * K ^ (q * H))
          = ((2 ^ (r - 1) * N) ^ H * M ^ H) * K ^ (q * H) := by ring
        _ ≤ H ^ H * K ^ (q * H) := Nat.mul_le_mul_right _ hAH
        _ ≤ M ^ H * (K + 1) ^ (q * H) * K ^ (M * q * N) := h1
        _ = M ^ H * ((K + 1) ^ (q * H) * K ^ (M * q * N)) := by ring
    exact Nat.le_of_mul_le_mul_left hmul hMpos
  have hstep2 : ((2 ^ (r - 1) * N) ^ H * K ^ (q * H)) ^ (3 * K) ≤
      ((K + 1) ^ (q * H) * K ^ (M * q * N)) ^ (3 * K) :=
    Nat.pow_le_pow_left hstep1 (3 * K)
  have hK4 : (K + 1) ^ K ≤ 4 * K ^ K := PEqualNP.Outside.L_lib_674.pow_one_add_le_four hKpos
  have hK4_pow : (K + 1) ^ (q * H * (3 * K)) ≤ (4 * K ^ K) ^ (3 * q * H) := by
    rw [show q * H * (3 * K) = K * (3 * q * H) by ring, pow_mul]
    exact Nat.pow_le_pow_left hK4 (3 * q * H)
  have hKM : K ^ (M * q * N * (3 * K)) ≤ K ^ (4 * q * H) := by
    apply Nat.pow_le_pow_right hKpos
    calc M * q * N * (3 * K) = q * (3 * M * (K * N)) := by ring
      _ ≤ q * (4 * H) := Nat.mul_le_mul_left q h3
      _ = 4 * q * H := by ring
  have hstep3 : (2 ^ (r - 1) * N) ^ (3 * K * H) * K ^ (3 * K * q * H) ≤
      (4 ^ (3 * q) * K ^ (4 * q)) ^ H * K ^ (3 * K * q * H) := by
    calc (2 ^ (r - 1) * N) ^ (3 * K * H) * K ^ (3 * K * q * H)
        = ((2 ^ (r - 1) * N) ^ H * K ^ (q * H)) ^ (3 * K) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          congr 2 <;> ring
      _ ≤ ((K + 1) ^ (q * H) * K ^ (M * q * N)) ^ (3 * K) := hstep2
      _ = (K + 1) ^ (q * H * (3 * K)) * K ^ (M * q * N * (3 * K)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ (4 * K ^ K) ^ (3 * q * H) * K ^ (4 * q * H) := Nat.mul_le_mul hK4_pow hKM
      _ = (4 ^ (3 * q) * K ^ (4 * q)) ^ H * K ^ (3 * K * q * H) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [mul_pow, ← pow_mul, ← pow_mul]
          ring
  have hstep4 : (2 ^ (r - 1) * N) ^ (3 * K * H) ≤ (4 ^ (3 * q) * K ^ (4 * q)) ^ H :=
    Nat.le_of_mul_le_mul_right hstep3 (pow_pos hKpos _)
  rw [pow_mul] at hstep4
  have hstep5 : (2 ^ (r - 1) * N) ^ (3 * K) ≤ 4 ^ (3 * q) * K ^ (4 * q) :=
    (Nat.pow_le_pow_iff_left hHpos.ne').mp hstep4
  calc (2 ^ (r - 1) * N) ^ (3 * K)
      ≤ 4 ^ (3 * q) * K ^ (4 * q) := hstep5
    _ = (2 ^ 2) ^ (3 * q) * (2 ^ r) ^ (4 * q) := by rfl
    _ = 2 ^ ((4 * r + 6) * q) := by
        rw [← pow_mul, ← pow_mul, ← pow_add]
        congr 1; ring
