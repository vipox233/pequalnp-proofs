import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1247_aux

-- =========================================================================
-- Part 1: Hadamard sign matrix orthogonality and Parseval identity
-- =========================================================================

private def bitVal {m : ℕ} (f g : Fin m → Bool) : ℝ :=
  if ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
  then (1 : ℝ) else 0

private def signH {m : ℕ} (f g : Fin m → Bool) : ℝ :=
  1 - 2 * bitVal f g

private lemma signH_eq_prod {m : ℕ} (f g : Fin m → Bool) :
    signH f g = ∏ i : Fin m, if (f i && g i) = true then (-1 : ℝ) else 1 := by
  unfold signH bitVal
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  set c := ((Finset.univ : Finset (Fin m)).filter (fun i => (f i && g i) = true)).card
  have hmod := Nat.mod_two_eq_zero_or_one c
  rcases hmod with h0 | h1
  · have hev : Even c := Nat.even_iff.mpr h0
    rw [if_neg (by omega), hev.neg_one_pow]
    norm_num
  · have hodd : Odd c := Nat.odd_iff.mpr h1
    rw [if_pos h1, hodd.neg_one_pow]
    norm_num

private lemma signH_sq {m : ℕ} (f g : Fin m → Bool) : signH f g * signH f g = 1 := by
  unfold signH bitVal
  split_ifs <;> norm_num

private lemma hadamard_row_orth {m : ℕ} (f1 f2 : Fin m → Bool) :
    (∑ g : Fin m → Bool, signH f1 g * signH f2 g) = if f1 = f2 then (2 ^ m : ℝ) else 0 := by
  by_cases hEq : f1 = f2
  · subst hEq
    rw [if_pos rfl]
    have h1 : ∀ g : Fin m → Bool, signH f1 g * signH f1 g = 1 := fun g => signH_sq f1 g
    rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ]
    simp [Fintype.card_bool, Fintype.card_fin]
  · rw [if_neg hEq]
    have hex : ∃ i0 : Fin m, f1 i0 ≠ f2 i0 := by
      by_contra hall
      push_neg at hall
      exact hEq (funext hall)
    rcases hex with ⟨i0, hi0⟩
    let flip : (Fin m → Bool) → (Fin m → Bool) := fun g => Function.update g i0 (!g i0)
    have hflip_inv : ∀ g, flip (flip g) = g := by
      intro g; funext i
      by_cases hi : i = i0
      · subst hi; simp [flip]
      · simp [flip, hi]
    have hflip_neg : ∀ g : Fin m → Bool, signH f1 (flip g) * signH f2 (flip g) = -(signH f1 g * signH f2 g) := by
      intro g
      rw [signH_eq_prod, signH_eq_prod, signH_eq_prod, signH_eq_prod]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
          ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
      have hrest1 : (∏ i ∈ Finset.univ.erase i0, if (f1 i && flip g i) = true then (-1 : ℝ) else 1) =
          ∏ i ∈ Finset.univ.erase i0, if (f1 i && g i) = true then (-1 : ℝ) else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
        simp [flip, hne]
      have hrest2 : (∏ i ∈ Finset.univ.erase i0, if (f2 i && flip g i) = true then (-1 : ℝ) else 1) =
          ∏ i ∈ Finset.univ.erase i0, if (f2 i && g i) = true then (-1 : ℝ) else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
        simp [flip, hne]
      rw [hrest1, hrest2]
      have hfront : (if (f1 i0 && flip g i0) = true then (-1 : ℝ) else 1) *
          (if (f2 i0 && flip g i0) = true then (-1 : ℝ) else 1) =
          -((if (f1 i0 && g i0) = true then (-1 : ℝ) else 1) *
            (if (f2 i0 && g i0) = true then (-1 : ℝ) else 1)) := by
        simp only [flip, Function.update_self]
        cases hf1 : f1 i0 <;> cases hf2 : f2 i0 <;> cases hg : g i0
        all_goals try (rw [hf1, hf2] at hi0; exact absurd rfl hi0)
        all_goals norm_num
      calc ((if (f1 i0 && flip g i0) = true then (-1 : ℝ) else 1) *
              ∏ i ∈ Finset.univ.erase i0, if (f1 i && g i) = true then (-1 : ℝ) else 1) *
            ((if (f2 i0 && flip g i0) = true then (-1 : ℝ) else 1) *
              ∏ i ∈ Finset.univ.erase i0, if (f2 i && g i) = true then (-1 : ℝ) else 1)
          = ((if (f1 i0 && flip g i0) = true then (-1 : ℝ) else 1) *
              (if (f2 i0 && flip g i0) = true then (-1 : ℝ) else 1)) *
            ((∏ i ∈ Finset.univ.erase i0, if (f1 i && g i) = true then (-1 : ℝ) else 1) *
              (∏ i ∈ Finset.univ.erase i0, if (f2 i && g i) = true then (-1 : ℝ) else 1)) := by ring
        _ = -((if (f1 i0 && g i0) = true then (-1 : ℝ) else 1) *
              (if (f2 i0 && g i0) = true then (-1 : ℝ) else 1)) *
            ((∏ i ∈ Finset.univ.erase i0, if (f1 i && g i) = true then (-1 : ℝ) else 1) *
              (∏ i ∈ Finset.univ.erase i0, if (f2 i && g i) = true then (-1 : ℝ) else 1)) := by rw [hfront]
        _ = _ := by ring
    set S := ∑ g : Fin m → Bool, signH f1 g * signH f2 g
    have hbij : S = ∑ g : Fin m → Bool, signH f1 (flip g) * signH f2 (flip g) := by
      refine (Finset.sum_bij' (fun g _ => flip g) (fun g _ => flip g)
        (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
        (fun g _ => hflip_inv g) (fun g _ => hflip_inv g) (fun _ _ => rfl)).symm
    have hneg : S = -S := by
      calc S = ∑ g : Fin m → Bool, signH f1 (flip g) * signH f2 (flip g) := hbij
        _ = ∑ g : Fin m → Bool, -(signH f1 g * signH f2 g) :=
              Finset.sum_congr rfl (fun g _ => hflip_neg g)
        _ = -S := by rw [Finset.sum_neg_distrib]
    linarith

private lemma hadamard_parseval {m : ℕ} (u : (Fin m → Bool) → ℝ) :
    (∑ g : Fin m → Bool, (∑ f : Fin m → Bool, u f * signH f g) ^ 2) =
      (2 ^ m : ℝ) * ∑ f : Fin m → Bool, (u f) ^ 2 := by
  have h1 : ∀ g : Fin m → Bool,
      (∑ f : Fin m → Bool, u f * signH f g) ^ 2 =
        ∑ f1 : Fin m → Bool, ∑ f2 : Fin m → Bool, u f1 * u f2 * (signH f1 g * signH f2 g) := by
    intro g
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro f1 _
    apply Finset.sum_congr rfl; intro f2 _
    ring
  rw [Finset.sum_congr rfl (fun g _ => h1 g)]
  rw [Finset.sum_comm]
  have h2 : ∀ f1 : Fin m → Bool,
      (∑ g : Fin m → Bool, ∑ f2 : Fin m → Bool, u f1 * u f2 * (signH f1 g * signH f2 g)) =
        (2 ^ m : ℝ) * (u f1) ^ 2 := by
    intro f1
    rw [Finset.sum_comm]
    have h3 : ∀ f2 : Fin m → Bool,
        (∑ g : Fin m → Bool, u f1 * u f2 * (signH f1 g * signH f2 g)) =
          if f1 = f2 then (2 ^ m : ℝ) * (u f1) ^ 2 else 0 := by
      intro f2
      rw [← Finset.mul_sum, hadamard_row_orth]
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl (fun f2 _ => h3 f2)]
    simp [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl (fun f1 _ => h2 f1), ← Finset.mul_sum]

-- =========================================================================
-- Part 2: Stars-and-bars count of monomials of degree <= d in q variables
-- =========================================================================

private def expSet (q d : ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset (fun _ : Fin q => Finset.range (d + 1))).filter (fun e => ∑ i, e i ≤ d)

private lemma mem_expSet {q d : ℕ} {e : Fin q → ℕ} :
    e ∈ expSet q d ↔ ∑ i, e i ≤ d := by
  simp only [expSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
  intro hsum i
  have hle : e i ≤ ∑ j : Fin q, e j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

private lemma expSet_card : ∀ q d : ℕ, (expSet q d).card = Nat.choose (q + d) d := by
  intro q
  induction q with
  | zero =>
    intro d
    have hEq : expSet 0 d = {Fin.elim0} := by
      ext e
      simp only [mem_expSet, Finset.mem_singleton]
      exact ⟨fun _ => funext (fun i => i.elim0), fun _ => by simp⟩
    rw [hEq, Finset.card_singleton, zero_add, Nat.choose_self]
  | succ q ihq =>
    intro d
    induction d with
    | zero =>
      have hEq : expSet (q + 1) 0 = {fun _ => 0} := by
        ext e
        simp only [mem_expSet, Nat.le_zero, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
          Finset.mem_singleton]
        exact ⟨fun h => funext h, fun h i => by rw [h]⟩
      rw [hEq, Finset.card_singleton, add_zero, Nat.choose_zero_right]
    | succ d ihd =>
      let S := expSet (q + 1) (d + 1)
      let S0 := S.filter (fun e => e (Fin.last q) = 0)
      let S1 := S.filter (fun e => e (Fin.last q) ≠ 0)
      have hdisj : Disjoint S0 S1 := by
        rw [Finset.disjoint_left]
        intro e h0 h1
        exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h0).2
      have hunion : S0 ∪ S1 = S := by
        ext e; simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
        by_cases h : e (Fin.last q) = 0 <;> simp [h]
      have hcard0 : S0.card = (expSet q (d + 1)).card := by
        let drop : (Fin (q + 1) → ℕ) → (Fin q → ℕ) := fun e i => e i.castSucc
        let lift : (Fin q → ℕ) → (Fin (q + 1) → ℕ) := fun e => Fin.snoc e 0
        refine Finset.card_bij' (fun e _ => drop e) (fun e _ => lift e) ?_ ?_ ?_ ?_
        · intro e he
          simp only [S0, S, Finset.mem_filter, mem_expSet] at he
          rw [mem_expSet]
          have hs := he.1
          rw [Fin.sum_univ_castSucc, he.2, add_zero] at hs
          exact hs
        · intro e he
          rw [mem_expSet] at he
          simp only [S0, S, Finset.mem_filter, mem_expSet]
          refine ⟨?_, by simp [lift]⟩
          rw [Fin.sum_univ_castSucc]
          simpa [lift] using he
        · intro e he
          have h0 : e (Fin.last q) = 0 := (Finset.mem_filter.mp he).2
          funext i
          refine Fin.lastCases ?_ ?_ i
          · simp [lift, h0]
          · intro j; simp [lift, drop]
        · intro e _
          funext i; simp [drop, lift]
      have hcard1 : S1.card = (expSet (q + 1) d).card := by
        let dec : (Fin (q + 1) → ℕ) → (Fin (q + 1) → ℕ) :=
          fun e => Function.update e (Fin.last q) (e (Fin.last q) - 1)
        let inc : (Fin (q + 1) → ℕ) → (Fin (q + 1) → ℕ) :=
          fun e => Function.update e (Fin.last q) (e (Fin.last q) + 1)
        refine Finset.card_bij' (fun e _ => dec e) (fun e _ => inc e) ?_ ?_ ?_ ?_
        · intro e he
          simp only [S1, S, Finset.mem_filter, mem_expSet] at he
          rw [mem_expSet, Fin.sum_univ_castSucc]
          have hs := he.1
          rw [Fin.sum_univ_castSucc] at hs
          have hrest : (∑ i : Fin q, dec e i.castSucc) = ∑ i : Fin q, e i.castSucc := by
            apply Finset.sum_congr rfl; intro i _
            simp [dec, Fin.castSucc_ne_last]
          rw [hrest]
          simp only [dec, Function.update_self]
          omega
        · intro e he
          rw [mem_expSet] at he
          simp only [S1, S, Finset.mem_filter, mem_expSet]
          refine ⟨?_, by simp [inc]⟩
          rw [Fin.sum_univ_castSucc] at he ⊢
          have hrest : (∑ i : Fin q, inc e i.castSucc) = ∑ i : Fin q, e i.castSucc := by
            apply Finset.sum_congr rfl; intro i _
            simp [inc, Fin.castSucc_ne_last]
          rw [hrest]
          simp only [inc, Function.update_self]
          omega
        · intro e he
          have hne : e (Fin.last q) ≠ 0 := (Finset.mem_filter.mp he).2
          funext i
          by_cases hi : i = Fin.last q
          · subst hi; simp only [inc, dec, Function.update_self]; omega
          · simp [inc, dec, hi]
        · intro e _
          funext i
          by_cases hi : i = Fin.last q
          · subst hi; simp [dec, inc]
          · simp [dec, inc, hi]
      have htot : S.card = S0.card + S1.card := by rw [← hunion, Finset.card_union_of_disjoint hdisj]
      change S.card = Nat.choose ((q + 1) + (d + 1)) (d + 1)
      rw [htot, hcard0, hcard1, ihq (d + 1), ihd]
      have h1 : q + (d + 1) = q + d + 1 := by omega
      have h2 : (q + 1) + d = q + d + 1 := by omega
      have h3 : (q + 1) + (d + 1) = (q + d + 1) + 1 := by omega
      rw [h1, h2, h3]
      rw [add_comm ((q + d + 1).choose (d + 1))]
      exact (Nat.choose_succ_succ (q + d + 1) d).symm

-- =========================================================================
-- Part 3: Polynomial column vectors lie in the monomial span
-- =========================================================================

private def monom {m q : ℕ} (a : (Fin m → Bool) → Fin q → ℝ) (e : Fin q → ℕ) : (Fin m → Bool) → ℝ :=
  fun f => ∏ i : Fin q, (a f i) ^ (e i)

private lemma monom_mul_coord {m q : ℕ} (a : (Fin m → Bool) → Fin q → ℝ)
    (e : Fin q → ℕ) (i0 : Fin q) :
    (fun f => a f i0 * monom a e f) = monom a (Function.update e i0 (e i0 + 1)) := by
  funext f
  unfold monom
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i0)]
  have hrest : (∏ i ∈ Finset.univ.erase i0, a f i ^ Function.update e i0 (e i0 + 1) i) =
      ∏ i ∈ Finset.univ.erase i0, a f i ^ e i := by
    apply Finset.prod_congr rfl; intro i hi
    have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    simp [hne]
  rw [hrest, Function.update_self, pow_succ]
  ring

private lemma pow_lin_mem_span {m q : ℕ} (a : (Fin m → Bool) → Fin q → ℝ) (bvec : Fin q → ℝ) :
    ∀ r : ℕ, (fun f => (∑ i : Fin q, a f i * bvec i) ^ r) ∈
      Submodule.span ℝ ((expSet q r).image (monom a) : Set ((Fin m → Bool) → ℝ)) := by
  intro r
  induction r with
  | zero =>
    have h0 : (fun _ : Fin m → Bool => (1 : ℝ)) = monom a (fun _ => 0) := by
      funext f; simp [monom]
    have hmem : monom a (fun _ => 0) ∈ ((expSet q 0).image (monom a) : Set ((Fin m → Bool) → ℝ)) := by
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_expSet]
      exact ⟨fun _ => 0, by simp, rfl⟩
    simpa [h0] using Submodule.subset_span hmem
  | succ r ih =>
    have hexp : (fun f => (∑ i : Fin q, a f i * bvec i) ^ (r + 1)) =
        ∑ i : Fin q, bvec i • (fun f => a f i * (∑ j : Fin q, a f j * bvec j) ^ r) := by
      funext f
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pow_succ, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [hexp]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    let mulLin : ((Fin m → Bool) → ℝ) →ₗ[ℝ] ((Fin m → Bool) → ℝ) :=
      { toFun := fun u f => a f i * u f
        map_add' := fun u v => by funext f; simp only [Pi.add_apply]; ring
        map_smul' := fun c u => by funext f; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    change mulLin (fun f => (∑ j : Fin q, a f j * bvec j) ^ r) ∈ _
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
      (fun c _ _ hx => by rw [map_smul]; exact Submodule.smul_mem _ c hx) ih
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_expSet] at hv
    rcases hv with ⟨e, he, rfl⟩
    have hupd : mulLin (monom a e) = monom a (Function.update e i (e i + 1)) := monom_mul_coord a e i
    rw [hupd]
    apply Submodule.subset_span
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_expSet]
    refine ⟨Function.update e i (e i + 1), ?_, rfl⟩
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)] at he
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hrest : (∑ j ∈ Finset.univ.erase i, Function.update e i (e i + 1) j) =
        ∑ j ∈ Finset.univ.erase i, e j := by
      apply Finset.sum_congr rfl; intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    rw [hrest, Function.update_self]
    omega

private lemma centered_col_mem_span {m q d : ℕ}
    (a b : (Fin m → Bool) → Fin q → ℝ) (P : (Fin m → Bool) → Polynomial ℝ)
    (hdeg : ∀ g, (P g).natDegree ≤ d) (g : Fin m → Bool) :
    (fun f => 1 - 2 * (P g).eval (∑ i : Fin q, a f i * b g i)) ∈
      Submodule.span ℝ ((expSet q d).image (monom a) : Set ((Fin m → Bool) → ℝ)) := by
  let W := Submodule.span ℝ ((expSet q d).image (monom a) : Set ((Fin m → Bool) → ℝ))
  have hmono : ∀ r ≤ d,
      Submodule.span ℝ ((expSet q r).image (monom a) : Set ((Fin m → Bool) → ℝ)) ≤ W := by
    intro r hr
    apply Submodule.span_mono
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, mem_expSet] at hv ⊢
    rcases hv with ⟨e, he, rfl⟩
    exact ⟨e, le_trans he hr, rfl⟩
  have h1 : (fun _ : Fin m → Bool => (1 : ℝ)) ∈ W := by
    have := hmono 0 (Nat.zero_le d) (pow_lin_mem_span a (b g) 0)
    simpa using this
  have hpred : (fun f => (P g).eval (∑ i : Fin q, a f i * b g i)) ∈ W := by
    have heval : (fun f => (P g).eval (∑ i : Fin q, a f i * b g i)) =
        ∑ r ∈ Finset.range (d + 1), (P g).coeff r • (fun f => (∑ i : Fin q, a f i * b g i) ^ r) := by
      funext f
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg g))]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heval]
    apply Submodule.sum_mem
    intro r hr
    apply Submodule.smul_mem
    exact hmono r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) (pow_lin_mem_span a (b g) r)
  have hcomb : (fun f => 1 - 2 * (P g).eval (∑ i : Fin q, a f i * b g i)) =
      (fun _ => (1 : ℝ)) - (2 : ℝ) • (fun f => (P g).eval (∑ i : Fin q, a f i * b g i)) := by
    funext f; simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [hcomb]
  exact Submodule.sub_mem W h1 (Submodule.smul_mem W 2 hpred)

-- =========================================================================
-- Part 4: Elementary Gram-Schmidt and Pythagoras bound
-- =========================================================================

private def dotV {m : ℕ} (u v : (Fin m → Bool) → ℝ) : ℝ :=
  ∑ f : Fin m → Bool, u f * v f

private lemma dotV_comm {m : ℕ} (u v : (Fin m → Bool) → ℝ) : dotV u v = dotV v u := by
  unfold dotV; apply Finset.sum_congr rfl; intro f _; ring

private lemma dotV_add_left {m : ℕ} (u v w : (Fin m → Bool) → ℝ) :
    dotV (u + v) w = dotV u w + dotV v w := by
  unfold dotV; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro f _; simp [Pi.add_apply]; ring

private lemma dotV_sub_left {m : ℕ} (u v w : (Fin m → Bool) → ℝ) :
    dotV (u - v) w = dotV u w - dotV v w := by
  unfold dotV; rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro f _; simp [Pi.sub_apply]; ring

private lemma dotV_add_right {m : ℕ} (u v w : (Fin m → Bool) → ℝ) :
    dotV u (v + w) = dotV u v + dotV u w := by
  rw [dotV_comm, dotV_add_left, dotV_comm v u, dotV_comm w u]

private lemma dotV_sub_right {m : ℕ} (u v w : (Fin m → Bool) → ℝ) :
    dotV u (v - w) = dotV u v - dotV u w := by
  rw [dotV_comm, dotV_sub_left, dotV_comm v u, dotV_comm w u]

private lemma dotV_smul_left {m : ℕ} (c : ℝ) (u v : (Fin m → Bool) → ℝ) :
    dotV (c • u) v = c * dotV u v := by
  unfold dotV; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro f _; simp [Pi.smul_apply]; ring

private lemma dotV_sum_left {m : ℕ} {ι : Type*} (s : Finset ι)
    (u : ι → (Fin m → Bool) → ℝ) (v : (Fin m → Bool) → ℝ) :
    dotV (∑ i ∈ s, u i) v = ∑ i ∈ s, dotV (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dotV]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dotV_add_left, ih]

private lemma dotV_self_nonneg {m : ℕ} (u : (Fin m → Bool) → ℝ) : 0 ≤ dotV u u := by
  unfold dotV
  exact Finset.sum_nonneg (fun f _ => mul_self_nonneg (u f))

private lemma dotV_self_pos_of_ne_zero {m : ℕ} {u : (Fin m → Bool) → ℝ} (hu : u ≠ 0) :
    0 < dotV u u := by
  have hex : ∃ f : Fin m → Bool, u f ≠ 0 := by
    by_contra hall; push_neg at hall; exact hu (funext hall)
  rcases hex with ⟨f0, hf0⟩
  unfold dotV
  have hpos : 0 < u f0 * u f0 := mul_self_pos.mpr hf0
  have hle : u f0 * u f0 ≤ ∑ f : Fin m → Bool, u f * u f :=
    Finset.single_le_sum (fun f _ => mul_self_nonneg (u f)) (Finset.mem_univ f0)
  linarith

private lemma exists_orthonormal_span {m : ℕ} :
    ∀ S : Finset ((Fin m → Bool) → ℝ),
      ∃ (k : ℕ) (e : Fin k → (Fin m → Bool) → ℝ),
        k ≤ S.card ∧
        (∀ i j : Fin k, dotV (e i) (e j) = if i = j then 1 else 0) ∧
        (∀ u ∈ Submodule.span ℝ (S : Set ((Fin m → Bool) → ℝ)),
          u = ∑ i : Fin k, (dotV u (e i)) • e i) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, Fin.elim0, le_refl 0, fun i => i.elim0, ?_⟩
    intro u hu
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hu
    subst hu; simp
  | @insert v S' hv ih =>
    rcases ih with ⟨k, e, hkle, horth, hspan⟩
    let w : (Fin m → Bool) → ℝ := v - ∑ i : Fin k, (dotV v (e i)) • e i
    have hworth : ∀ j : Fin k, dotV w (e j) = 0 := by
      intro j
      dsimp only [w]
      rw [dotV_sub_left, dotV_sum_left]
      have hterm : ∀ i : Fin k, dotV ((dotV v (e i)) • e i) (e j) =
          if i = j then dotV v (e j) else 0 := by
        intro i
        rw [dotV_smul_left, horth i j]
        split_ifs with h
        · subst h; ring
        · ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i)]
      simp [Finset.sum_ite_eq']
    by_cases hw : w = 0
    · refine ⟨k, e, le_trans hkle (by rw [Finset.card_insert_of_notMem hv]; omega), horth, ?_⟩
      intro u hu
      refine Submodule.span_induction ?_ (by simp [dotV])
        (fun x y _ _ hx hy => by
          rw [Finset.sum_congr rfl (fun i _ => by rw [dotV_add_left, add_smul]), Finset.sum_add_distrib]
          rw [← hx, ← hy])
        (fun c x _ hx => by
          rw [Finset.sum_congr rfl (fun i _ => by rw [dotV_smul_left, mul_smul]), ← Finset.smul_sum, ← hx])
        hu
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with hxEq | hxS'
      · rw [hxEq]
        exact sub_eq_zero.mp hw
      · exact hspan x (Submodule.subset_span hxS')
    · have hpos : 0 < dotV w w := dotV_self_pos_of_ne_zero hw
      set r := Real.sqrt (dotV w w)
      have hrpos : 0 < r := Real.sqrt_pos.mpr hpos
      have hrsq : r * r = dotV w w := Real.mul_self_sqrt (le_of_lt hpos)
      let eNew : (Fin m → Bool) → ℝ := r⁻¹ • w
      let e' : Fin (k + 1) → (Fin m → Bool) → ℝ := Fin.snoc e eNew
      have horth' : ∀ i j : Fin (k + 1), dotV (e' i) (e' j) = if i = j then 1 else 0 := by
        intro i j
        refine Fin.lastCases ?_ (fun i0 => ?_) i
        · refine Fin.lastCases ?_ (fun j0 => ?_) j
          · simp only [e', Fin.snoc_last, ↓reduceIte, eNew]
            rw [dotV_smul_left, dotV_comm, dotV_smul_left, ← hrsq]
            field_simp [ne_of_gt hrpos]
          · simp only [e', Fin.snoc_last, Fin.snoc_castSucc, (Fin.castSucc_ne_last j0).symm, ↓reduceIte, eNew]
            rw [dotV_smul_left, hworth j0, mul_zero]
        · refine Fin.lastCases ?_ (fun j0 => ?_) j
          · simp only [e', Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last i0, ↓reduceIte, eNew]
            rw [dotV_comm, dotV_smul_left, hworth i0, mul_zero]
          · simp only [e', Fin.snoc_castSucc, Fin.castSucc_inj]
            exact horth i0 j0
      refine ⟨k + 1, e', by rw [Finset.card_insert_of_notMem hv]; omega, horth', ?_⟩
      intro u hu
      refine Submodule.span_induction ?_ (by simp [dotV])
        (fun x y _ _ hx hy => by
          rw [Finset.sum_congr rfl (fun i _ => by rw [dotV_add_left, add_smul]), Finset.sum_add_distrib]
          rw [← hx, ← hy])
        (fun c x _ hx => by
          rw [Finset.sum_congr rfl (fun i _ => by rw [dotV_smul_left, mul_smul]), ← Finset.smul_sum, ← hx])
        hu
      intro x hx
      simp only [Finset.coe_insert, Set.mem_insert_iff] at hx
      rcases hx with hxEq | hxS'
      · rw [hxEq, Fin.sum_univ_castSucc]
        simp only [e', Fin.snoc_castSucc, Fin.snoc_last]
        have hdot_new : dotV v eNew = r := by
          have hvdecomp : v = w + ∑ i : Fin k, (dotV v (e i)) • e i := by
            dsimp only [w]; abel
          rw [hvdecomp, dotV_add_left, dotV_sum_left]
          have h0 : (∑ i : Fin k, dotV ((dotV v (e i)) • e i) eNew) = 0 := by
            apply Finset.sum_eq_zero; intro i _
            rw [dotV_smul_left, dotV_comm (e i) eNew]
            dsimp only [eNew]
            rw [dotV_smul_left, hworth i, mul_zero, mul_zero]
          rw [h0, add_zero, dotV_comm w eNew]
          dsimp only [eNew]
          rw [dotV_smul_left, ← hrsq]
          field_simp [ne_of_gt hrpos]
        rw [hdot_new]
        have hre : r • eNew = w := by
          dsimp only [eNew]
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
        rw [hre]
        dsimp only [w]
        abel
      · have hxEq := hspan x (Submodule.subset_span hxS')
        rw [Fin.sum_univ_castSucc]
        simp only [e', Fin.snoc_castSucc, Fin.snoc_last]
        have hdot0 : dotV x eNew = 0 := by
          rw [hxEq, dotV_sum_left]
          apply Finset.sum_eq_zero; intro i _
          rw [dotV_smul_left, dotV_comm (e i) eNew]
          dsimp only [eNew]
          rw [dotV_smul_left, hworth i, mul_zero, mul_zero]
        rw [hdot0, zero_smul, add_zero]
        exact hxEq

private lemma pythagoras_ge {m k : ℕ} (e : Fin k → (Fin m → Bool) → ℝ)
    (horth : ∀ i j : Fin k, dotV (e i) (e j) = if i = j then 1 else 0)
    (u h : (Fin m → Bool) → ℝ) (hu : u = ∑ i : Fin k, (dotV u (e i)) • e i) :
    dotV h h - ∑ i : Fin k, (dotV h (e i)) ^ 2 ≤ dotV (u - h) (u - h) := by
  let hp : (Fin m → Bool) → ℝ := ∑ i : Fin k, (dotV h (e i)) • e i
  let r : (Fin m → Bool) → ℝ := h - hp
  have hrorth : ∀ j : Fin k, dotV r (e j) = 0 := by
    intro j
    dsimp only [r, hp]
    rw [dotV_sub_left, dotV_sum_left]
    have hterm : ∀ i : Fin k, dotV ((dotV h (e i)) • e i) (e j) =
        if i = j then dotV h (e j) else 0 := by
      intro i; rw [dotV_smul_left, horth i j]
      split_ifs with hij
      · subst hij; ring
      · ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp [Finset.sum_ite_eq']
  have hcross : ∀ w : (Fin m → Bool) → ℝ, (w = ∑ i : Fin k, (dotV w (e i)) • e i) → dotV w r = 0 := by
    intro w hw
    rw [hw, dotV_sum_left]
    apply Finset.sum_eq_zero; intro i _
    rw [dotV_smul_left, dotV_comm (e i) r, hrorth i, mul_zero]
  have hhp_span : hp = ∑ i : Fin k, (dotV hp (e i)) • e i := by
    apply Finset.sum_congr rfl; intro j _
    congr 1
    dsimp only [hp]
    rw [dotV_sum_left]
    have hterm : ∀ i : Fin k, dotV ((dotV h (e i)) • e i) (e j) =
        if i = j then dotV h (e j) else 0 := by
      intro i; rw [dotV_smul_left, horth i j]
      split_ifs with hij
      · subst hij; ring
      · ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp [Finset.sum_ite_eq']
  have h_uhp_span : u - hp = ∑ i : Fin k, (dotV (u - hp) (e i)) • e i := by
    rw [Finset.sum_congr rfl (fun i _ => by rw [dotV_sub_left, sub_smul]), Finset.sum_sub_distrib]
    rw [← hu, ← hhp_span]
  have hdot_uhp_r : dotV (u - hp) r = 0 := hcross (u - hp) h_uhp_span
  have hdot_hp_r : dotV hp r = 0 := hcross hp hhp_span
  have hdot_hp_hp : dotV hp hp = ∑ i : Fin k, (dotV h (e i)) ^ 2 := by
    dsimp only [hp]
    rw [dotV_sum_left]
    apply Finset.sum_congr rfl; intro i _
    rw [dotV_smul_left, dotV_comm (e i), dotV_sum_left]
    have hterm : ∀ j : Fin k, dotV ((dotV h (e j)) • e j) (e i) =
        if j = i then dotV h (e i) else 0 := by
      intro j; rw [dotV_smul_left, horth j i]
      split_ifs with hji
      · subst hji; ring
      · ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  have h_eq1 : u - h = (u - hp) - r := by dsimp only [r]; abel
  have h_eq2 : h = hp + r := by dsimp only [r]; abel
  have h1 : dotV (u - h) (u - h) = dotV (u - hp) (u - hp) + dotV r r := by
    rw [h_eq1, dotV_sub_left, dotV_sub_right (u - hp) (u - hp) r, dotV_sub_right r (u - hp) r,
      dotV_comm r (u - hp), hdot_uhp_r]
    ring
  have h2 : dotV h h = dotV hp hp + dotV r r := by
    conv_lhs => rw [h_eq2]
    rw [dotV_add_left, dotV_add_right, dotV_add_right, dotV_comm r hp, hdot_hp_r]
    ring
  have hnn : 0 ≤ dotV (u - hp) (u - hp) := dotV_self_nonneg _
  linarith

private lemma main_aux (m q d : ℕ)
    (a b : (Fin m → Bool) → Fin q → ℝ)
    (P : (Fin m → Bool) → Polynomial ℝ)
    (hdeg : ∀ g, (P g).natDegree ≤ d) :
    let N := 2 ^ m
    let C := Nat.choose (q + d) d
    let prediction := fun (f g : Fin m → Bool) =>
      (P g).eval (∑ i, a f i * b g i)
    let bit := fun (f g : Fin m → Bool) =>
      if ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
      then (1 : ℝ) else 0
    let domain := (Finset.univ : Finset (Fin m → Bool))
    ((N * (N - C) : ℕ) : ℝ) ≤
      4 * ∑ f ∈ domain, ∑ g ∈ domain, (prediction f g - bit f g) ^ 2 := by
  intro N C prediction bit domain
  by_cases hNC : N ≤ C
  · have h0 : N - C = 0 := Nat.sub_eq_zero_of_le hNC
    rw [h0, mul_zero, Nat.cast_zero]
    apply mul_nonneg (by norm_num)
    apply Finset.sum_nonneg; intro f _
    apply Finset.sum_nonneg; intro g _
    exact sq_nonneg _
  · push_neg at hNC
    let S := (expSet q d).image (monom a)
    rcases exists_orthonormal_span S with ⟨k, e, hkle, horth, hspan⟩
    have hkC : k ≤ C := by
      calc k ≤ S.card := hkle
        _ ≤ (expSet q d).card := Finset.card_image_le
        _ = C := expSet_card q d
    have h4eq : 4 * ∑ f ∈ domain, ∑ g ∈ domain, (prediction f g - bit f g) ^ 2 =
        ∑ g ∈ domain, dotV (fun f => 1 - 2 * prediction f g - signH f g)
          (fun f => 1 - 2 * prediction f g - signH f g) := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro g _
      unfold dotV
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro f _
      dsimp only [signH, bitVal, bit]
      ring
    rw [h4eq]
    have hcol : ∀ g : Fin m → Bool,
        dotV (fun f => signH f g) (fun f => signH f g) -
          ∑ i : Fin k, (dotV (fun f => signH f g) (e i)) ^ 2 ≤
        dotV (fun f => 1 - 2 * prediction f g - signH f g)
          (fun f => 1 - 2 * prediction f g - signH f g) := by
      intro g
      have hmem := centered_col_mem_span a b P hdeg g
      have hsp := hspan (fun f => 1 - 2 * prediction f g) hmem
      exact pythagoras_ge e horth (fun f => 1 - 2 * prediction f g) (fun f => signH f g) hsp
    have hsum_ge : (∑ g ∈ domain, (dotV (fun f => signH f g) (fun f => signH f g) -
          ∑ i : Fin k, (dotV (fun f => signH f g) (e i)) ^ 2)) ≤
        ∑ g ∈ domain, dotV (fun f => 1 - 2 * prediction f g - signH f g)
          (fun f => 1 - 2 * prediction f g - signH f g) :=
      Finset.sum_le_sum (fun g _ => hcol g)
    have hhh : (∑ g ∈ domain, dotV (fun f => signH f g) (fun f => signH f g)) = (N : ℝ) * (N : ℝ) := by
      have h1 : ∀ g : Fin m → Bool, dotV (fun f => signH f g) (fun f => signH f g) = (N : ℝ) := by
        intro g; unfold dotV
        rw [Finset.sum_congr rfl (fun f _ => signH_sq f g), Finset.sum_const, Finset.card_univ]
        simp [N, Fintype.card_bool, Fintype.card_fin]
      rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const]
      simp [domain, N, Fintype.card_bool, Fintype.card_fin]
    have hproj : (∑ g ∈ domain, ∑ i : Fin k, (dotV (fun f => signH f g) (e i)) ^ 2) =
        (k : ℝ) * (N : ℝ) := by
      rw [Finset.sum_comm]
      have hi : ∀ i : Fin k,
          (∑ g ∈ domain, (dotV (fun f => signH f g) (e i)) ^ 2) = (N : ℝ) := by
        intro i
        have heq : ∀ g : Fin m → Bool,
            dotV (fun f => signH f g) (e i) = ∑ f : Fin m → Bool, e i f * signH f g := by
          intro g; unfold dotV; apply Finset.sum_congr rfl; intro f _; ring
        rw [Finset.sum_congr rfl (fun g _ => by rw [heq g]), hadamard_parseval (e i)]
        have hsq : (∑ f : Fin m → Bool, (e i f) ^ 2) = 1 := by
          have := horth i i
          simp only [↓reduceIte] at this
          rw [← this]; unfold dotV; apply Finset.sum_congr rfl; intro f _; ring
        rw [hsq, mul_one]
        simp [N]
      rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib, hhh, hproj] at hsum_ge
    have hcast : ((N * (N - C) : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - (C : ℝ)) := by
      rw [Nat.cast_mul, Nat.cast_sub (le_of_lt hNC)]
    have hkCr : (k : ℝ) ≤ (C : ℝ) := Nat.cast_le.mpr hkC
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith

end PEqualNP.Outside.L_lib_1247_aux

theorem PEqualNP.Outside.L_lib_1247 :
    ∀ (m q d : Nat)
      (a b : (Fin m → Bool) → Fin q → ℝ)
      (P : (Fin m → Bool) → Polynomial ℝ),
      (∀ g, (P g).natDegree ≤ d) →
      let N := 2^m
      let C := Nat.choose (q+d) d
      let prediction := fun (f g : Fin m → Bool) =>
        (P g).eval (∑ i, a f i * b g i)
      let bit := fun (f g : Fin m → Bool) =>
        if ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1
        then (1 : ℝ) else 0
      let domain := (Finset.univ : Finset (Fin m → Bool))
      ((N * (N-C) : Nat) : ℝ) ≤
        4 * ∑ f ∈ domain, ∑ g ∈ domain, (prediction f g - bit f g)^2 := by
  exact PEqualNP.Outside.L_lib_1247_aux.main_aux
