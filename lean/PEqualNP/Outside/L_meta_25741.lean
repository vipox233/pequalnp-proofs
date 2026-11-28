import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25741

open Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

-- Part 1: Reed-Muller exact minimum-weight arithmetic bound

def rmBound (q m d : ℕ) : ℕ :=
  let c := min d (m * (q - 1))
  let a := c / (q - 1)
  let b := c % (q - 1)
  q ^ (m - a) - b * q ^ (m - a - 1)

lemma rmBound_pos {q : ℕ} (hq : 2 ≤ q) (m d : ℕ) : 1 ≤ rmBound q m d := by
  dsimp only [rmBound]
  set c := min d (m * (q - 1))
  set a := c / (q - 1)
  set b := c % (q - 1)
  have hq1 : 0 < q - 1 := by omega
  have hb_lt : b < q - 1 := Nat.mod_lt c hq1
  have hc_le : c ≤ m * (q - 1) := min_le_right _ _
  have ha_le : a ≤ m := Nat.div_le_of_le_mul (by rwa [mul_comm])
  have hdiv : a * (q - 1) + b = c := by
    have := Nat.div_add_mod c (q - 1); rw [mul_comm]; exact this
  by_cases ham : a = m
  · rw [ham] at hdiv
    have hb0 : b = 0 := by omega
    rw [ham, hb0]
    simp
  · have hma : 1 ≤ m - a := by omega
    have hpow : q ^ (m - a) = q * q ^ (m - a - 1) := by
      have h1 : m - a = (m - a - 1) + 1 := by omega
      conv_lhs => rw [h1, pow_succ, mul_comm]
    have hp1 : 1 ≤ q ^ (m - a - 1) := Nat.one_le_pow _ _ (by omega)
    rw [hpow]
    have hmul : (q - b) * q ^ (m - a - 1) = q * q ^ (m - a - 1) - b * q ^ (m - a - 1) :=
      Nat.sub_mul q b (q ^ (m - a - 1))
    rw [← hmul]
    have hqb : 1 ≤ q - b := by omega
    exact Nat.mul_le_mul hqb hp1

lemma rmBound_eq_mul {q m d : ℕ} (hq : 2 ≤ q) (hd : d < m * (q - 1)) :
    rmBound q m d = (q - d % (q - 1)) * q ^ (m - d / (q - 1) - 1) := by
  dsimp only [rmBound]
  have hmin : min d (m * (q - 1)) = d := min_eq_left (le_of_lt hd)
  rw [hmin]
  have hq1 : 0 < q - 1 := by omega
  have ha_lt : d / (q - 1) < m := (Nat.div_lt_iff_lt_mul hq1).mpr hd
  have hpow : q ^ (m - d / (q - 1)) = q * q ^ (m - d / (q - 1) - 1) := by
    have h1 : m - d / (q - 1) = (m - d / (q - 1) - 1) + 1 := by omega
    conv_lhs => rw [h1, pow_succ, mul_comm]
  rw [hpow, Nat.sub_mul]

lemma rmBound_step {q m d r : ℕ} (hq : 2 ≤ q) (hrd : r ≤ d) (hrq : r ≤ q - 1) :
    rmBound q (m + 1) d ≤ (q - r) * rmBound q m (d - r) := by
  have hq1 : 0 < q - 1 := by omega
  by_cases hbig : (m + 1) * (q - 1) ≤ d
  · have h1 : rmBound q (m + 1) d = 1 := by
      dsimp only [rmBound]
      have hmin : min d ((m + 1) * (q - 1)) = (m + 1) * (q - 1) := min_eq_right hbig
      rw [hmin, Nat.mul_div_cancel _ hq1, Nat.mul_mod_left]
      simp
    rw [h1]
    have hqr : 1 ≤ q - r := by omega
    have hrm : 1 ≤ rmBound q m (d - r) := rmBound_pos hq m (d - r)
    exact Nat.mul_le_mul hqr hrm
  · push_neg at hbig
    rw [rmBound_eq_mul hq hbig]
    set a := d / (q - 1)
    set b := d % (q - 1)
    have hdiv : (q - 1) * a + b = d := Nat.div_add_mod d (q - 1)
    have hb_lt : b < q - 1 := Nat.mod_lt d hq1
    have ha_le : a ≤ m := by
      have := (Nat.div_lt_iff_lt_mul hq1).mpr hbig
      omega
    have hm1 : m + 1 - a - 1 = m - a := by omega
    rw [hm1]
    by_cases hrb : r ≤ b
    · by_cases ham : a = m
      · have hge : m * (q - 1) ≤ d - r := by
          rw [ham] at hdiv
          have : m * (q - 1) = (q - 1) * m := mul_comm _ _
          omega
        have hrm1 : rmBound q m (d - r) = 1 := by
          dsimp only [rmBound]
          have hmin : min (d - r) (m * (q - 1)) = m * (q - 1) := min_eq_right hge
          rw [hmin, Nat.mul_div_cancel _ hq1, Nat.mul_mod_left]
          simp
        rw [ham, Nat.sub_self, pow_zero, mul_one, hrm1, mul_one]
        omega
      · have hlt : d - r < m * (q - 1) := by
          have h1 : (a + 1) * (q - 1) ≤ m * (q - 1) := Nat.mul_le_mul_right (q - 1) (by omega)
          have h2 : a * (q - 1) = (q - 1) * a := mul_comm _ _
          have h3 : (a + 1) * (q - 1) = a * (q - 1) + (q - 1) := Nat.succ_mul a (q - 1)
          omega
        rw [rmBound_eq_mul hq hlt]
        have hdr_eq : d - r = (b - r) + (q - 1) * a := by omega
        have hdiv' : (d - r) / (q - 1) = a := by
          rw [hdr_eq, Nat.add_mul_div_left _ _ hq1, Nat.div_eq_of_lt (by omega), zero_add]
        have hmod' : (d - r) % (q - 1) = b - r := by
          rw [hdr_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        rw [hdiv', hmod']
        have hpow : q ^ (m - a) = q * q ^ (m - a - 1) := by
          have h1 : m - a = (m - a - 1) + 1 := by omega
          conv_lhs => rw [h1, pow_succ, mul_comm]
        rw [hpow, ← mul_assoc, ← mul_assoc]
        refine Nat.mul_le_mul_right (q ^ (m - a - 1)) ?_
        have hident : (q - r) * (q - (b - r)) = (q - b) * q + r * (b - r) := by
          zify [show r ≤ q by omega, show b - r ≤ q by omega, show r ≤ b by omega, show b ≤ q by omega]
          ring
        omega
    · push_neg at hrb
      have ha1 : 1 ≤ a := by
        by_contra ha0
        have ha_eq : a = 0 := Nat.lt_one_iff.mp (Nat.lt_of_not_ge ha0)
        rw [ha_eq, mul_zero, zero_add] at hdiv
        omega
      have hlt : d - r < m * (q - 1) := by
        have h1 : a * (q - 1) ≤ m * (q - 1) := Nat.mul_le_mul_right (q - 1) ha_le
        have h2 : a * (q - 1) = (q - 1) * a := mul_comm _ _
        omega
      rw [rmBound_eq_mul hq hlt]
      have hdr_eq : d - r = (q - 1 + b - r) + (q - 1) * (a - 1) := by
        have h1 : (q - 1) * a = (q - 1) * (a - 1) + (q - 1) := by
          have : a = (a - 1) + 1 := by omega
          conv_lhs => rw [this, mul_add, mul_one]
        omega
      have hrem_lt : q - 1 + b - r < q - 1 := by omega
      have hdiv' : (d - r) / (q - 1) = a - 1 := by
        rw [hdr_eq, Nat.add_mul_div_left _ _ hq1, Nat.div_eq_of_lt hrem_lt, zero_add]
      have hmod' : (d - r) % (q - 1) = q - 1 + b - r := by
        rw [hdr_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
      rw [hdiv', hmod']
      have hm_eq : m - (a - 1) - 1 = m - a := by omega
      rw [hm_eq, ← mul_assoc]
      refine Nat.mul_le_mul_right (q ^ (m - a)) ?_
      have hident : (q - r) * (q - (q - 1 + b - r)) = (q - b) + (q - 1 - r) * (r - b) := by
        zify [show r ≤ q by omega, show q - 1 + b - r ≤ q by omega, show r ≤ q - 1 + b by omega,
          show b ≤ q by omega, show r ≤ q - 1 by omega, show b ≤ r by omega, show 1 ≤ q by omega]
        ring
      omega

-- Part 2: Reduced multivariate polynomials over a finite field E

section PolyBound

variable {E : Type} [Field E] [Fintype E]

def redExp (q e : ℕ) : ℕ :=
  if e = 0 then 0 else (e - 1) % (q - 1) + 1

lemma redExp_le (q e : ℕ) : redExp q e ≤ e := by
  dsimp only [redExp]
  split_ifs with h
  · omega
  · have hmod := Nat.mod_le (e - 1) (q - 1)
    omega

lemma redExp_lt {q : ℕ} (hq : 2 ≤ q) (e : ℕ) : redExp q e ≤ q - 1 := by
  dsimp only [redExp]
  split_ifs with h
  · omega
  · have hmod := Nat.mod_lt (e - 1) (by omega : 0 < q - 1)
    omega

lemma pow_redExp_eq (x : E) (e : ℕ) :
    x ^ redExp (Fintype.card E) e = x ^ e := by
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  dsimp only [redExp]
  split_ifs with h0
  · rw [h0]
  · by_cases hx : x = 0
    · subst hx
      have h1 : 0 < (e - 1) % (Fintype.card E - 1) + 1 := by omega
      have h2 : 0 < e := by omega
      rw [zero_pow (by omega), zero_pow (by omega)]
    · have hfermat : x ^ (Fintype.card E - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx
      have hdiv : (e - 1) = (Fintype.card E - 1) * ((e - 1) / (Fintype.card E - 1)) +
          (e - 1) % (Fintype.card E - 1) := (Nat.div_add_mod (e - 1) (Fintype.card E - 1)).symm
      have he : e = (e - 1) + 1 := by omega
      conv_rhs => rw [he, hdiv, pow_succ, pow_add, pow_mul, hfermat, one_pow, one_mul]
      rw [pow_succ]

noncomputable def reducePoly {m : ℕ} (P : MvPolynomial (Fin m) E) : MvPolynomial (Fin m) E :=
  ∑ s ∈ P.support, MvPolynomial.monomial (s.mapRange (redExp (Fintype.card E)) (by simp [redExp])) (P.coeff s)

lemma totalDegree_sum_le {ι : Type} {m : ℕ} {E : Type} [CommSemiring E]
    (s : Finset ι) (f : ι → MvPolynomial (Fin m) E) :
    (∑ i ∈ s, f i).totalDegree ≤ s.sup (fun i => (f i).totalDegree) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le (le_max_left _ _) (le_trans ih (le_max_right _ _)))

lemma totalDegree_prod_le {ι : Type} {m : ℕ} {E : Type} [CommSemiring E]
    (s : Finset ι) (f : ι → MvPolynomial (Fin m) E) :
    (∏ i ∈ s, f i).totalDegree ≤ ∑ i ∈ s, (f i).totalDegree := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact le_trans (MvPolynomial.totalDegree_mul _ _) (Nat.add_le_add_left ih _)

lemma card_filter_add_not {α : Type} (s : Finset α) (p : α → Prop) :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  have hdisj : Disjoint (s.filter p) (s.filter (fun x => ¬ p x)) := by
    rw [Finset.disjoint_left]; intro x h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
  have hunion : s.filter p ∪ s.filter (fun x => ¬ p x) = s := by
    ext x; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  rw [← Finset.card_union_of_disjoint hdisj, hunion]

lemma eval_reducePoly {m : ℕ} (P : MvPolynomial (Fin m) E) (x : Fin m → E) :
    MvPolynomial.eval x (reducePoly P) = MvPolynomial.eval x P := by
  rw [reducePoly, map_sum, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [MvPolynomial.eval_monomial]
  congr 1
  rw [Finsupp.prod_of_support_subset _ (Finset.subset_univ _)]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [Finsupp.mapRange_apply]
    exact pow_redExp_eq (x j) (s j)
  · intro j _; simp

lemma totalDegree_reducePoly_le {m : ℕ} (P : MvPolynomial (Fin m) E) :
    (reducePoly P).totalDegree ≤ P.totalDegree := by
  rw [reducePoly]
  refine le_trans (totalDegree_sum_le _ _) ?_
  refine Finset.sup_le fun s hs => ?_
  refine le_trans (MvPolynomial.totalDegree_monomial_le _ _) ?_
  have hsum_le : (s.mapRange (redExp (Fintype.card E)) (by simp [redExp])).sum (fun _ e => e) ≤
      s.sum (fun _ e => e) := by
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _),
      Finsupp.sum_of_support_subset _ (Finset.subset_univ _)]
    · refine Finset.sum_le_sum fun j _ => ?_
      simp only [Finsupp.mapRange_apply]
      exact redExp_le (Fintype.card E) (s j)
    · intro j _; rfl
    · intro j _; rfl
  refine le_trans hsum_le ?_
  rw [MvPolynomial.totalDegree]
  exact Finset.le_sup (f := fun s : Fin m →₀ ℕ => s.sum fun _ e => e) hs

lemma degreeOf_reducePoly_le {m : ℕ} (P : MvPolynomial (Fin m) E) (j : Fin m) :
    (reducePoly P).degreeOf j ≤ Fintype.card E - 1 := by
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  rw [MvPolynomial.degreeOf_eq_sup]
  refine Finset.sup_le fun t ht => ?_
  rw [MvPolynomial.mem_support_iff, reducePoly, MvPolynomial.coeff_sum] at ht
  have hex : ∃ s ∈ P.support,
      (MvPolynomial.monomial (s.mapRange (redExp (Fintype.card E)) (by simp [redExp])) (P.coeff s)).coeff t ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact ht (Finset.sum_eq_zero hall)
  obtain ⟨s, _, hs⟩ := hex
  rw [MvPolynomial.coeff_monomial] at hs
  have hteq : s.mapRange (redExp (Fintype.card E)) (by simp [redExp]) = t := by
    by_contra hne; exact hs (if_neg hne)
  rw [← hteq, Finsupp.mapRange_apply]
  exact redExp_lt hq (s j)

lemma eval_finSuccEquiv {m : ℕ} (Q : MvPolynomial (Fin (m + 1)) E) (a : E) (y : Fin m → E) :
    ((MvPolynomial.finSuccEquiv E m Q).map (MvPolynomial.eval y)).eval a =
      MvPolynomial.eval (Fin.cons a y) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    have hc : MvPolynomial.finSuccEquiv E m (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
      have h1 := (MvPolynomial.finSuccEquiv E m).commutes c
      simpa [MvPolynomial.algebraMap_eq] using h1
    rw [hc, Polynomial.map_C, Polynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q ihp ihq =>
    simp [map_add, Polynomial.map_add, Polynomial.eval_add, ihp, ihq]
  | mul_X p i ih =>
    rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul, ih, map_mul]
    refine congrArg (MvPolynomial.eval (Fin.cons a y) p * ·) ?_
    refine Fin.cases ?_ ?_ i
    · rw [MvPolynomial.finSuccEquiv_X_zero, Polynomial.map_X, Polynomial.eval_X,
        MvPolynomial.eval_X, Fin.cons_zero]
    · intro j
      rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C, Polynomial.eval_C,
        MvPolynomial.eval_X, MvPolynomial.eval_X, Fin.cons_succ]

lemma reed_muller_nonzeros : ∀ (m d : ℕ) (Q : MvPolynomial (Fin m) E),
    Q ≠ 0 →
    Q.totalDegree ≤ d →
    (∀ j : Fin m, Q.degreeOf j ≤ Fintype.card E - 1) →
    rmBound (Fintype.card E) m d ≤
      (Finset.univ.filter (fun x : Fin m → E => MvPolynomial.eval x Q ≠ 0)).card := by
  intro m
  have hq : 2 ≤ Fintype.card E := Fintype.one_lt_card
  induction m with
  | zero =>
    intro d Q hQ _ _
    have hrm : rmBound (Fintype.card E) 0 d = 1 := by
      dsimp only [rmBound]; simp
    rw [hrm]
    have hQ_eq : Q = MvPolynomial.C (Q.coeff 0) := by
      ext s
      rw [Subsingleton.elim s 0, MvPolynomial.coeff_C]
      simp
    have hne : MvPolynomial.eval (Fin.elim0 : Fin 0 → E) Q ≠ 0 := by
      intro h0
      rw [hQ_eq, MvPolynomial.eval_C] at h0
      exact hQ (by rw [hQ_eq, h0, map_zero])
    have hmem : (Fin.elim0 : Fin 0 → E) ∈ Finset.univ.filter (fun x : Fin 0 → E => MvPolynomial.eval x Q ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    exact Finset.card_pos.mpr ⟨Fin.elim0, hmem⟩
  | succ m ih =>
    intro d Q hQ hdeg hdegOf
    set P1 : Polynomial (MvPolynomial (Fin m) E) := MvPolynomial.finSuccEquiv E m Q
    have hP1 : P1 ≠ 0 := fun h => hQ ((MvPolynomial.finSuccEquiv E m).injective (by simp [P1, h]))
    set r : ℕ := P1.natDegree
    set L : MvPolynomial (Fin m) E := P1.leadingCoeff
    have hL : L ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP1
    have hL_nonempty : L.support.Nonempty := MvPolynomial.support_nonempty.mpr hL
    have hcoeff_cons : ∀ (s : Fin m →₀ ℕ),
        L.coeff s = Q.coeff (Finsupp.cons r s) := fun s => by
      dsimp only [L, Polynomial.leadingCoeff, r, P1]
      exact MvPolynomial.finSuccEquiv_coeff_coeff s Q r
    have hr_le_q : r ≤ Fintype.card E - 1 := by
      obtain ⟨s, hs⟩ := hL_nonempty
      have hQmem : Finsupp.cons r s ∈ Q.support := by
        rw [MvPolynomial.mem_support_iff] at hs ⊢
        rw [← hcoeff_cons s]; exact hs
      have hle : (Finsupp.cons r s) 0 ≤ Q.degreeOf 0 := by
        rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun t : Fin (m + 1) →₀ ℕ => t 0) hQmem
      simp only [Finsupp.cons_zero] at hle
      exact le_trans hle (hdegOf 0)
    have hr_le_d : r ≤ d := by
      obtain ⟨s, hs⟩ := hL_nonempty
      have hQmem : Finsupp.cons r s ∈ Q.support := by
        rw [MvPolynomial.mem_support_iff] at hs ⊢
        rw [← hcoeff_cons s]; exact hs
      have hle : (Finsupp.cons r s).sum (fun _ e => e) ≤ Q.totalDegree := by
        rw [MvPolynomial.totalDegree]
        exact Finset.le_sup (f := fun t : Fin (m + 1) →₀ ℕ => t.sum fun _ e => e) hQmem
      have hsum : (Finsupp.cons r s).sum (fun _ e => e) = r + s.sum (fun _ e => e) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
          Fin.sum_univ_succ]
        simp
      omega
    have hL_deg : L.totalDegree ≤ d - r := by
      rw [MvPolynomial.totalDegree]
      refine Finset.sup_le fun s hs => ?_
      have hQmem : Finsupp.cons r s ∈ Q.support := by
        rw [MvPolynomial.mem_support_iff] at hs ⊢
        rw [← hcoeff_cons s]; exact hs
      have hle : (Finsupp.cons r s).sum (fun _ e => e) ≤ Q.totalDegree := by
        rw [MvPolynomial.totalDegree]
        exact Finset.le_sup (f := fun t : Fin (m + 1) →₀ ℕ => t.sum fun _ e => e) hQmem
      have hsum : (Finsupp.cons r s).sum (fun _ e => e) = r + s.sum (fun _ e => e) := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Finsupp.sum_fintype _ _ (fun _ => rfl),
          Fin.sum_univ_succ]
        simp
      omega
    have hL_degOf : ∀ j : Fin m, L.degreeOf j ≤ Fintype.card E - 1 := by
      intro j
      rw [MvPolynomial.degreeOf_eq_sup]
      refine Finset.sup_le fun s hs => ?_
      have hQmem : Finsupp.cons r s ∈ Q.support := by
        rw [MvPolynomial.mem_support_iff] at hs ⊢
        rw [← hcoeff_cons s]; exact hs
      have hle : (Finsupp.cons r s) j.succ ≤ Q.degreeOf j.succ := by
        rw [MvPolynomial.degreeOf_eq_sup]
        exact Finset.le_sup (f := fun t : Fin (m + 1) →₀ ℕ => t j.succ) hQmem
      simp only [Finsupp.cons_succ] at hle
      exact le_trans hle (hdegOf j.succ)
    have hIH := ih (d - r) L hL hL_deg hL_degOf
    -- For each y with L.eval y != 0, there are at least |E| - r values of a with Q.eval (Fin.cons a y) != 0
    let Ygood : Finset (Fin m → E) := Finset.univ.filter (fun y => MvPolynomial.eval y L ≠ 0)
    have hfiber : ∀ y ∈ Ygood, Fintype.card E - r ≤
        (Finset.univ.filter (fun a : E => MvPolynomial.eval (Fin.cons a y) Q ≠ 0)).card := by
      intro y hy
      have hLy : MvPolynomial.eval y L ≠ 0 := (Finset.mem_filter.mp hy).2
      let fy : Polynomial E := P1.map (MvPolynomial.eval y)
      have hfy_coeff : fy.coeff r = MvPolynomial.eval y L := by
        dsimp only [fy, L, Polynomial.leadingCoeff, r]
        rw [Polynomial.coeff_map]
      have hfy_ne : fy ≠ 0 := fun h0 => hLy (by rw [← hfy_coeff, h0, Polynomial.coeff_zero])
      have hfy_deg : fy.natDegree ≤ r := Polynomial.natDegree_map_le
      have hroots_le : (Finset.univ.filter (fun a : E => fy.eval a = 0)).card ≤ r := by
        have hsub : Finset.univ.filter (fun a : E => fy.eval a = 0) ⊆ fy.roots.toFinset := by
          intro a ha
          have ha0 : fy.eval a = 0 := (Finset.mem_filter.mp ha).2
          exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hfy_ne).mpr ha0)
        calc (Finset.univ.filter (fun a : E => fy.eval a = 0)).card
            ≤ fy.roots.toFinset.card := Finset.card_le_card hsub
          _ ≤ fy.roots.card := Multiset.toFinset_card_le _
          _ ≤ fy.natDegree := Polynomial.card_roots' fy
          _ ≤ r := hfy_deg
      have hsplit := card_filter_add_not (Finset.univ : Finset E) (fun a : E => fy.eval a = 0)
      have heq_filt : Finset.univ.filter (fun a : E => ¬ fy.eval a = 0) =
          Finset.univ.filter (fun a : E => MvPolynomial.eval (Fin.cons a y) Q ≠ 0) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, fy, P1, eval_finSuccEquiv]
      rw [heq_filt] at hsplit
      have huniv : (Finset.univ : Finset E).card = Fintype.card E := Finset.card_univ
      omega
    -- Biject Fin (m+1) -> E with E x (Fin m -> E)
    let e : (E × (Fin m → E)) ≃ (Fin (m + 1) → E) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun x => (x 0, Fin.tail x)
        left_inv := fun ⟨a, y⟩ => by ext <;> simp
        right_inv := fun x => Fin.cons_self_tail x }
    have hcard_eq : (Finset.univ.filter (fun x : Fin (m + 1) → E => MvPolynomial.eval x Q ≠ 0)).card =
        (Finset.univ.filter (fun p : E × (Fin m → E) => MvPolynomial.eval (Fin.cons p.1 p.2) Q ≠ 0)).card := by
      refine Finset.card_bij (fun x _ => e.symm x) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        simpa [e] using hx
      · intro x₁ _ x₂ _ h; exact e.symm.injective h
      · intro p hp
        refine ⟨e p, ?_, e.symm_apply_apply p⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        exact hp
    have hprod_le : (Fintype.card E - r) * Ygood.card ≤
        (Finset.univ.filter (fun p : E × (Fin m → E) => MvPolynomial.eval (Fin.cons p.1 p.2) Q ≠ 0)).card := by
      let Sbig := Ygood.biUnion (fun y => (Finset.univ.filter (fun a : E => MvPolynomial.eval (Fin.cons a y) Q ≠ 0)).map
        ⟨fun a => (a, y), fun _ _ h => (Prod.mk.inj h).1⟩)
      have hsub : Sbig ⊆ Finset.univ.filter (fun p : E × (Fin m → E) => MvPolynomial.eval (Fin.cons p.1 p.2) Q ≠ 0) := by
        intro p hp
        simp only [Sbig, Finset.mem_biUnion, Finset.mem_map, Function.Embedding.coeFn_mk,
          Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        obtain ⟨y, _, a, ha, rfl⟩ := hp
        exact ha
      have hdisj : Set.PairwiseDisjoint (Ygood : Set (Fin m → E))
          (fun y => (Finset.univ.filter (fun a : E => MvPolynomial.eval (Fin.cons a y) Q ≠ 0)).map
            ⟨fun a => (a, y), fun _ _ h => (Prod.mk.inj h).1⟩) := by
        intro y₁ _ y₂ _ hne
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hp1 hp2
        obtain ⟨a₁, _, rfl⟩ := hp1
        obtain ⟨a₂, _, h2⟩ := hp2
        exact hne (Prod.mk.inj h2).2.symm
      have hcard_big : Sbig.card = ∑ y ∈ Ygood, (Finset.univ.filter (fun a : E => MvPolynomial.eval (Fin.cons a y) Q ≠ 0)).card := by
        rw [Finset.card_biUnion hdisj]
        refine Finset.sum_congr rfl fun y _ => Finset.card_map _
      calc (Fintype.card E - r) * Ygood.card
          = ∑ _y ∈ Ygood, (Fintype.card E - r) := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ y ∈ Ygood, (Finset.univ.filter (fun a : E => MvPolynomial.eval (Fin.cons a y) Q ≠ 0)).card :=
            Finset.sum_le_sum hfiber
        _ = Sbig.card := hcard_big.symm
        _ ≤ _ := Finset.card_le_card hsub
    rw [hcard_eq]
    calc rmBound (Fintype.card E) (m + 1) d
        ≤ (Fintype.card E - r) * rmBound (Fintype.card E) m (d - r) :=
          rmBound_step hq hr_le_d hr_le_q
      _ ≤ (Fintype.card E - r) * Ygood.card := Nat.mul_le_mul_left _ hIH
      _ ≤ _ := hprod_le

end PolyBound

-- Part 3: Circuit-to-rank bridge via L_meta_25647 and determinant polynomial construction

lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_ite_ne_zero (x : ZMod 2) : (if decide (x ≠ 0) = true then (1 : ZMod 2) else 0) = x := by
  rcases zmod2_cases x with rfl | rfl <;> decide

lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with rfl | rfl <;> decide

lemma zmod2_xor_decide (a b : ZMod 2) :
    (if xor (decide (a ≠ 0)) (decide (b ≠ 0)) = true then (1 : ZMod 2) else 0) = a + b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

abbrev F2 : Type := ZMod 2

def b2f (b : Bool) : F2 := if b then 1 else 0

lemma f2_cases (x : F2) : x = 0 ∨ x = 1 := by
  rcases x with ⟨v, hv⟩
  interval_cases v
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma f2_add_self (x : F2) : x + x = 0 := by
  rcases f2_cases x with rfl | rfl <;> decide

lemma f2_eq_of_add_eq_zero {x y : F2} (h : x + y = 0) : x = y := by
  rcases f2_cases x with rfl | rfl <;> rcases f2_cases y with rfl | rfl <;> first | rfl | exact absurd h (by decide)

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_not (a : Bool) : b2f (!a) = b2f a + 1 := by
  cases a <;> decide

lemma b2f_inj {a b : Bool} (h : b2f a = b2f b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

def nlGate (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depthStep (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat]

def wireStep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map (fun a => ws.getD a false))]

def depthsOf (width : ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl depthStep (List.replicate width 0)

def wiresOf (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl wireStep inp

lemma nat_max_zero (a : ℕ) : max a 0 = a := max_eq_left (Nat.zero_le a)

lemma foldl_depthStep_length (ds : List ℕ) (gs : List Gate) :
    (gs.foldl depthStep ds).length = ds.length + gs.length := by
  induction gs generalizing ds with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, depthStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma depthsOf_length (width : ℕ) (gs : List Gate) :
    (depthsOf width gs).length = width + gs.length := by
  simp [depthsOf, foldl_depthStep_length]

lemma foldl_wireStep_length (ws : List Bool) (gs : List Gate) :
    (gs.foldl wireStep ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresOf_length (gs : List Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  simp [wiresOf, foldl_wireStep_length]

lemma getD_append_left {α : Type} (l₁ l₂ : List α) (i : ℕ) (d : α) (hi : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self {α : Type} (l : List α) (x d : α) :
    (l ++ [x]).getD l.length d = x := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl l.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma foldl_depthStep_getD_old (ds : List ℕ) (gs : List Gate) (w : ℕ) (hw : w < ds.length) :
    (gs.foldl depthStep ds).getD w 0 = ds.getD w 0 := by
  induction gs generalizing ds with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (depthStep ds g).length := by simp [depthStep]; omega
    rw [ih (depthStep ds g) hw']
    exact getD_append_left ds _ w 0 hw

lemma foldl_wireStep_getD_old (ws : List Bool) (gs : List Gate) (w : ℕ) (hw : w < ws.length) :
    (gs.foldl wireStep ws).getD w false = ws.getD w false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hw' : w < (wireStep ws g).length := by simp [wireStep]; omega
    rw [ih (wireStep ws g) hw']
    exact getD_append_left ws _ w false hw

lemma gate_eval_expand_two (op : GateOp) :
    ∃ c0 c1 c2 : F2, ∀ x y : Bool,
      b2f (op.eval [x, y]) =
        c0 + c1 * b2f x + c2 * b2f y +
        b2f (xor (xor (op.eval [false, false]) (op.eval [false, true]))
                 (xor (op.eval [true, false]) (op.eval [true, true]))) * (b2f x * b2f y) := by
  refine ⟨b2f (op.eval [false, false]),
    b2f (op.eval [true, false]) + b2f (op.eval [false, false]),
    b2f (op.eval [false, true]) + b2f (op.eval [false, false]), ?_⟩
  intro x y
  have hb0 : b2f false = 0 := rfl
  have hb1 : b2f true = 1 := rfl
  simp only [b2f_xor]
  cases x <;> cases y
  · simp only [hb0, mul_zero, add_zero]
  · simp only [hb0, hb1, mul_zero, mul_one, add_zero]
    have h := f2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [hb0, hb1, mul_zero, mul_one, add_zero]
    have h := f2_add_self (b2f (op.eval [false, false]))
    linear_combination -h
  · simp only [hb1, mul_one]
    have h1 := f2_add_self (b2f (op.eval [false, false]))
    have h2 := f2_add_self (b2f (op.eval [false, true]))
    have h3 := f2_add_self (b2f (op.eval [true, false]))
    linear_combination -h1 - h1 - h2 - h3

lemma gate_eval_expand_one (op : GateOp) :
    ∃ c0 c1 : F2, ∀ x : Bool, b2f (op.eval [x]) = c0 + c1 * b2f x := by
  refine ⟨b2f (op.eval [false]), b2f (op.eval [true]) + b2f (op.eval [false]), ?_⟩
  intro x
  have hb0 : b2f false = 0 := rfl
  have hb1 : b2f true = 1 := rfl
  cases x <;> simp only [hb0, hb1, mul_zero, mul_one, add_zero]
  have h := f2_add_self (b2f (op.eval [false]))
  linear_combination -h

-- Section 1: Matrix rank lemmas over F2

lemma rank_vecMulVec_le {n m : ℕ} (p : Fin n → F2) (q : Fin m → F2) :
    (Matrix.of fun i j => p i * q j).rank ≤ 1 := by
  let A : Matrix (Fin n) (Fin m) F2 := Matrix.of fun i j => p i * q j
  have hsub : LinearMap.range A.mulVecLin ≤ Submodule.span F2 {p} := by
    rintro _ ⟨v, rfl⟩
    have heq : A.mulVecLin v = (∑ j : Fin m, q j * v j) • p := by
      ext i
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, A,
        Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton p))
  have hle1 : Module.finrank F2 (LinearMap.range A.mulVecLin) ≤ Module.finrank F2 (Submodule.span F2 {p}) :=
    Submodule.finrank_mono hsub
  have hle2 : Module.finrank F2 (Submodule.span F2 {p}) ≤ 1 := by
    have h := finrank_span_le_card (R := F2) ({p} : Set (Fin n → F2))
    simpa using h
  exact le_trans hle1 hle2

lemma rank_add_le {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A B : Matrix ι κ F2) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hsub : LinearMap.range (A + B).mulVecLin ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have heq : (A + B).mulVecLin v = A.mulVecLin v + B.mulVecLin v := by
      ext i; simp
    rw [heq]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  have h1 : Module.finrank F2 (LinearMap.range (A + B).mulVecLin) ≤
      Module.finrank F2 (↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin)) :=
    Submodule.finrank_mono hsub
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  change Module.finrank F2 (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank F2 (LinearMap.range A.mulVecLin) + Module.finrank F2 (LinearMap.range B.mulVecLin)
  omega

lemma rank_zero_eq {n m : ℕ} : (0 : Matrix (Fin n) (Fin m) F2).rank = 0 := by
  simp [Matrix.rank]

lemma rank_sum_le {ι : Type} {n m : ℕ} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin m) F2) :
    (∑ i ∈ s, M i).rank ≤ ∑ i ∈ s, (M i).rank := by
  induction s using Finset.induction_on with
  | empty => simp [rank_zero_eq]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (rank_add_le _ _) (Nat.add_le_add_left ih _)


lemma rank_decomp {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) :
    ∃ (p : Fin M.rank → Fin n → F2) (q : Fin M.rank → Fin m → F2),
      ∀ x y, M x y = ∑ i : Fin M.rank, p i x * q i y := by
  let b := Module.finBasis F2 (LinearMap.range M.mulVecLin)
  refine ⟨fun i x => (b i).1 x,
    fun i y => b.repr ⟨M.mulVec (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩ i, ?_⟩
  intro x y
  have hlin := b.sum_repr ⟨M.mulVec (Pi.single y 1), ⟨Pi.single y 1, rfl⟩⟩
  have hval := congrFun (congrArg Subtype.val hlin) x
  simp only [Submodule.coe_sum, SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
  have hcol : M.mulVec (Pi.single y 1) x = M x y := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hcol] at hval
  rw [← hval]
  refine Finset.sum_congr rfl fun i _ => mul_comm _ _


lemma oneEach_getD {n m : ℕ} (x : Fin n) (y : Fin m) (w : ℕ) (hw : w < n + m) :
    (oneEach x y).getD w false =
      if h : w < n then decide (x.val = w) else decide (y.val = w - n) := by
  simp only [oneEach]
  by_cases h : w < n
  · rw [dif_pos h]
    have hlen : w < (List.ofFn (fun i : Fin n => decide (i = x))).length := by simp [h]
    rw [getD_append_left _ _ w false hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, ↓reduceDIte, Option.getD_some]
    by_cases hx : x.val = w
    · have : (⟨w, h⟩ : Fin n) = x := Fin.ext hx.symm
      simp [this, hx]
    · have : (⟨w, h⟩ : Fin n) ≠ x := fun he => hx (congrArg Fin.val he).symm
      simp [this, hx]
  · rw [dif_neg h]
    have hge : (List.ofFn (fun i : Fin n => decide (i = x))).length ≤ w := by simp; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, List.length_ofFn,
      List.getElem?_ofFn]
    have hwn : w - n < m := by omega
    rw [dif_pos hwn, Option.getD_some]
    by_cases hy : y.val = w - n
    · have : (⟨w - n, hwn⟩ : Fin m) = y := Fin.ext hy.symm
      simp [this, hy]
    · have : (⟨w - n, hwn⟩ : Fin m) ≠ y := fun he => hy (congrArg Fin.val he).symm
      simp [this, hy]

lemma foldr_max_le_iff (l : List ℕ) (b : ℕ) :
    l.foldr max 0 ≤ b ↔ ∀ x ∈ l, x ≤ b := by
  induction l with
  | nil => simp
  | cons a t ih => simp [max_le_iff, ih]

lemma circuit_depth1_decomp (n m : ℕ) (gs : List Gate)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + m + j)
    (hfan : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ M : Fin gs.length → Matrix (Fin n) (Fin m) F2,
      (∀ k, (M k).rank ≤ 2) ∧
      ∀ w < n + m + gs.length,
        ((depthsOf (n + m) gs).getD w 0 = 0 →
          ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
            ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD w false) = α x + β y + c) ∧
        ((depthsOf (n + m) gs).getD w 0 ≤ 1 →
          ∃ (coeff : Fin gs.length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
            (∀ k, coeff k ≠ 0 → nlGate (gs.get k) = true) ∧
            ∀ x y, b2f ((wiresOf gs (oneEach x y)).getD w false) =
              (∑ k : Fin gs.length, coeff k * M k x y) + α x + β y + c) := by
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨fun k => Fin.elim0 k, fun k => Fin.elim0 k, ?_⟩
    intro w hw
    simp only [List.length_nil, add_zero] at hw
    have hw_rep : ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
        ∀ x y, b2f ((wiresOf [] (oneEach x y)).getD w false) = α x + β y + c := by
      by_cases h : w < n
      · refine ⟨fun x => b2f (decide (x.val = w)), fun _ => 0, 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach_getD x y w hw, h, ↓reduceDIte, add_zero]
      · refine ⟨fun _ => 0, fun y => b2f (decide (y.val = w - n)), 0, fun x y => ?_⟩
        simp only [wiresOf, List.foldl_nil, oneEach_getD x y w hw, h, ↓reduceDIte, zero_add, add_zero]
    refine ⟨fun _ => hw_rep, fun _ => ?_⟩
    obtain ⟨α, β, c, hxy⟩ := hw_rep
    exact ⟨fun k => Fin.elim0 k, α, β, c, fun k => Fin.elim0 k, fun x y => by
      rw [hxy x y]; simp⟩
  | append_singleton gs g ih =>
    have hrb_gs : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + m + j := by
      intro j hj i hi
      have h1 := hrb j (by simp; omega) i
      have hgd : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ :=
        getD_append_left gs [g] j _ hj
      rw [hgd] at h1
      exact h1 hi
    have hfan_gs : ∀ g' ∈ gs, g'.inputs.length ≤ 2 := fun g' hg' => hfan g' (by simp [hg'])
    have hfan_g : g.inputs.length ≤ 2 := hfan g (by simp)
    have hrb_g : ∀ i ∈ g.inputs, i < n + m + gs.length := by
      intro i hi
      have h1 := hrb gs.length (by simp) i
      rw [getD_append_self gs g _] at h1
      exact h1 hi
    obtain ⟨Mprev, hMrk, hWprev⟩ := ih hrb_gs hfan_gs
    let ds := depthsOf (n + m) gs
    have hds_len : ds.length = n + m + gs.length := depthsOf_length (n + m) gs
    have hds_new : depthsOf (n + m) (gs ++ [g]) = depthStep ds g := by
      simp [depthsOf, ds, List.foldl_append]
    have hws_new : ∀ inp, wiresOf (gs ++ [g]) inp = wireStep (wiresOf gs inp) g := fun inp => by
      simp [wiresOf, List.foldl_append]
    have hws_len : ∀ (x : Fin n) (y : Fin m), (wiresOf gs (oneEach x y)).length = n + m + gs.length :=
      fun x y => by simp only [wiresOf_length, oneEach, List.length_append, List.length_ofFn]
    have hd_last : (depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 =
        (g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nlGate g).toNat := by
      rw [hds_new, depthStep, ← hds_len, getD_append_self]
    have hw_last : ∀ (x : Fin n) (y : Fin m), (wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false =
        g.op.eval (g.inputs.map (fun a => (wiresOf gs (oneEach x y)).getD a false)) := by
      intro x y
      rw [hws_new, wireStep, ← hws_len x y, getD_append_self]
    -- Determine the new rank-<=2 matrix M_last for gate g
    have hlast_build :
        ∃ (Mlast : Matrix (Fin n) (Fin m) F2),
          Mlast.rank ≤ 2 ∧
          ((depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 = 0 →
            ∃ (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                α x + β y + c) ∧
          ((depthsOf (n + m) (gs ++ [g])).getD (n + m + gs.length) 0 ≤ 1 →
            ∃ (coeff : Fin (gs ++ [g]).length → F2) (α : Fin n → F2) (β : Fin m → F2) (c : F2),
              (∀ k, coeff k ≠ 0 → nlGate ((gs ++ [g]).get k) = true) ∧
              ∀ x y, b2f ((wiresOf (gs ++ [g]) (oneEach x y)).getD (n + m + gs.length) false) =
                (∑ k : Fin (gs ++ [g]).length,
                  coeff k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) +
                α x + β y + c) := by
      cases hgin : g.inputs with
      | nil =>
        refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
        · intro _
          refine ⟨0, 0, b2f (g.op.eval []), fun x y => by rw [hw_last, hgin]; simp⟩
        · intro _
          refine ⟨0, 0, 0, b2f (g.op.eval []), fun k hk => absurd rfl hk, fun x y => by rw [hw_last, hgin]; simp⟩
      | cons a rest =>
        cases rest with
        | nil =>
          have ha_lt : a < n + m + gs.length := hrb_g a (by simp [hgin])
          have hnl_f : nlGate g = false := by simp [nlGate, hgin]
          obtain ⟨c0, c1, hexp⟩ := gate_eval_expand_one g.op
          refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
          · intro hd0
            rw [hd_last, hgin, hnl_f] at hd0
            have hda0 : ds.getD a 0 = 0 := by
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Bool.toNat_false, add_zero, nat_max_zero] at hd0
              omega
            obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 hda0
            refine ⟨fun x => c1 * αa x, fun y => c1 * βa y, c0 + c1 * ca, fun x y => ?_⟩
            rw [hw_last, hgin]
            simp only [List.map_cons, List.map_nil, hexp, hxa x y]
            ring
          · intro hd1
            rw [hd_last, hgin, hnl_f] at hd1
            have hda1 : ds.getD a 0 ≤ 1 := by
              simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                Bool.toNat_false, add_zero, nat_max_zero] at hd1
              omega
            obtain ⟨cfa, αa, βa, ca, hsupp, hxa⟩ := (hWprev a ha_lt).2 hda1
            let cf : Fin (gs ++ [g]).length → F2 := fun k =>
              if hk : k.val < gs.length then c1 * cfa ⟨k.val, hk⟩ else 0
            refine ⟨cf, fun x => c1 * αa x, fun y => c1 * βa y, c0 + c1 * ca, ?_, ?_⟩
            · intro k hk
              by_cases hlt : k.val < gs.length
              · simp only [cf, dif_pos hlt] at hk
                have hne : cfa ⟨k.val, hlt⟩ ≠ 0 := fun h0 => hk (by simp [h0])
                have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
                  simp [List.getElem_append_left hlt]
                rw [hget]
                exact hsupp ⟨k.val, hlt⟩ hne
              · simp only [cf, dif_neg hlt] at hk; exact absurd rfl hk
            · intro x y
              rw [hw_last, hgin]
              simp only [List.map_cons, List.map_nil, hexp, hxa x y]
              have hsum : (∑ k : Fin (gs ++ [g]).length,
                  cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else (0 : Matrix _ _ F2) x y)) =
                  c1 * ∑ k : Fin gs.length, cfa k * Mprev k x y := by
                have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                rw [Finset.mul_sum]
                let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                have hlast0 : cf (e (Fin.last gs.length)) = 0 := by
                  simp [cf, e]
                rw [hlast0, zero_mul, add_zero]
                refine Finset.sum_congr rfl fun k _ => ?_
                simp only [cf, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
                ring
              rw [hsum]; ring
        | cons b rest2 =>
          cases rest2 with
          | cons _ _ =>
            simp [hgin] at hfan_g
          | nil =>
            have ha_lt : a < n + m + gs.length := hrb_g a (by simp [hgin])
            have hb_lt : b < n + m + gs.length := hrb_g b (by simp [hgin])
            obtain ⟨c0, c1, c2, hexp⟩ := gate_eval_expand_two g.op
            have hq_eq : b2f (xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
                (xor (g.op.eval [true, false]) (g.op.eval [true, true]))) = b2f (nlGate g) := by
              simp [nlGate, hgin]
            by_cases hnl : nlGate g = true
            · -- Nonlinear gate: if depth <= 1 then both inputs have depth 0
              by_cases h0ab : ds.getD a 0 = 0 ∧ ds.getD b 0 = 0
              · obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 h0ab.1
                obtain ⟨αb, βb, cb, hxb⟩ := (hWprev b hb_lt).1 h0ab.2
                let Mlast : Matrix (Fin n) (Fin m) F2 :=
                  Matrix.of fun x y => αa x * βb y + αb x * βa y
                have hMlast_rk : Mlast.rank ≤ 2 := by
                  have h1 : Mlast = Matrix.of (fun x y => αa x * βb y) +
                      Matrix.of (fun x y => αb x * βa y) := by ext x y; simp [Mlast]
                  rw [h1]
                  exact le_trans (rank_add_le _ _)
                    (Nat.add_le_add (rank_vecMulVec_le αa βb) (rank_vecMulVec_le αb βa))
                refine ⟨Mlast, hMlast_rk, ?_, ?_⟩
                · intro hd0
                  rw [hd_last, hnl] at hd0; simp at hd0
                · intro _
                  let cf : Fin (gs ++ [g]).length → F2 := fun k =>
                    if k.val = gs.length then 1 else 0
                  refine ⟨cf,
                    fun x => αa x * αb x + (c1 + cb) * αa x + (c2 + ca) * αb x,
                    fun y => βa y * βb y + (c1 + cb) * βa y + (c2 + ca) * βb y,
                    c0 + c1 * ca + c2 * cb + ca * cb, ?_, ?_⟩
                  · intro k hk
                    have hkeq : k.val = gs.length := by
                      by_contra hne; simp [cf, hne] at hk
                    have hget : (gs ++ [g]).get k = g := by
                      simp [List.getElem_append_right (le_of_eq hkeq.symm), hkeq]
                    rw [hget]; exact hnl
                  · intro x y
                    rw [hw_last, hgin]
                    simp only [List.map_cons, List.map_nil]
                    rw [hexp, hq_eq, hnl, hxa x y, hxb x y]
                    have hb1 : b2f true = 1 := rfl
                    rw [hb1, one_mul]
                    have hsum : (∑ k : Fin (gs ++ [g]).length,
                        cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) =
                        Mlast x y := by
                      have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                      let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                      rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                      have hpref : ∑ k : Fin gs.length,
                          cf (e k.castSucc) * (if hk : (e k.castSucc).val < gs.length then
                            Mprev ⟨(e k.castSucc).val, hk⟩ x y else Mlast x y) = 0 := by
                        refine Finset.sum_eq_zero fun k _ => ?_
                        have hne : (e k.castSucc).val ≠ gs.length := by simp [e]; omega
                        simp [cf, hne]
                      rw [hpref, zero_add]
                      have hnotlt : ¬ (e (Fin.last gs.length)).val < gs.length := by simp [e]
                      have heq : (e (Fin.last gs.length)).val = gs.length := by simp [e]
                      simp [cf, heq, hnotlt]
                    rw [hsum]
                    dsimp only [Mlast, Matrix.of_apply]
                    ring
              · refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
                · intro hd0; rw [hd_last, hnl] at hd0; simp at hd0
                · intro hd1
                  rw [hd_last, hgin, hnl] at hd1
                  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                    Bool.toNat_true, nat_max_zero] at hd1
                  exfalso; apply h0ab; constructor <;> omega
            · -- Linear 2-input gate (`nlGate g = false`)
              have hnlf : nlGate g = false := Bool.eq_false_iff.mpr hnl
              refine ⟨0, by simp [rank_zero_eq], ?_, ?_⟩
              · intro hd0
                rw [hd_last, hgin, hnlf] at hd0
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                  Bool.toNat_false, add_zero, nat_max_zero] at hd0
                have hda0 : ds.getD a 0 = 0 := by omega
                have hdb0 : ds.getD b 0 = 0 := by omega
                obtain ⟨αa, βa, ca, hxa⟩ := (hWprev a ha_lt).1 hda0
                obtain ⟨αb, βb, cb, hxb⟩ := (hWprev b hb_lt).1 hdb0
                refine ⟨fun x => c1 * αa x + c2 * αb x, fun y => c1 * βa y + c2 * βb y,
                  c0 + c1 * ca + c2 * cb, fun x y => ?_⟩
                rw [hw_last, hgin]
                simp only [List.map_cons, List.map_nil]
                rw [hexp, hq_eq, hnlf, hxa x y, hxb x y]
                have hb0 : b2f false = 0 := rfl
                rw [hb0, zero_mul, add_zero]
                ring
              · intro hd1
                rw [hd_last, hgin, hnlf] at hd1
                simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
                  Bool.toNat_false, add_zero, nat_max_zero] at hd1
                have hda1 : ds.getD a 0 ≤ 1 := by omega
                have hdb1 : ds.getD b 0 ≤ 1 := by omega
                obtain ⟨cfa, αa, βa, ca, hsuppa, hxa⟩ := (hWprev a ha_lt).2 hda1
                obtain ⟨cfb, αb, βb, cb, hsuppb, hxb⟩ := (hWprev b hb_lt).2 hdb1
                let cf : Fin (gs ++ [g]).length → F2 := fun k =>
                  if hk : k.val < gs.length then c1 * cfa ⟨k.val, hk⟩ + c2 * cfb ⟨k.val, hk⟩ else 0
                refine ⟨cf, fun x => c1 * αa x + c2 * αb x, fun y => c1 * βa y + c2 * βb y,
                  c0 + c1 * ca + c2 * cb, ?_, ?_⟩
                · intro k hk
                  by_cases hlt : k.val < gs.length
                  · simp only [cf, dif_pos hlt] at hk
                    have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hlt⟩ := by
                      simp [List.getElem_append_left hlt]
                    rw [hget]
                    by_cases ha0 : cfa ⟨k.val, hlt⟩ ≠ 0
                    · exact hsuppa ⟨k.val, hlt⟩ ha0
                    · push_neg at ha0
                      have hb0 : cfb ⟨k.val, hlt⟩ ≠ 0 := fun h0 => hk (by simp [ha0, h0])
                      exact hsuppb ⟨k.val, hlt⟩ hb0
                  · simp only [cf, dif_neg hlt] at hk; exact absurd rfl hk
                · intro x y
                  rw [hw_last, hgin]
                  simp only [List.map_cons, List.map_nil]
                  rw [hexp, hq_eq, hnlf, hxa x y, hxb x y]
                  have hb0 : b2f false = 0 := rfl
                  rw [hb0, zero_mul, add_zero]
                  have hsum : (∑ k : Fin (gs ++ [g]).length,
                      cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else (0 : Matrix _ _ F2) x y)) =
                      c1 * (∑ k : Fin gs.length, cfa k * Mprev k x y) +
                      c2 * (∑ k : Fin gs.length, cfb k * Mprev k x y) := by
                    have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
                    let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
                    rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
                    have hlast0 : cf (e (Fin.last gs.length)) = 0 := by simp [cf, e]
                    rw [hlast0, zero_mul, add_zero, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
                    refine Finset.sum_congr rfl fun k _ => ?_
                    simp only [cf, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
                    ring
                  rw [hsum]; ring
    obtain ⟨Mlast, hMlast_rk, hlast0, hlast1⟩ := hlast_build
    let M : Fin (gs ++ [g]).length → Matrix (Fin n) (Fin m) F2 := fun k =>
      if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ else Mlast
    refine ⟨M, ?_, ?_⟩
    · intro k; dsimp only [M]; split_ifs with hk
      · exact hMrk ⟨k.val, hk⟩
      · exact hMlast_rk
    · intro w hw
      have hlen : (gs ++ [g]).length = gs.length + 1 := by simp
      by_cases hlt : w < n + m + gs.length
      · have hd_old : (depthsOf (n + m) (gs ++ [g])).getD w 0 = ds.getD w 0 := by
          rw [hds_new, depthStep]
          exact getD_append_left ds _ w 0 (by omega)
        have hw_old : ∀ x y, (wiresOf (gs ++ [g]) (oneEach x y)).getD w false =
            (wiresOf gs (oneEach x y)).getD w false := fun x y => by
          rw [hws_new, wireStep]
          exact getD_append_left _ _ w false (by rw [hws_len]; omega)
        constructor
        · intro hd0
          rw [hd_old] at hd0
          obtain ⟨α, β, c, hxy⟩ := (hWprev w hlt).1 hd0
          exact ⟨α, β, c, fun x y => by rw [hw_old]; exact hxy x y⟩
        · intro hd1
          rw [hd_old] at hd1
          obtain ⟨cfprev, α, β, c, hsupp, hxy⟩ := (hWprev w hlt).2 hd1
          let cf : Fin (gs ++ [g]).length → F2 := fun k =>
            if hk : k.val < gs.length then cfprev ⟨k.val, hk⟩ else 0
          refine ⟨cf, α, β, c, ?_, ?_⟩
          · intro k hk
            by_cases hklt : k.val < gs.length
            · simp only [cf, dif_pos hklt] at hk
              have hget : (gs ++ [g]).get k = gs.get ⟨k.val, hklt⟩ := by
                simp [List.getElem_append_left hklt]
              rw [hget]
              exact hsupp ⟨k.val, hklt⟩ hk
            · simp only [cf, dif_neg hklt] at hk; exact absurd rfl hk
          · intro x y
            rw [hw_old, hxy x y]
            have hsum : (∑ k : Fin (gs ++ [g]).length, cf k * M k x y) =
                ∑ k : Fin gs.length, cfprev k * Mprev k x y := by
              let e : Fin (gs.length + 1) ≃ Fin (gs ++ [g]).length := finCongr hlen.symm
              rw [← Equiv.sum_comp e, Fin.sum_univ_castSucc]
              have hlast0 : cf (e (Fin.last gs.length)) = 0 := by simp [cf, e]
              rw [hlast0, zero_mul, add_zero]
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [cf, M, e, finCongr_apply, Fin.val_cast, Fin.val_castSucc, Fin.eta, k.isLt, ↓reduceDIte]
            rw [hsum]
      · have hweq : w = n + m + gs.length := by omega
        subst hweq
        exact ⟨hlast0, fun hd1 => by
          obtain ⟨cf, α, β, c, hsupp, hxy⟩ := hlast1 hd1
          refine ⟨cf, α, β, c, hsupp, fun x y => ?_⟩
          have hsum_eq : (∑ k : Fin (gs ++ [g]).length,
              cf k * (if hk : k.val < gs.length then Mprev ⟨k.val, hk⟩ x y else Mlast x y)) =
              ∑ k : Fin (gs ++ [g]).length, cf k * M k x y :=
            Finset.sum_congr rfl fun k _ => by dsimp only [M]; split_ifs <;> rfl
          rw [hxy x y, hsum_eq]⟩

lemma dd_rank_le {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) (u : Fin n) (v : Fin m) :
    (Matrix.of fun x y => M x y + M x v + M u y + M u v).rank ≤ M.rank := by
  let L : (Fin m → F2) →ₗ[F2] (Fin n → F2) :=
    { toFun := fun w x => M.mulVec w x + M.mulVec w u
      map_add' := fun w1 w2 => by
        ext x; simp only [Matrix.mulVec_add, Pi.add_apply]; ring
      map_smul' := fun r w => by
        ext x; simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let P : (Fin n → F2) →ₗ[F2] (Fin n → F2) :=
    { toFun := fun z x => z x + z u
      map_add' := fun z1 z2 => by ext x; simp; ring
      map_smul' := fun r z => by ext x; simp; ring }
  let D : Matrix (Fin n) (Fin m) F2 := Matrix.of fun x y => M x y + M x v + M u y + M u v
  have hsub : LinearMap.range D.mulVecLin ≤ (LinearMap.range M.mulVecLin).map P := by
    rintro _ ⟨w, rfl⟩
    let w' : Fin m → F2 := fun y => w y + (if y = v then ∑ z : Fin m, w z else 0)
    refine ⟨M.mulVecLin w', ⟨w', rfl⟩, ?_⟩
    ext x
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Matrix.of_apply, D, w']
    have hmul : ∀ a : Fin n, ∑ y : Fin m, M a y * (w y + if y = v then ∑ z, w z else 0) =
        (∑ y, M a y * w y) + M a v * ∑ z, w z := by
      intro a
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
    rw [hmul x, hmul u]
    simp_rw [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  have h1 := Submodule.finrank_mono hsub
  have hmap_eq : (LinearMap.range M.mulVecLin).map P =
      LinearMap.range (P.comp (LinearMap.range M.mulVecLin).subtype) := by
    ext z; simp [Submodule.mem_map]
  have h2 : Module.finrank F2 ((LinearMap.range M.mulVecLin).map P) ≤
      Module.finrank F2 (LinearMap.range M.mulVecLin) := by
    rw [hmap_eq]
    have hrk := LinearMap.finrank_range_add_finrank_ker (P.comp (LinearMap.range M.mulVecLin).subtype)
    omega
  exact le_trans h1 h2

lemma countP_eq_card_filter {α : Type} (l : List α) (p : α → Bool) :
    l.countP p = (Finset.univ.filter (fun k : Fin l.length => p (l.get k) = true)).card := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, ih]
    have hcard : (Finset.univ.filter (fun k : Fin (a :: t).length => p ((a :: t).get k) = true)).card =
        (if p a = true then 1 else 0) +
        (Finset.univ.filter (fun k : Fin t.length => p (t.get k) = true)).card := by
      simp only [Finset.card_filter, List.length_cons, Fin.sum_univ_succ]
      cases hpa : p a <;> simp [hpa]
    rw [hcard]
    cases p a <;> simp <;> omega


def isLinearOK (gs : List Gate) (width : ℕ) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < width + j) ∧
  (∀ g ∈ gs, g.inputs.length ≤ 2)

lemma isLinearOK_append {width : ℕ} {gs1 gs2 : List Gate}
    (h1 : isLinearOK gs1 width) (h2 : isLinearOK gs2 (width + gs1.length)) :
    isLinearOK (gs1 ++ gs2) width := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    by_cases hlt : j < gs1.length
    · rw [getD_append_left gs1 gs2 j _ hlt] at hi
      exact h1.1 j hlt i hi
    · have hge : gs1.length ≤ j := Nat.le_of_not_lt hlt
      have hgd : (gs1 ++ gs2).getD j ⟨GateOp.or, []⟩ = gs2.getD (j - gs1.length) ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
      rw [hgd] at hi
      have hj2 : j - gs1.length < gs2.length := by simp at hj; omega
      have hlt2 := h2.1 (j - gs1.length) hj2 i hi
      omega
  · intro g hg
    simp only [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact h1.2 g hg1
    · exact h2.2 g hg2

-- Append a single XOR of two earlier wires `a, b < base` (2 linear gates: mod 2 then not)
def xor2Gates (base a b : ℕ) : List Gate :=
  [⟨GateOp.mod 2, [a, b]⟩, ⟨GateOp.not, [base]⟩]

lemma xor2Gates_ok (base a b : ℕ) (ha : a < base) (hb : b < base) :
    isLinearOK (xor2Gates base a b) base := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    simp only [xor2Gates, List.length_cons, List.length_nil] at hj
    interval_cases j
    · simp only [xor2Gates, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · simp only [xor2Gates, List.getD_cons_succ, List.getD_cons_zero, List.mem_singleton] at hi
      omega
  · intro g hg
    simp only [xor2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> simp

lemma isLinearOK_eq {gs : List Gate} {w₁ w₂ : ℕ} (h : isLinearOK gs w₁) (heq : w₁ = w₂) :
    isLinearOK gs w₂ := heq ▸ h

lemma nlGate_mod2 (a b : ℕ) : nlGate ⟨GateOp.mod 2, [a, b]⟩ = false := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma nlGate_not (a : ℕ) : nlGate ⟨GateOp.not, [a]⟩ = false := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma nlGate_and2 (a b : ℕ) : nlGate ⟨GateOp.and, [a, b]⟩ = true := by
  simp only [nlGate, List.length_cons, List.length_nil]
  decide

lemma xor2Gates_nl (base a b : ℕ) : (xor2Gates base a b).countP nlGate = 0 := by
  simp [xor2Gates, nlGate_mod2, nlGate_not]

lemma xor2Gates_val (ws : List Bool) (a b : ℕ) :
    b2f (((xor2Gates ws.length a b).foldl wireStep ws).getD (ws.length + 1) false) =
      b2f (ws.getD a false) + b2f (ws.getD b false) := by
  simp only [xor2Gates, List.foldl_cons, List.foldl_nil, wireStep, List.map_cons, List.map_nil]
  let v := (GateOp.mod 2).eval [ws.getD a false, ws.getD b false]
  have hl1 : (ws ++ [v]).length = ws.length + 1 := by simp
  have hget1 : (ws ++ [v]).getD ws.length false = v := getD_append_self ws v false
  have hget2 : ((ws ++ [v]) ++ [GateOp.not.eval [(ws ++ [v]).getD ws.length false]]).getD
      (ws.length + 1) false =
      GateOp.not.eval [(ws ++ [v]).getD ws.length false] := by
    rw [← hl1]; exact getD_append_self (ws ++ [v]) _ false
  rw [hget2, hget1]
  dsimp only [v]
  cases ws.getD a false <;> cases ws.getD b false <;> decide

lemma xor2Gates_depth (ds : List ℕ) (a b : ℕ) (d : ℕ)
    (hda : ds.getD a 0 ≤ d) (hdb : ds.getD b 0 ≤ d) :
    ((xor2Gates ds.length a b).foldl depthStep ds).getD (ds.length + 1) 0 ≤ d := by
  simp only [xor2Gates, List.foldl_cons, List.foldl_nil, depthStep, List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, nlGate_mod2, nlGate_not, Bool.toNat_false, add_zero, nat_max_zero]
  have hl1 : (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).length = ds.length + 1 := by simp
  have hg1 : (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0 =
      max (ds.getD a 0) (ds.getD b 0) := getD_append_self ds _ 0
  have hg2 : ((ds ++ [max (ds.getD a 0) (ds.getD b 0)]) ++
      [(ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0]).getD (ds.length + 1) 0 =
      (ds ++ [max (ds.getD a 0) (ds.getD b 0)]).getD ds.length 0 := by
    rw [← hl1]; exact getD_append_self _ _ 0
  rw [hg2, hg1]
  exact max_le hda hdb

-- XOR a list of existing wires `idxs` (all < base) starting from base; returns (gates, outputWire)
def xorListBuild (base : ℕ) (l : List ℕ) : List Gate × ℕ :=
  match l with
  | [] => ([⟨GateOp.or, []⟩], base)
  | [a] => ([], a)
  | a :: b :: rest =>
    let g1 := xor2Gates base a b
    let mid := base + 1
    let res := xorListBuild (base + 2) (mid :: rest)
    (g1 ++ res.1, res.2)
termination_by l.length

lemma xorListBuild_spec_aux : ∀ (k : ℕ) (idxs : List ℕ), idxs.length = k →
    ∀ base : ℕ, (∀ w ∈ idxs, w < base) →
      let p := xorListBuild base idxs
      isLinearOK p.1 base ∧
      p.1.countP nlGate = 0 ∧
      p.2 < base + p.1.length ∧
      (∀ (ws : List Bool), ws.length = base →
        b2f ((p.1.foldl wireStep ws).getD p.2 false) =
          (idxs.map (fun w => b2f (ws.getD w false))).sum) ∧
      (∀ (ds : List ℕ) (d : ℕ), ds.length = base → (∀ w ∈ idxs, ds.getD w 0 ≤ d) →
        (p.1.foldl depthStep ds).getD p.2 0 ≤ d) := by
  intro k
  induction k with
  | zero =>
    intro idxs hk base _
    have hnil : idxs = [] := List.eq_nil_of_length_eq_zero hk
    subst hnil
    simp only [xorListBuild, List.length_singleton, List.map_nil, List.sum_nil]
    have hnl0 : nlGate ⟨GateOp.or, []⟩ = false := by decide
    refine ⟨⟨?_, ?_⟩, by simp [hnl0], by omega, ?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0; simp at hi
    · intro g hg; simp at hg; subst hg; simp
    · intro ws hlen
      simp only [List.foldl_cons, List.foldl_nil, wireStep, List.map_nil]
      rw [← hlen, getD_append_self]; decide
    · intro ds d hlen _
      simp only [List.foldl_cons, List.foldl_nil, depthStep, hnl0, List.map_nil, List.foldr_nil,
        Bool.toNat_false, add_zero]
      rw [← hlen, getD_append_self]; omega
  | succ k ih =>
    intro idxs hk base hlt
    cases idxs with
    | nil => simp at hk
    | cons a rest =>
      cases rest with
      | nil =>
        have ha : a < base := hlt a (by simp)
        simp only [xorListBuild, List.length_nil, add_zero, List.countP_nil, List.foldl_nil,
          List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        refine ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
          trivial, ha, fun _ _ => trivial, fun ds d _ hd => hd a (by simp)⟩
      | cons b rest2 =>
        have ha : a < base := hlt a (by simp)
        have hb : b < base := hlt b (by simp)
        have hlen2 : ((base + 1) :: rest2).length = k := by simp at hk; simp; omega
        have hrest : ∀ w ∈ (base + 1) :: rest2, w < base + 2 := by
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · omega
          · have := hlt w (by simp [hw2]); omega
        obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := ih ((base + 1) :: rest2) hlen2 (base + 2) hrest
        simp only [xorListBuild]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · have hok1 := xor2Gates_ok base a b ha hb
          have hl : (xor2Gates base a b).length = 2 := rfl
          exact isLinearOK_append hok1 (by simpa [hl] using hok2)
        · rw [List.countP_append, xor2Gates_nl, hnl2]
        · simp only [List.length_append]
          have hl : (xor2Gates base a b).length = 2 := rfl
          omega
        · intro ws hlen
          rw [List.foldl_append]
          let ws1 := (xor2Gates base a b).foldl wireStep ws
          have hlen1 : ws1.length = base + 2 := by
            dsimp only [ws1]; rw [foldl_wireStep_length, hlen]; rfl
          rw [hval2 ws1 hlen1]
          simp only [List.map_cons, List.sum_cons]
          have hmid : b2f (ws1.getD (base + 1) false) = b2f (ws.getD a false) + b2f (ws.getD b false) := by
            dsimp only [ws1]; rw [← hlen]; exact xor2Gates_val ws a b
          have htail : rest2.map (fun w => b2f (ws1.getD w false)) =
              rest2.map (fun w => b2f (ws.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hwlt : w < ws.length := by
              have := hlt w (by simp [hw]); omega
            rw [foldl_wireStep_getD_old ws (xor2Gates base a b) w hwlt]
          rw [hmid, htail, add_assoc]
        · intro ds d hlen hd
          rw [List.foldl_append]
          let ds1 := (xor2Gates base a b).foldl depthStep ds
          have hlen1 : ds1.length = base + 2 := by
            dsimp only [ds1]; rw [foldl_depthStep_length, hlen]; rfl
          refine hdep2 ds1 d hlen1 ?_
          intro w hw
          simp only [List.mem_cons] at hw
          rcases hw with rfl | hw2
          · dsimp only [ds1]; rw [← hlen]
            exact xor2Gates_depth ds a b d (hd a (by simp)) (hd b (by simp))
          · have hwlt : w < ds.length := by
              have := hlt w (by simp [hw2]); omega
            rw [foldl_depthStep_getD_old ds (xor2Gates base a b) w hwlt]
            exact hd w (by simp [hw2])

lemma xorListBuild_spec (idxs : List ℕ) (base : ℕ) (hlt : ∀ w ∈ idxs, w < base) :
    let p := xorListBuild base idxs
    isLinearOK p.1 base ∧
    p.1.countP nlGate = 0 ∧
    p.2 < base + p.1.length ∧
    (∀ (ws : List Bool), ws.length = base →
      b2f ((p.1.foldl wireStep ws).getD p.2 false) =
        (idxs.map (fun w => b2f (ws.getD w false))).sum) ∧
    (∀ (ds : List ℕ) (d : ℕ), ds.length = base → (∀ w ∈ idxs, ds.getD w 0 ≤ d) →
      (p.1.foldl depthStep ds).getD p.2 0 ≤ d) :=
  xorListBuild_spec_aux idxs.length idxs rfl base hlt

lemma sum_filter_nodup_fin {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → Bool) (x : Fin n) :
    ((l.filter p).map (fun i => b2f (decide (x.val = i.val)))).sum =
      if x ∈ l ∧ p x = true then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    by_cases hax : x = a
    · subst hax
      have hxt : x ∉ t := hl.1
      have iht := ih hl.2
      simp only [hxt, false_and, ↓reduceIte] at iht
      cases hpa : p x with
      | false =>
        simp [hpa, iht]
      | true =>
        have hxx : b2f (decide True) = 1 := rfl
        simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons, List.sum_cons, eq_self_iff_true, hxx, iht, add_zero, List.mem_cons, true_or, and_self]
    · have hvne : x.val ≠ a.val := fun h => hax (Fin.ext h)
      have iht := ih hl.2
      cases hpa : p a with
      | false =>
        simp [hpa, iht, hax]
      | true =>
        have hxa : b2f (decide (x.val = a.val)) = 0 := by simp [b2f, hvne]
        simp only [List.filter_cons, hpa, ↓reduceIte, List.map_cons, List.sum_cons, hxa, zero_add,
          iht, List.mem_cons, hax, false_or]

lemma sum_finRange_filter {n : ℕ} (α : Fin n → F2) (x : Fin n) :
    (((List.finRange n).filter (fun i => decide (α i = 1))).map
      (fun i => b2f (decide (x.val = i.val)))).sum = α x := by
  rw [sum_filter_nodup_fin (List.finRange n) (List.nodup_finRange n) _ x]
  have hmem : x ∈ List.finRange n := List.mem_finRange x
  rcases f2_cases (α x) with h0 | h1
  · simp [hmem, h0]
  · simp [hmem, h1]

def affineIdxs (n m base : ℕ) (α : Fin n → F2) (β : Fin m → F2) (c : F2) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (α i = 1))).map Fin.val ++
  ((List.finRange m).filter (fun j => decide (β j = 1))).map (fun j => n + j.val) ++
  (if c = 1 then [base] else [])

def affineBuild (n m base : ℕ) (α : Fin n → F2) (β : Fin m → F2) (c : F2) : List Gate × ℕ :=
  let g0 : List Gate := [⟨GateOp.and, []⟩]
  let res := xorListBuild (base + 1) (affineIdxs n m base α β c)
  (g0 ++ res.1, res.2)

lemma affineBuild_spec (n m base : ℕ) (hbase : n + m ≤ base)
    (α : Fin n → F2) (β : Fin m → F2) (c : F2) :
    let p := affineBuild n m base α β c
    isLinearOK p.1 base ∧
    p.1.countP nlGate = 0 ∧
    p.2 < base + p.1.length ∧
    (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
      ws.length = base →
      (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
      b2f ((p.1.foldl wireStep ws).getD p.2 false) = α x + β y + c) ∧
    (∀ (ds : List ℕ),
      ds.length = base →
      (∀ w < n + m, ds.getD w 0 = 0) →
      (p.1.foldl depthStep ds).getD p.2 0 = 0) := by
  have hidxs_lt : ∀ w ∈ affineIdxs n m base α β c, w < base + 1 := by
    intro w hw
    simp only [affineIdxs, List.mem_append, List.mem_map, List.mem_filter] at hw
    rcases hw with (⟨i, _, rfl⟩ | ⟨j, _, rfl⟩) | hc
    · omega
    · omega
    · split_ifs at hc with h1
      · simp at hc; omega
      · simp at hc
  obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := xorListBuild_spec (affineIdxs n m base α β c) (base + 1) hidxs_lt
  have hok0 : isLinearOK [⟨GateOp.and, []⟩] base := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0; simp at hi
    · intro g hg; simp at hg; subst hg; simp
  have hnl0 : ([⟨GateOp.and, []⟩] : List Gate).countP nlGate = 0 := by
    have h : nlGate ⟨GateOp.and, []⟩ = false := by decide
    simp [h]
  simp only [affineBuild]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact isLinearOK_append hok0 (by simpa using hok2)
  · rw [List.countP_append, hnl0, hnl2]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x y ws hlen hws
    rw [List.foldl_append]
    let ws1 := ([⟨GateOp.and, []⟩] : List Gate).foldl wireStep ws
    have hlen1 : ws1.length = base + 1 := by simp [ws1, wireStep, hlen]
    rw [hval2 ws1 hlen1]
    have hget_old : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := by
      intro w hw
      have h1 := foldl_wireStep_getD_old ws [⟨GateOp.and, []⟩] w (by omega)
      exact h1.trans (hws w hw)
    have hget_base : b2f (ws1.getD base false) = 1 := by
      dsimp only [ws1]
      simp only [List.foldl_cons, List.foldl_nil, wireStep, List.map_nil]
      rw [← hlen, getD_append_self]
      decide
    simp only [affineIdxs, List.map_append, List.sum_append, List.map_map]
    have hsum1 : (((List.finRange n).filter (fun i => decide (α i = 1))).map
        ((fun w => b2f (ws1.getD w false)) ∘ Fin.val)).sum = α x := by
      have hcongr : (((List.finRange n).filter (fun i => decide (α i = 1))).map
          ((fun w => b2f (ws1.getD w false)) ∘ Fin.val)) =
          (((List.finRange n).filter (fun i => decide (α i = 1))).map
          (fun i => b2f (decide (x.val = i.val)))) := by
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp_apply, hget_old i.val (by omega),
          oneEach_getD x y i.val (by omega), i.isLt, ↓reduceDIte]
      rw [hcongr]
      exact sum_finRange_filter α x
    have hsum2 : (((List.finRange m).filter (fun j => decide (β j = 1))).map
        ((fun w => b2f (ws1.getD w false)) ∘ fun j => n + j.val)).sum = β y := by
      have hcongr : (((List.finRange m).filter (fun j => decide (β j = 1))).map
          ((fun w => b2f (ws1.getD w false)) ∘ fun j => n + j.val)) =
          (((List.finRange m).filter (fun j => decide (β j = 1))).map
          (fun j => b2f (decide (y.val = j.val)))) := by
        refine List.map_congr_left fun j _ => ?_
        have hnotlt : ¬ n + j.val < n := by omega
        have hsub : n + j.val - n = j.val := by omega
        simp only [Function.comp_apply, hget_old (n + j.val) (by omega),
          oneEach_getD x y (n + j.val) (by omega), hnotlt, ↓reduceDIte, hsub]
      rw [hcongr]
      exact sum_finRange_filter β y
    have hsum3 : ((if c = 1 then [base] else []).map (fun w => b2f (ws1.getD w false))).sum = c := by
      rcases f2_cases c with rfl | rfl
      · simp
      · simp only [↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
          hget_base]
    rw [hsum1, hsum2, hsum3]
  · intro ds hlen hds
    rw [List.foldl_append]
    let ds1 := ([⟨GateOp.and, []⟩] : List Gate).foldl depthStep ds
    have hlen1 : ds1.length = base + 1 := by simp [ds1, depthStep, hlen]
    have h0 : ((xorListBuild (base + 1) (affineIdxs n m base α β c)).1.foldl depthStep ds1).getD
        (xorListBuild (base + 1) (affineIdxs n m base α β c)).2 0 ≤ 0 := by
      refine hdep2 ds1 0 hlen1 ?_
      intro w hw
      simp only [affineIdxs, List.mem_append, List.mem_map, List.mem_filter] at hw
      rcases hw with (⟨i, _, rfl⟩ | ⟨j, _, rfl⟩) | hc
      · rw [foldl_depthStep_getD_old ds _ i.val (by omega), hds i.val (by omega)]
      · rw [foldl_depthStep_getD_old ds _ (n + j.val) (by omega), hds (n + j.val) (by omega)]
      · split_ifs at hc with h1
        · simp only [List.mem_singleton] at hc
          subst hc
          dsimp only [ds1]
          have hnl_and : nlGate ⟨GateOp.and, []⟩ = false := by decide
          simp only [List.foldl_cons, List.foldl_nil, depthStep, hnl_and, List.map_nil,
            List.foldr_nil, Bool.toNat_false, add_zero]
          rw [← hlen, getD_append_self]
        · simp at hc
    exact Nat.eq_zero_of_le_zero h0

def pairGadget (n m base : ℕ) (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2) : List Gate × ℕ :=
  let a1 := affineBuild n m base p1 q2 0
  let base1 := base + a1.1.length
  let a2 := affineBuild n m base1 p2 q1 0
  let base2 := base1 + a2.1.length
  let gand : Gate := ⟨GateOp.and, [a1.2, a2.2]⟩
  (a1.1 ++ a2.1 ++ [gand], base2)

lemma pairGadget_spec (n m base : ℕ) (hbase : n + m ≤ base)
    (p1 p2 : Fin n → F2) (q1 q2 : Fin m → F2) :
    let g := pairGadget n m base p1 p2 q1 q2
    isLinearOK g.1 base ∧
    g.1.countP nlGate = 1 ∧
    g.2 < base + g.1.length ∧
    (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
      ws.length = base →
      (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
      b2f ((g.1.foldl wireStep ws).getD g.2 false) =
        p1 x * q1 y + p2 x * q2 y + p1 x * p2 x + q1 y * q2 y) ∧
    (∀ (ds : List ℕ),
      ds.length = base →
      (∀ w < n + m, ds.getD w 0 = 0) →
      (g.1.foldl depthStep ds).getD g.2 0 ≤ 1) := by
  dsimp only [pairGadget]
  set a1 := affineBuild n m base p1 q2 0
  set base1 := base + a1.1.length with hbase1
  set a2 := affineBuild n m base1 p2 q1 0
  set base2 := base1 + a2.1.length with hbase2
  set gand : Gate := ⟨GateOp.and, [a1.2, a2.2]⟩
  obtain ⟨hok1, hnl1, hlt1, hval1, hdep1⟩ := affineBuild_spec n m base hbase p1 q2 0
  change isLinearOK a1.1 base at hok1
  change a1.1.countP nlGate = 0 at hnl1
  change a1.2 < base1 at hlt1
  obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := affineBuild_spec n m base1 (by omega) p2 q1 0
  change isLinearOK a2.1 base1 at hok2
  change a2.1.countP nlGate = 0 at hnl2
  change a2.2 < base2 at hlt2
  have hok_and : isLinearOK [gand] base2 := by
    refine ⟨?_, ?_⟩
    · intro j hj i hi
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      simp only [List.getD_cons_zero, gand, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    · intro g hg; simp at hg; subst hg; simp [gand]
  have hnl_and : nlGate gand = true := nlGate_and2 a1.2 a2.2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h12 := isLinearOK_append hok1 hok2
    exact isLinearOK_append h12 (isLinearOK_eq hok_and (by simp [List.length_append, hbase1, hbase2]; omega))
  · simp [List.countP_append, hnl1, hnl2, hnl_and]
  · simp only [List.length_append, List.length_singleton]; omega
  · intro x y ws hlen hws
    rw [List.foldl_append, List.foldl_append]
    let ws1 := a1.1.foldl wireStep ws
    have hlen1 : ws1.length = base1 := by simp [ws1, foldl_wireStep_length, hlen, hbase1]
    have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
      (foldl_wireStep_getD_old ws a1.1 w (by omega)).trans (hws w hw)
    let ws2 := a2.1.foldl wireStep ws1
    have hlen2 : ws2.length = base2 := by simp [ws2, foldl_wireStep_length, hlen1, hbase2]
    have hw1 : b2f (ws2.getD a1.2 false) = p1 x + q2 y := by
      have hold := foldl_wireStep_getD_old ws1 a2.1 a1.2 (by omega)
      rw [hold, hval1 x y ws hlen hws, add_zero]
    have hw2 : b2f (ws2.getD a2.2 false) = p2 x + q1 y := by
      rw [hval2 x y ws1 hlen1 hws1, add_zero]
    simp only [List.foldl_cons, List.foldl_nil, wireStep, gand, List.map_cons, List.map_nil]
    change b2f ((ws2 ++ [GateOp.and.eval [ws2.getD a1.2 false, ws2.getD a2.2 false]]).getD base2 false) = _
    rw [← hlen2, getD_append_self]
    have hand : b2f (GateOp.and.eval [ws2.getD a1.2 false, ws2.getD a2.2 false]) =
        b2f (ws2.getD a1.2 false) * b2f (ws2.getD a2.2 false) := by
      cases ws2.getD a1.2 false <;> cases ws2.getD a2.2 false <;> decide
    rw [hand, hw1, hw2]
    ring
  · intro ds hlen hds
    rw [List.foldl_append, List.foldl_append]
    let ds1 := a1.1.foldl depthStep ds
    have hlen1 : ds1.length = base1 := by simp [ds1, foldl_depthStep_length, hlen, hbase1]
    have hds1 : ∀ w < n + m, ds1.getD w 0 = 0 := fun w hw =>
      (foldl_depthStep_getD_old ds a1.1 w (by omega)).trans (hds w hw)
    let ds2 := a2.1.foldl depthStep ds1
    have hlen2 : ds2.length = base2 := by simp [ds2, foldl_depthStep_length, hlen1, hbase2]
    have hd1 : ds2.getD a1.2 0 = 0 := by
      rw [foldl_depthStep_getD_old ds1 a2.1 a1.2 (by omega), hdep1 ds hlen hds]
    have hd2 : ds2.getD a2.2 0 = 0 := hdep2 ds1 hlen1 hds1
    simp only [List.foldl_cons, List.foldl_nil, depthStep, gand, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, hnl_and, Bool.toNat_true, nat_max_zero]
    change (ds2 ++ [max (ds2.getD a1.2 0) (ds2.getD a2.2 0) + 1]).getD base2 0 ≤ 1
    rw [← hlen2, getD_append_self, hd1, hd2]
    omega

def pairListBuild (n m : ℕ) :
    ℕ → List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2)) → List Gate × List ℕ
  | _, [] => ([], [])
  | base, (p1, p2, q1, q2) :: rest =>
    let g1 := pairGadget n m base p1 p2 q1 q2
    let r := pairListBuild n m (base + g1.1.length) rest
    (g1.1 ++ r.1, g1.2 :: r.2)

lemma pairListBuild_spec (n m : ℕ)
    (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))) :
    ∀ base : ℕ, n + m ≤ base →
      let res := pairListBuild n m base pairs
      isLinearOK res.1 base ∧
      res.1.countP nlGate = pairs.length ∧
      (∀ w ∈ res.2, w < base + res.1.length) ∧
      (∀ (x : Fin n) (y : Fin m) (ws : List Bool),
        ws.length = base →
        (∀ w < n + m, ws.getD w false = (oneEach x y).getD w false) →
        (res.2.map (fun w => b2f ((res.1.foldl wireStep ws).getD w false))).sum =
          (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
          (pairs.map (fun t => t.1 x * t.2.1 x)).sum +
          (pairs.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum) ∧
      (∀ (ds : List ℕ),
        ds.length = base →
        (∀ w < n + m, ds.getD w 0 = 0) →
        ∀ w ∈ res.2, (res.1.foldl depthStep ds).getD w 0 ≤ 1) := by
  induction pairs with
  | nil =>
    intro base _
    simp only [pairListBuild, List.length_nil, List.countP_nil, List.map_nil, List.sum_nil, add_zero]
    exact ⟨⟨fun j hj => absurd hj (Nat.not_lt_zero _), fun _ h => by simp at h⟩,
      trivial, fun _ h => by simp at h, fun _ _ _ _ _ => trivial,
      fun _ _ _ _ h => by simp at h⟩
  | cons hd rest ih =>
    rcases hd with ⟨p1, p2, q1, q2⟩
    intro base hbase
    dsimp only [pairListBuild]
    set g1 := pairGadget n m base p1 p2 q1 q2
    set r := pairListBuild n m (base + g1.1.length) rest
    obtain ⟨hok1, hnl1, hlt1, hval1, hdep1⟩ := pairGadget_spec n m base hbase p1 p2 q1 q2
    change isLinearOK g1.1 base at hok1
    change g1.1.countP nlGate = 1 at hnl1
    change g1.2 < base + g1.1.length at hlt1
    obtain ⟨hok2, hnl2, hlt2, hval2, hdep2⟩ := ih (base + g1.1.length) (by omega)
    change isLinearOK r.1 (base + g1.1.length) at hok2
    change r.1.countP nlGate = rest.length at hnl2
    change ∀ w ∈ r.2, w < base + g1.1.length + r.1.length at hlt2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact isLinearOK_append hok1 hok2
    · rw [List.countP_append, hnl1, hnl2]; simp; omega
    · intro w hw
      simp only [List.mem_cons] at hw
      simp only [List.length_append]
      rcases hw with rfl | hw2
      · omega
      · have := hlt2 w hw2; omega
    · intro x y ws hlen hws
      rw [List.foldl_append]
      let ws1 := g1.1.foldl wireStep ws
      have hlen1 : ws1.length = base + g1.1.length := by simp [ws1, foldl_wireStep_length, hlen]
      have hws1 : ∀ w < n + m, ws1.getD w false = (oneEach x y).getD w false := fun w hw =>
        (foldl_wireStep_getD_old ws g1.1 w (by omega)).trans (hws w hw)
      simp only [List.map_cons, List.sum_cons]
      have hhead : b2f ((r.1.foldl wireStep ws1).getD g1.2 false) =
          p1 x * q1 y + p2 x * q2 y + p1 x * p2 x + q1 y * q2 y := by
        have hlt1' : g1.2 < ws1.length := by rw [hlen1]; exact hlt1
        rw [foldl_wireStep_getD_old ws1 r.1 g1.2 hlt1']
        exact hval1 x y ws hlen hws
      rw [hhead, hval2 x y ws1 hlen1 hws1]
      ring
    · intro ds hlen hds w hw
      rw [List.foldl_append]
      let ds1 := g1.1.foldl depthStep ds
      have hlen1 : ds1.length = base + g1.1.length := by simp [ds1, foldl_depthStep_length, hlen]
      have hds1 : ∀ w < n + m, ds1.getD w 0 = 0 := fun w hw =>
        (foldl_depthStep_getD_old ds g1.1 w (by omega)).trans (hds w hw)
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw2
      · have hlt1' : g1.2 < ds1.length := by rw [hlen1]; exact hlt1
        rw [foldl_depthStep_getD_old ds1 r.1 g1.2 hlt1']
        exact hdep1 ds hlen hds
      · exact hdep2 ds1 hlen1 hds1 w hw2

lemma rankPairs_aux {n m : ℕ} :
    ∀ (r : ℕ) (p : Fin r → Fin n → F2) (q : Fin r → Fin m → F2),
      ∃ (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))),
        pairs.length = (r + 1) / 2 ∧
        ∀ x y, (∑ i : Fin r, p i x * q i y) =
          (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum
  | 0, _, _ => ⟨[], rfl, fun _ _ => by simp⟩
  | 1, p, q =>
    ⟨[(p 0, 0, q 0, 0)], rfl, fun x y => by simp [Fin.sum_univ_one]⟩
  | r + 2, p, q => by
    obtain ⟨pairs', hlen', hsum'⟩ := rankPairs_aux r
      (fun i => p i.castSucc.castSucc) (fun i => q i.castSucc.castSucc)
    refine ⟨(p (Fin.last r).castSucc, p (Fin.last (r + 1)),
        q (Fin.last r).castSucc, q (Fin.last (r + 1))) :: pairs', ?_, ?_⟩
    · simp only [List.length_cons, hlen']; omega
    · intro x y
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [List.map_cons, List.sum_cons, ← hsum' x y]
      ring

lemma rankPairs {n m : ℕ} (M : Matrix (Fin n) (Fin m) F2) :
    ∃ (pairs : List ((Fin n → F2) × (Fin n → F2) × (Fin m → F2) × (Fin m → F2))),
      pairs.length = (M.rank + 1) / 2 ∧
      ∀ x y, M x y = (pairs.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum := by
  obtain ⟨p, q, hM⟩ := rank_decomp M
  obtain ⟨pairs, hlen, hsum⟩ := rankPairs_aux M.rank p q
  exact ⟨pairs, hlen, fun x y => (hM x y).trans (hsum x y)⟩



lemma fits_one_iff_rank {n : ℕ} (G : Fin n → Fin n → Bool) (u v : Fin n) (t : ℕ) :
    let nonlinear := fun (g : Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    (∃ (C : Circuit) (tap : Fin 1 → ℕ),
      ReadsBack (n + n) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
      ∀ j : Fin 1, (depths (n + n) C).getD (tap j) 0 ≤ 1 ∧ Represents G ⟨C.gates, tap j⟩) ↔
    (Matrix.of fun i j : Fin n =>
      (if G i j then (1 : ZMod 2) else 0) + (if G i v then 1 else 0) +
      (if G u j then 1 else 0) + (if G u v then 1 else 0)).rank ≤ 2 * t := by
  intro nonlinear depths
  let X : Matrix (Fin n) (Fin n) F2 := Matrix.of fun x y =>
    b2f (G x y) + b2f (G x v) + b2f (G u y) + b2f (G u v)
  change _ ↔ X.rank ≤ 2 * t
  constructor
  · rintro ⟨C, tap, hrb, hfan, hcnt, htap⟩
    obtain ⟨M, hMrk, hW⟩ := circuit_depth1_decomp n n C.gates hrb hfan
    have htap_rep : ∃ (cf : Fin C.gates.length → F2) (α : Fin n → F2) (β : Fin n → F2) (c : F2),
        (∀ k, cf k ≠ 0 → nlGate (C.gates.get k) = true) ∧
        ∀ x y, b2f (G x y) = (∑ k : Fin C.gates.length, cf k * M k x y) + α x + β y + c := by
      have hrep : ∀ x y, (wiresOf C.gates (oneEach x y)).getD (tap 0) false = G x y :=
        fun x y => (htap 0).2 x y
      by_cases hlt : tap 0 < n + n + C.gates.length
      · obtain ⟨cf, α, β, c, hsupp, hxy⟩ := (hW (tap 0) hlt).2 (htap 0).1
        exact ⟨cf, α, β, c, hsupp, fun x y => by rw [← hrep x y]; exact hxy x y⟩
      · refine ⟨0, 0, 0, 0, fun k hk => absurd rfl hk, fun x y => ?_⟩
        rw [← hrep x y]
        have hge : (wiresOf C.gates (oneEach x y)).length ≤ tap 0 := by
          simp only [wiresOf_length, oneEach, List.length_append, List.length_ofFn]; omega
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge, b2f]
    obtain ⟨cf, α, β, c, hsupp, hG⟩ := htap_rep
    let D : Fin C.gates.length → Matrix (Fin n) (Fin n) F2 := fun k =>
      Matrix.of fun x y => M k x y + M k x v + M k u y + M k u v
    have hDrk : ∀ k, (D k).rank ≤ 2 := fun k => le_trans (dd_rank_le (M k) u v) (hMrk k)
    let Sset : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => cf k = 1)
    let NLset : Finset (Fin C.gates.length) := Finset.univ.filter (fun k => nlGate (C.gates.get k) = true)
    have hXsum : X = ∑ k ∈ Sset, D k := by
      ext x y
      simp only [X, Matrix.of_apply, hG x y, hG x v, hG u y, hG u v, Matrix.sum_apply, D]
      have hsplit : (∑ k : Fin C.gates.length, cf k * (M k x y + M k x v + M k u y + M k u v)) =
          ∑ k ∈ Sset, (M k x y + M k x v + M k u y + M k u v) := by
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun k => cf k = 1)]
        have h0 : ∑ k ∈ Finset.univ.filter (fun k => ¬ cf k = 1),
            cf k * (M k x y + M k x v + M k u y + M k u v) = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hne : cf k ≠ 1 := (Finset.mem_filter.mp hk).2
          rcases f2_cases (cf k) with h0 | h1
          · simp [h0]
          · exact absurd h1 hne
        rw [h0, add_zero]
        refine Finset.sum_congr rfl fun k hk => ?_
        have h1 : cf k = 1 := (Finset.mem_filter.mp hk).2
        simp [h1]
      rw [← hsplit]
      simp_rw [mul_add, Finset.sum_add_distrib]
      have h1 := f2_add_self (α x)
      have h2 := f2_add_self (α u)
      have h3 := f2_add_self (β y)
      have h4 := f2_add_self (β v)
      have h5 := f2_add_self c
      linear_combination h1 + h2 + h3 + h4 + h5 + h5
    have hsub : Sset ⊆ NLset := fun k hk => by
      simp only [Sset, NLset, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hsupp k (by rw [hk]; decide)
    have hcard_le : Sset.card ≤ t := by
      have h1 := Finset.card_le_card hsub
      have h2 : NLset.card = C.gates.countP nlGate := (countP_eq_card_filter C.gates nlGate).symm
      change C.gates.countP nlGate ≤ t at hcnt
      omega
    calc X.rank = (∑ k ∈ Sset, D k).rank := by rw [hXsum]
      _ ≤ ∑ k ∈ Sset, (D k).rank := rank_sum_le Sset D
      _ ≤ ∑ _k ∈ Sset, 2 := Finset.sum_le_sum fun k _ => hDrk k
      _ = 2 * Sset.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * t := by omega
  · intro hrk
    obtain ⟨pairsX, hlenX, hpX⟩ := rankPairs X
    have hplen : pairsX.length ≤ t := by rw [hlenX]; omega
    let bX := pairListBuild n n (n + n) pairsX
    let baseP := n + n + bX.1.length
    have hbaseP : baseP = n + n + bX.1.length := rfl
    obtain ⟨hokX, hnlX, hltX, hvalX, hdepX⟩ := pairListBuild_spec n n pairsX (n + n) (le_refl _)
    change isLinearOK bX.1 (n + n) at hokX
    change bX.1.countP nlGate = pairsX.length at hnlX
    change ∀ w ∈ bX.2, w < baseP at hltX
    let α0 : Fin n → F2 := fun x => b2f (G x v) + (pairsX.map (fun t => t.1 x * t.2.1 x)).sum
    let β0 : Fin n → F2 := fun y => b2f (G u y) + (pairsX.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum
    let c0 : F2 := b2f (G u v)
    let aff0 := affineBuild n n baseP α0 β0 c0
    let baseA0 := baseP + aff0.1.length
    have hbaseA0 : baseA0 = baseP + aff0.1.length := rfl
    let out0 := xorListBuild baseA0 (aff0.2 :: bX.2)
    obtain ⟨hokA0, hnlA0, hltA0, hvalA0, hdepA0⟩ := affineBuild_spec n n baseP (by omega) α0 β0 c0
    change isLinearOK aff0.1 baseP at hokA0
    change aff0.1.countP nlGate = 0 at hnlA0
    change aff0.2 < baseA0 at hltA0
    have hlt_in0 : ∀ w ∈ aff0.2 :: bX.2, w < baseA0 := by
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hwx
      · exact hltA0
      · have := hltX w hwx; omega
    obtain ⟨hokO0, hnlO0, hltO0, hvalO0, hdepO0⟩ := xorListBuild_spec _ baseA0 hlt_in0
    change isLinearOK out0.1 baseA0 at hokO0
    change out0.1.countP nlGate = 0 at hnlO0
    let gs := bX.1 ++ aff0.1 ++ out0.1
    have hokAll : isLinearOK gs (n + n) := by
      have h1 : isLinearOK (bX.1 ++ aff0.1) (n + n) :=
        isLinearOK_append hokX (isLinearOK_eq hokA0 hbaseP.symm)
      exact isLinearOK_append h1 (isLinearOK_eq hokO0 (by simp [List.length_append, hbaseP, hbaseA0]; omega))
    refine ⟨⟨gs, out0.2⟩, fun _ => out0.2, hokAll.1, hokAll.2, ?_, ?_⟩
    · simp only [gs, List.countP_append]
      change bX.1.countP nlGate + aff0.1.countP nlGate + out0.1.countP nlGate ≤ t
      omega
    · intro _
      constructor
      · let ds0 := List.replicate (n + n) 0
        let dsX := bX.1.foldl depthStep ds0
        let dsA0 := aff0.1.foldl depthStep dsX
        have hds0_len : ds0.length = n + n := List.length_replicate
        have hds0_get : ∀ w < n + n, ds0.getD w 0 = 0 := fun w hw => by
          simp [ds0, List.getD_eq_getElem?_getD, hw]
        have hdsX_len : dsX.length = baseP := by simp [dsX, foldl_depthStep_length, hds0_len, hbaseP]
        have hdsX_get : ∀ w < n + n, dsX.getD w 0 = 0 := fun w hw =>
          (foldl_depthStep_getD_old ds0 bX.1 w (by omega)).trans (hds0_get w hw)
        have hdsA0_len : dsA0.length = baseA0 := by simp [dsA0, foldl_depthStep_length, hdsX_len, hbaseA0]
        change (gs.foldl depthStep ds0).getD out0.2 0 ≤ 1
        simp only [gs, List.foldl_append]
        refine hdepO0 dsA0 1 hdsA0_len ?_
        intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hwx
        · rw [hdepA0 dsX hdsX_len hdsX_get]; omega
        · have hw1 := hltX w hwx
          rw [foldl_depthStep_getD_old dsX aff0.1 w (by omega)]
          exact hdepX ds0 hds0_len hds0_get w hwx
      · intro x y
        apply b2f_inj
        change b2f ((gs.foldl wireStep (oneEach x y)).getD out0.2 false) = b2f (G x y)
        let ws0 := oneEach x y
        let wsX := bX.1.foldl wireStep ws0
        let wsA0 := aff0.1.foldl wireStep wsX
        have hws0_len : ws0.length = n + n := by simp [ws0, oneEach]
        have hws0_get : ∀ w < n + n, ws0.getD w false = (oneEach x y).getD w false := fun _ _ => rfl
        have hwsX_len : wsX.length = baseP := by simp [wsX, foldl_wireStep_length, hws0_len, hbaseP]
        have hwsX_get : ∀ w < n + n, wsX.getD w false = (oneEach x y).getD w false := fun w hw =>
          (foldl_wireStep_getD_old ws0 bX.1 w (by omega)).trans (hws0_get w hw)
        have hwsA0_len : wsA0.length = baseA0 := by simp [wsA0, foldl_wireStep_length, hwsX_len, hbaseA0]
        simp only [gs, List.foldl_append]
        change b2f ((out0.1.foldl wireStep wsA0).getD out0.2 false) = b2f (G x y)
        rw [hvalO0 wsA0 hwsA0_len]
        simp only [List.map_cons, List.sum_cons]
        have ha0_v : b2f (wsA0.getD aff0.2 false) = α0 x + β0 y + c0 :=
          hvalA0 x y wsX hwsX_len hwsX_get
        have hX_v : (bX.2.map (fun w => b2f (wsA0.getD w false))).sum =
            (pairsX.map (fun t => t.1 x * t.2.2.1 y + t.2.1 x * t.2.2.2 y)).sum +
            (pairsX.map (fun t => t.1 x * t.2.1 x)).sum +
            (pairsX.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum := by
          have hcongr : bX.2.map (fun w => b2f (wsA0.getD w false)) =
              bX.2.map (fun w => b2f (wsX.getD w false)) := by
            refine List.map_congr_left fun w hw => ?_
            have hw1 := hltX w hw
            rw [foldl_wireStep_getD_old wsX aff0.1 w (by omega)]
          rw [hcongr]
          exact hvalX x y ws0 hws0_len hws0_get
        rw [ha0_v, hX_v]
        have hXp := hpX x y
        have hXx : X x y = b2f (G x y) + b2f (G x v) + b2f (G u y) + b2f (G u v) := rfl
        dsimp only [α0, β0, c0]
        have h1 := f2_add_self (b2f (G x v))
        have h2 := f2_add_self (b2f (G u y))
        have h3 := f2_add_self (b2f (G u v))
        have h4 := f2_add_self ((pairsX.map (fun t => t.1 x * t.2.1 x)).sum)
        have h5 := f2_add_self ((pairsX.map (fun t => t.2.2.1 y * t.2.2.2 y)).sum)
        linear_combination hXx - hXp + h1 + h2 + h3 + h4 + h5

lemma galoisField_finrank (h : ℕ) (hh : 0 < h) :
    Module.finrank (ZMod 2) (GaloisField 2 h) = h := by
  letI : Fintype (GaloisField 2 h) := Fintype.ofFinite (GaloisField 2 h)
  have hcard : Fintype.card (GaloisField 2 h) = 2 ^ h := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 h (by omega)
  have hpow : Fintype.card (GaloisField 2 h) =
      (Fintype.card (ZMod 2)) ^ Module.finrank (ZMod 2) (GaloisField 2 h) :=
    Module.card_eq_pow_finrank (K := ZMod 2) (V := GaloisField 2 h)
  rw [hcard, ZMod.card 2] at hpow
  exact (Nat.pow_right_injective (by norm_num : 1 < 2) hpow).symm

lemma rank_bilinear_eq {h m : ℕ} (hh : 0 < h)
    {K : Type} [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K] [FiniteDimensional (GaloisField 2 h) K]
    (basis : Module.Basis (Fin (h * m)) (ZMod 2) K) (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0)
    (D : K →ₗ[GaloisField 2 h] K) :
    let point : Fin (h * m + 1) → K := Fin.cases 0 basis
    (Matrix.of fun x y : Fin (h * m + 1) => bit (D (point x) * point y)).rank =
      h * Module.finrank (GaloisField 2 h) (LinearMap.range D) := by
  intro point
  let F := ZMod 2
  let E := GaloisField 2 h
  let M : Matrix (Fin (h * m + 1)) (Fin (h * m + 1)) F :=
    Matrix.of fun x y => bit (D (point x) * point y)
  let Φ : (Fin (h * m + 1) → F) →ₗ[F] K :=
    { toFun := fun v => ∑ x : Fin (h * m + 1), v x • point x
      map_add' := fun v₁ v₂ => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r v => by simp [mul_smul, Finset.smul_sum] }
  let T : K →ₗ[F] (Fin (h * m + 1) → F) :=
    { toFun := fun u y => bit (u * point y)
      map_add' := fun u₁ u₂ => by ext y; simp [add_mul, map_add]
      map_smul' := fun r u => by ext y; simp [smul_mul_assoc, map_smul] }
  have hΦ_surj : Function.Surjective Φ := by
    intro w
    refine ⟨Fin.cases 0 (basis.repr w), ?_⟩
    dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ, zero_smul, zero_add, point]
    exact basis.sum_repr w
  have hT_inj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hu0
    have hex : ∃ w : K, bit w ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hbit (LinearMap.ext fun w => by simp [hall w])
    obtain ⟨w, hw⟩ := hex
    have hrep := basis.sum_repr (u⁻¹ * w)
    have hbw : bit w = ∑ i : Fin (h * m), basis.repr (u⁻¹ * w) i * bit (u * basis i) := by
      have hw_eq : w = u * (u⁻¹ * w) := by field_simp [hu0]
      conv_lhs => rw [hw_eq, ← hrep]
      rw [Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, map_smul, smul_eq_mul]
    have hzero : ∀ i : Fin (h * m), bit (u * basis i) = 0 := fun i => by
      have hi := congrFun hu i.succ
      simpa [T, point] using hi
    simp only [hzero, mul_zero, Finset.sum_const_zero] at hbw
    exact hw hbw
  have hfactor : M.transpose.mulVecLin = T.comp ((D.restrictScalars F).comp Φ) := by
    ext v y
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.of_apply, M, LinearMap.comp_apply, T, Φ, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.restrictScalars_apply]
    rw [map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [LinearMap.map_smul_of_tower, smul_mul_assoc, map_smul, smul_eq_mul, mul_comm]
  have hrange : LinearMap.range M.transpose.mulVecLin = (LinearMap.range (D.restrictScalars F)).map T := by
    rw [hfactor, LinearMap.range_comp, LinearMap.range_comp, LinearMap.range_eq_top.mpr hΦ_surj,
      Submodule.map_top]
  have hrk_F : M.rank = Module.finrank F (LinearMap.range (D.restrictScalars F)) := by
    rw [← Matrix.rank_transpose M]
    change Module.finrank F (LinearMap.range M.transpose.mulVecLin) = _
    rw [hrange]
    exact (Submodule.equivMapOfInjective T hT_inj _).finrank_eq.symm
  have hsub_eq : Module.finrank F (LinearMap.range (D.restrictScalars F)) =
      Module.finrank F (LinearMap.range D) := by
    let eR : LinearMap.range (D.restrictScalars F) ≃ₗ[F] LinearMap.range D :=
      { toFun := fun x => ⟨x.1, x.2⟩
        invFun := fun x => ⟨x.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact eR.finrank_eq
  rw [hrk_F, hsub_eq]
  have htower := Module.finrank_mul_finrank F E (LinearMap.range D)
  rw [galoisField_finrank h hh] at htower
  exact htower.symm

lemma poly_det_of_linearMap {m : ℕ} {E : Type} [Field E]
    {K : Type} [Field K] [Algebra E K] [FiniteDimensional E K]
    (bK : Module.Basis (Fin m) E K) (C : K →ₗ[E] K) :
    ∃ P : MvPolynomial (Fin m) E,
      P.totalDegree ≤ Module.finrank E (LinearMap.range C) ∧
      MvPolynomial.eval 0 P = 1 ∧
      ∀ z : K, z ≠ 0 → (∃ v : K, v ≠ 0 ∧ C v = z * v) →
        MvPolynomial.eval (bK.repr z⁻¹) P = 0 := by
  set r := Module.finrank E (LinearMap.range C)
  let bR : Module.Basis (Fin r) E (LinearMap.range C) := Module.finBasis E (LinearMap.range C)
  let lam : Fin r → (K →ₗ[E] E) := fun a =>
    (Finsupp.lapply a).comp (bR.repr.toLinearMap.comp C.rangeRestrict)
  let w : Fin r → K := fun a => (bR a).1
  have hC_decomp : ∀ v : K, C v = ∑ a : Fin r, lam a v • w a := by
    intro v
    have h1 := bR.sum_repr (C.rangeRestrict v)
    have h2 : (∑ a : Fin r, bR.repr (C.rangeRestrict v) a • (bR a).1) = C v := by
      have hsub := congrArg Subtype.val h1
      simp only [Submodule.coe_sum, SetLike.val_smul] at hsub
      exact hsub
    exact h2.symm
  let A : Matrix (Fin r) (Fin r) (MvPolynomial (Fin m) E) :=
    Matrix.of fun a b =>
      (if a = b then 1 else 0) -
        ∑ j : Fin m, MvPolynomial.C (lam a (bK j * w b)) * MvPolynomial.X j
  let P : MvPolynomial (Fin m) E := A.det
  have hA_deg : ∀ a b : Fin r, (A a b).totalDegree ≤ 1 := by
    intro a b
    dsimp only [A, Matrix.of_apply]
    refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
    · split_ifs
      · simp
      · simp
    · refine le_trans (totalDegree_sum_le _ _) (Finset.sup_le fun j _ => ?_)
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      simp [MvPolynomial.totalDegree_X]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- totalDegree P <= r
    dsimp only [P]
    rw [Matrix.det_apply]
    refine le_trans (totalDegree_sum_le _ _) (Finset.sup_le fun σ _ => ?_)
    have hsign_deg : ∀ (q : MvPolynomial (Fin m) E), (Equiv.Perm.sign σ • q).totalDegree ≤ q.totalDegree := by
      intro q
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
      · simp [h1]
      · simp [h1, MvPolynomial.totalDegree_neg]
    refine le_trans (hsign_deg _) ?_
    refine le_trans (totalDegree_prod_le _ _) ?_
    calc ∑ a : Fin r, (A (σ a) a).totalDegree
        ≤ ∑ _a : Fin r, 1 := Finset.sum_le_sum fun a _ => hA_deg (σ a) a
      _ = r := by simp
  · -- eval 0 P = 1
    dsimp only [P]
    rw [RingHom.map_det]
    have hmat : (MvPolynomial.eval (0 : Fin m → E)).mapMatrix A = (1 : Matrix (Fin r) (Fin r) E) := by
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, A, Matrix.of_apply, map_sub, map_sum,
        map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Pi.zero_apply, mul_zero,
        Finset.sum_const_zero, sub_zero, Matrix.one_apply]
      split_ifs <;> simp
    rw [hmat, Matrix.det_one]
  · -- eval (bK.repr z⁻¹) P = 0 when z != 0 and C v = z * v for v != 0
    intro z hz ⟨v, hv, hCv⟩
    let u := z⁻¹
    let c : Fin r → E := fun a => lam a v
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hCv0 : C v = 0 := by
        rw [hC_decomp v]
        exact Finset.sum_eq_zero fun a _ => by
          have : lam a v = 0 := congrFun hc0 a
          simp [this]
      have hzv0 : z * v = 0 := hCv.symm.trans hCv0
      exact (mul_ne_zero hz hv) hzv0
    let M : Matrix (Fin r) (Fin r) E := (MvPolynomial.eval (bK.repr u)).mapMatrix A
    have hM_mul : M.mulVec c = 0 := by
      ext a
      have hv_eq : v = ∑ b : Fin r, c b • (u * w b) := by
        have h1 : v = u * C v := by
          dsimp only [u]; rw [hCv, ← mul_assoc, inv_mul_cancel₀ hz, one_mul]
        rw [h1, hC_decomp v, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mul_smul_comm]
      have hlam_v : lam a v = ∑ b : Fin r, c b * lam a (u * w b) := by
        conv_lhs => rw [hv_eq]
        rw [map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [map_smul, smul_eq_mul]
      have hu_rep : ∀ b : Fin r, lam a (u * w b) = ∑ j : Fin m, bK.repr u j * lam a (bK j * w b) := by
        intro b
        have hu := bK.sum_repr u
        conv_lhs => rw [← hu, Finset.sum_mul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul]
      simp only [Matrix.mulVec, dotProduct, M, RingHom.mapMatrix_apply, Matrix.map_apply,
        A, Matrix.of_apply, map_sub, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        Pi.zero_apply]
      have hsum_eq : ∑ b : Fin r, ((MvPolynomial.eval (bK.repr u)) (if a = b then 1 else 0) -
          ∑ j : Fin m, lam a (bK j * w b) * bK.repr u j) * c b =
          c a - ∑ b : Fin r, c b * lam a (u * w b) := by
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        congr 1
        · have hite : ∀ b : Fin r, (MvPolynomial.eval (bK.repr u)) (if a = b then (1 : MvPolynomial (Fin m) E) else 0) * c b =
              if b = a then c b else 0 := by
            intro b
            by_cases hab : a = b
            · subst hab; simp
            · have hba : b ≠ a := Ne.symm hab
              simp [hab, hba]
          simp only [hite, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        · refine Finset.sum_congr rfl fun b _ => ?_
          rw [hu_rep b, mul_comm]
          congr 1
          refine Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [hsum_eq]
      dsimp only [c]
      rw [← hlam_v, sub_self]
    have hdet0 : M.det = 0 := by
      by_contra hdet_ne
      have hne : M.mulVec c ≠ 0 := by
        intro h0
        have hu_det : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet_ne
        have h1 := congrArg (fun vec => M⁻¹.mulVec vec) h0
        simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu_det, Matrix.one_mulVec,
          Matrix.mulVec_zero] at h1
        exact hc_ne h1
      exact hne hM_mul
    dsimp only [P]
    rw [RingHom.map_det]
    exact hdet0

lemma main_proof (h m t budget : ℕ) (hh : 0 < h) (hm_pos : 0 < m)
    (hk1 : h * m - h ≤ 2 * t) (hk2 : 2 * t < h * m)
    (K : Type) [Field K] [Algebra (ZMod 2) K] [Algebra (GaloisField 2 h) K]
    [IsScalarTower (ZMod 2) (GaloisField 2 h) K] [FiniteDimensional (GaloisField 2 h) K]
    (hm : Module.finrank (GaloisField 2 h) K = m)
    (basis : Module.Basis (Fin (h * m)) (ZMod 2) K)
    (bit : K →ₗ[ZMod 2] ZMod 2) (hbit : bit ≠ 0) :
    let nonlinear := fun (g : Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    let fits := fun (n m' q' : ℕ) (G : Fin q' → Fin n → Fin m' → Bool) (t' : ℕ) =>
      ∃ (C : Circuit) (tap : Fin q' → ℕ),
        ReadsBack (n + m') C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t' ∧
        ∀ j : Fin q', (depths (n + m') C).getD (tap j) 0 ≤ 1 ∧
          Represents (G j) ⟨C.gates, tap j⟩
    let E := GaloisField 2 h
    let q := 2 ^ h
    let n := h * m + 1
    let point : Fin n → K := Fin.cases 0 basis
    let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
    let table := fun (C : K →ₗ[E] K) (x y : Fin n) => decide (bit (C (point x) * point y) ≠ 0)
    let serves := fun (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K) =>
      ∀ z ∈ S, ∃ i : Fin l,
        fits n n 1 (fun _ x y => xor (mult z x y) (table (C i) x y)) t
    let rk := fun (D : K →ₗ[E] K) => Module.finrank E (LinearMap.range D)
    let c := min budget (m * (q - 1))
    let a := c / (q - 1)
    let b := c % (q - 1)
    let left := q ^ (m - a) - b * q ^ (m - a - 1)
    (∀ (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K),
      (0 : K) ∉ S → (∑ i : Fin l, rk (C i)) ≤ budget → serves l C S →
      S.card + left ≤ q ^ m) ∧
    (∃ (C : Fin c → (K →ₗ[E] K)) (S : Finset K),
      (0 : K) ∉ S ∧
      (∀ i : Fin c, rk (C i) = 1 ∧ fits n n 1 (fun _ => table (C i)) ((h + 1) / 2)) ∧
      serves c C S ∧ S.card + left = q ^ m) := by
  intro nonlinear depths fits E q n point mult table serves rk c a b left
  letI : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = q := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 h (by omega)
  have hq2 : 2 ≤ q := by
    have : 2 ^ 1 ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
    omega
  let bK : Module.Basis (Fin m) E K := Module.finBasisOfFinrankEq E K hm
  -- Equivalence of `fits` with E-kernel non-triviality
  have hfits_table : ∀ (D : K →ₗ[E] K) (t' : ℕ),
      fits n n 1 (fun _ => table D) t' ↔ h * rk D ≤ 2 * t' := by
    intro D t'
    have h1 := fits_one_iff_rank (table D) 0 0 t'
    dsimp only at h1
    have hmat : (Matrix.of fun x y : Fin n =>
        (if table D x y then (1 : ZMod 2) else 0) + (if table D x 0 then 1 else 0) +
        (if table D 0 y then 1 else 0) + (if table D 0 0 then 1 else 0)) =
        Matrix.of fun x y : Fin n => bit (D (point x) * point y) := by
      ext x y
      simp only [Matrix.of_apply, table, point, Fin.cases_zero, map_zero, zero_mul, mul_zero,
        ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      exact zmod2_ite_ne_zero (bit (D (point x) * point y))
    rw [hmat, rank_bilinear_eq hh basis bit hbit D] at h1
    exact h1
  have hfits_diff : ∀ (z : K) (D : K →ₗ[E] K),
      fits n n 1 (fun _ x y => xor (mult z x y) (table D x y)) t ↔
        ∃ v : K, v ≠ 0 ∧ D v = z * v := by
    intro z D
    let Lz : K →ₗ[E] K := LinearMap.mulLeft E z
    let Dz : K →ₗ[E] K := Lz + D
    have h1 := fits_one_iff_rank (fun x y => xor (mult z x y) (table D x y)) 0 0 t
    dsimp only at h1
    have hmat : (Matrix.of fun x y : Fin n =>
        (if xor (mult z x y) (table D x y) then (1 : ZMod 2) else 0) +
        (if xor (mult z x 0) (table D x 0) then 1 else 0) +
        (if xor (mult z 0 y) (table D 0 y) then 1 else 0) +
        (if xor (mult z 0 0) (table D 0 0) then 1 else 0)) =
        Matrix.of fun x y : Fin n => bit (Dz (point x) * point y) := by
      ext x y
      simp only [Matrix.of_apply, mult, table, point, Fin.cases_zero, map_zero, zero_mul, mul_zero,
        ne_eq, not_true_eq_false, decide_false, Bool.xor_false, Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [zmod2_xor_decide]
      simp [Dz, Lz, add_mul, map_add]
    rw [hmat, rank_bilinear_eq hh basis bit hbit Dz] at h1
    dsimp only [fits]
    rw [h1]
    have hchar2 : ∀ x : K, x + x = 0 := by
      intro x
      have h2 : algebraMap (ZMod 2) K (2 : ZMod 2) = 0 := by
        have h0 : (2 : ZMod 2) = 0 := rfl
        rw [h0, map_zero]
      have h2' : (2 : K) = 0 := by
        simpa [map_ofNat] using h2
      calc x + x = 2 * x := (two_mul x).symm
        _ = 0 := by rw [h2', zero_mul]
    have hrk_lt : h * rk Dz ≤ 2 * t ↔ rk Dz < m := by
      constructor
      · intro hle
        by_contra hge
        push_neg at hge
        have : h * m ≤ h * rk Dz := Nat.mul_le_mul_left h hge
        omega
      · intro hlt
        have hle : rk Dz ≤ m - 1 := by omega
        have : h * rk Dz ≤ h * (m - 1) := Nat.mul_le_mul_left h hle
        have hsub : h * (m - 1) = h * m - h := by rw [Nat.mul_sub_left_distrib, mul_one]
        omega
    rw [hrk_lt]
    have hrn := LinearMap.finrank_range_add_finrank_ker Dz
    rw [hm] at hrn
    change rk Dz + Module.finrank E (LinearMap.ker Dz) = m at hrn
    constructor
    · intro hlt
      have hker_pos : 0 < Module.finrank E (LinearMap.ker Dz) := by omega
      have hker_ne : LinearMap.ker Dz ≠ ⊥ := fun hbot => by
        rw [hbot, finrank_bot] at hker_pos; omega
      obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
      refine ⟨v, hv_ne, ?_⟩
      have h0 : z * v + D v = 0 := by simpa [Dz, Lz] using hv_mem
      have h2 := hchar2 (z * v)
      calc D v = (z * v + z * v) + D v := by rw [h2, zero_add]
        _ = z * v + (z * v + D v) := add_assoc _ _ _
        _ = z * v := by rw [h0, add_zero]
    · rintro ⟨v, hv_ne, hDv⟩
      have hv_mem : v ∈ LinearMap.ker Dz := by
        change z * v + D v = 0
        rw [hDv]
        exact hchar2 (z * v)
      have hker_ne : LinearMap.ker Dz ≠ ⊥ := fun hbot => hv_ne (by rw [hbot, Submodule.mem_bot] at hv_mem; exact hv_mem)
      have hker_pos : 0 < Module.finrank E (LinearMap.ker Dz) := by
        by_contra h0
        have heq0 : Module.finrank E (LinearMap.ker Dz) = 0 := by omega
        exact hker_ne (Submodule.finrank_eq_zero.mp heq0)
      omega
  constructor
  · -- Part A: Upper bound on S.card
    intro l C S h0S hsum_rk hserv
    have hP_each : ∀ i : Fin l, ∃ P : MvPolynomial (Fin m) E,
        P.totalDegree ≤ rk (C i) ∧
        MvPolynomial.eval 0 P = 1 ∧
        ∀ z : K, z ≠ 0 → (∃ v : K, v ≠ 0 ∧ C i v = z * v) →
          MvPolynomial.eval (bK.repr z⁻¹) P = 0 :=
      fun i => poly_det_of_linearMap bK (C i)
    choose Pi hPi_deg hPi_0 hPi_root using hP_each
    let P : MvPolynomial (Fin m) E := ∏ i : Fin l, Pi i
    have hP_deg : P.totalDegree ≤ budget := by
      calc P.totalDegree ≤ ∑ i : Fin l, (Pi i).totalDegree := totalDegree_prod_le _ _
        _ ≤ ∑ i : Fin l, rk (C i) := Finset.sum_le_sum fun i _ => hPi_deg i
        _ ≤ budget := hsum_rk
    have hP_0 : MvPolynomial.eval 0 P = 1 := by
      dsimp only [P]
      rw [map_prod]
      exact Finset.prod_eq_one fun i _ => hPi_0 i
    let Q := reducePoly P
    have hQ_0 : MvPolynomial.eval 0 Q = 1 := by rw [eval_reducePoly, hP_0]
    have hQ_ne : Q ≠ 0 := fun h0 => by rw [h0, map_zero] at hQ_0; exact zero_ne_one hQ_0
    have hQ_deg : Q.totalDegree ≤ budget := le_trans (totalDegree_reducePoly_le P) hP_deg
    have hQ_degOf : ∀ j : Fin m, Q.degreeOf j ≤ Fintype.card E - 1 := degreeOf_reducePoly_le P
    have hRM := reed_muller_nonzeros m budget Q hQ_ne hQ_deg hQ_degOf
    have hrm_eq : rmBound (Fintype.card E) m budget = left := by
      simp only [rmBound, hcardE, left, c, a, b]
    rw [hrm_eq] at hRM
    -- Map S injectively into the zero set of Q on Fin m -> E
    have hS_zeros : S.card ≤ (Finset.univ.filter (fun x : Fin m → E => MvPolynomial.eval x Q = 0)).card := by
      refine Finset.card_le_card_of_injOn (fun z => (bK.repr z⁻¹ : Fin m → E)) ?_ ?_
      · intro z hz
        have hz0 : z ≠ 0 := fun h => h0S (h ▸ hz)
        obtain ⟨i, hi⟩ := hserv z hz
        have hv := (hfits_diff z (C i)).mp hi
        have hroot_i := hPi_root i z hz0 hv
        have hroot_P : MvPolynomial.eval (bK.repr z⁻¹) P = 0 := by
          dsimp only [P]
          rw [map_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ i) hroot_i
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Q, eval_reducePoly]
        exact hroot_P
      · intro z₁ _ z₂ _ heq
        have hinv : z₁⁻¹ = z₂⁻¹ := bK.repr.injective (Finsupp.ext (congrFun heq))
        exact inv_injective hinv
    have hsplit := card_filter_add_not
      (Finset.univ : Finset (Fin m → E)) (fun x : Fin m → E => MvPolynomial.eval x Q = 0)
    have hcard_ne_eq : (Finset.univ.filter (fun x : Fin m → E => ¬ MvPolynomial.eval x Q = 0)).card =
        (Finset.univ.filter (fun x : Fin m → E => MvPolynomial.eval x Q ≠ 0)).card := rfl
    have hcard_univ : (Finset.univ : Finset (Fin m → E)).card = q ^ m := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcardE]
    rw [hcard_ne_eq, hcard_univ] at hsplit
    omega
  · -- Part B: Tight construction achieving S.card + left = q ^ m
    have hq1_pos : 0 < q - 1 := by omega
    have hcard_nz : Fintype.card {α : E // α ≠ 0} = q - 1 := by
      rw [Fintype.card_subtype]
      have heq : Finset.univ.filter (fun α : E => α ≠ 0) = Finset.univ.erase (0 : E) := by
        ext α; simp [ne_comm]
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hcardE]
    let eNz : Fin (q - 1) ≃ {α : E // α ≠ 0} := (Fintype.equivFinOfCardEq hcard_nz).symm
    have hc_le : c ≤ m * (q - 1) := min_le_right _ _
    let coordIdx : Fin c → Fin m := fun i =>
      ⟨i.val / (q - 1), (Nat.div_lt_iff_lt_mul hq1_pos).mpr (lt_of_lt_of_le i.isLt hc_le)⟩
    let valIdx : Fin c → E := fun i => (eNz ⟨i.val % (q - 1), Nat.mod_lt _ hq1_pos⟩).1
    have hval_ne : ∀ i : Fin c, valIdx i ≠ 0 := fun i => (eNz _).2
    let C : Fin c → (K →ₗ[E] K) := fun i =>
      { toFun := fun v => ((valIdx i)⁻¹ * bK.repr v (coordIdx i)) • (1 : K)
        map_add' := fun v₁ v₂ => by simp [mul_add, add_smul]
        map_smul' := fun s v => by simp [smul_smul]; ring_nf }
    let badX : Finset (Fin m → E) := Finset.univ.filter (fun x =>
      ∀ i : Fin c, x (coordIdx i) ≠ valIdx i)
    let S : Finset K := (Finset.univ.filter (fun x : Fin m → E =>
      ∃ i : Fin c, x (coordIdx i) = valIdx i)).image (fun x => (bK.repr.symm (Finsupp.equivFunOnFinite.symm x))⁻¹)
    refine ⟨C, S, ?_, ?_, ?_, ?_⟩
    · -- 0 notin S
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
      intro x ⟨i, hi⟩ hzero
      have hinv0 : bK.repr.symm (Finsupp.equivFunOnFinite.symm x) = 0 := inv_eq_zero.mp hzero
      have hx0 : x = 0 := by
        have h1 := congrArg bK.repr hinv0
        simp only [LinearEquiv.apply_symm_apply, map_zero] at h1
        ext j
        have := congrArg (fun f : Fin m →₀ E => f j) h1
        simpa using this
      rw [hx0] at hi
      exact hval_ne i hi.symm
    · -- rk (C i) = 1 and fits table (C i) ((h+1)/2)
      intro i
      have hrk1 : rk (C i) = 1 := by
        have hsub : LinearMap.range (C i) = Submodule.span E ({(1 : K)} : Set K) := by
          apply le_antisymm
          · rintro _ ⟨v, rfl⟩
            exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton 1))
          · rw [Submodule.span_singleton_le_iff_mem]
            refine ⟨valIdx i • bK (coordIdx i), ?_⟩
            simp only [C, LinearMap.coe_mk, AddHom.coe_mk, map_smul, bK.repr_self,
              Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
            rw [smul_smul, mul_inv_cancel₀ (hval_ne i), one_smul]
        dsimp only [rk]
        rw [hsub, finrank_span_singleton (one_ne_zero : (1 : K) ≠ 0)]
      refine ⟨hrk1, ?_⟩
      rw [hfits_table (C i) ((h + 1) / 2), hrk1, mul_one]
      omega
    · -- serves c C S
      intro z hz
      simp only [S, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      obtain ⟨x, ⟨i, hi⟩, rfl⟩ := hz
      refine ⟨i, (hfits_diff _ (C i)).mpr ?_⟩
      set u := bK.repr.symm (Finsupp.equivFunOnFinite.symm x)
      have hu_ne : u ≠ 0 := by
        intro hu0
        have hx0 : x (coordIdx i) = 0 := by
          have h1 := congrArg (fun v => bK.repr v (coordIdx i)) hu0
          simpa [u] using h1
        exact hval_ne i (hi.symm.trans hx0)
      refine ⟨u, hu_ne, ?_⟩
      have hrepr : bK.repr u (coordIdx i) = valIdx i := by
        have h1 : bK.repr u (coordIdx i) = x (coordIdx i) := by simp [u]
        exact h1.trans hi
      simp only [C, LinearMap.coe_mk, AddHom.coe_mk, hrepr, inv_mul_cancel₀ (hval_ne i), one_smul]
      exact (inv_mul_cancel₀ hu_ne).symm
    · -- S.card + left = q ^ m
      have hS_card : S.card = (Finset.univ.filter (fun x : Fin m → E =>
          ∃ i : Fin c, x (coordIdx i) = valIdx i)).card := by
        refine Finset.card_image_of_injective _ ?_
        intro x₁ x₂ h
        have h1 := inv_injective h
        have h2 := bK.repr.symm.injective h1
        exact Finsupp.equivFunOnFinite.symm.injective h2
      have hsplit : (Finset.univ.filter (fun x : Fin m → E => ∃ i : Fin c, x (coordIdx i) = valIdx i)).card +
          badX.card = (Finset.univ : Finset (Fin m → E)).card := by
        have hdisj : Disjoint (Finset.univ.filter (fun x : Fin m → E => ∃ i : Fin c, x (coordIdx i) = valIdx i)) badX := by
          rw [Finset.disjoint_left]; intro x h1 h2
          obtain ⟨i, hi⟩ := (Finset.mem_filter.mp h1).2
          exact (Finset.mem_filter.mp h2).2 i hi
        have hunion : Finset.univ.filter (fun x : Fin m → E => ∃ i : Fin c, x (coordIdx i) = valIdx i) ∪ badX = Finset.univ := by
          ext x
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, badX]
          by_cases h : ∃ i : Fin c, x (coordIdx i) = valIdx i
          · exact ⟨fun _ => trivial, fun _ => Or.inl h⟩
          · exact ⟨fun _ => trivial, fun _ => Or.inr fun i hi => h ⟨i, hi⟩⟩
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hcard_univ : (Finset.univ : Finset (Fin m → E)).card = q ^ m := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcardE]
      -- Compute badX.card = left directly via Finset.pi!
      let allowed : Fin m → Finset E := fun r =>
        if r.val < a then {0}
        else if r.val = a then
          Finset.univ.filter (fun α : E => ∀ j : Fin (q - 1), j.val < b → (eNz j).1 ≠ α)
        else Finset.univ
      have hbad_pi : badX = Fintype.piFinset allowed := by
        ext x
        simp only [badX, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
        constructor
        · intro hx r
          dsimp only [allowed]
          split_ifs with hr1 hr2
          · rw [Finset.mem_singleton]
            by_contra hne
            let j := eNz.symm ⟨x r, hne⟩
            have hidx_lt : r.val * (q - 1) + j.val < c := by
              have hdiv : a * (q - 1) + b = c := by
                have := Nat.div_add_mod c (q - 1); rw [mul_comm]; exact this
              have h1 : (r.val + 1) * (q - 1) ≤ a * (q - 1) := Nat.mul_le_mul_right _ (by omega)
              have h2 : (r.val + 1) * (q - 1) = r.val * (q - 1) + (q - 1) := Nat.succ_mul _ _
              have hj := j.isLt
              omega
            let i : Fin c := ⟨r.val * (q - 1) + j.val, hidx_lt⟩
            have hci : coordIdx i = r := by
              apply Fin.ext
              change (r.val * (q - 1) + j.val) / (q - 1) = r.val
              rw [add_comm, mul_comm, Nat.add_mul_div_left _ _ hq1_pos, Nat.div_eq_of_lt j.isLt, zero_add]
            have hvi : valIdx i = x r := by
              have hmod : (r.val * (q - 1) + j.val) % (q - 1) = j.val := by
                rw [add_comm, mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
              have hfin : (⟨(r.val * (q - 1) + j.val) % (q - 1), Nat.mod_lt _ hq1_pos⟩ : Fin (q - 1)) = j :=
                Fin.ext hmod
              change (eNz _).1 = x r
              rw [hfin]
              simpa [j] using congrArg Subtype.val (eNz.apply_symm_apply ⟨x r, hne⟩)
            exact hx i (by rw [hci, hvi])
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro j hjb heq
            have hidx_lt : a * (q - 1) + j.val < c := by
              have hdiv : a * (q - 1) + b = c := by
                have := Nat.div_add_mod c (q - 1); rw [mul_comm]; exact this
              omega
            let i : Fin c := ⟨a * (q - 1) + j.val, hidx_lt⟩
            have hci : coordIdx i = r := by
              apply Fin.ext
              change (a * (q - 1) + j.val) / (q - 1) = r.val
              rw [add_comm, mul_comm, Nat.add_mul_div_left _ _ hq1_pos, Nat.div_eq_of_lt j.isLt, zero_add, hr2]
            have hvi : valIdx i = (eNz j).1 := by
              have hmod : (a * (q - 1) + j.val) % (q - 1) = j.val := by
                rw [add_comm, mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
              have hfin : (⟨(a * (q - 1) + j.val) % (q - 1), Nat.mod_lt _ hq1_pos⟩ : Fin (q - 1)) = j :=
                Fin.ext hmod
              change (eNz _).1 = (eNz j).1
              rw [hfin]
            exact hx i (by rw [hci, hvi, heq])
          · exact Finset.mem_univ _
        · intro hx i
          have hxr := hx (coordIdx i)
          dsimp only [allowed] at hxr
          have hdiv_c : a * (q - 1) + b = c := by
            have := Nat.div_add_mod c (q - 1); rw [mul_comm]; exact this
          have hdiv_i : (coordIdx i).val * (q - 1) + i.val % (q - 1) = i.val := by
            have := Nat.div_add_mod i.val (q - 1); rw [mul_comm]; exact this
          split_ifs at hxr with hr1 hr2
          · rw [Finset.mem_singleton] at hxr
            rw [hxr]; exact (hval_ne i).symm
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hxr
            have hmod_lt : i.val % (q - 1) < b := by
              have hi := i.isLt
              rw [hr2] at hdiv_i
              omega
            exact (hxr ⟨i.val % (q - 1), Nat.mod_lt _ hq1_pos⟩ hmod_lt).symm
          · exfalso
            have hge : a + 1 ≤ (coordIdx i).val := by omega
            have h1 : (a + 1) * (q - 1) ≤ (coordIdx i).val * (q - 1) := Nat.mul_le_mul_right _ hge
            have h2 : (a + 1) * (q - 1) = a * (q - 1) + (q - 1) := Nat.succ_mul _ _
            have hb_lt : b < q - 1 := Nat.mod_lt c hq1_pos
            have hi := i.isLt
            omega
      have hbad_card : badX.card = left := by
        rw [hbad_pi, Fintype.card_piFinset]
        have hcard_allowed : ∀ r : Fin m, (allowed r).card =
            if r.val < a then 1 else if r.val = a then q - b else q := by
          intro r
          dsimp only [allowed]
          split_ifs with hr1 hr2
          · simp
          · -- card of univ \ image of Fin b under eNz
            let imgB : Finset E := (Finset.univ.filter (fun j : Fin (q - 1) => j.val < b)).image (fun j => (eNz j).1)
            have hfilt_eq : Finset.univ.filter (fun α : E => ∀ j : Fin (q - 1), j.val < b → (eNz j).1 ≠ α) =
                Finset.univ \ imgB := by
              ext α
              simp [imgB]
            rw [hfilt_eq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hcardE]
            have himg_card : imgB.card = b := by
              rw [Finset.card_image_of_injective _ (fun j₁ j₂ h => eNz.injective (Subtype.ext h))]
              have hb_lt : b < q - 1 := Nat.mod_lt c hq1_pos
              have hbij : (Finset.univ.filter (fun j : Fin (q - 1) => j.val < b)).card = b := by
                have hcard_fin : (Finset.univ.filter (fun j : Fin (q - 1) => j.val < b)).card =
                    (Finset.univ : Finset (Fin b)).card := by
                  refine Finset.card_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_
                  · intro _ _; exact Finset.mem_univ _
                  · intro j₁ _ j₂ _ h; exact Fin.ext (congrArg (Fin.val : Fin b → ℕ) h)
                  · intro k _
                    refine ⟨⟨k.val, lt_trans k.isLt hb_lt⟩, ?_, Fin.ext rfl⟩
                    simp [k.isLt]
                rw [hcard_fin, Finset.card_univ, Fintype.card_fin]
              exact hbij
            rw [himg_card]
          · rw [Finset.card_univ, hcardE]
        simp_rw [hcard_allowed]
        by_cases ham : a = m
        · have hb0 : b = 0 := by
            have hdiv : a * (q - 1) + b = c := by
              have := Nat.div_add_mod c (q - 1); rw [mul_comm]; exact this
            rw [ham] at hdiv
            omega
          have hprod1 : ∏ r : Fin m, (if r.val < a then 1 else if r.val = a then q - b else q) = 1 := by
            refine Finset.prod_eq_one fun r _ => ?_
            have hr : r.val < a := by rw [ham]; exact r.isLt
            simp [hr]
          rw [hprod1]
          simp [left, ham, hb0]
        · have ha_lt : a < m := by
            have ha_le : a ≤ m := Nat.div_le_of_le_mul (by rwa [mul_comm])
            omega
          let ra : Fin m := ⟨a, ha_lt⟩
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ra)]
          have hra_val : (if ra.val < a then 1 else if ra.val = a then q - b else q) = q - b := by
            simp [ra]
          rw [hra_val]
          let Sgt := Finset.univ.filter (fun r : Fin m => a < r.val)
          have herase : ∏ r ∈ Finset.univ.erase ra, (if r.val < a then 1 else if r.val = a then q - b else q) =
              ∏ _r ∈ Sgt, q := by
            rw [← Finset.prod_subset (s₁ := Sgt) (s₂ := Finset.univ.erase ra)]
            · refine Finset.prod_congr rfl fun r hr => ?_
              have hgt : a < r.val := (Finset.mem_filter.mp hr).2
              have h1 : ¬ r.val < a := by omega
              have h2 : r.val ≠ a := by omega
              simp [h1, h2]
            · intro r hr
              have hgt : a < r.val := (Finset.mem_filter.mp hr).2
              refine Finset.mem_erase.mpr ⟨fun h => by rw [h] at hgt; simp [ra] at hgt, Finset.mem_univ _⟩
            · intro r hr hnot
              have hne : r ≠ ra := (Finset.mem_erase.mp hr).1
              have hval_ne : r.val ≠ a := fun h => hne (Fin.ext h)
              have hnotgt : ¬ a < r.val := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
              have hlt : r.val < a := by omega
              simp [hlt]
          rw [herase, Finset.prod_const]
          have hSgt_card : Sgt.card = m - a - 1 := by
            have hcard_fin : Sgt.card = (Finset.univ : Finset (Fin (m - a - 1))).card := by
              refine Finset.card_bij (fun r hr => ⟨r.val - a - 1, by
                have := (Finset.mem_filter.mp hr).2; have := r.isLt; omega⟩) ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro r₁ hr₁ r₂ hr₂ h
                have h1 := (Finset.mem_filter.mp hr₁).2
                have h2 := (Finset.mem_filter.mp hr₂).2
                have hv := congrArg Fin.val h
                simp only at hv
                exact Fin.ext (by omega)
              · intro k _
                have hk := k.isLt
                exact ⟨⟨a + 1 + k.val, by omega⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, by dsimp; omega⟩,
                  Fin.ext (by dsimp; omega)⟩
            rw [hcard_fin, Finset.card_univ, Fintype.card_fin]
          rw [hSgt_card]
          dsimp only [left]
          have hpow : q ^ (m - a) = q * q ^ (m - a - 1) := by
            have h1 : m - a = (m - a - 1) + 1 := by omega
            conv_lhs => rw [h1, pow_succ, mul_comm]
          rw [hpow, Nat.sub_mul]
      omega

end PEqualNP.Outside.L_meta_25741

theorem PEqualNP.Outside.L_meta_25741 :
    let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      (g.inputs.length == 2) &&
      xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
          (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
    let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
      C.gates.foldl (fun (ds : List ℕ) g =>
        ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
        (List.replicate width 0)
    let fits := fun (n m q : ℕ) (G : Fin q → Fin n → Fin m → Bool) (t : ℕ) =>
      ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin q → ℕ),
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
        (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧ C.gates.countP nonlinear ≤ t ∧
        ∀ j : Fin q, (depths (n+m) C).getD (tap j) 0 ≤ 1 ∧
          PEqualNP.Represents.Represents (G j) ⟨C.gates, tap j⟩
    ∀ (h m t budget : ℕ), 0 < h → 0 < m →
      let F := ZMod 2
      let E := GaloisField 2 h
      let q := 2^h
      let k := h*m
      let n := k+1
      k-h ≤ 2*t → 2*t < k →
      ∀ (K : Type) [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]
        [FiniteDimensional E K], Module.finrank E K = m →
        ∀ (basis : Module.Basis (Fin k) F K) (bit : K →ₗ[F] F), bit ≠ 0 →
          let point : Fin n → K := Fin.cases 0 basis
          let mult := fun (z : K) (x y : Fin n) => decide (bit (z * point x * point y) ≠ 0)
          let table := fun (C : K →ₗ[E] K) (x y : Fin n) => decide (bit (C (point x) * point y) ≠ 0)
          let serves := fun (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K) =>
            ∀ z ∈ S, ∃ i : Fin l,
              fits n n 1 (fun _ x y => xor (mult z x y) (table (C i) x y)) t
          let rk := fun (D : K →ₗ[E] K) => Module.finrank E (LinearMap.range D)
          let c := min budget (m*(q-1))
          let a := c/(q-1)
          let b := c%(q-1)
          let left := q^(m-a) - b*q^(m-a-1)
          (∀ (l : ℕ) (C : Fin l → (K →ₗ[E] K)) (S : Finset K),
            (0 : K) ∉ S → (∑ i : Fin l, rk (C i)) ≤ budget → serves l C S →
            S.card + left ≤ q^m) ∧
          (∃ (C : Fin c → (K →ₗ[E] K)) (S : Finset K),
            (0 : K) ∉ S ∧
            (∀ i : Fin c, rk (C i) = 1 ∧ fits n n 1 (fun _ => table (C i)) ((h+1)/2)) ∧
            serves c C S ∧ S.card + left = q^m) := by
  intro nonlinear depths fits h m t budget hh hm_pos F E q k n hk1 hk2 K _ _ _ _ _ hm basis bit hbit
  exact PEqualNP.Outside.L_meta_25741.main_proof h m t budget hh hm_pos hk1 hk2 K hm basis bit hbit
