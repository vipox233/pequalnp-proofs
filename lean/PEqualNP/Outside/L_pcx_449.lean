import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.Inductions

namespace PEqualNP.Outside.L_pcx_449

abbrev UpperBit := ZMod 2
abbrev UpperAddress (r : ℕ) := Fin r → UpperBit
abbrev UpperPoly (r : ℕ) := MvPolynomial (Fin r ⊕ Unit) UpperBit

def upperEval {r : ℕ} (p : UpperPoly r) (x : UpperAddress r) (u : UpperBit) : UpperBit :=
  MvPolynomial.eval (Sum.elim x (fun _ => u)) p

def upperSupport {r : ℕ} (b : UpperBit) (x : UpperAddress r) : Finset (Fin r) :=
  Finset.univ.filter (fun j => x j = b)

def upperColor {r : ℕ} (d : ℕ) (x : UpperAddress r) : UpperBit :=
  if d + 1 ≤ (upperSupport 1 x).card then 1 else 0

lemma upperBit_cases (b : UpperBit) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma upperSupport_card {r : ℕ} (x : UpperAddress r) :
    (upperSupport 1 x).card + (upperSupport 0 x).card = r := by
  have h : ∀ j : Fin r, (¬ x j = 1) ↔ x j = 0 := by
    intro j
    rcases upperBit_cases (x j) with hj | hj <;> simp [hj]
  simpa [upperSupport, h] using
    (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
      (fun j => x j = 1))

noncomputable def upperLit {r : ℕ} (b : UpperBit) (j : Fin r ⊕ Unit) : UpperPoly r :=
  if b = 1 then MvPolynomial.X j else 1 - MvPolynomial.X j

lemma upperLit_degree {r : ℕ} (b : UpperBit) (j : Fin r ⊕ Unit) :
    (upperLit b j).totalDegree ≤ 1 := by
  unfold upperLit
  split
  · simp
  · exact (MvPolynomial.totalDegree_sub _ _).trans (by simp)

lemma upperLit_eval {r : ℕ} (b : UpperBit) (j : Fin r ⊕ Unit)
    (v : Fin r ⊕ Unit → UpperBit) :
    MvPolynomial.eval v (upperLit b j) = if v j = b then 1 else 0 := by
  rcases upperBit_cases b with hb | hb <;> rcases upperBit_cases (v j) with hj | hj <;>
    simp [upperLit, hb, hj]

noncomputable def upperProduct {r : ℕ} (b : UpperBit) (s : Finset (Fin r)) : UpperPoly r :=
  ∏ j ∈ s, upperLit b (Sum.inl j)

lemma upperProduct_degree {r : ℕ} (b : UpperBit) (s : Finset (Fin r)) :
    (upperProduct b s).totalDegree ≤ s.card := by
  unfold upperProduct
  calc
    _ ≤ ∑ j ∈ s, (upperLit b (Sum.inl j : Fin r ⊕ Unit)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _j ∈ s, (1 : ℕ) := Finset.sum_le_sum (fun j _ => upperLit_degree b (Sum.inl j))
    _ = s.card := by simp

lemma upperProduct_eval {r : ℕ} (b : UpperBit) (s : Finset (Fin r))
    (x : UpperAddress r) (u : UpperBit) :
    upperEval (upperProduct b s) x u = if s ⊆ upperSupport b x then 1 else 0 := by
  classical
  simp only [upperEval, upperProduct, MvPolynomial.eval_prod, upperLit_eval, Sum.elim_inl]
  by_cases h : s ⊆ upperSupport b x
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro j hj
    exact ite_eq_left (by simpa [upperSupport] using h hj)
  · rw [ite_eq_right h]
    obtain ⟨j, hj, hnot⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero hj
    exact ite_eq_right (by simpa [upperSupport] using hnot)

lemma upperColor_ball {r d : ℕ} (hr : r ≤ 2*d+1) (x : UpperAddress r) :
    (upperSupport (1 - upperColor d x) x).card ≤ d := by
  have he := upperSupport_card x
  unfold upperColor
  split
  · rw [sub_self]
    omega
  · rw [sub_zero]
    omega

lemma upperMask {r d : ℕ} (hr : r ≤ 2*d+1) (y : UpperAddress r) :
    ∃ G : UpperPoly r, G.totalDegree ≤ d+1 ∧ (∀ u, upperEval G y u = 1) ∧
      ∀ x u, upperColor d x ≠ upperColor d y → upperEval G x u = 0 := by
  classical
  by_cases hy : d+1 ≤ (upperSupport 1 y).card
  · obtain ⟨s, hsub, hs⟩ := Finset.exists_subset_card_eq hy
    refine ⟨upperProduct 1 s, (upperProduct_degree 1 s).trans_eq hs, ?_, ?_⟩
    · intro u
      rw [upperProduct_eval, ite_eq_left hsub]
    · intro x u hx
      rw [upperProduct_eval, ite_eq_right]
      intro h
      have hx' : d+1 ≤ (upperSupport 1 x).card := hs ▸ Finset.card_le_card h
      exact hx (by simp [upperColor, hy, hx'])
  · have hc := upperSupport_card y
    have hs0 : r-d ≤ (upperSupport 0 y).card := by omega
    obtain ⟨s, hsub, hs⟩ := Finset.exists_subset_card_eq hs0
    refine ⟨upperProduct 0 s, (upperProduct_degree 0 s).trans (by omega), ?_, ?_⟩
    · intro u
      rw [upperProduct_eval, ite_eq_left hsub]
    · intro x u hx
      rw [upperProduct_eval, ite_eq_right]
      intro h
      have hc' := upperSupport_card x
      have hs' := Finset.card_le_card h
      have hx' : ¬ d+1 ≤ (upperSupport 1 x).card := by omega
      exact hx (by simp [upperColor, hy, hx'])

open MvPolynomial

noncomputable def ballIndicator {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (Y : Finset ι) (L : ι → MvPolynomial σ (ZMod 2)) :
    MvPolynomial σ (ZMod 2) :=
  ∑ T ∈ (Finset.univ.powerset.filter (fun T : Finset ι => Y ⊆ T ∧ T.card ≤ d)),
    ∏ j ∈ T, L j

lemma ballIndicator_degree {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} {Y : Finset ι} {L : ι → MvPolynomial σ (ZMod 2)}
    (hL : ∀ j, (L j).totalDegree ≤ 1) : (ballIndicator d Y L).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro T hT
  calc
    (∏ j ∈ T, L j).totalDegree ≤ ∑ j ∈ T, (L j).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ j ∈ T, (1 : ℕ) := Finset.sum_le_sum fun j _ => hL j
    _ = T.card := by simp
    _ ≤ d := ((Finset.mem_filter.mp hT).2).2

lemma ballIndicator_eval {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} {Y : Finset ι} {L : ι → MvPolynomial σ (ZMod 2)}
    (v : σ → ZMod 2) (A : Finset ι)
    (hA : ∀ j, MvPolynomial.eval v (L j) = if j ∈ A then 1 else 0)
    (ha : A.card ≤ d) : MvPolynomial.eval v (ballIndicator d Y L) =
      if A = Y then 1 else 0 := by
  classical
  have ev (T : Finset ι) : MvPolynomial.eval v (∏ j ∈ T, L j) =
      if T ⊆ A then 1 else 0 := by
    rw [MvPolynomial.eval_prod]
    by_cases hT : T ⊆ A
    · rw [ite_eq_left hT]
      exact Finset.prod_eq_one fun j hj => (hA j).trans (ite_eq_left (hT hj))
    · rw [ite_eq_right hT]
      obtain ⟨j, hj, hjA⟩ := Finset.not_subset.mp hT
      exact Finset.prod_eq_zero hj ((hA j).trans (ite_eq_right hjA))
  unfold ballIndicator
  rw [MvPolynomial.eval_sum]
  simp_rw [ev]
  rw [← Finset.sum_filter]
  have idx : (Finset.univ.powerset.filter (fun T : Finset ι => Y ⊆ T ∧ T.card ≤ d)).filter
      (fun T => T ⊆ A) = Finset.Icc Y A := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and,
      Finset.mem_Icc]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, (Finset.card_le_card h.2).trans ha⟩, h.2⟩
  rw [idx]
  by_cases hYA : Y ⊆ A
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_Icc_finset hYA, Nat.cast_pow]
    by_cases hAY : A = Y
    · simp [hAY]
    · have hh : Y.card < A.card := Finset.card_lt_card (lt_of_le_of_ne hYA (Ne.symm hAY))
      rw [ite_eq_right hAY, show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_pow (by omega)]
  · rw [Finset.Icc_eq_empty hYA, Finset.sum_empty, ite_eq_right (fun h => hYA h.symm.le)]

noncomputable def ballInterpolate {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    (d : ℕ) (f : Finset ι → ZMod 2) (L : ι → MvPolynomial σ (ZMod 2)) :
    MvPolynomial σ (ZMod 2) :=
  ∑ Y : Finset ι, C (f Y) * ballIndicator d Y L

lemma ballInterpolate_degree {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} {f : Finset ι → ZMod 2} {L : ι → MvPolynomial σ (ZMod 2)}
    (hL : ∀ j, (L j).totalDegree ≤ 1) : (ballInterpolate d f L).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro Y _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simpa only [MvPolynomial.totalDegree_C, zero_add] using
    (ballIndicator_degree (d := d) (Y := Y) hL)

lemma ballInterpolate_eval {ι σ : Type*} [Fintype ι] [DecidableEq ι]
    {d : ℕ} {f : Finset ι → ZMod 2} {L : ι → MvPolynomial σ (ZMod 2)}
    (v : σ → ZMod 2) (A : Finset ι)
    (hA : ∀ j, MvPolynomial.eval v (L j) = if j ∈ A then 1 else 0)
    (ha : A.card ≤ d) : MvPolynomial.eval v (ballInterpolate d f L) = f A := by
  unfold ballInterpolate
  simp_rw [MvPolynomial.eval_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    ballIndicator_eval v A hA ha, mul_ite, mul_one, mul_zero, eq_comm (a := A)]
  simp

lemma addressInterpolate {r : ℕ} (d : ℕ) (b : ZMod 2)
    (f : (Fin r → ZMod 2) → ZMod 2) :
    ∃ H : MvPolynomial (Fin r ⊕ Unit) (ZMod 2), H.totalDegree ≤ d ∧
      ∀ (x : Fin r → ZMod 2) (u : ZMod 2),
        (Finset.univ.filter (fun j => x j = b)).card ≤ d →
          MvPolynomial.eval (Sum.elim x (fun _ => u)) H = f x := by
  have bits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by
    intro z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  let L : Fin r → MvPolynomial (Fin r ⊕ Unit) (ZMod 2) :=
    fun j => 1 - (X (Sum.inl j) - C b)
  let fromSupport : Finset (Fin r) → Fin r → ZMod 2 :=
    fun A j => if j ∈ A then b else 1 + b
  refine ⟨ballInterpolate d (f ∘ fromSupport) L, ballInterpolate_degree ?_, ?_⟩
  · intro j
    dsimp only [L]
    apply (MvPolynomial.totalDegree_sub _ _).trans
    rw [MvPolynomial.totalDegree_one, max_le_iff]
    refine ⟨Nat.zero_le _, (MvPolynomial.totalDegree_sub _ _).trans ?_⟩
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C, max_zero]
  · intro x u hx
    let A : Finset (Fin r) := Finset.univ.filter (fun j => x j = b)
    have nz (j : Fin r) (h : x j ≠ b) : x j - b = 1 :=
      (bits (x j - b)).resolve_left (sub_ne_zero.mpr h)
    have hA (j : Fin r) : MvPolynomial.eval (Sum.elim x (fun _ : Unit => u)) (L j) =
        if j ∈ A then 1 else 0 := by
      by_cases h : x j = b
      · simp [L, A, h]
      · simp [L, A, h, nz j h]
    have hs : fromSupport A = x := by
      funext j
      by_cases h : x j = b
      · simp [fromSupport, A, h]
      · simpa [fromSupport, A, h] using (sub_eq_iff_eq_add.mp (nz j h)).symm
    simpa only [Function.comp_apply, hs] using
      (ballInterpolate_eval (f := f ∘ fromSupport) (Sum.elim x (fun _ : Unit => u)) A hA hx)

open MvPolynomial

lemma upperMarkers {r d : ℕ} (hr : r ≤ 2*d+1) :
    ∃ mark : UpperAddress r → UpperPoly r, (∀ y, (mark y).totalDegree ≤ d+1) ∧
      (∀ y u, upperEval (mark y) y u = 1) ∧
      ∀ y x, y ≠ x → upperEval (mark y) x (upperColor d x) = 0 := by
  classical
  have oneMarker (y : UpperAddress r) :
      ∃ p : UpperPoly r, p.totalDegree ≤ d+1 ∧ (∀ u, upperEval p y u = 1) ∧
        ∀ x, y ≠ x → upperEval p x (upperColor d x) = 0 := by
    obtain ⟨G, hG, hGy, hGoff⟩ := upperMask hr y
    let c := upperColor d y
    let f : UpperAddress r → UpperBit := fun x =>
      (if x = y then 1 else 0) - upperEval G x (upperColor d x)
    obtain ⟨H, hH, hHe⟩ := addressInterpolate d (1-c) f
    let L : UpperPoly r := upperLit c (Sum.inr ())
    have hL (x : UpperAddress r) (u : UpperBit) :
        upperEval L x u = if u = c then 1 else 0 := by
      exact upperLit_eval c (Sum.inr ()) _
    have hHsame (x : UpperAddress r) (hx : upperColor d x = c) :
        upperEval H x (upperColor d x) = f x := by
      have hball : (upperSupport (1-c) x).card ≤ d := by
        rw [← hx]
        exact upperColor_ball hr x
      exact hHe x (upperColor d x) hball
    refine ⟨G + L * H, ?_, ?_, ?_⟩
    · refine (totalDegree_add _ _).trans (max_le hG ?_)
      exact (totalDegree_mul _ _).trans
        ((Nat.add_le_add (upperLit_degree c (Sum.inr ())) hH).trans_eq (Nat.add_comm 1 d))
    · intro u
      simp only [upperEval, eval_add, eval_mul]
      change upperEval G y u + upperEval L y u * upperEval H y u = 1
      by_cases hu : u = c
      · have hh := hHsame y rfl
        change upperEval H y c = f y at hh
        rw [hu, hL, ite_eq_left rfl, one_mul, hh, hGy]
        simp [f, hGy]
      · rw [hL, ite_eq_right hu, zero_mul, add_zero, hGy]
    · intro x hyx
      simp only [upperEval, eval_add, eval_mul]
      change upperEval G x (upperColor d x) +
        upperEval L x (upperColor d x) * upperEval H x (upperColor d x) = 0
      by_cases hx : upperColor d x = c
      · rw [hL, ite_eq_left hx, one_mul, hHsame x hx]
        simp only [f, ite_eq_right (Ne.symm hyx), zero_sub, add_neg_cancel]
      · rw [hL, ite_eq_right hx, zero_mul, add_zero, hGoff x _ hx]
  choose mark hm using oneMarker
  exact ⟨mark, fun y => (hm y).1, fun y => (hm y).2.1, fun y => (hm y).2.2⟩

open scoped BigOperators



open MvPolynomial

private abbrev LowerK := ZMod 2
private abbrev LowerP (r : ℕ) := MvPolynomial (Fin r ⊕ Unit) LowerK
private abbrev LowerQ (r : ℕ) := MvPolynomial (Fin r) LowerK

private def lowerOption {r : ℕ} : Fin r ⊕ Unit → Option (Fin r)
  | .inl i => some i
  | .inr _ => none

private noncomputable def lowerCurry {r : ℕ} (p : LowerP r) : Polynomial (LowerQ r) :=
  optionEquivLeft LowerK (Fin r) (rename lowerOption p)

private noncomputable def lowerA {r : ℕ} (p : LowerP r) : LowerQ r :=
  (lowerCurry p).coeff 0

private noncomputable def lowerB {r : ℕ} (p : LowerP r) : LowerQ r :=
  (lowerCurry p).divX.eval 1

private abbrev lowerValue {r : ℕ} (p : LowerP r) (x : Fin r → LowerK) (u : LowerK) :
    LowerK :=
  eval (Sum.elim x (fun _ => u)) p

private lemma lowerAddSelf (a : LowerK) : a + a = 0 := by
  rw [← two_mul, show (2 : LowerK) = 0 by decide, zero_mul]

private lemma lowerA_degree {r : ℕ} (p : LowerP r) :
    (lowerA p).totalDegree ≤ p.totalDegree :=
  (totalDegree_coeff_optionEquivLeft_le LowerK (Fin r) (rename lowerOption p) 0).trans
    (totalDegree_rename_le _ p)

private lemma lowerB_degree {r d : ℕ} (p : LowerP r) (hp : p.totalDegree ≤ d + 1) :
    (lowerB p).totalDegree ≤ d := by
  classical
  unfold lowerB
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  apply totalDegree_finsetSum_le
  intro i hi
  have hcoef : (lowerCurry p).coeff (i + 1) ≠ 0 := by
    simpa only [Polynomial.mem_support_iff, Polynomial.coeff_divX] using hi
  have hi' : i + 1 ≤ (rename lowerOption p).totalDegree := by
    apply le_trans (Polynomial.le_natDegree_of_ne_zero hcoef)
    rw [lowerCurry, natDegree_optionEquivLeft]
    exact degreeOf_le_totalDegree _ _
  have hbound :=
    totalDegree_coeff_optionEquivLeft_add_le LowerK (Fin r) (rename lowerOption p) (i + 1) hi'
  have hrename := totalDegree_rename_le lowerOption p
  rw [Polynomial.coeff_divX]
  change ((lowerCurry p).coeff (i + 1)).totalDegree ≤ d
  change ((lowerCurry p).coeff (i + 1)).totalDegree + (i + 1) ≤
    (rename lowerOption p).totalDegree at hbound
  omega

private lemma lowerEvalCurry {r : ℕ} (p : LowerP r) (x : Fin r → LowerK) (u : LowerK) :
    lowerValue p x u = Polynomial.eval u (Polynomial.map (eval x) (lowerCurry p)) := by
  let g : Option (Fin r) → LowerK := fun i => i.elim u x
  have hg : Sum.elim x (fun _ : Unit => u) = g ∘ lowerOption := by
    funext i
    cases i <;> rfl
  calc
    lowerValue p x u = eval (g ∘ lowerOption) p := congrArg (fun f => eval f p) hg
    _ = eval g (rename lowerOption p) := (eval_rename lowerOption g p).symm
    _ = _ := optionEquivLeft_elim_eval LowerK (Fin r) x u (rename lowerOption p)

private lemma lowerEvalA {r : ℕ} (p : LowerP r) (x : Fin r → LowerK) :
    eval x (lowerA p) = lowerValue p x 0 := by
  rw [lowerEvalCurry, Polynomial.eval_zero_map, ← Polynomial.coeff_zero_eq_eval_zero]
  rfl

private lemma lowerEvalB {r : ℕ} (p : LowerP r) (x : Fin r → LowerK) :
    eval x (lowerB p) = lowerValue p x 1 + lowerValue p x 0 := by
  have h : (lowerCurry p).eval 1 = lowerB p + lowerA p := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add (lowerCurry p)]
    simp [lowerA, lowerB]
  rw [lowerEvalCurry p x 1, Polynomial.eval_one_map, h, map_add, lowerEvalA, add_assoc,
    lowerAddSelf, add_zero]

private lemma lowerSumMonomial {r : ℕ} (m : Fin r →₀ ℕ) (a : LowerK)
    (j : Fin r) (hj : m j = 0) :
    (∑ x : Fin r → LowerK, eval x (monomial m a)) = 0 := by
  simp only [eval_monomial]
  simp_rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [← Finset.mul_sum, ← Fintype.prod_sum (fun (i : Fin r) (c : LowerK) => c ^ m i)]
  have hj' : (∑ c : LowerK, c ^ m j) = 0 := by
    simp [hj, ZMod.card, show (2 : LowerK) = 0 by decide]
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hj', mul_zero]

private lemma lowerSumEval {r : ℕ} (q : LowerQ r) (hq : q.totalDegree < r) :
    (∑ x : Fin r → LowerK, eval x q) = 0 := by
  classical
  conv_lhs =>
    arg 2
    intro x
    rw [q.as_sum, map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro m hm
  have hdeg : q.totalDegree < 1 * Fintype.card (Fin r) := by simpa using hq
  obtain ⟨j, hj⟩ := q.exists_degree_lt 1 hdeg hm
  exact lowerSumMonomial m (q.coeff m) j (by omega)

private lemma lowerPointDegree {r : ℕ} (q : LowerQ r) (y : Fin r → LowerK)
    (hy : eval y q = 1) (hother : ∀ x, y ≠ x → eval x q = 0) :
    r ≤ q.totalDegree := by
  classical
  by_contra! hdegree
  have hsum : (∑ x : Fin r → LowerK, eval x q) = 1 := by
    rw [Finset.sum_eq_single y (fun x _ hxy => hother x (Ne.symm hxy))
      (fun h => (h (Finset.mem_univ y)).elim), hy]
  exact zero_ne_one (lowerSumEval q hdegree |>.symm.trans hsum)

private lemma lowerBit (u : LowerK) : u = 0 ∨ u = 1 := by
  fin_cases u <;> first | exact Or.inl rfl | exact Or.inr rfl

lemma lowerBound (r d : ℕ)
    (menu : (Fin r → ZMod 2) → Finset (MvPolynomial (Fin r ⊕ Unit) (ZMod 2)))
    (w : (Fin r → ZMod 2) → ZMod 2)
    (hdegree : ∀ y p, p ∈ menu y → p.totalDegree ≤ d+1)
    (hown : ∀ y u, ∃ p ∈ menu y, MvPolynomial.eval (Sum.elim y (fun _ => u)) p = 1)
    (hother : ∀ y x, y ≠ x → ∀ p ∈ menu y, MvPolynomial.eval (Sum.elim x (fun _ => w x)) p = 0) :
    r ≤ 2*d+1 := by
  classical
  let y : Fin r → LowerK := fun _ => 0
  by_cases hcommon : ∃ p ∈ menu y, lowerValue p y 0 = 1 ∧ lowerValue p y 1 = 1
  · obtain ⟨p, hp, hp0, hp1⟩ := hcommon
    let q := lowerA p * (1 + lowerB p)
    have hq : q.totalDegree ≤ 2*d+1 := by
      unfold q
      have hA := (lowerA_degree p).trans (hdegree y p hp)
      have hB := lowerB_degree p (hdegree y p hp)
      have hsum := totalDegree_add 1 (lowerB p)
      rw [totalDegree_one, zero_max] at hsum
      have hmul := totalDegree_mul (lowerA p) (1 + lowerB p)
      omega
    apply le_trans (lowerPointDegree q y ?_ ?_) hq
    · simp only [q, map_mul, map_add, map_one, lowerEvalA, lowerEvalB, hp0, hp1]
      decide
    · intro x hxy
      have hx := hother y x hxy p hp
      change lowerValue p x (w x) = 0 at hx
      rcases lowerBit (w x) with hw | hw
      · rw [hw] at hx
        simp [q, lowerEvalA, hx]
      · rw [hw] at hx
        rcases lowerBit (lowerValue p x 0) with hv | hv
        · simp [q, lowerEvalA, hv]
        · simp only [q, map_mul, map_add, map_one, lowerEvalA, lowerEvalB, hx, hv]
          decide
  · obtain ⟨p0, hp0, hy0⟩ := hown y 0
    obtain ⟨p1, hp1, hy1⟩ := hown y 1
    change lowerValue p0 y 0 = 1 at hy0
    change lowerValue p1 y 1 = 1 at hy1
    have h01 : lowerValue p0 y 1 = 0 :=
      (lowerBit _).resolve_right fun h => hcommon ⟨p0, hp0, hy0, h⟩
    have h10 : lowerValue p1 y 0 = 0 :=
      (lowerBit _).resolve_right fun h => hcommon ⟨p1, hp1, h, hy1⟩
    let q := lowerA p0 * lowerB p1 + lowerA p1 * lowerB p0
    have hmul (p t : LowerP r) (hp : p ∈ menu y) (ht : t ∈ menu y) :
        (lowerA p * lowerB t).totalDegree ≤ 2*d+1 := by
      have hA := (lowerA_degree p).trans (hdegree y p hp)
      have hB := lowerB_degree t (hdegree y t ht)
      have hmul := totalDegree_mul (lowerA p) (lowerB t)
      omega
    have hq : q.totalDegree ≤ 2*d+1 :=
      (totalDegree_add _ _).trans (max_le (hmul p0 p1 hp0 hp1) (hmul p1 p0 hp1 hp0))
    apply le_trans (lowerPointDegree q y ?_ ?_) hq
    · simp [q, lowerEvalA, lowerEvalB, hy0, hy1, h01, h10]
    · intro x hxy
      have hx0 := hother y x hxy p0 hp0
      have hx1 := hother y x hxy p1 hp1
      change lowerValue p0 x (w x) = 0 at hx0
      change lowerValue p1 x (w x) = 0 at hx1
      rcases lowerBit (w x) with hw | hw
      · rw [hw] at hx0 hx1
        simp [q, lowerEvalA, hx0, hx1]
      · rw [hw] at hx0 hx1
        simp only [q, map_mul, map_add, lowerEvalA, lowerEvalB, hx0, hx1, zero_add]
        rw [mul_comm (lowerValue p1 x 0), lowerAddSelf]

end PEqualNP.Outside.L_pcx_449

theorem PEqualNP.Outside.L_pcx_449 : (∀ r d : ℕ,
  let K := ZMod 2
  let I := Fin r → K
  let P := MvPolynomial (Fin r ⊕ Unit) K
  let val := fun (p : P) (x : I) (u : K) => MvPolynomial.eval (Sum.elim x (fun _ => u)) p
  let color := fun (x : I) => (if d+1 ≤ (Finset.univ.filter (fun j => x j = 1)).card
    then (1 : K) else 0)
  let possible := ∃ (menu : I → Finset P) (w : I → K),
    (∀ y, ∀ p ∈ menu y, p.totalDegree ≤ d+1) ∧
    (∀ y u, ∃ p ∈ menu y, val p y u = 1) ∧
    ∀ y x, y ≠ x → ∀ p ∈ menu y, val p x (w x) = 0
  (possible ↔ r ≤ 2*d+1) ∧
    (r ≤ 2*d+1 → ∃ mark : I → P, (∀ y, (mark y).totalDegree ≤ d+1) ∧
      (∀ y u, val (mark y) y u = 1) ∧
      ∀ y x, y ≠ x → val (mark y) x (color x) = 0)) := by
  intro r d
  dsimp only
  constructor
  · constructor
    · rintro ⟨menu, w, hdegree, hown, hother⟩
      exact PEqualNP.Outside.L_pcx_449.lowerBound r d menu w hdegree hown hother
    · intro hr
      obtain ⟨mark, hdegree, hown, hother⟩ := PEqualNP.Outside.L_pcx_449.upperMarkers hr
      refine ⟨fun y => {mark y}, PEqualNP.Outside.L_pcx_449.upperColor d, ?_, ?_, ?_⟩
      · intro y p hp
        obtain rfl := Finset.mem_singleton.mp hp
        exact hdegree y
      · exact fun y u => ⟨mark y, Finset.mem_singleton_self _, hown y u⟩
      · intro y x hyx p hp
        obtain rfl := Finset.mem_singleton.mp hp
        exact hother y x hyx
  · exact PEqualNP.Outside.L_pcx_449.upperMarkers
