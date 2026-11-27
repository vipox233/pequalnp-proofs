import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_500

open MvPolynomial PEqualNP.ProofComplexity

variable {σ : Type}

theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

theorem pcDerivable_monomial_mul {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (a : σ →₀ ℕ) : ∀ {g : MvPolynomial σ (ZMod 2)}, PCDerivable F B g →
      (a.sum fun _ e => e) + g.totalDegree ≤ B → PCDerivable F B (monomial a 1 * g) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    intro g hg _
    have : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [this, one_mul]
    exact hg
  | add a b iha ihb =>
    intro g hg hdeg
    have hsplit : monomial (a + b) (1 : ZMod 2) * g = monomial a 1 * (monomial b 1 * g) := by
      rw [← mul_assoc, monomial_mul_monomial, one_mul]
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    have hb : (monomial b (1 : ZMod 2) * g).totalDegree
        ≤ (b.sum fun _ e => e) + g.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add_right (totalDegree_monomial_le b 1) _)
    rw [hsplit]
    exact iha (ihb hg (by omega)) (by omega)
  | single j n =>
    induction n with
    | zero =>
      intro g hg _
      have : (monomial (Finsupp.single j 0) (1 : ZMod 2)) = 1 := by simp
      rw [this, one_mul]
      exact hg
    | succ n ih =>
      intro g hg hdeg
      have hsplit : monomial (Finsupp.single j (n + 1)) (1 : ZMod 2) * g
          = X j * (monomial (Finsupp.single j n) 1 * g) := by
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      have hd1 : ((Finsupp.single j (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd2 : ((Finsupp.single j n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      have hlow : (monomial (Finsupp.single j n) (1 : ZMod 2) * g).totalDegree
          ≤ n + g.totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add_right
          ((totalDegree_monomial_le _ 1).trans_eq hd2) _)
      rw [hsplit]
      refine .mulX j (ih hg (by omega)) ?_
      refine (totalDegree_mul _ _).trans ?_
      have := totalDegree_X (R := ZMod 2) j
      omega

namespace BoolVanish
variable {σ : Type}

noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

theorem boolDerivable_monomial (d : ℕ) :
    ∀ (n : ℕ) (a : σ →₀ ℕ), (a.sum fun _ e => e) = n → n ≤ d →
      PCDerivable (boolAxioms σ) d (monomial a 1 + monomial (mlin a) 1) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn hd
  by_cases hall : ∀ v, a v ≤ 1
  · have : mlin a = a := by
      ext v; rw [mlin_apply]; have := hall v; omega
    rw [this, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
    exact .zero
  simp only [not_forall, not_le] at hall
  obtain ⟨v, hv⟩ := hall
  set b := a - Finsupp.single v 2 with hb
  have ha : a = b + Finsupp.single v 2 := by
    ext w
    simp only [hb, Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with h
    · subst h; omega
    · omega
  set a' := b + Finsupp.single v 1 with ha'
  have hsum : ∀ c : σ →₀ ℕ, ∀ k, ((c + Finsupp.single v k).sum fun _ e => e)
      = (c.sum fun _ e => e) + k := by
    intro c k
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
  have hmlin : mlin a' = mlin a := by
    ext w
    simp only [mlin_apply, ha, ha', Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hna : (a.sum fun _ e => e) = (b.sum fun _ e => e) + 2 := by rw [ha, hsum]
  have hna' : (a'.sum fun _ e => e) = (b.sum fun _ e => e) + 1 := by rw [ha', hsum]
  have hstep : PCDerivable (boolAxioms σ) d (monomial a 1 + monomial a' 1) := by
    have hid : monomial a (1 : ZMod 2) + monomial a' 1
        = monomial b 1 * (X v * X v + X v) := by
      rw [mul_add, X, monomial_mul_monomial, monomial_mul_monomial, monomial_mul_monomial,
        ← Finsupp.single_add, ha, ha', one_mul, one_mul]
    rw [hid]
    have hax : PCDerivable (boolAxioms σ) d (X v * X v + X v) := by
      refine .ax ⟨v, rfl⟩ ?_
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]; omega
      · rw [totalDegree_X]; omega
    refine pcDerivable_monomial_mul b hax ?_
    have : (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_X]
      · rw [totalDegree_X]; omega
    omega
  have hrest := ih _ (by omega) a' rfl (by omega)
  rw [hmlin] at hrest
  have := PCDerivable.add hstep hrest
  have e : monomial a (1 : ZMod 2) + monomial a' 1 + (monomial a' 1 + monomial (mlin a) 1)
      = monomial a 1 + monomial (mlin a) 1 := by
    rw [add_assoc, ← add_assoc (monomial a' 1), ← two_smul (ZMod 2) (monomial a' 1),
      show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]
  rwa [e] at this

end BoolVanish

namespace Cover

theorem degX {ι : Type} (n : ℕ) (T : Finset ι) (f : ι → Fin n) :
    (∏ i ∈ T, (X (f i) : MvPolynomial (Fin n) (ZMod 2))).totalDegree ≤ T.card := by
  refine (totalDegree_finsetProd T _).trans ?_
  rw [Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro i _
  rw [totalDegree_X]

theorem degLit (n : ℕ) (l : Fin n × Bool) :
    (if l.2 = true then 1 + X l.1 else X l.1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree ≤ 1 := by
  split_ifs
  · refine (totalDegree_add _ _).trans ?_
    rw [totalDegree_one, totalDegree_X]
    exact max_le (Nat.zero_le 1) (le_refl 1)
  · rw [totalDegree_X]

theorem degClause (n : ℕ) (C : Clause (Fin n)) : (clausePoly C).totalDegree ≤ C.card := by
  unfold clausePoly
  refine (totalDegree_finsetProd C _).trans ?_
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun l _ => degLit n l)

theorem split (n : ℕ) (C : Clause (Fin n)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), (q = 0 ∨ q.totalDegree < C.card) ∧
      clausePoly C = (∏ l ∈ C, X l.1) + q := by
  unfold clausePoly
  induction C using Finset.induction_on with
  | empty => exact ⟨0, Or.inl rfl, by simp⟩
  | insert a S ha ih =>
    obtain ⟨q, hq, he⟩ := ih
    rw [Finset.prod_insert ha, Finset.prod_insert ha, he, Finset.card_insert_of_notMem ha]
    have hM : (∏ l ∈ S, (X l.1 : MvPolynomial (Fin n) (ZMod 2))).totalDegree ≤ S.card :=
      degX n S Prod.fst
    have hX : (X a.1 : MvPolynomial (Fin n) (ZMod 2)).totalDegree = 1 := totalDegree_X _
    have hmul := totalDegree_mul (X a.1 : MvPolynomial (Fin n) (ZMod 2)) q
    have hq1 : q.totalDegree ≤ S.card := by
      rcases hq with h | h
      · rw [h, totalDegree_zero]; exact Nat.zero_le _
      · omega
    have hq2 : (X a.1 * q).totalDegree ≤ S.card := by
      rcases hq with h | h
      · rw [h, mul_zero, totalDegree_zero]; exact Nat.zero_le _
      · omega
    by_cases hs : a.2 = true
    · simp only [hs, ↓reduceIte]
      refine ⟨(∏ l ∈ S, X l.1) + q + X a.1 * q, Or.inr ?_, by ring⟩
      have h1 := totalDegree_add ((∏ l ∈ S, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) + q) (X a.1 * q)
      have h2 := totalDegree_add (∏ l ∈ S, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) q
      have h3 := max_le hM hq1
      have h4 := max_le (h2.trans h3) hq2
      exact Nat.lt_succ_of_le (h1.trans h4)
    · have hb : a.2 = false := by simpa using hs
      simp only [hb, Bool.false_eq_true, ↓reduceIte]
      refine ⟨X a.1 * q, ?_, by ring⟩
      rcases hq with h | h
      · left; rw [h, mul_zero]
      · right; omega

theorem mulT (n : ℕ) (F : Set (MvPolynomial (Fin n) (ZMod 2))) (B : ℕ)
    (p : MvPolynomial (Fin n) (ZMod 2)) (hp : PCDerivable F B p) (T : Finset (Fin n))
    (hdeg : ∀ T' : Finset (Fin n), T' ⊆ T → ((∏ j ∈ T', X j) * p).totalDegree ≤ B) :
    PCDerivable F B ((∏ j ∈ T, X j) * p) := by
  induction T using Finset.induction_on with
  | empty => simpa using hp
  | insert a S ha ih =>
    have h1 := ih (fun T' hT' => hdeg T' (hT'.trans (Finset.subset_insert a S)))
    have h2 := hdeg (insert a S) (Finset.Subset.refl _)
    rw [Finset.prod_insert ha, mul_assoc] at h2 ⊢
    exact PCDerivable.mulX a h1 h2

theorem main (n : ℕ) (F : Set (Clause (Fin n))) (S : Finset (Fin n)) (C : Clause (Fin n))
    (hS : S.Nonempty) (hsub : (C.image Prod.fst) ⊆ S)
    (hcons : ∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C))
    (hd : PCDerivable (cnfSystem F) S.card (clausePoly C)) :
    ∃ q : MvPolynomial (Fin n) (ZMod 2), q.totalDegree < S.card ∧
      PCDerivable (cnfSystem F) S.card ((∏ i ∈ S, MvPolynomial.X i) + q) := by
  have hinj : ∀ x ∈ C, ∀ y ∈ C, x.1 = y.1 → x = y := by
    rintro ⟨i, b⟩ hl ⟨j, c⟩ hl' hij
    simp only at hij
    subst hij
    by_contra hne
    apply hcons i
    cases b <;> cases c <;> simp_all
  have hinj' : Set.InjOn Prod.fst (C : Set (Fin n × Bool)) :=
    fun x hx y hy h => hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) h
  have hcard : (C.image Prod.fst).card = C.card := Finset.card_image_of_injOn hinj'
  have hTc : (S \ C.image Prod.fst).card + C.card = S.card := by
    rw [← hcard]; exact Finset.card_sdiff_add_card_eq_card hsub
  have hder := mulT n (cnfSystem F) S.card (clausePoly C) hd (S \ C.image Prod.fst) (by
    intro T' hT'
    refine (totalDegree_mul _ _).trans ?_
    have h1 := degX n T' id
    have h2 := degClause n C
    have h3 := Finset.card_le_card hT'
    simp only [id] at h1
    omega)
  obtain ⟨q, hq, he⟩ := split n C
  have hprod : (∏ l ∈ C, (X l.1 : MvPolynomial (Fin n) (ZMod 2))) =
      ∏ i ∈ C.image Prod.fst, X i := (Finset.prod_image hinj).symm
  have hS' : (∏ j ∈ S \ C.image Prod.fst, (X j : MvPolynomial (Fin n) (ZMod 2))) *
      ∏ i ∈ C.image Prod.fst, X i = ∏ i ∈ S, X i := Finset.prod_sdiff hsub
  refine ⟨(∏ j ∈ S \ C.image Prod.fst, X j) * q, ?_, ?_⟩
  · rcases hq with h | h
    · rw [h, mul_zero, totalDegree_zero]; exact Finset.card_pos.mpr hS
    · have h1 := degX n (S \ C.image Prod.fst) id
      have h2 := totalDegree_mul (∏ j ∈ S \ C.image Prod.fst, (X j : MvPolynomial (Fin n) (ZMod 2))) q
      simp only [id] at h1
      omega
  · have hfin : (∏ i ∈ S, (X i : MvPolynomial (Fin n) (ZMod 2))) +
        (∏ j ∈ S \ C.image Prod.fst, X j) * q =
        (∏ j ∈ S \ C.image Prod.fst, X j) * clausePoly C := by
      rw [he, hprod, mul_add, hS']
    rw [hfin]; exact hder

end Cover

abbrev P (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

variable {n r : ℕ} {F : Set (Clause (Fin n))}

abbrev D (F : Set (Clause (Fin n))) (r : ℕ) := PCDerivable (cnfSystem F) (r+1)

theorem selfRel (p : P n) : D F r (p+p) := by
  rw [CharTwo.add_self_eq_zero]
  exact .zero

theorem chain {p q t : P n} (h : D F r (p+q)) (k : D F r (q+t)) : D F r (p+t) := by
  have e : (p+q)+(q+t) = p+t := by
    rw [add_assoc, ← add_assoc q, CharTwo.add_self_eq_zero, zero_add]
  exact e ▸ h.add k

theorem rev {p q : P n} (h : D F r (p+q)) : D F r (q+p) := add_comm p q ▸ h

theorem reduced (hr : 0 < r)
    (hcover : ∀ S : Finset (Fin n), S.card = r →
      ∃ q : P n, q.totalDegree < r ∧ D F r ((∏ i ∈ S, X i) + q))
    (p : P n) (hp : p.totalDegree ≤ r) :
    ∃ q : P n, q.totalDegree < r ∧ D F r (p+q) := by
  classical
  have hm (s : Fin n →₀ ℕ) (hs : s ∈ p.support) :
      ∃ q : P n, q.totalDegree < r ∧ D F r (monomial s (p.coeff s)+q) := by
    have hd : (s.sum fun _ e => e) ≤ r := (le_totalDegree hs).trans hp
    have hc : p.coeff s = 1 := by
      have hn := MvPolynomial.mem_support_iff.mp hs
      have hx : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
      exact hx _ hn
    rw [hc]
    have hcard : s.support.card ≤ r := by
      apply le_trans _ hd
      rw [Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hml : (BoolVanish.mlin s).support = s.support := by
      ext i
      simp only [Finsupp.mem_support_iff, BoolVanish.mlin_apply]
      omega
    have he : monomial (BoolVanish.mlin s) (1 : ZMod 2) = ∏ i ∈ s.support, X i := by
      rw [← prod_X_pow_eq_monomial, hml]
      apply Finset.prod_congr rfl
      intro i hi
      have hi' := Finsupp.mem_support_iff.mp hi
      rw [BoolVanish.mlin_apply, show min (s i) 1 = 1 by omega, pow_one]
    have hder := BoolVanish.boolDerivable_monomial r _ s rfl hd
    rw [he] at hder
    have lift : D F r (monomial s 1 + ∏ i ∈ s.support, X i) :=
      pcDerivable_mono hder (by omega) (by rintro z ⟨i,rfl⟩; exact Or.inl ⟨i,rfl⟩)
    rcases lt_or_eq_of_le hcard with h | h
    · exact ⟨_, lt_of_le_of_lt (Cover.degX n s.support id) h, lift⟩
    · obtain ⟨q,hq,hrel⟩ := hcover _ h
      exact ⟨q,hq,chain lift hrel⟩
  have sumred (S : Finset (Fin n →₀ ℕ)) (hS : S ⊆ p.support) :
      ∃ q : P n, q.totalDegree < r ∧ D F r ((∑ s ∈ S, monomial s (p.coeff s))+q) := by
    induction S using Finset.induction_on with
    | empty => exact ⟨0, by simpa using hr, by simpa using (PCDerivable.zero : D F r 0)⟩
    | insert s S hs ih =>
      obtain ⟨u,hu,du⟩ := hm s (hS (Finset.mem_insert_self _ _))
      obtain ⟨v,hv,dv⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hS)
      refine ⟨u+v, lt_of_le_of_lt (totalDegree_add _ _) (max_lt hu hv), ?_⟩
      rw [Finset.sum_insert hs, add_add_add_comm]
      exact du.add dv
  simpa only [support_sum_monomial_coeff] using sumred p.support (by rfl)

abbrev Lit (n : ℕ) := Fin n × Bool

noncomputable def factor (l : Lit n) : P n :=
  if l.2 = true then 1 + X l.1 else X l.1

theorem mulFactor (l : Lit n) {p : P n} (hp : D F r p) (hd : p.totalDegree ≤ r) :
    D F r (factor l * p) := by
  have hx : D F r (X l.1 * p) := by
    apply PCDerivable.mulX _ hp
    exact (totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega)
  unfold factor
  split_ifs
  · simpa only [add_mul, one_mul] using hp.add hx
  · exact hx

theorem mulRel (l : Lit n) {p q : P n} (hp : p.totalDegree ≤ r) (hq : q.totalDegree ≤ r)
    (e : D F r (p+q)) : D F r (factor l * p + factor l * q) := by
  rw [← mul_add]
  exact mulFactor l e ((totalDegree_add _ _).trans (max_le hp hq))

theorem transport {p q : P n} (e : D F r (p+q)) (hq : D F r q) : D F r p := by
  have eq : D F r (q+0) := by simpa using hq
  simpa using chain e eq

theorem factorBound (l : Lit n) {p : P n} (hp : p.totalDegree < r) :
    (factor l * p).totalDegree ≤ r :=
  (totalDegree_mul _ _).trans (by have := Cover.degLit n l; change (factor l).totalDegree ≤ 1 at this; omega)

theorem foldSmall (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (hr : 0 < r) (L : List (Lit n)) :
    (L.foldr s 1).totalDegree < r := by
  induction L with
  | nil => simpa using hr
  | cons l L ih => exact (hs l _ ih).1

theorem stepRel (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (l : Lit n) {p q : P n} (hp : p.totalDegree < r) (hq : q.totalDegree < r)
    (e : D F r (p+q)) : D F r (s l p + s l q) :=
  chain (hs l _ hp).2 (chain (mulRel l hp.le hq.le e) (rev (hs l _ hq).2))

theorem stepSwap (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (l k : Lit n) {p : P n} (hp : p.totalDegree < r) :
    D F r (s l (s k p) + s k (s l p)) := by
  have two (i j : Lit n) : D F r (s i (s j p) + factor i * (factor j * p)) :=
    chain (hs i _ (hs j _ hp).1).2
      (mulRel i (hs j _ hp).1.le (factorBound j hp) (hs j _ hp).2)
  have e := two k l
  rw [mul_left_comm (factor k) (factor l)] at e
  exact chain (two l k) (rev e)

theorem foldPerm (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (hr : 0 < r) {A B : List (Lit n)} (e : A.Perm B) :
    D F r (A.foldr s 1 + B.foldr s 1) := by
  induction e with
  | nil => exact selfRel _
  | cons l h ih => exact stepRel s hs l (foldSmall s hs hr _) (foldSmall s hs hr _) ih
  | swap l k L => exact stepSwap s hs _ _ (foldSmall s hs hr L)
  | trans h k ih ik => exact chain ih ik

theorem foldProd (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (hr : 0 < r) (L : List (Lit n)) (hL : L.length ≤ r+1) :
    D F r (L.foldr s 1 + (L.map factor).prod) := by
  induction L with
  | nil => exact selfRel _
  | cons l L ih =>
    have hlen : L.length ≤ r := by simpa using hL
    have degProd (A : List (Lit n)) : (A.map factor).prod.totalDegree ≤ A.length := by
      induction A with
      | nil => simp
      | cons k A hk =>
        simpa only [List.map_cons, List.prod_cons, List.length_cons] using
          (totalDegree_mul (factor k) (A.map factor).prod).trans (by
            have := Cover.degLit n k; change (factor k).totalDegree ≤ 1 at this; omega)
    exact chain (hs l _ (foldSmall s hs hr L)).2
      (mulRel l (foldSmall s hs hr L).le ((degProd L).trans hlen) (ih (by omega)))

theorem branch (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (hr : 0 < r) (h : ¬ D F r 1) (I : List (Fin n)) :
    ∃ L : List (Lit n), L.map Prod.fst = I ∧ ¬ D F r (L.foldr s 1) := by
  induction I with
  | nil => exact ⟨[],rfl,h⟩
  | cons i I ih =>
    obtain ⟨L, hL, hd⟩ := ih
    let p := L.foldr s 1
    have hp : p.totalDegree < r := foldSmall s hs hr L
    by_cases hb : D F r (s (i,false) p)
    · refine ⟨(i,true)::L, by simp [hL], ?_⟩
      intro ha
      have h0 := transport (rev (hs (i,false) p hp).2) hb
      have h1 := transport (rev (hs (i,true) p hp).2) ha
      change D F r (X i * p) at h0
      change D F r ((1+X i)*p) at h1
      rw [add_mul,one_mul] at h1
      exact hd (transport h1 h0)
    · exact ⟨(i,false)::L, by simp [hL], hb⟩

theorem foldPrefix (s : Lit n → P n → P n)
    (hs : ∀ l (p : P n), p.totalDegree < r →
  (s l p).totalDegree < r ∧ D F r (s l p + factor l * p))
    (hr : 0 < r) (A B : List (Lit n)) (hd : D F r (B.foldr s 1)) :
    D F r ((A++B).foldr s 1) := by
  induction A with
  | nil => simpa using hd
  | cons l A ih =>
    have hp := foldSmall s hs hr (A++B)
    exact transport (hs l _ hp).2 (mulFactor l ih hp.le)

theorem finish (hr : 0 < r) (width : ∀ C ∈ F, Finset.card C ≤ r+1)
    (bad : ¬ Satisfiable F)
    (cover : ∀ S : Finset (Fin n), S.card = r →
      ∃ q : P n, q.totalDegree < r ∧ D F r ((∏ i ∈ S, X i) + q)) : D F r 1 := by
  classical
  have stepExists (l : Lit n) (p : P n) : ∃ q : P n, p.totalDegree < r →
      q.totalDegree < r ∧ D F r (q + factor l * p) := by
    by_cases hp : p.totalDegree < r
    · obtain ⟨q,hq,eq⟩ := reduced hr cover _ (factorBound l hp)
      exact ⟨q, fun _ => ⟨hq, rev eq⟩⟩
    · exact ⟨0,fun h => (hp h).elim⟩
  choose s hs using stepExists
  by_contra h
  obtain ⟨L,hL,hnd⟩ := branch s hs hr h (Finset.univ : Finset (Fin n)).toList
  let a : Fin n → Bool := fun i => decide ((i,false) ∈ L)
  have hns : ¬ Satisfies a F := fun hh => bad ⟨a,hh⟩
  obtain ⟨C, hC, hc⟩ : ∃ C ∈ F, ¬ ClauseSat a C := by
    simpa [Satisfies] using hns
  have subset : C.toList ⊆ L := by
    rintro ⟨i,b⟩ hi
    have hi' := Finset.mem_toList.mp hi
    have ne : a i ≠ b := fun e => hc ⟨(i,b),hi',e⟩
    have existsLit : i ∈ L.map Prod.fst := by rw [hL]; simp
    obtain ⟨⟨j,c⟩, hm, rfl⟩ := List.mem_map.mp existsLit
    cases b <;> cases c <;> simp_all [a]
  obtain ⟨L', hp, hsub⟩ := List.subperm_iff.mp (C.nodup_toList.subperm subset)
  obtain ⟨R,hperm⟩ := hsub.exists_perm_append
  have perm := (hp.symm.trans hperm).trans (List.perm_append_comm)
  have eq := foldProd s hs hr C.toList (by simpa using width C hC)
  rw [Finset.prod_map_toList] at eq
  have ax : D F r (clausePoly C) :=
    .ax (Or.inr ⟨C,hC,rfl⟩) ((Cover.degClause n C).trans (width C hC))
  have hd : D F r (C.toList.foldr s 1) := transport eq ax
  exact hnd (transport (foldPerm s hs hr perm) (foldPrefix s hs hr R C.toList hd))
end PEqualNP.Outside.L_lib_500
theorem PEqualNP.Outside.L_lib_500 : (∀ (n r : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))), 0 < r → r ≤ n →
  (∀ E ∈ F, Finset.card E ≤ r+1) → ¬ PEqualNP.ProofComplexity.Satisfiable F →
  (∀ S : Finset (Fin n), S.card = r → ∃ C : PEqualNP.ProofComplexity.Clause (Fin n), (C.image Prod.fst) ⊆ S ∧
    (∀ i : Fin n, ¬ ((i, true) ∈ C ∧ (i, false) ∈ C)) ∧
    PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) r (PEqualNP.ProofComplexity.clausePoly C)) →
    PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem F) (r+1)) := by
  intro n r F hr _ width bad cover
  apply PEqualNP.Outside.L_lib_500.finish hr width bad
  intro S hS
  obtain ⟨C,hsub,hcons,hd⟩ := cover S hS
  obtain ⟨q,hq,e⟩ := PEqualNP.Outside.L_lib_500.Cover.main n F S C
    (Finset.card_pos.mp (by omega)) hsub hcons (hS ▸ hd)
  refine ⟨q, by omega, ?_⟩
  exact PEqualNP.Outside.L_lib_500.pcDerivable_mono e (by omega) (by rfl)
