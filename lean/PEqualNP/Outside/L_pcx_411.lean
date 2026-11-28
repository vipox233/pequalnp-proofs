import PEqualNP.Defs
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.FieldTheory.Finite.Polynomial

open scoped BigOperators

namespace PEqualNP.Outside.L_pcx_411

namespace Product411

open MvPolynomial PEqualNP.ProofComplexity

variable {σ : Type}

-- Multiplication helpers adapted from PEqualNP.ProofComplexity.Helpers.PCToolkit.
/-- Monotonicity of polynomial calculus in the axioms and in the degree bound. -/
theorem pcDerivable_mono {F F' : Set (MvPolynomial σ (ZMod 2))} {B B' : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (hB : B ≤ B') (hF : F ⊆ F') :
    PCDerivable F' B' p := by
  induction h with
  | ax hp hdeg => exact .ax (hF hp) (hdeg.trans hB)
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hB)

/-- Multiplication of a derived line by a monomial, inside a fixed degree bound. -/
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

/-- Finite sums of derived lines are derived. -/
theorem pcDerivable_sum {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ} {ι : Type}
    (s : Finset ι) (f : ι → MvPolynomial σ (ZMod 2)) (h : ∀ i ∈ s, PCDerivable F B (f i)) :
    PCDerivable F B (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCDerivable.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact .add (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- Multiplication of a derived line by an arbitrary polynomial: the degree bound grows to
at most the sum of the two degrees. -/
theorem pcDerivable_mul_left {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {g : MvPolynomial σ (ZMod 2)} (hg : PCDerivable F B g) (q : MvPolynomial σ (ZMod 2)) :
    PCDerivable F (max B (q.totalDegree + g.totalDegree)) (q * g) := by
  have hg' : PCDerivable F (max B (q.totalDegree + g.totalDegree)) g :=
    pcDerivable_mono hg (le_max_left _ _) subset_rfl
  have hq : q * g = ∑ a ∈ q.support, monomial a (q.coeff a) * g := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_mul]
  rw [hq]
  refine pcDerivable_sum _ _ fun a ha => ?_
  have hc : q.coeff a = 1 := by
    have h0 : q.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize q.coeff a = c at h0
    revert h0; revert c; decide
  rw [hc]
  refine pcDerivable_monomial_mul a hg' ?_
  have : (a.sum fun _ e => e) ≤ q.totalDegree := le_totalDegree ha
  exact (Nat.add_le_add_right this _).trans (le_max_right _ _)

-- The contextual product induction follows the checked L-pcx-382 proof.
abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

private theorem degree_line {V : Type} {A : Set (Poly V)} {d : ℕ} {p : Poly V}
    (h : PCDerivable A d p) : p.totalDegree ≤ d := by
  induction h with
  | ax _ h => exact h
  | zero => simp
  | add _ _ ih₁ ih₂ => exact (totalDegree_add _ _).trans (max_le ih₁ ih₂)
  | mulX _ _ h _ => exact h

private theorem degree_product {V ι : Type} (S : Finset ι) (p : ι → Poly V) :
    (∏ i ∈ S, p i).totalDegree ≤ ∑ i ∈ S, (p i).totalDegree := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (totalDegree_mul _ _).trans (Nat.add_le_add_left ih _)

private theorem with_factor {V : Type} {A F : Set (Poly V)} {d B : ℕ}
    (q : Poly V) (hq : q.totalDegree + d ≤ B)
    (base : ∀ p ∈ A, p.totalDegree ≤ d → PCDerivable F B (q * p))
    {p : Poly V} (h : PCDerivable A d p) : PCDerivable F B (q * p) := by
  induction h with
  | ax hp hd => exact base _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable F B 0)
  | add _ _ ih₁ ih₂ =>
    rw [mul_add]
    exact .add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [mul_left_comm q (X j)]
    apply PCDerivable.mulX j ih
    rw [← mul_left_comm q (X j)]
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add_left hd _).trans hq)

private theorem derive_products {V : Type} {F : Set (Poly V)} {B : ℕ} :
    ∀ (t : ℕ) (A : Fin t → Set (Poly V)) (D : Fin t → ℕ) (q : Poly V)
      (p : Fin t → Poly V), (∀ i, PCDerivable (A i) (D i) (p i)) →
      q.totalDegree + (∑ i, D i) ≤ B →
      (∀ f : Fin t → Poly V, (∀ i, f i ∈ A i ∧ (f i).totalDegree ≤ D i) →
        PCDerivable F B (q * ∏ i, f i)) →
      PCDerivable F B (q * ∏ i, p i) := by
  intro t
  induction t with
  | zero =>
    intro A D q p _ _ base
    exact base p (fun i => Fin.elim0 i)
  | succ t ih =>
    intro A D q p deriv hp base
    rw [Fin.sum_univ_succ] at hp
    let r : Poly V := ∏ i : Fin t, p i.succ
    have r_bound : r.totalDegree ≤ ∑ i : Fin t, D i.succ :=
      (degree_product Finset.univ (fun i : Fin t => p i.succ)).trans
        (Finset.sum_le_sum fun i _ => degree_line (deriv i.succ))
    have qr_bound : (q*r).totalDegree + D 0 ≤ B := by
      have h := totalDegree_mul q r
      omega
    rw [Fin.prod_univ_succ, ← mul_assoc]
    change PCDerivable F B ((q * p 0) * r)
    rw [mul_right_comm]
    apply with_factor (q*r) qr_bound _ (deriv 0)
    intro a ha da
    have qa_bound : (q*a).totalDegree + (∑ i : Fin t, D i.succ) ≤ B := by
      have h := totalDegree_mul q a
      omega
    have suffix := ih (fun i => A i.succ) (fun i => D i.succ) (q*a)
      (fun i => p i.succ) (fun i => deriv i.succ) qa_bound (by
        intro f hf
        let full : Fin (t+1) → Poly V := Fin.cons a f
        have hfull (j : Fin (t+1)) : full j ∈ A j ∧ (full j).totalDegree ≤ D j := by
          refine Fin.cases ?_ (fun i => ?_) j
          · simpa [full] using And.intro ha da
          · simpa [full] using hf i
        simpa only [full, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, ← mul_assoc]
          using base full hfull)
    simpa only [r, mul_right_comm q a] using suffix

theorem offending {V : Type} (F : Set (Poly V)) {t B : ℕ} (E : Fin t → Set (Poly V))
    (D : Fin t → ℕ) (p : Poly V) (degree : p.totalDegree + (∑ j, D j) ≤ B)
    (branches : ∀ j, PCRefutable (F ∪ E j) (D j)) (notDeriv : ¬ PCDerivable F B p) :
    ∃ e : Fin t → Poly V, (∀ j, e j ∈ E j ∧ (e j).totalDegree ≤ D j) ∧
      ¬ PCDerivable F B (p * ∏ j, e j) := by
  classical
  by_contra noWitness
  apply notDeriv
  have base (e : Fin t → Poly V) (he : ∀ j, e j ∈ F ∪ E j ∧ (e j).totalDegree ≤ D j) :
      PCDerivable F B (p * ∏ j, e j) := by
    by_cases hasBase : ∃ i, e i ∈ F
    · obtain ⟨i,hi⟩ := hasBase
      let I := (Finset.univ : Finset (Fin t)).erase i
      let q := ∏ j ∈ I, e j
      have costs : (∑ j ∈ I, D j) + D i = ∑ j, D j :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i)
      have qDegree : q.totalDegree ≤ ∑ j ∈ I, D j :=
        (degree_product I e).trans (Finset.sum_le_sum fun j _ => (he j).2)
      have eDegree := (he i).2
      have pq := totalDegree_mul p q
      have deriv := pcDerivable_mul_left (PCDerivable.ax hi eDegree) (p*q)
      have enough : max (D i) ((p*q).totalDegree+(e i).totalDegree) ≤ B :=
        max_le (by omega) (by omega)
      have result := pcDerivable_mono deriv enough (fun _ h => h)
      rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at result
      exact result
    · have allExtra (i : Fin t) : e i ∈ E i ∧ (e i).totalDegree ≤ D i :=
        ⟨((he i).1).resolve_left (fun hi => hasBase ⟨i,hi⟩), (he i).2⟩
      by_contra bad
      exact noWitness ⟨e,allExtra,bad⟩
  have result := derive_products t (fun i => F ∪ E i) D p (fun _ => 1) branches degree base
  simpa using result

end Product411

namespace Vanish411

open MvPolynomial PEqualNP.ProofComplexity Product411

variable {σ : Type}

-- Soundness proof adapted from PEqualNP.ProofComplexity.Helpers.PCToolkit.
/-- Soundness of polynomial calculus: a common zero of the axioms is a zero of every derived
line. -/
private theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

-- Boolean multilinearization and cube-vanishing proof adapted from
-- PEqualNP.ProofComplexity.Helpers.BoolVanish in the upstream PequalNP repository.

/-- The Boolean axioms. -/
private noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

/-- Clamp every exponent to at most `1`. -/
private noncomputable def mlin (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.mapRange (fun n => min n 1) (by simp) a

private theorem mlin_apply (a : σ →₀ ℕ) (v : σ) : mlin a v = min (a v) 1 := by
  simp [mlin]

private theorem boolDerivable_monomial (d : ℕ) :
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

/-- A multilinear polynomial over `ZMod 2` vanishing at every point is zero. -/
private theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
    (hq : ∀ a ∈ q.support, ∀ v, a v ≤ 1) (h0 : ∀ x : σ → ZMod 2, eval x q = 0) : q = 0 := by
  classical
  obtain ⟨s, r, rfl⟩ := exists_finset_rename q
  have hinj : Function.Injective (Subtype.val : s → σ) := Subtype.val_injective
  have hr : r = 0 := by
    refine MvPolynomial.eq_zero_of_eval_eq_zero s (ZMod 2) r (fun y => ?_) ?_
    · have := h0 (fun v => if h : v ∈ s then y ⟨v, h⟩ else 0)
      rw [eval_rename] at this
      have hy : ((fun v => if h : v ∈ s then y ⟨v, h⟩ else 0) ∘ Subtype.val) = y := by
        funext w
        simp
      rwa [hy] at this
    · rw [mem_restrictDegree]
      intro c hc i
      have hc' : Finsupp.mapDomain Subtype.val c ∈ (rename Subtype.val r).support := by
        rw [mem_support_iff, coeff_rename_mapDomain _ hinj]
        exact mem_support_iff.mp hc
      have := hq _ hc' i
      rw [Finsupp.mapDomain_apply_of_injective hinj] at this
      simpa using this
  rw [hr, map_zero]

theorem vanish_derivable : ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (d : ℕ) (p : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → p.totalDegree ≤ d → (∀ x : σ → ZMod 2, MvPolynomial.eval x p = 0) → PEqualNP.ProofComplexity.PCDerivable F d p := by
  classical
  intro σ F d p hF hd hvan
  set p' : MvPolynomial σ (ZMod 2) :=
    ∑ a ∈ p.support, monomial (mlin a) (p.coeff a) with hp'
  have hcoeff : ∀ a ∈ p.support, p.coeff a = 1 := by
    intro a ha
    have h0 : p.coeff a ≠ 0 := mem_support_iff.mp ha
    generalize p.coeff a = c at h0
    revert h0; revert c; decide
  have hder : PCDerivable (boolAxioms σ) d (p + p') := by
    have : p + p' = ∑ a ∈ p.support, (monomial a 1 + monomial (mlin a) 1) := by
      conv_lhs => rw [p.as_sum]
      rw [hp', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [hcoeff a ha]
    rw [this]
    refine pcDerivable_sum _ _ fun a ha => boolDerivable_monomial d _ a rfl ?_
    exact (le_totalDegree ha).trans hd
  have hbool : ∀ x : σ → ZMod 2, ∀ f ∈ boolAxioms σ, eval x f = 0 := by
    rintro x f ⟨v, rfl⟩
    simp only [map_add, map_mul, eval_X]
    generalize x v = c
    revert c; decide
  have hp'0 : p' = 0 := by
    refine eq_zero_of_multilinear p' ?_ ?_
    · intro c hc v
      obtain ⟨a, -, hca⟩ := Finset.mem_biUnion.mp (support_sum hc)
      rw [support_monomial] at hca
      split_ifs at hca
      · simp at hca
      · rw [Finset.mem_singleton.mp hca, mlin_apply]; omega
    · intro x
      have h1 := pcDerivable_eval_eq_zero hder x (hbool x)
      rwa [map_add, hvan x, zero_add] at h1
  have hpp : p = p + p' := by rw [hp'0, add_zero]
  rw [hpp]
  refine pcDerivable_mono hder le_rfl ?_
  rintro f ⟨v, rfl⟩
  exact hF v

end Vanish411

namespace Face411

abbrev F := ZMod 2

def face {V : Type} [Fintype V] [DecidableEq V] (U : Finset V) (seed : V → F) :
    Finset (V → F) := Finset.univ.filter fun y => ∀ v ∉ U, y v = seed v

def monomial {V : Type} (S : Finset V) (y : V → F) : F := ∏ v ∈ S, y v

def eval {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → F)
    (y : V → F) : F := ∑ S : Finset V, coeff S * monomial S y

theorem mem_face {V : Type} [Fintype V] [DecidableEq V] (U : Finset V) (seed y : V → F) :
    y ∈ face U seed ↔ ∀ v ∉ U, y v = seed v := by
  simp [face]

private theorem binary : ∀ x : F, x = 0 ∨ x = 1 := by decide +kernel

private theorem face_prod {V : Type} [Fintype V] [DecidableEq V]
    (U S : Finset V) (seed : V → F) :
    (∑ y ∈ face U seed, monomial S y) =
      ∏ v : V, ∑ a ∈ (if v ∈ U then Finset.univ else {seed v}), if v ∈ S then a else 1 := by
  let allowed (v : V) : Finset F := if v ∈ U then Finset.univ else {seed v}
  have hf : face U seed = Fintype.piFinset allowed := by
    ext y
    rw [mem_face, Fintype.mem_piFinset]
    constructor
    · intro hy v
      by_cases hv : v ∈ U
      · simp [allowed, hv]
      · simp [allowed, hv, hy v hv]
    · intro hy v hv
      simpa [allowed, hv] using hy v
  rw [hf, Finset.prod_univ_sum]
  simp [monomial, allowed]

private theorem face_vanishes {V : Type} [Fintype V] [DecidableEq V]
    (U S : Finset V) (seed : V → F) (h : ¬ U ⊆ S) :
    (∑ y ∈ face U seed, monomial S y) = 0 := by
  obtain ⟨v,hv,hs⟩ := Finset.not_subset.mp h
  rw [face_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ v)
  have ht : (∑ _ : F, (1 : F)) = 0 := by decide +kernel
  simpa [hv, hs] using ht

private theorem face_top {V : Type} [Fintype V] [DecidableEq V]
    (U : Finset V) (seed : V → F) : (∑ y ∈ face U seed, monomial U y) = 1 := by
  rw [face_prod]
  apply Finset.prod_eq_one
  intro v _
  by_cases hv : v ∈ U
  · have ht : (∑ a : F, a) = 1 := by decide +kernel
    simpa [hv] using ht
  · simp [hv]

theorem face_sum {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → F)
    (U : Finset V) (hU : coeff U ≠ 0) (hmax : ∀ S, coeff S ≠ 0 → S.card ≤ U.card)
    (seed : V → F) : (∑ y ∈ face U seed, eval coeff y) = 1 := by
  unfold eval
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_eq_single U]
  · rw [face_top, (binary _).resolve_left hU, mul_one]
  · intro S _ hSU
    by_cases hc : coeff S = 0
    · rw [hc, zero_mul]
    · have sub : ¬ U ⊆ S := fun hs => hSU (Finset.eq_of_subset_of_card_le hs (hmax S hc)).symm
      rw [face_vanishes U S seed sub, mul_zero]
  · simp

theorem odd_of_face_sum {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → F)
    (U : Finset V) (seed : V → F) (h : (∑ y ∈ face U seed, eval coeff y) = 1) :
    Odd (((face U seed).filter fun y => eval coeff y = 1).card) := by
  have heq : (((face U seed).filter fun y => eval coeff y = 1).card : F) =
      ∑ y ∈ face U seed, eval coeff y := by
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro y _
    rcases binary (eval coeff y) with he | he <;> simp [he]
  exact ZMod.natCast_eq_one_iff_odd.mp (heq.trans h)

theorem odd_face {V : Type} [Fintype V] [DecidableEq V] (coeff : Finset V → F)
    (h : ∃ S, coeff S ≠ 0) : ∃ U, coeff U ≠ 0 ∧
      (∀ S, coeff S ≠ 0 → S.card ≤ U.card) ∧
      ∀ seed, Odd (((face U seed).filter fun y => eval coeff y = 1).card) := by
  let support := Finset.univ.filter fun S => coeff S ≠ 0
  have nonempty : support.Nonempty := by
    obtain ⟨S, hS⟩ := h
    exact ⟨S, by simp [support, hS]⟩
  obtain ⟨U, hU, hmax⟩ := Finset.exists_max_image support Finset.card nonempty
  have hn : coeff U ≠ 0 := by simpa [support] using hU
  have hb (S : Finset V) (hS : coeff S ≠ 0) : S.card ≤ U.card :=
    hmax S (by simp [support, hS])
  exact ⟨U, hn, hb, fun seed => odd_of_face_sum coeff U seed (face_sum coeff U hn hb seed)⟩

end Face411

namespace Affine411

open MvPolynomial
abbrev F := ZMod 2

private theorem substitution_degree {σ τ : Type} (φ : σ → MvPolynomial τ F) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ F) :
    (bind₁ φ p).totalDegree ≤ T * p.totalDegree := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ a.support, (φ i ^ a i).totalDegree
      ≤ ∑ i ∈ a.support, T * a i := Finset.sum_le_sum fun i _ =>
        (totalDegree_pow _ _).trans (by rw [mul_comm]; exact Nat.mul_le_mul_right _ (hφ i))
    _ = T * ∑ i ∈ a.support, a i := by rw [Finset.mul_sum]
    _ ≤ T * p.totalDegree := Nat.mul_le_mul_left _ (le_totalDegree ha)

theorem affine_pullback {V : Type} [Fintype V] [DecidableEq V] (q : MvPolynomial V F)
    (L : (V → F) ≃ₗ[F] (V → F)) (a : V → F) :
    ∃ p : MvPolynomial V F, p.totalDegree ≤ q.totalDegree ∧
      ∀ y : V → F, MvPolynomial.eval y p = MvPolynomial.eval (a + L y) q := by
  let b := Pi.basisFun F V
  let φ := fun v : V => C (a v) + ∑ u : V, C (L (b u) v) * X u
  have hφ (v : V) : (φ v).totalDegree ≤ 1 := by
    apply (totalDegree_add _ _).trans
    rw [totalDegree_C, zero_max]
    refine totalDegree_finsetSum_le fun u _ => ?_
    exact (totalDegree_mul _ _).trans (by simp)
  refine ⟨bind₁ φ q, by simpa only [one_mul] using substitution_degree φ hφ q, ?_⟩
  intro y
  have sy (v : V) : ∑ u : V, L (b u) v * y u = L y v := by
    have h := congrFun (congrArg L (b.sum_equivFun y)) v
    simpa [map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b, Pi.basisFun_equivFun,
      mul_comm] using h
  have ey (v : V) : MvPolynomial.eval y (φ v) = (a + L y) v := by
    simp [φ, map_sum, sy]
  change aeval y (bind₁ φ q) = aeval (a + L y) q
  have he : (fun v => aeval y (φ v)) = a + L y := funext ey
  rw [aeval_bind₁, he]

noncomputable def coeffs {V : Type} [DecidableEq V] (p : MvPolynomial V F) (S : Finset V) : F :=
  ∑ a ∈ p.support.filter (fun a => a.support = S), p.coeff a

theorem coeff_degree {V : Type} [DecidableEq V] (p : MvPolynomial V F) {S : Finset V}
    (hne : coeffs p S ≠ 0) : S.card ≤ p.totalDegree := by
  have hraw : (p.support.filter (fun a => a.support = S)).Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    apply hne
    rw [coeffs, he, Finset.sum_empty]
  obtain ⟨a, ha⟩ := hraw
  obtain ⟨hin, hS⟩ := Finset.mem_filter.mp ha
  rw [← hS]
  calc
    a.support.card = ∑ i ∈ a.support, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ a.support, a i := Finset.sum_le_sum fun i hi =>
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    _ ≤ p.totalDegree := le_totalDegree hin

private theorem pow_eq_self {x : F} {n : ℕ} (hn : n ≠ 0) : x^n = x := by
  have h : ∀ a : F, a = 0 ∨ a = 1 := by decide +kernel
  rcases h x with rfl | rfl
  · exact zero_pow hn
  · exact one_pow n

theorem eval_coeffs {V : Type} [Fintype V] [DecidableEq V] (p : MvPolynomial V F)
    (x : V → F) : Face411.eval (coeffs p) x = MvPolynomial.eval x p := by
  classical
  unfold Face411.eval coeffs
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ S : Finset V, ∑ a ∈ p.support.filter (fun a => a.support = S),
        p.coeff a * Face411.monomial a.support x := by
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a ∈ p.support, p.coeff a * Face411.monomial a.support x :=
      Finset.sum_fiberwise p.support Finsupp.support _
    _ = _ := by
      conv_rhs => rw [p.as_sum]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [eval_monomial]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      exact (pow_eq_self (Finsupp.mem_support_iff.mp hi)).symm

end Affine411

end PEqualNP.Outside.L_pcx_411

open PEqualNP.Outside.L_pcx_411

theorem PEqualNP.Outside.L_pcx_411 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (MvPolynomial V (ZMod 2)))
        (t B : ℕ) (E : Fin t → Set (MvPolynomial V (ZMod 2))) (D : Fin t → ℕ)
        (p : MvPolynomial V (ZMod 2)),
      let X := V → ZMod 2
      (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
      p.totalDegree + (∑ j, D j) ≤ B →
      (∀ j, PEqualNP.ProofComplexity.PCRefutable (F ∪ E j) (D j)) →
      ¬ PEqualNP.ProofComplexity.PCDerivable F B p →
      ∃ e : Fin t → MvPolynomial V (ZMod 2),
        (∀ j, e j ∈ E j ∧ (e j).totalDegree ≤ D j) ∧
        let q := p * ∏ j, e j
        ¬ PEqualNP.ProofComplexity.PCDerivable F B q ∧
        ∀ (L : X ≃ₗ[ZMod 2] X) (a : X), ∃ U : Finset V, U.card ≤ q.totalDegree ∧
          ∀ x : X, Odd ((Finset.univ.filter (fun y : X =>
            (∀ v, v ∉ U → y v = x v) ∧ MvPolynomial.eval (a + L y) q = 1)).card) := by
  intro V _ _ F t B E D p
  dsimp only
  intro hBool hBudget hBranch hHard
  obtain ⟨e, he, hn⟩ := Product411.offending F E D p hBudget hBranch hHard
  let q := p * ∏ j, e j
  have hprod : (∏ j, e j).totalDegree ≤ ∑ j, D j :=
    (Product411.degree_product Finset.univ e).trans (Finset.sum_le_sum fun j _ => (he j).2)
  have hdegree : q.totalDegree ≤ B :=
    (MvPolynomial.totalDegree_mul _ _).trans ((Nat.add_le_add_left hprod _).trans hBudget)
  obtain ⟨v, hv⟩ : ∃ v : V → ZMod 2, MvPolynomial.eval v q ≠ 0 := by
    by_contra h
    have zero (y : V → ZMod 2) : MvPolynomial.eval y q = 0 :=
      not_ne_iff.mp (not_exists.mp h y)
    exact hn (Vanish411.vanish_derivable V F B q hBool hdegree zero)
  refine ⟨e, he, hn, ?_⟩
  intro L a
  obtain ⟨r, hd, eval_r⟩ := Affine411.affine_pullback q L a
  have nonzero : ∃ S, Affine411.coeffs r S ≠ 0 := by
    by_contra h
    let y := L.symm (v-a)
    have hy : a + L y = v := by
      rw [show L y = v-a from L.apply_symm_apply _, add_comm, sub_add_cancel]
    have zero (S : Finset V) : Affine411.coeffs r S = 0 :=
      not_ne_iff.mp (not_exists.mp h S)
    have h0 : Face411.eval (Affine411.coeffs r) y = 0 := by simp [Face411.eval, zero]
    rw [Affine411.eval_coeffs, eval_r, hy] at h0
    exact hv h0
  obtain ⟨U, hU, _, hOdd⟩ := Face411.odd_face (Affine411.coeffs r) nonzero
  refine ⟨U, (Affine411.coeff_degree r hU).trans hd, ?_⟩
  intro x
  simpa only [Face411.face, Finset.filter_filter, Affine411.eval_coeffs, eval_r] using hOdd x
