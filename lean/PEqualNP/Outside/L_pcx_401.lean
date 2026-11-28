import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_pcx_401_aux

namespace Helpers

open PEqualNP.ProofComplexity


open MvPolynomial

variable {σ τ : Type}

/-- Monotonicity of polynomial calculus in the hypotheses and in the degree bound. -/
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

/-- Soundness of polynomial calculus: a common zero of the hypotheses is a zero of every derived
line. -/
theorem pcDerivable_eval_eq_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) (a : σ → ZMod 2)
    (ha : ∀ f ∈ F, eval a f = 0) : eval a p = 0 := by
  induction h with
  | ax hp _ => exact ha _ hp
  | zero => simp
  | add _ _ ih1 ih2 => simp [ih1, ih2]
  | mulX j _ _ ih => simp [ih]

/-- A refutable system has no common zero. -/
theorem pcRefutable_no_common_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (h : PCRefutable F B) : ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := pcDerivable_eval_eq_zero h a ha
  simp at this

/-- A substitution of polynomials of degree at most `T` multiplies the degree by at most
`T`. -/
theorem totalDegree_bind₁_le (φ : σ → MvPolynomial τ (ZMod 2)) {T : ℕ}
    (hφ : ∀ j, (φ j).totalDegree ≤ T) (p : MvPolynomial σ (ZMod 2)) :
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

/-- Weighted replay of a derivation under a substitution. Let `φ` substitute polynomials of
degree at most `T` for the variables and let `w` be a multiplier of degree at most `s`. If
the image `w * bind₁ φ a` of every hypothesis `a` of degree at most `D` is derivable from `G` in
degree `T * D + s`, then so is the image of every line derivable from `F` in degree `D`. -/
theorem pcDerivable_replay {F : Set (MvPolynomial σ (ZMod 2))}
    {G : Set (MvPolynomial τ (ZMod 2))} {T D s : ℕ}
    (φ : σ → MvPolynomial τ (ZMod 2)) (hφ : ∀ j, (φ j).totalDegree ≤ T)
    (w : MvPolynomial τ (ZMod 2)) (hw : w.totalDegree ≤ s)
    (hax : ∀ a ∈ F, a.totalDegree ≤ D → PCDerivable G (T * D + s) (w * bind₁ φ a))
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F D p) :
    PCDerivable G (T * D + s) (w * bind₁ φ p) := by
  induction h with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => simpa using PCDerivable.zero
  | add _ _ ih1 ih2 =>
    rw [map_add, mul_add]
    exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simpa using PCDerivable.zero
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    have hrw : w * bind₁ φ (X j * p) = φ j * (w * bind₁ φ p) := by
      rw [map_mul, bind₁_X_right]
      ring
    rw [hrw]
    have hb := totalDegree_bind₁_le φ hφ p
    have hwb : (w * bind₁ φ p).totalDegree ≤ s + T * p.totalDegree :=
      (totalDegree_mul _ _).trans (Nat.add_le_add hw hb)
    have hbound : (φ j).totalDegree + (w * bind₁ φ p).totalDegree ≤ T * D + s := by
      have h1 : T * (1 + p.totalDegree) ≤ T * D :=
        Nat.mul_le_mul_left _ (hXp ▸ hdeg)
      have h2 := hφ j
      rw [mul_add, mul_one] at h1
      omega
    have := pcDerivable_mul_left ih (φ j)
    rwa [max_eq_left hbound] at this

/-- A common zero of the bit pigeonhole system sends different pigeons to different holes. -/
theorem bitPHPSystem_injective {m l : ℕ} (a : Fin m × Fin l → ZMod 2)
    (ha : ∀ f ∈ bitPHPSystem m l, eval a f = 0) :
    Function.Injective (fun (i : Fin m) (t : Fin l) => a (i, t)) := by
  intro i i' hii
  by_contra hne
  have h := ha _ (Or.inr ⟨i, i', hne, rfl⟩)
  rw [map_prod] at h
  obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.mp h
  have hEq : a (i, t) = a (i', t) := congrFun hii t
  simp only [map_add, map_one, eval_X, hEq] at ht
  generalize a (i', t) = c at ht
  revert ht; revert c; decide

/-- With more pigeons than holes, the bit pigeonhole system has no common zero. -/
theorem bitPHPSystem_no_common_zero {m l : ℕ} (hml : 2 ^ l < m) :
    ¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ bitPHPSystem m l, eval a f = 0 := by
  rintro ⟨a, ha⟩
  have := Fintype.card_le_of_injective _ (bitPHPSystem_injective a ha)
  simp at this
  omega


end Helpers

namespace Helpers.BoolVanish


open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_401_aux.Helpers

variable {σ : Type}

/-- The Boolean hypotheses. -/
noncomputable def boolAxioms (σ : Type) : Set (MvPolynomial σ (ZMod 2)) :=
  Set.range fun v : σ => X v * X v + X v

/-- Clamp every exponent to at most `1`. -/
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

/-- A multilinear polynomial over `ZMod 2` vanishing at every point is zero. -/
theorem eq_zero_of_multilinear (q : MvPolynomial σ (ZMod 2))
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


end Helpers.BoolVanish

namespace T394


open MvPolynomial PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_401_aux.Helpers

abbrev Poly (V : Type) := MvPolynomial V (ZMod 2)

def b2z {V : Type} (x : V → Bool) : V → ZMod 2 :=
  fun v => (x v).toNat

def z2b {V : Type} (y : V → ZMod 2) : V → Bool :=
  fun v => decide (y v = 1)

lemma b2z_z2b {V : Type} (y : V → ZMod 2) : b2z (z2b y) = y := by
  funext v
  simp only [b2z, z2b]
  generalize y v = c
  revert c
  decide

lemma z2b_b2z {V : Type} (x : V → Bool) : z2b (b2z x) = x := by
  funext v
  simp only [b2z, z2b]
  have h : ∀ b : Bool, decide ((b.toNat : ZMod 2) = 1) = b := by decide
  exact h (x v)

lemma eval_bind1 {V : Type} (y : V → ZMod 2) (φ : V → Poly V) (p : Poly V) :
    eval y (bind₁ φ p) = eval (fun v => eval y (φ v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ihp => simp [map_mul, bind₁_X_right, ihp]

lemma zmod2_eq_one_of_ne_zero {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  revert hc
  revert c
  decide

lemma zmod2_add_self {V : Type} (p : Poly V) : p + p = 0 := by
  rw [← two_smul (ZMod 2) p, show (2 : ZMod 2) = 0 from rfl, zero_smul]

lemma zmod2_add_cancel_left {V : Type} (p q : Poly V) : p + (p + q) = q := by
  rw [← add_assoc, zmod2_add_self, zero_add]

lemma zmod2_add_cancel_right {V : Type} (p q : Poly V) : (p + q) + q = p := by
  rw [add_assoc, zmod2_add_self, add_zero]

lemma zmod2_mul_diff {V : Type} (P P' Q Q' : Poly V) :
    P * Q + P' * Q' = Q * (P + P') + P' * (Q + Q') := by
  have h1 : Q * (P + P') + P' * (Q + Q') = P * Q + (Q * P' + Q * P') + P' * Q' := by ring
  rw [h1, zmod2_add_self, add_zero]

lemma refutable_zero_of_sat {V : Type} {F E0 : Set (Poly V)} {a0 : V → ZMod 2}
    (hsat : ∀ e ∈ E0, eval a0 e = 0) {r : Poly V} (hr : PCDerivable (F ∪ E0) 0 r) :
    PCDerivable F 0 r := by
  induction hr with
  | @ax p hp hdeg =>
    rcases hp with hF | hE
    · exact .ax hF hdeg
    · have hC : p = C (constantCoeff p) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero hdeg)
      have hev := hsat p hE
      rw [hC, eval_C] at hev
      rw [hC, hev, map_zero]
      exact .zero
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      rw [mul_zero]
      exact .zero
    · have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
        rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
      omega

lemma pcDerivable_cut {V : Type} {G H : Set (Poly V)} {d B : ℕ}
    (hd : d ≤ B) (hax : ∀ a ∈ G, a.totalDegree ≤ d → PCDerivable H B a)
    {r : Poly V} (hr : PCDerivable G d r) : PCDerivable H B r := by
  induction hr with
  | ax hp hdeg => exact hax _ hp hdeg
  | zero => exact .zero
  | add _ _ ih1 ih2 => exact .add ih1 ih2
  | mulX j _ hdeg ih => exact .mulX j ih (hdeg.trans hd)

lemma with_factor {V : Type} {A G : Set (Poly V)} {d B : ℕ}
    (q : Poly V) (hq : q.totalDegree + d ≤ B)
    (base : ∀ p ∈ A, p.totalDegree ≤ d → PCDerivable G B (q * p))
    {p : Poly V} (h : PCDerivable A d p) : PCDerivable G B (q * p) := by
  induction h with
  | ax hp hd => exact base _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable G B 0)
  | add _ _ ih1 ih2 =>
    rw [mul_add]
    exact .add ih1 ih2
  | @mulX j r _ hd ih =>
    rw [mul_left_comm q (X j) r]
    refine .mulX j ih ?_
    rw [← mul_left_comm q (X j) r]
    exact (totalDegree_mul q (X j * r)).trans ((Nat.add_le_add_left hd _).trans hq)

lemma merge_linear_split_le {V : Type} {G : Set (Poly V)}
    (hG_bool : ∀ v : V, X v * X v + X v ∈ G)
    {g : Poly V} (hg : g.totalDegree ≤ 1)
    {d0 d1 : ℕ} (hd0 : 1 ≤ d0) (hd01 : d0 ≤ d1)
    (h0 : PCRefutable (G ∪ {g}) d0)
    (h1 : PCRefutable (G ∪ {1 + g}) d1) :
    ∃ d : ℕ, 1 ≤ d ∧ 2 ^ d ≤ 2 ^ d0 + 2 ^ d1 ∧ PCRefutable G d := by
  set d : ℕ := if d0 = d1 then d1 + 1 else d1 with hd_def
  have hd_ge1 : 1 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hd_ge2 : 2 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hd1_le : d1 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hd0_add : d0 + 1 ≤ d := by
    rw [hd_def]
    split_ifs <;> omega
  have hpow : 2 ^ d ≤ 2 ^ d0 + 2 ^ d1 := by
    rw [hd_def]
    split_ifs with heq
    · subst heq
      rw [pow_succ]
      omega
    · exact Nat.le_add_left _ _
  have h1g_deg : (1 + g).totalDegree ≤ 1 :=
    (totalDegree_add 1 g).trans (max_le (by simp) hg)
  have h1g : PCDerivable G d (1 + g) := by
    have hmul : PCDerivable G d ((1 + g) * 1) := by
      refine with_factor (1 + g) (by omega) ?_ h0
      intro p hp hdeg
      rcases hp with hpG | hpg
      · have hpa : PCDerivable G d0 p := .ax hpG hdeg
        have hpm := pcDerivable_mul_left hpa (1 + g)
        exact pcDerivable_mono hpm (max_le (by omega) (by omega)) subset_rfl
      · rw [Set.mem_singleton_iff] at hpg
        rw [hpg]
        refine BoolVanish.vanish_derivable V G d ((1 + g) * g) hG_bool ?_ ?_
        · exact (totalDegree_mul (1 + g) g).trans (by omega)
        · intro y
          simp only [map_mul, map_add, map_one]
          generalize eval y g = c
          revert c
          decide
    simpa only [mul_one] using hmul
  refine ⟨d, hd_ge1, hpow, ?_⟩
  refine pcDerivable_cut hd1_le ?_ h1
  intro a ha hdeg
  rcases ha with haG | ha1g
  · exact .ax haG (hdeg.trans hd1_le)
  · rw [Set.mem_singleton_iff] at ha1g
    subst ha1g
    exact h1g

lemma merge_linear_split {V : Type} {G : Set (Poly V)}
    (hG_bool : ∀ v : V, X v * X v + X v ∈ G)
    {g : Poly V} (hg : g.totalDegree ≤ 1)
    {d0 d1 : ℕ} (hd0 : 1 ≤ d0) (hd1 : 1 ≤ d1)
    (h0 : PCRefutable (G ∪ {g}) d0)
    (h1 : PCRefutable (G ∪ {1 + g}) d1) :
    ∃ d : ℕ, 1 ≤ d ∧ 2 ^ d ≤ 2 ^ d0 + 2 ^ d1 ∧ PCRefutable G d := by
  by_cases hle : d0 ≤ d1
  · exact merge_linear_split_le hG_bool hg hd0 hle h0 h1
  · have hle' : d1 ≤ d0 := by omega
    have h1g_deg : (1 + g).totalDegree ≤ 1 :=
      (totalDegree_add 1 g).trans (max_le (by simp) hg)
    have h11g : (1 : Poly V) + (1 + g) = g := zmod2_add_cancel_left 1 g
    have h0' : PCRefutable (G ∪ {1 + (1 + g)}) d0 := by
      rwa [h11g]
    obtain ⟨d, hd, hpow, href⟩ := merge_linear_split_le hG_bool h1g_deg hd1 hle' h1 h0'
    exact ⟨d, hd, by omega, href⟩

lemma finsupp_eq_zero_or_single {V : Type} (m : V →₀ ℕ) (hm : (m.sum fun _ e => e) ≤ 1) :
    m = 0 ∨ ∃ v : V, m = Finsupp.single v 1 := by
  classical
  by_cases hm0 : m = 0
  · exact Or.inl hm0
  · right
    have hne : m.support.Nonempty := Finsupp.support_nonempty_iff.mpr hm0
    obtain ⟨v, hv⟩ := hne
    refine ⟨v, ?_⟩
    have hv1 : 1 ≤ m v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
    have hle : m v ≤ m.sum (fun _ e => e) :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hv
    have hmv : m v = 1 := by omega
    ext w
    by_cases hw : w = v
    · subst hw
      simp [hmv]
    · rw [Finsupp.single_eq_of_ne hw]
      by_contra hmw
      have hws : w ∈ m.support := Finsupp.mem_support_iff.mpr hmw
      have hsub : ({v, w} : Finset V) ⊆ m.support := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl <;> assumption
      have hpair : m v + m w ≤ ∑ u ∈ m.support, m u := by
        have hsum : ∑ u ∈ ({v, w} : Finset V), m u ≤ ∑ u ∈ m.support, m u :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair (Ne.symm hw)] at hsum
      have hmw1 : 1 ≤ m w := Nat.pos_of_ne_zero hmw
      have hmsum : m.sum (fun _ e => e) = ∑ u ∈ m.support, m u := rfl
      omega

lemma deg_le_one_add_bind1 {V : Type} {G : Set (Poly V)} {B : ℕ}
    (φ : V → Poly V) (hφ : ∀ v : V, PCDerivable G B (X v + φ v))
    {h : Poly V} (hh : h.totalDegree ≤ 1) :
    PCDerivable G B (h + bind₁ φ h) := by
  have heq : h + bind₁ φ h = ∑ m ∈ h.support, (monomial m (h.coeff m) + bind₁ φ (monomial m (h.coeff m))) := by
    conv_lhs => rw [h.as_sum]
    rw [map_sum, ← Finset.sum_add_distrib]
  rw [heq]
  refine pcDerivable_sum _ _ fun m hm => ?_
  have hc : h.coeff m = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hm)
  rw [hc]
  have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans hh
  rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨v, rfl⟩
  · have h1 : (monomial (0 : V →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [h1, map_one, zmod2_add_self]
    exact .zero
  · have hx : (monomial (Finsupp.single v 1) (1 : ZMod 2)) = X v := rfl
    rw [hx, bind₁_X_right]
    exact hφ v

lemma elim_affine {V : Type} :
    ∀ (k : ℕ) (A : Finset (Poly V)), A.card = k →
      (∀ g ∈ A, g.totalDegree ≤ 1) →
      PCDerivable (A : Set (Poly V)) 1 1 ∨
      ∃ φ : V → Poly V,
        (∀ v : V, (φ v).totalDegree ≤ 1) ∧
        (∀ v : V, PCDerivable (A : Set (Poly V)) 1 (X v + φ v)) ∧
        (∀ y : V → ZMod 2, ∀ g ∈ A, eval (fun v => eval y (φ v)) g = 0) := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro A hcard hA
  by_cases hnz : ∃ g ∈ A, g ≠ 0
  · obtain ⟨g, hgA, hg0⟩ := hnz
    by_cases hv0 : ∃ v0 : V, g.coeff (Finsupp.single v0 1) ≠ 0
    · obtain ⟨v0, hv0_ne⟩ := hv0
      have hv0_one : g.coeff (Finsupp.single v0 1) = 1 := zmod2_eq_one_of_ne_zero hv0_ne
      set r : Poly V := g + X v0 with hr_def
      have hr_deg : r.totalDegree ≤ 1 :=
        (totalDegree_add g (X v0)).trans (max_le (hA g hgA) (by simp))
      have hr_no_v0 : ∀ m ∈ r.support, m v0 = 0 := by
        intro m hm
        have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans hr_deg
        rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨w, rfl⟩
        · simp
        · by_cases hw : w = v0
          · subst hw
            exfalso
            have hne : r.coeff (Finsupp.single w 1) ≠ 0 := mem_support_iff.mp hm
            have hcoef : r.coeff (Finsupp.single w 1) = 0 := by
              have hadd : r.coeff (Finsupp.single w 1) =
                  g.coeff (Finsupp.single w 1) + (X w : Poly V).coeff (Finsupp.single w 1) := by
                rw [hr_def, AddMonoidAlgebra.coeff_add]
                rfl
              rw [hadd, hv0_one]
              have hcx : (X w : Poly V).coeff (Finsupp.single w 1) = 1 := by
                rw [X, coeff_monomial]
                simp
              rw [hcx]
              decide
            exact hne hcoef
          · simp [hw]
      set ψ : V → Poly V := Function.update X v0 r with hψ_def
      have hψ_deg : ∀ w : V, (ψ w).totalDegree ≤ 1 := by
        intro w
        by_cases hw : w = v0
        · subst hw
          simp [hψ_def, hr_deg]
        · simp [hψ_def, hw]
      have hbind_r : bind₁ ψ r = r := by
        conv_lhs => rw [r.as_sum]
        conv_rhs => rw [r.as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        have hc : r.coeff m = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hm)
        rw [hc]
        have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans hr_deg
        rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨w, rfl⟩
        · have h1 : (monomial (0 : V →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
          rw [h1, map_one]
        · have hne : w ≠ v0 := by
            intro heq
            subst heq
            have := hr_no_v0 (Finsupp.single w 1) hm
            simp at this
          have hx : (monomial (Finsupp.single w 1) (1 : ZMod 2)) = X w := rfl
          rw [hx, bind₁_X_right, hψ_def, Function.update_of_ne hne]
      have hg_eq : g = X v0 + r := by
        rw [hr_def, add_comm g (X v0), zmod2_add_cancel_left]
      have hbind_g : bind₁ ψ g = 0 := by
        rw [hg_eq, map_add, bind₁_X_right, hψ_def, Function.update_self, hbind_r, zmod2_add_self]
      have hψ_der : ∀ w : V, PCDerivable (A : Set (Poly V)) 1 (X w + ψ w) := by
        intro w
        by_cases hw : w = v0
        · subst hw
          rw [hψ_def, Function.update_self, ← hg_eq]
          exact .ax hgA (hA g hgA)
        · rw [hψ_def, Function.update_of_ne hw, zmod2_add_self]
          exact .zero
      set A' : Finset (Poly V) := (A.erase g).image (bind₁ ψ) with hA'_def
      have hA'_card : A'.card < k := by
        rw [← hcard, hA'_def]
        exact Finset.card_image_le.trans_lt (Finset.card_erase_lt_of_mem hgA)
      have hA'_deg : ∀ h' ∈ A', h'.totalDegree ≤ 1 := by
        intro h' hh'
        rw [hA'_def, Finset.mem_image] at hh'
        obtain ⟨h, hh, rfl⟩ := hh'
        have h1 := totalDegree_bind₁_le ψ hψ_deg h
        have h2 := hA h (Finset.mem_of_mem_erase hh)
        omega
      have hA'_der : ∀ h' ∈ A', PCDerivable (A : Set (Poly V)) 1 h' := by
        intro h' hh'
        rw [hA'_def, Finset.mem_image] at hh'
        obtain ⟨h, hh, rfl⟩ := hh'
        have hhA : h ∈ A := Finset.mem_of_mem_erase hh
        have h1 : PCDerivable (A : Set (Poly V)) 1 h := .ax hhA (hA h hhA)
        have h2 : PCDerivable (A : Set (Poly V)) 1 (h + bind₁ ψ h) :=
          deg_le_one_add_bind1 ψ hψ_der (hA h hhA)
        have h3 := PCDerivable.add h1 h2
        rwa [zmod2_add_cancel_left] at h3
      rcases ih A'.card hA'_card A' rfl hA'_deg with hleft | ⟨φ', hφ'_deg, hφ'_der, hφ'_van⟩
      · left
        exact pcDerivable_cut le_rfl (fun a ha _ => hA'_der a ha) hleft
      · right
        set φ : V → Poly V := fun w => bind₁ φ' (ψ w) with hφ_def
        have hφ'_der_A : ∀ w : V, PCDerivable (A : Set (Poly V)) 1 (X w + φ' w) := by
          intro w
          exact pcDerivable_cut le_rfl (fun a ha _ => hA'_der a ha) (hφ'_der w)
        refine ⟨φ, ?_, ?_, ?_⟩
        · intro w
          dsimp only [φ]
          have h1 := totalDegree_bind₁_le φ' hφ'_deg (ψ w)
          have h2 := hψ_deg w
          omega
        · intro w
          by_cases hw : w = v0
          · subst hw
            dsimp only [φ, ψ]
            rw [Function.update_self]
            have hr_der : PCDerivable (A : Set (Poly V)) 1 (r + bind₁ φ' r) :=
              deg_le_one_add_bind1 φ' hφ'_der_A hr_deg
            have hg_der : PCDerivable (A : Set (Poly V)) 1 (X w + r) := by
              rw [← hg_eq]
              exact .ax hgA (hA g hgA)
            have hadd := PCDerivable.add hg_der hr_der
            have hsimp : (X w + r) + (r + bind₁ φ' r) = X w + bind₁ φ' r := by
              rw [add_assoc, zmod2_add_cancel_left]
            rwa [hsimp] at hadd
          · dsimp only [φ, ψ]
            rw [Function.update_of_ne hw, bind₁_X_right]
            exact hφ'_der_A w
        · intro y h hhA
          set y' : V → ZMod 2 := fun w => eval y (φ' w) with hy'_def
          have hz_eq : (fun w => eval y (φ w)) = fun w => eval y' (ψ w) := by
            funext w
            dsimp only [φ]
            rw [eval_bind1]
          rw [hz_eq, ← eval_bind1]
          by_cases hhg : h = g
          · subst hhg
            rw [hbind_g, map_zero]
          · have hmem : bind₁ ψ h ∈ A' := by
              rw [hA'_def, Finset.mem_image]
              exact ⟨h, Finset.mem_erase.mpr ⟨hhg, hhA⟩, rfl⟩
            exact hφ'_van y (bind₁ ψ h) hmem
    · left
      push Not at hv0
      have hsupp : g.support = {0} := by
        ext m
        simp only [Finset.mem_singleton]
        constructor
        · intro hm
          have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans (hA g hgA)
          rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨v0, rfl⟩
          · rfl
          · exfalso
            exact (mem_support_iff.mp hm) (hv0 v0)
        · rintro rfl
          by_contra h0
          apply hg0
          rw [g.as_sum]
          refine Finset.sum_eq_zero fun m hm => ?_
          have hmdeg : (m.sum fun _ e => e) ≤ 1 := (le_totalDegree hm).trans (hA g hgA)
          rcases finsupp_eq_zero_or_single m hmdeg with rfl | ⟨v0, rfl⟩
          · exact False.elim (h0 hm)
          · exact False.elim ((mem_support_iff.mp hm) (hv0 v0))
      have hg1 : g = 1 := by
        rw [g.as_sum, hsupp, Finset.sum_singleton]
        have h0mem : (0 : V →₀ ℕ) ∈ g.support := by
          rw [hsupp]
          exact Finset.mem_singleton_self 0
        have hc0 : g.coeff 0 = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp h0mem)
        rw [hc0]
        rfl
      rw [← hg1]
      exact .ax hgA (hA g hgA)
  · right
    push Not at hnz
    refine ⟨X, fun v => by simp, fun v => ?_, fun y g hg => ?_⟩
    · rw [zmod2_add_self]
      exact .zero
    · rw [hnz g hg, map_zero]

lemma derive_sub_diff_monomial {V : Type} {G : Set (Poly V)} {B : ℕ} (hB : 1 ≤ B)
    (φ : V → Poly V) (hφ_deg : ∀ v : V, (φ v).totalDegree ≤ 1)
    (hφ_der : ∀ v : V, PCDerivable G 1 (X v + φ v)) :
    ∀ (m : V →₀ ℕ), (m.sum fun _ e => e) ≤ B →
      PCDerivable G B (monomial m 1 + bind₁ φ (monomial m 1)) := by
  intro m
  induction m using Finsupp.induction_linear with
  | zero =>
    intro _
    have h1 : (monomial (0 : V →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [h1, map_one, zmod2_add_self]
    exact .zero
  | add a b iha ihb =>
    intro hdeg
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)] at hdeg
    set P : Poly V := monomial a 1 with hP_def
    set Q : Poly V := monomial b 1 with hQ_def
    have hPQ : monomial (a + b) (1 : ZMod 2) = P * Q := by
      rw [hP_def, hQ_def, monomial_mul_monomial, one_mul]
    rw [hPQ, map_mul, zmod2_mul_diff P (bind₁ φ P) Q (bind₁ φ Q)]
    have hPa : P.totalDegree ≤ a.sum fun _ e => e := totalDegree_monomial_le a 1
    have hQb : Q.totalDegree ≤ b.sum fun _ e => e := totalDegree_monomial_le b 1
    have hφP : (bind₁ φ P).totalDegree ≤ a.sum fun _ e => e := by
      have := totalDegree_bind₁_le φ hφ_deg P
      omega
    have hφQ : (bind₁ φ Q).totalDegree ≤ b.sum fun _ e => e := by
      have := totalDegree_bind₁_le φ hφ_deg Q
      omega
    have hPdiff : (P + bind₁ φ P).totalDegree ≤ a.sum fun _ e => e :=
      (totalDegree_add _ _).trans (max_le hPa hφP)
    have hQdiff : (Q + bind₁ φ Q).totalDegree ≤ b.sum fun _ e => e :=
      (totalDegree_add _ _).trans (max_le hQb hφQ)
    have h1 := pcDerivable_mul_left (iha (by omega)) Q
    have h2 := pcDerivable_mul_left (ihb (by omega)) (bind₁ φ P)
    refine .add ?_ ?_
    · exact pcDerivable_mono h1 (max_le le_rfl (by omega)) subset_rfl
    · exact pcDerivable_mono h2 (max_le le_rfl (by omega)) subset_rfl
  | single v n =>
    induction n with
    | zero =>
      intro _
      have h1 : (monomial (Finsupp.single v 0) (1 : ZMod 2)) = 1 := by simp
      rw [h1, map_one, zmod2_add_self]
      exact .zero
    | succ n ihn =>
      intro hdeg
      have hd1 : ((Finsupp.single v (n + 1)).sum fun _ e => e) = n + 1 :=
        Finsupp.sum_single_index rfl
      have hd0 : ((Finsupp.single v n).sum fun _ e => e) = n :=
        Finsupp.sum_single_index rfl
      rw [hd1] at hdeg
      set Q : Poly V := monomial (Finsupp.single v n) 1 with hQ_def
      have hXQ : monomial (Finsupp.single v (n + 1)) (1 : ZMod 2) = X v * Q := by
        rw [hQ_def, X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, add_comm 1 n]
      rw [hXQ, map_mul, bind₁_X_right, zmod2_mul_diff (X v) (φ v) Q (bind₁ φ Q)]
      have hQn : Q.totalDegree ≤ n := (totalDegree_monomial_le _ 1).trans_eq hd0
      have hφQ : (bind₁ φ Q).totalDegree ≤ n := by
        have := totalDegree_bind₁_le φ hφ_deg Q
        omega
      have hXφ : (X v + φ v).totalDegree ≤ 1 :=
        (totalDegree_add (X v) (φ v)).trans (max_le (by simp) (hφ_deg v))
      have hQdiff : (Q + bind₁ φ Q).totalDegree ≤ n :=
        (totalDegree_add _ _).trans (max_le hQn hφQ)
      have h1 := pcDerivable_mul_left (pcDerivable_mono (hφ_der v) hB subset_rfl) Q
      have h2 := pcDerivable_mul_left (ihn (by omega)) (φ v)
      have hφv := hφ_deg v
      refine .add ?_ ?_
      · exact pcDerivable_mono h1 (max_le le_rfl (by omega)) subset_rfl
      · exact pcDerivable_mono h2 (max_le le_rfl (by omega)) subset_rfl

lemma derive_sub_diff {V : Type} {G : Set (Poly V)} {B : ℕ} (hB : 1 ≤ B)
    (φ : V → Poly V) (hφ_deg : ∀ v : V, (φ v).totalDegree ≤ 1)
    (hφ_der : ∀ v : V, PCDerivable G 1 (X v + φ v))
    {e : Poly V} (he : e.totalDegree ≤ B) :
    PCDerivable G B (e + bind₁ φ e) := by
  have heq : e + bind₁ φ e = ∑ m ∈ e.support, (monomial m 1 + bind₁ φ (monomial m 1)) := by
    conv_lhs => rw [e.as_sum]
    rw [map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hc : e.coeff m = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp hm)
    rw [hc]
  rw [heq]
  refine pcDerivable_sum _ _ fun m hm =>
    derive_sub_diff_monomial hB φ hφ_deg hφ_der m ((le_totalDegree hm).trans he)

lemma leaf_refutable {V : Type} {F E0 : Set (Poly V)} {d : ℕ}
    (hF_bool : ∀ v : V, X v * X v + X v ∈ F)
    (hd : 1 ≤ d)
    (href : PCRefutable (F ∪ E0) d)
    (A : Finset (Poly V))
    (hA_deg : ∀ g ∈ A, g.totalDegree ≤ 1)
    (hE0_van : ∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) → ∀ e ∈ E0, eval y e = 0) :
    PCRefutable (F ∪ (A : Set (Poly V))) d := by
  rcases elim_affine A.card A rfl hA_deg with hleft | ⟨φ, hφ_deg, hφ_der, hφ_van⟩
  · exact pcDerivable_mono hleft hd Set.subset_union_right
  · refine pcDerivable_cut le_rfl ?_ href
    intro e he hdeg
    rcases he with heF | heE
    · exact .ax (Or.inl heF) hdeg
    · have hφ_der' : ∀ v : V, PCDerivable (F ∪ (A : Set (Poly V))) 1 (X v + φ v) :=
        fun v => pcDerivable_mono (hφ_der v) le_rfl Set.subset_union_right
      have hdiff : PCDerivable (F ∪ (A : Set (Poly V))) d (e + bind₁ φ e) :=
        derive_sub_diff hd φ hφ_deg hφ_der' hdeg
      have hbind_deg : (bind₁ φ e).totalDegree ≤ d := by
        have := totalDegree_bind₁_le φ hφ_deg e
        omega
      have hbind_van : ∀ y : V → ZMod 2, eval y (bind₁ φ e) = 0 := by
        intro y
        rw [eval_bind1]
        exact hE0_van (fun v => eval y (φ v)) (hφ_van y) e heE
      have hbind_der : PCDerivable (F ∪ (A : Set (Poly V))) d (bind₁ φ e) :=
        pcDerivable_mono
          (BoolVanish.vanish_derivable V F d (bind₁ φ e) hF_bool hbind_deg hbind_van)
          le_rfl Set.subset_union_left
      have hadd := PCDerivable.add hdiff hbind_der
      rwa [zmod2_add_cancel_right] at hadd

noncomputable def linPoly {V : Type} (e : LinEq V) : Poly V :=
  (∑ v ∈ e.1, X v) + C ((e.2).toNat : ZMod 2)

lemma totalDegree_linPoly {V : Type} (e : LinEq V) : (linPoly e).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · refine totalDegree_finsetSum_le fun v _ => ?_
    simp
  · rw [totalDegree_C]
    exact Nat.zero_le 1

lemma eval_linPoly_eq_zero_iff {V : Type} (y : V → ZMod 2) (e : LinEq V) :
    eval y (linPoly e) = 0 ↔ LinEqSat (z2b y) e := by
  classical
  have hsum : eval y (∑ v ∈ e.1, (X v : Poly V)) =
      ((e.1.filter (fun v => z2b y v = true)).card : ZMod 2) := by
    rw [map_sum]
    have hterm : ∀ v ∈ e.1, eval y (X v : Poly V) =
        if z2b y v = true then (1 : ZMod 2) else 0 := by
      intro v _
      rw [eval_X]
      simp only [z2b]
      have h : ∀ c : ZMod 2, c = if decide (c = 1) = true then (1 : ZMod 2) else 0 := by decide
      exact h (y v)
    rw [Finset.sum_congr rfl hterm, Finset.sum_boole]
  simp only [linPoly, map_add, eval_C, hsum, LinEqSat]
  set n : ℕ := (e.1.filter (fun v => z2b y v = true)).card with hn_def
  have hcast : (n : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    push_cast
    rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]
  rw [hcast, Nat.odd_iff]
  have hlt : n % 2 < 2 := Nat.mod_lt n (by decide)
  rcases e.2 with _ | _
  · interval_cases (n % 2) <;> decide
  · interval_cases (n % 2) <;> decide

lemma eval_one_add_linPoly_eq_zero_iff {V : Type} (y : V → ZMod 2) (e : LinEq V) :
    eval y (1 + linPoly e) = 0 ↔ ¬ LinEqSat (z2b y) e := by
  rw [← eval_linPoly_eq_zero_iff y e, map_add, map_one]
  generalize eval y (linPoly e) = c
  revert c
  decide

lemma merge_linTerm_list {V : Type} (S_false S_true : ℕ) :
    ∀ (L : List (LinEq V)), L ≠ [] →
      ∀ (G : Set (Poly V)), (∀ v : V, X v * X v + X v ∈ G) →
      (∃ d_t, 1 ≤ d_t ∧ 2 ^ d_t ≤ S_true ∧
        PCRefutable (G ∪ {p | ∃ e ∈ L, p = linPoly e}) d_t) →
      (∀ k : Fin L.length, ∃ d_f, 1 ≤ d_f ∧ 2 ^ d_f ≤ S_false ∧
        PCRefutable (G ∪ {p | ∃ e ∈ L.take k.val, p = linPoly e} ∪ {1 + linPoly (L.get k)}) d_f) →
      ∃ d, 1 ≤ d ∧ 2 ^ d ≤ L.length * S_false + S_true ∧ PCRefutable G d := by
  intro L
  induction L with
  | nil =>
    intro hne
    exact False.elim (hne rfl)
  | cons e rest ih =>
    intro _ G hG_bool htrue hfalse
    by_cases hrest : rest = []
    · subst hrest
      obtain ⟨d_t, hdt1, hdt_pow, hdt_ref⟩ := htrue
      obtain ⟨d_f, hdf1, hdf_pow, hdf_ref⟩ := hfalse ⟨0, by simp⟩
      have ht_set : G ∪ {p | ∃ e' ∈ [e], p = linPoly e'} = G ∪ {linPoly e} := by
        ext p
        simp
      have hf_set : G ∪ {p | ∃ e' ∈ List.take 0 [e], p = linPoly e'} ∪
          {1 + linPoly ([e].get ⟨0, by simp⟩)} = G ∪ {1 + linPoly e} := by
        ext p
        simp
      rw [ht_set] at hdt_ref
      rw [hf_set] at hdf_ref
      obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
        merge_linear_split hG_bool (totalDegree_linPoly e) hdt1 hdf1 hdt_ref hdf_ref
      refine ⟨d, hd1, ?_, hd_ref⟩
      simp only [List.length_singleton, one_mul]
      omega
    · set G' : Set (Poly V) := G ∪ {linPoly e} with hG'_def
      have hG'_bool : ∀ v : V, X v * X v + X v ∈ G' := fun v => Or.inl (hG_bool v)
      have htrue' : ∃ d_t, 1 ≤ d_t ∧ 2 ^ d_t ≤ S_true ∧
          PCRefutable (G' ∪ {p | ∃ e' ∈ rest, p = linPoly e'}) d_t := by
        obtain ⟨d_t, hdt1, hdt_pow, hdt_ref⟩ := htrue
        refine ⟨d_t, hdt1, hdt_pow, ?_⟩
        have hset : G' ∪ {p | ∃ e' ∈ rest, p = linPoly e'} =
            G ∪ {p | ∃ e' ∈ e :: rest, p = linPoly e'} := by
          ext p
          simp only [hG'_def, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq,
            List.mem_cons]
          constructor
          · rintro ((hG | rfl) | ⟨e', he', rfl⟩)
            · exact Or.inl hG
            · exact Or.inr ⟨e, Or.inl rfl, rfl⟩
            · exact Or.inr ⟨e', Or.inr he', rfl⟩
          · rintro (hG | ⟨e', rfl | he', rfl⟩)
            · exact Or.inl (Or.inl hG)
            · exact Or.inl (Or.inr rfl)
            · exact Or.inr ⟨e', he', rfl⟩
        rwa [hset]
      have hfalse' : ∀ k : Fin rest.length, ∃ d_f, 1 ≤ d_f ∧ 2 ^ d_f ≤ S_false ∧
          PCRefutable (G' ∪ {p | ∃ e' ∈ rest.take k.val, p = linPoly e'} ∪
            {1 + linPoly (rest.get k)}) d_f := by
        intro k
        obtain ⟨d_f, hdf1, hdf_pow, hdf_ref⟩ := hfalse k.succ
        refine ⟨d_f, hdf1, hdf_pow, ?_⟩
        have hset : G' ∪ {p | ∃ e' ∈ rest.take k.val, p = linPoly e'} ∪
              {1 + linPoly (rest.get k)} =
            G ∪ {p | ∃ e' ∈ (e :: rest).take k.succ.val, p = linPoly e'} ∪
              {1 + linPoly ((e :: rest).get k.succ)} := by
          ext p
          simp only [hG'_def, Fin.val_succ, List.take_succ_cons,
            Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons]
          constructor
          · rintro (((hG | rfl) | ⟨e', he', rfl⟩) | h1)
            · exact Or.inl (Or.inl hG)
            · exact Or.inl (Or.inr ⟨e, Or.inl rfl, rfl⟩)
            · exact Or.inl (Or.inr ⟨e', Or.inr he', rfl⟩)
            · exact Or.inr h1
          · rintro ((hG | ⟨e', rfl | he', rfl⟩) | h1)
            · exact Or.inl (Or.inl (Or.inl hG))
            · exact Or.inl (Or.inl (Or.inr rfl))
            · exact Or.inl (Or.inr ⟨e', he', rfl⟩)
            · exact Or.inr h1
        rwa [hset]
      obtain ⟨d1, hd1_1, hd1_pow, hd1_ref⟩ := ih hrest G' hG'_bool htrue' hfalse'
      obtain ⟨d0, hd0_1, hd0_pow, hd0_ref⟩ := hfalse ⟨0, by simp⟩
      have hf0_set : G ∪ {p | ∃ e' ∈ List.take 0 (e :: rest), p = linPoly e'} ∪
          {1 + linPoly ((e :: rest).get ⟨0, by simp⟩)} = G ∪ {1 + linPoly e} := by
        ext p
        simp
      rw [hf0_set] at hd0_ref
      obtain ⟨d, hd_1, hd_pow, hd_ref⟩ :=
        merge_linear_split hG_bool (totalDegree_linPoly e) hd1_1 hd0_1 hd1_ref hd0_ref
      refine ⟨d, hd_1, ?_, hd_ref⟩
      simp only [List.length_cons, Nat.add_mul, one_mul]
      omega

def follows {V : Type} (ask : List Bool → LinTerm V) (p : List Bool) (x : V → Bool) : Prop :=
  ∀ i : Fin p.length, p.get i = true ↔ LinTermSat x (ask (p.take i.val))

lemma follows_of_isPrefix {V : Type} {ask : List Bool → LinTerm V} {r p : List Bool} {x : V → Bool}
    (hrp : List.IsPrefix r p) (hp : follows ask p x) : follows ask r x := by
  obtain ⟨t, rfl⟩ := hrp
  intro i
  have hi : i.val < (r ++ t).length := Nat.lt_of_lt_of_le i.isLt (by simp)
  have h1 := hp ⟨i.val, hi⟩
  have hget : (r ++ t).get ⟨i.val, hi⟩ = r.get i := by
    simp [List.get_eq_getElem, List.getElem_append_left i.isLt]
  have htake : (r ++ t).take i.val = r.take i.val :=
    List.take_append_of_le_length (Nat.le_of_lt i.isLt)
  rwa [hget, htake] at h1

lemma follows_append_singleton {V : Type} {ask : List Bool → LinTerm V} {q : List Bool}
    {b : Bool} {x : V → Bool} (hq : follows ask q x)
    (hb : b = true ↔ LinTermSat x (ask q)) :
    follows ask (q ++ [b]) x := by
  intro i
  by_cases hi : i.val < q.length
  · have hget : (q ++ [b]).get i = q.get ⟨i.val, hi⟩ := by
      simp [List.get_eq_getElem, List.getElem_append_left hi]
    have htake : (q ++ [b]).take i.val = q.take i.val :=
      List.take_append_of_le_length (Nat.le_of_lt hi)
    rw [hget, htake]
    exact hq ⟨i.val, hi⟩
  · have heq : i.val = q.length := by
      have hlt := i.isLt
      simp only [List.length_append, List.length_singleton] at hlt
      omega
    have hget : (q ++ [b]).get i = b := by
      simp [List.get_eq_getElem, heq]
    have htake : (q ++ [b]).take i.val = q := by
      rw [heq, List.take_left]
    rw [hget, htake]
    exact hb

noncomputable def leavesUnder (leaves : Finset (List Bool)) (q : List Bool) :
    Finset (List Bool) := by
  classical
  exact leaves.filter (fun p => List.IsPrefix q p)

lemma mem_leavesUnder {leaves : Finset (List Bool)} {q p : List Bool} :
    p ∈ leavesUnder leaves q ↔ p ∈ leaves ∧ List.IsPrefix q p := by
  classical
  simp [leavesUnder]

lemma leavesUnder_eq_singleton {leaves : Finset (List Bool)}
    (hpfree : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    {q : List Bool} (hq : q ∈ leaves) :
    leavesUnder leaves q = {q} := by
  ext p
  rw [mem_leavesUnder, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hqp⟩
    exact (hpfree q hq p hp hqp).symm
  · rintro rfl
    exact ⟨hq, List.prefix_rfl⟩

lemma leavesUnder_disjoint {leaves : Finset (List Bool)} (q : List Bool) :
    Disjoint (leavesUnder leaves (q ++ [false])) (leavesUnder leaves (q ++ [true])) := by
  rw [Finset.disjoint_left]
  intro p hpf hpt
  rw [mem_leavesUnder] at hpf hpt
  obtain ⟨s1, hs1⟩ := hpf.2
  obtain ⟨s2, hs2⟩ := hpt.2
  have heq : q ++ (false :: s1) = q ++ (true :: s2) := by
    simpa [List.append_assoc] using hs1.trans hs2.symm
  have hcons := List.append_cancel_left heq
  simp at hcons

lemma leavesUnder_split {leaves : Finset (List Bool)} {q : List Bool} (hq : q ∉ leaves) :
    leavesUnder leaves q =
      leavesUnder leaves (q ++ [false]) ∪ leavesUnder leaves (q ++ [true]) := by
  ext p
  simp only [Finset.mem_union, mem_leavesUnder]
  constructor
  · rintro ⟨hp, hqp⟩
    obtain ⟨t, rfl⟩ := hqp
    cases t with
    | nil =>
      simp at hp
      exact False.elim (hq hp)
    | cons b t' =>
      have hpr : List.IsPrefix (q ++ [b]) (q ++ b :: t') :=
        ⟨t', by simp [List.append_assoc]⟩
      cases b
      · exact Or.inl ⟨hp, hpr⟩
      · exact Or.inr ⟨hp, hpr⟩
  · rintro (⟨hp, hqp⟩ | ⟨hp, hqp⟩)
    · exact ⟨hp, (List.prefix_append q [false]).trans hqp⟩
    · exact ⟨hp, (List.prefix_append q [true]).trans hqp⟩

lemma unique_leaf_under {V : Type} {leaves : Finset (List Bool)} {ask : List Bool → LinTerm V}
    (hpfree : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    (hcover : ∀ x : V → Bool, ∃ p ∈ leaves, follows ask p x)
    {q : List Bool} (hne : (leavesUnder leaves q).Nonempty)
    {x : V → Bool} (hq : follows ask q x) :
    ∃ p ∈ leavesUnder leaves q, follows ask p x := by
  obtain ⟨p, hp_mem, hp_fol⟩ := hcover x
  obtain ⟨p', hp'_mem⟩ := hne
  rw [mem_leavesUnder] at hp'_mem
  have hget_eq : ∀ j : ℕ, (hjp : j < p.length) → (hjq : j < q.length) → p[j] = q[j] := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjp hjq
    have htake : p.take j = q.take j := by
      refine List.ext_getElem ?_ ?_
      · simp [Nat.le_of_lt hjp, Nat.le_of_lt hjq]
      · intro t ht1 ht2
        have htj : t < j := by
          simp [Nat.le_of_lt hjp] at ht1
          exact ht1
        simp only [List.getElem_take]
        exact ih t htj (Nat.lt_trans htj hjp) (Nat.lt_trans htj hjq)
    have h1 := hp_fol ⟨j, hjp⟩
    have h2 := hq ⟨j, hjq⟩
    rw [htake] at h1
    have hiff : p[j] = true ↔ q[j] = true := by
      simpa [List.get_eq_getElem] using h1.trans h2.symm
    cases hpi : p[j] <;> cases hqi : q[j] <;> simp_all
  have hcomp : List.IsPrefix p q ∨ List.IsPrefix q p := by
    by_cases hlen : p.length ≤ q.length
    · left
      refine ⟨q.drop p.length, ?_⟩
      have htk : q.take p.length = p := by
        refine List.ext_getElem ?_ ?_
        · simp [hlen]
        · intro t ht1 ht2
          simp only [List.getElem_take]
          exact (hget_eq t ht2 (Nat.lt_of_lt_of_le ht2 hlen)).symm
      simpa only [htk] using List.take_append_drop p.length q
    · right
      have hlen' : q.length ≤ p.length := by omega
      refine ⟨p.drop q.length, ?_⟩
      have htk : p.take q.length = q := by
        refine List.ext_getElem ?_ ?_
        · simp [hlen']
        · intro t ht1 ht2
          simp only [List.getElem_take]
          exact hget_eq t (Nat.lt_of_lt_of_le ht2 hlen') ht2
      simpa only [htk] using List.take_append_drop q.length p
  rcases hcomp with hpq | hqp
  · have hpp' : List.IsPrefix p p' := hpq.trans hp'_mem.2
    have heq : p = p' := hpfree p hp_mem p' hp'_mem.1 hpp'
    refine ⟨p, mem_leavesUnder.mpr ⟨hp_mem, ?_⟩, hp_fol⟩
    rw [heq]
    exact hp'_mem.2
  · exact ⟨p, mem_leavesUnder.mpr ⟨hp_mem, hqp⟩, hp_fol⟩

def remCopies {V : Type} (ask : List Bool → LinTerm V) (k : ℕ) (p : List Bool) : ℕ :=
  ∏ i ∈ (Finset.univ : Finset (Fin p.length)).filter (fun i => k ≤ i.val),
    if p.get i then 1 else max 1 (ask (p.take i.val)).card

lemma remCopies_zero {V : Type} (ask : List Bool → LinTerm V) (p : List Bool) :
    remCopies ask 0 p =
      ∏ i : Fin p.length, if p.get i then 1 else max 1 (ask (p.take i.val)).card := by
  simp [remCopies]

lemma remCopies_self {V : Type} (ask : List Bool → LinTerm V) (p : List Bool) :
    remCopies ask p.length p = 1 := by
  unfold remCopies
  have hempty : (Finset.univ : Finset (Fin p.length)).filter (fun i => p.length ≤ i.val) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
      not_le]
    exact i.isLt
  rw [hempty, Finset.prod_empty]

lemma remCopies_step {V : Type} (ask : List Bool → LinTerm V) {q p : List Bool} {b : Bool}
    (hp : List.IsPrefix (q ++ [b]) p) :
    remCopies ask q.length p =
      (if b then 1 else max 1 (ask q).card) * remCopies ask (q.length + 1) p := by
  obtain ⟨t, rfl⟩ := hp
  have hlt : q.length < (q ++ [b] ++ t).length := by
    simp
  set i0 : Fin (q ++ [b] ++ t).length := ⟨q.length, hlt⟩
  have hfilt : (Finset.univ : Finset (Fin (q ++ [b] ++ t).length)).filter
        (fun i => q.length ≤ i.val) =
      insert i0 ((Finset.univ : Finset (Fin (q ++ [b] ++ t).length)).filter
        (fun i => q.length + 1 ≤ i.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff, i0]
    omega
  have hnotmem : i0 ∉ (Finset.univ : Finset (Fin (q ++ [b] ++ t).length)).filter
      (fun i => q.length + 1 ≤ i.val) := by
    simp [i0]
  have hget : (q ++ [b] ++ t).get i0 = b := by
    simp [i0, List.get_eq_getElem, List.append_assoc]
  have htake : (q ++ [b] ++ t).take i0.val = q := by
    simp [i0, List.append_assoc]
  unfold remCopies
  rw [hfilt, Finset.prod_insert hnotmem, hget, htake]

lemma tree_solve {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (Poly V)) (leaves : Finset (List Bool))
    (ask : List Bool → LinTerm V) (E : List Bool → Set (Poly V)) (D : List Bool → ℕ)
    (hpfree : ∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q)
    (hcover : ∀ x : V → Bool, ∃ p ∈ leaves, follows ask p x)
    (hsat : ∀ p ∈ leaves, ∃ x : V → Bool, follows ask p x)
    (hF_bool : ∀ v : V, X v * X v + X v ∈ F)
    (heval : ∀ p ∈ leaves, ∀ x : V → Bool, follows ask p x → ∀ e ∈ E p, eval (b2z x) e = 0)
    (href : ∀ p ∈ leaves, PCRefutable (F ∪ E p) (D p))
    (hDpos : ∀ p ∈ leaves, 1 ≤ D p) :
    ∀ (fuel : ℕ) (q : List Bool),
      leaves.sup List.length - q.length ≤ fuel →
      (leavesUnder leaves q).Nonempty →
      ∀ (A : Finset (Poly V)),
        (∀ g ∈ A, g.totalDegree ≤ 1) →
        (∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) → follows ask q (z2b y)) →
        ∃ d : ℕ, 1 ≤ d ∧
          2 ^ d ≤ ∑ p ∈ leavesUnder leaves q, remCopies ask q.length p * 2 ^ (D p) ∧
          PCRefutable (F ∪ (A : Set (Poly V))) d := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro q hfuel hne A hA_deg hA_fol
    obtain ⟨p0, hp0⟩ := hne
    rw [mem_leavesUnder] at hp0
    have hplen : p0.length ≤ leaves.sup List.length := Finset.le_sup hp0.1
    have hqle : q.length ≤ p0.length := hp0.2.length_le
    have hqeq : q.length = p0.length := by omega
    obtain ⟨t, ht⟩ := hp0.2
    have ht0 : t = [] := by
      have hlen : q.length + t.length = p0.length := by
        rw [← List.length_append, ht]
      have : t.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this
    subst ht0
    simp only [List.append_nil] at ht
    subst ht
    have hq_mem : q ∈ leaves := hp0.1
    rw [leavesUnder_eq_singleton hpfree hq_mem, Finset.sum_singleton, remCopies_self, one_mul]
    refine ⟨D q, hDpos q hq_mem, le_rfl, ?_⟩
    refine leaf_refutable hF_bool (hDpos q hq_mem) (href q hq_mem) A hA_deg ?_
    intro y hy e he
    have hfol := hA_fol y hy
    have h0 := heval q hq_mem (z2b y) hfol e he
    rwa [b2z_z2b] at h0
  | succ fuel ih =>
    intro q hfuel hne A hA_deg hA_fol
    by_cases hq_mem : q ∈ leaves
    · rw [leavesUnder_eq_singleton hpfree hq_mem, Finset.sum_singleton, remCopies_self, one_mul]
      refine ⟨D q, hDpos q hq_mem, le_rfl, ?_⟩
      refine leaf_refutable hF_bool (hDpos q hq_mem) (href q hq_mem) A hA_deg ?_
      intro y hy e he
      have hfol := hA_fol y hy
      have h0 := heval q hq_mem (z2b y) hfol e he
      rwa [b2z_z2b] at h0
    · set Lf := leavesUnder leaves (q ++ [false]) with hLf_def
      set Lt := leavesUnder leaves (q ++ [true]) with hLt_def
      have hsplit : leavesUnder leaves q = Lf ∪ Lt := leavesUnder_split hq_mem
      have hdisj : Disjoint Lf Lt := leavesUnder_disjoint q
      set Sf : ℕ := ∑ p ∈ Lf, remCopies ask (q.length + 1) p * 2 ^ (D p) with hSf_def
      set St : ℕ := ∑ p ∈ Lt, remCopies ask (q.length + 1) p * 2 ^ (D p) with hSt_def
      have hsum_eq :
          ∑ p ∈ leavesUnder leaves q, remCopies ask q.length p * 2 ^ (D p) =
            max 1 (ask q).card * Sf + St := by
        rw [hsplit, Finset.sum_union hdisj]
        have hLf_sum : ∑ p ∈ Lf, remCopies ask q.length p * 2 ^ (D p) =
            max 1 (ask q).card * Sf := by
          rw [hSf_def, Finset.mul_sum]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hLf_def, mem_leavesUnder] at hp
          rw [remCopies_step ask hp.2]
          simp [mul_assoc]
        have hLt_sum : ∑ p ∈ Lt, remCopies ask q.length p * 2 ^ (D p) = St := by
          rw [hSt_def]
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hLt_def, mem_leavesUnder] at hp
          rw [remCopies_step ask hp.2]
          simp
        rw [hLf_sum, hLt_sum]
      have hq_lt_sup : q.length < leaves.sup List.length := by
        obtain ⟨p0, hp0⟩ := hne
        rw [mem_leavesUnder] at hp0
        have hplen : p0.length ≤ leaves.sup List.length := Finset.le_sup hp0.1
        obtain ⟨t, rfl⟩ := hp0.2
        cases t with
        | nil =>
          simp at hp0
          exact False.elim (hq_mem hp0)
        | cons b t' =>
          simp only [List.length_append, List.length_cons] at hplen
          omega
      have hfuel' : ∀ b : Bool, leaves.sup List.length - (q ++ [b]).length ≤ fuel := by
        intro b
        simp only [List.length_append, List.length_singleton]
        omega
      by_cases hLf_ne : Lf.Nonempty
      · by_cases hLt_ne : Lt.Nonempty
        · have hask_ne : (ask q).Nonempty := by
            obtain ⟨p0, hp0⟩ := hLf_ne
            rw [hLf_def, mem_leavesUnder] at hp0
            obtain ⟨x0, hx0⟩ := hsat p0 hp0.1
            have hx0' := follows_of_isPrefix hp0.2 hx0
            have hi := hx0' ⟨q.length, by simp⟩
            have hget : (q ++ [false]).get ⟨q.length, by simp⟩ = false := by
              simp [List.get_eq_getElem]
            have htake : (q ++ [false]).take q.length = q := by
              simp
            rw [hget, htake] at hi
            by_contra hempty
            rw [Finset.not_nonempty_iff_eq_empty] at hempty
            have htr : LinTermSat x0 (ask q) := by
              rw [hempty]
              intro e he
              simp at he
            have := hi.mpr htr
            simp at this
          set L : List (LinEq V) := (ask q).toList with hL_def
          have hL_ne : L ≠ [] := by
            intro hnil
            have hcard0 : (ask q).card = 0 := by
              rw [← Finset.length_toList (s := ask q), ← hL_def, hnil, List.length_nil]
            exact hask_ne.ne_empty (Finset.card_eq_zero.mp hcard0)
          have hL_len : L.length = (ask q).card := Finset.length_toList (ask q)
          have hmax : max 1 (ask q).card = L.length := by
            have hpos : 1 ≤ (ask q).card := Finset.card_pos.mpr hask_ne
            omega
          have htrue_branch : ∃ d_t, 1 ≤ d_t ∧ 2 ^ d_t ≤ St ∧
              PCRefutable ((F ∪ (A : Set (Poly V))) ∪ {p | ∃ e ∈ L, p = linPoly e}) d_t := by
            set At : Finset (Poly V) := A ∪ (L.map linPoly).toFinset with hAt_def
            have hAt_deg : ∀ g ∈ At, g.totalDegree ≤ 1 := by
              intro g hg
              rw [hAt_def, Finset.mem_union] at hg
              rcases hg with hgA | hgL
              · exact hA_deg g hgA
              · rw [List.mem_toFinset, List.mem_map] at hgL
                obtain ⟨e, _, rfl⟩ := hgL
                exact totalDegree_linPoly e
            have hAt_fol : ∀ y : V → ZMod 2, (∀ g ∈ At, eval y g = 0) →
                follows ask (q ++ [true]) (z2b y) := by
              intro y hy
              refine follows_append_singleton
                (hA_fol y (fun g hg => hy g (Finset.mem_union_left _ hg))) ?_
              simp only [true_iff]
              intro e he
              have heL : e ∈ L := Finset.mem_toList.mpr he
              have hmem : linPoly e ∈ At := by
                rw [hAt_def]
                exact Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, heL, rfl⟩))
              exact (eval_linPoly_eq_zero_iff y e).mp (hy (linPoly e) hmem)
            obtain ⟨d_t, hdt1, hdt_pow, hdt_ref⟩ :=
              ih (q ++ [true]) (hfuel' true) hLt_ne At hAt_deg hAt_fol
            have hset : F ∪ (At : Set (Poly V)) =
                (F ∪ (A : Set (Poly V))) ∪ {p | ∃ e ∈ L, p = linPoly e} := by
              ext p
              simp only [hAt_def, Finset.coe_union, Set.mem_union, Finset.mem_coe,
                List.mem_toFinset, List.mem_map, Set.mem_ofPred_eq]
              constructor
              · rintro (hF | (hA | ⟨e, he, rfl⟩))
                · exact Or.inl (Or.inl hF)
                · exact Or.inl (Or.inr hA)
                · exact Or.inr ⟨e, he, rfl⟩
              · rintro ((hF | hA) | ⟨e, he, rfl⟩)
                · exact Or.inl hF
                · exact Or.inr (Or.inl hA)
                · exact Or.inr (Or.inr ⟨e, he, rfl⟩)
            rw [hset] at hdt_ref
            have hlen_t : (q ++ [true]).length = q.length + 1 := by simp
            rw [hlen_t] at hdt_pow
            exact ⟨d_t, hdt1, hdt_pow, hdt_ref⟩
          have hfalse_branch : ∀ k : Fin L.length, ∃ d_f, 1 ≤ d_f ∧ 2 ^ d_f ≤ Sf ∧
              PCRefutable ((F ∪ (A : Set (Poly V))) ∪
                {p | ∃ e ∈ L.take k.val, p = linPoly e} ∪
                {1 + linPoly (L.get k)}) d_f := by
            intro k
            set Af : Finset (Poly V) :=
              A ∪ ((L.take k.val).map linPoly).toFinset ∪ {1 + linPoly (L.get k)} with hAf_def
            have hAf_deg : ∀ g ∈ Af, g.totalDegree ≤ 1 := by
              intro g hg
              rw [hAf_def, Finset.mem_union, Finset.mem_union, Finset.mem_singleton] at hg
              rcases hg with (hgA | hgL) | rfl
              · exact hA_deg g hgA
              · rw [List.mem_toFinset, List.mem_map] at hgL
                obtain ⟨e, _, rfl⟩ := hgL
                exact totalDegree_linPoly e
              · exact (totalDegree_add 1 _).trans (max_le (by simp) (totalDegree_linPoly _))
            have hAf_fol : ∀ y : V → ZMod 2, (∀ g ∈ Af, eval y g = 0) →
                follows ask (q ++ [false]) (z2b y) := by
              intro y hy
              refine follows_append_singleton
                (hA_fol y (fun g hg => hy g (by rw [hAf_def]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hg)))) ?_
              simp only [Bool.false_eq_true, false_iff]
              intro hsat_term
              have hmem_e : L.get k ∈ ask q := Finset.mem_toList.mp (List.get_mem L k)
              have hsat_e : LinEqSat (z2b y) (L.get k) := hsat_term (L.get k) hmem_e
              have hmem_p : 1 + linPoly (L.get k) ∈ Af := by
                rw [hAf_def]
                exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
              have hnot := (eval_one_add_linPoly_eq_zero_iff y (L.get k)).mp (hy _ hmem_p)
              exact hnot hsat_e
            obtain ⟨d_f, hdf1, hdf_pow, hdf_ref⟩ :=
              ih (q ++ [false]) (hfuel' false) hLf_ne Af hAf_deg hAf_fol
            have hset : F ∪ (Af : Set (Poly V)) =
                (F ∪ (A : Set (Poly V))) ∪
                  {p | ∃ e ∈ L.take k.val, p = linPoly e} ∪
                  {1 + linPoly (L.get k)} := by
              ext p
              simp only [hAf_def, Finset.coe_union, Finset.coe_singleton, Set.mem_union,
                Finset.mem_coe, List.mem_toFinset, List.mem_map, Set.mem_ofPred_eq,
                Set.mem_singleton_iff]
              constructor
              · rintro (hF | ((hA | ⟨e, he, rfl⟩) | rfl))
                · exact Or.inl (Or.inl (Or.inl hF))
                · exact Or.inl (Or.inl (Or.inr hA))
                · exact Or.inl (Or.inr ⟨e, he, rfl⟩)
                · exact Or.inr rfl
              · rintro (((hF | hA) | ⟨e, he, rfl⟩) | rfl)
                · exact Or.inl hF
                · exact Or.inr (Or.inl (Or.inl hA))
                · exact Or.inr (Or.inl (Or.inr ⟨e, he, rfl⟩))
                · exact Or.inr (Or.inr rfl)
            rw [hset] at hdf_ref
            have hlen_f : (q ++ [false]).length = q.length + 1 := by simp
            rw [hlen_f] at hdf_pow
            exact ⟨d_f, hdf1, hdf_pow, hdf_ref⟩
          obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
            merge_linTerm_list Sf St L hL_ne (F ∪ (A : Set (Poly V)))
              (fun v => Or.inl (hF_bool v)) htrue_branch hfalse_branch
          refine ⟨d, hd1, ?_, hd_ref⟩
          rw [hsum_eq, hmax]
          exact hd_pow
        · rw [Finset.not_nonempty_iff_eq_empty] at hLt_ne
          have hA_fol' : ∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) →
              follows ask (q ++ [false]) (z2b y) := by
            intro y hy
            obtain ⟨p, hp_mem, hp_fol⟩ :=
              unique_leaf_under hpfree hcover hne (hA_fol y hy)
            rw [hsplit, hLt_ne, Finset.union_empty, hLf_def, mem_leavesUnder] at hp_mem
            exact follows_of_isPrefix hp_mem.2 hp_fol
          obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
            ih (q ++ [false]) (hfuel' false) hLf_ne A hA_deg hA_fol'
          have hlen_f : (q ++ [false]).length = q.length + 1 := by simp
          rw [hlen_f] at hd_pow
          refine ⟨d, hd1, ?_, hd_ref⟩
          rw [hsum_eq]
          have h1le : 1 ≤ max 1 (ask q).card := le_max_left 1 _
          calc 2 ^ d ≤ Sf := hd_pow
            _ = 1 * Sf := (one_mul Sf).symm
            _ ≤ max 1 (ask q).card * Sf := Nat.mul_le_mul_right Sf h1le
            _ ≤ max 1 (ask q).card * Sf + St := Nat.le_add_right _ _
      · rw [Finset.not_nonempty_iff_eq_empty] at hLf_ne
        have hLt_ne : Lt.Nonempty := by
          obtain ⟨p, hp⟩ := hne
          rw [hsplit, hLf_ne, Finset.empty_union] at hp
          exact ⟨p, hp⟩
        have hA_fol' : ∀ y : V → ZMod 2, (∀ g ∈ A, eval y g = 0) →
            follows ask (q ++ [true]) (z2b y) := by
          intro y hy
          obtain ⟨p, hp_mem, hp_fol⟩ :=
            unique_leaf_under hpfree hcover hne (hA_fol y hy)
          rw [hsplit, hLf_ne, Finset.empty_union, hLt_def, mem_leavesUnder] at hp_mem
          exact follows_of_isPrefix hp_mem.2 hp_fol
        obtain ⟨d, hd1, hd_pow, hd_ref⟩ :=
          ih (q ++ [true]) (hfuel' true) hLt_ne A hA_deg hA_fol'
        have hlen_t : (q ++ [true]).length = q.length + 1 := by simp
        rw [hlen_t] at hd_pow
        refine ⟨d, hd1, ?_, hd_ref⟩
        rw [hsum_eq]
        exact hd_pow.trans (Nat.le_add_left _ _)




theorem main394 : (∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (MvPolynomial V (ZMod 2)))
    (leaves : Finset (List Bool)) (ask : List Bool → PEqualNP.ProofComplexity.LinTerm V)
    (E : List Bool → Set (MvPolynomial V (ZMod 2))) (D : List Bool → ℕ),
    let follows := fun (p : List Bool) (x : V → Bool) =>
      ∀ i : Fin p.length, p.get i = true ↔
        PEqualNP.ProofComplexity.LinTermSat x (ask (p.take i.val))
    (∀ p ∈ leaves, ∀ q ∈ leaves, List.IsPrefix p q → p = q) →
    (∀ x : V → Bool, ∃ p ∈ leaves, follows p x) →
    (∀ p ∈ leaves, ∃ x : V → Bool, follows p x) →
    (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
    (∀ p ∈ leaves, ∀ x : V → Bool, follows p x → ∀ e ∈ E p,
      MvPolynomial.eval (fun v => (x v).toNat : V → ZMod 2) e = 0) →
    (∀ p ∈ leaves, PEqualNP.ProofComplexity.PCRefutable (F ∪ E p) (D p)) →
    let copies := fun p : List Bool => ∏ i : Fin p.length,
      if p.get i then 1 else max 1 (ask (p.take i.val)).card
    PEqualNP.ProofComplexity.PCRefutable F
      (Nat.log 2 (∑ p ∈ leaves, copies p * 2^(D p)))) := by
  intro V _ _ F leaves ask E D follows hpfree hcover hsat hF_bool heval href copies
  by_cases hD0 : ∃ p ∈ leaves, D p = 0
  · obtain ⟨p0, hp0, hDp0⟩ := hD0
    obtain ⟨x0, hx0⟩ := hsat p0 hp0
    have href0 : PEqualNP.ProofComplexity.PCRefutable (F ∪ E p0) 0 := hDp0 ▸ href p0 hp0
    have hF0 : PEqualNP.ProofComplexity.PCRefutable F 0 :=
      PEqualNP.Outside.L_pcx_401_aux.T394.refutable_zero_of_sat (heval p0 hp0 x0 hx0) href0
    exact PEqualNP.Outside.L_pcx_401_aux.Helpers.pcDerivable_mono hF0 (Nat.zero_le _) subset_rfl
  · push Not at hD0
    have hDpos : ∀ p ∈ leaves, 1 ≤ D p := fun p hp => Nat.pos_of_ne_zero (hD0 p hp)
    have hne : (PEqualNP.Outside.L_pcx_401_aux.T394.leavesUnder leaves []).Nonempty := by
      obtain ⟨p, hp, _⟩ := hcover (fun _ => false)
      exact ⟨p, PEqualNP.Outside.L_pcx_401_aux.T394.mem_leavesUnder.mpr ⟨hp, List.nil_prefix⟩⟩
    obtain ⟨d, _, hd_pow, hd_ref⟩ :=
      PEqualNP.Outside.L_pcx_401_aux.T394.tree_solve F leaves ask E D
        hpfree hcover hsat hF_bool heval href hDpos
        (leaves.sup List.length) [] (by simp) hne ∅
        (fun _ hg => False.elim (Finset.notMem_empty _ hg))
        (fun _ _ i => Fin.elim0 i)
    have hlu_nil : PEqualNP.Outside.L_pcx_401_aux.T394.leavesUnder leaves [] = leaves := by
      ext p
      simp [PEqualNP.Outside.L_pcx_401_aux.T394.mem_leavesUnder]
    rw [hlu_nil, List.length_nil] at hd_pow
    have hsum_eq :
        (∑ p ∈ leaves, PEqualNP.Outside.L_pcx_401_aux.T394.remCopies ask 0 p * 2 ^ (D p)) =
          ∑ p ∈ leaves, copies p * 2 ^ (D p) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [PEqualNP.Outside.L_pcx_401_aux.T394.remCopies_zero]
    rw [hsum_eq] at hd_pow
    have hF_eq : F ∪ ((∅ : Finset (PEqualNP.Outside.L_pcx_401_aux.T394.Poly V)) :
        Set (PEqualNP.Outside.L_pcx_401_aux.T394.Poly V)) = F := by
      simp
    rw [hF_eq] at hd_ref
    exact PEqualNP.Outside.L_pcx_401_aux.Helpers.pcDerivable_mono hd_ref
      (Nat.le_log_of_pow_le (by norm_num) hd_pow) subset_rfl

end T394


section Mine

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds

variable {V : Type}

/-- An affine form over the two-element field: coefficients and a constant. -/
abbrev Af (V : Type) := (V → ZMod 2) × ZMod 2

/-- The value of an affine form. -/
def av [Fintype V] (f : Af V) (y : V → ZMod 2) : ZMod 2 := (∑ v, f.1 v * y v) + f.2

lemma av_add [Fintype V] (f g : Af V) (y : V → ZMod 2) : av (f + g) y = av f y + av g y := by
  simp only [av, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma av_zero [Fintype V] (y : V → ZMod 2) : av (0 : Af V) y = 0 := by
  simp [av]

lemma av_one [Fintype V] (y : V → ZMod 2) : av (((0 : V → ZMod 2), (1 : ZMod 2)) : Af V) y = 1 := by
  simp [av]

lemma av_list_sum [Fintype V] (l : List (Af V)) (y : V → ZMod 2) :
    av l.sum y = (l.map (fun f => av f y)).sum := by
  induction l with
  | nil => simp [av_zero]
  | cons f l ih => simp [List.sum_cons, av_add, ih]

lemma av_vadd [Fintype V] (f : Af V) (y u : V → ZMod 2) :
    av f (y + u) = av f y + ∑ v, f.1 v * u v := by
  simp only [av, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

/-- The query equation saying that the affine form takes the value one. -/
def qe [Fintype V] (f : Af V) : LinEq V :=
  (Finset.univ.filter (fun v => f.1 v = 1), decide (f.2 = 0))

lemma qe_sat [Fintype V] (f : Af V) (x : V → Bool) :
    LinEqSat x (qe f) ↔ av f (T394.b2z x) = 1 := by
  have h := T394.eval_linPoly_eq_zero_iff (T394.b2z x) (qe f)
  rw [T394.z2b_b2z] at h
  rw [← h]
  simp only [T394.linPoly, qe, map_add, map_sum, eval_X, eval_C, av]
  rw [Finset.sum_filter]
  have h1 : ∀ c d : ZMod 2, (if c = 1 then d else 0) = c * d := by decide
  simp only [h1]
  have h2 : ∀ s c : ZMod 2, (s + ((decide (c = 0)).toNat : ZMod 2) = 0 ↔ s + c = 1) := by decide
  exact h2 _ _

lemma qe_term_sat [Fintype V] (f : Af V) (x : V → Bool) :
    LinTermSat x ({qe f} : LinTerm V) ↔ av f (T394.b2z x) = 1 := by
  simp only [LinTermSat, Finset.mem_singleton, forall_eq]
  exact qe_sat f x

/-! ### Symbolic run of the circuit -/

def isNL (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | .or => true
  | _ => false

def nl (gs : List Gate) : ℕ := gs.countP isNL

def rd (w : List (Af V)) (l : List ℕ) : List (Af V) := l.map (fun i => w.getD i 0)

def qform (g : Gate) (w : List (Af V)) : Af V := (rd w g.inputs).headD 0

def stepOp : GateOp → List (Af V) → Bool → Af V
  | .and, l, β => if β then l.getD 1 0 else 0
  | .or, l, β => if β then ((0 : V → ZMod 2), (1 : ZMod 2)) else l.getD 1 0
  | .not, l, _ => ((0 : V → ZMod 2), (1 : ZMod 2)) + l.headD 0
  | .mod _, l, _ => ((0 : V → ZMod 2), (1 : ZMod 2)) + l.sum
  | .maj, _, _ => 0

def stepF (g : Gate) (w : List (Af V)) (β : Bool) : Af V := stepOp g.op (rd w g.inputs) β

def run : List Gate → List (Af V) → List Bool → List (Af V) × Option (Af V) × List Bool
  | [], w, bs => (w, none, bs)
  | g :: gs, w, bs =>
    if isNL g then
      match bs with
      | [] => (w, some (qform g w), [])
      | β :: bs' => run gs (w ++ [stepF g w β]) bs'
    else run gs (w ++ [stepF g w false]) bs

def Shape (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ g.op = .mod 2 ∨
    (g.op = .not ∧ g.inputs.length = 1)

def Agree [Fintype V] (w : List (Af V)) (wb : List Bool) (y : V → ZMod 2) : Prop :=
  w.length = wb.length ∧ ∀ i, av (w.getD i 0) y = ((wb.getD i false).toNat : ZMod 2)

lemma agree_append [Fintype V] {w : List (Af V)} {wb : List Bool} {y : V → ZMod 2}
    (hA : Agree w wb y) {a : Af V} {c : Bool} (hac : av a y = (c.toNat : ZMod 2)) :
    Agree (w ++ [a]) (wb ++ [c]) y := by
  obtain ⟨hl, h⟩ := hA
  refine ⟨by simp [hl], fun i => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getElem?_append_left hi, List.getElem?_append_left (hl ▸ hi),
      ← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD]
    exact h i
  · subst hi
    rw [List.getElem?_append_right le_rfl, List.getElem?_append_right (le_of_eq hl.symm)]
    simp [hl, hac]
  · rw [List.getElem?_append_right hi.le, List.getElem?_append_right (hl ▸ hi.le)]
    have h1 : [a][i - w.length]? = none := by
      rw [List.getElem?_eq_none_iff]; simp; omega
    have h2 : [c][i - wb.length]? = none := by
      rw [List.getElem?_eq_none_iff]; simp; omega
    rw [h1, h2]
    simp [av_zero]

lemma count_cast (l : List Bool) :
    ((l.count true : ℕ) : ZMod 2) = (l.map (fun c => (c.toNat : ZMod 2))).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    cases c
    · simp [List.count_cons, ih]
    · simp [List.count_cons, ih]
      ring

lemma mod_cast2 (c : ℕ) : ((decide (c % 2 = 0)).toNat : ZMod 2) = 1 + (c : ZMod 2) := by
  rw [← ZMod.natCast_mod c 2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> decide

lemma step_ok [Fintype V] (y : V → ZMod 2) (g : Gate) (hg : Shape g) (w : List (Af V))
    (wb : List Bool) (hA : ∀ i, av (w.getD i 0) y = ((wb.getD i false).toNat : ZMod 2))
    (β : Bool) (hβ : isNL g = true → (β = true ↔ av (qform g w) y = 1)) :
    av (stepF g w β) y = ((g.op.eval (g.inputs.map fun i => wb.getD i false)).toNat : ZMod 2) := by
  rcases hg with ⟨hop, hlen⟩ | hop | ⟨hop, hlen⟩
  · obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
    have hnl : isNL g = true := by
      rcases hop with h | h <;> simp [isNL, h]
    have hb := hβ hnl
    simp only [qform, rd, hij, List.map_cons, List.map_nil, List.headD_cons] at hb
    rw [hA i] at hb
    have hi := hA i
    have hj := hA j
    rcases hop with h | h
    · simp only [stepF, rd, hij, h, List.map_cons, List.map_nil, stepOp, GateOp.eval]
      cases hwi : wb.getD i false <;> cases β <;> simp_all [av_zero, av_one]
    · simp only [stepF, rd, hij, h, List.map_cons, List.map_nil, stepOp, GateOp.eval]
      cases hwi : wb.getD i false <;> cases β <;> simp_all [av_zero, av_one]
  · simp only [stepF, rd, hop, stepOp, GateOp.eval]
    rw [av_add, av_one, av_list_sum, mod_cast2, count_cast, List.map_map, List.map_map]
    congr 2
    apply List.map_congr_left
    intro i _
    exact hA i
  · obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp hlen
    simp only [stepF, rd, hop, hi, stepOp, GateOp.eval, List.map_cons, List.map_nil,
      List.headD_cons]
    rw [av_add, av_one, hA i]
    cases wb.getD i false <;> decide

lemma run_short [Fintype V] : ∀ (gs : List Gate) (w : List (Af V)) (bs : List Bool),
    bs.length < nl gs → ∃ w' f, run gs w bs = (w', some f, []) := by
  intro gs
  induction gs with
  | nil => intro w bs h; simp [nl] at h
  | cons g gs ih =>
    intro w bs h
    by_cases hg : isNL g = true
    · cases bs with
      | nil => exact ⟨w, qform g w, by simp [run, hg]⟩
      | cons β bs' =>
        have h' : bs'.length < nl gs := by
          simp [nl, List.countP_cons, hg] at h ⊢; omega
        obtain ⟨w', f, hr⟩ := ih (w ++ [stepF g w β]) bs' h'
        exact ⟨w', f, by simp [run, hg, hr]⟩
    · have h' : bs.length < nl gs := by
        simp [nl, List.countP_cons, hg] at h ⊢; omega
      obtain ⟨w', f, hr⟩ := ih (w ++ [stepF g w false]) bs h'
      exact ⟨w', f, by simp [run, hg, hr]⟩

lemma run_correct [Fintype V] (y : V → ZMod 2) : ∀ (gs : List Gate) (w : List (Af V))
    (wb : List Bool) (bs : List Bool),
    (∀ g ∈ gs, Shape g) → Agree w wb y → nl gs ≤ bs.length →
    (∀ k < nl gs, ∀ w' f r, run gs w (bs.take k) = (w', some f, r) →
      (bs.getD k false = true ↔ av f y = 1)) →
    ∃ w', run gs w bs = (w', none, bs.drop (nl gs)) ∧
      Agree w' (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) wb)
        y := by
  intro gs
  induction gs with
  | nil =>
    intro w wb bs _ hA _ _
    exact ⟨w, by simp [run, nl], by simpa using hA⟩
  | cons g gs ih =>
    intro w wb bs hsh hA hlen hcons
    have hg : Shape g := hsh g (by simp)
    have hsh' : ∀ g ∈ gs, Shape g := fun g' hg' => hsh g' (by simp [hg'])
    by_cases hnl : isNL g = true
    · have hnlc : nl (g :: gs) = nl gs + 1 := by simp [nl, List.countP_cons, hnl]
      cases bs with
      | nil => simp [hnlc] at hlen
      | cons β bs' =>
        have h0 := hcons 0 (by omega) w (qform g w) [] (by simp [run, hnl])
        simp only [List.getD_cons_zero] at h0
        have hA' := agree_append hA (step_ok y g hg w wb hA.2 β (fun _ => h0))
        have hlen' : nl gs ≤ bs'.length := by simp [hnlc] at hlen; omega
        have hcons' : ∀ k < nl gs, ∀ w' f r,
            run gs (w ++ [stepF g w β]) (bs'.take k) = (w', some f, r) →
              (bs'.getD k false = true ↔ av f y = 1) := by
          intro k hk w' f r hr
          have := hcons (k + 1) (by omega) w' f r (by simp [run, hnl, hr])
          simpa using this
        obtain ⟨w', hr, hA''⟩ := ih _ _ bs' hsh' hA' hlen' hcons'
        refine ⟨w', ?_, ?_⟩
        · simp [run, hnl, hr, hnlc]
        · simpa using hA''
    · have hnlc : nl (g :: gs) = nl gs := by simp [nl, List.countP_cons, hnl]
      have hA' := agree_append hA (step_ok y g hg w wb hA.2 false (fun h => absurd h hnl))
      have hlen' : nl gs ≤ bs.length := by omega
      have hcons' : ∀ k < nl gs, ∀ w' f r,
          run gs (w ++ [stepF g w false]) (bs.take k) = (w', some f, r) →
            (bs.getD k false = true ↔ av f y = 1) := by
        intro k hk w' f r hr
        exact hcons k (by omega) w' f r (by simp [run, hnl, hr])
      obtain ⟨w', hr, hA''⟩ := ih _ _ bs hsh' hA' hlen' hcons'
      refine ⟨w', ?_, ?_⟩
      · simp [run, hnl, hr, hnlc]
      · simpa using hA''

/-! ### The question asked at a node of the tree -/

def askOf [Fintype V] (pk : ℕ → ℕ) (res : List (Af V) × Option (Af V) × List Bool) : LinTerm V :=
  match res.2.1 with
  | some f => {qe f}
  | none => {qe (res.1.getD (pk res.2.2.length) 0)}

lemma askOf_card [Fintype V] (pk : ℕ → ℕ) (res : List (Af V) × Option (Af V) × List Bool) :
    (askOf pk res).card = 1 := by
  unfold askOf
  split <;> simp

/-! ### Paths -/

noncomputable def pathAux (ask : List Bool → LinTerm V) (x : V → Bool) : ℕ → List Bool
  | 0 => []
  | k + 1 => pathAux ask x k ++
      [@decide (LinTermSat x (ask (pathAux ask x k))) (Classical.propDecidable _)]

lemma length_pathAux (ask : List Bool → LinTerm V) (x : V → Bool) (k : ℕ) :
    (pathAux ask x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pathAux, ih]

lemma follows_pathAux (ask : List Bool → LinTerm V) (x : V → Bool) (k : ℕ) :
    T394.follows ask (pathAux ask x k) x := by
  induction k with
  | zero => intro i; exact absurd i.isLt (by simp [pathAux])
  | succ k ih =>
    exact T394.follows_append_singleton ih (@decide_eq_true_iff _ (Classical.propDecidable _))

lemma pathAux_unique (ask : List Bool → LinTerm V) (x : V → Bool) :
    ∀ (k : ℕ) (p : List Bool), p.length = k → T394.follows ask p x → p = pathAux ask x k := by
  intro k
  induction k with
  | zero => intro p hp _; simpa [pathAux] using hp
  | succ k ih =>
    intro p hp hf
    have hne : p ≠ [] := by intro h; simp [h] at hp
    have hsplit := List.dropLast_append_getLast hne
    have hdl : p.dropLast.length = k := by simp [hp]
    have hf' : T394.follows ask p.dropLast x :=
      T394.follows_of_isPrefix (List.dropLast_prefix p) hf
    have hih := ih p.dropLast hdl hf'
    have hlast := hf ⟨k, by omega⟩
    have htake : p.take k = p.dropLast := by
      rw [List.dropLast_eq_take, hp]; rfl
    simp only [htake] at hlast
    have hget : p.get ⟨k, by omega⟩ = p.getLast hne := by
      rw [List.getLast_eq_getElem]; simp [hp]
    rw [hget] at hlast
    rw [← hsplit, hih]
    simp only [pathAux]
    congr 2
    rw [← hih]
    exact Bool.eq_iff_iff.mpr (hlast.trans (@decide_eq_true_iff _ (Classical.propDecidable _)).symm)

lemma pathAux_take (ask : List Bool → LinTerm V) (x : V → Bool) {k m : ℕ} (h : k ≤ m) :
    (pathAux ask x m).take k = pathAux ask x k := by
  apply pathAux_unique ask x k
  · simp [length_pathAux, h]
  · exact T394.follows_of_isPrefix (List.take_prefix _ _) (follows_pathAux ask x m)

end Mine

section Main2

open MvPolynomial PEqualNP.ProofComplexity PEqualNP.CircuitLowerBounds

variable {V : Type} [Fintype V] [DecidableEq V]

lemma init_agree (n : ℕ) (order : Fin n → V) (y : V → ZMod 2) :
    Agree ([0, ((0 : V → ZMod 2), (1 : ZMod 2))] ++
      List.ofFn (fun i : Fin n => ((Pi.single (order i) (1 : ZMod 2) : V → ZMod 2), (0 : ZMod 2))))
      ([false, true] ++ List.ofFn (fun i : Fin n => decide (y (order i) = 1))) y := by
  refine ⟨by simp, fun i => ?_⟩
  have hz : ∀ c : ZMod 2, c = ((decide (c = 1)).toNat : ZMod 2) := by decide
  rcases i with _ | _ | k
  · simp [av_zero]
  · simp [av_one]
  · simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      List.getElem?_ofFn]
    by_cases hk : k < n
    · simp only [hk, dite_true, Option.getD_some]
      rw [← hz]
      simp [av, Pi.single_apply]
    · simp [hk, av_zero]

lemma log_le_aux (S d W : ℕ) (h : S ≤ 2 ^ d * W) : Nat.log 2 S ≤ d + Nat.log 2 W := by
  rcases Nat.eq_zero_or_pos S with hS | hS
  · simp [hS]
  rcases Nat.eq_zero_or_pos W with hW | hW
  · subst hW; simp at h; omega
  have h1 : W < 2 ^ (Nat.log 2 W + 1) := Nat.lt_pow_succ_log_self (by norm_num) W
  have h2 : S < 2 ^ (d + Nat.log 2 W + 1) := by
    calc S ≤ 2 ^ d * W := h
      _ < 2 ^ d * 2 ^ (Nat.log 2 W + 1) := Nat.mul_lt_mul_of_pos_left h1 (by positivity)
      _ = 2 ^ (d + Nat.log 2 W + 1) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (by omega) h2
  omega

lemma zmod2_iff_eq (a c : ZMod 2) : ((a = 1 ↔ c = 1) ↔ a = c) := by
  revert a c; decide

lemma region_props (t : ℕ) (f : Fin t → Af V) (R : Finset (V → ZMod 2)) (x₀ : V → ZMod 2)
    (hR : ∀ y, y ∈ R ↔ ∀ k, av (f k) y = av (f k) x₀) :
    (R.card = 2 ^ Module.finrank (ZMod 2)
        (LinearMap.ker (Matrix.mulVecLin (fun k v => (f k).1 v)))) ∧
      Fintype.card V - Module.finrank (ZMod 2)
        (LinearMap.ker (Matrix.mulVecLin (fun k v => (f k).1 v))) ≤ t ∧
      Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (fun k v => (f k).1 v))) ≤
        Fintype.card V ∧
      (∀ u ∈ LinearMap.ker (Matrix.mulVecLin (fun k v => (f k).1 v)), x₀ + u ∈ R) ∧
      (∀ y ∈ R, y - x₀ ∈ LinearMap.ker (Matrix.mulVecLin (fun k v => (f k).1 v))) := by
  classical
  set Φ := Matrix.mulVecLin (fun (k : Fin t) (v : V) => (f k).1 v) with hΦ
  have hmem : ∀ u, u ∈ LinearMap.ker Φ ↔ ∀ k, ∑ v, (f k).1 v * u v = 0 := by
    intro u
    rw [LinearMap.mem_ker, funext_iff]
    exact Iff.rfl
  have h1 : ∀ u ∈ LinearMap.ker Φ, x₀ + u ∈ R := by
    intro u hu
    rw [hR]
    intro k
    rw [av_vadd, (hmem u).1 hu k, add_zero]
  have h2 : ∀ y ∈ R, y - x₀ ∈ LinearMap.ker Φ := by
    intro y hy
    rw [hmem]
    intro k
    have h3 := (hR y).1 hy k
    have e := av_vadd (f k) x₀ (y - x₀)
    rw [add_sub_cancel, h3] at e
    linear_combination -e
  have hRimg : R = (Finset.univ.filter (fun u => u ∈ LinearMap.ker Φ)).image (fun u => x₀ + u) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hy
      exact ⟨y - x₀, h2 y hy, by abel⟩
    · rintro ⟨u, hu, rfl⟩
      exact h1 u hu
  have hcardA : (Finset.univ.filter (fun u => u ∈ LinearMap.ker Φ)).card =
      2 ^ Module.finrank (ZMod 2) (LinearMap.ker Φ) := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker Φ)
    rw [ZMod.card] at hc
    rw [← hc]
    exact (Fintype.card_of_subtype _ (fun u => by simp)).symm
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hle1 := Submodule.finrank_le (LinearMap.range Φ)
  have hle2 := Submodule.finrank_le (LinearMap.ker Φ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hle1
  rw [Module.finrank_fintype_fun_eq_card] at hle2 hrn
  refine ⟨?_, by omega, hle2, h1, h2⟩
  rw [hRimg, Finset.card_image_of_injective _ (add_right_injective x₀), hcardA]

lemma list_eq_of_getD {p1 p2 : List Bool} (hl : p1.length = p2.length)
    (h : ∀ i, p1.getD i false = p2.getD i false) : p1 = p2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  rwa [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

set_option maxHeartbeats 1000000 in
theorem main (b : ℕ) (F : Set (MvPolynomial V (ZMod 2)))
    (E : (Fin b → ZMod 2) → Set (MvPolynomial V (ZMod 2)))
    (D : (Fin b → ZMod 2) → ℕ) (H : Circuit)
    (order : Fin (Fintype.card V) ≃ V) (pick : Fin b → Fin (2 + Fintype.card V + H.size))
    (msg : (V → ZMod 2) → Fin b → ZMod 2)
    (hmsg : ∀ x j, msg x j = (((H.wires ([false, true] ++
      List.ofFn (fun i : Fin (Fintype.card V) => decide (x (order i) = 1)))).getD
        (pick j).val false).toNat : ZMod 2))
    (hshape : ∀ g ∈ H.gates, Shape g)
    (hbool : ∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F)
    (hE : ∀ x : V → ZMod 2, ∀ e ∈ E (msg x), MvPolynomial.eval x e = 0)
    (hD : ∀ y ∈ Finset.univ.image msg, PCRefutable (F ∪ E y) (D y)) :
    ∃ (x₀ : V → ZMod 2) (A : Submodule (ZMod 2) (V → ZMod 2)) (a : Fin b → ZMod 2)
      (L : (V → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2)),
      Fintype.card V - Module.finrank (ZMod 2) A ≤ nl H.gates ∧
      (∀ u ∈ A, msg (x₀ + u) = a + L u) ∧
      PCRefutable F (Fintype.card V - Module.finrank (ZMod 2) A +
        Nat.log 2 (∑ y ∈ (Finset.univ.filter (fun u : V → ZMod 2 =>
          @decide (u ∈ A) (Classical.propDecidable _))).image (fun u => a + L u), 2 ^ D y)) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, t = nl H.gates := ⟨_, rfl⟩
  rw [← ht]
  obtain ⟨init, hinitA⟩ : ∃ init : List (Af V), ∀ y : V → ZMod 2, Agree init ([false, true] ++
      List.ofFn (fun i : Fin (Fintype.card V) => decide (y (order i) = 1))) y :=
    ⟨_, init_agree _ order⟩
  obtain ⟨pk, hpk⟩ : ∃ pk : ℕ → ℕ, ∀ j : Fin b, pk j.val = (pick j).val :=
    ⟨fun j => if h : j < b then (pick ⟨j, h⟩).val else 0, fun j => by simp [j.isLt]⟩
  obtain ⟨ask, hask⟩ : ∃ ask : List Bool → LinTerm V, ∀ q, ask q = askOf pk (run H.gates init q) :=
    ⟨_, fun _ => rfl⟩
  -- the run along a followed path
  have hcons : ∀ (p : List Bool) (x : V → Bool), T394.follows ask p x → t ≤ p.length →
      ∃ w', run H.gates init p = (w', none, p.drop t) ∧
        Agree w' (H.wires ([false, true] ++ List.ofFn (fun i : Fin (Fintype.card V) =>
          decide (T394.b2z x (order i) = 1)))) (T394.b2z x) := by
    intro p x hf hlen
    have hrc := run_correct (T394.b2z x) H.gates init _ p hshape (hinitA _) (ht ▸ hlen) ?_
    · rw [← ht] at hrc
      exact hrc
    intro k hk w' f r hr
    have h1 : p.get ⟨k, by omega⟩ = true ↔ LinTermSat x (ask (p.take k)) := hf ⟨k, by omega⟩
    rw [hask, hr] at h1
    have h2 : askOf pk (w', some f, r) = ({qe f} : LinTerm V) := rfl
    rw [h2, qe_term_sat] at h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact h1
  -- the word read at a leaf
  obtain ⟨wordOf, hwordOf⟩ : ∃ wordOf : List Bool → Fin b → ZMod 2,
      ∀ p j, wordOf p j = if p.getD (t + j.val) false then 1 else 0 := ⟨_, fun _ _ => rfl⟩
  have hword : ∀ (p : List Bool) (x : V → Bool), p.length = t + b → T394.follows ask p x →
      wordOf p = msg (T394.b2z x) := by
    intro p x hp hf
    funext j
    have hpre : T394.follows ask (p.take (t + j.val)) x :=
      T394.follows_of_isPrefix (List.take_prefix _ _) hf
    have hlen : (p.take (t + j.val)).length = t + j.val := by simp [hp] <;> omega
    obtain ⟨w', hr, hA⟩ := hcons _ x hpre (by omega)
    have hdl : ((p.take (t + j.val)).drop t).length = j.val := by simp [hp] <;> omega
    have h1 : p.get ⟨t + j.val, by omega⟩ = true ↔ LinTermSat x (ask (p.take (t + j.val))) :=
      hf ⟨t + j.val, by omega⟩
    rw [hask, hr] at h1
    have h2 : askOf pk (w', none, (p.take (t + j.val)).drop t) =
        ({qe (w'.getD (pk ((p.take (t + j.val)).drop t).length) 0)} : LinTerm V) := rfl
    rw [h2, hdl, qe_term_sat, hpk j] at h1
    have hm : msg (T394.b2z x) j = av (w'.getD (pick j).val 0) (T394.b2z x) :=
      (hmsg (T394.b2z x) j).trans (hA.2 _).symm
    rw [← hm] at h1
    have hg : p.getD (t + j.val) false = p.get ⟨t + j.val, by omega⟩ := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rfl
    rw [hwordOf, hg]
    by_cases hb : p.get ⟨t + j.val, by omega⟩ = true
    · rw [if_pos hb]
      exact (h1.mp hb).symm
    · rw [if_neg hb]
      have hne : msg (T394.b2z x) j ≠ 1 := fun h => hb (h1.mpr h)
      revert hne
      generalize msg (T394.b2z x) j = c
      revert c
      decide
  -- the query forms of the first phase
  obtain ⟨qf, hqf⟩ : ∃ qf : List Bool → ℕ → Af V,
      ∀ q k, qf q k = ((run H.gates init (q.take k)).2.1).getD 0 := ⟨_, fun _ _ => rfl⟩
  have hregion : ∀ (q : List Bool), q.length = t → ∀ y : V → ZMod 2,
      (T394.follows ask q (T394.z2b y) ↔
        ∀ k : Fin t, (q.getD k.val false = true ↔ av (qf q k.val) y = 1)) := by
    intro q hq y
    have hask_k : ∀ k : ℕ, k < t → ask (q.take k) = ({qe (qf q k)} : LinTerm V) := by
      intro k hk
      obtain ⟨w', f, hr⟩ := run_short H.gates init (q.take k) (by simp; omega)
      rw [hask, hr, hqf, hr]
      rfl
    have hgd : ∀ k (hk : k < q.length), q.getD k false = q.get ⟨k, hk⟩ := by
      intro k hk
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      rfl
    constructor
    · intro hf k
      have h1 : q.get ⟨k.val, by omega⟩ = true ↔ LinTermSat (T394.z2b y) (ask (q.take k.val)) :=
        hf ⟨k.val, by omega⟩
      rw [hask_k k.val k.isLt, qe_term_sat, T394.b2z_z2b] at h1
      rw [hgd k.val (by omega)]
      exact h1
    · intro h i
      have h1 := h ⟨i.val, by omega⟩
      show q.get i = true ↔ LinTermSat (T394.z2b y) (ask (q.take i.val))
      rw [hask_k i.val (by omega), qe_term_sat, T394.b2z_z2b]
      rw [hgd i.val i.isLt] at h1
      exact h1
  have hmsgaff : ∀ (q : List Bool), q.length = t → ∀ y : V → ZMod 2,
      T394.follows ask q (T394.z2b y) →
        ∀ j, msg y j = av (((run H.gates init q).1).getD (pick j).val 0) y := by
    intro q hq y hf j
    obtain ⟨w', hr, hA⟩ := hcons q (T394.z2b y) hf (by omega)
    rw [T394.b2z_z2b] at hA
    rw [hr]
    exact (hmsg y j).trans (hA.2 _).symm
  -- leaves
  set Lv : Finset (List Bool) := Finset.univ.image (fun x : V → Bool => pathAux ask x (t + b))
    with hLv
  have hLv_mem : ∀ p ∈ Lv, ∃ x, p = pathAux ask x (t + b) := by
    intro p hp
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨x, rfl⟩
  have hLv_len : ∀ p ∈ Lv, p.length = t + b := by
    intro p hp
    obtain ⟨x, rfl⟩ := hLv_mem p hp
    exact length_pathAux _ _ _
  have h394 := T394.main394 V F Lv ask (fun p => E (wordOf p)) (fun p => D (wordOf p))
    (fun p hp q hq hpq => hpq.eq_of_length (by rw [hLv_len p hp, hLv_len q hq]))
    (fun x => ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ x), follows_pathAux ask x _⟩)
    (fun p hp => by
      obtain ⟨x, rfl⟩ := hLv_mem p hp
      exact ⟨x, follows_pathAux ask x _⟩)
    hbool
    (fun p hp x hf e he => by
      have hw := hword p x (hLv_len p hp) hf
      rw [hw] at he
      exact hE _ e he)
    (fun p hp => by
      obtain ⟨x, rfl⟩ := hLv_mem p hp
      rw [hword _ x (length_pathAux _ _ _) (follows_pathAux ask x _)]
      exact hD _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hcopies : ∀ p : List Bool, (∏ i : Fin p.length,
      (if p.get i then 1 else max 1 (ask (p.take i.val)).card)) = 1 := by
    intro p
    apply Finset.prod_eq_one
    intro i _
    split_ifs <;> simp [hask, askOf_card]
  set S := ∑ p ∈ Lv, 2 ^ D (wordOf p) with hSdef
  have hS : PCRefutable F (Nat.log 2 S) := by
    have h := h394
    simp only [hcopies, one_mul] at h
    exact h
  -- regions
  set Q := Lv.image (List.take t) with hQ
  have hQ_len : ∀ q ∈ Q, q.length = t := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    simp [hLv_len p hp]
  set Rq : List Bool → Finset (V → ZMod 2) :=
    fun q => Finset.univ.filter (fun y => T394.follows ask q (T394.z2b y)) with hRq
  have hRq_ne : ∀ q ∈ Q, ∃ x₀, x₀ ∈ Rq q := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨x, rfl⟩ := hLv_mem p hp
    refine ⟨T394.b2z x, ?_⟩
    simp only [hRq, Finset.mem_filter, Finset.mem_univ, true_and, T394.z2b_b2z]
    exact T394.follows_of_isPrefix (List.take_prefix _ _) (follows_pathAux ask x _)
  -- the affine structure of a region
  have hRq_aff : ∀ q ∈ Q, ∀ x₀ ∈ Rq q, ∀ y,
      y ∈ Rq q ↔ ∀ k : Fin t, av (qf q k.val) y = av (qf q k.val) x₀ := by
    intro q hq x₀ hx₀ y
    have hx := (hregion q (hQ_len q hq) x₀).1 (by simpa [hRq] using hx₀)
    simp only [hRq, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hregion q (hQ_len q hq) y]
    constructor
    · intro h k
      exact (zmod2_iff_eq _ _).1 ((h k).symm.trans (hx k))
    · intro h k
      rw [h k]
      exact hx k
  set Aq : List Bool → Submodule (ZMod 2) (V → ZMod 2) :=
    fun q => LinearMap.ker (Matrix.mulVecLin (fun (k : Fin t) v => (qf q k.val).1 v)) with hAq
  have hprops : ∀ q ∈ Q, ∀ x₀ ∈ Rq q,
      (Rq q).card = 2 ^ Module.finrank (ZMod 2) (Aq q) ∧
      Fintype.card V - Module.finrank (ZMod 2) (Aq q) ≤ t ∧
      Module.finrank (ZMod 2) (Aq q) ≤ Fintype.card V ∧
      (∀ u ∈ Aq q, x₀ + u ∈ Rq q) ∧ (∀ y ∈ Rq q, y - x₀ ∈ Aq q) := by
    intro q hq x₀ hx₀
    exact region_props t (fun k => qf q k.val) (Rq q) x₀ (hRq_aff q hq x₀ hx₀)
  set Wq : List Bool → ℕ := fun q => ∑ y ∈ (Rq q).image msg, 2 ^ D y with hWq
  -- step A: the leaves are counted by the words of the regions
  have hA : S ≤ ∑ q ∈ Q, Wq q := by
    rw [hSdef, ← Finset.sum_fiberwise_of_maps_to (g := List.take t) (t := Q)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    apply Finset.sum_le_sum
    intro q hq
    have hinj : ∀ p1 ∈ Lv.filter (fun p => p.take t = q), ∀ p2 ∈ Lv.filter (fun p => p.take t = q),
        wordOf p1 = wordOf p2 → p1 = p2 := by
      intro p1 hp1 p2 hp2 hw
      rw [Finset.mem_filter] at hp1 hp2
      have hl1 := hLv_len p1 hp1.1
      have hl2 := hLv_len p2 hp2.1
      apply list_eq_of_getD (by rw [hl1, hl2])
      intro i
      by_cases hi : i < t
      · have e := congrArg (fun l : List Bool => l.getD i false) (hp1.2.trans hp2.2.symm)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, if_true] at e
        simpa [List.getD_eq_getElem?_getD] using e
      · by_cases hi2 : i < t + b
        · have e := congrFun hw ⟨i - t, by omega⟩
          rw [hwordOf, hwordOf] at e
          have hti : t + (i - t) = i := by omega
          simp only [hti] at e
          cases h1 : p1.getD i false <;> cases h2 : p2.getD i false <;> rw [h1, h2] at e <;>
            first | rfl | (exfalso; revert e; decide)
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    rw [← Finset.sum_image (f := fun y => 2 ^ D y) hinj]
    apply Finset.sum_le_sum_of_subset
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    rw [Finset.mem_filter] at hp
    obtain ⟨x, hpx⟩ := hLv_mem p hp.1
    have hf : T394.follows ask p x := hpx ▸ follows_pathAux ask x _
    rw [hword p x (hLv_len p hp.1) hf]
    apply Finset.mem_image_of_mem
    simp only [hRq, Finset.mem_filter, Finset.mem_univ, true_and, T394.z2b_b2z]
    rw [← hp.2]
    exact T394.follows_of_isPrefix (List.take_prefix _ _) hf
  -- step B: the regions partition the inputs
  have hB : ∑ q ∈ Q, (Rq q).card = 2 ^ Fintype.card V := by
    have hu : (Finset.univ : Finset (V → ZMod 2)).card = 2 ^ Fintype.card V := by
      simp [Finset.card_univ, Fintype.card_fun, ZMod.card]
    rw [← hu, Finset.card_eq_sum_card_fiberwise (f := fun y => pathAux ask (T394.z2b y) t) (t := Q)]
    · apply Finset.sum_congr rfl
      intro q hq
      congr 1
      ext y
      simp only [hRq, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact (pathAux_unique ask _ t q (hQ_len q hq) h).symm
      · intro h
        rw [← h]
        exact follows_pathAux ask _ t
    · intro y _
      simp only [Finset.mem_coe]
      rw [← pathAux_take ask (T394.z2b y) (Nat.le_add_right t b)]
      exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  -- step C: averaging
  have hQne : Q.Nonempty := by
    refine ⟨(pathAux ask (fun _ => false) (t + b)).take t, ?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  obtain ⟨q, hqQ, hq⟩ : ∃ q ∈ Q,
      S ≤ 2 ^ (Fintype.card V - Module.finrank (ZMod 2) (Aq q)) * Wq q := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ q ∈ Q, 2 ^ Fintype.card V * Wq q < S * (Rq q).card := by
      intro q hq
      obtain ⟨x₀, hx₀⟩ := hRq_ne q hq
      obtain ⟨hc, _, hr, _, _⟩ := hprops q hq x₀ hx₀
      rw [hc]
      have h1 := hcon q hq
      calc 2 ^ Fintype.card V * Wq q
          = 2 ^ Module.finrank (ZMod 2) (Aq q) *
            (2 ^ (Fintype.card V - Module.finrank (ZMod 2) (Aq q)) * Wq q) := by
            rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hr]
        _ < 2 ^ Module.finrank (ZMod 2) (Aq q) * S :=
            Nat.mul_lt_mul_of_pos_left h1 (by positivity)
        _ = S * 2 ^ Module.finrank (ZMod 2) (Aq q) := mul_comm _ _
    have hsum := Finset.sum_lt_sum_of_nonempty hQne hlt
    rw [← Finset.mul_sum, ← Finset.mul_sum, hB] at hsum
    have : ∑ q ∈ Q, Wq q < S := by
      by_contra hc
      push_neg at hc
      have := Nat.mul_le_mul_left (2 ^ Fintype.card V) hc
      rw [mul_comm S] at hsum
      omega
    omega
  -- step D: the chosen region
  obtain ⟨x₀, hx₀⟩ := hRq_ne q hqQ
  obtain ⟨_, hdt, _, h1, h2⟩ := hprops q hqQ x₀ hx₀
  obtain ⟨L, hLapp⟩ : ∃ L : (V → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2), ∀ u j,
      L u j = ∑ v, (((run H.gates init q).1).getD (pick j).val 0).1 v * u v :=
    ⟨Matrix.mulVecLin (fun (j : Fin b) v => (((run H.gates init q).1).getD (pick j).val 0).1 v),
      fun _ _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : Fin b → ZMod 2, ∀ j,
      a j = (((run H.gates init q).1).getD (pick j).val 0).2 + L x₀ j := ⟨_, fun _ => rfl⟩
  have haff : ∀ u ∈ Aq q, msg (x₀ + u) = a + L u := by
    intro u hu
    have hy := h1 u hu
    have hfol : T394.follows ask q (T394.z2b (x₀ + u)) := by
      simpa [hRq] using hy
    funext j
    rw [hmsgaff q (hQ_len q hqQ) _ hfol j, Pi.add_apply, ha j, hLapp, hLapp]
    simp only [av, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  refine ⟨x₀, Aq q, a, L, hdt, haff, ?_⟩
  refine Helpers.pcDerivable_mono hS ?_ subset_rfl
  apply log_le_aux
  refine hq.trans (Nat.mul_le_mul_left _ ?_)
  apply Finset.sum_le_sum_of_subset
  intro y hy
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hzA := h2 z hz
  have e := haff (z - x₀) hzA
  rw [add_sub_cancel] at e
  rw [e]
  apply Finset.mem_image_of_mem
  simp [hzA]

end Main2

end PEqualNP.Outside.L_pcx_401_aux

theorem PEqualNP.Outside.L_pcx_401 : ∀ (V : Type) [Fintype V] [DecidableEq V] (b : ℕ)
    (F : Set (MvPolynomial V (ZMod 2)))
    (E : (Fin b → ZMod 2) → Set (MvPolynomial V (ZMod 2)))
    (D : (Fin b → ZMod 2) → ℕ) (H : PEqualNP.CircuitLowerBounds.Circuit),
  let K := ZMod 2
  let X := V → K
  let Y := Fin b → K
  let n := Fintype.card V
  ∀ (order : Fin n ≃ V) (pick : Fin b → Fin (2+n+H.size)),
    let msg := fun (x : X) (j : Fin b) =>
      let ws := H.wires ([false,true] ++ List.ofFn (fun i : Fin n => decide (x (order i) = 1)))
      ((ws.getD (pick j).val false).toNat : K)
    let t := H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (2+n) H →
    (∀ g ∈ H.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      g.op = .mod 2 ∨ (g.op = .not ∧ g.inputs.length = 1)) →
    (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
    (∀ x : X, ∀ e ∈ E (msg x), MvPolynomial.eval x e = 0) →
    (∀ y ∈ Finset.univ.image msg, PEqualNP.ProofComplexity.PCRefutable (F ∪ E y) (D y)) →
    ∃ (x₀ : X) (A : Submodule K X) (a : Y) (L : X →ₗ[K] Y),
      let d := n - Module.finrank K A
      let points := Finset.univ.filter (fun u : X => @decide (u ∈ A) (Classical.propDecidable _))
      let words := points.image (fun u => a + L u)
      d ≤ t ∧ (∀ u ∈ A, msg (x₀+u) = a + L u) ∧
        PEqualNP.ProofComplexity.PCRefutable F (d + Nat.log 2 (∑ y ∈ words, 2^(D y))) := by
  intro V _ _ b F E D H K X Y n order pick msg t _ hshape hbool hE hD
  have ht : H.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or)
      (Classical.propDecidable _)) = PEqualNP.Outside.L_pcx_401_aux.nl H.gates := by
    unfold PEqualNP.Outside.L_pcx_401_aux.nl
    congr 1
    funext g
    rcases g with ⟨op, ins⟩
    cases op <;> simp [PEqualNP.Outside.L_pcx_401_aux.isNL]
  obtain ⟨x₀, A, a, L, h1, h2, h3⟩ := PEqualNP.Outside.L_pcx_401_aux.main b F E D H order pick
    msg (fun _ _ => rfl) hshape hbool hE hD
  refine ⟨x₀, A, a, L, ?_⟩
  intro d points words
  exact ⟨le_of_le_of_eq h1 ht.symm, h2, h3⟩
