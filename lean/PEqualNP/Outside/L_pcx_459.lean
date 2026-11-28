import PEqualNP.Defs
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.FieldTheory.Finite.Polynomial

namespace PEqualNP.Outside.L_pcx_459

open scoped BigOperators

namespace Toolkit459

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

end Toolkit459

namespace Vanish459

open MvPolynomial PEqualNP.ProofComplexity Toolkit459

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

end Vanish459

namespace Lift459

open MvPolynomial PEqualNP.ProofComplexity Toolkit459

abbrev K := ZMod 2
abbrev P (V : Type) := MvPolynomial V K

noncomputable def lift {V : Type} : P V →ₐ[K] P (V ⊕ Unit) := rename Sum.inl

noncomputable def hiddenBit {V : Type} : P (V ⊕ Unit) := X (Sum.inr ())

noncomputable def hidden {V : Type} {m : ℕ} (F : Set (P V)) (a b : Fin m → P V) :
    Set (P (V ⊕ Unit)) :=
  Set.image lift F ∪ {hiddenBit*hiddenBit+hiddenBit} ∪
    Set.range (fun i => lift (a i) + hiddenBit * lift (b i))

noncomputable def visible {V : Type} {m : ℕ} (F : Set (P V)) (a b : Fin m → P V) : Set (P V) :=
  F ∪ Set.range (fun i => a i * (1+b i)) ∪
    {z | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i}

private theorem add_self_zero {V : Type} (a : P V) : a+a = 0 := by
  rw [← two_smul K, show (2 : K) = 0 from rfl, zero_smul]

private theorem mul_within {V : Type} {F : Set (P V)} {D : ℕ} {g q : P V}
    (hg : PCDerivable F D g) (hd : q.totalDegree+g.totalDegree ≤ D) :
    PCDerivable F D (q*g) :=
  pcDerivable_mono (pcDerivable_mul_left hg q) (max_le le_rfl hd) subset_rfl

private theorem rename_replay {V W : Type} {F : Set (P V)} {G : Set (P W)} {B D : ℕ}
    (e : V → W) (hBD : B ≤ D)
    (ax : ∀ f ∈ F, f.totalDegree ≤ B → PCDerivable G D (rename e f))
    {p : P V} (hp : PCDerivable F B p) : PCDerivable G D (rename e p) := by
  induction hp with
  | ax hf hd => exact ax _ hf hd
  | zero => simpa only [map_zero] using (PCDerivable.zero : PCDerivable G D 0)
  | add _ _ ih₁ ih₂ => simpa only [map_add] using PCDerivable.add ih₁ ih₂
  | mulX j _ hd ih =>
    rw [map_mul, rename_X]
    apply PCDerivable.mulX _ ih
    rw [← rename_X, ← map_mul]
    exact (totalDegree_rename_le _ _).trans (hd.trans hBD)

private theorem row_degree {V : Type} {d : ℕ} {a b : P V}
    (ha : a.totalDegree ≤ d+1) (hb : b.totalDegree ≤ d) :
    (lift a + hiddenBit*lift b).totalDegree ≤ d+1 := by
  have h₁ : (lift b).totalDegree ≤ d :=
    (totalDegree_rename_le (Sum.inl : V → V ⊕ Unit) b).trans hb
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_rename_le _ _).trans ha) ?_)
  exact (totalDegree_mul _ _).trans (by rw [hiddenBit, totalDegree_X]; omega)

private theorem bool_lift {V : Type} {m : ℕ} (F : Set (P V)) (a b : Fin m → P V)
    (hbool : ∀ v : V, X v * X v + X v ∈ F) (v : V ⊕ Unit) :
    X v * X v + X v ∈ hidden F a b := by
  cases v with
  | inl v =>
    apply Or.inl
    apply Or.inl
    exact ⟨X v * X v + X v, hbool v, by simp [lift]⟩
  | inr u =>
    cases u
    exact Or.inl (Or.inr rfl)

private theorem lift_test {V : Type} {m d : ℕ} (F : Set (P V)) (a b : Fin m → P V)
    (hbool : ∀ v : V, X v * X v + X v ∈ F)
    (hdeg : ∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) :
    (∀ i, PCDerivable (hidden F a b) (2*d+1) (lift (a i*(1+b i)))) ∧
    (∀ i j, PCDerivable (hidden F a b) (2*d+1) (lift (a i*b j+a j*b i))) := by
  let A (i : Fin m) := lift (a i)
  let B (i : Fin m) := lift (b i)
  let h : P (V ⊕ Unit) := hiddenBit
  let row (i : Fin m) := A i+h*B i
  have aux (i : Fin m) : (B i).totalDegree ≤ d :=
    (totalDegree_rename_le _ _).trans (hdeg i).2
  have hrow (i : Fin m) : (row i).totalDegree ≤ d+1 := row_degree (hdeg i).1 (hdeg i).2
  have hbit : h.totalDegree = 1 := totalDegree_X _
  have make_row (i : Fin m) : PCDerivable (hidden F a b) (2*d+1) (row i) :=
    .ax (Or.inr ⟨i, rfl⟩) ((hrow i).trans (by omega))
  constructor
  · intro i
    have gi : (1+B i).totalDegree ≤ d :=
      (totalDegree_add _ _).trans (max_le (by simp) (aux i))
    have hd : (B i*B i+B i).totalDegree ≤ 2*d := by
      apply (totalDegree_add _ _).trans
      apply max_le
      · have le := aux i
        exact (totalDegree_mul _ _).trans (by omega)
      · have le := aux i
        omega
    have sq : PCDerivable (hidden F a b) (2*d+1) (B i*B i+B i) := by
      refine Vanish459.vanish_derivable _ _ _ _ (bool_lift F a b hbool) (hd.trans (by omega)) ?_
      intro x
      rw [map_add, map_mul]
      generalize eval x (B i) = t
      exact (show ∀ t : K, t*t+t = 0 from by decide +kernel) t
    have g₁ := mul_within (make_row i) (q := 1+B i) (by have := hrow i; omega)
    have g₂ := mul_within sq (q := h) (by omega)
    have he : (1+B i)*row i + h*(B i*B i+B i) = A i*(1+B i) := by
      dsimp only [row]
      calc
        _ = A i*(1+B i) + (h*(B i*B i+B i) + h*(B i*B i+B i)) := by ring
        _ = _ := by rw [add_self_zero, add_zero]
    have g := PCDerivable.add g₁ g₂
    rw [he] at g
    simpa only [map_mul, map_add, map_one] using g
  · intro i j
    have g₁ := mul_within (make_row i) (q := B j) (by have := hrow i; have := aux j; omega)
    have g₂ := mul_within (make_row j) (q := B i) (by have := hrow j; have := aux i; omega)
    have he : B j*row i + B i*row j = A i*B j+A j*B i := by
      dsimp only [row]
      calc
        _ = A i*B j+A j*B i + (h*B i*B j + h*B i*B j) := by ring
        _ = _ := by rw [add_self_zero, add_zero]
    have g := PCDerivable.add g₁ g₂
    rw [he] at g
    simpa only [map_add, map_mul] using g

theorem forward {V : Type} {m d : ℕ} (F : Set (P V)) (a b : Fin m → P V)
    (hbool : ∀ v : V, X v * X v + X v ∈ F)
    (hdeg : ∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) :
    ∀ B : ℕ, PCRefutable (visible F a b) B → PCRefutable (hidden F a b) (max B (2*d+1)) := by
  intro B hp
  obtain ⟨diag, minor⟩ := lift_test F a b hbool hdeg
  have hstep := rename_replay (F := visible F a b) (G := hidden F a b)
    (Sum.inl : V → V ⊕ Unit) (le_max_left B (2*d+1)) ?_ hp
  · simpa only [PCRefutable, map_one] using hstep
  · intro f hf hd
    change PCDerivable (hidden F a b) (max B (2*d+1)) (lift f)
    rcases hf with (hF | ⟨i, rfl⟩) | ⟨i,j,_,rfl⟩
    · exact .ax (Or.inl (Or.inl ⟨f, hF, rfl⟩))
        ((totalDegree_rename_le _ _).trans (hd.trans (le_max_left _ _)))
    · exact pcDerivable_mono (diag i) (le_max_right _ _) subset_rfl
    · exact pcDerivable_mono (minor i j) (le_max_right _ _) subset_rfl

end Lift459

namespace Special459

open MvPolynomial PEqualNP.ProofComplexity

abbrev K := ZMod 2
abbrev P (V : Type) := MvPolynomial V K

noncomputable def lift {V : Type} : P V →ₐ[K] P (V ⊕ Unit) :=
  rename Sum.inl

noncomputable def h (V : Type) : P (V ⊕ Unit) := X (Sum.inr ())

noncomputable def hidden {V : Type} {m : ℕ} (F : Set (P V)) (a b : Fin m → P V) :
    Set (P (V ⊕ Unit)) :=
  Set.image lift F ∪ {h V * h V + h V} ∪
    Set.range (fun i => lift (a i) + h V * lift (b i))

noncomputable def branch {V : Type} {m : ℕ} (F : Set (P V)) (a b : Fin m → P V) (ε : K) : Set (P V) :=
  F ∪ Set.range (fun i => a i + C ε * b i)

private noncomputable def values {V : Type} (ε : K) : V ⊕ Unit → P V
  | .inl i => X i
  | .inr _ => C ε

private theorem bit_cases (ε : K) : ε = 0 ∨ ε = 1 := by
  exact (show ∀ ε : K, ε = 0 ∨ ε = 1 by decide +kernel) ε

private theorem boolean_square (ε : K) : ε * ε + ε = 0 := by
  exact (show ∀ ε : K, ε * ε + ε = 0 by decide +kernel) ε

private theorem subst_degree {V : Type} (ε : K) (p : P (V ⊕ Unit)) :
    (bind₁ (values ε) p).totalDegree ≤ p.totalDegree := by
  have hval : ∀ j : V ⊕ Unit, (values ε j).totalDegree ≤ 1 := by
    intro j
    cases j <;> simp [values]
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun a ha => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc
    (∑ i ∈ a.support, (values ε i ^ a i).totalDegree)
        ≤ ∑ i ∈ a.support, a i := Finset.sum_le_sum fun i _ =>
      (totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (a i) (hval i))
    _ ≤ _ := le_totalDegree ha

private theorem subst_lift {V : Type} (ε : K) (p : P V) :
    bind₁ (values ε) (lift p) = p := by
  have he : (bind₁ (values ε)).comp (lift : P V →ₐ[K] P (V ⊕ Unit)) =
      AlgHom.id K (P V) := by
    ext i
    simp [lift, values]
  exact DFunLike.congr_fun he p

private theorem replay {V : Type} (ε : K) {A : Set (P (V ⊕ Unit))}
    {G : Set (P V)} {B : ℕ}
    (ha : ∀ p ∈ A, p.totalDegree ≤ B → PCDerivable G B (bind₁ (values ε) p))
    {p : P (V ⊕ Unit)} (hp : PCDerivable A B p) :
    PCDerivable G B (bind₁ (values ε) p) := by
  induction hp with
  | ax hmem hd => exact ha _ hmem hd
  | zero => simpa only [map_zero] using PCDerivable.zero
  | add _ _ ih₁ ih₂ =>
    rw [map_add]
    exact PCDerivable.add ih₁ ih₂
  | @mulX j p _ hd ih =>
    have hdeg := (subst_degree ε (X j * p)).trans hd
    rw [map_mul, bind₁_X_right] at hdeg ⊢
    cases j with
    | inl i => exact PCDerivable.mulX i ih hdeg
    | inr i =>
      rcases bit_cases ε with hε | hε
      · simp only [values, hε, map_zero, zero_mul]
        exact PCDerivable.zero
      · simpa only [values, hε, map_one, one_mul] using ih

theorem specialize {V : Type} {m B : ℕ} (F : Set (P V)) (a b : Fin m → P V) (ε : K)
    (hh : PCRefutable (hidden F a b) B) : PCRefutable (branch F a b ε) B := by
  have ha (q : P (V ⊕ Unit)) (hq : q ∈ hidden F a b) (hd : q.totalDegree ≤ B) :
      PCDerivable (branch F a b ε) B (bind₁ (values ε) q) := by
    have hdeg := (subst_degree ε q).trans hd
    rcases hq with (⟨p,hp,rfl⟩ | hb) | ⟨i,rfl⟩
    · rw [subst_lift] at hdeg ⊢
      exact PCDerivable.ax (Or.inl hp) hdeg
    · rw [Set.mem_singleton_iff] at hb
      rw [hb]
      simp only [h, map_mul, map_add, bind₁_X_right, values]
      rw [← map_mul, ← map_add, boolean_square, map_zero]
      exact PCDerivable.zero
    · simp only [map_add, map_mul, subst_lift, h, bind₁_X_right, values] at hdeg ⊢
      exact PCDerivable.ax (Or.inr ⟨i,rfl⟩) hdeg
  unfold PCRefutable at hh ⊢
  simpa only [map_one] using replay ε ha hh

theorem two {V : Type} {m B : ℕ} (F : Set (P V)) (a b : Fin m → P V)
    (hh : PCRefutable (hidden F a b) B) :
    PCRefutable (F ∪ Set.range a) B ∧ PCRefutable (F ∪ Set.range (fun i => a i+b i)) B := by
  constructor
  · simpa only [branch, map_zero, zero_mul, add_zero ] using specialize F a b 0 hh
  · simpa only [branch, map_one, one_mul] using specialize F a b 1 hh

end Special459

namespace Cross459

open MvPolynomial PEqualNP.ProofComplexity

abbrev P (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

noncomputable def visible {n m : ℕ} (F : Set (P n)) (a b : Fin m → P n) : Set (P n) :=
  F ∪ Set.range (fun i => a i * (1+b i)) ∪
    {z : P n | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i}

private theorem double_zero {n : ℕ} (x : P n) : x + x = 0 := by
  have h : (2 : P n) = 0 := CharP.cast_eq_zero (P n) 2
  rw [← two_mul, h, zero_mul]

private theorem one_add_degree {n : ℕ} {d : ℕ} {b : P n} (hb : b.totalDegree ≤ d) :
    (1+b).totalDegree ≤ d := by
  exact (totalDegree_add _ _).trans (max_le (by simp) hb)

private theorem diagonal {n m d : ℕ} (F : Set (P n)) (a b : Fin m → P n)
    (hdeg : ∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) (i : Fin m) :
    PCDerivable (visible F a b) (2*d+1) (a i*(1+b i)) := by
  refine .ax (Or.inl (Or.inr ⟨i,rfl⟩)) ?_
  apply (totalDegree_mul _ _).trans
  have ha := (hdeg i).1
  have hb := one_add_degree (hdeg i).2
  omega

private theorem minor {n m d : ℕ} (F : Set (P n)) (a b : Fin m → P n)
    (hdeg : ∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) (i j : Fin m) :
    PCDerivable (visible F a b) (2*d+1) (a i*b j+a j*b i) := by
  have hsmall (i j : Fin m) (hlt : i < j) :
      PCDerivable (visible F a b) (2*d+1) (a i*b j+a j*b i) := by
    refine .ax (Or.inr ⟨i,j,hlt,rfl⟩) ?_
    have ha := (totalDegree_mul (a i) (b j)).trans
      (Nat.add_le_add (hdeg i).1 (hdeg j).2)
    have hb := (totalDegree_mul (a j) (b i)).trans
      (Nat.add_le_add (hdeg j).1 (hdeg i).2)
    exact (totalDegree_add _ _).trans (max_le (by omega) (by omega))
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hsmall i j hij
  · rw [double_zero]
    exact .zero
  · simpa only [add_comm (a j*b i) (a i*b j)] using hsmall j i hji

private theorem square_deriv {n B : ℕ} (F : Set (P n)) (A : P n)
    (hbool : ∀ v : Fin n, X v * X v + X v ∈ F)
    (hA : 2*A.totalDegree ≤ B) : PCDerivable F B (A*A + A) := by
  apply Vanish459.vanish_derivable _ _ _ _ hbool
  · have hh := totalDegree_mul A A
    exact (totalDegree_add _ _).trans (max_le (by omega) (by omega))
  · intro x
    simp only [map_add, map_mul]
    exact (show ∀ e : ZMod 2, e*e+e=0 by decide) _

theorem cross {n m d : ℕ} (F : Set (P n)) (a b : Fin m → P n)
    (hbool : ∀ v : Fin n, X v * X v + X v ∈ F)
    (hdeg : ∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) (i j : Fin m) :
    PCDerivable (visible F a b) (3*d+2) (a i*(a j+b j)) := by
  have he : a i*(a i*b j+a j*b i) + a j*(a i*(1+b i)) + b j*(a i*a i+a i) =
      a i*(a j+b j) := by
    calc
      _ = a i*(a j+b j) + (a i*a i*b j+a i*a i*b j) + (a i*a j*b i+a i*a j*b i) := by ring
      _ = _ := by rw [double_zero, double_zero, add_zero, add_zero]
  rw [← he]
  apply PCDerivable.add
  · apply PCDerivable.add
    · apply Toolkit459.pcDerivable_mono
        (Toolkit459.pcDerivable_mul_left (minor (d := d) F a b hdeg i j) (a i)) _ subset_rfl
      apply max_le (by omega)
      have hi := (hdeg i).1
      have h1 := totalDegree_mul (a i) (b j)
      have h2 := totalDegree_mul (a j) (b i)
      have hj := hdeg j
      have hk := hdeg i
      have hm : (a i*b j+a j*b i).totalDegree ≤ 2*d+1 :=
        (totalDegree_add _ _).trans (max_le (by omega) (by omega))
      omega
    · apply Toolkit459.pcDerivable_mono
        (Toolkit459.pcDerivable_mul_left (diagonal (d := d) F a b hdeg i) (a j)) _ subset_rfl
      apply max_le (by omega)
      have hb := one_add_degree (hdeg i).2
      have h0 := totalDegree_mul (a i) (1+b i)
      have h1 := (hdeg i).1
      have h2 := (hdeg j).1
      omega
  · have hs : PCDerivable (visible F a b) (2*d+2) (a i*a i+a i) := by
      apply square_deriv _ _ (fun v => Or.inl (Or.inl (hbool v)))
      have hi := (hdeg i).1
      omega
    apply Toolkit459.pcDerivable_mono (Toolkit459.pcDerivable_mul_left hs (b j)) _ subset_rfl
    apply max_le (by omega)
    have h1 := (hdeg i).1
    have h2 := (hdeg j).2
    have h3 := totalDegree_mul (a i) (a i)
    have hsdeg : (a i*a i+a i).totalDegree ≤ 2*d+2 :=
      (totalDegree_add _ _).trans (max_le (by omega) (by omega))
    omega

end Cross459

namespace Combine459

open MvPolynomial PEqualNP.ProofComplexity Toolkit459

abbrev P (σ : Type) := MvPolynomial σ (ZMod 2)

private theorem line_degree {σ : Type} {A : Set (P σ)} {D : ℕ} {p : P σ}
    (line : PCDerivable A D p) : p.totalDegree ≤ D := by
  induction line with
  | ax _ h => exact h
  | zero => simp
  | add _ _ hp hq => exact (totalDegree_add _ _).trans (max_le hp hq)
  | mulX _ _ h _ => exact h

private theorem replay_factor {σ : Type} {A G : Set (P σ)} {D B : ℕ}
    (q : P σ) (hq : q.totalDegree + D ≤ B)
    (axiom_images : ∀ p ∈ A, p.totalDegree ≤ D → PCDerivable G B (q*p))
    {p : P σ} (line : PCDerivable A D p) : PCDerivable G B (q*p) := by
  induction line with
  | ax hp hd => exact axiom_images _ hp hd
  | zero => simpa only [mul_zero] using (PCDerivable.zero : PCDerivable G B 0)
  | add _ _ ih₀ ih₁ =>
    rw [mul_add]
    exact .add ih₀ ih₁
  | mulX i _ hd ih =>
    rw [mul_left_comm q (X i)]
    apply PCDerivable.mulX i ih
    rw [← mul_left_comm q (X i)]
    exact (totalDegree_mul _ _).trans ((Nat.add_le_add_left hd _).trans hq)

private theorem replay_product {σ : Type} {A₀ A₁ G : Set (P σ)} {D₀ D₁ B : ℕ}
    (hB : D₀+D₁ ≤ B)
    (axiom_products : ∀ a ∈ A₀, a.totalDegree ≤ D₀ →
      ∀ b ∈ A₁, b.totalDegree ≤ D₁ → PCDerivable G B (a*b))
    {p q : P σ} (hp : PCDerivable A₀ D₀ p) (hq : PCDerivable A₁ D₁ q) :
    PCDerivable G B (p*q) := by
  rw [mul_comm p q]
  apply replay_factor q (by have hq' := line_degree hq; omega) _ hp
  intro a ha hda
  rw [mul_comm q a]
  exact replay_factor a (by omega) (fun b hb hdb => axiom_products a ha hda b hb hdb) hq

theorem combine {σ I J : Type} (F G : Set (P σ)) (a : I → P σ) (b : J → P σ)
    {D₀ D₁ B : ℕ} (hB : D₀+D₁ ≤ B) (hF : F ⊆ G)
    (cross : ∀ i j, PCDerivable G B (a i*b j))
    (h₀ : PCRefutable (F ∪ Set.range a) D₀) (h₁ : PCRefutable (F ∪ Set.range b) D₁) :
    PCRefutable G B := by
  change PCDerivable G B 1
  have h₀' : PCDerivable (F ∪ Set.range a) D₀ 1 := h₀
  have h₁' : PCDerivable (F ∪ Set.range b) D₁ 1 := h₁
  suffices h : PCDerivable G B (1*1) by simpa only [one_mul] using h
  refine replay_product hB ?_ h₀' h₁'
  intro p hp hpd q hq hqd
  rcases hp with hp | ⟨i, rfl⟩
  · have ax : PCDerivable G D₀ p := .ax (hF hp) hpd
    have prod := pcDerivable_mul_left ax q
    rw [mul_comm q p] at prod
    exact pcDerivable_mono prod (max_le (by omega) (by omega)) subset_rfl
  · rcases hq with hq | ⟨j, rfl⟩
    · have ax : PCDerivable G D₁ q := .ax (hF hq) hqd
      have prod := pcDerivable_mul_left ax (a i)
      exact pcDerivable_mono prod (max_le (by omega) (by omega)) subset_rfl
    · exact cross i j

end Combine459

end PEqualNP.Outside.L_pcx_459

open PEqualNP.Outside.L_pcx_459

theorem PEqualNP.Outside.L_pcx_459 :
    ∀ (n m d : ℕ),
      let K := ZMod 2
      let V := Fin n
      let P := MvPolynomial V K
      let U := V ⊕ Unit
      let A := MvPolynomial U K
      let refP := @PEqualNP.ProofComplexity.PCRefutable V
      let refA := @PEqualNP.ProofComplexity.PCRefutable U
      let lift := fun p : P => MvPolynomial.rename (Sum.inl : V → U) p
      let h : A := MvPolynomial.X (Sum.inr ())
      ∀ (F : Set P) (a b : Fin m → P),
        (∀ v : V, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) →
        (∀ i, (a i).totalDegree ≤ d+1 ∧ (b i).totalDegree ≤ d) →
        let hidden := Set.image lift F ∪ {h*h+h} ∪ Set.range (fun i => lift (a i) + h * lift (b i))
        let visible := F ∪ Set.range (fun i => a i * (1+b i)) ∪
          {z : P | ∃ i j : Fin m, i < j ∧ z = a i * b j + a j * b i}
        (∀ B, refP visible B → refA hidden (max B (2*d+1))) ∧
        (∀ B₀ B₁, refP (F ∪ Set.range a) B₀ →
          refP (F ∪ Set.range (fun i => a i+b i)) B₁ →
          refP visible (max (B₀+B₁) (3*d+2))) ∧
        ∀ B, refA hidden B → refP visible (max (2*B) (3*d+2)) := by
  intro n m d
  dsimp only
  intro F a b hbool hdeg
  have project (B₀ B₁ : ℕ)
      (h₀ : PEqualNP.ProofComplexity.PCRefutable (F ∪ Set.range a) B₀)
      (h₁ : PEqualNP.ProofComplexity.PCRefutable (F ∪ Set.range (fun i => a i+b i)) B₁) :
      PEqualNP.ProofComplexity.PCRefutable (Cross459.visible F a b) (max (B₀+B₁) (3*d+2)) :=
    Combine459.combine F (Cross459.visible F a b) a (fun i => a i+b i)
      (le_max_left _ _) (fun _ hp => Or.inl (Or.inl hp))
      (fun i j => Toolkit459.pcDerivable_mono (Cross459.cross F a b hbool hdeg i j)
        (le_max_right _ _) subset_rfl) h₀ h₁
  refine ⟨Lift459.forward F a b hbool hdeg, project, ?_⟩
  intro B hh
  obtain ⟨h₀, h₁⟩ := Special459.two F a b hh
  change PEqualNP.ProofComplexity.PCRefutable (Cross459.visible F a b) (max (2*B) (3*d+2))
  rw [two_mul]
  exact project B B h₀ h₁
