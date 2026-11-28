import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_468
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
abbrev K := ZMod 2
abbrev V (m k : ℕ) := Fin m × Option (Fin k)
abbrev P (m k : ℕ) := MvPolynomial (V m k) K
abbrev Mask (m : ℕ) := Finset (Fin m)
noncomputable def part {m k : ℕ} (S : Mask m) (j : Option (Fin k)) : P m k := ∑ i∈S, X (i,j)
noncomputable def test {m k : ℕ} (S : Mask m) : P m k :=
  part S none * ∏ j : Fin k, (1 + part S (some j))
noncomputable def bools (m k : ℕ) : Set (P m k) := Set.range (fun v : V m k => X v * X v + X v)
noncomputable def pin {m k : ℕ} (S : Mask m) : Set (P m k) := {1 + part S none} ∪ Set.range (fun j : Fin k => part S (some j))
noncomputable def sys {m k : ℕ} (H : Finset (Mask m)) (S : Mask m) : Set (P m k) :=
  bools m k ∪ Set.image (test (k:=k)) (H : Set (Mask m)) ∪ pin S
def short (m k : ℕ) : Finset (Mask m) := Finset.univ.filter (fun S => S.card≤k+1)

variable {σ τ : Type}
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

theorem cube_sum (n : ℕ) (f : MvPolynomial (Fin n) (ZMod 2)) (hf : f.totalDegree < n) :
    ∑ x : Fin n → ZMod 2, MvPolynomial.eval x f = 0 := by
  classical
  simp only [MvPolynomial.eval_eq']
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun d hd => ?_)
  rw [← Finset.mul_sum]
  have hprod : ∑ x : Fin n → ZMod 2, ∏ i, x i ^ d i = ∏ i, ∑ c : ZMod 2, c ^ d i := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  have hex : ∃ i, d i = 0 := by
    by_contra hno
    have hpos : ∀ i, 1 ≤ d i := fun i => Nat.one_le_iff_ne_zero.2 (fun h => hno ⟨i, h⟩)
    have h1 := MvPolynomial.le_totalDegree hd
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
    have h2 : ∑ _i : Fin n, 1 ≤ ∑ i, d i := Finset.sum_le_sum (fun i _ => hpos i)
    simp at h2
    omega
  obtain ⟨i, hi⟩ := hex
  rw [hprod, Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
  rw [hi]
  decide

end Pool468
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
def bit {m : ℕ} (S : Mask m) (i : Fin m) : K := if i∈S then 1 else 0
def probe {m k : ℕ} (p a b : Fin m) (z : Fin (k+1) → K) : V m k → K
  | (i,none) => (if i=p then 1 else 0) + (if i=a then z 0 else 0)
  | (i,some j) => if i=b then z j.succ else 0

theorem sumProbe_none {m k : ℕ} (R : Mask m) (p a b : Fin m) (z : Fin (k+1) → K) :
    (∑ i∈R, probe p a b z (i,none)) = bit R p + bit R a*z 0 := by
  classical
  simp [probe,Finset.sum_add_distrib,bit,ite_mul]
theorem sumProbe_some {m k : ℕ} (R : Mask m) (p a b : Fin m) (z : Fin (k+1) → K) (j : Fin k) :
    (∑ i∈R, probe p a b z (i,some j)) = bit R b*z j.succ := by
  classical
  simp [probe,bit,ite_mul]
theorem affine_sum (c v : K) : ∑ z : K, (c+v*z) = v := by revert c v; decide
theorem factors (k : ℕ) (u : K → K) (v : Fin k → K → K) :
    (∑ z : Fin (k+1) → K, u (z 0) * ∏ j : Fin k, v j (z j.succ)) =
    (∑ y : K, u y) * ∏ j : Fin k, ∑ y : K, v j y := by
  classical
  let h : Fin (k+1) → K → K := Fin.cases u v
  have eq : (∑ z : Fin (k+1) → K, ∏ i : Fin (k+1), h i (z i)) =
      ∏ i : Fin (k+1), ∑ c : K, h i c := by
    rw [Finset.prod_univ_sum,Fintype.piFinset_univ]
  simpa only [Fin.prod_univ_succ,h,Fin.cases_zero,Fin.cases_succ] using eq

theorem profile {m k : ℕ} (hk : 0<k) (p a b : Fin m) (R : Mask m) :
    (∑ z : Fin (k+1) → K, eval (probe p a b z) (test R)) = bit R a * bit R b := by
  classical
  calc
    _ = ∑ z : Fin (k+1) → K, (bit R p + bit R a*z 0) *
        ∏ j : Fin k, (1 + bit R b*z j.succ) := by
      apply Finset.sum_congr rfl
      intro z _
      simp [test,part,sumProbe_none,sumProbe_some]
    _ = _ := by
      rw [factors k (fun c => bit R p + bit R a*c) (fun _ c => 1+bit R b*c),affine_sum]
      simp only [affine_sum,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      by_cases h : b∈R
      · simp [bit,h]
      · simp [bit,h,Nat.ne_of_gt hk]

noncomputable def probePoly {m k : ℕ} (p a b : Fin m) : V m k → MvPolynomial (Fin (k+1)) K
  | (i,none) => (if i=p then 1 else 0) + (if i=a then X 0 else 0)
  | (i,some j) => if i=b then X j.succ else 0
theorem probePoly_low {m k : ℕ} (p a b : Fin m) (v : V m k) :
    (probePoly (k:=k) p a b v).totalDegree≤1 := by
  obtain ⟨i,_|j⟩ := v
  · exact (totalDegree_add _ _).trans (max_le (by split <;> simp) (by split <;> simp))
  · simp only [probePoly]; split <;> simp
theorem probePoly_eval {m k : ℕ} (p a b : Fin m) (z : Fin (k+1) → K) (v : V m k) :
    eval z (probePoly p a b v)=probe p a b z v := by
  obtain ⟨i,_|j⟩ := v
  · simp only [probe,probePoly,map_add]
    split_ifs <;> simp
  · by_cases h : i=b <;> simp [probe,probePoly,h]

theorem evalProbeBind {m k : ℕ} (p a b : Fin m) (z : Fin (k+1) → K) (f : P m k) :
    eval (probe p a b z) f = eval z (bind₁ (probePoly p a b) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add g h ig ih => simp [map_add,ig,ih]
  | mul_X g i ig => simp [map_mul,bind₁_X_right,ig,probePoly_eval]

theorem cubeLow {m k : ℕ} (p a b : Fin m) (f : P m k) (hd : f.totalDegree<k+1) :
    ∑ z : Fin (k+1) → K, eval (probe p a b z) f = 0 := by
  have cap := totalDegree_bind₁_le (probePoly p a b) (probePoly_low p a b) f
  rw [one_mul] at cap
  have van := cube_sum (k+1) (bind₁ (probePoly p a b) f) (cap.trans_lt hd)
  convert van using 1
  apply Finset.sum_congr rfl
  intro z _
  exact evalProbeBind p a b z f

end Pool468
namespace Obstruction468
open MvPolynomial PEqualNP.ProofComplexity
abbrev K := ZMod 2
abbrev Poly (V : Type) := MvPolynomial V K
def agree {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (p : Poly V) (c : T → K) :=
  ∀ x∈Q, eval x p = ∑ i, c i * eval x (f i)
def separated {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (d : ℕ) :=
  ∀ (p : Poly V) (c : T → K), p.totalDegree<d → agree Q f p c → ∀ i, c i=0

theorem mulX_degree {V : Type} (v : V) (p : Poly V) (hp : p≠0) :
    p.totalDegree < (X v * p).totalDegree := by
  classical
  have ne : p.support.Nonempty := by
    by_contra! bad
    apply hp
    ext d
    have h : d∉p.support := by simp [bad]
    simpa using (not_ne_iff.mp (fun hn => h (mem_support_iff.mpr hn)))
  obtain ⟨e,he,eq⟩ := Finset.exists_mem_eq_sup p.support ne (fun m => m.sum (fun _ n => n))
  have step : (e+Finsupp.single v 1) ∈ (X v*p).support := by
    apply mem_support_iff.mpr
    have h := mem_support_iff.mp he
    have key : (X v*p).coeff (e+Finsupp.single v 1)=p.coeff e := by
      first
      | solve | simp
      | solve | simp [mul_comm (X v) p]
      | solve | simp [X,add_comm]
      | exact?
    rwa [key]
  have more := le_totalDegree step
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at more
  change (p.support.sup (fun m => m.sum (fun _ n => n))) < _
  omega

theorem lines {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (A : Set (Poly V))
    (d : ℕ) (van : ∀ a∈A, ∀ x∈Q, eval x a=0) (sep : separated Q f d)
    {p : Poly V} (h : PCDerivable (A ∪ Set.range f) d p) : ∃ c, agree Q f p c := by
  classical
  induction h with
  | ax hp _ =>
    rcases hp with a|⟨i,rfl⟩
    · exact ⟨0,fun x hx => by simpa using van _ a x hx⟩
    · refine ⟨fun j => if i=j then 1 else 0,?_⟩
      intro x hx
      simp
  | zero => exact ⟨0,fun x _ => by simp⟩
  | add _ _ il ir =>
    obtain ⟨a,ha⟩ := il
    obtain ⟨b,hb⟩ := ir
    refine ⟨a+b,?_⟩
    intro x hx
    simp only [map_add,ha x hx,hb x hx,Pi.add_apply,add_mul,Finset.sum_add_distrib]
  | @mulX v p hp hd ih =>
    refine ⟨0,?_⟩
    intro x hx
    by_cases hn : p=0
    · simp [hn]
    · have degree := mulX_degree v p hn
      obtain ⟨c,hc⟩ := ih
      have z := sep p c (by omega) hc
      have hz : eval x p=0 := by simpa [z] using hc x hx
      simp [hz]

theorem notRefutable {V T : Type} [Fintype T] (Q : Set (V → K)) (f : T → Poly V) (A : Set (Poly V))
    (d : ℕ) (hd : 0<d) (wit : Q.Nonempty) (van : ∀ a∈A, ∀ x∈Q, eval x a=0)
    (sep : separated Q f d) : ¬PCRefutable (A ∪ Set.range f) d := by
  intro contra
  obtain ⟨c,hc⟩ := lines Q f A d van sep contra
  have val := sep 1 c (by simpa using hd) hc
  obtain ⟨x,hx⟩ := wit
  have bad := hc x hx
  simpa [val] using bad

theorem cube_separates {V T B Z : Type} [Fintype T] [Fintype Z]
    (Q : Set (V → K)) (f : T → Poly V) (d : ℕ)
    (probe : B → Z → (V → K)) (inside : ∀ b z, probe b z∈Q)
    (low : ∀ p : Poly V, p.totalDegree < d → ∀ b, ∑ z, eval (probe b z) p=0)
    (profiles : LinearIndependent K (fun i : T => fun b : B => ∑ z, eval (probe b z) (f i))) :
    separated Q f d := by
  classical
  intro p c dp agree
  apply Fintype.linearIndependent_iff.mp profiles c
  funext b
  change (∑ i, c i • (fun b : B => ∑ z, eval (probe b z) (f i))) b = 0
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ z, eval (probe b z) p := Finset.sum_congr rfl (fun z _ => (agree _ (inside b z)).symm)
    _ = 0 := low p dp b
end Obstruction468
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
def pinned {m k : ℕ} (S : Mask m) (x : V m k → K) :=
  (∑ i∈S, x (i,none))=1 ∧ ∀ j : Fin k, (∑ i∈S, x (i,some j))=0

theorem vanishPin {m k : ℕ} (S : Mask m) (g : P m k) (hg : g∈bools m k ∪ pin S)
    (x : V m k → K) (hx : pinned S x) : eval x g=0 := by
  rcases hg with ⟨v,rfl⟩|hg
  · have field (a : K) : a*a+a=0 := by revert a; decide
    simp [field]
  · rcases hg with h|⟨j,rfl⟩
    · have eq : g=1+part S none := h
      rw [eq]
      simp [part,hx.1] <;> decide
    · simpa [part] using hx.2 j

theorem noRefBelow {m k : ℕ} (hk : 0<k) (S : Mask m) (sne : S.Nonempty)
    (H : Finset (Mask m)) {B : Type} (a b : B → Fin m)
    (awayA : ∀ t, a t∉S) (awayB : ∀ t, b t∉S)
    (li : LinearIndependent K (fun R : H => fun t : B => bit R.val (a t)*bit R.val (b t))) :
    ¬PCRefutable (sys (k:=k) H S) (k+1) := by
  classical
  obtain ⟨p,hp⟩ := sne
  let f : H → P m k := fun R => test R.val
  let Q : Set (V m k → K) := { x | pinned S x }
  have bank : sys (k:=k) H S = (bools m k ∪ pin S) ∪ Set.range f := by
    ext g
    constructor
    · rintro ((h|⟨R,hr,rfl⟩)|h)
      exact Or.inl (Or.inl h)
      exact Or.inr ⟨⟨R,hr⟩,rfl⟩
      exact Or.inl (Or.inr h)
    · rintro ((h|h)|⟨R,rfl⟩)
      exact Or.inl (Or.inl h)
      exact Or.inr h
      exact Or.inl (Or.inr ⟨R.val,R.property,rfl⟩)
  rw [bank]
  apply Obstruction468.notRefutable Q f (bools m k ∪ pin S) (k+1) (by omega)
  · refine ⟨probe p p p (fun _ : Fin (k+1) => 0),?_⟩
    constructor
    · rw [sumProbe_none]; simp [bit,hp]
    · intro j; rw [sumProbe_some]; simp
  · exact fun g hg x hx => vanishPin S g hg x hx
  apply Obstruction468.cube_separates Q f (k+1) (fun t z => probe p (a t) (b t) z)
  · intro t z
    constructor
    · rw [sumProbe_none]; simp [bit,hp,awayA t]
    · intro j; rw [sumProbe_some]; simp [bit,awayB t]
  · intro g dg t
    exact cubeLow p (a t) (b t) g dg
  · simpa only [f,profile hk] using li

end Pool468
namespace Donor454

open scoped BigOperators

abbrev F2 := ZMod 2

private lemma zmod2_ne_zero_iff (x : F2) : x ≠ 0 ↔ x = 1 := by
  revert x; decide

private def mask {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : F2 :=
  if i ∈ S then 1 else 0

private def supp {m : ℕ} (v : Fin m → F2) : Finset (Fin m) :=
  Finset.univ.filter (fun i => v i = 1)

private lemma mask_supp {m : ℕ} (v : Fin m → F2) : mask (supp v) = v := by
  funext i
  simp only [mask, supp, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : v i = 1
  · simp [h]
  · have h0 : v i = 0 := by revert h; generalize v i = x; revert x; decide
    simp [h0]

private lemma supp_mask {m : ℕ} (S : Finset (Fin m)) : supp (mask S) = S := by
  ext i
  simp only [supp, mask, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : i ∈ S <;> simp [h]

private lemma dot_eq_dotProduct {m : ℕ} (S : Finset (Fin m)) (a : Fin m → F2) :
    (∑ i ∈ S, a i) = dotProduct (mask S) a := by
  simp only [dotProduct, mask, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]

private def orth {m : ℕ} (U : Submodule F2 (Fin m → F2)) : Submodule F2 (Fin m → F2) :=
  { carrier := {v | ∀ u ∈ U, dotProduct v u = 0},
    zero_mem' := fun u _ => by simp [dotProduct], add_mem' := fun {v w} hv hw u hu => by
      simp only [Set.mem_ofPred_eq] at hv hw ⊢
      rw [add_dotProduct, hv u hu, hw u hu, zero_add],
    smul_mem' := fun c {v} hv u hu => by
      simp only [Set.mem_ofPred_eq] at hv ⊢
      rw [smul_dotProduct, hv u hu, smul_zero] }

private lemma le_orth_orth {m : ℕ} (U : Submodule F2 (Fin m → F2)) : U ≤ orth (orth U) := by
  intro u hu v hv
  rw [dotProduct_comm]
  exact hv u hu

private lemma finrank_orth_add {m : ℕ} (U : Submodule F2 (Fin m → F2)) :
    Module.finrank F2 (orth U) + Module.finrank F2 U = m := by
  classical
  let d := Module.finrank F2 U
  let b : Module.Basis (Fin d) F2 U := Module.finBasis F2 U
  let ev : (Fin m → F2) →ₗ[F2] (Fin d → F2) :=
    { toFun := fun v j => dotProduct v (b j).1
      map_add' := fun v w => by funext j; exact add_dotProduct v w (b j).1
      map_smul' := fun c v => by funext j; exact smul_dotProduct c v (b j).1 }
  have hker : LinearMap.ker ev = orth U := by
    ext v
    simp only [LinearMap.mem_ker]
    constructor
    · intro hv u hu
      have hu_eq : ∑ j : Fin d, b.repr ⟨u, hu⟩ j • (b j).1 = u := by
        have h1 := congr_arg Subtype.val (b.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at h1
        exact h1
      rw [← hu_eq, dotProduct_sum]
      apply Finset.sum_eq_zero
      intro j _
      have h0 : dotProduct v (b j).1 = 0 := congr_fun hv j
      rw [dotProduct_smul, h0, smul_zero]
    · intro hv
      funext j
      exact hv (b j).1 (b j).2
  have hsurj : Function.Surjective ev := by
    by_contra hns
    have hne : LinearMap.range ev ≠ ⊤ := fun htop =>
      hns (LinearMap.range_eq_top.mp htop)
    have hdim_lt : Module.finrank F2 (LinearMap.range ev) < d := by
      calc Module.finrank F2 (LinearMap.range ev)
          < Module.finrank F2 (Fin d → F2) := Submodule.finrank_lt hne
        _ = d := Module.finrank_fin_fun F2
    obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.range ev)
    have hW_pos : 0 < Module.finrank F2 W := by
      have hmod := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range ev) W
      rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, add_zero,
        Module.finrank_fin_fun F2] at hmod
      omega
    have hW_ne : W ≠ ⊥ := fun hbot => by rw [hbot, finrank_bot] at hW_pos; omega
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne
    let pW : (Fin d → F2) →ₗ[F2] W := Submodule.projectionOnto W (LinearMap.range ev) hW.symm
    let bw := Module.finBasis F2 W
    have hex_i : ∃ i, bw.repr ⟨w, hwW⟩ i ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hw0
      have h1 := congr_arg Subtype.val (bw.sum_repr ⟨w, hwW⟩)
      simp only [hall, zero_smul, Finset.sum_const_zero] at h1
      exact h1.symm
    rcases hex_i with ⟨i0, hi0⟩
    let φ : (Fin d → F2) →ₗ[F2] F2 := (bw.coord i0).comp pW
    let c : Fin d → F2 := fun j => φ (Pi.single j 1)
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hφw : φ w = bw.repr ⟨w, hwW⟩ i0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_left hW.symm ⟨w, hwW⟩]
        rfl
      have hφ_zero : φ w = 0 := by
        have hw_sum : w = ∑ j : Fin d, w j • Pi.single j (1 : F2) := by
          funext t
          simp [Finset.sum_apply, Pi.single_apply]
        rw [hw_sum, map_sum]
        apply Finset.sum_eq_zero
        intro j _
        have hcj : c j = 0 := congr_fun hc0 j
        rw [map_smul, show φ (Pi.single j 1) = c j from rfl, hcj, smul_zero]
      exact hi0 (hφw.symm.trans hφ_zero)
    have hcomb0 : ∑ j : Fin d, c j • (b j).1 = 0 := by
      funext t
      have hmem : ev (Pi.single t 1) ∈ LinearMap.range ev := ⟨Pi.single t 1, rfl⟩
      have hφ_ev : φ (ev (Pi.single t 1)) = 0 := by
        simp only [φ, LinearMap.comp_apply, pW]
        rw [Submodule.projectionOnto_apply_right hW.symm ⟨_, hmem⟩, map_zero]
      have hev_sum : ev (Pi.single t 1) =
          ∑ j : Fin d, (b j).1 t • Pi.single j (1 : F2) := by
        funext j
        simp [ev, dotProduct, Pi.single_apply, Finset.sum_apply]
      rw [hev_sum, map_sum] at hφ_ev
      simp only [map_smul, smul_eq_mul] at hφ_ev
      rw [Finset.sum_apply]
      calc ∑ j : Fin d, (c j • (b j).1) t
          = ∑ j : Fin d, (b j).1 t * c j := by
              refine Finset.sum_congr rfl fun j _ => by
                change c j * (b j).1 t = (b j).1 t * c j
                ring
        _ = 0 := hφ_ev
    have hcombU : ∑ j : Fin d, c j • b j = 0 := by
      apply Subtype.ext
      simpa using hcomb0
    have hc_all0 := Fintype.linearIndependent_iff.mp b.linearIndependent c hcombU
    exact hc_ne (funext hc_all0)
  have hrn := LinearMap.finrank_range_add_finrank_ker ev
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fin_fun F2,
    Module.finrank_fin_fun F2, hker, add_comm] at hrn
  exact hrn

private lemma orth_orth {m : ℕ} (U : Submodule F2 (Fin m → F2)) : orth (orth U) = U := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (le_orth_orth U)
  have h1 := finrank_orth_add U
  have h2 := finrank_orth_add (orth U)
  omega

private lemma orth_le_orth {m : ℕ} {U V : Submodule F2 (Fin m → F2)} (h : U ≤ V) :
    orth V ≤ orth U :=
  fun _ hv u hu => hv u (h hu)

private lemma exists_subspace_finrank_between {m : ℕ} (U : Submodule F2 (Fin m → F2)) (r : ℕ)
    (h1 : Module.finrank F2 U ≤ r) (h2 : r ≤ m) :
    ∃ W : Submodule F2 (Fin m → F2), U ≤ W ∧ Module.finrank F2 W = r := by
  classical
  obtain ⟨C, hUC⟩ := Submodule.exists_isCompl U
  have hC_dim : Module.finrank F2 C = m - Module.finrank F2 U := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq U C
    rw [hUC.sup_eq_top, hUC.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun F2] at hmod
    omega
  let d := r - Module.finrank F2 U
  have hd_le : d ≤ Module.finrank F2 C := by omega
  let bC := Module.finBasis F2 C
  let C0 : Submodule F2 (Fin m → F2) :=
    Submodule.span F2 (Set.range (fun i : Fin d => (bC ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1))
  have hC0_le : C0 ≤ C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (bC _).2
  have hC0_li : LinearIndependent F2
      (fun i : Fin d => (bC ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let g' : Fin (Module.finrank F2 C) → F2 :=
      fun j => if hj : j.val < d then g ⟨j.val, hj⟩ else 0
    have hsum' : ∑ j : Fin (Module.finrank F2 C), g' j • bC j = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, Submodule.coe_sum]
      calc ∑ j : Fin (Module.finrank F2 C), (g' j • bC j).1
          = ∑ j ∈ (Finset.univ : Finset (Fin (Module.finrank F2 C))).filter (fun j => j.val < d),
              (g' j • bC j).1 := by
              symm
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro j _ hnot
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
              simp [g', hnot]
        _ = ∑ i : Fin d, g i • (bC ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1 := by
              refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩) ?_ ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
              · intro i _
                exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩,
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, Fin.ext rfl⟩
              · intro j hj
                have hjd := (Finset.mem_filter.mp hj).2
                simp [g', hjd]
        _ = 0 := hg
    have hg'0 := Fintype.linearIndependent_iff.mp bC.linearIndependent g' hsum'
      ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩
    simpa [g', i.isLt] using hg'0
  have hC0_dim : Module.finrank F2 C0 = d := by
    rw [finrank_span_eq_card hC0_li, Fintype.card_fin]
  refine ⟨U ⊔ C0, le_sup_left, ?_⟩
  have hinf : U ⊓ C0 = ⊥ := eq_bot_iff.mpr (le_trans (inf_le_inf_left U hC0_le) hUC.inf_eq_bot.le)
  have hmod := Submodule.finrank_sup_add_finrank_inf_eq U C0
  rw [hinf, finrank_bot, add_zero, hC0_dim] at hmod
  omega

private lemma exists_linearEquiv_map_eq {m : ℕ} {v w : Fin m → F2} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : (Fin m → F2) ≃ₗ[F2] (Fin m → F2), e v = w := by
  classical
  let V : Submodule F2 (Fin m → F2) := Submodule.span F2 {v}
  let W : Submodule F2 (Fin m → F2) := Submodule.span F2 {w}
  have hV_dim : Module.finrank F2 V = 1 := finrank_span_singleton hv
  have hW_dim : Module.finrank F2 W = 1 := finrank_span_singleton hw
  obtain ⟨V', hVV'⟩ := Submodule.exists_isCompl V
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hV'_dim : Module.finrank F2 V' = m - 1 := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq V V'
    rw [hVV'.sup_eq_top, hVV'.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun F2, hV_dim] at hmod
    omega
  have hW'_dim : Module.finrank F2 W' = m - 1 := by
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hWW'.sup_eq_top, hWW'.inf_eq_bot, finrank_top, finrank_bot, add_zero,
      Module.finrank_fin_fun F2, hW_dim] at hmod
    omega
  let e1 : V ≃ₗ[F2] W :=
    ((LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv).symm).trans
      (LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) w hw)
  let e2 : V' ≃ₗ[F2] W' :=
    LinearEquiv.ofFinrankEq V' W' (hV'_dim.trans hW'_dim.symm)
  let eV : (V × V') ≃ₗ[F2] (Fin m → F2) := Submodule.prodEquivOfIsCompl V V' hVV'
  let eW : (W × W') ≃ₗ[F2] (Fin m → F2) := Submodule.prodEquivOfIsCompl W W' hWW'
  let e : (Fin m → F2) ≃ₗ[F2] (Fin m → F2) :=
    (eV.symm.trans (e1.prodCongr e2)).trans eW
  refine ⟨e, ?_⟩
  have hvV : v ∈ V := Submodule.subset_span (Set.mem_singleton v)
  have heV_v : eV (⟨v, hvV⟩, 0) = v := by simp [eV]
  have heV_symm : eV.symm v = (⟨v, hvV⟩, 0) := by
    apply eV.injective
    rw [eV.apply_symm_apply, heV_v]
  have he1_v : e1 ⟨v, hvV⟩ = ⟨w, Submodule.subset_span (Set.mem_singleton w)⟩ := by
    simp only [e1, LinearEquiv.trans_apply]
    have h1 : LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv (1 : F2) = ⟨v, hvV⟩ := by
      ext i; simp [LinearEquiv.toSpanNonzeroSingleton]
    have h2 : (LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv).symm ⟨v, hvV⟩ = 1 := by
      apply (LinearEquiv.toSpanNonzeroSingleton F2 (Fin m → F2) v hv).injective
      rw [LinearEquiv.apply_symm_apply, h1]
    rw [h2]
    ext i; simp [LinearEquiv.toSpanNonzeroSingleton]
  simp only [e, LinearEquiv.trans_apply, heV_symm, LinearEquiv.prodCongr_apply, Prod.map_apply,
    he1_v, map_zero]
  simp [eW]

private lemma bernoulli_nat (x y : ℕ) : ∀ t : ℕ, 0 < t →
    x ^ t + t * x ^ (t - 1) * y ≤ (x + y) ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    cases n with
    | zero => simp
    | succ m =>
      have hm := ih (Nat.succ_pos m)
      have hmul := Nat.mul_le_mul_right (x + y) hm
      rw [← pow_succ] at hmul
      calc x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y
          ≤ (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) := by
            have hexp : (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) =
                (x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y) + (m + 1) * x ^ m * y ^ 2 := by ring
            omega
        _ ≤ (x + y) ^ (m + 2) := hmul

private lemma main_proof (m k : ℕ) (hkm : k < m) :
    let K := ZMod 2
    let I := Fin m
    let X := I → K
    let msk := fun (S : Finset I) (i : I) => if i ∈ S then (1 : K) else 0
    let dot := fun (S : Finset I) (a : X) => ∑ i ∈ S, a i
    let works := fun (H : Finset (Finset I)) =>
      ∀ (a : X) (b : Fin k → X),
        (∃ u : Fin k → K, ∀ i, a i = ∑ j, u j * b j i) ↔
        ∀ S ∈ H, (∀ j, dot S (b j) = 0) → dot S a = 0
    (∀ H : Finset (Finset I), works H ↔
      ∀ W : Submodule K X, Module.finrank K W = m - k →
        Submodule.span K {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W} = W) ∧
    (∀ H : Finset (Finset I), works H →
      (m - k) * (2 ^ m - 1) ≤ H.card * (2 ^ (m - k) - 1) ∧
      ∀ w : ℕ, (∀ S ∈ H, S.card ≤ w) → m.choose (k + 1) ≤ H.card * w.choose (k + 1)) ∧
    works (Finset.univ.filter (fun S : Finset I => S.card ≤ k + 1)) ∧
    ∃ H : Finset (Finset I), works H ∧ H.card ≤ 2 ^ (k + 1) * ((k + 1) * m + 1) := by
  classical
  intro K I X msk dot works
  have hchar : ∀ H : Finset (Finset I), works H ↔
      ∀ W : Submodule K X, Module.finrank K W = m - k →
        Submodule.span K {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W} = W := by
    intro H
    constructor
    · intro hH W hW
      apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro x ⟨S, _, rfl, hxW⟩
        exact hxW
      · let M := Submodule.span K {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W}
        have hW_orth_dim : Module.finrank K (orth W) = k := by
          have := finrank_orth_add W
          change Module.finrank K (orth W) + Module.finrank K W = m at this
          omega
        let bW := Module.finBasis K (orth W)
        let b : Fin k → X := fun j => (bW ⟨j.val, by rw [hW_orth_dim]; exact j.isLt⟩).1
        have hspan_b : Submodule.span K (Set.range b) = orth W := by
          apply le_antisymm
          · apply Submodule.span_le.mpr
            rintro _ ⟨j, rfl⟩
            exact (bW _).2
          · intro x hx
            have h1 : (∑ i : Fin (Module.finrank K (orth W)), bW.repr ⟨x, hx⟩ i • (bW i).1) = x := by
              have h := congr_arg Subtype.val (bW.sum_repr ⟨x, hx⟩)
              rw [Submodule.coe_sum] at h
              exact h
            have hx_eq : x = ∑ j : Fin k,
                bW.repr ⟨x, hx⟩ ⟨j.val, by rw [hW_orth_dim]; exact j.isLt⟩ • b j := by
              conv_lhs => rw [← h1]
              refine Finset.sum_bij (fun i _ => ⟨i.val, by rw [← hW_orth_dim]; exact i.isLt⟩)
                ?_ ?_ ?_ ?_
              · intro _ _; exact Finset.mem_univ _
              · intro i1 _ i2 _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
              · intro j _
                exact ⟨⟨j.val, by rw [hW_orth_dim]; exact j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩
              · intro i _
                rfl
            rw [hx_eq]
            exact Submodule.sum_mem _ fun j _ =>
              Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        have horth_sub : orth M ≤ orth W := by
          intro a ha
          have ha_dot : ∀ S ∈ H, (∀ j, dot S (b j) = 0) → dot S a = 0 := by
            intro S hSH hSb
            have hSW : msk S ∈ W := by
              rw [← orth_orth W]
              intro u hu
              rw [← hspan_b] at hu
              refine Submodule.span_induction
                (p := fun v _ => dotProduct (msk S) v = 0) ?_ ?_ ?_ ?_ hu
              · rintro _ ⟨j, rfl⟩
                change dotProduct (mask S) (b j) = 0
                rw [← dot_eq_dotProduct]
                exact hSb j
              · simp [dotProduct]
              · intro v1 v2 _ _ h1 h2
                rw [dotProduct_add, h1, h2, zero_add]
              · intro c v _ hv
                rw [dotProduct_smul, hv, smul_zero]
            have hSM : msk S ∈ M := Submodule.subset_span ⟨S, hSH, rfl, hSW⟩
            change ∑ i ∈ S, a i = 0
            rw [dot_eq_dotProduct, dotProduct_comm]
            exact ha (msk S) hSM
          obtain ⟨u, hu⟩ := (hH a b).mpr ha_dot
          have ha_eq : a = ∑ j : Fin k, u j • b j := by
            funext i
            rw [Finset.sum_apply, hu i]
            rfl
          rw [ha_eq, ← hspan_b]
          exact Submodule.sum_mem _ fun j _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
        have hle := orth_le_orth horth_sub
        rw [orth_orth W, orth_orth M] at hle
        exact hle
    · intro hspan a b
      constructor
      · rintro ⟨u, hu⟩ S _ hSb
        simp only [dot, hu]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro j _
        rw [← Finset.mul_sum]
        have hj : ∑ i ∈ S, b j i = 0 := hSb j
        rw [hj, mul_zero]
      · intro hdot
        let U := Submodule.span K (Set.range b)
        have hU_dim : Module.finrank K U ≤ k := by
          have h1 := finrank_span_le_card (R := K) (Set.range b)
          have hsub : (Set.range b).toFinset ⊆ Finset.univ.image b := by
            intro x hx; simp at hx ⊢; exact hx
          exact h1.trans ((Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp)))
        have ha_orth : a ∈ orth (orth U) := by
          intro v hv
          have horthU_dim : m - k ≤ Module.finrank K (orth U) := by
            have := finrank_orth_add U
            change Module.finrank K (orth U) + Module.finrank K U = m at this
            omega
          have hv_orth : ∃ W : Submodule K X, W ≤ orth U ∧ v ∈ W ∧ Module.finrank K W = m - k := by
            have hspanv_le : Submodule.span K {v} ≤ orth U :=
              Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hv)
            have hspanv_dim : Module.finrank K (Submodule.span K {v}) ≤ m - k := by
              by_cases hv0 : v = 0
              · subst hv0
                rw [Submodule.span_zero_singleton, finrank_bot]
                omega
              · rw [finrank_span_singleton hv0]; omega
            obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Submodule.span K {v})
            let C1 : Submodule K X := C ⊓ orth U
            have hsup1 : Submodule.span K {v} ⊔ C1 = orth U := by
              apply le_antisymm
              · exact sup_le hspanv_le inf_le_right
              · intro x hx
                have hmem : x ∈ Submodule.span K {v} ⊔ C := by rw [hC.sup_eq_top]; trivial
                rcases Submodule.mem_sup.mp hmem with ⟨y, hy, z, hz, rfl⟩
                have hzU : z ∈ orth U := by
                  have : y + z - y ∈ orth U := (orth U).sub_mem hx (hspanv_le hy)
                  simpa using this
                exact Submodule.add_mem_sup hy ⟨hz, hzU⟩
            have hinf1 : Submodule.span K {v} ⊓ C1 = ⊥ :=
              eq_bot_iff.mpr (le_trans (inf_le_inf_left _ inf_le_left) hC.inf_eq_bot.le)
            have hC1_dim : Module.finrank K (Submodule.span K {v}) + Module.finrank K C1 =
                Module.finrank K (orth U) := by
              have hmod := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {v}) C1
              rw [hsup1, hinf1, finrank_bot, add_zero] at hmod
              exact hmod.symm
            let d := (m - k) - Module.finrank K (Submodule.span K {v})
            have hd_le : d ≤ Module.finrank K C1 := by omega
            let bC1 := Module.finBasis K C1
            let C0 : Submodule K X := Submodule.span K
              (Set.range (fun i : Fin d => (bC1 ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1))
            have hC0_le : C0 ≤ C1 := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (bC1 _).2)
            have hC0_li : LinearIndependent K
                (fun i : Fin d => (bC1 ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1) := by
              rw [Fintype.linearIndependent_iff]
              intro g hg i
              let g' : Fin (Module.finrank K C1) → K :=
                fun j => if hj : j.val < d then g ⟨j.val, hj⟩ else 0
              have hsum' : ∑ j : Fin (Module.finrank K C1), g' j • bC1 j = 0 := by
                apply Subtype.ext
                rw [ZeroMemClass.coe_zero, Submodule.coe_sum]
                calc ∑ j : Fin (Module.finrank K C1), (g' j • bC1 j).1
                    = ∑ j ∈ (Finset.univ : Finset (Fin (Module.finrank K C1))).filter (fun j => j.val < d),
                        (g' j • bC1 j).1 := by
                        symm
                        apply Finset.sum_subset (Finset.filter_subset _ _)
                        intro j _ hnot
                        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
                        simp [g', hnot]
                  _ = ∑ i : Fin d, g i • (bC1 ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩).1 := by
                        refine Finset.sum_bij (fun j hj => ⟨j.val, (Finset.mem_filter.mp hj).2⟩)
                          ?_ ?_ ?_ ?_
                        · intro _ _; exact Finset.mem_univ _
                        · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congr_arg Fin.val h)
                        · intro i _
                          exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩,
                            Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩, Fin.ext rfl⟩
                        · intro j hj
                          have hjd := (Finset.mem_filter.mp hj).2
                          simp [g', hjd]
                  _ = 0 := hg
              have hg'0 := Fintype.linearIndependent_iff.mp bC1.linearIndependent g' hsum'
                ⟨i.val, lt_of_lt_of_le i.isLt hd_le⟩
              simpa [g', i.isLt] using hg'0
            have hC0_dim : Module.finrank K C0 = d := by
              rw [finrank_span_eq_card hC0_li, Fintype.card_fin]
            refine ⟨Submodule.span K {v} ⊔ C0, sup_le hspanv_le (le_trans hC0_le inf_le_right),
              Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton v)), ?_⟩
            have hinf0 : Submodule.span K {v} ⊓ C0 = ⊥ :=
              eq_bot_iff.mpr (le_trans (inf_le_inf_left _ hC0_le) (le_of_eq hinf1))
            have hmod := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {v}) C0
            rw [hinf0, finrank_bot, add_zero, hC0_dim] at hmod
            exact hmod.trans (by omega)
          rcases hv_orth with ⟨W, hW_le, hvW, hW_dim⟩
          rw [← hspan W hW_dim] at hvW
          rw [dotProduct_comm]
          refine Submodule.span_induction (p := fun w _ => dotProduct w a = 0) ?_ ?_ ?_ ?_ hvW
          · rintro _ ⟨S, hSH, rfl, hSW⟩
            change dotProduct (mask S) a = 0
            rw [← dot_eq_dotProduct]
            apply hdot S hSH
            intro j
            change ∑ i ∈ S, b j i = 0
            rw [dot_eq_dotProduct]
            exact hW_le hSW (b j) (Submodule.subset_span ⟨j, rfl⟩)
          · simp [dotProduct]
          · intro w1 w2 _ _ h1 h2
            rw [add_dotProduct, h1, h2, zero_add]
          · intro c w _ hw
            rw [smul_dotProduct, hw, smul_zero]
        rw [orth_orth U] at ha_orth
        rcases Submodule.mem_span_range_iff_exists_fun K |>.mp ha_orth with ⟨u, hu⟩
        refine ⟨u, fun i => ?_⟩
        have hi := congr_fun hu.symm i
        rw [Finset.sum_apply] at hi
        exact hi
  refine ⟨hchar, ?_, ?_, ?_⟩
  · intro H hH
    have hH_span := (hchar H).mp hH
    constructor
    · haveI : Fintype (Submodule K X) := Fintype.ofFinite _
      let Subs : Finset (Submodule K X) :=
        Finset.univ.filter (fun W : Submodule K X => Module.finrank K W = m - k)
      have hSubs_pos : 0 < Subs.card := by
        obtain ⟨W0, _, hW0⟩ := exists_subspace_finrank_between (⊥ : Submodule K X) (m - k)
          (by simp) (by omega)
        exact Finset.card_pos.mpr ⟨W0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hW0⟩⟩
      let NZ : Finset X := Finset.univ.filter (fun v : X => v ≠ 0)
      have hNZ_card : NZ.card = 2 ^ m - 1 := by
        have hcomp : NZ.card + (Finset.univ.filter (fun v : X => v = 0)).card = 2 ^ m := by
          rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
          calc ∑ v : X, ((if v ≠ 0 then 1 else 0) + (if v = 0 then 1 else 0))
              = ∑ _v : X, 1 := Finset.sum_congr rfl fun v _ => by by_cases h : v = 0 <;> simp [h]
            _ = Fintype.card X := by simp
            _ = 2 ^ m := by simp [X, K, I]
        have h0 : (Finset.univ.filter (fun v : X => v = 0)).card = 1 := by
          have : (Finset.univ.filter (fun v : X => v = 0)) = {0} := by ext v; simp
          rw [this, Finset.card_singleton]
        omega
      let deg : X → ℕ := fun v => (Subs.filter (fun W => v ∈ W)).card
      have hdeg_const : ∀ v ∈ NZ, ∀ w ∈ NZ, deg v = deg w := by
        intro v hv w hw
        simp only [NZ, Finset.mem_filter, Finset.mem_univ, true_and] at hv hw
        obtain ⟨e, he⟩ := exists_linearEquiv_map_eq hv hw
        refine Finset.card_bij (fun W _ => W.map e.toLinearMap) ?_ ?_ ?_
        · intro W hW
          simp only [Finset.mem_filter, Subs, Finset.mem_univ, true_and] at hW ⊢
          refine ⟨?_, ⟨v, hW.2, he⟩⟩
          rw [LinearEquiv.finrank_map_eq, hW.1]
        · intro W1 _ W2 _ h
          ext x
          have hx := congr_arg (fun U : Submodule K X => e x ∈ U) h
          simp only [Submodule.mem_map, LinearEquiv.coe_coe, e.injective.eq_iff, exists_eq_right] at hx
          exact eq_iff_iff.mp hx
        · intro W hW
          simp only [Finset.mem_filter, Subs, Finset.mem_univ, true_and] at hW
          refine ⟨W.map e.symm.toLinearMap, ?_, ?_⟩
          · simp only [Finset.mem_filter, Subs, Finset.mem_univ, true_and]
            refine ⟨?_, ⟨w, hW.2, by rw [← he]; exact e.symm_apply_apply v⟩⟩
            rw [LinearEquiv.finrank_map_eq, hW.1]
          · ext x
            simp only [Submodule.mem_map, LinearEquiv.coe_coe]
            constructor
            · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
              simpa using hy
            · intro hx
              exact ⟨e.symm x, ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
      have hNZ_ne : NZ.Nonempty := by
        have hpos : 0 < 2 ^ m - 1 := by
          have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        exact Finset.card_pos.mp (by omega)
      obtain ⟨v0, hv0⟩ := hNZ_ne
      let C1 := deg v0
      have hcount_nz : Subs.card * (2 ^ (m - k) - 1) = (2 ^ m - 1) * C1 := by
        have h1 : ∑ W ∈ Subs, (NZ.filter (fun v => v ∈ W)).card = ∑ v ∈ NZ, deg v := by
          simp only [deg, Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
        have hW_nz : ∀ W ∈ Subs, (NZ.filter (fun v => v ∈ W)).card = 2 ^ (m - k) - 1 := by
          intro W hW
          simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and] at hW
          have hcardW : (Finset.univ.filter (fun v : X => v ∈ W)).card = 2 ^ (m - k) := by
            rw [← Fintype.card_subtype]
            have hnc := Module.natCard_eq_pow_finrank (K := K) (V := W)
            rw [Nat.card_eq_fintype_card, Nat.card_zmod, hW] at hnc
            exact hnc
          have hsplit : (NZ.filter (fun v => v ∈ W)).card + 1 =
              (Finset.univ.filter (fun v : X => v ∈ W)).card := by
            have h0 : (0 : X) ∈ Finset.univ.filter (fun v : X => v ∈ W) := by simp
            have herase : NZ.filter (fun v => v ∈ W) =
                (Finset.univ.filter (fun v : X => v ∈ W)).erase 0 := by
              ext v; simp [NZ, and_comm]
            rw [herase, Finset.card_erase_of_mem h0]
            have hpos := Finset.card_pos.mpr ⟨0, h0⟩
            omega
          omega
        have hL : ∑ W ∈ Subs, (NZ.filter (fun v => v ∈ W)).card = Subs.card * (2 ^ (m - k) - 1) := by
          rw [Finset.sum_congr rfl hW_nz, Finset.sum_const, smul_eq_mul]
        have hR : ∑ v ∈ NZ, deg v = (2 ^ m - 1) * C1 := by
          rw [Finset.sum_congr rfl (fun v hv => hdeg_const v hv v0 hv0), Finset.sum_const,
            smul_eq_mul, hNZ_card]
        rw [← hL, h1, hR]
      have hcount_H : Subs.card * (m - k) ≤ H.card * C1 := by
        let Hnz := H.filter (fun S => msk S ≠ 0)
        have hper_W : ∀ W ∈ Subs, m - k ≤ (Hnz.filter (fun S => msk S ∈ W)).card := by
          intro W hW
          simp only [Subs, Finset.mem_filter, Finset.mem_univ, true_and] at hW
          have hsp := hH_span W hW
          have hsub : {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W} ⊆
              ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X) ∪ {0} := by
            rintro x ⟨S, hSH, rfl, hSW⟩
            by_cases h0 : msk S = 0
            · exact Or.inr h0
            · left
              simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Hnz]
              exact ⟨S, ⟨⟨hSH, h0⟩, hSW⟩, rfl⟩
          have hsp_le : W ≤ Submodule.span K ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X) := by
            conv_lhs => rw [← hsp]
            apply Submodule.span_le.mpr
            intro x hx
            rcases hsub hx with hx1 | hx0
            · exact Submodule.subset_span hx1
            · rw [Set.mem_singleton_iff.mp hx0]; exact Submodule.zero_mem _
          have hle_fin : m - k ≤
              Module.finrank K (Submodule.span K ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)) := by
            rw [← hW]
            exact Submodule.finrank_mono hsp_le
          have hle_card : Module.finrank K (Submodule.span K
              ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)) ≤
              ((Hnz.filter (fun S => msk S ∈ W)).image msk).card := by
            have h1 := finrank_span_le_card (R := K) ((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)
            have h2 : (((Hnz.filter (fun S => msk S ∈ W)).image msk : Set X)).toFinset =
                (Hnz.filter (fun S => msk S ∈ W)).image msk := by
              ext x; simp
            rwa [h2] at h1
          exact le_trans hle_fin (le_trans hle_card Finset.card_image_le)
        have hswap : ∑ W ∈ Subs, (Hnz.filter (fun S => msk S ∈ W)).card =
            ∑ S ∈ Hnz, deg (msk S) := by
          simp only [deg, Finset.card_eq_sum_ones, Finset.sum_filter]
          rw [Finset.sum_comm]
        calc Subs.card * (m - k)
            = ∑ _W ∈ Subs, (m - k) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ W ∈ Subs, (Hnz.filter (fun S => msk S ∈ W)).card := Finset.sum_le_sum hper_W
          _ = ∑ S ∈ Hnz, deg (msk S) := hswap
          _ = ∑ _S ∈ Hnz, C1 := Finset.sum_congr rfl fun S hS =>
                hdeg_const (msk S) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  (Finset.mem_filter.mp hS).2⟩) v0 hv0
          _ = Hnz.card * C1 := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ H.card * C1 := Nat.mul_le_mul_right C1 (Finset.card_filter_le _ _)
      have hmul : Subs.card * ((m - k) * (2 ^ m - 1)) ≤ Subs.card * (H.card * (2 ^ (m - k) - 1)) := by
        calc Subs.card * ((m - k) * (2 ^ m - 1))
            = (Subs.card * (m - k)) * (2 ^ m - 1) := by ring
          _ ≤ (H.card * C1) * (2 ^ m - 1) := Nat.mul_le_mul_right _ hcount_H
          _ = H.card * ((2 ^ m - 1) * C1) := by ring
          _ = H.card * (Subs.card * (2 ^ (m - k) - 1)) := by rw [← hcount_nz]
          _ = Subs.card * (H.card * (2 ^ (m - k) - 1)) := by ring
      exact Nat.le_of_mul_le_mul_left hmul hSubs_pos
    · intro w hw
      let SubsK : Finset (Finset I) := Finset.univ.powersetCard (k + 1)
      have hSubsK_card : SubsK.card = m.choose (k + 1) := by
        simp [SubsK, I, Finset.card_powersetCard]
      have hcover_T : ∀ T ∈ SubsK, ∃ S ∈ H, T ⊆ S := by
        intro T hT
        rw [Finset.mem_powersetCard] at hT
        have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨i0, hi0⟩ := hT_ne
        let W : Submodule K X :=
          { carrier := {v : X | ∀ i ∈ T, v i = v i0},
            zero_mem' := fun _ _ => rfl, add_mem' := fun {v1 v2} h1 h2 i hi => by
              change v1 i + v2 i = v1 i0 + v2 i0
              rw [h1 i hi, h2 i hi],
            smul_mem' := fun c {v} hv i hi => by
              change c * v i = c * v i0
              rw [hv i hi] }
        have hW_dim : Module.finrank K W = m - k := by
          let ev : X →ₗ[K] ({i : I // i ∈ T.erase i0} → K) :=
            { toFun := fun v j => v j.1 - v i0
              map_add' := fun v1 v2 => by
                funext j
                change (v1 j.1 + v2 j.1) - (v1 i0 + v2 i0) = (v1 j.1 - v1 i0) + (v2 j.1 - v2 i0)
                ring
              map_smul' := fun c v => by
                funext j
                change c * v j.1 - c * v i0 = c * (v j.1 - v i0)
                ring }
          have hker : LinearMap.ker ev = W := by
            ext v
            simp only [LinearMap.mem_ker]
            constructor
            · intro hv i hi
              by_cases hii : i = i0
              · rw [hii]
              · have hmem : i ∈ T.erase i0 := Finset.mem_erase.mpr ⟨hii, hi⟩
                exact sub_eq_zero.mp (congr_fun hv ⟨i, hmem⟩)
            · intro hv
              funext j
              exact sub_eq_zero.mpr (hv j.1 (Finset.mem_of_mem_erase j.2))
          have hsurj : Function.Surjective ev := by
            intro y
            let v : X := fun i => if hi : i ∈ T.erase i0 then y ⟨i, hi⟩ else 0
            refine ⟨v, ?_⟩
            funext j
            have hi0_not : i0 ∉ T.erase i0 := Finset.notMem_erase i0 T
            change v j.1 - v i0 = y j
            simp only [v, j.2, ↓reduceDIte, hi0_not, sub_zero]
          have hrn := LinearMap.finrank_range_add_finrank_ker ev
          rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
            Module.finrank_fin_fun F2, hker, Fintype.card_coe, Finset.card_erase_of_mem hi0,
            hT.2] at hrn
          omega
        have hmaskT : msk T ∈ W := fun i hi => by simp [msk, hi, hi0]
        rw [← hH_span W hW_dim] at hmaskT
        by_contra hno
        push Not at hno
        have hall0 : ∀ x ∈ {x : X | ∃ S ∈ H, x = msk S ∧ x ∈ W}, x i0 = 0 := by
          rintro x ⟨S, hSH, rfl, hSW⟩
          by_contra hx0
          have hx1 : msk S i0 = 1 := (zmod2_ne_zero_iff _).mp hx0
          apply hno S hSH
          intro i hi
          have h1 : msk S i = 1 := (hSW i hi).trans hx1
          simp only [msk] at h1
          by_contra hni
          simp [hni] at h1
        have hT0 : msk T i0 = 0 := by
          refine Submodule.span_induction (p := fun x _ => x i0 = 0) ?_ ?_ ?_ ?_ hmaskT
          · intro x hx; exact hall0 x hx
          · rfl
          · intro x y _ _ hx hy; change x i0 + y i0 = 0; rw [hx, hy, zero_add]
          · intro c x _ hx; change c * x i0 = 0; rw [hx, mul_zero]
        simp [msk, hi0] at hT0
      have hsub : SubsK ⊆ H.biUnion (fun S => S.powersetCard (k + 1)) := by
        intro T hT
        rcases hcover_T T hT with ⟨S, hSH, hTS⟩
        exact Finset.mem_biUnion.mpr ⟨S, hSH, Finset.mem_powersetCard.mpr ⟨hTS, (Finset.mem_powersetCard.mp hT).2⟩⟩
      calc m.choose (k + 1)
          = SubsK.card := hSubsK_card.symm
        _ ≤ (H.biUnion (fun S => S.powersetCard (k + 1))).card := Finset.card_le_card hsub
        _ ≤ ∑ S ∈ H, (S.powersetCard (k + 1)).card := Finset.card_biUnion_le
        _ = ∑ S ∈ H, S.card.choose (k + 1) := by
              refine Finset.sum_congr rfl fun S _ => Finset.card_powersetCard (k + 1) S
        _ ≤ ∑ _S ∈ H, w.choose (k + 1) :=
              Finset.sum_le_sum fun S hS => Nat.choose_le_choose (k + 1) (hw S hS)
        _ = H.card * w.choose (k + 1) := by rw [Finset.sum_const, smul_eq_mul]
  · rw [hchar]
    intro W hW
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨S, _, rfl, hxW⟩
      exact hxW
    · let q : X →ₗ[K] (X ⧸ W) := Submodule.mkQ W
      let gen : Set (X ⧸ W) := Set.range (fun i : I => q (Pi.single i 1))
      have hgen_span : Submodule.span K gen = ⊤ := by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective W y
        have hx_sum : x = ∑ i : I, x i • Pi.single i (1 : K) := by
          funext t; simp [Finset.sum_apply, Pi.single_apply]
        rw [hx_sum, map_sum]
        exact Submodule.sum_mem _ fun i _ =>
          Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range.mpr ⟨i, rfl⟩))
      obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent K gen
      have hB_card : B.toFinset.card = k := by
        have h1 := finrank_span_set_eq_card (R := K) hBli
        rw [hBspan, hgen_span, finrank_top] at h1
        have hq_dim : Module.finrank K (X ⧸ W) = k := by
          have := Submodule.finrank_quotient_add_finrank W
          rw [Module.finrank_fin_fun F2, hW] at this
          omega
        omega
      have hex_idx : ∀ y ∈ B.toFinset, ∃ i : I, q (Pi.single i 1) = y := by
        intro y hy
        exact hBsub (Set.mem_toFinset.mp hy)
      choose idx hidx using hex_idx
      let P : Finset I := B.toFinset.attach.image (fun y => idx y.1 y.2)
      have hP_card : P.card ≤ k := by
        calc P.card
            ≤ B.toFinset.attach.card := Finset.card_image_le
          _ = B.toFinset.card := Finset.card_attach
          _ = k := hB_card
      have hP_span : Submodule.span K (Set.range (fun i : P => q (Pi.single i.1 1))) = ⊤ := by
        rw [eq_top_iff, ← hgen_span, ← hBspan]
        apply Submodule.span_le.mpr
        intro y hy
        have hyf : y ∈ B.toFinset := Set.mem_toFinset.mpr hy
        have hmemP : idx y hyf ∈ P :=
          Finset.mem_image.mpr ⟨⟨y, hyf⟩, Finset.mem_attach _ _, rfl⟩
        exact Submodule.subset_span ⟨⟨idx y hyf, hmemP⟩, hidx y hyf⟩
      have hex_v : ∀ j : I, j ∉ P →
          ∃ v : X, v ∈ W ∧ (supp v).card ≤ k + 1 ∧ ∀ t : I, t ∉ P → v t = if t = j then 1 else 0 := by
        intro j hjP
        have hqj : q (Pi.single j 1) ∈ Submodule.span K (Set.range (fun i : P => q (Pi.single i.1 1))) := by
          rw [hP_span]; trivial
        rcases (Submodule.mem_span_range_iff_exists_fun K).mp hqj with ⟨c, hc⟩
        let v : X := Pi.single j 1 - ∑ i : P, c i • Pi.single i.1 (1 : K)
        have hvW : v ∈ W := by
          rw [← Submodule.Quotient.mk_eq_zero W]
          change q v = 0
          simp only [v, map_sub, map_sum, map_smul, hc, sub_self]
        have hv_out : ∀ t : I, t ∉ P → v t = if t = j then 1 else 0 := by
          intro t htP
          change (Pi.single (M := fun _ : I => K) j (1 : K) t) -
            (∑ i : P, c i • Pi.single (M := fun _ : I => K) i.1 (1 : K)) t = _
          rw [Pi.single_apply, Finset.sum_apply]
          have hsum0 : ∑ i : P, (c i • Pi.single (M := fun _ : I => K) i.1 (1 : K)) t = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            have hit : t ≠ i.1 := fun h => htP (h ▸ i.2)
            simp [Pi.single_apply, hit]
          rw [hsum0, sub_zero]
        have hsupp_sub : supp v ⊆ insert j P := by
          intro t ht
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          by_cases htj : t = j
          · exact Finset.mem_insert.mpr (Or.inl htj)
          · by_cases htP : t ∈ P
            · exact Finset.mem_insert.mpr (Or.inr htP)
            · exfalso
              have hv0 : v t = 0 := by rw [hv_out t htP, if_neg htj]
              rw [hv0] at ht
              exact zero_ne_one ht
        have hsupp_card : (supp v).card ≤ k + 1 := by
          calc (supp v).card
              ≤ (insert j P).card := Finset.card_le_card hsupp_sub
            _ ≤ P.card + 1 := Finset.card_insert_le j P
            _ ≤ k + 1 := by omega
        exact ⟨v, hvW, hsupp_card, hv_out⟩
      let Pc : Finset I := Finset.univ \ P
      have hPc_card : m - k ≤ Pc.card := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
        omega
      choose vs hvsW hvs_card hvs_coord using hex_v
      let f : Pc → X := fun j => vs j.1 (Finset.mem_sdiff.mp j.2).2
      have hf_li : LinearIndependent K f := by
        rw [Fintype.linearIndependent_iff]
        intro g hg j
        have h0 : (∑ i : Pc, g i • f i) j.1 = 0 := by rw [hg]; rfl
        rw [Finset.sum_apply] at h0
        have hsum : (∑ i : Pc, (g i • f i) j.1) = g j := by
          calc ∑ i : Pc, (g i • f i) j.1
              = ∑ i : Pc, g i * (if j.1 = i.1 then 1 else 0) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  change g i * vs i.1 (Finset.mem_sdiff.mp i.2).2 j.1 = _
                  rw [hvs_coord i.1 (Finset.mem_sdiff.mp i.2).2 j.1 (Finset.mem_sdiff.mp j.2).2]
            _ = ∑ i : Pc, if i = j then g i else 0 := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  by_cases hij : i = j
                  · subst hij; simp
                  · have hne : j.1 ≠ i.1 := fun h => hij (Subtype.ext h.symm)
                    simp [hij, hne]
            _ = g j := by simp
        rw [hsum] at h0
        exact h0
      let M := Submodule.span K {x : X | ∃ S ∈ Finset.univ.filter (fun S : Finset I => S.card ≤ k + 1),
        x = msk S ∧ x ∈ W}
      have hspan_f_le : Submodule.span K (Set.range f) ≤ M := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        apply Submodule.subset_span
        refine ⟨supp (f j), ?_, (mask_supp (f j)).symm, hvsW j.1 (Finset.mem_sdiff.mp j.2).2⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hvs_card j.1 (Finset.mem_sdiff.mp j.2).2
      have hM_le : M ≤ W := Submodule.span_le.mpr (by rintro _ ⟨_, _, rfl, hxW⟩; exact hxW)
      have hdim_M : Module.finrank K M = m - k := by
        have h1 : Pc.card ≤ Module.finrank K M := by
          calc Pc.card = Fintype.card Pc := (Fintype.card_coe Pc).symm
            _ = Module.finrank K (Submodule.span K (Set.range f)) :=
                (finrank_span_eq_card hf_li).symm
            _ ≤ Module.finrank K M := Submodule.finrank_mono hspan_f_le
        have h2 : Module.finrank K M ≤ m - k := by
          rw [← hW]; exact Submodule.finrank_mono hM_le
        omega
      have hMW : M = W := Submodule.eq_of_le_of_finrank_eq hM_le (hdim_M.trans hW.symm)
      exact le_of_eq hMW.symm
  · let M := 2 ^ (k + 1)
    let L := (k + 1) * m
    let N := M * (L + 1)
    have hM_ge2 : 2 ≤ M := by
      have : 2 ^ 1 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hpow_strict : (M - 1) ^ N * 2 ^ L < M ^ N := by
      have hstep : 2 * (M - 1) ^ M ≤ M ^ M := by
        have h1 := bernoulli_nat (M - 1) 1 M (by omega)
        rw [Nat.sub_add_cancel (by omega), mul_one] at h1
        have h2 : (M - 1) ^ M ≤ M * (M - 1) ^ (M - 1) := by
          have hpow : (M - 1) ^ M = (M - 1) * (M - 1) ^ (M - 1) := by
            rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]
          rw [hpow]
          exact Nat.mul_le_mul_right _ (Nat.sub_le M 1)
        omega
      have hpow_le : (2 * (M - 1) ^ M) ^ (L + 1) ≤ (M ^ M) ^ (L + 1) :=
        Nat.pow_le_pow_left hstep (L + 1)
      rw [mul_pow, ← pow_mul, ← pow_mul] at hpow_le
      have hpos : 0 < (M - 1) ^ N := Nat.pow_pos (by omega)
      have h2lt : 2 ^ L < 2 ^ (L + 1) := Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self L)
      calc (M - 1) ^ N * 2 ^ L
          < (M - 1) ^ N * 2 ^ (L + 1) := Nat.mul_lt_mul_of_pos_left h2lt hpos
        _ = 2 ^ (L + 1) * (M - 1) ^ N := by ring
        _ ≤ M ^ N := hpow_le
    let GoodPair := (Fin k → X) × X
    let hit : GoodPair → X → Prop := fun p v =>
      (∀ j : Fin k, dotProduct v (p.1 j) = 0) ∧ dotProduct v p.2 = 1
    let Valid : Finset GoodPair := Finset.univ.filter (fun p =>
      ∃ v : X, hit p v)
    have hValid_card : Valid.card ≤ 2 ^ L := by
      calc Valid.card
          ≤ Fintype.card GoodPair := Finset.card_le_univ Valid
        _ = (2 ^ m) ^ k * 2 ^ m := by simp [GoodPair, X, K, I]
        _ = 2 ^ L := by rw [← pow_mul, ← pow_add]; congr 1; simp [L]; ring
    have hmiss_card : ∀ p ∈ Valid,
        ((Finset.univ : Finset X).filter (fun v => ¬ hit p v)).card ≤ 2 ^ (m - k - 1) * (M - 1) := by
      intro p hp
      simp only [Valid, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨v0, hv0_orth, hv0_dot⟩
      let U : Submodule K X := Submodule.span K (Set.range p.1)
      let W0 : Submodule K X := orth U
      let W1 : Submodule K X := W0 ⊓ orth (Submodule.span K {p.2})
      have hadd_W1 : ∀ v : X, hit p v → v + v0 ∈ W1 := by
        intro v hv
        refine ⟨?_, ?_⟩
        · intro u hu
          refine Submodule.span_induction (p := fun w _ => dotProduct (v + v0) w = 0) ?_ ?_ ?_ ?_ hu
          · rintro _ ⟨j, rfl⟩; rw [add_dotProduct, hv.1 j, hv0_orth j, zero_add]
          · simp [dotProduct]
          · intro w1 w2 _ _ h1 h2; rw [dotProduct_add, h1, h2, zero_add]
          · intro c w _ hw; rw [dotProduct_smul, hw, smul_zero]
        · intro u hu
          refine Submodule.span_induction (p := fun w _ => dotProduct (v + v0) w = 0) ?_ ?_ ?_ ?_ hu
          · rintro _ rfl
            rw [add_dotProduct, hv.2, hv0_dot]
            decide
          · simp [dotProduct]
          · intro w1 w2 _ _ h1 h2; rw [dotProduct_add, h1, h2, zero_add]
          · intro c w _ hw; rw [dotProduct_smul, hw, smul_zero]
      have hhit_eq : (Finset.univ.filter (fun v : X => hit p v)).card = Fintype.card W1 := by
        rw [← Finset.card_univ]
        refine Finset.card_bij
          (fun v hv => (⟨v + v0, hadd_W1 v (Finset.mem_filter.mp hv).2⟩ : W1)) ?_ ?_ ?_
        · intro _ _
          exact Finset.mem_univ _
        · intro v1 _ v2 _ h
          have hval : v1 + v0 = v2 + v0 := congr_arg Subtype.val h
          exact add_right_cancel hval
        · intro w _
          refine ⟨w.1 + v0, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hit]
            refine ⟨fun j => ?_, ?_⟩
            · rw [add_dotProduct, w.2.1 (p.1 j) (Submodule.subset_span ⟨j, rfl⟩), hv0_orth j, zero_add]
            · rw [add_dotProduct, w.2.2 p.2 (Submodule.subset_span (Set.mem_singleton p.2)), hv0_dot, zero_add]
          · apply Subtype.ext
            funext i
            change (w.1 i + v0 i) + v0 i = w.1 i
            have : v0 i + v0 i = 0 := by generalize v0 i = x; revert x; decide
            rw [add_assoc, this, add_zero]
      have hU_dim : Module.finrank K U ≤ k := by
        have h1 := finrank_span_le_card (R := K) (Set.range p.1)
        have hsub : (Set.range p.1).toFinset ⊆ Finset.univ.image p.1 := by
          intro x hx; simp at hx ⊢; exact hx
        exact h1.trans ((Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp)))
      have hW1_dim : m - k - 1 ≤ Module.finrank K W1 := by
        have hW0_dim : m - k ≤ Module.finrank K W0 := by
          have := finrank_orth_add U
          change Module.finrank K W0 + Module.finrank K U = m at this
          omega
        let φ : W0 →ₗ[K] K :=
          { toFun := fun w => dotProduct w.1 p.2
            map_add' := fun w1 w2 => add_dotProduct w1.1 w2.1 p.2
            map_smul' := fun c w => smul_dotProduct c w.1 p.2 }
        have hker : Module.finrank K (LinearMap.ker φ) = Module.finrank K W1 := by
          let e : LinearMap.ker φ ≃ₗ[K] W1 :=
            { toFun := fun w => ⟨w.1.1, w.1.2, fun u hu => by
                refine Submodule.span_induction (p := fun z _ => dotProduct w.1.1 z = 0) ?_ ?_ ?_ ?_ hu
                · rintro _ rfl; exact w.2
                · simp [dotProduct]
                · intro z1 z2 _ _ h1 h2; rw [dotProduct_add, h1, h2, zero_add]
                · intro c z _ hz; rw [dotProduct_smul, hz, smul_zero]⟩
              invFun := fun w => ⟨⟨w.1, w.2.1⟩, w.2.2 p.2 (Submodule.subset_span (Set.mem_singleton p.2))⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          exact e.finrank_eq
        have hrn := LinearMap.finrank_range_add_finrank_ker φ
        have hrg : Module.finrank K (LinearMap.range φ) ≤ 1 := by
          calc Module.finrank K (LinearMap.range φ)
              ≤ Module.finrank K K := Submodule.finrank_le _
            _ = 1 := Module.finrank_self K
        omega
      have hhit_lb : 2 ^ (m - k - 1) ≤ (Finset.univ.filter (fun v : X => hit p v)).card := by
        rw [hhit_eq]
        have hnc := Module.natCard_eq_pow_finrank (K := K) (V := W1)
        rw [Nat.card_eq_fintype_card, Nat.card_zmod] at hnc
        rw [hnc]
        exact Nat.pow_le_pow_right (by omega) hW1_dim
      have hcomp : (Finset.univ.filter (fun v : X => hit p v)).card +
          (Finset.univ.filter (fun v : X => ¬ hit p v)).card = 2 ^ m := by
        rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
        calc ∑ v : X, ((if hit p v then 1 else 0) + (if ¬ hit p v then 1 else 0))
            = ∑ _v : X, 1 := Finset.sum_congr rfl fun v _ => by by_cases h : hit p v <;> simp [h]
          _ = Fintype.card X := by simp
          _ = 2 ^ m := by simp [X, K, I]
      have h2m : 2 ^ (m - k - 1) * M = 2 ^ m := by
        simp only [M, ← pow_add]
        congr 1
        omega
      have hmul : 2 ^ (m - k - 1) * (M - 1) + 2 ^ (m - k - 1) = 2 ^ m := by
        rw [← h2m]
        have : M = (M - 1) + 1 := by omega
        conv_rhs => rw [this]
        ring
      omega
    let BadTuples : Finset (Fin N → X) :=
      Valid.biUnion (fun p =>
        (Finset.univ : Finset (Fin N → X)).filter (fun f => ∀ t : Fin N, ¬ hit p (f t)))
    have hBad_lt : BadTuples.card < (Finset.univ : Finset (Fin N → X)).card := by
      have hcard_univ : (Finset.univ : Finset (Fin N → X)).card = (2 ^ (m - k - 1) * M) ^ N := by
        have h2m : 2 ^ (m - k - 1) * M = 2 ^ m := by
          simp only [M, ← pow_add]
          congr 1
          omega
        have hcardX : Fintype.card X = 2 ^ m := by simp [X, K, I]
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, hcardX, h2m]
      have hBad_le : BadTuples.card ≤ Valid.card * (2 ^ (m - k - 1) * (M - 1)) ^ N := by
        calc BadTuples.card
            ≤ ∑ p ∈ Valid, ((Finset.univ : Finset (Fin N → X)).filter
                (fun f => ∀ t : Fin N, ¬ hit p (f t))).card := Finset.card_biUnion_le
          _ = ∑ p ∈ Valid, ((Finset.univ : Finset X).filter (fun v => ¬ hit p v)).card ^ N := by
                refine Finset.sum_congr rfl fun p _ => ?_
                have heq : (Finset.univ : Finset (Fin N → X)).filter (fun f => ∀ t : Fin N, ¬ hit p (f t)) =
                    Fintype.piFinset (fun _ : Fin N => (Finset.univ : Finset X).filter (fun v => ¬ hit p v)) := by
                  ext f; simp [Fintype.mem_piFinset]
                rw [heq, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ ∑ _p ∈ Valid, (2 ^ (m - k - 1) * (M - 1)) ^ N :=
                Finset.sum_le_sum fun p hp => Nat.pow_le_pow_left (hmiss_card p hp) N
          _ = Valid.card * (2 ^ (m - k - 1) * (M - 1)) ^ N := by
                rw [Finset.sum_const, smul_eq_mul]
      rw [hcard_univ, mul_pow]
      calc BadTuples.card
          ≤ Valid.card * (2 ^ (m - k - 1) * (M - 1)) ^ N := hBad_le
        _ ≤ 2 ^ L * (2 ^ (m - k - 1) * (M - 1)) ^ N := Nat.mul_le_mul_right _ hValid_card
        _ = (2 ^ (m - k - 1)) ^ N * ((M - 1) ^ N * 2 ^ L) := by rw [mul_pow]; ring
        _ < (2 ^ (m - k - 1)) ^ N * M ^ N :=
              Nat.mul_lt_mul_of_pos_left hpow_strict (Nat.pow_pos (Nat.pow_pos (by omega)))
    have hex_good : ∃ f : Fin N → X, f ∉ BadTuples := by
      have hne : ((Finset.univ : Finset (Fin N → X)) \ BadTuples).Nonempty := by
        apply Finset.card_pos.mp
        rw [Finset.card_sdiff, Finset.inter_univ]
        omega
      rcases hne with ⟨f, hf⟩
      exact ⟨f, (Finset.mem_sdiff.mp hf).2⟩
    rcases hex_good with ⟨f, hf⟩
    let H : Finset (Finset I) := (Finset.univ : Finset (Fin N)).image (fun t => supp (f t))
    refine ⟨H, ?_, ?_⟩
    · intro a b
      constructor
      · rintro ⟨u, hu⟩ S _ hSb
        simp only [dot, hu]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro j _
        rw [← Finset.mul_sum]
        have hj : ∑ i ∈ S, b j i = 0 := hSb j
        rw [hj, mul_zero]
      · intro hdot
        by_contra hno
        let U := Submodule.span K (Set.range b)
        have ha_notU : a ∉ U := by
          intro haU
          rcases (Submodule.mem_span_range_iff_exists_fun K).mp haU with ⟨u, hu⟩
          apply hno
          refine ⟨u, fun i => ?_⟩
          have hi := congr_fun hu.symm i
          rw [Finset.sum_apply] at hi
          exact hi
        rw [← orth_orth U] at ha_notU
        have hex_v : ∃ v : X, hit (b, a) v := by
          by_contra hnv
          push Not at hnv
          apply ha_notU
          intro v hv
          have hvj : ∀ j : Fin k, dotProduct v (b j) = 0 :=
            fun j => hv (b j) (Submodule.subset_span ⟨j, rfl⟩)
          have hne1 : dotProduct v a ≠ 1 := fun h1 => hnv v ⟨hvj, h1⟩
          rw [dotProduct_comm]
          by_contra hne0
          exact hne1 ((zmod2_ne_zero_iff _).mp hne0)
        have hval : (b, a) ∈ Valid := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hex_v⟩
        have hnot_bad : ¬ ∀ t : Fin N, ¬ hit (b, a) (f t) := by
          intro hall
          apply hf
          exact Finset.mem_biUnion.mpr ⟨(b, a), hval, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩⟩
        push Not at hnot_bad
        rcases hnot_bad with ⟨t0, ht0_orth, ht0_dot⟩
        have hS_mem : supp (f t0) ∈ H := Finset.mem_image.mpr ⟨t0, Finset.mem_univ _, rfl⟩
        have hS_b : ∀ j : Fin k, dot (supp (f t0)) (b j) = 0 := by
          intro j
          change ∑ i ∈ supp (f t0), b j i = 0
          rw [dot_eq_dotProduct, mask_supp]
          exact ht0_orth j
        have hS_a : ∑ i ∈ supp (f t0), a i = 0 := hdot (supp (f t0)) hS_mem hS_b
        rw [dot_eq_dotProduct, mask_supp, ht0_dot] at hS_a
        exact one_ne_zero hS_a
    · calc H.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_image_le
        _ = N := by simp

end Donor454

theorem detect454 :
  ∀ m k : ℕ, k < m →
  let K := ZMod 2
  let I := Fin m
  let X := I → K
  let mask := fun (S : Finset I) (i : I) => if i ∈ S then (1 : K) else 0
  let dot := fun (S : Finset I) (a : X) => ∑ i ∈ S, a i
  let works := fun (H : Finset (Finset I)) =>
    ∀ (a : X) (b : Fin k → X),
      (∃ u : Fin k → K, ∀ i, a i = ∑ j, u j * b j i) ↔
      ∀ S ∈ H, (∀ j, dot S (b j) = 0) → dot S a = 0
  (∀ H : Finset (Finset I), works H ↔
    ∀ W : Submodule K X, Module.finrank K W = m-k →
      Submodule.span K {x : X | ∃ S ∈ H, x = mask S ∧ x ∈ W} = W) ∧
  (∀ H : Finset (Finset I), works H →
    (m-k)*(2^m-1) ≤ H.card*(2^(m-k)-1) ∧
    ∀ w : ℕ, (∀ S ∈ H, S.card ≤ w) → m.choose (k+1) ≤ H.card * w.choose (k+1)) ∧
  works (Finset.univ.filter (fun S : Finset I => S.card ≤ k+1)) ∧
  ∃ H : Finset (Finset I), works H ∧ H.card ≤ 2^(k+1)*((k+1)*m+1) := by
  intro m k hkm
  exact Donor454.main_proof m k hkm


namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
def detects {m k : ℕ} (H : Finset (Mask m)) :=
  ∀ x : V m k → K, (∃ u : Fin k → K, ∀ i, x (i,none) = ∑ j, u j * x (i,some j)) ↔
    ∀ R∈H, eval x (test R)=0

theorem evalTest {m k : ℕ} (R : Mask m) (x : V m k → K) :
    eval x (test R)=0 ↔ (∀ j : Fin k, ∑ i∈R, x (i,some j)=0) → ∑ i∈R, x (i,none)=0 := by
  classical
  have f2 (c : K) : c=0 ∨ c=1 := by revert c; decide
  have expr : eval x (test R) = (∑ i∈R, x (i,none)) * ∏ j : Fin k, (1+∑ i∈R, x (i,some j)) := by
    simp [test,part]
  rw [expr]
  by_cases zero : ∀ j : Fin k, ∑ i∈R, x (i,some j)=0
  · simp [zero]
  · obtain ⟨j,hj⟩ := not_forall.mp zero
    have val := (f2 _).resolve_left hj
    have prodzero : (∏ j : Fin k, (1+∑ i∈R, x (i,some j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [val]; decide
    simp [prodzero,zero]

theorem semanticPools : ∀ k : ℕ, ∃ C m₀ : ℕ, ∀ m≥m₀,
    detects (k:=k) (short m k) ∧ ∃ H : Finset (Mask m), H.card≤C*m ∧ detects (k:=k) H := by
  intro k
  refine ⟨2^(k+1)*(k+2),k+1,?_⟩
  intro m hm
  have both := detect454 m k (by omega)
  obtain ⟨sh,H,hworks,sz⟩ := both.2.2
  have convert (G : Finset (Mask m)) (h : ∀ (a : Fin m → K) (b : Fin k → Fin m → K),
      (∃ u : Fin k → K, ∀ i, a i=∑ j,u j*b j i) ↔
      ∀ R∈G, (∀ j, ∑ i∈R,b j i=0) → ∑ i∈R,a i=0) : detects (k:=k) G := by
    intro x
    simpa only [evalTest] using h (fun i => x (i,none)) (fun j i => x (i,some j))
  refine ⟨convert _ sh,H,?_,convert _ hworks⟩
  apply sz.trans
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  nlinarith

end Pool468
namespace Pool468
open MvPolynomial PEqualNP.ProofComplexity
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
        rw [← mul_assoc, X, monomial_mul_monomial, one_mul,
          ← Finsupp.single_add, add_comm 1 n]
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

theorem degPart {m k : ℕ} (S : Mask m) (j : Option (Fin k)) : (part S j).totalDegree≤1 :=
  (totalDegree_finsetSum _ _).trans (Finset.sup_le (fun i _ => by simp))
theorem twice {V : Type} (a : MvPolynomial V K) : a+a=0 := by
  rw [← two_smul (ZMod 2) a,show (2 : ZMod 2) = 0 from rfl,zero_smul]
theorem shortRef {m k : ℕ} (H : Finset (Mask m)) (S : Mask m) (own : S∈H) :
    PCRefutable (sys (k:=k) H S) (k+1) := by
  classical
  let F := sys (k:=k) H S
  let A : P m k := part S none
  let B (i : Fin k) : P m k := part S (some i)
  let Q (T : Finset (Fin k)) : P m k := A * ∏ j∈T, (1+B j)
  have degQ (T : Finset (Fin k)) : (Q T).totalDegree≤1+T.card := by
    apply (totalDegree_mul _ _).trans
    apply Nat.add_le_add (degPart S none)
    calc
      _ ≤ ∑ j∈T, (1+B j).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ _j∈T, 1 := Finset.sum_le_sum (fun j _ => (totalDegree_add _ _).trans
        (max_le (by simp) (degPart S (some j))))
      _ = _ := by simp
  have diff (T : Finset (Fin k)) : PCDerivable F (k+1) (Q T + A) := by
    induction T using Finset.induction_on with
    | empty => simpa [Q,twice] using (PCDerivable.zero : PCDerivable F (k+1) 0)
    | insert j T hj ih =>
      have hb : B j ∈ F := Or.inr (Or.inr ⟨j,rfl⟩)
      have small := Finset.card_le_univ (insert j T)
      rw [Finset.card_insert_of_notMem hj,Fintype.card_fin] at small
      have hprod := pcDerivable_mul_left (PCDerivable.ax hb (B := k+1) ((degPart S (some j)).trans (by omega))) (Q T)
      have cap : (Q T).totalDegree+(B j).totalDegree≤k+1 := by
        have := degQ T; have := degPart S (some j); change (B j).totalDegree ≤ 1 at this; omega
      rw [max_eq_left cap] at hprod
      have eq : Q (insert j T)+A = Q T*B j+(Q T+A) := by
        dsimp [Q]; rw [Finset.prod_insert hj]; ring
      rw [eq]
      exact .add hprod ih
  have htest : Q Finset.univ ∈ F := Or.inl (Or.inr ⟨S,own,rfl⟩)
  have hd : (Q Finset.univ).totalDegree≤k+1 := by simpa [Nat.add_comm] using degQ Finset.univ
  have a := PCDerivable.add (PCDerivable.ax htest hd) (diff Finset.univ)
  rw [← add_assoc,twice,zero_add] at a
  have hp : 1+A∈F := Or.inr (Or.inl rfl)
  have dp : (1+A).totalDegree≤k+1 := (totalDegree_add _ _).trans
    (max_le (by simp) ((degPart S none).trans (by omega)))
  have final := PCDerivable.add (PCDerivable.ax hp dp) a
  rwa [add_assoc,twice,add_zero] at final

end Pool468

namespace Donor453
theorem z2 (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c; decide

theorem lin_fwd (k m : ℕ) (α : Fin m → ZMod 2) (β : Fin m → Fin k → ZMod 2)
    (u : Fin k → ZMod 2) (hu : ∀ i, α i = ∑ j, u j * β i j) (S : Finset (Fin m)) :
    (∑ i ∈ S, α i) * ∏ j, (1 + ∑ i ∈ S, β i j) = 0 := by
  by_cases hz : ∀ j, ∑ i ∈ S, β i j = 0
  · have : ∑ i ∈ S, α i = 0 := by
      calc ∑ i ∈ S, α i = ∑ i ∈ S, ∑ j, u j * β i j := Finset.sum_congr rfl (fun i _ => hu i)
        _ = ∑ j, ∑ i ∈ S, u j * β i j := Finset.sum_comm
        _ = ∑ j, u j * ∑ i ∈ S, β i j := by simp only [Finset.mul_sum]
        _ = 0 := by simp [hz]
    rw [this, zero_mul]
  · obtain ⟨j, hj⟩ := not_forall.1 hz
    have h1 : ∑ i ∈ S, β i j = 1 := (z2 _).resolve_left hj
    have : ∏ j, (1 + ∑ i ∈ S, β i j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [h1]; decide
    rw [this, mul_zero]

end Donor453
namespace Fibers468
open scoped BigOperators
abbrev K := ZMod 2
abbrev Vec (n : ℕ) := Fin n → K
abbrev Mat (a b : ℕ) := Fin a × Fin b → K
def outer {a b : ℕ} (u : Vec a) (v : Vec b) : Mat a b := fun xy => u xy.1 * v xy.2
def outerMap {a b : ℕ} (u : Vec a) : Vec b →ₗ[K] Mat a b where
  toFun := outer u
  map_add' f g := by funext xy; exact mul_add .. 
  map_smul' t f := by funext xy; change u xy.1*(t*f xy.2)=t*(u xy.1*f xy.2); ring
def fiber {a b : ℕ} (L : Submodule K (Mat a b)) (u : Vec a) : Submodule K (Vec b) :=
  L.comap (outerMap u)
theorem cardK (X : Type*) [AddCommGroup X] [Module K X] [Finite X] [Fintype X] :
    Fintype.card X=2^(Module.finrank K X) := by
  have h := Module.natCard_eq_pow_finrank (K:=K) (V:=X)
  simpa [Nat.card_eq_fintype_card,K] using h

theorem fibers_budget {a b : ℕ} (L : Submodule K (Mat a b)) {ι : Type} [Fintype ι]
    (u : ι → Vec a) (li : LinearIndependent K u) :
    (∑ i, Module.finrank K (fiber L (u i))) ≤ Module.finrank K L := by
  classical
  let pack (f : (i : ι) → fiber L (u i)) : L :=
    ⟨∑ i, outer (u i) (f i).val, L.sum_mem (fun i _ => (f i).property)⟩
  have inject : Function.Injective pack := by
    intro f g eq
    have eqs : (∑ i, outer (u i) (f i).val) = ∑ i, outer (u i) (g i).val := congrArg Subtype.val eq
    funext i
    apply Subtype.ext
    funext y
    have id (x : Fin a) : (∑ i, u i x * (f i).val y) = ∑ i, u i x * (g i).val y := by
      simpa only [Finset.sum_apply,outer] using congrFun eqs (x,y)
    have zero : ∑ i, ((f i).val y-(g i).val y) • u i=0 := by
      funext x
      change (∑ i, ((f i).val y-(g i).val y) • u i) x=0
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,sub_mul,Finset.sum_sub_distrib]
      simpa only [mul_comm,sub_eq_zero] using id x
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp li _ zero i)
  have h := Fintype.card_le_of_injective pack inject
  rw [Fintype.card_pi,cardK L] at h
  simp_rw [cardK (fiber L _)] at h
  rw [Finset.prod_pow_eq_pow_sum] at h
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp h

theorem heavy_count {a b d r : ℕ} (L : Submodule K (Mat a b))
    (bound : Module.finrank K L < (r+1)*(d+1)) :
    (Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))).card ≤ 2^r := by
  classical
  let heavy : Set (Vec a) := {u | d < Module.finrank K (fiber L u)}
  obtain ⟨B,sub,span,ind⟩ := exists_linearIndependent K heavy
  have h := fibers_budget L (fun i : B => i.val) ind
  have sumBound : Fintype.card B * (d+1) ≤ ∑ i : B, Module.finrank K (fiber L i.val) := by
    calc
      _ = ∑ _i : B, (d+1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => sub i.property)
  have br : Fintype.card B ≤ r := by
    by_contra! bad
    have sc : (r+1)*(d+1) ≤ Fintype.card B*(d+1) := Nat.mul_le_mul_right (d+1) bad
    omega
  have sr : Module.finrank K (Submodule.span K heavy) ≤ r := by
    have eq := finrank_span_set_eq_card (R:=K) ind
    rw [span] at eq
    simpa [eq] using br
  let X := Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))
  let emb (x : X) : Submodule.span K heavy := ⟨x.val,Submodule.subset_span (Finset.mem_filter.mp x.property).2⟩
  have inject : Function.Injective emb := fun x y h => Subtype.ext (congrArg (fun z : Submodule.span K heavy => z.val) h)
  calc
    X.card = Fintype.card X := (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Submodule.span K heavy) := Fintype.card_le_of_injective emb inject
    _ ≤ 2^r := by rw [cardK]; exact Nat.pow_le_pow_right (by decide) sr

end Fibers468
namespace Fibers468
open scoped BigOperators
open Classical in
theorem matrixBound {a b d r : ℕ} (L : Submodule K (Mat a b))
    (bound : Module.finrank K L < (r+1)*(d+1)) :
    (Finset.univ.filter (fun z : Vec a × Vec b => outer z.1 z.2 ∈ L)).card ≤
      2^(a+d)+2^(r+b) := by
  classical
  let heavy := Finset.univ.filter (fun u : Vec a => d < Module.finrank K (fiber L u))
  let count (u : Vec a) := (Finset.univ.filter (fun v : Vec b => outer u v∈L)).card
  have cnt (u : Vec a) : count u = 2^Module.finrank K (fiber L u) := by
    change (Finset.univ.filter (fun v : Vec b => outer u v∈L)).card = _
    rw [← Fintype.card_subtype]
    exact cardK (fiber L u)
  have cb (u : Vec a) : count u ≤ (if u∈heavy then 2^b else 0) + 2^d := by
    split_ifs with h
    · have ub : count u ≤ Fintype.card (Vec b) := Finset.card_le_univ _
      have ub2 : count u ≤ 2^b := by simpa [Vec,K] using ub
      exact Nat.le_trans ub2 (Nat.le_add_right _ _)
    · have small : Module.finrank K (fiber L u) ≤ d := by
        by_contra! bad
        exact h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,bad⟩)
      rw [cnt,zero_add]
      exact Nat.pow_le_pow_right (by decide) small
  have splitCount : (Finset.univ.filter (fun z : Vec a × Vec b => outer z.1 z.2∈L)).card = ∑ u, count u := by
    simp only [count,Finset.card_filter,Fintype.sum_prod_type]
  rw [splitCount]
  calc
    _ ≤ ∑ u : Vec a, ((if u∈heavy then 2^b else 0) + 2^d) := Finset.sum_le_sum (fun i _ => cb i)
    _ = heavy.card * 2^b + 2^a * 2^d := by
      rw [Finset.sum_add_distrib,←Finset.sum_filter]
      simp [Vec,K]
    _ ≤ 2^r*2^b + 2^a * 2^d := Nat.add_le_add_right (Nat.mul_le_mul_right _ (heavy_count L bound)) _
    _ = _ := by rw [←pow_add,←pow_add,add_comm]
end Fibers468

namespace Uniform468
open scoped BigOperators
open Classical in
theorem pull_count {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [Fintype X] [Fintype Y]
    (f : X →+ Y) (onto : Function.Surjective f) (B : Finset Y) (A : Finset X)
    (ha : ∀ x, x∈A ↔ f x∈B) :
    A.card * Fintype.card Y = B.card * Fintype.card X := by
  classical
  choose sec hs using onto
  let e : (A × Y) ≃ (B × X) := {
    toFun := fun ⟨a,y⟩ => (⟨f a.val,(ha a.val).mp a.property⟩,a.val+sec y-sec (f a.val))
    invFun := fun ⟨y,x⟩ => (⟨x+sec y.val-sec (f x),(ha _).mpr (by simp [hs,y.property])⟩,f x)
    left_inv := by
      intro z; obtain ⟨a,y⟩ := z
      apply Prod.ext
      · apply Subtype.ext; dsimp; simp [hs] <;> abel
      · dsimp; simp [hs]
    right_inv := by
      intro z; obtain ⟨y,x⟩ := z
      apply Prod.ext
      · apply Subtype.ext; dsimp; simp [hs]
      · dsimp; simp [hs] <;> abel
  }
  simpa only [Fintype.card_prod,Fintype.card_coe] using Fintype.card_congr e
end Uniform468
namespace Blocks468
open Fibers468
abbrev Idx (B n : ℕ) := Fin B × (Fin n ⊕ Fin n)
def restrictMap {B n m : ℕ} (e : Idx B n ↪ Fin m) (j : Fin B) : Vec m →+ (Vec n × Vec n) where
  toFun x := (fun i => x (e (j,.inl i)),fun i => x (e (j,.inr i)))
  map_zero' := rfl
  map_add' _ _ := rfl
theorem restrict_onto {B n m : ℕ} (e : Idx B n ↪ Fin m) (j : Fin B) :
    Function.Surjective (restrictMap e j) := by
  classical
  intro z
  let emb := fun i : Fin n ⊕ Fin n => e (j,i)
  have inj : Function.Injective emb := fun _ _ h => congrArg Prod.snd (e.injective h)
  let both := Sum.elim z.1 z.2
  let x : Vec m := Function.extend emb both (fun _ => 0)
  refine ⟨x,Prod.ext ?_ ?_⟩
  · funext i; exact inj.extend_apply both (fun _ => (0 : Fibers468.K)) (Sum.inl i)
  · funext i; exact inj.extend_apply both (fun _ => (0 : Fibers468.K)) (Sum.inr i)
def feature {B n m : ℕ} (e : Idx B n ↪ Fin m) (j : Fin B) (x : Vec m) : Mat n n :=
  outer ((restrictMap e j x).1) ((restrictMap e j x).2)
def admissible {B n m : ℕ} (e : Idx B n ↪ Fin m) (H : Finset (Vec m)) :=
  ∀ j, LinearIndepOn K (feature e j) (H : Set (Vec m))
theorem avoid {B t m D : ℕ} (bp : 0<B) (dp : 0<D) (num : 2*B*D ≤ 2^t)
    (e : Idx B (2*t) ↪ Fin m) (H : Finset (Vec m))
    (small : H.card < (t+1)*(t+1)) (old : admissible e H) :
    ∃ bad : Finset (Vec m), bad.card*D ≤ Fintype.card (Vec m) ∧
      ∀ v, v∉bad → admissible e (insert v H) := by
  classical
  let L (j : Fin B) := Submodule.span K ((feature e j) '' (H : Set (Vec m)))
  have dim (j : Fin B) : Module.finrank K (L j) < (t+1)*(t+1) := by
    apply lt_of_le_of_lt (finrank_span_le_card ..) ?_
    have sub : ((feature e j) '' (H : Set (Vec m))).toFinset ⊆ H.image (feature e j) := by
      intro x hx; simpa using hx
    exact ((Finset.card_le_card sub).trans Finset.card_image_le).trans_lt small
  let R (j : Fin B) := Finset.univ.filter (fun w : Vec (2*t) × Vec (2*t) => outer w.1 w.2 ∈ L j)
  let badAt (j : Fin B) := Finset.univ.filter (fun x : Vec m => restrictMap e j x ∈ R j)
  let Bad := Finset.univ.biUnion badAt
  refine ⟨Bad,?_,?_⟩
  · have per (j : Fin B) : (badAt j).card*(B*D) ≤ Fintype.card (Vec m) := by
      have pull := Uniform468.pull_count (restrictMap e j) (restrict_onto e j) (R j) (badAt j) (by
        intro w; simp [badAt])
      have cap := matrixBound (L j) (dim j)
      change (R j).card ≤ 2^(2*t+t)+2^(t+2*t) at cap
      have num' : (R j).card*(B*D) ≤ Fintype.card (Vec (2*t) × Vec (2*t)) := by
        simp only [Vec,Fintype.card_prod,Fintype.card_fun,ZMod.card,Fintype.card_fin,←pow_add]
        rw [show 2*t+2*t=(2*t+t)+t by omega,pow_add]
        have s := Nat.mul_le_mul_left (2^(2*t+t)) num
        rw [Nat.add_comm t (2*t)] at cap
        nlinarith only [Nat.mul_le_mul_right (B*D) cap,s]
      have positive : 0<Fintype.card (Vec (2*t) × Vec (2*t)) := Fintype.card_pos
      apply Nat.le_of_mul_le_mul_right (show _ * Fintype.card (Vec (2*t) × Vec (2*t)) ≤ _ * Fintype.card (Vec (2*t) × Vec (2*t)) from ?_) positive
      calc
        _ = ((badAt j).card*Fintype.card (Vec (2*t) × Vec (2*t)))*(B*D) := by ring
        _ = ((R j).card*(B*D))*Fintype.card (Vec m) := by rw [pull]; ring
        _ ≤ _ := by simpa only [mul_comm] using Nat.mul_le_mul_right (Fintype.card (Vec m)) num'
    have sc := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => per j)
    rw [←Finset.sum_mul] at sc
    have whole := Nat.mul_le_mul_right (B*D) (Finset.card_biUnion_le : Bad.card ≤ ∑ j, (badAt j).card)
    have bound : (Bad.card*D)*B ≤ Fintype.card (Vec m)*B := by
      calc
        _ = Bad.card*(B*D) := by ring
        _ ≤ _ := whole.trans (by simpa [mul_comm] using sc)
    exact Nat.le_of_mul_le_mul_right bound bp
  · intro v hv j
    have no : feature e j v ∉ L j := by
      intro h
      apply hv
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩⟩
    have vn : v∉H := fun h => no (Submodule.subset_span ⟨v,h,rfl⟩)
    rw [Finset.coe_insert]
    exact (linearIndepOn_insert (by simpa using vn)).2 ⟨old j,no⟩
theorem skipBlock {B n m : ℕ} (e : Idx B n ↪ Fin m) (S : Finset (Fin m)) (size : S.card<B) :
    ∃ j : Fin B, ∀ i, e (j,i) ∉ S := by
  classical
  by_contra! h
  choose i hi using h
  let f (j : Fin B) : S := ⟨e (j,i j),hi j⟩
  have inject : Function.Injective f := fun x y eq => congrArg Prod.fst (e.injective (congrArg Subtype.val eq))
  have bad := Fintype.card_le_of_injective f inject
  simp at bad
  omega
end Blocks468
namespace Greedy468
open scoped BigOperators
open Classical in
theorem find_row {A B : Type} [Fintype B] [Nonempty B]
    (U : Finset A) (hu : U.Nonempty) (G : Finset B) (hit : A → B → Prop)
    (d : ℕ) (mass : ∀ x∈U, Fintype.card B ≤ d * (G.filter (hit x)).card) :
    ∃ y∈G, U.card ≤ d * (U.filter (fun x => hit x y)).card := by
  classical
  let f (y : B) := if y∈G then (U.filter (fun x => hit x y)).card else 0
  have count : (∑ y : B, f y) = ∑ x∈U, (G.filter (hit x)).card := by
    simp only [f,← Finset.sum_filter]
    rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  obtain ⟨y,_,hy⟩ := Finset.exists_max_image (Finset.univ : Finset B) f Finset.univ_nonempty
  have db (x) (hx : x∈U) := mass x hx
  have lower := Finset.sum_le_sum db
  have upper := Finset.sum_le_sum (fun j hj => hy j hj)
  have bound : U.card * Fintype.card B ≤ (d * f y) * Fintype.card B := calc
    _ ≤ ∑ x∈U, d*(G.filter (hit x)).card := by simpa using lower
    _ = d * ∑ t : B, f t := by rw [←Finset.mul_sum,count]
    _ ≤ d * (Fintype.card B * f y) := Nat.mul_le_mul_left d (by simpa using upper)
    _ = _ := by ring
  have gain := Nat.le_of_mul_le_mul_right bound Fintype.card_pos
  by_cases ok : y∈G
  · exact ⟨y,ok,by simpa [f,ok] using gain⟩
  · have z : f y=0 := by simp [f,ok]
    rw [z,Nat.mul_zero] at gain
    exact (Nat.not_lt_of_ge gain (Finset.card_pos.mpr hu)).elim

open Classical in
theorem greedy {A B : Type} [Fintype B] [Nonempty B] [DecidableEq B] (U : Finset A)
    (hit : A → B → Prop) (ok : Finset B → Prop) (start : ok ∅)
    (D N : ℕ) (dpos : 1≤D)
    (extend : ∀ H : Finset B, H.card<N → ok H → ∃ G : Finset B,
      (∀ y∈G, ok (insert y H)) ∧
      ∀ x∈U, Fintype.card B ≤ D * (G.filter (hit x)).card)
    (enough : U.card * (D-1)^N < D^N) :
    ∃ H : Finset B, H.card≤N ∧ ok H ∧ ∀ x∈U, ∃ y∈H, hit x y := by
  classical
  let miss (H : Finset B) := U.filter (fun x => ∀ y∈H, ¬hit x y)
  have iter (t : ℕ) (ht : t≤N) : ∃ H : Finset B, H.card≤t ∧ ok H ∧
        (miss H).card*D^t ≤ U.card*(D-1)^t := by
    induction t with
    | zero => exact ⟨∅,by simp,start,by simp [miss]⟩
    | succ t ih =>
      obtain ⟨H,sz,oh,bound⟩ := ih (by omega)
      by_cases nz : (miss H).Nonempty
      · obtain ⟨G,extend,mass⟩ := extend H (by omega) oh
        obtain ⟨y,hy,gain⟩ := find_row (miss H) nz G hit D (fun x hx => mass x (Finset.mem_filter.mp hx).1)
        have split : (miss (insert y H)).card + ((miss H).filter (fun x => hit x y)).card = (miss H).card := by
          have eq : miss (insert y H) = (miss H).filter (fun x => ¬hit x y) := by
            ext x; simp [miss]; tauto
          rw [eq,add_comm]
          exact Finset.card_filter_add_card_filter_not ..
        have step : (miss (insert y H)).card * D ≤ (miss H).card*(D-1) := by
          have eq := congrArg (fun c : ℕ => c*D) split
          have pos : D-1+1=D := by omega
          have lift := congrArg (fun c : ℕ => (miss H).card*c) pos
          simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at eq lift
          nlinarith only [eq,lift,gain]
        refine ⟨insert y H,(Finset.card_insert_le ..).trans (by omega),extend y hy,?_⟩
        calc
          _ = ((miss (insert y H)).card*D)*D^t := by rw [pow_succ]; ring
          _ ≤ ((miss H).card*(D-1))*D^t := Nat.mul_le_mul_right _ step
          _ = ((miss H).card*D^t)*(D-1) := by ring
          _ ≤ (U.card*(D-1)^t)*(D-1) := Nat.mul_le_mul_right _ bound
          _ = _ := by rw [pow_succ]; ring
      · refine ⟨H,by omega,oh,?_⟩
        simp [Finset.not_nonempty_iff_eq_empty.mp nz]
  obtain ⟨H,sz,oh,bound⟩ := iter N le_rfl
  have empty : miss H=∅ := by
    by_contra h
    have pos : 1≤(miss H).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)
    have le := Nat.mul_le_mul_right (D^N) pos
    simp at le; omega
  refine ⟨H,sz,oh,?_⟩
  intro x hx
  by_contra! no
  have mem : x∈miss H := Finset.mem_filter.mpr ⟨hx,no⟩
  simpa [empty] using mem
end Greedy468
namespace Design468
open Fibers468 Pool468 MvPolynomial
abbrev X (m k : ℕ) := V m k → Pool468.K
def mark {m : ℕ} (v : Vec m) : Mask m := Finset.univ.filter (fun i => v i=1)
theorem markBit {m : ℕ} (v : Vec m) (i : Fin m) : bit (mark v) i=v i := by
  have val : ∀ c : Pool468.K, c=0 ∨ c=1 := by decide
  rcases val (v i) with h|h <;> simp [bit,mark,h]
def syndrome {m k : ℕ} (x : X m k) : Vec m →ₗ[Pool468.K] (Option (Fin k) → Pool468.K) where
  toFun v j := ∑ i, v i*x (i,j)
  map_add' v w := by ext j; simp [add_mul,Finset.sum_add_distrib]
  map_smul' c v := by ext j; simp [Finset.mul_sum,mul_assoc]
def desired (k : ℕ) : Option (Fin k) → Pool468.K := fun j => if j.isNone then 1 else 0
def rejects {m k : ℕ} (x : X m k) (v : Vec m) := syndrome x v=desired k
theorem syndrome_at {m k : ℕ} (x : X m k) (v : Vec m) (j : Option (Fin k)) :
    syndrome x v j = ∑ i∈mark v,x (i,j) := by
  change (∑ i,v i*x (i,j))=_
  rw [mark,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  have val : ∀ a : Pool468.K, a=0 ∨ a=1 := by decide
  rcases val (v i) with h|h <;> simp [h]
theorem reject_iff {m k : ℕ} (x : X m k) (v : Vec m) :
    rejects x v ↔ eval x (test (mark v)) ≠ 0 := by
  change rejects x v ↔ ¬ eval x (test (mark v)) = 0
  rw [evalTest]
  have val : ∀ a : Pool468.K, a=0 ∨ a=1 := by decide
  constructor
  · intro h outputs
    have one : ∑ i∈mark v,x (i,none)=1 := by
      rw [←syndrome_at]; exact congrFun h none
    have z (j : Fin k) : ∑ i∈mark v,x (i,some j)=0 := by
      rw [←syndrome_at]; exact congrFun h (some j)
    exact one_ne_zero (one.symm.trans (outputs z))
  · intro h
    have data (j : Fin k) : ∑ i∈mark v, x (i,some j)=0 := by
      by_contra hn
      exact h (fun all => (hn (all j)).elim)
    have resp : (∑ i∈mark v, x (i,none))≠0 := fun h0 => h (fun _ => h0)
    funext j
    cases j with
    | none =>
      change syndrome x v none=1
      rw [syndrome_at]; exact (val _).resolve_left resp
    | some j =>
      change syndrome x v (some j)=0
      rw [syndrome_at]; exact data j

open Classical in
theorem rejectMass {m k : ℕ} (x : X m k) (hit : ∃ v, rejects x v) :
    Fintype.card (Vec m) ≤ 2^(k+1)*(Finset.univ.filter (rejects x)).card := by
  classical
  let f := syndrome x
  obtain ⟨v,hv⟩ := hit
  let y : LinearMap.range f := ⟨desired k,v,hv⟩
  have onto : Function.Surjective f.rangeRestrict := by
    rintro ⟨v,w,hw⟩
    exact ⟨w,Subtype.ext hw⟩
  have h := Uniform468.pull_count f.rangeRestrict.toAddMonoidHom onto {y}
    (Finset.univ.filter (rejects x)) (by
      intro w
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro hw
        apply Subtype.ext
        exact hw
      · intro hw
        exact congrArg (fun z : LinearMap.range f => z.val) hw)
  rw [Finset.card_singleton,one_mul] at h
  have cap : Fintype.card (LinearMap.range f) ≤ 2^(k+1) := by
    have u := Fintype.card_le_of_injective (Subtype.val : LinearMap.range f → _) Subtype.val_injective
    simpa [Pool468.K] using u
  rw [← h]
  exact (Nat.mul_le_mul_left _ cap).trans_eq (Nat.mul_comm _ _)

private lemma bernoulli_nat (x y : ℕ) : ∀ t : ℕ, 0 < t →
    x ^ t + t * x ^ (t - 1) * y ≤ (x + y) ^ t := by
  intro t
  induction t with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    cases n with
    | zero => simp
    | succ m =>
      have hm := ih (Nat.succ_pos m)
      have hmul := Nat.mul_le_mul_right (x + y) hm
      rw [← pow_succ] at hmul
      calc x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y
          ≤ (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) := by
            have hexp : (x ^ (m + 1) + (m + 1) * x ^ m * y) * (x + y) =
                (x ^ (m + 2) + (m + 2) * x ^ (m + 1) * y) + (m + 1) * x ^ m * y ^ 2 := by ring
            omega
        _ ≤ (x + y) ^ (m + 2) := hmul


theorem enough (D L : ℕ) (hD : 2≤D) : 2^L*(D-1)^(D*(L+1)) < D^(D*(L+1)) := by
  have hstep : 2*(D-1)^D ≤ D^D := by
    have h1 := bernoulli_nat (D-1) 1 D (by omega)
    rw [Nat.sub_add_cancel (by omega),mul_one] at h1
    have h2 : (D-1)^D ≤ D*(D-1)^(D-1) := by
      have eq : (D-1)^D=(D-1)*(D-1)^(D-1) := by
        rw [mul_comm,← pow_succ,Nat.sub_add_cancel (by omega)]
      rw [eq]
      exact Nat.mul_le_mul_right _ (Nat.sub_le D 1)
    omega
  have power := Nat.pow_le_pow_left hstep (L+1)
  rw [mul_pow,←pow_mul,←pow_mul] at power
  exact (Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide : 1<2) (Nat.lt_succ_self L))
    (Nat.pow_pos (by omega : 0 < D-1))).trans_le power
end Design468
namespace Design468
open Fibers468 Pool468 Blocks468 MvPolynomial PEqualNP.ProofComplexity
theorem assemble (k : ℕ) (hk : 0<k) : ∃ C m₀ : ℕ, ∀ m≥m₀,
    ∃ H : Finset (Mask m), H.card≤C*m ∧ detects (k:=k) H ∧
      ∀ S∈short m k, S.Nonempty → PCRefutable (sys (k:=k) (short m k) S) (k+1) ∧
        ¬PCRefutable (sys (k:=k) H S) (k+1) := by
  classical
  let B := k+2
  let D := 2*2^(k+1)
  let C := D*(k+2)
  let big := 4*B*C + 2*B*D + k+2
  obtain ⟨_,oldm,donor⟩ := semanticPools k
  refine ⟨C,max oldm (4*B*big),?_⟩
  intro m hm
  have hOld := (donor m ((le_max_left ..).trans hm)).1
  have bigM : 4*B*big ≤ m := (le_max_right ..).trans hm
  have bp : 0<B := by dsimp [B]; omega
  have hD : 2≤D := by dsimp [D]; have := Nat.two_pow_pos (k+1); omega
  let t := m/(4*B)
  have lower : big ≤ t := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa [mul_comm] using bigM)
  have mul : 4*B*t≤m := by simpa only [t,Nat.mul_comm] using Nat.div_mul_le_self m (4*B)
  have upper : m < (t+1)*(4*B) := (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self t)
  have npos : 0<m := by
    have hb : 0<big := by dsimp [big]; omega
    have := Nat.mul_pos (by omega : 0<4*B) hb; omega
  let N := D*((k+1)*m+1)
  have budget : N≤C*m := by
    change D*((k+1)*m+1) ≤ (D*(k+2))*m
    rw [Nat.mul_assoc D (k+2) m]
    apply Nat.mul_le_mul_left
    nlinarith
  have sparse : N < (t+1)*(t+1) := by
    have coff : 4*B*C ≤ t := by dsimp [big] at lower; omega
    have rhs := Nat.mul_le_mul_left (t+1) coff
    have lhs := Nat.mul_le_mul_left C upper.le
    nlinarith only [budget,lhs,rhs]
  have num : 2*B*D ≤ 2^t := by
    have small : 2*B*D ≤ t := by dsimp [big] at lower; omega
    exact small.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have cardEmb : Fintype.card (Idx B (2*t)) ≤ Fintype.card (Fin m) := by
    simp only [Idx,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin]
    nlinarith only [mul]
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le cardEmb
  let U := Finset.univ.filter (fun x : X m k => ∃ v : Vec m, rejects x v)
  have nU : U.card ≤ 2^((k+1)*m) := by
    apply (Finset.card_le_univ U).trans
    simp [X,V,Pool468.K,mul_comm]
  have beginOK : admissible e (∅ : Finset (Vec m)) := by intro j; simp
  have extOK (H : Finset (Vec m)) (sz : H.card<N) (old : admissible e H) :
      ∃ G : Finset (Vec m), (∀ v∈G, admissible e (insert v H)) ∧
       ∀ x∈U, Fintype.card (Vec m) ≤ D * (G.filter (rejects x)).card := by
    obtain ⟨bad,bsize,good⟩ := avoid bp (by omega : 0<D) num e H (sz.trans sparse) old
    let G := Finset.univ \ bad
    refine ⟨G,fun v hv => good v (Finset.mem_sdiff.mp hv).2,?_⟩
    intro x hx
    let T := Finset.univ.filter (rejects x)
    let R := G.filter (rejects x)
    have hits : Fintype.card (Vec m) ≤ 2^(k+1)*T.card := rejectMass x (Finset.mem_filter.mp hx).2
    have inclusion : T ⊆ R ∪ bad := by
      intro i hi
      by_cases h : i∈bad
      exact Finset.mem_union_right _ h
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩,
        (Finset.mem_filter.mp hi).2⟩)
    have inc := Nat.mul_le_mul_left D ((Finset.card_le_card inclusion).trans (Finset.card_union_le _ _))
    change _ ≤ D*R.card
    dsimp [D] at inc bsize ⊢
    nlinarith only [hits,inc,bsize]
  have enough' := (Nat.mul_le_mul_right ((D-1)^N) nU).trans_lt (enough D ((k+1)*m) hD)
  obtain ⟨T,size,ok,hits⟩ := Greedy468.greedy U rejects (admissible e) beginOK D N (by omega) extOK enough'
  let H := T.image mark
  refine ⟨H,Finset.card_image_le.trans (size.trans budget),?_,?_⟩
  · intro x
    constructor
    · intro feas R hR
      have hitall := (Donor453.lin_fwd k m (fun i => x (i,none))
        (fun i j => x (i,some j)) feas.choose feas.choose_spec R)
      simpa [test,part] using hitall
    · intro tests
      apply (hOld x).mpr
      intro R hR
      by_contra off
      let v : Vec m := bit R
      have self : mark v=R := by ext i; simp [mark,v,bit]
      have member : x∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,(reject_iff x v).mpr (by rwa [self])⟩
      obtain ⟨w,hw,hxw⟩ := hits x member
      exact (reject_iff x w).mp hxw (tests _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
  · intro S hS sne
    refine ⟨shortRef (short m k) S hS,?_⟩
    have sc : S.card<B := by have q := (Finset.mem_filter.mp hS).2; dsimp [B]; omega
    obtain ⟨j,hj⟩ := skipBlock e S sc
    let a (z : Fin (2*t) × Fin (2*t)) := e (j,Sum.inl z.1)
    let b (z : Fin (2*t) × Fin (2*t)) := e (j,Sum.inr z.2)
    apply noRefBelow hk S sne H a b (fun z => hj _) (fun z => hj _)
    have pre (R : H) : ∃ w : T, mark w.val=R.val := by
      obtain ⟨w,hw,eq⟩ := Finset.mem_image.mp R.property
      exact ⟨⟨w,hw⟩,eq⟩
    choose back law using pre
    have inj : Function.Injective back := by
      intro R R' eq
      apply Subtype.ext
      rw [←law R,←law R',eq]
    have lin : LinearIndependent Pool468.K (fun R : H => feature e j (back R).val) :=
      (ok j).comp back inj
    convert lin using 1
    funext R z
    change bit R.val (a z)*bit R.val (b z) = (back R).val (a z)*(back R).val (b z)
    rw [←law R,markBit,markBit]
end Design468

end PEqualNP.Outside.L_pcx_468

theorem PEqualNP.Outside.L_pcx_468 : ∀ k : ℕ, 0 < k → ∃ C m₀ : ℕ, ∀ m ≥ m₀,
  let K := ZMod 2
  let I := Fin m
  let J := Fin k
  let V := I × Option J
  let P := MvPolynomial V K
  let Mask := Finset I
  let part := fun (S : Mask) (j : Option J) => ∑ i ∈ S, (MvPolynomial.X (i,j) : P)
  let test := fun S : Mask => part S none * ∏ j : J, (1 + part S (some j))
  let bools : Set P := Set.range (fun v : V => MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)
  let pin := fun S : Mask => ({1 + part S none} : Set P) ∪ Set.range (fun j : J => part S (some j))
  let sys := fun (H : Finset Mask) (S : Mask) => bools ∪ Set.image test (H : Set Mask) ∪ pin S
  let short := Finset.univ.filter (fun S : Mask => S.card ≤ k+1)
  ∃ H : Finset Mask, H.card ≤ C*m ∧
    (∀ x : V → K,
      (∃ u : J → K, ∀ i : I, x (i,none) = ∑ j, u j * x (i,some j)) ↔
      ∀ R ∈ H, MvPolynomial.eval x (test R) = 0) ∧
    ∀ S ∈ short, S.Nonempty →
      PEqualNP.ProofComplexity.PCRefutable (sys short S) (k+1) ∧
      ¬ PEqualNP.ProofComplexity.PCRefutable (sys H S) (k+1) := by
  exact PEqualNP.Outside.L_pcx_468.Design468.assemble
