import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace PEqualNP.Outside.L_lib_925_aux

theorem l925_stay_le {d : ℕ} (hd : 2 ≤ d) :
    0 < 1 / (1 + Real.sqrt ((2 : ℝ)^d - 1)) ∧
    1 / (1 + Real.sqrt ((2 : ℝ)^d - 1)) ≤ 3/8 := by
  have hp : (2 : ℝ)^2 ≤ 2^d := pow_le_pow_right₀ (by norm_num) hd
  have hs := Real.sq_sqrt (show 0 ≤ (2 : ℝ)^d - 1 by nlinarith)
  have hn := Real.sqrt_nonneg ((2 : ℝ)^d - 1)
  have hlow : (5 : ℝ)/3 ≤ Real.sqrt ((2 : ℝ)^d - 1) := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < 5/3 + Real.sqrt ((2 : ℝ)^d - 1) by positivity)]
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity)).2
    linarith

theorem l925_marked_rows {u : ℝ} (hu : 0 ≤ u) (hmax : u ≤ 3/8) :
    (2*u^2)*(3/4) + 2*u*(1-u) ≤ (1-u/4)*(3/4) ∧
    (2*u*(1-u))*(3/4) + (u^2+(1-u)^2) ≤ 1-u/4 := by
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hmax) (show 0 ≤ 4-u by linarith)]
  · nlinarith [mul_nonneg hu (show 0 ≤ 1/2-u by linarith)]

theorem l925_weighted_norm {a b c r x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (h₁ : 3*a+4*b ≤ 3*r) (h₂ : 3*b+4*c ≤ 4*r) :
    (a*x + b*y)^2 + (b*x + c*y)^2 ≤ r^2*(x^2+y^2) := by
  have p₁ : (a*x+b*y)^2 ≤ (3*a+4*b)*(a*x^2/3+b*y^2/4) := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (4*x-3*y))]
  have p₂ : (b*x+c*y)^2 ≤ (3*b+4*c)*(b*x^2/3+c*y^2/4) := by
    nlinarith [mul_nonneg (mul_nonneg hb hc) (sq_nonneg (4*x-3*y))]
  have q₁ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ a*x^2/3+b*y^2/4 by positivity)
  have q₂ := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ b*x^2/3+c*y^2/4 by positivity)
  have s₁ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ r*x^2/3 by positivity)
  have s₂ := mul_le_mul_of_nonneg_right h₂ (show 0 ≤ r*y^2/4 by positivity)
  linarith only [p₁,p₂,q₁,q₂,s₁,s₂]


theorem l925_marked_contraction {u x y : ℝ}
    (hu : 0 ≤ u) (hmax : u ≤ 3/8) :
    ((2*u^2)*x + 2*u*(1-u)*y)^2 +
    (2*u*(1-u)*x + (u^2+(1-u)^2)*y)^2 ≤ (1-u/4)^2*(x^2+y^2) := by
  obtain ⟨h₁,h₂⟩ := l925_marked_rows hu hmax
  apply l925_weighted_norm
  · positivity
  · exact mul_nonneg (by positivity) (by linarith)
  · positivity
  · linarith
  · linarith
  · linarith

theorem l925_step_contraction {u x y : ℝ} (hu : 0 ≤ u) (h1 : u ≤ 1) :
    (u*x+(1-u)*y)^2 + ((1-u)*x+u*y)^2 ≤ x^2+y^2 := by
  nlinarith [mul_nonneg (mul_nonneg hu (sub_nonneg.mpr h1)) (sq_nonneg (x-y))]

def l925_sign {d : ℕ} (c v : Fin d → ZMod 2) : ℝ :=
  if (∑ j, c j * v j) = 0 then 1 else -1

theorem l925_character_sum {d : ℕ} {c : Fin d → ZMod 2} (hc : c ≠ 0) :
    ∑ v : Fin d → ZMod 2, l925_sign c v = 0 := by
  classical
  obtain ⟨k,hk⟩ : ∃ k, c k ≠ 0 := by
    by_contra! h
    exact hc (funext h)
  have two : ∀ q : ZMod 2, q = 0 ∨ q = 1 := by decide
  have hck := (two (c k)).resolve_left hk
  let e : Fin d → ZMod 2 := fun j => if j = k then 1 else 0
  have he : ∑ j, c j * e j = 1 := by simp [e, mul_ite, hck]
  have flip (v : Fin d → ZMod 2) :
      l925_sign c (v+e) = - l925_sign c v := by
    have hv : (∑ j, c j * (v+e) j) = (∑ j, c j * v j)+1 := by
      simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, he]
    unfold l925_sign
    rw [hv]
    have htwo : (1 : ZMod 2) + 1 = 0 := by decide
    rcases two (∑ j, c j * v j) with h|h <;> simp [h, htwo]
  have shift := Equiv.sum_comp (Equiv.addRight e) (fun v => l925_sign c v)
  change (∑ v, l925_sign c (v+e)) = _ at shift
  simp_rw [flip] at shift
  rw [Finset.sum_neg_distrib] at shift
  linarith

theorem l925_nonzero_character {d : ℕ} {c : Fin d → ZMod 2} (hc : c ≠ 0) :
    ∑ v ∈ (Finset.univ : Finset (Fin d → ZMod 2)).erase 0, l925_sign c v = -1 := by
  classical
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin d → ZMod 2))
    (l925_sign c) (Finset.mem_univ 0)
  rw [l925_character_sum hc] at h
  have h0 : l925_sign c 0 = 1 := by simp [l925_sign]
  rw [h0] at h
  linarith


abbrev l925_fiber {ι V : Type*} [Zero V] (p : ι → ι) (S : Finset ι) :=
  {x : ι → V // (∀ i, x i = 0 ∨ x (p i) = 0 ∨ x i = x (p i)) ∧
    ∀ i, x i ≠ 0 ↔ i ∈ S}

def l925_isolate {ι V : Type*} [DecidableEq ι] [Zero V]
    (p : ι → ι) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hn : p i ∉ S) (hp : ∀ j ∈ S, p j ≠ i) :
    l925_fiber (V := V) p S ≃
      l925_fiber (V := V) p (S.erase i) × {v : V // v ≠ 0} := by
  classical
  let drop (x : l925_fiber (V := V) p S) :
      l925_fiber (V := V) p (S.erase i) := by
    refine ⟨Function.update x.val i 0, ?_, ?_⟩
    · intro j
      by_cases h : j = i
      · subst j
        exact Or.inl (Function.update_self ..)
      by_cases h' : p j = i
      · exact Or.inr (Or.inl (by simp [h']))
      simpa [Function.update_of_ne h, Function.update_of_ne h'] using x.property.1 j
    · intro j
      by_cases h : j = i
      · subst j
        simp
      simp [Finset.mem_erase, h, x.property.2]
  let put (z : l925_fiber (V := V) p (S.erase i) × {v : V // v ≠ 0}) :
      l925_fiber (V := V) p S := by
    refine ⟨Function.update z.1.val i z.2.val, ?_, ?_⟩
    · intro j
      by_cases h : j = i
      · subst j
        have hn' : p i ≠ i := fun h => hn (h.symm ▸ hi)
        have hz : z.1.val (p i) = 0 := by
          by_contra h
          exact hn (Finset.mem_of_mem_erase ((z.1.property.2 _).1 h))
        exact Or.inr (Or.inl (by simpa [Function.update_of_ne hn'] using hz))
      by_cases h' : p j = i
      · have hz : z.1.val j = 0 := by
          by_contra hh
          exact hp j (Finset.mem_of_mem_erase ((z.1.property.2 _).1 hh)) h'
        exact Or.inl (by simpa [Function.update_of_ne h] using hz)
      simpa [Function.update_of_ne h, Function.update_of_ne h'] using z.1.property.1 j
    · intro j
      by_cases h : j = i
      · subst j
        simp [hi,z.2.property]
      simp [z.1.property.2, Finset.mem_erase, h]
  refine ⟨fun x => (drop x, ⟨x.val i,(x.property.2 i).2 hi⟩), put, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext j
    by_cases h : j = i <;> simp [drop,put,h,Function.update_of_ne]
  · intro z
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases h : j = i
      · subst j
        have hz : z.1.val i = 0 := by
          by_contra hh
          exact Finset.notMem_erase i S ((z.1.property.2 i).1 hh)
        simp [drop,put,hz]
      simp [drop,put,Function.update_of_ne h]
    · apply Subtype.ext
      simp [put]


def l925_apply (u : ℝ) (marked : Bool) (z : ℝ × ℝ) : ℝ × ℝ :=
  if marked then (2*u^2*z.1+2*u*(1-u)*z.2, 2*u*(1-u)*z.1+(u^2+(1-u)^2)*z.2)
  else (u*z.1+(1-u)*z.2, (1-u)*z.1+u*z.2)

def l925_run (u : ℝ) (bs : List Bool) (z : ℝ × ℝ) : ℝ × ℝ :=
  bs.foldr (l925_apply u) z

theorem l925_product_norm {u : ℝ} (hu : 0 ≤ u) (hm : u ≤ 3/8)
    (bs : List Bool) (z : ℝ × ℝ) :
    (l925_run u bs z).1^2+(l925_run u bs z).2^2 ≤
      ((1-u/4)^bs.count true)^2*(z.1^2+z.2^2) := by
  induction bs with
  | nil => simp [l925_run]
  | cons m bs ih =>
    cases m
    · simp only [l925_run, List.foldr_cons, l925_apply,
        Bool.false_eq_true, ite_false, List.count_cons] at *
      simpa using (l925_step_contraction hu (show u ≤ 1 by linarith)).trans ih
    · let y := l925_run u bs z
      have h := l925_marked_contraction (x := y.1) (y := y.2) hu hm
      have q := mul_le_mul_of_nonneg_left ih (sq_nonneg (1-u/4))
      change (l925_apply u true y).1^2+(l925_apply u true y).2^2 ≤ _
      change (l925_apply u true y).1^2+(l925_apply u true y).2^2 ≤ _ at h
      apply (h.trans q).trans_eq
      simp [pow_succ]
      ring

theorem l925_trace_bound {u : ℝ} (hu : 0 ≤ u) (hm : u ≤ 3/8)
    (bs : List Bool) :
    (l925_run u bs (1,0)).1 + (l925_run u bs (0,1)).2 ≤
      2*(1-u/4)^bs.count true := by
  have bound := l925_product_norm hu hm bs
  let A := l925_run u bs (1,0)
  let B := l925_run u bs (0,1)
  let r := (1-u/4)^bs.count true
  have hr : 0 ≤ r := pow_nonneg (by linarith) _
  have ha : A.1^2+A.2^2 ≤ r^2 := by simpa [A,r] using bound (1,0)
  have hb : B.1^2+B.2^2 ≤ r^2 := by simpa [B,r] using bound (0,1)
  have fst : A.1 ≤ r := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < A.1+r by linarith),sq_nonneg A.2]
  have snd : B.2 ≤ r := by
    by_contra! h
    nlinarith [mul_pos (sub_pos.mpr h) (show 0 < B.2+r by linarith),sq_nonneg B.1]
  change A.1+B.2 ≤ 2*r
  linarith


theorem l925_parity_centres {n : ℕ} (W : Finset (Fin n)) :
    ∃ T : Finset (Fin n), T ⊆ W ∧ W.card/2 ≤ T.card ∧
      (∀ i ∈ T, 0 < i.val) ∧ ∀ i ∈ T, ∀ j ∈ T, i.val+1 ≠ j.val := by
  classical
  let P := W.filter fun i => 0 < i.val
  let A := P.filter fun i => i.val % 2 = 0
  let B := P.filter fun i => i.val % 2 = 1
  have small : (W \ P).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have zi : i.val=0 := by
      rcases Finset.mem_sdiff.mp hi with ⟨wi,ni⟩
      by_contra! q
      exact ni (Finset.mem_filter.mpr ⟨wi,Nat.pos_of_ne_zero q⟩)
    have zj : j.val=0 := by
      rcases Finset.mem_sdiff.mp hj with ⟨wj,nj⟩
      by_contra! q
      exact nj (Finset.mem_filter.mpr ⟨wj,Nat.pos_of_ne_zero q⟩)
    exact Fin.ext (zi.trans zj.symm)
  have del := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (fun i : Fin n => 0 < i.val) W)
  change (W \ P).card + P.card = W.card at del
  have union : A ∪ B = P := by
    ext i
    simp only [A,B,Finset.mem_union,Finset.mem_filter]
    constructor
    · rintro (⟨h,_⟩|⟨h,_⟩) <;> exact h
    · intro h
      rcases Nat.mod_two_eq_zero_or_one i.val with h0|h1
      · exact Or.inl ⟨h,h0⟩
      · exact Or.inr ⟨h,h1⟩
  have dis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i h₁ h₂
    have h := (Finset.mem_filter.mp h₁).2
    have k := (Finset.mem_filter.mp h₂).2
    omega
  have eq := Finset.card_union_of_disjoint dis
  rw [union] at eq
  have choose (k : ℕ) (hsize : W.card/2 ≤ (P.filter fun i => i.val % 2 = k).card) :
      ∃ T : Finset (Fin n), T ⊆ W ∧ W.card/2 ≤ T.card ∧
        (∀ i ∈ T, 0 < i.val) ∧ ∀ i ∈ T, ∀ j ∈ T, i.val+1 ≠ j.val := by
    refine ⟨_,(Finset.filter_subset _ _).trans (Finset.filter_subset _ W),hsize,?_,?_⟩
    · intro i h; exact (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2
    · intro i hi j hj
      have h := (Finset.mem_filter.mp hi).2
      have q := (Finset.mem_filter.mp hj).2
      omega
  by_cases h : W.card/2 ≤ A.card
  · exact choose 0 h
  · apply choose 1
    change W.card/2 ≤ B.card
    omega


theorem l925_boundary_injective {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Zero V] (p : ι → ι) (trans : ∀ i j, ∃ k : ℕ, p^[k] i = j)
    (S : Finset ι) (hS : S ≠ Finset.univ) :
    Function.Injective (fun (x : l925_fiber (V := V) p S)
      (i : {j // j ∈ S ∧ p j ∉ S}) => (⟨x.val i.val,(x.property.2 _).2 i.property.1⟩ : {v : V // v ≠ 0})) := by
  classical
  intro x y eq
  obtain ⟨outside,ho⟩ : ∃ j, j ∉ S := by
    by_contra! h
    exact hS (Finset.eq_univ_of_forall h)
  have zeroOutside (z : l925_fiber (V := V) p S) {j} (hj : j ∉ S) :
      z.val j = 0 := by
    by_contra nz
    exact hj ((z.property.2 j).1 nz)
  have propagate (i : ι) (hi : x.val i ≠ y.val i) : x.val (p i) ≠ y.val (p i) := by
    have mem : i ∈ S := by
      by_contra h
      exact hi ((zeroOutside x h).trans (zeroOutside y h).symm)
    have following : p i ∈ S := by
      by_contra h
      exact hi (congrArg Subtype.val (congrFun eq ⟨i,mem,h⟩))
    have get (z : l925_fiber (V := V) p S) : z.val i = z.val (p i) :=
      ((z.property.1 i).resolve_left ((z.property.2 _).2 mem)).resolve_left ((z.property.2 _).2 following)
    rwa [← get x, ← get y]
  apply Subtype.ext
  funext i
  by_contra ne
  have all (k : ℕ) : x.val (p^[k] i) ≠ y.val (p^[k] i) := by
    induction k with
    | zero => exact ne
    | succ k ih => simpa only [Function.iterate_succ_apply'] using propagate _ ih
  obtain ⟨k,hk⟩ := trans i outside
  have hn := all k
  rw [hk] at hn
  exact hn ((zeroOutside x ho).trans (zeroOutside y ho).symm)

theorem l925_boundary_count {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Zero V] [Fintype V] [DecidableEq V] (p : ι → ι) (trans : ∀ i j, ∃ k : ℕ, p^[k] i = j)
    (S : Finset ι) (hS : S ≠ Finset.univ) :
    Nat.card (l925_fiber (V := V) p S) ≤
    (Fintype.card V - 1)^(S.filter (fun j => p j ∉ S)).card := by
  classical
  have h := Nat.card_le_card_of_injective _ (l925_boundary_injective (V := V) p trans S hS)
  rw [Nat.card_fun] at h
  have c₁ : Nat.card {v : V // v ≠ 0} = Fintype.card V - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  have c₂ : Nat.card {j // j ∈ S ∧ p j ∉ S} = (S.filter (fun j => p j ∉ S)).card := by
    let E : {j // j ∈ S ∧ p j ∉ S} ≃ ↥(S.filter fun j => p j ∉ S) :=
      Equiv.subtypeEquivRight (fun j => by simp)
    rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_coe]
  simpa only [c₁,c₂] using h


noncomputable def l925_weight {ι : Type*} [Fintype ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (x : ι → Fin d → ZMod 2) : ℝ :=
  ∏ i, l925_sign (C i) (x i)

noncomputable def l925_fsum {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (p : ι → ι) (S : Finset ι) : ℝ := by
  classical
  exact ∑ x : l925_fiber (V := Fin d → ZMod 2) p S,
    l925_weight C x.val

theorem l925_update_weight {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (x : ι → Fin d → ZMod 2) (i : ι) (v : Fin d → ZMod 2) (hx : x i=0) :
    l925_weight C (Function.update x i v) =
      l925_weight C x * l925_sign (C i) v := by
  classical
  unfold l925_weight
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      ← Finset.prod_erase_mul _ (fun j => l925_sign (C j) (x j)) (Finset.mem_univ i)]
  have off : (∏ j ∈ Finset.univ.erase i, l925_sign (C j) (Function.update x i v j)) =
      ∏ j ∈ Finset.univ.erase i, l925_sign (C j) (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [off,Function.update_self,hx]
  simp [l925_sign]

theorem l925_isolated_bias {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (p : ι → ι) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hn : p i ∉ S) (hp : ∀ j ∈ S, p j ≠ i) (hc : C i ≠ 0) :
    l925_fsum C p S = -l925_fsum C p (S.erase i) := by
  classical
  let A := l925_fiber (V := Fin d → ZMod 2) p S
  let B := l925_fiber (V := Fin d → ZMod 2) p (S.erase i)
  let K := {v : Fin d → ZMod 2 // v ≠ 0}
  let e : A ≃ B × K := l925_isolate p S i hi hn hp
  have factor (z : B × K) : l925_weight C (e.symm z).val =
      l925_weight C z.1.val * l925_sign (C i) z.2.val := by
    have hz : z.1.val i = 0 := by
      by_contra h
      exact Finset.notMem_erase i S ((z.1.property.2 i).1 h)
    exact l925_update_weight C z.1.val i z.2.val hz
  have sumK : ∑ v : K, l925_sign (C i) v.val = -1 := by
    rw [← Finset.sum_subtype (Finset.univ.erase (0 : Fin d → ZMod 2))
      (fun j => by simp) (l925_sign (C i))]
    exact l925_nonzero_character hc
  change (∑ x : A, l925_weight C x.val) =
    -∑ x : B, l925_weight C x.val
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  simp_rw [factor, ← Finset.mul_sum, sumK]
  simp


theorem l925_weight_abs {ι : Type*} [Fintype ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (x : ι → Fin d → ZMod 2) :
    |l925_weight C x| = 1 := by
  classical
  have each (i : ι) : |l925_sign (C i) (x i)| = 1 := by
    unfold l925_sign
    split_ifs <;> norm_num
  simp [l925_weight,Finset.abs_prod,each]

theorem l925_base_bias {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (p : ι → ι) (trans : ∀ i j, ∃ k : ℕ, p^[k] i = j)
    (S : Finset ι) (hS : S ≠ Finset.univ) :
    |l925_fsum C p S| ≤
      ((Fintype.card (Fin d → ZMod 2) - 1 : ℕ) : ℝ)^(S.filter (fun j => p j ∉ S)).card := by
  classical
  let A := l925_fiber (V := Fin d → ZMod 2) p S
  change |∑ x : A, l925_weight C x.val| ≤ _
  calc
    _ ≤ ∑ x : A, |l925_weight C x.val| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = (Fintype.card A : ℝ) := by simp [l925_weight_abs]
    _ ≤ _ := by
      have h := l925_boundary_count (V := Fin d → ZMod 2) p trans S hS
      change Nat.card A ≤ _ at h
      rw [Nat.card_eq_fintype_card] at h
      exact_mod_cast h

theorem l925_support_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (p : ι → ι) (trans : ∀ i j, ∃ k : ℕ, p^[k] i = j)
    (S J : Finset ι) (hS : S ≠ Finset.univ) (sub : J ⊆ S)
    (single : ∀ i ∈ J, C i ≠ 0 ∧ p i ∉ S ∧ ∀ j ∈ S, p j ≠ i) :
    let q : ℝ := (Fintype.card (Fin d → ZMod 2) - 1 : ℕ)
    |l925_fsum C p S| * q^J.card ≤ q^(S.filter fun j => p j ∉ S).card := by
  classical
  let q : ℝ := (Fintype.card (Fin d → ZMod 2) - 1 : ℕ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  change |l925_fsum C p S| * q^J.card ≤ q^(S.filter fun j => p j ∉ S).card
  induction J using Finset.induction_on generalizing S with
  | empty => simpa [q] using l925_base_bias C p trans S hS
  | @insert i J hnot ih =>
    obtain ⟨c,nxt,prev⟩ := single i (Finset.mem_insert_self ..)
    have mem : i ∈ S := sub (Finset.mem_insert_self ..)
    have s' : S.erase i ≠ Finset.univ := by
      intro eq
      exact Finset.notMem_erase i S (eq.symm ▸ Finset.mem_univ i)
    have jsub : J ⊆ S.erase i := by
      intro j hj
      exact Finset.mem_erase.mpr ⟨fun e => hnot (e ▸ hj),sub (Finset.mem_insert_of_mem hj)⟩
    have prior :=  ih (S.erase i) s' jsub (by
      intro j hj
      obtain ⟨a,b,c⟩ := single j (Finset.mem_insert_of_mem hj)
      exact ⟨a,fun h => b (Finset.mem_of_mem_erase h),fun k hk => c k (Finset.mem_of_mem_erase hk)⟩)
    have changeEnds : (S.erase i).filter (fun j => p j ∉ S.erase i) =
        (S.filter fun j => p j ∉ S).erase i := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨⟨ne,m⟩,h⟩
        exact ⟨ne,m,fun pm => h ⟨prev j m,pm⟩⟩
      · rintro ⟨ne,m,h⟩
        exact ⟨⟨ne,m⟩,fun hp => h hp.2⟩
    have endMem : i ∈ S.filter (fun j => p j ∉ S) := Finset.mem_filter.mpr ⟨mem,nxt⟩
    have count := Finset.card_erase_add_one endMem
    rw [changeEnds] at prior
    rw [l925_isolated_bias C p S i mem nxt prev c,abs_neg,
      Finset.card_insert_of_notMem hnot, pow_succ, ← count, pow_succ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right prior hq


def l925_char (t : ZMod 2) : ℝ := if t = 0 then 1 else -1

theorem l925_char_add (a b : ZMod 2) :
    l925_char (a+b) = l925_char a * l925_char b := by
  have two : ∀ x : ZMod 2, x=0 ∨ x=1 := by decide
  have hh : (1 : ZMod 2) + 1 = 0 := by decide
  rcases two a with rfl|rfl <;> rcases two b with rfl|rfl <;> simp [l925_char,hh]

theorem l925_char_sum {ι : Type*} (s : Finset ι) (t : ι → ZMod 2) :
    l925_char (∑ i ∈ s,t i) = ∏ i ∈ s,l925_char (t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l925_char]
  | insert i s hi ih => simp [hi,l925_char_add,ih]

theorem l925_filtered_bias {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (C : ι → Fin d → ZMod 2) (p : ι → ι) (S : Finset ι) :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    let legal := fun x : ι → Fin d → ZMod 2 => ∀ i, x i=0 ∨ x (p i)=0 ∨ x i=x (p i)
    let supp := fun x : ι → Fin d → ZMod 2 => Finset.univ.filter fun i => x i≠0
    (∑ x ∈ Finset.univ.filter (fun x => legal x ∧ supp x=S),
      if (∑ i,∑ j, C i j * x i j)=0 then (1 : ℝ) else -1) =
    l925_fsum C p S := by
  classical
  dsimp only
  let A := l925_fiber (V := Fin d → ZMod 2) p S
  let h (x : ι → Fin d → ZMod 2) := (∀ i,x i=0 ∨ x (p i)=0 ∨ x i=x (p i)) ∧
      Finset.univ.filter (fun i => x i≠0) = S
  have mem (x : ι → Fin d → ZMod 2) : x ∈ Finset.univ.filter h ↔
      (∀ i,x i=0 ∨ x (p i)=0 ∨ x i=x (p i)) ∧ ∀ i, x i≠0 ↔ i ∈ S := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,h]
    apply and_congr_right
    intro _
    constructor
    · intro eq i
      rw [← eq]
      simp
    · intro eq
      ext i
      simpa using eq i
  trans ∑ x ∈ Finset.univ.filter h, l925_char (∑ i, ∑ j, C i j*x i j)
  · apply Finset.sum_congr _ _
    · ext x; simp [h]
    · intro x hx; unfold l925_char; split_ifs <;> rfl
  unfold l925_fsum
  rw [Finset.sum_subtype (Finset.univ.filter h) mem]
  apply Finset.sum_congr (by ext z; simp)
  intro x _
  exact l925_char_sum _ _
  all_goals infer_instance


abbrev l925_span : List Bool → ℕ
  | [] => 0
  | false :: bs => l925_span bs + 1
  | true :: bs => l925_span bs + 2

def l925_head {m : ℕ} (x : Fin m → Bool) (b : Bool) : Bool :=
  if hm : 0 < m then x ⟨0,hm⟩ else b

def l925_edge (u : ℝ) (a b : Bool) : ℝ := if a = b then u else 1-u

def l925_two (u : ℝ) (a c b : Bool) : ℝ :=
  if a = false ∧ c = true ∧ b = false then u^2
  else l925_edge u a c * l925_edge u c b

def l925_path (u : ℝ) : (bs : List Bool) →
    (Fin (l925_span bs) → Bool) → Bool → ℝ
  | [], _, _ => 1
  | false :: bs, x, b =>
    l925_edge u (x 0) (l925_head (Fin.tail x) b) *
      l925_path u bs (Fin.tail x) b
  | true :: bs, x, b =>
    l925_two u (x 0) (x 1) (l925_head (Fin.tail (Fin.tail x)) b) *
      l925_path u bs (Fin.tail (Fin.tail x)) b

theorem l925_sum_cons {m : ℕ} (f : (Fin (m+1) → Bool) → ℝ) :
    (∑ x, f x) = ∑ y : Fin m → Bool, (f (Fin.cons false y) + f (Fin.cons true y)) := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m+1) => Bool)) f, Fintype.sum_prod_type]
  simp [Fin.consEquiv_apply, Finset.sum_add_distrib, add_comm]

noncomputable def l925_entry (u : ℝ) (bs : List Bool) (a b : Bool) : ℝ :=
  ∑ x, if l925_head x b = a then l925_path u bs x b else 0

theorem l925_partition_tail {m : ℕ} (h : (Fin m → Bool) → Bool)
    (f : (Fin m → Bool) → ℝ) (k : Bool → ℝ) :
    (∑ x, k (h x) * f x) = k false * (∑ x, if h x = false then f x else 0) +
      k true * (∑ x, if h x = true then f x else 0) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  cases h x <;> simp

theorem l925_entry_step (u : ℝ) (bs : List Bool) (a b : Bool) :
    l925_entry u (false::bs) a b =
    l925_edge u a false * l925_entry u bs false b +
    l925_edge u a true * l925_entry u bs true b := by
  unfold l925_entry
  simp only [l925_span]
  rw [l925_sum_cons]
  rw [← l925_partition_tail]
  apply Finset.sum_congr rfl
  intro x _
  cases a <;> simp [l925_head,l925_path,
    Fin.tail_cons]

theorem l925_entry_mark (u : ℝ) (bs : List Bool) (a b : Bool) :
    l925_entry u (true::bs) a b =
    (l925_two u a false false + l925_two u a true false) *
      l925_entry u bs false b +
    (l925_two u a false true + l925_two u a true true) *
      l925_entry u bs true b := by
  unfold l925_entry
  simp only [l925_span]
  rw [l925_sum_cons,l925_sum_cons]
  rw [← l925_partition_tail (k := fun t =>
    l925_two u a false t + l925_two u a true t)]
  apply Finset.sum_congr rfl
  intro x _
  cases a <;> simp [l925_head,l925_path,
    Fin.tail_cons,add_mul]


theorem l925_entry_vec (u : ℝ) (bs : List Bool) (b : Bool) :
    (l925_entry u bs false b, l925_entry u bs true b) =
    l925_run u bs (if b then (0,1) else (1,0)) := by
  induction bs with
  | nil =>
    cases b <;> simp [l925_entry,l925_run,
      l925_path,l925_head,l925_span]
  | cons m bs ih =>
    change _ = l925_apply u m (l925_run u bs _)
    rw [← ih]
    cases m
    · simp [l925_entry_step, l925_apply, l925_edge]
    · apply Prod.ext <;>
        simp [l925_entry_mark,l925_apply,
          l925_two,l925_edge] <;> ring

theorem l925_closed_sum {u : ℝ} (hu : 0 ≤ u) (hm : u ≤ 3/8)
    (bs : List Bool) (h : 0 < l925_span bs) :
    (∑ x : Fin (l925_span bs) → Bool, l925_path u bs x (x ⟨0,h⟩)) ≤
      2*(1-u/4)^bs.count true := by
  have split : (∑ x : Fin (l925_span bs) → Bool, l925_path u bs x (x ⟨0,h⟩)) =
      l925_entry u bs false false + l925_entry u bs true true := by
    unfold l925_entry
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    cases z : x ⟨0,h⟩ <;> simp [l925_head,h,z]
  rw [split]
  have f := congrArg Prod.fst (l925_entry_vec u bs false)
  have t := congrArg Prod.snd (l925_entry_vec u bs true)
  simp only [Bool.false_eq_true,ite_false,ite_true] at f t
  rw [f,t]
  exact l925_trace_bound hu hm bs


def l925_marks : (bs : List Bool) → Fin (l925_span bs) → Bool
  | [], i => Fin.elim0 i
  | false::bs, i => Fin.cons (α := fun _ => Bool) false (l925_marks bs) i
  | true::bs, i => Fin.cons (α := fun _ => Bool) false (Fin.cons (α := fun _ => Bool) true (l925_marks bs)) i

theorem l925_tile (n : ℕ) (t : Fin n → Bool)
    (first : ∀ i, t i = true → 0 < i.val)
    (sep : ∀ i j, t i = true → t j = true → i.val+1 ≠ j.val) :
    ∃ bs : List Bool, ∃ h : n = l925_span bs,
      ∀ i, l925_marks bs (i.cast h) = t i := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => exact ⟨[],rfl,fun i => Fin.elim0 i⟩
    | succ n =>
      have h0 : t 0 = false := by
        cases e : t 0 with
        | false => rfl
        | true => exact False.elim (Nat.not_lt_zero _ (first 0 e))
      cases n with
      | zero =>
        refine ⟨[false],rfl,?_⟩
        intro i
        have h : i=0 := Fin.ext (by have := i.isLt; change i.val=0; omega)
        subst i
        exact h0.symm
      | succ k =>
        cases h1 : t 1 with
        | true =>
          obtain ⟨bs,hb,matchb⟩ := ih k (by omega) (fun i => t i.succ.succ) (by
            intro i hi
            by_contra! z
            have bad := sep 1 i.succ.succ h1 hi
            simp only [Fin.val_succ] at bad
            have one : (1 : Fin (k+2)).val=1 := by simp
            omega) (by
            intro i j a b m
            apply sep i.succ.succ j.succ.succ a b
            simp only [Fin.val_succ]
            omega)
          subst k
          refine ⟨true::bs,rfl,?_⟩
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact h0.symm
          · refine Fin.cases ?_ (fun v => ?_) j
            · simpa [l925_marks] using h1.symm
            · simpa [l925_marks] using matchb v
        | false =>
          obtain ⟨bs,hb,matchb⟩ := ih (k+1) (by omega) (fun i => t i.succ) (by
            intro i hi
            by_contra! z
            have iz : i=0 := Fin.ext (by change i.val=0; omega)
            subst i
            change t 1 = true at hi
            simp [h1] at hi) (by
            intro i j a b m
            apply sep i.succ j.succ a b
            simp only [Fin.val_succ]
            omega)
          refine ⟨false::bs,congrArg Nat.succ hb,?_⟩
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa [l925_marks] using h0.symm
          · exact matchb j

theorem l925_mark_count (bs : List Bool) :
    (∑ i, if l925_marks bs i = true then 1 else 0 : ℕ) = bs.count true := by
  induction bs with
  | nil => simp [l925_span]
  | cons m bs ih =>
    cases m
    · simpa [l925_marks,Fin.sum_univ_succ,List.count_cons] using ih
    · rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [l925_marks, Fin.cons_zero,Fin.cons_succ,Bool.false_eq_true,ite_false,ite_true,Nat.zero_add,ih]
      simp [Nat.add_comm]


def l925_after {n : ℕ} (x : Fin n → Bool) (b : Bool) (i : Fin n) : Bool :=
  Fin.snoc (α := fun _ => Bool) x b i.succ

def l925_before {n : ℕ} (x : Fin n → Bool) (b : Bool) (i : Fin n) : Bool :=
  Fin.cons (α := fun _ => Bool) b x i.castSucc

def l925_endbit (a b : Bool) : ℕ := if a = true ∧ b = false then 1 else 0

def l925_isobit (m z a b : Bool) : ℕ :=
  if m = true ∧ z = false ∧ a = true ∧ b = false then 1 else 0

def l925_ends {n : ℕ} (x : Fin n → Bool) (b : Bool) : ℕ :=
  ∑ i, l925_endbit (x i) (l925_after x b i)

def l925_solos {n : ℕ} (t x : Fin n → Bool) (z b : Bool) : ℕ :=
  ∑ i, l925_isobit (t i) (l925_before x z i)
    (x i) (l925_after x b i)

theorem l925_after_zero {n : ℕ} (a : Bool) (x : Fin n → Bool) (b : Bool) :
    l925_after (Fin.cons a x) b 0 = l925_head x b := by
  unfold l925_after
  rw [← Fin.cons_snoc_eq_snoc_cons]
  change Fin.snoc (α := fun _ => Bool) x b 0 = _
  cases n with
  | zero => exact Fin.snoc_last _ _
  | succ n => simp [l925_head,Fin.snoc_apply_zero]

theorem l925_after_succ {n : ℕ} (a : Bool) (x : Fin n → Bool) (b : Bool) (i : Fin n) :
    l925_after (Fin.cons a x) b i.succ = l925_after x b i := by
  unfold l925_after
  rw [← Fin.cons_snoc_eq_snoc_cons, Fin.cons_succ]

theorem l925_ends_cons {n : ℕ} (a : Bool) (x : Fin n → Bool) (b : Bool) :
    l925_ends (Fin.cons a x) b =
      l925_endbit a (l925_head x b) + l925_ends x b := by
  unfold l925_ends
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,l925_after_zero,l925_after_succ]

theorem l925_solos_cons {n : ℕ} (m a : Bool) (t x : Fin n → Bool) (z b : Bool) :
    l925_solos (Fin.cons m t) (Fin.cons a x) z b =
      l925_isobit m z a (l925_head x b) + l925_solos t x a b := by
  unfold l925_solos
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,l925_after_zero,l925_after_succ]
  rfl

def l925_pot (v : ℝ) (a : Bool) : ℝ := if a then v else 1

theorem l925_normal_edge {v : ℝ} (hv : 0 < v) (a b : Bool) :
    (1+v)*l925_edge (1/(1+v)) a b * l925_pot v a =
      (v^2)^l925_endbit a b * l925_pot v b := by
  have h : 1+v ≠ 0 := by linarith
  cases a <;> cases b <;> simp [l925_edge,l925_endbit,
    l925_pot] <;> field_simp <;> simp

theorem l925_normal_two {v : ℝ} (hv : 0 < v) (a c b : Bool) :
    (1+v)^2*l925_two (1/(1+v)) a c b * l925_pot v a *
      (v^2)^l925_isobit true a c b =
      (v^2)^(l925_endbit a c + l925_endbit c b) *
      l925_pot v b := by
  have h : 1+v ≠ 0 := by linarith
  cases a <;> cases c <;> cases b <;> simp [l925_two,l925_edge,
    l925_endbit,l925_isobit,l925_pot] <;> field_simp <;> simp


theorem l925_join_weight {L R x y s m t e f j k : ℝ} (hm : m ≠ 0)
    (front : L*x*s*j=e*m) (back : R*y*m*k=f*t) :
    (L*R)*(x*y)*s*(j*k)=(e*f)*t := by
  apply mul_right_cancel₀ hm
  calc
    _ = (L*x*s*j)*(R*y*m*k) := by ring
    _ = _ := by rw [front,back]; ring

theorem l925_path_normal {v : ℝ} (hv : 0 < v) (bs : List Bool)
    (x : Fin (l925_span bs) → Bool) (z b : Bool) :
    (1+v)^l925_span bs * l925_path (1/(1+v)) bs x b *
      l925_pot v (l925_head x b) *
      (v^2)^l925_solos (l925_marks bs) x z b =
      (v^2)^l925_ends x b * l925_pot v b := by
  induction bs generalizing z with
  | nil => simp [l925_span,l925_head,l925_path,
      l925_ends,l925_solos]
  | cons m bs ih =>
    have nonzero (a : Bool) : l925_pot v a ≠ 0 := by
      cases a <;> simp [l925_pot,hv.ne']
    cases m
    · let a := x 0
      let y := Fin.tail x
      have same : x = Fin.cons a y := (Fin.cons_self_tail x).symm
      have tail := ih y a
      have head := l925_normal_edge hv a (l925_head y b)
      have combined := l925_join_weight (nonzero _) (show
        (1+v) * l925_edge (1/(1+v)) a (l925_head y b) *
        l925_pot v a * 1 = _ by simpa using head) tail
      rw [same]
      simp [l925_span,l925_path,l925_head,
        l925_marks,l925_solos_cons,l925_ends_cons,
        l925_isobit,pow_add] at combined ⊢
      linear_combination combined
    · let a := x 0
      let c := x 1
      let y := Fin.tail (Fin.tail x)
      have same : x = Fin.cons a (Fin.cons c y) := by
        change x = Fin.cons (x 0) (Fin.cons (Fin.tail x 0) (Fin.tail (Fin.tail x)))
        rw [Fin.cons_self_tail,Fin.cons_self_tail]
      have tail := ih y c
      have head := l925_normal_two hv a c (l925_head y b)
      have combined := l925_join_weight (nonzero _) head tail
      rw [same]
      simp [l925_span,l925_path,l925_marks,
        l925_solos_cons,l925_ends_cons,l925_head,
        l925_isobit,pow_add] at combined ⊢
      split_ifs at combined ⊢ <;> first | contradiction | linear_combination combined


def l925_next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩

theorem l925_reachable {n : ℕ} (i j : Fin n) :
    ∃ k : ℕ, l925_next^[k] i = j := by
  have step (k : ℕ) : (l925_next^[k] i).val=(i.val+k)%n := by
    induction k with
    | zero => simp [Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change ((l925_next^[k] i).val+1)%n = _
      rw [ih,Nat.mod_add_mod]
      rfl
  refine ⟨n-i.val+j.val,Fin.ext ?_⟩
  rw [step,show i.val+(n-i.val+j.val)=j.val+n by omega,Nat.add_mod_right,Nat.mod_eq_of_lt j.isLt]

theorem l925_after_cycle {n : ℕ} (hn : 0<n) (x : Fin n → Bool) (i : Fin n) :
    l925_after x (x ⟨0,hn⟩) i = x (l925_next i) := by
  unfold l925_after
  by_cases h : i.val+1<n
  · let j : Fin n := ⟨i.val+1,h⟩
    have eq : i.succ=j.castSucc := Fin.ext rfl
    have eq' : l925_next i = j := Fin.ext (Nat.mod_eq_of_lt h)
    rw [eq,Fin.snoc_castSucc,eq']
  · have h' : i.val+1=n := by omega
    have eq : i.succ=Fin.last n := Fin.ext h'
    have eq' : l925_next i = ⟨0,hn⟩ := by
      apply Fin.ext
      simp [l925_next,h']
    rw [eq,Fin.snoc_last,eq']

theorem l925_before_cycle {n : ℕ} (x : Fin n → Bool) (z : Bool)
    {i j : Fin n} (hi : 0 < i.val) (h : l925_next j = i) :
    l925_before x z i = x j := by
  have val := congrArg Fin.val h
  change (j.val+1)%n = i.val at val
  have hj : j.val+1<n := by
    by_contra hh
    have k : j.val+1=n := by omega
    rw [k,Nat.mod_self] at val
    omega
  rw [Nat.mod_eq_of_lt hj] at val
  have cast : i.castSucc = j.succ := Fin.ext val.symm
  unfold l925_before
  rw [cast,Fin.cons_succ]

def l925_boolEquiv (n : ℕ) : Finset (Fin n) ≃ (Fin n → Bool) where
  toFun S i := decide (i ∈ S)
  invFun x := Finset.univ.filter fun i => x i = true
  left_inv S := by ext i; simp
  right_inv x := by funext i; cases h : x i <;> simp [h]


theorem l925_one_support {d : ℕ} {v : ℝ} (hv : 0<v)
    (qval : ((Fintype.card (Fin d → ZMod 2)-1 : ℕ) : ℝ)=v^2)
    (bs : List Bool) (hn : 0<l925_span bs)
    (C : Fin (l925_span bs) → Fin d → ZMod 2)
    (marked : ∀ i, l925_marks bs i = true → 0 < i.val ∧ C i ≠ 0)
    (S : Finset (Fin (l925_span bs))) (proper : S ≠ Finset.univ) :
    let x := l925_boolEquiv _ S
    |l925_fsum C l925_next S| ≤
      (1+v)^l925_span bs * l925_path (1/(1+v)) bs x (x ⟨0,hn⟩) := by
  classical
  let n := l925_span bs
  let x : Fin n → Bool := fun i => decide (i ∈ S)
  let b := x ⟨0,hn⟩
  let p : Fin n → Fin n := l925_next
  let J := Finset.univ.filter fun i : Fin n => l925_marks bs i = true ∧
    l925_before x false i = false ∧ x i = true ∧ l925_after x b i = false
  have charJ (i : Fin n) : i ∈ J ↔ l925_marks bs i = true ∧
      l925_before x false i = false ∧ x i = true ∧ l925_after x b i = false := by simp [J]
  have sub : J ⊆ S := fun i hi => of_decide_eq_true ((charJ i).1 hi).2.2.1
  have iso (i : Fin n) (hi : i ∈ J) : C i ≠ 0 ∧ p i ∉ S ∧ ∀ j ∈ S, p j ≠ i := by
    obtain ⟨t,pr,onx,nx⟩ := (charJ i).1 hi
    obtain ⟨pos,ci⟩ := marked i t
    rw [l925_after_cycle hn x i] at nx
    refine ⟨ci,of_decide_eq_false nx,?_⟩
    intro j hj eq
    rw [l925_before_cycle x false pos eq] at pr
    exact (of_decide_eq_false pr) hj
  have ce : l925_ends x b = (S.filter fun i => p i ∉ S).card := by
    unfold l925_ends l925_endbit
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext j
    have eq : l925_after x b j = x (p j) := l925_after_cycle hn x j
    simp [eq,x]
  have cj : l925_solos (l925_marks bs) x false b = J.card := by
    unfold l925_solos l925_isobit
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext j
    simp [J]
  have bound := l925_support_bound C p l925_reachable S J proper sub iso
  dsimp only at bound
  rw [qval,← ce,← cj] at bound
  have norm := l925_path_normal hv bs x false b
  have hbase : l925_head x b = b := by simp [l925_head,b]
  rw [hbase] at norm
  have nz : l925_pot v b ≠ 0 := by cases b <;> simp [l925_pot,hv.ne']
  have ident : (1+v)^n * l925_path (1/(1+v)) bs x b *
      (v^2)^l925_solos (l925_marks bs) x false b =
      (v^2)^l925_ends x b := by
    apply mul_right_cancel₀ nz
    convert norm using 1; ring
  rw [← ident] at bound
  exact (le_of_mul_le_mul_right bound (by positivity))


theorem l925_path_nonneg {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (bs : List Bool) (x : Fin (l925_span bs) → Bool) (b : Bool) :
    0 ≤ l925_path u bs x b := by
  have edge (a c : Bool) : 0 ≤ l925_edge u a c := by
    unfold l925_edge
    split <;> linarith
  have two (a c e : Bool) : 0 ≤ l925_two u a c e := by
    unfold l925_two
    split
    · positivity
    · exact mul_nonneg (edge _ _) (edge _ _)
  induction bs with
  | nil => exact zero_le_one
  | cons m bs ih =>
    cases m
    · exact mul_nonneg (edge _ _) (ih _)
    · exact mul_nonneg (two _ _ _) (ih _)

set_option maxHeartbeats 600000 in
theorem l925_total {n d : ℕ} (hn : 3 ≤ n) (hd : 2 ≤ d)
    (C : Fin n → Fin d → ZMod 2) :
    let W := Finset.univ.filter fun i => C i ≠ 0
    let L := 1 + Real.sqrt ((2 : ℝ)^d-1)
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ, |l925_fsum C l925_next S|) ≤
      2*L^n*(1-1/(4*L))^(W.card/2) := by
  classical
  let W := Finset.univ.filter fun i => C i ≠ 0
  obtain ⟨T,sub,sz,pos,sep⟩ := l925_parity_centres W
  obtain ⟨bs,hb,pattern⟩ := l925_tile n (fun i => decide (i ∈ T))
    (fun i h => pos i (of_decide_eq_true h))
    (fun i j a b => sep i (of_decide_eq_true a) j (of_decide_eq_true b))
  subst n
  let v := Real.sqrt ((2 : ℝ)^d-1)
  let u := 1/(1+v)
  have hp : (2 : ℝ)^2 ≤ 2^d := pow_le_pow_right₀ (by norm_num) hd
  have hv : 0 < v := Real.sqrt_pos.2 (by nlinarith)
  have qval : ((Fintype.card (Fin d → ZMod 2)-1 : ℕ) : ℝ)=v^2 := by
    dsimp [v]
    rw [Real.sq_sqrt (by nlinarith)]
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card]
    rw [Nat.cast_sub (Nat.succ_le_of_lt (pow_pos (by decide) _))]
    push_cast; rfl
  have mark (i : Fin (l925_span bs)) (h : l925_marks bs i = true) :
      0 < i.val ∧ C i ≠ 0 := by
    have hi : i ∈ T := of_decide_eq_true ((pattern i).symm.trans h)
    exact ⟨pos i hi,(Finset.mem_filter.mp (sub hi)).2⟩
  have hc : bs.count true = T.card := by
    rw [← l925_mark_count bs]
    have pat (i : Fin (l925_span bs)) : l925_marks bs i = decide (i ∈ T) := pattern i
    simp [pat]
  have ne : 0 < l925_span bs := by omega
  let P := fun x : Fin (l925_span bs) → Bool => l925_path u bs x (x ⟨0,ne⟩)
  let E := l925_boolEquiv (l925_span bs)
  obtain ⟨hu',hm'⟩ := l925_stay_le hd
  have hu : 0 ≤ u := hu'.le
  have hm : u ≤ 3/8 := hm'
  have hle : u ≤ 1 := by linarith
  have dec : (1-u/4)^bs.count true ≤ (1-u/4)^(W.card/2) :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (sz.trans_eq hc.symm)
  have norm : 1-u/4 = 1-1/(4*(1+v)) := by
    dsimp [u]
    rw [div_div, mul_comm (1+v)]
  change (∑ S ∈ (Finset.univ : Finset (Finset (Fin (l925_span bs)))).erase Finset.univ, _) ≤
    2*(1+v)^l925_span bs*(1-1/(4*(1+v)))^(W.card/2)
  calc
    _ ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin (l925_span bs)))).erase Finset.univ,
        (1+v)^l925_span bs * P (E S) := by
      apply Finset.sum_le_sum
      intro S h
      exact l925_one_support hv qval bs ne C mark S (Finset.ne_of_mem_erase h)
    _ ≤ ∑ S : Finset (Fin (l925_span bs)), (1+v)^l925_span bs * P (E S) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro S _ _
      exact mul_nonneg (by positivity) (l925_path_nonneg hu hle _ _ _)
    _ = (1+v)^l925_span bs * ∑ x, P x := by
      rw [← Finset.mul_sum,Equiv.sum_comp E P]
    _ ≤ (1+v)^l925_span bs * (2*(1-u/4)^bs.count true) :=
      mul_le_mul_of_nonneg_left (l925_closed_sum hu hm bs ne) (by positivity)
    _ ≤ (1+v)^l925_span bs * (2*(1-u/4)^(W.card/2)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left dec (by norm_num)) (by positivity)
    _ = _ := by rw [norm]; ring

end PEqualNP.Outside.L_lib_925_aux

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.L_lib_925 : (∀ (n d : ℕ), 3 ≤ n → 2 ≤ d →
  ∀ C : Fin n → Fin d → ZMod 2,
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let F := ZMod 2
  let V := Fin d → F
  let X := Fin n → V
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩ : Fin n)
  let proper := (Finset.univ : Finset (Finset (Fin n))).erase Finset.univ
  let legal := fun x : X => ∀ i, x i = 0 ∨ x (next i) = 0 ∨ x i = x (next i)
  let supp := fun x : X => Finset.univ.filter (fun i => x i ≠ 0)
  let sgn := fun x : X =>
    if (∑ i, ∑ j, C i j * x i j) = 0 then (1 : ℝ) else -1
  let bias := fun S : Finset (Fin n) =>
    ∑ x ∈ (Finset.univ.filter (fun x : X => legal x ∧ supp x = S)), sgn x
  let w := (Finset.univ.filter (fun i : Fin n => C i ≠ 0)).card
  let L := 1 + Real.sqrt ((2 : ℝ)^d - 1)
  (∑ S ∈ proper, |bias S|) ≤ 2 * L^n * (1 - 1/(4*L))^(w/2)) := by
  intro n d hn hd C
  dsimp only
  have total := PEqualNP.Outside.L_lib_925_aux.l925_total hn hd C
  dsimp only at total
  convert total using 1
  · apply Finset.sum_congr
    · ext S
      simp
    · intro S _
      apply congrArg abs
      have h := PEqualNP.Outside.L_lib_925_aux.l925_filtered_bias C
        PEqualNP.Outside.L_lib_925_aux.l925_next S
      dsimp only at h
      refine Eq.trans ?_ (h.trans ?_)
      swap
      · exact congrArg (fun inst : DecidableEq (Fin n) =>
          @PEqualNP.Outside.L_lib_925_aux.l925_fsum (Fin n) _ inst d C
            PEqualNP.Outside.L_lib_925_aux.l925_next S) (Subsingleton.elim _ _)
      apply Finset.sum_congr
      · ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply and_congr
        · rfl
        · apply iff_of_eq
          apply congrArg (fun A => A = S)
          apply Finset.ext
          intro i
          simp
      · intro x _
        split_ifs <;> rfl
  · congr 3
    apply congrArg Finset.card
    ext i
    simp
