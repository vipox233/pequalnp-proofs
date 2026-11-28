import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Count
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Infix
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_32056

private abbrev Bit := ZMod 2

private lemma bit_cases (a : Bit) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma bit_cancel (a b : Bit) : a + b + a = b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;> decide

private lemma bit_solve (a b c : Bit) : a + b = c ↔ b = c + a := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    rcases bit_cases c with rfl | rfl <;> decide

private lemma find_pivot {V : Type*} [Fintype V] [DecidableEq V]
    (l : (V → Bit) →ₗ[Bit] Bit) (hl : l ≠ 0) : ∃ p : V, l (Pi.single p 1) = 1 := by
  contrapose! hl
  apply LinearMap.ext
  intro x
  have hx : (∑ i : V, x i • Pi.single i (1 : Bit)) = x := by
    classical
    have heq (i : V) : x i • Pi.single i (1 : Bit) = Pi.single i (x i) := by
      funext j
      by_cases h : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne h]
    simp_rw [heq]
    exact Finset.univ_sum_single x
  rw [← hx, map_sum]
  simp only [map_smul, LinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  have hi : l (Pi.single i 1) = 0 := (bit_cases _).resolve_right (hl i)
  simp [hi]

private lemma eliminate_pivot {V : Type*} [DecidableEq V] (S : Finset V)
    (l : (S → Bit) →ₗ[Bit] Bit) (p : S) (hp : l (Pi.single p 1) = 1) :
    ∃ E : ((S.erase p.val) → Bit) →ₗ[Bit] (S → Bit),
      (∀ u, l (E u) = 0) ∧
      (∀ b : Bit, ∀ u, l (E u + b • Pi.single p 1) = b) ∧
      (∀ b : Bit, ∀ u, ∀ i : S.erase p.val,
        (show S → Bit from E u + b • Pi.single p 1) ⟨i, Finset.mem_of_mem_erase i.property⟩ = u i) ∧
      (∀ b : Bit, ∀ x, l x = b → ∃ u, E u + b • Pi.single p 1 = x) := by
  let U := S.erase p.val
  let e : S → Bit := Pi.single p 1
  let P : (U → Bit) →ₗ[Bit] (S → Bit) := LinearMap.pi fun i : S =>
    if hi : i.val ∈ U then LinearMap.proj (⟨i.val, hi⟩ : U) else 0
  let E : (U → Bit) →ₗ[Bit] (S → Bit) := P + (l.comp P).smulRight e
  have he : l e = 1 := hp
  have happ (u : U → Bit) : E u = P u + l (P u) • e := by
    simp [E, LinearMap.smulRight_apply]
  have hzero (u : U → Bit) : l (E u) = 0 := by
    rw [happ, map_add, map_smul, he, smul_eq_mul, mul_one]
    simpa using bit_cancel (l (P u)) 0
  have hcoord (u : U → Bit) (i : S) (hi : i.val ∈ U) : P u i = u ⟨i.val, hi⟩ := by
    simp [P, hi]
  have hcoordp (u : U → Bit) : P u p = 0 := by simp [P, U]
  have hecoord (i : S) (hi : i.val ∈ U) : e i = 0 := by
    apply Pi.single_eq_of_ne
    intro h
    subst i
    exact Finset.notMem_erase _ _ hi
  refine ⟨E, hzero, ?_, ?_, ?_⟩
  · intro b u
    change l (E u + b • e) = b
    rw [map_add, hzero, map_smul, he, smul_eq_mul, mul_one, zero_add]
  · intro b u i
    let j : S := ⟨i, Finset.mem_of_mem_erase i.property⟩
    change (E u + b • e) j = u i
    rw [happ]
    simp [Pi.add_apply, Pi.smul_apply, hecoord j i.property, hcoord u j i.property, j]
  · intro b x hx
    let u : U → Bit := fun i => x ⟨i, Finset.mem_of_mem_erase i.property⟩
    have hx' : P u + x p • e = x := by
      funext i
      by_cases hij : i = p
      · subst i
        simp [Pi.add_apply, Pi.smul_apply, hcoordp, e]
      · have hi : i.val ∈ U := Finset.mem_erase.mpr ⟨fun h => hij (Subtype.ext h), i.property⟩
        simp [Pi.add_apply, Pi.smul_apply, hcoord u i hi, hecoord i hi, u]
    have hxp : l (P u) + x p = b := by
      simpa only [map_add, map_smul, he, smul_eq_mul, mul_one] using congrArg l hx' |>.trans hx
    have hcoef : l (P u) + b = x p := by
      exact (add_comm _ _).trans ((bit_solve _ _ _).mp hxp).symm
    refine ⟨u, ?_⟩
    change E u + b • e = x
    rw [happ, add_assoc, ← add_smul, hcoef, hx']

open Finset Polynomial

private noncomputable def auditScore {A I : Type*} [Fintype A] [DecidableEq I]
    (hits : A → Finset I) (j : ℕ) : ℕ :=
  ∑ x : A, (hits x).card.choose j

private lemma auditScore_coeff {A I : Type*} [Fintype A] [DecidableEq I]
    (hits : A → Finset I) (j : ℕ) :
    auditScore hits j = (∑ x : A, (1 + X : Polynomial ℕ) ^ (hits x).card).coeff j := by
  simp [auditScore, coeff_one_add_X_pow]

private lemma auditScore_audits {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (hits : A → Finset I) (j : ℕ) :
    auditScore hits j = ∑ s ∈ (univ : Finset I).powersetCard j,
      (univ.filter (fun x : A => s ⊆ hits x)).card := by
  classical
  have hfilter (x : A) : ((univ : Finset I).powersetCard j).filter (fun s => s ⊆ hits x) =
      (hits x).powersetCard j := by
    ext s
    simp [and_comm]
  unfold auditScore
  simp_rw [← card_powersetCard]
  simp_rw [← hfilter, card_eq_sum_ones, sum_filter]
  rw [sum_comm]

private lemma auditScore_mono_audits {A B I : Type*} [Fintype A] [Fintype B] [Fintype I]
    [DecidableEq I] (hitsA : A → Finset I) (hitsB : B → Finset I) (j : ℕ)
    (h : ∀ s ∈ (univ : Finset I).powersetCard j,
      (univ.filter (fun x : A => s ⊆ hitsA x)).card ≤
      (univ.filter (fun x : B => s ⊆ hitsB x)).card) :
    auditScore hitsA j ≤ auditScore hitsB j := by
  rw [auditScore_audits, auditScore_audits]
  exact sum_le_sum h

private lemma auditScore_universal {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (hits : A → Finset I) (j : ℕ) :
    auditScore hits j ≤ Fintype.card A * (Fintype.card I).choose j := by
  unfold auditScore
  calc
    _ ≤ ∑ _ : A, (Fintype.card I).choose j :=
      Finset.sum_le_sum (fun x _ => Nat.choose_le_choose _ (Finset.card_le_univ _))
    _ = _ := by simp [nsmul_eq_mul]

open scoped BigOperators


private theorem fp_square (u : Bit) : u * u = u := by
  fin_cases u
  · exact zero_mul (0 : Bit)
  · exact one_mul (1 : Bit)

private theorem fp_indicator (u v : Bit) :
    1 + u + v = (if u = v then 1 else 0) := by
  fin_cases u <;> fin_cases v <;> decide

private def fpMonomial {V X : Type*} (coords : X → V → Bit) (s : Finset V) (x : X) : Bit :=
  ∏ i ∈ s, coords x i

private theorem fpMonomial_insert_apply {V X : Type*} [DecidableEq V]
    (coords : X → V → Bit) (s : Finset V) (i : V) (x : X) :
    fpMonomial coords (insert i s) x = coords x i * fpMonomial coords s x := by
  unfold fpMonomial
  by_cases hi : i ∈ s
  · rw [Finset.insert_eq_of_mem hi, ← Finset.mul_prod_erase s (coords x) hi,
      ← mul_assoc, fp_square]
  · exact Finset.prod_insert hi

private theorem fp_linear_apply {V : Type*} [Fintype V] [DecidableEq V]
    (l : (V → Bit) →ₗ[Bit] Bit) (x : V → Bit) : l x = ∑ i, l (Pi.single i 1) * x i := by
  have hx : (∑ i, x i • Pi.single i (1 : Bit)) = x := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, LinearMap.sum_single_apply]
  calc
    l x = l (∑ i, x i • Pi.single i (1 : Bit)) := congrArg l hx.symm
    _ = ∑ i, l (Pi.single i 1) * x i := by
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

-- Each audited product can be replaced by an affine form on the solution set.
-- Consequently the independent-support monomials span all functions on that set.
private theorem affineFootprint_card_le {V E : Type*} [Fintype V]
    (a b : E → V) (hne : ∀ e, a e ≠ b e)
    (l : E → (V → Bit) →ₗ[Bit] Bit) (c : E → Bit) :
    Nat.card {x : V → Bit // ∀ e, x (a e) * x (b e) = l e x + c e} ≤
      Nat.card {x : V → Bit // ∀ e, ¬ (x (a e) = 1 ∧ x (b e) = 1)} := by
  classical
  let S := {x : V → Bit // ∀ e, x (a e) * x (b e) = l e x + c e}
  let I := {x : V → Bit // ∀ e, ¬ (x (a e) = 1 ∧ x (b e) = 1)}
  let _ : Fintype S := Fintype.ofFinite S
  let _ : Fintype I := Fintype.ofFinite I
  let m : Finset V → S → Bit := fpMonomial (fun x : S => x.1)
  let mono : I → S → Bit := fun y => m (Finset.univ.filter fun i => y.1 i = 1)
  let M := Submodule.span Bit (Set.range mono)
  have hm (s : Finset V) : m s ∈ M := by
    suffices h : ∀ n (s : Finset V), s.card = n → m s ∈ M from h _ s rfl
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro s hn
      by_cases hs : ∀ e, ¬ (a e ∈ s ∧ b e ∈ s)
      · let y : V → Bit := fun i => if i ∈ s then 1 else 0
        have hy (i : V) : y i = 1 ↔ i ∈ s := by simp [y]
        let z : I := ⟨y, fun e hz => hs e ⟨(hy _).mp hz.1, (hy _).mp hz.2⟩⟩
        have hz : (Finset.univ.filter fun i => z.1 i = 1) = s := by
          ext i
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy i
        have : mono z ∈ M := Submodule.subset_span ⟨z, rfl⟩
        simpa only [mono, hz] using this
      · push Not at hs
        obtain ⟨e, ha, hb⟩ := hs
        let t := (s.erase (a e)).erase (b e)
        have hb' : b e ∈ s.erase (a e) := Finset.mem_erase.mpr ⟨(hne e).symm, hb⟩
        have ht : t.card + 2 = n := by
          have h₁ := Finset.card_erase_add_one ha
          have h₂ := Finset.card_erase_add_one hb'
          dsimp only [t]
          omega
        have hreduce : m s = (∑ i, l e (Pi.single i 1) • m (insert i t)) + c e • m t := by
          funext x
          have hprod : m s x = (x.1 (a e) * x.1 (b e)) * m t x := by
            dsimp only [m, fpMonomial, t]
            rw [← Finset.mul_prod_erase s x.1 ha,
              ← Finset.mul_prod_erase (s.erase (a e)) x.1 hb', mul_assoc]
          rw [hprod, x.2 e, fp_linear_apply, add_mul, Finset.sum_mul]
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, m,
            fpMonomial_insert_apply, mul_assoc]
        rw [hreduce]
        refine M.add_mem (M.sum_mem ?_) (M.smul_mem _ (ih _ (by omega) t rfl))
        intro i _
        exact M.smul_mem _ (ih _ (by have := Finset.card_insert_le i t; omega) _ rfl)
  have hdelta (z : S) : (Pi.single z 1 : S → Bit) ∈ M := by
    -- Multiply the coordinate equality indicators, keeping every product squarefree.
    let Q (s t : Finset V) : S → Bit := fun x => (∏ i ∈ s, (1 + z.1 i + x.1 i)) * m t x
    have hQ (s : Finset V) : ∀ t, Q s t ∈ M := by
      induction s using Finset.induction_on with
      | empty =>
        intro t
        have heq : Q ∅ t = m t := by
          funext x
          simp [Q]
        rw [heq]
        exact hm t
      | @insert i s hi ih =>
        intro t
        have heq : Q (insert i s) t = (1 + z.1 i) • Q s t + Q s (insert i t) := by
          funext x
          simp only [Q, m, Finset.prod_insert hi, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
            fpMonomial_insert_apply]
          ring
        rw [heq]
        exact M.add_mem (M.smul_mem _ (ih t)) (ih _)
    have heq : Q Finset.univ ∅ = Pi.single z 1 := by
      funext x
      simp only [Q, m, fpMonomial, Finset.prod_empty, mul_one, Pi.single_apply]
      by_cases hx : x = z
      · subst x
        rw [ite_eq_left rfl]
        exact Finset.prod_eq_one fun i _ => by rw [fp_indicator, ite_eq_left rfl]
      · rw [ite_eq_right hx]
        have hn : ∃ i, z.1 i ≠ x.1 i := by
          by_contra! hall
          exact hx (Subtype.ext (funext fun i => (hall i).symm))
        obtain ⟨i, hi⟩ := hn
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
          fp_indicator, ite_eq_right hi, zero_mul]
    rw [← heq]
    exact hQ _ _
  have htop : M = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun Bit S).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, rfl⟩
    change Pi.basisFun Bit S z ∈ M
    rw [Pi.basisFun_apply]
    exact hdelta z
  change Nat.card S ≤ Nat.card I
  have hdim := finrank_le_of_span_eq_top (v := mono) htop
  simpa only [Nat.card_eq_fintype_card, Module.finrank_fintype_fun_eq_card] using hdim

open Finset

private lemma sum_powers_two (d : ℕ) : (∑ p ∈ range d, 2 ^ p) + 1 = 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih => rw [sum_range_succ, pow_succ]; omega

private lemma weighted_telescopes (b gain : ℕ → ℕ) (d : ℕ)
    (hstep : ∀ p < d, b p + gain p = 2 * b (p + 1)) :
    b 0 + ∑ p ∈ range d, 2 ^ p * gain p = 2 ^ d * b d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [sum_range_succ, ← add_assoc, ih (fun p hp => hstep p (by omega)),
      ← Nat.mul_add, hstep d (by omega), pow_succ]
    ac_rfl

private lemma depth_allocation
    (b gain count : ℕ → ℕ) (d r a : ℕ) (hdr : d ≤ r)
    (hstep : ∀ p < d, b p + gain p = 2 * b (p + 1)) (hg : Antitone gain)
    (hcount : ∀ p, count p ≤ 2 ^ p)
    (htotal : ∑ p ∈ range r, count p ≤ (2 ^ d - 1) + a) :
    b 0 + ∑ p ∈ range r, count p * gain p ≤ 2 ^ d * b d + a * gain d := by
  let slack (p : ℕ) := 2 ^ p * (gain p - gain d)
  have hpt (p : ℕ) : count p * gain p ≤ count p * gain d + slack p := by
    by_cases hp : p ≤ d
    · have hh := hg hp
      have h := Nat.mul_le_mul_right (gain p - gain d) (hcount p)
      have heq : count p * gain p =
          count p * gain d + count p * (gain p - gain d) := by
        rw [← Nat.mul_add, Nat.add_comm (gain d), Nat.sub_add_cancel hh]
      rw [heq]
      exact Nat.add_le_add_left h _
    · have hh := hg (show d ≤ p by omega)
      exact (Nat.mul_le_mul_left (count p) hh).trans (Nat.le_add_right _ _)
  have hslack : ∑ p ∈ range d, slack p = ∑ p ∈ range r, slack p := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr hdr)
    intro p _ hp
    have hdp : d ≤ p := by simpa using hp
    simp [slack, Nat.sub_eq_zero_of_le (hg hdp)]
  have hsplit :
      (∑ p ∈ range d, slack p) + (2 ^ d - 1) * gain d = ∑ p ∈ range d, 2 ^ p * gain p := by
    have hs := sum_powers_two d
    have hs' : ∑ p ∈ range d, 2 ^ p = 2 ^ d - 1 := by omega
    rw [← hs', Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hpd := hg (Nat.le_of_lt (Finset.mem_range.mp hp))
    unfold slack
    rw [← Nat.mul_add, Nat.sub_add_cancel hpd]
  calc
    b 0 + ∑ p ∈ range r, count p * gain p ≤
        b 0 + ∑ p ∈ range r, (count p * gain d + slack p) :=
      Nat.add_le_add_left (Finset.sum_le_sum fun p _ => hpt p) _
    _ = b 0 + ((∑ p ∈ range r, count p) * gain d + ∑ p ∈ range d, slack p) := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, hslack]
    _ ≤ b 0 + (((2 ^ d - 1) + a) * gain d + ∑ p ∈ range d, slack p) :=
      Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_right _ htotal) _) _
    _ = (b 0 + ∑ p ∈ range d, 2 ^ p * gain p) + a * gain d := by
      rw [Nat.add_mul, ← hsplit]
      ac_rfl
    _ = 2 ^ d * b d + a * gain d := by rw [weighted_telescopes b gain d hstep]

private abbrev Hist := List Bool

private def runTree {A : Type*} (nodes : Finset Hist) (ask : Hist → A → Bool) (x : A) :
    ℕ → Hist → Hist
  | 0, h => h
  | m + 1, h => if h ∈ nodes then runTree nodes ask x m (h ++ [ask h x]) else h

private lemma runTree_fold {A : Type*} (nodes : Finset Hist) (ask : Hist → A → Bool)
    (x : A) (m : ℕ) (h : Hist) : runTree nodes ask x m h =
      (List.range m).foldl (fun q _ => if q ∈ nodes then q ++ [ask q x] else q) h := by
  induction m generalizing h with
  | zero => rfl
  | succ m ih =>
    simp only [List.range_succ_eq_map, List.foldl_cons, List.foldl_map, Function.comp_def]
    by_cases hh : h ∈ nodes
    · simpa only [runTree, if_pos hh] using ih (h ++ [ask h x])
    · have hf (l : List ℕ) : l.foldl (fun q _ => if q ∈ nodes then q ++ [ask q x] else q) h = h := by
        induction l with
        | nil => rfl
        | cons _ l ih' => simpa only [List.foldl_cons, if_neg hh] using ih'
      simp only [runTree, if_neg hh, hf]

private def descendants (nodes : Finset Hist) (h : Hist) : Finset Hist :=
  nodes.filter (fun q => h <+: q)

private lemma descendants_child (nodes : Finset Hist) (h : Hist) (b : Bool) :
    descendants nodes (h ++ [b]) ⊆ descendants nodes h := by
  intro q hq
  obtain ⟨hqN, hqp⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨hqN, (List.prefix_append _ _).trans hqp⟩

private lemma descendants_budget (nodes : Finset Hist) (h : Hist) (hh : h ∈ nodes) :
    (descendants nodes (h ++ [false])).card + (descendants nodes (h ++ [true])).card + 1 ≤
      (descendants nodes h).card := by
  let left := descendants nodes (h ++ [false])
  let right := descendants nodes (h ++ [true])
  have hd : Disjoint left right := by
    apply Finset.disjoint_left.mpr
    intro q hl hr
    obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hl).2
    obtain ⟨r, hr⟩ := (Finset.mem_filter.mp hr).2
    have he : h ++ (false :: l) = h ++ (true :: r) := by
      simpa only [List.append_assoc, List.singleton_append] using hl.trans hr.symm
    have hh' := List.append_cancel_left he
    simp at hh'
  have hnot : h ∉ left ∪ right := by
    intro H
    rcases Finset.mem_union.mp H with hL | hR
    · have := (Finset.mem_filter.mp hL).2.length_le
      simp at this
    · have := (Finset.mem_filter.mp hR).2.length_le
      simp at this
  have hsub : insert h (left ∪ right) ⊆ descendants nodes h := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_filter.mpr ⟨hh, List.prefix_rfl⟩
    · rcases Finset.mem_union.mp hq with hl | hr
      · exact descendants_child nodes h false hl
      · exact descendants_child nodes h true hr
  have hcard := Finset.card_le_card hsub
  rwa [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hd] at hcard

private lemma tree_accounting {A : Type*} [DecidableEq A] (nodes : Finset Hist)
    (ask : Hist → A → Bool) (value : Hist → A → ℕ) (good : ℕ → Finset A → Prop)
    (b gain : ℕ → ℕ) (r : ℕ)
    (hstep : ∀ p < r, b p + gain p = 2 * b (p + 1))
    (hleaf : ∀ p P, good p P → ∀ h, ∑ x ∈ P, value h x ≤ b p)
    (hsat : ∀ p P, r ≤ p → good p P → ∀ choice : A → Hist,
      ∑ x ∈ P, value (choice x) x ≤ b p)
    (hbranch : ∀ p P, good p P → ∀ h,
      (∃ bit : Bool, ∀ x ∈ P, ask h x = bit) ∨
      (good (p+1) (P.filter (fun x => ask h x = false)) ∧
        good (p+1) (P.filter (fun x => ask h x = true)))) :
    ∀ (m p : ℕ) (h : Hist) (P : Finset A), good p P →
      ∃ count : ℕ → ℕ,
        (∀ i, i < p → count i = 0) ∧
        (∀ i, count i ≤ 2 ^ (i - p)) ∧
        (∑ i ∈ Finset.range r, count i ≤ (descendants nodes h).card) ∧
        (∑ x ∈ P, value (runTree nodes ask x m h) x ≤
          b p + ∑ i ∈ Finset.range r, count i * gain i) := by
  intro m
  induction m with
  | zero =>
    intro p h P hgood
    refine ⟨fun _ => 0, by simp, by simp, by simp, ?_⟩
    simpa [runTree] using hleaf p P hgood h
  | succ m ih =>
    intro p h P hgood
    by_cases hsat' : r ≤ p
    · refine ⟨fun _ => 0, by simp, by simp, by simp, ?_⟩
      simpa using hsat p P hsat' hgood (fun x => runTree nodes ask x (m+1) h)
    by_cases hnode : h ∈ nodes
    · rcases hbranch p P hgood h with ⟨bit, hbit⟩ | ⟨hfalse, htrue⟩
      · rcases ih p (h++[bit]) P hgood with ⟨c, hcz, hcp, hcb, hcv⟩
        refine ⟨c, hcz, hcp, hcb.trans (Finset.card_le_card (descendants_child nodes h bit)), ?_⟩
        convert hcv using 1
        apply Finset.sum_congr rfl
        intro x hx
        simp [runTree, hnode, hbit x hx]
      · let P0 := P.filter (fun x => ask h x = false)
        let P1 := P.filter (fun x => ask h x = true)
        rcases ih (p+1) (h++[false]) P0 hfalse with ⟨c0,h0z,h0p,h0b,h0v⟩
        rcases ih (p+1) (h++[true]) P1 htrue with ⟨c1,h1z,h1p,h1b,h1v⟩
        let c (i : ℕ) := (if i = p then 1 else 0) + (c0 i + c1 i)
        have htotal (f : ℕ → ℕ) :
            (∑ i ∈ Finset.range r, c i * f i) =
              f p + ((∑ i ∈ Finset.range r, c0 i * f i) + (∑ i ∈ Finset.range r, c1 i * f i)) := by
          simp only [c, Nat.add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
          rw [Finset.sum_ite_eq' _ _ (fun i => f i)]
          simp [show p < r by omega]
        refine ⟨c, ?_, ?_, ?_, ?_⟩
        · intro i hi
          simp [c, show i ≠ p by omega, h0z i (by omega), h1z i (by omega)]
        · intro i
          rcases lt_trichotomy i p with hl | he | hg
          · simp [c, hl.ne, h0z i (by omega), h1z i (by omega)]
          · subst i
            simp [c, h0z p (by omega), h1z p (by omega)]
          · have heq : i - p = (i - (p+1)) + 1 := by omega
            simp only [c, hg.ne', if_false, zero_add, heq, pow_succ]
            have := h0p i
            have := h1p i
            omega
        · have he := htotal (fun _ => 1)
          simp only [mul_one] at he
          rw [he]
          have hbud := descendants_budget nodes h hnode
          omega
        · have hdis : Disjoint P0 P1 := by
            apply Finset.disjoint_left.mpr
            intro x hx0 hx1
            exact Bool.false_ne_true ((Finset.mem_filter.mp hx0).2.symm.trans
              (Finset.mem_filter.mp hx1).2)
          have hparts : P0 ∪ P1 = P := by
            ext x
            cases hx : ask h x <;> simp [P0, P1, hx]
          have hsum :
              (∑ x ∈ P, value (runTree nodes ask x (m+1) h) x) =
                (∑ x ∈ P0, value (runTree nodes ask x m (h++[false])) x) +
                (∑ x ∈ P1, value (runTree nodes ask x m (h++[true])) x) := by
            rw [← hparts, Finset.sum_union hdis]
            congr 1 <;> apply Finset.sum_congr rfl <;> intro x hx
            · simp [runTree, hnode, (Finset.mem_filter.mp hx).2]
            · simp [runTree, hnode, (Finset.mem_filter.mp hx).2]
          rw [htotal gain, hsum]
          have hs := hstep p (by omega)
          omega
    · refine ⟨fun _ => 0, by simp, by simp, by simp, ?_⟩
      simpa [runTree, hnode] using hleaf p P hgood h

open Polynomial

abbrev Z := Polynomial ℕ

private noncomputable def weight : Z := 1 + X

private noncomputable def transfer (v : Z × Z) : Z × Z :=
  ((v.1 + v.2) * weight, v.1 * weight + v.2)

private noncomputable def transferIter : ℕ → (Z × Z) → (Z × Z)
  | 0, v => v
  | n + 1, v => transfer (transferIter n v)

private lemma transferIter_succ_left (n : ℕ) (v : Z × Z) :
    transferIter (n + 1) v = transferIter n (transfer v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change transfer (transferIter (n + 1) v) =
      transfer (transferIter n (transfer v))
    rw [ih]

private lemma transferIter_add (a b : ℕ) (v : Z × Z) :
    transferIter (a + b) v = transferIter b (transferIter a v) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    change transfer (transferIter (a + b) v) = transfer (transferIter b (transferIter a v))
    rw [ih]

private lemma transferIter_eq_foldl (n : ℕ) (v : Z × Z) :
    transferIter n v = (List.range n).foldl (fun u _ => transfer u) v := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [transferIter, List.range_succ, List.foldl_append, ih]; rfl

private noncomputable def dot (v u : Z × Z) : Z := v.1 * u.1 + v.2 * u.2

private lemma transfer_dot (v u : Z × Z) : dot (transfer v) u = dot v (transfer u) := by
  unfold dot transfer
  ring

private lemma transferIter_dot (n : ℕ) (v u : Z × Z) :
    dot (transferIter n v) u = dot v (transferIter n u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    rw [show transferIter (n + 1) v = transfer (transferIter n v) from rfl,
      transfer_dot, ih, transferIter_succ_left]

private noncomputable def endpoint (n : ℕ) := transferIter n (1, 1)

private noncomputable def pathZ (n : ℕ) : Z := (endpoint n).1 + (endpoint n).2

private noncomputable def gap : ℕ → Z
  | 0 => 0
  | n + 1 => X * (endpoint n).2

private lemma endpoint_gap (n : ℕ) : (endpoint n).1 = (endpoint n).2 + gap n := by
  cases n with
  | zero => simp [endpoint, transferIter, gap]
  | succ n =>
    change ((endpoint n).1 + (endpoint n).2) * weight =
      (endpoint n).1 * weight + (endpoint n).2 + X * (endpoint n).2
    unfold weight
    ring

private lemma path_dot (a b : ℕ) : pathZ (a + b) = dot (endpoint a) (endpoint b) := by
  calc
    pathZ (a + b) = dot (transferIter b (endpoint a)) (1, 1) := by
      simp [pathZ, endpoint, dot, transferIter_add]
    _ = dot (endpoint a) (endpoint b) := transferIter_dot b (endpoint a) (1, 1)

private lemma path_fusion (a b : ℕ) :
    2 * pathZ (a + b) = pathZ a * pathZ b + gap a * gap b := by
  rw [path_dot]
  unfold pathZ dot
  rw [endpoint_gap a, endpoint_gap b]
  ring

private lemma path_split (n : ℕ) :
    2 * weight * pathZ n = pathZ (n + 1) + gap (n + 1) := by
  change 2 * weight * ((endpoint n).1 + (endpoint n).2) =
      ((endpoint n).1 + (endpoint n).2) * weight +
        ((endpoint n).1 * weight + (endpoint n).2) + X * (endpoint n).2
  unfold weight
  ring

private lemma coeff_mul_le_left {p q : Z} (r : Z) (h : ∀ n, p.coeff n ≤ q.coeff n) :
    ∀ n, (p * r).coeff n ≤ (q * r).coeff n := by
  intro n
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  exact Finset.sum_le_sum (fun ab _ => Nat.mul_le_mul_right _ (h ab.1))

private lemma path_fusion_coeff (a b j : ℕ) :
    (pathZ a * pathZ b).coeff j ≤ (2 * pathZ (a + b)).coeff j := by
  rw [path_fusion, coeff_add]
  exact Nat.le_add_right _ _

private lemma path_split_coeff (n j : ℕ) :
    (pathZ (n + 1)).coeff j ≤ (2 * weight * pathZ n).coeff j := by
  rw [path_split, coeff_add]
  exact Nat.le_add_right _ _

private abbrev Poly := Polynomial ℕ

private def coeffLE (p q : Poly) : Prop := ∀ j, p.coeff j ≤ q.coeff j

private lemma cle_mul {p q : Poly} (h : coeffLE p q) (r : Poly) :
    coeffLE (r * p) (r * q) := by
  intro j
  simp only [Polynomial.coeff_mul]
  exact Finset.sum_le_sum (fun ab _ => Nat.mul_le_mul_left _ (h ab.2))

private lemma cle_trans {p q r : Poly} (h : coeffLE p q) (u : coeffLE q r) : coeffLE p r :=
  fun j => (h j).trans (u j)

private def runEdges : List ℕ → List ℕ
  | [] => []
  | 0 :: rs => runEdges rs
  | (n + 1) :: rs => n :: runEdges rs

private lemma runEdges_le (rs : List ℕ) : (runEdges rs).length ≤ rs.length := by
  induction rs with
  | nil => simp [runEdges]
  | cons a rs ih => cases a <;> simp only [runEdges, List.length_cons] <;> omega

private lemma runEdges_count (rs : List ℕ) : (runEdges rs).sum + (runEdges rs).length = rs.sum := by
  induction rs with
  | nil => simp [runEdges]
  | cons a rs ih =>
    cases a <;> simp only [runEdges, List.sum_cons, List.length_cons] <;> omega

private noncomputable def runWeight (w : Poly) (P : ℕ → Poly) : ℕ → Poly
  | 0 => w
  | n + 1 => w ^ 2 * P n

private lemma runProduct (w : Poly) (P : ℕ → Poly) (rs : List ℕ) :
    (rs.map (runWeight w P)).prod =
      w ^ (rs.length + (runEdges rs).length) * ((runEdges rs).map P).prod := by
  induction rs with
  | nil => simp [runEdges]
  | cons a rs ih =>
    cases a with
    | zero =>
      simp only [List.map_cons, List.prod_cons, runWeight, ih, List.length_cons, runEdges]
      have h : rs.length + 1 + (runEdges rs).length =
          1 + (rs.length + (runEdges rs).length) := by omega
      rw [h, pow_add w 1 (rs.length + (runEdges rs).length), pow_one, mul_assoc]
    | succ a =>
      simp only [List.map_cons, List.prod_cons, runWeight, ih, List.length_cons, runEdges]
      have h : rs.length + 1 + ((runEdges rs).length + 1) =
          2 + (rs.length + (runEdges rs).length) := by omega
      rw [h, pow_add w 2 (rs.length + (runEdges rs).length)]
      ac_rfl

private lemma pathProduct_bound (P : ℕ → Poly)
    (fusion : ∀ a b, coeffLE (P a * P b) (2 * P (a + b))) (a : ℕ) (rs : List ℕ) :
    coeffLE (((a :: rs).map P).prod) (2 ^ rs.length * P (a + rs.sum)) := by
  induction rs generalizing a with
  | nil => simp [coeffLE]
  | cons b rs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons, List.sum_cons]
    apply cle_trans (cle_mul (ih b) (P a))
    conv_lhs => rw [← mul_assoc, mul_comm (P a), mul_assoc]
    rw [pow_succ, mul_assoc]
    exact cle_mul (fusion a (b + rs.sum)) (2 ^ rs.length)

private noncomputable def packed (w : Poly) (P : ℕ → Poly) (p q n : ℕ) : Poly :=
  2 ^ q * w ^ (p + q + 1) * P n

private lemma packed_move (w : Poly) (P : ℕ → Poly)
    (split : ∀ n, coeffLE (P (n + 1)) (2 * w * P n)) (p q n t : ℕ) :
    coeffLE (packed w P p q (n + t)) (packed w P p (q + t) n) := by
  have step (q m : ℕ) : coeffLE (packed w P p q (m + 1)) (packed w P p (q + 1) m) := by
    have he : packed w P p (q + 1) m = (2 ^ q * w ^ (p + q + 1)) * (2 * w * P m) := by
      unfold packed
      rw [show p + (q + 1) + 1 = (p + q + 1) + 1 by omega, pow_succ 2, pow_succ w]
      ac_rfl
    rw [he]
    exact cle_mul (split m) _
  induction t generalizing q with
  | zero => exact fun _ => Nat.le_refl _
  | succ t ih =>
    rw [show q + (t + 1) = (q + 1) + t by omega]
    exact cle_trans (step q (n + t)) (ih (q + 1))

private lemma runs_concentrate (w : Poly) (P : ℕ → Poly)
    (fusion : ∀ a b, coeffLE (P a * P b) (2 * P (a + b)))
    (split : ∀ n, coeffLE (P (n + 1)) (2 * w * P n))
    (rs : List ℕ) (hp : 0 < rs.sum) :
    let p := rs.length
    let r := min p rs.sum
    coeffLE ((rs.map (runWeight w P)).prod) (packed w P p (r - 1) (rs.sum - r)) := by
  dsimp only
  have hn := runEdges_count rs
  have hl := runEdges_le rs
  cases he : runEdges rs with
  | nil => simp [he] at hn; omega
  | cons a tail =>
    rw [he, List.sum_cons, List.length_cons] at hn
    rw [he, List.length_cons] at hl
    rw [runProduct, he, List.length_cons]
    have hr : tail.length + 1 ≤ min rs.length rs.sum := by omega
    have h₁ : coeffLE (w ^ (rs.length + (tail.length + 1)) * ((a :: tail).map P).prod)
        (packed w P rs.length tail.length (a + tail.sum)) := by
      have h := cle_mul (pathProduct_bound P fusion a tail) (w ^ (rs.length + (tail.length + 1)))
      unfold packed
      rw [show rs.length + tail.length + 1 = rs.length + (tail.length + 1) by omega]
      conv_rhs at h => rw [← mul_assoc, mul_comm (w ^ (rs.length + (tail.length + 1)))]
      exact h
    apply cle_trans h₁
    have h₂ := packed_move w P split rs.length tail.length (rs.sum - min rs.length rs.sum)
      (min rs.length rs.sum - (tail.length + 1))
    rwa [show tail.length + (min rs.length rs.sum - (tail.length + 1)) =
        min rs.length rs.sum - 1 by omega,
      show rs.sum - min rs.length rs.sum + (min rs.length rs.sum - (tail.length + 1)) =
        a + tail.sum by omega] at h₂

open Finset Polynomial

private noncomputable def maskEdge (a b : Bool) : Z :=
  if a && b then 1 else weight

private noncomputable def maskPath : List Bool → Bool → Bool → Z
  | [], a, b => maskEdge a b
  | m :: ms, a, b => maskEdge a false * maskPath ms false b +
      if m then maskEdge a true * maskPath ms true b else 0

private noncomputable def maskPathEdges {n : ℕ} (a b : Bool) (x : Fin n → Bool) : Z :=
  ∏ i : Fin (n + 1), maskEdge (Fin.cons (α := fun _ => Bool) a x i)
    (Fin.snoc (α := fun _ => Bool) x b i)

private lemma maskPathEdges_cons {n : ℕ} (a b c : Bool) (x : Fin n → Bool) :
    maskPathEdges a b (Fin.cons c x) = maskEdge a c * maskPathEdges c b x := by
  rw [maskPathEdges, Fin.prod_univ_succ, ← Fin.cons_snoc_eq_snoc_cons]
  simp only [Fin.cons_zero, Fin.cons_succ, maskPathEdges]

private lemma maskPath_sum {n : ℕ} (m : Fin n → Bool) (a b : Bool) :
    (∑ x : Fin n → Bool, if ∀ i, x i = true → m i = true then maskPathEdges a b x else 0) =
      maskPath (List.ofFn m) a b := by
  induction n generalizing a b with
  | zero =>
    have hz (x : Fin 0 → Bool) : maskPathEdges a b x = maskEdge a b := by
      rw [maskPathEdges, Fin.prod_univ_one, Fin.cons_zero]
      change maskEdge a (Fin.snoc (α := fun _ => Bool) x b (Fin.last 0)) = _
      rw [Fin.snoc_last]
    simp [hz, maskPath]
  | succ n ih =>
    let e := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
    rw [← e.sum_comp, Fintype.sum_prod_type, List.ofFn_succ]
    simp only [e, Fin.consEquiv_apply, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      maskPathEdges_cons]
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, false_implies, true_and]
    have aux (c : Bool) :
        (∑ x : Fin n → Bool, if ∀ i, x i = true → m i.succ = true then
          maskEdge a c * maskPathEdges c b x else 0) =
          maskEdge a c * maskPath (List.ofFn fun i : Fin n => m i.succ) c b := by
      rw [← ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp
    by_cases hm : m 0 = true <;> simp [hm, aux, maskPath, add_comm]

private lemma maskPath_cut (u v : List Bool) (a b : Bool) :
    maskPath (u ++ false :: v) a b = maskPath u a false * maskPath v false b := by
  induction u generalizing a with
  | nil => simp [maskPath]
  | cons m u ih =>
    cases m <;> simp [maskPath, ih, add_mul, mul_assoc]

private noncomputable def maskCycle {k : ℕ} [NeZero k] (m : Fin k → Bool) : Z :=
  ∑ x : Fin k → Bool, if ∀ i, x i = true → m i = true then
    ∏ i : Fin k, maskEdge (x i) (x (i + 1)) else 0

private lemma maskCycle_path {n : ℕ} (m : Fin (n + 1) → Bool) :
    maskCycle m = maskPath (List.ofFn fun i : Fin n => m i.succ) false false +
      if m 0 then maskPath (List.ofFn fun i : Fin n => m i.succ) true true else 0 := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => Bool)
  rw [maskCycle, ← e.sum_comp, Fintype.sum_prod_type]
  have he (a : Bool) (x : Fin n → Bool) :
      (∏ i : Fin (n + 1), maskEdge (Fin.cons (α := fun _ => Bool) a x i)
        (Fin.cons (α := fun _ => Bool) a x (i + 1))) =
        maskPathEdges a a x := by
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last, Fin.last_add_one, Fin.cons_zero]
    · have hj : j.castSucc + 1 = j.succ := by
        apply Fin.ext
        simp
      rw [Fin.snoc_castSucc, hj, Fin.cons_succ]
  simp only [e, Fin.consEquiv_apply, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, he]
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, false_implies, true_and]
  rw [maskPath_sum, add_comm]
  cases m 0 <;> simp [maskPath_sum]

private lemma maskCycle_rotate {k : ℕ} [NeZero k] (m : Fin k → Bool) (a : Fin k) :
    maskCycle (fun i => m (i + a)) = maskCycle m := by
  let e := Equiv.addRight a
  let E := Equiv.arrowCongr e.symm (Equiv.refl Bool)
  rw [maskCycle, maskCycle, ← E.sum_comp]
  apply Finset.sum_congr rfl
  intro x hx
  have hp : (∀ i, E x i = true → m (i + a) = true) ↔ (∀ i, x i = true → m i = true) := by
    change (∀ i, x (e i) = true → m (e i) = true) ↔ _
    exact e.forall_congr_right (q := fun i => x i = true → m i = true)
  by_cases h : ∀ i, E x i = true → m (i + a) = true
  · rw [ite_eq_left h, ite_eq_left (hp.mp h)]
    conv_rhs => rw [← Equiv.prod_comp e (fun i => maskEdge (x i) (x (i + 1)))]
    apply Finset.prod_congr rfl
    intro i hi
    change maskEdge (x (i + a)) (x ((i + 1) + a)) = maskEdge (x (i + a)) (x ((i + a) + 1))
    rw [show (i + 1) + a = (i + a) + 1 by ac_rfl]
  · rw [ite_eq_right h, ite_eq_right (mt hp.mpr h)]

open Finset Polynomial

private lemma maskPath_free (t : ℕ) (b : Bool) :
    (maskPath (List.replicate t true) false b, maskPath (List.replicate t true) true b) =
      transferIter t (maskEdge false b, maskEdge true b) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [show transferIter (t + 1) (maskEdge false b, maskEdge true b) =
      transfer (transferIter t (maskEdge false b, maskEdge true b)) from rfl, ← ih]
    simp only [List.replicate_succ, maskPath, ite_true, transfer, maskEdge,
      Bool.false_and, Bool.true_and, Bool.false_eq_true, ite_false, one_mul]
    congr 1 <;> ring

private lemma maskTransfer_scale (t : ℕ) (v : Z × Z) (c : Z) :
    transferIter t (c * v.1, c * v.2) =
      (c * (transferIter t v).1, c * (transferIter t v).2) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change transfer (transferIter t (c * v.1, c * v.2)) =
      (c * (transfer (transferIter t v)).1, c * (transfer (transferIter t v)).2)
    rw [ih]
    unfold transfer
    congr 1 <;> ring

private lemma maskPath_run (t : ℕ) :
    maskPath (List.replicate t true) false false = runWeight weight pathZ t := by
  cases t with
  | zero => rfl
  | succ t =>
    have hh := congrArg Prod.fst (maskPath_free (t + 1) false)
    change maskPath (List.replicate (t + 1) true) false false =
      (transfer (transferIter t (weight, weight))).1 at hh
    have hsc := maskTransfer_scale t ((1, 1) : Z × Z) weight
    simp only [mul_one] at hsc
    rw [hh, hsc]
    simp only [transfer, runWeight, pathZ, endpoint]
    ring

private lemma maskPath_cycle_free (t : ℕ) :
    maskCycle (fun _ : Fin (t + 1) => true) =
      (transferIter (t + 1) (1, 0)).1 + (transferIter (t + 1) (0, 1)).2 := by
  have h0 : transfer (1, 0) = (maskEdge false false, maskEdge true false) := by
    simp [transfer, maskEdge]
  have h1 : transfer (0, 1) = (maskEdge false true, maskEdge true true) := by
    simp [transfer, maskEdge]
  rw [maskCycle_path, transferIter_succ_left, transferIter_succ_left, h0, h1]
  simp only [List.ofFn_const, ite_true]
  rw [← maskPath_free, ← maskPath_free]

private def maskRunTail : List ℕ → List Bool
  | [] => []
  | r :: rs => false :: (List.replicate r true ++ maskRunTail rs)

private lemma maskRun_exists (ms : List Bool) :
    ∃ r rs, ms = List.replicate r true ++ maskRunTail rs := by
  induction ms with
  | nil => exact ⟨0, [], rfl⟩
  | cons m ms ih =>
    obtain ⟨r, rs, rfl⟩ := ih
    cases m
    · exact ⟨0, r :: rs, rfl⟩
    · exact ⟨r + 1, rs, rfl⟩

private lemma maskRunTail_length (rs : List ℕ) :
    (maskRunTail rs).length = rs.sum + rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [maskRunTail, ih]; omega

private lemma maskRunTail_count (rs : List ℕ) : (maskRunTail rs).count true = rs.sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [maskRunTail, ih, List.count_append]

private lemma maskRun_factor (r : ℕ) (rs : List ℕ) :
    maskPath (List.replicate r true ++ maskRunTail rs) false false =
      ((r :: rs).map (runWeight weight pathZ)).prod := by
  induction rs generalizing r with
  | nil => simp [maskRunTail, maskPath_run]
  | cons t ts ih => simp [maskRunTail, maskPath_cut, maskPath_run, ih]

private lemma maskRun_all_zero (rs : List ℕ) (h : rs.sum = 0) :
    (rs.map (runWeight weight pathZ)).prod = weight ^ rs.length := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    have hr : r = 0 := by simp only [List.sum_cons] at h; omega
    have hs : rs.sum = 0 := by simp [hr] at h; exact h
    simp [hr, ih hs, runWeight, pow_succ']

private noncomputable def maskB (k p : ℕ) : Z :=
  if p = 0 then (transferIter k (1, 0)).1 + (transferIter k (0, 1)).2
  else if 2 * p < k then (2 : Z) ^ (p - 1) * weight ^ (2 * p) * pathZ (k - 2 * p)
  else (2 : Z) ^ (k - p) * weight ^ k

private lemma maskB_runs (k : ℕ) (rs : List ℕ) (hp : 0 < rs.length)
    (hk : k = rs.length + rs.sum) :
    coeffLE ((rs.map (runWeight weight pathZ)).prod) (maskB k rs.length) := by
  by_cases hn : rs.sum = 0
  · rw [maskRun_all_zero rs hn]
    have hkr : k = rs.length := by omega
    simp [maskB, hp.ne', hkr, show ¬ (2 * rs.length < rs.length) by omega, coeffLE]
  have hh := runs_concentrate weight pathZ path_fusion_coeff path_split_coeff rs (by omega)
  dsimp only at hh
  by_cases hl : 2 * rs.length < k
  · have hm : min rs.length rs.sum = rs.length := by omega
    simpa [maskB, hp.ne', hl, hm, packed, show rs.length + (rs.length - 1) + 1 =
      2 * rs.length by omega, show k - 2 * rs.length = rs.sum - rs.length by omega] using hh
  · have hm : min rs.length rs.sum = rs.sum := by omega
    have hw : pathZ 0 = (2 : Z) := by norm_num [pathZ, endpoint, transferIter]
    rw [hm, Nat.sub_self, packed, hw, show rs.length + (rs.sum - 1) + 1 = k by omega,
      mul_comm ((2 : Z) ^ (rs.sum - 1)) (weight ^ k), mul_assoc, ← pow_succ,
      show rs.sum - 1 + 1 = k - rs.length by omega, mul_comm] at hh
    simpa [maskB, hp.ne', hl] using hh

open Finset Polynomial

private lemma maskCount {n : ℕ} (m : Fin n → Bool) :
    (List.ofFn m).count true = ∑ i, if m i = true then (1 : ℕ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ, List.count_cons, ih]
    cases m 0 <;> simp [Nat.add_comm]

private noncomputable def idealMasked {k : ℕ} [NeZero k] (S : Finset (Fin k)) : Z :=
  maskCycle (fun i => decide (i ∈ S))

private lemma idealMasked_def {k : ℕ} [NeZero k] (S : Finset (Fin k)) :
    idealMasked S = ∑ x ∈ (Finset.univ : Finset (Fin k → Bool)).filter
      (fun x => ∀ i, x i = true → i ∈ S), ∏ i : Fin k, maskEdge (x i) (x (i + 1)) := by
  rw [Finset.sum_filter]
  simp [idealMasked, maskCycle]

private lemma maskSucc_val {k : ℕ} [NeZero k] (i : Fin k) :
    (i + 1).val = (i.val + 1) % k := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

private lemma idealMasked_coeff {k : ℕ} [NeZero k] (S : Finset (Fin k)) (j : ℕ) :
    (idealMasked S).coeff j =
      ∑ x ∈ (Finset.univ : Finset (Fin k → Bool)).filter (fun x => ∀ i, x i = true → i ∈ S),
        ((Finset.univ : Finset (Fin k)).filter (fun i =>
          ¬ (x i = true ∧ x (i + 1) = true))).card.choose j := by
  rw [idealMasked_def, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro x hx
  have hprod : (∏ i : Fin k, maskEdge (x i) (x (i + 1))) =
      weight ^ ((Finset.univ : Finset (Fin k)).filter (fun i =>
          ¬ (x i = true ∧ x (i + 1) = true))).card := by
    rw [← Finset.prod_const, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases x i <;> cases x (i + 1) <;> simp [maskEdge]
  rw [hprod]
  simp [weight, coeff_one_add_X_pow]

private lemma maskCycle_bound {n : ℕ} (m : Fin (n + 1) → Bool) :
    coeffLE (maskCycle m) (maskB (n + 1) ((n + 1) - ∑ i, if m i = true then (1 : ℕ) else 0)) := by
  by_cases h : ∀ i, m i = true
  · have hm : m = fun _ => true := funext h
    rw [hm, maskPath_cycle_free]
    simp [maskB, coeffLE]
  push Not at h
  obtain ⟨a, ha⟩ := h
  let m' : Fin (n + 1) → Bool := fun i => m (i + a)
  have hm' : m' 0 = false := by simpa [m'] using ha
  have hrot : (∑ i, if m' i = true then (1 : ℕ) else 0) = ∑ i, if m i = true then (1 : ℕ) else 0 :=
    Equiv.sum_comp (Equiv.addRight a) (fun i => if m i = true then 1 else 0)
  rw [← maskCycle_rotate m a, ← hrot]
  change coeffLE (maskCycle m') _
  rw [maskCycle_path, Fin.sum_univ_succ, hm']
  simp only [Bool.false_eq_true, ite_false, add_zero, zero_add]
  let ms := List.ofFn (fun i : Fin n => m' i.succ)
  obtain ⟨r, rs, hr⟩ := maskRun_exists ms
  change coeffLE (maskPath ms false false) (maskB (n + 1)
    (n + 1 - ∑ i : Fin n, if m' i.succ = true then (1 : ℕ) else 0))
  have hcount := maskCount (fun i : Fin n => m' i.succ)
  change ms.count true = _ at hcount
  rw [hr, List.count_append, List.count_replicate, maskRunTail_count] at hcount
  simp only [beq_self_eq_true, ite_true] at hcount
  have hlen : ms.length = n := List.length_ofFn
  rw [hr, List.length_append, List.length_replicate, maskRunTail_length] at hlen
  rw [hr, maskRun_factor, ← hcount]
  have hp : n + 1 - (r + rs.sum) = (r :: rs).length := by simp; omega
  rw [hp]
  apply maskB_runs
  · simp
  · simp; omega

private lemma idealMasked_bound {n : ℕ} (S : Finset (Fin (n + 1))) :
    coeffLE (idealMasked S) (maskB (n + 1) (n + 1 - S.card)) := by
  have h := maskCycle_bound (fun i => decide (i ∈ S))
  simpa [idealMasked, ← Finset.sum_filter] using h

private def canonicalFree (k p : ℕ) : Finset (Fin k) :=
  Finset.univ.filter fun i => ¬ (i.val % 2 = 0 ∧ i.val < 2 * p)

private def canonicalTail : ℕ → ℕ → List Bool
  | 0, r => List.replicate r true
  | q + 1, r => true :: false :: canonicalTail q r

private lemma canonicalTail_indices (q r n : ℕ) (hn : n = 2 * q + r) :
    (List.ofFn fun i : Fin n => decide (¬ (i.val % 2 = 1 ∧ i.val < 2 * q))) =
      canonicalTail q r := by
  induction q generalizing n with
  | zero =>
    obtain rfl : n = r := by omega
    simp [canonicalTail]
  | succ q ih =>
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 + 1 := ⟨n - 2, by omega⟩
    rw [List.ofFn_succ, List.ofFn_succ, canonicalTail]
    have he : (fun i : Fin t => decide (¬ (i.succ.succ.val % 2 = 1 ∧ i.succ.succ.val < 2 * (q + 1)))) =
        fun i : Fin t => decide (¬ (i.val % 2 = 1 ∧ i.val < 2 * q)) := by
      funext i
      simp only [Fin.val_succ, decide_eq_decide]
      omega
    rw [he, ih t (by omega)]
    simp [show 1 < 2 * (q + 1) by omega]

private lemma canonicalTail_factor (q r : ℕ) :
    maskPath (canonicalTail q r) false false =
      (2 : Z) ^ q * weight ^ (2 * q) * runWeight weight pathZ r := by
  induction q with
  | zero => simp [canonicalTail, maskPath_run]
  | succ q ih =>
    change maskPath ([true] ++ false :: canonicalTail q r) false false = _
    rw [maskPath_cut, ih, show [true] = List.replicate 1 true from rfl, maskPath_run]
    simp only [runWeight, pathZ, endpoint, transferIter]
    rw [show 2 * (q + 1) = 2 * q + 2 by omega, pow_add, pow_succ (2 : Z)]
    ring

private lemma idealMasked_canonical {n p : ℕ} (hp : p ≤ (n + 2) / 2) :
    idealMasked (canonicalFree (n + 1) p) = maskB (n + 1) p := by
  cases p with
  | zero =>
    simp [idealMasked, canonicalFree, maskPath_cycle_free, maskB]
  | succ q =>
    let m : Fin (n + 1) → Bool := fun i => decide (i ∈ canonicalFree (n + 1) (q + 1))
    change maskCycle m = _
    have hm0 : m 0 = false := by simp [m, canonicalFree]
    rw [maskCycle_path, hm0]
    simp only [Bool.false_eq_true, ite_false, add_zero]
    have he : (fun i : Fin n => m i.succ) =
        fun i : Fin n => decide (¬ (i.val % 2 = 1 ∧ i.val < 2 * q)) := by
      funext i
      simp only [m, canonicalFree, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ,
        decide_eq_decide]
      omega
    rw [he, canonicalTail_indices q (n - 2 * q) n (by omega), canonicalTail_factor]
    by_cases hl : 2 * (q + 1) < n + 1
    · have hm : n - 2 * q = (n + 1 - 2 * (q + 1)) + 1 := by omega
      rw [hm]
      simp only [maskB, Nat.succ_ne_zero, ite_false, ite_eq_left hl, Nat.add_sub_cancel, runWeight]
      rw [show 2 * (q + 1) = 2 * q + 2 by omega, pow_add]
      ring
    · have hr : n - 2 * q = 0 ∨ n - 2 * q = 1 := by omega
      rcases hr with hr | hr
      · have hk : n + 1 = 2 * q + 1 := by omega
        have hf : n + 1 - (q + 1) = q := by omega
        rw [maskB, ite_eq_right (Nat.succ_ne_zero q), ite_eq_right hl, hr, runWeight, hf, hk,
          pow_succ, mul_assoc]
      · have hk : n + 1 = 2 * q + 2 := by omega
        have hf : n + 1 - (q + 1) = q + 1 := by omega
        rw [maskB, ite_eq_right (Nat.succ_ne_zero q), ite_eq_right hl, hr, runWeight, hf, hk]
        simp only [pathZ, endpoint, transferIter]
        rw [pow_add weight, pow_succ (2 : Z)]
        ring

private lemma canonicalFree_nested {k p q : ℕ} (hpq : p ≤ q) :
    canonicalFree k q ⊆ canonicalFree k p := by
  intro i
  simp only [canonicalFree, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

private lemma canonicalFree_pins (k p : ℕ) (hp : p ≤ (k + 1) / 2) :
    ((Finset.univ : Finset (Fin k)) \ canonicalFree k p) =
      Finset.univ.map ({
        toFun := fun i : Fin p => ⟨2 * i.val, by have := i.isLt; omega⟩
        inj' := by
          intro i j h
          apply Fin.ext
          have he := congrArg Fin.val h
          change 2 * i.val = 2 * j.val at he
          omega
      } : Fin p ↪ Fin k) := by
  ext i
  simp only [canonicalFree, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not, Finset.mem_map]
  constructor
  · intro h
    refine ⟨⟨i.val / 2, by omega⟩, Fin.ext ?_⟩
    change 2 * (i.val / 2) = i.val
    omega
  · rintro ⟨j, e⟩
    have hj : 2 * j.val = i.val := congrArg Fin.val e
    have hlt := j.isLt
    omega

private lemma canonicalFree_card (k p : ℕ) (hp : p ≤ (k + 1) / 2) :
    (canonicalFree k p).card = k - p := by
  have he : (((Finset.univ : Finset (Fin k)) \ canonicalFree k p)).card = p := by
    rw [canonicalFree_pins k p hp]
    simp
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (canonicalFree k p))
  simp only [he, Finset.card_univ, Fintype.card_fin] at hc
  omega

private lemma maskB_posted (k p : ℕ) :
    let w : Z := 1 + Polynomial.X
    let advance := fun (v : Z × Z) => ((v.1 + v.2) * w, v.1 * w + v.2)
    let walk := fun (n : ℕ) (v : Z × Z) => (List.range n).foldl (fun a _ => advance a) v
    let path := fun (n : ℕ) => let v := walk n (1, 1); v.1 + v.2
    let cycle := (walk k (1, 0)).1 + (walk k (0, 1)).2
    maskB k p = if p = 0 then cycle else if 2 * p < k then
      Polynomial.C (2 ^ (p - 1)) * w ^ (2 * p) * path (k - 2 * p)
      else Polynomial.C (2 ^ (k - p)) * w ^ k := by
  dsimp only
  have hc (n : ℕ) : Polynomial.C (2 ^ n : ℕ) = (2 : Z) ^ n := by
    rw [map_pow]
    norm_num
  rw [maskB]
  simp only [pathZ, endpoint, transferIter_eq_foldl, hc, weight, transfer]

private lemma idealMasked_bound_pos {k : ℕ} [NeZero k] (S : Finset (Fin k)) :
    coeffLE (idealMasked S) (maskB k (k - S.card)) := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact idealMasked_bound S

private lemma idealMasked_canonical_pos {k p : ℕ} [NeZero k] (hp : p ≤ (k + 1) / 2) :
    idealMasked (canonicalFree k p) = maskB k p := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact idealMasked_canonical hp

-- Index rotation identities adapted from L_meta_25736.lean at 4f56a4ca1e513be6cb3a251b5c6efe1c3516a3c4.
private def kernelIx {k : ℕ} (hk : 0 < k) (a : ℕ) : Fin k :=
  ⟨a % k, Nat.mod_lt a hk⟩

private lemma kernelIx_add {k : ℕ} (hk : 0 < k) (a b : ℕ) :
    kernelIx hk ((kernelIx hk a).val + b) = kernelIx hk (a + b) :=
  Fin.ext (Nat.mod_add_mod ..)

private lemma kernelIx_self {k : ℕ} (hk : 0 < k) (j : Fin k) :
    kernelIx hk j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)

private lemma kernelIx_forward_back {k : ℕ} (hk : 0 < k) (j : Fin k) (s : ℕ) :
    kernelIx hk ((kernelIx hk (j.val + s)).val + k - s % k) = j := by
  have hlt := Nat.mod_lt s hk
  have hdiv := Nat.mod_add_div s k
  have heq : j.val + s + (k - s % k) = j.val + ((s / k + 1) * k) := by
    rw [Nat.add_mul, one_mul, mul_comm (s / k) k]
    omega
  apply Fin.ext
  change (((j.val + s) % k + k - s % k) % k) = j.val
  rw [show (j.val + s) % k + k - s % k = (j.val + s) % k + (k - s % k) by omega,
    Nat.mod_add_mod, heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]

private lemma kernelIx_back_forward {k : ℕ} (hk : 0 < k) (j : Fin k) (s : ℕ) :
    kernelIx hk ((kernelIx hk (j.val + k - s % k)).val + s) = j := by
  have hlt := Nat.mod_lt s hk
  have hdiv := Nat.mod_add_div s k
  have heq : j.val + k - s % k + s = j.val + ((s / k + 1) * k) := by
    rw [Nat.add_mul, one_mul, mul_comm (s / k) k]
    omega
  apply Fin.ext
  change (((j.val + k - s % k) % k + s) % k) = j.val
  rw [Nat.mod_add_mod, heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]

private def kernelMixer {k : ℕ} (hk : 0 < k) (s : ℕ) :
    (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun x j := x j + x (kernelIx hk (j.val + s)) + x (kernelIx hk (j.val + k - s % k))
  map_add' _ _ := by funext j; dsimp only [Pi.add_apply]; ring
  map_smul' _ _ := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private lemma kernelMixer_mem {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Fin k → ZMod 2) :
    x ∈ (kernelMixer hk s).ker ↔
      ∀ j : Fin k, x j + x (kernelIx hk (j.val + s)) + x (kernelIx hk (j.val + 2 * s)) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j
    have hh := congrFun h (kernelIx hk (j.val + s))
    change x (kernelIx hk (j.val + s)) + x (kernelIx hk ((kernelIx hk (j.val + s)).val + s)) +
      x (kernelIx hk ((kernelIx hk (j.val + s)).val + k - s % k)) = 0 at hh
    rw [kernelIx_add, kernelIx_forward_back, show j.val + s + s = j.val + 2 * s by omega] at hh
    simpa only [add_comm, add_left_comm, add_assoc] using hh
  · intro h
    funext j
    let b := kernelIx hk (j.val + k - s % k)
    have hh := h b
    have hb : kernelIx hk (b.val + s) = j := kernelIx_back_forward hk j s
    have hb₂ : kernelIx hk (b.val + 2 * s) = kernelIx hk (j.val + s) := by
      rw [show b.val + 2 * s = b.val + s + s by omega, ← kernelIx_add, hb]
    rw [hb, hb₂] at hh
    change x j + x (kernelIx hk (j.val + s)) + x b = 0
    simpa only [add_comm, add_left_comm, add_assoc] using hh

private lemma kernelOrbit_injective {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Function.Injective (fun p : Fin (Nat.gcd k s) × Fin (k / Nat.gcd k s) =>
      kernelIx hk (p.1.val + p.2.val * s)) := by
  rintro ⟨r, i⟩ ⟨t, j⟩ h
  have hh : r.val + i.val * s ≡ t.val + j.val * s [MOD k] := congrArg Fin.val h
  have hr := hh.of_dvd (Nat.gcd_dvd_left k s)
  have hs : s ≡ 0 [MOD Nat.gcd k s] := Nat.modEq_zero_iff_dvd.mpr (Nat.gcd_dvd_right k s)
  have hr' : r.val ≡ t.val [MOD Nat.gcd k s] := by
    have hri : r.val + i.val * s ≡ r.val [MOD Nat.gcd k s] := by
      simpa using (hs.mul_left i.val).add_left r.val
    have htj : t.val + j.val * s ≡ t.val [MOD Nat.gcd k s] := by
      simpa using (hs.mul_left j.val).add_left t.val
    exact hri.symm.trans (hr.trans htj)
  have hrt : r = t := Fin.ext (hr'.eq_of_lt_of_lt r.isLt t.isLt)
  subst t
  have hij := (hh.add_left_cancel' r.val).cancel_right_div_gcd hk
  have hij' : i = j := Fin.ext (hij.eq_of_lt_of_lt i.isLt j.isLt)
  subst j
  rfl

private noncomputable def kernelOrbit {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Fin (Nat.gcd k s) × Fin (k / Nat.gcd k s) ≃ Fin k :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨kernelOrbit_injective hk s, by
      simp only [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm (Nat.gcd k s)]
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left k s)⟩)

private lemma kernelOrbit_nat {k : ℕ} (hk : 0 < k) (s : ℕ)
    (hn : 0 < k / Nat.gcd k s) (r : Fin (Nat.gcd k s)) (m : ℕ) :
    kernelOrbit hk s (r, kernelIx hn m) = kernelIx hk (r.val + m * s) := by
  let n := k / Nat.gcd k s
  have hmul : k ∣ n * s := by
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right k s
    refine ⟨t, ?_⟩
    rw [ht, ← Nat.mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left k s)]
  have hmod : (m % n) * s ≡ m * s [MOD k] :=
    ((Nat.mod_modEq m n).mul_right' s).of_dvd hmul
  apply Fin.ext
  change (r.val + (m % n) * s) % k = (r.val + m * s) % k
  exact hmod.add_left r.val

private lemma kernelMixer_cycles {k : ℕ} (hk : 0 < k) (s : ℕ)
    (hn : 0 < k / Nat.gcd k s) (x : Fin k → ZMod 2) :
    x ∈ (kernelMixer hk s).ker ↔
      ∀ (r : Fin (Nat.gcd k s)) (m : ℕ),
        x (kernelOrbit hk s (r, kernelIx hn m)) +
          x (kernelOrbit hk s (r, kernelIx hn (m + 1))) +
          x (kernelOrbit hk s (r, kernelIx hn (m + 2))) = 0 := by
  rw [kernelMixer_mem]
  have h₁ (r : Fin (Nat.gcd k s)) (m : ℕ) :
      kernelOrbit hk s (r, kernelIx hn (m + 1)) =
        kernelIx hk ((kernelOrbit hk s (r, kernelIx hn m)).val + s) := by
    rw [kernelOrbit_nat, kernelOrbit_nat, kernelIx_add]
    congr 1
    ring
  have h₂ (r : Fin (Nat.gcd k s)) (m : ℕ) :
      kernelOrbit hk s (r, kernelIx hn (m + 2)) =
        kernelIx hk ((kernelOrbit hk s (r, kernelIx hn m)).val + 2 * s) := by
    rw [kernelOrbit_nat, kernelOrbit_nat, kernelIx_add]
    congr 1
    ring
  constructor
  · intro h r m
    rw [h₁, h₂]
    exact h _
  · intro h j
    obtain ⟨⟨r, m⟩, rfl⟩ := (kernelOrbit hk s).surjective j
    specialize h r m.val
    rw [h₁, h₂, kernelIx_self] at h
    exact h

private lemma kernelBit_add_self (a : ZMod 2) : a + a = 0 := by
  have ha : a = 0 ∨ a = 1 := by
    rcases a with ⟨a, ha⟩
    interval_cases a
    · left; rfl
    · right; rfl
  rcases ha with rfl | rfl <;> decide

private def kernelPattern (v : ZMod 2 × ZMod 2) (m : ℕ) : ZMod 2 :=
  if m % 3 = 0 then v.1 else if m % 3 = 1 then v.2 else v.1 + v.2

private lemma kernelPattern_triple (v : ZMod 2 × ZMod 2) (m : ℕ) :
    kernelPattern v m + kernelPattern v (m + 1) + kernelPattern v (m + 2) = 0 := by
  have hz : v.1 + v.2 + (v.1 + v.2) = 0 := kernelBit_add_self _
  have h₁ : (m + 1) % 3 = (m % 3 + 1) % 3 := by omega
  have h₂ : (m + 2) % 3 = (m % 3 + 2) % 3 := by omega
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;>
    rw [hm] at h₁ h₂ <;>
    simp only [kernelPattern, hm, h₁, h₂] <;> norm_num <;>
    simpa only [add_comm, add_left_comm, add_assoc] using hz

private lemma kernelPattern_of_recurrence (f : ℕ → ZMod 2)
    (h : ∀ m, f m + f (m + 1) + f (m + 2) = 0) (m : ℕ) :
    f m = kernelPattern (f 0, f 1) m := by
  have hstep (a : ℕ) : f (a + 3) = f a := by
    have h₁ := h a
    have h₂ : f (a + 1) + f (a + 2) + f (a + 3) = 0 := h (a + 1)
    linear_combination h₂ - h₁
  have hmod : f m = f (m % 3) := by
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      by_cases hm : m < 3
      · rw [Nat.mod_eq_of_lt hm]
      calc
        f m = f (m - 3) := by
          have hEq : m - 3 + 3 = m := by omega
          simpa only [hEq] using hstep (m - 3)
        _ = f ((m - 3) % 3) := ih _ (by omega)
        _ = f (m % 3) := by congr 1; omega
  have htwo : f 2 = f 0 + f 1 := by
    have hzero : f 0 + f 1 + f 2 = 0 := h 0
    have hself := kernelBit_add_self (f 0 + f 1)
    linear_combination hzero - hself
  rw [hmod]
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm | hm <;> simp [kernelPattern, hm, htwo]

private lemma kernelPattern_zero_of_period (f : ℕ → ZMod 2) {n : ℕ}
    (h : ∀ m, f m + f (m + 1) + f (m + 2) = 0)
    (hp : ∀ m, f (n + m) = f m) (hn : ¬ 3 ∣ n) (m : ℕ) : f m = 0 := by
  have hn' : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have h₀ := (kernelPattern_of_recurrence f h (n + 0)).symm.trans (hp 0)
  have h₁ := (kernelPattern_of_recurrence f h (n + 1)).symm.trans (hp 1)
  have hab : f 0 = 0 ∧ f 1 = 0 := by
    rcases hn' with hn' | hn'
    · have hn₁ : (n + 1) % 3 = 2 := by omega
      simp [kernelPattern, hn'] at h₀
      simp [kernelPattern, hn₁] at h₁
      exact ⟨h₁, h₀.trans h₁⟩
    · have hn₁ : (n + 1) % 3 = 0 := by omega
      simp [kernelPattern, hn'] at h₀
      simp [kernelPattern, hn₁] at h₁
      exact ⟨h₁.trans h₀, h₀⟩
  rw [kernelPattern_of_recurrence f h m]
  simp [kernelPattern, hab.1, hab.2]

private theorem kernelMixer_card {k : ℕ} (hk : 0 < k) (s : ℕ) :
    Nat.card (kernelMixer hk s).ker = 2 ^ (if 3 ∣ k / Nat.gcd k s then 2 * Nat.gcd k s else 0) := by
  classical
  let g := Nat.gcd k s
  let n := k / g
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh : n * g = k := Nat.div_mul_cancel (Nat.gcd_dvd_left k s)
    rw [hz, zero_mul] at hh
    exact (Nat.ne_of_gt hk) hh.symm
  let e := kernelOrbit hk s
  by_cases h3 : 3 ∣ n
  · rw [ite_eq_left h3]
    let encode : (kernelMixer hk s).ker → (Fin g → ZMod 2 × ZMod 2) :=
      fun x r => (x.val (e (r, kernelIx hn 0)), x.val (e (r, kernelIx hn 1)))
    have value (x : (kernelMixer hk s).ker) (r : Fin g) (m : ℕ) :
        x.val (e (r, kernelIx hn m)) = kernelPattern (encode x r) m :=
      kernelPattern_of_recurrence _ ((kernelMixer_cycles hk s hn x.val).mp x.property r) m
    have hinj : Function.Injective encode := by
      intro x y hxy
      apply Subtype.ext
      funext j
      obtain ⟨⟨r, m⟩, rfl⟩ := e.surjective j
      rw [← kernelIx_self hn m, value, value, hxy]
    have hsurj : Function.Surjective encode := by
      intro v
      let x : Fin k → ZMod 2 := fun j => kernelPattern (v (e.symm j).1) (e.symm j).2.val
      have hx (r : Fin g) (m : ℕ) : x (e (r, kernelIx hn m)) = kernelPattern (v r) m := by
        dsimp only [x]
        rw [e.symm_apply_apply]
        change kernelPattern (v r) (m % n) = kernelPattern (v r) m
        have hm : (m % n) % 3 = m % 3 := (Nat.mod_modEq m n).of_dvd h3
        simp [kernelPattern, hm]
      have hxker : x ∈ (kernelMixer hk s).ker := by
        apply (kernelMixer_cycles hk s hn x).mpr
        intro r m
        rw [hx, hx, hx]
        exact kernelPattern_triple (v r) m
      refine ⟨⟨x, hxker⟩, ?_⟩
      funext r
      change (x (e (r, kernelIx hn 0)), x (e (r, kernelIx hn 1))) = v r
      rw [hx, hx]
      simp [kernelPattern]
    rw [Nat.card_congr (Equiv.ofBijective encode ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_prod, ZMod.card]
    rw [pow_mul]
    rfl
  · rw [ite_eq_right h3, pow_zero]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨0, ?_⟩
    intro x
    apply Subtype.ext
    funext j
    obtain ⟨⟨r, m⟩, rfl⟩ := e.surjective j
    rw [← kernelIx_self hn m]
    let f : ℕ → ZMod 2 := fun a => x.val (e (r, kernelIx hn a))
    have hf := (kernelMixer_cycles hk s hn x.val).mp x.property r
    have hp (a : ℕ) : f (n + a) = f a := by
      have hm : (n + a) % n = a % n := by simp
      exact congrArg (fun i => x.val (e (r, i))) (Fin.ext hm)
    exact kernelPattern_zero_of_period f hf hp h3 m.val

private abbrev MixerWord (k : ℕ) := Fin k → ZMod 2

private abbrev MixerTree (k : ℕ) :=
  Finset (List Bool) × (List Bool → MixerWord k →ₗ[ZMod 2] ZMod 2) ×
    (List Bool → ZMod 2) × (List Bool → MixerWord k →ₗ[ZMod 2] MixerWord k) ×
    (List Bool → MixerWord k)

private def mixerPredict {k : ℕ} (tr : MixerTree k) (x : MixerWord k) : MixerWord k :=
  let h := (List.range tr.1.card).foldl (fun p _ =>
    if p ∈ tr.1 then p ++ [decide (tr.2.1 p x + tr.2.2.1 p ≠ 0)] else p) []
  tr.2.2.2.1 h x + tr.2.2.2.2 h

private def mixerValue {k : ℕ} (f : MixerWord k → MixerWord k) (tr : MixerTree k)
    (j : ℕ) (x : MixerWord k) : ℕ :=
  Nat.choose ((Finset.univ : Finset (Fin k)).filter (fun i => mixerPredict tr x i = f x i)).card j

private def mixerPull {k : ℕ} (tr : MixerTree k)
    (A : MixerWord k →ₗ[ZMod 2] MixerWord k) (b : MixerWord k)
    (D : MixerWord k →ₗ[ZMod 2] MixerWord k) (d : MixerWord k) : MixerTree k :=
  (tr.1, fun h => (tr.2.1 h).comp A, fun h => tr.2.1 h b + tr.2.2.1 h,
    fun h => (tr.2.2.2.1 h).comp A + D, fun h => tr.2.2.2.1 h b + tr.2.2.2.2 h + d)

private lemma mixerPredict_pull {k : ℕ} (tr : MixerTree k)
    (A : MixerWord k →ₗ[ZMod 2] MixerWord k) (b : MixerWord k)
    (D : MixerWord k →ₗ[ZMod 2] MixerWord k) (d x : MixerWord k) :
    mixerPredict (mixerPull tr A b D d) x = mixerPredict tr (A x + b) + D x + d := by
  simp only [mixerPredict, mixerPull, LinearMap.add_apply, LinearMap.comp_apply, map_add, add_assoc]
  abel

private lemma mixerValue_pull {k : ℕ} (f g : MixerWord k → MixerWord k) (tr : MixerTree k)
    (A : MixerWord k →ₗ[ZMod 2] MixerWord k) (b : MixerWord k)
    (D : MixerWord k →ₗ[ZMod 2] MixerWord k) (d x : MixerWord k) (j : ℕ)
    (hg : g x = f (A x + b) + D x + d) :
    mixerValue g (mixerPull tr A b D d) j x = mixerValue f tr j (A x + b) := by
  simp [mixerValue, mixerPredict_pull, hg, Pi.add_apply]

private lemma mixer_splitting {k : ℕ} (L : MixerWord k →ₗ[ZMod 2] MixerWord k) :
    ∃ S : MixerWord k →ₗ[ZMod 2] MixerWord k, ∃ e : (LinearMap.ker L × LinearMap.range L) ≃ MixerWord k,
      (∀ u y, e (u,y) = S y + u) ∧ (∀ u y, L (e (u,y)) = y) := by
  obtain ⟨s, hs⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  have hs' (y : LinearMap.range L) : L (s y) = y :=
    congrArg Subtype.val (LinearMap.congr_fun hs y)
  obtain ⟨p, hp⟩ := (LinearMap.range L).subtype.exists_leftInverse_of_injective
    (LinearMap.range L).ker_subtype
  have hp' (y : LinearMap.range L) : p y = y := LinearMap.congr_fun hp y
  let e : (LinearMap.ker L × LinearMap.range L) ≃ MixerWord k :=
    { toFun := fun z => s z.2 + z.1
      invFun := fun x => (⟨x - s (L.rangeRestrict x), by
        rw [LinearMap.mem_ker, map_sub, hs']; exact sub_self (L x)⟩, L.rangeRestrict x)
      left_inv := by
        rintro ⟨u, y⟩
        have he : L.rangeRestrict (s y + u) = y := by
          apply Subtype.ext
          change L (s y + u) = y
          rw [map_add, hs', LinearMap.mem_ker.mp u.property, add_zero]
        apply Prod.ext
        · apply Subtype.ext
          dsimp only
          rw [he]
          abel
        · exact he
      right_inv := fun x => by dsimp; abel }
  refine ⟨s.comp p, e, ?_, ?_⟩
  · intro u y
    change s y + u = s (p y) + u
    rw [hp']
  · intro u y
    change L (s y + u) = y
    rw [map_add, hs', LinearMap.mem_ker.mp u.property, add_zero]

private def mixerQuad {k : ℕ} (a b : Fin k → Fin k) (x : MixerWord k) : MixerWord k :=
  fun i => x (a i) * x (b i)

private def mixerCross {k : ℕ} (a b : Fin k → Fin k) (c : MixerWord k) :
    MixerWord k →ₗ[ZMod 2] MixerWord k :=
  LinearMap.pi fun i => c (b i) • LinearMap.proj (a i) + c (a i) • LinearMap.proj (b i)

private lemma mixerQuad_translate {k : ℕ} (a b : Fin k → Fin k) (x c : MixerWord k) :
    mixerQuad a b (x + c) = mixerQuad a b x + mixerCross a b c x + mixerQuad a b c := by
  funext i
  simp [mixerQuad, mixerCross, Pi.add_apply]
  ring

private lemma mixer_transfer {k m B : ℕ} (a b : Fin k → Fin k)
    (L D : MixerWord k →ₗ[ZMod 2] MixerWord k) (d : MixerWord k) (T : ℕ → ℕ)
    (hm : Nat.card (LinearMap.ker L) = m)
    (hupper : ∀ tr : MixerTree k, tr.1.card < B → ∀ j,
      (∑ x, mixerValue (mixerQuad a b) tr j x) ≤ T j)
    (hlower : ∃ tr : MixerTree k, tr.1.card < B ∧ ∀ j,
      (∑ x, mixerValue (mixerQuad a b) tr j x) = T j) :
    let f := fun x => mixerQuad a b (L x) + D x + d
    (∀ tr : MixerTree k, tr.1.card < B → ∀ j, (∑ x, mixerValue f tr j x) ≤ m * T j) ∧
    ∃ fam : Fin m → MixerTree k, (∀ i, (fam i).1.card < B) ∧
      ∀ j, (∑ i, ∑ x, mixerValue f (fam i) j x) = m * T j := by
  classical
  let : Fintype (LinearMap.ker L) := Fintype.ofFinite _
  let : Fintype (LinearMap.range L) := Fintype.ofFinite _
  have hkm : Fintype.card (LinearMap.ker L) = m := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨S, e, he, hL⟩ := mixer_splitting L
  let q := mixerQuad a b
  let f := fun x => q (L x) + D x + d
  have hsum (v : MixerWord k → ℕ) : (∑ x, v x) = ∑ u : LinearMap.ker L,
      ∑ y : LinearMap.range L, v (e (u,y)) := by
    rw [← e.sum_comp v, Fintype.sum_prod_type]
  change (∀ tr : MixerTree k, tr.1.card < B → ∀ j, (∑ x, mixerValue f tr j x) ≤ m * T j) ∧ _
  constructor
  · intro tr ht j
    have hrhs : (∑ _ : LinearMap.ker L, T j) = m * T j := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hkm]
      rfl
    rw [hsum, ← hrhs]
    apply Finset.sum_le_sum
    intro u _
    let tr' := mixerPull tr S u (-(D.comp S)) (-(D u + d))
    have hpt (y : LinearMap.range L) : mixerValue f tr j (e (u, y)) = mixerValue q tr' j y := by
      symm
      have hg : q y = f (S y + u) + (-(D.comp S)) y + (-(D u + d)) := by
        have hy : L (S y + u) = y := by rw [← he u y, hL]
        simp only [f, hy, map_add, LinearMap.neg_apply, LinearMap.comp_apply]
        abel
      simpa only [tr', he] using mixerValue_pull f q tr S u (-(D.comp S)) (-(D u + d)) y j hg
    simp_rw [hpt]
    calc
      _ ≤ ∑ y, mixerValue q tr' j y := by
        let emb : LinearMap.range L ↪ MixerWord k := ⟨Subtype.val, Subtype.val_injective⟩
        calc
          _ = ∑ y ∈ Finset.univ.map emb, mixerValue q tr' j y :=
            (Finset.sum_map Finset.univ emb (mixerValue q tr' j)).symm
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (by intros; exact Nat.zero_le _)
      _ ≤ T j := hupper tr' ht j
  · obtain ⟨tr, ht, hs⟩ := hlower
    obtain ⟨C, hC⟩ := (LinearMap.range L).exists_isCompl
    let : Fintype C := Fintype.ofFinite _
    let E := (C.prodEquivOfIsCompl (LinearMap.range L) hC.symm).toEquiv
    have hcard : Fintype.card C = m := by
      have h1 := Fintype.card_congr e
      have h2 := Fintype.card_congr E
      rw [Fintype.card_prod, hkm] at h1
      rw [Fintype.card_prod, ← h1] at h2
      exact Nat.eq_of_mul_eq_mul_right (Fintype.card_pos_iff.mpr ⟨0⟩) h2
    let φ : Fin m ≃ C := (Fintype.equivFinOfCardEq hcard).symm
    let trC (c : C) := mixerPull tr L c (D - (mixerCross a b c).comp L) (d - q c)
    refine ⟨fun i => trC (φ i), fun _ => ht, ?_⟩
    intro j
    have hpt (c : C) (x : MixerWord k) :
        mixerValue f (trC c) j x = mixerValue q tr j (L x + c) := by
      apply mixerValue_pull
      simp only [f, q, mixerQuad_translate, LinearMap.sub_apply, LinearMap.comp_apply]
      abel
    change (∑ i, (fun c => ∑ x, mixerValue f (trC c) j x) (φ i)) = m * T j
    rw [φ.sum_comp (fun c => ∑ x, mixerValue f (trC c) j x)]
    simp_rw [hsum, hpt, hL]
    have htranslate : (∑ c : C, ∑ y : LinearMap.range L, mixerValue q tr j (y + c)) = T j := by
      rw [← hs j, ← E.sum_comp (mixerValue q tr j), Fintype.sum_prod_type]
      simp only [E, LinearEquiv.coe_toEquiv, Submodule.coe_prodEquivOfIsCompl', add_comm]
    simp_rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hkm]
    rw [← Finset.mul_sum, htranslate]
    rfl

private abbrev Cube (k : ℕ) := Fin k → Bit

private def chartGood (k : ℕ) (p : ℕ) (P : Finset (Cube k)) : Prop := by
  classical
  exact ∃ S : Finset (Fin k), p + S.card = k ∧
    ∃ (A : (S → Bit) →ₗ[Bit] Cube k) (v : Cube k),
      (∀ u, ∀ i : S, (A u + v) i.val = u i) ∧
      P = Finset.univ.image (fun u => A u + v)

private lemma chart_injective {k : ℕ} {S : Finset (Fin k)}
    {A : (S → Bit) →ₗ[Bit] Cube k} {v : Cube k}
    (hA : ∀ u, ∀ i : S, (A u + v) i.val = u i) :
    Function.Injective (fun u => A u + v) := by
  intro u z h
  funext i
  rw [← hA u i, ← hA z i]
  exact congrFun h i.val

private lemma chart_zero (k : ℕ) : chartGood k 0 (Finset.univ : Finset (Cube k)) := by
  classical
  let S : Finset (Fin k) := Finset.univ
  let A : (S → Bit) →ₗ[Bit] Cube k := LinearMap.pi (fun i => LinearMap.proj (⟨i, Finset.mem_univ _⟩ : S))
  refine ⟨S, by simp [S], A, 0, ?_, ?_⟩
  · intro u i
    simp [A]
  · ext x
    simp only [Finset.mem_univ, Finset.mem_image, true_and, true_iff, add_zero]
    exact ⟨fun i => x i.val, rfl⟩

private lemma bit_decide (x : Bit) (b : Bool) :
    decide (x ≠ 0) = b ↔ x = (if b then 1 else 0) := by
  rcases bit_cases x with rfl | rfl <;> cases b <;> decide

private lemma chart_branch {k p : ℕ} {P : Finset (Cube k)}
    (good : chartGood k p P) (ask : Cube k →ₗ[Bit] Bit) (c : Bit) :
    (∃ b : Bool, ∀ x ∈ P, decide (ask x + c ≠ 0) = b) ∨
      (chartGood k (p+1) (P.filter (fun x => decide (ask x + c ≠ 0) = false)) ∧
        chartGood k (p+1) (P.filter (fun x => decide (ask x + c ≠ 0) = true))) := by
  classical
  obtain ⟨S, hS, A, v, hA, rfl⟩ := good
  let l := ask.comp A
  by_cases hl : l = 0
  · left
    refine ⟨decide (ask v + c ≠ 0), ?_⟩
    intro x hx
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hx
    have hu : ask (A u) = 0 := congrArg (fun d : (S → Bit) →ₗ[Bit] Bit => d u) hl
    simp [map_add, hu]
  · right
    obtain ⟨pivot, hp⟩ := find_pivot l hl
    obtain ⟨E, _, hE, hcE, hsE⟩ := eliminate_pivot S l pivot hp
    have branch (b : Bool) : chartGood k (p+1)
        ((Finset.univ.image (fun u => A u + v)).filter (fun x => decide (ask x + c ≠ 0) = b)) := by
      let U := S.erase pivot.val
      let β : Bit := (if b then 1 else 0) + (ask v + c)
      let A' := A.comp E
      let v' := A (β • Pi.single pivot 1) + v
      have hb (u : S → Bit) : decide (ask (A u + v) + c ≠ 0) = b ↔ l u = β := by
        rw [bit_decide, map_add, add_assoc]
        change l u + (ask v + c) = _ ↔ l u = _
        rw [add_comm (l u)]
        exact bit_solve _ _ _
      have hAv (u : U → Bit) : A' u + v' = A (E u + β • Pi.single pivot 1) + v := by
        simp [A', v', map_add, add_assoc]
      refine ⟨U, ?_, A', v', ?_, ?_⟩
      · have hcard : U.card + 1 = S.card := Finset.card_erase_add_one pivot.property
        omega
      · intro u i
        rw [hAv]
        have hi := hA (E u + β • Pi.single pivot 1) ⟨i.val, Finset.mem_of_mem_erase i.property⟩
        exact hi.trans (hcE β u i)
      · ext x
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨u, rfl⟩, h⟩
          obtain ⟨z, hz⟩ := hsE β u ((hb u).mp h)
          exact ⟨z, by rw [hAv, hz]⟩
        · rintro ⟨u, rfl⟩
          rw [hAv]
          exact ⟨⟨_, rfl⟩, (hb _).mpr (hE β u)⟩
    exact ⟨branch false, branch true⟩

private lemma chart_card {k p : ℕ} {P : Finset (Cube k)}
    (good : chartGood k p P) : P.card = 2 ^ (k-p) := by
  classical
  obtain ⟨S, hS, A, v, hA, rfl⟩ := good
  rw [Finset.card_image_of_injective _ (chart_injective hA), Finset.card_univ,
    Fintype.card_fun, Fintype.card_coe, ZMod.card, show k-p = S.card by omega]

private noncomputable def hitsEq {k : ℕ} (p q : Cube k) : Finset (Fin k) :=
  Finset.univ.filter (fun i => p i = q i)

private lemma chart_trivial {k p j : ℕ} {P : Finset (Cube k)}
    (good : chartGood k p P) (v : Cube k → Finset (Fin k)) :
    ∑ x ∈ P, (v x).card.choose j ≤ 2 ^ (k-p) * k.choose j := by
  calc
    _ ≤ ∑ _ ∈ P, k.choose j := Finset.sum_le_sum fun x _ =>
      Nat.choose_le_choose _ (by simpa using Finset.card_le_univ (v x))
    _ = _ := by simp [chart_card good, nsmul_eq_mul]


private def quad {k : ℕ} (a b : Fin k → Fin k) (x : Cube k) : Cube k :=
  fun i => x (a i) * x (b i)

private def zeroExt {k : ℕ} (S : Finset (Fin k)) (u : S → Bit) : Cube k :=
  fun i => if h : i ∈ S then u ⟨i,h⟩ else 0

private lemma product_zero_iff (x y : Bit) :
    0 = x * y ↔ ¬ (x = 1 ∧ y = 1) := by
  rcases bit_cases x with rfl | rfl <;> rcases bit_cases y with rfl | rfl <;> decide

private lemma natCard_filter {A : Type*} [Fintype A] (p : A → Prop) [DecidablePred p] :
    Nat.card {x : A // p x} = (Finset.univ.filter p).card := by
  let e : {x : A // p x} ≃ {x : A // x ∈ Finset.univ.filter p} :=
    Equiv.subtypeEquivRight (fun x => by simp)
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

private lemma chart_footprint {k : ℕ} (a b : Fin k → Fin k) (hab : ∀ i, a i ≠ b i)
    (S : Finset (Fin k)) (A : (S → Bit) →ₗ[Bit] Cube k) (v : Cube k)
    (coord : ∀ u, ∀ i : S, (A u + v) i.val = u i)
    (aff : Cube k →ₗ[Bit] Cube k) (c : Cube k) (j : ℕ) :
    (∑ x ∈ (Finset.univ.image (fun u => A u + v)),
      (hitsEq (aff x + c) (quad a b x)).card.choose j) ≤
      auditScore (fun u => hitsEq 0 (quad a b (zeroExt S u))) j := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ h => chart_injective coord h)]
  apply auditScore_mono_audits (fun u => hitsEq (aff (A u+v)+c) (quad a b (A u+v)))
  intro U _
  let E := {i : Fin k // i ∈ U ∧ a i ∈ S ∧ b i ∈ S}
  let aa (e : E) : S := ⟨a e.val, e.property.2.1⟩
  let bb (e : E) : S := ⟨b e.val, e.property.2.2⟩
  let la (e : E) : (S → Bit) →ₗ[Bit] Bit := ((LinearMap.proj e.val).comp aff).comp A
  let cc (e : E) : Bit := (aff v+c) e.val
  let test (u : S → Bit) := ∀ e : E, u (aa e) * u (bb e) = la e u + cc e
  let avoid (u : S → Bit) := ∀ e : E, ¬ (u (aa e) = 1 ∧ u (bb e) = 1)
  have htest (u : S → Bit) (hu : U ⊆ hitsEq (aff (A u+v)+c) (quad a b (A u+v))) : test u := by
    intro e
    have h := (Finset.mem_filter.mp (hu e.property.1)).2.symm
    change ((A u+v) (a e.val)) * ((A u+v) (b e.val)) = (aff (A u+v)+c) e.val at h
    rw [coord u (aa e), coord u (bb e)] at h
    simpa [la, cc, map_add, Pi.add_apply, add_assoc] using h
  have havoid (u : S → Bit) : avoid u ↔ U ⊆ hitsEq 0 (quad a b (zeroExt S u)) := by
    constructor
    · intro hu i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change 0 = (zeroExt S u) (a i) * (zeroExt S u) (b i)
      by_cases ha : a i ∈ S
      · by_cases hb : b i ∈ S
        · let e : E := ⟨i,hi,ha,hb⟩
          simpa only [zeroExt, dif_pos ha, dif_pos hb] using
            (product_zero_iff (u (aa e)) (u (bb e))).mpr (hu e)
        · simp [zeroExt, ha, hb]
      · simp [zeroExt, ha]
    · intro h e
      have he := (Finset.mem_filter.mp (h e.property.1)).2
      change 0 = (zeroExt S u) (a e.val) * (zeroExt S u) (b e.val) at he
      rw [show (zeroExt S u) (a e.val) = u (aa e) by simp [zeroExt, aa, e.property.2.1],
        show (zeroExt S u) (b e.val) = u (bb e) by simp [zeroExt, bb, e.property.2.2]] at he
      exact (product_zero_iff _ _).mp he
  calc
    _ ≤ (Finset.univ.filter test).card := Finset.card_le_card (fun u hu =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, htest u (Finset.mem_filter.mp hu).2⟩)
    _ = Nat.card {u // test u} := (natCard_filter test).symm
    _ ≤ Nat.card {u // avoid u} := affineFootprint_card_le aa bb
      (fun e h => hab e.val (congrArg Subtype.val h)) la cc
    _ = (Finset.univ.filter avoid).card := natCard_filter avoid
    _ = _ := congrArg Finset.card (Finset.ext fun u => by simp [havoid u])


private abbrev GainPoly := Polynomial ℕ


private noncomputable def gainW : GainPoly := 1 + (Polynomial.X : GainPoly)

private noncomputable def gainAdvance (v : GainPoly × GainPoly) : GainPoly × GainPoly := ((v.1+v.2)*gainW, v.1*gainW+v.2)
private noncomputable def gainWalk (n : ℕ) (v : GainPoly × GainPoly) : GainPoly × GainPoly :=
  (List.range n).foldl (fun a _ => gainAdvance a) v
private noncomputable def gainPath (n : ℕ) : GainPoly := let v := gainWalk n (1,1); v.1+v.2
private noncomputable def gainCycle (n : ℕ) : GainPoly := (gainWalk n (1,0)).1 + (gainWalk n (0,1)).2
private noncomputable def gainB (k p : ℕ) : GainPoly :=
  if p = 0 then gainCycle k else if 2*p < k then
    Polynomial.C (2^(p-1)) * gainW^(2*p) * gainPath (k-2*p)
  else Polynomial.C (2^(k-p)) * gainW^k

-- Coordinates of the transfer power in the basis consisting of the transfer and the identity.
private noncomputable def gainAB : ℕ → GainPoly × GainPoly
  | 0 => (0, 1)
  | n+1 => ((gainW+1)*(gainAB n).1+(gainAB n).2, gainW*(Polynomial.X : GainPoly)*(gainAB n).1)

private theorem gainWalk_eq (n : ℕ) (u v : GainPoly) :
    gainWalk n (u,v) =
      ((gainAB n).1*(u+v)*gainW+(gainAB n).2*u, (gainAB n).1*(u*gainW+v)+(gainAB n).2*v) := by
  induction n with
  | zero => simp [gainWalk, gainAB]
  | succ n ih =>
    have hs : gainWalk (n+1) (u,v) = gainAdvance (gainWalk n (u,v)) := by
      simp [gainWalk, List.range_succ, List.foldl_append]
    rw [hs, ih]
    apply Prod.ext <;> simp only [gainAB, gainAdvance, gainW] <;> ring

private theorem gainPath_eq (n : ℕ) :
    gainPath n = (3*gainW+1)*(gainAB n).1+2*(gainAB n).2 := by
  simp only [gainPath, gainWalk_eq]
  ring

private theorem gainCycle_eq (n : ℕ) :
    gainCycle n = (gainW+1)*(gainAB n).1+2*(gainAB n).2 := by
  simp only [gainCycle, gainWalk_eq]
  ring

private noncomputable def gainS (n : ℕ) : GainPoly :=
  (Polynomial.X : GainPoly)*((4*gainW^2+3*gainW+1)*(gainAB n).1+(3*gainW+1)*(gainAB n).2)
private noncomputable def gainT (n : ℕ) : GainPoly :=
  (Polynomial.X : GainPoly)*((2*gainW^2+gainW+1)*(gainAB n).1+(gainW+1)*(gainAB n).2)

private theorem gainPath_two (n : ℕ) :
    4*gainW^2*gainPath n = gainPath (n+2)+gainS n := by
  simp only [gainPath_eq, gainAB, gainS, gainW]
  ring

private theorem gainCycle_two (n : ℕ) :
    2*gainW^2*gainPath n = gainCycle (n+2)+gainT n := by
  simp only [gainPath_eq, gainCycle_eq, gainAB, gainT, gainW]
  ring

private theorem gainS_two (n : ℕ) : ∃ r : GainPoly, gainS (n+2) = 2*gainW^2*gainS n+r := by
  let a := (gainAB n).1
  let b := (gainAB n).2
  refine ⟨(Polynomial.X : GainPoly)*((gainW+1)^3*((gainW+1)*a+b)+(2*gainW+1)*(gainW^2+gainW)*(Polynomial.X : GainPoly)*a), ?_⟩
  simp only [gainS, gainAB, gainW, a, b]
  ring

private theorem gainT_two (n : ℕ) : ∃ r : GainPoly, gainT (n+2) = gainW^2*gainS n+r := by
  let a := (gainAB n).1
  let b := (gainAB n).2
  refine ⟨(Polynomial.X : GainPoly)*((2*gainW^2+gainW+1)*(a+b)+(gainW^3+2*gainW^2)*(Polynomial.X : GainPoly)*a+(gainW^2+3*gainW)*gainW*a), ?_⟩
  simp only [gainT, gainS, gainAB, gainW, a, b]
  ring

private theorem gainS_one : ∃ r : GainPoly, gainS 1 = 2*gainW^2*(Polynomial.X : GainPoly)+r := by
  refine ⟨(Polynomial.X : GainPoly)*((2*gainW+1)*(gainW+1)), ?_⟩
  simp only [gainS, gainAB]
  ring

private theorem gainT_one : ∃ r : GainPoly, gainT 1 = gainW^2*(Polynomial.X : GainPoly)+r := by
  refine ⟨(Polynomial.X : GainPoly)*(gainW^2+gainW+1), ?_⟩
  simp only [gainT, gainAB]
  ring

private noncomputable def gainScale (p : ℕ) : GainPoly := Polynomial.C (2^(p-1)) * gainW^(2*p)

private theorem gainScale_succ (p : ℕ) (hp : 0 < p) :
    gainScale (p+1) = gainScale p * (2*gainW^2) := by
  unfold gainScale
  rw [show p+1-1 = (p-1)+1 by omega, show 2*(p+1) = 2*p+2 by omega,
    Nat.pow_succ, map_mul, pow_add]
  norm_num; ring

-- The even endpoint agrees with the interior formula because the empty path has weight 2.
private theorem gainB_le (k p : ℕ) (hp : 0 < p) (h : 2*p ≤ k) :
    gainB k p = gainScale p * gainPath (k-2*p) := by
  by_cases hl : 2*p < k
  · simp [gainB, gainScale, Nat.ne_of_gt hp, hl]
  · have hk : k = 2*p := by omega
    subst k
    rw [gainB, ite_eq_right (Nat.ne_of_gt hp), ite_eq_right (Nat.lt_irrefl _), gainScale,
      Nat.sub_self, gainPath_eq, gainAB, show 2*p-p = (p-1)+1 by omega, Nat.pow_succ, map_mul]
    norm_num; ring

private theorem gainInitial (n : ℕ) :
    2*gainB (n+2) 1 = gainB (n+2) 0 + gainT n := by
  rw [gainB_le (n+2) 1 (by omega) (by omega),
    show n+2-2*1 = n by omega, show gainB (n+2) 0 = gainCycle (n+2) by simp [gainB]]
  simpa [gainScale, mul_assoc] using gainCycle_two n

private theorem gainMiddle (p n : ℕ) (hp : 0 < p) :
    2*gainB (n+(2*p+2)) (p+1) = gainB (n+(2*p+2)) p + gainScale p * gainS n := by
  rw [gainB_le _ (p+1) (by omega) (by omega), gainB_le _ p hp (by omega),
    show n+(2*p+2)-2*(p+1) = n by omega, show n+(2*p+2)-2*p = n+2 by omega,
    gainScale_succ p hp]
  calc
    _ = gainScale p * (4*gainW^2*gainPath n) := by ring
    _ = _ := by rw [gainPath_two]; ring

private theorem gainOdd (p : ℕ) (hp : 0 < p) :
    2*gainB (2*p+1) (p+1) = gainB (2*p+1) p + gainScale p * (Polynomial.X : GainPoly) := by
  rw [gainB_le _ p hp (by omega), show 2*p+1-2*p = 1 by omega]
  have h : gainB (2*p+1) (p+1) = Polynomial.C (2^p) * gainW^(2*p+1) := by
    rw [gainB, ite_eq_right (by omega), ite_eq_right (by omega), show 2*p+1-(p+1) = p by omega]
  have hpow : 2^p = 2^(p-1)*2 := calc
    _ = 2^((p-1)+1) := by congr 1; omega
    _ = _ := Nat.pow_succ _ _
  rw [h, gainScale, hpow, map_mul, pow_succ gainW (2*p), gainPath_eq]
  simp only [gainAB, gainW]
  norm_num; ring

private theorem gainCompare {x y z a b r : GainPoly}
    (h₁ : 2*y = x+a) (h₂ : 2*z = y+b) (h₃ : a = b+r) (j : ℕ) :
    (2*z+x).coeff j ≤ (3*y).coeff j := by
  have h : 3*y = (2*z+x)+r := calc
    _ = 2*y+y := by ring
    _ = x+(b+r)+y := by rw [h₁, h₃]
    _ = (y+b)+x+r := by ring
    _ = _ := by rw [← h₂]
  rw [h, Polynomial.coeff_add]
  exact Nat.le_add_right _ _

private theorem gain_nonnegative (k p j : ℕ) (hk : 1 < k) (hp : p+1 ≤ (k+1)/2) :
    (gainB k p).coeff j ≤ (2*gainB k (p+1)).coeff j := by
  have hex : ∃ a : GainPoly, 2*gainB k (p+1) = gainB k p+a := by
    rcases eq_or_ne p 0 with rfl | hn
    · obtain ⟨n, rfl⟩ : ∃ n, k=n+2 := ⟨k-2, by omega⟩
      exact ⟨_, gainInitial n⟩
    · by_cases h : k = 2*p+1
      · subst k
        exact ⟨_, gainOdd p (by omega)⟩
      · obtain ⟨n, rfl⟩ : ∃ n, k=n+(2*p+2) := ⟨k-(2*p+2), by omega⟩
        exact ⟨_, gainMiddle p n (by omega)⟩
  obtain ⟨a, ha⟩ := hex
  rw [ha, Polynomial.coeff_add]
  exact Nat.le_add_right _ _

private theorem gain_nonincreasing (k p j : ℕ) (hp : p+2 ≤ (k+1)/2) :
    (2*gainB k (p+2)+gainB k p).coeff j ≤ (3*gainB k (p+1)).coeff j := by
  rcases eq_or_ne p 0 with rfl | hn
  · by_cases h : k = 3
    · subst k
      obtain ⟨r, hr⟩ := gainT_one
      exact gainCompare (gainInitial 1) (gainOdd 1 (by omega)) (r := r)
        (by simpa [gainScale] using hr) j
    · obtain ⟨n, rfl⟩ : ∃ n, k=n+4 := ⟨k-4, by omega⟩
      obtain ⟨r, hr⟩ := gainT_two n
      exact gainCompare (gainInitial (n+2)) (gainMiddle 1 n (by omega)) (r := r)
        (by simpa [gainScale] using hr) j
  · have hpos : 0 < p := by omega
    by_cases h : k = 2*p+3
    · subst k
      have h₁ := gainMiddle p 1 hpos
      rw [show 1+(2*p+2) = 2*p+3 by omega] at h₁
      have h₂ := gainOdd (p+1) (by omega)
      rw [show 2*(p+1)+1 = 2*p+3 by omega, gainScale_succ p hpos] at h₂
      obtain ⟨r, hr⟩ := gainS_one
      exact gainCompare h₁ h₂ (r := gainScale p * r) (by rw [hr]; ring) j
    · obtain ⟨n, rfl⟩ : ∃ n, k=n+(2*p+4) := ⟨k-(2*p+4), by omega⟩
      have h₁ := gainMiddle p (n+2) hpos
      rw [show n+2+(2*p+2) = n+(2*p+4) by omega] at h₁
      have h₂ := gainMiddle (p+1) n (by omega)
      rw [show n+(2*(p+1)+2) = n+(2*p+4) by omega, gainScale_succ p hpos] at h₂
      obtain ⟨r, hr⟩ := gainS_two n
      exact gainCompare h₁ h₂ (r := gainScale p * r) (by rw [hr]; ring) j


private abbrev AffTree (k : ℕ) :=
  Finset Hist × (Hist → Cube k →ₗ[Bit] Bit) × (Hist → Bit) ×
    (Hist → Cube k →ₗ[Bit] Cube k) × (Hist → Cube k)

private def evalTree {k : ℕ} (tree : AffTree k) (x : Cube k) : Cube k :=
  let h := runTree tree.1 (fun h x => decide (tree.2.1 h x + tree.2.2.1 h ≠ 0)) x tree.1.card []
  tree.2.2.2.1 h x + tree.2.2.2.2 h

private noncomputable def treeScore {k : ℕ} (q : Cube k → Cube k) (tree : AffTree k) (j : ℕ) : ℕ :=
  auditScore (fun x => hitsEq (evalTree tree x) (q x)) j

private def stopDepth (k : ℕ) := (k+1)/2

private def leafLimit (k L : ℕ) := min L (2 ^ stopDepth k)

private def balDepth (k L : ℕ) := Nat.log2 (leafLimit k L)

private def extraLeaves (k L : ℕ) := leafLimit k L - 2 ^ balDepth k L

private noncomputable def balPoly (k L : ℕ) : Polynomial ℕ :=
  let d := balDepth k L
  let a := extraLeaves k L
  Polynomial.C (2^d-a) * gainB k d + Polynomial.C (2*a) * gainB k (d+1)

private lemma depthFacts (k L : ℕ) (hL : 0 < L) :
    let r := stopDepth k
    let M := leafLimit k L
    let d := balDepth k L
    let a := extraLeaves k L
    2^d ≤ M ∧ M < 2^(d+1) ∧ d ≤ r ∧ a < 2^d ∧ (d = r → a = 0) := by
  dsimp only
  let r := stopDepth k
  let M := leafLimit k L
  let d := balDepth k L
  have hM : 0 < M := Nat.lt_min.mpr ⟨hL, pow_pos (by decide) _⟩
  have hMd : 2^d ≤ M := Nat.log2_self_le hM.ne'
  have hMd' : M < 2^(d+1) := (Nat.log2_lt hM.ne').mp (Nat.lt_succ_self _)
  have hMr : M ≤ 2^r := min_le_right _ _
  have hdr : d ≤ r := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hMd.trans hMr)
  refine ⟨hMd,hMd',hdr,?_,?_⟩
  · rw [pow_succ] at hMd'
    change M - 2^d < 2^d
    omega
  · intro he
    change d = r at he
    change M - 2^d = 0
    rw [he]
    exact Nat.sub_eq_zero_of_le hMr

private noncomputable def gainCoeff (k j p : ℕ) : ℕ :=
  if p < stopDepth k then 2 * (gainB k (p+1)).coeff j - (gainB k p).coeff j else 0

private lemma gainCoeff_step (k j : ℕ) (hk : 1 < k) (p : ℕ) (hp : p < stopDepth k) :
    (gainB k p).coeff j + gainCoeff k j p = 2 * (gainB k (p+1)).coeff j := by
  have h := gain_nonnegative k p j hk (by exact hp)
  simp only [Polynomial.coeff_ofNat_mul] at h
  rw [gainCoeff, ite_eq_left hp, Nat.add_sub_cancel' h]

private lemma gainCoeff_antitone (k j : ℕ) (hk : 1 < k) : Antitone (gainCoeff k j) := by
  apply antitone_nat_of_succ_le
  intro p
  by_cases hp : p+1 < stopDepth k
  · have hp0 : p < stopDepth k := by omega
    have h := gain_nonincreasing k p j (by exact hp)
    simp only [Polynomial.coeff_add, Polynomial.coeff_ofNat_mul] at h
    have h₀ := gainCoeff_step k j hk p hp0
    have h₁ := gainCoeff_step k j hk (p+1) hp
    rw [show p+1+1 = p+2 by omega] at h₁
    omega
  · simp [gainCoeff, hp]

private lemma balPoly_coeff (k L j : ℕ) (hk : 1 < k) (hL : 0 < L) :
    (balPoly k L).coeff j = 2 ^ balDepth k L * (gainB k (balDepth k L)).coeff j +
      extraLeaves k L * gainCoeff k j (balDepth k L) := by
  let d := balDepth k L
  let a := extraLeaves k L
  obtain ⟨_, _, hdr, ha, hz⟩ := depthFacts k L hL
  change (Polynomial.C (2^d-a) * gainB k d + Polynomial.C (2*a) * gainB k (d+1)).coeff j =
    2^d*(gainB k d).coeff j + a*gainCoeff k j d
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  by_cases hd : d = stopDepth k
  · have h0 : a = 0 := hz hd
    simp [h0]
  · have hs := gainCoeff_step k j hk d (lt_of_le_of_ne hdr hd)
    calc
      _ = (2^d-a) * (gainB k d).coeff j + a * (2 * (gainB k (d+1)).coeff j) := by ac_rfl
      _ = 2^d*(gainB k d).coeff j + a*gainCoeff k j d := by
        rw [← hs, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt ha)]

private lemma saturatedCoeff (k p j : ℕ) (hk : 1 < k) (hp : stopDepth k ≤ p) :
    (gainB k p).coeff j = 2^(k-p)*k.choose j := by
  have hp0 : p ≠ 0 := by unfold stopDepth at hp; omega
  have hk' : ¬ 2*p < k := by unfold stopDepth at hp; omega
  rw [gainB, ite_eq_right hp0, ite_eq_right hk', Polynomial.coeff_C_mul]
  simp [gainW, Polynomial.coeff_one_add_X_pow]

private lemma full_upper {k L : ℕ} (hk : 1 < k) (hL : 0 < L) (a b : Fin k → Fin k)
    (hab : ∀ i, a i ≠ b i)
    (mask_bound : ∀ (S : Finset (Fin k)) j,
      auditScore (fun u => hitsEq 0 (quad a b (zeroExt S u))) j ≤ (gainB k (k-S.card)).coeff j)
    (tree : AffTree k) (htree : tree.1.card < L) (j : ℕ) :
    treeScore (quad a b) tree j ≤ (balPoly k L).coeff j := by
  classical
  let r := stopDepth k
  let d := balDepth k L
  let a' := extraLeaves k L
  let B (p : ℕ) := (gainB k p).coeff j
  let ask (h : Hist) (x : Cube k) := decide (tree.2.1 h x + tree.2.2.1 h ≠ 0)
  let value (h : Hist) (x : Cube k) := (hitsEq (tree.2.2.2.1 h x + tree.2.2.2.2 h) (quad a b x)).card.choose j
  have hleaf (p : ℕ) (P : Finset (Cube k)) (hP : chartGood k p P) (h : Hist) :
      ∑ x ∈ P, value h x ≤ B p := by
    obtain ⟨S, hS, A, v, hA, rfl⟩ := hP
    apply (chart_footprint a b hab S A v hA (tree.2.2.2.1 h) (tree.2.2.2.2 h) j).trans
    rw [show p = k - S.card by omega]
    exact mask_bound S j
  have hsat (p : ℕ) (P : Finset (Cube k)) (hp : r ≤ p) (hP : chartGood k p P)
      (f : Cube k → Hist) : ∑ x ∈ P, value (f x) x ≤ B p := by
    rw [show B p = 2^(k-p)*k.choose j from saturatedCoeff k p j hk hp]
    exact chart_trivial hP (fun x => hitsEq (tree.2.2.2.1 (f x) x + tree.2.2.2.2 (f x)) (quad a b x))
  obtain ⟨count, _, hcp, hcb, hcv⟩ := tree_accounting tree.1 ask value (chartGood k) B
    (gainCoeff k j) r (gainCoeff_step k j hk) hleaf hsat
    (fun p P hP h => chart_branch hP (tree.2.1 h) (tree.2.2.1 h)) tree.1.card 0 [] Finset.univ (chart_zero k)
  have hcp' (i : ℕ) : count i ≤ 2^i := by simpa using hcp i
  have hcountL : (∑ i ∈ Finset.range r, count i) ≤ tree.1.card :=
    hcb.trans (Finset.card_le_card (Finset.filter_subset _ _))
  have hcountR : (∑ i ∈ Finset.range r, count i) + 1 ≤ 2^r := by
    rw [← sum_powers_two r]
    exact Nat.add_le_add_right (Finset.sum_le_sum fun i _ => hcp' i) _
  obtain ⟨hMd, _, hdr, _, _⟩ := depthFacts k L hL
  have hL' : (∑ i ∈ Finset.range r, count i) + 1 ≤ leafLimit k L :=
    Nat.le_min.mpr ⟨by omega, hcountR⟩
  have htotal : (∑ i ∈ Finset.range r, count i) ≤ (2^d-1)+a' := by
    change 2^d ≤ leafLimit k L at hMd
    change (∑ i ∈ Finset.range r, count i) ≤ (2^d-1) + (leafLimit k L - 2^d)
    have : 0 < 2^d := pow_pos (by decide) _
    omega
  have hu := depth_allocation B (gainCoeff k j) count d r a' hdr
    (fun p hp => gainCoeff_step k j hk p (lt_of_lt_of_le hp hdr)) (gainCoeff_antitone k j hk) hcp' htotal
  rw [balPoly_coeff k L j hk hL]
  exact hcv.trans hu


private def histories (p : ℕ) : Finset Hist :=
  Finset.univ.image (List.ofFn : (Fin p → Bool) → Hist)

private lemma mem_histories (h : Hist) (p : ℕ) : h ∈ histories p ↔ h.length = p := by
  constructor
  · intro hh
    obtain ⟨bs, _, rfl⟩ := Finset.mem_image.mp hh
    exact List.length_ofFn
  · intro hh
    subst p
    exact Finset.mem_image.mpr ⟨h.get, Finset.mem_univ _, List.ofFn_get _⟩

private lemma card_histories (p : ℕ) : (histories p).card = 2^p := by
  rw [histories, Finset.card_image_of_injective _ List.ofFn_injective]
  simp [Fintype.card_fun]

private def belowDepth (d : ℕ) : Finset Hist := (Finset.range d).biUnion histories

private lemma mem_belowDepth (d : ℕ) (h : Hist) : h ∈ belowDepth d ↔ h.length < d := by
  simp [belowDepth, mem_histories]

private lemma card_belowDepth (d : ℕ) : (belowDepth d).card + 1 = 2^d := by
  unfold belowDepth
  rw [Finset.card_biUnion]
  · simpa only [card_histories] using sum_powers_two d
  · intro p _ q _ hne
    apply Finset.disjoint_left.mpr
    intro h hp hq
    exact hne (((mem_histories h p).mp hp).symm.trans ((mem_histories h q).mp hq))

private def pivotHistory {k : ℕ} (pv : ℕ → Fin k) (p : ℕ) (x : Cube k) : Hist :=
  List.ofFn (fun i : Fin p => decide (x (pv i.val) ≠ 0))

private lemma pivotHistory_length {k : ℕ} (pv : ℕ → Fin k) (p : ℕ) (x : Cube k) :
    (pivotHistory pv p x).length = p := List.length_ofFn

private lemma pivotHistory_succ {k : ℕ} (pv : ℕ → Fin k) (p : ℕ) (x : Cube k) :
    pivotHistory pv (p+1) x = pivotHistory pv p x ++ [decide (x (pv p) ≠ 0)] := by
  simpa only [pivotHistory, List.concat_eq_append, Fin.val_castSucc, Fin.val_last] using
    List.ofFn_succ' (fun i : Fin (p+1) => decide (x (pv i.val) ≠ 0))

private lemma runTree_hits_stop {A : Type*} (nodes : Finset Hist) (ask : Hist → A → Bool)
    (x : A) (H : ℕ → Hist) (q : ℕ)
    (hs : ∀ n, H (n+1) = H n ++ [ask (H n) x])
    (hnode : ∀ n < q, H n ∈ nodes) (hstop : H q ∉ nodes) :
    ∀ m p, p ≤ q → q ≤ p+m → runTree nodes ask x m (H p) = H q := by
  intro m
  induction m with
  | zero =>
    intro p hp hq
    have he : p = q := by omega
    subst p
    rfl
  | succ m ih =>
    intro p hp hq
    by_cases he : p = q
    · subst p
      simp [runTree, hstop]
    · have ha := hnode p (by omega)
      rw [runTree, ite_eq_left ha, ← hs]
      exact ih (p+1) (by omega) (by omega)

private def freePivots {k : ℕ} (pv : ℕ → Fin k) (p : ℕ) : Finset (Fin k) :=
  Finset.univ \ (Finset.range p).image pv

private lemma mem_freePivots {k : ℕ} (pv : ℕ → Fin k) (p : ℕ) (i : Fin k) :
    i ∈ freePivots pv p ↔ ¬ ∃ n < p, pv n = i := by
  simp [freePivots]

private def historyBit {k : ℕ} (idx : Fin k → ℕ) (h : Hist) (i : Fin k) : Bit :=
  if h.getD (idx i) false then 1 else 0

private lemma historyBit_read {k r p : ℕ} (pv : ℕ → Fin k) (idx : Fin k → ℕ)
    (hinv : ∀ n < r, idx (pv n) = n) (hpr : p ≤ r) (x : Cube k)
    (i : Fin k) (hi : i ∉ freePivots pv p) : historyBit idx (pivotHistory pv p x) i = x i := by
  obtain ⟨n, hn, rfl⟩ : ∃ n < p, pv n = i := not_not.mp (by rwa [mem_freePivots] at hi)
  unfold historyBit
  rw [hinv n (lt_of_lt_of_le hn hpr), List.getD_eq_getElem _ _ (by simpa [pivotHistory] using hn)]
  simp only [pivotHistory, List.getElem_ofFn]
  exact ((bit_decide _ _).mp rfl).symm

private def pivotExtend {k : ℕ} (pv : ℕ → Fin k) (idx : Fin k → ℕ) (p : ℕ) (h : Hist)
    (u : freePivots pv p → Bit) : Cube k :=
  fun i => if hi : i ∈ freePivots pv p then u ⟨i,hi⟩ else historyBit idx h i

private lemma pivotSlice_image {k r p : ℕ} (pv : ℕ → Fin k) (idx : Fin k → ℕ)
    (hinv : ∀ n < r, idx (pv n) = n) (hpr : p ≤ r) (h : Hist) (hlen : h.length = p) :
    (Finset.univ.filter (fun x : Cube k => pivotHistory pv p x = h)) =
      Finset.univ.image (pivotExtend pv idx p h) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hx
    refine ⟨fun i => x i.val, ?_⟩
    funext i
    by_cases hi : i ∈ freePivots pv p
    · simp [pivotExtend, hi]
    · rw [← hx]
      simp [pivotExtend, hi, historyBit_read pv idx hinv hpr x i hi]
  · rintro ⟨u, rfl⟩
    apply List.ext_getElem
    · simp [pivotHistory, hlen]
    · intro n hn hn'
      have hp : n < p := by simpa [hlen] using hn'
      have hv : pv n ∉ freePivots pv p := (mem_freePivots ..).not.mpr (not_not.mpr ⟨n,hp,rfl⟩)
      simp only [pivotHistory, List.getElem_ofFn, pivotExtend, dite_eq_right hv, historyBit,
        hinv n (lt_of_lt_of_le hp hpr), List.getD_eq_getElem h false hn']
      cases h[n]'hn' <;> decide

private lemma pivotExtend_injective {k : ℕ} (pv : ℕ → Fin k) (idx : Fin k → ℕ)
    (p : ℕ) (h : Hist) : Function.Injective (pivotExtend pv idx p h) := by
  intro u z he
  funext i
  simpa [pivotExtend, i.property] using congrFun he i.val


private noncomputable def pivotOut {k : ℕ} (a b : Fin k → Fin k) (pv : ℕ → Fin k)
    (idx : Fin k → ℕ) (h : Hist) : Cube k →ₗ[Bit] Cube k :=
  LinearMap.pi fun i =>
    if a i ∉ freePivots pv h.length then historyBit idx h (a i) • LinearMap.proj (b i)
    else if b i ∉ freePivots pv h.length then historyBit idx h (b i) • LinearMap.proj (a i)
    else 0

private lemma pivot_hits {k r p : ℕ} (a b : Fin k → Fin k) (pv : ℕ → Fin k) (idx : Fin k → ℕ)
    (hinv : ∀ n < r, idx (pv n) = n) (hpr : p ≤ r) (x : Cube k) :
    hitsEq (pivotOut a b pv idx (pivotHistory pv p x) x) (quad a b x) =
      hitsEq 0 (quad a b (zeroExt (freePivots pv p) (fun i => x i.val))) := by
  ext i
  simp only [hitsEq, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a i ∈ freePivots pv p
  · by_cases hb : b i ∈ freePivots pv p
    · simp [pivotOut, pivotHistory_length, quad, zeroExt, ha, hb]
    · simp [pivotOut, pivotHistory_length, quad, zeroExt, ha, hb,
        historyBit_read pv idx hinv hpr x (b i) hb, mul_comm]
  · simp [pivotOut, pivotHistory_length, quad, zeroExt, ha,
      historyBit_read pv idx hinv hpr x (a i) ha]

private lemma pivotSlice_score {k r p : ℕ} (a b : Fin k → Fin k) (pv : ℕ → Fin k)
    (idx : Fin k → ℕ) (hinv : ∀ n < r, idx (pv n) = n) (hpr : p ≤ r)
    (h : Hist) (hlen : h.length = p) (j : ℕ) :
    (∑ x ∈ Finset.univ.filter (fun x : Cube k => pivotHistory pv p x = h),
      (hitsEq (pivotOut a b pv idx h x) (quad a b x)).card.choose j) =
      auditScore (fun u => hitsEq 0 (quad a b (zeroExt (freePivots pv p) u))) j := by
  classical
  have hslice := pivotSlice_image pv idx hinv hpr h hlen
  rw [hslice, Finset.sum_image (fun _ _ _ _ he => pivotExtend_injective pv idx p h he)]
  unfold auditScore
  apply Finset.sum_congr rfl
  intro u hu
  let x := pivotExtend pv idx p h u
  have hx : x ∈ Finset.univ.image (pivotExtend pv idx p h) := Finset.mem_image.mpr ⟨u,hu,rfl⟩
  have hx' : x ∈ Finset.univ.filter (fun x : Cube k => pivotHistory pv p x = h) := by rwa [hslice]
  have hH : pivotHistory pv p x = h := (Finset.mem_filter.mp hx').2
  have hval := pivot_hits a b pv idx hinv hpr x
  rw [hH] at hval
  have hres : (fun i : freePivots pv p => x i.val) = u := by
    funext i
    simp [x, pivotExtend, i.property]
  rw [hres] at hval
  exact congrArg (fun s : Finset (Fin k) => s.card.choose j) hval


private lemma full_lower {k L : ℕ} (hL : 0 < L) (a b : Fin k → Fin k)
    (pv : ℕ → Fin k) (idx : Fin k → ℕ) (hinv : ∀ n < stopDepth k, idx (pv n) = n)
    (mask_exact : ∀ p ≤ stopDepth k, ∀ j,
      auditScore (fun u => hitsEq 0 (quad a b (zeroExt (freePivots pv p) u))) j =
        (gainB k p).coeff j) :
    ∃ tree : AffTree k, tree.1.card < L ∧ ∀ j, treeScore (quad a b) tree j = (balPoly k L).coeff j := by
  classical
  let r := stopDepth k
  let d := balDepth k L
  let A := extraLeaves k L
  obtain ⟨hMd, _, hdr, hA, ha0⟩ := depthFacts k L hL
  obtain ⟨sel, hsel, hcard⟩ := Finset.exists_subset_card_eq
    (show A ≤ (histories d).card by rw [card_histories]; exact Nat.le_of_lt hA)
  let nodes := belowDepth d ∪ sel
  have hD : Disjoint (belowDepth d) sel := by
    apply Finset.disjoint_left.mpr
    intro h h₀ h₁
    have hh := (mem_histories h d).mp (hsel h₁)
    have hl := (mem_belowDepth d h).mp h₀
    omega
  have hN : nodes.card + 1 = 2^d + A := by
    unfold nodes
    rw [Finset.card_union_of_disjoint hD, hcard, Nat.add_right_comm, card_belowDepth]
  have hM : 2^d + A = leafLimit k L := Nat.add_sub_of_le hMd
  have hNL : nodes.card < L := by
    have := min_le_left L (2 ^ r)
    change leafLimit k L ≤ L at this
    omega
  let tree : AffTree k := (nodes, fun h => LinearMap.proj (pv h.length), fun _ => 0,
    pivotOut a b pv idx, fun _ => 0)
  let ask (h : Hist) (x : Cube k) := decide (x (pv h.length) ≠ 0)
  have hrun (x : Cube k) :
      let q := if pivotHistory pv d x ∈ sel then d+1 else d
      runTree nodes ask x nodes.card [] = pivotHistory pv q x := by
    dsimp only
    let q := if pivotHistory pv d x ∈ sel then d+1 else d
    have hs (n : ℕ) : pivotHistory pv (n+1) x = pivotHistory pv n x ++ [ask (pivotHistory pv n x) x] := by
      simp only [ask, pivotHistory_length, pivotHistory_succ]
    have hm : ∀ n < q, pivotHistory pv n x ∈ nodes := by
      intro n hn
      by_cases hd : n < d
      · exact Finset.mem_union.mpr (Or.inl ((mem_belowDepth _ _).mpr (by simpa [pivotHistory_length])))
      · have he : pivotHistory pv d x ∈ sel ∧ n = d := by
          by_cases hx : pivotHistory pv d x ∈ sel
          · rw [show q = d+1 by simp [q,hx]] at hn
            exact ⟨hx, by omega⟩
          · rw [show q = d by simp [q,hx]] at hn
            omega
        exact Finset.mem_union.mpr (Or.inr (he.2.symm ▸ he.1))
    have hn : pivotHistory pv q x ∉ nodes := by
      intro hh
      rcases Finset.mem_union.mp hh with hlow | hh
      · have h := (mem_belowDepth _ _).mp hlow
        rw [pivotHistory_length] at h
        by_cases hx : pivotHistory pv d x ∈ sel <;> simp [q,hx] at h
      · have h := (mem_histories _ _).mp (hsel hh)
        rw [pivotHistory_length] at h
        by_cases hx : pivotHistory pv d x ∈ sel
        · simp [q,hx] at h
        · exact hx (h ▸ hh)
    have hq : q ≤ nodes.card := by
      have hpow : d < 2^d := Nat.lt_two_pow_self
      by_cases hx : pivotHistory pv d x ∈ sel
      · have hApos : 0 < A := hcard ▸ Finset.card_pos.mpr ⟨_,hx⟩
        have : q = d+1 := by simp [q,hx]
        omega
      · have : q = d := by simp [q,hx]
        omega
    change runTree nodes ask x nodes.card [] = pivotHistory pv q x
    simpa only [show pivotHistory pv 0 x = [] from rfl] using
      runTree_hits_stop nodes ask x (fun n => pivotHistory pv n x) q hs hm hn
        nodes.card 0 (by omega) (by omega)
  refine ⟨tree, hNL, ?_⟩
  intro j
  let val (x : Cube k) : ℕ := (hitsEq (evalTree tree x) (quad a b x)).card.choose j
  let valH (h : Hist) (x : Cube k) : ℕ := (hitsEq (pivotOut a b pv idx h x) (quad a b x)).card.choose j
  have hval (x : Cube k) : val x =
      valH (pivotHistory pv (if pivotHistory pv d x ∈ sel then d+1 else d) x) x := by
    have h := hrun x
    simpa [val, valH, evalTree, tree, ask] using congrArg (fun h => valH h x) h
  let B (p : ℕ) := (gainB k p).coeff j
  have hinner (h : Hist) (hh : h ∈ histories d) :
      (∑ x ∈ Finset.univ.filter (fun x : Cube k => pivotHistory pv d x = h), val x) =
        if h ∈ sel then 2 * B (d+1) else B d := by
    have hhlen : h.length = d := (mem_histories h d).mp hh
    by_cases hhs : h ∈ sel
    · rw [ite_eq_left hhs]
      have hpr : d+1 ≤ r := by
        have hpos : 0 < A := hcard ▸ Finset.card_pos.mpr ⟨h,hhs⟩
        by_contra! hn
        have hzero := ha0 (by omega : d = r)
        omega
      let bit (x : Cube k) := decide (x (pv d) ≠ 0)
      let P := Finset.univ.filter (fun x : Cube k => pivotHistory pv d x = h)
      have hsplit (bd : Bool) : P.filter (fun x => bit x = bd) =
          Finset.univ.filter (fun x : Cube k => pivotHistory pv (d+1) x = h ++ [bd]) := by
        ext x
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, pivotHistory_succ]
        constructor
        · rintro ⟨h₀,h₁⟩
          rw [h₀, show decide (x (pv d) ≠ 0) = bd from h₁]
        · intro he
          have he' := List.append_inj' he (by simp)
          exact ⟨he'.1, (List.cons.inj he'.2).1⟩
      change (∑ x ∈ P, val x) = _
      rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset Bool))
        (g := bit) (fun _ _ => Finset.mem_univ _) val]
      calc
        _ = (Finset.univ : Finset Bool).card * B (d+1) := by
          apply Finset.sum_const_nat
          intro bd _
          rw [hsplit bd]
          change _ = (gainB k (d+1)).coeff j
          rw [← mask_exact (d+1) hpr j,
            ← pivotSlice_score a b pv idx hinv hpr (h ++ [bd]) (by simp [hhlen]) j]
          apply Finset.sum_congr rfl
          intro x hx
          have hx' := (Finset.mem_filter.mp hx).2
          obtain ⟨h₀,_⟩ := List.append_inj' ((pivotHistory_succ pv d x).symm.trans hx') (by simp)
          rw [hval, h₀, ite_eq_left hhs, hx']
        _ = _ := by simp
    · rw [ite_eq_right hhs]
      change _ = (gainB k d).coeff j
      rw [← mask_exact d hdr j, ← pivotSlice_score a b pv idx hinv hdr h hhlen j]
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      rw [hval, hx', ite_eq_right hhs, hx']
  change (∑ x : Cube k, val x) = _
  rw [← Finset.sum_fiberwise_of_maps_to (t := histories d)
    (g := fun x => pivotHistory pv d x) (fun x _ => (mem_histories _ _).mpr (pivotHistory_length _ _ _)) val]
  calc
    _ = ∑ h ∈ histories d, if h ∈ sel then 2 * B (d+1) else B d := Finset.sum_congr rfl hinner
    _ = ((histories d \ sel).card * B d) + sel.card * (2 * B (d+1)) := by
      have hd : Disjoint (histories d \ sel) sel := Finset.disjoint_left.mpr fun _ h hn =>
        (Finset.mem_sdiff.mp h).2 hn
      conv_lhs => rw [← Finset.sdiff_union_of_subset hsel]
      rw [Finset.sum_union hd]
      congr 1
      · exact Finset.sum_const_nat (fun _ h => ite_eq_right (Finset.mem_sdiff.mp h).2)
      · exact Finset.sum_const_nat (fun _ h => ite_eq_left h)
    _ = (balPoly k L).coeff j := by
      change _ = (Polynomial.C (2^d-A) * gainB k d + Polynomial.C (2*A) * gainB k (d+1)).coeff j
      rw [Finset.card_sdiff_of_subset hsel, card_histories, hcard, Polynomial.coeff_add,
        Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      unfold B
      ac_rfl


private def cycleA {k : ℕ} (hk : 0 < k) (i : Fin k) := kernelIx hk (i.val+1)

private def cycleB {k : ℕ} (hk : 0 < k) (i : Fin k) := kernelIx hk (i.val+2)

private lemma cycleA_succ {k : ℕ} [NeZero k] (hk : 0 < k) (i : Fin k) :
    cycleA hk i = i+1 := Fin.ext (maskSucc_val i).symm

private lemma cycleB_succ {k : ℕ} [NeZero k] (hk : 0 < k) (i : Fin k) :
    cycleB hk i = (i+1)+1 := by
  rw [← cycleA_succ hk, ← cycleA_succ hk]
  exact (kernelIx_add hk (i.val+1) 1).symm

private lemma cycle_ends_ne {k : ℕ} [NeZero k] (hk : 1 < k) (i : Fin k) :
    cycleA (by omega : 0 < k) i ≠ cycleB (by omega : 0 < k) i := by
  rw [cycleA_succ, cycleB_succ]
  intro h
  have h' : (0 : Fin k) = 1 := add_left_cancel (by simpa only [add_zero] using h)
  have hval : (0 : ℕ) = 1 % k := by simpa only [Fin.val_zero, Fin.val_one'] using congrArg Fin.val h'
  rw [Nat.mod_eq_of_lt hk] at hval
  omega

private noncomputable def maskBitsEquiv {k : ℕ} (S : Finset (Fin k)) :
    (S → Bit) ≃ {x : Fin k → Bool // ∀ i, x i = true → i ∈ S} where
  toFun u := ⟨fun i => decide (zeroExt S u i ≠ 0), by
    intro i hi
    by_contra hn
    simp [zeroExt, hn] at hi⟩
  invFun x i := if x.val i.val then 1 else 0
  left_inv u := by
    funext i
    have h : zeroExt S u i.val = u i := by simp [zeroExt, i.property]
    change (if decide (zeroExt S u i.val ≠ 0) then 1 else 0) = u i
    rw [h]
    exact ((bit_decide _ _).mp rfl).symm
  right_inv x := by
    apply Subtype.ext
    funext i
    change decide (zeroExt S (fun j => if x.val j.val then 1 else 0) i ≠ 0) = x.val i
    rw [bit_decide]
    by_cases hi : i ∈ S
    · simp [zeroExt, hi]
    · have hfalse : x.val i = false := Bool.eq_false_iff.mpr (fun h => hi (x.property i h))
      simp [zeroExt, hi, hfalse]

private lemma mask_card_hits {k : ℕ} [NeZero k] (hk : 0 < k) (S : Finset (Fin k)) (u : S → Bit) :
    (hitsEq 0 (quad (cycleA hk) (cycleB hk) (zeroExt S u))).card =
      ((Finset.univ : Finset (Fin k)).filter (fun i =>
        ¬ ((maskBitsEquiv S u).val i = true ∧ (maskBitsEquiv S u).val (i+1) = true))).card := by
  let x := (maskBitsEquiv S u).val
  let good (i : Fin k) := ¬ (x i = true ∧ x (i+1) = true)
  have hp (i : Fin k) : i ∈ hitsEq 0 (quad (cycleA hk) (cycleB hk) (zeroExt S u)) ↔ good (i+1) := by
    have hx (i : Fin k) : x i = true ↔ zeroExt S u i = 1 := bit_decide _ true
    simp only [hitsEq, Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply,
      quad, product_zero_iff, cycleA_succ hk, cycleB_succ hk, good, hx]
  rw [show hitsEq 0 (quad (cycleA hk) (cycleB hk) (zeroExt S u)) =
      Finset.univ.filter (fun i => good (i+1)) by ext i; simpa using hp i]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin k)) (fun i => if good i then (1 : ℕ) else 0)

private lemma scoreMask {k : ℕ} [NeZero k] (hk : 0 < k) (S : Finset (Fin k)) (j : ℕ) :
    auditScore (fun u => hitsEq 0 (quad (cycleA hk) (cycleB hk) (zeroExt S u))) j =
      (idealMasked S).coeff j := by
  classical
  rw [idealMasked_coeff, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  unfold auditScore
  rw [← (maskBitsEquiv S).sum_comp]
  apply Finset.sum_congr rfl
  intro u _
  rw [mask_card_hits hk S u]

private def evenPivot {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := kernelIx hk (2*n)

private lemma evenPivot_idx {k : ℕ} (hk : 0 < k) (n : ℕ) (hn : n < stopDepth k) :
    (evenPivot hk n).val / 2 = n := by
  have hlt : 2*n < k := by unfold stopDepth at hn; omega
  change (2*n % k) / 2 = n
  rw [Nat.mod_eq_of_lt hlt]
  omega

private lemma evenPivot_free {k p : ℕ} (hk : 0 < k) (hp : p ≤ stopDepth k) :
    freePivots (evenPivot hk) p = canonicalFree k p := by
  ext i
  simp only [mem_freePivots, canonicalFree, Finset.mem_filter, Finset.mem_univ, true_and]
  apply not_congr
  constructor
  · rintro ⟨n, hn, hni⟩
    have hlt : 2*n < k := by unfold stopDepth at hp; omega
    have he : (2*n)%k = i.val := congrArg Fin.val hni
    rw [Nat.mod_eq_of_lt hlt] at he
    omega
  · intro hi
    refine ⟨i.val/2, by omega, Fin.ext ?_⟩
    change (2*(i.val/2))%k = i.val
    have he : 2*(i.val/2) = i.val := by omega
    rw [he, Nat.mod_eq_of_lt i.isLt]

private lemma treeScore_mixer {k : ℕ} (q : Cube k → Cube k) (tr : AffTree k) (j : ℕ) :
    treeScore q tr j = ∑ x, mixerValue q tr j x := by
  unfold treeScore auditScore hitsEq evalTree mixerValue mixerPredict
  simp only [runTree_fold]

private noncomputable def cycleTarget (k L : ℕ) : Polynomial ℕ :=
  if k = 1 then 2 * (1 + Polynomial.X) else balPoly k L

private lemma cubeCycle {k L : ℕ} (hk : 0 < k) (hL : 0 < L) :
    (∀ tr : AffTree k, tr.1.card < L → ∀ j,
        treeScore (quad (cycleA hk) (cycleB hk)) tr j ≤ (cycleTarget k L).coeff j) ∧
      ∃ tr : AffTree k, tr.1.card < L ∧ ∀ j,
        treeScore (quad (cycleA hk) (cycleB hk)) tr j = (cycleTarget k L).coeff j := by
  classical
  letI : NeZero k := ⟨hk.ne'⟩
  by_cases h1 : k = 1
  · subst k
    have hq (x : Cube 1) : quad (cycleA hk) (cycleB hk) x = x := by
      funext i
      unfold quad
      rw [Subsingleton.elim (cycleA hk i) i, Subsingleton.elim (cycleB hk i) i]
      exact fp_square _
    have hcoeff (j : ℕ) : (cycleTarget 1 L).coeff j = 2 * Nat.choose 1 j := by
      rw [cycleTarget, ite_eq_left rfl, Polynomial.coeff_ofNat_mul]
      congr 1
      simpa using Polynomial.coeff_one_add_X_pow ℕ 1 j
    constructor
    · intro tr _ j
      rw [hcoeff]
      exact (auditScore_universal _ j).trans (by simp [Cube, Bit, Fintype.card_fun, ZMod.card])
    · let tr : AffTree 1 := (∅, fun _ => 0, fun _ => 0, fun _ => LinearMap.id, fun _ => 0)
      refine ⟨tr, by simpa [tr] using hL, ?_⟩
      intro j
      rw [hcoeff]
      simp [treeScore, auditScore, evalTree, runTree, tr, hq, hitsEq, Cube, Bit, Fintype.card_fun, ZMod.card]
  · have hk1 : 1 < k := by omega
    have he : ∀ p, maskB k p = gainB k p := fun p => maskB_posted k p
    rw [cycleTarget, ite_eq_right h1]
    constructor
    · intro tr ht j
      apply full_upper hk1 hL (cycleA hk) (cycleB hk) (cycle_ends_ne hk1) _ tr ht j
      intro S i
      rw [scoreMask, ← he]
      exact idealMasked_bound_pos S i
    · apply full_lower hL (cycleA hk) (cycleB hk) (evenPivot hk) (fun i => i.val/2) (evenPivot_idx hk)
      intro p hp j
      rw [scoreMask, evenPivot_free hk hp, idealMasked_canonical_pos hp, he]


private def rotateLinear {k : ℕ} (hk : 0 < k) (s : ℕ) : Cube k →ₗ[Bit] Cube k where
  toFun x i := x (kernelIx hk (i.val+k-s%k))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rotateEquiv {k : ℕ} (hk : 0 < k) (s : ℕ) : Cube k ≃ Cube k where
  toFun := rotateLinear hk s
  invFun x i := x (kernelIx hk (i.val+s))
  left_inv x := by
    funext i
    change x (kernelIx hk ((kernelIx hk (i.val+s)).val+k-s%k)) = x i
    rw [kernelIx_forward_back]
  right_inv x := by
    funext i
    change x (kernelIx hk ((kernelIx hk (i.val+k-s%k)).val+s)) = x i
    rw [kernelIx_back_forward]

private lemma rotated_kernel_card {k : ℕ} (hk : 0 < k) (s spacing : ℕ) :
    Nat.card ((kernelMixer hk spacing).comp (rotateLinear hk s)).ker =
      2 ^ (if 3 ∣ k / Nat.gcd k spacing then 2 * Nat.gcd k spacing else 0) := by
  let R := rotateEquiv hk s
  let f := kernelMixer hk spacing
  let L := f.comp (rotateLinear hk s)
  let e : L.ker ≃ f.ker := {
    toFun := fun u => ⟨R u, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp u.property)⟩
    invFun := fun u => ⟨R.symm u, LinearMap.mem_ker.mpr (by
      change f (R (R.symm u)) = 0
      rw [R.apply_symm_apply]
      exact LinearMap.mem_ker.mp u.property)⟩
    left_inv := fun u => Subtype.ext (R.symm_apply_apply u)
    right_inv := fun u => Subtype.ext (R.apply_symm_apply u) }
  exact (Nat.card_congr e).trans (kernelMixer_card hk spacing)

private lemma addLinear_out {k : ℕ} (hk : 0 < k) (s t spacing : ℕ) (name c : Cube k) :
    let L := (kernelMixer hk spacing).comp (rotateLinear hk s)
    ∃ (D : Cube k →ₗ[Bit] Cube k) (d : Cube k), ∀ (x : Cube k),
      (fun i : Fin k =>
        let old := rotateLinear hk s x + name
        let y := fun j : Fin k =>
          old j + old (kernelIx hk (j.val + spacing)) + old (kernelIx hk (j.val + k - spacing % k))
        y i + (1+y (cycleA hk i))*y (cycleB hk i) + rotateLinear hk t x i + c i) =
        mixerQuad (cycleA hk) (cycleB hk) (L x) + D x + d := by
  let M := kernelMixer hk spacing
  let L := M.comp (rotateLinear hk s)
  let u := M name
  let a := cycleA hk
  let b := cycleB hk
  let takeB : Cube k →ₗ[Bit] Cube k := LinearMap.pi fun i => LinearMap.proj (b i)
  let D := L + (mixerCross a b u).comp L + takeB.comp L + rotateLinear hk t
  let d := u + mixerQuad a b u + takeB u + c
  refine ⟨D, d, ?_⟩
  intro x
  funext i
  have hy (j : Fin k) :
      let z := rotateLinear hk s x + name
      z j + z (kernelIx hk (j.val + spacing)) + z (kernelIx hk (j.val + k - spacing % k)) =
        (L x + u) j := congrFun (map_add M (rotateLinear hk s x) name) j
  dsimp only
  simp only [hy]
  change (L x + u) i + (1+(L x+u) (a i))*(L x+u) (b i) + rotateLinear hk t x i + c i =
    (mixerQuad a b (L x) + D x + d) i
  simp only [D, d, mixerQuad, mixerCross, takeB, LinearMap.comp_apply, LinearMap.add_apply,
    LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.smul_apply, Pi.add_apply, smul_eq_mul]
  ring


end PEqualNP.Outside.L_meta_32056

open PEqualNP.Outside.L_meta_32056

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_32056 :
∀ (k : Nat) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : Nat => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (n : Nat) (word : W) (i : Fin k) => word (ix (i.val+k-n % k))
  ∀ (spacing s t : Nat) (name constant : W),
    let out := fun (raw : W) (site : Fin k) =>
      let old := rot s raw + name
      let y := fun u : Fin k =>
        old u + old (ix (u.val+spacing)) + old (ix (u.val+k-spacing % k))
      y site + (1+y (ix (site.val+1)))*y (ix (site.val+2)) + rot t raw site + constant site
    let H := List Bool
    let Tree := Finset H × (H → W →ₗ[F] F) × (H → F) × (H → W →ₗ[F] W) × (H → W)
    let predict : Tree → W → W := fun tree raw =>
      let nodes := tree.1
      let ask := tree.2.1
      let bias := tree.2.2.1
      let aff := tree.2.2.2.1
      let c := tree.2.2.2.2
      let leaf := (List.range nodes.card).foldl (fun (p : H) _ =>
        if p ∈ nodes then p ++ [decide (ask p raw + bias p ≠ 0)] else p) []
      aff leaf raw + c leaf
    let g := Nat.gcd k spacing
    let h := if 3 ∣ k/g then 2*g else 0
    ∀ L : Nat, 0 < L →
      let Z := Polynomial Nat
      let w : Z := 1 + Polynomial.X
      let advance := fun (v : Z × Z) => ((v.1+v.2)*w, v.1*w+v.2)
      let walk := fun (n : Nat) (v : Z × Z) => (List.range n).foldl (fun a _ => advance a) v
      let path := fun (n : Nat) => let v := walk n (1,1); v.1+v.2
      let cycle := (walk k (1,0)).1 + (walk k (0,1)).2
      let B := fun p : Nat =>
        if p = 0 then cycle else if 2*p < k then
          Polynomial.C (2^(p-1)) * w^(2*p) * path (k-2*p)
        else Polynomial.C (2^(k-p)) * w^k
      let M := min L (2^((k+1)/2))
      let d := Nat.log2 M
      let a := M-2^d
      let target : Z := if k = 1 then 2*w else
        Polynomial.C (2^d-a)*B d + Polynomial.C (2*a)*B (d+1)
      let score := fun (tree : Tree) (j : Nat) =>
        ∑ x : W, Nat.choose ((Finset.univ : Finset (Fin k)).filter
          (fun i => predict tree x i = out x i)).card j
      (∀ tree : Tree, tree.1.card < L → ∀ j : Nat,
        score tree j ≤ min (2^k * Nat.choose k j) (2^h * target.coeff j)) ∧
      ∃ family : Fin (2^h) → Tree,
        (∀ u, (family u).1.card < L) ∧
        ∀ j : Nat, (∑ u, score (family u) j) = 2^h * target.coeff j := by
  classical
  intro k hk F W ix rot spacing s t name constant out H Tree predict g h L hL Z w advance walk path cycle B M d a target score
  exact (by
    obtain ⟨hu, hl⟩ := cubeCycle hk hL
    obtain ⟨D, e, hdecomp⟩ := addLinear_out hk s t spacing name constant
    let lin := (kernelMixer hk spacing).comp (rotateLinear hk s)
    have hm : Nat.card lin.ker = 2 ^ h := rotated_kernel_card hk s spacing
    have hout : out = fun x => mixerQuad (cycleA hk) (cycleB hk) (lin x) + D x + e :=
      funext hdecomp
    obtain ⟨hup, hlow⟩ := mixer_transfer (cycleA hk) (cycleB hk) lin D e (fun j => target.coeff j) hm
      (B := L) (fun tr ht j => by rw [← treeScore_mixer]; exact hu tr ht j) (by
        obtain ⟨tr, ht, hr⟩ := hl
        refine ⟨tr, ht, ?_⟩
        intro j
        rw [← treeScore_mixer]
        exact hr j)
    have hs (tr : Tree) (j : ℕ) : score tr j = ∑ x, mixerValue out tr j x := rfl
    constructor
    · intro tr hcard j
      apply Nat.le_min.mpr
      constructor
      · calc
          score tr j = treeScore out tr j := by rw [hs, treeScore_mixer]
          _ ≤ 2^k * Nat.choose k j := by
            simpa [treeScore, Cube, Bit, ZMod.card] using
              auditScore_universal (fun x => hitsEq (evalTree tr x) (out x)) j
      · rw [hs, hout]
        exact hup tr hcard j
    · obtain ⟨fam, hbudget, hsum⟩ := hlow
      refine ⟨fam, hbudget, ?_⟩
      intro j
      simp_rw [hs, hout]
      exact hsum j)
