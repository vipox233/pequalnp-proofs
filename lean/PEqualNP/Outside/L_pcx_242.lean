import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_242_aux

open MvPolynomial PEqualNP.ProofComplexity

abbrev Poly (n : ℕ) := MvPolynomial (Fin n) (ZMod 2)

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> decide

theorem add_self_eq_zero {n : ℕ} (p : Poly n) : p + p = 0 := by
  ext d
  rw [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero]
  exact zmod2_add_self (p.coeff d)

theorem zmod2_eq_one_of_ne_zero {c : ZMod 2} (h : c ≠ 0) : c = 1 := by
  fin_cases c
  · exact absurd rfl h
  · rfl

theorem coeff_add' {n : ℕ} (p q : Poly n) (d : Fin n →₀ ℕ) :
    (p + q).coeff d = p.coeff d + q.coeff d := by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

noncomputable def indF {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  ∑ i ∈ S, Finsupp.single i 1

theorem indF_apply {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    indF S i = if i ∈ S then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [indF]
  | @insert j S hj ih =>
    unfold indF
    rw [Finset.sum_insert hj, Finsupp.add_apply, Finsupp.single_apply]
    change (if j = i then 1 else 0) + indF S i = if i ∈ insert j S then 1 else 0
    rw [ih]
    by_cases hji : j = i
    · subst hji
      simp [hj]
    · have hij : i ≠ j := Ne.symm hji
      simp [hji, hij]

theorem indF_support {n : ℕ} (S : Finset (Fin n)) : (indF S).support = S := by
  ext i
  rw [Finsupp.mem_support_iff, indF_apply]
  by_cases hi : i ∈ S <;> simp [hi]

theorem indF_sum {n : ℕ} (S : Finset (Fin n)) : (indF S).sum (fun _ k => k) = S.card := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  simp only [indF_apply, Finset.sum_boole, Nat.cast_id]
  congr 1
  ext i
  simp

theorem indF_inj {n : ℕ} {S T : Finset (Fin n)} (h : indF S = indF T) : S = T := by
  rw [← indF_support S, ← indF_support T, h]

noncomputable def mon {n : ℕ} (S : Finset (Fin n)) : Poly n :=
  ∏ i ∈ S, X i

theorem mon_eq_monomial {n : ℕ} (S : Finset (Fin n)) : mon S = monomial (indF S) 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp [mon, indF, monomial_zero']
  | @insert i S hi ih =>
    rw [mon, Finset.prod_insert hi, ← mon, ih, X, monomial_mul_monomial, mul_one]
    congr 1
    unfold indF
    rw [Finset.sum_insert hi]

theorem totalDegree_mon_le {n : ℕ} (S : Finset (Fin n)) : (mon S).totalDegree ≤ S.card := by
  rw [mon_eq_monomial]
  refine (totalDegree_monomial_le (indF S) (1 : ZMod 2)).trans ?_
  change (indF S).sum (fun _ k => k) ≤ S.card
  rw [indF_sum]

theorem mon_mul_disjoint {n : ℕ} {S T : Finset (Fin n)} (h : Disjoint S T) :
    mon S * mon T = mon (S ∪ T) := by
  unfold mon
  rw [Finset.prod_union h]

theorem coeff_mon {n : ℕ} (S T : Finset (Fin n)) :
    (mon S).coeff (indF T) = if S = T then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  by_cases h : S = T
  · subst h; simp
  · have hne : indF S ≠ indF T := fun e => h (indF_inj e)
    simp [h, hne]

noncomputable def ml {n : ℕ} (d : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  d.mapRange (fun k => min k 1) rfl

theorem ml_eq_indF_support {n : ℕ} (d : Fin n →₀ ℕ) : ml d = indF d.support := by
  ext i
  rw [ml, Finsupp.mapRange_apply, indF_apply]
  by_cases h : d i = 0
  · have hns : i ∉ d.support := Finsupp.notMem_support_iff.mpr h
    simp [h, hns]
  · have hs : i ∈ d.support := Finsupp.mem_support_iff.mpr h
    simp only [hs, ite_true]
    omega

noncomputable def nf {n : ℕ} (p : Poly n) : Poly n :=
  ∑ d ∈ p.support, monomial (ml d) (p.coeff d)

theorem nf_eq_sum_indF {n : ℕ} (p : Poly n) :
    nf p = ∑ d ∈ p.support, monomial (indF d.support) (p.coeff d) := by
  unfold nf
  refine Finset.sum_congr rfl fun d _ => by rw [ml_eq_indF_support]

theorem nf_monomial {n : ℕ} (d : Fin n →₀ ℕ) (c : ZMod 2) :
    nf (monomial d c) = monomial (indF d.support) c := by
  by_cases hc : c = 0
  · subst hc
    simp [nf]
  · rw [nf_eq_sum_indF, support_monomial, ite_eq_right_of_eq_false _ _ (eq_false hc),
      Finset.sum_singleton, coeff_monomial, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

theorem nf_add {n : ℕ} (p q : Poly n) : nf (p + q) = nf p + nf q := by
  classical
  have aux : ∀ (s : Finset (Fin n →₀ ℕ)) (r : Poly n), r.support ⊆ s →
      nf r = ∑ d ∈ s, monomial (indF d.support) (r.coeff d) := by
    intro s r hs
    rw [nf_eq_sum_indF]
    apply Finset.sum_subset hs
    intro d _ hd
    have h0 : r.coeff d = 0 := notMem_support_iff.mp hd
    rw [h0, map_zero]
  let s := p.support ∪ q.support
  have hpq : (p + q).support ⊆ s := support_add
  rw [aux s (p + q) hpq, aux s p Finset.subset_union_left, aux s q Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [coeff_add', map_add]

theorem nf_zero {n : ℕ} : nf (0 : Poly n) = 0 := by
  simp [nf]

theorem nf_sum {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Poly n) :
    nf (∑ a ∈ s, f a) = ∑ a ∈ s, nf (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [nf_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, nf_add, ih]

theorem nf_mul_monomial {n : ℕ} (d1 d2 : Fin n →₀ ℕ) (c1 c2 : ZMod 2) :
    nf (monomial d1 c1 * monomial d2 c2) = monomial (indF (d1.support ∪ d2.support)) (c1 * c2) := by
  rw [monomial_mul_monomial, nf_monomial]
  apply congrArg (fun s => monomial (indF s) (c1 * c2))
  ext i
  rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff,
    Finsupp.mem_support_iff, Finsupp.add_apply]
  omega

theorem nf_mul_boolAx {n : ℕ} (p : Poly n) (v : Fin n) :
    nf (p * (X v * X v + X v)) = 0 := by
  rw [p.as_sum, Finset.sum_mul, nf_sum]
  apply Finset.sum_eq_zero
  intro d _
  rw [mul_add, nf_add]
  have h1 : (X v : Poly n) * X v = monomial (Finsupp.single v 2) 1 := by
    rw [X, monomial_mul_monomial, mul_one, ← Finsupp.single_add]
  have h2 : (X v : Poly n) = monomial (Finsupp.single v 1) 1 := rfl
  rw [h1, h2, nf_mul_monomial, nf_mul_monomial]
  have hsupp : (Finsupp.single v 2).support = (Finsupp.single v 1).support := by
    ext i
    simp
  rw [hsupp, add_self_eq_zero]

theorem nf_monomial_mul_mon {n : ℕ} (d : Fin n →₀ ℕ) (S : Finset (Fin n)) :
    nf (monomial d (1 : ZMod 2) * mon S) = mon (d.support ∪ S) := by
  rw [mon_eq_monomial, nf_mul_monomial, mul_one, indF_support, mon_eq_monomial]

theorem card_support_le_sum {n : ℕ} (d : Fin n →₀ ℕ) : d.support.card ≤ d.sum (fun _ k => k) := by
  rw [Finsupp.sum]
  calc d.support.card = ∑ _i ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hne : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      omega

theorem totalDegree_X_le_one {n : ℕ} (j : Fin n) : (X j : Poly n).totalDegree ≤ 1 := by
  rw [X]
  exact (totalDegree_monomial_le (Finsupp.single j 1) (1 : ZMod 2)).trans (by simp)

theorem totalDegree_clausePoly_le {n : ℕ} (C : Clause (Fin n)) :
    (clausePoly C).totalDegree ≤ C.card := by
  classical
  induction C using Finset.induction_on with
  | empty => simp [clausePoly]
  | @insert l C hl ih =>
    rw [clausePoly, Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    have h1 := totalDegree_mul (if l.2 = true then 1 + X l.1 else X l.1 : Poly n) (clausePoly C)
    have h2 : (if l.2 = true then 1 + X l.1 else X l.1 : Poly n).totalDegree ≤ 1 := by
      cases l.2
      · simp only [Bool.false_eq_true, ite_false]; exact totalDegree_X_le_one l.1
      · simp only [ite_true]
        exact (totalDegree_add (1 : Poly n) (X l.1)).trans (max_le (by simp) (totalDegree_X_le_one l.1))
    rw [clausePoly] at h1 ih
    omega

def clauseOf {n : ℕ} (pred : Fin n → Finset (Fin n)) (v : Fin n) : Clause (Fin n) :=
  insert (v, true) ((pred v).image (fun u => (u, false)))

theorem clausePoly_clauseOf {n : ℕ} (pred : Fin n → Finset (Fin n)) (v : Fin n)
    (hv : v ∉ pred v) :
    clausePoly (clauseOf pred v) = mon (pred v) + mon (insert v (pred v)) := by
  classical
  unfold clausePoly clauseOf
  have hni : (v, true) ∉ (pred v).image (fun u => (u, false)) := by
    rw [Finset.mem_image]
    rintro ⟨u, _, hu⟩
    have := (Prod.mk.inj hu).2
    simp at this
  rw [Finset.prod_insert hni]
  simp only [ite_true]
  have himg : ∏ l ∈ (pred v).image (fun u => (u, false)),
      (if l.2 = true then (1 : Poly n) + X l.1 else X l.1) = mon (pred v) := by
    rw [Finset.prod_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    unfold mon
    refine Finset.prod_congr rfl fun u _ => by simp
  rw [himg, add_mul, one_mul]
  congr 1
  unfold mon
  rw [Finset.prod_insert hv]

theorem totalDegree_clauseOf {n : ℕ} (pred : Fin n → Finset (Fin n)) (v : Fin n)
    (hv : v ∉ pred v) :
    (clausePoly (clauseOf pred v)).totalDegree = (pred v).card + 1 := by
  apply le_antisymm
  · have h1 := totalDegree_clausePoly_le (clauseOf pred v)
    have h2 : (clauseOf pred v).card ≤ (pred v).card + 1 := by
      unfold clauseOf
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)
    omega
  · rw [clausePoly_clauseOf pred v hv]
    have hmem : indF (insert v (pred v)) ∈ (mon (pred v) + mon (insert v (pred v))).support := by
      rw [mem_support_iff, coeff_add', coeff_mon, coeff_mon]
      have hne : pred v ≠ insert v (pred v) := by
        intro h
        apply hv
        rw [h]
        exact Finset.mem_insert_self v _
      simp [hne]
    have hle : (indF (insert v (pred v))).sum (fun _ k => k) ≤
        (mon (pred v) + mon (insert v (pred v))).totalDegree :=
      Finset.le_sup (f := fun s : Fin n →₀ ℕ => s.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_insert_of_notMem hv] at hle
    exact hle

def pin1 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, true), (s, true)}
def pin2 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, false), (s, true)}
def pin3 {n : ℕ} (s t : Fin n) : Clause (Fin n) := {(t, false), (s, false)}

theorem clausePoly_pin1 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin1 s t) = (1 + X s) + X t + X t * X s := by
  unfold clausePoly pin1
  have hne : (t, true) ≠ (s, true) := fun h => hst (Prod.mk.inj h).1.symm
  rw [Finset.prod_pair hne]
  simp only [ite_true]
  ring

theorem clausePoly_pin2 {n : ℕ} {s t : Fin n} :
    clausePoly (pin2 s t) = X t + X t * X s := by
  unfold clausePoly pin2
  have hne : (t, false) ≠ (s, true) := fun h => by have := (Prod.mk.inj h).2; simp at this
  rw [Finset.prod_pair hne]
  simp only [Bool.false_eq_true, ite_false, ite_true]
  ring

theorem clausePoly_pin3 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    clausePoly (pin3 s t) = X t * X s := by
  unfold clausePoly pin3
  have hne : (t, false) ≠ (s, false) := fun h => hst (Prod.mk.inj h).1.symm
  rw [Finset.prod_pair hne]
  simp only [Bool.false_eq_true, ite_false]

theorem totalDegree_pin1 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    (clausePoly (pin1 s t)).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans (by unfold pin1; exact Finset.card_le_two)
  · rw [clausePoly_pin1 hst]
    have hts : t ≠ s := hst.symm
    have heq : (1 + X s + X t + X t * X s : Poly n) =
        mon ∅ + mon {s} + mon {t} + mon {t, s} := by
      simp [mon, Finset.prod_pair hts]
    rw [heq]
    have hmem : indF ({t, s} : Finset (Fin n)) ∈
        (mon ∅ + mon {s} + mon {t} + mon {t, s}).support := by
      rw [mem_support_iff, coeff_add', coeff_add', coeff_add', coeff_mon, coeff_mon, coeff_mon, coeff_mon]
      have h1 : (∅ : Finset (Fin n)) ≠ {t, s} := (Finset.insert_ne_empty _ _).symm
      have h2 : ({s} : Finset (Fin n)) ≠ {t, s} := by
        intro h
        have : t ∈ ({s} : Finset (Fin n)) := by rw [h]; simp
        exact hts (Finset.mem_singleton.mp this)
      have h3 : ({t} : Finset (Fin n)) ≠ {t, s} := by
        intro h
        have : s ∈ ({t} : Finset (Fin n)) := by rw [h]; simp
        exact hst (Finset.mem_singleton.mp this)
      simp [h1, h2, h3]
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair hts] at hle
    exact hle

theorem totalDegree_pin2 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    (clausePoly (pin2 s t)).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans (by unfold pin2; exact Finset.card_le_two)
  · rw [clausePoly_pin2]
    have hts : t ≠ s := hst.symm
    have heq : (X t + X t * X s : Poly n) = mon {t} + mon {t, s} := by
      simp [mon, Finset.prod_pair hts]
    rw [heq]
    have hmem : indF ({t, s} : Finset (Fin n)) ∈ (mon {t} + mon {t, s}).support := by
      rw [mem_support_iff, coeff_add', coeff_mon, coeff_mon]
      have h3 : ({t} : Finset (Fin n)) ≠ {t, s} := by
        intro h
        have : s ∈ ({t} : Finset (Fin n)) := by rw [h]; simp
        exact hst (Finset.mem_singleton.mp this)
      simp [h3]
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair hts] at hle
    exact hle

theorem totalDegree_pin3 {n : ℕ} {s t : Fin n} (hst : s ≠ t) :
    (clausePoly (pin3 s t)).totalDegree = 2 := by
  apply le_antisymm
  · exact (totalDegree_clausePoly_le _).trans (by unfold pin3; exact Finset.card_le_two)
  · rw [clausePoly_pin3 hst]
    have hts : t ≠ s := hst.symm
    have heq : (X t * X s : Poly n) = mon {t, s} := by
      simp [mon, Finset.prod_pair hts]
    rw [heq]
    have hmem : indF ({t, s} : Finset (Fin n)) ∈ (mon {t, s}).support := by
      rw [mem_support_iff, coeff_mon]
      simp
    have hle := Finset.le_sup (f := fun e : Fin n →₀ ℕ => e.sum (fun _ k => k)) hmem
    rw [indF_sum, Finset.card_pair hts] at hle
    exact hle

def enabled {n : ℕ} (s : Fin n) (pred : Fin n → Finset (Fin n))
    (z : Option (Fin n)) (current : Finset (Option (Fin n))) : Prop :=
  z = none ∨ ∃ i : Fin n, z = some i ∧
    ((i = s ∧ none ∈ current) ∨ (i ≠ s ∧ ∀ u ∈ pred i, some u ∈ current))

def up {n : ℕ} (d : ℕ) (s : Fin n) (pred : Fin n → Finset (Fin n))
    (A B : Finset (Option (Fin n))) : Prop :=
  B.card ≤ d ∧ ∃ z, z ∉ A ∧ B = insert z A ∧ enabled s pred z A

def stepRel {n : ℕ} (d : ℕ) (s : Fin n) (pred : Fin n → Finset (Fin n))
    (U V : Finset (Option (Fin n))) : Prop :=
  up d s pred U V ∨ up d s pred V U

theorem stepRel_symm {n : ℕ} {d : ℕ} {s : Fin n} {pred : Fin n → Finset (Fin n)}
    {U V : Finset (Option (Fin n))} (h : stepRel d s pred U V) : stepRel d s pred V U :=
  h.symm

theorem rtg_symm {n : ℕ} {d : ℕ} {s : Fin n} {pred : Fin n → Finset (Fin n)}
    {U V : Finset (Option (Fin n))}
    (h : Relation.ReflTransGen (stepRel d s pred) U V) :
    Relation.ReflTransGen (stepRel d s pred) V U := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head (stepRel_symm hstep) ih

theorem bridge_source {n : ℕ} {d : ℕ} {s : Fin n} {pred : Fin n → Finset (Fin n)}
    (M : Finset (Fin n)) (hns : s ∉ M) (hcard : M.card + 2 ≤ d) :
    Relation.ReflTransGen (stepRel d s pred) (M.image some) ((insert s M).image some) := by
  let A0 := M.image some
  let A1 := insert none A0
  let A2 := insert (some s) A1
  let B0 := (insert s M).image some
  have hnone0 : none ∉ A0 := by
    simp only [A0, Finset.mem_image, reduceCtorEq, and_false, exists_false, not_false_eq_true]
  have hs1 : some s ∉ A1 := by
    simp only [A1, A0, Finset.mem_insert, Finset.mem_image, Option.some.injEq, reduceCtorEq,
      false_or, not_exists, not_and]
    intro x hx hxs
    exact hns (hxs ▸ hx)
  have hnoneB : none ∉ B0 := by
    simp only [B0, Finset.mem_image, reduceCtorEq, and_false, exists_false, not_false_eq_true]
  have hA0c : A0.card = M.card := Finset.card_image_of_injective M (Option.some_injective (Fin n))
  have hA1c : A1.card = M.card + 1 := by rw [Finset.card_insert_of_notMem hnone0, hA0c]
  have hA2c : A2.card = M.card + 2 := by rw [Finset.card_insert_of_notMem hs1, hA1c]
  have hA2eq : A2 = insert none B0 := by
    ext z
    simp only [A2, A1, A0, B0, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | rfl | ⟨x, hx, rfl⟩)
      · right; exact ⟨s, Or.inl rfl, rfl⟩
      · left; rfl
      · right; exact ⟨x, Or.inr hx, rfl⟩
    · rintro (rfl | ⟨x, rfl | hx, rfl⟩)
      · right; left; rfl
      · left; rfl
      · right; right; exact ⟨x, hx, rfl⟩
  have hstep1 : up d s pred A0 A1 := ⟨by omega, none, hnone0, rfl, Or.inl rfl⟩
  have hstep2 : up d s pred A1 A2 :=
    ⟨by omega, some s, hs1, rfl, Or.inr ⟨s, rfl, Or.inl ⟨rfl, Finset.mem_insert_self none A0⟩⟩⟩
  have hstep3 : up d s pred B0 A2 := ⟨by omega, none, hnoneB, hA2eq, Or.inl rfl⟩
  exact Relation.ReflTransGen.tail
    (Relation.ReflTransGen.tail (Relation.ReflTransGen.single (Or.inl hstep1)) (Or.inl hstep2))
    (Or.inr hstep3)

def StaticRep {n : ℕ} (axioms : Finset (Clause (Fin n))) (budget : ℕ) (target : Poly n) : Prop :=
  ∃ (q : Clause (Fin n) → Poly n) (b : Fin n → Poly n),
    (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (clausePoly C).totalDegree ≤ budget) ∧
    (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
    axioms.sum (fun C => q C * clausePoly C) + (∑ v, b v * (X v * X v + X v)) = target

theorem staticRep_zero {n : ℕ} (axioms : Finset (Clause (Fin n))) (budget : ℕ) :
    StaticRep axioms budget 0 :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => Or.inl rfl, fun _ => Or.inl rfl, by simp⟩

theorem staticRep_add {n : ℕ} {axioms : Finset (Clause (Fin n))} {budget : ℕ} {p1 p2 : Poly n}
    (h1 : StaticRep axioms budget p1) (h2 : StaticRep axioms budget p2) :
    StaticRep axioms budget (p1 + p2) := by
  obtain ⟨q1, b1, hq1, hb1, heq1⟩ := h1
  obtain ⟨q2, b2, hq2, hb2, heq2⟩ := h2
  refine ⟨fun C => q1 C + q2 C, fun v => b1 v + b2 v, ?_, ?_, ?_⟩
  · intro C hC
    dsimp only
    rcases hq1 C hC with h10 | h1d <;> rcases hq2 C hC with h20 | h2d
    · left; rw [h10, h20, add_zero]
    · right; rw [h10, zero_add]; exact h2d
    · right; rw [h20, add_zero]; exact h1d
    · right
      have := totalDegree_add (q1 C) (q2 C)
      omega
  · intro v
    dsimp only
    rcases hb1 v with h10 | h1d <;> rcases hb2 v with h20 | h2d
    · left; rw [h10, h20, add_zero]
    · right; rw [h10, zero_add]; exact h2d
    · right; rw [h20, add_zero]; exact h1d
    · right
      have := totalDegree_add (b1 v) (b2 v)
      omega
  · rw [← heq1, ← heq2]
    have hsum1 : axioms.sum (fun C => (q1 C + q2 C) * clausePoly C) =
        axioms.sum (fun C => q1 C * clausePoly C) + axioms.sum (fun C => q2 C * clausePoly C) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun C _ => add_mul _ _ _
    have hsum2 : (∑ v : Fin n, (b1 v + b2 v) * (X v * X v + X v)) =
        (∑ v : Fin n, b1 v * (X v * X v + X v)) + (∑ v : Fin n, b2 v * (X v * X v + X v)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ => add_mul _ _ _
    rw [hsum1, hsum2]
    ring

theorem staticRep_single {n : ℕ} {axioms : Finset (Clause (Fin n))} {budget : ℕ}
    {C : Clause (Fin n)} (hC : C ∈ axioms) (r : Poly n)
    (hdeg : r.totalDegree + (clausePoly C).totalDegree ≤ budget) :
    StaticRep axioms budget (r * clausePoly C) := by
  classical
  refine ⟨fun C' => if C' = C then r else 0, fun _ => 0, ?_, fun _ => Or.inl rfl, ?_⟩
  · intro C' _
    by_cases h : C' = C
    · subst h; right; simpa using hdeg
    · left; simp [h]
  · simp only [zero_mul, Finset.sum_const_zero, add_zero]
    rw [Finset.sum_eq_single C]
    · simp
    · intro C' _ hne; simp [hne]
    · intro h; exact absurd hC h

def proj {n : ℕ} (U : Finset (Option (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter (fun i : Fin n => some i ∈ U)

theorem proj_empty {n : ℕ} : proj (∅ : Finset (Option (Fin n))) = ∅ := by
  ext i; simp [proj]

theorem proj_image_some {n : ℕ} (S : Finset (Fin n)) : proj (S.image some) = S := by
  ext i
  simp [proj]

theorem card_proj_le {n : ℕ} (U : Finset (Option (Fin n))) : (proj U).card ≤ U.card := by
  have hsub : (proj U).image some ⊆ U := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp hi).2
  calc (proj U).card = ((proj U).image some).card :=
        (Finset.card_image_of_injective _ (Option.some_injective (Fin n))).symm
    _ ≤ U.card := Finset.card_le_card hsub

theorem card_proj_add_one_le_of_none {n : ℕ} (U : Finset (Option (Fin n))) (hnone : none ∈ U) :
    (proj U).card + 1 ≤ U.card := by
  have hsub : insert none ((proj U).image some) ⊆ U := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hnone
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hi).2
  have hni : none ∉ (proj U).image some := by simp
  calc (proj U).card + 1 = ((proj U).image some).card + 1 := by
        rw [Finset.card_image_of_injective _ (Option.some_injective (Fin n))]
    _ = (insert none ((proj U).image some)).card := (Finset.card_insert_of_notMem hni).symm
    _ ≤ U.card := Finset.card_le_card hsub

theorem dir_forward {n d : ℕ} {s t : Fin n} (hst : s ≠ t)
    (pred : Fin n → Finset (Fin n)) (hpred : ∀ v, v ≠ s → v ∉ pred v)
    (hstat : StaticRep ((Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}) d 1) :
    ∃ S : Finset (Fin n), t ∈ S ∧ (S.card < d ∨ s ∈ S) ∧
      Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some) := by
  classical
  by_contra hno
  let F := (Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}
  let Comp : Finset (Fin n) → Prop := fun S =>
    Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some)
  let chi : Poly n → ZMod 2 := fun p =>
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => Comp S), (nf p).coeff (indF S)
  have hchi_add : ∀ p1 p2 : Poly n, chi (p1 + p2) = chi p1 + chi p2 := by
    intro p1 p2
    simp only [chi, nf_add, coeff_add', Finset.sum_add_distrib]
  have hchi_zero : chi 0 = 0 := by
    simp [chi, nf_zero]
  have hchi_sum : ∀ {ι : Type} (I : Finset ι) (f : ι → Poly n),
      chi (∑ a ∈ I, f a) = ∑ a ∈ I, chi (f a) := by
    intro ι I f
    induction I using Finset.induction_on with
    | empty => simp [hchi_zero]
    | @insert a I ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hchi_add, ih]
  have hchi_mon : ∀ S : Finset (Fin n), chi (mon S) = if Comp S then 1 else 0 := by
    intro S
    have hnf_mon : nf (mon S) = mon S := by
      rw [mon_eq_monomial, nf_monomial, indF_support]
    simp only [chi, hnf_mon, coeff_mon]
    by_cases hS : Comp S
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hS)]
      have hmem : S ∈ Finset.univ.filter (fun T : Finset (Fin n) => Comp T) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩
      rw [Finset.sum_eq_single S]
      · simp
      · intro T _ hTS; simp [hTS.symm]
      · intro h; exact absurd hmem h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hS)]
      apply Finset.sum_eq_zero
      intro T hT
      have hTS : S ≠ T := by
        intro e; subst e; exact hS (Finset.mem_filter.mp hT).2
      simp [hTS]
  have hchi_nf : ∀ p : Poly n, chi p = chi (nf p) := by
    intro p
    have hnf2 : nf (nf p) = nf p := by
      conv_lhs => rw [nf_eq_sum_indF p]
      rw [nf_sum]
      conv_rhs => rw [nf_eq_sum_indF p]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [nf_monomial, indF_support]
    simp only [chi, hnf2]
  have hchi_one : chi 1 = 1 := by
    have h1 : (1 : Poly n) = mon ∅ := by simp [mon]
    rw [h1, hchi_mon]
    have hC0 : Comp ∅ := by
      change Relation.ReflTransGen (stepRel d s pred) ∅ ((∅ : Finset (Fin n)).image some)
      simp [Relation.ReflTransGen.refl]
    simp [hC0]
  have hchi_bool : ∀ (p : Poly n) (v : Fin n), chi (p * (X v * X v + X v)) = 0 := by
    intro p v
    rw [hchi_nf, nf_mul_boolAx, hchi_zero]
  have hchi_clause : ∀ v ∈ Finset.univ.erase s, ∀ q : Poly n,
      (q = 0 ∨ q.totalDegree + (clausePoly (clauseOf pred v)).totalDegree ≤ d) →
      chi (q * clausePoly (clauseOf pred v)) = 0 := by
    intro v hv q hq
    rcases hq with rfl | hdeg
    · simp [hchi_zero]
    · have hvs : v ≠ s := (Finset.mem_erase.mp hv).1
      have hv_np : v ∉ pred v := hpred v hvs
      rw [totalDegree_clauseOf pred v hv_np] at hdeg
      rw [q.as_sum, Finset.sum_mul, hchi_sum]
      apply Finset.sum_eq_zero
      intro e he
      have hc : q.coeff e = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp he)
      rw [hc]
      have hed : e.sum (fun _ k => k) ≤ q.totalDegree :=
        Finset.le_sup (f := fun m : Fin n →₀ ℕ => m.sum (fun _ k => k)) he
      have hMcard : e.support.card + (pred v).card + 1 ≤ d := by
        have := card_support_le_sum e
        omega
      rw [hchi_nf, clausePoly_clauseOf pred v hv_np, mul_add, nf_add,
        nf_monomial_mul_mon, nf_monomial_mul_mon, hchi_add, hchi_mon, hchi_mon]
      set A := e.support ∪ pred v
      set B := e.support ∪ insert v (pred v)
      have hBeq : B = insert v A := by
        ext x; simp only [A, B, Finset.mem_union, Finset.mem_insert]; tauto
      by_cases hvA : v ∈ A
      · have hBA : B = A := by rw [hBeq, Finset.insert_eq_of_mem hvA]
        rw [hBA]
        exact zmod2_add_self _
      · have hBcard : B.card ≤ d := by
          rw [hBeq, Finset.card_insert_of_notMem hvA]
          have hA_le : A.card ≤ e.support.card + (pred v).card := Finset.card_union_le _ _
          omega
        have hup : up d s pred (A.image some) (B.image some) := by
          refine ⟨?_, some v, ?_, ?_, ?_⟩
          · rw [Finset.card_image_of_injective _ (Option.some_injective (Fin n))]
            exact hBcard
          · simp [hvA]
          · rw [hBeq, Finset.image_insert]
          · right
            refine ⟨v, rfl, Or.inr ⟨hvs, fun u hu => ?_⟩⟩
            exact Finset.mem_image.mpr ⟨u, Finset.mem_union_right _ hu, rfl⟩
        have hiff : Comp A ↔ Comp B := by
          constructor
          · intro hA; exact Relation.ReflTransGen.tail hA (Or.inl hup)
          · intro hB; exact Relation.ReflTransGen.tail hB (Or.inr hup)
        by_cases hA : Comp A
        · have hB := hiff.mp hA
          simp only [hA, hB, ite_true]
          exact zmod2_add_self 1
        · have hB : ¬ Comp B := fun h => hA (hiff.mpr h)
          simp [hA, hB]
  have hchi_pin_gen : ∀ (e : Fin n →₀ ℕ), e.support.card + 2 ≤ d →
      chi (monomial e (1 : ZMod 2) * (1 + X s)) = 0 ∧
      chi (monomial e (1 : ZMod 2) * X t) = 0 ∧
      chi (monomial e (1 : ZMod 2) * (X t * X s)) = 0 := by
    intro e hec
    refine ⟨?_, ?_, ?_⟩
    · have h1s : (1 + X s : Poly n) = mon ∅ + mon {s} := by simp [mon]
      rw [hchi_nf, h1s, mul_add, nf_add, nf_monomial_mul_mon, nf_monomial_mul_mon,
        hchi_add, hchi_mon, hchi_mon]
      simp only [Finset.union_empty, Finset.union_singleton]
      by_cases hsM : s ∈ e.support
      · rw [Finset.insert_eq_of_mem hsM]
        exact zmod2_add_self _
      · have hbr := bridge_source (d := d) (s := s) (pred := pred) e.support hsM hec
        have hiff : Comp e.support ↔ Comp (insert s e.support) :=
          ⟨fun h => h.trans hbr, fun h => h.trans (rtg_symm hbr)⟩
        by_cases hM : Comp e.support
        · have hM' := hiff.mp hM
          simp only [hM, hM', ite_true]
          exact zmod2_add_self 1
        · have hM' : ¬ Comp (insert s e.support) := fun h => hM (hiff.mpr h)
          simp [hM, hM']
    · have hXt : (X t : Poly n) = mon {t} := by simp [mon]
      rw [hchi_nf, hXt, nf_monomial_mul_mon, Finset.union_singleton, hchi_mon]
      have hnc : ¬ Comp (insert t e.support) := by
        intro hc
        apply hno
        refine ⟨insert t e.support, Finset.mem_insert_self t _, Or.inl ?_, hc⟩
        have := Finset.card_insert_le t e.support
        omega
      simp [hnc]
    · have hXts : (X t * X s : Poly n) = mon {t, s} := by simp [mon, Finset.prod_pair hst.symm]
      rw [hchi_nf, hXts, nf_monomial_mul_mon, hchi_mon]
      have hnc : ¬ Comp (e.support ∪ {t, s}) := by
        intro hc
        apply hno
        refine ⟨e.support ∪ {t, s}, Finset.mem_union_right _ (Finset.mem_insert_self t {s}),
          Or.inr (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self s))), hc⟩
      rw [ite_eq_right_of_eq_false _ _ (eq_false hnc)]
  obtain ⟨q, b, hq, hb, heq⟩ := hstat
  have hchi_lhs : chi (F.sum (fun C => q C * clausePoly C) + ∑ v, b v * (X v * X v + X v)) = 0 := by
    rw [hchi_add, hchi_sum, hchi_sum]
    have hb0 : ∑ v : Fin n, chi (b v * (X v * X v + X v)) = 0 :=
      Finset.sum_eq_zero fun v _ => hchi_bool (b v) v
    have hF0 : ∑ C ∈ F, chi (q C * clausePoly C) = 0 := by
      apply Finset.sum_eq_zero
      intro C hCF
      rcases Finset.mem_union.mp hCF with hC1 | hC2
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hC1
        exact hchi_clause v hv (q (clauseOf pred v)) (hq _ hCF)
      · have hqC := hq C hCF
        rcases hqC with hq0 | hqdeg
        · rw [hq0, zero_mul, hchi_zero]
        · have hdeg2 : (q C).totalDegree + 2 ≤ d := by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hC2
            rcases hC2 with rfl | rfl | rfl
            · rw [totalDegree_pin1 hst] at hqdeg; exact hqdeg
            · rw [totalDegree_pin2 hst] at hqdeg; exact hqdeg
            · rw [totalDegree_pin3 hst] at hqdeg; exact hqdeg
          rw [(q C).as_sum, Finset.sum_mul, hchi_sum]
          apply Finset.sum_eq_zero
          intro e he
          have hc : (q C).coeff e = 1 := zmod2_eq_one_of_ne_zero (mem_support_iff.mp he)
          rw [hc]
          have hed : e.sum (fun _ k => k) ≤ (q C).totalDegree :=
            Finset.le_sup (f := fun m : Fin n →₀ ℕ => m.sum (fun _ k => k)) he
          have hMcard : e.support.card + 2 ≤ d := by
            have := card_support_le_sum e
            omega
          obtain ⟨hp1, hp2, hp3⟩ := hchi_pin_gen e hMcard
          simp only [Finset.mem_insert, Finset.mem_singleton] at hC2
          rcases hC2 with rfl | rfl | rfl
          · rw [clausePoly_pin1 hst, mul_add, mul_add, hchi_add, hchi_add, hp1, hp2, hp3]
            simp
          · rw [clausePoly_pin2, mul_add, hchi_add, hp2, hp3]
            simp
          · rw [clausePoly_pin3 hst, hp3]
    rw [hF0, hb0, add_zero]
  rw [heq, hchi_one] at hchi_lhs
  exact one_ne_zero hchi_lhs

theorem dir_backward {n d : ℕ} {s t : Fin n} (hst : s ≠ t)
    (pred : Fin n → Finset (Fin n)) (hpred : ∀ v, v ≠ s → v ∉ pred v)
    (S : Finset (Fin n)) (htS : t ∈ S) (hcond : S.card < d ∨ s ∈ S)
    (hpath : Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some)) :
    StaticRep ((Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}) d 1 := by
  let F := (Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}
  have hpin1 : pin1 s t ∈ F := Finset.mem_union_right _ (by simp)
  have hpin2 : pin2 s t ∈ F := Finset.mem_union_right _ (by simp)
  have hpin3 : pin3 s t ∈ F := Finset.mem_union_right _ (by simp)
  have hup_rep : ∀ A B : Finset (Option (Fin n)), up d s pred A B →
      StaticRep F d (mon (proj A) + mon (proj B)) := by
    intro A B ⟨hBcard, z, hzA, hBeq, hen⟩
    subst hBeq
    rcases hen with rfl | ⟨i, rfl, ⟨his_eq, hnone⟩ | ⟨his, hpi⟩⟩
    · have hpeq : proj (insert none A) = proj A := by
        ext x; simp [proj]
      rw [hpeq, add_self_eq_zero]
      exact staticRep_zero F d
    · rw [his_eq] at hzA hBcard ⊢
      have hns : s ∉ proj A := fun h => hzA (Finset.mem_filter.mp h).2
      have hpeq : proj (insert (some s) A) = insert s (proj A) := by
        ext x
        simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Option.some.injEq]
      have hAcard : (proj A).card + 2 ≤ d := by
        have h1 := card_proj_add_one_le_of_none A hnone
        rw [Finset.card_insert_of_notMem hzA] at hBcard
        omega
      have hsum : mon (proj A) + mon (proj (insert (some s) A)) =
          mon (proj A) * clausePoly (pin1 s t) + mon (proj A) * clausePoly (pin2 s t) := by
        rw [hpeq, clausePoly_pin1 hst, clausePoly_pin2]
        have h1 : mon (insert s (proj A)) = X s * mon (proj A) := by
          unfold mon; rw [Finset.prod_insert hns]
        rw [h1]
        have h2 : mon (proj A) * (1 + X s + X t + X t * X s) + mon (proj A) * (X t + X t * X s) =
            mon (proj A) + X s * mon (proj A) +
            (mon (proj A) * (X t + X t * X s) + mon (proj A) * (X t + X t * X s)) := by ring
        rw [h2, add_self_eq_zero, add_zero]
      rw [hsum]
      refine staticRep_add ?_ ?_
      · exact staticRep_single hpin1 (mon (proj A))
          (by rw [totalDegree_pin1 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le _) 2).trans hAcard)
      · exact staticRep_single hpin2 (mon (proj A))
          (by rw [totalDegree_pin2 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le _) 2).trans hAcard)
    · have hni : i ∉ proj A := fun h => hzA (Finset.mem_filter.mp h).2
      have hpeq : proj (insert (some i) A) = insert i (proj A) := by
        ext x
        simp only [proj, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Option.some.injEq]
      have hsub : pred i ⊆ proj A := fun u hu => Finset.mem_filter.mpr ⟨Finset.mem_univ u, hpi u hu⟩
      let R := proj A \ pred i
      have hdisj1 : Disjoint R (pred i) := disjoint_sdiff_self_left
      have hU1 : R ∪ pred i = proj A := Finset.sdiff_union_of_subset hsub
      have hni_R : i ∉ R := fun h => hni (Finset.mem_sdiff.mp h).1
      have hdisj2 : Disjoint R (insert i (pred i)) := Finset.disjoint_insert_right.mpr ⟨hni_R, hdisj1⟩
      have hU2 : R ∪ insert i (pred i) = insert i (proj A) := by
        ext x
        simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (hR | rfl | hp)
          · right; exact (Finset.mem_sdiff.mp hR).1
          · left; rfl
          · right; exact hsub hp
        · rintro (rfl | hA)
          · right; left; rfl
          · by_cases hp : x ∈ pred i
            · right; right; exact hp
            · left; exact Finset.mem_sdiff.mpr ⟨hA, hp⟩
      have hRcard : R.card + ((pred i).card + 1) ≤ d := by
        have h1 : R.card + (pred i).card = (proj A).card := by
          rw [← Finset.card_union_of_disjoint hdisj1, hU1]
        have h2 : (proj A).card + 1 = (proj (insert (some i) A)).card := by
          rw [hpeq, Finset.card_insert_of_notMem hni]
        have h3 := card_proj_le (insert (some i) A)
        omega
      have hcl : clauseOf pred i ∈ F :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨his, Finset.mem_univ i⟩, rfl⟩)
      have heq : mon (proj A) + mon (proj (insert (some i) A)) =
          mon R * clausePoly (clauseOf pred i) := by
        rw [hpeq, clausePoly_clauseOf pred i (hpred i his), mul_add,
          mon_mul_disjoint hdisj1, hU1, mon_mul_disjoint hdisj2, hU2]
      rw [heq]
      refine staticRep_single hcl (mon R) ?_
      rw [totalDegree_clauseOf pred i (hpred i his)]
      exact (Nat.add_le_add_right (totalDegree_mon_le R) _).trans hRcard
  have hpath_rep : ∀ U V : Finset (Option (Fin n)),
      Relation.ReflTransGen (stepRel d s pred) U V →
      StaticRep F d (mon (proj U) + mon (proj V)) := by
    intro U V h
    induction h with
    | refl =>
      rw [add_self_eq_zero]
      exact staticRep_zero F d
    | @tail b c _ hstep ih =>
      have hsrep : StaticRep F d (mon (proj b) + mon (proj c)) := by
        rcases hstep with h1 | h2
        · exact hup_rep b c h1
        · rw [add_comm]
          exact hup_rep c b h2
      have hsum := staticRep_add ih hsrep
      have hcancel : (mon (proj U) + mon (proj b)) + (mon (proj b) + mon (proj c)) =
          mon (proj U) + mon (proj c) := by
        calc (mon (proj U) + mon (proj b)) + (mon (proj b) + mon (proj c))
            = mon (proj U) + (mon (proj b) + mon (proj b)) + mon (proj c) := by ring
          _ = mon (proj U) + 0 + mon (proj c) := by rw [add_self_eq_zero]
          _ = mon (proj U) + mon (proj c) := by ring
      rwa [hcancel] at hsum
  have h1S : StaticRep F d (1 + mon S) := by
    have h := hpath_rep ∅ (S.image some) hpath
    rw [proj_empty, proj_image_some] at h
    simpa [mon] using h
  have hScard : S.card ≤ d := by
    have hne : (S.image some) ≠ ∅ := by
      intro h
      have : some t ∈ (∅ : Finset (Option (Fin n))) := h ▸ Finset.mem_image.mpr ⟨t, htS, rfl⟩
      exact Finset.notMem_empty _ this
    have hcard_gen : ∀ W : Finset (Option (Fin n)),
        Relation.ReflTransGen (stepRel d s pred) ∅ W → W ≠ ∅ → W.card ≤ d := by
      intro W hW hWne
      cases hW with
      | refl => exact absurd rfl hWne
      | tail _ hstep =>
        rcases hstep with ⟨hB, _⟩ | ⟨hB, z, _, hBeq, _⟩
        · exact hB
        · have hle : W.card ≤ (insert z W).card := Finset.card_le_card (Finset.subset_insert _ _)
          rw [← hBeq] at hle
          omega
    have := hcard_gen (S.image some) hpath hne
    rwa [Finset.card_image_of_injective _ (Option.some_injective (Fin n))] at this
  have hS : StaticRep F d (mon S) := by
    rcases hcond with hlt | hsS
    · set R := S.erase t
      have hRcard : R.card + 2 ≤ d := by
        have hR : R.card = S.card - 1 := Finset.card_erase_of_mem htS
        have hpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨t, htS⟩
        omega
      have heq : mon S = mon R * clausePoly (pin2 s t) + mon R * clausePoly (pin3 s t) := by
        rw [clausePoly_pin2, clausePoly_pin3 hst]
        have h1 : mon S = X t * mon R := by
          unfold mon R
          conv_lhs => rw [← Finset.insert_erase htS]
          rw [Finset.prod_insert (Finset.notMem_erase t S)]
        rw [h1]
        have h2 : mon R * (X t + X t * X s) + mon R * (X t * X s) =
            X t * mon R + (mon R * (X t * X s) + mon R * (X t * X s)) := by ring
        rw [h2, add_self_eq_zero, add_zero]
      rw [heq]
      refine staticRep_add ?_ ?_
      · exact staticRep_single hpin2 (mon R)
          (by rw [totalDegree_pin2 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le R) 2).trans hRcard)
      · exact staticRep_single hpin3 (mon R)
          (by rw [totalDegree_pin3 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le R) 2).trans hRcard)
    · set R := (S.erase t).erase s
      have hs_er : s ∈ S.erase t := Finset.mem_erase.mpr ⟨hst, hsS⟩
      have hRcard : R.card + 2 ≤ d := by
        have h1 : R.card = (S.erase t).card - 1 := Finset.card_erase_of_mem hs_er
        have h2 : (S.erase t).card = S.card - 1 := Finset.card_erase_of_mem htS
        have h3 : 2 ≤ S.card := by
          have : ({s, t} : Finset (Fin n)) ⊆ S := by
            intro x hx
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl
            · exact hsS
            · exact htS
          have h4 := Finset.card_le_card this
          rw [Finset.card_pair hst] at h4
          exact h4
        omega
      have heq : mon S = mon R * clausePoly (pin3 s t) := by
        rw [clausePoly_pin3 hst]
        have h1 : mon S = X t * (X s * mon R) := by
          unfold mon R
          conv_lhs => rw [← Finset.insert_erase htS]
          rw [Finset.prod_insert (Finset.notMem_erase t S)]
          congr 1
          conv_lhs => rw [← Finset.insert_erase hs_er]
          rw [Finset.prod_insert (Finset.notMem_erase s (S.erase t))]
        rw [h1]
        ring
      rw [heq]
      exact staticRep_single hpin3 (mon R)
        (by rw [totalDegree_pin3 hst]; exact (Nat.add_le_add_right (totalDegree_mon_le R) 2).trans hRcard)
  have hsum := staticRep_add h1S hS
  have hcancel : (1 + mon S) + mon S = (1 : Poly n) := by
    calc (1 + mon S) + mon S = 1 + (mon S + mon S) := add_assoc _ _ _
      _ = 1 + 0 := by rw [add_self_eq_zero]
      _ = 1 := add_zero 1
  rwa [hcancel] at hsum

theorem main (n d : ℕ) (s t : Fin n) (hst : s ≠ t)
    (pred : Fin n → Finset (Fin n)) (hpred : ∀ v, v ≠ s → v ∉ pred v) :
    StaticRep ((Finset.univ.erase s).image (clauseOf pred) ∪ {pin1 s t, pin2 s t, pin3 s t}) d 1 ↔
      ∃ S : Finset (Fin n), t ∈ S ∧ (S.card < d ∨ s ∈ S) ∧
        Relation.ReflTransGen (stepRel d s pred) ∅ (S.image some) :=
  ⟨dir_forward hst pred hpred, fun ⟨S, htS, hcond, hpath⟩ =>
    dir_backward hst pred hpred S htS hcond hpath⟩

end PEqualNP.Outside.L_pcx_242_aux

theorem PEqualNP.Outside.L_pcx_242 : ∀ (n d : ℕ) (s t : Fin n), s ≠ t →
  ∀ pred : Fin n → Finset (Fin n), (∀ v, v ≠ s → v ∉ pred v) →
  let P := MvPolynomial (Fin n) (ZMod 2)
  let static := fun (axioms : Finset (PEqualNP.ProofComplexity.Clause (Fin n))) (budget : ℕ) =>
    ∃ (q : PEqualNP.ProofComplexity.Clause (Fin n) → P) (b : Fin n → P),
      (∀ C ∈ axioms, q C = 0 ∨ (q C).totalDegree + (PEqualNP.ProofComplexity.clausePoly C).totalDegree ≤ budget) ∧
      (∀ v, b v = 0 ∨ (b v).totalDegree + 2 ≤ budget) ∧
      axioms.sum (fun C => q C * PEqualNP.ProofComplexity.clausePoly C) +
        (∑ v, b v * (MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v)) = 1
  let clause := fun v : Fin n =>
    insert (v,true) ((pred v).image (fun u => (u,false)))
  let pins : Finset (PEqualNP.ProofComplexity.Clause (Fin n)) :=
    {{(t,true),(s,true)}, {(t,false),(s,true)}, {(t,false),(s,false)}}
  let F := (Finset.univ.erase s).image clause ∪ pins
  let enabled := fun (z : Option (Fin n)) (current : Finset (Option (Fin n))) =>
    z = none ∨ ∃ i : Fin n, z = some i ∧
      ((i = s ∧ none ∈ current) ∨ (i ≠ s ∧ ∀ u ∈ pred i, some u ∈ current))
  let up := fun A B : Finset (Option (Fin n)) => B.card ≤ d ∧
    ∃ z, z ∉ A ∧ B = insert z A ∧ enabled z A
  static F d ↔
    ∃ S : Finset (Fin n), t ∈ S ∧ (S.card < d ∨ s ∈ S) ∧
      Relation.ReflTransGen (fun U V => up U V ∨ up V U) ∅ (S.image some) := by
  intro n d s t hst pred hpred P static clause pins F enabled up
  exact PEqualNP.Outside.L_pcx_242_aux.main n d s t hst pred hpred
