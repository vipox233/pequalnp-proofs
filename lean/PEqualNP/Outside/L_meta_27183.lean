import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27183

open PEqualNP.CircuitLowerBounds

private def well (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length,
    ((C.gates.get j).op = .not ∧ ∃ a, a < 9+j.val ∧ (C.gates.get j).inputs = [a]) ∨
    (((C.gates.get j).op = .and ∨ (C.gates.get j).op = .or) ∧
      ∃ a b, a < b ∧ b < 9+j.val ∧ (C.gates.get j).inputs = [a,b])

private def value (C : Circuit) (x : Fin 9 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private def beforeStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem foldLen (gs : List Gate) (w : List Bool) :
    (gs.foldl beforeStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih,beforeStep]; omega

private theorem foldKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl beforeStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [beforeStep]; omega)]
    exact List.getD_append w _ false i hi

private theorem rawValue (C : Circuit) (x : Fin 9 → Bool) (i : Fin 9) :
    value C x i = x i := by
  change (C.gates.foldl beforeStep (List.ofFn x)).getD i false = _
  rw [foldKeep _ _ _ (by simp)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using i.isLt)]
  rw [Option.getD_some, List.getElem_ofFn]

private theorem readsEarlier (C : Circuit) (h : well C) (j : Fin C.gates.length)
    (i : ℕ) (hi : i ∈ (C.gates.get j).inputs) : i < 9+j.val := by
  rcases h j with ⟨_,a,ha,e⟩ | ⟨_,a,b,hab,hb,e⟩
  · rw [e] at hi
    have eq : i = a := by simpa using hi
    exact eq ▸ ha
  · rw [e] at hi
    rcases (show i = a ∨ i = b by simpa using hi) with rfl | rfl
    · omega
    · exact hb

private theorem gateValue (C : Circuit) (h : well C) (x : Fin 9 → Bool) (j : Fin C.gates.length) :
    value C x (9+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (value C x)) := by
  let start := (C.gates.take j.val).foldl beforeStep (List.ofFn x)
  have len : start.length = 9+j.val := by
    simp [start,foldLen,List.length_take,Nat.min_eq_left j.isLt.le]
  have front : C.gates = C.gates.take j.val ++ C.gates.get j :: C.gates.drop (j.val+1) := by
    change C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val+1)
    rw [← List.drop_eq_getElem_cons j.isLt,List.take_append_drop]
  have all : C.wires (List.ofFn x) =
      (C.gates.drop (j.val+1)).foldl beforeStep (beforeStep start (C.gates.get j)) := by
    change C.gates.foldl beforeStep _ = _
    conv_lhs => rw [front]
    rw [List.foldl_append,List.foldl_cons]
  have eqs : ∀ i < 9+j.val, value C x i = start.getD i false := by
    intro i hi
    unfold value
    rw [all,foldKeep _ _ _ (by simp [beforeStep,len]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  have maps : ((C.gates.get j).inputs.map (value C x)) =
      (C.gates.get j).inputs.map (fun i => start.getD i false) :=
    List.map_congr_left fun i hi => eqs _ (readsEarlier C h j i hi)
  rw [maps]
  unfold value
  rw [all,foldKeep _ _ _ (by simp [beforeStep,len])]
  simp [beforeStep,List.getD_eq_getElem?_getD,List.getElem?_append_right,len]

private def reads (C : Circuit) (u v : ℕ) : Prop :=
  ∃ j : Fin C.gates.length, v = 9+j.val ∧ u ∈ (C.gates.get j).inputs

private theorem readsLt (C : Circuit) (h : well C) {u v : ℕ} (e : reads C u v) : u < v := by
  obtain ⟨j,rfl,hj⟩ := e
  exact readsEarlier C h j _ hj

private def path (C : Circuit) (u v : ℕ) : Prop :=
  Relation.ReflTransGen (reads C) u v

private theorem pathLe (C : Circuit) (h : well C) {u v : ℕ} (p : path C u v) : u ≤ v := by
  induction p with
  | refl => rfl
  | tail _ e ih => exact le_trans ih (readsLt C h e).le

private def oneRead (C : Circuit) : Prop :=
  ∀ u v v', 2 ≤ u → reads C u v → reads C u v' → v = v'

private theorem pathLinear (C : Circuit) (h : well C) (unique : oneRead C)
    {u a b : ℕ} (hu : 2 ≤ u) (p : path C u a) (q : path C u b) :
    path C a b ∨ path C b a := by
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl q
  | head e p ih =>
    rcases q.cases_head with eq | ⟨v,ev,pv⟩
    · subst b
      exact Or.inr (Relation.ReflTransGen.head e p)
    · have same := unique _ _ _ hu e ev
      subst v
      exact ih (le_trans hu (readsLt C h e).le) pv

private theorem feeders (C : Circuit) (h : well C) (unique : oneRead C)
    {i a b v : ℕ} (hi : 2 ≤ i) (pa : path C i a) (pb : path C i b)
    (av : reads C a v) (bv : reads C b v) : a = b := by
  have impossible {u t : ℕ} (p : path C u t) (iu : path C i u)
      (uv : reads C u v) (tv : reads C t v) : u = t := by
    rcases p.cases_head with eq | ⟨z,uz,zt⟩
    · exact eq
    · have zu := unique _ _ _ (le_trans hi (pathLe C h iu)) uz uv
      subst z
      exact False.elim (not_lt_of_ge (pathLe C h zt) (readsLt C h tv))
  rcases pathLinear C h unique hi pa pb with p | p
  · exact impossible p pa av bv
  · exact (impossible p pb bv av).symm

private def changes (C : Circuit) (x y : Fin 9 → Bool) (u v : ℕ) : Prop :=
  reads C u v ∧ value C x v ≠ value C y v

private theorem findChange (C : Circuit) (h : well C) (x y : Fin 9 → Bool) (i : Fin 9)
    (agree : ∀ k, k ≠ i → x k = y k) :
    ∀ w < 9+C.gates.length, value C x w ≠ value C y w →
      Relation.ReflTransGen (changes C x y) i.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound diff
    by_cases raw : w < 9
    · let k : Fin 9 := ⟨w,raw⟩
      have neq : x k ≠ y k := by
        change value C x k.val ≠ value C y k.val at diff
        rwa [rawValue C x k,rawValue C y k] at diff
      have eq : k = i := by by_contra ne; exact neq (agree k ne)
      have vw : w = i.val := congrArg Fin.val eq
      rw [vw]
    · let j : Fin C.gates.length := ⟨w-9,by omega⟩
      have wj : w = 9+j.val := by simp [j]; omega
      obtain ⟨u,hu,ne⟩ : ∃ u ∈ (C.gates.get j).inputs,
          value C x u ≠ value C y u := by
        by_contra! same
        apply diff
        rw [wj,gateValue C h x j,gateValue C h y j]
        rw [List.map_congr_left same]
      have read : reads C u w := ⟨j,wj,hu⟩
      exact .tail (ih u (readsLt C h read) (by have := readsLt C h read; omega) ne)
        ⟨read,diff⟩

private theorem diffPath (C : Circuit) (h : well C) (x y : Fin 9 → Bool) (i : Fin 9)
    (agree : ∀ k, k ≠ i → x k = y k) (w : ℕ) (bound : w < 9+C.gates.length)
    (diff : value C x w ≠ value C y w) : path C i.val w := by
  have p := findChange C h x y i agree w bound diff
  exact Relation.ReflTransGen.mono (p := reads C) (fun _ _ edge => edge.1) _ _ p

private def matching (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

private def agrees (C : Circuit) : Prop :=
  ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x

private def row (n : ℕ) (k : Fin 9) : Bool := n.testBit k.val

private def pivotLow : Fin 9 → ℕ := ![160,96,80,132,68,66,20,12,10]
private def pivotHigh : Fin 9 → ℕ := ![161,98,84,140,84,98,84,140,266]

private theorem pivotal :
    ∀ i : Fin 9, matching (row (pivotLow i)) = false ∧
      matching (row (pivotHigh i)) = true ∧
      ∀ k : Fin 9, k ≠ i → row (pivotLow i) k = row (pivotHigh i) k := by decide

private def used (C : Circuit) : List ℕ := C.gates.flatMap Gate.inputs

private theorem usedOfRead (C : Circuit) {u v : ℕ} (r : reads C u v) : u ∈ used C := by
  obtain ⟨j,_,hj⟩ := r
  exact List.mem_flatMap.mpr ⟨_,List.get_mem _ _,hj⟩

private theorem sumFn {n : ℕ} (f : Fin n → ℕ) : (List.ofFn f).sum = ∑ i, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ,Fin.sum_univ_succ,ih]

private theorem countReaders (C : Circuit) (u : ℕ) :
    (used C).count u = ∑ j : Fin C.gates.length, ((C.gates.get j).inputs.count u) := by
  rw [used,List.count_flatMap,← List.ofFn_getElem_eq_map,sumFn]
  rfl

private theorem countTwo (C : Circuit) {u v w : ℕ}
    (rv : reads C u v) (rw' : reads C u w) (ne : v ≠ w) :
    2 ≤ (used C).count u := by
  obtain ⟨j,rfl,hj⟩ := rv
  obtain ⟨k,rfl,hk⟩ := rw'
  have distinct : j ≠ k := by intro e; subst k; exact ne rfl
  rw [countReaders]
  calc
    2 = ∑ i : Fin C.gates.length, ((if i=j then 1 else 0) + (if i=k then 1 else 0)) := by simp [Finset.sum_add_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      by_cases e : i = j
      · subst i
        simpa [distinct] using List.count_pos_iff.mpr hj
      · by_cases f : i = k
        · subst i
          simpa [e] using List.count_pos_iff.mpr hk
        · simp [e,f]

private theorem usedLen (C : Circuit) :
    (used C).length = ∑ j : Fin C.gates.length, (C.gates.get j).inputs.length := by
  rw [used,List.length_flatMap,← List.ofFn_getElem_eq_map,sumFn]
  rfl

private theorem pointReader (C : Circuit) (wf : well C) (good : agrees C)
    (root : C.output + 1 = 9+C.gates.length) (nontriv : 0 < C.gates.length)
    (i : Fin 9) : ∃ v, reads C i.val v ∧
      value C (row (pivotLow i)) v ≠ value C (row (pivotHigh i)) v := by
  have ⟨lo,hi,agree⟩ := pivotal i
  have diff : value C (row (pivotLow i)) C.output ≠ value C (row (pivotHigh i)) C.output := by
    change C.eval _ ≠ C.eval _
    rw [good,good,lo,hi]
    decide
  have p := findChange C wf _ _ i agree C.output (by omega) diff
  rcases p.cases_head with eq | ⟨v,hv,_⟩
  · have := i.isLt
    omega
  · exact ⟨v,hv.1,hv.2⟩

private theorem usedBeforeRoot (C : Circuit) (wf : well C) (good : agrees C)
    (root : C.output + 1 = 9+C.gates.length) (nontriv : 0 < C.gates.length)
    (live : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs) :
    ∀ u < C.output, 1 ≤ (used C).count u := by
  intro u hu
  have mem : u ∈ used C := by
    by_cases raw : u < 9
    · obtain ⟨v,hv,_⟩ := pointReader C wf good root nontriv ⟨u,raw⟩
      exact usedOfRead C hv
    · let j : Fin C.gates.length := ⟨u-9,by omega⟩
      obtain ⟨k,_,hk⟩ := live j (by simp [j]; omega)
      have eq : 9+j.val = u := by simp [j]; omega
      exact usedOfRead C (show reads C u (9+k.val) from ⟨k,rfl,eq ▸ hk⟩)
  exact List.count_pos_iff.mpr mem

private theorem usedLimits (C : Circuit) (wf : well C) (root : C.output + 1 = 9+C.gates.length) :
    ∑ u ∈ Finset.range C.output, (used C).count u = (used C).length := by
  have e : ∑ u ∈ Finset.range C.output, (((used C) : Multiset ℕ).count u) =
      (((used C) : Multiset ℕ).card) := by
    apply Multiset.sum_count_eq_card
    intro u hu
    change u ∈ used C at hu
    obtain ⟨g,hg,hug⟩ := List.mem_flatMap.mp hu
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hg
    have lt := readsEarlier C wf ⟨j,hj⟩ u hug
    exact Finset.mem_range.mpr (by dsimp at lt; omega)
  simpa only [Multiset.coe_count,Multiset.coe_card] using e

private theorem prefixAndAgree : ∀ i : Fin 9, i.val < 2 →
    (row (pivotLow i) 0 && row (pivotLow i) 1) =
      (row (pivotHigh i) 0 && row (pivotHigh i) 1) := by decide

private theorem firstValue (C : Circuit) (wf : well C)
    (g0 : C.gates[0]? = some ⟨.and,[0,1]⟩) (x : Fin 9 → Bool) :
    value C x 9 = (x 0 && x 1) := by
  let j0 : Fin C.gates.length := ⟨0,(List.getElem?_eq_some_iff.mp g0).1⟩
  have g0' : C.gates.get j0 = ⟨.and,[0,1]⟩ := (List.getElem?_eq_some_iff.mp g0).2
  change value C x (9+j0.val) = _
  rw [gateValue C wf x j0,g0']
  simp [GateOp.eval,← rawValue C x (0 : Fin 9),← rawValue C x (1 : Fin 9)]

private theorem prefixCounts (C : Circuit) (wf : well C) (good : agrees C)
    (root : C.output+1 = 9+C.gates.length) (g0 : C.gates[0]? = some ⟨.and,[0,1]⟩) :
    ∀ u < 2, 2 ≤ (used C).count u := by
  let j0 : Fin C.gates.length := ⟨0,(List.getElem?_eq_some_iff.mp g0).1⟩
  have g0' : C.gates.get j0 = ⟨.and,[0,1]⟩ := (List.getElem?_eq_some_iff.mp g0).2
  intro u hu
  let i : Fin 9 := ⟨u,by omega⟩
  obtain ⟨v,hv,dv⟩ := pointReader C wf good root j0.isLt i
  have raw : reads C u 9 := ⟨j0,rfl,by rw [g0']; simp; omega⟩
  refine countTwo C hv raw ?_
  intro e
  subst v
  apply dv
  rw [firstValue C wf g0,firstValue C wf g0]
  exact prefixAndAgree i hu

private theorem countAndRead (C : Circuit) (wf : well C) (lim : C.gates.length ≤ 11)
    (out : C.output + 1 = 9+C.gates.length)
    (usedOnce : ∀ u < C.output, 1 ≤ (used C).count u)
    (extra : ∀ u < 2, 2 ≤ (used C).count u)
    (pin : Fin C.gates.length) (pinLen : (C.gates.get pin).inputs.length = 1) :
    oneRead C ∧ ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j = pin := by
  let weight (j : Fin C.gates.length) := (C.gates.get j).inputs.length + if j=pin then 1 else 0
  have ub (j : Fin C.gates.length) : weight j ≤ 2 := by
    by_cases eq : j = pin
    · subst j
      unfold weight
      rw [pinLen]
      simp
    · simp only [weight,eq,if_false,Nat.add_zero]
      rcases wf j with ⟨_,_,_,e⟩ | ⟨_,_,_,_,_,e⟩ <;> rw [e] <;> simp
  have sumWeight : (∑ j : Fin C.gates.length, weight j) = (used C).length + 1 := by
    unfold weight
    rw [Finset.sum_add_distrib,← usedLen]
    simp
  have lenBound : (used C).length + 1 ≤ 2*C.gates.length := by
    rw [← sumWeight]
    calc
      _ ≤ ∑ j : Fin C.gates.length, 2 := Finset.sum_le_sum (fun j _ => ub j)
      _ = _ := by simp [Nat.mul_comm]
  let base (u : ℕ) := 1 + if u < 2 then 1 else 0
  have bSum : ∑ u ∈ Finset.range C.output, base u = C.output + 2 := by
    simp only [base,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    congr 1
    rw [← Finset.sum_filter]
    have eq : (Finset.range C.output).filter (fun u => u < 2) = Finset.range 2 := by
      ext u
      simp only [Finset.mem_filter,Finset.mem_range]
      omega
    rw [eq]
    decide
  have lower (u : ℕ) (hu : u ∈ Finset.range C.output) : base u ≤ (used C).count u := by
    by_cases tiny : u < 2
    · unfold base
      rw [if_pos tiny]
      exact extra u tiny
    · unfold base
      rw [if_neg tiny]
      exact usedOnce u (Finset.mem_range.mp hu)
  have bLe := Finset.sum_le_sum lower
  rw [bSum,usedLimits C wf out] at bLe
  have eqLen : (used C).length + 1 = 2*C.gates.length := by omega
  constructor
  · intro u v v' hi hv hv'
    by_contra neq
    have two := countTwo C hv hv' neq
    have mem : u ∈ Finset.range C.output := by
      obtain ⟨j,_,hj⟩ := hv
      have e := readsEarlier C wf j u hj
      exact Finset.mem_range.mpr (by have := j.isLt; omega)
    have kt : base u < (used C).count u := by
      unfold base
      rw [if_neg (Nat.not_lt.mpr hi)]
      omega
    have lt := Finset.sum_lt_sum lower ⟨u,mem,kt⟩
    rw [bSum,usedLimits C wf out] at lt
    omega
  · intro j op
    by_contra neq
    have len1 : weight j < 2 := by
      simp only [weight,neq,if_false,Nat.add_zero]
      rcases wf j with ⟨_,_,_,e⟩ | ⟨h,_,_,_,_,_⟩
      · rw [e]; simp
      · rw [op] at h
        cases h <;> contradiction
    have lt : (∑ j : Fin C.gates.length, weight j) < ∑ j : Fin C.gates.length, 2 :=
      Finset.sum_lt_sum (fun j _ => ub j) ⟨j,Finset.mem_univ _,len1⟩
    rw [sumWeight,eqLen] at lt
    simp [Nat.mul_comm] at lt

private def shape (a ai aj b bi bj : Bool) : Prop :=
  a = true ∧ ai = false ∧ aj = false ∧ b = false ∧ bi = true ∧ bj = true

private def still (a ai b bi : Bool) : Prop := a = ai ∧ b = bi

private def combine (isAnd u v : Bool) : Bool := if isAnd then u && v else u || v

private theorem shapeCombine :
    ∀ (t a ai aj b bi bj c ci cj d di dj : Bool),
      (still a ai b bi ∨ still c ci d di) →
      (still a aj b bj ∨ still c cj d dj) →
      shape (combine t a c) (combine t ai ci) (combine t aj cj)
        (combine t b d) (combine t bi di) (combine t bj dj) →
      shape a ai aj b bi bj ∨ shape c ci cj d di dj := by
  intro t a ai aj b bi bj c ci cj d di dj sameI sameJ result
  cases t <;> rcases sameI with sameI | sameI <;> rcases sameJ with sameJ | sameJ <;>
    simp only [still] at sameI sameJ <;> simp [combine,shape] at result ⊢ <;> grind

private theorem stillFeeder (C : Circuit) (wf : well C) (one : oneRead C)
    (x xi y yi : Fin 9 → Bool) (i : Fin 9) (ihi : 2 ≤ i.val)
    (agreeX : ∀ k, k ≠ i → x k = xi k) (agreeY : ∀ k, k ≠ i → y k = yi k)
    (a b u : ℕ) (bound : u < 9+C.gates.length)
    (ne : a ≠ b) (ha : reads C a u) (hb : reads C b u) :
    still (value C x a) (value C xi a) (value C y a) (value C yi a) ∨
    still (value C x b) (value C xi b) (value C y b) (value C yi b) := by
  classical
  by_cases sa : still (value C x a) (value C xi a) (value C y a) (value C yi a)
  · exact Or.inl sa
  · right
    have aa : path C i.val a := by
      unfold still at sa
      rcases not_and_or.mp sa with h | h
      · exact diffPath C wf x xi i agreeX a (by have := readsLt C wf ha; omega) h
      · exact diffPath C wf y yi i agreeY a (by have := readsLt C wf ha; omega) h
    have no : ¬ path C i.val b := fun bb => ne (feeders C wf one ihi aa bb ha hb)
    constructor
    · by_contra h
      exact no (diffPath C wf x xi i agreeX b (by have := readsLt C wf hb; omega) h)
    · by_contra h
      exact no (diffPath C wf y yi i agreeY b (by have := readsLt C wf hb; omega) h)

private theorem inputPairs :
    (∀ k : Fin 9, k ≠ 2 → row 85 k = row 81 k ∧ row 457 k = row 461 k) ∧
    (∀ k : Fin 9, k ≠ 4 → row 85 k = row 69 k ∧ row 457 k = row 473 k) := by decide

private theorem inputNotShape :
    ∀ k : Fin 9, ¬ shape (row 85 k) (row 81 k) (row 69 k)
       (row 457 k) (row 461 k) (row 473 k) := by
  unfold shape
  decide

private theorem targetShape :
    shape (matching (row 85)) (matching (row 81)) (matching (row 69))
      (matching (row 457)) (matching (row 461)) (matching (row 473)) := by
  unfold shape
  decide

private def wireShape (C : Circuit) (w : ℕ) : Prop :=
    shape (value C (row 85) w) (value C (row 81) w) (value C (row 69) w)
      (value C (row 457) w) (value C (row 461) w) (value C (row 473) w)

private theorem gateCombine (C : Circuit) (wf : well C) (j : Fin C.gates.length)
    (a b : ℕ) (t : Bool)
    (op : (C.gates.get j).op = if t then .and else .or)
    (inp : (C.gates.get j).inputs = [a,b]) (x : Fin 9 → Bool) :
    value C x (9+j.val) = combine t (value C x a) (value C x b) := by
  rw [gateValue C wf x j,op,inp]
  cases t <;> simp [GateOp.eval,combine]

private theorem impossibleShape (C : Circuit) (wf : well C) (one : oneRead C)
    (notShape : ∀ j : Fin C.gates.length, (C.gates.get j).op = .not →
      ¬ wireShape C (9+j.val)) :
    ∀ w < 9+C.gates.length, ¬ wireShape C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w earlier =>
    intro bound pat
    by_cases raw : w < 9
    · let k : Fin 9 := ⟨w,raw⟩
      apply inputNotShape k
      unfold wireShape at pat
      change shape (value C (row 85) k.val) (value C (row 81) k.val)
        (value C (row 69) k.val) (value C (row 457) k.val)
        (value C (row 461) k.val) (value C (row 473) k.val) at pat
      simpa only [rawValue] using pat
    · let j : Fin C.gates.length := ⟨w-9,by omega⟩
      have wj : w = 9+j.val := by simp [j]; omega
      rcases wf j with ⟨hn,_⟩ | ⟨op,a,b,ab,hb,inp⟩
      · exact notShape j hn (wj ▸ pat)
      have haRead : reads C a w := ⟨j,wj,by rw [inp]; simp⟩
      have hbRead : reads C b w := ⟨j,wj,by rw [inp]; simp⟩
      have still2 := stillFeeder C wf one (row 85) (row 81) (row 457) (row 461)
        (2 : Fin 9) (by decide) (fun k hk => (inputPairs.1 k hk).1)
        (fun k hk => (inputPairs.1 k hk).2) a b w bound (Nat.ne_of_lt ab) haRead hbRead
      have still4 := stillFeeder C wf one (row 85) (row 69) (row 457) (row 473)
        (4 : Fin 9) (by decide) (fun k hk => (inputPairs.2 k hk).1)
        (fun k hk => (inputPairs.2 k hk).2) a b w bound (Nat.ne_of_lt ab) haRead hbRead
      obtain ⟨t,eq⟩ : ∃ t : Bool, (C.gates.get j).op = if t then .and else .or := by
        rcases op with op | op
        · exact ⟨true,op⟩
        · exact ⟨false,op⟩
      unfold wireShape at pat
      rw [wj,gateCombine C wf j a b t eq inp,gateCombine C wf j a b t eq inp,
        gateCombine C wf j a b t eq inp,gateCombine C wf j a b t eq inp,
        gateCombine C wf j a b t eq inp,gateCombine C wf j a b t eq inp] at pat
      have both := shapeCombine t _ _ _ _ _ _ _ _ _ _ _ _ still2 still4 pat
      have la := readsLt C wf haRead
      have lb := readsLt C wf hbRead
      rcases both with aa | bb
      · exact earlier a la (by omega) aa
      · exact earlier b lb (by omega) bb

private theorem main (C : Circuit) (lim : C.size ≤ 11) (good : agrees C)
    (out : C.output + 1 = 9+C.size) (wf : well C)
    (live : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (first : C.gates.head? = some ⟨.and,[0,1]⟩)
    (second : C.gates.tail.head? = some ⟨.not,[9]⟩) : False := by
  change C.gates.length ≤ 11 at lim
  change C.output + 1 = 9+C.gates.length at out
  have g0 : C.gates[0]? = some ⟨.and,[0,1]⟩ := by
    simpa only [List.head?_eq_getElem?] using first
  have g1 : C.gates[1]? = some ⟨.not,[9]⟩ := by
    simpa only [List.head?_eq_getElem?,List.getElem?_tail,Nat.zero_add] using second
  have positive := (List.getElem?_eq_some_iff.mp g0).1
  let pin : Fin C.gates.length := ⟨1,(List.getElem?_eq_some_iff.mp g1).1⟩
  have pinGate : C.gates.get pin = ⟨.not,[9]⟩ := (List.getElem?_eq_some_iff.mp g1).2
  have pinLen : (C.gates.get pin).inputs.length = 1 := by rw [pinGate]; rfl
  obtain ⟨one,onlyNot⟩ := countAndRead C wf lim out
    (usedBeforeRoot C wf good out positive live) (prefixCounts C wf good out g0) pin pinLen
  have secondValue (x : Fin 9 → Bool) :
      value C x (9+pin.val) = !(x 0 && x 1) := by
    rw [gateValue C wf x pin,pinGate]
    simp [GateOp.eval,firstValue C wf g0]
  have notShape (j : Fin C.gates.length) (op : (C.gates.get j).op = .not) :
      ¬ wireShape C (9+j.val) := by
    have eq := onlyNot j op
    subst j
    intro hs
    have same : value C (row 85) (9+pin.val) = value C (row 81) (9+pin.val) := by
      rw [secondValue,secondValue]
      decide
    exact Bool.noConfusion (hs.1.symm.trans (same.trans hs.2.1))
  apply impossibleShape C wf one notShape C.output (by omega)
  unfold wireShape
  change shape (C.eval (List.ofFn (row 85))) (C.eval (List.ofFn (row 81)))
    (C.eval (List.ofFn (row 69))) (C.eval (List.ofFn (row 457)))
    (C.eval (List.ofFn (row 461))) (C.eval (List.ofFn (row 473)))
  change ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x at good
  simpa only [good] using targetShape

end PEqualNP.Outside.L_meta_27183

open PEqualNP.Outside.L_meta_27183 in
theorem PEqualNP.Outside.L_meta_27183 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [9]⟩)
) := by
  rintro ⟨C,_,lim,good,out,wf,_,live,first,second⟩
  exact main C lim good out wf live first second
