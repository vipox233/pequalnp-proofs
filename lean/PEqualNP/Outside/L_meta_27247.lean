import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27247

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


private theorem prefixFirstAgree : ∀ i : Fin 9, i.val < 2 →
    (row (pivotLow i) 0 && row (pivotLow i) 1) =
      (row (pivotHigh i) 0 && row (pivotHigh i) 1) := by decide

private theorem prefixSecondAgree :
    (row (pivotLow 2) 2 && (row (pivotLow 2) 0 && row (pivotLow 2) 1)) =
      (row (pivotHigh 2) 2 && (row (pivotHigh 2) 0 && row (pivotHigh 2) 1)) := by decide

private theorem prefixCounts (C : Circuit) (wf : well C) (good : agrees C)
    (root : C.output+1 = 9+C.gates.length)
    (g0 : C.gates[0]? = some ⟨.and,[0,1]⟩) (g1 : C.gates[1]? = some ⟨.and,[2,9]⟩) :
    ∀ u < 3, 2 ≤ (used C).count u := by
  have j0b := (List.getElem?_eq_some_iff.mp g0).1
  have j1b := (List.getElem?_eq_some_iff.mp g1).1
  let j0 : Fin C.gates.length := ⟨0,j0b⟩
  let j1 : Fin C.gates.length := ⟨1,j1b⟩
  have g0' : C.gates.get j0 = ⟨.and,[0,1]⟩ := (List.getElem?_eq_some_iff.mp g0).2
  have g1' : C.gates.get j1 = ⟨.and,[2,9]⟩ := (List.getElem?_eq_some_iff.mp g1).2
  have firstValue (x : Fin 9 → Bool) :
      value C x 9 = (x 0 && x 1) := by
    change value C x (9+j0.val) = _
    rw [gateValue C wf x j0,g0']
    simp [GateOp.eval,← rawValue C x (0 : Fin 9),← rawValue C x (1 : Fin 9)]
  have secondValue (x : Fin 9 → Bool) :
      value C x 10 = (x 2 && (x 0 && x 1)) := by
    change value C x (9+j1.val) = _
    rw [gateValue C wf x j1,g1']
    simp [GateOp.eval,firstValue,← rawValue C x (2 : Fin 9)]
  intro u hu
  let i : Fin 9 := ⟨u,by omega⟩
  obtain ⟨v,hv,dv⟩ := pointReader C wf good root (by omega) i
  by_cases small : u < 2
  · have raw : reads C u 9 := ⟨j0,rfl,by rw [g0']; simp; omega⟩
    refine countTwo C hv raw ?_
    intro e
    subst v
    apply dv
    rw [firstValue,firstValue]
    exact prefixFirstAgree i small
  · have eq : u = 2 := by omega
    have raw : reads C u 10 := ⟨j1,rfl,by rw [g1',eq]; simp⟩
    refine countTwo C hv raw ?_
    intro e
    subst v
    apply dv
    rw [secondValue,secondValue]
    have ie : i = 2 := Fin.ext eq
    rw [ie]
    exact prefixSecondAgree

private def shared (C : Circuit) (u : ℕ) : Prop :=
  ∃ v w, v ≠ w ∧ reads C u v ∧ reads C u w

private def single (C : Circuit) (u : ℕ) : Prop :=
  ∀ v w, reads C u v → reads C u w → v = w

private theorem singleOf (C : Circuit) {u : ℕ} (hn : ¬ shared C u) : single C u := by
  intro v w hv hw
  by_contra neq
  exact hn ⟨v,w,neq,hv,hw⟩

private theorem sharingCount (C : Circuit) (h : well C) (lim : C.gates.length ≤ 12)
    (out : C.output + 1 = 9+C.gates.length)
    (usedOnce : ∀ u < C.output, 1 ≤ (used C).count u)
    (extra : ∀ u < 3, 2 ≤ (used C).count u) :
    (∀ u v, 3 ≤ u → 3 ≤ v → shared C u → shared C v → u = v) ∧
    (∀ u, 3 ≤ u → shared C u → ∀ g : Fin C.gates.length, (C.gates.get g).op ≠ .not) := by
  have ub (j : Fin C.gates.length) : (C.gates.get j).inputs.length ≤ 2 := by
    rcases h j with ⟨_,_,_,e⟩ | ⟨_,_,_,_,_,e⟩ <;> rw [e] <;> simp
  have lenBound : (used C).length ≤ 2*C.gates.length := by
    rw [usedLen]
    calc
      _ ≤ ∑ j : Fin C.gates.length, 2 := Finset.sum_le_sum (fun j _ => ub j)
      _ = _ := by simp [Nat.mul_comm]
  let base (u : ℕ) := 1 + if u < 3 then 1 else 0
  have bSum : ∑ u ∈ Finset.range C.output, base u = C.output + 3 := by
    simp only [base,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    congr 1
    rw [← Finset.sum_filter]
    have eq : (Finset.range C.output).filter (fun u => u < 3) = Finset.range 3 := by
      ext u
      simp only [Finset.mem_filter,Finset.mem_range]
      omega
    rw [eq]
    decide
  have lower (u : ℕ) (hu : u ∈ Finset.range C.output) : base u ≤ (used C).count u := by
    by_cases tiny : u < 3
    · unfold base; rw [if_pos tiny]; exact extra u tiny
    · unfold base; rw [if_neg tiny]; exact usedOnce u (Finset.mem_range.mp hu)
  have slack (u : ℕ) (hu : 3 ≤ u) (s : shared C u) :
      u ∈ Finset.range C.output ∧ 1 + base u ≤ (used C).count u := by
    obtain ⟨v,w,ne,hv,hw⟩ := s
    have two := countTwo C hv hw ne
    obtain ⟨j,_,hj⟩ := hv
    have l := readsEarlier C h j u hj
    exact ⟨Finset.mem_range.mpr (by have := j.isLt; omega),
      by unfold base; rw [if_neg (Nat.not_lt.mpr hu)]; exact two⟩
  constructor
  · intro u v hu hv su sv
    by_contra ne
    obtain ⟨mu,lu⟩ := slack u hu su
    obtain ⟨mv,lv⟩ := slack v hv sv
    have sum := Finset.sum_le_sum (s := Finset.range C.output)
      (f := fun w => base w + (if w = u then 1 else 0) + (if w = v then 1 else 0))
      (g := fun w => (used C).count w) (by
        intro w mw
        by_cases eu : w = u
        · subst w
          simpa [ne,Nat.add_comm] using lu
        · by_cases ev : w = v
          · subst w
            simpa [eu,Nat.add_comm] using lv
          · simpa [eu,ev] using lower w mw)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,bSum,usedLimits C h out] at sum
    simp [mu,mv] at sum
    omega
  · intro u hu su j isNot
    obtain ⟨mu,lu⟩ := slack u hu su
    have lt := Finset.sum_lt_sum lower ⟨u,mu,by omega⟩
    rw [bSum,usedLimits C h out] at lt
    have jlt : (C.gates.get j).inputs.length < 2 := by
      rcases h j with ⟨_,_,_,e⟩ | ⟨op,_,_,_,_,_⟩
      · rw [e]; simp
      · rw [isNot] at op
        cases op <;> contradiction
    have less : (∑ j : Fin C.gates.length, (C.gates.get j).inputs.length) <
        ∑ j : Fin C.gates.length, 2 :=
      Finset.sum_lt_sum (fun j _ => ub j) ⟨j,Finset.mem_univ _,jlt⟩
    rw [← usedLen] at less
    simp [Nat.mul_comm] at less
    omega

private theorem forgetChange (C : Circuit) (x y : Fin 9 → Bool) {u v : ℕ}
    (p : Relation.ReflTransGen (changes C x y) u v) : path C u v :=
  Relation.ReflTransGen.mono (p := reads C) (fun _ _ e => e.1) _ _ p

private theorem findAnyChange (C : Circuit) (h : well C) (x y : Fin 9 → Bool) :
    ∀ w < 9+C.gates.length, value C x w ≠ value C y w →
      ∃ i : Fin 9, x i ≠ y i ∧ Relation.ReflTransGen (changes C x y) i.val w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound diff
    by_cases raw : w < 9
    · let i : Fin 9 := ⟨w,raw⟩
      change value C x i.val ≠ value C y i.val at diff
      rw [rawValue C x i,rawValue C y i] at diff
      exact ⟨i,diff,.refl⟩
    · let j : Fin C.gates.length := ⟨w-9,by omega⟩
      have wj : w = 9+j.val := by simp [j]; omega
      obtain ⟨u,hu,ne⟩ : ∃ u ∈ (C.gates.get j).inputs,
          value C x u ≠ value C y u := by
        by_contra! same
        apply diff
        rw [wj,gateValue C h x j,gateValue C h y j]
        rw [List.map_congr_left same]
      have read : reads C u w := ⟨j,wj,hu⟩
      have earlier := readsLt C h read
      obtain ⟨i,hi,p⟩ := ih u earlier (by omega) ne
      exact ⟨i,hi,.tail p ⟨read,diff⟩⟩

private theorem pathLinear (C : Circuit) (h : well C) {u a : ℕ} (cap : ℕ)
    (p : path C u a) :
    ∀ {b}, path C u b → (∀ z, path C u z → z < cap → single C z) →
      a < cap → b < cap → path C a b ∨ path C b a := by
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => intro b q _ _ _; exact Or.inl q
  | head e p ih =>
    intro b q unique ac bc
    rcases q.cases_head with eq | ⟨v,ev,pv⟩
    · subst b
      exact Or.inr (Relation.ReflTransGen.head e p)
    · have front := Nat.lt_of_le_of_lt (pathLe C h (Relation.ReflTransGen.head e p)) ac
      have same := unique _ .refl front _ _ e ev
      subst v
      exact ih pv (fun z hz lz => unique z (.head e hz) lz) ac bc

private theorem feeders (C : Circuit) (h : well C) {i a b v : ℕ}
    (unique : ∀ z, path C i z → z < v → single C z)
    (pa : path C i a) (pb : path C i b) (av : reads C a v) (bv : reads C b v) : a = b := by
  have impossible {u t : ℕ} (p : path C u t) (iu : path C i u)
      (uv : reads C u v) (tv : reads C t v) : u = t := by
    rcases p.cases_head with eq | ⟨z,uz,zt⟩
    · exact eq
    · have zu := unique _ iu (readsLt C h uv) _ _ uz uv
      subst z
      exact False.elim (not_lt_of_ge (pathLe C h zt) (readsLt C h tv))
  rcases pathLinear C h v pa pb unique (readsLt C h av) (readsLt C h bv) with p | p
  · exact impossible p pa av bv
  · exact (impossible p pb bv av).symm

private theorem changeThrough (C : Circuit) (h : well C) (x y : Fin 9 → Bool)
    {u w : ℕ} (p : path C u w) :
    ∀ {root}, w ≤ root →
      (∀ z, path C u z → z < w → single C z) →
      Relation.ReflTransGen (changes C x y) u root →
      Relation.ReflTransGen (changes C x y) u w ∧
      Relation.ReflTransGen (changes C x y) w root := by
  induction p using Relation.ReflTransGen.head_induction_on with
  | refl => intro root _ _ q; exact ⟨.refl,q⟩
  | head e p ih =>
    intro root le unique q
    have left := lt_of_lt_of_le (readsLt C h e) (pathLe C h p)
    rcases q.cases_head with eq | ⟨v,step,rest⟩
    · omega
    · have same := unique _ .refl left _ _ e step.1
      subst v
      obtain ⟨pre,post⟩ := ih le (fun z hz lz => unique z (.head e hz) lz) rest
      exact ⟨.head step pre,post⟩

private theorem changedEndpoint (C : Circuit) (x y : Fin 9 → Bool) {u w : ℕ}
    (p : Relation.ReflTransGen (changes C x y) u w) (ne : u ≠ w) :
    value C x w ≠ value C y w := by
  cases p with
  | refl => exact False.elim (ne rfl)
  | tail _ e => exact e.2

private theorem monoValue (C : Circuit) (wf : well C)
    (noNot : ∀ j : Fin C.gates.length, (C.gates.get j).op ≠ .not)
    (x y : Fin 9 → Bool) (le : ∀ i, x i ≤ y i) :
    ∀ w < 9+C.gates.length, value C x w ≤ value C y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound
    by_cases raw : w < 9
    · let k : Fin 9 := ⟨w,raw⟩
      change value C x k.val ≤ value C y k.val
      rw [rawValue,rawValue]
      exact le k
    · let j : Fin C.gates.length := ⟨w-9,by omega⟩
      have wj : w = 9+j.val := by simp [j]; omega
      rcases wf j with ⟨no,_⟩ | ⟨op,a,b,ab,hb,inp⟩
      · exact False.elim (noNot j no)
      have aa := ih a (by omega) (by omega)
      have bb := ih b (by omega) (by omega)
      rw [wj,gateValue C wf x j,gateValue C wf y j,inp]
      rcases op with ha | ho
      · rw [ha]
        simpa [GateOp.eval] using (show (value C x a && value C x b) ≤ (value C y a && value C y b) by
          cases ea : value C x a <;> cases eb : value C y a <;> cases ec : value C x b <;> cases ed : value C y b <;> simp_all)
      · rw [ho]
        simpa [GateOp.eval] using (show (value C x a || value C x b) ≤ (value C y a || value C y b) by
          cases ea : value C x a <;> cases eb : value C y a <;> cases ec : value C x b <;> cases ed : value C y b <;> simp_all)
private def shape (a ai aj b bi bj : Bool) : Prop :=
  a = true ∧ ai = false ∧ aj = false ∧ b = false ∧ bi = true ∧ bj = true

private def still (a ai b bi : Bool) : Prop := a = ai ∧ b = bi

private def combine (isAnd u v : Bool) : Bool := if isAnd then u && v else u || v

private def polar (neg x : Bool) : Bool := if neg then !x else x

private theorem polarNot (p x : Bool) : polar p (!x) = polar (!p) x := by
  cases p <;> cases x <;> rfl

private theorem shapeCombine :
    ∀ (p t a ai aj b bi bj c ci cj d di dj : Bool),
      (still a ai b bi ∨ still c ci d di) →
      (still a aj b bj ∨ still c cj d dj) →
      shape (polar p (combine t a c)) (polar p (combine t ai ci)) (polar p (combine t aj cj))
        (polar p (combine t b d)) (polar p (combine t bi di)) (polar p (combine t bj dj)) →
      shape (polar p a) (polar p ai) (polar p aj) (polar p b) (polar p bi) (polar p bj) ∨
      shape (polar p c) (polar p ci) (polar p cj) (polar p d) (polar p di) (polar p dj) := by
  intro p t a ai aj b bi bj c ci cj d di dj sameI sameJ result
  cases p <;> cases t <;> rcases sameI with sameI | sameI <;> rcases sameJ with sameJ | sameJ <;>
    simp only [still] at sameI sameJ <;> simp [combine,shape,polar] at result ⊢ <;> grind

private theorem stillFeeder (C : Circuit) (wf : well C)
    (x xi y yi : Fin 9 → Bool) (i : Fin 9)
    (agreeX : ∀ k, k ≠ i → x k = xi k) (agreeY : ∀ k, k ≠ i → y k = yi k)
    (a b u : ℕ) (bound : u < 9+C.gates.length)
    (one : ∀ z, path C i.val z → z < u → single C z)
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
    have no : ¬ path C i.val b := fun bb => ne (feeders C wf one aa bb ha hb)
    constructor
    · by_contra h
      exact no (diffPath C wf x xi i agreeX b (by have := readsLt C wf hb; omega) h)
    · by_contra h
      exact no (diffPath C wf y yi i agreeY b (by have := readsLt C wf hb; omega) h)


private def sharedShape (C : Circuit) (xs : Fin 6 → ℕ) (p : Bool) (w : ℕ) : Prop :=
  shape (polar p (value C (row (xs 0)) w)) (polar p (value C (row (xs 1)) w))
    (polar p (value C (row (xs 2)) w)) (polar p (value C (row (xs 3)) w))
    (polar p (value C (row (xs 4)) w)) (polar p (value C (row (xs 5)) w))

private def switchOK (xs : Fin 6 → ℕ) (i j : Fin 9) : Prop :=
  (∀ k : Fin 9, k ≠ i → row (xs 0) k = row (xs 1) k ∧ row (xs 3) k = row (xs 4) k) ∧
  (∀ k : Fin 9, k ≠ j → row (xs 0) k = row (xs 2) k ∧ row (xs 3) k = row (xs 5) k)

private theorem binaryValue (C : Circuit) (wf : well C) (j : Fin C.gates.length)
    (a b : ℕ) (t : Bool) (op : (C.gates.get j).op = if t then .and else .or)
    (inp : (C.gates.get j).inputs = [a,b]) (x : Fin 9 → Bool) :
    value C x (9+j.val) = combine t (value C x a) (value C x b) := by
  rw [gateValue C wf x j,op,inp]
  cases t <;> simp [GateOp.eval,combine]

private theorem unaryValue (C : Circuit) (wf : well C) (j : Fin C.gates.length) (a : ℕ)
    (op : (C.gates.get j).op = .not) (inp : (C.gates.get j).inputs = [a])
    (x : Fin 9 → Bool) : value C x (9+j.val) = !(value C x a) := by
  rw [gateValue C wf x j,op,inp]
  rfl

private theorem shapeImpossible (C : Circuit) (wf : well C)
    (xs : Fin 6 → ℕ) (i j : Fin 9) (neq : i ≠ j) (sw : switchOK xs i j) (cap : ℕ)
    (uniqueI : ∀ z, path C i.val z → z < cap → single C z)
    (uniqueJ : ∀ z, path C j.val z → z < cap → single C z) :
    ∀ w, w ≤ cap → w < 9+C.gates.length → ∀ p, ¬ sharedShape C xs p w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w earlier =>
    intro wc bound p pat
    by_cases raw : w < 9
    · let k : Fin 9 := ⟨w,raw⟩
      by_cases eq : k = i
      · have ne : k ≠ j := eq ▸ neq
        have hh := (sw.2 k ne).1
        have eqv := congrArg (polar p) ((rawValue C _ k).trans (hh.trans (rawValue C _ k).symm))
        exact Bool.noConfusion (pat.1.symm.trans (eqv.trans pat.2.2.1))
      · have hh := (sw.1 k eq).1
        have eqv := congrArg (polar p) ((rawValue C _ k).trans (hh.trans (rawValue C _ k).symm))
        exact Bool.noConfusion (pat.1.symm.trans (eqv.trans pat.2.1))
    · let g : Fin C.gates.length := ⟨w-9,by omega⟩
      have wg : w = 9+g.val := by simp [g]; omega
      rcases wf g with ⟨hn,a,al,inp⟩ | ⟨op,a,b,ab,hb,inp⟩
      · have ha : a < w := by omega
        apply earlier a ha (by omega) (by omega) (!p)
        unfold sharedShape at pat ⊢
        rw [wg] at pat
        simpa only [unaryValue C wf g a hn inp,polarNot] using pat
      · have haRead : reads C a w := ⟨g,wg,by rw [inp]; simp⟩
        have hbRead : reads C b w := ⟨g,wg,by rw [inp]; simp⟩
        have stillI := stillFeeder C wf (row (xs 0)) (row (xs 1)) (row (xs 3)) (row (xs 4)) i
          (fun k hk => (sw.1 k hk).1) (fun k hk => (sw.1 k hk).2) a b w bound
          (fun z hz lw => uniqueI z hz (by omega)) (Nat.ne_of_lt ab) haRead hbRead
        have stillJ := stillFeeder C wf (row (xs 0)) (row (xs 2)) (row (xs 3)) (row (xs 5)) j
          (fun k hk => (sw.2 k hk).1) (fun k hk => (sw.2 k hk).2) a b w bound
          (fun z hz lw => uniqueJ z hz (by omega)) (Nat.ne_of_lt ab) haRead hbRead
        obtain ⟨t,eq⟩ : ∃ t : Bool, (C.gates.get g).op = if t then .and else .or := by
          rcases op with op | op
          · exact ⟨true,op⟩
          · exact ⟨false,op⟩
        unfold sharedShape at pat
        rw [wg] at pat
        simp only [binaryValue C wf g a b t eq inp] at pat
        have both := shapeCombine p t _ _ _ _ _ _ _ _ _ _ _ _ stillI stillJ pat
        have la := readsLt C wf haRead
        have lb := readsLt C wf hbRead
        rcases both with aa | bb
        · exact earlier a la (by omega) (by omega) p aa
        · exact earlier b lb (by omega) (by omega) p bb

private def certificate : List (List ℕ) := [
  [],
  [],
  [],
  [4, 12, 20, 132, 140, 68, 84, 76, 84],
  [],
  [2, 10, 34, 258, 266, 66, 98, 74, 98],
  [1, 17, 33, 257, 273, 129, 161, 145, 161],
  [1, 17, 33, 257, 273, 129, 161, 145, 161],
  [],
  [2, 10, 66, 258, 266, 34, 98, 42, 98],
  [3, 19, 67, 259, 275, 35, 99, 51, 99],
  [2, 10, 66, 258, 266, 34, 98, 42, 98],
  [3, 35, 99, 131, 163, 3, 99, 35, 99],
  [2, 10, 98, 258, 266, 2, 98, 10, 98],
  [1, 17, 33, 257, 273, 129, 161, 145, 161],
  [1, 17, 33, 257, 273, 129, 161, 145, 161],
  [],
  [3, 11, 131, 259, 267, 35, 163, 43, 163],
  [1, 17, 129, 257, 273, 33, 161, 49, 161],
  [1, 17, 129, 257, 273, 33, 161, 49, 161],
  [3, 35, 163, 67, 99, 3, 163, 35, 163],
  [2, 10, 34, 258, 266, 66, 98, 74, 98],
  [1, 17, 161, 257, 273, 1, 161, 17, 161],
  [1, 17, 161, 257, 273, 1, 161, 17, 161],
  [4, 68, 132, 20, 84, 12, 140, 76, 140],
  [2, 10, 66, 258, 266, 34, 98, 42, 98],
  [1, 17, 129, 257, 273, 33, 161, 49, 161],
  [1, 17, 129, 257, 273, 33, 161, 49, 161],
  [4, 68, 132, 20, 84, 12, 140, 76, 140],
  [2, 10, 98, 258, 266, 2, 98, 10, 98],
  [1, 17, 161, 257, 273, 1, 161, 17, 161],
  [1, 17, 161, 257, 273, 1, 161, 17, 161],
  [],
  [3, 259, 267, 19, 275, 3, 267, 259, 267],
  [3, 259, 275, 11, 267, 3, 275, 259, 275],
  [4, 12, 20, 132, 140, 68, 84, 76, 84],
  [1, 33, 257, 129, 161, 17, 273, 49, 273],
  [1, 33, 257, 129, 161, 17, 273, 49, 273],
  [1, 33, 273, 129, 161, 1, 273, 33, 273],
  [1, 33, 273, 129, 161, 1, 273, 33, 273],
  [2, 66, 258, 34, 98, 10, 266, 74, 266],
  [2, 66, 266, 34, 98, 2, 266, 66, 266],
  [2, 66, 258, 34, 98, 10, 266, 74, 266],
  [2, 66, 266, 34, 98, 2, 266, 66, 266],
  [1, 33, 257, 129, 161, 17, 273, 49, 273],
  [1, 33, 257, 129, 161, 17, 273, 49, 273],
  [1, 33, 273, 129, 161, 1, 273, 33, 273],
  [1, 33, 273, 129, 161, 1, 273, 33, 273],
  [1, 129, 257, 33, 161, 17, 273, 145, 273],
  [1, 129, 257, 33, 161, 17, 273, 145, 273],
  [1, 129, 273, 33, 161, 1, 273, 129, 273],
  [1, 129, 273, 33, 161, 1, 273, 129, 273],
  [1, 161, 257, 1, 161, 17, 273, 161, 257],
  [1, 161, 257, 1, 161, 17, 273, 161, 257],
  [2, 34, 258, 66, 98, 10, 266, 42, 266],
  [2, 34, 266, 66, 98, 2, 266, 34, 266],
  [1, 129, 257, 33, 161, 17, 273, 145, 273],
  [1, 129, 257, 33, 161, 17, 273, 145, 273],
  [1, 129, 273, 33, 161, 1, 273, 129, 273],
  [1, 129, 273, 33, 161, 1, 273, 129, 273],
  [1, 161, 257, 1, 161, 17, 273, 161, 257],
  [1, 161, 257, 1, 161, 17, 273, 161, 257],
  [2, 98, 258, 2, 98, 10, 266, 98, 258],
  []
]

private def marked (U : Fin 6 → Bool) (i : Fin 9) : Bool :=
  if h : 3 ≤ i.val then U ⟨i.val-3,by have := i.isLt; omega⟩ else false

private def supportSet (U : Fin 6 → Bool) : Finset (Fin 6) :=
  Finset.univ.filter fun i => U i = true

private def rowCode (U : Fin 6 → Bool) : ℕ :=
  (if U 0 then 1 else 0) + (if U 1 then 2 else 0) + (if U 2 then 4 else 0) +
    (if U 3 then 8 else 0) + (if U 4 then 16 else 0) + (if U 5 then 32 else 0)

private def certAt (U : Fin 6 → Bool) (k : ℕ) : ℕ :=
  (certificate.getD (rowCode U) []).getD k 0

private def sameInside (U : Fin 6 → Bool) (a b : ℕ) : Prop :=
  ∀ i : Fin 9, i.val < 3 ∨ marked U i = true → row a i = row b i

private def sameOutside (U : Fin 6 → Bool) (a b : ℕ) : Prop :=
  ∀ i : Fin 9, marked U i = false → row a i = row b i

private def separates (U : Fin 6 → Bool) (a b l r : ℕ) : Prop :=
  sameInside U a l ∧ sameInside U b r ∧ sameOutside U l r ∧ matching (row l) ≠ matching (row r)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3500000 in
private theorem coversCofactors :
    ∀ U : Fin 6 → Bool, 2 ≤ (supportSet U).card → (supportSet U).card ≤ 5 →
    separates U (certAt U 0) (certAt U 1) (certAt U 3) (certAt U 4) ∧
    separates U (certAt U 0) (certAt U 2) (certAt U 5) (certAt U 6) ∧
    separates U (certAt U 1) (certAt U 2) (certAt U 7) (certAt U 8) := by
  unfold separates sameInside sameOutside
  decide

private def testRows : Fin 7 → Fin 6 → ℕ :=
  ![![87,71,23,295,311,359], ![87,71,23,295,311,359], ![143,135,15,295,303,423],
    ![271,263,15,151,159,407], ![143,135,15,295,303,423], ![87,71,23,295,311,359],
    ![103,71,39,151,183,215]]

private def testI : Fin 7 → Fin 9 := ![4,4,3,3,3,4,5]
private def testJ : Fin 7 → Fin 9 := ![6,6,7,8,7,6,6]

private theorem testSwitch :
    ∀ k : Fin 7, switchOK (testRows k) (testI k) (testJ k) := by unfold switchOK; decide

private theorem testPivots :
    ∀ k : Fin 7, 3 ≤ (testI k).val ∧ 3 ≤ (testJ k).val ∧ testI k ≠ testJ k := by decide

private theorem testShape :
    ∀ k : Fin 7, shape
      (matching (row (testRows k 0))) (matching (row (testRows k 1)))
      (matching (row (testRows k 2))) (matching (row (testRows k 3)))
      (matching (row (testRows k 4))) (matching (row (testRows k 5))) := by unfold shape; decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2400000 in
private theorem avoidSmall :
    ∀ U : Fin 6 → Bool, (supportSet U).card ≤ 1 →
      ∃ k : Fin 7, marked U (testI k) = false ∧ marked U (testJ k) = false := by decide

private theorem fullSupport (U : Fin 6 → Bool) (h : 6 ≤ (supportSet U).card) :
    ∀ i, U i = true := by
  have le : (supportSet U).card ≤ 6 := by simpa using Finset.card_le_card (Finset.subset_univ (supportSet U))
  have full : supportSet U = Finset.univ := (supportSet U).eq_univ_of_card (by simpa using le_antisymm le h)
  intro i
  have hi : i ∈ supportSet U := full ▸ Finset.mem_univ i
  simpa [supportSet] using hi

private theorem mainShape (C : Circuit) (good : agrees C) (k : Fin 7) :
    sharedShape C (testRows k) false C.output := by
  change ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x at good
  change shape (C.eval (List.ofFn (row (testRows k 0)))) (C.eval (List.ofFn (row (testRows k 1))))
    (C.eval (List.ofFn (row (testRows k 2)))) (C.eval (List.ofFn (row (testRows k 3))))
    (C.eval (List.ofFn (row (testRows k 4)))) (C.eval (List.ofFn (row (testRows k 5))))
  simpa only [good] using testShape k

private theorem forwardRows :
    (∀ i : Fin 9, row (testRows 0 1) i ≤ row (testRows 0 0) i) ∧
    (∀ i : Fin 9, row (testRows 0 2) i ≤ row (testRows 0 0) i) ∧
    (∀ i : Fin 9, row (testRows 0 3) i ≤ row (testRows 0 4) i) ∧
    (∀ i : Fin 9, row (testRows 0 3) i ≤ row (testRows 0 5) i) := by decide

private theorem orderedDiff : ∀ a b : Bool, a ≤ b → a ≠ b → a = false ∧ b = true := by decide

set_option maxHeartbeats 1500000 in
private theorem main (C : Circuit) (lim : C.size ≤ 12) (good : agrees C)
    (out : C.output + 1 = 9+C.size) (wf : well C)
    (live : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (first : C.gates.head? = some ⟨.and,[0,1]⟩)
    (second : C.gates.tail.head? = some ⟨.and,[2,9]⟩) : False := by
  classical
  change C.gates.length ≤ 12 at lim
  change C.output + 1 = 9+C.gates.length at out
  have g0 : C.gates[0]? = some ⟨.and,[0,1]⟩ := by
    simpa only [List.head?_eq_getElem?] using first
  have g1 : C.gates[1]? = some ⟨.and,[2,9]⟩ := by
    simpa only [List.head?_eq_getElem?,List.getElem?_tail,Nat.zero_add] using second
  have positive := (List.getElem?_eq_some_iff.mp g0).1
  obtain ⟨atMostOne,noNotIfShared⟩ := sharingCount C wf lim out
    (usedBeforeRoot C wf good out positive live) (prefixCounts C wf good out g0 g1)
  have rootBound : C.output < 9+C.gates.length := by omega
  by_cases anyShare : ∃ w, 3 ≤ w ∧ shared C w
  · obtain ⟨w,w3,ws⟩ := anyShare
    have fence : w < C.output := by
      obtain ⟨_,_,_,⟨j,_,hj⟩,_⟩ := ws
      have lv := readsEarlier C wf j w hj
      have := j.isLt
      omega
    have wBound : w < 9+C.gates.length := by omega
    have unique (z : ℕ) (z3 : 3 ≤ z) (ne : z ≠ w) : single C z :=
      singleOf C (fun sz => ne (atMostOne z w z3 w3 sz ws))
    have beforeW (i : Fin 9) (hi : 3 ≤ i.val) :
        ∀ z, path C i.val z → z < w → single C z := by
      intro z iz zw
      exact unique z (le_trans hi (pathLe C wf iz)) (by omega)
    let U : Fin 6 → Bool := fun i => decide (path C (3+i.val) w)
    have spec (i : Fin 9) (hi : 3 ≤ i.val) : marked U i = true ↔ path C i.val w := by
      have e : 3 + (i.val-3) = i.val := by omega
      simp [marked,U,hi,e]
    by_cases small : (supportSet U).card ≤ 1
    · obtain ⟨k,markI,markJ⟩ := avoidSmall U small
      obtain ⟨i3,j3,neq⟩ := testPivots k
      have avoid (i : Fin 9) (hi : 3 ≤ i.val) (off : marked U i = false) :
          ∀ z, path C i.val z → z < C.output → single C z := by
        intro z iz _
        apply unique z (le_trans hi (pathLe C wf iz))
        intro eq
        subst z
        exact Bool.noConfusion (off.symm.trans ((spec i hi).mpr iz))
      exact shapeImpossible C wf _ _ _ neq (testSwitch k) C.output
        (avoid _ i3 markI) (avoid _ j3 markJ) C.output le_rfl rootBound false (mainShape C good k)
    · by_cases full : 6 ≤ (supportSet U).card
      · have all := fullSupport U full
        have pathAll (i : Fin 9) (hi : 3 ≤ i.val) : path C i.val w :=
          (spec i hi).mp (by simp [marked,hi,all])
        have rawEnds {u : ℕ} (p : path C u w) (wh : w < 9) : u = w := by
          rcases p.cases_head with e | ⟨v,⟨g,rfl,_⟩,q⟩
          · exact e
          · have := pathLe C wf q
            omega
        have internal : 9 ≤ w := by
          by_contra! low
          have a := rawEnds (pathAll 3 (by decide)) low
          have b := rawEnds (pathAll 4 (by decide)) low
          exact (by decide : (3 : Fin 9).val ≠ (4 : Fin 9).val) (a.trans b.symm)
        have mono := monoValue C wf (noNotIfShared w w3 ws)
        have turnAt (i : Fin 9) (hi : 3 ≤ i.val) (a b : Fin 9 → Bool)
            (agree : ∀ k, k ≠ i → a k = b k) (ord : ∀ k, a k ≤ b k)
            (changesRoot : value C a C.output ≠ value C b C.output) :
            value C a w = false ∧ value C b w = true := by
          have p := findChange C wf a b i agree C.output rootBound changesRoot
          have pre := (changeThrough C wf a b (pathAll i hi) fence.le (beforeW i hi) p).1
          exact orderedDiff _ _ (mono a b ord w wBound)
            (changedEndpoint C a b pre (by have := i.isLt; omega))
        let xs := testRows 0
        let i := testI 0
        let j := testJ 0
        obtain ⟨i3,j3,neq⟩ := testPivots 0
        have sw : switchOK xs i j := testSwitch 0
        have src := mainShape C good 0
        change shape (value C (row (xs 0)) C.output) (value C (row (xs 1)) C.output)
          (value C (row (xs 2)) C.output) (value C (row (xs 3)) C.output)
          (value C (row (xs 4)) C.output) (value C (row (xs 5)) C.output) at src
        obtain ⟨r0,r1,r2,r3,r4,r5⟩ := src
        have nfalse : false ≠ true := by decide
        have a := turnAt i i3 (row (xs 1)) (row (xs 0))
          (fun k hk => (sw.1 k hk).1.symm) forwardRows.1
          (fun eq => nfalse (r1.symm.trans (eq.trans r0)))
        have b := turnAt j j3 (row (xs 2)) (row (xs 0))
          (fun k hk => (sw.2 k hk).1.symm) forwardRows.2.1
          (fun eq => nfalse (r2.symm.trans (eq.trans r0)))
        have c := turnAt i i3 (row (xs 3)) (row (xs 4))
          (fun k hk => (sw.1 k hk).2) forwardRows.2.2.1
          (fun eq => nfalse (r3.symm.trans (eq.trans r4)))
        have d := turnAt j j3 (row (xs 3)) (row (xs 5))
          (fun k hk => (sw.2 k hk).2) forwardRows.2.2.2
          (fun eq => nfalse (r3.symm.trans (eq.trans r5)))
        exact shapeImpossible C wf xs i j neq sw w (beforeW i i3) (beforeW j j3)
          w le_rfl wBound false ⟨a.2,a.1,b.1,c.1,c.2,d.2⟩
      · obtain ⟨p01,p02,p12⟩ := coversCofactors U (by omega) (by omega)
        have depends (a b : ℕ) (agree : sameInside U a b) :
            value C (row a) w = value C (row b) w := by
          by_contra diff
          obtain ⟨i,di,p⟩ := findAnyChange C wf _ _ w wBound diff
          by_cases hi : 3 ≤ i.val
          · exact di (agree i (.inr ((spec i hi).mpr (forgetChange C _ _ p))))
          · exact di (agree i (.inl (by omega)))
        have different (a b l r : ℕ) (sep : separates U a b l r) :
            value C (row a) w ≠ value C (row b) w := by
          obtain ⟨iai,ibj,off,targetDiff⟩ := sep
          intro eq
          have sw : value C (row l) w = value C (row r) w :=
            (depends a l iai).symm.trans (eq.trans (depends b r ibj))
          have rootDiff : value C (row l) C.output ≠ value C (row r) C.output := by
            change C.eval (List.ofFn (row l)) ≠ C.eval (List.ofFn (row r))
            rwa [good,good]
          obtain ⟨i,di,q⟩ := findAnyChange C wf _ _ C.output rootBound rootDiff
          have on : marked U i = true := by
            cases em : marked U i
            · exact False.elim (di (off i em))
            · rfl
          have i3 : 3 ≤ i.val := by
            by_contra! low
            simp [marked,show ¬3 ≤ i.val by omega] at on
          have ip := (spec i i3).mp on
          have pre := (changeThrough C wf _ _ ip fence.le (beforeW i i3) q).1
          by_cases iw : i.val = w
          · apply di
            rw [← rawValue C (row l) i, ← rawValue C (row r) i, iw]
            exact sw
          · exact changedEndpoint C _ _ pre iw sw
        have d01 := different _ _ _ _ p01
        have d02 := different _ _ _ _ p02
        have d12 := different _ _ _ _ p12
        cases e0 : value C (row (certAt U 0)) w <;>
          cases e1 : value C (row (certAt U 1)) w <;>
          cases e2 : value C (row (certAt U 2)) w
        all_goals first
          | exact d01 (e0.trans e1.symm)
          | exact d02 (e0.trans e2.symm)
          | exact d12 (e1.trans e2.symm)
  · let k : Fin 7 := 0
    obtain ⟨i3,j3,neq⟩ := testPivots k
    have unique (i : Fin 9) (hi : 3 ≤ i.val) :
        ∀ z, path C i.val z → z < C.output → single C z := by
      intro z iz _
      exact singleOf C (fun s => anyShare ⟨z,le_trans hi (pathLe C wf iz),s⟩)
    exact shapeImpossible C wf _ _ _ neq (testSwitch k) C.output
      (unique _ i3) (unique _ j3) C.output le_rfl rootBound false (mainShape C good k)

end PEqualNP.Outside.L_meta_27247

open PEqualNP.Outside.L_meta_27247 in
theorem PEqualNP.Outside.L_meta_27247 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
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
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 9]⟩)
) := by
  rintro ⟨C,_,lim,good,out,wf,_,live,first,second⟩
  exact main C lim good out wf live first second
