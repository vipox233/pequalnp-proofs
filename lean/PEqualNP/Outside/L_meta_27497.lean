import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27497

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

private def pivotLow : Fin 9 → ℕ := ![160,100,82,132,68,66,20,12,10]
private def pivotHigh : Fin 9 → ℕ := ![161,102,86,140,84,98,84,140,266]

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



private theorem prefixAgree : ∀ i : Fin 9, i.val = 1 ∨ i.val = 2 →
    (row (pivotLow i) 1 || row (pivotLow i) 2) =
      (row (pivotHigh i) 1 || row (pivotHigh i) 2) := by decide

private theorem prefixCounts (C : Circuit) (wf : well C) (good : agrees C)
    (root : C.output+1 = 9+C.gates.length)
    (g1 : C.gates[1]? = some ⟨.or,[1,2]⟩) :
    ∀ u, u = 1 ∨ u = 2 → 2 ≤ (used C).count u := by
  have j1b := (List.getElem?_eq_some_iff.mp g1).1
  let j1 : Fin C.gates.length := ⟨1,j1b⟩
  have g1' : C.gates.get j1 = ⟨.or,[1,2]⟩ := (List.getElem?_eq_some_iff.mp g1).2
  have secondValue (x : Fin 9 → Bool) : value C x 10 = (x 1 || x 2) := by
    change value C x (9+j1.val) = _
    rw [gateValue C wf x j1,g1']
    simp [GateOp.eval,← rawValue C x (1 : Fin 9),← rawValue C x (2 : Fin 9)]
  intro u hu
  let i : Fin 9 := ⟨u,by rcases hu with h|h <;> omega⟩
  obtain ⟨v,hv,dv⟩ := pointReader C wf good root (by omega) i
  have raw : reads C u 10 := ⟨j1,rfl,by rw [g1']; simpa using hu⟩
  refine countTwo C hv raw ?_
  intro e
  subst v
  apply dv
  rw [secondValue,secondValue]
  exact prefixAgree i hu

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
    (extra : ∀ u, u = 1 ∨ u = 2 → 2 ≤ (used C).count u)
    (pin : Fin C.gates.length) (pinLen : (C.gates.get pin).inputs.length = 1)
    (w : ℕ) (w3 : 3 ≤ w) (ws : shared C w) :
    single C 0 ∧ ∀ g : Fin C.gates.length, (C.gates.get g).op = .not → g = pin := by
  let weight (j : Fin C.gates.length) := (C.gates.get j).inputs.length + if j = pin then 1 else 0
  have ub (j : Fin C.gates.length) : weight j ≤ 2 := by
    by_cases eq : j = pin
    · subst j
      unfold weight
      rw [pinLen]
      simp
    · simp only [weight,eq,if_false,Nat.add_zero]
      rcases h j with ⟨_,_,_,e⟩ | ⟨_,_,_,_,_,e⟩ <;> rw [e] <;> simp
  have sumWeight : (∑ j : Fin C.gates.length, weight j) = (used C).length + 1 := by
    unfold weight
    rw [Finset.sum_add_distrib,← usedLen]
    simp
  have lenBound : (used C).length + 1 ≤ 2*C.gates.length := by
    rw [← sumWeight]
    calc
      _ ≤ ∑ j : Fin C.gates.length, 2 := Finset.sum_le_sum (fun j _ => ub j)
      _ = _ := by simp [Nat.mul_comm]
  let base (u : ℕ) := 1 + if u = 1 ∨ u = 2 then 1 else 0
  have bSum : ∑ u ∈ Finset.range C.output, base u = C.output + 2 := by
    simp only [base,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
    congr 1
    rw [← Finset.sum_filter]
    have eq : (Finset.range C.output).filter (fun u => u = 1 ∨ u = 2) = {1,2} := by
      ext u
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert,Finset.mem_singleton]
      omega
    rw [eq]
    decide
  have lower (u : ℕ) (hu : u ∈ Finset.range C.output) : base u ≤ (used C).count u := by
    by_cases eq : u = 1 ∨ u = 2
    · unfold base; rw [if_pos eq]; exact extra u eq
    · unfold base; rw [if_neg eq]; exact usedOnce u (Finset.mem_range.mp hu)
  have slack (u : ℕ) (hu : ¬ (u = 1 ∨ u = 2)) (s : shared C u) :
      u ∈ Finset.range C.output ∧ 1 + base u ≤ (used C).count u := by
    obtain ⟨v,t,ne,hv,ht⟩ := s
    have two := countTwo C hv ht ne
    obtain ⟨j,_,hj⟩ := hv
    have l := readsEarlier C h j u hj
    exact ⟨Finset.mem_range.mpr (by have := j.isLt; omega),
      by unfold base; rw [if_neg hu]; exact two⟩
  obtain ⟨mw,lw⟩ := slack w (by omega) ws
  constructor
  · apply singleOf C
    intro s0
    obtain ⟨mz,lz⟩ := slack 0 (by decide) s0
    have ne : w ≠ 0 := by omega
    have sum := Finset.sum_le_sum (s := Finset.range C.output)
      (f := fun u => base u + (if u = w then 1 else 0) + (if u = 0 then 1 else 0))
      (g := fun u => (used C).count u) (by
        intro u mu
        by_cases ew : u = w
        · subst u
          simpa [ne,Nat.add_comm] using lw
        · by_cases ez : u = 0
          · subst u
            simpa [ew,Nat.add_comm] using lz
          · simpa [ew,ez] using lower u mu)
    rw [Finset.sum_add_distrib,Finset.sum_add_distrib,bSum,usedLimits C h out] at sum
    simp [mw,mz] at sum
    omega
  · intro j isNot
    by_contra neq
    have lt := Finset.sum_lt_sum lower ⟨w,mw,by omega⟩
    rw [bSum,usedLimits C h out] at lt
    have jlt : weight j < 2 := by
      simp only [weight,neq,if_false,Nat.add_zero]
      rcases h j with ⟨_,_,_,e⟩ | ⟨op,_,_,_,_,_⟩
      · rw [e]; simp
      · rw [isNot] at op
        cases op <;> contradiction
    have less : (∑ j : Fin C.gates.length, weight j) <
        ∑ j : Fin C.gates.length, 2 :=
      Finset.sum_lt_sum (fun j _ => ub j) ⟨j,Finset.mem_univ _,jlt⟩
    rw [sumWeight] at less
    simp [Nat.mul_comm] at less
    omega
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


private theorem flipInputs :
    row 160 0 = false ∧ row 161 0 = true ∧
    ∀ i : Fin 9, i ≠ 0 → row 160 i = row 161 i := by decide

private theorem notMonotone (C : Circuit) (wf : well C)
    (pin : Fin C.gates.length) (pinZero : pin.val = 0)
    (pinGet : C.gates.get pin = ⟨.not,[0]⟩)
    (only0 : single C 0)
    (onlyNot : ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j = pin) :
    ∀ w < 9+C.gates.length, w ≠ 0 →
      value C (row 161) w ≤ value C (row 160) w := by
  have seed : reads C 0 9 := ⟨pin,by omega,by rw [pinGet]; simp⟩
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro bound nz
    by_cases raw : w < 9
    · let k : Fin 9 := ⟨w,raw⟩
      change value C (row 161) k.val ≤ value C (row 160) k.val
      rw [rawValue,rawValue,flipInputs.2.2 k (by intro e; exact nz (congrArg Fin.val e))]
    · let j : Fin C.gates.length := ⟨w-9,by omega⟩
      have wj : w = 9+j.val := by simp [j]; omega
      rcases wf j with ⟨no,a,ha,inp⟩ | ⟨op,a,b,ab,hb,inp⟩
      · have eq := onlyNot j no
        rw [wj,eq,unaryValue C wf pin 0 (by rw [pinGet]) (by rw [pinGet]),
          unaryValue C wf pin 0 (by rw [pinGet]) (by rw [pinGet])]
        rw [show value C (row 161) 0 = row 161 0 from rawValue C _ (0 : Fin 9),
          show value C (row 160) 0 = row 160 0 from rawValue C _ (0 : Fin 9)]
        decide
      · have noRead (u : ℕ) (hu : u ∈ (C.gates.get j).inputs) : u ≠ 0 := by
          intro eq
          subst u
          have eqR := only0 (9+j.val) 9 ⟨j,rfl,hu⟩ seed
          have eqPin : j = pin := Fin.ext (by omega)
          rw [eqPin,pinGet] at op
          cases op <;> contradiction
        have aa := ih a (by omega) (by omega) (noRead a (by rw [inp]; simp))
        have bb := ih b (by omega) (by omega) (noRead b (by rw [inp]; simp))
        rw [wj,gateValue C wf (row 161) j,gateValue C wf (row 160) j,inp]
        rcases op with ha | ho
        · rw [ha]
          simpa [GateOp.eval] using
            (show (value C (row 161) a && value C (row 161) b) ≤
              (value C (row 160) a && value C (row 160) b) by
              cases e1 : value C (row 161) a <;> cases e2 : value C (row 160) a <;>
                cases e3 : value C (row 161) b <;> cases e4 : value C (row 160) b <;> simp_all)
        · rw [ho]
          simpa [GateOp.eval] using
            (show (value C (row 161) a || value C (row 161) b) ≤
              (value C (row 160) a || value C (row 160) b) by
              cases e1 : value C (row 161) a <;> cases e2 : value C (row 160) a <;>
                cases e3 : value C (row 161) b <;> cases e4 : value C (row 160) b <;> simp_all)

private def testRows : Fin 6 → ℕ := ![87,71,23,295,311,359]

private theorem testSwitch : switchOK testRows 4 6 := by unfold switchOK; decide

private theorem testShape : shape
    (matching (row (testRows 0))) (matching (row (testRows 1)))
    (matching (row (testRows 2))) (matching (row (testRows 3)))
    (matching (row (testRows 4))) (matching (row (testRows 5))) := by unfold shape; decide

private theorem main (C : Circuit) (lim : C.size ≤ 12) (good : agrees C)
    (out : C.output + 1 = 9+C.size) (wf : well C)
    (live : ∀ j : Fin C.gates.length, j.val+1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9+j.val ∈ (C.gates.get k).inputs)
    (first : C.gates.head? = some ⟨.not,[0]⟩)
    (second : C.gates.tail.head? = some ⟨.or,[1,2]⟩) : False := by
  change C.gates.length ≤ 12 at lim
  change C.output + 1 = 9+C.gates.length at out
  have g0 : C.gates[0]? = some ⟨.not,[0]⟩ := by
    simpa only [List.head?_eq_getElem?] using first
  have g1 : C.gates[1]? = some ⟨.or,[1,2]⟩ := by
    simpa only [List.head?_eq_getElem?,List.getElem?_tail,Nat.zero_add] using second
  have positive := (List.getElem?_eq_some_iff.mp g0).1
  let pin : Fin C.gates.length := ⟨0,positive⟩
  have pinGet : C.gates.get pin = ⟨.not,[0]⟩ := (List.getElem?_eq_some_iff.mp g0).2
  have pinLen : (C.gates.get pin).inputs.length = 1 := by rw [pinGet]; rfl
  have one (u : ℕ) (u3 : 3 ≤ u) : single C u := by
    apply singleOf C
    intro sharedU
    obtain ⟨only0,onlyNot⟩ := sharingCount C wf lim out
      (usedBeforeRoot C wf good out positive live) (prefixCounts C wf good out g1)
      pin pinLen u u3 sharedU
    have decreasing := notMonotone C wf pin rfl pinGet only0 onlyNot C.output (by omega) (by omega)
    change C.eval (List.ofFn (row 161)) ≤ C.eval (List.ofFn (row 160)) at decreasing
    rw [good,good] at decreasing
    exact (by decide : ¬ matching (row 161) ≤ matching (row 160)) decreasing
  have unique (i : Fin 9) (hi : 3 ≤ i.val) :
      ∀ z, path C i.val z → z < C.output → single C z := by
    intro z iz _
    exact one z (le_trans hi (pathLe C wf iz))
  apply shapeImpossible C wf testRows 4 6 (by decide) testSwitch C.output
    (unique 4 (by decide)) (unique 6 (by decide)) C.output le_rfl (by omega) false
  change ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = matching x at good
  change shape (C.eval (List.ofFn (row (testRows 0)))) (C.eval (List.ofFn (row (testRows 1))))
    (C.eval (List.ofFn (row (testRows 2)))) (C.eval (List.ofFn (row (testRows 3))))
    (C.eval (List.ofFn (row (testRows 4)))) (C.eval (List.ofFn (row (testRows 5))))
  simpa only [good] using testShape

end PEqualNP.Outside.L_meta_27497

open PEqualNP.Outside.L_meta_27497 in
theorem PEqualNP.Outside.L_meta_27497 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [1, 2]⟩)
) := by
  rintro ⟨C,_,lim,good,out,wf,_,live,first,second⟩
  exact main C lim good out wf live first second
