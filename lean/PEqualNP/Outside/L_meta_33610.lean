import PEqualNP.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_33610_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Ref := Option ℕ
abbrev Bank := List Ref × List Gate

def gateOK (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2

def read (w : List Bool) : Ref → Bool
  | none => false
  | some i => w.getD i false

def evalStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

abbrev wires (w : List Bool) (gs : List Gate) : List Bool := gs.foldl evalStep w

theorem oldAt {α : Type} (l r : List α) {i : ℕ} (hi : i<l.length) (fallback : α) :
    (l++r).getD i fallback = l.getD i fallback := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem newAt {α : Type} (l : List α) (a fallback : α) :
    (l++[a]).getD l.length fallback = a := by
  simp [List.getD_eq_getElem?_getD]

theorem farAt {α : Type} (l : List α) {i : ℕ} (hi : l.length ≤ i) (fallback : α) :
    l.getD i fallback = fallback := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hi]

theorem wires_len (w : List Bool) (gs : List Gate) : (wires w gs).length = w.length+gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [ih,evalStep]; omega

def emit (n : ℕ) (op : GateOp) (is : List ℕ) : Option Gate × Ref :=
  (some ⟨op,is⟩, some n)

def opIsAnd : GateOp → Bool
  | .and => true
  | _ => false

def simplify (n : ℕ) (op : GateOp) : List Ref → Option Gate × Ref
  | [] => if opIsAnd op then emit n op [] else (none,none)
  | [a] => (none,a)
  | [some a,some b] => emit n op [a,b]
  | [some a,none] => if opIsAnd op then (none,none) else (none,some a)
  | [none,some b] => if opIsAnd op then (none,none) else (none,some b)
  | [none,none] => (none,none)
  | _ => (none,none)

private theorem len_cases {α : Type} (as : List α) (h : as.length ≤ 2) :
    as = [] ∨ (∃ a, as=[a]) ∨ (∃ a b, as=[a,b]) := by
  rcases as with _ | ⟨a,as⟩
  · exact Or.inl rfl
  rcases as with _ | ⟨b,as⟩
  · exact Or.inr (Or.inl ⟨a,rfl⟩)
  rcases as with _ | ⟨c,as⟩
  · exact Or.inr (Or.inr ⟨a,b,rfl⟩)
  · simp at h

theorem simplify_sound (w : List Bool) {op : GateOp} (ok : op=.and ∨ op=.or)
    (rs : List Ref) (short : rs.length ≤ 2) :
    let s := simplify w.length op rs
    read (wires w s.1.toList) s.2 = op.eval (rs.map (read w)) := by
  rcases len_cases rs short with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · rcases ok with rfl | rfl <;> simp [simplify,opIsAnd,emit,read,List.foldl,evalStep,GateOp.eval]
  · rcases ok with rfl | rfl <;> simp [simplify,read,GateOp.eval]
  · cases a <;> cases b <;> rcases ok with rfl | rfl <;>
      simp [simplify,opIsAnd,emit,read,List.foldl,evalStep,GateOp.eval]

theorem simplify_bounded (w : List Bool) (op : GateOp) (rs : List Ref)
    (short : rs.length ≤ 2) (bounds : ∀ i, some i ∈ rs → i<w.length) :
    let s := simplify w.length op rs
    ∀ i, s.2=some i → i < (wires w s.1.toList).length := by
  rcases len_cases rs short with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · by_cases h : opIsAnd op = true <;> simp [simplify,h,emit,evalStep]
  · cases a <;> simp_all [simplify]
  · by_cases h : opIsAnd op = true <;> cases a <;> cases b <;>
      simp_all [simplify,emit,evalStep]

theorem simplify_legal (n : ℕ) {op : GateOp} (ok : op=.and ∨ op=.or)
    (rs : List Ref) (short : rs.length ≤ 2) :
    ∀ g ∈ (simplify n op rs).1.toList, gateOK g := by
  rcases len_cases rs short with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · rcases ok with rfl | rfl <;> simp [simplify,opIsAnd,emit,gateOK]
  · simp [simplify]
  · cases a <;> cases b <;> rcases ok with rfl | rfl <;>
      simp [simplify,opIsAnd,emit,gateOK]

theorem drop_on_false (n : ℕ) (op : GateOp)
    (rs : List Ref) (short : rs.length ≤ 2) (onFalse : none ∈ rs) :
    (simplify n op rs).1=none := by
  rcases len_cases rs short with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · simp at onFalse
  · rfl
  · cases a <;> cases b <;> by_cases h : opIsAnd op = true <;> simp_all [simplify]

theorem false_on_all (n : ℕ) (op : GateOp)
    (rs : List Ref) (short : rs.length ≤ 2) (nonempty : rs ≠ [])
    (onFalse : ∀ r ∈ rs, r=none) : (simplify n op rs).2=none := by
  rcases len_cases rs short with rfl | ⟨a,rfl⟩ | ⟨a,b,rfl⟩
  · contradiction
  · have eq := onFalse a (by simp)
    simp [simplify,eq]
  · have eq1 := onFalse a (by simp)
    have eq2 := onFalse b (by simp)
    simp [simplify,eq1,eq2]

def refs (A : Bank) (g : Gate) : List Ref := g.inputs.map (fun i => A.1.getD i none)

def proposal (n : ℕ) (A : Bank) (g : Gate) : Option Gate × Ref :=
  simplify (n+A.2.length) g.op (refs A g)

def advance (n : ℕ) (A : Bank) (g : Gate) : Bank :=
  (A.1++[(proposal n A g).2], A.2++(proposal n A g).1.toList)

theorem adv_refs (n : ℕ) (A : Bank) (g : Gate) : (advance n A g).1.length=A.1.length+1 := by
  simp [advance]

theorem adv_len (n : ℕ) (A : Bank) (g : Gate) : (advance n A g).2.length ≤ A.2.length+1 := by
  have : (proposal n A g).1.toList.length ≤ 1 := by cases (proposal n A g).1 <;> simp
  simp [advance]

theorem adv_drop (n : ℕ) (A : Bank) (g : Gate) (h : none ∈ refs A g)
    (ok : gateOK g) : (advance n A g).2.length=A.2.length := by
  have stop := drop_on_false (n+A.2.length) g.op (refs A g)
    (by simpa [refs] using ok.2) h
  simp [advance,proposal,stop]

theorem adv_none (n : ℕ) (A : Bank) (g : Gate) (ok : gateOK g)
    (notEmpty : g.inputs ≠ []) (allBad : ∀ i ∈ g.inputs, A.1.getD i none=none) :
    (advance n A g).1.getD A.1.length none=none := by
  rw [advance,newAt]
  apply false_on_all
  · simpa [refs] using ok.2
  · simpa [refs] using notEmpty
  · intro r hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact allBad i hi

def Sim (xs ys : List Bool) (A : Bank) : Prop :=
  xs.length=A.1.length ∧
  (∀ i, xs.getD i false=read (wires ys A.2) (A.1.getD i none)) ∧
  (∀ i j, A.1.getD i none=some j → j<(wires ys A.2).length)

theorem sim_step {xs ys : List Bool} {A : Bank} {g : Gate}
    (h : Sim xs ys A) (ok : gateOK g) : Sim (evalStep xs g) ys (advance ys.length A g) := by
  let w := wires ys A.2
  let s := proposal ys.length A g
  have eqLen : w.length=ys.length+A.2.length := wires_len _ _
  have eqS : s=simplify w.length g.op (refs A g) := by simp [s,proposal,eqLen]
  have newW : wires ys (advance ys.length A g).2 = wires w s.1.toList := by
    simp [advance,s,w,List.foldl_append]
  have sameVals : g.inputs.map (fun j => xs.getD j false) = (refs A g).map (read w) := by
    simp only [refs,List.map_map,Function.comp_def]
    exact List.map_congr_left (fun j _ => h.2.1 j)
  have sound := simplify_sound w ok.1 (refs A g) (by simpa [refs] using ok.2)
  have indexBound := simplify_bounded w g.op (refs A g) (by simpa [refs] using ok.2) (by
    intro j hj
    obtain ⟨i,_,eq⟩ := List.mem_map.mp hj
    exact h.2.2 i j eq)
  rw [← eqS] at sound indexBound
  have len := h.1
  refine ⟨by simp [evalStep,advance,len], ?_, ?_⟩
  · intro i
    rw [newW]
    change (xs++[_]).getD i false = read (wires w s.1.toList) ((A.1++[s.2]).getD i none)
    rcases lt_trichotomy i A.1.length with small | same | big
    · rw [oldAt _ _ (by simpa only [len] using small),oldAt _ _ small,h.2.1 i]
      cases eq : A.1.getD i none with
      | none => rfl
      | some j =>
        have bound := h.2.2 i j eq
        simp only [read]
        have pref : ∃ tail, wires w s.1.toList=w++tail := by
          cases s.1 <;> simp [List.foldl,evalStep]
        obtain ⟨tail,rt⟩ := pref
        rw [rt,oldAt _ _ bound]
    · subst i
      have en : A.1.length = xs.length := len.symm
      rw [newAt, en, newAt]
      rw [sameVals]
      exact sound.symm
    · have f1 : (xs++[g.op.eval (List.map (fun i => xs.getD i false) g.inputs)]).length ≤ i := by
        simp; omega
      have f2 : (A.1++[s.2]).length ≤ i := by simp; omega
      rw [farAt _ f1,farAt _ f2]
      rfl
  · intro i j hj
    rw [newW]
    change (A.1++[s.2]).getD i none=some j at hj
    rcases lt_trichotomy i A.1.length with small | same | big
    · rw [oldAt _ _ small] at hj
      have bound : w.length ≤ (wires w s.1.toList).length := by
        calc
          w.length ≤ w.length+s.1.toList.length := Nat.le_add_right _ _
          _ = (wires w s.1.toList).length := (wires_len _ _).symm
      exact (h.2.2 i j hj).trans_le bound
    · subst i
      rw [newAt] at hj
      exact indexBound j hj
    · have f2 : (A.1++[s.2]).length ≤ i := by simp; omega
      rw [farAt _ f2] at hj
      contradiction

theorem sim_all {xs ys : List Bool} (gs : List Gate)
    (ok : ∀ g ∈ gs, gateOK g) (A : Bank) (h : Sim xs ys A) :
    Sim (wires xs gs) ys (gs.foldl (advance ys.length) A) := by
  induction gs generalizing xs A with
  | nil => exact h
  | cons g gs ih =>
    have hg := ok g (by simp)
    exact ih (fun f hf => ok f (by simp [hf])) _ (sim_step h hg)

theorem run_legal (n : ℕ) (gs : List Gate) (ok : ∀ g ∈ gs, gateOK g)
    (A : Bank) (old : ∀ g ∈ A.2, gateOK g) :
    ∀ g ∈ (gs.foldl (advance n) A).2, gateOK g := by
  induction gs generalizing A with
  | nil => exact old
  | cons g gs ih =>
    apply ih (fun f hf => ok f (by simp [hf]))
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact old f hf
    · have hg := ok g (by simp)
      exact simplify_legal _ hg.1 _ (by simpa [refs] using hg.2) _ hf

end PEqualNP.Outside.L_meta_33610_aux

namespace PEqualNP.Outside.L_meta_33610_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def initial {n : ℕ} (a : Fin (n+1)) : Bank :=
  (List.ofFn (a.insertNth none (fun i : Fin n => some i.val)), [])

def lifted {n : ℕ} (a : Fin (n+1)) (x : Fin n → Bool) : Fin (n+1) → Bool :=
  a.insertNth false x

theorem getD_ofFn {α : Type} {n : ℕ} (f : Fin n → α) (i : Fin n) (d : α) :
    (List.ofFn f).getD i.val d = f i := by
  simp [List.getD_eq_getElem?_getD,i.isLt]

theorem initial_len {n : ℕ} (a : Fin (n+1)) : (initial a).1.length=n+1 := by
  simp [initial]

theorem initial_a {n : ℕ} (a : Fin (n+1)) : (initial a).1.getD a.val none=none := by
  rw [initial,getD_ofFn,Fin.insertNth_apply_same]

theorem lifted_count {n : ℕ} (a : Fin (n+1)) (x : Fin n → Bool) :
    (List.ofFn (lifted a x)).count true=(List.ofFn x).count true := by
  classical
  simp only [List.count_ofFn]
  let S := Finset.univ.filter (fun j : Fin n => x j = true)
  have h : (Finset.univ.filter (fun j => lifted a x j = true)) = S.image a.succAbove := by
    ext i
    refine Fin.succAboveCases a ?_ (fun j => ?_) i
    · constructor
      · intro h
        have hh := (Finset.mem_filter.mp h).2
        change lifted a x a = true at hh
        simp [lifted] at hh
      · intro h
        obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
        exact (Fin.succAbove_ne _ _ hj).elim
    · constructor
      · intro h
        have val := (Finset.mem_filter.mp h).2
        have val' : x j = true := by simpa [lifted] using val
        exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,val'⟩,rfl⟩
      · intro h
        obtain ⟨k,hk,hkj⟩ := Finset.mem_image.mp h
        have eq := (Fin.succAbove_right_injective (p := a)) hkj
        subst k
        have val := (Finset.mem_filter.mp hk).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [lifted] using val⟩
  rw [h,Finset.card_image_of_injective _ Fin.succAbove_right_injective]

theorem initial_sim {n : ℕ} (a : Fin (n+1)) (x : Fin n → Bool) :
    Sim (List.ofFn (lifted a x)) (List.ofFn x) (initial a) := by
  refine ⟨by simp [initial],?_,?_⟩
  · intro i
    by_cases hi : i<n+1
    · let j : Fin (n+1) := ⟨i,hi⟩
      change (List.ofFn (lifted a x)).getD j.val false =
        read (List.ofFn x) ((List.ofFn (a.insertNth none (fun k : Fin n => some k.val))).getD j.val none)
      rw [getD_ofFn,getD_ofFn]
      refine Fin.succAboveCases a ?_ (fun k => ?_) j
      · simp [lifted,read]
      · simp [lifted,read]
    · rw [farAt _ (by simpa using Nat.le_of_not_gt hi),
          farAt _ (by simpa [initial] using Nat.le_of_not_gt hi)]
      rfl
  · intro i j eq
    by_cases hi : i<n+1
    · let k : Fin (n+1) := ⟨i,hi⟩
      change (List.ofFn (a.insertNth none (fun l : Fin n => some l.val))).getD k.val none=some j at eq
      rw [getD_ofFn] at eq
      have bound : ∀ b : Fin (n+1), @Fin.insertNth n (fun _ => Ref) a none (fun l => some l.val) b=some j → j<n := by
        intro b
        refine Fin.succAboveCases a ?_ (fun l => ?_) b
        · simp
        · intro h
          simp at h
          exact h ▸ l.isLt
      simpa [wires_len,initial] using bound k eq
    · rw [farAt _ (by simpa [initial] using Nat.le_of_not_gt hi)] at eq
      contradiction

def snapshot {n : ℕ} (a : Fin (n+1)) (gs : List Gate) (i : ℕ) : Bank :=
  (gs.take i).foldl (advance n) (initial a)

theorem snap_step {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {j : ℕ} (h : j < gs.length) :
    snapshot a gs (j+1) = advance n (snapshot a gs j) gs[j] := by
  unfold snapshot
  rw [List.take_succ_eq_append_getElem h,List.foldl_append]
  rfl

theorem snap_full {n : ℕ} (a : Fin (n+1)) (gs : List Gate) :
    snapshot a gs gs.length = gs.foldl (advance n) (initial a) := by
  simp [snapshot]

theorem snap_refs_len {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {j : ℕ} (le : j ≤ gs.length) :
    (snapshot a gs j).1.length=n+1+j := by
  induction j with
  | zero => simp [snapshot,initial]
  | succ j ih =>
    rw [snap_step a (by omega),adv_refs,ih (by omega)]
    rfl

theorem snap_keep {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {i j k : ℕ}
    (ij : i ≤ j) (jlen : j ≤ gs.length) (range : k<n+1+i) :
    (snapshot a gs j).1.getD k none=(snapshot a gs i).1.getD k none := by
  induction ij with
  | refl => rfl
  | @step j ij ih =>
    have jlt : j<gs.length := by omega
    rw [snap_step a jlt]
    change ((snapshot a gs j).1++[_]).getD k none=_
    have range' : k < (snapshot a gs j).1.length := by
      rw [snap_refs_len a (show j ≤ gs.length by omega)]
      exact range.trans_le (Nat.add_le_add_left ij _)
    rw [oldAt _ _ range']
    exact ih (by omega)

theorem snap_a {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {j : ℕ} (le : j ≤ gs.length) :
    (snapshot a gs j).1.getD a.val none=none := by
  rw [snap_keep a (i:=0) (Nat.zero_le _) le (by simpa using a.isLt)]
  exact initial_a a

theorem snap_count {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {i j : ℕ}
    (ij : i ≤ j) (jlen : j ≤ gs.length) :
    (snapshot a gs j).2.length ≤ (snapshot a gs i).2.length+(j-i) := by
  induction ij with
  | refl => simp
  | @step j ij ih =>
    have le := ih (by omega)
    rw [snap_step a (show j<gs.length by omega)]
    have next := adv_len n (snapshot a gs j) gs[j]
    have diff : j+1-i=j-i+1 := Nat.succ_sub ij
    rw [diff,← Nat.add_assoc]
    exact next.trans (Nat.add_le_add_right le 1)

theorem snap_drop {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {j w : ℕ}
    (jlt : j<gs.length) (legal : gateOK gs[j])
    (reads : w ∈ gs[j].inputs) (zero : (snapshot a gs j).1.getD w none=none) :
    (snapshot a gs (j+1)).2.length=(snapshot a gs j).2.length := by
  rw [snap_step a jlt]
  exact adv_drop _ _ _ (List.mem_map.mpr ⟨w,reads,zero⟩) legal

theorem snap_none {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {j : ℕ}
    (jlt : j<gs.length) (legal : gateOK gs[j]) (nonempty : gs[j].inputs ≠ [])
    (zeros : ∀ w ∈ gs[j].inputs, (snapshot a gs j).1.getD w none=none) :
    (snapshot a gs (j+1)).1.getD (n+1+j) none=none := by
  rw [snap_step a jlt,← snap_refs_len a (by omega : j ≤ gs.length)]
  exact adv_none _ _ _ legal nonempty zeros

theorem head_zero {n b : ℕ} (a : Fin (n+1)) {gs : List Gate}
    (hl : 0<gs.length) (first : gs[0]=⟨.and,[a.val,b]⟩) :
    (snapshot a gs 1).1.getD (n+1) none=none := by
  rw [snap_step a hl,first]
  change ((initial a).1++[(proposal n (initial a) ⟨.and,[a.val,b]⟩).2]).getD (n+1) none=none
  have next := newAt (initial a).1 (proposal n (initial a) ⟨.and,[a.val,b]⟩).2 none
  rw [initial_len a] at next
  rw [next]
  simp only [proposal,refs,List.map_cons,List.map_nil,initial_a]
  cases (initial a).1.getD b none <;> simp [simplify,opIsAnd]

theorem three_savings {n : ℕ} (a : Fin (n+1)) {gs : List Gate} {j k : ℕ}
    (pj : 0<j) (jk : j<k) (kl : k<gs.length)
    (d0 : (snapshot a gs 1).2.length=(snapshot a gs 0).2.length)
    (dj : (snapshot a gs (j+1)).2.length=(snapshot a gs j).2.length)
    (dk : (snapshot a gs (k+1)).2.length=(snapshot a gs k).2.length) :
    (snapshot a gs gs.length).2.length+3 ≤ gs.length := by
  have h1 := snap_count a (gs:=gs) (i:=1) (j:=j) (by omega) (by omega)
  have h2 := snap_count a (gs:=gs) (i:=j+1) (j:=k) (by omega) (by omega)
  have h3 := snap_count a (gs:=gs) (i:=k+1) (j:=gs.length) (by omega) (by omega)
  have start : (snapshot a gs 0).2.length = 0 := rfl
  omega

end PEqualNP.Outside.L_meta_33610_aux

namespace PEqualNP.Outside.L_meta_33610_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def supported {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

theorem count_support {n : ℕ} (S : Finset (Fin n)) :
    (List.ofFn (supported S)).count true = S.card := by
  rw [List.count_ofFn]
  congr 1
  ext i
  simp [supported]

theorem except_append {k : ℕ} {w z : List Bool}
    (len : w.length=z.length)
    (agree : ∀ i, i ≠ k → w.getD i false=z.getD i false) (v : Bool) :
    ∀ i, i ≠ k → (w++[v]).getD i false=(z++[v]).getD i false := by
  intro i hi
  rcases lt_trichotomy i w.length with lt | eq | gt
  · rw [oldAt _ _ lt,oldAt _ _ (by omega),agree _ hi]
  · have eq' : i=z.length := eq.trans len
    conv_lhs => rw [eq,newAt]
    conv_rhs => rw [eq',newAt]
  · have l1 : (w++[v]).length ≤ i := by simp; omega
    have l2 : (z++[v]).length ≤ i := by simp; omega
    rw [farAt _ l1,farAt _ l2]

theorem except_tail {k : ℕ} (gs : List Gate) (unused : ∀ g ∈ gs, k ∉ g.inputs)
    {w z : List Bool} (len : w.length=z.length)
    (agree : ∀ i, i ≠ k → w.getD i false=z.getD i false) :
    ∀ i, i ≠ k → (wires w gs).getD i false=(wires z gs).getD i false := by
  induction gs generalizing w z with
  | nil => exact agree
  | cons g gs ih =>
    have hg := unused g (by simp)
    have equal : g.inputs.map (fun i => w.getD i false) =
        g.inputs.map (fun i => z.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact agree i (fun eq => hg (eq ▸ hi))
    have after : (evalStep w g).length=(evalStep z g).length := by simp [evalStep,len]
    have valid : ∀ i, i ≠ k → (evalStep w g).getD i false=(evalStep z g).getD i false := by
      simpa only [evalStep,equal] using except_append len agree (g.op.eval (g.inputs.map (fun i => z.getD i false)))
    exact ih (fun g hg => unused g (by simp [hg])) after valid

def WeightTwo (n : ℕ) (C : Circuit) : Prop :=
  (∀ x : Fin n → Bool, (List.ofFn x).count true=2 → C.eval (List.ofFn x)=true) ∧
  (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x)=false)

theorem a_reader {n : ℕ} (a b : Fin (n+1)) (ne : a ≠ b) (large : 2 ≤ n)
    (tail : List Gate) (o : ℕ) (out : o ≠ a.val)
    (exactness : WeightTwo (n+1) ⟨⟨.and,[a.val,b.val]⟩::tail,o⟩) :
    ∃ g ∈ tail, a.val ∈ g.inputs := by
  obtain ⟨c,ca,cb⟩ := Fin.exists_ne_and_ne_of_two_lt a b (by omega)
  let x := supported ({c} : Finset (Fin (n+1)))
  let y := supported ({a,c} : Finset (Fin (n+1)))
  let u := List.ofFn x
  let v := List.ofFn y
  let g : Gate := ⟨.and,[a.val,b.val]⟩
  have xcount : u.count true ≤ 1 := by
    change (List.ofFn (supported ({c} : Finset (Fin (n+1))))).count true ≤ 1
    rw [count_support]
    simp
  have ycount : v.count true=2 := by
    change (List.ofFn (supported ({a,c} : Finset (Fin (n+1))))).count true=2
    rw [count_support]
    simp [Ne.symm ca]
  have xval := exactness.2 x xcount
  have yval := exactness.1 y ycount
  by_contra no
  have unused : ∀ f ∈ tail, a.val ∉ f.inputs := fun f hf hn => no ⟨f,hf,hn⟩
  have equalLen : u.length=v.length := by simp [u,v]
  have equalOutside (i : ℕ) (different : i ≠ a.val) : u.getD i false=v.getD i false := by
    by_cases hi : i<n+1
    · let k : Fin (n+1) := ⟨i,hi⟩
      have ka : k ≠ a := fun e => different (congrArg Fin.val e)
      change u.getD k.val false=v.getD k.val false
      dsimp [u,v]
      rw [getD_ofFn,getD_ofFn]
      simp [x,y,supported,ka]
    · rw [farAt _ (by simpa [u] using Nat.le_of_not_gt hi),
          farAt _ (by simpa [v] using Nat.le_of_not_gt hi)]
  have bx : u.getD b.val false=false := by
    dsimp [u]
    rw [getD_ofFn]
    simp [x,supported,Ne.symm cb]
  have by' : v.getD b.val false=false := by
    dsimp [v]
    rw [getD_ofFn]
    simp [y,supported,Ne.symm cb,Ne.symm ne]
  have gU : evalStep u g=u++[false] := by
    simp only [evalStep,g,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,bx,Bool.and_true,Bool.and_false]
  have gV : evalStep v g=v++[false] := by
    simp only [evalStep,g,GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,by',Bool.and_true,Bool.and_false]
  have equalOutputs := except_tail tail unused
    (w:=evalStep u g) (z:=evalStep v g) (by simp [gU,gV,equalLen])
    (by rw [gU,gV]; exact except_append equalLen equalOutside false) o out
  change (wires (evalStep u g) tail).getD o false=false at xval
  change (wires (evalStep v g) tail).getD o false=true at yval
  rw [xval,yval] at equalOutputs
  cases equalOutputs

private theorem dual_inputs {as : List ℕ} {a b : ℕ}
    (len : as.length ≤ 2) (ne : a ≠ b) (ha : a ∈ as) (hb : b ∈ as) :
    ∀ u ∈ as, u=a ∨ u=b := by
  rcases len_cases as len with rfl | ⟨i,rfl⟩ | ⟨i,j,rfl⟩
  · simp at ha
  · simp at ha hb
    exact (ne (ha.trans hb.symm)).elim
  · simp [List.mem_cons] at ha hb
    rcases ha with rfl | rfl
    · rcases hb with eq | rfl
      · exact (ne eq.symm).elim
      · intro u hu
        simpa using hu
    · rcases hb with rfl | eq
      · intro u hu
        simpa [or_comm] using hu
      · exact (ne eq.symm).elim

theorem compact {n : ℕ} (a b : Fin (n+1)) (lt : a.val < b.val) (large : 2 ≤ n)
    (C : Circuit) (mono : Monotone2 C)
    (head : C.gates.head?=some ⟨.and,[a.val,b.val]⟩)
    (lastOut : C.output+1=(n+1)+C.size)
    (connected : ∀ j : Fin C.gates.length, j.val+1<C.gates.length →
      ∃ k : Fin C.gates.length, j.val<k.val ∧ n+1+j.val ∈ (C.gates.get k).inputs)
    (exactness : WeightTwo (n+1) C) :
    ∃ D : Circuit, Monotone2 D ∧ D.size+3 ≤ C.size ∧ WeightTwo n D := by
  classical
  let gs := C.gates
  have pos : 0<gs.length := by
    cases eq : C.gates with
    | nil => simp [eq] at head
    | cons g tail => simp [gs,eq]
  have headGate : gs[0]=⟨.and,[a.val,b.val]⟩ := by
    simpa [gs,List.head?_eq_getElem?,pos] using head
  have Cgs : C=⟨gs,C.output⟩ := by cases C; rfl
  have a_ne_b : a ≠ b := fun eq => (Nat.ne_of_lt lt) (congrArg Fin.val eq)
  have badOut : C.output ≠ a.val := by
    simp only [Circuit.size] at lastOut
    have := a.isLt
    omega
  have ok (g) (hg : g ∈ gs) : gateOK g := by
    simpa [gateOK] using mono g hg
  have gok (j) (bound : j<gs.length) : gateOK gs[j] :=
    ok _ (List.getElem_mem bound)
  let F := snapshot a gs gs.length
  have simulation (x : Fin n → Bool) :
      Sim (C.wires (List.ofFn (lifted a x))) (List.ofFn x) F := by
    have h := sim_all gs ok (initial a) (initial_sim a x)
    change Sim (wires (List.ofFn (lifted a x)) gs) (List.ofFn x) (snapshot a gs gs.length)
    rw [snap_full]
    simpa only [List.length_ofFn] using h
  have outLive : F.1.getD C.output none ≠ none := by
    intro stop
    let i : Fin n := ⟨0,by omega⟩
    let j : Fin n := ⟨1,by omega⟩
    have neIJ : i ≠ j := fun e => by
      have := congrArg Fin.val e
      simp [i,j] at this
    let x := supported {i,j}
    have cnt : (List.ofFn (lifted a x)).count true=2 := by
      rw [lifted_count,count_support]
      simp [neIJ]
    have on := exactness.1 (lifted a x) cnt
    have off := (simulation x).2.1 C.output
    rw [stop] at off
    have contradiction : true=false := on.symm.trans off
    cases contradiction
  have openerFalse := head_zero a pos headGate
  have gateZero (j : ℕ) (lj : 1 ≤ j) (jl : j ≤ gs.length) :
      (snapshot a gs j).1.getD (n+1) none=none := by
    rw [snap_keep a lj jl (by omega : n+1<n+1+1)]
    exact openerFalse
  have headNonLast : 1<gs.length := by
    by_contra! small
    have eq : C.output=n+1 := by
      simp only [Circuit.size] at lastOut
      change 0<C.gates.length at pos
      change C.gates.length ≤ 1 at small
      omega
    exact outLive (by rw [eq]; exact gateZero _ (by omega) le_rfl)
  have drop0 : (snapshot a gs 1).2.length=(snapshot a gs 0).2.length := by
    apply snap_drop a pos (gok 0 pos) (w:=a.val)
    · simp [headGate]
    · exact snap_a a (Nat.zero_le _)
  have rawReader : ∃ (j : ℕ) (hj : j<gs.length), 0<j ∧ a.val ∈ gs[j].inputs := by
    cases eq : gs with
    | nil => simp [eq] at pos
    | cons g tail =>
      have hg : g=⟨.and,[a.val,b.val]⟩ := by simpa [eq] using headGate
      have same : C=⟨⟨.and,[a.val,b.val]⟩::tail,C.output⟩ := by
        conv_lhs => rw [Cgs]
        rw [eq,hg]
      obtain ⟨f,hf,hr⟩ := a_reader a b a_ne_b large tail C.output badOut (same ▸ exactness)
      obtain ⟨j,lt,rfl⟩ := List.getElem_of_mem hf
      refine ⟨j+1,by simpa using lt,by omega,?_⟩
      simpa using hr
  obtain ⟨u,ul,upos,ureads⟩ := rawReader
  obtain ⟨v, uv, vreads⟩ := connected ⟨0,pos⟩ headNonLast
  have vpos : 0<v.val := uv
  change n+1+0 ∈ gs[v.val].inputs at vreads
  simp only [Nat.add_zero] at vreads
  have dropU := snap_drop a ul (gok u ul) ureads (snap_a a (Nat.le_of_lt ul))
  have dropV := snap_drop a v.isLt (gok v.val v.isLt) vreads
    (gateZero v.val (by omega) (Nat.le_of_lt v.isLt))
  have saved : F.2.length+3 ≤ gs.length := by
    rcases lt_trichotomy u v.val with hv | same | hv
    · exact three_savings a upos hv v.isLt drop0 dropU dropV
    · have also : n+1 ∈ gs[u].inputs := by simpa only [same] using vreads
      have two := dual_inputs (gok u ul).2 (by have := a.isLt; omega : a.val ≠ n+1) ureads also
      have zeroFor : ∀ w ∈ gs[u].inputs, (snapshot a gs u).1.getD w none=none := by
        intro w hw
        rcases two w hw with rfl | rfl
        · exact snap_a a (Nat.le_of_lt ul)
        · exact gateZero _ (by omega) (Nat.le_of_lt ul)
      have report : (snapshot a gs (u+1)).1.getD (n+1+u) none=none :=
        snap_none a ul (gok u ul) (by intro eq; simp [eq] at ureads) zeroFor
      have earlier : u+1<gs.length := by
        by_contra! small
        have outAt : C.output=n+1+u := by
          change C.gates.length ≤ u+1 at small
          simp only [Circuit.size] at lastOut
          omega
        rw [outAt] at outLive
        exact outLive ((snap_keep a (by omega : u+1 ≤ gs.length) le_rfl
          (by omega : n+1+u<n+1+(u+1))).trans report)
      obtain ⟨w,after,uses⟩ := connected ⟨u,ul⟩ earlier
      change u < w.val at after
      change n+1+u ∈ gs[w.val].inputs at uses
      have wZero : (snapshot a gs w.val).1.getD (n+1+u) none=none :=
        (snap_keep a (by omega : u+1 ≤ w.val) (Nat.le_of_lt w.isLt)
          (by omega : n+1+u<n+1+(u+1))).trans report
      have dropW := snap_drop a w.isLt (gok w.val w.isLt) uses wZero
      exact three_savings a upos after w.isLt drop0 dropU dropW
    · exact three_savings a vpos hv ul drop0 dropV dropU
  obtain ⟨out,fo⟩ : ∃ out, F.1.getD C.output none=some out := by
    cases eq : F.1.getD C.output none with
    | none => exact (outLive eq).elim
    | some out => exact ⟨out,rfl⟩
  let D : Circuit := ⟨F.2,out⟩
  refine ⟨D,?_,saved,?_⟩
  · intro f hf
    have h : gateOK f := run_legal n gs ok (initial a) (by simp [initial]) f
      (by simpa [D,F,snap_full] using hf)
    simpa [gateOK] using h
  · have preserve (x : Fin n → Bool) :
        D.eval (List.ofFn x)=C.eval (List.ofFn (lifted a x)) := by
      have h := (simulation x).2.1 C.output
      rw [fo] at h
      exact h.symm
    constructor
    · intro x hx
      rw [preserve]
      exact exactness.1 _ (by rwa [lifted_count])
    · intro x hx
      rw [preserve]
      exact exactness.2 _ (by rwa [lifted_count])

end PEqualNP.Outside.L_meta_33610_aux

open PEqualNP.Outside.L_meta_33610_aux in
theorem PEqualNP.Outside.L_meta_33610 :
∀ (n a b : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ n → PEqualNP.MetaComplexity.Monotone2 C → a < b → b < n + 1 → C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [a, b]⟩ → C.output + 1 = (n + 1) + C.size → (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length → ∃ k : Fin C.gates.length, j.val < k.val ∧ (n + 1) + j.val ∈ (C.gates.get k).inputs) → (∀ x : Fin (n + 1) → Bool, (List.ofFn x).count true = 2 → C.eval (List.ofFn x) = true) ∧ (∀ x : Fin (n + 1) → Bool, (List.ofFn x).count true ≤ 1 → C.eval (List.ofFn x) = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size + 3 ≤ C.size ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true = 2 → D.eval (List.ofFn x) = true) ∧ (∀ x : Fin n → Bool, (List.ofFn x).count true ≤ 1 → D.eval (List.ofFn x) = false)
  := by
  intro n a b C hn mono ab bn head output connected exactness
  let i : Fin (n+1) := ⟨a,by omega⟩
  let j : Fin (n+1) := ⟨b,bn⟩
  exact compact i j ab hn C mono head output connected exactness
