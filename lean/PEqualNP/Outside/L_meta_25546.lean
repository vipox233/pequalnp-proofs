import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def read (C : Circuit) (w : Nat) := readsIn C (Finset.range C.size) w
def use (C : Circuit) (w : Nat) := read C w + (if C.output=w then 1 else 0)
def E (N : Nat) (C : Circuit) := ∑ w ∈ Finset.range (N+C.size), (use C w - 1)
def excess (N : Nat) (C : Circuit) := ∑ w ∈ Finset.range N, (read C w - 1)
def unary (C : Circuit) := (C.gates.filter (fun g => g.inputs.length == 1)).length
def mixed (N : Nat) (C : Circuit) :=
  (C.gates.filter (fun g => g.inputs.length == 2 && (g.inputs.filter (fun w => w<N)).length == 1)).length
def shapes (C : Circuit) : Prop := ∀ g ∈ C.gates,
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length=2) ∨ (g.op=GateOp.not ∧ g.inputs.length=1)
def live (N : Nat) (C : Circuit) : Prop :=
  ∀ j : Fin C.gates.length, N+j.val ≠ C.output → 0 < read C (N+j.val)

end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux.PruneWire
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem getD_snoc (w : List Bool) (x : Bool) (i : ℕ) :
    (w ++ [x]).getD i false =
      if i < w.length then w.getD i false else if i = w.length then x else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : 1 ≤ i - w.length := by omega
    rw [List.getElem?_eq_none (by simpa using this)]; rfl

theorem getD_big (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

theorem fold_stab (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    simp only [step, getD_snoc, if_pos h]

theorem main_fold2 (n m p : ℕ) (B : List Gate)
    (hB : ∀ g ∈ B, n + m ∉ g.inputs) (w w' : List Bool)
    (hl : w.length = w'.length + 1) (hm : n + m ≤ w'.length)
    (hI : ∀ i, i ≠ n + m → w.getD i false = w'.getD (eraseRedirect n m p i) false) :
    ∀ i, i ≠ n + m → (B.foldl step w).getD i false =
      ((B.map (fun g => (⟨g.op, g.inputs.map (eraseRedirect n m p)⟩ : Gate))).foldl step
        w').getD (eraseRedirect n m p i) false := by
  induction B generalizing w w' with
  | nil => simpa using hI
  | cons g B ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    apply ih (fun g' hg' => hB g' (by simp [hg']))
    · simp [step, hl]
    · simp [step]; omega
    · intro i hi
      simp only [step, getD_snoc, List.map_map]
      have hx : g.op.eval (g.inputs.map fun i => w.getD i false) =
          g.op.eval (g.inputs.map ((fun i => w'.getD i false) ∘ eraseRedirect n m p)) := by
        congr 1
        apply List.map_congr_left
        intro a ha
        exact hI a (fun h => hg (h ▸ ha))
      have hIi := hI i hi
      obtain ⟨r, hr⟩ : ∃ r, r = eraseRedirect n m p i := ⟨_, rfl⟩
      rw [← hr] at hIi ⊢
      unfold eraseRedirect at hr
      rw [if_neg hi] at hr
      by_cases h1 : i < w.length
      · have hr1 : r < w'.length := by split_ifs at hr <;> omega
        rw [if_pos h1, if_pos hr1]; exact hIi
      · rw [if_neg h1]
        by_cases h2 : i = w.length
        · have h4 : r = w'.length := by split_ifs at hr <;> omega
          rw [if_pos h2, if_neg (by omega), if_pos h4]
          exact hx
        · have h4 : w'.length < r := by split_ifs at hr <;> omega
          rw [if_neg h2, if_neg (by omega), if_neg (by omega)]

theorem split_fold (C : Circuit) (x : List Bool) (m : ℕ) (hm : m < C.gates.length) :
    C.gates.foldl step x = (C.gates.drop (m + 1)).foldl step
      (step ((C.gates.take m).foldl step x) C.gates[m]) := by
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by simp
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]

theorem unread (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hu : ∀ k, m < k → ∀ hk : k < C.gates.length, n + m ∉ C.gates[k].inputs)
    (x : List Bool) (hx : x.length = n) (i : ℕ) (hi : i ≠ n + m) :
    PEqualNP.LowMerge.wireVal C x i =
      PEqualNP.LowMerge.wireVal (eraseGate n C m p) x (eraseRedirect n m p i) := by
  simp only [PEqualNP.LowMerge.wireVal, wires_eq]
  rw [split_fold C x m hm]
  simp only [eraseGate, if_pos hm]
  rw [List.foldl_append]
  have hWA : (List.foldl step x (List.take m C.gates)).length = n + m := by
    rw [fold_len, hx, List.length_take]; omega
  apply main_fold2 n m p _ _ _ _ _ _ _ i hi
  · intro g hg
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    simp only [List.getElem_drop]
    exact hu _ (by omega) _
  · simp [step]
  · omega
  · intro j hj
    generalize List.foldl step x (List.take m C.gates) = WA at *
    unfold eraseRedirect
    rw [if_neg hj]
    simp only [step, getD_snoc, hWA]
    by_cases h3 : j < n + m
    · rw [if_pos h3, if_neg (by omega)]
    · rw [if_neg h3, if_neg hj, if_pos (by omega), getD_big _ _ (by omega)]


end PEqualNP.Outside.L_meta_25546_aux.PruneWire

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private theorem erase_dead {N : Nat} {C : Circuit} (sh : shapes C) (back : ReadsBack N C)
    (j : Fin C.gates.length) (unused : read C (N+j.val) = 0)
    (hout : N+j.val ≠ C.output) :
    let D := eraseGate N C j.val N
    shapes D ∧ ReadsBack N D ∧ D.size + 1 = C.size ∧ mixed N D ≤ mixed N C ∧
      ∀ x : List Bool, x.length = N → D.eval x = C.eval x := by
  let D := eraseGate N C j.val N
  let rename (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect N j.val N)⟩
  have hgs : D.gates = C.gates.take j.val ++ (C.gates.drop (j.val+1)).map rename := by
    simp [D,eraseGate,j.isLt,rename]
  have hsz : D.gates.length+1 = C.gates.length := by
    rw [hgs,List.length_append,List.length_take,List.length_map,List.length_drop]
    omega
  have hu (t : Nat) (ht : t < C.gates.length) : N+j.val ∉ (gateAt C t).inputs := by
    intro hit
    have pos := List.count_pos_iff.mpr hit
    have le : (gateAt C t).inputs.count (N+j.val) ≤ read C (N+j.val) :=
      Finset.single_le_sum (f := fun l => (gateAt C l).inputs.count (N+j.val))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
    omega
  refine ⟨?_, ?_, hsz, ?_, ?_⟩
  · intro g hg
    rw [hgs,List.mem_append] at hg
    rcases hg with h | h
    · exact sh _ (List.mem_of_mem_take h)
    · obtain ⟨g₀,h₀,rfl⟩ := List.mem_map.mp h
      simpa [rename] using sh _ (List.mem_of_mem_drop h₀)
  · intro t ht w hw
    change t < D.gates.length at ht
    change w ∈ (gateAt D t).inputs at hw
    have atEq (E : Circuit) (l : Nat) (hl : l < E.gates.length) :
        gateAt E l = E.gates[l] := by simp [gateAt,hl]
    rw [atEq D t ht] at hw
    have takeLen : (C.gates.take j.val).length = j.val := by simp [Nat.le_of_lt j.isLt]
    by_cases h : t < j.val
    · have same : D.gates[t] = C.gates[t]'(by omega) := by
        simp only [hgs,List.getElem_append_left (by omega : t < (C.gates.take j.val).length),
          List.getElem_take]
      rw [same,←atEq] at hw
      exact back t (by omega) w hw
    · have same : D.gates[t] = rename (gateAt C (t+1)) := by
        simp only [hgs,List.getElem_append_right (by omega : (C.gates.take j.val).length ≤ t),
          takeLen,List.getElem_map,List.getElem_drop]
        simp only [show j.val+1+(t-j.val) = t+1 by omega,atEq C (t+1) (by omega)]
      rw [same] at hw
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
      have early := back (t+1) (by omega) v hv
      have different : v ≠ N+j.val := fun e => hu (t+1) (by omega) (e ▸ hv)
      unfold eraseRedirect
      split_ifs <;> omega
  · let isMix (g : Gate) := g.inputs.length == 2 && (g.inputs.filter (fun w => w<N)).length == 1
    have raw (w : Nat) : decide (eraseRedirect N j.val N w < N) = decide (w<N) := by
      have eq : eraseRedirect N j.val N w < N ↔ w<N := by
        unfold eraseRedirect
        split_ifs <;> omega
      simp [eq]
    have countRaw (l : List Nat) :
        ((l.map (eraseRedirect N j.val N)).filter (fun w => w<N)).length =
          (l.filter (fun w => w<N)).length := by
      induction l with
      | nil => rfl
      | cons a l ih =>
        simp only [List.map_cons,List.filter_cons,raw]
        split <;> simp [ih]
    have isSame (g : Gate) : isMix (rename g) = isMix g := by simp [isMix,rename,countRaw]
    have countMix (l : List Gate) : ((l.map rename).filter isMix).length =
        (l.filter isMix).length := by
      induction l with
      | nil => rfl
      | cons g l ih =>
        simp only [List.map_cons,List.filter_cons,isSame]
        split <;> simp [ih]
    change (D.gates.filter isMix).length ≤ (C.gates.filter isMix).length
    rw [hgs,List.filter_append,List.length_append,countMix]
    have splitC : C.gates = C.gates.take j.val ++ C.gates[j.val] :: C.gates.drop (j.val+1) := by simp
    conv_rhs => rw [splitC]
    simp only [List.filter_append,List.length_append,List.filter_cons]
    split <;> simp
  · intro x hx
    have notRead (t : Nat) (_ : j.val < t) (ht : t < C.gates.length) :
        N+j.val ∉ C.gates[t].inputs := by simpa [gateAt,ht] using hu t ht
    have eq := PruneWire.unread N C j.val N j.isLt notRead x hx C.output (Ne.symm hout)
    have outIndex : D.output = eraseRedirect N j.val N C.output := by simp [D,eraseGate,j.isLt]
    change (D.wires x).getD D.output false = (C.wires x).getD C.output false
    rw [outIndex]
    exact eq.symm

theorem prune46 {r c : Nat} {G : Fin r → Fin c → Bool} (C : Circuit) (sh : shapes C)
    (back : ReadsBack (r+c) C) (rep : Represents G C) :
    ∃ D, shapes D ∧ ReadsBack (r+c) D ∧ Represents G D ∧ live (r+c) D ∧
      D.size ≤ C.size ∧ mixed (r+c) D ≤ mixed (r+c) C := by
  classical
  let good (s : Nat) := ∃ D : Circuit, shapes D ∧ ReadsBack (r+c) D ∧ Represents G D ∧
    mixed (r+c) D ≤ mixed (r+c) C ∧ D.size=s
  have witness : ∃ s, good s := ⟨C.size,C,sh,back,rep,le_rfl,rfl⟩
  obtain ⟨D,ds,db,dr,dm,sz⟩ := Nat.find_spec witness
  refine ⟨D,ds,db,dr,?_,?_,dm⟩
  · intro j hj
    by_contra! dead
    have hz : read D (r+c+j.val)=0 := by omega
    obtain ⟨es,eb,esz,em,ee⟩ := erase_dead ds db j hz hj
    let E := eraseGate (r+c) D j.val (r+c)
    have er : Represents G E := by
      intro u v
      exact (ee (oneEach u v) (by simp [oneEach])).trans (dr u v)
    have minimal := Nat.find_min' witness
      (show good E.size from ⟨E,es,eb,er,em.trans dm,rfl⟩)
    change E.size+1=D.size at esz
    omega
  · rw [sz]
    exact Nat.find_min' witness (show good C.size from ⟨C,sh,back,rep,le_rfl,rfl⟩)
end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds
lemma zeroCount46 {r c : Nat} {C : Circuit}
    (row : ∀ u v : Fin r, use C u.val=0 → use C v.val=0 → u=v)
    (col : ∀ u v : Fin c, use C (r+u.val)=0 → use C (r+v.val)=0 → u=v) :
    ((Finset.range (r+c)).filter (fun w => use C w=0)).card ≤ 2 := by
  let s := (Finset.range (r+c)).filter (fun w => use C w=0)
  let low := s.filter (fun w => w<r)
  let high := s.filter (fun w => r≤w)
  have L : low.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨as,an⟩ := Finset.mem_filter.mp ha
    obtain ⟨bs,bn⟩ := Finset.mem_filter.mp hb
    exact congrArg Fin.val (row ⟨a,an⟩ ⟨b,bn⟩ (Finset.mem_filter.mp as).2 (Finset.mem_filter.mp bs).2)
  have H : high.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨as,an⟩ := Finset.mem_filter.mp ha
    obtain ⟨bs,bn⟩ := Finset.mem_filter.mp hb
    obtain ⟨ar,az⟩ := Finset.mem_filter.mp as
    obtain ⟨br,bz⟩ := Finset.mem_filter.mp bs
    have al := Finset.mem_range.mp ar
    have bl := Finset.mem_range.mp br
    have ea : r+(a-r)=a := by omega
    have eb : r+(b-r)=b := by omega
    have e := col ⟨a-r,by omega⟩ ⟨b-r,by omega⟩ (by simpa only [ea] using az) (by simpa only [eb] using bz)
    have h : a-r=b-r := congrArg Fin.val e
    omega
  have sub : s ⊆ low ∪ high := by
    intro a ha
    by_cases hl : a<r
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha,hl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha,by omega⟩)
  have x := Finset.card_le_card sub
  have y := Finset.card_union_le low high
  change s.card ≤ 2
  omega

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
private theorem sum_get511 {α : Type} (f : α → Nat) (z : α) (l : List α) :
    (∑ j ∈ Finset.range l.length, f (l.getD j z)) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons,Finset.sum_range_succ']
    simp only [List.getD_cons_succ,List.getD_cons_zero,List.map_cons,List.sum_cons]
    omega

private theorem sum_arity511 (gs : List Gate) (shape : ∀g ∈ gs, g.inputs.length=2 ∨ g.inputs.length=1) :
    (gs.map (fun g => g.inputs.length)).sum + (gs.filter (fun g => g.inputs.length==1)).length =
      2*gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have tail := ih (fun x hx => shape x (by simp [hx]))
    rcases shape g (by simp) with h|h <;>
      simp [h] <;> omega

private theorem input_arities511 {N : Nat} {C : Circuit} (sh : shapes C) (back : ReadsBack N C) :
    (∑ w ∈ Finset.range (N+C.size),read C w) + unary C = 2*C.size := by
  classical
  have occ (j : Nat) (hj : j∈Finset.range C.size) :
      (∑ w ∈ Finset.range (N+C.size), (gateAt C j).inputs.count w) = (gateAt C j).inputs.length := by
    have sub : (gateAt C j).inputs.toFinset ⊆ Finset.range (N+C.size) := by
      intro w hw
      have jlt : j<C.size := Finset.mem_range.mp hj
      have bound := back j jlt w (List.mem_toFinset.mp hw)
      exact Finset.mem_range.mpr (by omega)
    calc
      _ = ∑ w ∈ (gateAt C j).inputs.toFinset, (gateAt C j).inputs.count w :=
        (Finset.sum_subset sub (fun w _ h => List.count_eq_zero.mpr (fun m => h (List.mem_toFinset.mpr m)))).symm
      _ = _ := List.sum_toFinset_count_eq_length _
  unfold read readsIn
  rw [Finset.sum_comm,Finset.sum_congr rfl occ]
  change (∑ j ∈ Finset.range C.gates.length, (C.gates.getD j ⟨.or,[]⟩).inputs.length) + _ = _
  rw [sum_get511 (fun g : Gate => g.inputs.length)]
  exact sum_arity511 _ (fun g hg => (sh g hg).imp And.right And.right)

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_natAdd]
    omega

private lemma foldIgnores {p q : Nat} (gs : List Gate)
    (avoid : ∀g∈gs, ∀i∈g.inputs,i≠p ∧ i≠q) (x y : List Bool) (hl : x.length=y.length)
    (ag : ∀i,i≠p → i≠q → x.getD i false=y.getD i false) :
    ∀i,i≠p → i≠q →
      (gs.foldl PruneWire.step x).getD i false=(gs.foldl PruneWire.step y).getD i false := by
  induction gs generalizing x y with
  | nil => exact ag
  | cons g gs ih =>
    apply ih (fun z hz=>avoid z (by simp [hz]))
    · simp [PruneWire.step,hl]
    · intro i hp hq
      have eq : g.inputs.map (fun j=>x.getD j false)=g.inputs.map (fun j=>y.getD j false) :=
        List.map_congr_left (fun j hj=>ag j (avoid g (by simp) j hj).1 (avoid g (by simp) j hj).2)
      simp only [PruneWire.step,PruneWire.getD_snoc,hl,eq,ag i hp hq]

private lemma avoids {C : Circuit} {w : Nat} (h : use C w=0) :
    C.output≠w ∧ ∀g∈C.gates,w∉g.inputs := by
  have hr : read C w=0 := by unfold use at h;omega
  constructor
  · intro eq; simp [use,eq] at h
  · intro g hg hit
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    have m : w∈(gateAt C j).inputs := by simpa [gateAt,hj] using hit
    have d := List.count_pos_iff.mpr m
    have le : (gateAt C j).inputs.count w ≤ read C w :=
      Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w)) (Finset.mem_range.mpr hj)
    omega

private lemma swap46 {r c p q : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (rep:Represents G C) (hp:use C p=0) (hq:use C q=0) (u v:Fin r) (j l:Fin c)
    (same : ∀i:Fin (r+c), i.val≠p → i.val≠q →
      pt r c u.val (r+j.val) i = pt r c v.val (r+l.val) i) :
    G u j = G v l := by
  obtain ⟨op,ap⟩:=avoids hp
  obtain ⟨oq,aq⟩:=avoids hq
  rw [←rep u j,←rep v l,oneEach_pt,oneEach_pt]
  apply foldIgnores C.gates (p:=p) (q:=q) (fun g hg i hi=>⟨fun e=>ap g hg (e ▸ hi),fun e=>aq g hg (e ▸ hi)⟩)
    _ _ (by simp) _ C.output op oq
  intro i ip iq
  by_cases hi:i<r+c
  · simpa [List.getD_eq_getElem?_getD,hi] using same ⟨i,hi⟩ ip iq
  · simp [List.getD_eq_getElem?_getD,hi]

theorem noUse46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (ri:Function.Injective G) (ci:Function.Injective (fun v u=>G u v)) (rep:Represents G C) :
    ((Finset.range (r+c)).filter (fun w=>use C w=0)).card≤2 := by
  apply zeroCount46
  · intro u v hu hv
    apply ri;funext j
    apply swap46 rep hu hv u v j j
    intro i x y;simp [pt,x,y]
  · intro j l hj hl
    apply ci;funext u
    apply swap46 rep hj hl u u j l
    intro i x y;simp [pt,x,y]

theorem ledger46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (ri:Function.Injective G) (ci:Function.Injective (fun v u=>G u v)) (sh:shapes C)
    (back:ReadsBack (r+c) C) (rep:Represents G C) (hl:live (r+c) C) :
    r+c+E (r+c) C+unary C ≤ C.size+3 := by
  classical
  let N:=r+c
  let S:=Finset.range (N+C.size)
  have ar:=input_arities511 sh back
  have zr := noUse46 ri ci rep
  have zsub : (S.filter (fun w=>use C w=0)) ⊆ (Finset.range N).filter (fun w=>use C w=0) := by
    intro w hw
    obtain ⟨hm,hz⟩:=Finset.mem_filter.mp hw
    apply Finset.mem_filter.mpr;refine ⟨Finset.mem_range.mpr ?_,hz⟩
    by_contra! h
    have bound : w<N+C.size:=Finset.mem_range.mp hm
    have wj : N+(w-N)=w := by omega
    have out : w≠C.output := fun e => (avoids hz).1 e.symm
    have livew:=hl ⟨w-N,by change w-N<C.size;omega⟩ (by dsimp;change N+(w-N)≠C.output;rwa [wj])
    change 0<read C (N+(w-N)) at livew
    rw [wj] at livew
    unfold use at hz
    omega
  have zeros : (S.filter (fun w=>use C w=0)).card≤2 :=
    (Finset.card_le_card zsub).trans zr
  have book : N+C.size+E N C = (∑w∈S,use C w)+(S.filter (fun w=>use C w=0)).card := by
    calc
      _ = ∑ w∈S, (1+(use C w-1)) := by simp [S,E,Finset.sum_add_distrib]
      _ = ∑ w∈S, (use C w + if use C w=0 then 1 else 0) := by
        apply Finset.sum_congr rfl;intro w _;split_ifs <;> omega
      _ = _ := by rw [Finset.sum_add_distrib,Finset.card_filter]
  have usele : (∑w∈S,use C w) ≤ (∑w∈S,read C w)+1 := by
    simp only [use,Finset.sum_add_distrib]
    simp [eq_comm]; split <;> omega
  change (∑w∈S,read C w)+unary C=2*C.size at ar
  change N+E N C+unary C≤C.size+3
  omega

theorem noRowUse46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (ri:Function.Injective G) (rep:Represents G C) {u v : Fin r} (hu:use C u.val=0) (hv:use C v.val=0) : u=v := by
  apply ri;funext j
  apply swap46 rep hu hv u v j j
  intro i x y;simp [pt,x,y]

end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def port (C : Circuit) {r : Nat} (u : Fin r) (j : Fin C.size) : Prop :=
  use C u.val = 1 ∧ u.val ∈ (gateAt C j.val).inputs ∧
    ((gateAt C j.val).op = .and ∨ (gateAt C j.val).op = .or)

def links (N : Nat) (C : Circuit) (j k : Fin C.size) : Prop :=
  use C (N+j.val)=1 ∧ N+j.val ∈ (gateAt C k.val).inputs

noncomputable def good (r : Nat) (C : Circuit) : Finset (Fin C.size) := by
  classical exact Finset.univ.filter (fun j => ∃ u : Fin r, port C u j)

noncomputable def starts (r c : Nat) (C : Circuit) : Finset (Fin C.size) := by
  classical exact (good r C).filter (fun k => ¬ ∃ j ∈ good r C, links (r+c) C j k)

noncomputable def deep (r c : Nat) (C : Circuit) : Finset (Fin C.size) := by
  classical exact (good r C).filter (fun i => ∃ j ∈ good r C, ∃ k ∈ good r C,
    links (r+c) C i j ∧ links (r+c) C j k)

end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux.Wire


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_W (C : Circuit) (x : List Bool) : C.wires x = W C.gates x := rfl

theorem eval_W (C : Circuit) (x : List Bool) : C.eval x = (W C.gates x).getD C.output false := rfl

theorem circuitFun_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = (W C.gates (List.ofFn x)).getD C.output false := rfl

theorem W_nil (w : List Bool) : W [] w = w := rfl

theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

theorem W_single (g : Gate) (w : List Bool) : W [g] w = step w g := rfl

theorem W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

theorem W_snoc (gs : List Gate) (g : Gate) (w : List Bool) : W (gs ++ [g]) w = step (W gs w) g := by
  rw [W_append]; rfl

theorem W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

theorem W_snoc_getD (gs : List Gate) (g : Gate) (w : List Bool) (t : ℕ) :
    (W (gs ++ [g]) w).getD t false =
      if t = w.length + gs.length then g.op.eval (g.inputs.map fun i => (W gs w).getD i false)
      else (W gs w).getD t false := by
  rw [W_snoc]
  by_cases ht : t = w.length + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_length]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < w.length + gs.length
    · exact step_lt _ _ _ (by rw [W_length]; exact hlt)
    · rw [getD_ge _ _ (by rw [step_len, W_length]; omega), getD_ge _ _ (by rw [W_length]; omega)]

theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

theorem W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    (List.ofFn x).getD u false = x ⟨u, hu⟩ := by
  simp [List.getD_eq_getElem?_getD, hu]

theorem ofFn_getD_ge {n : ℕ} (x : Fin n → Bool) (u : ℕ) (hu : n ≤ u) :
    (List.ofFn x).getD u false = false := getD_ge _ _ (by simpa using hu)

theorem split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate), gs = pre ++ gs[j] :: post ∧ pre.length = j := by
  refine ⟨gs.take j, gs.drop (j + 1), ?_, by simp; omega⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

theorem split2 (gs : List Gate) : ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    ∃ pre post, pre.length = j ∧ gs = pre ++ g :: post ∧ ∀ g2, gs.set j g2 = pre ++ g2 :: post := by
  induction gs with
  | nil => intro j g h; simp at h
  | cons a gs ih =>
    intro j g h
    cases j with
    | zero =>
      have ha : a = g := by simpa using h
      subst ha
      exact ⟨[], gs, rfl, rfl, fun g2 => rfl⟩
    | succ j =>
      have h2 : gs[j]? = some g := by simpa using h
      obtain ⟨pre, post, hl, e1, e2⟩ := ih j g h2
      refine ⟨a :: pre, post, by rw [List.length_cons, hl], ?_, fun g2 => ?_⟩
      · exact congrArg (List.cons a) e1
      · exact congrArg (List.cons a) (e2 g2)

theorem step_congr (P : List Bool) (g1 g2 : Gate)
    (h : g1.op.eval (g1.inputs.map fun i => P.getD i false)
      = g2.op.eval (g2.inputs.map fun i => P.getD i false)) :
    step P g1 = step P g2 := by
  show P ++ [_] = P ++ [_]
  rw [h]

theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

theorem gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

theorem gateAt_ge {C : Circuit} {j : ℕ} (hj : C.gates.length ≤ j) :
    gateAt C j = ⟨GateOp.or, []⟩ := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none hj]

theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem eval_and_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.and.eval (l.map f) = true ↔ ∀ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_or_iff (l : List ℕ) (f : ℕ → Bool) :
    GateOp.or.eval (l.map f) = true ↔ ∃ i ∈ l, f i = true := by
  simp [GateOp.eval]

theorem eval_and2 (a b : Bool) : GateOp.and.eval [a, b] = (a && b) := by
  cases a <;> cases b <;> rfl

theorem eval_or2 (a b : Bool) : GateOp.or.eval [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem eval_and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl

theorem eval_or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

theorem circuitFun_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    circuitFun n C x = val C (List.ofFn x) C.output := rfl

theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]

theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩

def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)

theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega

theorem oe_getD (n m : ℕ) (u : Fin n) (v : Fin m) (k : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD k false = true ↔ (k = u.val ∨ k = n + v.val) := by
  rw [oneEach_pt]
  have hu := u.isLt
  have hv := v.isLt
  by_cases hk : k < n + m
  · rw [ofFn_getD _ k hk]
    simp [pt]
  · rw [ofFn_getD_ge _ k (by omega)]
    simp only [Bool.false_eq_true, false_iff]
    omega

theorem oe_len (n m : ℕ) (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  rw [oneEach_pt, List.length_ofFn]

theorem uniq (C : Circuit) (w j0 j : ℕ) (hj0 : j0 < C.gates.length) (hj : j < C.gates.length)
    (h1 : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1)
    (hw0 : w ∈ (gateAt C j0).inputs) (hw : w ∈ (gateAt C j).inputs) : j = j0 := by
  by_contra hne
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h1
  have hs := Finset.add_le_sum (f := fun k => (gateAt C k).inputs.count w) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (show j0 < C.size from hj0)) (Finset.mem_range.2 (show j < C.size from hj)) (Ne.symm hne)
  have c0 := List.count_pos_iff.2 hw0
  have c1 := List.count_pos_iff.2 hw
  omega


end PEqualNP.Outside.L_meta_25546_aux.Wire

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Wire

theorem atOnly46 {C : Circuit} {w : Nat} {j : Fin C.size} (one : use C w=1)
    (hit : w∈(gateAt C j.val).inputs) :
    C.output≠w ∧ ∀ k : Fin C.size, w∈(gateAt C k.val).inputs → k=j := by
  have cnt := List.count_pos_iff.mpr hit
  have hle : (gateAt C j).inputs.count w ≤ read C w :=
    Finset.single_le_sum (fun i _ => Nat.zero_le ((gateAt C i).inputs.count w))
      (Finset.mem_range.mpr j.isLt)
  have no : C.output≠w := by
    intro e
    simp [use,e] at one
    omega
  have eq : read C w=1 := by simpa [use,no] using one
  exact ⟨no,fun k hk => Fin.ext (Wire.uniq C w j k j.isLt k.isLt eq hit hk)⟩

private def input46 (r c u : Nat) (v : Fin c) := List.ofFn (Wire.pt r c u (r+v.val))
def bit46 (r c : Nat) (C : Circuit) (u : Nat) (v : Fin c) := Wire.val C (input46 r c u v)
def profile46 (r c : Nat) (C : Circuit) (u : Nat) : Fin c → Bool :=
  fun v => bit46 r c C u v C.output

theorem raw46 {r c x : Nat} {C : Circuit} (u : Nat) (v : Fin c) (hx : x<r) :
    bit46 r c C u v x = decide (x=u) := by
  rw [bit46,input46,Wire.val_ofFn_lt _ _ _ (by omega)]
  simp [Wire.pt,show x≠r+v.val by omega]

theorem profile_rep46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (rep : Represents G C) (u : Fin r) : profile46 r c C u.val = G u := by
  funext v
  rw [←rep u v,Wire.oneEach_pt]
  rfl

theorem compare46 {r c : Nat} {C : Circuit} (back : ReadsBack (r+c) C)
    (a b : Nat) (v : Fin c) (bad : Finset Nat)
    (init : ∀ z<r+c, z∉bad → (z=a ↔ z=b))
    (stop : ∀ j : Fin C.size, r+c+j.val∉bad →
      ∀ z ∈ (gateAt C j.val).inputs, z ∈ bad →
        bit46 r c C a v (r+c+j.val) = bit46 r c C b v (r+c+j.val)) :
    ∀ w ∉ bad, bit46 r c C a v w = bit46 r c C b v w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro nw
    by_cases inp : w<r+c
    · simp only [bit46,input46,Wire.val_ofFn_lt _ _ _ inp,Wire.pt,init w inp nw]
    by_cases bound : r+c+C.gates.length≤w
    · exact (Wire.val_ge (x:=input46 r c a v) (n:=r+c) (by simp [input46]) bound).trans
        (Wire.val_ge (x:=input46 r c b v) (n:=r+c) (by simp [input46]) bound).symm
    let j : Fin C.size := ⟨w-(r+c),by change w-(r+c)<C.gates.length;omega⟩
    have hji : r+c+j.val=w := by dsimp [j];omega
    rw [←hji] at nw ⊢
    by_cases hit : ∃z∈(gateAt C j.val).inputs,z∈bad
    · obtain ⟨z,hz,hb⟩:=hit
      exact stop j nw z hz hb
    · unfold bit46
      rw [Wire.val_gate_rb (x:=input46 r c a v) (n:=r+c) (by simp [input46]) j.isLt (back _ j.isLt),
        Wire.val_gate_rb (x:=input46 r c b v) (n:=r+c) (by simp [input46]) j.isLt (back _ j.isLt)]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i (hji ▸ back _ j.isLt _ hi) (fun hb => hit ⟨i,hi,hb⟩)

theorem forced46 {r c : Nat} {C : Circuit} (back : ReadsBack (r+c) C)
    {j : Fin C.size} {w : Nat} {a : Nat} {v : Fin c} {d : Bool}
    (op : (gateAt C j).op = if d then .or else .and)
    (hw : w∈(gateAt C j).inputs) (hv : bit46 r c C a v w=d) :
    bit46 r c C a v (r+c+j.val)=d := by
  simp only [bit46] at hv ⊢
  rw [Wire.val_gate_rb (n:=r+c) (by simp [input46]) j.isLt (back _ j.isLt),op]
  cases d
  · simp only [Bool.false_eq_true,↓reduceIte,GateOp.eval,List.all_map,List.all_eq_false,
      Function.comp_apply,id_eq,Bool.not_eq_true]
    exact ⟨w,hw,hv⟩
  · simp only [↓reduceIte,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
    exact ⟨w,hw,hv⟩

theorem port_unique46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (ri : Function.Injective G) (back : ReadsBack (r+c) C) (rep : Represents G C)
    {u v : Fin r} {j : Fin C.size} (pu : port C u j) (pv : port C v j) : u=v := by
  by_contra ne
  have neq : u.val≠v.val := fun h=>ne (Fin.ext h)
  obtain ⟨outU,toU⟩ := atOnly46 pu.1 pu.2.1
  obtain ⟨outV,toV⟩ := atOnly46 pv.1 pv.2.1
  apply ne
  apply ri
  rw [←profile_rep46 rep u,←profile_rep46 rep v]
  funext col
  apply compare46 back u.val v.val col {u.val,v.val} _ _ C.output (by simp [outU,outV])
  · intro z hz h
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at h
    simp [h.1,h.2]
  · intro k nk z hz hbad
    have eq : k=j := by
      rcases Finset.mem_insert.mp hbad with rfl | h
      · exact toU k hz
      · obtain rfl := Finset.mem_singleton.mp h;exact toV k hz
    subst k
    rcases pu.2.2 with op | op
    · exact (forced46 back (d:=false) op pv.2.1 (by rw [raw46 _ _ v.isLt];simp [Ne.symm neq])).trans
        (forced46 back (d:=false) op pu.2.1 (by rw [raw46 _ _ u.isLt];simp [neq])).symm
    · exact (forced46 back (d:=true) op pu.2.1 (by rw [raw46 _ _ u.isLt];simp)).trans
        (forced46 back (d:=true) op pv.2.1 (by rw [raw46 _ _ v.isLt];simp)).symm

end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

private theorem triple46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (ri : Function.Injective G) (back : ReadsBack (r+c) C) (rep : Represents G C)
    {u v w : Fin r} {i j k : Fin C.size} (A : port C u i) (B : port C v j) (D : port C w k)
    (ab : links (r+c) C i j) (bc : links (r+c) C j k) :
    profile46 r c C u = profile46 r c C (r+c) := by
  let N := r+c
  obtain ⟨ou,tu⟩ := atOnly46 A.1 A.2.1
  obtain ⟨ov,tv⟩ := atOnly46 B.1 B.2.1
  obtain ⟨ow,tw⟩ := atOnly46 D.1 D.2.1
  obtain ⟨oi,ti⟩ := atOnly46 ab.1 ab.2
  obtain ⟨oj,tj⟩ := atOnly46 bc.1 bc.2
  have ij : i.val<j.val := by have h:=back j.val j.isLt _ ab.2;omega
  have jk : j.val<k.val := by have h:=back k.val k.isLt _ bc.2;omega
  have uv : u.val≠v.val := by
    intro e;have q:=tu j (e ▸ B.2.1);have:=congrArg Fin.val q;omega
  have uw : u.val≠w.val := by
    intro e;have q:=tu k (e ▸ D.2.1);have:=congrArg Fin.val q;omega
  have vw : v.val≠w.val := by
    intro e;have q:=tv k (e ▸ D.2.1);have:=congrArg Fin.val q;omega
  have vbase : v.val≠r+c := by omega
  have wbase : w.val≠r+c := by omega
  by_cases bAnd : (gateAt C j.val).op=.and
  · funext col
    apply compare46 back u.val (r+c) col {u.val,r+c+i.val} _ _ C.output (by simp [ou,oi])
    · intro z hz ok
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ok
      simp [ok.1,ne_of_lt hz]
    · intro t ht z hz hb
      rcases Finset.mem_insert.mp hb with hu | hz'
      · subst z
        obtain rfl := tu t hz
        simp at ht
      · obtain rfl := Finset.mem_singleton.mp hz'
        obtain rfl := ti t hz
        apply (forced46 back (d:=false) bAnd B.2.1 _).trans
          (forced46 back (d:=false) bAnd B.2.1 _).symm
        · rw [raw46 _ _ v.isLt];simp [Ne.symm uv]
        · rw [raw46 _ _ v.isLt];simp [vbase]
  by_cases dAnd : (gateAt C k.val).op=.and
  · funext col
    apply compare46 back u.val (r+c) col {u.val,r+c+i.val,r+c+j.val} _ _ C.output
      (by simp [ou,oi,oj])
    · intro z hz ok
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ok
      simp [ok.1,ne_of_lt hz]
    · intro t ht z hz hb
      rcases Finset.mem_insert.mp hb with hu | hb
      · subst z;obtain rfl:=tu t hz;simp at ht
      rcases Finset.mem_insert.mp hb with hu | hb
      · subst z;obtain rfl:=ti t hz;simp at ht
      obtain rfl := Finset.mem_singleton.mp hb
      obtain rfl := tj t hz
      apply (forced46 back (d:=false) dAnd D.2.1 _).trans
        (forced46 back (d:=false) dAnd D.2.1 _).symm
      · rw [raw46 _ _ w.isLt];simp [Ne.symm uw]
      · rw [raw46 _ _ w.isLt];simp [wbase]
  · have bOr := B.2.2.resolve_left bAnd
    have dOr := D.2.2.resolve_left dAnd
    exfalso
    apply vw
    apply congrArg Fin.val
    apply ri
    rw [←profile_rep46 rep v,←profile_rep46 rep w]
    funext col
    apply compare46 back v.val w.val col {v.val,w.val,r+c+j.val} _ _ C.output (by simp [ov,ow,oj])
    · intro z hz ok
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at ok
      simp [ok.1, ok.2.1]
    · intro t ht z hz hb
      have tk : t=k := by
        rcases Finset.mem_insert.mp hb with h | hb
        · subst z; obtain rfl:=tv t hz;simp at ht
        rcases Finset.mem_insert.mp hb with h | hb
        · subst z;exact tw t hz
        obtain rfl := Finset.mem_singleton.mp hb
        exact tj t hz
      subst t
      have bj : bit46 r c C v.val col (r+c+j.val)=true :=
        forced46 back (d:=true) bOr B.2.1 (by rw [raw46 _ _ v.isLt];simp)
      exact (forced46 back (d:=true) dOr bc.2 bj).trans
        (forced46 back (d:=true) dOr D.2.1 (by rw [raw46 _ _ w.isLt];simp)).symm

theorem deepCard46 {r c : Nat} {G : Fin r → Fin c → Bool} {C : Circuit}
    (ri : Function.Injective G) (back : ReadsBack (r+c) C) (rep : Represents G C) :
    (deep r c C).card≤1 := by
  classical
  have rowOf (i : Fin C.size) (hi : i∈deep r c C) : ∃u : Fin r, port C u i ∧
      profile46 r c C u = profile46 r c C (r+c) := by
    obtain ⟨gi,j,gj,k,gk,l1,l2⟩ := Finset.mem_filter.mp hi
    obtain ⟨u,hu⟩ := (Finset.mem_filter.mp gi).2
    obtain ⟨v,hv⟩ := (Finset.mem_filter.mp gj).2
    obtain ⟨w,hw⟩ := (Finset.mem_filter.mp gk).2
    exact ⟨u,hu,triple46 ri back rep hu hv hw l1 l2⟩
  apply Finset.card_le_one.mpr
  intro i hi j hj
  obtain ⟨u,hu,pu⟩:=rowOf i hi
  obtain ⟨v,hv,pv⟩:=rowOf j hj
  have eq : G u = G v := by rw [←profile_rep46 rep u,pu,←pv,profile_rep46 rep v]
  obtain rfl:=ri eq
  exact ((atOnly46 hu.1 hu.2.1).2 j hv.2.1).symm

end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
private noncomputable def cheap (r c : Nat) (C:Circuit) : Finset Nat := by
  classical
  exact ((Finset.range c).image (fun j=>r+j)) ∪
    ((Finset.univ \ good r C).image (fun j:Fin C.size=>r+c+j.val))
private lemma cheapCard (r c:Nat) (C:Circuit) : (cheap r c C).card ≤ c+(C.size-(good r C).card) := by
  classical
  have h:=Finset.card_union_le ((Finset.range c).image (fun j=>r+j))
    ((Finset.univ \ good r C).image (fun j:Fin C.size=>r+c+j.val))
  apply h.trans
  apply Nat.add_le_add
  · exact (Finset.card_image_le).trans (by simp)
  · exact (Finset.card_image_le).trans (by simp [Finset.card_sdiff_of_subset (Finset.subset_univ _)])
private lemma oneRead {C:Circuit} {j w:Nat} (hj:j<C.size) :
    (gateAt C j).inputs.count w ≤ read C w :=
  Finset.single_le_sum (fun t _=>Nat.zero_le ((gateAt C t).inputs.count w)) (Finset.mem_range.mpr hj)
private lemma startOperand {r c : Nat} {C:Circuit} (sh:shapes C) (back:ReadsBack (r+c) C)
    (uniq:∀ {u v:Fin r} {j:Fin C.size},port C u j → port C v j → u=v)
    {j:Fin C.size} (hj:j∈starts r c C) :
    ∃ w∈(gateAt C j.val).inputs, use C w≠1 ∨ w∈cheap r c C := by
  classical
  obtain ⟨gj,nop⟩ := (Finset.mem_filter.mp hj :
    j∈good r C ∧ ¬ ∃ k∈good r C,links (r+c) C k j)
  obtain ⟨u,pu⟩ := (Finset.mem_filter.mp gj).2
  obtain ⟨us,hu,op⟩ := pu
  have boundj : j.val<C.gates.length := j.isLt
  have hg : gateAt C j.val ∈ C.gates := by simp [gateAt,boundj]
  have two : (gateAt C j.val).inputs.length=2 := by
    rcases sh _ hg with h|h
    · exact h.2
    · rcases op with o|o <;> simp [o] at h
  obtain ⟨b,d,bd⟩:=List.length_eq_two.mp two
  have hread:=oneRead (C:=C) (w:=u.val) j.isLt
  have ru : read C u.val≤1 := by unfold use at us;omega
  obtain ⟨w,hw,ne⟩ : ∃w∈(gateAt C j.val).inputs, w≠u.val := by
    rw [bd] at hu hread ⊢
    by_contra! h
    have bb:=h b (by simp)
    have dd:=h d (by simp)
    simp [bb,dd] at hread;omega
  refine ⟨w,hw,?_⟩
  by_cases hone : use C w=1
  · right
    by_cases raw : w<r
    · let v:Fin r:=⟨w,raw⟩
      have eq:=uniq (u:=v) (v:=u) ⟨hone,hw,op⟩ ⟨us,hu,op⟩
      exact (ne (congrArg Fin.val eq)).elim
    · by_cases column : w<r+c
      · apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨w-r,Finset.mem_range.mpr (by omega),by omega⟩
      · let k : Fin C.size := ⟨w-(r+c),by have z:=back j.val j.isLt w hw;have:=j.isLt;omega⟩
        have e : r+c+k.val=w := by dsimp [k];omega
        have ng:k∉good r C := fun h=>nop ⟨k,h,by change use C (r+c+k.val)=1 ∧ _;rw [e];exact ⟨hone,hw⟩⟩
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨k,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ng⟩,e⟩
  · exact Or.inl hone

theorem countStarts46 {r c : Nat} {C:Circuit} (sh:shapes C) (back:ReadsBack (r+c) C)
    (uniq:∀ {u v:Fin r} {j:Fin C.size},port C u j → port C v j → u=v) :
    (starts r c C).card ≤ c+(C.size-(good r C).card)+2*E (r+c) C := by
  classical
  let N:=r+c
  let W:=Finset.range (N+C.size)
  let J:=(starts r c C).image (fun j=>j.val)
  let A:=cheap r c C
  let term := fun (i w:Nat) => if use C w≠1 ∨ w∈A then (gateAt C i).inputs.count w else 0
  have js : J ⊆ Finset.range C.size := by
    intro i hi;obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi;exact Finset.mem_range.mpr j.isLt
  have pays (i:Nat) (hi:i∈J) : 1 ≤ ∑w∈W,term i w := by
    obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
    obtain ⟨w,hw,hq⟩:=startOperand sh back uniq hj
    have hl:=back j.val j.isLt w hw
    have mem : w∈W:=Finset.mem_range.mpr (by dsimp [N];have:=j.isLt;omega)
    have one:=Finset.single_le_sum (f:=term j.val) (fun _ _=>Nat.zero_le _) mem
    have hpos:=List.count_pos_iff.mpr hw
    change use C w≠1 ∨ w∈A at hq
    apply le_trans (b:=term j.val w) _ one
    simp only [term,ite_eq_left hq]
    omega
  have cap (w:Nat) : (∑i∈J,term i w) ≤ (if w∈A then 1 else 0)+2*(use C w-1) := by
    by_cases rele:use C w≠1 ∨ w∈A
    · simp only [term,ite_eq_left rele]
      have le : (∑ i∈J,(gateAt C i).inputs.count w) ≤ read C w :=
        Finset.sum_le_sum_of_subset_of_nonneg js (fun _ _ _ => Nat.zero_le _)
      have le' : read C w≤use C w := by unfold use;omega
      by_cases h:w∈A
      · simp only [ite_eq_left h];omega
      · have hn : use C w≠1:=rele.resolve_right h
        simp only [ite_eq_right h];omega
    · simp [term,rele]
  have h := Finset.sum_le_sum pays
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at h
  rw [Finset.sum_comm] at h
  have bound:=h.trans (Finset.sum_le_sum (fun w (_:w∈W)=>cap w))
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at bound
  have cA : (∑w∈W,if w∈A then 1 else 0)≤A.card := by
    rw [←Finset.card_filter];exact Finset.card_le_card (fun w hw=>(Finset.mem_filter.mp hw).2)
  have exactJ:J.card=(starts r c C).card := Finset.card_image_of_injective _ Fin.val_injective
  change (starts r c C).card ≤ c+(C.size-(good r C).card)+2*(∑w∈W,(use C w-1))
  have sizeA := cheapCard r c C
  change A.card≤_ at sizeA
  omega
end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
private noncomputable def singles (C:Circuit) :=
  Finset.univ.filter (fun j:Fin C.size=>(gateAt C j.val).inputs.length=1)

private lemma singleCard (C:Circuit) : (singles C).card=unary C := by
  classical
  let P := fun g:Gate => g.inputs.length==1
  have cnt (l : List Gate) : (∑ j∈Finset.range l.length, if (l.getD j ⟨.or,[]⟩).inputs.length=1 then 1 else 0)
        = (l.filter P).length := by
    induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.length_cons,Finset.sum_range_succ']
      simp only [List.getD_cons_succ,List.getD_cons_zero,List.filter_cons]
      rw [ih]
      by_cases h:x.inputs.length=1 <;> simp [h,P]
  have e:=cnt C.gates
  rw [←Fin.sum_univ_eq_sum_range] at e
  unfold singles
  rw [Finset.card_filter]
  exact e

lemma countRows46 {r c : Nat} {C:Circuit} {G:Fin r→Fin c→Bool}
    (ri:Function.Injective G) (sh:shapes C) (rep:Represents G C)
    (uniq:∀ {u v:Fin r} {j:Fin C.size},port C u j → port C v j → u=v) :
    r ≤ (good r C).card + E (r+c) C + unary C + 2 := by
  classical
  let R:=Finset.univ (α:=Fin r)
  let bad:=R.filter (fun u=>use C u.val=0)
  let many:=R.filter (fun u=>1<use C u.val)
  let out:=R.filter (fun u=>C.output=u.val)
  let rem:=R.filter (fun u=>use C u.val=1 ∧ C.output≠u.val)
  have hb:bad.card≤1 := Finset.card_le_one.mpr (fun u hu v hv=>noRowUse46 ri rep (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2)
  have ho:out.card≤1 := Finset.card_le_one.mpr (fun u hu v hv=>Fin.ext ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2))
  have hm:many.card≤E (r+c) C := by
    let I:=many.image Fin.val
    have eq:I.card=many.card := Finset.card_image_of_injective _ Fin.val_injective
    have part:I ⊆ Finset.range (r+c+C.size) := by
      intro z hz; obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz;apply Finset.mem_range.mpr;have:=u.isLt;omega
    calc
      _ = ∑ _w∈I, 1 := by simp [eq]
      _ ≤ ∑ w∈I, (use C w-1) := by
        apply Finset.sum_le_sum
        intro w hw;obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
        have hz:1<use C u.val := (Finset.mem_filter.mp hu).2
        omega
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg part (fun _ _ _=>Nat.zero_le _)
  have hit (u:Fin r) (hm:u∈rem):∃j:Fin C.size,u.val∈(gateAt C j.val).inputs := by
    obtain ⟨one,no⟩ := (Finset.mem_filter.mp hm).2
    have ru:read C u.val=1 := by simpa [use,no] using one
    by_contra! h
    have nul:read C u.val=0 := by
      unfold read readsIn
      apply Finset.sum_eq_zero
      intro j hj
      apply List.count_eq_zero.mpr
      exact h ⟨j,Finset.mem_range.mp hj⟩
    omega
  let f (u:Fin r) := if h:u∈rem then (hit u h).choose.val else C.size
  have fmem (u:Fin r) (h:u∈rem) : f u<C.size ∧ u.val∈(gateAt C (f u)).inputs := by
    simp only [f,dite_eq_left h]
    exact ⟨(hit u h).choose.isLt,(hit u h).choose_spec⟩
  have gshape (j:Fin C.size) := sh (gateAt C j.val) (by have hj:j.val<C.gates.length:=j.isLt;simp [gateAt,hj])
  have inj : Set.InjOn f (rem: Set (Fin r)) := by
    intro u hu v hv eq
    obtain ⟨jl,um⟩:=fmem u hu
    have vm: v.val∈(gateAt C (f u)).inputs := eq ▸ (fmem v hv).2
    let j:Fin C.size:=⟨f u,jl⟩
    rcases gshape j with h|h
    · exact uniq (j:=j) ⟨(Finset.mem_filter.mp hu).2.1,um,h.1⟩ ⟨(Finset.mem_filter.mp hv).2.1,vm,h.1⟩
    · obtain ⟨i,hi⟩:=List.length_eq_one_iff.mp h.2
      change (gateAt C (f u)).inputs=[i] at hi
      simp [hi] at um vm
      exact Fin.ext (um.trans vm.symm)
  let gs:=good r C ∪ singles C
  have sub:rem.image f ⊆ gs.image Fin.val := by
    intro w hw;obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨fj,um⟩:=fmem u hu
    let j:Fin C.size:=⟨f u,fj⟩
    apply Finset.mem_image.mpr
    refine ⟨j,?_,rfl⟩
    rcases gshape j with h|h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,(Finset.mem_filter.mp hu).2.1,um,h.1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩)
  have hr:rem.card≤(good r C).card+unary C := by
    calc
      rem.card=(rem.image f).card := (Finset.card_image_of_injOn inj).symm
      _ ≤ _ := Finset.card_le_card sub
      _ ≤ gs.card := Finset.card_image_le
      _ ≤ _ := (Finset.card_union_le _ _).trans (by rw [singleCard])
  have cover:R ⊆ (bad∪many)∪(out∪rem) := by
    intro u hu
    by_cases z:use C u.val=0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,z⟩))
    by_cases b:1<use C u.val
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,b⟩))
    by_cases e:C.output=u.val
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hu,e⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu,by omega,e⟩))
  have h:= (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have h' := Finset.card_union_le bad many
  have h'' := Finset.card_union_le out rem
  have sz:R.card=r:=by simp [R]
  omega
end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem pathCount46 {r c : Nat} {C : Circuit}
    (_hin : ∀ j∈good r C, ∀ x∈good r C, ∀ y∈good r C,
      links (r+c) C x j → links (r+c) C y j → x=y)
    (hout : ∀ j∈good r C, ∀ x∈good r C, ∀ y∈good r C,
      links (r+c) C j x → links (r+c) C j y → x=y)
    (hd : (deep r c C).card≤1) : (good r C).card≤2*(starts r c C).card+1 := by
  classical
  let G := good r C
  let S := starts r c C
  let T := deep r c C
  let R := links (r+c) C
  have roots {v : Fin C.size} (gv:v∈G) (nv:v∉S) : ∃ u∈G, R u v := by
    by_contra hn
    exact nv (Finset.mem_filter.mpr ⟨gv,hn⟩)
  let nextV (u : Fin C.size) := if ex : ∃v∈G,R u v then Classical.choose ex else u
  have nextEq {u v : Fin C.size} (gu : u∈G) (gv : v∈G) (e : R u v) : nextV u = v := by
    have ex : ∃v∈G,R u v := ⟨v,gv,e⟩
    rw [show nextV u = Classical.choose ex by simp [nextV,ex]]
    exact hout u gu _ (Classical.choose_spec ex).1 v gv (Classical.choose_spec ex).2 e
  have sub : G ⊆ (S ∪ S.image nextV) ∪ T.image (fun u=>nextV (nextV u)) := by
    intro v gv
    by_cases vs : v∈S
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ vs)
    · obtain ⟨u,gu,uv⟩ := roots gv vs
      by_cases us : u∈S
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u,us,nextEq gu gv uv⟩))
      · obtain ⟨z,gz,zu⟩ := roots gu us
        have deepZ : z∈T := Finset.mem_filter.mpr ⟨gz,u,gu,v,gv,zu,uv⟩
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,deepZ,by rw [nextEq gz gu zu,nextEq gu gv uv]⟩)
  have A := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have B := Finset.card_union_le S (S.image nextV)
  have H : (S.image nextV).card ≤ S.card := Finset.card_image_le
  have J : (T.image (fun u=>nextV (nextV u))).card ≤ T.card := Finset.card_image_le
  change T.card≤1 at hd
  change G.card≤2*S.card+1
  omega

theorem pathIn46 {r c : Nat} {C : Circuit} (sh : shapes C) :
    ∀ j∈good r C, ∀ x∈good r C, ∀ y∈good r C,
      links (r+c) C x j → links (r+c) C y j → x=y := by
  classical
  intro j gj x _ y _ xj yj
  obtain ⟨u,portU⟩ := (Finset.mem_filter.mp gj).2
  have jj : j.val<C.gates.length := j.isLt
  have mem : gateAt C j.val ∈ C.gates := by simp [gateAt,jj]
  have hh : (gateAt C j.val).inputs.length≤2 := by rcases sh _ mem with h|h <;> omega
  have hu := portU.2.1
  have hx := xj.2
  have hy := yj.2
  let g := (gateAt C j.val).inputs
  have two (i j k : Nat) (hi : i∈g) (hj : j∈g) (hk : k∈g) : i=j ∨ i=k ∨ j=k := by
    change g.length≤2 at hh
    generalize g=g' at hh hi hj hk
    rcases g' with _ | ⟨a,_ | ⟨b,_ | ⟨p,l⟩⟩⟩ <;> simp_all <;> grind
  have h := two u.val (r+c+x.val) (r+c+y.val) hu hx hy
  have ht := u.isLt
  apply Fin.ext; omega

end PEqualNP.Outside.L_meta_25546_aux

namespace PEqualNP.Outside.L_meta_25546_aux
open PEqualNP.CircuitLowerBounds
theorem pathOut46 {r c : Nat} {C : Circuit} :
    ∀ j∈good r C, ∀ x∈good r C, ∀ y∈good r C,
      links (r+c) C j x → links (r+c) C j y → x=y := by
  intro j _ x _ y _ jx jy
  exact (atOnly46 jy.1 jy.2).2 x jx.2
end PEqualNP.Outside.L_meta_25546_aux

open PEqualNP.Outside.L_meta_25546_aux in
theorem PEqualNP.Outside.L_meta_25546 :
∀ (r c : ℕ), 2 ≤ r → 2 ≤ c →
  ∀ (G : Fin r → Fin c → Bool), Function.Injective G →
    Function.Injective (fun v u => G u v) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
    (∀ g ∈ C.gates,
      ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (r + c) C →
    PEqualNP.Represents.Represents G C →
    10 * r + 5 * c ≤ 9 * C.size + 28 := by
  intro r c _ _ G ri ci C sh back rep
  obtain ⟨D,ds,db,dr,dl,sz,_⟩ := prune46 C sh back rep
  have unique : ∀ {u v : Fin r} {j : Fin D.size}, port D u j → port D v j → u=v :=
    fun a b => port_unique46 ri db dr a b
  have ledger := ledger46 ri ci ds db dr dl
  have rows := countRows46 ri ds dr unique
  have marks := countStarts46 ds db unique
  have chains := pathCount46 (pathIn46 ds) pathOut46 (deepCard46 ri db dr)
  have bounded : (good r D).card≤D.size := (Finset.card_le_univ _).trans (by simp)
  omega
