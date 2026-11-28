import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1385

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def inputsAt (n : Nat) (t : Fin (n+1)) : List Bool :=
  (List.ofFn (fun j : Fin n => decide (j.val < t.val))) ++ [false,true]

theorem prefix_length (n : Nat) (t : Fin (n+1)) : (inputsAt n t).length = n+2 := by
  simp [inputsAt]

theorem prefix_read (n : Nat) (t : Fin (n+1)) (i : Nat) (hi : i < n+2) :
    (inputsAt n t).getD i false = if i<n then decide (i < t.val) else decide (i = n+1) := by
  unfold inputsAt
  have h : (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length = n := by simp
  by_cases lt : i < n
  · have inList : i < (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length := by simpa [h] using lt
    rw [List.getD_append _ _ _ _ inList, if_pos lt]
    rw [List.getD_eq_getElem _ _ inList]
    simp
  · have outside : (List.ofFn (fun j : Fin n => decide (j.val < t.val))).length ≤ i := by simpa [h] using Nat.le_of_not_gt lt
    rw [List.getD_append_right _ _ _ _ outside, h, if_neg lt]
    have cases : i = n ∨ i = n+1 := by omega
    rcases cases with rfl | rfl <;> simp

def fits (n p b s : Nat) (word : Fin (n+1) → Bool) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ ReadsBack (n+2) C ∧ C.size-notCount C ≤ p ∧
    notCount C ≤ b ∧ C.size ≤ s ∧ C.output < n+2+C.size ∧
    ∀ t, C.eval (inputsAt n t) = word t

def assign (n m : Nat) (f : Nat → Nat) (j : Nat) : Nat :=
  if j < n then f j else m+(j-n)

def relocateGate (n m : Nat) (f : Nat → Nat) (g : Gate) : Gate :=
  ⟨g.op,g.inputs.map (assign n m f)⟩

def relocate (n m : Nat) (f : Nat → Nat) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relocateGate n m f), assign n m f C.output⟩

theorem assign_bound {n m : Nat} {f : Nat → Nat} (hf : ∀ j < n, f j < m)
    {i k : Nat} (h : i < n+k) : assign n m f i < m+k := by
  unfold assign
  split
  · have := hf i ‹i<n›
    omega
  · omega

theorem notCount_relocate (n m : Nat) (f : Nat → Nat) (C : Circuit) :
    notCount (relocate n m f C) = notCount C := by
  simp only [notCount, relocate]
  generalize C.gates = gs
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change ((relocateGate n m f g :: gs.map (relocateGate n m f)).filter _).length = _
    simp only [List.filter_cons, relocateGate]
    split <;> simp_all

theorem relocate_size (n m : Nat) (f : Nat → Nat) (C : Circuit) :
    (relocate n m f C).size = C.size := by simp [relocate, Circuit.size]

theorem relocate_fanin {n m : Nat} {f : Nat → Nat} {C : Circuit} (h : FanInTwo C) :
    FanInTwo (relocate n m f C) := by
  intro g hg
  change g ∈ C.gates.map (relocateGate n m f) at hg
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hg
  simpa only [relocateGate, List.length_map] using h old ho

theorem relocate_reads {n m : Nat} {f : Nat → Nat} {C : Circuit}
    (hf : ∀ j < n, f j < m) (h : ReadsBack n C) : ReadsBack m (relocate n m f C) := by
  intro j hj i hi
  simp only [relocate, List.length_map] at hj
  have mapped : j < (relocate n m f C).gates.length := by simpa [relocate] using hj
  have heq : gateAt (relocate n m f C) j = relocateGate n m f (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem _ _ mapped, List.getD_eq_getElem _ _ hj]
    simp [relocate]
  rw [heq] at hi
  obtain ⟨old, ho, rfl⟩ := List.mem_map.mp hi
  exact assign_bound hf (h j hj old ho)

def pushGate (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

theorem getD_snoc (xs : List Bool) (x : Bool) (i : Nat) :
    (xs++[x]).getD i false = if i=xs.length then x else xs.getD i false := by
  by_cases h : i<xs.length
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_eq_default xs false (Nat.le_of_not_gt h)]
    by_cases he : i=xs.length
    · simp [he]
    · have positive : 0 < i-xs.length := by omega
      rw [if_neg he, List.getD_eq_default [x] false (show [x].length ≤ i-xs.length from positive)]

theorem fold_relocate {n m : Nat} {f : Nat → Nat} (hf : ∀ j < n, f j < m)
    (gs : List Gate) (k : Nat) (xs ys : List Bool)
    (hx : xs.length = n+k) (hy : ys.length = m+k)
    (data : ∀ i, xs.getD i false = ys.getD (assign n m f i) false) :
    ∀ i, (gs.foldl pushGate xs).getD i false =
      ((gs.map (relocateGate n m f)).foldl pushGate ys).getD (assign n m f i) false := by
  induction gs generalizing k xs ys with
  | nil => exact data
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih (k+1) _ _ (by simp [pushGate,hx,Nat.add_assoc]) (by simp [pushGate,hy,Nat.add_assoc])
    intro i
    have values : g.inputs.map (fun j => xs.getD j false) =
        (relocateGate n m f g).inputs.map (fun j => ys.getD j false) := by
      simp only [relocateGate, List.map_map, Function.comp_def]
      exact List.map_congr_left (fun j _ => data j)
    have same : i=xs.length ↔ assign n m f i=ys.length := by
      simp only [hx, hy, assign]
      split
      · have := hf i ‹i<n›
        omega
      · omega
    simp only [pushGate, getD_snoc, same, values]
    simp only [relocateGate, data]

theorem fits_relabel {n m p b s : Nat} {word : Fin (n+1) → Bool}
    (h : fits n p b s word) (f : Nat → Nat) (tmap : Fin (m+1) → Fin (n+1))
    (hf : ∀ i < n+2, f i < m+2)
    (hw : ∀ t i, i < n+2 → (inputsAt n (tmap t)).getD i false = (inputsAt m t).getD (f i) false) :
    fits m p b s (word ∘ tmap) := by
  obtain ⟨C, hfan, hr, hp, hb, hs, ho, he⟩ := h
  let D := relocate (n+2) (m+2) f C
  refine ⟨D, relocate_fanin hfan, relocate_reads hf hr, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [D, relocate_size, notCount_relocate] using hp
  · simpa [D, notCount_relocate] using hb
  · simpa [D, relocate_size] using hs
  · have hdo := assign_bound hf ho
    rw [show D.size = C.size from relocate_size _ _ _ _]
    exact hdo
  · intro t
    have init : ∀ i, (inputsAt n (tmap t)).getD i false = (inputsAt m t).getD (assign (n+2) (m+2) f i) false := by
      intro i
      by_cases yes : i < n+2
      · simpa only [assign, if_pos yes] using hw t i yes
      · rw [List.getD_eq_default _ _ (by rw [prefix_length]; omega),
            List.getD_eq_default _ _ (by rw [prefix_length]; simp [assign,yes])]
    have transfer := fold_relocate hf C.gates 0 (inputsAt n (tmap t)) (inputsAt m t)
      (by simp [prefix_length]) (by simp [prefix_length]) init C.output
    change C.eval (inputsAt n (tmap t)) = D.eval (inputsAt m t) at transfer
    exact transfer.symm.trans (he (tmap t))

end PEqualNP.Outside.L_lib_1385

namespace PEqualNP.Outside.L_lib_1385

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)
open PEqualNP.NotBracket (notCount)

def multiFit (n a p b s : Nat) (W : Nat → Fin a → Bool) : Prop :=
  ∃ (C : Circuit) (tap : Fin a → Nat), FanInTwo C ∧ ReadsBack (n+2) C ∧
    C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧ C.size-notCount C ≤ p ∧
    notCount C ≤ b ∧ C.size ≤ s ∧ ∀ (l : Fin (n+1)) i,
      (C.wires (inputsAt n l)).getD (tap i) false = W l.val i

def retime (n h l : Nat) : Nat := if l ≤ h then l else min n (max h (l-2))

def extension (n a h : Nat) (W : Nat → Fin (a+1) → Bool) (l : Nat) (i : Fin (a+4)) : Bool :=
  if i.val < a+1 then W (retime n h l) (Fin.ofNat (a+1) i.val)
  else if i.val = a+1 then decide (h+1 ≤ l ∧ l < n+3)
  else if i.val = a+2 then decide (h+2 ≤ l ∧ l < n+4)
  else if l = h+1 then false else if l = n+3 then true else W (retime n h l) 0

def stretch (n h i : Nat) : Nat :=
  if i<n then (if i<h then i else i+2) else if i=n then n+4 else n+5

theorem decisions {P Q : Prop} [Decidable P] [Decidable Q] (eq : P ↔ Q) : decide P = decide Q := by
  by_cases h : P
  · simp [h,eq.mp h]
  · have hn : ¬ Q := fun hq => h (eq.mpr hq)
    simp [h,hn]

theorem stretch_bound (n h : Nat) : ∀ i<n+2, stretch n h i<n+4+2 := by
  intro i hi
  unfold stretch
  split_ifs <;> omega

theorem retime_bound {n h : Nat} (hh : h<n) (l : Nat) : retime n h l < n+1 := by
  unfold retime
  split <;> omega

theorem stretch_row (n h : Nat) (hh : h<n) (l : Fin (n+4+1)) (i : Nat) (hi : i<n+2) :
    (inputsAt n ⟨retime n h l.val,retime_bound hh _⟩).getD i false =
      (inputsAt (n+4) l).getD (stretch n h i) false := by
  rw [prefix_read n _ i hi, prefix_read (n+4) _ _ (stretch_bound n h i hi)]
  by_cases old : i < n
  · by_cases early : i < h
    · have place : stretch n h i = i := by simp only [stretch,ite_eq_left old,ite_eq_left early]
      simp only [place,ite_eq_left old,ite_eq_left (show i < n+4 by omega),Fin.val_mk]
      apply decisions
      unfold retime
      split <;> omega
    · have place : stretch n h i = i+2 := by simp only [stretch,ite_eq_left old,ite_eq_right early]
      simp only [place,ite_eq_left old,ite_eq_left (show i+2 < n+4 by omega),Fin.val_mk]
      apply decisions
      unfold retime
      split <;> omega
  · have cases : i=n ∨ i=n+1 := by omega
    rcases cases with rfl|rfl <;> simp (disch := omega) [stretch]

theorem replay_row {n h : Nat} (hh : h<n) (C : Circuit) (l : Fin (n+4+1)) (i : Nat) :
    (C.wires (inputsAt n ⟨retime n h l.val,retime_bound hh _⟩)).getD i false =
    ((relocate (n+2) (n+4+2) (stretch n h) C).wires (inputsAt (n+4) l)).getD
      (assign (n+2) (n+4+2) (stretch n h) i) false := by
  let t : Fin (n+1) := ⟨retime n h l.val,retime_bound hh _⟩
  apply fold_relocate (stretch_bound n h) C.gates 0 (inputsAt n t) (inputsAt (n+4) l)
    (by simp [prefix_length]) (by simp [prefix_length]) _ i
  intro j
  by_cases hhj : j<n+2
  · exact (by simpa only [assign,ite_eq_left hhj,t] using stretch_row n h hh l j hhj)
  · rw [List.getD_eq_default _ _ (by rw [prefix_length]; omega),
        List.getD_eq_default _ _ (by rw [prefix_length]; simp [assign,hhj])]

def pulseGates (n h base old : Nat) : List Gate := [
  ⟨.not,[n+2]⟩, ⟨.and,[h,base]⟩, ⟨.not,[n+3]⟩, ⟨.and,[h+1,base+2]⟩,
  ⟨.not,[h]⟩, ⟨.or,[old,n+2]⟩, ⟨.or,[base+4,base+3]⟩, ⟨.and,[base+5,base+6]⟩]

theorem wire_length (C : Circuit) (input : List Bool) :
    (C.wires input).length = input.length + C.size := by
  unfold Circuit.wires Circuit.size
  change (C.gates.foldl pushGate input).length = _
  generalize C.gates = gs
  induction gs generalizing input with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons,ih]
    simp [pushGate]
    omega

theorem pulse_readback (n h base old : Nat) (hh : h<n) (hb : n+4+2 ≤ base)
    (ho : old<base) : ReadsBack base ⟨pulseGates n h base old, 0⟩ := by
  intro j hj i hi
  change j<8 at hj
  interval_cases j <;> simp [gateAt,pulseGates] at hi ⊢ <;> omega

theorem append_readback {m : Nat} {C : Circuit} {gs : List Gate}
    (hC : ReadsBack m C) (hG : ReadsBack (m+C.size) ⟨gs,0⟩) :
    ReadsBack m ⟨C.gates ++ gs,C.output⟩ := by
  intro j hj i hi
  by_cases old : j<C.gates.length
  · have eq : gateAt ⟨C.gates ++ gs,C.output⟩ j=gateAt C j := List.getD_append _ _ _ _ old
    rw [eq] at hi
    exact hC j old i hi
  · have eq : gateAt ⟨C.gates ++ gs,C.output⟩ j=gateAt ⟨gs,0⟩ (j-C.gates.length) :=
      List.getD_append_right _ _ _ _ (Nat.le_of_not_gt old)
    rw [eq] at hi
    have bound : j-C.gates.length<gs.length := by
      change j<(C.gates++gs).length at hj
      simp only [List.length_append] at hj
      omega
    have lt := hG (j-C.gates.length) bound i hi
    change i < m+C.gates.length+(j-C.gates.length) at lt
    omega

theorem pulse_values (n h old : Nat) (prior : List Bool) (hraw : h+1<prior.length)
    (h2 : n+2<prior.length) (h3 : n+3<prior.length) (ho : old<prior.length) :
    let base := prior.length
    let hot := prior.getD h false
    let early := prior.getD (h+1) false
    let late := prior.getD (n+2) false
    let last := prior.getD (n+3) false
    let orig := prior.getD old false
    let P := hot && !late
    let Q := early && !last
    (pulseGates n h base old).foldl pushGate prior =
      prior ++ [!late,P,!last,Q,!hot,orig||late,(!hot)||Q,(orig||late) && ((!hot)||Q)] := by
  dsimp only
  have read_old (tails : List Bool) (i : Nat) (hi : i<prior.length) :
      (prior++tails).getD i false = prior.getD i false := List.getD_append _ _ _ _ hi
  have read_new (tails : List Bool) (i : Nat) :
      (prior++tails).getD (prior.length+i) false = tails.getD i false := by
    rw [List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega
  have read_zero (tails : List Bool) :
      (prior++tails).getD prior.length false = tails.getD 0 false := by simpa using read_new tails 0
  have hhot : h<prior.length := by omega
  simp only [pulseGates,pushGate,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil,
    GateOp.eval,List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id,
    Bool.and_true,Bool.or_false,List.append_assoc,List.cons_append,List.nil_append,
    read_old _ _ hraw,read_old _ _ h2,read_old _ _ h3,read_old _ _ ho,read_old _ _ hhot,
    read_new,read_zero,List.getD_cons_zero,List.getD_cons_succ]

theorem wires_read_input (C : Circuit) (input : List Bool) (i : Nat) (hi : i < input.length) :
    (C.wires input).getD i false = input.getD i false := by
  unfold Circuit.wires
  generalize C.gates = gs
  induction gs generalizing input with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons,ih _ (by simp; omega),List.getD_append _ _ _ _ hi]

theorem pulse_signal (start finish level : Nat) :
    (decide (start < level) && !decide (finish < level)) =
      decide (start+1 ≤ level ∧ level<finish+1) := by
  by_cases h : start<level <;> by_cases h' : finish<level <;> simp (disch := omega) [h,h'] <;> omega

theorem root_signal (n h l : Nat) (hh : h<n) (hl : l≤n+4) (w : Nat → Bool)
    (end_false : w n = false) :
    ((w (retime n h l) || decide (n+2<l)) &&
      (!decide (h<l) || decide (h+2≤l ∧ l<n+4))) =
    if l=h+1 then false else if l=n+3 then true else w (retime n h l) := by
  by_cases a : l≤h
  · rw [ite_eq_right (show l≠h+1 by omega),ite_eq_right (show l≠n+3 by omega)]
    simp [show ¬n+2<l by omega, show ¬h<l by omega]
  by_cases b : l=h+1
  · subst l
    simp (disch := omega)
  by_cases c : l≤n+2
  · rw [ite_eq_right b,ite_eq_right (show l≠n+3 by omega)]
    simp [show ¬n+2<l by omega,show h+2≤l by omega, show l<n+4 by omega]
  by_cases d : l=n+3
  · subst l
    simp [show h<n+3 by omega,show h≤n+1 by omega,show n+3≠h+1 by omega,show n+2≠h by omega]
  have e : l=n+4 := by omega
  subst l
  have last : retime n h (n+4)=n := by unfold retime; split <;> omega
  simp [last,end_false,show h<n+4 by omega]

theorem extend {n a p b s h : Nat} {W : Nat → Fin (a+1) → Bool}
    (hh : h<n) (_first_true : W h 0 = true) (last_false : W n 0 = false)
    (witness : multiFit n (a+1) p b s W) :
    multiFit (n+4) (a+4) (p+5) (b+3) (s+8) (extension n a h W) := by
  obtain ⟨C,tap,hfan,hread,hout,htap,hp,hb,hs,hsem⟩ := witness
  let m := n+4+2
  let move := assign (n+2) m (stretch n h)
  let D := relocate (n+2) m (stretch n h) C
  let base := m+D.size
  let last := pulseGates n h base (move (tap 0))
  let E : Circuit := ⟨D.gates++last,D.output⟩
  let chosen (i : Fin (a+4)) :=
    if i.val < a+1 then move (tap (Fin.ofNat (a+1) i.val))
    else if i.val=a+1 then base+1 else if i.val=a+2 then base+3 else base+7
  have hDsize : D.size=C.size := relocate_size _ _ _ _
  have hDnot : notCount D=notCount C := notCount_relocate _ _ _ _
  have hEsize : E.size=D.size+8 := by simp [E,last,pulseGates,Circuit.size]
  have hEnot : notCount E=notCount D+3 := by simp [E,last,pulseGates,notCount,List.filter_append]
  have tapbound (i : Fin (a+1)) : move (tap i)<base := by
    have low := assign_bound (stretch_bound n h) (htap i)
    simpa only [base,move,hDsize] using low
  have outbound : D.output<base := by
    have low := assign_bound (stretch_bound n h) hout
    change assign (n+2) m (stretch n h) C.output < m+D.size
    rw [hDsize]
    exact low
  have fan : FanInTwo E := by
    intro g hg
    change g ∈ D.gates ++ last at hg
    rcases List.mem_append.mp hg with hg|hg
    · exact relocate_fanin hfan g hg
    · simp only [last,pulseGates,List.mem_cons,List.not_mem_nil,or_false] at hg
      rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  have back : ReadsBack m E := append_readback (relocate_reads (stretch_bound n h) hread)
    (pulse_readback n h base _ hh (by dsimp [base,m]; omega) (tapbound 0))
  refine ⟨E,chosen,fan,back,?_,?_,?_,?_,?_,?_⟩
  · change D.output<m+E.size
    rw [hEsize]
    dsimp [base] at outbound
    omega
  · intro i
    change chosen i < m+E.size
    rw [hEsize]
    dsimp only [chosen]
    split_ifs
    · exact (tapbound _).trans (by dsimp [base]; omega)
    all_goals dsimp [base]; omega
  · rw [hEsize,hEnot,hDsize,hDnot]
    omega
  · rw [hEnot,hDnot]
    omega
  · rw [hEsize,hDsize]
    omega
  · intro l i
    let prior := D.wires (inputsAt (n+4) l)
    have len : prior.length=base := by simp only [prior,wire_length,prefix_length,base,m]
    have oldeval (j : Fin (a+1)) : prior.getD (move (tap j)) false = W (retime n h l.val) j :=
      (replay_row hh C l (tap j)).symm.trans (hsem ⟨retime n h l.val,retime_bound hh _⟩ j)
    have input_value (j : Nat) (hj : j<n+4) : prior.getD j false = decide (j<l.val) := by
      dsimp only [prior]
      rw [wires_read_input _ _ _ (by rw [prefix_length]; omega),
          prefix_read _ _ _ (by omega),ite_eq_left hj]
    let P := decide (h+1≤l.val ∧ l.val<n+3)
    let Q := decide (h+2≤l.val ∧ l.val<n+4)
    let root := ((W (retime n h l.val) 0 || decide (n+2<l.val)) && (!decide (h<l.val) || Q))
    let trailing := [!decide (n+2<l.val), P, !decide (n+3<l.val), Q,
      !decide (h<l.val), W (retime n h l.val) 0 || decide (n+2<l.val),
      !decide (h<l.val) || Q, root]
    have values : E.wires (inputsAt (n+4) l)=prior++trailing := by
      change (D.gates++last).foldl pushGate (inputsAt (n+4) l) = _
      rw [List.foldl_append]
      change last.foldl pushGate prior = _
      have hB : n+4+2 ≤ base := by dsimp [base,m]; omega
      have hval := pulse_values n h (move (tap 0)) prior
        (by rw [len]; omega) (by rw [len]; omega) (by rw [len]; omega) (by rw [len]; exact tapbound 0)
      dsimp only at hval
      rw [len] at hval
      rw [input_value h (by omega),input_value (h+1) (by omega),input_value (n+2) (by omega),
          input_value (n+3) (by omega),oldeval 0] at hval
      rw [pulse_signal h (n+2), pulse_signal (h+1) (n+3)] at hval
      exact hval
    rw [values]
    dsimp only [chosen,extension]
    by_cases earlier : i.val<a+1
    · rw [ite_eq_left earlier, ite_eq_left earlier,
        List.getD_append _ _ _ _ (by rw [len]; exact tapbound _)]
      exact oldeval _
    rw [ite_eq_right earlier, ite_eq_right earlier]
    have get (j : Nat) : (prior++trailing).getD (base+j) false = trailing.getD j false := by
      rw [List.getD_append_right _ _ _ _ (by rw [len]; omega),len]
      congr 1
      omega
    by_cases pidx : i.val=a+1
    · rw [ite_eq_left pidx,ite_eq_left pidx,get]
      rfl
    rw [ite_eq_right pidx,ite_eq_right pidx]
    by_cases qidx : i.val=a+2
    · rw [ite_eq_left qidx,ite_eq_left qidx,get]
      rfl
    rw [ite_eq_right qidx,ite_eq_right qidx,get]
    exact root_signal n h l.val hh (by have := l.isLt; omega) (fun t => W t 0) last_false

end PEqualNP.Outside.L_lib_1385

namespace PEqualNP.Outside.L_lib_1385

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity (FanInTwo)
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

def family (d l : Nat) (i : Fin (d+1)) : Bool :=
  if i.val=0 then decide (l % 2=1) else decide (i.val≤l ∧ l<d+i.val)

theorem family_initial : multiFit 2 2 1 1 2 (family 1) := by
  let C : Circuit := ⟨[⟨.not,[1]⟩,⟨.and,[0,4]⟩],5⟩
  refine ⟨C,fun _ => 5, ?_, ?_, by decide, ?_, by decide, by decide, by decide, ?_⟩
  · simp [FanInTwo,C]
  · intro j hj i hi
    change j<2 at hj
    interval_cases j <;> simp [gateAt,C] at hi ⊢ <;> omega
  · intro i
    change 5 < 6
    decide
  · decide +kernel

theorem extended_family {d : Nat} (dpos : 0<d) (odd : d % 2=1)
    (l : Fin (2*d+4+1)) (i : Fin (d+2+1)) :
    let choose : Fin (d+4) := if i.val=0 then ⟨d+3,by omega⟩ else ⟨i.val,by have := i.isLt; omega⟩
    extension (2*d) d d (family d) l.val choose = family (d+2) l.val i := by
  intro choose
  have hli := l.isLt
  have hii := i.isLt
  by_cases zero : i.val=0
  · have value : choose.val=d+3 := by simp [choose,zero]
    unfold extension
    rw [value,ite_eq_right (show ¬ d+3<d+1 by omega),ite_eq_right (show d+3≠d+1 by omega),
      ite_eq_right (show d+3≠d+2 by omega)]
    unfold family
    rw [ite_eq_left zero,ite_eq_left (show (0 : Fin (d+1)).val=0 from rfl)]
    by_cases a : l.val≤d
    · rw [ite_eq_right (show l.val≠d+1 by omega),ite_eq_right (show l.val≠2*d+3 by omega)]
      simp only [retime,ite_eq_left a]
    by_cases b : l.val=d+1
    · rw [ite_eq_left b]
      exact (decide_eq_false (show ¬ l.val % 2=1 by omega)).symm
    by_cases c : l.val≤2*d+2
    · have middle : retime (2*d) d l.val=l.val-2 := by unfold retime; split <;> omega
      rw [ite_eq_right b,ite_eq_right (show l.val≠2*d+3 by omega),middle]
      apply decisions
      omega
    by_cases e : l.val=2*d+3
    · rw [ite_eq_right b,ite_eq_left e]
      exact (decide_eq_true (show l.val % 2=1 by omega)).symm
    have end_val : l.val=2*d+4 := by omega
    have end_old : retime (2*d) d l.val=2*d := by unfold retime; split <;> omega
    rw [ite_eq_right b,ite_eq_right e,end_old]
    apply decisions
    omega
  · have value : choose.val=i.val := by simp [choose,zero]
    unfold extension
    rw [value]
    by_cases old : i.val<d+1
    · rw [ite_eq_left old]
      have oval : (Fin.ofNat (d+1) i.val).val=i.val := by
        exact Nat.mod_eq_of_lt old
      unfold family
      rw [oval]
      simp only [ite_eq_right zero]
      apply decisions
      unfold retime
      split <;> omega
    · rw [ite_eq_right old]
      have cases : i.val=d+1 ∨ i.val=d+2 := by omega
      unfold family
      rw [ite_eq_right zero]
      rcases cases with t|t
      · rw [ite_eq_left t,t]
        apply decisions
        omega
      · rw [ite_eq_right (show i.val≠d+1 by omega),ite_eq_left t,t]
        apply decisions
        omega

theorem family_step (d p b s : Nat) (dpos : 0<d) (odd : d % 2 = 1)
    (prior : multiFit (2*d) (d+1) p b s (family d)) :
    multiFit (2*(d+2)) (d+2+1) (p+5) (b+3) (s+8) (family (d+2)) := by
  have true_at : family d d 0 = true := by simp [family,odd]
  have false_at : family d (2*d) 0 = false := by simp (disch := omega) [family]
  have extended := extend (h := d) (by omega) true_at false_at prior
  obtain ⟨C,tap,hf,hr,ho,ht,hp,hb,hs,eval⟩ := extended
  have newn : 2*(d+2) = 2*d+4 := by omega
  rw [newn]
  let route (i : Fin (d+2+1)) : Fin (d+4) :=
    if i.val=0 then ⟨d+3,by omega⟩ else ⟨i.val,by have := i.isLt; omega⟩
  refine ⟨C,tap ∘ route,hf,hr,ho,fun i => ht (route i),hp,hb,hs, ?_⟩
  intro l i
  exact (eval l (route i)).trans (extended_family dpos odd l i)

theorem family_all (h : Nat) :
    let d := 2*h+1
    multiFit (2*d) (d+1) (5*h+1) (3*h+1) (8*h+2) (family d) := by
  induction h with
  | zero => exact family_initial
  | succ h ih =>
    let d := 2*h+1
    have step := family_step d (5*h+1) (3*h+1) (8*h+2) (by dsimp [d]; omega) (by dsimp [d]; omega) ih
    dsimp only
    have hd : 2*(h+1)+1 = d+2 := by dsimp [d]; omega
    rw [hd]
    convert step using 1 <;> omega

end PEqualNP.Outside.L_lib_1385

theorem PEqualNP.Outside.L_lib_1385 :
  let fit := fun (n a p b s : Nat) (W : Nat → Fin a → Bool) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
      PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
      C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
      C.size - PEqualNP.NotBracket.notCount C ≤ p ∧ PEqualNP.NotBracket.notCount C ≤ b ∧ C.size ≤ s ∧
      ∀ (l : Fin (n+1)) i, (C.wires
        (List.ofFn (fun j : Fin n => decide (j.val < l.val)) ++ [false,true])).getD (tap i) false = W l.val i
  (∀ (n a p b s h : Nat) (W : Nat → Fin (a+1) → Bool),
    h < n → W h 0 = true → W n 0 = false → fit n (a+1) p b s W →
    let retime := fun l : Nat => if l ≤ h then l else min n (max h (l-2))
    let V := fun (l : Nat) (i : Fin (a+4)) =>
      if i.val < a+1 then W (retime l) (Fin.ofNat (a+1) i.val)
      else if i.val = a+1 then decide (h+1 ≤ l ∧ l < n+3)
      else if i.val = a+2 then decide (h+2 ≤ l ∧ l < n+4)
      else if l = h+1 then false else if l = n+3 then true else W (retime l) 0
    fit (n+4) (a+4) (p+5) (b+3) (s+8) V) ∧
  ∀ h : Nat,
    let d := 2*h+1
    let V := fun (l : Nat) (i : Fin (d+1)) =>
      if i.val = 0 then decide (l % 2 = 1) else decide (i.val ≤ l ∧ l < d+i.val)
    fit (2*d) (d+1) (5*h+1) (3*h+1) (8*h+2) V := by
  exact ⟨fun _ _ _ _ _ _ _ => PEqualNP.Outside.L_lib_1385.extend, PEqualNP.Outside.L_lib_1385.family_all⟩
